/-
# Cassels, Chapter 9, §1: proper equivalence and proper automorphs

**Layer:** integer-valued forms `Q : QuadForm ℤ n` (the library's integral forms; Cassels' classically integral
forms are those with `IsClassicallyIntegral`). The library's classes are $\mathrm{GL}_n(\mathbb Z)$-classes
(`Siegel.IntEquiv`); this file adds Cassels' *proper* classes ($\mathrm{SL}_n(\mathbb Z)$-classes).

**Defines**
* `ProperIntEquiv Q Q'`: $Q(T\vec x) = Q'(\vec x)$ for some $T \in \mathrm{GL}_n(\mathbb Z)$ with $\det T = 1$ (Cassels,
  Ch. 9, §1, p. 127: *proper* equivalence); `ImproperIntEquiv`: the same with $\det T = -1$;
* `properSetoid n`, `PClass n`: proper classes;
* `AutPlus Q`: the proper integral automorphs $O^{+}(Q)$, a subgroup of `Siegel.Aut Q` $= O(Q)$;
* `HasImproperAut Q`: $Q$ has an integral automorph of determinant $-1$.

**Proves**
* proper equivalence is an equivalence relation, and for binary forms it is `Binary.SLEquiv`
  (`properIntEquiv_iff_sLEquiv`);
* improper equivalence is not an equivalence relation (`not_equivalence_improperIntEquiv`, with Cassels' example);
* $[O(Q) : O^{+}(Q)]$ is $1$ or $2$, and it is $2$ exactly when $Q$ has an improper automorph
  (`index_autPlus`);
* Cassels' examples: $x^{2} + 5y^{2}$ has the improper automorph $\operatorname{diag}(1, -1)$; $3x^{2} + 2xy + 10y^{2}$
  has none (the second form is reconstructed, see `not_hasImproperAut_ex`);
* (9.r3) if $Q$ has an improper automorph its class is its proper class; otherwise the class is the union of exactly
  two proper classes (`intEquiv_iff_properIntEquiv_of_hasImproperAut`, `ncard_properClasses_in_class`).
-/
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Binary.ClassBijection
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.LocalDensity.JordanForm
import QuadFormsKB.Equiv.Integral

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Determinants in $\mathrm{GL}_n(\mathbb Z)$ -/

/-- An element of $\mathrm{GL}_n(\mathbb Z)$ has determinant $\pm 1$. -/
theorem det_GL_int_eq (g : GL (Fin n) ℤ) : g.val.det = 1 ∨ g.val.det = -1 := by
  have h : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  exact Int.isUnit_iff.mp h

/-- **The reflection** $R = \operatorname{diag}(-1, 1, \dots, 1)$ (in the variable $x_0$) as an element of
$\mathrm{GL}_n(\mathbb Z)$, $n \ge 1$; $\det R = -1$ and $R^{2} = 1$. -/
def reflFirst (hn : 0 < n) : GL (Fin n) ℤ where
  val := diagonal (Function.update 1 ⟨0, hn⟩ (-1))
  inv := diagonal (Function.update 1 ⟨0, hn⟩ (-1))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    by_cases h : i = ⟨0, hn⟩ <;> simp [h]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    by_cases h : i = ⟨0, hn⟩ <;> simp [h]

theorem det_reflFirst (hn : 0 < n) : (reflFirst hn).val.det = -1 := by
  simp only [reflFirst, det_diagonal]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
  rw [Function.update_self, Finset.prod_eq_one]
  · ring
  · intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rfl

theorem reflFirst_mul_self (hn : 0 < n) : reflFirst hn * reflFirst hn = 1 := by
  ext1
  exact (reflFirst hn).val_inv

/-- **Substitution:** for an integral form $Q$ and an integral matrix $M$, $\vec x \mapsto Q(M\vec x)$ is an integral form
(its Hessian is $M^{\mathsf T} H M$, symmetric with even diagonal). -/
theorem exists_eval_mulVec_form (Q : QuadForm ℤ n) (M : Matrix (Fin n) (Fin n) ℤ) :
    ∃ Q' : QuadForm ℤ n, ∀ x, Q.eval (M *ᵥ x) = Q'.eval x := by
  have hsym : (Mᵀ * Q.hessian * M).IsSymm := by
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    congr 2
    simp [QuadForm.hessian, add_comm]
  have hev : ∀ i, Even ((Mᵀ * Q.hessian * M) i i) := fun i => by
    have h := LocalDensity.two_mul_eval_eq_hessian Q (M *ᵥ Pi.single i 1)
    have e : (Mᵀ * Q.hessian * M) i i = (M *ᵥ Pi.single i 1) ⬝ᵥ (Q.hessian *ᵥ (M *ᵥ Pi.single i 1)) := by
      have h1 : (Mᵀ * Q.hessian * M) i i = ((Mᵀ * Q.hessian * M) *ᵥ Pi.single i 1) i := by
        simp
      rw [h1, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_single_one]
      simp [mulVec, dotProduct, transpose_apply]
    exact ⟨Q.eval (M *ᵥ Pi.single i 1), by rw [e, ← h]; ring⟩
  obtain ⟨Q', hQ'⟩ := exists_hessian_eq _ hsym hev
  exact ⟨Q', (eval_mulVec_eq_iff_hessian Q Q' M).mpr hQ'.symm⟩

/-! ### Proper and improper equivalence -/

/-- **Proper equivalence** (Cassels, Ch. 9, §1, p. 127): $Q(T\vec x) = Q'(\vec x)$ for all $\vec x \in \mathbb Z^n$, for
some integral $T$ with $\det T = +1$ (an element of $\mathrm{SL}_n(\mathbb Z)$). For binary forms this is
`Binary.SLEquiv` (`properIntEquiv_iff_sLEquiv`). -/
@[kb "cassels1978" "Ch. 9, §1, (1.1), p. 127 (proper equivalence)"]
def ProperIntEquiv (Q Q' : QuadForm ℤ n) : Prop :=
  ∃ T : GL (Fin n) ℤ, T.val.det = 1 ∧ ∀ x, Q.eval (T.val *ᵥ x) = Q'.eval x

/-- **Improper equivalence** (Cassels, Ch. 9, §1, p. 127): $Q(T\vec x) = Q'(\vec x)$ for all $\vec x \in \mathbb Z^n$, for
some integral $T$ with $\det T = -1$. -/
@[kb "cassels1978" "Ch. 9, §1, (1.1), p. 127 (improper equivalence)"]
def ImproperIntEquiv (Q Q' : QuadForm ℤ n) : Prop :=
  ∃ T : GL (Fin n) ℤ, T.val.det = -1 ∧ ∀ x, Q.eval (T.val *ᵥ x) = Q'.eval x

theorem ProperIntEquiv.refl (Q : QuadForm ℤ n) : ProperIntEquiv Q Q := ⟨1, by simp, fun x => by simp⟩

theorem ProperIntEquiv.symm {Q Q' : QuadForm ℤ n} (h : ProperIntEquiv Q Q') : ProperIntEquiv Q' Q := by
  obtain ⟨T, hT, h⟩ := h
  refine ⟨T⁻¹, ?_, fun x => ?_⟩
  · have := congrArg Matrix.det (T.inv_val)
    rw [det_mul, det_one, hT, mul_one] at this
    exact this
  · rw [← h, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem ProperIntEquiv.trans {Q Q' Q'' : QuadForm ℤ n} (h : ProperIntEquiv Q Q')
    (h' : ProperIntEquiv Q' Q'') : ProperIntEquiv Q Q'' := by
  obtain ⟨T, hT, h⟩ := h
  obtain ⟨T', hT', h'⟩ := h'
  refine ⟨T * T', by rw [Units.val_mul, det_mul, hT, hT', one_mul], fun x => ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, h, h']

theorem ProperIntEquiv.intEquiv {Q Q' : QuadForm ℤ n} (h : ProperIntEquiv Q Q') : IntEquiv Q Q' := by
  obtain ⟨T, -, h⟩ := h
  exact ⟨T, h⟩

theorem ImproperIntEquiv.intEquiv {Q Q' : QuadForm ℤ n} (h : ImproperIntEquiv Q Q') : IntEquiv Q Q' := by
  obtain ⟨T, -, h⟩ := h
  exact ⟨T, h⟩

/-- **Cassels, Ch. 9, §1, p. 127:** *"Clearly proper equivalence is an equivalence relation."* -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (proper equivalence is an equivalence relation)"]
theorem equivalence_properIntEquiv : Equivalence (ProperIntEquiv (n := n)) :=
  ⟨ProperIntEquiv.refl, ProperIntEquiv.symm, ProperIntEquiv.trans⟩

/-- An equivalence is proper or improper. -/
theorem intEquiv_iff_proper_or_improper (Q Q' : QuadForm ℤ n) :
    IntEquiv Q Q' ↔ ProperIntEquiv Q Q' ∨ ImproperIntEquiv Q Q' := by
  constructor
  · rintro ⟨T, h⟩
    rcases det_GL_int_eq T with hd | hd
    · exact Or.inl ⟨T, hd, h⟩
    · exact Or.inr ⟨T, hd, h⟩
  · rintro (h | h)
    · exact h.intEquiv
    · exact h.intEquiv

/-- Proper equivalence of binary forms is the library's `Binary.SLEquiv`. -/
theorem properIntEquiv_iff_sLEquiv (f g : BinQF) : ProperIntEquiv f g ↔ Binary.SLEquiv f g := Iff.rfl

/-- `ProperIntEquiv` as a setoid. -/
def properSetoid (n : ℕ) : Setoid (QuadForm ℤ n) where
  r := ProperIntEquiv
  iseqv := equivalence_properIntEquiv

/-- **Proper classes** (Cassels' *proper equivalence classes*, p. 127) of integral forms in $n$ variables. -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (proper equivalence class)"]
abbrev PClass (n : ℕ) := Quotient (properSetoid n)

/-- The proper class of $Q$. -/
def pclassOf (Q : QuadForm ℤ n) : PClass n := Quotient.mk (properSetoid n) Q

theorem pclassOf_eq_pclassOf_iff {Q Q' : QuadForm ℤ n} : pclassOf Q = pclassOf Q' ↔ ProperIntEquiv Q Q' :=
  Quotient.eq (r := properSetoid n)

/-! ### Proper automorphs -/

/-- **The proper integral automorphs** $O^{+}(Q) = \{T \in O(Q) : \det T = 1\}$ (Cassels, Ch. 9, §1, p. 127), a
subgroup of `Aut Q` $= O(Q)$. -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (proper automorphs O⁺(f))"]
def AutPlus (Q : QuadForm ℤ n) : Subgroup (GL (Fin n) ℤ) :=
  Aut Q ⊓ (MonoidHom.ker ((Units.map (detMonoidHom (n := Fin n) (R := ℤ)))))

theorem mem_autPlus_iff {Q : QuadForm ℤ n} {T : GL (Fin n) ℤ} :
    T ∈ AutPlus Q ↔ T ∈ Aut Q ∧ T.val.det = 1 := by
  simp only [AutPlus, Subgroup.mem_inf, MonoidHom.mem_ker]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Units.val h
    simpa using this
  · ext1; simpa using h

/-- **$Q$ has an improper automorph:** some $T \in O(Q)$ has $\det T = -1$. -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (improper automorphs)"]
def HasImproperAut (Q : QuadForm ℤ n) : Prop := ∃ T ∈ Aut Q, T.val.det = -1

theorem hasImproperAut_iff_improperIntEquiv_self (Q : QuadForm ℤ n) :
    HasImproperAut Q ↔ ImproperIntEquiv Q Q := by
  constructor
  · rintro ⟨T, hT, hd⟩; exact ⟨T, hd, hT⟩
  · rintro ⟨T, hd, hT⟩; exact ⟨T, hT, hd⟩

open Classical in
/-- **Cassels, Ch. 9, §1, p. 127:** *either no improper automorphs exist (and then $O^{+}(f) = O(f)$) or $O^{+}(f)$ is of
index $2$ in $O(f)$.* Here as the relative index of `AutPlus Q` in `Aut Q`. -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (index of O⁺(f) in O(f))"]
theorem index_autPlus (Q : QuadForm ℤ n) :
    (AutPlus Q).relIndex (Aut Q) = if HasImproperAut Q then 2 else 1 := by
  classical
  -- `AutPlus Q ⊓ Aut Q` is the kernel of the determinant `Aut Q → ℤˣ`, whose image is `{1}` or `{±1}`
  set φ : Aut Q →* ℤˣ := (Units.map (detMonoidHom (n := Fin n) (R := ℤ))).comp (Aut Q).subtype
  have hker : (AutPlus Q).subgroupOf (Aut Q) = φ.ker := by
    ext ⟨T, hT⟩
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_autPlus_iff, φ, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    refine ⟨fun h => ?_, fun h => ⟨hT, ?_⟩⟩
    · ext1; simpa using h.2
    · have := congrArg Units.val h
      simpa using this
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  split_ifs with h
  · obtain ⟨T, hT, hd⟩ := h
    have hrange : φ.range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact φ.range.one_mem
      · refine ⟨⟨T, hT⟩, ?_⟩
        ext1
        simpa [φ] using hd
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  · have hrange : φ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro u ⟨⟨T, hT⟩, rfl⟩
      rw [Subgroup.mem_bot]
      ext1
      rcases det_GL_int_eq T with hd | hd
      · simpa [φ] using hd
      · exact absurd ⟨T, hT, hd⟩ h
    rw [hrange, Subgroup.card_bot]

/-! ### Cassels' examples (p. 127–128) -/

/-- $x^{2} + 5y^{2}$ (variables $x_0, x_1$). -/
def exForm1 : QuadForm ℤ 2 := QuadForm.ofUpper ![![1, 0], ![0, 5]]

/-- $3x^{2} + 2xy + 10y^{2}$ (variables $x_0, x_1$; see `not_hasImproperAut_ex`). -/
def exForm2 : QuadForm ℤ 2 := QuadForm.ofUpper ![![3, 2], ![0, 10]]

theorem eval_exForm1 (x : Fin 2 → ℤ) : exForm1.eval x = x 0 ^ 2 + 5 * x 1 ^ 2 := by
  simp [exForm1, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

theorem eval_exForm2 (x : Fin 2 → ℤ) : exForm2.eval x = 3 * x 0 ^ 2 + 2 * x 0 * x 1 + 10 * x 1 ^ 2 := by
  simp [exForm2, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

/-- **Cassels, Ch. 9, §1, p. 127:** $x^{2} + 5y^{2}$ *has the improper automorph* $(x, y) \mapsto (x, -y)$. -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (x² + 5y² has an improper automorph)"]
theorem hasImproperAut_ex : HasImproperAut exForm1 := by
  refine ⟨reflFirst (n := 2) (by norm_num), fun x => ?_, det_reflFirst _⟩
  rw [eval_exForm1, eval_exForm1]
  simp only [reflFirst, mulVec_diagonal]
  simp

/-- **Cassels, Ch. 9, §1, p. 128:** a form with no improper automorph. *The only integral representations of $3$ are
$f_2(\mathbf a) = 3$ with $\mathbf a = \pm(1, 0)$; if $T$ is an automorph then $T(1,0) = \pm(1,0)$* and $T$ is proper.

*Reconstruction:* the scan lost the form; $3x^{2} + 2xy + 10y^{2}$ fits the argument quoted (it is
$2x^{2} + (x+y)^{2} + 9y^{2}$, so the value $3$ forces $y = 0$, $x = \pm 1$). -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (a form with no improper automorph; form reconstructed)"]
theorem not_hasImproperAut_ex : ¬ HasImproperAut exForm2 := by
  rintro ⟨T, hT, hd⟩
  have hev : ∀ x, exForm2.eval (T.val *ᵥ x) = exForm2.eval x := hT
  -- the image of `e₀` represents `3`, so it is `±e₀`
  have h3 := hev ![1, 0]
  have h3' := hev ![0, 1]
  have h3'' := hev ![1, 1]
  simp only [eval_exForm2, mulVec, dotProduct, Fin.sum_univ_two] at h3 h3' h3''
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3 h3' h3''
  rw [Matrix.det_fin_two] at hd
  set a := T.val 0 0; set b := T.val 0 1; set c := T.val 1 0; set d := T.val 1 1
  have key : 6 * (a * b) + 2 * (a * d) + 2 * (b * c) + 20 * (c * d) = 2 := by
    linear_combination h3'' - h3 - h3'
  have hc : c = 0 := by nlinarith [sq_nonneg (a + c), sq_nonneg c, sq_nonneg a]
  rw [hc] at key hd
  have had : a * d = -1 := by linarith
  omega

/-- **Cassels, Ch. 9, §1, p. 127:** *improper equivalence is not an equivalence relation* (it is not reflexive on
binary forms: `not_hasImproperAut_ex`). -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (improper equivalence is not an equivalence relation)"]
theorem not_equivalence_improperIntEquiv : ¬ Equivalence (ImproperIntEquiv (n := 2)) := fun h =>
  not_hasImproperAut_ex ((hasImproperAut_iff_improperIntEquiv_self _).mpr (h.refl _))

/-! ### 9.r3: classes and proper classes -/

/-- The form $Q(R\vec x)$ with $R = \operatorname{diag}(-1, 1, \dots, 1)$: improperly equivalent to $Q$. -/
def twist (hn : 0 < n) (Q : QuadForm ℤ n) : QuadForm ℤ n :=
  Classical.choose (exists_eval_mulVec_form Q (reflFirst hn).val)

theorem eval_twist (hn : 0 < n) (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    (twist hn Q).eval x = Q.eval ((reflFirst hn).val *ᵥ x) :=
  (Classical.choose_spec (exists_eval_mulVec_form Q (reflFirst hn).val) x).symm

theorem improperIntEquiv_twist (hn : 0 < n) (Q : QuadForm ℤ n) : ImproperIntEquiv Q (twist hn Q) :=
  ⟨reflFirst hn, det_reflFirst hn, fun x => (eval_twist hn Q x).symm⟩

/-- An improper equivalence $Q \to Q'$ is a proper equivalence $Q(R\,\cdot) \to Q'$. -/
theorem properIntEquiv_twist_of_improper (hn : 0 < n) {Q Q' : QuadForm ℤ n} (h : ImproperIntEquiv Q Q') :
    ProperIntEquiv (twist hn Q) Q' := by
  obtain ⟨T, hT, h⟩ := h
  refine ⟨reflFirst hn * T, by rw [Units.val_mul, det_mul, det_reflFirst, hT]; ring, fun x => ?_⟩
  rw [eval_twist, Units.val_mul, ← mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, reflFirst_mul_self,
    Units.val_one, one_mulVec, h]

/-- **Cassels, Ch. 9, §1, p. 128 (first half):** *if $f$ has an improper automorph then the equivalence class and the
proper equivalence class to which $f$ belongs coincide.* -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (class = proper class when there is an improper automorph)"]
theorem intEquiv_iff_properIntEquiv_of_hasImproperAut {Q : QuadForm ℤ n} (hQ : HasImproperAut Q)
    (Q' : QuadForm ℤ n) : IntEquiv Q Q' ↔ ProperIntEquiv Q Q' := by
  refine ⟨fun h => ?_, ProperIntEquiv.intEquiv⟩
  rcases (intEquiv_iff_proper_or_improper Q Q').mp h with h | ⟨T, hT, h⟩
  · exact h
  · obtain ⟨S, hS, hSd⟩ := hQ
    refine ⟨S * T, by rw [Units.val_mul, det_mul, hSd, hT]; ring, fun x => ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hS, h]

/-- Without an improper automorph, $Q$ and $Q(R\,\cdot)$ are not properly equivalent. -/
theorem not_properIntEquiv_twist (hn : 0 < n) {Q : QuadForm ℤ n} (hQ : ¬ HasImproperAut Q) :
    ¬ ProperIntEquiv Q (twist hn Q) := by
  rintro ⟨T, hT, h⟩
  refine hQ ⟨T * reflFirst hn, fun x => ?_, by rw [Units.val_mul, det_mul, hT, det_reflFirst]; ring⟩
  rw [Units.val_mul, ← mulVec_mulVec, h, eval_twist, mulVec_mulVec, ← Units.val_mul, reflFirst_mul_self,
    Units.val_one, one_mulVec]

/-- **The class of $Q$ is the union of the proper classes of $Q$ and of $Q(R\,\cdot)$** ($n \ge 1$). -/
theorem intEquiv_iff_properIntEquiv_or_twist (hn : 0 < n) (Q Q' : QuadForm ℤ n) :
    IntEquiv Q Q' ↔ ProperIntEquiv Q Q' ∨ ProperIntEquiv (twist hn Q) Q' := by
  rw [intEquiv_iff_proper_or_improper]
  refine or_congr Iff.rfl ⟨properIntEquiv_twist_of_improper hn, fun h => ?_⟩
  obtain ⟨T, hT, h⟩ := h
  refine ⟨reflFirst hn * T, by rw [Units.val_mul, det_mul, det_reflFirst, hT]; ring, fun x => ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, ← eval_twist, h]

/-- **The proper classes contained in the class of $Q$.** -/
def properClassesIn (Q : QuadForm ℤ n) : Set (PClass n) := {c | ∃ Q', pclassOf Q' = c ∧ IntEquiv Q Q'}

open Classical in
/-- **Cassels, Ch. 9, §1, p. 128 (9.r3):** *if $f$ has an improper automorph then the equivalence class and the proper
equivalence class to which $f$ belongs will coincide. If, however, $f$ has no improper automorphs then the equivalence
class of $f$ splits into two proper equivalence classes.* Stated for $n \ge 1$ as the number of proper classes in the
class of $Q$ (for $n = 0$ there is one form and one class). -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (a class is one or two proper classes)"]
theorem ncard_properClassesIn (hn : 0 < n) (Q : QuadForm ℤ n) :
    (properClassesIn Q).ncard = if HasImproperAut Q then 1 else 2 := by
  classical
  have hset : properClassesIn Q = {pclassOf Q, pclassOf (twist hn Q)} := by
    ext c
    induction c using Quotient.inductionOn with
    | h Q' =>
      simp only [properClassesIn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨Q'', h, hQ''⟩
        have h' : ProperIntEquiv Q'' Q' := pclassOf_eq_pclassOf_iff.mp h
        rcases (intEquiv_iff_properIntEquiv_or_twist hn Q Q'').mp hQ'' with h2 | h2
        · exact Or.inl (pclassOf_eq_pclassOf_iff.mpr (h2.trans h')).symm
        · exact Or.inr (pclassOf_eq_pclassOf_iff.mpr (h2.trans h')).symm
      · rintro (h | h)
        · exact ⟨Q, h.symm, IsometricGL.refl Q⟩
        · refine ⟨twist hn Q, h.symm, (improperIntEquiv_twist hn Q).intEquiv⟩
  rw [hset]
  split_ifs with h
  · have : pclassOf (twist hn Q) = pclassOf Q := by
      refine pclassOf_eq_pclassOf_iff.mpr (ProperIntEquiv.symm ?_)
      exact (intEquiv_iff_properIntEquiv_of_hasImproperAut h _).mp (improperIntEquiv_twist hn Q).intEquiv
    rw [this, Set.pair_eq_singleton, Set.ncard_singleton]
  · rw [Set.ncard_pair]
    intro he
    exact not_properIntEquiv_twist hn h (pclassOf_eq_pclassOf_iff.mp he)

/-! ### 9.r8: equivalence of definite forms is a finite search -/

/-- **Cassels, Ch. 9, §1, pp. 131–132 (9.r8), definite case:** *the reader can readily construct for himself a procedure
for deciding whether two definite forms are equivalent*: for $f$ positive definite and any $g$, the integral matrices
$T \in \mathrm{GL}_n(\mathbb Z)$ with $f(T\mathbf x) = g(\mathbf x)$ form a finite set (the $j$-th column of $T$ is one of
the finitely many representations of $g(e_j)$ by $f$, `IntQF.PosDef.repSet_finite`). The indefinite case (spinor genera,
automorphs) is not formalized. -/
@[kb "cassels1978" "Ch. 9, §1, pp. 131–132 (equivalence of definite forms: a finite search)"]
theorem finite_equivalences {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (g : QuadForm ℤ n) :
    {T : GL (Fin n) ℤ | ∀ x, f.eval (T.val *ᵥ x) = g.eval x}.Finite := by
  classical
  have hfin : (Set.univ.pi fun i : Fin n => repSet f (g.eval (Pi.single i 1))).Finite :=
    Set.Finite.pi fun i => IntQF.PosDef.repSet_finite hf _
  refine Set.Finite.of_finite_image (f := fun T : GL (Fin n) ℤ => fun i => T.val *ᵥ Pi.single i 1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨T, hT, rfl⟩ i -
    exact hT (Pi.single i 1)
  · intro T _ T' _ h
    ext i j
    have := congrFun (congrFun h j) i
    simpa [mulVec_single_one] using this

/-! ### 9.r4: primitive forms -/

/-- **Primitive** (Cassels, Ch. 9, §1, p. 128, for classically integral forms $f = \sum f_{ij}x_ix_j$, $f_{ij} = f_{ji}
\in \mathbb Z$): $\gcd(f_{ij}) = 1$. Here $f_{ij} = H_{ij}/2$ ($H$ the Hessian), and "$\gcd = 1$" is: every common
divisor is a unit. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (primitive form)"]
def IsPrimitiveCI (f : QuadForm ℤ n) : Prop :=
  IsClassicallyIntegral f ∧ ∀ c : ℤ, (∀ i j, c ∣ f.hessian i j / 2) → IsUnit c

/-- **Properly primitive** (Cassels, p. 128): primitive with at least one $f_{ii}$ odd. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (properly primitive)"]
def IsProperlyPrimitive (f : QuadForm ℤ n) : Prop := IsPrimitiveCI f ∧ ∃ i, ¬ (2 : ℤ) ∣ f.coeff i i

/-- **Improperly primitive** (Cassels, p. 128): primitive with every $f_{ii}$ even. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (improperly primitive)"]
def IsImproperlyPrimitive (f : QuadForm ℤ n) : Prop := IsPrimitiveCI f ∧ ∀ i, (2 : ℤ) ∣ f.coeff i i

/-- **Cassels, Ch. 9, §1, p. 128:** *if $f$ is improperly primitive, then $\tfrac12 f(\mathbf x) \in \mathbb Z[\mathbf x]$
but $\tfrac12 f(\mathbf x)$ is not an integral form* (in the classical sense): $f = 2g$ for an integer-valued form $g$
that is not classically integral. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (½f for improperly primitive f)"]
theorem exists_half_of_improperlyPrimitive {f : QuadForm ℤ n} (hf : IsImproperlyPrimitive f) :
    ∃ g : QuadForm ℤ n, (2 : ℤ) • g = f ∧ ¬ IsClassicallyIntegral g := by
  obtain ⟨⟨hci, hprim⟩, hdiag⟩ := hf
  have hoff := (isClassicallyIntegral_iff f).mp hci
  have hev : ∀ i j, i ≤ j → 2 ∣ f.coeff i j := fun i j hij => by
    rcases hij.lt_or_eq with h | rfl
    · exact even_iff_two_dvd.mp (hoff i j h)
    · exact hdiag i
  refine ⟨QuadForm.ofUpper fun i j => f.coeff i j / 2, ?_, fun hg => ?_⟩
  · ext i j
    simp only [QuadForm.smul_coeff, Matrix.smul_apply, QuadForm.ofUpper, Matrix.of_apply, smul_eq_mul]
    split_ifs with hij
    · exact Int.mul_ediv_cancel' (hev i j hij)
    · rw [f.upper (not_le.mp hij)]; ring
  · have hg' := (isClassicallyIntegral_iff _).mp hg
    refine (show ¬ IsUnit (2 : ℤ) by decide) (hprim 2 fun i j => ?_)
    have key : ∀ i j, i ≤ j → 2 ∣ f.hessian i j / 2 := by
      intro i j hij
      rcases hij.lt_or_eq with h | rfl
      · have h1 := even_iff_two_dvd.mp (hg' i j h)
        simp only [QuadForm.ofUpper, Matrix.of_apply, if_pos h.le] at h1
        have : f.hessian i j = f.coeff i j := by
          simp [QuadForm.hessian, f.upper h]
        rw [this]; exact h1
      · have : f.hessian i i = 2 * f.coeff i i := by simp [QuadForm.hessian]; ring
        rw [this, Int.mul_ediv_cancel_left _ two_ne_zero]
        exact hdiag i
    rcases le_total i j with h | h
    · exact key i j h
    · have hs : f.hessian i j = f.hessian j i := by simp [QuadForm.hessian, add_comm]
      rw [hs]; exact key j i h

end QuadFormsKB.Siegel
