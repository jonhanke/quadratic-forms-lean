import QuadFormsKB.Binary.FormsIdeals
import QuadFormsKB.Siegel.Genus

/-!
# Classes of binary forms and the class group

For a fundamental discriminant $D < 0$:

* **Proper classes** (`slSetoid`): $\{\mathrm{SL}_2(\mathbb{Z})\text{-classes of primitive positive definite forms of
  discriminant } D\} \simeq \mathrm{Cl}(\mathcal O_{K_D})$, $f \mapsto [\mathfrak a_f]$ (`slClassEquiv`,
  `card_slClasses`: their number is $h(D)$).
* **$\mathrm{GL}_2(\mathbb{Z})$-classes** (the convention of this repository, the repo's `Siegel.IntEquiv`): they correspond to the classes
  of $\mathrm{Cl}$ modulo inversion $[\mathfrak a] \sim [\mathfrak a]^{-1} = [\bar{\mathfrak a}]$ (`glClassEquiv`), and
  $2\,\#\{\mathrm{GL}\text{-classes}\} = h + \#\mathrm{Cl}[2]$ (`two_mul_card_glClasses`).

Sources: Cox, *Primes of the form $x^2 + ny^2$*, §7.B, Thm. 7.7 and §2.A (proper vs. improper equivalence) [unverified locator];
Buell, *Binary Quadratic Forms*, Ch. 6; Cohen, §5.2.
-/

open QuadraticAlgebra NumberField Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF

variable {D : ℤ}

/-! ### Matrices and substitutions -/

/-- A vector in $\mathbb{Z}^2$ is `![x 0, x 1]`. -/
theorem vec_two_eq (x : Fin 2 → ℤ) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

/-- **Evaluation after a change of variables is `subst`:**
$f\!\left(\begin{pmatrix} p & q \\ r & s\end{pmatrix}\vec x\right) = (\mathrm{subst}\ p\,q\,r\,s\ f)(x_0, x_1)$. -/
theorem eval_mulVec (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval f (M *ᵥ x) = (BinQF.subst (M 0 0) (M 0 1) (M 1 0) (M 1 1) f).eval (x 0) (x 1) := by
  rw [eval_subst]
  have : M *ᵥ x = ![M 0 0 * x 0 + M 0 1 * x 1, M 1 0 * x 0 + M 1 1 * x 1] := by
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [this]; rfl

/-- **Values determine the substituted form:** $f(M\vec x) = g(\vec x)$ for all $\vec x$ iff
$g = \mathrm{subst}\ M\ f$. -/
theorem forall_eval_mulVec_iff (f g : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (∀ x, QuadForm.eval f (M *ᵥ x) = QuadForm.eval g x) ↔
      BinQF.subst (M 0 0) (M 0 1) (M 1 0) (M 1 1) f = g := by
  constructor
  · intro h
    refine ext_eval fun x y => ?_
    have := h ![x, y]
    rw [eval_mulVec] at this
    simpa [BinQF.eval] using this
  · rintro rfl x
    rw [eval_mulVec, vec_two_eq x]; rfl

/-- The determinant of an element of $\mathrm{GL}_2(\mathbb{Z})$ is $\pm 1$. -/
theorem det_GL_eq (g : GL (Fin 2) ℤ) : g.val.det = 1 ∨ g.val.det = -1 := by
  have h : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  exact Int.eq_one_or_neg_one_of_mul_eq_one h

/-- $d^2 = 1$ in $\mathbb{Z}$ iff $d = \pm 1$. -/
theorem eq_one_or_neg_one_of_sq {d : ℤ} (h : d ^ 2 = 1) : d = 1 ∨ d = -1 :=
  Int.isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨d, by rw [← sq]; exact h⟩)

/-- The element $\begin{pmatrix} p & q \\ r & s\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{Z})$ when $ps - qr = \pm 1$. -/
noncomputable def glOf (p q r s : ℤ) (h : (p * s - q * r) ^ 2 = 1) : GL (Fin 2) ℤ :=
  Matrix.nonsingInvUnit !![p, q; r, s] (by
    rw [Matrix.det_fin_two_of]
    exact isUnit_iff_exists_inv.mpr ⟨p * s - q * r, by rw [← sq]; exact h⟩)

@[simp] theorem glOf_val (p q r s : ℤ) (h) : (glOf p q r s h).val = !![p, q; r, s] := rfl

/-! ### Proper ($\mathrm{SL}_2(\mathbb{Z})$) equivalence -/

/-- **Proper equivalence** ($\mathrm{SL}_2(\mathbb{Z})$-equivalence) of binary forms: $f(\gamma\vec x) = g(\vec x)$ for all
$\vec x \in \mathbb{Z}^2$, for some $\gamma \in \mathrm{GL}_2(\mathbb{Z})$ with $\det\gamma = 1$. The $\mathrm{GL}_2(\mathbb{Z})$
version is the repo's `Siegel.IntEquiv` (the convention of this repository for classes). Source: Cox, §2.A [unverified locator]. -/
@[kb "cox2013" "§2.A [unverified locator]"]
def SLEquiv (f g : BinQF) : Prop :=
  ∃ γ : GL (Fin 2) ℤ, γ.val.det = 1 ∧ ∀ x, QuadForm.eval f (γ.val *ᵥ x) = QuadForm.eval g x

/-- **Proper equivalence via `subst`:** $f \sim_{\mathrm{SL}} g$ iff $g = f \circ \begin{pmatrix} p & q \\ r & s\end{pmatrix}$ with
$ps - qr = 1$. -/
theorem sLEquiv_iff (f g : BinQF) :
    SLEquiv f g ↔ ∃ p q r s : ℤ, p * s - q * r = 1 ∧ BinQF.subst p q r s f = g := by
  constructor
  · rintro ⟨γ, hd, h⟩
    rw [forall_eval_mulVec_iff] at h
    exact ⟨_, _, _, _, by rw [← Matrix.det_fin_two]; exact hd, h⟩
  · rintro ⟨p, q, r, s, hd, rfl⟩
    refine ⟨glOf p q r s (by rw [hd]; norm_num), by simp [Matrix.det_fin_two_of, hd], ?_⟩
    rw [forall_eval_mulVec_iff]; simp

/-- **$\mathrm{GL}_2(\mathbb{Z})$-equivalence via `subst`:** `Siegel.IntEquiv f g` iff
$g = f \circ \begin{pmatrix} p & q \\ r & s\end{pmatrix}$ with $ps - qr = \pm 1$. -/
theorem intEquiv_iff (f g : BinQF) :
    Siegel.IntEquiv f g ↔ ∃ p q r s : ℤ, (p * s - q * r) ^ 2 = 1 ∧ BinQF.subst p q r s f = g := by
  constructor
  · rintro ⟨γ, h⟩
    rw [forall_eval_mulVec_iff] at h
    refine ⟨_, _, _, _, ?_, h⟩
    rw [← Matrix.det_fin_two]
    rcases det_GL_eq γ with h' | h' <;> rw [h'] <;> norm_num
  · rintro ⟨p, q, r, s, hd, rfl⟩
    exact ⟨glOf p q r s hd, by rw [forall_eval_mulVec_iff]; simp⟩

theorem SLEquiv.refl (f : BinQF) : SLEquiv f f :=
  (sLEquiv_iff f f).mpr ⟨1, 0, 0, 1, by ring, ext_abc (by simp) (by simp) (by simp)⟩

theorem SLEquiv.symm {f g : BinQF} (h : SLEquiv f g) : SLEquiv g f := by
  obtain ⟨γ, hd, h⟩ := h
  refine ⟨γ⁻¹, ?_, fun x => ?_⟩
  · have : γ.val.det * (γ⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [hd, one_mul] at this; exact this
  · rw [← h, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem SLEquiv.trans {f g h : BinQF} (h₁ : SLEquiv f g) (h₂ : SLEquiv g h) : SLEquiv f h := by
  obtain ⟨γ, hd, h₁⟩ := h₁
  obtain ⟨γ', hd', h₂⟩ := h₂
  exact ⟨γ * γ', by rw [Units.val_mul, Matrix.det_mul, hd, hd', one_mul],
    fun x => by rw [Units.val_mul, ← mulVec_mulVec, h₁, h₂]⟩

/-- A proper equivalence is a $\mathrm{GL}_2(\mathbb{Z})$-equivalence. -/
theorem SLEquiv.intEquiv {f g : BinQF} (h : SLEquiv f g) : Siegel.IntEquiv f g := by
  obtain ⟨γ, -, h⟩ := h; exact ⟨γ, h⟩

/-- **A $\mathrm{GL}_2(\mathbb{Z})$-class is the union of at most two proper classes:** $f \sim_{\mathrm{GL}} g$ iff
$f \sim_{\mathrm{SL}} g$ or $\bar f \sim_{\mathrm{SL}} g$, where $\bar f = (a, -b, c) = f \circ \operatorname{diag}(1, -1)$
(`conjForm`). Source: Cox, §2.A [unverified locator] (the improper equivalences are $\operatorname{diag}(1,-1)$ times proper ones). -/
@[kb "cox2013" "§2.A [unverified locator]"]
theorem intEquiv_iff_sLEquiv_or (f g : BinQF) :
    Siegel.IntEquiv f g ↔ SLEquiv f g ∨ SLEquiv (conjForm f) g := by
  rw [intEquiv_iff, sLEquiv_iff, sLEquiv_iff]
  constructor
  · rintro ⟨p, q, r, s, hd, rfl⟩
    rcases eq_one_or_neg_one_of_sq hd with h | h
    · exact Or.inl ⟨p, q, r, s, h, rfl⟩
    · refine Or.inr ⟨p, q, -r, -s, by linarith, ext_abc ?_ ?_ ?_⟩ <;> simp [conjForm]
      ring
  · rintro (⟨p, q, r, s, hd, rfl⟩ | ⟨p, q, r, s, hd, rfl⟩)
    · exact ⟨p, q, r, s, by rw [hd]; norm_num, rfl⟩
    · refine ⟨p, q, -r, -s, by linear_combination (p * s - q * r + 1) * hd, ext_abc ?_ ?_ ?_⟩ <;>
        simp [conjForm]
      ring

/-! ### Lattices and change of basis -/

/-- **A unimodular change of basis does not change the lattice:** for $ps - qr = 1$,
$\mathbb{Z}\alpha + \mathbb{Z}\beta = \mathbb{Z}(p\alpha + r\beta) + \mathbb{Z}(q\alpha + s\beta)$. -/
theorem lattice_eq_of_det {α β : QOrder D} {p q r s : ℤ} (hd : p * s - q * r = 1) (z : QOrder D) :
    (∃ x y : ℤ, z = x • α + y • β) ↔ (∃ x y : ℤ, z = x • (p • α + r • β) + y • (q • α + s • β)) := by
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨x * s - y * q, -(x * r) + y * p, ?_⟩
    ext
    · simp; linear_combination (-(x * α.re) - y * β.re) * hd
    · simp; linear_combination (-(x * α.im) - y * β.im) * hd
  · rintro ⟨x, y, rfl⟩
    exact ⟨x * p + y * q, x * r + y * s, by ext <;> simp <;> ring⟩

/-- $\alpha \neq 0$ when $\operatorname{odet}(\alpha, \beta) \neq 0$. -/
theorem ne_zero_of_odet {α β : QOrder D} (h : odet α β ≠ 0) : α ≠ 0 := by
  rintro rfl; simp [odet] at h

variable [IsQuadDisc D]

/-- **An ideal with a basis of form $g$ is in the class of $\mathfrak a_g$:** if $(\alpha, \beta)$ is a $\mathbb{Z}$-basis of $J$
with $\operatorname{odet}(\alpha, \beta) \neq 0$ and form $g$ ($\operatorname{disc} g = D$, $g_a \neq 0$), then $[J] = [\mathfrak a_g]$ in
$\mathrm{Cl}(\mathbb{Z}[\omega])$ (`span_mul_formIdeal`: $(\alpha)\mathfrak a_g = (g_a) J$). This is "ideal $\to$ form $\to$ ideal
is the identity on classes"; the other composite is `isFormOf_formIdeal`. Source: Cox, Thm. 7.7, proof. -/
@[kb "cox2013" "§7.B, proof of Thm. 7.7"]
theorem mk0_eq_of_isFormOf {g : BinQF} (hg : g.disc = D) (ha : g.a ≠ 0) {α β : QOrder D}
    (h : IsFormOf g α β) (hn : odet α β ≠ 0) (J : (Ideal (QOrder D))⁰)
    (hJ : ∀ z, z ∈ (J : Ideal (QOrder D)) ↔ ∃ x y : ℤ, z = x • α + y • β) :
    ClassGroup.mk0 J = ClassGroup.mk0 ⟨formIdeal D g, mem_nonZeroDivisors_of_ne_zero (formIdeal_ne_bot ha)⟩ := by
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨(g.a : QOrder D), α, by exact_mod_cast ha, ne_zero_of_odet hn,
    (span_mul_formIdeal hg ha h hn J hJ).symm⟩

omit [IsQuadDisc D] in
/-- **The norm form is positive definite for $D < 0$:** $N(z) > 0$ for $z \neq 0$
($4N(u + v\omega) = (2u + b_D v)^2 - D v^2$). -/
theorem norm_pos_of_neg (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) {z : QOrder D} (hz : z ≠ 0) :
    0 < norm z := by
  have hq := discr_qa_qb hD4
  rw [discr_def] at hq
  have h4 : 4 * norm z = (2 * z.re + qb D * z.im) ^ 2 - D * z.im ^ 2 := by
    rw [QuadraticAlgebra.norm_def]; linear_combination -(z.im ^ 2) * hq
  by_cases him : z.im = 0
  · have hre : z.re ≠ 0 := fun h => hz (QuadraticAlgebra.ext h him)
    rw [him] at h4
    have : 0 < (2 * z.re) ^ 2 := by positivity
    nlinarith
  · have : 0 < z.im ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * z.re + qb D * z.im)]

/-! ### Primitive positive definite forms and the class map -/

/-- **Primitive positive definite forms of discriminant $D$:** $\operatorname{disc} f = D$, $f$ positive definite
(`BinQF.PosDef`) and primitive ($\gcd(a, b, c) = 1$). For a fundamental $D < 0$, the last two conditions are
equivalent to $a > 0$ (`mem_primPosForm_iff`). -/
abbrev PrimPosForm (D : ℤ) : Type := {f : BinQF // f.disc = D ∧ f.PosDef ∧ f.IsPrimitive}

theorem PrimPosForm.a_pos (f : PrimPosForm D) : 0 < f.1.a :=
  ((posDef_iff_posDef' f.1).mp f.2.2.1).1

omit [IsQuadDisc D] in
/-- For a fundamental $D < 0$: $f$ is a primitive positive definite form of discriminant $D$ iff
$\operatorname{disc} f = D$ and $a > 0$. -/
theorem mem_primPosForm_iff (hfund : Int.IsFundamentalDiscr D) (hD : D < 0) (f : BinQF) :
    (f.disc = D ∧ f.PosDef ∧ f.IsPrimitive) ↔ (f.disc = D ∧ 0 < f.a) := by
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, ((posDef_iff_posDef' f).mp h2).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (posDef_iff_posDef' f).mpr ⟨h2, h1 ▸ hD⟩, isPrimitive_of_fund hfund h1⟩

/-- **Proper equivalence of primitive positive definite forms** as a setoid; its quotient is the set of proper
($\mathrm{SL}_2(\mathbb{Z})$-) classes. -/
def slSetoid (D : ℤ) : Setoid (PrimPosForm D) where
  r f g := SLEquiv f.1 g.1
  iseqv := ⟨fun f => SLEquiv.refl f.1, SLEquiv.symm, SLEquiv.trans⟩

/-- **$\mathrm{GL}_2(\mathbb{Z})$-equivalence of primitive positive definite forms** (the repo's `Siegel.IntEquiv`) as a
setoid; its quotient is the set of classes in the convention of this repository. -/
def glSetoid (D : ℤ) : Setoid (PrimPosForm D) where
  r f g := Siegel.IntEquiv f.1 g.1
  iseqv := ⟨fun f => Siegel.IsometricGL.refl f.1, Siegel.IsometricGL.symm, Siegel.IsometricGL.trans⟩

/-- **The ideal class of a form**, $f \mapsto [\mathfrak a_f] \in \mathrm{Cl}(\mathbb{Z}[\omega])$. -/
noncomputable def idealClass (f : PrimPosForm D) : ClassGroup (QOrder D) :=
  ClassGroup.mk0 ⟨formIdeal D f.1, mem_nonZeroDivisors_of_ne_zero (formIdeal_ne_bot f.a_pos.ne')⟩

/-- **Properly equivalent forms have the same ideal class** (for any $D$): if $g = f \circ \gamma$, $\det\gamma = 1$, then
$(p a + r(k_f - \omega),\ q a + s(k_f - \omega))$ is a basis of $\mathfrak a_f$ with form $g$, so
$[\mathfrak a_g] = [\mathfrak a_f]$. Source: Cox, Thm. 7.7, proof. -/
@[kb "cox2013" "§7.B, Thm. 7.7"]
theorem idealClass_eq_of_sLEquiv {f g : PrimPosForm D} (h : SLEquiv f.1 g.1) : idealClass f = idealClass g := by
  obtain ⟨p, q, r, s, hd, hg⟩ := (sLEquiv_iff _ _).mp h
  have hf := isFormOf_formIdeal f.2.1
  have hsub := hf.subst hd
  rw [hg] at hsub
  have hn : odet (p • fα D f.1 + r • fβ D f.1) (q • fα D f.1 + s • fβ D f.1) ≠ 0 := by
    rw [odet_comb, hd, one_mul, odet_fα_fβ f.2.1]; exact f.a_pos.ne'
  refine mk0_eq_of_isFormOf g.2.1 g.a_pos.ne' hsub hn _ fun z => ?_
  rw [mem_formIdeal_iff_exists f.2.1, lattice_eq_of_det hd]

/-- **Forms with the same ideal class are properly equivalent** ($D < 0$): if $x\mathfrak a_f = y\mathfrak a_g$ then
$(xa_f, x(k_f - \omega))$ and $(ya_g, y(k_g - \omega))$ are two positively oriented bases (as $N(x), N(y) > 0$) of one
lattice, with forms $f$ and $g$; they differ by $\mathrm{SL}_2(\mathbb{Z})$ (`IsFormOf.exists_subst_of_lattice_eq`), and
the form of a basis is unique. Source: Cox, Thm. 7.7, proof. -/
@[kb "cox2013" "§7.B, Thm. 7.7"]
theorem sLEquiv_of_idealClass_eq (hD : D < 0) {f g : PrimPosForm D} (h : idealClass f = idealClass g) :
    SLEquiv f.1 g.1 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  have hD4 := (IsQuadDisc.fund (D := D)).1
  have hf := (isFormOf_formIdeal f.2.1).mul x
  have hg := (isFormOf_formIdeal g.2.1).mul y
  have hlat : ∀ z, (∃ u v : ℤ, z = u • (x * fα D f.1) + v • (x * fβ D f.1)) ↔
      (∃ u v : ℤ, z = u • (y * fα D g.1) + v • (y * fβ D g.1)) := fun z => by
    rw [← mem_span_mul_formIdeal_iff f.2.1, ← mem_span_mul_formIdeal_iff g.2.1]
    exact SetLike.ext_iff.mp hxy z
  have hn : 0 < odet (x * fα D f.1) (x * fβ D f.1) := by
    rw [odet_mul, odet_fα_fβ f.2.1]; exact mul_pos (norm_pos_of_neg hD hD4 hx) f.a_pos
  have hn' : 0 < odet (y * fα D g.1) (y * fβ D g.1) := by
    rw [odet_mul, odet_fα_fβ g.2.1]; exact mul_pos (norm_pos_of_neg hD hD4 hy) g.a_pos
  obtain ⟨p, q, r, s, hd, h'⟩ := hf.exists_subst_of_lattice_eq hlat hn hn'
  exact (sLEquiv_iff _ _).mpr ⟨p, q, r, s, hd, h'.unique hg hn'.ne'⟩

/-- **Every ideal class is the class of a form** ($D < 0$): by the Hermite normal form a nonzero ideal is
$J = C\mathfrak a_f$ with $a > 0$ (`exists_eq_span_mul_formIdeal`). Source: Cox, Thm. 7.7. -/
@[kb "cox2013" "§7.B, Thm. 7.7"]
theorem idealClass_surjective (hD : D < 0) : Function.Surjective (idealClass (D := D)) := by
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨C, f, hC, hfD, ha, hJ⟩ :=
    exists_eq_span_mul_formIdeal (J : Ideal (QOrder D)) (nonZeroDivisors.coe_ne_zero J)
  refine ⟨⟨f, (mem_primPosForm_iff (IsQuadDisc.fund (D := D)) hD f).mpr ⟨hfD, ha⟩⟩, ?_⟩
  unfold idealClass
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨(C : QOrder D), 1, by exact_mod_cast hC.ne', one_ne_zero, ?_⟩
  rw [Ideal.span_singleton_one, Ideal.top_mul, ← hJ]

/-- **Proper classes ↔ ideal classes** ($D < 0$ fundamental): $[f] \mapsto [\mathfrak a_f]$ is a bijection from the
$\mathrm{SL}_2(\mathbb{Z})$-classes of primitive positive definite forms of discriminant $D$ onto
$\mathrm{Cl}(\mathbb{Z}[\omega])$. Source: Cox, Thm. 7.7 (ii); Buell, Thm. 6.20 [unverified locator]. -/
@[kb "cox2013" "§7.B, Thm. 7.7 (ii)"]
noncomputable def slClassEquivOrder (hD : D < 0) : Quotient (slSetoid D) ≃ ClassGroup (QOrder D) :=
  Equiv.ofBijective (Quotient.lift idealClass fun _ _ h => idealClass_eq_of_sLEquiv h)
    ⟨fun x y => Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (sLEquiv_of_idealClass_eq hD h),
      fun c => let ⟨f, hf⟩ := idealClass_surjective hD c; ⟨Quotient.mk _ f, hf⟩⟩

/-- $\mathrm{Cl}(\mathbb{Z}[\omega]) \cong \mathrm{Cl}(\mathcal O_{K_D})$ (`orderEquiv`). -/
noncomputable def classGroupEquiv (D : ℤ) [IsQuadDisc D] : ClassGroup (QOrder D) ≃* ClassGroup (𝓞 (QField D)) :=
  ClassGroup.mulEquiv (orderEquiv D).toRingEquiv

/-- **The theorem of forms and ideals** ($D < 0$ fundamental): the proper ($\mathrm{SL}_2(\mathbb{Z})$-) classes of
primitive positive definite forms of discriminant $D$ are in bijection with $\mathrm{Cl}(\mathcal O_{K_D})$, via
$f \mapsto [\mathfrak a_f]$, $\mathfrak a_f = \mathbb{Z}a + \mathbb{Z}\frac{-b + \sqrt D}{2}$ (up to the sign of the second generator).
Source: Cox, Thm. 7.7 (ii). -/
@[kb "cox2013" "§7.B, Thm. 7.7 (ii)"]
noncomputable def slClassEquiv (hD : D < 0) : Quotient (slSetoid D) ≃ ClassGroup (𝓞 (QField D)) :=
  (slClassEquivOrder hD).trans (classGroupEquiv D).toEquiv

/-- **The number of proper classes is the class number:** $\#\{\mathrm{SL}_2(\mathbb{Z})\text{-classes}\} = h(D)$. -/
@[kb "cox2013" "§7.B, Thm. 7.7 (ii)"]
theorem card_slClasses (hD : D < 0) : Nat.card (Quotient (slSetoid D)) = classNumber (QField D) := by
  rw [Nat.card_congr (slClassEquiv hD), classNumber, Nat.card_eq_fintype_card]

theorem finite_slClasses (hD : D < 0) : Finite (Quotient (slSetoid D)) :=
  Finite.of_equiv _ (slClassEquiv hD).symm

/-! ### $\mathrm{GL}_2(\mathbb{Z})$-classes: the class group modulo inversion -/

/-- **The opposite form** $\bar f = (a, -b, c)$ of a primitive positive definite form. -/
def PrimPosForm.conj (f : PrimPosForm D) : PrimPosForm D :=
  ⟨conjForm f.1, by rw [disc_conjForm]; exact f.2.1,
    (posDef_iff_posDef' _).mpr ⟨by simpa using f.a_pos, by
      rw [disc_conjForm]; exact ((posDef_iff_posDef' _).mp f.2.2.1).2⟩,
    isPrimitive_conjForm f.2.2.2⟩

/-- **The opposite form has the inverse class:** $[\mathfrak a_{\bar f}] = [\mathfrak a_f]^{-1}$, since
$\bar{\mathfrak a}_f\,\mathfrak a_f = (a)$ (`formIdeal_conj_mul`). Source: Cox, Lemma 7.14 [unverified locator] and Thm. 7.7. -/
@[kb "cox2013" "§7.C, Lemma 7.14 [unverified locator]"]
theorem idealClass_conj (f : PrimPosForm D) : idealClass f.conj = (idealClass f)⁻¹ := by
  unfold idealClass
  rw [ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨(f.1.a : QOrder D), by exact_mod_cast f.a_pos.ne', formIdeal_conj_mul f.2.1 f.2.2.2⟩

/-- **The class group modulo inversion**: the orbits of $\{\pm 1\}$ acting on $\mathrm{Cl}$ by $c \mapsto c^{\pm 1}$
(written additively, `Additive G`, so that $\mathbb{Z}^\times$ acts by $u \cdot c = u c$). Two classes are identified iff
$c' = c$ or $c' = c^{-1}$ (`orbitRel_inv_iff`). -/
abbrev ModInv (G : Type*) [CommGroup G] : Type _ := MulAction.orbitRel.Quotient ℤˣ (Additive G)

omit [IsQuadDisc D] in
/-- The orbit relation of $\pm 1$ on $\mathrm{Cl}$: $c \sim c'$ iff $c = c'$ or $c = c'^{-1}$. -/
theorem orbitRel_inv_iff {G : Type*} [CommGroup G] (x y : G) :
    MulAction.orbitRel ℤˣ (Additive G) (Additive.ofMul x) (Additive.ofMul y) ↔ x = y ∨ x = y⁻¹ := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · left; simpa using hu.symm
    · right
      rw [Units.smul_def] at hu
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at hu
      rw [← Additive.ofMul.injective.eq_iff]; simp [← hu]
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · refine ⟨-1, ?_⟩
      rw [Units.smul_def]; simp

/-- **$\mathrm{GL}_2(\mathbb{Z})$-classes ↔ ideal classes modulo inversion** ($D < 0$ fundamental), in the
convention of this repository (classes are $\mathrm{GL}_2(\mathbb{Z})$-classes, `Siegel.IntEquiv`): $[f]_{\mathrm{GL}} \mapsto \{[\mathfrak a_f],
[\mathfrak a_f]^{-1}\}$. A $\mathrm{GL}$-class is a proper class together with its opposite (`intEquiv_iff_sLEquiv_or`), and
the opposite form has the inverse ideal class (`idealClass_conj`). Source: Cox, §2.A [unverified locator] and Thm. 7.7. -/
@[kb "cox2013" "§2.A; §7.B, Thm. 7.7 [unverified locator]"]
noncomputable def glClassEquivOrder (hD : D < 0) : Quotient (glSetoid D) ≃ ModInv (ClassGroup (QOrder D)) :=
  Equiv.ofBijective
    (Quotient.lift (fun f => (Quotient.mk _ (Additive.ofMul (idealClass f)) : ModInv _)) fun f g h => by
      apply Quotient.sound
      change MulAction.orbitRel _ _ _ _
      rw [orbitRel_inv_iff]
      rcases (intEquiv_iff_sLEquiv_or _ _).mp h with h | h
      · exact Or.inl (idealClass_eq_of_sLEquiv h)
      · have := idealClass_eq_of_sLEquiv (f := f.conj) h
        rw [idealClass_conj] at this
        exact Or.inr (by rw [← this, inv_inv]))
    ⟨fun x y => Quotient.inductionOn₂ x y fun f g h => by
      have h' := Quotient.exact h
      change MulAction.orbitRel _ _ _ _ at h'
      rw [orbitRel_inv_iff] at h'
      apply Quotient.sound
      change Siegel.IntEquiv f.1 g.1
      rcases h' with h' | h'
      · exact (sLEquiv_of_idealClass_eq hD h').intEquiv
      · rw [← idealClass_conj] at h'
        have := sLEquiv_of_idealClass_eq hD h'
        exact Siegel.IsometricGL.symm ((intEquiv_iff_sLEquiv_or _ _).mpr (Or.inr this.symm)),
    fun c => Quotient.inductionOn c fun c => by
      obtain ⟨f, hf⟩ := idealClass_surjective hD (Additive.toMul c)
      exact ⟨Quotient.mk _ f, by simp [hf]⟩⟩

omit [IsQuadDisc D] in
/-- **Counting orbits of inversion** (Burnside for $\{\pm 1\}$): for a finite abelian group $G$,
$2\,\#(G/\{c \sim c^{-1}\}) = \#G + \#\{c : c^2 = 1\}$. -/
theorem two_mul_card_modInv (G : Type*) [CommGroup G] [Finite G] :
    2 * Nat.card (ModInv G) = Nat.card G + Nat.card {x : G // x ^ 2 = 1} := by
  classical
  have := Fintype.ofFinite G
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ℤˣ (Additive G)
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} by decide, Finset.sum_pair (by decide),
    Fintype.card_units_int] at hB
  have h1 : Fintype.card (MulAction.fixedBy (Additive G) (1 : ℤˣ)) = Nat.card G := by
    rw [← Nat.card_eq_fintype_card]
    simp only [MulAction.fixedBy_one_eq_univ]
    rw [Nat.card_univ]; rfl
  have h2 : Fintype.card (MulAction.fixedBy (Additive G) (-1 : ℤˣ)) = Nat.card {x : G // x ^ 2 = 1} := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, ?_⟩
        invFun := fun x => ⟨Additive.ofMul x.1, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx := x.2
      rw [MulAction.mem_fixedBy, Units.smul_def] at hx
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_eq_iff_eq_neg] at hx
      have : Additive.toMul x.1 = (Additive.toMul x.1)⁻¹ := by
        conv_lhs => rw [hx]
        rfl
      rw [sq]
      nth_rewrite 2 [this]
      exact mul_inv_cancel _
    · rw [MulAction.mem_fixedBy, Units.smul_def]
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
      have hx := x.2
      rw [sq, mul_eq_one_iff_eq_inv] at hx
      rw [neg_eq_iff_eq_neg]
      show Additive.ofMul x.1 = Additive.ofMul (x.1)⁻¹
      rw [← hx]
  rw [h1, h2, ← Nat.card_eq_fintype_card] at hB
  rw [hB, mul_comm]

/-- **The number of $\mathrm{GL}_2(\mathbb{Z})$-classes** ($D < 0$ fundamental): with $h = h(D)$ and
$\mathrm{Cl}[2] = \{c \in \mathrm{Cl}(\mathcal O_{K_D}) : c^2 = 1\}$ (the ambiguous classes),
$$2\,\#\{\mathrm{GL}_2(\mathbb{Z})\text{-classes of primitive positive definite forms of discriminant } D\} = h + \#\mathrm{Cl}[2].$$
A proper class with $[f] = [\bar f]$ (an ambiguous class) is a whole $\mathrm{GL}$-class; the others pair up. -/
@[kb "cox2013" "§2.A; §7.B, Thm. 7.7 [unverified locator]"]
theorem two_mul_card_glClasses (hD : D < 0) :
    2 * Nat.card (Quotient (glSetoid D)) =
      classNumber (QField D) + Nat.card {c : ClassGroup (𝓞 (QField D)) // c ^ 2 = 1} := by
  have : Finite (ClassGroup (QOrder D)) := Finite.of_equiv _ (classGroupEquiv D).toEquiv.symm
  rw [Nat.card_congr (glClassEquivOrder hD), two_mul_card_modInv, classNumber, ← Nat.card_eq_fintype_card,
    Nat.card_congr (classGroupEquiv D).toEquiv]
  congr 1
  exact Nat.card_congr ((classGroupEquiv D).toEquiv.subtypeEquiv fun c => by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← map_pow, map_eq_one_iff _ (classGroupEquiv D).injective])

omit [IsQuadDisc D] in
/-- An isomorphism of groups induces a bijection of the classes modulo inversion. -/
def ModInv.congr {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) : ModInv G ≃ ModInv H :=
  Quotient.congr (Additive.toMul.trans (e.toEquiv.trans Additive.ofMul)) fun x y => by
    obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective y
    show MulAction.orbitRel _ _ (Additive.ofMul x) (Additive.ofMul y) ↔
      MulAction.orbitRel _ _ (Additive.ofMul (e x)) (Additive.ofMul (e y))
    rw [orbitRel_inv_iff, orbitRel_inv_iff, ← map_inv e, e.injective.eq_iff, e.injective.eq_iff]

/-- **$\mathrm{GL}_2(\mathbb{Z})$-classes ↔ $\mathrm{Cl}(\mathcal O_{K_D})$ modulo inversion** ($D < 0$ fundamental; the convention
of this repository). See `glClassEquivOrder`. -/
@[kb "cox2013" "§2.A; §7.B, Thm. 7.7 [unverified locator]"]
noncomputable def glClassEquiv (hD : D < 0) : Quotient (glSetoid D) ≃ ModInv (ClassGroup (𝓞 (QField D))) :=
  (glClassEquivOrder hD).trans (ModInv.congr (classGroupEquiv D))

end QuadFormsKB.Binary
