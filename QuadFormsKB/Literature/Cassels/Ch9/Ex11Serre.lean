/-
# Cassels, Chapter 9, Example 11 (ii): odd indefinite unimodular forms are determined by their signature

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 11 (ii), p. 164 (attributed to
Serre). Companion to `Ch9/Ex11.lean`, which states (ii) as `Ex11_ii` and proves (i) (`ex11_i`).

**Conventions** as in `Ch9/Ex11.lean`: forms `QuadForm ℤ n` (0-based variables $x_0, \dots, x_{n-1}$); *classically
integral of determinant $\pm 1$* is `IsUnimodularCI`; *indefinite* is `IsIndefinite` (a positive and a negative real
value); *properly primitive* is `Siegel.IsProperlyPrimitive`; equivalence over $\mathbb Z$ is `Siegel.IntEquiv`
($\mathrm{GL}_n(\mathbb Z)$), over $\mathbb R$ it is `QuadForm.IsometricIn ℝ`. A *sign vector* $\varepsilon$
(`IsSignVec`) has all entries $\pm 1$; the *sign-diagonal form* is $\langle \varepsilon \rangle(\mathbf x) =
\sum_i \varepsilon_i x_i^2$ (`QuadForm.diag ε`).

**Proves (unconditionally).**
* `exists_signDiag` (the classical normal form, Serre, *A Course in Arithmetic*, Ch. V, §2.2, Thm. 4 for odd forms): an
  indefinite properly primitive classically integral form of determinant $\pm 1$ is equivalent over $\mathbb Z$ to a
  sign-diagonal form $\langle \varepsilon \rangle$.
* `ex11_ii_holds` (**Cassels, Ch. 9, Ex. 11 (ii)**): the named statement `Ex11_ii` holds.

**Route (elementary, no local theory).** By (i) (`ex11_i`) $f \cong y_0^2 - y_1^2 + g$ with $g$ unimodular in $n - 2$
variables. For $n = 2$ this is $\langle 1, -1 \rangle$. Otherwise choose $\delta = \pm 1$ with $h = \delta y^2 + g$
indefinite ($\delta = 1$ if $g$ is indefinite or negative definite, $\delta = -1$ if $g$ is positive definite; a unimodular
form which is not indefinite is definite, `posDef_or_posDef_neg`). Then $h$ is unimodular, indefinite and properly
primitive in $n - 1$ variables, so by induction $h \cong \langle \varepsilon' \rangle$, and
$f \cong \langle -\delta \rangle \perp h \cong \langle -\delta, \varepsilon' \rangle$ (after a permutation of the first two
variables when $\delta = 1$). Two sign-diagonal forms which are equivalent over $\mathbb R$ have the same number of
negative entries (Sylvester's law of inertia, `HasseIsoNF.negCountR_eq_of_isometric`, from Mathlib), hence differ by a
permutation of the variables, which is an equivalence over $\mathbb Z$.
-/
import QuadFormsKB.Literature.Cassels.Ch9.Ex11
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch9Ex11

open QuadFormsKB QuadFormsKB.Siegel

variable {n m : ℕ}

/-! ### Sign vectors and sign-diagonal forms -/

/-- **Sign vector:** every entry of $\varepsilon \in \mathbb Z^n$ is $1$ or $-1$. Argument `ε`: the vector. -/
def IsSignVec (ε : Fin n → ℤ) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

/-- **$f$ is equivalent to a sign-diagonal form:** there is a sign vector $\varepsilon$ with
$f \cong_{\mathbb Z} \langle \varepsilon \rangle = \sum_i \varepsilon_i x_i^2$. Argument `f`: the form. -/
def IsSignDiag (f : QuadForm ℤ n) : Prop := ∃ ε : Fin n → ℤ, IsSignVec ε ∧ IntEquiv f (QuadForm.diag ε)

/-- Helper: values of a diagonal integral form over any commutative ring $K$: $\langle a \rangle(\mathbf x) =
\sum_i a_i x_i^2$. -/
theorem evalIn_diag_int {K : Type*} [CommRing K] (a : Fin n → ℤ) (x : Fin n → K) :
    (QuadForm.diag a).evalIn K x = ∑ i, (a i : K) * x i ^ 2 := by
  simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- Helper: values of a diagonal integral form over $\mathbb Z$. -/
theorem eval_diag_int (a : Fin n → ℤ) (x : Fin n → ℤ) : (QuadForm.diag a).eval x = ∑ i, a i * x i ^ 2 := by
  rw [QuadForm.eval, evalIn_diag_int]; simp

/-- Helper: a permutation $\sigma$ of the variables gives an equivalence over $\mathbb Z$: if $g(\mathbf x) =
f(\mathbf x \circ \sigma)$ for all $\mathbf x$, then $f \cong g$ (by the permutation matrix of $\sigma$). -/
theorem intEquiv_of_perm {f g : QuadForm ℤ n} (σ : Equiv.Perm (Fin n))
    (h : ∀ x : Fin n → ℤ, g.eval x = f.eval (x ∘ σ)) : IntEquiv f g := by
  have hu : IsUnit (σ.permMatrix ℤ).det := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> simp
  refine ⟨glOfUnit (σ.permMatrix ℤ) hu, fun x => ?_⟩
  rw [glOfUnit_val, Matrix.permMatrix_mulVec, h]

/-- Helper: being equivalent to a sign-diagonal form is invariant under equivalence. -/
theorem IsSignDiag.of_intEquiv {f g : QuadForm ℤ n} (hf : IsSignDiag f) (h : IntEquiv g f) : IsSignDiag g := by
  obtain ⟨ε, hε, e⟩ := hf
  exact ⟨ε, hε, IsometricGL.trans h e⟩

/-- Helper: transport along a bijection of the variables (possibly between `Fin a` and `Fin b` with $a = b$ not
definitionally): if $g(\mathbf x) = f(\mathbf x \circ e^{-1})$ and $f$ is sign-diagonal, so is $g$. -/
theorem IsSignDiag.of_equiv {a b : ℕ} (e : Fin b ≃ Fin a) {f : QuadForm ℤ a} {g : QuadForm ℤ b}
    (hf : IsSignDiag f) (h : ∀ x : Fin b → ℤ, g.eval x = f.eval (x ∘ e.symm)) : IsSignDiag g := by
  have hab : a = b := by simpa using (Fintype.card_congr e).symm
  subst hab
  exact hf.of_intEquiv (IsometricGL.symm (intEquiv_of_perm e.symm h))

/-- Helper: a sign-diagonal form is sign-diagonal. -/
theorem isSignDiag_diag {ε : Fin n → ℤ} (hε : IsSignVec ε) : IsSignDiag (QuadForm.diag ε) :=
  ⟨ε, hε, IsometricGL.refl _⟩

/-- Helper: the block matrix $\operatorname{diag}(S, P)$ is $\operatorname{diag}(S, 1)\operatorname{diag}(1, P)$; its
action on the two blocks of coordinates. -/
theorem blockLin_blockLinR_castAdd {a : ℕ} (S : Matrix (Fin a) (Fin a) ℤ) (P : Matrix (Fin m) (Fin m) ℤ)
    (x : Fin (a + m) → ℤ) :
    (fun i => ((blockLin (m := m) S * blockLinR (a := a) P) *ᵥ x) (Fin.castAdd m i)) =
      S *ᵥ (fun i => x (Fin.castAdd m i)) := by
  rw [← Matrix.mulVec_mulVec, blockLin_mulVec_castAdd, blockLinR_mulVec_castAdd]

/-- Helper: second block of the action of $\operatorname{diag}(S, 1)\operatorname{diag}(1, P)$. -/
theorem blockLin_blockLinR_natAdd {a : ℕ} (S : Matrix (Fin a) (Fin a) ℤ) (P : Matrix (Fin m) (Fin m) ℤ)
    (x : Fin (a + m) → ℤ) :
    (fun j => ((blockLin (m := m) S * blockLinR (a := a) P) *ᵥ x) (Fin.natAdd a j)) =
      P *ᵥ (fun j => x (Fin.natAdd a j)) := by
  rw [← Matrix.mulVec_mulVec, blockLin_mulVec_natAdd, blockLinR_mulVec_natAdd]

/-- Helper: equivalences of the two summands give an equivalence of orthogonal sums. -/
theorem intEquiv_orthSum {a : ℕ} {f f' : QuadForm ℤ a} {g g' : QuadForm ℤ m} (hf : IntEquiv f f')
    (hg : IntEquiv g g') : IntEquiv (QuadForm.orthSum f g) (QuadForm.orthSum f' g') := by
  obtain ⟨S, hS⟩ := hf
  obtain ⟨P, hP⟩ := hg
  have hu : IsUnit (blockLin (m := m) S.val * blockLinR (a := a) P.val).det := by
    rw [Matrix.det_mul, det_blockLin, det_blockLinR]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp S.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit)
  refine ⟨glOfUnit _ hu, fun x => ?_⟩
  rw [glOfUnit_val]
  show (QuadForm.orthSum f g).evalIn ℤ _ = (QuadForm.orthSum f' g').evalIn ℤ x
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, blockLin_blockLinR_castAdd, blockLin_blockLinR_natAdd]
  exact congrArg₂ (· + ·) (hS _) (hP _)

/-- Helper: the orthogonal sum of two diagonal forms is diagonal, $\langle a \rangle \perp \langle b \rangle =
\langle a, b \rangle$ (`Fin.append`), as an equivalence. -/
theorem intEquiv_orthSum_diag {a : ℕ} (u : Fin a → ℤ) (v : Fin m → ℤ) :
    IntEquiv (QuadForm.orthSum (QuadForm.diag u) (QuadForm.diag v)) (QuadForm.diag (Fin.append u v)) := by
  refine ⟨1, fun x => ?_⟩
  rw [Units.val_one, Matrix.one_mulVec]
  show (QuadForm.orthSum (QuadForm.diag u) (QuadForm.diag v)).evalIn ℤ x = (QuadForm.diag (Fin.append u v)).eval x
  rw [QuadForm.evalIn_orthSum, eval_diag_int, evalIn_diag_int, evalIn_diag_int, Fin.sum_univ_add]
  simp

/-- Helper: the orthogonal sum of two sign-diagonal forms is sign-diagonal. -/
theorem IsSignDiag.orthSum {a : ℕ} {f : QuadForm ℤ a} {g : QuadForm ℤ m} (hf : IsSignDiag f) (hg : IsSignDiag g) :
    IsSignDiag (QuadForm.orthSum f g) := by
  obtain ⟨u, hu, eu⟩ := hf
  obtain ⟨v, hv, ev⟩ := hg
  refine ⟨Fin.append u v, fun i => ?_, IsometricGL.trans (intEquiv_orthSum eu ev) (intEquiv_orthSum_diag u v)⟩
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hu i
  · rw [Fin.append_right]; exact hv j

/-! ### The one-variable form $\langle \delta \rangle$ and the form $h = \langle \delta \rangle \perp g$ -/

/-- Helper: the form $\langle \delta \rangle = \delta y^2$ in one variable. Argument `δ`: the coefficient. -/
abbrev unary (δ : ℤ) : QuadForm ℤ 1 := QuadForm.diag ![δ]

/-- Helper: $\langle \delta \rangle$ is the form of the $1 \times 1$ Gram matrix $(\delta)$. -/
theorem unary_eq_ofGram (δ : ℤ) : unary δ = Siegel.ofGram (Matrix.diagonal ![δ]) := by
  apply QuadForm.eq_of_eval_eq
  intro x
  rw [Siegel.eval_ofGram (by simp [Matrix.IsSymm, Matrix.diagonal_transpose]), eval_diag_int]
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal_apply]
  ring

/-- Helper: $\langle \pm 1 \rangle$ is classically integral of determinant $\pm 1$. -/
theorem isUnimodularCI_unary {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : IsUnimodularCI (unary δ) := by
  rw [unary_eq_ofGram]
  refine isUnimodularCI_ofGram (by simp [Matrix.IsSymm, Matrix.diagonal_transpose]) ?_
  rw [Matrix.det_diagonal]
  rcases hδ with rfl | rfl <;> simp

/-- Helper: the values of $h = \langle \delta \rangle \perp g$ on $(t, \mathbf z)$ over a commutative ring. -/
theorem evalIn_unary_orthSum {K : Type*} [CommRing K] (δ : ℤ) (g : QuadForm ℤ m) (t : K) (z : Fin m → K) :
    (QuadForm.orthSum (unary δ) g).evalIn K (Fin.append ![t] z) = (δ : K) * t ^ 2 + g.evalIn K z := by
  rw [QuadForm.evalIn_orthSum, evalIn_diag_int]
  simp

/-- Helper: a unimodular form of positive dimension takes a positive or a negative value at an integer vector, according as
it is positive or negative definite. -/
theorem exists_pos_of_posDef {g : QuadForm ℤ (m + 1)} (hg : IntQF.PosDef g) : 0 < g.eval (Pi.single 0 1) :=
  hg _ (by intro h; have := congrFun h 0; simp at this)

/-- Helper: the real value of an integral form at an integer vector. -/
theorem evalIn_real_intVec (g : QuadForm ℤ m) (x : Fin m → ℤ) :
    g.evalIn ℝ (fun i => (x i : ℝ)) = (g.eval x : ℝ) := Siegel.evalIn_intCast g x

/-- Helper: given a unimodular $g$ in $m + 1$ variables, there is $\delta = \pm 1$ with $\langle \delta \rangle \perp g$
indefinite: $\delta = 1$ unless $g$ is positive definite, $\delta = -1$ then. -/
theorem exists_delta {g : QuadForm ℤ (m + 1)} (hg : IsUnimodularCI g) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ IsIndefinite (QuadForm.orthSum (unary δ) g) := by
  by_cases hpd : IntQF.PosDef g
  · refine ⟨-1, Or.inr rfl, ⟨Fin.append ![0] (fun i => ((Pi.single 0 1 : Fin (m + 1) → ℤ) i : ℝ)), ?_⟩,
      ⟨Fin.append ![1] 0, ?_⟩⟩
    · rw [evalIn_unary_orthSum, evalIn_real_intVec]
      have := exists_pos_of_posDef hpd
      have : (0 : ℝ) < (g.eval (Pi.single 0 1) : ℝ) := by exact_mod_cast this
      simpa using this
    · rw [evalIn_unary_orthSum]
      simp [QuadForm.evalIn]
  · refine ⟨1, Or.inl rfl, ⟨Fin.append ![1] 0, ?_⟩, ?_⟩
    · rw [evalIn_unary_orthSum]
      simp [QuadForm.evalIn]
    · by_cases hind : IsIndefinite g
      · obtain ⟨-, ⟨y, hy⟩⟩ := hind
        refine ⟨Fin.append ![0] y, ?_⟩
        rw [evalIn_unary_orthSum]
        simpa using hy
      · rcases posDef_or_posDef_neg hg hind with h | h
        · exact absurd h hpd
        · refine ⟨Fin.append ![0] (fun i => ((Pi.single 0 1 : Fin (m + 1) → ℤ) i : ℝ)), ?_⟩
          rw [evalIn_unary_orthSum, evalIn_real_intVec]
          have h1 := exists_pos_of_posDef h
          rw [eval_negForm] at h1
          have : (g.eval (Pi.single 0 1) : ℝ) < 0 := by exact_mod_cast (by omega : g.eval (Pi.single 0 1) < 0)
          simpa using this

/-- Helper: $\langle \pm 1 \rangle \perp g$ is properly primitive for unimodular $g$ (its value at $(1, \mathbf 0)$ is
odd). -/
theorem isProperlyPrimitive_unary_orthSum {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {g : QuadForm ℤ m} (hg : IsUnimodularCI g) :
    IsProperlyPrimitive (QuadForm.orthSum (unary δ) g) := by
  have hu := isUnimodularCI_orthSum (isUnimodularCI_unary hδ) hg
  refine ⟨isPrimitiveCI_of_unimodular (by omega) hu, ?_⟩
  by_contra hall
  push Not at hall
  have h2 := (diag_even_iff hu.1).mp (fun i => hall i) (Fin.append ![1] 0)
  have e := evalIn_unary_orthSum (K := ℤ) δ g 1 0
  rw [show g.evalIn ℤ 0 = 0 by simp [QuadForm.evalIn]] at e
  have e' : (QuadForm.orthSum (unary δ) g).eval (Fin.append ![1] 0) = δ := by
    rw [QuadForm.eval, e]; simp
  rw [e'] at h2
  rcases hδ with rfl | rfl <;> omega

/-! ### The normal form -/

/-- Helper: $y_0^2 - y_1^2 + g$ in $2 + 0$ variables is $\langle 1, -1 \rangle$. -/
theorem isSignDiag_oddPlane_zero (g : QuadForm ℤ 0) : IsSignDiag (QuadForm.orthSum oddPlane g) := by
  have hε : IsSignVec (Fin.append ![1, -1] (Fin.elim0 : Fin 0 → ℤ)) := by
    intro i; fin_cases i <;> simp [Fin.append, Fin.addCases]
  refine ⟨_, hε, ⟨1, fun x => ?_⟩⟩
  rw [Units.val_one, Matrix.one_mulVec]
  show (QuadForm.orthSum oddPlane g).evalIn ℤ x = _
  rw [QuadForm.evalIn_orthSum, eval_diag_int, Fin.sum_univ_add]
  have h0 : g.evalIn ℤ (fun b => x (Fin.natAdd 2 b)) = 0 := eval_dim_zero g _
  rw [h0]
  have := eval_oddPlane (fun a => x (Fin.castAdd 0 a))
  simp only [QuadForm.eval] at this
  rw [this]
  simp [Fin.sum_univ_two]
  ring

/-- Helper: $y_0^2 - y_1^2 \cong \langle -\delta, \delta \rangle$ for $\delta = \pm 1$ (the identity, or the transposition of
the two variables). -/
theorem oddPlane_equiv {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) : IntEquiv oddPlane (QuadForm.diag ![-δ, δ]) := by
  rcases hδ with rfl | rfl
  · refine intEquiv_of_perm (Equiv.swap 0 1) fun x => ?_
    rw [eval_diag_int, eval_oddPlane]
    simp [Fin.sum_univ_two]
    ring
  · refine intEquiv_of_perm 1 fun x => ?_
    rw [eval_diag_int, eval_oddPlane]
    simp [Fin.sum_univ_two]
    ring

/-- **The normal form of odd indefinite unimodular forms** (Serre, *A Course in Arithmetic*, Ch. V, §2.2, Thm. 4; the
step behind Cassels, Ch. 9, Ex. 11 (ii)): an indefinite properly primitive classically integral form of determinant
$\pm 1$ is equivalent over $\mathbb Z$ to $\sum_i \varepsilon_i x_i^2$ with all $\varepsilon_i = \pm 1$. -/
theorem exists_signDiag : ∀ (n : ℕ) (f : QuadForm ℤ n), IsUnimodularCI f → IsIndefinite f →
    IsProperlyPrimitive f → IsSignDiag f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hind hprop
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by have := two_le_of_isIndefinite hind; omega⟩
    obtain ⟨g, hg, hfg⟩ := ex11_i f hf hind hprop
    refine IsSignDiag.of_intEquiv ?_ hfg
    rcases m with _ | k
    · exact isSignDiag_oddPlane_zero g
    · obtain ⟨δ, hδ, hhind⟩ := exists_delta hg
      have hh : IsSignDiag (QuadForm.orthSum (unary δ) g) :=
        ih (1 + (k + 1)) (by omega) _ (isUnimodularCI_orthSum (isUnimodularCI_unary hδ) hg) hhind
          (isProperlyPrimitive_unary_orthSum hδ hg)
      have hF : IsSignDiag (QuadForm.orthSum (unary (-δ)) (QuadForm.orthSum (unary δ) g)) := by
        refine IsSignDiag.orthSum (isSignDiag_diag ?_) hh
        intro i; fin_cases i; rcases hδ with rfl | rfl <;> simp
      -- `y₀² - y₁² + g ≅ (-δ)y₀² + δy₁² + g`, then reindex `Fin (2 + (k + 1)) ≃ Fin (1 + (1 + (k + 1)))`
      refine IsSignDiag.of_intEquiv ?_ (intEquiv_orthSum (oddPlane_equiv hδ) (IsometricGL.refl g))
      have hn : 1 + (1 + (k + 1)) = 2 + (k + 1) := by omega
      refine hF.of_equiv (finCongr hn.symm) fun x => ?_
      show (QuadForm.orthSum (QuadForm.diag ![-δ, δ]) g).evalIn ℤ x = (QuadForm.orthSum (unary (-δ))
        (QuadForm.orthSum (unary δ) g)).evalIn ℤ _
      rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, evalIn_diag_int,
        evalIn_diag_int, evalIn_diag_int]
      have e0 : (finCongr hn.symm).symm (Fin.castAdd (1 + (k + 1)) (0 : Fin 1)) = Fin.castAdd (k + 1) (0 : Fin 2) :=
        Fin.ext (by simp)
      have e1 : (finCongr hn.symm).symm (Fin.natAdd 1 (Fin.castAdd (k + 1) (0 : Fin 1))) =
          Fin.castAdd (k + 1) (1 : Fin 2) := Fin.ext (by simp)
      have e2 : ∀ b : Fin (k + 1), (finCongr hn.symm).symm (Fin.natAdd 1 (Fin.natAdd 1 b)) = Fin.natAdd 2 b :=
        fun b => Fin.ext (by simp; omega)
      simp only [Function.comp_apply, Fin.sum_univ_one, Fin.sum_univ_two, e0, e1, e2]
      simp
      ring

/-! ### Sylvester's law and the proof of (ii) -/

/-- Helper: the number of negative entries of a sign vector, read in $\mathbb R$, is an invariant of real equivalence of
the sign-diagonal forms (Sylvester's law of inertia, `HasseIsoNF.negCountR_eq_of_isometric`). -/
theorem negCountR_eq_of_isometricIn {ε ε' : Fin n → ℤ}
    (h : (QuadForm.diag ε).IsometricIn ℝ (QuadForm.diag ε')) :
    HasseIsoNF.negCountR (fun i => (ε i : ℝ)) = HasseIsoNF.negCountR (fun i => (ε' i : ℝ)) := by
  apply HasseIsoNF.negCountR_eq_of_isometric
  obtain ⟨P, hP, e⟩ := h
  refine ⟨P, hP, fun x => ?_⟩
  have h1 := e x
  rw [evalIn_diag_int, evalIn_diag_int] at h1
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
  simpa using h1

/-- Helper: the number of entries $-1$ of a sign vector, as the cardinality of a subtype. -/
theorem card_neg_eq (ε : Fin n → ℤ) :
    HasseIsoNF.negCountR (fun i => (ε i : ℝ)) = Fintype.card {i // decide (ε i < 0) = true} := by
  rw [HasseIsoNF.negCountR, Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((ε i : ℝ) < 0) ↔ ε i < 0 := by exact_mod_cast Iff.rfl
  by_cases h : ε i < 0 <;> simp [h, this]

/-- Helper: two sign vectors with the same number of entries $-1$ differ by a permutation. -/
theorem exists_perm_of_negCount {ε ε' : Fin n → ℤ} (hε : IsSignVec ε) (hε' : IsSignVec ε')
    (h : HasseIsoNF.negCountR (fun i => (ε i : ℝ)) = HasseIsoNF.negCountR (fun i => (ε' i : ℝ))) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ε (σ i) = ε' i := by
  rw [card_neg_eq, card_neg_eq] at h
  have e : ∀ c : Bool, {i // decide (ε' i < 0) = c} ≃ {i // decide (ε i < 0) = c} := fun c => by
    apply Fintype.equivOfCardEq
    cases c
    · have h1 := Fintype.card_subtype_compl (fun i : Fin n => decide (ε i < 0) = true)
      have h2 := Fintype.card_subtype_compl (fun i : Fin n => decide (ε' i < 0) = true)
      simp only [Bool.not_eq_true, Fintype.card_fin] at h1 h2
      rw [h1, h2, h]
    · exact h.symm
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_⟩
  have hd : decide (ε (Equiv.ofFiberEquiv e i) < 0) = decide (ε' i < 0) := Equiv.ofFiberEquiv_map e i
  rw [decide_eq_decide] at hd
  rcases hε (Equiv.ofFiberEquiv e i) with h1 | h1 <;> rcases hε' i with h2 | h2 <;> rw [h1, h2] at hd ⊢ <;>
    simp at hd ⊢

/-- **Cassels, Ch. 9, Ex. 11 (ii)** (p. 164): *if $f_1, f_2$ are indefinite and properly primitive (classically integral
of determinant $\pm 1$) and equivalent over $\mathbb R$, then they are equivalent over $\mathbb Z$.* The named statement
`Ex11_ii` holds, unconditionally. *Proof:* both are equivalent to sign-diagonal forms (`exists_signDiag`); these are
equivalent over $\mathbb R$, so they have the same number of entries $-1$ (Sylvester) and differ by a permutation of the
variables. -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (ii), p. 164 (proof)"]
theorem ex11_ii_holds : Ex11_ii := by
  intro m f₁ f₂ hu₁ hu₂ hi₁ hi₂ hp₁ hp₂ hR
  obtain ⟨ε₁, hε₁, e₁⟩ := exists_signDiag _ f₁ hu₁ hi₁ hp₁
  obtain ⟨ε₂, hε₂, e₂⟩ := exists_signDiag _ f₂ hu₂ hi₂ hp₂
  have hci : ∀ {ε : Fin (2 + m) → ℤ}, IsSignVec ε → IsClassicallyIntegral (QuadForm.diag ε) := fun {ε} hε => by
    have : QuadForm.diag ε = Siegel.ofGram (Matrix.diagonal ε) := by
      apply QuadForm.eq_of_eval_eq
      intro x
      rw [Siegel.eval_ofGram (by simp [Matrix.IsSymm, Matrix.diagonal_transpose]), eval_diag_int]
      simp [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, sq, mul_comm, mul_left_comm]
    rw [this]
    exact Siegel.ci_ofGram (by simp [Matrix.IsSymm, Matrix.diagonal_transpose])
  have hR' : (QuadForm.diag ε₁).IsometricIn ℝ (QuadForm.diag ε₂) :=
    isometricIn_real_trans (isometricIn_real_symm (isometricIn_real_of_intEquiv hu₁.1 (hci hε₁) e₁))
      (isometricIn_real_trans hR (isometricIn_real_of_intEquiv hu₂.1 (hci hε₂) e₂))
  obtain ⟨σ, hσ⟩ := exists_perm_of_negCount hε₁ hε₂ (negCountR_eq_of_isometricIn hR')
  have hperm : IntEquiv (QuadForm.diag ε₁) (QuadForm.diag ε₂) := by
    refine intEquiv_of_perm σ.symm fun x => ?_
    rw [eval_diag_int, eval_diag_int]
    rw [← Equiv.sum_comp σ (fun j => ε₁ j * (x ∘ ⇑σ.symm) j ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hσ]
  exact IsometricGL.trans e₁ (IsometricGL.trans hperm (IsometricGL.symm e₂))

end QuadFormsKB.Cassels.Ch9Ex11
