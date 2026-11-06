/-
# Cassels, Chapter 13, §6: representation by anisotropic ternaries

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §6, *Representation by anisotropic ternaries*,
pp. 303–306: reduced representations of $m < 0$ (Theorem 6.2) and of $m > 0$ (copolar points (6.15), Theorem 6.3)
with respect to a fundamental polygon $\mathcal P$ of Theorem 6.1 (`exists_fundamental_polygon`).

Setting as in `Ch13/Sec8.lean`: $f$ integral ternary, $F = L^{\mathsf T}\operatorname{diag}(1, 1, -1)L$, so
$f = X_0^2 + X_1^2 - X_2^2$ with $X = L\vec{x}$ ("$f$ is $\mathbb{R}$-equivalent to $X_1^2 + X_2^2 - X_3^2$");
$\pi(\vec{x}) = (X_0/X_2, X_1/X_2)$ (`projPt (L *ᵥ x)`). The theorems are stated for any convex set $\mathcal P$ with the
property (i) of Theorem 6.1 lying in a disc of radius $r < 1$ (Theorem 6.1, Corollary); the $\mathcal P$ of Theorem 6.1
is one.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec8

open Matrix

namespace QuadFormsKB.Reduction

/-! ### Helpers: the Lorentz bilinear form and projective facts -/

/-- Helper: the Lorentz bilinear form $B(X, Y) = X_0Y_0 + X_1Y_1 - X_2Y_2$. -/
private def lbil (X Y : Fin 3 → ℝ) : ℝ := X 0 * Y 0 + X 1 * Y 1 - X 2 * Y 2

/-- Helper: `lbil` as a dot product with `lorentz`. -/
private theorem lbil_eq (X Y : Fin 3 → ℝ) : X ⬝ᵥ (lorentz *ᵥ Y) = lbil X Y := by
  simp [lorentz, lbil, dotProduct, Fin.sum_univ_three, mulVec_diagonal]
  ring

/-- Helper: $A = LTL^{-1}$ satisfies $A^{\mathsf T}\,\mathrm{lorentz}\,A = \mathrm{lorentz}$ for a real automorph $T$. -/
private theorem conj_lorentz {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * realMat Q * T = realMat Q) :
    (L * T * L⁻¹)ᵀ * lorentz * (L * T * L⁻¹) = lorentz := by
  have h1 : (L * T * L⁻¹)ᵀ * lorentz * (L * T * L⁻¹) =
      (L⁻¹)ᵀ * (Tᵀ * (Lᵀ * lorentz * L) * T) * L⁻¹ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, ← hF, hT, hF]
  have h2 : (L⁻¹)ᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv L hL, Matrix.transpose_one]
  calc (L⁻¹)ᵀ * (Lᵀ * lorentz * L) * L⁻¹ = ((L⁻¹)ᵀ * Lᵀ) * lorentz * (L * L⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = lorentz := by rw [h2, Matrix.mul_nonsing_inv L hL]; simp

/-- Helper: such an $A$ preserves the Lorentz bilinear form. -/
private theorem lbil_pres {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * lorentz * A = lorentz) (X Y : Fin 3 → ℝ) :
    lbil (A *ᵥ X) (A *ᵥ Y) = lbil X Y := by
  rw [← lbil_eq, ← lbil_eq]
  conv_rhs => rw [← hA]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec X,
    Matrix.vecMul_transpose]

/-- Helper: $\pi(cY) = \pi(Y)$ for $c \ne 0$. -/
private theorem projPt_smul_aux {c : ℝ} (hc : c ≠ 0) (Y : Fin 3 → ℝ) : projPt (c • Y) = projPt Y := by
  ext i
  fin_cases i <;> simp [projPt, mul_div_mul_left _ _ hc]

/-- Helper: the lift of the projection is the rescaling to last coordinate $1$. -/
private theorem liftPt_projPt_aux {X : Fin 3 → ℝ} (h : X 2 ≠ 0) : liftPt (projPt X) = (X 2)⁻¹ • X := by
  ext i
  fin_cases i <;> simp [liftPt, projPt, h, div_eq_inv_mul]

/-- Helper: $A(\mathrm{lift}\,\pi X) = X_2^{-1}\,AX$. -/
private theorem mulVec_liftPt_projPt_aux (A : Matrix (Fin 3) (Fin 3) ℝ) {X : Fin 3 → ℝ} (h : X 2 ≠ 0) :
    A *ᵥ liftPt (projPt X) = (X 2)⁻¹ • (A *ᵥ X) := by
  rw [liftPt_projPt_aux h, Matrix.mulVec_smul]

/-- Helper: projective fact, $\mathrm{flt}_A(\pi X) = \pi(AX)$ when both are defined. -/
private theorem flt_projPt (A : Matrix (Fin 3) (Fin 3) ℝ) {X : Fin 3 → ℝ} (h : X 2 ≠ 0) :
    flt A (projPt X) = projPt (A *ᵥ X) := by
  unfold flt
  rw [mulVec_liftPt_projPt_aux A h, projPt_smul_aux (inv_ne_zero h)]

/-- Helper: $B(\ell\xi, \ell\xi) = |\xi|^2 - 1$. -/
private theorem lbil_liftPt_self (ξ : Fin 2 → ℝ) : lbil (liftPt ξ) (liftPt ξ) = ξ 0 ^ 2 + ξ 1 ^ 2 - 1 := by
  simp [lbil, liftPt]; ring

/-- Helper: $B(Y, Y) < 0$ forces $Y_2 \ne 0$. -/
private theorem two_ne_zero_of_lbil_neg {Y : Fin 3 → ℝ} (h : lbil Y Y < 0) : Y 2 ≠ 0 := by
  intro h2
  simp only [lbil, h2] at h
  nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1)]

/-- Helper: the value of the integral form is the Lorentz value of $L\vec{x}$. -/
private theorem eval_eq_lbil {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hF : realMat Q = Lᵀ * lorentz * L) (c : Fin 3 → ℤ) :
    ((Q.eval c : ℤ) : ℝ) = lbil (L *ᵥ cast c) (L *ᵥ cast c) := by
  have : ((Q.eval c : ℤ) : ℝ) = val (realMat Q) (cast c) := by
    rw [← QuadForm.evalIn_real_eq_val]
    simp [QuadForm.evalIn, cast]
  rw [this, ← lbil_eq, hF, val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Helper: $L\,\widetilde{(Tc)} = A\,(L\tilde c)$ for $A = L \tilde T L^{-1}$. -/
private theorem L_cast_mulVec {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (T : Matrix (Fin 3) (Fin 3) ℤ)
    (c : Fin 3 → ℤ) : L *ᵥ cast (T *ᵥ c) = (L * castM T * L⁻¹) *ᵥ (L *ᵥ cast c) := by
  have h : L * castM T * L⁻¹ * L = L * castM T := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul L hL, Matrix.mul_one]
  rw [← castM_mulVec_cast, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/-- Helper: integer vectors with bounded real coordinates form a finite set. -/
private theorem finite_bdd (C : ℝ) : {b : Fin 3 → ℤ | ∀ i, |(b i : ℝ)| ≤ C}.Finite := by
  apply (Set.Finite.pi (t := fun _ : Fin 3 => Set.Icc (-⌈C⌉) ⌈C⌉) (fun _ => Set.finite_Icc _ _)).subset
  intro b hb i _
  have hab := abs_le.mp (hb i)
  have hc : C ≤ (⌈C⌉ : ℝ) := Int.le_ceil C
  have h1 : ((b i : ℤ) : ℝ) ≤ ⌈C⌉ := hab.2.trans hc
  have h2 : (-(⌈C⌉ : ℤ) : ℝ) ≤ b i := by
    linarith [hab.1]
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h1

/-- Helper: a linear image of a coordinatewise-bounded vector is coordinatewise-bounded. -/
private theorem bdd_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) : ∃ C : ℝ, ∀ (X : Fin 3 → ℝ) (B : ℝ), 0 ≤ B →
    (∀ j, |X j| ≤ B) → ∀ i, |(M *ᵥ X) i| ≤ C * B := by
  let _ := Matrix.linftyOpNormedAddCommGroup (m := Fin 3) (n := Fin 3) (α := ℝ)
  refine ⟨‖M‖, fun X B hB hX i => ?_⟩
  have h1 : ‖X‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).2 (fun j => by simpa using hX j)
  calc |(M *ᵥ X) i| = ‖(M *ᵥ X) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖M *ᵥ X‖ := norm_le_pi_norm _ i
    _ ≤ ‖M‖ * ‖X‖ := Matrix.linfty_opNorm_mulVec M X
    _ ≤ ‖M‖ * B := by gcongr

/-- Helper: a set of integer vectors whose images $L\vec{b}$ have all squared coordinates $\le K$ is finite. -/
private theorem finite_of_sq_bdd {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (K : ℝ)
    (S : Set (Fin 3 → ℤ)) (hS : ∀ b ∈ S, ∀ j, (L *ᵥ cast b) j ^ 2 ≤ K) : S.Finite := by
  obtain ⟨C, hC⟩ := bdd_mulVec L⁻¹
  refine (finite_bdd (C * √K)).subset (fun b hb i => ?_)
  have hX : ∀ j, |(L *ᵥ cast b) j| ≤ √K := fun j => Real.abs_le_sqrt (hS b hb j)
  have h := hC (L *ᵥ cast b) (√K) (Real.sqrt_nonneg _) hX i
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL, Matrix.one_mulVec] at h

/-- Helper: the real conjugate of an integral automorph preserves the Lorentz form. -/
private theorem autPlus_conj {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) :
    (L * castM T.val * L⁻¹)ᵀ * lorentz * (L * castM T.val * L⁻¹) = lorentz :=
  conj_lorentz hL hF ((mem_aut_iff_act Q T).1 (Siegel.mem_autPlus_iff.1 hT).1)

/-- **Theorem 6.2** (Cassels, Ch. 13, §6, p. 305): let $f$ be integral anisotropic, $\mathbb{R}$-equivalent to
$X_0^2 + X_1^2 - X_2^2$, let $\mathcal P$ be as in Theorem 6.1 (property (i), contained in $\xi_0^2 + \xi_1^2 \le r^2$,
$r < 1$) and let $m < 0$. A representation $\vec{b}$ of $m$ is *reduced* if $\pi(\vec{b}) \in \mathcal P$. Then
(i) every integral representation $\vec{c}$ of $m$ is equivalent to a reduced one: $T\vec{c}$ is reduced for some
$T \in O^+(f)$; (ii) the reduced integral representations are finite in number, and can be found effectively: they
satisfy $X_2(\vec{b})^2 \le |m|/(1 - r^2)$. (The radius $r$ is taken $\ge 0$, as in the Corollary to Theorem 6.1.) -/
@[kb "cassels1978" "Ch. 13, §6, Thm. 6.2, (6.14), p. 305"]
theorem reduced_rep_neg {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) {P : Set (Fin 2 → ℝ)} {r : ℝ} (hr : r < 1) (hr0 : 0 ≤ r)
    (hPr : ∀ ξ ∈ P, ξ 0 ^ 2 + ξ 1 ^ 2 ≤ r ^ 2)
    (hP : ∀ α ∈ disc, ∃ T ∈ Siegel.AutPlus Q, actD L (castM T.val) α ∈ P) {m : ℤ} (hm : m < 0) :
    (∀ c : Fin 3 → ℤ, Q.eval c = m → ∃ T ∈ Siegel.AutPlus Q, projPt (L *ᵥ cast (T.val *ᵥ c)) ∈ P) ∧
    {b : Fin 3 → ℤ | Q.eval b = m ∧ projPt (L *ᵥ cast b) ∈ P}.Finite ∧
    ∀ b : Fin 3 → ℤ, Q.eval b = m → projPt (L *ᵥ cast b) ∈ P → (L *ᵥ cast b) 2 ^ 2 ≤ |(m : ℝ)| / (1 - r ^ 2) := by
  have hmR : (m : ℝ) < 0 := by exact_mod_cast hm
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - r ^ 2 := by linarith
  have hX : ∀ b : Fin 3 → ℤ, Q.eval b = m → projPt (L *ᵥ cast b) ∈ P →
      (L *ᵥ cast b) 2 ^ 2 ≤ |(m : ℝ)| / (1 - r ^ 2) ∧
      (L *ᵥ cast b) 0 ^ 2 + (L *ᵥ cast b) 1 ^ 2 ≤ |(m : ℝ)| / (1 - r ^ 2) := by
    intro b hb hbP
    have h := eval_eq_lbil hF b
    rw [hb] at h
    set X := L *ᵥ cast b with hXd
    have hX2 : X 2 ≠ 0 := two_ne_zero_of_lbil_neg (by rw [← h]; exact hmR)
    have hX2p : 0 < X 2 ^ 2 := by positivity
    have h1 := hPr _ hbP
    simp only [projPt] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
    rw [div_pow, div_pow, ← add_div, div_le_iff₀ hX2p] at h1
    simp only [lbil] at h
    rw [abs_of_neg hmR]
    have h2 : X 2 ^ 2 * (1 - r ^ 2) ≤ -(m : ℝ) := by nlinarith
    have h3 : X 2 ^ 2 ≤ -(m : ℝ) / (1 - r ^ 2) := by rw [le_div_iff₀ hpos]; exact h2
    refine ⟨h3, ?_⟩
    have : X 0 ^ 2 + X 1 ^ 2 ≤ X 2 ^ 2 := by nlinarith
    linarith
  refine ⟨?_, ?_, fun b hb hbP => (hX b hb hbP).1⟩
  · intro c hc
    have h := eval_eq_lbil hF c
    rw [hc] at h
    have hX2 : (L *ᵥ cast c) 2 ≠ 0 := two_ne_zero_of_lbil_neg (by rw [← h]; exact hmR)
    have hX2p : 0 < (L *ᵥ cast c) 2 ^ 2 := by positivity
    have hα : projPt (L *ᵥ cast c) ∈ disc := by
      show (projPt (L *ᵥ cast c)) 0 ^ 2 + (projPt (L *ᵥ cast c)) 1 ^ 2 < 1
      simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [div_pow, div_pow, ← add_div, div_lt_one hX2p]
      simp only [lbil] at h
      nlinarith
    obtain ⟨T, hT, hTP⟩ := hP _ hα
    refine ⟨T, hT, ?_⟩
    rw [L_cast_mulVec hL T.val c, ← flt_projPt _ hX2]
    exact hTP
  · refine finite_of_sq_bdd hL (|(m : ℝ)| / (1 - r ^ 2)) _ ?_
    rintro b ⟨hb, hbP⟩ j
    obtain ⟨h2, h01⟩ := hX b hb hbP
    fin_cases j
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ((L *ᵥ cast b) 1)]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg ((L *ᵥ cast b) 0)]
    · exact h2

/-- **Copolar points** (Cassels, Ch. 13, §6, (6.15), p. 306): $\vec{\alpha}, \vec{\beta} \in \mathbb{R}^2$ are copolar if
$\alpha_0\beta_0 + \alpha_1\beta_1 = 1$ (each lies on the polar line of the other with respect to the circle
$\xi_0^2 + \xi_1^2 = 1$). -/
@[kb "cassels1978" "Ch. 13, §6, (6.15), p. 306 (copolar points)"]
def Copolar (α β : Fin 2 → ℝ) : Prop := α 0 * β 0 + α 1 * β 1 = 1

/-- Helper: copolarity is orthogonality of the lifts. -/
private theorem copolar_iff (α β : Fin 2 → ℝ) : Copolar α β ↔ lbil (liftPt α) (liftPt β) = 0 := by
  simp only [Copolar, lbil, liftPt]
  simp
  constructor <;> intro h <;> linarith

/-- **Automorphs preserve copolarity** (Cassels, Ch. 13, §6, p. 306): if $T \in O_{\mathbb{R}}(f)$ and $\vec{\alpha},
\vec{\beta}$ are copolar (and $T(\vec{\alpha})$, $T(\vec{\beta})$ are defined) then so are $T(\vec{\alpha})$, $T(\vec{\beta})$. -/
@[kb "cassels1978" "Ch. 13, §6, p. 306 (T preserves copolarity)"]
theorem copolar_actD {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * realMat Q * T = realMat Q)
    {α β : Fin 2 → ℝ} (hα : ((L * T * L⁻¹) *ᵥ liftPt α) 2 ≠ 0) (hβ : ((L * T * L⁻¹) *ᵥ liftPt β) 2 ≠ 0)
    (h : Copolar α β) : Copolar (actD L T α) (actD L T β) := by
  have hA := conj_lorentz hL hF hT
  have h0 := lbil_pres hA (liftPt α) (liftPt β)
  rw [(copolar_iff _ _).1 h] at h0
  set Xa := (L * T * L⁻¹) *ᵥ liftPt α with hXa
  set Xb := (L * T * L⁻¹) *ᵥ liftPt β with hXb
  show Copolar (projPt Xa) (projPt Xb)
  simp only [lbil] at h0
  simp only [Copolar, projPt]
  simp
  field_simp
  linarith

/-- **Theorem 6.3** (Cassels, Ch. 13, §6, pp. 306–307): in the setting of Theorem 6.2, let $m > 0$. A representation
$\vec{b}$ of $m$ is *reduced* if either $X_2(\vec{b}) = 0$ ($\pi(\vec{b})$ not defined) or some $\vec{\alpha} \in \mathcal P$
is copolar with $\pi(\vec{b})$. Then (i) every integral representation $\vec{c}$ of $m$ is equivalent to a reduced one:
$T\vec{c}$ is reduced for some $T \in O^+(f)$ — here $\mathcal P$ is required to lie in $\mathcal D$; (ii) the reduced
integral representations are finite in number and can be found effectively: $X_0(\vec{b})^2 + X_1(\vec{b})^2 \le
m/(1 - r^2)$. (The radius $r$ is taken $\ge 0$, as in the Corollary to Theorem 6.1.) -/
@[kb "cassels1978" "Ch. 13, §6, Thm. 6.3, pp. 306–307"]
theorem reduced_rep_pos {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) {P : Set (Fin 2 → ℝ)} {r : ℝ} (hr : r < 1) (hr0 : 0 ≤ r)
    (hPr : ∀ ξ ∈ P, ξ 0 ^ 2 + ξ 1 ^ 2 ≤ r ^ 2) (hPD : P ⊆ disc)
    (hP : ∀ α ∈ disc, ∃ T ∈ Siegel.AutPlus Q, actD L (castM T.val) α ∈ P) {m : ℤ} (hm : 0 < m) :
    (∀ c : Fin 3 → ℤ, Q.eval c = m → ∃ T ∈ Siegel.AutPlus Q,
      (L *ᵥ cast (T.val *ᵥ c)) 2 = 0 ∨ ∃ α ∈ P, Copolar α (projPt (L *ᵥ cast (T.val *ᵥ c)))) ∧
    {b : Fin 3 → ℤ | Q.eval b = m ∧
      ((L *ᵥ cast b) 2 = 0 ∨ ∃ α ∈ P, Copolar α (projPt (L *ᵥ cast b)))}.Finite ∧
    ∀ b : Fin 3 → ℤ, Q.eval b = m → ((L *ᵥ cast b) 2 = 0 ∨ ∃ α ∈ P, Copolar α (projPt (L *ᵥ cast b))) →
      (L *ᵥ cast b) 0 ^ 2 + (L *ᵥ cast b) 1 ^ 2 ≤ (m : ℝ) / (1 - r ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - r ^ 2 := by linarith
  have hX : ∀ b : Fin 3 → ℤ, Q.eval b = m →
      ((L *ᵥ cast b) 2 = 0 ∨ ∃ α ∈ P, Copolar α (projPt (L *ᵥ cast b))) →
      (L *ᵥ cast b) 2 ^ 2 ≤ (m : ℝ) / (1 - r ^ 2) ∧
      (L *ᵥ cast b) 0 ^ 2 + (L *ᵥ cast b) 1 ^ 2 ≤ (m : ℝ) / (1 - r ^ 2) := by
    intro b hb hred
    have h := eval_eq_lbil hF b
    rw [hb] at h
    simp only [lbil] at h
    set X := L *ᵥ cast b with hXd
    have hS : X 0 ^ 2 + X 1 ^ 2 ≤ (m : ℝ) / (1 - r ^ 2) := by
      rw [le_div_iff₀ hpos]
      rcases hred with h2 | ⟨α, hαP, hcop⟩
      · rw [h2] at h
        nlinarith [mul_nonneg hmR.le (sq_nonneg r)]
      · by_cases h2 : X 2 = 0
        · rw [h2] at h
          nlinarith [mul_nonneg hmR.le (sq_nonneg r)]
        · simp only [Copolar, projPt, Matrix.cons_val_zero, Matrix.cons_val_one] at hcop
          have hcop' : α 0 * X 0 + α 1 * X 1 = X 2 := by
            field_simp at hcop; linarith
          have hcs : (α 0 * X 0 + α 1 * X 1) ^ 2 ≤ (α 0 ^ 2 + α 1 ^ 2) * (X 0 ^ 2 + X 1 ^ 2) := by
            nlinarith [sq_nonneg (α 0 * X 1 - α 1 * X 0)]
          have hαr := hPr α hαP
          have hSn : 0 ≤ X 0 ^ 2 + X 1 ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_right hαr hSn
          rw [hcop'] at hcs
          nlinarith
    refine ⟨?_, hS⟩
    nlinarith
  refine ⟨?_, ?_, fun b hb hred => (hX b hb hred).2⟩
  · intro c hc
    have h := eval_eq_lbil hF c
    rw [hc] at h
    by_cases hX2 : (L *ᵥ cast c) 2 = 0
    · refine ⟨1, one_mem _, Or.inl ?_⟩
      simpa using hX2
    · have hX2p : 0 < (L *ᵥ cast c) 2 ^ 2 := by positivity
      have hs : 1 < (projPt (L *ᵥ cast c)) 0 ^ 2 + (projPt (L *ᵥ cast c)) 1 ^ 2 := by
        simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [div_pow, div_pow, ← add_div, one_lt_div hX2p]
        simp only [lbil] at h
        nlinarith
      set ξ := projPt (L *ᵥ cast c) with hξ
      set s := ξ 0 ^ 2 + ξ 1 ^ 2 with hsdef
      have hs0 : 0 < s := by linarith
      set β : Fin 2 → ℝ := s⁻¹ • ξ with hβdef
      have hβs : β 0 ^ 2 + β 1 ^ 2 = s⁻¹ := by
        simp only [hβdef, Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith
      have hβD : β ∈ disc := by
        show β 0 ^ 2 + β 1 ^ 2 < 1
        rw [hβs]; exact inv_lt_one_of_one_lt₀ hs
      have hcop : Copolar ξ β := by
        simp only [Copolar, hβdef, Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith
      obtain ⟨T, hT, hTP⟩ := hP _ hβD
      refine ⟨T, hT, ?_⟩
      rw [L_cast_mulVec hL T.val c]
      set A := L * castM T.val * L⁻¹ with hAdef
      by_cases hY : (A *ᵥ (L *ᵥ cast c)) 2 = 0
      · exact Or.inl hY
      · refine Or.inr ⟨actD L (castM T.val) β, hTP, ?_⟩
        have hA := autPlus_conj hL hF hT
        have hTr : (castM T.val)ᵀ * realMat Q * castM T.val = realMat Q :=
          (mem_aut_iff_act Q T).1 (Siegel.mem_autPlus_iff.1 hT).1
        have hβ2 : (A *ᵥ liftPt β) 2 ≠ 0 := by
          apply two_ne_zero_of_lbil_neg
          rw [lbil_pres hA, lbil_liftPt_self, hβs]
          have : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
          linarith
        have hξ2 : (A *ᵥ liftPt ξ) 2 ≠ 0 := by
          rw [hξ, mulVec_liftPt_projPt_aux A hX2]
          simpa [hX2] using hY
        have hc2 : Copolar ξ β → Copolar β ξ := by
          intro hh; simp only [Copolar] at hh ⊢; linarith
        have := copolar_actD hL hF hTr hβ2 hξ2 (hc2 hcop)
        rw [← flt_projPt A hX2]
        exact this
  · refine finite_of_sq_bdd hL ((m : ℝ) / (1 - r ^ 2)) _ ?_
    rintro b ⟨hb, hred⟩ j
    obtain ⟨h2, h01⟩ := hX b hb hred
    fin_cases j
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ((L *ᵥ cast b) 1)]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg ((L *ᵥ cast b) 0)]
    · exact h2

end QuadFormsKB.Reduction
