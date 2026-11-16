/-
# Smith's invariants $\Omega$, $\Delta$ of ternary forms and the generalized Lagrange identity

**Library** `QuadFormsKB.Historical.SmithPapers` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Smith, *On the orders and genera of ternary quadratic forms*, 1867; *Collected Mathematical
  Papers* I, p. 455): for a primitive ternary form $f$ with matrix $M$ and
  $D = \det M \neq 0$, let $\Omega$ be the greatest common divisor of the $2 \times 2$ minors of $M$. Then
  $\operatorname{adj} M = \Omega \cdot F$ with $F$ primitive (the primitive contravariant), $D = \Omega^2 \Delta$ for an
  integer $\Delta$, $\operatorname{adj} F = \Delta M$, $\det F = \Omega \Delta^2$, $F$ has invariants
  $[\Delta, \Omega]$, and $[\Omega, \Delta]$ is invariant under $\mathrm{SL}_3(\mathbb Z)$ (`smith_invariants`).
* (Smith, *ibid.*):
  $f(u) f(v) - B(u, v)^2 = \Omega\, F(u \times v)$ and $F(u) F(v) - B_F(u, v)^2 = \Delta\, f(u \times v)$
  (`smith_cross_identities`).

The general identity $f(u) f(v) - B(u, v)^2 = \phi(u \times v)$ with the adjoint form $\phi$
(`adjoint_cross_identity`) is also Dickson's (32), wrapped in `QuadFormsKB.Historical.DicksonStudies`.

Conventions. A ternary form is given by its symmetric integer matrix $M$ (Gauss's and Smith's convention
$f = a x_0^2 + a' x_1^2 + a'' x_2^2 + 2 b x_1 x_2 + 2 b' x_2 x_0 + 2 b'' x_0 x_1$, so the cross coefficients are even);
$f(v) = v^{T} M v$ and $B(u, v) = u^{T} M v$. Variables are 0-based ($x_0, x_1, x_2$ for Smith's $x, y, z$).
Here $\Omega \ge 0$ always (the greatest common divisor of the entries of $\operatorname{adj} M$, which are the
$2 \times 2$ minors up to sign). Smith takes $\Omega$, $\Delta$ positive for definite forms and of opposite signs for
indefinite ones; for indefinite forms Smith's pair is $(-\Omega, -\Delta)$ or $(\Omega, \Delta)$ and his $F$ is $\pm$
ours. The identities hold with either convention; `smith_invariants` records $\Omega(F) = |\Delta|$.

All **proved**, unconditional.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import QuadFormsKB.Citation

namespace QuadFormsKB.Historical.SmithPapers

open Matrix

/-- The ternary form with matrix $M$: $f(v) = v^{T} M v$. -/
def tern (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) : ℤ := v ⬝ᵥ (M *ᵥ v)

/-- The bilinear form of $M$: $B(u, v) = u^{T} M v$ (so $f(v) = B(v, v)$). -/
def bil (M : Matrix (Fin 3) (Fin 3) ℤ) (u v : Fin 3 → ℤ) : ℤ := u ⬝ᵥ (M *ᵥ v)

/-- The content of an integer $3 \times 3$ matrix: the (nonnegative) greatest common divisor of its nine entries. -/
def content (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ := Finset.univ.gcd (fun p : Fin 3 × Fin 3 => M p.1 p.2)

/-- A matrix is primitive if the greatest common divisor of its entries is $1$. -/
def IsPrimitive (M : Matrix (Fin 3) (Fin 3) ℤ) : Prop := content M = 1

/-- Smith's invariant $\Omega$: the greatest common divisor of the $2 \times 2$ minors of $M$, i.e. of the entries
of $\operatorname{adj} M$. -/
def omega (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ := content (adjugate M)

/-- Smith's primitive contravariant $F$: the matrix $\operatorname{adj} M / \Omega$. -/
def contravariant (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  (adjugate M).map (fun x => x / omega M)

/-- Smith's invariant $\Delta = D / \Omega^2$, $D = \det M$. -/
def delta (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ := M.det / omega M ^ 2


private theorem content_dvd (M : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) : content M ∣ M i j :=
  Finset.gcd_dvd (f := fun p : Fin 3 × Fin 3 => M p.1 p.2) (Finset.mem_univ (i, j))

private theorem dvd_content {M : Matrix (Fin 3) (Fin 3) ℤ} {d : ℤ} (h : ∀ i j, d ∣ M i j) :
    d ∣ content M :=
  Finset.dvd_gcd (fun p _ => h p.1 p.2)

private theorem content_nonneg (M : Matrix (Fin 3) (Fin 3) ℤ) : 0 ≤ content M := by
  have h : normalize (content M) = content M := Finset.normalize_gcd
  exact Int.nonneg_of_normalize_eq_self h

private theorem content_smul (c : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    content (c • M) = |c| * content M := by
  unfold content
  have h := Finset.gcd_mul_left (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
    (f := fun p : Fin 3 × Fin 3 => M p.1 p.2) (a := c)
  have e : normalize c = |c| := by
    rcases le_total 0 c with hc | hc
    · rw [Int.normalize_of_nonneg hc, abs_of_nonneg hc]
    · rw [Int.normalize_of_nonpos hc, abs_of_nonpos hc]
  simpa [e] using h

private theorem content_eq_zero {M : Matrix (Fin 3) (Fin 3) ℤ} (h : content M = 0) : M = 0 := by
  ext i j
  have := content_dvd M i j
  rw [h] at this
  simpa using this

private theorem content_mul_dvd (Q X R : Matrix (Fin 3) (Fin 3) ℤ) :
    content X ∣ content (Q * X * R) := by
  apply dvd_content
  intro i j
  simp only [Matrix.mul_apply]
  refine Finset.dvd_sum fun l _ => Dvd.dvd.mul_right ?_ _
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (content_dvd X k l) _

private theorem omega_dvd_conj (M P : Matrix (Fin 3) (Fin 3) ℤ) (_hP : P.det = 1) :
    omega M ∣ omega (Pᵀ * M * P) := by
  unfold omega
  have : adjugate (Pᵀ * M * P) = adjugate P * adjugate M * adjugate Pᵀ := by
    rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc]
  rw [this]
  exact content_mul_dvd _ _ _

private theorem omega_conj (M P : Matrix (Fin 3) (Fin 3) ℤ) (hP : P.det = 1) :
    omega (Pᵀ * M * P) = omega M := by
  have h1 := omega_dvd_conj M P hP
  have hP' : (adjugate P).det = 1 := by
    rw [det_adjugate]; simp [hP]
  have h2 := omega_dvd_conj (Pᵀ * M * P) (adjugate P) hP'
  have e : (adjugate P)ᵀ * (Pᵀ * M * P) * adjugate P = M := by
    have a1 : (adjugate P)ᵀ * Pᵀ = 1 := by
      rw [adjugate_transpose, adjugate_mul, det_transpose, hP]; simp
    have a2 : P * adjugate P = 1 := by rw [mul_adjugate, hP]; simp
    calc (adjugate P)ᵀ * (Pᵀ * M * P) * adjugate P
        = ((adjugate P)ᵀ * Pᵀ) * M * (P * adjugate P) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [a1, a2]; simp
  rw [e] at h2
  exact Int.dvd_antisymm (content_nonneg _) (content_nonneg _) h2 h1

private theorem tern_smul (c : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    tern (c • M) v = c * tern M v := by
  unfold tern
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Smith's invariants of a ternary form** (Smith 1867, *Collected Mathematical
Papers* I, p. 455). Let $M$ be a symmetric, primitive integer matrix with $D = \det M \neq 0$. Then
$\operatorname{adj} M = \Omega F$ with $F$ primitive and symmetric, $D = \Omega^2 \Delta$, $\operatorname{adj} F =
\Delta M$, $\det F = \Omega \Delta^2$, the invariants of $F$ are $\Omega(F) = |\Delta|$ and $\Delta(F) = \Omega$, and
$\Omega$, $\Delta$ are unchanged by every substitution $M \mapsto P^{T} M P$ with $\det P = 1$. -/
@[kb "smith1894a" "p. 455"]
theorem smith_invariants (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : M.IsSymm) (hprim : IsPrimitive M)
    (hD : M.det ≠ 0) :
    0 < omega M ∧ adjugate M = omega M • contravariant M ∧ (contravariant M).IsSymm ∧
      IsPrimitive (contravariant M) ∧ M.det = omega M ^ 2 * delta M ∧
      adjugate (contravariant M) = delta M • M ∧ (contravariant M).det = omega M * delta M ^ 2 ∧
      omega (contravariant M) = |delta M| ∧ delta (contravariant M) = omega M ∧
      ∀ P : Matrix (Fin 3) (Fin 3) ℤ, P.det = 1 →
        omega (Pᵀ * M * P) = omega M ∧ delta (Pᵀ * M * P) = delta M := by
  have hadj_ne : adjugate M ≠ 0 := by
    intro h
    have : (adjugate M).det = M.det ^ 2 := by simpa using det_adjugate M
    rw [h] at this
    simp at this
    exact hD ((pow_eq_zero_iff (n := 2) (by norm_num)).mp this.symm)
  have hΩnn : 0 ≤ omega M := content_nonneg _
  have hΩ0 : omega M ≠ 0 := fun h => hadj_ne (content_eq_zero h)
  have hΩ : 0 < omega M := lt_of_le_of_ne hΩnn (Ne.symm hΩ0)
  have hadjF : adjugate M = omega M • contravariant M := by
    ext i j
    simp only [contravariant, Matrix.smul_apply, map_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (content_dvd _ i j)).symm
  have hFprim : IsPrimitive (contravariant M) := by
    unfold IsPrimitive
    have h := content_smul (omega M) (contravariant M)
    rw [← hadjF, abs_of_pos hΩ] at h
    have h' : omega M * 1 = omega M * content (contravariant M) := by
      rw [mul_one]; exact h
    exact (mul_left_cancel₀ hΩ0 h').symm
  have hE1 : M.det • M = omega M ^ 2 • adjugate (contravariant M) := by
    have h1 := adjugate_adjugate M (by simp)
    rw [hadjF, adjugate_smul] at h1
    simpa using h1.symm
  have hdvd : omega M ^ 2 ∣ M.det := by
    have h1 : omega M ^ 2 ∣ content (M.det • M) := by
      apply dvd_content
      intro i j
      rw [hE1]
      simp
    rw [content_smul, hprim, mul_one] at h1
    exact (dvd_abs _ _).mp h1
  have hDe : M.det = omega M ^ 2 * delta M := (Int.mul_ediv_cancel' hdvd).symm
  have hΩ2 : omega M ^ 2 ≠ 0 := pow_ne_zero _ hΩ0
  have hΔ0 : delta M ≠ 0 := by
    intro h; rw [h, mul_zero] at hDe; exact hD hDe
  have hadjFM : adjugate (contravariant M) = delta M • M := by
    ext i j
    have := congrArg (fun A => A i j) hE1
    simp only [Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [hDe] at this
    apply mul_left_cancel₀ hΩ2
    rw [← this]; ring
  have hdetF : (contravariant M).det = omega M * delta M ^ 2 := by
    have h1 : (adjugate M).det = M.det ^ 2 := by simpa using det_adjugate M
    rw [hadjF, det_smul, hDe] at h1
    simp only [Fintype.card_fin] at h1
    have h3 : omega M ^ 3 * ((contravariant M).det) = omega M ^ 3 * (omega M * delta M ^ 2) := by
      rw [h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero _ hΩ0) h3
  have hFsymm : (contravariant M).IsSymm := by
    ext i j
    have h : (adjugate M) j i = (adjugate M) i j := by
      have h2 : (adjugate M)ᵀ = adjugate M := by rw [adjugate_transpose, hM.eq]
      exact congrFun (congrFun h2 i) j
    simp only [contravariant, transpose_apply, map_apply]
    rw [h]
  have hωF : omega (contravariant M) = |delta M| := by
    unfold omega
    rw [hadjFM, content_smul]
    have : content M = 1 := hprim
    rw [this, mul_one]
  have hδF : delta (contravariant M) = omega M := by
    unfold delta
    rw [hωF, hdetF, sq_abs]
    have : delta M ^ 2 ≠ 0 := pow_ne_zero _ hΔ0
    rw [mul_comm]
    exact Int.mul_ediv_cancel_left _ this
  refine ⟨hΩ, hadjF, hFsymm, hFprim, hDe, hadjFM, hdetF, hωF, hδF, ?_⟩
  intro P hP
  have h1 := omega_conj M P hP
  have h2 : (Pᵀ * M * P).det = M.det := by simp [det_mul, hP]
  refine ⟨h1, ?_⟩
  unfold delta
  rw [h1, h2]

/-- The generalized Lagrange identity (Cauchy-Binet for $3 \times 3$ matrices): for a symmetric matrix $A$,
$f(u) f(v) - B(u, v)^2 = \phi(u \times v)$, where $\phi$ is the adjoint form (matrix $\operatorname{adj} A$). -/
theorem adjoint_cross_identity (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (u v : Fin 3 → ℤ) :
    tern A u * tern A v - bil A u v ^ 2 = tern (adjugate A) (crossProduct u v) := by
  have h01 : A 1 0 = A 0 1 := hA.apply 0 1
  have h02 : A 2 0 = A 0 2 := hA.apply 0 2
  have h12 : A 2 1 = A 1 2 := hA.apply 1 2
  simp [tern, bil, adjugate_fin_three, cross_apply, dotProduct, mulVec, Fin.sum_univ_three, h01, h02, h12]
  ring

/-- **Smith's identities for a ternary form and its contravariant** (Smith 1867,
*Collected Mathematical Papers* I, p. 457). For a symmetric primitive $M$ with $\det M \neq 0$ and its primitive
contravariant $F$: $f(u) f(v) - B(u, v)^2 = \Omega\, F(u \times v)$ and
$F(u) F(v) - B_F(u, v)^2 = \Delta\, f(u \times v)$. -/
@[kb "smith1894a" "p. 457"]
theorem smith_cross_identities (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : M.IsSymm) (hprim : IsPrimitive M)
    (hD : M.det ≠ 0) (u v : Fin 3 → ℤ) :
    tern M u * tern M v - bil M u v ^ 2 = omega M * tern (contravariant M) (crossProduct u v) ∧
      tern (contravariant M) u * tern (contravariant M) v - bil (contravariant M) u v ^ 2 =
        delta M * tern M (crossProduct u v) := by
  obtain ⟨-, hadjF, hFsymm, -, -, hadjFM, -⟩ := smith_invariants M hM hprim hD
  refine ⟨?_, ?_⟩
  · rw [adjoint_cross_identity M hM u v]
    conv_lhs => rw [hadjF]
    exact tern_smul _ _ _
  · rw [adjoint_cross_identity _ hFsymm u v, hadjFM]
    exact tern_smul _ _ _

end QuadFormsKB.Historical.SmithPapers
