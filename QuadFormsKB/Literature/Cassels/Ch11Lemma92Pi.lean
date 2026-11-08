/-
# Cassels, Chapter 11, proof of Lemma 9.2: case (c₁), the auxiliary prime $\pi$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, case (c₁), p. 247:
"$p = \pi$. Since $d(f) \in U_\pi^2$, we may suppose further that $f(\mathbf r_3) = -f(\mathbf r_4) = 1$. We take for $\Gamma_\pi$ the
lattice with basis $\pi\mathbf w, \mathbf r_3, \mathbf r_4$ … We note also, by (9.57), that $f$ represents primitively the whole of
$\mathbb Z_\pi$ on $\Gamma_\pi$."

**Proves.**
* `binary_represents_all`: a binary form $ax^2 + bxy + cy^2$ over $\mathbb Z_p$ ($p$ odd) whose discriminant $b^2 - 4ac$ is the square
  of a unit represents every element of $\mathbb Z_p$ (a hyperbolic plane).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92CaseB

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-- **A binary form with unit square discriminant represents everything** ($p$ odd): if $b^2 - 4ac = s^2$ with $s$ a unit,
then for every $c_0 \in \mathbb Z_p$ there are $x, y$ with $ax^2 + bxy + cy^2 = c_0$. *Proof:* $4a(ax^2 + bxy + cy^2) =
(2ax + by)^2 - s^2y^2$; if $a$ is a unit put $2ax + by - sy = 1$, $2ax + by + sy = 4ac_0$; if $c$ is a unit, symmetrically;
otherwise $b$ is a unit and $x = c_0b^{-1}$, $y = 1 - \dots$ is found by Hensel. -/
theorem binary_represents_all_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b c s : ℤ_[p]) (hs : IsUnit s)
    (hdisc : b ^ 2 - 4 * a * c = s ^ 2) (ha : IsUnit a) (c0 : ℤ_[p]) :
    ∃ x y : ℤ_[p], a * x ^ 2 + b * x * y + c * y ^ 2 = c0 := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hp2 ?_)
    have h1 : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
    have h3 : p ∣ 2 := by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd 2).mp h1
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3
  obtain ⟨i2, hi2⟩ := h2.exists_right_inv
  obtain ⟨si, hsi⟩ := hs.exists_right_inv
  · obtain ⟨ai, hai⟩ := ha.exists_right_inv
    -- `2a x + (b - s) y = 1`, `2a x + (b + s) y = 4 a c₀`
    refine ⟨(1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * i2 * ai, (4 * a * c0 - 1) * i2 * si, ?_⟩
    have e1 : 2 * a * ((1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * i2 * ai) +
        (b - s) * ((4 * a * c0 - 1) * i2 * si) = 1 := by
      linear_combination (1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * (a * ai) * hi2 +
        (1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * hai
    have e2 : 2 * s * ((4 * a * c0 - 1) * i2 * si) = 4 * a * c0 - 1 := by
      linear_combination (4 * a * c0 - 1) * (s * si) * hi2 + (4 * a * c0 - 1) * hsi
    have key : 4 * a * (a * ((1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * i2 * ai) ^ 2 +
        b * ((1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * i2 * ai) * ((4 * a * c0 - 1) * i2 * si) +
        c * ((4 * a * c0 - 1) * i2 * si) ^ 2) = 4 * a * c0 := by
      linear_combination (-(((4 * a * c0 - 1) * i2 * si) ^ 2)) * hdisc +
        (2 * a * ((1 - (b - s) * ((4 * a * c0 - 1) * i2 * si)) * i2 * ai) +
          (b + s) * ((4 * a * c0 - 1) * i2 * si) + 1) * e1 + e2
    have h4a : IsUnit (4 * a) := by
      have : (4 : ℤ_[p]) = 2 * 2 := by norm_num
      rw [this]; exact (h2.mul h2).mul ha
    exact h4a.mul_left_cancel key

theorem binary_represents_all {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b c s : ℤ_[p]) (hs : IsUnit s)
    (hdisc : b ^ 2 - 4 * a * c = s ^ 2) (c0 : ℤ_[p]) :
    ∃ x y : ℤ_[p], a * x ^ 2 + b * x * y + c * y ^ 2 = c0 := by
  by_cases ha : IsUnit a
  · exact binary_represents_all_aux hp2 a b c s hs hdisc ha c0
  by_cases hc : IsUnit c
  · obtain ⟨y, x, h⟩ := binary_represents_all_aux hp2 c b a s hs (by linear_combination hdisc) hc c0
    exact ⟨x, y, by linear_combination h⟩
  -- `a, c ∈ pℤ_p`, so `b` is a unit; substitute `x ↦ x + y`
  have hpa : (p : ℤ_[p]) ∣ a := (PadicInt.norm_lt_one_iff_dvd a).mp
    (lt_of_le_of_ne (PadicInt.norm_le_one a) (fun h => ha (PadicInt.isUnit_iff.mpr h)))
  have hpc : (p : ℤ_[p]) ∣ c := (PadicInt.norm_lt_one_iff_dvd c).mp
    (lt_of_le_of_ne (PadicInt.norm_le_one c) (fun h => hc (PadicInt.isUnit_iff.mpr h)))
  have hb : IsUnit b := by
    have hb2 : IsUnit (b ^ 2) := by
      obtain ⟨ka, hka⟩ := hpa
      have := isUnit_add_p_mul (hs.pow 2) (4 * ka * c)
      convert this using 1; rw [hka] at hdisc; linear_combination hdisc
    exact (isUnit_pow_iff (by norm_num)).mp hb2
  have hc' : IsUnit (a + b + c) := by
    obtain ⟨ka, hka⟩ := hpa
    obtain ⟨kc, hkc⟩ := hpc
    have := isUnit_add_p_mul hb (ka + kc)
    convert this using 1; rw [hka, hkc]; ring
  obtain ⟨y, x, h⟩ := binary_represents_all_aux hp2 (a + b + c) (2 * a + b) a s hs
    (by linear_combination hdisc) hc' c0
  exact ⟨x + y, y, by linear_combination h⟩

/-- Helper ($p$ odd): $x \equiv 1 \pmod p$ is a square in $\mathbb Z_p$. -/
theorem exists_sq_of_dvd_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x - 1) :
    ∃ y : ℤ_[p], y ^ 2 = x := by
  obtain ⟨t, ht⟩ := hx
  have h2 : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hp2 ?_)
    have h1 : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
    have h3 : p ∣ 2 := by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd 2).mp h1
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3
  obtain ⟨z, hz⟩ := exists_root_quadratic (-t) 2 1 h2
  exact ⟨1 + (p : ℤ_[p]) * z, by linear_combination (p : ℤ_[p]) * hz - ht⟩

/-- Helper: the determinant of a $4 \times 4$ block diagonal matrix with $2 \times 2$ blocks. -/
theorem det_blockDiag4 {R : Type*} [CommRing R] (a b c d e f g h : R) :
    (!![a, b, 0, 0; c, d, 0, 0; 0, 0, e, f; 0, 0, g, h] : Matrix (Fin 4) (Fin 4) R).det =
      (a * d - b * c) * (e * h - f * g) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

/-- **$(\mathbf u, e)$ extends to a basis** (Cassels, Ch. 8, Lemma 2.1, (iii) ⇒ (i)): if the Gram matrix
$\begin{pmatrix} B(\mathbf u,\mathbf u) & B(\mathbf u,e) \\ B(e,\mathbf u) & B(e,e)\end{pmatrix}$ has a unit determinant, then
$\mathbf u, e$ are the first two columns of some $T \in \mathrm{GL}_4(\mathbb Z_p)$. -/
theorem exists_basis_of_unimodular_pair {p : ℕ} [Fact p.Prime] (Q : QuadForm ℤ_[p] 4) (u e : Fin 4 → ℤ_[p])
    (hD : IsUnit (bl Q u u * bl Q e e - bl Q u e ^ 2)) :
    ∃ T : GL (Fin 4) ℤ_[p], T.val *ᵥ Pi.single 0 1 = u ∧ T.val *ᵥ Pi.single 1 1 = e := by
  classical
  set c : Fin 2 → Fin 4 → ℤ_[p] := ![u, e] with hc
  have h31 := (tfae_extends_basis_padic (n := 4) (p := p) (J := 2) (by norm_num) c).out 3 1
  obtain ⟨Di, hDi⟩ := hD.exists_right_inv
  obtain ⟨T, hT⟩ := h31.mp fun v ⟨y, hy⟩ => by
    -- pair with `u` and `e`
    set φ := PadicInt.Coe.ringHom (p := p)
    have hpair : ∀ x : Fin 4 → ℤ_[p], v 0 * ((bl Q u x : ℤ_[p]) : ℚ_[p]) + v 1 * ((bl Q e x : ℤ_[p]) : ℚ_[p]) = ((bl Q y x : ℤ_[p]) : ℚ_[p]) := by
      intro x
      have hy' : (fun i => (y i : ℚ_[p])) = v 0 • (fun i => (u i : ℚ_[p])) + v 1 • (fun i => (e i : ℚ_[p])) := by
        rw [← hy]; simp [Fin.sum_univ_two, hc]
      have e1 : ((bl Q y x : ℤ_[p]) : ℚ_[p]) = bl (Q.map φ) (fun i => φ (y i)) (fun i => φ (x i)) :=
        (bl_map φ Q y x).symm
      have e2 : ((bl Q u x : ℤ_[p]) : ℚ_[p]) = bl (Q.map φ) (fun i => φ (u i)) (fun i => φ (x i)) :=
        (bl_map φ Q u x).symm
      have e3 : ((bl Q e x : ℤ_[p]) : ℚ_[p]) = bl (Q.map φ) (fun i => φ (e i)) (fun i => φ (x i)) :=
        (bl_map φ Q e x).symm
      rw [e1, e2, e3]
      change _ = bl (Q.map φ) (fun i => (y i : ℚ_[p])) _
      rw [hy', bl_add_left, bl_smul_left, bl_smul_left]; rfl
    have hu := hpair u
    have he := hpair e
    have hcomm : ((bl Q e u : ℤ_[p]) : ℚ_[p]) = ((bl Q u e : ℤ_[p]) : ℚ_[p]) := by rw [bl_comm]
    rw [hcomm] at hu
    have hDq : ((bl Q u u * bl Q e e - bl Q u e ^ 2 : ℤ_[p]) : ℚ_[p]) * (Di : ℚ_[p]) = 1 := by
      rw [← PadicInt.coe_mul, hDi, PadicInt.coe_one]
    intro j
    fin_cases j
    · refine ⟨(bl Q e e * bl Q y u - bl Q u e * bl Q y e) * Di, ?_⟩
      push_cast at hDq ⊢
      linear_combination (-(v 0)) * hDq + ((bl Q e e : ℤ_[p]) : ℚ_[p]) * (Di : ℚ_[p]) * hu -
        ((bl Q u e : ℤ_[p]) : ℚ_[p]) * (Di : ℚ_[p]) * he
    · refine ⟨(bl Q u u * bl Q y e - bl Q u e * bl Q y u) * Di, ?_⟩
      push_cast at hDq ⊢
      linear_combination (-(v 1)) * hDq + ((bl Q u u : ℤ_[p]) : ℚ_[p]) * (Di : ℚ_[p]) * he -
        ((bl Q u e : ℤ_[p]) : ℚ_[p]) * (Di : ℚ_[p]) * hu
  exact ⟨T, hT 0, hT 1⟩

/-- Helper: the $4 \times 4$ matrix with columns $c_0, \dots, c_3$ (over any commutative ring). -/
def colMat' {R : Type*} [CommRing R] (c : Fin 4 → Fin 4 → R) : Matrix (Fin 4) (Fin 4) R := Matrix.of fun i j => c j i

/-- Helper: the entries of $E^{\mathsf T}HE$ are the polar values of the columns of $E$. -/
theorem mul_hessian_mul_apply {R : Type*} [CommRing R] (Q : QuadForm R 4) (c : Fin 4 → Fin 4 → R) (i j : Fin 4) :
    ((colMat' c)ᵀ * Q.hessian * colMat' c) i j = bl Q (c i) (c j) := by
  simp only [colMat', bl, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The orthogonal complement of $(\mathbf u, e)$ at $\pi$ is a hyperbolic plane** (Cassels (9.45)–(9.47), (9.57)): over
$\mathbb Z_p$, $p$ odd, if $B(\mathbf u, e)$ is a unit, $p \mid Q(\mathbf u)$ and $\det H_Q = 16\delta^2$ with $\delta$ a unit, then there are
$k_3, k_4 \perp \mathbf u, e$ such that $\mathbf u, e, k_3, k_4$ is a basis and the binary form $Q(xk_3 + yk_4)$ has discriminant
$B(k_3,k_4)^2 - 4Q(k_3)Q(k_4) = s^2$, $s$ a unit. -/
theorem exists_hyperbolic_complement {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (Q : QuadForm ℤ_[p] 4)
    (u e : Fin 4 → ℤ_[p]) (hB : IsUnit (bl Q u e)) (hg : (p : ℤ_[p]) ∣ Q.eval u) (δ : ℤ_[p]) (hδ : IsUnit δ)
    (hdet : Q.hessian.det = 16 * δ ^ 2) :
    ∃ k3 k4 : Fin 4 → ℤ_[p], bl Q u k3 = 0 ∧ bl Q e k3 = 0 ∧ bl Q u k4 = 0 ∧ bl Q e k4 = 0 ∧
      IsUnit (colMat' ![u, e, k3, k4]).det ∧
      ∃ s : ℤ_[p], IsUnit s ∧ bl Q k3 k4 ^ 2 - 4 * Q.eval k3 * Q.eval k4 = s ^ 2 := by
  classical
  obtain ⟨Bi, hBi⟩ := hB.exists_right_inv
  obtain ⟨gq, hgq⟩ := hg
  have h2 : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hp2 ?_)
    have h1 : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
    have h3 : p ∣ 2 := by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd 2).mp h1
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3
  -- `X = B² - (bl Q u e)(u,u)(bl Q u e)(e,e) = ((bl Q u e) r)²`
  have huu : bl Q u u = 2 * ((p : ℤ_[p]) * gq) := by rw [bl_self, hgq]
  obtain ⟨r, hr⟩ := exists_sq_of_dvd_sub_one hp2 (x := 1 - bl Q u u * bl Q e e * Bi ^ 2)
    ⟨-(2 * gq * bl Q e e * Bi ^ 2), by rw [huu]; ring⟩
  have hru : IsUnit r := by
    have : IsUnit (r ^ 2) := by
      rw [hr, huu]
      have := isUnit_add_p_mul (p := p) isUnit_one (-(2 * gq * bl Q e e * Bi ^ 2))
      convert this using 1; ring
    exact (isUnit_pow_iff (by norm_num)).mp this
  have hX : (bl Q u e) ^ 2 - bl Q u u * bl Q e e = ((bl Q u e) * r) ^ 2 := by
    rw [mul_pow, hr]; linear_combination (bl Q u u * bl Q e e) * ((bl Q u e) * Bi + 1) * hBi
  have hD : IsUnit (bl Q u u * bl Q e e - (bl Q u e) ^ 2) := by
    have : bl Q u u * bl Q e e - (bl Q u e) ^ 2 = -(((bl Q u e) * r) ^ 2) := by rw [← hX]; ring
    rw [this]; exact ((hB.mul hru).pow 2).neg
  obtain ⟨Di, hDi⟩ := hD.exists_right_inv
  obtain ⟨T, hT0, hT1⟩ := exists_basis_of_unimodular_pair Q u e hD
  -- the projections of `T e₂`, `T e₃`
  have hproj : ∀ c : Fin 4 → ℤ_[p], bl Q u (c - ((bl Q e e * bl Q u c - (bl Q u e) * bl Q e c) * Di) • u -
      ((bl Q u u * bl Q e c - (bl Q u e) * bl Q u c) * Di) • e) = 0 ∧ bl Q e (c - ((bl Q e e * bl Q u c - (bl Q u e) * bl Q e c) * Di) • u -
      ((bl Q u u * bl Q e c - (bl Q u e) * bl Q u c) * Di) • e) = 0 := by
    intro c
    have hcomm : bl Q e u = (bl Q u e) := by rw [bl_comm]
    refine ⟨?_, ?_⟩
    · rw [bl_sub_right, bl_sub_right, bl_smul_right, bl_smul_right]
      linear_combination (-(bl Q u c)) * hDi
    · rw [bl_sub_right, bl_sub_right, bl_smul_right, bl_smul_right, hcomm]
      linear_combination (-(bl Q e c)) * hDi
  set c3 := T.val *ᵥ Pi.single 2 1
  set c4 := T.val *ᵥ Pi.single 3 1
  set α3 := (bl Q e e * bl Q u c3 - (bl Q u e) * bl Q e c3) * Di
  set β3 := (bl Q u u * bl Q e c3 - (bl Q u e) * bl Q u c3) * Di
  set α4 := (bl Q e e * bl Q u c4 - (bl Q u e) * bl Q e c4) * Di
  set β4 := (bl Q u u * bl Q e c4 - (bl Q u e) * bl Q u c4) * Di
  set k3 := c3 - α3 • u - β3 • e with hk3
  set k4 := c4 - α4 • u - β4 • e with hk4
  obtain ⟨o13, o23⟩ := hproj c3
  obtain ⟨o14, o24⟩ := hproj c4
  -- `E = T U` with `U` unitriangular
  have hE : colMat' ![u, e, k3, k4] = T.val * !![1, 0, -α3, -α4; 0, 1, -β3, -β4; 0, 0, 1, 0; 0, 0, 0, 1] := by
    have hT0' : ∀ i, T.val i 0 = u i := fun i => by
      have := congrFun hT0 i; rw [mulVec_single_one] at this; simpa using this
    have hT1' : ∀ i, T.val i 1 = e i := fun i => by
      have := congrFun hT1 i; rw [mulVec_single_one] at this; simpa using this
    have hc3 : ∀ i, c3 i = T.val i 2 := fun i => by simp [c3, mulVec_single_one]
    have hc4 : ∀ i, c4 i = T.val i 3 := fun i => by simp [c4, mulVec_single_one]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases j <;> simp [colMat', hk3, hk4, hT0', hT1', hc3, hc4] <;> ring
  have hEdet : IsUnit (colMat' ![u, e, k3, k4]).det := by
    rw [hE, Matrix.det_mul]
    have hU : (!![1, 0, -α3, -α4; 0, 1, -β3, -β4; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ_[p]).det = 1 := by
      rw [Matrix.det_succ_column_zero]; simp [Fin.sum_univ_succ, Matrix.det_succ_column_zero, Fin.succAbove]
    rw [hU, mul_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit
  refine ⟨k3, k4, o13, o23, o14, o24, hEdet, ?_⟩
  -- the discriminant
  have o13' : bl Q u k3 = 0 := o13
  have o23' : bl Q e k3 = 0 := o23
  have o14' : bl Q u k4 = 0 := o14
  have o24' : bl Q e k4 = 0 := o24
  have hblock : (colMat' ![u, e, k3, k4])ᵀ * Q.hessian * colMat' ![u, e, k3, k4] =
      !![bl Q u u, bl Q u e, 0, 0; bl Q u e, bl Q e e, 0, 0; 0, 0, bl Q k3 k3, bl Q k3 k4;
        0, 0, bl Q k3 k4, bl Q k4 k4] := by
    refine Matrix.ext fun i j => ?_
    rw [mul_hessian_mul_apply]
    fin_cases i <;> fin_cases j <;> simp [o13', o23', o14', o24', bl_comm Q k3 u, bl_comm Q k3 e,
      bl_comm Q k4 u, bl_comm Q k4 e, bl_comm Q e u, bl_comm Q k4 k3]
  have hdd := congrArg Matrix.det hblock
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_blockDiag4, hdet, bl_self Q k3, bl_self Q k4] at hdd
  obtain ⟨Bri, hBri⟩ := (hB.mul hru).exists_right_inv
  refine ⟨4 * (colMat' ![u, e, k3, k4]).det * δ * Bri, ?_, ?_⟩
  · have h4 : IsUnit (4 : ℤ_[p]) := by
      have : (4 : ℤ_[p]) = 2 * 2 := by norm_num
      rw [this]; exact h2.mul h2
    exact ((h4.mul hEdet).mul hδ).mul (isUnit_of_mul_eq_one_right' hBri)
  · have hXd : bl Q u u * bl Q e e - bl Q u e * bl Q u e = -((bl Q u e * r) ^ 2) := by
      linear_combination -hX
    rw [hXd] at hdd
    linear_combination (-(Bri ^ 2)) * hdd - (bl Q k3 k4 ^ 2 - 4 * Q.eval k3 * Q.eval k4) *
      (bl Q u e * r * Bri + 1) * hBri

section Pkg

open QuadFormsKB.Lattices

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **$W\tilde W$ fixes the vectors normal to $\mathbf u$** (over $\mathbb Z_p$): if the columns of $B'$ are normal to
$\mathbf u$ and $H_f\mathbf u = e\,r$ ($e \ne 0$), $W\tilde W + c_0r^{\mathsf T} = 1$, then $W(\tilde WB') = B'$ (the argument of
`pkgCaseA`). -/
theorem W_Wt_eq_of_orth (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (c0 r : Fin 4 → ℤ) (hWW : W * Wt + Matrix.vecMulVec c0 r = 1) (e : ℤ)
    (he0 : e ≠ 0) (he : f.hessian *ᵥ u = e • r) (B' : Matrix (Fin 4) (Fin 3) ℤ_[pOf v])
    (horth : ∀ j, bl (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v])) (Ch11L92.col B' j) = 0) :
    W.map (Int.castRingHom ℤ_[pOf v]) * (Wt.map (Int.castRingHom ℤ_[pOf v]) * B') = B' := by
  classical
  set φ := Int.castRingHom ℤ_[pOf v] with hφ
  have hr0 : ∀ j, (fun i => (r i : ℤ_[pOf v])) ⬝ᵥ Ch11L92.col B' j = 0 := by
    intro j
    have h1 := horth j
    rw [bl_comm, bl, hessian_map] at h1
    have h2 : f.hessian.map φ *ᵥ (fun i => (u i : ℤ_[pOf v])) = (e : ℤ_[pOf v]) • fun i => (r i : ℤ_[pOf v]) := by
      funext i
      have := congrFun he i
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [hφ, ← cast_mulVec, this]; simp
    rw [h2, dotProduct_smul, smul_eq_mul, dotProduct_comm] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (by exact_mod_cast h) he0
    · exact h
  have hm : W.map φ * Wt.map φ = 1 - Matrix.vecMulVec (fun i => (c0 i : ℤ_[pOf v])) (fun i => (r i : ℤ_[pOf v])) := by
    rw [← Matrix.map_mul, eq_sub_iff_add_eq]
    have := congrArg (fun M => M.map φ) hWW
    simp only [Matrix.map_add, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← this]; congr 1; ext i j; simp [Matrix.vecMulVec_apply, φ]
  rw [← Matrix.mul_assoc, hm, Matrix.sub_mul, Matrix.one_mul, sub_eq_self]
  refine Matrix.ext fun i j => ?_
  have := hr0 j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  simp only [Ch11L92.col, mulVec_single_one, Matrix.col_apply, dotProduct] at this
  rw [show ∑ k, (c0 i : ℤ_[pOf v]) * (r k : ℤ_[pOf v]) * B' k j = (c0 i : ℤ_[pOf v]) * ∑ k, (r k : ℤ_[pOf v]) * B' k j
    by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, this, mul_zero]

/-- Helper: a unit value of a polar form forces a unit coordinate. -/
theorem exists_isUnit_of_bl_isUnit {p : ℕ} [Fact p.Prime] (Q : QuadForm ℤ_[p] 4) (x y : Fin 4 → ℤ_[p])
    (h : IsUnit (bl Q x y)) : ∃ i, IsUnit (x i) := by
  by_contra hno
  push Not at hno
  have hdvd : (p : ℤ_[p]) ∣ bl Q x y := by
    unfold bl
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_right ?_ _
    have := hno i
    exact (PadicInt.norm_lt_one_iff_dvd _).mp
      (lt_of_le_of_ne (PadicInt.norm_le_one _) (fun h1 => this (PadicInt.isUnit_iff.mpr h1)))
  exact PadicInt.p_nonunit (isUnit_of_dvd_unit hdvd h)

/-- **Case (c₁), $p = \pi$, as a local package** (Cassels, p. 247, (9.58)): $\Gamma_\pi$ has basis $\pi\mathbf w, k_3, k_4$ with
$\mathbf w = B(\mathbf u, e)\mathbf u - 2f(\mathbf u)e$ and $k_3, k_4$ spanning the hyperbolic plane $\langle\mathbf u, e\rangle^\perp$
(`exists_hyperbolic_complement`, which uses $d(f) \in U_\pi^2$). It represents every element of $\mathbb Z_\pi$, so every integer
$a$ is served with $b_0 = 1$; primitivity holds because $B(b\mathbf u + \mathbf c, e) \equiv bB(\mathbf u, e) \pmod \pi$. -/
def pkgPi (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ) (Wt : Matrix (Fin 3) (Fin 4) ℤ)
    (c0 r : Fin 4 → ℤ) (hWW : W * Wt + Matrix.vecMulVec c0 r = 1) (e : ℤ) (he0 : e ≠ 0)
    (he : f.hessian *ᵥ u = e • r) (horth : ∀ z, bl f u (W *ᵥ z) = 0) (hp2 : pOf v ≠ 2) (ee : Fin 4 → ℤ)
    (hee : ¬ (pOf v : ℤ) ∣ bl f u ee) (hg : (pOf v : ℤ) ∣ f.eval u) (δ : ℤ_[pOf v]) (hδ : IsUnit δ)
    (hdet : (f.map (Int.castRingHom ℤ_[pOf v])).hessian.det = 16 * δ ^ 2) (A : ℤ → Prop) (p0 : ℕ) :
    LocalPkg f u W A p0 v := by
  classical
  have hBu : IsUnit (bl (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v])) (fun i => (ee i : ℤ_[pOf v]))) := by
    rw [show bl (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v])) (fun i => (ee i : ℤ_[pOf v])) =
      ((bl f u ee : ℤ) : ℤ_[pOf v]) from bl_map (Int.castRingHom ℤ_[pOf v]) f u ee]
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hee ?_)
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
  have hgp : (pOf v : ℤ_[pOf v]) ∣ (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => (u i : ℤ_[pOf v])) := by
    rw [show (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => (u i : ℤ_[pOf v])) =
      ((f.eval u : ℤ) : ℤ_[pOf v]) from eval_map_hom (Int.castRingHom ℤ_[pOf v]) f u]
    obtain ⟨k, hk⟩ := hg; exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hex := exists_hyperbolic_complement hp2 (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v]))
    (fun i => (ee i : ℤ_[pOf v])) hBu hgp δ hδ hdet
  let k3 := hex.choose
  let k4 := hex.choose_spec.choose
  have hk := hex.choose_spec.choose_spec
  let w0 : Fin 4 → ℤ_[pOf v] := bl (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v]))
      (fun i => (ee i : ℤ_[pOf v])) • (fun i => (u i : ℤ_[pOf v])) -
    (2 * (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => (u i : ℤ_[pOf v]))) • (fun i => (ee i : ℤ_[pOf v]))
  let B'' : Matrix (Fin 4) (Fin 3) ℤ_[pOf v] := Matrix.of fun i j => ![(pOf v : ℤ_[pOf v]) • w0, k3, k4] j i
  have hcol : ∀ j, Ch11L92.col B'' j = ![(pOf v : ℤ_[pOf v]) • w0, k3, k4] j := by
    intro j; funext i; simp [Ch11L92.col, B'', mulVec_single_one]
  have o13 := hk.1
  have o23 := hk.2.1
  have o14 := hk.2.2.1
  have o24 := hk.2.2.2.1
  have hEdet := hk.2.2.2.2.1
  have hsd := hk.2.2.2.2.2.choose_spec.1
  have hdisc := hk.2.2.2.2.2.choose_spec.2
  have hk3 : hex.choose = k3 := rfl
  -- the columns of `B''` are normal to `u`
  have horthB : ∀ j, bl (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => (u i : ℤ_[pOf v])) (Ch11L92.col B'' j) = 0 := by
    intro j
    rw [hcol]
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [bl_smul_right, bl_sub_right, bl_smul_right, bl_smul_right, bl_self]; ring
    · exact o13
    · exact o14
  have hWC := W_Wt_eq_of_orth v f u W Wt c0 r hWW e he0 he B'' horthB
  set C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v] := Wt.map (Int.castRingHom ℤ_[pOf v]) * B'' with hCdef
  have hWCv : ∀ η, W.map (Int.castRingHom ℤ_[pOf v]) *ᵥ (C *ᵥ η) = B'' *ᵥ η := fun η => by
    rw [mulVec_mulVec, hWC]
  have hB'' : ∀ η : Fin 3 → ℤ_[pOf v], B'' *ᵥ η = (η 0 * (pOf v : ℤ_[pOf v])) • w0 + η 1 • k3 + η 2 • k4 := by
    intro η; funext i
    simp [B'', mulVec, dotProduct, Fin.sum_univ_three]; ring
  have hev : ∀ η, ((gramOf f W).map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η) =
      (f.map (Int.castRingHom ℤ_[pOf v])).eval (B'' *ᵥ η) := by
    intro η; rw [gramOf_map, gramOf_eval, hWCv]
  -- the binary form on `⟨k₃, k₄⟩` represents everything
  have hrep : ∀ c : ℤ_[pOf v], ∃ η : Fin 3 → ℤ_[pOf v],
      ((gramOf f W).map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η) = c := by
    intro c
    obtain ⟨x, y, hxy⟩ := binary_represents_all hp2 _ _ _ _ hsd hdisc c
    refine ⟨![0, x, y], ?_⟩
    rw [hev, hB'']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zero_mul, zero_smul, zero_add]
    rw [eval_add, eval_smul, eval_smul, bl_smul_left, bl_smul_right, ← hxy]; ring
  -- `det C ≠ 0`
  have hC : C.det ≠ 0 := by
    intro h0
    obtain ⟨η, hη0, hη⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hη0
    have hB0 : B'' *ᵥ η = 0 := by rw [← hWCv, hη, mulVec_zero]
    set γv : Fin 4 → ℤ_[pOf v] := ![η 0 * (pOf v : ℤ_[pOf v]) * bl (f.map (Int.castRingHom ℤ_[pOf v]))
        (fun i => (u i : ℤ_[pOf v])) (fun i => (ee i : ℤ_[pOf v])),
      -(η 0 * (pOf v : ℤ_[pOf v]) * (2 * (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => (u i : ℤ_[pOf v])))),
      η 1, η 2] with hγv
    have hEγ : colMat' ![(fun i => (u i : ℤ_[pOf v])), (fun i => (ee i : ℤ_[pOf v])), k3, k4] *ᵥ γv = 0 := by
      rw [← hB0, hB'']; funext i
      simp [colMat', mulVec, dotProduct, Fin.sum_univ_four, hγv, w0]; ring
    have hγ0 := Matrix.eq_zero_of_mulVec_eq_zero (hEdet.ne_zero) hEγ
    have h1 := congrFun hγ0 2
    have h2 := congrFun hγ0 3
    have h0' := congrFun hγ0 0
    simp only [hγv, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Pi.zero_apply] at h0' h1 h2
    funext i
    fin_cases i
    · have hp0 : (pOf v : ℤ_[pOf v]) ≠ 0 := by exact_mod_cast (Fact.out : (pOf v).Prime).ne_zero
      rcases mul_eq_zero.mp h0' with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hp0
      · exact absurd h hBu.ne_zero
    · exact h1
    · exact h2
  refine
    { M := tLat v hC
      isLattice := tLat_isLattice v hC
      le_std := tLat_le_std v hC
      units := fun L hQ hL w hw => units_mem_tLat v (gramOf f W) hC 0 (fun η η' => by simp)
        (fun w' _ => by obtain ⟨η, hη⟩ := hrep w'; exact ⟨η, by rw [hη]; ring⟩) L hQ hL w hw
      N := 1
      cond := fun a _ => ⟨1, fun b hb => ⟨?_, fun z hzM _ => Or.inl ?_⟩⟩ }
  · exact exists_mem_tLat_of_rep v (gramOf f W) hC (hrep _)
  · -- primitivity
    obtain ⟨η, hη⟩ := (intVec_mem_tLat_iff v hC z).mp hzM
    have hbu : IsUnit ((b : ℤ) : ℤ_[pOf v]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
      have hd := (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
      have h1 : ((pOf v ^ 1 : ℕ) : ℤ) ∣ b - 1 := Int.ModEq.dvd hb.symm
      have : (pOf v : ℤ) ∣ 1 := by have := dvd_sub hd (by simpa using h1); simpa using this
      exact (Fact.out : (pOf v).Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    have hcast : (fun i => (((b • u + W *ᵥ z) i : ℤ) : ℤ_[pOf v])) =
        (b : ℤ_[pOf v]) • (fun i => (u i : ℤ_[pOf v])) + B'' *ᵥ η := by
      rw [← hWCv, ← hη]; funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Int.cast_add, Int.cast_mul, cast_mulVec]
    apply primAt_of_isUnit_cast v
    refine exists_isUnit_of_bl_isUnit (f.map (Int.castRingHom ℤ_[pOf v])) _ (fun i => (ee i : ℤ_[pOf v])) ?_
    rw [hcast, hB'', bl_add_left, bl_add_left, bl_add_left, bl_smul_left, bl_smul_left, bl_smul_left,
      bl_smul_left, bl_comm _ k3, o23, bl_comm _ k4, o24, mul_zero, mul_zero, add_zero, add_zero]
    have := isUnit_add_p_mul (hbu.mul hBu) (η 0 * bl (f.map (Int.castRingHom ℤ_[pOf v])) w0
      (fun i => (ee i : ℤ_[pOf v])))
    convert this using 1; ring

end Pkg

end QuadFormsKB.Cassels.Ch11L92
