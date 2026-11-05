/-
# The proportion $\rho$ when the unimodular constituent is even

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264 (bibliography key `conwaysloane1988`).

For an even unimodular $U$ (blocks $2xy$, $2x^2 + 2xy + 2y^2$ of exponent $0$) and integral symmetric $B$, the
proportion $\rho(U, B)$ of $W$ with $U + 2W^{\mathsf T}BW \sim U$ (`rho`, `TwoAdicRho.lean`) is computed here:
$\rho(U, B) = 1$ if $B$ has even diagonal, and $\rho(U, B) = \frac12(1 + \varepsilon 2^{-t})$ otherwise, $2t = \dim U$,
$\varepsilon$ the sign of $U$ (the proportion of zeros of the quadratic form $x^{\mathsf T}Ux/2$ over $\mathbb F_2$).

**Method.** With $K = W^{\mathsf T}BW$ and $d_i = K_{ii}$, over $\mathbb Z/4$ the quadratic form of $U + 2K$ is
$Q_U(x) + 2x^{\mathsf T}d = Q_U(x + \lambda) - Q_U(\lambda)$, $\lambda = U^{-1}d$.
* If $Q_U(\lambda) = 0$, the transvection $x \mapsto x + (\lambda^{\mathsf T}Ux)\lambda$ carries $Q_U$ to $Q_{U+2K}$
  modulo $4$, and Hensel's lemma for even forms (`zpEquiv_of_even_congr`) gives $U + 2K \sim U$.
* If $Q_U(\lambda) = 2$, the Gauss sum $\sum_{x \bmod 4} \chi(Q(x))$ (`gsum`, $\chi(0) = 1$, $\chi(2) = -1$) changes
  sign; it is a $\mathbb Z_2$-invariant and equals $\varepsilon 8^t \neq 0$ for $U$, so $U + 2K \not\sim U$.
* Counting: $d \bmod 2$ is $(\ell(w_i))_i$, $\ell$ the diagonal of $B$ modulo $2$, so $\lambda$ is uniform when $\ell \ne 0$.
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicReduced

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

variable {a b : ℕ}

/-! ### Hensel's lemma for even forms, over $\mathbb Z_2$ -/

theorem odd_sq_mod8 {d : ℤ} (hd : ¬ 2 ∣ d) : (8 : ℤ) ∣ d ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
  have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  rw [this]
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  exact ⟨m, by rw [hm]; ring⟩

/-- **Hensel's lemma for even forms, over $\mathbb Z_2$**: if $S$ is integral symmetric with even diagonal and odd
determinant, and $T = S + D$ with $D$ symmetric, $D \equiv 0 \pmod 2$ and $D_{ii} \equiv 0 \pmod 4$, then
$T \sim S$. -/
theorem zpEquiv_of_even_congr {S T : Matrix (Fin a) (Fin a) ℤ} (hS : Sᵀ = S) (hSe : EvenDiag S) (hSd : ¬ 2 ∣ S.det)
    (hT : Tᵀ = T) (hD2 : AllDvd 2 (T - S)) (hD4 : ∀ i, (4 : ℤ) ∣ (T - S) i i) :
    ZpEquiv (S.map (Int.cast : ℤ → ℚ_[2])) (T.map (Int.cast : ℤ → ℚ_[2])) := by
  set D := T - S with hDdef
  set d := S.det
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) ℤ, V = d • S.adjugate := ⟨_, rfl⟩
  have hVs : Vᵀ = V := by rw [hV, transpose_smul, adjugate_transpose, hS]
  have hDs : Dᵀ = D := by rw [hDdef, transpose_sub, hS, hT]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) ℤ, M = V * D * V := ⟨_, rfl⟩
  have hMs : Mᵀ = M := by rw [hM, transpose_mul, transpose_mul, hVs, hDs, Matrix.mul_assoc]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin a) (Fin a) ℤ, D = (2 : ℤ) • N := by
    refine ⟨Matrix.of fun i j => D i j / 2, ?_⟩
    ext i j; simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' (hD2 i j)]
  have hNs : Nᵀ = N := by
    have : (2 : ℤ) • Nᵀ = (2 : ℤ) • N := by rw [← transpose_smul, ← hN, hDs]
    ext i j; have := congrArg (fun X => X i j) this; simp only [Matrix.smul_apply, smul_eq_mul] at this; omega
  have hNd : ∀ i, 2 ∣ N i i := fun i => by
    have h := hD4 i; rw [hN] at h; simp only [Matrix.smul_apply, smul_eq_mul] at h; omega
  have hM2 : AllDvd 2 M := by
    intro i j; rw [hM, hN, Matrix.mul_smul, Matrix.smul_mul]
    exact ⟨(V * N * V) i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩
  have hM4 : ∀ i, (4 : ℤ) ∣ M i i := by
    intro i
    rw [hM, hN, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    have : (2 : ℤ) ∣ (V * N * V) i i := by
      have hq := diag_quad hNs hNd V i
      rw [hVs] at hq
      exact ⟨_, hq⟩
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc]; ring⟩
  obtain ⟨N', hN'2, hN'⟩ := exists_approx hS hSe hMs hM2 hM4 3
  have hSM : S * M * S = (d ^ 4) • D := by
    have h1 : S * S.adjugate = d • (1 : Matrix (Fin a) (Fin a) ℤ) := Matrix.mul_adjugate S
    have h2 : S.adjugate * S = d • (1 : Matrix (Fin a) (Fin a) ℤ) := Matrix.adjugate_mul S
    rw [hM, hV]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, h1]
    rw [Matrix.mul_assoc _ S.adjugate S, h2]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
    congr 1; ring
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Matrix (Fin a) (Fin a) ℤ, N' = (2 : ℤ) • N₁ := by
    refine ⟨Matrix.of fun i j => N' i j / 2, ?_⟩
    ext i j; simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' (hN'2 i j)]
  have hodd1 : ¬ 2 ∣ (1 + N' * S).det := by
    rw [hN₁, Matrix.smul_mul]
    exact not_two_dvd_det_add (by simp) _
  refine dyadic_zpEquiv_of_int S T (1 + N' * S) hS hT (Int.not_even_iff_odd.mp fun h => hSd (even_iff_two_dvd.mp h))
    (Int.not_even_iff_odd.mp fun h => hodd1 (even_iff_two_dvd.mp h)) fun i j => ?_
  have h8 := hN' i j
  have hd4 : (8 : ℤ) ∣ d ^ 4 - 1 := by
    have := odd_sq_mod8 hSd
    have e : d ^ 4 - 1 = (d ^ 2 - 1) * (d ^ 2 + 1) := by ring
    rw [e]; exact this.mul_right _
  have e : ((1 + N' * S)ᵀ * S * (1 + N' * S) : Matrix (Fin a) (Fin a) ℤ) i j - T i j =
      ((1 + N' * S)ᵀ * S * (1 + N' * S) - (S + S * M * S) : Matrix (Fin a) (Fin a) ℤ) i j +
        (d ^ 4 - 1) * D i j := by
    rw [hSM, hDdef]; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [e]
  exact dvd_add (by simpa using h8) (hd4.mul_right _)

/-! ### Quadratic values modulo $4$ and the Gauss sum -/

/-- $Q_V(x) = x^{\mathsf T}Vx$ over $\mathbb Z/4$. -/
def qv (V : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) : ZMod (2 ^ 2) := x ⬝ᵥ V *ᵥ x

/-- $\chi(0) = 1$, $\chi(2) = -1$, $\chi = 0$ on odd classes. -/
def chi (z : ZMod (2 ^ 2)) : ℤ := if z = 0 then 1 else if z = 2 then -1 else 0

/-- **The Gauss sum** $\sum_{x \bmod 4}\chi(x^{\mathsf T}Vx)$. -/
def gsum (V : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) : ℤ := ∑ x, chi (qv V x)

theorem qv_congr (V G : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) :
    qv (Gᵀ * V * G) x = qv V (G *ᵥ x) := by
  unfold qv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem gsum_congr {V G : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))} (hG : IsUnit G) : gsum (Gᵀ * V * G) = gsum V := by
  obtain ⟨u, rfl⟩ := hG
  unfold gsum
  refine Fintype.sum_bijective (fun x => (u : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) *ᵥ x) ?_ _ _
    fun x => by rw [qv_congr]
  refine ⟨fun x y hxy => ?_, fun y => ⟨(↑u⁻¹ : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) *ᵥ y, ?_⟩⟩
  · have := congrArg (fun z => (↑u⁻¹ : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec] using this
  · simp [Matrix.mulVec_mulVec]

/-- The Gauss sum is an invariant of $\mathbb Z_2$-equivalence. -/
theorem gsum_eq_of_zpEquiv {U U' : Matrix (Fin a) (Fin a) ℤ}
    (h : ZpEquiv (U.map (Int.cast : ℤ → ℚ_[2])) (U'.map (Int.cast : ℤ → ℚ_[2]))) :
    gsum (red 2 U') = gsum (red 2 U) := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h 2
  change gsum (U'.map (Int.castRingHom (ZMod (2 ^ 2)))) = gsum (U.map (Int.castRingHom (ZMod (2 ^ 2))))
  rw [← hGe, gsum_congr hG]

theorem qv_add_transpose (A : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) :
    qv (A + Aᵀ) x = 2 * qv A x := by
  unfold qv
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose, dotProduct_comm x (x ᵥ* A),
    ← Matrix.dotProduct_mulVec]
  ring

/-- The quadratic values of an even form are even. -/
theorem qv_even {U : Matrix (Fin a) (Fin a) ℤ} (hUs : Uᵀ = U) (hUe : EvenDiag U) (x : Fin a → ZMod (2 ^ 2)) :
    ∃ z, qv (red 2 U) x = 2 * z := by
  refine ⟨qv (red 2 (halfUp U)) x, ?_⟩
  rw [← qv_add_transpose, ← red_transpose, ← red_add, halfUp_add_transpose hUs hUe]

theorem chi_sub_two {z : ZMod (2 ^ 2)} (hz : ∃ w, z = 2 * w) : chi (z - 2) = -chi z := by
  obtain ⟨w, rfl⟩ := hz
  revert w; decide

theorem chi_add {u v : ZMod (2 ^ 2)} (hu : ∃ w, u = 2 * w) (hv : ∃ w, v = 2 * w) : chi (u + v) = chi u * chi v := by
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨w', rfl⟩ := hv
  revert w w'; decide

theorem qv_add (A C : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) :
    qv (A + C) x = qv A x + qv C x := by
  unfold qv; rw [Matrix.add_mulVec, dotProduct_add]

theorem qv_smul (c : ZMod (2 ^ 2)) (A : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) :
    qv (c • A) x = c * qv A x := by
  unfold qv; rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem qv_sub (A C : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (x : Fin a → ZMod (2 ^ 2)) :
    qv (A - C) x = qv A x - qv C x := by
  unfold qv; rw [Matrix.sub_mulVec, dotProduct_sub]

theorem qv_add_vec {V : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))} (hV : Vᵀ = V) (x y : Fin a → ZMod (2 ^ 2)) :
    qv V (x + y) = qv V x + 2 * (x ⬝ᵥ V *ᵥ y) + qv V y := by
  unfold qv
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  have : y ⬝ᵥ V *ᵥ x = x ⬝ᵥ V *ᵥ y := by
    have h1 : V *ᵥ x = x ᵥ* V := by
      conv_lhs => rw [← hV]
      exact Matrix.mulVec_transpose V x
    rw [dotProduct_comm, h1, ← Matrix.dotProduct_mulVec]
  rw [this]; ring

theorem two_mul_sq (z : ZMod (2 ^ 2)) : 2 * (z * z) = 2 * z := by revert z; decide

/-- For symmetric integral $K$, $2Q_K(x) = 2\sum_i K_{ii}x_i$ over $\mathbb Z/4$. -/
theorem two_qv_K {K : Matrix (Fin a) (Fin a) ℤ} (hK : Kᵀ = K) (x : Fin a → ZMod (2 ^ 2)) :
    2 * qv (red 2 K) x = 2 * (x ⬝ᵥ fun i => ((K i i : ℤ) : ZMod (2 ^ 2))) := by
  set Kd : Matrix (Fin a) (Fin a) ℤ := Matrix.diagonal fun i => K i i
  have hKo : (K - Kd)ᵀ = K - Kd := by rw [transpose_sub, hK, Matrix.diagonal_transpose]
  have hKe : EvenDiag (K - Kd) := fun i => by simp [Kd]
  obtain ⟨z, hz⟩ := qv_even hKo hKe x
  have e : red 2 K = red 2 (K - Kd) + red 2 Kd := by rw [← red_add]; abel_nf
  rw [e, qv_add, hz, mul_add, show (2 : ZMod (2 ^ 2)) * (2 * z) = 0 by
    rw [← mul_assoc, show (2 : ZMod (2 ^ 2)) * 2 = 0 from rfl, zero_mul], zero_add]
  have hd : red 2 Kd = Matrix.diagonal fun i => ((K i i : ℤ) : ZMod (2 ^ 2)) := by
    ext i j; by_cases h : i = j <;> simp [Kd, h, Matrix.diagonal_apply]
  rw [hd]
  unfold qv
  simp only [Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show x i * (((K i i : ℤ) : ZMod (2 ^ 2)) * x i) = ((K i i : ℤ) : ZMod (2 ^ 2)) * (x i * x i) by ring,
    ← mul_assoc, mul_comm (2 : ZMod (2 ^ 2)), mul_assoc, two_mul_sq]
  ring

section Perturb

variable {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}

/-- The diagonal $d$ of $K = W^{\mathsf T}BW$ modulo $4$. -/
def dvec (B : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin b) (Fin a) ℤ) : Fin a → ZMod (2 ^ 2) :=
  fun i => (((Wᵀ * B * W) i i : ℤ) : ZMod (2 ^ 2))

/-- $\lambda = U^{-1}d$ over $\mathbb Z/4$. -/
noncomputable def lam (U : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin b) (Fin a) ℤ) :
    Fin a → ZMod (2 ^ 2) := (red 2 U)⁻¹ *ᵥ dvec B W

theorem qv_perturb (hUs : Uᵀ = U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B) (W : Matrix (Fin b) (Fin a) ℤ)
    (x : Fin a → ZMod (2 ^ 2)) :
    qv (red 2 (U + (2 : ℤ) • (Wᵀ * B * W))) x = qv (red 2 U) (x + lam U B W) - qv (red 2 U) (lam U B W) := by
  have hUr : (red 2 U)ᵀ = red 2 U := by rw [← red_transpose, hUs]
  have hu := isUnit_red_det (r := 2) hUd
  rw [red_add, red_smul, qv_add, qv_smul, qv_add_vec hUr]
  have hK := two_qv_K (quad_symm hBs W) x
  have e : red 2 U *ᵥ lam U B W = dvec B W := by
    rw [lam, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  rw [e]
  push_cast
  rw [hK]
  unfold dvec
  ring

theorem gsum_perturb (hUs : Uᵀ = U) (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    (W : Matrix (Fin b) (Fin a) ℤ) :
    gsum (red 2 (U + (2 : ℤ) • (Wᵀ * B * W))) =
      if qv (red 2 U) (lam U B W) = 0 then gsum (red 2 U) else -gsum (red 2 U) := by
  unfold gsum
  simp only [qv_perturb hUs hUd hBs W]
  rw [Fintype.sum_equiv (Equiv.addRight (lam U B W))
    (fun x => chi (qv (red 2 U) (x + lam U B W) - qv (red 2 U) (lam U B W)))
    (fun y => chi (qv (red 2 U) y - qv (red 2 U) (lam U B W))) (fun x => rfl)]
  split_ifs with hc
  · simp [hc]
  · obtain ⟨w, hw⟩ := qv_even hUs hUe (lam U B W)
    have hc2 : qv (red 2 U) (lam U B W) = 2 := by
      rw [hw] at hc ⊢; clear hw; revert hc; revert w; decide
    rw [hc2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => chi_sub_two (qv_even hUs hUe y)

/-- **No equivalence when $Q_U(\lambda) \ne 0$**, if the Gauss sum of $U$ is nonzero. -/
theorem not_good_of_qv (hUs : Uᵀ = U) (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    (hg : gsum (red 2 U) ≠ 0) {W : Matrix (Fin b) (Fin a) ℤ} (hc : qv (red 2 U) (lam U B W) ≠ 0) :
    ¬ Good U B W := fun h => by
  have h1 := gsum_eq_of_zpEquiv h
  rw [gsum_perturb hUs hUe hUd hBs W, if_neg hc] at h1
  exact hg (by linarith)

theorem qv_single (V : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (i : Fin a) : qv V (Pi.single i 1) = V i i := by
  unfold qv; rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]; rfl

theorem dot_single (V : Matrix (Fin a) (Fin a) (ZMod (2 ^ 2))) (i j : Fin a) :
    Pi.single i 1 ⬝ᵥ V *ᵥ Pi.single j 1 = V i j := by
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]; rfl

theorem int_dvd_of_zmod {z : ℤ} (h : ((z : ℤ) : ZMod (2 ^ 2)) = 0) : (4 : ℤ) ∣ z := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd z (2 ^ 2)).mp h
  simpa using this

/-- **Equivalence when $Q_U(\lambda) = 0$**: the transvection $x \mapsto x + (\lambda^{\mathsf T}Ux)\lambda$ carries the
quadratic values of $U$ to those of $U + 2W^{\mathsf T}BW$ modulo $4$, and Hensel's lemma for even forms lifts. -/
theorem good_of_qv (hUs : Uᵀ = U) (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    {W : Matrix (Fin b) (Fin a) ℤ} (hc : qv (red 2 U) (lam U B W) = 0) : Good U B W := by
  set l := lam U B W with hl
  set Λ : Fin a → ℤ := fun i => ((l i).val : ℤ) with hΛdef
  have hΛ : (fun i => ((Λ i : ℤ) : ZMod (2 ^ 2))) = l := by funext i; simp [Λ]
  set v : Fin a → ℤ := U *ᵥ Λ with hv
  set G₀ : Matrix (Fin a) (Fin a) ℤ := 1 + vecMulVec Λ v with hG₀
  have hUr : (red 2 U)ᵀ = red 2 U := by rw [← red_transpose, hUs]
  -- `G₀` has odd determinant
  obtain ⟨c, hc2⟩ : ∃ c, v ⬝ᵥ Λ = 2 * c := by
    set H := halfUp U
    have hU' : U = H + Hᵀ := (halfUp_add_transpose hUs hUe).symm
    refine ⟨Λ ⬝ᵥ H *ᵥ Λ, ?_⟩
    rw [hv, dotProduct_comm]
    conv_lhs => rw [hU']
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose, dotProduct_comm Λ (Λ ᵥ* H),
      ← Matrix.dotProduct_mulVec]
    ring
  have hdG : ¬ 2 ∣ G₀.det := by
    have e : G₀ = 1 + replicateCol Unit Λ * replicateRow Unit v := by
      rw [hG₀]; congr 1; ext i j; simp [vecMulVec_apply, Matrix.mul_apply, replicateCol, replicateRow]
    rw [e, det_one_add_replicateCol_mul_replicateRow, hc2]
    omega
  have hoddG : Odd G₀.det := Int.not_even_iff_odd.mp fun h => hdG (even_iff_two_dvd.mp h)
  have hoddU : Odd U.det := Int.not_even_iff_odd.mp fun h => hUd (even_iff_two_dvd.mp h)
  set S := G₀ᵀ * U * G₀ with hS
  set T := U + (2 : ℤ) • (Wᵀ * B * W) with hT
  have hSs : Sᵀ = S := quad_symm hUs G₀
  have hTs : Tᵀ = T := by rw [hT, transpose_add, transpose_smul, quad_symm hBs, hUs]
  have hSd : ¬ 2 ∣ S.det := by
    rw [hS, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    intro h
    have := (hoddG.mul hoddU).mul hoddG
    exact (Int.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  have h1 : ZpEquiv (U.map (Int.cast : ℤ → ℚ_[2])) (S.map (Int.cast : ℤ → ℚ_[2])) :=
    dyadic_zpEquiv_of_int U S G₀ hUs hSs hoddU hoddG fun i j => ⟨0, by simp [hS]⟩
  -- the quadratic values of `T` and `S` agree modulo `4`
  have hu := isUnit_red_det (r := 2) hUd
  have hUl : red 2 U *ᵥ l = dvec B W := by
    rw [hl, lam, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hq : ∀ x, qv (red 2 T) x = qv (red 2 S) x := by
    intro x
    have hG : red 2 G₀ *ᵥ x = x + ((red 2 U *ᵥ l) ⬝ᵥ x) • l := by
      rw [hG₀, red_add, red_one, Matrix.add_mulVec, Matrix.one_mulVec]
      congr 1
      have e : red 2 (vecMulVec Λ v) = vecMulVec l (red 2 U *ᵥ l) := by
        ext i j
        simp only [map_apply, vecMulVec_apply, map_mul, hv, Matrix.mulVec, dotProduct, map_sum]
        rw [← hΛ]; simp
      rw [e, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [hS, red_mul, red_mul, red_transpose, qv_congr, hG, qv_add_vec hUr, qv_perturb hUs hUd hBs W x, qv_add_vec hUr]
    have hsc : qv (red 2 U) (((red 2 U *ᵥ l) ⬝ᵥ x) • l) = ((red 2 U *ᵥ l) ⬝ᵥ x) ^ 2 * qv (red 2 U) l := by
      unfold qv; rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
    have hx : x ⬝ᵥ red 2 U *ᵥ l = (red 2 U *ᵥ l) ⬝ᵥ x := dotProduct_comm _ _
    rw [hsc, ← hl, hc, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hx]
    have := two_mul_sq ((red 2 U *ᵥ l) ⬝ᵥ x)
    linear_combination (-1 : ZMod (2 ^ 2)) * this
  -- hence `T - S` is even with diagonal divisible by `4`
  have hD0 : ∀ x, qv (red 2 (T - S)) x = 0 := fun x => by rw [red_sub, qv_sub, hq, sub_self]
  have hDs : (T - S)ᵀ = T - S := by rw [transpose_sub, hTs, hSs]
  have hD4 : ∀ i, (4 : ℤ) ∣ (T - S) i i := fun i => by
    have := hD0 (Pi.single i 1)
    rw [qv_single] at this
    exact int_dvd_of_zmod this
  have hD2 : AllDvd 2 (T - S) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact (dvd_trans ⟨2, by norm_num⟩ (hD4 i))
    · have hDr : (red 2 (T - S))ᵀ = red 2 (T - S) := by rw [← red_transpose, hDs]
      have := hD0 (Pi.single i 1 + Pi.single j 1)
      rw [qv_add_vec hDr, qv_single, qv_single, dot_single] at this
      have hii := hD4 i
      have hjj := hD4 j
      have h4 : (4 : ℤ) ∣ (T - S) i i + 2 * (T - S) i j + (T - S) j j :=
        int_dvd_of_zmod (by push_cast; exact this)
      omega
  exact h1.trans (zpEquiv_of_even_congr hSs (quad_evenDiag hUs hUe G₀) hSd hTs hD2 hD4)

end Perturb

/-! ### The Gauss sum of an even block list -/

theorem qv_orthSum {m n : ℕ} (F : Matrix (Fin m) (Fin m) (ZMod (2 ^ 2))) (G : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2)))
    (x : Fin (m + n) → ZMod (2 ^ 2)) :
    qv (orthSumMat F G) x = qv F (fun i => x (Fin.castAdd n i)) + qv G (fun j => x (Fin.natAdd m j)) := by
  unfold qv
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, orthSumG_cc, orthSumG_cn, orthSumG_nc, orthSumG_nn,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

theorem gsum_orthSum {m n : ℕ} {F : Matrix (Fin m) (Fin m) ℤ} {G : Matrix (Fin n) (Fin n) ℤ}
    (hF : Fᵀ = F) (hFe : EvenDiag F) (hG : Gᵀ = G) (hGe : EvenDiag G) :
    gsum (red 2 (orthSumMat F G)) = gsum (red 2 F) * gsum (red 2 G) := by
  have e : red 2 (orthSumMat F G) = orthSumMat (red 2 F) (red 2 G) := orthSumMat_map _ (map_zero _) F G
  unfold gsum
  rw [e]
  simp only [qv_orthSum]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Fintype.sum_equiv ((finSumFinEquiv.arrowCongr (Equiv.refl _)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)) _ _ fun x => ?_
  simp only [Equiv.trans_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_apply, Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd, id_eq,
    Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  exact chi_add (qv_even hF hFe _) (qv_even hG hGe _)

theorem gsum_hyp : gsum (red 2 (bInt (DyBlock.hyp 0))) = 8 := by decide

theorem gsum_ell : gsum (red 2 (bInt (DyBlock.ell 0))) = -8 := by decide

theorem gsum_intMat_even : ∀ L : List DyBlock, (∀ c ∈ L, blockExp c = 0 ∧ ¬ IsSqBlock c) →
    gsum (red 2 (intMat L)) = (Sign.prodList (L.map blockSign)).toInt * 8 ^ L.length
  | [], _ => by
    haveI : IsEmpty (Fin (dyDim [])) := inferInstanceAs (IsEmpty (Fin 0))
    have h0 : ∀ x : Fin (dyDim []) → ZMod (2 ^ 2), qv (red 2 (intMat [])) x = 0 := fun x => by
      simp [qv, dotProduct]
    unfold gsum
    simp only [h0]
    simp only [chi, if_true, Finset.sum_const, smul_eq_mul, mul_one, Sign.prodList, List.map_nil, Sign.toInt,
      List.length_nil, pow_zero]
    rw [Finset.card_univ, Fintype.card_unique]; rfl
  | c :: L, h => by
    have hc := h c (by simp)
    have hL : ∀ c' ∈ L, blockExp c' = 0 ∧ ¬ IsSqBlock c' := fun c' hc' => h c' (by simp [hc'])
    have he : EvenDiag (intMat L) := evenDiag_intMat L (fun c' hc' => (hL c' hc').1.ge)
      fun c' hc' hh => (hL c' hc').2 hh.1
    have hbe : EvenDiag (bInt c) := evenDiag_bInt c (fun hh => hc.2 hh.1) hc.1.ge
    show gsum (red 2 (orthSumMat (bInt c) (intMat L))) = _
    rw [gsum_orthSum (isSymm_bInt c).eq hbe (isSymm_intMat L).eq he, gsum_intMat_even L hL]
    simp only [List.map_cons, Sign.prodList, Sign.toInt_mul, List.length_cons, pow_succ]
    cases c with
    | sq e u => exact absurd trivial hc.2
    | hyp e => obtain rfl : e = 0 := hc.1; rw [gsum_hyp]; simp [blockSign, Sign.toInt]; ring
    | ell e => obtain rfl : e = 0 := hc.1; rw [gsum_ell]; simp [blockSign, Sign.toInt]; ring

/-! ### Counting -/

section Count

variable {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}

/-- $\Psi(W)_i = \sum_k B_{kk}W_{ki}$ over $\mathbb Z/4$: the diagonal of $W^{\mathsf T}BW$ modulo $2$, made additive. -/
def psi (B : Matrix (Fin b) (Fin b) ℤ) : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) →+ (Fin a → ZMod (2 ^ 2)) :=
  AddMonoidHom.mk' (fun W i => ∑ k, ((B k k : ℤ) : ZMod (2 ^ 2)) * W k i) fun W W' => by
    funext i; simp [Finset.sum_add_distrib, mul_add]

theorem two_mul_dvec_sub (hBs : Bᵀ = B) (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) (i : Fin a) :
    2 * (dvec B (lift W) i - psi B W i) = 0 := by
  have : NeZero (2 ^ 2) := ⟨by norm_num⟩
  have h1 : dvec B (lift W) i = (Wᵀ * red 2 B * W) i i := by
    unfold dvec
    rw [show ((((lift W)ᵀ * B * lift W) i i : ℤ) : ZMod (2 ^ 2)) = (red 2 ((lift W)ᵀ * B * lift W)) i i from rfl,
      red_mul, red_mul, red_transpose, red_lift]
  have hBr : (red 2 B)ᵀ = red 2 B := by rw [← red_transpose, hBs]
  -- the diagonal of `WᵀBW` against `Σ B_kk W_ki`
  set Wi : Fin b → ZMod (2 ^ 2) := fun k => W k i
  have h2 : (Wᵀ * red 2 B * W) i i = qv (red 2 B) Wi := by
    simp only [qv, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul,
      Finset.mul_sum, Wi]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h1, h2, mul_sub, two_qv_K hBs Wi]
  simp [psi, dotProduct, Wi, mul_comm]

theorem mul_eq_zero_of_two {u v : ZMod (2 ^ 2)} (hu : 2 * u = 0) (hv : 2 * v = 0) : u * v = 0 := by
  revert u v; decide

theorem qv_lam_eq (hUs : Uᵀ = U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B) (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) :
    qv (red 2 U) (lam U B (lift W)) = qv (red 2 U) ((red 2 U)⁻¹ *ᵥ psi B W) := by
  have hUr : (red 2 U)ᵀ = red 2 U := by rw [← red_transpose, hUs]
  set δ : Fin a → ZMod (2 ^ 2) := dvec B (lift W) - psi B W with hδ
  have h2δ : (2 : ZMod (2 ^ 2)) • δ = 0 := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hδ, Pi.sub_apply]
    exact two_mul_dvec_sub hBs W i
  set z := (red 2 U)⁻¹ *ᵥ δ
  have h2z : ∀ i, 2 * z i = 0 := fun i => by
    have : (2 : ZMod (2 ^ 2)) • z = (red 2 U)⁻¹ *ᵥ ((2 : ZMod (2 ^ 2)) • δ) := by rw [Matrix.mulVec_smul]
    rw [h2δ, Matrix.mulVec_zero] at this
    have := congrFun this i
    simpa using this
  have e : lam U B (lift W) = (red 2 U)⁻¹ *ᵥ psi B W + z := by
    rw [lam, ← Matrix.mulVec_add, hδ, add_sub_cancel]
  rw [e, qv_add_vec hUr]
  have h1 : (red 2 U)⁻¹ *ᵥ psi B W ⬝ᵥ red 2 U *ᵥ z = (red 2 U)⁻¹ *ᵥ psi B W ⬝ᵥ red 2 U *ᵥ z := rfl
  have hcross : 2 * ((red 2 U)⁻¹ *ᵥ psi B W ⬝ᵥ red 2 U *ᵥ z) = 0 := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul]
    have : (2 : ZMod (2 ^ 2)) • z = 0 := funext fun i => by simpa using h2z i
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hzz : qv (red 2 U) z = 0 := by
    unfold qv
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [mul_comm (red 2 U i j), ← mul_assoc, mul_eq_zero_of_two (h2z i) (h2z j), zero_mul]
  rw [hcross, hzz]; ring

theorem psi_surjective {k₀ : Fin b} (hk : ¬ 2 ∣ B k₀ k₀) :
    Function.Surjective (psi (a := a) B) := by
  intro y
  have hu : IsUnit ((B k₀ k₀ : ℤ) : ZMod (2 ^ 2)) := isUnit_odd hk
  refine ⟨fun k i => if k = k₀ then hu.unit⁻¹ * y i else 0, ?_⟩
  funext i
  simp only [psi, AddMonoidHom.mk'_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]

/-- **$\rho$ for an even unimodular $U$ next to a type I constituent**: if the Gauss sum of $U$ is nonzero and $B$ has
an odd diagonal entry, $\rho(U, B) = \frac12\left(1 + 4^{-a}\sum_{x \bmod 4}\chi(x^{\mathsf T}Ux)\right)$. -/
theorem rho_even (hUs : Uᵀ = U) (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    (hg : gsum (red 2 U) ≠ 0) {k₀ : Fin b} (hk : ¬ 2 ∣ B k₀ k₀) :
    rho U B = (1 + (gsum (red 2 U) : ℝ) / 4 ^ a) / 2 := by
  classical
  have : NeZero (2 ^ 2) := ⟨by norm_num⟩
  have hu := isUnit_red_det (r := 2) hUd
  set P : (Fin a → ZMod (2 ^ 2)) → Prop := fun y => qv (red 2 U) ((red 2 U)⁻¹ *ᵥ y) = 0
  have hgood : ∀ W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)), Good U B (lift W) ↔ P (psi B W) := fun W => by
    show _ ↔ qv (red 2 U) ((red 2 U)⁻¹ *ᵥ psi B W) = 0
    rw [← qv_lam_eq hUs hUd hBs W]
    exact ⟨fun h => by_contra fun hc => not_good_of_qv hUs hUe hUd hBs hg hc h,
      fun h => good_of_qv hUs hUe hUd hBs h⟩
  have h1 := card_comp_div (psi (a := a) B) (psi_surjective hk) P
  unfold rho
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [hgood]
  -- the proportion of good `W` is that of `y` with `P y`
  have hcardM : (Fintype.card (Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) : ℝ) = 4 ^ (b * a) := by
    rw [Fintype.card_eq_nat_card, Matrix.card_matrix]; simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]
  have hcardV : (Fintype.card (Fin a → ZMod (2 ^ 2)) : ℝ) = 4 ^ a := by simp [ZMod.card]
  rw [← hcardM, h1, hcardV]
  -- `P y` iff `Q_U(U⁻¹y) = 0`; count the zeros of `Q_U`
  have hbij : (Finset.univ.filter P).card = (Finset.univ.filter fun x => qv (red 2 U) x = 0).card := by
    have hl : ∀ x : Fin a → ZMod (2 ^ 2), (red 2 U)⁻¹ *ᵥ (red 2 U *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have hr : ∀ x : Fin a → ZMod (2 ^ 2), red 2 U *ᵥ ((red 2 U)⁻¹ *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    refine Finset.card_bij (fun y _ => (red 2 U)⁻¹ *ᵥ y) (fun y hy => ?_) (fun y _ y' _ h => ?_) (fun x hx => ?_)
    · simpa [P] using hy
    · have := congrArg (fun v => red 2 U *ᵥ v) h
      simpa only [hr] using this
    · refine ⟨red 2 U *ᵥ x, ?_, hl x⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, hl] at hx ⊢
      exact hx
  rw [hbij]
  have hval : ∀ x, chi (qv (red 2 U) x) = if qv (red 2 U) x = 0 then 1 else -1 := fun x => by
    obtain ⟨w, hw⟩ := qv_even hUs hUe x
    rw [hw]; clear hw; revert w; decide
  have hc4 : Fintype.card (Fin a → ZMod (2 ^ 2)) = 4 ^ a := by simp [ZMod.card]
  set Z := (Finset.univ.filter fun x : Fin a → ZMod (2 ^ 2) => qv (red 2 U) x = 0).card with hZ
  have hle : Z ≤ 4 ^ a := hc4 ▸ Finset.card_le_univ _
  have hgZ : gsum (red 2 U) = 2 * (Z : ℤ) - 4 ^ a := by
    unfold gsum
    simp only [hval]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_neg]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin a → ZMod (2 ^ 2)))) (fun x => qv (red 2 U) x = 0)
    rw [Finset.card_univ, hc4, ← hZ] at hsplit
    have hsZ : (Z : ℤ) + ((Finset.univ.filter fun x => ¬ qv (red 2 U) x = 0).card : ℤ) = 4 ^ a := by
      exact_mod_cast hsplit
    rw [← hZ]
    simp only [nsmul_eq_mul, mul_one, mul_neg]
    linarith
  have hg2 : (gsum (red 2 U) : ℝ) = 2 * (Z : ℝ) - 4 ^ a := by rw [hgZ]; push_cast; ring
  rw [hg2]
  field_simp
  ring

end Count

/-! ### The value of $\rho$ when $f_1$ has type II -/

theorem exists_odd_diag : ∀ L : List DyBlock, (∀ c ∈ L, c.Valid) → (∀ c ∈ L, 0 ≤ blockExp c) →
    (∃ c ∈ L, IsSqBlock c ∧ blockExp c = 0) → ∃ k, ¬ 2 ∣ intMat L k k
  | [], _, _, ⟨c, hc, _⟩ => absurd hc (by simp)
  | c :: L, hv, he, ⟨c', hc', hsq, h0⟩ => by
    rcases List.mem_cons.mp hc' with rfl | hL
    · cases c' with
      | sq e u =>
        obtain rfl : e = 0 := h0
        refine ⟨Fin.castAdd (dyDim L) (⟨0, Nat.one_pos⟩ : Fin (DyBlock.sq 0 u).dim), ?_⟩
        rw [show intMat (DyBlock.sq 0 u :: L) = orthSumMat (bInt (.sq 0 u)) (intMat L) from rfl, orthSumMat_cc]
        have h := valid_odd (hv (.sq 0 u) (by simp))
        have e : bInt (DyBlock.sq 0 u) (⟨0, Nat.one_pos⟩ : Fin (DyBlock.sq 0 u).dim) ⟨0, Nat.one_pos⟩ = u := by
          show (2 : ℤ) ^ (0 : ℤ).toNat * u = u; simp
        rw [e]; exact h
      | hyp e => exact absurd hsq id
      | ell e => exact absurd hsq id
    · obtain ⟨k, hk⟩ := exists_odd_diag L (fun x hx => hv x (by simp [hx])) (fun x hx => he x (by simp [hx]))
        ⟨c', hL, hsq, h0⟩
      refine ⟨Fin.natAdd c.dim k, ?_⟩
      show ¬ 2 ∣ orthSumMat (bInt c) (intMat L) (Fin.natAdd c.dim k) (Fin.natAdd c.dim k)
      rwa [orthSumMat_nn]

theorem dyDim_even_list : ∀ L : List DyBlock, (∀ c ∈ L, ¬ IsSqBlock c) → dyDim L = 2 * L.length
  | [], _ => rfl
  | c :: L, h => by
    have := dyDim_even_list L fun x hx => h x (by simp [hx])
    cases c with
    | sq e u => exact absurd trivial (h (.sq e u) (by simp))
    | hyp e => show 2 + dyDim L = _; rw [this]; simp; ring
    | ell e => show 2 + dyDim L = _; rw [this]; simp; ring

/-- **`RhoValueTwo` when $f_1$ has type II** (Conway–Sloane 1988, (3), Table 1): for a decomposition $D$ whose
constituent $f_1$ has type II and $f_2$ type I, $\rho(U, B) = P(f_1) = \frac12(1 + \varepsilon 2^{-t})$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264 (p = 2, the proportion rho when f_1 has type II)"]
theorem rho_eq_rhoValue_typeII {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) (he : ∀ b ∈ D, 0 ≤ blockExp b)
    (h0 : (blockSymbol D 0).type = .II) (h1 : (blockSymbol D 1).type = .I) :
    rho (intMat (low D)) (intMat (high D)) = rhoValue (blockSymbol D) := by
  have hnsq := not_sq_of_typeII h0
  have hL : ∀ c ∈ low D, blockExp c = 0 ∧ ¬ IsSqBlock c := fun c hc => ⟨exp_low c hc, hnsq c hc⟩
  have hg := gsum_intMat_even (low D) hL
  have hUs := (isSymm_intMat (low D)).eq
  have hUe : EvenDiag (intMat (low D)) := evenDiag_intMat_of_typeII (low D) (fun c hc => (exp_low c hc).ge)
    (by rw [blockSymbol_low_zero]; exact h0)
  -- an odd diagonal entry of `B`
  have hsq1 : ∃ c ∈ high D, IsSqBlock c ∧ blockExp c = 0 := by
    have h1' : (blockSymbol (high D) 0).type = .I := by rw [blockSymbol_high]; exact h1
    unfold blockSymbol at h1'
    simp only at h1'
    by_contra hn
    push Not at hn
    have : ((high D).filter fun c => blockExp c = ((0 : ℕ) : ℤ)).any (fun c => decide (IsSqBlock c)) = false := by
      rw [List.any_eq_false]
      intro c hc hsq
      have hc' := List.mem_filter.mp hc
      exact hn c hc'.1 (by simpa using hsq) (by simpa using hc'.2)
    rw [this] at h1'
    exact absurd h1' (by decide)
  have heh : ∀ c ∈ high D, 0 ≤ blockExp c := by
    intro c hc
    simp only [high, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    obtain ⟨c', ⟨hc', hc0⟩, rfl⟩ := hc
    rw [blockExp_lowerB]; have := he c' hc'; omega
  obtain ⟨k, hk⟩ := exists_odd_diag (high D) (valid_high hv) heh hsq1
  have hε : (Sign.prodList ((low D).map blockSign)) = (blockSymbol D 0).sign := by
    rw [← blockSymbol_low_zero]
    unfold blockSymbol
    simp only
    congr 2
    exact (List.filter_eq_self.mpr fun c hc => by simpa using exp_low c hc).symm
  have hdim : (blockSymbol D 0).dim = 2 * (low D).length := by
    rw [← dyDim_low, dyDim_even_list _ hnsq]
  have hgne : gsum (red 2 (intMat (low D))) ≠ 0 := by
    rw [hg]
    have : (Sign.prodList ((low D).map blockSign)).toInt ≠ 0 := by
      cases Sign.prodList ((low D).map blockSign) <;> decide
    exact mul_ne_zero this (pow_ne_zero _ (by norm_num))
  rw [rho_even hUs hUe (det_low_odd D hv) (isSymm_intMat _).eq hgne hk, hg, hε]
  unfold rhoValue pII
  rw [if_pos h0, if_neg (by rw [h1]; decide), hdim, dyDim_even_list _ hnsq]
  simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  have e : ((8 : ℝ) ^ (low D).length) / 4 ^ (2 * (low D).length) = ((2 : ℝ) ^ (low D).length)⁻¹ := by
    rw [pow_mul, show ((4 : ℝ) ^ 2) = 16 by norm_num, ← div_pow, show (8 : ℝ) / 16 = 2⁻¹ by norm_num, inv_pow]
  rw [mul_div_assoc, e]

/-- **Input: the value of $\rho$ next to an odd unimodular constituent** (Conway–Sloane 1988, (3), p. 263, Table 1,
p. 264, §5–6, pp. 265–266; not proved in the paper). `RhoValueTwo` restricted to the decompositions whose constituent
$f_1$ has type I; the case of $f_1$ of type II is proved (`rho_eq_rhoValue_typeII`). For such $D$, with $U$ the blocks
of exponent $0$ and $B$ the others lowered by one, the proportion $\rho(U, B)$ of $W \in M_{b\times a}(\mathbb Z/4)$
with $U + 2W^{\mathsf T}BW \sim U$ over $\mathbb Z_2$ is `rhoValue σ`.
Field:
- `rho_eq`: the identity for every such $D$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §5–6, pp. 265–266 (p = 2, rho next to an odd f_1)"]
structure RhoValueTwoTypeI : Prop where
  rho_eq : ∀ D : List DyBlock, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) → (blockSymbol D 0).type = .I →
    rho (intMat (low D)) (intMat (high D)) = rhoValue (blockSymbol D)

/-- `RhoValueTwo` from its type I part. -/
theorem rhoValueTwo_of_typeI (R : RhoValueTwoTypeI) : RhoValueTwo := by
  refine ⟨fun D hv he h => ?_⟩
  by_cases h0 : (blockSymbol D 0).type = .I
  · exact R.rho_eq D hv he h0
  · have h0' : (blockSymbol D 0).type = .II := by cases h' : (blockSymbol D 0).type <;> simp_all
    have h1 : (blockSymbol D 1).type = .I := h.resolve_left h0
    exact rho_eq_rhoValue_typeII hv he h0' h1

/-- **Formula (3) at $p = 2$ from the two remaining inputs** (both about a single odd unimodular constituent $f_1$). -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); Tables 1–2, p. 264; §6, p. 266"]
theorem pMassFormulaTwo_of_typeI_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwoTypeI) : PMassFormulaTwo :=
  pMassFormulaTwo_of_inputs I (rhoValueTwo_of_typeI R)

end QuadFormsKB.ConwaySloane.Mass.Two

namespace QuadFormsKB.ConwaySloane.Mass

open Two

/-- **The mass formula from the genus symbols, conditional only on the two inputs about an odd unimodular constituent
at $p = 2$** (Conway–Sloane 1988, (2), (3), §7, §9): for a positive definite symmetric integral Gram matrix $A$ of
dimension $n \ge 3$, $m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$, assuming
`PMassUnimodularTwoTypeI` and `RhoValueTwoTypeI`. Unconditional when the 2-adic constituent $f_1$ of every splitting
step has type II, in particular when all 2-adic constituents have type II (`mass_eq_stdMass_mul_symbols_typeII`). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols_of_typeI_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwoTypeI) {n : ℕ}
    (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ) (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) :=
  mass_eq_stdMass_mul_symbols_of_inputs I (rhoValueTwo_of_typeI R) hn hA hQ τ N₂ hτ hτN σ N hodd

/-- **§9 (i)** (Conway–Sloane 1988, pp. 269–272): $m(\mathrm{diag}(7,1,1)) = \frac3{16}$, conditional only on the two
inputs about an odd unimodular constituent at $p = 2$. -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass_of_typeI_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwoTypeI) :
    Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 :=
  example_i_mass_of_inputs I (rhoValueTwo_of_typeI R)

end QuadFormsKB.ConwaySloane.Mass
