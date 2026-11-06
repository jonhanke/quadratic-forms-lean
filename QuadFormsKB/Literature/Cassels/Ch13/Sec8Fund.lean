/-
# Cassels, Chapter 13, §6 Theorem 6.1 and §8 Theorem 8.1: fundamental polygon and generators

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, Theorem 6.1 (p. 304, proved in §8,
pp. 313–316) and Theorem 8.1 (p. 316), from the Dirichlet domain of `Sec8.lean`. Setting and notation as in
`Sec8.lean`: $f$ is an integral ternary form with real matrix $F = L^{\mathsf T}\operatorname{diag}(1, 1, -1)L$, and
$T \in O^+(f)$ acts on the disc $\mathcal D$ by `actD L T`.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec8

open Matrix

namespace QuadFormsKB.Reduction

open S8

/-! ### Helpers for Theorem 8.1: `coshDist` versus the Euclidean distance -/

/-- Helper: the Euclidean distance is controlled by $\cosh d$: $|x-\zeta|^2 \le 2(\cosh d(\zeta,x) - 1)$. -/
theorem sq_dist_le_coshDist {ζ x : Fin 2 → ℝ} (hζ : ζ ∈ disc) (hx : x ∈ disc) :
    (x 0 - ζ 0) ^ 2 + (x 1 - ζ 1) ^ 2 ≤ 2 * (coshDist ζ x - 1) := by
  have hsa := Real.sqrt_pos.2 (disc_u_pos hζ)
  have hsb := Real.sqrt_pos.2 (disc_u_pos hx)
  have ea := Real.sq_sqrt (disc_u_pos hζ).le
  have eb := Real.sq_sqrt (disc_u_pos hx).le
  have hc1 := one_le_coshDist hζ hx
  have hA : 1 - ζ 0 * x 0 - ζ 1 * x 1 =
      coshDist ζ x * (√(1 - ζ 0 ^ 2 - ζ 1 ^ 2) * √(1 - x 0 ^ 2 - x 1 ^ 2)) := by
    rw [coshDist_eq hζ hx]; field_simp
  set sa := √(1 - ζ 0 ^ 2 - ζ 1 ^ 2)
  set sb := √(1 - x 0 ^ 2 - x 1 ^ 2)
  have hζ' : ζ 0 ^ 2 + ζ 1 ^ 2 < 1 := hζ
  have hx' : x 0 ^ 2 + x 1 ^ 2 < 1 := hx
  have hsa1 : sa ≤ 1 := by nlinarith [sq_nonneg (ζ 0), sq_nonneg (ζ 1)]
  have hsb1 : sb ≤ 1 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hs1 : sa * sb ≤ 1 := by nlinarith [mul_nonneg hsa.le (sub_nonneg.2 hsb1)]
  have key : (x 0 - ζ 0) ^ 2 + (x 1 - ζ 1) ^ 2 = 2 * (coshDist ζ x * (sa * sb)) - sa ^ 2 - sb ^ 2 := by
    linear_combination 2 * hA + ea + eb
  rw [key]
  nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hs1), sq_nonneg (sa - sb)]

/-- Helper: $\cosh d$ is close to $1$ for Euclidean-close points of $\{1 - |\cdot|^2 \ge \kappa\}$. -/
theorem coshDist_le_of_close {ζ x : Fin 2 → ℝ} (hζ : ζ ∈ disc) (hx : x ∈ disc) {κ : ℝ} (hκ : 0 < κ)
    (hκζ : κ ≤ 1 - ζ 0 ^ 2 - ζ 1 ^ 2) (hκx : κ ≤ 1 - x 0 ^ 2 - x 1 ^ 2) :
    coshDist ζ x ≤ 1 + ((x 0 - ζ 0) ^ 2 + (x 1 - ζ 1) ^ 2) / (2 * κ ^ 2) := by
  have hsa := Real.sqrt_pos.2 (disc_u_pos hζ)
  have hsb := Real.sqrt_pos.2 (disc_u_pos hx)
  have ea := Real.sq_sqrt (disc_u_pos hζ).le
  have eb := Real.sq_sqrt (disc_u_pos hx).le
  have hc1 := one_le_coshDist hζ hx
  have hA : 1 - ζ 0 * x 0 - ζ 1 * x 1 =
      coshDist ζ x * (√(1 - ζ 0 ^ 2 - ζ 1 ^ 2) * √(1 - x 0 ^ 2 - x 1 ^ 2)) := by
    rw [coshDist_eq hζ hx]; field_simp
  set sa := √(1 - ζ 0 ^ 2 - ζ 1 ^ 2)
  set sb := √(1 - x 0 ^ 2 - x 1 ^ 2)
  set c := coshDist ζ x
  have hs2 : (sa * sb) ^ 2 = (1 - ζ 0 ^ 2 - ζ 1 ^ 2) * (1 - x 0 ^ 2 - x 1 ^ 2) := by
    rw [mul_pow, ea, eb]
  have hκs : κ ^ 2 ≤ (sa * sb) ^ 2 := by
    rw [hs2]; nlinarith
  have hA2 : (1 - ζ 0 * x 0 - ζ 1 * x 1) ^ 2 - (1 - ζ 0 ^ 2 - ζ 1 ^ 2) * (1 - x 0 ^ 2 - x 1 ^ 2) ≤
      (x 0 - ζ 0) ^ 2 + (x 1 - ζ 1) ^ 2 := by
    nlinarith [sq_nonneg (ζ 0 * x 1 - ζ 1 * x 0)]
  have hcc : (1 - ζ 0 * x 0 - ζ 1 * x 1) ^ 2 = c ^ 2 * (sa * sb) ^ 2 := by rw [hA]; ring
  have hc2 : 0 ≤ c ^ 2 - 1 := by nlinarith
  rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  calc (c - 1) * (2 * κ ^ 2) ≤ κ ^ 2 * (c ^ 2 - 1) := by
        nlinarith [mul_nonneg (sq_nonneg κ) (sq_nonneg (c - 1))]
    _ ≤ (sa * sb) ^ 2 * (c ^ 2 - 1) := mul_le_mul_of_nonneg_right hκs hc2
    _ = (1 - ζ 0 * x 0 - ζ 1 * x 1) ^ 2 - (1 - ζ 0 ^ 2 - ζ 1 ^ 2) * (1 - x 0 ^ 2 - x 1 ^ 2) := by
        rw [hcc, ← hs2]; ring
    _ ≤ _ := hA2

/-- Helper: scalar multiples $s\vec w$, $0 \le s \le 1$, of a point of the disc are in the disc. -/
theorem smul_mem_disc {w : Fin 2 → ℝ} (hw : w ∈ disc) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : s • w ∈ disc := by
  have hw' : w 0 ^ 2 + w 1 ^ 2 < 1 := hw
  show (s • w) 0 ^ 2 + (s • w) 1 ^ 2 < 1
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs1), sq_nonneg (w 0), sq_nonneg (w 1), mul_nonneg (mul_nonneg hs0 (sub_nonneg.2 hs1)) (add_nonneg (sq_nonneg (w 0)) (sq_nonneg (w 1)))]

/-- Helper: $\cosh d$ between two points of a segment from $0$ to $\vec w$. -/
theorem coshDist_smul_le {w : Fin 2 → ℝ} (hw : w ∈ disc) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    coshDist (s • w) (t • w) ≤ 1 + (t - s) ^ 2 / (2 * (1 - w 0 ^ 2 - w 1 ^ 2) ^ 2) := by
  have hw' : w 0 ^ 2 + w 1 ^ 2 < 1 := hw
  have hκ : 0 < 1 - w 0 ^ 2 - w 1 ^ 2 := by linarith
  have h := coshDist_le_of_close (smul_mem_disc hw hs0 hs1) (smul_mem_disc hw ht0 ht1) hκ
    (by simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [sq_nonneg (w 0), sq_nonneg (w 1),
        mul_nonneg (sub_nonneg.2 hs1) (add_nonneg hs0 (by norm_num : (0:ℝ) ≤ 1)),
        mul_nonneg (mul_nonneg hs0 hs0) (add_nonneg (sq_nonneg (w 0)) (sq_nonneg (w 1))),
        mul_nonneg (sub_nonneg.2 (pow_le_one₀ hs0 hs1 (n := 2))) (add_nonneg (sq_nonneg (w 0)) (sq_nonneg (w 1)))])
    (by simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [sq_nonneg (w 0), sq_nonneg (w 1),
        mul_nonneg (sub_nonneg.2 (pow_le_one₀ ht0 ht1 (n := 2))) (add_nonneg (sq_nonneg (w 0)) (sq_nonneg (w 1)))])
  refine h.trans ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  gcongr 1 + ?_
  have : (t * w 0 - s * w 0) ^ 2 + (t * w 1 - s * w 1) ^ 2 = (t - s) ^ 2 * (w 0 ^ 2 + w 1 ^ 2) := by ring
  rw [this]
  have : (t - s) ^ 2 * (w 0 ^ 2 + w 1 ^ 2) ≤ (t - s) ^ 2 * 1 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Helper: $\cosh d$ is invariant under $O^+(f)$. -/
theorem coshDist_actD {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) {ξ η : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    coshDist (actD L (castM T.val) ξ) (actD L (castM T.val) η) = coshDist ξ η :=
  (isLor_conj_aut hL hF (aut_of_autPlus hT)).coshDist_flt hξ hη

/-! ### Helpers for Theorem 6.1: a nontrivial proper automorph fixes only a collinear set -/

theorem bil_smul2 (a b : ℝ) (X Y : Fin 3 → ℝ) : bil (a • X) (b • Y) = a * b * bil X Y := by
  simp only [bil, Pi.smul_apply, smul_eq_mul]; ring

theorem smul_inv_aux (u x : Fin 3 → ℝ) (h2 : u 2 ≠ 0) (hl : x = (u 2)⁻¹ • u) : u = u 2 • x := by
  rw [hl, smul_smul, mul_inv_cancel₀ h2, one_smul]

/-- Helper: a fixed point of a Lorentz matrix on the disc is an eigenvector with eigenvalue $\pm1$. -/
theorem fixed_eigen {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc)
    (hfix : flt P ξ = ξ) : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ P *ᵥ liftPt ξ = ε • liftPt ξ := by
  have h2 := hP.last_ne hξ
  have hl := liftPt_flt_of h2
  rw [hfix] at hl
  have hu : P *ᵥ liftPt ξ = (P *ᵥ liftPt ξ) 2 • liftPt ξ := smul_inv_aux _ _ h2 hl
  refine ⟨(P *ᵥ liftPt ξ) 2, ?_, hu⟩
  have hb := hP.bil_mulVec (liftPt ξ) (liftPt ξ)
  have hb' : bil ((P *ᵥ liftPt ξ) 2 • liftPt ξ) ((P *ᵥ liftPt ξ) 2 • liftPt ξ) = bil (liftPt ξ) (liftPt ξ) := by
    rw [← hu]; exact hb
  rw [bil_smul2, bil_liftPt] at hb'
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have h3 : ((P *ᵥ liftPt ξ) 2 - 1) * ((P *ᵥ liftPt ξ) 2 + 1) = 0 := by
    have hneg : ξ 0 * ξ 0 + ξ 1 * ξ 1 - 1 ≠ 0 := by nlinarith
    apply mul_right_cancel₀ hneg
    linarith
  rcases mul_eq_zero.1 h3 with h | h
  · left; linarith
  · right; linarith

/-- Helper: the coordinates of an eigenvector equation. -/
theorem eig_coords {P : Matrix (Fin 3) (Fin 3) ℝ} {ε : ℝ} {p : Fin 2 → ℝ}
    (h : P *ᵥ liftPt p = ε • liftPt p) :
    P 0 0 * p 0 + P 0 1 * p 1 + P 0 2 = ε * p 0 ∧ P 1 0 * p 0 + P 1 1 * p 1 + P 1 2 = ε * p 1 ∧
      P 2 0 * p 0 + P 2 1 * p 1 + P 2 2 = ε := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [mulVec, dotProduct, Fin.sum_univ_three, liftPt] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem castM_injective' {A B : Matrix (Fin 3) (Fin 3) ℤ} (h : castM A = castM B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [castM] using this

theorem castM_neg' (A : Matrix (Fin 3) (Fin 3) ℤ) : castM (-A) = -castM A := by
  ext i j; simp [castM]

/-- Helper: a proper integral automorph fixing three non-collinear points of the disc is the identity. -/
theorem eq_one_of_three_fixed {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q)
    {p q r : Fin 2 → ℝ} (hp : p ∈ disc) (hq : q ∈ disc) (hr : r ∈ disc)
    (hpf : actD L (castM T.val) p = p) (hqf : actD L (castM T.val) q = q)
    (hrf : actD L (castM T.val) r = r)
    (hdet : (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0) ≠ 0) : T = 1 := by
  have hP := isLor_conj_aut hL hF (aut_of_autPlus hT)
  set P := L * castM T.val * L⁻¹ with hPdef
  obtain ⟨εp, hεp, hpe⟩ := fixed_eigen hP hp hpf
  obtain ⟨εq, hεq, hqe⟩ := fixed_eigen hP hq hqf
  obtain ⟨εr, hεr, hre⟩ := fixed_eigen hP hr hrf
  have same : ∀ {x y : Fin 2 → ℝ} {a b : ℝ}, x ∈ disc → y ∈ disc → (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      P *ᵥ liftPt x = a • liftPt x → P *ᵥ liftPt y = b • liftPt y → a = b := by
    intro x y a b hx hy ha hb hxe hye
    have h := hP.bil_mulVec (liftPt x) (liftPt y)
    rw [hxe, hye, bil_smul2, bil_liftPt] at h
    have hlt := inner_lt_one hx hy
    have hab : a * b = 1 := by
      have : (a * b - 1) * (x 0 * y 0 + x 1 * y 1 - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | (exfalso; norm_num at hab)
  have e1 := same hp hq hεp hεq hpe hqe
  have e2 := same hp hr hεp hεr hpe hre
  subst e1; subst e2
  set ε := εp
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![p 0, q 0, r 0; p 1, q 1, r 1; 1, 1, 1]
  have hMdet : M.det = (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0) := by
    simp [M, Matrix.det_fin_three]; ring
  have hMu : IsUnit M.det := by rw [hMdet]; exact isUnit_iff_ne_zero.2 hdet
  obtain ⟨a0, a1, a2⟩ := eig_coords hpe
  obtain ⟨b0, b1, b2⟩ := eig_coords hqe
  obtain ⟨c0, c1, c2⟩ := eig_coords hre
  have hPM : P * M = ε • M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith
  have hP1 : P = ε • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    calc P = P * (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv M hMu, Matrix.mul_one]
      _ = (P * M) * M⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = ε • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [hPM, Matrix.smul_mul, Matrix.mul_nonsing_inv M hMu]
  have hTe : castM T.val = ε • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    have h : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hL
    calc castM T.val = (L⁻¹ * L) * castM T.val * (L⁻¹ * L) := by rw [h]; simp
      _ = L⁻¹ * P * L := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = ε • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [hP1]; simp [h]
  have hdetT : T.val.det = 1 := (Siegel.mem_autPlus_iff.1 hT).2
  rcases hεp with h1 | h1
  · rw [h1, one_smul] at hTe
    have : T.val = 1 := castM_injective' (by rw [hTe, castM_one])
    exact Units.ext this
  · exfalso
    rw [h1, neg_one_smul] at hTe
    have : T.val = -1 := castM_injective' (by rw [hTe, castM_neg', castM_one])
    rw [this] at hdetT
    simp [Matrix.det_neg] at hdetT

/-- Helper: a line $\{\xi : a \cdot \xi = a \cdot p\}$ of the plane has Lebesgue measure zero. -/
theorem volume_line_eq_zero {a : Fin 2 → ℝ} (ha : a ≠ 0) (p : Fin 2 → ℝ) :
    MeasureTheory.volume {ξ : Fin 2 → ℝ | a ⬝ᵥ ξ = a ⬝ᵥ p} = 0 := by
  let f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun ξ => a ⬝ᵥ ξ
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  let s : AffineSubspace ℝ (Fin 2 → ℝ) := AffineSubspace.mk' p (LinearMap.ker f)
  have hs : (s : Set (Fin 2 → ℝ)) = {ξ | a ⬝ᵥ ξ = a ⬝ᵥ p} := by
    ext ξ
    simp only [SetLike.mem_coe, s, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, Set.mem_ofPred_eq]
    show a ⬝ᵥ (ξ - p) = 0 ↔ _
    rw [dotProduct_sub, sub_eq_zero]
  have hne : s ≠ ⊤ := by
    intro h
    have hm : p + a ∈ s := by rw [h]; trivial
    have hm' : p + a ∈ (s : Set (Fin 2 → ℝ)) := hm
    rw [hs] at hm'
    simp only [Set.mem_ofPred_eq, dotProduct_add] at hm'
    have : a ⬝ᵥ a = 0 := by linarith
    exact ha (dotProduct_self_eq_zero.1 this)
  rw [← hs]
  exact MeasureTheory.Measure.addHaar_affineSubspace _ s hne

/-- Helper: for $T \ne 1$ the fixed set of $T$ on $\mathcal D$ has measure zero. -/
theorem volume_fixed_eq_zero {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) (hT1 : T ≠ 1) :
    MeasureTheory.volume {ξ : Fin 2 → ℝ | ξ ∈ disc ∧ actD L (castM T.val) ξ = ξ} = 0 := by
  set Fx := {ξ : Fin 2 → ℝ | ξ ∈ disc ∧ actD L (castM T.val) ξ = ξ} with hFx
  by_cases h : ∃ p ∈ Fx, ∃ q ∈ Fx, p ≠ q
  · obtain ⟨p, hp, q, hq, hpq⟩ := h
    have hcol : ∀ r ∈ Fx, (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0) = 0 := by
      intro r hr
      by_contra hd
      exact hT1 (eq_one_of_three_fixed hL hF hT hp.1 hq.1 hr.1 hp.2 hq.2 hr.2 hd)
    set a : Fin 2 → ℝ := ![-(q 1 - p 1), q 0 - p 0] with ha
    have ha0 : a ≠ 0 := by
      intro h0
      apply hpq
      have h1 : q 1 - p 1 = 0 := by have := congrFun h0 0; simp [ha] at this; linarith
      have h2 : q 0 - p 0 = 0 := by have := congrFun h0 1; simp [ha] at this; linarith
      ext i; fin_cases i
      · simp; linarith
      · simp; linarith
    refine MeasureTheory.measure_mono_null (fun r hr => ?_) (volume_line_eq_zero ha0 p)
    have := hcol r hr
    simp only [Set.mem_ofPred_eq, ha, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · push Not at h
    exact Set.Subsingleton.measure_zero (fun p hp q hq => h p hp q hq) _

/-- Helper: there is a point of $\mathcal D$ whose stabilizer in $O^+(f)$ is trivial. -/
theorem exists_generic_point {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ β ∈ disc, ∀ T ∈ Siegel.AutPlus Q, actD L (castM T.val) β = β → T = 1 := by
  by_contra hcon
  push Not at hcon
  set W : Set (Fin 2 → ℝ) := {ξ | ξ 0 ^ 2 + ξ 1 ^ 2 < 1 / 2} with hW
  have hWo : IsOpen W := isOpen_lt (by fun_prop) continuous_const
  have h0W : (0 : Fin 2 → ℝ) ∈ W := by simp [hW]
  have hWd : ∀ β ∈ W, β ∈ disc := fun β hβ => by
    have : β 0 ^ 2 + β 1 ^ 2 < 1 / 2 := hβ
    show β 0 ^ 2 + β 1 ^ 2 < 1
    linarith
  have hR : ∀ β ∈ W, hypDist 0 β ≤ Real.arcosh 2 := by
    intro β hβ
    have hβ' : β 0 ^ 2 + β 1 ^ 2 < 1 / 2 := hβ
    unfold hypDist
    rw [coshDist_zero_left]
    have hpos : 0 < 1 - β 0 ^ 2 - β 1 ^ 2 := by linarith
    have hs : 0 < √(1 - β 0 ^ 2 - β 1 ^ 2) := Real.sqrt_pos.2 hpos
    have hs2 : 1 / 2 ≤ √(1 - β 0 ^ 2 - β 1 ^ 2) := by
      rw [Real.le_sqrt' (by norm_num)]; nlinarith
    have hle : 1 / √(1 - β 0 ^ 2 - β 1 ^ 2) ≤ 2 := by
      rw [div_le_iff₀ hs]; linarith
    exact (Real.arcosh_le_arcosh (by positivity) (by norm_num)).2 hle
  set S : Set (GL (Fin 3) ℤ) := {T | T ∈ Siegel.AutPlus Q ∧ hypDist 0 (actD L (castM T.val) 0) ≤ 2 * Real.arcosh 2 ∧
    T ≠ 1} with hS
  have hSfin : S.Finite := (finite_dist_le hL hF (2 * Real.arcosh 2)).subset fun T hT => ⟨hT.1, hT.2.1⟩
  have hcover : W ⊆ ⋃ T ∈ S, {ξ : Fin 2 → ℝ | ξ ∈ disc ∧ actD L (castM T.val) ξ = ξ} := by
    intro β hβ
    obtain ⟨T, hT, hfix, hT1⟩ := hcon β (hWd β hβ)
    simp only [Set.mem_iUnion]
    refine ⟨T, ⟨hT, ?_, hT1⟩, hWd β hβ, hfix⟩
    have h1 := hd_triangle zero_mem_disc (hWd β hβ) (actD_mem_disc hL hF hT zero_mem_disc)
    have h2 := hypDist_actD hL hF hT (hWd β hβ) zero_mem_disc
    rw [hfix] at h2
    have h3 := hd_comm (hWd β hβ) zero_mem_disc
    have := hR β hβ
    linarith
  have hnull : MeasureTheory.volume (⋃ T ∈ S, {ξ : Fin 2 → ℝ | ξ ∈ disc ∧ actD L (castM T.val) ξ = ξ}) = 0 := by
    rw [MeasureTheory.measure_biUnion_null_iff hSfin.countable]
    intro T hT
    exact volume_fixed_eq_zero hL hF hT.1 hT.2.2
  have hpos : 0 < MeasureTheory.volume W := hWo.measure_pos _ ⟨0, h0W⟩
  have := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hcover
  rw [hnull] at this
  exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl _)

/-! ### Helpers for Theorem 6.1: Lorentz maps preserve convexity on the disc -/

theorem pos_aux {a b X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hX : X ≠ 0) (hXY : 0 < X * Y) :
    0 < X * (a * X + b * Y) := by
  have hX2 : 0 < X ^ 2 := by positivity
  have : X * (a * X + b * Y) = a * X ^ 2 + b * (X * Y) := by ring
  rw [this]
  rcases ha.eq_or_lt with h | h
  · have hb1 : b = 1 := by linarith
    rw [← h, hb1]; linarith
  · have := mul_pos h hX2
    have := mul_nonneg hb hXY.le
    linarith

/-- Helper: a Lorentz map sends a convex combination of two points of the disc to a convex combination of the
images. -/
theorem flt_convex_comb {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {x y : Fin 2 → ℝ} (hx : x ∈ disc)
    (hy : y ∈ disc) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ a' b' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ a' + b' = 1 ∧ flt P (a • x + b • y) = a' • flt P x + b' • flt P y := by
  have hw := hP.last_mul_pos hx hy
  have hX := hP.last_ne hx
  have hY := hP.last_ne hy
  set X := P *ᵥ liftPt x with hXdef
  set Y := P *ᵥ liftPt y with hYdef
  have hlift : liftPt (a • x + b • y) = a • liftPt x + b • liftPt y := by
    ext i; fin_cases i
    · simp [liftPt]
    · simp [liftPt]
    · simp [liftPt]; linarith
  have hmul : P *ᵥ liftPt (a • x + b • y) = a • X + b • Y := by
    rw [hlift, mulVec_add, mulVec_smul, mulVec_smul]
  have h1 := pos_aux ha hb hab hX hw
  have h2 : 0 < Y 2 * (b * Y 2 + a * X 2) := pos_aux hb ha (by linarith) hY (by linarith [mul_comm (X 2) (Y 2)])
  set d := a * X 2 + b * Y 2 with hd
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hdd : 0 < d ^ 2 := by positivity
  have ha' : 0 ≤ a * X 2 / d := by
    have : a * X 2 / d = a * (X 2 * d) / d ^ 2 := by field_simp
    rw [this]; exact div_nonneg (mul_nonneg ha h1.le) hdd.le
  have hb' : 0 ≤ b * Y 2 / d := by
    have : b * Y 2 / d = b * (Y 2 * d) / d ^ 2 := by field_simp
    rw [this]; exact div_nonneg (mul_nonneg hb (by nlinarith [h2])) hdd.le
  refine ⟨a * X 2 / d, b * Y 2 / d, ha', hb', ?_, ?_⟩
  · field_simp
    exact hd.symm
  · ext i; fin_cases i
    · simp only [Fin.zero_eta, flt_apply_zero, hmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hXdef, ← hYdef, ← hd]
      field_simp
    · simp only [Fin.mk_one, flt_apply_one, hmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hXdef, ← hYdef, ← hd]
      field_simp

theorem flt_flt_lorInv {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {z : Fin 2 → ℝ} (hz : z ∈ disc) :
    flt P (flt (lorInv P) z) = z := by
  rw [← hP.isLor_lorInv.flt_mul hz, hP.mul_lorInv, flt_one]

/-- Helper: a Lorentz map sends convex subsets of the disc to convex sets. -/
theorem convex_image_flt {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {S : Set (Fin 2 → ℝ)} (hS : S ⊆ disc)
    (hc : Convex ℝ S) : Convex ℝ (flt P '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  have hu := hP.flt_mem_disc (hS hx)
  have hv := hP.flt_mem_disc (hS hy)
  have hz : a • flt P x + b • flt P y ∈ disc := convex_disc hu hv ha hb hab
  obtain ⟨a', b', ha', hb', hab', he⟩ := flt_convex_comb hP.isLor_lorInv hu hv ha hb hab
  rw [hP.flt_lorInv (hS hx), hP.flt_lorInv (hS hy)] at he
  refine ⟨a' • x + b' • y, hc hx hy ha' hb' hab', ?_⟩
  rw [← he, flt_flt_lorInv hP hz]

/-- Helper: a Lorentz map takes the convex hull of a subset of the disc to the convex hull of the image. -/
theorem flt_image_convexHull {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {V : Set (Fin 2 → ℝ)}
    (hV : V ⊆ disc) : flt P '' convexHull ℝ V = convexHull ℝ (flt P '' V) := by
  have hVc : convexHull ℝ V ⊆ disc := convexHull_min hV convex_disc
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hCd : convexHull ℝ (flt P '' V) ⊆ disc :=
      convexHull_min (by rintro _ ⟨v, hv, rfl⟩; exact hP.flt_mem_disc (hV hv)) convex_disc
    have : convexHull ℝ V ⊆ flt (lorInv P) '' convexHull ℝ (flt P '' V) :=
      convexHull_min (fun v hv => ⟨flt P v, subset_convexHull ℝ _ ⟨v, hv, rfl⟩, hP.flt_lorInv (hV hv)⟩)
        (convex_image_flt hP.isLor_lorInv hCd (convex_convexHull ℝ _))
    obtain ⟨c, hc, hcx⟩ := this hx
    rw [← hcx, flt_flt_lorInv hP (hCd hc)]
    exact hc
  · exact convexHull_min (Set.image_mono (subset_convexHull ℝ V)) (convex_image_flt hP hVc (convex_convexHull ℝ V))

/-- **Theorem 6.1** (Cassels, Ch. 13, §6, p. 304; proved in §8, pp. 313–316): let $f$ be anisotropic. There is a
convex polygon $\mathcal P$ with vertices in $\mathcal D$ such that (i) every $\vec{\alpha} \in \mathcal D$ has
$T(\vec{\alpha}) \in \mathcal P$ for some $T \in O^+(f)$; (ii) if $\vec{\alpha}$ is in the interior of $\mathcal P$ and
$T(\vec{\alpha}) \in \mathcal P$, $T \in O^+(f)$, then $T = I$. -/
@[kb "cassels1978" "Ch. 13, §6, Thm. 6.1, p. 304; proof in §8, pp. 313–316"]
theorem exists_fundamental_polygon {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ V : Finset (Fin 2 → ℝ), (∀ v ∈ V, v ∈ disc) ∧
      (∀ α ∈ disc, ∃ T ∈ Siegel.AutPlus Q, actD L (castM T.val) α ∈ convexHull ℝ (V : Set (Fin 2 → ℝ))) ∧
      ∀ α ∈ interior (convexHull ℝ (V : Set (Fin 2 → ℝ))), ∀ T ∈ Siegel.AutPlus Q,
        actD L (castM T.val) α ∈ convexHull ℝ (V : Set (Fin 2 → ℝ)) → T = 1 := by
  classical
  obtain ⟨β, hβ, hgen⟩ := exists_generic_point hL hF
  obtain ⟨B, hB, hBe⟩ := exists_lorBoost hβ
  have hB0 : flt B 0 = β := flt_zero_boost hβ hBe
  have hBi := hB.isLor_lorInv
  set L' := lorInv B * L with hL'def
  have hL'det : IsUnit L'.det := by
    rw [hL'def, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_right_inverse hB.lorInv_mul).mul hL
  have hF' : realMat Q = L'ᵀ * lorentz * L' := by
    rw [hF, hL'def, Matrix.transpose_mul]
    calc Lᵀ * lorentz * L = Lᵀ * ((lorInv B)ᵀ * lorentz * lorInv B) * L := by
          rw [show (lorInv B)ᵀ * lorentz * lorInv B = lorentz from hBi]
      _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨V', hV'd, hDV'⟩ := dirichletDomain_eq_convexHull hQ hL'det hF'
  have hLi : L'⁻¹ = L⁻¹ * B := by
    apply Matrix.inv_eq_right_inv
    calc L' * (L⁻¹ * B) = lorInv B * (L * L⁻¹) * B := by rw [hL'def]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one, hB.lorInv_mul]
  have hrel : ∀ T ∈ Siegel.AutPlus Q, ∀ ξ ∈ disc,
      actD L' (castM T.val) ξ = flt (lorInv B) (actD L (castM T.val) (flt B ξ)) := by
    intro T hT ξ hξ
    have hP := isLor_conj_aut hL hF (aut_of_autPlus hT)
    unfold actD
    have : L' * castM T.val * L'⁻¹ = lorInv B * (L * castM T.val * L⁻¹) * B := by
      rw [hLi, hL'def]; simp only [Matrix.mul_assoc]
    rw [this, hB.flt_mul hξ]
    exact hP.flt_mul (hB.flt_mem_disc hξ)
  have hE0 : ∀ ξ ∈ disc, hypDist (flt (lorInv B) ξ) 0 = hypDist ξ β := by
    intro ξ hξ
    have := hB.hypDist_flt (hBi.flt_mem_disc hξ) zero_mem_disc
    rw [flt_flt_lorInv hB hξ, hB0] at this
    exact this.symm
  have hE1 : ∀ ξ ∈ disc, ∀ T ∈ Siegel.AutPlus Q,
      hypDist (flt (lorInv B) ξ) (actD L' (castM T.val) 0) = hypDist ξ (actD L (castM T.val) β) := by
    intro ξ hξ T hT
    rw [hrel T hT 0 zero_mem_disc, hB0]
    exact hBi.hypDist_flt hξ (actD_mem_disc hL hF hT hβ)
  have hV'sub : (V' : Set (Fin 2 → ℝ)) ⊆ disc := fun v hv => hV'd v hv
  have hPeq : convexHull ℝ ((V'.image (flt B) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) =
      flt B '' dirichletDomain Q L' := by
    rw [Finset.coe_image, ← flt_image_convexHull hB hV'sub, ← hDV']
  have hVd : ∀ v ∈ V'.image (flt B), v ∈ disc := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    exact hB.flt_mem_disc (hV'd u hu)
  have hPdisc : ∀ ξ ∈ convexHull ℝ ((V'.image (flt B) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)), ξ ∈ disc :=
    fun ξ hξ => convexHull_min (fun v hv => hVd v hv) convex_disc hξ
  have hPD : ∀ ξ ∈ disc, ξ ∈ convexHull ℝ ((V'.image (flt B) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) ↔
      ∀ T ∈ Siegel.AutPlus Q, hypDist ξ β ≤ hypDist ξ (actD L (castM T.val) β) := by
    intro ξ hξ
    rw [hPeq]
    have hmem : ξ ∈ flt B '' dirichletDomain Q L' ↔ flt (lorInv B) ξ ∈ dirichletDomain Q L' := by
      constructor
      · rintro ⟨ζ, hζ, rfl⟩
        rwa [hB.flt_lorInv hζ.1]
      · intro h
        exact ⟨_, h, flt_flt_lorInv hB hξ⟩
    rw [hmem]
    constructor
    · intro h T hT
      have := h.2 T hT
      rwa [hE0 ξ hξ, hE1 ξ hξ T hT] at this
    · intro h
      refine ⟨hBi.flt_mem_disc hξ, fun T hT => ?_⟩
      rw [hE0 ξ hξ, hE1 ξ hξ T hT]
      exact h T hT
  refine ⟨V'.image (flt B), hVd, ?_, ?_⟩
  · intro α hα
    obtain ⟨T₀, hT₀, hmin⟩ := exists_nearest_orbit hL'det hF' (hBi.flt_mem_disc hα)
    refine ⟨T₀⁻¹, inv_mem hT₀, ?_⟩
    have hξ : actD L (castM (T₀⁻¹).val) α ∈ disc := actD_mem_disc hL hF (inv_mem hT₀) hα
    rw [hPD _ hξ]
    intro T hT
    have hmin' : hypDist α (actD L (castM T₀.val) β) ≤ hypDist α (actD L (castM (T₀ * T).val) β) := by
      have := hmin (T₀ * T) (mul_mem hT₀ hT)
      rwa [hE1 α hα T₀ hT₀, hE1 α hα (T₀ * T) (mul_mem hT₀ hT)] at this
    have e1 : hypDist (actD L (castM (T₀⁻¹).val) α) β = hypDist α (actD L (castM T₀.val) β) := by
      have := hypDist_actD hL hF hT₀ hξ hβ
      rw [actD_actD_inv hL hF hT₀ hα] at this
      exact this.symm
    have e2 : hypDist (actD L (castM (T₀⁻¹).val) α) (actD L (castM T.val) β) =
        hypDist α (actD L (castM (T₀ * T).val) β) := by
      have := hypDist_actD hL hF hT₀ hξ (actD_mem_disc hL hF hT hβ)
      rw [actD_actD_inv hL hF hT₀ hα, ← actD_mul hL hF hT₀ hT hβ] at this
      exact this.symm
    rw [e1, e2]
    exact hmin'
  · intro α hα T hT hTα
    by_contra hT1
    have hαP := interior_subset hα
    have hαd := hPdisc α hαP
    have hne : actD L (castM T.val) β ≠ β := fun h => hT1 (hgen T hT h)
    obtain ⟨γ, hγ⟩ : ∃ γ, γ = actD L (castM (T⁻¹).val) β := ⟨_, rfl⟩
    have hγd : γ ∈ disc := hγ ▸ actD_mem_disc hL hF (inv_mem hT) hβ
    have hβγ : β ≠ γ := by
      intro h
      apply hne
      have h2 : actD L (castM T.val) γ = β := by rw [hγ]; exact actD_actD_inv hL hF hT hβ
      rwa [← h] at h2
    obtain ⟨a, c, ha, heq, hle⟩ := exists_bisector hβ hγd hβγ
    have hsub : convexHull ℝ ((V'.image (flt B) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) ⊆
        {ζ | a ⬝ᵥ ζ ≤ c} := fun ζ hζ => by
      have hζd := hPdisc ζ hζ
      apply (hle ζ hζd).1
      rw [hγ]
      exact (hPD ζ hζd).1 hζ _ (inv_mem hT)
    have hlt : a ⬝ᵥ α < c := by
      have hmem : {ζ | a ⬝ᵥ ζ ≤ c} ∈ nhds α := mem_interior_iff_mem_nhds.1 (interior_mono hsub hα)
      have hle' : a ⬝ᵥ α ≤ c := hsub hαP
      by_contra hnl
      have heqc : a ⬝ᵥ α = c := le_antisymm hle' (not_lt.1 hnl)
      have hc : Continuous (fun t : ℝ => α + t • a) := by fun_prop
      have ht : Filter.Tendsto (fun t : ℝ => α + t • a) (nhds 0) (nhds α) := by simpa using hc.tendsto 0
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (ht hmem)
      have hm : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
      have h1 : a ⬝ᵥ (α + (ε / 2) • a) ≤ c := hball hm
      rw [dotProduct_add, dotProduct_smul, heqc, smul_eq_mul] at h1
      have hpos : 0 < a ⬝ᵥ a := by
        have h0 : 0 ≤ a ⬝ᵥ a := by
          simp only [dotProduct, Fin.sum_univ_two]; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
        rcases h0.lt_or_eq with h | h
        · exact h
        · exact absurd (dotProduct_self_eq_zero.1 h.symm) ha
      nlinarith [mul_pos (by positivity : (0 : ℝ) < ε / 2) hpos]
    have hd1 : hypDist α β < hypDist α γ :=
      lt_of_le_of_ne ((hle α hαd).2 hlt.le) (fun h => absurd ((heq α hαd).1 h) hlt.ne)
    have hd2 : hypDist α γ = hypDist (actD L (castM T.val) α) β := by
      rw [hγ]
      have := hypDist_actD hL hF hT hαd (actD_mem_disc hL hF (inv_mem hT) hβ)
      rw [actD_actD_inv hL hF hT hβ] at this
      exact this.symm
    have hd3 : hypDist (actD L (castM T.val) α) β ≤ hypDist α β := by
      have := (hPD _ (actD_mem_disc hL hF hT hαd)).1 hTα T hT
      rwa [hypDist_actD hL hF hT hαd hβ] at this
    linarith

/-- **Theorem 8.1** (Cassels, Ch. 13, §8, p. 316): let $f$ be anisotropic, let $\mathcal U$ be any open set containing
$\mathcal D_0$, and let $\Xi$ be the set of $T \in O^+(f)$ such that $T(\mathcal D_0)$ meets $\mathcal U$. Then $O^+(f)$ is
generated by $\Xi$ and the stabilizer of $0$. -/
@[kb "cassels1978" "Ch. 13, §8, Thm. 8.1, (8.10)–(8.13), p. 316"]
theorem autPlus_eq_closure {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (hDU : dirichletDomain Q L ⊆ U) :
    Subgroup.closure ({T | T ∈ Siegel.AutPlus Q ∧ (actD L (castM T.val) '' dirichletDomain Q L ∩ U).Nonempty} ∪
      {T | T ∈ Siegel.AutPlus Q ∧ actD L (castM T.val) 0 = 0}) = Siegel.AutPlus Q := by
  classical
  obtain ⟨V, hVd, hD⟩ := dirichletDomain_eq_convexHull hQ hL hF
  have hcomp : IsCompact (dirichletDomain Q L) := by
    rw [hD]; exact V.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨δ, hδ, hthick⟩ := hcomp.exists_thickening_subset_open hU hDU
  obtain ⟨-, hcover, -, -⟩ := dirichletDomain_spec hL hF
  set Γ := Subgroup.closure ({T | T ∈ Siegel.AutPlus Q ∧
      (actD L (castM T.val) '' dirichletDomain Q L ∩ U).Nonempty} ∪
      {T | T ∈ Siegel.AutPlus Q ∧ actD L (castM T.val) 0 = 0}) with hΓ
  have hΓle : Γ ≤ Siegel.AutPlus Q :=
    Subgroup.closure_le _ |>.2 (Set.union_subset (fun T hT => hT.1) (fun T hT => hT.1))
  have hD0 : (0 : Fin 2 → ℝ) ∈ dirichletDomain Q L := by
    refine ⟨zero_mem_disc, fun T hT => ?_⟩
    rw [(hd_eq_zero zero_mem_disc zero_mem_disc).2 rfl]
    exact hd_nonneg zero_mem_disc (actD_mem_disc hL hF hT zero_mem_disc)
  -- Step 1: points of `U`
  have key1 : ∀ ζ ∈ dirichletDomain Q L, ∀ x ∈ disc, coshDist ζ x < 1 + δ ^ 2 / 4 → x ∈ U := by
    intro ζ hζ x hx hc
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨ζ, hζ, ?_⟩
    have h := sq_dist_le_coshDist hζ.1 hx
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [Real.dist_eq]
    apply abs_lt_of_sq_lt_sq _ hδ.le
    have h2 : 0 < δ ^ 2 := by positivity
    fin_cases i
    · simp only [Fin.zero_eta]
      nlinarith [sq_nonneg (x 1 - ζ 1)]
    · simp only [Fin.mk_one]
      nlinarith [sq_nonneg (x 0 - ζ 0)]
  -- Step 2: one step of the chain
  have step : ∀ S ∈ Γ, ∀ p p' z, z ∈ dirichletDomain Q L → p = actD L (castM S.val) z → p' ∈ disc →
      coshDist p p' < 1 + δ ^ 2 / 4 → ∃ S' ∈ Γ, p' ∈ actD L (castM S'.val) '' dirichletDomain Q L := by
    intro S hS p p' z hz hp hp' hc
    have hSA := hΓle hS
    have hzd : z ∈ disc := hz.1
    have hpd : p ∈ disc := hp ▸ actD_mem_disc hL hF hSA hzd
    obtain ⟨S', hS'A, z', hz', hp'e⟩ : ∃ S' ∈ Siegel.AutPlus Q, p' ∈ actD L (castM S'.val) '' dirichletDomain Q L := by
      have := hcover ▸ hp'
      simpa using this
    obtain ⟨z', hz', rfl⟩ := hp'e
    have hxi : S⁻¹ * S' ∈ Γ := by
      apply Subgroup.subset_closure
      left
      refine ⟨mul_mem (inv_mem hSA) hS'A, actD L (castM (S⁻¹ * S').val) z', ⟨z', hz', rfl⟩, ?_⟩
      have e1 : actD L (castM (S⁻¹ * S').val) z' = actD L (castM (S⁻¹).val) (actD L (castM S'.val) z') :=
        actD_mul hL hF (inv_mem hSA) hS'A hz'.1
      have e2 : z = actD L (castM (S⁻¹).val) p := by rw [hp, actD_inv_actD hL hF hSA hzd]
      rw [e1]
      apply key1 z hz _ (actD_mem_disc hL hF (inv_mem hSA) hp')
      rw [e2, coshDist_actD hL hF (inv_mem hSA) hpd hp']
      exact hc
    refine ⟨S', ?_, z', hz', rfl⟩
    have := mul_mem hS hxi
    rwa [mul_inv_cancel_left] at this
  -- Step 3: the chain along the segment from `0` to `T(0)`
  refine le_antisymm hΓle fun T hT => ?_
  set w := actD L (castM T.val) 0 with hw
  have hwd : w ∈ disc := actD_mem_disc hL hF hT zero_mem_disc
  have hw' : w 0 ^ 2 + w 1 ^ 2 < 1 := hwd
  have hκ : 0 < 1 - w 0 ^ 2 - w 1 ^ 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ((1 - w 0 ^ 2 - w 1 ^ 2) ^ 2 * δ ^ 2))
  set k : ℕ := N + 1 with hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by simp [hk]
  have hkN : 2 / ((1 - w 0 ^ 2 - w 1 ^ 2) ^ 2 * δ ^ 2) < k := by
    rw [hk]; push_cast; linarith
  have hsmall : 1 / (2 * (1 - w 0 ^ 2 - w 1 ^ 2) ^ 2 * (k : ℝ) ^ 2) < δ ^ 2 / 4 := by
    have h3 : 0 < (1 - w 0 ^ 2 - w 1 ^ 2) ^ 2 * δ ^ 2 := by positivity
    rw [div_lt_iff₀ h3] at hkN
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hk1 hkpos.le]
  have chain : ∀ i : ℕ, i ≤ k → ∃ S ∈ Γ, ((i : ℝ) / k) • w ∈ actD L (castM S.val) '' dirichletDomain Q L := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, one_mem _, 0, hD0, ?_⟩
      rw [actD_one hL]; simp
    | succ i ih =>
      intro hi
      obtain ⟨S, hS, z, hz, hzp⟩ := ih (by omega)
      have hi0 : (0 : ℝ) ≤ i / k := by positivity
      have hi1 : (i : ℝ) / k ≤ 1 := by
        rw [div_le_one hkpos]; exact_mod_cast (by omega : i ≤ k)
      have hj0 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) / k := by positivity
      have hj1 : ((i + 1 : ℕ) : ℝ) / k ≤ 1 := by
        rw [div_le_one hkpos]; exact_mod_cast hi
      apply step S hS _ _ z hz hzp.symm (smul_mem_disc hwd hj0 hj1)
      refine lt_of_le_of_lt (coshDist_smul_le hwd hi0 hi1 hj0 hj1) ?_
      have e : ((i + 1 : ℕ) : ℝ) / k - (i : ℝ) / k = 1 / k := by push_cast; field_simp; ring
      rw [e]
      refine lt_of_le_of_lt (le_of_eq ?_) (by linarith [hsmall] : 1 + 1 / (2 * (1 - w 0 ^ 2 - w 1 ^ 2) ^ 2 * (k : ℝ) ^ 2) < 1 + δ ^ 2 / 4)
      congr 1
      field_simp
  obtain ⟨S, hS, z, hz, hzp⟩ := chain k le_rfl
  rw [div_self hkpos.ne', one_smul] at hzp
  have hSA := hΓle hS
  have hxi : S⁻¹ * T ∈ Γ := by
    apply Subgroup.subset_closure
    left
    refine ⟨mul_mem (inv_mem hSA) hT, z, ⟨0, hD0, ?_⟩, hDU hz⟩
    rw [actD_mul hL hF (inv_mem hSA) hT zero_mem_disc, ← hw, ← hzp, actD_inv_actD hL hF hSA hz.1]
  have := mul_mem hS hxi
  rwa [mul_inv_cancel_left] at this

end QuadFormsKB.Reduction
