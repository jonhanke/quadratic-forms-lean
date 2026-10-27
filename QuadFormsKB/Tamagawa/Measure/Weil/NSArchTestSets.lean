/-
# The local test sets near $1$ in the norm-one spheres

**Layer:** $A, B\in\mathbb R$ (resp. $\mathbb C$) nonzero; $S_1 = \{x : \operatorname{nrd}x = 1\}$ in $\mathbb H[\mathbb R,A,B]$ (resp. $\mathbb H[\mathbb C,A,B]$) with
its Haar measure $\sigma$ (`sig`, `sigC`).

* **`posR A B`** $= \{x\in S_1(\mathbb R) : x_0>0,\ \|x\|<2\}$ and **`posC A B`** $= \{x\in S_1(\mathbb C) : \operatorname{Re}x_0>0,\ \|x\|<2\}$:
  open, containing $1$, of positive finite measure, and disjoint from their negatives.
* **`injOn_phiSplit_posR`**, **`injOn_phiNS_posC`**, **`injOn_phiSplitC_posC`**: the three local maps $\varphi_w$ (kernel $\pm1$) are
  injective on these sets.

Source: Weil 1982, §2.3, Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSRatio
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSplitC

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray SphereLerayC

theorem eq_one_or_neg_one_of_sq {K : Type*} [Field K] {r : K} (hr : r ^ 2 = 1) : r = 1 ∨ r = -1 := by
  have h : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 h with h | h
  · left; linear_combination h
  · right; linear_combination h

/-! ### Real spheres -/

section Real

variable {A B : ℝ}

/-- **The real test set** $\{x\in S_1 : x_0>0,\ \|x\|<2\}$. -/
def posR (A B : ℝ) : Set (Sph (normForm A B) 1) := {x | 0 < (x : Fin 4 → ℝ) 0 ∧ ‖(x : Fin 4 → ℝ)‖ < 2}

theorem isOpen_posR : IsOpen (posR A B) :=
  (isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val)).inter
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)

theorem measurableSet_posR : MeasurableSet (posR A B) := isOpen_posR.measurableSet

theorem one_mem_posR : (1 : Sph (normForm A B) 1) ∈ posR A B := by
  have e : ((1 : Sph (normForm A B) 1) : Fin 4 → ℝ) = Pi.single 0 1 := by
    rw [sph_one_val]; funext i; fin_cases i <;> rfl
  refine ⟨by rw [e]; simp, ?_⟩
  rw [e, Pi.norm_single, norm_one]; norm_num

theorem sig_posR_pos : 0 < sig (normForm A B) 1 (posR A B) :=
  isOpen_posR.measure_pos _ ⟨1, one_mem_posR⟩

theorem sig_posR_ne_top : sig (normForm A B) 1 (posR A B) ≠ ∞ :=
  ((measure_mono fun x (hx : x ∈ posR A B) => (show ‖(x : Fin 4 → ℝ)‖ ≤ 2 from hx.2.le)).trans_lt
    (isCompact_normLe (A := A) (B := B) 2).measure_lt_top).ne

theorem eq_of_smul_posR {x x' : Sph (normForm A B) 1} {r : ℝ} (hr : r ^ 2 = 1)
    (h : (x' : Fin 4 → ℝ) = r • (x : Fin 4 → ℝ)) (hx : 0 < (x : Fin 4 → ℝ) 0) (hx' : 0 < (x' : Fin 4 → ℝ) 0) :
    r = 1 := by
  rcases eq_one_or_neg_one_of_sq hr with h1 | h1
  · exact h1
  · exfalso
    have := congrFun h 0
    rw [h1, Pi.smul_apply, smul_eq_mul] at this
    linarith

theorem injOn_phiSplit_posR {d t : ℝ} (ht0 : t ≠ 0) (ht : t ^ 2 = d) (hA : A ≠ 0) :
    InjOn (phiSplit (A := A) (B := B) ht0 ht) (posR A B ×ˢ posR A B) := by
  intro p hp p' hp' h
  obtain ⟨r, hr, h1, h2⟩ := eq_smul_of_phiSplit_eq ht0 ht hA h
  have hr1 := eq_of_smul_posR hr h1 hp.1.1 hp'.1.1
  rw [hr1, one_smul] at h1 h2
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)

end Real

/-! ### Complex spheres -/

section Complex

variable {A B : ℂ}

/-- **The complex test set** $\{x\in S_1 : \operatorname{Re}x_0>0,\ \|x\|<2\}$. -/
def posC (A B : ℂ) : Set (SphC (normForm A B) 1) :=
  {x | 0 < ((x : Fin 4 → ℂ) 0).re ∧ ‖(x : Fin 4 → ℂ)‖ < 2}

theorem isOpen_posC : IsOpen (posC A B) :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp ((continuous_apply 0).comp continuous_subtype_val))).inter
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)

theorem measurableSet_posC : MeasurableSet (posC A B) := isOpen_posC.measurableSet

theorem one_mem_posC : (1 : SphC (normForm A B) 1) ∈ posC A B := by
  have e : ((1 : SphC (normForm A B) 1) : Fin 4 → ℂ) = Pi.single 0 1 := by
    rw [sphC_one_val]; funext i; fin_cases i <;> rfl
  refine ⟨by rw [e]; simp, ?_⟩
  rw [e, Pi.norm_single, norm_one]; norm_num

theorem sigC_posC_pos : 0 < sigC (normForm A B) 1 (posC A B) :=
  isOpen_posC.measure_pos _ ⟨1, one_mem_posC⟩

theorem sigC_posC_ne_top : sigC (normForm A B) 1 (posC A B) ≠ ∞ :=
  ((measure_mono fun x (hx : x ∈ posC A B) => (show ‖(x : Fin 4 → ℂ)‖ ≤ 2 from hx.2.le)).trans_lt
    (isCompact_normLeC (A := A) (B := B) 2).measure_lt_top).ne

theorem eq_of_smul_posC {x x' : SphC (normForm A B) 1} {r : ℂ} (hr : r ^ 2 = 1)
    (h : (x' : Fin 4 → ℂ) = r • (x : Fin 4 → ℂ)) (hx : 0 < ((x : Fin 4 → ℂ) 0).re)
    (hx' : 0 < ((x' : Fin 4 → ℂ) 0).re) : r = 1 := by
  rcases eq_one_or_neg_one_of_sq hr with h1 | h1
  · exact h1
  · exfalso
    have := congrArg Complex.re (congrFun h 0)
    rw [h1, Pi.smul_apply, smul_eq_mul, neg_one_mul, Complex.neg_re] at this
    linarith

theorem injOn_phiSplitC_posC {d t : ℂ} (ht0 : t ≠ 0) (ht : t ^ 2 = d) (hA : A ≠ 0) :
    InjOn (phiSplitC (A := A) (B := B) ht0 ht) (posC A B ×ˢ posC A B) := by
  intro p hp p' hp' h
  obtain ⟨r, hr, h1, h2⟩ := eq_smul_of_phiSplitC_eq ht0 ht hA h
  have hr1 := eq_of_smul_posC hr h1 hp.1.1 hp'.1.1
  rw [hr1, one_smul] at h1 h2
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)

end Complex

theorem injOn_phiNS_posC {A B d : ℝ} {t : ℂ} (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0) (hA : A ≠ 0) :
    InjOn (phiNS (A := A) (B := B) ht htre ht0) (posC (A : ℂ) (B : ℂ)) := by
  intro x hx x' hx' h
  obtain ⟨r, hr, h1⟩ := eq_smul_of_phiNS_eq ht htre ht0 hA h
  have hr1 := eq_of_smul_posC hr h1 hx.1 hx'.1
  rw [hr1, one_smul] at h1
  exact Subtype.ext h1.symm

/-! ### Positivity of the reduced norm on the image of the local maps -/

section Scalar

variable {K : Type*} [Field K] {A B : K}

theorem qVec_smul' (c : K) (x : ℍ[K,A,B]) : qVec (c • x) = c • qVec x := by
  funext i; fin_cases i <;> simp [qVec]

theorem qVec_inj {x y : ℍ[K,A,B]} (h : qVec x = qVec y) : x = y := by
  rw [← vecQ_qVec x, h, vecQ_qVec]

/-- A quaternion commuting with $i$ and $j$ is a scalar. -/
theorem eq_coe_re_of_comm (hA : A ≠ 0) (h2 : (2 : K) ≠ 0) {q : ℍ[K,A,B]}
    (hi : q * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * q) (hj : q * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * q) :
    q = (q.re : ℍ[K,A,B]) := by
  have i2 := congrArg QuaternionAlgebra.imJ hi
  have i3 := congrArg QuaternionAlgebra.imK hi
  have j3 := congrArg QuaternionAlgebra.imK hj
  simp at i2 i3 j3
  have hK : q.imK = 0 := by
    have : 2 * (A * q.imK) = 0 := by linear_combination -i2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact (mul_eq_zero.1 h).resolve_left hA
  have hJ : q.imJ = 0 := by
    have : 2 * q.imJ = 0 := by linear_combination -i3
    exact (mul_eq_zero.1 this).resolve_left h2
  have hI : q.imI = 0 := by
    have : 2 * q.imI = 0 := by linear_combination j3
    exact (mul_eq_zero.1 this).resolve_left h2
  ext <;> simp [hI, hJ, hK]


/-- **If $v\mapsto q_1vq_2$ is the scalar $u\neq0$, then $q_1$ is a scalar and $q_1q_2 = u$.** -/
theorem scalar_of_sqMat_eq_smul (hA : A ≠ 0) (h2 : (2 : K) ≠ 0) {q₁ q₂ : ℍ[K,A,B]} {u : K}
    (hu : u ≠ 0) (h : sqMat q₁ q₂ = u • 1) : q₁ = (q₁.re : ℍ[K,A,B]) ∧ q₁ * q₂ = (u : ℍ[K,A,B]) := by
  have hv : ∀ w : ℍ[K,A,B], q₁ * w * q₂ = u • w := fun w => by
    have := congrArg (· *ᵥ qVec w) h
    simp only [sqMat_mulVec, vecQ_qVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    rw [← qVec_smul'] at this
    exact qVec_inj this
  have h1 : q₁ * q₂ = (u : ℍ[K,A,B]) := by
    have := hv 1
    rw [mul_one] at this
    rw [this]; ext <;> simp
  have hc : ∀ w : ℍ[K,A,B], q₁ * w = w * q₁ := fun w => by
    have e1 := hv (w * q₁)
    have e2 : q₁ * (w * q₁) * q₂ = u • (q₁ * w) := by
      rw [show q₁ * (w * q₁) * q₂ = q₁ * w * (q₁ * q₂) by simp only [mul_assoc], h1,
        QuaternionAlgebra.mul_coe_eq_smul]
    rw [e1] at e2
    exact (smul_right_injective _ hu e2).symm
  exact ⟨eq_coe_re_of_comm hA h2 (hc _) (hc _), h1⟩

/-- **Real split places**: if $\mathrm{sq}(X_1,\bar X_2) = u\,\mathrm{sq}(p_1,\bar p_2)$ with $\operatorname{nrd}X_1 = u\neq0$ and
$\operatorname{nrd}p_i = 1$, then $u>0$. -/
theorem pos_of_sqMat_eq_smul {A B : ℝ} (hA : A ≠ 0) {X₁ X₂ p₁ p₂ : ℍ[ℝ,A,B]} {u : ℝ} (hu : u ≠ 0)
    (hX : nrd X₁ = u) (hp₁ : nrd p₁ = 1) (hp₂ : nrd p₂ = 1)
    (h : sqMat X₁ (star X₂) = u • sqMat p₁ (star p₂)) : 0 < u := by
  have e : sqMat (star p₁ * X₁) (star X₂ * p₂) = u • 1 := by
    rw [← sqMat_mul, h, Matrix.mul_smul, sqMat_mul, star_mul_eq_nrd, star_mul_eq_nrd, hp₁, hp₂,
      QuaternionAlgebra.coe_one, sqMat_one_one]
  obtain ⟨hr, -⟩ := scalar_of_sqMat_eq_smul hA two_ne_zero hu e
  have hn := congrArg nrd hr
  rw [nrd_coe, nrd_mul, nrd_star, hp₁, one_mul, hX] at hn
  rw [hn]
  exact lt_of_le_of_ne (sq_nonneg _) (fun h0 => hu (by rw [hn, ← h0]))

/-- **Real places with $E_w = \mathbb C$**: if $M_R(X) = u\,M_R(y)$ with $u\neq0$ real and $\operatorname{nrd}y = 1$, then
$u>0$. -/
theorem pos_of_MR_eq_smul {A B : ℝ} (hA : A ≠ 0) {t : ℂ} (htre : t.re = 0) (ht0 : t ≠ 0)
    {X y : ℍ[ℂ, (A : ℂ), (B : ℂ)]} {u : ℝ} (hu : u ≠ 0) (hy : nrd y = 1)
    (h : MR t X = u • MR t y) : 0 < u := by
  set Z := star y * X
  have e1 : MR t Z = u • 1 := by
    rw [MR_mul htre ht0, h, Matrix.mul_smul, ← MR_mul htre ht0, star_mul_eq_nrd, hy, QuaternionAlgebra.coe_one,
      MR_one htre ht0]
  have e2 : MC t Z = (u : ℂ) • 1 := by
    rw [MC_eq_map htre ht0, e1]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have e3 : sqMat Z (conjQ (star Z)) = (u : ℂ) • 1 := by
    have := congrArg (fun M => tMatN t * M * tInvN t) e2
    simp only [MC] at this
    rw [show tMatN t * (tInvN t * sqMat Z (conjQ (star Z)) * tMatN t) * tInvN t =
        (tMatN t * tInvN t) * sqMat Z (conjQ (star Z)) * (tMatN t * tInvN t) by simp only [Matrix.mul_assoc],
      tMatN_mul_tInvC ht0, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, tMatN_mul_tInvC ht0] at this
    exact this
  have hA' : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  obtain ⟨hr, hprod⟩ := scalar_of_sqMat_eq_smul hA' two_ne_zero (Complex.ofReal_ne_zero.2 hu) e3
  rw [hr] at hprod
  have hc : conjQ (star ((Z.re : ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)])) = ((starRingEnd ℂ Z.re : ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) := by
    ext <;> simp
  rw [hc, ← QuaternionAlgebra.coe_mul] at hprod
  have hre := congrArg (fun q : ℍ[ℂ, (A : ℂ), (B : ℂ)] => q.re) hprod
  simp only [QuaternionAlgebra.re_coe] at hre
  rw [Complex.mul_conj] at hre
  have hpos : (0 : ℝ) ≤ Complex.normSq Z.re := Complex.normSq_nonneg _
  have : (Complex.normSq Z.re : ℝ) = u := by exact_mod_cast hre
  rw [← this]
  exact lt_of_le_of_ne hpos (fun h0 => hu (by rw [← this, ← h0]))

end Scalar

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
