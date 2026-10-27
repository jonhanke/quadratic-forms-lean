import QuadFormsKB.Tamagawa.Measure.Weil.NSArchNSMap
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSL1C
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchGraphR

/-!
# The map $\varphi_w$ at a real place with $E_w = \mathbb C$ as a homomorphism

**Layer:** as `NSArchNSMap`: $A, B, d$ real, $t\in\mathbb C$ with $t^2 = d$, $\operatorname{Re}t = 0$, $t\ne0$;
$L_w = S_1(\mathbb C) = \{x\in\mathbb C^4 : N(x) = 1\}$ (`SphC (normForm A B) 1`, the group $\mathrm{SL}_1(D\otimes\mathbb C)$).

* **`phiNS`**: $L_w\to SO(Q_0)(\mathbb R)$, $x\mapsto$ `MR t x`; continuous (`continuous_phiNS`); kernel $\pm1$
  (`eq_smul_of_phiNS_eq`), hence locally injective (`isLocInj_phiNS`).
* **`realS`**: $S_1(\mathbb R)\to S_1(\mathbb C)$; `phiNS_realS`: $\varphi(h) = \mathrm{diag}(1,c_h)$.
* **`sNS`**: the Cayley point $X(y)$ for $y\in S_1(Q_0)$ with $y_0 > -1$; `phiNS_sNS_e0`: $\varphi(X(y))e_0 = y$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix Complex
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Siegel QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  SphereLeray SphereLerayC QuadFormsKB.Tamagawa.Measure.Leray QuadFormsKB.Tamagawa.Measure.OrbitalReal

variable {A B d : ℝ} {t : ℂ} (ht : t ^ 2 = (d : ℂ)) (htre : t.re = 0) (ht0 : t ≠ 0)

local notation "LC" => SphC (normForm (A : ℂ) (B : ℂ)) 1

theorem vecQ_mul_sphC (x y : LC) :
    (vecQ ((x * y : LC) : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = vecQ (x : Fin 4 → ℂ) * vecQ (y : Fin 4 → ℂ) := by
  rw [sphC_mul_val, vecQ_qVec]

theorem vecQ_one_sphC : (vecQ ((1 : LC) : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = 1 := by
  rw [sphC_one_val, vecQ_qVec]

include ht htre ht0 in
theorem phiNS_mem (x : LC) :
    (⟨MR t (vecQ (x : Fin 4 → ℂ)), MR t (star (vecQ (x : Fin 4 → ℂ))), by
      rw [← MR_mul htre ht0, mul_star_eq_nrd, nrd_sphC]; simpa using MR_one (A := A) (B := B) htre ht0, by
      rw [← MR_mul htre ht0, star_mul_eq_nrd, nrd_sphC]; simpa using MR_one (A := A) (B := B) htre ht0⟩ :
      GL (Fin 4) ℝ) ∈ soReal (nsFormR A B d) := by
  rw [mem_soReal_iff]
  exact ⟨MR_isometry ht htre ht0 (nrd_sphC x), det_MR htre ht0 (nrd_sphC x)⟩

/-- **The map $\varphi_w$ at a real place with $E_w = \mathbb C$.** -/
def phiNS : LC →* ArchSO (nsFormR A B d) where
  toFun x := ⟨_, phiNS_mem ht htre ht0 x⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show MR t (vecQ ((1 : LC) : Fin 4 → ℂ)) = 1
    rw [vecQ_one_sphC, MR_one htre ht0]
  map_mul' x y := by
    apply Subtype.ext; apply Units.ext
    show MR t (vecQ ((x * y : LC) : Fin 4 → ℂ)) = MR t (vecQ (x : Fin 4 → ℂ)) * MR t (vecQ (y : Fin 4 → ℂ))
    rw [vecQ_mul_sphC, MR_mul htre ht0]

theorem mat_phiNS (x : LC) : ArchSOInst.mat _ (phiNS ht htre ht0 x) = MR (A := A) (B := B) t (vecQ (x : Fin 4 → ℂ)) := rfl

/-! ### Continuity -/

theorem lmat_eqC (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : lmat x = !![x.re, (A : ℂ) * x.imI, (B : ℂ) * x.imJ,
    -((A : ℂ) * B) * x.imK; x.imI, x.re, (B : ℂ) * x.imK, -(B : ℂ) * x.imJ; x.imJ, -(A : ℂ) * x.imK, x.re,
    (A : ℂ) * x.imI; x.imK, -x.imJ, x.imI, x.re] := lmat_eq x

theorem rmat_eqC (x : ℍ[ℂ, (A : ℂ), (B : ℂ)]) : rmat x = !![x.re, (A : ℂ) * x.imI, (B : ℂ) * x.imJ,
    -((A : ℂ) * B) * x.imK; x.imI, x.re, -(B : ℂ) * x.imK, (B : ℂ) * x.imJ; x.imJ, (A : ℂ) * x.imK, x.re,
    -(A : ℂ) * x.imI; x.imK, x.imJ, -x.imI, x.re] := rmat_eq x

theorem continuous_lmat_vecN : Continuous fun v : Fin 4 → ℂ => lmat (vecQ v : ℍ[ℂ, (A : ℂ), (B : ℂ)]) := by
  have e : (fun v : Fin 4 → ℂ => lmat (vecQ v : ℍ[ℂ, (A : ℂ), (B : ℂ)])) = fun v => !![v 0, (A : ℂ) * v 1,
      (B : ℂ) * v 2, -((A : ℂ) * B) * v 3; v 1, v 0, (B : ℂ) * v 3, -(B : ℂ) * v 2; v 2, -(A : ℂ) * v 3, v 0,
      (A : ℂ) * v 1; v 3, -v 2, v 1, v 0] := by
    funext v; rw [lmat_eqC]; rfl
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_rmat_c_vecC :
    Continuous fun v : Fin 4 → ℂ => rmat (conjQ (star (vecQ v : ℍ[ℂ, (A : ℂ), (B : ℂ)]))) := by
  have e : (fun v : Fin 4 → ℂ => rmat (conjQ (star (vecQ v : ℍ[ℂ, (A : ℂ), (B : ℂ)])))) = fun v =>
      !![conj (v 0), (A : ℂ) * -conj (v 1), (B : ℂ) * -conj (v 2), -((A : ℂ) * B) * -conj (v 3);
        -conj (v 1), conj (v 0), -(B : ℂ) * -conj (v 3), (B : ℂ) * -conj (v 2);
        -conj (v 2), (A : ℂ) * -conj (v 3), conj (v 0), -(A : ℂ) * -conj (v 1);
        -conj (v 3), -conj (v 2), - -conj (v 1), conj (v 0)] := by
    funext v; rw [rmat_eqC]; simp [vecQ]
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_MC_vec : Continuous fun v : Fin 4 → ℂ => MC (A := A) (B := B) t (vecQ v) := by
  have h : Continuous fun v : Fin 4 → ℂ =>
      sqMat (vecQ v : ℍ[ℂ, (A : ℂ), (B : ℂ)]) (conjQ (star (vecQ v))) := by
    simp only [sqMat_isometry_gen.sqMat_eq_lmat_mul_rmat_gen]
    exact continuous_lmat_vecN.matrix_mul continuous_rmat_c_vecC
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

theorem continuous_MR_vec : Continuous fun v : Fin 4 → ℂ => MR (A := A) (B := B) t (vecQ v) :=
  continuous_MC_vec.matrix_map Complex.continuous_re

theorem continuous_phiNS : Continuous (phiNS (A := A) (B := B) ht htre ht0) := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · exact continuous_MR_vec.comp continuous_subtype_val
  · have e : ∀ x : LC, (((ArchSO.incl _ (phiNS ht htre ht0 x) : GL (Fin 4) ℝ))⁻¹ : GL (Fin 4) ℝ).val =
        MR (A := A) (B := B) t (vecQ ((x⁻¹ : LC) : Fin 4 → ℂ)) := fun x => by
      rw [← map_inv (ArchSO.incl _), ← map_inv (phiNS ht htre ht0)]; exact mat_phiNS ht htre ht0 _
    exact (continuous_congr e).2 (continuous_MR_vec.comp (continuous_subtype_val.comp continuous_inv))

/-! ### The kernel -/

theorem eq_scalar_of_conj_trivial_gen {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {A' B' : K} (hA : A' ≠ 0)
    {a : ℍ[K,A',B']} (ha : nrd a = 1)
    (h : ∀ y : Fin 3 → K, a * Quat.pure y * star a = Quat.pure y) : ∃ r : K, r ^ 2 = 1 ∧ a = (r : ℍ[K,A',B']) := by
  have hc : conjSO (unitOfNrdOne a ha) = 1 := by
    apply Subtype.ext
    show conjGL (unitOfNrdOne a ha) = 1
    apply Units.ext
    change LinearMap.toMatrix' (conjLin (unitOfNrdOne a ha)) = 1
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    show imv (a * Quat.pure y * star a) = y
    rw [h, imv_pure]
  have hm : unitOfNrdOne a ha ∈ centerUnits A' B' := by
    rw [← ker_conjSO h2 hA, MonoidHom.mem_ker]; exact hc
  obtain ⟨r, hr⟩ := mem_centerUnits.1 hm
  refine ⟨r, ?_, hr⟩
  have := congrArg nrd hr
  rw [nrd_coe] at this
  exact this.symm.trans ha

include htre ht0 in
theorem sqMat_eq_of_MR_eq {X Y : ℍ[ℂ, (A : ℂ), (B : ℂ)]} (h : MR t X = MR t Y) :
    sqMat X (conjQ (star X)) = sqMat Y (conjQ (star Y)) := by
  have hC : MC t X = MC t Y := by rw [MC_eq_map htre ht0, MC_eq_map htre ht0, h]
  have e : ∀ Z : ℍ[ℂ, (A : ℂ), (B : ℂ)], sqMat Z (conjQ (star Z)) = tMatN t * MC t Z * tInvN t := fun Z => by
    rw [MC]; simp only [← Matrix.mul_assoc]
    rw [tMatN_mul_tInvC ht0, Matrix.one_mul, Matrix.mul_assoc, tMatN_mul_tInvC ht0, Matrix.mul_one]
  rw [e, e, hC]

/-- **Kernel of `phiNS`**: $\varphi(x) = \varphi(x')$ implies $x' = rx$ with $r^2 = 1$. -/
theorem eq_smul_of_phiNS_eq (hA : A ≠ 0) {x x' : LC} (h : phiNS ht htre ht0 x = phiNS ht htre ht0 x') :
    ∃ r : ℂ, r ^ 2 = 1 ∧ (x' : Fin 4 → ℂ) = r • (x : Fin 4 → ℂ) := by
  set X := (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)])
  set X' := (vecQ (x' : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)])
  have hX : nrd X = 1 := nrd_sphC _
  have hX' : nrd X' = 1 := nrd_sphC _
  have hM : sqMat X (conjQ (star X)) = sqMat X' (conjQ (star X')) := by
    have := congrArg (ArchSOInst.mat _) h
    rw [mat_phiNS, mat_phiNS] at this
    exact sqMat_eq_of_MR_eq htre ht0 this
  have hv : ∀ v : ℍ[ℂ, (A : ℂ), (B : ℂ)], X * v * conjQ (star X) = X' * v * conjQ (star X') := fun v => by
    have := congrArg (· *ᵥ qVec v) hM
    simp only [sqMat_mulVec, vecQ_qVec] at this
    have := congrArg (vecQ (A := (A : ℂ)) (B := (B : ℂ))) this
    rwa [vecQ_qVec, vecQ_qVec] at this
  have he := hv 1
  simp only [mul_one] at he
  have hsY : conjQ (star X) = star X * (X * conjQ (star X)) := by
    rw [← mul_assoc, star_mul_eq_nrd, hX]; simp
  have hsY' : conjQ (star X') = star X' * (X' * conjQ (star X')) := by
    rw [← mul_assoc, star_mul_eq_nrd, hX']; simp
  have hu : IsUnit (X' * conjQ (star X')) := by
    rw [isUnit_iff_nrd_ne_zero, nrd_mul, nrd_conjQ, nrd_star, hX']; simp
  have hcj : ∀ v : ℍ[ℂ, (A : ℂ), (B : ℂ)], X * v * star X = X' * v * star X' := fun v => by
    have h1 := hv v
    rw [hsY, hsY', he] at h1
    have h1' : (X * v * star X) * (X' * conjQ (star X')) = (X' * v * star X') * (X' * conjQ (star X')) := by
      simpa only [mul_assoc] using h1
    exact hu.mul_left_inj.1 h1'
  set a := star X' * X
  have ha : nrd a = 1 := by rw [nrd_mul, nrd_star, hX', hX, one_mul]
  have hsa : star a = star X * X' := by rw [star_mul, star_star]
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  obtain ⟨r, hr2, hr⟩ := eq_scalar_of_conj_trivial_gen (two_ne_zero (α := ℂ)) hA' ha fun y => by
    rw [hsa]
    calc star X' * X * Quat.pure y * (star X * X') = star X' * (X * Quat.pure y * star X) * X' := by
          simp only [mul_assoc]
      _ = star X' * (X' * Quat.pure y * star X') * X' := by rw [hcj]
      _ = (star X' * X') * Quat.pure y * (star X' * X') := by simp only [mul_assoc]
      _ = _ := by rw [star_mul_eq_nrd, hX']; simp
  have hr1 : r * r = 1 := by rw [← sq]; exact hr2
  have hXr : X = (r : ℍ[ℂ, (A : ℂ), (B : ℂ)]) * X' := by
    have : X' * a = X := by rw [← mul_assoc, mul_star_eq_nrd, hX']; simp
    rw [← this, hr, ← QuaternionAlgebra.coe_commutes]
  have hX'r : X' = (r : ℍ[ℂ, (A : ℂ), (B : ℂ)]) * X := by
    rw [hXr, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hr1, QuaternionAlgebra.coe_one, one_mul]
  refine ⟨r, hr2, ?_⟩
  have := congrArg qVec hX'r
  rw [qVec_vecQ, QuaternionAlgebra.coe_mul_eq_smul] at this
  rw [this]; funext i; fin_cases i <;> simp [X, qVec, vecQ]

/-- Points of the complex norm-one sphere have sup norm bounded below. -/
theorem norm_ge_of_sphC_ns (x : LC) :
    1 / (1 + ‖(A : ℂ)‖ + ‖(B : ℂ)‖ + ‖(A : ℂ) * B‖) ≤ ‖(x : Fin 4 → ℂ)‖ ^ 2 := by
  have hx := nrd_sphC x
  set r := ‖(x : Fin 4 → ℂ)‖
  have hi : ∀ i, ‖(x : Fin 4 → ℂ) i‖ ^ 2 ≤ r ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ i) 2
  have hc : 0 < 1 + ‖(A : ℂ)‖ + ‖(B : ℂ)‖ + ‖(A : ℂ) * B‖ := by positivity
  rw [div_le_iff₀ hc]
  simp only [nrd, vecQ] at hx
  have h1 : (1 : ℝ) ≤ ‖(x : Fin 4 → ℂ) 0‖ ^ 2 + ‖(A : ℂ)‖ * ‖(x : Fin 4 → ℂ) 1‖ ^ 2 +
      ‖(B : ℂ)‖ * ‖(x : Fin 4 → ℂ) 2‖ ^ 2 + ‖(A : ℂ) * B‖ * ‖(x : Fin 4 → ℂ) 3‖ ^ 2 := by
    have := congrArg norm hx
    rw [norm_one] at this
    rw [← this]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)) ?_
    · simp [norm_pow, norm_mul]
    · simp [norm_pow, norm_mul]
    · simp [norm_pow, norm_mul, mul_assoc]
  nlinarith [hi 0, hi 1, hi 2, hi 3, norm_nonneg (A : ℂ), norm_nonneg (B : ℂ), norm_nonneg ((A : ℂ) * B)]

theorem isLocInj_phiNS (hA : A ≠ 0) : IsLocInj (phiNS (A := A) (B := B) ht htre ht0) := by
  intro x
  set c := 1 / (1 + ‖(A : ℂ)‖ + ‖(B : ℂ)‖ + ‖(A : ℂ) * B‖)
  have hc : 0 < c := by positivity
  refine ⟨{y | dist y x < Real.sqrt c}, isOpen_lt (continuous_id.dist continuous_const) continuous_const,
    by simpa using Real.sqrt_pos.2 hc, fun y hy y' hy' hyy => ?_⟩
  obtain ⟨r, hr2, h1⟩ := eq_smul_of_phiNS_eq ht htre ht0 hA hyy
  have hr : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hr with rfl | rfl
  · exact (Subtype.ext (by simpa using h1)).symm
  · exfalso
    have hd : dist (y' : Fin 4 → ℂ) (y : Fin 4 → ℂ) < 2 * Real.sqrt c := by
      calc dist (y' : Fin 4 → ℂ) (y : Fin 4 → ℂ) ≤ dist (y' : Fin 4 → ℂ) x + dist (y : Fin 4 → ℂ) x :=
            dist_triangle_right _ _ _
        _ < Real.sqrt c + Real.sqrt c := add_lt_add hy' hy
        _ = 2 * Real.sqrt c := by ring
    rw [h1, dist_eq_norm, show (-1 : ℂ) • (y : Fin 4 → ℂ) - (y : Fin 4 → ℂ) = (-2 : ℂ) • (y : Fin 4 → ℂ) by
      module, norm_smul] at hd
    have hn := norm_ge_of_sphC_ns y
    have : ‖(y : Fin 4 → ℂ)‖ < Real.sqrt c := by norm_num at hd; linarith
    have := (Real.lt_sqrt (norm_nonneg _)).1 this
    linarith

/-! ### The real sphere inside the complex sphere -/

theorem eval_qVec_qC (q : ℍ[ℝ,A,B]) :
    (normForm (A : ℂ) (B : ℂ)).eval (qVec (qC q)) = ((normForm A B).eval (qVec q) : ℂ) := by
  rw [eval_normForm_qVec, eval_normForm_qVec, nrd_qC]

/-- $S_1(\mathbb R)\to S_1(\mathbb C)$ (real quaternions as complex ones). -/
def realS : Sph (normForm A B) 1 →* LC where
  toFun h := ⟨qVec (qC (vecQ (h : Fin 4 → ℝ))), by
    show (normForm (A : ℂ) (B : ℂ)).eval _ = 1
    rw [eval_qVec_qC, qVec_vecQ, h.2, Complex.ofReal_one]⟩
  map_one' := by
    apply Subtype.ext
    show qVec (qC (vecQ (qVec (1 : ℍ[ℝ,A,B])))) = qVec (1 : ℍ[ℂ, (A : ℂ), (B : ℂ)])
    rw [vecQ_qVec, map_one]
  map_mul' x y := by
    apply Subtype.ext
    show qVec (qC (vecQ (qVec (vecQ (x : Fin 4 → ℝ) * vecQ (y : Fin 4 → ℝ) : ℍ[ℝ,A,B])))) =
      qVec (vecQ (qVec (qC (vecQ (x : Fin 4 → ℝ)))) * vecQ (qVec (qC (vecQ (y : Fin 4 → ℝ)))) :
        ℍ[ℂ, (A : ℂ), (B : ℂ)])
    rw [vecQ_qVec, vecQ_qVec, vecQ_qVec, map_mul]

theorem vecQ_realS (h : Sph (normForm A B) 1) :
    (vecQ ((realS h : LC) : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = qC (vecQ (h : Fin 4 → ℝ)) := by
  show vecQ (qVec _) = _; rw [vecQ_qVec]

theorem continuous_realS : Continuous (realS (A := A) (B := B)) := by
  refine Continuous.subtype_mk ?_ _
  have h : ∀ i, Continuous fun x : Sph (normForm A B) 1 => (x : Fin 4 → ℝ) i :=
    fun i => (continuous_apply i).comp continuous_subtype_val
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [qVec, qC_re, qC_imI, qC_imJ, qC_imK, vecQ] <;>
    exact Complex.continuous_ofReal.comp (h _)

theorem realS_injective : Function.Injective (realS (A := A) (B := B)) := fun x y h => by
  apply Subtype.ext
  funext i
  have := congrFun (congrArg Subtype.val h) i
  fin_cases i <;> simpa [realS, qVec, vecQ] using this

include htre ht0 in
/-- **Real quaternions act by $\mathrm{diag}(1,c_h)$.** -/
theorem phiNS_realS (hd0 : d ≠ 0) (h : Sph (normForm A B) 1) :
    phiNS ht htre ht0 (realS h) = iota 1 (pureFormD A B d) (cS hd0 (conjS h)) := by
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (phiNS ht htre ht0 (realS h)) = ArchSOInst.mat _ (iota 1 (pureFormD A B d) (cS hd0 (conjS h)))
  rw [mat_phiNS, vecQ_realS, MR_qC htre ht0 (nrd_sph h), mat_iota, mat_cS, mat_conjS_eq_conjGL]
  rfl

/-! ### The Cayley section -/

include ht in
theorem eval_qVec_cayX {y : Sph (nsFormR A B d) 1} (hy0 : 0 < 1 + (y : Fin 4 → ℝ) 0) :
    (normForm (A : ℂ) (B : ℂ)).eval (qVec (cayX (A := A) (B := B) t (y : Fin 4 → ℝ))) = 1 := by
  rw [eval_normForm_qVec, nrd_cayX ht y.2 hy0]

/-- **The Cayley point** $X(y)\in S_1(\mathbb C)$, $y_0 > -1$. -/
def sNS (y : Sph (nsFormR A B d) 1) (hy0 : 0 < 1 + (y : Fin 4 → ℝ) 0) : LC :=
  ⟨qVec (cayX (A := A) (B := B) t (y : Fin 4 → ℝ)), eval_qVec_cayX ht hy0⟩

theorem vecQ_sNS (y : Sph (nsFormR A B d) 1) (hy0 : 0 < 1 + (y : Fin 4 → ℝ) 0) :
    (vecQ ((sNS ht y hy0 : LC) : Fin 4 → ℂ) : ℍ[ℂ, (A : ℂ), (B : ℂ)]) = cayX (A := A) (B := B) t (y : Fin 4 → ℝ) := by
  show vecQ (qVec _) = _; rw [vecQ_qVec]

/-- **$\varphi(X(y))e_0 = y$.** -/
theorem phiNS_sNS_e0 (y : Sph (nsFormR A B d) 1) (hy0 : 0 < 1 + (y : Fin 4 → ℝ) 0) :
    ArchSOInst.mat _ (phiNS ht htre ht0 (sNS ht y hy0)) *ᵥ (e₀ : Fin 4 → ℝ) = (y : Fin 4 → ℝ) := by
  rw [mat_phiNS, vecQ_sNS]; exact MR_cayX_e0 ht htre ht0 y.2 hy0

/-! ### The test set -/

/-- The Cayley point, extended by $1$ where $y_0\le-1$. -/
def sNS0 (y : Sph (nsFormR A B d) 1) : LC := if hy : 0 < 1 + (y : Fin 4 → ℝ) 0 then sNS ht y hy else 1

theorem sNS0_of_pos {y : Sph (nsFormR A B d) 1} (hy : 0 < 1 + (y : Fin 4 → ℝ) 0) : sNS0 ht y = sNS ht y hy :=
  dif_pos hy

/-- **The test set**: the points $X(y)h$ with $y$ in the graph ball and $h$ in the Cayley ball. -/
def ysNS (δ : ℝ) : Set LC :=
  (fun p : Sph (nsFormR A B d) 1 × Sph (normForm A B) 1 => sNS0 ht p.1 * realS p.2) ''
    (grBall A B d δ ×ˢ cayBall A B δ)

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
