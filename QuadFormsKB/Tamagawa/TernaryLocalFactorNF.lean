/-
# The local factors of the trace-zero lattice at every place, from a local adapted basis

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$ ($ab \ne 0$), $\mathcal O$ a maximal order, $v$ a finite place, $E$ a local
adapted basis of $\mathcal O_v$ (`LTZ`), $P$ the coordinates of $E_1, E_2, E_3$, $T = \langle -a,-b,ab\rangle\circ P$ the integral local form of
$\mathcal O_v^0$ (`LTZ.formT`), $\rho = \operatorname{re}E_0$.

**Proves** (`LTZ.localFactor_eq`), at every finite place:
$$\tfrac12\beta_v(T, T)\,\|\det P\|^4 = (1 - q^{-2})\,\varepsilon_v\,\|8\|^{-1}\,\|ab\|^{-3}\,\|\det(\text{coordinates of }E)\|,\qquad
\varepsilon_v = \tfrac{2}{1 - q^{-1}}\ (v \in \mathrm{Ram}_f),\ 1\ \text{otherwise},$$
by porting the frame computations to local adapted bases: split places (`exists_GL_split`: $T \cong \langle -1\rangle\perp(-x_1x_2)$ and
$|2\rho| = 1$), odd ramified places (`exists_GL_oddRam`: $T \cong \langle u_0\rangle\perp\varpi\langle u_1, u_2\rangle$, $|\rho| = 1$), ramified dyadic places
(`exists_GL_ramDyadic`: $T \cong \langle u\rangle\perp\varpi T'$, $|2\rho| = 1$), with the DVR densities.

Sources: Voight 2021, §§13.3, 22.1; Kitaoka 1993, §5.6 [unverified]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.TernaryLocalBasisNF
import QuadFormsKB.Tamagawa.TernaryIndexNF
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
  QuadFormsKB.QuatZeta QuadFormsKB.HilbertModular QuadFormsKB.NFEuler IsLocalization QuadFormsKB.LocalDensity.NF

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {v : HeightOneSpectrum (𝓞 F)}
  {O : Subalgebra (𝓞 F) (QuatF F a b)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem map_splitForm_slT_nf : (splitForm (-1 : 𝔬) (slT 𝔬)).map (algebraMap 𝔬 Fv) = detSlForm v := by
  ext i j
  simp only [QuadForm.map, Matrix.map_apply, splitForm_coeff]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [cornerMat_zero_zero, cornerMat_zero_succ, cornerMat_succ_zero, cornerMat_succ_succ]
  · simp [detSlForm]
  · fin_cases j <;> simp [detSlForm]
  · fin_cases i <;> simp [detSlForm]
  · fin_cases i <;> fin_cases j <;> simp [slT, detSlForm]

local notation "𝔽v" => IsLocalRing.ResidueField 𝔬
local notation "resv" => IsLocalRing.residue 𝔬

theorem pi_dvd_of_residue_eq_zero_nf {x : 𝔬} (h : resv x = 0) : NF.π v ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, (NF.irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

/-- Anisotropy of the binary part mod $\varpi$ (copy of `aniso_residue_of_diag`, no PID). -/
theorem aniso_residue_of_diag_nf (hodd : ¬ NF.π v ∣ 2) {S : QuadForm 𝔬 3} (hS : ∀ z, S.eval z = 0 → z = 0)
    {W : Matrix (Fin 3) (Fin 3) 𝔬} (hW : IsUnit W.det) {u₀ u₁ u₂ : 𝔬} (hu1 : IsUnit u₁) (hu2 : IsUnit u₂)
    (hSW : S.compMat W = QuadForm.diag ![u₀, NF.π v * u₁, NF.π v * u₂]) :
    ∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  have h1F : resv u₁ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu1
  by_cases hy : y = 0
  · subst hy
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, mul_eq_zero,
      h1F, false_or, pow_eq_zero_iff] at hxy
    exact ⟨hxy, rfl⟩
  exfalso
  obtain ⟨X, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨Y, rfl⟩ := IsLocalRing.residue_surjective y
  have hYu : IsUnit Y := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hy
  have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) hodd
  set m : 𝔬 := -(u₂ * Y ^ 2)
  have hmu : IsUnit (2 * m) := h2u.mul (hu2.mul (hYu.pow 2)).neg
  have hdvd : NF.π v ^ 1 ∣ (DVR.unary u₁).eval ![X] - m := by
    rw [pow_one]
    apply pi_dvd_of_residue_eq_zero_nf
    rw [eval_unary]
    simp only [m, Matrix.cons_val_zero, sub_neg_eq_add, map_add, map_mul, map_pow]
    linear_combination hxy
  obtain ⟨y', hy', -⟩ := DVR.exists_eval_eq_of_dvd (NF.irreducible_π v) (DVR.unary u₁) (e := 0)
    (by simp) (by simpa using DVR.dvr_not_dvd_of_isUnit (NF.irreducible_π v) hmu) le_rfl ![X] hdvd
  rw [eval_unary] at hy'
  set z : Fin 3 → 𝔬 := ![0, y' 0, Y]
  have hz : S.eval (W *ᵥ z) = 0 := by
    rw [← eval_compMat, hSW, eval_diag_gen, Fin.sum_univ_three]
    simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (NF.π v) * hy'
  have h0 := hS _ hz
  have hz0 : z = 0 := by
    have := congrArg (fun w => W⁻¹ *ᵥ w) h0
    simpa [mulVec_mulVec, nonsing_inv_mul _ hW] using this
  have := congrFun hz0 2
  simp only [z, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at this
  exact hYu.ne_zero this

/-- A unimodular diagonal ternary form over $\mathfrak o_v$ ($v \nmid 2$) is isotropic (copy, no PID). -/
theorem exists_isotropic_unit_diag_nf (hodd : ¬ NF.π v ∣ 2) {u₀ u₁ u₂ : 𝔬} (hu0 : IsUnit u₀) (hu1 : IsUnit u₁)
    (hu2 : IsUnit u₂) : ∃ z : Fin 3 → 𝔬, z ≠ 0 ∧ (QuadForm.diag ![u₀, u₁, u₂]).eval z = 0 := by
  classical
  have := Fintype.ofFinite 𝔽v
  have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) hodd
  have h2F : (2 : 𝔽v) ≠ 0 := by
    have := h2u.map resv; rw [map_ofNat] at this; exact this.ne_zero
  have hchar : ringChar 𝔽v ≠ 2 := fun h => h2F (by
    have := ringChar.Nat.cast_ringChar (R := 𝔽v); rw [h] at this; exact_mod_cast this)
  have hcard := FiniteField.odd_card_of_char_ne_two hchar
  have h0F : resv u₀ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu0
  have h1F : resv u₁ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu1
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C (resv u₀) * Polynomial.X ^ 2)
    (g := Polynomial.C (resv u₁) * Polynomial.X ^ 2 + Polynomial.C (resv u₂))
    (by rw [Polynomial.degree_C_mul_X_pow 2 h0F]; rfl)
    (by rw [Polynomial.degree_add_C (by rw [Polynomial.degree_C_mul_X_pow 2 h1F]; norm_num),
      Polynomial.degree_C_mul_X_pow 2 h1F]; rfl) hcard
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at hxy
  obtain ⟨X, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨Y, rfl⟩ := IsLocalRing.residue_surjective y
  set m : 𝔬 := -u₂
  have hmu : IsUnit (2 * m) := h2u.mul hu2.neg
  have hdvd : NF.π v ^ 1 ∣ (QuadForm.diag ![u₀, u₁]).eval ![X, Y] - m := by
    rw [pow_one]
    apply pi_dvd_of_residue_eq_zero_nf
    rw [eval_diag_gen, Fin.sum_univ_two]
    simp only [m, Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, map_add, map_mul, map_pow]
    linear_combination hxy
  obtain ⟨w, hw, -⟩ := DVR.exists_eval_eq_of_dvd (NF.irreducible_π v) (QuadForm.diag ![u₀, u₁]) (e := 0)
    (by simp) (by simpa using DVR.dvr_not_dvd_of_isUnit (NF.irreducible_π v) hmu) le_rfl ![X, Y] hdvd
  rw [eval_diag_gen, Fin.sum_univ_two] at hw
  refine ⟨![w 0, w 1, 1], fun h => by simpa using congrFun h 2, ?_⟩
  rw [eval_diag_gen, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hw ⊢
  linear_combination hw

theorem valued_pow_mul_unit_nf {k : ℕ} {u : 𝔬} (hu : IsUnit u) :
    Valued.v (algebraMap 𝔬 Fv (NF.π v ^ k * u)) = WithZero.exp (-(k : ℤ)) := by
  show Valued.v (((NF.π v ^ k * u : 𝔬)) : Fv) = _
  push_cast
  rw [map_mul, map_pow, NF.valued_π, (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu,
    mul_one, ← WithZero.exp_nsmul]
  congr 1; simp

namespace LTZ

variable (L : LTZ v O)

/-! ### Split places -/

section Split

variable (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
  (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
    (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F))

include hφ in
/-- **At a split place, $T \cong \langle -1\rangle\perp(-x_1x_2)$ over $\mathfrak o_v$** ($\mathcal O_v^0 \cong \mathfrak{sl}_2(\mathfrak o_v)$). -/
theorem exists_GL_split (hO : IsOrder (𝓞 F) F O) :
    ∃ Y : Matrix (Fin 3) (Fin 3) 𝔬, IsUnit Y.det ∧ (L.formT hO).compMat Y = splitForm (-1) (slT 𝔬) := by
  set Hm : Matrix (Fin 2) (Fin 2) Fv := !![1, 0; 0, -1]
  set z : Fin 3 → QuatV v a b := ![φ.symm Hm, E12 v φ, E21 v φ]
  have hz : ∀ k, z k ∈ Ov0NF v O := by
    intro k; fin_cases k
    · show φ.symm Hm ∈ Ov0NF v O
      rw [mem_Ov0NF, mem_localOrder_iff_split_nf v φ hφ, re_eq_zero_iff_trace_nf v φ, AlgEquiv.apply_symm_apply]
      refine ⟨(mem_matOrder).2 fun i j => ?_, by simp [Hm, Matrix.trace_fin_two]⟩
      fin_cases i <;> fin_cases j
      · exact ⟨1, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨-1, by simp [Hm]⟩
    · exact E12_mem_nf v φ hφ
    · exact E21_mem_nf v φ hφ
  have hy : ∀ k, ∃ c : Fin 3 → 𝔬, z k = L.psi (fun l => (c l : Fv)) := fun k => (L.mem_Ov0_iff _).1 (hz k)
  choose c hc using hy
  set Yo : Matrix (Fin 3) (Fin 3) 𝔬 := Matrix.of fun r k => c k r with hYo
  set Y := Yo.map (algebraMap 𝔬 Fv) with hY
  set Sv := (QV v a b).compMat L.Pm
  have hSv : ∀ w, Sv.eval w = nrd (L.psi w) := fun w => (L.nrd_psi w).symm
  have hYw : ∀ w : Fin 3 → Fv, L.psi (Y *ᵥ w) = ∑ k, w k • z k := by
    intro w
    simp_rw [hc, psi, Finset.smul_sum, smul_smul]
    simp only [mulVec, dotProduct, Y, Yo, Matrix.map_apply, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]; rfl
  have hval : ∀ w, (Sv.compMat Y).eval w = (detSlForm v).eval w := by
    intro w
    rw [eval_compMat, hSv, hYw, ← det_algEquiv φ, eval_detSlForm]
    simp only [Fin.sum_univ_three, map_add, map_smul, z, E12, E21, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, AlgEquiv.apply_symm_apply]
    simp [Hm, Matrix.det_fin_two]
    ring
  have hS : Sv.compMat Y = detSlForm v := eq_of_eval_eq hval
  have hdecomp : ∀ M : Matrix (Fin 2) (Fin 2) Fv, M 0 0 + M 1 1 = 0 →
      M = M 0 0 • Hm + M 0 1 • Matrix.single 0 1 1 + M 1 0 • Matrix.single 1 0 1 := by
    intro M hM
    refine Matrix.ext fun r s => ?_
    fin_cases r <;> fin_cases s
    · simp [Hm]
    · simp [Hm]
    · simp [Hm]
    · show M 1 1 = M 0 0 * (-1) + M 0 1 * 0 + M 1 0 * 0
      linear_combination hM
  have hcol : ∀ i : Fin 3, ∃ γ : Fin 3 → 𝔬, Y *ᵥ (fun k => algebraMap 𝔬 Fv (γ k)) = Pi.single i 1 := by
    intro i
    have hmem : L.psi (Pi.single i 1) ∈ Ov0NF v O := by
      rw [L.psi_mem_Ov0_iff]
      intro j
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    obtain ⟨hloc, hre⟩ := hmem
    rw [mem_localOrder_iff_split_nf v φ hφ, mem_matOrder] at hloc
    rw [re_eq_zero_iff_trace_nf v φ, Matrix.trace_fin_two] at hre
    obtain ⟨g00, hg00⟩ := hloc 0 0
    obtain ⟨g01, hg01⟩ := hloc 0 1
    obtain ⟨g10, hg10⟩ := hloc 1 0
    refine ⟨![g00, g01, g10], ?_⟩
    apply L.psi_injective
    rw [hYw]
    apply φ.injective
    rw [hdecomp _ hre, ← hg00, ← hg01, ← hg10]
    simp only [Fin.sum_univ_three, map_add, map_smul, z, E12, E21, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, AlgEquiv.apply_symm_apply]
  choose γ hγ using hcol
  set C : Matrix (Fin 3) (Fin 3) 𝔬 := Matrix.of fun k i => γ i k
  have hYC : Yo * C = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective 𝔬 Fv)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Matrix.ext fun r i => ?_
    have := congrFun (hγ i) r
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, C, Matrix.of_apply]
    refine this.trans ?_
    rw [Matrix.one_apply, Pi.single_apply]
  refine ⟨Yo, ?_, ?_⟩
  · have := congrArg Matrix.det hYC
    rw [det_mul, det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  · apply NF.map_injective (IsFractionRing.injective 𝔬 Fv)
    rw [← map_compMat, L.map_formT hO, map_splitForm_slT_nf]
    exact hS

include hφ in
/-- **At a split place $|2\rho|_v = 1$.** -/
theorem norm_two_mul_re_split (hO : IsOrder (𝓞 F) F O) : ‖(2 : Fv) * (L.E 0).re‖ = 1 := by
  refine le_antisymm (L.norm_two_mul_re_le hO) (L.one_le_norm_two_mul_re (y := φ.symm (Matrix.single 0 0 1)) ?_ ?_)
  · rw [mem_localOrder_iff_split_nf v φ hφ, AlgEquiv.apply_symm_apply, mem_matOrder]
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Matrix.single_apply]; tauto⟩
  · have htr : trd (φ.symm (Matrix.single 0 0 1)) = 1 := by
      rw [trd_eq_trace_nf v φ, AlgEquiv.apply_symm_apply, Matrix.trace_fin_two]; simp
    rw [trd] at htr
    have h2 : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    field_simp
    linear_combination htr

end Split

/-! ### Odd ramified places -/

section OddRam

theorem one_le_norm_re : 1 ≤ ‖(L.E 0).re‖ := by
  obtain ⟨c, hc⟩ := (L.mem_iff 1).1 (Subalgebra.one_mem _)
  have h := congrArg QuaternionAlgebra.re hc
  rw [L.re_sum, QuaternionAlgebra.re_one] at h
  have hle : ‖((c 0 : 𝔬) : Fv)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (c 0).2)
  have h2 := congrArg norm h
  rw [norm_mul, norm_one] at h2
  nlinarith [norm_nonneg ((c 0 : 𝔬) : Fv), norm_nonneg (L.E 0).re]

theorem norm_two_of_odd (hodd : ¬ NF.π v ∣ 2) : ‖(2 : Fv)‖ = 1 := by
  have h := norm_coe_of_pow_dvd v (x := (2 : 𝔬)) (e := 0) (by simp) (by simpa using hodd)
  rw [pow_zero, inv_one] at h
  rw [← h]; push_cast; rfl

theorem norm_re_eq_one_of_odd (hO : IsOrder (𝓞 F) F O) (hodd : ¬ NF.π v ∣ 2) : ‖(L.E 0).re‖ = 1 := by
  have h := L.norm_two_mul_re_le hO
  rw [norm_mul, norm_two_of_odd hodd, one_mul] at h
  exact le_antisymm h L.one_le_norm_re

theorem eval_QVPm_coe (hO : IsOrder (𝓞 F) F O) (z : Fin 3 → 𝔬) :
    ((QV v a b).compMat L.Pm).eval (fun i => algebraMap 𝔬 Fv (z i)) = algebraMap 𝔬 Fv ((L.formT hO).eval z) := by
  rw [← L.map_formT hO, DVR.eval_map_comp']

theorem formT_nondegenerate (hO : IsOrder (𝓞 F) F O) (ha : a ≠ 0) (hb : b ≠ 0) : (L.formT hO).Nondegenerate := by
  intro h0
  have h := L.det_hessian_formT hO
  rw [h0, map_zero] at h
  have hr : algebraMap 𝔬 Fv (ι v a) * algebraMap 𝔬 Fv (ι v b) * L.Pm.det ≠ 0 := mul_ne_zero (mul_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha))
    ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb))) L.det_Pm_ne_zero
  have h8 : (8 : Fv) ≠ 0 := by
    have : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    rw [show (8 : Fv) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero this this) this
  exact mul_ne_zero h8 (pow_ne_zero 2 hr) h.symm

set_option maxHeartbeats 1600000 in
/-- **The Jordan shape of $\mathcal O_v^0$ at an odd ramified place:** $T \cong \langle u_0\rangle\perp\varpi\langle u_1, u_2\rangle$ over
$\mathfrak o_v$, $\langle\bar u_1,\bar u_2\rangle$ anisotropic (port of `TZFrame.exists_GL_oddRam`). -/
theorem exists_GL_oddRam (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (hv : v ∈ ramFin ha hb)
    (hodd : ¬ NF.π v ∣ 2) :
    ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W.det ∧ IsUnit u₀ ∧ IsUnit u₁ ∧ IsUnit u₂ ∧
      (∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
      (L.formT hO.1).compMat W = splitForm u₀ (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]) := by
  have hdiv := hdiv_of_mem_ramFin_nf v ha hb hv
  have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
  have hπ := NF.irreducible_π v
  set S := L.formT hO.1 with hSdef
  have hSnd : S.Nondegenerate := L.formT_nondegenerate hO.1 ha hb
  have haniso : ∀ z, S.eval z = 0 → z = 0 := L.formT_aniso hdiv hO.1
  obtain ⟨W, d, hWu, hd0, hWd⟩ := exists_diag_compMat v hodd S hSnd
  have hdec : ∀ i, ∃ (k : ℕ) (u : 𝔬), IsUnit u ∧ d i = NF.π v ^ k * u := by
    intro i
    obtain ⟨k, hk, hk'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (hd0 i)
    obtain ⟨w, hw, hw1⟩ := DVR.dvr_exact hπ hk hk'
    exact ⟨k, w, hw1, hw⟩
  choose k u hu hdu using hdec
  have hevalW : ∀ i, S.eval (W *ᵥ Pi.single i 1) = d i := by
    intro i
    rw [← eval_compMat, hWd, eval_diag_gen]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hπF : algebraMap 𝔬 Fv (NF.π v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hπ.ne_zero
  -- (1) the exponents are at most `1` (maximality)
  have hk1 : ∀ i, k i ≤ 1 := by
    intro i
    by_contra hki
    push Not at hki
    set x : Fin 3 → Fv := fun j => algebraMap 𝔬 Fv ((W *ᵥ Pi.single i 1) j) with hx
    have hint : IsLocalization.IsInteger 𝔬
        (((QV v a b).compMat L.Pm).eval ((algebraMap 𝔬 Fv (NF.π v))⁻¹ • x)) := by
      rw [eval_smul_vec_nf, hx, L.eval_QVPm_coe hO.1, hevalW, hdu i]
      obtain ⟨j, hj⟩ : ∃ j, k i = j + 2 := ⟨k i - 2, by omega⟩
      refine ⟨NF.π v ^ j * u i, ?_⟩
      rw [hj, map_mul, map_mul, map_pow, map_pow]
      field_simp
      ring
    have hy := L.isInteger_of_eval hdiv heq _ hint
    have hcol : ∀ j, NF.π v ∣ W j i := by
      intro j
      obtain ⟨c, hc⟩ := hy j
      refine ⟨c, IsFractionRing.injective 𝔬 Fv ?_⟩
      rw [map_mul, hc]
      simp only [hx, Pi.smul_apply, smul_eq_mul, mulVec_single_one]
      field_simp
      rfl
    have hdvd : NF.π v ∣ W.det := by
      rw [Matrix.det_succ_column W i]
      exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hcol j) _) _
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd hWu)
  -- (2) not all exponents vanish (anisotropy)
  have hk0 : ¬ ∀ i, k i = 0 := by
    intro h
    have hd : d = ![u 0, u 1, u 2] := by
      ext i; fin_cases i <;> simp [hdu, h]
    obtain ⟨z, hz0, hz⟩ := exists_isotropic_unit_diag_nf (v := v) hodd (hu 0) (hu 1) (hu 2)
    rw [← hd, ← hWd, eval_compMat] at hz
    have h0 := haniso _ hz
    apply hz0
    have := congrArg (fun w => W⁻¹ *ᵥ w) h0
    simpa [mulVec_mulVec, nonsing_inv_mul _ hWu] using this
  -- (3) the sum of the exponents is even (square discriminant)
  have hpar : Even (k 0 + k 1 + k 2) := by
    have h1 := congrArg Matrix.det (hessian_compMat S W)
    rw [hWd, det_mul, det_mul, det_transpose] at h1
    have hHd : (QuadForm.diag d).hessian.det = 8 * (d 0 * d 1 * d 2) := by
      simp [QuadForm.hessian, QuadForm.diag, Fin.prod_univ_three]; ring
    rw [hHd] at h1
    set r : Fv := algebraMap 𝔬 Fv (ι v a) * algebraMap 𝔬 Fv (ι v b) * L.Pm.det with hr
    have hr0 : r ≠ 0 := mul_ne_zero (mul_ne_zero
      ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha))
      ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb))) L.det_Pm_ne_zero
    have h3 := congrArg (algebraMap 𝔬 Fv) h1
    simp only [map_mul] at h3
    rw [L.det_hessian_formT hO.1, ← hr] at h3
    simp only [map_mul, map_pow, map_ofNat] at h3
    set s : Fv := algebraMap 𝔬 Fv W.det * r with hs
    have hs0 : s ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hWu.ne_zero) hr0
    have h8 : (8 : Fv) ≠ 0 := by
      have : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
      rw [show (8 : Fv) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero this this) this
    have h4 : algebraMap 𝔬 Fv (d 0 * d 1 * d 2) = s ^ 2 := by
      apply mul_left_cancel₀ h8
      simp only [map_mul, hs]; linear_combination h3
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hs0
    have h5 := congrArg Valued.v h4
    rw [map_pow, hm, hdu 0, hdu 1, hdu 2, show NF.π v ^ k 0 * u 0 * (NF.π v ^ k 1 * u 1) * (NF.π v ^ k 2 * u 2) =
      NF.π v ^ (k 0 + k 1 + k 2) * (u 0 * u 1 * u 2) by ring,
      valued_pow_mul_unit_nf ((hu 0).mul (hu 1) |>.mul (hu 2)),
      ← WithZero.exp_nsmul, WithZero.exp_inj] at h5
    exact ⟨Int.toNat (-m), by simp at h5; omega⟩
  -- (4) conclude
  have fin : ∀ (W' : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W'.det → IsUnit u₀ → IsUnit u₁ →
      IsUnit u₂ → S.compMat W' = QuadForm.diag ![u₀, NF.π v * u₁, NF.π v * u₂] →
      ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W.det ∧ IsUnit u₀ ∧ IsUnit u₁ ∧ IsUnit u₂ ∧
        (∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
        S.compMat W = splitForm u₀ (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]) :=
    fun W' u₀ u₁ u₂ hW' h0 h1 h2 hS' => ⟨W', u₀, u₁, u₂, hW', h0, h1, h2,
      aniso_residue_of_diag_nf hodd haniso hW' h1 h2 hS', by rw [hS', diag_three_eq_splitForm]⟩
  have hperm : ∀ σ : Equiv.Perm (Fin 3), IsUnit (W * σ.permMatrix 𝔬).det := fun σ => by
    rw [det_mul, Matrix.det_permutation]
    exact hWu.mul (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])
  have h0' := hk1 0
  have h1' := hk1 1
  have h2' := hk1 2
  interval_cases hk0' : k 0 <;> interval_cases hk1' : k 1 <;> interval_cases hk2' : k 2
  · exact absurd (fun i => by fin_cases i <;> assumption) hk0
  · exact absurd hpar (by decide)
  · exact absurd hpar (by decide)
  · exact fin W (u 0) (u 1) (u 2) hWu (hu 0) (hu 1) (hu 2) (by
      rw [hWd]; congr 1; ext i; fin_cases i <;> simp [hdu, hk0', hk1', hk2'])
  · exact absurd hpar (by decide)
  · exact fin (W * (Equiv.swap (0 : Fin 3) 1).permMatrix 𝔬) (u 1) (u 0) (u 2) (hperm _) (hu 1) (hu 0) (hu 2) (by
      rw [← compMat_mul, hWd, diag_compMat_perm]; congr 1; ext i
      fin_cases i <;> simp [hdu, hk0', hk1', hk2', Equiv.swap_apply_of_ne_of_ne])
  · exact fin (W * (Equiv.swap (0 : Fin 3) 2).permMatrix 𝔬) (u 2) (u 1) (u 0) (hperm _) (hu 2) (hu 1) (hu 0) (by
      rw [← compMat_mul, hWd, diag_compMat_perm]; congr 1; ext i
      fin_cases i <;> simp [hdu, hk0', hk1', hk2', Equiv.swap_apply_of_ne_of_ne])
  · exact absurd hpar (by decide)

end OddRam

/-! ### Ramified dyadic places -/

section RamDyadic

/-- **The shape of $\mathcal O_v^0$ at a ramified dyadic place:** $T \cong \langle u\rangle\perp\varpi T'$ over $\mathfrak o_v$. -/
theorem exists_GL_ramDyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (hv : v ∈ ramFin ha hb)
    (h2 : NF.π v ∣ 2) :
    ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u : 𝔬) (T : QuadForm 𝔬 2), IsUnit W.det ∧ IsUnit u ∧ IsUnit T.hessian.det ∧
      (∀ x : Fin 2 → 𝔬, NF.π v ∣ T.eval x → ∀ i, NF.π v ∣ x i) ∧ (L.formT hO.1).compMat W = splitForm u (NF.π v • T) ∧
      ∃ g : 𝔬, IsUnit g ∧ -u * (T.coeff 0 1 ^ 2 - 4 * T.coeff 0 0 * T.coeff 1 1) = g ^ 2 := by
  have hdiv := hdiv_of_mem_ramFin_nf v ha hb hv
  have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
  exact exists_ram_dyadic_shape (NF.irreducible_π v) two_ne_zero h2 _ (L.hmax_ram hdiv heq hO.1) (L.hdisc hO.1 ha hb)

/-- **At a ramified dyadic place $|2\rho|_v = 1$.** -/
theorem norm_two_mul_re_ramDyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : NF.π v ∣ 2) : ‖(2 : Fv) * (L.E 0).re‖ = 1 := by
  obtain ⟨W, u, T, hWu, huu, hTu, haniso, hW, g, hg, hgu⟩ := L.exists_GL_ramDyadic ha hb hO hv h2
  have hdiv := hdiv_of_mem_ramFin_nf v ha hb hv
  have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
  set ι' := algebraMap 𝔬 Fv with hι'
  set z0 : Fin 3 → 𝔬 := fun l => W l 0 with hz0
  set f0 : QuatV v a b := L.psi (fun l => ι' (z0 l)) with hf0
  have hSz0 : (L.formT hO.1).eval z0 = u := by
    have := congrArg (fun S : QuadForm 𝔬 3 => S.coeff 0 0) hW
    simp only [compMat_coeff, le_refl, ite_true] at this
    rw [this]; simp [splitForm_coeff]
  have hnrd0 : nrd f0 = ι' u := by
    rw [hf0, ← L.eval_formT_coe hO.1, hSz0]
  have hre0 : f0.re = 0 := L.re_psi _
  set B := T.coeff 0 1 with hB
  have hg0 : ι' g ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hg.ne_zero
  set c : Fv := ι' B / (2 * ι' g) with hc
  set x : QuatV v a b := ⟨1 / 2, 0, 0, 0⟩ + c • f0 with hx
  have hxre : x.re = 1 / 2 := by
    simp only [hx, QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hre0, mul_zero, add_zero]
  have hnrdx : nrd x = ι' (u * T.coeff 0 0 * T.coeff 1 1 * ↑hg.unit⁻¹ ^ 2) := by
    have h2F : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    have hgi : ι' g * ι' ↑hg.unit⁻¹ = 1 := by rw [← map_mul, hg.mul_val_inv, map_one]
    have hgu' : -ι' u * (ι' B ^ 2 - 4 * ι' (T.coeff 0 0) * ι' (T.coeff 1 1)) = ι' g ^ 2 := by
      have := congrArg ι' hgu
      simpa [map_mul, map_sub, map_pow, map_neg, map_ofNat] using this
    have hn : nrd x = 1 / 4 + c ^ 2 * nrd f0 := by
      simp only [nrd, hx, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
        QuaternionAlgebra.imK_smul, smul_eq_mul, hre0]
      ring
    rw [hn, hnrd0, hc]
    simp only [map_mul, map_pow]
    have hginv : ι' ↑hg.unit⁻¹ = (ι' g)⁻¹ := eq_inv_of_mul_eq_one_right hgi
    rw [hginv]
    field_simp
    linear_combination (-4 : Fv) * hgu'
  have hxmem : x ∈ localOrder (v := v) a b O := by
    rw [heq, mem_valOrder, hnrdx]; exact ⟨_, rfl⟩
  exact le_antisymm (L.norm_two_mul_re_le hO.1) (L.one_le_norm_two_mul_re hxmem hxre)

end RamDyadic

end LTZ

/-! ### The local factor -/

section Factor

theorem localDensityForm_compMat_unit {T S : QuadForm 𝔬 3} {W : Matrix (Fin 3) (Fin 3) 𝔬} (hW : IsUnit W.det)
    (h : T.compMat W = S) : DVR.localDensityForm T T (NF.π v) = DVR.localDensityForm S S (NF.π v) := by
  have hg : Siegel.IsometricGL T S :=
    ⟨((Matrix.isUnit_iff_isUnit_det W).2 hW).unit, fun x => by rw [← h, eval_compMat]; rfl⟩
  rw [DVR.localDensityForm_congr_left hg, DVR.localDensityForm_congr_right S hg]

theorem norm_unit {u : 𝔬} (hu : IsUnit u) : ‖algebraMap 𝔬 Fv u‖ = 1 := by
  have := norm_coe_of_pow_dvd v (x := u) (e := 0) (by simp)
    (by simpa using DVR.dvr_not_dvd_of_isUnit (NF.irreducible_π v) hu)
  rwa [pow_zero, inv_one] at this

theorem norm_det_hessian_of_compMat {T S : QuadForm 𝔬 3} {W : Matrix (Fin 3) (Fin 3) 𝔬} (hW : IsUnit W.det)
    (h : T.compMat W = S) : ‖algebraMap 𝔬 Fv T.hessian.det‖ = ‖algebraMap 𝔬 Fv S.hessian.det‖ := by
  have h1 := congrArg Matrix.det (hessian_compMat T W)
  rw [h, det_mul, det_mul, det_transpose] at h1
  rw [h1, map_mul, map_mul, norm_mul, norm_mul, norm_unit hW]; ring

theorem norm_pi : ‖algebraMap 𝔬 Fv (NF.π v)‖ = (DVR.q 𝔬 : ℝ)⁻¹ := by
  have hπ := NF.irreducible_π v
  have := norm_coe_of_pow_dvd v (x := NF.π v) (e := 1) (by simp)
    (by rw [pow_succ, pow_one]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one
      ((mul_dvd_mul_iff_left hπ.ne_zero).1 (by simpa using h))))
  rwa [pow_one] at this

theorem alg_ramDyadic {q t X Y : ℝ} (hq : 1 < q) (ht : 0 < t) (hY : 0 < Y) (hXY : X * Y = t⁻¹ * q⁻¹) :
    1 / 2 * (4 * t⁻¹ * q ^ 2 * (q + 1)) * Y ^ 4 =
      (1 - (q ^ 2)⁻¹) * (2 / (1 - q⁻¹)) * (t ^ 3)⁻¹ * (X ^ 3)⁻¹ * (t⁻¹ * Y) := by
  have hq0 : 0 < q := by linarith
  have hX : X = t⁻¹ * q⁻¹ / Y := (eq_div_iff hY.ne').2 hXY
  have hne : q - 1 ≠ 0 := by linarith
  rw [hX, show 1 - q⁻¹ = (q - 1) / q by field_simp, show 1 - (q ^ 2)⁻¹ = (q - 1) * (q + 1) / q ^ 2 by
    field_simp; ring]
  field_simp
  ring

theorem alg_oddRam {q X Y : ℝ} (hq : 1 < q) (hY : 0 < Y) (hXY : X * Y = q⁻¹) :
    1 / 2 * (4 * q ^ 2 * (q + 1)) * Y ^ 4 =
      (1 - (q ^ 2)⁻¹) * (2 / (1 - q⁻¹)) * (1 ^ 3)⁻¹ * (X ^ 3)⁻¹ * (1 * Y) := by
  have hq0 : 0 < q := by linarith
  have hX : X = q⁻¹ / Y := (eq_div_iff hY.ne').2 hXY
  have hne : q - 1 ≠ 0 := by linarith
  rw [hX, show 1 - q⁻¹ = (q - 1) / q by field_simp, show 1 - (q ^ 2)⁻¹ = (q - 1) * (q + 1) / q ^ 2 by
    field_simp; ring]
  field_simp
  ring

theorem alg_split {q t X Y : ℝ} (ht : 0 < t) (hY : 0 < Y) (hXY : X * Y = t⁻¹) :
    1 / 2 * (2 * t⁻¹ * (1 - (q ^ 2)⁻¹)) * Y ^ 4 =
      (1 - (q ^ 2)⁻¹) * 1 * (t ^ 3)⁻¹ * (X ^ 3)⁻¹ * (t⁻¹ * Y) := by
  have hX : X = t⁻¹ / Y := (eq_div_iff hY.ne').2 hXY
  rw [hX]
  field_simp

theorem sq_eq_of_sq_eq {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ^ 2 = c ^ 2) : x = c :=
  (pow_left_inj₀ hx hc two_ne_zero).1 h

/-- **The predicted local factor** of the trace-zero lattice in terms of $|8|_v$, $|ab|_v$ and $|\det(\text{coordinates of }E)|_v$:
$(1 - q^{-2})\,\varepsilon\,|8|^{-1}|ab|^{-3}\,|\det|$, $\varepsilon = 2/(1 - q^{-1})$ if $D$ ramifies at $v$, else $1$. -/
def tzLoc (v : HeightOneSpectrum (𝓞 F)) (ram : Prop) [Decidable ram] (x8 xab xdet : ℝ) : ℝ :=
  (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * (if ram then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) *
    x8⁻¹ * (xab ^ 3)⁻¹ * xdet

set_option maxHeartbeats 1600000 in
/-- **The local factor of the trace-zero lattice at every finite place** (a local adapted basis $E$, any class number):
$$\tfrac12\beta_v(T, T)\,\|\det P\|^4 = (1-q^{-2})\,\varepsilon_v\,\|8\|^{-1}\|ab\|^{-3}\|\det(\text{coordinates of }E)\|.$$ -/
@[kb "voight2021" "§§13.3, 22.1 (local maximal orders); Kitaoka 1993, §5.6 [unverified]"]
theorem LTZ.localFactor_eq (L : LTZ v O) (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    {_inst : Decidable (v ∈ ramFin ha hb)} :
    (1 / 2 : ℝ) * DVR.localDensityForm (L.formT hO.1) (L.formT hO.1) (NF.π v) * ‖L.Pm.det‖ ^ 4 =
      tzLoc v (v ∈ ramFin ha hb) ‖(8 : Fv)‖ ‖algebraMap 𝔬 Fv (NF.ι v a) * algebraMap 𝔬 Fv (NF.ι v b)‖
        ‖L.coordV.det‖ := by
  have hπ := NF.irreducible_π v
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (DVR.q 𝔬 : ℝ) := ⟨_, rfl⟩
  have hqP : (normP v : ℝ) = q := by rw [hq, NF.q_completion]
  have hq2 : (2 : ℝ) ≤ q := by rw [← hqP]; exact_mod_cast two_le_normP v
  have hq0 : 0 < q := by linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ‖algebraMap 𝔬 Fv (NF.ι v a) * algebraMap 𝔬 Fv (NF.ι v b)‖ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ‖L.Pm.det‖ := ⟨_, rfl⟩
  rw [← hX, ← hY]
  have hX0 : 0 < X := by
    rw [hX]; exact norm_pos_iff.2 (mul_ne_zero
      ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (NF.ι_ne_zero v ha))
      ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (NF.ι_ne_zero v hb)))
  have hY0 : 0 < Y := by rw [hY]; exact norm_pos_iff.2 L.det_Pm_ne_zero
  have hcoord : ‖L.coordV.det‖ = ‖(L.E 0).re‖ * Y := by rw [L.det_coordV, norm_mul, hY]
  -- `|det H_T| = |8| X² Y²`
  have hdetH : ‖algebraMap 𝔬 Fv (L.formT hO.1).hessian.det‖ = ‖(8 : Fv)‖ * X ^ 2 * Y ^ 2 := by
    rw [L.det_hessian_formT hO.1, norm_mul, norm_pow, norm_mul, hX, hY, norm_mul]; ring
  -- the 2-adic valuation of 2
  obtain ⟨e, he, he'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (two_ne_zero : (2 : 𝔬) ≠ 0)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = ‖(2 : Fv)‖ := ⟨_, rfl⟩
  have ht : t = (q ^ e)⁻¹ := by
    have := norm_coe_of_pow_dvd v (x := (2 : 𝔬)) he he'
    rw [htdef, hq, ← this, show (2 : Fv) = algebraMap 𝔬 Fv 2 from (map_ofNat _ 2).symm]; rfl
  have ht0 : 0 < t := by rw [ht]; positivity
  have h8 : ‖(8 : Fv)‖ = t ^ 3 := by rw [show (8 : Fv) = 2 ^ 3 by norm_num, norm_pow, htdef]
  unfold tzLoc
  rw [h8, hcoord, hqP]
  have hrpow2 : q ^ (-(2 : ℝ)) = (q ^ 2)⁻¹ := by
    rw [Real.rpow_neg hq0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hrpow1 : q ^ (-(1 : ℝ)) = q⁻¹ := Real.rpow_neg_one q
  rw [hrpow2, hrpow1]
  have h2t : ‖algebraMap 𝔬 Fv 2‖ = t := by rw [map_ofNat, htdef]
  have hq1 : 1 < q := by linarith
  by_cases hv : v ∈ ramFin ha hb
  · rw [if_pos hv]
    by_cases h2 : NF.π v ∣ 2
    · -- ramified dyadic
      have he1 : 1 ≤ e := by
        by_contra h0; push Not at h0; interval_cases e; exact he' (by simpa using h2)
      obtain ⟨W, u, T, hWu, huu, hTu, haniso, hW, -⟩ := L.exists_GL_ramDyadic ha hb hO hv h2
      rw [localDensityForm_compMat_unit hWu hW,
        localDensityForm_ram_dyadic hπ two_ne_zero ⟨he, he'⟩ he1 huu T hTu haniso]
      have hρ : ‖(L.E 0).re‖ = t⁻¹ := by
        have h := L.norm_two_mul_re_ramDyadic ha hb hO hv h2
        rw [norm_mul, ← htdef] at h
        exact eq_inv_of_mul_eq_one_right h
      have hH := norm_det_hessian_of_compMat hWu hW
      have hsmul : (NF.π v • T).hessian = NF.π v • T.hessian := by
        ext i j; simp only [hessian, smul_coeff, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
          smul_eq_mul, mul_add]
      rw [hdetH, det_hessian_splitForm, hsmul, det_smul, Fintype.card_fin, map_mul, map_mul, map_mul, map_pow,
        norm_mul, norm_mul, norm_mul, norm_pow, norm_unit huu, norm_unit hTu, norm_pi, h2t, ← hq, h8] at hH
      have hXY : X * Y = t⁻¹ * q⁻¹ := by
        refine sq_eq_of_sq_eq (by positivity) (by positivity) ?_
        have ht3 : t ^ 3 ≠ 0 := by positivity
        calc (X * Y) ^ 2 = (t ^ 3 * X ^ 2 * Y ^ 2) / t ^ 3 := by field_simp
          _ = (t⁻¹ * q⁻¹) ^ 2 := by rw [hH]; field_simp
      have hqe : (DVR.q 𝔬 : ℝ) ^ e = t⁻¹ := by rw [← hq, ht, inv_inv]
      rw [show (4 : ℝ) * (DVR.q 𝔬 : ℝ) ^ (e + 2) * ((DVR.q 𝔬 : ℝ) + 1) = 4 * t⁻¹ * q ^ 2 * (q + 1) by
        rw [pow_add, hqe, ← hq]; ring, hρ]
      exact alg_ramDyadic hq1 ht0 hY0 hXY
    · -- odd ramified
      obtain ⟨W, u₀, u₁, u₂, hWu, h0, h1, hu2, haniso, hW⟩ := L.exists_GL_oddRam ha hb hO hv h2
      rw [localDensityForm_compMat_unit hWu hW, localDensityForm_odd_ram hπ h2 h0 h1 hu2 haniso]
      have hρ := L.norm_re_eq_one_of_odd hO.1 h2
      have ht1 : t = 1 := by rw [htdef]; exact norm_two_of_odd h2
      have hH := norm_det_hessian_of_compMat hWu hW
      have hHd : (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]).hessian.det = 4 * (NF.π v * u₁) * (NF.π v * u₂) := by
        simp [QuadForm.hessian, QuadForm.diag]; ring
      have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd hπ h2
      have h4u : IsUnit (4 : 𝔬) := by rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact h2u.mul h2u
      rw [hdetH, det_hessian_splitForm, hHd] at hH
      simp only [map_mul, norm_mul] at hH
      rw [norm_unit h0, norm_unit h1, norm_unit hu2, norm_unit h2u, norm_unit h4u, norm_pi, ← hq, h8, ht1] at hH
      have hXY : X * Y = q⁻¹ := by
        refine sq_eq_of_sq_eq (by positivity) (by positivity) ?_
        calc (X * Y) ^ 2 = 1 ^ 3 * X ^ 2 * Y ^ 2 := by ring
          _ = (q⁻¹) ^ 2 := by rw [hH]; ring
      rw [show (4 : ℝ) * (DVR.q 𝔬 : ℝ) ^ 2 * ((DVR.q 𝔬 : ℝ) + 1) = 4 * q ^ 2 * (q + 1) by rw [← hq], hρ, ht1]
      exact alg_oddRam hq1 hY0 hXY
  · -- split
    rw [if_neg hv]
    obtain ⟨φ, hφ⟩ := split_of_not_mem_ramFin_nf v ha hb hO hv
    obtain ⟨Yg, hYu, hYg⟩ := L.exists_GL_split φ hφ hO.1
    rw [localDensityForm_compMat_unit hYu hYg]
    have hsl : IsUnit (slT 𝔬).hessian.det := by rw [det_hessian_slT]; exact isUnit_one.neg
    have hβ : DVR.localDensityForm (splitForm (-1) (slT 𝔬)) (splitForm (-1) (slT 𝔬)) (NF.π v) =
        2 * t⁻¹ * (1 - (q ^ 2)⁻¹) := by
      by_cases h2 : NF.π v ∣ 2
      · have he1 : 1 ≤ e := by
          by_contra h0; push Not at h0; interval_cases e; exact he' (by simpa using h2)
        rw [localDensityForm_frame_dyadic hπ two_ne_zero ⟨he, he'⟩ he1 isUnit_one.neg (slT 𝔬) hsl, ht, inv_inv, hq]
      · classical
        have hdet : ¬ NF.π v ∣ (splitForm (-1 : 𝔬) (slT 𝔬)).hessian.det := by
          rw [det_hessian_splitForm, det_hessian_slT]
          intro h; exact h2 (by simpa using h)
        have := Fintype.ofFinite (IsLocalRing.ResidueField 𝔬)
        have h := DVR.localDensityForm_self_odd (NF.π v) 1 (splitForm (-1 : 𝔬) (slT 𝔬)) hπ h2 hdet
        have ht1 : t = 1 := by rw [htdef]; exact norm_two_of_odd h2
        rw [h, ht1, hq]
        simp
    rw [hβ]
    have hρ : ‖(L.E 0).re‖ = t⁻¹ := by
      have h := L.norm_two_mul_re_split φ hφ hO.1
      rw [norm_mul, ← htdef] at h
      exact eq_inv_of_mul_eq_one_right h
    have hH := norm_det_hessian_of_compMat hYu hYg
    rw [hdetH, det_hessian_splitForm, det_hessian_slT, h8, map_mul, map_mul, norm_mul, norm_mul, h2t] at hH
    simp only [map_neg, map_one, norm_neg, norm_one, mul_one] at hH
    have hXY : X * Y = t⁻¹ := by
      refine sq_eq_of_sq_eq (by positivity) (by positivity) ?_
      have ht3 : t ^ 3 ≠ 0 := by positivity
      calc (X * Y) ^ 2 = (t ^ 3 * X ^ 2 * Y ^ 2) / t ^ 3 := by field_simp
        _ = (t⁻¹) ^ 2 := by rw [hH]; field_simp
    rw [hρ]
    exact alg_split ht0 hY0 hXY

end Factor

end QuadFormsKB.QuatOrder
