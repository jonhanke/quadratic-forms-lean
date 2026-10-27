/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryCorollaries
import QuadFormsKB.Tamagawa.TernaryBadDVR

/-!
# The local factors of the trace-zero lattice at the split dyadic and odd ramified places

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, a finite place $v$, the completion $\mathfrak o_v \subset F_v$; a maximal order
$\mathcal O$ of $D = (a,b)_F$ with a trace-zero frame (`TZFrame`), $Q_0$ over $\mathcal O_F$ with $Q_0\otimes F = Q_{\mathcal O^0}$.

`TernaryTamagawaTwo F` is reduced to `TraceZeroBadLocalFactors F`: the value of $\alpha_v(Q_0, Q_0)$ (`tzFactor`) at every place
$v \mid 2$ and every $v \in \mathrm{Ram}_f(D)$. This file proves it at

* **split dyadic places** ($v \mid 2$, $v \notin \mathrm{Ram}_f$): $\mathcal O_v^0 \cong \mathfrak{sl}_2(\mathfrak o_v)$ with $\det$ *integrally*
  (`TZFrame.exists_GL_split`: $Q_0 \cong \langle -1\rangle\perp(-x_1x_2)$ over $\mathfrak o_v$), so the frame lemma gives
  $\alpha_v = q^e(1 - q^{-2})$, $e = \mathrm{ord}_v 2$ (`localDensityForm_frame_dyadic`); and $|\operatorname{re}e_0|_v = |2|_v^{-1}$ because the
  trace form of $M_2(\mathfrak o_v)$ is onto $\mathfrak o_v$ (`TZFrame.absV_two_mul_re_split`);
* **odd ramified places** ($v \nmid 2$, $v \in \mathrm{Ram}_f$): $\mathcal O_v^0 = \{x \in D_v^0 : \operatorname{nrd}x \in \mathfrak o_v\}$ is the unique maximal
  lattice of an anisotropic ternary space with square discriminant, so a Jordan splitting (`exists_diag_compMat`) has exponents
  $(0, 1, 1)$ and $Q_0 \cong \langle u_0\rangle\perp\varpi\langle u_1, u_2\rangle$ with $\langle\bar u_1, \bar u_2\rangle$ anisotropic
  (`TZFrame.exists_GL_oddRam`); `localDensityForm_odd_ram` gives $\alpha_v = 2q^2(q+1)$.

**Proves** `TZFrame.siegelDensity_split_dyadic`, `TZFrame.siegelDensity_odd_ram`, the reduction of the input to the ramified
dyadic places (`TraceZeroBadLocalFactors.of_ramDyadic`) and the headline `ternaryTamagawaTwo_of_ramDyadicLocalFactors`.

Sources: Voight 2021, §§13.3, 22.1 (local maximal orders) [unverified]; Kitaoka 1993, §5.6 [unverified]. Indices are 0-based.
-/

open NumberField IsDedekindDomain Matrix Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.LocalDensity
  QuadFormsKB.QuatZeta QuadFormsKB.HilbertModular QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]

/-! ### Glue: densities through an integral change of variables, and absolute values -/

section Glue

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\alpha_v(Q_0, Q_0) = \tfrac12\beta_\varpi(S, S)$ for any $S = (Q_0\otimes\mathfrak o_v)\circ W$, $W \in \mathrm{GL}_3(\mathfrak o_v)$. -/
theorem siegelDensity_eq_of_compMat {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (W : Matrix (Fin n) (Fin n) 𝔬)
    (hW : IsUnit W.det) {S : QuadForm 𝔬 n} (hS : (NF.Qp v Q₀).compMat W = S) :
    NF.siegelDensity v Q₀ Q₀ = 1 / 2 * DVR.localDensityForm S S (NF.π v) := by
  have hg : Siegel.IsometricGL (NF.Qp v Q₀) S :=
    ⟨((Matrix.isUnit_iff_isUnit_det W).2 hW).unit, fun x => by
      rw [← hS, eval_compMat]; rfl⟩
  simp only [NF.siegelDensity, ite_true]
  rw [NF.localDensityForm_eq_completion, DVR.localDensityForm_congr_left hg,
    DVR.localDensityForm_congr_right S hg]

/-- $|y|_v = q^{-e}$ for $y \in \mathcal O_F$ with $\varpi^e \,\|\, y$. -/
theorem absV_of_pow_dvd {y : 𝓞 F} {e : ℕ} (he : NF.π v ^ e ∣ NF.ι v y) (he' : ¬ NF.π v ^ (e + 1) ∣ NF.ι v y) :
    absV v (algebraMap (𝓞 F) F y) = ((normP v : ℝ) ^ e)⁻¹ := by
  show ‖((NF.ι v y : 𝔬) : Fv)‖ = _
  rw [norm_coe_of_pow_dvd v he he', NF.q_completion]

/-- The exact power of $\varpi$ dividing $2$. -/
theorem exists_ord_two : ∃ e : ℕ, NF.π v ^ e ∣ (2 : 𝔬) ∧ ¬ NF.π v ^ (e + 1) ∣ (2 : 𝔬) :=
  DVR.exists_pow_dvd_not_dvd (NF.π v) (NF.irreducible_π v) two_ne_zero

theorem absV_two_eq {e : ℕ} (he : NF.π v ^ e ∣ (2 : 𝔬)) (he' : ¬ NF.π v ^ (e + 1) ∣ (2 : 𝔬)) :
    absV v 2 = ((normP v : ℝ) ^ e)⁻¹ := by
  have := absV_of_pow_dvd v (y := 2) (by rwa [map_ofNat]) (by rwa [map_ofNat])
  rwa [map_ofNat] at this

theorem absV_eight_eq {e : ℕ} (he : NF.π v ^ e ∣ (2 : 𝔬)) (he' : ¬ NF.π v ^ (e + 1) ∣ (2 : 𝔬)) :
    absV v 8 = ((normP v : ℝ) ^ e)⁻¹ ^ 3 := by
  rw [show (8 : F) = 2 * 2 * 2 by norm_num, absV_mul, absV_mul, absV_two_eq v he he']; ring

theorem normP_pos : (0 : ℝ) < normP v := by
  have := two_le_normP v; exact_mod_cast (by omega : 0 < normP v)

theorem rpow_sq_neg_three_halves {X : ℝ} (hX : 0 < X) : (X ^ 2) ^ (-(3 / 2 : ℝ)) = (X ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX.le, show ((2 : ℕ) : ℝ) * -(3 / 2) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hX.le, Real.rpow_natCast]

theorem normP_rpow_neg_two : (normP v : ℝ) ^ (-(2 : ℝ)) = ((normP v : ℝ) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (normP_pos v).le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- $\varpi^e \,\|\, \iota(y)$ whenever $\iota(y)\,u = c$ for a unit $u$ and $\varpi^e \,\|\, c$. -/
theorem pow_dvd_of_mul_unit {x c u : 𝔬} (hu : IsUnit u) (h : x * u = c) {e : ℕ} (he : NF.π v ^ e ∣ c)
    (he' : ¬ NF.π v ^ (e + 1) ∣ c) : NF.π v ^ e ∣ x ∧ ¬ NF.π v ^ (e + 1) ∣ x := by
  obtain ⟨w, rfl⟩ := hu
  subst h
  exact ⟨(Units.dvd_mul_right).mp he, fun h' => he' ((Units.dvd_mul_right).mpr h')⟩

end Glue

/-! ### Split dyadic places -/

section SplitDyadic

variable {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The binary form $-x_0x_1$ (the off-diagonal part of $\det$ on $\mathfrak{sl}_2$). -/
def slT (A : Type*) [CommRing A] : QuadForm A 2 where
  coeff := !![0, -1; 0, 0]
  upper := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

theorem det_hessian_slT (A : Type*) [CommRing A] : (slT A).hessian.det = -1 := by
  simp [slT, QuadForm.hessian, Matrix.det_fin_two]

theorem map_splitForm_slT : (splitForm (-1 : 𝔬) (slT 𝔬)).map (algebraMap 𝔬 Fv) = detSlForm v := by
  ext i j
  simp only [QuadForm.map, Matrix.map_apply, splitForm_coeff]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [cornerMat_zero_zero, cornerMat_zero_succ, cornerMat_succ_zero, cornerMat_succ_succ]
  · simp [detSlForm]
  · fin_cases j <;> simp [detSlForm]
  · fin_cases i <;> simp [detSlForm]
  · fin_cases i <;> fin_cases j <;> simp [slT, detSlForm]

/-- **At a split place, $Q_0 \cong \langle -1\rangle\perp(-x_1x_2)$ over $\mathfrak o_v$** ($\mathcal O_v^0 \cong \mathfrak{sl}_2(\mathfrak o_v)$
integrally, every residue characteristic): the coordinates $Y$ of $\varphi^{-1}(h), \varphi^{-1}(e_{12}), \varphi^{-1}(e_{21})$ are
integral, carry $Q_0$ to $\det|_{\mathfrak{sl}_2}$, and $Y$ is invertible over $\mathfrak o_v$ because these three elements span
$\mathcal O_v^0$ (a trace-zero integral matrix is $\alpha h + \beta e_{12} + \gamma e_{21}$). -/
theorem TZFrame.exists_GL_split
    (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
      (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F))
    {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∃ Y : Matrix (Fin 3) (Fin 3) 𝔬, IsUnit Y.det ∧ (NF.Qp v Q₀).compMat Y = splitForm (-1) (slT 𝔬) := by
  set Hm : Matrix (Fin 2) (Fin 2) Fv := !![1, 0; 0, -1]
  set z : Fin 3 → QuatV v a b := ![φ.symm Hm, E12 v φ, E21 v φ]
  have hz : ∀ k, z k ∈ fr.Ov0 v := by
    intro k; fin_cases k
    · show φ.symm Hm ∈ fr.Ov0 v
      rw [fr.mem_Ov0_iff, mem_localOrder_iff_split v φ hφ, re_eq_zero_iff_trace v φ, AlgEquiv.apply_symm_apply]
      refine ⟨(mem_matOrder).2 fun i j => ?_, by simp [Hm, Matrix.trace_fin_two]⟩
      fin_cases i <;> fin_cases j
      · exact ⟨1, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨-1, by simp [Hm]⟩
    · exact E12_mem fr v φ hφ
    · exact E21_mem fr v φ hφ
  have hy : ∀ k, ∃ y, fr.psiv v y = z k := fun k => fr.exists_psiv_eq v ((fr.mem_Ov0_iff v _).1 (hz k)).2
  choose y hyz using hy
  have hyint : ∀ k r, IsLocalization.IsInteger 𝔬 (y k r) := by
    intro k r
    have h := ((fr.mem_Ov0_iff_repr v (fr.psiv v (y k))).1 (by rw [hyz]; exact hz k)).2 r
    rw [fr.repr_psiv] at h
    simpa using h
  choose c hc using hyint
  set Yo : Matrix (Fin 3) (Fin 3) 𝔬 := Matrix.of fun r k => c k r with hYo
  set Y := Yo.map (algebraMap 𝔬 Fv) with hY
  set Sv := fr.QF.map (algebraMap F Fv)
  have hSv : ∀ w, Sv.eval w = nrd (fr.psiv v w) := fun w => by
    rw [TZFrame.psiv, nrd_psiP]
    show (fr.QF.map (algebraMap F Fv)).eval w = _
    rw [TZFrame.QF, ← QuadForm.map_compMat, pureForm_map, TZFrame.PGv_val]; rfl
  have hYw : ∀ w : Fin 3 → Fv, Y *ᵥ w = ∑ k, w k • y k := by
    intro w; ext r
    simp [Y, Yo, mulVec, dotProduct, Finset.sum_apply, hc, mul_comm]
  have hlin : ∀ w : Fin 3 → Fv, fr.psiv v (∑ k, w k • y k) = ∑ k, w k • z k := by
    intro w
    rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hyz 0, ← hyz 1, ← hyz 2]
    simp only [TZFrame.psiv, psiP, mulVec_add, mulVec_smul, pure_add, pure_smul]
  have hval : ∀ w, (Sv.compMat Y).eval w = (detSlForm v).eval w := by
    intro w
    rw [eval_compMat, hSv, hYw, hlin, ← det_algEquiv φ, eval_detSlForm]
    simp only [Fin.sum_univ_three, map_add, map_smul, z, E12, E21, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, AlgEquiv.apply_symm_apply]
    simp [Hm, Matrix.det_fin_two]
    ring
  have hS : Sv.compMat Y = detSlForm v := eq_of_eval_eq hval
  -- psiv is injective
  have hinj : ∀ w w' : Fin 3 → Fv, fr.psiv v w = fr.psiv v w' → w = w' := by
    intro w w' h
    have h2 := congrArg (complBasis (v := v) fr.e fr.isOrder).repr h
    rw [fr.repr_psiv, fr.repr_psiv] at h2
    have h3 := congrArg (fun f => (Finsupp.equivFunOnFinite f : Fin 4 → Fv)) h2
    simp only [Equiv.apply_symm_apply] at h3
    funext i
    have := congrFun h3 i.succ
    simpa using this
  -- every standard basis vector is an integral combination of the columns of `Y`
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
    have hmem : fr.psiv v (Pi.single i 1) ∈ fr.Ov0 v := by
      rw [fr.psiv_mem_Ov0_iff]
      intro j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    obtain ⟨hloc, hre⟩ := (fr.mem_Ov0_iff v _).1 hmem
    rw [mem_localOrder_iff_split v φ hφ, mem_matOrder] at hloc
    rw [re_eq_zero_iff_trace v φ, Matrix.trace_fin_two] at hre
    obtain ⟨g00, hg00⟩ := hloc 0 0
    obtain ⟨g01, hg01⟩ := hloc 0 1
    obtain ⟨g10, hg10⟩ := hloc 1 0
    refine ⟨![g00, g01, g10], ?_⟩
    apply hinj
    rw [hYw, hlin]
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
    rw [← map_compMat, map_Qp_eq, hQ, map_splitForm_slT]
    exact hS

/-- **At a split place $|2\operatorname{re}e_0|_v = 1$**: $\varphi^{-1}(e_{11}) \in \mathcal O_v$ has reduced trace $1$, and its
reduced trace is $c_0\operatorname{trd}e_0$ with $c_0 \in \mathfrak o_v$ (the $e_0$-coordinate); and $\operatorname{trd}e_0 \in \mathcal O_F$. -/
theorem TZFrame.absV_two_mul_re_split
    (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
      (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    absV v (2 * (fr.e 0 : QuatF F a b).re) = 1 := by
  set ρ := (fr.e 0 : QuatF F a b).re
  set x : QuatV v a b := φ.symm (Matrix.single 0 0 1)
  have hx : x ∈ localOrder (v := v) a b O := by
    rw [mem_localOrder_iff_split v φ hφ, AlgEquiv.apply_symm_apply, mem_matOrder]
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Matrix.single_apply]; tauto⟩
  have htr : trd x = 1 := by
    rw [trd_eq_trace v φ, AlgEquiv.apply_symm_apply, Matrix.trace_fin_two]; simp
  obtain ⟨c, hc⟩ := (mem_localOrder_iff fr.e fr.isOrder x).1 hx 0
  have hre := fr.re_eq_repr v x
  rw [complHom_re] at hre
  have h1 : (algebraMap 𝔬 Fv c) * algebraMap F Fv (2 * ρ) = 1 := by
    rw [hc, map_mul, map_ofNat, ← htr, trd, hre]; ring
  have hle : ‖algebraMap 𝔬 Fv c‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2)
  have hge : 1 ≤ absV v (2 * ρ) := by
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 : absV v (2 * ρ) = ‖algebraMap F Fv (2 * ρ)‖ := rfl
    rw [h3]
    nlinarith [norm_nonneg (algebraMap 𝔬 Fv c), norm_nonneg (algebraMap F Fv (2 * ρ))]
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd fr.isOrder (fr.e 0).2).1
  have hle' : absV v (2 * ρ) ≤ 1 := by
    have := absV_int_le_one v t; rwa [ht, trd] at this
  exact le_antisymm hle' hge

/-- **The local factor at a split dyadic place** ($v \mid 2$, $v \notin \mathrm{Ram}_f$): $\alpha_v(Q_0, Q_0) = q^e(1 - q^{-2})$,
$q^e = |2|_v^{-1}$, which is `tzFactor` there: $|8|_v^{-1}|D'|_v^{-3/2}|\operatorname{re}e_0|_v = |2|_v^{-3}\cdot|2|_v^{3}\cdot|2|_v^{-1}$
($D' = \det H_{Q_0}/8$ with $\det H_{Q_0} \sim 2$). -/
theorem TZFrame.siegelDensity_split_dyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∉ ramFin ha hb) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) {_inst : Decidable (v ∈ ramFin ha hb)} :
    NF.siegelDensity v Q₀ Q₀ = tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re) := by
  obtain ⟨φ, hφ⟩ := split_of_not_mem_ramFin v ha hb hO hv
  obtain ⟨Y, hYu, hY⟩ := fr.exists_GL_split v φ hφ hQ
  obtain ⟨e, he, he'⟩ := exists_ord_two v
  have he1 : 1 ≤ e := by
    by_contra h0
    push Not at h0
    interval_cases e
    apply he'
    rw [zero_add, pow_one]
    have := (NF.π_pow_dvd_ι_iff v 1 2).2 (by rwa [pow_one])
    rwa [pow_one, map_ofNat] at this
  have hsl : IsUnit (slT 𝔬).hessian.det := by rw [det_hessian_slT]; exact isUnit_one.neg
  rw [siegelDensity_eq_of_compMat v Q₀ Y hYu hY,
    localDensityForm_frame_dyadic (NF.irreducible_π v) two_ne_zero ⟨he, he'⟩ he1 isUnit_one.neg (slT 𝔬) hsl]
  set X : ℝ := (normP v : ℝ) ^ e with hX
  have hX0 : 0 < X := pow_pos (normP_pos v) e
  have h2v := absV_two_eq v he he'
  rw [← hX] at h2v
  -- `|re e₀| = |2|⁻¹`
  have hρ : absV v (fr.e 0 : QuatF F a b).re = X := by
    have h := fr.absV_two_mul_re_split v φ hφ
    rw [absV_mul, h2v] at h
    field_simp at h
    linarith
  -- `|D'| = |2| / |8|`
  have hdet : NF.ι v Q₀.hessian.det * Y.det ^ 2 = 2 := by
    have h1 := congrArg Matrix.det (hessian_compMat (NF.Qp v Q₀) Y)
    rw [hY, det_hessian_splitForm, det_hessian_slT, det_mul, det_mul, det_transpose, NF.det_hessian_Qp] at h1
    linear_combination -h1
  obtain ⟨hde, hde'⟩ := pow_dvd_of_mul_unit v (hYu.pow 2) hdet he he'
  have hD : absV v (detHalf Q₀) = X ^ 2 := by
    rw [detHalf, absV_div, absV_of_pow_dvd v hde hde', absV_eight_eq v he he', ← hX]
    field_simp
  unfold tzFactor
  rw [if_neg hv, absV_eight_eq v he he', ← hX, hρ, hD, rpow_sq_neg_three_halves hX0, normP_rpow_neg_two,
    NF.q_completion]
  field_simp
  ring

end SplitDyadic

/-! ### Odd ramified places -/

section OddRam

variable {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem TZFrame.eval_QF_map (w : Fin 3 → Fv) : (fr.QF.map (algebraMap F Fv)).eval w = nrd (fr.psiv v w) := by
  rw [TZFrame.psiv, nrd_psiP]
  show (fr.QF.map (algebraMap F Fv)).eval w = _
  rw [TZFrame.QF, ← QuadForm.map_compMat, pureForm_map, TZFrame.PGv_val]; rfl

theorem TZFrame.psiv_injective : Function.Injective (fr.psiv v) := by
  intro w w' h
  have h2 := congrArg (complBasis (v := v) fr.e fr.isOrder).repr h
  rw [fr.repr_psiv, fr.repr_psiv] at h2
  have h3 := congrArg (fun f => (Finsupp.equivFunOnFinite f : Fin 4 → Fv)) h2
  simp only [Equiv.apply_symm_apply] at h3
  funext i
  have := congrFun h3 i.succ
  simpa using this

theorem TZFrame.re_psiv (y : Fin 3 → Fv) : (fr.psiv v y).re = 0 := by
  rw [fr.re_eq_repr, fr.repr_psiv]; simp

theorem TZFrame.psiv_zero : fr.psiv v 0 = 0 := by
  rw [TZFrame.psiv_eq]; exact Finset.sum_eq_zero fun l _ => by rw [Pi.zero_apply, zero_smul]

theorem TZFrame.eval_Qp_coe {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) (z : Fin 3 → 𝔬) :
    algebraMap 𝔬 Fv ((NF.Qp v Q₀).eval z) = (fr.QF.map (algebraMap F Fv)).eval (fun i => algebraMap 𝔬 Fv (z i)) := by
  rw [← hQ, ← map_Qp_eq, DVR.eval_map_comp']

/-- **$Q_0$ is anisotropic over $\mathfrak o_v$ at a ramified place** ($D_v$ is a division algebra). -/
theorem TZFrame.Qp_aniso (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) (z : Fin 3 → 𝔬) (hz : (NF.Qp v Q₀).eval z = 0) : z = 0 := by
  have h := fr.eval_Qp_coe v hQ z
  rw [hz, map_zero, fr.eval_QF_map] at h
  have h0 := hdiv _ h.symm
  have : (fun i => algebraMap 𝔬 Fv (z i)) = 0 := fr.psiv_injective v (by rw [h0, fr.psiv_zero])
  funext i
  exact IsFractionRing.injective 𝔬 Fv (by simpa using congrFun this i)

/-- **$\mathcal O_v^0$ is the maximal lattice at a ramified place:** if $Q_0(y) \in \mathfrak o_v$ for $y \in F_v^3$ then $y \in \mathfrak o_v^3$
($\mathcal O_v = \{x : \operatorname{nrd}x \in \mathfrak o_v\}$). -/
theorem TZFrame.isInteger_of_eval (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0)
    (heq : localOrder (v := v) a b O = valOrder (R := 𝔬) hdiv) (y : Fin 3 → Fv)
    (hy : IsLocalization.IsInteger 𝔬 ((fr.QF.map (algebraMap F Fv)).eval y)) :
    ∀ i, IsLocalization.IsInteger 𝔬 (y i) := by
  rw [fr.eval_QF_map] at hy
  have hmem : fr.psiv v y ∈ fr.Ov0 v := by
    rw [fr.mem_Ov0_iff, heq, mem_valOrder]; exact ⟨hy, fr.re_psiv v y⟩
  rw [fr.psiv_mem_Ov0_iff] at hmem
  intro i
  rw [isInteger_iff_le_one' v]
  have := hmem i
  simpa using this

theorem eval_smul_vec {A : Type*} [CommRing A] {n : ℕ} (Q : QuadForm A n) (c : A) (x : Fin n → A) :
    Q.eval (c • x) = c ^ 2 * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem diag_three_eq_splitForm {A : Type*} [CommRing A] (u₀ c₁ c₂ : A) :
    QuadForm.diag ![u₀, c₁, c₂] = splitForm u₀ (QuadForm.diag ![c₁, c₂]) := by
  ext i j
  simp only [splitForm_coeff, QuadForm.diag]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [cornerMat_zero_zero, cornerMat_zero_succ, cornerMat_succ_zero, cornerMat_succ_succ]
  · simp
  · simp [(Fin.succ_ne_zero j).symm]
  · simp [Fin.succ_ne_zero i]
  · fin_cases i <;> fin_cases j <;> simp

/-- $\langle d_0, d_1, d_2\rangle\circ P_\sigma = \langle d_{\sigma^{-1}(0)}, \dots\rangle$ for a permutation matrix. -/
theorem diag_compMat_perm {A : Type*} [CommRing A] (d : Fin 3 → A) (σ : Equiv.Perm (Fin 3)) :
    (QuadForm.diag d).compMat (σ.permMatrix A) = QuadForm.diag (d ∘ σ.symm) :=
  eq_of_eval_eq fun x => by
    rw [eval_compMat, PEquiv.toMatrix_toPEquiv_mulVec, eval_diag_gen, eval_diag_gen]
    rw [← Equiv.sum_comp σ.symm]
    simp

local notation "𝔽v" => IsLocalRing.ResidueField 𝔬
local notation "resv" => IsLocalRing.residue 𝔬

theorem pi_dvd_of_residue_eq_zero {x : 𝔬} (h : resv x = 0) : NF.π v ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, (NF.irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

/-- **Anisotropy of the binary part mod $\varpi$:** if $S\circ W = \langle u_0, \varpi u_1, \varpi u_2\rangle$ with $S$ anisotropic over
$\mathfrak o_v$ ($v \nmid 2$), then $\langle\bar u_1, \bar u_2\rangle$ is anisotropic over the residue field (else Hensel gives an
isotropic vector $(0, x, y)$). -/
theorem aniso_residue_of_diag (hodd : ¬ NF.π v ∣ 2) {S : QuadForm 𝔬 3} (hS : ∀ z, S.eval z = 0 → z = 0)
    {W : Matrix (Fin 3) (Fin 3) 𝔬} (hW : IsUnit W.det) {u₀ u₁ u₂ : 𝔬} (hu1 : IsUnit u₁) (hu2 : IsUnit u₂)
    (hSW : S.compMat W = QuadForm.diag ![u₀, NF.π v * u₁, NF.π v * u₂]) :
    ∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  have h1F : resv u₁ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu1
  have h2F : resv u₂ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu2
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
    apply pi_dvd_of_residue_eq_zero
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

/-- **A unimodular diagonal ternary form over $\mathfrak o_v$ ($v \nmid 2$) is isotropic** (Chevalley–Warning in the form
`FiniteField.exists_root_sum_quadratic`, then Hensel). -/
theorem exists_isotropic_unit_diag (hodd : ¬ NF.π v ∣ 2) {u₀ u₁ u₂ : 𝔬} (hu0 : IsUnit u₀) (hu1 : IsUnit u₁)
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
    apply pi_dvd_of_residue_eq_zero
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

theorem valued_pow_mul_unit {k : ℕ} {u : 𝔬} (hu : IsUnit u) :
    Valued.v (algebraMap 𝔬 Fv (NF.π v ^ k * u)) = WithZero.exp (-(k : ℤ)) := by
  show Valued.v (((NF.π v ^ k * u : 𝔬)) : Fv) = _
  push_cast
  rw [map_mul, map_pow, NF.valued_π, (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu,
    mul_one, ← WithZero.exp_nsmul]
  congr 1; simp

/-- **The Jordan shape of $\mathcal O_v^0$ at an odd ramified place:** $Q_0 \cong \langle u_0\rangle\perp\varpi\langle u_1, u_2\rangle$ over
$\mathfrak o_v$ with $u_i$ units and $\langle\bar u_1, \bar u_2\rangle$ anisotropic. *Proof:* diagonalize (`exists_diag_compMat`),
$d_i = \varpi^{k_i}u_i$. Maximality (`TZFrame.isInteger_of_eval`) gives $k_i \le 1$; anisotropy (`TZFrame.Qp_aniso`) excludes
$k = (0,0,0)$ (`exists_isotropic_unit_diag`); $d_0d_1d_2$ is a square in $F_v$ ($\det H_{Q_0} = 8(\det P\,ab)^2$), so $\sum k_i$ is even.
Hence $k$ is a permutation of $(0, 1, 1)$. -/
theorem TZFrame.exists_GL_oddRam (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W.det ∧ IsUnit u₀ ∧ IsUnit u₁ ∧ IsUnit u₂ ∧
      (∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
      (NF.Qp v Q₀).compMat W = splitForm u₀ (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]) := by
  have hdiv := hdiv_of_mem_ramFin v ha hb hv
  have heq := localOrder_eq_valOrder ha hb hO hdiv
  have hπ := NF.irreducible_π v
  have hodd : ¬ NF.π v ∣ 2 := by
    intro h; apply h2
    have := (NF.π_pow_dvd_ι_iff v 1 2).1 (by rw [pow_one, map_ofNat]; exact h)
    rwa [pow_one] at this
  set S := NF.Qp v Q₀ with hSdef
  have hQ0 : Q₀.Nondegenerate := by
    intro h0; apply fr.detHalf_ne_zero ha hb hQ; rw [detHalf, h0, map_zero, zero_div]
  have hSnd : S.Nondegenerate := NF.nondegenerate_Qp v hQ0
  have haniso : ∀ z, S.eval z = 0 → z = 0 := fr.Qp_aniso v hdiv hQ
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
        ((fr.QF.map (algebraMap F Fv)).eval ((algebraMap 𝔬 Fv (NF.π v))⁻¹ • x)) := by
      rw [eval_smul_vec, hx, ← fr.eval_Qp_coe v hQ, hevalW, hdu i]
      obtain ⟨j, hj⟩ : ∃ j, k i = j + 2 := ⟨k i - 2, by omega⟩
      refine ⟨NF.π v ^ j * u i, ?_⟩
      rw [hj, map_mul, map_mul, map_pow, map_pow]
      field_simp
      ring
    have hy := fr.isInteger_of_eval v hdiv heq _ hint
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
    obtain ⟨z, hz0, hz⟩ := exists_isotropic_unit_diag v hodd (hu 0) (hu 1) (hu 2)
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
    rw [hHd, hSdef, NF.det_hessian_Qp] at h1
    have h2' := fr.detHalf_eq hQ
    rw [detHalf] at h2'
    set r : F := fr.Pm.det * algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b with hr
    have hr0 : r ≠ 0 := by
      have := fr.detHalf_ne_zero ha hb hQ
      rw [fr.detHalf_eq hQ] at this
      intro h0; apply this; rw [show fr.Pm.det ^ 2 * (algebraMap (𝓞 F) F a) ^ 2 * (algebraMap (𝓞 F) F b) ^ 2 =
        r ^ 2 by rw [hr]; ring, h0]; ring
    have hdetF : algebraMap (𝓞 F) F Q₀.hessian.det = 8 * r ^ 2 := by
      rw [hr]; field_simp at h2'; linear_combination h2'
    have h3 := congrArg (algebraMap 𝔬 Fv) h1
    have hcomm : algebraMap 𝔬 Fv (NF.ι v Q₀.hessian.det) = algebraMap F Fv (algebraMap (𝓞 F) F Q₀.hessian.det) :=
      rfl
    simp only [map_mul] at h3
    rw [hcomm, hdetF] at h3
    simp only [map_mul, map_pow, map_ofNat] at h3
    set s : Fv := algebraMap 𝔬 Fv W.det * algebraMap F Fv r with hs
    have hs0 : s ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hWu.ne_zero)
      ((map_ne_zero _).mpr hr0)
    have h8 : (8 : Fv) ≠ 0 := by
      have : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
      rw [show (8 : Fv) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero this this) this
    have h4 : algebraMap 𝔬 Fv (d 0 * d 1 * d 2) = s ^ 2 := by
      apply mul_left_cancel₀ h8
      simp only [map_mul, hs]; linear_combination h3
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hs0
    have h5 := congrArg Valued.v h4
    rw [map_pow, hm, hdu 0, hdu 1, hdu 2, show NF.π v ^ k 0 * u 0 * (NF.π v ^ k 1 * u 1) * (NF.π v ^ k 2 * u 2) =
      NF.π v ^ (k 0 + k 1 + k 2) * (u 0 * u 1 * u 2) by ring, valued_pow_mul_unit v ((hu 0).mul (hu 1) |>.mul (hu 2)),
      ← WithZero.exp_nsmul, WithZero.exp_inj] at h5
    exact ⟨Int.toNat (-m), by simp at h5; omega⟩
  -- (4) conclude
  have fin : ∀ (W' : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W'.det → IsUnit u₀ → IsUnit u₁ →
      IsUnit u₂ → S.compMat W' = QuadForm.diag ![u₀, NF.π v * u₁, NF.π v * u₂] →
      ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u₀ u₁ u₂ : 𝔬), IsUnit W.det ∧ IsUnit u₀ ∧ IsUnit u₁ ∧ IsUnit u₂ ∧
        (∀ x y : 𝔽v, resv u₁ * x ^ 2 + resv u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
        S.compMat W = splitForm u₀ (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]) :=
    fun W' u₀ u₁ u₂ hW' h0 h1 h2 hS' => ⟨W', u₀, u₁, u₂, hW', h0, h1, h2,
      aniso_residue_of_diag v hodd haniso hW' h1 h2 hS', by rw [hS', diag_three_eq_splitForm]⟩
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

/-- **The local factor at an odd ramified place** ($v \nmid 2$, $v \in \mathrm{Ram}_f$): $\alpha_v(Q_0, Q_0) = 2q^2(q+1)$, which is
`tzFactor` there: $(1 - q^{-2})\cdot\frac{2}{1 - q^{-1}}\cdot|D'|_v^{-3/2} = 2(1 + q^{-1})q^3$ with $|D'|_v = q^{-2}$ ($\det H_{Q_0} \sim 8u_0u_1u_2\varpi^2$),
$|8|_v = |\operatorname{re}e_0|_v = 1$. -/
theorem TZFrame.siegelDensity_odd_ram (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) {_inst : Decidable (v ∈ ramFin ha hb)} :
    NF.siegelDensity v Q₀ Q₀ = tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re) := by
  obtain ⟨W, u₀, u₁, u₂, hWu, h0, h1, hu2, haniso, hW⟩ := fr.exists_GL_oddRam v ha hb hO hv h2 hQ
  have hπ := NF.irreducible_π v
  have hodd : ¬ NF.π v ∣ 2 := by
    intro h; apply h2
    have := (NF.π_pow_dvd_ι_iff v 1 2).1 (by rw [pow_one, map_ofNat]; exact h)
    rwa [pow_one] at this
  rw [siegelDensity_eq_of_compMat v Q₀ W hWu hW, localDensityForm_odd_ram hπ hodd h0 h1 hu2 haniso]
  have hdet : NF.ι v Q₀.hessian.det * W.det ^ 2 = NF.π v ^ 2 * (8 * (u₀ * u₁ * u₂)) := by
    have h1' := congrArg Matrix.det (hessian_compMat (NF.Qp v Q₀) W)
    rw [hW, det_hessian_splitForm, det_mul, det_mul, det_transpose, NF.det_hessian_Qp] at h1'
    have hH : (QuadForm.diag ![NF.π v * u₁, NF.π v * u₂]).hessian.det = 4 * (NF.π v * u₁) * (NF.π v * u₂) := by
      simp [QuadForm.hessian, QuadForm.diag]; ring
    rw [hH] at h1'
    linear_combination -h1'
  have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd hπ hodd
  have h8u : IsUnit (8 * (u₀ * u₁ * u₂) : 𝔬) := by
    rw [show (8 : 𝔬) = 2 * 2 * 2 by norm_num]; exact ((h2u.mul h2u).mul h2u).mul ((h0.mul h1).mul hu2)
  have hc2 : NF.π v ^ 2 ∣ NF.π v ^ 2 * (8 * (u₀ * u₁ * u₂)) := dvd_mul_right _ _
  have hc3 : ¬ NF.π v ^ (2 + 1) ∣ NF.π v ^ 2 * (8 * (u₀ * u₁ * u₂)) := by
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)]
    exact DVR.dvr_not_dvd_of_isUnit hπ h8u
  obtain ⟨hde, hde'⟩ := pow_dvd_of_mul_unit v (hWu.pow 2) hdet hc2 hc3
  have hq := normP_pos v
  have hD : absV v (detHalf Q₀) = ((normP v : ℝ)⁻¹) ^ 2 := by
    rw [detHalf, absV_div, absV_of_pow_dvd v hde hde', absV_eight v h2, inv_pow]; simp
  unfold tzFactor
  rw [if_pos hv, absV_eight v h2, fr.absV_re_eq_one v h2, hD, rpow_sq_neg_three_halves (inv_pos.mpr hq),
    normP_rpow_neg_two, Real.rpow_neg_one, NF.q_completion]
  have hq1 : (normP v : ℝ)⁻¹ < 1 := by
    have := two_le_normP v
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < normP v))
  have hne : 1 - (normP v : ℝ)⁻¹ ≠ 0 := by linarith
  have hq2 : (2 : ℝ) ≤ normP v := by exact_mod_cast two_le_normP v
  have hne2 : (normP v : ℝ) - 1 ≠ 0 := by linarith
  rw [show 1 - (normP v : ℝ)⁻¹ = ((normP v : ℝ) - 1) / normP v by field_simp]
  field_simp
  ring

end OddRam

/-! ### Reduction of the input to the ramified dyadic places -/

section Reduction

open Classical in
/-- **Input: the local densities of the trace-zero lattice at the ramified dyadic places.** As `TraceZeroBadLocalFactors`,
but only for finite places $v$ with $v \mid 2$ **and** $v \in \mathrm{Ram}_f(D)$:
$$\alpha_v(Q_0, Q_0) = (1-q_v^{-2})\cdot\frac{2}{1-q_v^{-1}}\cdot|8|_v^{-1}\,|\det\tfrac12H_{Q_0}|_v^{-3/2}\,|\operatorname{re}e_0|_v.$$

Field:
- `factor`: the displayed identity (`tzFactor` with the ramified flag) at every ramified dyadic place.

*Hypothesis hygiene.* A statement about the trace-zero part of the valuation ring of the dyadic quaternion division algebra
$D_v$ only (one local lattice up to isometry for each dyadic completion of $F$); it is not the global conclusion. The other
places are proved: odd split (`TZFrame.siegelDensity_odd_split`), split dyadic (`TZFrame.siegelDensity_split_dyadic`),
odd ramified (`TZFrame.siegelDensity_odd_ram`). For $F = \mathbb Q$ it is one statement, at $p = 2$ for algebras ramified at $2$
(e.g. Hamilton's quaternions). -/
@[kb "voight2021" "§§13.3, 22.1 (the maximal order of the dyadic division algebra) [unverified]; Weil 1982, §3.7(a)"]
structure TraceZeroRamDyadicLocalFactors (F : Type) [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] : Prop where
  factor : ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ (O : Subalgebra (𝓞 F) (QuatF F a b)), IsMaximalOrder (𝓞 F) F O → ∀ (fr : TZFrame O) (Q₀ : QuadForm (𝓞 F) 3),
      Q₀.map (algebraMap (𝓞 F) F) = fr.QF → ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal →
        v ∈ ramFin ha hb →
        LocalDensity.NF.siegelDensity v Q₀ Q₀ =
          tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re)

/-- **The input from the ramified dyadic places only** (the split dyadic and odd ramified places are proved here). -/
theorem TraceZeroBadLocalFactors.of_ramDyadic (I : TraceZeroRamDyadicLocalFactors F) :
    TraceZeroBadLocalFactors F := by
  classical
  refine ⟨fun a b ha hb hdef O hO fr Q₀ hQ v hbad => ?_⟩
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  · by_cases hv : v ∈ ramFin ha hb
    · exact I.factor a b ha hb hdef O hO fr Q₀ hQ v h2 hv
    · exact fr.siegelDensity_split_dyadic v ha hb hO hv h2 hQ
  · have hv : v ∈ ramFin ha hb := hbad.resolve_left h2
    exact fr.siegelDensity_odd_ram v ha hb hO hv h2 hQ

/-- **`TernaryTamagawaTwo F` from the ramified dyadic local factors only** ($F$ totally real, $\mathcal O_F$ a PID, $F = \mathbb Q$
included). -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65"]
theorem ternaryTamagawaTwo_of_ramDyadicLocalFactors [IsTotallyReal F] (I : TraceZeroRamDyadicLocalFactors F) :
    TernaryTamagawaTwo F :=
  ternaryTamagawaTwo_of_badLocalFactors (TraceZeroBadLocalFactors.of_ramDyadic I)

end Reduction

end QuadFormsKB.QuatOrder

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.QuatOrder

section NFRamDyadic

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **$\tau(SO(Q_0)) = 2$ in every rank $N \ge 3$ from the ramified dyadic local factors** ($[F:\mathbb Q] \ge 2$, $\mathcal O_F$ a PID). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; §3.7, Thm 3.7.1, p. 65"]
theorem tamagawaNumberTwo_all_ranks_of_ramDyadic (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroRamDyadicLocalFactors F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_traceZero hd (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 3$ from the ramified dyadic local factors.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem massFormula_all_ranks_of_ramDyadic (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroRamDyadicLocalFactors F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_traceZero hd (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q₀ hpd

/-- **Siegel's formula in every rank $N \ge 4$ from the ramified dyadic local factors.** -/
@[kb "weil1982" "§4.5, p. 100, Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_all_ranks_of_ramDyadic (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (I : TraceZeroRamDyadicLocalFactors F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_of_traceZero hd (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q₀ hpd hm

end NFRamDyadic

section RatRamDyadic

/-- **$\tau(SO) = 2$ over $\mathbb Q$ in every rank $N \ge 3$ from the local factor at $2$ of algebras ramified at $2$.** -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 and Thm. 3.7.1, p. 65, over ℚ"]
theorem tamagawaNumberTwo_rat_all_ranks_of_ramDyadic (I : TraceZeroRamDyadicLocalFactors ℚ) {N : ℕ} (hN : 3 ≤ N)
    (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_rat_all_ranks_of_traceZero (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q₀ hpd

/-- **Siegel's formula over $\mathbb Q$ in every rank $N \ge 4$ from the local factor at $2$.** -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every rank ≥ 4 [unverified]"]
theorem siegelFormulaAt_rat_all_ranks_of_ramDyadic (I : TraceZeroRamDyadicLocalFactors ℚ) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_rat_all_ranks_of_traceZero (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q₀ hpd hm

/-- **Hanke's Siegel formula over $\mathbb Z$ in every rank $N \ge 4$ from the local factor at $2$.** -/
@[kb "siegel1935" "Hauptsatz, every rank ≥ 4, Hanke's (5.3) form over ℤ [unverified]"]
theorem siegelFormula_int_all_ranks_of_ramDyadic (I : TraceZeroRamDyadicLocalFactors ℚ) {N : ℕ} (hN : 4 ≤ N)
    (Q : QuadForm ℤ N) (hQ : IntQF.PosDef Q) : Siegel.SiegelFormula Q :=
  siegelFormula_int_all_ranks_of_traceZero (TraceZeroBadLocalFactors.of_ramDyadic I) hN Q hQ

end RatRamDyadic

end QuadFormsKB.Tamagawa
