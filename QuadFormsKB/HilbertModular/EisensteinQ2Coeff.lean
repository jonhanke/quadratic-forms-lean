/-
# The Fourier coefficients of the weight-2 Eisenstein series of the genus

**Setting.** $F$ totally real of degree $d \ge 2$, $\mathcal O = \mathcal O_F$, $\mathfrak N \ne 0$, $f$ with constant terms at every cusp
(`HasCuspLimits f 2`) and the $\Gamma_0(\mathfrak N)$-law with a character $\chi$. The $E^{(2)}_f$ (`eisGen2`) is the finite combination
$\sum_C\sum_ra_r\,E_2(\cdot; \Phi_{C,\mathfrak d_r})$ of weight-2 series of the periodic weights $\Phi_{C,\mathfrak d}$ (`eisWt2`), with the
Möbius coefficients $a_r = \sum_{S:\kappa(\mathfrak d_S) = r}(-1)^{|S|}N(\lambda_S)^{-2}$.

**Main results.**
* `eis2_eisWt2_sqf`: $E_2(\cdot; \Phi_{C,\mathfrak d_S}) = N(\lambda_S)^{-2}E_2(\cdot; \Phi_{C,\mathfrak d_{\kappa(\mathfrak d_S)}})$ (Hecke's limit $s \to 0^+$ of
  the scaling, `heckeSeries_scaleWeight`), so $E^{(2)}_f = \sum_C\sum_S(-1)^{|S|}E_2(\cdot; \Phi_{C,\mathfrak d_S})$
  coefficientwise.
* `summable_rowCo_moebius` (**absolute convergence**): for $\mu \in \mathfrak d^{-1}\setminus 0$ the row coefficients
  $(S, t) \mapsto \rho_{\Phi_{C,\mathfrak d_S}}(t, \mu)$ are absolutely summable: $|\rho| \le K\,|N(c)|^{-1}N(\mathfrak b\mathfrak d_S)^{-1}$, nonzero only
  if $(c) = \mathfrak b\mathfrak d_S\mathfrak e$ with $\mathfrak e \mid \mu\mathfrak N\mathfrak d$, so $|\rho| \le K'N(\mathfrak d_S)^{-2}N(\mathfrak e)^{-2}$.
* `hasSum_rowCo_moebius` (**Möbius inversion in each row**): $\sum_S(-1)^{|S|}\rho_{\Phi_{C,\mathfrak d_S}}(t, \mu)
  = c_{\mathcal O}\Lambda_2(\mu)|N(c)|^{-1}\cdot\frac1{N(M)}\sum_{r\in\mathcal O/M}[\mathfrak b(c, \tilde r) = \mathfrak b_C]\varphi_f(c, \tilde r)e(\operatorname{Tr}\mu\tilde r/c)$.
* **`qCoeff_eisGen2`**: $a_\mu(E^{(2)}_f) = \sum_C\sum_{t\in U\backslash F}R_C(t, \mu)$, absolutely convergent, with $R_C$ the Möbius-inverted row
  coefficient (`rowRed`).
* For $f = \theta_{\mathrm{Gen}}$ (`qCoeff_eisQ2`): $R_C(t, \mu) = C_Q\,c_{\mathcal O}\,\Lambda_2(\mu)\,A_{C,t}(\mu)$ with $A_{C,t}$ the row part of
  the singular series (`SingularNF.ssPart`), hence
  $$a_\mu(E_Q) = C_Q\,c_{\mathcal O}\,\Lambda_2(\mu)\sum_{(C,t)}A_{C,t}(\mu),\qquad \sum_{(C,t)}|A_{C,t}(\mu)| < \infty\ (\mu \gg 0).$$

Sources: Hecke (1927) [unverified]; Siegel (1935), §§3–5 [unverified]; Shimura, Duke Math. J. 45 (1978), §3 [unverified]. Over
$\mathbb Q$: `Siegel.GenusEis.hasSum_eisQCoeff`.
-/
import QuadFormsKB.SiegelWeil.SingularSeriesNF2

open Complex Matrix NumberField UpperHalfPlane Filter Topology IsDedekindDomain
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

open SiegelWeil.SingularNF (eTr eTr_add eTr_of_mem eTr_eq_one_iff)

section Generic

variable {f : (InfinitePlace F → ℍ) → ℂ} {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}

/-- **Translation invariance of $\Phi_{C,\mathfrak d}$**: $\Phi(c, d + cb) = \Phi(c, d)$ for $b \in \mathcal O$ (the $\Gamma_0(\mathfrak N)$-law for
$\begin{pmatrix}1&b\\0&1\end{pmatrix}$, $\chi(1) = 1$). -/
lemma eisWt2_add_mul (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (𝔡 : Ideal (𝓞 F)) (c d : F) (b : 𝓞 F) :
    eisWt2 f 𝔑 C 𝔡 (c, d + c * ιO b) = eisWt2 f 𝔑 C 𝔡 (c, d) := by
  have hγ : translO b ∈ Gamma0R 𝔑 := by
    rw [mem_Gamma0R]; simp [translO]
  have h := congrFun (slashWeight_eisWt2 hf hfχ C 𝔡 hγ) (c, d + c * ιO b)
  have h11 : (translO b : SL(2, 𝓞 F)) 1 1 = 1 := by simp [translO]
  rw [h11, map_one, MulChar.map_one, one_smul] at h
  rw [← h, slashWeight]
  obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply (toF F (translO b))
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [rowMul_fst, i0, i2, toF_apply]; simp [translO]
  · simp only [rowMul_snd, i1, i3, toF_apply]; simp [translO]


lemma sqfLevel_ne_bot (h𝔑 : 𝔑 ≠ ⊥) (C : ClassGroup (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    𝔑 * repIdeal C * sqfIdeal S ≠ ⊥ :=
  mul_ne_zero (mul_ne_zero h𝔑 (repIdeal_ne_bot C)) (sqfIdeal_ne_bot S)

lemma tendsto_prod_abs_rpow (l : F) (hl : l ≠ 0) :
    Tendsto (fun s : ℝ => ∏ v, ((|realEmb F v l| ^ (-2 * s) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun s : ℝ => ∏ v, ((|realEmb F v l| ^ (-2 * s) : ℝ) : ℂ)) (𝓝 0)
      (𝓝 (∏ v : InfinitePlace F, ((|realEmb F v l| ^ (-2 * (0 : ℝ)) : ℝ) : ℂ))) := by
    refine tendsto_finsetProd _ fun v _ => ?_
    have hv : |realEmb F v l| ≠ 0 :=
      abs_ne_zero.mpr ((map_ne_zero_iff _ (realEmb_injective F v)).mpr hl)
    have hc : Continuous fun s : ℝ => |realEmb F v l| ^ (-2 * s) :=
      (Real.continuous_const_rpow hv).comp (continuous_const.mul continuous_id)
    exact (Complex.continuous_ofReal.comp hc).tendsto 0
  simp only [mul_zero, Real.rpow_zero, Complex.ofReal_one, Finset.prod_const_one] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Within a ray class the weight-2 series scale**: $E_2(\cdot; \Phi_{C,\mathfrak d_S}) = N(\lambda_S)^{-2}\,E_2(\cdot; \Phi_{C,\mathfrak d_r})$,
$r = \kappa(\mathfrak d_S)$ ($d \ge 2$; Hecke's limit of `heckeSeries_scaleWeight`, the factor $\prod_v|\sigma_v(\lambda_S)|^{-2s} \to 1$). -/
@[kb "hecke1927" "weight-2 series within a ray class differ by N(λ)^{-2} (Hecke's limit) [unverified]"]
theorem eis2_eisWt2_sqf (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (z : InfinitePlace F → ℍ) :
    eis2 (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) z =
      (∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ (-(2 : ℤ)) *
        eis2 (eisWt2 f 𝔑 C (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S))))
          (𝔑 * repIdeal C * keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S))) (keyLevel_ne_bot h𝔑 C _) z := by
  have hW1 := intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)
  have hW2 := intWeight_eisWt2 h𝔑 hf hfχ C (keyRep_ne_bot 𝔑 (rayKey 𝔑 (sqfIdeal S)))
  obtain ⟨hl, he, hc⟩ := (exists_keyScale 𝔑 S).choose_spec
  have hscale := eisWt2_eq_scale hf hfχ C hl he hc
  have t1 := tendsto_heckeSeries_two hd hW1 z
  have t2 := tendsto_heckeSeries_two hd hW2 z
  have heq : (fun s => heckeSeries (eisWt2 f 𝔑 C (sqfIdeal S)) 2 s z) = fun s =>
      ((∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ 2)⁻¹ *
        (∏ v, ((|realEmb F v (keyScale 𝔑 S)| ^ (-2 * s) : ℝ) : ℂ)) *
          heckeSeries (eisWt2 f 𝔑 C (keyRep 𝔑 (rayKey 𝔑 (sqfIdeal S)))) 2 s z := by
    funext s
    rw [hscale, heckeSeries_scaleWeight hW2.unit]
    rfl
  have t3 := ((tendsto_const_nhds (x := ((∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ 2)⁻¹)).mul
    (tendsto_prod_abs_rpow (keyScale 𝔑 S) (keyScale_ne_zero 𝔑 S))).mul t2
  rw [← heq, mul_one] at t3
  rw [tendsto_nhds_unique t1 t3, _root_.zpow_neg, zpow_ofNat]


/-! ### Möbius inversion in each row -/

open Classical in
/-- The numerator $c' \in \mathcal O$ of an integral row $\tilde t = \iota(c')$ (junk value $1$ otherwise). -/
noncomputable def rowNum (t : UOrbitF F) : 𝓞 F :=
  if h : ∃ c' : 𝓞 F, ιO c' = crep t then h.choose else 1

lemma rowNum_spec {t : UOrbitF F} (h : ∃ c' : 𝓞 F, ιO c' = crep t) : ιO (rowNum t) = crep t := by
  classical
  rw [rowNum, dif_pos h]; exact h.choose_spec

variable (f 𝔑) in
open Classical in
/-- **The Möbius-inverted row coefficient** of class $C$:
$R_C(t, \mu) = c_{\mathcal O}\Lambda_2(\mu)|N(c)|^{-1}\cdot\frac1{N(M)}\sum_{r\in\mathcal O/M}[\mathfrak b(c, \tilde r) = \mathfrak b_C]\,\varphi_f(c, \tilde r)\,
e(\operatorname{Tr}\mu\tilde r/c)$ for an integral row $c = \tilde t = \iota(c') \ne 0$, $M = \mathfrak N c'$ (`redPart`), and $0$ for the other rows.
Parameters: `f`, `𝔑` (level), `C` (class), `t` (row), `μ` (frequency). -/
@[kb "hecke1927" "Möbius-inverted row coefficients of the weight-2 Eisenstein series [unverified]"]
noncomputable def rowRed (C : ClassGroup (𝓞 F)) (t : UOrbitF F) (μ : F) : ℂ :=
  if t.out ≠ 0 ∧ ∃ c' : 𝓞 F, ιO c' = crep t then
    (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) * ((absNorm (crep t) : ℝ) : ℂ)⁻¹ *
      rowAvg (redPart f C) (𝔑 * Ideal.span {rowNum t}) (crep t) μ
  else 0

lemma eisWt2_eq_zero_of_not_mem (C : ClassGroup (𝓞 F)) (𝔡 : Ideal (𝓞 F)) {c d : F}
    (h : c ∉ ((repIdeal C * 𝔡 : Ideal (𝓞 F)) : FI)) : eisWt2 f 𝔑 C 𝔡 (c, d) = 0 := by
  rw [eisWt2, cutWeight_of_not_le]
  intro h'
  exact h (cuspIdeal_le_iff.mp h').1

/-- **Möbius inversion of the row coefficients**: for $\mu \in \mathfrak d^{-1}$ and every row $t$,
$\sum_S(-1)^{|S|}\rho_{\Phi_{C,\mathfrak d_S}}(t, \mu) = R_C(t, \mu)$ (`rowRed`). In the row $c = \tilde t$ all the weights $\Phi_{C,\mathfrak d_S}$ are
averaged over the common modulus $M = \mathfrak N c'$ (`rowCo_eq`), and $\sum_S(-1)^{|S|}\Phi_{C,\mathfrak d_S}(y) = [\mathfrak b(y) = \mathfrak b_C]\varphi_f(y)$
(`hasSum_moebius_eisWt2`). -/
@[kb "hecke1927" "Möbius inversion of the row coefficients [unverified]"]
theorem hasSum_rowCo_moebius (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {μ : F} (hμ : μ ∈ invDifferent F) (t : UOrbitF F) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (-1 : ℂ) ^ S.card *
      rowCo (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) t μ)
      (rowRed f 𝔑 C t μ) := by
  classical
  by_cases ht : t.out = 0
  · rw [rowRed, if_neg (fun h => h.1 ht)]
    simp only [rowCo_of_out_eq_zero _ _ _ ht, mul_zero]
    exact hasSum_zero
  by_cases hint : ∃ c' : 𝓞 F, ιO c' = crep t
  swap
  · rw [rowRed, if_neg (fun h => hint h.2)]
    have h0 : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), rowCo (eisWt2 f 𝔑 C (sqfIdeal S))
        (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) t μ = 0 := by
      intro S
      refine rowCo_of_row_eq_zero _ _ _ (fun d => ?_) μ
      by_contra hW0
      obtain ⟨q, hq⟩ := (intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)).supp _ hW0
      exact hint ⟨q.1, congrArg Prod.fst hq⟩
    simp only [h0, mul_zero]
    exact hasSum_zero
  rw [rowRed, if_pos ⟨ht, hint⟩]
  set c := crep t
  set c' := rowNum t
  have hc' : ιO c' = c := rowNum_spec hint
  have hc : c ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
  have hc'0 : c' ≠ 0 := by rintro h; rw [h, map_zero] at hc'; exact hc hc'.symm
  set M := 𝔑 * Ideal.span {c'}
  have hM : M ≠ ⊥ := mul_ne_zero h𝔑 (SiegelWeil.SingularNF.span_ne_bot hc'0)
  have hμM : ∀ m ∈ M, eTr (μ * ιO m / c) = 1 := by
    intro m hm
    obtain ⟨n, -, rfl⟩ := Ideal.mem_mul_span_singleton.mp hm
    apply eTr_of_mem
    rw [map_mul, hc', show μ * (ιO n * c) / c = ιO n * μ by field_simp]
    exact algebraMap_mul_mem_invDifferent n hμ
  set K : ℂ := (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) * ((absNorm c : ℝ) : ℂ)⁻¹
  -- each row coefficient is `K` times the average over `M`
  have hrow : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), rowCo (eisWt2 f 𝔑 C (sqfIdeal S))
      (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) t μ =
        K * rowAvg (eisWt2 f 𝔑 C (sqfIdeal S)) M c μ := by
    intro S
    by_cases hmem : c' ∈ repIdeal C * sqfIdeal S
    · have hle : M ≤ 𝔑 * repIdeal C * sqfIdeal S := by
        rw [mul_assoc]
        exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      exact rowCo_eq (intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)) ht hM hle hμM
    · have hnot : c ∉ ((repIdeal C * sqfIdeal S : Ideal (𝓞 F)) : FI) := by
        intro h
        obtain ⟨a, ha, ha'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h
        rw [← hc'] at ha'
        exact hmem (FaithfulSMul.algebraMap_injective (𝓞 F) F ha' ▸ ha)
      rw [rowCo_of_row_eq_zero _ _ _ (fun d => eisWt2_eq_zero_of_not_mem C _ hnot) μ, rowAvg]
      simp [eisWt2_eq_zero_of_not_mem C _ hnot]
  simp_rw [hrow]
  -- Möbius inversion under the finite sum
  haveI := SiegelWeil.SingularNF.finite_quot hM
  letI : Fintype (𝓞 F ⧸ M) := Fintype.ofFinite _
  have hsum : HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (-1 : ℂ) ^ S.card *
      rowAvg (eisWt2 f 𝔑 C (sqfIdeal S)) M c μ) (rowAvg (redPart f C) M c μ) := by
    simp only [rowAvg, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine hasSum_sum fun r _ => ?_
    have h := (hasSum_moebius_eisWt2 hf hfχ C (y := (c, ιO (Quotient.out r))) (Or.inl hc)).mul_right
      (((Ideal.absNorm M : ℂ))⁻¹ * eTr (μ * ιO (Quotient.out r) / c))
    convert h using 1
    · funext S; ring
    · ring
  convert hsum.mul_left K using 1
  funext S; ring


/-! ### Absolute convergence over $(S, t)$ -/

/-- **The denominator bound**: if $(c) = \mathfrak a\mathfrak e$ (integral $\mathfrak a, \mathfrak e \ne 0$) and $\mu\,c^{-1}\mathfrak N\mathfrak a \subseteq \mathfrak d^{-1}$
($\mu \in \mathfrak d^{-1}\setminus0$), then $\mathfrak e \supseteq \mu\mathfrak N\mathfrak d$, so $N(\mathfrak e) \le N(\mu\mathfrak N\mathfrak d)$. -/
lemma absNorm_le_of_rowCond (h𝔑 : 𝔑 ≠ ⊥) {μ : F} (hμ0 : μ ≠ 0) {𝔞 𝔢 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥)
    (h𝔢 : 𝔢 ≠ ⊥) {c : F} (hc : FractionalIdeal.spanSingleton (𝓞 F)⁰ c = (𝔞 : FI) * (𝔢 : FI))
    (hcond : ∀ m ∈ 𝔑 * 𝔞, μ / c * ιO m ∈ invDifferent F) :
    (Ideal.absNorm 𝔢 : ℝ) ≤ ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ μ * (𝔑 : FI) *
      ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI)) : ℚ) : ℝ) := by
  set J := FractionalIdeal.spanSingleton (𝓞 F)⁰ μ * (𝔑 : FI) * ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact mul_ne_zero (coeIdeal_ne_zero' h𝔞) (coeIdeal_ne_zero' h𝔢) hc.symm
  -- step 1: `μ 𝔑𝔞 ⊆ c 𝔡⁻¹`
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ μ * ((𝔑 * 𝔞 : Ideal (𝓞 F)) : FI) ≤
      FractionalIdeal.spanSingleton (𝓞 F)⁰ c * invDifferent F := by
    refine FractionalIdeal.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 F)⁰).mp hi
    obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    have hzm : z * m ∈ 𝔑 * 𝔞 := Ideal.mul_mem_left _ z hm
    have e : z • μ * ιO m = c * (μ / c * ιO (z * m)) := by
      rw [Algebra.smul_def, map_mul]; field_simp
    rw [e]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ c) (hcond _ hzm)
  -- step 2: `J 𝔞 ⊆ (c) = 𝔞𝔢`, so `J ⊆ 𝔢`
  have hdif : invDifferent F * ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI) = 1 := by
    rw [SiegelWeil.SingularNF.coe_dif, mul_inv_cancel₀ invDifferent_ne_zero]
  have h2 : J * (𝔞 : FI) ≤ (𝔢 : FI) * (𝔞 : FI) := by
    have := mul_le_mul_left h1 ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI)
    calc J * (𝔞 : FI) = FractionalIdeal.spanSingleton (𝓞 F)⁰ μ * ((𝔑 * 𝔞 : Ideal (𝓞 F)) : FI) *
          ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI) := by
          rw [FractionalIdeal.coeIdeal_mul]; ring
      _ ≤ FractionalIdeal.spanSingleton (𝓞 F)⁰ c * invDifferent F *
          ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI) := this
      _ = (𝔢 : FI) * (𝔞 : FI) := by rw [mul_assoc, hdif, mul_one, hc, mul_comm]
  have h3 : J ≤ (𝔢 : FI) := fi_le_of_mul_le (coeIdeal_ne_zero' h𝔞) h2
  -- step 3: norms
  obtain ⟨𝔣, h𝔣⟩ := exists_eq_coeIdeal_mul_of_le h𝔢 h3
  have hJ0 : J ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (coeIdeal_ne_zero' h𝔑)) (coeIdeal_ne_zero' SiegelWeil.SingularNF.dif_ne_bot)
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have h𝔣0 : 𝔣 ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot, mul_zero] at h𝔣
    exact hJ0 h𝔣
  have hN𝔣 : (1 : ℝ) ≤ (Ideal.absNorm 𝔣 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔣0)
  rw [h𝔣, map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  have : (0 : ℝ) ≤ (Ideal.absNorm 𝔢 : ℝ) := Nat.cast_nonneg _
  nlinarith


open Classical in
/-- **The row average of $\Phi_{C,\mathfrak d}$ is $O(N(\mathfrak b_C\mathfrak d)^{-1})$**: with $|\Phi| \le B$ and $\Phi(c, r) = 0$ unless
$r \in \mathfrak b_C\mathfrak d$, $\big|\frac1{N(\mathfrak M)}\sum_{r\in\mathcal O/\mathfrak M}\Phi(c, \tilde r)e(\cdot)\big| \le B\,\#(\mathfrak b\mathfrak d/\mathfrak M)/N(\mathfrak M)
= B/N(\mathfrak b\mathfrak d)$, $\mathfrak M = \mathfrak N\mathfrak b\mathfrak d$. -/
lemma norm_rowAvg_eisWt2_le (h𝔑 : 𝔑 ≠ ⊥) (C : ClassGroup (𝓞 F)) {B : ℝ}
    (hB : ∀ 𝔡 y, ‖eisWt2 f 𝔑 C 𝔡 y‖ ≤ B) {𝔡 : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) (c μ : F) :
    ‖rowAvg (eisWt2 f 𝔑 C 𝔡) (𝔑 * repIdeal C * 𝔡) c μ‖ ≤ B * ((Ideal.absNorm (repIdeal C * 𝔡) : ℝ))⁻¹ := by
  set J := 𝔑 * repIdeal C * 𝔡
  set I := repIdeal C * 𝔡
  have hJ : J ≠ ⊥ := mul_ne_zero (mul_ne_zero h𝔑 (repIdeal_ne_bot C)) h𝔡
  have hI : I ≠ ⊥ := mul_ne_zero (repIdeal_ne_bot C) h𝔡
  have hJI : J ≤ I := by
    rw [show J = 𝔑 * I by simp only [J, I, mul_assoc]]; exact Ideal.mul_le_right
  haveI := SiegelWeil.SingularNF.finite_quot hJ
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 𝔡 (0, 0))
  -- the pointwise bound
  have hpt : ∀ r : 𝓞 F ⧸ J, ‖eisWt2 f 𝔑 C 𝔡 (c, ιO (Quotient.out r)) *
      eTr (μ * ιO (Quotient.out r) / c)‖ ≤ if Quotient.out r ∈ I then B else 0 := by
    intro r
    rw [norm_mul, norm_eTr, mul_one]
    split_ifs with hr
    · exact hB _ _
    · rw [eisWt2, cutWeight_of_not_le, norm_zero]
      intro h
      obtain ⟨a, ha, ha'⟩ := (FractionalIdeal.mem_coeIdeal _).mp (cuspIdeal_le_iff.mp h).2
      exact hr (FaithfulSMul.algebraMap_injective (𝓞 F) F ha' ▸ ha)
  -- the count
  have hcnt := sum_indicator_mem_quot hJ hJI
  rw [finsum_eq_sum_of_fintype] at hcnt
  have hcntR : (∑ r : 𝓞 F ⧸ J, (if Quotient.out r ∈ I then (1 : ℝ) else 0)) * (Ideal.absNorm I : ℝ) =
      (Ideal.absNorm J : ℝ) := by
    apply Complex.ofReal_injective
    push_cast
    rw [← hcnt]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  have hNI : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI)
  have hNJ : (0 : ℝ) < Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ)
  rw [rowAvg, finsum_eq_sum_of_fintype, norm_mul, norm_inv, Complex.norm_natCast]
  calc ((Ideal.absNorm J : ℝ))⁻¹ * ‖∑ r : 𝓞 F ⧸ J, eisWt2 f 𝔑 C 𝔡 (c, ιO (Quotient.out r)) *
        eTr (μ * ιO (Quotient.out r) / c)‖
      ≤ ((Ideal.absNorm J : ℝ))⁻¹ * ∑ r : 𝓞 F ⧸ J, (if Quotient.out r ∈ I then B else 0) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hpt r)
    _ = ((Ideal.absNorm J : ℝ))⁻¹ * (B * ∑ r : 𝓞 F ⧸ J, (if Quotient.out r ∈ I then (1 : ℝ) else 0)) := by
        congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp
    _ = B * ((Ideal.absNorm I : ℝ))⁻¹ := by
        have e : ∑ r : 𝓞 F ⧸ J, (if Quotient.out r ∈ I then (1 : ℝ) else 0) =
            (Ideal.absNorm J : ℝ) / (Ideal.absNorm I : ℝ) := by
          rw [eq_div_iff hNI.ne']; exact hcntR
        rw [e]; field_simp

variable (𝔑) in
/-- **The support condition of the row coefficients** of $\Phi_{C,\mathfrak d_S}$ at $\mu$: the row $c = \tilde t \ne 0$ is integral, lies in
$\mathfrak b_C\mathfrak d_S$, and $\mu c^{-1}\mathfrak N\mathfrak b_C\mathfrak d_S \subseteq \mathfrak d^{-1}$. Parameters: `C`, `μ`, `p = (S, t)`. -/
def RowCond (C : ClassGroup (𝓞 F)) (μ : F) (p : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F) : Prop :=
  p.2.out ≠ 0 ∧ (∃ c' : 𝓞 F, ιO c' = crep p.2 ∧ c' ∈ repIdeal C * sqfIdeal p.1) ∧
    ∀ m ∈ 𝔑 * (repIdeal C * sqfIdeal p.1), μ / crep p.2 * ιO m ∈ invDifferent F

open Classical in
/-- **The bound on the row coefficients**: $|\rho_{\Phi_{C,\mathfrak d_S}}(t, \mu)| \le c_{\mathcal O}|\Lambda_2(\mu)|B\cdot|N(c)|^{-1}N(\mathfrak b_C\mathfrak d_S)^{-1}$ on
`RowCond`, and $0$ off it. -/
theorem norm_rowCo_le (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {B : ℝ} (hB : ∀ 𝔡 y, ‖eisWt2 f 𝔑 C 𝔡 y‖ ≤ B) (μ : F)
    (p : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F) :
    ‖rowCo (eisWt2 f 𝔑 C (sqfIdeal p.1)) (𝔑 * repIdeal C * sqfIdeal p.1) (sqfLevel_ne_bot h𝔑 C p.1) p.2 μ‖ ≤
      ((latConst (oBasis F) : ℝ) * ‖lipCoeff 2 (realVec μ)‖ * B) *
        (if RowCond 𝔑 C μ p then (absNorm (crep p.2))⁻¹ * ((Ideal.absNorm (repIdeal C * sqfIdeal p.1) : ℝ))⁻¹
          else 0) := by
  obtain ⟨S, t⟩ := p
  dsimp only
  have hW := intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB ⊥ (0, 0))
  by_cases hP : RowCond 𝔑 C μ (S, t)
  · rw [if_pos hP]
    obtain ⟨ht, -, hcond⟩ := hP
    dsimp only at ht hcond
    have hc : crep t ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
    have hμM : ∀ m ∈ 𝔑 * repIdeal C * sqfIdeal S, eTr (μ * ιO m / crep t) = 1 := by
      intro m hm
      rw [mul_assoc] at hm
      apply eTr_of_mem
      rw [show μ * ιO m / crep t = μ / crep t * ιO m by ring]
      exact hcond m hm
    rw [rowCo_eq hW ht (sqfLevel_ne_bot h𝔑 C S) le_rfl hμM, norm_mul, norm_mul, norm_mul, norm_inv,
      Complex.norm_real (absNorm (crep t)), Real.norm_of_nonneg (absNorm_pos hc).le]
    have h1 := norm_rowAvg_eisWt2_le h𝔑 C hB (sqfIdeal_ne_bot S) (crep t) μ
    have hL : ‖((latConst (oBasis F) : NNReal) : ℂ)‖ = (latConst (oBasis F) : ℝ) := by
      rw [show ((latConst (oBasis F) : NNReal) : ℂ) = (((latConst (oBasis F) : ℝ)) : ℂ) from rfl,
        Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    rw [hL]
    have hA : 0 ≤ (absNorm (crep t))⁻¹ := inv_nonneg.mpr (absNorm_pos hc).le
    calc (latConst (oBasis F) : ℝ) * ‖lipCoeff 2 (realVec μ)‖ * (absNorm (crep t))⁻¹ *
          ‖rowAvg (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (crep t) μ‖
        ≤ (latConst (oBasis F) : ℝ) * ‖lipCoeff 2 (realVec μ)‖ * (absNorm (crep t))⁻¹ *
          (B * ((Ideal.absNorm (repIdeal C * sqfIdeal S) : ℝ))⁻¹) := by gcongr
      _ = _ := by ring
  · rw [if_neg hP, mul_zero]
    have h0 : rowCo (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) t μ = 0 := by
      simp only [RowCond, not_and_or, not_exists, not_forall] at hP
      rcases hP with ht | hint | ⟨m, hm, hnot⟩
      · exact rowCo_of_out_eq_zero _ _ _ (not_not.mp ht) μ
      · refine rowCo_of_row_eq_zero _ _ _ (fun d => eisWt2_eq_zero_of_not_mem C _ fun h => ?_) μ
        obtain ⟨a, ha, ha'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h
        exact (hint a).elim (· ha') (· ha)
      · obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, eTr (ιO r * (μ / crep t * ιO m)) ≠ 1 := by
          by_contra h
          push Not at h
          exact hnot ((SiegelWeil.SingularNF.mem_invDifferent_iff_eTr _).mpr h)
        refine rowCo_of_eTr_ne hW (m₀ := r * m) ?_ ?_
        · rw [mul_assoc]; exact Ideal.mul_mem_left _ r hm
        · rw [map_mul]; convert hr using 2; ring
    rw [h0, norm_zero]


/-- **Absolute convergence of the Möbius family of row coefficients** ($\mu \ne 0$): $(S, t) \mapsto \rho_{\Phi_{C,\mathfrak d_S}}(t, \mu)$ is
absolutely summable. On `RowCond` write $(c') = \mathfrak b\mathfrak d_S\,\mathfrak e$; then $\mathfrak e \supseteq \mu\mathfrak N\mathfrak d$
(`absNorm_le_of_rowCond`), $(S, t) \mapsto (S, \mathfrak e)$ is injective, and
$|N(c)|^{-1}N(\mathfrak b\mathfrak d_S)^{-1} \le N(\mu\mathfrak N\mathfrak d)\,N(\mathfrak d_S)^{-2}N(\mathfrak e)^{-2}$, summable ($\zeta_F(2)^2$-type). -/
@[kb "hecke1927" "absolute convergence of the Möbius family of row coefficients [unverified]"]
theorem summable_rowCo_moebius (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {μ : F} (hμ0 : μ ≠ 0) :
    Summable fun p : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F =>
      ‖rowCo (eisWt2 f 𝔑 C (sqfIdeal p.1)) (𝔑 * repIdeal C * sqfIdeal p.1) (sqfLevel_ne_bot h𝔑 C p.1) p.2 μ‖ := by
  classical
  set 𝔟 := repIdeal C
  have h𝔟 := repIdeal_ne_bot C
  obtain ⟨B, hB⟩ := ((finite_range_perExt h𝔑 hf hfχ h𝔟).image (‖·‖)).bddAbove
  have hW : ∀ 𝔡 y, ‖eisWt2 f 𝔑 C 𝔡 y‖ ≤ max B 0 := by
    intro 𝔡 y
    by_cases h : cuspIdeal y.1 y.2 ≤ ((𝔟 * 𝔡 : Ideal (𝓞 F)) : FI)
    · rw [eisWt2, cutWeight_of_le h]; exact (hB ⟨_, ⟨y, rfl⟩, rfl⟩).trans (le_max_left _ _)
    · rw [eisWt2, cutWeight_of_not_le h, norm_zero]; exact le_max_right _ _
  set H : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F → ℝ := fun p =>
    if RowCond 𝔑 C μ p then (absNorm (crep p.2))⁻¹ * ((Ideal.absNorm (𝔟 * sqfIdeal p.1) : ℝ))⁻¹ else 0
  suffices hH : Summable H by
    exact hH.mul_left _ |>.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun p => norm_rowCo_le h𝔑 hf hfχ C hW μ p
  set P : Set (Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F) := {p | RowCond 𝔑 C μ p}
  have hex : ∀ p ∈ P, ∃ 𝔢 : Ideal (𝓞 F),
      Ideal.span {rowNum p.2} = (𝔟 * sqfIdeal p.1) * 𝔢 := by
    rintro ⟨S, t⟩ ⟨-, ⟨c', hc', hmem⟩, -⟩
    have : c' = rowNum t := FaithfulSMul.algebraMap_injective (𝓞 F) F (hc'.trans (rowNum_spec ⟨c', hc'⟩).symm)
    subst this
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  choose! E hE using hex
  have hcrep : ∀ p ∈ P, ιO (rowNum p.2) = crep p.2 := by
    rintro ⟨S, t⟩ ⟨-, ⟨c', hc', -⟩, -⟩
    exact rowNum_spec ⟨c', hc'⟩
  have hnum0 : ∀ p ∈ P, rowNum p.2 ≠ 0 := by
    intro p hp h0
    have := hcrep p hp
    rw [h0, map_zero] at this
    exact hp.1 ((crep_eq_zero_iff p.2).mp this.symm)
  have hE0 : ∀ p ∈ P, E p ≠ ⊥ := by
    intro p hp h0
    have := hE p hp
    rw [h0, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at this
    exact hnum0 p hp this
  set ι : P → Finset (HeightOneSpectrum (𝓞 F)) × Ideal (𝓞 F) := fun p => (p.1.1, E p.1)
  have hι : Function.Injective ι := by
    rintro ⟨⟨S, t⟩, hp⟩ ⟨⟨S', t'⟩, hq⟩ hpq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpq
    simp only [ι] at h1 h2
    subst h1
    have hspan : Ideal.span {rowNum t} = Ideal.span {rowNum t'} := by
      rw [hE _ hp, hE _ hq, h2]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have h3 : t = t' := by
      rw [← crep_mk t, ← crep_mk t']
      refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨u⁻¹, ?_⟩))
      rw [← hcrep _ hp, ← hcrep _ hq, ← hu, Units.smul_def, Algebra.smul_def, ← map_mul]
      congr 1
      show (u⁻¹ : (𝓞 F)ˣ) * (rowNum t * (u : 𝓞 F)) = rowNum t
      rw [mul_comm (rowNum t) (u : 𝓞 F), ← mul_assoc, Units.inv_mul, one_mul]
    subst h3
    rfl
  -- the constant
  set NJ : ℝ := ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ μ * (𝔑 : FI) *
      ((SiegelWeil.SingularNF.dif F : Ideal (𝓞 F)) : FI)) : ℚ) : ℝ)
  set h : Finset (HeightOneSpectrum (𝓞 F)) × Ideal (𝓞 F) → ℝ := fun q =>
    (Ideal.absNorm (sqfIdeal q.1) : ℝ) ^ (-(2 : ℝ)) * (Ideal.absNorm q.2 : ℝ) ^ (-(2 : ℝ))
  have hh : Summable h := by
    have h1 : Summable fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
        (Ideal.absNorm (sqfIdeal S) : ℝ) ^ (-(2 : ℝ)) := summable_absNorm_sqfIdeal one_lt_two
    have h2 : Summable fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) :=
      QuadFormsKB.NFEuler.summable_absNorm_rpow one_lt_two
    exact Summable.mul_of_nonneg h1 h2 (fun S => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hHP : ∀ p : P, H p ≤ NJ * h (ι p) := by
    rintro ⟨⟨S, t⟩, hp⟩
    have hp' := hp
    obtain ⟨ht, -, hcond⟩ := hp'
    have hp2 : RowCond 𝔑 C μ (S, t) := hp
    simp only [H, ι, h]
    rw [if_pos hp2]
    set 𝔞 := 𝔟 * sqfIdeal S
    have h𝔞 : 𝔞 ≠ ⊥ := mul_ne_zero h𝔟 (sqfIdeal_ne_bot S)
    have h𝔢 := hE0 _ hp
    have hspan := hE _ hp
    -- `(crep t) = 𝔞 𝔢` as fractional ideals
    have hc : FractionalIdeal.spanSingleton (𝓞 F)⁰ (crep t) = (𝔞 : FI) * (E (S, t) : FI) := by
      rw [← hcrep _ hp, ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul]
      exact congrArg _ hspan
    have hNe := absNorm_le_of_rowCond h𝔑 hμ0 h𝔞 h𝔢 hc hcond
    -- norms
    have hA : absNorm (crep t) = (Ideal.absNorm 𝔞 : ℝ) * (Ideal.absNorm (E (S, t)) : ℝ) := by
      rw [← hcrep _ hp, absNorm, ← absNorm_span_eq_prod_abs, hspan, map_mul]; push_cast; ring
    have hN𝔞 : (Ideal.absNorm 𝔞 : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * (Ideal.absNorm (sqfIdeal S) : ℝ) := by
      rw [map_mul]; push_cast; ring
    have hb1 : (1 : ℝ) ≤ Ideal.absNorm 𝔟 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔟)
    have hd1 : (1 : ℝ) ≤ Ideal.absNorm (sqfIdeal S) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact sqfIdeal_ne_bot S)
    have he1 : (1 : ℝ) ≤ Ideal.absNorm (E (S, t)) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔢)
    rw [hA, hN𝔞, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two,
      Real.rpow_two]
    set b := (Ideal.absNorm 𝔟 : ℝ)
    set d := (Ideal.absNorm (sqfIdeal S) : ℝ)
    set e := (Ideal.absNorm (E (S, t)) : ℝ)
    have hb0 : 0 < b := by linarith
    have hd0 : 0 < d := by linarith
    have he0 : 0 < e := by linarith
    rw [show (b * d * e)⁻¹ * (b * d)⁻¹ = (b ^ 2)⁻¹ * ((d ^ 2)⁻¹ * e⁻¹) by field_simp]
    have hb2 : (b ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have hee : e⁻¹ ≤ NJ * (e ^ 2)⁻¹ := by
      rw [show NJ * (e ^ 2)⁻¹ = NJ / e * e⁻¹ by field_simp]
      have : 1 ≤ NJ / e := by rw [le_div_iff₀ he0]; linarith
      nlinarith [inv_pos.mpr he0]
    calc (b ^ 2)⁻¹ * ((d ^ 2)⁻¹ * e⁻¹) ≤ 1 * ((d ^ 2)⁻¹ * (NJ * (e ^ 2)⁻¹)) := by
          gcongr
      _ = NJ * ((d ^ 2)⁻¹ * (e ^ 2)⁻¹) := by ring
  have hHs : Summable fun p : P => H p := by
    refine ((hh.comp_injective hι).mul_left NJ).of_nonneg_of_le (fun p => ?_) hHP
    simp only [H]
    rw [if_pos (show RowCond 𝔑 C μ p.1 from p.2)]
    exact mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg fun v _ => abs_nonneg _))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hind : H = P.indicator H := by
    funext p
    by_cases hp : p ∈ P
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]; simp only [H]; rw [if_neg (show ¬ RowCond 𝔑 C μ p from hp)]
  rw [hind]
  exact summable_subtype_iff_indicator.mp hHs


/-! ### The Fourier coefficients of $E^{(2)}_f$ -/

lemma oDual_ne_zero {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) : oDual m ≠ 0 := by
  intro h
  apply hm
  apply (QuadFormsKB.Analysis.dualEquiv (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)).injective
  apply Subtype.ext
  rw [QuadFormsKB.Analysis.dualEquiv_coe, QuadFormsKB.Analysis.dualEquiv_coe]
  rw [show QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m = oDual m from rfl, h]
  exact oDual_zero.symm

/-- **The coefficient of one weight-2 series of the family, Möbius-summed over $S$**: for $\mu = \mu_m \ne 0$,
$\sum_S(-1)^{|S|}a_\mu(E_2(\cdot; \Phi_{C,\mathfrak d_S})) = \sum_tR_C(t, \mu)$, both absolutely convergent. -/
theorem hasSum_qCoeff_moebius (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) :
    (Summable fun t => ‖rowRed f 𝔑 C t (oDual m)‖) ∧
      HasSum (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (-1 : ℂ) ^ S.card *
        qCoeff (eis2 (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S))
          (oBasis F) (realVec (oDual m))) (∑' t, rowRed f 𝔑 C t (oDual m)) := by
  set μ := oDual m
  have hμ : μ ∈ invDifferent F := oDual_mem m
  have hμ0 : μ ≠ 0 := oDual_ne_zero hm
  set g : Finset (HeightOneSpectrum (𝓞 F)) × UOrbitF F → ℂ := fun p => (-1 : ℂ) ^ p.1.card *
    rowCo (eisWt2 f 𝔑 C (sqfIdeal p.1)) (𝔑 * repIdeal C * sqfIdeal p.1) (sqfLevel_ne_bot h𝔑 C p.1) p.2 μ
  have hn := summable_rowCo_moebius h𝔑 hf hfχ C hμ0
  have hgn : Summable fun p => ‖g p‖ := hn.congr fun p => by simp [g]
  have hg : Summable g := hgn.of_norm
  -- each coefficient is the sum of its rows
  have hq : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (-1 : ℂ) ^ S.card *
      qCoeff (eis2 (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S))
        (oBasis F) (realVec μ) = ∑' t, g (S, t) := by
    intro S
    have hW := intWeight_eisWt2 h𝔑 hf hfχ C (sqfIdeal_ne_bot S)
    have hper := isLatticePeriodic_of_mem_modularFormChar
      (eis2_eisWt2_mem_modularFormChar hd h𝔑 hf hfχ C (sqfIdeal_ne_bot S) (sqfLevel_ne_bot h𝔑 C S))
    rw [(qCoeff_eis2 hW (eisWt2_add_mul hf hfχ C _) hper hm).2, ← tsum_mul_left]
  -- the rows, Möbius-summed
  have hrow : ∀ t, HasSum (fun S => g (S, t)) (rowRed f 𝔑 C t μ) := fun t =>
    hasSum_rowCo_moebius h𝔑 hf hfχ C hμ t
  refine ⟨?_, ?_⟩
  · refine ((hgn.comp_injective Prod.swap_injective).prod).of_nonneg_of_le (fun _ => norm_nonneg _) fun t => ?_
    rw [← (hrow t).tsum_eq]
    exact norm_tsum_le_tsum_norm ((hgn.comp_injective Prod.swap_injective).prod_factor t)
  · simp_rw [hq]
    have h1 : HasSum (fun S => ∑' t, g (S, t)) (∑' p, g p) :=
      hg.hasSum.prod_fiberwise fun S => (hg.prod_factor S).hasSum
    have hsw : HasSum (fun p : UOrbitF F × Finset (HeightOneSpectrum (𝓞 F)) => g (p.2, p.1)) (∑' p, g p) :=
      (Equiv.prodComm _ _).hasSum_iff.mpr hg.hasSum
    have h2 : HasSum (fun t => rowRed f 𝔑 C t μ) (∑' p, g p) := hsw.prod_fiberwise fun t => hrow t
    rwa [h2.tsum_eq]


lemma qCoeff_smul' {ι J : Type*} [Fintype ι] [Fintype J] (c : ℂ) (g : (ι → ℍ) → ℂ)
    (b : Module.Basis J ℝ (ι → ℝ)) (ν : ι → ℝ) : qCoeff (c • g) b ν = c * qCoeff g b ν := by
  simp only [qCoeff, coeff, Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]

/-- **The Fourier coefficients of $E^{(2)}_f$** (any enumeration of the keys): for $\mu = \mu_m \in \mathfrak d^{-1}\setminus0$,
$$a_\mu(E^{(2)}_f) = \sum_{C\in\mathrm{Cl}_F}\sum_{t\in U\backslash F}R_C(t, \mu)\qquad(\texttt{rowRed}).$$
*Proof:* linearity over the finite family $\sum_C\sum_ra_r\,E_2(\cdot; \Phi_{C,\mathfrak d_r})$; un-grouping the keys
($a_r\,a_\mu(E_2(\Phi_{C,\mathfrak d_r})) = \sum_{\kappa(\mathfrak d_S) = r}(-1)^{|S|}a_\mu(E_2(\Phi_{C,\mathfrak d_S}))$, `eis2_eisWt2_sqf`); and
`hasSum_qCoeff_moebius`. -/
theorem qCoeff_eisGen2' [Fintype (RayKeyT 𝔑)] (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) :
    qCoeff (eisGen2' f 𝔑 h𝔑) (oBasis F) (realVec (oDual m)) = ∑ C, ∑' t, rowRed f 𝔑 C t (oDual m) := by
  classical
  set μ := oDual m
  set g : ClassGroup (𝓞 F) → RayKeyT 𝔑 → (InfinitePlace F → ℍ) → ℂ := fun C r =>
    eis2 (eisWt2 f 𝔑 C (keyRep 𝔑 r)) (𝔑 * repIdeal C * keyRep 𝔑 r) (keyLevel_ne_bot h𝔑 C r)
  have hmod : ∀ C r, g C r ∈ modularFormChar 𝔑 χ 2 := fun C r =>
    eis2_eisWt2_mem_modularFormChar hd h𝔑 hf hfχ C (keyRep_ne_bot 𝔑 r) _
  -- linearity
  have hlin : qCoeff (eisGen2' f 𝔑 h𝔑) (oBasis F) (realVec μ) =
      ∑ C, ∑ r, eisGen2Coeff 𝔑 r * qCoeff (g C r) (oBasis F) (realVec μ) := by
    rw [eisGen2', ← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
      (f := fun C r => eisGen2Coeff 𝔑 r • g C r), ← dualVec_oBasis]
    rw [qCoeff_sum_smul (Finset.univ ×ˢ Finset.univ) (fun p => eisGen2Coeff 𝔑 p.2) (f := fun p => g p.1 p.2)
      (fun p _ => (hmod p.1 p.2).1.2.1) (fun p _ => isLatticePeriodic_of_mem_modularFormChar (hmod p.1 p.2)) m,
      Finset.sum_product' (f := fun C r => eisGen2Coeff 𝔑 r * qCoeff (g C r) (oBasis F) (dualVec (oBasis F) m))]
  rw [hlin]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hmo := (hasSum_qCoeff_moebius hd h𝔑 hf hfχ C hm).2
  set q : Finset (HeightOneSpectrum (𝓞 F)) → ℂ := fun S => (-1 : ℂ) ^ S.card *
    qCoeff (eis2 (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S))
      (oBasis F) (realVec μ)
  have hqs : Summable q := hmo.summable
  -- scaling within a key
  have hscale : ∀ S, q S = (-1 : ℂ) ^ S.card * (∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ (-(2 : ℤ)) *
      qCoeff (g C (rayKey 𝔑 (sqfIdeal S))) (oBasis F) (realVec μ) := by
    intro S
    have hfun : eis2 (eisWt2 f 𝔑 C (sqfIdeal S)) (𝔑 * repIdeal C * sqfIdeal S) (sqfLevel_ne_bot h𝔑 C S) =
        ((∏ v, (realEmb F v (keyScale 𝔑 S) : ℂ)) ^ (-(2 : ℤ))) • g C (rayKey 𝔑 (sqfIdeal S)) :=
      funext fun z => eis2_eisWt2_sqf hd h𝔑 hf hfχ C S z
    simp only [q]
    rw [hfun, qCoeff_smul', mul_assoc]
  -- regroup by keys
  have hsplit : ∀ S, q S = ∑ r : RayKeyT 𝔑, if rayKey 𝔑 (sqfIdeal S) = r then q S else 0 := by
    intro S; rw [Finset.sum_ite_eq]; simp
  have hsum : ∀ r ∈ (Finset.univ : Finset (RayKeyT 𝔑)),
      Summable fun S => if rayKey 𝔑 (sqfIdeal S) = r then q S else 0 := by
    intro r _
    refine (hqs.indicator {S | rayKey 𝔑 (sqfIdeal S) = r}).congr fun S => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← hmo.tsum_eq, tsum_congr hsplit, Summable.tsum_finsetSum hsum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eisGen2Coeff, ← tsum_mul_right]
  refine tsum_congr fun S => ?_
  by_cases hS : rayKey 𝔑 (sqfIdeal S) = r
  · rw [if_pos hS, if_pos hS, hscale S, hS]
  · rw [if_neg hS, if_neg hS, zero_mul]

/-- **The Fourier coefficients of $E^{(2)}_f$** (the `eisGen2`): $a_\mu(E^{(2)}_f) = \sum_C\sum_tR_C(t, \mu)$ for
$\mu = \mu_m \in \mathfrak d^{-1}\setminus 0$ ($d \ge 2$), each inner series absolutely convergent. -/
@[kb "hecke1927" "Fourier coefficients of the weight-2 Eisenstein series with prescribed constant terms [unverified]"]
theorem qCoeff_eisGen2 (hd : 2 ≤ Fintype.card (InfinitePlace F)) (h𝔑 : 𝔑 ≠ ⊥) (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) :
    (∀ C, Summable fun t => ‖rowRed f 𝔑 C t (oDual m)‖) ∧
      qCoeff (eisGen2 f 𝔑 h𝔑) (oBasis F) (realVec (oDual m)) = ∑ C, ∑' t, rowRed f 𝔑 C t (oDual m) := by
  let := finite_rayKey (F := F) h𝔑
  let := Fintype.ofFinite (RayKeyT 𝔑)
  exact ⟨fun C => (hasSum_qCoeff_moebius hd h𝔑 hf hfχ C hm).1, qCoeff_eisGen2' hd h𝔑 hf hfχ hm⟩


open Classical in
/-- **Translation invariance of $[\mathfrak b(y) = \mathfrak b_C]\varphi_f(y)$** in a row $c \ne 0$. -/
lemma redPart_add_mul (hf : HasCuspLimits f 2)
    (hfχ : ∀ γ ∈ Gamma0R 𝔑, f ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f)
    (C : ClassGroup (𝓞 F)) {c : F} (hc : c ≠ 0) (d : F) (b : 𝓞 F) :
    redPart f C (c, d + c * ιO b) = redPart f C (c, d) := by
  have hid : cuspIdeal c (d + c * ιO b) = cuspIdeal c d := by
    rw [mul_comm c]; exact SiegelWeil.SingularNF.cuspIdeal_add_mul c d b
  have hγ : translO b ∈ Gamma0R 𝔑 := by rw [mem_Gamma0R]; simp [translO]
  have hphi := phiF_rowMul_inv hf (hfχ _ hγ) (x := (c, d + c * ιO b)) (Or.inl hc)
  have h11 : (translO b : SL(2, 𝓞 F)) 1 1 = 1 := by simp [translO]
  rw [h11, map_one, MulChar.map_one, one_mul] at hphi
  have hrow : rowMul (c, d + c * ιO b) (toF F (translO b))⁻¹ = (c, d) := by
    obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply (toF F (translO b))
    refine Prod.ext ?_ ?_
    · simp only [rowMul_fst, i0, i2, toF_apply]; simp [translO]
    · simp only [rowMul_snd, i1, i3, toF_apply]; simp [translO]
  rw [hrow] at hphi
  simp only [redPart, hid, hphi]

end Generic

/-! ### The genus Eisenstein series $E_Q$ in weight 2 -/

section Theta

open QuadFormsKB.Lattices

variable {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : n = 2 * 2)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF Q₀) stdLat)

open SiegelWeil.SingularNF in
include hQ hn hlev h𝔑 hfree in
/-- **The Möbius-inverted row coefficient of $\theta_{\mathrm{Gen}}$ is a row part of the singular series**: for $\mu \in \mathfrak d^{-1}$,
$$R_C(t, \mu) = C_Q\,c_{\mathcal O}\,\Lambda_2(\mu)\,A_{C,t}(\mu),$$
$C_Q$ = `eisCst Q₀ 2` (the theta constant term $\varphi(1, u) = C_QG_Q(-u)$, `phiF_thetaGen`), $A_{C,t}$ = `ssPart`. In the row
$c = \tilde t$: $\varphi(c, r) = N(c)^2\varphi(1, r/c)$, the average over $\mathfrak N c'$ reduces to one over $c'$, and $N(c') = |N(c)|$. -/
@[kb "siegel1935" "row coefficients of θ_Gen = C_Q c_𝒪 Λ₂ × row parts of the singular series [unverified]"]
theorem rowRed_thetaGen (C : ClassGroup (𝓞 F)) (t : UOrbitF F) {μ : F} (hμ : μ ∈ invDifferent F) :
    rowRed (thetaGen (formF Q₀) stdLat) 𝔑 C t μ =
      eisCst Q₀ 2 * (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) * ssPart Q₀ μ (C, t) := by
  classical
  set f := thetaGen (formF Q₀) stdLat
  have hf : HasCuspLimits f 2 := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hfχ := (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  rw [rowRed]
  split_ifs with h
  swap
  · -- no point has this row key
    have h0 : ssPart Q₀ μ (C, t) = 0 := by
      rw [ssPart]
      refine (tsum_congr fun x => ?_).trans tsum_zero
      rw [if_neg]
      intro hk
      apply h
      obtain ⟨c', hc', -⟩ := exists_isDen_of_rowKey hk
      exact ⟨fun h0 => crep_ne_zero_of_rowKey hk ((crep_eq_zero_iff t).mpr h0), c', hc'⟩
    rw [h0, mul_zero]
  obtain ⟨ht, hint⟩ := h
  set c := crep t
  set c' := rowNum t
  have hc' : ιO c' = c := rowNum_spec hint
  have hc : c ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
  have hc'0 : c' ≠ 0 := by rintro h; rw [h, map_zero] at hc'; exact hc hc'.symm
  haveI := finite_quot_span hc'0
  letI : Fintype (𝓞 F ⧸ Ideal.span {c'}) := Fintype.ofFinite _
  -- reduce the modulus from `𝔑 c'` to `c'`
  have hM : 𝔑 * Ideal.span {c'} ≠ ⊥ := mul_ne_zero h𝔑 (span_ne_bot hc'0)
  have havg := avg_quot_eq (I := Ideal.span {c'}) hM Ideal.mul_le_right
    (fun r => redPart f C (c, ιO r) * eTr (μ * ιO r / c)) (by
    intro r m hm
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_add, map_mul, hc', mul_comm (ιO b) c, redPart_add_mul hf hfχ C hc, mul_add, add_div,
      eTr_add, show μ * (c * ιO b) / c = ιO b * μ by field_simp,
      eTr_of_mem (algebraMap_mul_mem_invDifferent b hμ), mul_one])
  rw [rowAvg, havg]
  -- the row part through the representative `c'`
  have hpart := tsum_rowKey_eq_sum C t hc'0 hc' (fun x => ssFun Q₀ μ (-x))
  rw [ssPart]
  simp only at hpart ⊢
  rw [hpart, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  set R := Quotient.out r
  -- the summand
  have hss : ssFun Q₀ μ (-jmap c' r) = gaussAvg Q₀ (-(ιO R / c)) * eTr (μ * ιO R / c) := by
    rw [jmap, ← QuotientAddGroup.mk_neg, ssFun_mk Q₀ hμ, hc']
    congr 1; congr 1; ring
  have hphi : phiF f 2 (c, ιO R) = (∏ v, (realEmb F v c : ℂ)) ^ (2 : ℤ) * (eisCst Q₀ 2 * gaussAvg Q₀ (-(ιO R / c))) := by
    have h1 := phiF_smul hf (x := ((1 : F), ιO R / c)) (Or.inl one_ne_zero) hc
    rw [mul_one, mul_div_cancel₀ _ hc] at h1
    have h2 : phiF f 2 ((1 : F), ιO R / c) = eisCst Q₀ 2 * gaussAvg Q₀ (-(ιO R / c)) := by
      have := phiF_thetaGen hQ hn hlev h𝔑 hfree (ιO R / c)
      exact_mod_cast this
    rw [h1, h2]
  have hN : (Ideal.absNorm (Ideal.span {c'}) : ℂ) = ((absNorm c : ℝ) : ℂ) := by
    have := absNorm_span_eq_prod_abs c'
    rw [hc'] at this
    exact_mod_cast this
  have hsq : (∏ v, (realEmb F v c : ℂ)) ^ (2 : ℤ) = ((absNorm c : ℝ) : ℂ) ^ 2 := by
    rw [zpow_ofNat, absNorm, Complex.ofReal_prod, ← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  have hA : ((absNorm c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (absNorm_pos hc).ne'
  rw [hss]
  by_cases hred : cuspIdeal (ιO c') (ιO R) = ((repIdeal C : Ideal (𝓞 F)) : FI)
  · rw [if_pos hred]
    have hred' : cuspIdeal c (ιO R) = ((repIdeal C : Ideal (𝓞 F)) : FI) := by rw [← hc']; exact hred
    rw [redPart, if_pos hred', hphi, hN, hsq]
    field_simp
  · rw [if_neg hred]
    have hred' : ¬ cuspIdeal c (ιO R) = ((repIdeal C : Ideal (𝓞 F)) : FI) := by rw [← hc']; exact hred
    rw [redPart, if_neg hred']
    ring


lemma latConst_oBasis_ne_zero : (latConst (oBasis F) : ℂ) ≠ 0 := by
  rw [show ((latConst (oBasis F) : NNReal) : ℂ) = (((latConst (oBasis F) : ℝ)) : ℂ) from rfl,
    latConst_oBasis_eq, Complex.ofReal_ne_zero]
  exact inv_ne_zero (Real.sqrt_pos.mpr discr_pos).ne'

include hQ hn hlev h𝔑 hfree in
/-- **The Fourier coefficients of the genus Eisenstein series in weight 2** ($n = 4$, $d \ge 2$, free genus): for
$\mu = \mu_m \in \mathfrak d^{-1}\setminus 0$,
$$a_\mu(E_Q) = C_Q\,c_{\mathcal O}\,\Lambda_2(\mu)\sum_{(C,t)}A_{C,t}(\mu),$$
the **singular series grouped by rows** (`SingularNF.ssPart`), which converges absolutely when $\mu \gg 0$. This is the
`eisQCoeff` formula with the singular series summed over denominators instead of over $F/\mathcal O$ (for $n = 4$ the latter does
not converge absolutely). -/
@[kb "siegel1935" "Fourier coefficients of E_Q in weight 2 over F: grouped singular series (n = 4) [unverified]"]
theorem qCoeff_eisQ2_eq (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m : Fin (Module.finrank ℚ F) → ℤ}
    (hm : m ≠ 0) :
    (lipCoeff 2 (realVec (oDual m)) ≠ 0 → Summable fun p => ‖SiegelWeil.SingularNF.ssPart Q₀ (oDual m) p‖) ∧
      qCoeff (eisQ2 Q₀ 𝔑 h𝔑) (oBasis F) (realVec (oDual m)) =
        eisCst Q₀ 2 * (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec (oDual m)) *
          ∑' p, SiegelWeil.SingularNF.ssPart Q₀ (oDual m) p := by
  classical
  set f := thetaGen (formF Q₀) stdLat
  have hf : HasCuspLimits f 2 := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hfχ := (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  obtain ⟨hs, hq⟩ := qCoeff_eisGen2 hd h𝔑 hf hfχ hm
  set μ := oDual m
  have hμ : μ ∈ invDifferent F := oDual_mem m
  have hE : eisQ2 Q₀ 𝔑 h𝔑 = eisGen2 f 𝔑 h𝔑 := rfl
  have hrr : ∀ C t, rowRed f 𝔑 C t μ = (eisCst Q₀ 2 * (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ)) *
      SiegelWeil.SingularNF.ssPart Q₀ μ (C, t) :=
    fun C t => rowRed_thetaGen hQ hn hlev h𝔑 hfree C t hμ
  by_cases hL : lipCoeff 2 (realVec μ) = 0
  · refine ⟨fun h => absurd hL h, ?_⟩
    rw [hE, hq]
    simp only [hrr, hL, mul_zero, zero_mul, tsum_zero, Finset.sum_const_zero]
  have hK : eisCst Q₀ 2 * (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (eisCst_ne_zero (isTotPosGram_Q₀ hQ) 2) latConst_oBasis_ne_zero) hL
  generalize eisCst Q₀ 2 * (latConst (oBasis F) : ℂ) * lipCoeff 2 (realVec μ) = K at hrr hK ⊢
  -- absolute summability of the row parts
  have hsC : ∀ C, Summable fun t => ‖SiegelWeil.SingularNF.ssPart Q₀ μ (C, t)‖ := by
    intro C
    refine ((hs C).mul_left ‖K‖⁻¹).congr fun t => ?_
    rw [hrr, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hK), one_mul]
  have hsP : Summable fun p => ‖SiegelWeil.SingularNF.ssPart Q₀ μ p‖ :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hsC, Summable.of_finite⟩
  refine ⟨fun _ => hsP, ?_⟩
  rw [hE, hq, hsP.of_norm.tsum_prod' (fun C => (hsC C).of_norm), tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun t => hrr C t

end Theta

end QuadFormsKB.HilbertModular
