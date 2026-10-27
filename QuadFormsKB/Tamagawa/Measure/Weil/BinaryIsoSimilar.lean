import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsotropic
import QuadFormsKB.Binary.RelDensities

/-!
# Similar isotropic binary forms: the Tamagawa measures and the characters correspond

**Layer:** a number field $F$; $Q_0$ a nondegenerate binary form over $\mathcal O_F$ with $Q_0\otimes F$ isotropic,
$G\in M_2(\mathcal O_F)$ with $\det G\ne0$, $c\in\mathcal O_F\setminus0$, $Q_1 = c\,(Q_0\circ G)$ (`simForm`).

**Proves**
* `chiP_eq_one_of_isSquare`: if $-\det H_{Q_0}$ is a square in $F$ (i.e. $Q_0\otimes F$ is isotropic), then
  $\chi_{\mathfrak p}(Q_0) = 1$ at every $\mathfrak p\nmid2\det H_{Q_0}$; hence (`multipliable_siegelDensity_div_lamV`) the
  local factors $\alpha_v(L,L)/\lambda_v$, $\lambda_v = 1-N(v)^{-1}$, are $1$ for almost all $v$;
* `map_muFin_simConjFin_lamV`: $(g\mapsto G^{-1}gG)_*\mu^{\lambda}_{f,Q_0} = \prod'_v\|\delta\|_v\cdot\mu^{\lambda}_{f,Q_1}$ for
  $\lambda = $ `lamV`;
* **`map_muTam_simConjAdele_lamV`**: $(g\mapsto G^{-1}gG)_*$`muTam Q₀ lamV` $=$ `muTam Q₁ lamV` (product formula);
* **`isoChar_simConjAdele`**: $\chi_{G^{-1}e}(G^{-1}gG) = \chi_e(g)$ (the isotropic line $Fe$ of $Q_0$ is the line
  $FG^{-1}e$ of $Q_1$).

Source: Weil 1982, §2.3, Thm 2.3.1, pp. 21–22 (independence of choices, product formula).
-/

open MeasureTheory Measure Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity
  QuadFormsKB.QuadForm QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.RegProd QuadFormsKB.NFEuler
  QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.ArchSOMeasure

variable {F : Type} [Field F] [NumberField F]

/-! ### The local factors of an isotropic binary form -/

/-- If $-\det H_{Q_0} = s^2$ with $s\in F$, then $s\in\mathcal O_F$. -/
theorem exists_int_sqrt_of_isSquare {Q₀ : QuadForm (𝓞 F) 2} (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    ∃ s : 𝓞 F, s * s = -Q₀.hessian.det := by
  obtain ⟨s, hs⟩ := h
  have hint : IsIntegral ℤ (s ^ 2) := by
    rw [sq, ← hs]; exact (-Q₀.hessian.det).isIntegral_coe
  have hs' : IsIntegral ℤ s := IsIntegral.of_pow two_pos hint
  refine ⟨⟨s, hs'⟩, RingOfIntegers.coe_injective ?_⟩
  show s * s = ((-Q₀.hessian.det : 𝓞 F) : F)
  exact hs.symm

/-- **$\chi_{\mathfrak p} = 1$ for an isotropic binary form** at every $\mathfrak p\nmid2\det H$. -/
theorem chiP_eq_one_of_isSquare {Q₀ : QuadForm (𝓞 F) 2} (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badPrimes Q₀) : chiP v Q₀ = 1 := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h2 => hv (v.asIdeal.mul_mem_right _ h2)
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun hd => hv (v.asIdeal.mul_mem_left _ hd)
  have hd' : -Q₀.hessian.det ∉ v.asIdeal := fun h' => hd (v.asIdeal.neg_mem_iff.mp h')
  rw [chiP_binary_eq_charNF v Q₀ h2 hd]
  obtain ⟨s, hs⟩ := exists_int_sqrt_of_isSquare h
  have : Siegel.charNF v (-Q₀.hessian.det) = 1 :=
    (Binary.Rel.charNF_eq_one_iff v hd').mpr ⟨s, by rw [← hs, sq, sub_self]; exact v.asIdeal.zero_mem⟩
  rw [this]; norm_num

theorem lamV_eq (v : HeightOneSpectrum (𝓞 F)) : lamV v = 1 - (1 : ℝ) / (normP v : ℝ) := by
  simp [lamV, normP, one_div]

/-- **The local factors $\alpha_v/\lambda_v$ of an isotropic binary form are $1$ for almost all $v$**, so their product
converges absolutely. -/
theorem multipliable_siegelDensity_div_lamV {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate)
    (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    Multipliable fun v => NF.siegelDensity v Q₀ Q₀ / lamV v := by
  classical
  have hS : ∀ v ∉ (finite_badPrimes Q₀ hQ).toFinset, chiP v Q₀ = (fun _ => (1 : ℝ)) v := fun v hv =>
    chiP_eq_one_of_isSquare h v (by simpa using hv)
  refine (multipliable_siegelDensity_binary_reg hQ _ hS).congr fun v => ?_
  simp only [lamV_eq, _root_.zpow_neg_one, div_eq_mul_inv]

theorem isSquare_simForm {Q₀ : QuadForm (𝓞 F) 2} {c : 𝓞 F} {G : Matrix (Fin 2) (Fin 2) (𝓞 F)}
    (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    IsSquare (algebraMap (𝓞 F) F (-(simForm Q₀ c G).hessian.det)) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨algebraMap (𝓞 F) F (c * G.det) * s, ?_⟩
  rw [hessian_det_simForm]
  have : algebraMap (𝓞 F) F (-(c ^ 2 * G.det ^ 2 * Q₀.hessian.det)) =
      algebraMap (𝓞 F) F (c * G.det) ^ 2 * algebraMap (𝓞 F) F (-Q₀.hessian.det) := by
    simp only [map_neg, map_mul, map_pow]; ring
  rw [this, hs]; ring

/-! ### The finite Tamagawa measures of similar isotropic forms -/

section Fin

variable {Q₀ : QuadForm (𝓞 F) 2} {c : 𝓞 F} {G : Matrix (Fin 2) (Fin 2) (𝓞 F)}

/-- **The finite Tamagawa measures of similar isotropic binary forms** (convergence factors $\lambda_v = 1-N(v)^{-1}$):
$(g\mapsto G^{-1}gG)_*\mu^{\lambda}_{f,Q_0} = \prod'_v\|\delta\|_v\cdot\mu^{\lambda}_{f,Q_1}$ (as `map_muFin_simConjFin`, with the
finitely supported products of `multipliable_siegelDensity_div_lamV`). -/
theorem map_muFin_simConjFin_lamV (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    (Tamagawa.Measure.muFin Q₀ lamV).map (simConjFin hc hG) =
      ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
          ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖) •
        Tamagawa.Measure.muFin (simForm Q₀ c G) lamV := by
  classical
  have hn : 0 < 2 := two_pos
  have hQ₁ := nondegenerate_simForm hQ hc hG
  have h₁ := isSquare_simForm (c := c) (G := G) h
  have : LocallyCompactSpace (SOAf (simForm Q₀ c G)) :=
    (isClosed_soAf _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hlam : ∀ v : HeightOneSpectrum (𝓞 F), 0 < lamV v := lamV_pos
  set lam := (lamV : HeightOneSpectrum (𝓞 F) → ℝ) with hlamdef
  set S := (simBad_finite hc hG).toFinset with hS
  set e := simConjFin (Q₀ := Q₀) hc hG with he
  have hmeas : Measurable e := e.continuous.measurable
  set nδ : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ with hnδ
  set α₀ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀ with hα₀def
  set α₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v (simForm Q₀ c G) (simForm Q₀ c G)
    with hα₁def
  have hα₀ : ∀ v, 0 < α₀ v := fun v => siegelDensity_self_pos' Q₀ hQ v
  have hα₁ : ∀ v, 0 < α₁ v := fun v => siegelDensity_self_pos' _ hQ₁ v
  have hnδpos : ∀ v, 0 < nδ v := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr (coe_ne_zero_of_ne_zero (simJac_ne_zero hc hG)))
  have hnδ1 : ∀ v ∉ S, nδ v = 1 := fun v hv =>
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v _).mpr (by simpa [hS] using hv)
  have : IsMulLeftInvariant ((Tamagawa.Measure.muFin Q₀ lam).map e) :=
    isMulLeftInvariant_map e.toMulEquiv.toMonoidHom.toMulHom hmeas e.surjective
  have : SigmaFinite ((Tamagawa.Measure.muFin Q₀ lam).map e) :=
    (e.toHomeomorph.toMeasurableEquiv).sigmaFinite_map
  have hμK : ∀ v, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (α₀ v) := fun v => by
    rw [muLocSO_soStabSO, div_one]
  have hμU : ∀ v, muLocSO v Q₀ 1 (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
      (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) = ENNReal.ofReal (nδ v * α₁ v) := fun v => by
    rw [sim_muLocSO_simU hn hQ v hc hG, ENNReal.ofReal_mul (hnδpos v).le]
  have hgood : ∀ v ∉ S, α₀ v = α₁ v := fun v hv =>
    sim_alpha_eq_of_good hn hQ v hc hG (by simpa [hS] using hv)
  -- the two finitely supported products
  set f₀ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α₀ v / lam v with hf₀
  set f₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α₁ v / lam v with hf₁
  have hm₀ : Multipliable f₀ := multipliable_siegelDensity_div_lamV hQ h
  have hm₁ : Multipliable f₁ := multipliable_siegelDensity_div_lamV hQ₁ h₁
  have hff₀ : finFactor Q₀ lam = ∏' v, f₀ v := finFactor_eq Q₀ hQ hlam
  have hff₁ : finFactor (simForm Q₀ c G) lam = ∏' v, f₁ v := finFactor_eq _ hQ₁ hlam
  have hval : ((Tamagawa.Measure.muFin Q₀ lam).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) =
      ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) lam) := by
    have hU : ∀ v ∈ S, MeasurableSet (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) := fun v _ =>
      ((isOpen_soStabSO v _).preimage (simConjSOV v hc hG).continuous).measurableSet
    rw [Measure.map_apply hmeas (isOpen_KSO _).measurableSet, simConjFin_preimage_KSO,
      muFin_boxSO Q₀ hQ hlam S _ hU]
    have hr : ∀ v, muLocSO v Q₀ (lam v) (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) /
          muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (nδ v * α₁ v / α₀ v) := fun v => by
      rw [← haarSO_eq_div Q₀ hQ v (hlam v), haarSO_eq_div Q₀ hQ v one_pos, hμU, hμK,
        ENNReal.ofReal_div_of_pos (hα₀ v)]
    rw [Finset.prod_congr rfl fun v _ => hr v,
      ← ENNReal.ofReal_prod_of_nonneg (fun v _ => (div_pos (mul_pos (hnδpos v) (hα₁ v)) (hα₀ v)).le),
      ← ENNReal.ofReal_mul (finFactor_nonneg _ _)]
    congr 1
    rw [hff₀, hff₁, tprod_eq_prod_mul_tprod_ite f₀ hm₀ S (fun v _ => (div_pos (hα₀ v) (hlam v)).ne'),
      tprod_eq_prod_mul_tprod_ite f₁ hm₁ S (fun v _ => (div_pos (hα₁ v) (hlam v)).ne'), tprod_eq_prod hnδ1,
      show (∏' v, if v ∈ S then (1 : ℝ) else f₀ v) = ∏' v, if v ∈ S then (1 : ℝ) else f₁ v from
        tprod_congr fun v => by by_cases hv : v ∈ S <;> simp [hv, hf₀, hf₁, hgood]]
    have key : (∏ v ∈ S, f₀ v) * ∏ v ∈ S, nδ v * α₁ v / α₀ v = (∏ v ∈ S, nδ v) * ∏ v ∈ S, f₁ v := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [hf₀, hf₁]
      field_simp [(hα₀ v).ne', (hlam v).ne']
    linear_combination (∏' v, if v ∈ S then (1 : ℝ) else f₁ v) * key
  have hfin : ((Tamagawa.Measure.muFin Q₀ lam).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) ≠ ∞ := by
    rw [hval]; exact ENNReal.ofReal_ne_top
  have hP : 0 ≤ ∏' v, nδ v := tprod_nonneg fun v => (hnδpos v).le
  rw [eq_haarNorm (isCompact_KSO _) (isOpen_KSO _) _ hfin, hval]
  unfold Tamagawa.Measure.muFin
  rw [show (ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) lam)).toNNReal =
      (∏' v, nδ v).toNNReal * (finFactor (simForm Q₀ c G) lam).toNNReal by
    rw [← Real.toNNReal_mul hP]; exact ENNReal.toNNReal_coe _,
    sim_haarNorm_mul]
  ext A hA
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rfl


/-- **Similar isotropic binary forms have corresponding Tamagawa measures**:
$(g\mapsto G^{-1}gG)_*\mu_{\mathrm{Tam},Q_0} = \mu_{\mathrm{Tam},Q_1}$ for the convergence factors $\lambda_v = 1-N(v)^{-1}$
(the archimedean factor $\prod_{w\mid\infty}|\delta|_w^{m_w}$ and the finite factor $\prod_v\|\delta\|_v$ cancel by the product
formula). -/
@[kb "weil1982" "§2.3, Thm 2.3.1, pp. 21–22 (independence of choices, product formula)"]
theorem map_muTam_simConjAdele_lamV (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (h : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det))) :
    (muTam Q₀ hQ lamV).map (simConjAdele hc hG) = muTam (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) lamV := by
  have hδ := simJac_ne_zero hc hG
  have hpf := prod_infinitePlace_mul_tprod_finitePlace hδ
  have hf : ⇑(simConjAdele (Q₀ := Q₀) hc hG) = Prod.map (simConjInf hc hG) (simConjFin hc hG) := rfl
  have h1 : Measurable (simConjInf (Q₀ := Q₀) hc hG) := (simConjInf hc hG).continuous.measurable
  have h2 : Measurable (simConjFin (Q₀ := Q₀) hc hG) := (simConjFin hc hG).continuous.measurable
  rw [muTam, hf, map_prodMap_prod h1 h2 _ _ _ _ (map_muArchTamSO_simConjInf hQ hc hG) (map_muFin_simConjFin_lamV hQ hc hG h),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _), hpf, ENNReal.ofReal_one,
    one_smul, muTam]

end Fin

/-! ### The characters of similar forms -/

section Char

variable {Q₀ : QuadForm (𝓞 F) 2} {c : 𝓞 F} {G : Matrix (Fin 2) (Fin 2) (𝓞 F)}

/-- If $M\iota(e) = t\,\iota(e)$ with $e\ne0$, then the eigenvalue of $M$ on the line of $e$ is $t$. -/
theorem eigVal_eq_of_mulVec {K : Type*} [Field K] (ι : F →+* K) {e : Fin 2 → F} (he : e ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) K} {t : K} (h : M *ᵥ (ι ∘ e) = t • (ι ∘ e)) : eigVal ι e M = t := by
  rw [eigVal, h, Pi.smul_apply, smul_eq_mul, Function.comp, mul_div_assoc,
    div_self ((map_ne_zero ι).mpr (isoIdx_ne_zero he)), mul_one]

/-- **Conjugation and eigenvalues**: if $P$ is invertible over $F$ and $M\iota(e) = t\,\iota(e)$, then
$P_K^{-1}MP_K$ has eigenvalue $t$ on the line of $P^{-1}e$. -/
theorem eigVal_conj {K : Type*} [Field K] (ι : F →+* K) (P : GL (Fin 2) F) {e : Fin 2 → F} (he : e ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) K} {t : K} (h : M *ᵥ (ι ∘ e) = t • (ι ∘ e)) :
    eigVal ι (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e)
      (((Matrix.GeneralLinearGroup.map ι P)⁻¹ : GL (Fin 2) K) * M *
        (Matrix.GeneralLinearGroup.map ι P : GL (Fin 2) K)) = t := by
  have he' : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e ≠ 0 := by
    intro h0
    apply he
    have := congrArg (fun x => ((P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) h0
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, mulVec_zero] at this
  refine eigVal_eq_of_mulVec ι he' ?_
  have hmap : ∀ (A : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F), ι ∘ (A *ᵥ x) = A.map ι *ᵥ (ι ∘ x) := fun A x => by
    funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  have hPi : ((Matrix.GeneralLinearGroup.map ι P)⁻¹ : GL (Fin 2) K) =
      Matrix.GeneralLinearGroup.map ι (P⁻¹) := (map_inv _ _).symm
  rw [hmap, hPi, ← mulVec_mulVec, ← mulVec_mulVec]
  have h1 : ((Matrix.GeneralLinearGroup.map ι P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map ι *ᵥ (ι ∘ e)) = ι ∘ e := by
    rw [mulVec_mulVec]
    have : ((Matrix.GeneralLinearGroup.map ι P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map ι = 1 := by
      rw [show ((Matrix.GeneralLinearGroup.map ι P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map ι from rfl, ← Matrix.map_mul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero ι) (map_one ι)]
    rw [this, one_mulVec]
  rw [h1, h, mulVec_smul]
  rfl

theorem qF_eq_zero_iff_hessian (Q : QuadForm (𝓞 F) 2) (x : Fin 2 → F) :
    qF Q x = 0 ↔ x ⬝ᵥ ((Q.map (algebraMap (𝓞 F) F)).hessian *ᵥ x) = 0 := by
  have h := two_mul_evalIn (Q := Q.map (algebraMap (𝓞 F) F)) (R := F) x
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  rw [← h]
  change (Q.map (algebraMap (𝓞 F) F)).evalIn F x = 0 ↔ _
  constructor
  · intro h0; rw [h0, mul_zero]
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left two_ne_zero

/-- **The isotropic vector of a similar form**: if $Q_0(e) = 0$ then $Q_1(G^{-1}e) = c\,Q_0(e) = 0$. -/
theorem isIsoVec_simForm {e : Fin 2 → F} (he : IsIsoVec Q₀ e) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    IsIsoVec (simForm Q₀ c G) ((((LatChange.glF G hG)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e) := by
  set P : GL (Fin 2) F := LatChange.glF G hG
  have hPe : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e) = e := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine ⟨fun h0 => he.1 ?_, ?_⟩
  · rw [← hPe, h0, mulVec_zero]
  · rw [qF_eq_zero_iff_hessian, hessian_simForm hG, smul_mulVec, dotProduct_smul, ← mulVec_mulVec,
      ← mulVec_mulVec, hPe, dotProduct_mulVec, vecMul_transpose, hPe, (qF_eq_zero_iff_hessian Q₀ e).mp he.2,
      smul_zero]

variable (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e) (hc : c ≠ 0) (hG : G.det ≠ 0)

theorem finComp_simConjFin (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    finComp (simConjFin hc hG g) v = simConjSOV v hc hG (finComp g v) := rfl

theorem isoCharV_simConjSOV (v : HeightOneSpectrum (𝓞 F)) (x : SOv v Q₀) :
    isoCharV (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) v (simConjSOV v hc hG x) =
      isoCharV hQ he v x := by
  change eigVal _ _ (omat (simConjV v hc hG x.1)) = eigVal _ e (omat x.1)
  rw [omat, simConjV_val]
  exact eigVal_conj _ _ he.1 (isoCharV_spec hQ he v x)

theorem isoCharFin_simConjFin (g : SOAf Q₀) :
    isoCharFin (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) (simConjFin hc hG g) =
      isoCharFin hQ he g := by
  ext v : 1
  change isoCharV (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) v (finComp (simConjFin hc hG g) v) =
    isoCharV hQ he v (finComp g v)
  rw [finComp_simConjFin, isoCharV_simConjSOV]

theorem isoCharInf_simConjInf (g : GInfSO Q₀) :
    isoCharInf (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) (simConjInf hc hG g) =
      isoCharInf hQ he g := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change eigVal _ _ ((ArchSO.incl _ ((simConjInf hc hG g).1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      eigVal _ e ((ArchSO.incl _ (g.1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [simConjInf_fst]
    exact eigVal_conj _ _ he.1 (isoCharR_spec hQ he w (g.1 w))
  · change eigVal _ _ (ArchSOC.mat _ ((simConjInf hc hG g).2 w)) = eigVal _ e (ArchSOC.mat _ (g.2 w))
    rw [simConjInf_snd, conjSOC_mat]
    exact eigVal_conj _ _ he.1 (isoCharC_spec hQ he w (g.2 w))

/-- **The characters of similar forms correspond**: $\chi_{G^{-1}e}(G^{-1}gG) = \chi_e(g)$ in $\mathbb A_F^\times$. -/
theorem isoChar_simConjAdele (g : SOAdele Q₀) :
    isoChar (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) (simConjAdele hc hG g) =
      isoChar hQ he g := by
  apply Units.ext
  rw [isoChar_val, isoChar_val]
  exact Prod.ext (isoCharInf_simConjInf hQ he hc hG g.1) (isoCharFin_simConjFin hQ he hc hG g.2)

end Char

end QuadFormsKB.Tamagawa.Measure.Weil
