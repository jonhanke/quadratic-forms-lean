/-
# The orbit stabilizers of an isotropic rank-2 complement: the hypotheses of the torus lemma

**Layer:** number fields, adeles. Setting of `IsoMeasures.lean`: $Q_0$ in $N = r + 2$ variables, $T_0$, a rational frame
$\Xi$ with isotropic complement, its algebraic frame data `isoTower` ($Q''$ binary isotropic, $\iota = \iota_\infty\times\iota_f$),
the isotropic vector `isoVec` of $Q''$ and its eigenvalue character $\chi$. For $b\in SO(V)(\mathbb A_f)$ the orbit stabilizer
$U_b = \iota_f^{-1}(b^{-1}SO(\hat L)b)$ (`orbitStab`). This file proves the hypotheses of the torus lemma
(`tauIso_eq_tsum_DCq`) for $U = U_b$:

* `isoNormFin_orbitStab`: $|\chi(u)|_f = 1$ for $u\in U_b$ (an eigenvalue of a matrix in $GL_N(\mathcal O_v)$ is a unit,
  at every finite place $v$);
* `discreteTopology_levelGroup_orbitStab`: the level groups $\{\gamma_\infty : \gamma\in SO(Q'')(F),\ \gamma_f\in U_b\}$ are
  discrete ($\iota_\infty$ maps them injectively into the unit group of the lattice $b^{-1}\hat L\cap V$);
* `measurableSet_orbitStab_iso`, `muFin_orbitStab_iso_ne_zero`, `muFin_orbitStab_iso_ne_top`: for the representative of an
  orbit of integral frames, $U_b$ is measurable of positive finite measure (it is a box, `IsoAlg.orbitStab_eq_boxSO`);
* `multipliable_muLocSO_lamV_iso`, `finFactor_lamV_iso_pos`: the convergence factors $\lambda_v = 1 - Nv^{-1}$ make the
  local masses of $Q''$ equal to $1$ off a finite set.
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoMeasures
import QuadFormsKB.Tamagawa.Indefinite.Rank2Measures

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F]

section Gen

theorem one_le_tprod_real {ι : Type*} (b : ι → ℝ) (hb : ∀ i, 1 ≤ b i) (hm : Multipliable b) :
    1 ≤ ∏' i, b i :=
  ge_of_tendsto' hm.hasProd (fun _s =>
    Finset.prod_induction b (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hb i)

/-- **Positivity of the finite factor of a binary form for $\lambda_v = 1 - Nv^{-1}$**, with no isotropy hypothesis: the
factors $\alpha_v/\lambda_v$ are $\ge 1$ off the bad primes, so the product is either non-convergent (value $1$) or $\ge$ a
positive number. -/
theorem finFactor_lamV_pos_gen (Q' : QuadForm (𝓞 F) 2) (hQ' : Q'.Nondegenerate) : 0 < finFactor Q' lamV := by
  classical
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (muLocSO v Q' (lamV v) (soStabSO v Q' : Set (SOv v Q'))).toReal with ha
  have ha0 : ∀ v, 0 < a v := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos Q' hQ' v (lamV_pos v))
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  set S := (finite_badPrimes Q' hQ').toFinset with hSdef
  have hge : ∀ v, 1 ≤ (if v ∈ S then 1 else a v) := by
    intro v
    by_cases hv : v ∈ S
    · simp [hv]
    · rw [if_neg hv]
      have hv' : v ∉ badPrimes Q' := by simpa [hSdef] using hv
      simp only [ha]
      rw [muLocSO_soStabSO, ENNReal.toReal_ofReal (div_pos (siegelDensity_self_pos' Q' hQ' v) (lamV_pos v)).le,
        siegelDensity_binary_good Q' hQ' v hv', le_div_iff₀ (lamV_pos v), one_mul, lamV_eq]
      have hN : (0 : ℝ) < (NFEuler.normP v : ℝ) := by
        have := NFEuler.two_le_normP v
        exact_mod_cast (by omega : 0 < NFEuler.normP v)
      have h1 := (abs_le.1 (abs_chiP_le Q' v)).2
      have h2 : chiP v Q' / (NFEuler.normP v : ℝ) ≤ 1 / (NFEuler.normP v : ℝ) := div_le_div_of_nonneg_right h1 hN.le
      linarith
  show 0 < ∏' v, a v
  by_cases hm : Multipliable a
  · rw [tprod_eq_prod_mul_tprod_ite a hm S fun v _ => (ha0 v).ne']
    refine mul_pos (Finset.prod_pos fun v _ => ha0 v) ?_
    exact lt_of_lt_of_le one_pos
      (one_le_tprod_real _ hge (IsoAlg.multipliable_ite_one a hm S fun v _ => (ha0 v).ne'))
  · rw [tprod_eq_one_of_not_multipliable hm]; exact one_pos

end Gen

section GenOrbit

variable {r n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (Ξ : RatFrame Q₀ T₀) (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)

theorem muLoc_stab_ne_top (v : HeightOneSpectrum (𝓞 F))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hQ' : fr.Q'.Nondegenerate)
    (M : LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v))) :
    muLoc v fr.Q' 1 (stabilizer (orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) M :
      Set (orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))) ≠ ⊤ := by
  intro h
  have e := measure_stdStab_div_stab v Q₀ T₀ fr hQ' M
  rw [h, ENNReal.div_top] at e
  obtain ⟨h21, h12⟩ := stabilizerY_relIndex_ne_zero v Q₀ T₀ fr M
  have hw : 0 < locFrameWeightG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) M :=
    div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h12)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero h21))
  have := ENNReal.ofReal_pos.2 hw
  rw [← e] at this
  exact lt_irrefl _ this

theorem muLocSO_orbitStab_ne_top (hn' : 1 ≤ n') (b : IsoAlg.IntFr Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) :
    muLocSO v D.Q'' 1 (orbitStab (locIota v Q₀ T₀ (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT)) (soStabSO v Q₀)
      (evalSO Q₀ v b.1) : Set (SOv v D.Q'')) ≠ ⊤ := by
  have hK := IsoAlg.muLocSO_orbitStab_eq v Q₀ T₀ (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT) hT D.hQ'' hn'
    (evalSO Q₀ v b.1) (IsoAlg.locFrAt Q₀ hQ T₀ Ξ D hT b.1 b.2 v) rfl
  rw [hK, muLocSO_locOrbitStab v Q₀ T₀ (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT) D.hQ'' (by omega) hT,
    map_stabilizer_subtype]
  exact ne_top_of_le_ne_top (muLoc_stab_ne_top Q₀ T₀ v (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT) D.hQ'' _)
    (measure_mono (by exact_mod_cast inf_le_right))

theorem rel_decomp (b b' : IsoAlg.IntFr Q₀ T₀ Ξ) (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    ∃ k ∈ KSO Q₀, ∃ a, b'.1 = k * b.1 * D.ιFin a := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := stab_iotaB (IsoAlg.stabIn_frameCprod Q₀ hQ T₀ Ξ D) _ hfix
  exact ⟨k, hk, a, by rw [ha]; group⟩

theorem muFin_box_ne (hn' : 1 ≤ n') {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v)
    (hff : 0 < finFactor D.Q'' lam) (b : SOAf Q₀)
    (hb : ∀ v ∉ IsoAlg.towerBad Q₀ hQ T₀ Ξ D hT, evalSO Q₀ v b = 1)
    (hint : b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r) :
    muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b) ≠ 0 ∧ muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b) ≠ ⊤ := by
  classical
  set fr := IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT
  set Bad := IsoAlg.towerBad Q₀ hQ T₀ Ξ D hT
  have hU : ∀ v ∈ Bad, MeasurableSet
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) :=
    fun v _ => (IsoAlg.isOpen_orbitStab_loc v Q₀ T₀ fr _).measurableSet
  rw [IsoAlg.orbitStab_eq_boxSO Q₀ hQ T₀ Ξ D hT b hb, muFin_boxSO D.Q'' D.hQ'' hlam Bad _ hU]
  have hfac : ∀ v ∈ Bad, muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q'')) ≠ 0 ∧
      muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q'')) ≠ ⊤ := fun v _ =>
    ⟨muLocSO_soStabSO_pos D.Q'' D.hQ'' v (hlam v), by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top⟩
  have hnum : ∀ v ∈ Bad, muLocSO v D.Q'' (lam v)
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) ≠ 0 ∧ muLocSO v D.Q'' (lam v)
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) ≠ ⊤ := by
    intro v _
    have := QuadFormsKB.Tamagawa.Measure.ConeFinite.isHaarMeasure_muLocSO v D.Q'' D.hQ''
    rw [IsoAlg.muLocSO_apply_lam D.Q'' v (hlam v)]
    have hl0 : ENNReal.ofReal (lam v)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 (hlam v))).ne'
    refine ⟨mul_ne_zero hl0
      ((IsoAlg.isOpen_orbitStab_loc v Q₀ T₀ fr _).measure_pos _ ⟨1, Subgroup.one_mem _⟩).ne', ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (muLocSO_orbitStab_ne_top Q₀ hQ T₀ Ξ D hT hn' ⟨b, hint⟩ v)
  constructor
  · refine mul_ne_zero (ENNReal.ofReal_pos.2 hff).ne' ?_
    refine Finset.prod_ne_zero_iff.2 fun v hv => ?_
    exact (ENNReal.div_pos (hnum v hv).1 (hfac v hv).2).ne'
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun v hv => ?_)
    exact (ENNReal.div_lt_top (hnum v hv).2 (hfac v hv).1).ne

include hT in
theorem orbit_facts (hn' : 1 ≤ n') {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v)
    (hff : 0 < finFactor D.Q'' lam) (O : FinOrbit Q₀ T₀ Ξ) :
    MeasurableSet (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O) : Set (SOAf D.Q'')) ∧
      muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) ≠ 0 ∧
      muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) ≠ ⊤ := by
  classical
  set b : IsoAlg.IntFr Q₀ T₀ Ξ := Quotient.out O
  obtain ⟨b', hrel, hgood⟩ := IsoAlg.exists_goodRep Q₀ hQ T₀ Ξ D hT hn' b
  obtain ⟨k, hk, a, hb'⟩ := rel_decomp Q₀ hQ T₀ Ξ D b b' hrel
  have hset : (orbitStab D.ιFin (KSO Q₀) b'.1 : Set (SOAf D.Q'')) =
      ((orbitStab D.ιFin (KSO Q₀) b.1).comap (MulAut.conj a).toMonoidHom : Subgroup (SOAf D.Q'')) := by
    rw [hb', orbitStab_mul_mul _ _ _ _ hk]
  have hmeas' : MeasurableSet (orbitStab D.ιFin (KSO Q₀) b'.1 : Set (SOAf D.Q'')) := by
    rw [IsoAlg.orbitStab_eq_boxSO Q₀ hQ T₀ Ξ D hT b'.1 hgood]
    exact measurableSet_boxSO D.Q'' _ _ fun v _ => (IsoAlg.isOpen_orbitStab_loc v Q₀ T₀ _ _).measurableSet
  have hbU : (orbitStab D.ιFin (KSO Q₀) b.1 : Set (SOAf D.Q'')) =
      (fun x => a⁻¹ * x * a) ⁻¹' (orbitStab D.ιFin (KSO Q₀) b'.1 : Set (SOAf D.Q'')) := by
    rw [hset]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hm : MeasurableSet (orbitStab D.ιFin (KSO Q₀) b.1 : Set (SOAf D.Q'')) := by
    rw [hbU]
    exact hmeas'.preimage ((measurable_id.const_mul _).mul_const _)
  have hmu : muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b'.1) =
      muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b.1) := by
    have := IsoAlg.isMulRightInvariant_muFin_lam D.Q'' lam D.hQ'' (by omega)
    rw [hb', orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]
  have hne := muFin_box_ne Q₀ hQ T₀ Ξ D hT hn' hlam hff b'.1 hgood b'.2
  rw [hmu] at hne
  exact ⟨hm, hne⟩

theorem discreteTopology_levelGroup_gen (b : SOAf Q₀) (c : SOAf D.Q'') :
    DiscreteTopology (levelGroup (GammaSOAdele D.Q'') (orbitStab D.ιFin (KSO Q₀) b) c) := by
  classical
  haveI := discreteTopology_levelGroup Q₀ (D.ιFin c * b⁻¹)
  have hmem : ∀ h : levelGroup (GammaSOAdele D.Q'') (orbitStab D.ιFin (KSO Q₀) b) c,
      D.ιInf (h : GInfSO D.Q'') ∈ levelGroup (GammaSOAdele Q₀) (KSO Q₀) (D.ιFin c * b⁻¹) := by
    intro h
    obtain ⟨g, hg, hgh⟩ := Subgroup.mem_map.mp h.2
    refine Subgroup.mem_map.mpr ⟨MonoidHom.prodMap D.ιInf D.ιFin g, ⟨D.gamma_mem g hg.1, ?_⟩, ?_⟩
    · have h2 : c⁻¹ * g.2 * c ∈ orbitStab D.ιFin (KSO Q₀) b := hg.2
      rw [mem_orbitStab'] at h2
      show (D.ιFin c * b⁻¹)⁻¹ * D.ιFin g.2 * (D.ιFin c * b⁻¹) ∈ KSO Q₀
      rw [map_mul, map_mul, map_inv] at h2
      have e : (D.ιFin c * b⁻¹)⁻¹ * D.ιFin g.2 * (D.ιFin c * b⁻¹) =
          b * ((D.ιFin c)⁻¹ * D.ιFin g.2 * D.ιFin c) * b⁻¹ := by group
      rw [e]; exact h2
    · show D.ιInf g.1 = D.ιInf (h : GInfSO D.Q'')
      rw [← hgh]; rfl
  have hdisc : DiscreteTopology (levelGroup (GammaSOAdele D.Q'') (orbitStab D.ιFin (KSO Q₀) b) c) :=
    DiscreteTopology.of_continuous_injective
      (f := fun h : levelGroup (GammaSOAdele D.Q'') (orbitStab D.ιFin (KSO Q₀) b) c =>
        (⟨D.ιInf (h : GInfSO D.Q''), hmem h⟩ : levelGroup (GammaSOAdele Q₀) (KSO Q₀) (D.ιFin c * b⁻¹)))
      ((D.continuous_ιInf.comp continuous_subtype_val).subtype_mk _)
      fun a c' hac => Subtype.ext (D.ιInf_injective Q₀ hQ T₀ Ξ (congrArg Subtype.val hac))
  exact hdisc

end GenOrbit

section Ultra

theorem valuation_eigen_le_one {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (hM : ∀ i j, w (M i j) ≤ 1) (x : Fin N → K) (hx : x ≠ 0) (c : K)
    (h : M *ᵥ x = c • x) : w c ≤ 1 := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon
    exact hx (funext fun k => by_contra fun hk => hcon ⟨k, hk⟩)
  have : Nonempty (Fin N) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => w (x k))
  have hxi : w (x i) ≠ 0 := by
    intro h0
    have := hi j
    simp only [h0] at this
    exact hj ((Valuation.zero_iff w).1 (le_antisymm this zero_le))
  have h1 : w (c * x i) ≤ w (x i) := by
    have : (M *ᵥ x) i = c * x i := by rw [h]; simp
    rw [← this, mulVec, dotProduct]
    refine Valuation.map_sum_le w fun k _ => ?_
    rw [map_mul]
    calc w (M i k) * w (x k) ≤ 1 * w (x i) := mul_le_mul' (hM i k) (hi k)
      _ = w (x i) := one_mul _
  rw [map_mul] at h1
  by_contra hc
  have hc := not_le.1 hc
  have := mul_lt_mul_of_pos_right hc (zero_lt_iff.2 hxi)
  rw [one_mul] at this
  exact absurd h1 (not_le.2 this)

theorem valuation_eigen_eq_one {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {N : ℕ}
    (M M' : Matrix (Fin N) (Fin N) K) (hM : ∀ i j, w (M i j) ≤ 1) (hM' : ∀ i j, w (M' i j) ≤ 1)
    (hMM : M' * M = 1) (x : Fin N → K) (hx : x ≠ 0) (c : K) (h : M *ᵥ x = c • x) : w c = 1 := by
  have h1 := valuation_eigen_le_one w M hM x hx c h
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx
    have : M' *ᵥ (M *ᵥ x) = x := by rw [mulVec_mulVec, hMM, one_mulVec]
    rw [← this, h]; simp
  have h2 : M' *ᵥ x = c⁻¹ • x := by
    have hx' : x = c • (M' *ᵥ x) := by
      have e : M' *ᵥ (M *ᵥ x) = x := by rw [mulVec_mulVec, hMM, one_mulVec]
      calc x = M' *ᵥ (M *ᵥ x) := e.symm
        _ = c • (M' *ᵥ x) := by rw [h, mulVec_smul]
    calc M' *ᵥ x = c⁻¹ • (c • (M' *ᵥ x)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • x := by rw [← hx']
  have h3 := valuation_eigen_le_one w M' hM' x hx c⁻¹ h2
  rw [map_inv₀] at h3
  have hpos : 0 < w c := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 hc0)
  exact le_antisymm h1 ((inv_le_one₀ hpos).1 h3)

end Ultra

variable {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

include hiso in
theorem isSquare_iso : IsSquare (algebraMap (𝓞 F) F (-(isoTower Q₀ hQ T₀ hT Ξ).Q''.hessian.det)) :=
  (isotropicF_iff_isSquare _).1 (isotropicF_isoTower Q₀ hQ T₀ hT hiso Ξ)

theorem lamL_one_eq_lamV : lamL (F := F) (fun _ => (1 : ℝ)) = lamV := funext fun v => (lamV_eq v).symm

include hiso in
theorem hS_iso : ∀ v ∉ (finite_badPrimes (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'').toFinset,
    chiP v (isoTower Q₀ hQ T₀ hT Ξ).Q'' = (fun _ => (1 : ℝ)) v := fun v hv =>
  chiP_eq_one_of_isSquare (isSquare_iso Q₀ hQ T₀ hT hiso Ξ) v (by simpa using hv)

include hiso in
/-- With $\lambda_v = 1 - Nv^{-1}$ the local masses $\lambda_v^{-1}\alpha_v(L'')$ of the isotropic $Q''$ have an
absolutely convergent product. -/
theorem multipliable_muLocSO_lamV_iso :
    Multipliable fun v => (muLocSO v (isoTower Q₀ hQ T₀ hT Ξ).Q'' (lamV v)
      (soStabSO v (isoTower Q₀ hQ T₀ hT Ξ).Q'' : Set (SOv v (isoTower Q₀ hQ T₀ hT Ξ).Q''))).toReal := by
  have := multipliable_muLocSO_lamL (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ''
    (χ := fun _ => (1 : ℝ)) (fun v => by simp) _ (hS_iso Q₀ hQ T₀ hT hiso Ξ)
  rwa [lamL_one_eq_lamV] at this

include hiso in
/-- With $\lambda_v = 1 - Nv^{-1}$ the product of the local masses of the isotropic $Q''$ is positive. -/
theorem finFactor_lamV_iso_pos :
    0 < ∏' v, (muLocSO v (isoTower Q₀ hQ T₀ hT Ξ).Q'' (lamV v)
      (soStabSO v (isoTower Q₀ hQ T₀ hT Ξ).Q'' : Set (SOv v (isoTower Q₀ hQ T₀ hT Ξ).Q''))).toReal := by
  have := finFactor_lamL_pos (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ''
    (χ := fun _ => (1 : ℝ)) (fun v => by simp) _ (hS_iso Q₀ hQ T₀ hT hiso Ξ)
  rwa [lamL_one_eq_lamV, finFactor] at this

theorem isoCharV_unit_orbitStab (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)) {e : Fin 2 → F} (he : IsIsoVec D.Q'' e)
    (b : SOAf Q₀) (u : SOAf D.Q'') (hu : u ∈ orbitStab D.ιFin (KSO Q₀) b) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (isoCharV D.hQ'' he v (finComp u v)) = 1 := by
  have hst := (mem_KSO_iff Q₀ _).1 (mem_orbitStab'.1 hu) v
  have hstd : ((evalSO Q₀ v (b * D.ιFin u * b⁻¹) : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F))
      (v.adicCompletion F)) ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v := hst
  have hstd' : (((evalSO Q₀ v (b * D.ιFin u * b⁻¹))⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F))
      (v.adicCompletion F)) ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v := (soStabSO v Q₀).inv_mem hst
  set gv := evalSO Q₀ v (b * D.ιFin u * b⁻¹) with hgv
  set eb := evalSO Q₀ v b with heb
  set ei := evalSO Q₀ v (D.ιFin u) with hei
  have hgv' : gv = eb * ei * eb⁻¹ := by simp only [hgv, heb, hei, map_mul, map_inv]
  set x0 : Fin (r + 2) → v.adicCompletion F :=
    (D.Cm.map (σV v)) *ᵥ ((algebraMap F (v.adicCompletion F)) ∘ e) with hx0def
  have hCV := D.hCV ((1, u) : SOAdele D.Q'') v
  have hspec := isoCharV_spec D.hQ'' he v (finComp u v)
  have hx0 : omat (ei : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *ᵥ x0 =
      isoCharV D.hQ'' he v (finComp u v) • x0 := by
    have h1 : omat (ei : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) =
        matV Q₀ (MonoidHom.prodMap D.ιInf D.ιFin ((1, u) : SOAdele D.Q'')) v := rfl
    have h2 : matV D.Q'' ((1, u) : SOAdele D.Q'') v =
        omat (finComp u v : orthGroup (D.Q''.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) := rfl
    rw [hx0def, mulVec_mulVec, h1, hCV, h2, ← mulVec_mulVec, hspec, mulVec_smul]
  have hx0ne : x0 ≠ 0 := by
    intro h0
    have hCe : D.Cm *ᵥ e = 0 := by
      funext i
      apply (algebraMap F (v.adicCompletion F)).injective
      have := congrFun h0 i
      rw [hx0def, ← RingHom.map_mulVec] at this
      simpa using this
    apply he.1
    refine Matrix.eq_zero_of_mulVec_eq_zero (witt_nd _ D.hQ'') ?_
    rw [← D.hCH, ← mulVec_mulVec, ← mulVec_mulVec, hCe]
    simp
  obtain ⟨x0, hx0, hx0ne⟩ : ∃ x0 : Fin (r + 2) → v.adicCompletion F,
      omat (ei : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *ᵥ x0 =
        isoCharV D.hQ'' he v (finComp u v) • x0 ∧ x0 ≠ 0 := ⟨_, hx0, hx0ne⟩
  have hbb : omat ((eb⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
      omat (eb : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = 1 := by
    rw [← omat_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hMM : omat ((gv⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
      omat (gv : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = 1 := by
    rw [← omat_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hMdec : omat (gv : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) =
      omat (eb : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
        omat (ei : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
        omat ((eb⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) := by
    rw [hgv', ← omat_mul, ← omat_mul]; rfl
  obtain ⟨x1, hx1⟩ : ∃ x1, x1 = omat (eb : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *ᵥ x0 :=
    ⟨_, rfl⟩
  have hx1ne : x1 ≠ 0 := by
    intro h0
    apply hx0ne
    have : omat ((eb⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *ᵥ x1 = x0 := by
      rw [hx1, mulVec_mulVec, hbb, one_mulVec]
    rw [← this, h0]; simp
  have hx1eig : omat (gv : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *ᵥ x1 =
      isoCharV D.hQ'' he v (finComp u v) • x1 := by
    rw [hMdec, hx1]
    generalize omat (eb : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = B at *
    generalize omat (ei : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = Mi at *
    generalize omat ((eb⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = B' at *
    have e2 : B * Mi * B' * B = B * Mi := by rw [Matrix.mul_assoc (B * Mi) B' B, hbb, Matrix.mul_one]
    rw [mulVec_mulVec, e2, ← mulVec_mulVec, hx0, mulVec_smul]
  exact valuation_eigen_eq_one Valued.v _ _
    (fun i j => entry_le_one_of_mem_stdStab v hstd i j) (fun i j => entry_le_one_of_mem_stdStab v hstd' i j)
    hMM x1 hx1ne _ hx1eig

theorem isoNormFin_eq_one_of_units (Q : QuadForm (𝓞 F) 2) (hQ' : Q.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q e)
    (u : SOAf Q) (h : ∀ v, Valued.v (isoCharV hQ' he v (finComp u v)) = 1) : isoNormFin Q hQ' he u = 1 := by
  have hfin : finPart (isoChar hQ' he ((1, u) : SOAdele Q)) ∈ OHatUnits F := by
    rw [finPart_mem_OHatUnits_iff]
    intro v
    exact h v
  have hinf : infPart (isoChar hQ' he ((1, u) : SOAdele Q)) = 1 := by
    apply Units.ext
    show (isoCharInf hQ' he (1 : GInfSO Q), isoCharFin hQ' he u).1 = _
    rw [map_one]; rfl
  unfold isoNormFin ideleNorm
  rw [hinf, finprod_eq_one_of_forall_eq_one fun v => by rw [modAt_eq_one_of_mem hfin v]; rfl]
  simp

/-- **$|\chi(u)|_f = 1$ on the orbit stabilizers.** -/
theorem isoNormFin_orbitStab (b : SOAf Q₀) (u : SOAf (isoTower Q₀ hQ T₀ hT Ξ).Q'')
    (hu : u ∈ orbitStab (isoTower Q₀ hQ T₀ hT Ξ).ιFin (KSO Q₀) b) :
    isoNormFin (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ) u = 1 := by
  exact isoNormFin_eq_one_of_units _ _ _ _ (isoCharV_unit_orbitStab Q₀ hQ T₀ Ξ _ _ b u hu)

/-- **The level groups of the orbit stabilizers are discrete.** -/
theorem discreteTopology_levelGroup_orbitStab (b : SOAf Q₀) (c : SOAf (isoTower Q₀ hQ T₀ hT Ξ).Q'') :
    DiscreteTopology (levelGroup (GammaSOAdele (isoTower Q₀ hQ T₀ hT Ξ).Q'')
      (orbitStab (isoTower Q₀ hQ T₀ hT Ξ).ιFin (KSO Q₀) b) c) :=
  discreteTopology_levelGroup_gen Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) b c

/-- The orbit stabilizer of the representative of an orbit of integral frames is measurable. -/
theorem measurableSet_orbitStab_iso (O : FinOrbit Q₀ T₀ Ξ) :
    MeasurableSet (orbitStab (isoTower Q₀ hQ T₀ hT Ξ).ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O) :
      Set (SOAf (isoTower Q₀ hQ T₀ hT Ξ).Q'')) := by
  exact (orbit_facts Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT (by norm_num) (fun v => lamV_pos v)
    (finFactor_lamV_pos_gen _ (isoTower Q₀ hQ T₀ hT Ξ).hQ'') O).1

/-- The orbit stabilizer of the representative of an orbit of integral frames has positive measure. -/
theorem muFin_orbitStab_iso_ne_zero (O : FinOrbit Q₀ T₀ Ξ) :
    muFin (isoTower Q₀ hQ T₀ hT Ξ).Q'' lamV
      (orbitStab (isoTower Q₀ hQ T₀ hT Ξ).ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) ≠ 0 := by
  exact (orbit_facts Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT (by norm_num) (fun v => lamV_pos v)
    (finFactor_lamV_pos_gen _ (isoTower Q₀ hQ T₀ hT Ξ).hQ'') O).2.1

/-- The orbit stabilizer of the representative of an orbit of integral frames has finite measure. -/
theorem muFin_orbitStab_iso_ne_top (O : FinOrbit Q₀ T₀ Ξ) :
    muFin (isoTower Q₀ hQ T₀ hT Ξ).Q'' lamV
      (orbitStab (isoTower Q₀ hQ T₀ hT Ξ).ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) ≠ ⊤ := by
  exact (orbit_facts Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT (by norm_num) (fun v => lamV_pos v)
    (finFactor_lamV_pos_gen _ (isoTower Q₀ hQ T₀ hT Ξ).hQ'') O).2.2

end QuadFormsKB.Tamagawa.Indefinite
