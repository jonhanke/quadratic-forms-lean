/-
# Hanke 2005: the mass of a totally definite lattice and Theorem 5.1 in the totally definite case

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For $F$ totally real and $Q_0$ totally positive definite, $G_a = \prod_{v\in a}SO_n(\mathbb R)$ is compact, the unit groups
$\Gamma_a$ are finite, and Hanke's mass (1.1) is $\sum_{a\in\mathrm{Cl}}[\Gamma_a:1]^{-1}$. This file proves that the mass in the
form (5.6) (`hankeMass`) is this sum (`hankeMass_definite`): $\tau_a(\Gamma_a\backslash G_a) = \tau_a(G_a)/|\Gamma_a|$ and
$\tau_a(G_a) = \prod_{v\in a}|\det\psi|_v^{-(n+1)/2}\tau_{\mathbb R}(SO_n(\mathbb R)) = \mathrm{vol}_C(C_a)$ (with (4.1.1) and
the repository's `ArchVol.archVolSO_eq_volume`). Since Hanke's classes are proper classes ($G = SO$), the mass is twice
the repository's `Lattices.mass` (classes and automorphisms for $O$): `hankeMass_definite_eq_two_mul_mass`.
-/
import QuadFormsKB.Literature.Hanke2005.MassFormula

open MeasureTheory Measure NumberField IsDedekindDomain Filter Real
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### Helper lemmas -/

/-- **A positive definite real form has Witt index $0$** (it is anisotropic, so $\mathbb H^0\perp Q$ is its Witt
decomposition). -/
theorem wittIndex_eq_zero_of_posDef {Q : QuadForm ℝ n} (hQ : Siegel.IsPosDefR Q) :
    QuadraticForm.wittIndex (QuadForm.toQuadraticForm Q) = 0 := by
  have ha : (QuadForm.toQuadraticForm Q).Anisotropic := fun x hx => by
    by_contra hne
    have := hQ x hne
    rw [QuadForm.toQuadraticForm_apply] at hx
    linarith
  exact (QuadraticForm.eq_wittIndex _ (QuadraticForm.radical_eq_bot_of_anisotropic ha) ha
    (m := 0) ⟨(QuadraticForm.Witt.hyperbolicSpaceZeroProd _).symm⟩).symm

/-- **$r_v = 0$ at every place** for $F$ totally real and $Q_0$ totally positive definite. -/
theorem rAt_eq_zero (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (w : InfinitePlace F) : rAt Q₀ w = 0 := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  unfold rAt
  simp only [hw, ↓reduceDIte]
  exact wittIndex_eq_zero_of_posDef (isPosDefR_map Q₀ _ hQ hpd)


/-- **Embeddings versus places** for a totally real field: $\sigma\mapsto$ the place $\|\sigma(\cdot)\|$ (a bijection
$\mathrm{Hom}(F,\mathbb C)\simeq$ `InfinitePlace F`, via `realPlaceEquiv`). -/
def embPlaceH : (F →ₐ[ℚ] ℂ) ≃ InfinitePlace F :=
  realPlaceEquiv.trans (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w)

/-- The place of an embedding $\sigma$ is $x\mapsto\|\sigma x\|$. -/
theorem embPlaceH_apply (σ : F →ₐ[ℚ] ℂ) (x : F) : embPlaceH σ x = ‖σ x‖ := rfl

/-- **$\mathrm{vol}_C(C_v)$ at a definite place**: $\det\psi_\sigma^{-(n+1)/2}\,\tau_{\mathbb R}(SO_n(\mathbb R))$
(`volCReal_zero`). -/
theorem volCAt_embPlaceH (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (σ : F →ₐ[ℚ] ℂ) :
    volCAt Q₀ (embPlaceH σ) = detGram Q₀ σ ^ (-((n : ℝ) + 1) / 2) * tauR n := by
  have hw : (embPlaceH σ).IsReal := IsTotallyReal.isReal _
  unfold volCAt
  simp only [hw, ↓reduceIte]
  rw [rAt_eq_zero Q₀ hQ hpd, Nat.sub_zero, volCReal_zero, hw.mult_eq_one, pow_one,
    embPlaceH_apply, Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- $\prod_v\mathrm{vol}_C(C_v) = \prod_\sigma\det\psi_\sigma^{-(n+1)/2}\cdot\tau_{\mathbb R}(SO_n(\mathbb R))^{[F:\mathbb Q]}$
in the totally definite case. -/
theorem prod_volCAt (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    ∏ w, volCAt Q₀ w =
      (∏ σ : F →ₐ[ℚ] ℂ, detGram Q₀ σ ^ (-((n : ℝ) + 1) / 2)) * tauR n ^ Module.finrank ℚ F := by
  rw [← Fintype.prod_equiv embPlaceH (fun σ => volCAt Q₀ (embPlaceH σ)) _ (fun _ => rfl)]
  simp only [volCAt_embPlaceH Q₀ hQ hpd]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, AlgHom.card]

/-- `archVolSO m d = d^{-(m+1)/2} · archVolSO m 1`. -/
theorem archVolSO_eq_rpow_mul (m : ℕ) (d : ℝ) :
    archVolSO m d = d ^ (-((m : ℝ) + 1) / 2) * archVolSO m 1 := by
  unfold archVolSO
  rw [Real.one_rpow]; ring

/-- **Total mass of `muArchTamSO`** (totally definite): $c_F\prod_\sigma$ `archVolSO n (detGram σ)`. -/
theorem muArchTamSO_univH (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    muArchTamSO Q₀ hQ Set.univ =
      ENNReal.ofReal (cF F n) * ∏ σ : F →ₐ[ℚ] ℂ, ENNReal.ofReal (archVolSO n (detGram Q₀ σ)) := by
  rw [← map_muInfTam Q₀ hQ hn hpd, Measure.map_apply (measurable_archEquivM1d Q₀) MeasurableSet.univ,
    Set.preimage_univ, muInfTam_univ]

/-- **Total mass of Hanke's archimedean measure** (totally definite): $\tau_a(G_a) = \prod_v\mathrm{vol}_C(C_v)$. -/
theorem muArchHanke_univ (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    muArchHanke Q₀ hQ Set.univ = ENNReal.ofReal (∏ w, volCAt Q₀ w) := by
  have hcF : 0 < cF F n := by
    unfold cF
    have hd : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    positivity
  have hpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 ≤ archVolSO n (detGram Q₀ σ) := fun σ => (archVolSO_detGram_pos Q₀ hQ σ).le
  rw [muArchHanke, Measure.smul_apply, smul_eq_mul, muArchTamSO_univH Q₀ hQ hn hpd,
    ← ENNReal.ofReal_prod_of_nonneg (fun σ _ => hpos σ), ← ENNReal.ofReal_mul hcF.le,
    ← ENNReal.ofReal_mul (archHankeConst_pos (F := F) (n := n)).le, prod_volCAt Q₀ hQ hpd]
  congr 1
  have h1 : archHankeConst F n * cF F n = (2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)) := by
    unfold archHankeConst; field_simp
  simp only [archVolSO_eq_rpow_mul n (detGram Q₀ _), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    AlgHom.card]
  rw [← mul_assoc, h1, tauR_eq_two_pow_mul_archVolSO, mul_pow, ← pow_mul]
  ring

/-- **Covolume of a finite subgroup:** if $\Gamma$ is finite with an exact measurable fundamental domain in $G$ for a
left-invariant measure $\mu$, then $\mathrm{covol}(\Gamma)\cdot|\Gamma| = \mu(G)$. -/
theorem covolume_mul_card_of_finite {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) [Finite Γ] (μ : Measure G) [μ.IsMulLeftInvariant] {D : Set G} (hD : MeasurableSet D)
    (hfd : ∀ a : G, ∃! s : Γ, s • a ∈ D) :
    covolume Γ G μ * (Nat.card Γ : ℝ≥0∞) = μ Set.univ := by
  have : Fintype Γ := Fintype.ofFinite Γ
  have hdom : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hD.nullMeasurableSet hfd
  rw [hdom.covolume_eq_volume μ, hdom.measure_eq_tsum' Set.univ, tsum_fintype]
  simp only [Set.univ_inter, measure_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

/-- **$|\Gamma_b| = |\Gamma_f\cap bKb^{-1}|$:** for $\Gamma\le A\times B$ projecting injectively to both factors, the level
group $\Gamma_b\le A$ has the cardinality of the stabilizer of $bK$ in the image of $\Gamma$ in $B$. -/
theorem card_levelGroup_eq {A B : Type*} [Group A] [Group B] (Γ : Subgroup (A × B)) (K : Subgroup B) (b : B)
    (h1 : ∀ γ ∈ Γ, γ.1 = 1 → γ = 1) (h2 : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1) :
    Nat.card (levelGroup Γ K b) =
      Nat.card (MulAction.stabilizer (Γ.map (MonoidHom.snd A B)) (QuotientGroup.mk b : B ⧸ K)) := by
  have hmem : ∀ γ : levelStab Γ K b, γ.1 ∈ Γ ∧ b⁻¹ * γ.1.2 * b ∈ K := fun γ => γ.2
  let φ : levelStab Γ K b → MulAction.stabilizer (Γ.map (MonoidHom.snd A B)) (QuotientGroup.mk b : B ⧸ K) :=
    fun γ => ⟨⟨γ.1.2, Subgroup.mem_map.mpr ⟨γ.1, (hmem γ).1, rfl⟩⟩,
      (mem_stabilizer_coset _ _ _ _).mpr (hmem γ).2⟩
  let ψ : levelStab Γ K b → levelGroup Γ K b := fun γ => ⟨γ.1.1, Subgroup.mem_map.mpr ⟨γ.1, γ.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro γ γ' h
      have e : γ.1.2 = γ'.1.2 := congrArg (fun z => ((z : Subgroup.map _ _) : B)) (congrArg Subtype.val h)
      apply Subtype.ext
      have := h2 (γ.1 * γ'.1⁻¹) (Γ.mul_mem (hmem γ).1 (Γ.inv_mem (hmem γ').1))
        (by simp [e])
      exact mul_inv_eq_one.mp this
    · rintro ⟨⟨x, hx⟩, hs⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨g, hg, (mem_stabilizer_coset _ _ _ ⟨_, hx⟩).mp hs⟩, rfl⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro γ γ' h
      have e : γ.1.1 = γ'.1.1 := congrArg Subtype.val h
      apply Subtype.ext
      have := h1 (γ.1 * γ'.1⁻¹) (Γ.mul_mem (hmem γ).1 (Γ.inv_mem (hmem γ').1))
        (by simp [e])
      exact mul_inv_eq_one.mp this
    · rintro ⟨a, ha⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      exact ⟨⟨g, hg⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective ψ hψ)).symm.trans (Nat.card_congr (Equiv.ofBijective φ hφ))

/-- The finite-adelic projection of `GammaSOAdele` is `GammaSOf` (as `map_snd_GammaSO` for `GammaSO`). -/
theorem map_snd_GammaSOAdele (Q₀ : QuadForm (𝓞 F) n) :
    (GammaSOAdele Q₀).map (MonoidHom.snd (GInfSO Q₀) (SOAf Q₀)) = GammaSOf Q₀ := by
  rw [← map_snd_GammaSO]
  unfold GammaSOAdele GammaSO
  rw [MonoidHom.map_range, MonoidHom.map_range]
  congr 1

/-- **Unit groups and `dcMass`** (totally definite): every $\Gamma_i$ is finite and $\sum_i|\Gamma_i|^{-1} =$
`dcMass` $(SO(V)(F), SO(\hat L))$ (the double cosets `DC` are the $\Gamma_f$-orbits on $SO(V)(\mathbb A_f)/SO(\hat L)$
and $\Gamma_i\cong\mathrm{Stab}(\beta_iK)$). -/
theorem tsum_inv_card_unitGroup (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n).1) :
    (∀ i : DC Q₀, Finite (unitGroup Q₀ i)) ∧
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (dcMass (GammaSOf Q₀) (KSO Q₀)) := by
  have hfinQ := finite_orbits_SO Q₀ hQ hn hpd hLi
  have hmap := map_snd_GammaSOAdele Q₀
  -- the card comparison
  have hcard : ∀ i : DC Q₀, Nat.card (unitGroup Q₀ i) =
      Nat.card (MulAction.stabilizer (GammaSOf Q₀) (QuotientGroup.mk (dcRep Q₀ i) : SOAf Q₀ ⧸ KSO Q₀)) := by
    intro i
    have := card_levelGroup_eq (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
      (fun γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ h1) (GammaSOAdele_inj Q₀)
    rw [hmap] at this
    exact this
  have hfin : ∀ i : DC Q₀, Finite (unitGroup Q₀ i) := by
    intro i
    have h := finite_stabilizer_SO Q₀ hpd hLi (QuotientGroup.mk (dcRep Q₀ i) : SOAf Q₀ ⧸ KSO Q₀)
    have : 0 < Nat.card (unitGroup Q₀ i) := by rw [hcard i]; exact Nat.card_pos
    exact Nat.finite_of_card_ne_zero this.ne'
  refine ⟨hfin, ?_⟩
  -- the bijection of double cosets with orbits
  let Φ : DC Q₀ → MulAction.orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀) :=
    fun i => Quotient.mk'' (QuotientGroup.mk (dcRep Q₀ i))
  have hΦinj : Function.Injective Φ := by
    intro i j h
    have h1 := Quotient.exact' h
    rw [MulAction.orbitRel_apply] at h1
    obtain ⟨g, hg⟩ := h1
    have hg' : (g : SOAf Q₀) • (QuotientGroup.mk (dcRep Q₀ j) : SOAf Q₀ ⧸ KSO Q₀) =
        QuotientGroup.mk (dcRep Q₀ i) := hg
    have hg2 : (QuotientGroup.mk ((g : SOAf Q₀) * dcRep Q₀ j) : SOAf Q₀ ⧸ KSO Q₀) = QuotientGroup.mk (dcRep Q₀ i) := hg'
    rw [QuotientGroup.eq] at hg2
    have hgm : (g : SOAf Q₀) ∈ (GammaSOAdele Q₀).map (MonoidHom.snd (GInfSO Q₀) (SOAf Q₀)) := by
      rw [hmap]; exact g.2
    obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp hgm
    refine (dcRep_disj Q₀ j i γ hγ _ hg2 1 (KSO Q₀).one_mem ?_).symm
    simp only [MonoidHom.coe_snd] at hγg
    rw [hγg]; group
  have hΦsurj : Function.Surjective Φ := by
    intro ω
    induction ω using Quotient.inductionOn' with | h y => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    obtain ⟨i, γ, hγ, k, hk, hb⟩ := dcRep_cov Q₀ b
    refine ⟨i, (Quotient.sound' ?_).symm⟩
    rw [MulAction.orbitRel_apply]
    have hgm : γ.2 ∈ GammaSOf Q₀ := by
      rw [← hmap]; exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    refine ⟨⟨γ.2, hgm⟩, ?_⟩
    show (QuotientGroup.mk (γ.2 * dcRep Q₀ i) : SOAf Q₀ ⧸ KSO Q₀) = QuotientGroup.mk b
    rw [QuotientGroup.eq, hb]
    simpa [mul_assoc] using (KSO Q₀).inv_mem hk
  have hΦ : Function.Bijective Φ := ⟨hΦinj, hΦsurj⟩
  have hterm : ∀ i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ((Nat.card (MulAction.stabilizer (GammaSOf Q₀) (Φ i).out) : ℝ≥0∞))⁻¹ := by
    intro i
    rw [hcard i, card_stabilizer_of_mem_orbit (out_mem_orbit (Φ i) _ rfl)]
  simp only [hterm]
  refine (Equiv.tsum_eq (Equiv.ofBijective Φ hΦ)
    (fun ω => ((Nat.card (MulAction.stabilizer (GammaSOf Q₀) ω.out) : ℝ≥0∞))⁻¹)).trans ?_
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀))
  rw [tsum_fintype]
  unfold dcMass orbitMass
  rw [finsum_eq_sum_of_fintype, ENNReal.ofReal_sum_of_nonneg (fun ω _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have := finite_stabilizer_SO Q₀ hpd hLi ω.out
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Nat.card_pos), ENNReal.ofReal_natCast]

/-- $\det\psi_\sigma > 0$ (nonzero for nondegenerate $Q_0$). -/
theorem detGram_posH (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (σ : F →ₐ[ℚ] ℂ) : 0 < detGram Q₀ σ := by
  refine norm_pos_iff.mpr ?_
  rw [map_div₀, div_ne_zero_iff]
  refine ⟨(map_ne_zero_iff _ σ.toRingHom.injective).mpr ?_, (map_ne_zero_iff _ σ.toRingHom.injective).mpr
    (pow_ne_zero _ two_ne_zero)⟩
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

/-- $\prod_v\mathrm{vol}_C(C_v) > 0$ in the totally definite case. -/
theorem prod_volCAt_pos (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : 0 < ∏ w, volCAt Q₀ w := by
  rw [prod_volCAt Q₀ hQ hpd]
  exact mul_pos (Finset.prod_pos fun σ _ => Real.rpow_pos_of_pos (detGram_posH Q₀ hQ σ) _)
    (pow_pos (tauR_pos n) _)

/-- **Hanke's mass of a totally definite lattice** (thesis, (1.1), p. 2, and (5.5), first case, p. 16): for $F$ totally
real and $Q_0$ totally positive definite ($G_a$ compact), $\mathrm{Mass}(\Lambda,\varphi) = \sum_{a\in\mathrm{Cl}}[\Gamma_a:1]^{-1}$,
and this is `hankeMass` (the form (5.6)). -/
@[kb "hanke2005crelle" "(1.1), p. 2; (5.5)–(5.6), pp. 16–17 (definite case)"]
theorem hankeMass_definite (hn : 1 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    hankeMass Q₀ hQ = ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ := by
  have hLi := HilbertModular.isIntegral_stdLat Q₀
  obtain ⟨hfin, -⟩ := tsum_inv_card_unitGroup Q₀ hQ hn hpd hLi
  have hP := prod_volCAt_pos Q₀ hQ hpd
  have hP0 : ENNReal.ofReal (∏ w, volCAt Q₀ w) ≠ 0 := (ENNReal.ofReal_pos.mpr hP).ne'
  have hPT : ENNReal.ofReal (∏ w, volCAt Q₀ w) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcov : ∀ i : DC Q₀, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (∏ w, volCAt Q₀ w) * ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ := by
    intro i
    have := hfin i
    obtain ⟨D, hD, hfd⟩ := exists_fd_levelGroup Q₀ (dcRep Q₀ i)
    have h := covolume_mul_card_of_finite (unitGroup Q₀ i) (muArchHanke Q₀ hQ) hD hfd
    rw [muArchHanke_univ Q₀ hQ hn hpd] at h
    have hc0 : (Nat.card (unitGroup Q₀ i) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← div_eq_mul_inv, ENNReal.eq_div_iff hc0 (ENNReal.natCast_ne_top _), mul_comm]
    exact h
  unfold hankeMass
  simp only [hcov]
  rw [ENNReal.tsum_mul_left, div_eq_mul_inv, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel hP0 hPT, one_mul]


/-- **Hanke's mass is twice the repository's mass** (totally definite case): $\sum_{a}1/|SO(M_a)| = 2\sum_{[M]}1/|O(M)|$,
the second sum over the classes of the genus of $\mathcal O_F^n$ for the full orthogonal group (`Lattices.mass`). -/
theorem hankeMass_definite_eq_two_mul_mass (hn : 1 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    hankeMass Q₀ hQ = ENNReal.ofReal (2 * mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
  have hLi := HilbertModular.isIntegral_stdLat Q₀
  rw [hankeMass_definite hn Q₀ hQ hpd, (tsum_inv_card_unitGroup Q₀ hQ hn hpd hLi).2,
    mass_SO_eq_two_mul_mass Q₀ hQ hn hpd hLi]



/-- **Theorem 5.1, totally definite case** (Hanke thesis, Theorem 5.1, Part 1, pp. 17–18; agrees with Shimura's formula
over totally real fields): for $F$ totally real, $Q_0$ totally positive definite in $n\ge3$ variables with
$\mathcal O_F^n$ maximal and Shimura's hypothesis, $\sum_a[\Gamma_a:1]^{-1}$ is the right side of Theorem 5.1. Conditional on
`ShimuraMaximalDensity F` and `ShimuraMaximalTypes F`. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite)"]
theorem theorem51_definite (I₁ : ShimuraMaximalDensity F) (I₂ : ShimuraMaximalTypes F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) := by
  rw [← hankeMass_definite (by omega) Q₀ hQ hpd]
  exact theorem51 I₁ I₂ hn Q₀ hQ hmax hdet

end QuadFormsKB.Hanke2005
