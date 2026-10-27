import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Iso

/-!
# $\tau(\mathrm{SL}_1(D)) < \infty$ for split $D$, and the reduction of $\tau(\mathrm{SL}_1(D)) = 1$ to a measure identity

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus 0$, $x, y\in F$ with $x^2 - ay^2 = b$, so that
$D = \mathbb H[F,a,b]\cong M_2(F)$; $\psi : \mathrm{SL}_1(D)(\mathbb A)\cong\mathrm{SL}_2(\mathbb A_F)$ is `sl1SplitEquiv`.

The quotient is Weil's $G_{\mathbb A}/G_k$ for the right action $\gamma\cdot g = g\gamma^{-1}$ (`slRightAction`), while
`SL1F` acts on `SL1A` by left multiplication. The two are exchanged by $g\mapsto g^{-1}$, which preserves Haar measure
because $\mathrm{SL}_2(\mathbb A_F)$ is unimodular.

**Proves**
* `continuous_modularCharacter` (any locally compact group): the modular character is continuous.
* `isMulRightInvariant_of_rightFD` (any locally compact group): a left Haar measure with a fundamental domain of finite
  positive measure for a right-type action (commuting with left translations, preserving the modular character) is
  right invariant. *Proof.* $\Delta$ descends to the quotient; left translation by $g$ moves the level sets
  $\{t\le\Delta < rt\}$, $r = \Delta(g)$, to $\{rt\le\Delta < r^2t\}$ without changing their measure in a fundamental
  domain, so a finite total forces $\Delta(g) = 1$.
* `isMulRightInvariant_muT`, `map_inv_eq_self_SL2A`: $\mathrm{SL}_2(\mathbb A_F)$ is unimodular, and every Haar measure on it
  is inversion invariant.
* `covolume_SL1F_eq_covolume_map`: $\operatorname{covol}(\mathrm{SL}_1(D)(F)\backslash\mathrm{SL}_1(D)(\mathbb A),\mu) =
  \operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F),\psi_*\mu)$ for every Haar measure $\mu$.
* **`covolume_muSL1_ne_top_of_split`**: $\tau(\mathrm{SL}_1(D)) < \infty$ for split $D$, hence
  **`covolume_muPD_eq_two_mul_of_split`**: $\tau(PD^\times) = 2\,\tau(\mathrm{SL}_1(D))$.
* **`covolume_muSL1_ne_top`**, **`covolume_muPD_eq_two_mul_covolume_muSL1`**: the same for every quaternion algebra
  (including division algebras), unconditionally.
* **`tauSL1EqOne_of_map_eq_muT`**: $\tau(\mathrm{SL}_1(D)) = 1$ as soon as $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$
  (the fibration measure); this measure identity is what remains for split $D$.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal MatrixGroups Pointwise Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Unimodularity from a lattice for a right-type action -/

section Unimodular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **The modular character is continuous** (any locally compact group). -/
theorem continuous_modularCharacter : Continuous fun g : G => (Measure.modularCharacter g : ℝ) := by
  borelize G
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  set μ : Measure G := Measure.haar
  have hint : ∫ x, f x ∂μ ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  have key : ∀ g : G, (Measure.modularCharacter g : ℝ) = (∫ y, f (y⁻¹ * g) ∂μ.inv) / ∫ x, f x ∂μ := by
    intro g
    change (Measure.modularCharacterFun g : ℝ) = _
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g,
      Measure.haarScalarFactor_eq_integral_div _ _ f_cont f_comp hint,
      integral_map (AEMeasurable.mul_const aemeasurable_id' _) f_cont.aestronglyMeasurable, Measure.inv,
      integral_map measurable_inv.aemeasurable
        ((by fun_prop : Continuous fun y : G => f (y⁻¹ * g)).aestronglyMeasurable)]
    simp
  simp_rw [key]
  exact (continuous_integral_apply_inv_mul f_cont f_comp).div_const _

variable [MeasurableSpace G] [BorelSpace G]

/-- **A left Haar measure with a fundamental domain of finite positive measure for a right-type action is right
invariant** (the action commutes with left translations and preserves the modular character, e.g.
$\gamma\cdot g = g\gamma^{-1}$ for a lattice $\Gamma$ on which $\Delta$ is trivial). -/
theorem isMulRightInvariant_of_rightFD (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    {Γ : Type*} [Group Γ] [Countable Γ] [MulAction Γ G] [MeasurableConstSMul Γ G]
    (hcomm : ∀ (γ : Γ) (g x : G), γ • (g * x) = g * (γ • x))
    (hΔ : ∀ (γ : Γ) (x : G), Measure.modularCharacter (γ • x) = Measure.modularCharacter x)
    [SMulInvariantMeasure Γ G μ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (h0 : μ D ≠ 0) (htop : μ D ≠ ∞) :
    μ.IsMulRightInvariant := by
  set Δ : G → ℝ := fun g => (Measure.modularCharacter g : ℝ)
  have hΔm : Measurable Δ := continuous_modularCharacter.measurable
  have hΔpos : ∀ g, 0 < Δ g := fun g => Measure.modularCharacterFun_pos g
  have hΔmul : ∀ g h, Δ (g * h) = Δ g * Δ h := fun g h => by simp [Δ, map_mul]
  have hΔinv : ∀ g, Δ g⁻¹ = (Δ g)⁻¹ := fun g => by simp [Δ, map_inv]
  -- level sets
  set S : ℝ → ℝ → Set G := fun r t => Δ ⁻¹' Ico t (r * t)
  have hSm : ∀ r t, MeasurableSet (S r t) := fun r t => hΔm measurableSet_Ico
  have hSinv : ∀ r t (γ : Γ), (fun x => γ • x) ⁻¹' S r t = S r t := fun r t γ => by
    ext x; simp only [S, mem_preimage, Δ, hΔ]
  -- left translates of `D` are fundamental domains
  have hgD : ∀ g : G, IsFundamentalDomain Γ ((fun x => g⁻¹ * x) ⁻¹' D) μ := fun g =>
    hD.preimage_of_equiv (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving Function.bijective_id
      fun γ x => by simp [hcomm]
  -- the shift
  have hshift : ∀ g : G, ∀ t, μ (S (Δ g) (Δ g * t) ∩ D) = μ (S (Δ g) t ∩ D) := by
    intro g t
    have hpre : (fun x => g⁻¹ * x) ⁻¹' S (Δ g) t = S (Δ g) (Δ g * t) := by
      ext x
      have hg := hΔpos g
      simp only [S, mem_preimage, mem_Ico, hΔmul, hΔinv]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · have := mul_le_mul_of_nonneg_left h1 hg.le
          rwa [← mul_assoc, mul_inv_cancel₀ hg.ne', one_mul] at this
        · have := mul_lt_mul_of_pos_left h2 hg
          rwa [← mul_assoc, mul_inv_cancel₀ hg.ne', one_mul] at this
      · rintro ⟨h1, h2⟩
        constructor
        · have := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hg).le
          rwa [← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul] at this
        · have := mul_lt_mul_of_pos_left h2 (inv_pos.2 hg)
          rwa [← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul] at this
    rw [hD.measure_set_eq (hgD g) (hSm _ _) (hSinv _ _), ← hpre, ← preimage_inter,
      measure_preimage_mul]
  -- `Δ g ≤ 1` for every `g`
  have hle : ∀ g : G, Δ g ≤ 1 := by
    intro g
    by_contra hlt
    push Not at hlt
    set r := Δ g
    have hr0 : 0 < r := hΔpos g
    -- every level set `[t, rt)` with `t > 0` is null in `D`
    have hnull : ∀ t, 0 < t → μ (S r t ∩ D) = 0 := by
      intro t ht
      have hn : ∀ n : ℕ, μ (S r (r ^ n * t) ∩ D) = μ (S r t ∩ D) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', mul_assoc, hshift g, ih]
      have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => S r (r ^ n * t) ∩ D) := by
        intro m n hmn
        wlog hlt' : m < n generalizing m n
        · exact (this hmn.symm (lt_of_le_of_ne (not_lt.1 hlt') hmn.symm)).symm
        refine Set.disjoint_left.2 fun x hx hy => ?_
        have h1 : Δ x < r * (r ^ m * t) := hx.1.2
        have h2 : r ^ n * t ≤ Δ x := hy.1.1
        have h3 : r * (r ^ m * t) ≤ r ^ n * t := by
          rw [← mul_assoc, ← pow_succ']
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlt.le hlt') ht.le
        linarith
      have hsum : ∑' n : ℕ, μ (S r (r ^ n * t) ∩ D) ≤ μ D := by
        rw [← measure_iUnion₀ (hdisj.mono fun i j h => h.aedisjoint)
          fun n => (hSm _ _).nullMeasurableSet.inter hD.nullMeasurableSet]
        exact measure_mono (iUnion_subset fun n => inter_subset_right)
      simp_rw [hn] at hsum
      by_contra hne
      rw [ENNReal.tsum_const_eq_top_of_ne_zero hne, top_le_iff] at hsum
      exact htop hsum
    -- `D` is covered by the level sets `[r^k, r^{k+1})`
    have hcover : D ⊆ ⋃ k : ℤ, S r (r ^ k) ∩ D := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (hΔpos x) hlt
      refine mem_iUnion.2 ⟨k, ⟨?_, hx⟩⟩
      simp only [S, mem_preimage, mem_Ico]
      rw [← zpow_one_add₀ hr0.ne', add_comm]
      exact hk
    exact h0 (measure_mono_null hcover (measure_iUnion_null fun k => hnull _ (zpow_pos hr0 k)))
  have h1 : ∀ g : G, Measure.modularCharacterFun g = 1 := by
    intro g
    have a1 := hle g
    have a2 := hle g⁻¹
    rw [hΔinv] at a2
    have hg := hΔpos g
    have : Δ g = 1 := le_antisymm a1 (by
      by_contra h; push Not at h
      have := (one_lt_inv₀ hg).2 h
      linarith)
    exact NNReal.coe_eq_one.1 this
  refine ⟨fun g => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul, h1, one_smul]

/-- A left and right invariant Haar measure on a second-countable group is inversion invariant. -/
theorem map_inv_eq_self_of_isMulRightInvariant [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] : μ.map (fun x => x⁻¹) = μ := by
  have hH : μ.inv.IsHaarMeasure :=
    { lt_top_of_isCompact := fun K hK => hK.measure_lt_top
      toIsOpenPosMeasure := by
        refine ⟨fun U hU hne => ?_⟩
        rw [Measure.inv_apply]
        exact (hU.inv).measure_ne_zero μ hne.inv }
  set c := haarScalarFactor μ.inv μ
  have hc : μ.inv = (c : ℝ≥0∞) • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have hsm : ((c : ℝ≥0∞) • μ).inv = (c : ℝ≥0∞) • μ.inv := by
    unfold Measure.inv; exact Measure.map_smul _ measurable_inv.aemeasurable
  have hcc : μ = ((c : ℝ≥0∞) * c) • μ := by
    have h2 : μ.inv.inv = μ := Measure.inv_inv μ
    rw [hc, hsm, hc, smul_smul] at h2
    exact h2.symm
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts G))
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK := congrArg (fun ν : Measure G => ν K) hcc
  simp only [Measure.smul_apply, smul_eq_mul] at hK
  have hcc' : (c : ℝ≥0∞) * c = 1 := by
    have : (c : ℝ≥0∞) * c * μ K = 1 * μ K := by rw [one_mul]; exact hK.symm
    exact (ENNReal.mul_left_inj h0 ht).1 this
  have hc1 : c = 1 := by
    have : c * c = 1 := by exact_mod_cast hcc'
    nlinarith [c.2, sq_nonneg ((c : ℝ) - 1), show ((c : ℝ)) * c = 1 by exact_mod_cast this]
  change μ.inv = μ
  rw [hc, hc1, ENNReal.coe_one, one_smul]

end Unimodular

/-! ### $\mathrm{SL}_2(\mathbb A_F)$ is unimodular -/

variable {F : Type} [Field F] [NumberField F]

/-- **$\mathrm{SL}_2(\mathbb A_F)$ is unimodular**: $\mu_T$ is right invariant (it has the lattice $\mathrm{SL}_2(F)$ for the
right action, `covolume_muT_lt_top`, and $\Delta$ is trivial on $\mathrm{SL}_2(F)$, `modularCharacter_slEmb`). -/
theorem isMulRightInvariant_muT : (muT F).IsMulRightInvariant := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  have hFD : IsFundamentalDomain (SL(2, F)) D (muT F) := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  refine isMulRightInvariant_of_rightFD (muT F) (Γ := SL(2, F)) (fun γ g x => ?_) (fun γ x => ?_) hFD
    (muT_fundDomain_ne_zero hFD) (muT_fundDomain_lt_top hFD).ne
  · simp only [slRight_smul_def, mul_assoc]
  · rw [slRight_smul_def, map_mul, map_inv, modularCharacter_slEmb, inv_one, mul_one]

/-- Every Haar measure on $\mathrm{SL}_2(\mathbb A_F)$ is right invariant. -/
theorem isMulRightInvariant_SL2A (μ : Measure (SL2A F)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have := isMulRightInvariant_muT (F := F)
  rw [isMulLeftInvariant_eq_smul μ (muT F)]
  infer_instance

/-- **Every Haar measure on $\mathrm{SL}_2(\mathbb A_F)$ is inversion invariant.** -/
theorem map_inv_eq_self_SL2A (μ : Measure (SL2A F)) [μ.IsHaarMeasure] : μ.map (fun x => x⁻¹) = μ := by
  have := isMulRightInvariant_SL2A μ
  exact map_inv_eq_self_of_isMulRightInvariant μ

/-- Haar measures on $\mathrm{SL}_2(\mathbb A_F)$ are invariant under the right action of $\mathrm{SL}_2(F)$. -/
theorem smulInvariantMeasure_SL2A (μ : Measure (SL2A F)) [μ.IsHaarMeasure] :
    SMulInvariantMeasure (SL(2, F)) (SL2A F) μ := by
  have := isMulRightInvariant_SL2A μ
  exact ⟨fun γ s _ => by
    change μ ((fun g => g * (slEmb F γ)⁻¹) ⁻¹' s) = μ s
    exact measure_preimage_mul_right μ _ s⟩

/-! ### Transport of the covolume along $\psi$ -/

section Transport

variable {a b x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

theorem sl1SplitEquiv_symm_slEmb_mem (γ : SL(2, F)) : (sl1SplitEquiv ha0 hb0 h).symm (slEmb F γ) ∈ SL1F a b := by
  rw [mem_SL1F_iff_sl1SplitEquiv_mem ha0 hb0 h, ContinuousMulEquiv.apply_symm_apply]
  exact ⟨γ, rfl⟩

/-- The bijection $\mathrm{SL}_2(F)\to\mathrm{SL}_1(D)(F)$, $\gamma\mapsto\psi^{-1}(\gamma)$. -/
def slToSL1F (γ : SL(2, F)) : SL1F a b := ⟨_, sl1SplitEquiv_symm_slEmb_mem ha0 hb0 h γ⟩

theorem slToSL1F_bijective : Function.Bijective (slToSL1F ha0 hb0 h) := by
  refine ⟨fun γ δ hγδ => ?_, fun ε => ?_⟩
  · have := congrArg (fun ε : SL1F a b => sl1SplitEquiv ha0 hb0 h (ε : SL1A a b)) hγδ
    simp only [slToSL1F, ContinuousMulEquiv.apply_symm_apply] at this
    exact slEmb_injective this
  · obtain ⟨γ, hγ⟩ := (mem_SL1F_iff_sl1SplitEquiv_mem ha0 hb0 h ε).1 ε.2
    refine ⟨γ, Subtype.ext ?_⟩
    change (sl1SplitEquiv ha0 hb0 h).symm (slEmb F γ) = ε
    rw [hγ, ContinuousMulEquiv.symm_apply_apply]

set_option maxHeartbeats 1000000 in
/-- An exact fundamental domain $D_K$ for the left action of $\mathrm{SL}_1(D)(F)$ gives the exact fundamental domain
$\{g : \psi^{-1}(g^{-1})\in D_K\}$ for the right action of $\mathrm{SL}_2(F)$. -/
theorem isExactFD_right_of_SL1F {DK : Set (SL1A a b)} (hDK : IsExactFD (Γ := SL1F a b) DK) :
    IsExactFD (Γ := SL(2, F)) ((fun g : SL2A F => (sl1SplitEquiv ha0 hb0 h).symm g⁻¹) ⁻¹' DK) := by
  set ψ := sl1SplitEquiv ha0 hb0 h
  have hψm : Measurable fun g : SL2A F => ψ.symm g⁻¹ := (ψ.symm.continuous.comp continuous_inv).measurable
  refine ⟨hψm hDK.1, fun g => ?_⟩
  have hsm : ∀ γ : SL(2, F), ψ.symm (γ • g)⁻¹ = slToSL1F ha0 hb0 h γ • ψ.symm g⁻¹ := by
    intro γ
    rw [Subgroup.smul_def, slRight_smul_def, mul_inv_rev, inv_inv, map_mul]
    rfl
  obtain ⟨ε, hε, huniq⟩ := hDK.2 (ψ.symm g⁻¹)
  obtain ⟨γ, rfl⟩ := (slToSL1F_bijective ha0 hb0 h).2 ε
  refine ⟨γ, ?_, fun δ hδ => ?_⟩
  · show ψ.symm (γ • g)⁻¹ ∈ DK
    rw [hsm γ]; exact hε
  · have hδ' : ψ.symm (δ • g)⁻¹ ∈ DK := hδ
    rw [hsm δ] at hδ'
    have : slToSL1F ha0 hb0 h δ = slToSL1F ha0 hb0 h γ := huniq _ hδ'
    exact (slToSL1F_bijective ha0 hb0 h).1 this

/-- **$\operatorname{covol}(\mathrm{SL}_1(D)(F)\backslash\mathrm{SL}_1(D)(\mathbb A),\mu) =
\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F),\psi_*\mu)$** for every Haar measure $\mu$ on
$\mathrm{SL}_1(D)(\mathbb A)$. -/
theorem covolume_SL1F_eq_covolume_map (μ : Measure (SL1A a b)) [μ.IsHaarMeasure] :
    covolume (SL1F a b) (SL1A a b) μ =
      covolume (SL(2, F)) (SL2A F) (μ.map (sl1SplitEquiv ha0 hb0 h)) := by
  set ψ := sl1SplitEquiv ha0 hb0 h
  have hν : (μ.map ψ).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have := smulInvariantMeasure_SL2A (μ.map ψ)
  have : SMulInvariantMeasure (SL1F a b) (SL1A a b) μ := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := a) (b := b)
  have hE := isExactFD_right_of_SL1F ha0 hb0 h hDK
  rw [(hDK.isFundamentalDomain μ).covolume_eq_volume, (hE.isFundamentalDomain _).covolume_eq_volume]
  have hψm : Measurable ψ := ψ.continuous.measurable
  have hψsm : Measurable ψ.symm := ψ.symm.continuous.measurable
  have hpre : (fun g : SL2A F => ψ.symm g⁻¹) ⁻¹' DK = (fun g => g⁻¹) ⁻¹' (ψ.symm ⁻¹' DK) := rfl
  rw [hpre, ← Measure.map_apply measurable_inv (hψsm hDK.1), map_inv_eq_self_SL2A,
    Measure.map_apply hψm (hψsm hDK.1), ← preimage_comp]
  congr 1
  ext k; simp [ψ]

end Transport

/-! ### Finiteness and the reduction of `TauSL1EqOne` -/

section Integral

variable {a b : NumberField.RingOfIntegers F} {x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
  (h : x ^ 2 - (a : F) * y ^ 2 = (b : F))

include h in
/-- **$\tau(\mathrm{SL}_1(D)) < \infty$ for split $D$** (the finiteness for $\mathrm{SL}_2$, transported along $\psi$). -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) < ∞) [unverified locator]"]
theorem covolume_muSL1_ne_top_of_split :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) ≠ ∞ := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have := isHaarMeasure_muSL1 (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  rw [covolume_SL1F_eq_covolume_map ha0' hb0' h]
  set ν := (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0').map (sl1SplitEquiv ha0' hb0' h)
  have : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have := smulInvariantMeasure_SL2A ν
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  have hFD : IsFundamentalDomain (SL(2, F)) D ν := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  rw [hFD.covolume_eq_volume]
  exact (haar_fundDomain_lt_top ν hFD).1.ne

include h in
/-- **$\tau(PD^\times) = 2\,\tau(\mathrm{SL}_1(D))$ for split $D$**, unconditionally. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (τ(PD^×) = 2 via τ(SL₁) and the centre)"]
theorem covolume_muPD_eq_two_mul_of_split :
    covolume (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) =
      2 * covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
        (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) :=
  covolume_muPD_eq_two_mul a b ha0 hb0 (covolume_muSL1_ne_top_of_split ha0 hb0 h)

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ for split $D$ once $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$** (`tamagawa_SL2`). -/
theorem covolume_muSL1_eq_one_of_map_eq_muT
    (hmap : (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)).map
      (sl1SplitEquiv (by simpa using ha0) (by simpa using hb0) h) = muT F) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 1 := by
  have := isHaarMeasure_muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0)
    (by simpa using hb0)
  rw [covolume_SL1F_eq_covolume_map (by simpa using ha0) (by simpa using hb0) h, hmap]
  exact tamagawa_SL2

end Integral

section Every

variable (a b : NumberField.RingOfIntegers F)

/-- **$\tau(\mathrm{SL}_1(D)) < \infty$ for every quaternion algebra** $D = \mathbb H[F,a,b]$: for division $D$ it is
$1$ (`tauSL1EqOne_of_division`), otherwise $D$ is split (`exists_norm_eq_of_not_division`) and
`covolume_muSL1_ne_top_of_split` applies. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) < ∞) [unverified locator]"]
theorem covolume_muSL1_ne_top (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) ≠ ∞ := by
  by_cases hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ
  · rw [(tauSL1EqOne_of_division a b hdiv).covolume_eq_one ha0 hb0]
    exact ENNReal.one_ne_top
  · obtain ⟨x, y, h⟩ := exists_norm_eq_of_not_division (a : F) (b : F) two_ne_zero (by simpa using ha0)
      (by simpa using hb0) hdiv
    exact covolume_muSL1_ne_top_of_split ha0 hb0 h

/-- **$\tau(PD^\times) = 2\,\tau(\mathrm{SL}_1(D))$ for every quaternion algebra** $D = \mathbb H[F,a,b]$ (split or not),
every number field, every signature, unconditionally. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (τ(PD^×) = 2 via τ(SL₁) and the centre)"]
theorem covolume_muPD_eq_two_mul_covolume_muSL1 (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    covolume (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) =
      2 * covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
        (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) :=
  covolume_muPD_eq_two_mul a b ha0 hb0 (covolume_muSL1_ne_top a b ha0 hb0)

end Every

end QuadFormsKB.Tamagawa.Measure.Weil
