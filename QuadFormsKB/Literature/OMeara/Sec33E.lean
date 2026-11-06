/-
# O'Meara §33E: the "density" $M(i)/\lVert i\rVert$ (33:4, 33:5)

**Setting.** As in `Sec33D.lean`: $F$ a number field, $J_F$ = `IdeleGroup (𝓞 F) F`, $\lVert i\rVert$ the volume (Mathlib's
norm of the adèle ring, `norm_idele_eq`), `IsBoundedByIdele i x` and $M(i)$ = `boundedCount i`.

**Proves** `exists_boundedCount_le` (**33:4**) and `exists_lt_boundedCount` (**33:5**). O'Meara proves them for every
global field by the Pigeon Holing Principle and the Product Formula (Artin–Whaples); here $F$ is a number field.
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec33D

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

open scoped nonZeroDivisors

open QuadFormsKB.Tamagawa.Measure.Weil (ordAt ideleIdeal count_ideleIdeal)

/-! ### The finite part of an idèle as a fractional ideal -/

/-- The fractional ideal of the finite part of an idèle. -/
def idealOf (i : J) : FractionalIdeal (𝓞 F)⁰ F :=
  (ideleIdeal F (finPartHom i) : FractionalIdeal (𝓞 F)⁰ F)

theorem idealOf_ne_zero (i : J) : idealOf i ≠ 0 := Units.ne_zero _

theorem ideleAt_ne_zero (i : J) (v : HeightOneSpectrum (𝓞 F)) : ideleAt i v ≠ 0 := by
  have := QuadFormsKB.Tamagawa.Measure.Weil.valued_unit_ne_zero (finPartHom i) v
  intro h
  apply this
  show Valued.v (ideleAt i v) = 0
  rw [h, map_zero]

theorem norm_ideleAt_eq (i : J) (v : HeightOneSpectrum (𝓞 F)) :
    ‖ideleAt i v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(FractionalIdeal.count F v (idealOf i))) := by
  rw [QuadFormsKB.WeilRep.norm_eq_absNorm_pow v (ideleAt_ne_zero i v)]
  congr 1
  rw [idealOf, count_ideleIdeal, ordAt_finPartHom, neg_neg]

theorem norm_coe_eq (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    ‖(x : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^
      (-(FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ x))) := by
  have hx' : (x : v.adicCompletion F) ≠ 0 := by
    exact (map_ne_zero (algebraMap F (v.adicCompletion F))).2 hx
  rw [QuadFormsKB.WeilRep.norm_eq_absNorm_pow v hx']
  congr 1
  have : Valued.v (x : v.adicCompletion F) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [this, QuadFormsKB.Analysis.valuation_eq_exp_neg_count v hx, WithZero.log_exp]

theorem mem_iff_count_le (I : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) {x : F} (hx : x ≠ 0) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 F), FractionalIdeal.count F v I ≤
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ x) := by
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≠ 0 := by
    simpa using hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  have hK : I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≠ 0 := mul_ne_zero (inv_ne_zero hI) hs
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ I ↔
      I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ 1 := by
    constructor
    · intro h
      calc I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ I⁻¹ * I := mul_le_mul' le_rfl h
        _ = 1 := inv_mul_cancel₀ hI
    · intro h
      calc FractionalIdeal.spanSingleton (𝓞 F)⁰ x
          = I * (I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ x) := by
            rw [← mul_assoc, mul_inv_cancel₀ hI, one_mul]
        _ ≤ I * 1 := mul_le_mul' le_rfl h
        _ = I := mul_one _
  rw [h1, QuadFormsKB.Analysis.le_one_iff_count_nonneg hK]
  refine forall_congr' fun v => ?_
  rw [FractionalIdeal.count_mul F v (inv_ne_zero hI) hs, FractionalIdeal.count_inv]
  omega

/-- Boundedness at the finite spots is membership in the fractional ideal of the idèle. -/
theorem finite_bound_iff_mem (i : J) (x : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ ≤ ‖ideleAt i v‖) ↔ x ∈ idealOf i := by
  by_cases hx : x = 0
  · subst hx
    simp only [HeightOneSpectrum.adicCompletion.coe_zero, norm_zero, norm_nonneg, implies_true,
      true_iff]
    exact Submodule.zero_mem _
  · rw [mem_iff_count_le _ (idealOf_ne_zero i) hx]
    refine forall_congr' fun v => ?_
    rw [norm_coe_eq v hx, norm_ideleAt_eq]
    have h1 : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    rw [zpow_le_zpow_iff_right₀ h1]
    omega

theorem finprod_norm_ideleAt (i : J) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖ideleAt i v‖ =
      ((FractionalIdeal.absNorm (idealOf i) : ℚ) : ℝ)⁻¹ := by
  have h := QuadFormsKB.Tamagawa.Measure.Weil.finprod_modAt_eq (finPartHom i)
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖ideleAt i v‖ = (QuadFormsKB.Tamagawa.Measure.Weil.modAt (finPartHom i) v : ℝ) := by
    intro v
    rw [QuadFormsKB.Tamagawa.Measure.Weil.modAt_eq_zpow, norm_ideleAt_eq, idealOf, count_ideleIdeal]
  simp_rw [h2]
  rw [h]
  rfl

theorem norm_idele_eq' (i : J) :
    ‖(i : AdeleRing (𝓞 F) F)‖ =
      (∏ w : InfinitePlace F, ‖ideleAtInf i w‖ ^ w.mult) /
        ((FractionalIdeal.absNorm (idealOf i) : ℚ) : ℝ) := by
  rw [norm_idele_eq, finprod_norm_ideleAt, div_eq_mul_inv]

/-! ### The norm bound and the infinite places -/

theorem absNorm_le_prod {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) {y : F} (hy : y ∈ I) (hy0 : y ≠ 0) :
    ((FractionalIdeal.absNorm I : ℚ) : ℝ) ≤ ∏ w : InfinitePlace F, w y ^ w.mult := by
  rw [InfinitePlace.prod_eq_abs_norm, ← FractionalIdeal.absNorm_span_singleton (𝓞 F) y]
  have hs : FractionalIdeal.spanSingleton (𝓞 F)⁰ y ≠ 0 := by simpa using hy0
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ y ≤ I := (FractionalIdeal.spanSingleton_le_iff_mem).2 hy
  have h1 : I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ y ≤ 1 := by
    calc I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ y ≤ I⁻¹ * I := mul_le_mul' le_rfl hle
      _ = 1 := inv_mul_cancel₀ hI
  obtain ⟨Jd, hJd⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 h1
  have hJne : Jd ≠ ⊥ := by
    intro h
    rw [h] at hJd
    have : (I⁻¹ * FractionalIdeal.spanSingleton (𝓞 F)⁰ y) ≠ 0 := mul_ne_zero (inv_ne_zero hI) hs
    apply this
    rw [← hJd]; simp
  have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ y = I * Jd := by
    rw [hJd, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (Jd : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
    have : 1 ≤ Ideal.absNorm Jd := Nat.one_le_iff_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using hJne)
    exact_mod_cast this
  have hpos : (0 : ℚ) ≤ FractionalIdeal.absNorm I := FractionalIdeal.absNorm_nonneg I
  rw [hspan, map_mul]
  have : FractionalIdeal.absNorm I ≤ FractionalIdeal.absNorm I * FractionalIdeal.absNorm (Jd : FractionalIdeal (𝓞 F)⁰ F) :=
    le_mul_of_one_le_right hpos hN
  exact_mod_cast this

theorem norm_ideleAtInf_pos (i : J) (w : InfinitePlace F) : 0 < ‖ideleAtInf i w‖ := by
  obtain ⟨hu1, hu2, -⟩ := AdeleRing.isUnit_iff.1 i.isUnit
  exact norm_pos_iff.2 (hu1 w)

theorem isBoundedByIdele_iff (i : J) (x : F) :
    IsBoundedByIdele i x ↔ x ∈ idealOf i ∧ ∀ w : InfinitePlace F, w x ≤ ‖ideleAtInf i w‖ := by
  unfold IsBoundedByIdele
  rw [finite_bound_iff_mem]
  refine and_congr Iff.rfl (forall_congr' fun w => ?_)
  have : ‖(x : w.Completion)‖ = w x := by simp; rfl
  rw [this]

/-! ### Pigeonhole in a fractional ideal -/

theorem exists_diff_mem_pow_mul (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (r : ℕ) (T : Finset F)
    (hT : ∀ t ∈ T, t ∈ (I : FractionalIdeal (𝓞 F)⁰ F))
    (hcard : (2 ^ r) ^ (Module.finrank ℚ F) < T.card) :
    ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ ≠ t₂ ∧
      ∃ y ∈ (I : FractionalIdeal (𝓞 F)⁰ F), t₁ - t₂ = ((2 ^ r : ℕ) : F) * y := by
  classical
  set b := NumberField.basisOfFractionalIdeal F I with hb
  have hmem : ∀ t ∈ T, ∃ c : Module.Free.ChooseBasisIndex ℤ I → ℤ, ∑ j, c j • b j = t := by
    intro t ht
    have := (NumberField.mem_span_basisOfFractionalIdeal (K := F) (I := I) (x := t)).2 (hT t ht)
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  choose! c hc using hmem
  let f : F → (Module.Free.ChooseBasisIndex ℤ I → ZMod (2 ^ r)) := fun t j => ((c t j : ℤ) : ZMod (2 ^ r))
  have hcardι : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = Module.finrank ℚ F :=
    (Module.finrank_eq_card_basis b).symm
  have hlt : (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ I → ZMod (2 ^ r))).card < T.card := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, hcardι]
    exact hcard
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (f := f) (fun a _ => Finset.mem_univ _)
  have hdvd : ∀ j, ∃ d : ℤ, c t₁ j - c t₂ j = (2 ^ r : ℤ) * d := by
    intro j
    have := congrFun hf j
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (c t₂ j) (c t₁ j) (2 ^ r)).1 this.symm
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, by push_cast at hd; linarith⟩
  choose d hd using hdvd
  refine ⟨t₁, ht₁, t₂, ht₂, hne, ∑ j, d j • b j, ?_, ?_⟩
  · have := (NumberField.mem_span_basisOfFractionalIdeal (K := F) (I := I)
      (x := ∑ j, d j • b j)).1 ((Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨d, rfl⟩)
    exact this
  · rw [← hc t₁ ht₁, ← hc t₂ ht₂, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, hd j]
    simp [mul_smul, zsmul_eq_mul]

theorem card_le_of_box (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (r : InfinitePlace F → ℝ)
    (T : Finset F)
    (hT : ∀ t ∈ T, t ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ w : InfinitePlace F, w t ≤ r w) :
    (T.card : ℝ) ≤ max 1 (4 ^ (Module.finrank ℚ F) * ((∏ w, r w ^ w.mult) /
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ))) := by
  set n := Module.finrank ℚ F with hn
  set A : ℝ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) with hAdef
  have hA : 0 < A := by
    have h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.absNorm_nonneg _
    have h1 : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero I
    rw [hAdef]
    exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)
  set V := (∏ w, r w ^ w.mult) / A with hV
  have hstar : ∀ k : ℕ, (2 ^ k) ^ n < T.card → (((2 : ℝ) ^ k) ^ n) ≤ 2 ^ n * V := by
    intro k hk
    obtain ⟨t₁, h1, t₂, h2, hne, y, hy, hyeq⟩ :=
      exists_diff_mem_pow_mul I k T (fun t ht => (hT t ht).1) hk
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne
      simpa [sub_eq_zero] using hyeq
    have hw : ∀ w : InfinitePlace F, w y ≤ 2 * r w / 2 ^ k := by
      intro w
      have h3 : w (t₁ - t₂) ≤ 2 * r w := by
        calc w (t₁ - t₂) ≤ w t₁ + w t₂ := by
              have := AbsoluteValue.sub_le_add w.1 t₁ t₂
              exact this
          _ ≤ r w + r w := add_le_add ((hT t₁ h1).2 w) ((hT t₂ h2).2 w)
          _ = 2 * r w := by ring
      rw [hyeq, map_mul] at h3
      have h4 : w ((2 ^ k : ℕ) : F) = 2 ^ k := by rw [InfinitePlace.map_natCast]; push_cast; rfl
      rw [h4] at h3
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hnorm := absNorm_le_prod (Units.ne_zero I) hy hy0
    have hprod : ∏ w : InfinitePlace F, w y ^ w.mult ≤ ∏ w : InfinitePlace F, (2 * r w / 2 ^ k) ^ w.mult :=
      Finset.prod_le_prod₀ (fun w _ => by positivity) fun w _ =>
        pow_le_pow_left₀ (by positivity) (hw w) _
    have hprod2 : ∏ w : InfinitePlace F, (2 * r w / 2 ^ k) ^ w.mult =
        (2 / 2 ^ k) ^ n * ∏ w : InfinitePlace F, r w ^ w.mult := by
      have : ∀ w : InfinitePlace F, (2 * r w / 2 ^ k) ^ w.mult = (2 / 2 ^ k) ^ w.mult * r w ^ w.mult := by
        intro w; rw [← mul_pow]; ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    have hfin : A ≤ (2 / 2 ^ k) ^ n * ∏ w : InfinitePlace F, r w ^ w.mult := by
      rw [← hprod2]; exact hnorm.trans hprod
    have h5 : (2 / (2 : ℝ) ^ k) ^ n = 2 ^ n / ((2 : ℝ) ^ k) ^ n := by rw [div_pow]
    rw [h5] at hfin
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ k) ^ n := by positivity
    rw [hV, mul_div_assoc', le_div_iff₀ hA]
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos] at hfin
    nlinarith
  by_cases h1 : T.card ≤ 1
  · exact le_max_of_le_left (by exact_mod_cast h1)
  · replace h1 := not_le.1 h1
    have hn0 : 0 < n := Module.finrank_pos
    have hex : ∃ k : ℕ, T.card ≤ (2 ^ (k + 1)) ^ n := by
      refine ⟨T.card, ?_⟩
      have h2 : T.card < 2 ^ (T.card + 1) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact h2.le.trans (Nat.le_self_pow hn0.ne' _)
    classical
    have hk : T.card ≤ (2 ^ (Nat.find hex + 1)) ^ n := Nat.find_spec hex
    have hlt : (2 ^ (Nat.find hex)) ^ n < T.card := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h]; simp; omega
      · have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rw [e] at this
        omega
    have hs := hstar _ hlt
    refine le_max_of_le_right ?_
    calc (T.card : ℝ) ≤ ((2 : ℝ) ^ (Nat.find hex + 1)) ^ n := by exact_mod_cast hk
      _ = 2 ^ n * (((2 : ℝ) ^ (Nat.find hex)) ^ n) := by ring
      _ ≤ 2 ^ n * (2 ^ n * V) := by gcongr
      _ = 4 ^ n * V := by rw [← mul_assoc, ← mul_pow]; norm_num

/-! ### Minkowski's theorem with a uniform constant -/

open scoped NNReal ENNReal in
theorem exists_minkowski_const : ∃ κ : ℝ, 0 < κ ∧
    ∀ (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (f : InfinitePlace F → ℝ≥0),
      κ * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) <
          ∏ w, ((f w : ℝ)) ^ w.mult →
        ∃ a ∈ (I : FractionalIdeal (𝓞 F)⁰ F), a ≠ 0 ∧ ∀ w : InfinitePlace F, w a < f w := by
  classical
  set L : ℝ≥0∞ := MeasureTheory.volume
    (ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)) with hL
  have hLtop : L ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hL0 : L ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero _
  set Q : ℝ≥0∞ := L * 2 ^ (Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace F)) with hQ
  have hQtop : Q ≠ ⊤ := ENNReal.mul_ne_top hLtop (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hQ0 : Q ≠ 0 := mul_ne_zero hL0 (pow_ne_zero _ two_ne_zero)
  have hfac : (0 : ℝ) < (NumberField.mixedEmbedding.convexBodyLTFactor F : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (NumberField.mixedEmbedding.convexBodyLTFactor_ne_zero F))
  refine ⟨Q.toReal / (NumberField.mixedEmbedding.convexBodyLTFactor F : ℝ),
    div_pos (ENNReal.toReal_pos hQ0 hQtop) hfac, fun I f h => ?_⟩
  refine NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt F I ?_
  rw [NumberField.mixedEmbedding.convexBodyLT_volume, NumberField.mixedEmbedding.minkowskiBound,
    NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis]
  have hRtop : (NumberField.mixedEmbedding.convexBodyLTFactor F : ℝ≥0∞) *
      ((∏ w, f w ^ w.mult : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hLHS : ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) * L *
      2 ^ (Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace F)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  rw [← ENNReal.toReal_lt_toReal hLHS hRtop]
  have hQr : Q.toReal = L.toReal * 2 ^ (Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace F)) := by
    rw [hQ, ENNReal.toReal_mul, ENNReal.toReal_pow]; norm_num
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by exact_mod_cast FractionalIdeal.absNorm_nonneg _), ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  rw [hQr, div_mul_eq_mul_div, div_lt_iff₀ hfac] at h
  push_cast at h ⊢
  norm_num at h ⊢
  nlinarith [h]

/-! ### Many elements from one -/

/-- The elements of the integral basis of $F$, as elements of $F$. -/
def xb (F : Type) [Field F] [NumberField F] (j : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) : F :=
  ((RingOfIntegers.basis F j : 𝓞 F) : F)

/-- A constant bounding the archimedean sizes of the integral basis. -/
def Xc (F : Type) [Field F] [NumberField F] : ℝ :=
  1 + ∑ j, ∑ w : InfinitePlace F, w (xb F j)

theorem one_le_Xc : 1 ≤ Xc F := by
  unfold Xc
  have : 0 ≤ ∑ j, ∑ w : InfinitePlace F, w (xb F j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => by positivity
  linarith

theorem exists_many_elements (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (y : F)
    (hy : y ∈ (I : FractionalIdeal (𝓞 F)⁰ F)) (hy0 : y ≠ 0) (N : ℕ) :
    ∃ T : Finset F, T.card = (N + 1) ^ (Module.finrank ℚ F) ∧
      ∀ t ∈ T, t ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ w : InfinitePlace F, w t ≤ w y * (N * Xc F) := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let bz := RingOfIntegers.basis F
  let u : (ι → Fin (N + 1)) → 𝓞 F := fun c => ∑ j, (((c j : ℕ) : ℤ)) • bz j
  have hu : ∀ c, ((u c : 𝓞 F) : F) = ∑ j, ((c j : ℕ) : F) * xb F j := by
    intro c
    simp [u, xb, zsmul_eq_mul]
    rfl
  let z : (ι → Fin (N + 1)) → F := fun c => ((u c : 𝓞 F) : F) * y
  have hinj : Function.Injective z := by
    intro c c' h
    have h1 : ((u c : 𝓞 F) : F) = ((u c' : 𝓞 F) : F) := mul_right_cancel₀ hy0 h
    have h2 : u c = u c' := Subtype.ext h1
    have h3 : bz.repr (u c) = bz.repr (u c') := by rw [h2]
    have e1 := bz.repr_sum_self (fun j => (((c j : ℕ) : ℤ)))
    have e2 := bz.repr_sum_self (fun j => (((c' j : ℕ) : ℤ)))
    change bz.repr (∑ j, (((c j : ℕ) : ℤ)) • bz j) = bz.repr (∑ j, (((c' j : ℕ) : ℤ)) • bz j) at h3
    funext j
    have h4 : (bz.repr (∑ j, (((c j : ℕ) : ℤ)) • bz j)) j = (bz.repr (∑ j, (((c' j : ℕ) : ℤ)) • bz j)) j := by
      rw [h3]
    rw [congrFun e1 j, congrFun e2 j] at h4
    simpa [Fin.ext_iff] using h4
  refine ⟨Finset.univ.image z, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have hc : Fintype.card ι = Module.finrank ℚ F := by
      rw [← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
    rw [hc]
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 ht
    refine ⟨?_, fun w => ?_⟩
    · have : z c = (u c : 𝓞 F) • y := by simp [z, Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ hy
    · show w (((u c : 𝓞 F) : F) * y) ≤ _
      rw [map_mul, mul_comm (w y)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hu]
      calc w (∑ j, ((c j : ℕ) : F) * xb F j) ≤ ∑ j, w (((c j : ℕ) : F) * xb F j) :=
            AbsoluteValue.sum_le w.1 _ _
        _ = ∑ j, ((c j : ℕ) : ℝ) * w (xb F j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, InfinitePlace.map_natCast]
        _ ≤ ∑ j, (N : ℝ) * w (xb F j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast Nat.lt_succ_iff.1 (c j).2
        _ = N * ∑ j, w (xb F j) := by rw [Finset.mul_sum]
        _ ≤ N * Xc F := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            unfold Xc
            have : ∀ j, w (xb F j) ≤ ∑ w' : InfinitePlace F, w' (xb F j) := fun j =>
              Finset.single_le_sum (f := fun w' : InfinitePlace F => w' (xb F j))
                (fun w' _ => by positivity) (Finset.mem_univ w)
            linarith [Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => this j)]

theorem absNorm_unit_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    0 < ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) := by
  have h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.absNorm_nonneg _
  have h1 : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero I
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)

open scoped NNReal in
theorem exists_card_ge : ∃ c : ℝ, 0 < c ∧ ∀ (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (r : InfinitePlace F → ℝ),
    (∀ w, 0 < r w) → ∃ T : Finset F,
      (∀ t ∈ T, t ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ w : InfinitePlace F, w t ≤ r w) ∧
      c * ((∏ w, r w ^ w.mult) / ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ))
        ≤ T.card := by
  classical
  obtain ⟨κ, hκ, hM⟩ := exists_minkowski_const (F := F)
  set X := Xc F with hX
  have hX1 : 1 ≤ X := one_le_Xc
  set n := Module.finrank ℚ F with hn
  have hn0 : n ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hXn : 0 < X ^ n := by positivity
  refine ⟨1 / (κ * X ^ n), by positivity, fun I r hr => ?_⟩
  set A := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) with hA
  have hApos : 0 < A := absNorm_unit_pos I
  set V := (∏ w, r w ^ w.mult) / A with hV
  have hVpos : 0 < V := div_pos (Finset.prod_pos fun w _ => pow_pos (hr w) _) hApos
  have hex : ∃ s : ℕ, V ≤ κ * (s * X) ^ n := by
    refine ⟨⌈V / κ⌉₊, ?_⟩
    have h1 : V / κ ≤ ⌈V / κ⌉₊ := Nat.le_ceil _
    have h2 : (1 : ℝ) ≤ ⌈V / κ⌉₊ := by
      have : 0 < ⌈V / κ⌉₊ := Nat.ceil_pos.2 (div_pos hVpos hκ)
      exact_mod_cast this
    have h3 : (1 : ℝ) ≤ (⌈V / κ⌉₊ : ℝ) * X := by nlinarith
    have h4 : (⌈V / κ⌉₊ : ℝ) * X ≤ ((⌈V / κ⌉₊ : ℝ) * X) ^ n := le_self_pow₀ h3 hn0
    rw [div_le_iff₀ hκ] at h1
    nlinarith
  set s0 := Nat.find hex with hs0
  have hP : V ≤ κ * (s0 * X) ^ n := Nat.find_spec hex
  have hs0pos : s0 ≠ 0 := by
    intro h
    rw [h] at hP
    simp [zero_pow hn0] at hP
    linarith
  have hlt : κ * (((s0 - 1 : ℕ) : ℝ) * X) ^ n < V := by
    have := Nat.find_min hex (m := s0 - 1) (by omega)
    exact_mod_cast not_le.1 this
  have hcount : 1 / (κ * X ^ n) * V ≤ (s0 : ℝ) ^ n := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    calc V ≤ κ * (s0 * X) ^ n := hP
      _ = κ * X ^ n * (s0 : ℝ) ^ n := by rw [mul_pow]; ring
  by_cases hN : s0 - 1 = 0
  · refine ⟨{0}, fun t ht => ?_, ?_⟩
    · rw [Finset.mem_singleton] at ht
      subst ht
      exact ⟨Submodule.zero_mem _, fun w => by simpa using (hr w).le⟩
    · have : s0 = 1 := by omega
      rw [this] at hcount
      simpa using hcount
  · have hNpos : (0 : ℝ) < ((s0 - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    set N := s0 - 1 with hNdef
    have hNX : 0 < (N : ℝ) * X := by positivity
    have hcond : κ * A < ∏ w, (((Real.toNNReal (r w / (N * X)) : ℝ≥0) : ℝ)) ^ w.mult := by
      have : ∏ w, (((Real.toNNReal (r w / (N * X)) : ℝ≥0) : ℝ)) ^ w.mult =
          (∏ w, r w ^ w.mult) / ((N : ℝ) * X) ^ n := by
        simp_rw [Real.coe_toNNReal _ (div_pos (hr _) hNX).le, div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
      rw [this, lt_div_iff₀ (by positivity)]
      have h5 := hlt
      rw [hV, lt_div_iff₀ hApos] at h5
      linarith
    obtain ⟨y, hy, hy0, hyb⟩ := hM I (fun w => Real.toNNReal (r w / (N * X))) hcond
    obtain ⟨T, hTcard, hT⟩ := exists_many_elements I y hy hy0 N
    refine ⟨T, fun t ht => ⟨(hT t ht).1, fun w => ?_⟩, ?_⟩
    · have h1 := (hT t ht).2 w
      have h2 := hyb w
      rw [Real.coe_toNNReal _ (div_pos (hr w) hNX).le] at h2
      calc w t ≤ w y * (N * X) := h1
        _ ≤ r w / (N * X) * (N * X) := mul_le_mul_of_nonneg_right h2.le hNX.le
        _ = r w := div_mul_cancel₀ _ hNX.ne'
    · rw [hTcard]
      have : N + 1 = s0 := by omega
      rw [this]
      exact_mod_cast hcount

/-- **33:4 (Theorem).** There is a constant $D > 0$ depending only on $F$ such that
$M(i) \le \max(1, D\lVert i\rVert)$ for every idèle $i$; in particular an idèle bounds only finitely many elements of
$F$. -/
@[kb "omeara1963" "§33E, 33:4, p. 69"]
theorem exists_boundedCount_le :
    ∃ D : ℝ, 0 < D ∧ ∀ i : J, {x : F | IsBoundedByIdele i x}.Finite ∧
      (boundedCount i : ℝ) ≤ max 1 (D * ‖(i : AdeleRing (𝓞 F) F)‖) := by
  refine ⟨4 ^ (Module.finrank ℚ F), by positivity, fun i => ?_⟩
  have key : ∀ T : Finset F, (∀ t ∈ T, IsBoundedByIdele i t) →
      (T.card : ℝ) ≤ max 1 (4 ^ (Module.finrank ℚ F) * ‖(i : AdeleRing (𝓞 F) F)‖) := by
    intro T hT
    rw [norm_idele_eq' i]
    exact card_le_of_box (ideleIdeal F (finPartHom i)) (fun w => ‖ideleAtInf i w‖) T
      (fun t ht => (isBoundedByIdele_iff i t).1 (hT t ht))
  have hfin : {x : F | IsBoundedByIdele i x}.Finite := by
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈max 1 (4 ^ (Module.finrank ℚ F) * ‖(i : AdeleRing (𝓞 F) F)‖)⌉₊ + 1)
    have := key T (fun t ht => hTsub ht)
    rw [hTcard] at this
    have h2 := Nat.le_ceil (max 1 (4 ^ (Module.finrank ℚ F) * ‖(i : AdeleRing (𝓞 F) F)‖))
    push_cast at this
    linarith
  refine ⟨hfin, ?_⟩
  unfold boundedCount
  have : Nat.card {x : F // IsBoundedByIdele i x} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
    rfl
  rw [this]
  exact key _ (fun t ht => by simpa using ht)

/-- **33:5 (Theorem).** There is a constant $C$ with $0 < C < 1$ depending only on $F$ such that
$C\lVert i\rVert < M(i)$ for every idèle $i$. In particular an idèle of large enough volume bounds a non-zero element
of $F$. -/
@[kb "omeara1963" "§33E, 33:5, p. 70"]
theorem exists_lt_boundedCount :
    ∃ C : ℝ, 0 < C ∧ C < 1 ∧ ∀ i : J, C * ‖(i : AdeleRing (𝓞 F) F)‖ < boundedCount i := by
  obtain ⟨c, hc, hT⟩ := exists_card_ge (F := F)
  obtain ⟨D, hD, hfin⟩ := exists_boundedCount_le (F := F)
  refine ⟨min (c / 2) (1 / 2), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun i => ?_⟩
  obtain ⟨T, hTb, hTc⟩ := hT (ideleIdeal F (finPartHom i)) (fun w => ‖ideleAtInf i w‖)
    (norm_ideleAtInf_pos i)
  have hV := norm_idele_eq' i
  have hApos := absNorm_unit_pos (ideleIdeal F (finPartHom i))
  have hVpos : 0 < ‖(i : AdeleRing (𝓞 F) F)‖ := by
    rw [hV]
    exact div_pos (Finset.prod_pos fun w _ => pow_pos (norm_ideleAtInf_pos i w) _) hApos
  have hM : (T.card : ℝ) ≤ boundedCount i := by
    have hs := (hfin i).1
    have hsub : (↑T : Set F) ⊆ {x : F | IsBoundedByIdele i x} :=
      fun t ht => (isBoundedByIdele_iff i t).2 (hTb t ht)
    have := Set.ncard_le_ncard hsub hs
    rw [Set.ncard_coe_finset] at this
    unfold boundedCount
    rw [← Nat.card_coe_set_eq] at this
    exact_mod_cast this
  have hTc' : c * ‖(i : AdeleRing (𝓞 F) F)‖ ≤ T.card := by
    rw [hV]; exact hTc
  calc min (c / 2) (1 / 2) * ‖(i : AdeleRing (𝓞 F) F)‖ < c * ‖(i : AdeleRing (𝓞 F) F)‖ := by
        refine mul_lt_mul_of_pos_right ?_ hVpos
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    _ ≤ T.card := hTc'
    _ ≤ boundedCount i := hM

end QuadFormsKB.OMeara
