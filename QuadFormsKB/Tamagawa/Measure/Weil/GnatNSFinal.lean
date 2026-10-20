/-
# The non-square half of Weil Thm 2.3.1, reduced to the local ratios at the bad places

**Layer:** a totally real number field $F$ (any class number).

* **`isTotallyReal_of_basis`**: $K = F(\delta)$ with $\delta^2 = d\gg0$ is totally real.
* **`NSBadPlaceRatio F`** (input, named): Weil's local ratio $r_v = R_v^{-3}\|ab\|_v^{-3}\|d\|_v^{15/2}$ of the non-square model at each of the
  finitely many bad places $v$ ($|2abd|_v\ne1$ or $v\mid\operatorname{disc}(1,\delta)$), in the form
  $$\prod_{w\mid v}\frac{\mu_w(K^{(3)}_{m_w})\,\omega_w(\mathcal O_w^\times)}{\omega_w(\operatorname{nrd}\Lambda^{(m_w)}_w)}\cdot
    \frac{\omega_v(N_v)}{\omega_v(\mathcal O_v^\times)} = r_v\cdot\mu^{SO}_v(U_v),$$
  $U_v = \varphi(\{y\in G^\natural(F_v) : y_w\in\Lambda^{(m_w)}_w\ \forall w\mid v\})$ — a purely local statement at one place of $F$ (and the
  places of $K$ over it). It mentions no lattice, covolume, Tamagawa number or global measure.
* **`gnatMeasureComparisonNS_of_ratio`**: `NSBadPlaceRatio F → GnatMeasureComparisonNSDef F` — all good places (split, and inert
  with the $SO^-(4,q)$ count), the archimedean places and the product formula are proved (`map_muP_nsPEquiv_of_local`,
  `prod_siegelDensity_good`, `finFactor_regroup`, `arch_identity_ns`).
* Consumers: **`siegelFormulaAt_totallyReal_of_ratio`** (Siegel's formula for every totally positive definite form over
  $\mathcal O_F$ in every rank $N\ge4$, every totally positive $m$), `quaternaryTamagawaTwo_of_ratio`,
  `rankFourUnitSiegel_of_ratio`, `tamagawaNumberTwo_all_ranks_of_ratio`, `massFormula_all_ranks_of_ratio`.

*Hypothesis hygiene.* `NSBadPlaceRatio` is strictly smaller than `GnatMeasureComparisonNSDef`: it is a family of local
identities at single places, each a comparison of explicit local volumes.

Source: Weil 1982, Thm 2.3.1 (local ratios, ∏_v r_v = 1); §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSGood

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain Module
open scoped ENNReal ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular LocalDensity

/-! ### $K$ is totally real; the basis is integral -/

section Basics

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

theorem complex_real_of_sq_pos {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z ^ 2 = r) : z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  rcases mul_eq_zero.1 (show 2 * (z.re * z.im) = 0 by linarith) with h | h
  · norm_num at h
  · rcases mul_eq_zero.1 h with h | h
    · rw [h] at h1; nlinarith [sq_nonneg z.im]
    · exact h

include hb₀ hb₁ in
/-- **$K = F(\sqrt d)$ is totally real for $d\gg0$.** -/
theorem isTotallyReal_of_basis [IsTotallyReal F] (hd : IsTotallyPos (d : F)) : IsTotallyReal K := by
  refine ⟨fun w => ?_⟩
  rw [← mk_embedding w, isReal_mk_iff, ComplexEmbedding.isReal_iff]
  set φ := w.embedding
  set τ : F →+* ℂ := φ.comp (algebraMap F K)
  have hτ : ∀ c : F, (starRingEnd ℂ) (τ c) = τ c := fun c =>
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)) c
  have hδ : (starRingEnd ℂ) (φ (bK 1)) = φ (bK 1) := by
    have hpos := hd τ.toRatAlgHom
    rw [Complex.lt_def] at hpos
    have hsq : (φ (bK 1)) ^ 2 = (((τ (d : F)).re : ℝ) : ℂ) := by
      rw [sq, ← map_mul, hb₁]
      apply Complex.ext
      · simp [τ]
      · simp only [Complex.ofReal_im]; exact hpos.2.symm
    have him := complex_real_of_sq_pos hpos.1 hsq
    exact Complex.conj_eq_iff_im.2 him
  ext x
  obtain ⟨c₀, c₁, rfl⟩ := span_basis hb₀ x
  change (starRingEnd ℂ) (φ (algebraMap F K c₀ + algebraMap F K c₁ * bK 1)) = φ (algebraMap F K c₀ + algebraMap F K c₁ * bK 1)
  rw [map_add, map_mul, map_add, map_mul]
  exact congrArg₂ _ (hτ c₀) (congrArg₂ _ (hτ c₁) hδ)

include hb₀ hb₁ in
theorem isIntegral_basis : ∀ i, IsIntegral ℤ (bK i) := by
  intro i
  fin_cases i
  · show IsIntegral ℤ (bK 0)
    rw [hb₀]; exact isIntegral_one
  · show IsIntegral ℤ (bK 1)
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [sq, hb₁]
    have := (d.2).map (IsScalarTower.toAlgHom ℤ F K)
    exact this

end Basics

section HPD

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b d : 𝓞 F}

theorem hpd_qNS (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (hdpos : IsTotallyPos (d : F)) :
    IsTotallyPosDef (formF (qNS a b d)) := by
  rw [qNS]
  refine isTotallyPosDef_formF_diag _ fun i => ?_
  fin_cases i
  · intro σ; show 0 < σ ((1 : 𝓞 F) : F); simp only [map_one]
    exact (zero_lt_one : (0 : ℂ) < 1)
  · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hdpos
    simpa [neg_mul] using this
  · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hnb hdpos
    simpa [neg_mul] using this
  · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul (QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hnb) hdpos
    simpa [neg_mul_neg] using this

end HPD

/-! ### The named input: the local ratios at the bad places -/

variable (F : Type) [Field F] [NumberField F]

/-- **Input (named): Weil's local ratios at the bad places of the non-square model** ($m = 4$, Weil 1982, Thm 2.3.1
[unverified page]).

Fields:
- `ratio`: for every non-square model ($a, b, d\in\mathcal O_F$, $-a,-b,d\gg0$, $K = F(\delta)$ with basis $(1,\delta)$,
  $\delta^2 = d$, $\alpha = a$, $\beta = b$ in $\mathcal O_K$) and every finite place $v$ of $F$ that is **not** good (`NSGoodPlace`:
  $|2abd|_v = 1$ and $v\nmid\operatorname{disc}(1,\delta)$), the local identity
  $$\Bigl(\prod_{w\mid v}\frac{\mu_w(K^{(3)}_{m_w})\,\omega_w(\mathcal O_w^\times)}{\omega_w(\operatorname{nrd}\Lambda^{(m_w)}_w)}\Bigr)\cdot
    \frac{\omega_v(N_v)}{\omega_v(\mathcal O_v^\times)} = r_v\cdot\mu^{SO}_v(U_v)$$
  with $m_w$ = `nsLevK`, $K^{(3)}_{m_w}$ the congruence subgroup of $SO(\langle-\alpha,-\beta,\alpha\beta\rangle)(K_w)$ (`congSO3S`),
  $\Lambda^{(m_w)}_w$ = `lamCong`, $N_v$ = `nsN`, $U_v$ = `nsU` (the image under $\varphi$ of the $y\in G^\natural(F_v)$ with all
  $y_w\in\Lambda^{(m_w)}_w$) and $r_v$ = `nsRatio` $= R_v^{-3}\|ab\|_v^{-3}\|d\|_v^{15/2}$. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios) [unverified page]"]
structure NSBadPlaceRatio : Prop where
  ratio : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (_hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (_hdpos : IsTotallyPos (d : F)) (v : HeightOneSpectrum (𝓞 F))
    (_hv : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v),
    (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
        (congSO3S (a := α) (b := β) (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w) *
      omegaV w (unitsVSub w) / omegaV w (nL α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w)) *
        (omegaV v (nsN α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) v) / omegaV v (unitsVSub v)) =
      ENNReal.ofReal (nsRatio K a b d v) * Measure.muLocSO v (qNS a b d) 1
        (nsU hb₁ hα hβ (ne_zero_of_algebraMap_eq hα hα0) (d_ne_zero_of_basis hb₁) (nsLevK hα0 hβ0)
          (one_le_nsLevK hα0 hβ0) v)

variable {F}

set_option maxHeartbeats 1600000 in
/-- **The non-square half of Weil's Thm 2.3.1 from the local ratios at the bad places** (every totally real $F$). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏_v r_v = 1); §3.7, pp. 64-65 [unverified page]"]
theorem gnatMeasureComparisonNS_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) : GnatMeasureComparisonNSDef F := by
  refine ⟨fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos hQ => ?_⟩
  haveI : IsTotallyReal K := isTotallyReal_of_basis hb₀ hb₁ hdpos
  have ha0 := ne_zero_of_algebraMap_eq hα hα0
  have hb0 := ne_zero_of_algebraMap_eq hβ hβ0
  have hd0 := d_ne_zero_of_basis hb₁
  have hint := isIntegral_basis hb₀ hb₁
  have hK2 := finrank_eq_two_of_basis hb₀ hb₁
  have hgood : ∀ v ∉ nsBad (bK := bK) ha0 hb0 hd0, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v :=
    fun v hv => nsGood_of_not_mem bK hv
  refine map_muP_nsPEquiv_of_local hb₀ hb₁ hα hβ hα0 hβ0 ha0 hb0 hd0 hna hnb hdpos hQ hint (nsRatio K a b d)
    (nsRatio_pos ha0 hb0 hd0) ?_ ?_ ?_
  · exact finFactor_regroup hα0 hβ0 hQ _ fun v hv => prod_siegelDensity_good hb₀ hb₁ hα hβ (hgood v hv)
  · refine arch_identity_ns hK2 hα hβ hα0 hβ0 ha0 hb0 hd0 hna hnb hdpos hQ (hpd_qNS hna hnb hdpos) _ fun v hv => ?_
    obtain ⟨-, hav, hbv, hdv, hdisc⟩ := hgood v hv
    refine ⟨relDisc_eq_one hint hdisc, ?_, ?_⟩
    · rw [← valued_algebraMap, map_mul, Valuation.map_mul, hav, hbv, one_mul]
    · rw [← valued_algebraMap]; exact hdv
  · intro v hv
    have hv' : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := (Set.Finite.mem_toFinset _).1 hv
    exact hR.ratio a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos v hv'

/-! ### Consumers -/

/-- **`GnatMeasureComparisonDef F`** from the bad-place local ratios. -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparisonDef_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) : GnatMeasureComparisonDef F :=
  gnatMeasureComparisonDef_of_ns (gnatMeasureComparisonNS_of_ratio hR)

/-- **`GnatTamagawaComparisonDef F`** from the bad-place local ratios. -/
@[kb "weil1982" "Thm 2.3.1; §3.7 [unverified page]"]
theorem gnatTamagawaComparisonDef_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) : GnatTamagawaComparisonDef F :=
  gnatTamagawaComparisonDef_of_measure (gnatMeasureComparisonDef_of_ratio hR)

/-- **$\tau(SO_4) = 2$ for every totally real $F$**, from the bad-place local ratios. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem quaternaryTamagawaTwo_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_ns (gnatMeasureComparisonNS_of_ratio hR)

/-- **`RankFourUnitSiegel F`** from the bad-place local ratios. -/
@[kb "weil1982" "§4.5, p. 100; §3.7; Thm 2.3.1"]
theorem rankFourUnitSiegel_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_ns (gnatMeasureComparisonNS_of_ratio hR)

/-- **Siegel's formula for every totally positive definite form over $\mathcal O_F$ in every rank $N\ge4$, every totally
positive $m$, every totally real $F$** (any class number), from the bad-place local ratios of the non-square model. -/
@[kb "siegel1935" "Hauptsatz [unverified]; weil1982 §4.5, Thm 4.5.1"]
theorem siegelFormulaAt_totallyReal_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < QuadFormsKB.HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_totallyReal_of_ns (gnatMeasureComparisonNS_of_ratio hR) hN Q₀ hpd hm

/-- **$\tau = 2$ in every rank $N\ge4$**, from the bad-place local ratios. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem tamagawaNumberTwo_all_ranks_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_ns (gnatMeasureComparisonNS_of_ratio hR) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$**, from the bad-place local ratios. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem massFormula_all_ranks_of_ratio [IsTotallyReal F] (hR : NSBadPlaceRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_ns (gnatMeasureComparisonNS_of_ratio hR) hN Q₀ hpd

end QuadFormsKB.Tamagawa.Measure.Weil
