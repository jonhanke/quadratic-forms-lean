import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.FibreConst

/-!
# The group-level fibre form on `SO(V)(F_v)` at a finite place
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayFinite
open QuadFormsKB.Tamagawa.Measure.FibreDecomp QuadFormsKB.Tamagawa.Measure.FibreConst

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.FibreSO

section ProdComap

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- `ν × e^*μ = (id × e)^*(ν × μ)` for a measurable embedding `e`. -/
theorem prod_comap_right (ν : Measure α) [SigmaFinite ν] (μ : Measure γ) [SigmaFinite μ] {e : β → γ}
    (he : MeasurableEmbedding e) [SigmaFinite (μ.comap e)] :
    ν.prod (μ.comap e) = (ν.prod μ).comap (Prod.map id e) := by
  have hemb : MeasurableEmbedding (Prod.map (id : α → α) e) := MeasurableEmbedding.id.prodMap he
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [hemb.comap_apply]
  have : Prod.map id e '' (s ×ˢ t) = s ×ˢ (e '' t) := by
    ext ⟨a, c⟩
    simp only [Set.mem_image, Set.mem_prod, Prod.map_apply, id_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a', b', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, b', h2, rfl⟩
    · rintro ⟨h1, b', h2, rfl⟩; exact ⟨a, b', ⟨h1, h2⟩, rfl, rfl⟩
  rw [this, Measure.prod_prod, he.comap_apply]

end ProdComap

section SO

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem det_orb_eq (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)
    (x : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) (h : orthGroup (QQ' Q₀') (v.adicCompletion F)) :
    ((FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn (x, h) :
      orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) : GL (Fin (n + 1)) (v.adicCompletion F)).val.det =
      ((h : GL (Fin n) (v.adicCompletion F)).val.det) := by
  have hsec : ((FibreO.secOrth v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn x :
      orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) : GL (Fin (n + 1)) (v.adicCompletion F)).val.det = 1 :=
    (Weil.sphereSec_mem (FibreO.hessV_transpose v (QQ m₀ Q₀'))
      two_ne_zero (FibreO.sphereData v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm)
        (QQ'_nondeg Q₀' hQ') hn)
      ((FibreO.mem_sphereSet_iff v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') x.1).1 x.2)).2
  have hiota : ((FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') h : orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) :
      GL (Fin (n + 1)) (v.adicCompletion F)).val.det = (h : GL (Fin n) (v.adicCompletion F)).val.det := by
    rw [FibreO.iota_val, det_cornerMat, one_mul]
  show (((FibreO.secOrth v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn x *
    FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') h : orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) :
      GL (Fin (n + 1)) (v.adicCompletion F)).val.det = _)
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hsec, hiota, one_mul]

theorem det_orb (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)
    (x : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) (h : orthGroup (QQ' Q₀') (v.adicCompletion F))
    (hh : h ∈ soSub (QQ' Q₀') (v.adicCompletion F)) :
    ((FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn (x, h) :
      orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) : GL (Fin (n + 1)) (v.adicCompletion F)).val.det = 1 := by
  rw [det_orb_eq v m₀ hm Q₀' hQ' hn x h]; exact hh

/-- **The coordinates `orb(x, h) = s(x)·diag(1, h)` on `SO(V)(F_v)`**, `h ∈ SO(Q')`. -/
def orbSO (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)
    (p : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀) × SOv v Q₀') : SOv v (splitForm m₀ Q₀') :=
  ⟨FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn (p.1, p.2.1),
    det_orb v m₀ hm Q₀' hQ' hn p.1 p.2.1 p.2.2⟩

theorem measurable_orbSO (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate)
    (hn : 1 ≤ n) : Measurable (orbSO v m₀ hm Q₀' hQ' hn) := by
  have hQ := hQ0 m₀ Q₀' hm hQ'
  refine ((measurableEmbedding_soSub v (splitForm m₀ Q₀') hQ).measurable_comp_iff).1 ?_
  exact (FibreO.measurable_orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn).comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

@[kb "weil1982" "§2.4 Thm 2.4.3 p. 25 (SO(V)(F_v) = orb_*(sphere x SO(xi-perp))) [unverified]"]
theorem fibre_SO (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n) :
    ((nuS v m₀ hm Q₀' hQ').prod (muLocSO v Q₀' 1)).map (orbSO v m₀ hm Q₀' hQ' hn) =
      ENNReal.ofReal (absTwoM v m₀ ^ n) • muLocSO v (splitForm m₀ Q₀') 1 := by
  have hQ := hQ0 m₀ Q₀' hm hQ'
  have hEG := measurableEmbedding_soSub v (splitForm m₀ Q₀') hQ
  have hEH := measurableEmbedding_soSub v Q₀' hQ'
  have hGeq : muLocSO v (splitForm m₀ Q₀') 1 = (muLoc v (splitForm m₀ Q₀') 1).comap Subtype.val :=
    muLocSO_eq_comap v _ hQ (by omega) one_pos
  have hHeq : muLocSO v Q₀' 1 = (muLoc v Q₀' 1).comap Subtype.val :=
    muLocSO_eq_comap v _ hQ' (by omega) one_pos
  have hfib := fibre_constant v m₀ hm Q₀' hQ' hn
  haveI hHaar : (muLoc v Q₀' 1).IsHaarMeasure := isHaarMeasure_muLoc v _ hQ' one_pos
  haveI : SigmaFinite ((muLoc v Q₀' 1).comap (Subtype.val : SOv v Q₀' → _)) :=
    Weil.sigmaFinite_comap_subtype (muLoc v Q₀' 1)
      (O := (soSub (QQ' Q₀') (v.adicCompletion F) : Set (orthGroup (QQ' Q₀') (v.adicCompletion F))))
      (isOpen_soSub v (QQ' Q₀') (QQ'_nondeg Q₀' hQ')).measurableSet
  have hprod : (nuS v m₀ hm Q₀' hQ').prod (muLocSO v Q₀' 1) =
      ((nuS v m₀ hm Q₀' hQ').prod (muLoc v Q₀' 1)).comap (Prod.map id Subtype.val) := by
    rw [hHeq]; exact prod_comap_right _ _ hEH
  ext B hB
  rw [Measure.map_apply (measurable_orbSO v m₀ hm Q₀' hQ' hn) hB, hprod,
    (MeasurableEmbedding.id.prodMap hEH).comap_apply, Measure.smul_apply, hGeq, hEG.comap_apply, smul_eq_mul]
  have hset : Prod.map id (Subtype.val : SOv v Q₀' → _) '' (orbSO v m₀ hm Q₀' hQ' hn ⁻¹' B) =
      FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn ⁻¹'
        (Subtype.val '' B) := by
    ext ⟨x, h⟩
    simp only [Set.mem_image, Set.mem_preimage, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨x', h', hB', rfl, rfl⟩
      exact ⟨orbSO v m₀ hm Q₀' hQ' hn (x', h'), hB', rfl⟩
    · rintro ⟨b, hb, hbe⟩
      have hdet : (h : GL (Fin n) (v.adicCompletion F)).val.det = 1 := by
        rw [← det_orb_eq v m₀ hm Q₀' hQ' hn x h, ← hbe]; exact b.2
      refine ⟨x, ⟨h, hdet⟩, ?_, rfl, rfl⟩
      show orbSO v m₀ hm Q₀' hQ' hn (x, ⟨h, hdet⟩) ∈ B
      have : orbSO v m₀ hm Q₀' hQ' hn (x, ⟨h, hdet⟩) = b := Subtype.ext hbe.symm
      rw [this]; exact hb
  rw [hset, ← Measure.map_apply (FibreO.measurable_orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm)
    (QQ'_nondeg Q₀' hQ') hn) (hEG.measurableSet_image.2 hB), hfib, Measure.smul_apply, smul_eq_mul]

/-- **The group-level orbital identity at a finite place** (Weil 1982, §2.4 Thm 2.4.3 and §3.4 [unverified pages]; the
finite-place analogue of `lerayMeasure_orbital`/`lerayMeasure_orbital_realPlace`): for `Q = ⟨m₀⟩ ⊥ Q₀'` over `𝓞 F`
(`m₀ ≠ 0`, `Q₀'` nondegenerate, `n ≥ 1`), at every finite place `v` (dyadic included),
`μ_{SO(V_v)} = |2m₀|_v^{-n} · orb_*(σ_{m₀} × μ_{SO(ξ^⊥)})`, `orb(x, h) = s(x)·diag(1, h)`, `s` the reflection section,
with the `muLocSO` on both groups and `σ_{m₀}` the Leray measure on `{Q = m₀}` (`nuS`). The local constant
`|2m₀|_v^{-n}`
is the `v`-component of an idele of norm `1` (`prod_orbital_constants_eq_one`). -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25; §3.4; §4.5 (local factors at the finite places) [unverified]"]
theorem lerayMeasure_orbital_finitePlace (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n) :
    muLocSO v (splitForm m₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v m₀ ^ n)⁻¹) •
        ((nuS v m₀ hm Q₀' hQ').prod (muLocSO v Q₀' 1)).map (orbSO v m₀ hm Q₀' hQ' hn) := by
  rw [fibre_SO v m₀ hm Q₀' hQ' hn, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (absTwoM_pos v hm).le _)),
    inv_mul_cancel₀ (pow_pos (absTwoM_pos v hm) n).ne', ENNReal.ofReal_one, one_smul]

/-- **Lintegral form of the orbital identity** (Weil's Lemma 2.4.1 form): for measurable `f ≥ 0` on `SO(V)(F_v)`,
`∫ f dμ_G = |2m₀|_v^{-n} ∫_{sphere} ∫_{SO(Q')} f(s(x)·diag(1,h)) dμ_H dσ`. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1 [unverified]"]
theorem lintegral_orbital_finitePlace (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n) {f : SOv v (splitForm m₀ Q₀') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂muLocSO v (splitForm m₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v m₀ ^ n)⁻¹) *
        ∫⁻ x, ∫⁻ h, f (orbSO v m₀ hm Q₀' hQ' hn (x, h)) ∂muLocSO v Q₀' 1 ∂nuS v m₀ hm Q₀' hQ' := by
  haveI hHaar : (muLoc v Q₀' 1).IsHaarMeasure := isHaarMeasure_muLoc v _ hQ' one_pos
  haveI : SigmaFinite (muLocSO v Q₀' 1) := by
    rw [muLocSO_eq_comap v _ hQ' (by omega) one_pos]
    exact Weil.sigmaFinite_comap_subtype (muLoc v Q₀' 1)
      (O := (soSub (QQ' Q₀') (v.adicCompletion F) : Set (orthGroup (QQ' Q₀') (v.adicCompletion F))))
      (isOpen_soSub v (QQ' Q₀') (QQ'_nondeg Q₀' hQ')).measurableSet
  rw [lerayMeasure_orbital_finitePlace v m₀ hm Q₀' hQ' hn, lintegral_smul_measure,
    lintegral_map hf (measurable_orbSO v m₀ hm Q₀' hQ' hn),
    lintegral_prod (fun a => f (orbSO v m₀ hm Q₀' hQ' hn a))
      (hf.comp (measurable_orbSO v m₀ hm Q₀' hQ' hn)).aemeasurable, smul_eq_mul]

/-- **The Leray measure on the sphere is the Leray measure of the cone factor** (`σ_m` is carried by the sphere): the push-forward
of the sphere measure `nuS` to `V_v = F_v^{n+1}` is `σ_m = lerayMeasure … (ι m₀)`. -/
theorem map_val_nuS (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) :
    (nuS v m₀ hm Q₀' hQ').map Subtype.val =
      lerayMeasure v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v (hQ0 m₀ Q₀' hm hQ'))
        ((NF.ι v m₀ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  have hemb := MeasurableEmbedding.subtype_coe (FibreLeray.measurableSet_sphereSet v (splitForm m₀ Q₀') (mm m₀))
  unfold nuS FibreLeray.sphereMeasure
  rw [hemb.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have := FibreLeray.sig_sph_compl v (splitForm m₀ Q₀') (hQ0 m₀ Q₀' hm hQ') (algebraMap F (v.adicCompletion F) (mm m₀))
  rw [ae_iff]
  convert this using 2
  ext x
  simp [FibreLeray.sphereSet_eq]

/-- **The product formula for the local constants**: the constants `|2m₀|_w^{-n}` of the orbital identity (finite places
here, the infinite places) multiply to `1` over all places of `F`
(the finite product runs over the places dividing `2m₀`, at all others `|2m₀|_v = 1`). -/
@[kb "weil1982" "§2.1 (product formula) [unverified]"]
theorem prod_orbital_constants_eq_one (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (n : ℕ) :
    (∏ w : InfinitePlace F, ((w (algebraMap (𝓞 F) F (2 * m₀)) ^ w.mult) ^ n)⁻¹) *
      ∏ v ∈ badSet m₀ hm, (absTwoM v m₀ ^ n)⁻¹ = 1 := by
  have hx : algebraMap (𝓞 F) F (2 * m₀) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ RingOfIntegers.coe_injective]; exact mul_ne_zero two_ne_zero hm
  have h1 := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 F) F (2 * m₀))
  have h2 := prod_absTwoM m₀ hm
  have h3 : normTwoM m₀ = |((Algebra.norm ℚ (algebraMap (𝓞 F) F (2 * m₀)) : ℚ) : ℝ)| := by
    unfold normTwoM; exact prod_norm_embeddings _
  rw [h3] at h2
  have hN : (0 : ℝ) < |((Algebra.norm ℚ (algebraMap (𝓞 F) F (2 * m₀)) : ℚ) : ℝ)| := by
    rw [abs_pos, Ne, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff]; exact hx
  rw [Rat.cast_abs] at h1
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, Finset.prod_pow, h1, h2]
  have hNn : (0 : ℝ) < |((Algebra.norm ℚ (algebraMap (𝓞 F) F (2 * m₀)) : ℚ) : ℝ)| ^ n := pow_pos hN n
  rw [inv_pow]
  field_simp

end SO

end QuadFormsKB.Tamagawa.Measure.FibreSO
