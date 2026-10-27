import QuadFormsKB.Tamagawa.Measure.OrbitalReal
import QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-!
# The Leray measure of an orbit box $\{s(x)\,\mathrm{diag}(1,h) : x\in A,\ h\in W\}$

**Layer:** one archimedean place; a form $Q$ in $m+1$ variables equal to $\langle c\rangle\perp Q'$ (`splitForm`), any signature,
$c\ne0$, $Q'$ nondegenerate; a measurable section $s$ of the orbit map $g\mapsto ge_0$ onto the sphere $S_c = \{Q = c\}$; the embedding
$h\mapsto\mathrm{diag}(1,h)$ of $SO(Q')$.

* **`lerayMeasure_image_sec`** (real places): $\mu_Q(\{s(x)\,\mathrm{diag}(1,h) : x\in A,\ h\in W\}) =
  |2c|^{-m}\,\sigma_c(A)\,\mu_{Q'}(W)$;
* **`lerayMeasureC_image_sec`** (complex places): the same with $|2c|_{\mathbb C}^{-m} = |2c|^{-2m}$.

These are the real and complex orbital identities (`lerayMeasure_orbital`, `lerayMeasureC_orbital`)
evaluated on a product set; the form is only required to be *equal* to $\langle c\rangle\perp Q'$
(so that it applies to $Q = \langle1,-a,-b,ab\rangle^{\sigma_w}$ directly),
and the section and the embedding are given by their matrices.
-/

open MeasureTheory Measure Matrix Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure

variable {m : ℕ}

theorem cornerMat_one_mulVec_e₀ {R : Type*} [CommRing R] (M : Matrix (Fin m) (Fin m) R) :
    cornerMat (1 : R) M *ᵥ (e₀ : Fin (m + 1) → R) = e₀ := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, cornerMat]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, cornerMat]

theorem cornerMat_one_injective {R : Type*} [CommRing R] :
    Function.Injective (cornerMat (1 : R) : Matrix (Fin m) (Fin m) R → _) := fun M N h => by
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  simpa using this

/-! ### Real places -/

section Real

open OrbitalReal SphereLeray LerayReal

theorem lerayMeasure_image_sec {c : ℝ} (hc : c ≠ 0) {Q' : QuadForm ℝ m} (hQ' : gramDetR Q' ≠ 0)
    (Q : QuadForm ℝ (m + 1)) (hQe : Q = splitForm c Q') (hQ : gramDetR Q ≠ 0)
    (sec : Sph Q c → ArchSO Q) (hsec : Measurable sec)
    (hspec : ∀ x, ArchSOInst.mat _ (sec x) *ᵥ (e₀ : Fin (m + 1) → ℝ) = (x : Fin (m + 1) → ℝ))
    (ι' : ArchSO Q' → ArchSO Q) (hι' : ∀ h, ArchSOInst.mat _ (ι' h) = cornerMat 1 (ArchSOInst.mat Q' h))
    {A : Set (Sph Q c)} (hA : MeasurableSet A) {W : Set (ArchSO Q')} (_hW : MeasurableSet W) :
    lerayMeasure Q hQ ((fun p : Sph Q c × ArchSO Q' => sec p.1 * ι' p.2) '' (A ×ˢ W)) =
      ENNReal.ofReal ((|2 * c| ^ m)⁻¹) * (sig Q c A * lerayMeasure Q' hQ' W) := by
  subst hQe
  have hι : ι' = iota c Q' := funext fun h => Subtype.ext (by
    exact Units.ext ((hι' h).trans (mat_iota c Q' h).symm))
  subst hι
  set s : SphSection c Q' := ⟨sec, hsec, hspec⟩
  have hinj : Function.Injective (orb s) := by
    rintro ⟨x, h⟩ ⟨x', h'⟩ hxh
    have hx : x = x' := by
      apply Subtype.ext
      have e : ∀ (y : Sph (splitForm c Q') c) (k : ArchSO Q'),
          ArchSOInst.mat _ (orb s (y, k)) *ᵥ (e₀ : Fin (m + 1) → ℝ) = (y : Fin (m + 1) → ℝ) := fun y k => by
        rw [orb, show ArchSOInst.mat _ (s.toFun y * iota c Q' k) =
          ArchSOInst.mat _ (s.toFun y) * ArchSOInst.mat _ (iota c Q' k) from rfl, ← mulVec_mulVec, mat_iota,
          cornerMat_one_mulVec_e₀, s.spec]
      rw [← e x h, ← e x' h', hxh]
    subst hx
    have hk : iota c Q' h = iota c Q' h' := mul_left_cancel hxh
    have := congrArg (ArchSOInst.mat _) hk
    rw [mat_iota, mat_iota] at this
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (Units.ext (cornerMat_one_injective this))⟩
  have hme : MeasurableEmbedding (orb s) := (measurable_orb s).measurableEmbedding hinj
  have := isHaarMeasure_lerayMeasure hQ'
  have himg : (fun p : Sph (splitForm c Q') c × ArchSO Q' => s.toFun p.1 * iota c Q' p.2) '' (A ×ˢ W) =
      orb s '' (A ×ˢ W) := rfl
  rw [himg, lerayMeasure_orbital hc hQ' s, Measure.smul_apply, hme.map_apply, hinj.preimage_image,
    Measure.prod_prod, smul_eq_mul]

end Real

/-! ### Complex places -/

section Complex

open OrbitalComplex SphereLerayC LerayComplex

theorem lerayMeasureC_image_sec {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (hQ' : gramDetC Q' ≠ 0)
    (Q : QuadForm ℂ (m + 1)) (hQe : Q = splitForm c Q') (hQ : gramDetC Q ≠ 0)
    (sec : SphC Q c → ArchSOC Q) (hsec : Measurable sec)
    (hspec : ∀ x, ArchSOC.mat _ (sec x) *ᵥ (e₀ : Fin (m + 1) → ℂ) = (x : Fin (m + 1) → ℂ))
    (ι' : ArchSOC Q' → ArchSOC Q) (hι' : ∀ h, ArchSOC.mat _ (ι' h) = cornerMat 1 (ArchSOC.mat Q' h))
    {A : Set (SphC Q c)} (hA : MeasurableSet A) {W : Set (ArchSOC Q')} (_hW : MeasurableSet W) :
    lerayMeasureC Q hQ ((fun p : SphC Q c × ArchSOC Q' => sec p.1 * ι' p.2) '' (A ×ˢ W)) =
      (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) * (sigC Q c A * lerayMeasureC Q' hQ' W) := by
  subst hQe
  have hι : ι' = iotaC c Q' := funext fun h => Subtype.ext (by
    exact Units.ext ((hι' h).trans (mat_iotaC c Q' h).symm))
  subst hι
  set s : SphSectionC c Q' := ⟨sec, hsec, hspec⟩
  have hinj : Function.Injective (orbC s) := by
    rintro ⟨x, h⟩ ⟨x', h'⟩ hxh
    have hx : x = x' := by
      apply Subtype.ext
      have e : ∀ (y : SphC (splitForm c Q') c) (k : ArchSOC Q'),
          ArchSOC.mat _ (orbC s (y, k)) *ᵥ (e₀ : Fin (m + 1) → ℂ) = (y : Fin (m + 1) → ℂ) := fun y k => by
        rw [orbC, show ArchSOC.mat _ (s.toFun y * iotaC c Q' k) =
          ArchSOC.mat _ (s.toFun y) * ArchSOC.mat _ (iotaC c Q' k) from rfl, ← mulVec_mulVec, mat_iotaC,
          cornerMat_one_mulVec_e₀, s.spec]
      rw [← e x h, ← e x' h', hxh]
    subst hx
    have hk : iotaC c Q' h = iotaC c Q' h' := mul_left_cancel hxh
    have := congrArg (ArchSOC.mat _) hk
    rw [mat_iotaC, mat_iotaC] at this
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (Units.ext (cornerMat_one_injective this))⟩
  have hme : MeasurableEmbedding (orbC s) := (measurable_orbC s).measurableEmbedding hinj
  have := isHaarMeasure_lerayMeasureC hQ'
  have himg : (fun p : SphC (splitForm c Q') c × ArchSOC Q' => s.toFun p.1 * iotaC c Q' p.2) '' (A ×ˢ W) =
      orbC s '' (A ×ˢ W) := rfl
  rw [himg, lerayMeasureC_orbital hc hQ' s, Measure.smul_apply, hme.map_apply, hinj.preimage_image,
    Measure.prod_prod, smul_eq_mul]

end Complex

end QuadFormsKB.Tamagawa.Measure
