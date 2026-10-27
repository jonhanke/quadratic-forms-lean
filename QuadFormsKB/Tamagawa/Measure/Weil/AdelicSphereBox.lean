import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereGood
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalReal
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFibProof
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamUnimodular

/-!
# The sphere measure on boxes

For the constructed adelic sphere data, the quotient measure $\sigma$ satisfies
(**`sphereMeasure_mul_secMulImage`**) $\sigma(A)\,\mu'(B) = \mu(s(A)\,\iota(B))$ for symmetric $B$ (inversion invariance of
`muTam`, `muTam_inv_preimage`), which reduces $\sigma$ on product sets to the local orbital identities.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

include hQ in
theorem sphereMeasure_mul_preimage {A : Set (adelicSphere Q₀ ρ)} (hA : MeasurableSet A)
    {B : Set (SOAdele S.C.Q')} (hB : MeasurableSet B) :
    muTam Q₀ hQ (fun _ => 1) ((S.coordEquiv hρ).symm ⁻¹' (A ×ˢ B)) =
      S.sphereMeasure hρ hQ hk A * muTam S.C.Q' S.C.hQ' (fun _ => 1) B := by
  have hμ' := isFiniteMeasureOnCompacts_muTam' S.C.Q' S.C.hQ' (fun _ => 1)
  have hspec := S.refSet_spec hk
  have hμ : ∀ (h' : SOAdele S.C.Q') (E : Set (SOAdele Q₀)), MeasurableSet E →
      muTam Q₀ hQ (fun _ => 1) ((fun g => S.iota h' * g) ⁻¹' E) = muTam Q₀ hQ (fun _ => 1) E :=
    fun h' E _ => measure_preimage_mul _ _ _
  exact quotMeasure_mul (S.coordEquiv hρ) S.iota (fun x h h' => S.coordFun_mul hρ x h h')
    (muTam Q₀ hQ fun _ => 1) hμ (muTam S.C.Q' S.C.hQ' fun _ => 1) (muTam_ne_zero S.C.Q' S.C.hQ' hk) hspec.1
    hspec.2.1 hspec.2.2 (S.coverSet hρ) (S.measurableSet_coverSet hρ) (S.iUnion_coverSet hρ)
    (S.coverSet_fin hρ hQ) hB hA

theorem coordEquiv_symm_preimage {A : Set (adelicSphere Q₀ ρ)} {B : Set (SOAdele S.C.Q')}
    (hBsym : ∀ h, h⁻¹ ∈ B ↔ h ∈ B) :
    (S.coordEquiv hρ).symm ⁻¹' (A ×ˢ B) = (fun g => g⁻¹) ⁻¹' secMulImage (S.sphereSection hρ) S.iota A B := by
  ext g
  simp only [mem_preimage, mem_prod]
  constructor
  · intro hg
    set p := (S.coordEquiv hρ).symm g
    have e : g = S.coordFun hρ p := ((S.coordEquiv hρ).apply_symm_apply g).symm
    refine ⟨p.1, hg.1, p.2⁻¹, (hBsym _).mpr hg.2, ?_⟩
    rw [e, coordFun, _root_.mul_inv_rev, inv_inv, map_inv]
  · rintro ⟨y, hy, h, hh, e⟩
    have e' : g = S.coordFun hρ (y, h⁻¹) := by
      rw [coordFun, map_inv, ← _root_.mul_inv_rev, ← e, inv_inv]
    rw [e', show (S.coordEquiv hρ).symm (S.coordFun hρ (y, h⁻¹)) = (y, h⁻¹) from
      (S.coordEquiv hρ).symm_apply_apply (y, h⁻¹)]
    exact ⟨hy, (hBsym h).mpr (by simpa using hh)⟩

include hQ in
/-- **$\sigma(A)\,\mu'(B) = \mu(s(A)\,\iota(B))$** for symmetric measurable $B$. -/
theorem sphereMeasure_mul_secMulImage {A : Set (adelicSphere Q₀ ρ)} (hA : MeasurableSet A)
    {B : Set (SOAdele S.C.Q')} (hB : MeasurableSet B) (hBsym : ∀ h, h⁻¹ ∈ B ↔ h ∈ B) :
    S.sphereMeasure hρ hQ hk A * muTam S.C.Q' S.C.hQ' (fun _ => 1) B =
      muTam Q₀ hQ (fun _ => 1) (secMulImage (S.sphereSection hρ) S.iota A B) := by
  have hm : MeasurableSet ((S.coordEquiv hρ).symm ⁻¹' (A ×ˢ B)) := (S.coordEquiv hρ).symm.measurable (hA.prod hB)
  rw [← S.sphereMeasure_mul_preimage hρ hQ hk hA hB, S.coordEquiv_symm_preimage hρ hBsym]
  rw [S.coordEquiv_symm_preimage hρ hBsym] at hm
  have hE : MeasurableSet (secMulImage (S.sphereSection hρ) S.iota A B) := by
    have := measurable_inv hm
    simpa [Set.preimage_preimage] using this
  exact muTam_inv_preimage Q₀ hQ (by omega) _ hE

/-! ### Product sets (totally real $F$) -/

section TotallyReal

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

variable (Q₀ ρ) in
/-- **The product set** $\prod_wA_w\times\prod_v(T_v\cap L_v)$ in $T(\rho)_{\mathbb A}$. -/
def boxA (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ))) :
    Set (adelicSphere Q₀ ρ) :=
  {y | (∀ w, (⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩ : Sph (QRe Q₀ w) (σR w ρ)) ∈ AR w) ∧
    ∀ v, IntVec v (adV y.1 v)}

/-- **The product set** $\prod_wB_w\times SO(\hat L')$ in $SO(Q')(\mathbb A)$. -/
def boxB (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w))) : Set (SOAdele S.C.Q') :=
  {h | (∀ w, h.1.1 w ∈ BR w) ∧ h.2 ∈ KSO S.C.Q'}

/-- The local images at the real places. -/
def ER (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w))) (w : {w : InfinitePlace F // w.IsReal}) :
    Set (ArchSO (QRe Q₀ w)) :=
  secMulImage (S.secSOR hρ w) (S.iotaR w) (AR w) (BR w)

/-- The local images at the finite places. -/
def EV (v : HeightOneSpectrum (𝓞 F)) : Set (SOv v Q₀) :=
  secMulImage (S.secSO hρ v) (S.iotaSO v) (intSph Q₀ ρ v) (soStabSO v S.C.Q' : Set (SOv v S.C.Q'))

theorem evalSO_sphereSection (y : adelicSphere Q₀ ρ) (v : HeightOneSpectrum (𝓞 F)) :
    evalSO Q₀ v (S.sphereSection hρ y).2 =
      S.secSO hρ v ⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩ := rfl

theorem evalSO_iota (h : SOAdele S.C.Q') (v : HeightOneSpectrum (𝓞 F)) :
    evalSO Q₀ v (S.iota h).2 = S.iotaSO v (evalSO S.C.Q' v h.2) := rfl

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

set_option maxHeartbeats 1000000 in
/-- **$s(A)\,\iota(B)$ for product sets is a product set.** -/
theorem secMulImage_box (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w))) :
    secMulImage (S.sphereSection hρ) S.iota (boxA Q₀ ρ AR) (S.boxB BR) =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ ∀ v, evalSO Q₀ v g.2 ∈ S.EV hρ v} := by
  ext g
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    refine ⟨fun w => ⟨⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩, hy.1 w, h.1.1 w, hh.1 w, ?_⟩,
      fun v => ⟨⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩, hy.2 v, evalSO S.C.Q' v h.2,
      (mem_KSO_iff S.C.Q' h.2).mp hh.2 v, ?_⟩⟩
    · rw [← S.secInf_fst, ← S.iota_fst]; rfl
    · rw [← S.evalSO_sphereSection, ← S.evalSO_iota, Prod.snd_mul, map_mul]
  · rintro ⟨hgR, hgV⟩
    choose yw hyw hw hhw ew using hgR
    choose yv hyv hv hhv ev using hgV
    -- the adelic point
    let y : AdeleSpace F (Fin (k + 1)) := fun j =>
      (((fun w => (yw w).1 j), (fun w => isEmptyElim w)),
        ⟨fun v => (yv v).1 j, Filter.Eventually.of_forall fun v =>
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hyv v j)⟩)
    have hyR : ∀ w, adR y w = (yw w).1 := fun w => rfl
    have hyV : ∀ v, adV y v = (yv v).1 := fun v => rfl
    have hyT : y ∈ adelicSphere Q₀ ρ := ⟨fun w => by rw [hyR]; exact (mem_sphR_iff Q₀ ρ w _).mp (yw w).2,
      fun w => isEmptyElim w, fun v => by rw [hyV]; exact (mem_sphV_iff Q₀ ρ v _).mp (yv v).2⟩
    let y' : adelicSphere Q₀ ρ := ⟨y, hyT⟩
    have hyA : y' ∈ boxA Q₀ ρ AR := ⟨fun w => by
      have : (⟨adR y'.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y'.2.1 w)⟩ : Sph (QRe Q₀ w) (σR w ρ)) = yw w :=
        Subtype.ext rfl
      rw [this]; exact hyw w, fun v => by rw [show adV y'.1 v = (yv v).1 from rfl]; exact hyv v⟩
    -- the adelic stabilizer element
    let hf : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) :=
      ⟨fun v => ((hv v : SOv v S.C.Q') : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)),
        Filter.Eventually.of_forall fun v => Subgroup.mem_subgroupOf.mp (hhv v)⟩
    have hfso : hf ∈ soAf (S.C.Q'.map (algebraMap (𝓞 F) F)) := fun v => (hv v).2
    let h : SOAdele S.C.Q' := ((hw, fun w => isEmptyElim w), ⟨hf, hfso⟩)
    have hB : h ∈ S.boxB BR := ⟨hhw, (mem_KSO_iff S.C.Q' _).mpr fun v => hhv v⟩
    refine ⟨y', hyA, h, hB, ?_⟩
    refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => isEmptyElim w)) ?_
    · rw [ew w]
      show _ = (S.secInf hρ y').1 w * S.iotaR w (hw w)
      rw [S.secInf_fst]
      congr 2
    · apply Subtype.ext; apply RestrictedProduct.ext; intro v
      have e := congrArg (fun x : SOv v Q₀ => (x : orthGroup QF (v.adicCompletion F))) (ev v)
      simp only [coe_evalSO] at e
      rw [e]
      show _ = (((S.sphereSection hρ y').2 : OAf QF) v) * ((S.iota h).2 : OAf QF) v
      have e1 : ((S.sphereSection hρ y').2 : OAf QF) v =
          ((S.secSO hρ v ⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : SOv v Q₀) :
            orthGroup QF (v.adicCompletion F)) := rfl
      have e2 : ((S.iota h).2 : OAf QF) v = ((S.iotaSO v (hv v) : SOv v Q₀) : orthGroup QF (v.adicCompletion F)) :=
        rfl
      rw [e1, e2]
      have : (⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : sphV Q₀ ρ v) = yv v := Subtype.ext rfl
      rw [this]; rfl

/-- The archimedean box in $G_\infty$ (totally real). -/
def archBox {n : ℕ} (Q : QuadForm (𝓞 F) n) (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w))) :
    Set (GInfSO Q) := (Set.pi univ E) ×ˢ univ

open Classical in
theorem muArchTamSO_archBox {n : ℕ} (Q : QuadForm (𝓞 F) n) (hQ' : Q.Nondegenerate)
    (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w))) :
    muArchTamSO Q hQ' (archBox Q E) =
      ENNReal.ofReal (cF F n) * ∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w) := by
  have hc : cxWeil F n = 1 := by
    rw [cxWeil, show nrComplexPlaces F = 0 from Fintype.card_eq_zero, mul_zero, pow_zero]
  have : ∀ w : {w : InfinitePlace F // w.IsReal},
      SigmaFinite (lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q hQ' w); infer_instance
  have : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (LerayComplex.lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w)) := fun w => isEmptyElim w
  have hpc : (Measure.pi fun w : {w : InfinitePlace F // w.IsComplex} =>
      LerayComplex.lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w)) univ = 1 := by
    rw [Measure.pi_univ, Fintype.prod_empty]
  have hpr : (Measure.pi fun w : {w : InfinitePlace F // w.IsReal} =>
      lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w)) (Set.pi univ E) =
      ∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w) := Measure.pi_pi _ _
  rw [muArchTamSO, hc, mul_one, Measure.smul_apply, smul_eq_mul, archBox, LerayArch.muArchNF,
    LerayArch.muArchLeray, Measure.prod_prod]
  erw [hpr, hpc, mul_one]

open Classical in
/-- **The Tamagawa measure of a product set.** -/
theorem muTam_prodSet {n : ℕ} (Q : QuadForm (𝓞 F) n) (hQ' : Q.Nondegenerate)
    (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w))) (Ef : Set (SOAf Q)) :
    muTam Q hQ' (fun _ => 1) {g | (∀ w, g.1.1 w ∈ E w) ∧ g.2 ∈ Ef} =
      ENNReal.ofReal (cF F n) * (∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w)) *
        Measure.muFin Q (fun _ => 1) Ef := by
  have : {g : SOAdele Q | (∀ w, g.1.1 w ∈ E w) ∧ g.2 ∈ Ef} = archBox Q E ×ˢ Ef := by
    ext g; simp [archBox, Set.mem_pi]
  rw [this, muTam, Measure.prod_prod, muArchTamSO_archBox]

end TotallyReal

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
