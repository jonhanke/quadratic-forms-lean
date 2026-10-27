/-
# $\mu_P(\pi(S_0^U))$ for the non-square model over every number field

**Layer:** $F$ any number field, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$ (no total reality, no definiteness),
$G^\natural$ = `gnatBCO`, $H_S$ = `HS` over $K$.

* **`nsS0U`**: $S_0^U = \{g\in G^\natural : g_1\in H_S,\ \mathrm{nsInf}(g)\in U\}$ for $U\subseteq G_\infty$ open with $1\in U$.
* **`nsInf_zHom`**: the centre maps to $1$ in $G_\infty$.
* **`BinfPos`**, **`nsXF'`**, **`tamIdeles_nsXF'`**: the $F$-side idele set (shell $|t_w|\in(1,4)$ at every archimedean place,
  positive at the real places, finite part of $\iota(t)$ in $N_H$) and its measure
  $\omega_\infty(\mathrm{BinfPos})\,\mu_f(\mathrm{box}(S,N))$.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFib
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSMaps
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqAnyD
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqFibration
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSConeK
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqPDArch

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat

noncomputable section

section NSAny

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ
local notation "nsI" => nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0

/-- **The test set** $S_0^U = \{g\in G^\natural : g_1\in H_S,\ \mathrm{nsInf}(g)\in U\}$. -/
def nsS0U (U : Set (GInfSO (qNS a b d))) : Set (dN).G :=
  {g | g ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ∧ nsI g ∈ U}

theorem isOpen_nsS0U {U : Set (GInfSO (qNS a b d))} (hUo : IsOpen U) :
    IsOpen (nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U) :=
  (isOpen_nsS0 hb₀ hα0 hβ0 ((isOpen_quatCongS SK mK hmK1).preimage (continuous_quatFinPart α β))).inter
    (hUo.preimage (continuous_nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0))

/-- **The centre of $G^\natural$ maps to $1$ in $G_\infty$.** -/
theorem nsInf_zHom (c : (Adeles F)ˣ) : nsI ((dN).zHom c) = 1 :=
  congrArg Prod.fst ((nsAdele_eq_one_iff hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 _).2 ⟨c, rfl⟩)

theorem nsInf_zHom_mul (c : (Adeles F)ˣ) (g : (dN).G) : nsI ((dN).zHom c * g) = nsI g := by
  rw [map_mul, nsInf_zHom hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0, one_mul]

end NSAny

/-! ### The $F$-side idele set, every number field -/

section FSideAny

/-- The shell $B_\infty$ (all archimedean places, $|t_w|\in(1,4)$) intersected with the positivity at the real places. -/
def BinfPos {F : Type} [Field F] [NumberField F] : Set (mixedSpace F)ˣ :=
  {t | t ∈ (Binf : Set (mixedSpace F)ˣ) ∧ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < (t : mixedSpace F).1 w}

theorem measurableSet_BinfPos {F : Type} [Field F] [NumberField F] : MeasurableSet (BinfPos (F := F)) :=
  measurableSet_Binf.inter (measurableSet_of_forall_real (P := fun _ x => 0 < x) fun _ => measurableSet_Ioi)

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {d : 𝓞 F} {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (S : Finset (HeightOneSpectrum (𝓞 F))) (SK : Finset (HeightOneSpectrum (𝓞 K)))
  (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

variable (F α β) in
/-- **$X_F' = \{t\in B'_F : t_v>0\ (v\text{ real}),\ \iota(t)_f\in N_H\}$.** -/
def nsXF' : Set (Adeles F)ˣ :=
  {t | t ∈ (Bset' : Set (Adeles F)ˣ) ∧ (∀ w : {w : InfinitePlace F // w.IsReal}, 0 < (t : Adeles F).1.1 w) ∧
    finPart (adeleUnitsMap F K t) ∈ NH α β SK mK hmK1}

include hb₀ hb₁ in
theorem nsN_subset' (v : HeightOneSpectrum (𝓞 F)) : nsN α β mK hmK1 v ⊆ unitsVSub v := by
  intro r hr
  obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v
  have := nL_subset mK hmK1 w (hr w hw)
  exact (valued_localRingHom_eq_one_iff w hw _).1 this

include hb₀ hb₁ in
theorem nsXF'_eq_box(hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S) :
    nsXF' F α β SK mK hmK1 = idelesEquiv F ⁻¹' ((BinfPos (F := F)) ×ˢ ideleBox S (nsN α β mK hmK1)) := by
  have hcomp : ∀ (t : (Adeles F)ˣ) (w : HeightOneSpectrum (𝓞 K)),
      unitAt (finPart (adeleUnitsMap F K t)) w = Units.map (localRingHom (underPlace w) w rfl).toMonoidHom
        (unitAt (finPart t) (underPlace w)) := fun t w =>
    Units.ext (by
      change ((adeleUnitsMap F K t : Adeles K)).2 w = _
      rw [coe_adeleUnitsMap, adeleMap_snd_apply_over (underPlace w) w rfl]; rfl)
  ext t
  simp only [nsXF', mem_setOf_eq, mem_preimage, mem_prod]
  constructor
  · rintro ⟨hB, hpos, hN⟩
    refine ⟨⟨hB.1, hpos⟩, fun u => ?_⟩
    split_ifs with hu
    · intro w hw
      subst hw
      have := hN w
      rw [if_pos ((hSK w).2 hu), hcomp] at this
      exact this
    · exact (finPart_mem_OHatUnits_iff t).1 hB.2 u
  · rintro ⟨⟨hinf, hpos⟩, hbox⟩
    have hfin : finPart t ∈ OHatUnits F := by
      change (idelesEquiv F t).2 ∈ OHatUnits F
      rw [← SetLike.mem_coe, ← ideleBox_empty (nsN α β mK hmK1)]
      intro u
      have := hbox u
      simp only [Finset.notMem_empty, ite_false]
      split_ifs at this with hu
      · exact nsN_subset' hb₀ hb₁ mK hmK1 u this
      · exact this
    refine ⟨⟨hinf, hfin⟩, hpos, fun w => ?_⟩
    split_ifs with hw
    · have := hbox (underPlace w)
      rw [if_pos ((hSK w).1 hw)] at this
      rw [hcomp]; exact this w rfl
    · exact (finPart_mem_OHatUnits_iff _).1 ((finPart_adeleUnitsMap_mem_iff hb₀ hb₁ t).2 hfin) w

include hb₀ hb₁ in
/-- **$\mathrm{tamIdeles}_F(X_F') = \omega_\infty(\mathrm{BinfPos})\,\mu_f(\mathrm{box}(S,N))$**, every number field. -/
theorem tamIdeles_nsXF' (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S) :
    tamIdeles F (nsXF' F α β SK mK hmK1) =
      omegaInf F (BinfPos (F := F)) * muFinUnits F (ideleBox S (nsN α β mK hmK1)) := by
  rw [nsXF'_eq_box hb₀ hb₁ S SK mK hmK1 hSK, tamIdeles_prod]

theorem measurableSet_nsN' (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (nsN α β mK hmK1 v) := by
  have e : nsN α β mK hmK1 v = ⋂ w : PlaceSet (K := K) v,
      (Units.map (localRingHom v w.1 w.2).toMonoidHom) ⁻¹' nL α β mK hmK1 w.1 := by
    ext r
    simp only [nsN, mem_setOf_eq, mem_iInter, mem_preimage]
    exact ⟨fun h w => h w.1 w.2, fun h w hw => h ⟨w, hw⟩⟩
  rw [e]
  exact MeasurableSet.iInter fun w => (measurableSet_nL mK hmK1 w.1).preimage
    (Continuous.units_map _ (continuous_localRingHom v w.1 w.2)).measurable

include hb₀ hb₁ in
theorem measurableSet_nsXF' (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S) :
    MeasurableSet (nsXF' F α β SK mK hmK1) := by
  rw [nsXF'_eq_box hb₀ hb₁ S SK mK hmK1 hSK]
  exact (measurableSet_BinfPos.prod (measurableSet_ideleBox S _ fun v _ => measurableSet_nsN' mK hmK1 v)).preimage
    (idelesEquiv F).continuous.measurable

end FSideAny

/-! ### Archimedean triviality of the base change -/

section BCArch

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)
  {a b : F} {A' B' : K} (hA' : A' = algebraMap F K a) (hB' : B' = algebraMap F K b)
  {L : Type*} [Field L] (f : Adeles F →+* L) (hf : f (⟨0, 1⟩ : Adeles F) = 0)

include hb₀ hb₁ hf in
/-- If $y\in\mathbb A_K$ has zero archimedean part, then $\Theta^{-1}y$ is killed by every `f` vanishing on the finite idempotent. -/
theorem quadBC_symm_arch_zero (y : Adeles K) (hy : y.1 = 0) :
    f ((quadBaseChange hb₀ hb₁).symm y).re = 0 ∧ f ((quadBaseChange hb₀ hb₁).symm y).im = 0 := by
  set z := (quadBaseChange hb₀ hb₁).symm y with hz
  set e : QuadAdele F d := ⟨(⟨0, 1⟩ : Adeles F), 0⟩ with he
  have h1 : adeleMap F K (⟨0, 1⟩ : Adeles F) * y = y := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, adeleMap_fst, hy]
      change infRingHom F K (0 : mixedSpace F) * 0 = 0
      rw [mul_zero]
    · rw [Prod.snd_mul, adeleMap_snd]
      change finMap F K 1 * y.2 = y.2
      rw [map_one, one_mul]
  have h2 : e * z = z := by
    apply (quadBaseChange hb₀ hb₁).injective
    rw [map_mul, hz, RingEquiv.apply_symm_apply, quadBaseChange_apply]
    simp only [he, map_zero, mul_zero, add_zero]
    exact h1
  have h3 := congrArg QuadraticAlgebra.re h2
  have h4 := congrArg QuadraticAlgebra.im h2
  simp only [he, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, mul_zero, zero_mul, add_zero, zero_add] at h3 h4
  refine ⟨?_, ?_⟩
  · rw [← h3, map_mul, hf, zero_mul]
  · rw [← h4, map_mul, hf, zero_mul]

include hb₀ hb₁ hf in
/-- If $y\in\mathbb A_K$ has archimedean part $1$, then $f$ sends $(\Theta^{-1}y)$ to $1$ (real part) and $0$ (imaginary part)
for every `f` vanishing on the finite idempotent and with `f 1 = 1`. -/
theorem quadBC_symm_arch_one (y : Adeles K) (hy : y.1 = 1) :
    f ((quadBaseChange hb₀ hb₁).symm y).re = 1 ∧ f ((quadBaseChange hb₀ hb₁).symm y).im = 0 := by
  have h := quadBC_symm_arch_zero hb₀ hb₁ f hf (y - 1) (by rw [Prod.fst_sub, hy]; simp)
  have e : (quadBaseChange hb₀ hb₁).symm y = (quadBaseChange hb₀ hb₁).symm (y - 1) + 1 := by
    rw [map_sub, map_one]; ring
  rw [e, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_add,
    map_add, h.1, h.2, map_one, map_zero]
  simp

theorem quatBC_symm_re (w : QuatAdele (F := K) (algebraMap F K a) (algebraMap F K b)) :
    ((quatBaseChange hb₀ hb₁ a b).symm w).re = (quadBaseChange hb₀ hb₁).symm w.re := by
  apply (quadBaseChange hb₀ hb₁).injective
  rw [← quatBaseChange_re, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem bcRing_re (x : QuatAdele (F := K) A' B') :
    (bcRing hb₀ hb₁ hA' hB' x).re = (quadBaseChange hb₀ hb₁).symm x.re := by
  change ((quatBaseChange hb₀ hb₁ a b).symm (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') x)).re = _
  rw [quatBC_symm_re]; rfl

theorem bcRing_imI (x : QuatAdele (F := K) A' B') :
    (bcRing hb₀ hb₁ hA' hB' x).imI = (quadBaseChange hb₀ hb₁).symm x.imI := by
  change ((quatBaseChange hb₀ hb₁ a b).symm (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') x)).imI = _
  apply (quadBaseChange hb₀ hb₁).injective
  rw [← quatBaseChange_imI, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; rfl

theorem bcRing_imJ (x : QuatAdele (F := K) A' B') :
    (bcRing hb₀ hb₁ hA' hB' x).imJ = (quadBaseChange hb₀ hb₁).symm x.imJ := by
  change ((quatBaseChange hb₀ hb₁ a b).symm (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') x)).imJ = _
  apply (quadBaseChange hb₀ hb₁).injective
  rw [← quatBaseChange_imJ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; rfl

theorem bcRing_imK (x : QuatAdele (F := K) A' B') :
    (bcRing hb₀ hb₁ hA' hB' x).imK = (quadBaseChange hb₀ hb₁).symm x.imK := by
  change ((quatBaseChange hb₀ hb₁ a b).symm (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') x)).imK = _
  apply (quadBaseChange hb₀ hb₁).injective
  rw [← quatBaseChange_imK, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; rfl

include hf in
/-- **Archimedean triviality**: if $x\in D'\otimes\mathbb A_K$ has archimedean part $1$, then every component map `deMap f`
(with `f` vanishing on the finite idempotent) sends $\Theta^{-1}x$ to $1$. -/
theorem deMap_bcRing_of_arch_one (x : QuatAdele (F := K) A' B') (h0 : x.re.1 = 1) (h1 : x.imI.1 = 0)
    (h2 : x.imJ.1 = 0) (h3 : x.imK.1 = 0) {ta tb td : L} (hd : f (diagRing F d) = td) (ha : f (diagRing F a) = ta)
    (hb : f (diagRing F b) = tb) : deMap f hd ha hb (bcRing hb₀ hb₁ hA' hB' x) = 1 := by
  have e0 := quadBC_symm_arch_one hb₀ hb₁ f hf x.re h0
  have e1 := quadBC_symm_arch_zero hb₀ hb₁ f hf x.imI h1
  have e2 := quadBC_symm_arch_zero hb₀ hb₁ f hf x.imJ h2
  have e3 := quadBC_symm_arch_zero hb₀ hb₁ f hf x.imK h3
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [deMap_re, qeMap_re, bcRing_re, QuaternionAlgebra.re_one, QuadraticAlgebra.re_one]; exact e0.1
    · rw [deMap_re, qeMap_im, bcRing_re, QuaternionAlgebra.re_one, QuadraticAlgebra.im_one]; exact e0.2
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [deMap_imI, qeMap_re, bcRing_imI]; simpa using e1.1
    · rw [deMap_imI, qeMap_im, bcRing_imI]; simpa using e1.2
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [deMap_imJ, qeMap_re, bcRing_imJ]; simpa using e2.1
    · rw [deMap_imJ, qeMap_im, bcRing_imJ]; simpa using e2.2
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [deMap_imK, qeMap_re, bcRing_imK]; simpa using e3.1
    · rw [deMap_imK, qeMap_im, bcRing_imK]; simpa using e3.2

end BCArch

section NSAny2

open QuadFormsKB.Quat.Gnat QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ
local notation "nsI" => nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0

include hb₀ hb₁ hα hβ in
/-- **If the first component of $g$ has trivial archimedean part, then $\mathrm{nsInf}(g)=1$.** -/
theorem nsInf_eq_one_of_arch (g : (dN).G)
    (h0 : ((g : MK × (Adeles F)ˣ).1 : QuatAdele (α : K) (β : K)).re.1 = 1)
    (h1 : ((g : MK × (Adeles F)ˣ).1 : QuatAdele (α : K) (β : K)).imI.1 = 0)
    (h2 : ((g : MK × (Adeles F)ˣ).1 : QuatAdele (α : K) (β : K)).imJ.1 = 0)
    (h3 : ((g : MK × (Adeles F)ˣ).1 : QuatAdele (α : K) (β : K)).imK.1 = 0) : nsI g = 1 := by
  refine Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)
  · have key : nsPairR hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) w g = 1 := by
      refine Subtype.ext (Units.ext ?_)
      rw [nsPairR_val]
      exact deMap_bcRing_of_arch_one hb₀ hb₁ hα hβ (fAtR w) rfl _ h0 h1 h2 h3 (fAtR_diag w (d : F))
        (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
    have h1' : (phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 ha0)
          ((map_ne_zero _).2 hd0) (nsPairR hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) w g) :
            GL (Fin 4) ℝ) = 1 := by
      rw [key]; simp
    change ArchSO.incl _ (nsR hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 w g) = ArchSO.incl _ 1
    rw [nsR_incl, nsGLR_apply, h1']
    exact (map_one _).symm
  · have key : nsPairC hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) w g = 1 := by
      refine Subtype.ext (Units.ext ?_)
      rw [nsPairC_val]
      exact deMap_bcRing_of_arch_one hb₀ hb₁ hα hβ (fAtC w) rfl _ h0 h1 h2 h3 (fAtC_diag w (d : F))
        (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
    have h1' : (phiSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 ha0)
          ((map_ne_zero _).2 hd0) (nsPairC hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) w g) :
            GL (Fin 4) ℂ) = 1 := by
      rw [key]; simp
    change ArchSOC.incl _ (nsC hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 w g) = ArchSOC.incl _ 1
    rw [nsC_incl, nsGLC_apply, h1']
    exact (map_one _).symm


include hb₀ hb₁ hα hβ in
set_option maxHeartbeats 1600000 in
/-- **Base points with trivial archimedean image**: for $t\in X_F'$ there is $g\in S_0$ with $p(g)=t$ and $\mathrm{nsInf}(g)=1$. -/
theorem exists_base_point
    (hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1)
    {t : (Adeles F)ˣ} (ht : t ∈ nsXF' F α β SK mK hmK1) :
    ∃ g : (dN).G, (g : MK × (Adeles F)ˣ).2 = t ∧ g ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ∧ nsI g = 1 := by
  obtain ⟨hB, hpos, hN⟩ := ht
  have hB2 : finPart t ∈ OHatUnits F := hB.2
  -- a square root of the archimedean part
  have hγ : ∀ w : {w : InfinitePlace F // w.IsComplex}, ∃ γ : ℂ, γ ^ 2 = (t : Adeles F).1.2 w :=
    fun w => IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose γ hγ using hγ
  have hγ0 : ∀ w, γ w ≠ 0 := fun w h => by
    apply unit_snd_ne_zero (infPart t) w
    change (t : Adeles F).1.2 w = 0
    rw [← hγ w, h]; norm_num
  set r : (mixedSpace F)ˣ := mkInfUnitRC (fun w => Real.sqrt ((t : Adeles F).1.1 w)) γ
    (fun w => (Real.sqrt_pos.2 (hpos w)).ne') hγ0 with hr_def
  have hr : r ^ 2 = infPart t := by
    apply Units.ext
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · rw [Units.val_pow_eq_pow_val]
      change (Real.sqrt ((t : Adeles F).1.1 w)) ^ 2 = (t : Adeles F).1.1 w
      exact Real.sq_sqrt (hpos w).le
    · rw [Units.val_pow_eq_pow_val]
      exact hγ w
  set u : (Adeles F)ˣ := (idelesEquiv F).symm (r, 1) with hu_def
  set t' : (Adeles F)ˣ := (idelesEquiv F).symm (1, finPart t) with ht'_def
  have ht_eq : t = u ^ 2 * t' := by
    apply (idelesEquiv F).injective
    rw [map_mul, map_pow, hu_def, ht'_def]
    simp only [ContinuousMulEquiv.apply_symm_apply, idelesEquiv_apply]
    refine Prod.ext ?_ ?_
    · simp [hr]
    · simp
  have hinf' : infPart t' = 1 := by
    have := congrArg Prod.fst (show idelesEquiv F t' = (1, finPart t) from (idelesEquiv F).apply_symm_apply _)
    exact this
  have hfin' : finPart t' = finPart t := by
    have := congrArg Prod.snd (show idelesEquiv F t' = (1, finPart t) from (idelesEquiv F).apply_symm_apply _)
    exact this
  have hfinu : finPart u = 1 := by
    have := congrArg Prod.snd (show idelesEquiv F u = (r, 1) from (idelesEquiv F).apply_symm_apply _)
    exact this
  -- local data
  obtain ⟨y, hyL, hyt, hyS⟩ := exists_local_cong SK mK hmK1 hSKg (adeleUnitsMap F K t) hN
  have harch : ((adeleUnitsMap F K t' : (Adeles K)ˣ) : Adeles K).1 = 1 := by
    rw [coe_adeleUnitsMap, adeleMap_fst]
    have : (t' : Adeles F).1 = 1 := by
      have := congrArg Units.val hinf'
      exact this
    rw [this]; exact map_one _
  have hfinEq : ∀ w, ((adeleUnitsMap F K t' : (Adeles K)ˣ) : Adeles K).2 w =
      ((adeleUnitsMap F K t : (Adeles K)ˣ) : Adeles K).2 w := by
    intro w
    rw [coe_adeleUnitsMap, coe_adeleUnitsMap, adeleMap_snd, adeleMap_snd]
    have : (t' : Adeles F).2 = (t : Adeles F).2 := by
      have := congrArg Units.val hfin'
      exact this
    rw [this]
  set xh := mkAdeleUnit (α : K) (β : K) (fun _ => 1) (fun _ => 1) y (Filter.Eventually.of_forall hyL) with hxh
  have hG : nrdUnit xh = adeleUnitsMap F K t' := by
    refine nrdUnit_mkAdeleUnit_eq_gen _ _ _ y _ (fun w => ?_) (fun w => ?_) (fun v => ?_)
    · rw [harch]; simp
    · rw [harch]; simp
    · rw [hyt v, hfinEq v]
  let h0 : (dN).G := ⟨(xh, t'), hG⟩
  have hxhS : xh ∈ HS α β SK mK hmK1 := by
    rw [mem_HS]
    exact ⟨fun v => by rw [hxh, unitAtA_mkAdeleUnit]; exact hyL v,
      fun v hv => by rw [hxh, unitAtA_mkAdeleUnit]; exact hyS v hv⟩
  have hzu : (dN).zHom u ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) := by
    change quatScalar (α : K) (β : K) (adeleUnitsMap F K u) ∈ HS α β SK mK hmK1
    rw [quatScalar_mem_HS_iff SK mK hmK1 hα0, finPart_adeleUnitsMap_mem_iff hb₀ hb₁, hfinu]
    exact (OHatUnits F).one_mem
  have h0S : h0 ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) := hxhS
  have hq := (quatUnitsEquiv (α : K) (β : K)).apply_symm_apply (mkInfUnit (α : K) (β : K) (fun _ => 1) (fun _ => 1),
    mkFinUnit (α : K) (β : K) y (Filter.Eventually.of_forall hyL))
  have hq1 : ((quatUnitsEquiv (α : K) (β : K) xh).1 : QuatInf (α : K) (β : K)) =
      ((mkInfUnit (α : K) (β : K) (fun _ => 1) (fun _ => 1) : (QuatInf (α : K) (β : K))ˣ) : QuatInf (α : K) (β : K)) :=
    congrArg (fun p => ((p.1 : (QuatInf (α : K) (β : K))ˣ) : QuatInf (α : K) (β : K))) hq
  refine ⟨(dN).zHom u * h0, ?_, (nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem hzu h0S, ?_⟩
  · change u ^ 2 * t' = t
    exact ht_eq.symm
  · rw [map_mul, nsInf_zHom hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0, one_mul]
    have c0 : (xh : QuatAdele (α : K) (β : K)).re.1 = 1 := by
      have := congrArg QuaternionAlgebra.re hq1
      refine this.trans (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) <;> simp [mkInfUnit]
    have c1 : (xh : QuatAdele (α : K) (β : K)).imI.1 = 0 := by
      have := congrArg QuaternionAlgebra.imI hq1
      refine this.trans (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) <;> simp [mkInfUnit]
    have c2 : (xh : QuatAdele (α : K) (β : K)).imJ.1 = 0 := by
      have := congrArg QuaternionAlgebra.imJ hq1
      refine this.trans (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) <;> simp [mkInfUnit]
    have c3 : (xh : QuatAdele (α : K) (β : K)).imK.1 = 0 := by
      have := congrArg QuaternionAlgebra.imK hq1
      refine this.trans (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) <;> simp [mkInfUnit]
    exact nsInf_eq_one_of_arch hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 h0 c0 c1 c2 c3

set_option maxHeartbeats 3200000 in
include hb₀ hb₁ hα hβ in
/-- **$\mu_P(\pi(S_0^U))\cdot\omega_\infty(V_1)\mu_f(\hat{\mathcal O}_F^\times) =
\mu_{\mathrm{SL}_1(D')}(\{x\in H_S : \mathrm{nsInf}(x,1)\in U\})\cdot\omega_\infty(\mathrm{BinfPos})\,\mu_f(\mathrm{box}(S,N))$**
for every number field $F$ (no total reality), provided the test set is positive at the real places. -/
theorem muP_nsS0U_mul (U : Set (GInfSO (qNS a b d))) (hUo : IsOpen U) (hU1 : (1 : GInfSO (qNS a b d)) ∈ U)
    (hpos : ∀ g : (dN).G, g ∈ nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U →
      ∀ v : {v : InfinitePlace F // v.IsReal}, 0 < ((g : MK × (Adeles F)ˣ).2 : Adeles F).1.1 v)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U) *
        (omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F)) =
      muSL1N hα0 hβ0 {x : (nrdHom (α : K) (β : K)).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} *
        (omegaInf F (BinfPos (F := F)) * muFinUnits F (ideleBox S (nsN α β mK hmK1))) := by
  set S₀ := nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U with hS₀def
  have hS₀o : IsOpen S₀ := isOpen_nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 hUo
  have hmeasS : MeasurableSet {g : (dN).G | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} :=
    hS₀o.measurableSet.inter (measurableSet_Bset'.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  have hzS : ∀ u : (Adeles F)ˣ, (dN).zHom u ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ↔ finPart u ∈ OHatUnits F := by
    intro u
    change quatScalar (α : K) (β : K) (adeleUnitsMap F K u) ∈ HS α β SK mK hmK1 ↔ _
    rw [quatScalar_mem_HS_iff SK mK hmK1 hα0, finPart_adeleUnitsMap_mem_iff hb₀ hb₁]
  -- along π
  have hc : ∀ g ∈ S₀, tamIdeles F {u | g * (dN).zHom u ∈ S₀ ∧
      (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ (Bset' : Set (Adeles F)ˣ)} =
      omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F) := by
    intro g hg
    obtain ⟨hgS, hgU⟩ := hg
    have hν : nrdUnit (g : MK × (Adeles F)ˣ).1 = adeleUnitsMap F K (g : MK × (Adeles F)ˣ).2 := (dN).ν_fst g
    have hnrd : finPart (g : MK × (Adeles F)ˣ).2 ∈ OHatUnits F := by
      rw [← finPart_adeleUnitsMap_mem_iff hb₀ hb₁, ← hν]
      exact finPart_nrd_mem_OHat' α β _ ((mem_HS α β SK mK hmK1).1 hgS).1
    have hz : ∀ u : (Adeles F)ˣ, g * (dN).zHom u ∈ S₀ ↔ finPart u ∈ OHatUnits F := by
      intro u
      constructor
      · rintro ⟨h1, -⟩
        exact (hzS u).1 (((nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hgS).1 h1)
      · intro h
        exact ⟨((nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hgS).2 ((hzS u).2 h), by
          rw [map_mul, nsInf_zHom hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0, mul_one]; exact hgU⟩
    have hset : {u | g * (dN).zHom u ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ (Bset' : Set (Adeles F)ˣ)} =
        idelesEquiv F ⁻¹' ({v : (mixedSpace F)ˣ | v ^ 2 * infPart (g : MK × (Adeles F)ˣ).2 ∈ Binf} ×ˢ
          (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ)) := by
      ext u
      simp only [mem_setOf_eq, Bset', mem_preimage, mem_prod, idelesEquiv_apply, SetLike.mem_coe, hz]
      rw [mul_comm (g : MK × (Adeles F)ˣ).2 (u ^ 2), infPart_mul, infPart_pow', finPart_mul, finPart_pow']
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, (OHatUnits F).mul_mem ((OHatUnits F).pow_mem h1 2) hnrd⟩
    rw [hset, tamIdeles_prod, omegaInf_sq_mul_Binf]
  have h1 := (dN).muG_eq_mul_muP_set (muBC bK 0 hb₀ hα0 hβ0) S₀ hS₀o measurableSet_Bset'
    (omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F)) hc
  -- along p
  set cE := muBC bK 0 hb₀ hα0 hβ0 {x : ((dN).ν : MK →* (Adeles K)ˣ).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} with hcE
  set X : Set (dN).Apos := {q | (q : (Adeles F)ˣ) ∈ nsXF' F α β SK mK hmK1} with hX
  have hXm : MeasurableSet X :=
    (measurableSet_nsXF' hb₀ hb₁ S SK mK hmK1 hSK).preimage measurable_subtype_coe
  have hk : ∀ g : (dN).G, NormalFib.fibK (dN).p ((dN).muS (muBC bK 0 hb₀ hα0 hβ0)) g
      {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} =
        X.indicator (fun _ => cE) ((dN).p g) := by
    intro g
    rw [NormalFib.fibK_apply _ _ _ hmeasS, GnatData.muS, Measure.map_apply (map_continuous (dN).kerSEquiv.symm).measurable
      (hmeasS.preimage (NormalFib.measurable_mul_val _ _))]
    by_cases hx : (g : MK × (Adeles F)ˣ).2 ∈ nsXF' F α β SK mK hmK1
    · have hxX : (dN).p g ∈ X := hx
      rw [Set.indicator_of_mem hxX]
      obtain ⟨g₀, hg₀2, hg₀S, hg₀I⟩ :=
        exists_base_point hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 hSKg hx
      have hk0 : g₀⁻¹ * g ∈ (dN).p.ker := by
        rw [(dN).mem_ker_p]
        change ((g₀ : MK × (Adeles F)ˣ).2)⁻¹ * (g : MK × (Adeles F)ˣ).2 = 1
        rw [hg₀2, inv_mul_cancel]
      obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ((dN).ν : MK →* (Adeles K)ˣ).ker, (dN).kerSEquiv.symm m₀ = ⟨g₀⁻¹ * g, hk0⟩ :=
        ⟨(dN).kerSEquiv ⟨g₀⁻¹ * g, hk0⟩, ContinuousMulEquiv.symm_apply_apply _ _⟩
      have e : ∀ x, g * (((dN).kerSEquiv.symm x : (dN).p.ker) : (dN).G) =
          g₀ * (((dN).kerSEquiv.symm (m₀ * x) : (dN).p.ker) : (dN).G) := by
        intro x
        rw [map_mul, hm₀, Subgroup.coe_mul]
        change g * _ = g₀ * (g₀⁻¹ * g * _)
        group
      have hmem : ∀ z : (dN).p.ker, ((g₀ * (z : (dN).G) ∈ S₀ ∧
          ((g₀ * (z : (dN).G) : (dN).G) : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)) ↔
          ((z : (dN).G) ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ∧ nsI (z : (dN).G) ∈ U)) := by
        intro z
        have hz1 : (((z : (dN).G)) : MK × (Adeles F)ˣ).2 = 1 := (dN).mem_ker_p.1 z.2
        have hB : ((g₀ * (z : (dN).G) : (dN).G) : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ) := by
          change (g₀ : MK × (Adeles F)ˣ).2 * ((z : (dN).G) : MK × (Adeles F)ˣ).2 ∈ _
          rw [hz1, mul_one, hg₀2]; exact hx.1
        have hm := (nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hg₀S (y := (z : (dN).G))
        have hI : nsI (g₀ * (z : (dN).G)) = nsI (z : (dN).G) := by rw [map_mul, hg₀I, one_mul]
        constructor
        · rintro ⟨⟨h1, h2⟩, -⟩
          exact ⟨hm.1 h1, by rwa [hI] at h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨hm.2 h1, by rw [hI]; exact h2⟩, hB⟩
      have hset : (dN).kerSEquiv.symm ⁻¹' ((fun k : (dN).p.ker => g * (k : (dN).G)) ⁻¹'
          {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)}) =
          (fun x => m₀ * x) ⁻¹' {x : ((dN).ν : MK →* (Adeles K)ˣ).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} := by
        ext x
        have := hmem ((dN).kerSEquiv.symm (m₀ * x))
        rw [← e x] at this
        exact this
      rw [hset, measure_preimage_mul]
    · have hxX : (dN).p g ∉ X := hx
      rw [Set.indicator_of_notMem hxX]
      convert measure_empty (μ := muBC bK 0 hb₀ hα0 hβ0)
      ext x
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, h3⟩
      set z : (dN).G := (((dN).kerSEquiv.symm x : (dN).p.ker) : (dN).G) with hz
      have hz1 : ((z : (dN).G) : MK × (Adeles F)ˣ).2 = 1 := (dN).mem_ker_p.1 ((dN).kerSEquiv.symm x).2
      have hzz : ((g * z : (dN).G) : MK × (Adeles F)ˣ).2 = (g : MK × (Adeles F)ˣ).2 := by
        change (g : MK × (Adeles F)ˣ).2 * ((z : (dN).G) : MK × (Adeles F)ˣ).2 = _
        rw [hz1, mul_one]
      have hν : nrdUnit ((g * z : (dN).G) : MK × (Adeles F)ˣ).1 =
          adeleUnitsMap F K ((g * z : (dN).G) : MK × (Adeles F)ˣ).2 := (dN).ν_fst _
      rw [hzz] at hν h3
      apply hx
      refine ⟨h3, fun v => ?_, ?_⟩
      · have := hpos (g * z) ⟨h1, h2⟩ v
        rw [hzz] at this; exact this
      · rw [← hν]
        exact finPart_nrd_mem_NH SK mK hmK1 h1
  have himg : Subtype.val '' X = nsXF' F α β SK mK hmK1 := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro ht
      obtain ⟨g, hg2, -, -⟩ := exists_base_point hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 hSKg ht
      exact ⟨(dN).p g, by
        show (((dN).p g : (dN).Apos) : (Adeles F)ˣ) ∈ nsXF' F α β SK mK hmK1
        rw [(dN).coe_p, hg2]; exact ht, hg2⟩
  have hp : (dN).muG (muBC bK 0 hb₀ hα0 hβ0) {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} =
      cE * (omegaInf F (BinfPos (F := F)) * muFinUnits F (ideleBox S (nsN α β mK hmK1))) := by
    rw [(dN).muG_apply_of_fibK (muBC bK 0 hb₀ hα0 hβ0) _ hmeasS (fun q => X.indicator (fun _ => cE) q) hk,
      lintegral_indicator_const hXm, GnatData.muA_apply, himg, tamIdeles_nsXF' hb₀ hb₁ S SK mK hmK1 hSK]
  exact (mul_comm _ _).trans (h1.symm.trans hp)

/-- **Along $\pi$, for a measurable set** (`muG_eq_mul_muP_set` with openness replaced by measurability of $S_0$ and
$\pi(S_0)$). -/
theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.GnatData.muG_eq_mul_muP_set' {k : Type} [Field k] [NumberField k]
    {M T : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
    (d : GnatData k M T) (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]
    (S₀ : Set d.G) (hS₀ : MeasurableSet S₀) (hπ : MeasurableSet (d.π '' S₀)) {B : Set (Adeles k)ˣ}
    (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ g ∈ S₀, tamIdeles k {u | g * d.zHom u ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 * u ^ 2 ∈ B} = c) :
    d.muG μSν {g | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} = c * d.muP μSν (d.π '' S₀) := by
  have hS : MeasurableSet {g : d.G | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} :=
    hS₀.inter (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  rw [← d.fibMeas_muP μSν]
  refine fibMeas_apply_of_kern _ _ d.measurable_π _ _ hS hπ c ?_ ?_
  · rintro q ⟨g, hg, rfl⟩
    refine ⟨g, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _)), ← hc g hg]
    rfl
  · intro g hg
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _))]
    convert measure_empty (μ := tamIdeles k)
    ext u
    simp only [mem_preimage, mem_empty_iff_false, iff_false, GnatData.coe_kerZEquiv, mem_ofPred_eq]
    rintro ⟨h1, -⟩
    apply hg
    refine ⟨_, h1, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 (d.mem_ker_π.2 ⟨u, rfl⟩), mul_one]

set_option maxHeartbeats 3200000 in
include hb₀ hb₁ hα hβ in
/-- **`muP_nsS0U_mul` for a measurable test set** ($U$ measurable and $\pi(S_0^U)$ measurable instead of $U$ open):
$\mu_P(\pi(S_0^U))\cdot\omega_\infty(V_1)\mu_f(\hat{\mathcal O}_F^\times) =
\mu_{\mathrm{SL}_1(D')}(\{x\in H_S : \mathrm{nsInf}(x,1)\in U\})\cdot\omega_\infty(\mathrm{BinfPos})\,\mu_f(\mathrm{box}(S,N))$**
for every number field $F$ (no total reality), provided the test set is positive at the real places. -/
theorem muP_nsS0U_mul_of_meas (U : Set (GInfSO (qNS a b d))) (hUm : MeasurableSet U)
    (hπm : MeasurableSet ((dN).π '' nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U))
    (hpos : ∀ g : (dN).G, g ∈ nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U →
      ∀ v : {v : InfinitePlace F // v.IsReal}, 0 < ((g : MK × (Adeles F)ˣ).2 : Adeles F).1.1 v)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U) *
        (omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F)) =
      muSL1N hα0 hβ0 {x : (nrdHom (α : K) (β : K)).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} *
        (omegaInf F (BinfPos (F := F)) * muFinUnits F (ideleBox S (nsN α β mK hmK1))) := by
  set S₀ := nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U with hS₀def
  have hS₀m : MeasurableSet S₀ :=
    (isOpen_nsS0 hb₀ hα0 hβ0 ((isOpen_quatCongS SK mK hmK1).preimage (continuous_quatFinPart α β))).measurableSet.inter
      (hUm.preimage (continuous_nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0).measurable)
  have hmeasS : MeasurableSet {g : (dN).G | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} :=
    hS₀m.inter (measurableSet_Bset'.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  have hzS : ∀ u : (Adeles F)ˣ, (dN).zHom u ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ↔ finPart u ∈ OHatUnits F := by
    intro u
    change quatScalar (α : K) (β : K) (adeleUnitsMap F K u) ∈ HS α β SK mK hmK1 ↔ _
    rw [quatScalar_mem_HS_iff SK mK hmK1 hα0, finPart_adeleUnitsMap_mem_iff hb₀ hb₁]
  -- along π
  have hc : ∀ g ∈ S₀, tamIdeles F {u | g * (dN).zHom u ∈ S₀ ∧
      (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ (Bset' : Set (Adeles F)ˣ)} =
      omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F) := by
    intro g hg
    obtain ⟨hgS, hgU⟩ := hg
    have hν : nrdUnit (g : MK × (Adeles F)ˣ).1 = adeleUnitsMap F K (g : MK × (Adeles F)ˣ).2 := (dN).ν_fst g
    have hnrd : finPart (g : MK × (Adeles F)ˣ).2 ∈ OHatUnits F := by
      rw [← finPart_adeleUnitsMap_mem_iff hb₀ hb₁, ← hν]
      exact finPart_nrd_mem_OHat' α β _ ((mem_HS α β SK mK hmK1).1 hgS).1
    have hz : ∀ u : (Adeles F)ˣ, g * (dN).zHom u ∈ S₀ ↔ finPart u ∈ OHatUnits F := by
      intro u
      constructor
      · rintro ⟨h1, -⟩
        exact (hzS u).1 (((nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hgS).1 h1)
      · intro h
        exact ⟨((nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hgS).2 ((hzS u).2 h), by
          rw [map_mul, nsInf_zHom hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0, mul_one]; exact hgU⟩
    have hset : {u | g * (dN).zHom u ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ (Bset' : Set (Adeles F)ˣ)} =
        idelesEquiv F ⁻¹' ({v : (mixedSpace F)ˣ | v ^ 2 * infPart (g : MK × (Adeles F)ˣ).2 ∈ Binf} ×ˢ
          (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ)) := by
      ext u
      simp only [mem_setOf_eq, Bset', mem_preimage, mem_prod, idelesEquiv_apply, SetLike.mem_coe, hz]
      rw [mul_comm (g : MK × (Adeles F)ˣ).2 (u ^ 2), infPart_mul, infPart_pow', finPart_mul, finPart_pow']
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, (OHatUnits F).mul_mem ((OHatUnits F).pow_mem h1 2) hnrd⟩
    rw [hset, tamIdeles_prod, omegaInf_sq_mul_Binf]
  have h1 := (dN).muG_eq_mul_muP_set' (muBC bK 0 hb₀ hα0 hβ0) S₀ hS₀m hπm measurableSet_Bset'
    (omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F)) hc
  -- along p
  set cE := muBC bK 0 hb₀ hα0 hβ0 {x : ((dN).ν : MK →* (Adeles K)ˣ).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} with hcE
  set X : Set (dN).Apos := {q | (q : (Adeles F)ˣ) ∈ nsXF' F α β SK mK hmK1} with hX
  have hXm : MeasurableSet X :=
    (measurableSet_nsXF' hb₀ hb₁ S SK mK hmK1 hSK).preimage measurable_subtype_coe
  have hk : ∀ g : (dN).G, NormalFib.fibK (dN).p ((dN).muS (muBC bK 0 hb₀ hα0 hβ0)) g
      {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} =
        X.indicator (fun _ => cE) ((dN).p g) := by
    intro g
    rw [NormalFib.fibK_apply _ _ _ hmeasS, GnatData.muS, Measure.map_apply (map_continuous (dN).kerSEquiv.symm).measurable
      (hmeasS.preimage (NormalFib.measurable_mul_val _ _))]
    by_cases hx : (g : MK × (Adeles F)ˣ).2 ∈ nsXF' F α β SK mK hmK1
    · have hxX : (dN).p g ∈ X := hx
      rw [Set.indicator_of_mem hxX]
      obtain ⟨g₀, hg₀2, hg₀S, hg₀I⟩ :=
        exists_base_point hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 hSKg hx
      have hk0 : g₀⁻¹ * g ∈ (dN).p.ker := by
        rw [(dN).mem_ker_p]
        change ((g₀ : MK × (Adeles F)ˣ).2)⁻¹ * (g : MK × (Adeles F)ˣ).2 = 1
        rw [hg₀2, inv_mul_cancel]
      obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ((dN).ν : MK →* (Adeles K)ˣ).ker, (dN).kerSEquiv.symm m₀ = ⟨g₀⁻¹ * g, hk0⟩ :=
        ⟨(dN).kerSEquiv ⟨g₀⁻¹ * g, hk0⟩, ContinuousMulEquiv.symm_apply_apply _ _⟩
      have e : ∀ x, g * (((dN).kerSEquiv.symm x : (dN).p.ker) : (dN).G) =
          g₀ * (((dN).kerSEquiv.symm (m₀ * x) : (dN).p.ker) : (dN).G) := by
        intro x
        rw [map_mul, hm₀, Subgroup.coe_mul]
        change g * _ = g₀ * (g₀⁻¹ * g * _)
        group
      have hmem : ∀ z : (dN).p.ker, ((g₀ * (z : (dN).G) ∈ S₀ ∧
          ((g₀ * (z : (dN).G) : (dN).G) : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)) ↔
          ((z : (dN).G) ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1) ∧ nsI (z : (dN).G) ∈ U)) := by
        intro z
        have hz1 : (((z : (dN).G)) : MK × (Adeles F)ˣ).2 = 1 := (dN).mem_ker_p.1 z.2
        have hB : ((g₀ * (z : (dN).G) : (dN).G) : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ) := by
          change (g₀ : MK × (Adeles F)ˣ).2 * ((z : (dN).G) : MK × (Adeles F)ˣ).2 ∈ _
          rw [hz1, mul_one, hg₀2]; exact hx.1
        have hm := (nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).mul_mem_cancel_left hg₀S (y := (z : (dN).G))
        have hI : nsI (g₀ * (z : (dN).G)) = nsI (z : (dN).G) := by rw [map_mul, hg₀I, one_mul]
        constructor
        · rintro ⟨⟨h1, h2⟩, -⟩
          exact ⟨hm.1 h1, by rwa [hI] at h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨hm.2 h1, by rw [hI]; exact h2⟩, hB⟩
      have hset : (dN).kerSEquiv.symm ⁻¹' ((fun k : (dN).p.ker => g * (k : (dN).G)) ⁻¹'
          {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)}) =
          (fun x => m₀ * x) ⁻¹' {x : ((dN).ν : MK →* (Adeles K)ˣ).ker | (x : MK) ∈ HS α β SK mK hmK1 ∧
          nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ U} := by
        ext x
        have := hmem ((dN).kerSEquiv.symm (m₀ * x))
        rw [← e x] at this
        exact this
      rw [hset, measure_preimage_mul]
    · have hxX : (dN).p g ∉ X := hx
      rw [Set.indicator_of_notMem hxX]
      convert measure_empty (μ := muBC bK 0 hb₀ hα0 hβ0)
      ext x
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, h3⟩
      set z : (dN).G := (((dN).kerSEquiv.symm x : (dN).p.ker) : (dN).G) with hz
      have hz1 : ((z : (dN).G) : MK × (Adeles F)ˣ).2 = 1 := (dN).mem_ker_p.1 ((dN).kerSEquiv.symm x).2
      have hzz : ((g * z : (dN).G) : MK × (Adeles F)ˣ).2 = (g : MK × (Adeles F)ˣ).2 := by
        change (g : MK × (Adeles F)ˣ).2 * ((z : (dN).G) : MK × (Adeles F)ˣ).2 = _
        rw [hz1, mul_one]
      have hν : nrdUnit ((g * z : (dN).G) : MK × (Adeles F)ˣ).1 =
          adeleUnitsMap F K ((g * z : (dN).G) : MK × (Adeles F)ˣ).2 := (dN).ν_fst _
      rw [hzz] at hν h3
      apply hx
      refine ⟨h3, fun v => ?_, ?_⟩
      · have := hpos (g * z) ⟨h1, h2⟩ v
        rw [hzz] at this; exact this
      · rw [← hν]
        exact finPart_nrd_mem_NH SK mK hmK1 h1
  have himg : Subtype.val '' X = nsXF' F α β SK mK hmK1 := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro ht
      obtain ⟨g, hg2, -, -⟩ := exists_base_point hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 hSKg ht
      exact ⟨(dN).p g, by
        show (((dN).p g : (dN).Apos) : (Adeles F)ˣ) ∈ nsXF' F α β SK mK hmK1
        rw [(dN).coe_p, hg2]; exact ht, hg2⟩
  have hp : (dN).muG (muBC bK 0 hb₀ hα0 hβ0) {g | g ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 ∈ (Bset' : Set (Adeles F)ˣ)} =
      cE * (omegaInf F (BinfPos (F := F)) * muFinUnits F (ideleBox S (nsN α β mK hmK1))) := by
    rw [(dN).muG_apply_of_fibK (muBC bK 0 hb₀ hα0 hβ0) _ hmeasS (fun q => X.indicator (fun _ => cE) q) hk,
      lintegral_indicator_const hXm, GnatData.muA_apply, himg, tamIdeles_nsXF' hb₀ hb₁ S SK mK hmK1 hSK]
  exact (mul_comm _ _).trans (h1.symm.trans hp)

end NSAny2

end

end QuadFormsKB.Tamagawa.Measure.Weil
