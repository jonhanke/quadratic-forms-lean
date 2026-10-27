/-
# Non-square discriminant: the maps $G^\natural(\mathbb A_F)\to SO(V)(\mathbb A_f)$ and $\to G_\infty$

**Layer:** as `GnatNSAdelic`; $G^\natural$ = the `gnatBC bK 0 hb₀ hA0 hB0` (with $A' = a$, $B' = b$ in $K$), $Q_0 = q_{\mathrm{ns}}(a,b,d)$
= `qNS a b d`.

**Defines/proves**
* `nsUnit`: $g\mapsto\Theta^{-1}(g_1)\in(D_E\otimes\mathbb A_F)^\times$ and **`nsUnit_nrd`** ($\operatorname{nrd}_E = u$);
* `nsPairV`, `nsPairR`, `nsPairC`: the local components in $G^\natural(F_v)$, $G^\natural(\mathbb R)$, $G^\natural(\mathbb C)$;
* **`nsFin`** (lands in the restricted product: $\Lambda_E^\times$ at almost all $v$, `nsSOK_mem_stdStab`), **`continuous_nsFin`**;
* **`nsInf`**, **`continuous_nsInf`**.

Source: Weil 1982, §3.7, pp. 64–65 [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSAdelic

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology
  Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F} (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F)) (hA0 : A' ≠ 0) (hB0 : B' ≠ 0)

local notation "dN" => gnatBC bK 0 hb₀ hA0 hB0
local notation "Q₀" => qNS a b d
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)
local notation "MQ" => (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ

/-! ### The transported unit and its norm -/

/-- $g = (m,u)\mapsto\Theta^{-1}(m)$. -/
def nsUnit : (gnatBC bK 0 hb₀ hA0 hB0).G →* MQ :=
  (bcHom hb₀ hb₁ hA' hB').comp ((MonoidHom.fst _ _).comp (gnatBC bK 0 hb₀ hA0 hB0).gnat.subtype)

theorem nsUnit_apply (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g = bcHom hb₀ hb₁ hA' hB' (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1 := rfl

theorem continuous_nsUnit : Continuous (nsUnit hb₀ hb₁ hA' hB' hA0 hB0) :=
  (continuous_bcHom hb₀ hb₁ hA' hB').comp (continuous_fst.comp continuous_subtype_val)

/-- **$\operatorname{nrd}_E(\Theta^{-1}g_1) = g_2$.** -/
theorem nsUnit_nrd (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) *
      star ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))).re =
      (⟨((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F), 0⟩ : QuadAdele F (d : F)) :=
  bcHom_nrd hb₀ hb₁ hA' hB' _ _ ((gnatBC bK 0 hb₀ hA0 hB0).ν_fst g)

/-! ### Local components -/

/-- The local component at a finite place, in the $G^\natural(F_v)$. -/
def nsPairV (v : HeightOneSpectrum (𝓞 F)) : (gnatBC bK 0 hb₀ hA0 hB0).G →* GnK (v.adicCompletion F) a b d :=
  ((Units.map (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))).toMonoidHom).comp
    (nsUnit hb₀ hb₁ hA' hB' hA0 hB0)).codRestrict _ fun g =>
      deMap_mem_Gnat _ _ _ _ (nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g)

theorem nsPairV_val (v : HeightOneSpectrum (𝓞 F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    (((nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d) :
      DEr (v.adicCompletion F) a b d) =
      deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
        ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) := rfl

theorem nsPairV_inv_val (v : HeightOneSpectrum (𝓞 F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ((((nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d)⁻¹ :
      DEK (v.adicCompletion F) a b d) : DEr (v.adicCompletion F) a b d) =
      deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
        (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) := rfl

/-- $D_E$ over $\mathbb R$ at a real place. -/
abbrev DEre (a b d : 𝓞 F) (w : {w : InfinitePlace F // w.IsReal}) : Type :=
  DE (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) (embedding_of_isReal w.2 (d : F))

/-- $D_E$ over $\mathbb C$ at a complex place. -/
abbrev DEcx (a b d : 𝓞 F) (w : {w : InfinitePlace F // w.IsComplex}) : Type :=
  DE (w.1.embedding (a : F)) (w.1.embedding (b : F)) (w.1.embedding (d : F))

/-- The local component at a real place. -/
def nsPairR (w : {w : InfinitePlace F // w.IsReal}) : (gnatBC bK 0 hb₀ hA0 hB0).G →*
    Gnat (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) (embedding_of_isReal w.2 (d : F)) :=
  ((Units.map (deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))).toMonoidHom).comp
    (nsUnit hb₀ hb₁ hA' hB' hA0 hB0)).codRestrict _ fun g =>
      deMap_mem_Gnat _ _ _ _ (nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g)

/-- The local component at a complex place. -/
def nsPairC (w : {w : InfinitePlace F // w.IsComplex}) : (gnatBC bK 0 hb₀ hA0 hB0).G →*
    Gnat (w.1.embedding (a : F)) (w.1.embedding (b : F)) (w.1.embedding (d : F)) :=
  ((Units.map (deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))).toMonoidHom).comp
    (nsUnit hb₀ hb₁ hA' hB' hA0 hB0)).codRestrict _ fun g =>
      deMap_mem_Gnat _ _ _ _ (nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g)

theorem nsPairR_val (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    (((nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEre a b d w)ˣ) : DEre a b d w) =
      deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
        ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) := rfl

theorem nsPairC_val (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    (((nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEcx a b d w)ˣ) : DEcx a b d w) =
      deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
        ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) := rfl

/-! ### Integrality at almost all places -/

/-- A unit of $D_E\otimes\mathbb A_F$ lies in $\Lambda_E^\times$ at almost all places. -/
theorem eventually_deMap_mem_lamEUnits (x : MQ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Units.map (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))).toMonoidHom x ∈
        lamEUnits v a b d := by
  set y : QuatQuadAdele F (d : F) (a : F) (b : F) := (x : QuatQuadAdele F (d : F) (a : F) (b : F))
  set z : QuatQuadAdele F (d : F) (a : F) (b : F) := ((x⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))
  filter_upwards [y.re.re.2.2, y.re.im.2.2, y.imI.re.2.2, y.imI.im.2.2, y.imJ.re.2.2, y.imJ.im.2.2,
    y.imK.re.2.2, y.imK.im.2.2, z.re.re.2.2, z.re.im.2.2, z.imI.re.2.2, z.imI.im.2.2, z.imJ.re.2.2,
    z.imJ.im.2.2, z.imK.re.2.2, z.imK.im.2.2] with v h1 h2 h3 h4 h5 h6 h7 h8 k1 k2 k3 k4 k5 k6 k7 k8
  exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩, ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩, ⟨k7, k8⟩⟩⟩

/-! ### The finite adelic map -/

variable (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

/-- The local components of `nsFin`. -/
def nsFinFun (g : (gnatBC bK 0 hb₀ hA0 hB0).G) : OAf QF :=
  ⟨fun v => (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
    orthGroup QF (v.adicCompletion F)), by
    filter_upwards [eventually_deMap_mem_lamEUnits (nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)] with v hv
    exact nsSOK_mem_stdStab v ha0 hd0 (valued_algebraMap_int_le_one v a) (valued_algebraMap_int_le_one v b)
      (valued_algebraMap_int_le_one v d) _ hv⟩

@[simp] theorem nsFinFun_apply (g : (gnatBC bK 0 hb₀ hA0 hB0).G) (v : HeightOneSpectrum (𝓞 F)) :
    nsFinFun hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g v =
      (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
        orthGroup QF (v.adicCompletion F)) := rfl

/-- **$G^\natural(\mathbb A_F)\to SO(V)(\mathbb A_f)$** for the non-square model, $g\mapsto(\varphi_{g_v})_v$. -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
def nsFin : (gnatBC bK 0 hb₀ hA0 hB0).G →* SOAf Q₀ where
  toFun g := ⟨nsFinFun hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g, fun v =>
    (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g)).2⟩
  map_one' := by
    ext v : 2
    simp only [nsFinFun_apply, map_one]
    simp
  map_mul' g h := by
    ext v : 2
    simp only [nsFinFun_apply, map_mul]
    simp

@[simp] theorem nsFin_apply (g : (gnatBC bK 0 hb₀ hA0 hB0).G) (v : HeightOneSpectrum (𝓞 F)) :
    ((nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g : SOAf Q₀) : OAf QF) v =
      (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
        orthGroup QF (v.adicCompletion F)) := rfl

/-- The coordinate hypotheses of `continuous_nsMat_comp` for `deMap f ∘ (unit-valued continuous map)`. -/
theorem deMap_coord_continuous {X : Type*} [TopologicalSpace X] {L : Type*} [Field L] [TopologicalSpace L]
    (f : Adeles F →+* L) (hf : Continuous f) {td ta tb : L} (hd : f (diagRing F (d : F)) = td)
    (ha : f (diagRing F (a : F)) = ta) (hb : f (diagRing F (b : F)) = tb)
    (φ : X → QuatQuadAdele F (d : F) (a : F) (b : F)) (hφ : Continuous φ) :
    ∀ c : DE ta tb td → QE td, (c = fun z => z.re) ∨ (c = fun z => z.imI) ∨ (c = fun z => z.imJ) ∨
      (c = fun z => z.imK) → Continuous (fun t => (c (deMap f hd ha hb (φ t))).re) ∧
        Continuous (fun t => (c (deMap f hd ha hb (φ t))).im) := by
  have hq := (continuous_quatQuad_iff (d : F) (a : F) (b : F)).1 hφ
  rintro c (rfl | rfl | rfl | rfl)
  · exact ⟨hf.comp ((continuous_quad_re _).comp hq.1), hf.comp ((continuous_quad_im _).comp hq.1)⟩
  · exact ⟨hf.comp ((continuous_quad_re _).comp hq.2.1), hf.comp ((continuous_quad_im _).comp hq.2.1)⟩
  · exact ⟨hf.comp ((continuous_quad_re _).comp hq.2.2.1), hf.comp ((continuous_quad_im _).comp hq.2.2.1)⟩
  · exact ⟨hf.comp ((continuous_quad_re _).comp hq.2.2.2), hf.comp ((continuous_quad_im _).comp hq.2.2.2)⟩

/-- Continuity of one finite component. -/
theorem continuous_nsSOK_pairV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun g : (gnatBC bK 0 hb₀ hA0 hB0).G =>
      (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
        orthGroup QF (v.adicCompletion F)) := by
  have hu := continuous_nsUnit hb₀ hb₁ hA' hB' hA0 hB0
  have h1 : Continuous fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) :=
    Units.continuous_val.comp hu
  have h2 : Continuous fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) := Units.continuous_coe_inv.comp hu
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G,
        (((nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
          orthGroup QF (v.adicCompletion F)) : GL (Fin 4) (v.adicCompletion F)) :
            Matrix (Fin 4) (Fin 4) (v.adicCompletion F)) =
        nsMat (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
      rw [nsSOK_coe, nsGL_apply, phiSO_val]; rfl
    refine (continuous_congr e).2 ?_
    exact continuous_nsMat_comp _ _
      (deMap_coord_continuous (fAt v) (continuous_fAt v) _ _ _ _ h1)
      (deMap_coord_continuous (fAt v) (continuous_fAt v) _ _ _ _ h2)
  · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G,
        ((((nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
          orthGroup QF (v.adicCompletion F)) : GL (Fin 4) (v.adicCompletion F))⁻¹ : GL (Fin 4) (v.adicCompletion F)) :
            Matrix (Fin 4) (Fin 4) (v.adicCompletion F)) =
        nsMat (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAt v) (fAt_diag v (d : F)) (fAt_diag v (a : F)) (fAt_diag v (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
      rw [nsSOK_coe, nsGL_apply, ← Subgroup.coe_inv, phiSO_inv_val]; rfl
    refine (continuous_congr e).2 ?_
    exact continuous_nsMat_comp _ _
      (deMap_coord_continuous (fAt v) (continuous_fAt v) _ _ _ _ h2)
      (deMap_coord_continuous (fAt v) (continuous_fAt v) _ _ _ _ h1)

theorem isOpen_adeles_integral : IsOpen {y : Adeles F | ∀ v : HeightOneSpectrum (𝓞 F), y.2 v ∈ v.adicCompletionIntegers F} :=
  (RestrictedProduct.isOpen_forall_mem (fun v => isOpen_adicCompletionIntegers v)).preimage continuous_snd

/-- **`nsFin` is continuous** (as `continuous_sqFin`: on the open set where all finite components lie in $\Lambda_E^\times$ it
factors through $\prod_vO(\mathfrak o_v^4)$). -/
theorem continuous_nsFin : Continuous (nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) := by
  refine continuous_of_continuousAt_one _ ?_
  have hu := continuous_nsUnit hb₀ hb₁ hA' hB' hA0 hB0
  have h1 : Continuous fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) :=
    Units.continuous_val.comp hu
  have h2 : Continuous fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) := Units.continuous_coe_inv.comp hu
  have hq1 := (continuous_quatQuad_iff (d : F) (a : F) (b : F)).1 h1
  have hq2 := (continuous_quatQuad_iff (d : F) (a : F) (b : F)).1 h2
  have hO := isOpen_adeles_integral (F := F)
  have hre := continuous_quad_re (d : F)
  have him := continuous_quad_im (d : F)
  set U : Set (gnatBC bK 0 hb₀ hA0 hB0).G := (fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).re.re) ⁻¹'
      {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩ ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) :
        QuatQuadAdele F (d : F) (a : F) (b : F)).re.im) ⁻¹' {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imI.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imI.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imJ.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imJ.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imK.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imK.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).re.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).re.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imI.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imI.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imJ.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imJ.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imK.re) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F} ∩
      ((fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)).imK.im) ⁻¹'
        {y | ∀ v, y.2 v ∈ v.adicCompletionIntegers F}))))))))))))))) with hUdef
  have hUo : IsOpen U :=
    (hO.preimage (hre.comp hq1.1)).inter ((hO.preimage (him.comp hq1.1)).inter ((hO.preimage (hre.comp hq1.2.1)).inter ((hO.preimage (him.comp hq1.2.1)).inter ((hO.preimage (hre.comp hq1.2.2.1)).inter ((hO.preimage (him.comp hq1.2.2.1)).inter ((hO.preimage (hre.comp hq1.2.2.2)).inter ((hO.preimage (him.comp hq1.2.2.2)).inter ((hO.preimage (hre.comp hq2.1)).inter ((hO.preimage (him.comp hq2.1)).inter ((hO.preimage (hre.comp hq2.2.1)).inter ((hO.preimage (him.comp hq2.2.1)).inter ((hO.preimage (hre.comp hq2.2.2.1)).inter ((hO.preimage (him.comp hq2.2.2.1)).inter ((hO.preimage (hre.comp hq2.2.2.2)).inter ((hO.preimage (him.comp hq2.2.2.2)))))))))))))))))
  have hint1 : ∀ x : QuatQuadAdele F (d : F) (a : F) (b : F), x = 1 →
      (∀ v, x.re.re.2 v ∈ v.adicCompletionIntegers F) ∧ (∀ v, x.re.im.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v, x.imI.re.2 v ∈ v.adicCompletionIntegers F) ∧ (∀ v, x.imI.im.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v, x.imJ.re.2 v ∈ v.adicCompletionIntegers F) ∧ (∀ v, x.imJ.im.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v, x.imK.re.2 v ∈ v.adicCompletionIntegers F) ∧ (∀ v, x.imK.im.2 v ∈ v.adicCompletionIntegers F) := by
    rintro x rfl
    refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_,
      fun v => ?_⟩ <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;>
      first | exact one_mem _ | exact zero_mem _
  have h1U : (1 : (gnatBC bK 0 hb₀ hA0 hB0).G) ∈ U := by
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hint1 ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 1 : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) (by rw [map_one, Units.val_one])
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hint1 (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 1)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) (by rw [map_one, inv_one, Units.val_one])
    exact ⟨k1, k2, k3, k4, k5, k6, k7, k8, l1, l2, l3, l4, l5, l6, l7, l8⟩
  have hU : U ∈ 𝓝 (1 : (gnatBC bK 0 hb₀ hA0 hB0).G) := hUo.mem_nhds h1U
  have hmem : ∀ g ∈ U, ∀ v, (nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
      orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v := fun g hg v => by
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hg
    exact nsSOK_mem_stdStab v ha0 hd0 (valued_algebraMap_int_le_one v a) (valued_algebraMap_int_le_one v b)
      (valued_algebraMap_int_le_one v d) _ ⟨⟨⟨k1 v, k2 v⟩, ⟨k3 v, k4 v⟩, ⟨k5 v, k6 v⟩, ⟨k7 v, k8 v⟩⟩,
        ⟨⟨l1 v, l2 v⟩, ⟨l3 v, l4 v⟩, ⟨l5 v, l6 v⟩, ⟨l7 v, l8 v⟩⟩⟩
  let φ : U → ∀ v, (stdStab QF v : Set (orthGroup QF (v.adicCompletion F))) :=
    fun g v => ⟨_, hmem g.1 g.2 v⟩
  have hφ : Continuous φ := continuous_pi fun v =>
    ((continuous_nsSOK_pairV hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v).comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous fun g : U => ((nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g.1 : SOAf Q₀) : OAf QF) := by
    have := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup QF (v.adicCompletion F))
      (A := fun v => (stdStab QF v : Set (orthGroup QF (v.adicCompletion F)))) (𝓕 := cofinite)).continuous.comp hφ
    refine this.congr fun g => ?_
    ext v : 1
    rfl
  have hon : ContinuousOn (fun g => ((nsFin hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g : SOAf Q₀) : OAf QF)) U :=
    continuousOn_iff_continuous_domRestrict.2 hcomp
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff).2 (hon.continuousAt hU)

/-! ### The archimedean map -/

theorem phiSO_mem_soReal_qNS (w : {w : InfinitePlace F // w.IsReal})
    (α : Gnat (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) (embedding_of_isReal w.2 (d : F))) :
    (phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) α :
      GL (Fin 4) ℝ) ∈ soReal (QRe Q₀ w) := by
  have h := phiSO_hessian_qNS (embedding_of_isReal w.2) a b d ha0 hd0 α
  rw [mem_soReal_iff, QRe, hessian_map_NF]
  exact ⟨by convert h.1 using 3, by convert h.2 using 2⟩

theorem phiSO_mem_soC_qNS (w : {w : InfinitePlace F // w.IsComplex})
    (α : Gnat (w.1.embedding (a : F)) (w.1.embedding (b : F)) (w.1.embedding (d : F))) :
    (phiSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) α :
      GL (Fin 4) ℂ) ∈ soC (QCx Q₀ w) := by
  obtain ⟨h1, h2⟩ := phiSO_hessian_qNS w.1.embedding a b d ha0 hd0 α
  rw [mem_soC_iff, gramC, QCx, hessian_map_NF]
  refine ⟨?_, by convert h2 using 2⟩
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1

/-- The real component as a matrix. -/
def nsGLR (w : {w : InfinitePlace F // w.IsReal}) : (gnatBC bK 0 hb₀ hA0 hB0).G →* GL (Fin 4) ℝ :=
  (SO (V0Form (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F))
    (embedding_of_isReal w.2 (d : F)))).subtype.comp
    ((phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0)).comp
      (nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w))

/-- The complex component as a matrix. -/
def nsGLC (w : {w : InfinitePlace F // w.IsComplex}) : (gnatBC bK 0 hb₀ hA0 hB0).G →* GL (Fin 4) ℂ :=
  (SO (V0Form (w.1.embedding (a : F)) (w.1.embedding (b : F)) (w.1.embedding (d : F)))).subtype.comp
    ((phiSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0)).comp
      (nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w))

theorem nsGLR_apply (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nsGLR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g = phiSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2))
      ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) (nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g) := by
  simp only [nsGLR, MonoidHom.comp_apply, Subgroup.coe_subtype]

theorem nsGLC_apply (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nsGLC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g = phiSO (two_ne_zero_of_ringHom w.1.embedding)
      ((map_ne_zero _).2 ha0) ((map_ne_zero _).2 hd0) (nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g) := by
  simp only [nsGLC, MonoidHom.comp_apply, Subgroup.coe_subtype]

/-- The real component $G^\natural(\mathbb A_F)\to SO(Q^{\sigma_w})(\mathbb R)$. -/
def nsR (w : {w : InfinitePlace F // w.IsReal}) : (gnatBC bK 0 hb₀ hA0 hB0).G →* ArchSO (QRe Q₀ w) :=
  ((nsGLR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w).codRestrict (soReal (QRe Q₀ w)) fun g => by
    rw [nsGLR_apply]; exact phiSO_mem_soReal_qNS ha0 hd0 w _ :)

/-- The complex component $G^\natural(\mathbb A_F)\to SO(Q^{\tau_w})(\mathbb C)$. -/
def nsC (w : {w : InfinitePlace F // w.IsComplex}) : (gnatBC bK 0 hb₀ hA0 hB0).G →* ArchSOC (QCx Q₀ w) :=
  ((nsGLC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w).codRestrict (soC (QCx Q₀ w)) fun g => by
    rw [nsGLC_apply]; exact phiSO_mem_soC_qNS ha0 hd0 w _ :)

theorem nsR_incl (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSO.incl _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) = nsGLR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g := rfl

theorem nsC_incl (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOC.incl _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) = nsGLC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g := rfl

/-- **$G^\natural(\mathbb A_F)\to G_\infty$** for the non-square model. -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]"]
def nsInf : (gnatBC bK 0 hb₀ hA0 hB0).G →* GInfSO Q₀ :=
  (MonoidHom.pi fun w => nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w).prod
    (MonoidHom.pi fun w => nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w)

set_option maxHeartbeats 1000000 in
theorem continuous_nsInf : Continuous (nsInf hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) := by
  have hu := continuous_nsUnit hb₀ hb₁ hA' hB' hA0 hB0
  have h1 : Continuous fun g => ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) :=
    Units.continuous_val.comp hu
  have h2 : Continuous fun g => (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F)) := Units.continuous_coe_inv.comp hu
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G, ((ArchSO.incl _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) :
          GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) =
          nsMat (deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
        rw [nsR_incl, nsGLR_apply, phiSO_val]; rfl
      refine (continuous_congr e).2 ?_
      exact continuous_nsMat_comp _ _
        (deMap_coord_continuous (fAtR w) (continuous_fAtR w) _ _ _ _ h1)
        (deMap_coord_continuous (fAtR w) (continuous_fAtR w) _ _ _ _ h2)
    · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G, (((ArchSO.incl _ (nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) :
          GL (Fin 4) ℝ)⁻¹ : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) =
          nsMat (deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAtR w) (fAtR_diag w (d : F)) (fAtR_diag w (a : F)) (fAtR_diag w (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
        rw [nsR_incl, nsGLR_apply, ← Subgroup.coe_inv, phiSO_inv_val]; rfl
      refine (continuous_congr e).2 ?_
      exact continuous_nsMat_comp _ _
        (deMap_coord_continuous (fAtR w) (continuous_fAtR w) _ _ _ _ h2)
        (deMap_coord_continuous (fAtR w) (continuous_fAtR w) _ _ _ _ h1)
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G, ((ArchSOC.incl _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) :
          GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) =
          nsMat (deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
        rw [nsC_incl, nsGLC_apply, phiSO_val]; rfl
      refine (continuous_congr e).2 ?_
      exact continuous_nsMat_comp _ _
        (deMap_coord_continuous (fAtC w) (continuous_fAtC w) _ _ _ _ h1)
        (deMap_coord_continuous (fAtC w) (continuous_fAtC w) _ _ _ _ h2)
    · have e : ∀ g : (gnatBC bK 0 hb₀ hA0 hB0).G, (((ArchSOC.incl _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g) :
          GL (Fin 4) ℂ)⁻¹ : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) =
          nsMat (deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
            (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)))
          (deMap (fAtC w) (fAtC_diag w (d : F)) (fAtC_diag w (a : F)) (fAtC_diag w (b : F))
            ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))) := fun g => by
        rw [nsC_incl, nsGLC_apply, ← Subgroup.coe_inv, phiSO_inv_val]; rfl
      refine (continuous_congr e).2 ?_
      exact continuous_nsMat_comp _ _
        (deMap_coord_continuous (fAtC w) (continuous_fAtC w) _ _ _ _ h2)
        (deMap_coord_continuous (fAtC w) (continuous_fAtC w) _ _ _ _ h1)

end QuadFormsKB.Tamagawa.Measure.Weil
