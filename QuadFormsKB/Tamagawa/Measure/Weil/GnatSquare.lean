import QuadFormsKB.Tamagawa.Measure.Weil.GnatQuat
import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Final

/-!
# Square discriminant:
$G^\natural = \{(\alpha,\beta)\in D^\times\times D^\times : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$


**Layer:** $F$ any number field, $D = \mathbb H[F,a,b]$ any quaternion algebra, division or split ($a, b\in\mathcal O_F\setminus0$, the library's
standard order). For $V$ quaternary with square discriminant, $V\cong c\,(D,\operatorname{nrd})$, $E = F\times F$, $D_E = D\times D$ and
(`pairEquiv`, `mem_Gnat_iff_nrd_eq`, `evQ_phiLin`)
$G^\natural = \{(\alpha,\beta) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$ acting on
$V = D$ by $x\mapsto\alpha x\beta^{-1}$, with $SO(V)\cong G^\natural/\mathbb G_m$. Here adelically:

* **`gnatSq a b`**: the `GnatData` with $M = (D\otimes\mathbb A)^\times\times(D\otimes\mathbb A)^\times$, $\nu = \operatorname{nrd}\times\operatorname{nrd}$,
  $\iota(u) = (u,u)$, $s(u) = (u,u)$ (scalars), $A_+$ = `posA a b`, $\Gamma_M = D^\times\times D^\times$;
* `covolume_muSL1N`: $\tau(\mathrm{SL}_1(D)) = 1$ on $\ker\operatorname{nrd}$, and `map_adK_muSL1N`: `muSL1N` is invariant under
  conjugation by every unit of $D\otimes\mathbb A$ (every quaternion algebra);
* `muSq`: the Tamagawa measure $\mu_{\mathrm{SL}_1}\times\mu_{\mathrm{SL}_1}$ on $\ker\nu = \mathrm{SL}_1(D)(\mathbb A)^2$, and
  `covolume_muSq`: $\tau(\mathrm{SL}_1(D)^2) = 1$;
* **`covolume_gnatSq`**: for Weil's quotient measure $\mu_P$ on $P = G^\natural(\mathbb A)/\mathbb A^\times$ (= $SO(D,\operatorname{nrd})(\mathbb A)$),
  $$\operatorname{vol}(P(F)\backslash P(\mathbb A),\ \mu_P) = 2,$$
  **unconditionally**, for every quaternion algebra over every number field (division or split; the split case uses
  `tauSL1EqOne`, and the conjugation invariance comes from the unimodularity of $\mathrm{SL}_1(\mathbb A)$, not from compactness).

This is the case $E = F\times F$; it is not Weil's $(R^{(1)}\times R^{(1)})/\pm1$ (p. 65), which sits inside as the
derived group. The identification of $\mu_P$ with `muTam` of the norm form is the remaining step (see
`GnatTamagawa.lean`).
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

section Data

variable (a b : F)

/-- $\operatorname{nrd}$ as a continuous homomorphism. -/
def nrdCHom : (QuatAdele a b)ˣ →ₜ* (Adeles F)ˣ := ⟨nrdHom a b, continuous_nrdHom⟩

/-- `quatScalar` as a continuous homomorphism. -/
def quatScalarCHom : (Adeles F)ˣ →ₜ* (QuatAdele a b)ˣ := ⟨quatScalar a b, continuous_quatScalar a b⟩

/-- The diagonal $u\mapsto(u,u)$. -/
def diagCHom {X : Type*} [Group X] [TopologicalSpace X] : X →ₜ* X × X :=
  ⟨(MonoidHom.id X).prod (MonoidHom.id X), continuous_id.prodMk continuous_id⟩

theorem isClosedEmbedding_quatScalar : IsClosedEmbedding (quatScalar a b) := by
  have h : (quatScalar a b : (Adeles F)ˣ → (QuatAdele a b)ˣ) =
      Subtype.val ∘ (scalarEquiv (a := a) (b := b) : (Adeles F)ˣ → (quatScalar a b).range) := rfl
  rw [h]
  exact (isClosed_range_quatScalar (a := a) (b := b)).isClosedEmbedding_subtypeVal.comp
    (scalarEquiv (a := a) (b := b)).toHomeomorph.isClosedEmbedding

theorem isClosedEmbedding_diag {X : Type*} [TopologicalSpace X] [T2Space X] :
    IsClosedEmbedding (fun x : X => (x, x)) :=
  ⟨⟨IsInducing.of_comp (continuous_id.prodMk continuous_id) continuous_fst IsInducing.id,
    fun x y h => congrArg Prod.fst h⟩, by
    have : Set.range (fun x : X => (x, x)) = Set.diagonal X := by ext ⟨x, y⟩; simp [eq_comm]
    rw [this]; exact isClosed_diagonal⟩

variable {a b}

/-- **The data of $G^\natural$ for $E = F\times F$**: $\{(\alpha,\beta,u) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta = u\}$. -/
def gnatSq (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    GnatData F ((QuatAdele a b)ˣ × (QuatAdele a b)ˣ) ((Adeles F)ˣ × (Adeles F)ˣ) where
  ν := (nrdCHom a b).prodMap (nrdCHom a b)
  ι := diagCHom
  s := diagCHom.comp (quatScalarCHom a b)
  ι_injective x y h := congrArg Prod.fst h
  s_closedEmbedding := isClosedEmbedding_diag.comp (isClosedEmbedding_quatScalar a b)
  s_central u m := Prod.ext (quatScalar_comm a b u m.1) (quatScalar_comm a b u m.2)
  ν_s u := Prod.ext (nrdUnit_quatScalar (a := a) (b := b) u) (nrdUnit_quatScalar (a := a) (b := b) u)
  Apos := posA a b
  isOpen_Apos := isOpen_posA a b
  mem_Apos m u h := by
    have h1 : nrdHom a b m.1 = u := congrArg Prod.fst h
    exact (mem_posA_iff_exists_nrd ha0 hb0 u).2 ⟨m.1, h1⟩
  surj_Apos u hu := by
    obtain ⟨x, hx⟩ := (mem_posA_iff_exists_nrd ha0 hb0 u).1 hu
    exact ⟨(x, x), Prod.ext hx hx⟩
  ΓM := (quatUnitsSub a b).prod (quatUnitsSub a b)

variable (ha0 : a ≠ 0) (hb0 : b ≠ 0)

theorem gnatSq_ν_apply (m : (QuatAdele a b)ˣ × (QuatAdele a b)ˣ) :
    (gnatSq ha0 hb0).ν m = (nrdHom a b m.1, nrdHom a b m.2) := rfl

instance : DiscreteTopology (gnatSq ha0 hb0).ΓM :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : (quatUnitsSub a b).prod (quatUnitsSub a b) =>
      ((⟨(x : (QuatAdele a b)ˣ × (QuatAdele a b)ˣ).1, x.2.1⟩ : quatUnitsSub a b),
        (⟨(x : (QuatAdele a b)ˣ × (QuatAdele a b)ˣ).2, x.2.2⟩ : quatUnitsSub a b)))
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    fun x y h => Subtype.ext (Prod.ext (congrArg (fun z => (z.1 : (QuatAdele a b)ˣ)) h)
      (congrArg (fun z => (z.2 : (QuatAdele a b)ˣ)) h))

instance : Countable (gnatSq ha0 hb0).ΓM :=
  Injective.countable (f := fun x : (quatUnitsSub a b).prod (quatUnitsSub a b) =>
      ((⟨(x : (QuatAdele a b)ˣ × (QuatAdele a b)ˣ).1, x.2.1⟩ : quatUnitsSub a b),
        (⟨(x : (QuatAdele a b)ˣ × (QuatAdele a b)ˣ).2, x.2.2⟩ : quatUnitsSub a b)))
    fun x y h => Subtype.ext (Prod.ext (congrArg (fun z => (z.1 : (QuatAdele a b)ˣ)) h)
      (congrArg (fun z => (z.2 : (QuatAdele a b)ˣ)) h))

theorem gnatSq_hsΓ (u : (Adeles F)ˣ) : (gnatSq ha0 hb0).s u ∈ (gnatSq ha0 hb0).ΓM ↔ u ∈ diagUnitsSub F := by
  change (quatScalar a b u ∈ quatUnitsSub a b ∧ quatScalar a b u ∈ quatUnitsSub a b) ↔ _
  rw [and_self, quatScalar_mem_quatUnitsSub_iff]

theorem gnatSq_heich (f : Fˣ) (hf : diagUnits F f ∈ (gnatSq ha0 hb0).Apos) :
    ∃ γ ∈ (gnatSq ha0 hb0).ΓM, (gnatSq ha0 hb0).ν γ = (gnatSq ha0 hb0).ι (diagUnits F f) := by
  obtain ⟨γ, hγ, hνγ⟩ := exists_global_nrd ha0 hb0 f hf
  exact ⟨(γ, γ), ⟨hγ, hγ⟩, Prod.ext hνγ hνγ⟩

theorem gnatSq_hsign (x : (Adeles F)ˣ) : ∃ f : Fˣ, diagUnits F f * x ∈ (gnatSq ha0 hb0).Apos :=
  exists_diag_mul_mem_posA x

end Data

/-! ### $\mathrm{SL}_1(D)$ on $\ker\operatorname{nrd}$, every quaternion algebra -/

section Kernel

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ on $\ker\operatorname{nrd}$** for every quaternion algebra $D = \mathbb H[F,a,b]$ (division or
split), every number field (`tauSL1EqOne`). -/
theorem covolume_muSL1N :
    covolume ((quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) = 1 := by
  have hH := isHaarMeasure_muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (F := F)
    (by simpa using ha0) (by simpa using hb0)
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := (a : F)) (b := (b : F))
  have hFD : IsExactFD (Γ := (quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      ((kerNrdEquiv (a : F) (b : F)).symm '' DK) :=
    isExactFD_image_mulEquiv' (kerNrdEquiv (a : F) (b : F)).symm.toMulEquiv
      (kerNrdEquiv (a : F) (b : F)).continuous.measurable _ _
      (fun y => by
        rw [← kerNrdEquiv_mem_iff]
        change (kerNrdEquiv _ _) ((kerNrdEquiv _ _).symm y) ∈ _ ↔ _
        rw [ContinuousMulEquiv.apply_symm_apply]) hDK
  have : SMulInvariantMeasure ((quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  have hm : Measurable (kerNrdEquiv (a : F) (b : F)).symm := (kerNrdEquiv _ _).symm.continuous.measurable
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have h1 := covolume_SL1_eq (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hDK
  rw [(tauSL1EqOne a b).covolume_eq_one ha0 hb0] at h1
  rw [(hFD.isFundamentalDomain _).covolume_eq_volume, muSL1N, Measure.map_apply hm hFD.1,
    (kerNrdEquiv (a : F) (b : F)).symm.injective.preimage_image]
  exact h1.symm

/-- **Conjugation by any unit of $D\otimes\mathbb A$ preserves `muSL1N`**, for every quaternion algebra $D$ (division or
split): $\mathrm{SL}_1(\mathbb A)$ is unimodular because $\tau(\mathrm{SL}_1) = 1 < \infty$ (`isMulRightInvariant_muSL1_of_lt_top`),
hence `map_adK_muSL1_of_isMulRightInvariant`. -/
theorem map_adK_muSL1N (m : (QuatAdele (a : F) (b : F))ˣ) :
    (muSL1N ha0 hb0).map (NormalFib.adK (nrdHom (a : F) (b : F)) m) = muSL1N ha0 hb0 := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hfin : covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0') ≠ ∞ := by
    rw [(tauSL1EqOne a b).covolume_eq_one ha0 hb0]; exact ENNReal.one_ne_top
  have := isMulRightInvariant_muSL1_of_lt_top (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hfin
  rw [adK_nrdHom_eq, muSL1N]
  have h1 : Measurable (kerNrdEquiv (a : F) (b : F)) := (kerNrdEquiv _ _).continuous.measurable
  have h2 : Measurable (kerNrdEquiv (a : F) (b : F)).symm := (kerNrdEquiv _ _).symm.continuous.measurable
  have h3 := NormalFib.measurable_adK (nrdOne (a : F) (b : F)) (quatSplit (a : F) (b : F) m).1
  rw [Measure.map_map (h2.comp (h3.comp h1)) h2]
  have : ((kerNrdEquiv (a : F) (b : F)).symm ∘ NormalFib.adK (nrdOne (a : F) (b : F)) (quatSplit _ _ m).1 ∘
      kerNrdEquiv (a : F) (b : F)) ∘ (kerNrdEquiv (a : F) (b : F)).symm =
      (kerNrdEquiv (a : F) (b : F)).symm ∘ NormalFib.adK (nrdOne (a : F) (b : F)) (quatSplit _ _ m).1 := by
    funext y; simp
  rw [this, ← Measure.map_map h2 h3,
    map_adK_muSL1_of_isMulRightInvariant (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0']

end Kernel

/-! ### The Tamagawa measure of $\ker\nu = \mathrm{SL}_1(D)(\mathbb A)^2$ -/

omit [NumberField F] in
/-- **Products of exact fundamental domains** (generic). -/
theorem isExactFD_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] [MeasurableSpace H₁] [MeasurableSpace H₂]
    {Γ₁ : Subgroup H₁} {Γ₂ : Subgroup H₂} {D₁ : Set H₁} {D₂ : Set H₂} (h₁ : IsExactFD (Γ := Γ₁) D₁)
    (h₂ : IsExactFD (Γ := Γ₂) D₂) : IsExactFD (Γ := Γ₁.prod Γ₂) (D₁ ×ˢ D₂) := by
  refine ⟨h₁.1.prod h₂.1, fun y => ?_⟩
  obtain ⟨γ₁, hγ₁, hu₁⟩ := h₁.2 y.1
  obtain ⟨γ₂, hγ₂, hu₂⟩ := h₂.2 y.2
  refine ⟨⟨((γ₁ : H₁), (γ₂ : H₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨hγ₁, hγ₂⟩, fun γ hγ => ?_⟩
  have e₁ := hu₁ ⟨(γ : H₁ × H₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ hγ.1
  have e₂ := hu₂ ⟨(γ : H₁ × H₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ hγ.2
  exact Subtype.ext (Prod.ext (congrArg Subtype.val e₁) (congrArg Subtype.val e₂))

section Measure

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

/-- `gnatSq` for $a, b\in\mathcal O_F$. -/
abbrev gnatSqO : GnatData F ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ)
    ((Adeles F)ˣ × (Adeles F)ˣ) :=
  gnatSq (a := (a : F)) (b := (b : F)) (by simpa using ha0) (by simpa using hb0)

local notation "dSq" => gnatSqO ha0 hb0
/-- $\nu = \operatorname{nrd}\times\operatorname{nrd}$ as a homomorphism. -/
abbrev nuSq : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ →* (Adeles F)ˣ × (Adeles F)ˣ :=
  ((gnatSqO ha0 hb0).ν : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ →* (Adeles F)ˣ × (Adeles F)ˣ)

theorem nuSq_eq : nuSq ha0 hb0 = (nrdHom (a : F) (b : F)).prodMap (nrdHom (a : F) (b : F)) := rfl

theorem mem_ker_nuSq {x : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ} :
    x ∈ (nuSq ha0 hb0).ker ↔ x.1 ∈ (nrdHom (a : F) (b : F)).ker ∧ x.2 ∈ (nrdHom (a : F) (b : F)).ker := by
  rw [nuSq_eq, MonoidHom.ker_prodMap]; rfl


instance : DiscreteTopology ((quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : (quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker =>
      (⟨((x : (nrdHom (a : F) (b : F)).ker) : (QuatAdele (a : F) (b : F))ˣ), x.2⟩ : quatUnitsSub (a : F) (b : F)))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

/-- The units of $D\otimes\mathbb A$. -/
local notation "MD" => (QuatAdele ((a : 𝓞 F) : F) ((b : 𝓞 F) : F))ˣ

/-- $\ker(\operatorname{nrd}\times\operatorname{nrd})\cong\ker\operatorname{nrd}\times\ker\operatorname{nrd}$. -/
def kerSqEquiv : (nuSq ha0 hb0).ker ≃ₜ* (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker where
  toFun x := (⟨((x : MD × MD)).1, ((mem_ker_nuSq ha0 hb0).1 x.2).1⟩, ⟨((x : MD × MD)).2, ((mem_ker_nuSq ha0 hb0).1 x.2).2⟩)
  invFun y := ⟨((y.1 : MD), (y.2 : MD)), (mem_ker_nuSq ha0 hb0).2 ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    have h1 : Continuous fun x : (nuSq ha0 hb0).ker => ((x : MD × MD)).1 := continuous_fst.comp continuous_subtype_val
    have h2 : Continuous fun x : (nuSq ha0 hb0).ker => ((x : MD × MD)).2 := continuous_snd.comp continuous_subtype_val
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)
  continuous_invFun := by
    have h : Continuous fun y : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker =>
        ((y.1 : MD), (y.2 : MD)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    exact h.subtype_mk _

/-- **The Tamagawa measure $\mu_{\mathrm{SL}_1}\times\mu_{\mathrm{SL}_1}$ on $\ker\nu$.** -/
def muSq : Measure (nuSq ha0 hb0).ker :=
  ((muSL1N ha0 hb0).prod (muSL1N ha0 hb0)).map (kerSqEquiv ha0 hb0).symm

instance : (muSq ha0 hb0).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

theorem adK_sq_eq (m : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) :
    NormalFib.adK (nuSq ha0 hb0) m = (kerSqEquiv ha0 hb0).symm ∘
      Prod.map (NormalFib.adK (nrdHom (a : F) (b : F)) m.1) (NormalFib.adK (nrdHom (a : F) (b : F)) m.2) ∘
        kerSqEquiv ha0 hb0 := by
  funext x; rfl

theorem map_adK_muSq (m : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) :
    (muSq ha0 hb0).map (NormalFib.adK (nuSq ha0 hb0) m) = muSq ha0 hb0 := by
  have hk : Measurable (kerSqEquiv ha0 hb0) := (kerSqEquiv ha0 hb0).continuous.measurable
  have hks : Measurable (kerSqEquiv ha0 hb0).symm := (kerSqEquiv ha0 hb0).symm.continuous.measurable
  have h1 := NormalFib.measurable_adK (nrdHom (a : F) (b : F)) m.1
  have h2 := NormalFib.measurable_adK (nrdHom (a : F) (b : F)) m.2
  rw [adK_sq_eq, muSq, Measure.map_map (hks.comp ((h1.prodMap h2).comp hk)) hks]
  have : ((kerSqEquiv ha0 hb0).symm ∘ Prod.map (NormalFib.adK (nrdHom (a : F) (b : F)) m.1)
      (NormalFib.adK (nrdHom (a : F) (b : F)) m.2) ∘ kerSqEquiv ha0 hb0) ∘ (kerSqEquiv ha0 hb0).symm =
      (kerSqEquiv ha0 hb0).symm ∘ Prod.map (NormalFib.adK (nrdHom (a : F) (b : F)) m.1)
        (NormalFib.adK (nrdHom (a : F) (b : F)) m.2) := by
    funext y; simp
  rw [this, ← Measure.map_map hks (h1.prodMap h2), ← Measure.map_prod_map _ _ h1 h2,
    map_adK_muSL1N ha0 hb0, map_adK_muSL1N ha0 hb0]

set_option maxHeartbeats 1600000 in
/-- **$\tau(\mathrm{SL}_1(D)\times\mathrm{SL}_1(D)) = 1$** (every quaternion algebra $D$). -/
theorem covolume_muSq :
    covolume ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (nuSq ha0 hb0).ker (muSq ha0 hb0) = 1 := by
  set Γ1 := (quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker
  obtain ⟨D1, hD1m, hD1⟩ := exists_measurableSet_forall_existsUnique_smul_mem Γ1
  have hμ1 : muSL1N ha0 hb0 D1 = 1 := by
    have : SMulInvariantMeasure Γ1 (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) :=
      ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
    rw [← covolume_muSL1N ha0 hb0, ((IsExactFD.isFundamentalDomain ⟨hD1m, hD1⟩) _).covolume_eq_volume]
  -- the product is an exact fundamental domain of `Γ1 × Γ1`, transported to `ker ν`
  set e := (kerSqEquiv ha0 hb0).symm
  have hmem : ∀ y, e y ∈ (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker ↔ y ∈ Γ1.prod Γ1 := by
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hFDprod : IsExactFD (Γ := Γ1.prod Γ1) (D1 ×ˢ D1) := isExactFD_prod ⟨hD1m, hD1⟩ ⟨hD1m, hD1⟩
  have hFD : IsExactFD (Γ := (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (e '' (D1 ×ˢ D1)) :=
    isExactFD_image_mulEquiv' e.toMulEquiv (kerSqEquiv ha0 hb0).continuous.measurable _ _ hmem hFDprod
  have : Countable ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) :=
    Injective.countable (f := fun x : (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker =>
      (⟨((x : (nuSq ha0 hb0).ker) : _ × _), x.2⟩ : (dSq).ΓM))
      fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')
  have : SMulInvariantMeasure ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (nuSq ha0 hb0).ker
      (muSq ha0 hb0) := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  have hks : Measurable e := e.continuous.measurable
  rw [(hFD.isFundamentalDomain _).covolume_eq_volume, muSq, Measure.map_apply hks hFD.1,
    e.injective.preimage_image, Measure.prod_prod, hμ1, one_mul]

end Measure

/-! ### The theorem -/

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "dSq" => gnatSqO ha0 hb0

/-- **Square discriminant:
$\operatorname{vol}(SO(D,\operatorname{nrd})(F)\backslash SO(D,\operatorname{nrd})(\mathbb A)) = 2$** for Weil's
quotient measure $\mu_P = \mu_{G^\natural}/\mu_{\mathbb A^\times}$, $\mu_{G^\natural}$ fibred over `tamIdeles` with fibre
$\mu_{\mathrm{SL}_1}\times\mu_{\mathrm{SL}_1}$, for every quaternion algebra $D$ (division or split) over every number field.
Unconditional. -/
@[kb "weil1982" "§3.7, pp. 64-65 (m = 4, square discriminant) [unverified page]; §3.2, p. 43 (centre)"]
theorem covolume_gnatSq :
    covolume (dSq).gamP (dSq).P ((dSq).muP (muSq ha0 hb0)) = 2 := by
  have h := (dSq).covolume_muP (muSq ha0 hb0) (gnatSq_hsΓ _ _) (gnatSq_heich _ _) (gnatSq_hsign _ _)
    (map_adK_muSq ha0 hb0) (covolume_muSq ha0 hb0)
  rw [h, mul_one]

end

end QuadFormsKB.Tamagawa.Measure.Weil
