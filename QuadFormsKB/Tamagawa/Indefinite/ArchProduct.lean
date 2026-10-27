/-
# Products of archimedean fibrations (Siegel's formula for indefinite forms)

**Layer:** abstract group and measure theory. The archimedean group of a number field $F$ is a product over the
infinite places, $G_\infty = \prod_{w\ \mathrm{real}}SO(Q^{\sigma_w})(\mathbb R)\times
\prod_{w\ \mathrm{complex}}SO(Q^{\tau_w})(\mathbb C)$ (`GInfSO`). This file assembles archimedean fibrations
(`ThetaUnfold.ArchFibration`) of the factors into one for the product.

**Proves / constructs** (all unconditional, standard axioms only)
* `piProdME`, `measurePreserving_piProdME`: $(\prod_i\alpha_i\times\beta_i)\cong(\prod_i\alpha_i)\times(\prod_i\beta_i)$
  carries $\bigotimes_i(\mu_i\otimes\nu_i)$ to $(\bigotimes_i\mu_i)\otimes(\bigotimes_i\nu_i)$ (dependent version of
  Mathlib's `measurePreserving_arrowProdEquivProdArrow`); `measurePreserving_prodProdProdComm` likewise for two
  factors;
* `pi_smul`: $\bigotimes_i c_i\mu_i = (\prod_ic_i)\bigotimes_i\mu_i$ for finite $c_i$;
* `stabPi`, `stabProd`: the stabilizer of $y$ in a product group is the product of the stabilizers;
* `ArchFibration.pi`, `ArchFibration.prod`, `ArchFibration.smul`: fibrations of the factors (constants $c_i$) give a
  fibration of the product (constant $\prod_ic_i$), and rescaling $\mu_A$ by $a$ rescales the constant by $a$.

**Outside results used:** Mathlib's `FiniteSpanningSetsIn.ext`, `generateFrom_eq_prod`, `generateFrom_pi`,
`Measure.pi_eq`, `Measure.pi_map_pi`, `map_prod_map`.
-/
import QuadFormsKB.Tamagawa.Indefinite.ThetaUnfold

open MeasureTheory Measure MulAction Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Rearranging products of measures -/

section Rearrange

variable {ι : Type*} [Fintype ι] (α β : ι → Type*) [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]

/-- $(\prod_i\alpha_i\times\beta_i)\cong(\prod_i\alpha_i)\times(\prod_i\beta_i)$, measurably. -/
def piProdME : (∀ i, α i × β i) ≃ᵐ (∀ i, α i) × (∀ i, β i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

/-- **Products of product measures, dependent version**: `piProdME` carries
$\bigotimes_i(\mu_i\otimes\nu_i)$ to $(\bigotimes_i\mu_i)\otimes(\bigotimes_i\nu_i)$. -/
theorem measurePreserving_piProdME (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (piProdME α β) (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (piProdME α β).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (piProdME α β) ⁻¹' (univ.pi s ×ˢ univ.pi t) = (univ.pi fun i => s i ×ˢ t i) by
          ext x
          exact ⟨fun h i _ => ⟨h.1 i trivial, h.2 i trivial⟩,
            fun h => ⟨fun i _ => (h i trivial).1, fun i _ => (h i trivial).2⟩⟩]
      simp_rw [pi_pi, prod_prod, pi_pi, Finset.prod_mul_distrib]

variable {T₁ T₂ S₁ S₂ : Type*} [MeasurableSpace T₁] [MeasurableSpace T₂] [MeasurableSpace S₁] [MeasurableSpace S₂]

/-- $(T_1\times T_2)\times(S_1\times S_2)\cong(T_1\times S_1)\times(T_2\times S_2)$, measurably. -/
def prodProdProdCommME (T₁ T₂ S₁ S₂ : Type*) [MeasurableSpace T₁] [MeasurableSpace T₂] [MeasurableSpace S₁]
    [MeasurableSpace S₂] : (T₁ × T₂) × (S₁ × S₂) ≃ᵐ (T₁ × S₁) × (T₂ × S₂) where
  toEquiv := Equiv.prodProdProdComm T₁ T₂ S₁ S₂
  measurable_toFun := ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  measurable_invFun := ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

/-- **Rearranging a fourfold product measure.** -/
theorem measurePreserving_prodProdProdComm (σ₁ : Measure T₁) (σ₂ : Measure T₂) (μ₁ : Measure S₁)
    (μ₂ : Measure S₂) [SigmaFinite σ₁] [SigmaFinite σ₂] [SigmaFinite μ₁] [SigmaFinite μ₂] :
    MeasurePreserving (prodProdProdCommME T₁ T₂ S₁ S₂) ((σ₁.prod σ₂).prod (μ₁.prod μ₂))
      ((σ₁.prod μ₁).prod (σ₂.prod μ₂)) where
  measurable := (prodProdProdCommME T₁ T₂ S₁ S₂).measurable
  map_eq := by
    have h1 := σ₁.toFiniteSpanningSetsIn.prod μ₁.toFiniteSpanningSetsIn
    have h2 := σ₂.toFiniteSpanningSetsIn.prod μ₂.toFiniteSpanningSetsIn
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_prod.prod isPiSystem_prod) (h1.prod h2) ?_).symm
    · exact (generateFrom_eq_prod generateFrom_prod generateFrom_prod h1.isCountablySpanning
        h2.isCountablySpanning).symm
    · rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, _, ⟨c, hc, d, hd, rfl⟩, rfl⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (prodProdProdCommME T₁ T₂ S₁ S₂) ⁻¹' ((a ×ˢ b) ×ˢ (c ×ˢ d)) = (a ×ˢ c) ×ˢ (b ×ˢ d) by
          ext ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
          simp only [mem_preimage, mem_prod]
          exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩]
      simp only [prod_prod]
      ring

/-- A finite multiple of a σ-finite measure is σ-finite. -/
theorem sigmaFinite_smul {γ : Type*} [MeasurableSpace γ] (μ : Measure γ) [SigmaFinite μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) :=
  ⟨⟨⟨spanningSets μ, fun _ => trivial, fun k => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ k), iUnion_spanningSets μ⟩⟩⟩

/-- $\bigotimes_ic_i\mu_i = (\prod_ic_i)\bigotimes_i\mu_i$ for finite constants. -/
theorem pi_smul {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)] (μ : ∀ i, Measure (γ i)) [∀ i, SigmaFinite (μ i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    haveI := fun i => sigmaFinite_smul (μ i) (hc i)
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI := fun i => sigmaFinite_smul (μ i) (hc i)
  refine pi_eq fun s hs => ?_
  rw [Measure.smul_apply, pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  rfl

end Rearrange

/-! ### Stabilizers in product groups -/

section Stab

variable {ι : Type*} {A : ι → Type*} [∀ i, Group (A i)] {Y : ι → Type*} [∀ i, MulAction (A i) (Y i)]

/-- The stabilizer of `y` in $\prod_iA_i$ is $\prod_i\operatorname{Stab}_{A_i}(y_i)$. -/
def stabPi (y : ∀ i, Y i) : stabilizer (∀ i, A i) y ≃* ∀ i, stabilizer (A i) (y i) where
  toFun g i := ⟨(g : ∀ i, A i) i, congrFun (mem_stabilizer_iff.mp g.2) i⟩
  invFun h := ⟨fun i => h i, mem_stabilizer_iff.mpr (funext fun i => mem_stabilizer_iff.mp (h i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [∀ i, MeasurableSpace (A i)]

/-- `stabPi` as a measurable equivalence. -/
def stabPiME (y : ∀ i, Y i) : stabilizer (∀ i, A i) y ≃ᵐ ∀ i, stabilizer (A i) (y i) where
  toEquiv := (stabPi y).toEquiv
  measurable_toFun := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (measurable_pi_iff.mpr fun i =>
    measurable_subtype_coe.comp (measurable_pi_apply i)).subtype_mk

variable {A₁ A₂ Y₁ Y₂ : Type*} [Group A₁] [Group A₂] [MulAction A₁ Y₁] [MulAction A₂ Y₂]

/-- **The componentwise action** of $A_1\times A_2$ on $Y_1\times Y_2$: $(g_1, g_2)\cdot(y_1, y_2) =
(g_1y_1, g_2y_2)$. -/
instance instMulActionProdProd : MulAction (A₁ × A₂) (Y₁ × Y₂) where
  smul g y := (g.1 • y.1, g.2 • y.2)
  one_smul y := Prod.ext (one_smul A₁ y.1) (one_smul A₂ y.2)
  mul_smul g h y := Prod.ext (mul_smul g.1 h.1 y.1) (mul_smul g.2 h.2 y.2)

theorem prod_smul_def (g : A₁ × A₂) (y : Y₁ × Y₂) : g • y = (g.1 • y.1, g.2 • y.2) := rfl

/-- The stabilizer of $(y_1, y_2)$ in $A_1\times A_2$ is $\operatorname{Stab}(y_1)\times\operatorname{Stab}(y_2)$. -/
def stabProd (y : Y₁ × Y₂) : stabilizer (A₁ × A₂) y ≃* stabilizer A₁ y.1 × stabilizer A₂ y.2 where
  toFun g := (⟨(g : A₁ × A₂).1, congrArg Prod.fst (mem_stabilizer_iff.mp g.2)⟩,
    ⟨(g : A₁ × A₂).2, congrArg Prod.snd (mem_stabilizer_iff.mp g.2)⟩)
  invFun h := ⟨((h.1 : A₁), (h.2 : A₂)), mem_stabilizer_iff.mpr
    (Prod.ext (mem_stabilizer_iff.mp h.1.2) (mem_stabilizer_iff.mp h.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [MeasurableSpace A₁] [MeasurableSpace A₂]

/-- `stabProd` as a measurable equivalence. -/
def stabProdME (y : Y₁ × Y₂) : stabilizer (A₁ × A₂) y ≃ᵐ stabilizer A₁ y.1 × stabilizer A₂ y.2 where
  toEquiv := (stabProd y).toEquiv
  measurable_toFun := (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
    (measurable_snd.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk

end Stab

/-! ### Operations on archimedean fibrations -/

section Smul

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μA : Measure A}
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T] {P : Set Y} {σ : Measure T} {τ : T → Y}
  {c : ℝ≥0∞}

/-- **Transport along an equality of measures** on `A`; the stabilizer measures and coordinates are unchanged. -/
def ArchFibration.congrMeasure (𝔉 : ArchFibration μA P σ τ c) {μA' : Measure A} (h : μA = μA') :
    ArchFibration μA' P σ τ c where
  μH := 𝔉.μH
  coord := 𝔉.coord
  sigmaFinite := 𝔉.sigmaFinite
  leftInv := 𝔉.leftInv
  fib y hy := h ▸ 𝔉.fib y hy

/-- **Rescaling**: a fibration for $\mu_A$ with constant $c$ is one for $a\mu_A$ with constant $ac$. -/
def ArchFibration.smul (𝔉 : ArchFibration μA P σ τ c) (a : ℝ≥0∞) : ArchFibration (a • μA) P σ τ (a * c) where
  μH := 𝔉.μH
  coord := 𝔉.coord
  sigmaFinite := 𝔉.sigmaFinite
  leftInv := 𝔉.leftInv
  fib y hy := by
    conv_lhs => rw [𝔉.fib y hy]
    rw [smul_smul]

end Smul

section Pi

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Group (A i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, MeasurableMul (A i)] {Y : ι → Type*} [∀ i, MulAction (A i) (Y i)] {T : ι → Type*}
  [∀ i, MeasurableSpace (T i)] {μA : ∀ i, Measure (A i)} {P : ∀ i, Set (Y i)} {σ : ∀ i, Measure (T i)}
  {τ : ∀ i, T i → Y i} {c : ι → ℝ≥0∞}

/-- The orbit coordinates of a product: $\mathrm{coord}(x, h)_i = \mathrm{coord}_i(x_i, h_i)$. -/
def piCoord (𝔉 : ∀ i, ArchFibration (μA i) (P i) (σ i) (τ i) (c i)) (y : ∀ i, Y i) (hy : y ∈ univ.pi P) :
    OrbitCoord (stabilizer (∀ i, A i) y).subtype (fun (x : ∀ i, T i) i => τ i (x i)) y where
  coord := (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (stabPiME y)).trans
    ((piProdME T fun i => stabilizer (A i) (y i)).symm.trans
      (MeasurableEquiv.piCongrRight fun i => ((𝔉 i).coord (y i) (hy i trivial)).coord))
  mul x h h' := by
    funext i
    exact ((𝔉 i).coord (y i) (hy i trivial)).mul (x i) ((stabPi y) h i) ((stabPi y) h' i)
  orbit x h := by
    funext i
    exact ((𝔉 i).coord (y i) (hy i trivial)).orbit (x i) ((stabPi y) h i)

/-- **The fibration of a finite product** $\prod_iA_i$ acting on $\prod_iY_i$ over $\prod_iP_i$, with
$\mu_{H_y} = \bigotimes_i\mu_{H_{y_i}}$ and constant $\prod_ic_i$ (finite constants). -/
def ArchFibration.pi [∀ i, SigmaFinite (σ i)] (hc : ∀ i, c i ≠ ⊤)
    (𝔉 : ∀ i, ArchFibration (μA i) (P i) (σ i) (τ i) (c i)) :
    ArchFibration (Measure.pi μA) (univ.pi P) (Measure.pi σ) (fun x i => τ i (x i)) (∏ i, c i) where
  μH y := (Measure.pi fun i => (𝔉 i).μH (y i)).map (stabPiME y).symm
  coord y hy := piCoord 𝔉 y hy
  sigmaFinite y := by
    haveI := fun i => (𝔉 i).sigmaFinite (y i)
    exact (stabPiME y).symm.sigmaFinite_map
  leftInv y := by
    haveI := fun i => (𝔉 i).sigmaFinite (y i)
    haveI := fun i => (𝔉 i).leftInv (y i)
    haveI : ∀ i, MeasurableMul (stabilizer (A i) (y i)) := fun i => measurableMul_subgroup _
    haveI := measurableMul_subgroup (stabilizer (∀ i, A i) y)
    exact isMulLeftInvariant_map (stabPi y).symm.toMulHom (stabPiME y).symm.measurable
      (stabPi y).symm.surjective
  fib y hy := by
    haveI := fun i => (𝔉 i).sigmaFinite (y i)
    have hmc : ∀ i, Measurable ((𝔉 i).coord (y i) (hy i trivial)).coord := fun i =>
      ((𝔉 i).coord (y i) (hy i trivial)).coord.measurable
    haveI : ∀ i, SigmaFinite (((σ i).prod ((𝔉 i).μH (y i))).map ((𝔉 i).coord (y i) (hy i trivial)).coord) :=
      fun i => ((𝔉 i).coord (y i) (hy i trivial)).coord.sigmaFinite_map
    have h1 : (Measure.pi σ).prod ((Measure.pi fun i => (𝔉 i).μH (y i)).map (stabPiME y).symm) =
        ((Measure.pi σ).prod (Measure.pi fun i => (𝔉 i).μH (y i))).map (Prod.map id (stabPiME y).symm) := by
      rw [← map_prod_map _ _ measurable_id (stabPiME y).symm.measurable, Measure.map_id]
    set G : (∀ i, T i × stabilizer (A i) (y i)) → ∀ i, A i :=
      fun z i => ((𝔉 i).coord (y i) (hy i trivial)).coord (z i) with hGdef
    have hG : Measurable G := measurable_pi_iff.mpr fun i => (hmc i).comp (measurable_pi_apply i)
    have h2 : (piCoord 𝔉 y hy).coord ∘ Prod.map id (stabPiME y).symm =
        G ∘ (piProdME T fun i => stabilizer (A i) (y i)).symm := by
      funext p
      rfl
    show Measure.pi μA = (∏ i, c i) • ((Measure.pi σ).prod
      ((Measure.pi fun i => (𝔉 i).μH (y i)).map (stabPiME y).symm)).map (piCoord 𝔉 y hy).coord
    rw [h1, Measure.map_map (piCoord 𝔉 y hy).coord.measurable (measurable_id.prodMap (stabPiME y).symm.measurable),
      h2, ← Measure.map_map hG (piProdME T fun i => stabilizer (A i) (y i)).symm.measurable,
      (measurePreserving_piProdME T (fun i => stabilizer (A i) (y i)) σ
        (fun i => (𝔉 i).μH (y i))).symm.map_eq, hGdef,
      pi_map_pi (fun i => (hmc i).aemeasurable), ← pi_smul _ c hc]
    congr 1
    funext i
    exact (𝔉 i).fib (y i) (hy i trivial)

end Pi

section Prod

variable {A₁ A₂ : Type*} [Group A₁] [Group A₂] [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableMul A₁]
  [MeasurableMul A₂] {Y₁ Y₂ : Type*} [MulAction A₁ Y₁] [MulAction A₂ Y₂] {T₁ T₂ : Type*} [MeasurableSpace T₁]
  [MeasurableSpace T₂] {μ₁ : Measure A₁} {μ₂ : Measure A₂} {P₁ : Set Y₁} {P₂ : Set Y₂} {σ₁ : Measure T₁}
  {σ₂ : Measure T₂} {τ₁ : T₁ → Y₁} {τ₂ : T₂ → Y₂} {c₁ c₂ : ℝ≥0∞}

/-- The orbit coordinates of a product of two: $\mathrm{coord}((x_1, x_2), h) =
(\mathrm{coord}_1(x_1, h_1), \mathrm{coord}_2(x_2, h_2))$. -/
def prodCoord (𝔉₁ : ArchFibration μ₁ P₁ σ₁ τ₁ c₁) (𝔉₂ : ArchFibration μ₂ P₂ σ₂ τ₂ c₂) (y : Y₁ × Y₂)
    (hy : y ∈ P₁ ×ˢ P₂) : OrbitCoord (stabilizer (A₁ × A₂) y).subtype (Prod.map τ₁ τ₂) y where
  coord := (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (stabProdME y)).trans
    ((prodProdProdCommME T₁ T₂ _ _).trans
      (MeasurableEquiv.prodCongr (𝔉₁.coord y.1 hy.1).coord (𝔉₂.coord y.2 hy.2).coord))
  mul x h h' := Prod.ext ((𝔉₁.coord y.1 hy.1).mul x.1 ((stabProd y) h).1 ((stabProd y) h').1)
    ((𝔉₂.coord y.2 hy.2).mul x.2 ((stabProd y) h).2 ((stabProd y) h').2)
  orbit x h := Prod.ext ((𝔉₁.coord y.1 hy.1).orbit x.1 ((stabProd y) h).1)
    ((𝔉₂.coord y.2 hy.2).orbit x.2 ((stabProd y) h).2)

/-- **The fibration of a product of two groups**, with $\mu_{H_y} = \mu_{H_{y_1}}\otimes\mu_{H_{y_2}}$ and constant
$c_1c_2$. -/
def ArchFibration.prod [SigmaFinite σ₁] [SigmaFinite σ₂] (𝔉₁ : ArchFibration μ₁ P₁ σ₁ τ₁ c₁)
    (𝔉₂ : ArchFibration μ₂ P₂ σ₂ τ₂ c₂) :
    ArchFibration (μ₁.prod μ₂) (P₁ ×ˢ P₂) (σ₁.prod σ₂) (Prod.map τ₁ τ₂) (c₁ * c₂) where
  μH y := ((𝔉₁.μH y.1).prod (𝔉₂.μH y.2)).map (stabProdME y).symm
  coord y hy := prodCoord 𝔉₁ 𝔉₂ y hy
  sigmaFinite y := by
    haveI := 𝔉₁.sigmaFinite y.1
    haveI := 𝔉₂.sigmaFinite y.2
    exact (stabProdME y).symm.sigmaFinite_map
  leftInv y := by
    haveI := 𝔉₁.sigmaFinite y.1
    haveI := 𝔉₂.sigmaFinite y.2
    haveI := 𝔉₁.leftInv y.1
    haveI := 𝔉₂.leftInv y.2
    haveI := measurableMul_subgroup (stabilizer A₁ y.1)
    haveI := measurableMul_subgroup (stabilizer A₂ y.2)
    haveI := measurableMul_subgroup (stabilizer (A₁ × A₂) y)
    exact isMulLeftInvariant_map (stabProd y).symm.toMulHom (stabProdME y).symm.measurable
      (stabProd y).symm.surjective
  fib y hy := by
    haveI := 𝔉₁.sigmaFinite y.1
    haveI := 𝔉₂.sigmaFinite y.2
    set C₁ := (𝔉₁.coord y.1 hy.1).coord
    set C₂ := (𝔉₂.coord y.2 hy.2).coord
    have h1 : (σ₁.prod σ₂).prod (((𝔉₁.μH y.1).prod (𝔉₂.μH y.2)).map (stabProdME y).symm) =
        ((σ₁.prod σ₂).prod ((𝔉₁.μH y.1).prod (𝔉₂.μH y.2))).map (Prod.map id (stabProdME y).symm) := by
      rw [← map_prod_map _ _ measurable_id (stabProdME y).symm.measurable, Measure.map_id]
    have h2 : (prodCoord 𝔉₁ 𝔉₂ y hy).coord ∘ Prod.map id (stabProdME y).symm =
        Prod.map C₁ C₂ ∘ prodProdProdCommME T₁ T₂ _ _ := by
      funext p
      rfl
    show μ₁.prod μ₂ = (c₁ * c₂) • ((σ₁.prod σ₂).prod
      (((𝔉₁.μH y.1).prod (𝔉₂.μH y.2)).map (stabProdME y).symm)).map (prodCoord 𝔉₁ 𝔉₂ y hy).coord
    rw [h1, Measure.map_map (prodCoord 𝔉₁ 𝔉₂ y hy).coord.measurable
        (measurable_id.prodMap (stabProdME y).symm.measurable), h2,
      ← Measure.map_map (C₁.measurable.prodMap C₂.measurable) (prodProdProdCommME T₁ T₂ _ _).measurable,
      (measurePreserving_prodProdProdComm σ₁ σ₂ (𝔉₁.μH y.1) (𝔉₂.μH y.2)).map_eq,
      ← map_prod_map _ _ C₁.measurable C₂.measurable]
    conv_lhs => rw [𝔉₁.fib y.1 hy.1, 𝔉₂.fib y.2 hy.2]
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

end Prod

end QuadFormsKB.Tamagawa.Indefinite
