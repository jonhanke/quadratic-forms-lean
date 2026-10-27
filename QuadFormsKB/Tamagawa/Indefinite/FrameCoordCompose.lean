/-
# Orbit coordinates for frames: composition, the archimedean factor, conjugation

**Layer:** abstract group and measure theory (no number theory). The proof of Siegel's formula for indefinite forms by
forms
builds the orbit coordinates of the frames $X = (x_0,\dots,x_r)$ of a quadratic space by
induction on $r$ from those of single vectors (the adelic sphere). This file is the induction step and the two
operations used afterwards, all on the `OrbitCoord` (a measurable equivalence $T\times H\cong G$ with
$\mathrm{coord}(x, h'h) = \iota(h')\,\mathrm{coord}(x,h)$ and $\mathrm{coord}(x,h)^{-1}y_0 = \tau(x)$).

**Defines / proves**
* `OrbitCoord.compose` (**the induction step**): from coordinates $C_0$ of the orbit of $y_0\in V$ under $G$ (stabilizer
  $\iota_0(H_0)$) and coordinates $C'$ of the orbit of a frame $\Xi'$ of $V'$ under $H_0$, where $e : V'\to V$ is
  $H_0$-equivariant ($e(hz) = \iota_0(h)e(z)$), coordinates $(T_0\times T')\times H\cong G$ of the orbit of the frame
  $(y_0, e(\Xi'))$, $\mathrm{coord}((x,x'),h) = C_0(x, C'(x', h))$. `fib_compose`: the fibration identities
  $\mu_G = c_0\,C_{0*}(\sigma_0\otimes\mu_0)$, $\mu_0 = c'\,C'_*(\sigma'\otimes\mu_H)$ give
  $\mu_G = c_0c'\,\mathrm{coord}_*((\sigma_0\otimes\sigma')\otimes\mu_H)$. `stab_compose`: the stabilizer of the frame is
  $\iota_0\iota'(H)$ if the two stabilizers are $\iota_0(H_0)$, $\iota'(H)$ and $e$ is injective.
* `OrbitCoord.base`: the empty frame ($r = 0$), $T = $ point, $\mathrm{coord} = \mathrm{id}$.
* `OrbitCoord.fstFactor` (**the archimedean factor**): for $G = A\times B$, $H = A'\times B'$, $\iota = \iota_A\times\iota_B$, acting
  on $Y_A\times Y_B$ with base point $(a_0, b_0)$ and stabilizer $\iota(H)$, coordinates $T_A\times A'\cong A$ of the orbit of
  $a_0$, $T_A = \{y : (y, b_0)\in\tau(T)\}$ (Lusin–Souslin for the measurability of the inverse).
* `OrbitCoord.conj`: coordinates at $a\cdot y_0$ from coordinates at $y_0$ (conjugation of the stabilizer).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.SphereUnfoldAbstract
import QuadFormsKB.Tamagawa.Indefinite.ArchProduct

open MeasureTheory Set MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### The induction step -/

section Compose

variable {G H₀ H : Type*} [Group G] [Group H₀] [Group H] [MeasurableSpace G] [MeasurableSpace H₀]
  [MeasurableSpace H] {V V' : Type*} [MulAction G V] [MulAction H₀ V']
  {T₀ T' : Type*} [MeasurableSpace T₀] [MeasurableSpace T']
  {ι₀ : H₀ →* G} {ι' : H →* H₀} {τ₀ : T₀ → V} {y₀ : V} {r : ℕ} {τ' : T' → Fin r → V'} {Ξ' : Fin r → V'}

/-- **The parametrization of the composite frames**: $(x, x')\mapsto(\tau_0(x), C_0(x,1)^{-1}e(\tau'(x')))$. -/
def composeτ (C₀ : OrbitCoord ι₀ τ₀ y₀) (e : V' → V) (τ' : T' → Fin r → V') (p : T₀ × T') : Fin (r + 1) → V :=
  Fin.cons (τ₀ p.1) fun j => (C₀.coord (p.1, 1))⁻¹ • e (τ' p.2 j)

/-- **The composite orbit coordinates** $\mathrm{coord}((x,x'),h) = C_0(x, C'(x', h))$ of the frame $(y_0, e(\Xi'))$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.compose (C₀ : OrbitCoord ι₀ τ₀ y₀) (e : V' → V) (he : ∀ (h : H₀) (z : V'), e (h • z) = ι₀ h • e z)
    (C' : OrbitCoord ι' τ' Ξ') :
    OrbitCoord (ι₀.comp ι') (composeτ C₀ e τ') (Fin.cons y₀ fun j => e (Ξ' j) : Fin (r + 1) → V) where
  coord := MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl T₀) C'.coord).trans C₀.coord)
  mul := by
    rintro ⟨x, x'⟩ h h'
    show C₀.coord (x, C'.coord (x', h' * h)) = ι₀ (ι' h') * C₀.coord (x, C'.coord (x', h))
    rw [C'.mul, C₀.mul]
  orbit := by
    rintro ⟨x, x'⟩ h
    show (C₀.coord (x, C'.coord (x', h)))⁻¹ • (Fin.cons y₀ fun j => e (Ξ' j) : Fin (r + 1) → V) =
      composeτ C₀ e τ' (x, x')
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Pi.smul_apply, Fin.cons_zero, composeτ]
      exact C₀.orbit x _
    · have hj := congrFun (C'.orbit x' h) j
      rw [Pi.smul_apply] at hj
      simp only [Pi.smul_apply, Fin.cons_succ, composeτ]
      rw [C₀.coord_eq x (C'.coord (x', h)), _root_.mul_inv_rev, mul_smul, ← map_inv ι₀, ← he, hj]

theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.compose_coord (C₀ : OrbitCoord ι₀ τ₀ y₀) (e : V' → V)
    (he : ∀ (h : H₀) (z : V'), e (h • z) = ι₀ h • e z) (C' : OrbitCoord ι' τ' Ξ') (p : (T₀ × T') × H) :
    (C₀.compose e he C').coord p = C₀.coord (p.1.1, C'.coord (p.1.2, p.2)) := rfl

/-- **The fibration identities compose**: $\mu_G = c_0\,C_{0*}(\sigma_0\otimes\mu_0)$ and
$\mu_0 = c'\,C'_*(\sigma'\otimes\mu_H)$ give $\mu_G = c_0c'\,\mathrm{coord}_*((\sigma_0\otimes\sigma')\otimes\mu_H)$. -/
theorem fib_compose (C₀ : OrbitCoord ι₀ τ₀ y₀) (e : V' → V) (he : ∀ (h : H₀) (z : V'), e (h • z) = ι₀ h • e z)
    (C' : OrbitCoord ι' τ' Ξ') {μG : Measure G} {μ₀ : Measure H₀} {μH : Measure H} {σ₀ : Measure T₀}
    {σ' : Measure T'} [SFinite σ₀] [SFinite σ'] [SFinite μH] {c₀ c' : ℝ≥0∞}
    (h₀ : μG = c₀ • (σ₀.prod μ₀).map C₀.coord) (h' : μ₀ = c' • (σ'.prod μH).map C'.coord) :
    μG = (c₀ * c') • ((σ₀.prod σ').prod μH).map (C₀.compose e he C').coord := by
  rw [h₀, h', Measure.prod_smul_right, Measure.map_smul, smul_smul]
  congr 1
  have hm1 : σ₀.prod ((σ'.prod μH).map C'.coord) =
      (σ₀.prod (σ'.prod μH)).map (Prod.map id C'.coord) := by
    rw [← Measure.map_prod_map _ _ measurable_id C'.coord.measurable, Measure.map_id]
  have hm2 : σ₀.prod (σ'.prod μH) = ((σ₀.prod σ').prod μH).map MeasurableEquiv.prodAssoc :=
    (measurePreserving_prodAssoc σ₀ σ' μH).map_eq.symm
  rw [hm1, hm2, Measure.map_map (Measurable.prodMap measurable_id C'.coord.measurable)
      MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map C₀.coord.measurable
      ((Measurable.prodMap measurable_id C'.coord.measurable).comp MeasurableEquiv.prodAssoc.measurable)]
  rfl
  exact C₀.coord.measurable.aemeasurable

/-- **The stabilizer of the composite frame**: if the stabilizer of $y_0$ is in $\iota_0(H_0)$, that of $\Xi'$ in $\iota'(H)$,
and $e$ is injective, the stabilizer of $(y_0, e(\Xi'))$ is in $\iota_0\iota'(H)$. Relative version: for subgroups
$\Gamma\le G$, $\Gamma_0\le H_0$, $\Gamma'\le H$. -/
theorem stab_compose {Γ : Subgroup G} {Γ₀ : Subgroup H₀} {Γ' : Subgroup H} (e : V' → V)
    (he : ∀ (h : H₀) (z : V'), e (h • z) = ι₀ h • e z) (he' : Function.Injective e)
    (hι₀ : Function.Injective ι₀)
    (h₀ : ∀ γ ∈ Γ, γ • y₀ = y₀ → ∃ h ∈ Γ₀, ι₀ h = γ)
    (h' : ∀ γ ∈ Γ₀, γ • Ξ' = Ξ' → ∃ h ∈ Γ', ι' h = γ) :
    ∀ γ ∈ Γ, γ • (Fin.cons y₀ fun j => e (Ξ' j) : Fin (r + 1) → V) = Fin.cons y₀ (fun j => e (Ξ' j)) →
      ∃ h ∈ Γ', (ι₀.comp ι') h = γ := by
  intro γ hγ hfix
  have hy : γ • y₀ = y₀ := by
    have := congrFun hfix 0
    simpa only [Pi.smul_apply, Fin.cons_zero] using this
  obtain ⟨h₁, hh₁, rfl⟩ := h₀ γ hγ hy
  have hΞ : h₁ • Ξ' = Ξ' := by
    funext j
    have := congrFun hfix j.succ
    simp only [Pi.smul_apply, Fin.cons_succ] at this
    rw [← he] at this
    exact he' this
  obtain ⟨h, hh, rfl⟩ := h' h₁ hh₁ hΞ
  exact ⟨h, hh, rfl⟩

end Compose

/-! ### The empty frame -/

section Base

variable {G : Type*} [Group G] [MeasurableSpace G] {V : Type*} [MulAction G V]

/-- **The coordinates of the empty frame** ($r = 0$): $T$ a point, $\mathrm{coord}(\ast, g) = g$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.base : OrbitCoord (MonoidHom.id G) (fun _ : Unit => (Fin.elim0 : Fin 0 → V)) Fin.elim0 where
  coord := MeasurableEquiv.punitProd
  mul _ _ _ := rfl
  orbit _ _ := funext fun j => j.elim0

/-- The fibration identity of the empty frame: $\mu = \mathrm{coord}_*(\delta\otimes\mu)$. -/
theorem fib_base (μ : Measure G) [SFinite μ] :
    μ = (1 : ℝ≥0∞) • ((Measure.dirac ()).prod μ).map (OrbitCoord.base (G := G) (V := V)).coord := by
  rw [one_smul, Measure.dirac_prod, Measure.map_map (OrbitCoord.base (G := G) (V := V)).coord.measurable
    measurable_prodMk_left]
  exact (Measure.map_id).symm

end Base

/-! ### Transport along an equivariant bijection -/

section Transport

variable {G H : Type*} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H] {Y Z : Type*}
  [MulAction G Y] [MulAction G Z] {T : Type*} [MeasurableSpace T] {ι : H →* G} {τ : T → Y} {y₀ : Y}

/-- **Transport of orbit coordinates** along an equivariant map $\varphi : Y\to Z$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.transport (C : OrbitCoord ι τ y₀) (φ : Y → Z) (hφ : ∀ (g : G) y, φ (g • y) = g • φ y) :
    OrbitCoord ι (φ ∘ τ) (φ y₀) where
  coord := C.coord
  mul := C.mul
  orbit x h := by rw [← hφ, C.orbit]; rfl

end Transport

/-! ### The archimedean factor -/

section Factor

variable {A B A' B' : Type*} [Group A] [Group B] [Group A'] [Group B']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']
  {YA YB : Type*} [MulAction A YA] [MulAction B YB] [MeasurableSpace YA]
  {T : Type*} [MeasurableSpace T] {ιA : A' →* A} {ιB : B' →* B} {τ : T → YA × YB} {a₀ : YA} {b₀ : YB}

/-- The stabilizer of the base point in $G$ is $\iota(H)$. -/
def StabIn (ι : A' × B' →* A × B) (y₀ : YA × YB) : Prop := ∀ g : A × B, g • y₀ = y₀ → ∃ h, ι h = g

theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.iota_smul_base (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) (h : A' × B') :
    MonoidHom.prodMap ιA ιB h • (a₀, b₀) = (a₀, b₀) := by
  obtain ⟨x⟩ : Nonempty T := ⟨(C.coord.symm 1).1⟩
  have h1 := C.orbit x 1
  have h2 := C.orbit x h⁻¹
  rw [show (h⁻¹ : A' × B') = h⁻¹ * 1 from (mul_one _).symm, C.mul, _root_.mul_inv_rev, mul_smul, ← h1] at h2
  rw [map_inv, inv_inv] at h2
  exact (smul_left_cancel _ h2)

/-- $\tau$ is injective when the stabilizer of the base point is $\iota(H)$. -/
theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.τ_injective (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) : Function.Injective τ := by
  intro x x' hxx
  have h1 := C.orbit x 1
  have h2 := C.orbit x' 1
  have hfix : (C.coord (x', 1) * (C.coord (x, 1))⁻¹) • (a₀, b₀) = (a₀, b₀) := by
    rw [mul_smul, h1, hxx, ← h2, smul_inv_smul]
  obtain ⟨h, hh⟩ := hst _ hfix
  have : C.coord (x', 1) = C.coord (x, h) := by
    rw [C.coord_eq x h, hh, inv_mul_cancel_right]
  exact (congrArg Prod.fst (C.coord.injective this)).symm

/-- The archimedean parameter space $T_A = \{y : (y, b_0)\in\tau(T)\}$. -/
def factorT (τ : T → YA × YB) (b₀ : YB) : Set YA := {y | ∃ x, τ x = (y, b₀)}

theorem τ_symm_eq (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) (a : A) :
    τ (C.coord.symm (a, 1)).1 = (a⁻¹ • a₀, b₀) := by
  rw [← C.inv_smul_eq, Prod.inv_mk, inv_one, prod_smul_def]
  simp

/-- The inverse of the archimedean coordinates, $a\mapsto(a^{-1}a_0,\ \text{the }A'\text{-part of }C^{-1}(a,1))$. -/
def factorInv (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) (a : A) : factorT τ b₀ × A' :=
  (⟨a⁻¹ • a₀, (C.coord.symm (a, 1)).1, τ_symm_eq C a⟩, (C.coord.symm (a, 1)).2.1)

theorem factorInv_injective (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) : Function.Injective (factorInv C) := by
  intro a a' haa
  have h1 : (C.coord.symm (a, 1)).1 = (C.coord.symm (a', 1)).1 := C.τ_injective hst (by
    rw [τ_symm_eq C a, τ_symm_eq C a']
    exact congrArg (fun p : factorT τ b₀ × A' => ((p.1 : YA), b₀)) haa)
  have h2 : (C.coord.symm (a, 1)).2.1 = (C.coord.symm (a', 1)).2.1 := congrArg Prod.snd haa
  have ea : ((a, 1) : A × B) = MonoidHom.prodMap ιA ιB (C.coord.symm (a, 1)).2 *
      C.coord ((C.coord.symm (a, 1)).1, 1) := by
    rw [← C.coord_eq, Prod.mk.eta, C.coord.apply_symm_apply]
  have ea' : ((a', 1) : A × B) = MonoidHom.prodMap ιA ιB (C.coord.symm (a', 1)).2 *
      C.coord ((C.coord.symm (a', 1)).1, 1) := by
    rw [← C.coord_eq, Prod.mk.eta, C.coord.apply_symm_apply]
  have ea1 : a = ιA (C.coord.symm (a, 1)).2.1 * (C.coord ((C.coord.symm (a, 1)).1, 1)).1 :=
    congrArg Prod.fst ea
  have ea1' : a' = ιA (C.coord.symm (a', 1)).2.1 * (C.coord ((C.coord.symm (a', 1)).1, 1)).1 :=
    congrArg Prod.fst ea'
  rw [ea1, ea1', h1, h2]

/-- For $(y, b_0) = \tau(x)$, the point of $A$ with archimedean coordinates $(y, h)$ is $\iota_A(h)\,C(x,1)_A$. -/
theorem factorInv_iota_mul (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) {y : YA} {x : T} (hx : τ x = (y, b₀)) (h : A') :
    factorInv C (ιA h * (C.coord (x, 1)).1) = (⟨y, x, hx⟩, h) := by
  set c := C.coord (x, 1)
  have hc : c⁻¹ • ((a₀, b₀) : YA × YB) = (y, b₀) := by rw [C.orbit]; exact hx
  have hcb : ((1 : A), c.2) • ((a₀, b₀) : YA × YB) = (a₀, b₀) := by
    have h2 : c.2⁻¹ • b₀ = b₀ := congrArg Prod.snd hc
    show ((1 : A) • a₀, c.2 • b₀) = (a₀, b₀)
    rw [one_smul]
    refine Prod.ext rfl ?_
    show c.2 • b₀ = b₀
    calc c.2 • b₀ = c.2 • (c.2⁻¹ • b₀) := by rw [h2]
      _ = b₀ := smul_inv_smul _ _
  obtain ⟨k, hk⟩ := hst _ hcb
  have hk2 : ιB k.2 = c.2 := congrArg Prod.snd hk
  have hcoord : C.coord (x, (h, k.2⁻¹)) = (ιA h * c.1, 1) := by
    rw [C.coord_eq]
    refine Prod.ext rfl ?_
    show ιB k.2⁻¹ * c.2 = 1
    rw [map_inv, hk2, inv_mul_cancel]
  have hsymm : C.coord.symm (ιA h * c.1, 1) = (x, (h, k.2⁻¹)) := by
    rw [← hcoord, C.coord.symm_apply_apply]
  refine Prod.ext (Subtype.ext ?_) ?_
  · show (ιA h * c.1)⁻¹ • a₀ = y
    have h3 := τ_symm_eq C (ιA h * c.1)
    rw [hsymm, hx] at h3
    exact (congrArg Prod.fst h3).symm
  · show (C.coord.symm (ιA h * c.1, 1)).2.1 = h
    rw [hsymm]

theorem factorInv_surjective (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) : Function.Surjective (factorInv C) := by
  rintro ⟨⟨y, x, hx⟩, h⟩
  exact ⟨_, factorInv_iota_mul C hst hx h⟩

theorem measurable_factorInv (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hmeas : Measurable fun a : A => a⁻¹ • a₀) : Measurable (factorInv C) := by
  have hs : Measurable fun a : A => C.coord.symm (a, 1) :=
    C.coord.symm.measurable.comp (measurable_id.prodMk measurable_const)
  exact (hmeas.subtype_mk).prodMk (measurable_fst.comp (measurable_snd.comp hs))

variable [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
  [MeasurableSpace.CountablySeparated (factorT τ b₀ × A')]

/-- **The archimedean coordinates** $T_A\times A'\cong A$ (inverse of `factorInv`; measurable by Lusin–Souslin). -/
def factorEquiv (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (hmeas : Measurable fun a : A => a⁻¹ • a₀) :
    factorT τ b₀ × A' ≃ᵐ A :=
  MeasurableEquiv.symm
    { toEquiv := Equiv.ofBijective (factorInv C) ⟨factorInv_injective C hst, factorInv_surjective C hst⟩
      measurable_toFun := measurable_factorInv C hmeas
      measurable_invFun := by
        have hemb := (measurable_factorInv C hmeas).measurableEmbedding (factorInv_injective C hst)
        intro S hS
        have : (Equiv.ofBijective (factorInv C) ⟨factorInv_injective C hst, factorInv_surjective C hst⟩).symm ⁻¹' S =
            factorInv C '' S := by
          ext p
          simp only [mem_preimage, mem_image]
          constructor
          · intro hp
            exact ⟨_, hp, Equiv.ofBijective_apply_symm_apply _ _ _⟩
          · rintro ⟨a, ha, rfl⟩
            convert ha; exact Equiv.ofBijective_symm_apply_apply _ _ a
        rw [this]
        exact hemb.measurableSet_image.mpr hS }

theorem factorEquiv_apply (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (hmeas : Measurable fun a : A => a⁻¹ • a₀)
    {y : YA} {x : T} (hx : τ x = (y, b₀)) (h : A') :
    factorEquiv C hst hmeas (⟨y, x, hx⟩, h) = ιA h * (C.coord (x, 1)).1 := by
  show (Equiv.ofBijective (factorInv C) ⟨factorInv_injective C hst, factorInv_surjective C hst⟩).symm _ = _
  rw [Equiv.symm_apply_eq]
  exact (factorInv_iota_mul C hst hx h).symm

/-- **The archimedean factor of orbit coordinates**: coordinates of the orbit of $a_0$ under $A$, with stabilizer
$\iota_A(A')$ and parameter space $T_A = \{y : (y, b_0)\in\tau(T)\}$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.fstFactor (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (hmeas : Measurable fun a : A => a⁻¹ • a₀) :
    OrbitCoord ιA (Subtype.val : factorT τ b₀ → YA) a₀ where
  coord := factorEquiv C hst hmeas
  mul := by
    rintro ⟨y, x, hx⟩ h h'
    rw [factorEquiv_apply C hst hmeas hx, factorEquiv_apply C hst hmeas hx, map_mul, mul_assoc]
  orbit := by
    rintro ⟨y, x, hx⟩ h
    rw [factorEquiv_apply C hst hmeas hx, _root_.mul_inv_rev, mul_smul]
    have hfix : (ιA h)⁻¹ • a₀ = a₀ := by
      have := congrArg Prod.fst (C.iota_smul_base (h⁻¹, 1))
      rw [← map_inv]
      exact this
    rw [hfix]
    have h1 : (C.coord (x, 1))⁻¹ • ((a₀, b₀) : YA × YB) = (y, b₀) := by rw [C.orbit]; exact hx
    exact congrArg Prod.fst h1

end Factor

/-! ### Conjugation to another point of the orbit -/

section Conj

variable {A H : Type*} [Group A] [Group H] [MeasurableSpace A] [MeasurableSpace H] [MeasurableMul A]
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T] {ι : H →* A} {τ : T → Y} {y₀ : Y}

/-- $h\mapsto a\,\iota(h)\,a^{-1}$, onto the stabilizer of $a\,y_0$ (if the stabilizer of $y_0$ is $\iota(H)$). -/
def conjStab (C : OrbitCoord ι τ y₀) (a : A) : H →* stabilizer A (a • y₀) where
  toFun h := ⟨a * ι h * a⁻¹, by
    obtain ⟨x⟩ : Nonempty T := ⟨(C.coord.symm 1).1⟩
    have hfix : ι h • y₀ = y₀ := by
      have h1 := C.orbit x 1
      have h2 := C.orbit x h⁻¹
      rw [show h⁻¹ = h⁻¹ * 1 from (mul_one _).symm, C.mul, _root_.mul_inv_rev, mul_smul, ← h1, map_inv,
        inv_inv] at h2
      exact smul_left_cancel _ h2
    show (a * ι h * a⁻¹) • a • y₀ = a • y₀
    rw [mul_smul, mul_smul, inv_smul_smul, hfix]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' h h' := Subtype.ext (by simp [mul_assoc])

theorem conjStab_bijective (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g) (a : A) :
    Function.Bijective (conjStab C a) := by
  refine ⟨fun h h' e => C.ι_injective ?_, fun s => ?_⟩
  · have := congrArg Subtype.val e
    simpa [conjStab] using this
  · obtain ⟨h, hh⟩ := hst (a⁻¹ * s * a) (by
      rw [mul_smul, mul_smul, s.2, inv_smul_smul])
    exact ⟨h, Subtype.ext (by simp [conjStab, hh, mul_assoc])⟩

variable [MeasurableInv A]

/-- `conjStab` as a measurable equivalence $H\simeq\operatorname{Stab}_A(a\,y_0)$ ($\iota$ a measurable embedding). -/
def conjStabME (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g) (hι : MeasurableEmbedding ι)
    (a : A) : H ≃ᵐ stabilizer A (a • y₀) where
  toEquiv := Equiv.ofBijective (conjStab C a) (conjStab_bijective C hst a)
  measurable_toFun := by
    refine Measurable.subtype_mk ?_
    exact ((measurable_const_mul a).comp hι.measurable).mul_const _
  measurable_invFun := by
    -- the inverse is $s\mapsto\iota^{-1}(a^{-1}sa)$, measurable through `hι.equivRange`
    have hrange : ∀ s : stabilizer A (a • y₀), a⁻¹ * s * a ∈ Set.range ι := fun s =>
      hst _ (by rw [mul_smul, mul_smul, s.2, inv_smul_smul])
    have hm : Measurable fun s : stabilizer A (a • y₀) => (⟨a⁻¹ * s * a, hrange s⟩ : Set.range ι) :=
      (((measurable_const_mul a⁻¹).comp measurable_subtype_coe).mul_const a).subtype_mk
    have heq : (Equiv.ofBijective (conjStab C a) (conjStab_bijective C hst a)).symm =
        fun s : stabilizer A (a • y₀) => hι.equivRange.symm ⟨a⁻¹ * s * a, hrange s⟩ := by
      funext s
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      have h1 := congrArg Subtype.val (hι.equivRange.apply_symm_apply ⟨a⁻¹ * s * a, hrange s⟩)
      simp only [MeasurableEmbedding.equivRange_apply] at h1
      show (s : A) = a * ι _ * a⁻¹
      rw [h1]; group
    rw [heq]
    exact hι.equivRange.symm.measurable.comp hm

theorem conjStabME_apply (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (a : A) (h : H) :
    ((conjStabME C hst hι a h : stabilizer A (a • y₀)) : A) = a * ι h * a⁻¹ := rfl

/-- **Orbit coordinates at $a\,y_0$**: $(x, s)\mapsto a\,C(x, \varphi^{-1}(s))$, $\varphi(h) = a\iota(h)a^{-1}$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.conj (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (a : A) : OrbitCoord (stabilizer A (a • y₀)).subtype τ (a • y₀) where
  coord := ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl T) (conjStabME C hst hι a).symm).trans C.coord).trans
    (MeasurableEquiv.mulLeft a)
  mul := by
    intro x s s'
    show a * C.coord (x, (conjStabME C hst hι a).symm (s' * s)) =
      (s' : A) * (a * C.coord (x, (conjStabME C hst hι a).symm s))
    have hmul : (conjStabME C hst hι a).symm (s' * s) =
        (conjStabME C hst hι a).symm s' * (conjStabME C hst hι a).symm s := by
      rw [MeasurableEquiv.symm_apply_eq]
      apply Subtype.ext
      show (s' : A) * s = a * ι ((conjStabME C hst hι a).symm s' * (conjStabME C hst hι a).symm s) * a⁻¹
      have e1 := congrArg Subtype.val ((conjStabME C hst hι a).apply_symm_apply s')
      have e2 := congrArg Subtype.val ((conjStabME C hst hι a).apply_symm_apply s)
      rw [conjStabME_apply] at e1 e2
      rw [map_mul, ← e1, ← e2]
      group
    rw [hmul, C.mul]
    have e1 := congrArg Subtype.val ((conjStabME C hst hι a).apply_symm_apply s')
    rw [conjStabME_apply] at e1
    conv_rhs => rw [← e1]
    group
  orbit := by
    intro x s
    show (a * C.coord (x, (conjStabME C hst hι a).symm s))⁻¹ • a • y₀ = τ x
    rw [_root_.mul_inv_rev, mul_smul, inv_smul_smul, C.orbit]

variable {σ : Measure T} [SFinite σ]

/-- Orbit coordinates at $y = a\,y_0$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.conjAt (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (a : A) {y : Y} (hy : a • y₀ = y) :
    OrbitCoord (stabilizer A y).subtype τ y := by
  subst hy; exact C.conj hst hι a

/-- The stabilizer measure at $y = a\,y_0$: $\varphi_{a*}\mu'$. -/
def stabMeasureAt (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (μ' : Measure H) (a : A) {y : Y} (hy : a • y₀ = y) :
    Measure (stabilizer A y) := by
  subst hy; exact μ'.map (conjStabME C hst hι a)

theorem sigmaFinite_stabMeasureAt (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (μ' : Measure H) [SigmaFinite μ'] (a : A) {y : Y} (hy : a • y₀ = y) :
    SigmaFinite (stabMeasureAt C hst hι μ' a hy) := by
  subst hy
  exact (conjStabME C hst hι a).sigmaFinite_map

theorem isMulLeftInvariant_stabMeasureAt (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (μ' : Measure H) [μ'.IsMulLeftInvariant] (a : A) {y : Y} (hy : a • y₀ = y) :
    (stabMeasureAt C hst hι μ' a hy).IsMulLeftInvariant := by
  subst hy
  refine ⟨fun s => ?_⟩
  show (μ'.map (conjStabME C hst hι a)).map (s * ·) = μ'.map (conjStabME C hst hι a)
  set e := conjStabME C hst hι a
  have hcomp : (fun t => s * t) ∘ e = e ∘ fun h => e.symm s * h := by
    funext h
    apply Subtype.ext
    simp only [Function.comp_apply, Subgroup.coe_mul]
    have e1 := congrArg Subtype.val (e.apply_symm_apply s)
    rw [conjStabME_apply] at e1
    rw [conjStabME_apply, conjStabME_apply, map_mul]
    conv_lhs => rw [← e1]
    group
  have hms : Measurable fun t : stabilizer A (a • y₀) => s * t :=
    Measurable.subtype_mk ((measurable_const_mul (s : A)).comp measurable_subtype_coe)
  have hg : Measurable fun h : H => e.symm s * h := by
    have : (fun h : H => e.symm s * h) = e.symm ∘ (fun t => s * t) ∘ e := by
      funext h
      apply e.injective
      show e (e.symm s * h) = e (e.symm (s * e h))
      rw [e.apply_symm_apply]
      exact (congrFun hcomp h).symm
    rw [this]
    exact e.symm.measurable.comp (hms.comp e.measurable)
  rw [Measure.map_map hms e.measurable, hcomp, ← Measure.map_map e.measurable hg, map_mul_left_eq_self]

theorem fib_conjAt [MeasurableMul₂ A] (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (μA : Measure A) [μA.IsMulLeftInvariant] (μ' : Measure H) [SFinite μ']
    (c : ℝ≥0∞) (hfib : μA = c • (σ.prod μ').map C.coord) (a : A) {y : Y} (hy : a • y₀ = y) :
    μA = c • (σ.prod (stabMeasureAt C hst hι μ' a hy)).map (C.conjAt hst hι a hy).coord := by
  subst hy
  show μA = c • (σ.prod (μ'.map (conjStabME C hst hι a))).map (C.conj hst hι a).coord
  have hp : σ.prod (μ'.map (conjStabME C hst hι a)) =
      (σ.prod μ').map (Prod.map id (conjStabME C hst hι a)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (conjStabME C hst hι a).measurable, Measure.map_id]
  have hc : (C.conj hst hι a).coord ∘ Prod.map id (conjStabME C hst hι a) = (fun g => a * g) ∘ C.coord := by
    funext ⟨t, k⟩
    simp [OrbitCoord.conj, MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
  rw [hp, Measure.map_map (C.conj hst hι a).coord.measurable
      (measurable_id.prodMap (conjStabME C hst hι a).measurable), hc,
    ← Measure.map_map (measurable_const_mul a) C.coord.measurable]
  rw [← Measure.map_smul, ← hfib, map_mul_left_eq_self]
  exact (measurable_const_mul a).aemeasurable

/-- **An archimedean fibration over the whole orbit** from orbit coordinates at one point: if
$\mu_A = c\,C_*(\sigma\otimes\mu')$ with $\mu_A$ left invariant and $\mu'$ left invariant and $\sigma$-finite, then at every
$y = a\,y_0$ ($a$ chosen) the conjugated coordinates and $\mu_{H_y} = \varphi_{a*}\mu'$ fibre $\mu_A$ with the same constant.
Constructed, not assumed. -/
def archFibrationOfCoord [MeasurableMul₂ A] (C : OrbitCoord ι τ y₀) (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g)
    (hι : MeasurableEmbedding ι) (μA : Measure A) [μA.IsMulLeftInvariant] (μ' : Measure H) [SigmaFinite μ']
    [μ'.IsMulLeftInvariant] (c : ℝ≥0∞) (hfib : μA = c • (σ.prod μ').map C.coord) :
    ArchFibration μA (Set.range fun a : A => a • y₀) σ τ c := by
  classical
  exact
  { μH := fun y => if hy : y ∈ Set.range fun a : A => a • y₀ then
        stabMeasureAt C hst hι μ' hy.choose hy.choose_spec else 0
    coord := fun y hy => C.conjAt hst hι hy.choose hy.choose_spec
    sigmaFinite := fun y => by
      by_cases hy : y ∈ Set.range fun a : A => a • y₀
      · rw [dif_pos hy]; exact sigmaFinite_stabMeasureAt C hst hι μ' _ _
      · rw [dif_neg hy]; infer_instance
    leftInv := fun y => by
      by_cases hy : y ∈ Set.range fun a : A => a • y₀
      · rw [dif_pos hy]; exact isMulLeftInvariant_stabMeasureAt C hst hι μ' _ _
      · rw [dif_neg hy]; exact ⟨fun g => by simp⟩
    fib := fun y hy => by
      rw [dif_pos hy]
      exact fib_conjAt C hst hι μA μ' c hfib _ _ }

theorem archFibrationOfCoord_μH [MeasurableMul₂ A] (C : OrbitCoord ι τ y₀)
    (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g) (hι : MeasurableEmbedding ι) (μA : Measure A)
    [μA.IsMulLeftInvariant] (μ' : Measure H) [SigmaFinite μ'] [μ'.IsMulLeftInvariant] (c : ℝ≥0∞)
    (hfib : μA = c • (σ.prod μ').map C.coord) {y : Y} (hy : y ∈ Set.range fun a : A => a • y₀) :
    (archFibrationOfCoord C hst hι μA μ' c hfib).μH y = stabMeasureAt C hst hι μ' hy.choose hy.choose_spec := by
  simp only [archFibrationOfCoord, dif_pos hy]

end Conj

end QuadFormsKB.Tamagawa.Indefinite
