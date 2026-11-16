/-
# Orders of a quaternion algebra as lattices in $F^4$: localization, intersection, gluing (Voight, 9.4.9, 9.5.3)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Theorem 9.4.9 (local-global dictionary
for lattices), Lemma 9.5.3 (completion of a lattice).

**Setting.** $F$ a number field, $B = (a,b)_F$ = `QuatF F a b`, $B_v$ = `QuatV v a b` for a finite place $v$. The coordinates
$x = x_0 + x_1 i + x_2 j + x_3 k \mapsto (x_0, \dots, x_3)$ identify $B \cong F^4$ and $B_v \cong F_v^4$ (`coordF`, `coordV`),
compatibly with the completion map (`coordV_complHom`). Under them the completion $\mathcal O_v$ (`QuatOrder.localOrder`) of an
$\mathbb Z_F$-submodule is the localization `Lattices.loc` of its image. This lets the library's local-global theorems for
lattices in $F^n$ (`Lattices/Local.lean`: `loc_injective`, `le_iff_forall_loc`, `LocFamily.glue`, `loc_glue`) act on orders.

**Contents (proved).**
* `mem_localOrder_iff_coord`: $y \in \mathcal O_v \iff \operatorname{coord}(y) \in \operatorname{loc}_v(\operatorname{coord}\mathcal O)$.
* `order_eq_of_localOrder_eq`, `order_le_of_localOrder_le`: orders are determined by, and inclusions of orders are tested on,
  their completions.
* `localOrder_inf`: completion commutes with intersection of orders: $(\mathcal O_1 \cap \mathcal O_2)_v = \mathcal O_{1,v} \cap \mathcal O_{2,v}$.
* `exists_order_localOrder_eq`: **gluing of orders**: a family $(\Lambda_v)$ of $\mathfrak o_v$-orders of $B_v$ that agrees with
  $\mathcal O_{0,v}$ for almost all $v$ ($\mathcal O_0$ a global order) is the family of completions of a global order.
-/
import QuadFormsKB.Literature.Voight.Wave4.LocalGlobalEichler
import QuadFormsKB.Lattices.Local
import QuadFormsKB.Tamagawa.IdealLocalGlobalNF

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave9

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

section Coordinates

/-- **Coordinates of a quaternion** $x_0 + x_1 i + x_2 j + x_3 k \mapsto (x_0, x_1, x_2, x_3)$, an $K$-linear equivalence
$(c_1, c_2)_K \cong K^4$. -/
def coordEquiv (K : Type*) [Field K] (c₁ c₂ : K) : ℍ[K, c₁, c₂] ≃ₗ[K] (Fin 4 → K) where
  toFun x := ![x.re, x.imI, x.imJ, x.imK]
  invFun c := ⟨c 0, c 1, c 2, c 3⟩
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl
  left_inv x := by rfl
  right_inv c := by ext i; fin_cases i <;> rfl

/-- $\mathbb Z_F$-submodules of $B$, with the module structure coming from the algebra structure (the one
`Subalgebra.toSubmodule` uses). -/
abbrev SubM (a b : 𝓞 F) : Type :=
  @Submodule (𝓞 F) (QuatF F a b) CommRing.toCommSemiring.toSemiring QuaternionAlgebra.instRing.toAddCommMonoid
    Algebra.toModule

/-- Coordinates on $B = (a,b)_F$. -/
abbrev coordF (a b : 𝓞 F) : QuatF F a b ≃ₗ[F] (Fin 4 → F) := coordEquiv F _ _

/-- Coordinates on $B_v = (a,b)_{F_v}$. -/
abbrev coordV (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : QuatV v a b ≃ₗ[v.adicCompletion F] (Fin 4 → v.adicCompletion F) :=
  coordEquiv _ _ _

theorem coordV_complHom (v : HeightOneSpectrum (𝓞 F)) (x : QuatF F a b) :
    coordV v a b (complHom v a b x) = locVec v (coordF a b x) := by
  ext i; fin_cases i <;> rfl

/-- The image of an $\mathbb Z_F$-submodule of $B$ in $F^4$. -/
def latOf (S : SubM a b) : Submodule (𝓞 F) (Fin 4 → F) :=
  S.map ((coordF a b : QuatF F a b →ₗ[F] Fin 4 → F).restrictScalars (𝓞 F))

theorem mem_latOf {S : SubM a b} {c : Fin 4 → F} :
    c ∈ latOf S ↔ (coordF a b).symm c ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show (coordF a b).symm (coordF a b x) ∈ S
    rw [LinearEquiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem latOf_mono {S S' : SubM a b} : latOf S ≤ latOf S' ↔ S ≤ S' := by
  constructor
  · intro h x hx
    have := mem_latOf.1 (h ⟨x, hx, rfl⟩)
    simpa using this
  · intro h c hc
    rw [mem_latOf] at hc ⊢
    exact h hc

theorem latOf_injective {S S' : SubM a b} (h : latOf S = latOf S') : S = S' :=
  le_antisymm (latOf_mono.1 h.le) (latOf_mono.1 h.ge)

theorem latOf_inf (S S' : SubM a b) : latOf (S ⊓ S') = latOf S ⊓ latOf S' := by
  ext c
  simp only [mem_latOf, Submodule.mem_inf]

theorem coe_latOf (S : SubM a b) :
    (latOf S : Set (Fin 4 → F)) = (coordF a b : QuatF F a b →ₗ[F] Fin 4 → F) '' (S : Set (QuatF F a b)) := rfl

/-- An order is a lattice in $F^4$. -/
theorem isLattice_latOf {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    (latOf (Subalgebra.toSubmodule O)).IsLattice F := by
  refine ⟨hO.fg.map _, ?_⟩
  rw [coe_latOf, ← Submodule.map_span]
  have h : Submodule.span F ((Subalgebra.toSubmodule O : SubM a b) : Set (QuatF F a b)) = ⊤ :=
    hO.span
  rw [h, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (coordF a b).surjective

end Coordinates

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The completion is the localization of the coordinate lattice**: $y \in \mathcal O_v$ iff
$\operatorname{coord}(y) \in \operatorname{loc}_v(\operatorname{coord}\mathcal O)$ (Voight 2021, Lemma 9.5.3). -/
theorem mem_localOrder_iff_coord (O : Subalgebra (𝓞 F) (QuatF F a b)) (y : QuatV v a b) :
    y ∈ localOrder (v := v) a b O ↔ coordV v a b y ∈ loc v (latOf (Subalgebra.toSubmodule O)) := by
  have hmap : Submodule.map ((coordV v a b : QuatV v a b →ₗ[Fv] Fin 4 → Fv).restrictScalars 𝔬)
      (Submodule.span 𝔬 (complHom v a b '' (O : Set (QuatF F a b)))) =
      loc v (latOf (Subalgebra.toSubmodule O)) := by
    rw [Submodule.map_span, loc]
    congr 1
    ext c
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨coordF a b x, ⟨x, hx, rfl⟩, (coordV_complHom v x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨complHom v a b x, ⟨x, hx, rfl⟩, coordV_complHom v x⟩
  rw [← hmap]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := (coordV v a b).injective hzy
    rwa [this] at hz

theorem coordV_mem_loc_iff (O : Subalgebra (𝓞 F) (QuatF F a b)) (c : Fin 4 → Fv) :
    c ∈ loc v (latOf (Subalgebra.toSubmodule O)) ↔ (coordV v a b).symm c ∈ localOrder (v := v) a b O := by
  rw [mem_localOrder_iff_coord, LinearEquiv.apply_symm_apply]

end Local

/-! ### Lattices in $F^n$: completion commutes with intersection -/

section Lat

variable {n : ℕ}

/-- **Completion commutes with intersection of lattices**: $(L_1 \cap L_2)_v = L_{1,v} \cap L_{2,v}$ (from the gluing
theorem: the family $(L_{1,w} \cap L_{2,w})_w$ glues to $L_1 \cap L_2$). -/
theorem loc_inf {L₁ L₂ : Submodule (𝓞 F) (Fin n → F)} (h₁ : L₁.IsLattice F) (h₂ : L₂.IsLattice F)
    (v : HeightOneSpectrum (𝓞 F)) : loc v (L₁ ⊓ L₂) = loc v L₁ ⊓ loc v L₂ := by
  let M : LocFamily F n :=
    { M := fun w => loc w L₁ ⊓ loc w L₂
      isLattice := fun w => by
        obtain ⟨k₁, hk₁, hk₁'⟩ := exists_local_bounds w (loc_isLattice w h₁)
        obtain ⟨k₂, hk₂, -⟩ := exists_local_bounds w (loc_isLattice w h₂)
        exact isLattice_of_bounds w (k := (max k₁ k₂ : ℕ))
          (le_inf ((ball_anti w (by push_cast; exact le_max_left _ _)).trans hk₁)
            ((ball_anti w (by push_cast; exact le_max_right _ _)).trans hk₂)) (inf_le_left.trans hk₁')
      eventually_std := by
        filter_upwards [loc_eventually_std h₁, loc_eventually_std h₂] with w hw₁ hw₂
        rw [hw₁, hw₂, inf_idem] }
  have hglue : M.glue = L₁ ⊓ L₂ := by
    ext x
    rw [LocFamily.mem_glue, Submodule.mem_inf, mem_iff_forall_loc h₁, mem_iff_forall_loc h₂, ← forall_and]
    rfl
  have := M.loc_glue v
  rw [hglue] at this
  exact this

end Lat

/-! ### Orders are determined by their completions; completion commutes with intersection -/

section Orders

theorem loc_latOf_eq_iff {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (v : HeightOneSpectrum (𝓞 F)) :
    loc v (latOf (Subalgebra.toSubmodule O)) = loc v (latOf (Subalgebra.toSubmodule O')) ↔
      localOrder (v := v) a b O = localOrder (v := v) a b O' := by
  constructor
  · intro h
    ext y
    rw [mem_localOrder_iff_coord, mem_localOrder_iff_coord, h]
  · intro h
    ext c
    rw [coordV_mem_loc_iff, coordV_mem_loc_iff, h]

/-- **Orders are determined by their completions** (Voight 2021, Theorem 9.4.9). -/
@[kb "voight2021" "Theorem 9.4.9, p. 143"]
theorem order_eq_of_localOrder_eq {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (hO' : IsOrder (𝓞 F) F O')
    (h : ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O = localOrder (v := v) a b O') :
    O = O' := by
  have := loc_injective (isLattice_latOf hO) (isLattice_latOf hO') fun v => (loc_latOf_eq_iff v).2 (h v)
  exact Subalgebra.toSubmodule_injective (latOf_injective this)

/-- **Inclusion of orders is tested locally** (Voight 2021, Theorem 9.4.9). -/
@[kb "voight2021" "Theorem 9.4.9, p. 143"]
theorem order_le_of_localOrder_le {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (hO' : IsOrder (𝓞 F) F O')
    (h : ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O ≤ localOrder (v := v) a b O') : O ≤ O' := by
  have : latOf (Subalgebra.toSubmodule O) ≤ latOf (Subalgebra.toSubmodule O') := by
    rw [le_iff_forall_loc (isLattice_latOf hO')]
    intro v c hc
    rw [coordV_mem_loc_iff] at hc ⊢
    exact h v hc
  exact latOf_mono.1 this

theorem localOrder_mono' {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (v : HeightOneSpectrum (𝓞 F)) (h : O ≤ O') :
    localOrder (v := v) a b O ≤ localOrder (v := v) a b O' :=
  Submodule.span_mono (Set.image_mono h)

/-- **Completion commutes with intersection of orders**: $(\mathcal O_1 \cap \mathcal O_2)_v = \mathcal O_{1,v} \cap \mathcal O_{2,v}$
(Voight 2021, Lemma 9.5.3 with Theorem 9.4.9). -/
@[kb "voight2021" "Lemma 9.5.3, p. 146"]
theorem localOrder_inf {O₁ O₂ : Subalgebra (𝓞 F) (QuatF F a b)} (h₁ : IsOrder (𝓞 F) F O₁) (h₂ : IsOrder (𝓞 F) F O₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    localOrder (v := v) a b (O₁ ⊓ O₂) = localOrder (v := v) a b O₁ ⊓ localOrder (v := v) a b O₂ := by
  ext y
  rw [Algebra.mem_inf, mem_localOrder_iff_coord, mem_localOrder_iff_coord, mem_localOrder_iff_coord]
  have : latOf (Subalgebra.toSubmodule (O₁ ⊓ O₂)) =
      latOf (Subalgebra.toSubmodule O₁) ⊓ latOf (Subalgebra.toSubmodule O₂) := by
    rw [← latOf_inf]; rfl
  rw [this, loc_inf (isLattice_latOf h₁) (isLattice_latOf h₂), Submodule.mem_inf]

theorem isOrder_of_isLattice_latOf {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (h : (latOf (Subalgebra.toSubmodule O)).IsLattice F) : IsOrder (𝓞 F) F O := by
  refine ⟨?_, ?_⟩
  · have hfg := h.fg.map (((coordF a b).symm : (Fin 4 → F) →ₗ[F] QuatF F a b).restrictScalars (𝓞 F))
    have heq : (Subalgebra.toSubmodule O : SubM a b) =
        Submodule.map (((coordF a b).symm : (Fin 4 → F) →ₗ[F] QuatF F a b).restrictScalars (𝓞 F))
          (latOf (Subalgebra.toSubmodule O)) := by
      ext x
      constructor
      · intro hx
        exact ⟨coordF a b x, ⟨x, hx, rfl⟩, (coordF a b).symm_apply_apply x⟩
      · rintro ⟨c, hc, rfl⟩
        exact mem_latOf.1 hc
    rw [heq]
    exact hfg
  · have hs := h.span_eq_top
    rw [eq_top_iff]
    intro x _
    have hx : coordF a b x ∈ Submodule.span F (latOf (Subalgebra.toSubmodule O) : Set (Fin 4 → F)) := by
      rw [hs]; trivial
    rw [coe_latOf, ← Submodule.map_span] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := (coordF a b).injective hzx
    rwa [this] at hz

/-- The coordinate image of an $\mathfrak o_v$-order of $B_v$. -/
def latV (v : HeightOneSpectrum (𝓞 F)) (Λ : Subalgebra (v.adicCompletionIntegers F) (QuatV v a b)) :
    Submodule (v.adicCompletionIntegers F) (Fin 4 → v.adicCompletion F) :=
  Submodule.map ((coordV v a b : QuatV v a b →ₗ[v.adicCompletion F] Fin 4 → v.adicCompletion F).restrictScalars
    (v.adicCompletionIntegers F)) (Subalgebra.toSubmodule Λ)

theorem mem_latV {v : HeightOneSpectrum (𝓞 F)} {Λ : Subalgebra (v.adicCompletionIntegers F) (QuatV v a b)}
    {c : Fin 4 → v.adicCompletion F} : c ∈ latV v Λ ↔ (coordV v a b).symm c ∈ Λ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (coordV v a b).symm (coordV v a b y) ∈ Λ
    rw [LinearEquiv.symm_apply_apply]
    exact hy
  · intro h
    exact ⟨_, h, (coordV v a b).apply_symm_apply c⟩

theorem isLattice_latV {v : HeightOneSpectrum (𝓞 F)} {Λ : Subalgebra (v.adicCompletionIntegers F) (QuatV v a b)}
    (h : IsOrder (v.adicCompletionIntegers F) (v.adicCompletion F) Λ) :
    (latV v Λ).IsLattice (v.adicCompletion F) := by
  refine ⟨h.fg.map _, ?_⟩
  have h2 : Submodule.span (v.adicCompletion F) ((Subalgebra.toSubmodule Λ : Submodule _ _) : Set (QuatV v a b)) = ⊤ :=
    h.span
  have : ((latV v Λ : Submodule (v.adicCompletionIntegers F) _) : Set (Fin 4 → v.adicCompletion F)) =
      (coordV v a b : QuatV v a b →ₗ[v.adicCompletion F] Fin 4 → v.adicCompletion F) ''
        ((Subalgebra.toSubmodule Λ : Submodule _ _) : Set (QuatV v a b)) := rfl
  rw [this, ← Submodule.map_span, h2, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (coordV v a b).surjective

/-- **Gluing of orders** (Voight 2021, Theorem 9.4.9, existence): a family $(\Lambda_v)$ of $\mathfrak o_v$-orders of $B_v$
that equals the completion of a fixed global order $\mathcal O_0$ at almost all places is the family of completions of a
global order $\mathcal O$. -/
@[kb "voight2021" "Theorem 9.4.9, p. 143"]
theorem exists_order_localOrder_eq {O₀ : Subalgebra (𝓞 F) (QuatF F a b)} (h₀ : IsOrder (𝓞 F) F O₀)
    (Λ : ∀ v : HeightOneSpectrum (𝓞 F), Subalgebra (v.adicCompletionIntegers F) (QuatV v a b))
    (hΛ : ∀ v, IsOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (Λ v))
    (hev : ∀ᶠ v in Filter.cofinite, Λ v = localOrder (v := v) a b O₀) :
    ∃ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O ∧
      ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O = Λ v := by
  classical
  let M : LocFamily F 4 :=
    { M := fun w => latV w (Λ w)
      isLattice := fun w => isLattice_latV (hΛ w)
      eventually_std := by
        filter_upwards [hev, loc_eventually_std (isLattice_latOf h₀)] with w hw hstd
        rw [← hstd]
        ext c
        rw [mem_latV, hw, coordV_mem_loc_iff] }
  let O : Subalgebra (𝓞 F) (QuatF F a b) :=
    { carrier := {x | ∀ w, complHom w a b x ∈ Λ w}
      mul_mem' := fun hx hy w => by rw [map_mul]; exact (Λ w).mul_mem (hx w) (hy w)
      add_mem' := fun hx hy w => by rw [map_add]; exact (Λ w).add_mem (hx w) (hy w)
      one_mem' := fun w => by rw [map_one]; exact (Λ w).one_mem
      zero_mem' := fun w => by rw [map_zero]; exact (Λ w).zero_mem
      algebraMap_mem' := fun r w => by rw [Gen.complHom_algebraMap]; exact (Λ w).algebraMap_mem _ }
  have hlat : latOf (Subalgebra.toSubmodule O) = M.glue := by
    ext c
    rw [mem_latOf, LocFamily.mem_glue]
    refine forall_congr' fun w => ?_
    have : locVec w c = coordV w a b (complHom w a b ((coordF a b).symm c)) := by
      rw [coordV_complHom]; simp
    show complHom w a b ((coordF a b).symm c) ∈ Λ w ↔ locVec w c ∈ latV w (Λ w)
    rw [mem_latV, this, LinearEquiv.symm_apply_apply]
  have hO : IsOrder (𝓞 F) F O := isOrder_of_isLattice_latOf (hlat ▸ M.glue_isLattice)
  refine ⟨O, hO, fun w => ?_⟩
  ext y
  rw [mem_localOrder_iff_coord, hlat, M.loc_glue]
  show coordV w a b y ∈ latV w (Λ w) ↔ _
  rw [mem_latV, LinearEquiv.symm_apply_apply]

end Orders

end QuadFormsKB.Voight.Wave9
