/-
# Existence of a measurable fundamental domain for a discrete subgroup

**Layer:** abstract topological group and measure theory. Written for upstreaming to Mathlib: general
hypotheses, no number theory, no imports from the rest of the library.

Mathlib has `IsFundamentalDomain` and the integration API but no general existence statement (see the TODO in
`Mathlib/MeasureTheory/Group/FundamentalDomain.lean`). We prove: if `G` is a second-countable topological group and
`Γ ≤ G` is a discrete subgroup (acting by left multiplication), then there is a *measurable* set `D` such that every
`Γ`-orbit meets `D` in **exactly one point** (an exact, not merely a.e., fundamental domain). Local compactness and
the Hausdorff property are not used.

*Proof.* Discreteness gives an open `W ∋ 1` with `W ∩ Γ = {1}`; continuity of `(a, b) ↦ a b⁻¹` gives an open `V ∋ 1`
with `V V⁻¹ ⊆ W`. By second countability (Lindelöf) the open sets `V g` cover `G` by countably many `U_n = V g_n`, and
`γ U_n ∩ U_n ≠ ∅ → γ = 1` for `γ ∈ Γ`. Put `D = ⋃_n (U_n ∖ ⋃_{m<n} Γ U_m)`.
-/
import Mathlib

open MeasureTheory Set Pointwise

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A discrete subgroup admits an open symmetric `V ∋ 1` such that two points of `V` in one `Γ`-orbit coincide:
`γ x = y` with `γ ∈ Γ`, `x y ∈ V` forces `γ = 1`. -/
theorem exists_isOpen_orbit_unique (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ γ ∈ Γ, ∀ x ∈ V, ∀ y ∈ V, γ * x = y → γ = 1 := by
  obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.mp (isOpen_discrete ({(1 : Γ)} : Set Γ))
  have hW1 : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ (Subtype.val ⁻¹' W : Set Γ) := by rw [hWe]; rfl
    exact this
  have hWΓ : ∀ γ ∈ Γ, γ ∈ W → γ = 1 := fun γ hγ hγW => by
    have : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' W : Set Γ) := hγW
    rw [hWe] at this
    exact congrArg Subtype.val (mem_singleton_iff.mp this)
  obtain ⟨V, hV, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (hW.mem_nhds hW1)
  refine ⟨V ∩ V⁻¹, hV.inter hV.inv, ⟨hV1, by simpa using hV1⟩, fun γ hγ x hx y hy hxy => hWΓ γ hγ ?_⟩
  apply hVV
  refine ⟨y, hy.1, x⁻¹, hx.2, ?_⟩
  rw [← hxy]; group

/-- Open sets `u n` covering `G`, each meeting every `Γ`-orbit at most once. -/
theorem exists_seq_isOpen_orbit_unique [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ u : ℕ → Set G, (∀ n, IsOpen (u n)) ∧ (⋃ n, u n) = univ ∧
      ∀ n, ∀ γ ∈ Γ, ∀ x ∈ u n, ∀ y ∈ u n, γ * x = y → γ = 1 := by
  obtain ⟨V, hV, hV1, hVΓ⟩ := exists_isOpen_orbit_unique Γ
  let U : G → Set G := fun g => (fun y => y * g⁻¹) ⁻¹' V
  have hUo : ∀ g, IsOpen (U g) := fun g => hV.preimage (continuous_id.mul continuous_const)
  have hUg : ∀ g, U g ∈ nhds g := fun g => (hUo g).mem_nhds (by simpa [U] using hV1)
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds hUg
  have hne : s.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    subst h
    simp at hcov
    exact (empty_ne_univ hcov)
  obtain ⟨f, hf⟩ := hs.exists_eq_range hne
  refine ⟨fun n => U (f n), fun n => hUo _, ?_, fun n γ hγ x hx y hy hxy => ?_⟩
  · rw [eq_univ_iff_forall]
    intro x
    have : x ∈ ⋃ g ∈ s, U g := by rw [hcov]; trivial
    simp only [mem_iUnion] at this ⊢
    obtain ⟨g, hg, hx⟩ := this
    rw [hf] at hg
    obtain ⟨n, rfl⟩ := hg
    exact ⟨n, hx⟩
  · refine hVΓ γ hγ (x * (f n)⁻¹) hx (y * (f n)⁻¹) hy ?_
    rw [← hxy]; group

/-- **Existence of an exact measurable fundamental domain.** If `G` is a second-countable topological group with its
Borel-open σ-algebra and `Γ ≤ G` is a discrete subgroup, there is a measurable `D ⊆ G` meeting every `Γ`-orbit in
exactly one point: for every `x` there is a unique `γ : Γ` with `γ • x ∈ D`. -/
theorem exists_measurableSet_forall_existsUnique_smul_mem
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ D : Set G, MeasurableSet D ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨u, hu, hcov, hΓ⟩ := exists_seq_isOpen_orbit_unique Γ
  -- the saturation of `u m`
  let sat : ℕ → Set G := fun m => ⋃ γ ∈ Γ, (fun y => γ * y) ⁻¹' u m
  have hsat_open : ∀ m, IsOpen (sat m) := fun m =>
    isOpen_biUnion fun γ _ => (hu m).preimage (continuous_const.mul continuous_id)
  have hsat : ∀ m y, y ∈ sat m ↔ ∃ γ ∈ Γ, γ * y ∈ u m := fun m y => by simp [sat]
  let D : Set G := ⋃ n, u n \ ⋃ m ∈ Finset.range n, sat m
  have hD : MeasurableSet D := MeasurableSet.iUnion fun n =>
    (hu n).measurableSet.diff (isOpen_biUnion fun m _ => hsat_open m).measurableSet
  refine ⟨D, hD, fun x => ?_⟩
  have hD_mem : ∀ y, y ∈ D ↔ ∃ n, y ∈ u n ∧ ∀ m < n, y ∉ sat m := fun y => by
    simp [D]
  have hsat_inv : ∀ m (γ : G), γ ∈ Γ → ∀ y, y ∈ sat m → γ * y ∈ sat m := by
    intro m γ hγ y hy
    obtain ⟨δ, hδ, hδy⟩ := (hsat m y).mp hy
    exact (hsat m _).mpr ⟨δ * γ⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ), by simpa [mul_assoc] using hδy⟩
  have hex : ∃ n, x ∈ sat n := by
    have : x ∈ ⋃ n, u n := by rw [hcov]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp this
    exact ⟨n, (hsat n x).mpr ⟨1, Γ.one_mem, by simpa using hn⟩⟩
  classical
  let N := Nat.find hex
  have hN : x ∈ sat N := Nat.find_spec hex
  have hN_min : ∀ m < N, x ∉ sat m := fun m hm => Nat.find_min hex hm
  -- any point of the orbit lying in `D` lies in `u N`
  have key : ∀ γ : G, γ ∈ Γ → γ * x ∈ D → γ * x ∈ u N := by
    intro γ hγ hmem
    obtain ⟨n, hn, hnm⟩ := (hD_mem _).mp hmem
    have hxn : x ∈ sat n := (hsat n x).mpr ⟨γ, hγ, hn⟩
    have h1 : N ≤ n := Nat.find_min' hex hxn
    have h2 : n ≤ N := by
      by_contra hlt
      push_neg at hlt
      apply hnm N hlt
      obtain ⟨δ, hδ, hδx⟩ := (hsat N x).mp hN
      exact (hsat N _).mpr ⟨δ * γ⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ), by
        rw [show δ * γ⁻¹ * (γ * x) = δ * x by group]; exact hδx⟩
    have : n = N := le_antisymm h2 h1
    subst this; exact hn
  obtain ⟨γ, hγ, hγN⟩ := (hsat N x).mp hN
  refine ⟨⟨γ, hγ⟩, ?_, fun γ' hγ' => ?_⟩
  · show γ * x ∈ D
    refine (hD_mem _).mpr ⟨N, hγN, fun m hm hms => hN_min m hm ?_⟩
    have := hsat_inv m γ⁻¹ (Γ.inv_mem hγ) _ hms
    simpa using this
  · -- uniqueness
    obtain ⟨γ', hγ'Γ⟩ := γ'
    have hγ'D : γ' * x ∈ D := hγ'
    have h1 := key γ' hγ'Γ hγ'D
    have : γ' = γ := by
      have := hΓ N (γ' * γ⁻¹) (Γ.mul_mem hγ'Γ (Γ.inv_mem hγ)) (γ * x) (by
        have hγD : γ * x ∈ D := by
          refine (hD_mem _).mpr ⟨N, hγN, fun m hm hms => hN_min m hm ?_⟩
          simpa using hsat_inv m γ⁻¹ (Γ.inv_mem hγ) _ hms
        exact key γ hγ hγD) (γ' * x) h1 (by group)
      exact mul_inv_eq_one.mp this
    subst this; rfl

/-- **Existence of a fundamental domain** (Mathlib's `IsFundamentalDomain`) for a discrete subgroup of a
second-countable topological group acting by left multiplication, for every measure. -/
theorem exists_isFundamentalDomain
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) :
    ∃ D : Set G, IsFundamentalDomain Γ D μ := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_smul_mem Γ
  exact ⟨D, IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

/-- **Bridge: exact fundamental domain for a subgroup of a discrete subgroup.** If `Γ ≤ G` is discrete and `S ≤ Γ` is
any subgroup (given as `Subgroup Γ`, acting on `G` through `Γ`), there is a measurable `E ⊆ G` such that every
`x ∈ G` has exactly one `s ∈ S` with `s • x ∈ E`. (Apply `exists_measurableSet_forall_existsUnique_smul_mem` to the
image of `S` in `G`, which is discrete as a subset of `Γ`.) -/
theorem exists_measurableSet_forall_existsUnique_smul_mem_of_subgroup
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (S : Subgroup Γ) :
    ∃ E : Set G, MeasurableSet E ∧ ∀ x : G, ∃! s : S, s • x ∈ E := by
  set H : Subgroup G := S.map Γ.subtype
  have hHΓ : ∀ h : H, (h : G) ∈ Γ := by
    rintro ⟨_, ⟨s, _, rfl⟩⟩; exact s.2
  have : DiscreteTopology H :=
    DiscreteTopology.of_continuous_injective (f := fun h : H => (⟨h, hHΓ h⟩ : Γ))
      (continuous_subtype_val.subtype_mk _) fun a b hab => Subtype.ext (congrArg (fun z : Γ => (z : G)) hab)
  obtain ⟨E, hE, h⟩ := exists_measurableSet_forall_existsUnique_smul_mem H
  refine ⟨E, hE, fun x => ?_⟩
  let e : S ≃* H := S.equivMapOfInjective Γ.subtype Γ.subtype_injective
  have key : ∀ s : S, s • x = e s • x := fun _ => rfl
  obtain ⟨h₀, hh₀, huniq⟩ := h x
  refine ⟨e.symm h₀, ?_, fun s hs => ?_⟩
  · show e.symm h₀ • x ∈ E
    rw [key, MulEquiv.apply_symm_apply]; exact hh₀
  · apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact huniq _ (show e s • x ∈ E by rw [← key]; exact hs)

/-- The bridge for stabilizers, in the form `hEx` of `lintegral_orbit_unfold` / `covolume_le_tsum_orbit_integrals`:
for a discrete `Γ ≤ G` acting on a set `X` and `r ∈ X`, the stabilizer `Γ_r` (a `Subgroup Γ`) has an exact measurable
fundamental domain in `G`. -/
theorem exists_measurableSet_forall_existsUnique_stabilizer_smul_mem
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {X : Type*} [MulAction Γ X] (r : X) :
    ∃ E : Set G, MeasurableSet E ∧ ∀ y : G, ∃! s : MulAction.stabilizer Γ r, s • y ∈ E :=
  exists_measurableSet_forall_existsUnique_smul_mem_of_subgroup Γ _

instance (Γ : Subgroup G) [DiscreteTopology Γ] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) : HasFundamentalDomain Γ G μ :=
  ⟨exists_isFundamentalDomain Γ μ⟩

end QuadFormsKB.Tamagawa.Measure.Weil
