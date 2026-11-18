import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Group.Units

/-!
# Mathlib's σ-algebra on a unit group is the Borel σ-algebra

**Generic, Mathlib-only hypotheses (upstreamable).** Mathlib puts on the unit group $M^\times$ of a monoid $M$ with a
σ-algebra the pullback σ-algebra along $u\mapsto u$ (`Units.instMeasurableSpace`), while the topology of $M^\times$ is
the one induced by $u\mapsto(u, u^{-1})$ (the idele topology when $M$ is an adele ring). The two σ-algebras need not
be comparable in general, but when $M$ is Hausdorff with its Borel σ-algebra and $M^\times$ is Polish (for instance a
locally compact, second countable, Hausdorff topological group), the injective continuous map $M^\times\to M$ is a
measurable embedding (Lusin–Souslin, Mathlib's `Continuous.measurableEmbedding`), so the pullback σ-algebra is the
Borel σ-algebra of $M^\times$:

* **`polishSpace_of_locallyCompact_group`**: a locally compact, second countable, Hausdorff topological group is Polish;
* **`borelSpace_units_of_polishSpace`**: `BorelSpace Mˣ` for Mathlib's instance, if $M^\times$ is Polish;
* **`borelSpace_units`**: the same if $M^\times$ is locally compact and second countable.

This replaces the library's former global instances `MeasurableSpace Mˣ := borel Mˣ` (ideles, finite idele group,
archimedean units, local units, quaternion units), which duplicated Mathlib's instance without being definitionally
equal to it.
-/

open MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure

/-- A locally compact, second countable, Hausdorff topological group is Polish (complete for its right uniformity,
which is countably generated). -/
theorem polishSpace_of_locallyCompact_group (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] : PolishSpace G := by
  let _ := IsTopologicalGroup.rightUniformSpace G
  have : IsRightUniformGroup G := { toIsTopologicalGroup := ‹_›, uniformity_eq := rfl }
  have : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (uniformity G).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  infer_instance

/-- **Mathlib's σ-algebra on $M^\times$ is Borel when $M^\times$ is Polish**: for a Hausdorff topological monoid $M$
with its Borel σ-algebra, the pullback σ-algebra along $M^\times\to M$ (`Units.instMeasurableSpace`) is the Borel
σ-algebra of the units topology. -/
theorem borelSpace_units_of_polishSpace (M : Type*) [Monoid M] [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] [PolishSpace Mˣ] : BorelSpace Mˣ := by
  -- the Borel σ-algebra as a local instance (tried before Mathlib's global one)
  let mb : MeasurableSpace Mˣ := borel Mˣ
  have : BorelSpace Mˣ := ⟨rfl⟩
  have he : MeasurableEmbedding (Units.val : Mˣ → M) :=
    Continuous.measurableEmbedding Units.continuous_val Units.val_injective
  exact @BorelSpace.mk Mˣ _ Units.instMeasurableSpace he.comap_eq

/-- **Mathlib's σ-algebra on $M^\times$ is Borel when $M^\times$ is locally compact and second countable** ($M$ a
Hausdorff topological monoid with its Borel σ-algebra). -/
theorem borelSpace_units (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] [LocallyCompactSpace Mˣ] [SecondCountableTopology Mˣ] : BorelSpace Mˣ := by
  have : T2Space Mˣ := Units.isEmbedding_embedProduct.t2Space
  have := polishSpace_of_locallyCompact_group Mˣ
  exact borelSpace_units_of_polishSpace M

/-- **Mathlib's σ-algebra on $M^\times$ is Borel when $M$ is locally compact and second countable** ($M$ a Hausdorff
topological monoid with its Borel σ-algebra; $M^\times$ is then closed in $M\times M^{\mathrm{op}}$). -/
theorem borelSpace_units_of_secondCountable (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BorelSpace Mˣ := by
  have : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology Mˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  have : LocallyCompactSpace Mˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact borelSpace_units M

end QuadFormsKB.Tamagawa.Measure
