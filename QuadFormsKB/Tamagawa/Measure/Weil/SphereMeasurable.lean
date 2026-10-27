import QuadFormsKB.Tamagawa.Measure.Weil.SphereBlock
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.LerayComplex
import QuadFormsKB.Tamagawa.Measure.LerayReal

/-!
# Measurability of the two-branch section and of maps into the orthogonal groups


* **`measurable_secP`**, **`measurable_secPInv`**: for a measurable set $\{x : b(x)\}$ the two-branch section
  $s(x)$ (`secP`) and its inverse (`secPInv`) are measurable maps $R^n\to M_n(R)$ (measurable field operations on $R$).
* **`measurable_of_val_inv`**: a map $f : X\to \mathrm{GL}_n(K)$ ($K$ second countable with its Borel $\sigma$-algebra) is
  Borel measurable as soon as $x\mapsto f(x)$ and $x\mapsto f(x)^{-1}$ are measurable as matrix-valued maps (the topology of
  $\mathrm{GL}_n(K)$ is induced by $g\mapsto (g, g^{-1})\in M_n(K)\times M_n(K)^{\mathrm{op}}$).
* **`measurable_of_inducing_comp`**: measurability into a space whose topology is induced from $\mathrm{GL}_n(K)$
  can be tested after composing with the inclusion.
* **`measurable_archSO_of`**, **`measurable_archSOC_of`**, **`measurable_orthGroup_of`**: the same criterion for maps into
  $\mathrm{SO}(Q)(\mathbb R)$, $\mathrm{SO}(Q)(\mathbb C)$ and $O(Q)(F_v)$, whose $\sigma$-algebras are Borel.
-/

open Matrix
open scoped Matrix NumberField

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

open ArchSOMeasure LerayComplex
open QuadFormsKB.Lattices
open LocalDensity

noncomputable section

section Sec

variable {R : Type*} [Field R] {n : ℕ} [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableSub₂ R]
  [MeasurableMul₂ R] [MeasurableInv R] [MeasurableSingletonClass R]
  (H : Matrix (Fin n) (Fin n) R) (D : SphereData H) {b : (Fin n → R) → Prop}

/-- **The two-branch section is measurable** when the branch set is measurable. -/
theorem measurable_secP (hb : MeasurableSet {x | b x}) : Measurable (secP H D b) := by
  classical
  have h1 : Measurable fun x : Fin n → R => refl H (x + D.x₀) * refl H D.x₀ :=
    measurable_matMul (measurable_refl_comp (measurable_id.add_const D.x₀)) measurable_const
  have h2 : Measurable fun x : Fin n → R => refl H (x - D.x₀) * refl H D.w :=
    measurable_matMul (measurable_refl_comp (measurable_id.sub_const D.x₀)) measurable_const
  exact Measurable.ite hb h1 h2

/-- **The inverse two-branch section is measurable** when the branch set is measurable. -/
theorem measurable_secPInv (hb : MeasurableSet {x | b x}) : Measurable (secPInv H D b) := by
  classical
  have h1 : Measurable fun x : Fin n → R => refl H D.x₀ * refl H (x + D.x₀) :=
    measurable_matMul measurable_const (measurable_refl_comp (measurable_id.add_const D.x₀))
  have h2 : Measurable fun x : Fin n → R => refl H D.w * refl H (x - D.x₀) :=
    measurable_matMul measurable_const (measurable_refl_comp (measurable_id.sub_const D.x₀))
  exact Measurable.ite hb h1 h2

end Sec

section GLsec

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] {n : ℕ} {X : Type*} [MeasurableSpace X]

/-- **Measurability into $\mathrm{GL}_n(K)$ (Borel) from measurability of $f$ and $f^{-1}$ as matrices.** -/
theorem measurable_of_val_inv {f : X → GL (Fin n) K}
    (h1 : Measurable fun x => ((f x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h2 : Measurable fun x => (((f x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    @Measurable X (GL (Fin n) K) _ (borel _) f := by
  let : MeasurableSpace (GL (Fin n) K) := borel _
  have : BorelSpace (GL (Fin n) K) := ⟨rfl⟩
  have : BorelSpace (Matrix (Fin n) (Fin n) K) := inferInstanceAs (BorelSpace (Fin n → Fin n → K))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → K))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : OpensMeasurableSpace (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun U hU =>
      (show MeasurableSet (MulOpposite.op ⁻¹' U) from (hU.preimage MulOpposite.continuous_op).measurableSet)⟩
  have hop : Measurable (MulOpposite.op : Matrix (Fin n) (Fin n) K → (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) :=
    fun _ h => h
  have hprod : Measurable fun x => Units.embedProduct (Matrix (Fin n) (Fin n) K) (f x) :=
    h1.prodMk (hop.comp h2)
  refine measurable_of_isOpen fun U hU => ?_
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  exact hprod hV.measurableSet

/-- **Testing measurability into a space with topology induced from $\mathrm{GL}_n(K)$** after composing
with the inclusion. -/
theorem measurable_of_inducing_comp {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {g : T → GL (Fin n) K} (hg : Topology.IsInducing g) {f : X → T}
    (hf : @Measurable X (GL (Fin n) K) _ (borel _) (g ∘ f)) : Measurable f := by
  let : MeasurableSpace (GL (Fin n) K) := borel _
  have : BorelSpace (GL (Fin n) K) := ⟨rfl⟩
  refine measurable_of_isOpen fun U hU => ?_
  rw [hg.isOpen_iff] at hU
  obtain ⟨V, hV, rfl⟩ := hU
  exact hf hV.measurableSet

end GLsec

section Concrete

variable {n : ℕ} {X : Type*} [MeasurableSpace X]

/-- **Measurability into $\mathrm{SO}(Q)(\mathbb R)$** from measurability of the matrix and its inverse. -/
theorem measurable_archSO_of {Q : QuadForm ℝ n} {f : X → ArchSO Q}
    (h1 : Measurable fun x => ((ArchSO.incl Q (f x) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ))
    (h2 : Measurable fun x => (((ArchSO.incl Q (f x))⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) :
    Measurable f := by
  have hind : Topology.IsInducing (ArchSO.incl Q) := Topology.IsInducing.subtypeVal
  exact measurable_of_inducing_comp hind
    (measurable_of_val_inv (f := fun x => ArchSO.incl Q (f x)) h1 h2)

/-- **Measurability into $\mathrm{SO}(Q)(\mathbb C)$** from measurability of the matrix and its inverse. -/
theorem measurable_archSOC_of {Q : QuadForm ℂ n} {f : X → ArchSOC Q}
    (h1 : Measurable fun x => ((ArchSOC.incl Q (f x) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    (h2 : Measurable fun x => (((ArchSOC.incl Q (f x))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) :
    Measurable f := by
  have hind : Topology.IsInducing (ArchSOC.incl Q) := Topology.IsInducing.subtypeVal
  exact measurable_of_inducing_comp hind
    (measurable_of_val_inv (f := fun x => ArchSOC.incl Q (f x)) h1 h2)

variable {F : Type} [Field F] [NumberField F]

/-- **Measurability into $O(Q)(F_v)$** from measurability of the matrix and its inverse
(for any Borel $\sigma$-algebra on $F_v$). -/
theorem measurable_orthGroup_of {Q : QuadForm F n} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    {f : X → orthGroup Q (v.adicCompletion F)}
    (h1 : Measurable fun x => (((f x : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (h2 : Measurable fun x => ((((f x : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))⁻¹ :
      GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    Measurable f :=
  measurable_of_inducing_comp
    (g := fun g : orthGroup Q (v.adicCompletion F) => (g : GL (Fin n) (v.adicCompletion F)))
    Topology.IsInducing.subtypeVal
    (measurable_of_val_inv
      (f := fun x => ((f x : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))) h1 h2)

end Concrete

end

end QuadFormsKB.Tamagawa.Measure.Weil
