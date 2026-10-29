/-
# O'Meara §11H: completion of a finite extension (11:19)

**Proves** `compositum_completion` (**11:19**): for a finite extension $E/F$, a completion $E_{\mathfrak P}$ of $E$ and
a complete subfield $F_{\mathfrak P}$ containing (the image of) $F$ densely, $E_{\mathfrak P}$ is spanned over
$F_{\mathfrak P}$ by the image of $E$ (O'Meara's $E_{\mathfrak P} = E F_{\mathfrak P}$) and
$[E_{\mathfrak P} : F_{\mathfrak P}] \le [E : F]$.

**Formulation.** Instead of taking the closure of $F$ inside $E_{\mathfrak P}$ we take any complete non-trivially normed
field $K'$ ($= F_{\mathfrak P}$) with a ring map $\iota_F\colon F \to K'$, a normed $K'$-algebra $W$ ($= E_{\mathfrak P}$)
and a ring map $\iota_E\colon E \to W$ with dense range, compatible with $\iota_F$ and the algebra structures. The
closure of $F$ in $E_{\mathfrak P}$ is an instance (by 11:15 it is the completion of $F$). Special case: the valuation
of the complete field $F_{\mathfrak P}$ is non-trivial. The density of $\iota_F(F)$ in $K'$ is not needed for the proof.
Proof: the $K'$-span of the images of an $F$-basis of $E$ is finite dimensional, hence closed, and contains the dense
image of $E$.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Filter Topology

namespace QuadFormsKB.OMeara

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {K' W : Type*} [NontriviallyNormedField K'] [CompleteSpace K'] [NormedField W] [NormedAlgebra K' W]

/-- **11:19.** With $E/F$ finite, $\iota_E\colon E \to W$ a ring map with dense range into a normed algebra $W$ over a
complete non-trivially normed field $K'$, compatible with $\iota_F\colon F \to K'$ (that is,
$\iota_E(a x) = \iota_F(a)\,\iota_E(x)$ for $a \in F$): the $K'$-span of $\iota_E(E)$ is all of $W$, and
$\dim_{K'} W \le [E : F]$. -/
@[kb "omeara1963" "§11H, 11:19, p. 14"]
theorem compositum_completion (ιF : F →+* K') (ιE : E →+* W)
    (hcompat : ∀ x : F, ιE (algebraMap F E x) = algebraMap K' W (ιF x))
    (hdense : DenseRange ιE) :
    Submodule.span K' (Set.range ιE) = ⊤ ∧ Module.finrank K' W ≤ Module.finrank F E := by
  let b := Module.finBasis F E
  set S := Submodule.span K' (Set.range fun i => ιE (b i)) with hS
  have hfd : FiniteDimensional K' S := FiniteDimensional.span_of_finite K' (Set.finite_range _)
  have hmem : ∀ e : E, ιE e ∈ S := by
    intro e
    have : e = ∑ i, b.repr e i • b i := (b.sum_repr e).symm
    rw [this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul, hcompat, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed (S : Set W) := Submodule.closed_of_finiteDimensional S
  have htop : S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    have : w ∈ closure (Set.range ιE) := hdense.closure_eq ▸ Set.mem_univ w
    exact hclosed.closure_subset_iff.2 (by rintro _ ⟨e, rfl⟩; exact hmem e) this
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← htop]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨b i, rfl⟩)
  · have h1 := finrank_range_le_card (R := K') (fun i => ιE (b i))
    have h2 : Module.finrank K' W = Module.finrank K' S := by rw [htop]; simp
    rw [h2]
    simpa [hS, Set.finrank] using h1

end QuadFormsKB.OMeara
