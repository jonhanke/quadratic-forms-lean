/-
# Cassels, Chapter 11, §1: the spinor norm commutes with localization (p. 200)

Cassels (Ch. 11, §1, p. 200) notes that the injection $O^+(V) \subset O^+(V_p)$ corresponds to the natural homomorphism
$\mathbb Q^\times/(\mathbb Q^\times)^2 \to \mathbb Q_p^\times/(\mathbb Q_p^\times)^2$: the spinor norm of the image of a
rational isometry is the image of its spinor norm. Here over a number field $F$ and a finite prime $\mathfrak p$
(`v : HeightOneSpectrum (𝓞 F)`), for every isometry (proper or not) of a nondegenerate form $Q$ in $n$ variables:
`spinorNorm_orthMap` (factor $\sigma$ into symmetries by Cartan–Dieudonné, `exists_symmProd_eq`; the image of a symmetry
$\tau_x$ is $\tau_x$ over $F_\mathfrak p$; `orthMap_symmProd`, `valProd_map_locVec` of `Lattices/SACorrection.lean`).
-/
import QuadFormsKB.Lattices.SACorrection

open NumberField IsDedekindDomain Matrix

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **The spinor norm commutes with localization** (Cassels, Ch. 11, §1, p. 200: the injection
$O^+(V) \subset O^+(V_p)$ corresponds to $\mathbb Q^\times/(\mathbb Q^\times)^2 \to \mathbb Q_p^\times/(\mathbb Q_p^\times)^2$),
over a number field $F$: for a nondegenerate form $Q$ and an isometry $\sigma \in O(V)(F)$ there is $a \in F^\times$ with
$\theta(\sigma) = a\,(F^\times)^2$ and $\theta(\sigma_\mathfrak p) = a\,(F_\mathfrak p^\times)^2$, where $\sigma_\mathfrak p$ is the
image of $\sigma$ in $O(V)(F_\mathfrak p)$. Arguments: `hQ` nondegeneracy of $Q$, `v` the finite prime $\mathfrak p$,
`σ` the isometry. -/
@[kb "cassels1978" "Ch. 11, §1, p. 200 (O⁺(V) ⊂ O⁺(V_p) corresponds to ℚ^×/(ℚ^×)² → ℚ_p^×/(ℚ_p^×)²; over a number field)"]
theorem spinorNorm_orthMap (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (σ : orthGroup Q F) :
    ∃ a : F, a ≠ 0 ∧ spinorNorm Q F σ = sqClassOf a ∧
      spinorNorm Q (v.adicCompletion F) (orthMap Q (v.adicCompletion F) σ) =
        sqClassOf (algebraMap F (v.adicCompletion F) a) := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ σ
  refine ⟨valProd Q F xs, valProd_ne_zero Q F hxs, spinorNorm_symmProd Q F hQ xs hxs, ?_⟩
  have hxs' : ∀ y ∈ xs.map (locVec v), Q.evalIn (v.adicCompletion F) y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [evalIn_locVec]
    exact (map_ne_zero _).mpr (hxs x hx)
  rw [orthMap_symmProd, spinorNorm_symmProd Q _ hQ _ hxs', valProd_map_locVec]

end QuadFormsKB.Lattices
