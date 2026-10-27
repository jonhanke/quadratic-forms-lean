/-
# Cassels, Chapter 11: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/` that state (variants of) items of Cassels' Chapter 11 (*Spinor genera*,
pp. 197–254) but carried no Cassels tag. The tags are
added here with `attribute [kb …]`, so the files where the declarations live are unchanged.

Differences of setting, noted in each locator: the library works over a number field $F$ (Cassels: $\mathbb Q$),
with the finite adelic group `OAf` built from the full local orthogonal groups, and with O'Meara's spinor genus
`SameSpinorGenus` (rational factor in $O(V)$); Cassels' spinor genus is the *proper* spinor genus
`SameProperSpinorGenus` (rational factor in $O^+(V)$; see `Literature/Cassels/Ch11Sec1.lean`).
-/
import QuadFormsKB.Literature.OMeara.Sec102Spn
import QuadFormsKB.Literature.OMeara.Sec101D
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Lattices.SAVSA
import QuadFormsKB.Lattices.SATernaryAway
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Tamagawa.LatIndexCard
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.E8

namespace QuadFormsKB

/-! ### §1. Introduction -/

-- Lemma 1.1: classes of lattices in V are classes of forms equivalent to f over k
attribute [kb "cassels1978" "Ch. 11, Lemma 1.1, p. 197 (free lattices over 𝓞_F, wide = GL_n equivalence)"]
  Lattices.isIsometric_latOf_iff
attribute [kb "cassels1978" "Ch. 11, Lemma 1.1, p. 197 (over ℚ, positive definite: classes in the genus)"]
  Tamagawa.RatBridge.bijOn_latClass_rat

-- §1, p. 198: notation Λ_p, O(Λ), O(Λ_p)
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (notation: the localization Λ_p)"] Lattices.loc
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (notation: O(Λ); Cassels' O⁺(Λ) is O(Λ) ∩ O⁺(V))"] Lattices.autLat
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (notation: O(Λ_p); Cassels' O⁺(Λ_p) is O(Λ_p) ∩ O⁺(V_p))"]
  Lattices.locStabV

-- Theorem 1.1: local lattices glue to a unique global lattice
attribute [kb "cassels1978" "Ch. 11, Thm. 1.1, p. 198 (existence and uniqueness, given Γ^(p) = Λ_p for almost all p)"]
  Lattices.LocFamily.existsUnique_loc_eq
attribute [kb "cassels1978" "Ch. 11, Thm. 1.1, p. 198 (the lattice Γ); §2, (2.9), p. 205"] Lattices.LocFamily.glue
attribute [kb "cassels1978" "Ch. 11, §2, proof of Thm. 1.1, pp. 205–206 (Γ_p = Γ^(p))"] Lattices.LocFamily.loc_glue
attribute [kb "cassels1978" "Ch. 11, §2, p. 204 (Λ_p = Γ_p for almost all p, (2.4))"] Lattices.loc_eventually_std
attribute [kb "cassels1978" "Ch. 11, §2, proof of Thm. 1.1, p. 206 (Γ = ∩_p (Γ_p ∩ V))"] Lattices.mem_iff_forall_loc

-- Lemma 1.2: lattices of the genus as an orbit, classes as double cosets
attribute [kb "cassels1978" "Ch. 11, (1.5)–(1.9) and Lemma 1.2, p. 199 (the genus as the orbit of the adelic group)"]
  Lattices.orbit_eq_genus
attribute [kb "cassels1978" "Ch. 11, Lemma 1.2 (i), p. 199 (the stabilizer of Λ is ∏ O(Λ_p))"]
  Lattices.stabilizer_eq_locStab
attribute [kb "cassels1978" "Ch. 11, Lemma 1.2 (ii), p. 199 (variant: classes in the genus as double cosets, full O)"]
  Lattices.dosetEquivClassesInGenus

-- §1, (1.16)–(1.21): the spinor norm and its kernels
attribute [kb "cassels1978" "Ch. 11, §1, (1.16)–(1.17), p. 200 (the spinor norm θ)"] Lattices.spinorNormHom
attribute [kb "cassels1978" "Ch. 11, §1, p. 200 (Θ(V), Θ(V_p): the kernel of θ on O⁺)"] Lattices.spinorKernel
attribute [kb "cassels1978" "Ch. 11, §1, (1.18), p. 200 (θ(V) = θ(O⁺(V)))"] Lattices.spinorNormGroup
attribute [kb "cassels1978" "Ch. 11, §1, (1.21), p. 200 (θ(Λ_p))"] Lattices.localSpinorNormGroup

-- Lemma 1.4: the spinor genus (Cassels' S(Λ, Γ) is the proper spinor genus)
attribute [kb "cassels1978" "Ch. 11, (1.25)–(1.27), p. 200, and Lemma 1.4, p. 201 (the relation S: proper spinor genus)"]
  Lattices.SameProperSpinorGenus Lattices.sameProperSpinorGenus_iff
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4 (i), p. 201 (S is an equivalence relation)"]
  Lattices.SameProperSpinorGenus.refl Lattices.SameProperSpinorGenus.symm Lattices.SameProperSpinorGenus.trans
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4 (ii), p. 201 (properly equivalent lattices are in one spinor genus)"]
  Lattices.IsProperIsometric.sameProperSpinorGenus
attribute [kb "cassels1978" "Ch. 11, Lemma 1.4 (iii), p. 201 (a spinor genus lies in a genus)"]
  Lattices.SameProperSpinorGenus.sameProperGenus
attribute [kb "cassels1978" "Ch. 11, §1, p. 198 (proper equivalence Γ = αΛ, α ∈ O⁺(V))"] Lattices.IsProperIsometric

/-! ### §2. Localization of lattices -/

-- Lemma 2.1: the index is the product of the local indices
attribute [kb "cassels1978" "Ch. 11, Lemma 2.1, p. 206 (the index as a product of local indices; over 𝓞_F)"]
  Tamagawa.SiegelSpace.latIndex_mul_relIndex Tamagawa.SiegelSpace.latIndex_eq_relIndex_div

/-! ### §3. The number of spinor genera -/

-- (3.8)–(3.15) and Theorem 3.1: the group G and the principal homogeneous space
attribute [kb "cassels1978" "Ch. 11, §3, (3.8)–(3.15), pp. 208–209 (adelic form of G = R/ST: O(V)(𝔸_f)/O(V)O'(V_𝔸)O(Λ̂))"]
  Lattices.spnLocGroup
attribute [kb "cassels1978" "Ch. 11, Thm. 3.1, p. 211 (adelic form; the spinor genera in the genus ≃ the group G)"]
  Lattices.spinorGeneraEquivQuot Lattices.dosetEquivQuot
attribute [kb "cassels1978" "Ch. 11, (3.16), p. 209 (g² = 1 in G)"] Lattices.spinorGeneraQuot_mul_self
attribute [kb "cassels1978" "Ch. 11, §3, p. 209 (G is abelian)"] Lattices.spinorGeneraQuot_comm

-- Lemma 3.6, Corollary (variant: O'Meara's spinor genus, indefinite)
attribute [kb "cassels1978" "Ch. 11, Lemma 3.6, Cor., p. 213 (variant: full O, V isotropic at every infinite place)"]
  Lattices.sameSpinorGenus_of_sameGenus

/-! ### §4. An alternative approach -/

-- Lemma 4.2 (variant: an isometric lattice, not necessarily properly isometric)
attribute [kb "cassels1978" "Ch. 11, Lemma 4.2, p. 216 (variant: Γ isometric, not necessarily properly, to Λ)"]
  Lattices.exists_isometric_agree

/-! ### §8. A generalized strong approximation -/

attribute [kb "cassels1978" "Ch. 11, Lemma 8.1, p. 231 (generalization: over a number field, u = ∞)"]
  Lattices.exists_very_strong_approx
attribute [kb "cassels1978" "Ch. 11, Lemma 8.1, p. 231 (generalization: over a number field, u a finite prime)"]
  Lattices.exists_very_strong_approx_at
attribute [kb "cassels1978" "Ch. 11, Thm. 8.1, pp. 231–232 (generalization: over a number field, u a finite prime)"]
  Lattices.vecApproxAt_of_isotropicAt
attribute [kb "cassels1978" "Ch. 11, Thm. 8.2, p. 232 (generalization: over a number field, u a finite prime)"]
  Lattices.rotApproxAt_of_isotropicAt Lattices.strongApproximationSpinAt

-- Theorem 8.4, Corollary 2 (partial): one class of positive definite classically integral forms of determinant 1
-- for n ≤ 5 (Hermite's bound, not Cassels' 2-neighbour sketch); the improperly primitive form E₈ for n = 8
attribute [kb "cassels1978" "Ch. 11, Thm. 8.4, Cor. 2, p. 234 (variant: n ≤ 5, one class, via Hermite's bound)"]
  Siegel.Hermite.unimodular_posDef_equiv_one
attribute [kb "cassels1978" "Ch. 11, Thm. 8.4, Cor. 2, p. 235 (variant: the improperly primitive form of determinant 1 for n = 8 exists, E₈)"]
  Siegel.e8_det Siegel.e8_posDef

end QuadFormsKB
