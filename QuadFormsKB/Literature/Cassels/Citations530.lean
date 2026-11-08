import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.Local

/-!
# Cassels, *Rational Quadratic Forms*: citation tags for items the coverage audit marked "not cited"

Only `@[kb]` attributes are added here (no statement, definition or proof). The declarations formalize the items in
the library's adelic language over a number field (Cassels works over $\mathbb Q$ with the proper orthogonal group and
a finite set of primes); the locators say so.

* Ch. 11, Lemma 1.2, p. 199: $\Gamma = \beta\Lambda$ for an idele-type family $\beta = (\beta_p)$; two such lattices are
  equal iff $\beta' = \beta\eta$ with $\eta_p \in O^{+}(\Lambda_p)$ and properly equivalent iff
  $\beta'_p = \alpha\beta_p\eta_p$: the library states it as "the genus is the orbit of $O(V)(\mathbb A_f)$"
  (`Lattices.orbit_eq_genus`) and "the classes in the genus are the double cosets
  $O(V) \backslash O(V)(\mathbb A_f) / O(\hat L)$" (`Lattices.dosetEquivClassesInGenus`).
* Ch. 11, proof of Theorem 1.1, pp. 204–206 (row 11.p1 of the audit): a family of local lattices, equal to the
  localizations of one lattice at almost all $p$, is the family of localizations of a unique lattice (the gluing
  $\Gamma = \bigcap_p (V \cap \Gamma^{(p)})$): `Lattices.LocFamily.glue`, `Lattices.LocFamily.loc_glue`,
  `Lattices.mem_iff_forall_loc`.
-/

namespace QuadFormsKB

attribute [kb "cassels1978" "Ch. 11, Lemma 1.2, p. 199 (variant: the genus is one orbit of O(V)(𝔸_f); full orthogonal group, number field)"]
  Lattices.orbit_eq_genus

attribute [kb "cassels1978" "Ch. 11, Lemma 1.2, p. 199 (variant: classes in the genus = double cosets O(V)\\O(V)(𝔸_f)/O(L̂); number field)"]
  Lattices.dosetEquivClassesInGenus

attribute [kb "cassels1978" "Ch. 11, proof of Thm. 1.1, pp. 204–206 (the lattice glued from local lattices; number field)"]
  Lattices.LocFamily.glue

attribute [kb "cassels1978" "Ch. 11, proof of Thm. 1.1, pp. 204–206 (the glued lattice has the prescribed localizations)"]
  Lattices.LocFamily.loc_glue

attribute [kb "cassels1978" "Ch. 11, proof of Thm. 1.1, pp. 204–206 (Γ = ⋂_p (V ∩ Γ_p): a lattice is the intersection of its localizations)"]
  Lattices.mem_iff_forall_loc

end QuadFormsKB
