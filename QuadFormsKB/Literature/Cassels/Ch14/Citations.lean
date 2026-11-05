/-
# Cassels, Chapter 14: citations for declarations elsewhere in the library

Declarations outside `Literature/Cassels/Ch14/` that state (variants of) items of Cassels' Chapter 14 (*Composition
of binary quadratic forms*, pp. 331–361) but carried no Cassels tag yet. The tags are added with
`attribute [kb …]`, so the files where the declarations live are unchanged. Each locator says how the declaration differs from Cassels' item. Most of them are for a
fundamental discriminant $D < 0$ and positive definite forms, where composition is defined through ideal classes; the
general case ($D \ne 0$ of either sign, Dirichlet's composition) is `Ch14/Group.lean`.
-/
import QuadFormsKB.Binary.GenusComposition
import QuadFormsKB.Binary.GenusDuplication
import QuadFormsKB.Binary.GenusCount
import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Binary.ClassNumberFormula
import QuadFormsKB.Binary.KroneckerChar
import QuadFormsKB.Binary.GenusCharacters

namespace QuadFormsKB

/-! ### §1: conventions and the results announced (14.r1–14.r3) -/

attribute [kb "cassels1978" "Ch. 14, §1, (1.1)–(1.3), p. 331 (primitive forms)"] BinQF.IsPrimitive
attribute [kb "cassels1978" "Ch. 14, §1, (1.4)–(1.5), p. 331 (D = b² − 4ac)"] BinQF.disc
attribute [kb "cassels1978" "Ch. 14, §1, (1.6)–(1.7), p. 331 (D ≡ 0, 1 mod 4)"] BinQF.disc_mod_four
attribute [kb "cassels1978" "Ch. 14, §1, p. 331 (equivalence means proper equivalence)"] Binary.SLEquiv
attribute [kb "cassels1978" "Ch. 14, §1, pp. 331–332 (the group of classes; D < 0 fundamental, via ideal classes)"]
  Binary.isFormClassGroup
attribute [kb "cassels1978" "Ch. 14, §1, pp. 331–332 (the group of classes, interface; D < 0 fundamental)"]
  Binary.IsFormClassGroup
attribute [kb "cassels1978" "Ch. 14, §1, p. 332 (the inverse class consists of the improperly equivalent forms; D < 0 fundamental)"]
  Binary.idealClass_conj

/-! ### §3: genera (14.r3, 14.r6, Corollary to Theorem 3.1) -/

attribute [kb "cassels1978" "Ch. 14, §1, p. 332 and §3, p. 339 (genera; D < 0 fundamental)"] Binary.slGenus
attribute [kb "cassels1978" "Ch. 14, §3, p. 339 (the genus of a class; D < 0 fundamental)"]
  Binary.IsFormClassGroup.genusOf
attribute [kb "cassels1978" "Ch. 14, §3, Cor. to Thm. 3.1, p. 339 (any two genera have the same number of classes; D < 0 fundamental, interface)"]
  Binary.IsFormClassGroup.card_classes_in_genus
attribute [kb "cassels1978" "Ch. 14, §3, Cor. to Thm. 3.1, p. 339 (any two genera have the same number of classes; D < 0 fundamental)"]
  Binary.card_classes_in_genus'
attribute [kb "cassels1978" "Ch. 14, §3, Cor. to Thm. 3.1, p. 339 (proper classes in a genus; D < 0 fundamental)"]
  Binary.card_slClasses_in_genus
attribute [kb "cassels1978" "Ch. 14, §1, pp. 332–333 (the number of genera; D < 0 fundamental)"] Binary.card_genera

/-! ### §4 and §6: ambiguous classes (14.r7, 14.r10) -/

attribute [kb "cassels1978" "Ch. 14, §4, p. 341 (classes improperly equivalent to themselves)"] Binary.exists_improper_iff
attribute [kb "cassels1978" "Ch. 14, §4, (4.1), p. 341 (ambiguous classes: 𝔆² = 𝔈 iff improperly equivalent to itself; D < 0 fundamental)"]
  Binary.sLEquiv_conj_iff
attribute [kb "cassels1978" "Ch. 14, §1, pp. 332–333, and §6, p. 345 (the number of ambiguous classes; D < 0 fundamental)"]
  Binary.card_twoTorsion
attribute [kb "cassels1978" "Ch. 14, §1, p. 332, and §6, p. 345 (squares = principal genus; D < 0 fundamental)"]
  Binary.principalGenus_eq_sq

/-! ### Notes and examples (14.r14, Ex. 1–12) -/

attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (forms and ideal classes; D < 0 fundamental)"] Binary.slClassEquiv
attribute [kb "cassels1978" "Ch. 14, Notes, p. 356 (class-number formulae, Appendix B; D > 0 fundamental)"]
  Binary.classNumberFormula_pos_fundUnit
attribute [kb "cassels1978" "Ch. 14, Ex. 2, pp. 358–359 (the Kronecker symbol as a character mod D; fundamental D)"]
  Binary.kroneckerChar
attribute [kb "cassels1978" "Ch. 14, Ex. 2 (α), p. 358 (the Kronecker symbol at odd primes p ∤ D)"] Binary.kronZ_odd_prime
attribute [kb "cassels1978" "Ch. 14, Ex. 2, pp. 358–359 (the Kronecker symbol as a product of the genus characters; fundamental D)"]
  Binary.prod_genusChar_eq_kronZ

end QuadFormsKB
