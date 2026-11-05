/-
# Cassels, Chapters 1–4: remaining citations
Declarations elsewhere in the library, and Mathlib facts, that state (variants of) running-text claims of
Chapters 1–4 of Cassels, *Rational Quadratic Forms* (1978), which had no citation tag yet. Library declarations get their
tag with `attribute [kb …]` (their files are unchanged); Mathlib facts get a thin comparison lemma whose proof is
the Mathlib lemma. Each locator says how the declaration differs from Cassels' claim.
-/
import QuadFormsKB.Defs.Rational
import QuadFormsKB.LocalDensity.Explicit
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.Tamagawa.Indefinite.OneClass
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup

namespace QuadFormsKB

/-! ### Chapter 1 -/

attribute [kb "cassels1978" "Ch. 1, §1, (1.11), p. 3 (the homogeneous equation f(x) = 0 is soluble: a non-trivial zero over K)"]
  QuadForm.IsotropicIn
attribute [kb "cassels1978" "Ch. 1, §1, (1.13)–(1.14), p. 3 (a primitive solution of f(x) ≡ 0 mod M, for M a prime power, from an isotropic vector over ℚ_p; variant)"]
  LocalDensity.exists_primitive_zero_mod_of_isotropicIn
attribute [kb "cassels1978" "Ch. 1, §3, p. 8 (terminology: the local fields ℚ_p, p ≤ ∞, with ℚ_∞ = ℝ; the places of ℚ)"]
  RatPlace
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (a genus of indefinite forms in n ≥ 3 variables usually has one class; variant: one proper class (double coset) under local hypotheses, over a principal ideal domain)"]
  Tamagawa.Indefinite.subsingleton_DC_of_bad
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (for a definite integral form, f(x) = c has finitely many solutions, so representability is a finite search)"]
  IntQF.PosDef.repSet_finite

/-! ### Chapter 2 -/

/-- **Cassels, Ch. 2, §1, (1.1), p. 11.** For a quadratic form $\phi$ on a module $U$ over a commutative ring in
which $2$ is invertible, with associated symmetric bilinear form $\phi(u_1, u_2)$
(`QuadraticMap.associated`), $\phi(u) = \phi(u, u)$. Comparison lemma for Mathlib's
`QuadraticMap.associated_eq_self_apply`. -/
@[kb "cassels1978" "Ch. 2, §1, (1.1), p. 11 (φ(u) = φ(u, u))"]
theorem Cassels.Ch2.associated_self {R U : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup U]
    [Module R U] (Q : QuadraticForm R U) (u : U) : QuadraticMap.associated Q u u = Q u :=
  QuadraticMap.associated_eq_self_apply R Q u

/-- **Cassels, Ch. 2, §1, p. 11.** A quadratic form satisfies (i) $\phi(\lambda u) = \lambda^2\phi(u)$ and
(ii) $\phi(u_1 + u_2) - \phi(u_1) - \phi(u_2)$ is bilinear in $u_1, u_2$ (Mathlib's definition of
`QuadraticMap`: `QuadraticMap.map_smul` and `QuadraticMap.polarBilin`). -/
@[kb "cassels1978" "Ch. 2, §1, p. 11 (a quadratic form: φ(λu) = λ²φ(u) and the polar form is bilinear)"]
theorem Cassels.Ch2.quadratic_axioms {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (Q : QuadraticForm R U) (c : R) (u v : U) :
    Q (c • u) = c ^ 2 * Q u ∧ Q (u + v) - Q u - Q v = QuadraticMap.polarBilin Q u v := by
  refine ⟨?_, rfl⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, sq]

/-- **Cassels, Ch. 2, §1, p. 13.** Orthogonality: $u \perp w$ if $\phi(u, w) = 0$; the orthogonal complement of a
subspace $W$ is the set of $u$ with $u \perp w$ for all $w \in W$ (`LinearMap.BilinForm.orthogonal`, with $\phi$
written `B`). Comparison lemma for Mathlib's `LinearMap.BilinForm.mem_orthogonal_iff`. -/
@[kb "cassels1978" "Ch. 2, §1, p. 13 (definition: u ⊥ w when φ(u, w) = 0; the orthogonal complement)"]
theorem Cassels.Ch2.mem_orthogonal_iff {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (B : LinearMap.BilinForm R U) (W : Submodule R U) (u : U) :
    u ∈ B.orthogonal W ↔ ∀ w ∈ W, B w u = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

/-! ### Chapter 3 -/

attribute [kb "cassels1978" "Ch. 3, §3, proof of Lemma 3.4, pp. 46–47 (reduction to generators of ℚ^×/(ℚ^×)²; proof route)"]
  hilbert_product_formula
attribute [kb "cassels1978" "Ch. 3, §4, proof of Lemma 4.1, pp. 47–48 (Newton's iteration; the library's step for quadratic maps over a complete discrete valuation ring; proof route)"]
  LocalDensity.DVR.newton_lift

/-! ### Chapter 4 -/

attribute [kb "cassels1978" "Ch. 4, §1, p. 55 (convention: ℚ_p is a local field, p = ∞ allowed with ℚ_∞ = ℝ)"]
  RatPlace
attribute [kb "cassels1978" "Ch. 4, §1, proof of Thm. 1.2, p. 56 (the rest is Ch. 2, Lemma 5.7: W(ℝ) is free on ⟨1⟩; proof route)"]
  Cassels.witt_real_free

end QuadFormsKB
