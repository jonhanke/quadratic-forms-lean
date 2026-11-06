/-
# Cassels, Chapter 5: citations for declarations elsewhere in the library

Declarations (Mathlib, Chapter 12 of the library, and proof steps of Chapter 5) that state running-text items of Cassels' Chapter 5
(*Tools from the geometry of numbers*, pp. 67–74) and carried no Cassels tag. The tags are added with `attribute [kb …]`, so the files where the declarations
live are unchanged. Each locator says how the declaration differs from Cassels' item.
-/
import Mathlib.Combinatorics.Pigeonhole
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Cassels.Ch12.Hermite
import QuadFormsKB.Literature.Cassels.Ch5.Supplement

/-! ### §2: Dirichlet's pigeonhole principle (5.r3) -/

-- 5.r3: Cassels' remark that Blichfeldt's theorem is a continuous analogue of Dirichlet's Schubfachprinzip: if
-- m > kn papers are filed in n pigeon-holes, some pigeon-hole holds at least k + 1 papers. Mathlib's finite form:
-- a map from a finset of card > k·#t into t has a fiber of card > k.
attribute [kb "cassels1978" "Ch. 5, §2, p. 68 (Dirichlet's Schubfachprinzip: m > kn papers in n pigeon-holes, some pigeon-hole holds ≥ k + 1)"]
  Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to

/-! ### §3: Hermite's bound (3.9) -/

-- (3.9): Hermite's estimate m ≤ (4/3)^{(n−1)/2} d(g)^{1/n} for the minimum m of a positive definite real form g in n
-- variables; proved in the library as Cassels' Ch. 12, Thm. 2.1 with Hermite's constant.
attribute [kb "cassels1978" "Ch. 5, §3, (3.9), p. 73 (Hermite's bound for the minimum of a positive definite form)"]
  QuadFormsKB.Reduction.hermiteConstantBound_hermite

/-! ### §2: proof of Theorem 2.1 (5.p1) -/

-- 5.p1: (2.1)–(2.3): S is cut into the pieces S(u) in the unit cubes u + W, translated back into W; the pieces have
-- total volume v(S) > k. The integral form of this decomposition: ∫_W Σ_u 1_S(x + u) dx = v(S).
attribute [kb "cassels1978" "Ch. 5, §2, proof of Thm. 2.1, (2.1)–(2.3), p. 68 (the translated pieces of S have total volume v(S); integral form)"]
  QuadFormsKB.Cassels.Ch5.blichfeldt_integral
