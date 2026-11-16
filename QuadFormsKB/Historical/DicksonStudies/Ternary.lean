/-
# Ternary forms in Dickson's *Studies in the Theory of Numbers*, ch. IX

**Library** `QuadFormsKB.Historical.DicksonStudies` (historical library, not imported by `QuadFormsKB`). 
Targets:

* (Dickson 1930, ch. IX, (32)): for a ternary form $f$ with
  symmetric matrix $A$ and adjoint form $\phi$ (matrix $\operatorname{adj} A$),
  $f(u) f(v) - (u^{T} A v)^2 = \phi(u \times v)$ (`dickson_adjoint_identity`; wrapper of
  `SmithPapers.adjoint_cross_identity`).
* (Dickson 1930, ch. IX): for every primitive
  $Z \in \mathbb Z^3$ there is a primitive $a \in \mathbb Z^3$ with $a \cdot Z = 0$ (`exists_primitive_orthogonal`).
  The the historical sources note records that Dickson's displayed choice of $a$ fails for $Z = (1, -1, 0)$; the statement holds.
* (Dickson 1930, ch. IX): an integral ternary form of odd
  determinant properly represents an integer $\equiv 1$ and one $\equiv 3 \pmod 4$
  (`dickson_odd_determinant_values`; wrapper of `SmithPapers.proper_values_one_three_mod_four`).

Conventions as in `QuadFormsKB.Historical.SmithPapers`: a ternary form is its symmetric integer matrix (Dickson's
"classic" forms $\sum a_{ij} x_i x_j$, $a_{ij} = a_{ji}$), variables 0-based. All **proved**, unconditional.
-/
import QuadFormsKB.Historical.SmithPapers.Values

namespace QuadFormsKB.Historical.DicksonStudies

open Matrix QuadFormsKB.Historical.SmithPapers

/-- **The adjoint identity** (Dickson, *Studies* (1930), ch. IX, (32)): for a ternary
form $f$ with symmetric matrix $A$ and adjoint form $\phi$, $f(u) f(v) - (u^{T} A v)^2 = \phi(u \times v)$. -/
@[kb "dickson1930" "ch. IX, (32) ([unverified locator])"]
theorem dickson_adjoint_identity (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (u v : Fin 3 → ℤ) :
    tern A u * tern A v - bil A u v ^ 2 = tern (adjugate A) (crossProduct u v) :=
  adjoint_cross_identity A hA u v

/-- **A primitive vector orthogonal to a given primitive vector** (Dickson, *Studies*
(1930), ch. IX): for every primitive $Z \in \mathbb Z^3$ there is a primitive $a \in \mathbb Z^3$ with
$a \cdot Z = 0$. -/
@[kb "dickson1930" "ch. IX ([unverified locator])"]
theorem exists_primitive_orthogonal (Z : Fin 3 → ℤ) (hZ : VecPrimitive Z) :
    ∃ a : Fin 3 → ℤ, VecPrimitive a ∧ a ⬝ᵥ Z = 0 := by
  by_cases h : Z 0 = 0 ∧ Z 1 = 0
  · refine ⟨![1, 0, 0], fun d hd => isUnit_of_dvd_one (by simpa using hd 0), ?_⟩
    simp [dotProduct, Fin.sum_univ_three, h.1]
  · have hpos : 0 < Int.gcd (Z 0) (Z 1) := by
      rw [Int.gcd_pos_iff]
      by_contra hc
      exact h (by push Not at hc; exact hc)
    obtain ⟨g, m, n, -, hmn, hm, hn⟩ := Int.exists_gcd_one' hpos
    -- Z 0 = m g, Z 1 = n g with gcd m n = 1; take a = (n, -m, 0)
    obtain ⟨s, t, hst⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hmn
    refine ⟨![n, -m, 0], fun d hd => ?_, ?_⟩
    · have h1 : d ∣ n := by simpa using hd 0
      have h2 : d ∣ -m := by simpa using hd 1
      have h3 : d ∣ m := by simpa using h2.neg_right
      exact isUnit_of_dvd_one (by
        rw [← hst]
        exact dvd_add (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h1 _))
    · simp [dotProduct, Fin.sum_univ_three, hm, hn]
      ring

/-- **Odd determinant** (Dickson, *Studies* (1930), ch. IX): an integral ternary form
of odd determinant properly represents an integer $\equiv 1$ and one $\equiv 3 \pmod 4$. -/
@[kb "dickson1930" "ch. IX ([unverified locator])"]
theorem dickson_odd_determinant_values (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (hdet : Odd A.det) :
    (∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = 1) ∧
      (∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = 3) :=
  proper_values_one_three_mod_four A hA hdet

end QuadFormsKB.Historical.DicksonStudies
