/-
# The critical numbers of the 15-Theorem and the 290-Theorem

The **15-Theorem** (Conway–Schneeberger; proof by Bhargava) concerns *classically integral*
positive definite forms (even cross coefficients, i.e. integer Gram matrix), the **290-Theorem**
(Bhargava–Hanke) *integral* ones (integer coefficients, i.e. integer-valued); `Equiv/Integral.lean`
makes the difference precise. Each says that such a form is universal iff it represents a short
list of critical numbers. This file records the two lists and proves the easy direction of the
290-Theorem; the theorems themselves are not formalized here.
-/
import QuadFormsKB.Literature.Universal.Basic

namespace QuadFormsKB

variable {n : ℕ}

/-- **The critical numbers of the 15-Theorem:** $1, 2, 3, 5, 6, 7, 10, 14, 15$. -/
def criticalFifteen : List ℤ := [1, 2, 3, 5, 6, 7, 10, 14, 15]

/-- The 29 critical numbers of the 290-Theorem. -/
def criticalTwoNinety : List ℤ :=
  [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 34, 35, 37, 42, 58,
    93, 110, 145, 203, 290]

/-- **The easy direction:** a universal form represents every critical number of the
290-Theorem (they are all positive). -/
@[kb "bhargavahanke" "Thm. 1"]
theorem represents_critical_of_universal (Q : IntQF n) (hQ : Q.Universal) :
    ∀ m ∈ criticalTwoNinety, Q.Represents m := by
  intro m hm
  apply hQ
  simp only [criticalTwoNinety, List.mem_cons, List.not_mem_nil, or_false] at hm
  omega

end QuadFormsKB
