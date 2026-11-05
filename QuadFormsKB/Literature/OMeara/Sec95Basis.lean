/-
# O'Meara §95: a normalized orthogonal base of an anisotropic quaternary space over a non-dyadic field

**Setting.** $R$ is a discrete valuation ring (O'Meara's $\mathfrak o$) with fraction field $F$ (`IsFractionRing R F`),
$2 \ne 0$ in $F$, $\pi \in R$ a prime element, and $(V, Q)$ a quadratic space over $F$ with O'Meara's bilinear form
$B$ = `bil Q`.

**Defines** `S95.NormalBasis Q π`: an orthogonal base $e_0, e_1, e_2, e_3$ of $V$ with
$$Q(e_0) = a_0,\quad Q(e_1) = a_1,\quad Q(e_2) = \pi a_2,\quad Q(e_3) = \pi a_3 \qquad (a_i \in \mathfrak u).$$
This is the lattice $L = L_1 \perp L_2$ with $L_1 \cong \langle 1\rangle \perp \langle -\Delta\rangle$ and
$L_2 \cong \langle \pi\rangle \perp \langle -\pi\Delta\rangle$ of step 4 of the proof of O'Meara's 95:1 (1973
printing, p. 282), up to the units; indices are $0$-based (O'Meara's $L_1, L_2$ are spanned by $e_0, e_1$ and
$e_2, e_3$).

**Proves** `S95.NormalBasis.Q_eq`: $Q(\sum_i c_ie_i) = c_0^2a_0 + c_1^2a_1 + \pi(c_2^2a_2 + c_3^2a_3)$, and the
expansion `S95.NormalBasis.Q_repr` of $Q(z)$ in the coordinates of $z$.
-/
import QuadFormsKB.Literature.OMeara.Sec82Isom

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace S95

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- **A normalized orthogonal base** (the base of the lattice $L_1 \perp L_2$ in step 4 of the proof of O'Meara's
95:1, p. 282): an orthogonal base $e_0, \dots, e_3$ of $V$ and units $a_0, \dots, a_3$ of $R$ with
$Q(e_0) = a_0$, $Q(e_1) = a_1$, $Q(e_2) = \pi a_2$, $Q(e_3) = \pi a_3$. -/
structure NormalBasis (π : R) where
  /-- The base $e_0, e_1, e_2, e_3$. -/
  e : Basis (Fin 4) F V
  /-- The units $a_0, a_1, a_2, a_3$. -/
  a : Fin 4 → R
  /-- Each $a_i$ is a unit of $R$. -/
  unit : ∀ i, IsUnit (a i)
  /-- The base is orthogonal: $B(e_i, e_j) = 0$ for $i \ne j$. -/
  orth : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0
  /-- $Q(e_0) = a_0$. -/
  Q0 : Q (e 0) = algebraMap R F (a 0)
  /-- $Q(e_1) = a_1$. -/
  Q1 : Q (e 1) = algebraMap R F (a 1)
  /-- $Q(e_2) = \pi a_2$. -/
  Q2 : Q (e 2) = algebraMap R F (π * a 2)
  /-- $Q(e_3) = \pi a_3$. -/
  Q3 : Q (e 3) = algebraMap R F (π * a 3)

namespace NormalBasis

variable {Q} {π : R} (N : NormalBasis Q π)

/-- $Q(\sum_i c_ie_i) = \sum_i c_i^2Q(e_i)$ for the orthogonal base. -/
theorem Q_sum_e (c : Fin 4 → F) : Q (∑ i, c i • N.e i) = ∑ i, c i ^ 2 * Q (N.e i) := by
  rw [Q_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [bil_self]; ring
  · intro j _ hji
    rw [N.orth i j (Ne.symm hji)]; ring
  · simp

/-- $Q(\sum_i c_ie_i) = c_0^2a_0 + c_1^2a_1 + \pi(c_2^2a_2 + c_3^2a_3)$. -/
theorem Q_eq (c : Fin 4 → F) :
    Q (∑ i, c i • N.e i) = c 0 ^ 2 * algebraMap R F (N.a 0) + c 1 ^ 2 * algebraMap R F (N.a 1) +
      algebraMap R F π * (c 2 ^ 2 * algebraMap R F (N.a 2) + c 3 ^ 2 * algebraMap R F (N.a 3)) := by
  rw [N.Q_sum_e, Fin.sum_univ_four, N.Q0, N.Q1, N.Q2, N.Q3]
  simp only [map_mul]; ring

/-- The value $Q(z)$ in the coordinates $z = \sum_i c_ie_i$ of $z$ (`N.e.repr z`). -/
theorem Q_repr (z : V) :
    Q z = (N.e.repr z 0) ^ 2 * algebraMap R F (N.a 0) + (N.e.repr z 1) ^ 2 * algebraMap R F (N.a 1) +
      algebraMap R F π * ((N.e.repr z 2) ^ 2 * algebraMap R F (N.a 2) +
        (N.e.repr z 3) ^ 2 * algebraMap R F (N.a 3)) := by
  conv_lhs => rw [← N.e.sum_repr z]
  exact N.Q_eq _

end NormalBasis

end S95

end QuadFormsKB.OMeara
