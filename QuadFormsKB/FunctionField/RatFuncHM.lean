/-
# Hasse–Minkowski over $\mathbb{F}_q(t)$ in dimension at most 3

O'Meara 66:1 for the global field $F = k(t)$, $k$ a finite field of odd characteristic, in the binary
and ternary cases, following O'Meara's own proof (steps 2 and 3 of 66:1):

* $n = 2$ (`RatFuncPlace.hasseMinkowski_two`): $\langle a_0, a_1 \rangle$ is isotropic iff $-a_0 a_1$ is a
  square; apply the Global Square Theorem 65:15 for $k(t)$ (`RatFuncPlace.isSquare_iff_everywhere`).
  This holds for **every** field $k$ of characteristic $\ne 2$.
* $n = 3$ (`RatFuncPlace.hasseMinkowski_three`): $\langle a_0, a_1, a_2 \rangle$ is isotropic iff
  $(-a_1/a_0, -a_2/a_0) = 1$; apply the Hasse Norm Theorem 65:23 for $k(t)$
  (`RatFuncPlace.hilbert_eq_one_of_everywhere`, proved by Legendre's descent over $k[t]$).

Both are unconditional. The field-general reductions (diagonalization, isometry invariance, the binary
and ternary criteria) are those of `FieldGen`, valid in characteristic $\ne 2$.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncLegendre
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open IsDedekindDomain Polynomial

namespace QuadFormsKB.RatFuncPlace

variable {k : Type} [Field k]

/-- $2 \ne 0$ in $k(t)$ when $\operatorname{char} k \ne 2$. -/
theorem two_ne_zero_ratFunc (hk : ringChar k ≠ 2) : (2 : RatFunc k) ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have : (2 : RatFunc k) = algebraMap k (RatFunc k) 2 := (map_ofNat _ 2).symm
  rw [this, Ne, map_eq_zero_iff _ (algebraMap k (RatFunc k)).injective]
  exact h2

/-- $k(t)$ is infinite (it contains $k[t]$). -/
instance infinite_ratFunc : Infinite (RatFunc k) :=
  Infinite.of_injective (algebraMap k[X] (RatFunc k)) (IsFractionRing.injective k[X] (RatFunc k))

/-- **Hasse–Minkowski for binary forms over $k(t)$** (O'Meara 66:1, step 2, for $F = k(t)$): for any
field $k$ of characteristic $\ne 2$, a nondegenerate binary form $Q$ over $k(t)$ is isotropic over
$k(t)$ iff it is isotropic over every completion $k(t)_v$. *Proof:* diagonalize,
$Q \cong \langle a_0, a_1 \rangle$, which is isotropic over a field $K \supseteq k(t)$ iff $-a_0 a_1$ is a
square in $K$; apply `isSquare_iff_everywhere`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 2, F = k(t))"]
theorem hasseMinkowski_two (hk : ringChar k ≠ 2) (Q : QuadForm (RatFunc k) 2)
    (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [Algebra (RatFunc k) K],
      Q.IsotropicIn K ↔ IsSquare ((algebraMap (RatFunc k) K) (-(a 0 * a 1))) := by
    intro K _ _
    rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso), ea]
    exact FieldGen.isotropic_diag_two_iff K _ _ (ha 0) (ha 1)
  have kF : Q.IsotropicIn (RatFunc k) ↔ IsSquare (-(a 0 * a 1)) := by
    rw [key (RatFunc k)]; rfl
  rw [kF, isSquare_iff_everywhere]
  constructor
  · intro h v
    have := h v
    cases v with
    | finite w => exact (key _).2 this
    | infinite => exact (key _).2 this
  · intro h v
    have := h v
    cases v with
    | finite w => exact (key _).1 this
    | infinite => exact (key _).1 this

variable [Fintype k]

/-- **Hasse–Minkowski for ternary forms over $\mathbb{F}_q(t)$** (O'Meara 66:1, step 3, for
$F = \mathbb{F}_q(t)$, $q$ odd): a nondegenerate ternary form $Q$ over $k(t)$ is isotropic over $k(t)$
iff it is isotropic over every completion $k(t)_v$. *Proof:* diagonalize,
$Q \cong \langle a_0, a_1, a_2 \rangle$, which is isotropic over $K$ iff the Hilbert symbol
$(-a_1/a_0, -a_2/a_0)_K = 1$; apply the Hasse norm theorem `hilbert_eq_one_of_everywhere`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 3, F = k(t))"]
theorem hasseMinkowski_three (hk : ringChar k ≠ 2) (Q : QuadForm (RatFunc k) 3)
    (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    rw [FieldGen.isotropicIn_iff_of_isometricIn (RatFunc k)
      (FieldGen.isometricIn_of_base (RatFunc k) hiso), ea,
      FieldGen.isotropic_diag_three_iff (RatFunc k) _ _ _ (ha 0) (ha 1) (ha 2)]
    have h1 : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 1)) (ha 0)
    have h2 : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 2)) (ha 0)
    have := hilbert_eq_one_of_everywhere hk _ _ h1 h2 ?_
    · simpa using this
    intro v
    have hv := h v
    cases v with
    | finite w =>
      simp only [atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv
    | infinite =>
      simp only [atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$ for $n \le 3$** (O'Meara 66:1, $F = \mathbb{F}_q(t)$, $q$ odd,
$n \le 3$): a nondegenerate quadratic form of dimension $n \le 3$ over $k(t)$ is isotropic over $k(t)$
iff it is isotropic over every completion. For $n \le 1$ both sides are false. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (n ≤ 3, F = k(t))"]
theorem hasseMinkowski_le_three (hk : ringChar k ≠ 2) {n : ℕ} (hn : n ≤ 3)
    (Q : QuadForm (RatFunc k) n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  match n, hn, Q, hQ with
  | 2, _, Q, hQ => exact hasseMinkowski_two hk Q hQ
  | 3, _, Q, hQ => exact hasseMinkowski_three hk Q hQ
  | 0, _, Q, _ =>
    have hno : ∀ (K : Type) [Field K] [Algebra (RatFunc k) K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      obtain ⟨x, hx, _⟩ := h
      exact hx (Subsingleton.elim _ _)
    exact ⟨fun h => absurd h (hno _), fun h => absurd (h .infinite) (hno _)⟩
  | 1, _, Q, hQ =>
    obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
    have hno : ∀ (K : Type) [Field K] [Algebra (RatFunc k) K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)] at h
      obtain ⟨x, hx, hx0⟩ := h
      apply hx
      funext i
      fin_cases i
      have := ha 0
      simp [QuadForm.evalIn, QuadForm.diag] at hx0
      simpa [this] using hx0
    exact ⟨fun h => absurd h (hno _), fun h => absurd (h .infinite) (hno _)⟩

end QuadFormsKB.RatFuncPlace
