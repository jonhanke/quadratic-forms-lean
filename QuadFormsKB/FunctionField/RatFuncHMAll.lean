/-
# Hasse–Minkowski over $\mathbb{F}_q(t)$ in every dimension

Assembly of the cases for $F = k(t)$, $k$ a finite field of odd characteristic:

* $n \le 3$: `hasseMinkowski_le_three` (unconditional; Legendre's descent in $k[t]$);
* $n = 4$: `hasseMinkowski_four_of_inputs` (Serre's route; conditional on the named inputs
  `HilbertReciprocity` and `PrescribedHilbert`; the local input `LocalHilbertMul` is proved in
  `RatFuncLocal.lean`);
* $n \ge 5$: both sides hold for every form (`isotropic_of_five_le`, Tsen–Lang), so the equivalence is
  unconditional and needs no nondegeneracy.

O'Meara 66:1 is stated for global fields in general; over a number field the case $n \ge 5$ comes from
66:2 via the local theory, while over $k(t)$ the global statement itself is the elementary
Chevalley–Warning argument.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncLocal
import QuadFormsKB.FunctionField.RatFuncTsen

namespace QuadFormsKB.RatFuncPlace

variable {k : Type} [Field k] [Fintype k]

omit [Fintype k] in
/-- Isotropy goes up from $k(t)$ to any extension field, in every characteristic (the proof of
`FieldGen.isotropicIn_of_base`, which carries a `NeZero 2` section hypothesis it does not use). -/
theorem isotropicIn_of_ratFunc {n : ℕ} (K : Type) [Field K] [Algebra (RatFunc k) K]
    (Q : QuadForm (RatFunc k) n) (h : Q.IsotropicIn (RatFunc k)) : Q.IsotropicIn K := by
  obtain ⟨x, hx, hQ⟩ := h
  refine ⟨fun i => algebraMap (RatFunc k) K (x i), ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    simpa using congrFun h0 i
  · have : QuadForm.evalIn K Q (fun i => algebraMap (RatFunc k) K (x i)) =
        algebraMap (RatFunc k) K (QuadForm.evalIn (RatFunc k) Q x) := by
      unfold QuadForm.evalIn
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [this, hQ, map_zero]

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$ for $n \ge 5$** (unconditional, no nondegeneracy needed):
a quadratic form in $n \ge 5$ variables over $k(t)$ is isotropic over $k(t)$ iff it is isotropic at
every place, because both sides always hold (Tsen–Lang, `isotropic_of_five_le`). -/
@[kb "omeara1963" "§66, 66:1 and 66:2, pp. 187–188 (n ≥ 5, F = F_q(t))"]
theorem hasseMinkowski_five_le {n : ℕ} (hn : 5 ≤ n) (Q : QuadForm (RatFunc k) n) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  have hQ := isotropic_of_five_le hn Q
  refine ⟨fun _ v => ?_, fun _ => hQ⟩
  cases v with
  | finite w => exact isotropicIn_of_ratFunc _ _ hQ
  | infinite => exact isotropicIn_of_ratFunc _ _ hQ

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$, $n \ne 4$** (O'Meara 66:1 for $F = \mathbb{F}_q(t)$,
$q$ odd, every dimension except $4$; unconditional): a nondegenerate quadratic form $Q$ of dimension
$n \ne 4$ over $k(t)$ is isotropic over $k(t)$ iff it is isotropic over every completion of $k(t)$. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (n ≠ 4, F = F_q(t))"]
theorem hasseMinkowski_ne_four (hk : ringChar k ≠ 2) {n : ℕ} (hn : n ≠ 4)
    (Q : QuadForm (RatFunc k) n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  rcases Nat.lt_or_ge n 4 with h | h
  · exact hasseMinkowski_le_three hk (by omega) Q hQ
  · exact hasseMinkowski_five_le (by omega) Q

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$ for $n = 4$** (O'Meara 66:1, $n = 4$,
$F = \mathbb{F}_q(t)$, $q$ odd; conditional on the named global inputs `HilbertReciprocity` and
`PrescribedHilbert`): `hasseMinkowski_four_of_inputs` with the local input `LocalHilbertMul` supplied by
`localHilbertMul` (proved, `RatFuncLocal.lean`). -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 4, F = F_q(t))"]
theorem hasseMinkowski_four_of_global_inputs (hk : ringChar k ≠ 2) (hR : HilbertReciprocity k)
    (hP : PrescribedHilbert k) (Q : QuadForm (RatFunc k) 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_four_of_inputs hk hR hP (localHilbertMul hk) Q hQ

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$** (O'Meara 66:1 for $F = \mathbb{F}_q(t)$, $q$ odd, every
dimension; conditional on the named global inputs `HilbertReciprocity` and `PrescribedHilbert`, which
enter only for $n = 4$): a nondegenerate quadratic form over $k(t)$ is isotropic over $k(t)$ iff it is
isotropic over every completion of $k(t)$. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (F = F_q(t))"]
theorem hasseMinkowski_of_inputs (hk : ringChar k ≠ 2) (hR : HilbertReciprocity k)
    (hP : PrescribedHilbert k) {n : ℕ}
    (Q : QuadForm (RatFunc k) n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  by_cases hn : n = 4
  · subst hn
    exact hasseMinkowski_four_of_global_inputs hk hR hP Q hQ
  · exact hasseMinkowski_ne_four hk hn Q hQ

end QuadFormsKB.RatFuncPlace
