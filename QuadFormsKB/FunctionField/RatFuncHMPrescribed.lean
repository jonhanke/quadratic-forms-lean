/-
# Hasse–Minkowski over $\mathbb{F}_q(t)$ with Hilbert reciprocity proved

With Hilbert reciprocity over $\mathbb{F}_q(t)$ proved (`hilbertReciprocity`, `RatFuncReciprocity.lean`), the
Hasse–Minkowski theorem over $\mathbb{F}_q(t)$, $q$ odd, is conditional only on the named input
`PrescribedHilbert k` (elements with prescribed local Hilbert symbols, O'Meara 71:19 for $\mathbb{F}_q(t)$), and only
in dimension $n = 4$.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncReciprocity
import QuadFormsKB.FunctionField.RatFuncHMAll
import QuadFormsKB.FunctionField.RatFuncPrescribed

namespace QuadFormsKB.RatFuncPlace

variable {k : Type} [Field k] [Fintype k]

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$ for $n = 4$** (O'Meara 66:1, $n = 4$, $F = \mathbb{F}_q(t)$, $q$ odd;
conditional on the named input `PrescribedHilbert k` only): a nondegenerate quaternary form over $k(t)$ is isotropic
iff it is isotropic at every place. Hilbert reciprocity is supplied by `hilbertReciprocity`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 4, F = F_q(t))"]
theorem hasseMinkowski_four_of_prescribed (hk : ringChar k ≠ 2) (hP : PrescribedHilbert k)
    (Q : QuadForm (RatFunc k) 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_four_of_global_inputs hk (hilbertReciprocity hk) hP Q hQ

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$** (O'Meara 66:1 for $F = \mathbb{F}_q(t)$, $q$ odd, every dimension;
conditional on the named input `PrescribedHilbert k`, which enters only for $n = 4$): a nondegenerate quadratic
form over $k(t)$ is isotropic over $k(t)$ iff it is isotropic over every completion of $k(t)$. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (F = F_q(t))"]
theorem hasseMinkowski_of_prescribed (hk : ringChar k ≠ 2) (hP : PrescribedHilbert k) {n : ℕ}
    (Q : QuadForm (RatFunc k) n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_of_inputs hk (hilbertReciprocity hk) hP Q hQ

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$** (O'Meara 66:1 for $F = \mathbb{F}_q(t)$, $q$ odd, every dimension;
conditional only on the named input `PrescribedSquarePrimes k`, primes with prescribed square classes, the
Chebotarev / Kornblum consequence, which enters only for $n = 4$): `PrescribedHilbert k` is supplied by
`prescribedHilbert_of_squarePrimes`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (F = F_q(t))"]
theorem hasseMinkowski_of_squarePrimes (hk : ringChar k ≠ 2) (hD : PrescribedSquarePrimes k) {n : ℕ}
    (Q : QuadForm (RatFunc k) n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_of_prescribed hk (prescribedHilbert_of_squarePrimes hk hD) Q hQ

end QuadFormsKB.RatFuncPlace
