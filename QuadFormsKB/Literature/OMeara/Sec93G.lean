/-
# O'Meara §93G: the 2-adic case, and the statement of 93:29

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$; O'Meara's
*2-adic local field* (§93G, p. 276) is a dyadic local field in which $2$ is a prime element, here
`IsTwoAdic R` ($2$ irreducible in $R$) together with `[HenselianLocalRing R]` and `[Finite (ResidueField R)]`.
Indices are $0$-based: O'Meara's $L_i$, $\mathfrak n_i$ ($1 \le i \le t$) are the values at `i - 1 : Fin t`.

**Defines** (O'Meara 1963, §93G, pp. 276–277)
* `IsTwoAdic R` (p. 276): $2\mathfrak o = \mathfrak p$;
* `SameJordanInvariants` (p. 276): the Jordan invariants $t, \dim L_i, \mathfrak s_i, \mathfrak n_i$ agree;
* the statement `TwoAdicClassification` (**Theorem 93:29**, p. 277), proved in `Sec93G29Main.lean`.
-/
import QuadFormsKB.Literature.OMeara.Sec93E

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-- **2-adic local field** (O'Meara 1963, §93G, p. 276): $2\mathfrak o = \mathfrak p$, i.e. $2$ is a prime element of
the ring of integers (for example $\mathbb Q_2$). Stated for the discrete valuation ring $R$: $2$ is irreducible. -/
@[kb "omeara1963" "§93G, p. 276 (2-adic local field: 2o = p)"]
def IsTwoAdic (R : Type*) [CommRing R] : Prop := Irreducible (2 : R)

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **The same Jordan invariants** (O'Meara 1963, §93G, p. 276): Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_{t'}$ with $t = t'$ and $\dim L_i = \dim K_i$,
$\mathfrak s_i = \mathfrak sL_i = \mathfrak sK_i$, $\mathfrak n_i = \mathfrak nL_i = \mathfrak nK_i$ for every $i$.
(Over a 2-adic field the $\mathfrak n_i$ do not depend on the Jordan splitting; O'Meara calls $t, \dim L_i,
\mathfrak s_i, \mathfrak n_i$ the Jordan invariants of $L$.) -/
@[kb "omeara1963" "§93G, p. 276 (Jordan invariants t, dim L_i, s_i, n_i)"]
def SameJordanInvariants {t t' : ℕ} (Ls : Fin t → Submodule R V) (Ks : Fin t' → Submodule R V') : Prop :=
  ∃ h : t = t', ∀ i : Fin t, finrank R (Ls i) = finrank R (Ks (Fin.cast h i)) ∧
    scale Q (Ls i) = scale Q' (Ks (Fin.cast h i)) ∧ normIdeal Q (Ls i) = normIdeal Q' (Ks (Fin.cast h i))

end Defs

section Classification

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Theorem 93:29** (O'Meara 1963, §93G, p. 277), *named statement* (assumed, not proved here). Let $L$ and $K$ be
lattices on a regular quadratic space $V$ over a 2-adic local field $F$ with Jordan splittings
$L = L_1 \perp \cdots \perp L_t$, $K = K_1 \perp \cdots \perp K_t$ and the same Jordan invariants
$t, \dim L_i, \mathfrak s_i, \mathfrak n_i$, and let $L_{(1)} \subset \cdots \subset L_{(t)}$,
$K_{(1)} \subset \cdots \subset K_{(t)}$ be the Jordan chains. Then $\operatorname{cls} L = \operatorname{cls} K$ if and
only if for $1 \le i \le t - 1$:
1. $dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak n_i\mathfrak n_{i+1}/\mathfrak s_i^2$;
2. $FL_{(i)} \to FK_{(i)} \perp \langle 2^{u_i}\rangle$ when $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$, where
   $u_i = \operatorname{ord}_\mathfrak p \mathfrak n_i$ (so $2^{u_i}\mathfrak o = \mathfrak n_i$).

Indices are $0$-based: the condition for O'Meara's $i$ is stated for the pair `i`, `j` with `j = i + 1`;
$L_{(i)}$ is `jordanChain Ls i`; $\mathfrak n_i\mathfrak n_{i+1}/\mathfrak s_i^2$ is `Submodule` division;
$2^{u_i}$ is written as the power $2^u$ ($u \in \mathbb Z$) with $2^u\mathfrak o = \mathfrak n_i$ (unique since $2$ is
prime). The page image shows "$\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$" (non-strict; an earlier version of this
statement read it as strict, under which the "if" direction is false). Proved over
2-adic fields and their completions: `G29.twoAdicClassification_twoAdic`, `G29.twoAdicClassification_twoAdic_nf`. -/
@[kb "omeara1963" "§93G, 93:29, p. 277"]
structure TwoAdicClassification : Prop where
  cls_eq_iff : IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] {t : ℕ} (Ls Ks : Fin t → Submodule R V),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → SameJordanInvariants Q Q Ls Ks →
      (cls Q L = cls Q K ↔ ∀ i j : Fin t, (j : ℕ) = i + 1 →
        DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i)
          (normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i))) ∧
        (normIdeal Q (Ls j) ≤ (4 : F) • normIdeal Q (Ls i) → ∀ u : ℤ,
          R ∙ ((2 : F) ^ u) = normIdeal Q (Ls i) →
          SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) ((2 : F) ^ u)))

end Classification

end QuadFormsKB.OMeara
