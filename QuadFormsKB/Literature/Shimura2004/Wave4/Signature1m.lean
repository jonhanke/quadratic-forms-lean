/-
# Shimura 2004, §14.4–Theorem 14.7: the action $\alpha(x) = (ax+b)(cx+d)^{-1}$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter IV, §14.4 ((14.4)–(14.7)),
§14.6 ((14.8), (14.9)) and Theorem 14.7 (printed pp. 141–143). Page numbers in the tags are printed pages.

**Setting and dictionary.** Shimura fixes $\kappa, \iota \in V$ with $\kappa^2 = 1$, $\iota^2 = -1$,
$\kappa\iota + \iota\kappa = 0$ and puts $e = (\kappa + \iota)/2$, $f = (\kappa - \iota)/2$; equivalently (as here) a
weak Witt decomposition $V = U + Fe + Ff$ (`Q e = 0`, `Q f = 0`, `polar Q e f = 1`) with $\kappa = e + f$ and
$\iota = e - f$ (written `e - f`; `ι` is Mathlib's map $V \to A(V)$). $W = (F\kappa)^\perp$ is `wSpace Q e f`
(`Wave4/Phi.lean`), $\Psi$ is `psi` (`Wave4/MatrixModel.lean`) and its entries in $A(U)$ are mapped into $A(V)$ by
`incl`. All algebraic statements below hold over every field $F$ of characteristic $\ne 2$; Theorem 14.7 itself is for
$F = \mathbb R$ and $\varphi$ of signature $(1, m)$, $m > 1$.

**Defines**
* (14.6a) $\bar x = \iota x\iota$ (`barW`) and $\eta(x) = -(\iota x + x\iota)/2 = -\varphi(\iota, x)$ (`etaW`), a scalar;
* (14.6b) $H = \{x \in W : \eta(x) > 0\}$, $H' = \{x \in W : \eta(x) < 0\}$ (`upperH`, `lowerH`; over $\mathbb R$);
* (14.8) for $\alpha \in A(V)$ with $\Psi(\alpha)$ having rows $(a, b)$, $(c, d)$ and $x \in A(V)$:
  $\lambda(\alpha, x) = cx + d$ (`lamA`) and $\alpha(x) = (ax + b)(cx + d)^{-1}$ (`actA`, with `Ring.inverse`, so it
  is Shimura's $\alpha(x)$ whenever $cx + d$ is invertible).

**Proves** (unconditional; standard axioms only)
* (14.6a) $\eta(x)$ is the scalar $-(\iota x + x\iota)/2$ (`algebraMap_etaW`) and (14.7) $2\eta(x)\iota = x - \bar x$
  for $x \in W$ (`formula_14_7`);
* (14.9): $\Psi(\alpha)\,{}^t(x, 1) = {}^t(\alpha(x), 1)\,\lambda(\alpha, x)$ whenever $\lambda(\alpha, x)$ is invertible
  (`formula_14_9`);
* Theorem 14.7 (2) $\lambda(\beta\alpha, x) = \lambda(\beta, \alpha(x))\lambda(\alpha, x)$ and (1)
  $(\beta\alpha)(x) = \beta(\alpha(x))$, for every $\alpha, \beta \in A(V)$ for which
  the $\lambda$'s involved are invertible (`theorem_14_7_2`, `theorem_14_7_1`). These are the parts of the proof of
  Theorem 14.7 that follow from (14.9) alone.

**Stated** (named proposition, not proved here): `Theorem14_7`, the main assertions of Theorem 14.7: for
$\alpha \in G^\pm(V)$ and $x \in H \cup H'$, $\lambda(\alpha, x)$ is invertible and lies in $G^\pm(W)$, $\alpha(x) \in
H \cup H'$, and $\alpha$ preserves or exchanges $H$ and $H'$ according as $\mu(\alpha) > 0$ or $< 0$. Shimura's proof
uses Lemma 14.5 (a parametrization of the set $Y$ of second columns of $\Psi(G^0(V))$) and the signature argument
(14.5); neither is formalized yet.
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.Phi
import QuadFormsKB.Literature.Shimura2004.Wave3.SubspaceGroup
import QuadFormsKB.Literature.Shimura2004.Wave3.TubeDomain
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

section Algebraic

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

local notation "A" => CliffordAlgebra Q

variable (Q e f) in
/-- **Shimura's $\eta(x)$** (14.6a), p. 141: $\eta(x) = -(\iota x + x\iota)/2$, i.e. $-\varphi(\iota, x)$ with
$\iota = e - f$ (here $2\varphi$ = `polar Q`). -/
@[kb "shimura2004" "(14.6a), p. 141 (η(x) = −(ιx + xι)/2)"]
def etaW (x : V) : F := -(⅟2 * QuadraticMap.polar Q (e - f) x)

variable (Q e f) in
/-- **Shimura's $\bar x$** (14.6a), p. 141: $\bar x = \iota x \iota$. -/
@[kb "shimura2004" "(14.6a), p. 141 (x̄ = ιxι)"]
def barW (x : V) : A := ι Q (e - f) * ι Q x * ι Q (e - f)

/-- (14.6a): $\eta(x)$ is the scalar $-(\iota x + x\iota)/2$. -/
theorem algebraMap_etaW (x : V) :
    algebraMap F A (etaW Q e f x) = -(⅟2 : F) • (ι Q (e - f) * ι Q x + ι Q x * ι Q (e - f)) := by
  rw [ι_mul_ι_add_swap, etaW, map_neg, map_mul, neg_smul, Algebra.smul_def]

/-- **(14.7)**, p. 141: $2\eta(x)\iota = x - \bar x$ for $x \in W$ (with $\iota^2 = -1$). -/
@[kb "shimura2004" "(14.7), p. 141 (2η(x)ι = x − x̄)"]
theorem formula_14_7 (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (x : V) :
    algebraMap F A (2 * etaW Q e f x) * ι Q (e - f) = ι Q x - barW Q e f x := by
  have hsq : ι Q (e - f) * ι Q (e - f) = -1 := by
    rw [ι_sq_scalar, Q_ell he hf hef, map_neg, map_one]
  have hsw : ι Q (e - f) * ι Q x + ι Q x * ι Q (e - f) =
      algebraMap F A (QuadraticMap.polar Q (e - f) x) := ι_mul_ι_add_swap _ _
  have h2 : (2 : F) * etaW Q e f x = -QuadraticMap.polar Q (e - f) x := by
    rw [etaW, mul_neg, ← mul_assoc, mul_invOf_self, one_mul]
  rw [h2, map_neg, ← hsw, barW]
  calc -(ι Q (e - f) * ι Q x + ι Q x * ι Q (e - f)) * ι Q (e - f)
      = -(ι Q (e - f) * ι Q x * ι Q (e - f)) - ι Q x * (ι Q (e - f) * ι Q (e - f)) := by noncomm_ring
    _ = _ := by rw [hsq]; noncomm_ring

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)

/-- **Shimura's $\lambda(\alpha, x) = cx + d$** (14.8), p. 142, for $\Psi(\alpha)$ with rows $(a, b)$, $(c, d)$
(entries mapped into $A(V)$). -/
@[kb "shimura2004" "(14.8), p. 142 (λ(α, x) = cx + d)"]
def lamA (α X : A) : A := incl Q e f (psi he hf hef α 1 0) * X + incl Q e f (psi he hf hef α 1 1)

/-- The numerator $ax + b$ of (14.8). -/
def numA (α X : A) : A := incl Q e f (psi he hf hef α 0 0) * X + incl Q e f (psi he hf hef α 0 1)

/-- **Shimura's $\alpha(x) = (ax + b)(cx + d)^{-1}$** (14.8), p. 142 (`Ring.inverse`, so this is Shimura's
$\alpha(x)$ whenever $cx + d$ is invertible). -/
@[kb "shimura2004" "(14.8), p. 142 (α(x) = (ax + b)(cx + d)⁻¹)"]
def actA (α X : A) : A := numA he hf hef α X * Ring.inverse (lamA he hf hef α X)

/-- **(14.9)**, p. 142: $\Psi(\alpha)\,{}^t(x, 1) = {}^t(\alpha(x), 1)\,\lambda(\alpha, x)$ when $\lambda(\alpha, x)$
is invertible: the first rows give $ax + b = \alpha(x)\lambda(\alpha, x)$ (the second rows agree by definition). -/
@[kb "shimura2004" "(14.9), p. 142 (Ψ(α)ᵗ(x, 1) = ᵗ(α(x), 1)λ(α, x))"]
theorem formula_14_9 (α X : A) (h : IsUnit (lamA he hf hef α X)) :
    numA he hf hef α X = actA he hf hef α X * lamA he hf hef α X := by
  rw [actA, mul_assoc, Ring.inverse_mul_cancel _ h, mul_one]

theorem psi_mul_entries (β α : A) (i : Fin 2) (j : Fin 2) :
    psi he hf hef (β * α) i j = psi he hf hef β i 0 * psi he hf hef α 0 j +
      psi he hf hef β i 1 * psi he hf hef α 1 j := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem lamA_mul (β α X : A) :
    lamA he hf hef (β * α) X = incl Q e f (psi he hf hef β 1 0) * numA he hf hef α X +
      incl Q e f (psi he hf hef β 1 1) * lamA he hf hef α X := by
  simp only [lamA, numA, psi_mul_entries, map_add, map_mul]
  noncomm_ring

theorem numA_mul (β α X : A) :
    numA he hf hef (β * α) X = incl Q e f (psi he hf hef β 0 0) * numA he hf hef α X +
      incl Q e f (psi he hf hef β 0 1) * lamA he hf hef α X := by
  simp only [lamA, numA, psi_mul_entries, map_add, map_mul]
  noncomm_ring

/-- **Theorem 14.7 (2)**, p. 142: $\lambda(\beta\alpha, x) = \lambda(\beta, \alpha(x))\lambda(\alpha, x)$, whenever
$\lambda(\alpha, x)$ is invertible. -/
@[kb "shimura2004" "Theorem 14.7 (2), p. 142 (λ(βα, x) = λ(β, α(x))λ(α, x))"]
theorem theorem_14_7_2 (β α X : A) (h : IsUnit (lamA he hf hef α X)) :
    lamA he hf hef (β * α) X = lamA he hf hef β (actA he hf hef α X) * lamA he hf hef α X := by
  rw [lamA_mul, formula_14_9 he hf hef α X h]
  simp only [lamA, add_mul, mul_assoc]

/-- $ax + b$ for $\beta\alpha$ is $(a_\beta\alpha(x) + b_\beta)\lambda(\alpha, x)$. -/
theorem numA_mul_eq (β α X : A) (h : IsUnit (lamA he hf hef α X)) :
    numA he hf hef (β * α) X = numA he hf hef β (actA he hf hef α X) * lamA he hf hef α X := by
  rw [numA_mul, formula_14_9 he hf hef α X h]
  simp only [numA, add_mul, mul_assoc]

/-- **Theorem 14.7 (1)**, p. 142: $(\beta\alpha)(x) = \beta(\alpha(x))$, whenever $\lambda(\alpha, x)$ and
$\lambda(\beta, \alpha(x))$ are invertible. -/
@[kb "shimura2004" "Theorem 14.7 (1), p. 142 (β(α(x)) = (βα)(x))"]
theorem theorem_14_7_1 (β α X : A) (h : IsUnit (lamA he hf hef α X))
    (h' : IsUnit (lamA he hf hef β (actA he hf hef α X))) :
    actA he hf hef (β * α) X = actA he hf hef β (actA he hf hef α X) := by
  have e1 := numA_mul_eq he hf hef β α X h
  have e2 := theorem_14_7_2 he hf hef β α X h
  obtain ⟨u, hu⟩ := h
  obtain ⟨u', hu'⟩ := h'
  set Y := actA he hf hef α X
  have : actA he hf hef β Y = numA he hf hef β Y * ((u'⁻¹ : Aˣ) : A) := by
    rw [actA, ← hu', Ring.inverse_unit]
  rw [this, actA, e1, e2, ← hu, ← hu', ← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul,
    mul_assoc, ← mul_assoc (u : A), Units.mul_inv, one_mul]

end Algebraic

/-! ### Signature $(1, m)$ over $\mathbb R$: the half-spaces and the statement of Theorem 14.7 -/

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} {e f : V}

variable (Q e f) in
/-- **Shimura's $H$** (14.6b), p. 141: $H = \{x \in W : \eta(x) > 0\}$. -/
@[kb "shimura2004" "(14.6b), p. 141 (H = {x ∈ W | η(x) > 0}, H' = {x ∈ W | η(x) < 0})"]
def upperH : Set V := {x | x ∈ wSpace Q e f ∧ 0 < etaW Q e f x}

variable (Q e f) in
/-- **Shimura's $H'$** (14.6b), p. 141: $H' = \{x \in W : \eta(x) < 0\}$. -/
@[kb "shimura2004" "(14.6b), p. 141 (H = {x ∈ W | η(x) > 0}, H' = {x ∈ W | η(x) < 0})"]
def lowerH : Set V := {x | x ∈ wSpace Q e f ∧ etaW Q e f x < 0}

/-- **Theorem 14.7** (Shimura 2004, p. 142), main assertions, as a named proposition (not proved here). Let
$\varphi$ have signature $(1, m)$ on $V$ with $m > 1$ (`IsLorentzian Q`, $\dim V \ge 3$), and $\kappa = e + f$,
$\iota = e - f$. For every $\alpha \in G^\pm(V)$ and $x \in H \cup H'$:
* $\lambda(\alpha, x)$ is invertible and belongs to $G^\pm(W)$ (`subspaceCliffordGroup Q (e + f) i`, with the parity
  $i$ of $\alpha$);
* $\alpha(x) = y$ is a vector of $H \cup H'$;
* if $\mu(\alpha) > 0$ then $\alpha$ maps $H$ to $H$ and $H'$ to $H'$; if $\mu(\alpha) < 0$ it exchanges them.
Items (1), (2) of the theorem are `theorem_14_7_1`, `theorem_14_7_2` (given the invertibility asserted here). -/
@[kb "shimura2004" "Theorem 14.7, p. 142 (λ(α, x) ∈ G^±(W) invertible and α(x) ∈ H ∪ H'; μ(α) > 0 preserves H, H')"]
def Theorem14_7 (Q : QuadraticForm ℝ V) (e f : V) (he : Q e = 0) (hf : Q f = 0)
    (hef : QuadraticMap.polar Q e f = 1) (hQ : (QuadraticMap.associated Q).Nondegenerate) : Prop :=
  IsLorentzian Q → 3 ≤ finrank ℝ V →
  ∀ (α : homogeneousCliffordGroup Q) (i : ZMod 2) (x : V),
    ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q i → x ∈ upperH Q e f ∪ lowerH Q e f →
    (∃ u : (CliffordAlgebra Q)ˣ, (u : CliffordAlgebra Q) =
        lamA he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) (ι Q x) ∧
        u ∈ subspaceCliffordGroup Q (e + f) i) ∧
    ∃ y : V, ι Q y = actA he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) (ι Q x) ∧
      y ∈ upperH Q e f ∪ lowerH Q e f ∧
      (0 < ((muHom hQ α : ℝˣ) : ℝ) → (x ∈ upperH Q e f ↔ y ∈ upperH Q e f)) ∧
      (((muHom hQ α : ℝˣ) : ℝ) < 0 → (x ∈ upperH Q e f ↔ y ∈ lowerH Q e f))

end Real

end MatrixModel

end QuadFormsKB.Shimura2004
