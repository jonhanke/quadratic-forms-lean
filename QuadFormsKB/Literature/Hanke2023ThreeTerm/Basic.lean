import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Siegel.Theta

/-!
# Saha–Hanke, three-term theta relations: basic objects

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §2 and §3.1.

* Convention 2.1: a real binary form $q_{11} x^2 + q_{12} x y + q_{22} y^2$ is the triple
  $(q_{11}, q_{22}, q_{12}) \in \mathbb{R}^3$ (`RForm`, evaluated by `RForm.eval`).
* Definition 2.2: the $\mathrm{GL}_2(\mathbb{Z})$ reduction domain
  $V = \{q_{22} - q_{11} \ge 0,\ q_{12} \ge 0,\ q_{11} - q_{12} \ge 0,\ q_{11} > 0\}$ (`domainV`);
  an integral form $f = a x^2 + b x y + c y^2$ is reduced (`IsReduced`) when
  $0 \le b \le a \le c$ and $a > 0$, i.e. when its triple $(a, c, b)$ lies in $V$.
* Definition 3.1: strongly primitive vectors (`StronglyPrimitive`): $\gcd(x, y) = 1$ and the last
  non-zero coordinate is positive; strongly primitive representation numbers
  $r^{\tilde *}_Q(m)$ (`spRepNum`).

Theta series are compared through their coefficients: a linear relation
$\sum_i \alpha_i \theta_{Q_i} = 0$ means $\sum_i \alpha_i r_{Q_i}(m) = 0$ for all $m \ge 0$
(`ThetaRelation3`); for positive definite forms this gives the identity of functions on the upper
half plane (`theta_relation_of_coeff` in `NonTrivialRelation.lean`).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- **Convention 2.1 (binary quadratic forms as tuples).** The real binary form
$Q(x, y) = q_{11} x^2 + q_{12} x y + q_{22} y^2$ is recorded as the triple
$(q_{11}, q_{22}, q_{12}) \in \mathbb{R}^3$ (note the order: the $xy$ coefficient is last). -/
@[kb "hanke2023threeterm" "§2, Convention 2.1, p. 3"]
abbrev RForm := ℝ × ℝ × ℝ

/-- The value $Q(x, y) = q_{11} x^2 + q_{12} x y + q_{22} y^2$ of the real form
$Q = (q_{11}, q_{22}, q_{12})$ at the integer vector $v = (x, y)$. -/
def RForm.eval (Q : RForm) (v : ℤ × ℤ) : ℝ :=
  Q.1 * (v.1 : ℝ) ^ 2 + Q.2.2 * v.1 * v.2 + Q.2.1 * (v.2 : ℝ) ^ 2

/-- **Definition 2.2 (the $\mathrm{GL}_2(\mathbb{Z})$ reduction domain $V$).** The set of triples
$(q_{11}, q_{22}, q_{12})$ with $q_{22} - q_{11} \ge 0$, $q_{12} \ge 0$, $q_{11} - q_{12} \ge 0$ and
$q_{11} > 0$. -/
@[kb "hanke2023threeterm" "§2, Definition 2.2, p. 3"]
def domainV : Set RForm :=
  {Q | 0 ≤ Q.2.1 - Q.1 ∧ 0 ≤ Q.2.2 ∧ 0 ≤ Q.1 - Q.2.2 ∧ 0 < Q.1}

/-- The triple $(a, c, b)$ of an integral binary form $f = a x^2 + b x y + c y^2$ (Convention 2.1). -/
def toRForm (f : BinQF) : RForm := ((f.a : ℝ), (f.c : ℝ), (f.b : ℝ))

lemma toRForm_eval (f : BinQF) (v : ℤ × ℤ) :
    (toRForm f).eval v = (f.eval v.1 v.2 : ℝ) := by
  simp only [RForm.eval, toRForm, BinQF.eval_eq]; push_cast; ring

/-- **Reduced integral binary form** (Definition 2.2 for integral forms): $f = a x^2 + bxy + cy^2$
with $0 \le b \le a \le c$ and $a > 0$, i.e. `toRForm f ∈ domainV`. -/
@[kb "hanke2023threeterm" "§2, Definition 2.2, p. 3"]
def IsReduced (f : BinQF) : Prop := 0 ≤ f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c ∧ 0 < f.a

lemma isReduced_iff_mem_domainV (f : BinQF) : IsReduced f ↔ toRForm f ∈ domainV := by
  simp only [IsReduced, domainV, toRForm, Set.mem_ofPred_eq, sub_nonneg]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by exact_mod_cast h3, by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h1, by exact_mod_cast h4⟩

/-- **Definition 3.1 (strongly primitive vectors).** $(x, y) \in \mathbb{Z}^2$ is strongly
primitive if $\gcd(x, y) = 1$ and its last non-zero coordinate is positive: $y > 0$, or $y = 0$
and $x > 0$ (so $(1, 0)$ is the only strongly primitive vector with $y = 0$). -/
@[kb "hanke2023threeterm" "§3.1, Definition 3.1, p. 4"]
def StronglyPrimitive (v : ℤ × ℤ) : Prop :=
  Int.gcd v.1 v.2 = 1 ∧ (0 < v.2 ∨ (v.2 = 0 ∧ 0 < v.1))

/-- **Definition 3.1 (strongly primitive representation number)**
$r^{\tilde *}_Q(m) = \#\{(x, y) \text{ strongly primitive} : Q(x, y) = m\}$. -/
@[kb "hanke2023threeterm" "§3.1, Definition 3.1, p. 4"]
noncomputable def spRepNum (Q : BinQF) (m : ℤ) : ℕ :=
  Nat.card {v : ℤ × ℤ // StronglyPrimitive v ∧ Q.eval v.1 v.2 = m}

/-- **A three-term linear relation** $\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} +
\alpha_3 \theta_{Q_3} = 0$ among theta series (equation (2)), as the identity of all
$q$-expansion coefficients: $\alpha_1 r_{Q_1}(m) + \alpha_2 r_{Q_2}(m) + \alpha_3 r_{Q_3}(m) = 0$
for every $m \ge 0$. -/
@[kb "hanke2023threeterm" "§1, equation (2), p. 2"]
def ThetaRelation3 (Q₁ Q₂ Q₃ : BinQF) (α₁ α₂ α₃ : ℝ) : Prop :=
  ∀ m : ℕ, α₁ * repNum Q₁ m + α₂ * repNum Q₂ m + α₃ * repNum Q₃ m = 0

end QuadFormsKB.Hanke2023ThreeTerm
