import QuadFormsKB.Defs.QuadForm
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Automorphisms of reduced positive ternary forms (Eisenstein 1851, § 6, Tafeln I and II)

(Eisenstein, *Tabelle der reducirten positiven ternären quadratischen Formen*,
J. reine angew. Math. 41 (1851), 141-190, § 6, pp. 162-165, with the erratum of p. 190), continuing Gauss's ternary
section (*Disq. Arith.* Arts. 266-285).

Eisenstein writes a ternary form as
$$\begin{pmatrix} a & a' & a'' \\ b & b' & b'' \end{pmatrix} = a x^2 + a' y^2 + a'' z^2 + 2b\,yz + 2b'\,xz + 2b''\,xy$$
(`eisensteinForm`), and for a positive form lets $\delta$ be the number of substitutions of determinant $+1$ carrying
it into itself (`automorphCount`). For a form reduced in his sense (§ 2, pp. 143-144; `EisensteinReduced`, two
types: lower coefficients all positive, or all $\le 0$), § 6 computes $\delta$ from two tables of conditions with
weights $t$: Tafel I (12 numbers) for positive lower coefficients, Tafel II (18 numbers) otherwise; add the weights of
**all** numbers whose conditions hold (no logical absorption), and multiply by $1, 2, 4$ according as at most one,
exactly two, or all three lower coefficients vanish (`eisensteinDelta`). Tafel II, number (12), is taken **as
corrected** in the errata (p. 190): $a = b' + 2b''$, $a' = 2b + b'$ (printed: $2b' + b''$, $2b + b''$).

* **Stated:** `EisensteinDeltaTables`: for every positive definite reduced form, $\delta = $ the table value. Not
  proved here (the historical sources record a brute-force check against all 1262 reduced forms with $D \le 100$).
-/

namespace QuadFormsKB.Historical.Gauss

open Matrix

/-- **Eisenstein's ternary form** $\begin{pmatrix} a & a' & a'' \\ b & b' & b'' \end{pmatrix}
= a x^2 + a' y^2 + a'' z^2 + 2b\,yz + 2b'\,xz + 2b''\,xy$ (variables $x, y, z$ are coordinates $0, 1, 2$). -/
@[kb "eisenstein1851" "§ 1, p. 141"]
def eisensteinForm (a a' a'' b b' b'' : ℤ) : QuadForm ℤ 3 :=
  QuadForm.ofUpper ![![a, 2 * b'', 2 * b'], ![0, a', 2 * b], ![0, 0, a'']]

/-- **Positive definite:** $Q(v) > 0$ for every nonzero $v \in \mathbb{Z}^3$. -/
def TernPosDef (Q : QuadForm ℤ 3) : Prop := ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < QuadForm.eval Q v

/-- **Eisenstein's $\delta$:** the number of substitutions $g \in \mathrm{SL}_3(\mathbb{Z})$ ("system determinant
$+1$") with $Q(g v) = Q(v)$ for all $v$ (finite for positive $Q$; Eisenstein, § 4, p. 151). -/
@[kb "eisenstein1851" "§ 4, p. 151"]
noncomputable def automorphCount (Q : QuadForm ℤ 3) : ℕ :=
  Nat.card {g : SpecialLinearGroup (Fin 3) ℤ // ∀ v, QuadForm.eval Q ((g : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v) = QuadForm.eval Q v}

/-- **Eisenstein's reduced forms** (§ 2, pp. 143-144), for the form with coefficients $a, a', a''$ and lower
coefficients $B, B', B''$ (`eisensteinForm a a' a'' B B' B''`).

*Type I* ($B, B', B'' > 0$): $a \le a' \le a''$, $2B \le a'$, $2B' \le a$, $2B'' \le a$; if $a = a'$ then $B \le B'$;
if $a' = a''$ then $B' \le B''$; if $2B = a'$ then $B'' \le 2B'$; if $2B' = a$ then $B'' \le 2B$; if $2B'' = a$ then
$B' \le 2B$.

*Type II* ($B = -b$, $B' = -b'$, $B'' = -b''$ with $b, b', b'' \ge 0$): $a \le a' \le a''$, $2b \le a'$, $2b' \le a$,
$2b'' \le a$, $2(b + b' + b'') \le a + a'$; if $a = a'$ then $b \le b'$; if $a' = a''$ then $b' \le b''$; if
$2b = a'$ then $b'' = 0$; if $2b' = a$ then $b'' = 0$; if $2b'' = a$ then $b' = 0$; if $2(b + b' + b'') = a + a'$ then
$a \le 2b' + b''$. -/
@[kb "eisenstein1851" "§ 2, pp. 143-144"]
def EisensteinReduced (a a' a'' B B' B'' : ℤ) : Prop :=
  (0 < B ∧ 0 < B' ∧ 0 < B'' ∧ a ≤ a' ∧ a' ≤ a'' ∧ 2 * B ≤ a' ∧ 2 * B' ≤ a ∧ 2 * B'' ≤ a ∧
    (a = a' → B ≤ B') ∧ (a' = a'' → B' ≤ B'') ∧ (2 * B = a' → B'' ≤ 2 * B') ∧
    (2 * B' = a → B'' ≤ 2 * B) ∧ (2 * B'' = a → B' ≤ 2 * B)) ∨
  (B ≤ 0 ∧ B' ≤ 0 ∧ B'' ≤ 0 ∧ a ≤ a' ∧ a' ≤ a'' ∧ 2 * (-B) ≤ a' ∧ 2 * (-B') ≤ a ∧ 2 * (-B'') ≤ a ∧
    2 * (-B - B' - B'') ≤ a + a' ∧
    (a = a' → -B ≤ -B') ∧ (a' = a'' → -B' ≤ -B'') ∧ (2 * (-B) = a' → B'' = 0) ∧
    (2 * (-B') = a → B'' = 0) ∧ (2 * (-B'') = a → B' = 0) ∧
    (2 * (-B - B' - B'') = a + a' → a ≤ 2 * (-B') + (-B'')))

/-- The weight $t$ if the condition holds, else $0$. -/
def tw (c : Prop) [Decidable c] (t : ℕ) : ℕ := if c then t else 0

/-- **Tafel I** (§ 6, p. 162), positive lower coefficients $b, b', b''$: the sum of the weights of the numbers
(1)-(12) whose conditions hold. -/
@[kb "eisenstein1851" "§ 6, p. 162 (Tafel I)"]
def tafelOne (a a' a'' b b' b'' : ℤ) : ℕ :=
  tw True 1 +
  tw (a = 2 * b' ∧ a = 2 * b'') 1 +
  tw (a = 2 * b' ∧ b'' = 2 * b) 1 +
  tw (a = 2 * b'' ∧ b' = 2 * b) 1 +
  tw (a' = 2 * b ∧ b'' = 2 * b') 1 +
  tw (a = a' ∧ b = b') 1 +
  tw (a' = a'' ∧ b' = b'') 1 +
  tw (a = 2 * b' ∧ a = 2 * b'' ∧ a' = a'') 1 +
  tw (a = 2 * b' ∧ a = 2 * b'' ∧ a = 4 * b ∧ a' = a'') 2 +
  tw (a = a' ∧ a = 2 * b ∧ a = 2 * b' ∧ a = 2 * b'') 3 +
  tw (a = a' ∧ a' = a'' ∧ b = b' ∧ b' = b'') 3 +
  tw (a = a' ∧ a' = a'' ∧ a = 2 * b ∧ a = 2 * b' ∧ a = 2 * b'') 13

/-- **Tafel II** (§ 6, p. 162, with the erratum of p. 190 in number (12)), lower coefficients $-b, -b', -b''$ with
$b, b', b'' \ge 0$; $\sigma$ is the condition $a + a' = 2(b + b' + b'')$. -/
@[kb "eisenstein1851" "§ 6, p. 162 (Tafel II); erratum p. 190"]
def tafelTwo (a a' a'' b b' b'' : ℤ) : ℕ :=
  let σ := a + a' = 2 * (b + b' + b'')
  tw True 1 +
  tw (a = 2 * b' ∧ b'' = 0) 1 +
  tw (a = 2 * b'' ∧ b' = 0) 1 +
  tw (a' = 2 * b ∧ b'' = 0) 1 +
  tw (σ ∧ a = 2 * b' + b'' ∧ a' = 2 * b + b'') 1 +
  tw (a = a' ∧ b = b') 1 +
  tw (a' = a'' ∧ b' = b'') 1 +
  tw (σ ∧ a = a' ∧ a = b + b' + b'') 1 +
  tw (σ ∧ a = a' ∧ a = 2 * b ∧ a = 2 * b' ∧ b'' = 0) 2 +
  tw (a = a' ∧ a = 2 * b'' ∧ b = 0 ∧ b' = 0) 3 +
  tw (a' = a'' ∧ a' = 2 * b ∧ b' = 0 ∧ b'' = 0) 3 +
  tw (σ ∧ a' = a'' ∧ a = b' + 2 * b'' ∧ a' = 2 * b + b') 1 +
  tw (σ ∧ a' = a'' ∧ b' = b'' ∧ a = 3 * b') 2 +
  tw (a = a' ∧ a' = a'' ∧ b = b' ∧ b' = b'') 3 +
  tw (σ ∧ a = a' ∧ a' = a'') 2 +
  tw (σ ∧ a = a' ∧ a' = a'' ∧ b = b') 2 +
  tw (σ ∧ a = a' ∧ a' = a'' ∧ b' = b'') 3 +
  tw (σ ∧ a = a' ∧ a' = a'' ∧ a = 3 * b ∧ a = 3 * b' ∧ a = 3 * b'') 6

/-- **Eisenstein's rule** (§ 6, pp. 163-164) for the form with lower coefficients $B, B', B''$: the table sum (Tafel I
if all three are positive, Tafel II with $b = -B$ etc. otherwise) times $1$, $2$ or $4$ according as at most one,
exactly two, or all three lower coefficients vanish. -/
@[kb "eisenstein1851" "§ 6, pp. 163-164"]
def eisensteinDelta (a a' a'' B B' B'' : ℤ) : ℕ :=
  let zeros := (if B = 0 then 1 else 0) + (if B' = 0 then 1 else 0) + (if B'' = 0 then 1 else 0)
  let mult : ℕ := if zeros = 3 then 4 else if zeros = 2 then 2 else 1
  mult * (if 0 < B ∧ 0 < B' ∧ 0 < B'' then tafelOne a a' a'' B B' B'' else tafelTwo a a' a'' (-B) (-B') (-B''))

/-- **Eisenstein's tables for $\delta$** (Eisenstein 1851, § 6, pp. 162-164, with the
erratum of p. 190): for every positive definite ternary form
$\begin{pmatrix} a & a' & a'' \\ B & B' & B'' \end{pmatrix}$ reduced in Eisenstein's sense, the number $\delta$ of its
automorphs of determinant $+1$ is given by the tables: $\delta = $ `eisensteinDelta a a' a'' B B' B''`. Stated, not
proved. -/
@[kb "eisenstein1851" "§ 6, pp. 162-164; erratum p. 190"]
def EisensteinDeltaTables : Prop :=
  ∀ a a' a'' B B' B'' : ℤ, TernPosDef (eisensteinForm a a' a'' B B' B'') → EisensteinReduced a a' a'' B B' B'' →
    automorphCount (eisensteinForm a a' a'' B B' B'') = eisensteinDelta a a' a'' B B' B''

/-- **Eisenstein's worked examples** (§ 6, pp. 164-165) agree with the rule as formalized: e.g.
$(2, 2, 2; 1, 1, 1)$ gives $\delta = 24$, $(1, 1, 1; 0, 0, 0)$ gives $24$, $(3, 3, 3; -1, -1, -1)$ gives $24$,
$(1, 2, 2; -1, 0, 0)$ gives $12$, $(2, 2, 3; -1, -1, 0)$ gives $8$, $(4, 5, 6; 1, 2, 2)$ gives $4$,
$(2, 5, 8; -1, -1, 0)$ gives $2$ and $(3, 4, 6; 2, 1, 1)$ gives $1$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisensteinDelta_examples :
    eisensteinDelta 2 2 2 1 1 1 = 24 ∧ eisensteinDelta 1 1 1 0 0 0 = 24 ∧
    eisensteinDelta 3 3 3 (-1) (-1) (-1) = 24 ∧ eisensteinDelta 1 2 2 (-1) 0 0 = 12 ∧
    eisensteinDelta 2 2 3 (-1) (-1) 0 = 8 ∧ eisensteinDelta 4 5 6 1 2 2 = 4 ∧
    eisensteinDelta 2 5 8 (-1) (-1) 0 = 2 ∧ eisensteinDelta 3 4 6 2 1 1 = 1 := by
  decide

end QuadFormsKB.Historical.Gauss
