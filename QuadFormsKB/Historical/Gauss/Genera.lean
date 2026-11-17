import QuadFormsKB.Historical.Gauss.Forms
import QuadFormsKB.Binary.GenusComposition

/-!
# Genus characters: Gauss's assigned characters, the number of genera, and Kronecker's identity

(Kronecker, *Werke* 4, XXXI § X, pp. 379-383, equations (U), (M*), with Hensel's
corrections, Zusätze 98-101, p. 506): the analytic form of genus theory.

## Kronecker's identity (stated)

For a negative discriminant $D = D_1 D_2$ split into two discriminants ("complementary discriminant divisors"),
Kronecker proves (with $\tau$ the number of units, the sums over a system of classes $(a, b, c)$ and over all
$(m, n) \ne (0, 0)$):
$$\tau \sum_{h, k \ge 1} \Bigl(\frac{D_1}{h}\Bigr)\Bigl(\frac{D_2}{k}\Bigr) F(hk)
  = \sum_{(a, b, c)} \Bigl(\frac{D_1}{a}\Bigr) \sum_{m, n} F(am^2 + bmn + cn^2),$$
for arbitrary $F$ (equation (M*)); with $F(k) = k^{-1-\varrho}$ this is
$\tau L(s, \chi_{D_1}) L(s, \chi_{D_2}) = \sum_{\text{classes}} \chi_{D_1}(f)\,\zeta_f(s)$. Taking $F$ the indicator
of one integer $m$ gives the equivalent coefficientwise identity
$$\sum_{[f]} \chi_{D_1}(f)\, r_f(m) = \tau \sum_{d \mid m} \Bigl(\frac{D_1}{d}\Bigr)\Bigl(\frac{D_2}{m/d}\Bigr),$$
which is `KroneckerGenusCharacterIdentity`, stated for a **fundamental** discriminant $D < 0$ (Kronecker allows
$D = D_0 Q^2$ with a conductor $Q$ and $D > 0$; restriction recorded as a loose end). Here $\chi_{D_1}(f)$ is the
genus character: $\bigl(\frac{D_1}{m}\bigr)$ for any $m$ represented by $f$ and prime to $D$ (Kronecker takes $m = a$
for a representative with $a$ prime to $D$). Hensel's correction (Zusatz 98, p. 506: for even $D$ the factor $D_2$ must
be the even one) is automatic for fundamental $D$, where at most one of $D_1, D_2$ is even.

* **Proved:** the case $D_1 = 1$ (Kronecker's equation (M), Dirichlet's formula `kronecker_identity_trivial_character`,
  wrapper of the library's `Binary.dirichlet_sum_repNum_int`).
* **Stated:** the general case (`KroneckerGenusCharacterIdentity`).

## Gauss's assigned characters and the number of genera (wrappers)

For fundamental $D < 0$ with $t$ distinct prime factors (Gauss, *Disq. Arith.* Arts. 229-231, 261, 287):
the characters of a form are well defined on its values (`Binary.genusChar_eval_eq_formChar`, Art. 229), their product
is $1$ (`assigned_characters_product`, Art. 261: at most half of the possible complete characters occur), every
complete character with product $1$ occurs (`assigned_characters_exist`, Art. 287), and the number of genera is
$2^{t-1}$ (`card_genera_eq`).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary NumberField

/-- **Kronecker's genus character $\chi_{D_1}$ of a form** (Kronecker, *Werke* 4, p. 380): $\bigl(\frac{D_1}{m}\bigr)$
(the library's integer-valued Kronecker symbol `kronZ D₁`) at a value $m = f(x, y)$ prime to $D$, chosen once and
for all (the value does not depend on the choice, Gauss's Art. 229; that is not needed for the statement). It is $0$
if $f$ represents no number prime to $D$. -/
noncomputable def kroneckerGenusChar (D D₁ : ℤ) (f : BinQF) : ℤ :=
  open Classical in
  if h : ∃ x y : ℤ, IsCoprime (f.eval x y) D then
    kronZ D₁ ((f.eval h.choose h.choose_spec.choose : ℤ) : ZMod D₁.natAbs)
  else 0

/-- **Kronecker's genus character identity** (Kronecker, *Werke* 4, XXXI § X, (U) and
(M*), pp. 379-383), coefficientwise, for a fundamental discriminant $D < 0$ written as $D = D_1 D_2$ with $D_1, D_2$
fundamental discriminants $\ne 1$: for every $m \ge 1$,
$$\sum_{[f]} \chi_{D_1}(f)\, r_f(m) = w \sum_{d \mid m} \Bigl(\frac{D_1}{d}\Bigr)\Bigl(\frac{D_2}{m/d}\Bigr),$$
the sum over the proper classes of primitive positive definite forms of discriminant $D$, $w$ the number of units
of $\mathbb{Q}(\sqrt D)$ (Kronecker's $\tau$). Stated, not proved. -/
@[kb "kronecker1929" "XXXI § X, (U) and (M*), pp. 379-383; Zusätze 98-101, p. 506"]
def KroneckerGenusCharacterIdentity (D D₁ D₂ : ℤ) [IsQuadDisc D] [Fact (D < 0)] [IsQuadDisc D₁] [IsQuadDisc D₂] :
    Prop :=
  D = D₁ * D₂ → ∀ m : ℕ, m ≠ 0 →
    (∑ c : Quotient (slSetoid D), kroneckerGenusChar D D₁ c.out.1 * (slClassRepNum m c : ℤ)) =
      (Units.torsionOrder (QField D) : ℤ) *
        ∑ d ∈ m.divisors, kronZ D₁ ((d : ℤ) : ZMod D₁.natAbs) * kronZ D₂ (((m / d : ℕ) : ℤ) : ZMod D₂.natAbs)

/-- **Kronecker's identity for the trivial character** $D_1 = 1$ (Kronecker's equation (M); Dirichlet's formula;
wrapper of the library's `Binary.dirichlet_sum_repNum_int`): for fundamental $D < 0$ and $m \ge 1$,
$$\sum_{[f]} r_f(m) = w \sum_{d \mid m} \Bigl(\frac{D}{d}\Bigr).$$ -/
@[kb "kronecker1929" "XXXI § X, p. 382 ((M*) reduces to (M) for D₁ = 1)"]
theorem kronecker_identity_trivial_character {D : ℤ} [IsQuadDisc D] [Fact (D < 0)] {m : ℕ} (hm : m ≠ 0) :
    ((∑ c : Quotient (slSetoid D), slClassRepNum m c : ℕ) : ℤ) =
      Units.torsionOrder (QField D) * ∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) :=
  dirichlet_sum_repNum_int hm

/-- **The product of the assigned characters is $1$** (Gauss, *Disq. Arith.* Art. 261; wrapper of the library's
`Binary.prod_formChar_eq_one`): for a primitive positive definite form of fundamental discriminant $D < 0$,
$\prod_{p \mid D} \chi_p(f) = 1$. Hence at most half of the $2^t$ possible complete characters belong to genera. -/
@[kb "gauss1801" "Art. 261"]
theorem assigned_characters_product {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (hpos : f.PosDef') : ∏ p ∈ D.natAbs.primeFactors, formChar f p = 1 :=
  prod_formChar_eq_one hf hD hpos

/-- **Every complete character with product $1$ belongs to a genus** (Gauss, *Disq. Arith.* Art. 287 III; wrapper of
the library's `Binary.exists_form_of_signs`): for fundamental $D < 0$ and signs $e_p = \pm 1$ ($p \mid D$) with
$\prod_p e_p = 1$ there is a primitive positive definite form of discriminant $D$ with $\chi_p(f) = e_p$ for all
$p \mid D$. -/
@[kb "gauss1801" "Art. 287 III, pp. 479-480"]
theorem assigned_characters_exist {D : ℤ} [IsQuadDisc D] (hD : D < 0) (e : ℕ → ℤ)
    (he : ∀ p ∈ D.natAbs.primeFactors, e p = 1 ∨ e p = -1) (hprod : ∏ p ∈ D.natAbs.primeFactors, e p = 1) :
    ∃ f : BinQF, Primitive f ∧ f.disc = D ∧ f.PosDef' ∧ ∀ p ∈ D.natAbs.primeFactors, formChar f p = e p :=
  exists_form_of_signs hD e he hprod

/-- **The number of genera is $2^{t-1}$** (Gauss, *Disq. Arith.* Arts. 261 and 287; wrapper of the library's
`Binary.card_genera`): for a fundamental discriminant $D < 0$ with $t$ distinct prime factors, the primitive positive
definite forms of discriminant $D$ fall into exactly $2^{t-1}$ genera. -/
@[kb "gauss1801" "Arts. 261, 287, pp. 479-480"]
theorem card_genera_eq {D : ℤ} [IsQuadDisc D] (hD : D < 0) :
    Nat.card (Genera D) = 2 ^ (D.natAbs.primeFactors.card - 1) :=
  card_genera hD

end QuadFormsKB.Historical.Gauss
