import QuadFormsKB.Historical.Gauss.CompositionInvariance
import QuadFormsKB.Historical.Gauss.Duplication

/-!
# Gauss's duplication substitution, composition of non-primitive forms, derived orders (Arts. 236, 259, 286, 287)

(Art. 287 I: if a form is compounded of $f$ with itself, the middle coefficients
of the substitution agree) (Art. 286: the duplication substitution built from a representation of the
opposite form by $x^2 - 2yz$) (Art. 236 for non-primitive forms) and (Art. 259, last
paragraph: ambiguous classes of an order derived from a primitive order).

## What is proved

* `art287_eq_of_compounded_self` (Art. 287 I (a)): if a bilinear substitution with coprime six numbers has
  $P = Q$, $R - S = R + S$-type relations coming from a **common** $n = n'$, then $p_1 = p_2$ and $q_1 = q_2$;
  `art287_specialization` is part (b).  **Restriction recorded:** Gauss gets $n = n'$ from $n^2 = d/D = n'^2$
  (Art. 235). The library does not contain the relation $n^2 = d/D$ (`IsCompounded` only records the six relations and
  positivity), so $n = n'$ is an explicit hypothesis here.
* `art286_*` (Art. 286): the two duplication substitutions, with the sign forced by the representation of the
  opposite form determined (see `art286_middle_coefficient`), and `art286_duplicate`: $F$ is its own duplicate.
* `isCompounded_scaleForm`, `art236_exists_compounded_nonprimitive` (Art. 236, non-primitive forms $m f_0$,
  $m' f_0'$ with $f_0, f_0'$ primitive of equal discriminant).
* `card_ambiguous_derived` (Art. 259, last paragraph): the ambiguous classes of the derived forms $m f$ are in bijection
  with the ambiguous classes of the primitive order.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-! ### Art. 287 I: the two middle coefficients of a self-composition agree -/

/-- Core of Art. 287 I: for a bilinear substitution whose six numbers have no common divisor other than $\pm 1$,
the relations $P = Q$, $S = 0$, $T = U$ force $p_1 = p_2$ and $q_1 = q_2$. (Proof: they say that
$u = (p_1 - p_2, q_1 - q_2)$ is parallel to $(p_0, q_0)$, $(p_1, q_1)$, $(p_2, q_2)$, $(p_3, q_3)$; if $u \ne 0$ all
four are parallel and all six minors vanish.) -/
theorem art287_core (p q : Fin 4 → ℤ) (hcop : ∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d)
    (hPQ : minors p q 0 = minors p q 1) (hS : minors p q 3 = 0) (hTU : minors p q 4 = minors p q 5) :
    p 1 = p 2 ∧ q 1 = q 2 := by
  simp only [minors, Matrix.cons_val] at hPQ hS hTU
  by_contra hne
  have hu : ¬ (p 1 - p 2 = 0 ∧ q 1 - q 2 = 0) := by
    rintro ⟨h1, h2⟩; exact hne ⟨by linarith, by linarith⟩
  -- parallelism relations with `u`
  have h0 : p 0 * (q 1 - q 2) - q 0 * (p 1 - p 2) = 0 := by linear_combination hPQ
  have h3 : p 3 * (q 1 - q 2) - q 3 * (p 1 - p 2) = 0 := by linear_combination -hTU
  have h1 : p 1 * (q 1 - q 2) - q 1 * (p 1 - p 2) = 0 := by linear_combination -hS
  have h2 : p 2 * (q 1 - q 2) - q 2 * (p 1 - p 2) = 0 := by linear_combination -hS
  have key : ∀ vx vy wx wy : ℤ, vx * (q 1 - q 2) - vy * (p 1 - p 2) = 0 →
      wx * (q 1 - q 2) - wy * (p 1 - p 2) = 0 → vx * wy - vy * wx = 0 := by
    intro vx vy wx wy hv hw
    by_cases hx : p 1 - p 2 = 0
    · have hy : q 1 - q 2 ≠ 0 := fun hy => hu ⟨hx, hy⟩
      have : (q 1 - q 2) * (vx * wy - vy * wx) = 0 := by
        rw [hx] at hv hw; linear_combination wy * hv - vy * hw
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hy
      · exact h
    · have : (p 1 - p 2) * (vx * wy - vy * wx) = 0 := by
        linear_combination wx * hv - vx * hw
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx
      · exact h
  have hall : ∀ i, minors p q i = 0 := by
    intro i
    fin_cases i
    · exact key (p 0) (q 0) (p 1) (q 1) h0 h1
    · exact key (p 0) (q 0) (p 2) (q 2) h0 h2
    · exact key (p 0) (q 0) (p 3) (q 3) h0 h3
    · exact hS
    · exact key (p 1) (q 1) (p 3) (q 3) h1 h3
    · exact key (p 2) (q 2) (p 3) (q 3) h2 h3
  have := hcop 0 (fun i => by rw [hall i])
  exact absurd this not_isUnit_zero

/-- **Art. 287 I (a)** (Gauss, *Disq. Arith.* Art. 287 I): if $F$ is transformed into
the product $f \cdot f$ (the **same** form twice) by a bilinear substitution whose six numbers have no common divisor, and
the six relations of Art. 235 hold with a **common** $n = n'$ (library coefficients:
$P = a n$, $R - S = b n$, $U = c n$, $Q = a n$, $R + S = b n$, $T = c n$), then $p_1 = p_2$ and $q_1 = q_2$ (the two middle
coefficients of the substitution agree).

**Difference from the source:** Gauss obtains $n = n'$ from $n^2 = d/D = n'^2$ (Art. 235, with $n, n' > 0$); the
library has no formal counterpart of $n^2 = d/D$, so $n = n'$ is taken as the hypothesis (a restriction recorded here).
The transformation hypothesis `_hT` is part of the setting but not used by the proof, which only needs the
six relations and the coprimality. -/
@[kb "gauss1801" "Art. 287 I"]
theorem art287_eq_of_compounded_self {F f : BinQF} {p q : Fin 4 → ℤ} (_hT : TransformsInto F f f p q)
    (hcop : ∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) {n : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n) (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n)
    (h2 : (minors p q 5 : ℚ) = f.c * n) (h3 : (minors p q 1 : ℚ) = f.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f.b * n) (h5 : (minors p q 4 : ℚ) = f.c * n) :
    p 1 = p 2 ∧ q 1 = q 2 := by
  refine art287_core p q hcop ?_ ?_ ?_
  · have : (minors p q 0 : ℚ) = minors p q 1 := by rw [h0, h3]
    exact_mod_cast this
  · have : (minors p q 3 : ℚ) = 0 := by linarith
    exact_mod_cast this
  · have : (minors p q 4 : ℚ) = minors p q 5 := by rw [h2, h5]
    exact_mod_cast this

/-- **Art. 287 I (b)**: if $F$ is transformed into $f \cdot f$ by a bilinear substitution with
$p_1 = p_2$ and $q_1 = q_2$, then $F(T, U) = f(t, u)^2$ for $T = p_0t^2 + 2p_1tu + p_3u^2$,
$U = q_0t^2 + 2q_1tu + q_3u^2$ (put $x = x' = t$, $y = y' = u$). -/
@[kb "gauss1801" "Art. 287 I"]
theorem art287_specialization {F f : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f p q)
    (hp : p 1 = p 2) (hq : q 1 = q 2) (t u : ℤ) :
    F.eval (p 0 * t ^ 2 + 2 * p 1 * t * u + p 3 * u ^ 2) (q 0 * t ^ 2 + 2 * q 1 * t * u + q 3 * u ^ 2) =
      (f.eval t u) ^ 2 := by
  have := hT t u t u
  simp only [bilin, ← hp, ← hq] at this
  rw [pow_two (f.eval t u), ← this]
  congr 1 <;> ring

/-! ### Art. 286: the duplication substitution -/

/-- **The sign of the middle coefficient** (Art. 286): if
$F' = A T^2 - 2 B T U + C U^2$ (the opposite of $F = (A, B, C)$) is represented by $x^2 - 2yz$ via
$(x, y, z) = (\alpha T + \beta U, \alpha' T + \beta' U, \alpha'' T + \beta'' U)$, then comparing the coefficient of
$TU$ gives $-2B = 2(\alpha\beta - \alpha'\beta'' - \alpha''\beta')$, i.e. the sign is **forced**:
$B = -(\alpha\beta - \alpha'\beta'' - \alpha''\beta') = \alpha'\beta'' + \alpha''\beta' - \alpha\beta$
(the historical sources' "$\pm$" is therefore the sign $-$; with $+$ the substitutions below hold only after replacing $Y$ by $-Y$).
This statement checks the identity: the values of $F'$ at $(T, U)$ are those of $x^2 - 2yz$. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_middle_coefficient (α β α' β' α'' β'' T U : ℤ) :
    (α * T + β * U) ^ 2 - 2 * (α' * T + β' * U) * (α'' * T + β'' * U) =
      (α ^ 2 - 2 * α' * α'') * T ^ 2 - 2 * (α' * β'' + α'' * β' - α * β) * T * U +
        (β ^ 2 - 2 * β' * β'') * U ^ 2 := by ring

/-- **The determinant** (Art. 286): with $a = \alpha\beta' - \alpha'\beta$, $b = \alpha'\beta'' - \alpha''\beta'$,
$c = \alpha''\beta - \alpha\beta''$ and $A = \alpha^2 - 2\alpha'\alpha''$, $B = \alpha'\beta'' + \alpha''\beta' - \alpha\beta$,
$C = \beta^2 - 2\beta'\beta''$: $b^2 - 2ac = B^2 - AC$. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_det (α β α' β' α'' β'' : ℤ) :
    (α' * β'' - α'' * β') ^ 2 - 2 * (α * β' - α' * β) * (α'' * β - α * β'') =
      (α' * β'' + α'' * β' - α * β) ^ 2 - (α ^ 2 - 2 * α' * α'') * (β ^ 2 - 2 * β' * β'') := by ring

/-- **The first duplication substitution** (Art. 286): with $A, B, C$ as in
`art286_middle_coefficient` and $a, b, c$ as in `art286_det`, the substitution
$p = (2\beta', \beta, \beta, \beta'')$, $q = (2\alpha', \alpha, \alpha, \alpha'')$ transforms $F = (A, B, C)$ into
the product of $(2a, -b, c)$ with itself. Verified by `ring`; agrees with the historical sources. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_transforms_first (α β α' β' α'' β'' : ℤ) :
    TransformsInto (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
      (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β''))
      (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β''))
      ![2 * β', β, β, β''] ![2 * α', α, α, α''] := by
  intro x y x' y'
  simp only [eval_gaussForm, bilin]
  simp
  ring

/-- **The second duplication substitution** (Art. 286):
$p = (\beta', \beta, \beta, 2\beta'')$, $q = (\alpha', \alpha, \alpha, 2\alpha'')$ transforms $F = (A, B, C)$ into
the product of $(a, -b, 2c)$ with itself. Verified by `ring`; agrees with the historical sources. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_transforms_second (α β α' β' α'' β'' : ℤ) :
    TransformsInto (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
      (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β'')))
      (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β'')))
      ![β', β, β, 2 * β''] ![α', α, α, 2 * α''] := by
  intro x y x' y'
  simp only [eval_gaussForm, bilin]
  simp
  ring

/-- **At least one of $a, c$ is odd** (Art. 286): if $F = (A, B, C)$ is properly primitive and the minors
$a, b, c$ of the representation have no common divisor (the properness of the representation), then $a$ or $c$ is odd.
(If both were even, $b$ would be odd; the orthogonality $\alpha b + \alpha' c + \alpha'' a = 0 =
\beta b + \beta' c + \beta'' a$ makes $\alpha, \beta$ even, so $A, C$ and $2B$ are even, contradicting primitivity.) -/
@[kb "gauss1801" "Art. 286"]
theorem art286_odd_or_odd (α β α' β' α'' β'' : ℤ)
    (hF : (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β'')).IsPrimitive)
    (hcop : ∀ d : ℤ, d ∣ (α * β' - α' * β) → d ∣ (α' * β'' - α'' * β') → d ∣ (α'' * β - α * β'') → IsUnit d) :
    Odd (α * β' - α' * β) ∨ Odd (α'' * β - α * β'') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hc⟩ := hcon
  rw [Int.not_odd_iff_even] at ha hc
  obtain ⟨a1, ha1⟩ := ha
  obtain ⟨c1, hc1⟩ := hc
  have hb : ¬ (2 : ℤ) ∣ (α' * β'' - α'' * β') := by
    intro h
    have := hcop 2 ⟨a1, by omega⟩ h ⟨c1, by omega⟩
    exact absurd this (by decide)
  have hαb : (2 : ℤ) ∣ α * (α' * β'' - α'' * β') :=
    ⟨-(α' * c1 + α'' * a1), by linear_combination (-α') * hc1 - α'' * ha1⟩
  have hβb : (2 : ℤ) ∣ β * (α' * β'' - α'' * β') :=
    ⟨-(β' * c1 + β'' * a1), by linear_combination (-β') * hc1 - β'' * ha1⟩
  have hα : (2 : ℤ) ∣ α := (Int.prime_two.dvd_mul.mp hαb).resolve_right hb
  have hβ : (2 : ℤ) ∣ β := (Int.prime_two.dvd_mul.mp hβb).resolve_right hb
  obtain ⟨α1, hα1⟩ := hα
  obtain ⟨β1, hβ1⟩ := hβ
  have := hF 2 ⟨2 * α1 ^ 2 - α' * α'', by simp only [a_gaussForm]; rw [hα1]; ring⟩
    ⟨α' * β'' + α'' * β' - α * β, by simp only [b_gaussForm]⟩
    ⟨2 * β1 ^ 2 - β' * β'', by simp only [c_gaussForm]; rw [hβ1]; ring⟩
  exact absurd this (by decide)

/-- Properly primitive (in Gauss's sense) from an odd coefficient: if $\gcd(a, b, c) = 1$ and $c$ is odd then
$(2a, -b, c)$ is properly primitive. -/
theorem isPrimitive_two_mul_of_odd {a b c : ℤ} (hc : Odd c)
    (hcop : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) : (gaussForm (2 * a) (-b) c).IsPrimitive := by
  intro d h1 h2 h3
  simp only [a_gaussForm, b_gaussForm, c_gaussForm] at h1 h2 h3
  obtain ⟨k, hk⟩ := hc
  obtain ⟨e, he⟩ := h3
  have hd2 : IsCoprime d 2 := ⟨e, -k, by linarith⟩
  have h1' : d ∣ a := hd2.dvd_of_dvd_mul_left (by simpa [mul_comm] using h1)
  have h2' : d ∣ b := by
    have : d ∣ 2 * -b := by simpa using h2
    have := hd2.dvd_of_dvd_mul_left this
    exact (dvd_neg).mp this
  exact hcop d h1' h2' ⟨e, he⟩

/-- Properly primitive from an odd first coefficient: if $\gcd(a, b, c) = 1$ and $a$ is odd then $(a, -b, 2c)$ is
properly primitive. -/
theorem isPrimitive_two_mul_of_odd' {a b c : ℤ} (ha : Odd a)
    (hcop : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) : (gaussForm a (-b) (2 * c)).IsPrimitive := by
  intro d h1 h2 h3
  simp only [a_gaussForm, b_gaussForm, c_gaussForm] at h1 h2 h3
  obtain ⟨k, hk⟩ := ha
  obtain ⟨e, he⟩ := h1
  have hd2 : IsCoprime d 2 := ⟨e, -k, by linarith⟩
  have h2' : d ∣ b := by
    have : d ∣ 2 * -b := by simpa using h2
    have := hd2.dvd_of_dvd_mul_left this
    exact (dvd_neg).mp this
  have h3' : d ∣ c := hd2.dvd_of_dvd_mul_left (by simpa [mul_comm] using h3)
  exact hcop d ⟨e, he⟩ h2' h3'

/-- **$F$ is compounded of $(2a, -b, c)$ with itself** (Art. 286), when that form is properly
primitive: the first duplication substitution has six numbers $(2a, 2a, -2b, 0, c, c)$, so Art. 235's relations hold with
$n = n' = 1$, and the six numbers are coprime exactly because $(2a, -b, c)$ is properly primitive. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_isCompounded_first (α β α' β' α'' β'' : ℤ)
    (hp : (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β'')).IsPrimitive) :
    IsCompounded (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
      (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β''))
      (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β'')) := by
  refine ⟨![2 * β', β, β, β''], ![2 * α', α, α, α''], art286_transforms_first α β α' β' α'' β'', ?_,
    1, 1, one_pos, one_pos, ?_⟩
  · intro d hd
    have h0 := hd 0
    have h2 := hd 2
    have h4 := hd 4
    simp only [minors, Matrix.cons_val] at h0 h2 h4
    try simp at h0 h2 h4
    refine hp d ?_ ?_ ?_
    · simp only [a_gaussForm]; convert h0 using 1; ring
    · simp only [b_gaussForm]; convert h2 using 1; ring
    · simp only [c_gaussForm]; convert h4 using 1; ring
  · simp [minors]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **$F$ is compounded of $(a, -b, 2c)$ with itself** (Art. 286), when that form is properly
primitive: the second duplication substitution has six numbers $(a, a, -2b, 0, 2c, 2c)$ and $n = n' = 1$. -/
@[kb "gauss1801" "Art. 286"]
theorem art286_isCompounded_second (α β α' β' α'' β'' : ℤ)
    (hp : (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β''))).IsPrimitive) :
    IsCompounded (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
      (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β'')))
      (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β''))) := by
  refine ⟨![β', β, β, 2 * β''], ![α', α, α, 2 * α''], art286_transforms_second α β α' β' α'' β'', ?_,
    1, 1, one_pos, one_pos, ?_⟩
  · intro d hd
    have h0 := hd 0
    have h2 := hd 2
    have h4 := hd 4
    simp only [minors, Matrix.cons_val] at h0 h2 h4
    try simp at h0 h2 h4
    refine hp d ?_ ?_ ?_
    · simp only [a_gaussForm]; convert h0 using 1; ring
    · simp only [b_gaussForm]; convert h2 using 1; ring
    · simp only [c_gaussForm]; convert h4 using 1; ring
  · simp [minors]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **$F$ is its own duplicate, from a representation of the opposite form** (Gauss,
*Disq. Arith.* Art. 286): let $F = (A, B, C)$ with $A = \alpha^2 - 2\alpha'\alpha''$,
$B = \alpha'\beta'' + \alpha''\beta' - \alpha\beta$, $C = \beta^2 - 2\beta'\beta''$ (so that the opposite form is
represented by $x^2 - 2yz$), $a, b, c$ the minors, with $F$ properly primitive and $\gcd(a, b, c) = 1$ (the representation
is proper). Then either $c$ is odd, $(2a, -b, c)$ is properly primitive and $F$ is compounded directly of
$(2a, -b, c)$ with itself, or $a$ is odd, $(a, -b, 2c)$ is properly primitive and $F$ is compounded directly of
$(a, -b, 2c)$ with itself (with $n = n' = 1$ in both cases). The hypotheses "$F$ properly primitive" and
"$\gcd(a, b, c) = 1$" are the source's; the latter is **not** implied by the former (e.g. $\alpha = 1$,
$(\beta, \beta', \beta'') = (0, 2, 2)$, all other $\alpha$'s $0$, gives $F = (1, 0, -8)$ properly primitive with
$(a, b, c) = (2, 0, -2)$). -/
@[kb "gauss1801" "Art. 286"]
theorem art286_duplicate (α β α' β' α'' β'' : ℤ)
    (hF : (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β'')).IsPrimitive)
    (hcop : ∀ d : ℤ, d ∣ (α * β' - α' * β) → d ∣ (α' * β'' - α'' * β') → d ∣ (α'' * β - α * β'') → IsUnit d) :
    (Odd (α'' * β - α * β'') ∧
      (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β'')).IsPrimitive ∧
      IsCompounded (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
        (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β''))
        (gaussForm (2 * (α * β' - α' * β)) (-(α' * β'' - α'' * β')) (α'' * β - α * β''))) ∨
    (Odd (α * β' - α' * β) ∧
      (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β''))).IsPrimitive ∧
      IsCompounded (gaussForm (α ^ 2 - 2 * α' * α'') (α' * β'' + α'' * β' - α * β) (β ^ 2 - 2 * β' * β''))
        (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β'')))
        (gaussForm (α * β' - α' * β) (-(α' * β'' - α'' * β')) (2 * (α'' * β - α * β'')))) := by
  rcases art286_odd_or_odd α β α' β' α'' β'' hF hcop with ha | hc
  · right
    have hp := isPrimitive_two_mul_of_odd' (c := α'' * β - α * β'') ha hcop
    exact ⟨ha, hp, art286_isCompounded_second α β α' β' α'' β'' hp⟩
  · left
    have hp := isPrimitive_two_mul_of_odd hc hcop
    exact ⟨hc, hp, art286_isCompounded_first α β α' β' α'' β'' hp⟩

/-! ### Art. 236 for non-primitive forms -/

/-- **Scaling a form:** $m f = (m a) x^2 + (m b) xy + (m c) y^2$. -/
def scaleForm (m : ℤ) (f : BinQF) : BinQF := BinQF.mk (m * f.a) (m * f.b) (m * f.c)

@[simp] theorem a_scaleForm (m : ℤ) (f : BinQF) : (scaleForm m f).a = m * f.a := by simp [scaleForm]
@[simp] theorem b_scaleForm (m : ℤ) (f : BinQF) : (scaleForm m f).b = m * f.b := by simp [scaleForm]
@[simp] theorem c_scaleForm (m : ℤ) (f : BinQF) : (scaleForm m f).c = m * f.c := by simp [scaleForm]

theorem eval_scaleForm (m : ℤ) (f : BinQF) (x y : ℤ) : (scaleForm m f).eval x y = m * f.eval x y := by
  rw [eval_eq, eval_eq]; simp only [a_scaleForm, b_scaleForm, c_scaleForm]; ring

/-- **Art. 236 for non-primitive forms, scaling** (Gauss, *Disq. Arith.* Art. 236): if $F$ is
compounded directly of $f_0$ and $f_0'$ and $m, m' > 0$, then $m m' F$ (all coefficients multiplied) is compounded
directly of $m f_0$ and $m' f_0'$, by the same substitution; the six numbers are unchanged and $n, n'$ become
$n / m'$, $n' / m$. -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
theorem isCompounded_scaleForm {F f f' : BinQF} (h : IsCompounded F f f') {m m' : ℤ} (hm : 0 < m) (hm' : 0 < m') :
    IsCompounded (scaleForm (m * m') F) (scaleForm m f) (scaleForm m' f') := by
  obtain ⟨p, q, hT, hcop, n, n', hn, hn', h0, h1, h2, h3, h4, h5⟩ := h
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hmQ' : (0 : ℚ) < m' := by exact_mod_cast hm'
  refine ⟨p, q, ?_, hcop, n / m', n' / m, div_pos hn hmQ', div_pos hn' hmQ, ?_⟩
  · intro x y x' y'
    rw [eval_scaleForm, eval_scaleForm, eval_scaleForm, hT]; ring
  · simp only [a_scaleForm, b_scaleForm, c_scaleForm]
    push_cast
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0]; field_simp
    · rw [h1]; field_simp
    · rw [h2]; field_simp
    · rw [h3]; field_simp
    · rw [h4]; field_simp
    · rw [h5]; field_simp

/-- **Art. 236 for non-primitive forms** (Gauss, *Disq. Arith.* Art. 236): if $f_0, f_0'$ are
primitive of the same nonzero discriminant and $m, m' > 0$, then the (non-primitive) forms $m f_0$, $m' f_0'$ have a
form compounded directly of them (namely $m m' F_0$ for $F_0$ compounded of $f_0, f_0'$; Gauss's Art. 236 hypothesis is only
that the determinants are in the ratio of two squares, which is `GaussCompositionExistence`, still stated). -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
theorem art236_exists_compounded_nonprimitive {f₀ f₀' : BinQF} (hf : f₀.IsPrimitive) (hf' : f₀'.IsPrimitive)
    (hD : f₀.disc = f₀'.disc) (hD0 : f₀.disc ≠ 0) {m m' : ℤ} (hm : 0 < m) (hm' : 0 < m') :
    ∃ F : BinQF, IsCompounded F (scaleForm m f₀) (scaleForm m' f₀') := by
  obtain ⟨F₀, hc, -, -⟩ := art236_exists_compounded hf hf' hD hD0
  exact ⟨_, isCompounded_scaleForm hc hm hm'⟩

/-! ### Art. 259: ambiguous classes of a derived order -/

theorem subst_scaleForm (m p q r s : ℤ) (f : BinQF) :
    subst p q r s (scaleForm m f) = scaleForm m (subst p q r s f) := by
  apply ext_eval; intro x y
  simp only [eval_subst, eval_scaleForm]

theorem scaleForm_injective {m : ℤ} (hm : m ≠ 0) {f g : BinQF} (h : scaleForm m f = scaleForm m g) : f = g := by
  have ha := congrArg BinQF.a h
  have hb := congrArg BinQF.b h
  have hc := congrArg BinQF.c h
  simp only [a_scaleForm, b_scaleForm, c_scaleForm] at ha hb hc
  exact ext_abc (mul_left_cancel₀ hm ha) (mul_left_cancel₀ hm hb) (mul_left_cancel₀ hm hc)

/-- **Proper equivalence is unchanged by scaling** (Art. 259): for $m \ne 0$, $m f \sim m g$ iff $f \sim g$. -/
@[kb "gauss1801" "Art. 259"]
theorem sLEquiv_scaleForm_iff {m : ℤ} (hm : m ≠ 0) {f g : BinQF} :
    SLEquiv (scaleForm m f) (scaleForm m g) ↔ SLEquiv f g := by
  rw [sLEquiv_iff, sLEquiv_iff]
  constructor
  · rintro ⟨p, q, r, s, hd, h⟩
    exact ⟨p, q, r, s, hd, scaleForm_injective hm (by rw [← subst_scaleForm]; exact h)⟩
  · rintro ⟨p, q, r, s, hd, h⟩
    exact ⟨p, q, r, s, hd, by rw [subst_scaleForm, h]⟩

theorem conjForm_scaleForm (m : ℤ) (f : BinQF) : conjForm (scaleForm m f) = scaleForm m (conjForm f) :=
  ext_abc (by simp) (by simp) (by simp)

/-- **Ambiguous form** (Gauss, *Disq. Arith.* Art. 223 and 257): a form properly equivalent to its opposite form
$(a, -b, c)$ (`Binary.conjForm`). -/
def IsAmbiguousForm (f : BinQF) : Prop := SLEquiv f (conjForm f)

theorem isAmbiguousForm_congr {f g : BinQF} (e : SLEquiv f g) : IsAmbiguousForm f ↔ IsAmbiguousForm g := by
  unfold IsAmbiguousForm
  constructor
  · intro h; exact (e.symm.trans h).trans (sLEquiv_conjForm e)
  · intro h; exact (e.trans h).trans (sLEquiv_conjForm e).symm

/-- **Scaling preserves ambiguity** (Art. 259): $m f$ is ambiguous iff $f$ is ($m \ne 0$). -/
@[kb "gauss1801" "Art. 259"]
theorem isAmbiguousForm_scaleForm_iff {m : ℤ} (hm : m ≠ 0) (f : BinQF) :
    IsAmbiguousForm (scaleForm m f) ↔ IsAmbiguousForm f := by
  unfold IsAmbiguousForm
  rw [conjForm_scaleForm, sLEquiv_scaleForm_iff hm]

/-- **The forms of the derived order** $\{m f : f \text{ primitive of discriminant } D\}$. -/
def DerivedForm (D m : ℤ) : Type := {g : BinQF // ∃ f : PrimForm D, g = scaleForm m f.1}

/-- Proper equivalence on the derived forms. -/
def derivedSetoid (D m : ℤ) : Setoid (DerivedForm D m) where
  r g h := SLEquiv g.1 h.1
  iseqv := ⟨fun g => SLEquiv.refl g.1, SLEquiv.symm, SLEquiv.trans⟩

/-- **The proper classes of the derived order** (Art. 259): derived forms up to proper equivalence. -/
def DerivedClass (D m : ℤ) : Type := Quotient (derivedSetoid D m)

/-- **A derived class is ambiguous** if (equivalently, for every representative, `isAmbiguousForm_congr`) its forms
are properly equivalent to their opposite forms. -/
def DerivedClass.IsAmbiguous {D m : ℤ} (C : DerivedClass D m) : Prop :=
  Quotient.liftOn C (fun g : DerivedForm D m => IsAmbiguousForm g.1)
    (fun g h e => propext (isAmbiguousForm_congr e))

/-- The map sending the class of a primitive form $f$ to the class of $m f$. -/
def derivedClassMap (D : ℤ) {m : ℤ} (hm : m ≠ 0) : FormClass D → DerivedClass D m :=
  Quotient.map (fun f : PrimForm D => (⟨scaleForm m f.1, f, rfl⟩ : DerivedForm D m))
    (fun f g (h : SLEquiv f.1 g.1) => (sLEquiv_scaleForm_iff hm).2 h)

/-- **Primitive classes and derived classes correspond** (Art. 259): $\mathfrak C \mapsto m\mathfrak C$ is a bijection. -/
theorem derivedClassMap_bijective (D : ℤ) {m : ℤ} (hm : m ≠ 0) : Function.Bijective (derivedClassMap D hm) := by
  constructor
  · intro C C'
    induction C using Quotient.inductionOn with | _ f =>
    induction C' using Quotient.inductionOn with | _ g =>
    intro h
    exact Quotient.sound ((sLEquiv_scaleForm_iff hm).1 (Quotient.exact h))
  · intro C
    induction C using Quotient.inductionOn with | _ g =>
    obtain ⟨g, f, rfl⟩ := g
    exact ⟨Quotient.mk (primSetoid D) f, rfl⟩

/-- **Ambiguous classes of a derived order** (Gauss, *Disq. Arith.* Art. 259, last
paragraph): for $m \ne 0$ the number of ambiguous classes (classes $\mathfrak C$ with $\mathfrak C^{-1} = \mathfrak C$)
of the primitive forms of discriminant $D$ equals the number of ambiguous classes of the derived forms $m f$ (the
classes properly equivalent to their opposite forms), via $\mathfrak C \mapsto m \mathfrak C$. -/
@[kb "gauss1801" "Art. 259, last paragraph"]
theorem card_ambiguous_derived (D : ℤ) [NonzeroDisc D] {m : ℤ} (hm : m ≠ 0) :
    Nat.card {C : FormClass D // C⁻¹ = C} = Nat.card {C : DerivedClass D m // C.IsAmbiguous} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ (derivedClassMap_bijective D hm)) ?_)
  intro C
  obtain ⟨f, rfl⟩ := FormClass.mk_surjective C
  rw [FormClass.mk_inv]
  show _ ↔ IsAmbiguousForm (scaleForm m f.1)
  rw [isAmbiguousForm_scaleForm_iff hm]
  exact ⟨fun h => (FormClass.mk_eq_mk.1 h).symm, fun h => FormClass.mk_eq_mk.2 h.symm⟩

end QuadFormsKB.Historical.Gauss

