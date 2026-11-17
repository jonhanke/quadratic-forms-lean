import QuadFormsKB.Historical.Gauss.SectionSix
import QuadFormsKB.Historical.Gauss.Determinants

/-!
# Representations by Gauss's forms (*Disquisitiones Arithmeticae*, Section V, Arts. 154-155, 166, 179)

Four results of the historical sources, all proved:

* (Arts. 154-155): the value $v = \mu (m b + n c) - \nu (m a + n b)$ of a proper representation
  satisfies $v^2 \equiv b^2 - ac \pmod M$ (`value_sq_modEq_gaussDet`); any two Bezout pairs give congruent values
  (`art155Value_modEq_of_bezout`); every integer congruent to one value is a value (`exists_bezout_art155Value_eq`).
* (Art. 154): every representation of $M \ne 0$ is $\mu$ times a primitive representation of
  $M / \mu^2$ (`representation_eq_gcd_mul_primitive`, `representations_eq_iUnion_primitive`).
* (Art. 166, end): a substitution of determinant $\pm 1$ preserves the greatest common divisor of
  a vector (`gcd_substVector`), hence properness of representations (`proper_representation_subst_iff`).
* (Art. 179): for negative determinant $-D$, the integer $4D/m^2$ with $m = \gcd(A, 2B, C)$ is
  at least $3$ and is $\equiv 0, 3 \pmod 4$ (`art179_quotient`).

Gauss's $(a, b, c)$ is `gaussForm a b c`, i.e. $a x^2 + 2 b x y + c y^2$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Arts. 154-155: the value of a proper representation -/

/-- **The value of a proper representation squares to the determinant** (the historical sources;
*Disq. Arith.* Arts. 154-155): if $M = (a, b, c)(m, n)$ is properly represented by $x = m$, $y = n$, and
$\mu m + \nu n = 1$, then $v = \mu (m b + n c) - \nu (m a + n b)$ satisfies $v^2 \equiv b^2 - ac \pmod M$.
A restatement of `art155_value_sq` in the terms of the row, with $M$ named. -/
@[kb "gauss1801" "Art. 154-155"]
theorem value_sq_modEq_gaussDet (a b c m n μ ν M : ℤ) (hM : (gaussForm a b c).eval m n = M)
    (h : μ * m + ν * n = 1) :
    (μ * (m * b + n * c) - ν * (m * a + n * b)) ^ 2 ≡ b ^ 2 - a * c [ZMOD M] := by
  subst hM
  exact art155_value_sq a b c m n μ ν h

/-- **Any two Bezout pairs give congruent values** (*Disq. Arith.* Art. 155): if
$\mu m + \nu n = 1 = \mu' m + \nu' n$ then, with $k = \nu \mu' - \mu \nu'$, one has $\mu' = \mu + k n$,
$\nu' = \nu - k m$ and $v' - v = k M$, where $M = a m^2 + 2 b m n + c n^2$; so the values are congruent
modulo $M$. -/
@[kb "gauss1801" "Art. 154-155"]
theorem art155Value_modEq_of_bezout (a b c m n μ ν μ' ν' : ℤ) (h : μ * m + ν * n = 1)
    (h' : μ' * m + ν' * n = 1) :
    art155Value a b c m n μ ν ≡ art155Value a b c m n μ' ν' [ZMOD (gaussForm a b c).eval m n] := by
  rw [Int.modEq_iff_dvd, eval_gaussForm]
  refine ⟨ν * μ' - μ * ν', ?_⟩
  have h1 : μ' - μ = (ν * μ' - μ * ν') * n := by linear_combination (-μ') * h + μ * h'
  have h2 : ν' - ν = -(ν * μ' - μ * ν') * m := by linear_combination (-ν') * h + ν * h'
  unfold art155Value
  linear_combination (m * b + n * c) * h1 - (m * a + n * b) * h2

/-- **Every integer congruent to a value is a value** (*Disq. Arith.* Art. 155): if
$\mu m + \nu n = 1$ and $w \equiv v \pmod M$ for $v$ the value of $(\mu, \nu)$, then there is a Bezout pair
$(\mu', \nu')$ (namely $\mu' = \mu - k n$, $\nu' = \nu + k m$ with $v - w = k M$) with value exactly $w$. -/
@[kb "gauss1801" "Art. 154-155"]
theorem exists_bezout_art155Value_eq (a b c m n μ ν w : ℤ) (h : μ * m + ν * n = 1)
    (hw : w ≡ art155Value a b c m n μ ν [ZMOD (gaussForm a b c).eval m n]) :
    ∃ μ' ν' : ℤ, μ' * m + ν' * n = 1 ∧ art155Value a b c m n μ' ν' = w := by
  rw [Int.modEq_iff_dvd, eval_gaussForm] at hw
  obtain ⟨k, hk⟩ := hw
  refine ⟨μ - k * n, ν + k * m, by linear_combination h, ?_⟩
  unfold art155Value at hk ⊢
  linear_combination hk

/-! ### Art. 154: reduction to primitive representations -/

/-- **Pointwise reduction** (*Disq. Arith.* Art. 154): if $f(x, y) = M \ne 0$ and
$\mu = \gcd(x, y)$, then $\mu > 0$, $\mu^2 \mid M$, and $(x/\mu, y/\mu)$ is a primitive (coprime) representation
of $M/\mu^2$ by $f$, with $x = \mu (x/\mu)$, $y = \mu (y/\mu)$. -/
@[kb "gauss1801" "Art. 154"]
theorem representation_eq_gcd_mul_primitive (a b c x y M : ℤ) (hM : M ≠ 0)
    (hxy : (gaussForm a b c).eval x y = M) :
    0 < Int.gcd x y ∧ ((Int.gcd x y : ℤ) ^ 2 ∣ M) ∧ Int.gcd (x / Int.gcd x y) (y / Int.gcd x y) = 1 ∧
      (gaussForm a b c).eval (x / Int.gcd x y) (y / Int.gcd x y) = M / (Int.gcd x y : ℤ) ^ 2 ∧
      x = Int.gcd x y * (x / Int.gcd x y) ∧ y = Int.gcd x y * (y / Int.gcd x y) := by
  have hpos : 0 < Int.gcd x y := by
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with h0 | h0
    · exfalso
      rw [Int.gcd_eq_zero_iff] at h0
      obtain ⟨rfl, rfl⟩ := h0
      apply hM; rw [← hxy, eval_gaussForm]; ring
    · exact h0
  obtain ⟨m', n', hcop, hx, hy⟩ := Int.exists_gcd_one hpos
  set g : ℤ := (Int.gcd x y : ℤ) with hg
  have hgne : g ≠ 0 := by positivity
  have hxe : x / g = m' := by rw [hx]; exact Int.mul_ediv_cancel _ hgne
  have hye : y / g = n' := by rw [hy]; exact Int.mul_ediv_cancel _ hgne
  have hsq : M = g ^ 2 * (gaussForm a b c).eval m' n' := by
    rw [← hxy, hx, hy, eval_gaussForm, eval_gaussForm]; ring
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hgne
  refine ⟨hpos, ⟨_, hsq⟩, ?_, ?_, ?_, ?_⟩
  · rw [hxe, hye]; exact hcop
  · rw [hxe, hye, hsq]; exact (Int.mul_ediv_cancel_left _ hg2).symm
  · rw [hxe]; exact hx.trans (mul_comm _ _)
  · rw [hye]; exact hy.trans (mul_comm _ _)

/-- **All representations from primitive ones** (*Disq. Arith.* Art. 154): for
$M \ne 0$, the set of representations $\{(x, y) \mid f(x, y) = M\}$ of $M$ by Gauss's $(a, b, c)$ is the union,
over positive integers $\mu$ with $\mu^2 \mid M$, of the sets
$\{(\mu e, \mu f') \mid \gcd(e, f') = 1,\ f(e, f') = M / \mu^2\}$ (the representations $x = \mu e$, $y = \mu f'$
with $(e, f')$ primitive). -/
@[kb "gauss1801" "Art. 154"]
theorem representations_eq_iUnion_primitive (a b c M : ℤ) (hM : M ≠ 0) :
    {p : ℤ × ℤ | (gaussForm a b c).eval p.1 p.2 = M} =
      ⋃ (μ : ℕ) (_ : 0 < μ ∧ (μ : ℤ) ^ 2 ∣ M),
        {p : ℤ × ℤ | ∃ e f' : ℤ, Int.gcd e f' = 1 ∧ (gaussForm a b c).eval e f' = M / (μ : ℤ) ^ 2 ∧
          p = ((μ : ℤ) * e, (μ : ℤ) * f')} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hxy
    obtain ⟨hpos, hdvd, hcop, hev, hx, hy⟩ := representation_eq_gcd_mul_primitive a b c x y M hM hxy
    exact ⟨Int.gcd x y, ⟨hpos, hdvd⟩, _, _, hcop, hev, by rw [← hx, ← hy]⟩
  · rintro ⟨μ, ⟨hpos, ⟨q, hq⟩⟩, e, f', hcop, hev, hp⟩
    have hμ : (μ : ℤ) ^ 2 ≠ 0 := by positivity
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    have : M / (μ : ℤ) ^ 2 = q := by rw [hq]; exact Int.mul_ediv_cancel_left _ hμ
    rw [this] at hev
    rw [eval_gaussForm] at hev ⊢
    rw [hq, ← hev]; ring

/-! ### Art. 166: substitutions of determinant $\pm 1$ preserve properness -/

/-- **A substitution of determinant $\pm 1$ preserves the gcd of a vector** (the historical sources;
*Disq. Arith.* Art. 166, end): if $\alpha\delta - \beta\gamma = \pm 1$ then
$\gcd(\alpha m + \beta n, \gamma m + \delta n) = \gcd(m, n)$ (`Int.gcd`). -/
@[kb "gauss1801" "Art. 166"]
theorem gcd_substVector (α β γ δ m n : ℤ) (hdet : α * δ - β * γ = 1 ∨ α * δ - β * γ = -1) :
    Int.gcd (α * m + β * n) (γ * m + δ * n) = Int.gcd m n := by
  apply Nat.dvd_antisymm
  · rw [← Int.natCast_dvd_natCast]
    have hu := Int.gcd_dvd_left (a := α * m + β * n) (b := γ * m + δ * n)
    have hv := Int.gcd_dvd_right (a := α * m + β * n) (b := γ * m + δ * n)
    have hm : (Int.gcd (α * m + β * n) (γ * m + δ * n) : ℤ) ∣ m * (α * δ - β * γ) := by
      have : m * (α * δ - β * γ) = δ * (α * m + β * n) - β * (γ * m + δ * n) := by ring
      rw [this]; exact dvd_sub (dvd_mul_of_dvd_right hu _) (dvd_mul_of_dvd_right hv _)
    have hn : (Int.gcd (α * m + β * n) (γ * m + δ * n) : ℤ) ∣ n * (α * δ - β * γ) := by
      have : n * (α * δ - β * γ) = α * (γ * m + δ * n) - γ * (α * m + β * n) := by ring
      rw [this]; exact dvd_sub (dvd_mul_of_dvd_right hv _) (dvd_mul_of_dvd_right hu _)
    rcases hdet with h | h <;> rw [h] at hm hn <;> simp only [mul_one, mul_neg, dvd_neg] at hm hn <;>
      exact Int.dvd_coe_gcd hm hn
  · rw [← Int.natCast_dvd_natCast]
    have hm := Int.gcd_dvd_left (a := m) (b := n)
    have hn := Int.gcd_dvd_right (a := m) (b := n)
    exact Int.dvd_coe_gcd (dvd_add (dvd_mul_of_dvd_right hm _) (dvd_mul_of_dvd_right hn _))
      (dvd_add (dvd_mul_of_dvd_right hm _) (dvd_mul_of_dvd_right hn _))

/-- **Proper representations correspond under equivalence** (*Disq. Arith.* Art. 166,
end): if $F$ goes into $F'$ = `subst α β γ δ F` by $x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$ with
$\alpha\delta - \beta\gamma = \pm 1$, then $(m, n)$ is a proper representation of $M$ by $F'$ (value $M$ and
$\gcd(m, n) = 1$) iff its image $(\alpha m + \beta n, \gamma m + \delta n)$ is a proper representation of $M$
by $F$. -/
@[kb "gauss1801" "Art. 166"]
theorem proper_representation_subst_iff (F : BinQF) (α β γ δ m n M : ℤ)
    (hdet : α * δ - β * γ = 1 ∨ α * δ - β * γ = -1) :
    ((subst α β γ δ F).eval m n = M ∧ Int.gcd m n = 1) ↔
      (F.eval (α * m + β * n) (γ * m + δ * n) = M ∧
        Int.gcd (α * m + β * n) (γ * m + δ * n) = 1) := by
  rw [eval_subst, gcd_substVector α β γ δ m n hdet]

/-! ### Art. 179: the quotient $4D/m^2$ -/

/-- **The quotient $4D/m^2$ for negative determinant** (*Disq. Arith.* Art. 179):
let $B^2 - AC = -D$ with $D > 0$ and $m = \gcd(A, 2B, C)$ (`gcd3 A (2 * B) C`). Then $m^2 \mid 4D$ and
$N = 4D/m^2$ satisfies $N \equiv 0$ or $3 \pmod 4$ and $3 \le N$; so $N \ne 1, 2$ and only the cases $N > 4$,
$N = 4$, $N = 3$ occur. (Proof: $N = 4(A/m)(C/m) - (2B/m)^2$.) -/
@[kb "gauss1801" "Art. 179"]
theorem art179_quotient (A B C D : ℤ) (hD : 0 < D) (hdet : B ^ 2 - A * C = -D) :
    ((gcd3 A (2 * B) C : ℤ) ^ 2 ∣ 4 * D) ∧
      ((4 * D / (gcd3 A (2 * B) C : ℤ) ^ 2) % 4 = 0 ∨ (4 * D / (gcd3 A (2 * B) C : ℤ) ^ 2) % 4 = 3) ∧
      3 ≤ 4 * D / (gcd3 A (2 * B) C : ℤ) ^ 2 := by
  obtain ⟨⟨A', hA⟩, ⟨B', hB⟩, ⟨C', hC⟩⟩ := (dvd_gcd3 (gcd3 A (2 * B) C : ℤ) A (2 * B) C).mp dvd_rfl
  set m : ℤ := (gcd3 A (2 * B) C : ℤ) with hm
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hA hB hC
    simp only [zero_mul] at hA hB hC
    have : B = 0 := by omega
    subst hA hC; subst this
    simp at hdet; omega
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h4D : 4 * D = m ^ 2 * (4 * A' * C' - B' ^ 2) := by
    have : 4 * D = 4 * (A * C) - (2 * B) ^ 2 := by linear_combination 4 * hdet
    rw [this, hA, hB, hC]; ring
  have hN : 4 * D / m ^ 2 = 4 * A' * C' - B' ^ 2 := by rw [h4D]; exact Int.mul_ediv_cancel_left _ hm2
  refine ⟨⟨_, h4D⟩, ?_⟩
  rw [hN]
  have hpos : 0 < 4 * A' * C' - B' ^ 2 := by
    have : 0 < m ^ 2 * (4 * A' * C' - B' ^ 2) := by rw [← h4D]; omega
    exact pos_of_mul_pos_right this (by positivity) |> fun h => h
  have hmod : (4 * A' * C' - B' ^ 2) % 4 = 0 ∨ (4 * A' * C' - B' ^ 2) % 4 = 3 := by
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' B'
    · left
      have : 4 * A' * C' - B' ^ 2 = 4 * (A' * C' - k ^ 2) := by rw [hk]; ring
      omega
    · right
      have : 4 * A' * C' - B' ^ 2 = 4 * (A' * C' - k ^ 2 - k - 1) + 3 := by rw [hk]; ring
      omega
  exact ⟨hmod, by omega⟩

end QuadFormsKB.Historical.Gauss
