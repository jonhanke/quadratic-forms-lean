import QuadFormsKB.Historical.Gauss.Determinants
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Orders of Gauss's forms (Disquisitiones Arithmeticae, Arts. 226 and 256)

(Art. 226, the orders of forms of a given determinant)
(Art. 226, the number of orders) and (Art. 256 I, admissibility of the first coefficient of the
simplest form of an order).

Gauss's *order* of $(a, b, c)$ is `gaussOrder a b c` $= (b^2 - ac,\ \gcd(a,b,c),\ \gcd(a,2b,c))$
(`Determinants.lean`).

* `art226_derived_form`: if $m = \gcd(a,b,c) > 0$ then $(a, b, c) = m\,(a', b', c')$ with
  $\gcd(a', b', c') = 1$ and $b^2 - ac = m^2 (b'^2 - a'c')$; $\gcd(a, 2b, c) \in \{m, 2m\}$ according as the
  derived form $(a', b', c')$ is properly or improperly primitive; the derived form is unique
  (`art226_derived_form_unique`); an improperly primitive form has determinant $\equiv 1 \pmod 4$
  (`art226_improper_det_mod_four`).
* `art226_order_realized_iff`: the triples $(D, m, m')$ that are orders of a nonzero form are
  exactly those with $m > 0$, $m^2 \mid D$ and either $m' = m$, or $m' = 2m$ and $D/m^2 \equiv 1 \pmod 4$.
* `art226_number_of_orders`: for $D \ne 0$ the set `gaussOrdersOfDet D` of orders of determinant $D$
  is finite, of cardinality $\#\{m > 0 : m^2 \mid D\} + \#\{m > 0 : m^2 \mid D,\ D/m^2 \equiv 1 \pmod 4\}$;
  `art226_number_of_orders_product` is Gauss's product formula $(\mu+1)(\alpha+1)(\beta+1)\cdots$ resp.
  $(\mu+2)(\alpha+1)(\beta+1)\cdots$.
* `art256_admissible`: admissibility of $A$ for a simplest form $(A, B, C)$. Gauss's simplest forms satisfy
  $A \mid C$, made an explicit hypothesis: the note in the historical sources (integrality of $C$) alone does not suffice, e.g.
  $(2, 0, 3)$; see the docstring.

Everything is proved; nothing is assumed.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Arithmetic helpers -/

/-- Equal arguments give equal $\gcd_3$ (helper for rewriting arguments by `ring`). -/
theorem gcd3_congr {x y z x' y' z' : ℤ} (h1 : x = x') (h2 : y = y') (h3 : z = z') :
    gcd3 x y z = gcd3 x' y' z' := by
  subst h1 h2 h3; rfl

/-- **Scaling:** $\gcd(k a, k b, k c) = k \gcd(a, b, c)$ for a natural number $k$. -/
theorem gcd3_mul_left (k : ℕ) (a b c : ℤ) :
    gcd3 (k * a) (k * b) (k * c) = k * gcd3 a b c := by
  unfold gcd3
  have h1 : Int.gcd ((k : ℤ) * a) ((k : ℤ) * b) = k * Int.gcd a b := by
    rw [Int.gcd_mul_left]; simp
  rw [h1]
  push_cast
  rw [Int.gcd_mul_left]
  simp

/-- $\gcd(1, b, c) = 1$. -/
theorem gcd3_one_left (b c : ℤ) : gcd3 1 b c = 1 := by
  unfold gcd3; simp

/-- $\gcd(2, 1, c) = 1$. -/
theorem gcd3_two_one (c : ℤ) : gcd3 2 1 c = 1 := by
  unfold gcd3
  have : Int.gcd 2 1 = 1 := by decide
  simp [this]

/-- $\gcd(2, 2, 2k) = 2$. -/
theorem gcd3_two_two (k : ℤ) : gcd3 2 2 (2 * k) = 2 := by
  have h := gcd3_mul_left 2 1 1 k
  simp only [Nat.cast_ofNat] at h
  rw [gcd3_congr (x' := 2 * 1) (y' := 2 * 1) (z' := 2 * k) (by ring) (by ring) rfl, h, gcd3_one_left]

/-- $\gcd(a, b, c) > 0$ iff $(a, b, c) \ne (0, 0, 0)$. -/
theorem gcd3_pos_iff (a b c : ℤ) : 0 < gcd3 a b c ↔ (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    simp [gcd3] at h
  · intro h
    by_contra h0
    have h0 : gcd3 a b c = 0 := by omega
    obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 a b c) a b c).mp dvd_rfl
    rw [h0] at ha hb hc
    simp at ha hb hc
    tauto

/-- The determinant of a scaled form: $\det(k a, k b, k c) = k^2 \det(a, b, c)$. -/
theorem gaussDet_smul (k a b c : ℤ) : gaussDet (k * a) (k * b) (k * c) = k ^ 2 * gaussDet a b c := by
  unfold gaussDet; ring

/-- **Characterisation of equality of orders:** $\text{order}(a,b,c) = (D, m, m')$ iff the determinant is $D$, the
$\gcd(a,b,c)$ is $m$ and the $\gcd(a,2b,c)$ is $m'$. -/
theorem gaussOrder_eq_iff {a b c D : ℤ} {m m' : ℕ} :
    gaussOrder a b c = (D, m, m') ↔ gaussDet a b c = D ∧ gcd3 a b c = m ∧ gcd3 a (2 * b) c = m' := by
  unfold gaussOrder
  simp only [Prod.mk.injEq]

/-! ### Row : orders of forms of determinant $D$ -/

/-- **Dichotomy** (Gauss, *Disq. Arith.* Art. 226): $\gcd(a, 2b, c)$ is either
$\gcd(a, b, c)$ or $2 \gcd(a, b, c)$. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_gcd_dichotomy (a b c : ℤ) :
    gcd3 a (2 * b) c = gcd3 a b c ∨ gcd3 a (2 * b) c = 2 * gcd3 a b c := by
  have h1 : gcd3 a b c ∣ gcd3 a (2 * b) c := by
    rw [← Int.natCast_dvd_natCast, dvd_gcd3]
    obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 a b c) a b c).mp dvd_rfl
    exact ⟨ha, dvd_mul_of_dvd_right hb 2, hc⟩
  have h2 : gcd3 a (2 * b) c ∣ 2 * gcd3 a b c := by
    have e := gcd3_mul_left 2 a b c
    simp only [Nat.cast_ofNat] at e
    rw [← e, ← Int.natCast_dvd_natCast, dvd_gcd3]
    obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 a (2 * b) c) a (2 * b) c).mp dvd_rfl
    exact ⟨dvd_mul_of_dvd_right ha 2, hb, dvd_mul_of_dvd_right hc 2⟩
  obtain ⟨k, hk⟩ := h1
  rcases Nat.eq_zero_or_pos (gcd3 a b c) with h0 | hpos
  · left; rw [h0] at hk ⊢; simpa using hk
  · have hk2 : k ∣ 2 := by
      refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
      rw [hk, mul_comm 2 (gcd3 a b c)] at h2
      exact h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
    · left; simpa using hk
    · right; rw [hk]; ring

/-- **The derived form** (Gauss, *Disq. Arith.* Art. 226): if $m = \gcd(a, b, c) > 0$,
then $(a, b, c) = m\,(a', b', c')$ with $\gcd(a', b', c') = 1$, the determinants are related by
$b^2 - ac = m^2 (b'^2 - a'c')$, and
$\gcd(a, 2b, c) = m \cdot \gcd(a', 2b', c')$, so that $\gcd(a, 2b, c) = m$ iff the derived form is properly
primitive ($\gcd(a', 2b', c') = 1$) and $\gcd(a, 2b, c) = 2m$ iff it is improperly primitive
($\gcd(a', 2b', c') = 2$). -/
@[kb "gauss1801" "Art. 226"]
theorem art226_derived_form (a b c : ℤ) (hm : 0 < gcd3 a b c) :
    ∃ a' b' c' : ℤ, a = gcd3 a b c * a' ∧ b = gcd3 a b c * b' ∧ c = gcd3 a b c * c' ∧
      gcd3 a' b' c' = 1 ∧ gaussDet a b c = (gcd3 a b c : ℤ) ^ 2 * gaussDet a' b' c' ∧
      gcd3 a (2 * b) c = gcd3 a b c * gcd3 a' (2 * b') c' ∧
      (gcd3 a (2 * b) c = gcd3 a b c ↔ gcd3 a' (2 * b') c' = 1) ∧
      (gcd3 a (2 * b) c = 2 * gcd3 a b c ↔ gcd3 a' (2 * b') c' = 2) := by
  obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 a b c) a b c).mp dvd_rfl
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  have e := gcd3_mul_left (gcd3 a b c) a' b' c'
  rw [← ha', ← hb', ← hc'] at e
  have hg : gcd3 a' b' c' = 1 := by
    have : gcd3 a b c * gcd3 a' b' c' = gcd3 a b c * 1 := by rw [← e, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hm this
  have e2 := gcd3_mul_left (gcd3 a b c) a' (2 * b') c'
  have e2' : gcd3 a (2 * b) c = gcd3 a b c * gcd3 a' (2 * b') c' := by
    rw [← e2]
    exact gcd3_congr ha' (by linear_combination 2 * hb') hc'
  have hdi := art226_gcd_dichotomy a' b' c'
  rw [hg] at hdi
  refine ⟨a', b', c', ha', hb', hc', hg, ?_, e2', ?_, ?_⟩
  · have := gaussDet_smul (gcd3 a b c) a' b' c'
    rw [← ha', ← hb', ← hc'] at this
    exact this
  · rw [e2']
    constructor
    · intro h; exact Nat.eq_of_mul_eq_mul_left hm (by rw [h, mul_one])
    · intro h; rw [h, mul_one]
  · rw [e2']
    constructor
    · intro h; exact Nat.eq_of_mul_eq_mul_left hm (h.trans (mul_comm _ _))
    · intro h; rw [h]; exact mul_comm _ _

/-- **Uniqueness of the derived form** (Gauss, *Disq. Arith.* Art. 226): if
$(a, b, c) = k\,(a', b', c')$ with $\gcd(a', b', c') = 1$ and $\gcd(a, b, c) > 0$, then
$k = \gcd(a, b, c)$; consequently two such decompositions of $(a, b, c)$ have the same multiplier and the same
derived form. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_derived_form_unique {a b c a' b' c' a'' b'' c'' : ℤ} {k k' : ℕ}
    (hpos : 0 < gcd3 a b c)
    (h1 : a = k * a' ∧ b = k * b' ∧ c = k * c') (g1 : gcd3 a' b' c' = 1)
    (h2 : a = k' * a'' ∧ b = k' * b'' ∧ c = k' * c'') (g2 : gcd3 a'' b'' c'' = 1) :
    k = k' ∧ a' = a'' ∧ b' = b'' ∧ c' = c'' := by
  have mult : ∀ {k : ℕ} {a' b' c' : ℤ}, a = k * a' ∧ b = k * b' ∧ c = k * c' → gcd3 a' b' c' = 1 →
      k = gcd3 a b c := by
    intro k a' b' c' ⟨ha, hb, hc⟩ g
    have := gcd3_mul_left k a' b' c'
    rw [← ha, ← hb, ← hc, g, mul_one] at this
    exact this.symm
  have hk := mult h1 g1
  have hk' := mult h2 g2
  have hkk : k = k' := hk.trans hk'.symm
  subst hkk
  have hk0 : (k : ℤ) ≠ 0 := by
    have : 0 < k := hk ▸ hpos
    exact_mod_cast this.ne'
  obtain ⟨ha1, hb1, hc1⟩ := h1
  obtain ⟨ha2, hb2, hc2⟩ := h2
  exact ⟨rfl, mul_left_cancel₀ hk0 (ha1.symm.trans ha2), mul_left_cancel₀ hk0 (hb1.symm.trans hb2),
    mul_left_cancel₀ hk0 (hc1.symm.trans hc2)⟩

/-- **Improperly primitive forms have determinant $\equiv 1 \pmod 4$** (Gauss, *Disq. Arith.* Art. 226, the historical sources
): if $\gcd(a, b, c) = 1$ and $\gcd(a, 2b, c) = 2$ then $a$ and $c$ are even, $b$ is odd and
$b^2 - ac \equiv 1 \pmod 4$. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_improper_det_mod_four {a b c : ℤ} (h1 : gcd3 a b c = 1) (h2 : gcd3 a (2 * b) c = 2) :
    Even a ∧ Odd b ∧ Even c ∧ gaussDet a b c % 4 = 1 := by
  obtain ⟨ha, hb2, hc⟩ := (dvd_gcd3 2 a (2 * b) c).mp (by rw [h2]; norm_num)
  have hb : ¬ (2 : ℤ) ∣ b := by
    intro hb
    have := (dvd_gcd3 2 a b c).mpr ⟨ha, hb, hc⟩
    rw [h1] at this
    norm_num at this
  have hbo : Odd b := by
    rcases Int.even_or_odd b with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hb
    · exact ho
  obtain ⟨x, hx⟩ := ha
  obtain ⟨z, hz⟩ := hc
  obtain ⟨y, hy⟩ := hbo
  refine ⟨⟨x, by omega⟩, ⟨y, hy⟩, ⟨z, by omega⟩, ?_⟩
  have : gaussDet a b c = 4 * (y * y + y - x * z) + 1 := by
    unfold gaussDet; rw [hx, hz, hy]; ring
  rw [this]; omega

/-- **Realization, properly primitive derived form:** the order of $m\,(1, 0, -e) = (m, 0, -me)$ is
$(m^2 e,\ m,\ m)$. -/
theorem gaussOrder_proper_rep (m : ℕ) (e : ℤ) :
    gaussOrder m 0 (-(m * e)) = ((m : ℤ) ^ 2 * e, m, m) := by
  rw [gaussOrder_eq_iff]
  refine ⟨by unfold gaussDet; ring, ?_, ?_⟩
  · rw [gcd3_congr (x' := (m : ℤ) * 1) (y' := (m : ℤ) * 0) (z' := (m : ℤ) * (-e)) (by ring) (by ring) (by ring),
      gcd3_mul_left, gcd3_one_left, mul_one]
  · rw [gcd3_congr (x' := (m : ℤ) * 1) (y' := (m : ℤ) * 0) (z' := (m : ℤ) * (-e)) (by ring) (by ring) (by ring),
      gcd3_mul_left, gcd3_one_left, mul_one]

/-- **Realization, improperly primitive derived form:** the order of $m\,(2, 1, 2k) = (2m, m, 2mk)$ is
$(m^2 (1 - 4k),\ m,\ 2m)$. -/
theorem gaussOrder_improper_rep (m : ℕ) (k : ℤ) :
    gaussOrder (2 * (m : ℤ)) m (2 * m * k) = ((m : ℤ) ^ 2 * (1 - 4 * k), m, 2 * m) := by
  rw [gaussOrder_eq_iff]
  refine ⟨by unfold gaussDet; ring, ?_, ?_⟩
  · rw [gcd3_congr (x' := (m : ℤ) * 2) (y' := (m : ℤ) * 1) (z' := (m : ℤ) * (2 * k)) (by ring) (by ring) (by ring),
      gcd3_mul_left, gcd3_two_one, mul_one]
  · rw [gcd3_congr (x' := (m : ℤ) * 2) (y' := (m : ℤ) * 2) (z' := (m : ℤ) * (2 * k)) (by ring) (by ring) (by ring),
      gcd3_mul_left, gcd3_two_two]
    ring

/-- **Which triples are orders** (Gauss, *Disq. Arith.* Art. 226): $(D, m, m')$ is the
order of some nonzero form $(a, b, c)$ iff $m > 0$, $m^2 \mid D$ and either $m' = m$ (the form is derived from a
properly primitive form of determinant $D/m^2$) or $m' = 2m$ and $D/m^2 \equiv 1 \pmod 4$ (derived from an improperly
primitive form of determinant $D/m^2$). The properly primitive order is $m = 1 = m'$, the improperly primitive one
$m = 1$, $m' = 2$. Realized by $m\,(1, 0, -D/m^2)$ and $m\,(2, 1, (1 - D/m^2)/2)$. (Extra: here
"nonzero" is $(a, b, c) \ne (0, 0, 0)$, which is needed for $\gcd(a, b, c) > 0$; the determinant $D = 0$ is
allowed.) -/
@[kb "gauss1801" "Art. 226"]
theorem art226_order_realized_iff (D : ℤ) (m m' : ℕ) :
    (∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ gaussOrder a b c = (D, m, m')) ↔
      0 < m ∧ (m : ℤ) ^ 2 ∣ D ∧ (m' = m ∨ (m' = 2 * m ∧ D / (m : ℤ) ^ 2 % 4 = 1)) := by
  constructor
  · rintro ⟨a, b, c, hne, hord⟩
    rw [gaussOrder_eq_iff] at hord
    obtain ⟨hd, hm, hm'⟩ := hord
    have hpos := (gcd3_pos_iff a b c).2 hne
    obtain ⟨a', b', c', -, -, -, g1, hdet, hprod, hp, hi⟩ := art226_derived_form a b c hpos
    subst hm hm' hd
    have hm0 : ((gcd3 a b c : ℕ) : ℤ) ^ 2 ≠ 0 := by positivity
    refine ⟨hpos, ⟨_, hdet⟩, ?_⟩
    rcases art226_gcd_dichotomy a b c with h | h
    · left; exact h
    · right
      refine ⟨h, ?_⟩
      have h2 : gcd3 a' (2 * b') c' = 2 := (hi.mp h)
      rw [hdet, Int.mul_ediv_cancel_left _ hm0]
      exact (art226_improper_det_mod_four g1 h2).2.2.2
  · rintro ⟨hm, ⟨e, he⟩, hcases⟩
    have hm0 : (m : ℤ) ^ 2 ≠ 0 := by positivity
    have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    rcases hcases with hh | ⟨hh, h4⟩
    · refine ⟨m, 0, -(m * e), Or.inl hmz, ?_⟩
      rw [gaussOrder_proper_rep, he, hh]
    · rw [he, Int.mul_ediv_cancel_left _ hm0] at h4
      refine ⟨2 * m, m, 2 * m * (-(e / 4)), Or.inl (by positivity), ?_⟩
      rw [gaussOrder_improper_rep, he, hh]
      have hk : (1 : ℤ) - 4 * -(e / 4) = e := by omega
      rw [hk]

/-! ### Row : the number of orders -/

/-- **The set of orders of determinant $D$** (Gauss, *Disq. Arith.* Art. 226): the
triples $(D, \gcd(a,b,c), \gcd(a,2b,c))$ over all nonzero forms $(a, b, c)$ of determinant $D$. -/
def gaussOrdersOfDet (D : ℤ) : Set (ℤ × ℕ × ℕ) :=
  {o | ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ gaussDet a b c = D ∧ gaussOrder a b c = o}

/-- Membership in `gaussOrdersOfDet`: the classification of `art226_order_realized_iff`. -/
theorem mem_gaussOrdersOfDet {D : ℤ} {o : ℤ × ℕ × ℕ} :
    o ∈ gaussOrdersOfDet D ↔ o.1 = D ∧ 0 < o.2.1 ∧ (o.2.1 : ℤ) ^ 2 ∣ D ∧
      (o.2.2 = o.2.1 ∨ (o.2.2 = 2 * o.2.1 ∧ D / (o.2.1 : ℤ) ^ 2 % 4 = 1)) := by
  obtain ⟨d, m, m'⟩ := o
  constructor
  · rintro ⟨a, b, c, hne, hdet, hord⟩
    have hd : d = D := by
      have := (gaussOrder_eq_iff.mp hord).1
      rw [← this, hdet]
    subst hd
    exact ⟨rfl, (art226_order_realized_iff d m m').mp ⟨a, b, c, hne, hord⟩⟩
  · rintro ⟨rfl, h⟩
    obtain ⟨a, b, c, hne, hord⟩ := (art226_order_realized_iff d m m').mpr h
    exact ⟨a, b, c, hne, (gaussOrder_eq_iff.mp hord).1, hord⟩

/-- The natural numbers $m > 0$ with $m^2 \mid D$ (for $D \ne 0$ these are all of them: $m \le |D|$). -/
def gaussSquareDivisors (D : ℤ) : Finset ℕ :=
  (Finset.Icc 1 D.natAbs).filter fun m => (m : ℤ) ^ 2 ∣ D

/-- The natural numbers $m > 0$ with $m^2 \mid D$ and $D / m^2 \equiv 1 \pmod 4$. -/
def gaussSquareDivisorsOneModFour (D : ℤ) : Finset ℕ :=
  (gaussSquareDivisors D).filter fun m => D / (m : ℤ) ^ 2 % 4 = 1

theorem mem_gaussSquareDivisors {D : ℤ} (hD : D ≠ 0) {m : ℕ} :
    m ∈ gaussSquareDivisors D ↔ 0 < m ∧ (m : ℤ) ^ 2 ∣ D := by
  unfold gaussSquareDivisors
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have h3 := Int.natAbs_dvd_natAbs.mpr h2
    simp only [Int.natAbs_pow, Int.natAbs_natCast] at h3
    have h4 := Nat.le_of_dvd (Int.natAbs_pos.mpr hD) h3
    exact (Nat.le_self_pow two_ne_zero m).trans h4

theorem mem_gaussSquareDivisorsOneModFour {D : ℤ} (hD : D ≠ 0) {m : ℕ} :
    m ∈ gaussSquareDivisorsOneModFour D ↔ 0 < m ∧ (m : ℤ) ^ 2 ∣ D ∧ D / (m : ℤ) ^ 2 % 4 = 1 := by
  unfold gaussSquareDivisorsOneModFour
  rw [Finset.mem_filter, mem_gaussSquareDivisors hD, and_assoc]

/-- The finite set of orders of determinant $D$, as images of the two counting sets. -/
def gaussOrdersFinset (D : ℤ) : Finset (ℤ × ℕ × ℕ) :=
  (gaussSquareDivisors D).image (fun m => (D, m, m)) ∪
    (gaussSquareDivisorsOneModFour D).image (fun m => (D, m, 2 * m))

theorem gaussOrdersOfDet_eq {D : ℤ} (hD : D ≠ 0) :
    gaussOrdersOfDet D = ↑(gaussOrdersFinset D) := by
  ext ⟨d, m, m'⟩
  rw [mem_gaussOrdersOfDet, Finset.mem_coe, gaussOrdersFinset, Finset.mem_union, Finset.mem_image,
    Finset.mem_image]
  constructor
  · rintro ⟨rfl, hm, hdv, h | ⟨h, h4⟩⟩
    · exact Or.inl ⟨m, (mem_gaussSquareDivisors hD).mpr ⟨hm, hdv⟩, by simp only at h; rw [h]⟩
    · exact Or.inr ⟨m, (mem_gaussSquareDivisorsOneModFour hD).mpr ⟨hm, hdv, h4⟩, by simp only at h; rw [h]⟩
  · rintro (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩)
    · simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl, rfl⟩ := hxe
      obtain ⟨h1, h2⟩ := (mem_gaussSquareDivisors hD).mp hx
      exact ⟨rfl, h1, h2, Or.inl rfl⟩
    · simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl, rfl⟩ := hxe
      obtain ⟨h1, h2, h3⟩ := (mem_gaussSquareDivisorsOneModFour hD).mp hx
      exact ⟨rfl, h1, h2, Or.inr ⟨rfl, h3⟩⟩

/-- **The number of orders of determinant $D$** (Gauss, *Disq. Arith.* Art. 226, sum
form): for $D \ne 0$ the set of orders of determinant $D$ is finite, with
$$\#\{m > 0 : m^2 \mid D\} + \#\{m > 0 : m^2 \mid D,\ D/m^2 \equiv 1 \pmod 4\}$$
elements (one properly primitive order and one improperly primitive order, each derived with multiplier $m$,
for each such $m$). For the product formula see `art226_number_of_orders_product`. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_number_of_orders {D : ℤ} (hD : D ≠ 0) :
    (gaussOrdersOfDet D).Finite ∧
      (gaussOrdersOfDet D).ncard =
        (gaussSquareDivisors D).card + (gaussSquareDivisorsOneModFour D).card := by
  rw [gaussOrdersOfDet_eq hD]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset, gaussOrdersFinset, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · intro x y h
    simp only [Prod.mk.injEq] at h
    omega
  · intro x y h
    simp only [Prod.mk.injEq] at h
    exact h.2.1
  · rw [Finset.disjoint_left]
    intro o ho ho'
    rw [Finset.mem_image] at ho ho'
    obtain ⟨x, hx, rfl⟩ := ho
    obtain ⟨y, hy, hy'⟩ := ho'
    simp only [Prod.mk.injEq] at hy'
    obtain ⟨-, h1, h2⟩ := hy'
    have := ((mem_gaussSquareDivisorsOneModFour hD).mp hy).1
    omega

/-! #### The product formula -/

/-- If $D'$ is squarefree and $m^2 \mid D' s^2$ then $m \mid s$. -/
theorem sq_dvd_of_squarefree {n m s : ℕ} (hn : Squarefree n) (hs : 0 < s)
    (h : m ^ 2 ∣ n * s ^ 2) : m ∣ s := by
  obtain ⟨m', s', hcop, hm, hs'⟩ := Nat.exists_coprime m s
  set g := Nat.gcd m s with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hs
  have hg2 : 0 < g ^ 2 := by positivity
  rw [hm, hs'] at h
  have h' : m' ^ 2 * g ^ 2 ∣ (n * s' ^ 2) * g ^ 2 := by
    convert h using 1 <;> ring
  have h'' : m' ^ 2 ∣ n * s' ^ 2 := Nat.dvd_of_mul_dvd_mul_right hg2 h'
  have h3 : m' ^ 2 ∣ n := (Nat.Coprime.pow 2 2 hcop).dvd_of_dvd_mul_right h''
  have h4 : IsUnit m' := hn m' (by rw [← pow_two]; exact h3)
  have h5 : m' = 1 := Nat.isUnit_iff.mp h4
  rw [hm, h5, one_mul]
  exact Nat.gcd_dvd_right m s

/-- For $s > 0$ and $D'$ squarefree, the count set of `gaussSquareDivisors (D' s^2)` is the set of divisors of
$s$. -/
theorem gaussSquareDivisors_eq_divisors {D' : ℤ} (hD' : Squarefree D') {s : ℕ} (hs : 0 < s) :
    gaussSquareDivisors (D' * (s : ℤ) ^ 2) = s.divisors := by
  have hD'0 : D' ≠ 0 := hD'.ne_zero
  have hD : D' * (s : ℤ) ^ 2 ≠ 0 := by positivity
  ext m
  rw [mem_gaussSquareDivisors hD, Nat.mem_divisors]
  constructor
  · rintro ⟨hm, hdv⟩
    refine ⟨sq_dvd_of_squarefree (Int.squarefree_natAbs.mpr hD') hs ?_, hs.ne'⟩
    have := Int.natAbs_dvd_natAbs.mpr hdv
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  · rintro ⟨⟨t, ht⟩, -⟩
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    refine ⟨hm, ⟨D' * (t : ℤ) ^ 2, ?_⟩⟩
    have : (s : ℤ) = m * t := by exact_mod_cast ht
    rw [this]; ring

/-- $D' t^2 \equiv 1 \pmod 4$ iff $D' \equiv 1 \pmod 4$ and $t$ is odd. -/
theorem mul_sq_mod_four (D' : ℤ) (t : ℕ) :
    (D' * (t : ℤ) ^ 2) % 4 = 1 ↔ D' % 4 = 1 ∧ Odd t := by
  rcases Nat.even_or_odd' t with ⟨r, rfl | rfl⟩
  · have : D' * ((2 * r : ℕ) : ℤ) ^ 2 = 4 * (D' * r ^ 2) := by push_cast; ring
    rw [this]
    simp [Nat.not_odd_iff_even]
  · have : D' * ((2 * r + 1 : ℕ) : ℤ) ^ 2 = D' + 4 * (D' * (r ^ 2 + r)) := by push_cast; ring
    rw [this]
    simp

/-- A divisor of $2^\mu u$ ($u$ odd) is odd iff it divides $u$... in the form: for odd $t$, $t \mid 2^\mu u$ iff
$t \mid u$. -/
theorem odd_dvd_two_pow_mul {t u μ : ℕ} (ht : Odd t) : t ∣ 2 ^ μ * u ↔ t ∣ u := by
  have hc : Nat.Coprime t (2 ^ μ) := Nat.Coprime.pow_right μ (Nat.coprime_two_right.mpr ht)
  exact ⟨fun h => hc.dvd_of_dvd_mul_left h, fun h => h.mul_left _⟩

/-- The count set `gaussSquareDivisorsOneModFour` for $D = D' s^2$. -/
theorem card_gaussSquareDivisorsOneModFour {D' : ℤ} (hD' : Squarefree D') {s μ u : ℕ} (hu : Odd u)
    (hs : s = 2 ^ μ * u) :
    (gaussSquareDivisorsOneModFour (D' * (s : ℤ) ^ 2)).card =
      if D' % 4 = 1 then u.divisors.card else 0 := by
  have hu0 : 0 < u := hu.pos
  have hs0 : 0 < s := by rw [hs]; positivity
  have hD'0 : D' ≠ 0 := hD'.ne_zero
  have hD : D' * (s : ℤ) ^ 2 ≠ 0 := by positivity
  have hmem : ∀ m, m ∈ gaussSquareDivisorsOneModFour (D' * (s : ℤ) ^ 2) ↔
      m ∈ s.divisors ∧ D' % 4 = 1 ∧ Odd (s / m) := by
    intro m
    unfold gaussSquareDivisorsOneModFour
    rw [Finset.mem_filter, gaussSquareDivisors_eq_divisors hD' hs0]
    constructor
    · rintro ⟨hm, h⟩
      have hm' := hm
      obtain ⟨t, ht⟩ := (Nat.mem_divisors.mp hm).1
      have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
      have hst : s / m = t := by rw [ht]; exact Nat.mul_div_cancel_left t hmpos
      have hmz : (m : ℤ) ^ 2 ≠ 0 := by positivity
      have hq : D' * (s : ℤ) ^ 2 / (m : ℤ) ^ 2 = D' * (t : ℤ) ^ 2 := by
        have : D' * (s : ℤ) ^ 2 = (m : ℤ) ^ 2 * (D' * (t : ℤ) ^ 2) := by
          rw [ht]; push_cast; ring
        rw [this, Int.mul_ediv_cancel_left _ hmz]
      rw [hq, mul_sq_mod_four] at h
      exact ⟨hm', h.1, by rw [hst]; exact h.2⟩
    · rintro ⟨hm, h4, hodd⟩
      refine ⟨hm, ?_⟩
      obtain ⟨t, ht⟩ := (Nat.mem_divisors.mp hm).1
      have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
      have hst : s / m = t := by rw [ht]; exact Nat.mul_div_cancel_left t hmpos
      have hmz : (m : ℤ) ^ 2 ≠ 0 := by positivity
      have hq : D' * (s : ℤ) ^ 2 / (m : ℤ) ^ 2 = D' * (t : ℤ) ^ 2 := by
        have : D' * (s : ℤ) ^ 2 = (m : ℤ) ^ 2 * (D' * (t : ℤ) ^ 2) := by
          rw [ht]; push_cast; ring
        rw [this, Int.mul_ediv_cancel_left _ hmz]
      rw [hq, mul_sq_mod_four]
      exact ⟨h4, by rw [hst] at hodd; exact hodd⟩
  by_cases h4 : D' % 4 = 1
  · rw [if_pos h4]
    refine Finset.card_nbij' (fun m => s / m) (fun t => s / t) ?_ ?_ ?_ ?_
    · intro m hm
      have hm' := (hmem m).mp (Finset.mem_coe.mp hm)
      obtain ⟨hmd, -, hodd⟩ := hm'
      rw [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨?_, hu0.ne'⟩
      rw [← odd_dvd_two_pow_mul (μ := μ) hodd, ← hs]
      exact Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hmd).1
    · intro t ht
      rw [Finset.mem_coe, Nat.mem_divisors] at ht
      have htodd : Odd t := hu.of_dvd_nat ht.1
      have hts : t ∣ s := by rw [hs]; exact ht.1.mul_left _
      rw [Finset.mem_coe, hmem]
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hts, hs0.ne'⟩, h4, ?_⟩
      rw [Nat.div_div_self hts hs0.ne']
      exact htodd
    · intro m hm
      have := (hmem m).mp (Finset.mem_coe.mp hm)
      exact Nat.div_div_self (Nat.mem_divisors.mp this.1).1 hs0.ne'
    · intro t ht
      rw [Finset.mem_coe, Nat.mem_divisors] at ht
      have hts : t ∣ s := by rw [hs]; exact ht.1.mul_left _
      exact Nat.div_div_self hts hs0.ne'
  · rw [if_neg h4, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro m hm
    exact h4 ((hmem m).mp hm).2.1

/-- **Gauss's formula for the number of orders** (*Disq. Arith.* Art. 226, product form):
write $D = D'\,s^2$ with $D'$ squarefree and $s = 2^{\mu} u$, $u$ odd, $u = A^{\alpha} B^{\beta} \cdots$ (distinct
odd primes $A, B, \ldots$), so $D = D' 2^{2\mu} A^{2\alpha} B^{2\beta} \cdots$. Then the number of orders of
determinant $D$ is $(\mu+1)(\alpha+1)(\beta+1)\cdots$ if $D' \not\equiv 1 \pmod 4$ (i.e. $D' \equiv 2, 3$) and
$(\mu+2)(\alpha+1)(\beta+1)\cdots$ if $D' \equiv 1 \pmod 4$. Here
$(\alpha+1)(\beta+1)\cdots$ is `∏ p ∈ u.primeFactors, (u.factorization p + 1)`. (Proved; Gauss states it without
proof. Nothing differs from the source; the case $D' \equiv 0 \pmod 4$ does not occur for squarefree $D'$.) -/
@[kb "gauss1801" "Art. 226"]
theorem art226_number_of_orders_product {D' : ℤ} (hD' : Squarefree D') {s μ u : ℕ} (hu : Odd u)
    (hs : s = 2 ^ μ * u) :
    (gaussOrdersOfDet (D' * (s : ℤ) ^ 2)).ncard =
      (if D' % 4 = 1 then μ + 2 else μ + 1) * ∏ p ∈ u.primeFactors, (u.factorization p + 1) := by
  have hu0 : 0 < u := hu.pos
  have hs0 : 0 < s := by rw [hs]; positivity
  have hD'0 : D' ≠ 0 := hD'.ne_zero
  have hD : D' * (s : ℤ) ^ 2 ≠ 0 := by positivity
  rw [(art226_number_of_orders hD).2, gaussSquareDivisors_eq_divisors hD' hs0,
    card_gaussSquareDivisorsOneModFour hD' hu hs, ← Nat.card_divisors hu0.ne']
  have hcop : Nat.Coprime (2 ^ μ) u := Nat.Coprime.pow_left μ (Nat.coprime_two_left.mpr hu)
  have hcard : s.divisors.card = (μ + 1) * u.divisors.card := by
    rw [hs, hcop.card_divisors_mul, Nat.divisors_prime_pow Nat.prime_two]
    simp
  rw [hcard]
  split_ifs <;> ring

/-! ### Row : admissibility (Art. 256 I) -/

/-- **The shape of a simplest form of an order** (Gauss, *Disq. Arith.* Art. 256): $(A, B, C)$ with $A > 0$,
$A \mid C$ and either $B = 0$ or $2B = A$. These are the forms $m\,(1, 0, -D/m^2) = (m, 0, -D/m)$ (order
$(D, m, m)$) and $m\,(2, 1, (1 - D/m^2)/2)$ (order $(D, m, 2m)$), which are the simplest forms of the orders of
`art226_order_realized_iff`; in both cases $A = \gcd(A, 2B, C)$. -/
def IsGaussSimplestForm (A B C : ℤ) : Prop := 0 < A ∧ A ∣ C ∧ (B = 0 ∨ 2 * B = A)

/-- **Admissibility of the first coefficient of the simplest form of an order** (Gauss, *Disq. Arith.* Art. 256 I,
the historical sources). Let $(A, B, C)$ be of simplest form (`IsGaussSimplestForm`: $A > 0$, $A \mid C$,
$B = 0$ or $2B = A$) and $D = B^2 - AC$.

* If $B = 0$ (the order is derived from a properly primitive order): $\gcd(A, 2B, C) = \gcd(A, B, C) = A$ and
  $A^2 \mid D$.
* If $2B = A$ (improperly primitive order, or derived from an improperly primitive order): $A$ is even,
  $\gcd(A, 2B, C) = A$, $\gcd(A, B, C) = A/2$, $B^2 = A^2/4 \mid D$ and $D/(A^2/4) = 4D/A^2 \equiv 1 \pmod 4$.

**Comparison with the historical sources:** their statement, and Gauss's, take the form to be the simplest form of an
order, and such a form has $A \mid C$ (it is $m(1,0,-D/m^2)$ resp. $m(2,1,(1 - D/m^2)/2)$ with $D/m^2 \equiv 1
\pmod 4$). Their note says the claim follows merely from $C = (B^2 - D)/A$ being an integer with $B = 0$ or
$B = A/2$; that is not enough without $A \mid C$: for $(A, B, C) = (2, 0, 3)$, $D = -6$ and $A^2 = 4 \nmid 6$. We
therefore include $A \mid C$ in the hypothesis (`IsGaussSimplestForm`). -/
@[kb "gauss1801" "Art. 256"]
theorem art256_admissible {A B C : ℤ} (h : IsGaussSimplestForm A B C) :
    (B = 0 → (gcd3 A (2 * B) C : ℤ) = A ∧ (gcd3 A B C : ℤ) = A ∧ A ^ 2 ∣ gaussDet A B C) ∧
    (2 * B = A → Even A ∧ (gcd3 A (2 * B) C : ℤ) = A ∧ 2 * (gcd3 A B C : ℤ) = A ∧
      B ^ 2 ∣ gaussDet A B C ∧ gaussDet A B C / B ^ 2 % 4 = 1 ∧
      4 * gaussDet A B C / A ^ 2 = gaussDet A B C / B ^ 2) := by
  obtain ⟨hA, ⟨k, hk⟩, hB⟩ := h
  constructor
  · rintro rfl
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hA.le
    subst hk
    have e : gcd3 (n : ℤ) (2 * 0) (n * k) = n := by
      rw [gcd3_congr (x' := (n : ℤ) * 1) (y' := (n : ℤ) * 0) (z' := (n : ℤ) * k) (by ring) (by ring) rfl,
        gcd3_mul_left, gcd3_one_left, mul_one]
    have e' : gcd3 (n : ℤ) 0 (n * k) = n := by
      rw [gcd3_congr (x' := (n : ℤ) * 1) (y' := (n : ℤ) * 0) (z' := (n : ℤ) * k) (by ring) (by ring) rfl,
        gcd3_mul_left, gcd3_one_left, mul_one]
    refine ⟨by rw [e], by rw [e'], ⟨-k, ?_⟩⟩
    unfold gaussDet; ring
  · intro h2
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, B = b := Int.eq_ofNat_of_zero_le (by omega)
    have hA' : A = 2 * b := by omega
    subst hA'
    subst hk
    have e1 : gcd3 (2 * (b : ℤ)) b (2 * b * k) = b := by
      rw [gcd3_congr (x' := (b : ℤ) * 2) (y' := (b : ℤ) * 1) (z' := (b : ℤ) * (2 * k)) (by ring) (by ring)
        (by ring), gcd3_mul_left, gcd3_two_one, mul_one]
    have e2 : gcd3 (2 * (b : ℤ)) (2 * b) (2 * b * k) = 2 * b := by
      rw [gcd3_congr (x' := (b : ℤ) * 2) (y' := (b : ℤ) * 2) (z' := (b : ℤ) * (2 * k)) (by ring) (by ring)
        (by ring), gcd3_mul_left, gcd3_two_two]
      ring
    have hD : gaussDet (2 * (b : ℤ)) b (2 * b * k) = (b : ℤ) ^ 2 * (1 - 4 * k) := by
      unfold gaussDet; ring
    have hb0 : (b : ℤ) ^ 2 ≠ 0 := by
      have : (0 : ℤ) < 2 * b := hA
      have : (b : ℤ) ≠ 0 := by omega
      positivity
    refine ⟨⟨b, by ring⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e2]; push_cast; ring
    · rw [e1]
    · rw [hD]; exact ⟨_, rfl⟩
    · rw [hD, Int.mul_ediv_cancel_left _ hb0]; omega
    · rw [hD, Int.mul_ediv_cancel_left _ hb0]
      have : 4 * ((b : ℤ) ^ 2 * (1 - 4 * k)) = (2 * (b : ℤ)) ^ 2 * (1 - 4 * k) := by ring
      rw [this, Int.mul_ediv_cancel_left _ (by positivity)]

end QuadFormsKB.Historical.Gauss
