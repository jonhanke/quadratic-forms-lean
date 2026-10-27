/-
# Classical special cases over $\mathbb Q$: the values of $x_0^2 - 2x_1^2$

**Layer:** $\mathbb Z$, $\mathbb Q$ (elementary).

The analogue, for $x_0^2 - 2x_1^2$ (the norm form of $\mathbb Z[\sqrt2]$), of Fermat's criterion for sums of two squares
(Mathlib `Nat.eq_sq_add_sq_iff`):

* **the criterion** (`pell2_value_iff`, `pell2_value_int_iff`): an integer $m$ (of either sign) is a value
  $x_0^2 - 2x_1^2$ with $x_0, x_1\in\mathbb Z$ iff every prime $q\equiv\pm3\pmod8$ divides $m$ to an even power;
* **rational equals integral** (`pell2_value_rat_iff`): an integer is a value over $\mathbb Q$ iff it is one over
  $\mathbb Z$.

The proof is elementary and follows the arithmetic of $\mathbb Z[\sqrt2]$ without constructing it: the norm is
multiplicative (`pell2_value_mul`); $1+\sqrt2$ has norm $-1$, so values come with either sign (`pell2_value_neg_iff`);
$2 = 2^2 - 2\cdot1^2$ ramifies; a prime $p\equiv\pm1\pmod8$ splits, i.e. is a value (`pell2_value_prime`, from $2$ being a
square mod $p$ and Thue's lemma); a prime $q\equiv\pm3\pmod8$ is inert: $q\mid x_0^2-2x_1^2$ forces $q\mid x_0$, $q\mid x_1$
(`even_padicValNat_of_pell2_value`).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Tamagawa.Classical

/-- **The values of $x_0^2-2x_1^2$ are closed under multiplication:**
$(a^2-2b^2)(c^2-2d^2) = (ac+2bd)^2 - 2(ad+bc)^2$ (the norm of $\mathbb Z[\sqrt2]$ is multiplicative). -/
theorem pell2_value_mul {m n : ℤ} (hm : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m)
    (hn : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = n) : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m * n := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c + 2 * b * d, a * d + b * c, by ring⟩

/-- **Values come with either sign:** $-(x_0^2-2x_1^2) = (x_0+2x_1)^2 - 2(x_0+x_1)^2$ ($1+\sqrt2$ has norm $-1$). -/
theorem pell2_value_neg_iff (m : ℤ) :
    (∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = -m) ↔ ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m := by
  have key : ∀ n : ℤ, (∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = n) → ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = -n := by
    rintro n ⟨x, y, rfl⟩
    exact ⟨x + 2 * y, x + y, by ring⟩
  exact ⟨fun h => by simpa using key _ h, key m⟩

/-- If $x^2=2y^2$ in $\mathbb Z$ then $x=0$ (infinite descent on $|x|$). -/
theorem pell2_sq_eq_two_sq_imp_zero : ∀ (n : ℕ) (x y : ℤ), x.natAbs = n → x ^ 2 = 2 * y ^ 2 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h
    have hx : (2 : ℤ) ∣ x := by
      have : (2 : ℤ) ∣ x ^ 2 := ⟨y ^ 2, h⟩
      exact Int.prime_two.dvd_of_dvd_pow this
    obtain ⟨a, rfl⟩ := hx
    have hy : (2 : ℤ) ∣ y := by
      have : (2 : ℤ) ∣ y ^ 2 := ⟨a ^ 2, by linarith⟩
      exact Int.prime_two.dvd_of_dvd_pow this
    obtain ⟨b, rfl⟩ := hy
    by_contra hne
    have ha : a ≠ 0 := by rintro rfl; simp at hne
    have := ih a.natAbs (by omega) a b rfl (by linarith)
    exact ha this

/-- If $x^2-2y^2=0$ in $\mathbb Z$ then $x=y=0$. -/
theorem pell2_zero_value_imp_zero {x y : ℤ} (h : x ^ 2 - 2 * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx := pell2_sq_eq_two_sq_imp_zero _ x y rfl (by linarith)
  subst hx
  refine ⟨rfl, ?_⟩
  simpa using h

/-- **Thue's lemma modulo a prime:** for every $a$ modulo $p$ there are integers $x,y$, not both zero, with
$x\equiv ay\pmod p$ and $|x|,|y|\le\lfloor\sqrt p\rfloor$ (pigeonhole on $(u,v)\mapsto u-av$). -/
theorem pell2_thue {p : ℕ} (hp : p.Prime) (a : ZMod p) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ Nat.sqrt p ∧ y.natAbs ≤ Nat.sqrt p ∧
      ((x : ℤ) : ZMod p) = a * (y : ℤ) := by
  have := Fact.mk hp
  set k := Nat.sqrt p with hk
  let f : Fin (k + 1) × Fin (k + 1) → ZMod p := fun uv => (uv.1.val : ZMod p) - a * (uv.2.val : ZMod p)
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (k + 1) × Fin (k + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
    have := Nat.lt_succ_sqrt p
    nlinarith [this]
  obtain ⟨⟨u1, v1⟩, ⟨u2, v2⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨(u1.val : ℤ) - u2.val, (v1.val : ℤ) - v2.val, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    apply hne
    have h1 : u1.val = u2.val := by omega
    have h2 : v1.val = v2.val := by omega
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  · have := u1.isLt; have := u2.isLt; omega
  · have := v1.isLt; have := v2.isLt; omega
  · simp only [f] at heq
    push_cast
    linear_combination heq

/-- **A prime $p\equiv\pm1\pmod8$ is a value of $x_0^2-2x_1^2$** (it splits in $\mathbb Z[\sqrt2]$): $2$ is a square
mod $p$, $a^2\equiv2$, and Thue's lemma gives $x_0\equiv ax_1\pmod p$ with $0<\max(|x_0|,|x_1|)<\sqrt p$, so
$x_0^2-2x_1^2 = -p$. -/
theorem pell2_value_prime {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 1 ∨ p % 8 = 7) :
    ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = p := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_two_iff hp2).2 h8
  obtain ⟨x, y, hxy, hx, hy, hcong⟩ := pell2_thue hp a
  set k := Nat.sqrt p with hk
  have hkk : k * k ≤ p := Nat.sqrt_le p
  have hkne : k * k ≠ p := by
    intro h
    have hd : k ∣ p := ⟨k, h.symm⟩
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · rw [h1] at h; simp at h; exact hp.one_lt.ne' h.symm
    · rw [h1] at h; nlinarith [hp.two_le]
  have hklt : k * k < p := lt_of_le_of_ne hkk hkne
  have hdvd : (p : ℤ) ∣ x ^ 2 - 2 * y ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcong]
    have : (2 : ZMod p) = a * a := ha
    rw [this]; ring
  have hx2 : x ^ 2 ≤ (k : ℤ) * k := by
    have : x ^ 2 = ((x.natAbs : ℕ) : ℤ) ^ 2 := by simp [sq_abs]
    rw [this]; exact_mod_cast (by rw [sq]; exact Nat.mul_le_mul hx hx : x.natAbs ^ 2 ≤ k * k)
  have hy2 : y ^ 2 ≤ (k : ℤ) * k := by
    have : y ^ 2 = ((y.natAbs : ℕ) : ℤ) ^ 2 := by simp [sq_abs]
    rw [this]; exact_mod_cast (by rw [sq]; exact Nat.mul_le_mul hy hy : y.natAbs ^ 2 ≤ k * k)
  have hklt' : (k : ℤ) * k < p := by exact_mod_cast hklt
  obtain ⟨c, hc⟩ := hdvd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc1 : -2 < c := by
    by_contra hh; push Not at hh
    nlinarith [sq_nonneg x]
  have hc2 : c < 1 := by
    by_contra hh; push Not at hh
    nlinarith [sq_nonneg y]
  have : c = 0 ∨ c = -1 := by omega
  rcases this with rfl | rfl
  · exfalso
    obtain ⟨h1, h2⟩ := pell2_zero_value_imp_zero (x := x) (y := y) (by linarith)
    rcases hxy with h | h <;> simp_all
  · exact ⟨x + 2 * y, x + y, by linarith [hc, show (x + 2*y)^2 - 2*(x+y)^2 = -(x^2 - 2*y^2) by ring]⟩

/-- If an inert prime $q\equiv\pm3\pmod 8$ divides $x^2-2y^2$ then $q\mid x$ and $q\mid y$. -/
theorem pell2_inert_dvd {q : ℕ} (hq : q.Prime) (h8 : q % 8 = 3 ∨ q % 8 = 5) {x y : ℤ}
    (h : (q : ℤ) ∣ x ^ 2 - 2 * y ^ 2) : (q : ℤ) ∣ x ∧ (q : ℤ) ∣ y := by
  have := Fact.mk hq
  have hq2 : q ≠ 2 := by rintro rfl; omega
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at h
  have hy : (y : ZMod q) = 0 := by
    by_contra hy
    have : IsSquare (2 : ZMod q) := ⟨(x : ZMod q) / y, by
      rw [div_mul_div_comm, ← sq, ← sq, eq_div_iff (pow_ne_zero 2 hy)]
      linear_combination (-1 : ZMod q) * h⟩
    have := (ZMod.exists_sq_eq_two_iff hq2).1 this
    omega
  refine ⟨?_, hy⟩
  rw [hy] at h
  simpa using h

/-- Descent for $x^2-2y^2=m\neq0$: the $q$-adic valuation of $|m|$ is even for inert $q$. -/
theorem pell2_even_valuation_aux {q : ℕ} (hq : q.Prime) (h8 : q % 8 = 3 ∨ q % 8 = 5) :
    ∀ n : ℕ, ∀ x y : ℤ, (x ^ 2 - 2 * y ^ 2).natAbs = n → x ^ 2 - 2 * y ^ 2 ≠ 0 →
      Even (padicValNat q n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hn hm
  have := Fact.mk hq
  by_cases hd : (q : ℤ) ∣ x ^ 2 - 2 * y ^ 2
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := pell2_inert_dvd hq h8 hd
    have hm' : a ^ 2 - 2 * b ^ 2 ≠ 0 := by
      intro h0
      apply hm
      rw [ha, hb]; linear_combination (q : ℤ) ^ 2 * h0
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
    have heq : (x ^ 2 - 2 * y ^ 2).natAbs = q ^ 2 * (a ^ 2 - 2 * b ^ 2).natAbs := by
      have : x ^ 2 - 2 * y ^ 2 = (q : ℤ) ^ 2 * (a ^ 2 - 2 * b ^ 2) := by
        rw [ha, hb]; ring
      rw [this, Int.natAbs_mul]; simp
    have hpos : 0 < (a ^ 2 - 2 * b ^ 2).natAbs := Int.natAbs_pos.2 hm'
    have hlt : (a ^ 2 - 2 * b ^ 2).natAbs < n := by
      rw [← hn, heq]
      have : 2 ≤ q := hq.two_le
      have h4 : 2 ≤ q ^ 2 := by nlinarith
      have := Nat.mul_le_mul_right (a ^ 2 - 2 * b ^ 2).natAbs h4
      omega
    have := ih _ hlt a b rfl hm'
    rw [← hn, heq, padicValNat.mul (pow_ne_zero 2 hq.ne_zero) hpos.ne', padicValNat.prime_pow]
    exact ⟨1 + this.choose, by have := this.choose_spec; omega⟩
  · have : ¬ q ∣ n := by
      rw [← hn]; intro h'; exact hd (Int.natCast_dvd.2 h')
    rw [padicValNat.eq_zero_of_not_dvd this]; exact Even.zero

/-- **A prime $q\equiv\pm3\pmod8$ divides a nonzero value of $x_0^2-2x_1^2$ to an even power** ($q$ is inert in
$\mathbb Z[\sqrt2]$: $2$ is not a square mod $q$, so $q\mid x_0^2-2x_1^2$ forces $q\mid x_0$ and $q\mid x_1$). -/
theorem even_padicValNat_of_pell2_value {m : ℤ} (hm : m ≠ 0) (h : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m)
    {q : ℕ} (hq : q.Prime) (h8 : q % 8 = 3 ∨ q % 8 = 5) : Even (padicValNat q m.natAbs) := by
  obtain ⟨x, y, rfl⟩ := h
  exact pell2_even_valuation_aux hq h8 _ x y rfl hm

/-- The criterion passes from $dn$ to $n$ when every prime $q\equiv3,5\pmod8$ divides $d$ to an even power. -/
theorem pell2_crit_of_mul {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0)
    (hdc : ∀ q : ℕ, q.Prime → q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q d))
    (h : ∀ q ∈ (d * n).primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q (d * n))) :
    ∀ q ∈ n.primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q n) := by
  intro q hq h8
  have hqp := Nat.prime_of_mem_primeFactors hq
  have := Fact.mk hqp
  have hqdn : q ∈ (d * n).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hqp, Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hq) d, mul_ne_zero hd hn⟩
  have h1 := h q hqdn h8
  rw [padicValNat.mul hd hn] at h1
  exact (Nat.even_add.1 h1).1 (hdc q hqp h8)

/-- The criterion implies representability, for natural numbers (induction on $m$, removing the least prime factor). -/
theorem pell2_value_of_forall {m : ℕ}
    (h : ∀ q ∈ m.primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q m)) :
    ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := Nat.minFac_dvd m
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hp0 : m.minFac ≠ 0 := hp.ne_zero
  by_cases h8 : m.minFac % 8 = 3 ∨ m.minFac % 8 = 5
  · have hev := h m.minFac (Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd m, by omega⟩) h8
    have hv1 : 1 ≤ padicValNat m.minFac m := one_le_padicValNat_of_dvd (by omega) (Nat.minFac_dvd m)
    have hv2 : 2 ≤ padicValNat m.minFac m := by obtain ⟨r, hr⟩ := hev; omega
    obtain ⟨n, hn⟩ := (padicValNat_dvd_iff_le (by omega)).2 hv2
    have hn0 : n ≠ 0 := by rintro rfl; omega
    have hlt : n < m := by
      rw [hn]
      have : 2 ≤ m.minFac ^ 2 := by nlinarith [hp.two_le]
      nlinarith [Nat.pos_of_ne_zero hn0]
    have hcrit := pell2_crit_of_mul (pow_ne_zero 2 hp0) hn0
      (fun q hq _ => by have := Fact.mk hq; rw [padicValNat.pow]; exact even_two_mul _) (hn ▸ h)
    obtain ⟨x, y, hxy⟩ := ih n hlt hcrit
    exact ⟨m.minFac * x, m.minFac * y, by
      rw [show (m : ℤ) = (m.minFac : ℤ) ^ 2 * n by exact_mod_cast hn, ← hxy]; ring⟩
  · have hprep : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m.minFac := by
      by_cases hp2 : m.minFac = 2
      · exact ⟨2, 1, by rw [hp2]; norm_num⟩
      · refine pell2_value_prime hp ?_
        have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
        omega
    have hlt : k < m := by
      rw [hk]
      have := hp.two_le
      nlinarith [Nat.pos_of_ne_zero hk0]
    have hcrit := pell2_crit_of_mul hp0 hk0 (fun q hq hq8 => by
      have := Fact.mk hq
      rw [padicValNat_primes (fun e => h8 (by rw [← e]; exact hq8))]
      exact Even.zero) (hk ▸ h)
    obtain ⟨x, y, hxy⟩ := ih k hlt hcrit
    rw [show (m : ℤ) = (m.minFac : ℤ) * k by exact_mod_cast hk]
    exact pell2_value_mul hprep ⟨x, y, hxy⟩

/-- **The values of $x_0^2-2x_1^2$** (Dirichlet, *Vorlesungen über Zahlentheorie* [unverified locator]; the analogue of
Fermat's two-squares criterion `Nat.eq_sq_add_sq_iff`): for every $m\in\mathbb N$,
$m = x_0^2 - 2x_1^2$ for some $x_0, x_1\in\mathbb Z$ iff every prime $q\equiv3,5\pmod8$ divides $m$ to an even power
($v_q(m)$ even). Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie (numbers represented by a binary form) [unverified locator]"]
theorem pell2_value_iff {m : ℕ} :
    (∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m) ↔
      ∀ q ∈ m.primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q m) := by
  refine ⟨fun h q hq h8 => ?_, pell2_value_of_forall⟩
  have hm : m ≠ 0 := (Nat.mem_primeFactors.1 hq).2.2
  simpa using even_padicValNat_of_pell2_value (m := (m : ℤ)) (by exact_mod_cast hm) h
    (Nat.prime_of_mem_primeFactors hq) h8

/-- **The values of $x_0^2-2x_1^2$, every integer**: for every $m\in\mathbb Z$ (of either sign),
$m = x_0^2 - 2x_1^2$ for some $x_0, x_1\in\mathbb Z$ iff every prime $q\equiv3,5\pmod8$ divides $|m|$ to an even power.
Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie (numbers represented by a binary form) [unverified locator]"]
theorem pell2_value_int_iff {m : ℤ} :
    (∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m) ↔
      ∀ q ∈ m.natAbs.primeFactors, q % 8 = 3 ∨ q % 8 = 5 → Even (padicValNat q m.natAbs) := by
  rw [← pell2_value_iff]
  rcases Int.natAbs_eq m with h | h
  · rw [← h]
  · conv_lhs => rw [h]
    exact pell2_value_neg_iff _

/-- **Rational values are integral values**: an integer $m$ is $x_0^2 - 2x_1^2$ with $x_0, x_1\in\mathbb Q$ iff it is
$x_0^2 - 2x_1^2$ with $x_0, x_1\in\mathbb Z$ (clear denominators, $mc^2 = X_0^2 - 2X_1^2$, and apply the criterion,
which only sees $v_q(m)$ modulo $2$). Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie (numbers represented by a binary form) [unverified locator]"]
theorem pell2_value_rat_iff {m : ℤ} :
    (∃ x y : ℚ, x ^ 2 - 2 * y ^ 2 = m) ↔ ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m := by
  refine ⟨fun ⟨x, y, h⟩ => ?_, fun ⟨x, y, h⟩ => ⟨x, y, by exact_mod_cast h⟩⟩
  by_cases hm : m = 0
  · exact ⟨0, 0, by simp [hm]⟩
  -- clear denominators: $X_0 = x\,c$, $X_1 = y\,c$ with $c = \mathrm{den}(x)\,\mathrm{den}(y)$
  set c : ℕ := x.den * y.den with hc
  have hc0 : c ≠ 0 := mul_ne_zero x.den_nz y.den_nz
  have hXY : (x.num * y.den) ^ 2 - 2 * (y.num * x.den) ^ 2 = m * (c : ℤ) ^ 2 := by
    have hx := Rat.mul_den_eq_num x
    have hy := Rat.mul_den_eq_num y
    have : (((x.num * y.den) ^ 2 - 2 * (y.num * x.den) ^ 2 : ℤ) : ℚ) = ((m * (c : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast
      rw [← hx, ← hy, hc, ← h]; push_cast; ring
    exact_mod_cast this
  have hmc : m * (c : ℤ) ^ 2 ≠ 0 := mul_ne_zero hm (by exact_mod_cast pow_ne_zero 2 hc0)
  rw [pell2_value_int_iff]
  intro q hq h8
  have hqp := Nat.prime_of_mem_primeFactors hq
  have := Fact.mk hqp
  have hev := even_padicValNat_of_pell2_value hmc ⟨_, _, hXY⟩ hqp h8
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    padicValNat.mul (Int.natAbs_ne_zero.2 hm) (pow_ne_zero 2 hc0), padicValNat.pow] at hev
  exact (Nat.even_add.1 hev).2 (even_two_mul _)

end QuadFormsKB.Tamagawa.Classical
