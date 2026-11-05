/-
# Cassels, Chapter 14, §6: the conditional biquadratic symbol and (6.25)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 351–352 (the worked example $D = 4rs$).

* (p. 351) For a prime $p \equiv 1 \pmod 4$ and a quadratic residue $a$ modulo $p$, the *conditional biquadratic
  symbol* is $[a/p]_4 = 1$ if $a \equiv b^4 \pmod p$ is soluble and $-1$ otherwise (`condBiquadSym`).
* (p. 352) "Clearly $[a_1a_2/r]_4 = [a_1/r]_4[a_2/r]_4$ in the sense that if two of the symbols are defined then so is
  the third and the equation holds" (`condBiquadSym_mul`, `legendreSym_eq_one_of_mul`).
* (6.24)–(6.25), p. 352: for primes $r \equiv s \equiv 1 \pmod 4$ with $(r/s) = 1$ and a primitive representation
  $rx^2 - sy^2 = w^2$ with $w$ prime to $2rs$, one has $(w/r) = [s/r]_4$ (`legendreSym_eq_condBiquadSym`).

*Garbled source.* In the machine-read text (6.24) reads "$rx^2 - sy^2 = w$"; the page image (p. 351) has $w^2$.
*Erratum:* on p. 352 Cassels justifies $l = 1$ for $r \equiv 5 \pmod 8$ "by regarding (6.14) as a congruence modulo
8"; the equation meant is (6.24). The primitivity $\gcd(x, y) = 1$ of the representation, implicit in Cassels (it
comes from Lemma 2.5), is an explicit hypothesis here; without it the step "$(r/q) = 1$ by (6.24)" fails.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Pell

namespace QuadFormsKB.Composition

/-- **Cassels' conditional biquadratic symbol** $[a/p]_4$ (Ch. 14, §6, p. 351): $1$ if $a \equiv b^4 \pmod p$ for some
integer $b$, and $-1$ otherwise. Cassels defines it only for a quadratic residue $a$ of a prime $p \equiv 1 \pmod 4$
("defined" below means $p \equiv 1 \pmod 4$ and $(a/p) = 1$); outside that range the value is meaningless. -/
@[kb "cassels1978" "Ch. 14, §6, p. 351 (the conditional biquadratic symbol [a/p]₄)"]
noncomputable def condBiquadSym (p : ℕ) (a : ℤ) : ℤ := by
  classical exact if ∃ b : ℤ, b ^ 4 ≡ a [ZMOD p] then 1 else -1

lemma condBiquadSym_cases (p : ℕ) (a : ℤ) : condBiquadSym p a = 1 ∨ condBiquadSym p a = -1 := by
  unfold condBiquadSym
  split_ifs <;> simp

lemma pm_inj {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {u v : ℤ} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (h : (u : ZMod p) = v) : u = v := by
  have : Fact (2 < p) := ⟨by
    have := (Fact.out : p.Prime).two_le
    omega⟩
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact absurd (by simpa using h) (ZMod.neg_one_ne_one.symm)
  · exact absurd (by simpa using h) (ZMod.neg_one_ne_one)
  · rfl

lemma fourth_iff {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    (∃ b : ℤ, b ^ 4 ≡ a [ZMOD p]) ↔ (a : ZMod p) ^ (p / 4) = 1 := by
  have hp' : p.Prime := Fact.out
  have hm : p - 1 = 4 * (p / 4) := by omega
  constructor
  · rintro ⟨b, hb⟩
    have hb' : ((b : ℤ) : ZMod p) ^ 4 = (a : ZMod p) := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hb
      simpa using this
    have hb0 : (b : ZMod p) ≠ 0 := by
      intro h0; rw [h0] at hb'; apply ha; rw [← hb']; norm_num
    rw [← hb', ← pow_mul, ← hm]
    exact ZMod.pow_card_sub_one_eq_one hb0
  · intro h
    set m := p / 4 with hmdef
    have hm0 : 0 < m := by have := hp'.two_le; omega
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 _ ha))
    have h1 : g ^ (k * (m : ℤ)) = 1 := by
      rw [zpow_mul, hk, zpow_natCast]
      ext
      simpa using h
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord, hm] at h2
    have h3 : ((4 : ℤ)) ∣ k := by
      have : (4 : ℤ) * m ∣ k * m := by exact_mod_cast h2
      exact (Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hm0.ne') this)
    obtain ⟨j, hj⟩ := h3
    have hx : (((g ^ j : (ZMod p)ˣ) : ZMod p)) ^ 4 = (a : ZMod p) := by
      have h4 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hk
      simp only [Units.val_mk0] at h4
      have h5 : g ^ (4 * j) = (g ^ j) ^ 4 := by rw [mul_comm, zpow_mul]; simp
      rw [← h4, hj, h5]
      simp
    refine ⟨((g ^ j : (ZMod p)ˣ) : ZMod p).val, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ _).1
    simpa using hx

lemma cast_condBiquad {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {a : ℤ} (ha : legendreSym p a = 1) :
    (condBiquadSym p a : ZMod p) = (a : ZMod p) ^ (p / 4) := by
  have ha0 : (a : ZMod p) ≠ 0 := fun h => by
    have := (legendreSym.eq_zero_iff p a).2 h
    omega
  have hsq : ((a : ZMod p) ^ (p / 4)) * ((a : ZMod p) ^ (p / 4)) = 1 := by
    have := legendreSym.eq_pow p a
    rw [ha] at this
    rw [← pow_add, ← two_mul]
    have h2 : 2 * (p / 4) = p / 2 := by omega
    rw [h2, ← this]; simp
  by_cases h : ∃ b : ℤ, b ^ 4 ≡ a [ZMOD p]
  · rw [(fourth_iff hp ha0).1 h]
    unfold condBiquadSym
    simp [h]
  · have h' : (a : ZMod p) ^ (p / 4) ≠ 1 := fun h1 => h ((fourth_iff hp ha0).2 h1)
    have := (mul_self_eq_one_iff.1 hsq).resolve_left h'
    rw [this]
    unfold condBiquadSym
    simp [h]

/-- **"If two of the symbols are defined then so is the third"** (Cassels, Ch. 14, §6, p. 352): if two of $a_1, a_2,
a_1a_2$ are quadratic residues modulo $p$, so is the third. -/
@[kb "cassels1978" "Ch. 14, §6, p. 352 ([a₁a₂/r]₄: if two symbols are defined, so is the third)"]
theorem legendreSym_eq_one_of_two {p : ℕ} [Fact p.Prime] {a₁ a₂ : ℤ} :
    (legendreSym p a₁ = 1 → legendreSym p a₂ = 1 → legendreSym p (a₁ * a₂) = 1) ∧
    (legendreSym p a₁ = 1 → legendreSym p (a₁ * a₂) = 1 → legendreSym p a₂ = 1) ∧
    (legendreSym p a₂ = 1 → legendreSym p (a₁ * a₂) = 1 → legendreSym p a₁ = 1) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [legendreSym.mul, h1, h2]; rfl
  · rw [legendreSym.mul, h1, one_mul] at h2; exact h2
  · rw [legendreSym.mul, h1, mul_one] at h2; exact h2

/-- **Multiplicativity of the conditional biquadratic symbol** (Cassels, Ch. 14, §6, p. 352):
$[a_1a_2/p]_4 = [a_1/p]_4[a_2/p]_4$ for quadratic residues $a_1, a_2$ of a prime $p \equiv 1 \pmod 4$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 352 ([a₁a₂/r]₄ = [a₁/r]₄[a₂/r]₄)"]
theorem condBiquadSym_mul {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {a₁ a₂ : ℤ} (h₁ : legendreSym p a₁ = 1)
    (h₂ : legendreSym p a₂ = 1) :
    condBiquadSym p (a₁ * a₂) = condBiquadSym p a₁ * condBiquadSym p a₂ := by
  have h12 : legendreSym p (a₁ * a₂) = 1 := by rw [legendreSym.mul, h₁, h₂]; rfl
  apply pm_inj hp (condBiquadSym_cases _ _)
  · rcases condBiquadSym_cases p a₁ with h | h <;> rcases condBiquadSym_cases p a₂ with h' | h' <;>
      simp [h, h']
  · push_cast
    rw [cast_condBiquad hp h12, cast_condBiquad hp h₁, cast_condBiquad hp h₂]
    push_cast
    ring

/-- **$[-1/r]_4 = (2/r)$** (Cassels, Ch. 14, §6, p. 352, used for $r \equiv 1$ and $r \equiv 5 \pmod 8$): for a prime
$r \equiv 1 \pmod 4$, $-1$ is a fourth power modulo $r$ iff $r \equiv 1 \pmod 8$. -/
@[kb "cassels1978" "Ch. 14, §6, p. 352 ([−1/r]₄ = (2/r))"]
theorem condBiquadSym_neg_one {r : ℕ} [Fact r.Prime] (hr : r % 4 = 1) :
    condBiquadSym r (-1) = legendreSym r 2 := by
  have hr2 : r ≠ 2 := by omega
  have hneg : legendreSym r (-1) = 1 := by
    rw [legendreSym.at_neg_one hr2, ZMod.χ₄_nat_one_mod_four hr]
  have h2 : legendreSym r 2 = if r % 8 = 1 then 1 else -1 := by
    rw [legendreSym.at_two hr2, ZMod.χ₈_nat_eq_if_mod_eight]
    have h21 : r % 2 = 1 := by omega
    by_cases h8 : r % 8 = 1
    · simp [h21, h8]
    · have h5 : r % 8 = 5 := by omega
      simp [h21, h5]
  apply pm_inj hr (condBiquadSym_cases _ _)
  · rw [h2]; split_ifs <;> simp
  · rw [cast_condBiquad hr hneg, h2]
    have hm : (-1 : ZMod r) ^ (r / 4) = if r % 8 = 1 then 1 else -1 := by
      split_ifs with h8
      · have : r / 4 = 2 * (r / 8) := by omega
        rw [this, pow_mul]; simp
      · have : r / 4 = 2 * (r / 8) + 1 := by omega
        rw [this, pow_succ, pow_mul]; simp
    push_cast
    rw [hm]

lemma legendre_two_eq {r : ℕ} [Fact r.Prime] (hr : r % 4 = 1) :
    legendreSym r 2 = if r % 8 = 1 then 1 else -1 := by
  have hr2 : r ≠ 2 := by omega
  rw [legendreSym.at_two hr2, ZMod.χ₈_nat_eq_if_mod_eight]
  have h21 : r % 2 = 1 := by omega
  by_cases h8 : r % 8 = 1
  · simp [h21, h8]
  · have h5 : r % 8 = 5 := by omega
    simp [h21, h5]

lemma legendre_prod_one {r : ℕ} [Fact r.Prime] :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → legendreSym r q = 1) → legendreSym r n = 1 := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp
  | prime p hp =>
    intro _ h
    exact h p hp dvd_rfl
  | mul a b iha ihb =>
    intro hab h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    push_cast
    rw [legendreSym.mul, iha ha (fun q hq hd => h q hq (dvd_mul_of_dvd_left hd _)),
      ihb hb (fun q hq hd => h q hq (dvd_mul_of_dvd_right hd _))]
    rfl

lemma legendre_natAbs {r : ℕ} [Fact r.Prime] (hr : r % 4 = 1) (y : ℤ) :
    legendreSym r y = legendreSym r (y.natAbs : ℤ) := by
  have hr2 : r ≠ 2 := by omega
  have hneg : legendreSym r (-1) = 1 := by
    rw [legendreSym.at_neg_one hr2, ZMod.χ₄_nat_one_mod_four hr]
  rcases Int.natAbs_eq y with h | h
  · rw [← h]
  · conv_lhs => rw [h]
    rw [neg_eq_neg_one_mul, legendreSym.mul, hneg, one_mul]

lemma mod8_aux : ∀ S X Y W : ZMod 8, (S = 1 ∨ S = 5) →
    (X = 1 ∨ X = 3 ∨ X = 5 ∨ X = 7 ∨ Y = 1 ∨ Y = 3 ∨ Y = 5 ∨ Y = 7) →
    (W = 1 ∨ W = 3 ∨ W = 5 ∨ W = 7) → 5 * X ^ 2 - S * Y ^ 2 = W ^ 2 → Y = 2 ∨ Y = 6 := by
  decide +kernel

lemma zmod8_odd (x : ℤ) (h : x % 2 = 1) :
    (x : ZMod 8) = 1 ∨ (x : ZMod 8) = 3 ∨ (x : ZMod 8) = 5 ∨ (x : ZMod 8) = 7 := by
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h | h | h | h
  · left; have := (ZMod.intCast_eq_intCast_iff' x 1 8).2 (by simpa using h); simpa using this
  · right; left; have := (ZMod.intCast_eq_intCast_iff' x 3 8).2 (by simpa using h); simpa using this
  · right; right; left
    have := (ZMod.intCast_eq_intCast_iff' x 5 8).2 (by simpa using h); simpa using this
  · right; right; right
    have := (ZMod.intCast_eq_intCast_iff' x 7 8).2 (by simpa using h); simpa using this

lemma mod8_y {r s : ℕ} (hr : r % 8 = 5) (hs : s % 4 = 1) {x y w : ℤ} (hxy : IsCoprime x y)
    (h : (r : ℤ) * x ^ 2 - s * y ^ 2 = w ^ 2) (hw : w % 2 = 1) : ∃ k : ℤ, y = 2 * k ∧ k % 2 = 1 := by
  have hcop : x % 2 = 1 ∨ y % 2 = 1 := by
    by_contra hc
    push Not at hc
    have h2x : (2 : ℤ) ∣ x := by omega
    have h2y : (2 : ℤ) ∣ y := by omega
    have := hxy.isUnit_of_dvd' h2x h2y
    rw [Int.isUnit_iff] at this
    omega
  have hS : (s : ZMod 8) = 1 ∨ (s : ZMod 8) = 5 := by
    have : s % 8 = 1 ∨ s % 8 = 5 := by omega
    rcases this with h1 | h1
    · left
      have := (ZMod.natCast_eq_natCast_iff' s 1 8).2 (by simpa using h1); simpa using this
    · right
      have := (ZMod.natCast_eq_natCast_iff' s 5 8).2 (by simpa using h1); simpa using this
  have hR : (r : ZMod 8) = 5 := by
    have := (ZMod.natCast_eq_natCast_iff' r 5 8).2 (by simpa using hr); simpa using this
  have hc := congrArg (Int.cast : ℤ → ZMod 8) h
  push_cast at hc
  rw [hR] at hc
  have hX : _ := hcop.elim (fun h => Or.inl (zmod8_odd x h)) (fun h => Or.inr (zmod8_odd y h))
  have := mod8_aux _ _ _ _ hS (by
    rcases hX with h | h
    · tauto
    · tauto) (zmod8_odd w hw) hc
  have hy8 : y % 8 = 2 ∨ y % 8 = 6 := by
    rcases this with h | h
    · left
      have := (ZMod.intCast_eq_intCast_iff' y 2 8).1 (by simpa using h); simpa using this
    · right
      have := (ZMod.intCast_eq_intCast_iff' y 6 8).1 (by simpa using h); simpa using this
  exact ⟨y / 2, by omega, by omega⟩

/-- **Cassels, Ch. 14, §6, (6.25)** (p. 352): *let $r \ne s$ be primes with $r \equiv s \equiv 1 \pmod 4$ and
$(r/s) = 1$, and let $rx^2 - sy^2 = w^2$ (6.24) with $\gcd(x, y) = 1$ and $w$ prime to $2rs$. Then
$(w/r) = [s/r]_4$.* (Cassels: $(w/r) = [w^2/r]_4 = [-sy^2/r]_4 = [s/r]_4[-1/r]_4(y/r)$ and $(y/r) = (2/r)^l$ with
$2^l \,\|\, y$.) -/
@[kb "cassels1978" "Ch. 14, §6, (6.24)–(6.25), p. 352 ((w/r) = [s/r]₄)"]
theorem legendreSym_eq_condBiquadSym {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1)
    (hrs : r ≠ s) (hη : legendreSym s r = 1) {x y w : ℤ} (hxy : IsCoprime x y)
    (h : (r : ℤ) * x ^ 2 - s * y ^ 2 = w ^ 2) (hw : IsCoprime w (2 * r * s)) :
    legendreSym r w = condBiquadSym r s := by
  have hrp : r.Prime := Fact.out
  have hsp : s.Prime := Fact.out
  have hr2 : r ≠ 2 := by omega
  have hrz : Prime (r : ℤ) := Nat.prime_iff_prime_int.1 hrp
  have hwr' : IsCoprime w (r : ℤ) :=
    (IsCoprime.mul_right_iff.1 (IsCoprime.mul_right_iff.1 hw).1).2
  have hw2' : IsCoprime w 2 := (IsCoprime.mul_right_iff.1 (IsCoprime.mul_right_iff.1 hw).1).1
  have hrw : ¬ (r : ℤ) ∣ w := by
    intro hd
    have := hwr'.isUnit_of_dvd' hd dvd_rfl
    rw [Int.isUnit_iff] at this
    have := hrp.two_le
    omega
  have hwodd : w % 2 = 1 := by
    by_contra hc
    have h2 : (2 : ℤ) ∣ w := by omega
    have := hw2'.isUnit_of_dvd' h2 dvd_rfl
    rw [Int.isUnit_iff] at this
    omega
  have hwr : ((w : ℤ) : ZMod r) ≠ 0 := fun h0 =>
    hrw ((ZMod.intCast_zmod_eq_zero_iff_dvd w r).1 h0)
  have hwsq : (r : ℤ) ∣ w ^ 2 → False := fun hd => hrw (hrz.dvd_of_dvd_pow hd)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hwsq
    rw [← h]; exact ⟨x ^ 2, by ring⟩
  -- odd prime factors of y
  have hq : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ y → q ≠ 2 → legendreSym r q = 1 := by
    intro q hqp hqy hq2
    have : Fact q.Prime := ⟨hqp⟩
    have hqr : q ≠ r := by
      rintro rfl
      apply hwsq
      rw [← h]
      exact dvd_sub (dvd_mul_right _ _) (Dvd.dvd.mul_left (dvd_pow hqy two_ne_zero) _)
    have hqx : ¬ (q : ℤ) ∣ x := by
      intro hd
      have := hxy.isUnit_of_dvd' hd hqy
      rw [Int.isUnit_iff] at this
      have := hqp.two_le
      omega
    have hX : (x : ZMod q) ≠ 0 := fun h0 => hqx ((ZMod.intCast_zmod_eq_zero_iff_dvd x q).1 h0)
    have hR : ((r : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (r : ℤ) q).1 h0
      have h' : q ∣ r := by exact_mod_cast this
      exact hqr ((Nat.prime_dvd_prime_iff_eq hqp hrp).1 h')
    have hY : (y : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd y q).2 hqy
    have hc := congrArg (Int.cast : ℤ → ZMod q) h
    push_cast at hc
    rw [hY] at hc
    have hsq : legendreSym q (r : ℤ) = 1 := by
      rw [legendreSym.eq_one_iff q hR]
      refine ⟨(w : ZMod q) * (x : ZMod q)⁻¹, ?_⟩
      push_cast at hR ⊢
      field_simp
      linear_combination hc
    rw [← legendreSym.quadratic_reciprocity_one_mod_four (p := r) (q := q) hr hq2]
    exact hsq
  -- (y / r) = (2 / r)
  have hy : legendreSym r y = legendreSym r 2 := by
    have h2 := legendre_two_eq hr
    rw [legendre_natAbs hr y]
    have hy0' : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
    by_cases h8 : r % 8 = 1
    · simp only [h8, ite_true] at h2
      rw [h2]
      apply legendre_prod_one _ hy0'
      intro q hqp hqd
      by_cases hq2 : q = 2
      · subst hq2; exact_mod_cast h2
      · exact hq q hqp (Int.natCast_dvd.2 hqd) hq2
    · have h5 : r % 8 = 5 := by omega
      obtain ⟨k, hk, hkodd⟩ := mod8_y h5 hs hxy h hwodd
      have hk0 : k ≠ 0 := by omega
      have hk1 : legendreSym r k = 1 := by
        rw [legendre_natAbs hr k]
        apply legendre_prod_one _ (Int.natAbs_ne_zero.2 hk0)
        intro q hqp hqd
        have hqk : (q : ℤ) ∣ k := Int.natCast_dvd.2 hqd
        have hq2 : q ≠ 2 := by
          rintro rfl
          have : (2 : ℤ) ∣ k := by exact_mod_cast hqk
          omega
        exact hq q hqp (by rw [hk]; exact dvd_mul_of_dvd_right hqk _) hq2
      rw [← legendre_natAbs hr y, hk, legendreSym.mul, hk1, mul_one]
  have hL : legendreSym r 2 = 1 ∨ legendreSym r 2 = -1 := by
    rw [legendre_two_eq hr]; split_ifs <;> simp
  have hLL : legendreSym r 2 * legendreSym r 2 = 1 := by
    rcases hL with h' | h' <;> rw [h'] <;> norm_num
  have hls : legendreSym r (s : ℤ) = 1 := by
    rw [← legendreSym.quadratic_reciprocity_one_mod_four (p := r) (q := s) hr (by omega)]
    exact hη
  have hcs := cast_condBiquad hr hls
  push_cast at hcs
  have hneg : legendreSym r (-1) = 1 := by
    rw [legendreSym.at_neg_one hr2, ZMod.χ₄_nat_one_mod_four hr]
  have hcm := cast_condBiquad hr hneg
  rw [condBiquadSym_neg_one hr] at hcm
  have hcw := legendreSym.eq_pow r w
  have hcy := legendreSym.eq_pow r y
  rw [hy] at hcy
  have hW : (w : ZMod r) ^ 2 = -1 * ((s : ZMod r) * (y : ZMod r) ^ 2) := by
    have := congrArg (Int.cast : ℤ → ZMod r) h
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination (-1 : ZMod r) * this
  have h2m : r / 2 = 2 * (r / 4) := by omega
  have key : (legendreSym r w : ZMod r) =
      ((legendreSym r 2 * legendreSym r 2 * condBiquadSym r s : ℤ) : ZMod r) := by
    rw [hcw, h2m, pow_mul, hW, mul_pow, mul_pow, ← pow_mul]
    have hcm' : (legendreSym r 2 : ZMod r) = (-1) ^ (r / 4) := by simpa using hcm
    rw [h2m] at hcy
    push_cast
    rw [← hcy, ← hcs, ← hcm']
    ring
  rw [hLL, one_mul] at key
  exact pm_inj hr (by
    rcases legendreSym.eq_one_or_neg_one r hwr with h' | h' <;> simp [h'])
    (condBiquadSym_cases _ _) key

end QuadFormsKB.Composition
