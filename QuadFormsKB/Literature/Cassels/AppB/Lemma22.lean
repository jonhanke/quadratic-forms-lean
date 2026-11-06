/-
# Cassels, Appendix B, §2, Lemma 2.2: the count $2^\mu$ of orbits of primitive representations

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Appendix B, §2, Lemma 2.2 and its Corollary (2.13),
pp. 372–373. Notation: $D$ is a fundamental discriminant (`IsQuadDisc D`), $\chi_D = (D/\cdot)$ the Kronecker symbol
(`kronZ D` is its integer value, `kroneckerChar D` the Dirichlet character); forms are integral binary forms
$f = ax^2 + bxy + cy^2$ (`BinQF`); a vector $(x, y)$ is $(v_0, v_1)$ (0-based `Fin 2`); orbits are those of the
group `AutSL f` of proper automorphs (determinant $1$) on `primRepVecs f m`; the classes are those of
`Composition.FormClass D`.

**What is proved.** `primRepOrbitCount_holds`: for $m > 0$ prime to $D$, the number of orbits of primitive
representations of $m$, summed over all proper classes of forms of discriminant $D$, is $2^\mu$ if $(D/p) = +1$ for
every prime $p \mid m$ ($\mu$ the number of distinct prime divisors) and $0$ otherwise. This discharges the named
statement `PrimRepOrbitCount D` of `Sec2Lemmas.lean`, hence `cor_lemma_2_2_uncond` (the Corollary (2.13)) is
unconditional.

**Proof, in two parts.**

* *(a) Orbits $\leftrightarrow$ residues $u \bmod 2m$ with $u^2 \equiv D \pmod{4m}$* (the book's bijection with the forms
  $[m, u, v]$, $u^2 - 4mv = D$, $u$ taken modulo $2m$): `ub`, `ub_eq`, `ub_aut`, `ubTot_injective`, `range_ubTot`,
  `sum_orbit_count_eq`. For fundamental $D$ every form of discriminant $D$ is primitive
  (`Binary.isPrimitive_of_fund`), so the classes `FormClass D` are all proper classes of forms of discriminant $D$.
* *(b) The number of such residues* is half the number $\#\{x \bmod 4m : x^2 = D\}$ (`sqrtCount_eq_two_mul_card`), which
  is $2\prod_{p \mid m}(1 + \chi_D(p))$ (`sqrtCount_four_mul`): multiplicativity by the Chinese remainder theorem
  (`sqrtCount_mul`), Hensel lifting at odd primes (`sqrtCount_mul_prime`, `sqrtCount_odd_prime_pow`), four square roots
  modulo $2^k$, $k \ge 3$, for $D \equiv 1 \pmod 8$ and none for $D \equiv 5 \pmod 8$
  (`sqrtCount_two_pow_of_mod_eight_one`, `sqrtCount_two_pow_of_mod_eight_five`), and two modulo $4$
  (`sqrtCount_four`). The product is $2^\mu$ or $0$ since each $\chi_D(p) = \pm 1$ (`prod_one_add_kronZ`).

The count formula was also checked numerically (the number of $u \bmod 2m$ with $u^2 \equiv D \pmod{4m}$ against
$\prod_{p \mid m}(1 + \chi_D(p))$ for $D \in \{-3, -4, -7, -8, 5, 8, 12, 13, -20, 21, \dots\}$ and $m \le 60$ prime to $D$).

No errata found. (The statement, the lemma's first sentence "$m$ is represented primitively only if all $(D/p) = +1$", is
the case count $= 0$ here.)
-/
import QuadFormsKB.Literature.Cassels.AppB.Sec2Lemmas
import QuadFormsKB.Literature.Cassels.AppB.PrimRep

open Matrix

namespace QuadFormsKB.Cassels

open QuadFormsKB.Binary BinQF

/-! ### Part (b): counting the square roots of $D$ modulo $n$ -/

/-- Helper: the number $\#\{x \in \mathbb Z/n : x^2 = D\}$ of square roots of the integer $D$ modulo $n$. -/
noncomputable def sqrtCount (D : ℤ) (n : ℕ) : ℕ := Nat.card {x : ZMod n // x * x = (D : ZMod n)}

/-- Helper: the square root count is multiplicative on coprime moduli (Chinese remainder theorem). -/
theorem sqrtCount_mul {a b : ℕ} (h : a.Coprime b) (D : ℤ) :
    sqrtCount D (a * b) = sqrtCount D a * sqrtCount D b := by
  unfold sqrtCount
  let e := ZMod.chineseRemainder h
  have key : {x : ZMod (a * b) // x * x = (D : ZMod (a * b))} ≃
      {y : ZMod a × ZMod b // y.1 * y.1 = (D : ZMod a) ∧ y.2 * y.2 = (D : ZMod b)} :=
    e.toEquiv.subtypeEquiv (fun x => by
      constructor
      · intro hx
        have := congrArg e hx
        rw [map_mul, map_intCast] at this
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      · rintro ⟨h1, h2⟩
        apply e.injective
        rw [map_mul, map_intCast]
        exact Prod.ext h1 h2)
  rw [Nat.card_congr (key.trans (Equiv.subtypeProdEquivProd (p := fun x : ZMod a => x * x = (D : ZMod a))
    (q := fun y : ZMod b => y * y = (D : ZMod b)))), Nat.card_prod]

/-- Helper: $x^2 = D$ in $\mathbb Z/n$ for the class of an integer $a$ iff $n \mid a^2 - D$. -/
theorem intCast_mul_self_eq_iff (n : ℕ) (a D : ℤ) :
    (a : ZMod n) * (a : ZMod n) = (D : ZMod n) ↔ (n : ℤ) ∣ a * a - D := by
  rw [← Int.cast_mul, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Helper: the integer core of injectivity of Hensel lifting at an odd prime $p \mid n$, $p \nmid D$. -/
theorem hensel_inj_core {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hn : n ≠ 0) {D a b : ℤ}
    (hpD : ¬ (p : ℤ) ∣ D) (hab : (n : ℤ) ∣ b - a) (ha : ((n * p : ℕ) : ℤ) ∣ a * a - D)
    (hb : ((n * p : ℕ) : ℤ) ∣ b * b - D) : ((n * p : ℕ) : ℤ) ∣ b - a := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨c, hc⟩ := hab
  have h1 : ((n * p : ℕ) : ℤ) ∣ (n : ℤ) * (c * (a + b)) := by
    have : (n : ℤ) * (c * (a + b)) = (b * b - D) - (a * a - D) := by
      have : b = a + n * c := by linarith
      subst this; ring
    rw [this]; exact dvd_sub hb ha
  push_cast at h1
  have h2 : (p : ℤ) ∣ c * (a + b) := by
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    exact (mul_dvd_mul_iff_left hn').mp h1
  rcases hpz.dvd_or_dvd h2 with h | h
  · obtain ⟨d, hd⟩ := h
    exact ⟨d, by push_cast; rw [hc, hd]; ring⟩
  · exfalso
    have hpn' : (p : ℤ) ∣ n := by exact_mod_cast hpn
    have h3 : (p : ℤ) ∣ 2 * a := by
      have : 2 * a = (a + b) - (b - a) := by ring
      rw [this]; exact dvd_sub h (hc ▸ dvd_mul_of_dvd_left hpn' c)
    rcases hpz.dvd_or_dvd h3 with h4 | h4
    · have : p ∣ 2 := by exact_mod_cast h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    · apply hpD
      have h5 : (p : ℤ) ∣ a * a - D := dvd_trans (by exact_mod_cast (dvd_mul_of_dvd_left hpn p)) ha
      have := dvd_sub (dvd_mul_of_dvd_left h4 a) h5
      simpa using this

/-- Helper: the integer core of surjectivity of Hensel lifting. -/
theorem hensel_surj_core {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) {D a : ℤ}
    (hpD : ¬ (p : ℤ) ∣ D) (ha : (n : ℤ) ∣ a * a - D) :
    ∃ t : ℤ, ((n * p : ℕ) : ℤ) ∣ (a + n * t) * (a + n * t) - D := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨c, hc⟩ := ha
  have hpn' : (p : ℤ) ∣ n := by exact_mod_cast hpn
  have hpa : ¬ (p : ℤ) ∣ 2 * a := by
    intro h
    rcases hpz.dvd_or_dvd h with h4 | h4
    · have : p ∣ 2 := by exact_mod_cast h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    · apply hpD
      have h5 : (p : ℤ) ∣ a * a - D := hc ▸ dvd_mul_of_dvd_left hpn' c
      have := dvd_sub (dvd_mul_of_dvd_left h4 a) h5
      simpa using this
  have hcop : IsCoprime (p : ℤ) (2 * a) := (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hpa
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨-v * c, ?_⟩
  obtain ⟨w, hw⟩ := hpn'
  refine ⟨u * c + (-v * c) ^ 2 * w, ?_⟩
  push_cast
  have hn : (n : ℤ) = p * w := hw
  have : (a + n * (-v * c)) * (a + n * (-v * c)) - D = n * (c + 2 * a * (-v * c) + n * (-v * c) ^ 2) := by
    linear_combination hc
  rw [this]
  have h2 : c + 2 * a * (-v * c) + n * (-v * c) ^ 2 = p * (u * c + (-v * c) ^ 2 * w) := by
    rw [hn]; linear_combination (-c) * huv
  rw [h2]; ring

/-- Helper: **Hensel lifting at an odd prime**: if $p$ is an odd prime with $p \mid n$, $p \nmid D$, then the square
roots of $D$ modulo $np$ correspond bijectively to those modulo $n$. -/
theorem sqrtCount_mul_prime {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hn : n ≠ 0) {D : ℤ}
    (hpD : ¬ (p : ℤ) ∣ D) : sqrtCount D (n * p) = sqrtCount D n := by
  have hdvd : n ∣ n * p := dvd_mul_right n p
  have : NeZero n := ⟨hn⟩
  have : NeZero (n * p) := ⟨mul_ne_zero hn hp.ne_zero⟩
  unfold sqrtCount
  let f : {x : ZMod (n * p) // x * x = (D : ZMod (n * p))} → {x : ZMod n // x * x = (D : ZMod n)} :=
    fun x => ⟨ZMod.castHom hdvd (ZMod n) x.1, by rw [← map_mul, x.2, map_intCast]⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
    have hxy' : (a : ZMod n) = (b : ZMod n) := by
      have := congrArg Subtype.val hxy
      simpa [f] using this
    rw [intCast_mul_self_eq_iff] at hx hy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy'
    have := hensel_inj_core hp hp2 hpn hn hpD hxy' hx hy
    simp only [Subtype.mk.injEq]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact this
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
    rw [intCast_mul_self_eq_iff] at hy
    obtain ⟨t, ht⟩ := hensel_surj_core hp hp2 hpn hpD hy
    refine ⟨⟨((a + n * t : ℤ) : ZMod (n * p)), ?_⟩, ?_⟩
    · rw [intCast_mul_self_eq_iff]; exact ht
    · simp only [f, Subtype.mk.injEq, map_intCast]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-t, by ring⟩

/-- Helper: **square roots modulo an odd prime power**: for an odd prime $p \nmid D$ ($D$ a fundamental discriminant) and
$k \ge 1$, $\#\{x \in \mathbb Z/p^k : x^2 = D\} = 1 + (D/p)$. -/
theorem sqrtCount_odd_prime_pow {D : ℤ} [IsQuadDisc D] {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (hpD : ¬ (p : ℤ) ∣ D) {k : ℕ} (hk : 1 ≤ k) : (sqrtCount D (p ^ k) : ℤ) = legendreSym p D + 1 := by
  have hp := hpf.out
  induction k, hk using Nat.le_induction with
  | base =>
    rw [pow_one, ← rootCount_odd p hp2, rootCount_eq_card_sqrts p hp2]
    unfold sqrtCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [sq]
  | succ k hk ih =>
    rw [pow_succ, sqrtCount_mul_prime hp hp2 (dvd_pow_self p (by omega)) (pow_ne_zero _ hp.ne_zero) hpD]
    exact ih

/-- Helper: modulo $4$ the number of square roots of $D \equiv 0, 1 \pmod 4$ is $2$. -/
theorem sqrtCount_four {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) : sqrtCount D 4 = 2 := by
  have hc : (D : ZMod 4) = ((D % 4 : ℤ) : ZMod 4) := by simpa using (ZMod.intCast_mod D 4).symm
  unfold sqrtCount
  rw [hc]
  rcases hD with h | h <;> rw [h] <;> simp only [Int.cast_zero, Int.cast_one] <;>
    (rw [Nat.card_eq_fintype_card]; decide)

/-- Helper: **no square roots of $D \equiv 5 \pmod 8$ modulo $2^k$, $k \ge 3$**. -/
theorem sqrtCount_two_pow_of_mod_eight_five {D : ℤ} (hD : D % 8 = 5) {k : ℕ} (hk : 3 ≤ k) :
    sqrtCount D (2 ^ k) = 0 := by
  unfold sqrtCount
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [intCast_mul_self_eq_iff] at hx
  have h8 : (8 : ℤ) ∣ a * a - D := by
    have : ((8 : ℕ) : ℤ) ∣ ((2 ^ k : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (by have := pow_dvd_pow 2 hk; norm_num at this ⊢; exact this)
    exact dvd_trans (by exact_mod_cast this) hx
  have : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;>
    (have := Int.mul_emod a a 8; rw [h] at this; omega)

/-- Helper: for $D \equiv 1 \pmod 8$ there is an odd integer $a$ with $a^2 \equiv D \pmod{2^{j+3}}$. -/
theorem exists_odd_sq_two_pow {D : ℤ} (hD : D % 8 = 1) (j : ℕ) :
    ∃ a : ℤ, Odd a ∧ (2 : ℤ) ^ (j + 3) ∣ a * a - D := by
  induction j with
  | zero => exact ⟨1, odd_one, by omega⟩
  | succ j ih =>
    obtain ⟨a, ha, t, ht⟩ := ih
    rcases Int.even_or_odd t with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · exact ⟨a, ha, t', by rw [ht, ht']; ring⟩
    · obtain ⟨a', rfl⟩ := ha
      refine ⟨2 * a' + 1 + 2 ^ (j + 2), ?_, t' + a' + 1 + 2 ^ j, ?_⟩
      · exact ⟨a' + 2 ^ (j + 1), by ring⟩
      · have e : (2 * a' + 1 + 2 ^ (j + 2)) * (2 * a' + 1 + 2 ^ (j + 2)) - D =
            ((2 * a' + 1) * (2 * a' + 1) - D) + 2 ^ (j + 3) * (2 * a' + 1) + 2 ^ (2 * j + 4) := by ring
        rw [e, ht, ht']; ring

/-- Helper: **two square roots of $D$ modulo $2^{j+3}$ differ by $\pm$ and by $0$ or $2^{j+2}$**: if $a$ is odd and
$a^2 \equiv b^2 \equiv D \pmod{2^{j+3}}$ then $b \equiv \pm a$ or $\pm a + 2^{j+2}$ modulo $2^{j+3}$. -/
theorem two_pow_core {j : ℕ} {a b D : ℤ} (ha : Odd a) (hA : (2 : ℤ) ^ (j + 3) ∣ a * a - D)
    (hB : (2 : ℤ) ^ (j + 3) ∣ b * b - D) :
    (2 : ℤ) ^ (j + 3) ∣ b - a ∨ (2 : ℤ) ^ (j + 3) ∣ b - a - 2 ^ (j + 2) ∨
      (2 : ℤ) ^ (j + 3) ∣ b + a ∨ (2 : ℤ) ^ (j + 3) ∣ b + a - 2 ^ (j + 2) := by
  have h2 : (2 : ℤ) ∣ 2 ^ (j + 3) := dvd_pow_self 2 (by omega)
  have hDo : ¬ Even D := by
    intro hD
    have := Int.even_sub.mp (even_iff_two_dvd.mpr (h2.trans hA))
    exact (Int.not_even_iff_odd.mpr (ha.mul ha)) (this.mpr hD)
  have hb : Odd b := by
    by_contra hb
    have hbe : Even b := Int.not_odd_iff_even.mp hb
    have := Int.even_sub.mp (even_iff_two_dvd.mpr (h2.trans hB))
    exact hDo (this.mp (hbe.mul_right b))
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hprod : (2 : ℤ) ^ (j + 3) ∣ (2 * b' + 1 - (2 * a' + 1)) * (2 * b' + 1 + (2 * a' + 1)) := by
    have : (2 * b' + 1 - (2 * a' + 1)) * (2 * b' + 1 + (2 * a' + 1)) =
        ((2 * b' + 1) * (2 * b' + 1) - D) - ((2 * a' + 1) * (2 * a' + 1) - D) := by ring
    rw [this]; exact dvd_sub hB hA
  have hef : (2 : ℤ) ^ (j + 1) ∣ (b' - a') * (b' + a' + 1) := by
    have e : (2 * b' + 1 - (2 * a' + 1)) * (2 * b' + 1 + (2 * a' + 1)) = 4 * ((b' - a') * (b' + a' + 1)) := by ring
    rw [e, show (2 : ℤ) ^ (j + 3) = 4 * 2 ^ (j + 1) by ring] at hprod
    exact (mul_dvd_mul_iff_left (by norm_num)).mp hprod
  rcases Int.even_or_odd (b' - a') with ⟨c, hc⟩ | he
  · have hf : Odd (b' + a' + 1) := ⟨a' + c, by linarith⟩
    obtain ⟨t, ht⟩ := (IsCoprime.pow_left (Int.isCoprime_two_left.mpr hf)).dvd_of_dvd_mul_right hef
    rcases Int.even_or_odd t with ⟨t', rfl⟩ | ⟨t', rfl⟩
    · left
      exact ⟨t', by linear_combination 2 * ht⟩
    · right; left
      exact ⟨t', by linear_combination 2 * ht⟩
  · have hf : Even (b' + a' + 1) := by
      obtain ⟨c, hc⟩ := he
      exact ⟨a' + c + 1, by linarith⟩
    have hf' : Odd (b' - a') := he
    obtain ⟨t, ht⟩ := (IsCoprime.pow_left (Int.isCoprime_two_left.mpr hf')).dvd_of_dvd_mul_left hef
    rcases Int.even_or_odd t with ⟨t', rfl⟩ | ⟨t', rfl⟩
    · right; right; left
      exact ⟨t', by linear_combination 2 * ht⟩
    · right; right; right
      exact ⟨t', by linear_combination 2 * ht⟩

/-- Helper: **$D \equiv 1 \pmod 8$ has exactly four square roots modulo $2^{j+3}$**: $\pm a$ and $\pm a + 2^{j+2}$. -/
theorem sqrtCount_two_pow_of_mod_eight_one {D : ℤ} (hD : D % 8 = 1) (j : ℕ) :
    sqrtCount D (2 ^ (j + 3)) = 4 := by
  obtain ⟨a, ha, hA⟩ := exists_odd_sq_two_pow hD j
  obtain ⟨a', rfl⟩ := ha
  set h : ℤ := 2 ^ (j + 2) with hh
  have hN : ((2 ^ (j + 3) : ℕ) : ℤ) = 2 * h := by push_cast; rw [hh]; ring
  have hN4 : (4 : ℤ) ∣ ((2 ^ (j + 3) : ℕ) : ℤ) := by
    rw [hN]; exact ⟨2 ^ (j + 1), by rw [hh]; ring⟩
  have hh4 : (4 : ℤ) ∣ h := ⟨2 ^ j, by rw [hh]; ring⟩
  have hhpos : 0 < h := by rw [hh]; positivity
  have hnh : ¬ (((2 ^ (j + 3) : ℕ) : ℤ) ∣ h) := by
    intro hd
    have := Int.le_of_dvd hhpos hd
    rw [hN] at this; omega
  have hA' : ((2 ^ (j + 3) : ℕ) : ℤ) ∣ (2 * a' + 1) * (2 * a' + 1) - D := by push_cast; exact hA
  unfold sqrtCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : Finset.univ.filter (fun x : ZMod (2 ^ (j + 3)) => x * x = (D : ZMod (2 ^ (j + 3)))) =
      {((2 * a' + 1 : ℤ) : ZMod (2 ^ (j + 3))), ((-(2 * a' + 1) : ℤ) : ZMod (2 ^ (j + 3))),
        ((2 * a' + 1 + h : ℤ) : ZMod (2 ^ (j + 3))), ((-(2 * a' + 1) + h : ℤ) : ZMod (2 ^ (j + 3)))} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      obtain ⟨b, rfl⟩ := ZMod.intCast_surjective x
      rw [intCast_mul_self_eq_iff] at hx
      have hx' : (2 : ℤ) ^ (j + 3) ∣ b * b - D := by push_cast at hx; exact hx
      rcases two_pow_core ⟨a', rfl⟩ hA hx' with h1 | h1 | h1 | h1
      · left; rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast; exact (dvd_sub_comm).mp h1
      · right; right; left; rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
        rw [dvd_sub_comm]; rw [hh]; convert h1 using 1; ring
      · right; left; rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
        rw [dvd_sub_comm]; convert h1 using 1; ring
      · right; right; right; rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
        rw [dvd_sub_comm]; rw [hh]; convert h1 using 1; ring
    · obtain ⟨t, ht⟩ := hA'
      rintro (rfl | rfl | rfl | rfl) <;> rw [intCast_mul_self_eq_iff]
      · exact ⟨t, ht⟩
      · exact ⟨t, by rw [← ht]; ring⟩
      · refine ⟨t + (2 * a' + 1) + 2 ^ (j + 1), ?_⟩
        rw [hN] at ht ⊢; rw [hh] at ht ⊢; linear_combination ht
      · refine ⟨t - (2 * a' + 1) + 2 ^ (j + 1), ?_⟩
        rw [hN] at ht ⊢; rw [hh] at ht ⊢; linear_combination ht
  have key : ∀ u v : ℤ, ¬ (((2 ^ (j + 3) : ℕ)) : ℤ) ∣ v - u →
      (u : ZMod (2 ^ (j + 3))) ≠ (v : ZMod (2 ^ (j + 3))) :=
    fun u v hu he => hu ((ZMod.intCast_eq_intCast_iff_dvd_sub u v _).mp he)
  have n12 := key (2 * a' + 1) (-(2 * a' + 1)) (fun hd => by have := dvd_trans hN4 hd; omega)
  have n13 := key (2 * a' + 1) (2 * a' + 1 + h) (fun hd => by
    have : 2 * a' + 1 + h - (2 * a' + 1) = h := by ring
    rw [this] at hd; exact hnh hd)
  have n14 := key (2 * a' + 1) (-(2 * a' + 1) + h) (fun hd => by have := dvd_trans hN4 hd; omega)
  have n23 := key (-(2 * a' + 1)) (2 * a' + 1 + h) (fun hd => by have := dvd_trans hN4 hd; omega)
  have n24 := key (-(2 * a' + 1)) (-(2 * a' + 1) + h) (fun hd => by
    have : -(2 * a' + 1) + h - -(2 * a' + 1) = h := by ring
    rw [this] at hd; exact hnh hd)
  have n34 := key (2 * a' + 1 + h) (-(2 * a' + 1) + h) (fun hd => by have := dvd_trans hN4 hd; omega)
  rw [hset, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simpa using n34
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n23, n24⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n12, n13, n14⟩

/-- Helper: $D$ has exactly one square root modulo $1$. -/
theorem sqrtCount_one (D : ℤ) : sqrtCount D 1 = 1 := by
  unfold sqrtCount
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- Helper: **the local factor of the count at a prime $p \mid 4m$** ($m$ prime to the fundamental discriminant $D$):
$\#\{x \bmod p^v : x^2 = D\} = c_p\,t_p$, where $c_2 = 2$, $c_p = 1$ for odd $p$, and $t_p = 1 + \chi_D(p)$ if
$p \mid m$, $t_p = 1$ otherwise, $v$ the exponent of $p$ in $4m$. -/
theorem sqrtCount_local {D : ℤ} [IsQuadDisc D] {m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime m D.natAbs) {p : ℕ}
    (hp : p.Prime) (hpd : p ∣ 4 * m) :
    (sqrtCount D (p ^ (4 * m).factorization p) : ℤ) =
      (if p = 2 then 2 else 1) * (if p ∣ m then 1 + kronZ D (p : ZMod D.natAbs) else 1) := by
  have hfund := (IsQuadDisc.fund (D := D)).1
  have h4m : 4 * m ≠ 0 := by omega
  have hpD : p ∣ m → ¬ (p : ℤ) ∣ D := by
    intro hpm hpD
    have : p ∣ D.natAbs := Int.natCast_dvd.mp hpD
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpm this)
  by_cases hp2 : p = 2
  · subst hp2
    rw [ite_eq_left rfl]
    have hv : (4 * m).factorization 2 = m.factorization 2 + 2 := by
      rw [Nat.factorization_mul (by norm_num) hm.ne', Finsupp.add_apply,
        show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self Nat.prime_two]
      simp [add_comm]
    by_cases h2m : 2 ∣ m
    · rw [ite_eq_left h2m]
      have hDodd : D % 2 = 1 := by
        by_contra hne
        have : (2 : ℤ) ∣ D := by omega
        exact hpD h2m (by exact_mod_cast this)
      have hD1 : D % 4 = 1 := by omega
      have hpos : 0 < m.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm.ne' h2m
      obtain ⟨j, hj⟩ : ∃ j, m.factorization 2 = j + 1 := ⟨m.factorization 2 - 1, by omega⟩
      rw [hv, hj, show j + 1 + 2 = j + 3 by ring]
      have h2 := kronZ_two (D := D)
      rw [ite_eq_left hD1] at h2
      push_cast
      rw [h2]
      by_cases h8 : D % 8 = 1
      · rw [sqrtCount_two_pow_of_mod_eight_one h8, ite_eq_left h8]; norm_num
      · rw [sqrtCount_two_pow_of_mod_eight_five (by omega) (by omega), ite_eq_right h8]; norm_num
    · rw [ite_eq_right h2m]
      have h0 : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2m
      rw [hv, h0, zero_add]
      have := sqrtCount_four (D := D) hfund
      norm_num [this]
  · rw [ite_eq_right hp2]
    have hpm : p ∣ m := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · exfalso
        have : p ∣ 2 ^ 2 := by simpa using h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
      · exact h
    rw [ite_eq_left hpm]
    have hv : 1 ≤ (4 * m).factorization p := Nat.Prime.factorization_pos_of_dvd hp h4m hpd
    have : Fact p.Prime := ⟨hp⟩
    rw [sqrtCount_odd_prime_pow hp2 (hpD hpm) hv, kronZ_odd_prime p hp2]
    ring

/-- Helper: **the number of square roots of $D$ modulo $4m$** for a fundamental discriminant $D$ and $m > 0$ prime to
$D$: $\#\{x \in \mathbb Z/4m : x^2 = D\} = 2\prod_{p \mid m}(1 + \chi_D(p))$ (Chinese remainder theorem, Hensel lifting
at odd primes, and the square roots modulo $2^k$). -/
theorem sqrtCount_four_mul {D : ℤ} [IsQuadDisc D] {m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime m D.natAbs) :
    (sqrtCount D (4 * m) : ℤ) = 2 * ∏ p ∈ m.primeFactors, (1 + kronZ D (p : ZMod D.natAbs)) := by
  have h4m : 4 * m ≠ 0 := by omega
  have hmult := Nat.multiplicative_factorization (sqrtCount D) (fun x y h => sqrtCount_mul h D)
    (sqrtCount_one D) h4m
  rw [hmult, Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [Finset.prod_congr rfl (fun p hp => sqrtCount_local hm hcop (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)), Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_ite_eq']
    rw [ite_eq_left]
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, by omega, h4m⟩
  · rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, _, _⟩, hpm⟩; exact ⟨hp, hpm, hm.ne'⟩
    · rintro ⟨hp, hpm, _⟩; exact ⟨⟨hp, dvd_mul_of_dvd_right hpm 4, h4m⟩, hpm⟩

/-! ### Part (a): orbits of primitive representations and the forms $[m, u, v]$ -/

/-- Helper: the form $f \circ M$ for an integer matrix $M$, i.e. $(x, y) \mapsto f(M(x, y)^T)$
(`Binary.BinQF.subst` at the entries of $M$). Arguments: `f` the form, `M` the matrix. -/
def cfM (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) : BinQF := subst (M 0 0) (M 0 1) (M 1 0) (M 1 1) f

/-- Helper: $(f \circ M)(x) = f(Mx)$ for a vector $x \in \mathbb Z^2$. -/
theorem eval_cfM (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval (cfM f M) x = QuadForm.eval f (M *ᵥ x) := by
  rw [eval_mulVec, cfM, vec_two_eq x]
  rfl

/-- Helper: $f \circ (AB) = (f \circ A) \circ B$. -/
theorem cfM_mul (f : BinQF) (A B : Matrix (Fin 2) (Fin 2) ℤ) : cfM f (A * B) = cfM (cfM f A) B := by
  refine ext_eval fun x y => ?_
  have h1 := eval_cfM f (A * B) ![x, y]
  have h2 := eval_cfM (cfM f A) B ![x, y]
  have h3 := eval_cfM f A (B *ᵥ ![x, y])
  rw [mulVec_mulVec] at h3
  exact h1.trans (h3.symm.trans h2.symm)

/-- Helper: the first coefficient of $f \circ M$ is $f$ at the first column of $M$. -/
theorem cfM_a (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) : (cfM f M).a = f.eval (M 0 0) (M 1 0) := by
  simp only [cfM, subst, a_mk, eval_eq]

/-- Helper: the discriminant is unchanged by a determinant-one substitution. -/
theorem cfM_disc (f : BinQF) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = 1) : (cfM f M).disc = f.disc := by
  rw [cfM, disc_subst_of_det _ _ _ _ _ (by rw [← Matrix.det_fin_two, hM]; norm_num)]

/-- Helper: the middle coefficient of $f \circ M$. -/
theorem cfM_b (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (cfM f M).b = 2 * f.a * M 0 0 * M 0 1 + f.b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) + 2 * f.c * M 1 0 * M 1 1 := by
  simp only [cfM, subst, b_mk]

/-- Helper: **a form with given $a$, $b$ and discriminant is determined** when $a \ne 0$. -/
theorem ext_of_a_b_disc {f g : BinQF} (ha : f.a = g.a) (hb : f.b = g.b) (hd : f.disc = g.disc) (h0 : f.a ≠ 0) :
    f = g := by
  refine ext_abc ha hb ?_
  have : 4 * f.a * f.c = 4 * f.a * g.c := by
    unfold disc at hd; rw [← ha, ← hb] at hd; linarith
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) h0) this

/-- Helper: two completions of the same first column $(x, y)$ to a determinant-one matrix differ by a shift of the
second column by a multiple $k$ of the first. -/
theorem exists_shift {x y q s q' s' : ℤ} (h : x * s - q * y = 1) (h' : x * s' - q' * y = 1) :
    ∃ k : ℤ, q' = q + k * x ∧ s' = s + k * y :=
  ⟨s * (q' - q) - q * (s' - s), by linear_combination (-(q' - q) - q) * h + q * h',
    by linear_combination (-(s' - s) - s) * h + s * h'⟩

/-- Helper: shifting the second column by $k$ times the first changes $b$ by $2k f(x, y)$. -/
theorem b_shift (f : BinQF) (x y q s k : ℤ) :
    (subst x (q + k * x) y (s + k * y) f).b = (subst x q y s f).b + 2 * k * f.eval x y := by
  simp only [subst, b_mk, eval_eq]; ring

/-- Helper: **the residue $u \bmod 2m$ attached to a primitive representation $v$ of $m$ by $f$**: complete $v$ to a
matrix $T \in \mathrm{SL}_2(\mathbb Z)$ with first column $v$ and take the middle coefficient $u$ of $f \circ T = [m, u, *]$,
modulo $2m$ (`ub_eq`: independent of the completion). Arguments: `f` the form, `m` the represented integer, `v` the
vector. (Value $0$ if $v$ is not primitive.) -/
noncomputable def ub (f : BinQF) (m : ℕ) (v : Fin 2 → ℤ) : ZMod (2 * m) :=
  if h : IsCoprime (v 0) (v 1) then
    (((subst (v 0) (Classical.choose (exists_subst_a_eq f h)) (v 1)
      (Classical.choose (Classical.choose_spec (exists_subst_a_eq f h))) f).b : ℤ) : ZMod (2 * m))
  else 0

/-- Helper: **`ub` is independent of the completion.** If $f(v) = m$ and $v_0 s - q v_1 = 1$, then
`ub f m v` is the class mod $2m$ of the middle coefficient of
$f \circ \begin{pmatrix} v_0 & q \\ v_1 & s \end{pmatrix}$. -/
theorem ub_eq {f : BinQF} {m : ℕ} {v : Fin 2 → ℤ} (hv : f.eval (v 0) (v 1) = m) {q s : ℤ}
    (h : v 0 * s - q * v 1 = 1) :
    ub f m v = (((subst (v 0) q (v 1) s f).b : ℤ) : ZMod (2 * m)) := by
  have hc : IsCoprime (v 0) (v 1) := ⟨s, -q, by linear_combination h⟩
  unfold ub
  rw [dite_eq_left hc]
  obtain ⟨hdet, -⟩ := Classical.choose_spec (Classical.choose_spec (exists_subst_a_eq f hc))
  have key : ∀ q0 s0 : ℤ, v 0 * s0 - q0 * v 1 = 1 →
      (((subst (v 0) q0 (v 1) s0 f).b : ℤ) : ZMod (2 * m)) = (((subst (v 0) q (v 1) s f).b : ℤ) : ZMod (2 * m)) := by
    intro q0 s0 h0
    obtain ⟨k, hq, hs⟩ := exists_shift h0 h
    rw [hq, hs, b_shift, hv, Int.cast_add]
    have : ((2 * k * (m : ℤ) : ℤ) : ZMod (2 * m)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨k, by push_cast; ring⟩
    rw [this, add_zero]
  exact key _ _ hdet

/-- Helper: `ub` computed from a determinant-one matrix with first column $v$. -/
theorem ub_eq_matrix {f : BinQF} {m : ℕ} {v : Fin 2 → ℤ} (hv : f.eval (v 0) (v 1) = m)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = 1) (h0 : M 0 0 = v 0) (h1 : M 1 0 = v 1) :
    ub f m v = (((cfM f M).b : ℤ) : ZMod (2 * m)) := by
  have hd : v 0 * M 1 1 - M 0 1 * v 1 = 1 := by rw [← h0, ← h1, ← Matrix.det_fin_two]; exact hM
  rw [ub_eq hv hd, cfM, h0, h1]

/-- Helper: $f(v_0, v_1)$ is the value `QuadForm.eval` at the vector $v$. -/
theorem eval_binQF_vec (f : BinQF) (v : Fin 2 → ℤ) : f.eval (v 0) (v 1) = QuadForm.eval f v := by
  rw [BinQF.eval, ← vec_two_eq v]

/-- Helper: a primitive vector is the first column of a matrix of determinant $1$. -/
theorem exists_completion {v : Fin 2 → ℤ} (h : IsCoprime (v 0) (v 1)) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ M 0 0 = v 0 ∧ M 1 0 = v 1 := by
  obtain ⟨r, s, hdet, -⟩ := exists_subst_a_eq (BinQF.mk 1 0 0) h
  exact ⟨!![v 0, r; v 1, s], by rw [Matrix.det_fin_two_of]; exact hdet, by simp, by simp⟩

/-- Helper: **the class `ub f m v` is the image of a square root of $D$ modulo $4m$.** If $f$ has discriminant $D$ and
$f(v) = m$ with $v$ primitive, then $\mathrm{ub}(f, m, v) = u \bmod 2m$ with $u^2 \equiv D \pmod{4m}$. -/
theorem ub_mem {f : BinQF} {D : ℤ} {m : ℕ} {v : Fin 2 → ℤ} (hf : f.disc = D)
    (hv : f.eval (v 0) (v 1) = m) (hc : IsCoprime (v 0) (v 1)) :
    ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
      ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) x = ub f m v := by
  obtain ⟨M, hM, h0, h1⟩ := exists_completion hc
  refine ⟨(((cfM f M).b : ℤ) : ZMod (4 * m)), ?_, ?_⟩
  · rw [intCast_mul_self_eq_iff]
    have ha : (cfM f M).a = m := by rw [cfM_a, h0, h1, hv]
    have hd := cfM_disc f hM
    rw [hf] at hd
    unfold BinQF.disc at hd
    rw [ha] at hd
    exact ⟨(cfM f M).c, by push_cast; linear_combination hd⟩
  · rw [map_intCast, ub_eq_matrix hv hM h0 h1]

/-- Helper: **`ub` is invariant under the proper automorphs of $f$.** -/
theorem ub_aut {f : BinQF} {m : ℕ} {v : Fin 2 → ℤ} (hv : f.eval (v 0) (v 1) = m)
    (hc : IsCoprime (v 0) (v 1)) {γ : GL (Fin 2) ℤ} (hγ : γ ∈ AutSL f) :
    f.eval ((γ.val *ᵥ v) 0) ((γ.val *ᵥ v) 1) = m ∧ ub f m (γ.val *ᵥ v) = ub f m v := by
  have hγa : cfM f γ.val = f := mem_aut_iff.mp (mem_autSL.mp hγ).1
  have hγd : γ.val.det = 1 := (mem_autSL.mp hγ).2
  have hev : f.eval ((γ.val *ᵥ v) 0) ((γ.val *ᵥ v) 1) = m := by
    rw [eval_binQF_vec, ← eval_cfM, hγa, ← eval_binQF_vec, hv]
  refine ⟨hev, ?_⟩
  obtain ⟨M, hM, h0, h1⟩ := exists_completion hc
  have hdet : (γ.val * M).det = 1 := by rw [Matrix.det_mul, hγd, hM, one_mul]
  have e0 : (γ.val * M) 0 0 = (γ.val *ᵥ v) 0 := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  have e1 : (γ.val * M) 1 0 = (γ.val *ᵥ v) 1 := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  rw [ub_eq_matrix hev hdet e0 e1, ub_eq_matrix hv hM h0 h1, cfM_mul, hγa]

/-- Helper: a substitution of determinant $1$ gives a properly equivalent form. -/
theorem sLEquiv_cfM (f : BinQF) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = 1) : SLEquiv f (cfM f M) :=
  (sLEquiv_iff _ _).mpr ⟨M 0 0, M 0 1, M 1 0, M 1 1, by rw [← Matrix.det_fin_two]; exact hM, rfl⟩

/-- Helper: **same residue, same data.** If $f$, $g$ have discriminant $D$ and $f(v) = m = g(w)$ with $v$, $w$
primitive and `ub f m v = ub g m w`, then there are determinant-one matrices $M$, $N$ with first columns $v$, $w$ and
$f \circ M = g \circ N$. -/
theorem ub_inj_core {D : ℤ} {f g : BinQF} {m : ℕ} (hm : 0 < m) (hf : f.disc = D) (hg : g.disc = D)
    {v w : Fin 2 → ℤ} (hv : f.eval (v 0) (v 1) = m) (hw : g.eval (w 0) (w 1) = m)
    (hcv : IsCoprime (v 0) (v 1)) (hcw : IsCoprime (w 0) (w 1)) (h : ub f m v = ub g m w) :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ N.det = 1 ∧ M 0 0 = v 0 ∧ M 1 0 = v 1 ∧
      N 0 0 = w 0 ∧ N 1 0 = w 1 ∧ cfM f M = cfM g N := by
  obtain ⟨M, hM, hM0, hM1⟩ := exists_completion hcv
  obtain ⟨N, hN, hN0, hN1⟩ := exists_completion hcw
  rw [ub_eq_matrix hv hM hM0 hM1, ub_eq_matrix hw hN hN0 hN1, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  push_cast at hk
  set N' : Matrix (Fin 2) (Fin 2) ℤ := !![w 0, N 0 1 + (-k) * w 0; w 1, N 1 1 + (-k) * w 1] with hN'
  have hN'det : N'.det = 1 := by
    rw [hN', Matrix.det_fin_two_of]
    rw [Matrix.det_fin_two, hN0, hN1] at hN
    linear_combination hN
  have hcN : cfM g N = subst (w 0) (N 0 1) (w 1) (N 1 1) g := by rw [cfM, hN0, hN1]
  have hcN' : cfM g N' = subst (w 0) (N 0 1 + (-k) * w 0) (w 1) (N 1 1 + (-k) * w 1) g := by
    simp [cfM, hN']
  refine ⟨M, N', hM, hN'det, hM0, hM1, by simp [hN'], by simp [hN'], ?_⟩
  have ha1 : (cfM f M).a = m := by rw [cfM_a, hM0, hM1, hv]
  have ha2 : (cfM g N').a = m := by rw [cfM_a]; simp [hN', hw]
  have hb2 : (cfM g N').b = (cfM g N).b + 2 * (-k) * m := by
    rw [hcN', hcN, b_shift, hw]
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ext_of_a_b_disc (by rw [ha1, ha2]) ?_ ?_ (by rw [ha1]; exact hm0)
  · rw [hb2]; linarith
  · rw [cfM_disc f hM, cfM_disc g hN'det, hf, hg]

/-- Helper: **equal substituted forms give a proper automorph.** If $f \circ M = f \circ N$ for determinant-one
matrices $M$, $N$, then some proper automorph $\gamma$ of $f$ carries the first column of $M$ to that of $N$. -/
theorem exists_aut_of_cfM_eq {f : BinQF} {M N : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = 1) (hN : N.det = 1)
    (h : cfM f M = cfM f N) {v w : Fin 2 → ℤ} (hv : M *ᵥ ![1, 0] = v) (hw : N *ᵥ ![1, 0] = w) :
    ∃ γ ∈ AutSL f, γ.val *ᵥ v = w := by
  let Ms : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨M, hM⟩
  let Ns : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨N, hN⟩
  have hγ : ((Matrix.SpecialLinearGroup.toGL (Ns * Ms⁻¹)).val : Matrix (Fin 2) (Fin 2) ℤ) = N * M.adjugate := by
    show ((Ns * Ms⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  have hMadj : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hM, one_smul]
  have hadjM : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hM, one_smul]
  refine ⟨Matrix.SpecialLinearGroup.toGL (Ns * Ms⁻¹), ?_, ?_⟩
  · rw [mem_autSL]
    refine ⟨?_, Matrix.SpecialLinearGroup.det_coe (Ns * Ms⁻¹)⟩
    rw [mem_aut_iff]
    show cfM f ((Matrix.SpecialLinearGroup.toGL (Ns * Ms⁻¹)).val) = f
    rw [hγ, cfM_mul, ← h, ← cfM_mul, hMadj]
    exact ext_abc (by simp [cfM]) (by simp [cfM]) (by simp [cfM])
  · rw [hγ, ← hv, ← hw, mulVec_mulVec, mul_assoc, hadjM, mul_one]

/-- Helper: the first column of a matrix as a matrix-vector product. -/
theorem mulVec_col0 {M : Matrix (Fin 2) (Fin 2) ℤ} {v : Fin 2 → ℤ} (h0 : M 0 0 = v 0) (h1 : M 1 0 = v 1) :
    M *ᵥ ![1, 0] = v := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

/-- Helper: the set of orbits of the proper automorphs of $f$ on the primitive representations of $m$ by $f$
(the quotient defining `primRepOrbitCount`). -/
abbrev OrbQ (f : BinQF) (m : ℕ) : Type :=
  Quotient ((autOrbitSetoid f).comap (Subtype.val : primRepVecs f m → Fin 2 → ℤ))

/-- Helper: the residue class `ub` as a function on orbits (well defined by `ub_aut`). -/
noncomputable def ubQ (f : BinQF) (m : ℕ) : OrbQ f m → ZMod (2 * m) :=
  Quotient.lift (fun v : primRepVecs f m => ub f m v.1) (by
    intro v w hvw
    obtain ⟨γ, hγ, h⟩ := hvw
    have := (ub_aut (f := f) (m := m) v.2.1 v.2.2 hγ).2
    rw [h] at this
    exact this.symm)

section Count

open QuadFormsKB.Composition

variable (D : ℤ) (m : ℕ)

/-- Helper: the map from all orbits of primitive representations of $m$ by all classes to residues mod $2m$. -/
noncomputable def ubTot : (Σ c : FormClass D, OrbQ (Quotient.out c).1 m) → ZMod (2 * m) :=
  fun x => ubQ (Quotient.out x.1).1 m x.2

variable {D m}

/-- Helper: `ubTot` is injective (distinct orbits of distinct classes give distinct residues mod $2m$). -/
theorem ubTot_injective (hm : 0 < m) : Function.Injective (ubTot D m) := by
  rintro ⟨c, q⟩ ⟨c', q'⟩ h
  induction q using Quotient.inductionOn with | _ v => ?_
  induction q' using Quotient.inductionOn with | _ w => ?_
  have hf := (Quotient.out c).2.2
  have hg := (Quotient.out c').2.2
  obtain ⟨M, N, hM, hN, hM0, hM1, hN0, hN1, hMN⟩ := ub_inj_core hm hf hg v.2.1 w.2.1 v.2.2 w.2.2 h
  have hcc : c = c' := by
    have h1 : SLEquiv (Quotient.out c).1 (Quotient.out c').1 :=
      (sLEquiv_cfM _ hM).trans (hMN ▸ (sLEquiv_cfM _ hN).symm)
    have h2 := FormClass.mk_eq_mk.2 h1
    have e1 : FormClass.mk (Quotient.out c) = c := Quotient.out_eq c
    have e2 : FormClass.mk (Quotient.out c') = c' := Quotient.out_eq c'
    rw [e1, e2] at h2
    exact h2
  subst hcc
  obtain ⟨γ, hγ, hγv⟩ := exists_aut_of_cfM_eq hM hN hMN (mulVec_col0 hM0 hM1) (mulVec_col0 hN0 hN1)
  congr 1
  exact Quotient.sound ⟨γ, hγ, hγv⟩

/-- Helper: **the residues attained.** The image of `ubTot` is the set of classes $u \bmod 2m$ with $u^2 \equiv D
\pmod{4m}$ (the images of the square roots of $D$ modulo $4m$). -/
theorem range_ubTot [IsQuadDisc D] :
    Set.range (ubTot D m) = {u | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
      ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) x = u} := by
  ext u
  constructor
  · rintro ⟨⟨c, q⟩, rfl⟩
    induction q using Quotient.inductionOn with | _ v => ?_
    exact ub_mem (Quotient.out c).2.2 v.2.1 v.2.2
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [intCast_mul_self_eq_iff] at hx
    obtain ⟨c', hc'⟩ := hx
    push_cast at hc'
    set g : BinQF := BinQF.mk m z c' with hg
    have hgD : g.disc = D := by
      simp only [hg, BinQF.disc, a_mk, b_mk, c_mk]; linear_combination hc'
    have hprim : g.IsPrimitive := isPrimitive_of_fund (IsQuadDisc.fund) hgD
    let G : PrimForm D := ⟨g, hprim, hgD⟩
    obtain ⟨c, hc⟩ : ∃ c : FormClass D, c = FormClass.mk G := ⟨_, rfl⟩
    have hcl : SLEquiv (Quotient.out c).1 g := by
      have e1 : FormClass.mk (Quotient.out c) = c := Quotient.out_eq c
      exact (FormClass.mk_eq_mk (f := Quotient.out c) (g := G)).1 (e1.trans hc)
    obtain ⟨p, q, r, s, hdet, hsub⟩ := (sLEquiv_iff _ _).1 hcl
    have h10 := eval_subst p q r s (Quotient.out c).1 1 0
    rw [hsub] at h10
    have hev : (Quotient.out c).1.eval p r = m := by
      have h1 : g.eval 1 0 = m := by rw [eval_eq]; simp [hg]
      simpa [h1] using h10.symm
    have hcop : IsCoprime p r := ⟨s, -q, by linear_combination hdet⟩
    refine ⟨⟨c, Quotient.mk _ ⟨![p, r], hev, hcop⟩⟩, ?_⟩
    show ub (Quotient.out c).1 m ![p, r] = _
    rw [ub_eq (q := q) (s := s) (by simpa using hev) (by simpa using hdet)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hsub, hg, b_mk, map_intCast]

/-- Helper: **doubling.** Each residue class mod $2m$ containing a square root of $D$ modulo $4m$ contains exactly two
of them ($x$ and $x + 2m$), so $\#\{x \bmod 4m : x^2 = D\} = 2\,\#\{u \bmod 2m : u \text{ lifts to such an } x\}$. -/
theorem sqrtCount_eq_two_mul_card (hm : 0 < m) (D : ℤ) :
    sqrtCount D (4 * m) = 2 * Nat.card {u : ZMod (2 * m) | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
      ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) x = u} := by
  classical
  have : NeZero (4 * m) := ⟨by omega⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  set φ := ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) with hφ
  set S : Finset (ZMod (4 * m)) := Finset.univ.filter (fun x => x * x = (D : ZMod (4 * m))) with hS
  have h1 : sqrtCount D (4 * m) = S.card := by
    unfold sqrtCount; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : Nat.card {u : ZMod (2 * m) | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧ φ x = u} =
      (S.image φ).card := by
    have hiff : ∀ u : ZMod (2 * m), u ∈ {u : ZMod (2 * m) | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
        φ x = u} ↔ u ∈ S.image φ := by
      intro u; simp [hS, Finset.mem_image]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_coe]
  set a : ZMod (4 * m) := 2 * (m : ZMod (4 * m)) with ha
  have h4 : (4 : ZMod (4 * m)) * (m : ZMod (4 * m)) = 0 := by
    have := ZMod.natCast_self (4 * m)
    push_cast at this; exact this
  have ha2 : 2 * a = 0 := by rw [ha]; linear_combination h4
  have haa : a * a = 0 := by rw [ha]; linear_combination (m : ZMod (4 * m)) * h4
  have hφa : φ a = 0 := by
    rw [ha, map_mul, map_natCast, map_ofNat]
    have := ZMod.natCast_self (2 * m)
    push_cast at this; exact this
  have hane : a ≠ 0 := by
    intro h0
    have : ((2 * m : ℕ) : ZMod (4 * m)) = 0 := by push_cast; rw [ha] at h0; exact h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hfib : ∀ u ∈ S.image φ, (S.filter (fun x => φ x = u)).card = 2 := by
    intro u hu
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.card_eq_two]
    refine ⟨x0, x0 + a, fun h => hane (by simpa using h.symm), ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxS, hφx⟩
      have ht : x - x0 = ((x - x0).val : ZMod (4 * m)) := (ZMod.natCast_zmod_val _).symm
      have h0 : (((x - x0).val : ℕ) : ZMod (2 * m)) = 0 := by
        have := congrArg φ ht
        rw [map_sub, hφx, sub_self, map_natCast] at this
        exact this.symm
      rw [ZMod.natCast_eq_zero_iff] at h0
      obtain ⟨k, hk⟩ := h0
      have hlt := ZMod.val_lt (x - x0)
      have hk2 : k < 2 := by
        by_contra hge
        replace hge := not_lt.mp hge
        have := Nat.mul_le_mul_left (2 * m) hge
        omega
      interval_cases k
      · left
        have : x - x0 = 0 := by rw [ht, hk]; simp
        exact sub_eq_zero.1 this
      · right
        have : x - x0 = a := by rw [ht, hk, ha]; push_cast; ring
        rw [← this]; ring
    · rintro (rfl | rfl)
      · exact ⟨hx0, rfl⟩
      · refine ⟨?_, ?_⟩
        · have hx0' : x0 * x0 = (D : ZMod (4 * m)) := by simpa [hS] using hx0
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          linear_combination hx0' + x0 * ha2 + haa
        · rw [map_add, hφa, add_zero]
  rw [h1, h2, Finset.card_eq_sum_card_image φ S, Finset.sum_congr rfl hfib]
  simp [mul_comm]

/-- Helper: **the number of orbits, summed over the classes**, is the number of residues attained by `ubTot`. -/
theorem sum_orbit_count_eq [IsQuadDisc D] (hm : 0 < m) :
    ∑ᶠ c : FormClass D, primRepOrbitCount (Quotient.out c).1 m = Nat.card (Set.range (ubTot D m)) := by
  classical
  have : NeZero (2 * m) := ⟨by omega⟩
  have hinj := ubTot_injective (D := D) hm
  have : NonzeroDisc D := ⟨(IsQuadDisc.fund (D := D)).ne_zero, (IsQuadDisc.fund (D := D)).1⟩
  have : Finite (FormClass D) := FormClass.finite
  have : Fintype (FormClass D) := Fintype.ofFinite _
  have hfin : Finite (Σ c : FormClass D, OrbQ (Quotient.out c).1 m) := Finite.of_injective _ hinj
  have : ∀ c : FormClass D, Finite (OrbQ (Quotient.out c).1 m) := fun c =>
    Finite.of_injective (fun q => (⟨c, q⟩ : Σ c : FormClass D, OrbQ (Quotient.out c).1 m))
      (fun q q' h => by simpa using h)
  have e : ∀ c : FormClass D, primRepOrbitCount (Quotient.out c).1 m = Nat.card (OrbQ (Quotient.out c).1 m) :=
    fun c => rfl
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun c _ => e c), ← Nat.card_sigma]
  exact Nat.card_congr (Equiv.ofInjective _ hinj)

end Count

/-- Helper: for a prime $p$ not dividing the fundamental discriminant $D$, $\chi_D(p) = \pm 1$. -/
theorem kronZ_prime_eq_one_or_neg_one {D : ℤ} [IsQuadDisc D] {p : ℕ} (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) :
    kronZ D (p : ZMod D.natAbs) = 1 ∨ kronZ D (p : ZMod D.natAbs) = -1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have hfund := (IsQuadDisc.fund (D := D)).1
    have hDodd : D % 4 = 1 := by
      rcases hfund with h | h
      · exfalso; apply hpD; exact_mod_cast (show (2 : ℤ) ∣ D by omega)
      · exact h
    have h2 := kronZ_two (D := D)
    rw [ite_eq_left hDodd] at h2
    push_cast
    rw [h2]
    by_cases h8 : D % 8 = 1
    · left; rw [ite_eq_left h8]
    · right; rw [ite_eq_right h8]
  · have : Fact p.Prime := ⟨hp⟩
    rw [kronZ_odd_prime p hp2]
    refine legendreSym.eq_one_or_neg_one p ?_
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Helper: **the product of the local factors.** For $m > 0$ prime to $D$,
$\prod_{p \mid m}(1 + \chi_D(p)) = 2^{\mu}$ if $\chi_D(p) = 1$ for all primes $p \mid m$ ($\mu$ the number of distinct
prime divisors of $m$), and $0$ otherwise. -/
theorem prod_one_add_kronZ {D : ℤ} [IsQuadDisc D] {m : ℕ} (hcop : Nat.Coprime m D.natAbs) :
    ∏ p ∈ m.primeFactors, (1 + kronZ D (p : ZMod D.natAbs)) =
      if ∀ p ∈ m.primeFactors, kronZ D (p : ZMod D.natAbs) = 1 then (2 : ℤ) ^ m.primeFactors.card else 0 := by
  by_cases hall : ∀ p ∈ m.primeFactors, kronZ D (p : ZMod D.natAbs) = 1
  · rw [ite_eq_left hall, Finset.prod_congr rfl (fun p hp => by rw [hall p hp]; norm_num : ∀ p ∈ m.primeFactors,
      1 + kronZ D (p : ZMod D.natAbs) = 2), Finset.prod_const]
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨p, hp, hne⟩ := hall
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    have hpD : ¬ (p : ℤ) ∣ D := by
      intro hpD
      have : p ∣ D.natAbs := Int.natCast_dvd.mp hpD
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpm this)
    have hneg : kronZ D (p : ZMod D.natAbs) = -1 :=
      (kronZ_prime_eq_one_or_neg_one hpp hpD).resolve_left hne
    exact Finset.prod_eq_zero hp (by rw [hneg]; norm_num)

/-- **Cassels, Appendix B, §2, Lemma 2.2 (p. 372): the count $2^\mu$ of orbits of primitive representations, proved.**
For a fundamental discriminant $D$ and every integer $m > 0$ prime to $D$, the total number, over all proper classes of
forms of discriminant $D$ (`Composition.FormClass D`), of orbits of the proper automorphs on the primitive
representations of $m$ is $2^{\mu}$ if every prime divisor $p$ of $m$ has $(D/p) = +1$ ($\mu$ the number of distinct
prime divisors of $m$), and $0$ otherwise. This is the named statement `PrimRepOrbitCount D`, now an unconditional
theorem.

**Proof (following the book).** Complete a primitive representation $v = (x_0, y_0)$ of $m$ by a form $f$ to a matrix
$T \in \mathrm{SL}_2(\mathbb Z)$ with first column $v$; then $f \circ T = [m, u, *]$ with $u^2 \equiv D \pmod{4m}$, and a
different completion changes $u$ by a multiple of $2m$ (`ub_eq`). The residue $u \bmod 2m$ is constant on the orbits of
the proper automorphs (`ub_aut`), and it separates the orbits of all classes (`ubTot_injective`: two data with the same
residue give $f \circ M = g \circ N$, so $f$ and $g$ are properly equivalent, and then $\gamma = N M^{-1}$ is a proper
automorph of $f$, `exists_aut_of_cfM_eq`). Every residue with $u^2 \equiv D \pmod{4m}$ is attained, since $[m, u, v]$
represents $m$ primitively by $(1, 0)$ (`range_ubTot`). So the count equals the number of $u \bmod 2m$ with
$u^2 \equiv D \pmod{4m}$, i.e. half the number of square roots of $D$ modulo $4m$ (`sqrtCount_eq_two_mul_card`). That
number is $2\prod_{p \mid m}(1 + (D/p))$ by the Chinese remainder theorem, Hensel lifting at odd primes
(`sqrtCount_mul_prime`) and the four square roots modulo $2^k$ when $D \equiv 1 \pmod 8$ (`sqrtCount_four_mul`), and the
product is $2^\mu$ or $0$ (`prod_one_add_kronZ`).

Unconditional. Argument: `D` the fundamental discriminant (`IsQuadDisc D`). -/
@[kb "cassels1978" "App. B, §2, Lemma 2.2, p. 372 (the count 2^μ of orbits of primitive representations, proved)"]
theorem primRepOrbitCount_holds (D : ℤ) [IsQuadDisc D] : PrimRepOrbitCount D where
  count m hm hcop := by
    rw [sum_orbit_count_eq hm, range_ubTot]
    have h1 := sqrtCount_eq_two_mul_card hm D
    have h2 := sqrtCount_four_mul (D := D) hm hcop
    rw [prod_one_add_kronZ hcop] at h2
    have hiff : (∀ p ∈ m.primeFactors, kroneckerChar D (p : ZMod D.natAbs) = 1) ↔
        ∀ p ∈ m.primeFactors, kronZ D (p : ZMod D.natAbs) = 1 := by
      simp only [kroneckerChar_apply, Int.cast_eq_one]
    simp only [hiff]
    rw [h1] at h2
    push_cast at h2
    split_ifs at h2 ⊢ with hall
    · exact_mod_cast (by linarith : (Nat.card ↑{u : ZMod (2 * m) | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
        ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) x = u} : ℤ) = 2 ^ m.primeFactors.card)
    · exact_mod_cast (by linarith : (Nat.card ↑{u : ZMod (2 * m) | ∃ x : ZMod (4 * m), x * x = (D : ZMod (4 * m)) ∧
        ZMod.castHom (show 2 * m ∣ 4 * m from ⟨2, by ring⟩) (ZMod (2 * m)) x = u} : ℤ) = 0)

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.2, (2.13) (pp. 372–373), unconditional:** for real $s > 1$,
$$\sum_{f}{}^{*}\ \sum_{\substack{m > 0\\ (m, D) = 1}}a_f(m)\,m^{-s} = \prod_{(D/p) = +1}\frac{1 + p^{-s}}{1 - p^{-s}},$$
where $\sum^*_f$ runs over the classes of forms of discriminant $D$ (`Composition.FormClass D`, with a representative
`Quotient.out c`), $a_f(m)$ = `primRepOrbitCount f m`, and the product is over all primes $p$ with the factor $1$ when
$(D/p) \ne +1$. This is `cor_lemma_2_2` with its hypothesis `PrimRepOrbitCount D` discharged by
`primRepOrbitCount_holds`. Arguments: `D` the fundamental discriminant, `s` real with `hs : 1 < s`. -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.2, (2.13), pp. 372–373 (unconditional)"]
theorem cor_lemma_2_2_uncond (D : ℤ) [IsQuadDisc D] {s : ℝ} (hs : 1 < s) :
    ∑ᶠ c : Composition.FormClass D, ∑' m : ℕ,
        (if 0 < m ∧ Nat.Coprime m D.natAbs then (primRepOrbitCount (Quotient.out c).1 m : ℝ) * (m : ℝ) ^ (-s) else 0) =
      ∏' p : Nat.Primes, (if kroneckerChar D p = 1 then
        (1 + ((p : ℕ) : ℝ) ^ (-s)) / (1 - ((p : ℕ) : ℝ) ^ (-s)) else 1) :=
  cor_lemma_2_2 D (primRepOrbitCount_holds D) hs

end QuadFormsKB.Cassels
