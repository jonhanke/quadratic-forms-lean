/-
# Dickson's universal ternary zero forms (*Studies in the Theory of Numbers*, 1930, ch. XII)

**Library** `QuadFormsKB.Historical.DicksonStudies` (historical library, not imported by `QuadFormsKB`). 
Targets, all from Dickson, *Studies in the Theory of
Numbers* (1930), ch. XII, §§ 87-91, pp. 189-193:

* (§ 88, p. 190): necessity of condition (8): if the normal
  form $F$ is universal, then every prime $p \mid t$ satisfies $p \nmid R$ and $R$ is a quadratic residue modulo $p$
  (`dickson_universal_necessary`, **proved**), hence $R$ is prime to $t$ and a square modulo $t$
  (`cond8_of_universal`, **proved**).
* (Theorem 109, § 89, p. 192): for $e = 0$, $F$ is universal
  iff (8) holds. Necessity **proved**; sufficiency **stated** (`DicksonTheorem109Sufficiency`), and the theorem
  `dickson_theorem_109` is proved conditional on it.
* (Theorem 111, § 91, p. 193): for $c$ odd and $e \ge 1$,
  $F$ is universal iff (8) holds and $bd$ is even. Necessity **proved** (`dickson_theorem_111_necessary`); sufficiency
  **stated** (`DicksonTheorem111Sufficiency`), the theorem conditional on it (`dickson_theorem_111`).
* (§§ 87-91): the complete criterion (Theorems 107-111)
  **stated** (`DicksonUniversalCriterion`), and proved conditional on the two sufficiency statements, the stated
  Theorem 110 (`DicksonTheorem110`) and the stated fact that $c$ even, $e \ge 2$ is never universal
  (`DicksonClassicExponent`) (`dickson_universal_criterion_of`).

**Setting.** Dickson calls an integral form *universal* if it represents every integer (positive, negative and $0$),
and a *zero form* if it has a nontrivial integral zero. A universal ternary zero form is equivalent to one in the
normal form
$$F(x, y, z) = 2^e g a\, x y + g b\, y^2 + c\, y z + g d\, z^2,\qquad g, a \text{ odd},\ (a, d) = 1,\ (c, g) = 1,$$
(`normalForm`, `NormalHyp`); $t$ is the largest divisor of $a$ prime to $g$ (`IsPrimeToPart`), $R = c^2 - 4g^2bd$
(`dicksonR`), and condition (8) is "$R$ is prime to $t$ and a square modulo $t$" (`Cond8`).

*Notes.* The printed statement of Theorem 111 reads "$c$ odd, $e = 1$"; the proof treats every $e \ge 1$, and a
computer search (the historical sources occurrence note) supports $e \ge 1$, which is the reading formalized here (not recorded
as an erratum: it may be a typesetting slip of the source or of its text recognition). The sufficiency proofs in
the source use Dirichlet's theorem on primes in arithmetic progressions (to choose $y$ a prime $\pi$ with
$(g d G \mid \pi) = 1$) and are not formalized here; see the loose ends.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.PrincipalIdealDomain
import QuadFormsKB.Citation

namespace QuadFormsKB.Historical.DicksonStudies

/-- Dickson's normal form $F = 2^e g a\, x y + g b\, y^2 + c\, y z + g d\, z^2$. -/
def normalForm (e : ℕ) (g a b c d : ℤ) (x y z : ℤ) : ℤ :=
  2 ^ e * g * a * x * y + g * b * y ^ 2 + c * y * z + g * d * z ^ 2

/-- A ternary integral form is universal if it represents every integer. -/
def Universal (F : ℤ → ℤ → ℤ → ℤ) : Prop := ∀ G : ℤ, ∃ x y z : ℤ, F x y z = G

/-- The hypotheses of the normal form: $g$, $a$ odd, $(a, d) = 1$, $(c, g) = 1$. -/
def NormalHyp (g a c d : ℤ) : Prop := Odd g ∧ Odd a ∧ IsCoprime a d ∧ IsCoprime c g

/-- $t$ is the largest (positive) divisor of $a$ prime to $g$. -/
def IsPrimeToPart (t a g : ℤ) : Prop :=
  0 < t ∧ t ∣ a ∧ IsCoprime t g ∧ ∀ s : ℤ, s ∣ a → IsCoprime s g → s ∣ t

/-- Dickson's $R = c^2 - 4 g^2 b d$ (the discriminant of $g b y^2 + c y z + g d z^2$, up to the factor $g^2$ in the
cross term). -/
def dicksonR (g b c d : ℤ) : ℤ := c ^ 2 - 4 * g ^ 2 * b * d

/-- Dickson's condition (8): $R$ is prime to $t$ and a square modulo $t$. -/
def Cond8 (t R : ℤ) : Prop := IsCoprime R t ∧ ∃ r : ℤ, t ∣ r ^ 2 - R

/-- Hensel lifting for squares at an odd prime. -/
private lemma sq_lift_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (R : ℤ) (hR : ¬ (p : ℤ) ∣ R)
    (h1 : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - R) : ∀ k : ℕ, ∃ r : ℤ, (p : ℤ) ^ (k + 1) ∣ r ^ 2 - R := by
  intro k
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    obtain ⟨r, m, hm⟩ := ih
    have hpi : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).irreducible
    have hpr : ¬ (p : ℤ) ∣ r := by
      intro h
      apply hR
      have h2 : (p : ℤ) ∣ r ^ 2 - R := ⟨p ^ k * m, by rw [hm]; ring⟩
      have h3 : (p : ℤ) ∣ r ^ 2 := dvd_pow h (by norm_num)
      exact (dvd_sub_right h3).mp h2
    have h2 : ¬ (p : ℤ) ∣ 2 := by
      intro h
      have h' : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
      exact hp2 this
    have hc : IsCoprime (p : ℤ) (2 * r) := by
      rw [hpi.coprime_iff_not_dvd]
      intro h
      rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
      · exact h2 h
      · exact hpr h
    obtain ⟨v, u, huv⟩ := hc
    refine ⟨r + (-(m * u)) * (p : ℤ) ^ (k + 1), m * v + (-(m * u)) ^ 2 * (p : ℤ) ^ k, ?_⟩
    linear_combination hm - ((p : ℤ) ^ (k + 1) * m) * huv

private lemma sq_crt (m n R : ℤ) (h : IsCoprime m n) (h1 : ∃ r : ℤ, m ∣ r ^ 2 - R)
    (h2 : ∃ r : ℤ, n ∣ r ^ 2 - R) : ∃ r : ℤ, m * n ∣ r ^ 2 - R := by
  obtain ⟨u, v, huv⟩ := id h
  obtain ⟨r1, hr1⟩ := h1
  obtain ⟨r2, hr2⟩ := h2
  refine ⟨r1 * v * n + r2 * u * m, h.mul_dvd ?_ ?_⟩
  · have h3 : m ∣ (r1 * v * n + r2 * u * m) - r1 :=
      ⟨u * (r2 - r1), by linear_combination r1 * huv⟩
    have h4 : (r1 * v * n + r2 * u * m) ^ 2 - R = ((r1 * v * n + r2 * u * m) - r1) *
        ((r1 * v * n + r2 * u * m) + r1) + (r1 ^ 2 - R) := by ring
    rw [h4]
    exact dvd_add (dvd_mul_of_dvd_left h3 _) ⟨hr1.choose, hr1.choose_spec⟩
  · have h3 : n ∣ (r1 * v * n + r2 * u * m) - r2 :=
      ⟨v * (r1 - r2), by linear_combination r2 * huv⟩
    have h4 : (r1 * v * n + r2 * u * m) ^ 2 - R = ((r1 * v * n + r2 * u * m) - r2) *
        ((r1 * v * n + r2 * u * m) + r2) + (r2 ^ 2 - R) := by ring
    rw [h4]
    exact dvd_add (dvd_mul_of_dvd_left h3 _) ⟨hr2.choose, hr2.choose_spec⟩

private lemma sq_mod_nat (R : ℤ) : ∀ n : ℕ, 0 < n →
    (∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 ∧ ¬ (p : ℤ) ∣ R ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - R) →
    ∃ r : ℤ, (n : ℤ) ∣ r ^ 2 - R := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ H
    obtain ⟨h2, hR, h1⟩ := H p hp (dvd_pow_self p hk.ne')
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simpa using sq_lift_prime_pow p hp h2 R hR h1 k'
  | zero => intro h; omega
  | one => intro _ _; exact ⟨0, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ H
    have := sq_crt (a : ℤ) (b : ℤ) R (Nat.isCoprime_iff_coprime.mpr hab)
      (iha (by omega) fun p hp hpa => H p hp (dvd_mul_of_dvd_left hpa _))
      (ihb (by omega) fun p hp hpb => H p hp (dvd_mul_of_dvd_right hpb _))
    simpa using this

/-- **Necessity of (8)** (Dickson, *Studies* (1930), § 88, p. 190). If the normal form
$F$ (any $e \ge 0$) is universal, then for every prime $p \mid t$: $p \nmid R$ and $R$ is a square modulo $p$. -/
@[kb "dickson1930" "ch. XII, § 88, p. 190"]
theorem dickson_universal_necessary (e : ℕ) (g a b c d t : ℤ) (hN : NormalHyp g a c d)
    (ht : IsPrimeToPart t a g) (hU : Universal (normalForm e g a b c d)) (p : ℕ) (hp : p.Prime)
    (hpt : (p : ℤ) ∣ t) :
    ¬ (p : ℤ) ∣ dicksonR g b c d ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - dicksonR g b c d := by
  have := Fact.mk hp
  obtain ⟨ht0, hta, htg, -⟩ := ht
  obtain ⟨hg, ha, had, hcg⟩ := hN
  have hpa : (p : ℤ) ∣ a := hpt.trans hta
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := ha
    obtain ⟨j, hj⟩ := hpa
    push_cast at hj
    omega
  have hone : ¬ IsUnit (p : ℤ) := by
    rw [Int.isUnit_iff_natAbs_eq]
    simpa using hp.one_lt.ne'
  have hpg : ¬ (p : ℤ) ∣ g := fun h => hone (htg.isUnit_of_dvd' hpt h)
  have hpd : ¬ (p : ℤ) ∣ d := fun h => hone (had.isUnit_of_dvd' hpa h)
  have hz : ∀ n : ℤ, (n : ZMod p) = 0 ↔ (p : ℤ) ∣ n := fun n => ZMod.intCast_zmod_eq_zero_iff_dvd n p
  have hgz : (g : ZMod p) ≠ 0 := fun h => hpg ((hz g).mp h)
  have hdz : (d : ZMod p) ≠ 0 := fun h => hpd ((hz d).mp h)
  have h2z : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hK : (4 * g * d : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2z h2z) hgz) hdz
  have hapz : (a : ZMod p) = 0 := (hz a).mpr hpa
  -- the key identity modulo p
  have key : ∀ (G : ℤ) (x y z : ℤ), normalForm e g a b c d x y z = G →
      (4 * g * d * G : ZMod p) = (2 * g * d * z + c * y) ^ 2 - (dicksonR g b c d : ℤ) * y ^ 2 := by
    intro G x y z h
    have h' : ((normalForm e g a b c d x y z : ℤ) : ZMod p) = (G : ZMod p) := by rw [h]
    simp only [normalForm] at h'
    simp only [dicksonR]
    push_cast at h' ⊢
    rw [hapz] at h'
    linear_combination (4 * (g : ZMod p) * d) * (-h')
  have hRsq : (dicksonR g b c d : ZMod p) ≠ 0 ∧ IsSquare (dicksonR g b c d : ZMod p) := by
    by_cases hR0 : (dicksonR g b c d : ZMod p) = 0
    · exfalso
      obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
      obtain ⟨x, y, z, hF⟩ := hU (((4 * g * d : ZMod p)⁻¹ * n).val : ℤ)
      have := key _ x y z hF
      rw [hR0] at this
      push_cast at this
      rw [ZMod.natCast_zmod_val] at this
      rw [← mul_assoc, mul_inv_cancel₀ hK, one_mul] at this
      exact hn ⟨(2 * g * d * z + c * y : ZMod p), by rw [this]; ring⟩
    · refine ⟨hR0, ?_⟩
      by_contra hns
      exfalso
      obtain ⟨x, y, z, hF⟩ := hU (p : ℤ)
      have := key _ x y z hF
      simp only [Int.cast_natCast, ZMod.natCast_self, mul_zero] at this
      have hRc : (dicksonR g b c d : ZMod p) = c ^ 2 - 4 * g ^ 2 * b * d := by simp [dicksonR]
      rw [hRc] at this hns
      have hy : (y : ZMod p) = 0 := by
        by_contra hy
        apply hns
        refine ⟨((2 * g * d * z + c * y : ZMod p)) / y, ?_⟩
        field_simp
        linear_combination this
      have hz0 : (z : ZMod p) = 0 := by
        rw [hy] at this
        have h3 : (2 * g * d * z : ZMod p) ^ 2 = 0 := by linear_combination -this
        have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
        simpa [h2z, hgz, hdz] using this
      obtain ⟨y', hy'⟩ := (hz y).mp hy
      obtain ⟨z', hz'⟩ := (hz z).mp hz0
      obtain ⟨a', ha'⟩ := hpa
      have h5 : (p : ℤ) * p ∣ (p : ℤ) := by
        refine ⟨2 ^ e * g * a' * x * y' + g * b * y' ^ 2 + c * y' * z' + g * d * z' ^ 2, ?_⟩
        have h7 := hF
        simp only [normalForm] at h7
        rw [hy', hz', ha'] at h7
        linear_combination (-1 : ℤ) * h7
      have h6 : (p : ℤ) ∣ 1 := by
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have := (mul_dvd_mul_iff_left hp0).mp (by simpa using h5 : (p : ℤ) * p ∣ (p : ℤ) * 1)
        exact this
      exact hone (isUnit_of_dvd_one h6)
  obtain ⟨hR0, r', hr'⟩ := hRsq
  refine ⟨fun h => hR0 ((hz _).mpr h), r'.val, ?_⟩
  rw [← hz]
  push_cast
  rw [ZMod.natCast_zmod_val, hr']
  ring

/-- **Necessity of (8), modulo $t$** ("hence modulo $t$"): if the normal form is
universal, then $R$ is prime to $t$ and a square modulo $t$ (from the prime case by Hensel lifting at the odd primes
of $t$ and the Chinese remainder theorem). -/
@[kb "dickson1930" "ch. XII, § 88, p. 190"]
theorem cond8_of_universal (e : ℕ) (g a b c d t : ℤ) (hN : NormalHyp g a c d) (ht : IsPrimeToPart t a g)
    (hU : Universal (normalForm e g a b c d)) : Cond8 t (dicksonR g b c d) := by
  have hnec := dickson_universal_necessary e g a b c d t hN ht hU
  obtain ⟨ht0, hta, htg, -⟩ := ht
  obtain ⟨hg, ha, had, hcg⟩ := hN
  have hcop : IsCoprime (dicksonR g b c d) t := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    apply Nat.coprime_of_dvd
    intro p hp hpR hpt
    have h1 : (p : ℤ) ∣ dicksonR g b c d := Int.natCast_dvd.mpr hpR
    have h2 : (p : ℤ) ∣ t := Int.natCast_dvd.mpr hpt
    exact (hnec p hp h2).1 h1
  refine ⟨hcop, ?_⟩
  have hodd : ∀ p : ℕ, p.Prime → p ∣ t.toNat → p ≠ 2 ∧ ¬ (p : ℤ) ∣ dicksonR g b c d ∧
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - dicksonR g b c d := by
    intro p hp hpt
    have h2 : (p : ℤ) ∣ t := by
      have : (p : ℤ) ∣ (t.toNat : ℤ) := by exact_mod_cast hpt
      rwa [Int.toNat_of_nonneg ht0.le] at this
    refine ⟨?_, hnec p hp h2⟩
    rintro rfl
    obtain ⟨k, hk⟩ := ha
    obtain ⟨j, hj⟩ := h2.trans hta
    push_cast at hj
    omega
  obtain ⟨r, hr⟩ := sq_mod_nat (dicksonR g b c d) t.toNat (by omega) hodd
  exact ⟨r, by rwa [Int.toNat_of_nonneg ht0.le] at hr⟩

/-- **Stated** (sufficiency in Dickson's Theorem 109, § 89, p. 192): for $e = 0$, condition (8) implies that the
normal form is universal. Dickson's proof chooses $y$ a prime in a suitable arithmetic progression (Dirichlet's
theorem) and solves $F \equiv G \pmod{g a y}$ in $z$. -/
def DicksonTheorem109Sufficiency : Prop :=
  ∀ g a b c d t : ℤ, NormalHyp g a c d → IsPrimeToPart t a g → Cond8 t (dicksonR g b c d) →
    Universal (normalForm 0 g a b c d)

/-- **Dickson's Theorem 109** (*Studies* (1930), § 89, p. 192): for $e = 0$ the normal
form $F = g a\, x y + g b\, y^2 + c\, y z + g d\, z^2$ is universal iff (8) holds. Necessity is proved
(`cond8_of_universal`); sufficiency is the stated `DicksonTheorem109Sufficiency`. -/
@[kb "dickson1930" "ch. XII, § 89, Theorem 109, p. 192"]
theorem dickson_theorem_109 (hsuff : DicksonTheorem109Sufficiency) (g a b c d t : ℤ) (hN : NormalHyp g a c d)
    (ht : IsPrimeToPart t a g) :
    Universal (normalForm 0 g a b c d) ↔ Cond8 t (dicksonR g b c d) :=
  ⟨cond8_of_universal 0 g a b c d t hN ht, hsuff g a b c d t hN ht⟩

/-- **Necessity in Dickson's Theorem 111** (*Studies* (1930), § 91, p. 193): for $c$
odd and $e \ge 1$, a universal normal form satisfies (8) and has $b d$ even (if $b$, $d$ are odd, $F$ is even only
when $y$, $z$ are even, and then $4 \mid F$, so $F$ misses $2$). -/
@[kb "dickson1930" "ch. XII, § 91, Theorem 111, p. 193"]
theorem dickson_theorem_111_necessary (e : ℕ) (he : 1 ≤ e) (g a b c d t : ℤ) (hN : NormalHyp g a c d)
    (ht : IsPrimeToPart t a g) (hc : Odd c) (hU : Universal (normalForm e g a b c d)) :
    Cond8 t (dicksonR g b c d) ∧ Even (b * d) := by
  refine ⟨cond8_of_universal e g a b c d t hN ht hU, ?_⟩
  obtain ⟨hg, ha, had, hcg⟩ := hN
  by_contra hbd
  rw [Int.even_mul, not_or] at hbd
  obtain ⟨hb, hd⟩ := hbd
  rw [Int.not_even_iff_odd] at hb hd
  obtain ⟨x, y, z, hF⟩ := hU 2
  have hF2 : ((normalForm e g a b c d x y z : ℤ) : ZMod 2) = 0 := by
    rw [hF]; rfl
  have hg1 := ZMod.intCast_eq_one_iff_odd.mpr hg
  have hb1 := ZMod.intCast_eq_one_iff_odd.mpr hb
  have hc1 := ZMod.intCast_eq_one_iff_odd.mpr hc
  have hd1 := ZMod.intCast_eq_one_iff_odd.mpr hd
  simp only [normalForm] at hF2
  push_cast at hF2
  rw [hg1, hb1, hc1, hd1] at hF2
  have h2e : (2 : ZMod 2) ^ e = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl]
    exact zero_pow (by omega)
  rw [h2e] at hF2
  have hyz : ∀ y z : ZMod 2, y ^ 2 + y * z + z ^ 2 = 0 → y = 0 ∧ z = 0 := by decide
  obtain ⟨hy, hz⟩ := hyz y z (by linear_combination hF2)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hy hz
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨z', hz'⟩ := hz
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have h7 := hF
  simp only [normalForm] at h7
  push_cast at hy' hz'
  rw [hy', hz'] at h7
  have h8 : 4 * (2 ^ e' * g * a * x * y' + g * b * y' ^ 2 + c * y' * z' + g * d * z' ^ 2) = 2 := by
    linear_combination h7
  omega

/-- **Stated** (sufficiency in Dickson's Theorem 111, § 91, p. 193): for $c$ odd and $e \ge 1$, condition (8) and
$b d$ even imply that the normal form is universal. -/
def DicksonTheorem111Sufficiency : Prop :=
  ∀ (e : ℕ) (g a b c d t : ℤ), 1 ≤ e → NormalHyp g a c d → IsPrimeToPart t a g → Odd c →
    Cond8 t (dicksonR g b c d) → Even (b * d) → Universal (normalForm e g a b c d)

/-- **Dickson's Theorem 111** (*Studies* (1930), § 91, p. 193): for $c$ odd and
$e \ge 1$, the normal form is universal iff (8) holds and $b d$ is even; conditional on the stated sufficiency. -/
@[kb "dickson1930" "ch. XII, § 91, Theorem 111, p. 193"]
theorem dickson_theorem_111 (hsuff : DicksonTheorem111Sufficiency) (e : ℕ) (he : 1 ≤ e) (g a b c d t : ℤ)
    (hN : NormalHyp g a c d) (ht : IsPrimeToPart t a g) (hc : Odd c) :
    Universal (normalForm e g a b c d) ↔ Cond8 t (dicksonR g b c d) ∧ Even (b * d) :=
  ⟨dickson_theorem_111_necessary e he g a b c d t hN ht hc,
    fun h => hsuff e g a b c d t he hN ht hc h.1 h.2⟩

/-- **Stated** (Dickson's Theorem 110, § 90, p. 192): for $e = 1$ and $c$ even (a classic form), the normal form is
universal iff (8) holds and either $d$ is odd, or $d \equiv 2 \pmod 4$ and $b$ is odd. -/
def DicksonTheorem110 : Prop :=
  ∀ g a b c d t : ℤ, NormalHyp g a c d → IsPrimeToPart t a g → Even c →
    (Universal (normalForm 1 g a b c d) ↔
      Cond8 t (dicksonR g b c d) ∧ (Odd d ∨ (d % 4 = 2 ∧ Odd b)))

/-- **Stated** (Dickson, § 90, p. 193): a normal form with $c$ even and $e \ge 2$ is never
universal. -/
def DicksonClassicExponent : Prop :=
  ∀ (e : ℕ) (g a b c d : ℤ), 2 ≤ e → NormalHyp g a c d → Even c → ¬ Universal (normalForm e g a b c d)

/-- **Stated** (Dickson, *Studies* (1930), §§ 87-91, Theorems 107-111): the normal
form $F$ is universal iff (8) holds and one of: $e = 0$; $e = 1$, $c$ even, and ($d$ odd, or $d \equiv 2 \pmod 4$
and $b$ odd); $e \ge 1$, $c$ odd, and $b d$ even. -/
def DicksonUniversalCriterion : Prop :=
  ∀ (e : ℕ) (g a b c d t : ℤ), NormalHyp g a c d → IsPrimeToPart t a g →
    (Universal (normalForm e g a b c d) ↔ Cond8 t (dicksonR g b c d) ∧
      (e = 0 ∨ (e = 1 ∧ Even c ∧ (Odd d ∨ (d % 4 = 2 ∧ Odd b))) ∨ (1 ≤ e ∧ Odd c ∧ Even (b * d))))

/-- **The complete criterion, conditionally**: Dickson's criterion for universal
ternary zero forms in normal form follows from the sufficiency halves of Theorems 109 and 111, Theorem 110 and the
exclusion of $c$ even, $e \ge 2$ (all four stated); the necessity of (8) is proved. -/
@[kb "dickson1930" "ch. XII, §§ 87-91, pp. 189-193"]
theorem dickson_universal_criterion_of (h109 : DicksonTheorem109Sufficiency) (h110 : DicksonTheorem110)
    (h111 : DicksonTheorem111Sufficiency) (hcl : DicksonClassicExponent) : DicksonUniversalCriterion := by
  intro e g a b c d t hN ht
  by_cases he0 : e = 0
  · subst he0
    constructor
    · intro h
      exact ⟨cond8_of_universal 0 g a b c d t hN ht h, Or.inl rfl⟩
    · intro h
      exact h109 g a b c d t hN ht h.1
  rcases Int.even_or_odd c with hc | hc
  · by_cases he1 : e = 1
    · subst he1
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := (h110 g a b c d t hN ht hc).mp h
        exact ⟨h1, Or.inr (Or.inl ⟨rfl, hc, h2⟩)⟩
      · rintro ⟨h1, h | h | h⟩
        · exact absurd h (by omega)
        · exact (h110 g a b c d t hN ht hc).mpr ⟨h1, h.2.2⟩
        · exact absurd hc (Int.not_even_iff_odd.mpr h.2.1)
    · constructor
      · intro h
        exact absurd h (hcl e g a b c d (by omega) hN hc)
      · rintro ⟨h1, h | h | h⟩
        · exact absurd h he0
        · exact absurd h.1 he1
        · exact absurd hc (Int.not_even_iff_odd.mpr h.2.1)
  · have he : 1 ≤ e := by omega
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := dickson_theorem_111_necessary e he g a b c d t hN ht hc h
      exact ⟨h1, Or.inr (Or.inr ⟨he, hc, h2⟩)⟩
    · rintro ⟨h1, h | h | h⟩
      · exact absurd h he0
      · exact absurd h.2.1 (Int.not_even_iff_odd.mpr hc)
      · exact h111 e g a b c d t he hN ht hc h1 h.2.2

end QuadFormsKB.Historical.DicksonStudies
