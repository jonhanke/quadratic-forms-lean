/-
# Cassels, Chapter 14, Examples 1 and 2 (iv): fundamental discriminants; the Kronecker symbol at $-1$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Examples, pp. 358–359.

* Ex. 1: an integer $D \ne 0$ is a *discriminant* if $D \equiv 0, 1 \pmod 4$; it is *fundamental* if it is not of the
  shape $D_0b^2$ with $D_0$ a discriminant and $b^2 > 1$. Cassels' definition agrees with Mathlib's
  `Int.IsFundamentalDiscr` (`isCasselsFundamental_iff`). (i) Every discriminant is uniquely $D = D_0b^2$ with $D_0$
  fundamental (and $b > 0$) (`ex1_i`). (ii) $8, -8, -4$ and $(-1)^{(p-1)/2}p$ ($p$ an odd prime) are fundamental, and
  every fundamental discriminant is uniquely a product of distinct members of this set (`ex1_ii_mem`, `ex1_ii`).
  (Cassels prints "produce" for "product".)
* Ex. 2 (iv): with the Kronecker symbol $(D/b)$ of Ex. 2 (Siegel's `kroneckerSym`, the same definition) extended to
  $b < 0$ by periodicity modulo $D$, $(D/{-1}) = 1$ if $D > 0$ and $-1$ if $D < 0$: for every $b > 0$ prime to $D$
  with $b \equiv -1 \pmod D$, $(D/b) = \operatorname{sign} D$ (`ex2_iv`). The display is lost in the machine-read
  text and was read from the page image (p. 359).
-/
import QuadFormsKB.Siegel.ThetaCharacter

namespace QuadFormsKB.Composition

/-- **Cassels' fundamental discriminant** (Ch. 14, Ex. 1, p. 358): $D \ne 0$, $D \equiv 0, 1 \pmod 4$, and $D$ is not
$D_0b^2$ with $D_0 \equiv 0, 1 \pmod 4$ and $b^2 > 1$. -/
def IsCasselsFundamental (D : ℤ) : Prop :=
  D ≠ 0 ∧ (D % 4 = 0 ∨ D % 4 = 1) ∧ ¬ ∃ D₀ b : ℤ, (D₀ % 4 = 0 ∨ D₀ % 4 = 1) ∧ 1 < b ^ 2 ∧ D = D₀ * b ^ 2

private lemma sq_mod4 (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨k, rfl⟩ : 2 ∣ x := by omega
    left; ring_nf; omega
  · obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    right; ring_nf; omega


private lemma sq_mod4_odd (x : ℤ) (h : x % 2 = 1) : x ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  ring_nf; omega


private lemma mul_mod4 {a c : ℤ} (ha : a % 4 = 0 ∨ a % 4 = 1) (hc : c % 4 = 0 ∨ c % 4 = 1) :
    (a * c) % 4 = 0 ∨ (a * c) % 4 = 1 := by
  rw [Int.mul_emod]; rcases ha with h | h <;> rcases hc with h' | h' <;> simp [h, h']

/-- **Cassels' definition of a fundamental discriminant is Mathlib's** `Int.IsFundamentalDiscr` (Ch. 14, Ex. 1,
p. 358). -/
@[kb "cassels1978" "Ch. 14, Ex. 1, p. 358 (fundamental discriminant)"]
theorem isCasselsFundamental_iff (D : ℤ) : IsCasselsFundamental D ↔ Int.IsFundamentalDiscr D := by
  rw [Int.isFundamentalDiscr_iff_forall_prime]
  constructor
  · rintro ⟨h0, h4, hn⟩
    refine ⟨h4, fun p hp ⟨e, he, he4⟩ => hn ⟨e, p, he4, ?_, by rw [he]; ring⟩⟩
    have := hp.two_le
    have : (2:ℤ) ≤ p := by exact_mod_cast this
    nlinarith
  · rintro ⟨h4, hn⟩
    refine ⟨?_, h4, ?_⟩
    · rintro rfl
      exact hn 2 Nat.prime_two ⟨0, by simp, by simp⟩
    · rintro ⟨D₀, b, hD₀, hb, rfl⟩
      have hb1 : b.natAbs ≠ 1 := by
        intro h
        have : b ^ 2 = 1 := by rw [← Int.natAbs_sq, h]; simp
        omega
      obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
      obtain ⟨c, hc⟩ : (p : ℤ) ∣ b := Int.natCast_dvd.2 hpb
      refine hn p hp ⟨D₀ * c ^ 2, by rw [hc]; ring, mul_mod4 hD₀ (sq_mod4 c)⟩

theorem ex1_key {D₀ D₁ b c : ℤ} (h₀ : Int.IsFundamentalDiscr D₀) (h₁ : Int.IsFundamentalDiscr D₁)
    (h : D₀ * b ^ 2 = D₁ * c ^ 2) {p : ℕ} (hp : p.Prime) (hpb : (p : ℤ) ∣ b)
    (hpc : ¬ (p : ℤ) ∣ c) : False := by
  rw [Int.isFundamentalDiscr_iff_forall_prime] at h₀ h₁
  obtain ⟨b', rfl⟩ := hpb
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcop : IsCoprime ((p : ℤ) ^ 2) (c ^ 2) :=
    (Prime.coprime_iff_not_dvd hpz |>.2 hpc).pow
  have hdv : (p : ℤ) ^ 2 ∣ D₁ := by
    have : (p : ℤ) ^ 2 ∣ D₁ * c ^ 2 := ⟨D₀ * b' ^ 2, by rw [← h]; ring⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨f, hf⟩ := hdv
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : D₀ * b' ^ 2 = f * c ^ 2 := by
    have : (p : ℤ) ^ 2 * (D₀ * b' ^ 2) = (p : ℤ) ^ 2 * (f * c ^ 2) := by
      rw [hf] at h; linarith
    exact mul_left_cancel₀ (pow_ne_zero 2 hp0) this
  refine h₁.2 p hp ⟨f, hf, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hc2 : c % 2 = 1 := by
      have : ¬ (2:ℤ) ∣ c := by exact_mod_cast hpc
      omega
    have := sq_mod4_odd c hc2
    have hm := mul_mod4 h₀.1 (sq_mod4 b')
    rw [h2, Int.mul_emod, this] at hm
    simpa using hm
  · have : ((p : ℤ)) % 2 = 1 := by exact_mod_cast Nat.odd_iff.1 hodd
    have := sq_mod4_odd p this
    have h14 := h₁.1
    rw [hf, Int.mul_emod, this] at h14
    simpa using h14


theorem ex1_uniq {D₀ D₁ : ℤ} (h₀ : Int.IsFundamentalDiscr D₀) (h₁ : Int.IsFundamentalDiscr D₁) :
    ∀ n : ℕ, ∀ b c : ℤ, b.natAbs = n → 0 < b → 0 < c → D₀ * b ^ 2 = D₁ * c ^ 2 → D₀ = D₁ ∧ b = c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b c hn hb hc h
  by_cases hbc : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c
  · obtain ⟨p, hp, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := hbc
    have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
    have hb' : 0 < b' := pos_of_mul_pos_right hb hp0.le
    have hc' : 0 < c' := pos_of_mul_pos_right hc hp0.le
    have h2 : D₀ * b' ^ 2 = D₁ * c' ^ 2 := by
      have : (p : ℤ) ^ 2 * (D₀ * b' ^ 2) = (p : ℤ) ^ 2 * (D₁ * c' ^ 2) := by linarith
      exact mul_left_cancel₀ (pow_ne_zero 2 hp0.ne') this
    have hlt : b'.natAbs < n := by
      rw [← hn, Int.natAbs_mul]
      have := hp.two_le
      have : 0 < b'.natAbs := by omega
      simp only [Int.natAbs_natCast]; nlinarith
    obtain ⟨h1, h2⟩ := ih _ hlt b' c' rfl hb' hc' h2
    exact ⟨h1, by rw [h2]⟩
  · push Not at hbc
    have hb1 : b = 1 := by
      by_contra hne
      have : b.natAbs ≠ 1 := by omega
      obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd this
      exact hbc p hp (Int.natCast_dvd.2 hpb) |> fun h' => ex1_key h₀ h₁ h hp (Int.natCast_dvd.2 hpb) h'
    have hc1 : c = 1 := by
      by_contra hne
      have : c.natAbs ≠ 1 := by omega
      obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd this
      exact ex1_key h₁ h₀ h.symm hp (Int.natCast_dvd.2 hpb) (fun h' => hbc p hp h' (Int.natCast_dvd.2 hpb) |> fun x => x)
    subst hb1; subst hc1
    simpa using h


/-- **Cassels, Ch. 14, Ex. 1 (i)** (p. 358): *every discriminant $D$ ($D \ne 0$, $D \equiv 0, 1 \pmod 4$) can be
written uniquely as $D = D_0b^2$ with $D_0$ a fundamental discriminant*; uniqueness is for $b > 0$. -/
@[kb "cassels1978" "Ch. 14, Ex. 1 (i), p. 358"]
theorem ex1_i {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃! p : ℤ × ℤ, Int.IsFundamentalDiscr p.1 ∧ 0 < p.2 ∧ D = p.1 * p.2 ^ 2 := by
  have ex : ∀ n : ℕ, ∀ D : ℤ, D.natAbs = n → D ≠ 0 → (D % 4 = 0 ∨ D % 4 = 1) →
      ∃ p : ℤ × ℤ, Int.IsFundamentalDiscr p.1 ∧ 0 < p.2 ∧ D = p.1 * p.2 ^ 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro D hn hD hD4
    by_cases hf : Int.IsFundamentalDiscr D
    · exact ⟨(D, 1), hf, one_pos, by simp⟩
    · rw [Int.isFundamentalDiscr_iff_forall_prime] at hf
      push Not at hf
      obtain ⟨p, hp, e, he, he4⟩ := hf hD4
      have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
      have he0 : e ≠ 0 := by rintro rfl; simp at he; exact hD he
      have hlt : e.natAbs < n := by
        rw [← hn, he, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have := hp.two_le
        have : 0 < e.natAbs := by omega
        have h4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith
      obtain ⟨⟨D₀, b⟩, h1, h2, h3⟩ := ih _ hlt e rfl he0 he4
      refine ⟨(D₀, p * b), h1, by simp only; positivity, ?_⟩
      simp only at h3 ⊢
      rw [he, h3]; ring
  refine (ex _ D rfl hD hD4).imp fun p hp => ⟨hp, ?_⟩
  rintro ⟨D₁, c⟩ ⟨h1, h2, h3⟩
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨e1, e2⟩ := ex1_uniq hp1 h1 _ p.2 c rfl hp2 h2 (by rw [← hp3, ← h3])
  exact Prod.ext e1.symm e2.symm ▸ rfl

/-- **Cassels' prime discriminants** (Ch. 14, Ex. 1 (ii), p. 358): $8$, $-8$, $-4$ and $(-1)^{(p-1)/2}p$ for odd
primes $p$. -/
def primeDiscriminants : Set ℤ :=
  {8, -8, -4} ∪ {d | ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ d = (-1) ^ ((p - 1) / 2) * p}

lemma sqf_neg {x : ℤ} (h : Squarefree x) : Squarefree (-x) :=
  fun y hy => h y (by simpa using hy)


lemma qs_cases (p : ℕ) : ((-1 : ℤ) ^ ((p - 1) / 2) * p = p) ∨ ((-1 : ℤ) ^ ((p - 1) / 2) * p = -p) := by
  rcases neg_one_pow_eq_or ℤ ((p - 1) / 2) with h | h <;> rw [h] <;> simp


/-- **Cassels, Ch. 14, Ex. 1 (ii)** (p. 358), first part: *$\pm 8$, $-4$ and $(-1)^{(p-1)/2}p$ are fundamental
discriminants.* -/
@[kb "cassels1978" "Ch. 14, Ex. 1 (ii), p. 358 (±8, −4, (−1)^((p−1)/2) p are fundamental)"]
theorem ex1_ii_mem {d : ℤ} (hd : d ∈ primeDiscriminants) : Int.IsFundamentalDiscr d := by
  rcases hd with h | ⟨p, hp, hp2, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · rw [show (8:ℤ) = 4 * 2 by norm_num, Int.isFundamentalDiscr_four_mul]
      exact ⟨Int.prime_two.squarefree, by norm_num⟩
    · rw [show (-8:ℤ) = 4 * (-2) by norm_num, Int.isFundamentalDiscr_four_mul]
      exact ⟨sqf_neg Int.prime_two.squarefree, by norm_num⟩
    · rw [show (-4:ℤ) = 4 * (-1) by norm_num, Int.isFundamentalDiscr_four_mul]
      exact ⟨sqf_neg squarefree_one, by norm_num⟩
  · have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    have hsq : Squarefree (p : ℤ) := (Nat.prime_iff_prime_int.1 hp).squarefree
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    rcases Nat.odd_mod_four_iff.1 hodd with h1 | h3
    · rw [Even.neg_one_pow ⟨(p - 1) / 4, by omega⟩, one_mul]
      exact ⟨by omega, hsq⟩
    · rw [Odd.neg_one_pow ⟨(p - 3) / 4, by omega⟩]
      exact ⟨by omega, by simpa using sqf_neg hsq⟩

theorem ex1_exS : ∀ n : ℕ, ∀ D : ℤ, D.natAbs = n → Int.IsFundamentalDiscr D →
    ∃ S : Finset ℤ, (↑S : Set ℤ) ⊆ primeDiscriminants ∧ ∏ d ∈ S, d = D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hn hf
  have hD0 := hf.ne_zero
  have fin : ∀ s D' : ℤ, s ∈ primeDiscriminants → D = s * D' → Int.IsFundamentalDiscr D' →
      ¬ s ∣ D' → 2 ≤ s.natAbs → ∃ S : Finset ℤ, (↑S : Set ℤ) ⊆ primeDiscriminants ∧ ∏ d ∈ S, d = D := by
    intro s D' hs hD hf' hnd h2
    have hD'0 := hf'.ne_zero
    have hlt : D'.natAbs < n := by
      rw [← hn, hD, Int.natAbs_mul]
      have : 0 < D'.natAbs := by omega
      nlinarith
    obtain ⟨S', hS', hp'⟩ := ih _ hlt D' rfl hf'
    have hns : s ∉ S' := fun hm => hnd (hp' ▸ Finset.dvd_prod_of_mem (fun x => x) hm)
    refine ⟨insert s S', ?_, ?_⟩
    · rw [Finset.coe_insert]; exact Set.insert_subset hs hS'
    · rw [Finset.prod_insert hns, hp', hD]
  by_cases h1 : D = 1
  · exact ⟨∅, by simp, by simp [h1]⟩
  rw [Int.isFundamentalDiscr_iff_squarefree] at hf
  rcases hf with ⟨h4, hsq⟩ | ⟨h4, hsq, hm⟩
  · -- odd case
    have hna : D.natAbs ≠ 1 := by omega
    obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hna
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    have hp2 : p ≠ 2 := by omega
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hmod : ((-1 : ℤ) ^ ((p - 1) / 2) * p) % 4 = 1 := by
      rcases Nat.odd_mod_four_iff.1 hpodd with h1 | h3
      · rw [Even.neg_one_pow ⟨(p - 1) / 4, by omega⟩, one_mul]; omega
      · rw [Odd.neg_one_pow ⟨(p - 3) / 4, by omega⟩]; omega
    set s : ℤ := (-1 : ℤ) ^ ((p - 1) / 2) * p with hs
    have hsmem : s ∈ primeDiscriminants := Or.inr ⟨p, hp, hp2, rfl⟩
    have hsa : s.natAbs = p := by
      rcases qs_cases p with h | h <;> rw [hs, h] <;> simp
    have hsD : s ∣ D := by
      rw [← Int.natAbs_dvd_natAbs, hsa]; exact hpD
    obtain ⟨D', hD'⟩ := hsD
    have hD'4 : D' % 4 = 1 := by
      have := Int.mul_emod s D' 4
      rw [hmod] at this; rw [← hD'] at this; omega
    have hsq' : Squarefree D' := by rw [hD'] at hsq; exact hsq.of_mul_right
    have hf' : Int.IsFundamentalDiscr D' := Int.isFundamentalDiscr_iff_squarefree.2 (Or.inl ⟨hD'4, hsq'⟩)
    refine fin s D' hsmem hD' hf' ?_ (by omega)
    rintro ⟨c, hc⟩
    have := hsq s ⟨c, by rw [hD', hc]; ring⟩
    have := Int.isUnit_iff_natAbs_eq.1 this
    omega
  · have hDm : D = 4 * (D / 4) := by omega
    generalize D / 4 = m at hDm hsq hm
    rcases hm with hm | hm
    · obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
      have hsq' : Squarefree m' := hsq.of_mul_right
      have hm'2 : m' % 2 = 1 := by omega
      rcases (by omega : m' % 4 = 1 ∨ m' % 4 = 3) with h | h
      · refine fin 8 m' (Or.inl (by simp)) (by omega)
          (Int.isFundamentalDiscr_iff_squarefree.2 (Or.inl ⟨h, hsq'⟩)) ?_ (by simp)
        rintro ⟨c, hc⟩
        omega
      · refine fin (-8) (-m') (Or.inl (by simp)) (by omega)
          (Int.isFundamentalDiscr_iff_squarefree.2 (Or.inl ⟨by omega, sqf_neg hsq'⟩)) ?_ (by simp)
        rintro ⟨c, hc⟩
        omega
    · refine fin (-4) (-m) (Or.inl (by simp)) (by omega)
        (Int.isFundamentalDiscr_iff_squarefree.2 (Or.inl ⟨by omega, sqf_neg hsq⟩)) ?_ (by simp)
      rintro ⟨c, hc⟩
      omega


def ex1E0 : Finset ℤ := {8, -8, -4}


lemma ex1_e0_inj : ∀ A ∈ ex1E0.powerset, ∀ B ∈ ex1E0.powerset, ∏ x ∈ A, x = ∏ x ∈ B, x → A = B := by
  unfold ex1E0; decide


def ex1Ostar (D : ℤ) : Finset ℤ :=
  (D.natAbs.primeFactors.erase 2).image (fun p : ℕ => (-1 : ℤ) ^ ((p - 1) / 2) * p)


lemma qs_odd {p : ℕ} (h : p % 2 = 1) : ((-1 : ℤ) ^ ((p - 1) / 2) * p) % 2 = 1 := by
  rcases qs_cases p with h' | h' <;> rw [h'] <;> omega


lemma ex1_claimA {D : ℤ} {S : Finset ℤ} (hS : (↑S : Set ℤ) ⊆ primeDiscriminants) (hp : ∏ d ∈ S, d = D)
    (hD : D ≠ 0) (d : ℤ) : (d ∈ S ∧ d ∉ ex1E0) ↔ d ∈ ex1Ostar D := by
  constructor
  · rintro ⟨hd, hnd⟩
    have hmem := hS hd
    rcases hmem with h | ⟨p, hpp, hp2, rfl⟩
    · exfalso; apply hnd; unfold ex1E0; simpa using h
    · have hdD : ((-1 : ℤ) ^ ((p - 1) / 2) * p) ∣ D := hp ▸ Finset.dvd_prod_of_mem (fun x => x) hd
      have hpD : (p : ℤ) ∣ D := by
        rcases qs_cases p with h | h <;> rw [h] at hdD
        · exact hdD
        · exact (neg_dvd.1 hdD)
      unfold ex1Ostar
      rw [Finset.mem_image]
      exact ⟨p, Finset.mem_erase.2 ⟨hp2, Nat.mem_primeFactors.2 ⟨hpp, Int.natCast_dvd.1 hpD, by omega⟩⟩, rfl⟩
  · intro hd
    unfold ex1Ostar at hd
    rw [Finset.mem_image] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    obtain ⟨hq2, hq'⟩ := Finset.mem_erase.1 hq
    obtain ⟨hqp, hqD, -⟩ := Nat.mem_primeFactors.1 hq'
    have hqodd : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hqp
    have hqd : (q : ℤ) ∣ ∏ d ∈ S, d := by rw [hp]; exact Int.natCast_dvd.2 hqD
    obtain ⟨s, hsS, hqs⟩ := hqz.exists_mem_finset_dvd hqd
    refine ⟨?_, ?_⟩
    · have hsm := hS hsS
      rcases hsm with h | ⟨r, hrp, hr2, rfl⟩
      · exfalso
        have h8 : (q : ℤ) ∣ 8 ∨ (q : ℤ) ∣ -8 ∨ (q : ℤ) ∣ -4 := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
          rcases h with rfl | rfl | rfl <;> tauto
        have h8' : q ∣ 8 ∨ q ∣ 8 ∨ q ∣ 4 := by
          rcases h8 with h | h | h
          · left; exact_mod_cast h
          · right; left; exact_mod_cast (dvd_neg.1 h)
          · right; right; exact_mod_cast (dvd_neg.1 h)
        have hq3 : q ∣ 2 := by
          rcases h8' with h | h | h
          · exact hqp.dvd_of_dvd_pow (n := 3) (by simpa using h)
          · exact hqp.dvd_of_dvd_pow (n := 3) (by simpa using h)
          · exact hqp.dvd_of_dvd_pow (n := 2) (by simpa using h)
        have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 hq3
        exact hq2 this
      · have hqr : (q : ℤ) ∣ (r : ℤ) := by
          rcases qs_cases r with h | h <;> rw [h] at hqs
          · exact hqs
          · exact (dvd_neg.1 hqs)
        have : q = r := (Nat.prime_dvd_prime_iff_eq hqp hrp).1 (by exact_mod_cast hqr)
        subst this
        exact hsS
    · intro hE
      have := qs_odd hqodd
      unfold ex1E0 at hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      omega


theorem ex1_uniqS {D : ℤ} (hD : D ≠ 0) {S₁ S₂ : Finset ℤ} (h₁ : (↑S₁ : Set ℤ) ⊆ primeDiscriminants)
    (p₁ : ∏ d ∈ S₁, d = D) (h₂ : (↑S₂ : Set ℤ) ⊆ primeDiscriminants) (p₂ : ∏ d ∈ S₂, d = D) :
    S₁ = S₂ := by
  have ex1_key : ∀ S : Finset ℤ, (↑S : Set ℤ) ⊆ primeDiscriminants → ∏ d ∈ S, d = D →
      (∏ x ∈ S.filter (· ∈ ex1E0), x) * ∏ x ∈ ex1Ostar D, x = D ∧ S.filter (· ∈ ex1E0) ⊆ ex1E0 := by
    intro S hS hp
    refine ⟨?_, fun x hx => (Finset.mem_filter.1 hx).2⟩
    have : S.filter (fun x => ¬ x ∈ ex1E0) = ex1Ostar D := by
      ext d; rw [Finset.mem_filter]; exact ex1_claimA hS hp hD d
    rw [← this, Finset.prod_filter_mul_prod_filter_not, hp]
  obtain ⟨k1, s1⟩ := ex1_key S₁ h₁ p₁
  obtain ⟨k2, s2⟩ := ex1_key S₂ h₂ p₂
  have hP : ∏ x ∈ ex1Ostar D, x ≠ 0 := by
    intro h; rw [h, mul_zero] at k1; exact hD k1.symm
  have heq : ∏ x ∈ S₁.filter (· ∈ ex1E0), x = ∏ x ∈ S₂.filter (· ∈ ex1E0), x :=
    mul_right_cancel₀ hP (k1.trans k2.symm)
  have hE := ex1_e0_inj _ (Finset.mem_powerset.2 s1) _ (Finset.mem_powerset.2 s2) heq
  ext d
  by_cases hd : d ∈ ex1E0
  · have := congrArg (d ∈ ·) hE
    simpa [hd] using this
  · have a1 := ex1_claimA h₁ p₁ hD d
    have a2 := ex1_claimA h₂ p₂ hD d
    constructor
    · intro h; exact (a2.2 (a1.1 ⟨h, hd⟩)).1
    · intro h; exact (a1.2 (a2.1 ⟨h, hd⟩)).1


/-- **Cassels, Ch. 14, Ex. 1 (ii)** (p. 358), second part: *every fundamental discriminant is uniquely expressible as a
product of distinct members of* `primeDiscriminants` (the empty product giving $D = 1$). -/
@[kb "cassels1978" "Ch. 14, Ex. 1 (ii), p. 358 (unique product of distinct prime discriminants)"]
theorem ex1_ii {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    ∃! S : Finset ℤ, (↑S : Set ℤ) ⊆ primeDiscriminants ∧ ∏ d ∈ S, d = D := by
  obtain ⟨S, h1, h2⟩ := ex1_exS _ D rfl hD
  exact ⟨S, ⟨h1, h2⟩, fun S' ⟨h1', h2'⟩ => ex1_uniqS hD.ne_zero h1' h2' h1 h2⟩

lemma chi8_neg (x : ZMod 8) : ZMod.χ₈ (-x) = ZMod.χ₈ x := by revert x; decide


lemma chi8_natAbs (D : ℤ) : ZMod.χ₈ ((D.natAbs : ℕ) : ZMod 8) = ZMod.χ₈ (D : ZMod 8) := by
  have h := Int.natAbs_eq D
  generalize D.natAbs = n at h ⊢
  rcases h with h | h
  · rw [h]; push_cast; rfl
  · rw [h]; push_cast; rw [chi8_neg]


lemma recip_int {D : ℤ} (hD4 : D % 4 = 1) {m : ℕ} (hm : Odd m) :
    jacobiSym (m : ℤ) D.natAbs = jacobiSym D m := by
  rcases lt_or_gt_of_ne (show D ≠ 0 by omega) with hneg | hpos
  · have h3 : D.natAbs % 4 = 3 := by omega
    have hcast : ((D.natAbs : ℕ) : ℤ) = -D := by omega
    have e : jacobiSym ((D.natAbs : ℕ) : ℤ) m = ZMod.χ₄ m * jacobiSym D m := by
      rw [hcast, show -D = (-1) * D by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hm]
    rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hm) with h1 | h3'
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 (by rw [Nat.odd_iff]; omega), e,
        ZMod.χ₄_nat_one_mod_four h1, one_mul]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h3' h3, e, ZMod.χ₄_nat_three_mod_four h3']
      ring
  · have h1 : D.natAbs % 4 = 1 := by omega
    have hcast : ((D.natAbs : ℕ) : ℤ) = D := by omega
    have := jacobiSym.quadratic_reciprocity_one_mod_four' hm h1
    rw [this, hcast]


/-- **Cassels, Ch. 14, Ex. 2 (ii)** (p. 358): *if $D$ is odd, $(D/b) = (b/|D|)$, the right-hand side being the ordinary
Jacobi symbol $\prod_p (b/p)^{\delta(p)}$ for $D = \pm\prod_p p^{\delta(p)}$.* (The display is lost in the machine-read
text; read from the page image, p. 358.) -/
@[kb "cassels1978" "Ch. 14, Ex. 2 (ii), p. 358 ((D/b) = (b/|D|) for D odd)"]
theorem ex2_ii {D : ℤ} (hD4 : D % 4 = 1) {b : ℕ} (hb : 0 < b) :
    Siegel.kroneckerSym D b = jacobiSym b D.natAbs := by
  have hDodd : ¬ Even D := by rw [Int.not_even_iff_odd, Int.odd_iff]; omega
  have hDa : Odd D.natAbs := by
    rw [Nat.odd_iff]; omega
  have hm : Odd (ordCompl[2] b) :=
    Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hb.ne')
  have hb' : b = 2 ^ b.factorization 2 * ordCompl[2] b := (Nat.ordProj_mul_ordCompl_eq_self b 2).symm
  have h1 : jacobiSym (ordCompl[2] b : ℕ) D.natAbs = jacobiSym D (ordCompl[2] b) :=
    recip_int hD4 hm
  have h2 : jacobiSym 2 D.natAbs = ZMod.χ₈ (D : ZMod 8) := by
    rw [jacobiSym.at_two hDa, chi8_natAbs]
  conv_rhs => rw [hb']
  rw [Siegel.kroneckerSym, if_neg hDodd, Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left,
    Nat.cast_ofNat, h2, h1]

lemma kron_even (d : ℤ) {b : ℕ} (hb : Odd b) :
    Siegel.kroneckerSym (4 * d) b = jacobiSym d b := by
  rw [Siegel.kroneckerSym_of_odd _ hb, jacobiSym.mul_left, jacobiSym.at_four hb, one_mul]


lemma odd_of_coprime {d : ℤ} {b : ℕ} (hc : IsCoprime (b : ℤ) (4 * d)) : Odd b := by
  rw [← Nat.not_even_iff_odd]
  rintro ⟨k, hk⟩
  have : (2:ℤ) ∣ b := ⟨k, by rw [hk]; push_cast; ring⟩
  have h2 : (2:ℤ) ∣ 4 * d := ⟨2 * d, by ring⟩
  have := hc.isUnit_of_dvd' this h2
  have := Int.isUnit_iff.1 this
  omega


/-- **Cassels, Ch. 14, Ex. 2 (iii)** (p. 359): *if $b_1 \equiv b_2 \pmod D$ and $b_1, b_2 > 0$ are prime to $D$, then
$(D/b_1) = (D/b_2)$.* -/
@[kb "cassels1978" "Ch. 14, Ex. 2 (iii), p. 359 (periodicity of (D/b) modulo D)"]
theorem ex2_iii {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) {b₁ b₂ : ℕ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : IsCoprime (b₁ : ℤ) D) (h₂ : IsCoprime (b₂ : ℤ) D) (h : (b₁ : ℤ) ≡ b₂ [ZMOD D]) :
    Siegel.kroneckerSym D b₁ = Siegel.kroneckerSym D b₂ := by
  rcases hD4 with h4 | h4
  · obtain ⟨d, rfl⟩ : (4:ℤ) ∣ D := by omega
    have o1 := odd_of_coprime h₁
    have o2 := odd_of_coprime h₂
    rw [kron_even _ o1, kron_even _ o2, jacobiSym.mod_right _ o1, jacobiSym.mod_right _ o2]
    have hdvd : ((4 * d.natAbs : ℕ) : ℤ) ∣ (b₂ : ℤ) - b₁ := by
      have := Int.natAbs_dvd.2 (Int.modEq_iff_dvd.1 h)
      rw [Int.natAbs_mul] at this
      simpa using this
    have := Int.natCast_modEq_iff.1 (Int.modEq_iff_dvd.2 hdvd)
    have e : b₁ % (4 * d.natAbs) = b₂ % (4 * d.natAbs) := this
    rw [e]
  · rw [ex2_ii h4 hb₁, ex2_ii h4 hb₂]
    apply jacobiSym.mod_left'
    exact Int.modEq_iff_dvd.2 (Int.natAbs_dvd.2 (Int.modEq_iff_dvd.1 h))

lemma jac_one (n : ℕ) (hn : n ≠ 0) {b : ℕ} (hb : Odd b) (h : (4 * n : ℤ) ∣ b + 1) :
    jacobiSym n b = 1 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hdm : (m : ℤ) ∣ b + 1 :=
    dvd_trans ⟨4 * 2 ^ k, by push_cast; ring⟩ h
  have hb4 : b % 4 = 3 := by
    have : (4:ℤ) ∣ b + 1 := dvd_trans ⟨2 ^ k * m, by push_cast; ring⟩ h
    have := Nat.odd_iff.1 hb
    omega
  have hJm : jacobiSym m b = 1 := by
    have hbm : jacobiSym b m = jacobiSym (-1) m := by
      apply jacobiSym.mod_left'
      refine Int.modEq_iff_dvd.2 ?_
      obtain ⟨c, hc⟩ := hdm
      exact ⟨-c, by linarith⟩
    rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hm) with h1 | h3
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hb, hbm, jacobiSym.at_neg_one hm,
        ZMod.χ₄_nat_one_mod_four h1]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h3 hb4, hbm, jacobiSym.at_neg_one hm,
        ZMod.χ₄_nat_three_mod_four h3]; norm_num
  have hJ2 : jacobiSym 2 b ^ k = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h8 : b % 8 = 7 := by
        have : (8:ℤ) ∣ b + 1 := by
          refine dvd_trans ⟨2 ^ (k - 1) * m, ?_⟩ h
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          push_cast; ring_nf
        have := Nat.odd_iff.1 hb
        omega
      rw [jacobiSym.at_two hb, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [h8, Nat.odd_iff.1 hb]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, hJm, hJ2]
  norm_num


/-- **Cassels, Ch. 14, Ex. 2 (iv)** (p. 359): *extend the Kronecker symbol $(D/b)$ to $b < 0$ by periodicity modulo
$D$; then $(D/{-1}) = +1$ if $D > 0$ and $-1$ if $D < 0$.* Stated for the positive representatives $b \equiv -1
\pmod D$, $b$ prime to $D$, at which the periodic extension is evaluated. -/
@[kb "cassels1978" "Ch. 14, Ex. 2 (iv), p. 359 ((D/−1) = sign D)"]
theorem ex2_iv {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) {b : ℕ} (hb : 0 < b)
    (hcop : IsCoprime (b : ℤ) D) (hbD : (b : ℤ) ≡ -1 [ZMOD D]) :
    Siegel.kroneckerSym D b = if 0 < D then 1 else -1 := by
  rcases hD4 with h4 | h4
  · obtain ⟨d, rfl⟩ : (4:ℤ) ∣ D := by omega
    have ob := odd_of_coprime hcop
    rw [kron_even _ ob]
    have hd : 4 * d ∣ (b : ℤ) + 1 := by
      have := Int.modEq_iff_dvd.1 hbD
      exact (dvd_neg.1 (by simpa [sub_eq_add_neg, add_comm] using this))
    have hb4 : b % 4 = 3 := by
      have : (4:ℤ) ∣ b + 1 := dvd_trans ⟨d, rfl⟩ hd
      have := Nat.odd_iff.1 ob
      omega
    have hd0 : d ≠ 0 := by rintro rfl; simp at hD
    rcases lt_or_gt_of_ne hd0 with hneg | hpos
    · have hn : d = -(d.natAbs : ℤ) := by omega
      have hn0 : d.natAbs ≠ 0 := by omega
      have := jac_one d.natAbs hn0 ob (by
        have h' : (4 * (d.natAbs : ℤ)) = -(4 * d) := by omega
        rw [h']; exact (neg_dvd.2 hd))
      rw [hn, show -(d.natAbs : ℤ) = (-1) * d.natAbs by ring, jacobiSym.mul_left,
        jacobiSym.at_neg_one ob, this, ZMod.χ₄_nat_three_mod_four hb4]
      have : ¬ (0 < 4 * -(d.natAbs : ℤ)) := by omega
      simp
    · have hn : d = (d.natAbs : ℤ) := by omega
      have hn0 : d.natAbs ≠ 0 := by omega
      have := jac_one d.natAbs hn0 ob (by
        have h' : (4 * (d.natAbs : ℤ)) = 4 * d := by omega
        rw [h']; exact hd)
      rw [if_pos (by omega)]
      rw [hn, this]
  · have hodd : Odd D.natAbs := by rw [Nat.odd_iff]; omega
    rw [ex2_ii h4 hb]
    have : jacobiSym b D.natAbs = jacobiSym (-1) D.natAbs := by
      apply jacobiSym.mod_left'
      exact Int.modEq_iff_dvd.2 (Int.natAbs_dvd.2 (Int.modEq_iff_dvd.1 hbD.symm)) |>.symm
    rw [this, jacobiSym.at_neg_one hodd]
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · rw [if_neg (by omega), ZMod.χ₄_nat_three_mod_four (by omega)]
    · rw [if_pos hpos, ZMod.χ₄_nat_one_mod_four (by omega)]

end QuadFormsKB.Composition
