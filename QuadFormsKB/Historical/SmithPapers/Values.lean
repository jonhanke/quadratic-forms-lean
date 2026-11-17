/-
# Values of primitive forms prime to a given number; primes $x^2 \pm 3y^2$ (Smith)

**Library** `QuadFormsKB.Historical.SmithPapers` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Smith, *On the orders and genera of quadratic forms containing more than three indeterminates*,
  1867; *Collected Mathematical Papers* II): a primitive integral form in
  $n \ge 1$ variables represents an integer prime to any given $N$ if it is odd (some diagonal coefficient odd), and
  twice an integer prime to $N$ if it is even (`smith_primitive_represents_coprime`).
* (Smith, *On the orders and genera of ternary quadratic forms*, 1867; *Collected Mathematical
  Papers* I, p. 460): the ternary case, and if $\Omega \Delta$ is odd then $f$
  represents numbers $\equiv 1$ and $\equiv 3 \pmod 4$ (`smith_ternary_values`).
* (Smith, *Collected Mathematical Papers* II): a prime
  $p \equiv 1 \pmod{12}$ is represented by both $x^2 + 3y^2$ and $x^2 - 3y^2$; a prime $p \equiv 5 \pmod{12}$ by
  neither (`smith_primes_mod_twelve`).

Conventions. A form in $n$ variables is given by its symmetric integer matrix $A$, $f(x) = x^{T} A x$ (Gauss's and
Smith's convention: the cross coefficients $2 a_{ij}$ are even). It is primitive if the entries of $A$ have greatest
common divisor $1$; it is odd (properly primitive) if some $a_{ii}$ is odd and even (improperly primitive) if every
$a_{ii}$ is even, i.e. if all its values are even. Variables are 0-based.

All **proved**, unconditional.
-/
import QuadFormsKB.Historical.SmithPapers.Ternary
import QuadFormsKB.Historical.BinaryForms.Primes
import Mathlib.Data.ZMod.Basic

namespace QuadFormsKB.Historical.SmithPapers

open Matrix

/-- The form $f(x) = x^{T} A x$ of a square integer matrix. -/
def formVal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ := x ⬝ᵥ (A *ᵥ x)

/-- A matrix is primitive if every common divisor of its entries is a unit ($\pm 1$). -/
def MatPrimitive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ d : ℤ, (∀ i j, d ∣ A i j) → IsUnit d

/-- A vector is primitive if every common divisor of its coordinates is a unit; a representation $f(x) = m$ is proper
if $x$ is primitive. -/
def VecPrimitive {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ d : ℤ, (∀ i, d ∣ x i) → IsUnit d

private theorem formVal_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (x : Fin n → ℤ) :
    formVal A (c • x) = c ^ 2 * formVal A x := by
  simp only [formVal, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private theorem formVal_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    formVal A (x + y) = formVal A x + formVal A y + (x ⬝ᵥ (A *ᵥ y) + y ⬝ᵥ (A *ᵥ x)) := by
  simp only [formVal, mulVec_add, add_dotProduct, dotProduct_add]
  ring

private theorem formVal_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (N : ℤ) (x z : Fin n → ℤ) :
    formVal A (x + N • z) = formVal A x +
      N * (x ⬝ᵥ (A *ᵥ z) + z ⬝ᵥ (A *ᵥ x) + N * formVal A z) := by
  rw [formVal_add, formVal_smul]
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private theorem bil_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) (x z : Fin n → ℤ) :
    z ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]

private theorem single_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (Pi.single i (1 : ℤ) : Fin n → ℤ) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

private theorem formVal_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    formVal A (Pi.single i 1) = A i i := single_dot A i i

private theorem formVal_single_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) (i j : Fin n) :
    formVal A (Pi.single i 1 + Pi.single j 1) = A i i + A j j + 2 * A i j := by
  rw [formVal_add, formVal_single, formVal_single, single_dot, single_dot, hA.apply i j]
  ring

private theorem formVal_even {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (hd : ∀ i, Even (A i i)) (x : Fin n → ℤ) : Even (formVal A x) := by
  have h : ((formVal A x : ℤ) : ZMod 2) = 0 := by
    have e : formVal A x = ∑ p : Fin n × Fin n, x p.1 * (A p.1 p.2 * x p.2) := by
      simp [formVal, dotProduct, mulVec, Finset.mul_sum]
      exact (Fintype.sum_prod_type (fun p : Fin n × Fin n => x p.1 * (A p.1 p.2 * x p.2))).symm
    rw [e]
    push_cast
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 = p.2)]
    have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2),
        ((x p.1 : ℤ) : ZMod 2) * (((A p.1 p.2 : ℤ) : ZMod 2) * (x p.2 : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have : ((A p.1 p.2 : ℤ) : ZMod 2) = 0 := by
        rw [← hp']
        exact ZMod.intCast_eq_zero_iff_even.mpr (hd _)
      rw [this]; simp
    have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 = p.2),
        ((x p.1 : ℤ) : ZMod 2) * (((A p.1 p.2 : ℤ) : ZMod 2) * (x p.2 : ℤ)) = 0 := by
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        have : ((A p.2 p.1 : ℤ) : ZMod 2) = (A p.1 p.2 : ℤ) := by rw [hA.apply p.1 p.2]
        simp only [this]
        have : ((x p.2 : ℤ) : ZMod 2) * (((A p.1 p.2 : ℤ) : ZMod 2) * (x p.1 : ℤ)) =
            ((x p.1 : ℤ) : ZMod 2) * (((A p.1 p.2 : ℤ) : ZMod 2) * (x p.2 : ℤ)) := by ring
        rw [this]
        exact CharTwo.add_self_eq_zero _
      · intro p hp _ h
        have := (Finset.mem_filter.mp hp).2
        apply this
        have h1 := congrArg Prod.fst h
        exact h1.symm
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact fun h => hp h.symm
      · intro p hp; rfl
    rw [h1, h2, add_zero]
  exact ZMod.intCast_eq_zero_iff_even.mp h

private theorem exists_not_dvd_odd_prime {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (hprim : MatPrimitive A) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ x : Fin n → ℤ, ¬ (p : ℤ) ∣ formVal A x := by
  by_cases h : ∃ i, ¬ (p : ℤ) ∣ A i i
  · obtain ⟨i, hi⟩ := h
    exact ⟨Pi.single i 1, by rwa [formVal_single]⟩
  · push Not at h
    by_contra hcon
    push Not at hcon
    have hall : ∀ i j, (p : ℤ) ∣ A i j := by
      intro i j
      by_cases hij : i = j
      · subst hij; exact h i
      · have h1 := hcon (Pi.single i 1 + Pi.single j 1)
        rw [formVal_single_add A hA] at h1
        have h3 : (p : ℤ) ∣ 2 * A i j := by
          have := dvd_sub (dvd_sub h1 (h i)) (h j)
          convert this using 1
          ring
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h3 with h4 | h4
        · exfalso
          have : p ∣ 2 := by exact_mod_cast h4
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        · exact h4
    have hu := hprim p hall
    rw [Int.isUnit_iff] at hu
    rcases hu with hu | hu
    · exact hp.one_lt.ne' (by exact_mod_cast hu)
    · omega

private theorem formVal_two_witness {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (hprim : MatPrimitive A) (hd : ∀ i, Even (A i i)) :
    ∃ x : Fin n → ℤ, ¬ (2 : ℤ) ∣ formVal A x / 2 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ i j, (2 : ℤ) ∣ A i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact even_iff_two_dvd.mp (hd i)
    · obtain ⟨a, ha⟩ := hd i
      obtain ⟨b, hb⟩ := hd j
      have h1 := hcon (Pi.single i 1)
      have h2 := hcon (Pi.single j 1)
      have h3 := hcon (Pi.single i 1 + Pi.single j 1)
      rw [formVal_single] at h1 h2
      rw [formVal_single_add A hA] at h3
      omega
  have hu := hprim 2 hall
  rw [Int.isUnit_iff] at hu
  omega

private theorem crt_combine {n : ℕ} (g : (Fin n → ℤ) → ℤ)
    (hQ1 : ∀ (c : ℤ) (x : Fin n → ℤ), g (c • x) = c ^ 2 * g x)
    (hQ2 : ∀ (N : ℤ) (x z : Fin n → ℤ), N ∣ g (x + N • z) - g x)
    (q : ℕ) (hq : q.Prime) (a b : ℤ) (hab : a + b = 1) (hqb : (q : ℤ) ∣ b)
    (x1 x2 : Fin n → ℤ) (h1 : ¬ (q : ℤ) ∣ g x1) : ¬ (q : ℤ) ∣ g (a • x1 + b • x2) := by
  obtain ⟨c, hc⟩ := hqb
  have hx : a • x1 + b • x2 = a • x1 + (q : ℤ) • (c • x2) := by rw [hc, smul_smul]
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqa : ¬ (q : ℤ) ∣ a := by
    intro h
    have h' : (q : ℤ) ∣ 1 := by rw [← hab]; exact dvd_add h ⟨c, hc⟩
    exact hqp.not_dvd_one h'
  intro hdiv
  rw [hx] at hdiv
  have h2 := hQ2 (q : ℤ) (a • x1) (c • x2)
  have h3 : (q : ℤ) ∣ g (a • x1) := by
    have := dvd_sub hdiv h2
    simpa using this
  rw [hQ1] at h3
  rcases hqp.dvd_or_dvd h3 with h4 | h4
  · exact hqa (hqp.dvd_of_dvd_pow h4)
  · exact h1 h4

private theorem crt_primes {n : ℕ} (g : (Fin n → ℤ) → ℤ)
    (hQ1 : ∀ (c : ℤ) (x : Fin n → ℤ), g (c • x) = c ^ 2 * g x)
    (hQ2 : ∀ (N : ℤ) (x z : Fin n → ℤ), N ∣ g (x + N • z) - g x) (m : ℕ) :
    m ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ m → ∃ x, ¬ (q : ℤ) ∣ g x) →
      ∃ x, ∀ q : ℕ, q.Prime → q ∣ m → ¬ (q : ℤ) ∣ g x := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ _
    exact ⟨0, fun q hq hqd => absurd (Nat.dvd_one.mp hqd) hq.ne_one⟩
  | prime_pow p k hp hk =>
    intro _ h
    obtain ⟨x, hx⟩ := h p hp (dvd_pow_self p hk.ne')
    refine ⟨x, fun q hq hqd => ?_⟩
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd)
    subst this; exact hx
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    obtain ⟨x1, hx1⟩ := iha (by omega) (fun q hq hqd => h q hq (dvd_mul_of_dvd_left hqd b))
    obtain ⟨x2, hx2⟩ := ihb (by omega) (fun q hq hqd => h q hq (dvd_mul_of_dvd_right hqd a))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
    refine ⟨(v * b) • x1 + (u * a) • x2, fun q hq hqd => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).mp hqd with hqa | hqb
    · have := crt_combine g hQ1 hQ2 q hq (v * b) (u * a) (by linarith) (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hqa) u)
        x1 x2 (hx1 q hq hqa)
      exact this
    · have := crt_combine g hQ1 hQ2 q hq (u * a) (v * b) (by linarith) (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hqb) v)
        x2 x1 (hx2 q hq hqb)
      rwa [add_comm] at this

private theorem crt_values {n : ℕ} (g : (Fin n → ℤ) → ℤ)
    (hQ1 : ∀ (c : ℤ) (x : Fin n → ℤ), g (c • x) = c ^ 2 * g x)
    (hQ2 : ∀ (N : ℤ) (x z : Fin n → ℤ), N ∣ g (x + N • z) - g x)
    (N : ℤ) (hN : N ≠ 0) (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ N → ∃ x, ¬ (p : ℤ) ∣ g x) :
    ∃ x, IsCoprime (g x) N := by
  obtain ⟨x, hx⟩ := crt_primes g hQ1 hQ2 N.natAbs (Int.natAbs_ne_zero.mpr hN)
    (fun q hq hqd => h q hq (Int.natCast_dvd.mpr hqd))
  refine ⟨x, Int.isCoprime_iff_gcd_eq_one.mpr ?_⟩
  have : Nat.Coprime (g x).natAbs N.natAbs :=
    Nat.coprime_of_dvd (fun k hk hk1 hk2 => hx k hk hk2 (Int.natCast_dvd.mpr hk1))
  exact this

/-- **A primitive form represents numbers prime to $N$** (Smith 1867, *Collected
Mathematical Papers* II). Let $A$ be a symmetric primitive integer $n \times n$ matrix and $N \neq 0$.
(i) If some $a_{ii}$ is odd, there is $x \in \mathbb Z^n$ with $f(x)$ prime to $N$.
(ii) If every $a_{ii}$ is even, there is $x$ with $f(x) = 2m$ and $m$ prime to $N$. -/
@[kb "smith1894b" "[unverified locator]"]
theorem smith_primitive_represents_coprime {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (hprim : MatPrimitive A) (N : ℤ) (hN : N ≠ 0) :
    ((∃ i, Odd (A i i)) → ∃ x : Fin n → ℤ, IsCoprime (formVal A x) N) ∧
      ((∀ i, Even (A i i)) → ∃ (x : Fin n → ℤ) (m : ℤ), formVal A x = 2 * m ∧ IsCoprime m N) := by
  have hQ1 : ∀ (c : ℤ) (x : Fin n → ℤ), formVal A (c • x) = c ^ 2 * formVal A x :=
    formVal_smul A
  have hQ2 : ∀ (N : ℤ) (x z : Fin n → ℤ), N ∣ formVal A (x + N • z) - formVal A x := by
    intro N x z
    refine ⟨x ⬝ᵥ (A *ᵥ z) + z ⬝ᵥ (A *ᵥ x) + N * formVal A z, ?_⟩
    rw [formVal_add_smul]; ring
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    apply crt_values (formVal A) hQ1 hQ2 N hN
    intro p hp _
    by_cases h2 : p = 2
    · subst h2
      refine ⟨Pi.single i 1, ?_⟩
      rw [formVal_single]
      intro h
      have : Even (A i i) := even_iff_two_dvd.mpr (by exact_mod_cast h)
      exact (Int.not_even_iff_odd.mpr hi) this
    · exact exists_not_dvd_odd_prime A hA hprim p hp h2
  · intro hd
    have hE := formVal_even A hA hd
    have hh : ∀ x, 2 * (formVal A x / 2) = formVal A x :=
      fun x => Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hE x))
    have hQ1' : ∀ (c : ℤ) (x : Fin n → ℤ),
        formVal A (c • x) / 2 = c ^ 2 * (formVal A x / 2) := by
      intro c x
      apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
      have h1 := hh (c • x)
      have h2 := hh x
      have h3 := hQ1 c x
      linear_combination h1 + h3 - c ^ 2 * h2
    have hQ2' : ∀ (N : ℤ) (x z : Fin n → ℤ),
        N ∣ formVal A (x + N • z) / 2 - formVal A x / 2 := by
      intro N x z
      refine ⟨x ⬝ᵥ (A *ᵥ z) + N * (formVal A z / 2), ?_⟩
      apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
      have h1 := hh (x + N • z)
      have h2 := hh x
      have h4 := hh z
      have h5 := formVal_add_smul A N x z
      have hs := bil_symm A hA x z
      linear_combination h1 - h2 + h5 + N * hs - N ^ 2 * h4
    obtain ⟨x, hx⟩ := crt_values (fun x => formVal A x / 2) hQ1' hQ2' N hN (by
      intro p hp _
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨x, hx⟩ := formVal_two_witness A hA hprim hd
        exact ⟨x, by exact_mod_cast hx⟩
      · obtain ⟨x, hx⟩ := exists_not_dvd_odd_prime A hA hprim p hp h2
        exact ⟨x, fun h => hx (dvd_trans h (Dvd.intro_left 2 (hh x)))⟩)
    exact ⟨x, formVal A x / 2, (hh x).symm, hx⟩


private theorem vecPrim_of_one {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (hj : x j = 1) : VecPrimitive x :=
  fun _ h => isUnit_of_dvd_one (by simpa [hj] using h j)

private theorem tern_expand (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (x : Fin 3 → ℤ) :
    tern A x = A 0 0 * x 0 ^ 2 + A 1 1 * x 1 ^ 2 + A 2 2 * x 2 ^ 2 + 2 * A 0 1 * x 0 * x 1 +
      2 * A 0 2 * x 0 * x 2 + 2 * A 1 2 * x 1 * x 2 := by
  have h01 : A 1 0 = A 0 1 := hA.apply 0 1
  have h02 : A 2 0 = A 0 2 := hA.apply 0 2
  have h12 : A 2 1 = A 1 2 := hA.apply 1 2
  simp [tern, dotProduct, mulVec, Fin.sum_univ_three, h01, h02, h12]
  ring

set_option maxRecDepth 100000 in
private theorem key_mod4 : ∀ a b c d e f : ZMod 4,
    (a*b*c + 2*d*e*f - a*d^2 - b*e^2 - c*f^2 = 1 ∨ a*b*c + 2*d*e*f - a*d^2 - b*e^2 - c*f^2 = 3) →
    ((a = 1 ∨ b = 1 ∨ c = 1 ∨ a+b+2*f = 1 ∨ a+c+2*e = 1 ∨ b+c+2*d = 1 ∨ a+b+c+2*(d+e+f) = 1) ∧
     (a = 3 ∨ b = 3 ∨ c = 3 ∨ a+b+2*f = 3 ∨ a+c+2*e = 3 ∨ b+c+2*d = 3 ∨ a+b+c+2*(d+e+f) = 3)) := by
  decide

private theorem witness_of_key (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (r : ℤ)
    (h : ((A 0 0 : ℤ) : ZMod 4) = r ∨ ((A 1 1 : ℤ) : ZMod 4) = r ∨ ((A 2 2 : ℤ) : ZMod 4) = r ∨
      ((A 0 0 : ℤ) : ZMod 4) + (A 1 1 : ℤ) + 2 * (A 0 1 : ℤ) = r ∨
      ((A 0 0 : ℤ) : ZMod 4) + (A 2 2 : ℤ) + 2 * (A 0 2 : ℤ) = r ∨
      ((A 1 1 : ℤ) : ZMod 4) + (A 2 2 : ℤ) + 2 * (A 1 2 : ℤ) = r ∨
      ((A 0 0 : ℤ) : ZMod 4) + (A 1 1 : ℤ) + (A 2 2 : ℤ) + 2 * ((A 1 2 : ℤ) + (A 0 2 : ℤ) + (A 0 1 : ℤ)) = r) :
    ∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = r % 4 := by
  have fin : ∀ x : Fin 3 → ℤ, VecPrimitive x →
      (((tern A x : ℤ) : ZMod 4) = r) → ∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = r % 4 := by
    intro x hx hv
    exact ⟨x, hx, (ZMod.intCast_eq_intCast_iff' _ _ 4).mp hv⟩
  rcases h with h | h | h | h | h | h | h
  · refine fin ![1, 0, 0] (vecPrim_of_one _ 0 rfl) ?_
    rw [tern_expand A hA]; simpa using h
  · refine fin ![0, 1, 0] (vecPrim_of_one _ 1 rfl) ?_
    rw [tern_expand A hA]; simpa using h
  · refine fin ![0, 0, 1] (vecPrim_of_one _ 2 rfl) ?_
    rw [tern_expand A hA]; simpa using h
  · refine fin ![1, 1, 0] (vecPrim_of_one _ 0 rfl) ?_
    rw [tern_expand A hA]; simp; rw [← h]
  · refine fin ![1, 0, 1] (vecPrim_of_one _ 0 rfl) ?_
    rw [tern_expand A hA]; simp; rw [← h]
  · refine fin ![0, 1, 1] (vecPrim_of_one _ 1 rfl) ?_
    rw [tern_expand A hA]; simp; rw [← h]
  · refine fin ![1, 1, 1] (vecPrim_of_one _ 0 rfl) ?_
    rw [tern_expand A hA]; simp; rw [← h]; ring

/-- **An odd determinant gives proper values $\equiv 1$ and $\equiv 3 \pmod 4$**: a ternary form whose (symmetric)
matrix has odd determinant properly represents a number $\equiv 1$ and a number $\equiv 3 \pmod 4$. This is the
congruence lemma behind Smith's statement (ii) below and Dickson's . -/
theorem proper_values_one_three_mod_four (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (hdet : Odd A.det) :
    (∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = 1) ∧
      (∃ x : Fin 3 → ℤ, VecPrimitive x ∧ tern A x % 4 = 3) := by
  have h01 : A 1 0 = A 0 1 := hA.apply 0 1
  have h02 : A 2 0 = A 0 2 := hA.apply 0 2
  have h12 : A 2 1 = A 1 2 := hA.apply 1 2
  have hd : ((A.det : ℤ) : ZMod 4) = 1 ∨ ((A.det : ℤ) : ZMod 4) = 3 := by
    obtain ⟨k, hk⟩ := hdet
    have : A.det % 4 = 1 ∨ A.det % 4 = 3 := by omega
    rcases this with h | h
    · left
      exact (ZMod.intCast_eq_intCast_iff' _ 1 4).mpr (by simpa using h)
    · right
      exact (ZMod.intCast_eq_intCast_iff' _ 3 4).mpr (by simpa using h)
  have hc : ((A.det : ℤ) : ZMod 4) = ((A 0 0 : ℤ) : ZMod 4) * (A 1 1 : ℤ) * (A 2 2 : ℤ) +
      2 * (A 1 2 : ℤ) * (A 0 2 : ℤ) * (A 0 1 : ℤ) - (A 0 0 : ℤ) * (A 1 2 : ℤ) ^ 2 -
      (A 1 1 : ℤ) * (A 0 2 : ℤ) ^ 2 - (A 2 2 : ℤ) * (A 0 1 : ℤ) ^ 2 := by
    rw [det_fin_three, h01, h02, h12]
    push_cast
    ring
  rw [hc] at hd
  have k := key_mod4 _ _ _ _ _ _ hd
  have e1 : ((1 : ℤ) : ZMod 4) = 1 := by simp
  have e3 : ((3 : ℤ) : ZMod 4) = 3 := by simp
  refine ⟨?_, ?_⟩
  · have := witness_of_key A hA 1 (by simpa using k.1)
    simpa using this
  · have := witness_of_key A hA 3 (by simpa using k.2)
    simpa using this

/-- **Values of a primitive ternary form** (Smith 1867, *Collected Mathematical
Papers* I, p. 460). Let $M$ be a symmetric primitive integer $3 \times 3$ matrix with $\det M \neq 0$, and $N \neq 0$.
(i) If $f$ is properly primitive (some $a_{ii}$ odd), some value $f(x)$ is prime to $N$; if $f$ is improperly
primitive (all $a_{ii}$ even), some value is $2m$ with $m$ prime to $N$ (taking $N$ even, $f/2$ represents odd numbers).
(ii) If $\Omega \Delta$ is odd, $f$ represents a number $\equiv 1$ and a number $\equiv 3 \pmod 4$. -/
@[kb "smith1894a" "p. 460"]
theorem smith_ternary_values (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : M.IsSymm) (hprim : IsPrimitive M)
    (hD : M.det ≠ 0) (N : ℤ) (hN : N ≠ 0) :
    ((∃ i, Odd (M i i)) → ∃ x : Fin 3 → ℤ, IsCoprime (tern M x) N) ∧
      ((∀ i, Even (M i i)) → ∃ (x : Fin 3 → ℤ) (m : ℤ), tern M x = 2 * m ∧ IsCoprime m N) ∧
      (Odd (omega M * delta M) → (∃ x : Fin 3 → ℤ, tern M x % 4 = 1) ∧ (∃ x : Fin 3 → ℤ, tern M x % 4 = 3)) := by
  have hmp : MatPrimitive M := by
    intro d hd
    have h : d ∣ content M :=
      Finset.dvd_gcd (fun p _ => hd p.1 p.2)
    have h1 : content M = 1 := hprim
    rw [h1] at h
    exact isUnit_of_dvd_one h
  obtain ⟨h1, h2⟩ := smith_primitive_represents_coprime M hM hmp N hN
  refine ⟨h1, h2, ?_⟩
  intro hodd
  obtain ⟨-, -, -, -, hDe, -⟩ := smith_invariants M hM hprim hD
  have hodd' : Odd M.det := by
    rw [hDe]
    obtain ⟨ho, hd⟩ := Int.odd_mul.mp hodd
    exact (ho.pow).mul hd
  obtain ⟨⟨x, -, hx⟩, ⟨y, -, hy⟩⟩ := proper_values_one_three_mod_four M hM hodd'
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

/-- Thue's lemma modulo a prime: for every $a$ modulo $p$ there are integers $x, y$, not both zero, with
$x \equiv a y \pmod p$ and $|x|, |y| \le \lfloor\sqrt p\rfloor$ (pigeonhole on $(u, v) \mapsto u - a v$). -/
private theorem thue_aux {p : ℕ} (hp : p.Prime) (a : ZMod p) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ Nat.sqrt p ∧ y.natAbs ≤ Nat.sqrt p ∧
      ((x : ℤ) : ZMod p) = a * (y : ℤ) := by
  have := Fact.mk hp
  set k := Nat.sqrt p with hk
  let f : Fin (k + 1) × Fin (k + 1) → ZMod p :=
    fun uv => (uv.1.val : ZMod p) - a * (uv.2.val : ZMod p)
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

/-- If $x^2 = 3 y^2$ in $\mathbb Z$ then $x = 0$ (infinite descent). -/
private theorem three_sq_descent : ∀ n : ℕ, ∀ x y : ℤ, x.natAbs = n → x ^ 2 = 3 * y ^ 2 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h
    by_contra hx
    have h3 : (3 : ℤ) ∣ x ^ 2 := ⟨y ^ 2, h⟩
    obtain ⟨x', rfl⟩ := Int.prime_three.dvd_of_dvd_pow h3
    have hx' : x' ≠ 0 := fun h0 => hx (by simp [h0])
    have h' : y ^ 2 = 3 * x' ^ 2 := by nlinarith
    have hxpos : 0 < x' ^ 2 := by positivity
    have hlt : y ^ 2 < (3 * x') ^ 2 := by nlinarith
    have hlt' := sq_lt_sq.mp hlt
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hlt'
    have hy : y = 0 := ih y.natAbs (by omega) y x' rfl h'
    subst hy
    have : x' = 0 := by nlinarith
    exact hx' this

/-- **Primes $\equiv 1, 5 \pmod{12}$ and the forms $x^2 \pm 3y^2$** (Smith,
*Collected Mathematical Papers* II). A prime $p \equiv 1 \pmod{12}$ is $x^2 + 3y^2$ and is $x^2 - 3y^2$ for some
integers $x$, $y$; a prime $p \equiv 5 \pmod{12}$ is neither. -/
@[kb "smith1894b" "[unverified locator]"]
theorem smith_primes_mod_twelve (p : ℕ) (hp : p.Prime) :
    (p % 12 = 1 → (∃ x y : ℤ, x ^ 2 + 3 * y ^ 2 = p) ∧ (∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = p)) ∧
      (p % 12 = 5 → (¬ ∃ x y : ℤ, x ^ 2 + 3 * y ^ 2 = p) ∧ (¬ ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = p)) := by
  have hsq3 : ∀ x : ℤ, x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
    intro x
    rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h <;>
      simp [pow_two, Int.mul_emod, h]
  refine ⟨fun h12 => ⟨(QuadFormsKB.Historical.BinaryForms.prime_x2_add_3y2_iff p hp).mpr
      (Or.inr (by omega)), ?_⟩, fun h12 => ⟨?_, ?_⟩⟩
  · have := Fact.mk hp
    have h3 : IsSquare ((3 : ℕ) : ZMod p) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by omega) (by norm_num)]
      have : (p : ZMod 3) = 1 := by
        rw [← ZMod.natCast_mod, show p % 3 = 1 by omega]
        simp
      rw [this]
      exact ⟨1, by simp⟩
    obtain ⟨a, ha⟩ := h3
    have h3' : (3 : ZMod p) = a * a := by simpa using ha
    obtain ⟨x, y, hxy, hx, hy, hcong⟩ := thue_aux hp a
    set k := Nat.sqrt p with hk
    have hkk : k * k ≤ p := Nat.sqrt_le p
    have hkne : k * k ≠ p := by
      intro h
      have hd : k ∣ p := ⟨k, h.symm⟩
      rcases (Nat.dvd_prime hp).1 hd with h1 | h1
      · rw [h1] at h; simp at h; exact hp.one_lt.ne' h.symm
      · rw [h1] at h; nlinarith [hp.two_le]
    have hklt : k * k < p := lt_of_le_of_ne hkk hkne
    have hdvd : (p : ℤ) ∣ x ^ 2 - 3 * y ^ 2 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcong, h3']
      ring
    have hx2 : x ^ 2 ≤ (k : ℤ) * k := by
      have : x ^ 2 = ((x.natAbs : ℕ) : ℤ) ^ 2 := by simp [sq_abs]
      rw [this]; exact_mod_cast (by rw [sq]; exact Nat.mul_le_mul hx hx : x.natAbs ^ 2 ≤ k * k)
    have hy2 : y ^ 2 ≤ (k : ℤ) * k := by
      have : y ^ 2 = ((y.natAbs : ℕ) : ℤ) ^ 2 := by simp [sq_abs]
      rw [this]; exact_mod_cast (by rw [sq]; exact Nat.mul_le_mul hy hy : y.natAbs ^ 2 ≤ k * k)
    have hklt' : (k : ℤ) * k < p := by exact_mod_cast hklt
    obtain ⟨c, hc⟩ := hdvd
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hc1 : -3 < c := by
      by_contra hh; push Not at hh
      nlinarith [sq_nonneg x]
    have hc2 : c < 1 := by
      by_contra hh; push Not at hh
      nlinarith [sq_nonneg y]
    have hcases : c = 0 ∨ c = -1 ∨ c = -2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exfalso
      have hx0 : x = 0 := three_sq_descent _ x y rfl (by linarith)
      subst hx0
      have : y = 0 := by nlinarith
      rcases hxy with h | h <;> simp_all
    · exfalso
      have h1 := hsq3 x
      have h2 : x ^ 2 - 3 * y ^ 2 = -(p : ℤ) := by linarith
      have h3 : (p : ℤ) % 3 = 1 := by omega
      omega
    · have hE : Even (x ^ 2 - 3 * y ^ 2) := ⟨-p, by linarith⟩
      have hxy2 : Even (x - y) := by
        rw [Int.even_sub]
        have h3 : ¬ Even (3 : ℤ) := by decide
        simpa [Int.even_sub, Int.even_pow, Int.even_mul, parity_simps, h3] using hE
      obtain ⟨v, hv⟩ := hxy2
      refine ⟨y - v, v, ?_⟩
      have hx' : x = y + 2 * v := by linarith
      subst hx'
      nlinarith
  · rintro ⟨x, y, h⟩
    have := (QuadFormsKB.Historical.BinaryForms.prime_x2_add_3y2_iff p hp).mp ⟨x, y, h⟩
    omega
  · rintro ⟨x, y, h⟩
    have h1 := hsq3 x
    omega

end QuadFormsKB.Historical.SmithPapers
