/-
# Vanishing of Hilbert cusp forms from $T(\pi^2)$ relations at principal primes, any class number

`HeckeVanishing.lean` proves that a cusp form of weight $k \ge 2$ whose coefficients satisfy the $T(\pi^2)$ relations at all prime elements $\pi$
vanishes, for $\mathcal O_F$ a PID: rational primes $p = \pi_1\cdots\pi_g$ are products of prime elements, and Chebyshev's count of primes in
$(Y/4, Y]$ beats the mean-square bound. For class number $> 1$ only the **principal** primes $\mathfrak p = (\pi)$ have $T(\pi^2)$ relations among
the coefficients $a_\nu$, $\nu \in \mathfrak d^{-1}$, of a single form; at a non-principal $\mathfrak p$ the relation involves the lattices
$\mathfrak p^{-1}M$ of another genus (other components of a Hilbert modular form over the class group).

**Main results.**
* **`PrincipalPrimeSupply F`** (named input): infinitely many rational primes $p$ all of whose prime ideals are principal (Hilbert class field +
  Chebotarev); a theorem for $\mathcal O_F$ a PID (`principalPrimeSupply_of_pid`).
* `prime_of_irreducible_dvd`, `norm_coeff_sq_mul_ge'`, `exists_growth_of_rel'`: the chaining over $\pi \mid p$ for such $p$.
* `coeff_eq_zero_of_growth_strict`, `eq_zero_of_growth_strict`: with a strict gap $dk + 1 \le e$ a single large good prime suffices (no prime
  counting).
* **`eq_zero_of_heckeRel'`**: a cusp form of weight $k \ge 3$ with the $T(\pi^2)$ relations at the principal primes vanishes, given
  `PrincipalPrimeSupply F`, for every totally real $F$. ($e = d(2k-2) \ge dk + d$ for $k \ge 3$; $n = 4$ needs prime counting among the good
  primes, i.e. a density form of the input, and is not covered.)

Sources: Hecke's mean-square bound (Garrett 1990, Ch. 1 [unverified]); Neukirch, *Algebraic Number Theory*, VI.7.3, VII.13.4 [unverified].
-/
import QuadFormsKB.HilbertModular.HeckeVanishing

open Filter Topology NumberField
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

/-- **Principal prime supply** (named input for class number $> 1$): for every $N$ there is a rational prime $p > N$ all of whose prime
ideals in $\mathcal O_F$ are principal. True for every number field: a rational prime that splits completely in the Galois closure of the
Hilbert class field $H$ of $F$ has all its prime factors in $F$ split completely in $H/F$, hence principal (Artin reciprocity), and such $p$
have positive density (Chebotarev). Neukirch, *Algebraic Number Theory*, VI.7.3 (Hilbert class field: $\mathfrak p$ splits completely iff
principal) and VII.13.4 (Chebotarev) [unverified]. Not in Mathlib (class field theory). For $\mathcal O_F$ a PID it is a theorem
(`principalPrimeSupply_of_pid`). It is a statement about $\mathcal O_F$ only, not about modular forms or quadratic forms. -/
@[kb "neukirch1999" "VI.7.3 + VII.13.4: infinitely many p with all prime factors principal (input) [unverified]"]
structure PrincipalPrimeSupply (F : Type*) [Field F] [NumberField F] : Prop where
  exists_prime : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
    ∀ P : Ideal (𝓞 F), P.IsPrime → ((p : 𝓞 F) ∈ P) → Submodule.IsPrincipal P

/-- **For $\mathcal O_F$ a PID the principal prime supply holds** (every ideal is principal; infinitely many rational primes). -/
theorem principalPrimeSupply_of_pid (F : Type*) [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] :
    PrincipalPrimeSupply F :=
  ⟨fun N => by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (N + 1)
    exact ⟨p, by omega, hp2, fun P _ _ => IsPrincipalIdealRing.principal P⟩⟩

variable {F : Type} [Field F] [NumberField F]

/-- If every prime ideal containing $p$ is principal, every irreducible divisor of $p$ is a prime element. -/
lemma prime_of_irreducible_dvd {p : ℕ}
    (hp : ∀ P : Ideal (𝓞 F), P.IsPrime → ((p : 𝓞 F) ∈ P) → Submodule.IsPrincipal P) {t : 𝓞 F}
    (ht : Irreducible t) (htp : t ∣ (p : 𝓞 F)) : Prime t := by
  obtain ⟨P, hPmax, hP⟩ := Ideal.exists_le_maximal (Ideal.span {t})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact ht.not_isUnit)
  have htP : t ∈ P := hP (Ideal.subset_span rfl)
  obtain ⟨ϖ, hϖ⟩ := (hp P hPmax.isPrime (Ideal.mem_of_dvd _ htp htP)).principal
  have hPeq : P = Ideal.span {ϖ} := by rw [hϖ]
  have hϖprime : Prime ϖ := by
    have hP0 : P ≠ ⊥ := by
      intro h; rw [h, Ideal.mem_bot] at htP; exact ht.ne_zero htP
    rw [hPeq] at hPmax hP0
    exact (Ideal.span_singleton_prime (by rintro rfl; exact hP0 (by simp))).mp hPmax.isPrime
  rw [hPeq, Ideal.mem_span_singleton] at htP
  obtain ⟨s, rfl⟩ := htP
  rcases ht.isUnit_or_isUnit rfl with h | h
  · exact absurd h hϖprime.not_unit
  · exact (associated_mul_unit_right ϖ s h).prime hϖprime

section Chaining

variable {a : F → ℂ} {lam : 𝓞 F → ℂ} {m₀ w : ℕ} {c₀ : ℝ}
  {D : F → Prop} (hD : ∀ (t : 𝓞 F) (ν : F), D ν → D ((t : F) * ν))

include hD in
/-- **Chaining the $T(\mathfrak p^2)$ relations over the primes above $p$** (every prime of $\mathcal O_F$ above $p$ principal; any class number). Suppose that for every prime
$\pi$ of $\mathcal O_F$ with $\pi \nmid m_0$ and every $\nu$ that is a unit at $\pi$ (`IsUnitAt`),
$a(\pi^2\nu) = \lambda(\pi)\,a(\nu)$ with $|\lambda(\pi)| \ge c_0N(\pi)^w$, $0 < c_0 \le 1$. Then for a rational prime $p \nmid m_0\,\mathrm{disc}(F)$
and $\nu$ a unit at every $\pi \mid p$:
$$c_0^d\,p^{dw}\,|a(\nu)| \le |a(p^2\nu)|,\qquad d = [F : \mathbb Q].$$
*Proof.* $p = \pi_1\cdots\pi_g$ is squarefree (`not_sq_dvd_of_not_dvd_discr`); induct on the norm of a divisor $t \mid p$, peeling
off one prime factor $\pi$ of $t = \pi s$ at a time ($s^2\nu$ is a unit at $\pi$ since $\pi \nmid s$), and use
$N(\pi) \ge p$, $N(p) = p^d$. -/
@[kb "shimura1978" "T(𝔭²) at the primes above p, all principal (any class number) [unverified]"]
theorem norm_coeff_sq_mul_ge' (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1)
    (hrel : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → ∀ ν : F, D ν → IsUnitAt ϖ ν →
      a ((ϖ : F) ^ 2 * ν) = lam ϖ * a ν)
    (hlam : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → c₀ * (nm ϖ : ℝ) ^ w ≤ ‖lam ϖ‖)
    {p : ℕ} (hp : p.Prime)
    (hpp : ∀ P : Ideal (𝓞 F), P.IsPrime → ((p : 𝓞 F) ∈ P) → Submodule.IsPrincipal P)
    (hd : ¬ (p : ℤ) ∣ discr F) (hpm : ¬ p ∣ m₀) {ν : F} (hDν : D ν)
    (hν : ∀ ϖ : 𝓞 F, Prime ϖ → ϖ ∣ (p : 𝓞 F) → IsUnitAt ϖ ν) :
    c₀ ^ Module.finrank ℤ (𝓞 F) * (p : ℝ) ^ (Module.finrank ℤ (𝓞 F) * w) * ‖a ν‖ ≤
      ‖a ((p : F) ^ 2 * ν)‖ := by
  classical
  have hgood : ∀ ϖ : 𝓞 F, Prime ϖ → ϖ ∣ (p : 𝓞 F) → ¬ ϖ ∣ (m₀ : 𝓞 F) :=
    fun ϖ hϖ hϖp h => hpm (dvd_of_prime_dvd hϖ hp hϖp h)
  have hp0 : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- the claim, by strong induction on the norm
  have claim : ∀ N : ℕ, ∀ t : 𝓞 F, nm t = N → t ∣ (p : 𝓞 F) → ¬ IsUnit t →
      ∃ j : ℕ, (p : ℝ) ^ j ≤ nm t ∧ c₀ ^ j * (nm t : ℝ) ^ w * ‖a ν‖ ≤ ‖a ((t : F) ^ 2 * ν)‖ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro t hN ht htu
      have ht0 : t ≠ 0 := by rintro rfl; exact hp0 (zero_dvd_iff.mp ht)
      obtain ⟨ϖ, hϖi, hϖt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht0
      have hϖ : Prime ϖ := prime_of_irreducible_dvd hpp hϖi (hϖt.trans ht)
      obtain ⟨s, rfl⟩ := hϖt
      have hϖp : ϖ ∣ (p : 𝓞 F) := (dvd_mul_right ϖ s).trans ht
      have hϖν := hν ϖ hϖ hϖp
      by_cases hs : IsUnit s
      · -- `t = ϖ s` is itself prime
        have htp : Prime (ϖ * s) := (associated_mul_unit_right ϖ s hs).prime hϖ
        refine ⟨1, by rw [pow_one]; exact_mod_cast le_nm htp hp ht, ?_⟩
        rw [hrel _ htp (hgood _ htp ht) ν hDν (hν _ htp ht), norm_mul, pow_one]
        exact mul_le_mul_of_nonneg_right (hlam _ htp (hgood _ htp ht)) (norm_nonneg _)
      · have hsp : s ∣ (p : 𝓞 F) := (dvd_mul_left s ϖ).trans ht
        have hϖ1 : 1 < nm ϖ := by
          have h1 : nm ϖ ≠ 1 := fun h => hϖ.not_isUnit ((nm_eq_one_iff ϖ).mp h)
          have h0 : nm ϖ ≠ 0 := by
            rw [nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hϖ.ne_zero
          omega
        have hs0 : nm s ≠ 0 := by
          rw [nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
          rintro rfl; exact ht0 (mul_zero ϖ)
        have hlt : nm s < N := by
          rw [← hN, nm_mul]
          exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hs0) hϖ1
        obtain ⟨j, hj1, hj2⟩ := ih _ hlt s rfl hsp hs
        have hϖs : ¬ ϖ ∣ s := by
          rintro ⟨r, rfl⟩
          exact not_sq_dvd_of_not_dvd_discr hp hd hϖ ((by ring_nf; exact ⟨r, by ring⟩ :
            ϖ ^ 2 ∣ ϖ * (ϖ * r)).trans ht)
        refine ⟨j + 1, ?_, ?_⟩
        · rw [nm_mul, pow_succ, Nat.cast_mul, mul_comm (nm ϖ : ℝ)]
          exact mul_le_mul hj1 (by exact_mod_cast le_nm hϖ hp hϖp) (by positivity) (by positivity)
        · have e : ((ϖ * s : 𝓞 F) : F) ^ 2 * ν = (ϖ : F) ^ 2 * ((s : F) ^ 2 * ν) := by
            push_cast; ring
          rw [e, hrel ϖ hϖ (hgood ϖ hϖ hϖp) _ (by have := hD (s ^ 2) ν hDν; push_cast at this; exact this) (hϖν.sq_mul hϖ hϖs),
            norm_mul, nm_mul, Nat.cast_mul,
            mul_pow, pow_succ]
          have h1 := hlam ϖ hϖ (hgood ϖ hϖ hϖp)
          calc c₀ ^ j * c₀ * ((nm ϖ : ℝ) ^ w * (nm s : ℝ) ^ w) * ‖a ν‖ =
                (c₀ * (nm ϖ : ℝ) ^ w) * (c₀ ^ j * (nm s : ℝ) ^ w * ‖a ν‖) := by ring
            _ ≤ ‖lam ϖ‖ * ‖a ((s : F) ^ 2 * ν)‖ :=
                mul_le_mul h1 hj2 (by positivity) (norm_nonneg _)
  have hpu : ¬ IsUnit (p : 𝓞 F) := by
    rw [← nm_eq_one_iff, nm_natCast]
    have : 1 < p ^ Module.finrank ℤ (𝓞 F) :=
      Nat.one_lt_pow (Module.finrank_pos (R := ℤ) (M := 𝓞 F)).ne' hp.one_lt
    omega
  obtain ⟨j, hj1, hj2⟩ := claim _ (p : 𝓞 F) rfl dvd_rfl hpu
  rw [nm_natCast] at hj1 hj2
  push_cast at hj1 hj2
  have hjd : j ≤ Module.finrank ℤ (𝓞 F) :=
    (pow_le_pow_iff_right₀ (by exact_mod_cast hp.one_lt)).mp hj1
  have hcj : c₀ ^ Module.finrank ℤ (𝓞 F) ≤ c₀ ^ j := pow_le_pow_of_le_one hc₀.le hc₁ hjd
  calc c₀ ^ Module.finrank ℤ (𝓞 F) * (p : ℝ) ^ (Module.finrank ℤ (𝓞 F) * w) * ‖a ν‖ ≤
        c₀ ^ j * ((p : ℝ) ^ Module.finrank ℤ (𝓞 F)) ^ w * ‖a ν‖ := by
        rw [← pow_mul]; gcongr
    _ ≤ _ := by simpa using hj2

include hD in
/-- **The growth hypothesis from the $T(\mathfrak p^2)$ relations at principal primes** (any class number): under the hypotheses of
`norm_coeff_sq_mul_ge` (with $m_0 \ge 1$) and $a(0) = 0$, every $\nu \in F$ has $P$ such that
$c_0^d\,p^{dw}\,|a(\nu)| \le |a(p^2\nu)|$ for all primes $p > P$ whose prime ideals are all principal. ($P$ exceeds $m_0$, $|\mathrm{disc}(F)|$ and the norms of a
numerator and denominator of $\nu$.) -/
theorem exists_growth_of_rel' (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1) (hm₀ : 0 < m₀)
    (hrel : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → ∀ ν : F, D ν → IsUnitAt ϖ ν →
      a ((ϖ : F) ^ 2 * ν) = lam ϖ * a ν)
    (hlam : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → c₀ * (nm ϖ : ℝ) ^ w ≤ ‖lam ϖ‖)
    (h0 : a 0 = 0) (ν : F) (hDν : D ν) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime →
      (∀ Pr : Ideal (𝓞 F), Pr.IsPrime → ((p : 𝓞 F) ∈ Pr) → Submodule.IsPrincipal Pr) → P < p →
      c₀ ^ Module.finrank ℤ (𝓞 F) * (p : ℝ) ^ (Module.finrank ℤ (𝓞 F) * w) * ‖a ν‖ ≤
        ‖a ((p : F) ^ 2 * ν)‖ := by
  by_cases hν : ν = 0
  · refine ⟨0, fun p _ _ _ => ?_⟩
    subst hν; simp [h0]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) ν
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : (algebraMap (𝓞 F) F y) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hy0
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hν; rw [← hxy]; simp
  have hnm0 : ∀ t : 𝓞 F, t ≠ 0 → 0 < nm t := by
    intro t ht
    rw [Nat.pos_iff_ne_zero, nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
  refine ⟨m₀ + nm x + nm y + (discr F).natAbs, fun p hp hpp hpP => ?_⟩
  refine norm_coeff_sq_mul_ge' hD hc₀ hc₁ hrel hlam hp hpp ?_ ?_ hDν ?_
  · intro h
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at h1
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero F)) h1
    omega
  · intro h
    have := Nat.le_of_dvd hm₀ h
    omega
  · intro ϖ hϖ hϖp
    have hnd : ∀ t : 𝓞 F, t ≠ 0 → nm t < p → ¬ ϖ ∣ t := by
      intro t ht hlt hϖt
      have := dvd_of_prime_dvd hϖ hp hϖp (hϖt.trans (dvd_nm t))
      have := Nat.le_of_dvd (hnm0 t ht) this
      omega
    refine ⟨x, y, hnd x hx0 (by omega), hnd y hy0 (by omega), ?_⟩
    rw [← hxy, div_mul_cancel₀ _ hyF]

end Chaining


/-! ### Vanishing with an infinite set of good primes and a strict exponent gap -/

section Abstract

variable {J : Type*}

/-- **Coefficients with $p^e$-growth along $p^2$-dilations for infinitely many primes, with $s + 1 \le e$, vanish.** Let
$a : \mathbb Z^J \to \mathbb C$, $T(p^2m) = p^2T(m)$, $\sum_{m\in S}|a(m)|^2 \le CX^s$ when $T \le X$ on $S$, and for every $m$ some $P$ with
$c\,p^e|a(m)| \le |a(p^2m)|$ for all *good* primes $p > P$, where good primes are unbounded. Then $a = 0$. *Proof:* one good prime suffices:
$c^2p^{2e}|a(m)|^2 \le |a(p^2m)|^2 \le C(p^2M)^s \le |C|M^sp^{2e-2}$ with $M = \max(T(m), 1)$, so $c^2|a(m)|^2p^2 \le |C|M^s$ for arbitrarily large
$p$. (Unlike `coeff_eq_zero_of_growth`, no prime counting is needed; the price is $s < e$, i.e. $n \ge 6$.) -/
@[kb "iwaniec1997" "mean square vs. one large good prime (strict exponent gap), over F"]
theorem coeff_eq_zero_of_growth_strict (a : (J → ℤ) → ℂ) (T : (J → ℤ) → ℝ)
    (hT : ∀ (p : ℕ) (m : J → ℤ), T (((p : ℤ) ^ 2) • m) = (p : ℝ) ^ 2 * T m)
    {s C : ℝ} (hs : 0 ≤ s)
    (hpars : ∀ X : ℝ, 0 < X → ∀ S : Finset (J → ℤ), (∀ m ∈ S, T m ≤ X) → ∑ m ∈ S, ‖a m‖ ^ 2 ≤ C * X ^ s)
    {e : ℕ} (hse : s + 1 ≤ e) {c : ℝ} (hc : 0 < c) (good : ℕ → Prop)
    (hinf : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ good p)
    (hgrow : ∀ m, ∃ P : ℕ, ∀ p : ℕ, p.Prime → good p → P < p →
      c * (p : ℝ) ^ e * ‖a m‖ ≤ ‖a (((p : ℤ) ^ 2) • m)‖)
    (m₀ : J → ℤ) : a m₀ = 0 := by
  classical
  by_contra ha
  set δ := ‖a m₀‖ ^ 2 with hδdef
  have hδ : 0 < δ := by have := norm_pos_iff.mpr ha; positivity
  obtain ⟨P, hP⟩ := hgrow m₀
  set M : ℝ := max (T m₀) 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := |C| * M ^ s / (c ^ 2 * δ) with hKdef
  obtain ⟨p, hpN, hp, hgood⟩ := hinf (P + ⌈K⌉₊)
  have hr := hP p hp hgood (by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpK : K < p := by
    have := Nat.le_ceil K
    have h2 : (⌈K⌉₊ : ℝ) < p := by exact_mod_cast (by omega : ⌈K⌉₊ < p)
    linarith
  -- Parseval for the single coefficient `p² m₀`
  have hX : (0 : ℝ) < (p : ℝ) ^ 2 * M := by positivity
  have hpar := hpars _ hX {((p : ℤ) ^ 2) • m₀} (by
    intro m hm
    rw [Finset.mem_singleton] at hm
    rw [hm, hT]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
  rw [Finset.sum_singleton] at hpar
  have hlow : c ^ 2 * (p : ℝ) ^ (2 * e) * δ ≤ ‖a (((p : ℤ) ^ 2) • m₀)‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hr 2
    calc c ^ 2 * (p : ℝ) ^ (2 * e) * δ = (c * (p : ℝ) ^ e * ‖a m₀‖) ^ 2 := by
          rw [hδdef, pow_mul]; ring
      _ ≤ _ := this
  have hupper : C * ((p : ℝ) ^ 2 * M) ^ s ≤ |C| * M ^ s * (p : ℝ) ^ (2 * e - 2) := by
    have h1 : C * ((p : ℝ) ^ 2 * M) ^ s ≤ |C| * ((p : ℝ) ^ 2 * M) ^ s :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2 : ((p : ℝ) ^ 2 * M) ^ s = ((p : ℝ) ^ 2) ^ s * M ^ s := Real.mul_rpow (by positivity) hM.le
    have he1 : 1 ≤ e := by
      have : (1 : ℝ) ≤ e := by linarith
      exact_mod_cast this
    have h3 : ((p : ℝ) ^ 2) ^ s ≤ (p : ℝ) ^ (2 * e - 2) := by
      have e2 : (p : ℝ) ^ (2 * e - 2) = ((p : ℝ) ^ 2) ^ ((e - 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul]; congr 1; omega
      rw [e2]
      refine Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hp1) ?_
      rw [Nat.cast_sub he1]; push_cast; linarith
    calc C * ((p : ℝ) ^ 2 * M) ^ s ≤ |C| * (((p : ℝ) ^ 2) ^ s * M ^ s) := by rw [← h2]; exact h1
      _ ≤ |C| * ((p : ℝ) ^ (2 * e - 2) * M ^ s) := by gcongr
      _ = _ := by ring
  have hchain := hlow.trans (hpar.trans hupper)
  -- divide by `p^{2e-2}`
  have he1 : 1 ≤ e := by
    have : (1 : ℝ) ≤ e := by linarith
    exact_mod_cast this
  have hpe : (p : ℝ) ^ (2 * e) = (p : ℝ) ^ (2 * e - 2) * (p : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hpe] at hchain
  have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * e - 2) := by positivity
  have h4 : c ^ 2 * δ * (p : ℝ) ^ 2 ≤ |C| * M ^ s := by
    have : (p : ℝ) ^ (2 * e - 2) * (c ^ 2 * δ * (p : ℝ) ^ 2) ≤ (p : ℝ) ^ (2 * e - 2) * (|C| * M ^ s) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos
  have h5 : |C| * M ^ s < c ^ 2 * δ * (p : ℝ) := by
    have hK' : K * (c ^ 2 * δ) = |C| * M ^ s := by rw [hKdef]; field_simp
    rw [← hK']
    have : 0 < c ^ 2 * δ := by positivity
    nlinarith
  have h6 : c ^ 2 * δ * (p : ℝ) ≤ c ^ 2 * δ * (p : ℝ) ^ 2 := by
    have : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  linarith

end Abstract


section Cusp

variable [IsTotallyReal F]

/-- **A Hilbert cusp form with $p^e$-growth along infinitely many good primes and $dk + 1 \le e$ vanishes**: $f \in S_k(\Gamma_0(\mathfrak N), \chi)$,
$\mathfrak N \ne 0$; if good primes are unbounded and for every $\nu \in \mathfrak d^{-1}$ there is $P$ with $c\,p^e|a_\nu| \le |a_{p^2\nu}|$ for good
primes $p > P$, then $f = 0$ (`coeff_eq_zero_of_growth_strict` with the trace-ordered mean square, `sum_sq_qCoeff_le_trace_of_cuspFormChar`). -/
@[kb "iwaniec1997" "Hecke mean square vs. one good prime, over F (strict gap)"]
theorem eq_zero_of_growth_strict {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℕ}
    {f : (InfinitePlace F → UpperHalfPlane) → ℂ} (hf : f ∈ cuspFormChar 𝔑 χ (k : ℤ))
    {e : ℕ} (hke : Fintype.card (InfinitePlace F) * k + 1 ≤ e) {c : ℝ} (hc : 0 < c) (good : ℕ → Prop)
    (hinf : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ good p)
    (hgrow : ∀ m : Fin (Module.finrank ℚ F) → ℤ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → good p → P < p →
      c * (p : ℝ) ^ e * ‖qCoeff f (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
          (realVec (QuadFormsKB.Analysis.dualElt 1 m))‖ ≤
        ‖qCoeff f (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
          (realVec ((p : F) ^ 2 * QuadFormsKB.Analysis.dualElt 1 m))‖) :
    f = 0 := by
  classical
  set b := koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
  set a : (Fin (Module.finrank ℚ F) → ℤ) → ℂ :=
    fun m => qCoeff f b (realVec (QuadFormsKB.Analysis.dualElt 1 m)) with hadef
  obtain ⟨C, hC⟩ := sum_sq_qCoeff_le_trace_of_cuspFormChar h𝔑 hf
  have hzero : ∀ m, a m = 0 := by
    refine coeff_eq_zero_of_growth_strict a
      (fun m => ((Algebra.trace ℚ F (QuadFormsKB.Analysis.dualElt 1 m) : ℚ) : ℝ)) ?_
      (s := (Fintype.card (InfinitePlace F) : ℝ) * ((k : ℤ) : ℝ)) (by positivity)
      (C := Real.exp (4 * π) * C ^ 2) ?_ (e := e) ?_ hc good hinf ?_
    · intro p m
      rw [dualElt_zsmul]
      have e1 : (((p : ℤ) ^ 2 : ℤ) : F) * QuadFormsKB.Analysis.dualElt 1 m =
          ((p : ℚ) ^ 2) • QuadFormsKB.Analysis.dualElt 1 m := by
        rw [Algebra.smul_def]; simp
      rw [e1, LinearMap.map_smul, smul_eq_mul]
      push_cast; ring
    · intro X hX S hS
      exact hC X hX S hS
    · push_cast; exact_mod_cast hke
    · intro m
      obtain ⟨P, hP⟩ := hgrow m
      refine ⟨P, fun p hp hg hpP => ?_⟩
      have h := hP p hp hg hpP
      simp only [hadef]
      rw [dualElt_zsmul]
      push_cast
      exact h
  funext z
  have h := hasSum_qExpansion hf.1.2.1 (isLatticePeriodic_of_mem_cuspFormChar hf) z
  have h0 : ∀ m, qCoeff f b (dualVec b m) * qTerm (dualVec b m) z = 0 := by
    intro m
    rw [dualVec_koecherBasis]
    have := hzero m
    simp only [hadef] at this
    rw [this, zero_mul]
  rw [show (fun m => qCoeff f b (dualVec b m) * qTerm (dualVec b m) z) = fun _ => 0 from
    funext h0] at h
  simpa using h.unique hasSum_zero

/-- **Vanishing from $T(\pi^2)$ relations at principal primes, any class number, weight $k \ge 3$.** Let $f \in S_k(\Gamma_0(\mathfrak N), \chi)$,
$m_0 \ge 1$, with $a_{\pi^2\nu} = \lambda(\pi)a_\nu$ and $|\lambda(\pi)| \ge \frac12N(\pi)^{2k-2}$ for every prime element $\pi \nmid m_0$ and $\nu$ a
unit at $\pi$. Given `PrincipalPrimeSupply F` (infinitely many rational primes all of whose prime factors are principal), $f = 0$. *Proof:*
`exists_growth_of_rel'` gives the growth $2^{-d}p^{d(2k-2)}$ along those primes; $d(2k - 2) \ge dk + 1$ for $k \ge 3$
(`eq_zero_of_growth_strict`). For $\mathcal O_F$ a PID this is `eq_zero_of_heckeRel` (which also covers $k = 2$, using all primes). -/
@[kb "iwaniec1997" "vanishing over F from T(π²) relations at principal primes, k ≥ 3, any class number (given PrincipalPrimeSupply)"]
theorem eq_zero_of_heckeRel' (hPS : PrincipalPrimeSupply F) {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℕ}
    (hk : 3 ≤ k) {f : (InfinitePlace F → UpperHalfPlane) → ℂ} (hf : f ∈ cuspFormChar 𝔑 χ (k : ℤ))
    {lam : 𝓞 F → ℂ} {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hrel : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → ∀ m : Fin (Module.finrank ℚ F) → ℤ,
      IsUnitAt ϖ (QuadFormsKB.Analysis.dualElt 1 m) →
      qCoeff f (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
          (realVec ((ϖ : F) ^ 2 * QuadFormsKB.Analysis.dualElt 1 m)) =
        lam ϖ * qCoeff f (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
          (realVec (QuadFormsKB.Analysis.dualElt 1 m)))
    (hlam : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → (nm ϖ : ℝ) ^ (2 * k - 2) / 2 ≤ ‖lam ϖ‖) :
    f = 0 := by
  classical
  set b := koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
  have h0 : qCoeff f b (realVec 0) = 0 := by
    have : realVec (0 : F) = 0 := by funext v; simp [realVec]
    rw [this]
    have hz := hf.1.2.2 1
    simp only [map_one, SlashAction.slash_one] at hz
    exact qCoeff_zero_eq_zero hf.1.2.1 (isLatticePeriodic_of_mem_cuspFormChar hf) hz
  have hd := finrank_eq_card_infinitePlace (F := F)
  set good : ℕ → Prop := fun p =>
    ∀ P : Ideal (𝓞 F), P.IsPrime → ((p : 𝓞 F) ∈ P) → Submodule.IsPrincipal P
  refine eq_zero_of_growth_strict h𝔑 hf (e := Module.finrank ℤ (𝓞 F) * (2 * k - 2)) ?_
    (c := (1 / 2) ^ Module.finrank ℤ (𝓞 F)) (by positivity) good hPS.exists_prime ?_
  · rw [← hd]
    have hd1 : 1 ≤ Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have : Module.finrank ℤ (𝓞 F) * k + Module.finrank ℤ (𝓞 F) ≤ Module.finrank ℤ (𝓞 F) * (2 * k - 2) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  · intro m
    refine exists_growth_of_rel' (a := fun ν => qCoeff f b (realVec ν))
      (D := fun ν => ∃ m', QuadFormsKB.Analysis.dualElt 1 m' = ν)
      (fun t ν ⟨m', hm'⟩ => by rw [← hm']; exact exists_dualElt_mul t m') (by norm_num) (by norm_num)
      hm₀ (fun ϖ hϖ hϖm ν ⟨m', hm'⟩ hu => by subst hm'; exact hrel ϖ hϖ hϖm m' hu) (fun ϖ hϖ hϖm => by
        have := hlam ϖ hϖ hϖm; linarith) h0 _ ⟨m, rfl⟩

end Cusp

end QuadFormsKB.HilbertModular
