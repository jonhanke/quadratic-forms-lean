/-
# Theorem 5.7 over $\mathbb{Q}$: hypothesis-free per-prime and product lower bounds at every $p \nmid N$

**Layer:** $\mathbb{Q}$ (`QuadForm ℤ n`, $p$ a rational prime, $N$ = `level Q`, $\Delta$ = `disc Q` $= (-1)^{n/2}\det H$).
This is the $\mathbb{Q}$ counterpart of `Siegel/NFDyadicGoodUncond.lean`.

**What is new here.** The per-prime bounds L10 and the products L11 of `LocalDensity/LowerBounds.lean`
(`localDensity_ge_even`, `prod_localDensity_ge_even`, `prod_localDensity_ge_four`, `prod_localDensity_ge_odd`) are stated
for a unimodular diagonal form at odd $p$, or take, at each $p \in S$, such a form with the same counts as a hypothesis
(`hQa`), with the character written in terms of its entries. Here they are stated for **every** nondegenerate $Q$, at
**every** prime $p \nmid N$ (the paper's good primes, p. 357), with Hanke's character $\Phi_n(p)$ written intrinsically:

* $n$ even: $\Phi_n(p) = \left(\frac{\Delta}{p}\right)$, the Kronecker symbol `kroneckerSym (disc Q) p`. For odd $p$ this is
  the Legendre symbol $\left(\frac{(-1)^{n/2}\det H}{p}\right)$ (`kroneckerSym_disc_of_ne_two`); at $p = 2 \nmid N$ it is
  $\chi_8(\Delta)$, and it is the Arf sign of $Q \otimes \mathbb{Z}_2$ (`arfSignQ_two_eq_chi8`). So **$p = 2$ is a good prime**
  when $N$ is odd, as in the paper; `MainTerm.lean` and `GlobalLowerBound.lean` treat it as bad.
* $n$ odd: every $p \nmid N$ is odd (`two_dvd_level_of_odd`), and
  $\Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right)$ (Hanke's $D = \det H/2^n$; `legendreSym_prod_eq_odd`).

**Proofs.** At odd $p \nmid N$: Lemma 2.1 (`exists_diag_unimodular_same_counts_det`, with the determinant tracked) and the
diagonal results. At $p = 2 \nmid N$ ($n$ even): the bridge $\beta_2 = \beta_{\mathbb{Z}_2}$ (`localDensity_eq_padic`), $2^0$ is a
local level of $Q \otimes \mathbb{Z}_2$ (`isLocalLevel_two_of_odd_level`), and the dyadic per-place bound for a general even
unimodular form (`DVR.localDensity_ge_of_level_zero_dyadic`, via the pair-sum normal form). All proofs are local and
combinatorial (counting solutions mod $p^k$); nothing global is used.

**Headline results.**
* `localDensity_ge_even_level` (L10, $n$ even, every $p \nmid N$);
* `localDensity_ge_odd_level`, `localDensity_ge_three_level` (L10, $n$ odd);
* `prod_localDensity_ge_even_level`, `prod_localDensity_ge_four_level`, `prod_localDensity_ge_odd_level` (L11: the local
  parts of Thm 5.7(b), (c) and the second part of (a), for any finite set $S$ of primes $p \nmid N$);
* `localConstC'_level_even` ((5.12) corrected at every $p \nmid N$, $n$ even), `thm_5_7_c_even_level`, `thm_5_7_b_level`
  (ratio forms of Thm 5.7(b), (c) with the paper's bad set $\{p \mid N\}$; for odd $n$, `thm_5_7_c_odd` already has it,
  `isGoodPrime_iff_not_dvd_level`);
* `aE_four_ge_level` (the explicit lower bound $a_E(T') \ge 6D^{-1/2}T'\prod_{p \mid N}\beta_p(T')\prod\frac{p-1}{p+1}$ of
  Thm 5.7(b) with bad set $\{p \mid N\}$).

**Paper:** Hanke 2004, proof of Thm 5.7, pp. 374–376 (locators checked against the printed PDF).
-/
import QuadFormsKB.Siegel.MainTerm
import QuadFormsKB.Siegel.NFDyadicGood
import QuadFormsKB.LocalDensity.BridgeExplicit
import QuadFormsKB.Siegel.GlobalLowerBound

namespace QuadFormsKB.Siegel

open LocalDensity QuadForm

variable {n : ℕ}

local notation "ι2" => Int.castRingHom ℤ_[2]

/-! ### The character $\Phi_n(p)$ at $p \nmid N$ -/

/-- For odd $p$, $\left(\frac{\Delta}{p}\right) = \left(\frac{(-1)^{n/2}\det H}{p}\right)$ (Legendre symbol). -/
theorem kroneckerSym_disc_of_ne_two (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    kroneckerSym (disc Q) p = legendreSym p ((-1) ^ (n / 2) * Q.hessian.det) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rw [kroneckerSym_of_odd _ hodd, disc, jacobiSym.legendreSym.to_jacobiSym]

/-- $2 \nmid N \Rightarrow 2 \nmid \det H$, so $\Delta$ is odd. -/
theorem disc_odd_of_two_not_dvd_level {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hN : ¬ 2 ∣ level Q) :
    Odd (disc Q) := by
  have h2 : ¬ ((2 : ℕ) : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ Nat.prime_two).2 h)
  rw [← Int.not_even_iff_odd]
  intro he
  apply h2
  have : (2 : ℤ) ∣ disc Q := even_iff_two_dvd.1 he
  rw [disc] at this
  rcases neg_one_pow_eq_or ℤ (n / 2) with h1 | h1 <;> rw [h1] at this <;> simpa using this

/-- At $p = 2 \nmid N$: $\left(\frac{\Delta}{2}\right) = \chi_8(\Delta)$. -/
theorem kroneckerSym_disc_two {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hN : ¬ 2 ∣ level Q) :
    kroneckerSym (disc Q) 2 = ZMod.χ₈ (disc Q) := by
  have ho := disc_odd_of_two_not_dvd_level hQ hN
  have hne : ¬ Even (disc Q) := Int.not_even_iff_odd.2 ho
  have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  simp only [kroneckerSym, hne, ite_false, h2, pow_one, Nat.div_self two_pos, jacobiSym.one_right, mul_one]

/-- For odd $n$, $2 \mid N$ ($\det H$ is even, `hessian_det_even`). So every prime $p \nmid N$ is odd. -/
theorem two_dvd_level_of_odd {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hodd : Odd n) : 2 ∣ level Q :=
  (prime_dvd_level_iff hQ Nat.prime_two).2 (by exact_mod_cast even_iff_two_dvd.1 (hessian_det_even hodd))

/-- **$\Phi_n(p) = \pm 1$ at $p \nmid N$** ($n$ even): the Kronecker symbol $\left(\frac{\Delta}{p}\right)$ is a sign. -/
theorem kroneckerSym_disc_eq_or {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hN : ¬ p ∣ level Q) :
    kroneckerSym (disc Q) p = 1 ∨ kroneckerSym (disc Q) p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst h2
    rw [kroneckerSym_disc_two hQ hN]
    have ho := disc_odd_of_two_not_dvd_level hQ hN
    rw [ZMod.χ₈_int_eq_if_mod_eight]
    have : disc Q % 2 = 1 := Int.odd_iff.1 ho
    split_ifs <;> simp_all
  · rw [kroneckerSym_disc_of_ne_two Q p h2]
    have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ hp).2 h)
    have hu : ((((-1) ^ (n / 2) * Q.hessian.det : ℤ)) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      rcases neg_one_pow_eq_or ℤ (n / 2) with h1 | h1 <;> rw [h1] at h
      · exact hdet (by simpa using h)
      · exact hdet (by simpa using h)
    exact legendreSym.eq_one_or_neg_one p hu

/-! ### Per-prime bounds (L10) at every $p \nmid N$ -/

open Classical in
/-- **Per-prime lower bound at $p \nmid N$, $n$ even, any nondegenerate $Q$** (Hanke 2004, proof of Thm 5.7(b), (c),
p. 374). For $n \ge 4$ even, a prime $p \nmid N$ (including $p = 2$ when $N$ is odd) and $m \ne 0$, with
$\Phi = \Phi_n(p) = \left(\frac{\Delta}{p}\right)$ and $X = p^{(n-2)/2}$:
$$\beta_p(m) \;\ge\; \Big(1 - \frac{\Phi}{p^{n/2}}\Big)\cdot\begin{cases}\dfrac{X-1}{X+1} & \Phi = -1,\ p \mid m,\\ 1 & \text{otherwise.}
\end{cases}$$
The first factor is the local factor of $L(n/2, \Phi_n)^{-1}$; for $n = 4$ the second is the $\frac{p-1}{p+1}$ of Thm 5.7(b).
*Update:* the paper's good primes are the $p \nmid N$, and at $p = 2 \nmid N$ the same bound holds with
$\Phi_n(2) = \chi_8(\Delta)$ (the Arf sign); the paper does not compute the dyadic factor (Table 1 is for $p \nmid 2N$). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at every p ∤ N, n even, general Q)"]
theorem localDensity_ge_even_level (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n)
    (p : ℕ) [Fact p.Prime] (hN : ¬ p ∣ level Q) (m : ℤ) (hm : m ≠ 0) :
    (1 - (kroneckerSym (disc Q) p : ℝ) / (p : ℝ) ^ (n / 2)) *
        (if kroneckerSym (disc Q) p = -1 ∧ (p : ℤ) ∣ m then
          ((p : ℝ) ^ ((n - 2) / 2) - 1) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1) ≤
      localDensity Q p m := by
  have hpp : p.Prime := Fact.out
  by_cases h2 : p = 2
  · subst h2
    let _ : Fintype (IsLocalRing.ResidueField ℤ_[2]) :=
      Fintype.ofEquiv (ZMod 2) PadicInt.residueField.symm.toEquiv
    have hodd : Odd (level Q) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hN)
    have hL := isLocalLevel_two_of_odd_level hQ hodd
    have h := DVR.localDensity_ge_of_level_zero_dyadic (Q.map ι2) irreducible_two_padicInt dvd_rfl two_ne_zero
      hL (by omega) (ι2 m) (by simpa using hm)
    rw [arfSignQ_two_eq_chi8 hQ (by omega) hodd, q_padicInt] at h
    rw [kroneckerSym_disc_two hQ hN, localDensity_eq_padic]
    have hdvd : (2 : ℤ_[2]) ∣ ι2 m ↔ (2 : ℤ) ∣ m := two_dvd_intCast_iff m
    have hm' : ((m : ℤ) : ℤ_[2]) = ι2 m := rfl
    simp only [Nat.cast_ofNat, hm'] at h ⊢
    rw [show (n - 2) / 2 = n / 2 - 1 by omega]
    convert h using 3
    exact and_congr_right fun _ => hdvd.symm
  · have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ hpp).2 h)
    obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p h2 hdet
    have hχ := legendreSym_prod_eq_even Q heven p h2 a hu hprod (n / 2)
    rw [kroneckerSym_disc_of_ne_two Q p h2, ← hχ,
      (localDensity_congr_of_repCount Q (QuadForm.diag a) p hcnt m).1]
    exact localDensity_ge_even a p h2 ha hn heven m hm

open Classical in
/-- **Per-prime lower bound at $p \nmid N$, $n$ odd, any nondegenerate $Q$** (Hanke 2004, proof of Thm 5.7(a), (c),
p. 375): for $n \ge 3$ odd, $p \nmid N$ (so $p$ is odd), $\mathrm{ord}_p(T') \le 1$, $\nu \ge 0$ and
$\Phi = \Phi_n(p) = \left(\frac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right)$:
$$\beta_p(T'p^{2\nu}) \ge \beta_p(T')\cdot\begin{cases}\dfrac{1 - p^{-(n-1)/2}}{1 - p^{-(n-2)}} & p \nmid T',\ \Phi = 1,\\ 1 & \text{otherwise,}
\end{cases}\qquad \beta_p(T') = \begin{cases}1 - p^{-(n-1)} & p \mid T',\\ 1 + \Phi p^{-(n-1)/2} & p \nmid T'.\end{cases}$$ -/
@[kb "hanke2004" "Proof of Thm 5.7(a),(c), p. 375 (local factor at p ∤ N, n odd, general Q)"]
theorem localDensity_ge_odd_level (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (hodd : Odd n)
    (p : ℕ) [Fact p.Prime] (hN : ¬ p ∣ level Q) (T : ℤ) (hT0 : T ≠ 0) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ) :
    (if (p : ℤ) ∣ T then 1 - 1 / (p : ℝ) ^ (n - 1) else
        1 + (legendreSym p ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) : ℝ) / (p : ℝ) ^ ((n - 1) / 2)) *
      (if ¬ (p : ℤ) ∣ T ∧ legendreSym p ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1 then
        (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) else 1) ≤
      localDensity Q p ((p : ℤ) ^ (2 * ν) * T) := by
  have hpp : p.Prime := Fact.out
  have h2 : p ≠ 2 := fun h => hN (h ▸ two_dvd_level_of_odd hQ hodd)
  have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ hpp).2 h)
  obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p h2 hdet
  rw [← legendreSym_prod_eq_odd Q hodd p h2 a hu hprod, (localDensity_congr_of_repCount Q (QuadForm.diag a) p hcnt _).1]
  exact localDensity_ge_odd a p h2 ha hn hodd T hT0 hT2 ν

/-- **$n = 3$, $p \nmid N$, any nondegenerate $Q$:** $\beta_p(T'p^{2\nu}) \ge \beta_p(T')$ for $\mathrm{ord}_p(T') \le 1$ (Hanke 2004,
first part of Thm 5.7(a), p. 374: $C'_p(T') = 1$ at $p \nmid N$ when $n = 3$). -/
@[kb "hanke2004" "Thm 5.7(a), p. 374 (p ∤ N, n = 3, general Q)"]
theorem localDensity_ge_three_level (Q : QuadForm ℤ 3) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hN : ¬ p ∣ level Q) (T : ℤ) (hT0 : T ≠ 0) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ) :
    localDensity Q p T ≤ localDensity Q p ((p : ℤ) ^ (2 * ν) * T) := by
  have hpp : p.Prime := Fact.out
  have h2 : p ≠ 2 := fun h => hN (h ▸ two_dvd_level_of_odd hQ (by decide))
  have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ hpp).2 h)
  obtain ⟨a, ha, hcnt, -⟩ := exists_diag_unimodular_same_counts_det Q p h2 hdet
  rw [(localDensity_congr_of_repCount Q (QuadForm.diag a) p hcnt _).1,
    (localDensity_congr_of_repCount Q (QuadForm.diag a) p hcnt _).1]
  exact localDensity_ge_three a p h2 ha T hT0 hT2 ν

/-! ### Products over a finite set of primes $p \nmid N$ (L11) -/

/-- The two factors of `localDensity_ge_even_level` are nonnegative. -/
theorem even_level_factors_nonneg {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime)
    (hN : ¬ p ∣ level Q) :
    0 ≤ 1 - (kroneckerSym (disc Q) p : ℝ) / (p : ℝ) ^ (n / 2) ∧
      0 ≤ ((p : ℝ) ^ ((n - 2) / 2) - 1) / ((p : ℝ) ^ ((n - 2) / 2) + 1) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hX : (p : ℝ) ≤ (p : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  have hY : (p : ℝ) ≤ (p : ℝ) ^ (n / 2) := le_self_pow₀ (by linarith) (by omega)
  refine ⟨?_, div_nonneg (by linarith) (by linarith)⟩
  have hk : (kroneckerSym (disc Q) p : ℝ) ≤ 1 := by
    rcases kroneckerSym_disc_eq_or hQ hp hN with h | h <;> rw [h] <;> norm_num
  have : (kroneckerSym (disc Q) p : ℝ) / (p : ℝ) ^ (n / 2) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

open Classical in
/-- **The local part of Thm 5.7(b), (c) for $n$ even, at all primes $p \nmid N$, any nondegenerate $Q$** (Hanke 2004,
pp. 373–375). For $n \ge 4$ even, a finite set $S$ of primes $p \nmid N$ and $m \ne 0$, with $\Phi(p) = \left(\frac{\Delta}{p}\right)$
and $X_p = p^{(n-2)/2}$:
$$\prod_{p \in S}\beta_p(m) \;\ge\; \prod_{p \in S}\Big(1 - \frac{\Phi(p)}{p^{n/2}}\Big)
  \prod_{\substack{p \in S,\ p \mid m\\ \Phi(p) = -1}}\frac{X_p - 1}{X_p + 1}.$$
No hypothesis on the shape of $Q$ at $p$; $S$ may contain $2$ when $N$ is odd. -/
@[kb "hanke2004" "Thm 5.7(b),(c), pp. 373-375 (local part at all p ∤ N, n even, general Q)"]
theorem prod_localDensity_ge_even_level (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ level Q) (m : ℤ) (hm : m ≠ 0) :
    (∏ p ∈ S, (1 - (kroneckerSym (disc Q) p : ℝ) / (p : ℝ) ^ (n / 2))) *
        ∏ p ∈ S.filter (fun p => kroneckerSym (disc Q) p = -1 ∧ (p : ℤ) ∣ m),
          (((p : ℝ) ^ ((n - 2) / 2) - 1) / ((p : ℝ) ^ ((n - 2) / 2) + 1)) ≤
      ∏ p ∈ S, localDensity Q p m := by
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨h1, h2⟩ := even_level_factors_nonneg hQ hn (hS p hp).1 (hS p hp).2
    exact mul_nonneg h1 (by split_ifs <;> linarith)
  · have : Fact p.Prime := ⟨(hS p hp).1⟩
    exact localDensity_ge_even_level Q hQ hn heven p (hS p hp).2 m hm

open Classical in
/-- **The local part of Thm 5.7(b) ($n = 4$) at all primes $p \nmid N$, any nondegenerate $Q$** (Hanke 2004, p. 373): for a
finite set $S$ of primes $p \nmid N$, $m \ne 0$ and $\chi(p) = \left(\frac{\det H}{p}\right)$ (Kronecker symbol):
$$\prod_{p \in S}\beta_p(m) \;\ge\; \prod_{p \in S}\Big(1 - \frac{\chi(p)}{p^2}\Big)\prod_{\substack{p \in S,\ p \mid m\\ \chi(p) = -1}}\frac{p-1}{p+1}.$$
The first product is the partial Euler product of $L(2, \chi)^{-1}$, the second is the factor displayed in Thm 5.7(b). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (local part at all p ∤ N, n = 4, general Q)"]
theorem prod_localDensity_ge_four_level (Q : QuadForm ℤ 4) (hQ : Q.Nondegenerate) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ level Q) (m : ℤ) (hm : m ≠ 0) :
    (∏ p ∈ S, (1 - (kroneckerSym Q.hessian.det p : ℝ) / (p : ℝ) ^ 2)) *
        ∏ p ∈ S.filter (fun p => kroneckerSym Q.hessian.det p = -1 ∧ (p : ℤ) ∣ m),
          (((p : ℝ) - 1) / ((p : ℝ) + 1)) ≤
      ∏ p ∈ S, localDensity Q p m := by
  have h := prod_localDensity_ge_even_level Q hQ le_rfl (by decide) S hS m hm
  have hd : disc Q = Q.hessian.det := by simp [disc]
  simp only [hd, show (4 : ℕ) / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, pow_one] at h
  exact h

open Classical in
/-- **The local part of Thm 5.7(a) (second part) and (c) for $n$ odd, at all primes $p \nmid N$, any nondegenerate $Q$**
(Hanke 2004, pp. 375–376). For $n \ge 3$ odd, a finite set $S$ of primes $p \nmid N$, $T' \ne 0$ with
$\mathrm{ord}_p(T') \le 1$ ($p \in S$) and $m = T'(m')^2$, $m' = \prod_{p \in S}p^{\nu_p}$:
$$\prod_{p \in S}\beta_p(m) \;\ge\; \prod_{p \in S}\beta_p(T')\prod_{\substack{p \in S,\ p \nmid T'\\ \Phi_n(p) = 1}}
  \frac{1 - p^{-(n-1)/2}}{1 - p^{-(n-2)}},\qquad \Phi_n(p) = \left(\tfrac{(-1)^{(n-1)/2}\,2\det H\,T'}{p}\right).$$ -/
@[kb "hanke2004" "Thm 5.7(a),(c), pp. 375-376 (local part at all p ∤ N, n odd, general Q)"]
theorem prod_localDensity_ge_odd_level (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (hodd : Odd n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ level Q) (T : ℤ) (hT0 : T ≠ 0)
    (hT2 : ∀ p ∈ S, ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    (∏ p ∈ S, localDensity Q p T) *
        ∏ p ∈ S.filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          ((1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2))) ≤
      ∏ p ∈ S, localDensity Q p (T * (∏ p' ∈ S, (p' : ℤ) ^ ν p') ^ 2) := by
  have hodd2 : ∀ p ∈ S, p ≠ 2 := fun p hp h => (hS p hp).2 (h ▸ two_dvd_level_of_odd hQ hodd)
  choose! a ha hcnt u hu hprod using fun p (hp : p ∈ S) =>
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    exists_diag_unimodular_same_counts_det Q p (hodd2 p hp)
      (fun h => (hS p hp).2 ((prime_dvd_level_iff hQ (hS p hp).1).2 h))
  have h := prod_localDensity_ge_odd Q hn hodd S (fun p hp => ⟨(hS p hp).1, hodd2 p hp⟩) a ha hcnt T hT0 hT2 ν
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.prod_congr (Finset.filter_congr fun p hp => ?_) fun _ _ => rfl
  have : Fact p.Prime := ⟨(hS p hp).1⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym,
    legendreSym_prod_eq_odd Q hodd p (hodd2 p hp) (a p) (hu p hp) (hprod p hp)]

/-! ### $C'_p(T')$ at every $p \nmid N$ and Theorem 5.7(b), (c) (ratio form) with bad set $\{p \mid N\}$ -/

/-- For odd $n$ the good primes of `MainTerm.lean` (`IsGoodPrime`: $p$ odd, $p \nmid \det H$) are exactly the primes
$p \nmid N$; so `thm_5_7_a` and `thm_5_7_c_odd` already have the paper's bad set $\{p \mid N\}$. -/
theorem isGoodPrime_iff_not_dvd_level {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hodd : Odd n) {p : ℕ}
    (hp : p.Prime) : IsGoodPrime Q p ↔ ¬ p ∣ level Q := by
  rw [prime_dvd_level_iff hQ hp]
  refine ⟨fun h => h.2.2, fun h => ⟨hp, fun h2 => h ?_, h⟩⟩
  subst h2
  exact_mod_cast even_iff_two_dvd.1 (hessian_det_even hodd)

open Classical in
/-- **$C'_p(T')$ at every $p \nmid N$, $n \ge 4$ even, any nondegenerate $Q$** (Table 2, p. 370; (5.12) corrected): with
$\Phi = \left(\frac{\Delta}{p}\right)$ and $X = p^{(n-2)/2}$, for $\mathrm{ord}_p(T') \le 1$: $C'_p(T') = X/(X+1)$ if $\Phi = -1$ and
$p \nmid T'$, and $C'_p(T') = 1$ otherwise. Includes $p = 2 \nmid N$ (`DVR.localConstC'_of_level_zero_dyadic`). -/
@[kb "hanke2004" "Table 2, p. 370; (5.12), p. 371 (corrected; every p ∤ N, n even, general Q)"]
theorem localConstC'_level_even (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n)
    (p : ℕ) [Fact p.Prime] (hN : ¬ p ∣ level Q) (T : ℤ) (hT2 : ¬ (p : ℤ) ^ 2 ∣ T) :
    localConstC' Q p T =
      if kroneckerSym (disc Q) p = -1 ∧ ¬ (p : ℤ) ∣ T then
        (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1 := by
  have hpp : p.Prime := Fact.out
  by_cases h2 : p = 2
  · subst h2
    let _ : Fintype (IsLocalRing.ResidueField ℤ_[2]) :=
      Fintype.ofEquiv (ZMod 2) PadicInt.residueField.symm.toEquiv
    have hodd : Odd (level Q) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hN)
    have hL := isLocalLevel_two_of_odd_level hQ hodd
    have hT2' : ¬ (2 : ℤ_[2]) ^ 2 ∣ ι2 T := by
      have := PadicInt.pow_p_dvd_int_iff (p := 2) 2 T
      simp only [Nat.cast_ofNat] at this
      rw [show ι2 T = (T : ℤ_[2]) from rfl, this]; exact_mod_cast hT2
    have hC := DVR.localConstC'_of_level_zero_dyadic (Q.map ι2) irreducible_two_padicInt dvd_rfl two_ne_zero
      hL (by omega) (ι2 T) hT2'
    rw [arfSignQ_two_eq_chi8 hQ (by omega) hodd, q_padicInt] at hC
    have hC' : localConstC' Q 2 T = DVR.localConstC' (Q.map ι2) 2 (ι2 T) := by
      rw [localConstC', DVR.localConstC', localConstC_eq_padic]; rfl
    rw [hC', kroneckerSym_disc_two hQ hN, show (n - 2) / 2 = n / 2 - 1 by omega]
    have hdvd : (2 : ℤ_[2]) ∣ ι2 T ↔ (2 : ℤ) ∣ T := two_dvd_intCast_iff T
    rcases kroneckerSym_disc_eq_or hQ Nat.prime_two hN with hk | hk <;>
      rw [kroneckerSym_disc_two hQ hN] at hk <;> by_cases hT : (2 : ℤ) ∣ T
    · rw [hC.1 (hdvd.2 hT)]; simp [hk]
    · rw [hC.2.1 (fun h => hT (hdvd.1 h)) hk]; simp [hk]
    · rw [hC.1 (hdvd.2 hT)]; simp [hT]
    · rw [hC.2.2.1 (fun h => hT (hdvd.1 h)) hk]; simp [hk, hT]
  · have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h => hN ((prime_dvd_level_iff hQ hpp).2 h)
    rw [localConstC'_good_even Q hn heven p h2 hdet T hT2, kroneckerSym_disc_of_ne_two Q p h2,
      jacobiSym.legendreSym.to_jacobiSym]

open Classical in
/-- **Theorem 5.7(c), $n \ge 4$ even (and (b)), ratio form, with the paper's bad set $\{p \mid N\}$** (Hanke 2004, p. 373;
proof pp. 374–375). As `thm_5_7_c_even`, but "good" is $p \nmid N$ (so $p = 2$ is good when $N$ is odd) and
$\Phi_n(p) = \left(\frac{\Delta}{p}\right)$ (Kronecker symbol):
$$a_E(m) \;\ge\; a_E(T')\,\big((m')_{\mathrm{Iso}}\big)^{n-2}\prod_{p \in S \cap \mathrm{Iso},\ p \mid N}C'_p(T')
  \prod_{\substack{p \in S,\ p \nmid N,\ p \nmid T'\\ \Phi_n(p) = -1}}\frac{X_p}{X_p + 1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even, bad set p | N)"]
theorem thm_5_7_c_even_level (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) (heven : Even n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, ¬ p ∣ level Q → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ ¬ p ∣ level Q),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (fun p => ¬ p ∣ level Q)).filter
            (fun p => kroneckerSym (disc Q) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have hm : T * sqPart S ν ^ 2 ≠ 0 := mul_ne_zero hT.ne' (pow_ne_zero _ (sqPart_pos hS ν).ne')
  have h := aEWith_mul_sq_ge Q hQ (by omega) hS S₀ hT hst ν (fun p => ¬ p ∣ level Q)
    (fun p : ℕ => if kroneckerSym (disc Q) p = -1 ∧ ¬ (p : ℤ) ∣ T then
        (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) else 1)
    (fun p hp hG => by
      have : Fact p.Prime := ⟨hS p hp⟩
      rw [localConstC'_level_even Q hQ.nondegenerate hn heven p hG T (hT2 p hp hG)]
      refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < (p : ℝ) ^ ((n - 2) / 2) := pow_pos (by exact_mod_cast (hS p hp).pos) _
      split_ifs <;> positivity)
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate (by omega) hT.ne')
    (isEulerProductValue_eulerProduct Q hQ.nondegenerate (by omega) hm)
  rw [← Finset.prod_filter] at h
  convert h using 4 <;> first | rfl | (ext; simp)

open Classical in
/-- **Theorem 5.7(b)** (Hanke 2004, p. 373; proof p. 375), ratio form, $n = 4$, **bad set $\{p \mid N\}$**: with
$\chi(p) = \left(\frac{\det H}{p}\right)$ (Kronecker symbol; $\chi(2) = \chi_8(\det H)$ when $N$ is odd),
$$a_E(m) \;\ge\; a_E(T')\,\big((m')_{\mathrm{Iso}}\big)^{2}\prod_{p \in S \cap \mathrm{Iso},\ p \mid N}C'_p(T')
  \prod_{\substack{p \in S,\ p \nmid N,\ p \nmid T'\\ \chi(p) = -1}}\Big(1 + \frac1p\Big)^{-1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form, bad set p | N)"]
theorem thm_5_7_b_level (Q : IntQF 4) (hQ : IntQF.PosDef Q) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (S₀ : Finset (Fin 4)) {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, ¬ p ∣ level Q → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    aE Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ 2 *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ ¬ p ∣ level Q),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (fun p => ¬ p ∣ level Q)).filter
            (fun p => kroneckerSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (1 + 1 / (p : ℝ))⁻¹ ≤
      aE Q (T * sqPart S ν ^ 2) := by
  have h := thm_5_7_c_even_level Q hQ le_rfl (by decide) hS S₀ hT hst hT2 ν
  have hd : disc Q = Q.hessian.det := by simp [disc]
  simp only [hd, show (4 - 2) / 2 = 1 from rfl, show 4 - 2 = 2 from rfl, pow_one] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have : (0 : ℝ) < p := by
    simp only [Finset.mem_filter] at hp; exact_mod_cast (hS p hp.1.1).pos
  field_simp

/-! ### The global lower bound for $a_E(T')$, $n = 4$, with bad set $\{p \mid N\}$ -/

/-- **The primes dividing the level**, $\{p : p \mid N\}$ (the paper's bad primes). -/
noncomputable def levelPrimes (Q : QuadForm ℤ n) : Finset ℕ := (level Q).primeFactors

theorem mem_levelPrimes {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {p : ℕ} :
    p ∈ levelPrimes Q ↔ p.Prime ∧ p ∣ level Q := by
  rw [levelPrimes, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, (level_pos hQ).ne'⟩⟩

/-- $\{p \mid N\} \subseteq \{p \mid 2\det H\}$: the bad set of `badPrimes` contains the paper's. -/
theorem levelPrimes_subset_badPrimes {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) : levelPrimes Q ⊆ badPrimes Q := by
  intro p hp
  obtain ⟨hpp, hd⟩ := (mem_levelPrimes hQ).1 hp
  rw [mem_badPrimes hQ]
  refine ⟨hpp, fun hG => hG.2.2 ((prime_dvd_level_iff hQ hpp).1 hd)⟩

open Classical in
/-- **Partial Euler products, $n = 4$, bad set $\{p \mid N\}$:** for $Q$ nondegenerate quaternary, $T \ge 1$ and
$X \ge \max(N, T)$,
$$\prod_{p \le X}\beta_p(T) \;\ge\; \frac{6}{\pi^2}\prod_{p \mid N}\beta_p(T)
  \prod_{\substack{p \mid T,\ p \nmid N\\ \chi(p) = -1}}\frac{p-1}{p+1},\qquad \chi(p) = \Big(\frac{\det H}{p}\Big)\ \text{(Kronecker)}.$$ -/
theorem eulerPartialProd_four_ge_level (Q : QuadForm ℤ 4) (hQ : Q.Nondegenerate) {T : ℕ} (hT : 0 < T)
    {X : ℕ} (hX1 : level Q ≤ X) (hX2 : T ≤ X) :
    6 / Real.pi ^ 2 * (∏ p ∈ levelPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => ¬ p ∣ level Q ∧ kroneckerSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      eulerPartialProd Q T X := by
  set P := Nat.primesBelow (X + 1) with hP
  have hPmem : ∀ {p}, p ∈ P ↔ p ≤ X ∧ p.Prime := by
    intro p; rw [hP, Nat.mem_primesBelow, Nat.lt_succ_iff]
  have hE : eulerPartialProd Q T X = ∏ p ∈ P, localDensity Q p T := by
    rw [eulerPartialProd, primesUpTo]
    exact Finset.prod_subtype_eq_prod_filter (s := Finset.range (X + 1)) (p := Nat.Prime)
      (fun q : ℕ => localDensity Q q (T : ℤ))
  rw [hE, ← Finset.prod_filter_mul_prod_filter_not P (fun p => ¬ p ∣ level Q)]
  have hbad : P.filter (fun p => ¬ ¬ p ∣ level Q) = levelPrimes Q := by
    ext p
    rw [Finset.mem_filter, hPmem, mem_levelPrimes hQ, not_not]
    constructor
    · rintro ⟨⟨-, hp⟩, hg⟩; exact ⟨hp, hg⟩
    · rintro ⟨hp, hg⟩
      exact ⟨⟨le_trans (Nat.le_of_dvd (level_pos hQ) hg) hX1, hp⟩, hg⟩
  rw [hbad]
  set G := P.filter (fun p => ¬ p ∣ level Q) with hG
  set g : ℕ → ℝ := fun p =>
    if kroneckerSym Q.hessian.det p = -1 ∧ (p : ℤ) ∣ (T : ℤ) then ((p : ℝ) - 1) / ((p : ℝ) + 1) else 1
  have hGprime : ∀ p ∈ G, p.Prime := fun p hp => (hPmem.1 (Finset.mem_filter.1 hp).1).2
  have hd : disc Q = Q.hessian.det := by simp [disc]
  -- the good part
  have hgood : (∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ G, g p ≤ ∏ p ∈ G, localDensity Q p T := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have hp := hGprime p hp
      refine mul_nonneg (one_sub_inv_sq_mem hp).1.le ?_
      simp only [g]
      split_ifs
      · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        exact div_nonneg (by linarith) (by linarith)
      · exact zero_le_one
    · have hN := (Finset.mem_filter.1 hp).2
      have hp := hGprime p hp
      have : Fact p.Prime := ⟨hp⟩
      have h := localDensity_ge_even_level Q hQ le_rfl (by decide) p hN T (by exact_mod_cast hT.ne')
      simp only [hd, show (4 : ℕ) / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, pow_one] at h
      refine le_trans ?_ h
      have hP2 : (0 : ℝ) < (p : ℝ) ^ 2 := by have := hp.pos; positivity
      have hk : (kroneckerSym Q.hessian.det p : ℝ) ≤ 1 := by
        rcases kroneckerSym_disc_eq_or hQ hp hN with h | h <;> rw [hd] at h <;> rw [h] <;> norm_num
      have h1 : 1 - 1 / (p : ℝ) ^ 2 ≤ 1 - (kroneckerSym Q.hessian.det p : ℝ) / (p : ℝ) ^ 2 := by
        have := div_le_div_of_nonneg_right hk hP2.le; linarith
      have hg0 : 0 ≤ g p := by
        simp only [g]; split_ifs
        · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          exact div_nonneg (by linarith) (by linarith)
        · exact zero_le_one
      exact mul_le_mul_of_nonneg_right h1 hg0
  -- the character product
  have hgG : ∏ p ∈ G, g p =
      ∏ p ∈ T.primeFactors.filter (fun p => ¬ p ∣ level Q ∧ kroneckerSym Q.hessian.det p = -1),
        ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
    simp only [g]
    rw [← Finset.prod_filter]
    refine Finset.prod_congr (Finset.ext fun p => ?_) fun _ _ => rfl
    simp only [Finset.mem_filter, hG, hPmem, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨-, hp⟩, hg⟩, hχ, hd⟩
      exact ⟨⟨hp, Int.natCast_dvd_natCast.1 hd, hT.ne'⟩, hg, hχ⟩
    · rintro ⟨⟨hp, hd, -⟩, hg, hχ⟩
      exact ⟨⟨⟨le_trans (Nat.le_of_dvd hT hd) hX2, hp⟩, hg⟩, hχ, Int.natCast_dvd_natCast.2 hd⟩
  -- assemble
  have hz : 6 / Real.pi ^ 2 ≤ ∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2) := six_div_pi_sq_le_prod G hGprime
  have hB0 : 0 ≤ ∏ p ∈ levelPrimes Q, localDensity Q p T := Finset.prod_nonneg fun p hp => by
    have : Fact p.Prime := ⟨((mem_levelPrimes hQ).1 hp).1⟩
    exact LocalDensity.localDensity_nonneg Q hQ p T (by exact_mod_cast hT.ne')
  have hg0 : 0 ≤ ∏ p ∈ G, g p := by
    rw [hgG]
    refine Finset.prod_nonneg fun p hp => ?_
    have : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)
  rw [← hgG]
  calc 6 / Real.pi ^ 2 * (∏ p ∈ levelPrimes Q, localDensity Q p T) * ∏ p ∈ G, g p
      ≤ (∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * (∏ p ∈ levelPrimes Q, localDensity Q p T) *
          ∏ p ∈ G, g p := by gcongr
    _ = ((∏ p ∈ G, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ G, g p) *
          ∏ p ∈ levelPrimes Q, localDensity Q p T := by ring
    _ ≤ (∏ p ∈ G, localDensity Q p T) * ∏ p ∈ levelPrimes Q, localDensity Q p T :=
        mul_le_mul_of_nonneg_right hgood hB0

open Classical in
/-- **The lower bound for $a_E(T')$, $n = 4$, with the paper's bad set $\{p \mid N\}$** (Hanke 2004, Thm 5.7(b), p. 373,
proof pp. 374–375, with $1/L(2,\chi) \ge 6/\pi^2$): for $Q$ positive definite quaternary and $T' \ge 1$,
$$\beta_\infty(T')\prod_p\beta_p(T') \;\ge\; 6\,D^{-1/2}\,T'\prod_{p \mid N}\beta_p(T')
  \prod_{\substack{p \mid T',\ p \nmid N\\ \chi(p) = -1}}\frac{p-1}{p+1},\qquad \chi(p) = \Big(\frac{\det H}{p}\Big)\ \text{(Kronecker)}.$$
Compared with `aE_four_ge` (bad set $\{p \mid 2\det H\}$): when $N$ is odd, $p = 2$ moves from the bad product (factor
$\beta_2(T')$) to the good primes (factor $\ge 1 - 2^{-2}$, times $\frac13$ if $2 \mid T'$ and $\chi(2) = -1$); for odd $p$ the
two bad sets agree. ($\chi(2) = \chi_8(\det H)$ by `kroneckerSym_disc_two`.) -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375 (bad set p | N)"]
theorem aE_four_ge_level (Q : IntQF 4) (hQ : IntQF.PosDef Q) {T : ℕ} (hT : 0 < T) :
    6 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * (∏ p ∈ levelPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => ¬ p ∣ level Q ∧ kroneckerSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      aE Q T := by
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  have hlim := isEulerProductValue_eulerProduct Q hQ.nondegenerate le_rfl hT0
  have hle := ge_of_tendsto hlim (Filter.eventually_atTop.2
    ⟨max (level Q) T, fun X hX =>
      eulerPartialProd_four_ge_level Q hQ.nondegenerate hT (le_of_max_le_left hX)
        (le_of_max_le_right hX)⟩)
  rw [aE, aEWith, betaInf_four]
  have hD : 0 ≤ gramDet Q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDet_pos hQ).le _
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have hTr : (((T : ℤ) : ℝ)) = (T : ℝ) := by push_cast; rfl
  rw [hTr]
  calc 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * (∏ p ∈ levelPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => ¬ p ∣ level Q ∧ kroneckerSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)
      = Real.pi ^ 2 * gramDet Q ^ (-(1 / 2 : ℝ)) * T *
        (6 / Real.pi ^ 2 * (∏ p ∈ levelPrimes Q, localDensity Q p T) *
        ∏ p ∈ T.primeFactors.filter (fun p => ¬ p ∣ level Q ∧ kroneckerSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)) := by field_simp
    _ ≤ Real.pi ^ 2 * gramDet Q ^ (-(1 / 2 : ℝ)) * T * eulerProduct Q T :=
        mul_le_mul_of_nonneg_left hle (by positivity)

end QuadFormsKB.Siegel
