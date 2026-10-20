/-
# Euler products over the primes of a number field

Let $F$ be a number field, $d = [F:\mathbb{Q}]$, and for a nonzero prime $\mathfrak p$ of $\mathcal O_F$
(`HeightOneSpectrum (𝓞 F)`) let $N\mathfrak p = |\mathcal O_F/\mathfrak p|$ (`normP`). This file provides the Euler-product
analysis that Hanke 2004 Thm 5.7 needs over $F$.

**Euler products of local factors.**
* `summable_normP_rpow`: $\sum_{\mathfrak p} N\mathfrak p^{-\sigma} < \infty$ for $\sigma > 1$;
* `multipliable_of_abs_sub_one_le`: if $|f(\mathfrak p) - 1| \le C\,N\mathfrak p^{-\sigma}$ for almost all $\mathfrak p$
  ($\sigma > 1$), then $\prod_{\mathfrak p} f(\mathfrak p)$ converges unconditionally (absolutely); if moreover every
  $f(\mathfrak p) \ne 0$ the value is nonzero (`tprod_ne_zero_of_abs_sub_one_le`);
* `IsEulerProductValueNF f P`: the natural-order value $\prod_{N\mathfrak p \le X} f(\mathfrak p) \to P$ as
  $X \to \infty$ (the $n = 3$ analogue of `Siegel.IsEulerProductValue`), unique (`IsEulerProductValueNF.unique`) and
  implied by unconditional convergence (`isEulerProductValueNF_of_hasProd`).

**Euler product of $\zeta_F$.** For real $s > 1$,
$\zeta_F(s) = \sum_{\mathfrak a} N\mathfrak a^{-s}$ (`hasSum_absNorm_rpow`, from Mathlib's `NumberField.dedekindZeta`) and
$$\zeta_F(s) = \prod_{\mathfrak p}(1 - N\mathfrak p^{-s})^{-1}$$
(`hasProd_dedekindZeta`). *Proof* (a sieve, using only unique factorization in the form "$\mathfrak p \mid \mathfrak a
\Rightarrow \mathfrak a = \mathfrak p\mathfrak b$"): with $Z(T) = \sum_{\mathfrak a\ \text{prime to}\ T}N\mathfrak a^{-s}$,
$Z(T \cup \{\mathfrak p\}) = (1 - N\mathfrak p^{-s})\,Z(T)$, so $\prod_{\mathfrak p \in T}(1 - N\mathfrak p^{-s}) = Z(T)/\zeta_F(s)$,
and $Z(T) \to 1$ because an ideal $\ne \mathcal O_F$ prime to all $\mathfrak p$ with $N\mathfrak p \le X$ has norm $> X$.

**Comparison with $\zeta$.** Every $\mathfrak p$ lies over a rational prime $p$ (`primeBelow`), with
$p \le N\mathfrak p \le p^d$ and at most $d$ primes over each $p$ (`card_le_finrank`). Hence, for real $s > 1$,
$$1 \le \zeta_F(s) \le \zeta(s)^d \quad(\texttt{one\_le\_dedekindZetaR},\ \texttt{dedekindZetaR\_le\_zetaR\_pow}),\qquad
  \prod_{\mathfrak p \in S}(1 - N\mathfrak p^{-2}) \ge \zeta_F(2)^{-1} \ge (6/\pi^2)^d$$
for every finite set $S$ of primes (`six_div_pi_sq_pow_le_prod`).

*Note on the requested lower bound $\zeta(s) \le \zeta_F(s)$:* it is **false** in general (for $F = \mathbb{Q}(i)$,
$\zeta_F(s) = \zeta(s)L(s,\chi_{-4})$ and $L(s,\chi_{-4}) < 1$ for real $s > 1$); the correct elementary lower bound
proved here is $\zeta_F(s) \ge 1$. Hanke's argument only uses the upper bound.

Sources: Neukirch, *Algebraic Number Theory*, Ch. VII §5 (Dedekind zeta function, Euler product) and Ch. I §8
(primes over $p$, $\sum e_i f_i = d$) [unverified locators].
-/
import Mathlib
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

namespace QuadFormsKB.NFEuler

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### Primes of $F$ and their norms -/

/-- **The absolute norm $N\mathfrak p = |\mathcal O_F/\mathfrak p|$** of a nonzero prime $\mathfrak p$ of $\mathcal O_F$
(Mathlib's `Ideal.absNorm`). -/
abbrev normP (𝔭 : HeightOneSpectrum (𝓞 F)) : ℕ := Ideal.absNorm 𝔭.asIdeal

theorem asIdeal_injective :
    Function.Injective (fun 𝔭 : HeightOneSpectrum (𝓞 F) => 𝔭.asIdeal) :=
  fun _ _ h => HeightOneSpectrum.ext h

/-- $N\mathfrak p \ge 2$. -/
theorem two_le_normP (𝔭 : HeightOneSpectrum (𝓞 F)) : 2 ≤ normP 𝔭 := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact 𝔭.isPrime.ne_top
  unfold normP; omega

theorem rpow_neg_normP_pos (𝔭 : HeightOneSpectrum (𝓞 F)) (s : ℝ) : 0 < (normP 𝔭 : ℝ) ^ (-s) :=
  Real.rpow_pos_of_pos (by have := two_le_normP 𝔭; positivity) _

/-- $N\mathfrak p^{-s} \le 1/2$ for $s \ge 1$. -/
theorem rpow_neg_normP_le_half (𝔭 : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 1 ≤ s) :
    (normP 𝔭 : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ normP 𝔭 := by exact_mod_cast two_le_normP 𝔭
  rw [Real.rpow_neg (by positivity), one_div]
  refine inv_anti₀ (by norm_num) ?_
  calc (2 : ℝ) ≤ normP 𝔭 := h2
    _ = (normP 𝔭 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs

/-! ### $\zeta_F(s)$ as a sum over ideals -/

/-- The Dirichlet series of $\zeta_F$ converges for real $s > 1$ (otherwise `LSeries` would be $0$ near $1^+$,
contradicting the class number formula `tendsto_sub_one_mul_dedekindZeta_nhdsGT`). -/
theorem lSeriesSummable_dedekindZeta {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) := by
  by_contra hns
  have hev : (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta F t) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT hs] with t ht
    have : ¬ LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
        (t : ℂ) := fun h => hns (h.of_re_le_re (by simpa using ht.2.le))
    rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ this, mul_zero]
  have h1 := tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have h2 : Tendsto (fun t : ℝ => ((t : ℂ) - 1) * dedekindZeta F t) (nhdsWithin 1 (Set.Ioi 1))
      (𝓝 0) := tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique h1 h2
  have hpos := dedekindZeta_residue_pos F
  norm_cast at this
  linarith

/-- **$\zeta_F(s)$ for real $s$**, as a real number: $\operatorname{Re}\zeta_F(s)$ (for $s > 1$ the value is real,
`hasSum_absNorm_rpow`). -/
def dedekindZetaR (F : Type) [Field F] [NumberField F] (s : ℝ) : ℝ := (dedekindZeta F s).re

/-- **$\zeta_F(s) = \sum_{\mathfrak a} N\mathfrak a^{-s}$ for real $s > 1$**, the sum over all ideals of $\mathcal O_F$
(the zero ideal contributes $0^{-s} = 0$), converging absolutely. -/
@[kb "neukirch1999" "Ch. VII §5 [unverified]"]
theorem hasSum_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    HasSum (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-s)) (dedekindZetaR F s) := by
  have hs0 : s ≠ 0 := by linarith
  set a : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) with ha
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
      (s : ℂ) n = ((a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (neg_ne_zero.mpr hs0)]
    · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_mul,
        Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      simp [ha, div_eq_mul_inv]
  have hsumC := lSeriesSummable_dedekindZeta (F := F) hs
  have hsumR : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s)) :=
    Complex.summable_ofReal.mp (Summable.congr hsumC hterm)
  have hzeta : dedekindZetaR F s = ∑' n : ℕ, a n * (n : ℝ) ^ (-s) := by
    rw [dedekindZetaR, dedekindZeta, LSeries]
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  set G : Ideal (𝓞 F) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-s) with hG
  set e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hfin : ∀ n, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := fun n =>
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  have hGe : (fun x => G (e x)) = fun x => ((x.1 : ℕ) : ℝ) ^ (-s) := by
    funext x
    obtain ⟨n, I, hI⟩ := x
    simp [e, Equiv.sigmaFiberEquiv, hG, hI]
  have hfib : ∀ n : ℕ, Summable fun I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} =>
      ((n : ℕ) : ℝ) ^ (-s) := fun n => Summable.of_finite
  have hsum : Summable (fun x => G (e x)) := by
    rw [hGe, summable_sigma_of_nonneg (fun _ => by positivity)]
    refine ⟨hfib, ?_⟩
    simp_rw [tsum_const, nsmul_eq_mul]
    exact hsumR
  have hsumG : Summable G := e.summable_iff.mp hsum
  have hsum' : Summable fun x : (Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n}) =>
      ((x.1 : ℕ) : ℝ) ^ (-s) := by rw [← hGe]; exact hsum
  convert hsumG.hasSum using 1
  rw [hzeta, ← e.tsum_eq, hGe, Summable.tsum_sigma' hfib hsum']
  congr 1
  funext n
  change _ = ∑' _ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, ((n : ℕ) : ℝ) ^ (-s)
  rw [tsum_const, nsmul_eq_mul]

theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-s)) :=
  (hasSum_absNorm_rpow hs).summable

/-! ### Products of local factors -/

/-- **$\sum_{\mathfrak p} N\mathfrak p^{-\sigma} < \infty$ for $\sigma > 1$** (a subseries of $\zeta_F(\sigma)$). -/
@[kb "neukirch1999" "Ch. VII §5 [unverified]"]
theorem summable_normP_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun 𝔭 : HeightOneSpectrum (𝓞 F) => (normP 𝔭 : ℝ) ^ (-σ)) :=
  (summable_absNorm_rpow hσ).comp_injective asIdeal_injective

/-- **Absolute convergence of Euler products over $F$** (the number-field form of `Siegel.multipliable_eulerFactor`):
if $|f(\mathfrak p) - 1| \le C\,N\mathfrak p^{-\sigma}$ for all but finitely many $\mathfrak p$, with $\sigma > 1$, then
$\prod_{\mathfrak p} f(\mathfrak p)$ converges unconditionally in $\mathbb{R}$ (`Multipliable`). -/
@[kb "neukirch1999" "Ch. VII §5 [unverified]"]
theorem multipliable_of_abs_sub_one_le (f : HeightOneSpectrum (𝓞 F) → ℝ) {C σ : ℝ} (hσ : 1 < σ)
    (hf : ∀ᶠ 𝔭 in cofinite, |f 𝔭 - 1| ≤ C * (normP 𝔭 : ℝ) ^ (-σ)) : Multipliable f := by
  have hs : Summable fun 𝔭 => f 𝔭 - 1 :=
    Summable.of_norm_bounded_eventually ((summable_normP_rpow hσ).mul_left C)
      (hf.mono fun 𝔭 h => by rw [Real.norm_eq_abs]; exact h)
  simpa using Real.multipliable_one_add_of_summable hs

/-- **A convergent Euler product of nonzero factors is nonzero:** under the hypotheses of
`multipliable_of_abs_sub_one_le`, if every $f(\mathfrak p) \ne 0$ then $\prod_{\mathfrak p} f(\mathfrak p) \ne 0$.

*Proof.* Only finitely many factors satisfy $|f(\mathfrak p) - 1| \ge 1/2$; the product of the others is
$\exp(\sum \log f(\mathfrak p)) > 0$. -/
theorem tprod_ne_zero_of_abs_sub_one_le (f : HeightOneSpectrum (𝓞 F) → ℝ) {C σ : ℝ} (hσ : 1 < σ)
    (hf : ∀ᶠ 𝔭 in cofinite, |f 𝔭 - 1| ≤ C * (normP 𝔭 : ℝ) ^ (-σ)) (hf0 : ∀ 𝔭, f 𝔭 ≠ 0) :
    ∏' 𝔭, f 𝔭 ≠ 0 := by
  classical
  have hs : Summable fun 𝔭 => f 𝔭 - 1 :=
    Summable.of_norm_bounded_eventually ((summable_normP_rpow hσ).mul_left C)
      (hf.mono fun 𝔭 h => by rw [Real.norm_eq_abs]; exact h)
  have hB : {𝔭 | ¬ |f 𝔭 - 1| < 1 / 2}.Finite := by
    have := hs.tendsto_cofinite_zero.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))
    simpa [Real.dist_eq] using this
  set B := hB.toFinset
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun 𝔭 => if 𝔭 ∈ B then 1 else f 𝔭 with hg
  set h : HeightOneSpectrum (𝓞 F) → ℝ := fun 𝔭 => if 𝔭 ∈ B then f 𝔭 else 1 with hh
  have hgpos : ∀ 𝔭, 0 < g 𝔭 := by
    intro 𝔭
    simp only [hg]
    split_ifs with h𝔭
    · exact one_pos
    · have : |f 𝔭 - 1| < 1 / 2 := by
        by_contra hc; exact h𝔭 (hB.mem_toFinset.mpr hc)
      have := (abs_lt.mp this).1; linarith
  have hgs : Summable fun 𝔭 => g 𝔭 - 1 := by
    refine (hs.indicator (Bᶜ : Set _)).congr fun 𝔭 => ?_
    by_cases h𝔭 : 𝔭 ∈ B <;> simp [hg, h𝔭]
  have hglog : Summable fun 𝔭 => Real.log (g 𝔭) := by
    simpa using Real.summable_log_one_add_of_summable hgs
  have hgprod := Real.hasProd_of_hasSum_log hgpos hglog.hasSum
  have hhprod : HasProd h (∏ 𝔭 ∈ B, h 𝔭) :=
    hasProd_prod_of_ne_finset_one fun 𝔭 h𝔭 => by simp [hh, h𝔭]
  have hfg : f = fun 𝔭 => g 𝔭 * h 𝔭 := by
    funext 𝔭; by_cases h𝔭 : 𝔭 ∈ B <;> simp [hg, hh, h𝔭]
  rw [hfg, (hgprod.mul hhprod).tprod_eq]
  refine mul_ne_zero (Real.exp_pos _).ne' (Finset.prod_ne_zero_iff.mpr fun 𝔭 h𝔭 => ?_)
  simp [hh, h𝔭, hf0]

/-! ### The natural order $N\mathfrak p \le X$ -/

theorem finite_normP_le (X : ℕ) : {𝔭 : HeightOneSpectrum (𝓞 F) | normP 𝔭 ≤ X}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le X).preimage asIdeal_injective.injOn

/-- **The primes $\mathfrak p$ with $N\mathfrak p \le X$** (a finite set). -/
def primesNormLe (F : Type) [Field F] [NumberField F] (X : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_normP_le X).toFinset

@[simp] theorem mem_primesNormLe {X : ℕ} {𝔭 : HeightOneSpectrum (𝓞 F)} :
    𝔭 ∈ primesNormLe F X ↔ normP 𝔭 ≤ X := by
  simp [primesNormLe]

/-- $\{N\mathfrak p \le X\}$ exhausts the primes of $F$ as $X \to \infty$. -/
theorem tendsto_primesNormLe : Tendsto (primesNormLe F) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun X Y hXY 𝔭 h => by
    simp only [mem_primesNormLe] at h ⊢; omega) fun 𝔭 => ⟨normP 𝔭, by simp⟩

/-- **Partial Euler products in the natural order:** $\prod_{N\mathfrak p \le X} f(\mathfrak p)$. -/
def eulerPartialProdNF (f : HeightOneSpectrum (𝓞 F) → ℝ) (X : ℕ) : ℝ :=
  ∏ 𝔭 ∈ primesNormLe F X, f 𝔭

/-- **$P$ is the value of $\prod_{\mathfrak p} f(\mathfrak p)$ in the natural order** (the $n = 3$ analogue of
`Siegel.IsEulerProductValue`): $\prod_{N\mathfrak p \le X} f(\mathfrak p) \to P$ as $X \to \infty$ ($X \in \mathbb{N}$).

*Role:* for conditionally convergent products (Hanke 2004, (5.3)–(5.4) with $n = 3$, over $F$). For absolutely
convergent products this agrees with `tprod` (`isEulerProductValueNF_of_hasProd`); the value is unique
(`IsEulerProductValueNF.unique`). -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, over F)"]
def IsEulerProductValueNF (f : HeightOneSpectrum (𝓞 F) → ℝ) (P : ℝ) : Prop :=
  Tendsto (eulerPartialProdNF f) atTop (𝓝 P)

/-- The natural-order value is unique. -/
theorem IsEulerProductValueNF.unique {f : HeightOneSpectrum (𝓞 F) → ℝ} {P Q : ℝ}
    (hP : IsEulerProductValueNF f P) (hQ : IsEulerProductValueNF f Q) : P = Q :=
  tendsto_nhds_unique hP hQ

/-- An unconditionally convergent product has the same value in the natural order. -/
theorem isEulerProductValueNF_of_hasProd {f : HeightOneSpectrum (𝓞 F) → ℝ} {P : ℝ}
    (h : HasProd f P) : IsEulerProductValueNF f P :=
  (show Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ 𝔭 ∈ s, f 𝔭) atTop (𝓝 P) from h).comp
    tendsto_primesNormLe

/-! ### The Euler product of $\zeta_F$ (a sieve) -/

/-- The ideals prime to every $\mathfrak p \in T$ (not contained in any $\mathfrak p \in T$). -/
def coprimeTo (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (Ideal (𝓞 F)) :=
  {I | ∀ v ∈ T, ¬ I ≤ v.asIdeal}

/-- $Z_s(T) = \sum_{\mathfrak a\ \text{prime to}\ T} N\mathfrak a^{-s}$. -/
def sieveSum (s : ℝ) (T : Finset (HeightOneSpectrum (𝓞 F))) : ℝ :=
  ∑' I, (coprimeTo T).indicator (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-s)) I

theorem mul_mem_coprimeTo_iff {T : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)}
    (hp : p ∉ T) (J : Ideal (𝓞 F)) : p.asIdeal * J ∈ coprimeTo T ↔ J ∈ coprimeTo T := by
  constructor
  · intro h v hv hJ
    exact h v hv (le_trans Ideal.mul_le_right hJ)
  · intro h v hv hle
    rcases (Ideal.IsPrime.mul_le v.isPrime).mp hle with hq | hJ
    · have := p.isMaximal.eq_of_le v.isPrime.ne_top hq
      exact hp (HeightOneSpectrum.ext this ▸ hv)
    · exact h v hv hJ

open Classical in
/-- **One sieve step:** for $\mathfrak p \notin T$, $Z_s(T \cup \{\mathfrak p\}) = (1 - N\mathfrak p^{-s})\,Z_s(T)$. -/
theorem sieveSum_insert {s : ℝ} (hs : 1 < s) {T : Finset (HeightOneSpectrum (𝓞 F))}
    {p : HeightOneSpectrum (𝓞 F)} (hp : p ∉ T) :
    sieveSum s (insert p T) = (1 - (normP p : ℝ) ^ (-s)) * sieveSum s T := by
  classical
  set G : Ideal (𝓞 F) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-s) with hG
  have hGs : Summable G := summable_absNorm_rpow hs
  set q := p.asIdeal
  set D : Set (Ideal (𝓞 F)) := {I | I ∈ coprimeTo T ∧ I ≤ q} with hD
  have hsplit : ∀ I, (coprimeTo T).indicator G I =
      (coprimeTo (insert p T)).indicator G I + D.indicator G I := by
    intro I
    by_cases hI : I ∈ coprimeTo T
    · by_cases hIq : I ≤ q
      · have h1 : I ∉ coprimeTo (insert p T) := fun h => h p (Finset.mem_insert_self _ _) hIq
        have h2 : I ∈ D := ⟨hI, hIq⟩
        rw [Set.indicator_of_mem hI, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
      · have h1 : I ∈ coprimeTo (insert p T) := by
          intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hIq
          · exact hI v hv
        have h2 : I ∉ D := fun h => hIq h.2
        rw [Set.indicator_of_mem hI, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · have h1 : I ∉ coprimeTo (insert p T) := fun h => hI fun v hv => h v (Finset.mem_insert_of_mem hv)
      have h2 : I ∉ D := fun h => hI h.1
      rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hD_eq : ∑' I, D.indicator G I = (normP p : ℝ) ^ (-s) * sieveSum s T := by
    have hq0 : q ≠ ⊥ := p.ne_bot
    have hinj : Function.Injective (fun J : Ideal (𝓞 F) => q * J) := fun x y hxy =>
      mul_left_cancel₀ hq0 hxy
    have hsupp : Function.support (D.indicator G) ⊆ Set.range (fun J : Ideal (𝓞 F) => q * J) := by
      intro I hI
      have hmem : I ∈ D := by
        by_contra hn; exact hI (Set.indicator_of_notMem hn _)
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hmem.2
      exact ⟨J, hJ.symm⟩
    rw [← hinj.tsum_eq hsupp, sieveSum, ← tsum_mul_left]
    congr 1
    funext J
    have hiff : q * J ∈ D ↔ J ∈ coprimeTo T := by
      rw [hD, Set.mem_ofPred_eq, mul_mem_coprimeTo_iff hp]
      exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_le_left⟩⟩
    by_cases hJ : J ∈ coprimeTo T
    · rw [Set.indicator_of_mem (hiff.mpr hJ), Set.indicator_of_mem hJ, hG]
      simp only
      rw [map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    · rw [Set.indicator_of_notMem (fun h => hJ (hiff.mp h)), Set.indicator_of_notMem hJ, mul_zero]
  have hsum : sieveSum s T = sieveSum s (insert p T) + ∑' I, D.indicator G I := by
    rw [sieveSum, sieveSum, ← Summable.tsum_add (hGs.indicator _) (hGs.indicator _)]
    exact tsum_congr hsplit
  rw [hD_eq] at hsum
  linarith

theorem sieveSum_empty {s : ℝ} (hs : 1 < s) : sieveSum s (∅ : Finset (HeightOneSpectrum (𝓞 F))) =
    dedekindZetaR F s := by
  rw [← (hasSum_absNorm_rpow hs).tsum_eq, sieveSum]
  congr 1
  funext I
  rw [Set.indicator_of_mem]
  simp [coprimeTo]

/-- $Z_s(T) = \prod_{\mathfrak p \in T}(1 - N\mathfrak p^{-s})\cdot\zeta_F(s)$. -/
theorem sieveSum_eq_prod {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    sieveSum s T = (∏ 𝔭 ∈ T, (1 - (normP 𝔭 : ℝ) ^ (-s))) * dedekindZetaR F s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sieveSum_empty hs]
  | insert p T hp ih => rw [sieveSum_insert hs hp, ih, Finset.prod_insert hp, mul_assoc]

theorem one_le_sieveSum {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    1 ≤ sieveSum s T := by
  have hGs := summable_absNorm_rpow (F := F) hs
  have htop : (⊤ : Ideal (𝓞 F)) ∈ coprimeTo T := fun v _ h => v.isPrime.ne_top (top_le_iff.mp h)
  have := (hGs.indicator (coprimeTo T)).le_tsum ⊤ (fun j _ => Set.indicator_nonneg
    (fun I _ => by positivity) j)
  rw [Set.indicator_of_mem htop] at this
  rw [sieveSum]
  convert this using 1
  simp

/-- $\zeta_F(s) \ge 1$ for real $s > 1$. -/
theorem one_le_dedekindZetaR {s : ℝ} (hs : 1 < s) : 1 ≤ dedekindZetaR F s := by
  rw [← sieveSum_empty hs]; exact one_le_sieveSum hs ∅

/-- If $T$ contains every $\mathfrak p$ with $N\mathfrak p \le X$, then $Z_s(T) \le 1 + \sum_{N\mathfrak a > X} N\mathfrak a^{-s}$:
an ideal $\mathfrak a \ne 0, \mathcal O_F$ prime to $T$ lies in a prime $\mathfrak p \notin T$, so
$N\mathfrak a \ge N\mathfrak p > X$. -/
theorem sieveSum_le {s : ℝ} (hs : 1 < s) (X : ℕ) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hT : primesNormLe F X ⊆ T) :
    sieveSum s T ≤ 1 + ∑' I, {I : Ideal (𝓞 F) | X < Ideal.absNorm I}.indicator
      (fun I => (Ideal.absNorm I : ℝ) ^ (-s)) I := by
  classical
  have hs0 : -s ≠ 0 := by linarith
  set G : Ideal (𝓞 F) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-s) with hG
  have hGs : Summable G := summable_absNorm_rpow hs
  have hδ : ∑' I : Ideal (𝓞 F), (if I = ⊤ then (1 : ℝ) else 0) = 1 := by
    rw [tsum_ite_eq]
  rw [← hδ, ← Summable.tsum_add (summable_of_ne_finset_zero (s := {⊤}) (fun I hI => by
    simp only [Finset.mem_singleton] at hI; simp [hI])) (hGs.indicator _), sieveSum]
  refine Summable.tsum_le_tsum (fun I => ?_) (hGs.indicator _)
    ((summable_of_ne_finset_zero (s := {⊤}) (fun I hI => by
      simp only [Finset.mem_singleton] at hI; simp [hI])).add (hGs.indicator _))
  have hGnn : ∀ J, 0 ≤ G J := fun J => by positivity
  have hind_nn : 0 ≤ {I : Ideal (𝓞 F) | X < Ideal.absNorm I}.indicator G I :=
    Set.indicator_nonneg (fun J _ => hGnn J) I
  by_cases hI : I ∈ coprimeTo T
  · rw [Set.indicator_of_mem hI]
    by_cases htop : I = ⊤
    · subst htop; simp [hG] at hind_nn ⊢; linarith
    · simp only [htop, ↓reduceIte, zero_add]
      by_cases hbot : I = ⊥
      · subst hbot; simp [hG, Real.zero_rpow hs0]
      · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I htop
        have hm0 : m ≠ ⊥ := fun h => hbot (le_bot_iff.mp (h ▸ hIm))
        set v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hm0⟩
        have hvT : v ∉ T := fun h => hI v h hIm
        have hvX : X < normP v := by
          by_contra hc
          exact hvT (hT (mem_primesNormLe.mpr (not_lt.mp hc)))
        have hI0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        have hle : normP v ≤ Ideal.absNorm I :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hI0) (Ideal.absNorm_dvd_absNorm_of_le hIm)
        rw [Set.indicator_of_mem (show I ∈ {I : Ideal (𝓞 F) | X < Ideal.absNorm I} from
          lt_of_lt_of_le hvX hle)]
  · rw [Set.indicator_of_notMem hI]
    have : (0 : ℝ) ≤ if I = ⊤ then 1 else 0 := by split_ifs <;> norm_num
    linarith

/-- $\sum_{N\mathfrak a > X} N\mathfrak a^{-s} \to 0$ as $X \to \infty$. -/
theorem tendsto_tail_absNorm (s : ℝ) :
    Tendsto (fun X : ℕ => ∑' I, {I : Ideal (𝓞 F) | X < Ideal.absNorm I}.indicator
      (fun I => (Ideal.absNorm I : ℝ) ^ (-s)) I) atTop (𝓝 0) := by
  set G : Ideal (𝓞 F) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-s)
  set S : ℕ → Finset (Ideal (𝓞 F)) := fun X => (Ideal.finite_setOfPred_absNorm_le X).toFinset
  have hS : Tendsto S atTop atTop :=
    tendsto_atTop_finset_of_monotone (fun X Y hXY I h => by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h ⊢; omega)
      fun I => ⟨Ideal.absNorm I, by simp [S]⟩
  refine ((tendsto_tsum_compl_atTop_zero G).comp hS).congr fun X => ?_
  simp only [Function.comp_apply]
  have hset : {I : Ideal (𝓞 F) | X < Ideal.absNorm I} = {I | I ∉ S X} := by
    ext I; simp [S]
  rw [← tsum_subtype, hset]
  rfl

/-- $Z_s(T) \to 1$ as $T$ runs through the finite sets of primes. -/
theorem tendsto_sieveSum {s : ℝ} (hs : 1 < s) :
    Tendsto (sieveSum (F := F) s) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun T =>
    lt_of_lt_of_le ha (one_le_sieveSum hs T), fun b hb => ?_⟩
  obtain ⟨X, hX⟩ := ((tendsto_order.1 (tendsto_tail_absNorm (F := F) s)).2 (b - 1)
    (by linarith)).exists
  filter_upwards [eventually_ge_atTop (primesNormLe F X)] with T hT
  have := sieveSum_le hs X hT
  linarith

/-- **The Euler product of $1/\zeta_F$:** $\prod_{\mathfrak p}(1 - N\mathfrak p^{-s}) = \zeta_F(s)^{-1}$ for real $s > 1$. -/
theorem hasProd_one_sub_rpow {s : ℝ} (hs : 1 < s) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 F) => 1 - (normP 𝔭 : ℝ) ^ (-s)) (dedekindZetaR F s)⁻¹ := by
  have hz : 0 < dedekindZetaR F s := lt_of_lt_of_le one_pos (one_le_dedekindZetaR hs)
  have h := (tendsto_sieveSum (F := F) hs).div_const (dedekindZetaR F s)
  rw [one_div] at h
  refine h.congr fun T => ?_
  rw [sieveSum_eq_prod hs, mul_div_assoc, div_self hz.ne', mul_one]

/-- **The Euler product of the Dedekind zeta function**: for real $s > 1$,
$$\zeta_F(s) = \prod_{\mathfrak p}(1 - N\mathfrak p^{-s})^{-1},$$
the product over all nonzero primes of $\mathcal O_F$ converging unconditionally. -/
@[kb "neukirch1999" "Ch. VII §5, Prop. 5.2 [unverified]"]
theorem hasProd_dedekindZeta {s : ℝ} (hs : 1 < s) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 F) => (1 - (normP 𝔭 : ℝ) ^ (-s))⁻¹) (dedekindZetaR F s) := by
  have hz : 0 < dedekindZetaR F s := lt_of_lt_of_le one_pos (one_le_dedekindZetaR hs)
  have h := (hasProd_one_sub_rpow (F := F) hs).inv₀ (inv_ne_zero hz.ne')
  rw [inv_inv] at h
  refine h.congr fun T => ?_
  simp [Finset.prod_inv_distrib]

theorem dedekindZetaR_eq_tprod {s : ℝ} (hs : 1 < s) :
    dedekindZetaR F s = ∏' 𝔭 : HeightOneSpectrum (𝓞 F), (1 - (normP 𝔭 : ℝ) ^ (-s))⁻¹ :=
  (hasProd_dedekindZeta hs).tprod_eq.symm

/-! ### Primes over $p$ -/

/-- **The rational prime $p$ under $\mathfrak p$:** $p\mathbb{Z} = \mathfrak p \cap \mathbb{Z}$ (Mathlib's `Ideal.under`),
$p = |\mathbb{Z}/(\mathfrak p \cap \mathbb{Z})|$. -/
def primeBelow (𝔭 : HeightOneSpectrum (𝓞 F)) : Nat.Primes :=
  ⟨Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal), by
    have : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
    exact Nat.absNorm_under_prime _⟩

/-- $p \in \mathfrak p$ for $p$ = `primeBelow 𝔭`. -/
theorem natCast_primeBelow_mem (𝔭 : HeightOneSpectrum (𝓞 F)) :
    ((primeBelow 𝔭 : ℕ) : 𝓞 F) ∈ 𝔭.asIdeal := by
  have h : algebraMap ℤ (𝓞 F) ((Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal) : ℕ) : ℤ) ∈ 𝔭.asIdeal :=
    Ideal.mem_comap.mp (Ideal.absNorm_mem (Ideal.under ℤ 𝔭.asIdeal))
  rw [map_natCast] at h
  exact h

/-- $N\mathfrak p = p^{f}$ with $f = f(\mathfrak p/p)$ the inertia degree. -/
theorem normP_eq_pow (𝔭 : HeightOneSpectrum (𝓞 F)) :
    normP 𝔭 = (primeBelow 𝔭 : ℕ) ^ 𝔭.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ 𝔭.asIdeal) 𝔭.asIdeal).symm

/-- $p \le N\mathfrak p$. -/
theorem primeBelow_le_normP (𝔭 : HeightOneSpectrum (𝓞 F)) : (primeBelow 𝔭 : ℕ) ≤ normP 𝔭 := by
  have h2 := two_le_normP 𝔭
  rw [normP_eq_pow] at h2 ⊢
  have hf : 𝔭.asIdeal.inertiaDeg ℤ ≠ 0 := by
    intro h0; rw [h0, pow_zero] at h2; omega
  exact Nat.le_self_pow hf _

/-- $N\mathfrak p \le p^d$, $d = [F:\mathbb{Q}]$ (as $N\mathfrak p \mid N(p\mathcal O_F) = p^d$). -/
theorem normP_le_pow_finrank (𝔭 : HeightOneSpectrum (𝓞 F)) :
    normP 𝔭 ≤ (primeBelow 𝔭 : ℕ) ^ Module.finrank ℚ F := by
  have hle : Ideal.span {((primeBelow 𝔭 : ℕ) : 𝓞 F)} ≤ 𝔭.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (natCast_primeBelow_mem 𝔭)
  have h := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h
  exact Nat.le_of_dvd (pow_pos (primeBelow 𝔭).2.pos _) h

/-- **At most $d = [F:\mathbb{Q}]$ primes lie over a rational prime $p$:** distinct primes over $p$ are coprime and
all divide $p\mathcal O_F$, so $p^{\#T} \le \prod_{\mathfrak p \in T} N\mathfrak p \le N(p\mathcal O_F) = p^d$. -/
@[kb "neukirch1999" "Ch. I §8, Prop. 8.2 [unverified]"]
theorem card_le_finrank (p : Nat.Primes) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ 𝔭 ∈ T, primeBelow 𝔭 = p) : T.card ≤ Module.finrank ℚ F := by
  have hdvd : ∏ 𝔭 ∈ T, 𝔭.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ fun 𝔭 h𝔭 => Ideal.dvd_iff_le.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (hT 𝔭 h𝔭 ▸ natCast_primeBelow_mem 𝔭))
    intro a _ b _ hab
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (a.isMaximal.coprime_of_ne b.isMaximal fun h => hab (HeightOneSpectrum.ext h))
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  have h2 : (p : ℕ) ^ T.card ≤ ∏ 𝔭 ∈ T, Ideal.absNorm 𝔭.asIdeal := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun 𝔭 h𝔭 =>
      hT 𝔭 h𝔭 ▸ primeBelow_le_normP 𝔭
  have h3 := Nat.le_of_dvd (pow_pos p.2.pos _) h1
  exact (Nat.pow_le_pow_iff_right p.2.two_le).mp (h2.trans h3)

/-- **Grouping an Euler product by rational primes:** if $u \ge 1$ on $\{n \ge 2\}$ and $u$ is decreasing there,
then for every finite set $T$ of primes of $F$,
$\prod_{\mathfrak p \in T} u(N\mathfrak p) \le \prod_{p \in T|_{\mathbb{Q}}} u(p)^d$ (at most $d$ primes over each $p$, each
with $N\mathfrak p \ge p$; "all primes split completely" is the worst case). -/
theorem prod_le_prod_primeBelow_pow (u : ℕ → ℝ) (hu1 : ∀ n, 2 ≤ n → 1 ≤ u n)
    (hanti : ∀ m n, 2 ≤ m → m ≤ n → u n ≤ u m) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∏ 𝔭 ∈ T, u (normP 𝔭) ≤ ∏ p ∈ T.image primeBelow, u p ^ Module.finrank ℚ F := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (g := primeBelow) (t := T.image primeBelow)
    (fun 𝔭 h => Finset.mem_image_of_mem _ h)]
  have hnn : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), 0 ≤ u (normP 𝔭) := fun 𝔭 =>
    zero_le_one.trans (hu1 _ (two_le_normP 𝔭))
  refine Finset.prod_le_prod₀ (fun p _ => Finset.prod_nonneg fun 𝔭 _ => hnn 𝔭) fun p _ => ?_
  calc ∏ 𝔭 ∈ T with primeBelow 𝔭 = p, u (normP 𝔭)
      ≤ ∏ 𝔭 ∈ T with primeBelow 𝔭 = p, u (p : ℕ) := by
        refine Finset.prod_le_prod₀ (fun 𝔭 _ => hnn 𝔭) fun 𝔭 h𝔭 => ?_
        have he : primeBelow 𝔭 = p := (Finset.mem_filter.mp h𝔭).2
        have h1 : (p : ℕ) ≤ normP 𝔭 := he ▸ primeBelow_le_normP 𝔭
        exact hanti _ _ p.2.two_le h1
    _ = u (p : ℕ) ^ (T.filter fun 𝔭 => primeBelow 𝔭 = p).card := Finset.prod_const _
    _ ≤ u (p : ℕ) ^ Module.finrank ℚ F :=
        pow_le_pow_right₀ (hu1 _ p.2.two_le)
          (card_le_finrank p _ fun 𝔭 h => (Finset.mem_filter.mp h).2)

/-! ### $\zeta_F(s) \le \zeta(s)^d$ -/

/-- **The Riemann zeta function at real $s$**, as a real number $\operatorname{Re}\zeta(s)$. -/
def zetaR (s : ℝ) : ℝ := (riemannZeta s).re

/-- **The real Euler product of $\zeta$:** $\prod_p (1 - p^{-s})^{-1} = \zeta(s)$ for real $s > 1$ (Mathlib's
`riemannZeta_eulerProduct_hasProd`). -/
theorem hasProd_zetaR {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹) (zetaR s) := by
  have h := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have h2 := (Complex.continuous_re.tendsto _).comp h
  refine h2.congr fun T => ?_
  simp only [Function.comp_apply]
  rw [show (∏ p ∈ T, (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))⁻¹) =
      ((∏ p ∈ T, (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ : ℝ) : ℂ) by
    push_cast
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]]
  exact Complex.ofReal_re _

/-- $n^{-s} \in (0, 1/2]$ for $n \ge 2$ and $s \ge 1$. -/
theorem rpow_neg_mem {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 ≤ s) :
    0 < (n : ℝ) ^ (-s) ∧ (n : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  rw [Real.rpow_neg (by positivity), one_div]
  refine inv_anti₀ (by norm_num) ?_
  calc (2 : ℝ) ≤ n := h2
    _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs

/-- $n \mapsto n^{-s}$ is decreasing on $\{n \ge 2\}$ for $s > 0$. -/
theorem rpow_neg_anti {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) {s : ℝ} (hs : 0 < s) :
    (n : ℝ) ^ (-s) ≤ (m : ℝ) ^ (-s) := by
  have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact Real.rpow_le_rpow_of_nonpos this (by exact_mod_cast hmn) (by linarith)

/-- A partial product of an Euler product with factors $\ge 1$ is at most its value. -/
theorem prod_le_of_hasProd {ι : Type*} {g : ι → ℝ} {a : ℝ} (h : HasProd g a) (hg : ∀ i, 1 ≤ g i)
    (T : Finset ι) : ∏ i ∈ T, g i ≤ a := by
  classical
  refine ge_of_tendsto h ((eventually_ge_atTop T).mono fun T' hT' => ?_)
  rw [← Finset.prod_sdiff hT']
  exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ => zero_le_one.trans (hg i))
    (Finset.one_le_prod₀ fun i _ => hg i)

theorem one_le_inv_one_sub_rpow {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 1 ≤ s) :
    1 ≤ (1 - (n : ℝ) ^ (-s))⁻¹ := by
  obtain ⟨h0, h1⟩ := rpow_neg_mem hn hs
  exact (one_le_inv₀ (by linarith)).2 (by linarith)

/-- $\zeta(s) \ge 1$ for real $s > 1$. -/
theorem one_le_zetaR {s : ℝ} (hs : 1 < s) : 1 ≤ zetaR s := by
  simpa using prod_le_of_hasProd (hasProd_zetaR hs)
    (fun p => one_le_inv_one_sub_rpow p.2.two_le hs.le) ∅

/-- **Finite Euler products of $\zeta_F$ are bounded by $\zeta(s)^d$:** for every finite set $T$ of primes of $F$
and real $s > 1$, $\prod_{\mathfrak p \in T}(1 - N\mathfrak p^{-s})^{-1} \le \zeta(s)^d$. -/
theorem prod_inv_one_sub_le_zetaR_pow {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∏ 𝔭 ∈ T, (1 - (normP 𝔭 : ℝ) ^ (-s))⁻¹ ≤ zetaR s ^ Module.finrank ℚ F := by
  have hu1 : ∀ n : ℕ, 2 ≤ n → 1 ≤ (1 - (n : ℝ) ^ (-s))⁻¹ := fun n hn =>
    one_le_inv_one_sub_rpow hn hs.le
  have hanti : ∀ m n : ℕ, 2 ≤ m → m ≤ n → (1 - (n : ℝ) ^ (-s))⁻¹ ≤ (1 - (m : ℝ) ^ (-s))⁻¹ := by
    intro m n hm hmn
    have h1 := rpow_neg_anti hm hmn (by linarith : (0 : ℝ) < s)
    have h2 := (rpow_neg_mem hm hs.le).2
    exact inv_anti₀ (by linarith) (by linarith)
  refine (prod_le_prod_primeBelow_pow (fun n : ℕ => (1 - (n : ℝ) ^ (-s))⁻¹) hu1 hanti T).trans ?_
  rw [Finset.prod_pow]
  exact pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => zero_le_one.trans (hu1 _ p.2.two_le))
    (prod_le_of_hasProd (hasProd_zetaR hs) (fun p => hu1 _ p.2.two_le) _) _

/-- **$\zeta_F(s) \le \zeta(s)^d$** for real $s > 1$, $d = [F:\mathbb{Q}]$. -/
@[kb "hanke2004" "Thm 5.7 proof, p. 375 (ζ_F(s) ≤ ζ(s)^d) [unverified]"]
theorem dedekindZetaR_le_zetaR_pow {s : ℝ} (hs : 1 < s) :
    dedekindZetaR F s ≤ zetaR s ^ Module.finrank ℚ F :=
  le_of_tendsto' (hasProd_dedekindZeta hs) (prod_inv_one_sub_le_zetaR_pow hs)

/-- **$\prod_{\mathfrak p \in T}(1 - N\mathfrak p^{-s}) \ge \zeta(s)^{-d}$** for every finite set $T$ of primes. -/
theorem zetaR_pow_inv_le_prod {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (zetaR s ^ Module.finrank ℚ F)⁻¹ ≤ ∏ 𝔭 ∈ T, (1 - (normP 𝔭 : ℝ) ^ (-s)) := by
  have hpos : 0 < ∏ 𝔭 ∈ T, (1 - (normP 𝔭 : ℝ) ^ (-s)) := Finset.prod_pos fun 𝔭 _ => by
    have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).2; linarith
  have h := prod_inv_one_sub_le_zetaR_pow hs T
  rw [Finset.prod_inv_distrib] at h
  rw [inv_le_comm₀ (pow_pos (lt_of_lt_of_le one_pos (one_le_zetaR hs)) _) hpos]
  exact h

/-- $\zeta(2) = \pi^2/6$ (Mathlib's `riemannZeta_two`). -/
theorem zetaR_two : zetaR 2 = Real.pi ^ 2 / 6 := by
  rw [zetaR, show ((2 : ℝ) : ℂ) = 2 by norm_num, riemannZeta_two,
    show ((Real.pi : ℂ) ^ 2 / 6) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **$\prod_{\mathfrak p \in S}(1 - N\mathfrak p^{-2}) \ge (6/\pi^2)^d$** for every finite set $S$ of primes of $F$
(the number-field form of `Siegel.six_div_pi_sq_le_prod`, used in Hanke 2004 Thm 5.7(b) over $F$). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (1/ζ_F(2) ≥ ζ(2)^{-d}) [unverified]"]
theorem six_div_pi_sq_pow_le_prod (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F ≤ ∏ 𝔭 ∈ S, (1 - (normP 𝔭 : ℝ) ^ (-(2 : ℝ))) := by
  have h := zetaR_pow_inv_le_prod (s := 2) (by norm_num) S
  rw [zetaR_two, ← inv_pow, inv_div] at h
  exact h

/-- **$\zeta_F(2)^{-1} = \prod_{\mathfrak p}(1 - N\mathfrak p^{-2}) \ge (6/\pi^2)^d$.** -/
theorem six_div_pi_sq_pow_le_inv_dedekindZetaR :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F ≤ (dedekindZetaR F 2)⁻¹ :=
  ge_of_tendsto' (hasProd_one_sub_rpow (F := F) (by norm_num : (1 : ℝ) < 2))
    six_div_pi_sq_pow_le_prod

end

end QuadFormsKB.NFEuler
