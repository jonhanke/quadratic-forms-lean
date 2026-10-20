import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.KroneckerChar
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# $\zeta_K(s) = \zeta(s)\,L(s, \chi_D)$ for a quadratic field

Let $D \ne 1$ be a fundamental discriminant, $K = K_D = \mathbb{Q}(\sqrt D)$ (`QField D`) and $\chi_D$ the Kronecker
character (`kroneckerChar D`). The proof is **local**, an Euler factor at each rational prime $p$:

1. **Splitting of $p$ (Dedekind–Kummer).** $\mathcal O_K = \mathbb{Z}[\theta]$ with $\theta = (b_D + \sqrt D)/2$ of minimal
   polynomial $f_D = X^2 - b_D X - a_D$ (`QuadraticField.lean`), so for *every* $p$ (including $p = 2$) the primes of
   $K$ over $p$ correspond to the distinct monic irreducible factors $Q$ of $f_D \bmod p$, with $N\mathfrak p = p^{\deg Q}$
   (Mathlib's `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`). The factorization shape of $f_D \bmod p$ is read
   off from its number of roots (`prod_normalizedFactors`), and that number is $1 + \chi_D(p)$
   (`kroneckerChar_prime`). Hence (`localFactor_eq`)
   $$\prod_{\mathfrak p \mid p}(1 - N\mathfrak p^{-s})^{-1} = (1 - p^{-s})^{-1}(1 - \chi_D(p)p^{-s})^{-1}:$$
   $p$ splits ($\chi_D(p) = 1$), is inert ($-1$) or ramifies ($0$).
2. **Euler products.** Regrouping the Euler product of $\zeta_K$ (`NFEuler.hasProd_dedekindZeta`) by rational primes
   and comparing with Mathlib's Euler products of $\zeta$ and $L(s, \chi_D)$ gives
   $\zeta_K(s) = \zeta(s)L(s,\chi_D)$ for real $s > 1$ (`dedekindZeta_eq_mul_real`).
3. **Ideal counts.** Comparing Dirichlet coefficients (Mathlib's `LSeries.eq_of_LSeries_eventually_eq`):
   $\#\{\mathfrak a \subseteq \mathcal O_K : N\mathfrak a = m\} = \sum_{d \mid m}\chi_D(d)$ for $m \ge 1$
   (`card_ideals_absNorm_eq`), and then $\zeta_K(s) = \zeta(s)L(s, \chi_D)$ for all complex $s$ with
   $\operatorname{Re}s > 1$ (`dedekindZeta_eq_mul`).

Sources: Davenport, *Multiplicative Number Theory*, Ch. 6 (Dirichlet's class number formula, the factorization
$\zeta_K = \zeta L$); Zagier, *Zetafunktionen und quadratische Körper*, §11; Marcus, *Number Fields*, Ch. 3 Thm. 25
(splitting in quadratic fields) and Ch. 7; Cohen, *A Course in Computational Algebraic Number Theory*, §5.3.
-/

open Polynomial UniqueFactorizationMonoid NumberField IsDedekindDomain QuadFormsKB.NFEuler Filter
open scoped LSeries.notation

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

variable {D : ℤ}

/-! ### The factorization shape of $f_D \bmod p$ -/

/-- $f_D \bmod p$. -/
noncomputable def qpolyMod (D : ℤ) (p : ℕ) : (ZMod p)[X] := (qpoly D).map (Int.castRingHom (ZMod p))

theorem qpolyMod_eq (p : ℕ) :
    qpolyMod D p = X ^ 2 - C ((qb D : ZMod p)) * X - C ((qa D : ZMod p)) := by
  simp [qpolyMod, qpoly, Polynomial.map_sub, Polynomial.map_mul]

theorem qpolyMod_monic (p : ℕ) [Fact p.Prime] : (qpolyMod D p).Monic := qpoly_monic.map _

theorem qpolyMod_natDegree (p : ℕ) [Fact p.Prime] : (qpolyMod D p).natDegree = 2 := by
  rw [qpolyMod_eq]; compute_degree!

theorem isRoot_qpolyMod (p : ℕ) (x : ZMod p) :
    (qpolyMod D p).IsRoot x ↔ x ^ 2 = (qa D : ZMod p) + (qb D : ZMod p) * x := by
  rw [qpolyMod_eq, IsRoot, eval_sub, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_C, sub_sub,
    sub_eq_zero]
  constructor <;> intro h <;> linear_combination h

/-- **The shape of $f_D \bmod p$.** Writing $r$ for the number of roots of $f_D$ in $\mathbb{F}_p$, the multiset of
degrees of the distinct monic irreducible factors of $f_D \bmod p$ is $\{2\}$, $\{1\}$, $\{1, 1\}$ for $r = 0, 1, 2$;
in product form, for every $h : \mathbb{N} \to \mathbb{R}$. -/
theorem prod_normalizedFactors (p : ℕ) [Fact p.Prime] (h : ℕ → ℝ) :
    (rootCount D p = 0 ∧ ∏ Q ∈ (normalizedFactors (qpolyMod D p)).toFinset, h (p ^ Q.natDegree) = h (p ^ 2)) ∨
    (rootCount D p = 1 ∧ ∏ Q ∈ (normalizedFactors (qpolyMod D p)).toFinset, h (p ^ Q.natDegree) = h p) ∨
    (rootCount D p = 2 ∧ ∏ Q ∈ (normalizedFactors (qpolyMod D p)).toFinset, h (p ^ Q.natDegree) =
      h p * h p) := by
  classical
  set f := qpolyMod D p with hf
  have hroots : (Finset.univ.filter fun x : ZMod p => x ^ 2 = (qa D : ZMod p) + (qb D : ZMod p) * x) =
      Finset.univ.filter fun x => f.IsRoot x := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (isRoot_qpolyMod p x).symm
  by_cases hr : ∃ r, f.IsRoot r
  · obtain ⟨r, hr⟩ := hr
    set r' := (qb D : ZMod p) - r
    have hr2 := (isRoot_qpolyMod p r).mp hr
    have hfac : f = (X - C r) * (X - C r') := by
      rw [hf, qpolyMod_eq]
      simp only [r', C_sub]
      have : C ((qa D : ZMod p)) = C (r ^ 2 - (qb D : ZMod p) * r) := by rw [hr2]; ring_nf
      rw [this]; simp only [C_sub, C_mul, C_pow]; ring
    have hX : ∀ c : ZMod p, normalizedFactors (X - C c) = {X - C c} := fun c => by
      rw [normalizedFactors_irreducible (irreducible_X_sub_C c), (monic_X_sub_C c).normalize_eq_self]
    have hnf : normalizedFactors f = {X - C r, X - C r'} := by
      rw [hfac, normalizedFactors_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero r'), hX, hX]; rfl
    have hroot_iff : ∀ x, f.IsRoot x ↔ x = r ∨ x = r' := by
      intro x; rw [hfac, IsRoot, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, mul_eq_zero,
        sub_eq_zero, sub_eq_zero]
    have hR : (Finset.univ.filter fun x => f.IsRoot x) = {r, r'} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      exact hroot_iff x
    by_cases hne : r = r'
    · right; left
      refine ⟨by rw [rootCount, hroots, hR, hne]; simp, ?_⟩
      rw [hnf, hne]; simp
    · right; right
      refine ⟨by rw [rootCount, hroots, hR, Finset.card_pair hne], ?_⟩
      rw [hnf]
      have : (X - C r : (ZMod p)[X]) ≠ X - C r' := fun h => hne (by simpa using congrArg (eval 0) h)
      simp [Finset.prod_pair this]
  · simp only [not_exists] at hr
    left
    refine ⟨by rw [rootCount, hroots, Finset.filter_false_of_mem (fun x _ => hr x), Finset.card_empty], ?_⟩
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [qpolyMod_natDegree]; simp) hr
    rw [normalizedFactors_irreducible hirr, (qpolyMod_monic p).normalize_eq_self]
    simp [qpolyMod_natDegree]

/-! ### Primes over $p$ -/

section General

variable {F : Type} [Field F] [NumberField F]

theorem span_absNorm_under (𝔭 : HeightOneSpectrum (𝓞 F)) :
    Ideal.span {((primeBelow 𝔭 : ℕ) : ℤ)} = Ideal.under ℤ 𝔭.asIdeal := by
  have := Ideal.span_singleton_absNorm (S := ℤ) (I := Ideal.under ℤ 𝔭.asIdeal) (primeBelow 𝔭).2
  rw [Algebra.algebraMap_self, Ideal.comap_id] at this
  exact this

theorem absNorm_span_prime (p : ℕ) : Ideal.absNorm (Ideal.span {(p : ℤ)}) = p := by
  have := Ideal.absNorm_span_natCast (S := ℤ) p
  rwa [Module.finrank_self, pow_one] at this

/-- **Primes of $F$ over $p$**, two ways: the nonzero primes $\mathfrak p$ (`HeightOneSpectrum`) with
`primeBelow 𝔭 = p`, and Mathlib's `Ideal.primesOver (pℤ) 𝒪_F`. -/
noncomputable def fiberEquiv (p : Nat.Primes) :
    {𝔭 : HeightOneSpectrum (𝓞 F) // primeBelow 𝔭 = p} ≃
      (Ideal.span {((p : ℕ) : ℤ)}).primesOver (𝓞 F) where
  toFun 𝔭 := ⟨𝔭.1.asIdeal, 𝔭.1.isPrime, ⟨by have h := span_absNorm_under 𝔭.1; rwa [𝔭.2] at h⟩⟩
  invFun P := ⟨⟨P.1, P.2.1, by
      intro h
      have h1 := P.2.2.over
      rw [h, Ideal.under_bot, Ideal.span_singleton_eq_bot] at h1
      exact p.2.ne_zero (by exact_mod_cast h1)⟩, by
      apply Subtype.ext
      simp only [primeBelow]
      rw [← P.2.2.over, absNorm_span_prime]⟩
  left_inv 𝔭 := by ext; rfl
  right_inv P := by ext; rfl

end General

/-! ### The local factors of $\zeta_{K_D}$ -/

section Quadratic

variable [IsQuadDisc D]

instance instFactPrimesPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem exponent_theta : RingOfIntegers.exponent (theta D) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr adjoin_theta

theorem not_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ p ∣ RingOfIntegers.exponent (theta D) := by
  rw [exponent_theta]; exact hp.out.not_dvd_one

theorem monicFactorsMod_eq (p : ℕ) [Fact p.Prime] :
    RingOfIntegers.monicFactorsMod (theta D) p = (normalizedFactors (qpolyMod D p)).toFinset := by
  rw [RingOfIntegers.monicFactorsMod, minpoly_theta]; rfl

/-- The primes of $K_D$ over $p$ ↔ the distinct monic irreducible factors of $f_D \bmod p$ (Dedekind–Kummer). -/
noncomputable def fiberEquivFactors (p : Nat.Primes) :
    {𝔭 : HeightOneSpectrum (𝓞 (QField D)) // primeBelow 𝔭 = p} ≃
      RingOfIntegers.monicFactorsMod (theta D) (p : ℕ) :=
  (fiberEquiv p).trans (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent (p : ℕ)))

noncomputable instance (p : Nat.Primes) :
    Fintype {𝔭 : HeightOneSpectrum (𝓞 (QField D)) // primeBelow 𝔭 = p} :=
  Fintype.ofEquiv _ (fiberEquivFactors p).symm

/-- $N\mathfrak p = p^{\deg Q}$ for the prime $\mathfrak p$ attached to the factor $Q$. -/
theorem normP_fiberEquivFactors_symm (p : Nat.Primes) (Q : RingOfIntegers.monicFactorsMod (theta D) (p : ℕ)) :
    normP ((fiberEquivFactors p).symm Q).1 = (p : ℕ) ^ (Q : (ZMod (p : ℕ))[X]).natDegree := by
  set P := (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent (D := D) (p : ℕ))).symm Q
  have hP : ((fiberEquivFactors p).symm Q).1.asIdeal = (P : Ideal (𝓞 (QField D))) := rfl
  have hdeg := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (not_dvd_exponent (D := D) (p : ℕ)) Q.2
  have : (P : Ideal (𝓞 (QField D))).IsPrime := P.2.1
  have : (P : Ideal (𝓞 (QField D))).LiesOver (Ideal.span {((p : ℕ) : ℤ)}) := P.2.2
  have hn := Ideal.absNorm_pow_inertiaDeg (Ideal.span {((p : ℕ) : ℤ)}) (P : Ideal (𝓞 (QField D)))
  rw [normP, hP, ← hn, absNorm_span_prime, hdeg]

/-- **The fibre product over the primes of $K_D$ above $p$**, for any function $h$ of the norm:
$\prod_{\mathfrak p \mid p} h(N\mathfrak p) = \prod_{Q} h(p^{\deg Q})$, $Q$ over the monic irreducible factors of
$f_D \bmod p$. -/
theorem prod_fiber (p : Nat.Primes) (h : ℕ → ℝ) :
    ∏ 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 (QField D)) // primeBelow 𝔭 = p}, h (normP 𝔭.1) =
      ∏ Q ∈ (normalizedFactors (qpolyMod D p)).toFinset, h ((p : ℕ) ^ Q.natDegree) := by
  rw [← Equiv.prod_comp (fiberEquivFactors p).symm]
  simp_rw [normP_fiberEquivFactors_symm]
  rw [Finset.prod_coe_sort_eq_attach]
  rw [Finset.prod_attach (RingOfIntegers.monicFactorsMod (theta D) (p : ℕ))
    (fun Q => h ((p : ℕ) ^ Q.natDegree)), monicFactorsMod_eq]

/-- **The local factor identity** (the Euler factor at $p$, including $p = 2$): with
$\chi_D(p) = \#\{\text{roots of } f_D \bmod p\} - 1$ (`kroneckerChar_prime`),
$$\prod_{\mathfrak p \mid p}(1 - N\mathfrak p^{-s})^{-1} = (1 - p^{-s})^{-1}\,(1 - \chi_D(p)\,p^{-s})^{-1}.$$
($p$ splits into two primes of norm $p$ when $\chi_D(p) = 1$, is inert with norm $p^2$ when $\chi_D(p) = -1$, and
ramifies, one prime of norm $p$, when $\chi_D(p) = 0$.) -/
@[kb "marcus1977" "Ch. 3, Thm. 25; Ch. 7"]
theorem localFactor_eq (p : Nat.Primes) (s : ℝ) :
    ∏ 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 (QField D)) // primeBelow 𝔭 = p}, (1 - (normP 𝔭.1 : ℝ) ^ (-s))⁻¹ =
      (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ * (1 - ((rootCount D p : ℝ) - 1) * ((p : ℕ) : ℝ) ^ (-s))⁻¹ := by
  rw [prod_fiber p (fun n => (1 - (n : ℝ) ^ (-s))⁻¹)]
  set x := ((p : ℕ) : ℝ) ^ (-s)
  rcases prod_normalizedFactors (D := D) (p : ℕ) (fun n => (1 - (n : ℝ) ^ (-s))⁻¹) with
    ⟨hr, hprod⟩ | ⟨hr, hprod⟩ | ⟨hr, hprod⟩ <;> rw [hprod, hr]
  · have : (((p : ℕ) ^ 2 : ℕ) : ℝ) ^ (-s) = x ^ 2 := by
      push_cast; rw [Real.rpow_pow_comm (Nat.cast_nonneg _)]
    simp only [this, ← mul_inv]; congr 1; push_cast; ring
  · simp [x]
  · simp only [← mul_inv]; congr 1; push_cast; ring

/-- $\chi_D(p) \in \mathbb{R}$: $\chi_D(p) = \#\{\text{roots}\} - 1$. -/
theorem kroneckerChar_prime' (p : Nat.Primes) :
    kroneckerChar D ((p : ℕ) : ZMod D.natAbs) = (((rootCount D p : ℝ) - 1 : ℝ) : ℂ) := by
  rw [kroneckerChar_prime]; push_cast; rfl

theorem cpow_neg_eq (n : ℕ) (s : ℝ) : (n : ℂ) ^ (-(s : ℂ)) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]; push_cast; rfl

/-- **The factorization $\zeta_K(s) = \zeta(s)\,L(s, \chi_D)$ for real $s > 1$**, via Euler products: group the Euler
product of $\zeta_K$ by rational primes and use `localFactor_eq` at each $p$. -/
@[kb "davenport2000" "Ch. 6"]
theorem dedekindZetaR_eq_mul {s : ℝ} (hs : 1 < s) :
    ((dedekindZetaR (QField D) s : ℝ) : ℂ) =
      riemannZeta s * LSeries (fun n : ℕ => kroneckerChar D n) s := by
  have h0 := hasProd_dedekindZeta (F := QField D) hs
  have h1 := h0.map Complex.ofRealHom Complex.continuous_ofReal
  let e := Equiv.sigmaFiberEquiv (primeBelow (F := QField D))
  have h2 := (e.hasProd_iff).mpr h1
  have h3 := h2.sigma (fun p => hasProd_fintype _)
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have h4 := (riemannZeta_eulerProduct_hasProd hs').mul
    ((kroneckerChar D).LSeries_eulerProduct_hasProd hs')
  refine h3.unique (h4.congr_fun ?_)
  intro p
  simp only [Function.comp_apply, e, Equiv.sigmaFiberEquiv_apply, Complex.ofRealHom_eq_coe]
  rw [← Complex.ofReal_prod, localFactor_eq, kroneckerChar_prime', cpow_neg_eq]
  push_cast; rfl

end Quadratic

/-! ### Ideal counts and the factorization for complex $s$ -/

section General
variable {F : Type} [Field F] [NumberField F]

/-- For real $s > 1$ the Dedekind zeta value is real: $\zeta_F(s) = \operatorname{Re}\zeta_F(s)$. -/
theorem dedekindZeta_ofReal {s : ℝ} (hs : 1 < s) : dedekindZeta F s = ((dedekindZetaR F s : ℝ) : ℂ) := by
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
  have hz : dedekindZeta F s = ((∑' n : ℕ, a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [dedekindZeta, LSeries]
    simp_rw [hterm]
    rw [Complex.ofReal_tsum]
  rw [dedekindZetaR, hz, Complex.ofReal_re]

/-- The Dirichlet series of $\zeta_F$ converges absolutely somewhere. -/
theorem abscissa_dedekindZeta_lt_top :
    LSeries.abscissaOfAbsConv (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) < ⊤ := by
  have := (lSeriesSummable_dedekindZeta (F := F) (s := 2) (by norm_num)).abscissaOfAbsConv_le
  exact this.trans_lt (by simp)

end General

variable [IsQuadDisc D]

/-- The Dirichlet coefficients $\sum_{d \mid m}\chi_D(d)$ of $\zeta(s)L(s,\chi_D)$, as the Dirichlet convolution
$1 \ast \chi_D$. -/
theorem convolution_one_kronecker (m : ℕ) :
    ((1 : ℕ → ℂ) ⍟ (fun n : ℕ => kroneckerChar D n)) m = ∑ d ∈ m.divisors, kroneckerChar D d := by
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, one_mul]
  exact Nat.sum_divisorsAntidiagonal' (fun _ b => kroneckerChar D b)

theorem LSeries_one_conv {s : ℂ} (hs : 1 < s.re) :
    LSeries ((1 : ℕ → ℂ) ⍟ (fun n : ℕ => kroneckerChar D n)) s =
      riemannZeta s * LSeries (fun n : ℕ => kroneckerChar D n) s := by
  rw [LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    ((kroneckerChar D).LSeriesSummable_of_one_lt_re hs), LSeries_one_eq_riemannZeta hs]

/-- **Ideal counts in a quadratic field:** for every $m \ge 1$,
$$\#\{\mathfrak a \subseteq \mathcal O_{K_D} : N\mathfrak a = m\} = \sum_{d \mid m}\chi_D(d).$$
(Compare Dirichlet coefficients of $\zeta_K(s) = \zeta(s)L(s,\chi_D)$, which holds for real $s > 1$ by
`dedekindZetaR_eq_mul`.) This is the input to Dirichlet's representation-number formula. -/
@[kb "zagier1981" "§11, Satz 1 [unverified locator]"]
theorem card_ideals_absNorm_eq {m : ℕ} (hm : m ≠ 0) :
    (Nat.card {I : Ideal (𝓞 (QField D)) // Ideal.absNorm I = m} : ℂ) =
      ∑ d ∈ m.divisors, kroneckerChar D d := by
  rw [← convolution_one_kronecker]
  refine LSeries.eq_of_LSeries_eventually_eq abscissa_dedekindZeta_lt_top ?_ ?_ hm
  · have := (LSeriesSummable.convolution ((LSeriesSummable_one_iff (s := 2)).mpr (by norm_num))
      ((kroneckerChar D).LSeriesSummable_of_one_lt_re (s := 2) (by norm_num))).abscissaOfAbsConv_le
    exact this.trans_lt (by simp)
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    rw [LSeries_one_conv hx', ← dedekindZetaR_eq_mul hx, ← dedekindZeta_ofReal hx]
    rfl

/-- **Ideal counts, integer form:** $\#\{\mathfrak a : N\mathfrak a = m\} = \sum_{d \mid m}\chi_D(d)$ in $\mathbb{Z}$,
with $\chi_D$ the integer-valued `kronZ D`. -/
theorem card_ideals_absNorm_eq_int {m : ℕ} (hm : m ≠ 0) :
    (Nat.card {I : Ideal (𝓞 (QField D)) // Ideal.absNorm I = m} : ℤ) =
      ∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) := by
  have h := card_ideals_absNorm_eq (D := D) hm
  simp only [kroneckerChar_apply] at h
  exact_mod_cast h

/-- **$\zeta_K(s) = \zeta(s)\,L(s, \chi_D)$ for every complex $s$ with $\operatorname{Re}s > 1$** (both sides are
Dirichlet series with the same coefficients, `card_ideals_absNorm_eq`). -/
@[kb "davenport2000" "Ch. 6"]
theorem dedekindZeta_eq_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (QField D) s = riemannZeta s * LSeries (fun n : ℕ => kroneckerChar D n) s := by
  rw [← LSeries_one_conv hs, dedekindZeta]
  exact LSeries_congr (fun hn => card_ideals_absNorm_eq hn |>.trans (convolution_one_kronecker _).symm) s

end QuadFormsKB.Binary
