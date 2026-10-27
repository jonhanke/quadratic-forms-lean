/-
# The main term over a totally real field $F$: $a_E$, Theorem 5.4, (5.13), Theorem 5.7(a)

**Layer:** number field. $F$ is a number field (totally real where the archimedean side needs it), $Q$ =
`QuadForm (𝓞 F) n`, $\mathfrak p$ = `v : HeightOneSpectrum (𝓞 F)`, $N\mathfrak p$ = `Ideal.absNorm v.asIdeal`, and
$\beta_\mathfrak p$ = `LocalDensity.NF.localDensity v Q` (defined over $\mathcal O_F$, equal to the density at the
completion $\mathfrak o_\mathfrak p$). This is the number-field form of `Siegel/LocalProduct.lean` and
`Siegel/MainTerm.lean` (the paper's §5 is stated over $F$; the $\mathbb{Q}$ files are its $F = \mathbb{Q}$ case).

The archimedean density is a product over the real places $w$ of $F$ (`RealPlace F`), each a (5.5)-type factor
$\beta_w(m) = \frac{n\omega_n}{2}D_w^{-1/2}\sigma_w(m)^{(n-2)/2}$ with the local determinant $D_w = \det(\sigma_w(H)/2)$
(`betaInfAt`, `betaInfNF`; $N_{F_w/\mathbb{R}}$ is the identity at a real place). The local side of Siegel's formula is
$a_E(m) = \beta_\infty(m)\prod_\mathfrak p\beta_\mathfrak p(m)$ (`aEWithNF` with an explicit Euler-product value; `aENF` with
`tprod`, for $n \ge 4$). For $m = T'x^2$ ($x \in \mathcal O_F \setminus 0$, $\nu_\mathfrak p = \mathrm{ord}_\mathfrak p(x)$, `ordNF`):
* $\beta_\mathfrak p(T'x^2) = \beta_\mathfrak p(\varpi^{2\nu_\mathfrak p}T')$ at every $\mathfrak p$ (`localDensityNF_mul_sq`);
* $\beta_\infty(T'x^2) = \beta_\infty(T')\,N(x)^{n-2}$ for $F$ totally real and $T'$ totally nonnegative
  (`betaInfNF_mul_sq_norm`), with $N(x) = N((x)) = \prod_\mathfrak p N\mathfrak p^{\nu_\mathfrak p}$ (`absNorm_span_eq_prod`);
* hence the **ratio identity** $a_E(T'x^2) = a_E(T')\prod_{\mathfrak p \mid x}F_\mathfrak p$, $F_\mathfrak p =
  N\mathfrak p^{(n-2)\nu_\mathfrak p}\beta_\mathfrak p(\varpi^{2\nu_\mathfrak p}T')/\beta_\mathfrak p(T')$ (`aEWithNF_mul_sq`, `aENF_mul_sq`), and
  **Theorem 5.4** over $F$ (`thm_5_4_NF`, `thm_5_4_aENF`, uniform form `aEWithNF_mul_sq_eq_localConst`).

(5.13) (`eq_5_13_NF`, `eq_5_13_aENF`) and the first part of Theorem 5.7(a) (`thm_5_7_a_NF`).

**The good-prime hypothesis.** Absolute convergence for $n \ge 4$ and the values $C'_\mathfrak p = 1$ at good $\mathfrak p$ need
the local shape of $Q$ at $\mathfrak p \nmid 2\det H$: the counts of a unit diagonal form (`GoodPrimeShape`, the
number-field form of `exists_diag_unimodular_same_counts_det`). This is
taken here as an explicit hypothesis `hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v`
(see `goodPrimeShape_of_isGoodPrimeNF` in `NFGoodPrime.lean`).
Dyadic $\mathfrak p$ are bad (as $p = 2$ over $\mathbb{Q}$).

**Consistency over $\mathbb{Q}$.** `betaInfNF_rat`, `aEWithNF_rat` (with `LocalDensity.NF.localDensity_rat`): for an
integral form viewed over $\mathcal O_\mathbb{Q}$ the archimedean density and the local factors are the rational ones.

**$n = 3$.** Statements valid for $n = 3$ use `aEWithNF Q m P` with natural-order Euler-product values
(`NFEuler.IsEulerProductValueNF`, ordered by $N\mathfrak p$); `tprod` is used only for $n \ge 4$.
-/
import QuadFormsKB.Siegel.MainTerm
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.Analysis.NFLFunctions

open NumberField IsDedekindDomain Filter Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Matrix Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-! ### Real places and the archimedean density -/

/-- **The real places of $F$** (real infinite places, Mathlib's `InfinitePlace.IsReal`). -/
abbrev RealPlace (F : Type) [Field F] [NumberField F] := {w : InfinitePlace F // w.IsReal}

/-- **The real embedding $\sigma_w : F \to \mathbb{R}$** of a real place $w$. -/
def realEmb (w : RealPlace F) : F →+* ℝ := InfinitePlace.embedding_of_isReal w.2

/-- $|\sigma_w(x)| = w(x)$. -/
theorem abs_realEmb (w : RealPlace F) (x : F) : |realEmb w x| = w.1 x := by
  rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal w.2 x

/-- **The real form $\sigma_w(Q)$** at a real place $w$ (coefficients mapped by $\mathcal O_F \to F \to \mathbb{R}$). -/
def realForm (Q : QuadForm (𝓞 F) n) (w : RealPlace F) : QuadForm ℝ n :=
  Q.map ((realEmb w).comp (algebraMap (𝓞 F) F))

/-- **The local determinant $D_w$** (Hanke 2004, (5.5), p. 369, at the real place $w$): $D_w = \det(H_w/2) =
\det H_w / 2^n$, $H_w$ the Hessian of $\sigma_w(Q)$ (the Gram-matrix convention of `gramDet`). -/
@[kb "hanke2004" "(5.5), p. 369 (D at a real place)"]
def gramDetNF (Q : QuadForm (𝓞 F) n) (w : RealPlace F) : ℝ := (realForm Q w).hessian.det / 2 ^ n

/-- **The archimedean local density at a real place** (Hanke 2004, (5.5), p. 369):
$\beta_w(m) = \frac{n\,\omega_n\,D_w^{-1/2}}{2}\,\sigma_w(m)^{(n-2)/2}$ (as `betaInf`, with $D_w$ = `gramDetNF` and $m$
replaced by $\sigma_w(m)$; $N_{F_w/\mathbb{R}}$ is the identity). -/
@[kb "hanke2004" "(5.5), p. 369 (at a real place)"]
def betaInfAt (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (m : F) : ℝ :=
  n * unitBallVol n * gramDetNF Q w ^ (-(1 / 2 : ℝ)) / 2 * realEmb w m ^ (((n : ℝ) - 2) / 2)

/-- **The archimedean density over $F$** (Hanke 2004, (5.3) and (5.5), pp. 368–369): $\beta_\infty(m) =
\prod_{w\ \text{real}}\beta_w(m)$. For $F$ totally real (the paper's setting) these are all the infinite places. -/
@[kb "hanke2004" "(5.3), (5.5), pp. 368–369 (over F)"]
def betaInfNF (Q : QuadForm (𝓞 F) n) (m : F) : ℝ := ∏ w : RealPlace F, betaInfAt Q w m

/-- **(5.5) along a square class at one real place:** $\beta_w(T'x^2) = \beta_w(T')\,w(x)^{n-2}$ for $\sigma_w(T') \ge 0$,
$n \ge 2$. -/
theorem betaInfAt_mul_sq (Q : QuadForm (𝓞 F) n) (hn : 2 ≤ n) (w : RealPlace F) {T : F}
    (hT : 0 ≤ realEmb w T) (x : F) :
    betaInfAt Q w (T * x ^ 2) = betaInfAt Q w T * w.1 x ^ (n - 2) := by
  have hx : 0 ≤ w.1 x := by rw [← abs_realEmb]; exact abs_nonneg _
  have hsq : realEmb w x ^ 2 = w.1 x ^ 2 := by rw [← abs_realEmb, sq_abs]
  have hpow : (w.1 x ^ 2) ^ (((n : ℝ) - 2) / 2) = w.1 x ^ (n - 2) := by
    rw [← Real.rpow_natCast (w.1 x) 2, ← Real.rpow_mul hx, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hn]; push_cast; ring
  simp only [betaInfAt, map_mul, map_pow, hsq]
  rw [Real.mul_rpow hT (sq_nonneg _), hpow]
  ring

/-- **(5.5) along a square class over $F$:** $\beta_\infty(T'x^2) = \beta_\infty(T')\prod_w w(x)^{n-2}$ for $T'$
nonnegative at every real place, $n \ge 2$. -/
theorem betaInfNF_mul_sq (Q : QuadForm (𝓞 F) n) (hn : 2 ≤ n) {T : F}
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) (x : F) :
    betaInfNF Q (T * x ^ 2) = betaInfNF Q T * (∏ w : RealPlace F, w.1 x) ^ (n - 2) := by
  simp only [betaInfNF, betaInfAt_mul_sq Q hn _ (hT _), Finset.prod_mul_distrib, Finset.prod_pow]

/-- **The product over the real places is the norm** for totally real $F$: $\prod_w w(x) = |N_{F/\mathbb{Q}}(x)|$
(Mathlib's `InfinitePlace.prod_eq_abs_norm`, all multiplicities $1$). -/
theorem prod_realPlace_eq_abs_norm [IsTotallyReal F] (x : F) :
    ∏ w : RealPlace F, w.1 x = |Algebra.norm ℚ x| := by
  rw [← InfinitePlace.prod_eq_abs_norm,
    Finset.prod_subtype Finset.univ (p := InfinitePlace.IsReal) (F := inferInstance)
      (fun w => ⟨fun _ => IsTotallyReal.isReal w, fun _ => Finset.mem_univ _⟩)]
  simp

/-- $N((x)) = |N_{F/\mathbb{Q}}(x)|$ for $x \in \mathcal O_F$ (Mathlib's `Ideal.absNorm_span_singleton`). -/
theorem absNorm_span_eq_abs_norm (x : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = |Algebra.norm ℚ (x : F)| := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
  push_cast; rfl

/-! ### $\mathrm{ord}_\mathfrak p$ and the local square class -/

/-- **$\mathrm{ord}_\mathfrak p(x)$**: the exponent of $\mathfrak p$ in the ideal $(x)$ (as in Mathlib's
`intValuation`; $0$ for $x = 0$ by convention). -/
def ordNF (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors

/-- $x \in \mathfrak p^{\mathrm{ord}_\mathfrak p(x)} \setminus \mathfrak p^{\mathrm{ord}_\mathfrak p(x) + 1}$ for $x \ne 0$. -/
theorem mem_pow_ordNF (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} (hx : x ≠ 0) :
    x ∈ v.asIdeal ^ ordNF v x ∧ x ∉ v.asIdeal ^ (ordNF v x + 1) := by
  have hv := v.intValuation_if_neg hx
  refine ⟨(v.intValuation_le_pow_iff_mem x _).1 (by rw [hv]; rfl), fun h => ?_⟩
  have := (v.intValuation_le_pow_iff_mem x _).2 h
  rw [hv, exp_le_exp] at this
  change -((ordNF v x : ℕ) : ℤ) ≤ -(((ordNF v x + 1 : ℕ)) : ℤ) at this
  push_cast at this; omega

/-- $\mathrm{ord}_\mathfrak p(x) = 0$ for $x \notin \mathfrak p$. -/
theorem ordNF_eq_zero (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} (hx : x ∉ v.asIdeal) : ordNF v x = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx v.asIdeal.zero_mem
  by_contra h
  exact hx (Ideal.pow_le_self h (mem_pow_ordNF v hx0).1)

/-- Only finitely many primes contain a nonzero $x$. -/
theorem finite_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {x}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx)).subset
    fun v hv => Ideal.dvd_span_singleton.2 hv

/-- **The primes dividing $x$** (empty for $x = 0$). -/
def primesDividing (x : 𝓞 F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : x = 0 then ∅ else (finite_mem_asIdeal h).toFinset

theorem mem_primesDividing {x : 𝓞 F} (hx : x ≠ 0) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ primesDividing x ↔ x ∈ v.asIdeal := by
  simp [primesDividing, hx]

/-- **$N((x)) = \prod_{\mathfrak p \in S}N\mathfrak p^{\mathrm{ord}_\mathfrak p(x)}$** for every finite set $S$ containing the
primes dividing $x \ne 0$ (unique factorization, Mathlib's `Ideal.finprod_heightOneSpectrum_factorization`). -/
theorem absNorm_span_eq_prod {x : 𝓞 F} (hx : x ≠ 0) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v ∉ S, x ∉ v.asIdeal) :
    Ideal.absNorm (Ideal.span {x}) = ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ ordNF v x := by
  have hI : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have h := congrArg Ideal.absNorm (Ideal.finprod_heightOneSpectrum_factorization hI)
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← h, map_prod]
    exact Finset.prod_congr rfl fun v _ => map_pow _ _ _
  · intro v hv
    by_contra hvS
    apply hv
    change v.asIdeal ^ ordNF v x = 1
    rw [ordNF_eq_zero v (hS v hvS), pow_zero, Ideal.one_eq_top]

/-- **(5.5) along a square class, norm form** ($F$ totally real, $T'$ nonnegative at every real place, $n \ge 2$,
$x \ne 0$, $S \supseteq \{\mathfrak p \mid x\}$): $\beta_\infty(T'x^2) = \beta_\infty(T')\,N(x)^{n-2} =
\beta_\infty(T')\prod_{\mathfrak p \in S}N\mathfrak p^{(n-2)\nu_\mathfrak p}$. -/
@[kb "hanke2004" "(5.5), p. 369 (along a square class, over F)"]
theorem betaInfNF_mul_sq_norm [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hn : 2 ≤ n) {T : 𝓞 F}
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal) :
    betaInfNF Q ((T * x ^ 2 : 𝓞 F) : F) =
      betaInfNF Q (T : F) * ∏ v ∈ S, (N𝔭 v) ^ ((n - 2) * ordNF v x) := by
  have e : ((T * x ^ 2 : 𝓞 F) : F) = (T : F) * (x : F) ^ 2 := by push_cast; rfl
  rw [e, betaInfNF_mul_sq Q hn hT, prod_realPlace_eq_abs_norm, ← absNorm_span_eq_abs_norm,
    absNorm_span_eq_prod hx hS]
  push_cast
  rw [← Finset.prod_pow]
  exact congrArg _ (Finset.prod_congr rfl fun v _ => by rw [← pow_mul, mul_comm])

/-! ### Local densities over $\mathcal O_F$: positivity and square classes -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "𝔬" => v.adicCompletionIntegers F

/-- $\iota(x) = \varpi^{\mathrm{ord}_\mathfrak p(x)}u$ with $u \in \mathfrak o_\mathfrak p^\times$, for $x \ne 0$. -/
theorem ι_eq_pow_mul_unit {x : 𝓞 F} (hx : x ≠ 0) :
    ∃ u : 𝔬, IsUnit u ∧ NF.ι v x = NF.π v ^ ordNF v x * u := by
  obtain ⟨h1, h2⟩ := mem_pow_ordNF v hx
  obtain ⟨u, hu⟩ := (NF.π_pow_dvd_ι_iff v _ x).2 h1
  refine ⟨u, ?_, hu⟩
  by_contra hu1
  have hd : NF.π v ∣ u := by
    by_contra hd; exact hu1 (DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) hd)
  apply h2
  rw [← NF.π_pow_dvd_ι_iff, hu, pow_succ]
  exact mul_dvd_mul_left _ hd

/-- **$\beta_\mathfrak p$ along a square class** (the step "$\beta_\mathfrak p(m) = \beta_\mathfrak p(T'\pi_\mathfrak p^{2\nu_\mathfrak p})$" of the
proofs of Thms 5.4, 5.7, Hanke 2004, pp. 369, 373): $\beta_\mathfrak p(T'x^2) = \beta_\mathfrak p(\varpi^{2\,\mathrm{ord}_\mathfrak p(x)}T')$
for $x \ne 0$, at every prime (dyadic or not). -/
theorem localDensityNF_mul_sq (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) {x : 𝓞 F} (hx : x ≠ 0) :
    NF.localDensity v Q (T * x ^ 2) = NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) := by
  obtain ⟨u, hu, hxu⟩ := ι_eq_pow_mul_unit v hx
  rw [NF.localDensity_eq_completion, NF.localDensity_eq_completion]
  have e : NF.ι v (T * x ^ 2) = u ^ 2 * NF.ι v (NF.unif v ^ (2 * ordNF v x) * T) := by
    simp only [map_mul, map_pow, hxu]; ring
  rw [e]
  exact (DVR.localDensity_mul_sq_of_isUnit _ _ u hu _).2

/-- $\beta_\mathfrak p(T'x^2) = \beta_\mathfrak p(T')$ for $x \notin \mathfrak p$. -/
theorem localDensityNF_mul_sq_of_not_mem (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) {x : 𝓞 F}
    (hx : x ∉ v.asIdeal) : NF.localDensity v Q (T * x ^ 2) = NF.localDensity v Q T := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx v.asIdeal.zero_mem
  rw [localDensityNF_mul_sq v Q T hx0, ordNF_eq_zero v hx, mul_zero, pow_zero, one_mul]

/-- $\beta_\mathfrak p(m) \ge 0$ ($Q$ nondegenerate, $m \ne 0$). -/
theorem localDensityNF_nonneg (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) :
    0 ≤ NF.localDensity v Q m := by
  rw [NF.localDensity_eq_completion]
  exact DVR.localDensity_nonneg _ (NF.nondegenerate_Qp v hQ) _ (NF.irreducible_π v) (NF.two_ne_zero' v)
    _ (NF.ι_ne_zero v hm)

/-- $\beta_\mathfrak p(m) > 0$ if $m \ne 0$ is locally represented at $\mathfrak p$. -/
theorem localDensityNF_pos (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0)
    (h : NF.IsLocallyRepresentedAt v Q m) : 0 < NF.localDensity v Q m := by
  rw [NF.localDensity_eq_completion]
  exact DVR.localDensity_pos_of_isLocallyRepresentedAt _ (NF.nondegenerate_Qp v hQ) _
    (NF.irreducible_π v) (NF.two_ne_zero' v) _ (NF.ι_ne_zero v hm)
    ((NF.isLocallyRepresentedAt_iff v Q m).1 h)

/-- $C_\mathfrak p(T') \ge 0$ ($n \ge 3$). -/
theorem localConstCNF_nonneg (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {T : 𝓞 F}
    (hT : T ≠ 0) : 0 ≤ NF.localConstC v Q T := by
  rw [NF.localConstC_eq_completion]
  exact DVR.localConstC_nonneg _ (NF.nondegenerate_Qp v hQ) hn _ (NF.irreducible_π v)
    (NF.two_ne_zero' v) _ (NF.ι_ne_zero v hT)

/-- $C'_\mathfrak p(T') \ge 0$ ($n \ge 3$). -/
theorem localConstC'NF_nonneg (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {T : 𝓞 F}
    (hT : T ≠ 0) : 0 ≤ NF.localConstC' v Q T :=
  le_min zero_le_one (localConstCNF_nonneg v Q hQ hn hT)

/-- **Isotropic primes over $F$** (`Iso`, Hanke 2004, §5): $Q$ is isotropic over the completion $F_\mathfrak p$. -/
def IsIsotropicNF (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Q.IsotropicIn (v.adicCompletion F)

/-- **$C_\mathfrak p(T') = 0$ at anisotropic $\mathfrak p$** (Lemma 3.8 over $F$; from `DVR.localConstC_eq_zero_of_anisotropic`). -/
theorem localConstCNF_eq_zero_of_anisotropic (Q : QuadForm (𝓞 F) n) (haniso : ¬ IsIsotropicNF Q v)
    (T : 𝓞 F) (hT : NF.IsPStable v Q T) : NF.localConstC v Q T = 0 := by
  rw [NF.localConstC_eq_completion]
  exact (DVR.localConstC_eq_zero_of_anisotropic (v.adicCompletion F) _ _ (NF.irreducible_π v) ∅
    (by rwa [NF.isotropicIn_Qp_iff]) _ ((NF.isPStable_iff v Q ∅ T).1 hT)).2

/-- **Remark 5.4.1(a) over $F$, anisotropic case**: $\beta_\mathfrak p(\varpi^{2\nu}T') = \beta_\mathfrak p(T')/N\mathfrak p^{(n-2)\nu}$
for $Q$ anisotropic over $F_\mathfrak p$, $n \ge 3$, $T' \ne 0$ $\mathfrak p$-stable. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (anisotropic, over F)"]
theorem localDensityNF_pow_sq_of_anisotropic (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (haniso : ¬ IsIsotropicNF Q v) (T : 𝓞 F) (hT0 : T ≠ 0) (hT : NF.IsPStable v Q T)
    (ν : ℕ) :
    NF.localDensity v Q (NF.unif v ^ (2 * ν) * T) =
      NF.localDensity v Q T / (N𝔭 v) ^ ((n - 2) * ν) := by
  have h := DVR.localDensity_pow_sq_of_anisotropic (v.adicCompletion F) _ (NF.nondegenerate_Qp v hQ)
    hn _ (NF.irreducible_π v) (NF.two_ne_zero' v) ∅ (by rwa [NF.isotropicIn_Qp_iff]) _
    (NF.ι_ne_zero v hT0) ((NF.isPStable_iff v Q ∅ T).1 hT) ν
  simpa only [NF.localDensity_eq_completion, NF.q_completion, map_mul, map_pow] using h

/-- **A prime with $C'_\mathfrak p(T') > 0$ is isotropic.** -/
theorem isIsotropicNF_of_localConstC'_pos (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) (hT : NF.IsPStable v Q T)
    (h : 0 < NF.localConstC' v Q T) : IsIsotropicNF Q v := by
  by_contra haniso
  rw [NF.localConstC', localConstCNF_eq_zero_of_anisotropic v Q haniso T hT,
    min_eq_right zero_le_one] at h
  exact lt_irrefl _ h

end Local

/-! ### The Euler product over the primes of $F$ -/

/-- **The local factor** $\mathfrak p \mapsto \beta_\mathfrak p(Q, m)$. -/
def eulerFactorNF (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  NF.localDensity v Q m

/-- **The Euler product** $\prod_\mathfrak p\beta_\mathfrak p(m)$ over the primes of $F$ (`tprod`; for $n \ge 4$ it converges
absolutely, `multipliable_eulerFactorNF`). -/
def eulerProductNF (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : ℝ := ∏' v, eulerFactorNF Q m v

/-- **The local product over $F$ with a given Euler-product value $P$:** $\beta_\infty(m)\cdot P$ (for $n = 3$, $P$ is a
natural-order value, `IsEulerProductValueNF`). -/
def aEWithNF (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) (P : ℝ) : ℝ := betaInfNF Q (m : F) * P

/-- **The local side of Siegel's formula over $F$** (Hanke 2004, (5.3), p. 368):
$a_E(m) = \beta_\infty(m)\prod_\mathfrak p\beta_\mathfrak p(m)$, the product over the real places and the finite primes of $F$.
For $n \ge 4$ (absolute convergence); for $n = 3$ use `aEWithNF`.

*Erratum (Hanke 2004, (5.3) over $F \ne \mathbb Q$; confirmed by proof):* with the normalizations used here (Lebesgue
measure at each real place, $\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$) the Fourier coefficient of the genus Eisenstein
series is $|d_F|^{-(n-1)/2}$ times this (`HilbertModular.eisQ_coeff_eq_discr_mul_aENF`, `eisQ_coeff_ne_aENF`); over
$\mathbb Q$ the factor is $1$. -/
@[kb "hanke2004" "(5.3), p. 368 (over F)"]
def aENF (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : ℝ := aEWithNF Q m (eulerProductNF Q m)

/-- **Changing finitely many factors of a natural-order Euler product:** if $g = 1$ off $S$, then
$\prod g f = (\prod_S g)\prod f$ in the natural order. -/
theorem isEulerProductValueNF_mul_finite {f g : HeightOneSpectrum (𝓞 F) → ℝ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hg : ∀ v ∉ S, g v = 1) {P : ℝ}
    (hP : IsEulerProductValueNF f P) :
    IsEulerProductValueNF (fun v => g v * f v) ((∏ v ∈ S, g v) * P) := by
  have h1 := isEulerProductValueNF_of_hasProd (hasProd_prod_of_ne_finset_one hg)
  refine (h1.mul hP).congr fun X => ?_
  simp only [eulerPartialProdNF, Finset.prod_mul_distrib]

/-- **The local factors along a square class:** $\beta_\mathfrak p(T'x^2) = g_\mathfrak p\,\beta_\mathfrak p(T')$ with
$g_\mathfrak p = \beta_\mathfrak p(\varpi^{2\nu_\mathfrak p}T')/\beta_\mathfrak p(T')$ for $\mathfrak p \in S$ and $1$ otherwise. -/
theorem eulerFactorNF_mul_sq (Q : QuadForm (𝓞 F) n) {T x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hβ : ∀ v ∈ S, NF.localDensity v Q T ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    eulerFactorNF Q (T * x ^ 2) v =
      (if v ∈ S then NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T
        else 1) * eulerFactorNF Q T v := by
  simp only [eulerFactorNF]
  split_ifs with hv
  · rw [localDensityNF_mul_sq v Q T hx, div_mul_cancel₀ _ (hβ v hv)]
  · rw [localDensityNF_mul_sq_of_not_mem v Q T (hS v hv), one_mul]

/-- **The natural-order Euler product along a square class** (every $n$, in particular $n = 3$). -/
theorem isEulerProductValueNF_mul_sq (Q : QuadForm (𝓞 F) n) {T x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hβ : ∀ v ∈ S, NF.localDensity v Q T ≠ 0) {P : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P) :
    IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2))
      ((∏ v ∈ S, NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T) * P) := by
  classical
  have h := isEulerProductValueNF_mul_finite
    (g := fun v => if v ∈ S then
      NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T else 1)
    (S := S) (fun v hv => ite_eq_right_iff.2 fun h => absurd h hv) hP
  have e : (fun v => (if v ∈ S then
      NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T else 1) *
        eulerFactorNF Q T v) = eulerFactorNF Q (T * x ^ 2) :=
    funext fun v => (eulerFactorNF_mul_sq Q hx hS hβ v).symm
  rw [e] at h
  have hA : (∏ v ∈ S, if v ∈ S then
      NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T else 1) =
      ∏ v ∈ S, NF.localDensity v Q (NF.unif v ^ (2 * ordNF v x) * T) / NF.localDensity v Q T :=
    Finset.prod_congr rfl fun v hv => by simp [hv]
  rwa [hA] at h

/-! ### The ratio identity and Theorem 5.4 over $F$ -/

/-- **The local ratio factor over $F$:** $F_\mathfrak p(T', \nu) = N\mathfrak p^{(n-2)\nu}\,\beta_\mathfrak p(\varpi^{2\nu}T')/\beta_\mathfrak p(T')$
(as `sqShiftFactor`, with $q = N\mathfrak p$). -/
def sqShiftFactorNF (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ν : ℕ) : ℝ :=
  (N𝔭 v) ^ ((n - 2) * ν) *
    (NF.localDensity v Q (NF.unif v ^ (2 * ν) * T) / NF.localDensity v Q T)

/-- **The ratio identity over $F$** (the common core of Thms 5.4 and 5.7, Hanke 2004, pp. 369–374). Let $F$ be totally
real, $n \ge 2$, $T' \in \mathcal O_F$ nonnegative at every real place, $x \in \mathcal O_F \setminus 0$, $S$ a finite set of
primes containing those dividing $x$, $\beta_\mathfrak p(T') \ne 0$ for $\mathfrak p \in S$, and $P$, $P_m$ the natural-order
values of $\prod_\mathfrak p\beta_\mathfrak p(T')$, $\prod_\mathfrak p\beta_\mathfrak p(T'x^2)$. Then
$$\beta_\infty(T'x^2)\,P_m = \beta_\infty(T')\,P\prod_{\mathfrak p \in S}F_\mathfrak p(T', \mathrm{ord}_\mathfrak p(x)).$$ -/
theorem aEWithNF_mul_sq [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hn : 2 ≤ n) {T : 𝓞 F}
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hβ : ∀ v ∈ S, NF.localDensity v Q T ≠ 0) {P Pm : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q (T * x ^ 2) Pm = aEWithNF Q T P * ∏ v ∈ S, sqShiftFactorNF Q T v (ordNF v x) := by
  rw [hPm.unique (isEulerProductValueNF_mul_sq Q hx hS hβ hP), aEWithNF, aEWithNF,
    betaInfNF_mul_sq_norm Q hn hT hx hS]
  simp only [sqShiftFactorNF, Finset.prod_mul_distrib]
  ring

/-- **$F_\mathfrak p$ in terms of $C_\mathfrak p(T')$ over $F$** ((5.8) times $N\mathfrak p^{(n-2)\nu}$): for $n \ge 3$, $T' \ne 0$
$\mathfrak p$-stable, $F_\mathfrak p(T', \nu) = C_\mathfrak p(T')N\mathfrak p^{(n-2)\nu} + 1 - C_\mathfrak p(T')$. -/
theorem sqShiftFactorNF_eq_localConst (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (T : 𝓞 F) (hT0 : T ≠ 0) (hT : NF.IsPStable v Q T) (ν : ℕ) :
    sqShiftFactorNF Q T v ν =
      NF.localConstC v Q T * (N𝔭 v) ^ ((n - 2) * ν) + (1 - NF.localConstC v Q T) := by
  have hp : (0 : ℝ) < (N𝔭 v) ^ ((n - 2) * ν) := pow_pos (by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) _
  rw [sqShiftFactorNF, NF.localDensity_pow_sq_div v Q hQ hn T hT0 hT ν]
  field_simp

/-- $F_\mathfrak p(T', \nu) = N\mathfrak p^{(n-2)\nu}\big(C_\mathfrak p + (1 - C_\mathfrak p)/N\mathfrak p^{(n-2)\nu}\big)$ ((5.8) over $F$). -/
theorem sqShiftFactorNF_eq_bracket (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (T : 𝓞 F) (hT0 : T ≠ 0) (hT : NF.IsPStable v Q T) (ν : ℕ) :
    sqShiftFactorNF Q T v ν = (N𝔭 v) ^ ((n - 2) * ν) *
      (NF.localConstC v Q T + (1 - NF.localConstC v Q T) / (N𝔭 v) ^ ((n - 2) * ν)) := by
  rw [sqShiftFactorNF, NF.localDensity_pow_sq_div v Q hQ hn T hT0 hT ν]

/-- **$F_\mathfrak p = 1$ at anisotropic $\mathfrak p$** (Remark 5.4.1(a) over $F$). -/
theorem sqShiftFactorNF_of_anisotropic (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (haniso : ¬ IsIsotropicNF Q v) (T : 𝓞 F) (hT0 : T ≠ 0)
    (hT : NF.IsPStable v Q T) (ν : ℕ) : sqShiftFactorNF Q T v ν = 1 := by
  have hβ := localDensityNF_pos v Q hQ hT0 hT.1
  have hp : (0 : ℝ) < (N𝔭 v) ^ ((n - 2) * ν) := pow_pos (by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) _
  rw [sqShiftFactorNF, localDensityNF_pow_sq_of_anisotropic v Q hQ hn haniso T hT0 hT ν]
  field_simp

/-- **Theorem 5.4 over $F$, uniform form** ($C_\mathfrak p = 0$ at anisotropic $\mathfrak p$): under the hypotheses of
`aEWithNF_mul_sq` with $n \ge 3$, $Q$ nondegenerate and $T' \ne 0$ $\mathfrak p$-stable at every $\mathfrak p \in S$,
$$\beta_\infty(T'x^2)P_m = \beta_\infty(T')P\prod_{\mathfrak p \in S}\big(C_\mathfrak p(T')N\mathfrak p^{(n-2)\nu_\mathfrak p} + 1 - C_\mathfrak p(T')\big).$$ -/
theorem aEWithNF_mul_sq_eq_localConst [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F}
    (hx : x ≠ 0) {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) {P Pm : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q (T * x ^ 2) Pm = aEWithNF Q T P * ∏ v ∈ S,
      (NF.localConstC v Q T * (N𝔭 v) ^ ((n - 2) * ordNF v x) + (1 - NF.localConstC v Q T)) := by
  rw [aEWithNF_mul_sq Q (by omega) hT hx hS
    (fun v hv => (localDensityNF_pos v Q hQ hT0 (hst v hv).1).ne') hP hPm]
  congr 1
  exact Finset.prod_congr rfl fun v hv =>
    sqShiftFactorNF_eq_localConst Q hQ hn v T hT0 (hst v hv) _

open Classical in
/-- **Theorem 5.4 over a totally real field** (Hanke 2004, p. 369). Let $F$ be totally real, $Q$ nondegenerate over
$\mathcal O_F$ in $n \ge 3$ variables, $T' \in \mathcal O_F \setminus 0$ nonnegative at every real place, $x \in \mathcal O_F
\setminus 0$, $S$ a finite set of primes containing the primes dividing $x$, $T'$ $\mathfrak p$-stable at every $\mathfrak p \in S$,
$\nu_\mathfrak p = \mathrm{ord}_\mathfrak p(x)$, and $P$, $P_m$ the natural-order values of $\prod_\mathfrak p\beta_\mathfrak p(T')$ and
$\prod_\mathfrak p\beta_\mathfrak p(T'x^2)$. Then, with $a_E(\cdot) = \beta_\infty(\cdot)\prod_\mathfrak p\beta_\mathfrak p(\cdot)$,
$$a_E(T'x^2) = a_E(T')\prod_{\mathfrak p \in S \cap \mathrm{Iso}}\Big[C_\mathfrak p(T') + \frac{1 - C_\mathfrak p(T')}{N\mathfrak p^{(n-2)\nu_\mathfrak p}}\Big]
  \cdot N\big((x)_{\mathrm{Iso}}\big)^{n-2}, \qquad N\big((x)_{\mathrm{Iso}}\big) = \prod_{\mathfrak p \in S \cap \mathrm{Iso}}N\mathfrak p^{\nu_\mathfrak p}.$$
*Differences from the paper:* $m' = x$ is a global element (the paper allows $m' \in \mathbb A_F$; Remark 5.7.1's adelic
square classes are not formalized), and Siegel's formula (5.3) is not used: the statement is about the local
product. *Update (as over $\mathbb{Q}$, `thm_5_4`):* only nondegeneracy of $Q$ is used (the paper: totally definite). -/
@[kb "hanke2004" "Thm 5.4, p. 369 (over F)"]
theorem thm_5_4_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) {P Pm : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q (T * x ^ 2) Pm = aEWithNF Q T P *
      (∏ v ∈ S.filter (IsIsotropicNF Q),
        (NF.localConstC v Q T + (1 - NF.localConstC v Q T) / (N𝔭 v) ^ ((n - 2) * ordNF v x))) *
      (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) := by
  rw [aEWithNF_mul_sq Q (by omega) hT hx hS
      (fun v hv => (localDensityNF_pos v Q hQ hT0 (hst v hv).1).ne') hP hPm,
    ← Finset.prod_filter_mul_prod_filter_not S (IsIsotropicNF Q)]
  have h1 : ∏ v ∈ S.filter (fun v => ¬ IsIsotropicNF Q v), sqShiftFactorNF Q T v (ordNF v x) = 1 :=
    Finset.prod_eq_one fun v hv => by
      rw [Finset.mem_filter] at hv
      exact sqShiftFactorNF_of_anisotropic Q hQ hn v hv.2 T hT0 (hst v hv.1) _
  have h2 : ∏ v ∈ S.filter (IsIsotropicNF Q), sqShiftFactorNF Q T v (ordNF v x) =
      (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
      ∏ v ∈ S.filter (IsIsotropicNF Q),
        (NF.localConstC v Q T + (1 - NF.localConstC v Q T) / (N𝔭 v) ^ ((n - 2) * ordNF v x)) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [sqShiftFactorNF_eq_bracket Q hQ hn v T hT0 (hst v hv.1), ← pow_mul, mul_comm (ordNF v x)]
  rw [h1, h2]
  ring

/-! ### Lower bounds: (5.13) and Theorem 5.7(a) over $F$ -/

/-- **(5.11) times $N\mathfrak p^{(n-2)\nu}$ over $F$:** $C'_\mathfrak p(T')N\mathfrak p^{(n-2)\nu} \le F_\mathfrak p(T', \nu)$. -/
theorem sqShiftFactorNF_ge (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (T : 𝓞 F) (hT0 : T ≠ 0) (hT : NF.IsPStable v Q T) (ν : ℕ) :
    NF.localConstC' v Q T * (N𝔭 v) ^ ((n - 2) * ν) ≤ sqShiftFactorNF Q T v ν := by
  rw [sqShiftFactorNF, mul_comm]
  exact mul_le_mul_of_nonneg_left (NF.localDensity_pow_sq_div_ge v Q hQ hn T hT0 hT ν)
    (pow_nonneg (Nat.cast_nonneg _) _)

open Classical in
/-- **The product of the $F_\mathfrak p$ over $F$, bounded below** (the local engine of (5.13) and Thm 5.7): for $Q$
nondegenerate, $n \ge 3$, $T' \ne 0$ $\mathfrak p$-stable at every $\mathfrak p \in S$, and $0 < c_\mathfrak p \le C'_\mathfrak p(T')$ for
$\mathfrak p \in S \cap G$,
$$\Big(\prod_{\mathfrak p \in S \cap \mathrm{Iso}}N\mathfrak p^{\nu_\mathfrak p}\Big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p \notin G}C'_\mathfrak p(T')
  \prod_{\mathfrak p \in S \cap G}c_\mathfrak p \;\le\; \prod_{\mathfrak p \in S}F_\mathfrak p(T', \nu_\mathfrak p).$$ -/
theorem prod_sqShiftFactorNF_ge (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    {S : Finset (HeightOneSpectrum (𝓞 F))} {T : 𝓞 F} (hT0 : T ≠ 0)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (ν : HeightOneSpectrum (𝓞 F) → ℕ)
    (G : HeightOneSpectrum (𝓞 F) → Prop) (c : HeightOneSpectrum (𝓞 F) → ℝ)
    (hc : ∀ v ∈ S, G v → 0 < c v ∧ c v ≤ NF.localConstC' v Q T) :
    (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ν v) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ G v), NF.localConstC' v Q T) *
        ∏ v ∈ S.filter G, c v ≤
      ∏ v ∈ S, sqShiftFactorNF Q T v (ν v) := by
  have hiso : ∀ v ∈ S, G v → IsIsotropicNF Q v := fun v hv hG =>
    isIsotropicNF_of_localConstC'_pos v Q T (hst v hv) ((hc v hv hG).1.trans_le (hc v hv hG).2)
  set d : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if G v then c v else NF.localConstC' v Q T with hd
  have hGeq : (S.filter (IsIsotropicNF Q)).filter G = S.filter G := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hiso v h1 h3⟩, h3⟩
  have e1 : (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ G v), NF.localConstC' v Q T) *
        ∏ v ∈ S.filter G, c v = ∏ v ∈ S.filter (IsIsotropicNF Q), d v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (S.filter (IsIsotropicNF Q)) G, hGeq, mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun v hv => by
        rw [Finset.mem_filter] at hv; simp [hd, hv.2]
    · exact Finset.prod_congr rfl fun v hv => by
        rw [Finset.mem_filter] at hv; simp [hd, hv.2]
  rw [mul_assoc, e1, ← Finset.prod_pow, ← Finset.prod_mul_distrib, Finset.prod_filter]
  refine Finset.prod_le_prod₀ (fun v hv => ?_) (fun v hv => ?_)
  · have hd0 : 0 ≤ d v := by
      simp only [hd]; split_ifs with hG
      · exact (hc v hv hG).1.le
      · exact localConstC'NF_nonneg v Q hQ hn hT0
    split_ifs <;> positivity
  · split_ifs with hI
    · have hdC : d v ≤ NF.localConstC' v Q T := by
        simp only [hd]; split_ifs with hG
        · exact (hc v hv hG).2
        · exact le_rfl
      have hp0 : (0 : ℝ) ≤ (N𝔭 v) ^ ν v := pow_nonneg (Nat.cast_nonneg _) _
      calc ((N𝔭 v) ^ ν v) ^ (n - 2) * d v
          ≤ NF.localConstC' v Q T * (N𝔭 v) ^ ((n - 2) * ν v) := by
            rw [mul_comm, mul_comm (n - 2), pow_mul]
            exact mul_le_mul_of_nonneg_right hdC (pow_nonneg hp0 _)
        _ ≤ _ := sqShiftFactorNF_ge Q hQ hn v T hT0 (hst v hv) (ν v)
    · exact (sqShiftFactorNF_of_anisotropic Q hQ hn v hI T hT0 (hst v hv) (ν v)).ge

/-- **Totally positive definite** (Hanke 2004, §5): $\sigma_w(Q)$ is positive definite at every real place $w$. -/
@[kb "hanke2004" "§5, p. 368 (totally positive definite)"]
def IsTotallyPosDef (Q : QuadForm (𝓞 F) n) : Prop :=
  ∀ w : RealPlace F, ∀ y : Fin n → ℝ, y ≠ 0 → 0 < (realForm Q w).evalIn ℝ y

/-- $Q(c\vec y) = c^2Q(\vec y)$ for a real form. -/
theorem evalIn_real_smul (Q : QuadForm ℝ n) (c : ℝ) (y : Fin n → ℝ) :
    Q.evalIn ℝ (c • y) = c ^ 2 * Q.evalIn ℝ y := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **$D_w > 0$ for a totally positive definite form** (via the spectral factorization `exists_sqrt_factor`). -/
theorem gramDetNF_pos {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) (w : RealPlace F) :
    0 < gramDetNF Q w := by
  set H := (realForm Q w).hessian with hH
  have hA : ((1 / 2 : ℝ) • H).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, hH,
      QuadForm.hessian, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hev : ∀ y : Fin n → ℝ, (realForm Q w).evalIn ℝ y = y ⬝ᵥ (((1 / 2 : ℝ) • H) *ᵥ y) := by
    intro y
    have h := QuadForm.polar_eq_hessian ℝ (realForm Q w) y y
    rw [← two_smul ℝ y, evalIn_real_smul] at h
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
    rw [← hH] at h
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← h]
    ring
  obtain ⟨_, -, hdet, -⟩ := exists_sqrt_factor _ hA fun y hy => by rw [← hev]; exact hQ w y hy
  rw [Matrix.det_smul, Fintype.card_fin] at hdet
  rw [gramDetNF, ← hH, show H.det / 2 ^ n = (1 / 2 : ℝ) ^ n * H.det by
    rw [_root_.one_div_pow]; ring]
  exact hdet

/-- $\beta_\infty(m) \ge 0$ for $Q$ totally positive definite and $m$ nonnegative at every real place. -/
theorem betaInfNF_nonneg {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) {m : F}
    (hm : ∀ w : RealPlace F, 0 ≤ realEmb w m) : 0 ≤ betaInfNF Q m := by
  refine Finset.prod_nonneg fun w _ => ?_
  have h1 : 0 ≤ unitBallVol n := ENNReal.toReal_nonneg
  have h2 : 0 ≤ gramDetNF Q w ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDetNF_pos hQ w).le _
  have h3 : 0 ≤ realEmb w m ^ (((n : ℝ) - 2) / 2) := Real.rpow_nonneg (hm w) _
  unfold betaInfAt
  positivity

/-- A natural-order Euler-product value is $\ge 0$ ($Q$ nondegenerate, $m \ne 0$). -/
theorem isEulerProductValueNF_nonneg {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate)
    {m : 𝓞 F} (hm : m ≠ 0) {P : ℝ} (hP : IsEulerProductValueNF (eulerFactorNF Q m) P) : 0 ≤ P :=
  ge_of_tendsto' hP fun _ => Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQ hm

/-- $\beta_\infty(T')P \ge 0$. -/
theorem aEWithNF_nonneg {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {P : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P) : 0 ≤ aEWithNF Q T P :=
  mul_nonneg (betaInfNF_nonneg hQ hT) (isEulerProductValueNF_nonneg hQnd hT0 hP)

open Classical in
/-- **Lower bound for $a_E(T'x^2)/a_E(T')$ over $F$ with good primes** (the common form of (5.13) and Thm 5.7): under
the hypotheses of `thm_5_4_NF`, with $Q$ totally positive definite and $0 < c_\mathfrak p \le C'_\mathfrak p(T')$ for
$\mathfrak p \in S \cap G$,
$$\beta_\infty(T')P\,N((x)_{\mathrm{Iso}})^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p \notin G}C'_\mathfrak p(T')
  \prod_{\mathfrak p \in S \cap G}c_\mathfrak p \;\le\; \beta_\infty(T'x^2)P_m.$$ -/
theorem aEWithNF_mul_sq_ge [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 3 ≤ n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (G : HeightOneSpectrum (𝓞 F) → Prop)
    (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : ∀ v ∈ S, G v → 0 < c v ∧ c v ≤ NF.localConstC' v Q T)
    {P Pm : ℝ} (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q T P * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ G v), NF.localConstC' v Q T) *
        ∏ v ∈ S.filter G, c v ≤
      aEWithNF Q (T * x ^ 2) Pm := by
  rw [aEWithNF_mul_sq Q (by omega) hT hx hS
      (fun v hv => (localDensityNF_pos v Q hQnd hT0 (hst v hv).1).ne') hP hPm, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (aEWithNF_nonneg hQ hQnd hT0 hT hP)
  rw [← mul_assoc]
  exact prod_sqShiftFactorNF_ge Q hQnd hn hT0 hst (fun v => ordNF v x) G c hc

open Classical in
/-- **(5.13) over a totally real field** (Hanke 2004, p. 373), local product, any $n \ge 3$: for $Q$ totally positive
definite and nondegenerate, $T' \ne 0$ totally nonnegative and $\mathfrak p$-stable at every $\mathfrak p \in S$,
$x \ne 0$ with $S \supseteq \{\mathfrak p \mid x\}$, and natural-order Euler-product values $P$, $P_m$,
$$\beta_\infty(T'x^2)P_m \;\ge\; \beta_\infty(T')P\,N\big((x)_{\mathrm{Iso}}\big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso}}C'_\mathfrak p(T').$$
The paper's product runs over $\mathrm{Stable}(T') \cap \mathrm{Iso} \supseteq S \cap \mathrm{Iso}$; since $C'_\mathfrak p \le 1$ the bound
over $S$ is stronger. -/
@[kb "hanke2004" "(5.13), p. 373 (over F)"]
theorem eq_5_13_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 3 ≤ n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) {P Pm : ℝ}
    (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q T P * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), NF.localConstC' v Q T ≤
      aEWithNF Q (T * x ^ 2) Pm := by
  have h := aEWithNF_mul_sq_ge Q hQ hQnd hn hT0 hT hx hS hst (fun _ => False) (fun _ => 1)
    (fun _ _ h => h.elim) hP hPm
  simpa using h

/-! ### Good primes and the good-prime hypothesis -/

/-- **Good primes over $F$**: $\mathfrak p \nmid 2\det H$ (non-dyadic, and $\det H$ a unit at $\mathfrak p$). As over $\mathbb{Q}$
(`IsGoodPrime`), dyadic $\mathfrak p$ are treated as bad. -/
def IsGoodPrimeNF (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (2 : 𝓞 F) ∉ v.asIdeal ∧ Q.hessian.det ∉ v.asIdeal

/-- **The good-prime shape of $Q$ at $\mathfrak p$** (hypothesis; the number-field form of
`exists_diag_unimodular_same_counts_det`): over $\mathfrak o_\mathfrak p$,
$Q$ has the counts $r_{\varpi^k}(m)$ of a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with unit coefficients, and
$2^n\prod_i a_i = u^2\det H$ with $u$ a unit. At $\mathfrak p \nmid 2\det H$ this holds for every $Q$ (Lemma 2.1); it is taken
here as the hypothesis `∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355, at p ∤ 2det H (hypothesis, over F)"]
def GoodPrimeShape (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ a : Fin n → v.adicCompletionIntegers F, (∀ i, ¬ NF.π v ∣ a i) ∧
    (∀ (k : ℕ) (m : v.adicCompletionIntegers F),
      DVR.repCount (NF.Qp v Q) (NF.π v) k m = DVR.repCount (QuadForm.diag a) (NF.π v) k m) ∧
    ∃ u : v.adicCompletionIntegers F, ¬ NF.π v ∣ u ∧ 2 ^ n * ∏ i, a i = u ^ 2 * NF.ι v Q.hessian.det

/-- **Equal counts over a DVR give equal densities and local constants** (the DVR form of
`LocalDensity.localDensity_congr_of_repCount`; Zero-type counts are counts at a lower level, map $\pi_Z$). -/
theorem dvr_localDensity_congr_of_repCount {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] (Q Q' : QuadForm R n) (π : R)
    (hπ : Irreducible π) (h : ∀ k m, DVR.repCount Q π k m = DVR.repCount Q' π k m) (T : R) :
    DVR.localDensity Q π T = DVR.localDensity Q' π T ∧ DVR.localConstC Q π T = DVR.localConstC Q' π T := by
  have h1 : DVR.localDensity Q π T = DVR.localDensity Q' π T := by
    unfold DVR.localDensity; simp_rw [h]
  have h2 : DVR.localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ DVR.IsZeroType π k x) =
      DVR.localDensityOf Q' π (π ^ 2 * T) (fun k x => ¬ DVR.IsZeroType π k x) := by
    unfold DVR.localDensityOf Filter.limUnder
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have e1 := DVR.repCount_eq_zero_add_nonZero Q π hπ k (π ^ 2 * T)
    have e2 := DVR.repCount_eq_zero_add_nonZero Q' π hπ k (π ^ 2 * T)
    rw [DVR.repCountZero_eq Q π hπ _ T rfl k hk] at e1
    rw [DVR.repCountZero_eq Q' π hπ _ T rfl k hk] at e2
    rw [h, h] at e1
    have : DVR.repCountOf Q π k (π ^ 2 * T) (fun x => ¬ DVR.IsZeroType π k x) =
        DVR.repCountOf Q' π k (π ^ 2 * T) (fun x => ¬ DVR.IsZeroType π k x) := by omega
    rw [this]
  refine ⟨h1, ?_⟩
  rw [DVR.localConstC_eq_alg, DVR.localConstC_eq_alg, h1, h2]

section Good

variable (v : HeightOneSpectrum (𝓞 F))

/-- $\varpi \nmid 2$ at a non-dyadic prime. -/
theorem not_π_dvd_two {v : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ¬ NF.π v ∣ 2 := by
  rw [← map_ofNat (NF.ι v) 2, NF.π_dvd_ι_iff]; exact h2

/-- Under the good-prime shape, $\beta_\mathfrak p(m)$ is the density of the diagonal form at $\iota(m)$. -/
theorem localDensityNF_eq_diag {Q : QuadForm (𝓞 F) n} {a : Fin n → v.adicCompletionIntegers F}
    (hc : ∀ (k : ℕ) (m : v.adicCompletionIntegers F),
      DVR.repCount (NF.Qp v Q) (NF.π v) k m = DVR.repCount (QuadForm.diag a) (NF.π v) k m) (m : 𝓞 F) :
    NF.localDensity v Q m = DVR.localDensity (QuadForm.diag a) (NF.π v) (NF.ι v m) := by
  rw [NF.localDensity_eq_completion]
  exact (dvr_localDensity_congr_of_repCount _ _ _ (NF.irreducible_π v) hc _).1

/-- Under the good-prime shape, $C'_\mathfrak p(T')$ is that of the diagonal form at $\iota(T')$. -/
theorem localConstC'NF_eq_diag {Q : QuadForm (𝓞 F) n} {a : Fin n → v.adicCompletionIntegers F}
    (hc : ∀ (k : ℕ) (m : v.adicCompletionIntegers F),
      DVR.repCount (NF.Qp v Q) (NF.π v) k m = DVR.repCount (QuadForm.diag a) (NF.π v) k m) (T : 𝓞 F) :
    NF.localConstC' v Q T = DVR.localConstC' (QuadForm.diag a) (NF.π v) (NF.ι v T) := by
  rw [NF.localConstC'_eq_completion, DVR.localConstC', DVR.localConstC',
    (dvr_localDensity_congr_of_repCount _ _ _ (NF.irreducible_π v) hc _).2]

/-- $|\chi(a)| \le 1$ for the quadratic character of a finite field. -/
theorem abs_quadraticChar_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    |((quadraticChar K a : ℤ) : ℝ)| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases quadraticChar_dichotomy ha with h | h <;> simp [h]

/-- $N\mathfrak p \ge 2$, as a real number. -/
theorem two_le_normP_real : (2 : ℝ) ≤ N𝔭 v := by exact_mod_cast two_le_normP v

/-- **$|\beta_\mathfrak p(m) - 1| \le N\mathfrak p^{-2}$ at a good prime with $m \notin \mathfrak p$, $n \ge 4$** (Table 1: $\beta_\mathfrak p(m) =
1 - \chi/N\mathfrak p^{n/2}$ for $n$ even, $1 + \chi/N\mathfrak p^{(n-1)/2}$ for $n$ odd). -/
theorem abs_localDensityNF_sub_one_le {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (hG : IsGoodPrimeNF Q v)
    (hsh : GoodPrimeShape Q v) {m : 𝓞 F} (hm : m ∉ v.asIdeal) :
    |NF.localDensity v Q m - 1| ≤ 1 * (N𝔭 v) ^ (-(2 : ℝ)) := by
  obtain ⟨a, ha, hc, -⟩ := hsh
  have h2 := not_π_dvd_two hG.1
  have hmπ : ¬ NF.π v ∣ NF.ι v m := by rw [NF.π_dvd_ι_iff]; exact hm
  have hq : (DVR.q (v.adicCompletionIntegers F) : ℝ) = N𝔭 v := by rw [NF.q_completion]
  have hN1 : (1 : ℝ) ≤ N𝔭 v := by linarith [two_le_normP_real v]
  have hrpow : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, one_div]
  rw [one_mul, hrpow, localDensityNF_eq_diag v hc]
  have key : ∀ k : ℕ, 2 ≤ k → ∀ c : ℝ, |c| ≤ 1 → |c / (N𝔭 v) ^ k| ≤ 1 / (N𝔭 v) ^ 2 := by
    intro k hk c hc1
    have hpos : (0 : ℝ) < (N𝔭 v) ^ 2 := by positivity
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N𝔭 v) ^ k), div_le_div_iff₀ (by positivity) hpos]
    calc |c| * (N𝔭 v) ^ 2 ≤ 1 * (N𝔭 v) ^ 2 := mul_le_mul_of_nonneg_right hc1 hpos.le
      _ ≤ 1 * (N𝔭 v) ^ k := by rw [one_mul, one_mul]; exact pow_le_pow_right₀ hN1 hk
  rcases Nat.even_or_odd n with he | ho
  · rw [DVR.localDensity_diag_even_unit a _ (NF.irreducible_π v) h2 ha (by omega) he _ hmπ, hq,
      show ∀ c d : ℝ, 1 - c / d - 1 = -(c / d) from fun c d => by ring, abs_neg]
    exact key _ (by obtain ⟨j, rfl⟩ := he; omega) _ (abs_quadraticChar_le _)
  · rw [DVR.localDensity_diag_odd_unit a _ (NF.irreducible_π v) h2 ha ho _ hmπ, hq, add_sub_cancel_left]
    exact key _ (by obtain ⟨j, rfl⟩ := ho; omega) _ (abs_quadraticChar_le _)

/-- **$C'_\mathfrak p(T') = 1$ at good primes for $n = 3$** (Hanke 2004, (5.12), p. 371; first part of Thm 5.7(a)), over
$F$, for $T' \notin \mathfrak p^2$, under the good-prime shape. From `DVR.localConstC'_diag_three`. -/
theorem localConstC'NF_good_three {Q : QuadForm (𝓞 F) 3} (hG : IsGoodPrimeNF Q v)
    (hsh : GoodPrimeShape Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) : NF.localConstC' v Q T = 1 := by
  obtain ⟨a, ha, hc, -⟩ := hsh
  rw [localConstC'NF_eq_diag v hc]
  exact DVR.localConstC'_diag_three a _ (NF.irreducible_π v) (not_π_dvd_two hG.1) ha _
    (by rw [NF.π_pow_dvd_ι_iff]; exact hT2)

end Good

/-- $2\det H \cdot m \ne 0$. -/
theorem two_mul_det_mul_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) :
    (2 : 𝓞 F) * Q.hessian.det * m ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero hQ) hm

/-- **Absolute convergence of $\prod_\mathfrak p\beta_\mathfrak p(m)$ over $F$ for $n \ge 4$** (Hanke 2004, (5.3), p. 368), under the
good-prime shape: $|\beta_\mathfrak p(m) - 1| \le N\mathfrak p^{-2}$ for $\mathfrak p \nmid 2m\det H$, and
`NFEuler.multipliable_of_abs_sub_one_le`. -/
@[kb "hanke2004" "(5.3), p. 368 (n ≥ 4, over F)"]
theorem multipliable_eulerFactorNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    Multipliable (eulerFactorNF Q m) := by
  refine multipliable_of_abs_sub_one_le _ (C := 1) (σ := 2) (by norm_num) ?_
  filter_upwards [(finite_mem_asIdeal (two_mul_det_mul_ne_zero hQ hm)).eventually_cofinite_notMem]
    with v hv
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h))
  have hd : Q.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
  have hmv : m ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  exact abs_localDensityNF_sub_one_le v hn ⟨h2, hd⟩ (hshape v ⟨h2, hd⟩) hmv

theorem hasProd_eulerProductNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    HasProd (eulerFactorNF Q m) (eulerProductNF Q m) :=
  (multipliable_eulerFactorNF hQ hn hshape hm).hasProd

theorem isEulerProductValueNF_eulerProductNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate)
    (hn : 4 ≤ n) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    IsEulerProductValueNF (eulerFactorNF Q m) (eulerProductNF Q m) :=
  isEulerProductValueNF_of_hasProd (hasProd_eulerProductNF hQ hn hshape hm)

/-! ### The $n \ge 4$ forms (`aENF`) -/

/-- **The ratio identity for $n \ge 4$ over $F$** (`aENF`): $a_E(T'x^2) = a_E(T')\prod_{\mathfrak p \in S}F_\mathfrak p(T',
\nu_\mathfrak p)$, under the good-prime shape (for absolute convergence). -/
theorem aENF_mul_sq [IsTotallyReal F] {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hβ : ∀ v ∈ S, NF.localDensity v Q T ≠ 0) :
    aENF Q (T * x ^ 2) = aENF Q T * ∏ v ∈ S, sqShiftFactorNF Q T v (ordNF v x) :=
  aEWithNF_mul_sq Q (by omega) hT hx hS hβ (isEulerProductValueNF_eulerProductNF hQ hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQ hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))

open Classical in
/-- **Theorem 5.4 over $F$ for $n \ge 4$** (Hanke 2004, p. 369), with `aENF` (absolutely convergent Euler products,
under the good-prime shape `hshape`):
$$a_E(T'x^2) = a_E(T')\prod_{\mathfrak p \in S \cap \mathrm{Iso}}\Big[C_\mathfrak p(T') + \frac{1 - C_\mathfrak p(T')}{N\mathfrak p^{(n-2)\nu_\mathfrak p}}\Big]
  N\big((x)_{\mathrm{Iso}}\big)^{n-2}.$$ -/
@[kb "hanke2004" "Thm 5.4, p. 369 (over F)"]
theorem thm_5_4_aENF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) :
    aENF Q (T * x ^ 2) = aENF Q T *
      (∏ v ∈ S.filter (IsIsotropicNF Q),
        (NF.localConstC v Q T + (1 - NF.localConstC v Q T) / (N𝔭 v) ^ ((n - 2) * ordNF v x))) *
      (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) :=
  thm_5_4_NF Q hQ (by omega) hT0 hT hx hS hst (isEulerProductValueNF_eulerProductNF hQ hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQ hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))

open Classical in
/-- **(5.13) over $F$ for $n \ge 4$** (Hanke 2004, p. 373), with `aENF`:
$a_E(T'x^2) \ge a_E(T')\,N((x)_{\mathrm{Iso}})^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso}}C'_\mathfrak p(T')$. -/
@[kb "hanke2004" "(5.13), p. 373 (over F)"]
theorem eq_5_13_aENF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) :=
  eq_5_13_NF Q hQ hQnd (by omega) hT0 hT hx hS hst
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))

/-! ### Theorem 5.7(a), first part, over $F$ -/

open Classical in
/-- **Theorem 5.7(a), first part, over a totally real field** (Hanke 2004, p. 372; proof p. 374), $n = 3$. Let $F$ be
totally real, $Q$ a totally positive definite nondegenerate ternary form over $\mathcal O_F$ with the good-prime shape
at every good $\mathfrak p$ (`hshape`), $T' \ne 0$ totally nonnegative, $x \ne 0$, $S \supseteq \{\mathfrak p \mid x\}$ finite,
$T'$ $\mathfrak p$-stable at every $\mathfrak p \in S$ with $T' \notin \mathfrak p^2$ at the good $\mathfrak p \in S$, and $P$, $P_m$
natural-order values of $\prod_\mathfrak p\beta_\mathfrak p(T')$, $\prod_\mathfrak p\beta_\mathfrak p(T'x^2)$. Then
$$\beta_\infty(T'x^2)P_m \;\ge\; \Lambda_3(T')\,N\big((x)_{\mathrm{Iso}}\big), \qquad
  \Lambda_3(T') = \beta_\infty(T')P\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \text{bad}}C'_\mathfrak p(T'),$$
"bad" meaning $\mathfrak p \mid 2\det H$ (the paper: $\mathfrak p \mid N$; for $n = 3$ every dyadic $\mathfrak p$ divides $N$).
*Update (as over $\mathbb{Q}$, `thm_5_7_a`):* the hypothesis "$T'$ not in a spinor square class" concerns $a_H$ and is
not needed. The second part of (a) is `thm_5_7_a_second_NF` (`NFGlobalLowerBound.lean`). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part, over F)"]
theorem thm_5_7_a_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2)
    {P Pm : ℝ} (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q T P *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x ≤
      aEWithNF Q (T * x ^ 2) Pm := by
  have h := aEWithNF_mul_sq_ge Q hQ hQnd le_rfl hT0 hT hx hS hst (IsGoodPrimeNF Q) (fun _ => 1)
    (fun v hv hG => ⟨one_pos, (localConstC'NF_good_three v hG (hshape v hG) (hT2 v hv hG)).ge⟩)
    hP hPm
  simp only [show 3 - 2 = 1 from rfl, pow_one, Finset.prod_const_one, mul_one] at h
  refine le_of_eq_of_le ?_ h
  ring

/-! ### Consistency with the rational theory ($F = \mathbb{Q}$) -/

section Rat

/-- $\mathbb{Q}$ has exactly one real place. -/
instance : Unique (RealPlace ℚ) where
  default := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

/-- The real embedding of $\mathbb{Q}$ is the cast. -/
theorem realEmb_rat (w : RealPlace ℚ) (x : ℚ) : realEmb w x = x := by
  rw [show realEmb w = Rat.castHom ℝ from Subsingleton.elim _ _]; rfl

theorem hessian_map_NF {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Q : QuadForm R n) :
    (Q.map f).hessian = Q.hessian.map f := by
  simp only [QuadForm.hessian, QuadForm.map]
  rw [Matrix.map_add _ (map_add f), Matrix.transpose_map]

/-- **$D_w = D$ over $\mathbb{Q}$:** for an integral form viewed over $\mathcal O_\mathbb{Q}$, the local determinant at the real
place is Hanke's $D = \det H/2^n$ (`gramDet`). -/
theorem gramDetNF_rat (Q : QuadForm ℤ n) (w : RealPlace ℚ) :
    gramDetNF (Q.map (Int.castRingHom (𝓞 ℚ))) w = gramDet Q := by
  rw [gramDetNF, gramDet, realForm, hessian_map_NF, hessian_map_NF, Matrix.map_map]
  congr 1
  have h := RingHom.map_det (((realEmb w).comp (algebraMap (𝓞 ℚ) ℚ)).comp (Int.castRingHom (𝓞 ℚ)))
    Q.hessian
  rw [RingHom.mapMatrix_apply] at h
  rw [show (⇑((realEmb w).comp (algebraMap (𝓞 ℚ) ℚ)) ∘ ⇑(Int.castRingHom (𝓞 ℚ))) =
      ⇑(((realEmb w).comp (algebraMap (𝓞 ℚ) ℚ)).comp (Int.castRingHom (𝓞 ℚ))) from rfl, ← h]
  simp

/-- **Consistency check over $\mathbb{Q}$ (archimedean side):** for an integral form $Q$ viewed over $\mathcal O_\mathbb{Q}$,
the number-field archimedean density is the rational one, $\beta_\infty^{F = \mathbb{Q}}(m) = \beta_\infty(m)$ (`betaInf`). With
`LocalDensity.NF.localDensity_rat` ($\beta_\mathfrak p = \beta_p$) this identifies the local factors of `aEWithNF` over
$\mathbb{Q}$ with those of `aEWith`. -/
@[kb "hanke2004" "(5.5), p. 369 (consistency, F = ℚ)"]
theorem betaInfNF_rat (Q : QuadForm ℤ n) (m : ℚ) :
    betaInfNF (Q.map (Int.castRingHom (𝓞 ℚ))) m = betaInf Q m := by
  rw [betaInfNF, Fintype.prod_unique, betaInfAt, gramDetNF_rat, realEmb_rat, betaInf]

/-- **Consistency check over $\mathbb{Q}$ (local product with a given value):**
`aEWithNF` over $\mathcal O_\mathbb{Q}$ at an integer $m$ is `aEWith`. -/
theorem aEWithNF_rat (Q : QuadForm ℤ n) (m : ℤ) (P : ℝ) :
    aEWithNF (Q.map (Int.castRingHom (𝓞 ℚ))) (m : 𝓞 ℚ) P = aEWith Q m P := by
  rw [aEWithNF, aEWith, show (((m : 𝓞 ℚ) : ℚ)) = (m : ℚ) by simp, betaInfNF_rat]
  push_cast; rfl

end Rat

end QuadFormsKB.Siegel

end
