/-
# A Hilbert cusp form with $T(p^2)$-type growth vanishes

**Setting.** $F$ totally real of degree $d = [F : \mathbb Q]$ ($d$ = `Fintype.card (InfinitePlace F)`), $\mathfrak N \ne 0$,
$f \in S_k(\Gamma_0(\mathfrak N), \chi)$ (`cuspFormChar`), with $q$-coefficients $a_\nu$ = `qCoeff f (koecherBasis 1) (realVec ν)`
($\nu \in \mathfrak d^{-1}$, the dual of the period lattice $\mathcal O_F$).

**Main theorem** (`eq_zero_of_growth`). If for some $e \in \mathbb N$ with $dk \le e$ and some $c > 0$, every $\nu$ satisfies
$$c\,p^{e}\,|a_\nu| \le |a_{p^2\nu}| \qquad\text{for all rational primes } p > P(\nu),$$
then $f = 0$.

**Use.** For $f = \theta_{\mathrm{Gen}} - E_Q$ in rank $n = 2k$, the $T(\mathfrak p^2)$ identities at the primes $\mathfrak p \mid p$
give $a_{p^2\nu} = \prod_{\mathfrak p \mid p}\lambda_\mathfrak p\,a_\nu$ with $|\lambda_\mathfrak p| \ge \frac12N\mathfrak p^{n-2}$
(`HilbertModular/SiegelHecke.lean`), so the hypothesis holds with $e = d(n-2)$ and $c = 2^{-d}$, and
$$e = d(n-2) = d(2k-2) \ge dk \iff k \ge 2 \iff n \ge 4.$$
**So the comparison works for every even $n \ge 4$ and every degree $d$** (for $n = 4$ with equality $e = dk$, where the
count of primes is what wins; for $n \ge 6$ with room to spare). It fails for $n = 2$ ($e = 0 < d$).

*Proof.* Suppose $a_{\nu_0} \ne 0$, $\nu_0 = $ `dualElt 1 m₀`. ($m_0 = 0$ is impossible: $c\,p^e|a_0| \le |a_0|$ for all large $p$.)
For $Y$ large the primes $p \in (Y/4, Y]$ (`Siegel.HeckeVanishing.primesQuarter`) exceed $P(\nu_0)$; the $\nu = p^2\nu_0$ are
distinct, with $\operatorname{Tr}\nu = p^2\operatorname{Tr}\nu_0 \le Y^2M$ ($M = \max(\operatorname{Tr}\nu_0, 1)$) and
$|a_\nu|^2 \ge c^2(Y/4)^{2e}|a_{\nu_0}|^2$. The trace-ordered mean-square bound
(`sum_sq_qCoeff_le_trace_of_cuspFormChar`: $\sum_{\operatorname{Tr}\nu \le X}|a_\nu|^2 \le C'X^{dk}$) gives
$$\#\{Y/4 < p \le Y\}\cdot c^2 4^{-2e}Y^{2e}|a_{\nu_0}|^2 \le C'M^{dk}Y^{2dk} \le C'M^{dk}Y^{2e},$$
so $\#\{Y/4 < p \le Y\}$ is bounded, against Chebyshev (`Siegel.HeckeVanishing.eventually_card_primesQuarter_ge`).
The abstract form is `coeff_eq_zero_of_growth`; then $f = 0$ by Fourier inversion (`hasSum_qExpansion`).

Over $\mathbb Q$ ($d = 1$, $n = 4$): `Siegel.HeckeVanishing.coeff_eq_zero_of_sq_growth`, the template.

Sources: Hecke's mean-square bound (Garrett 1990, Ch. 1 [unverified]); the vanishing argument is the one used over
$\mathbb Q$, an elementary substitute for the Ramanujan–Petersson bound (no published antecedent found).
-/
import QuadFormsKB.HilbertModular.CuspBound
import QuadFormsKB.Siegel.HeckeVanishing

open Filter Topology NumberField
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Siegel.HeckeVanishing

/-! ### The abstract growth lemma -/

section Abstract

variable {J : Type*}

/-- **Coefficients with $p^e$-growth along $p^2$-dilations and a mean-square bound $X^s$, $s \le e$, vanish.**
Let $a : \mathbb Z^J \to \mathbb C$ and $T : \mathbb Z^J \to \mathbb R$ with $T(p^2m) = p^2T(m)$, such that
* (mean square) $\sum_{m\in S}|a(m)|^2 \le C X^s$ for every $X > 0$ and finite $S$ with $T \le X$ on $S$;
* (growth) for every $m$ there is $P$ with $c\,p^e|a(m)| \le |a(p^2m)|$ for all primes $p > P$;
with $c > 0$, $0 \le s \le e$ and $e \ge 1$. Then $a = 0$. (Here $T$ is the trace, $s = dk$.) -/
@[kb "iwaniec1997" "mean-square vs. prime count; vanishing argument as over Q, here over F"]
theorem coeff_eq_zero_of_growth (a : (J → ℤ) → ℂ) (T : (J → ℤ) → ℝ)
    (hT : ∀ (p : ℕ) (m : J → ℤ), T (((p : ℤ) ^ 2) • m) = (p : ℝ) ^ 2 * T m)
    {s C : ℝ} (hs : 0 ≤ s)
    (hpars : ∀ X : ℝ, 0 < X → ∀ S : Finset (J → ℤ), (∀ m ∈ S, T m ≤ X) → ∑ m ∈ S, ‖a m‖ ^ 2 ≤ C * X ^ s)
    {e : ℕ} (hse : s ≤ e) (he : 1 ≤ e) {c : ℝ} (hc : 0 < c)
    (hgrow : ∀ m, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P < p → c * (p : ℝ) ^ e * ‖a m‖ ≤ ‖a (((p : ℤ) ^ 2) • m)‖)
    (m₀ : J → ℤ) : a m₀ = 0 := by
  classical
  by_contra ha
  have hδ : 0 < ‖a m₀‖ := norm_pos_iff.mpr ha
  obtain ⟨P, hP⟩ := hgrow m₀
  by_cases hm0 : m₀ = 0
  · -- `c p^e |a 0| ≤ |a 0|` for all large primes is impossible
    subst hm0
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (P + ⌈1 / c⌉₊ + 2)
    have h := hP p hp (by omega)
    rw [smul_zero] at h
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hcp : 1 < c * p := by
      have h1 : 1 / c < p := by
        have := Nat.le_ceil (1 / c)
        have h2 : (⌈1 / c⌉₊ : ℝ) + 2 ≤ p := by exact_mod_cast (by omega : ⌈1 / c⌉₊ + 2 ≤ p)
        linarith
      rwa [div_lt_iff₀ hc, mul_comm] at h1
    have hpe : (p : ℝ) ≤ (p : ℝ) ^ e := by
      calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℝ) ^ e := pow_le_pow_right₀ hp1 he
    have : 1 < c * (p : ℝ) ^ e := lt_of_lt_of_le hcp (mul_le_mul_of_nonneg_left hpe hc.le)
    nlinarith
  -- the main case `m₀ ≠ 0`
  set δ := ‖a m₀‖ ^ 2 with hδdef
  have hδ2 : 0 < δ := by positivity
  set M : ℝ := max (T m₀) 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := |C| * M ^ s * 4 ^ (2 * e) / (c ^ 2 * δ) with hKdef
  obtain ⟨Y, hYB, hYge⟩ := ((eventually_card_primesQuarter_ge (K + 1)).and
    (eventually_ge_atTop (4 * (P + 1)))).exists
  set S := primesQuarter Y with hSdef
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
  have hbig : ∀ p ∈ S, P < p := by
    intro p hp
    have := (mem_primesQuarter.mp hp).1
    omega
  -- injectivity of `p ↦ p² m₀`
  obtain ⟨j₀, hj₀⟩ : ∃ j, m₀ j ≠ 0 := by
    by_contra h; push Not at h; exact hm0 (funext h)
  have hinj : Set.InjOn (fun p : ℕ => ((p : ℤ) ^ 2) • m₀) S := by
    intro p _ q _ h
    have := congrFun h j₀
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (p : ℤ) ^ 2 = (q : ℤ) ^ 2 := mul_right_cancel₀ hj₀ this
    have h3 : p ^ 2 = q ^ 2 := by exact_mod_cast h2
    exact Nat.pow_left_injective (by norm_num) h3
  -- traces
  have htr : ∀ m ∈ S.image (fun p : ℕ => ((p : ℤ) ^ 2) • m₀), T m ≤ (Y : ℝ) ^ 2 * M := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    rw [hT]
    have hpY : (p : ℝ) ≤ Y := by exact_mod_cast (mem_primesQuarter.mp hp).2.1
    have h1 : (p : ℝ) ^ 2 * T m₀ ≤ (p : ℝ) ^ 2 * M :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have h2 : (p : ℝ) ^ 2 * M ≤ (Y : ℝ) ^ 2 * M :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hpY 2) hM.le
    linarith
  have hX : (0 : ℝ) < (Y : ℝ) ^ 2 * M := by positivity
  have hsum := hpars _ hX _ htr
  rw [Finset.sum_image (f := fun m => ‖a m‖ ^ 2) hinj] at hsum
  -- lower bound for each prime
  have hlow : ∀ p ∈ S, c ^ 2 * ((Y : ℝ) / 4) ^ (2 * e) * δ ≤ ‖a (((p : ℤ) ^ 2) • m₀)‖ ^ 2 := by
    intro p hp
    have hp' := mem_primesQuarter.mp hp
    have hr := hP p hp'.2.2 (hbig p hp)
    have hpY : (Y : ℝ) / 4 ≤ p := by
      rw [div_le_iff₀ (by norm_num)]
      exact_mod_cast (by omega : Y ≤ p * 4)
    have h4 : ((Y : ℝ) / 4) ^ (2 * e) ≤ (p : ℝ) ^ (2 * e) := pow_le_pow_left₀ (by positivity) hpY _
    have hsq : (c * (p : ℝ) ^ e * ‖a m₀‖) ^ 2 ≤ ‖a (((p : ℤ) ^ 2) • m₀)‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr 2
    calc c ^ 2 * ((Y : ℝ) / 4) ^ (2 * e) * δ ≤ c ^ 2 * (p : ℝ) ^ (2 * e) * δ := by gcongr
      _ = (c * (p : ℝ) ^ e * ‖a m₀‖) ^ 2 := by rw [hδdef, pow_mul]; ring
      _ ≤ _ := hsq
  have hlowsum : (S.card : ℝ) * (c ^ 2 * ((Y : ℝ) / 4) ^ (2 * e) * δ) ≤
      ∑ p ∈ S, ‖a (((p : ℤ) ^ 2) • m₀)‖ ^ 2 := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hlow
  -- upper bound `C (Y² M)^s ≤ |C| M^s Y^{2e}`
  have hupper : C * ((Y : ℝ) ^ 2 * M) ^ s ≤ |C| * M ^ s * (Y : ℝ) ^ (2 * e) := by
    have h1 : C * ((Y : ℝ) ^ 2 * M) ^ s ≤ |C| * ((Y : ℝ) ^ 2 * M) ^ s :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2 : ((Y : ℝ) ^ 2 * M) ^ s = ((Y : ℝ) ^ 2) ^ s * M ^ s :=
      Real.mul_rpow (by positivity) hM.le
    have h3 : ((Y : ℝ) ^ 2) ^ s ≤ (Y : ℝ) ^ (2 * e) := by
      have e2 : (Y : ℝ) ^ (2 * e) = ((Y : ℝ) ^ 2) ^ (e : ℝ) := by
        rw [Real.rpow_natCast, ← pow_mul]
      rw [e2]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hY1) hse
    calc C * ((Y : ℝ) ^ 2 * M) ^ s ≤ |C| * (((Y : ℝ) ^ 2) ^ s * M ^ s) := by rw [← h2]; exact h1
      _ ≤ |C| * ((Y : ℝ) ^ (2 * e) * M ^ s) := by
          gcongr
      _ = _ := by ring
  have hchain := hlowsum.trans (hsum.trans hupper)
  have hY0 : (0 : ℝ) < (Y : ℝ) ^ (2 * e) := by positivity
  have e1 : (S.card : ℝ) * (c ^ 2 * ((Y : ℝ) / 4) ^ (2 * e) * δ) =
      ((S.card : ℝ) * (c ^ 2 * δ) / 4 ^ (2 * e)) * (Y : ℝ) ^ (2 * e) := by
    rw [div_pow]; field_simp
  rw [e1] at hchain
  have hle : (S.card : ℝ) * (c ^ 2 * δ) / 4 ^ (2 * e) ≤ |C| * M ^ s :=
    le_of_mul_le_mul_right (by linarith) hY0
  have hcard : (S.card : ℝ) ≤ K := by
    rw [hKdef, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  linarith

end Abstract

/-! ### Hilbert cusp forms -/

section Cusp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- $\nu_{cm} = c\,\nu_m$ for the dual lattice points `dualElt I m`. -/
lemma dualElt_zsmul (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (c : ℤ) (m : Fin (Module.finrank ℚ F) → ℤ) :
    QuadFormsKB.Analysis.dualElt I (c • m) = (c : F) * QuadFormsKB.Analysis.dualElt I m := by
  simp only [QuadFormsKB.Analysis.dualElt, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma mem_one_units {x : F} : x ∈ (((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) ↔ ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = x := by
  rw [Units.val_one]; exact FractionalIdeal.mem_one_iff _

lemma exists_latElt_eq (a : 𝓞 F) : ∃ k, QuadFormsKB.Analysis.latElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) k = (a : F) := by
  have ha : (a : F) ∈ (((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F) := mem_one_units.mpr ⟨a, rfl⟩
  obtain ⟨k, hk⟩ := (QuadFormsKB.Analysis.latEquiv (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)).surjective ⟨_, ha⟩
  refine ⟨k, ?_⟩
  rw [← QuadFormsKB.Analysis.latEquiv_coe, hk]

/-- **The dual lattice $\mathfrak d^{-1}$:** $y = \nu_m$ for some $m \in \mathbb Z^d$ iff $\operatorname{Tr}(b_iy) \in \mathbb Z$ for the basis $b_i$ of $\mathcal O_F$. -/
lemma exists_dualElt_iff (y : F) :
    (∃ m, QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m = y) ↔
      ∀ i, ∃ k : ℤ, Algebra.trace ℚ F (QuadFormsKB.Analysis.bq (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) i * y) = k := by
  constructor
  · rintro ⟨m, rfl⟩ i
    exact ⟨m i, QuadFormsKB.Analysis.trace_bq_mul_dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) i m⟩
  · intro h
    choose k hk using h
    refine ⟨k, ?_⟩
    have hrepr := ((QuadFormsKB.Analysis.bq (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)).traceDual).sum_repr y
    conv_rhs => rw [← hrepr]
    rw [QuadFormsKB.Analysis.dualElt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm y, hk i,
      Algebra.smul_def]
    simp

/-- $\mathfrak d^{-1}$ is an $\mathcal O_F$-module: $t\,\nu_m = \nu_{m'}$ for $t \in \mathcal O_F$. -/
lemma exists_dualElt_mul (t : 𝓞 F) (m : Fin (Module.finrank ℚ F) → ℤ) :
    ∃ m', QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m' = (t : F) * QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m := by
  rw [exists_dualElt_iff]
  intro i
  obtain ⟨b, hb⟩ := mem_one_units.mp (bq_mem (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) i)
  obtain ⟨k, hk⟩ := exists_latElt_eq (b * t)
  refine ⟨∑ j, k j * m j, ?_⟩
  rw [← mul_assoc, ← hb, show (algebraMap (𝓞 F) F b * (t : F)) = ((b * t : 𝓞 F) : F) by push_cast; rfl,
    ← hk, QuadFormsKB.Analysis.latElt, Finset.sum_mul, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, show ((k j : F)) = algebraMap ℚ F (k j) by simp, ← Algebra.smul_def, LinearMap.map_smul,
    QuadFormsKB.Analysis.trace_bq_mul_dualElt, smul_eq_mul]
/-- **A Hilbert cusp form with $T(p^2)$-type growth vanishes** (all degrees $d$, all $k$ with $dk \le e$). Let
$f \in S_k(\Gamma_0(\mathfrak N), \chi)$, $\mathfrak N \ne 0$, with $q$-coefficients $a_\nu$ = `qCoeff f (koecherBasis 1) (realVec ν)`. If
$c > 0$, $e \ge 1$, $dk \le e$ ($d$ = `Fintype.card (InfinitePlace F)`), and for every $\nu \in \mathfrak d^{-1}$ (`dualElt 1 m`) there is $P$ with
$$c\,p^e\,|a_\nu| \le |a_{p^2\nu}| \qquad(p > P \text{ prime}),$$
then $f = 0$. -/
@[kb "iwaniec1997" "Hecke mean square vs. Chebyshev, over F"]
theorem eq_zero_of_growth {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℕ}
    {f : (InfinitePlace F → UpperHalfPlane) → ℂ} (hf : f ∈ cuspFormChar 𝔑 χ (k : ℤ))
    {e : ℕ} (he : 1 ≤ e) (hke : Fintype.card (InfinitePlace F) * k ≤ e) {c : ℝ} (hc : 0 < c)
    (hgrow : ∀ m : Fin (Module.finrank ℚ F) → ℤ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P < p →
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
    refine coeff_eq_zero_of_growth a
      (fun m => ((Algebra.trace ℚ F (QuadFormsKB.Analysis.dualElt 1 m) : ℚ) : ℝ)) ?_
      (s := (Fintype.card (InfinitePlace F) : ℝ) * ((k : ℤ) : ℝ)) (by positivity)
      (C := Real.exp (4 * π) * C ^ 2) ?_ (e := e) ?_ he hc ?_
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
      refine ⟨P, fun p hp hpP => ?_⟩
      have h := hP p hp hpP
      simp only [hadef]
      rw [dualElt_zsmul]
      push_cast
      exact h
  -- Fourier inversion
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

end Cusp

/-! ### Chaining the $T(\mathfrak p^2)$ relations at the primes above a rational prime -/

section Chaining

variable {F : Type} [Field F] [NumberField F]

/-- $\nu \in F$ is a unit at the prime $(\pi)$: $\nu = x/y$ with $\pi \nmid x$, $\pi \nmid y$. -/
def IsUnitAt (ϖ : 𝓞 F) (ν : F) : Prop := ∃ x y : 𝓞 F, ¬ ϖ ∣ x ∧ ¬ ϖ ∣ y ∧ ν * (y : F) = x

lemma IsUnitAt.sq_mul {ϖ t : 𝓞 F} (hϖ : Prime ϖ) {ν : F} (h : IsUnitAt ϖ ν) (ht : ¬ ϖ ∣ t) :
    IsUnitAt ϖ ((t : F) ^ 2 * ν) := by
  obtain ⟨x, y, hx, hy, he⟩ := h
  refine ⟨t ^ 2 * x, y, fun h' => ?_, hy, ?_⟩
  · rcases hϖ.dvd_or_dvd h' with h'' | h''
    · exact ht (hϖ.dvd_of_dvd_pow h'')
    · exact hx h''
  · push_cast; rw [mul_assoc, he]

/-- The absolute norm $N(t) = [\mathcal O_F : t\mathcal O_F]$. -/
noncomputable abbrev nm (t : 𝓞 F) : ℕ := Ideal.absNorm (Ideal.span {t})

lemma nm_mul (a b : 𝓞 F) : nm (a * b) = nm a * nm b := by
  simp only [nm, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma nm_eq_one_iff (t : 𝓞 F) : nm t = 1 ↔ IsUnit t := by
  rw [nm, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]

lemma dvd_nm (t : 𝓞 F) : t ∣ ((nm t : ℕ) : 𝓞 F) := by
  have := Ideal.absNorm_mem (Ideal.span {t})
  rwa [Ideal.mem_span_singleton] at this

lemma nm_natCast (p : ℕ) : nm (p : 𝓞 F) = p ^ Module.finrank ℤ (𝓞 F) := by
  rw [nm, Ideal.absNorm_span_singleton, show ((p : 𝓞 F)) = algebraMap ℤ (𝓞 F) (p : ℤ) by simp,
    Algebra.norm_algebraMap]
  simp

/-- A prime $\pi \mid p$ divides an integer $k$ only if $p \mid k$. -/
lemma dvd_of_prime_dvd {ϖ : 𝓞 F} (hϖ : Prime ϖ) {p : ℕ} (hp : p.Prime) (hϖp : ϖ ∣ (p : 𝓞 F)) {k : ℕ}
    (hk : ϖ ∣ (k : 𝓞 F)) : p ∣ k := by
  by_contra h
  have hc : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).mpr h
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * k = 1 := by
    have := Nat.isCoprime_iff_coprime.mpr hc
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, h⟩
  have h1 : ϖ ∣ ((a * p + b * k : ℤ) : 𝓞 F) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖp _) (dvd_mul_of_dvd_right hk _)
  rw [hab] at h1
  exact hϖ.not_isUnit (isUnit_of_dvd_one (by simpa using h1))

lemma le_nm {ϖ : 𝓞 F} (hϖ : Prime ϖ) {p : ℕ} (hp : p.Prime) (hϖp : ϖ ∣ (p : 𝓞 F)) : p ≤ nm ϖ := by
  have h := dvd_of_prime_dvd hϖ hp hϖp (dvd_nm ϖ)
  refine Nat.le_of_dvd ?_ h
  rw [Nat.pos_iff_ne_zero, nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hϖ.ne_zero


/-- **Unramified primes are squarefree:** if $p \nmid \operatorname{disc}(F)$ then no prime $\pi$ of $\mathcal O_F$ has
$\pi^2 \mid p$ (Dedekind; Mathlib's `NumberField.not_dvd_discr_iff_forall_mem`: $e(\pi \mid p) = 1$, while $\pi^2 \mid p$ would
give $e \ge 2$). -/
theorem not_sq_dvd_of_not_dvd_discr {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) {ϖ : 𝓞 F}
    (hϖ : Prime ϖ) : ¬ ϖ ^ 2 ∣ (p : 𝓞 F) := by
  intro h
  set P := Ideal.span {ϖ} with hP
  have hPp : P.IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmem : ((p : ℤ) : 𝓞 F) ∈ P := by
    rw [hP, Ideal.mem_span_singleton]
    push_cast
    exact (dvd_pow_self ϖ two_ne_zero).trans h
  haveI := ((NumberField.not_dvd_discr_iff_forall_mem F (𝓞 F) hpZ).mp hd) P hPp hmem
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hPtop : P ≠ ⊤ := hPp.ne_top
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hPtop hpZ).mpr (by simpa using hmem)
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((p : ℤ) : 𝓞 F)} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  have hp0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have h1 := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(p : ℤ)}) P hp0
  rw [he] at h1
  have hdvd : P ^ 2 ∣ (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) := by
    rw [hmap, hP, Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    push_cast; exact h
  have h2 := le_emultiplicity_of_pow_dvd hdvd
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
    ((Ideal.prime_of_isPrime (by simpa [hP] using hϖ.ne_zero) hPp).irreducible) hp0, normalize_eq, ← h1] at h2
  norm_num at h2

variable [IsPrincipalIdealRing (𝓞 F)] {a : F → ℂ} {lam : 𝓞 F → ℂ} {m₀ w : ℕ} {c₀ : ℝ}
  {D : F → Prop} (hD : ∀ (t : 𝓞 F) (ν : F), D ν → D ((t : F) * ν))

include hD in
/-- **Chaining the $T(\mathfrak p^2)$ relations over the primes above $p$** ($\mathcal O_F$ a PID). Suppose that for every prime
$\pi$ of $\mathcal O_F$ with $\pi \nmid m_0$ and every $\nu$ that is a unit at $\pi$ (`IsUnitAt`),
$a(\pi^2\nu) = \lambda(\pi)\,a(\nu)$ with $|\lambda(\pi)| \ge c_0N(\pi)^w$, $0 < c_0 \le 1$. Then for a rational prime $p \nmid m_0\,\mathrm{disc}(F)$
and $\nu$ a unit at every $\pi \mid p$:
$$c_0^d\,p^{dw}\,|a(\nu)| \le |a(p^2\nu)|,\qquad d = [F : \mathbb Q].$$
*Proof.* $p = \pi_1\cdots\pi_g$ is squarefree (`not_sq_dvd_of_not_dvd_discr`); induct on the norm of a divisor $t \mid p$, peeling
off one prime factor $\pi$ of $t = \pi s$ at a time ($s^2\nu$ is a unit at $\pi$ since $\pi \nmid s$), and use
$N(\pi) \ge p$, $N(p) = p^d$. -/
@[kb "shimura1978" "T(𝔭²) at the primes above p (Hecke operators over F) [unverified]"]
theorem norm_coeff_sq_mul_ge (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1)
    (hrel : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → ∀ ν : F, D ν → IsUnitAt ϖ ν →
      a ((ϖ : F) ^ 2 * ν) = lam ϖ * a ν)
    (hlam : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → c₀ * (nm ϖ : ℝ) ^ w ≤ ‖lam ϖ‖)
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) (hpm : ¬ p ∣ m₀) {ν : F} (hDν : D ν)
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
      have hϖ : Prime ϖ := hϖi.prime
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

omit [IsPrincipalIdealRing (𝓞 F)] in
lemma finrank_eq_card_infinitePlace [IsTotallyReal F] :
    Module.finrank ℤ (𝓞 F) = Fintype.card (InfinitePlace F) := by
  rw [RingOfIntegers.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, IsTotallyReal.nrComplexPlaces_eq_zero]

include hD in
/-- **The growth hypothesis of `eq_zero_of_growth` from the $T(\mathfrak p^2)$ relations**: under the hypotheses of
`norm_coeff_sq_mul_ge` (with $m_0 \ge 1$) and $a(0) = 0$, every $\nu \in F$ has $P$ such that
$c_0^d\,p^{dw}\,|a(\nu)| \le |a(p^2\nu)|$ for all primes $p > P$. ($P$ exceeds $m_0$, $|\mathrm{disc}(F)|$ and the norms of a
numerator and denominator of $\nu$.) -/
theorem exists_growth_of_rel (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1) (hm₀ : 0 < m₀)
    (hrel : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → ∀ ν : F, D ν → IsUnitAt ϖ ν →
      a ((ϖ : F) ^ 2 * ν) = lam ϖ * a ν)
    (hlam : ∀ ϖ : 𝓞 F, Prime ϖ → ¬ ϖ ∣ (m₀ : 𝓞 F) → c₀ * (nm ϖ : ℝ) ^ w ≤ ‖lam ϖ‖)
    (h0 : a 0 = 0) (ν : F) (hDν : D ν) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P < p →
      c₀ ^ Module.finrank ℤ (𝓞 F) * (p : ℝ) ^ (Module.finrank ℤ (𝓞 F) * w) * ‖a ν‖ ≤
        ‖a ((p : F) ^ 2 * ν)‖ := by
  by_cases hν : ν = 0
  · refine ⟨0, fun p _ _ => ?_⟩
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
  refine ⟨m₀ + nm x + nm y + (discr F).natAbs, fun p hp hpP => ?_⟩
  refine norm_coeff_sq_mul_ge hD hc₀ hc₁ hrel hlam hp ?_ ?_ hDν ?_
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

/-! ### The vanishing theorem from the $T(\mathfrak p^2)$ relations -/

section HeckeRel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **A Hilbert cusp form of weight $k \ge 2$ whose coefficients satisfy $T(\mathfrak p^2)$ relations with
$|\lambda_\mathfrak p| \ge \tfrac12N\mathfrak p^{2k-2}$ vanishes** (every totally real $F$ with $\mathcal O_F$ a PID, every degree $d$).
Let $f \in S_k(\Gamma_0(\mathfrak N), \chi)$, $a_\nu$ = `qCoeff f (koecherBasis 1) (realVec ν)`, $m_0 \ge 1$, and suppose that for every
prime $\pi \nmid m_0$ of $\mathcal O_F$ and every $\nu \in \mathfrak d^{-1}$ (`dualElt 1 m`) that is a unit at $\pi$,
$$a_{\pi^2\nu} = \lambda(\pi)\,a_\nu,\qquad |\lambda(\pi)| \ge \tfrac12N(\pi)^{2k-2}.$$
Then $f = 0$. *Proof:* `exists_growth_of_rel` gives the growth with $e = d(2k-2) \ge dk$ ($k \ge 2$) and $c = 2^{-d}$;
`eq_zero_of_growth` concludes. This is the case $n = 2k$ of the Eichler eigenvalue $\lambda_\mathfrak p = q^{n-2} + \varepsilon q^{k-1} + 1$,
$|\lambda_\mathfrak p| \ge q^{n-2} - q^{k-1} + 1 \ge \tfrac12 q^{n-2}$. -/
@[kb "iwaniec1997" "vanishing over F from T(𝔭²) relations"]
theorem eq_zero_of_heckeRel {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {k : ℕ}
    (hk : 2 ≤ k) {f : (InfinitePlace F → UpperHalfPlane) → ℂ} (hf : f ∈ cuspFormChar 𝔑 χ (k : ℤ))
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
  have hd1 : 1 ≤ Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  refine eq_zero_of_growth h𝔑 hf (e := Module.finrank ℤ (𝓞 F) * (2 * k - 2)) ?_ ?_
    (c := (1 / 2) ^ Module.finrank ℤ (𝓞 F)) (by positivity) ?_
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [← hd]; exact Nat.mul_le_mul_left _ (by omega)
  · intro m
    refine exists_growth_of_rel (a := fun ν => qCoeff f b (realVec ν))
      (D := fun ν => ∃ m', QuadFormsKB.Analysis.dualElt 1 m' = ν)
      (fun t ν ⟨m', hm'⟩ => by rw [← hm']; exact exists_dualElt_mul t m') (by norm_num) (by norm_num)
      hm₀ (fun ϖ hϖ hϖm ν ⟨m', hm'⟩ hu => by subst hm'; exact hrel ϖ hϖ hϖm m' hu) (fun ϖ hϖ hϖm => by
        have := hlam ϖ hϖ hϖm; linarith) h0 _ ⟨m, rfl⟩

end HeckeRel

end QuadFormsKB.HilbertModular
