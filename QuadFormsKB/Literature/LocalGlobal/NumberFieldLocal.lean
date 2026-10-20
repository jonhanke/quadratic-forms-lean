/-
# Local facts at the places of a number field $F$

What the Hasse–Minkowski proof over $F$ needs at the completions $F_v$, beyond the input
`NFInputs.hilbertSymbol_mul_left_finite_nf`:

1. at an infinite place ($F_w \cong \mathbb{R}$ or $\mathbb{C}$) the Hilbert symbol is
   multiplicative (from the $\mathbb{R}$ case; trivial over $\mathbb{C}$);
2. at a finite place $\mathfrak{p} \nmid 2$, a diagonal form with at least three unit
   coefficients is isotropic (Chevalley–Warning over the residue field $\mathcal{O}_F/\mathfrak{p}$,
   then Hensel's lemma);
3. only finitely many finite places lie above $2$ or make a given coefficient a non-unit;
4. **weak approximation**: given local splittings $t_v$ at finitely many places, one global $t$
   works at all of them simultaneously (Lam VI §3; this replaces the Dirichlet-prime step of
   Serre's $\mathbb{Q}$ proof).

None of these is a class-field-theory input; all should be provable from Mathlib.
Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.NumberFieldInputs
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open NumberField IsDedekindDomain

namespace QuadFormsKB.NFLocal

variable {F : Type} [Field F] [NumberField F]

/-- **The Hilbert symbol at an infinite place is multiplicative:** for an infinite place $w$ of $F$
and $a, b, c \in F_w^\times$, $(ab, c)_w = (a, c)_w \, (b, c)_w$. ($F_w \cong \mathbb{R}$ reduces to
`hilbertSymbol_real_mul_left`; for $F_w \cong \mathbb{C}$ every symbol is $1$.) -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 [unverified]"]
theorem hilbertSymbol_mul_left_infinite_nf (w : InfinitePlace F) (a b c : w.Completion)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol w.Completion (a * b) c =
      hilbertSymbol w.Completion a c * hilbertSymbol w.Completion b c := by
  have transport : ∀ {K L : Type} [Field K] [Field L] (e : K ≃+* L) (a b : K),
      hilbertSymbol K a b = hilbertSymbol L (e a) (e b) := by
    intro K L _ _ e a b
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨e x, e y, e z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.injective] at h0 ⊢
        exact h0
      · rw [← map_pow, h]; simp
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨e.symm x, e.symm y, e.symm z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.symm.injective] at h0 ⊢
        exact h0
      · apply e.injective
        simp [h]
  have hC : ∀ a b : ℂ, hilbertSymbol ℂ a b = 1 := by
    intro a b
    unfold hilbertSymbol
    rw [if_pos]
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
    exact ⟨1, 0, s, by simp, by simp [hs]⟩
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    rw [transport e, transport e a, transport e b, map_mul]
    exact HilbertLocal.hilbertSymbol_real_mul_left _ _ _
      ((map_ne_zero_iff _ e.injective).2 ha) ((map_ne_zero_iff _ e.injective).2 hb)
      ((map_ne_zero_iff _ e.injective).2 hc)
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    rw [transport e, transport e a, transport e b, hC, hC, hC]
    norm_num

/-- **Residue step:** for a nonzero prime $\mathfrak{p}$ of $\mathcal{O}_F$ and
$b_0, b_1, b_2 \in \mathcal{O}_F \setminus \mathfrak{p}$, some $x, y \in \mathcal{O}_F$ satisfy
$b_0 x^2 + b_1 y^2 + b_2 \in \mathfrak{p}$.

*Proof* (Serre I §2.2, Cor. 2 of Chevalley–Warning; or counting). The residue field
$k = \mathcal{O}_F/\mathfrak{p}$ is finite (`Ideal.finite_quotient`-type results for number rings), say
$|k| = q$. If $q$ is odd, $\{b_0 x^2\}$ and $\{-b_2 - b_1 y^2\}$ each have $(q+1)/2$ elements of $k$, so
they meet (pigeonhole). If $q$ is even, every element of $k$ is a square, so take $y = 0$ and
$x^2 = -b_2/b_0$. Lift $x, y$ from $k$ to $\mathcal{O}_F$ (`Ideal.Quotient.mk_surjective`). Alternatively,
Mathlib's `char_dvd_card_solutions` (Chevalley–Warning) gives a nonzero zero of
$b_0 X^2 + b_1 Y^2 + b_2 Z^2$ over $k$. -/
@[kb "serre1973" "Ch. I §2.2, Cor. 2 [unverified]"]
theorem exists_sum_sq_mem_nf (v : HeightOneSpectrum (𝓞 F)) (b₀ b₁ b₂ : 𝓞 F)
    (h₀ : b₀ ∉ v.asIdeal) (h₁ : b₁ ∉ v.asIdeal) (h₂ : b₂ ∉ v.asIdeal) :
    ∃ x y : 𝓞 F, b₀ * x ^ 2 + b₁ * y ^ 2 + b₂ ∈ v.asIdeal := by
  classical
  haveI := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set q := Ideal.Quotient.mk v.asIdeal
  have B0 : q b₀ ≠ 0 := fun h => h₀ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have B1 : q b₁ ≠ 0 := fun h => h₁ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∃ X Y : 𝓞 F ⧸ v.asIdeal, q b₀ * X ^ 2 + q b₁ * Y ^ 2 + q b₂ = 0 := by
    by_cases hc : ringChar (𝓞 F ⧸ v.asIdeal) = 2
    · obtain ⟨X, hX⟩ := FiniteField.isSquare_of_char_two hc (-q b₂ / q b₀)
      refine ⟨X, 0, ?_⟩
      have : q b₀ * X ^ 2 = - q b₂ := by
        rw [pow_two, ← hX]; field_simp
      rw [this]; ring
    · have hodd : Fintype.card (𝓞 F ⧸ v.asIdeal) % 2 = 1 := by
        have := mt FiniteField.even_card_iff_char_two.mpr hc
        omega
      have hf : (Polynomial.C (q b₀) * Polynomial.X ^ 2).degree = 2 :=
        Polynomial.degree_C_mul_X_pow 2 B0
      have hg : (Polynomial.C (q b₁) * Polynomial.X ^ 2 + Polynomial.C (q b₂)).degree = 2 := by
        rw [Polynomial.degree_add_C, Polynomial.degree_C_mul_X_pow 2 B1]
        · rfl
        rw [Polynomial.degree_C_mul_X_pow 2 B1]; norm_num
      obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
      refine ⟨a, b, ?_⟩
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] at hab
      rw [← hab]; ring
  obtain ⟨X, Y, hXY⟩ := key
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective X
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
  refine ⟨x, y, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa [q, map_add, map_mul, map_pow] using hXY

/-- **Hensel step:** at a non-dyadic finite place ($2 \notin \mathfrak{p}$), an element $c \in F$ with
$v_{\mathfrak{p}}(c - 1) > 0$ (i.e. $c \equiv 1 \bmod \mathfrak{p}$) is a square in $F_{\mathfrak{p}}$.

*Proof* (Serre II §3.3, Thm. 3; Hensel's lemma). The polynomial $f(X) = X^2 - c$ over the complete
DVR $\widehat{\mathcal{O}}_{\mathfrak{p}}$ (`v.adicCompletionIntegers F`) has the approximate root $X = 1$:
$f(1) = 1 - c \in \mathfrak{p}$ while $f'(1) = 2$ is a unit because $2 \notin \mathfrak{p}$. Hensel's lemma
(Mathlib: `HenselianLocalRing`, which holds for complete local rings, or Newton iteration via
`Polynomial.exists_aeval_eq_zero_of_..`/`hensels_lemma`-style results for complete normed rings) gives a root.
Note $\|\cdot\|$ on $F_{\mathfrak{p}}$ satisfies $\|x\| < 1 \iff v(x) < 1$ (`Valued.toNormedField`). -/
@[kb "serre1973" "Ch. II §3.3, Thm. 3 [unverified]"]
theorem isSquare_of_valuation_sub_one_lt_nf (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (c : F) (hc : v.valuation F (c - 1) < 1) :
    IsSquare (algebraMap F (v.adicCompletion F) c) := by
  set K := v.adicCompletion F
  have hv : ∀ x : F, Valued.v (algebraMap F K x) = v.valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hn2 : ‖(2:K)‖ = 1 := by
    rw [Valued.toNormedField.norm_eq_one_iff]
    have : (2:K) = algebraMap F K (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
    rw [this, hv, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr h2
  have h2K : (2:K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn2; exact zero_ne_one hn2
  set e : K := algebraMap F K c - 1 with he
  have hr : ‖e‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, he, ← map_one (algebraMap F K), ← map_sub, hv]
    exact hc
  set r := ‖e‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  let f : K → K := fun y => (e - y^2)/2
  let s := Metric.closedBall (0:K) r
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div, hn2, div_one]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg, norm_pow]
    have := mul_le_mul hy hy (norm_nonneg y) hr0
    nlinarith
  have hcon : ContractingWith ‖e‖₊ (hmaps.restrict f s s) := by
    refine ⟨hr, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ (‖e‖₊ : ℝ) * dist (y:K) y'
    simp only [f, coe_nnnorm]
    rw [dist_eq_norm, dist_eq_norm]
    have : (e - (y:K)^2)/2 - (e - (y':K)^2)/2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, hn2, div_one]
    have : ‖(y:K) + y'‖ ≤ r := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hy')
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s, hr0]) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = e - y^2 := by
    have h3 : (2:K) * ((e - y^2)/2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2K] at h3
    exact h3.symm
  rw [he] at h2'
  linear_combination -h2'

/-- **Unit forms of rank $\ge 3$ at a non-dyadic finite place are isotropic:** let $\mathfrak{p}$ be a
nonzero prime of $\mathcal{O}_F$ with $2 \notin \mathfrak{p}$, and let $a_0, \dots, a_{m-1} \in F$
($m \ge 3$) all have $\mathfrak{p}$-adic valuation $0$ (units at $\mathfrak{p}$). Then
$\langle a_0, \dots, a_{m-1} \rangle$ is isotropic over $F_{\mathfrak{p}}$. (The $\mathbb{Q}_p$ case
is `RankFive.isotropic_padic_unit_ternary`.)

*Proof* (Serre IV §2.2 for $\mathbb{Q}_p$; O'Meara §63). By `FieldGen.isotropicIn_diag_of_prefix` it
suffices to treat $m = 3$. Scale each $a_i$ by a square so it lies in $\mathcal{O}_F \setminus \mathfrak{p}$
(a unit at $\mathfrak{p}$ is $b/s$ with $b, s \in \mathcal{O}_F \setminus \mathfrak{p}$, and
$b/s = bs/s^2$); scaling by squares does not change isotropy. By `exists_sum_sq_mem_nf` pick
$x, y \in \mathcal{O}_F$ with $b_0 x^2 + b_1 y^2 + b_2 \in \mathfrak{p}$. Then
$c = -(b_0 x^2 + b_1 y^2)/b_2 \equiv 1 \bmod \mathfrak{p}$, so $c = z^2$ in $F_{\mathfrak{p}}$ by
`isSquare_of_valuation_sub_one_lt_nf`, and $(x, y, z) \ne 0$ is a zero of
$\langle b_0, b_1, b_2 \rangle$. -/
@[kb "omeara1963" "§63 [unverified]"]
theorem isotropic_diag_units_nf (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (m : ℕ) (hm : 3 ≤ m) (a : Fin m → F) (ha : ∀ i, v.valuation F (a i) = 1) :
    (QuadForm.diag a).IsotropicIn (v.adicCompletion F) := by
  have rep : ∀ x : F, v.valuation F x = 1 → ∃ t s : 𝓞 F, s ∉ v.asIdeal ∧ t ∉ v.asIdeal ∧ x = algebraMap _ F t / algebraMap _ F s := by
    intro x hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd0' : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
    have hvd0 : v.intValuation d ≠ 0 := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]; simpa using hd0
    have hvn : v.intValuation n = v.intValuation d := by
      rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        div_eq_one_iff_eq hvd0] at hx
      exact hx
    set k := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors
    have hvd : v.intValuation d = WithZero.exp (-(k:ℤ)) := HeightOneSpectrum.intValuation_if_neg v hd0
    obtain ⟨J, hJ⟩ : v.asIdeal ^ k ∣ Ideal.span {d} := (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d k).mp (le_of_eq hvd)
    have hn : v.asIdeal ^ k ∣ Ideal.span {n} := (HeightOneSpectrum.intValuation_le_pow_iff_dvd v n k).mp (by rw [hvn, hvd])
    have hJp : ¬ J ≤ v.asIdeal := by
      intro hle
      have h1 : v.asIdeal ^ (k+1) ∣ Ideal.span {d} := by
        rw [hJ, pow_succ]; exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
      have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d (k+1)).mpr h1
      rw [hvd, WithZero.exp_le_exp] at h2
      push_cast at h2; omega
    obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hnk : n ∈ v.asIdeal ^ k := Ideal.dvd_iff_le.mp hn (Ideal.mem_span_singleton_self n)
    have hsn : n * s ∈ Ideal.span {d} := by rw [hJ]; exact Ideal.mul_mem_mul hnk hsJ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hsn
    have hs0 : s ≠ 0 := by rintro rfl; exact hsp (zero_mem _)
    have hs0' : algebraMap (𝓞 F) F s ≠ 0 := by simpa using hs0
    refine ⟨t, s, hsp, ?_, ?_⟩
    · intro htp
      have e := congrArg v.intValuation ht
      rw [map_mul, map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr hsp, mul_one, hvn] at e
      have : v.intValuation t = 1 := by
        have := e
        calc v.intValuation t = v.intValuation t * v.intValuation d / v.intValuation d := by
              rw [mul_div_assoc, div_self hvd0, mul_one]
          _ = 1 := by rw [this, div_self hvd0]
      exact HeightOneSpectrum.intValuation_eq_one_iff.mp this htp
    · rw [div_eq_div_iff hd0' hs0', ← map_mul, ← map_mul, ← ht]
  have main : ∀ a : Fin 3 → F, (∀ i, v.valuation F (a i) = 1) → (QuadForm.diag a).IsotropicIn (v.adicCompletion F) := by
    have evalIn_diag' : ∀ (n : ℕ) (K : Type) [Field K] [Algebra F K] (b : Fin n → F) (x : Fin n → K),
        QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i ^ 2 := by
      intro n K _ _ b x
      unfold QuadForm.evalIn QuadForm.diag
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    intro a ha
    choose t s hs ht hts using fun i => rep (a i) (ha i)
    have hb : ∀ i, t i * s i ∉ v.asIdeal := fun i h => (v.isPrime.mem_or_mem h).elim (ht i) (hs i)
    obtain ⟨x, y, hxy⟩ := exists_sum_sq_mem_nf v _ _ _ (hb 0) (hb 1) (hb 2)
    set φ := algebraMap (𝓞 F) F
    have hB2 : φ (t 2 * s 2) ≠ 0 := by
      intro h; apply hb 2; rw [map_eq_zero_iff φ (IsFractionRing.injective _ _)] at h; rw [h]; exact zero_mem _
    set c : F := -(φ (t 0 * s 0) * φ x ^ 2 + φ (t 1 * s 1) * φ y ^ 2) / φ (t 2 * s 2) with hcdef
    have hc1 : c - 1 = -φ (t 0 * s 0 * x ^ 2 + t 1 * s 1 * y ^ 2 + t 2 * s 2) / φ (t 2 * s 2) := by
      rw [hcdef]; field_simp; simp only [map_add, map_mul, map_pow]; ring
    have hc : v.valuation F (c - 1) < 1 := by
      rw [hc1, map_div₀, Valuation.map_neg, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr (hb 2), div_one]
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hxy
    have hc0 : c ≠ 0 := by
      intro h; rw [h, zero_sub, Valuation.map_neg, map_one] at hc; exact lt_irrefl _ hc
    obtain ⟨z, hz⟩ := isSquare_of_valuation_sub_one_lt_nf v h2 c hc
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [mul_zero, map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective] at hz; exact hc0 hz
    have hs' : ∀ i, φ (s i) ≠ 0 := fun i => by
      rw [map_ne_zero_iff φ (IsFractionRing.injective _ _)]; intro h; exact hs i (h ▸ zero_mem _)
    have hs2 : algebraMap F (v.adicCompletion F) (φ (s 2)) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective]; exact hs' 2
    have key : a 0 * (φ (s 0) * φ x) ^ 2 + a 1 * (φ (s 1) * φ y) ^ 2 + a 2 * φ (s 2) ^ 2 * c = 0 := by
      rw [hts 0, hts 1, hts 2, hcdef]
      have := hs' 0; have := hs' 1; have := hs' 2
      field_simp
      simp only [map_mul]
      ring
    refine ⟨![algebraMap F (v.adicCompletion F) (φ (s 0) * φ x), algebraMap F (v.adicCompletion F) (φ (s 1) * φ y),
      algebraMap F (v.adicCompletion F) (φ (s 2)) * z], ?_, ?_⟩
    · intro h
      exact (mul_ne_zero hs2 hz0) (by simpa using congrFun h 2)
    · rw [evalIn_diag', Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      have := congrArg (algebraMap F (v.adicCompletion F)) key
      simp only [map_add, map_mul, map_pow, map_zero, hz] at this
      rw [← this]; simp only [map_mul]; ring
  exact FieldGen.isotropicIn_diag_of_prefix _ 3 hm a (main _ (fun i => ha _))

/-- **Finitely many bad finite places:** for $a_0, \dots, a_{m-1} \in F^\times$, only finitely many
nonzero primes $\mathfrak{p}$ of $\mathcal{O}_F$ contain $2$ or give some $a_i$ a nonzero valuation. -/
@[kb "omeara1963" "§33 [unverified]"]
theorem finite_bad_places_nf (m : ℕ) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal ∨ ∃ i, v.valuation F (a i) ≠ 1}.Finite := by
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hI : Ideal.span {(2 : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact h2
  have hA := Ideal.finite_factors hI
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (a i) ≠ 1}.Finite := by
    intro i
    apply ((HeightOneSpectrum.Support.finite (𝓞 F) (a i)).union
      (HeightOneSpectrum.Support.finite (𝓞 F) (a i)⁻¹)).subset
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    simp only [Set.mem_union, HeightOneSpectrum.Support, Set.mem_setOf_eq, map_inv₀]
    rcases lt_or_gt_of_ne hv with h | h
    · right
      have h0 : v.valuation F (a i) ≠ 0 := by simpa using ha i
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h⟩
    · left; exact h
  have : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal ∨ ∃ i, v.valuation F (a i) ≠ 1}
      = {v | v.asIdeal ∣ Ideal.span {(2 : 𝓞 F)}} ∪ ⋃ i, {v | v.valuation F (a i) ≠ 1} := by
    ext v
    simp [Ideal.dvd_span_singleton]
  rw [this]
  exact hA.union (Set.finite_iUnion hB)

/-- **Weak approximation for the splitting step:** let $m \ge 1$, $a_0, \dots, a_{m+1} \in F^\times$,
and $S$ a finite set of places of $F$ at which $\langle a_0, \dots, a_{m+1} \rangle$ is isotropic.
Then some $t \in F^\times$ is represented by $\langle a_0, a_1 \rangle$ over $F$, and
$\langle t, a_2, \dots, a_{m+1} \rangle$ is isotropic over $F_v$ for every $v \in S$ (the form
`FieldGen.isotropic_of_split` needs).
(Proof: split locally with `FieldGen.exists_split_value`, approximate the local solutions of
$a_0 X^2 + a_1 Y^2 = t_v$ by one global pair $(X, Y)$, using that $F$ is dense in
$\prod_{v \in S} F_v$ and that $F_v^{\times 2}$ is open.) -/
@[kb "lam2005" "Ch. VI, proof of Thm. 3.1 [unverified]"]
theorem exists_global_split_nf (S : Finset (NFPlace F)) (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (m + 2) → F) (ha : ∀ i, a i ≠ 0)
    (hloc : ∀ v ∈ S, v.atPlace fun K _ _ => (QuadForm.diag a).IsotropicIn K) :
    ∃ t : F, t ≠ 0 ∧ (QuadForm.diag ![a 0, a 1]).RepresentsIn F t ∧
      ∀ v ∈ S, v.atPlace fun K _ _ =>
        (QuadForm.diag (Fin.cons t fun i : Fin m => a (i.addNat 2))).IsotropicIn K := by
  classical
  have evalIn_diag' : ∀ (n : ℕ) (K : Type) [Field K] [Algebra F K] (b : Fin n → F) (x : Fin n → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i ^ 2 := by
    intro n K _ _ b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have sq_near_one : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2:K) ≠ 0 →
      ∃ δ > 0, ∀ u : K, ‖u - 1‖ < δ → IsSquare u := by
    intro K _ _ h2
    have hn : 0 < ‖(2:K)‖ := norm_pos_iff.mpr h2
    set n := ‖(2:K)‖ with hn_def
    refine ⟨n^2/8, by positivity, fun u hu => ?_⟩
    set c := u - 1
    let f : K → K := fun y => (c - y^2)/2
    let s := Metric.closedBall (0:K) (n/4)
    have hmaps : Set.MapsTo f s s := by
      intro y hy
      simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
      simp only [f, norm_div]
      rw [div_le_iff₀ hn]
      calc ‖c - y^2‖ ≤ ‖c‖ + ‖y‖^2 := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_pow]
        _ ≤ n^2/8 + (n/4)^2 := by gcongr
        _ ≤ n/4 * n := by nlinarith
    have hcon : ContractingWith (1/2 : NNReal) (hmaps.restrict f s s) := by
      refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
      have hy := y.2; have hy' := y'.2
      simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
      change dist (f (y:K)) (f y') ≤ ((1/2 : NNReal) : ℝ) * dist (y:K) y'
      simp only [dist_eq_norm, f]
      have : (c - (y:K)^2)/2 - (c - (y':K)^2)/2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
      rw [this, norm_div, norm_mul, norm_neg, div_le_iff₀ hn]
      have : ‖(y:K) + y'‖ ≤ n/2 := (norm_add_le _ _).trans (by linarith)
      push_cast
      calc ‖(y:K) - y'‖ * ‖(y:K) + y'‖ ≤ ‖(y:K) - y'‖ * (n/2) := by gcongr
        _ = 1/2 * ‖(y:K) - ↑y'‖ * n := by ring
    obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
      hmaps hcon (x := 0) (by simp [s]; positivity) (edist_ne_top _ _)
    refine ⟨1 + y, ?_⟩
    have : f y = y := hfix
    simp only [f] at this
    have h2' : (2:K) * y = c - y^2 := by
      have h3 : (2:K) * ((c - y^2)/2) = 2 * y := by rw [this]
      rw [mul_div_cancel₀ _ h2] at h3
      exact h3.symm
    simp only [c] at h2'
    linear_combination -h2'
  have local_open : ∀ (K : Type) [NormedField K] [CompleteSpace K] [Algebra F K] (A : AbsoluteValue F ℝ),
      Continuous (fun x : WithAbs A => algebraMap F K (WithAbs.equiv A x)) → DenseRange (algebraMap F K) →
      (QuadForm.diag a).IsotropicIn K →
      ∃ U : Set (WithAbs A × WithAbs A), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
        a 0 * (WithAbs.equiv A p.1)^2 + a 1 * (WithAbs.equiv A p.2)^2 ≠ 0 ∧
        (QuadForm.diag (Fin.cons (a 0 * (WithAbs.equiv A p.1)^2 + a 1 * (WithAbs.equiv A p.2)^2)
          fun i : Fin m => a (i.addNat 2))).IsotropicIn K := by
    intro K _ _ _ A hcont hdense hiso
    obtain ⟨t, ht, ⟨X, Y, hXY⟩, z, hz⟩ := FieldGen.exists_split_value K m hm a ha hiso
    have h2 : (2:K) ≠ 0 := by
      have := (algebraMap F K).injective.ne (two_ne_zero : (2:F) ≠ 0); rwa [map_ofNat, map_zero] at this
    obtain ⟨δ, hδ, hsq⟩ := sq_near_one K h2
    let φ := algebraMap F K
    let g : K × K → K := fun q => (φ (a 0) * q.1^2 + φ (a 1) * q.2^2) / t
    have hg : Continuous g := by fun_prop
    let V : Set (K × K) := {q | ‖g q - 1‖ < min δ 1}
    have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
    have hXYV : (X, Y) ∈ V := by
      simp only [V, g, Set.mem_ofPred_eq, φ, hXY, div_self ht, sub_self, norm_zero]; positivity
    let ψ : WithAbs A × WithAbs A → K × K := fun p => (φ (WithAbs.equiv A p.1), φ (WithAbs.equiv A p.2))
    have hψ : Continuous ψ := (hcont.comp continuous_fst).prodMk (hcont.comp continuous_snd)
    refine ⟨ψ ⁻¹' V, hV.preimage hψ, ?_, ?_⟩
    · obtain ⟨⟨x, y⟩, hxy⟩ := (hdense.prodMap hdense).exists_mem_open hV ⟨_, hXYV⟩
      exact ⟨((WithAbs.equiv A).symm x, (WithAbs.equiv A).symm y), by simpa [ψ] using hxy⟩
    · rintro ⟨p, q⟩ hpq
      simp only [Set.mem_preimage, V, ψ, g, Set.mem_ofPred_eq] at hpq
      set x := WithAbs.equiv A p
      set y := WithAbs.equiv A q
      have hT : φ (a 0 * x^2 + a 1 * y^2) = φ (a 0) * φ x^2 + φ (a 1) * φ y^2 := by simp [φ]
      have hne : φ (a 0 * x^2 + a 1 * y^2) ≠ 0 := by
        intro h0
        rw [← hT, h0, zero_div, zero_sub, norm_neg, norm_one] at hpq
        exact absurd (hpq.trans_le (min_le_right _ _)) (lt_irrefl _)
      refine ⟨fun h => hne (by rw [h, map_zero]), ?_⟩
      obtain ⟨s, hs⟩ := hsq _ (hpq.trans_le (min_le_left _ _))
      rw [← hT] at hs
      refine ⟨Fin.cons 1 (fun i => s * z i), fun h => by simpa using congrFun h 0, ?_⟩
      rw [evalIn_diag', Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, one_pow, mul_one]
      have : φ (a 0 * x^2 + a 1 * y^2) = t * (s * s) := by rw [← hs]; field_simp
      rw [this]
      simp only [mul_pow]
      have hsum : ∑ i, (algebraMap F K) (a (i.addNat 2)) * (s ^ 2 * z i ^ 2) =
          s^2 * ∑ i, (algebraMap F K) (a (i.addNat 2)) * z i ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsum, hz]; ring
  let absv : NFPlace F → AbsoluteValue F ℝ := fun v => match v with
    | .infinite w => w.1
    | .finite v => NumberField.HeightOneSpectrum.adicAbv F v
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≤ 1 := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_le_one F v x
  have hlt : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) < 1 ↔ x ∈ v.asIdeal := by
    intro v x; rw [← FinitePlace.norm_embedding]; exact FinitePlace.norm_lt_one_iff_mem F v x
  have hw2 : ∀ w : InfinitePlace F, w 2 = 2 := by
    intro w; rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  have hfi : ∀ (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)), ¬ (NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv w.1 := by
    intro w v h
    have h0 := hle v 2
    rw [map_ofNat] at h0
    have h1 := (h 2 1).mp (by rw [map_one]; exact h0)
    change w 2 ≤ w 1 at h1
    rw [hw2, map_one] at h1; norm_num at h1
  have hpw : Pairwise fun i j : S => ¬ (absv i).IsEquiv (absv j) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij h
    cases i with
    | infinite w =>
      cases j with
      | infinite w' =>
        have e := InfinitePlace.eq_iff_isEquiv.mpr h
        subst e
        exact hij rfl
      | finite v => exact hfi w v h.symm
    | finite v =>
      cases j with
      | infinite w' => exact hfi w' v h
      | finite v' =>
        have hvv : v ≠ v' := by
          intro e; subst e; exact hij rfl
        have : ¬ v'.asIdeal ≤ v.asIdeal := by
          intro hle'
          exact hvv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
        obtain ⟨y, hy', hy⟩ := SetLike.not_le_iff_exists.mp this
        have h1 := (h 1 (algebraMap (𝓞 F) F y)).mp (by
          rw [map_one]; exact not_lt.mp (fun hh => hy ((hlt v y).mp hh)))
        rw [map_one] at h1
        exact absurd ((hlt v' y).mpr hy') (not_lt.mpr h1)
  have hnt : ∀ i : S, (absv i).IsNontrivial := by
    rintro ⟨i, hi⟩
    cases i with
    | infinite w => exact InfinitePlace.isNontrivial w
    | finite v =>
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      refine ⟨algebraMap (𝓞 F) F x, by simpa using hx0, ?_⟩
      exact ((hlt v x).mpr hx).ne
  have hdense := AbsoluteValue.denseRange_algebraMap_pi hnt hpw
  set T : F → F → F := fun x y => a 0 * x^2 + a 1 * y^2 with hTdef
  have hU : ∀ i : S, ∃ U : Set (WithAbs (absv i) × WithAbs (absv i)), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, T (WithAbs.equiv _ p.1) (WithAbs.equiv _ p.2) ≠ 0 ∧
        (i : NFPlace F).atPlace fun K _ _ =>
          (QuadForm.diag (Fin.cons (T (WithAbs.equiv _ p.1) (WithAbs.equiv _ p.2))
            fun i : Fin m => a (i.addNat 2))).IsotropicIn K := by
    rintro ⟨i, hi⟩
    have hl := hloc i hi
    cases i with
    | infinite w =>
      refine local_open w.Completion w.1 (InfinitePlace.Completion.continuous_coe w) ?_ hl
      have : (algebraMap F w.Completion : F → w.Completion) = (fun x : WithAbs w.1 =>
          InfinitePlace.Completion.ofCompletion (x : UniformSpace.Completion (WithAbs w.1))) ∘
          (WithAbs.equiv w.1).symm := rfl
      rw [this]
      unfold DenseRange
      rw [Function.Surjective.range_comp (WithAbs.equiv w.1).symm.surjective]
      exact InfinitePlace.Completion.denseRange_coe w
    | finite v =>
      refine local_open (v.adicCompletion F) (NumberField.HeightOneSpectrum.adicAbv F v) ?_
        (HeightOneSpectrum.denseRange_algebraMap F v) hl
      have : Isometry ((FinitePlace.embedding v).comp
          (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv F v)).toRingHom) := by
        apply AddMonoidHomClass.isometry_of_norm
        intro x
        rw [WithAbs.norm_eq_apply_ofAbs]
        exact FinitePlace.norm_embedding v _
      exact this.continuous
  choose U hUo hUn hUp using hU
  choose p hp using hUn
  let V : Set ((Π i : S, WithAbs (absv i)) × (Π i : S, WithAbs (absv i))) :=
    ⋂ i, (fun q => (q.1 i, q.2 i)) ⁻¹' U i
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => (hUo i).preimage (by fun_prop)
  have hVn : V.Nonempty := ⟨(fun i => (p i).1, fun i => (p i).2), Set.mem_iInter.mpr fun i => hp i⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := (hdense.prodMap hdense).exists_mem_open hVo hVn
  have key : ∀ i : S, T x y ≠ 0 ∧ (i : NFPlace F).atPlace fun K _ _ =>
          (QuadForm.diag (Fin.cons (T x y) fun i : Fin m => a (i.addNat 2))).IsotropicIn K := by
    intro i
    exact hUp i _ (Set.mem_iInter.mp hxy i)
  have hrep : (QuadForm.diag ![a 0, a 1]).RepresentsIn F (T x y) := by
    refine ⟨![x, y], ?_⟩
    rw [evalIn_diag']
    simp [Fin.sum_univ_two, T]
  rcases S.eq_empty_or_nonempty with hS | ⟨v0, hv0⟩
  · subst hS
    refine ⟨a 0, ha 0, ⟨![1, 0], ?_⟩, by simp⟩
    rw [evalIn_diag']
    simp [Fin.sum_univ_two]
  · exact ⟨T x y, (key ⟨v0, hv0⟩).1, hrep, fun v hv => (key ⟨v, hv⟩).2⟩

end QuadFormsKB.NFLocal
