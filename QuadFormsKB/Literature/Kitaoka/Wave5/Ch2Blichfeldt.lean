/-
# Kitaoka 1993, §2.2: Blichfeldt's estimate of Hermite's constant

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.2, Theorem 2.2.1 (p. 42), Lemma 2.2.2 (p. 44),
Lemma 2.2.3 (p. 44).

**Proves**
* `lemma222` (Lemma 2.2.2): for points $x, x^{(1)}, \dots, x^{(n)}$ of $\mathbb R^m$,
  $\sum_{i,j}|x^{(i)} - x^{(j)}|^2 \le 2n \sum_k |x - x^{(k)}|^2$ (and `lemma222_finset`, over a finite index set, in
  any real inner product space).
* `latMin_le_blichfeldtConst_mul` (Theorem 2.2.1, matrix form): for a positive definite real symmetric
  $m \times m$ matrix $p$ ($m \ge 1$), $\min p \le \frac 2\pi\,\Gamma(2 + m/2)^{2/m} (\det p)^{1/m}$.
* `theorem221` (Theorem 2.2.1): Hermite's constant satisfies $\mu_m \le \frac 2\pi\,\Gamma(2 + m/2)^{2/m}$ for
  $m \ge 1$.
* `lemma223` (Lemma 2.2.3): if the lattice $\Lambda = g\mathbb Z^m$ ($g \in \mathrm{GL}_m(\mathbb R)$) gives a packing
  of $\mathbb R^m$ by open unit balls, then $\operatorname{vol}(\mathbb R^m/\Lambda) = |\det g| \ge
  (2\pi)^{m/2}\,\Gamma(2 + m/2)^{-1}$.

**Proof notes.** Kitaoka proves Lemma 2.2.3 by counting lattice points in large cubes (Lemma 2.2.1) and deduces
Theorem 2.2.1 from it. Here the order is reversed and the counting is replaced by integration over a fundamental
domain (the same argument in integral form, as in Cassels' proof of Blichfeldt's theorem,
`Cassels.Ch5.blichfeldt_integral`): write $p = {}^t B B$ and $Q(y) = |By|^2 = p[y]$, let $c = \min p/2$ and
$F(y) = \sum_{u \in \mathbb Z^m}\max(0, c - Q(y + u))$. For each $y$, the finitely many $u$ with $Q(y+u) < c$ satisfy
$Q(u - u') \ge 2c$ for $u \ne u'$, so Lemma 2.2.2 gives $F(y) \le c$ (Kitaoka's inequality (6), scaled). Integrating
over the unit cube, $\int_{\mathbb R^m}\max(0, c - Q(y))\,dy \le c$; the left side is
$|\det B|^{-1}\pi^{m/2}c^{m/2+1}/\Gamma(2 + m/2)$ (change of variables and polar coordinates), which rearranges to the
bound. Lemma 2.2.3 then follows from the matrix form with $p = {}^t g g$.

The inequalities of Theorem 2.2.1 and Lemma 2.2.3 are proved non-strict, which is what Kitaoka's proof gives (his
proof of Lemma 2.2.3 passes to a limit). Theorem 2.2.1 and Lemma 2.2.3 assume $m \ge 1$ (for $m = 0$ there is no
lattice to speak of; in Lean $\mu_0 = 0$).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch2BlichfeldtConst
import QuadFormsKB.Literature.Kitaoka.Ch2Theorem211
import QuadFormsKB.Literature.Cassels.Ch5.Supplement
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.UniformSpace.Uniformizable

open MeasureTheory Matrix Set Metric

noncomputable section

namespace QuadFormsKB.Kitaoka.Blichfeldt

/-! ### Lemma 2.2.2 -/

/-- **Kitaoka 1993, Lemma 2.2.2** (p. 44), over a finite index set and in any real inner product space:
$\sum_{i, j \in s}\lVert a_i - a_j\rVert^2 \le 2\,\#s \sum_{k \in s}\lVert x - a_k\rVert^2$. -/
theorem lemma222_finset {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} (s : Finset ι)
    (x : E) (a : ι → E) :
    ∑ i ∈ s, ∑ j ∈ s, ‖a i - a j‖ ^ 2 ≤ 2 * s.card * ∑ k ∈ s, ‖x - a k‖ ^ 2 := by
  set b : ι → E := fun i => x - a i with hb
  have hab : ∀ i j, a i - a j = b j - b i := fun i j => by simp [hb]
  have key : ∑ i ∈ s, ∑ j ∈ s, ‖b j - b i‖ ^ 2 =
      2 * s.card * ∑ k ∈ s, ‖b k‖ ^ 2 - 2 * ‖∑ k ∈ s, b k‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    rw [← real_inner_self_eq_norm_sq (∑ k ∈ s, b k), sum_inner]
    simp_rw [inner_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j => inner ℝ (b j) (b i))]
    ring
  have h0 : 0 ≤ ‖∑ k ∈ s, b k‖ ^ 2 := by positivity
  simp_rw [hab]
  rw [key]
  linarith

/-- **Kitaoka 1993, Lemma 2.2.2** (p. 44): for $x, x^{(1)}, \dots, x^{(n)} \in \mathbb R^m$ (Euclidean space;
indices $0, \dots, n - 1$ here), $\sum_{i,j}|x^{(i)} - x^{(j)}|^2 \le 2n\sum_k |x - x^{(k)}|^2$. -/
@[kb "kitaoka1993" "§2.2, Lemma 2.2.2, p. 44"]
theorem lemma222 {m n : ℕ} (x : EuclideanSpace ℝ (Fin m)) (xs : Fin n → EuclideanSpace ℝ (Fin m)) :
    ∑ i, ∑ j, ‖xs i - xs j‖ ^ 2 ≤ 2 * n * ∑ k, ‖x - xs k‖ ^ 2 := by
  simpa using lemma222_finset Finset.univ x xs

/-! ### Periodization over the unit cube -/

/-- Periodization: for a measurable $f \ge 0$ on $\mathbb R^n$,
$\int_{[0,1)^n}\sum_{u \in \mathbb Z^n} f(x + u)\,dx = \int_{\mathbb R^n} f$ (the unit cube is a fundamental domain
of $\mathbb Z^n$). -/
theorem lintegral_unitCube_tsum {n : ℕ} {f : (Fin n → ℝ) → ENNReal} (hf : Measurable f) :
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
      ∑' u : Fin n → ℤ, f (x + fun i => (u i : ℝ)) = ∫⁻ x, f x := by
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) (volume : Measure (Fin n → ℝ))
  set G := (Cassels.stdLattice n).toAddSubgroup
  have : Countable G := (inferInstance : Countable (Cassels.stdLattice n))
  have hmeas : ∀ g : G, Measurable fun x => f (g +ᵥ x) := fun g => hf.comp (measurable_const_add _)
  have htot : ∫⁻ x, f x = ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)), ∑' g : G, f (g +ᵥ x) := by
    rw [fund.lintegral_eq_tsum'' f, lintegral_tsum]
    exact fun g => (hmeas g).aemeasurable
  rw [htot, Cassels.Ch5.unitCube_eq_fundamentalDomain]
  refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun x _ => ?_
  rw [← (Cassels.Ch5.intVecEquivStdLattice n).tsum_eq]
  refine tsum_congr fun u => ?_
  simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm x]
  rfl

/-! ### The radial integral -/

/-- The volume of the unit ball of $\mathbb R^m$: $\pi^{m/2}/\Gamma(m/2 + 1)$. -/
theorem volume_real_unitBall {m : ℕ} (hm : 1 ≤ m) :
    (volume : Measure (EuclideanSpace ℝ (Fin m))).real (ball 0 1) =
      Real.pi ^ ((m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (Real.Gamma_nonneg_of_nonneg (by positivity))), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul Real.pi_pos.le]
  ring_nf

/-- $\int_0^\infty r^{m-1}\max(c - r^2, 0)\,dr = 2c^{m/2+1}/(m(m+2))$ for $m \ge 1$, $c > 0$. -/
theorem integral_Ioi_pow_mul_max {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∫ r in Ioi (0 : ℝ), r ^ (m - 1) * max (c - r ^ 2) 0 =
      2 * c ^ ((m : ℝ) / 2 + 1) / (m * (m + 2)) := by
  set s := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hc
  have hss : s ^ 2 = c := Real.sq_sqrt hc.le
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc 0 s) measurableSet_Ioi Ioc_subset_Ioi_self
    (fun r hr => by
      have h1 : s < r := by
        rcases hr with ⟨hr0, hr1⟩
        simp only [mem_Ioc, not_and, not_le] at hr1
        exact hr1 hr0
      have : c - r ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right this])]
  rw [← intervalIntegral.integral_of_le hs0.le]
  have hcongr : ∫ r in (0 : ℝ)..s, r ^ (m - 1) * max (c - r ^ 2) 0 =
      ∫ r in (0 : ℝ)..s, (c * r ^ (m - 1) - r ^ (m - 1 + 2)) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs0.le] at hr
    have : 0 ≤ c - r ^ 2 := by nlinarith [hr.1, hr.2]
    simp only [max_eq_left this]
    ring
  rw [hcongr, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  have hm1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm]; simp
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hm'' : m - 1 + 2 + 1 = m + 2 := by omega
  rw [hm', hm'']
  push_cast [hm1]
  have hsm : s ^ m = c ^ ((m : ℝ) / 2) := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    ring_nf
  have hpow : c ^ ((m : ℝ) / 2 + 1) = c ^ ((m : ℝ) / 2) * c := by
    rw [Real.rpow_add hc, Real.rpow_one]
  rw [hpow, pow_add, hsm, hss]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  simp only [zero_pow (by omega : m ≠ 0), zero_pow (by omega : m + 2 ≠ 0)]
  have key : (1 : ℝ) / m - 1 / (m + 2) = 2 / (m * (m + 2)) := by field_simp; ring
  linear_combination (c ^ ((m : ℝ) / 2) * c) * key

/-- **The integral of the truncated paraboloid**: $\int_{\mathbb R^m}\max(c - |w|^2, 0)\,dw =
\pi^{m/2}c^{m/2+1}/\Gamma(2 + m/2)$ for $m \ge 1$, $c > 0$. -/
theorem integral_max_sub_normSq {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∫ w : EuclideanSpace ℝ (Fin m), max (c - ‖w‖ ^ 2) 0 =
      Real.pi ^ ((m : ℝ) / 2) * c ^ ((m : ℝ) / 2 + 1) / Real.Gamma (2 + (m : ℝ) / 2) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun r : ℝ => max (c - r ^ 2) 0)
  rw [h, finrank_euclideanSpace_fin, volume_real_unitBall hm, nsmul_eq_mul, smul_eq_mul]
  simp_rw [smul_eq_mul]
  rw [integral_Ioi_pow_mul_max hm hc]
  have hG : Real.Gamma (2 + (m : ℝ) / 2) = ((m : ℝ) / 2 + 1) * Real.Gamma ((m : ℝ) / 2 + 1) := by
    rw [show (2 : ℝ) + (m : ℝ) / 2 = ((m : ℝ) / 2 + 1) + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  have hG0 : Real.Gamma ((m : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hG]
  field_simp

/-! ### Theorem 2.2.1 -/

/-- The integral bound at the heart of Blichfeldt's argument: if $p = {}^t B B$ and $Q(y) = |By|^2$ satisfies
$Q(u) \ge 2c$ for all nonzero $u \in \mathbb Z^m$, then $F(y) = \sum_{u \in \mathbb Z^m}\max(0, c - Q(y + u)) \le c$
for every $y$ (Kitaoka's inequality (6), p. 44, scaled). -/
theorem tsum_le_of_minimum {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) {c : ℝ} (hc : 0 < c)
    (hmin : ∀ u : Fin m → ℤ, u ≠ 0 → 2 * c ≤ ‖WithLp.toLp 2 (B *ᵥ fun i => (u i : ℝ))‖ ^ 2)
    (y : Fin m → ℝ) :
    ∑' u : Fin m → ℤ, ENNReal.ofReal (c - ‖WithLp.toLp 2 (B *ᵥ (y + fun i => (u i : ℝ)))‖ ^ 2) ≤
      ENNReal.ofReal c := by
  set a : (Fin m → ℤ) → EuclideanSpace ℝ (Fin m) := fun u => WithLp.toLp 2 (B *ᵥ (y + fun i => (u i : ℝ)))
    with ha
  have hdiff : ∀ u v : Fin m → ℤ, a u - a v = WithLp.toLp 2 (B *ᵥ fun i => ((u - v) i : ℝ)) := by
    intro u v
    simp only [ha, ← WithLp.toLp_sub, ← Matrix.mulVec_sub]
    congr 2
    ext i
    simp
  refine tsum_le_of_sum_le' (by simp) fun T => ?_
  classical
  set T' := T.filter (fun u => ‖a u‖ ^ 2 < c) with hT'
  have hsplit : ∑ u ∈ T, ENNReal.ofReal (c - ‖a u‖ ^ 2) = ∑ u ∈ T', ENNReal.ofReal (c - ‖a u‖ ^ 2) := by
    rw [hT', Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with h
    · rfl
    · exact ENNReal.ofReal_of_nonpos (by linarith [not_lt.1 h])
  change ∑ u ∈ T, ENNReal.ofReal (c - ‖a u‖ ^ 2) ≤ _
  rw [hsplit, ← ENNReal.ofReal_sum_of_nonneg (fun u hu => by
    have := (Finset.mem_filter.1 hu).2
    linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- Lemma 2.2.2 with the centre $0$
  have hL := lemma222_finset T' 0 a
  simp only [zero_sub, norm_neg] at hL
  set N := T'.card with hN
  set S := ∑ k ∈ T', ‖a k‖ ^ 2 with hS
  have hlow : ∑ i ∈ T', ∑ j ∈ T', (if i = j then (0 : ℝ) else 2 * c) ≤
      ∑ i ∈ T', ∑ j ∈ T', ‖a i - a j‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    split_ifs with hij
    · positivity
    · rw [hdiff]
      exact hmin _ (sub_ne_zero.2 hij)
  have hcount : ∑ i ∈ T', ∑ j ∈ T', (if i = j then (0 : ℝ) else 2 * c) = N * ((N - 1) * (2 * c)) := by
    have : ∀ i ∈ T', ∑ j ∈ T', (if i = j then (0 : ℝ) else 2 * c) = (N - 1) * (2 * c) := by
      intro i hi
      have h1 : ∑ j ∈ T', (if i = j then (0 : ℝ) else 2 * c) =
          ∑ j ∈ T', 2 * c - ∑ j ∈ T', (if i = j then 2 * c else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [h1, Finset.sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true hi), Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ u ∈ T', (c - ‖a u‖ ^ 2) = N * c - S := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hS0 : 0 ≤ S := by positivity
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
    have h2 : N * ((N - 1) * (2 * c)) ≤ 2 * N * S := hcount ▸ hlow.trans hL
    have h3 : (N - 1) * c ≤ S := by nlinarith
    linarith

/-- Change of variables along an invertible matrix: $\int h(By)\,dy = |\det B|^{-1}\int h(z)\,dz$. -/
theorem lintegral_comp_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    {h : (Fin m → ℝ) → ENNReal} (hh : Measurable h) :
    ∫⁻ y, h (B *ᵥ y) = ENNReal.ofReal |B.det⁻¹| * ∫⁻ z, h z := by
  have hL : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → ℝ))) hL
  rw [LinearMap.det_toLin'] at hmap
  have hLm : Measurable (Matrix.toLin' B) := (Matrix.toLin' B).continuous_of_finiteDimensional.measurable
  calc ∫⁻ y, h (B *ᵥ y) = ∫⁻ y, h (Matrix.toLin' B y) := rfl
    _ = ∫⁻ z, h z ∂(Measure.map (Matrix.toLin' B) volume) := (lintegral_map hh hLm).symm
    _ = _ := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- $\int_{\mathbb R^m}\max(0, c - |By|^2)\,dy = |\det B|^{-1}\pi^{m/2}c^{m/2+1}/\Gamma(2 + m/2)$ for invertible $B$,
$m \ge 1$, $c > 0$ (as an extended nonnegative real). -/
theorem lintegral_ofReal_sub_normSq {m : ℕ} (hm : 1 ≤ m) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    ∫⁻ y : Fin m → ℝ, ENNReal.ofReal (c - ‖WithLp.toLp 2 (B *ᵥ y)‖ ^ 2) =
      ENNReal.ofReal |B.det⁻¹| *
        ENNReal.ofReal (Real.pi ^ ((m : ℝ) / 2) * c ^ ((m : ℝ) / 2 + 1) / Real.Gamma (2 + (m : ℝ) / 2)) := by
  have hg : Measurable fun w : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (c - ‖w‖ ^ 2) :=
    (measurable_const.sub (continuous_norm.measurable.pow_const 2)).ennreal_ofReal
  have hmeas : Measurable fun z : Fin m → ℝ => ENNReal.ofReal (c - ‖WithLp.toLp 2 z‖ ^ 2) :=
    hg.comp (PiLp.continuous_toLp 2 _).measurable
  rw [lintegral_comp_mulVec B hB hmeas]
  congr 1
  rw [(PiLp.volume_preserving_toLp (Fin m)).lintegral_comp hg]
  have hint : Integrable (fun w : EuclideanSpace ℝ (Fin m) => max (c - ‖w‖ ^ 2) 0) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_closedBall 0 (Real.sqrt c)) fun w hw => ?_
    have h1 : Real.sqrt c < ‖w‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hw
    have h2 : c < ‖w‖ ^ 2 := by
      have := mul_pos (sub_pos.2 h1) (add_pos_of_pos_of_nonneg (Real.sqrt_nonneg c |>.trans_lt h1)
        (Real.sqrt_nonneg c))
      nlinarith [Real.sq_sqrt hc.le]
    exact max_eq_right (by linarith)
  have hmax : ∀ w : EuclideanSpace ℝ (Fin m),
      ENNReal.ofReal (c - ‖w‖ ^ 2) = ENNReal.ofReal (max (c - ‖w‖ ^ 2) 0) := fun w => by
    rcases le_total (c - ‖w‖ ^ 2) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  simp_rw [hmax]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => le_max_right _ _),
    integral_max_sub_normSq hm hc]

/-- **Kitaoka 1993, Theorem 2.2.1** (p. 42), for a single matrix: for a positive definite real symmetric
$m \times m$ matrix $p$ with $m \ge 1$, $\min p \le \frac 2\pi\,\Gamma(2 + m/2)^{2/m}\,(\det p)^{1/m}$
(`Reduction.latMin`, `blichfeldtConst`). -/
@[kb "kitaoka1993" "§2.2, Thm. 2.2.1, p. 42 (min p ≤ 2π⁻¹Γ(2+m/2)^{2/m}(det p)^{1/m})"]
theorem latMin_le_blichfeldtConst_mul {m : ℕ} (hm : 1 ≤ m) (p : Matrix (Fin m) (Fin m) ℝ) (hp : p.PosDef) :
    Reduction.latMin p ≤ blichfeldtConst m * p.det ^ ((1 : ℝ) / m) := by
  obtain ⟨g, hg⟩ := Reduction.exists_GL_eq_transpose_mul_self p hp
  set B : Matrix (Fin m) (Fin m) ℝ := (g : Matrix (Fin m) (Fin m) ℝ) with hBdef
  have hQ : ∀ v : Fin m → ℝ, v ⬝ᵥ (p *ᵥ v) = ‖WithLp.toLp 2 (B *ᵥ v)‖ ^ 2 := by
    intro v
    rw [hg, EuclideanSpace.real_norm_sq_eq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    simp [dotProduct, sq]
  have hdetp : p.det = B.det ^ 2 := by rw [hg, det_mul, det_transpose]; ring
  have hBdet : B.det ≠ 0 := by
    intro h0
    have := hp.det_pos
    rw [hdetp, h0] at this
    simp at this
  have hΓ : 0 < Real.Gamma (2 + (m : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hrhs : 0 ≤ blichfeldtConst m * p.det ^ ((1 : ℝ) / m) := by
    unfold blichfeldtConst
    have := Real.pi_pos
    have := hp.det_pos
    positivity
  set μ := Reduction.latMin p with hμdef
  rcases le_or_gt μ 0 with hμ | hμ
  · exact hμ.trans hrhs
  set c := μ / 2 with hcdef
  have hc : 0 < c := by positivity
  have hmin : ∀ u : Fin m → ℤ, u ≠ 0 → 2 * c ≤ ‖WithLp.toLp 2 (B *ᵥ fun i => (u i : ℝ))‖ ^ 2 := by
    intro u hu
    rw [show 2 * c = μ by ring, ← hQ]
    refine csInf_le ⟨0, ?_⟩ ⟨u, hu, rfl⟩
    rintro r ⟨x, -, rfl⟩
    rw [hQ]
    positivity
  have hW : MeasurableSet (Set.pi Set.univ (fun _ : Fin m => Set.Ico (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hmeasF : Measurable fun y : Fin m → ℝ => ENNReal.ofReal (c - ‖WithLp.toLp 2 (B *ᵥ y)‖ ^ 2) := by
    have hc' : Continuous fun y : Fin m → ℝ => WithLp.toLp 2 (B *ᵥ y) :=
      (PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)
    exact (measurable_const.sub (hc'.norm.measurable.pow_const 2)).ennreal_ofReal
  have hF : ∫⁻ y : Fin m → ℝ, ENNReal.ofReal (c - ‖WithLp.toLp 2 (B *ᵥ y)‖ ^ 2) ≤ ENNReal.ofReal c := by
    rw [← lintegral_unitCube_tsum hmeasF]
    calc _ ≤ ∫⁻ _ in Set.pi Set.univ (fun _ : Fin m => Set.Ico (0 : ℝ) 1), ENNReal.ofReal c :=
          setLIntegral_mono' hW fun y _ => tsum_le_of_minimum B hc hmin y
      _ = ENNReal.ofReal c := by rw [setLIntegral_const, Real.volume_pi_Ico]; simp
  rw [lintegral_ofReal_sub_normSq hm B hBdet hc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hc.le] at hF
  -- `hF : |det B⁻¹| * (π^{m/2} c^{m/2+1} / Γ) ≤ c`; rearrange
  set D := |B.det| with hD
  have hD0 : 0 < D := abs_pos.2 hBdet
  set G := Real.Gamma (2 + (m : ℝ) / 2) with hG
  have hπ := Real.pi_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpow : c ^ ((m : ℝ) / 2 + 1) = c ^ ((m : ℝ) / 2) * c := by rw [Real.rpow_add hc, Real.rpow_one]
  rw [abs_inv, ← hD, hcpow] at hF
  have h1 : (Real.pi * c) ^ ((m : ℝ) / 2) ≤ G * D := by
    rw [Real.mul_rpow hπ.le hc.le]
    have hc2 : 0 < c ^ ((m : ℝ) / 2) := Real.rpow_pos_of_pos hc _
    have e : D⁻¹ * (Real.pi ^ ((m : ℝ) / 2) * (c ^ ((m : ℝ) / 2) * c) / G) =
        Real.pi ^ ((m : ℝ) / 2) * c ^ ((m : ℝ) / 2) * c / (G * D) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hF
    exact le_of_mul_le_mul_right (by linarith) hc
  have h2 : Real.pi * c ≤ (G * D) ^ ((2 : ℝ) / m) := by
    have := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 2 / m)
    rwa [← Real.rpow_mul (by positivity), show (m : ℝ) / 2 * (2 / m) = 1 by field_simp, Real.rpow_one] at this
  have h3 : (G * D) ^ ((2 : ℝ) / m) = G ^ ((2 : ℝ) / m) * p.det ^ ((1 : ℝ) / m) := by
    rw [Real.mul_rpow hΓ.le hD0.le, hdetp, ← sq_abs, ← hD, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    congr 2
    push_cast
    ring
  rw [h3] at h2
  unfold blichfeldtConst
  rw [← hG]
  have : μ = 2 * c := by rw [hcdef]; ring
  rw [this, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hπ]
  nlinarith

/-- **Kitaoka 1993, Theorem 2.2.1** (p. 42; Blichfeldt): Hermite's constant satisfies
$\mu_m \le \frac 2\pi\,\Gamma(2 + m/2)^{2/m}$ for $m \ge 1$ (`Reduction.hermiteConst`, `blichfeldtConst`). -/
@[kb "kitaoka1993" "§2.2, Thm. 2.2.1, p. 42"]
theorem theorem221 {m : ℕ} (hm : 1 ≤ m) : Reduction.hermiteConst m ≤ blichfeldtConst m := by
  refine csSup_le ⟨_, 1, Matrix.PosDef.one, rfl⟩ ?_
  rintro r ⟨p, hp, rfl⟩
  have hdet : 0 < p.det ^ ((1 : ℝ) / m) := Real.rpow_pos_of_pos hp.det_pos _
  rw [div_le_iff₀ hdet]
  exact latMin_le_blichfeldtConst_mul hm p hp

/-- **Kitaoka 1993, Lemma 2.2.3** (p. 44): let $\Lambda = g\mathbb Z^m$ ($g \in \mathrm{GL}_m(\mathbb R)$, $m \ge 1$) be
a lattice on Euclidean space $\mathbb R^m$ that gives a packing of $\mathbb R^m$, i.e. the open unit balls
$K_m + x$, $x \in \Lambda$, are pairwise disjoint (`hpack`, for the points $x = gu$, $u \in \mathbb Z^m$). Then
$\operatorname{vol}(\mathbb R^m/\Lambda) = |\det g| \ge (2\pi)^{m/2}\,\Gamma(2 + m/2)^{-1}$. -/
@[kb "kitaoka1993" "§2.2, Lemma 2.2.3, p. 44"]
theorem lemma223 {m : ℕ} (hm : 1 ≤ m) (g : GL (Fin m) ℝ)
    (hpack : ∀ u v : Fin m → ℤ, u ≠ v →
      Disjoint (ball (WithLp.toLp 2 ((g : Matrix (Fin m) (Fin m) ℝ) *ᵥ fun i => (u i : ℝ)) :
          EuclideanSpace ℝ (Fin m)) 1)
        (ball (WithLp.toLp 2 ((g : Matrix (Fin m) (Fin m) ℝ) *ᵥ fun i => (v i : ℝ))) 1)) :
    (2 * Real.pi) ^ ((m : ℝ) / 2) / Real.Gamma (2 + (m : ℝ) / 2) ≤
      |(g : Matrix (Fin m) (Fin m) ℝ).det| := by
  set B : Matrix (Fin m) (Fin m) ℝ := (g : Matrix (Fin m) (Fin m) ℝ) with hBdef
  set p := Bᵀ * B with hpdef
  have hBu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 (Units.isUnit g)
  have hp : p.PosDef := by
    have := PosDef.conjTranspose_mul_self B (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det B).2 hBu))
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hQ : ∀ v : Fin m → ℝ, v ⬝ᵥ (p *ᵥ v) = ‖WithLp.toLp 2 (B *ᵥ v)‖ ^ 2 := by
    intro v
    rw [hpdef, EuclideanSpace.real_norm_sq_eq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    simp [dotProduct, sq]
  -- every nonzero vector of $\Lambda$ has length at least $2$
  have h4 : 4 ≤ Reduction.latMin p := by
    refine le_csInf ⟨_, Pi.single ⟨0, hm⟩ 1, by simp, rfl⟩ ?_
    rintro r ⟨u, hu, rfl⟩
    rw [hQ]
    have hd := (disjoint_ball_ball_iff one_pos one_pos).1 (hpack u 0 hu)
    have h0 : (B *ᵥ fun i => ((0 : Fin m → ℤ) i : ℝ)) = 0 := by
      simp only [Pi.zero_apply, Int.cast_zero]
      exact Matrix.mulVec_zero B
    rw [h0, WithLp.toLp_zero, dist_zero_right] at hd
    nlinarith
  have hb := (h4.trans (latMin_le_blichfeldtConst_mul hm p hp))
  have hdetp : p.det = B.det ^ 2 := by rw [hpdef, det_mul, det_transpose]; ring
  set D := |B.det| with hD
  have hD0 : 0 < D := abs_pos.2 hBu.ne_zero
  set G := Real.Gamma (2 + (m : ℝ) / 2) with hG
  have hΓ : 0 < G := Real.Gamma_pos_of_pos (by positivity)
  have hπ := Real.pi_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : p.det ^ ((1 : ℝ) / m) = D ^ ((2 : ℝ) / m) := by
    rw [hdetp, ← sq_abs, ← hD, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    congr 1
    push_cast
    ring
  unfold blichfeldtConst at hb
  rw [hpow, ← hG, mul_assoc, ← Real.mul_rpow hΓ.le hD0.le] at hb
  -- `hb : 4 ≤ 2/π * (G D)^{2/m}`, i.e. `2π ≤ (G D)^{2/m}`
  have h2 : 2 * Real.pi ≤ (G * D) ^ ((2 : ℝ) / m) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hπ] at hb
    nlinarith
  have h3 := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2)
  rw [← Real.rpow_mul (by positivity), show (2 : ℝ) / m * ((m : ℝ) / 2) = 1 by field_simp,
    Real.rpow_one] at h3
  rw [div_le_iff₀ hΓ]
  linarith

end QuadFormsKB.Kitaoka.Blichfeldt
