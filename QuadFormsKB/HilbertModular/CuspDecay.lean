/-
# Hilbert modular forms: exponential decay of cusp forms at $i\infty$

Setting of `FourierInversion.lean`: $\iota$ finite, $b = (b_j)_{j\in J}$ an $\mathbb{R}$-basis of $\mathbb{R}^\iota$ with lattice
$\Lambda = \bigoplus_j\mathbb{Z}b_j$, $f : \mathbb{H}^\iota \to \mathbb{C}$ holomorphic and $\Lambda$-periodic, with $q$-coefficients
$a_\nu$ (`qCoeff`) on the dual lattice. Assume that $N\mathbf 1 \in \Lambda$ for some integer $N \ge 1$ ($\mathbf 1 = (1, \dots, 1)$;
for $F$ totally real and $\Lambda$ the image of a fractional ideal $I$ this is $N \in I$).

**Main result** (`exists_norm_le_exp_of_isZeroAtImInftyPi`): if $f(z) \to 0$ as $\min_v\operatorname{Im}z_v \to \infty$
(`IsZeroAtImInftyPi`), then for every $c > 0$ there is $M$ with
$$|f(z)| \le M\,e^{-2\pi t/N}\qquad\text{whenever } t \ge 0 \text{ and } \operatorname{Im}z_v \ge c + t \text{ for all } v.$$

*Proof.* (i) Boundedness at $i\infty$ kills $a_\nu$ unless $\nu \ge 0$ (`coeff_eq_zero_of_isBounded`); (ii) the limit $0$ kills
$a_0$, because $a_0 = c_0(y)$ is the mean of $f$ over the slice at height $y$ (`qCoeff_zero_eq_zero`); (iii) for $\nu \ge 0$,
$\nu \ne 0$ in the dual lattice, $\sum_v\nu_v = \langle\nu, \mathbf 1\rangle \in N^{-1}\mathbb{Z}_{>0}$, so $\sum_v\nu_v \ge 1/N$
(`one_le_mul_pair_one`); (iv) the $q$-expansion (`hasSum_qExpansion`) then gives
$|f(z)| \le \sum_\nu|a_\nu|e^{-2\pi\langle\nu, \operatorname{Im}z\rangle} \le e^{-2\pi t/N}\sum_\nu|a_\nu|e^{-2\pi c\langle\nu, \mathbf 1\rangle}$.

This is the input "cusp forms decay exponentially at each cusp" of the Siegel-set argument (`CuspBound.lean`). Unlike
the Koecher principle it needs no units and holds for every $|\iota|$ (including $d = 1$).

Sources: Garrett, *Holomorphic Hilbert Modular Forms* (1990), Ch. 1 (Fourier expansions at cusps) [unverified];
Freitag, *Hilbert Modular Forms* (1990), Ch. I §4 [unverified].
-/
import QuadFormsKB.HilbertModular.MeanSquare

open Filter Topology Complex UpperHalfPlane
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

/-- A set in `atImInftyPi` contains a region $\{z : \operatorname{Im}z_v \ge A\ \forall v\}$. -/
lemma exists_forall_im_ge_mem {s : Set (ι → ℍ)} (hs : s ∈ (atImInftyPi : Filter (ι → ℍ))) :
    ∃ A : ℝ, ∀ z : ι → ℍ, (∀ v, A ≤ (z v).im) → z ∈ s := by
  rw [atImInftyPi, Filter.mem_iInf_of_finite] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have h : ∀ v, ∃ A : ℝ, ∀ z : ι → ℍ, A ≤ (z v).im → z ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := Filter.mem_comap.mp (ht v)
    obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp hu
    exact ⟨A, fun z hz => hut (hA _ hz)⟩
  choose A hA using h
  refine ⟨∑ v, |A v|, fun z hz => Set.mem_iInter.mpr fun v => hA v z ?_⟩
  exact (le_abs_self _).trans ((Finset.single_le_sum (f := fun v => |A v|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ v)).trans (hz v))

/-- If $f \to 0$ at $i\infty$ then for every $\varepsilon > 0$, $|f| \le \varepsilon$ on some region $\{\operatorname{Im}z_v \ge A\}$. -/
lemma IsZeroAtImInftyPi.exists_bound {f : (ι → ℍ) → ℂ} (hz : IsZeroAtImInftyPi f) {ε : ℝ}
    (hε : 0 < ε) : ∃ A : ℝ, ∀ z : ι → ℍ, (∀ v, A ≤ (z v).im) → ‖f z‖ ≤ ε := by
  have h : ∀ᶠ z in (atImInftyPi : Filter (ι → ℍ)), ‖f z‖ ≤ ε := by
    have := (hz : Tendsto f atImInftyPi (𝓝 0)).eventually (Metric.closedBall_mem_nhds 0 hε)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  exact exists_forall_im_ge_mem h

lemma isDual_zero (b : Module.Basis J ℝ (ι → ℝ)) : IsDual b 0 :=
  fun _ => ⟨0, by simp [pair]⟩

/-- **The constant coefficient of a function vanishing at $i\infty$ is $0$**: $a_0 = c_0(y)$ for all $y$, and
$|c_0(y)| \le \sup_x|f(x + iy)|$, which is $\le \varepsilon$ for $y$ large. -/
theorem qCoeff_zero_eq_zero [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hz : IsZeroAtImInftyPi f) :
    qCoeff f b 0 = 0 := by
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := hz.exists_bound hε
  set y : ι → ℝ := fun _ => |A| + 1
  have hy : ∀ v, 0 < y v := fun _ => by positivity
  have h := coeff_eq_qCoeff hf hper (isDual_zero b) hy
  have hp : pair (0 : ι → ℝ) y = 0 := by simp [pair]
  rw [hp, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one] at h
  rw [← h]
  refine norm_coeff_le fun x => hA _ fun v => ?_
  have him : (ptXY x y v).im = y v := congrFun (imVec_ptXY hy) v
  rw [him]
  linarith [le_abs_self A]

/-- **Positive dual vectors have trace at least $1/N$** when $N\mathbf 1 \in \Lambda$: if $\nu$ is dual, $\nu \ge 0$ and $\nu \ne 0$, then
$N\langle\nu, \mathbf 1\rangle \ge 1$. -/
lemma one_le_mul_pair_one {b : Module.Basis J ℝ (ι → ℝ)} {N : ℕ} (hN : 0 < N) (m : J → ℤ)
    (hm : b.equivFun.symm (fun j => (m j : ℝ)) = fun _ => (N : ℝ)) {ν : ι → ℝ} (hν : IsDual b ν)
    (hnn : ∀ v, 0 ≤ ν v) (h0 : ν ≠ 0) : 1 ≤ (N : ℝ) * pair ν 1 := by
  obtain ⟨n, hn⟩ := hν.pair_int m
  rw [hm] at hn
  have hNp : (N : ℝ) * pair ν 1 = n := by
    rw [← hn]; simp only [pair, Pi.one_apply, mul_one, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  have hpos : 0 < pair ν 1 := by
    obtain ⟨w, hw⟩ : ∃ w, ν w ≠ 0 := by
      by_contra h; push Not at h; exact h0 (funext h)
    simp only [pair, Pi.one_apply, mul_one]
    exact Finset.sum_pos' (fun v _ => hnn v) ⟨w, Finset.mem_univ w, lt_of_le_of_ne (hnn w) (Ne.symm hw)⟩
  rw [hNp]
  have : (0 : ℝ) < n := by rw [← hNp]; exact mul_pos (by exact_mod_cast hN) hpos
  have : (1 : ℤ) ≤ n := by exact_mod_cast this
  exact_mod_cast this

/-- **Support of the $q$-expansion of a function vanishing at $i\infty$**: $a_\nu \ne 0$ implies $\nu \ge 0$ and $\nu \ne 0$. -/
lemma qCoeff_support_of_isZeroAtImInftyPi [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b)
    (hz : IsZeroAtImInftyPi f) (n : J → ℤ) (hn : qCoeff f b (dualVec b n) ≠ 0) :
    (∀ v, 0 ≤ dualVec b n v) ∧ dualVec b n ≠ 0 := by
  refine ⟨fun w => ?_, fun h0 => hn (h0 ▸ qCoeff_zero_eq_zero hf hper hz)⟩
  by_contra hw
  rw [not_le] at hw
  obtain ⟨A, hA⟩ := hz.exists_bound one_pos
  have hbd : ∀ x y, (∀ v, A ≤ y v) → (∀ v, 0 < y v) → ‖f (ptXY x y)‖ ≤ 1 := by
    intro x y hAy hy
    refine hA _ fun v => ?_
    rw [show (ptXY x y v).im = y v from congrFun (imVec_ptXY hy) v]
    exact hAy v
  have h0 := coeff_eq_zero_of_isBounded hf hper (isDual_dualVec b n) hbd hw (y := 1)
    (fun _ => one_pos)
  exact hn (by rw [qCoeff, h0, zero_mul])

/-- **Exponential decay at $i\infty$.** Let $f$ be holomorphic on $\mathbb{H}^\iota$, periodic for $\Lambda = \bigoplus_j\mathbb{Z}b_j$, with
$f(z) \to 0$ as $\min_v\operatorname{Im}z_v \to \infty$, and suppose $N\mathbf 1 \in \Lambda$ ($N \ge 1$; `hm`). Then for every $c > 0$
there is $M$ such that
$$|f(z)| \le M\,e^{-2\pi t/N}\qquad\text{whenever } t \ge 0 \text{ and } \operatorname{Im}z_v \ge c + t \text{ for every } v.$$

Parameters: `hf` (holomorphy), `hper` (periodicity), `hz` (vanishing at $i\infty$), `N`, `hN` ($N \ge 1$), `m`, `hm`
($\sum_jm_jb_j = N\mathbf 1$), `c`, `hc` ($c > 0$). -/
@[kb "garrett1990" "Ch. 1, Fourier expansions at the cusps; cusp forms decay exponentially [unverified]"]
theorem exists_norm_le_exp_of_isZeroAtImInftyPi [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b)
    (hz : IsZeroAtImInftyPi f) {N : ℕ} (hN : 0 < N) (m : J → ℤ)
    (hm : b.equivFun.symm (fun j => (m j : ℝ)) = fun _ => (N : ℝ)) {c : ℝ} (hc : 0 < c) :
    ∃ M, ∀ z : ι → ℍ, ∀ t : ℝ, 0 ≤ t → (∀ v, c + t ≤ (z v).im) →
      ‖f z‖ ≤ M * Real.exp (-2 * π * t / N) := by
  set z₀ : ι → ℍ := ptXY 0 (fun _ => c)
  have hz₀ : imVec z₀ = fun _ => c := imVec_ptXY fun _ => hc
  have hs₀ := summable_norm_qExpansion hf hper z₀
  refine ⟨∑' n, ‖qCoeff f b (dualVec b n) * qTerm (dualVec b n) z₀‖, fun z t ht hzt => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← (hasSum_qExpansion hf hper z).tsum_eq, ← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm (summable_norm_qExpansion hf hper z)).trans
    ((summable_norm_qExpansion hf hper z).tsum_le_tsum (fun n => ?_) (hs₀.mul_right _))
  rw [norm_mul, norm_mul, norm_qTerm, norm_qTerm, hz₀]
  by_cases h0 : qCoeff f b (dualVec b n) = 0
  · simp [h0]
  obtain ⟨hnn, hne⟩ := qCoeff_support_of_isZeroAtImInftyPi hf hper hz n h0
  have hone := one_le_mul_pair_one hN m hm (isDual_dualVec b n) hnn hne
  refine (mul_le_mul_of_nonneg_left ?_ (norm_nonneg (qCoeff f b (dualVec b n)))).trans_eq
    (mul_assoc _ _ _).symm
  rw [← Real.exp_add, Real.exp_le_exp]
  have hle : pair (dualVec b n) (fun _ => c) + t * pair (dualVec b n) 1 ≤
      pair (dualVec b n) (imVec z) := by
    simp only [pair, Pi.one_apply, mul_one, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have := mul_le_mul_of_nonneg_left (hzt v) (hnn v)
    simp only [imVec]; nlinarith
  have ht' : t / N ≤ t * pair (dualVec b n) 1 := by
    rw [div_le_iff₀ hNpos]; nlinarith
  have : -2 * π * pair (dualVec b n) (imVec z) ≤
      -2 * π * (pair (dualVec b n) (fun _ => c) + t / N) := by nlinarith [Real.pi_pos]
  have e : -2 * π * t / N = -2 * π * (t / N) := by ring
  rw [e]; linarith

end QuadFormsKB.HilbertModular
