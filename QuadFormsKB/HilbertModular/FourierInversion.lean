/-
# Hilbert modular forms VI: Fourier inversion ($q$-expansions)

Setting as in `QExpansion.lean`: $\iota$ finite, $b = (b_j)_{j\in J}$ an $\mathbb{R}$-basis of $\mathbb{R}^\iota$ with lattice
$\Lambda = \bigoplus_j\mathbb{Z}b_j$ (for $F$: a fractional ideal, `koecherBasis`), $f : \mathbb{H}^\iota \to \mathbb{C}$ holomorphic and
$\Lambda$-periodic, $\langle\nu, x\rangle = \sum_v\nu_vx_v$.

* **The dual lattice** $\Lambda^\vee = \{\nu : \langle\nu, b_j\rangle \in \mathbb{Z}\ \forall j\}$ is parametrized by $\mathbb{Z}^J$:
  $\nu_n$ = `dualVec b n` is the vector with $\langle\nu_n, b_j\rangle = n_j$ (`pair_dualVec`); every dual vector is some $\nu_n$
  (`IsDual.exists_dualVec`), and $n \mapsto \nu_n$ is injective.
* **Torus picture.** $g_y(\theta) = f(x(\theta) + iy)$ is a continuous function on $(\mathbb{R}/\mathbb{Z})^J$ (`torusFunC`), and
  $c_{\nu_n}(y)$ is its $n$-th Fourier coefficient in Mathlib's sense (`coeff_eq_mFourierCoeff`, `mFourierCoeff`).
* **Decay** (`exists_norm_coeff_le_exp`): for $0 < \delta < \min_v y_v$, $|c_\nu(y)| \le B\,e^{-2\pi\delta\|\nu\|_1}$ (holomorphy moves $y$
  by $\pm\delta$ in each coordinate); and $\sum_n e^{-a\|\nu_n\|_1} < \infty$ (`summable_exp_neg_l1`).
* **Fourier inversion** (`hasSum_qExpansion`): $f(z) = \sum_{n\in\mathbb{Z}^J}a_{\nu_n}e(\langle\nu_n, z\rangle)$ for all $z \in \mathbb{H}^\iota$,
  $e(\langle\nu, z\rangle) = \exp(2\pi i\sum_v\nu_vz_v)$ (`qTerm`), $a_\nu$ = `qCoeff`; absolutely (`summable_norm_qExpansion`) and
  locally uniformly (`tendstoLocallyUniformly_qExpansion`). *Proof:* Mathlib's
  `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` applied to $g_y$, whose coefficients are summable by the decay bound.
* **Uniqueness** (`qCoeff_unique`): an absolutely convergent expansion $f(x+iy) = \sum_n\alpha_ne(\langle\nu_n, x+iy\rangle)$ at one
  height $y$ has $\alpha_n = a_{\nu_n}$ (termwise integration, `mFourierCoeff_eq_of_hasSum`).

For $F$ totally real and $\Lambda$ the image of a fractional ideal $I$, $\langle\nu, z\rangle = \operatorname{Tr}(\nu z)$ and $\Lambda^\vee$ is the
image of the trace dual $I^\vee$ (`KoecherBounded.lean`, `dualVec_koecherBasis`).

Sources: Garrett, *Holomorphic Hilbert Modular Forms* (1990), Ch. 1 [unverified]; Freitag, *Hilbert Modular Forms* (1990),
Ch. I §4 [unverified].
-/
import QuadFormsKB.HilbertModular.QExpansion

open MeasureTheory Set Filter Topology Complex UpperHalfPlane UnitAddTorus
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

/-! ### The dual lattice -/

lemma pair_comm (ν x : ι → ℝ) : pair ν x = pair x ν := by
  simp only [pair, mul_comm]

lemma pair_eq_sum_coord (b : Module.Basis J ℝ (ι → ℝ)) (ν x : ι → ℝ) :
    pair ν x = ∑ j, b.equivFun x j * pair ν (b j) := by
  conv_lhs => rw [← b.sum_equivFun x]
  simp only [pair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => by ring

lemma eq_zero_of_pair_self {ν : ι → ℝ} (h : pair ν ν = 0) : ν = 0 := by
  funext v
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_self_nonneg (ν v))).mp h v
    (Finset.mem_univ _)
  simpa using mul_self_eq_zero.mp this

/-- $\nu \mapsto (\langle\nu, b_j\rangle)_j$. -/
noncomputable def pairMap (b : Module.Basis J ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun ν j := pair ν (b j)
  map_add' ν ν' := by funext j; simp [pair, add_mul, Finset.sum_add_distrib]
  map_smul' c ν := by funext j; simp [pair, Finset.mul_sum, mul_assoc]

lemma pairMap_injective (b : Module.Basis J ℝ (ι → ℝ)) : Function.Injective (pairMap b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ν h
  apply eq_zero_of_pair_self
  rw [pair_eq_sum_coord b ν ν]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : pair ν (b j) = 0 := congrFun h j
  rw [this, mul_zero]

/-- The isomorphism $\nu \mapsto (\langle\nu, b_j\rangle)_j$, $\mathbb{R}^\iota \cong \mathbb{R}^J$. -/
noncomputable def pairEquiv (b : Module.Basis J ℝ (ι → ℝ)) : (ι → ℝ) ≃ₗ[ℝ] (J → ℝ) :=
  LinearEquiv.ofBijective (pairMap b) ⟨pairMap_injective b,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        ← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card])).mp (pairMap_injective b)⟩

/-- **The dual lattice vectors** $\nu_n = \sum_j n_jb_j^\vee$, $n \in \mathbb{Z}^J$: the vector with $\langle\nu_n, b_j\rangle = n_j$. -/
noncomputable def dualVec (b : Module.Basis J ℝ (ι → ℝ)) (n : J → ℤ) : ι → ℝ :=
  (pairEquiv b).symm (fun j => (n j : ℝ))

lemma pair_dualVec (b : Module.Basis J ℝ (ι → ℝ)) (n : J → ℤ) (j : J) :
    pair (dualVec b n) (b j) = n j := by
  have := congrFun ((pairEquiv b).apply_symm_apply (fun j => (n j : ℝ))) j
  exact this

lemma isDual_dualVec (b : Module.Basis J ℝ (ι → ℝ)) (n : J → ℤ) : IsDual b (dualVec b n) :=
  fun j => ⟨n j, pair_dualVec b n j⟩

lemma dualVec_injective (b : Module.Basis J ℝ (ι → ℝ)) : Function.Injective (dualVec b) := by
  intro n n' h
  funext j
  have := pair_dualVec b n j
  rw [h, pair_dualVec] at this
  exact_mod_cast this.symm

/-- Every dual vector is some $\nu_n$. -/
lemma IsDual.exists_dualVec {b : Module.Basis J ℝ (ι → ℝ)} {ν : ι → ℝ} (hν : IsDual b ν) :
    ∃ n, dualVec b n = ν := by
  choose n hn using hν
  refine ⟨n, (pairEquiv b).injective ?_⟩
  rw [dualVec, LinearEquiv.apply_symm_apply]
  funext j
  exact (hn j).symm

lemma pair_dualVec_symm (b : Module.Basis J ℝ (ι → ℝ)) (n : J → ℤ) (t : J → ℝ) :
    pair (dualVec b n) (b.equivFun.symm t) = ∑ j, (n j : ℝ) * t j := by
  rw [pair_eq_sum_coord b, LinearEquiv.apply_symm_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [pair_dualVec, mul_comm]

/-! ### The torus function -/

/-- The projection $\mathbb{R}^J \to (\mathbb{R}/\mathbb{Z})^J$. -/
def torusMk (t : J → ℝ) : UnitAddTorus J := fun j => (t j : UnitAddCircle)

lemma isOpenQuotientMap_torusMk : IsOpenQuotientMap (torusMk : (J → ℝ) → UnitAddTorus J) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

/-- **The slice of $f$ at height $y$ as a function on the torus**: $\theta \mapsto f(x(\theta) + iy)$, $x(\theta) = \sum_j\theta_jb_j$
(well defined for $\Lambda$-periodic $f$; we use the representatives in $(0, 1]$). -/
noncomputable def torusFun (f : (ι → ℍ) → ℂ) (b : Module.Basis J ℝ (ι → ℝ)) (y : ι → ℝ)
    (θ : UnitAddTorus J) : ℂ :=
  f (ptXY (b.equivFun.symm (fun j => ((AddCircle.equivIoc 1 0 (θ j)) : ℝ))) y)

lemma torusFun_mk {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hper : IsLatticePeriodic f b)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) (t : J → ℝ) :
    torusFun f b y (torusMk t) = f (ptXY (b.equivFun.symm t) y) := by
  choose n hn using fun i => rep_sub_int (t i)
  simp only [torusFun, torusMk]
  rw [show (fun j => ((AddCircle.equivIoc 1 0 ((t j : UnitAddCircle))) : ℝ)) =
    t + fun j => (n j : ℝ) from funext fun j => hn j, map_add]
  exact hper n _ y hy

lemma continuous_torusFun {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hf : Continuous f)
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    Continuous (torusFun f b y) := by
  rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff]
  have : torusFun f b y ∘ torusMk = fun t => f (ptXY (b.equivFun.symm t) y) :=
    funext fun t => torusFun_mk hper hy t
  rw [this]
  exact (continuous_ptXY hy hf).comp
    (b.equivFun.symm : (J → ℝ) →ₗ[ℝ] (ι → ℝ)).continuous_of_finiteDimensional

/-- The torus function as a bundled continuous map. -/
noncomputable def torusFunC {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hf : Continuous f)
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) : C(UnitAddTorus J, ℂ) :=
  ⟨torusFun f b y, continuous_torusFun hf hper hy⟩

lemma mFourier_torusMk (n : J → ℤ) (t : J → ℝ) :
    mFourier n (torusMk t) = cexp (2 * π * Complex.I * ∑ j, (n j : ℝ) * t j) := by
  simp only [mFourier, ContinuousMap.coe_mk, torusMk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The coefficients are the torus Fourier coefficients**: $c_{\nu_n}(y) = \hat g_y(n)$. -/
lemma coeff_eq_mFourierCoeff {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) (n : J → ℤ) :
    coeff f b (dualVec b n) y = mFourierCoeff (torusFun f b y) n := by
  rw [mFourierCoeff_eq_integral _ n 0, coeff]
  have hs : {x : J → ℝ | ∀ i, x i ∈ Ioc ((0 : J → ℝ) i) ((0 : J → ℝ) i + 1)} = unitCube J := by
    ext t; simp [unitCube]
  rw [hs]
  refine setIntegral_congr_fun measurableSet_unitCube fun t _ => ?_
  have h1 := torusFun_mk hper hy t
  have h2 := mFourier_torusMk (-n) t
  change _ = mFourier (-n) (torusMk t) • torusFun f b y (torusMk t)
  rw [h1, h2, smul_eq_mul, mul_comm, pair_dualVec_symm]
  congr 2
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring


/-! ### Exponential decay of the coefficients and summability -/

/-- $\|\nu\|_1 = \sum_v|\nu_v|$. -/
def l1 (ν : ι → ℝ) : ℝ := ∑ v, |ν v|

lemma l1_nonneg (ν : ι → ℝ) : 0 ≤ l1 ν := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma abs_pair_le (ν x : ι → ℝ) : |pair ν x| ≤ l1 ν * l1 x := by
  calc |pair ν x| ≤ ∑ v, |ν v * x v| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v, |ν v| * |x v| := by simp [abs_mul]
    _ ≤ ∑ v, |ν v| * l1 x := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun u => |x u|)
          (fun u _ => abs_nonneg _) (Finset.mem_univ v)) (abs_nonneg _)
    _ = l1 ν * l1 x := by simp only [l1, Finset.sum_mul]

/-- The sign vector $s_v = \pm 1$. -/
def sgnVec (s : ι → Bool) : ι → ℝ := fun v => if s v then 1 else -1

/-- **Exponential decay of the Fourier coefficients**: for $0 < \delta < \min_v y_v$ there is $B$ with
$|c_\nu(y)| \le B\,e^{-2\pi\delta\|\nu\|_1}$ for every dual vector $\nu$ ($\|\nu\|_1 = \sum_v|\nu_v|$). *Proof:* move $y$ by
$-\delta\operatorname{sgn}(\nu)$ (`coeff_eq_exp_mul`) and use the slice bounds at the $2^d$ points $y - \delta s$. -/
lemma exists_norm_coeff_le_exp [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {y : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hδy : ∀ v, δ < y v) :
    ∃ B, ∀ ν, IsDual b ν → ‖coeff f b ν y‖ ≤ B * Real.exp (-2 * π * δ * l1 ν) := by
  have hy : ∀ v, 0 < y v := fun v => hδ.trans (hδy v)
  set ys : (ι → Bool) → ι → ℝ := fun s => y - δ • sgnVec s with hys
  have hyspos : ∀ s v, 0 < ys s v := by
    intro s v
    simp only [hys, Pi.sub_apply, Pi.smul_apply, sgnVec, smul_eq_mul]
    split_ifs <;> linarith [hδy v]
  choose B hB using fun s => exists_bound_slice hf.1 hper (hyspos s)
  refine ⟨∑ s, |B s|, fun ν hν => ?_⟩
  set s : ι → Bool := fun v => decide (0 ≤ ν v) with hsdef
  have h := coeff_eq_exp_mul hf hper hν (hyspos s) hy
  have hp : pair ν (y - ys s) = δ * l1 ν := by
    simp only [hys, sub_sub_cancel, pair_smul, l1]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [sgnVec, hsdef]
    by_cases h0 : 0 ≤ ν v
    · simp [h0, abs_of_nonneg h0]
    · simp [h0, abs_of_neg (lt_of_not_ge h0)]
  rw [h, hp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  refine mul_le_mul ?_ (by rw [show -2 * π * (δ * l1 ν) = -2 * π * δ * l1 ν by ring])
    (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  exact (norm_coeff_le (hB s)).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |B s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)))

lemma summable_prod_fin (g : ℤ → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    ∀ m : ℕ, Summable fun n : Fin m → ℤ => ∏ i, g (n i)
  | 0 => Summable.of_finite
  | m + 1 => by
    have ih := summable_prod_fin g hg0 hg m
    have h2 := Summable.mul_of_nonneg hg ih hg0 (fun n => Finset.prod_nonneg fun i _ => hg0 _)
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).summable_iff]
    convert h2 using 1
    funext p
    simp [Fin.prod_univ_succ, Fin.consEquiv]

lemma summable_prod_fintype (g : ℤ → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    Summable fun n : J → ℤ => ∏ j, g (n j) := by
  classical
  set e := Fintype.equivFin J
  have h := summable_prod_fin g hg0 hg (Fintype.card J)
  rw [← (e.arrowCongr (Equiv.refl ℤ)).symm.summable_iff]
  convert h using 1
  funext n
  simp only [Function.comp_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Equiv.symm_symm]
  exact Fintype.prod_equiv e _ _ fun j => rfl

lemma summable_exp_neg_sum_abs {a : ℝ} (ha : 0 < a) :
    Summable fun n : J → ℤ => Real.exp (-a * ∑ j, |(n j : ℝ)|) := by
  have hr : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg : Summable fun k : ℤ => Real.exp (-a) ^ k.natAbs := by
    refine Summable.of_nat_of_neg ?_ ?_ <;>
      simpa using summable_geometric_of_lt_one (Real.exp_pos _).le hr
  convert summable_prod_fintype _ (fun k => by positivity) hg using 1
  funext n
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
  ring_nf

/-- $\sum_{n\in\mathbb{Z}^J}e^{-a\|\nu_n\|_1}$ converges for $a > 0$. -/
lemma summable_exp_neg_l1 (b : Module.Basis J ℝ (ι → ℝ)) {a : ℝ} (ha : 0 < a) :
    Summable fun n : J → ℤ => Real.exp (-a * l1 (dualVec b n)) := by
  set C : ℝ := ∑ j, l1 (b j) + 1 with hC
  have hC0 : 0 < C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => l1_nonneg (b j); linarith
  refine (summable_exp_neg_sum_abs (J := J) (div_pos ha hC0)).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) fun n => Real.exp_le_exp.mpr ?_
  have hn : ∑ j, |(n j : ℝ)| ≤ C * l1 (dualVec b n) := by
    calc ∑ j, |(n j : ℝ)| = ∑ j, |pair (dualVec b n) (b j)| := by simp [pair_dualVec]
      _ ≤ ∑ j, l1 (dualVec b n) * l1 (b j) := Finset.sum_le_sum fun j _ => abs_pair_le _ _
      _ = l1 (dualVec b n) * (C - 1) := by rw [← Finset.mul_sum]; ring
      _ ≤ C * l1 (dualVec b n) := by nlinarith [l1_nonneg (dualVec b n)]
  rw [neg_mul, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff₀ hC0]
  nlinarith

/-! ### Fourier inversion -/

lemma exists_pos_lt_min {y : ι → ℝ} (hy : ∀ v, 0 < y v) : ∃ δ, 0 < δ ∧ ∀ v, δ < y v := by
  by_cases h : Nonempty ι
  · obtain ⟨v₀, hv₀⟩ := Finite.exists_min y
    exact ⟨y v₀ / 2, by linarith [hy v₀], fun v => by linarith [hv₀ v, hy v₀]⟩
  · exact ⟨1, one_pos, fun v => (h ⟨v⟩).elim⟩

lemma abs_pair_le_of_abs_le {ν w : ι → ℝ} {r : ℝ} (hw : ∀ v, |w v| ≤ r) :
    |pair ν w| ≤ r * l1 ν := by
  calc |pair ν w| ≤ ∑ v, |ν v * w v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, |ν v| * r := Finset.sum_le_sum fun v _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw v) (abs_nonneg _)
    _ = r * l1 ν := by rw [l1, ← Finset.sum_mul, mul_comm]

/-- **Local normal bound for the coefficients**: every $y > 0$ has a neighbourhood $U \subseteq \mathbb{R}^\iota_{>0}$ and a summable
majorant $M$ with $|c_{\nu_n}(y')| \le M_n$ for all $y' \in U$, $n \in \mathbb{Z}^J$. -/
lemma exists_local_majorant [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    ∃ U ∈ 𝓝 y, (∀ y' ∈ U, ∀ v, 0 < y' v) ∧ ∃ M : (J → ℤ) → ℝ, Summable M ∧
      ∀ n, ∀ y' ∈ U, ‖coeff f b (dualVec b n) y'‖ ≤ M n := by
  obtain ⟨δ, hδ, hδy⟩ := exists_pos_lt_min hy
  obtain ⟨B, hB⟩ := exists_norm_coeff_le_exp hf hper hδ hδy
  refine ⟨Metric.ball y (δ / 2), Metric.ball_mem_nhds _ (by linarith), ?_,
    fun n => B * Real.exp (-(π * δ) * l1 (dualVec b n)), ?_, ?_⟩
  · intro y' hy' v
    have := (dist_pi_lt_iff (by linarith)).mp (Metric.mem_ball.mp hy') v
    rw [Real.dist_eq] at this
    linarith [abs_lt.mp this, hδy v]
  · exact (summable_exp_neg_l1 b (by positivity)).mul_left B
  · intro n y' hy'
    have hy'pos : ∀ v, 0 < y' v := by
      intro v
      have := (dist_pi_lt_iff (by linarith)).mp (Metric.mem_ball.mp hy') v
      rw [Real.dist_eq] at this
      linarith [abs_lt.mp this, hδy v]
    have hw : ∀ v, |(y' - y) v| ≤ δ / 2 := fun v => by
      have := (dist_pi_lt_iff (by linarith)).mp (Metric.mem_ball.mp hy') v
      rw [Real.dist_eq] at this
      exact this.le
    have hp := abs_pair_le_of_abs_le (ν := dualVec b n) hw
    rw [coeff_eq_exp_mul hf hper (isDual_dualVec b n) hy hy'pos, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hB' := hB _ (isDual_dualVec b n)
    have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
      ((norm_nonneg _).trans hB')
    have he : Real.exp (-2 * π * pair (dualVec b n) (y' - y)) ≤
        Real.exp (2 * π * (δ / 2) * l1 (dualVec b n)) := by
      rw [Real.exp_le_exp]
      have := neg_abs_le (pair (dualVec b n) (y' - y))
      nlinarith [Real.pi_pos]
    calc Real.exp (-2 * π * pair (dualVec b n) (y' - y)) * ‖coeff f b (dualVec b n) y‖
        ≤ Real.exp (2 * π * (δ / 2) * l1 (dualVec b n)) *
          (B * Real.exp (-2 * π * δ * l1 (dualVec b n))) :=
          mul_le_mul he hB' (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (-(π * δ) * l1 (dualVec b n)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- $(\operatorname{Re} z_v)_v$. -/
def reVec (z : ι → ℍ) : ι → ℝ := fun v => (z v).re

/-- $(\operatorname{Im} z_v)_v$. -/
def imVec (z : ι → ℍ) : ι → ℝ := fun v => (z v).im

lemma imVec_pos (z : ι → ℍ) : ∀ v, 0 < imVec z v := fun v => (z v).im_pos

lemma ptXY_re_im (z : ι → ℍ) : ptXY (reVec z) (imVec z) = z := by
  funext v
  apply UpperHalfPlane.ext
  rw [ptXY_im (imVec_pos z)]
  simp only [reVec, imVec]
  exact Complex.re_add_im (z v)

/-- **The exponential** $e(\langle\nu, z\rangle) = \exp\big(2\pi i\sum_v\nu_vz_v\big)$ on $\mathbb{H}^\iota$ (for $F$:
$e(\operatorname{Tr}(\nu z))$). -/
noncomputable def qTerm (ν : ι → ℝ) (z : ι → ℍ) : ℂ :=
  cexp (2 * π * Complex.I * ∑ v, (ν v : ℂ) * (z v : ℂ))

lemma qTerm_eq (ν : ι → ℝ) (z : ι → ℍ) :
    qTerm ν z = (Real.exp (-2 * π * pair ν (imVec z)) : ℂ) *
      cexp (2 * π * Complex.I * (pair ν (reVec z) : ℂ)) := by
  rw [qTerm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have : ∀ v, (z v : ℂ) = ((z v).re : ℂ) + ((z v).im : ℂ) * Complex.I := fun v =>
    (Complex.re_add_im (z v)).symm
  simp only [pair, reVec, imVec, this]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    ring_nf
    rw [Complex.I_sq]
    ring

lemma norm_qTerm (ν : ι → ℝ) (z : ι → ℍ) :
    ‖qTerm ν z‖ = Real.exp (-2 * π * pair ν (imVec z)) := by
  rw [qTerm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    show 2 * π * Complex.I * (pair ν (reVec z) : ℂ) = ((2 * π * pair ν (reVec z) : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma qCoeff_mul_qTerm [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    (z : ι → ℍ) :
    qCoeff f b ν * qTerm ν z =
      coeff f b ν (imVec z) * cexp (2 * π * Complex.I * (pair ν (reVec z) : ℂ)) := by
  rw [coeff_eq_qCoeff hf hper hν (imVec_pos z), qTerm_eq]
  ring

lemma norm_qCoeff_mul_qTerm [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    (z : ι → ℍ) : ‖qCoeff f b ν * qTerm ν z‖ = ‖coeff f b ν (imVec z)‖ := by
  rw [qCoeff_mul_qTerm hf hper hν, norm_mul,
    show 2 * π * Complex.I * (pair ν (reVec z) : ℂ) = ((2 * π * pair ν (reVec z) : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma summable_norm_coeff [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    Summable fun n => ‖coeff f b (dualVec b n) y‖ := by
  obtain ⟨U, hU, -, M, hM, hle⟩ := exists_local_majorant hf hper hy
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => hle n y (mem_of_mem_nhds hU)

/-- **Fourier inversion on a horizontal slice**: for $f$ holomorphic and $\Lambda$-periodic and $y > 0$,
$$f(x + iy) = \sum_{n\in\mathbb{Z}^J}c_{\nu_n}(y)\,e(\langle\nu_n, x\rangle),$$
the series converging absolutely (`summable_norm_coeff`). -/
theorem hasSum_coeff_slice [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v)
    (x : ι → ℝ) :
    HasSum (fun n => coeff f b (dualVec b n) y *
      cexp (2 * π * Complex.I * (pair (dualVec b n) x : ℂ))) (f (ptXY x y)) := by
  set g := torusFunC hf.1 hper hy
  have hsum : Summable (mFourierCoeff g) := by
    refine Summable.of_norm ?_
    have : ∀ n, mFourierCoeff g n = coeff f b (dualVec b n) y := fun n =>
      (coeff_eq_mFourierCoeff hper hy n).symm
    simp only [this]
    exact summable_norm_coeff hf hper hy
  have h := hasSum_mFourier_series_apply_of_summable hsum (torusMk (b.equivFun x))
  have hg : g (torusMk (b.equivFun x)) = f (ptXY x y) := by
    change torusFun f b y _ = _
    rw [torusFun_mk hper hy, LinearEquiv.symm_apply_apply]
  rw [hg] at h
  convert h using 2 with n
  rw [smul_eq_mul, mFourier_torusMk]
  change _ = mFourierCoeff (torusFun f b y) n * _
  rw [← coeff_eq_mFourierCoeff hper hy n]
  congr 3
  conv_lhs => rw [← b.equivFun.symm_apply_apply x]
  rw [pair_dualVec_symm]

/-- **Fourier inversion ($q$-expansion)** for $f$ holomorphic on $\mathbb{H}^\iota$ and periodic for the lattice
$\Lambda = \bigoplus_j\mathbb{Z}b_j$: for every $z \in \mathbb{H}^\iota$,
$$f(z) = \sum_{\nu\in\Lambda^\vee}a_\nu\,e(\langle\nu, z\rangle),\qquad e(\langle\nu, z\rangle) = \exp\Big(2\pi i\sum_v\nu_vz_v\Big),$$
with $a_\nu$ = `qCoeff f b ν` and $\Lambda^\vee = \{\nu_n : n \in \mathbb{Z}^J\}$ (`dualVec`, `IsDual.exists_dualVec`). The
convergence is absolute (`summable_norm_qExpansion`) and locally uniform (`tendstoLocallyUniformly_qExpansion`). -/
@[kb "garrett1990" "Ch. 1, Fourier expansions of Hilbert modular forms [unverified]"]
theorem hasSum_qExpansion [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (z : ι → ℍ) :
    HasSum (fun n => qCoeff f b (dualVec b n) * qTerm (dualVec b n) z) (f z) := by
  have h := hasSum_coeff_slice hf hper (imVec_pos z) (reVec z)
  rw [ptXY_re_im] at h
  simpa only [qCoeff_mul_qTerm hf hper (isDual_dualVec b _)] using h

/-- The $q$-expansion converges absolutely. -/
theorem summable_norm_qExpansion [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b)
    (z : ι → ℍ) : Summable fun n => ‖qCoeff f b (dualVec b n) * qTerm (dualVec b n) z‖ := by
  simpa only [norm_qCoeff_mul_qTerm hf hper (isDual_dualVec b _)] using
    summable_norm_coeff hf hper (imVec_pos z)

lemma continuous_imVec : Continuous (imVec : (ι → ℍ) → ι → ℝ) :=
  continuous_pi fun v => UpperHalfPlane.continuous_im.comp (continuous_apply v)

/-- **The $q$-expansion converges locally uniformly** on $\mathbb{H}^\iota$ (partial sums over finite sets of
$n \in \mathbb{Z}^J$; Weierstrass M-test with the majorants of `exists_local_majorant`). -/
theorem tendstoLocallyUniformly_qExpansion [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) :
    TendstoLocallyUniformly
      (fun s : Finset (J → ℤ) => fun z => ∑ n ∈ s, qCoeff f b (dualVec b n) * qTerm (dualVec b n) z)
      f atTop := by
  have hf' : f = fun z => ∑' n, qCoeff f b (dualVec b n) * qTerm (dualVec b n) z :=
    funext fun z => (hasSum_qExpansion hf hper z).tsum_eq.symm
  refine tendstoLocallyUniformly_of_forall_exists_nhds fun z => ?_
  obtain ⟨U, hU, -, M, hM, hle⟩ := exists_local_majorant hf hper (imVec_pos z)
  refine ⟨imVec ⁻¹' U, continuous_imVec.continuousAt.preimage_mem_nhds hU, ?_⟩
  conv => enter [2]; rw [hf']
  refine tendstoUniformlyOn_tsum hM fun n w hw => ?_
  rw [norm_qCoeff_mul_qTerm hf hper (isDual_dualVec b _)]
  exact hle n _ hw

/-! ### Uniqueness of the coefficients -/

section Unique

/-- The measure on $\mathbb{R}/\mathbb{Z}$ used by Mathlib's torus Fourier theory (`Mathlib/Analysis/Fourier/AddCircleMulti.lean`):
the Haar probability measure. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)


lemma integral_mFourier (k : J → ℤ) :
    ∫ θ, mFourier k θ = if k = 0 then (1 : ℂ) else 0 := by
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := J)) 0 k
  simp only [mFourierLp, ContinuousMap.inner_toLp, mFourier_zero, ContinuousMap.one_apply,
    map_one, mul_one] at h
  exact h.trans (by simp only [eq_comm])

lemma norm_mFourier_apply (k : J → ℤ) (θ : UnitAddTorus J) : ‖mFourier k θ‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

lemma imVec_ptXY {x y : ι → ℝ} (hy : ∀ v, 0 < y v) : imVec (ptXY x y) = y := by
  funext v
  simp only [imVec, UpperHalfPlane.im, ptXY_im hy]
  simp

lemma reVec_ptXY {x y : ι → ℝ} (hy : ∀ v, 0 < y v) : reVec (ptXY x y) = x := by
  funext v
  simp only [reVec, UpperHalfPlane.re, ptXY_im hy]
  simp

/-- If a continuous function on the torus is the pointwise sum of an absolutely convergent trigonometric series
$\sum_m c_m\,e(\langle m, \theta\rangle)$, then $c_n$ is its $n$-th Fourier coefficient. -/
lemma mFourierCoeff_eq_of_hasSum {g : UnitAddTorus J → ℂ} {c : (J → ℤ) → ℂ}
    (hc : Summable fun m => ‖c m‖) (hg : ∀ θ, HasSum (fun m => c m * mFourier m θ) (g θ))
    (n : J → ℤ) : mFourierCoeff g n = c n := by
  have hF : ∀ m, Integrable (fun θ => mFourier (-n) θ * (c m * mFourier m θ)) := fun m =>
    ((mFourier (-n)).continuous.mul (continuous_const.mul (mFourier m).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ m, ∫ θ, ‖mFourier (-n) θ * (c m * mFourier m θ)‖ = ‖c m‖ := by
    intro m
    simp only [norm_mul, norm_mFourier_apply, one_mul, mul_one]
    simp
  have h := integral_tsum_of_summable_integral_norm hF (by simpa only [hnorm] using hc)
  rw [mFourierCoeff]
  simp only [smul_eq_mul]
  have hg' : ∀ θ, mFourier (-n) θ * g θ = ∑' m, mFourier (-n) θ * (c m * mFourier m θ) := by
    intro θ
    rw [(hg θ).tsum_eq.symm, tsum_mul_left]
  simp only [hg']
  refine h.symm.trans ?_
  have hm : ∀ m, ∫ θ, mFourier (-n) θ * (c m * mFourier m θ) = if m = n then c m else 0 := by
    intro m
    have : (fun θ => mFourier (-n) θ * (c m * mFourier m θ)) = fun θ => c m * mFourier (-n + m) θ := by
      funext θ; rw [mFourier_add]; ring
    rw [this, integral_const_mul, integral_mFourier]
    by_cases hmn : m = n
    · subst hmn; simp
    · have : -n + m ≠ 0 := fun h => hmn (by rw [neg_add_eq_zero] at h; exact h.symm)
      simp [this, hmn]
  simp only [hm]
  exact tsum_ite_eq n _

/-- **Uniqueness of the $q$-expansion.** If $f(x + iy) = \sum_n \alpha_n\,e(\langle\nu_n, x + iy\rangle)$ for all $x$ at one height
$y > 0$, with $\sum_n|\alpha_n|e^{-2\pi\langle\nu_n, y\rangle} < \infty$, then $\alpha_n = a_{\nu_n}$ (`qCoeff`) for all $n$. -/
theorem qCoeff_unique [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {α : (J → ℤ) → ℂ} {y : ι → ℝ}
    (hy : ∀ v, 0 < y v)
    (hsum : Summable fun n => ‖α n‖ * Real.exp (-2 * π * pair (dualVec b n) y))
    (hexp : ∀ x, HasSum (fun n => α n * qTerm (dualVec b n) (ptXY x y)) (f (ptXY x y)))
    (n : J → ℤ) : α n = qCoeff f b (dualVec b n) := by
  set c : (J → ℤ) → ℂ := fun m => α m * (Real.exp (-2 * π * pair (dualVec b m) y) : ℂ) with hcdef
  have hc : Summable fun m => ‖c m‖ := by
    simpa only [hcdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      using hsum
  have hg : ∀ θ, HasSum (fun m => c m * mFourier m θ) (torusFun f b y θ) := by
    intro θ
    set t : J → ℝ := fun j => ((AddCircle.equivIoc 1 0 (θ j)) : ℝ)
    have hθ : torusMk t = θ := funext fun j => AddCircle.coe_equivIoc
    rw [← hθ, torusFun_mk hper hy]
    convert hexp (b.equivFun.symm t) using 2 with m
    rw [qTerm_eq, imVec_ptXY hy, reVec_ptXY hy, pair_dualVec_symm, mFourier_torusMk, hcdef]
    push_cast
    ring
  have h := mFourierCoeff_eq_of_hasSum hc hg n
  rw [← coeff_eq_mFourierCoeff hper hy, coeff_eq_qCoeff hf hper (isDual_dualVec b n) hy,
    hcdef] at h
  exact (mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') h).symm

end Unique

end QuadFormsKB.HilbertModular
