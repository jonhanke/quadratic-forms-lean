/-
# Weight-2 Eisenstein series with residue weight: Fourier expansion, holomorphy, behaviour at $i\infty$

For an $M$-periodic weight $\beta$ and $C \ge 1$, the row sum has the Lipschitz expansion (`row_expansion`)
$$\sum_d\beta(d)\,(Cz+d)^{-2} = \frac{(-2\pi i)^2}{M^2}\sum_{r=0}^{M-1}\beta(r)\sum_{n \ge 0}n\,e^{2\pi i n(Cz+r)/M},$$
hence the decay bound `norm_row_le`. Consequences for $E_W$ (`EisensteinWt2/General.lean`): it is holomorphic on
$\mathbb{H}$ (`mdifferentiable_eis2`) and tends to its constant term $\sum_d W(0,d)d^{-2}$ at $i\infty$
(`tendsto_eis2_atImInfty`).
-/
import QuadFormsKB.Siegel.EisensteinWt2.General

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups Manifold

namespace QuadFormsKB.Siegel.EisensteinWt2

/-- Splitting a sum over $\mathbb{Z}$ into residue classes mod $M$. -/
lemma tsum_int_split {M : ℕ} [NeZero M] {f : ℤ → ℂ} (hf : Summable f) :
    ∑' d, f d = ∑ r : Fin M, ∑' k : ℤ, f (k * M + r) := by
  rw [← (Int.divModEquiv M).symm.tsum_eq]
  have hs : Summable fun p : ℤ × Fin M => f (p.1 * M + p.2) :=
    ((Int.divModEquiv M).symm.summable_iff.mpr hf).congr fun p => by simp
  have h2 : ∀ r : Fin M, Summable fun k : ℤ => f (k * M + r) := fun r =>
    hf.comp_injective fun a b h => by
      have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
      exact mul_right_cancel₀ hM (add_right_cancel h)
  calc ∑' p, f ((Int.divModEquiv M).symm p) = ∑' p : ℤ × Fin M, f (p.1 * M + p.2) :=
        tsum_congr fun p => by simp
    _ = ∑' k : ℤ, ∑ r : Fin M, f (k * M + r) := by rw [hs.tsum_prod]; simp [tsum_fintype]
    _ = _ := Summable.tsum_finsetSum fun r _ => h2 r

/-- $\sum_{n \ge 0} n q^n$ is bounded by $|q|/(1-|q|)^2$. -/
lemma norm_tsum_nat_mul_pow_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ, (n : ℂ) * q ^ n‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 2 := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hgeo : HasSum (fun k : ℕ => (k : ℝ) * ‖q‖ ^ k) (‖q‖ / (1 - ‖q‖) ^ 2) := by
    have hs : Summable (fun k : ℕ => (k : ℝ) * ‖q‖ ^ k) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hq0])
    rw [← tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (by rwa [Real.norm_of_nonneg hq0])]
    exact hs.hasSum
  exact tsum_of_norm_bounded hgeo fun k => by rw [norm_mul, norm_pow, Complex.norm_natCast]

lemma norm_cexp_two_pi_I (w : ℂ) : ‖cexp (2 * π * I * w)‖ = Real.exp (-2 * π * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

variable {M : ℕ} [NeZero M]

/-- **Lipschitz expansion of a periodic-weight row.** For $\beta$ $M$-periodic and $C \ge 1$:
$\sum_d\beta(d)(Cz+d)^{-2} = \frac{(-2\pi i)^2}{M^2}\sum_{r}\beta(r)\sum_{n \ge 0}n\,e^{2\pi i n(Cz+r)/M}$. -/
theorem row_expansion {β : ℤ → ℂ} (hβ : ∀ d, β (d + M) = β d) {B : ℝ} (hB : ∀ d, ‖β d‖ ≤ B)
    {C : ℕ} (hC : 0 < C) (z : ℍ) :
    ∑' d : ℤ, β d * (((C : ℂ) * z + d) ^ 2)⁻¹ =
      (-2 * π * I) ^ 2 / (M : ℂ) ^ 2 * ∑ r : Fin M, β r *
        ∑' n : ℕ, (n : ℂ) * cexp (2 * π * I * (((C : ℂ) * z + (r : ℕ)) / M)) ^ n := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hsum : Summable fun d : ℤ => β d * (((C : ℂ) * z + d) ^ 2)⁻¹ :=
    Summable.of_norm_bounded
      (((EisensteinSeries.linear_right_summable z C (k := 2) le_rfl).norm).mul_left B) fun d => by
        rw [norm_mul]
        refine mul_le_mul (hB d) (le_of_eq ?_) (norm_nonneg _) ((norm_nonneg _).trans (hB d))
        simp
  rw [tsum_int_split (M := M) hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  set w : ℂ := ((C : ℂ) * z + (r : ℕ)) / M with hw
  have hwim : 0 < w.im := by
    rw [hw, div_im]
    simp only [add_im, mul_im, natCast_re, UpperHalfPlane.coe_im, natCast_im, UpperHalfPlane.coe_re,
      zero_mul, add_zero, normSq_natCast, add_re, mul_re, sub_zero, natCast_re]
    have : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have hc : 0 < (C : ℝ) := by exact_mod_cast hC
    have := z.im_pos
    simp only [mul_zero, sub_zero, zero_div, sub_zero]
    positivity
  have hP : Function.Periodic β (M : ℤ) := hβ
  have hterm : ∀ k : ℤ, β (k * M + r) * (((C : ℂ) * z + ((k * M + r : ℤ) : ℂ)) ^ 2)⁻¹ =
      β r * ((M : ℂ) ^ 2)⁻¹ * ((w + k) ^ 2)⁻¹ := by
    intro k
    have h1 : β (k * M + r) = β r := by rw [add_comm]; exact hP.int_mul k (r : ℤ)
    rw [h1, hw]
    push_cast
    field_simp
    ring_nf
  rw [tsum_congr hterm, tsum_mul_left]
  have hq := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨w, hwim⟩
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one, one_div] at hq
  rw [show (∑' k : ℤ, ((w + k) ^ 2)⁻¹) = ∑' k : ℤ, ((((⟨w, hwim⟩ : ℍ) : ℂ) + k) ^ (1 + 1))⁻¹ by rfl, hq]
  field_simp
  ring

/-- **Decay of a periodic-weight row:** for $c \ne 0$, with $x = e^{-2\pi\operatorname{Im}z/M}$,
$\bigl|\sum_d\beta(d)(cz+d)^{-2}\bigr| \le \frac{4\pi^2}{M}\,B\,\frac{x^{|c|}}{(1-x)^2}$. -/
theorem norm_row_le {β : ℤ → ℂ} (hβ : ∀ d, β (d + M) = β d) {B : ℝ} (hB : ∀ d, ‖β d‖ ≤ B)
    {c : ℤ} (hc : c ≠ 0) (z : ℍ) :
    ‖∑' d : ℤ, β d * (((c : ℂ) * z + d) ^ 2)⁻¹‖ ≤
      4 * π ^ 2 / M * B * (Real.exp (-2 * π * z.im / M) ^ c.natAbs /
        (1 - Real.exp (-2 * π * z.im / M)) ^ 2) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set x := Real.exp (-2 * π * z.im / M) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by
    have := z.im_pos; have := Real.pi_pos
    rw [neg_mul, neg_mul, neg_div]; exact neg_neg_of_pos (by positivity))
  -- reduce to c = C > 0
  have key : ∀ (β' : ℤ → ℂ), (∀ d, β' (d + M) = β' d) → (∀ d, ‖β' d‖ ≤ B) → ∀ C : ℕ, 0 < C →
      ‖∑' d : ℤ, β' d * (((C : ℂ) * z + d) ^ 2)⁻¹‖ ≤ 4 * π ^ 2 / M * B * (x ^ C / (1 - x) ^ 2) := by
    intro β' hβ' hB' C hC
    rw [row_expansion hβ' hB' hC z, norm_mul]
    have hnorm : ‖(-2 * π * I : ℂ) ^ 2 / (M : ℂ) ^ 2‖ = 4 * π ^ 2 / M ^ 2 := by
      rw [norm_div, norm_pow, norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_natCast]
      ring
    have hrow : ∀ r : Fin M, ‖β' r * ∑' n : ℕ, (n : ℂ) *
        cexp (2 * π * I * (((C : ℂ) * z + (r : ℕ)) / M)) ^ n‖ ≤ B * (x ^ C / (1 - x) ^ 2) := by
      intro r
      set q := cexp (2 * π * I * (((C : ℂ) * z + (r : ℕ)) / M))
      have hq : ‖q‖ = x ^ C := by
        rw [norm_cexp_two_pi_I, hx, ← Real.exp_nat_mul]
        congr 1
        rw [div_im]
        simp only [add_im, mul_im, natCast_re, UpperHalfPlane.coe_im, natCast_im,
          UpperHalfPlane.coe_re, zero_mul, add_zero, normSq_natCast]
        field_simp
        ring
      have hxC : x ^ C < 1 := pow_lt_one₀ hx0.le hx1 hC.ne'
      rw [norm_mul]
      refine mul_le_mul (hB' r) ?_ (norm_nonneg _) hB0
      refine (norm_tsum_nat_mul_pow_le (hq ▸ hxC)).trans ?_
      rw [hq]
      apply div_le_div_of_nonneg_left (by positivity) (by nlinarith)
      have : x ^ C ≤ x := pow_le_of_le_one hx0.le hx1.le hC.ne'
      nlinarith
    rw [hnorm]
    calc 4 * π ^ 2 / M ^ 2 * ‖∑ r : Fin M, β' r * ∑' n : ℕ, (n : ℂ) *
          cexp (2 * π * I * (((C : ℂ) * z + (r : ℕ)) / M)) ^ n‖
        ≤ 4 * π ^ 2 / M ^ 2 * ∑ r : Fin M, B * (x ^ C / (1 - x) ^ 2) := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hrow r)
      _ = 4 * π ^ 2 / M * B * (x ^ C / (1 - x) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  rcases Int.natAbs_eq c with h | h
  · have := key β hβ hB c.natAbs (Int.natAbs_pos.mpr hc)
    rwa [← show ((c.natAbs : ℤ) : ℂ) = (c.natAbs : ℂ) by simp, ← h] at this
  · -- c = -C: substitute d ↦ -d
    have h' := key (fun d => β (-d)) (fun d => by
        rw [show -(d + M) = -d - M by ring]
        have := hβ (-d - M); rw [sub_add_cancel] at this; exact this.symm)
      (fun d => hB _) c.natAbs (Int.natAbs_pos.mpr hc)
    have heq : ∑' d : ℤ, β d * (((c : ℂ) * z + d) ^ 2)⁻¹ =
        ∑' d : ℤ, β (-d) * (((c.natAbs : ℂ) * z + d) ^ 2)⁻¹ := by
      rw [← (Equiv.neg ℤ).tsum_eq]
      refine tsum_congr fun d => ?_
      simp only [Equiv.neg_apply, Int.cast_neg]
      congr 1
      have hc' : (c : ℂ) = -(c.natAbs : ℂ) := by
        conv_lhs => rw [h]
        rw [Int.cast_neg, Int.cast_natCast]
      rw [hc']
      ring
    rw [heq]; exact h'

/-! ### $E_W$: decay of rows, holomorphy, and the limit at $i\infty$ -/

variable {N : ℕ} [NeZero N]

/-- The $c$-th row of $E_W$: $\sum_d W(c, d)(cz+d)^{-2}$ (for $z \in \mathbb{C}$). -/
noncomputable def rowW (W : ZMod N → ZMod N → ℂ) (c : ℤ) (w : ℂ) : ℂ :=
  ∑' d : ℤ, wt W c d * (((c : ℂ) * w + d) ^ 2)⁻¹

omit [NeZero N] in
lemma eis2_eq_tsum_rowW (W : ZMod N → ZMod N → ℂ) (z : ℍ) : eis2 W z = ∑' c, rowW W c z := rfl

omit [NeZero N] in
lemma rowW_zero (W : ZMod N → ZMod N → ℂ) (w w' : ℂ) : rowW W 0 w = rowW W 0 w' := by
  simp [rowW]

/-- The decay constant $x = e^{-2\pi y/N}$. -/
noncomputable def decayX (N : ℕ) (y : ℝ) : ℝ := Real.exp (-2 * π * y / N)

omit [NeZero N] in
lemma decayX_pos (y : ℝ) : 0 < decayX N y := Real.exp_pos _

lemma decayX_lt_one {y : ℝ} (hy : 0 < y) : decayX N y < 1 := by
  have hMpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine Real.exp_lt_one_iff.mpr ?_
  have := Real.pi_pos
  rw [neg_mul, neg_mul, neg_div]; exact neg_neg_of_pos (by positivity)

lemma decayX_anti {y y' : ℝ} (h : y ≤ y') : decayX N y' ≤ decayX N y := by
  have hMpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine Real.exp_le_exp.mpr ?_
  have := Real.pi_pos
  rw [div_le_div_iff_of_pos_right hMpos]; nlinarith

/-- The row bound $\frac{4\pi^2}{N}B\,x^{|c|}/(1-x)^2$. -/
noncomputable def rowBound (N : ℕ) (B y : ℝ) (c : ℤ) : ℝ :=
  4 * π ^ 2 / N * B * (decayX N y ^ c.natAbs / (1 - decayX N y) ^ 2)

lemma norm_rowW_le (W : ZMod N → ZMod N → ℂ) {c : ℤ} (hc : c ≠ 0) (z : ℍ) :
    ‖rowW W c z‖ ≤ rowBound N (wtBound W) z.im c :=
  norm_row_le (M := N) (β := wt W c) (fun d => wt_add_N_right W c d) (fun d => norm_wt_le W c d) hc z

lemma rowBound_anti {B y y' : ℝ} (hB : 0 ≤ B) (hy : 0 < y) (h : y ≤ y') (c : ℤ) :
    rowBound N B y' c ≤ rowBound N B y c := by
  unfold rowBound
  have h1 := decayX_anti (N := N) h
  have h0 := decayX_pos (N := N) y'
  have hl := decayX_lt_one (N := N) hy
  have hp : decayX N y' ^ c.natAbs ≤ decayX N y ^ c.natAbs := pow_le_pow_left₀ h0.le h1 _
  have hd : (1 - decayX N y) ^ 2 ≤ (1 - decayX N y') ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hMpos : (0 : ℝ) ≤ 4 * π ^ 2 / N * B := by positivity
  exact mul_le_mul_of_nonneg_left (div_le_div₀ (pow_nonneg (decayX_pos y).le _) hp (by nlinarith) hd) hMpos

lemma summable_rowBound {B y : ℝ} (hy : 0 < y) : Summable (rowBound N B y) :=
  ((summable_geom_natAbs (decayX_pos y).le (decayX_lt_one hy)).div_const _).mul_left _

/-- **$E_W$ at $i\infty$:** $E_W(z) \to \sum_d W(0,d)\,d^{-2}$ as $\operatorname{Im}z \to \infty$. -/
theorem tendsto_eis2_atImInfty (W : ZMod N → ZMod N → ℂ) :
    Tendsto (eis2 W) UpperHalfPlane.atImInfty (𝓝 (∑' d : ℤ, wt W 0 d * ((d : ℂ) ^ 2)⁻¹)) := by
  have hlim : (∑' d : ℤ, wt W 0 d * ((d : ℂ) ^ 2)⁻¹) =
      ∑' c : ℤ, (if c = 0 then ∑' d : ℤ, wt W 0 d * ((d : ℂ) ^ 2)⁻¹ else 0) := by
    rw [tsum_ite_eq]
  rw [hlim]
  have hev : ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty, 1 ≤ z.im :=
    (UpperHalfPlane.atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun c => if c = 0 then ‖rowW W 0 0‖ else rowBound N (wtBound W) 1 c)
    ?_ (fun c => ?_) ?_
  · refine ((summable_rowBound (N := N) (B := wtBound W) one_pos).update 0 ‖rowW W 0 0‖).congr
      fun c => ?_
    by_cases hc : c = 0 <;> simp [hc]
  · by_cases hc : c = 0
    · subst hc
      simp only [ite_true]
      refine tendsto_const_nhds.congr fun z => ?_
      simp
    · simp only [hc, ite_false]
      have h0 : Tendsto (fun z : ℍ => rowBound N (wtBound W) z.im c) UpperHalfPlane.atImInfty
          (𝓝 0) := by
        have hx : Tendsto (fun z : ℍ => decayX N z.im) UpperHalfPlane.atImInfty (𝓝 0) := by
          have hMpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
          refine Real.tendsto_exp_atBot.comp ?_
          have : Tendsto (fun z : ℍ => z.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
          have h2 : 0 < 2 * π / N := by have := Real.pi_pos; positivity
          refine (tendsto_neg_atTop_atBot.comp (this.const_mul_atTop h2)).congr fun z => ?_
          simp only [Function.comp_apply]; ring
        have := ((hx.pow c.natAbs).div ((tendsto_const_nhds (x := (1 : ℝ))).sub hx |>.pow 2)
          (by norm_num)).const_mul (4 * π ^ 2 / N * wtBound W)
        simpa [rowBound, zero_pow (Int.natAbs_ne_zero.mpr hc)] using this
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [hev] with z hz using norm_rowW_le W hc z
  · filter_upwards [hev] with z hz
    intro c
    by_cases hc : c = 0
    · subst hc; simp only [ite_true]; show ‖rowW W 0 z‖ ≤ _; rw [rowW_zero W _ 0]
    · simp only [hc, ite_false]
      exact (norm_rowW_le W hc z).trans
        (rowBound_anti (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          one_pos hz c)

lemma summable_vec_row_rpow (c : ℤ) :
    Summable fun d : ℤ => ‖(![c, d] : Fin 2 → ℤ)‖ ^ (-2 : ℝ) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := 2) one_lt_two) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun d hd => ?_
  by_contra h
  apply hd
  have hd0 : (0 : ℝ) < |(d : ℝ)| := abs_pos.mpr (by exact_mod_cast h)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  refine Real.rpow_le_rpow_of_nonpos hd0 ?_ (by norm_num)
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_max]
  exact le_max_of_le_right (by simp)

/-- Each row is holomorphic on a vertical strip region. -/
lemma differentiableOn_rowW (W : ZMod N → ZMod N → ℂ) (c : ℤ) {A B : ℝ} (hB : 0 < B) :
    DifferentiableOn ℂ (rowW W c) {w : ℂ | |w.re| < A ∧ B < w.im} := by
  set U := {w : ℂ | |w.re| < A ∧ B < w.im}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  set ρ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩
  refine differentiableOn_tsum_of_summable_norm
    (u := fun d => wtBound W * (ρ ^ (-2 : ℝ) * ‖(![c, d] : Fin 2 → ℤ)‖ ^ (-2 : ℝ)))
    (((summable_vec_row_rpow c).mul_left _).mul_left _) (fun d => ?_) hU (fun d w hw => ?_)
  · by_cases h : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · refine DifferentiableOn.const_mul ?_ _
      refine (((differentiableOn_const _).mul differentiableOn_id).add_const _ |>.pow 2).inv
        fun w hw => pow_ne_zero 2 ?_
      intro h0
      have him := congr_arg Complex.im h0
      simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
      rcases mul_eq_zero.mp him with h' | h'
      · have hc : c = 0 := by exact_mod_cast h'
        subst hc
        apply h; refine ⟨rfl, ?_⟩
        simpa using h0
      · linarith [hw.2]
  · have hw0 : 0 < w.im := hB.trans hw.2
    set z : ℍ := ⟨w, hw0⟩
    have hz : z ∈ UpperHalfPlane.verticalStrip A B := ⟨hw.1.le, hw.2.le⟩
    have hb := EisensteinSeries.summand_bound_of_mem_verticalStrip (k := 2) (by norm_num) ![c, d] hB hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
    rw [norm_mul]
    refine mul_le_mul (norm_wt_le W c d) ?_ (norm_nonneg _)
      ((norm_nonneg _).trans (norm_wt_le W 0 0))
    rw [norm_inv, norm_pow]
    have : ‖(c : ℂ) * (z : ℂ) + d‖ ^ (-2 : ℝ) = (‖(c : ℂ) * w + d‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg (norm_nonneg _)]; norm_cast
    rw [← this]; exact hb

/-- **$E_W$ is holomorphic on $\mathbb{H}$.** -/
theorem mdifferentiable_eis2 (W : ZMod N → ZMod N → ℂ) : MDiff (eis2 W) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z₀ hz₀
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  have hB : 0 < B := by simp only [B]; linarith [show (0 : ℝ) < z₀.im from hz₀]
  set U := {w : ℂ | |w.re| < A ∧ B < w.im}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hz₀U : z₀ ∈ U := ⟨by simp [A], by simp only [B]; linarith [show (0 : ℝ) < z₀.im from hz₀]⟩
  have hdiff : DifferentiableOn ℂ (fun w => ∑' c, rowW W c w) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => if c = 0 then ‖rowW W 0 0‖ else rowBound N (wtBound W) B c) ?_
      (fun c => differentiableOn_rowW W c hB) hU (fun c w hw => ?_)
    · refine ((summable_rowBound (N := N) (B := wtBound W) hB).update 0 ‖rowW W 0 0‖).congr
        fun c => ?_
      by_cases hc : c = 0 <;> simp [hc]
    · by_cases hc : c = 0
      · subst hc; simp only [ite_true]; rw [rowW_zero W _ 0]
      · simp only [hc, ite_false]
        have hw0 : 0 < w.im := hB.trans hw.2
        exact (norm_rowW_le W hc ⟨w, hw0⟩).trans
          (rowBound_anti (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            hB hw.2.le c)
  have heq : Set.EqOn (eis2 W ∘ UpperHalfPlane.ofComplex) (fun w => ∑' c, rowW W c w) U :=
    fun w hw => by
      have hw0 : 0 < w.im := hB.trans hw.2
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw0]
      rfl
  exact ((hdiff.congr heq).differentiableAt (hU.mem_nhds hz₀U)).differentiableWithinAt

end QuadFormsKB.Siegel.EisensteinWt2
