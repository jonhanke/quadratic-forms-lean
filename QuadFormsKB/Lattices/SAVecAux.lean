/-
# Auxiliary local facts for O'Meara 104:3

Small local lemmas used in the assembly of the anisotropic case of 104:3 (`Lattices/SAVectorsAnisotropic.lean`):
squares near $1$ in a complete normed field, real places ($x$ or $-x$ is a square), bounds on local vectors, the
local choice of $\beta$ at the primes of $T$ (step 4, item 4 of O'Meara's proof), and integrality of $B(x, y)$ on
$\mathfrak o_\mathfrak p^n$ at a good prime.
-/
import QuadFormsKB.Lattices.SAPerpCoords
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Lattices.SAVSA

open NumberField IsDedekindDomain Matrix Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **Squares near $1$** in a complete normed field with $2 \ne 0$ (contraction mapping). -/
theorem isSquare_of_norm_sub_one_lt {K : Type*} [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) {u : K}
    (hu : ‖u - 1‖ < ‖(2 : K)‖ ^ 2 / 8) : IsSquare u := by
  have hn : 0 < ‖(2:K)‖ := norm_pos_iff.mpr h2
  set nn := ‖(2:K)‖ with hn_def
  set c := u - 1
  let f : K → K := fun y => (c - y ^ 2) / 2
  let s := Metric.closedBall (0:K) (nn / 4)
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div]
    rw [div_le_iff₀ hn]
    calc ‖c - y ^ 2‖ ≤ ‖c‖ + ‖y‖ ^ 2 := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_pow]
      _ ≤ nn ^ 2 / 8 + (nn / 4) ^ 2 := by gcongr
      _ ≤ nn / 4 * nn := by nlinarith
  have hcon : ContractingWith (1/2 : NNReal) (hmaps.restrict f s s) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ ((1/2 : NNReal) : ℝ) * dist (y:K) y'
    simp only [dist_eq_norm, f]
    have : (c - (y:K) ^ 2) / 2 - (c - (y':K) ^ 2) / 2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, div_le_iff₀ hn]
    have : ‖(y:K) + y'‖ ≤ nn / 2 := (norm_add_le _ _).trans (by linarith)
    push_cast
    calc ‖(y:K) - y'‖ * ‖(y:K) + y'‖ ≤ ‖(y:K) - y'‖ * (nn / 2) := by gcongr
      _ = 1/2 * ‖(y:K) - ↑y'‖ * nn := by ring
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s]; positivity) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = c - y ^ 2 := by
    have h3 : (2:K) * ((c - y ^ 2) / 2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2] at h3
    exact h3.symm
  simp only [c] at h2'
  linear_combination -h2'

theorem norm_algebraMap_completion (w : InfinitePlace F) (k : F) : ‖algebraMap F w.Completion k‖ = w k := by
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.norm_coe (K := F) (v := w) (WithAbs.toAbs w.1 k)

/-- At an infinite place, $1 - x$ is a square when $w(x) < 1/2$. -/
theorem isSquare_one_sub_of_lt (w : InfinitePlace F) {x : F} (hx : w x < 1 / 2) :
    IsSquare (algebraMap F w.Completion (1 - x)) := by
  have h2 : (2 : w.Completion) ≠ 0 := by
    have := (algebraMap F w.Completion).injective.ne (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  refine isSquare_of_norm_sub_one_lt h2 ?_
  have hn2 : ‖(2 : w.Completion)‖ = 2 := by
    rw [show (2 : w.Completion) = algebraMap F w.Completion 2 by rw [map_ofNat], norm_algebraMap_completion]
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [hn2, map_sub, map_one, sub_sub_cancel_left, norm_neg, norm_algebraMap_completion]
  linarith

/-- At a real place every element or its negative is a square. -/
theorem isSquare_or_isSquare_neg (w : InfinitePlace F) (hw : w.IsReal) (x : w.Completion) :
    IsSquare x ∨ IsSquare (-x) := by
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rcases le_total 0 (ψ x) with h | h
  · left
    refine ⟨ψ.symm (Real.sqrt (ψ x)), ψ.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt h]
  · right
    refine ⟨ψ.symm (Real.sqrt (-ψ x)), ψ.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt (by linarith), map_neg]

/-- At a complex place every element is a square. -/
theorem isSquare_of_isComplex (w : InfinitePlace F) (hw : w.IsComplex) (x : w.Completion) : IsSquare x := by
  let ψ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (ψ x)
  exact ⟨ψ.symm z, ψ.injective (by rw [hz, map_mul, RingEquiv.apply_symm_apply])⟩

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- Every local vector lies in some ball $\mathfrak p^{-s}\mathfrak o_\mathfrak p^n$. -/
theorem exists_mem_ball_neg {n : ℕ} (x : Fin n → Fv) : ∃ s : ℤ, 0 ≤ s ∧ x ∈ ball v (-s) := by
  choose k hk using fun i => exists_valued_le v (x i)
  refine ⟨∑ i, (k i : ℤ), Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, fun i => ?_⟩
  rw [neg_neg]
  refine (hk i).trans (exp_le_exp.mpr ?_)
  exact Finset.single_le_sum (f := fun i => (k i : ℤ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)

/-- **The local choice of $\beta$ on $T$** (O'Meara 104:3, step 4, item 4): if $v(\lambda - 1) < 1$, $a \ne 0$, $d \ne 0$ and
$v(d/a) \le e^{-2m_0}$, $v(d/a) < v(4)$, there is $\beta_\mathfrak p$ with a neighbourhood $B$ on which
$v(\lambda\beta - 1) \le e^{-m_0}$ and $a(1 - \lambda^2\beta^2) \in d\,F_\mathfrak p^{\times 2}$. -/
theorem exists_beta_local {lam a d : Fv} (hlam : Valued.v (lam - 1) < 1) (ha : a ≠ 0) (hd : d ≠ 0) (m₀ : ℤ)
    (hda : Valued.v (d / a) ≤ exp (-(2 * m₀))) (hda4 : Valued.v (d / a) < Valued.v (4 : Fv)) :
    ∃ β₀ : Fv, ∃ B ∈ 𝓝 β₀, ∀ β ∈ B, Valued.v (lam * β - 1) ≤ exp (-m₀) ∧
      a * (1 - lam ^ 2 * β ^ 2) ≠ 0 ∧ IsSquare (a * (1 - lam ^ 2 * β ^ 2) / d) ∧
      Valued.v (a * (1 - lam ^ 2 * β ^ 2) / d) = 1 := by
  have hlam1 : Valued.v lam = 1 := by
    have : Valued.v (lam - 1) < Valued.v (1 : Fv) := by rwa [map_one]
    rw [Valuation.map_eq_of_sub_lt _ this, map_one]
  have hlam0 : lam ≠ 0 := fun h => by rw [h, map_zero] at hlam1; exact zero_ne_one hlam1
  set t := d / a
  have ht0 : t ≠ 0 := div_ne_zero hd ha
  obtain ⟨s, hs⟩ := HN.isSquare_of_valued_sub_one_lt v (1 - t) (by rw [sub_sub_cancel_left, Valuation.map_neg]; exact hda4)
  -- choose the root close to `1`
  obtain ⟨ρ, hρ, hρm⟩ : ∃ ρ : Fv, ρ * ρ = 1 - t ∧ Valued.v (ρ - 1) ≤ exp (-m₀) := by
    have hprod : (s - 1) * (s + 1) = -t := by linear_combination hs.symm
    by_cases h1 : Valued.v (s - 1) ≤ exp (-m₀)
    · exact ⟨s, hs.symm, h1⟩
    · refine ⟨-s, by rw [neg_mul_neg]; exact hs.symm, ?_⟩
      rw [show -s - 1 = -(s + 1) by ring, Valuation.map_neg]
      by_contra h2
      push Not at h1 h2
      have hne1 : s - 1 ≠ 0 := fun h => by rw [h, map_zero] at h1; exact not_lt_zero h1
      have hne2 : s + 1 ≠ 0 := fun h => by rw [h, map_zero] at h2; exact not_lt_zero h2
      obtain ⟨a1, ha1⟩ := exists_valued_eq_exp v hne1
      obtain ⟨a2, ha2⟩ := exists_valued_eq_exp v hne2
      rw [ha1, exp_lt_exp] at h1
      rw [ha2, exp_lt_exp] at h2
      have h3 := congrArg Valued.v hprod
      rw [map_mul, ha1, ha2, ← exp_add, Valuation.map_neg] at h3
      rw [← h3, exp_le_exp] at hda
      omega
  set β₀ := ρ / lam
  have hc₀ : a * (1 - lam ^ 2 * β₀ ^ 2) = d := by
    have hb : lam ^ 2 * β₀ ^ 2 = ρ * ρ := by simp only [β₀]; field_simp
    rw [hb, hρ]; simp only [t]; field_simp; ring
  have h4 : Valued.v (4 : Fv) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    have := (algebraMap F Fv).injective.ne (by norm_num : (4 : F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  obtain ⟨k4, hk4⟩ := exists_valued_eq_exp v ((Valuation.ne_zero_iff _).mp h4)
  have hc1 : Continuous fun β : Fv => lam * β - 1 := (continuous_const.mul continuous_id).sub continuous_const
  have hc2 : Continuous fun β : Fv => a * (1 - lam ^ 2 * β ^ 2) / d - 1 :=
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul (continuous_id.pow 2)))).div_const _).sub
      continuous_const
  have hB1 : {β : Fv | Valued.v (lam * β - 1) ≤ exp (-m₀)} ∈ 𝓝 β₀ := by
    have h := valued_le_mem_nhds v (lam * β₀) m₀
    have hcont : Continuous fun β : Fv => lam * β := continuous_const.mul continuous_id
    have := hcont.continuousAt (x := β₀) |>.preimage_mem_nhds h
    refine Filter.mem_of_superset this fun β hβ => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hβ ⊢
    have e : lam * β - 1 = (lam * β - lam * β₀) + (ρ - 1) := by simp only [β₀]; field_simp; ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hβ hρm)
  have hB2 : {β : Fv | Valued.v (a * (1 - lam ^ 2 * β ^ 2) / d - 1) < Valued.v (4 : Fv)} ∈ 𝓝 β₀ := by
    have hN := valued_lt_mem_nhds_zero v (-k4)
    rw [neg_neg, ← hk4] at hN
    have hN' : {u : Fv | Valued.v u < Valued.v (4 : Fv)} ∈
        𝓝 (a * (1 - lam ^ 2 * β₀ ^ 2) / d - 1) := by rw [hc₀, div_self hd, sub_self]; exact hN
    exact hc2.continuousAt.preimage_mem_nhds hN'
  have h41 : Valued.v (4 : Fv) ≤ 1 := by
    have := valued_int_le_one v (4 : 𝓞 F); rwa [map_ofNat] at this
  refine ⟨β₀, _, Filter.inter_mem hB1 hB2, fun β ⟨h1, h2⟩ => ⟨h1, ?_, ?_, ?_⟩⟩
  · intro h0
    simp only [Set.mem_ofPred_eq, h0, zero_div, zero_sub, Valuation.map_neg, map_one] at h2
    exact absurd (h2.trans_le h41) (lt_irrefl _)
  · exact HN.isSquare_of_valued_sub_one_lt v _ h2
  · have : Valued.v (a * (1 - lam ^ 2 * β ^ 2) / d - 1) < Valued.v (1 : Fv) := by
      rw [map_one]; exact h2.trans_le h41
    rw [Valuation.map_eq_of_sub_lt _ this, map_one]

end Local

end QuadFormsKB.Lattices
