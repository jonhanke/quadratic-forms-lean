/-
# Formula (3) at $p = 2$: the induction over the constituents

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263; §5, Table 1; §6 (bibliography key `conwaysloane1988`).

**The recursion of (3).** Splitting off the constituent $f_1$ of scale $1$ of a 2-adic symbol $\sigma$ changes the
right-hand side of (3) by an explicit factor (`pMassTwo_succ`):
$$m_2(\sigma) = \mathrm{step}(\sigma)\cdot m_2(\sigma')\cdot\sqrt2^{\,n_1\sum_k(k+1)n_{2^{k+1}}},$$
$\sigma'$ the shifted symbol (`shiftT`), where `stepFactor σ` collects the factor of $f_{1/2}$, the diagonal factors of
$f_1$ and of $f_2$ (whose bound/free status may change), and the change of $2^{n(\mathrm{I,I}) - n(\mathrm{II})}$.

**The induction** (`pMassDensity_intMat_of_step`): if the counting 2-mass satisfies the same one-step identity
$m_2(U \perp 2B) = \mathrm{step}(\sigma)\,m_2(B)\,2^{a(b + \operatorname{ord}_2\det B)/2}$ (`StepEq`) for the
decompositions considered, then $m_2(f) = $ `pMassTwo σ N` for them. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicSymbol

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Invariance under renaming the variables -/

theorem pMassDensity_reidx {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : Reidx M N) (hN : N.det ≠ 0) : pMassDensity 2 M = pMassDensity 2 N := by
  obtain ⟨e, rfl⟩ := h
  obtain rfl : m = n := by simpa using Fintype.card_congr e
  have hZ : ZpEquiv (N.map (Int.cast : ℤ → ℚ_[2])) ((N.submatrix e e).map (Int.cast : ℤ → ℚ_[2])) := by
    rw [← Matrix.submatrix_map]; exact dyadic_zpEquiv_perm _ e
  exact pMassDensity_eq_of_zpEquiv hZ hN (by rwa [det_submatrix_equiv_self])

theorem isTwoSymbolOf_reidx {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : Reidx M N) {σ : TwoSymbol} (hM : IsTwoSymbolOf (M.map (Int.cast : ℤ → ℚ_[2])) σ) :
    IsTwoSymbolOf (N.map (Int.cast : ℤ → ℚ_[2])) σ := by
  obtain ⟨e, rfl⟩ := h
  obtain rfl : m = n := by simpa using Fintype.card_congr e
  obtain ⟨D, hv, he, hd, hZ, hs⟩ := hM
  refine ⟨D, hv, he, hd, ?_, hs⟩
  refine ZpEquiv.trans ?_ hZ
  rw [← Matrix.submatrix_map]; exact dyadic_zpEquiv_perm _ e

/-! ### The recursion of the right-hand side -/

theorem lowerProd_pos (m : ℕ) : 0 < lowerProd 2 m := by
  unfold lowerProd
  refine Finset.prod_pos fun i _ => ?_
  have h : (1 : ℚ) < 2 ^ (2 * (i + 1)) := one_lt_pow₀ (by norm_num) (by omega)
  push_cast
  rw [sub_pos]
  exact inv_lt_one_of_one_lt₀ h

theorem diagFactor_pos (s : Species) : 0 < s.diagFactor 2 := by
  unfold Species.diagFactor
  split_ifs with h1 h2
  · exact one_pos
  · exact inv_pos.mpr (mul_pos two_pos (lowerProd_pos _))
  · refine inv_pos.mpr (mul_pos (mul_pos two_pos (lowerProd_pos _)) ?_)
    have hk : 1 ≤ s.dim / 2 := by
      rcases Nat.even_or_odd s.dim with ⟨k, hk⟩ | h
      · omega
      · exact absurd h h2
    have h2 : ((2 : ℕ) : ℚ) ^ (s.dim / 2) ≥ 2 := by
      calc ((2 : ℕ) : ℚ) ^ (s.dim / 2) ≥ ((2 : ℕ) : ℚ) ^ 1 := pow_le_pow_right₀ (by norm_num) hk
        _ = 2 := by norm_num
    have hs : (s.sign.toInt : ℚ) ≤ 1 := by cases s.sign <;> simp [Sign.toInt]
    have hi : 0 < (((2 : ℕ) : ℚ) ^ (s.dim / 2))⁻¹ := by positivity
    have hi2 : (((2 : ℕ) : ℚ) ^ (s.dim / 2))⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    nlinarith

/-- The diagonal factor $M_2$ of the constituent $k$ of $\sigma$ (species from Table 1 with its bound/free status). -/
def mFac (σ : TwoSymbol) (k : ℕ) : ℚ := (twoSpecies (σ k) (IsBound σ k)).diagFactor 2

theorem halfFactor_pos (σ : TwoSymbol) : 0 < halfFactor σ := by
  unfold halfFactor; split_ifs <;> norm_num

/-- **The step factor** of (3) at $p = 2$: the ratio of the right-hand sides of (3) for $\sigma$ and the shifted
symbol $\sigma'$, apart from the cross term:
$\frac{h(\sigma)\,M_2(f_1)\,M_2(f_2)}{h(\sigma')\,M_2'(f_2)}\cdot 2^{[f_1, f_2 \text{ type I}] - [f_1 \text{ type II}]\,n_1}$,
$h$ the factor of the zero-dimensional constituent $f_{1/2}$ (`halfFactor`) and $M_2'(f_2)$ the diagonal factor of $f_2$
with its bound/free status in $\sigma'$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (one step of (3), p = 2)"]
noncomputable def stepFactor (σ : TwoSymbol) : ℝ :=
  ((halfFactor σ * mFac σ 0 * mFac σ 1 / (halfFactor (shiftT σ) * mFac (shiftT σ) 0) : ℚ) : ℝ) *
    (2 : ℝ) ^ ((if (σ 0).type = .I ∧ (σ 1).type = .I then 1 else 0 : ℤ) -
      (if (σ 0).type = .II then ((σ 0).dim : ℤ) else 0))

theorem mFac_shift (σ : TwoSymbol) (k : ℕ) : mFac (shiftT σ) (k + 1) = mFac σ (k + 2) := by
  unfold mFac
  congr 1
  refine twoSpecies_congr ?_ rfl rfl rfl
  simp only [IsBound, shiftT]
  constructor <;> rintro (⟨-, h⟩ | h) <;> first | exact Or.inl ⟨by omega, h⟩ | exact Or.inr h

/-- **The recursion of (3) at $p = 2$.** -/
@[kb "conwaysloane1988" "(3), p. 263 (recursion over the constituents, p = 2)"]
theorem pMassTwo_succ (σ : TwoSymbol) (N : ℕ) :
    pMassTwo σ (N + 1) = stepFactor σ * pMassTwo (shiftT σ) N *
      Real.sqrt 2 ^ ((σ 0).dim * ∑ k ∈ Finset.range N, (k + 1) * (σ (k + 1)).dim) := by
  have hD : diagProdTwo σ (N + 1) =
      (halfFactor σ * mFac σ 0 * mFac σ 1 / (halfFactor (shiftT σ) * mFac (shiftT σ) 0)) *
        diagProdTwo (shiftT σ) N := by
    unfold diagProdTwo
    rw [Finset.prod_range_succ', Finset.prod_range_succ', Finset.prod_range_succ' _ N]
    have hP : ∏ k ∈ Finset.range N, (twoSpecies (σ (k + 1 + 1)) (IsBound σ (k + 1 + 1))).diagFactor 2 =
        ∏ k ∈ Finset.range N, (twoSpecies (shiftT σ (k + 1)) (IsBound (shiftT σ) (k + 1))).diagFactor 2 :=
      Finset.prod_congr rfl fun k _ => (mFac_shift σ k).symm
    rw [hP]
    have h1 := (halfFactor_pos (shiftT σ)).ne'
    have h2 := (diagFactor_pos (twoSpecies (shiftT σ 0) (IsBound (shiftT σ) 0))).ne'
    unfold mFac
    field_simp
  have hII' : (nII' σ (N + 1) : ℤ) = (if (σ 0).type = .I ∧ (σ 1).type = .I then 1 else 0) + nII' (shiftT σ) N := by
    unfold nII'
    rw [Finset.sum_range_succ']
    push_cast
    rw [add_comm]
    rfl
  have hII : (nII σ (N + 1) : ℤ) = (if (σ 0).type = .II then ((σ 0).dim : ℤ) else 0) + nII (shiftT σ) N := by
    unfold nII
    rw [Finset.sum_range_succ']
    push_cast
    rw [add_comm]
    rfl
  unfold pMassTwo stepFactor
  rw [hD, crossExp_succ, hII', hII, pow_add]
  push_cast
  have e : ((if (σ 0).type = .I ∧ (σ 1).type = .I then 1 else 0 : ℤ) + nII' (shiftT σ) N -
      ((if (σ 0).type = .II then ((σ 0).dim : ℤ) else 0) + nII (shiftT σ) N)) =
      ((if (σ 0).type = .I ∧ (σ 1).type = .I then 1 else 0 : ℤ) -
        (if (σ 0).type = .II then ((σ 0).dim : ℤ) else 0)) + (nII' (shiftT σ) N - nII (shiftT σ) N) := by ring
  rw [e, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [shiftT]
  ring

/-! ### The induction -/

/-- The one-step identity for a decomposition $D$: $m_2(U \perp 2B) = \mathrm{step}(\sigma)\,m_2(B)\,
2^{a(b + \operatorname{ord}_2\det B)/2}$ with $U$, $B$ the models of `low D`, `high D` and $\sigma$ the symbol of $D$. -/
def StepEq (D : List DyBlock) : Prop :=
  pMassDensity 2 (blk 2 (intMat (low D)) (intMat (high D))) = stepFactor (blockSymbol D) *
    pMassDensity 2 (intMat (high D)) *
      (2 : ℝ) ^ ((((dyDim (high D) + padicValInt 2 (intMat (high D)).det : ℕ) : ℝ) * dyDim (low D)) / 2)

theorem valid_high {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) : ∀ b ∈ high D, b.Valid := by
  intro b hb
  simp only [high, List.mem_map, List.mem_filter] at hb
  obtain ⟨c, ⟨hc, -⟩, rfl⟩ := hb
  have := hv c hc
  cases c <;> exact this

theorem exp_high {D : List DyBlock} {N : ℕ} (he : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N + 1) :
    ∀ b ∈ high D, 0 ≤ blockExp b ∧ blockExp b < N := by
  intro b hb
  simp only [high, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hb
  obtain ⟨c, ⟨hc, hc0⟩, rfl⟩ := hb
  have := he c hc
  rw [blockExp_lowerB]
  omega

theorem exp_low {D : List DyBlock} : ∀ b ∈ low D, blockExp b = 0 := by
  intro b hb
  simp only [low, List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2

theorem valid_low {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) : ∀ b ∈ low D, b.Valid := fun b hb =>
  hv b (List.mem_filter.mp hb).1

theorem pMassTwo_nil (N : ℕ) : pMassTwo (blockSymbol []) N = 1 := by
  have ht : ∀ k, blockSymbol [] k = TwoFactor.trivial := fun k => rfl
  rw [pMassTwo_congr (N := 0) (fun k _ => ht k) (Nat.zero_le N)]
  unfold pMassTwo diagProdTwo halfFactor nII nII' crossExp
  simp only [ht, Finset.range_zero, Finset.sum_empty, Finset.prod_range_one, zero_add]
  rw [twoSpecies_trivial_free (by simp [IsBound, ht, TwoFactor.trivial])]
  simp [TwoFactor.trivial, Species.diagFactor, Species.plus]

/-- **The induction over the constituents** (Conway–Sloane 1988, (3), p = 2): for a class $P$ of decompositions closed
under `high`, the one-step identity for the members of $P$ gives $m_2 = $ `pMassTwo` for them. -/
@[kb "conwaysloane1988" "(3), p. 263 (induction over the constituents, p = 2)"]
theorem pMassDensity_intMat_of_step (P : List DyBlock → Prop) (hP : ∀ D, P D → P (high D))
    (hstep : ∀ D, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) → P D → StepEq D) :
    ∀ (N : ℕ) (D : List DyBlock), (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) → P D →
      pMassDensity 2 (intMat D) = pMassTwo (blockSymbol D) N := by
  intro N
  induction N with
  | zero =>
    intro D _ he _
    obtain rfl : D = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb => by
      have := he b hb; omega
    rw [pMassTwo_nil]
    exact pMassDensity_fin_zero _
  | succ N ih =>
    intro D hv he hPD
    have he0 : ∀ b ∈ D, 0 ≤ blockExp b := fun b hb => (he b hb).1
    have hvh := valid_high hv
    have heh := exp_high he
    have hB := ih (high D) hvh heh (hP D hPD)
    rw [blockSymbol_high] at hB
    have hdet : (blk 2 (intMat (low D)) (intMat (high D))).det ≠ 0 := by
      rw [blk_det]
      exact mul_ne_zero (det_intMat_ne _ (valid_low hv))
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (det_intMat_ne _ hvh))
    rw [pMassDensity_reidx (reidx_split D he0) hdet, hstep D hv he0 hPD, hB, pMassTwo_succ,
      show Real.sqrt 2 = Real.sqrt ((2 : ℕ) : ℝ) by norm_num, sqrt_pow_eq_rpow]
    congr 2
    -- the exponents: `a = n₁` and `b + ord₂ det B = Σ (k+1) n_{k+1}`
    have ha : dyDim (low D) = (blockSymbol D 0).dim := by
      rw [← blockSymbol_low_zero D, dyDim_eq_sum]
      have := sum_levels (fun _ => 1) 1 (low D) fun b hb => by rw [exp_low b hb]; omega
      simp only [Finset.sum_range_one, one_mul] at this
      rw [this]
    have hb : dyDim (high D) + padicValInt 2 (intMat (high D)).det =
        ∑ k ∈ Finset.range N, (k + 1) * (blockSymbol D (k + 1)).dim := by
      rw [padicValInt_det_intMat _ hvh, dyDim_eq_sum]
      have := sum_levels (fun k => k + 1) N (high D) heh
      rw [blockSymbol_high] at this
      simp only [shiftT] at this
      rw [this, ← List.sum_map_add]
      congr 1
      refine List.map_congr_left fun b _ => ?_
      simp only [bVal]; ring
    rw [ha, hb]
    push_cast
    ring_nf

end QuadFormsKB.ConwaySloane.Mass.Two
