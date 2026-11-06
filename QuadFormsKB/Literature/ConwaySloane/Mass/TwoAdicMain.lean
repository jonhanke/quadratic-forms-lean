/-
# Formula (3) at $p = 2$: assembly, and the remaining named input

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Tables 1–2, p. 264, §5–6, pp. 265–266 (bibliography key `conwaysloane1988`).

Formula (3) at $p = 2$ is proved by induction over the Jordan constituents (`pMassDensity_intMat_of_step`): splitting
off the constituent $f_1$ of scale $1$ of a block model $U \perp 2B$ must change the counting 2-mass $m_2$ of §12 by the
factor by which it changes the right-hand side of (3) (`StepEq`, `pMassTwo_succ`).

**Proved here.**
* `stepEq_typeII`: the one-step identity when $f_1$ and $f_2$ both have type II, from
  $\alpha_2(U \perp 2B) = \alpha_2(U)\alpha_2(2B)$ (`pMassDensity_blk_two`) and the value of $m_2$ on an even unimodular
  form (passed as the hypothesis `TypeIIBase`, proved in `TwoAdicBase.lean`).
* `pMassFormulaTwo_of_step`: the named input `PMassStepTwoTypeI` below (the one-step identity when $f_1$ or $f_2$ has
  type I) and `TypeIIBase` give `PMassFormulaTwo`, formula (3) at $p = 2$ for every form.
* `pMassDensity_eq_pMassTwo_of_typeII`: formula (3) at $p = 2$ for every form all of whose 2-adic Jordan constituents
  have type II, from `TypeIIBase` alone.

**Named input.** `PMassStepTwoTypeI`: the one-step identity `StepEq D` for the block decompositions $D$ whose constituent
$f_1$ or $f_2$ has type I. In that case the perturbed forms $U + 2W^{\mathsf T}BW$ and $B + 2BWU^{-1}W^{\mathsf T}B$ of
the block count identity (`card_fromBlocks_eq_sum`) need not be equivalent to $U$ and $B$, and the proportion of $W$ for
which they are is the correction that Conway–Sloane's bound/free rule, the factor $\frac12$ of $f_{1/2}$ and the factor
$2^{n(\mathrm{I,I})}$ encode. The paper does not prove (3) at $p = 2$ ("derived by translation and simplification of
Watson's formula", §3, p. 262). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicStep
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicDensity
import QuadFormsKB.Literature.ConwaySloane.Mass.Formula

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Symmetry of the block models -/

theorem isSymm_bInt (b : DyBlock) : (bInt b).IsSymm := by
  cases b with
  | sq e u => ext i j; fin_cases i; fin_cases j; rfl
  | hyp e =>
    show ((2 ^ e.toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ))ᵀ = (2 ^ e.toNat : ℤ) • !![0, 1; 1, 0]
    rw [transpose_smul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> rfl
  | ell e =>
    show ((2 ^ e.toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ))ᵀ = (2 ^ e.toNat : ℤ) • !![2, 1; 1, 2]
    rw [transpose_smul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem isSymm_orthSumMat {a b : ℕ} {F : Matrix (Fin a) (Fin a) ℤ} {G : Matrix (Fin b) (Fin b) ℤ} (hF : F.IsSymm)
    (hG : G.IsSymm) : (orthSumMat F G).IsSymm := by
  unfold Matrix.IsSymm
  rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix, fromBlocks_transpose, hF.eq, hG.eq]
  simp

theorem isSymm_intMat : ∀ D : List DyBlock, (intMat D).IsSymm
  | [] => by unfold intMat; exact Matrix.isSymm_zero
  | b :: D => isSymm_orthSumMat (isSymm_bInt b) (isSymm_intMat D)

/-! ### The case $f_1$, $f_2$ of type II -/

/-- **The value of $m_2$ on an even unimodular form** (Conway–Sloane 1988, (3) and Table 1 for a single free type II
constituent): for a list $D$ of blocks $2xy$ and $2x^2 + 2xy + 2y^2$ of exponent $0$,
$m_2(D) = M_2(f_1)\,2^{-n}$, the diagonal factor of the species of Table 1 (free) times the factor $2^{-n(\mathrm{II})}$
of (3). Proved in `TwoAdicBase.lean`; stated here as the hypothesis of the assembly. -/
def TypeIIBase : Prop :=
  ∀ D : List DyBlock, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, blockExp b = 0) → (∀ b ∈ D, ¬ IsSqBlock b) →
    pMassDensity 2 (intMat D) = (mFac (blockSymbol D) 0 : ℝ) * (2 : ℝ) ^ (-(dyDim D : ℤ))

theorem dyDim_low (D : List DyBlock) : dyDim (low D) = (blockSymbol D 0).dim := by
  rw [← blockSymbol_low_zero D, dyDim_eq_sum]
  have := sum_levels (fun _ => 1) 1 (low D) fun b hb => by rw [exp_low b hb]; omega
  simp only [Finset.sum_range_one, one_mul] at this
  rw [this]

theorem not_sq_of_typeII {D : List DyBlock} (h : (blockSymbol D 0).type = .II) :
    ∀ b ∈ low D, ¬ IsSqBlock b := by
  intro b hb hsq
  have h' := h
  unfold blockSymbol at h'
  simp only at h'
  have : (D.filter fun b => blockExp b = ((0 : ℕ) : ℤ)).any (fun b => decide (IsSqBlock b)) = true := by
    rw [List.any_eq_true]
    refine ⟨b, ?_, by simpa using hsq⟩
    simp only [low, List.mem_filter, decide_eq_true_eq] at hb
    exact List.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩
  rw [this] at h'
  exact absurd h' (by decide)

theorem mFac_low (D : List DyBlock) (h1 : (blockSymbol D 1).type = .II) :
    mFac (blockSymbol (low D)) 0 = mFac (blockSymbol D) 0 := by
  unfold mFac
  rw [blockSymbol_low_zero]
  congr 1
  refine twoSpecies_congr ?_ rfl rfl rfl
  simp only [IsBound, blockSymbol_low_pos D one_ne_zero, TwoFactor.trivial, h1, ne_eq, not_true_eq_false,
    false_and, false_or, zero_add]

theorem mFac_shift_zero (σ : TwoSymbol) (h0 : (σ 0).type = .II) : mFac (shiftT σ) 0 = mFac σ 1 := by
  unfold mFac
  congr 1
  refine twoSpecies_congr ?_ rfl rfl rfl
  simp [IsBound, shiftT, h0]

theorem det_low_odd (D : List DyBlock) (hv : ∀ b ∈ D, b.Valid) : ¬ 2 ∣ (intMat (low D)).det := by
  obtain ⟨u, hu, h⟩ := det_intMat (low D) (valid_low hv)
  have h0 : ((low D).map bVal).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simp [bVal, exp_low b hb]
  rw [h, h0, pow_zero, one_mul]
  exact hu

/-- **The one-step identity when $f_1$ and $f_2$ have type II** (Conway–Sloane 1988, (3), p. 263, $p = 2$). -/
@[kb "conwaysloane1988" "(3), p. 263 (one step of the induction, p = 2, f_1 and f_2 of type II)"]
theorem stepEq_typeII (hbase : TypeIIBase) {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) (he : ∀ b ∈ D, 0 ≤ blockExp b)
    (h0 : (blockSymbol D 0).type = .II) (h1 : (blockSymbol D 1).type = .II) : StepEq D := by
  set σ := blockSymbol D with hσ
  have hvl := valid_low hv
  have hvh := valid_high hv
  have heh : ∀ b ∈ high D, 0 ≤ blockExp b := by
    intro b hb
    simp only [high, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    obtain ⟨c, ⟨hc, hc0⟩, rfl⟩ := hb
    rw [blockExp_lowerB]
    have := he c hc
    omega
  have hUe : EvenDiag (intMat (low D)) :=
    evenDiag_intMat_of_typeII (low D) (fun b hb => by rw [exp_low b hb]) (by rw [blockSymbol_low_zero]; exact h0)
  have hBe : EvenDiag (intMat (high D)) :=
    evenDiag_intMat_of_typeII (high D) heh (by rw [blockSymbol_high]; exact h1)
  unfold StepEq
  rw [pMassDensity_blk_two (isSymm_intMat _) hUe (det_low_odd D hv) (isSymm_intMat _) hBe (det_intMat_ne _ hvh),
    hbase (low D) hvl exp_low (not_sq_of_typeII h0), mFac_low D h1]
  have hstep : (mFac σ 0 : ℝ) * (2 : ℝ) ^ (-(dyDim (low D) : ℤ)) = stepFactor σ := by
    unfold stepFactor halfFactor
    rw [mFac_shift_zero σ h0, dyDim_low, ← hσ]
    have hs1 : (shiftT σ 0).type = .II := h1
    simp only [h0, hs1, ite_true, show ¬ (ScaledType.II = ScaledType.I) by decide, ite_false, false_and, zero_sub]
    have hpos := (diagFactor_pos (twoSpecies (σ 1) (IsBound σ 1))).ne'
    unfold mFac at hpos ⊢
    push_cast
    field_simp
  rw [hstep]

/-! ### The named input: the steps with a constituent of type I -/

/-- **Input: one step of formula (3) at $p = 2$ next to a type I constituent** (Conway–Sloane 1988, (3), p. 263,
Table 1, p. 264, §6, p. 266; not proved in the paper, which derives (3) at $p = 2$ "by translation and simplification of
Watson's formula", §3, p. 262). For every decomposition $D$ into blocks $2^e u x^2$, $2^e\cdot2xy$,
$2^e(2x^2+2xy+2y^2)$ of nonnegative exponents whose constituent $f_1$ (scale $1$) or $f_2$ (scale $2$) has type I, the
counting 2-mass of $U \perp 2B$ ($U$ the blocks of exponent $0$, $B$ the others with the exponent lowered by one)
satisfies
$$m_2(U \perp 2B) = \mathrm{step}(\sigma)\, m_2(B)\, 2^{a(b + \operatorname{ord}_2\det B)/2},$$
$a = \dim U$, $b = \dim B$, $\mathrm{step}(\sigma)$ the ratio of the right-hand sides of (3) (`stepFactor`).
It is a statement about one Jordan splitting of a single 2-adic lattice, not about masses.
Field:
- `step`: `StepEq D` for every such $D$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (one step at p = 2 next to type I; not proved in the paper)"]
structure PMassStepTwoTypeI : Prop where
  step : ∀ D : List DyBlock, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) →
    ((blockSymbol D 0).type = .I ∨ (blockSymbol D 1).type = .I) → StepEq D

/-! ### Assembly -/

theorem exp_lt_of_supported {D : List DyBlock} {N : ℕ} (he : ∀ b ∈ D, 0 ≤ blockExp b)
    (hN : (blockSymbol D).SupportedBelow N) : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N := by
  intro b hb
  refine ⟨he b hb, ?_⟩
  by_contra hlt
  push Not at hlt
  set k := (blockExp b).toNat
  have hk : blockExp b = k := by have := he b hb; omega
  have hd := congrArg TwoFactor.dim (hN k (by omega))
  simp only [blockSymbol, TwoFactor.trivial] at hd
  have hmem : b ∈ D.filter fun c => blockExp c = (k : ℤ) := List.mem_filter.mpr ⟨hb, by simpa using hk⟩
  have hpos : 0 < b.dim := by cases b <;> simp [DyBlock.dim]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := DyBlock.dim) hmem)
  omega

/-- Formula (3) at $p = 2$ for the block model of a decomposition, for a class of decompositions closed under `high`
on which the one-step identity holds. -/
theorem pMassDensity_intMat_eq (P : List DyBlock → Prop) (hP : ∀ D, P D → P (high D))
    (hstep : ∀ D, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) → P D → StepEq D)
    {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) (he : ∀ b ∈ D, 0 ≤ blockExp b) (hPD : P D) {N : ℕ}
    (hN : (blockSymbol D).SupportedBelow N) : pMassDensity 2 (intMat D) = pMassTwo (blockSymbol D) N :=
  pMassDensity_intMat_of_step P hP hstep N D hv (exp_lt_of_supported he hN) hPD

/-- From a 2-adic symbol of $A$ to the block model: $m_2(A) = m_2(\text{model})$. -/
theorem pMassDensity_eq_intMat {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hdet : A.det ≠ 0) {σ : TwoSymbol}
    (hσ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) σ) :
    ∃ D : List DyBlock, (∀ b ∈ D, b.Valid) ∧ (∀ b ∈ D, 0 ≤ blockExp b) ∧ σ = blockSymbol D ∧
      pMassDensity 2 A = pMassDensity 2 (intMat D) := by
  obtain ⟨D, hv, he, hn, hZ, rfl⟩ := hσ
  refine ⟨D, hv, he, rfl, ?_⟩
  subst hn
  have hs : (dyMat D).submatrix (Fin.cast rfl) (Fin.cast rfl) = dyMat D := by ext; simp
  rw [hs, ← intMat_map D he] at hZ
  exact (pMassDensity_eq_of_zpEquiv hZ hdet (det_intMat_ne D hv)).symm

/-- **Formula (3) at $p = 2$ from the named input** (Conway–Sloane 1988, (3), p. 263, Tables 1–2, §6): the one-step
identity next to type I constituents (`PMassStepTwoTypeI`) and the even unimodular value (`TypeIIBase`) give
`PMassFormulaTwo`. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); Tables 1–2, p. 264; §6, p. 266"]
theorem pMassFormulaTwo_of_step (I : PMassStepTwoTypeI) (hbase : TypeIIBase) : PMassFormulaTwo := by
  refine ⟨fun {n} A _ hdet σ N hσ hN => ?_⟩
  obtain ⟨D, hv, he, rfl, hm⟩ := pMassDensity_eq_intMat hdet hσ
  rw [hm]
  refine pMassDensity_intMat_eq (fun _ => True) (fun _ _ => trivial) (fun D hv he _ => ?_) hv he trivial hN
  by_cases h : (blockSymbol D 0).type = .I ∨ (blockSymbol D 1).type = .I
  · exact I.step D hv he h
  · push Not at h
    have h0 : (blockSymbol D 0).type = .II := by cases h' : (blockSymbol D 0).type <;> simp_all
    have h1 : (blockSymbol D 1).type = .II := by cases h' : (blockSymbol D 1).type <;> simp_all
    exact stepEq_typeII hbase hv he h0 h1

/-- **Formula (3) at $p = 2$ when every Jordan constituent has type II** (Conway–Sloane 1988, (3), p. 263): if the
2-adic symbol $\sigma$ of $A$ has only type II constituents, $m_2(A) = $ `pMassTwo σ N`. Needs only `TypeIIBase`. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2, all constituents of type II)"]
theorem pMassDensity_eq_pMassTwo_of_typeII (hbase : TypeIIBase) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (σ : TwoSymbol) (N : ℕ) (hσ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) σ)
    (hN : σ.SupportedBelow N) (hII : ∀ k, (σ k).type = .II) : pMassDensity 2 A = pMassTwo σ N := by
  obtain ⟨D, hv, he, rfl, hm⟩ := pMassDensity_eq_intMat hdet hσ
  rw [hm]
  refine pMassDensity_intMat_eq (fun D => ∀ k, (blockSymbol D k).type = .II)
    (fun D hD k => by rw [blockSymbol_high]; exact hD (k + 1))
    (fun D hv he hD => stepEq_typeII hbase hv he (hD 0) (hD 1)) hv he hII hN

end QuadFormsKB.ConwaySloane.Mass.Two
