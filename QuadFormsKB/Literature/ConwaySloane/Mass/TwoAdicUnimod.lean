/-
# Formula (3) at $p = 2$ for one odd unimodular constituent

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264, §6, p. 266, §12, p. 281 (bibliography key `conwaysloane1988`).

For an odd unimodular form $U$ over $\mathbb Z_2$ (blocks of exponent $0$, at least one block $ux^2$), the normal form
(`exists_normal`) gives $U \sim O \perp E$ with $O = \langle u\rangle$ or $\langle u, v\rangle$ and $E$ even
unimodular of dimension $2t'$. Splitting off $O$ (`alphaP_blk_odd`) gives
$\alpha_2(U) = \rho_O(E)\,\alpha_2(O)\,\alpha_2(E)$, with $\alpha_2(\langle u\rangle) = 4$,
$\alpha_2(\langle u, v\rangle) = 8$ or $4$, $\rho_{\langle u\rangle}(E) = 2^{-2t'}$, and $\alpha_2(E)$ from the type II
formula. Comparing with the right-hand side of (3), $m_2(U) = M_2(f_1)/4$ with $f_1$ free
(`pMassTwo_one_typeI`), is the octane computation of $r(f_1) = M_2^{\mathrm{free}}/M_2^{\mathrm{bound}}$.

This file treats odd dimension; indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicNormal
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicOddValue
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicReduced
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBinary

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### $\rho_{\langle u\rangle}(E) = 2^{-\dim E}$ -/

theorem card_evenCol (e : ℕ) : Nat.card {Y : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // EvenCol Y} = 4 ^ e := by
  have e1 : {Y : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // EvenCol Y} ≃
      (Fin e → {z : ZMod (2 ^ 3) // (2 : ℤ) ∣ (z.val : ℤ)}) :=
    { toFun := fun Y k => ⟨Y.1 k 0, Y.2 k⟩
      invFun := fun f => ⟨fun k _ => (f k).1, fun k => (f k).2⟩
      left_inv := fun Y => by ext k j; fin_cases j; rfl
      right_inv := fun f => rfl }
  have h4 : Nat.card {z : ZMod (2 ^ 3) // (2 : ℤ) ∣ (z.val : ℤ)} = 4 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [Nat.card_congr e1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h4]

theorem rhoO_unary_E {a : ℕ} (ha : a = 1) {O : Matrix (Fin a) (Fin a) ℤ} (hO : ∀ i, ¬ 2 ∣ O i i) {e : ℕ}
    {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) :
    rhoO O E = (1 / 2) ^ e := by
  subst ha
  unfold rhoO
  rw [card_goodO_E (hO 0) hEs hEe hEd, card_evenCol]
  push_cast
  rw [mul_one, div_eq_iff (by positivity), ← mul_pow]
  norm_num

/-! ### The pieces of a normal form -/

theorem intMat_unary_apply (u : ℤ) (i j : Fin (dyDim [DyBlock.sq 0 u])) : intMat [DyBlock.sq 0 u] i j = u := by
  show orthSumMat (bInt (DyBlock.sq 0 u)) (intMat []) i j = u
  refine Fin.addCases (fun i' => ?_) (fun i' => i'.elim0) i
  refine Fin.addCases (fun j' => ?_) (fun j' => j'.elim0) j
  rw [orthSumMat_cc]
  have hi : i' = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := i'.isLt; simp [DyBlock.dim] at this; omega)
  have hj : j' = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := j'.isLt; simp [DyBlock.dim] at this; omega)
  subst hi hj
  show (2 : ℤ) ^ (0 : ℤ).toNat * u = u
  simp

theorem intMat_unary_reidx (u : ℤ) : Reidx (intMat [DyBlock.sq 0 u]) !![u] := by
  refine ⟨finCongr rfl, ?_⟩
  ext i j
  rw [intMat_unary_apply]
  simp [Matrix.submatrix_apply]

theorem alphaP_unary_list {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) : alphaP 2 (intMat [DyBlock.sq 0 u]) = 4 := by
  rw [alphaP_reidx (intMat_unary_reidx u)]
  exact alphaP_unary (valid_odd hu)

theorem isEvenList_valid {E : List DyBlock} (hE : IsEvenList 0 E) : ∀ c ∈ E, c.Valid := by
  intro c hc
  cases c with
  | sq e u => exact absurd trivial (hE _ hc).2
  | hyp e => trivial
  | ell e => trivial

theorem isEvenList_evenDiag {E : List DyBlock} (hE : IsEvenList 0 E) : EvenDiag (intMat E) :=
  evenDiag_intMat E (fun c hc => (hE c hc).1.ge) fun c hc hh => (hE c hc).2 hh.1

theorem isEvenList_det {E : List DyBlock} (hE : IsEvenList 0 E) : ¬ 2 ∣ (intMat E).det :=
  det_odd_of_zero (isEvenList_valid hE) fun c hc => (hE c hc).1

/-- The sign $\varepsilon_E$ of an even unimodular block list. -/
def evenSign (E : List DyBlock) : Sign := Sign.prodList (E.map blockSign)

theorem blockF_even {E : List DyBlock} (hE : IsEvenList 0 E) :
    blockF E = ⟨2 * E.length, evenSign E, .II, 0⟩ := by
  unfold blockF evenSign
  have hd : (E.map DyBlock.dim).sum = 2 * E.length := by
    rw [← dyDim_even_list E fun c hc => (hE c hc).2]
    clear hE
    induction E with
    | nil => rfl
    | cons c E ih => simp [dyDim, ih]
  have ht : (E.any fun b => decide (IsSqBlock b)) = false := by
    rw [List.any_eq_false]; intro c hc; simpa using (hE c hc).2
  have ho : (E.map blockOddity).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have := (hE c hc).2
    cases c with
    | sq e u => exact absurd trivial this
    | hyp e => rfl
    | ell e => rfl
  rw [hd, ht, ho]
  rfl

theorem blockSymbol_of_exp_zero {L : List DyBlock} (h0 : ∀ c ∈ L, blockExp c = 0) (k : ℕ) :
    blockSymbol L k = if k = 0 then blockF L else TwoFactor.trivial := by
  rw [blockSymbol_eq_blockF]
  split_ifs with hk
  · subst hk; rw [List.filter_eq_self.mpr fun c hc => by simp [h0 c hc]]
  · rw [List.filter_eq_nil_iff.mpr fun c hc => by simp [h0 c hc]; omega]
    rfl

/-- $\alpha_2(E) = 2^{2t'}\cdot 2\,\Lambda(t')/(1 + \varepsilon_E 2^{-t'})$ for an even unimodular block list $E$ of
dimension $2t'$, $\Lambda(t) = \prod_{i=1}^{t}(1 - 2^{-2i})$ (`lowerProd`). -/
theorem alphaP_even_list {E : List DyBlock} (hE : IsEvenList 0 E) :
    alphaP 2 (intMat E) = 2 ^ (2 * E.length) * (2 * (lowerProd 2 E.length : ℝ)) /
      (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) := by
  have hv := isEvenList_valid hE
  have h0 : ∀ c ∈ E, blockExp c = 0 := fun c hc => (hE c hc).1
  have hP := pMassDensity_intMat_typeII_unimodular E hv h0 fun c hc => (hE c hc).2
  have hdet : padicValInt 2 (intMat E).det = 0 := padicValInt.eq_zero_of_not_dvd (isEvenList_det hE)
  unfold pMassDensity at hP
  rw [hdet] at hP
  have hS0 : blockSymbol E 0 = ⟨2 * E.length, evenSign E, .II, 0⟩ := by
    rw [blockSymbol_of_exp_zero h0, if_pos rfl, blockF_even hE]
  have hS1 : blockSymbol E 1 = TwoFactor.trivial := by rw [blockSymbol_of_exp_zero h0, if_neg one_ne_zero]
  have hm : mFac (blockSymbol E) 0 = mFree (blockSymbol E 0) := by
    rw [mFac_eq, if_neg]
    simp [IsBound, hS1, TwoFactor.trivial]
  have hex := blockSymbol_exists E hv 0
  have hII : (blockSymbol E 0).type = .II := by rw [hS0]
  have hx0 := one_add_ne_zero_II hex hII
  have hf := mFree_II hex hII
  rw [hm, hf, mBound_eq] at hP
  have htq : tq (blockSymbol E 0) = E.length := by rw [hS0]; simp [tq]
  rw [htq] at hP
  rw [hS0] at hP hx0
  simp only at hP hx0
  have hdim : dyDim E = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
  have e2 : ((2 : ℝ) ^ (-((dyDim E : ℕ) : ℤ))) = ((2 : ℝ) ^ (2 * E.length))⁻¹ := by
    rw [hdim, _root_.zpow_neg, zpow_natCast]
  rw [e2] at hP
  have h2 : 2 * E.length / 2 = E.length := by omega
  rw [h2] at hP hx0
  have hA := alphaP_pos Nat.prime_two (isSymm_intMat E) (det_intMat_ne _ hv)
  have hL := lowerProd_pos (E.length)
  have hx0' : (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) ≠ 0 := by
    intro h; apply hx0
    have : ((1 + ((evenSign E).toInt : ℚ) * ((2 : ℚ) ^ E.length)⁻¹ : ℚ) : ℝ) = 0 := by push_cast; exact h
    exact_mod_cast this
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero] at hP
  push_cast at hP
  have hLR : (0 : ℝ) < lowerProd 2 E.length := by exact_mod_cast hL
  field_simp at hP
  rw [eq_div_iff hx0']
  have h2t : (2 : ℝ) ^ E.length ≠ 0 := by positivity
  calc alphaP 2 (intMat E) * (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹)
      = (alphaP 2 (intMat E) * (2 ^ E.length + ((evenSign E).toInt : ℝ))) / 2 ^ E.length := by
        field_simp
    _ = (2 * (lowerProd 2 E.length : ℝ) * 2 ^ E.length * 2 ^ (2 * E.length)) / 2 ^ E.length := by rw [hP]
    _ = 2 ^ (2 * E.length) * (2 * (lowerProd 2 E.length : ℝ)) := by field_simp

/-! ### The right-hand side of (3) for one constituent of type I -/

theorem stepFactor_lowT_I (σ : TwoSymbol) (h : (σ 0).type = .I) :
    stepFactor (lowT σ) = ((mFree (σ 0) / 4 : ℚ) : ℝ) := by
  have hl : ∀ k, lowT σ (k + 1) = TwoFactor.trivial := fun k => rfl
  have hsh : ∀ k, shiftT (lowT σ) k = TwoFactor.trivial := fun k => rfl
  have hl0 : lowT σ 0 = σ 0 := rfl
  have hm0 : mFac (lowT σ) 0 = mFree (σ 0) := by
    rw [mFac_eq, if_neg]; · rfl
    simp [IsBound, hl, trivial_type]
  have hm1 : mFac (lowT σ) 1 = 1 / 2 := by
    unfold mFac
    rw [hl 0, twoSpecies_trivial_bound (by simp [IsBound, hl0, h])]
    simp [Species.diagFactor, Species.odd, lowerProd]
  have hhs : halfFactor (shiftT (lowT σ)) = 1 := by simp [halfFactor, hsh, trivial_type]
  have hms : mFac (shiftT (lowT σ)) 0 = 1 := by
    unfold mFac; rw [hsh 0, twoSpecies_trivial_free (by simp [IsBound, hsh, trivial_type])]
    simp [Species.diagFactor, Species.plus]
  have hh : halfFactor (lowT σ) = 1 / 2 := by simp [halfFactor, hl0, h]
  unfold stepFactor
  rw [hm0, hm1, hhs, hms, hh]
  have h1 : (lowT σ 1).type = .II := rfl
  simp only [hl0, h1, h, show ¬ (ScaledType.II = ScaledType.I) by decide,
    show ¬ (ScaledType.I = ScaledType.II) by decide, and_false, ite_false, sub_zero, zpow_zero, mul_one]
  push_cast
  ring

/-- **The right-hand side of (3)** for a single constituent $f_1$ of type I: $m_2 = r(f_1)/(8\Lambda(t))$,
$t = \lfloor (n-1)/2\rfloor$. -/
theorem pMassTwo_one_typeI {L : List DyBlock} (hv : ∀ c ∈ L, c.Valid) (h0 : ∀ c ∈ L, blockExp c = 0)
    (hI : (blockSymbol L 0).type = .I) :
    pMassTwo (blockSymbol L) 1 =
      ((rI (blockSymbol L 0) / (8 * lowerProd 2 (((blockSymbol L 0).dim - 1) / 2)) : ℚ) : ℝ) := by
  have hlow : low L = L := List.filter_eq_self.mpr fun c hc => by simp [h0 c hc]
  have hσ : blockSymbol L = lowT (blockSymbol L) := by
    conv_lhs => rw [← hlow]
    exact blockSymbol_low L
  have hex := blockSymbol_exists L hv 0
  have hst := stepFactor_lowT_I (blockSymbol L) hI
  rw [hσ, pMassTwo_lowT_one, hst]
  congr 1
  have hl0 : lowT (blockSymbol L) 0 = blockSymbol L 0 := rfl
  rw [hl0, mFree_I hex hI, mBound_eq]
  have htq : tq (blockSymbol L 0) = ((blockSymbol L 0).dim - 1) / 2 := by
    simp [tq, hI]
  rw [htq]
  have hL := lowerProd_pos (((blockSymbol L 0).dim - 1) / 2)
  field_simp
  ring

/-! ### The octane computation -/

theorem blockF_cons_sq (u : ℤ) (E : List DyBlock) :
    blockF (DyBlock.sq 0 u :: E) = ⟨1 + (blockF E).dim, (jacobiTwo u).mul (blockF E).sign, .I,
      (u : ZMod 8) + (blockF E).oddity⟩ := by
  unfold blockF
  simp [blockSign, blockOddity, DyBlock.dim, IsSqBlock, Sign.prodList]

theorem rI_odd {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) {E : List DyBlock} (hE : IsEvenList 0 E) :
    rI (blockF (DyBlock.sq 0 u :: E)) = 1 + (evenSign E).toInt * ((2 : ℚ) ^ E.length)⁻¹ := by
  rw [blockF_cons_sq, blockF_even hE]
  unfold rI octane
  simp only [show 1 + 2 * E.length - 1 = 2 * E.length by omega, show 2 * E.length / 2 = E.length by omega,
    add_zero]
  rcases hu with rfl | rfl | rfl | rfl <;> cases evenSign E <;>
    simp (config := { decide := true }) [jacobiTwo, Sign.mul, Sign.flip, Sign.toInt] <;> ring

theorem rI_even {u v : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) (hv : v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7)
    {E : List DyBlock} (hE : IsEvenList 0 E) :
    rI (blockF (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) =
      if (4 : ℤ) ∣ u + v then 1 + (evenSign E).toInt * ((2 : ℚ) ^ E.length)⁻¹ else 1 := by
  rw [blockF_cons_sq, blockF_cons_sq, blockF_even hE]
  unfold rI octane
  simp only [show 1 + (1 + 2 * E.length) - 1 = 2 * E.length + 1 by omega,
    show (2 * E.length + 1) / 2 = E.length by omega, add_zero]
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> cases evenSign E <;>
    simp (config := { decide := true }) [jacobiTwo, Sign.mul, Sign.flip, Sign.toInt] <;> ring

/-! ### Odd dimension -/

theorem reidx_cons_blk (c : DyBlock) (E : List DyBlock) :
    Reidx (intMat (c :: E)) (blk 1 (intMat [c]) (intMat E)) := by
  rw [blk_eq_orthSum 1, one_smul_int]
  exact reidx_append [c] E

/-- $\alpha_2(\langle u\rangle \perp E) = 8\Lambda(t')/(1 + \varepsilon_E 2^{-t'})$. -/
theorem alphaP_odd_normal {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) {E : List DyBlock} (hE : IsEvenList 0 E) :
    alphaP 2 (intMat (DyBlock.sq 0 u :: E)) =
      8 * (lowerProd 2 E.length : ℝ) / (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) := by
  have hvE := isEvenList_valid hE
  have hvO : ∀ c ∈ [DyBlock.sq 0 u], c.Valid := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact hu
  have heO : ∀ c ∈ [DyBlock.sq 0 u], blockExp c = 0 := by simp [blockExp]
  have hsO : ∀ c ∈ [DyBlock.sq 0 u], IsSqBlock c := by simp [IsSqBlock]
  have hO2 := intMat_sq_mod_two [DyBlock.sq 0 u] hvO heO hsO
  have h := alphaP_blk_odd hvO heO (Or.inl rfl) hO2 (isSymm_intMat E) (isEvenList_evenDiag hE)
    (det_intMat_ne _ hvE)
  have hr : rhoO (intMat [DyBlock.sq 0 u]) (intMat E) = (1 / 2) ^ (dyDim E) :=
    rhoO_unary_E rfl (fun i => by convert valid_odd hu using 2; exact intMat_unary_apply u i i) (isSymm_intMat E).eq
      (isEvenList_evenDiag hE) (isEvenList_det hE)
  rw [alphaP_reidx (reidx_cons_blk _ E), h, alphaP_unary_list hu, alphaP_even_list hE, hr]
  have hdim : dyDim E = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
  rw [hdim, pow_mul]
  have h2 : ((1 : ℝ) / 2) ^ 2 = (2 ^ 2)⁻¹ := by norm_num
  rw [h2, inv_pow]
  have h4 : ((2 : ℝ) ^ 2) ^ E.length ≠ 0 := by positivity
  rw [← pow_mul, mul_comm 2 E.length, pow_mul] at *
  field_simp
  ring

theorem pMassDensity_of_odd_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (h : ¬ 2 ∣ A.det) :
    pMassDensity 2 A = 1 / alphaP 2 A := by
  unfold pMassDensity
  rw [padicValInt.eq_zero_of_not_dvd h]
  simp

theorem valid_cons_even {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) {E : List DyBlock} (hE : IsEvenList 0 E) :
    ∀ c ∈ DyBlock.sq 0 u :: E, c.Valid := by
  intro c hc; rcases List.mem_cons.mp hc with rfl | hc
  · exact hu
  · exact isEvenList_valid hE c hc

theorem exp_cons_even {u : ℤ} {E : List DyBlock} (hE : IsEvenList 0 E) :
    ∀ c ∈ DyBlock.sq 0 u :: E, blockExp c = 0 := by
  intro c hc; rcases List.mem_cons.mp hc with rfl | hc
  · rfl
  · exact (hE c hc).1

/-- **Formula (3) for $\langle u\rangle \perp E$**, $E$ even unimodular. -/
theorem pMass_odd_normal {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) {E : List DyBlock} (hE : IsEvenList 0 E) :
    pMassDensity 2 (intMat (DyBlock.sq 0 u :: E)) = pMassTwo (blockSymbol (DyBlock.sq 0 u :: E)) 1 := by
  have hv := valid_cons_even hu hE
  have h0 := exp_cons_even (u := u) hE
  have hS : blockSymbol (DyBlock.sq 0 u :: E) 0 = blockF (DyBlock.sq 0 u :: E) := by
    rw [blockSymbol_of_exp_zero h0, if_pos rfl]
  have hI : (blockSymbol (DyBlock.sq 0 u :: E) 0).type = .I := by rw [hS, blockF_cons_sq]
  have hrI := rI_ne_zero (blockSymbol_exists _ hv 0) hI
  rw [pMassTwo_one_typeI hv h0 hI, hS, pMassDensity_of_odd_det (det_odd_of_zero hv h0),
    alphaP_odd_normal hu hE]
  rw [hS, rI_odd hu hE] at hrI
  rw [rI_odd hu hE]
  have hd : (blockF (DyBlock.sq 0 u :: E)).dim = 1 + 2 * E.length := by rw [blockF_cons_sq, blockF_even hE]
  rw [hd, show (1 + 2 * E.length - 1) / 2 = E.length by omega]
  have hL := lowerProd_pos E.length
  have hx : (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) ≠ 0 := by
    intro h; apply hrI
    have : ((1 + ((evenSign E).toInt : ℚ) * ((2 : ℚ) ^ E.length)⁻¹ : ℚ) : ℝ) = 0 := by push_cast; exact h
    exact_mod_cast this
  have hLR : (0 : ℝ) < lowerProd 2 E.length := by exact_mod_cast hL
  push_cast
  field_simp

/-! ### The zeros of the quadratic form of an even unimodular block list modulo $4$ -/

section Zeros

/-- Reduction of a column modulo $4$. -/
def col4 (e : ℕ) : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) →+ (Fin e → ZMod (2 ^ 2)) where
  toFun x i := ZMod.castHom (show 2 ^ 2 ∣ 2 ^ 3 by norm_num) (ZMod (2 ^ 2)) (x i 0)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem col4_surj (e : ℕ) : Function.Surjective (col4 e) := by
  intro y
  refine ⟨fun i _ => ((y i).val : ZMod (2 ^ 3)), ?_⟩
  ext i
  simp only [col4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_natCast]
  exact ZMod.natCast_zmod_val (y i)

theorem cast_quad_col (e : ℕ) (E : Matrix (Fin e) (Fin e) ℤ) (x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3))) :
    ((((lift x)ᵀ * E * lift x) 0 0 : ℤ) : ZMod (2 ^ 2)) = qv (red 2 E) (col4 e x) := by
  have hc : ∀ z : ZMod (2 ^ 3), (((z.val : ℤ)) : ZMod (2 ^ 2)) =
      ZMod.castHom (show 2 ^ 2 ∣ 2 ^ 3 by norm_num) (ZMod (2 ^ 2)) z := by
    intro z
    rw [ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]
  unfold qv
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Int.cast_sum,
    Int.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [lift, Matrix.map_apply, col4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← hc, red, Int.coe_castRingHom]
  ring

theorem four_dvd_iff_cast (z : ℤ) : (4 : ℤ) ∣ z ↔ ((z : ZMod (2 ^ 2)) = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

theorem card_qv_zero_add {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E) :
    ((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 0).card : ℤ) -
      ((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 2).card : ℤ) = gsum (red 2 E) ∧
    ((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 0).card : ℤ) +
      ((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 2).card : ℤ) = 4 ^ e := by
  have hval : ∀ y, qv (red 2 E) y = 0 ∨ qv (red 2 E) y = 2 := by
    intro y
    obtain ⟨z, hz⟩ := qv_even hEs hEe y
    have := (show ∀ z : ZMod (2 ^ 2), 2 * z = 0 ∨ 2 * z = 2 by decide) z
    rw [hz]; exact this
  have hdisj : Disjoint (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 0)
      (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 2) := by
    exact Finset.disjoint_filter.mpr fun y _ h0 h2 => by rw [h0] at h2; exact absurd h2 (by decide)
  have hunion : (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 0) ∪
      (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 2) = Finset.univ := by
    ext y; simp [hval y]
  constructor
  · unfold gsum
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => qv (red 2 E) y = 0)]
    have h1 : ∑ y ∈ Finset.univ.filter (fun y => qv (red 2 E) y = 0), chi (qv (red 2 E) y) =
        ((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 0).card : ℤ) := by
      rw [Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.mp hy).2]]; simp [chi]
    have h2 : ∑ y ∈ Finset.univ.filter (fun y => ¬ qv (red 2 E) y = 0), chi (qv (red 2 E) y) =
        -((Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 E) y = 2).card : ℤ) := by
      have hf : (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => ¬ qv (red 2 E) y = 0) =
          Finset.univ.filter fun y => qv (red 2 E) y = 2 := by
        ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hval y with h | h <;> rw [h] <;> decide
      have hc2 : chi (2 : ZMod (2 ^ 2)) = -1 := by decide
      rw [hf, Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.mp hy).2], Finset.sum_const, hc2]
      simp
    rw [h1, h2]; ring
  · rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    simp

/-- **The proportion of zeros**: $\#\{x \in (\mathbb Z/8)^{2t} : 4 \mid x^{\mathsf T}Ex\} = 8^{2t}(1 +
\varepsilon_E 2^{-t})/2$ for an even unimodular block list $E$ of dimension $2t$. -/
theorem card_four_dvd_even {E : List DyBlock} (hE : IsEvenList 0 E) :
    (Nat.card {x : Matrix (Fin (dyDim E)) (Fin 1) (ZMod (2 ^ 3)) //
        (4 : ℤ) ∣ ((lift x)ᵀ * intMat E * lift x) 0 0} : ℝ) =
      8 ^ (dyDim E) * (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2 := by
  classical
  set e := dyDim E
  have hEs := (isSymm_intMat E).eq
  have hEe := isEvenList_evenDiag hE
  have hcomp := card_comp_div (col4 e) (col4_surj e) (fun y => qv (red 2 (intMat E)) y = 0)
  have hset : Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) //
      (4 : ℤ) ∣ ((lift x)ᵀ * intMat E * lift x) 0 0} =
      (Finset.univ.filter fun x => qv (red 2 (intMat E)) (col4 e x) = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [four_dvd_iff_cast, cast_quad_col]
  rw [hset]
  obtain ⟨h1, h2⟩ := card_qv_zero_add hEs hEe
  have hg := gsum_intMat_even E hE
  have hdim : e = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
  have hcardG : Fintype.card (Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3))) = 8 ^ e := by
    rw [show Fintype.card (Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3))) = Fintype.card (Fin e → Fin 1 → ZMod (2 ^ 3))
      from rfl, Fintype.card_fun, Fintype.card_fun]
    simp
  have hcardH : Fintype.card (Fin e → ZMod (2 ^ 2)) = 4 ^ e := by simp
  rw [hcardG, hcardH] at hcomp
  set A := (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 (intMat E)) y = 0).card
  set B := (Finset.univ.filter fun y : Fin e → ZMod (2 ^ 2) => qv (red 2 (intMat E)) y = 2).card
  set t := E.length
  have h8 : ((8 : ℝ) ^ e) = ((2 : ℝ) ^ t) ^ 6 := by
    rw [hdim, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  have h4 : ((4 : ℝ) ^ e) = ((2 : ℝ) ^ t) ^ 4 := by
    rw [hdim, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  have h8t : ((8 : ℝ) ^ t) = ((2 : ℝ) ^ t) ^ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  have h2A : (2 : ℝ) * A = ((2 : ℝ) ^ t) ^ 4 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ t) ^ 3 := by
    have hz : (2 : ℤ) * A = 4 ^ e + (evenSign E).toInt * 8 ^ t := by
      have hg' : gsum (red 2 (intMat E)) = (evenSign E).toInt * 8 ^ t := hg
      linear_combination h1.trans hg' + h2
    have hz' : ((2 * A : ℤ) : ℝ) = ((4 ^ e + (evenSign E).toInt * 8 ^ t : ℤ) : ℝ) := by rw [hz]
    push_cast at hz'
    rw [hz', h4, h8t]
  push_cast at hcomp
  rw [h8, h4] at hcomp
  rw [h8]
  have hX : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)] at hcomp
  have hX4 : ((2 : ℝ) ^ t) ^ 4 ≠ 0 := by positivity
  have hC : ((Finset.univ.filter fun x => qv (red 2 (intMat E)) (col4 e x) = 0).card : ℝ) =
      A * ((2 : ℝ) ^ t) ^ 2 := by
    apply mul_right_cancel₀ hX4; linear_combination hcomp
  rw [hC, eq_div_iff two_ne_zero, mul_add, mul_one,
    show ((2 : ℝ) ^ t) ^ 6 * (((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ t)⁻¹) =
      ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ t) ^ 5 by field_simp]
  linear_combination ((2 : ℝ) ^ t) ^ 2 * h2A

end Zeros

/-! ### Reduction to the normal forms -/

/-- **Formula (3) for one odd unimodular constituent from the two normal shapes**: if it holds for
$\langle u\rangle \perp E$ and $\langle u, v\rangle \perp E$ ($E$ even unimodular), it holds for every list of blocks
of exponent $0$ of type I. -/
theorem pMassUnimodular_of_normal
    (hodd : ∀ u (E : List DyBlock), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → IsEvenList 0 E →
      pMassDensity 2 (intMat (DyBlock.sq 0 u :: E)) = pMassTwo (blockSymbol (DyBlock.sq 0 u :: E)) 1)
    (heven : ∀ u v (E : List DyBlock), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
      IsEvenList 0 E → pMassDensity 2 (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) =
        pMassTwo (blockSymbol (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) 1) :
    PMassUnimodularTwoTypeI := by
  refine ⟨fun L hv h0 hI => ?_⟩
  obtain ⟨us, E, hus, hE, hlen, hne, hF⟩ := exists_normal 0 L hv h0
  have hsq : ∃ c ∈ L, IsSqBlock c := by
    have : L.any (fun b => decide (IsSqBlock b)) = true := by
      by_contra h
      rw [blockSymbol_eq_blockF] at hI
      rw [List.filter_eq_self.mpr fun c hc => by simp [h0 c hc]] at hI
      unfold blockF at hI
      simp only [Bool.not_eq_true] at h
      rw [h] at hI
      simp at hI
    simpa using this
  have hus0 := hne hsq
  obtain ⟨L', hL'⟩ : ∃ L', L' = sqList 0 us ++ E := ⟨_, rfl⟩
  have hv' : ∀ c ∈ L', c.Valid := by
    intro c hc
    rw [hL'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hus u hu
    · exact isEvenList_valid hE c hc
  have h0' : ∀ c ∈ L', blockExp c = 0 := by
    intro c hc
    rw [hL'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; rfl
    · exact (hE c hc).1
  have hσ : blockSymbol L = blockSymbol L' := by
    have := blockSymbol_congr_prefix (e := 0) h0 h0' (hL' ▸ hF) []
    simpa using this
  have hn : dyDim L' = dyDim L := by
    rw [dyDim_eq_sum, dyDim_eq_sum]
    exact (congrArg TwoFactor.dim (hL' ▸ hF)).symm
  rw [pMassDensity_eq_of_blockSymbol_eq hv (fun c hc => (h0 c hc).ge) hv' (fun c hc => (h0' c hc).ge) hn hσ, hσ]
  subst hL'
  match us, hlen, hus0, hus with
  | [u], _, _, hus => exact hodd u E (hus u (by simp)) hE
  | [u, v], _, _, hus => exact heven u v E (hus u (by simp)) (hus v (by simp)) hE

/-! ### Even dimension -/

theorem four_dvd_sub_iff {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) : (4 : ℤ) ∣ u - v ↔ ¬ (4 : ℤ) ∣ u + v := by
  omega

/-- $\alpha_2(\langle u, v\rangle \perp E) = 8\Lambda(t')/r$ with $r = 1 + \varepsilon_E 2^{-t'}$ if $4 \mid u + v$ and
$r = 1$ otherwise. -/
theorem alphaP_even_normal {u v : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) (hv : v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7)
    {E : List DyBlock} (hE : IsEvenList 0 E) :
    alphaP 2 (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) =
      8 * (lowerProd 2 E.length : ℝ) /
        (if (4 : ℤ) ∣ u + v then 1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹ else 1) := by
  have hvE := isEvenList_valid hE
  have hvO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], c.Valid := by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hu
    · exact hv
  have heO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], blockExp c = 0 := by simp [blockExp]
  have hsO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], IsSqBlock c := by simp [IsSqBlock]
  have hO2 := intMat_sq_mod_two [DyBlock.sq 0 u, DyBlock.sq 0 v] hvO heO hsO
  have h := alphaP_blk_odd hvO heO (Or.inr rfl) hO2 (isSymm_intMat E) (isEvenList_evenDiag hE)
    (det_intMat_ne _ hvE)
  have hr : Reidx (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E))
      (blk 1 (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) (intMat E)) := by
    rw [blk_eq_orthSum 1, one_smul_int]
    exact reidx_append [DyBlock.sq 0 u, DyBlock.sq 0 v] E
  have hu' := valid_odd hu
  have hv' := valid_odd hv
  have hα2 : alphaP 2 (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) = if (4 : ℤ) ∣ u - v then 8 else 4 := by
    rw [intMat_sq_sq]; exact alphaP_diag2 hu' hv'
  have hρ := rhoO_binary_E_intMat (isSymm_intMat E).eq (isEvenList_evenDiag hE) (isEvenList_det hE) hu' hv'
  have hcnt := card_four_dvd_even hE
  rw [alphaP_reidx hr, h, hα2, hρ, alphaP_even_list hE]
  have hdim : dyDim E = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
  have hL := lowerProd_pos E.length
  have hLR : (0 : ℝ) < lowerProd 2 E.length := by exact_mod_cast hL
  have hx : (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) ≠ 0 := by
    have h1 := rI_ne_zero (f := blockF (DyBlock.sq 0 u :: E))
      (by
        have := blockSymbol_exists (DyBlock.sq 0 u :: E) (valid_cons_even hu hE) 0
        rwa [blockSymbol_of_exp_zero (exp_cons_even hE), if_pos rfl] at this)
      (by rw [blockF_cons_sq])
    rw [rI_odd hu hE] at h1
    intro h0; apply h1
    have : ((1 + ((evenSign E).toInt : ℚ) * ((2 : ℚ) ^ E.length)⁻¹ : ℚ) : ℝ) = 0 := by push_cast; exact h0
    exact_mod_cast this
  have hx2 : ((evenSign E).toInt : ℝ) + 2 ^ E.length ≠ 0 := by
    intro h0; apply hx; field_simp; linarith
  have h4t : (4 : ℝ) ^ E.length = (2 : ℝ) ^ (E.length * 2) := by rw [mul_comm, pow_mul]; norm_num
  by_cases h4 : (4 : ℤ) ∣ u + v
  · have h4' : ¬ (4 : ℤ) ∣ u - v := fun h' => (four_dvd_sub_iff hu' hv').mp h' h4
    rw [if_neg h4', if_pos h4, if_pos h4, mul_one, hdim]
    rw [pow_mul]
    have h2 : ((1 : ℝ) / 2) ^ 2 = (2 ^ 2)⁻¹ := by norm_num
    rw [h2, inv_pow]
    field_simp
    have hx3 : (2 : ℝ) ^ E.length + ((evenSign E).toInt : ℝ) ≠ 0 := by rwa [add_comm]
    rw [← pow_mul]; field_simp; try ring
  · have h4' : (4 : ℤ) ∣ u - v := (four_dvd_sub_iff hu' hv').mpr h4
    rw [if_pos h4', if_neg h4, if_neg h4, hcnt, hdim]
    rw [pow_mul, pow_mul]
    have h2 : ((1 : ℝ) / 2) ^ 2 = (2 ^ 2)⁻¹ := by norm_num
    rw [h2, inv_pow]
    have h8 : ((8 : ℝ) ^ 2) ^ E.length ≠ 0 := by positivity
    field_simp
    have hx3 : (2 : ℝ) ^ E.length + ((evenSign E).toInt : ℝ) ≠ 0 := by rwa [add_comm]
    rw [← pow_mul]; field_simp; try ring

/-- **Formula (3) for $\langle u, v\rangle \perp E$**, $E$ even unimodular. -/
theorem pMass_even_normal {u v : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) (hv : v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7)
    {E : List DyBlock} (hE : IsEvenList 0 E) :
    pMassDensity 2 (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) =
      pMassTwo (blockSymbol (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) 1 := by
  have hv0 : ∀ c ∈ DyBlock.sq 0 u :: DyBlock.sq 0 v :: E, c.Valid := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · exact hu
    · exact valid_cons_even hv hE c hc
  have h0 : ∀ c ∈ DyBlock.sq 0 u :: DyBlock.sq 0 v :: E, blockExp c = 0 := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact exp_cons_even hE c hc
  have hS : blockSymbol (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E) 0 = blockF (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E) := by
    rw [blockSymbol_of_exp_zero h0, if_pos rfl]
  have hI : (blockSymbol (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E) 0).type = .I := by rw [hS, blockF_cons_sq]
  have hrI := rI_ne_zero (blockSymbol_exists _ hv0 0) hI
  rw [pMassTwo_one_typeI hv0 h0 hI, hS, pMassDensity_of_odd_det (det_odd_of_zero hv0 h0),
    alphaP_even_normal hu hv hE]
  rw [hS, rI_even hu hv hE] at hrI
  rw [rI_even hu hv hE]
  have hd : (blockF (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)).dim = 1 + (1 + 2 * E.length) := by
    rw [blockF_cons_sq, blockF_cons_sq, blockF_even hE]
  rw [hd, show (1 + (1 + 2 * E.length) - 1) / 2 = E.length by omega]
  have hL := lowerProd_pos E.length
  have hLR : (0 : ℝ) < lowerProd 2 E.length := by exact_mod_cast hL
  split_ifs with h4
  · have hx : (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) ≠ 0 := by
      rw [if_pos h4] at hrI
      intro h0; apply hrI
      have : ((1 + ((evenSign E).toInt : ℚ) * ((2 : ℚ) ^ E.length)⁻¹ : ℚ) : ℝ) = 0 := by push_cast; exact h0
      exact_mod_cast this
    push_cast
    field_simp
  · push_cast
    field_simp

/-- **Formula (3) at $p = 2$ for one odd unimodular constituent** (Conway–Sloane 1988, (3), p. 263, Table 1, p. 264,
§6, p. 266; the paper does not prove (3) at $p = 2$): the former input `PMassUnimodularTwoTypeI` holds. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (p = 2, one odd unimodular constituent)"]
theorem pMassUnimodularTwoTypeI_holds : PMassUnimodularTwoTypeI :=
  pMassUnimodular_of_normal (fun _ _ hu hE => pMass_odd_normal hu hE) fun _ _ _ hu hv hE => pMass_even_normal hu hv hE

end QuadFormsKB.ConwaySloane.Mass.Two
