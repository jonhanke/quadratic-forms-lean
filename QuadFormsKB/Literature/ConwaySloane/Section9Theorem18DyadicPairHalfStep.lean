/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, pair-glue combined with the halving step

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicOverlattice.lean`: a local lattice $M = \gamma\mathbb Z_2^n$ over
$\mathbb Q_2$ ($v \mid 2$), with Gram matrix $G$ = `locGram Q v γ`, a scalar $c \ne 0$ and $A = cG$.

**The step.** Combine the halving step (`Section9Theorem18DyadicHalfStep.lean`) for a set $C$ of basis indices
($A_{ij} \in 4\mathbb Z_2$, $A_{ii} \in 8\mathbb Z_2$ on $C$, orthogonal to the rest) with the pair-glue step
(`Section9Theorem18DyadicPairGlue.lean`) for two indices $l_1 \ne l_2 \notin C$ with $b_{l_1}, b_{l_2}$ orthogonal to all
other basis vectors, $a = A_{l_1l_1}/2$ and $b = A_{l_2l_2}/2$ units with $\lvert a + b\rvert \le \lvert 4\rvert$, and
the remaining block unimodular ($\lvert\det\hat A\rvert = 1$, $\hat A$ = `hatA` with columns of $C \cup \{l_1, l_2\}$
replaced by unit vectors). Then the overlattice $M^+ = M + \tfrac12\sum_{k \in C}\mathbb Z_2 b_k +
\mathbb Z_2\tfrac12(b_{l_1} + b_{l_2})$ (basis $\gamma W_C W_{l_1l_2}$, `gamP`) is exactly the set of $x$ with $2x \in M$,
$cB(x, M) \subseteq \mathbb Z_2$ and $cQ(x) \in \mathbb Z_2$ (`CanonPredM Q M 2 c c`), so `EvenStable` passes from
`gamP` to $\gamma$.

**Defines** `PairHalf.Data Q v γ c C l₁ l₂` (the hypotheses), `PairHalf.gamP`.

**Proves** `PairHalf.pairHalf_canonPred_basis`, `PairHalf.pairHalf_mem_of_canonPred`, `PairHalf.evenStable_of_pairHalf`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicHalfStep

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace PairHalf

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- The hypotheses of the combined step for a basis $\gamma$, a scalar $c$, the halved set $C$ and the pair
$l_1 \ne l_2$ (both outside $C$). -/
structure Data (Q : QuadForm ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin n) (v.adicCompletion ℚ))
    (c : v.adicCompletion ℚ) (C : Finset (Fin n)) (l₁ l₂ : Fin n) : Prop where
  hc : c ≠ 0
  hl : l₁ ≠ l₂
  hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1
  heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1
  hCorth : ∀ i ∈ C, ∀ j, j ∉ C → locGram Q v γ i j = 0
  hC4 : ∀ i ∈ C, ∀ j ∈ C, Valued.v (c * locGram Q v γ i j) ≤ Valued.v (4 : v.adicCompletion ℚ)
  hC8 : ∀ i ∈ C, Valued.v (c * locGram Q v γ i i / 2) ≤ Valued.v (4 : v.adicCompletion ℚ)
  hl₁C : l₁ ∉ C
  hl₂C : l₂ ∉ C
  hcol₁ : ∀ i, i ≠ l₁ → locGram Q v γ i l₁ = 0
  hcol₂ : ∀ i, i ≠ l₂ → locGram Q v γ i l₂ = 0
  ha : Valued.v (c * locGram Q v γ l₁ l₁ / 2) = 1
  hb : Valued.v (c * locGram Q v γ l₂ l₂ / 2) = 1
  hab : Valued.v (c * (locGram Q v γ l₁ l₁ + locGram Q v γ l₂ l₂) / 2) ≤ Valued.v (4 : v.adicCompletion ℚ)
  hdet : Valued.v (HalfStep.hatA (c • locGram Q v γ) C {l₁, l₂}).det = 1

/-- The basis $\gamma W_C W_{l_1l_2}$ of $M^+$: $b_k$ ($k \notin C$, $k \ne l_1$), $\tfrac12 b_k$ ($k \in C$),
$\tfrac12(b_{l_1} + b_{l_2})$ ($k = l_1$). -/
def gamP (γ : GL (Fin n) Fv) (C : Finset (Fin n)) {l₁ l₂ : Fin n} (hl : l₁ ≠ l₂) : GL (Fin n) Fv :=
  PairGlue.gam (HalfStep.gamH γ C) hl

theorem gamP_val_mulVec (γ : GL (Fin n) Fv) (C : Finset (Fin n)) {l₁ l₂ : Fin n} (hl : l₁ ≠ l₂) (y : Fin n → Fv) :
    (gamP γ C hl).val *ᵥ y = γ.val *ᵥ (HalfStep.W C *ᵥ (PairGlue.W l₁ l₂ *ᵥ y)) := by
  rw [gamP, PairGlue.gam_val, HalfStep.gamH_val, mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]

variable {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C : Finset (Fin n)} {l₁ l₂ : Fin n}

theorem W_wvec (hD : Data Q v γ c C l₁ l₂) :
    HalfStep.W (v := v) C *ᵥ PairGlue.wvec l₁ l₂ = PairGlue.wvec l₁ l₂ := by
  rw [PairGlue.wvec, mulVec_smul, mulVec_add, HalfStep.W_mulVec_single, HalfStep.W_mulVec_single]
  simp [hD.hl₁C, hD.hl₂C]

/-- **The basis vectors of $M^+$ satisfy the canonical predicate.** -/
theorem pairHalf_canonPred_basis (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hD : Data Q v γ c C l₁ l₂) (k : Fin n) :
    CanonPredM Q (locAct v γ (std v)) 2 c c ((gamP γ C hD.hl).val *ᵥ Pi.single k 1) := by
  have hv2 := valued_two_dyadic v h2
  have hbk : γ.val *ᵥ Pi.single k 1 ∈ locAct v γ (std v) := ⟨_, single_mem_std k (by simp), rfl⟩
  rw [gamP_val_mulVec, PairGlue.W_mulVec_single]
  by_cases hk1 : k = l₁
  · subst hk1
    simp only [ite_true]
    rw [W_wvec hD]
    refine ⟨?_, fun y hy => ?_, ?_⟩
    · rw [← mulVec_smul, PairGlue.wvec, smul_smul, show (2 : Fv) * (1 / 2) = 1 by norm_num, one_smul]
      exact ⟨_, (std v).add_mem (single_mem_std _ (by simp)) (single_mem_std _ (by simp)), rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_locAct.mp hy
      have he1 := mem_std_iff.mp he
      rw [qbil_mulVec_locGram, PairGlue.wvec, smul_dotProduct, add_dotProduct, single_dotProduct,
        single_dotProduct, one_mul, one_mul, smul_eq_mul]
      have e1 : (locGram Q v γ *ᵥ e) k = locGram Q v γ k k * e k := by
        simp only [mulVec, dotProduct]
        rw [Finset.sum_eq_single k (fun i _ hi => by
          rw [locGram_symm', hD.hcol₁ i hi, zero_mul]) (by simp)]
      have e2 : (locGram Q v γ *ᵥ e) l₂ = locGram Q v γ l₂ l₂ * e l₂ := by
        simp only [mulVec, dotProduct]
        rw [Finset.sum_eq_single l₂ (fun i _ hi => by
          rw [locGram_symm', hD.hcol₂ i hi, zero_mul]) (by simp)]
      rw [e1, e2]
      have : c * (1 / 2 * (locGram Q v γ k k * e k + locGram Q v γ l₂ l₂ * e l₂)) =
          (c * locGram Q v γ k k / 2) * e k + (c * locGram Q v γ l₂ l₂ / 2) * e l₂ := by ring
      rw [this]
      refine Valuation.map_add_le _ ?_ ?_
      · rw [map_mul, hD.ha, one_mul]; exact he1 k
      · rw [map_mul, hD.hb, one_mul]; exact he1 l₂
    · have hQ2 := two_mul_evalIn_locGram (Q := Q) (v := v) γ (PairGlue.wvec k l₂)
      have hval : (PairGlue.wvec k l₂ : Fin n → Fv) ⬝ᵥ (locGram Q v γ *ᵥ PairGlue.wvec k l₂) =
          (locGram Q v γ k k + locGram Q v γ l₂ l₂) / 4 := by
        have h12 : locGram Q v γ k l₂ = 0 := by
          rw [locGram_symm']; exact hD.hcol₁ l₂ (Ne.symm hD.hl)
        have h21 : locGram Q v γ l₂ k = 0 := hD.hcol₁ l₂ (Ne.symm hD.hl)
        simp only [PairGlue.wvec, smul_add, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
          smul_dotProduct, dotProduct_smul, PairGlue.gram_single_single, smul_eq_mul, h12, h21]
        ring
      have e : c * Q.evalIn Fv (γ.val *ᵥ PairGlue.wvec k l₂) =
          (c * (locGram Q v γ k k + locGram Q v γ l₂ l₂) / 2) / 4 := by
        have : Q.evalIn Fv (γ.val *ᵥ PairGlue.wvec k l₂) =
            (locGram Q v γ k k + locGram Q v γ l₂ l₂) / 8 := by
          rw [hval] at hQ2
          linear_combination hQ2 / 2
        rw [this]; ring
      rw [e, map_div₀]
      have h4 : (0 : ℤᵐ⁰) < Valued.v (4 : Fv) :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (by norm_num))
      rw [div_le_one₀ h4]
      exact hD.hab
  · simp only [hk1, ite_false]
    rw [HalfStep.W_mulVec_single]
    by_cases hk : k ∈ C
    · simp only [hk, ite_true]
      refine ⟨?_, fun y hy => ?_, ?_⟩
      · rw [← mulVec_smul, smul_smul, show (2 : Fv) * (1 / 2) = 1 by norm_num, one_smul]; exact hbk
      · obtain ⟨e, he, rfl⟩ := mem_locAct.mp hy
        have he1 := mem_std_iff.mp he
        rw [qbil_mulVec_locGram, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
        have hsum : Valued.v (c * (locGram Q v γ *ᵥ e) k) ≤ Valued.v (4 : Fv) := by
          simp only [mulVec, dotProduct, Finset.mul_sum]
          refine Valuation.map_sum_le _ fun j _ => ?_
          by_cases hj : j ∈ C
          · rw [← mul_assoc, map_mul]
            calc Valued.v (c * locGram Q v γ k j) * Valued.v (e j) ≤ Valued.v (4 : Fv) * 1 :=
                  mul_le_mul' (hD.hC4 k hk j hj) (he1 j)
              _ = _ := mul_one _
          · rw [hD.hCorth k hk j hj, zero_mul, mul_zero, map_zero]; exact zero_le
        have e2 : c * (1 / 2 * (locGram Q v γ *ᵥ e) k) = (c * (locGram Q v γ *ᵥ e) k) / 2 := by ring
        rw [e2, map_div₀, div_le_one₀ (by rw [hv2]; exact exp_pos)]
        exact hsum.trans (HalfStep.valued_four_lt h2)
      · have h := two_mul_evalIn_locGram (Q := Q) (v := v) γ ((1 / 2 : Fv) • Pi.single k 1)
        have hq : Q.evalIn Fv (γ.val *ᵥ ((1 / 2 : Fv) • Pi.single k 1)) = locGram Q v γ k k / 8 := by
          have hd : ((1 / 2 : Fv) • (Pi.single k 1 : Fin n → Fv)) ⬝ᵥ
              (locGram Q v γ *ᵥ ((1 / 2 : Fv) • Pi.single k 1)) = locGram Q v γ k k / 4 := by
            rw [mulVec_smul, smul_dotProduct, dotProduct_smul, PairGlue.gram_single_single, smul_eq_mul,
              smul_eq_mul]; ring
          rw [hd] at h
          linear_combination h / 2
        rw [hq]
        have e : c * (locGram Q v γ k k / 8) = (c * locGram Q v γ k k / 2) / 4 := by ring
        rw [e, map_div₀]
        have h4 : (0 : ℤᵐ⁰) < Valued.v (4 : Fv) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (by norm_num))
        rw [div_le_one₀ h4]
        exact hD.hC8 k hk
    · simp only [hk, ite_false, one_smul]
      refine ⟨?_, fun y hy => ?_, ?_⟩
      · rw [two_smul]; exact (locAct v γ (std v)).add_mem hbk hbk
      · obtain ⟨e, he, rfl⟩ := mem_locAct.mp hy
        have he1 := mem_std_iff.mp he
        rw [HalfStep.qbil_basis_left]
        simp only [mulVec, dotProduct, Finset.mul_sum]
        refine valued_sum_le_one _ _ fun j _ => ?_
        rw [← mul_assoc, map_mul]
        exact mul_le_one' (hD.hint k j) (he1 j)
      · have h := two_mul_evalIn_locGram (Q := Q) (v := v) γ (Pi.single k 1)
        rw [PairGlue.gram_single_single] at h
        have : c * Q.evalIn Fv (γ.val *ᵥ Pi.single k 1) = c * locGram Q v γ k k / 2 := by
          rw [← h]; ring
        rw [this]; exact hD.heven k

/-- **$M^+$ is characterized by the canonical predicate.** -/
theorem pairHalf_mem_of_canonPred (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hD : Data Q v γ c C l₁ l₂) (x : Fin n → Fv)
    (hx : CanonPredM Q (locAct v γ (std v)) 2 c c x) : x ∈ locAct v (gamP γ C hD.hl) (std v) := by
  obtain ⟨hx2, hxB, hxQ⟩ := hx
  set G := locGram Q v γ
  set A := c • G
  set P : Finset (Fin n) := {l₁, l₂} with hP
  set d := (γ⁻¹ : GL (Fin n) Fv).val *ᵥ x with hd
  have hxd : γ.val *ᵥ d = x := by
    rw [hd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAij : ∀ i j, A i j = c * G i j := fun i j => by simp [A]
  have h2d : ∀ i, Valued.v (2 * d i) ≤ 1 := by
    intro i
    have := ((mem_locAct_std_iff γ _).mp hx2) i
    rwa [mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hAd : ∀ j, Valued.v ((A *ᵥ d) j) ≤ 1 := by
    intro j
    have hbj : γ.val *ᵥ Pi.single j 1 ∈ locAct v γ (std v) := ⟨_, single_mem_std j (by simp), rfl⟩
    have := hxB _ hbj
    rw [← hxd, qbil_mulVec_locGram, PairGlue.gram_vec_single] at this
    have e : (A *ᵥ d) j = c * ∑ i, d i * G i j := by
      simp only [mulVec, dotProduct, hAij, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : G j i = G i j := HalfStep.symm_G j i
      rw [hs]; ring
    rw [e]; exact this
  have hPC : ∀ l ∈ P, l ∉ C := by
    intro l hl
    simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hD.hl₁C
    · exact hD.hl₂C
  have hPorth : ∀ l ∈ P, ∀ j, j ≠ l → G j l = 0 := by
    intro l hl j hj
    simp only [hP, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hD.hcol₁ j hj
    · exact hD.hcol₂ j hj
  -- the three parts of $d$
  set dC : Fin n → Fv := fun i => if i ∈ C then d i else 0 with hdC
  set dD : Fin n → Fv := fun i => if i ∈ P then d i else 0 with hdD
  set d0 : Fin n → Fv := fun i => if i ∈ C ∨ i ∈ P then 0 else d i with hd0
  have hsplit : d = d0 + dD + dC := by
    funext i
    by_cases hC : i ∈ C
    · have hD' : i ∉ P := fun h => hPC i h hC
      simp [hd0, hdD, hdC, hC, hD']
    · by_cases hDi : i ∈ P
      · simp [hd0, hdD, hdC, hC, hDi]
      · simp [hd0, hdD, hdC, hC, hDi]
  -- zero patterns of $A$
  have hA_C : ∀ i j, i ∈ C → j ∉ C → A i j = 0 := fun i j hi hj => by
    rw [hAij]; exact mul_eq_zero_of_right _ (hD.hCorth i hi j hj)
  have hA_C' : ∀ i j, i ∉ C → j ∈ C → A i j = 0 := fun i j hi hj => by
    rw [hAij]; exact mul_eq_zero_of_right _ ((HalfStep.symm_G i j).trans (hD.hCorth j hj i hi))
  have hA_D : ∀ i j, j ∈ P → i ≠ j → A i j = 0 := fun i j hj hij => by
    rw [hAij]; exact mul_eq_zero_of_right _ (hPorth j hj i hij)
  have hA_D' : ∀ i j, i ∈ P → i ≠ j → A i j = 0 := fun i j hi hij => by
    rw [hAij]; exact mul_eq_zero_of_right _ ((HalfStep.symm_G i j).trans (hPorth i hi j (Ne.symm hij)))
  -- $d_0$ is integral
  have hAd0 : ∀ j, Valued.v ((A *ᵥ d0) j) ≤ 1 := by
    intro j
    by_cases hj : j ∈ C ∨ j ∈ P
    · have : (A *ᵥ d0) j = 0 := by
        simp only [mulVec, dotProduct]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i ∈ C ∨ i ∈ P
        · simp [hd0, hi]
        · have hi' : ¬ (i ∈ C ∨ i ∈ P) := hi
          push Not at hi'
          rcases hj with hj | hj
          · rw [hA_C j i hj hi'.1, zero_mul]
          · rw [hA_D' j i hj (fun h => hi'.2 (h ▸ hj)), zero_mul]
      rw [this, map_zero]; exact zero_le
    · push Not at hj
      have e : (A *ᵥ d) j = (A *ᵥ d0) j := by
        have z1 : (A *ᵥ dD) j = 0 := by
          simp only [mulVec, dotProduct]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i ∈ P
          · rw [hA_D j i hi (fun h => hj.2 (h ▸ hi)), zero_mul]
          · simp [hdD, hi]
        have z2 : (A *ᵥ dC) j = 0 := by
          simp only [mulVec, dotProduct]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i ∈ C
          · rw [hA_C' j i hj.1 hi, zero_mul]
          · simp [hdC, hi]
        conv_lhs => rw [hsplit]
        rw [mulVec_add, mulVec_add, Pi.add_apply, Pi.add_apply, z1, z2, add_zero, add_zero]
      rw [← e]; exact hAd j
  have hhat : HalfStep.hatA A C P *ᵥ d0 = A *ᵥ d0 := by
    funext j
    simp only [mulVec, dotProduct, HalfStep.hatA, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ C ∨ i ∈ P
    · simp [hd0, hi]
    · simp only [hi, ite_false]
  have hhat_int : ∀ i j, Valued.v (HalfStep.hatA A C P i j) ≤ 1 := by
    intro i j
    simp only [HalfStep.hatA, Matrix.of_apply]
    split_ifs
    · simp
    · simp
    · rw [hAij]; exact hD.hint i j
  have hdet' : Valued.v (HalfStep.hatA A C P).det = 1 := hD.hdet
  have hdet0 : (HalfStep.hatA A C P).det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdet'; exact zero_ne_one hdet'
  have hd0int : ∀ i, Valued.v (d0 i) ≤ 1 := by
    have hinv : (HalfStep.hatA A C P)⁻¹ *ᵥ (HalfStep.hatA A C P *ᵥ d0) = d0 := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet0), one_mulVec]
    intro i
    rw [← hinv, hhat]
    exact mulVec_integral _ _ (Glue.inv_integral _ hhat_int hdet') hAd0 i
  -- the quadratic condition
  have hcross : ∀ p q : Fin n → Fv, (∀ i j, p i ≠ 0 → q j ≠ 0 → A i j = 0) → p ⬝ᵥ (A *ᵥ q) = 0 :=
    fun p q h => HalfStep.dot_eq_zero_of_supp h
  have s0D : ∀ i j, d0 i ≠ 0 → dD j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjD : j ∈ P := by by_contra h; simp [hdD, h] at hj
    have hiD : ¬ (i ∈ C ∨ i ∈ P) := by intro h; simp [hd0, h] at hi
    exact hA_D i j hjD (fun h => hiD (Or.inr (h ▸ hjD)))
  have s0C : ∀ i j, d0 i ≠ 0 → dC j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjC : j ∈ C := by by_contra h; simp [hdC, h] at hj
    have hiC : i ∉ C := by intro h; simp [hd0, h] at hi
    exact hA_C' i j hiC hjC
  have sDC : ∀ i j, dD i ≠ 0 → dC j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjC : j ∈ C := by by_contra h; simp [hdC, h] at hj
    have hiD : i ∈ P := by by_contra h; simp [hdD, h] at hi
    exact hA_C' i j (hPC i hiD) hjC
  have sym : ∀ p q : Fin n → Fv, q ⬝ᵥ (A *ᵥ p) = p ⬝ᵥ (A *ᵥ q) := fun p q => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hquad : d ⬝ᵥ (A *ᵥ d) = d0 ⬝ᵥ (A *ᵥ d0) + dD ⬝ᵥ (A *ᵥ dD) + dC ⬝ᵥ (A *ᵥ dC) := by
    have h1 := hcross d0 dD s0D
    have h2' := hcross d0 dC s0C
    have h3 := hcross dD dC sDC
    have h1' : dD ⬝ᵥ (A *ᵥ d0) = 0 := by rw [sym]; exact h1
    have h2'' : dC ⬝ᵥ (A *ᵥ d0) = 0 := by rw [sym]; exact h2'
    have h3' : dC ⬝ᵥ (A *ᵥ dD) = 0 := by rw [sym]; exact h3
    rw [hsplit]
    simp only [mulVec_add, dotProduct_add, add_dotProduct, h1, h2', h3, h1', h2'', h3']
    ring
  have hcQ : c * Q.evalIn Fv x = d ⬝ᵥ (A *ᵥ d) / 2 := by
    have h := two_mul_evalIn_locGram (Q := Q) (v := v) γ d
    rw [hxd] at h
    have : d ⬝ᵥ (A *ᵥ d) = c * (d ⬝ᵥ (G *ᵥ d)) := by
      simp only [A, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [this, ← h]; ring
  have hhalf0 : Valued.v ((d0 ⬝ᵥ (A *ᵥ d0)) / 2) ≤ 1 :=
    valued_half_quad_le_one' A hA (fun i j => by rw [hAij]; exact hD.hint i j)
      (fun i => by rw [hAij]; exact hD.heven i) d0 hd0int
  -- the $C$ part
  set A4 : Matrix (Fin n) (Fin n) Fv := Matrix.of fun i j => if i ∈ C ∧ j ∈ C then A i j / 4 else 0 with hA4
  have hGs : ∀ a b, G a b = G b a := fun a b => HalfStep.symm_G a b
  have hA4s : A4ᵀ = A4 := by
    ext i j
    simp only [hA4, transpose_apply, Matrix.of_apply, hAij]
    by_cases hi : i ∈ C <;> by_cases hj : j ∈ C <;> simp [hi, hj, hGs j i]
  have h4ne : Valued.v (4 : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr (by norm_num)
  have h4pos : (0 : ℤᵐ⁰) < Valued.v (4 : Fv) := zero_lt_iff.mpr h4ne
  have hA4int : ∀ i j, Valued.v (A4 i j) ≤ 1 := by
    intro i j
    simp only [hA4, Matrix.of_apply]
    split_ifs with h
    · rw [map_div₀, div_le_one₀ h4pos, hAij]; exact hD.hC4 i h.1 j h.2
    · simp
  have hA4even : ∀ i, Valued.v (A4 i i / 2) ≤ 1 := by
    intro i
    simp only [hA4, Matrix.of_apply]
    split_ifs with h
    · rw [show A i i / 4 / 2 = (c * G i i / 2) / 4 by rw [hAij]; ring, map_div₀, div_le_one₀ h4pos]
      exact hD.hC8 i h.1
    · simp
  have h2dC : ∀ i, Valued.v ((2 • dC) i) ≤ 1 := by
    intro i
    simp only [hdC, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs
    · exact h2d i
    · simp
  have hCeq : dC ⬝ᵥ (A *ᵥ dC) = (2 • dC) ⬝ᵥ (A4 *ᵥ (2 • dC)) := by
    simp only [dotProduct, mulVec, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hdC, hA4, Matrix.of_apply]
    by_cases hi : i ∈ C <;> by_cases hj : j ∈ C <;> simp [hi, hj]; ring
  have hhalfC : Valued.v ((dC ⬝ᵥ (A *ᵥ dC)) / 2) ≤ 1 := by
    rw [hCeq]; exact valued_half_quad_le_one' A4 hA4s hA4int hA4even _ h2dC
  have hhalfD : Valued.v ((dD ⬝ᵥ (A *ᵥ dD)) / 2) ≤ 1 := by
    have e : (dD ⬝ᵥ (A *ᵥ dD)) / 2 =
        c * Q.evalIn Fv x - (d0 ⬝ᵥ (A *ᵥ d0)) / 2 - (dC ⬝ᵥ (A *ᵥ dC)) / 2 := by
      rw [hcQ, hquad]; ring
    rw [e]
    exact Valuation.map_sub_le _ (Valuation.map_sub_le _ hxQ hhalf0) hhalfC
  -- the pair part
  set a := c * G l₁ l₁ / 2 with ha
  set b := c * G l₂ l₂ / 2 with hb
  have hG21 : G l₂ l₁ = 0 := hD.hcol₁ l₂ (Ne.symm hD.hl)
  have hG12 : G l₁ l₂ = 0 := (HalfStep.symm_G l₁ l₂).trans hG21
  have hdDeq : dD = Pi.single l₁ (d l₁) + Pi.single l₂ (d l₂) := by
    funext i
    by_cases h1 : i = l₁
    · subst h1; simp [hdD, hP, hD.hl]
    · by_cases h2' : i = l₂
      · subst h2'; simp [hdD, hP, h1]
      · simp [hdD, hP, h1, h2']
  have hpair : (dD ⬝ᵥ (A *ᵥ dD)) / 2 = a * d l₁ ^ 2 + b * d l₂ ^ 2 := by
    rw [hdDeq]
    simp only [mulVec_add, mulVec_single, dotProduct_add, add_dotProduct, single_dotProduct]
    simp [hAij, Matrix.col, hG12, hG21, ha, hb]
    ring
  have hab1 : Valued.v (a * d l₁ ^ 2 + b * d l₂ ^ 2) ≤ 1 := by rw [← hpair]; exact hhalfD
  have hcong : Valued.v (2 * d l₂ - 2 * d l₁) ≤ Valued.v (2 : Fv) := by
    have hab' : Valued.v (b + a) ≤ Valued.v (4 : Fv) := by
      rw [show b + a = c * (G l₁ l₁ + G l₂ l₂) / 2 by simp only [a, b]; ring]; exact hD.hab
    refine PairGlue.pair_congr h2 hD.hb hab' (h2d l₂) (h2d l₁) ?_
    have : b * (2 * d l₂) ^ 2 + a * (2 * d l₁) ^ 2 = 4 * (a * d l₁ ^ 2 + b * d l₂ ^ 2) := by ring
    rw [this, map_mul]
    calc Valued.v (4 : Fv) * Valued.v (a * d l₁ ^ 2 + b * d l₂ ^ 2) ≤ Valued.v (4 : Fv) * 1 :=
          mul_le_mul' le_rfl hab1
      _ = _ := mul_one _
  -- the coordinates in the basis
  set d' : Fin n → Fv := fun i =>
    if i ∈ C then 2 * d i else if i = l₁ then 2 * d l₁ else if i = l₂ then d l₂ - d l₁ else d i with hd'
  have hd'int : ∀ i, Valued.v (d' i) ≤ 1 := by
    intro i
    by_cases hC : i ∈ C
    · simp only [hd', hC, ite_true]; exact h2d i
    · by_cases h1 : i = l₁
      · simp only [hd', h1, hD.hl₁C, ite_true, ite_false]; exact h2d l₁
      · by_cases h2' : i = l₂
        · simp only [hd', h2', hD.hl₂C, Ne.symm hD.hl, ite_true, ite_false]
          have e : d l₂ - d l₁ = (2 * d l₂ - 2 * d l₁) / 2 := by ring
          rw [e, map_div₀, div_le_one₀ (by rw [valued_two_dyadic v h2]; exact exp_pos)]
          exact hcong
        · have := hd0int i
          have hiP : i ∉ P := by simp [hP, h1, h2']
          simp only [hd0, hC, hiP, or_self, ite_false] at this
          simp only [hd', hC, h1, h2', ite_false]; exact this
  have hWd' : HalfStep.W C *ᵥ (PairGlue.W l₁ l₂ *ᵥ d') = d := by
    funext i
    rw [HalfStep.W, mulVec_diagonal, PairGlue.W_mulVec_apply hD.hl]
    by_cases hC : i ∈ C
    · have h1 : i ≠ l₁ := fun h => hD.hl₁C (h ▸ hC)
      have h2' : i ≠ l₂ := fun h => hD.hl₂C (h ▸ hC)
      simp only [hC, h1, h2', ite_true, ite_false, hd']
      ring
    · by_cases h1 : i = l₁
      · subst h1; simp only [hC, hd', ite_true, ite_false]; ring
      · by_cases h2' : i = l₂
        · subst h2'
          have hl1C : l₁ ∉ C := hD.hl₁C
          simp only [hC, h1, hd', hl1C, ite_true, ite_false]; ring
        · simp only [hC, h1, h2', hd', ite_false, one_mul]
  refine ⟨d', mem_std_iff.mpr hd'int, ?_⟩
  show (gamP γ C hD.hl).val *ᵥ d' = x
  rw [gamP_val_mulVec, hWd', hxd]

/-- **Pair-glue and halving step**: `EvenStable` passes from `gamP` to $\gamma$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (pair-glue and halving step of a chain of overlattices of L₂)"]
theorem evenStable_of_pairHalf (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hD : Data Q v γ c C l₁ l₂)
    (h : EvenStable Q (gamP γ C hD.hl)) : EvenStable Q γ :=
  evenStable_of_step γ (gamP γ C hD.hl) (pairHalf_canonPred_basis h2 hD) (pairHalf_mem_of_canonPred h2 hD) h

end PairHalf

end QuadFormsKB.ConwaySloane
