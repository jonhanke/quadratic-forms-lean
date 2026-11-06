/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the halving step of a chain of overlattices

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicOverlattice.lean`: a local lattice $M = \gamma\mathbb Z_2^n$ over
$\mathbb Q_2$ ($v \mid 2$), with Gram matrix $G$ = `locGram Q v γ` of $B$ in the basis $b_k = \gamma e_k$, a scalar
$c \ne 0$ and $A = cG$.

**The step.** Let $C$ be a set of basis indices whose vectors are orthogonal to the others, with $A_{ij} \in 4\mathbb Z_2$
($i, j \in C$) and $A_{ii} \in 8\mathbb Z_2$ ($i \in C$); let $D$ be a set of at most one index $l \notin C$ with $b_l$
orthogonal to all other basis vectors and $A_{ll}/2$ a unit; and let the remaining block be unimodular: the matrix
$\hat A$ (`hatA`), which is $A$ with the columns in $C \cup D$ replaced by the corresponding unit vectors, has
$\lvert\det\hat A\rvert = 1$. Then the overlattice $M^+ = M + \tfrac12\sum_{k \in C}\mathbb Z_2 b_k$ (basis
$\gamma W$, $W = \operatorname{diag}(\tfrac12$ on $C$, $1$ elsewhere$)$, `gamH`) is exactly the set of $x$ with
$2x \in M$, $cB(x, M) \subseteq \mathbb Z_2$ and $cQ(x) \in \mathbb Z_2$ (`CanonPredM Q M 2 c c`). So every
automorphism of $M$ preserves $M^+$, and `EvenStable` passes from $\gamma W$ to $\gamma$ (`evenStable_of_half`).

**Defines** `HalfStep.Data Q v γ c C D` (the hypotheses), `HalfStep.W`, `HalfStep.gamH`, `HalfStep.hatA`.

**Proves** `HalfStep.half_canonPred_basis`, `HalfStep.half_mem_of_canonPred`, `HalfStep.evenStable_of_half`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPairGlue

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace HalfStep

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- $\hat A$: the matrix $A$ with the columns in $C \cup D$ replaced by the unit vectors. -/
def hatA (A : Matrix (Fin n) (Fin n) Fv) (C D : Finset (Fin n)) : Matrix (Fin n) (Fin n) Fv :=
  Matrix.of fun i j => if j ∈ C ∨ j ∈ D then (if i = j then 1 else 0) else A i j

/-- The hypotheses of the halving step for a basis $\gamma$, a scalar $c$, the halved set $C$ and the set $D$ of at
most one single $\langle 2u\rangle$. -/
structure Data (Q : QuadForm ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin n) (v.adicCompletion ℚ))
    (c : v.adicCompletion ℚ) (C D : Finset (Fin n)) : Prop where
  hc : c ≠ 0
  hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1
  heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1
  hCorth : ∀ i ∈ C, ∀ j, j ∉ C → locGram Q v γ i j = 0
  hC4 : ∀ i ∈ C, ∀ j ∈ C, Valued.v (c * locGram Q v γ i j) ≤ Valued.v (4 : v.adicCompletion ℚ)
  hC8 : ∀ i ∈ C, Valued.v (c * locGram Q v γ i i / 2) ≤ Valued.v (4 : v.adicCompletion ℚ)
  hDC : ∀ l ∈ D, l ∉ C
  hDorth : ∀ l ∈ D, ∀ j, j ≠ l → locGram Q v γ j l = 0
  hDu : ∀ l ∈ D, Valued.v (c * locGram Q v γ l l / 2) = 1
  hD1 : D.card ≤ 1
  hdet : Valued.v (hatA (c • locGram Q v γ) C D).det = 1

/-- The basis change $W = \operatorname{diag}(w)$, $w_k = \tfrac12$ for $k \in C$ and $1$ otherwise. -/
def W (C : Finset (Fin n)) : Matrix (Fin n) (Fin n) Fv := Matrix.diagonal fun k => if k ∈ C then 1 / 2 else 1

theorem det_W_ne (C : Finset (Fin n)) : (W (v := v) C).det ≠ 0 := by
  rw [W, det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  split_ifs <;> norm_num

/-- The basis $\gamma W$ of $M^+$. -/
def gamH (γ : GL (Fin n) Fv) (C : Finset (Fin n)) : GL (Fin n) Fv :=
  γ * Matrix.GeneralLinearGroup.mkOfDetNeZero (W C) (det_W_ne C)

theorem gamH_val (γ : GL (Fin n) Fv) (C : Finset (Fin n)) : (gamH γ C).val = γ.val * W C := by
  rw [gamH, Units.val_mul]; rfl

theorem W_mulVec_single (C : Finset (Fin n)) (k : Fin n) :
    W (v := v) C *ᵥ Pi.single k 1 = (if k ∈ C then (1 / 2 : Fv) else 1) • Pi.single k 1 := by
  ext i
  rw [W, mulVec_diagonal]
  by_cases h : i = k
  · subst h; simp
  · simp [Pi.single_apply, h]

variable {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C D : Finset (Fin n)}

theorem symm_G (i j : Fin n) : locGram Q v γ i j = locGram Q v γ j i := locGram_symm' γ i j

/-- $\lvert B(b_k, y)\rvert$ for $y \in M$ in coordinates: $(Ge)_k = \sum_j G_{kj}e_j$. -/
theorem qbil_basis_left (k : Fin n) (e : Fin n → Fv) :
    qbil Q Fv (γ.val *ᵥ Pi.single k 1) (γ.val *ᵥ e) = (locGram Q v γ *ᵥ e) k := by
  rw [qbil_mulVec_locGram, single_dotProduct, one_mul]

theorem valued_four_lt (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (4 : Fv) ≤ Valued.v (2 : Fv) := by
  rw [PairGlue.valued_four_eq h2, valued_two_dyadic v h2, exp_le_exp]; norm_num

/-- **The basis vectors of $M^+$ satisfy the canonical predicate.** -/
theorem half_canonPred_basis (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hD : Data Q v γ c C D) (k : Fin n) :
    CanonPredM Q (locAct v γ (std v)) 2 c c ((gamH γ C).val *ᵥ Pi.single k 1) := by
  have hv2 := valued_two_dyadic v h2
  have hbk : γ.val *ᵥ Pi.single k 1 ∈ locAct v γ (std v) := ⟨_, single_mem_std k (by simp), rfl⟩
  rw [gamH_val, ← mulVec_mulVec, W_mulVec_single]
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
      exact hsum.trans (valued_four_lt h2)
    · have h := two_mul_evalIn_locGram (Q := Q) (v := v) γ ((1 / 2 : Fv) • Pi.single k 1)
      have hq : Q.evalIn Fv (γ.val *ᵥ ((1 / 2 : Fv) • Pi.single k 1)) = locGram Q v γ k k / 8 := by
        have hd : ((1 / 2 : Fv) • (Pi.single k 1 : Fin n → Fv)) ⬝ᵥ (locGram Q v γ *ᵥ ((1 / 2 : Fv) • Pi.single k 1))
            = locGram Q v γ k k / 4 := by
          rw [mulVec_smul, smul_dotProduct, dotProduct_smul, PairGlue.gram_single_single, smul_eq_mul,
            smul_eq_mul]; ring
        rw [hd] at h
        linear_combination h / 2
      rw [hq]
      have e : c * (locGram Q v γ k k / 8) = (c * locGram Q v γ k k / 2) / 4 := by ring
      rw [e, map_div₀]
      have h4 : (0 : ℤᵐ⁰) < Valued.v (4 : Fv) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (by norm_num))
      rw [div_le_one₀ h4]
      exact hD.hC8 k hk
  · simp only [hk, ite_false, one_smul]
    refine ⟨?_, fun y hy => ?_, ?_⟩
    · rw [two_smul]; exact (locAct v γ (std v)).add_mem hbk hbk
    · obtain ⟨e, he, rfl⟩ := mem_locAct.mp hy
      have he1 := mem_std_iff.mp he
      rw [qbil_basis_left]
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine valued_sum_le_one _ _ fun j _ => ?_
      rw [← mul_assoc, map_mul]
      exact mul_le_one' (hD.hint k j) (he1 j)
    · have h := two_mul_evalIn_locGram (Q := Q) (v := v) γ (Pi.single k 1)
      rw [PairGlue.gram_single_single] at h
      have : c * Q.evalIn Fv (γ.val *ᵥ Pi.single k 1) = c * locGram Q v γ k k / 2 := by
        rw [← h]; ring
      rw [this]; exact hD.heven k

/-- $p^{\mathsf T}Aq = 0$ when $A_{ij} = 0$ whenever $p_i \ne 0$ and $q_j \ne 0$. -/
theorem dot_eq_zero_of_supp {A : Matrix (Fin n) (Fin n) Fv} {p q : Fin n → Fv}
    (h : ∀ i j, p i ≠ 0 → q j ≠ 0 → A i j = 0) : p ⬝ᵥ (A *ᵥ q) = 0 := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hp : p i = 0
  · rw [hp, zero_mul]
  by_cases hq : q j = 0
  · rw [hq, mul_zero, mul_zero]
  rw [h i j hp hq, zero_mul, mul_zero]

/-- **$M^+$ is characterized by the canonical predicate.** -/
theorem half_mem_of_canonPred (hD : Data Q v γ c C D) (x : Fin n → Fv)
    (hx : CanonPredM Q (locAct v γ (std v)) 2 c c x) : x ∈ locAct v (gamH γ C) (std v) := by
  obtain ⟨hx2, hxB, hxQ⟩ := hx
  set G := locGram Q v γ
  set A := c • G
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
      have hs : G j i = G i j := symm_G j i
      rw [hs]; ring
    rw [e]; exact this
  -- the three parts of $d$
  set dC : Fin n → Fv := fun i => if i ∈ C then d i else 0 with hdC
  set dD : Fin n → Fv := fun i => if i ∈ D then d i else 0 with hdD
  set d0 : Fin n → Fv := fun i => if i ∈ C ∨ i ∈ D then 0 else d i with hd0
  have hsplit : d = d0 + dD + dC := by
    ext i
    by_cases hC : i ∈ C
    · have hD' : i ∉ D := fun h => hD.hDC i h hC
      simp [hd0, hdD, hdC, hC, hD']
    · by_cases hDi : i ∈ D
      · simp [hd0, hdD, hdC, hC, hDi]
      · simp [hd0, hdD, hdC, hC, hDi]
  -- zero patterns of $A$
  have hA_C : ∀ i j, i ∈ C → j ∉ C → A i j = 0 := fun i j hi hj => by rw [hAij]; exact mul_eq_zero_of_right _ (hD.hCorth i hi j hj)
  have hA_C' : ∀ i j, i ∉ C → j ∈ C → A i j = 0 := fun i j hi hj => by
    rw [hAij]; exact mul_eq_zero_of_right _ ((symm_G i j).trans (hD.hCorth j hj i hi))
  have hA_D : ∀ i j, j ∈ D → i ≠ j → A i j = 0 := fun i j hj hij => by rw [hAij]; exact mul_eq_zero_of_right _ (hD.hDorth j hj i hij)
  have hA_D' : ∀ i j, i ∈ D → i ≠ j → A i j = 0 := fun i j hi hij => by
    rw [hAij]; exact mul_eq_zero_of_right _ ((symm_G i j).trans (hD.hDorth i hi j (Ne.symm hij)))
  -- $d_0$ is integral
  have hAd0 : ∀ j, Valued.v ((A *ᵥ d0) j) ≤ 1 := by
    intro j
    by_cases hj : j ∈ C ∨ j ∈ D
    · have : (A *ᵥ d0) j = 0 := by
        simp only [mulVec, dotProduct]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i ∈ C ∨ i ∈ D
        · simp [hd0, hi]
        · have hi' : ¬ (i ∈ C ∨ i ∈ D) := hi
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
          by_cases hi : i ∈ D
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
  have hhat : hatA A C D *ᵥ d0 = A *ᵥ d0 := by
    funext j
    simp only [mulVec, dotProduct, hatA, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ C ∨ i ∈ D
    · simp [hd0, hi]
    · simp only [hi, ite_false]
  have hhat_int : ∀ i j, Valued.v (hatA A C D i j) ≤ 1 := by
    intro i j
    simp only [hatA, Matrix.of_apply]
    split_ifs
    · simp
    · simp
    · rw [hAij]; exact hD.hint i j
  have hdet0 : (hatA A C D).det ≠ 0 := by
    intro h0; have := hD.hdet; rw [h0, map_zero] at this; exact zero_ne_one this
  have hd0int : ∀ i, Valued.v (d0 i) ≤ 1 := by
    have hinv : (hatA A C D)⁻¹ *ᵥ (hatA A C D *ᵥ d0) = d0 := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet0), one_mulVec]
    intro i
    rw [← hinv, hhat]
    exact mulVec_integral _ _ (Glue.inv_integral _ hhat_int hD.hdet) hAd0 i
  -- the quadratic condition: $cQ(x) = \frac12 d_0^TAd_0 + \frac12 d_D^TAd_D + \frac12 d_C^TAd_C$
  have hcross : ∀ p q : Fin n → Fv, (∀ i j, p i ≠ 0 → q j ≠ 0 → A i j = 0) → p ⬝ᵥ (A *ᵥ q) = 0 :=
    fun p q h => dot_eq_zero_of_supp h
  have s0D : ∀ i j, d0 i ≠ 0 → dD j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjD : j ∈ D := by by_contra h; simp [hdD, h] at hj
    have hiD : ¬ (i ∈ C ∨ i ∈ D) := by intro h; simp [hd0, h] at hi
    exact hA_D i j hjD (fun h => hiD (Or.inr (h ▸ hjD)))
  have s0C : ∀ i j, d0 i ≠ 0 → dC j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjC : j ∈ C := by by_contra h; simp [hdC, h] at hj
    have hiC : i ∉ C := by intro h; simp [hd0, h] at hi
    exact hA_C' i j hiC hjC
  have sDC : ∀ i j, dD i ≠ 0 → dC j ≠ 0 → A i j = 0 := fun i j hi hj => by
    have hjC : j ∈ C := by by_contra h; simp [hdC, h] at hj
    have hiD : i ∈ D := by by_contra h; simp [hdD, h] at hi
    exact hA_C' i j (hD.hDC i hiD) hjC
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
    have : d ⬝ᵥ (A *ᵥ d) = c * (d ⬝ᵥ (G *ᵥ d)) := by simp only [A, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [this, ← h]; ring
  have hhalf0 : Valued.v ((d0 ⬝ᵥ (A *ᵥ d0)) / 2) ≤ 1 :=
    valued_half_quad_le_one' A hA (fun i j => by rw [hAij]; exact hD.hint i j)
      (fun i => by rw [hAij]; exact hD.heven i) d0 hd0int
  -- the $C$ part: $\frac12 d_C^TAd_C = \frac12 (2d_C)^T(A_C/4)(2d_C)$
  set A4 : Matrix (Fin n) (Fin n) Fv := Matrix.of fun i j => if i ∈ C ∧ j ∈ C then A i j / 4 else 0 with hA4
  have hGs : ∀ a b, G a b = G b a := fun a b => symm_G a b
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
    by_cases hi : i ∈ C <;> by_cases hj : j ∈ C <;> simp [hi, hj] <;> ring
  have hhalfC : Valued.v ((dC ⬝ᵥ (A *ᵥ dC)) / 2) ≤ 1 := by
    rw [hCeq]; exact valued_half_quad_le_one' A4 hA4s hA4int hA4even _ h2dC
  have hhalfD : Valued.v ((dD ⬝ᵥ (A *ᵥ dD)) / 2) ≤ 1 := by
    have e : (dD ⬝ᵥ (A *ᵥ dD)) / 2 = c * Q.evalIn Fv x - (d0 ⬝ᵥ (A *ᵥ d0)) / 2 - (dC ⬝ᵥ (A *ᵥ dC)) / 2 := by
      rw [hcQ, hquad]; ring
    rw [e]
    exact Valuation.map_sub_le _ (Valuation.map_sub_le _ hxQ hhalf0) hhalfC
  -- $d_l$ is integral for $l \in D$
  have hdDint : ∀ l ∈ D, Valued.v (d l) ≤ 1 := by
    intro l hl
    have hDl : D = {l} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hl, fun m hm => ?_⟩
      exact Finset.card_le_one.mp hD.hD1 m hm l hl
    have e : (dD ⬝ᵥ (A *ᵥ dD)) / 2 = (c * G l l / 2) * d l ^ 2 := by
      have hdDl : dD = Pi.single l (d l) := by
        ext i
        by_cases hi : i = l
        · subst hi; simp [hdD, hDl]
        · simp [hdD, hDl, hi]
      rw [hdDl, mulVec_single, single_dotProduct]
      simp [hAij, Matrix.col]
      ring
    rw [e, map_mul, hD.hDu l hl, one_mul, map_pow] at hhalfD
    by_contra hcon
    push Not at hcon
    have : 1 < Valued.v (d l) ^ 2 := one_lt_pow₀ hcon two_ne_zero
    exact absurd hhalfD (not_le.mpr this)
  -- the coordinates in the basis $\gamma W$
  set d' : Fin n → Fv := fun i => if i ∈ C then 2 * d i else d i with hd'
  have hd'int : ∀ i, Valued.v (d' i) ≤ 1 := by
    intro i
    by_cases hC : i ∈ C
    · simp only [hd', hC, ite_true]; exact h2d i
    · simp only [hd', hC, ite_false]
      by_cases hDi : i ∈ D
      · exact hdDint i hDi
      · have := hd0int i
        simp only [hd0, hC, hDi, or_self, ite_false] at this
        exact this
  have hWd' : W C *ᵥ d' = d := by
    ext i
    rw [W, mulVec_diagonal]
    by_cases hC : i ∈ C
    · simp only [hd', hC, ite_true]; ring
    · simp only [hd', hC, ite_false, one_mul]
  refine ⟨d', mem_std_iff.mpr hd'int, ?_⟩
  show (gamH γ C).val *ᵥ d' = x
  rw [gamH_val, ← mulVec_mulVec, hWd', hxd]

/-- **The halving step**: `EvenStable` passes from $\gamma W$ to $\gamma$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (halving step: a deep Jordan block of L₂ scaled down to an overlattice)"]
theorem evenStable_of_half (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hD : Data Q v γ c C D)
    (h : EvenStable Q (gamH γ C)) : EvenStable Q γ :=
  evenStable_of_step γ (gamH γ C) (half_canonPred_basis h2 hD) (half_mem_of_canonPred hD) h

end HalfStep

end QuadFormsKB.ConwaySloane
