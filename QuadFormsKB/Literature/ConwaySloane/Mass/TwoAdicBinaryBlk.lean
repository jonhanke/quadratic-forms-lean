/-
# The proportion $\rho$ for an odd binary part against $E \perp 2B$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §12, p. 281 (bibliography key `conwaysloane1988`).

Let $O = \langle u, v\rangle$ with $u, v$ odd, $E$ even unimodular and $B$ any integral symmetric matrix, and
$M = E \perp 2B$ (`blk 2 E B`). For $W$ with $E$-rows $w_0, w_1$ and $B$-rows $x_0, x_1$ (its two columns), with
$Q_E(w) = w^{\mathsf T}Ew$ and $Q_B(x) = x^{\mathsf T}Bx$, `goodO_binary_blk_iff` shows that $W$ is good iff
$w_0 \equiv w_1 \pmod 2$ and: if $u + v \equiv 0 \pmod 4$, then $Q_B(x_1 - x_0) \equiv 0 \pmod 4$; otherwise
($Q_B(x_0)$ even iff $Q_E(w_0) \equiv 0 \pmod 4$) and $Q_B(x_1 - x_0) \equiv 0 \pmod 4$. Counting modulo $8$
(`rhoO_binary_blk`) gives $\rho_O(M) = 2^{-e}\,p_B\cdot(1 \text{ or } C)$. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBinary

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### The block matrix $E \perp 2B$ acting on two columns -/

section Blk2

variable {e b : ℕ} (E : Matrix (Fin e) (Fin e) ℤ) (B : Matrix (Fin b) (Fin b) ℤ)

theorem blk_mul_cast {n : Type*} [Fintype n] (W : Matrix (Fin (e + b)) n ℤ) (k : Fin e) (j : n) :
    (blk 2 E B * W) (Fin.castAdd b k) j = (E * W.submatrix (Fin.castAdd b) id) k j := by
  simp [blk, Matrix.mul_apply, Fin.sum_univ_add]

theorem blk_mul_nat {n : Type*} [Fintype n] (W : Matrix (Fin (e + b)) n ℤ) (k : Fin b) (j : n) :
    (blk 2 E B * W) (Fin.natAdd e k) j = 2 * (B * W.submatrix (Fin.natAdd e) id) k j := by
  simp only [blk, Matrix.mul_apply, Fin.sum_univ_add, submatrix_apply, Function.comp, id,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem bil_blk (x y : Fin (e + b) → ℤ) :
    bil (blk 2 E B) x y = bil E (fun k => x (Fin.castAdd b k)) (fun k => y (Fin.castAdd b k)) +
      2 * bil B (fun k => x (Fin.natAdd e k)) (fun k => y (Fin.natAdd e k)) := by
  simp only [bil, blk, Fin.sum_univ_add, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- The second condition of `GoodO` for $O = \langle u, v\rangle$ and $M = E \perp 2B$: only the $E$-rows matter. -/
theorem evenDiag_binary_blk_iff {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEd : ¬ 2 ∣ E.det)
    {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (W : Matrix (Fin (e + b)) (Fin 2) ℤ) :
    EvenDiag (blk 2 E B * W * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Wᵀ * blk 2 E B) ↔
      ∀ k : Fin e, 2 ∣ W (Fin.castAdd b k) 0 - W (Fin.castAdd b k) 1 := by
  have hMs : (blk 2 E B)ᵀ = blk 2 E B :=
    (blk_isSymm (p := 2) (show E.IsSymm from hEs) (show B.IsSymm from hBs)).eq
  set P := blk 2 E B * W with hPdef
  have hP : blk 2 E B * W * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Wᵀ * blk 2 E B =
      P * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Pᵀ := by
    rw [hPdef, Matrix.transpose_mul, hMs]; simp only [Matrix.mul_assoc]
  have hd : ∀ i, (P * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Pᵀ) i i =
      v * P i 0 * P i 0 + u * P i 1 * P i 1 := by
    intro i
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of]
    ring
  let Z : Matrix (Fin e) (Fin 1) ℤ := Matrix.of fun k _ => W (Fin.castAdd b k) 0 + W (Fin.castAdd b k) 1
  have hZ : ∀ k, (E * Z) k 0 = P (Fin.castAdd b k) 0 + P (Fin.castAdd b k) 1 := by
    intro k
    rw [hPdef, blk_mul_cast, blk_mul_cast]
    simp only [Z, Matrix.mul_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib, submatrix_apply, id]
  unfold EvenDiag
  rw [hP]
  simp only [hd, par_iff hu hv]
  constructor
  · intro h k
    have := two_dvd_of_mul_unimod hEd (Y := Z) fun i => by rw [hZ]; exact h _
    have h2 := this k
    simp only [Z, Matrix.of_apply] at h2
    omega
  · intro h i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rw [← hZ, Matrix.mul_apply]
      exact Finset.dvd_sum fun j _ => by
        have := h j
        simp only [Z, Matrix.of_apply]
        exact Dvd.dvd.mul_left (by omega) _
    · rw [hPdef, blk_mul_nat, blk_mul_nat]
      exact ⟨(B * W.submatrix (Fin.natAdd e) id) k 0 + (B * W.submatrix (Fin.natAdd e) id) k 1, by ring⟩

end Blk2

/-! ### Finite checks over $\mathbb Z/8$ -/

theorem fact_s : ∀ u : ZMod (2 ^ 3), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → ∀ s : ZMod (2 ^ 3),
    4 * (s * (u - s)) = 0 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem fact_main : ∀ u : ZMod (2 ^ 3), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) →
    ∀ v : ZMod (2 ^ 3), (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
    ∀ q : ZMod (2 ^ 3), (q = 0 ∨ q = 2 ∨ q = 4 ∨ q = 6) →
    ∀ a b c : ZMod (2 ^ 3),
    (((u + v = 0 ∨ u + v = 4) →
      (((u + q + 2 * a) * (v + q + 2 * b) - (q + 2 * c) * (q + 2 * c) - u * v = 0 ∧
        ((u - v = 0 ∨ u - v = 4) → (q + 2 * a = 0 ∨ q + 2 * a = 4))) ↔
        (a + b - 2 * c = 0 ∨ a + b - 2 * c = 4))) ∧
    (¬ (u + v = 0 ∨ u + v = 4) →
      (((u + q + 2 * a) * (v + q + 2 * b) - (q + 2 * c) * (q + 2 * c) - u * v = 0 ∧
        ((u - v = 0 ∨ u - v = 4) → (q + 2 * a = 0 ∨ q + 2 * a = 4))) ↔
        (((a = 0 ∨ a = 2 ∨ a = 4 ∨ a = 6) ↔ (q = 0 ∨ q = 4)) ∧
          (a + b - 2 * c = 0 ∨ a + b - 2 * c = 4))))) := by
  decide +kernel

theorem z2_dvd_iff (z : ℤ) : (2 : ℤ) ∣ z ↔
    (z : ZMod (2 ^ 3)) = 0 ∨ (z : ZMod (2 ^ 3)) = 2 ∨ (z : ZMod (2 ^ 3)) = 4 ∨ (z : ZMod (2 ^ 3)) = 6 := by
  refine ⟨z_even_cases, fun h => ?_⟩
  rcases h with h | h | h | h
  · have := z8_dvd_of_eq (x := z) (y := 0) (by simpa using h); omega
  · have := z8_dvd_of_eq (x := z) (y := 2) (by simpa using h); omega
  · have := z8_dvd_of_eq (x := z) (y := 4) (by simpa using h); omega
  · have := z8_dvd_of_eq (x := z) (y := 6) (by simpa using h); omega

/-- **The arithmetic of the binary condition against $E \perp 2B$.** -/
theorem key_arith2 {u v q s m a b c : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (hq : 2 ∣ q) :
    ((8 : ℤ) ∣ (u + (q + 2 * a)) * (v + (q + 4 * s + 8 * m) + 2 * b) -
        (q + 2 * s + 2 * c) * (q + 2 * s + 2 * c) - u * v ∧
      ((4 : ℤ) ∣ u - v → (4 : ℤ) ∣ (u + (q + 2 * a)) - u)) ↔
    (if (4 : ℤ) ∣ u + v then (4 : ℤ) ∣ a + b - 2 * c
      else ((2 : ℤ) ∣ a ↔ (4 : ℤ) ∣ q) ∧ (4 : ℤ) ∣ a + b - 2 * c) := by
  have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
  have hs := fact_s _ (z_odd_cases hu) (s : ZMod (2 ^ 3))
  have hL : (((u + (q + 2 * a)) * (v + (q + 4 * s + 8 * m) + 2 * b) -
        (q + 2 * s + 2 * c) * (q + 2 * s + 2 * c) - u * v : ℤ) : ZMod (2 ^ 3)) =
      (((u + q + 2 * a) * (v + q + 2 * b) - (q + 2 * c) * (q + 2 * c) - u * v : ℤ) : ZMod (2 ^ 3)) := by
    push_cast
    linear_combination hs + ((s : ZMod (2 ^ 3)) * (a - c) + (m : ZMod (2 ^ 3)) * (u + q + 2 * a)) * h8
  have hm := fact_main (u : ZMod (2 ^ 3)) (z_odd_cases hu) v (z_odd_cases hv) q (z_even_cases hq) a b c
  rw [z8_dvd_iff, hL, show u + (q + 2 * a) - u = q + 2 * a by ring]
  by_cases h4 : (4 : ℤ) ∣ u + v
  · have h4' := (z4_dvd_iff _).mp h4
    push_cast at h4'
    have := hm.1 h4'
    simp only [h4, ↓reduceIte]
    rw [z4_dvd_iff, z4_dvd_iff, z4_dvd_iff]
    push_cast
    exact this
  · have h4' : ¬ ((u : ZMod (2 ^ 3)) + v = 0 ∨ (u : ZMod (2 ^ 3)) + v = 4) := by
      intro h; apply h4; rw [z4_dvd_iff]; push_cast; exact h
    have := hm.2 h4'
    simp only [h4, ↓reduceIte]
    rw [z4_dvd_iff, z4_dvd_iff, z4_dvd_iff, z4_dvd_iff, z2_dvd_iff]
    push_cast
    exact this

/-! ### Bilinear lemmas -/

section Bil2

variable {e : ℕ} (E : Matrix (Fin e) (Fin e) ℤ)

theorem bil_shift (hEs : Eᵀ = E) (hEe : EvenDiag E) (w d : Fin e → ℤ) :
    ∃ m, bil E (fun l => w l + 2 * d l) (fun l => w l + 2 * d l) = bil E w w + 4 * bil E w d + 8 * m := by
  obtain ⟨m, hm⟩ := bil_even E hEs hEe d
  refine ⟨m, ?_⟩
  rw [bil_add_fst E hEs, bil_add_snd, bil_add_snd, bil_comm E hEs d w, hm]
  ring

theorem bil_sub_self (hEs : Eᵀ = E) (x y : Fin e → ℤ) :
    bil E (fun k => y k - x k) (fun k => y k - x k) = bil E x x + bil E y y - 2 * bil E x y := by
  have hc := bil_comm E hEs y x
  unfold bil at *
  have h : ∀ k l, (y k - x k) * E k l * (y l - x l) =
      (x k * E k l * x l + y k * E k l * y l) - x k * E k l * y l - y k * E k l * x l := fun k l => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

end Bil2

/-! ### The condition `GoodO` against $E \perp 2B$ -/

theorem goodO1_binary_blk_iff {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (W : Matrix (Fin (e + b)) (Fin 2) ℤ) (hp : ∀ k : Fin e, 2 ∣ W (Fin.castAdd b k) 0 - W (Fin.castAdd b k) 1) :
    GoodO1 (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) (blk 2 E B) W ↔
      (if (4 : ℤ) ∣ u + v then
        (4 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
          (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
      else ((2 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 0) ↔
          (4 : ℤ) ∣ bil E (fun k => W (Fin.castAdd b k) 0) (fun k => W (Fin.castAdd b k) 0)) ∧
        (4 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
          (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)) := by
  have hMs : (blk 2 E B)ᵀ = blk 2 E B :=
    (blk_isSymm (p := 2) (show E.IsSymm from hEs) (show B.IsSymm from hBs)).eq
  have hQ : ∀ i j, (Wᵀ * blk 2 E B * W) i j =
      bil E (fun k => W (Fin.castAdd b k) i) (fun k => W (Fin.castAdd b k) j) +
        2 * bil B (fun k => W (Fin.natAdd e k) i) (fun k => W (Fin.natAdd e k) j) := by
    intro i j; rw [quad_apply, bil_blk]
  choose c hc using hp
  have hw1 : (fun k => W (Fin.castAdd b k) 1) = fun l => W (Fin.castAdd b l) 0 + 2 * (fun k => -c k) l := by
    funext k; simp only; linarith [hc k]
  obtain ⟨m, hm⟩ := bil_shift E hEs hEe (fun k => W (Fin.castAdd b k) 0) (fun k => -c k)
  obtain ⟨q', hq'⟩ := bil_even E hEs hEe (fun k => W (Fin.castAdd b k) 0)
  have h01 := bil_add_snd E (fun k => W (Fin.castAdd b k) 0) (fun k => W (Fin.castAdd b k) 0) (fun k => -c k)
  rw [← hw1] at h01 hm
  have hx01 : bil B (fun k => W (Fin.natAdd e k) 1) (fun k => W (Fin.natAdd e k) 0) =
      bil B (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 1) := bil_comm B hBs _ _
  have hQ00 := hQ 0 0
  have hQ01 := hQ 0 1
  have hQ10 : (Wᵀ * blk 2 E B * W) 1 0 = (Wᵀ * blk 2 E B * W) 0 1 :=
    congrFun (congrFun (quad_symm hMs W) 0) 1
  have hQ11 := hQ 1 1
  set q := bil E (fun k => W (Fin.castAdd b k) 0) (fun k => W (Fin.castAdd b k) 0) with hq
  set s := bil E (fun k => W (Fin.castAdd b k) 0) (fun k => -c k) with hs
  set a := bil B (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 0) with ha
  set b' := bil B (fun k => W (Fin.natAdd e k) 1) (fun k => W (Fin.natAdd e k) 1) with hb'
  set cc := bil B (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 1) with hcc
  have hqe : 2 ∣ q := ⟨q', hq'⟩
  have hSs : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W)ᵀ =
      (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W := by
    rw [transpose_add, quad_symm hMs]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hS00 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W) 0 0 = u + (q + 2 * a) := by
    simp [hQ00]
  have hS01 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W) 0 1 =
      q + 2 * s + 2 * cc := by
    simp [hQ01, h01]
  have hS10 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W) 1 0 =
      q + 2 * s + 2 * cc := by
    simp [hQ10, hQ01, h01]
  have hS11 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * blk 2 E B * W) 1 1 =
      v + (q + 4 * s + 8 * m) + 2 * b' := by
    simp [hQ11, hm]
    ring
  unfold GoodO1
  rw [zpEquiv_binary_iff hu hv hSs (by rw [hS00]; omega) (by rw [hS11]; omega) (by rw [hS01]; omega),
    Matrix.det_fin_two, hS10, hS00, hS01, hS11, key_arith2 hu hv hqe]
  have hy := bil_sub_self B hBs (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 1)
  rw [hy]

/-- **The condition `GoodO` for $O = \langle u, v\rangle$ and $M = E \perp 2B$**, $u, v$ odd, $E$ even unimodular,
$B$ symmetric: with $w_i$ the $E$-rows and $x_i$ the $B$-rows of column $i$ of $W$, $W$ is good iff
$w_0 \equiv w_1 \pmod 2$ and: if $u + v \equiv 0 \pmod 4$, $Q_B(x_1 - x_0) \equiv 0 \pmod 4$; otherwise
($2 \mid Q_B(x_0) \iff 4 \mid Q_E(w_0)$) and $Q_B(x_1 - x_0) \equiv 0 \pmod 4$. Here `bil B x x` is
$x^{\mathsf T}Bx$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem goodO_binary_blk_iff {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (W : Matrix (Fin (e + b)) (Fin 2) ℤ) :
    GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) (blk 2 E B) W ↔
      (∀ k : Fin e, 2 ∣ W (Fin.castAdd b k) 0 - W (Fin.castAdd b k) 1) ∧
      (if (4 : ℤ) ∣ u + v then
        (4 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
          (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
      else ((2 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 0) (fun k => W (Fin.natAdd e k) 0) ↔
          (4 : ℤ) ∣ bil E (fun k => W (Fin.castAdd b k) 0) (fun k => W (Fin.castAdd b k) 0)) ∧
        (4 : ℤ) ∣ bil B (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)
          (fun k => W (Fin.natAdd e k) 1 - W (Fin.natAdd e k) 0)) := by
  unfold GoodO
  constructor
  · rintro ⟨h1, h2⟩
    have hp := (evenDiag_binary_blk_iff hEs hEd hBs hu hv W).mp h2
    exact ⟨hp, (goodO1_binary_blk_iff hEs hEe hBs hu hv W hp).mp h1⟩
  · rintro ⟨hp, h⟩
    exact ⟨(goodO1_binary_blk_iff hEs hEe hBs hu hv W hp).mpr h,
      (evenDiag_binary_blk_iff hEs hEd hBs hu hv W).mpr hp⟩

/-! ### Quadratic forms of residues modulo $8$ -/

/-- The bilinear form $x^{\mathsf T}Ay$ on vectors of residues modulo $8$. -/
def bz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod (2 ^ 3)) : ZMod (2 ^ 3) :=
  ∑ k, ∑ l, x k * (A k l : ZMod (2 ^ 3)) * y l

theorem cast_val8 (x : ZMod (2 ^ 3)) : (((x.val : ℕ) : ℤ) : ZMod (2 ^ 3)) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem bil_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (X Y : Fin n → ℤ) (x y : Fin n → ZMod (2 ^ 3))
    (hx : ∀ k, (X k : ZMod (2 ^ 3)) = x k) (hy : ∀ k, (Y k : ZMod (2 ^ 3)) = y k) :
    ((bil A X Y : ℤ) : ZMod (2 ^ 3)) = bz A x y := by
  simp only [bil, bz]
  push_cast
  simp only [hx, hy]

/-- Residues $0, 2, 4, 6$ modulo $8$. -/
def Ev (z : ZMod (2 ^ 3)) : Prop := z = 0 ∨ z = 2 ∨ z = 4 ∨ z = 6

/-- Residues $0, 4$ modulo $8$. -/
def Q4 (z : ZMod (2 ^ 3)) : Prop := z = 0 ∨ z = 4

theorem dvd4_bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (X Y : Fin n → ℤ) (x y : Fin n → ZMod (2 ^ 3))
    (hx : ∀ k, (X k : ZMod (2 ^ 3)) = x k) (hy : ∀ k, (Y k : ZMod (2 ^ 3)) = y k) :
    (4 : ℤ) ∣ bil A X Y ↔ Q4 (bz A x y) := by
  rw [z4_dvd_iff, bil_cast A X Y x y hx hy]; rfl

theorem dvd2_bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (X Y : Fin n → ℤ) (x y : Fin n → ZMod (2 ^ 3))
    (hx : ∀ k, (X k : ZMod (2 ^ 3)) = x k) (hy : ∀ k, (Y k : ZMod (2 ^ 3)) = y k) :
    (2 : ℤ) ∣ bil A X Y ↔ Ev (bz A x y) := by
  rw [z2_dvd_iff, bil_cast A X Y x y hx hy]; rfl

/-- The columns of an $(e + b) \times 2$ matrix split into the four vectors $w_0, w_1, x_0, x_1$. -/
def quadEquiv (e b : ℕ) (α : Type*) : Matrix (Fin (e + b)) (Fin 2) α ≃
    (Fin e → α) × (Fin e → α) × (Fin b → α) × (Fin b → α) where
  toFun W := (fun k => W (Fin.castAdd b k) 0, fun k => W (Fin.castAdd b k) 1, fun k => W (Fin.natAdd e k) 0,
    fun k => W (Fin.natAdd e k) 1)
  invFun p := Matrix.of fun i j => Fin.addCases (motive := fun _ => α) (fun k => ![p.1 k, p.2.1 k] j)
    (fun k => ![p.2.2.1 k, p.2.2.2 k] j) i
  left_inv W := by
    ext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [Matrix.of_apply, Fin.addCases_left]; fin_cases j <;> rfl
    · simp only [Matrix.of_apply, Fin.addCases_right]; fin_cases j <;> rfl
  right_inv p := by
    simp only [Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    rfl

/-- **Counting quadruples**: the pairs $(w_0, x_0)$ with a property $Z$, the $4^e$ vectors $w_1 \equiv w_0 \pmod 2$,
and the differences $y = x_1 - x_0$ with a property $Y$ are independent. -/
theorem card_quad (e b : ℕ) (Z : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) → Prop)
    (Y : (Fin b → ZMod (2 ^ 3)) → Prop) :
    Nat.card {p : (Fin e → ZMod (2 ^ 3)) × (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
        (∀ k, (2 : ℤ) ∣ ((p.1 k).val : ℤ) - ((p.2.1 k).val : ℤ)) ∧ Z (p.1, p.2.2.1) ∧
          Y (fun k => p.2.2.2 k - p.2.2.1 k)} =
      Nat.card {r // Z r} * 4 ^ e * Nat.card {y // Y y} := by
  classical
  have hequiv : {p : (Fin e → ZMod (2 ^ 3)) × (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) ×
        (Fin b → ZMod (2 ^ 3)) //
        (∀ k, (2 : ℤ) ∣ ((p.1 k).val : ℤ) - ((p.2.1 k).val : ℤ)) ∧ Z (p.1, p.2.2.1) ∧
          Y (fun k => p.2.2.2 k - p.2.2.1 k)} ≃
      (Σ r : {r // Z r}, {w1 : Fin e → ZMod (2 ^ 3) // ∀ k, (2 : ℤ) ∣ ((r.1.1 k).val : ℤ) - ((w1 k).val : ℤ)}) ×
        {y // Y y} :=
    { toFun := fun p => (⟨⟨(p.1.1, p.1.2.2.1), p.2.2.1⟩, ⟨p.1.2.1, p.2.1⟩⟩,
        ⟨fun k => p.1.2.2.2 k - p.1.2.2.1 k, p.2.2.2⟩)
      invFun := fun s => ⟨(s.1.1.1.1, s.1.2.1, s.1.1.1.2, fun k => s.1.1.1.2 k + s.2.1 k), s.1.2.2, s.1.1.2, by
        have h : (fun k => s.1.1.1.2 k + s.2.1 k - s.1.1.1.2 k) = s.2.1 := funext fun k => by ring
        rw [h]; exact s.2.2⟩
      left_inv := fun p => by
        apply Subtype.ext
        obtain ⟨⟨w0, w1, x0, x1⟩, h⟩ := p
        simp
      right_inv := fun s => by
        obtain ⟨⟨⟨⟨w0, x0⟩, hZ⟩, ⟨w1, hP⟩⟩, ⟨y, hY⟩⟩ := s
        refine Prod.ext rfl (Subtype.ext ?_)
        funext k
        simp }
  rw [Nat.card_congr hequiv, Nat.card_prod, Nat.card_sigma,
    Finset.sum_congr rfl fun r _ => card_par e r.1.1, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul]

/-- The mixed condition on $(w_0, x_0)$: $u + v \equiv 0 \pmod 4$, or ($Q_B(x_0)$ even iff $Q_E(w_0) \equiv 0 \pmod 4$)
(as residues modulo $8$). -/
def Zp {e b : ℕ} (E : Matrix (Fin e) (Fin e) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) (h4 : Prop)
    (r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3))) : Prop :=
  h4 ∨ (Ev (bz B r.2 r.2) ↔ Q4 (bz E r.1 r.1))

theorem good_iff_quad {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (W : Matrix (Fin (e + b)) (Fin 2) (ZMod (2 ^ 3))) :
    GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) (blk 2 E B) (lift W) ↔
      (∀ k, (2 : ℤ) ∣ (((quadEquiv e b _ W).1 k).val : ℤ) - (((quadEquiv e b _ W).2.1 k).val : ℤ)) ∧
        Zp E B ((4 : ℤ) ∣ u + v) ((quadEquiv e b _ W).1, (quadEquiv e b _ W).2.2.1) ∧
        Q4 (bz B (fun k => (quadEquiv e b _ W).2.2.2 k - (quadEquiv e b _ W).2.2.1 k)
          (fun k => (quadEquiv e b _ W).2.2.2 k - (quadEquiv e b _ W).2.2.1 k)) := by
  rw [goodO_binary_blk_iff hEs hEe hEd hBs hu hv]
  have hY : (4 : ℤ) ∣ bil B (fun k => lift W (Fin.natAdd e k) 1 - lift W (Fin.natAdd e k) 0)
      (fun k => lift W (Fin.natAdd e k) 1 - lift W (Fin.natAdd e k) 0) ↔
      Q4 (bz B (fun k => (quadEquiv e b _ W).2.2.2 k - (quadEquiv e b _ W).2.2.1 k)
        (fun k => (quadEquiv e b _ W).2.2.2 k - (quadEquiv e b _ W).2.2.1 k)) := by
    refine dvd4_bil B _ _ _ _ (fun k => ?_) (fun k => ?_) <;>
    · show ((((W (Fin.natAdd e k) 1).val : ℤ) - ((W (Fin.natAdd e k) 0).val : ℤ) : ℤ) : ZMod (2 ^ 3)) = _
      rw [Int.cast_sub, cast_val8, cast_val8]; rfl
  have hX2 : (2 : ℤ) ∣ bil B (fun k => lift W (Fin.natAdd e k) 0) (fun k => lift W (Fin.natAdd e k) 0) ↔
      Ev (bz B (quadEquiv e b _ W).2.2.1 (quadEquiv e b _ W).2.2.1) :=
    dvd2_bil B _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _)
  have hX4 : (4 : ℤ) ∣ bil E (fun k => lift W (Fin.castAdd b k) 0) (fun k => lift W (Fin.castAdd b k) 0) ↔
      Q4 (bz E (quadEquiv e b _ W).1 (quadEquiv e b _ W).1) :=
    dvd4_bil E _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _)
  refine and_congr Iff.rfl ?_
  by_cases h4 : (4 : ℤ) ∣ u + v
  · simp only [h4, ↓reduceIte, Zp, true_or, true_and]
    exact hY
  · simp only [h4, ↓reduceIte, Zp, false_or]
    exact and_congr (iff_congr hX2 hX4) hY

/-- **The number of good $W$ modulo $8$**: `#{(w₀, x₀) : Z} · 4^e · #{y : Q_B(y) ≡ 0 (4)}`. -/
theorem card_goodO_binary_blk {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    Nat.card {W : Matrix (Fin (e + b)) (Fin 2) (ZMod (2 ^ 3)) //
        GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) (blk 2 E B) (lift W)} =
      Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) // Zp E B ((4 : ℤ) ∣ u + v) r} * 4 ^ e *
        Nat.card {y : Fin b → ZMod (2 ^ 3) // Q4 (bz B y y)} := by
  rw [← card_quad e b (Zp E B ((4 : ℤ) ∣ u + v)) (fun y => Q4 (bz B y y))]
  exact Nat.card_congr ((quadEquiv e b (ZMod (2 ^ 3))).subtypeEquiv fun W =>
    good_iff_quad hEs hEe hEd hBs hu hv W)

/-! ### The proportions -/

theorem card_fun8 (n : ℕ) : Nat.card (Fin n → ZMod (2 ^ 3)) = 8 ^ n := by
  rw [Nat.card_eq_fintype_card]; simp [ZMod.card]

/-- **The proportion $C$**: the proportion of $(w, x) \in (\mathbb Z/8)^e \times (\mathbb Z/8)^b$ with
$2 \mid Q_B(x) \iff 4 \mid Q_E(w)$. -/
noncomputable def cBE {e b : ℕ} (E : Matrix (Fin e) (Fin e) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) : ℝ :=
  (Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
    ((2 : ℤ) ∣ bil B (fun k => ((r.2 k).val : ℤ)) (fun k => ((r.2 k).val : ℤ)) ↔
      (4 : ℤ) ∣ bil E (fun k => ((r.1 k).val : ℤ)) (fun k => ((r.1 k).val : ℤ)))} : ℝ) / 8 ^ (e + b)

theorem card_Q4_eq_pB {b : ℕ} (B : Matrix (Fin b) (Fin b) ℤ) :
    Nat.card {y : Fin b → ZMod (2 ^ 3) // Q4 (bz B y y)} =
      Nat.card {z : Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift z)ᵀ * B * lift z) 0 0} :=
  (Nat.card_congr ((colEquiv b (ZMod (2 ^ 3))).subtypeEquiv fun z => by
    rw [quad1_apply]
    exact dvd4_bil B _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _))).symm

/-- **$\rho_O(E \perp 2B)$ for $O = \langle u, v\rangle$**: $\rho_O(M) = 2^{-e}\,p_B\,(1 \text{ if } u + v \equiv 0
\pmod 4 \text{, else } C)$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem rhoO_binary_blk {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    rhoO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) (blk 2 E B) =
      (1 / 2 : ℝ) ^ e * pB B * (if (4 : ℤ) ∣ u + v then 1 else cBE E B) := by
  unfold rhoO
  rw [card_goodO_binary_blk hEs hEe hEd hBs hu hv, card_Q4_eq_pB]
  unfold pB cBE
  set NY := Nat.card {z : Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift z)ᵀ * B * lift z) 0 0}
  have h8 : (8 : ℝ) ^ e = 2 ^ e * 4 ^ e := by rw [← mul_pow]; norm_num
  by_cases h4 : (4 : ℤ) ∣ u + v
  · have hN : Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
        Zp E B ((4 : ℤ) ∣ u + v) r} = 8 ^ e * 8 ^ b := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (p := Zp E B ((4 : ℤ) ∣ u + v)) fun r => Or.inl h4),
        Nat.card_prod, card_fun8, card_fun8]
    rw [hN]
    simp only [h4, ↓reduceIte]
    push_cast
    rw [pow_mul, pow_add, h8, one_div, inv_pow]
    field_simp
  · have hN : Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
        Zp E B ((4 : ℤ) ∣ u + v) r} = Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
        ((2 : ℤ) ∣ bil B (fun k => ((r.2 k).val : ℤ)) (fun k => ((r.2 k).val : ℤ)) ↔
      (4 : ℤ) ∣ bil E (fun k => ((r.1 k).val : ℤ)) (fun k => ((r.1 k).val : ℤ)))} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
      simp only [Zp, h4, false_or]
      exact (iff_congr (dvd2_bil B _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _))
        (dvd4_bil E _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _))).symm
    rw [hN]
    simp only [h4, ↓reduceIte]
    push_cast
    rw [pow_mul, pow_add, h8, one_div, inv_pow]
    field_simp

/-- **$\rho_O(E \perp 2B)$ for the model $O$ = `intMat [sq 0 u, sq 0 v]`.** -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem rhoO_binary_blk_intMat {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    rhoO (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) (blk 2 E B) =
      (1 / 2 : ℝ) ^ e * pB B * (if (4 : ℤ) ∣ u + v then 1 else cBE E B) :=
  (congrArg (fun O => rhoO O (blk 2 E B)) (intMat_sq_sq u v)).trans (rhoO_binary_blk hEs hEe hEd hBs hu hv)

/-- **$C$ when every diagonal entry of $B$ is even**: $C$ is the proportion of $w \in (\mathbb Z/8)^e$ with
$Q_E(w) \equiv 0 \pmod 4$. -/
theorem cBE_of_evenDiag {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hBs : Bᵀ = B) (hBe : EvenDiag B) :
    cBE E B = (Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) //
      (4 : ℤ) ∣ ((lift x)ᵀ * E * lift x) 0 0} : ℝ) / 8 ^ e := by
  unfold cBE
  have h1 : Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      ((2 : ℤ) ∣ bil B (fun k => ((r.2 k).val : ℤ)) (fun k => ((r.2 k).val : ℤ)) ↔
        (4 : ℤ) ∣ bil E (fun k => ((r.1 k).val : ℤ)) (fun k => ((r.1 k).val : ℤ)))} =
      Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift x)ᵀ * E * lift x) 0 0} * 8 ^ b := by
    have hq : ∀ r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)),
        (2 : ℤ) ∣ bil B (fun k => ((r.2 k).val : ℤ)) (fun k => ((r.2 k).val : ℤ)) := fun r => by
      obtain ⟨m, hm⟩ := bil_even B hBs hBe (fun k => ((r.2 k).val : ℤ))
      exact ⟨m, hm⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) =>
        (4 : ℤ) ∣ bil E (fun k => ((r.1 k).val : ℤ)) (fun k => ((r.1 k).val : ℤ))) fun r => by
          simp only [hq r, true_iff]),
      Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun w : Fin e → ZMod (2 ^ 3) =>
        (4 : ℤ) ∣ bil E (fun k => ((w k).val : ℤ)) (fun k => ((w k).val : ℤ)))),
      Nat.card_prod, card_fun8, ← card_Q4_eq_pB E]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
      dvd4_bil E _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _))
  rw [h1]
  push_cast
  rw [pow_add]
  field_simp

/-! ### $C = 1/2$ when $B$ has an odd diagonal entry -/

theorem fact_flip : ∀ z t β : ZMod (2 ^ 3), (β = 1 ∨ β = 3 ∨ β = 5 ∨ β = 7) →
    (Ev (z + 2 * t + β) ↔ ¬ Ev z) := by
  unfold Ev
  decide +kernel

theorem bz_add_single {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) (x : Fin b → ZMod (2 ^ 3))
    (k : Fin b) :
    ∃ t : ZMod (2 ^ 3), bz B (x + Pi.single k 1) (x + Pi.single k 1) = bz B x x + 2 * t + (B k k : ZMod (2 ^ 3)) := by
  classical
  have hsym : ∀ j, (B j k : ZMod (2 ^ 3)) = (B k j : ZMod (2 ^ 3)) := fun j => by
    have h : B j k = B k j := congrFun (congrFun hBs k) j
    rw [h]
  refine ⟨∑ l, (B k l : ZMod (2 ^ 3)) * x l, ?_⟩
  have e1 : (∑ i : Fin b, ∑ j : Fin b, if i = k then (B i j : ZMod (2 ^ 3)) * x j else 0) =
      ∑ j, (B k j : ZMod (2 ^ 3)) * x j := by
    rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
    simp
  simp only [bz, Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsym]
  rw [e1]
  simp only [mul_comm]
  ring

theorem Ev_flip {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {k : Fin b} (hk : ¬ 2 ∣ B k k)
    (x : Fin b → ZMod (2 ^ 3)) :
    Ev (bz B (x + Pi.single k 1) (x + Pi.single k 1)) ↔ ¬ Ev (bz B x x) := by
  obtain ⟨t, ht⟩ := bz_add_single hBs x k
  rw [ht]
  exact fact_flip _ _ _ (z_odd_cases hk)

theorem card_Ev_flip {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {k : Fin b} (hk : ¬ 2 ∣ B k k) :
    Nat.card {x : Fin b → ZMod (2 ^ 3) // ¬ Ev (bz B x x)} = Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)} := by
  classical
  refine Nat.card_congr (((Equiv.addRight (Pi.single k 1 : Fin b → ZMod (2 ^ 3))).subtypeEquiv
    (p := fun x => ¬ Ev (bz B x x)) (q := fun x => Ev (bz B x x)) fun x => ?_))
  rw [Equiv.coe_addRight, Ev_flip hBs hk]

theorem card_cond_odd {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B)
    {k : Fin b} (hk : ¬ 2 ∣ B k k) :
    2 * Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      (Ev (bz B r.2 r.2) ↔ Q4 (bz E r.1 r.1))} = 8 ^ e * 8 ^ b := by
  classical
  have hflip := card_Ev_flip hBs hk
  have hsum : Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)} +
      Nat.card {x : Fin b → ZMod (2 ^ 3) // ¬ Ev (bz B x x)} = 8 ^ b := by
    have := Nat.card_congr (Equiv.sumCompl (fun x : Fin b → ZMod (2 ^ 3) => Ev (bz B x x)))
    rw [Nat.card_sum, card_fun8] at this
    exact this
  have hcard : Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      (Ev (bz B r.2 r.2) ↔ Q4 (bz E r.1 r.1))} =
      8 ^ e * Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (w : Fin e → ZMod (2 ^ 3))
      (x : Fin b → ZMod (2 ^ 3)) => (Ev (bz B x x) ↔ Q4 (bz E w w)))), Nat.card_sigma]
    have hf : ∀ w : Fin e → ZMod (2 ^ 3), Nat.card {x : Fin b → ZMod (2 ^ 3) //
        (Ev (bz B x x) ↔ Q4 (bz E w w))} = Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)} := by
      intro w
      by_cases h : Q4 (bz E w w)
      · exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [h, iff_true])
      · rw [← hflip]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [h, iff_false])
    rw [Finset.sum_congr rfl fun w _ => hf w, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      card_fun8, smul_eq_mul]
  rw [hcard]
  have : 2 * Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)} = 8 ^ b := by omega
  calc 2 * (8 ^ e * Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)})
      = 8 ^ e * (2 * Nat.card {x : Fin b → ZMod (2 ^ 3) // Ev (bz B x x)}) := by ring
    _ = 8 ^ e * 8 ^ b := by rw [this]

/-- **$C = 1/2$ when some diagonal entry of $B$ is odd.** -/
theorem cBE_of_odd {e b : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hBs : Bᵀ = B) (hk : ∃ k, ¬ 2 ∣ B k k) : cBE E B = 1 / 2 := by
  obtain ⟨k, hk⟩ := hk
  unfold cBE
  have hnum : Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      ((2 : ℤ) ∣ bil B (fun k => ((r.2 k).val : ℤ)) (fun k => ((r.2 k).val : ℤ)) ↔
        (4 : ℤ) ∣ bil E (fun k => ((r.1 k).val : ℤ)) (fun k => ((r.1 k).val : ℤ)))} =
      Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      (Ev (bz B r.2 r.2) ↔ Q4 (bz E r.1 r.1))} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun r =>
      iff_congr (dvd2_bil B _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _))
        (dvd4_bil E _ _ _ _ (fun k => cast_val8 _) (fun k => cast_val8 _)))
  have h2 := card_cond_odd (E := E) hBs hk
  rw [hnum]
  have h2' : (2 : ℝ) * (Nat.card {r : (Fin e → ZMod (2 ^ 3)) × (Fin b → ZMod (2 ^ 3)) //
      (Ev (bz B r.2 r.2) ↔ Q4 (bz E r.1 r.1))} : ℝ) = 8 ^ e * 8 ^ b := by exact_mod_cast h2
  rw [pow_add]
  have h0 : (0 : ℝ) < 8 ^ e * 8 ^ b := by positivity
  field_simp
  linarith

end QuadFormsKB.ConwaySloane.Mass.Two
