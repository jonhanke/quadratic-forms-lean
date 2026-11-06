/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Hasse

/-!
# Paper 7 at odd primes: Hanke's local density of the genus of a tuple

For $v \nmid 2$ ($p = p_v$) and a Jordan tuple $(a, b; u_1, u_2, u_3)$ of Lemma 2.1, the Gram matrix of the form
$u_1x^2 + p^au_2y^2 + p^bu_3z^2$ is the integer diagonal matrix $A = \operatorname{diag}(u_1, p^au_2, p^bu_3)$
(`tupleMat`). This file proves:

* `beta_tupG`: $\beta_{G,v}(G) = \tfrac12\alpha_p(A)$ (`ConwaySloane.Mass.hankeBeta_eq_half_alphaP`);
* `isOddSymbolOf_tuple`: the $p$-adic symbol of $A$ is `symT a b u₁ u₂ u₃`;
* `pMass_tuple`: $m_p(A) = $ `pMassOdd` of that symbol (Conway–Sloane's formula (3), proved at odd $p$:
  `ConwaySloane.Mass.pMassFormulaOdd`);
* `invBeta_tupG`: $(1 - p^{-2})/\beta_{G,v}(G) = 2(1 - p^{-2})\,m_p(\sigma)/p^{2(a+b)}$.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

/-- The integer Gram matrix $\operatorname{diag}(u_1, p^au_2, p^bu_3)$ of the tuple form. -/
def tupleMat (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.diagonal (tupleVec p c a b e₁ e₂ e₃)

theorem det_tupleMat (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupleMat p c a b e₁ e₂ e₃).det = (p : ℤ) ^ (a + b) * (rep c e₁ * rep c e₂ * rep c e₃) := by
  unfold tupleMat
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [tupleVec_zero, tupleVec_one, tupleVec_two]
  ring

section AtV

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem not_dvd_rep3 {c : ℤ} (hc : jacobiSym c (pv v) = -1) (e₁ e₂ e₃ : ℤˣ) :
    ¬ (pv v : ℤ) ∣ rep c e₁ * rep c e₂ * rep c e₃ := by
  have hpp := Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)
  intro h
  rcases hpp.dvd_or_dvd h with h | h
  · rcases hpp.dvd_or_dvd h with h | h
    · exact not_dvd_rep hc e₁ h
    · exact not_dvd_rep hc e₂ h
  · exact not_dvd_rep hc e₃ h

theorem tupleMat_det_ne {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupleMat (pv v) c a b e₁ e₂ e₃).det ≠ 0 := by
  rw [det_tupleMat]
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : rep c e₁ * rep c e₂ * rep c e₃ ≠ 0 := fun h => not_dvd_rep3 hc e₁ e₂ e₃ (h ▸ dvd_zero _)
  exact mul_ne_zero (pow_ne_zero _ hpz) hu

theorem tupleMat_symm (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : (tupleMat p c a b e₁ e₂ e₃).IsSymm :=
  Matrix.isSymm_diagonal _

theorem padicVal_tupleMat {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    padicValInt (pv v) (tupleMat (pv v) c a b e₁ e₂ e₃).det = a + b := by
  rw [det_tupleMat]
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : rep c e₁ * rep c e₂ * rep c e₃ ≠ 0 := fun h => not_dvd_rep3 hc e₁ e₂ e₃ (h ▸ dvd_zero _)
  rw [padicValInt.mul (pow_ne_zero _ hpz) hu, padicValInt.eq_zero_of_not_dvd (not_dvd_rep3 hc e₁ e₂ e₃),
    add_zero]
  have : (((pv v : ℕ) : ℤ) ^ (a + b)) = (((pv v) ^ (a + b) : ℕ) : ℤ) := (Nat.cast_pow (pv v) (a + b)).symm
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- **$\beta_{G,v}(G) = \tfrac12\alpha_p(A)$** for the genus of a tuple, $A$ = `tupleMat`. -/
theorem beta_tupG {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupG v c a b e₁ e₂ e₃).beta = (1 / 2 : ℝ) * alphaP (pv v) (tupleMat (pv v) c a b e₁ e₂ e₃) := by
  unfold tupG
  rw [LocGenus.beta_mk]
  unfold betaForm
  have hG : Hanke2005.gramOf v ((tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬)) =
      ((tupleMat (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬)).map (algebraMap 𝔬 Fv) := by
    unfold Hanke2005.gramOf tupleForm tupleMat
    rw [map_diag_eq, hessian_diag_gen]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hij
    · simp only [map_mul, map_ofNat]
      field_simp
    · simp
  rw [hG]
  exact hankeBeta_eq_half_alphaP v (tupleMat_symm _ _ _ _ _ _ _) (tupleMat_det_ne hc a b e₁ e₂ e₃)

theorem alphaP_eq_div {p : ℕ} (hp : p.Prime) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) :
    alphaP p A = (p : ℝ) ^ (((padicValInt p A.det : ℝ) * ((n : ℝ) + 1)) / 2) / pMassDensity p A := by
  have hα := (alphaP_pos hp hA hdet).ne'
  unfold pMassDensity
  have h2 : (p : ℝ) ^ (((padicValInt p A.det : ℝ) * ((n : ℝ) + 1)) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.2 hp.pos) _).ne'
  field_simp

/-- **The $p$-adic symbol of the Gram matrix of a tuple** is `symT a b u₁ u₂ u₃` (the multiplicities
$[0=k]+[a=k]+[b=k]$ and the characters of the entries of exponent $k$). -/
theorem isOddSymbolOf_tuple (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ)
    (e₁ e₂ e₃ : ℤˣ) :
    IsOddSymbolOf (pv v) ((tupleMat (pv v) c a b e₁ e₂ e₃).map (Int.cast : ℤ → ℚ_[pv v]))
      (symT a b e₁ e₂ e₃) := by
  have k : (fun i => chiU (![repU hc e₁, repU hc e₂, repU hc e₃] i)) = ![e₁, e₂, e₃] := by
    funext i; fin_cases i <;> simp [chiU_repU]
  refine ⟨![0, a, b], fun i => (((![repU hc e₁, repU hc e₂, repU hc e₃] i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]),
    fun i => ?_, ?_, ?_⟩
  · show ‖(((![repU hc e₁, repU hc e₂, repU hc e₃] i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])‖ = 1
    rw [PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.1 (![repU hc e₁, repU hc e₂, repU hc e₃] i).isUnit
  · have : (tupleMat (pv v) c a b e₁ e₂ e₃).map (Int.cast : ℤ → ℚ_[pv v]) =
        Matrix.diagonal (fun i => ((pv v : ℕ) : ℚ_[pv v]) ^ (![0, a, b] : Fin 3 → ℕ) i *
          (((![repU hc e₁, repU hc e₂, repU hc e₃] i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])) := by
      unfold tupleMat
      rw [Matrix.diagonal_map (Int.cast_zero)]
      congr 1
      funext i
      fin_cases i <;> simp [tupleVec, repU_val]
    rw [this]
    exact ZpEquiv.refl _
  · rw [oddSymbolOfDiag_eq_symC hp2, k, symC_three]

theorem symT_trivial {a b : ℕ} (hab : a ≤ b) (x y z : ℤˣ) :
    ∀ k, b + 1 ≤ k → symT a b x y z k = OddFactor.trivial := by
  intro k hk
  have h0 : (0 : ℕ) ≠ k := by omega
  have h1 : a ≠ k := by omega
  have h2 : b ≠ k := by omega
  simp [symT, OddFactor.trivial, h0, h1, h2]

/-- **Conway–Sloane's formula (3) for the Gram matrix of a tuple:** $m_p(A) = $ `pMassOdd` of its symbol. -/
theorem pMass_tuple (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {a b : ℕ} (hab : a ≤ b)
    (e₁ e₂ e₃ : ℤˣ) :
    pMassDensity (pv v) (tupleMat (pv v) c a b e₁ e₂ e₃) = pMassOdd (pv v) (symT a b e₁ e₂ e₃) (b + 1) :=
  (pMassFormulaOdd hp2).pMass_eq _ (tupleMat_symm _ _ _ _ _ _ _) (tupleMat_det_ne hc a b e₁ e₂ e₃) _ (b + 1)
    (isOddSymbolOf_tuple hp2 hc a b e₁ e₂ e₃) (symT_trivial hab e₁ e₂ e₃)

theorem pMassOdd_pos' (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {a b : ℕ} (hab : a ≤ b)
    (e₁ e₂ e₃ : ℤˣ) : pMassOdd (pv v) (symT a b e₁ e₂ e₃) (b + 1) ≠ 0 := by
  rw [← pMass_tuple hp2 hc hab]
  unfold pMassDensity
  have hα := (alphaP_pos (Fact.out : (pv v).Prime) (tupleMat_symm (pv v) c a b e₁ e₂ e₃)
    (tupleMat_det_ne hc a b e₁ e₂ e₃))
  have : (0 : ℝ) < ((pv v : ℕ) : ℝ) ^ (((padicValInt (pv v) (tupleMat (pv v) c a b e₁ e₂ e₃).det : ℝ) *
      (((3 : ℕ) : ℝ) + 1)) / 2) := Real.rpow_pos_of_pos (Nat.cast_pos.2 (Fact.out : (pv v).Prime).pos) _
  exact (div_pos this hα).ne'

/-- **$(1 - p^{-2})/\beta_{G,v}(G)$ for the genus of a tuple** (Jordan tuple, $a \le b$):
$$\frac{1 - p^{-2}}{\beta_{G,v}(G)} = \frac{2(1 - p^{-2})\,m_p(\sigma)}{p^{2(a+b)}},$$
$m_p(\sigma)$ = `pMassOdd` of the symbol `symT a b u₁ u₂ u₃`. -/
theorem invBeta_tupG (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {a b : ℕ} (hab : a ≤ b)
    (e₁ e₂ e₃ : ℤˣ) :
    (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / (tupG v c a b e₁ e₂ e₃).beta =
      2 * (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) * pMassOdd (pv v) (symT a b e₁ e₂ e₃) (b + 1) /
        ((pv v : ℕ) : ℝ) ^ (2 * (a + b)) := by
  have hpr := (Fact.out : (pv v).Prime)
  have hm := pMassOdd_pos' hp2 hc hab e₁ e₂ e₃
  rw [beta_tupG hc, alphaP_eq_div hpr (tupleMat_symm _ _ _ _ _ _ _) (tupleMat_det_ne hc a b e₁ e₂ e₃),
    pMass_tuple hp2 hc hab, padicVal_tupleMat hc]
  have e : (((a + b : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 1)) / 2 = ((2 * (a + b) : ℕ) : ℝ) := by
    push_cast; ring
  rw [e, Real.rpow_natCast]
  have hp0 : (0 : ℝ) < ((pv v : ℕ) : ℝ) := Nat.cast_pos.2 hpr.pos
  have hpw : (0 : ℝ) < ((pv v : ℕ) : ℝ) ^ (2 * (a + b)) := pow_pos hp0 _
  field_simp

end AtV

end

end QuadFormsKB.Odd7
