/-
# Kitaoka 1993, Corollary 3.5.3: the anisotropic quaternary space over $\mathbb Q_p$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §3.5, Corollary 3.5.3, p. 63.

**Statement** (`corollary353`). Let $p$ be a prime. There is a unit $\delta \in \mathbb Z_p^\times$ with Hilbert
symbols $(p, \delta)_p = -1$ and $(\delta, u)_p = 1$ for every $u \in \mathbb Z_p^\times$, such that the diagonal
quaternary space $\langle 1, -\delta, p, -\delta p\rangle$ (coefficients $a_0, a_1, a_2, a_3$, 0-based) is
anisotropic over $\mathbb Q_p$, and every regular (nondegenerate) anisotropic quaternary quadratic space $U$ over
$\mathbb Q_p$ is isometric to it. In particular (`invariants_of_not_isotropic`) every such $U$ has determinant a
square, $dU = 1$ modulo squares, and Hasse invariant $\prod_{i<j}(a_i, a_j)_p = -(-1,-1)_p$.

**Proof.**
1. *Existence of $\delta$* (`exists_delta`). For $p$ odd take a unit whose residue is a nonsquare modulo $p$; for
   $p = 2$ take $\delta = 5$. Both Hilbert symbol conditions follow from the explicit formulas
   `HilbertLocal.hilbertSymbol_odd_formula` and `HilbertLocal.hilbertSymbol_two_formula`.
2. *Anisotropy criterion* (`not_isotropic_four_iff`). A diagonal form $\langle g_0, g_1, g_2, g_3\rangle$ is
   isotropic iff $\langle g_0, g_1\rangle$ and $\langle -g_2, -g_3\rangle$ represent a common $x \ne 0$
   (`PadicClass.isotropic_four_iff_common`), i.e. $(x, -g_0 g_1) = (g_0, g_1)$ and $(x, -g_2 g_3) = (-g_2, -g_3)$
   (`PadicClass.represents_two_iff`). By the prescription of two Hilbert symbols
   (`PadicClass.LocalHilbertField.exists_hs_eq_iff`) such an $x$ exists unless $g_0 g_1 g_2 g_3$ is a square and
   $(g_0, g_1) \ne (-g_2, -g_3)$. Hence the form is anisotropic iff both hold.
3. *Invariants* (`invariants_of_not_isotropic`). If $g_0 g_1 g_2 g_3 = s^2$ and $(g_0, g_1) = -(-g_2, -g_3)$, then
   expanding by bimultiplicativity, the Hasse invariant equals $-(-1,-1)$.
4. *The diagonal form is anisotropic* (`diag_not_isotropic`): its determinant is $(\delta p)^2$, $(1, -\delta) = 1$
   and $(-p, \delta p) = (-1, \delta)(p, \delta)(-p, p) = -1$.
5. *Uniqueness*: diagonalize $U$ (Mathlib `equivalent_weightedSumSquares_units_of_nondegenerate'`); by step 3 the two
   diagonal forms have equal dimension, determinant square class and Hasse invariant, hence are isometric by
   the classification `PadicClass.isometric_iff_invariants` (Serre IV §2.3, Thm. 7).

**Repository results used.** `PadicClass.localHilbertField_padic`, `PadicClass.isotropic_four_iff_common`,
`PadicClass.represents_two_iff`, `PadicClass.hs_eq_one_of_isSquare_neg_mul`,
`PadicClass.LocalHilbertField.exists_hs_eq_iff`, `PadicClass.isometric_iff_invariants`, `PadicClass.hasseVec`
(`PadicClassification.lean`); `HilbertLocal.hilbertSymbol_odd_formula`, `HilbertLocal.hilbertSymbol_two_formula`;
`Cor354.wss_equiv_iff` (`Ch3Corollary354.lean`).

The result is unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch3Corollary354
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

open QuadraticMap QuadFormsKB QuadFormsKB.QuadForm QuadFormsKB.PadicClass

noncomputable section
namespace QuadFormsKB.Kitaoka
namespace Cor353

variable (p : ℕ) [Fact p.Prime]

/-- A weighted sum of squares is anisotropic iff the diagonal `QuadForm` is not isotropic. -/
theorem wss_anisotropic_iff {n : ℕ} (a : Fin n → ℚ_[p]) :
    (weightedSumSquares ℚ_[p] a).Anisotropic ↔ ¬ (diag a).IsotropicIn ℚ_[p] := by
  have hev : ∀ y : Fin n → ℚ_[p], weightedSumSquares ℚ_[p] a y = ∑ i, a i * y i ^ 2 := by
    intro y
    rw [weightedSumSquares_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [_root_.sq, smul_eq_mul]
  rw [isotropicIn_diag_iff]
  constructor
  · rintro h ⟨y, hy, hy0⟩
    exact hy (h y (by rw [hev]; exact hy0))
  · intro h y hy
    by_contra hne
    exact h ⟨y, hne, by rw [← hev]; exact hy⟩

/-- Anisotropy criterion for quaternary diagonal forms over $\mathbb Q_p$: $\langle g_0, g_1, g_2, g_3\rangle$ is
anisotropic iff $g_0 g_1 g_2 g_3$ is a square and $(g_0, g_1)_p \ne (-g_2, -g_3)_p$. -/
theorem not_isotropic_four_iff {g₀ g₁ g₂ g₃ : ℚ_[p]} (h₀ : g₀ ≠ 0) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0)
    (h₃ : g₃ ≠ 0) :
    ¬ (diag ![g₀, g₁, g₂, g₃]).IsotropicIn ℚ_[p] ↔
      IsSquare (g₀ * g₁ * g₂ * g₃) ∧
        hilbertSymbol ℚ_[p] g₀ g₁ ≠ hilbertSymbol ℚ_[p] (-g₂) (-g₃) := by
  have hK := localHilbertField_padic p
  have hA : -(g₀ * g₁) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h₀ h₁)
  have hB : -(g₂ * g₃) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h₂ h₃)
  have eB : -(-g₂ * -g₃) = -(g₂ * g₃) := by ring
  have hcommon : (diag ![g₀, g₁, g₂, g₃]).IsotropicIn ℚ_[p] ↔
      ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSymbol ℚ_[p] x (-(g₀ * g₁)) = hilbertSymbol ℚ_[p] g₀ g₁ ∧
        hilbertSymbol ℚ_[p] x (-(g₂ * g₃)) = hilbertSymbol ℚ_[p] (-g₂) (-g₃) := by
    rw [isotropic_four_iff_common h₀ h₁ h₂ h₃]
    refine exists_congr fun x => and_congr_right fun hx => ?_
    rw [represents_two_iff hK h₀ h₁ hx,
      represents_two_iff hK (neg_ne_zero.mpr h₂) (neg_ne_zero.mpr h₃) hx, eB]
  rw [hcommon, hK.exists_hs_eq_iff hA hB (hs_pm _ _) (hs_pm _ _)]
  have C1 : IsSquare (-(g₀ * g₁)) → hilbertSymbol ℚ_[p] g₀ g₁ = 1 :=
    hs_eq_one_of_isSquare_neg_mul hK h₀ h₁
  have C2 : IsSquare (-(g₂ * g₃)) → hilbertSymbol ℚ_[p] (-g₂) (-g₃) = 1 := fun h =>
    hs_eq_one_of_isSquare_neg_mul hK (neg_ne_zero.mpr h₂) (neg_ne_zero.mpr h₃) (by rwa [eB])
  have eAB : -(g₀ * g₁) * -(g₂ * g₃) = g₀ * g₁ * g₂ * g₃ := by ring
  rw [eAB]
  tauto

theorem hasseVec_four (g₀ g₁ g₂ g₃ : ℚ_[p]) :
    hasseVec ![g₀, g₁, g₂, g₃] =
      hilbertSymbol ℚ_[p] g₀ g₁ * hilbertSymbol ℚ_[p] g₀ g₂ * hilbertSymbol ℚ_[p] g₀ g₃ *
        hilbertSymbol ℚ_[p] g₁ g₂ * hilbertSymbol ℚ_[p] g₁ g₃ * hilbertSymbol ℚ_[p] g₂ g₃ := by
  simp [hasseVec, Fin.prod_univ_four]
  left; ring

theorem pm_aux (ε a c e f b : ℤ) (ha : a = 1 ∨ a = -1) (hc : c = 1 ∨ c = -1) (he : e = 1 ∨ e = -1)
    (hf : f = 1 ∨ f = -1) (hb : b = 1 ∨ b = -1) (hne : a ≠ b) (hε : ε = a * e * c)
    (hβ : b = f * e * c) : ε = -f := by
  subst hε
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> rcases he with rfl | rfl <;>
    rcases hf with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- **Invariants of an anisotropic quaternary diagonal form over $\mathbb Q_p$**: the determinant is a nonzero
square and the Hasse invariant is $-(-1,-1)_p$ (Kitaoka, Cor. 3.5.3, "in particular"). -/
theorem invariants_of_not_isotropic {g₀ g₁ g₂ g₃ : ℚ_[p]} (h₀ : g₀ ≠ 0) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0)
    (h₃ : g₃ ≠ 0) (hna : ¬ (diag ![g₀, g₁, g₂, g₃]).IsotropicIn ℚ_[p]) :
    (∃ s : ℚ_[p], s ≠ 0 ∧ g₀ * g₁ * g₂ * g₃ = s ^ 2) ∧
      hasseVec ![g₀, g₁, g₂, g₃] = -hilbertSymbol ℚ_[p] (-1) (-1) := by
  have hK := localHilbertField_padic p
  obtain ⟨⟨s, hs⟩, hne⟩ := (not_isotropic_four_iff p h₀ h₁ h₂ h₃).mp hna
  have hprod : g₀ * g₁ * g₂ * g₃ ≠ 0 := by simp [h₀, h₁, h₂, h₃]
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hprod; rw [hs]; ring
  refine ⟨⟨s, hs0, by rw [hs]; ring⟩, ?_⟩
  have hm : g₀ * g₁ ≠ 0 := mul_ne_zero h₀ h₁
  have hn : g₂ * g₃ ≠ 0 := mul_ne_zero h₂ h₃
  have hc : s / (g₀ * g₁) ≠ 0 := div_ne_zero hs0 hm
  have hmn : g₂ * g₃ = (s / (g₀ * g₁)) ^ 2 * (g₀ * g₁) := by
    field_simp
    linear_combination hs
  -- Hasse invariant in terms of the symbol of the products
  have hε : hasseVec ![g₀, g₁, g₂, g₃] =
      hilbertSymbol ℚ_[p] g₀ g₁ * hilbertSymbol ℚ_[p] (g₀ * g₁) (g₂ * g₃) *
        hilbertSymbol ℚ_[p] g₂ g₃ := by
    rw [hasseVec_four, hK.mul_left _ _ _ h₀ h₁ hn, hK.mul_right h₀ h₂ h₃, hK.mul_right h₁ h₂ h₃]
    ring
  have hmm : hilbertSymbol ℚ_[p] (g₀ * g₁) (g₂ * g₃) = hilbertSymbol ℚ_[p] (-1) (g₀ * g₁) := by
    rw [hmn, hs_sq_right _ _ _ hc, hK.self hm, hilbertSymbol_comm]
  have hne1 : hilbertSymbol ℚ_[p] (-1) (g₂ * g₃) = hilbertSymbol ℚ_[p] (-1) (g₀ * g₁) := by
    rw [hmn, hs_sq_right _ _ _ hc]
  have hneg1 : (-1 : ℚ_[p]) ≠ 0 := by norm_num
  have hβ : hilbertSymbol ℚ_[p] (-g₂) (-g₃) =
      hilbertSymbol ℚ_[p] (-1) (-1) * hilbertSymbol ℚ_[p] (-1) (g₂ * g₃) *
        hilbertSymbol ℚ_[p] g₂ g₃ := by
    have e2 : -g₂ = -1 * g₂ := by ring
    have e3 : -g₃ = -1 * g₃ := by ring
    rw [e2, hK.mul_left _ _ _ hneg1 h₂ (by simpa using h₃), e3,
      hK.mul_right hneg1 hneg1 h₃, hK.mul_right h₂ hneg1 h₃, hK.mul_right hneg1 h₂ h₃,
      hilbertSymbol_comm ℚ_[p] g₂ (-1)]
    ring
  rw [hmm] at hε
  rw [hne1] at hβ
  exact pm_aux _ _ _ _ _ _ (hs_pm _ _) (hs_pm _ _) (hs_pm _ _) (hs_pm _ _) (hs_pm _ _) hne hε hβ

/-- **Existence of $\delta$**: a unit $\delta \in \mathbb Z_p^\times$ with $(p, \delta)_p = -1$ and
$(\delta, u)_p = 1$ for all units $u$ ($\delta = 5$ for $p = 2$, a nonsquare-residue unit for $p$ odd). -/
theorem exists_delta : ∃ δ : ℤ_[p], IsUnit δ ∧
    hilbertSymbol ℚ_[p] (p : ℚ_[p]) ((δ : ℤ_[p]) : ℚ_[p]) = -1 ∧
    ∀ u : ℤ_[p], IsUnit u → hilbertSymbol ℚ_[p] ((δ : ℤ_[p]) : ℚ_[p]) ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have hunit5 : IsUnit ((5 : ℕ) : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; norm_num
    have h5 : PadicInt.toZModPow 3 ((hunit5.unit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
      rw [IsUnit.unit_spec, map_natCast]; rfl
    have h2 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
    have hε : HilbertLocal.twoEps (5 : ZMod (2 ^ 3)) = 0 := by decide
    have hω : HilbertLocal.twoOmega (5 : ZMod (2 ^ 3)) = 1 := by decide
    have hε1 : HilbertLocal.twoEps (1 : ZMod (2 ^ 3)) = 0 := by decide
    refine ⟨((hunit5.unit : ℤ_[2]ˣ) : ℤ_[2]), Units.isUnit _, ?_, ?_⟩
    · have := HilbertLocal.hilbertSymbol_two_formula 1 0 1 hunit5.unit
      simp only [pow_zero, pow_one, one_mul, mul_one, Units.val_one, PadicInt.coe_one, map_one,
        zero_mul, add_zero] at this
      rw [h2, this, h5, hε, hω, hε1]; simp
    · intro u hu
      have := HilbertLocal.hilbertSymbol_two_formula 0 0 hunit5.unit hu.unit
      simp only [pow_zero, one_mul, zero_mul, add_zero] at this
      have hu' : ((hu.unit : ℤ_[2]ˣ) : ℤ_[2]) = u := hu.unit_spec
      rw [hu'] at this
      rw [this, h5, hε]; simp
  · have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨r0, hr0⟩ := FiniteField.exists_nonsquare hch
    have hr00 : r0 ≠ 0 := by rintro rfl; exact hr0 ⟨0, by simp⟩
    obtain ⟨v, hv⟩ := exists_unit_toZMod p r0 hr00
    refine ⟨(v : ℤ_[p]), v.isUnit, ?_, ?_⟩
    · have := HilbertLocal.hilbertSymbol_odd_formula hp2 1 0 1 v
      simp only [pow_zero, pow_one, one_mul, mul_one, Units.val_one, PadicInt.coe_one, zero_mul,
        mul_zero] at this
      rw [this]
      simp only [HilbertLocal.unitChar, hv]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr hr0]
    · intro u hu
      have := HilbertLocal.hilbertSymbol_units hp2 v hu.unit
      rwa [IsUnit.unit_spec] at this

/-- The diagonal form $\langle 1, -\delta, p, -\delta p\rangle$ is anisotropic when $(p, \delta)_p = -1$ and
$(\delta, u)_p = 1$ for all units $u$. -/
theorem diag_not_isotropic (δ : ℤ_[p]) (hδ : IsUnit δ)
    (h1 : hilbertSymbol ℚ_[p] (p : ℚ_[p]) ((δ : ℤ_[p]) : ℚ_[p]) = -1)
    (h2 : ∀ u : ℤ_[p], IsUnit u →
      hilbertSymbol ℚ_[p] ((δ : ℤ_[p]) : ℚ_[p]) ((u : ℤ_[p]) : ℚ_[p]) = 1) :
    ¬ (diag ![1, -((δ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]), -((δ : ℤ_[p]) : ℚ_[p]) * p]).IsotropicIn
      ℚ_[p] := by
  have hK := localHilbertField_padic p
  have hd0 : ((δ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h; exact hδ.ne_zero (PadicInt.ext (by simpa using h))
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [not_isotropic_four_iff p one_ne_zero (neg_ne_zero.mpr hd0) hp0
    (mul_ne_zero (neg_ne_zero.mpr hd0) hp0)]
  refine ⟨⟨((δ : ℤ_[p]) : ℚ_[p]) * p, by ring⟩, ?_⟩
  have hm1 : hilbertSymbol ℚ_[p] (-1) ((δ : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [hilbertSymbol_comm]
    have := h2 (-1) (by simp)
    simpa using this
  have hneg : (-(p : ℚ_[p])) ≠ 0 := neg_ne_zero.mpr hp0
  have e1 : -(-((δ : ℤ_[p]) : ℚ_[p]) * p) = ((δ : ℤ_[p]) : ℚ_[p]) * p := by ring
  have e2 : hilbertSymbol ℚ_[p] (-(p : ℚ_[p])) p = 1 := by
    have := hilbertSymbol_self_neg ℚ_[p] (-(p : ℚ_[p]))
    rwa [neg_neg] at this
  have e3 : hilbertSymbol ℚ_[p] (-(p : ℚ_[p])) ((δ : ℤ_[p]) : ℚ_[p]) = -1 := by
    rw [show -(p : ℚ_[p]) = -1 * p by ring, hK.mul_left _ _ _ (by norm_num) hp0 hd0, hm1, h1]
    norm_num
  rw [hs_one_left, e1, hK.mul_right hneg hd0 hp0, e2, e3]
  norm_num

/-- A diagonal `QuadForm` with entries `![a₀, a₁, a₂, a₃]` rewritten from an arbitrary `Fin 4` vector. -/
theorem eq_vec_four' (a : Fin 4 → ℚ_[p]) : ∃ a₀ a₁ a₂ a₃, a = ![a₀, a₁, a₂, a₃] :=
  ⟨a 0, a 1, a 2, a 3, by funext i; fin_cases i <;> rfl⟩

end Cor353

open Cor353 in
/-- **Kitaoka 1993, Corollary 3.5.3** (p. 63): over $\mathbb Q_p$ there is a unit $\delta \in \mathbb Z_p^\times$
with $(p, \delta)_p = -1$ and $(\delta, u)_p = 1$ for all $u \in \mathbb Z_p^\times$, such that the quaternary diagonal
form $\langle 1, -\delta, p, -\delta p\rangle$ is anisotropic, and every regular anisotropic quaternary quadratic
space $U$ over $\mathbb Q_p$ is isometric to it. (The "in particular" part, $dU = 1$ modulo squares and Hasse
invariant $-(-1,-1)_p$, is `Cor353.invariants_of_not_isotropic`.) -/
@[kb "kitaoka1993" "§3.5, Cor. 3.5.3, p. 63"]
theorem corollary353 (p : ℕ) [Fact p.Prime] :
    ∃ δ : ℤ_[p], IsUnit δ ∧ hilbertSymbol ℚ_[p] (p : ℚ_[p]) ((δ : ℤ_[p]) : ℚ_[p]) = -1 ∧
      (∀ u : ℤ_[p], IsUnit u →
        hilbertSymbol ℚ_[p] ((δ : ℤ_[p]) : ℚ_[p]) ((u : ℤ_[p]) : ℚ_[p]) = 1) ∧
      (weightedSumSquares ℚ_[p]
        ![1, -((δ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]), -((δ : ℤ_[p]) : ℚ_[p]) * p]).Anisotropic ∧
      ∀ Q : QuadraticForm ℚ_[p] (Fin 4 → ℚ_[p]), (QuadraticMap.polarBilin Q).Nondegenerate →
        Q.Anisotropic →
        Q.Equivalent (weightedSumSquares ℚ_[p]
          ![1, -((δ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]), -((δ : ℤ_[p]) : ℚ_[p]) * p]) := by
  have hK := localHilbertField_padic p
  obtain ⟨δ, hδ, h1, h2⟩ := exists_delta p
  have hT := diag_not_isotropic p δ hδ h1 h2
  have hd0 : ((δ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h; exact hδ.ne_zero (PadicInt.ext (by simpa using h))
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨δ, hδ, h1, h2, (wss_anisotropic_iff p _).mpr hT, ?_⟩
  intro Q hQ hA
  have hnd : (associated (R := ℚ_[p]) Q).SeparatingLeft := by
    intro x hx
    refine hQ.1 x fun y => ?_
    have e : Q.polarBilin x y = 2 • associated (R := ℚ_[p]) Q x y := by
      rw [← two_nsmul_associated ℚ_[p] Q]; rfl
    rw [e, hx y]; simp
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hnd
  have key : ∀ k, Module.finrank ℚ_[p] (Fin 4 → ℚ_[p]) = k →
      ∃ a : Fin k → ℚ_[p], (∀ i, a i ≠ 0) ∧ Q.Equivalent (weightedSumSquares ℚ_[p] a) := by
    intro k hk
    subst hk
    refine ⟨fun i => (w i : ℚ_[p]), fun i => (w i).ne_zero, ?_⟩
    have : weightedSumSquares ℚ_[p] w = weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p])) := by
      ext x; simp [weightedSumSquares_apply, Units.smul_def]
    rwa [← this]
  obtain ⟨a, ha, hw'⟩ := key 4 (Module.finrank_fin_fun _)
  obtain ⟨e⟩ := id hw'
  -- the diagonal form of `Q` is anisotropic
  have hAa : (weightedSumSquares ℚ_[p] a).Anisotropic := by
    intro x hx
    have h0 : Q (e.symm x) = 0 := by rw [e.symm.map_app]; exact hx
    have h1 := hA _ h0
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = 0 := by rw [h1]; exact map_zero e
  have hnT := (wss_anisotropic_iff p a).mp hAa
  obtain ⟨a₀, a₁, a₂, a₃, rfl⟩ := eq_vec_four' p a
  have h₀ : a₀ ≠ 0 := by simpa using ha 0
  have h₁ : a₁ ≠ 0 := by simpa using ha 1
  have h₂ : a₂ ≠ 0 := by simpa using ha 2
  have h₃ : a₃ ≠ 0 := by simpa using ha 3
  obtain ⟨⟨s, hs0, hs⟩, hHa⟩ := invariants_of_not_isotropic p h₀ h₁ h₂ h₃ hnT
  obtain ⟨⟨s', hs'0, hs'⟩, hHb⟩ := invariants_of_not_isotropic p one_ne_zero (neg_ne_zero.mpr hd0)
    hp0 (mul_ne_zero (neg_ne_zero.mpr hd0) hp0) hT
  have hb : ∀ i, (![1, -((δ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]), -((δ : ℤ_[p]) : ℚ_[p]) * p] :
      Fin 4 → ℚ_[p]) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hd0, hp0]
  have hiso : (diag ![1, -((δ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]), -((δ : ℤ_[p]) : ℚ_[p]) * p]).IsometricIn
      ℚ_[p] (diag ![a₀, a₁, a₂, a₃]) := by
    refine (isometric_iff_invariants hK hb ha).mpr ⟨⟨s / s', div_ne_zero hs0 hs'0, ?_⟩, ?_⟩
    · simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hs' ⊢
      rw [hs, hs']; field_simp
    · rw [hHa, hHb]
  exact hw'.trans ((Cor354.wss_equiv_iff p _ _).mpr hiso)

end QuadFormsKB.Kitaoka
