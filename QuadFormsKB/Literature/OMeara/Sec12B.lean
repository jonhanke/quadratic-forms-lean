/-
# O'Meara §12: complete archimedean fields (special case of 12:4)

**Proves** `complete_ordinary_isReal_or_isComplex` (**12:4**, special case): a field $F$ complete under a valuation $v$
with $|m| = m$ for all natural numbers $m$ (`IsOrdinaryAbs`, O'Meara's normalization 12:5) is isometrically
ring-isomorphic to $\mathbb R$ or to $\mathbb C$.

**Special case.** O'Meara's 12:4 assumes only that the valuation is complete and archimedean; by 12:1 such a valuation is
$|\ |_0^{\varrho}$ with $|\ |_0$ the ordinary one and $\varrho \in (0,1]$. For $\varrho = 1$ we get the statement here. The
case $\varrho < 1$ needs 12:2, 12:3 (that $|\ |_0$ again satisfies the triangle law), which Mathlib lacks and we do not
prove. Proof: $\mathbb R$ is the completion of $\mathbb Q$ (11:14 gives $\mathbb R \to F$ isometric), so $F$ is a normed
$\mathbb R$-algebra and Mathlib's Gelfand–Mazur theorem applies; in the complex case a multiplicative norm on
$\mathbb C$ extending $|\ |$ on $\mathbb R$ is the usual one, by comparing $N(z^n)$ with $2|z|^n$ (`norm_eq_of_algEquiv_complex`).
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.NumberTheory.Ostrowski
import QuadFormsKB.Literature.OMeara.Sec12A
import QuadFormsKB.Literature.OMeara.Sec11B

open Filter Topology

namespace QuadFormsKB.OMeara

universe u
variable {F : Type u} [Field F]

/-- If $|m| = m$ for natural $m$, then $|q| = |q|_\infty$ for every rational $q$ (viewed in $F$). -/
theorem ordinary_ratCast (v : AbsoluteValue F ℝ) (hv : IsOrdinaryAbs v) (q : ℚ) :
    v (q : F) = |(q : ℝ)| := by
  have hn : ∀ n : ℕ, v (n : F) = n := hv
  have hz : ∀ n : ℤ, v (n : F) = |(n : ℝ)| := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · simp [hn]
    · simp [hn]
  rw [Rat.cast_def, map_div₀, hz, hn, Rat.cast_def (K := ℝ), abs_div]
  simp


/-- $\mathbb R$ is a completion of $\mathbb Q$ at the usual absolute value. -/
theorem isCompletion_rat_real : IsCompletion Rat.AbsoluteValue.real ℝ (Rat.castHom ℝ) where
  norm_eq q := by
    show ‖((q : ℚ) : ℝ)‖ = Rat.AbsoluteValue.real q
    rw [Real.norm_eq_abs, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs]
  dense := Rat.denseRange_cast
  complete := inferInstance

/-- Key step: a multiplicative norm on ℂ extending |·| on ℝ is |·|. -/
theorem norm_eq_of_algEquiv_complex {T : Type*} [NormedField T] [NormedAlgebra ℝ T]
    (e : T ≃ₐ[ℝ] ℂ) (z : ℂ) : ‖e.symm z‖ = ‖z‖ := by
  have hI : ‖e.symm Complex.I‖ = 1 := by
    have h2 : ‖e.symm Complex.I‖ ^ 2 = 1 := by
      have : e.symm Complex.I ^ 2 = algebraMap ℝ T (-1) := by
        rw [← map_pow, Complex.I_sq]
        have : (-1 : ℂ) = algebraMap ℝ ℂ (-1) := by simp
        rw [this, AlgEquiv.commutes]
      rw [← norm_pow, this, norm_algebraMap']
      simp
    nlinarith [norm_nonneg (e.symm Complex.I)]
  have hdec : ∀ w : ℂ, ‖e.symm w‖ ≤ ‖w.re‖ + ‖w.im‖ := by
    intro w
    have : w = algebraMap ℝ ℂ w.re + algebraMap ℝ ℂ w.im * Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes]
    calc _ ≤ ‖algebraMap ℝ T w.re‖ + ‖algebraMap ℝ T w.im * e.symm Complex.I‖ := norm_add_le _ _
      _ = ‖w.re‖ + ‖w.im‖ := by rw [norm_mul, hI, norm_algebraMap', norm_algebraMap']; simp
  have key : ∀ w : ℂ, ‖e.symm w‖ ≤ ‖w‖ := by
    intro w
    by_contra hlt
    rw [not_le] at hlt
    have hw0 : 0 < ‖w‖ := by
      rcases eq_or_ne w 0 with rfl | h
      · simp at hlt
      · exact norm_pos_iff.2 h
    have hr : 1 < ‖e.symm w‖ / ‖w‖ := (one_lt_div hw0).2 hlt
    have ht := tendsto_pow_atTop_atTop_of_one_lt hr
    obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop 2).exists
    have h1 : ‖e.symm w‖ ^ n ≤ 2 * ‖w‖ ^ n := by
      have := hdec (w ^ n)
      rw [map_pow, norm_pow] at this
      have h3 : ‖(w ^ n).re‖ ≤ ‖w ^ n‖ := Complex.abs_re_le_norm _
      have h4 : ‖(w ^ n).im‖ ≤ ‖w ^ n‖ := Complex.abs_im_le_norm _
      rw [norm_pow] at h3 h4
      linarith
    rw [div_pow] at hn
    rw [lt_div_iff₀ (pow_pos hw0 n)] at hn
    linarith
  have hw : ∀ w : ℂ, ‖w‖ ≤ ‖e.symm w‖ ∨ w = 0 := by
    intro w
    by_cases h0 : w = 0
    · exact Or.inr h0
    · left
      have h1 := key w⁻¹
      rw [map_inv₀, norm_inv, norm_inv] at h1
      have hp : 0 < ‖e.symm w‖ := norm_pos_iff.2 (by simpa using h0)
      have hq : 0 < ‖w‖ := norm_pos_iff.2 h0
      rw [inv_le_inv₀ hp hq] at h1
      exact h1
  rcases hw z with h | h
  · exact le_antisymm (key z) h
  · simp [h]


/-- **12:4 (normalized case).** A field $F$ complete under a valuation $v$ with $|m|_v = m$ for all natural $m$ is
isometrically isomorphic to $\mathbb R$ ($|\varphi x| = v(x)$) or to $\mathbb C$ ($\lVert\varphi x\rVert = v(x)$). -/
@[kb "omeara1963" "§12, 12:4 (case |m| = m), p. 17"]
theorem complete_ordinary_isReal_or_isComplex (v : AbsoluteValue F ℝ) (hv : IsOrdinaryAbs v)
    [CompleteSpace (WithAbs v)] :
    (∃ φ : F ≃+* ℝ, ∀ x, |φ x| = v x) ∨ (∃ φ : F ≃+* ℂ, ∀ x, ‖φ x‖ = v x) := by
  have hn : ∀ n : ℕ, v (n : F) = n := hv
  have : CharZero F := charZero_of_inj_zero fun n h => by
    have := hn n
    rw [h, map_zero] at this
    exact_mod_cast this.symm
  let T := WithAbs v
  let σ : ℚ →+* T := (WithAbs.equiv v).symm.toRingHom.comp (Rat.castHom F)
  have hσ : ∀ q, ‖σ q‖ = Rat.AbsoluteValue.real q := fun q => by
    show v (q : F) = _
    rw [ordinary_ratCast v hv q, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs]
  obtain ⟨τ, -, hτ, -⟩ := exists_prolongation Rat.AbsoluteValue.real (Rat.castHom ℝ)
    isCompletion_rat_real σ hσ
  let : Algebra ℝ T := τ.toAlgebra
  let : NormedAlgebra ℝ T :=
    { (inferInstance : Algebra ℝ T) with
      norm_smul_le := fun r x => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (by congr 1; exact (hτ r).trans (Real.norm_eq_abs r |>.symm ▸ rfl)) }
  rcases NormedAlgebra.Real.nonempty_algEquiv_or T with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    refine ⟨(WithAbs.equiv v).symm.trans e.toRingEquiv, fun x => ?_⟩
    show |e (WithAbs.toAbs v x)| = ‖WithAbs.toAbs v x‖
    set y : T := WithAbs.toAbs v x
    have hy : y = τ (e y) := by
      apply e.injective
      have : τ (e y) = algebraMap ℝ T (e y) := rfl
      rw [this, AlgEquiv.commutes]
      simp
    conv_rhs => rw [hy]
    rw [hτ, Real.norm_eq_abs]
  · right
    refine ⟨(WithAbs.equiv v).symm.trans e.toRingEquiv, fun x => ?_⟩
    have := norm_eq_of_algEquiv_complex e (e (WithAbs.toAbs v x))
    rw [AlgEquiv.symm_apply_apply] at this
    exact this.symm

end QuadFormsKB.OMeara
