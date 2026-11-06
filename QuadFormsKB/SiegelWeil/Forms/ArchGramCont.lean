/-
# Continuity of the rectangular Gram density
**Layer:** real analysis on the space of symmetric matrices in upper coordinates (`UIdx r → ℝ`).

**Results.**
* `PDU_of_piv`: positive Schur pivots (`piv`) imply positive definiteness (`PDU`); the converse of `piv_of_PDU`.
  Hence the two notions agree. Proof by induction on the size, using
  $x^{\mathsf T}tx = s\,(a + u\cdot y/s)^2 + y^{\mathsf T}(V - uu^{\mathsf T}/s)\,y$ for $x = (a, y)$.
* `continuousAt_densRect_toReal`: for $r + 1 < N$ the density $t \mapsto \rho_{N,r}(t)$ (as a real number) is continuous at
  every point $T$ of $\mathbb R^{\{(i,j) : i \le j\}}$. Inside the positive definite cone it equals
  $c\,\det(t)^{(N-r-1)/2}$; outside the closure of the cone it vanishes; on the boundary it is squeezed by
  $c\,|\det t|^{(N-r-1)/2} \to 0$ because the exponent is positive.
* `continuousAt_densRect_mul`: the product of the density with a function continuous at $T$ is continuous at $T$.

Indices are 0-based.

**Inputs.** None: everything is proved from Mathlib, unconditionally.

Sources: Siegel, Ann. of Math. 36 (1935), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.SiegelWeil.Forms.ArchGram

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Hanke2005.ArchReal

/-- **Positive Schur pivots imply positive definiteness:** if `piv n t` then the symmetric matrix with upper coordinates
$t$ satisfies $x^{\mathsf T}tx > 0$ for all $x \ne 0$. Converse of `piv_of_PDU`. -/
theorem PDU_of_piv : ∀ (n : ℕ) (t : UIdx n → ℝ), piv n t → PDU t
  | 0, t, _ => by
    intro x hx
    exact absurd (Subsingleton.elim x 0) hx
  | n + 1, t, ⟨hs, hp⟩ => by
    intro x hx
    obtain ⟨a, y, rfl⟩ : ∃ a y, x = (Fin.cons a y : Fin (n + 1) → ℝ) :=
      ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [quad_cons]
    have key : sU t * a ^ 2 + 2 * a * (uU t ⬝ᵥ y) + y ⬝ᵥ (symU (vU t) *ᵥ y) =
        sU t * (a + (uU t ⬝ᵥ y) / sU t) ^ 2 + y ⬝ᵥ (symU (schurU t) *ᵥ y) := by
      rw [quad_schur]; field_simp; ring
    rw [key]
    by_cases hy : y = 0
    · subst hy
      have ha : a ≠ 0 := by
        rintro rfl
        exact hx (by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp)
      simp only [dotProduct_zero, zero_div, add_zero, mulVec_zero]
      have := mul_pos hs (pow_pos (abs_pos.2 ha) 2)
      simpa [sq_abs] using this
    · have h2 := PDU_of_piv n _ hp y hy
      have : 0 ≤ sU t * (a + (uU t ⬝ᵥ y) / sU t) ^ 2 := mul_nonneg hs.le (sq_nonneg _)
      linarith

/-- The symmetric matrix with upper coordinates $t$ depends continuously on $t$. -/
theorem continuous_symU {n : ℕ} : Continuous fun t : UIdx n → ℝ => symU t := by
  refine continuous_matrix fun i j => ?_
  simp only [symU, Matrix.of_apply]
  split_ifs <;> exact continuous_apply _

/-- The symmetric matrix with upper coordinates $t$ is symmetric. -/
theorem isSymm_symU {n : ℕ} (t : UIdx n → ℝ) : (symU t).IsSymm := by
  ext i j
  simp only [symU, transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h.le, not_le.2 h]
  · subst h; rfl
  · simp [h.le, not_le.2 h]

/-- **Continuity of the rectangular Gram density.** For $r + 1 < N$ the real-valued density
$t \mapsto \rho_{N,r}(t)$ is continuous at every $T$. -/
theorem continuousAt_densRect_toReal {N r : ℕ} (h : r + 1 < N) (T : UIdx r → ℝ) :
    ContinuousAt (fun t => (densRect N r t).toReal) T := by
  set a : ℝ := ((N : ℝ) - r - 1) / 2 with ha
  have ha0 : 0 < a := by
    have : (r : ℝ) + 1 < N := by exact_mod_cast h
    rw [ha]; linarith
  have hc := cprodRect_pos (show r ≤ N by omega)
  by_cases hT : piv r T
  · have hopen : IsOpen {t : UIdx r → ℝ | piv r t} := isOpen_piv r
    have hev : (fun t => (densRect N r t).toReal) =ᶠ[𝓝 T]
        fun t => cprodRect N r * (symU t).det ^ a := by
      filter_upwards [hopen.mem_nhds hT] with t ht
      obtain ⟨hd, he⟩ := densRect_of_piv N r t (by omega) ht
      rw [he, ENNReal.toReal_ofReal (mul_nonneg hc.le (Real.rpow_nonneg hd.le _))]
    refine ContinuousAt.congr ?_ hev.symm
    have hdet : ContinuousAt (fun t : UIdx r → ℝ => (symU t).det) T :=
      continuous_det_symU.continuousAt
    exact continuousAt_const.mul
      (ContinuousAt.rpow_const hdet (Or.inl (densRect_of_piv N r T (by omega) hT).1.ne'))
  · have hz : densRect N r T = 0 := densRect_eq_zero_of_not_piv N r T hT
    by_cases hd : (symU T).det = 0
    · rw [ContinuousAt, hz, ENNReal.toReal_zero]
      have hdet : Tendsto (fun t : UIdx r → ℝ => |(symU t).det|) (𝓝 T) (𝓝 0) := by
        have := (continuous_det_symU (n := r)).continuousAt (x := T)
        have h2 := this.abs
        simpa [ContinuousAt, hd] using h2
      have hup : Tendsto (fun t : UIdx r → ℝ => cprodRect N r * |(symU t).det| ^ a) (𝓝 T) (𝓝 0) := by
        have h1 : ContinuousAt (fun x : ℝ => cprodRect N r * x ^ a) 0 :=
          continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr ha0.le))
        have h3 := h1.tendsto.comp hdet
        simpa [Function.comp_def, Real.zero_rpow ha0.ne'] using h3
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun t => ENNReal.toReal_nonneg) (fun t => densRect_le N r (by omega) t)
    · have hneg : ∃ x : Fin r → ℝ, x ⬝ᵥ (symU T *ᵥ x) < 0 := by
        by_contra hcon
        push Not at hcon
        have hps : (symU T).PosSemidef := by
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isSymm_symU T) ?_
          intro x; simpa using hcon x
        have hpd : (symU T).PosDef :=
          (Matrix.PosSemidef.posDef_iff_isUnit hps).2
            ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
        have hP : PDU T := by
          intro x hx
          simpa using hpd.dotProduct_mulVec_pos hx
        exact hT (piv_of_PDU r T hP)
      obtain ⟨x, hx⟩ := hneg
      have hopen : IsOpen {t : UIdx r → ℝ | x ⬝ᵥ (symU t *ᵥ x) < 0} := by
        refine isOpen_lt ?_ continuous_const
        have : Continuous fun t : UIdx r → ℝ => symU t *ᵥ x := by
          refine continuous_pi fun i => ?_
          simp only [mulVec, dotProduct]
          exact continuous_finsetSum _ fun j _ => (((continuous_apply j).comp
            ((continuous_apply i).comp continuous_symU)).mul continuous_const)
        simp only [dotProduct]
        exact continuous_finsetSum _ fun j _ =>
          continuous_const.mul ((continuous_apply j).comp this)
      have hev : (fun t => (densRect N r t).toReal) =ᶠ[𝓝 T] fun _ => (densRect N r T).toReal := by
        filter_upwards [hopen.mem_nhds hx] with t ht
        have hxne : x ≠ 0 := by rintro rfl; simp at ht
        have hnp : ¬ piv r t := fun hp => by
          have := PDU_of_piv r t hp x hxne
          linarith
        rw [densRect_eq_zero_of_not_piv N r t hnp, hz]
      exact ContinuousAt.congr continuousAt_const hev.symm

/-- **The density times a function continuous at $T$ is continuous at $T$** (complex-valued version, for
$r + 1 < N$). -/
theorem continuousAt_densRect_mul {N r : ℕ} (h : r + 1 < N) {g : (UIdx r → ℝ) → ℂ} {T : UIdx r → ℝ}
    (hg : ContinuousAt g T) :
    ContinuousAt (fun t => ((densRect N r t).toReal : ℂ) * g t) T :=
  (Complex.continuous_ofReal.continuousAt.comp (continuousAt_densRect_toReal h T)).mul hg

end QuadFormsKB.SiegelWeil.Forms.ArchR
