/-
# Hanke 2005, Remark after (2.8): dependence on the choice of basis (finite places)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis (bib key `hanke2005crelle`), p. 5.

**Remark.** "Both the volume form $\tilde\omega_G$ and the local densities $\beta_v(\psi)$ depend not only on
$(V,\varphi)$ and $v$, but also on our given choice of basis for $(V,\varphi)$."

Finite-place version for the local density `hankeBeta v Λ ψ` $=\beta_v(\Lambda,\psi)$. Changing the basis of
$V = F_v^n$ by $A\in\mathrm{GL}_n(F_v)$ leaves the lattice $\Lambda$ fixed as a subset of $V$; in the new
coordinates the Gram matrix is ${}^tA\psi A$ and the lattice is $A^{-1}\Lambda$. We show:

* `hankeBeta_changeBasis`: $\beta_v(A^{-1}\Lambda,{}^tA\psi A) = |\det A|_v^{-(n+1)}\,\beta_v(\Lambda,\psi)$
  (a consequence of the corrected Lemma 2.2, `hankeBeta_congr`);
* `remark28_basis_dependence`: for $n\ge 1$ this factor can differ from $1$ (take $\psi = 1$,
  $A = \varpi\cdot 1_n$ with $\varpi$ a uniformizer, $\Lambda = \mathfrak o_v^n$), so $\beta_v$ really depends on the
  basis. Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Literature.Hanke2005.Lemma22
import QuadFormsKB.Citation

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {v}

/-- **Change of basis multiplies $\beta_v$ by $|\det A|_v^{-(n+1)}$** (Hanke thesis, Remark after (2.8), p. 5).
Let $A, B\in\mathrm{GL}_n(F_v)$, let $\Lambda = B\,\mathfrak o_v^n$, and let $\psi$ be symmetric
(hypothesis `hψ`: ${}^t\psi=\psi$) and nondegenerate (`hdet`: $\det\psi\ne0$). In the basis changed by $A$ the
lattice is $A^{-1}\Lambda$ and the Gram matrix is ${}^tA\psi A$, and
$\beta_v(A^{-1}\Lambda,{}^tA\psi A) = |\det A|_v^{-(n+1)}\,\beta_v(\Lambda,\psi)$. -/
@[kb "hanke2005crelle" "Remark after (2.8), p. 5"]
theorem hankeBeta_changeBasis (A B : GL (Fin n) Fv) {ψ : Matrix (Fin n) (Fin n) Fv} (hψ : ψᵀ = ψ)
    (hdet : ψ.det ≠ 0) :
    hankeBeta v (locAct v A⁻¹ (locAct v B (std v)))
        ((A : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (A : Matrix (Fin n) (Fin n) Fv)) =
      ‖(A : Matrix (Fin n) (Fin n) Fv).det‖ ^ (-((n : ℤ) + 1)) *
        hankeBeta v (locAct v B (std v)) ψ := by
  rw [← locAct_mul, hankeBeta_congr v A (A⁻¹ * B) hψ hdet, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The local density depends on the basis** (Hanke thesis, Remark after (2.8), p. 5). For $n\ge1$ there are a
symmetric invertible $\psi$ (namely $\psi = 1_n$, with `hψ`, `hdet`) and $A\in\mathrm{GL}_n(F_v)$ (namely
$A = \varpi\cdot1_n$, $\varpi$ a uniformizer) such that, for $\Lambda = \mathfrak o_v^n$ (`std v`),
$\beta_v(A^{-1}\Lambda,{}^tA\psi A)\ne\beta_v(\Lambda,\psi)$. -/
@[kb "hanke2005crelle" "Remark after (2.8), p. 5"]
theorem remark28_basis_dependence (hn : 1 ≤ n) :
    ∃ (A : GL (Fin n) Fv) (ψ : Matrix (Fin n) (Fin n) Fv), ψᵀ = ψ ∧ ψ.det ≠ 0 ∧
      hankeBeta v (locAct v A⁻¹ (std v))
          ((A : Matrix (Fin n) (Fin n) Fv)ᵀ * ψ * (A : Matrix (Fin n) (Fin n) Fv)) ≠
        hankeBeta v (std v) ψ := by
  set p : Fv := ((NF.π v : 𝔬) : Fv) with hp
  have hpv : Valued.v p = exp (-1 : ℤ) := NF.valued_π v
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hpv; exact WithZero.zero_ne_coe hpv
  let P : Matrix (Fin n) (Fin n) Fv := p • (1 : Matrix (Fin n) (Fin n) Fv)
  have hPd : P.det = p ^ n := by simp [P]
  let A : GL (Fin n) Fv := GeneralLinearGroup.mkOfDetNeZero P (by rw [hPd]; exact pow_ne_zero _ hp0)
  have hA : (A : Matrix (Fin n) (Fin n) Fv) = P := rfl
  have h1d : (1 : Matrix (Fin n) (Fin n) Fv).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  refine ⟨A, 1, Matrix.transpose_one, h1d, ?_⟩
  have hY := hankeBeta_changeBasis A 1 (ψ := (1 : Matrix (Fin n) (Fin n) Fv)) Matrix.transpose_one h1d
  rw [locAct_one] at hY
  rw [hY]
  have hdA : (A : Matrix (Fin n) (Fin n) Fv).det = p ^ n := by rw [hA, hPd]
  rw [hdA]
  have hpos := hankeBeta_std_one_pos (v := v) (n := n)
  have hq1 : 1 < DVR.q 𝔬 := by
    have h0 := DVR.q_pos (R := 𝔬)
    have h1 : DVR.q 𝔬 ≠ 1 := by
      rw [NF.q_completion]; intro h; exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  have hnorm : ‖p‖ = ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ := core_norm_of_valued v (e := 1) (by simpa using hpv)
  have hqr : (1 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast hq1
  have hr1 : ‖p‖ < 1 := by
    rw [hnorm, pow_one]; exact inv_lt_one_of_one_lt₀ hqr
  have hr0 : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hlt : ‖p ^ n‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ hr0.le hr1 (by omega)
  have hpos' : 0 < ‖p ^ n‖ := by rw [norm_pos_iff]; exact pow_ne_zero _ hp0
  intro h
  have hz : ‖p ^ n‖ ^ (-((n : ℤ) + 1)) > 1 := by
    have : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, _root_.zpow_neg, zpow_natCast]
    exact one_lt_inv_iff₀.mpr ⟨pow_pos hpos' _, pow_lt_one₀ hpos'.le hlt (by omega)⟩
  set X := hankeBeta v (std v) (1 : Matrix (Fin n) (Fin n) Fv)
  nlinarith

end QuadFormsKB.Hanke2005
