/-
# Hanke 2011, Theorem 6.2: the archimedean constant $C_{\vec\sigma_\infty,n}$ depends only on the signature

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Theorem 6.2, p. 25–26.

The library's one-genus Theorem 6.2 (`theorem_6_2_genus`) uses the constant `constC Q₀`, built from Hanke 2005's
$r_v$ = `Hanke2005.rAt Q₀ v` (the Witt index of $Q_0$ at the real place $v$). The paper's constant is
$$C_{\vec\sigma_\infty,n} = \prod_{v\ \mathrm{real}}2\cdot2^{-n\min(\sigma_{v,+},\sigma_{v,-})/2}V(\sigma_{v,+})V(\sigma_{v,-})
  \cdot\prod_{v\ \mathrm{complex}}2^{n(n-3)/2}V(n),$$
a function of the signature vector alone. Here:

* `wittIndex_of_hasSignature`: if $Q$ (over $F$) has signature $(\sigma_{v,+},\sigma_{v,-})$ at the real place $v$, the
  Witt index of $Q^{\sigma_v}$ over $\mathbb R$ is $\min(\sigma_{v,+},\sigma_{v,-})$ (Sylvester; O'Meara §61A).
* `rAt_of_hasSignature`: so $r_v = \min(\sigma_{v,+},\sigma_{v,-})$ for $Q = Q_0\otimes F$ of signature $\vec\sigma_\infty$.
* `sigConst σ` (the constant written with the signature vector), and `constC_eq_sigConst`: `constC Q₀ = sigConst σ`
  whenever $Q_0 \otimes F$ has signature $\vec\sigma_\infty$.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummed
import QuadFormsKB.Literature.Hanke2005.ArchNormalForm
import QuadFormsKB.Literature.Hanke2005.MuArchHankeFactor

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField NumberField.InfinitePlace Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular
  QuadFormsKB.Siegel QuadFormsKB.Hanke2005

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Evaluation commutes with a ring homomorphism applied to the coefficients and the vector. -/
theorem evalIn_ringHom {K K' : Type*} [Field K] [Field K'] [Algebra F K] (ψ : K →+* K') (Q : QuadForm F n)
    (x : Fin n → K) :
    ψ (Q.evalIn K x) = (Q.map (ψ.comp (algebraMap F K))).eval (fun i => ψ (x i)) := by
  simp only [QuadForm.evalIn, QuadForm.map, map_sum, Algebra.algebraMap_self, RingHom.id_apply, Matrix.map_apply,
    RingHom.comp_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem hessian_diag' {K : Type*} [CommRing K] (a : Fin n → K) :
    (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  unfold QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, two_mul]

theorem ncard_fin_lt (m : ℕ) : {i : Fin n | (i : ℕ) < m}.ncard = min n m := by
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  exact Fin.card_filter_val_lt

theorem ncard_sigVec_pos (p : SigPair n) : {i : Fin n | 0 < sigVec ℝ p i}.ncard = p.1.1 := by
  have e : {i : Fin n | 0 < sigVec ℝ p i} = {i : Fin n | (i : ℕ) < p.1.1} := by
    ext i
    simp only [Set.mem_setOf_eq, sigVec]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => by norm_num⟩
    · exact ⟨fun hh => by norm_num at hh, fun hh => absurd hh h⟩
  rw [e, ncard_fin_lt]
  have := p.2; omega

theorem ncard_sigVec_neg (p : SigPair n) : {i : Fin n | sigVec ℝ p i < 0}.ncard = p.1.2 := by
  have e : {i : Fin n | sigVec ℝ p i < 0} = {i : Fin n | (i : ℕ) < p.1.1}ᶜ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, sigVec]
    split_ifs with h
    · exact ⟨fun hh => by norm_num at hh, fun hh => absurd h hh⟩
    · exact ⟨fun _ => h, fun _ => by norm_num⟩
  rw [e, Set.ncard_compl, ncard_fin_lt, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := p.2; omega

/-- **The Witt index at a real place is $\min(\sigma_{v,+},\sigma_{v,-})$** for a form of signature $\vec\sigma_\infty$ (Sylvester's law of
inertia; O'Meara §61A, `OMeara.wittIndex_eq_min`). -/
@[kb "omeara1963" "§61A, p. 155 (ind V = min(ind⁺, ind⁻) over ℝ)"]
theorem wittIndex_of_hasSignature {Q : QuadForm F n} {σ : SignatureVector F n} (h : HasSignature Q σ)
    (w : {w : InfinitePlace F // w.IsReal}) (hQ : gramDetR (Q.map (embedding_of_isReal w.2)) ≠ 0) :
    QuadraticForm.wittIndex (Q.map (embedding_of_isReal w.2)).toQuadraticForm = min (σ w).1.1 (σ w).1.2 := by
  classical
  set QR := Q.map (embedding_of_isReal w.2)
  set ψe := InfinitePlace.Completion.ringEquivRealOfIsReal w.2
  set ψ : w.1.Completion →+* ℝ := (ψe : w.1.Completion →+* ℝ) with hψ
  obtain ⟨P, hP, hPe⟩ := (isometricIn_map_iff Q _).mp (h w)
  set P' : Matrix (Fin n) (Fin n) ℝ := P.map ψ with hP'
  have hcomp : ψ.comp (algebraMap F w.1.Completion) = embedding_of_isReal w.2 := by
    ext y; exact algebraMap_completion_real' w.2 y
  -- `QR (P' y) = Σ s_i y_i²`
  have hev : ∀ y : Fin n → ℝ, QR.eval (P' *ᵥ y) = (QuadForm.diag (sigVec ℝ (σ w))).eval y := by
    intro y
    set z : Fin n → w.1.Completion := fun i => ψe.symm (y i)
    have h1 := congrArg ψ (hPe z)
    rw [evalIn_ringHom ψ, evalIn_ringHom ψ, hcomp] at h1
    have hz : (fun i => ψ (z i)) = y := funext fun i => by simp [z, ψ]
    have hPz : (fun i => ψ ((P *ᵥ z) i)) = P' *ᵥ y := by
      funext i
      simp [hP', Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, z, ψ]
    rw [hPz, hz] at h1
    rw [h1]
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, QuadForm.map, Matrix.map_apply,
      Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_comp, Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h1 h2 <;> simp [Matrix.diagonal_apply, sigVec] <;> split_ifs <;> simp_all
  have hcm : QR.compMat P' = QuadForm.diag (sigVec ℝ (σ w)) :=
    QuadForm.eq_of_eval_eq fun y => by rw [QuadForm.eval_compMat, hev]
  have hH : P'ᵀ * gramMatrixR QR * P' = diagonal (sigVec ℝ (σ w)) := by
    have := congrArg QuadForm.hessian hcm
    rw [QuadForm.hessian_compMat, hessian_diag'] at this
    unfold gramMatrixR
    rw [Matrix.mul_smul, Matrix.smul_mul, this]
    ext i j
    simp [Matrix.diagonal_apply]
  have hdet : IsUnit P'.det := by
    have e : P'.det = ψ P.det := (RingHom.map_det ψ P).symm
    rw [e]
    exact hP.map ψ
  have hPu : IsUnit P' := (Matrix.isUnit_iff_isUnit_det P').mpr hdet
  rw [wittIndex_of_diag QR hQ hPu.unit (sigVec ℝ (σ w)) hH, ncard_sigVec_pos, ncard_sigVec_neg]

/-- **$r_v = \min(\sigma_{v,+},\sigma_{v,-})$** for $Q_0\otimes F$ of signature $\vec\sigma_\infty$ ($Q_0$ nondegenerate). -/
theorem rAt_of_hasSignature (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) {σ : SignatureVector F n}
    (h : HasSignature (formF Q₀) σ) (w : {w : InfinitePlace F // w.IsReal}) :
    rAt Q₀ w.1 = min (σ w).1.1 (σ w).1.2 := by
  rw [rAt_eq_wittIndex]
  exact wittIndex_of_hasSignature h w (Tamagawa.Measure.Weil.gramDetR_QRe_ne_zero Q₀ hQ w)

open Classical in
/-- **The archimedean constant $C_{\vec\sigma_\infty,n}$ of Theorem 6.2, as a function of the signature vector** (p. 26):
$\prod_{v\ \mathrm{real}}\mathrm{vol}(\sigma_{v,+},\sigma_{v,-})\cdot\prod_{v\ \mathrm{complex}}\mathrm{vol}_{\mathbb C}(n)$, with the library's
volumes `volCReal (n - r) r` ($r = \min(\sigma_{v,+},\sigma_{v,-})$) and `volCComplex n` (Hanke 2005, §4). -/
@[kb "hanke2011structure" "Thm. 6.2, p. 26 (C_{σ,n})"]
def sigConst (σ : SignatureVector F n) : ℝ :=
  ∏ w : InfinitePlace F, if hw : w.IsReal then
    volCReal (n - min (σ ⟨w, hw⟩).1.1 (σ ⟨w, hw⟩).1.2) (min (σ ⟨w, hw⟩).1.1 (σ ⟨w, hw⟩).1.2) else volCComplex n

open Classical in
/-- `constC Q₀ = sigConst σ`: the constant of the one-genus Theorem 6.2 depends only on the signature vector. -/
@[kb "hanke2011structure" "Thm. 6.2, p. 26 (C depends only on the signature vector)"]
theorem constC_eq_sigConst (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) {σ : SignatureVector F n}
    (h : HasSignature (formF Q₀) σ) : constC Q₀ = sigConst σ := by
  unfold constC sigConst
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : w.IsReal
  · rw [if_pos hw, dif_pos hw, rAt_of_hasSignature Q₀ hQ h ⟨w, hw⟩]
  · rw [if_neg hw, dif_neg hw]

theorem sigConst_pos (σ : SignatureVector F n) : 0 < sigConst σ := by
  classical
  unfold sigConst
  refine Finset.prod_pos fun w _ => ?_
  split_ifs
  · unfold volCReal
    have := tauR_pos (n - min (σ ⟨w, ‹_›⟩).1.1 (σ ⟨w, ‹_›⟩).1.2)
    have := tauR_pos (min (σ ⟨w, ‹_›⟩).1.1 (σ ⟨w, ‹_›⟩).1.2)
    positivity
  · unfold volCComplex
    have := tauR_pos n; positivity

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.wittIndex_of_hasSignature
#print axioms QuadFormsKB.Hanke2011Structure.constC_eq_sigConst
