/-
# Hanke 2011, Remark 7.9: existence of global genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Remark 7.9, p. 32.

**Remark 7.9** (as printed): the existence of a global genus of lattices in Lemma 7.8 (a totally definite
$\mathcal O_F$-valued binary lattice $L$ with $\det_H(L) = S$) "is equivalent to the local existence (at all $\mathfrak p$)
together with the condition that $S$ is globally rational".

Formalized (`remark_7_9`, every rank $n \ge 1$, every signature vector $\vec\sigma_\infty$, every number field, prescribed
Hasse invariants on a set $\mathbb S$): $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n) \ne \emptyset$ iff

1. $S$ is globally rational via some $\alpha \in F^\times$ ($\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ at every $\mathfrak p$) **such
   that $(-1)^{\sigma_{w,-}}\alpha$ is a square at every real place $w$**, and
2. there are local genera $G_{\mathfrak p}$ (nondegenerate, primitive, $\det_H G_{\mathfrak p} = S_{\mathfrak p}$, the
   prescribed Hasse invariants on $\mathbb S$) at every $\mathfrak p$ **whose Hasse invariants are almost all $1$ with product
   $\varepsilon_\infty$** ($\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n) \ne \emptyset$).

*Clarification (proposed by the formalization, not yet confirmed by the author):* the printed remark omits the sign condition in (1)
and the product condition in (2) (local existence at each $\mathfrak p$ separately is not enough: e.g. if every
$\mathfrak p$ has a unique local genus, its Hasse invariants must still multiply to $\varepsilon_\infty$, by Hilbert
reciprocity). For Lemma 7.8's totally definite binary case, (1) says $\alpha$ is totally positive. *Proof:* "only if":
`genStar_subset_genStarF`, `detH_isGloballyRational` (with $\alpha = \det H_Q$) and the signature (`sign_of_hasSignature`);
"if": Lemma 3.7's existence direction `genStarF_subset_genStar`. Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField NumberField.InfinitePlace Matrix QuadFormsKB.Lattices

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- At a real place, $(-1)^{\sigma_{w,-}}\det H_Q$ is a square for a form $Q$ of signature $\vec\sigma_\infty$. -/
theorem sign_of_hasSignature {Q : QuadForm F n} {σ : SignatureVector F n} (h : HasSignature Q σ)
    (w : {w : InfinitePlace F // w.IsReal}) :
    IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * Q.hessian.det)) := by
  classical
  set K := w.1.Completion
  obtain ⟨P, hP, hPe⟩ := (isometricIn_map_iff Q _).mp (h w)
  set s : Fin n → K := fun i => algebraMap F K (sigVec F (σ w) i)
  have hcm : (Q.map (algebraMap F K)).compMat P = QuadForm.diag s := by
    refine QuadForm.eq_of_eval_eq fun x => ?_
    rw [QuadForm.eval_compMat]
    have h1 := hPe x
    rw [← OMeara.evalIn_map_algebraMap K Q, ← OMeara.evalIn_map_algebraMap K (QuadForm.diag _)] at h1
    have e : (QuadForm.diag (sigVec F (σ w))).map (algebraMap F K) = QuadForm.diag s := by
      ext i j; simp [QuadForm.diag, QuadForm.map, s, Matrix.diagonal_apply]
    rw [e] at h1
    exact h1
  have hH := congrArg (fun q : QuadForm K n => q.hessian.det) hcm
  rw [QuadForm.hessian_compMat, det_mul, det_mul, det_transpose, QuadForm.hessian_map',
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hH
  have hdiag : (QuadForm.diag s).hessian.det = 2 ^ n * algebraMap F K ((-1) ^ (σ w).1.2) := by
    have : (QuadForm.diag s).hessian = Matrix.diagonal fun i => 2 * s i := by
      unfold QuadForm.hessian QuadForm.diag
      simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, two_mul]
    rw [this, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    simp only [s, ← map_prod, prod_sigVec]
  rw [hdiag] at hH
  -- `√2` in `K ≅ ℝ`
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal w.2
  set r : K := ψ.symm (Real.sqrt 2)
  have hr : r ^ 2 = 2 := by
    apply ψ.injective
    simp only [r, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
    exact Real.sq_sqrt (by norm_num)
  have hd : P.det ≠ 0 := hP.ne_zero
  refine ⟨r ^ n / P.det, ?_⟩
  have hsq : ((-1 : K) ^ (σ w).1.2) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [map_mul, map_pow, map_neg, map_one]
  have e2 : (2 : K) ^ n = (r ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, hr]
  have key : P.det * P.det * algebraMap F K Q.hessian.det = (r ^ n) ^ 2 * (-1) ^ (σ w).1.2 := by
    rw [← e2]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hH
  field_simp
  linear_combination (-1 : K) ^ (σ w).1.2 * key + (r ^ n) ^ 2 * hsq

/-- **Remark 7.9 (existence of global genera), corrected** (every $n \ge 1$, every signature vector, every number field):
$\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n) \ne \emptyset$ iff $S$ is globally rational via some $\alpha \in F^\times$
with $(-1)^{\sigma_{w,-}}\alpha$ a square at every real place, and local genera exist at every prime with the prescribed
Hasse invariants on $\mathbb S$ and Hasse product $\varepsilon_\infty$ (see the module docstring for the clarification). -/
@[kb "hanke2011structure" "Rem. 7.9, p. 32 (existence of global genera; clarified)"]
theorem remark_7_9 (hn : 1 ≤ n) (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) :
    (GenStar S σ 𝕊 c).Nonempty ↔
      (∃ α : Fˣ, (∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α)) ∧
        ∀ w : {w : InfinitePlace F // w.IsReal},
          IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) ∧
      (GenStarF (n := n) S (epsInf σ) 𝕊 c).Nonempty := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨?_, ⟨t, genStar_subset_genStarF S σ 𝕊 c ht⟩⟩
    obtain ⟨Q, hQ, L, hL, hσ, hS, -, -, -⟩ := ht
    refine ⟨Units.mk0 _ hQ, fun v => ?_, fun w => sign_of_hasSignature hσ w⟩
    rw [← hS, detH_comp Q hQ L v (locBasis_spec v L), rhoLocal_mk]
    have he : localHessDet Q hQ v (locBasis v L) =
        unitsToLocal v (Units.mk0 _ hQ) * (Units.map Matrix.detMonoidHom (locBasis v L)) ^ 2 := by
      apply Units.ext
      simp [localHessDet, unitsToLocal]
    rw [he, map_mul, SqCl.mk_sq_of_mem (Subgroup.mem_top _), mul_one]
  · rintro ⟨⟨α, hα, hsign⟩, t, ht⟩
    exact ⟨t, genStarF_subset_genStar hn S σ 𝕊 c α hα hsign ht⟩

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.remark_7_9
