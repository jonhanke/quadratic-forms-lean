/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF

/-!
# Paper 6, Remark 3.2: the signature vector of a quadratic space

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Rem. 3.2, p. 12.

Remark 3.2: "one obtains a vector of signatures of rank $n$ naturally from any $n$-dimensional non-degenerate quadratic
space $(V,Q)$ over $F$, and this vector determines the product of (non-degenerate) quadratic spaces
$\prod_{v\mid\infty}(V_v,Q_v)$ up to isomorphism." With `HasSignature Q σ` ($Q \cong \langle 1^{\sigma_{v,+}},
(-1)^{\sigma_{v,-}}\rangle$ over $F_v$ at every real place $v$, `Lemma37.lean`), for a nondegenerate form $Q$ in $n$ variables
over a number field $F$:

* `remark_3_2_exists`: $Q$ has a signature vector (Sylvester: $\sigma_{v,-}$ is the number of negative entries of a
  diagonalization of $Q$ under the real embedding $v$, `LocalClassNF.realNegIndex`);
* `remark_3_2_unique`: it is unique (Sylvester's law of inertia);
* `remark_3_2_determines`: two nondegenerate forms with the same signature vector are isometric over $F_v$ at **every**
  archimedean place $v$ (real places: both are $\cong \langle 1^{\sigma_{v,+}}, (-1)^{\sigma_{v,-}}\rangle$; complex places: all
  nondegenerate forms of dimension $n$ over $\mathbb C$ are isometric), i.e. the vector determines
  $\prod_{v\mid\infty}(V_v,Q_v)$; and conversely (`remark_3_2_iff`) forms isometric at every real place have the same vector.

Indices are 0-based.
-/

namespace QuadFormsKB.Hanke2011Structure

open NumberField QuadFormsKB.LocalClassNF

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- `HasSignature` in terms of the form over $F$ evaluated in $F_v$ (no base change of the coefficients). -/
theorem hasSignature_iff (Q : QuadForm F n) (σ : SignatureVector F n) :
    HasSignature Q σ ↔ ∀ w : {w : InfinitePlace F // w.IsReal},
      Q.IsometricIn w.1.Completion (QuadForm.diag (sigVec F (σ w))) := by
  unfold HasSignature
  refine forall_congr' fun w => ?_
  constructor
  · rintro ⟨P, hP, hx⟩
    exact ⟨P, hP, fun x => by
      have := hx x
      rwa [OMeara.evalIn_map_algebraMap, OMeara.evalIn_map_algebraMap] at this⟩
  · intro h
    exact OMeara.isometricIn_map_of_isometricIn _ h

/-- The number of negative entries of the sign vector of signature $(\sigma_+,\sigma_-)$ is $\sigma_-$. -/
theorem realNegCount_sigVec (w : InfinitePlace F) (hw : w.IsReal) (p : SigPair n) :
    realNegCount w hw (sigVec F p) = p.1.2 := by
  classical
  unfold realNegCount
  have e : (Finset.univ.filter fun i : Fin n => w.embedding_of_isReal hw (sigVec F p i) < 0) =
      Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < p.1.1 := by
    ext i
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, sigVec]
    by_cases h : (i : ℕ) < p.1.1 <;> simp [h]
  rw [e, Finset.card_filter]
  have h1 : (∑ i : Fin n, if ¬ (i : ℕ) < p.1.1 then 1 else 0) = ∑ i : Fin n, if (i : ℕ) < p.1.1 then 0 else 1 :=
    Finset.sum_congr rfl fun i _ => by split_ifs <;> simp_all
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if i < p.1.1 then 0 else 1) n, sum_range_not_lt]
  have := p.2
  omega

/-- The real negative index of the sign vector form of signature $(\sigma_+,\sigma_-)$ is $\sigma_-$. -/
theorem realNegIndex_sigVec (w : InfinitePlace F) (hw : w.IsReal) (p : SigPair n) :
    realNegIndex w hw (QuadForm.diag (sigVec F p)) = p.1.2 := by
  have hnd : (QuadForm.diag (sigVec F p)).Nondegenerate := OMeara.nondegenerate_diag _ (sigVec_ne_zero F p)
  rw [realNegIndex_eq_of_isometric w hw hnd (sigVec_ne_zero F p) (QuadForm.isometricIn_refl F _),
    realNegCount_sigVec]

theorem sigVec_nondegenerate (p : SigPair n) : (QuadForm.diag (sigVec F p)).Nondegenerate :=
  OMeara.nondegenerate_diag _ (sigVec_ne_zero F p)

/-- At a real place, $Q \cong \langle 1^{\sigma_+}, (-1)^{\sigma_-}\rangle$ over $F_v$ iff $\sigma_-$ is the negative index of $Q$. -/
theorem isometricIn_sigVec_iff (w : InfinitePlace F) (hw : w.IsReal) {Q : QuadForm F n} (hQ : Q.Nondegenerate)
    (p : SigPair n) : Q.IsometricIn w.Completion (QuadForm.diag (sigVec F p)) ↔ realNegIndex w hw Q = p.1.2 := by
  rw [isometric_real_iff_general w hw Q _ hQ (sigVec_nondegenerate p), realNegIndex_sigVec]

theorem realNegIndex_le (w : InfinitePlace F) (hw : w.IsReal) (Q : QuadForm F n) : realNegIndex w hw Q ≤ n := by
  unfold realNegIndex realNegCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **Remark 3.2 (existence):** every nondegenerate quadratic form $Q$ in $n$ variables over a number field $F$ has a signature
vector: at each real place $v$, $\sigma_{v,-}$ = the negative index of $Q$ under $v$ and $\sigma_{v,+} = n - \sigma_{v,-}$. -/
@[kb "hanke2011structure" "Rem. 3.2, p. 12 (a quadratic space gives a signature vector)"]
theorem remark_3_2_exists (Q : QuadForm F n) (hQ : Q.Nondegenerate) : ∃ σ : SignatureVector F n, HasSignature Q σ := by
  let σ : SignatureVector F n := fun w => (⟨(n - realNegIndex w.1 w.2 Q, realNegIndex w.1 w.2 Q), by
    have := realNegIndex_le w.1 w.2 Q; simp only; omega⟩ : SigPair n)
  refine ⟨σ, ?_⟩
  rw [hasSignature_iff]
  intro w
  exact (isometricIn_sigVec_iff w.1 w.2 hQ _).mpr rfl

/-- **Remark 3.2 (uniqueness):** the signature vector of a nondegenerate form is unique (Sylvester's law of inertia). -/
@[kb "hanke2011structure" "Rem. 3.2, p. 12 (uniqueness of the signature vector)"]
theorem remark_3_2_unique {Q : QuadForm F n} (hQ : Q.Nondegenerate) {σ σ' : SignatureVector F n}
    (h : HasSignature Q σ) (h' : HasSignature Q σ') : σ = σ' := by
  rw [hasSignature_iff] at h h'
  funext w
  have e1 := (isometricIn_sigVec_iff w.1 w.2 hQ _).mp (h w)
  have e2 := (isometricIn_sigVec_iff w.1 w.2 hQ _).mp (h' w)
  have s1 := (σ w).2
  have s2 := (σ' w).2
  apply Subtype.ext
  apply Prod.ext
  · omega
  · omega

/-- **Remark 3.2 (the signature vector determines the archimedean completions):** two nondegenerate forms $Q$, $Q'$ in $n$
variables over $F$ with the same signature vector are isometric over $F_v$ at every archimedean place $v$ (real or complex),
so the vector determines $\prod_{v\mid\infty}(V_v,Q_v)$ up to isomorphism. -/
@[kb "hanke2011structure" "Rem. 3.2, p. 12 (the vector determines the product of the archimedean spaces)"]
theorem remark_3_2_determines {Q Q' : QuadForm F n} (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    {σ : SignatureVector F n} (h : HasSignature Q σ) (h' : HasSignature Q' σ) (w : InfinitePlace F) :
    Q.IsometricIn w.Completion Q' := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [hasSignature_iff] at h h'
    exact QuadForm.isometricIn_trans _ (h ⟨w, hw⟩) (QuadForm.isometricIn_symm _ (h' ⟨w, hw⟩))
  · exact isometric_complex_general w hw Q Q' hQ hQ'

/-- **Remark 3.2 (converse):** nondegenerate forms isometric over $F_v$ at every real place have the same signature vector. -/
@[kb "hanke2011structure" "Rem. 3.2, p. 12 (converse)"]
theorem remark_3_2_iff {Q Q' : QuadForm F n} (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    {σ σ' : SignatureVector F n} (h : HasSignature Q σ) (h' : HasSignature Q' σ') :
    σ = σ' ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, Q.IsometricIn w.1.Completion Q' := by
  constructor
  · rintro rfl w
    exact remark_3_2_determines hQ hQ' h h' w.1
  · intro hiso
    refine remark_3_2_unique hQ h ?_
    rw [hasSignature_iff] at h' ⊢
    exact fun w => QuadForm.isometricIn_trans _ (hiso w) (h' w)

end

end QuadFormsKB.Hanke2011Structure
