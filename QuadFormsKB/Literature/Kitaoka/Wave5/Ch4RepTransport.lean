/-
# Transport of representations along isomorphisms of completions of $\mathbb Q$

Helpers for Kitaoka 1993, Corollary 4.1.4 (`Ch4Corollary414.lean`): a representation of rational quadratic forms
over a field $K \supseteq \mathbb Q$ transports along a ring isomorphism $K \cong L$ (`isRepresentedBy_ringEquiv`), in
particular from $\mathbb Q_p$ to the completion of $\mathbb Q$ at the prime $(p)$ of $\mathcal O_{\mathbb Q}$
(`isRepresentedBy_adicCompletion_of_padic`, along Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`).
(Kept apart from `Ch4HassePrinciple.lean`, whose imports change the `Algebra ℚ` instance found on the completion.)
-/
import QuadFormsKB.Equiv.NumberFieldRat
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Witt.Bridge

open NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- Evaluation of a rational form commutes with a ring isomorphism of coefficient fields. -/
theorem evalIn_ringEquiv {K L : Type} [Field K] [Field L] {_ : Algebra ℚ K} {_ : Algebra ℚ L} (e : K ≃+* L)
    {n : ℕ} (Q : RatQF n) (x : Fin n → K) :
    QuadForm.evalIn L Q (fun i => e (x i)) = e (QuadForm.evalIn K Q x) := by
  have hf : ∀ q, e (algebraMap ℚ K q) = algebraMap ℚ L q := fun q => by
    change (e.toRingHom.comp (algebraMap ℚ K)) q = algebraMap ℚ L q
    rw [Subsingleton.elim (e.toRingHom.comp (algebraMap ℚ K)) (algebraMap ℚ L)]
  simp only [QuadForm.evalIn, map_sum, apply_ite e, map_mul, hf, map_zero]

/-- Representations of rational forms transport along a ring isomorphism of fields over $\mathbb Q$. -/
theorem isRepresentedBy_ringEquiv {K L : Type} [Field K] [Field L] {_ : Algebra ℚ K} {_ : Algebra ℚ L}
    (e : K ≃+* L) {m n : ℕ} (QU : RatQF m) (QV : RatQF n)
    (h : OMeara.IsRepresentedBy (QU.toQuadraticFormIn K) (QV.toQuadraticFormIn K)) :
    OMeara.IsRepresentedBy (QU.toQuadraticFormIn L) (QV.toQuadraticFormIn L) := by
  obtain ⟨σ, hσ⟩ := h
  let X : Matrix (Fin n) (Fin m) K := LinearMap.toMatrix' σ.toLinearMap
  have hX : ∀ x, σ x = X.mulVec x := fun x => by
    simp only [X]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective σ.toLinearMap
    (LinearMap.ker_eq_bot.mpr hσ)
  let Y : Matrix (Fin m) (Fin n) K := LinearMap.toMatrix' g
  have hYX : Y * X = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    simp only [Y, X, Matrix.toLin'_toMatrix']
    exact hg
  have hYX' : Y.map e * X.map e = 1 := by
    rw [← Matrix.map_mul, hYX]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmv : ∀ x : Fin m → K, (X.map e).mulVec (fun i => e (x i)) = fun i => e (X.mulVec x i) := by
    intro x; funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  refine ⟨⟨(Matrix.toLin' (X.map e)), fun y => ?_⟩, ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x : Fin m → K, y = fun i => e (x i) :=
      ⟨fun i => e.symm (y i), by funext i; simp⟩
    show (QV.toQuadraticFormIn L) (Matrix.toLin' (X.map e) _) = _
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply, Matrix.toLin'_apply, hmv,
      evalIn_ringEquiv, evalIn_ringEquiv]
    congr 1
    have := σ.map_app x
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply, hX] at this
    exact this
  · intro y y' hyy
    have hyy' : (X.map e).mulVec y = (X.map e).mulVec y' := by
      change Matrix.toLin' (X.map e) y = Matrix.toLin' (X.map e) y' at hyy
      rwa [Matrix.toLin'_apply, Matrix.toLin'_apply] at hyy
    have := congrArg (fun z => (Y.map e).mulVec z) hyy'
    simpa [Matrix.mulVec_mulVec, hYX'] using this

/-- Representations over $\mathbb Q_p$ give representations over the completion of $\mathbb Q$ at the prime $(p)$
of $\mathcal O_{\mathbb Q}$. -/
theorem isRepresentedBy_adicCompletion_of_padic (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    [Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime] {m n : ℕ}
    (QU : RatQF m) (QV : RatQF n)
    (h : OMeara.IsRepresentedBy (QU.toQuadraticFormIn ℚ_[Rat.HeightOneSpectrum.primesEquiv v])
      (QV.toQuadraticFormIn ℚ_[Rat.HeightOneSpectrum.primesEquiv v])) :
    OMeara.IsRepresentedBy (QU.toQuadraticFormIn (v.adicCompletion ℚ)) (QV.toQuadraticFormIn (v.adicCompletion ℚ)) :=
  isRepresentedBy_ringEquiv (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.symm QU QV h

end QuadFormsKB.Kitaoka
