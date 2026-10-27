/-
# Consistency checks for Siegel's formula for frames, indefinite case: rank one

For $r = 1$, $T_0 = \langle m\rangle$ (`DVR.unary m`, Hessian $(2m)$), $N = 1 + n'$:
* `ratFrameEquivRatSphere`: the rational frames of $\langle m\rangle$ are the rational vectors with $Q_0(x) = m$;
* `cInfT_unary`: $c_\infty(\langle m\rangle) = c_F(N)\prod_w|2\sigma_w(m)|^{-(N-1)}$, which is `cInf m` of the case $r = 1$;
* `frameDensityProduct_unary`: $|d_F|^{-(N(N-1)-n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L,\langle m\rangle) =
  |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)$, the right side `finDensityProduct` of the case $r = 1$.
* `siegelIndefiniteForms_unary_consistent`: for $r = 1$ the total measures of representations in the two headlines
  (`repMeasureT` with `frameArchFibration`, `repMeasure` with `totallyRealArchFibration`) are equal, after transporting
  $Q$ along $1 + k = k + 1$.
So for $r = 1$ the headline `siegelIndefiniteForms_totallyReal` has the constants and local side of
`siegelIndefinite_release_totallyReal_uncond`; the two measures of representations are both defined from fibrations of the
same Tamagawa measure $\mu_\infty$ with the same constant $c_\infty$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefinite

open MeasureTheory Set Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil LocalDensity

variable {F : Type} [Field F] [NumberField F] {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (1 + n')) (m : 𝓞 F)

theorem compMat_unary_iff (X : Matrix (Fin (1 + n')) (Fin 1) F) :
    (Q₀.map (algebraMap (𝓞 F) F)).compMat X = (DVR.unary m).map (algebraMap (𝓞 F) F) ↔
      qF Q₀ (fun i => X i 0) = algebraMap (𝓞 F) F m := by
  refine QuadForm.ext_iff.trans ?_
  refine (Matrix.ext_iff (m := Fin 1) (n := Fin 1)).symm.trans ?_
  simp only [Fin.forall_fin_one, QuadForm.compMat_coeff]
  simp [DVR.unary, QuadForm.map, QuadForm.diag, qF]

/-- The rational frames of $\langle m\rangle$ are the rational vectors of value $m$. -/
def ratFrameEquivRatSphere : RatFrame Q₀ (DVR.unary m) ≃ RatSphere Q₀ (algebraMap (𝓞 F) F m) where
  toFun X := ⟨fun i => X.1 i 0, (compMat_unary_iff Q₀ m X.1).1 X.2⟩
  invFun η := ⟨Matrix.of fun i _ => η.1 i, (compMat_unary_iff Q₀ m _).2 η.2⟩
  left_inv X := Subtype.ext (by ext i j; rw [Subsingleton.elim j 0]; rfl)
  right_inv η := rfl

/-- $c_\infty(\langle m\rangle)$ is the archimedean constant `cInf m` of the case $r = 1$. -/
theorem cInfT_unary : cInfT Q₀ (DVR.unary m) = cInf (k := n') (algebraMap (𝓞 F) F m) := by
  have hdet : algebraMap (𝓞 F) F (DVR.unary m).hessian.det = 2 * algebraMap (𝓞 F) F m := by
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag, two_mul]
  rw [cInfT, cInf, Finset.prod_const_one, mul_one, add_comm 1 n']
  simp only [hdet, map_mul, map_ofNat]

/-- The local side for $r = 1$: $|d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)$. -/
theorem frameDensityProduct_unary :
    frameDensityProduct Q₀ (DVR.unary m) =
      |(discr F : ℝ)| ^ (-(((1 + n' : ℕ) : ℝ) - 1) / 2) * ∏' v : HeightOneSpectrum (𝓞 F), NF.localDensity v Q₀ m := by
  rw [frameDensityProduct]
  simp only [NF.localDensityForm_unary]
  congr 2
  push_cast
  ring

/-! ### Transport along $1 + k = k + 1$ -/

section Transport

variable {R : Type} {N M : ℕ}

theorem nondegenerate_transport [CommRing R] (h : N = M) {Q : QuadForm R N} (hQ : Q.Nondegenerate) :
    (h ▸ Q : QuadForm R M).Nondegenerate := by subst h; exact hQ

theorem tsum_unitVolume_transport (h : N = M) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) :
    ∑' i, unitVolume (h ▸ Q : QuadForm (𝓞 F) M) (nondegenerate_transport h hQ) i = ∑' i, unitVolume Q hQ i := by
  subst h; rfl

theorem localDensity_transport (h : N = M) (Q : QuadForm (𝓞 F) N) (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) :
    NF.localDensity v (h ▸ Q : QuadForm (𝓞 F) M) m = NF.localDensity v Q m := by
  subst h; rfl

theorem nonempty_ratSphere_transport (h : N = M) (Q : QuadForm (𝓞 F) N) (x : F)
    (ξ : RatSphere Q x) : Nonempty (RatSphere (h ▸ Q : QuadForm (𝓞 F) M) x) := by
  subst h; exact ⟨ξ⟩

end Transport

theorem unary_nondegenerate {m : 𝓞 F} (hm : (m : F) ≠ 0) : (DVR.unary m).Nondegenerate := by
  have hdet : algebraMap (𝓞 F) F (DVR.unary m).hessian.det = 2 * algebraMap (𝓞 F) F m := by
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag, two_mul]
  intro h0
  rw [h0, map_zero] at hdet
  rcases mul_eq_zero.1 hdet.symm with h | h
  · exact two_ne_zero h
  · exact hm h

/-- **Consistency for $r = 1$**: the frame headline and the $r = 1$ headline give the same total measure of the
representations of $m$ (the form $Q_1$ in $1 + k$ variables is transported to $k + 1$ variables along `Nat.add_comm`). -/
theorem siegelIndefiniteForms_unary_consistent [IsTotallyReal F] {k : ℕ} (hk : 3 ≤ k)
    (Q₁ : QuadForm (𝓞 F) (1 + k)) (hQ₁ : Q₁.Nondegenerate) {m : 𝓞 F} (hm : (m : F) ≠ 0)
    (Ξ : RatFrame Q₁ (DVR.unary m)) :
    ∑' i, repMeasureT Q₁ (DVR.unary m) hQ₁
        (frameArchFibration Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ) i =
      ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) (m : F)
        (totallyRealArchFibration _ (nondegenerate_transport _ hQ₁) hm (by omega)) i := by
  have hT := unary_nondegenerate hm
  have h1 := siegelIndefiniteForms_totallyReal Q₁ hQ₁ (DVR.unary m) hT hk Ξ le_rfl
  obtain ⟨ξ⟩ := nonempty_ratSphere_transport (Nat.add_comm 1 k) Q₁ _ (ratFrameEquivRatSphere Q₁ m Ξ)
  have h2 := siegelIndefinite_release_totallyReal_uncond (nondegenerate_transport (Nat.add_comm 1 k) hQ₁) hk hm ξ
  have e : cInf (k := k) (m : F) = cInfT Q₁ (DVR.unary m) := (cInfT_unary Q₁ m).symm
  set B := ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) (m : F)
        (totallyRealArchFibration _ (nondegenerate_transport _ hQ₁) hm (by omega)) i with hB
  clear_value B
  rw [e] at h2
  have hd : frameDensityProduct Q₁ (DVR.unary m) =
      finDensityProduct (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) m := by
    rw [frameDensityProduct_unary, finDensityProduct]
    simp only [localDensity_transport]
    congr 2
    push_cast
    ring
  rw [hd, ← tsum_unitVolume_transport (Nat.add_comm 1 k) Q₁ hQ₁] at h1
  have hc := cInfT_ne_zero_top Q₁ (DVR.unary m) hT
  exact (ENNReal.mul_right_inj hc.1 hc.2).1 (h1.trans h2.symm)

end QuadFormsKB.Tamagawa.Indefinite
