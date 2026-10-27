import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.LocalDensity.NFLocal

/-!
# The Euler product vanishes at the classes not represented over $F$ (proof of `NonrepresentedVanish`)

`NonrepresentedVanish` (in `TauTwoAnisotropic.lean`) was a named input: for $Q_0$ a form over $\mathcal O_F$ and a square
class $c\in F^\times/F^{\times2}$ with representative $\rho$ not represented by $Q = Q_0\otimes F$ over $F$,
Weil's spherical zeta function $Z(s,\rho)$ (`sphericalZetaAtNF`) is $0$ for every $s > 0$. This file proves it for every
**nondegenerate** form $Q_0$ in $k+1\ge1$ variables, so the input is discharged.

**Proof.** Hasse–Minkowski for representations over $F$ (`represents_iff_everywhere_nf`) shows that $Q$ fails to represent
$\rho$ over some completion $F_v$.
* *Complex $v$* is impossible (`representsIn_complex`): a nondegenerate form is not identically zero
  (`exists_qF_ne_zero`), so it takes a value $a\ne0$, and $\sqrt{\rho/a}$ scales a vector to a vector of value $\rho$ in
  an algebraically closed field.
* *Real $v = w$* : if the real form $Q_w$ took a value in $\rho\,\mathbb R^{\times2}$, say $Q_w(x) = \sigma_w(\rho)y^2$, then
  $Q_w(y^{-1}x) = \sigma_w(\rho)$ and, transporting through $F_w\cong\mathbb R$ (`eval_ringEquivReal`), $Q$ would represent
  $\rho$ over $F_w$. So the domain of integration of `sphArchAt` is empty (`sphArchAt_eq_zero`) and the finite product
  over the real places vanishes.
* *Finite $v$* : the same argument with the local form $Q_0\otimes\mathcal O_v$ (`evalIn_Qp`) shows that the domain of
  `sphInt` is empty, so `sphLocal` $=0$ (`sphLocal_eq_zero`), and an infinite product with one zero factor is $0$
  (Mathlib's `tprod_of_exists_eq_zero`).

In every case `sphericalZetaAt` $=0$, hence `sphericalZetaAtNF` $= 0$. The theorem is
`nonrepresentedVanish_of_nondegenerate`; no hypothesis beyond nondegeneracy of $Q_0$ is used.
-/

open MeasureTheory Set Filter Topology
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.SphericalZeta QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta
  QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

/-! ### Square classes and representations -/

/-- If $Q(x) = \rho y^2$ with $y\ne0$ then $Q$ represents $\rho$ (scale by $y^{-1}$). -/
theorem representsIn_of_eq_mul_sq {n : ℕ} {K : Type*} [Field K] [Algebra F K] (Q : QuadForm F n) (ρ : F)
    (x : Fin n → K) {y : K} (hy : y ≠ 0) (h : Q.evalIn K x = algebraMap F K ρ * y ^ 2) :
    Q.RepresentsIn K ρ := by
  refine ⟨y⁻¹ • x, ?_⟩
  rw [QuadFormsKB.Siegel.Kneser.evalIn_smul_gen, h]
  field_simp

/-- Evaluating $Q_0\otimes F$ over a field $K$ that is an $\mathcal O_F$-algebra through $F$ is evaluating $Q_0$. -/
theorem evalIn_map_algebraMap {n : ℕ} (Q : QuadForm (𝓞 F) n) (K : Type*) [Field K] [Algebra F K]
    [Algebra (𝓞 F) K] [IsScalarTower (𝓞 F) F K] (x : Fin n → K) :
    (Q.map (algebraMap (𝓞 F) F)).evalIn K x = Q.evalIn K x := by
  simp [QuadForm.evalIn, QuadForm.map, ← IsScalarTower.algebraMap_apply]

/-! ### Complex places -/

/-- A nondegenerate form in $k+1$ variables over a field of characteristic $0$ takes a nonzero value (otherwise its
polar form, hence its Hessian, vanishes). -/
theorem exists_qF_ne_zero {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) :
    ∃ ξ : Fin (k + 1) → F, qF Q₀ ξ ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hQ
  have hH : (Q₀.map (algebraMap (𝓞 F) F)).hessian = 0 := by
    ext i j
    have := QuadForm.polar_eq_hessian F (Q₀.map (algebraMap (𝓞 F) F)) (Pi.single i 1) (Pi.single j 1)
    have h1 := hall (Pi.single i 1 + Pi.single j 1)
    have h2 := hall (Pi.single i 1)
    have h3 := hall (Pi.single j 1)
    simp only [qF, QuadForm.eval] at h1 h2 h3
    rw [h1, h2, h3] at this
    simpa [Matrix.dotProduct_mulVec] using this.symm
  have hH' : Q₀.hessian.map (algebraMap (𝓞 F) F) = 0 := by
    rw [← hH]; simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
  have : algebraMap (𝓞 F) F Q₀.hessian.det = 0 := by
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hH').trans Matrix.det_zero
  exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 this

/-- At a complex place every nonzero element of $F$ is represented by a nondegenerate form (algebraic closedness). -/
theorem representsIn_complex {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) {ρ : F} (_hρ : ρ ≠ 0)
    {w : InfinitePlace F} (hw : w.IsComplex) :
    (Q₀.map (algebraMap (𝓞 F) F)).RepresentsIn w.Completion ρ := by
  obtain ⟨ξ, hξ⟩ := exists_qF_ne_zero Q₀ hQ
  set E := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  set a : F := qF Q₀ ξ
  have ha : algebraMap F w.Completion a ≠ 0 := (map_ne_zero _).2 hξ
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (E (algebraMap F w.Completion ρ / algebraMap F w.Completion a))
    (n := 2) (by norm_num)
  refine ⟨E.symm s • fun i => algebraMap F w.Completion (ξ i), ?_⟩
  rw [QuadFormsKB.Siegel.Kneser.evalIn_smul_gen]
  have hv : (Q₀.map (algebraMap (𝓞 F) F)).evalIn w.Completion (fun i => algebraMap F w.Completion (ξ i)) =
      algebraMap F w.Completion a := by
    simp only [a, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
      RingHom.id_apply, map_sum, map_mul, apply_ite, map_zero]
  rw [hv]
  have : E.symm s ^ 2 = algebraMap F w.Completion ρ / algebraMap F w.Completion a := by
    apply E.injective
    simpa using hs
  rw [this]
  field_simp

/-! ### Real places -/

/-- The ring isomorphism $F_w\cong\mathbb R$ at a real place sends $F$ to $\sigma_w(F)$. -/
theorem ringEquivReal_algebraMap (w : RealPlace F) (y : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal w.2 (algebraMap F w.1.Completion y) = QuadFormsKB.Siegel.realEmb w y := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe w.2 _

/-- Under $F_w\cong\mathbb R$, the value of $Q_0\otimes F$ at a vector over $F_w$ is the real value $Q_w$. -/
theorem eval_ringEquivReal {n : ℕ} (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (z : Fin n → w.1.Completion) :
    InfinitePlace.Completion.ringEquivRealOfIsReal w.2 ((Q.map (algebraMap (𝓞 F) F)).evalIn w.1.Completion z) =
      realVal Q w (fun i => InfinitePlace.Completion.ringEquivRealOfIsReal w.2 (z i)) := by
  simp [realVal, realForm, QuadForm.evalIn, QuadForm.map, map_sum, map_mul, apply_ite,
    QuadFormsKB.Siegel.realEmb]

/-- **The real factor vanishes** when $Q$ does not represent $\rho$ over the completion at $w$. -/
theorem sphArchAt_eq_zero {n : ℕ} (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (φ : (Fin n → ℝ) → ℝ) (ρ : F) (s : ℝ)
    (h : ¬ (Q.map (algebraMap (𝓞 F) F)).RepresentsIn w.1.Completion ρ) : sphArchAt Q w φ (QuadFormsKB.Siegel.realEmb w ρ) s = 0 := by
  have hempty : realVal Q w ⁻¹' sqClass (QuadFormsKB.Siegel.realEmb w ρ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => h ?_
    obtain ⟨y, hy, hxy⟩ := hx
    set E := InfinitePlace.Completion.ringEquivRealOfIsReal w.2
    refine ⟨fun i => E.symm (y⁻¹ * x i), ?_⟩
    apply E.injective
    rw [eval_ringEquivReal, ringEquivReal_algebraMap]
    have key : ∀ t, InfinitePlace.Completion.ringEquivRealOfIsReal w.2 (E.symm t) = t :=
      fun t => E.apply_symm_apply t
    simp only [key]
    have hh : realVal Q w (fun i => y⁻¹ * x i) = y⁻¹ ^ 2 * realVal Q w x :=
      QuadFormsKB.Siegel.Kneser.evalIn_smul_gen (realForm Q w) x y⁻¹
    rw [hh, show realVal Q w x = QuadFormsKB.Siegel.realEmb w ρ * y ^ 2 from hxy]
    field_simp
  rw [sphArchAt, hempty]
  simp

/-! ### Finite places -/

/-- **The finite factor vanishes** when $Q$ does not represent $\rho$ over $F_v$. -/
theorem sphLocal_eq_zero {n : ℕ} (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : F) (s : ℝ)
    (h : ¬ (Q.map (algebraMap (𝓞 F) F)).RepresentsIn (v.adicCompletion F) ρ) :
    sphLocal Q v (algebraMap F (v.adicCompletion F) ρ) s = 0 := by
  have hempty : latL v n ∩ (NF.Qp v Q).evalIn (v.adicCompletion F) ⁻¹'
      sqClass (algebraMap F (v.adicCompletion F) ρ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => h ?_
    obtain ⟨y, hy, hxy⟩ := hx.2
    refine representsIn_of_eq_mul_sq _ ρ x hy ?_
    rw [evalIn_map_algebraMap, ← NF.evalIn_Qp]
    exact hxy
  rw [sphLocal, sphInt, hempty]
  simp

/-! ### The theorem -/

/-- **The Euler product vanishes at the classes not represented over $F$** (Hasse–Minkowski for representations,
O'Meara 66:3): for every nondegenerate $Q_0$ in $k+1$ variables, $Z(s,\rho) = 0$ whenever $Q_0\otimes F$ does not
represent $\rho\in F^\times$ over $F$. This discharges the input `NonrepresentedVanish` unconditionally. -/
@[kb "omeara1963" "§66, 66:3, p. 189 (Hasse–Minkowski for representations)"]
theorem nonrepresentedVanish_of_nondegenerate {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)
    (Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ) (Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ) :
    NonrepresentedVanish Q₀ Φr Ψ := by
  refine ⟨fun c hc s _ => ?_⟩
  set ρ : F := ((Quotient.out c : Fˣ) : F) with hρdef
  have hρ : ρ ≠ 0 := (Quotient.out c).ne_zero
  have hQF : (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this]
    have h2 : (Q₀.hessian.map (algebraMap (𝓞 F) F)).det = algebraMap (𝓞 F) F Q₀.hessian.det :=
      (RingHom.map_det _ _).symm
    rw [h2]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hQ
  have hnot : ¬ (Q₀.map (algebraMap (𝓞 F) F)).RepresentsIn F ρ := by
    rintro ⟨x, hx⟩
    exact hc ⟨x, by simpa [qF, QuadForm.eval] using hx⟩
  rw [represents_iff_everywhere_nf _ hQF ρ hρ] at hnot
  simp only [NFPlace.Everywhere, NFPlace.atPlace, not_forall] at hnot
  obtain ⟨v, hv⟩ := hnot
  have hzero : sphericalZetaAt Q₀ Φr ρ s = 0 := by
    cases v with
    | infinite w =>
      rcases w.isReal_or_isComplex with hw | hw
      · unfold sphericalZetaAt
        rw [Finset.prod_eq_zero (Finset.mem_univ (⟨w, hw⟩ : RealPlace F)) (sphArchAt_eq_zero Q₀ ⟨w, hw⟩ _ ρ s hv)]
        simp
      · exact absurd (representsIn_complex Q₀ hQ hρ hw) hv
    | finite v =>
      unfold sphericalZetaAt
      rw [tprod_of_exists_eq_zero ⟨v, sphLocal_eq_zero Q₀ v ρ s hv⟩]
      simp
  unfold sphericalZetaAtNF
  rw [hzero, zero_mul]

end QuadFormsKB.Tamagawa.Measure.Weil