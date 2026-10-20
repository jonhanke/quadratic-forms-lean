/-
# Archimedean test functions of any signature

**Layer:** local analysis at the archimedean places, feeding `ZetaResidue.lean` and `SphericalResidue.lean`.

`ZetaResidue.lean` and `SphericalResidue.lean` take the archimedean test functions $\Phi_w$ as data subject to `IsArchTestFn` ($\Phi_w$ and $|Q_w|\Phi_w$
Lebesgue integrable) and to the hypothesis that the null cones $\{Q_w = 0\}$ are Lebesgue-null. Before this file both were
discharged only for a totally positive definite $Q$ and the Gaussian $e^{-aQ_w}$ (`isArchTestFn_gaussian`,
`ae_realVal_ne_zero`). Here they are discharged for **every nondegenerate $Q$ (any signature at every real place)** and
**every Schwartz function** $\Phi_w \in \mathcal S(\mathbb R^n)$; the complex-place analogues (on $\mathbb C^n$, with
$|\cdot|_{\mathbb C} = |\cdot|^2$) are proved by the same lemmas and used in `SphericalResidueNF.lean`.

**What `SphericalResidue.lean` needs from $\Phi_\infty$** (read off the proofs of `tendsto_mul_globalZeta_zero` and
`tendsto_mul_sphericalZeta_zero`): only real $s \in [0, 1]$ and the limit $s \to 0^+$ occur, and the archimedean factor
enters through
1. $\Phi_w \in L^1$ and $|Q_w|\Phi_w \in L^1$ (`IsArchTestFn`), which give $|Q_w|^s\Phi_w \in L^1$ for $s\in[0,1]$
   (majorant $(1+|Q_w|)|\Phi_w|$) and the continuity $Z_w(s) \to \int\Phi_w$ by dominated convergence;
2. $\{Q_w = 0\}$ Lebesgue-null (so $|Q_w|^s \to 1$ almost everywhere, and the square classes $\{Q_w \in \rho\mathbb R^{\times2}\}$
   cover $\mathbb R^n$ up to a null set);
3. $\Phi_w \ge 0$ (the sandwich $\mu(S) \le \dots \le \mu'(S)$ of Weil p. 108 compares nonnegative series). This one is
   removed in `SphericalResidueNF.lean` by multilinearity ($\Phi_w = \Phi_w^+ - \Phi_w^-$).
No meromorphic continuation and no complex $s$ are used: the residue in Weil's (8) is the limit of $s\,Z(s)$ as $s \to 0^+$.

**Results.**
* `measure_eq_zero_of_lines`: a measurable set meeting every line $x + \mathbb R v$ in a Lebesgue-null set is null for every
  translation-invariant s-finite measure (Tonelli over $t \in [0,1]$; no change of variables).
* `exists_evalIn_ne_zero`: a nondegenerate form in $n \ge 1$ variables over a field takes a nonzero value.
* **`volume_evalIn_eq_zero`**: for $K = \mathbb R$ or $\mathbb C$ (any `RCLike` field) and $P$ a quadratic form over $K$ with a
  nonzero value, $\{P = 0\}$ is null ($t \mapsto P(x + tv)$ is a nonzero polynomial of degree $2$ in $t \in \mathbb R$ when $P(v) \ne 0$).
* **`ae_realVal_ne_zero_of_nondegenerate`**: the real null cones of a nondegenerate $Q$ over $\mathcal O_F$ are null, any signature.
* `norm_evalIn_le`: $\|P(x)\| \le C\|x\|^2$.
* **`isArchTestFn_schwartz`**: every family of Schwartz functions $\Phi_w \in \mathcal S(\mathbb R^n, \mathbb R)$ is admissible.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.ZetaResidue

open IsDedekindDomain NumberField MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ArchTest

open QuadFormsKB.GlobalZeta QuadFormsKB.Siegel Matrix

/-! ### Sets that meet every line in a null set are null -/

/-- **Line averaging.** Let $E$ be a real topological vector space with a translation-invariant s-finite measure $\mu$, $N \subseteq E$
measurable and $v \in E$. If every line $x + \mathbb R v$ meets $N$ in a Lebesgue-null set of parameters, then $\mu(N) = 0$:
$\mu(N) = \int_0^1\mu(N - tv)\,dt = \int_E\int_0^1\mathbf 1_N(x + tv)\,dt\,d\mu(x) = 0$ (Tonelli). -/
theorem measure_eq_zero_of_lines {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] [μ.IsAddRightInvariant] {N : Set E} (hN : MeasurableSet N) (v : E)
    (h : ∀ x : E, volume {t : ℝ | x + t • v ∈ N} = 0) : μ N = 0 := by
  set ν : Measure ℝ := volume.restrict (Set.Icc 0 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  have hcont : Continuous fun p : ℝ × E => p.2 + p.1 • v :=
    continuous_snd.add (continuous_fst.smul continuous_const)
  have hmeas : Measurable fun p : ℝ × E => N.indicator (1 : E → ENNReal) (p.2 + p.1 • v) :=
    (measurable_one.indicator hN).comp hcont.measurable
  have key : ∀ t : ℝ, μ N = ∫⁻ x, N.indicator 1 (x + t • v) ∂μ := by
    intro t
    have hpre : MeasurableSet ((fun x => x + t • v) ⁻¹' N) :=
      hN.preimage (continuous_id.add continuous_const).measurable
    rw [show (fun x => N.indicator (1 : E → ENNReal) (x + t • v)) =
        ((fun x => x + t • v) ⁻¹' N).indicator 1 from by
          ext x; rfl,
      lintegral_indicator_one hpre, measure_preimage_add_right]
  calc μ N = ∫⁻ _ : ℝ, μ N ∂ν := by rw [lintegral_const, hν, mul_one]
    _ = ∫⁻ t, ∫⁻ x, N.indicator 1 (x + t • v) ∂μ ∂ν := lintegral_congr fun t => key t
    _ = ∫⁻ x, ∫⁻ t, N.indicator 1 (x + t • v) ∂ν ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ _ : E, 0 ∂μ := by
        refine lintegral_congr fun x => ?_
        have hpre : MeasurableSet {t : ℝ | x + t • v ∈ N} :=
          hN.preimage (continuous_const.add (continuous_id.smul continuous_const)).measurable
        rw [show (fun t : ℝ => N.indicator (1 : E → ENNReal) (x + t • v)) =
            {t : ℝ | x + t • v ∈ N}.indicator 1 from by
              ext t; simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply],
          lintegral_indicator_one hpre, Measure.restrict_apply hpre]
        exact measure_mono_null Set.inter_subset_left (h x)
    _ = 0 := lintegral_zero

/-! ### Quadratic forms over a field: a nonzero value, the restriction to lines, the null cone -/

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- $P(cx) = c^2P(x)$. -/
lemma evalIn_smul (P : QuadForm K n) (c : K) (x : Fin n → K) : P.evalIn K (c • x) = c ^ 2 * P.evalIn K x := by
  unfold QuadForm.evalIn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, mul_zero]; ring

/-- **$P$ on a line:** $P(x + cv) = P(x) + c\,B(x,v) + c^2P(v)$, $B(x,v) = x^{\mathsf T}Hv$. -/
lemma evalIn_add_smul (P : QuadForm K n) (x v : Fin n → K) (c : K) :
    P.evalIn K (x + c • v) = P.evalIn K x + c * (x ⬝ᵥ (P.hessian.map (algebraMap K K) *ᵥ v)) +
      c ^ 2 * P.evalIn K v := by
  have h := P.polar_eq_hessian K x (c • v)
  rw [evalIn_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h
  linear_combination h

/-- **A nondegenerate form takes a nonzero value** ($n \ge 1$): otherwise the polar form, hence the Hessian, vanishes. -/
theorem exists_evalIn_ne_zero {P : QuadForm K n} (hP : P.Nondegenerate) (hn : 1 ≤ n) :
    ∃ v : Fin n → K, P.evalIn K v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hP
  have hH : P.hessian = 0 := by
    ext i j
    have h := P.polar_eq_hessian K (Pi.single i 1) (Pi.single j 1)
    simp [hcon, Matrix.mulVec, dotProduct, Pi.single_apply] at h
    simpa using h.symm
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hH]; exact Matrix.det_zero

end Field

section RCLike

variable {K : Type*} [RCLike K] {n : ℕ}

/-- **The null cone of a quadratic form over $\mathbb R$ or $\mathbb C$ is null.** If $P(v) \ne 0$, then for every $x$ the map
$t \mapsto P(x + tv)$ ($t \in \mathbb R$) is a polynomial with leading coefficient $P(v)$, so it has at most two zeros; by
`measure_eq_zero_of_lines`, $\mu\{P = 0\} = 0$ for every translation-invariant s-finite $\mu$ on $K^n$. -/
theorem measure_evalIn_eq_zero [MeasurableSpace K] [BorelSpace K] (P : QuadForm K n) {v : Fin n → K}
    (hv : P.evalIn K v ≠ 0) (μ : Measure (Fin n → K)) [SFinite μ] [μ.IsAddRightInvariant] :
    μ {x | P.evalIn K x = 0} = 0 := by
  have hcont : Continuous fun x : Fin n → K => P.evalIn K x := by
    unfold QuadForm.evalIn
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop
  refine measure_eq_zero_of_lines μ (isClosed_eq hcont continuous_const).measurableSet v fun x => ?_
  set b := x ⬝ᵥ (P.hessian.map (algebraMap K K) *ᵥ v)
  set p : Polynomial K := Polynomial.C (P.evalIn K v) * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
    Polynomial.C (P.evalIn K x)
  have hp : p ≠ 0 := by
    intro h0
    have := congrArg (fun q => Polynomial.coeff q 2) h0
    simp [p] at this
    exact hv this
  have hsub : {t : ℝ | x + t • v ∈ {x | P.evalIn K x = 0}} ⊆
      (fun t : ℝ => (t : K)) ⁻¹' (p.roots.toFinset : Set K) := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    have h1 : x + t • v = x + (t : K) • v := by ext i; simp [RCLike.real_smul_eq_coe_mul]
    rw [h1, evalIn_add_smul] at ht
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    linear_combination ht
  exact measure_mono_null hsub ((p.roots.toFinset.finite_toSet.preimage
    (RCLike.ofReal_injective.injOn)).measure_zero _)

/-- $\|P(x)\| \le C\|x\|^2$ with $C = \sum_{i,j}\|c_{ij}\|$ (sup norm on $K^n$). -/
theorem norm_evalIn_le (P : QuadForm K n) (x : Fin n → K) :
    ‖P.evalIn K x‖ ≤ (∑ i, ∑ j, ‖P.coeff i j‖) * ‖x‖ ^ 2 := by
  unfold QuadForm.evalIn
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  split_ifs
  · rw [Algebra.algebraMap_self, RingHom.id_apply, norm_mul, norm_mul, sq, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
      (norm_le_pi_norm x j) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rw [norm_zero]; positivity

end RCLike

/-! ### The real places of a number field -/

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The form $Q_w = \sigma_w(Q)$ at a real place is nondegenerate if $Q$ is ($\sigma_w$ is injective on $\mathcal O_F$). -/
theorem nondegenerate_realForm {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (w : RealPlace F) :
    (realForm Q w).Nondegenerate := by
  set f : 𝓞 F →+* ℝ := (realEmb w).comp (algebraMap (𝓞 F) F)
  have hf : Function.Injective f :=
    (realEmb w).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hH : (realForm Q w).hessian = f.mapMatrix Q.hessian := by
    ext i j; simp [realForm, QuadForm.hessian, QuadForm.map, f]
  unfold QuadForm.Nondegenerate
  rw [hH, ← RingHom.map_det]
  exact fun h => hQ (hf (h.trans f.map_zero.symm))

/-- **The real null cones of a nondegenerate form are null, in every signature** ($n \ge 1$). This discharges the hypothesis
`hnull` of `tendsto_mul_globalZeta_zero` and `tendsto_mul_sphericalZeta_zero` (previously proved only for totally
positive definite $Q$, `ae_realVal_ne_zero`). -/
@[kb "weil1982" "§4.3, p. 89 (V = {F ≠ 0} carries the full measure)"]
theorem ae_realVal_ne_zero_of_nondegenerate {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (w : RealPlace F) : ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_evalIn_ne_zero (nondegenerate_realForm hQ w) hn
  rw [ae_iff]
  simpa [realVal] using measure_evalIn_eq_zero (realForm Q w) hv volume

/-- $|Q_w(x)| \le C\|x\|^2$. -/
lemma abs_realVal_le (Q : QuadForm (𝓞 F) n) (w : RealPlace F) :
    ∃ C, ∀ x : Fin n → ℝ, |realVal Q w x| ≤ C * ‖x‖ ^ 2 :=
  ⟨_, fun x => by simpa [realVal, Real.norm_eq_abs] using norm_evalIn_le (realForm Q w) x⟩

/-- **Every Schwartz function is an admissible archimedean test function**, for every nondegenerate or degenerate $Q$ and
every signature: $\Phi_w \in L^1$ and $|Q_w|\Phi_w \le C\|x\|^2|\Phi_w| \in L^1$ (`SchwartzMap.integrable_pow_mul`). -/
theorem isArchTestFn_schwartz (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → SchwartzMap (Fin n → ℝ) ℝ) :
    IsArchTestFn Q (fun w => Φ w) where
  integrable w := (Φ w).integrable
  integrable_mul w := by
    obtain ⟨C, hC⟩ := abs_realVal_le Q w
    refine (((Φ w).integrable_pow_mul volume 2).const_mul C).mono'
      ((continuous_abs.comp (continuous_realVal Q w)).mul (Φ w).continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, ← Real.norm_eq_abs (Φ w x), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

end QuadFormsKB.ArchTest
