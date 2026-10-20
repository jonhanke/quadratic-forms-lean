import QuadFormsKB.Analysis.MinkowskiPoisson

/-!
# Poisson summation for the lattice of a basis, with a bilinear pairing

**Layer:** real analysis; no number theory. Generic and upstreamable.

Let $W$ be a finite-dimensional real vector space with an additive Haar measure $\mu$ and a bilinear form
$\beta : W\times W\to\mathbb R$, let $b = (b_j)$ be a basis of $W$ and $b^\vee = (b_j^\vee)$ vectors with
$\beta(b_i, b_j^\vee) = \delta_{ij}$ (a dual basis for $\beta$). For a Schwartz function $f$ on $W$ and $u\in W$,
**`poisson_basis`**:
$$\sum_{k\in\mathbb Z^N} f\Big(u + \sum_j k_jb_j\Big) = \mu(P_b)^{-1}\sum_{m\in\mathbb Z^N}
  \hat f_\beta\Big(\sum_j m_jb_j^\vee\Big)\,e\Big(-\beta\big(u, \textstyle\sum_j m_jb_j^\vee\big)\Big),\qquad
  \hat f_\beta(z) = \int_W f(y)\,e(\beta(y, z))\,d\mu(y),$$
$P_b$ the parallelepiped of $b$. *Proof:* transport the standard Poisson formula on $\mathbb Z^N\subset\mathbb R^N$
(`poissonSummation_standard`, vendored from Sphere-Packing-Lean) along the coordinate map $t\mapsto\sum_j t_jb_j$, whose
push-forward of Lebesgue measure is $\mu(P_b)^{-1}\mu$, and for which $\langle T^{-1}y, m\rangle = \beta(y, \sum_j m_jb_j^\vee)$.
This generalizes the coordinate argument of `poisson_fractionalIdeal` (`Analysis/MinkowskiPoisson.lean`).
-/

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] {N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin N)

/-- The coordinate map $\mathbb R^N\to W$, $t\mapsto\sum_j t_jb_j$. -/
def basisT (b : Module.Basis (Fin N) ℝ W) : E ≃L[ℝ] W :=
  ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis.equiv b (Equiv.refl _)).toContinuousLinearEquiv

theorem basisT_single (b : Module.Basis (Fin N) ℝ W) (j : Fin N) :
    basisT b (EuclideanSpace.single j 1) = b j := by
  rw [← EuclideanSpace.basisFun_apply, ← OrthonormalBasis.coe_toBasis]
  change ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis.equiv b (Equiv.refl _)) _ = _
  rw [Module.Basis.equiv_apply]
  rfl

theorem intVec_eq_sum' (k : Fin N → ℤ) :
    SchwartzMap.PoissonSummation.Standard.intVec (d := N) k =
      ∑ j, (k j : ℝ) • EuclideanSpace.single j (1 : ℝ) := by
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec, Pi.single_apply]

theorem basisT_intVec (b : Module.Basis (Fin N) ℝ W) (k : Fin N → ℤ) :
    basisT b (SchwartzMap.PoissonSummation.Standard.intVec (d := N) k) = ∑ j, (k j : ℝ) • b j := by
  rw [intVec_eq_sum', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, basisT_single]

theorem inner_basisT_symm (b : Module.Basis (Fin N) ℝ W) (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W)
    (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0) (y : W) (m : Fin N → ℤ) :
    ⟪(basisT b).symm y, SchwartzMap.PoissonSummation.Standard.intVec (d := N) m⟫ =
      β y (∑ j, (m j : ℝ) • bd j) := by
  let L1 : W →ₗ[ℝ] ℝ := (innerSL ℝ (SchwartzMap.PoissonSummation.Standard.intVec
    (d := N) m)).toLinearMap ∘ₗ (basisT b).symm.toLinearMap
  let L2 : W →ₗ[ℝ] ℝ := β.flip (∑ j, (m j : ℝ) • bd j)
  have h : L1 = L2 := by
    refine b.ext fun i => ?_
    rw [← basisT_single]
    show ⟪SchwartzMap.PoissonSummation.Standard.intVec (d := N) m,
        (basisT b).symm ((basisT b) (EuclideanSpace.single i 1))⟫ =
      β ((basisT b) (EuclideanSpace.single i 1)) (∑ j, (m j : ℝ) • bd j)
    rw [ContinuousLinearEquiv.symm_apply_apply, basisT_single, EuclideanSpace.inner_single_right, map_sum]
    simp only [map_smul, hbd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp [SchwartzMap.PoissonSummation.Standard.intVec]
  have := congrArg (fun L : W →ₗ[ℝ] ℝ => L y) h
  simp only [L1, L2, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.flip_apply] at this
  rw [real_inner_comm]
  exact this

/-- The push-forward of Lebesgue measure under the coordinate map is $\mu(P_b)^{-1}\mu$. -/
theorem map_basisT_volume (μ : Measure W) [μ.IsAddHaarMeasure] (b : Module.Basis (Fin N) ℝ W) :
    Measure.map (basisT b) (volume : Measure E) = (μ b.parallelepiped)⁻¹ • μ := by
  rw [← (EuclideanSpace.basisFun (Fin N) ℝ).addHaar_eq_volume, Module.Basis.map_addHaar]
  have hb : (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.map ((basisT b : E ≃L[ℝ] W) : E ≃ₗ[ℝ] W) = b := by
    change _ = b
    have := Module.Basis.map_equiv (EuclideanSpace.basisFun (Fin N) ℝ).toBasis b (Equiv.refl _)
    rw [Equiv.refl_symm, Module.Basis.reindex_refl] at this
    exact this
  have h0 : μ b.parallelepiped ≠ 0 :=
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'
  have htop : μ b.parallelepiped ≠ ⊤ := b.parallelepiped.isCompact.measure_lt_top.ne
  haveI : ((μ b.parallelepiped)⁻¹ • μ).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0)
  rw [hb, Module.Basis.addHaar_eq_iff, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

/-- **Poisson summation for the lattice of a basis**, with the Fourier transform taken for a bilinear form $\beta$ for
which $b^\vee$ is dual to $b$. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem poisson_basis (μ : Measure W) [μ.IsAddHaarMeasure] (b : Module.Basis (Fin N) ℝ W)
    (β : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (bd : Fin N → W) (hbd : ∀ i j, β (b i) (bd j) = if i = j then 1 else 0)
    (f : SchwartzMap W ℂ) (u : W) :
    ∑' k : Fin N → ℤ, f (u + ∑ j, (k j : ℝ) • b j) =
      ((μ b.parallelepiped).toReal⁻¹ : ℝ) * ∑' m : Fin N → ℤ,
        (∫ y, f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) ∂μ) *
          ((𝐞 (-β u (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) := by
  set T := basisT b
  set g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f with hg
  have hgx : ∀ t, g t = f (T t) := fun t => rfl
  set v : E := T.symm u
  have hP := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard (d := N) g v
  rw [← (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := N)).tsum_eq] at hP
  have hL : ∀ k : Fin N → ℤ, g (v + ((SchwartzMap.PoissonSummation.Standard.equivIntVec (d := N) k :
      SchwartzMap.standardLattice _) : E)) = f (u + ∑ j, (k j : ℝ) • b j) := by
    intro k
    rw [hgx, map_add, ContinuousLinearEquiv.apply_symm_apply]
    change f (_ + T (SchwartzMap.PoissonSummation.Standard.intVec k)) = _
    rw [basisT_intVec]
  simp_rw [hL] at hP
  simp only [← RCLike.inner_eq_wInner_one] at hP
  rw [hP]
  have hpar : 0 < (μ b.parallelepiped).toReal := ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'
    b.parallelepiped.isCompact.measure_lt_top.ne
  rw [← tsum_mul_left, ← (Equiv.neg (Fin N → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply]
  -- the Fourier coefficient
  have hF : 𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec (-m)) =
      ((μ b.parallelepiped).toReal⁻¹ : ℝ) *
        ∫ y, f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) ∂μ := by
    set h : W → ℂ := fun y => f y * ((𝐞 (β y (∑ j, (m j : ℝ) • bd j)) : Circle) : ℂ) with hh
    have h1 : 𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec (-m)) =
        ∫ t, h (T t) := by
      rw [Real.fourier_eq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have : ⟪t, SchwartzMap.PoissonSummation.Standard.intVec (d := N) (-m)⟫ =
          -β (T t) (∑ j, (m j : ℝ) • bd j) := by
        rw [← inner_basisT_symm b β bd hbd (T t) m, ContinuousLinearEquiv.symm_apply_apply]
        have : SchwartzMap.PoissonSummation.Standard.intVec (d := N) (-m) =
            -SchwartzMap.PoissonSummation.Standard.intVec (d := N) m := by
          ext i; simp [SchwartzMap.PoissonSummation.Standard.intVec]
        rw [this, inner_neg_right]
      simp only [hh, hgx, Circle.smul_def, smul_eq_mul, this, neg_neg]
      ring
    have h2 : ∫ t, h (T t) = ∫ y, h y ∂(Measure.map T (volume : Measure E)) := by
      rw [show (Measure.map T (volume : Measure E)) =
        Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
      rfl
    rw [h1, h2, map_basisT_volume μ b, integral_smul_measure, ENNReal.toReal_inv]
    rw [Complex.real_smul, ofReal_inv]
  rw [hF]
  have hphase : ⟪v, SchwartzMap.PoissonSummation.Standard.intVec (d := N) (-m)⟫ =
      -β u (∑ j, (m j : ℝ) • bd j) := by
    have : SchwartzMap.PoissonSummation.Standard.intVec (d := N) (-m) =
        -SchwartzMap.PoissonSummation.Standard.intVec (d := N) m := by
      ext i; simp [SchwartzMap.PoissonSummation.Standard.intVec]
    rw [this, inner_neg_right, inner_basisT_symm b β bd hbd u m]
  rw [hphase, ← QuadFormsKB.Analysis.fourierChar_coe_eq_exp]
  push_cast
  ring


/-- The lattice sum of a Schwartz function converges absolutely. -/
theorem summable_basis (b : Module.Basis (Fin N) ℝ W) (f : SchwartzMap W ℂ) :
    Summable fun k : Fin N → ℤ => ‖f (∑ j, (k j : ℝ) • b j)‖ := by
  set g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (basisT b) f
  let K : TopologicalSpace.Compacts E := ⟨{0}, isCompact_singleton⟩
  have h := SchwartzMap.PoissonSummation.Standard.summable_norm_translate_restrict (d := N) g K
  have h' := (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := N)).summable_iff.mpr h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h'
  have hle := ContinuousMap.norm_coe_le_norm ((SchwartzMap.PoissonSummation.Standard.translate (d := N) g
    (SchwartzMap.PoissonSummation.Standard.equivIntVec k)).restrict K) ⟨0, rfl⟩
  have hval : ((SchwartzMap.PoissonSummation.Standard.translate (d := N) g
      (SchwartzMap.PoissonSummation.Standard.equivIntVec k)).restrict K) ⟨0, rfl⟩ =
      f (∑ j, (k j : ℝ) • b j) := by
    simp only [ContinuousMap.restrict_apply, SchwartzMap.PoissonSummation.Standard.translate_apply, zero_add]
    change f (basisT b (SchwartzMap.PoissonSummation.Standard.intVec k)) = _
    rw [basisT_intVec]
  rw [hval] at hle
  exact hle

end

end QuadFormsKB.Tamagawa.Measure.Weil
