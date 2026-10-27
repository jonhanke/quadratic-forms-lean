/-
# Siegel's formula for frames in Weil's form, for any complement rank $n'\ge1$

**Layer:** number fields, adeles. Frame coordinates `D : FrameTower Q₀ hQ n' (cols Ξ.1)` of a rational frame $\Xi$ of
$T_0$, $N = r + n'\ge3$, $n'\ge1$. `siegelFormsWeil` (`FrameSiegelReduce.lean`) assumes $n'\ge3$ and
$\tau(SO(Q'')) = 2$ for `muTam Q'' 1`; for $n' = 2$ that measure is not Weil's, so here the covolume
$t_H = \operatorname{covol}(SO(Q'')(F)\backslash SO(Q'')(\mathbb A),\ \texttt{muTam Q'' 1})$ is kept as it is:

* `lintegral_testFnT_eq_gen`: `lintegral_testFnT_eq` for $N\ge3$, $n'\ge1$;
* **`siegelFormsWeil_gen`**: if $\tau(SO(V)) = 2$, then
  $2\sum_i\rho^{\mathrm{Tam}}(M_i,T_0) = t_H\cdot\texttt{frameOrbitSum}\cdot\sum_iv(M_i)$.
* **`frameOrbitSum_lam`**: the orbit sum computed with the stabilizer measure `muFin Q'' λ` (any convergence factors
  $\lambda_v>0$ with $\prod_v\lambda_v^{-1}\alpha_v(L'')$ absolutely convergent and nonzero) is the product of the local
  factors $\beta_\mathfrak p(L,T_0)\,|\det g|_\mathfrak p^{n'+1}|\det H_{T_0}|_\mathfrak p^{-n'}\,\lambda_\mathfrak p$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameDensities
import QuadFormsKB.Tamagawa.Indefinite.FrameSiegelReduce

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1))

/-- `lintegral_testFnT_eq` for every $n'\ge1$ with $N = r + n'\ge3$. -/
theorem lintegral_testFnT_eq_gen (hn : 1 ≤ n') (hN : 3 ≤ r + n') {Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ p, testFnT Φ (D.τ p) ∂D.σ = frameOrbitSum Q₀ hQ T₀ Ξ D * ∫⁻ t, Φ t.1 ∂frameσA Q₀ hQ T₀ Ξ D := by
  classical
  have hn0 : 0 < n' := by omega
  have := D.sFinite
  have := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
  have := isMulRightInvariant_muFin D.Q'' D.hQ'' hn0
  have := isMulRightInvariant_muArchTamSO D.Q'' D.hQ''
  have hfib : (muArchTamSO Q₀ hQ).prod (muFin Q₀ fun _ => 1) =
      (D.σ.prod ((muArchTamSO D.Q'' D.hQ'').prod (muFin D.Q'' fun _ => 1))).map
        (frameCprod Q₀ hQ T₀ Ξ D).coord := D.fib
  have hA := frameσA_fib Q₀ hQ T₀ Ξ D
  have hU := exists_refSetInf Q₀ hQ T₀ Ξ D
  have hK : MeasurableSet (KSO Q₀ : Set (SOAf Q₀)) := (isOpen_KSO Q₀).measurableSet
  have hK0 : muFin Q₀ (fun _ => 1) (KSO Q₀ : Set (SOAf Q₀)) ≠ 0 := by
    rw [muFin_KSO]
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    rw [finFactor_one Q₀ hQ]
    exact tprod_siegelDensity_pos hN Q₀ hQ
  have hKt : muFin Q₀ (fun _ => 1) (KSO Q₀ : Set (SOAf Q₀)) ≠ ⊤ := by
    rw [muFin_KSO]; exact ENNReal.ofReal_ne_top
  obtain ⟨X, hXm, hX0, hXt⟩ := orb_exists_X (frameCA Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ) (muArchTamSO D.Q'' D.hQ'')
    (frameσA Q₀ hQ T₀ Ξ D) hA (frameσA_ne_zero Q₀ hQ T₀ Ξ D) hU
  have hKO : ∀ i : FinOrbit Q₀ T₀ Ξ, muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ i)) ≠ 0 ∧
      muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ i)) ≠ ⊤ := fun i =>
    orb_orbStab_ne (frameCprod Q₀ hQ T₀ Ξ D) (stabIn_frameCprod Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ)
      (muFin Q₀ fun _ => 1) (muArchTamSO D.Q'' D.hQ'') (muFin D.Q'' fun _ => 1) D.σ hfib (KSO Q₀) hK
      (finOrbitRep Q₀ T₀ Ξ i) hXm hX0 hXt hK0 hKt D.measurable_ιInf
      (orb_measurableSet_orbit Q₀ hQ T₀ Ξ D _)
  have key := lintegral_testFn_orbits (frameCprod Q₀ hQ T₀ Ξ D) (stabIn_frameCprod Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ)
    (muFin Q₀ fun _ => 1) (muArchTamSO D.Q'' D.hQ'') (muFin D.Q'' fun _ => 1) D.σ hfib
    (frameCA Q₀ hQ T₀ Ξ D) (frameσA Q₀ hQ T₀ Ξ D) hA (orb_measurable_projA Q₀ hQ T₀ Ξ D) (KSO Q₀) hK
    (finOrbitRep Q₀ T₀ Ξ) (fun i => orb_measurableSet_orbit Q₀ hQ T₀ Ξ D _) (fun i => (hKO i).1)
    (fun i => (hKO i).2) hU (latHatT F (r + n') r) (orb_disjoint Q₀ T₀ Ξ) (orb_cover Q₀ hQ T₀ Ξ D) Φ hΦ
  refine key.trans ?_
  rw [frameOrbitSum, ENNReal.tsum_mul_right]

set_option maxHeartbeats 800000 in
/-- **Siegel's formula for frames in Weil's form, any complement rank** ($n'\ge1$, $N\ge3$): if $\tau(SO(V)) = 2$, then
$$2\sum_i\rho^{\mathrm{Tam}}(M_i, T_0) = t_H\cdot\texttt{frameOrbitSum}\cdot\sum_iv(M_i),\qquad
  t_H = \operatorname{covol}(SO(Q'')(F)\backslash SO(Q'')(\mathbb A),\ \texttt{muTam Q'' 1}).$$ -/
theorem siegelFormsWeil_gen (hT : T₀.Nondegenerate) (hn : 1 ≤ n') (hN : 3 ≤ r + n')
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) :
    2 * ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i =
      covolume (GammaSOAdele D.Q'') (SOAdele D.Q'') (muTam D.Q'' D.hQ'' fun _ => 1) *
        (frameOrbitSum Q₀ hQ T₀ Ξ D * ∑' i, unitVolume Q₀ hQ i) := by
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  have := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have hEf : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  -- a test function with `0 < ∫ Φ dσA < ∞`
  obtain ⟨S, hSm, hS0, hSt⟩ := OrbitSection.exists_pos_lt_top (frameσA Q₀ hQ T₀ Ξ D)
    (frameσA_ne_zero Q₀ hQ T₀ Ξ D)
  obtain ⟨A, hAm, hAS⟩ := MeasurableSpace.measurableSet_comap.1 hSm
  set Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞ := A.indicator 1 with hΦdef
  have hΦ : Measurable Φ := measurable_one.indicator hAm
  have hI : ∫⁻ t, Φ t.1 ∂frameσA Q₀ hQ T₀ Ξ D = frameσA Q₀ hQ T₀ Ξ D S := by
    have : (fun t : factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ) => Φ t.1) = S.indicator 1 := by
      funext t
      rw [← hAS]; rfl
    rw [this, lintegral_indicator_one hSm]
  have hP : ∀ X : RatFrame Q₀ T₀, ratAT Q₀ T₀ X ∈ Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ := by
    intro X
    obtain ⟨γ, rfl⟩ := exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ D hT hn X
    exact ⟨(γ : SOAdele Q₀).1, (ratAT_smul Q₀ T₀ γ Ξ).symm⟩
  have h1 := lintegral_theta_classicalT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) hP Φ hΦ
    (hΦ.comp measurable_subtype_coe) hEf
  rw [lintegral_theta_frame Q₀ hQ T₀ Ξ D hT hn hΦ hEf, lintegral_testFnT_eq_gen Q₀ hQ T₀ Ξ D hn hN hΦ] at h1
  have hG : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  have hV := covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ
  rw [hG] at hV
  rw [hI] at h1
  set I := frameσA Q₀ hQ T₀ Ξ D S
  set mK := muFin Q₀ (fun _ => 1) (KSO Q₀)
  set ρ := ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i
  set V := ∑' i, unitVolume Q₀ hQ i
  set Sum := frameOrbitSum Q₀ hQ T₀ Ξ D
  set tH := covolume (GammaSOAdele D.Q'') (SOAdele D.Q'') (muTam D.Q'' D.hQ'' fun _ => 1)
  have h2 : I * (tH * (Sum * V)) = I * (2 * ρ) := by
    calc I * (tH * (Sum * V)) = (tH * (Sum * I)) * V := by ring
      _ = (mK * 1 * ρ * I) * V := by rw [h1]
      _ = I * ((mK * V) * ρ) := by ring
      _ = I * (2 * ρ) := by rw [← hV]
  exact ((ENNReal.mul_right_inj hS0 hSt).mp h2).symm

end QuadFormsKB.Tamagawa.Indefinite
