/-
# A uniform $L^1$ bound for $\omega(w)\omega(n(Z))\Phi$ over integral $Z$

**Layer:** local, one finite place $v$ of a number field $F$; harmonic analysis on $V^r = M_{2m\times r}(F_v)$.

**Setting.** $F_v$ is the completion at a finite place, $\psi_v$ the standard character, $\Phi \in \mathcal S(V^r)$ a Schwartz function
(`Sg (localDataV v) m r`, equivalently locally constant with compact support, `mem_Sg_iff`), and $\omega(n(Z))$, $\omega(w)$ the
Schrödinger operators `opNg`, `opWg`.

**Result** (`exists_bound_integral_opWg_opNg`). There is a constant $C$ such that for every $Z \in M_r(F_v)$ with all entries of
norm $\le 1$,
$$\int_{V^r}\big|\,\omega(w)\omega(n(Z))\Phi\,(Y)\big|\,dY \le C.$$
*Proof.* Uniformly in such $Z$: (1) $\omega(n(Z))\Phi$ is supported in the box of $\Phi$ and bounded by $\sup|\Phi|$;
(2) it is invariant under translation by a box of radius $\delta$ independent of $Z$ (the phase
$\psi(\operatorname{tr}(Z\,Q[X]))$ changes by a quantity bounded by $r^2\cdot O(\delta)$ on the support); (3) hence its Fourier transform
vanishes at $Y$ as soon as some entry of $Y$ has norm $> R'$ ($R'$ independent of $Z$), by translating $X$ in one coordinate
where $\psi(2a_iH_{ij}Y_{ij}) \ne 1$; (4) $|\omega(w)\varphi(Y)| \le |\gamma_V^rc_B^r|\int|\varphi|$. So the integrand is bounded by a
constant times the indicator of a compact box.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.NonArchSg
import QuadFormsKB.Weil.Genus.WeilRepUncond
import QuadFormsKB.Weil.Genus.HaarGL
import QuadFormsKB.Analysis.WeilIndexNF

open MeasureTheory Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep WeilRep.LocalData WeilRep.Genus

section General

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {m g : ℕ}

/-- A function in `SBG` is continuous (locally constant). -/
lemma continuous_of_mem_SBG {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ SBG K m g) : Continuous Φ := by
  obtain ⟨R, ε, hε, -, hinv⟩ := hΦ
  have hε' : 0 < ε.toNNReal := Real.toNNReal_pos.mpr hε
  refine continuous_iff_continuousAt.mpr fun X => ?_
  have hU : {Y : PtG m g K | Y - X ∈ box (m := m) (g := g) (K := K) ε.toNNReal} ∈ nhds X := by
    refine ((isOpen_box hε').preimage (continuous_sub_right X)).mem_nhds ?_
    show X - X ∈ box (m := m) (g := g) (K := K) ε.toNNReal
    simp
  refine (continuousAt_const (y := Φ X)).congr ?_
  filter_upwards [hU] with Y hY
  have := hinv X (Y - X) fun i j => by
    have h := hY i j
    rwa [Real.coe_toNNReal _ hε.le] at h
  rw [add_sub_cancel] at this
  exact this.symm

/-- A function in `SBG` is bounded. -/
lemma exists_norm_le_of_mem_SBG {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ SBG K m g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ X, ‖Φ X‖ ≤ M := by
  have hc := continuous_of_mem_SBG hΦ
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ
  obtain ⟨M, hM⟩ := (isCompact_box (m := m) (g := g) (K := K) |R|.toNNReal).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun X => ?_⟩
  by_cases h : Φ X = 0
  · simp [h]
  · refine (hM X (SetLike.mem_coe.mpr (mem_box.mpr fun i j => ?_))).trans (le_max_left _ _)
    rw [Real.coe_toNNReal _ (abs_nonneg R)]
    exact (hR X h i j).trans (le_abs_self R)

end General

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}
  (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- **Uniform $L^1$ bound for $\omega(w)\omega(n(Z))\Phi$ over integral $Z$.** For a Schwartz function $\Phi$ of
$V^r = M_{2m\times r}(F_v)$ there is a constant $C$ with
$\int_{V^r}|\omega(w)\omega(n(Z))\Phi(Y)|\,dY \le C$ for every $Z \in M_r(F_v)$ all of whose entries have norm $\le 1$. -/
theorem exists_bound_integral_opWg_opNg {Φ : PtG m r (v.adicCompletion F) → ℂ}
    (hΦ : Φ ∈ Sg (localDataV v) m r) :
    ∃ C : ℝ, ∀ Z : Matrix (Fin r) (Fin r) (v.adicCompletion F), (∀ i j, ‖Z i j‖ ≤ 1) →
      ∫ Y, ‖opWg (localDataV v) a (opNg (localDataV v) a Z Φ) Y‖ ∂muG (localDataV v) m r ≤ C := by
  have hΦ' : Φ ∈ SBG (v.adicCompletion F) m r := (mem_Sg_iff (D := localDataV v) rfl).mp hΦ
  obtain ⟨M0, hM0, hM⟩ := exists_norm_le_of_mem_SBG hΦ'
  obtain ⟨R, ε, hε, hR, hinv⟩ := hΦ'
  obtain ⟨ρ, hρ, hρ1⟩ := (Analysis.isStdChar_psiV v).triv
  obtain ⟨A, hA, hA1⟩ := (Analysis.isStdChar_psiV v).exists_large
  set Na : ℝ := ∑ i, ‖(a i : (v.adicCompletion F))‖ with hNa
  have hNa0 : 0 ≤ Na := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set Nr : ℝ := (r : ℝ) * r with hNr
  have hNr0 : 0 ≤ Nr := by positivity
  set M : ℝ := Nr * Na * (|R| + 1) with hMdef
  have hM0' : 0 ≤ M := by positivity
  set δ : ℝ := min ε (min 1 (ρ / (M + 1))) with hδ
  have hδpos : 0 < δ := lt_min hε (lt_min one_pos (div_pos hρ (by positivity)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδρ : δ ≤ ρ / (M + 1) := (min_le_right _ _).trans (min_le_right _ _)
  -- (1) uniform invariance
  have hinvZ : ∀ Z : Matrix (Fin r) (Fin r) (v.adicCompletion F), (∀ i j, ‖Z i j‖ ≤ 1) → ∀ X H : PtG m r (v.adicCompletion F),
      (∀ i j, ‖H i j‖ ≤ δ) → opNg (localDataV v) a Z Φ (X + H) = opNg (localDataV v) a Z Φ X := by
    intro Z hZ X H hH
    have hΦ' : Φ (X + H) = Φ X := hinv X H fun i j => (hH i j).trans hδε
    by_cases hX0 : Φ X = 0
    · simp [opNg, hΦ', hX0]
    have hXb : ∀ i j, ‖X i j‖ ≤ |R| := fun i j => (hR X hX0 i j).trans (le_abs_self _)
    have hsmall := norm_trace_QX_sub_le (a := a) Z X H (abs_nonneg R) hδpos.le hδ1 hXb hH
    have hS : ∑ j, ∑ k, ‖Z j k‖ ≤ Nr := by
      calc ∑ j, ∑ k, ‖Z j k‖ ≤ ∑ _j : Fin r, ∑ _k : Fin r, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hZ j k
        _ = Nr := by simp [hNr]
    have hle : (∑ j, ∑ k, ‖Z j k‖) * (∑ i, ‖(a i : (v.adicCompletion F))‖) * ((|R| + 1) * δ) ≤ ρ := by
      have h1 : (∑ j, ∑ k, ‖Z j k‖) * (∑ i, ‖(a i : (v.adicCompletion F))‖) * ((|R| + 1) * δ) ≤ M * δ := by
        have : Nr * Na * ((|R| + 1) * δ) = M * δ := by rw [hMdef]; ring
        rw [← this]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hNa0) (by positivity)
      refine h1.trans ?_
      calc M * δ ≤ M * (ρ / (M + 1)) := by gcongr
        _ = ρ * (M / (M + 1)) := by ring
        _ ≤ ρ * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
        _ = ρ := mul_one _
    have hψΔ := hρ1 _ (hsmall.trans hle)
    show ((localDataV v).ψ (trace (Z * QX a (X + H))) : ℂ) * Φ (X + H) =
      ((localDataV v).ψ (trace (Z * QX a X)) : ℂ) * Φ X
    rw [hΦ', show trace (Z * QX a (X + H)) = trace (Z * QX a X) +
      (trace (Z * QX a (X + H)) - trace (Z * QX a X)) by ring]
    have e := AddChar.map_add_eq_mul (localDataV v).ψ (trace (Z * QX a X))
      (trace (Z * QX a (X + H)) - trace (Z * QX a X))
    rw [e, show (localDataV v).ψ (trace (Z * QX a (X + H)) - trace (Z * QX a X)) = 1 from hψΔ,
      mul_one]
  -- (2) pointwise bounds on the integrand
  set Rn : NNReal := |R|.toNNReal with hRn
  have hsupp : ∀ (Z : Matrix (Fin r) (Fin r) (v.adicCompletion F)) X, X ∉ box (m := m) (g := r) (K := (v.adicCompletion F)) Rn →
      opNg (localDataV v) a Z Φ X = 0 := by
    intro Z X hX
    by_contra h
    apply hX
    refine mem_box.mpr fun i j => ?_
    rw [hRn, Real.coe_toNNReal _ (abs_nonneg R)]
    have hΦX : Φ X ≠ 0 := fun h0 => h (by simp [opNg, h0])
    exact (hR X hΦX i j).trans (le_abs_self R)
  have hnorm : ∀ (Z : Matrix (Fin r) (Fin r) (v.adicCompletion F)) X, ‖opNg (localDataV v) a Z Φ X‖ ≤ M0 := by
    intro Z X
    simpa [opNg] using hM X
  have hBorel : MeasurableSet (box (m := m) (g := r) (K := (v.adicCompletion F)) Rn : Set (PtG m r (v.adicCompletion F))) :=
    (isCompact_box Rn).isClosed.measurableSet
  have hD : (localDataV v).μ.IsAddHaarMeasure := inferInstanceAs ((Analysis.selfDualV v).IsAddHaarMeasure)
  have hHaar : (muG (localDataV v) m r).IsAddHaarMeasure := inferInstance
  have : (muG (localDataV v) m r).IsAddRightInvariant := inferInstance
  have : IsFiniteMeasureOnCompacts (muG (localDataV v) m r) := inferInstance
  set μ : Measure (PtG m r (v.adicCompletion F)) := muG (localDataV v) m r with hμ
  have hfin : ∀ R' : NNReal, μ (box (m := m) (g := r) (K := (v.adicCompletion F)) R') < ⊤ := fun R' =>
    (isCompact_box R').measure_lt_top
  -- (3) the integral is bounded
  have hI : ∀ (Z : Matrix (Fin r) (Fin r) (v.adicCompletion F)) (Y : PtG m r (v.adicCompletion F)),
      ‖∫ X, opNg (localDataV v) a Z Φ X * ((localDataV v).ψ (BX a X Y) : ℂ) ∂μ‖ ≤
        μ.real (box (m := m) (g := r) (K := (v.adicCompletion F)) Rn) * M0 := by
    intro Z Y
    have hint : Integrable ((box (m := m) (g := r) (K := (v.adicCompletion F)) Rn : Set (PtG m r (v.adicCompletion F))).indicator
        (fun _ => M0)) μ :=
      (integrableOn_const (hfin Rn).ne).integrable_indicator hBorel
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun X => ?_)).trans ?_
    · by_cases hX : X ∈ box (m := m) (g := r) (K := (v.adicCompletion F)) Rn
      · rw [Set.indicator_of_mem (SetLike.mem_coe.mpr hX), norm_mul]
        simpa using hnorm Z X
      · rw [Set.indicator_of_notMem (fun h => hX (SetLike.mem_coe.mp h)), hsupp Z X hX]
        simp
    · rw [integral_indicator_const _ hBorel, smul_eq_mul]
  -- (4) vanishing for large Y
  obtain ⟨δa, hδa, hδale⟩ := exists_uniform (fun i => ‖(a i : (v.adicCompletion F))‖) fun i =>
    norm_pos_iff.mpr (a i).ne_zero
  have h2 : 0 < ‖(2 : (v.adicCompletion F))‖ := norm_pos_iff.mpr two_ne_zero
  set R'r : ℝ := A / (‖(2 : (v.adicCompletion F))‖ * δa * δ) with hR'r
  set R' : NNReal := R'r.toNNReal with hR'
  have hI0 : ∀ (Z : Matrix (Fin r) (Fin r) (v.adicCompletion F)), (∀ i j, ‖Z i j‖ ≤ 1) → ∀ (Y : PtG m r (v.adicCompletion F)),
      Y ∉ box (m := m) (g := r) (K := (v.adicCompletion F)) R' →
      ∫ X, opNg (localDataV v) a Z Φ X * ((localDataV v).ψ (BX a X Y) : ℂ) ∂μ = 0 := by
    intro Z hZ Y hY
    rw [mem_box] at hY
    push Not at hY
    obtain ⟨i0, j0, hij⟩ := hY
    have hYb : R'r < ‖Y i0 j0‖ := lt_of_le_of_lt (Real.le_coe_toNNReal _) hij
    set c : (v.adicCompletion F) := 2 * (a i0 : (v.adicCompletion F)) * Y i0 j0 with hc
    have hcδ : A ≤ ‖c‖ * δ := by
      have h3 : A < ‖(2 : (v.adicCompletion F))‖ * δa * δ * ‖Y i0 j0‖ := by
        rw [hR'r, div_lt_iff₀ (by positivity)] at hYb
        linarith
      have h4 : ‖(2 : (v.adicCompletion F))‖ * δa * δ * ‖Y i0 j0‖ ≤ ‖c‖ * δ := by
        rw [hc, norm_mul, norm_mul]
        have := hδale i0
        have h5 : ‖(2 : (v.adicCompletion F))‖ * δa ≤ ‖(2 : (v.adicCompletion F))‖ * ‖(a i0 : (v.adicCompletion F))‖ := by gcongr
        calc ‖(2 : (v.adicCompletion F))‖ * δa * δ * ‖Y i0 j0‖ = (‖(2 : (v.adicCompletion F))‖ * δa) * ‖Y i0 j0‖ * δ := by ring
          _ ≤ (‖(2 : (v.adicCompletion F))‖ * ‖(a i0 : (v.adicCompletion F))‖) * ‖Y i0 j0‖ * δ := by gcongr
      linarith
    obtain ⟨h, hh, hψh⟩ := hA1 c δ hcδ
    set H : PtG m r (v.adicCompletion F) := Matrix.of fun i j => if i = i0 ∧ j = j0 then h else 0 with hH
    have hHn : ∀ i j, ‖H i j‖ ≤ δ := by
      intro i j
      simp only [hH, Matrix.of_apply]
      split_ifs
      · exact hh
      · rw [norm_zero]; exact hδpos.le
    have hBX : ∀ X, BX a (X + H) Y = BX a X Y + c * h := by
      intro X
      have hHs : ∑ i, ∑ j, 2 * (a i : (v.adicCompletion F)) * H i j * Y i j = c * h := by
        rw [Finset.sum_eq_single i0]
        · rw [Finset.sum_eq_single j0]
          · simp [hH, hc]; ring
          · intro j _ hj
            simp [hH, hj]
          · simp
        · intro i _ hi
          simp [hH, hi]
        · simp
      unfold BX
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      rw [hHs]
    set Iint : ℂ := ∫ X, opNg (localDataV v) a Z Φ X * ((localDataV v).ψ (BX a X Y) : ℂ) ∂μ with hIint
    have key : Iint = (((localDataV v).ψ (c * h) : Circle) : ℂ) * Iint := by
      conv_lhs => rw [hIint, ← integral_add_right_eq_self _ H]
      rw [hIint, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only
      rw [hinvZ Z hZ X H hHn, hBX, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hne : (((localDataV v).ψ (c * h) : Circle) : ℂ) ≠ 1 := fun h1 => hψh (Subtype.ext h1)
    have : (1 - (((localDataV v).ψ (c * h) : Circle) : ℂ)) * Iint = 0 := by linear_combination key
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by linear_combination -h0) hne
    · exact h0
  -- (5) assemble
  set B0 : ℝ := ‖(localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r‖ *
    (μ.real (box (m := m) (g := r) (K := (v.adicCompletion F)) Rn) * M0) with hB0
  have hB0nn : 0 ≤ B0 := by positivity
  have hR'meas : MeasurableSet (box (m := m) (g := r) (K := (v.adicCompletion F)) R' : Set (PtG m r (v.adicCompletion F))) :=
    (isCompact_box R').isClosed.measurableSet
  refine ⟨μ.real (box (m := m) (g := r) (K := (v.adicCompletion F)) R') * B0, fun Z hZ => ?_⟩
  have hint : Integrable ((box (m := m) (g := r) (K := (v.adicCompletion F)) R' : Set (PtG m r (v.adicCompletion F))).indicator
      (fun _ => B0)) μ := (integrableOn_const (hfin R').ne).integrable_indicator hR'meas
  have := integral_mono_of_nonneg (μ := μ)
    (f := fun Y => ‖opWg (localDataV v) a (opNg (localDataV v) a Z Φ) Y‖)
    (Filter.Eventually.of_forall fun Y => norm_nonneg _) hint (Filter.Eventually.of_forall fun Y => ?_)
  · refine this.trans (le_of_eq ?_)
    rw [integral_indicator_const _ hR'meas, smul_eq_mul]
  · by_cases hY : Y ∈ box (m := m) (g := r) (K := (v.adicCompletion F)) R'
    · rw [Set.indicator_of_mem (SetLike.mem_coe.mpr hY)]
      unfold opWg
      show ‖_ * _‖ ≤ B0
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hI Z Y) (norm_nonneg _)
    · rw [Set.indicator_of_notMem (fun h => hY (SetLike.mem_coe.mp h))]
      unfold opWg
      show ‖_ * ∫ X, opNg (localDataV v) a Z Φ X * (((localDataV v).ψ (BX a X Y) : Circle) : ℂ) ∂μ‖ ≤ 0
      rw [hI0 Z hZ Y hY]
      simp

end QuadFormsKB.SiegelWeil.Forms
