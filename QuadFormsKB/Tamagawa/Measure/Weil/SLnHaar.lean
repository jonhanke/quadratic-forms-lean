import QuadFormsKB.Tamagawa.Measure.Weil.SLnTamagawa

/-!
# `muSL` is a Haar measure; comparison with the measure $\mu_T$ on $\mathrm{SL}_2$

$F$ a number field.

* **`isHaarMeasure_muSL`**: the Tamagawa measure `muSL F k` of $\mathrm{SL}_{k+1}(\mathbb A_F)$ is a Haar measure.
  *Proof:* it is left invariant and σ-finite, so it is $c\cdot\mu_{\mathrm{Haar}}$ with $c\in[0,\infty]$; $c\ne0$ since
  `muSL` is nonzero, and $c\ne\infty$ because a fundamental domain $D$ has $\mu(D) = \tau = 1$ (`tamagawa_SLn`), while
  $\infty\cdot\mu_{\mathrm{Haar}}(D)\in\{0,\infty\}$.
* **`muSL_one_eq_muT`**: for $n = 2$, `muSL F 1` is the measure $\mu_T$ of `SL2Measure.lean`: both are left-invariant
  σ-finite measures, hence proportional, and both give covolume $1$ (`tamagawa_SL2`, `tamagawa_SLn`). So the local
  description of $\mu_T$ as Weil's product of local gauge-form measures (`muT_box`, `SL2Box.lean`) applies to `muSL F 1`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- **The Tamagawa measure `muSL F k` is a Haar measure on $\mathrm{SL}_{k+1}(\mathbb A_F)$.** -/
@[kb "weil1982" "§2.4, Thm 2.4.3 [unverified page]"]
theorem isHaarMeasure_muSL (k : ℕ) : (muSL F k).IsHaarMeasure := by
  set μH : Measure (SLnA F (Fin (k + 1))) := Measure.haar
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : SLnA F (Fin (k + 1)))
  have hU0 : μH (interior K) ≠ 0 :=
    (isOpen_interior.measure_pos μH ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩).ne'
  have hUt : μH (interior K) ≠ ∞ := (lt_of_le_of_lt (measure_mono interior_subset) hK.measure_lt_top).ne
  have heq := measure_eq_div_smul (muSL F k) μH hU0 hUt
  set c := muSL F k (interior K) / μH (interior K)
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin (k + 1))
  have hFD : IsFundamentalDomain (SpecialLinearGroup (Fin (k + 1)) F) D (muSL F k) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hD1 : muSL F k D = 1 := by rw [← tauSL_eq hFD]; exact tamagawa_SLn k
  have hc0 : c ≠ 0 := by
    intro h
    apply (good_muSL (F := F) k).ne_zero
    rw [heq, h, zero_smul]
  have hct : c ≠ ∞ := by
    intro h
    have := hD1
    rw [heq, h, Measure.smul_apply, smul_eq_mul] at this
    rcases eq_or_ne (μH D) 0 with h0 | h0
    · rw [h0, mul_zero] at this; exact zero_ne_one this
    · rw [ENNReal.top_mul h0] at this; exact ENNReal.top_ne_one this
  rw [heq]
  exact Measure.IsHaarMeasure.smul _ hc0 hct

/-- **For $n = 2$ the Tamagawa measure `muSL F 1` is the measure $\mu_T$.** -/
@[kb "weil1982" "§2.4, Thm 2.4.3 [unverified page] (uniqueness of the Tamagawa measure)"]
theorem muSL_one_eq_muT (A : Set (SLnA F (Fin 2))) : muSL F 1 A = muT F A := by
  let ν : @Measure (SLnA F (Fin 2)) measurableSpace_SLnA := muT F
  have : SigmaFinite ν := by exact (inferInstance : SigmaFinite (muT F))
  have : ν.IsMulLeftInvariant := by exact (inferInstance : (muT F).IsMulLeftInvariant)
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin 2)
  have hFD : IsFundamentalDomain (SpecialLinearGroup (Fin 2) F) D (muSL F 1) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hFDT : IsFundamentalDomain (SL(2, F)) D (muT F) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have h1 : muSL F 1 D = 1 := by rw [← tauSL_eq hFD]; exact tamagawa_SLn 1
  have h2 : ν D = 1 := by
    have : muT F D = 1 := by rw [← hFDT.covolume_eq_volume]; exact tamagawa_SL2
    exact this
  have heq := measure_eq_div_smul (muSL F 1) ν (s := D) (by rw [h2]; exact one_ne_zero)
    (by rw [h2]; exact ENNReal.one_ne_top)
  rw [h1, h2, ENNReal.div_self one_ne_zero ENNReal.one_ne_top, one_smul] at heq
  rw [heq]
  rfl

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
