import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume

/-!
# Shells in a fundamental domain of $F^\times$ in $\mathbb A_F^\times$

**Layer:** $F$ any number field, the Tamagawa measure `tamIdeles` on $\mathbb A_F^\times$ and the quotient measure
`muIdeleClass` on $F^\times\backslash\mathbb A_F^1$ (total mass $\rho_F$).

* **`tamIdeles_exactFD_logShell`**: for every exact fundamental domain $D$ of $F^\times$ in $\mathbb A_F^\times$ and every interval
  $[\alpha,\beta)$,
  $$\mu\big(D\cap\{x : \log\|x\|_{\mathbb A}\in[\alpha,\beta)\}\big) = \operatorname{vol}(F^\times\backslash\mathbb A_F^1)\cdot(\beta-\alpha).$$
  *Proof.* Through the splitting $\mathbb A^\times\cong\mathbb A^1\times\mathbb R_{>0}$ (`ideleSplit`, $\mu\mapsto\mu^1\times dt/t$), every slice
  $\{y : y\,s(t)\in D\}$ is an exact fundamental domain of $F^\times$ in $\mathbb A^1$, of $\mu^1$-measure
  $\operatorname{vol}(F^\times\backslash\mathbb A^1)$; integrate over $t$ (Tonelli).
* `tamIdeles_exactFD_logShell_eq_residue`: the same with $\rho_F$ (`muIdeleClass_univ_eq_residue`).

This is the $\mathbb G_m$-part of Weil 1982, §3.2, proof of Thm 3.2.1, p. 43 ($\int_{k^\times\backslash\mathbb A^\times}f(\|z\|)\,d^\times z
= \rho_k\int_0^\infty f(t)\,dt/t$, here for $f$ the indicator of an interval in $\log t$).
-/

open MeasureTheory Measure Set Function NumberField
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

theorem ideleSplit_symm_apply' (p : ideleOne F × Multiplicative ℝ) :
    (ideleSplit F).symm p = (p.1 : (Adeles F)ˣ) * normSectionHom F p.2 := rfl

theorem log_ideleNorm_ideleSplit_symm (p : ideleOne F × Multiplicative ℝ) :
    Real.log (ideleNorm F ((ideleSplit F).symm p)) = Multiplicative.toAdd p.2 := by
  have h := ideleSplit_apply_snd ((ideleSplit F).symm p)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  rw [h, toAdd_ofAdd]

/-- **Shells in a fundamental domain of $F^\times$ in $\mathbb A_F^\times$**: for an exact fundamental domain $D$ of $F^\times$
(acting by multiplication), $\mu(D\cap\{\log\|x\|\in[\alpha,\beta)\}) = \operatorname{vol}(F^\times\backslash\mathbb A^1)\,(\beta-\alpha)$. -/
@[kb "weil1982" "§3.2, proof of Thm 3.2.1, p. 43; §2.3 [unverified page] (ω = ω^1 × dt/t)"]
theorem tamIdeles_exactFD_logShell {D : Set (Adeles F)ˣ} (hD : IsExactFD (Γ := diagUnitsSub F) D) (α β : ℝ) :
    tamIdeles F (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β) =
      muIdeleClass F univ * ENNReal.ofReal (β - α) := by
  set e := ideleSplit F
  have hlogm : Measurable fun x : (Adeles F)ˣ => Real.log (ideleNorm F x) :=
    Real.measurable_log.comp continuous_ideleNorm.measurable
  have hSm : MeasurableSet (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β) :=
    hD.1.inter (hlogm measurableSet_Ico)
  have he : (e : (Adeles F)ˣ → ideleOne F × Multiplicative ℝ) = e.toHomeomorph.toMeasurableEquiv := rfl
  have hmap : tamIdeles F (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β) =
      ((muIdeleOne F).prod dtt) (e.symm ⁻¹' (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β)) := by
    rw [← map_ideleSplit_tamIdeles, he, MeasurableEquiv.map_apply, ← he, ← preimage_comp]
    congr 1
    ext x
    simp
  have hS' : MeasurableSet (e.symm ⁻¹' (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β)) :=
    e.symm.continuous.measurable hSm
  rw [hmap, Measure.prod_apply_symm hS']
  -- the slices
  have hslice : ∀ t : Multiplicative ℝ, (muIdeleOne F) ((fun y => (y, t)) ⁻¹'
      (e.symm ⁻¹' (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β))) =
      (Multiplicative.toAdd ⁻¹' Ico α β).indicator (fun _ => muIdeleClass F univ) t := by
    intro t
    have hlog : ∀ y : ideleOne F, Real.log (ideleNorm F (e.symm (y, t))) = Multiplicative.toAdd t :=
      fun y => log_ideleNorm_ideleSplit_symm (y, t)
    by_cases ht : Multiplicative.toAdd t ∈ Ico α β
    · rw [indicator_of_mem (show t ∈ Multiplicative.toAdd ⁻¹' Ico α β from ht)]
      have hset : (fun y => (y, t)) ⁻¹' (e.symm ⁻¹' (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β)) =
          {y : ideleOne F | e.symm (y, t) ∈ D} := by
        ext y; simp only [mem_preimage, mem_inter_iff, hlog y, ht, and_true]; rfl
      rw [hset]
      -- the slice is an exact fundamental domain of `F^×` in `𝔸^1`
      have hFD : IsExactFD (Γ := diagUnitsOne F) {y : ideleOne F | e.symm (y, t) ∈ D} := by
        refine ⟨hD.1.preimage (e.symm.continuous.measurable.comp (measurable_id.prodMk measurable_const)),
          fun y => ?_⟩
        have hsm : ∀ f : diagUnitsOne F, e.symm (f • y, t) = ((f : ideleOne F) : (Adeles F)ˣ) • e.symm (y, t) := by
          intro f
          rw [ideleSplit_symm_apply', ideleSplit_symm_apply', Subgroup.smul_def, smul_eq_mul, smul_eq_mul,
            Subgroup.coe_mul, mul_assoc]
        obtain ⟨γ, hγ, huniq⟩ := hD.2 (e.symm (y, t))
        have hγ1 : (γ : (Adeles F)ˣ) ∈ ideleOne F := diagUnitsSub_le_ideleOne γ.2
        refine ⟨⟨⟨γ, hγ1⟩, by
          change (⟨(γ : (Adeles F)ˣ), hγ1⟩ : ideleOne F) ∈ (diagUnitsSub F).subgroupOf (ideleOne F)
          exact Subgroup.mem_subgroupOf.2 γ.2⟩, ?_, fun f hf => ?_⟩
        · change e.symm (_ • y, t) ∈ D
          rw [hsm]; exact hγ
        · change e.symm (f • y, t) ∈ D at hf
          rw [hsm] at hf
          have hfΓ : ((f : ideleOne F) : (Adeles F)ˣ) ∈ diagUnitsSub F := Subgroup.mem_subgroupOf.1 f.2
          have := huniq ⟨_, hfΓ⟩ hf
          have h' : ((f : ideleOne F) : (Adeles F)ˣ) = γ := congrArg Subtype.val this
          exact Subtype.ext (Subtype.ext h')
      rw [muIdeleClass_univ (hFD.isFundamentalDomain _)]
    · rw [indicator_of_notMem (show t ∉ Multiplicative.toAdd ⁻¹' Ico α β from ht)]
      convert measure_empty (μ := muIdeleOne F)
      ext y; simp only [mem_preimage, mem_inter_iff, hlog y, ht, and_false, mem_empty_iff_false]
  simp_rw [hslice]
  have hI : MeasurableSet (Multiplicative.toAdd ⁻¹' Ico α β : Set (Multiplicative ℝ)) :=
    measurableSet_Ico (α := ℝ) (a := α) (b := β)
  rw [lintegral_indicator_const hI, dtt_apply]
  change muIdeleClass F univ * volume (Ico α β) = _
  rw [Real.volume_Ico]

/-- `tamIdeles_exactFD_logShell` with $\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$. -/
theorem tamIdeles_exactFD_logShell_eq_residue {D : Set (Adeles F)ˣ} (hD : IsExactFD (Γ := diagUnitsSub F) D)
    (α β : ℝ) :
    tamIdeles F (D ∩ (fun x => Real.log (ideleNorm F x)) ⁻¹' Ico α β) =
      ENNReal.ofReal (dedekindZeta_residue F) * ENNReal.ofReal (β - α) := by
  rw [tamIdeles_exactFD_logShell hD, muIdeleClass_univ_eq_residue]

end

end QuadFormsKB.Tamagawa.Measure.Weil
