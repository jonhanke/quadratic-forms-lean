import QuadFormsKB.Tamagawa.Measure.Weil.SL2Measure
import QuadFormsKB.Tamagawa.Measure.Weil.OrbitFibration

/-!
# the $\mu_T$ as an instance of the generic orbit fibration

$F$ any number field. $\mathrm{SL}_2(\mathbb A_F)$ acts on the primitive vectors $P\subseteq\mathbb A_F^2$
(`primSet`) by $g\cdot y = gy$, transitively, with base point $e_1$ and the measurable section $s$
(`SL2Section.lean`). This is an `OrbitSection` (`slOrbitSection`) whose stabilizer is $N(\mathbb A_F)$
(`mem_slStab_iff`). With $\mu_N$ = the image of the self-dual measure $dx$ under $x\mapsto n(x)$ (`muN`):

* **`muT_eq_fibMeasure`**: the Tamagawa measure is the generic fibration measure,
  $\mu_T = \Psi_*(dy|_P\otimes\mu_N)$, so all of `OrbitFibration.lean` applies to it;
* **`dyP_unique`**: $dy|_P$ is the unique $\mathrm{SL}_2(\mathbb A_F)$-invariant σ-finite measure $\nu$ on $P$ with
  $\Psi_*(\nu\otimes\mu_N) = \mu_T$ (Weil's uniqueness of the quotient measure on $G/H$).
-/

open IsDedekindDomain NumberField MeasureTheory Measure
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- $\mathrm{SL}_2(\mathbb A_F)$ acting on the primitive vectors by $g\cdot y = gy$. -/
instance slPrimAction : MulAction (SL2A F) (primSet F) where
  smul g y := ⟨Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (y : AdeleSpace F (Fin 2)),
    mulVec_mem_primSet g y.2⟩
  one_smul y := Subtype.ext (by
    show Matrix.mulVec ((1 : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) (y : AdeleSpace F (Fin 2)) = y
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])
  mul_smul g h y := Subtype.ext (by
    show Matrix.mulVec ((g * h : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) y =
      Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F))
        (Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (Adeles F)) (y : AdeleSpace F (Fin 2)))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec])

theorem slPrim_smul_val (g : SL2A F) (y : primSet F) :
    ((g • y : primSet F) : AdeleSpace F (Fin 2)) =
      Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (y : AdeleSpace F (Fin 2)) := rfl

variable (F) in
/-- The base point $e_1\in P$. -/
def eOne : primSet F := ⟨col 1, col_mem_primSet 1⟩

theorem smul_eOne (g : SL2A F) : ((g • eOne F : primSet F) : AdeleSpace F (Fin 2)) = col g := by
  rw [slPrim_smul_val, eOne, ← col_mul, mul_one]

variable (F) in
/-- **The orbit section of $g\mapsto g e_1$** on $\mathrm{SL}_2(\mathbb A_F)$ (the explicit section). -/
def slOrbitSection : OrbitSection (SL2A F) (primSet F) where
  base := eOne F
  sec y := sec (y : AdeleSpace F (Fin 2))
  sec_smul y := Subtype.ext (by rw [smul_eOne, col_sec y.2])
  measurable_sec := measurable_sec.comp measurable_subtype_coe
  measurable_orbit := by
    have : (fun g : SL2A F => g • eOne F) = fun g => ⟨col g, col_mem_primSet g⟩ :=
      funext fun g => Subtype.ext (smul_eOne g)
    rw [this]
    exact measurable_col.subtype_mk

theorem mem_slStab_iff (g : SL2A F) : g ∈ (slOrbitSection F).stab ↔ col g = col 1 := by
  rw [OrbitSection.mem_stab_iff]
  show g • eOne F = eOne F ↔ _
  rw [Subtype.ext_iff, smul_eOne]
  rfl

/-- $x\mapsto n(x)$ into the stabilizer. -/
def nStab (x : Adeles F) : (slOrbitSection F).stab := ⟨nA x, (mem_slStab_iff _).2 (col_nA x)⟩

theorem measurable_nStab : Measurable (nStab (F := F)) := measurable_nA.subtype_mk

theorem nStab_surjective (h : (slOrbitSection F).stab) :
    h = nStab ((h : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1) :=
  Subtype.ext (eq_nA_of_col_eq ((mem_slStab_iff _).1 h.2))

variable (F) in
/-- The measure $\mu_N$ on $N(\mathbb A_F)$: the self-dual measure $dx$ transported by $x\mapsto n(x)$. -/
def muN : Measure (slOrbitSection F).stab := (muAdd F).map nStab

/-- $x\mapsto n(x)$ as a measurable equivalence $\mathbb A_F\simeq N(\mathbb A_F)$. -/
def nStabEquiv : Adeles F ≃ᵐ (slOrbitSection F).stab where
  toFun := nStab
  invFun h := (h : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1
  left_inv _ := rfl
  right_inv h := (nStab_surjective h).symm
  measurable_toFun := measurable_nStab
  measurable_invFun := (measurable_SL2A_entry 0 1).comp measurable_subtype_coe

instance : SigmaFinite (muN F) := by
  have : muN F = (muAdd F).map (nStabEquiv (F := F)) := rfl
  rw [this]; exact nStabEquiv.sigmaFinite_map

instance : (muN F).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  rw [nStab_surjective h]
  set x₀ := ((h : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1)
  have hc : (fun k => nStab x₀ * k) ∘ nStab = nStab ∘ (fun x => x₀ + x) :=
    funext fun x => Subtype.ext (nA_add x₀ x)
  rw [muN, Measure.map_map (measurable_const_mul _) measurable_nStab, hc,
    ← Measure.map_map measurable_nStab (measurable_const_add x₀), map_add_left_eq_self]

/-- $\mathrm{SL}_2(\mathbb A_F)$ preserves $dy|_P$ (`measurePreserving_baseMap`). -/
instance : SMulInvariantMeasure (SL2A F) (primSet F) (dyP F) := by
  refine ⟨fun g t ht => ?_⟩
  have hb : (fun y : primSet F => g • y) = baseMap g := funext fun y => Subtype.ext (baseMap_val g y).symm
  rw [hb, ← Measure.map_apply (measurePreserving_baseMap g).measurable ht, (measurePreserving_baseMap g).map_eq]

/-- **The Tamagawa measure is the generic fibration measure:** $\mu_T = \Psi_*(dy|_P\otimes\mu_N)$ for the orbit
section of $g\mapsto g e_1$. -/
@[kb "weil1982" "§2.4, Thm 2.4.3 [unverified page]"]
theorem muT_eq_fibMeasure : muT F = (slOrbitSection F).fibMeasure (dyP F) (muN F) := by
  ext A hA
  have hi : Measurable (A.indicator (1 : SL2A F → ℝ≥0∞)) := measurable_one.indicator hA
  have e1 : muT F A = ∫⁻ g, A.indicator 1 g ∂muT F := (lintegral_indicator_one hA).symm
  have e2 : (slOrbitSection F).fibMeasure (dyP F) (muN F) A =
      ∫⁻ g, A.indicator 1 g ∂(slOrbitSection F).fibMeasure (dyP F) (muN F) := (lintegral_indicator_one hA).symm
  rw [e1, e2, (slOrbitSection F).lintegral_fibMeasure _ _ hi, muT, lintegral_map hi measurable_ofCoord,
    lintegral_prod (fun p => A.indicator 1 (ofCoord F p)) (hi.comp measurable_ofCoord).aemeasurable]
  refine lintegral_congr fun y => ?_
  have hf : Measurable fun h : (slOrbitSection F).stab => A.indicator 1 ((slOrbitSection F).sec y * ↑h) :=
    hi.comp (measurable_subtype_coe.const_mul _)
  have e3 := lintegral_map (μ := muAdd F) hf measurable_nStab
  rw [muN, e3]
  rfl

theorem muN_ne_zero : muN F ≠ 0 := by
  intro h
  have : muN F Set.univ = 0 := by rw [h]; rfl
  rw [muN, Measure.map_apply measurable_nStab MeasurableSet.univ, Set.preimage_univ] at this
  exact (NeZero.ne (muAdd F Set.univ)) this

/-- **Uniqueness of the quotient measure on $P = \mathrm{SL}_2(\mathbb A_F)/N(\mathbb A_F)$:** $dy|_P$ is the only
s-finite measure $\nu$ on $P$ with $\Psi_*(\nu\otimes\mu_N) = \mu_T$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 (uniqueness of the quotient measure) [unverified page]"]
theorem dyP_unique (ν : Measure (primSet F)) [SFinite ν]
    (h : (slOrbitSection F).fibMeasure ν (muN F) = muT F) : ν = dyP F :=
  (slOrbitSection F).fibMeasure_injective (muN F) muN_ne_zero (h.trans muT_eq_fibMeasure)

end

end QuadFormsKB.Tamagawa.Measure.Weil
