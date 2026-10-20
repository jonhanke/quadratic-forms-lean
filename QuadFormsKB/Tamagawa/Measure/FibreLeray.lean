import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayOrbital
import QuadFormsKB.Tamagawa.Measure.FibreO
import QuadFormsKB.Tamagawa.Measure.Weil.OrbitFibration

/-!
# The Leray measure on the sphere `{Q = m}` as an `O(V)(F_v)`-invariant measure
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.FibreLeray

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- Shells are a neighbourhood basis: a closed set missing `rho` misses all deep shells. -/
theorem exists_shell_disjoint {C : Set Fv} (hC : IsClosed C) {rho : Fv} (hrho : rho ∉ C) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ y ∈ C, y ∉ shell v rho k := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl rho hrho
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  refine ⟨K, fun k hk y hyC hys => ?_⟩
  have h1 : ‖y - rho‖ ≤ ‖HN.ϖ v‖ ^ k := (norm_le_iff_v v).2 hys
  have h2 : ‖HN.ϖ v‖ ^ k ≤ ‖HN.ϖ v‖ ^ K := pow_le_pow_of_le_one (norm_ϖ_pos v).le (norm_ϖ_lt_one v).le hk
  exact hball (Metric.mem_ball.2 (by rw [dist_eq_norm]; exact lt_of_le_of_lt (h1.trans h2) hK)) hyC

section Sig

/-- The Leray measure `σ_rho` of `Q₀` at `rho` (standard Haar measure on `F_v`). -/
abbrev sig (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (rho : Fv) : Measure (Fin n → Fv) :=
  lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) rho

/-- The sphere `{Q₀ = rho}` in `F_v^n`. -/
def sphereV (Q₀ : QuadForm (𝓞 F) n) (rho : Fv) : Set (Fin n → Fv) := {x | Q₀.evalIn Fv x = rho}

theorem isClosed_sphereV (Q₀ : QuadForm (𝓞 F) n) (rho : Fv) : IsClosed (sphereV v Q₀ rho) := by
  have : sphereV v Q₀ rho = Qv v (NF.Qp v Q₀) ⁻¹' {rho} := by
    ext x; simp [sphereV, Qv, NF.evalIn_Qp]
  rw [this]
  exact (isClosed_singleton).preimage (continuous_qv v _)

theorem sig_sph_compl (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (rho : Fv) : sig v Q₀ hQ rho (sphereV v Q₀ rho)ᶜ = 0 := by
  have hO : IsOpen ((sphereV v Q₀ rho)ᶜ \ {0}) :=
    (isClosed_sphereV v Q₀ rho).isOpen_compl.sdiff isClosed_singleton
  obtain ⟨T, s, hTc, hTO, hmem, hUeq⟩ := exists_countable_union_Cz v hO (by simp)
  have hU0 : ∀ x ∈ T, sig v Q₀ hQ rho (cosetP v x (s x)) = 0 := by
    intro x hx
    have hUC := hmem x hx
    have hsub : cosetP v x (s x) ⊆ (sphereV v Q₀ rho)ᶜ := fun y hy => (hTO hx |>.1) |> fun _ =>
      by
        have : cosetP v x (s x) ⊆ (sphereV v Q₀ rho)ᶜ \ {0} := by
          rw [hUeq]; exact Set.subset_iUnion₂ (s := fun x _ => cosetP v x (s x)) x hx
        exact (this hy).1
    have hcomp : IsCompact (Qv v (NF.Qp v Q₀) '' cosetP v x (s x)) := hUC.1.image (continuous_qv v _)
    have hrho : rho ∉ Qv v (NF.Qp v Q₀) '' cosetP v x (s x) := by
      rintro ⟨y, hy, hyrho⟩
      exact (hsub hy) (by simpa [sphereV, Qv, NF.evalIn_Qp] using hyrho)
    obtain ⟨K, hK⟩ := exists_shell_disjoint v hcomp.isClosed hrho
    obtain ⟨k, hk1, hk2⟩ := ((lerayMeasure_eventually v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) rho hUC).and
      (Filter.eventually_ge_atTop K)).exists
    rw [← hk1, LerayThick.lerayThick_apply _ _ _ hUC.2.1.measurableSet]
    have : cosetP v x (s x) ∩ Qv v (NF.Qp v Q₀) ⁻¹' shell v rho k = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hys
      exact hK k hk2 _ ⟨y, hy, rfl⟩ hys
    rw [this]; simp
  have hcover : (sphereV v Q₀ rho)ᶜ ⊆ {0} ∪ ⋃ x ∈ T, cosetP v x (s x) := by
    intro y hy
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · right
      have : y ∈ (sphereV v Q₀ rho)ᶜ \ {0} := ⟨hy, hy0⟩
      rw [hUeq] at this
      exact this
  refine measure_mono_null hcover ?_
  refine (measure_union_null (lerayMeasure_singleton_zero v _ _ _ rho) ?_)
  exact (measure_biUnion_null_iff hTc).2 hU0

theorem distribHaarChar_neg_one : distribHaarChar Fv (-1 : Fvˣ) = 1 := by
  have h : distribHaarChar Fv (-1 : Fvˣ) * distribHaarChar Fv (-1 : Fvˣ) = 1 := by
    rw [← map_mul]; simp
  set x := distribHaarChar Fv (-1 : Fvˣ)
  have h2 : x ^ 2 = 1 := by rw [sq]; exact h
  rcases (pow_eq_one_iff).1 h2 with h | h
  · exact h
  · omega

/-- **`O(V)(F_v)`-invariance of the Leray measure.** -/
theorem sig_map_orth (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (rho : Fv)
    (g : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) :
    Measure.map (fun x : Fin n → Fv => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x) (sig v Q₀ hQ rho) =
      sig v Q₀ hQ rho := by
  refine lerayMeasure_map_mulVec v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) rho (g : GL (Fin n) Fv) ?_ ?_
  · intro x
    simp only [Qv, NF.evalIn_Qp]
    exact evalIn_orthGroup v Q₀ g x
  · rcases det_eq_one_or_neg_one _ (nondegenerate_QF Q₀ hQ) g with h | h
    · have : GeneralLinearGroup.det (g : GL (Fin n) Fv) = 1 := Units.ext h
      rw [this, map_one]
    · have : GeneralLinearGroup.det (g : GL (Fin n) Fv) = -1 := Units.ext h
      rw [this]; exact distribHaarChar_neg_one v

instance sig_sigmaFinite (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (rho : Fv) :
    SigmaFinite (sig v Q₀ hQ rho) := by
  obtain ⟨T, s, hTc, hTO, hmem, hUeq⟩ := exists_countable_union_Cz v
    (isClosed_singleton (x := (0 : Fin n → Fv))).isOpen_compl (by simp)
  refine Measure.sigmaFinite_of_countable (S := insert {0} ((fun x => cosetP v x (s x)) '' T)) ((hTc.image _).insert _) ?_ ?_
  · intro t ht
    rcases ht with rfl | ⟨x, hx, rfl⟩
    · rw [lerayMeasure_singleton_zero]; exact ENNReal.zero_lt_top
    · exact lerayMeasure_lt_top v _ _ _ rho (hmem x hx)
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · exact Set.mem_sUnion.2 ⟨{0}, Set.mem_insert _ _, by simp [hx]⟩
    · have : x ∈ ({0}ᶜ : Set (Fin n → Fv)) := hx
      rw [hUeq] at this
      simp only [Set.mem_iUnion] at this
      obtain ⟨y, hy, hxy⟩ := this
      exact Set.mem_sUnion.2 ⟨_, Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩, hxy⟩

/-- The sphere of the form `Q₀.map alg` at `alg m` is the sphere of `Q₀` at `alg m` (up to the algebra maps). -/
theorem sphereSet_eq (Q₀ : QuadForm (𝓞 F) (n + 1)) (mF : F) :
    FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF = sphereV v Q₀ (algebraMap F Fv mF) := by
  ext x
  simp only [FibreO.sphereSet, sphereV, Set.mem_ofPred_eq, evalIn_QF]

theorem measurableSet_sphereSet (Q₀ : QuadForm (𝓞 F) (n + 1)) (mF : F) :
    MeasurableSet (FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF) := by
  rw [sphereSet_eq]; exact (isClosed_sphereV v Q₀ _).measurableSet

/-- **The Leray measure on the sphere `{Q = m}`**, as a measure on the subtype. -/
def sphereMeasure (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ : Q₀.Nondegenerate) (mF : F) :
    Measure (FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF) :=
  (sig v Q₀ hQ (algebraMap F Fv mF)).comap Subtype.val

instance sphereMeasure_sigmaFinite (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ : Q₀.Nondegenerate) (mF : F) :
    SigmaFinite (sphereMeasure v Q₀ hQ mF) :=
  Weil.sigmaFinite_comap_subtype _ (measurableSet_sphereSet v Q₀ mF)

instance sphereMeasure_smulInvariant (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ : Q₀.Nondegenerate) (mF : F) :
    SMulInvariantMeasure (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)
      (FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF) (sphereMeasure v Q₀ hQ mF) := by
  refine ⟨fun g t ht => ?_⟩
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_sphereSet v Q₀ mF)
  unfold sphereMeasure
  rw [hemb.comap_apply, hemb.comap_apply]
  have hset : Subtype.val '' ((fun x => g • x) ⁻¹' t) =
      (fun x : Fin (n + 1) → Fv => ((g : GL (Fin (n + 1)) Fv) : Matrix (Fin (n + 1)) (Fin (n + 1)) Fv) *ᵥ x) ⁻¹' (Subtype.val '' t) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hx : x ∈ FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF := by
        have h1 := y.2
        have hyx' : (y : Fin (n + 1) → Fv) = ((g : GL (Fin (n + 1)) Fv) : Matrix (Fin (n + 1)) (Fin (n + 1)) Fv) *ᵥ x := hyx
        have : x = ((g⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (y : Fin (n + 1) → Fv) := by
          rw [hyx', mulVec_mulVec]; simp
        rw [this]
        exact (g⁻¹ • y : FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF).2
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show g • (⟨x, hx⟩ : FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF) ∈ t
      have : g • (⟨x, hx⟩ : FibreO.sphereSet v (Q₀.map (algebraMap (𝓞 F) F)) mF) = y := Subtype.ext hyx.symm
      rw [this]; exact hy
  have hmeas : Measurable fun x : Fin (n + 1) → Fv => ((g : GL (Fin (n + 1)) Fv) : Matrix (Fin (n + 1)) (Fin (n + 1)) Fv) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hset, ← Measure.map_apply hmeas (hemb.measurableSet_image.2 ht), sig_map_orth]

end Sig

end QuadFormsKB.Tamagawa.Measure.FibreLeray
