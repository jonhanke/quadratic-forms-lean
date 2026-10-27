/-
# $\hat L$ and the embeddings of $SO(V)(F)$ (Siegel's formula for indefinite forms)

**Layer:** number fields; the library's adelic groups.

**Proves** (unconditional, standard axioms only)
* `latHat_stable`: $SO(\hat L)$ = `KSO Q₀` preserves $\hat L = \prod_v\mathfrak o_v^n$ (both ways);
* `GammaSOAdele_injA`: an element of $SO(V)(F)$ whose image in $G_\infty$ is $1$ is $1$;
* `ratA_injective`: the archimedean embedding of the rational sphere $T(m)(F)\to V_\infty$ is injective.
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalSetup

open MeasureTheory MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchSOMeasure NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- Elements of $SO(\hat L)$ have integral local matrices. -/
theorem matV_integral_of_KSO (k : SOAf Q₀) (hk : k ∈ KSO Q₀) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin n) :
    matV Q₀ ((1 : GInfSO Q₀), k) v i j ∈ v.adicCompletionIntegers F := by
  have h' : (k : OAf QF) ∈ (locStab QF (stdLat F n) : Set (OAf QF)) := hk
  rw [coe_locStab_std] at h'
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (entries_le_one_of_locAct v (h' v) i j)

theorem latHat_smul_mem (k : SOAf Q₀) (hk : k ∈ KSO Q₀) (z : Fin n → FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ latHat F n) : k • z ∈ latHat F n := by
  intro i v
  show (finSMul Q₀ ((1 : GInfSO Q₀), k) z i) v ∈ _
  rw [finSMul_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (matV_integral_of_KSO Q₀ k hk v i j) (hz j v)

/-- **$SO(\hat L)$ preserves $\hat L$.** -/
theorem latHat_stable (k : SOAf Q₀) (hk : k ∈ KSO Q₀) (z : Fin n → FiniteAdeleRing (𝓞 F) F) :
    k • z ∈ latHat F n ↔ z ∈ latHat F n := by
  refine ⟨fun h => ?_, latHat_smul_mem Q₀ k hk z⟩
  have := latHat_smul_mem Q₀ k⁻¹ ((KSO Q₀).inv_mem hk) _ h
  rwa [inv_smul_smul] at this

/-- **$SO(V)(F)\to G_\infty$ is injective.** -/
theorem GammaSOAdele_injA (γ : SOAdele Q₀) (hγ : γ ∈ GammaSOAdele Q₀) (h1 : γ.1 = 1) : γ = 1 := by
  obtain ⟨g, rfl⟩ := hγ
  have hM : ((g : orthGroup QF F) : GL (Fin n) F).val = 1 := by
    ext i j
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rcases w.isReal_or_isComplex with hw | hw
    · have := congrArg (fun x : GInfSO Q₀ => (ArchSO.incl _ (x.1 ⟨w, hw⟩) : GL (Fin n) ℝ).val i j) h1
      have h2 : (embedding_of_isReal hw) (((g : orthGroup QF F) : GL (Fin n) F).val i j) =
          (embedding_of_isReal hw) ((1 : Matrix (Fin n) (Fin n) F) i j) := by
        have h3 : (embedding_of_isReal hw) (((g : orthGroup QF F) : GL (Fin n) F).val i j) =
            (1 : Matrix (Fin n) (Fin n) ℝ) i j := this.trans (by simp)
        rw [h3, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      exact (embedding_of_isReal hw).injective h2
    · have := congrArg (fun x : GInfSO Q₀ => (ArchSOC.incl _ (x.2 ⟨w, hw⟩) : GL (Fin n) ℂ).val i j) h1
      have h2 : w.embedding (((g : orthGroup QF F) : GL (Fin n) F).val i j) =
          w.embedding ((1 : Matrix (Fin n) (Fin n) F) i j) := by
        have h3 : w.embedding (((g : orthGroup QF F) : GL (Fin n) F).val i j) =
            (1 : Matrix (Fin n) (Fin n) ℂ) i j := this.trans (by simp)
        rw [h3, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      exact w.embedding.injective h2
  have : g = 1 := Subtype.ext (Subtype.ext (Units.ext hM))
  rw [this, map_one]

/-- **The archimedean embedding of the rational sphere is injective.** -/
theorem ratA_injective (m : F) : Function.Injective (ratA Q₀ m) := by
  intro η η' h
  refine Subtype.ext (funext fun j => ?_)
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases w.isReal_or_isComplex with hw | hw
  · have := congrArg (fun x : VInf F n => x.1 ⟨w, hw⟩ j) h
    simp only [ratA, archVec, diagVec_apply, diag_fst, mixedEmbedding_apply_isReal] at this
    exact (embedding_of_isReal hw).injective this
  · have := congrArg (fun x : VInf F n => x.2 ⟨w, hw⟩ j) h
    simp only [ratA, archVec, diagVec_apply, diag_fst, mixedEmbedding_apply_isComplex] at this
    exact w.embedding.injective this

end QuadFormsKB.Tamagawa.Indefinite
