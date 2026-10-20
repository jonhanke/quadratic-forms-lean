/-
# Haar reduction for the non-square model

**Layer:** a number field $F$, a quadratic extension $K = F(\delta)$, $\delta^2 = d$ (basis $(1,\delta)$), $\alpha = a$, $\beta = b$
in $\mathcal O_K$, $G^\natural = \{g\in(D'\otimes\mathbb A_K)^\times : \operatorname{nrd}g\in\mathbb A_F^\times\}$ (`gnatBCO`), $P = G^\natural/\mathbb A_F^\times$,
$\Phi$ = `nsPEquiv` : $P\cong SO(\langle1,-ad,-bd,abd\rangle)(\mathbb A_F)$.

* **`eq_of_eq_on_open`** (generic): a Haar measure and a left invariant measure finite on compacts that agree on one nonempty
  open set of finite measure are equal (no compactness of the test set is needed).
* **`nsS0 H`**: for a subgroup $H\le(D'\otimes\mathbb A_K)^\times$, the subgroup $\{g\in G^\natural : g_1\in H\}$.
* **`map_muP_ns_eq_of_open`**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ as soon as $\mu_P(\pi(S_0)) = \mu_{\mathrm{Tam}}(\Phi(\pi(S_0)))<\infty$ for one
  open subgroup $S_0$.

Source: Weil 1982, §2.1 (uniqueness of Haar measure), Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatMeasureFinal

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

noncomputable section

section Generic

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Haar uniqueness on one open set of finite measure.** -/
@[kb "weil1982" "§2.1 (uniqueness of Haar measure) [unverified]"]
theorem eq_of_eq_on_open (μ μ' : Measure B) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ']
    [μ'.IsMulLeftInvariant] {U : Set B} (hUo : IsOpen U) (hUne : U.Nonempty) (hUt : μ U ≠ ∞)
    (h : μ U = μ' U) : μ = μ' := by
  have hc := isMulLeftInvariant_eq_smul μ' μ
  have h0 : μ U ≠ 0 := (hUo.measure_pos μ hUne).ne'
  have h1 : (haarScalarFactor μ' μ : ℝ≥0∞) = 1 := by
    have := congrArg (fun ν : Measure B => ν U) hc
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at this
    rw [← h] at this
    have h2 : (haarScalarFactor μ' μ : ℝ≥0∞) * μ U = 1 * μ U := by rw [one_mul]; exact this.symm
    exact (ENNReal.mul_left_inj h0 hUt).1 h2
  rw [hc]
  have : haarScalarFactor μ' μ = 1 := by exact_mod_cast h1
  rw [this, one_smul]

end Generic

section NS

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ

/-- $g\mapsto g_1$, $G^\natural\to(D'\otimes\mathbb A_K)^\times$. -/
abbrev nsFst : (dN).G →* MK := (MonoidHom.fst _ _).comp (dN).gnat.subtype

theorem continuous_nsFst : Continuous (nsFst hb₀ hα0 hβ0) := continuous_fst.comp continuous_subtype_val

/-- **The open subgroup $S_0 = \{g\in G^\natural : g_1\in H\}$.** -/
def nsS0 (H : Subgroup MK) : Subgroup (dN).G := H.comap (nsFst hb₀ hα0 hβ0)

theorem mem_nsS0 {H : Subgroup MK} {g : (dN).G} : g ∈ nsS0 hb₀ hα0 hβ0 H ↔ (g : MK × (Adeles F)ˣ).1 ∈ H := Iff.rfl

theorem isOpen_nsS0 {H : Subgroup MK} (hH : IsOpen (H : Set MK)) : IsOpen (nsS0 hb₀ hα0 hβ0 H : Set (dN).G) :=
  hH.preimage (continuous_nsFst hb₀ hα0 hβ0)

local notation "Φ" => nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
  (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)

/-- **Step 1 for the non-square model**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ if both measures agree, with a finite value, on
$\Phi(\pi(S_0))$ for one open subgroup $S_0\le G^\natural$. -/
@[kb "weil1982" "§2.3 (Haar uniqueness) [unverified]"]
theorem map_muP_ns_eq_of_open (hQ : (qNS a b d).Nondegenerate) (S₀ : Subgroup (dN).G)
    (hS₀ : IsOpen (S₀ : Set (dN).G)) (hfin : (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' S₀) ≠ ∞)
    (h : (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' S₀) = muTam (qNS a b d) hQ (fun _ => 1) (Φ '' ((dN).π '' S₀))) :
    ((dN).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ = muTam (qNS a b d) hQ (fun _ => 1) := by
  have := (dN).isHaarMeasure_muP (muBC bK 0 hb₀ hα0 hβ0)
  have : (((dN).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ).IsHaarMeasure := (Φ).isHaarMeasure_map _
  have hopen : IsOpen ((dN).π '' (S₀ : Set (dN).G)) := QuotientGroup.isOpenMap_coe _ hS₀
  have hopen' : IsOpen (Φ '' ((dN).π '' (S₀ : Set (dN).G))) := (Φ).isOpenMap _ hopen
  have hpre : Φ ⁻¹' (Φ '' ((dN).π '' (S₀ : Set (dN).G))) = (dN).π '' S₀ :=
    (Φ).toEquiv.injective.preimage_image _
  have hmap : ((dN).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ (Φ '' ((dN).π '' (S₀ : Set (dN).G))) =
      (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' S₀) := by
    exact (Measure.map_apply (Φ).continuous.measurable hopen'.measurableSet).trans (congrArg _ hpre)
  refine eq_of_eq_on_open _ _ hopen' ⟨_, ⟨_, ⟨1, S₀.one_mem, rfl⟩, rfl⟩⟩ (by rw [hmap]; exact hfin) ?_
  rw [hmap, h]

end NS

end

end QuadFormsKB.Tamagawa.Measure.Weil
