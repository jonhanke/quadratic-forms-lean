import Mathlib
import QuadFormsKB.Citation

/-!
# Splitting a Haar measure along a norm

**Generic, Mathlib-only hypotheses (upstreamable).** Let $G$ be a topological group with a continuous homomorphism
$N : G\to\mathbb R_{>0}$ (written additively-logarithmically as `Multiplicative ℝ`, i.e. $\log N$) and a continuous
homomorphic section $s$ with central image. Then

* **`splitEquiv`**: $g\mapsto(g\,s(N g)^{-1}, N g)$ is an isomorphism of topological groups
  $G\cong\ker N\times\mathbb R_{>0}$ (direct product, since $s$ is central);
* **`map_eq_prod_splitMeasure`**: for $G$ locally compact, second countable, every Haar measure $\mu$ on $G$ and every
  Haar measure $\nu$ on the second factor, $\Phi_*\mu = \mu^1\times\nu$ for the Haar measure
  $\mu^1$ = `splitMeasure Φ μ ν` on the first factor; **`splitMeasure_unique`**: $\mu^1$ is the only measure with this
  property, and **`splitMeasure_apply`**: $\mu^1(E) = \mu(\Phi^{-1}(E\times B))/\nu(B)$ for every $B$ with
  $0 < \nu(B) < \infty$;
* `dtt` = the Haar measure $dt/t$ on $\mathbb R_{>0}$, realized on `Multiplicative ℝ` as the image of Lebesgue measure
  $ds$ under $s\mapsto e^s$ (`dtt_ofAdd_Icc`: $\int_1^e dt/t = 1$).

This is the measure-theoretic part of Weil, *Adeles and algebraic groups* (1982), §2.3 [unverified page]
($A_{\mathbb A}^\times = A_{\mathbb A}^1\times\mathbb R_{>0}$ and the measure $\omega^1$ on $A_{\mathbb A}^1$).
-/

open MeasureTheory Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### `Multiplicative ℝ` as a measure space; $dt/t$ -/

instance instMeasurableSpaceMultiplicative {α : Type*} [m : MeasurableSpace α] : MeasurableSpace (Multiplicative α) :=
  m

instance instBorelSpaceMultiplicative {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [h : BorelSpace α] :
    BorelSpace (Multiplicative α) := h

/-- $s\mapsto e^s$ (formally `Multiplicative.ofAdd`) as a measurable equivalence $\mathbb R\to\mathbb R_{>0}$. -/
def ofAddMeasurableEquiv : ℝ ≃ᵐ Multiplicative ℝ where
  toEquiv := Multiplicative.ofAdd
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id

/-- **The Haar measure $dt/t$ on $\mathbb R_{>0}$**, in the logarithmic coordinate $t = e^s$: Lebesgue measure $ds$
transported to `Multiplicative ℝ`. -/
def dtt : Measure (Multiplicative ℝ) := Measure.map Multiplicative.ofAdd volume

theorem dtt_apply (A : Set (Multiplicative ℝ)) : dtt A = volume (Multiplicative.ofAdd ⁻¹' A) :=
  ofAddMeasurableEquiv.map_apply A

/-- $\int_1^e dt/t = 1$: the interval $[0,1]$ in the logarithmic coordinate. -/
theorem dtt_ofAdd_Icc : dtt (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1) = 1 := by
  rw [dtt_apply]
  change volume (Icc (0 : ℝ) 1) = 1
  simp

instance : dtt.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, dtt_apply, dtt_apply]
  have : Multiplicative.ofAdd ⁻¹' ((fun x => g * x) ⁻¹' A) =
      (fun x : ℝ => Multiplicative.toAdd g + x) ⁻¹' (Multiplicative.ofAdd ⁻¹' A) := rfl
  rw [this, measure_preimage_add]

instance : IsFiniteMeasureOnCompacts dtt := by
  refine ⟨fun K hK => ?_⟩
  rw [dtt_apply]
  exact (show IsCompact (X := ℝ) K from hK).measure_lt_top

instance : dtt.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [dtt_apply]
  exact (show IsOpen (X := ℝ) U from hU).measure_ne_zero volume hne

instance : dtt.IsHaarMeasure := ⟨⟩

instance : SigmaFinite dtt := by
  rw [dtt]; exact ofAddMeasurableEquiv.sigmaFinite_map (μ := volume)

/-! ### The splitting isomorphism $G\cong\ker N\times\mathbb R_{>0}$ -/

section Split

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem mul_s_inv_mem_ker (N : G →* Multiplicative ℝ) (s : Multiplicative ℝ →* G) (K : Subgroup G)
    (hK : ∀ g, g ∈ K ↔ N g = 1) (hNs : ∀ t, N (s t) = t) (g : G) : g * (s (N g))⁻¹ ∈ K := by
  rw [hK, map_mul, map_inv, hNs, mul_inv_cancel]

theorem s_inv_comm (s : Multiplicative ℝ →* G) (hs : ∀ t g, s t * g = g * s t) (t : Multiplicative ℝ) (g : G) :
    (s t)⁻¹ * g = g * (s t)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hs, mul_assoc, mul_inv_cancel, mul_one]

/-- **The splitting** $G\cong K\times\mathbb R_{>0}$ ($K = \ker N$), $g\mapsto(g\,s(Ng)^{-1}, Ng)$, inverse
$(h,t)\mapsto h\,s(t)$, for a continuous homomorphism $N$ with a continuous central homomorphic section $s$. -/
def splitEquiv (N : G →* Multiplicative ℝ) (s : Multiplicative ℝ →* G) (K : Subgroup G)
    (hK : ∀ g, g ∈ K ↔ N g = 1) (hNs : ∀ t, N (s t) = t)
    (hs : ∀ t g, s t * g = g * s t) (hN : Continuous N) (hsc : Continuous s) :
    G ≃ₜ* (K × Multiplicative ℝ) where
  toFun g := (⟨g * (s (N g))⁻¹, mul_s_inv_mem_ker N s K hK hNs g⟩, N g)
  invFun p := (p.1 : G) * s p.2
  left_inv g := by simp
  right_inv p := by
    obtain ⟨⟨h, hh⟩, t⟩ := p
    rw [hK] at hh
    have hN' : N (h * s t) = t := by rw [map_mul, hh, hNs, one_mul]
    ext
    · simp only [hN', mul_inv_cancel_right]
    · exact hN'
  map_mul' g h := by
    ext
    · change g * h * (s (N (g * h)))⁻¹ = g * (s (N g))⁻¹ * (h * (s (N h))⁻¹)
      rw [map_mul, map_mul, mul_inv_rev, mul_assoc, mul_assoc]
      congr 1
      rw [s_inv_comm s hs (N g) (h * (s (N h))⁻¹), mul_assoc]
    · exact map_mul N g h
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hN
    exact continuous_id.mul ((hsc.comp hN).inv)
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hsc.comp continuous_snd)

variable (N : G →* Multiplicative ℝ) (s : Multiplicative ℝ →* G) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ N g = 1) (hNs : ∀ t, N (s t) = t)
  (hs : ∀ t g, s t * g = g * s t) (hN : Continuous N) (hsc : Continuous s)

@[simp] theorem splitEquiv_apply_fst (g : G) :
    ((splitEquiv N s K hK hNs hs hN hsc g).1 : G) = g * (s (N g))⁻¹ := rfl

@[simp] theorem splitEquiv_apply_snd (g : G) : (splitEquiv N s K hK hNs hs hN hsc g).2 = N g := rfl

@[simp] theorem splitEquiv_symm_apply (p : K × Multiplicative ℝ) :
    (splitEquiv N s K hK hNs hs hN hsc).symm p = (p.1 : G) * s p.2 := rfl

end Split

/-! ### Splitting a Haar measure -/

section Measure

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  [SecondCountableTopology H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space H] [T2Space K]

/-- **The first factor of a split Haar measure**: for $\Phi : G\cong H\times K$ and Haar measures $\mu$ on $G$, $\nu$ on
$K$, the Haar measure $\mu^1$ on $H$ with $\Phi_*\mu = \mu^1\times\nu$ (`map_eq_prod_splitMeasure`). -/
def splitMeasure (Φ : G ≃ₜ* (H × K)) (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K)
    [ν.IsHaarMeasure] : Measure H :=
  Measure.haarScalarFactor (μ.map Φ) ((Measure.haar : Measure H).prod ν) • (Measure.haar : Measure H)

variable (Φ : G ≃ₜ* (H × K)) (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure]

instance isHaarMeasure_splitMeasure : (splitMeasure Φ μ ν).IsHaarMeasure := by
  have := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map Φ) ((Measure.haar : Measure H).prod ν)
  exact Measure.IsHaarMeasure.nnreal_smul _ this.ne'

/-- **$\Phi_*\mu = \mu^1\times\nu$** (uniqueness of Haar measure on the second countable group $H\times K$). -/
@[kb "weil1982" "§2.3 [unverified page] (ω on A_𝔸^× = ω^1 × dt/t)"]
theorem map_eq_prod_splitMeasure : μ.map Φ = (splitMeasure Φ μ ν).prod ν := by
  rw [splitMeasure, Measure.prod_smul_left]
  exact Measure.isMulLeftInvariant_eq_smul _ _

/-- **Uniqueness of the first factor**: if $\Phi_*\mu = \mu_1\times\nu$ then $\mu_1$ = `splitMeasure Φ μ ν`. -/
theorem splitMeasure_unique {μ₁ : Measure H} [SigmaFinite μ₁] (h : μ.map Φ = μ₁.prod ν) :
    μ₁ = splitMeasure Φ μ ν := by
  obtain ⟨B, hB, hB0, hBT⟩ : ∃ B : Set K, MeasurableSet B ∧ ν B ≠ 0 ∧ ν B ≠ ⊤ := by
    obtain ⟨C⟩ : Nonempty (TopologicalSpace.PositiveCompacts K) := inferInstance
    exact ⟨C, C.isCompact.measurableSet, (Measure.measure_pos_of_nonempty_interior ν C.interior_nonempty).ne',
      C.isCompact.measure_lt_top.ne⟩
  ext E hE
  have h1 := congrArg (fun m : Measure (H × K) => m (E ×ˢ B)) h
  have h2 := congrArg (fun m : Measure (H × K) => m (E ×ˢ B)) (map_eq_prod_splitMeasure Φ μ ν)
  simp only [Measure.prod_prod] at h1 h2
  have := h1.symm.trans h2
  exact (ENNReal.mul_left_inj hB0 hBT).mp this

/-- **$\mu^1(E) = \mu(\Phi^{-1}(E\times B))/\nu(B)$** for every measurable $B$ with $0 < \nu(B) < \infty$. -/
theorem splitMeasure_apply {B : Set K} (hB0 : ν B ≠ 0) (hBT : ν B ≠ ⊤) (E : Set H) :
    splitMeasure Φ μ ν E = μ (Φ ⁻¹' (E ×ˢ B)) / ν B := by
  have h := congrArg (fun m : Measure (H × K) => m (E ×ˢ B)) (map_eq_prod_splitMeasure Φ μ ν)
  simp only [Measure.prod_prod] at h
  rw [show (⇑Φ : G → H × K) = Φ.toHomeomorph.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply] at h
  rw [ENNReal.eq_div_iff hB0 hBT, mul_comm, ← h]
  rfl

end Measure

end

end QuadFormsKB.Tamagawa.Measure.Weil
