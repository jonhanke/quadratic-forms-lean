/-
# The $q$-coefficients of $\theta_Q$ and $\theta_{\mathrm{Gen}}$ over $F$

**Setting.** $F$ totally real, $a_\nu(f)$ = `qCoeff f (koecherBasis 1) (realVec ν)` for $\nu \in \mathfrak d^{-1}$ (`dualElt 1 m`), the
$q$-coefficients for the period lattice $\mathcal O_F$.

**Proves**
- **linearity** of $q$-coefficients over finite combinations of holomorphic periodic functions (`qCoeff_sum_smul`, `qCoeff_sub`),
  from the uniqueness of $q$-expansions (`qCoeff_unique`);
- **the coefficients of $\theta_Q$** (`qCoeff_thetaQ`): $a_\nu(\theta_Q) = r_Q(\nu)$ for $\nu \in \mathcal O_F$ and $a_\nu(\theta_Q) = 0$ for
  $\nu \in \mathfrak d^{-1}\setminus\mathcal O_F$ (from the $q$-expansion `hasSum_thetaQ`).
-/
import QuadFormsKB.HilbertModular.HeckeVanishing
import QuadFormsKB.HilbertModular.Theta

open NumberField Complex
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### Linearity of $q$-coefficients -/

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Type*} [Fintype J] {b : Module.Basis J ℝ (ι → ℝ)}

lemma IsLatticePeriodic.sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℂ) {f : κ → (ι → UpperHalfPlane) → ℂ}
    (hf : ∀ i ∈ s, IsLatticePeriodic (f i) b) : IsLatticePeriodic (∑ i ∈ s, c i • f i) b := by
  intro m x y hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [hf i hi m x y hy]

lemma IsHolomorphic.sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℂ) {f : κ → (ι → UpperHalfPlane) → ℂ}
    (hf : ∀ i ∈ s, IsHolomorphic (f i)) : IsHolomorphic (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHolomorphic_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul (c a)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma norm_qTerm_one (ν : ι → ℝ) : ‖qTerm ν (ptXY 0 1)‖ = Real.exp (-2 * π * pair ν 1) := by
  rw [norm_qTerm, imVec_ptXY (y := 1) (fun _ => one_pos)]

/-- **Linearity of $q$-coefficients**: $a_\nu\big(\sum_i c_if_i\big) = \sum_i c_i\,a_\nu(f_i)$ for $f_i$ holomorphic and periodic. -/
theorem qCoeff_sum_smul {κ : Type*} (s : Finset κ) (c : κ → ℂ) {f : κ → (ι → UpperHalfPlane) → ℂ}
    (hf : ∀ i ∈ s, IsHolomorphic (f i)) (hper : ∀ i ∈ s, IsLatticePeriodic (f i) b) (n : J → ℤ) :
    qCoeff (∑ i ∈ s, c i • f i) b (dualVec b n) = ∑ i ∈ s, c i * qCoeff (f i) b (dualVec b n) := by
  symm
  refine qCoeff_unique (IsHolomorphic.sum_smul s c hf) (IsLatticePeriodic.sum_smul s c hper)
    (α := fun n => ∑ i ∈ s, c i * qCoeff (f i) b (dualVec b n)) (y := 1) (fun _ => one_pos) ?_ ?_ n
  · -- summability, termwise
    have h : ∀ i ∈ s, Summable fun n => ‖c i‖ * (‖qCoeff (f i) b (dualVec b n)‖ *
        Real.exp (-2 * π * pair (dualVec b n) 1)) := by
      intro i hi
      refine (summable_norm_qExpansion (hf i hi) (hper i hi) (ptXY 0 1)).mul_left ‖c i‖ |>.congr fun n => ?_
      rw [norm_mul, norm_qTerm_one]
    refine (summable_sum h).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
    calc ‖∑ i ∈ s, c i * qCoeff (f i) b (dualVec b n)‖ * Real.exp (-2 * π * pair (dualVec b n) 1) ≤
          (∑ i ∈ s, ‖c i * qCoeff (f i) b (dualVec b n)‖) * Real.exp (-2 * π * pair (dualVec b n) 1) :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = _ := by rw [Finset.sum_mul]; simp [norm_mul, mul_assoc]
  · intro x
    have h : ∀ i ∈ s, HasSum (fun n => c i * qCoeff (f i) b (dualVec b n) * qTerm (dualVec b n) (ptXY x 1))
        (c i * f i (ptXY x 1)) := fun i hi => by
      simpa [mul_assoc] using (hasSum_qExpansion (hf i hi) (hper i hi) (ptXY x 1)).mul_left (c i)
    have := hasSum_sum h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa [Finset.sum_mul] using this

/-- $a_\nu(f - g) = a_\nu(f) - a_\nu(g)$. -/
theorem qCoeff_sub {f g : (ι → UpperHalfPlane) → ℂ} (hf : IsHolomorphic f) (hg : IsHolomorphic g)
    (hpf : IsLatticePeriodic f b) (hpg : IsLatticePeriodic g b) (n : J → ℤ) :
    qCoeff (f - g) b (dualVec b n) = qCoeff f b (dualVec b n) - qCoeff g b (dualVec b n) := by
  have e : f - g = ∑ i ∈ (Finset.univ : Finset (Fin 2)), ((![1, -1] : Fin 2 → ℂ) i) • (![f, g] i) := by
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [e, qCoeff_sum_smul (f := ![f, g]) _ (![1, -1] : Fin 2 → ℂ) (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

end Linear

/-! ### The coefficients of $\theta_Q$ -/

section Theta

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "I1" => (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- Every $\nu \in \mathcal O_F$ is a dual lattice point $\nu_m$ (`dualElt 1 m`): $\mathcal O_F \subseteq \mathfrak d^{-1}$. -/
lemma exists_dualElt_eq_int (ν : 𝓞 F) : ∃ m, QuadFormsKB.Analysis.dualElt I1 m = (ν : F) := by
  rw [exists_dualElt_iff]
  intro i
  obtain ⟨b, hb⟩ := mem_one_units.mp (bq_mem I1 i)
  refine ⟨Algebra.intTrace ℤ (𝓞 F) (b * ν), ?_⟩
  rw [← hb, show algebraMap (𝓞 F) F b * (ν : F) = algebraMap (𝓞 F) F (b * ν) by push_cast; rfl,
    (Algebra.algebraMap_intTrace (A := ℤ) (B := 𝓞 F) (b * ν)).symm]
  simp

lemma dualElt_injective : Function.Injective (QuadFormsKB.Analysis.dualElt (F := F) I1) := by
  intro m m' h
  funext i
  have h1 := QuadFormsKB.Analysis.trace_bq_mul_dualElt I1 i m
  have h2 := QuadFormsKB.Analysis.trace_bq_mul_dualElt I1 i m'
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

/-- The dual lattice index of $\nu \in \mathcal O_F$. -/
noncomputable def mOf (ν : 𝓞 F) : Fin (Module.finrank ℚ F) → ℤ := (exists_dualElt_eq_int ν).choose

lemma dualElt_mOf (ν : 𝓞 F) : QuadFormsKB.Analysis.dualElt I1 (mOf ν) = (ν : F) :=
  (exists_dualElt_eq_int ν).choose_spec

lemma mOf_injective : Function.Injective (mOf (F := F)) := by
  intro ν ν' h
  have := congrArg (QuadFormsKB.Analysis.dualElt I1) h
  rw [dualElt_mOf, dualElt_mOf] at this
  exact IsFractionRing.injective (𝓞 F) F this

open Classical in
/-- **The coefficients of $\theta_Q$ as a function on $\mathfrak d^{-1}$**: $r_Q(\nu)$ if $\nu_m = \nu \in \mathcal O_F$, else $0$. -/
noncomputable def thetaCoeffQ (Q : QuadForm (𝓞 F) n) (m : Fin (Module.finrank ℚ F) → ℤ) : ℂ :=
  if h : ∃ ν : 𝓞 F, (ν : F) = QuadFormsKB.Analysis.dualElt I1 m then (repNumF Q h.choose : ℂ) else 0

lemma thetaCoeffQ_mOf (Q : QuadForm (𝓞 F) n) (ν : 𝓞 F) : thetaCoeffQ Q (mOf ν) = repNumF Q ν := by
  have h : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 (mOf ν) := ⟨ν, (dualElt_mOf ν).symm⟩
  rw [thetaCoeffQ, dif_pos h]
  have : h.choose = ν := IsFractionRing.injective (𝓞 F) F (h.choose_spec.trans (dualElt_mOf ν))
  rw [this]

lemma thetaCoeffQ_eq_zero (Q : QuadForm (𝓞 F) n) {m : Fin (Module.finrank ℚ F) → ℤ}
    (hm : m ∉ Set.range (mOf (F := F))) : thetaCoeffQ Q m = 0 := by
  rw [thetaCoeffQ, dif_neg]
  rintro ⟨ν, hν⟩
  exact hm ⟨ν, dualElt_injective ((dualElt_mOf ν).trans hν)⟩

/-- **The $q$-coefficients of $\theta_Q$** ($Q$ totally positive definite over $\mathcal O_F$, $\theta_Q$ periodic for $\mathcal O_F$): for
$\nu \in \mathfrak d^{-1}$, $a_\nu(\theta_Q) = r_Q(\nu)$ if $\nu \in \mathcal O_F$ and $0$ otherwise (`thetaCoeffQ`). From the $q$-expansion
$\theta_Q = \sum_{\nu\in\mathcal O_F}r_Q(\nu)e(\operatorname{Tr}\nu z)$ (`hasSum_thetaQ`) and uniqueness (`qCoeff_unique`). -/
@[kb "freitag1990" "Ch. I §4, the Fourier coefficients of θ_Q [unverified]"]
theorem qCoeff_thetaQ {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (hper : IsLatticePeriodic (thetaQ Q) (koecherBasis I1)) (m : Fin (Module.finrank ℚ F) → ℤ) :
    qCoeff (thetaQ Q) (koecherBasis I1) (realVec (QuadFormsKB.Analysis.dualElt I1 m)) = thetaCoeffQ Q m := by
  classical
  rw [← dualVec_koecherBasis]
  symm
  have hterm : ∀ (ν : 𝓞 F) (z : InfinitePlace F → UpperHalfPlane),
      qTerm (dualVec (koecherBasis I1) (mOf ν)) z =
        cexp (2 * Real.pi * Complex.I * ∑ v, (realEmb F v (algebraMap (𝓞 F) F ν) : ℂ) * (z v : ℂ)) := by
    intro ν z
    rw [dualVec_koecherBasis, dualElt_mOf, qTerm]
    rfl
  refine qCoeff_unique (isHolomorphic_thetaQ hQ) hper (α := thetaCoeffQ Q) (y := 1) (fun _ => one_pos) ?_ ?_ m
  · -- summability via the injection `mOf`
    have hz : (fun _ => (1 : ℝ)) = (1 : InfinitePlace F → ℝ) := rfl
    set g : (Fin (Module.finrank ℚ F) → ℤ) → ℝ := fun n =>
      ‖thetaCoeffQ Q n‖ * Real.exp (-2 * π * pair (dualVec (koecherBasis I1) n) 1)
    have hzero : ∀ n ∉ Set.range (mOf (F := F)), g n = 0 := fun n hn => by
      simp [g, thetaCoeffQ_eq_zero Q hn]
    rw [← (mOf_injective (F := F)).summable_iff hzero]
    have hs := (summable_norm_thetaQTerm hQ (ptXY 0 1)).hasSum.tsum_fiberwise (fun x => Q.eval x)
    refine hs.summable.congr fun ν => ?_
    simp only [Function.comp_apply, g, thetaCoeffQ_mOf]
    have : ∀ x : ((fun x : Fin n → 𝓞 F => Q.eval x) ⁻¹' {ν}),
        ‖thetaQTerm Q (ptXY 0 1) x‖ = ‖qTerm (dualVec (koecherBasis I1) (mOf ν)) (ptXY 0 1)‖ := by
      rintro ⟨x, hx⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [hterm]; simp [thetaQTerm, hx]
    rw [tsum_congr this, tsum_const, nsmul_eq_mul, norm_qTerm_one, Complex.norm_natCast]
    rfl
  · intro x
    set f : (Fin (Module.finrank ℚ F) → ℤ) → ℂ := fun n =>
      thetaCoeffQ Q n * qTerm (dualVec (koecherBasis I1) n) (ptXY x 1)
    have hzero : ∀ n ∉ Set.range (mOf (F := F)), f n = 0 := fun n hn => by
      simp [f, thetaCoeffQ_eq_zero Q hn]
    rw [← (mOf_injective (F := F)).hasSum_iff hzero]
    convert hasSum_thetaQ hQ (ptXY x 1) using 1
    funext ν
    simp only [Function.comp_apply, f, thetaCoeffQ_mOf, hterm]

end Theta

end QuadFormsKB.HilbertModular
