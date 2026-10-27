import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayProps
import QuadFormsKB.Tamagawa.Measure.ConeAlgebra
import QuadFormsKB.Weil.ProductFormulas

/-!
# Charts for the Leray measures of the cone form at a finite place

$F_v$ = `v.adicCompletion F` ($v$ a finite place of a number field $F$, dyadic included), $\nu$ = `haarV v`
($\nu(\mathcal O_v) = 1$), $\mathrm{vol} = \nu^{\otimes n}$ on $F_v^n$, and $\sigma_\rho$ = the Leray measure
`lerayMeasure v ν Q hQ ρ` ($\sigma_\rho(U) = \lim_K \mathrm{vol}(U \cap Q^{-1}(\rho + \mathfrak p^K))/\nu(\mathfrak p^K)$ for
compact open $U \not\ni 0$). This file computes these measures in coordinates, for forms of the shape
$$Q(x_0, x_1, x') = c x_0^2 - c x_1^2 + Q'(x')\qquad(\text{the cone form }\langle c\rangle\perp\langle -c\rangle\perp Q').$$

* `vol_slab_le` (**the slab bound**): for $Q(x_0, x'') = A(x_0) + Q_2(x'')$ with $Q_2$ nondegenerate and $B''$ compact open
  avoiding $0$, $\mathrm{vol}\{x_0 \in W,\ x'' \in B'',\ Q(x) \in \rho + \mathfrak p^K\} \le M\,\nu(W)\,\nu(\mathfrak p^K)$ with $M$
  independent of $W$, $\rho$ and $K$ (from the stabilization `lerayThick_eventually_succ`, whose threshold does not depend
  on $\rho$). This is what makes hyperplane sections of the level sets null.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Preliminaries -/

section Prelim

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- **Fubini in the first coordinate**: $\int G\,d\mathrm{vol}_{n+1} = \int\!\int G(x_0, x'')\,d\mathrm{vol}_n(x'')\,d\nu(x_0)$. -/
theorem lintegral_volV_cons {N : ℕ} {G : (Fin (N + 1) → Fv) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂volV ν (N + 1) = ∫⁻ a, ∫⁻ y, G (Fin.cons a y) ∂volV ν N ∂ν := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Fv) 0
  have hE : MeasurePreserving E (volV ν (N + 1)) (ν.prod (volV ν N)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => ν) 0
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun a => lintegral_congr fun y => ?_
  congr 1
  simp [E, MeasurableEquiv.piFinSuccAbove]
  rfl

/-- The volume of a set in the first-coordinate splitting. -/
theorem volV_cons {N : ℕ} {S : Set (Fin (N + 1) → Fv)} (hS : MeasurableSet S) :
    volV ν (N + 1) S = ∫⁻ a, volV ν N {y | (Fin.cons a y : Fin (N + 1) → Fv) ∈ S} ∂ν := by
  rw [← lintegral_indicator_one hS, lintegral_volV_cons v ν ((measurable_one).indicator hS)]
  refine lintegral_congr fun a => ?_
  rw [← lintegral_indicator_one]
  · rfl
  · exact hS.preimage (continuous_const.finCons continuous_id).measurable

/-- Shell membership in terms of the norm. -/
theorem mem_shell_iff_norm {ρ y : Fv} {K : ℕ} : y ∈ shell v ρ K ↔ ‖y - ρ‖ ≤ ‖HN.ϖ v‖ ^ K := by
  rw [norm_le_iff_v]; rfl

theorem mem_latticeV_iff_norm {y : Fv} {K : ℕ} : y ∈ latticeV v (K : ℤ) ↔ ‖y‖ ≤ ‖HN.ϖ v‖ ^ K := by
  rw [norm_le_iff_v, mem_latticeV]

/-- Shells are translates: $y \in \rho + \mathfrak p^K \iff y - t \in (\rho - t) + \mathfrak p^K$. -/
theorem mem_shell_sub {ρ y t : Fv} {K : ℕ} : y - t ∈ shell v (ρ - t) K ↔ y ∈ shell v ρ K := by
  simp only [shell, Set.mem_setOf_eq, sub_sub_sub_cancel_right]

/-- **$\nu(\mathfrak p^j) \to 0$.** -/
theorem tendsto_measure_latticeV : Tendsto (fun j : ℕ => ν (latticeV v (j : ℤ) : Set Fv)) atTop (𝓝 0) := by
  have hanti : Antitone fun j : ℕ => (latticeV v (j : ℤ) : Set Fv) := by
    intro i j hij x hx
    rw [SetLike.mem_coe, mem_latticeV] at hx ⊢
    exact hx.trans (exp_le_exp.mpr (by omega))
  have hInter : (⋂ j : ℕ, (latticeV v (j : ℤ) : Set Fv)) = {0} := by
    ext x
    simp only [Set.mem_iInter, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · intro h
      have hle : ∀ j : ℕ, ‖x‖ ≤ ‖HN.ϖ v‖ ^ j := fun j => (mem_latticeV_iff_norm v).mp (h j)
      have h0 : ‖x‖ ≤ 0 := ge_of_tendsto
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_ϖ_lt_one v)) (Eventually.of_forall hle)
      exact norm_le_zero_iff.mp h0
    · rintro rfl j; exact (latticeV v (j : ℤ)).zero_mem
  have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun j : ℕ => (latticeV v (j : ℤ) : Set Fv))
    (fun j => (measurableSet_latticeV v (j : ℤ)).nullMeasurableSet)
    hanti ⟨0, measure_latticeV_ne_top v ν 0⟩
  rwa [hInter, measure_singleton] at h

end Prelim

/-! ### The slab bound -/

section Slab

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- **Uniform bound for the thickened Leray measures of one compact open set**: for $Q$ nondegenerate and $B$ compact
open with $0 \notin B$, there is $M < \infty$ with $\mathrm{vol}(B \cap Q^{-1}(t + \mathfrak p^K)) \le M\,\nu(\mathfrak p^K)$ for
**all** $t$ and $K$. -/
theorem exists_vol_shell_le {b : ℕ} (Q : QuadForm 𝔬 b) (hQ : Q.Nondegenerate) {B : Set (Fin b → Fv)}
    (hB : B ∈ Cz v b) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (t : Fv) (K : ℕ),
      volV ν b (B ∩ Qv v Q ⁻¹' shell v t K) ≤ M * ν (latticeV v (K : ℤ) : Set Fv) := by
  obtain ⟨K₀, hK₀⟩ := lerayThick_eventually_succ v ν Q hQ hB.1 hB.2.1 hB.2.2
  have hBfin : volV ν b B ≠ ⊤ := hB.1.measure_lt_top.ne
  set L : ℕ → ℝ≥0∞ := fun K => ν (latticeV v (K : ℤ) : Set Fv) with hL
  have hL0 : ∀ K, L K ≠ 0 := fun K => (measure_latticeV_pos v ν K).ne'
  have hLt : ∀ K, L K ≠ ⊤ := fun K => measure_latticeV_ne_top v ν K
  have hLanti : ∀ {i j : ℕ}, i ≤ j → L j ≤ L i := by
    intro i j hij
    refine measure_mono ?_
    intro x hx
    rw [SetLike.mem_coe, mem_latticeV] at hx ⊢
    exact hx.trans (exp_le_exp.mpr (by omega))
  refine ⟨volV ν b B / L K₀, ENNReal.div_ne_top hBfin (hL0 K₀), fun t K => ?_⟩
  have hmeas : MeasurableSet B := hB.2.1.measurableSet
  -- `λ_{t,K}(B) = λ_{t,K₀}(B)` for `K ≥ K₀`
  have hstab : ∀ K ≥ K₀, lerayThick ν (Qv v Q) (shell v t K) B = lerayThick ν (Qv v Q) (shell v t K₀) B := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => rfl
    | succ K hK ih => rw [← hK₀ t K hK, ih]
  have happ : ∀ K, lerayThick ν (Qv v Q) (shell v t K) B = (L K)⁻¹ * volV ν b (B ∩ Qv v Q ⁻¹' shell v t K) := by
    intro K; rw [lerayThick_apply ν _ _ hmeas, measure_shell]
  rcases le_or_gt K₀ K with hK | hK
  · have h1 := hstab K hK
    rw [happ, happ] at h1
    have h2 : volV ν b (B ∩ Qv v Q ⁻¹' shell v t K) = L K * ((L K₀)⁻¹ * volV ν b (B ∩ Qv v Q ⁻¹' shell v t K₀)) := by
      rw [← h1, ← mul_assoc, ENNReal.mul_inv_cancel (hL0 K) (hLt K), one_mul]
    rw [h2, mul_comm (L K)]
    gcongr
    rw [ENNReal.div_eq_inv_mul]
    gcongr
    exact Set.inter_subset_left
  · calc volV ν b (B ∩ Qv v Q ⁻¹' shell v t K) ≤ volV ν b B := measure_mono Set.inter_subset_left
      _ = volV ν b B / L K₀ * L K₀ := (ENNReal.div_mul_cancel (hL0 K₀) (hLt K₀)).symm
      _ ≤ volV ν b B / L K₀ * L K := by gcongr; exact hLanti hK.le

/-- **The slab bound.** Let $Q_2$ be nondegenerate in $b$ variables, $B''$ compact open with $0 \notin B''$, and
$A : F_v \to F_v$ measurable. There is $M < \infty$ such that for every measurable $W \subseteq F_v$, every $\rho$ and every
$K$, $\mathrm{vol}_{b+1}\{x : x_0 \in W,\ x'' \in B'',\ A(x_0) + Q_2(x'') \in \rho + \mathfrak p^K\} \le
M\,\nu(W)\,\nu(\mathfrak p^K)$. -/
theorem vol_slab_le {b : ℕ} (Q₂ : QuadForm 𝔬 b) (hQ₂ : Q₂.Nondegenerate) {B : Set (Fin b → Fv)}
    (hB : B ∈ Cz v b) {A : Fv → Fv} (hA : Measurable A) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (W : Set Fv), MeasurableSet W → ∀ (ρ : Fv) (K : ℕ),
      volV ν (b + 1) {x | x 0 ∈ W ∧ Fin.tail x ∈ B ∧ A (x 0) + Qv v Q₂ (Fin.tail x) ∈ shell v ρ K} ≤
        M * ν W * ν (latticeV v (K : ℤ) : Set Fv) := by
  obtain ⟨M, hM, hbound⟩ := exists_vol_shell_le v ν Q₂ hQ₂ hB
  refine ⟨M, hM, fun W hW ρ K => ?_⟩
  have hmeasB : MeasurableSet B := hB.2.1.measurableSet
  have hQm : Measurable (Qv v Q₂) := measurable_qv v Q₂
  have hS : MeasurableSet {x : Fin (b + 1) → Fv | x 0 ∈ W ∧ Fin.tail x ∈ B ∧
      A (x 0) + Qv v Q₂ (Fin.tail x) ∈ shell v ρ K} := by
    have ht : Measurable (Fin.tail : (Fin (b + 1) → Fv) → Fin b → Fv) :=
      (continuous_pi fun i => continuous_apply _).measurable
    refine (hW.preimage (measurable_pi_apply 0)).inter ((hmeasB.preimage ht).inter ?_)
    exact (measurableSet_shell v ρ K).preimage ((hA.comp (measurable_pi_apply 0)).add (hQm.comp ht))
  rw [volV_cons v ν hS]
  calc ∫⁻ a, volV ν b {y | (Fin.cons a y : Fin (b + 1) → Fv) ∈ {x : Fin (b + 1) → Fv | x 0 ∈ W ∧ Fin.tail x ∈ B ∧
        A (x 0) + Qv v Q₂ (Fin.tail x) ∈ shell v ρ K}} ∂ν
      ≤ ∫⁻ a, W.indicator (fun _ => M * ν (latticeV v (K : ℤ) : Set Fv)) a ∂ν := by
        refine lintegral_mono fun a => ?_
        by_cases ha : a ∈ W
        · rw [Set.indicator_of_mem ha]
          refine (measure_mono ?_).trans (hbound (ρ - A a) K)
          intro y hy
          simp only [Set.mem_setOf_eq, Fin.cons_zero, Fin.tail_cons] at hy
          refine ⟨hy.2.1, ?_⟩
          show Qv v Q₂ y ∈ shell v (ρ - A a) K
          have h := hy.2.2
          simp only [shell, Set.mem_setOf_eq] at h ⊢
          rwa [show Qv v Q₂ y - (ρ - A a) = A a + Qv v Q₂ y - ρ by ring]
        · rw [Set.indicator_of_notMem ha]
          refine le_of_eq (measure_eq_zero_iff_ae_notMem.mpr (Eventually.of_forall fun y hy => ?_))
          simp only [Set.mem_setOf_eq, Fin.cons_zero] at hy
          exact ha hy.1
    _ = M * ν W * ν (latticeV v (K : ℤ) : Set Fv) := by
        rw [lintegral_indicator_const hW]; ring

end Slab

/-! ### Scaling of the Leray measures by an arbitrary $t \in F_v^\times$ -/

section Scaling

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure] {n : ℕ}
  (Q : QuadForm (v.adicCompletionIntegers F) n) (hQ : Q.Nondegenerate)

/-- For $|t| \le 1$, $|t| = q^{-d}$: $t^2(\rho + \mathfrak p^K) = t^2\rho + \mathfrak p^{K + 2d}$. -/
theorem smul_shell_of_valued {t : Fv} (ht : t ≠ 0) {d : ℕ} (hd : Valued.v t = exp (-(d : ℤ))) (ρ : Fv) (K : ℕ) :
    (t ^ 2) • shell v ρ K = shell v (t ^ 2 * ρ) (K + 2 * d) := by
  have hv2 : Valued.v (t ^ 2) = exp (-((2 * d : ℕ) : ℤ)) := by
    rw [map_pow, hd, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
  have hne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  ext x
  simp only [Set.mem_smul_set, shell, Set.mem_setOf_eq, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [show t ^ 2 * y - t ^ 2 * ρ = t ^ 2 * (y - ρ) by ring, map_mul, hv2]
    calc exp (-((2 * d : ℕ) : ℤ)) * Valued.v (y - ρ) ≤ exp (-((2 * d : ℕ) : ℤ)) * exp (-(K : ℤ)) := by gcongr
      _ = exp (-((K + 2 * d : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
  · intro hx
    refine ⟨x / t ^ 2, ?_, mul_div_cancel₀ _ hne⟩
    rw [show x / t ^ 2 - ρ = (x - t ^ 2 * ρ) / t ^ 2 by field_simp, map_div₀, hv2,
      div_le_iff₀ (by simp)]
    calc Valued.v (x - t ^ 2 * ρ) ≤ exp (-((K + 2 * d : ℕ) : ℤ)) := hx
      _ = exp (-(K : ℤ)) * exp (-((2 * d : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring

include hQ in
/-- Scaling for $|t| \le 1$. -/
theorem lerayMeasure_map_smul_of_valued (t : Fvˣ) {d : ℕ} (hd : Valued.v (t : Fv) = exp (-(d : ℤ))) (ρ : Fv) :
    Measure.map (fun x : Fin n → Fv => (t : Fv) • x) (lerayMeasure v ν Q hQ ρ) =
      ((distribHaarChar Fv t : ℝ≥0∞) ^ 2 / (distribHaarChar Fv t : ℝ≥0∞) ^ n) •
        lerayMeasure v ν Q hQ ((t : Fv) ^ 2 * ρ) := by
  set g : GL (Fin n) Fv := diagGL fun _ => t
  have hfun : (fun x : Fin n → Fv => (t : Fv) • x) = fun x => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x := by
    funext x i; simp [g, coe_diagGL, Matrix.mulVec_diagonal]
  have hmeas : Measurable fun x : Fin n → Fv => (t : Fv) • x := by
    rw [hfun]; exact (continuous_const.matrix_mulVec continuous_id).measurable
  have hpre0 : (fun x : Fin n → Fv => (t : Fv) • x) ⁻¹' {0} = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h (Units.ne_zero _)
      · exact h
    · rintro rfl; simp
  refine measure_ext_Cz v ?_ ?_ ?_ ?_
  · rw [Measure.map_apply hmeas (measurableSet_singleton _), hpre0]
    exact lerayMeasure_singleton_zero v ν Q hQ ρ
  · simp [lerayMeasure_singleton_zero]
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet, hfun]
    exact (lerayMeasure_lt_top v ν Q hQ ρ (preimage_mulVec_mem_Cz v _ hU)).ne
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet, hfun, Measure.smul_apply, smul_eq_mul]
    have hU' := preimage_mulVec_mem_Cz v g hU
    have hev1 := lerayMeasure_eventually v ν Q hQ ρ hU'
    have hev2 := (tendsto_add_atTop_nat (2 * d)).eventually
      (lerayMeasure_eventually v ν Q hQ ((t : Fv) ^ 2 * ρ) hU)
    obtain ⟨K, hk1, hk2⟩ := (hev1.and hev2).exists
    rw [← hk1, ← hk2]
    have hmap := map_smul_lerayThick ν (Qv v Q) t (fun x => qv_smul v Q _ x) (shell v ρ K)
    have hsh : (((t ^ 2 : Fvˣ)) : Fv) • shell v ρ K = shell v ((t : Fv) ^ 2 * ρ) (K + 2 * d) := by
      rw [Units.val_pow_eq_pow_val]; exact smul_shell_of_valued v t.ne_zero hd ρ K
    rw [hsh] at hmap
    have := congrArg (fun m => m U) hmap
    simp only [Measure.map_apply hmeas hU.2.1.measurableSet, Measure.smul_apply, smul_eq_mul] at this
    rw [← hfun]
    exact this

include hQ in
/-- **Scaling of the Leray measure by any $t \in F_v^\times$**: $(x \mapsto tx)_*\sigma_\rho =
\Delta(t)^{2-n}\sigma_{t^2\rho}$, $\Delta = $ `distribHaarChar` ($= |t|_v$). -/
theorem lerayMeasure_map_smul_units (t : Fvˣ) (ρ : Fv) :
    Measure.map (fun x : Fin n → Fv => (t : Fv) • x) (lerayMeasure v ν Q hQ ρ) =
      ((distribHaarChar Fv t : ℝ≥0∞) ^ 2 / (distribHaarChar Fv t : ℝ≥0∞) ^ n) •
        lerayMeasure v ν Q hQ ((t : Fv) ^ 2 * ρ) := by
  have hv0 : Valued.v (t : Fv) ≠ 0 := (Valued.v).ne_zero_iff.mpr t.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (t : Fv) = exp m := ⟨_, (exp_log hv0).symm⟩
  rcases le_or_gt m 0 with hm0 | hm0
  · have hd : Valued.v (t : Fv) = exp (-((-m).toNat : ℤ)) := by
      rw [hm, Int.toNat_of_nonneg (by omega), neg_neg]
    exact lerayMeasure_map_smul_of_valued v ν Q hQ t hd ρ
  · -- apply the first case to `t⁻¹`
    have hd : Valued.v ((t⁻¹ : Fvˣ) : Fv) = exp (-((m.toNat : ℕ) : ℤ)) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hm, Int.toNat_of_nonneg hm0.le, WithZero.exp_neg]
    have h := lerayMeasure_map_smul_of_valued v ν Q hQ t⁻¹ hd ((t : Fv) ^ 2 * ρ)
    have hρ : ((t⁻¹ : Fvˣ) : Fv) ^ 2 * ((t : Fv) ^ 2 * ρ) = ρ := by
      rw [Units.val_inv_eq_inv_val, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ t.ne_zero, one_pow, one_mul]
    rw [hρ] at h
    have hmeas : ∀ s : Fvˣ, Measurable fun x : Fin n → Fv => (s : Fv) • x := fun s =>
      (continuous_const_smul _).measurable
    have hcomp : (fun x : Fin n → Fv => (t : Fv) • x) ∘ (fun x => ((t⁻¹ : Fvˣ) : Fv) • x) = id := by
      funext x; simp [smul_smul]
    have h2 := congrArg (Measure.map fun x : Fin n → Fv => (t : Fv) • x) h
    rw [Measure.map_map (hmeas t) (hmeas t⁻¹), hcomp, Measure.map_id, Measure.map_smul _ (hmeas t).aemeasurable] at h2
    have hΔ : (distribHaarChar Fv t⁻¹ : ℝ≥0∞) = (distribHaarChar Fv t : ℝ≥0∞)⁻¹ := by
      rw [map_inv, ENNReal.coe_inv (distribHaarChar_pos (A := Fv) (g := t)).ne']
    have hΔ0 : (distribHaarChar Fv t : ℝ≥0∞) ≠ 0 := by
      simpa using (distribHaarChar_pos (A := Fv) (g := t)).ne'
    have hΔt : (distribHaarChar Fv t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [h2, smul_smul, hΔ]
    have hc : (distribHaarChar Fv t : ℝ≥0∞) ^ 2 / (distribHaarChar Fv t : ℝ≥0∞) ^ n *
        (((distribHaarChar Fv t : ℝ≥0∞)⁻¹) ^ 2 / ((distribHaarChar Fv t : ℝ≥0∞)⁻¹) ^ n) = 1 := by
      rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, inv_inv]
      have h1 : ((distribHaarChar Fv t : ℝ≥0∞) ^ n)⁻¹ * (distribHaarChar Fv t : ℝ≥0∞) ^ n = 1 :=
        ENNReal.inv_mul_cancel (pow_ne_zero _ hΔ0) (ENNReal.pow_ne_top hΔt)
      have h2 : (distribHaarChar Fv t : ℝ≥0∞) ^ 2 * ((distribHaarChar Fv t : ℝ≥0∞) ^ 2)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero _ hΔ0) (ENNReal.pow_ne_top hΔt)
      calc ((distribHaarChar Fv t : ℝ≥0∞) ^ n)⁻¹ * (distribHaarChar Fv t : ℝ≥0∞) ^ 2 *
            ((distribHaarChar Fv t : ℝ≥0∞) ^ n * ((distribHaarChar Fv t : ℝ≥0∞) ^ 2)⁻¹)
          = (((distribHaarChar Fv t : ℝ≥0∞) ^ n)⁻¹ * (distribHaarChar Fv t : ℝ≥0∞) ^ n) *
            ((distribHaarChar Fv t : ℝ≥0∞) ^ 2 * ((distribHaarChar Fv t : ℝ≥0∞) ^ 2)⁻¹) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    rw [hc, one_smul]

end Scaling

/-! ### Topological preliminaries -/

section Topo

theorem continuous_tail {N : ℕ} : Continuous (Fin.tail : (Fin (N + 1) → Fv) → Fin N → Fv) :=
  continuous_pi fun i => continuous_apply _

/-- A closed norm-ball condition on a continuous function is clopen (ultrametric). -/
theorem isClopen_norm_le {X : Type*} [TopologicalSpace X] {f : X → Fv} (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    IsClopen {x | ‖f x‖ ≤ r} := by
  have h : {x | ‖f x‖ ≤ r} = f ⁻¹' Metric.closedBall 0 r := by ext x; simp
  rw [h]
  exact ⟨Metric.isClosed_closedBall.preimage hf,
    (IsUltrametricDist.isOpen_closedBall (0 : Fv) hr.ne').preimage hf⟩

/-- A big ball minus a small box is compact open and avoids $0$. -/
theorem closedBall_diff_mem_Cz {N : ℕ} {R : ℝ} (hR : 0 < R) (s : ℕ) :
    Metric.closedBall (0 : Fin N → Fv) R \ cosetP v 0 s ∈ Cz v N :=
  ⟨(isCompact_closedBall _ _).diff (isOpen_cosetP v 0 s),
    (IsUltrametricDist.isOpen_closedBall _ hR.ne').sdiff
    (by rw [cosetP_eq]; exact Metric.isClosed_closedBall), fun h => h.2 (mem_cosetP_self v 0 s)⟩

/-- A compact open set is invariant under small translations. -/
theorem exists_add_mem {N : ℕ} {U : Set (Fin N → Fv)} (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ δ > 0, ∀ x z, ‖z‖ < δ → (x + z ∈ U ↔ x ∈ U) := by
  obtain ⟨δ, hδ, hthick⟩ := hUc.exists_thickening_subset_open hUo subset_rfl
  refine ⟨δ, hδ, fun x z hz => ⟨fun hxz => ?_, fun hx => ?_⟩⟩
  · apply hthick
    rw [Metric.mem_thickening_iff]
    exact ⟨x + z, hxz, by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hz⟩
  · apply hthick
    rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, by rw [dist_eq_norm, add_sub_cancel_left]; exact hz⟩

theorem norm_v3_le {k : ℕ} (a b : Fv) (y : Fin k → Fv) {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖ConeAlgebra.v3 a b y‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  refine Fin.cases ha (fun i => Fin.cases hb (fun i => ?_) i) i
  exact (norm_le_pi_norm y i).trans hy

theorem measurable_v3 {k : ℕ} : Measurable fun p : Fv × Fv × (Fin k → Fv) => ConeAlgebra.v3 p.1 p.2.1 p.2.2 :=
  (continuous_fst.finCons ((continuous_fst.comp continuous_snd).finCons
    (continuous_snd.comp continuous_snd))).measurable

end Topo

/-! ### The hyperbolic-split chart of the sphere $S_c$ -/

section Sphere

open ConeAlgebra

variable {k : ℕ} (Q' : QuadForm (v.adicCompletionIntegers F) k)

/-- The second coordinate $x_1 = b$ of the graph point over $(q, y)$:
$b = (c - cq^2 - Q'(y))/(2cq)$. -/
def graphB (c q : Fv) (y : Fin k → Fv) : Fv := (c - c * q ^ 2 - Qv v Q' y) / (2 * c * q)

/-- **The graph point** of $S_c$ over $(q, y)$: $x = (b + q, b, y)$, so that $x_0 - x_1 = q$, $x' = y$, and
$Q(x) = c$ for $q \ne 0$. -/
def graphV (c q : Fv) (y : Fin k → Fv) : Fin (k + 1 + 1) → Fv := v3 (graphB v Q' c q y + q) (graphB v Q' c q y) y

theorem measurable_graphV (c : Fv) : Measurable fun p : Fv × (Fin k → Fv) => graphV v Q' c p.1 p.2 := by
  have hQ : Measurable (Qv v Q') := measurable_qv v Q'
  have hb : Measurable fun p : Fv × (Fin k → Fv) => graphB v Q' c p.1 p.2 := by
    unfold graphB
    exact ((measurable_const.sub (measurable_const.mul (measurable_fst.pow_const 2))).sub
      (hQ.comp measurable_snd)).div (measurable_const.mul measurable_fst)
  exact (measurable_v3 v).comp ((hb.add measurable_fst).prodMk (hb.prodMk measurable_snd))

theorem graphV_sub (c q : Fv) (y : Fin k → Fv) : graphV v Q' c q y 0 - graphV v Q' c q y 1 = q := by
  simp [graphV]

theorem tl_graphV (c q : Fv) (y : Fin k → Fv) : tl (graphV v Q' c q y) = y := by simp [graphV]

variable {Q : QuadForm (v.adicCompletionIntegers F) (k + 1 + 1)} {c : v.adicCompletion F}

/-- The value of $Q$ along the line $a \mapsto (a, a - q, y)$: $Q - c = 2cq\,(a - a^*)$, $a^* = b + q$. -/
theorem qv_line (hc : c ≠ 0) (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x)) (a : Fv) {q : Fv}
    (hq : q ≠ 0) (y : Fin k → Fv) :
    Qv v Q (v3 a (a - q) y) - c = 2 * c * q * (a - (graphB v Q' c q y + q)) := by
  rw [hQeq, v3_zero', v3_one', tl_v3, graphB]
  field_simp
  ring

theorem graphV_eq_v3 (c q : Fv) (y : Fin k → Fv) :
    graphV v Q' c q y = v3 (graphB v Q' c q y + q) (graphB v Q' c q y + q - q) y := by
  rw [graphV, add_sub_cancel_right]

/-- The haar measure of $\{a : a - a^* \in \beta\,\mathfrak p^K\}$ is $|\beta|\,\nu(\mathfrak p^K)$. -/
theorem haarV_affine (a₀ : Fv) {β : Fv} (hβ : β ≠ 0) (K : ℕ) :
    haarV v {a | a - a₀ ∈ (fun z => β * z) '' (latticeV v (K : ℤ) : Set Fv)} =
      ENNReal.ofReal ‖β‖ * haarV v (latticeV v (K : ℤ) : Set Fv) := by
  have h : {a | a - a₀ ∈ (fun z => β * z) '' (latticeV v (K : ℤ) : Set Fv)} =
      (fun a => a + (-a₀)) ⁻¹' ((fun z => β * z) '' (latticeV v (K : ℤ) : Set Fv)) := by
    ext a; simp [sub_eq_add_neg]
  rw [h, measure_preimage_add_right, Analysis.Weil.measure_smul_eq (haarV v) hβ, WeilRep.modK_eq_norm v hβ]

/-- **The inner integral along a line** $a \mapsto (a, a - q, y)$: for $q \ne 0$ and $K$ large (relative to the
translation-invariance radius $\delta$ of $U$ and to $|2cq|$), the line meets $U \cap \{Q \in c + \mathfrak p^K\}$ in a ball of
measure $|2cq|^{-1}\nu(\mathfrak p^K)$ if the graph point lies in $U$, and not at all otherwise. -/
theorem lintegral_line_shell (hc : c ≠ 0) (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x))
    {U : Set (Fin (k + 1 + 1) → Fv)} {δ : ℝ} (hδ : ∀ x z, ‖z‖ < δ → (x + z ∈ U ↔ x ∈ U)) {q : Fv} (hq : q ≠ 0)
    (y : Fin k → Fv) {K : ℕ} (hK : ‖HN.ϖ v‖ ^ K < δ * ‖2 * c * q‖) :
    ∫⁻ a, (U ∩ Qv v Q ⁻¹' shell v c K).indicator 1 (v3 a (a - q) y) ∂haarV v =
      U.indicator 1 (graphV v Q' c q y) *
        (ENNReal.ofReal ‖2 * c * q‖⁻¹ * haarV v (latticeV v (K : ℤ) : Set Fv)) := by
  set a₀ := graphB v Q' c q y + q with ha₀
  have h2cq : 2 * c * q ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hq
  have hn2cq : 0 < ‖2 * c * q‖ := norm_pos_iff.mpr h2cq
  set T : Set Fv := {a | a - a₀ ∈ (fun z => (2 * c * q)⁻¹ * z) '' (latticeV v (K : ℤ) : Set Fv)} with hT
  have hTiff : ∀ a, a ∈ T ↔ Qv v Q (v3 a (a - q) y) ∈ shell v c K := by
    intro a
    simp only [hT, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, shell]
    rw [qv_line v Q' hc hQeq a hq y]
    constructor
    · rintro ⟨z, hz, hza⟩
      rw [← ha₀, ← hza, ← mul_assoc, mul_inv_cancel₀ h2cq, one_mul]
      exact (mem_latticeV v).mp hz
    · intro h
      refine ⟨2 * c * q * (a - a₀), (mem_latticeV v).mpr h, ?_⟩
      rw [← mul_assoc, inv_mul_cancel₀ h2cq, one_mul]
  have hsmall : ∀ a ∈ T, ‖a - a₀‖ < δ := by
    intro a ha
    rw [hTiff, shell, Set.mem_setOf_eq, qv_line v Q' hc hQeq a hq y, ← ha₀, ← norm_le_iff_v,
      norm_mul] at ha
    calc ‖a - a₀‖ = ‖2 * c * q‖ * ‖a - a₀‖ / ‖2 * c * q‖ := by field_simp
      _ ≤ ‖HN.ϖ v‖ ^ K / ‖2 * c * q‖ := by gcongr
      _ < δ := by rw [div_lt_iff₀ hn2cq]; exact hK
  have hpt : ∀ a, v3 a (a - q) y = graphV v Q' c q y + v3 (a - a₀) (a - a₀) 0 := by
    intro a
    rw [graphV, v3_add]
    refine v3_congr (by rw [ha₀]; ring) (by rw [ha₀]; ring) (by simp)
  have hind : ∀ a, (U ∩ Qv v Q ⁻¹' shell v c K).indicator (1 : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞) (v3 a (a - q) y) =
      U.indicator 1 (graphV v Q' c q y) * T.indicator 1 a := by
    intro a
    by_cases ha : a ∈ T
    · have hm : v3 a (a - q) y ∈ U ↔ graphV v Q' c q y ∈ U := by
        rw [hpt]
        refine hδ _ _ (lt_of_le_of_lt (norm_v3_le v _ _ _ le_rfl le_rfl ?_) (hsmall a ha))
        rw [norm_zero]; exact norm_nonneg _
      by_cases hg : graphV v Q' c q y ∈ U
      · have hmem : v3 a (a - q) y ∈ U ∩ Qv v Q ⁻¹' shell v c K := ⟨hm.mpr hg, (hTiff a).mp ha⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hg, Set.indicator_of_mem ha]; simp
      · rw [Set.indicator_of_notMem (fun h => hg (hm.mp h.1)), Set.indicator_of_notMem hg, zero_mul]
    · rw [Set.indicator_of_notMem (fun h => ha ((hTiff a).mpr h.2)), Set.indicator_of_notMem ha, mul_zero]
  simp_rw [hind]
  have hTm : MeasurableSet T := by
    have : T = (fun a => a - a₀) ⁻¹' ((fun z => (2 * c * q)⁻¹ * z) '' (latticeV v (K : ℤ) : Set Fv)) := rfl
    rw [this]
    refine MeasurableSet.preimage ?_ (measurable_id.sub_const _)
    rw [show (fun z => (2 * c * q)⁻¹ * z) '' (latticeV v (K : ℤ) : Set Fv) =
        (fun z => (2 * c * q) * z) ⁻¹' (latticeV v (K : ℤ) : Set Fv) by
      ext z; simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨w, hw, rfl⟩; rwa [← mul_assoc, mul_inv_cancel₀ h2cq, one_mul]
      · intro h; exact ⟨_, h, by rw [← mul_assoc, inv_mul_cancel₀ h2cq, one_mul]⟩]
    exact (measurableSet_latticeV v K).preimage (measurable_const_mul _)
  rw [lintegral_const_mul _ (measurable_one.indicator hTm), lintegral_indicator_one hTm, hT,
    haarV_affine v a₀ (inv_ne_zero h2cq) K, norm_inv]

/-- **Fubini in the coordinates $(x_0, x_1, x')$**, then the substitution $x_1 = x_0 - q$:
$\int G\,d\mathrm{vol} = \int_{x'}\int_q\int_{a} G(a, a - q, x')$. -/
theorem lintegral_volV_line {G : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂volV (haarV v) (k + 1 + 1) =
      ∫⁻ y, ∫⁻ q, ∫⁻ a, G (v3 a (a - q) y) ∂haarV v ∂haarV v ∂volV (haarV v) k := by
  set ν := haarV v
  have hH : Measurable fun p : Fv × Fv × (Fin k → Fv) => G (v3 p.1 p.2.1 p.2.2) := hG.comp (measurable_v3 v)
  have e1 : ∫⁻ x, G x ∂volV ν (k + 1 + 1) = ∫⁻ a, ∫⁻ b, ∫⁻ y, G (v3 a b y) ∂volV ν k ∂ν ∂ν := by
    rw [lintegral_volV_cons v ν hG]
    refine lintegral_congr fun a => ?_
    exact lintegral_volV_cons v ν (G := fun z => G (Fin.cons a z))
      (hG.comp (continuous_const.finCons continuous_id).measurable)
  have e2 : ∀ a, ∫⁻ b, ∫⁻ y, G (v3 a b y) ∂volV ν k ∂ν = ∫⁻ y, ∫⁻ b, G (v3 a b y) ∂ν ∂volV ν k := by
    intro a
    refine lintegral_lintegral_swap ?_
    exact (hH.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable
  have hG3 : Measurable fun p : Fv × (Fin k → Fv) => ∫⁻ b, G (v3 p.1 b p.2) ∂ν :=
    (hH.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).lintegral_prod_right'
  rw [e1]
  simp_rw [e2]
  rw [lintegral_lintegral_swap hG3.aemeasurable]
  refine lintegral_congr fun y => ?_
  have e3 : ∀ a, ∫⁻ b, G (v3 a b y) ∂ν = ∫⁻ q, G (v3 a (a - q) y) ∂ν := fun a =>
    (lintegral_sub_left_eq_self (fun b => G (v3 a b y)) a).symm
  simp_rw [e3]
  refine lintegral_lintegral_swap ?_
  exact (hH.comp (measurable_fst.prodMk ((measurable_fst.sub measurable_snd).prodMk measurable_const))).aemeasurable

/-- **The shell volume in the chart** ($U$ measurable, $U \subseteq \{|x_0 - x_1| \ge r\}$, $U$ invariant under translations of
norm $< \delta$, $K$ large): $\mathrm{vol}(U \cap Q^{-1}(c + \mathfrak p^K)) =
\nu(\mathfrak p^K)\int_{x'}\int_q \mathbf 1_U(\mathrm{graph}(q, x'))\,|2cq|^{-1}$. -/
theorem volV_shell_eq (hc : c ≠ 0) (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x))
    {U : Set (Fin (k + 1 + 1) → Fv)} (hUm : MeasurableSet U) {δ : ℝ} (hδ : ∀ x z, ‖z‖ < δ → (x + z ∈ U ↔ x ∈ U))
    {r : ℝ} (hr : 0 < r) (hUr : ∀ x ∈ U, r ≤ ‖x 0 - x 1‖) {K : ℕ} (hK : ‖HN.ϖ v‖ ^ K < δ * ‖2 * c‖ * r) :
    volV (haarV v) (k + 1 + 1) (U ∩ Qv v Q ⁻¹' shell v c K) =
      (∫⁻ y, ∫⁻ q, U.indicator 1 (graphV v Q' c q y) * ENNReal.ofReal ‖2 * c * q‖⁻¹ ∂haarV v
        ∂volV (haarV v) k) * haarV v (latticeV v (K : ℤ) : Set Fv) := by
  set S := U ∩ Qv v Q ⁻¹' shell v c K with hS
  have hSm : MeasurableSet S := hUm.inter ((measurableSet_shell v c K).preimage (measurable_qv v Q))
  rw [← lintegral_indicator_one hSm, lintegral_volV_line v (measurable_one.indicator hSm)]
  have hL : haarV v (latticeV v (K : ℤ) : Set Fv) ≠ ⊤ := measure_latticeV_ne_top v (haarV v) K
  have inner : ∀ y q, ∫⁻ a, S.indicator 1 (v3 a (a - q) y) ∂haarV v =
      U.indicator 1 (graphV v Q' c q y) * ENNReal.ofReal ‖2 * c * q‖⁻¹ *
        haarV v (latticeV v (K : ℤ) : Set Fv) := by
    intro y q
    by_cases hq : r ≤ ‖q‖
    · have hq0 : q ≠ 0 := norm_pos_iff.mp (hr.trans_le hq)
      have hK' : ‖HN.ϖ v‖ ^ K < δ * ‖2 * c * q‖ := by
        rw [norm_mul (2 * c) q]
        have hδ0 : 0 < δ := by
          by_contra h
          push_neg at h
          have : δ * ‖2 * c‖ * r ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)) hr.le
          exact absurd (hK.trans_le this) (not_lt.mpr (pow_nonneg (norm_nonneg _) K))
        calc ‖HN.ϖ v‖ ^ K < δ * ‖2 * c‖ * r := hK
          _ ≤ δ * (‖2 * c‖ * ‖q‖) := by rw [mul_assoc]; gcongr
      rw [lintegral_line_shell v Q' hc hQeq hδ hq0 y hK']; ring
    · push_neg at hq
      have h1 : ∀ a, S.indicator (1 : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞) (v3 a (a - q) y) = 0 := by
        intro a
        refine Set.indicator_of_notMem (fun h => ?_) _
        have := hUr _ h.1
        simp only [v3_zero', v3_one', sub_sub_cancel] at this
        linarith
      have h2 : U.indicator (1 : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞) (graphV v Q' c q y) = 0 := by
        refine Set.indicator_of_notMem (fun h => ?_) _
        have := hUr _ h
        rw [graphV_sub] at this
        linarith
      simp only [h1, lintegral_zero, h2, zero_mul]
  simp_rw [inner]
  rw [← lintegral_mul_const' _ _ hL]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_mul_const' _ _ hL]

/-- **The hyperbolic-split chart of the sphere away from $\{x_0 = x_1\}$**: for $U$ compact open, $0 \notin U$,
$U \subseteq \{|x_0 - x_1| \ge r\}$ ($r > 0$),
$$\sigma_c(U) = \int_{F_v^k}\int_{F_v}\mathbf 1_U(\mathrm{graph}(q, y))\,\frac{dq}{|2cq|_v}\,dy.$$ -/
theorem lerayMeasure_sphere_far (hQ : Q.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x)) {U : Set (Fin (k + 1 + 1) → Fv)}
    (hU : U ∈ Cz v (k + 1 + 1)) {r : ℝ} (hr : 0 < r) (hUr : ∀ x ∈ U, r ≤ ‖x 0 - x 1‖) :
    lerayMeasure v (haarV v) Q hQ c U =
      ∫⁻ y, ∫⁻ q, U.indicator 1 (graphV v Q' c q y) * ENNReal.ofReal ‖2 * c * q‖⁻¹ ∂haarV v ∂volV (haarV v) k := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_add_mem v hU.1 hU.2.1
  have hpos : 0 < δ * ‖2 * c‖ * r := by
    have : (0 : ℝ) < ‖2 * c‖ := norm_pos_iff.mpr (mul_ne_zero two_ne_zero hc)
    positivity
  have hev : ∀ᶠ K : ℕ in atTop, ‖HN.ϖ v‖ ^ K < δ * ‖2 * c‖ * r :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_ϖ_lt_one v)).eventually (gt_mem_nhds hpos)
  obtain ⟨K, hK1, hK2⟩ := ((lerayMeasure_eventually v (haarV v) Q hQ c hU).and hev).exists
  rw [← hK1, lerayThick_apply _ _ _ hU.2.1.measurableSet, measure_shell,
    volV_shell_eq v Q' hc hQeq hU.2.1.measurableSet hδ hr hUr hK2, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel (measure_latticeV_pos v (haarV v) K).ne' (measure_latticeV_ne_top v (haarV v) K),
    mul_one]

/-- The norm of the value of a form over $\mathcal O_v$ on $\mathfrak p^sL$ is at most $q^{-2s}$. -/
theorem norm_qv_le_of_mem {n : ℕ} (Q₁ : QuadForm 𝔬 n) {s : ℕ} {x : Fin n → Fv} (hx : x ∈ cosetP v 0 s) :
    ‖Qv v Q₁ x‖ ≤ ‖HN.ϖ v‖ ^ (2 * s) := by
  rw [norm_le_iff_v]
  have := valued_qv_le v Q₁ s hx
  simpa using this

/-- **The hyperplane section $\{x_0 = x_1\}$ of the sphere is $\sigma_c$-null** (slab bound). -/
theorem lerayMeasure_sphere_null (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x)) {U : Set (Fin (k + 1 + 1) → Fv)}
    (hU : U ∈ Cz v (k + 1 + 1)) :
    lerayMeasure v (haarV v) Q hQ c (U ∩ {x | x 0 = x 1}) = 0 := by
  set ν := haarV v
  obtain ⟨R₀, hR₀⟩ := hU.1.isBounded.exists_norm_le
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hUR : ∀ x ∈ U, ‖x‖ ≤ R := fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one hcpos (norm_ϖ_lt_one v)
  have hs2 : ‖HN.ϖ v‖ ^ (2 * s) < ‖c‖ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le (by omega)) hs
  have hB : Metric.closedBall (0 : Fin k → Fv) R \ cosetP v 0 s ∈ Cz v k := closedBall_diff_mem_Cz v hRpos s
  have hA : Measurable fun t : Fv => -c * t ^ 2 := measurable_const.mul (measurable_id.pow_const 2)
  obtain ⟨M, hM, hslab⟩ := vol_slab_le v ν Q' hQ' hB hA
  obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hRpos) (norm_ϖ_lt_one v)
  set C := M * ν (Metric.closedBall (0 : Fv) R)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top hM (isCompact_closedBall _ _).measure_lt_top.ne
  -- the bound on the thin slabs
  have hbound : ∀ j ≥ j₀, lerayMeasure v ν Q hQ c (U ∩ {x | x 0 = x 1}) ≤ C * ν (latticeV v (j : ℤ) : Set Fv) := by
    intro j hj
    have hjR : ‖HN.ϖ v‖ ^ j * R < 1 := by
      have h1 : ‖HN.ϖ v‖ ^ j ≤ ‖HN.ϖ v‖ ^ j₀ := pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le hj
      calc ‖HN.ϖ v‖ ^ j * R ≤ ‖HN.ϖ v‖ ^ j₀ * R := by gcongr
        _ < R⁻¹ * R := by gcongr
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    set Uj := U ∩ {x : Fin (k + 1 + 1) → Fv | ‖x 0 - x 1‖ ≤ ‖HN.ϖ v‖ ^ j} with hUj
    have hcl : IsClopen {x : Fin (k + 1 + 1) → Fv | ‖x 0 - x 1‖ ≤ ‖HN.ϖ v‖ ^ j} :=
      isClopen_norm_le v ((continuous_apply 0).sub (continuous_apply 1)) (pow_pos (norm_ϖ_pos v) j)
    have hUjCz : Uj ∈ Cz v (k + 1 + 1) :=
      ⟨hU.1.inter_right hcl.1, hU.2.1.inter hcl.2, fun h => hU.2.2 h.1⟩
    have hsub : U ∩ {x | x 0 = x 1} ⊆ Uj := by
      rintro x ⟨hx, hx01⟩
      refine ⟨hx, ?_⟩
      show ‖x 0 - x 1‖ ≤ _
      rw [show x 0 = x 1 from hx01, sub_self, norm_zero]; positivity
    refine (measure_mono hsub).trans ?_
    have hev : ∀ᶠ K : ℕ in atTop, ‖HN.ϖ v‖ ^ K < ‖c‖ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_ϖ_lt_one v)).eventually (gt_mem_nhds hcpos)
    obtain ⟨K, hK1, hK2⟩ := ((lerayMeasure_eventually v ν Q hQ c hUjCz).and hev).exists
    rw [← hK1, lerayThick_apply _ _ _ hUjCz.2.1.measurableSet, measure_shell]
    set L := ν (latticeV v (K : ℤ) : Set Fv)
    have hL0 : L ≠ 0 := (measure_latticeV_pos v ν K).ne'
    have hLt : L ≠ ⊤ := measure_latticeV_ne_top v ν K
    -- the slices
    have hslice : ∀ a, volV ν (k + 1) {z | (Fin.cons a z : Fin (k + 1 + 1) → Fv) ∈ Uj ∩ Qv v Q ⁻¹' shell v c K} ≤
        (Metric.closedBall (0 : Fv) R).indicator (fun _ => M * ν (latticeV v (j : ℤ) : Set Fv) * L) a := by
      intro a
      by_cases ha : a ∈ Metric.closedBall (0 : Fv) R
      · rw [Set.indicator_of_mem ha]
        have hW : MeasurableSet (shell v a j) := measurableSet_shell v a j
        have h := hslab (shell v a j) hW (c - c * a ^ 2) K
        rw [measure_shell] at h
        refine (measure_mono ?_).trans h
        intro z hz
        obtain ⟨⟨hzU, hzj⟩, hzQ⟩ := hz
        have hx : (Fin.cons a z : Fin (k + 1 + 1) → Fv) = v3 a (z 0) (Fin.tail z) := by
          simp only [v3]; congr 1; exact (Fin.cons_self_tail z).symm
        rw [hx] at hzU hzj hzQ
        simp only [Set.mem_setOf_eq, v3_zero', v3_one'] at hzj
        simp only [Set.mem_preimage, hQeq, v3_zero', v3_one', tl_v3] at hzQ
        have hnx := hUR _ hzU
        have hza : ‖z 0‖ ≤ R := (norm_le_pi_norm (v3 a (z 0) (Fin.tail z)) 1).trans hnx
        have hta : ‖Fin.tail z‖ ≤ R := by
          have := (pi_norm_le_iff_of_nonneg hRpos.le).1 hnx
          refine (pi_norm_le_iff_of_nonneg hRpos.le).2 fun i => ?_
          have h2 := this i.succ.succ
          simpa [v3, Fin.tail] using h2
        refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
        · rw [mem_shell_iff_norm, norm_sub_rev]; exact hzj
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hta
        · intro hP
          have hQ'small := norm_qv_le_of_mem v Q' hP
          have hsum : ‖c * a ^ 2 - c * z 0 ^ 2‖ < ‖c‖ := by
            have e : c * a ^ 2 - c * z 0 ^ 2 = c * ((a - z 0) * (a + z 0)) := by ring
            rw [e, norm_mul, norm_mul]
            have hp : ‖a + z 0‖ ≤ R :=
              (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simpa using ha) hza)
            calc ‖c‖ * (‖a - z 0‖ * ‖a + z 0‖) ≤ ‖c‖ * (‖HN.ϖ v‖ ^ j * R) := by gcongr
              _ < ‖c‖ * 1 := by gcongr
              _ = ‖c‖ := mul_one _
          have hQx : ‖c * a ^ 2 - c * z 0 ^ 2 + Qv v Q' (Fin.tail z)‖ < ‖c‖ :=
            lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hsum (hQ'small.trans_lt hs2))
          have heq : ‖c * a ^ 2 - c * z 0 ^ 2 + Qv v Q' (Fin.tail z) - c‖ = ‖c‖ := by
            rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hQx.ne),
              norm_neg, max_eq_right hQx.le]
          have := (mem_shell_iff_norm v).mp hzQ
          rw [heq] at this
          exact absurd (this.trans_lt hK2) (lt_irrefl _)
        · have h := (mem_shell_sub v (t := c * a ^ 2)).mpr hzQ
          convert h using 2; ring
      · rw [Set.indicator_of_notMem ha]
        refine le_of_eq (measure_eq_zero_iff_ae_notMem.mpr (Eventually.of_forall fun z hz => ha ?_))
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_le_pi_norm (Fin.cons a z : Fin (k + 1 + 1) → Fv) 0).trans (hUR _ hz.1.1)
    have hSm : MeasurableSet (Uj ∩ Qv v Q ⁻¹' shell v c K) :=
      hUjCz.2.1.measurableSet.inter ((measurableSet_shell v c K).preimage (measurable_qv v Q))
    rw [volV_cons v ν hSm]
    calc L⁻¹ * ∫⁻ a, volV ν (k + 1) {z | (Fin.cons a z : Fin (k + 1 + 1) → Fv) ∈ Uj ∩ Qv v Q ⁻¹' shell v c K} ∂ν
        ≤ L⁻¹ * ∫⁻ a, (Metric.closedBall (0 : Fv) R).indicator
            (fun _ => M * ν (latticeV v (j : ℤ) : Set Fv) * L) a ∂ν := by gcongr with a; exact hslice a
      _ = C * ν (latticeV v (j : ℤ) : Set Fv) := by
        rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
        rw [show L⁻¹ * (M * ν (latticeV v (j : ℤ) : Set Fv) * L * ν (Metric.closedBall 0 R)) =
          (L⁻¹ * L) * (M * ν (Metric.closedBall 0 R)) * ν (latticeV v (j : ℤ) : Set Fv) by ring,
          ENNReal.inv_mul_cancel hL0 hLt, one_mul]
  have hlim : Tendsto (fun j : ℕ => C * ν (latticeV v (j : ℤ) : Set Fv)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (tendsto_measure_latticeV v ν) (Or.inr hC)
    rwa [mul_zero] at this
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨j₀, hbound⟩)) bot_le

/-- The density $|2cq|_v^{-1}$ of the chart. -/
def rhoS (c q : Fv) : ℝ≥0∞ := ENNReal.ofReal ‖2 * c * q‖⁻¹

theorem measurable_rhoS (c : Fv) : Measurable (rhoS v c) :=
  ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_id).norm.inv)

/-- **The chart measure** on $F_v^{k+2}$: the image of $|2cq|_v^{-1}dq\otimes dy$ under $(q, y) \mapsto \mathrm{graph}(q, y)$. -/
def sphChart (c : Fv) : Measure (Fin (k + 1 + 1) → Fv) :=
  (((haarV v).withDensity (rhoS v c)).prod (volV (haarV v) k)).map fun p => graphV v Q' c p.1 p.2

theorem lintegral_sphChart (c : Fv) {G : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂sphChart v Q' c = ∫⁻ q, ∫⁻ y, rhoS v c q * G (graphV v Q' c q y) ∂volV (haarV v) k ∂haarV v := by
  have hm : Measurable fun p : Fv × (Fin k → Fv) => G (graphV v Q' c p.1 p.2) := hG.comp (measurable_graphV v Q' c)
  rw [sphChart, lintegral_map hG (measurable_graphV v Q' c),
    lintegral_prod (fun p : Fv × (Fin k → Fv) => G (graphV v Q' c p.1 p.2)) hm.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_rhoS v c) hm.lintegral_prod_right']
  refine lintegral_congr fun q => ?_
  rw [Pi.mul_apply]
  exact (lintegral_const_mul _ (hm.comp (measurable_const.prodMk measurable_id))).symm

theorem sphChart_apply (c : Fv) {A : Set (Fin (k + 1 + 1) → Fv)} (hA : MeasurableSet A) :
    sphChart v Q' c A = ∫⁻ y, ∫⁻ q, A.indicator 1 (graphV v Q' c q y) * rhoS v c q ∂haarV v ∂volV (haarV v) k := by
  rw [← lintegral_indicator_one hA, lintegral_sphChart v Q' c (measurable_one.indicator hA)]
  have hm : Measurable fun p : Fv × (Fin k → Fv) => rhoS v c p.1 * A.indicator 1 (graphV v Q' c p.1 p.2) :=
    ((measurable_rhoS v c).comp measurable_fst).mul ((measurable_one.indicator hA).comp (measurable_graphV v Q' c))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [mul_comm (rhoS v c _)]

/-- The chart measure does not see $\{x_0 = x_1\}$ (the graph point has $x_0 - x_1 = q$, and $\{q = 0\}$ is null). -/
theorem sphChart_null (c : Fv) : sphChart v Q' c {x | x 0 = x 1} = 0 := by
  have hZ : MeasurableSet {x : Fin (k + 1 + 1) → Fv | x 0 = x 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  rw [sphChart, Measure.map_apply (measurable_graphV v Q' c) hZ]
  refine measure_mono_null (t := ({0} : Set Fv) ×ˢ Set.univ) ?_ ?_
  · rintro ⟨q, y⟩ h
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at h
    have := graphV_sub v Q' c q y
    rw [h, sub_self] at this
    exact ⟨this.symm, Set.mem_univ _⟩
  · rw [Measure.prod_prod, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_singleton, measure_singleton, zero_smul, lintegral_zero_measure, zero_mul]

/-- **The hyperbolic-split chart of the sphere at a finite place** (every $v$, dyadic included; $c \ne 0$, $Q'$
nondegenerate, $Q(x) = cx_0^2 - cx_1^2 + Q'(x')$): the Leray measure $\sigma_c$ is the chart measure,
$$\sigma_c = \mathrm{graph}_*\Big(\frac{dq}{|2cq|_v}\otimes dy\Big),\qquad \mathrm{graph}(q, y) = (b + q, b, y),\
  b = \frac{c - cq^2 - Q'(y)}{2cq},$$
and $\{x_0 = x_1\}$ is $\sigma_c$-null. Equivalently $\sigma_c = dx/dQ$ with $dx_0\,dx_1 = |2|_v^{-1}dp\,dq$ and
$\partial Q/\partial p = cq$. -/
@[kb "weil1982" "§2.2 (the Leray form dx/dQ in a chart); §2.4 [unverified]"]
theorem lerayMeasure_sphere_eq_sphChart (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x)) :
    lerayMeasure v (haarV v) Q hQ c = sphChart v Q' c := by
  have hZ : MeasurableSet {x : Fin (k + 1 + 1) → Fv | x 0 = x 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  refine measure_ext_Cz v (lerayMeasure_singleton_zero v _ Q hQ c) ?_
    (fun U hU => (lerayMeasure_lt_top v _ Q hQ c hU).ne) fun U hU => ?_
  · refine measure_mono_null (fun x hx => ?_) (sphChart_null v Q' c)
    simp only [Set.mem_singleton_iff] at hx
    simp [hx]
  -- the far pieces `U^j`
  set W : ℕ → Set (Fin (k + 1 + 1) → Fv) := fun j => U \ {x | ‖x 0 - x 1‖ < ‖HN.ϖ v‖ ^ j} with hW
  have hcont : Continuous fun x : Fin (k + 1 + 1) → Fv => x 0 - x 1 := (continuous_apply 0).sub (continuous_apply 1)
  have hlt : ∀ j : ℕ, IsClopen {x : Fin (k + 1 + 1) → Fv | ‖x 0 - x 1‖ < ‖HN.ϖ v‖ ^ j} := by
    intro j
    have h : {x : Fin (k + 1 + 1) → Fv | ‖x 0 - x 1‖ < ‖HN.ϖ v‖ ^ j} =
        (fun x => x 0 - x 1) ⁻¹' Metric.ball 0 (‖HN.ϖ v‖ ^ j) := by ext x; simp
    rw [h]
    exact ⟨(IsUltrametricDist.isClosed_ball _ _).preimage hcont, Metric.isOpen_ball.preimage hcont⟩
  have hWCz : ∀ j, W j ∈ Cz v (k + 1 + 1) := fun j =>
    ⟨hU.1.diff (hlt j).2, hU.2.1.sdiff (hlt j).1, fun h => hU.2.2 h.1⟩
  have hWr : ∀ j, ∀ x ∈ W j, ‖HN.ϖ v‖ ^ j ≤ ‖x 0 - x 1‖ := fun j x hx => not_lt.mp hx.2
  have hmono : Monotone W := by
    intro i j hij x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    exact lt_of_lt_of_le h (pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le hij)
  have hUnion : (⋃ j, W j) = U \ {x | x 0 = x 1} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_setOf_eq, hW, not_lt]
    constructor
    · rintro ⟨j, hxU, hj⟩
      refine ⟨hxU, fun h => ?_⟩
      rw [h, sub_self, norm_zero] at hj
      exact absurd hj (not_le.mpr (pow_pos (norm_ϖ_pos v) j))
    · rintro ⟨hxU, hx⟩
      have hpos : 0 < ‖x 0 - x 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hpos (norm_ϖ_lt_one v)
      exact ⟨j, hxU, hj.le⟩
  have h1 : lerayMeasure v (haarV v) Q hQ c U = ⨆ j, lerayMeasure v (haarV v) Q hQ c (W j) := by
    rw [← hmono.measure_iUnion, hUnion, ← measure_diff_null (s := U) (lerayMeasure_sphere_null v Q' hQ hQ' hc hQeq hU)]
    congr 1
    ext x; simp [and_comm]
  have h2 : sphChart v Q' c U = ⨆ j, sphChart v Q' c (W j) := by
    rw [← hmono.measure_iUnion, hUnion, measure_diff_null (sphChart_null v Q' c)]
  rw [h1, h2]
  refine iSup_congr fun j => ?_
  rw [lerayMeasure_sphere_far v Q' hQ hc hQeq (hWCz j) (pow_pos (norm_ϖ_pos v) j) (hWr j),
    sphChart_apply v Q' c (hWCz j).2.1.measurableSet]
  rfl

/-- **The sphere chart, integral form**: $\int F\,d\sigma_c = \int_{F_v}\int_{F_v^k}|2cq|_v^{-1}F(\mathrm{graph}(q, y))\,dy\,dq$. -/
theorem lintegral_lerayMeasure_sphere (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 - c * x 1 ^ 2 + Qv v Q' (tl x)) {G : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ x, G x ∂lerayMeasure v (haarV v) Q hQ c =
      ∫⁻ q, ∫⁻ y, rhoS v c q * G (graphV v Q' c q y) ∂volV (haarV v) k ∂haarV v := by
  rw [lerayMeasure_sphere_eq_sphChart v Q' hQ hQ' hc hQeq, lintegral_sphChart v Q' c hG]

end Sphere

/-! ### Support, and the stabilized value on one compact open set -/

section Support

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure] {n : ℕ}
  (Q : QuadForm (v.adicCompletionIntegers F) n) (hQ : Q.Nondegenerate)

/-- Shells are a neighbourhood basis: a closed set missing $\rho$ misses all deep shells. -/
theorem exists_shell_disjoint {C : Set Fv} (hC : IsClosed C) {rho : Fv} (hrho : rho ∉ C) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ y ∈ C, y ∉ shell v rho k := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl rho hrho
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  refine ⟨K, fun k hk y hyC hys => ?_⟩
  have h1 : ‖y - rho‖ ≤ ‖HN.ϖ v‖ ^ k := (norm_le_iff_v v).2 hys
  have h2 : ‖HN.ϖ v‖ ^ k ≤ ‖HN.ϖ v‖ ^ K := pow_le_pow_of_le_one (norm_ϖ_pos v).le (norm_ϖ_lt_one v).le hk
  exact hball (Metric.mem_ball.2 (by rw [dist_eq_norm]; exact lt_of_le_of_lt (h1.trans h2) hK)) hyC

include hQ in
/-- **$\sigma_\rho$ is carried by the level set $\{Q = \rho\}$** (any form over $\mathcal O_v$). -/
theorem lerayMeasure_compl_level (ρ : Fv) : lerayMeasure v ν Q hQ ρ {x | Qv v Q x ≠ ρ} = 0 := by
  have hcl : IsClosed {x : Fin n → Fv | Qv v Q x = ρ} := isClosed_eq (continuous_qv v Q) continuous_const
  have hO : IsOpen ({x : Fin n → Fv | Qv v Q x ≠ ρ} \ {0}) := by
    have : {x : Fin n → Fv | Qv v Q x ≠ ρ} = {x | Qv v Q x = ρ}ᶜ := rfl
    rw [this]; exact hcl.isOpen_compl.sdiff isClosed_singleton
  obtain ⟨T, s, hTc, hTO, hmem, hUeq⟩ := exists_countable_union_Cz v hO (by simp)
  have hU0 : ∀ x ∈ T, lerayMeasure v ν Q hQ ρ (cosetP v x (s x)) = 0 := by
    intro x hx
    have hUC := hmem x hx
    have hsub : cosetP v x (s x) ⊆ {x | Qv v Q x ≠ ρ} := by
      intro y hy
      have : cosetP v x (s x) ⊆ {x : Fin n → Fv | Qv v Q x ≠ ρ} \ {0} := by
        rw [hUeq]; exact Set.subset_iUnion₂ (s := fun x _ => cosetP v x (s x)) x hx
      exact (this hy).1
    have hcomp : IsCompact (Qv v Q '' cosetP v x (s x)) := hUC.1.image (continuous_qv v Q)
    have hrho : ρ ∉ Qv v Q '' cosetP v x (s x) := by
      rintro ⟨y, hy, hyrho⟩
      exact hsub hy hyrho
    obtain ⟨K, hK⟩ := exists_shell_disjoint v hcomp.isClosed hrho
    obtain ⟨k, hk1, hk2⟩ := ((lerayMeasure_eventually v ν Q hQ ρ hUC).and (Filter.eventually_ge_atTop K)).exists
    rw [← hk1, lerayThick_apply _ _ _ hUC.2.1.measurableSet]
    have : cosetP v x (s x) ∩ Qv v Q ⁻¹' shell v ρ k = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hys
      exact hK k hk2 _ ⟨y, hy, rfl⟩ hys
    rw [this]; simp
  have hcover : {x : Fin n → Fv | Qv v Q x ≠ ρ} ⊆ {0} ∪ ⋃ x ∈ T, cosetP v x (s x) := by
    intro y hy
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · right
      have : y ∈ {x : Fin n → Fv | Qv v Q x ≠ ρ} \ {0} := ⟨hy, hy0⟩
      rw [hUeq] at this
      exact this
  refine measure_mono_null hcover ?_
  refine measure_union_null (lerayMeasure_singleton_zero v _ _ _ ρ) ?_
  exact (measure_biUnion_null_iff hTc).2 hU0

include hQ in
/-- **Uniform stabilization on one compact open set**: there is $K_0$ with $\lambda_{\rho,K}(B) = \sigma_\rho(B)$ for all
$K \ge K_0$ and **all** $\rho$. -/
theorem exists_lerayThick_eq_lerayMeasure {B : Set (Fin n → Fv)} (hB : B ∈ Cz v n) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ ρ : Fv, lerayThick ν (Qv v Q) (shell v ρ K) B = lerayMeasure v ν Q hQ ρ B := by
  obtain ⟨K₀, hK₀⟩ := lerayThick_eventually_succ v ν Q hQ hB.1 hB.2.1 hB.2.2
  have hconst : ∀ ρ, ∀ K ≥ K₀, lerayThick ν (Qv v Q) (shell v ρ K) B = lerayThick ν (Qv v Q) (shell v ρ K₀) B := by
    intro ρ K hK
    induction K, hK using Nat.le_induction with
    | base => rfl
    | succ K hK ih => rw [← hK₀ ρ K hK, ih]
  refine ⟨K₀, fun K hK ρ => ?_⟩
  obtain ⟨K', hK'1, hK'2⟩ := ((lerayMeasure_eventually v ν Q hQ ρ hB).and (Filter.eventually_ge_atTop K₀)).exists
  rw [hconst ρ K hK, ← hK'1, hconst ρ K' hK'2]

end Support

/-! ### The cone: slicing $Q = cx_0^2 + Q_m(x')$ -/

section Cone

variable {k : ℕ} {Q : QuadForm (v.adicCompletionIntegers F) (k + 1 + 1)}
  {Qm : QuadForm (v.adicCompletionIntegers F) (k + 1)} {c : v.adicCompletion F}

/-- The product box $\{x : x_0 \in A,\ x' \in B\}$. -/
def boxP (A : Set Fv) (B : Set (Fin (k + 1) → Fv)) : Set (Fin (k + 1 + 1) → Fv) :=
  {x | x 0 ∈ A ∧ Fin.tail x ∈ B}

theorem boxP_mem_Cz {A : Set Fv} (hAc : IsCompact A) (hAo : IsOpen A) {B : Set (Fin (k + 1) → Fv)}
    (hB : B ∈ Cz v (k + 1)) : boxP v A B ∈ Cz v (k + 1 + 1) := by
  have he : boxP v A B = (fun x : Fin (k + 1 + 1) → Fv => (x 0, Fin.tail x)) ⁻¹' (A ×ˢ B) := rfl
  have hhome : Continuous fun x : Fin (k + 1 + 1) → Fv => (x 0, Fin.tail x) :=
    (continuous_apply 0).prodMk (continuous_tail v)
  refine ⟨?_, by rw [he]; exact (hAo.prod hB.2.1).preimage hhome, fun h => hB.2.2 ((show Fin.tail (0 : Fin (k + 1 + 1) → Fv) = 0 from rfl) ▸ h.2)⟩
  have hc : boxP v A B = (fun p : Fv × (Fin (k + 1) → Fv) => (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → Fv)) '' (A ×ˢ B) := by
    ext x
    simp only [boxP, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro hx; exact ⟨x 0, Fin.tail x, hx, Fin.cons_self_tail x⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; simpa using And.intro ha hb
  rw [hc]
  exact (hAc.prod hB.1).image (continuous_pi fun i => Fin.cases continuous_fst (fun j => (continuous_apply j).comp continuous_snd) i)

/-- **The slicing formula on a box away from $x' = 0$** ($Q = cx_0^2 + Q_m(x')$, $Q_m$ nondegenerate, $A$ compact open,
$B$ compact open with $0 \notin B$): $\sigma_0(\{x_0 \in A, x' \in B\}) = \int_A \sigma'_{-cx_0^2}(B)\,dx_0$, where $\sigma'$ is
the Leray measure of $Q_m$. -/
theorem lerayMeasure_cone_box (hQ : Q.Nondegenerate) (hQm : Qm.Nondegenerate)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 + Qv v Qm (Fin.tail x)) {A : Set Fv} (hAc : IsCompact A) (hAo : IsOpen A)
    {B : Set (Fin (k + 1) → Fv)} (hB : B ∈ Cz v (k + 1)) :
    lerayMeasure v (haarV v) Q hQ 0 (boxP v A B) =
      ∫⁻ a in A, lerayMeasure v (haarV v) Qm hQm (a ^ 2 * -c) B ∂haarV v := by
  set ν := haarV v
  obtain ⟨K₀, hK₀⟩ := exists_lerayThick_eq_lerayMeasure v ν Qm hQm hB
  have hP := boxP_mem_Cz v hAc hAo hB
  obtain ⟨K, hK1, hK2⟩ := ((lerayMeasure_eventually v ν Q hQ 0 hP).and (Filter.eventually_ge_atTop K₀)).exists
  rw [← hK1, lerayThick_apply _ _ _ hP.2.1.measurableSet, measure_shell]
  have hSm : MeasurableSet (boxP v A B ∩ Qv v Q ⁻¹' shell v 0 K) :=
    hP.2.1.measurableSet.inter ((measurableSet_shell v 0 K).preimage (measurable_qv v Q))
  rw [volV_cons v ν hSm]
  set L := ν (latticeV v (K : ℤ) : Set Fv)
  have hL0 : L ≠ 0 := (measure_latticeV_pos v ν K).ne'
  have hLt : L ≠ ⊤ := measure_latticeV_ne_top v ν K
  have hslice : ∀ a, volV ν (k + 1) {z | (Fin.cons a z : Fin (k + 1 + 1) → Fv) ∈ boxP v A B ∩ Qv v Q ⁻¹' shell v 0 K} =
      A.indicator (fun a => L * lerayMeasure v ν Qm hQm (a ^ 2 * -c) B) a := by
    intro a
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha]
      have h := hK₀ K hK2 (a ^ 2 * -c)
      rw [lerayThick_apply _ _ _ hB.2.1.measurableSet, measure_shell] at h
      rw [← h, ← mul_assoc, ENNReal.mul_inv_cancel hL0 hLt, one_mul]
      congr 1
      ext z
      simp only [boxP, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Fin.cons_zero, Fin.tail_cons, hQeq]
      rw [← mem_shell_sub v (t := c * a ^ 2)]
      simp only [ha, true_and]
      constructor
      · rintro ⟨hz, hs⟩; refine ⟨hz, ?_⟩; convert hs using 2 <;> ring
      · rintro ⟨hz, hs⟩; refine ⟨hz, ?_⟩; convert hs using 2 <;> ring
    · rw [Set.indicator_of_notMem ha]
      refine measure_eq_zero_iff_ae_notMem.mpr (Eventually.of_forall fun z hz => ha ?_)
      simpa [boxP] using hz.1.1
  simp_rw [hslice]
  rw [lintegral_indicator (hAo.measurableSet), lintegral_const_mul' _ _ hLt, ← mul_assoc,
    ENNReal.inv_mul_cancel hL0 hLt, one_mul]

/-- **The hyperplane section $\{x_0 = 0\}$ of the cone is $\sigma_0$-null** (slab bound in the slicing
$Q = cx_0^2 + Q_m(x')$). -/
theorem lerayMeasure_cone_null (hQ : Q.Nondegenerate) (hQm : Qm.Nondegenerate)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 + Qv v Qm (Fin.tail x)) {U : Set (Fin (k + 1 + 1) → Fv)}
    (hU : U ∈ Cz v (k + 1 + 1)) :
    lerayMeasure v (haarV v) Q hQ 0 (U ∩ {x | x 0 = 0}) = 0 := by
  set ν := haarV v
  obtain ⟨s₀, hs₀⟩ := exists_cosetP_subset v hU.1.isClosed.isOpen_compl (x := 0) hU.2.2
  obtain ⟨R₀, hR₀⟩ := hU.1.isBounded.exists_norm_le
  set R := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hUR : ∀ x ∈ U, ‖x‖ ≤ R := fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  have hB : Metric.closedBall (0 : Fin (k + 1) → Fv) R \ cosetP v 0 s₀ ∈ Cz v (k + 1) :=
    closedBall_diff_mem_Cz v hRpos s₀
  have hA : Measurable fun t : Fv => c * t ^ 2 := measurable_const.mul (measurable_id.pow_const 2)
  obtain ⟨M, hM, hslab⟩ := vol_slab_le v ν Qm hQm hB hA
  have hbound : ∀ j ≥ s₀, lerayMeasure v ν Q hQ 0 (U ∩ {x | x 0 = 0}) ≤ M * ν (latticeV v (j : ℤ) : Set Fv) := by
    intro j hj
    set Uj := U ∩ {x : Fin (k + 1 + 1) → Fv | ‖x 0‖ ≤ ‖HN.ϖ v‖ ^ j}
    have hcl : IsClopen {x : Fin (k + 1 + 1) → Fv | ‖x 0‖ ≤ ‖HN.ϖ v‖ ^ j} :=
      isClopen_norm_le v (continuous_apply 0) (pow_pos (norm_ϖ_pos v) j)
    have hUjCz : Uj ∈ Cz v (k + 1 + 1) := ⟨hU.1.inter_right hcl.1, hU.2.1.inter hcl.2, fun h => hU.2.2 h.1⟩
    have hsub : U ∩ {x | x 0 = 0} ⊆ Uj := by
      rintro x ⟨hx, hx0⟩
      refine ⟨hx, ?_⟩
      show ‖x 0‖ ≤ _
      rw [show x 0 = 0 from hx0, norm_zero]; positivity
    refine (measure_mono hsub).trans ?_
    obtain ⟨K, hK⟩ := (lerayMeasure_eventually v ν Q hQ 0 hUjCz).exists
    rw [← hK, lerayThick_apply _ _ _ hUjCz.2.1.measurableSet, measure_shell]
    set L := ν (latticeV v (K : ℤ) : Set Fv)
    have hL0 : L ≠ 0 := (measure_latticeV_pos v ν K).ne'
    have hLt : L ≠ ⊤ := measure_latticeV_ne_top v ν K
    have hW : MeasurableSet (latticeV v (j : ℤ) : Set Fv) := measurableSet_latticeV v j
    have h := hslab _ hW 0 K
    calc L⁻¹ * volV ν (k + 1 + 1) (Uj ∩ Qv v Q ⁻¹' shell v 0 K)
        ≤ L⁻¹ * (M * ν (latticeV v (j : ℤ) : Set Fv) * L) := by
          gcongr
          refine (measure_mono ?_).trans h
          rintro x ⟨⟨hxU, hxj⟩, hxQ⟩
          have hxj' : ‖x 0‖ ≤ ‖HN.ϖ v‖ ^ j := hxj
          refine ⟨(mem_latticeV_iff_norm v).mpr hxj', ⟨?_, ?_⟩, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            refine (pi_norm_le_iff_of_nonneg hRpos.le).2 fun i => ?_
            exact (norm_le_pi_norm x i.succ).trans (hUR x hxU)
          · intro hP
            apply hs₀ _ hxU
            rw [cosetP_eq, Metric.mem_closedBall, dist_zero_right]
            rw [cosetP_eq, Metric.mem_closedBall, dist_zero_right] at hP
            refine (pi_norm_le_iff_of_nonneg (pow_nonneg (norm_nonneg _) _)).2 fun i => ?_
            refine Fin.cases ?_ (fun i => ?_) i
            · exact hxj'.trans (pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le hj)
            · exact (norm_le_pi_norm (Fin.tail x) i).trans hP
          · have := hxQ
            simp only [Set.mem_preimage, hQeq] at this
            exact this
      _ = M * ν (latticeV v (j : ℤ) : Set Fv) := by
          rw [show L⁻¹ * (M * ν (latticeV v (j : ℤ) : Set Fv) * L) =
            (L⁻¹ * L) * (M * ν (latticeV v (j : ℤ) : Set Fv)) by ring, ENNReal.inv_mul_cancel hL0 hLt, one_mul]
  have hlim : Tendsto (fun j : ℕ => M * ν (latticeV v (j : ℤ) : Set Fv)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (tendsto_measure_latticeV v ν) (Or.inr hM)
    rwa [mul_zero] at this
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨s₀, hbound⟩)) bot_le

end Cone

/-! ### The cone chart: $\sigma_0 = $ image of $|q|^{k-1}dq\otimes\sigma'_{-c}$ under $(q, y) \mapsto q(1, y)$ -/

section ConeChart

variable {k : ℕ} (Qm : QuadForm (v.adicCompletionIntegers F) (k + 1)) (hQm : Qm.Nondegenerate)

theorem distribHaarChar_eq_norm (u : Fvˣ) : (distribHaarChar Fv u : ℝ) = ‖(u : Fv)‖ := by
  have h := WeilRep.modK_eq_norm v (Units.ne_zero u)
  rw [Analysis.Weil.modK_of_ne (Units.ne_zero u), Units.mk0_val] at h
  exact h

include hQm in
theorem sigmaFinite_lerayMeasure (ρ : Fv) : SigmaFinite (lerayMeasure v (haarV v) Qm hQm ρ) := by
  obtain ⟨T, s, hTc, -, hmem, hUeq⟩ := exists_countable_union_Cz v (isClosed_singleton (x := (0 : Fin (k + 1) → Fv))).isOpen_compl
    (by simp)
  refine Measure.sigmaFinite_of_countable (S := insert {0} ((fun x => cosetP v x (s x)) '' T))
    ((hTc.image _).insert _) ?_ ?_
  · rintro t (rfl | ⟨x, hx, rfl⟩)
    · rw [lerayMeasure_singleton_zero]; exact ENNReal.zero_lt_top
    · exact lerayMeasure_lt_top v _ Qm hQm ρ (hmem x hx)
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = 0
    · exact ⟨{0}, Set.mem_insert _ _, hx⟩
    · have : x ∈ ({0}ᶜ : Set (Fin (k + 1) → Fv)) := hx
      rw [hUeq, Set.mem_iUnion₂] at this
      obtain ⟨y, hy, hxy⟩ := this
      exact ⟨_, Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩, hxy⟩

/-- The radial density $|q|_v^{k-1}$ (written $|q|^k/|q|$, so that it is $0$ at $q = 0$). -/
def rhoC (k : ℕ) (q : Fv) : ℝ≥0∞ := ENNReal.ofReal (‖q‖ ^ k / ‖q‖)

theorem measurable_rhoC : Measurable (rhoC v k) :=
  ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const k).div measurable_norm)

/-- The cone point $q(1, y)$. -/
def coneVecV (q : Fv) (y : Fin (k + 1) → Fv) : Fin (k + 1 + 1) → Fv := q • (Fin.cons 1 y : Fin (k + 1 + 1) → Fv)

theorem measurable_coneVecV : Measurable fun p : Fv × (Fin (k + 1) → Fv) => coneVecV v p.1 p.2 :=
  (continuous_fst.smul (continuous_pi fun i => Fin.cases continuous_const
    (fun j => (continuous_apply j).comp continuous_snd) i)).measurable

theorem coneVecV_zero (q : Fv) (y : Fin (k + 1) → Fv) : coneVecV v q y 0 = q := by simp [coneVecV]

theorem tail_coneVecV (q : Fv) (y : Fin (k + 1) → Fv) : Fin.tail (coneVecV v q y) = q • y := by
  funext i; simp [coneVecV, Fin.tail]

/-- **The cone chart measure**: the image of $|q|_v^{k-1}dq\otimes\sigma'_{-c}$ under $(q, y) \mapsto q(1, y)$, with $\sigma'_{-c}$
the Leray measure of $Q_m$ at $-c$. -/
def coneChart (c : Fv) : Measure (Fin (k + 1 + 1) → Fv) :=
  (((haarV v).withDensity (rhoC v k)).prod (lerayMeasure v (haarV v) Qm hQm (-c))).map
    fun p => coneVecV v p.1 p.2

theorem lintegral_coneChart (c : Fv) {G : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂coneChart v Qm hQm c =
      ∫⁻ q, rhoC v k q * ∫⁻ y, G (coneVecV v q y) ∂lerayMeasure v (haarV v) Qm hQm (-c) ∂haarV v := by
  have := sigmaFinite_lerayMeasure v Qm hQm (-c)
  have hm : Measurable fun p : Fv × (Fin (k + 1) → Fv) => G (coneVecV v p.1 p.2) := hG.comp (measurable_coneVecV v)
  rw [coneChart, lintegral_map hG (measurable_coneVecV v),
    lintegral_prod (fun p : Fv × (Fin (k + 1) → Fv) => G (coneVecV v p.1 p.2)) hm.aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_rhoC v) hm.lintegral_prod_right'

/-- The scaling law in the form used for the cone: $\sigma'_{q^2\rho}(B) = |q|_v^{k-1}\,\sigma'_\rho(q^{-1}B)$. -/
theorem lerayMeasure_scale_apply {q : Fv} (hq : q ≠ 0) (ρ : Fv) {B : Set (Fin (k + 1) → Fv)} (hB : MeasurableSet B) :
    lerayMeasure v (haarV v) Qm hQm (q ^ 2 * ρ) B =
      rhoC v k q * lerayMeasure v (haarV v) Qm hQm ρ ((fun y => q • y) ⁻¹' B) := by
  set u : Fvˣ := Units.mk0 q hq
  have h := lerayMeasure_map_smul_units v (haarV v) Qm hQm u ρ
  have hmeas : Measurable fun y : Fin (k + 1) → Fv => q • y := (continuous_const_smul q).measurable
  have h2 := congrArg (fun μ => μ B) h
  simp only [Measure.map_apply hmeas hB, Measure.smul_apply, smul_eq_mul, u, Units.val_mk0] at h2
  have hΔ : (distribHaarChar Fv u : ℝ≥0∞) = ENNReal.ofReal ‖q‖ := by
    rw [← ENNReal.ofReal_coe_nnreal, show ((distribHaarChar Fv u : ℝ≥0) : ℝ) = ‖q‖ from
      distribHaarChar_eq_norm v u]
  rw [hΔ] at h2
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr hq
  set r : ℝ≥0∞ := ENNReal.ofReal ‖q‖ ^ 2 / ENNReal.ofReal ‖q‖ ^ (k + 1)
  have hr : r = ENNReal.ofReal (‖q‖ ^ 2 / ‖q‖ ^ (k + 1)) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hq0 _), ENNReal.ofReal_pow hq0.le, ENNReal.ofReal_pow hq0.le]
  have hrr : rhoC v k q * r = 1 := by
    rw [hr, rhoC, ← ENNReal.ofReal_mul (by positivity)]
    rw [show ‖q‖ ^ k / ‖q‖ * (‖q‖ ^ 2 / ‖q‖ ^ (k + 1)) = 1 by field_simp; ring, ENNReal.ofReal_one]
  rw [h2, ← mul_assoc, hrr, one_mul]

theorem coneChart_boxP (c : Fv) {A : Set Fv} (hA : MeasurableSet A) {B : Set (Fin (k + 1) → Fv)}
    (hB : MeasurableSet B) :
    coneChart v Qm hQm c (boxP v A B) = ∫⁻ a in A, lerayMeasure v (haarV v) Qm hQm (a ^ 2 * -c) B ∂haarV v := by
  have hP : MeasurableSet (boxP v A B) :=
    (hA.preimage (measurable_pi_apply 0)).inter (hB.preimage (continuous_tail v).measurable)
  rw [← lintegral_indicator_one hP, lintegral_coneChart v Qm hQm c (measurable_one.indicator hP),
    ← lintegral_indicator hA]
  have hae : ∀ᵐ q ∂haarV v, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  have hset : ∀ y, (boxP v A B).indicator (1 : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞) (coneVecV v q y) =
      A.indicator 1 q * ((fun y => q • y) ⁻¹' B).indicator 1 y := by
    intro y
    have hmem : coneVecV v q y ∈ boxP v A B ↔ q ∈ A ∧ q • y ∈ B := by
      simp only [boxP, Set.mem_setOf_eq, coneVecV_zero, tail_coneVecV]
    classical
    by_cases h1 : q ∈ A <;> by_cases h2 : q • y ∈ B
    · rw [Set.indicator_of_mem (hmem.mpr ⟨h1, h2⟩), Set.indicator_of_mem h1,
        Set.indicator_of_mem (show y ∈ (fun y => q • y) ⁻¹' B from h2)]; simp
    · rw [Set.indicator_of_notMem (fun h => h2 (hmem.mp h).2),
        Set.indicator_of_notMem (show y ∉ (fun y => q • y) ⁻¹' B from h2)]; simp
    · rw [Set.indicator_of_notMem (fun h => h1 (hmem.mp h).1), Set.indicator_of_notMem h1]; simp
    · rw [Set.indicator_of_notMem (fun h => h1 (hmem.mp h).1), Set.indicator_of_notMem h1]; simp
  simp_rw [hset]
  rw [lintegral_const_mul _ (measurable_one.indicator (hB.preimage (continuous_const_smul q).measurable)),
    lintegral_indicator_one (hB.preimage (continuous_const_smul q).measurable)]
  by_cases hqA : q ∈ A
  · rw [Set.indicator_of_mem hqA, Set.indicator_of_mem hqA, Pi.one_apply, one_mul,
      lerayMeasure_scale_apply v Qm hQm hq (-c) hB]
  · rw [Set.indicator_of_notMem hqA, Set.indicator_of_notMem hqA]; simp

theorem cosetP_eq_boxP (y : Fin (k + 1 + 1) → Fv) (s : ℕ) :
    cosetP v y s = boxP v {a | Valued.v (a - y 0) ≤ exp (-(s : ℤ))} (cosetP v (Fin.tail y) s) := by
  ext x
  simp only [cosetP, boxP, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.tail]

variable {Q : QuadForm (v.adicCompletionIntegers F) (k + 1 + 1)} {c : v.adicCompletion F}

/-- The two measures agree on a small box far from $\{x_0 = 0\}$. -/
theorem lerayMeasure_cone_box_eq (hQ : Q.Nondegenerate) (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 + Qv v Qm (Fin.tail x))
    {r : ℝ} (y : Fin (k + 1 + 1) → Fv) (s : ℕ) (hs : ‖HN.ϖ v‖ ^ (2 * s) < ‖c‖ * r ^ 2)
    (hr : ∀ x ∈ cosetP v y s, r ≤ ‖x 0‖) (h0 : (0 : Fin (k + 1 + 1) → Fv) ∉ cosetP v y s) (hr0 : 0 < r) :
    lerayMeasure v (haarV v) Q hQ 0 (cosetP v y s) = coneChart v Qm hQm c (cosetP v y s) := by
  set A : Set Fv := {a | Valued.v (a - y 0) ≤ exp (-(s : ℤ))}
  have hAeq : A = Metric.closedBall (y 0) (‖HN.ϖ v‖ ^ s) := by
    ext a; simp [A, Metric.mem_closedBall, dist_eq_norm, ← norm_le_iff_v]
  have hAc : IsCompact A := by rw [hAeq]; exact isCompact_closedBall _ _
  have hAo : IsOpen A := by rw [hAeq]; exact IsUltrametricDist.isOpen_closedBall _ (pow_pos (norm_ϖ_pos v) s).ne'
  have hAr : ∀ a ∈ A, r ≤ ‖a‖ := by
    intro a ha
    have : (Fin.cons a (Fin.tail y) : Fin (k + 1 + 1) → Fv) ∈ cosetP v y s := by
      rw [cosetP_eq_boxP]
      exact ⟨by simpa [A] using ha, by simpa using mem_cosetP_self v (Fin.tail y) s⟩
    simpa using hr _ this
  have hBm : MeasurableSet (cosetP v (Fin.tail y) s) := measurableSet_cosetP v _ s
  rw [cosetP_eq_boxP, coneChart_boxP v Qm hQm c hAo.measurableSet hBm]
  by_cases hB0 : (0 : Fin (k + 1) → Fv) ∈ cosetP v (Fin.tail y) s
  · -- far from the cone: both sides vanish
    have hBeq : cosetP v (Fin.tail y) s = cosetP v 0 s := by
      rcases cosetP_eq_or_disjoint v (Fin.tail y) 0 s with h | h
      · exact h
      · exact (Set.disjoint_iff.mp h ⟨hB0, mem_cosetP_self v 0 s⟩).elim
    have hsmall : ∀ a ∈ A, ∀ z ∈ cosetP v (Fin.tail y) s, ‖Qv v Qm z‖ < ‖c * a ^ 2‖ := by
      intro a ha z hz
      rw [hBeq] at hz
      calc ‖Qv v Qm z‖ ≤ ‖HN.ϖ v‖ ^ (2 * s) := norm_qv_le_of_mem v Qm hz
        _ < ‖c‖ * r ^ 2 := hs
        _ ≤ ‖c * a ^ 2‖ := by rw [norm_mul, norm_pow]; gcongr; exact hAr a ha
    have hL : lerayMeasure v (haarV v) Q hQ 0 (boxP v A (cosetP v (Fin.tail y) s)) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (lerayMeasure_compl_level v (haarV v) Q hQ 0)
      show Qv v Q x ≠ 0
      rw [hQeq]
      intro h0
      have h1 := hsmall _ hx.1 _ hx.2
      rw [show Qv v Qm (Fin.tail x) = -(c * x 0 ^ 2) by linear_combination h0, norm_neg] at h1
      exact lt_irrefl _ h1
    have hR : ∀ a ∈ A, lerayMeasure v (haarV v) Qm hQm (a ^ 2 * -c) (cosetP v (Fin.tail y) s) = 0 := by
      intro a ha
      refine measure_mono_null (fun z hz => ?_) (lerayMeasure_compl_level v (haarV v) Qm hQm _)
      show Qv v Qm z ≠ a ^ 2 * -c
      intro h
      have h1 := hsmall a ha z hz
      rw [h, show a ^ 2 * -c = -(c * a ^ 2) by ring, norm_neg] at h1
      exact lt_irrefl _ h1
    rw [hL, setLIntegral_congr_fun hAo.measurableSet hR, lintegral_zero]
  · have hBCz : cosetP v (Fin.tail y) s ∈ Cz v (k + 1) :=
      ⟨by rw [cosetP_eq]; exact isCompact_closedBall _ _, isOpen_cosetP v _ s, hB0⟩
    have hQm' := hQm
    exact lerayMeasure_cone_box v hQ hQm hQeq hAc hAo hBCz

/-- The chart measure does not see $\{x_0 = 0\}$. -/
theorem coneChart_null (c : Fv) : coneChart v Qm hQm c {x | x 0 = 0} = 0 := by
  have hZ : MeasurableSet {x : Fin (k + 1 + 1) → Fv | x 0 = 0} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have := sigmaFinite_lerayMeasure v Qm hQm (-c)
  rw [coneChart, Measure.map_apply (measurable_coneVecV v) hZ]
  refine measure_mono_null (t := ({0} : Set Fv) ×ˢ Set.univ) ?_ ?_
  · rintro ⟨q, y⟩ h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, coneVecV_zero] at h
    exact ⟨h, Set.mem_univ _⟩
  · rw [Measure.prod_prod, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_singleton, measure_singleton, zero_smul, lintegral_zero_measure, zero_mul]

/-- **The cone chart at a finite place** (every $v$, dyadic included; $c \ne 0$, $Q_m$ nondegenerate,
$Q(x) = cx_0^2 + Q_m(x')$): the Leray measure $\sigma_0$ of the punctured cone is the image of
$|q|_v^{k-1}dq\otimes\sigma'_{-c}$ under $(q, y) \mapsto q(1, y)$, $\sigma'_{-c}$ the Leray measure of $Q_m$ on $\{Q_m = -c\}$:
$$\int F\,d\sigma_0 = \int_{F_v}|q|_v^{k-1}\int F(q(1, y))\,d\sigma'_{-c}(y)\,dq.$$
This is the slicing $\sigma_0 = dx_0\otimes\sigma'_{-cx_0^2}$ (`lerayMeasure_cone_box`), the scaling
$\sigma'_{q^2\rho} = |q|^{k-1}(q\,\cdot)_*\sigma'_\rho$ (`lerayMeasure_map_smul_units`), and the nullity of $\{x_0 = 0\}$
(`lerayMeasure_cone_null`); the same normalization as at the real and complex places (`ConeReal.sigCone`). -/
@[kb "weil1982" "§2.2 (the Leray form dx/dQ on the cone Q = 0); §2.4 [unverified]"]
theorem lerayMeasure_cone_eq_coneChart (hQ : Q.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 + Qv v Qm (Fin.tail x)) :
    lerayMeasure v (haarV v) Q hQ 0 = coneChart v Qm hQm c := by
  refine measure_ext_Cz v (lerayMeasure_singleton_zero v _ Q hQ 0) ?_
    (fun U hU => (lerayMeasure_lt_top v _ Q hQ 0 hU).ne) fun U hU => ?_
  · refine measure_mono_null (fun x hx => ?_) (coneChart_null v Qm hQm c)
    simp only [Set.mem_singleton_iff] at hx
    simp [hx]
  set W : ℕ → Set (Fin (k + 1 + 1) → Fv) := fun j => U \ {x | ‖x 0‖ < ‖HN.ϖ v‖ ^ j} with hW
  have hcont : Continuous fun x : Fin (k + 1 + 1) → Fv => x 0 := continuous_apply 0
  have hlt : ∀ j : ℕ, IsClopen {x : Fin (k + 1 + 1) → Fv | ‖x 0‖ < ‖HN.ϖ v‖ ^ j} := by
    intro j
    have h : {x : Fin (k + 1 + 1) → Fv | ‖x 0‖ < ‖HN.ϖ v‖ ^ j} =
        (fun x => x 0) ⁻¹' Metric.ball 0 (‖HN.ϖ v‖ ^ j) := by ext x; simp
    rw [h]
    exact ⟨(IsUltrametricDist.isClosed_ball _ _).preimage hcont, Metric.isOpen_ball.preimage hcont⟩
  have hWCz : ∀ j, W j ∈ Cz v (k + 1 + 1) := fun j =>
    ⟨hU.1.diff (hlt j).2, hU.2.1.sdiff (hlt j).1, fun h => hU.2.2 h.1⟩
  have hWr : ∀ j, ∀ x ∈ W j, ‖HN.ϖ v‖ ^ j ≤ ‖x 0‖ := fun j x hx => not_lt.mp hx.2
  have hmono : Monotone W := by
    intro i j hij x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    exact lt_of_lt_of_le h (pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le hij)
  have hUnion : (⋃ j, W j) = U \ {x | x 0 = 0} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_setOf_eq, hW, not_lt]
    constructor
    · rintro ⟨j, hxU, hj⟩
      refine ⟨hxU, fun h => ?_⟩
      rw [h, norm_zero] at hj
      exact absurd hj (not_le.mpr (pow_pos (norm_ϖ_pos v) j))
    · rintro ⟨hxU, hx⟩
      have hpos : 0 < ‖x 0‖ := norm_pos_iff.mpr hx
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hpos (norm_ϖ_lt_one v)
      exact ⟨j, hxU, hj.le⟩
  have h1 : lerayMeasure v (haarV v) Q hQ 0 U = ⨆ j, lerayMeasure v (haarV v) Q hQ 0 (W j) := by
    rw [← hmono.measure_iUnion, hUnion,
      ← measure_diff_null (s := U) (lerayMeasure_cone_null v hQ hQm hQeq hU)]
    congr 1
    ext x; simp [and_comm]
  have h2 : coneChart v Qm hQm c U = ⨆ j, coneChart v Qm hQm c (W j) := by
    rw [← hmono.measure_iUnion, hUnion, measure_diff_null (coneChart_null v Qm hQm c)]
  rw [h1, h2]
  refine iSup_congr fun j => ?_
  -- decompose `W j` into small boxes
  set r := ‖HN.ϖ v‖ ^ j with hr
  have hr0 : 0 < r := pow_pos (norm_ϖ_pos v) j
  have hcr : 0 < ‖c‖ * r ^ 2 := mul_pos (norm_pos_iff.mpr hc) (pow_pos hr0 2)
  obtain ⟨s₀, hs₀⟩ := exists_coset_decomp v (hWCz j).1 (hWCz j).2.1
  obtain ⟨s₁, hs₁⟩ := exists_pow_lt_of_lt_one hcr (norm_ϖ_lt_one v)
  obtain ⟨𝒞, h𝒞, hdisj, hcov⟩ := hs₀ (max s₀ s₁) (le_max_left _ _)
  set s := max s₀ s₁
  have hs : ‖HN.ϖ v‖ ^ (2 * s) < ‖c‖ * r ^ 2 :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) (norm_ϖ_lt_one v).le (by omega)) hs₁
  have hmeasC : ∀ C ∈ 𝒞, MeasurableSet C := by
    intro C hC
    obtain ⟨y, -, rfl⟩ := h𝒞 C hC
    exact measurableSet_cosetP v y s
  have hbox : ∀ C ∈ 𝒞, lerayMeasure v (haarV v) Q hQ 0 C = coneChart v Qm hQm c C := by
    intro C hC
    obtain ⟨y, hy, rfl⟩ := h𝒞 C hC
    have hsub : cosetP v y s ⊆ W j := by
      rw [hcov]; exact Set.subset_biUnion_of_mem (u := id) hC
    exact lerayMeasure_cone_box_eq v Qm hQm hQ hQeq y s hs (fun x hx => hWr j x (hsub hx))
      (fun h => (hWCz j).2.2 (hsub h)) hr0
  have e1 := measure_biUnion_finset (μ := lerayMeasure v (haarV v) Q hQ 0) hdisj hmeasC
  have e2 := measure_biUnion_finset (μ := coneChart v Qm hQm c) hdisj hmeasC
  simp only [id_eq] at e1 e2
  rw [hcov, e1, e2]
  exact Finset.sum_congr rfl hbox

/-- **The cone chart, integral form.** -/
theorem lintegral_lerayMeasure_cone (hQ : Q.Nondegenerate) (hc : c ≠ 0)
    (hQeq : ∀ x, Qv v Q x = c * x 0 ^ 2 + Qv v Qm (Fin.tail x)) {G : (Fin (k + 1 + 1) → Fv) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ x, G x ∂lerayMeasure v (haarV v) Q hQ 0 =
      ∫⁻ q, rhoC v k q * ∫⁻ y, G (coneVecV v q y) ∂lerayMeasure v (haarV v) Qm hQm (-c) ∂haarV v := by
  rw [lerayMeasure_cone_eq_coneChart v Qm hQm hQ hc hQeq, lintegral_coneChart v Qm hQm c hG]

end ConeChart

end QuadFormsKB.Tamagawa.Measure.ConeFinite
