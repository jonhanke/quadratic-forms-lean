import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayFiniteNF

/-!
# Stabilization of the thickened Leray measures at a finite place

The Leray measure $dx/dQ$ on $\{Q = \rho\}$ is the limit of the thickened measures $\lambda_{\rho,k}$
(`LerayThick.lean`) as $k \to \infty$. This file proves that on every **compact open set $U \not\ni 0$** the family
$k \mapsto \lambda_{\rho,k}(U)$ is *eventually constant*, with a threshold $k_0(U)$ that does **not** depend on $\rho$. No
implicit function theorem, no Hensel lemma and no point counting are used: the argument is a **shear**.

*Proof.* Cut $U$ into cosets $P = y + \mathfrak p^sL$ ($y \neq 0$). Choose $i$ with $|(H^{\mathsf T}y)_i|$ maximal, so
$u_0 = B(y, e_i) \ne 0$. For $x \in P$ and $t \in \mathfrak p^{k}/u_0$,
$Q(x + te_i) = Q(x) + t\,u_0 + (\text{an element of } \mathfrak p^{k+1})$ once $s$ and $k$ are large. The translation
$x \mapsto x + te_i$ preserves $\mathrm{vol}$ and $P$, so the volumes of $\{x \in P : Q(x) \in c + \mathfrak p^{k+1}\}$ are the same for
all $c \in \rho + \mathfrak p^k$ (`vol_shear`). Averaging over $c$ (Tonelli, `vol_shell_succ`) gives
$\lambda_{\rho,k}(P) = \lambda_{\rho,k+1}(P)$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.LerayCone
open QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F


section Averaging

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

lemma measurableSet_shell (ρ : v.adicCompletion F) (k : ℕ) : MeasurableSet (shell v ρ k) := by
  rw [shell_eq]
  exact (measurableSet_latticeV v k).preimage (measurable_id.add_const _)

lemma shell_subset (ρ c : v.adicCompletion F) (k : ℕ) (hc : c ∈ shell v ρ k) :
    shell v c (k + 1) ⊆ shell v ρ k := by
  intro y hy
  simp only [shell, Set.mem_ofPred_eq] at hc hy ⊢
  calc Valued.v (y - ρ) = Valued.v ((y - c) + (c - ρ)) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ exp (-(k : ℤ)) := max_le (hy.trans (by rw [exp_le_exp]; omega)) hc

/-- **Averaging over the cosets** (Tonelli). If the volume of $A \cap f^{-1}(c + \mathfrak p^{k+1})$ is the same for all
$c \in \rho + \mathfrak p^k$, then $\nu(\mathfrak p^{k+1})\,\mathrm{vol}(A \cap f^{-1}(\rho+\mathfrak p^k)) =
\mathrm{vol}(A \cap f^{-1}(\rho+\mathfrak p^{k+1}))\,\nu(\rho+\mathfrak p^k)$. -/
theorem vol_shell_succ (A : Set (Fin n → v.adicCompletion F))
    (f : (Fin n → v.adicCompletion F) → v.adicCompletion F) (hf : Measurable f) (ρ : v.adicCompletion F) (k : ℕ)
    (h : ∀ c ∈ shell v ρ k, volV ν n (A ∩ f ⁻¹' shell v c (k + 1)) = volV ν n (A ∩ f ⁻¹' shell v ρ (k + 1))) :
    ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set (v.adicCompletion F)) * volV ν n (A ∩ f ⁻¹' shell v ρ k) =
      volV ν n (A ∩ f ⁻¹' shell v ρ (k + 1)) * ν (shell v ρ k) := by
  set M := shell v ρ k with hM
  set E : Set ((Fin n → v.adicCompletion F) × v.adicCompletion F) :=
    {p | Valued.v (f p.1 - p.2) ≤ exp (-((k + 1 : ℕ) : ℤ))} with hE
  have hEm : MeasurableSet E := by
    have : E = (fun p : (Fin n → v.adicCompletion F) × v.adicCompletion F => f p.1 - p.2) ⁻¹'
        (latticeV v ((k + 1 : ℕ) : ℤ) : Set (v.adicCompletion F)) := by
      ext p; simp [hE, mem_latticeV]
    rw [this]
    exact (measurableSet_latticeV v _).preimage ((hf.comp measurable_fst).sub measurable_snd)
  have hsfin : SFinite ((volV ν n).restrict A) := inferInstance
  have hfM : MeasurableSet (f ⁻¹' M) := (measurableSet_shell v ρ k).preimage hf
  classical
  have h1 : ((volV ν n).restrict A).prod (ν.restrict M) E =
      ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set (v.adicCompletion F)) * volV ν n (A ∩ f ⁻¹' M) := by
    rw [Measure.prod_apply hEm]
    have hsec : ∀ x, ν.restrict M (Prod.mk x ⁻¹' E) =
        (f ⁻¹' M).indicator (fun _ => ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set (v.adicCompletion F))) x := by
      intro x
      have hmeas : MeasurableSet (Prod.mk x ⁻¹' E) := measurable_prodMk_left hEm
      rw [Measure.restrict_apply hmeas]
      by_cases hx : f x ∈ M
      · have hset : Prod.mk x ⁻¹' E ∩ M = shell v (f x) (k + 1) := by
          ext c
          simp only [Set.mem_inter_iff, Set.mem_preimage, hE, Set.mem_ofPred_eq, shell]
          constructor
          · rintro ⟨h1, _⟩
            rw [← Valuation.map_neg]; simpa using h1
          · intro h2
            refine ⟨by rw [← Valuation.map_neg]; simpa using h2, ?_⟩
            exact shell_subset v ρ (f x) k hx (by simpa [shell] using h2)
        rw [hset, measure_shell, Set.indicator_of_mem (by simpa using hx)]
      · have hset : Prod.mk x ⁻¹' E ∩ M = ∅ := by
          ext c
          simp only [Set.mem_inter_iff, Set.mem_preimage, hE, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          intro h1 hcM
          apply hx
          have : f x ∈ shell v c (k + 1) := by
            simp only [shell, Set.mem_ofPred_eq]
            simpa using h1
          exact shell_subset v ρ c k hcM this
        rw [hset, measure_empty, Set.indicator_of_notMem (by simpa using hx)]
    simp_rw [hsec]
    rw [lintegral_indicator_const hfM, Measure.restrict_apply hfM, Set.inter_comm]
  have h2 : ((volV ν n).restrict A).prod (ν.restrict M) E =
      volV ν n (A ∩ f ⁻¹' shell v ρ (k + 1)) * ν M := by
    rw [Measure.prod_apply_symm hEm]
    have hsec : ∀ c ∈ M, ((volV ν n).restrict A) ((fun x => (x, c)) ⁻¹' E) =
        volV ν n (A ∩ f ⁻¹' shell v ρ (k + 1)) := by
      intro c hc
      have hset : (fun x => (x, c)) ⁻¹' E = f ⁻¹' shell v c (k + 1) := by
        ext x
        simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, shell]
      rw [hset, Measure.restrict_apply (hf (measurableSet_shell v c (k + 1))), Set.inter_comm, h c hc]
    rw [setLIntegral_congr_fun (measurableSet_shell v ρ k) hsec, lintegral_const, Measure.restrict_apply_univ]
  rw [h1] at h2
  exact h2

end Averaging

section Shear

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- **Shear equality.** If translation by $w$ preserves $U$ (in both directions) and carries $\{Q \in S\}$ to $\{Q \in S'\}$
on $U$, then $\mathrm{vol}(U \cap Q^{-1}S) = \mathrm{vol}(U \cap Q^{-1}S')$ (translation invariance of $\mathrm{vol}$). -/
theorem vol_shear (U : Set (Fin n → v.adicCompletion F)) (w : Fin n → v.adicCompletion F)
    (f : (Fin n → v.adicCompletion F) → v.adicCompletion F) (S S' : Set (v.adicCompletion F))
    (hU : ∀ x, x + w ∈ U ↔ x ∈ U) (hS : ∀ x ∈ U, f (x + w) ∈ S' ↔ f x ∈ S) :
    volV ν n (U ∩ f ⁻¹' S) = volV ν n (U ∩ f ⁻¹' S') := by
  have h := measure_preimage_add_right (volV ν n) w (U ∩ f ⁻¹' S')
  rw [← h]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨(hU x).mpr hx, (hS x hx).mpr hfx⟩
  · rintro ⟨hx, hfx⟩
    have hx' : x ∈ U := (hU x).mp hx
    exact ⟨hx', (hS x hx').mp hfx⟩

/-- The Hessian of $Q$ over $F_v$. -/
abbrev hessV (Q : QuadForm 𝔬 n) : Matrix (Fin n) (Fin n) Fv := Q.hessian.map (algebraMap 𝔬 Fv)

/-- $B(x, e_i) = x \cdot (H e_i)$. -/
def bil (Q : QuadForm 𝔬 n) (i : Fin n) (x : Fin n → Fv) : Fv := x ⬝ᵥ (hessV v Q *ᵥ Pi.single i 1)

/-- **The shear expansion**: $Q(x + te_i) = Q(x) + t\,B(x, e_i) + t^2Q(e_i)$. -/
theorem qv_add_shear (Q : QuadForm 𝔬 n) (x : Fin n → Fv) (t : Fv) (i : Fin n) :
    Qv v Q (x + t • Pi.single i 1) = Qv v Q x + t * bil v Q i x + t ^ 2 * Qv v Q (Pi.single i 1) := by
  have h := QuadForm.polar_eq_hessian Fv Q x (t • Pi.single i 1)
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h
  have h2 := qv_smul v Q t (Pi.single i 1)
  simp only [Qv] at h2 ⊢
  unfold bil
  linear_combination h + h2

lemma valued_algebraMap_le_one (a : 𝔬) : Valued.v (algebraMap 𝔬 Fv a) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a.2

/-- Coordinates of size $\le q^{-s}$ give $|B(z, e_i)| \le q^{-s}$. -/
lemma valued_bil_le (Q : QuadForm 𝔬 n) (i : Fin n) (z : Fin n → Fv) (s : ℕ)
    (hz : ∀ j, Valued.v (z j) ≤ exp (-(s : ℤ))) : Valued.v (bil v Q i z) ≤ exp (-(s : ℤ)) := by
  unfold bil
  rw [dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  have h1 : Valued.v ((hessV v Q *ᵥ Pi.single i 1) j) ≤ 1 := by
    simp only [hessV, Matrix.mulVec_single_one, Matrix.map_apply]
    exact valued_algebraMap_le_one v _
  calc Valued.v (z j) * Valued.v ((hessV v Q *ᵥ Pi.single i 1) j) ≤ exp (-(s : ℤ)) * 1 := by gcongr; exact hz j
    _ = _ := mul_one _

lemma bil_sub (Q : QuadForm 𝔬 n) (i : Fin n) (x y : Fin n → Fv) : bil v Q i (x - y) = bil v Q i x - bil v Q i y := by
  unfold bil; rw [sub_dotProduct]

/-- The coset $y + \mathfrak p_v^sL_v$ of $V_v = F_v^n$. -/
def cosetP (y : Fin n → Fv) (s : ℕ) : Set (Fin n → Fv) := {x | ∀ j, Valued.v (x j - y j) ≤ exp (-(s : ℤ))}

lemma single_mem_latL (i : Fin n) : (Pi.single i 1 : Fin n → Fv) ∈ latL v n := by
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- **The shear lemma on a coset.** If $|B(y, e_i)| \ge q^{-m}$ and $s \ge m + 1$, $k \ge \max(s + m, 2m + 1)$, then the
volumes $\mathrm{vol}(\{x \in y + \mathfrak p^sL : Q(x) \in c + \mathfrak p^{k+1}\})$ are the same for all
$c \in \rho + \mathfrak p^k$. -/
theorem vol_cosetP_shear (Q : QuadForm 𝔬 n) (y : Fin n → Fv) (i : Fin n) (mm s k : ℕ)
    (hu : exp (-(mm : ℤ)) ≤ Valued.v (bil v Q i y)) (hs : mm + 1 ≤ s) (hk1 : s + mm ≤ k) (hk2 : 2 * mm + 1 ≤ k)
    (ρ c : Fv) (hc : c ∈ shell v ρ k) :
    volV ν n (cosetP v y s ∩ Qv v Q ⁻¹' shell v c (k + 1)) =
      volV ν n (cosetP v y s ∩ Qv v Q ⁻¹' shell v ρ (k + 1)) := by
  set u₀ := bil v Q i y with hu₀
  have hupos : (0 : WithZero (Multiplicative ℤ)) < Valued.v u₀ := lt_of_lt_of_le (exp_pos) hu
  have hu0 : u₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hupos; exact lt_irrefl _ hupos
  set t : Fv := (c - ρ) / u₀ with ht
  have htu : t * u₀ = c - ρ := div_mul_cancel₀ _ hu0
  have htv : Valued.v t ≤ exp ((mm : ℤ) - k) := by
    rw [ht, map_div₀, div_le_iff₀ hupos]
    calc Valued.v (c - ρ) ≤ exp (-(k : ℤ)) := by simpa [shell] using hc
      _ = exp ((mm : ℤ) - k) * exp (-(mm : ℤ)) := by rw [← exp_add]; congr 1; ring
      _ ≤ exp ((mm : ℤ) - k) * Valued.v u₀ := by gcongr
  set w : Fin n → Fv := t • Pi.single i 1 with hw
  have hwj : ∀ j, Valued.v (w j) ≤ exp (-(s : ℤ)) := by
    intro j
    have : Valued.v (w j) ≤ Valued.v t := by
      simp only [hw, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs
      · simp
      · simp
    exact this.trans (htv.trans (by rw [exp_le_exp]; omega))
  have hU : ∀ x, x + w ∈ cosetP v y s ↔ x ∈ cosetP v y s := by
    have key : ∀ x, x ∈ cosetP v y s → x + w ∈ cosetP v y s := by
      intro x hx j
      have : x j + w j - y j = (x j - y j) + w j := by ring
      simp only [Pi.add_apply, this]
      exact (Valuation.map_add _ _ _).trans (max_le (hx j) (hwj j))
    refine fun x => ⟨fun h => ?_, key x⟩
    have := key (x + w) h
    have hh : ∀ j, Valued.v (-w j) ≤ exp (-(s : ℤ)) := fun j => by rw [Valuation.map_neg]; exact hwj j
    intro j
    have e : x j - y j = ((x + w) j - y j) + (-w j) := by simp only [Pi.add_apply]; ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (h j) (hh j))
  have hq0 : Valued.v (Qv v Q (Pi.single i 1)) ≤ 1 := valued_evalIn_le_one v Q (single_mem_latL v i)
  have hS : ∀ x ∈ cosetP v y s, Qv v Q (x + w) ∈ shell v c (k + 1) ↔ Qv v Q x ∈ shell v ρ (k + 1) := by
    intro x hx
    have hδ : Valued.v (bil v Q i (x - y)) ≤ exp (-(s : ℤ)) :=
      valued_bil_le v Q i (x - y) s fun j => by simpa using hx j
    have hbx : bil v Q i x = u₀ + bil v Q i (x - y) := by rw [bil_sub]; ring
    set E : Fv := t * bil v Q i (x - y) + t ^ 2 * Qv v Q (Pi.single i 1) with hE
    have hEv : Valued.v E ≤ exp (-((k + 1 : ℕ) : ℤ)) := by
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        calc Valued.v t * Valued.v (bil v Q i (x - y)) ≤ exp ((mm : ℤ) - k) * exp (-(s : ℤ)) := by gcongr
          _ ≤ _ := by rw [← exp_add, exp_le_exp]; push_cast; omega
      · rw [map_mul, map_pow]
        calc Valued.v t ^ 2 * Valued.v (Qv v Q (Pi.single i 1)) ≤ exp ((mm : ℤ) - k) ^ 2 * 1 := by gcongr
          _ = exp (2 * ((mm : ℤ) - k)) := by rw [mul_one, pow_two, ← exp_add]; congr 1; ring
          _ ≤ _ := by rw [exp_le_exp]; push_cast; omega
    have hexp : Qv v Q (x + w) - c = (Qv v Q x - ρ) + E := by
      rw [hw, qv_add_shear, hbx]
      linear_combination htu
    simp only [shell, Set.mem_ofPred_eq]
    rw [hexp]
    constructor
    · intro h
      have : Qv v Q x - ρ = ((Qv v Q x - ρ) + E) + (-E) := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le h (by rw [Valuation.map_neg]; exact hEv))
    · intro h
      exact (Valuation.map_add _ _ _).trans (max_le h hEv)
  exact (vol_shear v ν _ w _ _ _ hU hS).symm

end Shear

section Topology

lemma continuous_qv (Q : QuadForm 𝔬 n) : Continuous (Qv v Q) := by
  have : Qv v Q = fun x => x ⬝ᵥ (Q.coeff.map (algebraMap 𝔬 Fv) *ᵥ x) := by
    funext x; exact QuadForm.evalIn_eq_dotProduct Fv Q x
  rw [this]
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

lemma measurable_qv (Q : QuadForm 𝔬 n) : Measurable (Qv v Q) := (continuous_qv v Q).measurable

/-- $\|z\| \le \|\varpi\|^s \iff |z|_v \le q^{-s}$. -/
lemma norm_le_iff_v {z : Fv} {s : ℕ} : ‖z‖ ≤ ‖HN.ϖ v‖ ^ s ↔ Valued.v z ≤ exp (-(s : ℤ)) := by
  have h := coe_latticeV v (s : ℤ)
  rw [← mem_latticeV, ← SetLike.mem_coe, h, Metric.mem_closedBall, dist_zero_right, zpow_natCast, norm_pow]

lemma cosetP_eq (y : Fin n → Fv) (s : ℕ) : cosetP v y s = Metric.closedBall y (‖HN.ϖ v‖ ^ s) := by
  ext x
  rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg (by positivity)]
  simp only [cosetP, Set.mem_ofPred_eq, Pi.sub_apply, norm_le_iff_v]

lemma norm_ϖ_pos : 0 < ‖HN.ϖ v‖ := norm_pos_iff.mpr (HN.ϖ_ne_zero v)

lemma isOpen_cosetP (y : Fin n → Fv) (s : ℕ) : IsOpen (cosetP v y s) := by
  rw [cosetP_eq]
  exact IsUltrametricDist.isOpen_closedBall y (pow_pos (norm_ϖ_pos v) s).ne'

lemma measurableSet_cosetP (y : Fin n → Fv) (s : ℕ) : MeasurableSet (cosetP v y s) :=
  (isOpen_cosetP v y s).measurableSet

lemma mem_cosetP_self (y : Fin n → Fv) (s : ℕ) : y ∈ cosetP v y s := by
  intro j; simp

lemma cosetP_eq_or_disjoint (y z : Fin n → Fv) (s : ℕ) :
    cosetP v y s = cosetP v z s ∨ Disjoint (cosetP v y s) (cosetP v z s) := by
  simp only [cosetP_eq]
  exact IsUltrametricDist.closedBall_eq_or_disjoint y z _

/-- **A compact open set is a finite disjoint union of cosets of $\mathfrak p^sL$** (for $s$ large). -/
theorem exists_coset_decomp {U : Set (Fin n → Fv)} (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ 𝒞 : Finset (Set (Fin n → Fv)),
      (∀ C ∈ 𝒞, ∃ y ∈ U, C = cosetP v y s) ∧ (↑𝒞 : Set (Set (Fin n → Fv))).PairwiseDisjoint id ∧
      U = ⋃ C ∈ 𝒞, C := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hUc.exists_thickening_subset_open hUo subset_rfl
  obtain ⟨s₀, hs₀⟩ := exists_pow_lt_of_lt_one hδ (show ‖HN.ϖ v‖ < 1 from by
    simpa using norm_ϖ_lt_one v)
  refine ⟨s₀, fun s hs => ?_⟩
  have hr : ‖HN.ϖ v‖ ^ s < δ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (norm_ϖ_pos v).le (by simpa using norm_ϖ_lt_one v |>.le) hs) hs₀
  have hsub : ∀ y ∈ U, cosetP v y s ⊆ U := by
    intro y hy x hx
    apply hthick
    rw [Metric.mem_thickening_iff]
    exact ⟨y, hy, by rw [cosetP_eq, Metric.mem_closedBall] at hx; exact lt_of_le_of_lt hx hr⟩
  obtain ⟨t, htU, hcov⟩ := hUc.elim_nhds_subcover (fun y => cosetP v y s) fun y _ =>
    (isOpen_cosetP v y s).mem_nhds (mem_cosetP_self v y s)
  refine ⟨t.image (fun y => cosetP v y s), ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨y, htU y hy, rfl⟩
  · intro C hC C' hC' hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hC)
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hC')
    rcases cosetP_eq_or_disjoint v y z s with h | h
    · exact absurd h hne
    · exact h
  · apply Set.Subset.antisymm
    · intro x hx
      have := hcov hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨y, hy, hxy⟩ := this
      exact ⟨_, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨C, hC, hxC⟩ := hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hC
      exact hsub y (htU y hy) hxC

end Topology

section Stable

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- **From the averaged volume identity to equality of the thickened measures.** -/
theorem lerayThick_succ_eq (Q : QuadForm 𝔬 n) {A : Set (Fin n → Fv)} (hA : MeasurableSet A) (ρ : Fv) (k : ℕ)
    (h : ∀ c ∈ shell v ρ k, volV ν n (A ∩ Qv v Q ⁻¹' shell v c (k + 1)) =
      volV ν n (A ∩ Qv v Q ⁻¹' shell v ρ (k + 1))) :
    lerayThick ν (Qv v Q) (shell v ρ k) A = lerayThick ν (Qv v Q) (shell v ρ (k + 1)) A := by
  have hmain := vol_shell_succ v ν A (Qv v Q) (measurable_qv v Q) ρ k h
  rw [lerayThick_apply ν _ _ hA, lerayThick_apply ν _ _ hA, measure_shell, measure_shell]
  have ha0 : ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set Fv) ≠ 0 := (measure_latticeV_pos v ν _).ne'
  have hat : ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set Fv) ≠ ⊤ := measure_latticeV_ne_top v ν _
  have hb0 : ν (latticeV v (k : ℤ) : Set Fv) ≠ 0 := (measure_latticeV_pos v ν _).ne'
  have hbt : ν (latticeV v (k : ℤ) : Set Fv) ≠ ⊤ := measure_latticeV_ne_top v ν _
  rw [measure_shell] at hmain
  set a := ν (latticeV v ((k + 1 : ℕ) : ℤ) : Set Fv)
  set b := ν (latticeV v (k : ℤ) : Set Fv)
  set X := volV ν n (A ∩ Qv v Q ⁻¹' shell v ρ k)
  set Y := volV ν n (A ∩ Qv v Q ⁻¹' shell v ρ (k + 1))
  have hX : X = a⁻¹ * (Y * b) := by
    rw [← hmain, ← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
  rw [hX]
  calc b⁻¹ * (a⁻¹ * (Y * b)) = (b⁻¹ * b) * (a⁻¹ * Y) := by ring
    _ = a⁻¹ * Y := by rw [ENNReal.inv_mul_cancel hb0 hbt, one_mul]

lemma bil_eq_mulVec (Q : QuadForm 𝔬 n) (i : Fin n) (y : Fin n → Fv) :
    bil v Q i y = ((hessV v Q)ᵀ *ᵥ y) i := by
  unfold bil
  rw [Matrix.mulVec_single_one, dotProduct_comm]
  rfl

lemma exp_le_v_of_norm {z : Fv} {m : ℕ} (h : ‖HN.ϖ v‖ ^ m ≤ ‖z‖) : exp (-(m : ℤ)) ≤ Valued.v z := by
  have h1 : ‖HN.ϖ v ^ (m : ℤ)‖ ≤ ‖z‖ := by simpa [zpow_natCast, norm_pow] using h
  have := (Valued.toNormedField.norm_le_iff (x := HN.ϖ v ^ (m : ℤ)) (x' := z)).mp h1
  rwa [valued_ϖ_zpow] at this

/-- **Stabilization on compact open sets avoiding $0$** (the heart of the Leray limit): there is $k_0$, independent of $\rho$,
with $\lambda_{\rho,k}(U) = \lambda_{\rho,k+1}(U)$ for all $k \ge k_0$ and all $\rho \in F_v$. -/
@[kb "weil1982" "§2.4 (Leray measure as a limit of shells) [unverified]"]
theorem lerayThick_eventually_succ (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) {U : Set (Fin n → Fv)}
    (hUc : IsCompact U) (hUo : IsOpen U) (h0 : (0 : Fin n → Fv) ∉ U) :
    ∃ k₀ : ℕ, ∀ (ρ : Fv), ∀ k ≥ k₀,
      lerayThick ν (Qv v Q) (shell v ρ k) U = lerayThick ν (Qv v Q) (shell v ρ (k + 1)) U := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun ρ k _ => by simp⟩
  set A : Matrix (Fin n) (Fin n) Fv := (hessV v Q)ᵀ with hA
  have hdet : A.det ≠ 0 := by
    have hd : (hessV v Q).det = algebraMap 𝔬 Fv Q.hessian.det := by
      rw [RingHom.map_det]; rfl
    rw [hA, Matrix.det_transpose, hd]
    intro h
    apply hQ
    exact (Subtype.val_injective (by simpa using h : ((Q.hessian.det : 𝔬) : Fv) = 0))
  have hAne : ∀ y ∈ U, A *ᵥ y ≠ 0 := by
    intro y hy h
    apply h0
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet h
    rwa [this] at hy
  have hcont : ContinuousOn (fun y : Fin n → Fv => ‖A *ᵥ y‖) U :=
    (continuous_norm.comp (continuous_const.matrix_mulVec continuous_id)).continuousOn
  obtain ⟨y₀, hy₀, hmin⟩ := hUc.exists_isMinOn hne hcont
  set a := ‖A *ᵥ y₀‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr (hAne y₀ hy₀)
  obtain ⟨mm, hmm⟩ := exists_pow_lt_of_lt_one hapos (norm_ϖ_lt_one v)
  have hbil : ∀ y ∈ U, ∃ i, exp (-(mm : ℤ)) ≤ Valued.v (bil v Q i y) := by
    intro y hy
    have hge : a ≤ ‖A *ᵥ y‖ := hmin hy
    by_contra hcon
    push Not at hcon
    have : ‖A *ᵥ y‖ < a := by
      rw [pi_norm_lt_iff hapos]
      intro i
      by_contra hi
      push Not at hi
      have := exp_le_v_of_norm v (z := (A *ᵥ y) i) (m := mm) (hmm.le.trans hi)
      exact absurd (hcon i) (not_lt.mpr (by rwa [bil_eq_mulVec]))
    exact absurd hge (not_le.mpr this)
  obtain ⟨s₀, hs₀⟩ := exists_coset_decomp v hUc hUo
  set s := max s₀ (mm + 1) with hs
  obtain ⟨𝒞, hC, hdisj, hUeq⟩ := hs₀ s (le_max_left _ _)
  refine ⟨max (s + mm) (2 * mm + 1), fun ρ k hk => ?_⟩
  have hmeasC : ∀ C ∈ 𝒞, MeasurableSet C := by
    intro C hCm
    obtain ⟨y, -, rfl⟩ := hC C hCm
    exact measurableSet_cosetP v y s
  have hCeq : ∀ C ∈ 𝒞, lerayThick ν (Qv v Q) (shell v ρ k) C = lerayThick ν (Qv v Q) (shell v ρ (k + 1)) C := by
    intro C hCm
    obtain ⟨y, hy, rfl⟩ := hC C hCm
    obtain ⟨i, hi⟩ := hbil y hy
    refine lerayThick_succ_eq v ν Q (measurableSet_cosetP v y s) ρ k fun c hc => ?_
    exact vol_cosetP_shear v ν Q y i mm s k hi (le_max_right _ _) ((le_max_left _ _).trans hk)
      ((le_max_right _ _).trans hk) ρ c hc
  have hsum : ∀ k' : ℕ, lerayThick ν (Qv v Q) (shell v ρ k') U =
      ∑ C ∈ 𝒞, lerayThick ν (Qv v Q) (shell v ρ k') C := by
    intro k'
    conv_lhs => rw [hUeq]
    exact measure_biUnion_finset hdisj hmeasC
  rw [hsum k, hsum (k + 1)]
  exact Finset.sum_congr rfl hCeq

end Stable

end QuadFormsKB.Tamagawa.Measure.LerayFinite
