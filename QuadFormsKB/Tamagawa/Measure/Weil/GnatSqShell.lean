/-
# Archimedean shells for the idele measure

**Layer:** a totally real number field $F$ ($r$ real places), the $\omega_\infty$ on $F_\infty^\times$ (`omegaInf`).

* `BInf` $= \{u : 1\le u_w < e^2\ \forall w\}$, `Bsq` $= \{u : 1\le u_w^2 < e^2\ \forall w\}$ (open–closed boxes in $F_\infty^\times$).
* **`omegaInf_Bsq`**: $\omega_\infty(\text{Bsq}) = \omega_\infty(\text{BInf})$, both $\in(0,\infty)$: each is a disjoint union of $2^r$
  translates of $\{1\le u_w<e\}$ (signs $\pm1$, resp. $1, e$), so no integration is needed — only translation invariance.
* `Bset` $= \{t\in\mathbb A^\times : t_\infty\in\text{BInf},\ t_f\in\hat{\mathcal O}^\times\}$ and **`tamIdeles_sq_mem_Bset`**: for
  $t\gg0$ with $t_f\in\hat{\mathcal O}^\times$, $\mathrm{tamIdeles}\{u : u_f\in\hat{\mathcal O}^\times,\ u^2t\in\text{Bset}\} =
  \omega_\infty(\text{Bsq})\cdot\mu_f(\hat{\mathcal O}^\times)$ (translation by $\sqrt t$).

Source: Weil 1982, §2.3 (measures on $F_\infty^\times$) [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqPD

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  IsDedekindDomain
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]


/-- The unit of $F_\infty$ with real components $f$ (nonzero) and complex components $1$. -/
def mkInfUnitR (f : {w : InfinitePlace F // w.IsReal} → ℝ) (hf : ∀ w, f w ≠ 0) : (mixedSpace F)ˣ where
  val := (f, 1)
  inv := (fun w => (f w)⁻¹, 1)
  val_inv := Prod.ext (funext fun w => mul_inv_cancel₀ (hf w)) (mul_one _)
  inv_val := Prod.ext (funext fun w => inv_mul_cancel₀ (hf w)) (mul_one _)

@[simp] theorem mkInfUnitR_mul_fst (f : {w : InfinitePlace F // w.IsReal} → ℝ) (hf : ∀ w, f w ≠ 0) (u : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((mkInfUnitR f hf * u : (mixedSpace F)ˣ) : mixedSpace F).1 w = f w * (u : mixedSpace F).1 w := rfl

theorem mkInfUnitR_inv_mul_fst (f : {w : InfinitePlace F // w.IsReal} → ℝ) (hf : ∀ w, f w ≠ 0) (u : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    (((mkInfUnitR f hf)⁻¹ * u : (mixedSpace F)ˣ) : mixedSpace F).1 w = (f w)⁻¹ * (u : mixedSpace F).1 w := rfl

theorem continuous_infR (w : {w : InfinitePlace F // w.IsReal}) : Continuous fun u : (mixedSpace F)ˣ => (u : mixedSpace F).1 w :=
  (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)

/-- The basic box $\{1\le u_w < e\}$. -/
def BC : Set (mixedSpace F)ˣ := {u | ∀ w : {w : InfinitePlace F // w.IsReal}, (u : mixedSpace F).1 w ∈ Ico 1 (Real.exp 1)}

/-- $\{1\le u_w < e^2\}$. -/
def BInf : Set (mixedSpace F)ˣ := {u | ∀ w : {w : InfinitePlace F // w.IsReal}, (u : mixedSpace F).1 w ∈ Ico 1 (Real.exp 2)}

/-- $\{1\le u_w^2 < e^2\}$. -/
def Bsq : Set (mixedSpace F)ˣ := {u | ∀ w : {w : InfinitePlace F // w.IsReal}, (u : mixedSpace F).1 w ^ 2 ∈ Ico 1 (Real.exp 2)}

theorem measurableSet_of_forall_real {P : {w : InfinitePlace F // w.IsReal} → ℝ → Prop} (hP : ∀ w, MeasurableSet {x | P w x}) :
    MeasurableSet {u : (mixedSpace F)ˣ | ∀ w, P w ((u : mixedSpace F).1 w)} := by
  have : {u : (mixedSpace F)ˣ | ∀ w, P w ((u : mixedSpace F).1 w)} =
      ⋂ w, (fun u : (mixedSpace F)ˣ => (u : mixedSpace F).1 w) ⁻¹' {x | P w x} := by ext u; simp
  rw [this]
  exact MeasurableSet.iInter fun w => (hP w).preimage (continuous_infR w).measurable

theorem measurableSet_BC : MeasurableSet (BC (F := F)) :=
  measurableSet_of_forall_real fun _ => measurableSet_Ico

theorem measurableSet_BInf : MeasurableSet (BInf (F := F)) :=
  measurableSet_of_forall_real fun _ => measurableSet_Ico

theorem measurableSet_Bsq : MeasurableSet (Bsq (F := F)) :=
  measurableSet_of_forall_real fun _ => measurableSet_Ico.preimage (measurable_id.pow_const 2)

/-- The sign vector $\pm1$. -/
def sgnV (ε : {w : InfinitePlace F // w.IsReal} → Bool) : {w : InfinitePlace F // w.IsReal} → ℝ := fun w => if ε w then 1 else -1

theorem sgnV_ne_zero (ε : {w : InfinitePlace F // w.IsReal} → Bool) (w : {w : InfinitePlace F // w.IsReal}) : sgnV ε w ≠ 0 := by unfold sgnV; split_ifs <;> norm_num

/-- The vector $e^{\delta_w}$. -/
def expV (δ : {w : InfinitePlace F // w.IsReal} → Bool) : {w : InfinitePlace F // w.IsReal} → ℝ := fun w => if δ w then Real.exp 1 else 1

theorem expV_ne_zero (δ : {w : InfinitePlace F // w.IsReal} → Bool) (w : {w : InfinitePlace F // w.IsReal}) : expV δ w ≠ 0 := by
  unfold expV; split_ifs
  · exact (Real.exp_pos 1).ne'
  · norm_num

/-- **`Bsq` as a disjoint union of sign translates of `BC`.** -/
theorem Bsq_eq_iUnion :
    (Bsq (F := F)) = ⋃ ε : {w : InfinitePlace F // w.IsReal} → Bool, (fun u => (mkInfUnitR (sgnV ε) (sgnV_ne_zero ε))⁻¹ * u) ⁻¹' BC := by
  ext u
  simp only [Bsq, BC, mem_setOf_eq, mem_iUnion, mem_preimage, mkInfUnitR_inv_mul_fst, mem_Ico]
  have he : (1 : ℝ) < Real.exp 1 := by simpa using Real.exp_lt_exp.2 (zero_lt_one' ℝ)
  constructor
  · intro h
    refine ⟨fun w => decide (0 < (u : mixedSpace F).1 w), fun w => ?_⟩
    obtain ⟨h1, h2⟩ := h w
    set x := (u : mixedSpace F).1 w
    have habs : 1 ≤ |x| ∧ |x| < Real.exp 1 := by
      have h1' : (1 : ℝ) ^ 2 ≤ |x| ^ 2 := by rw [sq_abs, one_pow]; exact h1
      have h2' : |x| ^ 2 < Real.exp 1 ^ 2 := by rw [sq_abs, ← Real.exp_nat_mul]; norm_num; exact h2
      exact ⟨(pow_le_pow_iff_left₀ zero_le_one (abs_nonneg x) two_ne_zero).1 h1',
        (pow_lt_pow_iff_left₀ (abs_nonneg x) (Real.exp_pos 1).le two_ne_zero).1 h2'⟩
    by_cases hx : 0 < x
    · have : sgnV (fun w => decide (0 < (u : mixedSpace F).1 w)) w = 1 := by
        simp only [sgnV]; rw [if_pos (decide_eq_true hx)]
      rw [this, inv_one, one_mul]
      rw [abs_of_pos hx] at habs; exact habs
    · have : sgnV (fun w => decide (0 < (u : mixedSpace F).1 w)) w = -1 := by
        simp only [sgnV]; rw [if_neg (by simpa using hx)]
      rw [this]
      rw [abs_of_nonpos (not_lt.1 hx)] at habs
      rw [show (-1 : ℝ)⁻¹ * x = -x by ring]; exact habs
  · rintro ⟨ε, hε⟩ w
    obtain ⟨h1, h2⟩ := hε w
    set x := (u : mixedSpace F).1 w
    have hs : (sgnV ε w)⁻¹ * x = |x| ∨ (sgnV ε w)⁻¹ * x = -|x| := by
      unfold sgnV; split_ifs
      · rw [inv_one, one_mul]; rcases abs_choice x with h | h <;> [left; right] <;> linarith
      · rw [show (-1 : ℝ)⁻¹ * x = -x by ring]; rcases abs_choice x with h | h <;> [right; left] <;> linarith
    have habs : 1 ≤ |x| ∧ |x| < Real.exp 1 := by
      rcases hs with h | h
      · rw [h] at h1 h2; exact ⟨h1, h2⟩
      · rw [h] at h1; exact absurd h1 (by linarith [abs_nonneg x])
    refine ⟨?_, ?_⟩
    · rw [← sq_abs]; nlinarith [habs.1]
    · rw [← sq_abs, show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
      exact pow_lt_pow_left₀ habs.2 (abs_nonneg x) two_ne_zero

/-- **`BInf` as a disjoint union of translates of `BC` by $e^{\delta}$.** -/
theorem BInf_eq_iUnion :
    (BInf (F := F)) = ⋃ δ : {w : InfinitePlace F // w.IsReal} → Bool, (fun u => (mkInfUnitR (expV δ) (expV_ne_zero δ))⁻¹ * u) ⁻¹' BC := by
  ext u
  simp only [BInf, BC, mem_setOf_eq, mem_iUnion, mem_preimage, mkInfUnitR_inv_mul_fst, mem_Ico]
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  constructor
  · intro h
    refine ⟨fun w => decide (Real.exp 1 ≤ (u : mixedSpace F).1 w), fun w => ?_⟩
    obtain ⟨h1, h2⟩ := h w
    set x := (u : mixedSpace F).1 w
    by_cases hx : Real.exp 1 ≤ x
    · have : expV (fun w => decide (Real.exp 1 ≤ (u : mixedSpace F).1 w)) w = Real.exp 1 := by
        simp only [expV]; rw [if_pos (decide_eq_true hx)]
      rw [this]
      refine ⟨?_, ?_⟩
      · rw [le_inv_mul_iff₀ he, mul_one]; exact hx
      · rw [inv_mul_lt_iff₀ he, ← he2]; exact h2
    · have : expV (fun w => decide (Real.exp 1 ≤ (u : mixedSpace F).1 w)) w = 1 := by
        simp only [expV]; rw [if_neg (by simpa using hx)]
      rw [this, inv_one, one_mul]
      exact ⟨h1, not_le.1 hx⟩
  · rintro ⟨δ, hδ⟩ w
    obtain ⟨h1, h2⟩ := hδ w
    set x := (u : mixedSpace F).1 w
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by simpa using Real.add_one_le_exp (1 : ℝ) |>.trans' (by norm_num)
    unfold expV at h1 h2
    split_ifs at h1 h2 with hd
    · rw [le_inv_mul_iff₀ he, mul_one] at h1
      rw [inv_mul_lt_iff₀ he, ← he2] at h2
      exact ⟨he1.trans h1, h2⟩
    · rw [inv_one, one_mul] at h1 h2
      refine ⟨h1, h2.trans_le ?_⟩
      rw [he2]; nlinarith

theorem pairwise_disjoint_translates {ι : Type*} (f : ι → {w : InfinitePlace F // w.IsReal} → ℝ) (hf : ∀ i w, f i w ≠ 0)
    (hdisj : ∀ i j, i ≠ j → ∃ w, ∀ x : ℝ, ¬ ((f i w)⁻¹ * x ∈ Ico 1 (Real.exp 1) ∧ (f j w)⁻¹ * x ∈ Ico 1 (Real.exp 1))) :
    Pairwise (Disjoint on fun i => (fun u => (mkInfUnitR (f i) (hf i))⁻¹ * u) ⁻¹' (BC (F := F))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  obtain ⟨w, hw⟩ := hdisj i j hij
  exact hw _ ⟨hu w, hu' w⟩

theorem omegaInf_iUnion_translates {ι : Type*} [Fintype ι] (f : ι → {w : InfinitePlace F // w.IsReal} → ℝ) (hf : ∀ i w, f i w ≠ 0)
    (hd : Pairwise (Disjoint on fun i => (fun u => (mkInfUnitR (f i) (hf i))⁻¹ * u) ⁻¹' (BC (F := F)))) :
    omegaInf F (⋃ i, (fun u => (mkInfUnitR (f i) (hf i))⁻¹ * u) ⁻¹' BC) = Fintype.card ι * omegaInf F BC := by
  rw [measure_iUnion hd (fun i => measurableSet_BC.preimage (measurable_const_mul _)), tsum_fintype]
  simp_rw [measure_preimage_mul]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

theorem disj_expV (i j : {w : InfinitePlace F // w.IsReal} → Bool) (hij : i ≠ j) :
    ∃ w, ∀ x : ℝ, ¬ ((expV i w)⁻¹ * x ∈ Ico 1 (Real.exp 1) ∧ (expV j w)⁻¹ * x ∈ Ico 1 (Real.exp 1)) := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hij
  refine ⟨w, fun x ⟨h1, h2⟩ => ?_⟩
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  simp only [expV, mem_Ico] at h1 h2
  cases hi : i w <;> cases hj : j w <;> rw [hi] at h1 <;> rw [hj] at h2 <;> simp only [hi, hj, ne_eq,
    not_true_eq_false] at hw <;> simp only [Bool.false_eq_true, ite_false, ite_true, inv_one, one_mul] at h1 h2
  · rw [le_inv_mul_iff₀ he, mul_one] at h2; linarith [h1.2, h2.1]
  · rw [le_inv_mul_iff₀ he, mul_one] at h1; linarith [h1.1, h2.2]

theorem disj_sgnV (i j : {w : InfinitePlace F // w.IsReal} → Bool) (hij : i ≠ j) :
    ∃ w, ∀ x : ℝ, ¬ ((sgnV i w)⁻¹ * x ∈ Ico 1 (Real.exp 1) ∧ (sgnV j w)⁻¹ * x ∈ Ico 1 (Real.exp 1)) := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hij
  refine ⟨w, fun x ⟨h1, h2⟩ => ?_⟩
  simp only [sgnV, mem_Ico] at h1 h2
  cases hi : i w <;> cases hj : j w <;> rw [hi] at h1 <;> rw [hj] at h2 <;> simp only [hi, hj, ne_eq,
    not_true_eq_false] at hw <;> simp only [Bool.false_eq_true, ite_false, ite_true, inv_one, one_mul] at h1 h2
  · rw [show (-1 : ℝ)⁻¹ * x = -x by ring] at h1; linarith [h1.1, h2.1]
  · rw [show (-1 : ℝ)⁻¹ * x = -x by ring] at h2; linarith [h1.1, h2.1]

/-- **$\omega_\infty(\text{Bsq}) = \omega_\infty(\text{BInf})$.** -/
theorem omegaInf_Bsq : omegaInf F (Bsq (F := F)) = omegaInf F (BInf (F := F)) := by
  rw [Bsq_eq_iUnion, BInf_eq_iUnion,
    omegaInf_iUnion_translates _ _ (pairwise_disjoint_translates _ _ disj_sgnV),
    omegaInf_iUnion_translates _ _ (pairwise_disjoint_translates _ _ disj_expV)]

/-! ### Positivity and finiteness -/

section TotallyReal

variable [IsTotallyReal F]

theorem isEmpty_complex : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

theorem isCompact_preimage_box (c d : ℝ) (hc : 0 < c) :
    IsCompact ((Units.val : (mixedSpace F)ˣ → mixedSpace F) ⁻¹'
      {x : mixedSpace F | ∀ w : {w : InfinitePlace F // w.IsReal}, x.1 w ∈ Icc c d}) := by
  have := isEmpty_complex (F := F)
  have hA : IsCompact {x : mixedSpace F | ∀ w : {w : InfinitePlace F // w.IsReal}, x.1 w ∈ Icc c d} := by
    have : {x : mixedSpace F | ∀ w : {w : InfinitePlace F // w.IsReal}, x.1 w ∈ Icc c d} =
        (Set.univ.pi fun _ => Icc c d) ×ˢ (Set.univ : Set ({w : InfinitePlace F // w.IsComplex} → ℂ)) := by
      ext x; simp only [mem_setOf_eq, mem_prod, mem_univ_pi, mem_univ, and_true]
    rw [this]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_univ
  rw [isOpenEmbedding_val_mixedSpace.isEmbedding.isCompact_preimage_iff]
  · exact hA
  intro x hx
  have hu : IsUnit x := by
    rw [Prod.isUnit_iff]
    refine ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (by linarith [(hx w).1]), ?_⟩
    exact Pi.isUnit_iff.2 fun w => isEmptyElim w
  exact ⟨hu.unit, rfl⟩

theorem omegaInf_BInf_ne_top : omegaInf F (BInf (F := F)) ≠ ∞ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (isCompact_preimage_box (F := F) 1 (Real.exp 2) one_pos).measure_lt_top)
  intro u hu w
  exact ⟨(hu w).1, (hu w).2.le⟩

theorem omegaInf_BInf_ne_zero : omegaInf F (BInf (F := F)) ≠ 0 := by
  have := isEmpty_complex (F := F)
  set U : Set (mixedSpace F)ˣ := {u | ∀ w : {w : InfinitePlace F // w.IsReal}, (u : mixedSpace F).1 w ∈ Ioo 1 (Real.exp 2)}
  have hUo : IsOpen U := by
    have : U = ⋂ w, (fun u : (mixedSpace F)ˣ => (u : mixedSpace F).1 w) ⁻¹' Ioo 1 (Real.exp 2) := by ext u; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_Ioo.preimage (continuous_infR w)
  have he2 : (3 / 2 : ℝ) < Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hUne : U.Nonempty := ⟨mkInfUnitR (fun _ => 3 / 2) (fun _ => by norm_num), fun w =>
    ⟨show (1 : ℝ) < 3 / 2 by norm_num, show (3 / 2 : ℝ) < Real.exp 2 from he2⟩⟩
  have hsub : U ⊆ BInf := fun u hu w => ⟨(hu w).1.le, (hu w).2⟩
  have hpos : 0 < omegaInf F U := hUo.measure_pos (omegaInf F) hUne
  exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'

/-- $\{t\in\mathbb A^\times : t_\infty\in\text{BInf},\ t_f\in\hat{\mathcal O}^\times\}$. -/
def Bset : Set (Adeles F)ˣ := idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ))

theorem measurableSet_Bset : MeasurableSet (Bset (F := F)) :=
  (measurableSet_BInf.prod (isOpen_OHatUnits (F := F)).measurableSet).preimage
    (idelesEquiv F).continuous.measurable

theorem infPart_pow (u : (Adeles F)ˣ) (n : ℕ) : infPart (u ^ n) = infPart u ^ n := map_pow (Units.map _) u n
theorem finPart_pow (u : (Adeles F)ˣ) (n : ℕ) : finPart (u ^ n) = finPart u ^ n := map_pow (Units.map _) u n

/-- **The centre fibre**: for $t\gg0$ with $t_f\in\hat{\mathcal O}^\times$,
$\mathrm{tamIdeles}\{u : u_f\in\hat{\mathcal O}^\times,\ u^2t\in\text{Bset}\} = \omega_\infty(\text{BInf})\cdot\mu_f(\hat{\mathcal O}^\times)$. -/
theorem tamIdeles_sq_mem_Bset (t : (Adeles F)ˣ) (ht : ∀ w, 0 < (t : Adeles F).1.1 w)
    (htf : finPart t ∈ OHatUnits F) :
    tamIdeles F {u | finPart u ∈ OHatUnits F ∧ u ^ 2 * t ∈ Bset} =
      omegaInf F BInf * muFinUnits F (OHatUnits F) := by
  set ρ := mkInfUnitR (fun w => Real.sqrt ((t : Adeles F).1.1 w)) (fun w => (Real.sqrt_pos.2 (ht w)).ne')
  have hset : {u : (Adeles F)ˣ | finPart u ∈ OHatUnits F ∧ u ^ 2 * t ∈ Bset} =
      idelesEquiv F ⁻¹' (((fun x => ρ * x) ⁻¹' Bsq) ×ˢ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ)) := by
    ext u
    simp only [mem_setOf_eq, Bset, mem_preimage, mem_prod, idelesEquiv_apply, SetLike.mem_coe]
    rw [infPart_mul, infPart_pow, finPart_mul, finPart_pow]
    have hf : finPart u ∈ OHatUnits F → finPart u ^ 2 * finPart t ∈ OHatUnits F := fun h =>
      (OHatUnits F).mul_mem ((OHatUnits F).pow_mem h 2) htf
    have hinf : infPart u ^ 2 * infPart t ∈ BInf ↔ ρ * infPart u ∈ Bsq := by
      simp only [BInf, Bsq, mem_setOf_eq, mkInfUnitR_mul_fst]
      refine forall_congr' fun w => ?_
      have e : ((infPart u ^ 2 * infPart t : (mixedSpace F)ˣ) : mixedSpace F).1 w =
          (Real.sqrt ((t : Adeles F).1.1 w) * (infPart u : mixedSpace F).1 w) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (ht w).le]
        show ((u : Adeles F).1.1 w) ^ 2 * (t : Adeles F).1.1 w = (t : Adeles F).1.1 w * ((u : Adeles F).1.1 w) ^ 2
        ring
      rw [e, mkInfUnitR_mul_fst]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨hinf.1 h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, hinf.2 h2, hf h1⟩
  rw [hset, tamIdeles_prod, measure_preimage_mul, omegaInf_Bsq]

end TotallyReal

end

end QuadFormsKB.Tamagawa.Measure.Weil
