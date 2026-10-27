import QuadFormsKB.Tamagawa.Measure.Weil.SL2Measure

/-!
# Siegel's mean value theorem for $\mathrm{SL}_2$ and finiteness of $\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F))$

$F$ any number field, $\mu_T$ the fibration (Tamagawa) measure on $\mathrm{SL}_2(\mathbb A_F)$ (`SL2Measure.lean`),
$\mathrm{SL}_2(F)$ acting on the right ($G_{\mathbb A}/G_k$, AAG §2.4).

* **`lintegral_tsum_mulVec_eq`** (Siegel's mean value theorem, the continuous unfolding over the orbit
  $\mathrm{SL}_2(F)/N(F)\cong F^2\setminus 0$): for every fundamental domain $D$ of $G_{\mathbb A}/G_k$ and every
  measurable $f : \mathbb A_F^2\to[0,\infty]$,
  $$\int_D\sum_{\xi\in F^2\setminus0} f(g\xi)\,d\mu_T(g) = \int_{\mathbb A_F^2} f(y)\,dy .$$
  *Proof:* $\mathrm{SL}_2(F)$ is transitive on $F^2\setminus 0$ with stabilizer $N(F)$ at $e_1$; the orbit unfolding of
  Siegel's finiteness criterion reduces the left side to $\int_E f(ge_1)\,d\mu_T$ over an exact fundamental domain $E$
  of $N(F)$, and in the coordinates $g = s(y)n(x)$ one can take $E = \{x\in D_{\mathbb A}\}$ ($D_{\mathbb A}$ the
  fundamental domain of $F$ in $\mathbb A_F$, volume $1$),
  so the integral is $\operatorname{vol}(\mathbb A_F/F)\int_P f\,dy = \int f\,dy$ ($P$ conull).
* **Finiteness**: by adelic Minkowski there is a compact $C\subseteq\mathbb A_F^2$ with
  $\sum_{\xi\ne0}1_C(g\xi)\ge1$ for all $g$, so $\mu_T(D)\le\operatorname{vol}(C) < \infty$ (`muT_fundDomain_lt_top`); and
  $\mu_T(D) > 0$ (`muT_fundDomain_ne_zero`). Hence **`covolume_muT_lt_top`** and, for every Haar measure $\mu$,
  **`haar_fundDomain_lt_top`**: $\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)) < \infty$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open QuadFormsKB.WeilRep
open scoped ENNReal NNReal Pointwise Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### $F^2\setminus 0$ as an $\mathrm{SL}_2(F)$-set -/

variable (F) in
/-- The nonzero vectors of $F^2$. -/
def NZVec : Type := {ξ : Fin 2 → F // ξ ≠ 0}

instance : Countable (NZVec F) := inferInstanceAs (Countable {ξ : Fin 2 → F // ξ ≠ 0})

theorem mulVec_ne_zero (γ : SL(2, F)) {ξ : Fin 2 → F} (hξ : ξ ≠ 0) :
    Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) ξ ≠ 0 := by
  intro h
  apply hξ
  have : Matrix.mulVec ((γ⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      (Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

instance : MulAction (SL(2, F)) (NZVec F) where
  smul γ ξ := ⟨Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) ξ.1, mulVec_ne_zero γ ξ.2⟩
  one_smul ξ := Subtype.ext (by
    show Matrix.mulVec ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ξ.1 = ξ.1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])
  mul_smul γ δ ξ := Subtype.ext (by
    show Matrix.mulVec ((γ * δ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ξ.1 =
      Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) (Matrix.mulVec (δ : Matrix (Fin 2) (Fin 2) F) ξ.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec])

theorem NZVec.smul_val (γ : SL(2, F)) (ξ : NZVec F) :
    (γ • ξ).1 = Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) ξ.1 := rfl

variable (F) in
/-- $e_1 = (1, 0)$. -/
def e1 : NZVec F := ⟨![1, 0], fun h => by simpa using congrFun h 0⟩

/-- The section over $F$: $s(\xi)e_1 = \xi$ (the local formula `locB`, `locD` with $B = F$). -/
def secF (ξ : NZVec F) : SL(2, F) :=
  ⟨!![ξ.1 0, locB Set.univ (ξ.1 0) (ξ.1 1); ξ.1 1, locD Set.univ (ξ.1 0) (ξ.1 1)], by
    rw [Matrix.det_fin_two_of]
    refine locB_det (Set.mem_univ _) ?_
    by_contra h
    push Not at h
    exact ξ.2 (funext fun i => by fin_cases i <;> simp [h.1, h.2])⟩

/-- **$\mathrm{SL}_2(F)$ is transitive on $F^2\setminus 0$.** -/
theorem secF_smul_e1 (ξ : NZVec F) : secF ξ • e1 F = ξ := by
  refine Subtype.ext (funext fun i => ?_)
  rw [NZVec.smul_val]
  fin_cases i <;> simp [secF, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- An element of $\mathrm{SL}_2(F)$ fixing $e_1$ is $n(b)$. -/
theorem eq_nMat_of_smul_e1 {γ : SL(2, F)} (h : γ • e1 F = e1 F) :
    γ = nMat ((γ : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h' := congrArg Subtype.val h
  rw [NZVec.smul_val] at h'
  have h00 : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrFun h' 0; simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrFun h' 1; simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = 1 := γ.2
  rw [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · rfl
  · exact h10
  · exact hdet

theorem nMat_smul_e1 (b : F) : nMat b • e1 F = e1 F := by
  refine Subtype.ext (funext fun i => ?_)
  rw [NZVec.smul_val]
  fin_cases i <;> simp [nMat, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slEmb_nMat (b : F) : slEmb F (nMat b) = nA (diag F b) := by
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  show diag F ((nMat b : Matrix (Fin 2) (Fin 2) F) i j) = (nA (diag F b) : Matrix (Fin 2) (Fin 2) (Adeles F)) i j
  fin_cases i <;> fin_cases j <;> simp [nMat, nA, ← diagRing_apply]

theorem nA_neg (x : Adeles F) : (nA x)⁻¹ = nA (-x) := by
  rw [inv_eq_iff_mul_eq_one, nA_add, add_neg_cancel]
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

/-! ### The orbit integrand -/

theorem diagVec_mulVec (γ : SL(2, F)) (ξ : Fin 2 → F) :
    diagVec F (Fin 2) (Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) F) ξ) =
      Matrix.mulVec (slEmb F γ : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ) := by
  funext i
  simp only [diagVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, slEmb_apply, ← diagRing_apply,
    map_add, map_mul]

theorem mulVec_diagVec_e1 (g : SL2A F) :
    Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) (e1 F).1) = col g := by
  funext i
  simp [e1, col, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← diagRing_apply]

/-- The equivariant family $\Phi(\xi, g) = f(g\xi)$. -/
def orbitFn (f : AdeleSpace F (Fin 2) → ℝ≥0∞) (ξ : NZVec F) (g : SL2A F) : ℝ≥0∞ :=
  f (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ.1))

theorem orbitFn_smul (f : AdeleSpace F (Fin 2) → ℝ≥0∞) (γ : SL(2, F)) (ξ : NZVec F) (g : SL2A F) :
    orbitFn f (γ • ξ) (γ • g) = orbitFn f ξ g := by
  unfold orbitFn
  rw [NZVec.smul_val, diagVec_mulVec, slRight_smul_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul (slEmb F γ)⁻¹, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

/-! ### The exact fundamental domain of $N(F)$ -/

variable (F) in
/-- $E = \{s(y)n(x) : x\in D_{\mathbb A}\}$, an exact fundamental domain for the stabilizer $N(F)$ of $e_1$. -/
def stabDom : Set (SL2A F) := toCoord F ⁻¹' (Set.univ ×ˢ fundDom F)

theorem measurableSet_stabDom : MeasurableSet (stabDom F) :=
  measurable_toCoord (MeasurableSet.univ.prod measurableSet_fundDom)

theorem stab_smul_eq (s : MulAction.stabilizer (SL(2, F)) (e1 F)) (g : SL2A F) :
    s • g = g * nA (-diag F (((s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1)) := by
  show g * (slEmb F (s : SL(2, F)))⁻¹ = _
  rw [eq_nMat_of_smul_e1 s.2, slEmb_nMat, nA_neg]
  rfl

theorem existsUnique_stab_smul_mem_stabDom (g : SL2A F) :
    ∃! s : MulAction.stabilizer (SL(2, F)) (e1 F), s • g ∈ stabDom F := by
  have hmem : ∀ s : MulAction.stabilizer (SL(2, F)) (e1 F), s • g ∈ stabDom F ↔
      (⟨diag F (-((s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1), _, rfl⟩ : diagSub F) +ᵥ (toCoord F g).2 ∈
        fundDom F := by
    intro s
    rw [stab_smul_eq, stabDom, Set.mem_preimage, toCoord_mul_nA, Set.mem_prod]
    simp only [Set.mem_univ, true_and]
    show _ ↔ diag F (-(((s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1)) + (toCoord F g).2 ∈ fundDom F
    rw [map_neg, add_comm]
  obtain ⟨⟨_, η, rfl⟩, hη, huniq⟩ := existsUnique_vadd_mem_fundDom (toCoord F g).2
  have hs : nMat (-η) ∈ MulAction.stabilizer (SL(2, F)) (e1 F) := nMat_smul_e1 _
  refine ⟨⟨nMat (-η), hs⟩, (hmem _).mpr ?_, fun s hs' => ?_⟩
  · convert hη using 3
    simp [nMat]
  · have h1 := huniq _ ((hmem s).mp hs')
    have h2 : -((s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = η := diag_injective (congrArg Subtype.val h1)
    apply Subtype.ext
    rw [eq_nMat_of_smul_e1 s.2]
    congr 1
    rw [← h2, neg_neg]

/-! ### Siegel's mean value theorem -/

theorem col_ofCoord (p : primSet F × Adeles F) : col (ofCoord F p) = p.1 := by
  rw [ofCoord, col_mul_nA, col_sec p.1.2]

/-- $\int_E f(ge_1)\,d\mu_T = \int_{\mathbb A_F^2} f\,dy$ (coordinates, $\operatorname{vol}(D_{\mathbb A}) = 1$, $P$ conull). -/
theorem setLIntegral_stabDom (f : AdeleSpace F (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g in stabDom F, f (col g) ∂muT F = ∫⁻ y, f y ∂muAddVec F (Fin 2) := by
  rw [← lintegral_indicator measurableSet_stabDom, muT,
    lintegral_map ((show Measurable fun g => f (col g) from hf.comp measurable_col).indicator
      measurableSet_stabDom) measurable_ofCoord]
  have hpt : ∀ p : primSet F × Adeles F, (stabDom F).indicator (fun g => f (col g)) (ofCoord F p) =
      f p.1 * (fundDom F).indicator 1 p.2 := by
    intro p
    by_cases hp : p.2 ∈ fundDom F
    · have : ofCoord F p ∈ stabDom F := by
        show toCoord F (ofCoord F p) ∈ (Set.univ ×ˢ fundDom F : Set (primSet F × Adeles F))
        rw [toCoord_ofCoord]; exact ⟨Set.mem_univ p.1, hp⟩
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hp, Pi.one_apply, mul_one, col_ofCoord]
    · have : ofCoord F p ∉ stabDom F := by
        intro h
        have h' : toCoord F (ofCoord F p) ∈ Set.univ ×ˢ fundDom F := h
        rw [toCoord_ofCoord] at h'
        exact hp h'.2
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hp, mul_zero]
  simp_rw [hpt]
  rw [lintegral_prod_mul (f := fun y : primSet F => f y) (g := (fundDom F).indicator 1)
    (hf.comp measurable_subtype_coe).aemeasurable
    (measurable_one.indicator measurableSet_fundDom).aemeasurable,
    lintegral_indicator_one measurableSet_fundDom, muAdd_fundDom, mul_one, dyP,
    lintegral_subtype_comap measurableSet_primSet,
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp muAddVec_compl_primSet |>.mono
      fun y hy => by simpa using hy)]

/-- **Siegel's mean value theorem for $\mathrm{SL}_2$ over a number field.** For every fundamental domain $D$ of
$\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)$ (right action) and every measurable $f : \mathbb A_F^2\to[0,\infty]$,
$\int_D\sum_{\xi\in F^2\setminus0} f(g\xi)\,d\mu_T(g) = \int_{\mathbb A_F^2} f\,dy$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26 (unfolding) and Thm 2.4.3 [unverified page]"]
theorem lintegral_tsum_mulVec_eq {D : Set (SL2A F)} (hD : IsFundamentalDomain (SL(2, F)) D (muT F))
    (f : AdeleSpace F (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g in D, ∑' ξ : NZVec F, f (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ.1))
      ∂muT F = ∫⁻ y, f y ∂muAddVec F (Fin 2) := by
  have horb : ∀ ξ : NZVec F, ξ ∈ MulAction.orbit (SL(2, F)) (e1 F) := fun ξ => ⟨secF ξ, secF_smul_e1 ξ⟩
  let e : MulAction.orbit (SL(2, F)) (e1 F) ≃ NZVec F := Equiv.subtypeUnivEquiv horb
  have hmeas : Measurable (orbitFn f (e1 F)) := by
    have : orbitFn f (e1 F) = fun g => f (col g) := funext fun g => by rw [orbitFn, mulVec_diagVec_e1]
    rw [this]; exact hf.comp measurable_col
  calc ∫⁻ g in D, ∑' ξ : NZVec F, f (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F))
        (diagVec F (Fin 2) ξ.1)) ∂muT F
      = ∫⁻ g in D, ∑' ξ : MulAction.orbit (SL(2, F)) (e1 F), orbitFn f ξ g ∂muT F :=
        lintegral_congr fun g => (e.tsum_eq (fun ξ => orbitFn f ξ g)).symm
    _ = ∫⁻ g in stabDom F, orbitFn f (e1 F) g ∂muT F :=
        lintegral_orbit_unfold (e1 F) (orbitFn f) (orbitFn_smul f) hmeas hD measurableSet_stabDom
          existsUnique_stab_smul_mem_stabDom
    _ = ∫⁻ g in stabDom F, f (col g) ∂muT F := by
        refine lintegral_congr fun g => ?_
        rw [orbitFn, mulVec_diagVec_e1]
    _ = ∫⁻ y, f y ∂muAddVec F (Fin 2) := setLIntegral_stabDom f hf

/-! ### Finiteness -/

/-- **Finiteness** (Siegel's argument with adelic Minkowski): $\mu_T(D) < \infty$ for every fundamental domain $D$ of
$\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) finite)"]
theorem muT_fundDomain_lt_top {D : Set (SL2A F)} (hD : IsFundamentalDomain (SL(2, F)) D (muT F)) :
    muT F D < ∞ := by
  obtain ⟨K, hK, hKmem⟩ := exists_isCompact_forall_SL_mulVec_mem (F := F) (ι := Fin 2)
  have hf : Measurable (K.indicator (1 : AdeleSpace F (Fin 2) → ℝ≥0∞)) :=
    measurable_one.indicator hK.isClosed.measurableSet
  have hone : ∀ g : SL2A F, (1 : ℝ≥0∞) ≤ ∑' ξ : NZVec F, K.indicator 1
      (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ.1)) := by
    intro g
    obtain ⟨ξ, hξ, hmem⟩ := hKmem g
    calc (1 : ℝ≥0∞) = K.indicator 1 (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F))
          (diagVec F (Fin 2) (⟨ξ, hξ⟩ : NZVec F).1)) := by rw [Set.indicator_of_mem hmem, Pi.one_apply]
      _ ≤ _ := ENNReal.le_tsum (f := fun ξ : NZVec F => K.indicator 1
          (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ.1))) ⟨ξ, hξ⟩
  calc muT F D = ∫⁻ _ in D, 1 ∂muT F := by simp
    _ ≤ ∫⁻ g in D, ∑' ξ : NZVec F, K.indicator 1
          (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (Adeles F)) (diagVec F (Fin 2) ξ.1)) ∂muT F :=
        lintegral_mono fun g => hone g
    _ = muAddVec F (Fin 2) K := by
        rw [lintegral_tsum_mulVec_eq hD _ hf, lintegral_indicator_one hK.isClosed.measurableSet]
    _ < ∞ := hK.measure_lt_top

/-- $\mu_T(D) > 0$ for every fundamental domain $D$. -/
theorem muT_fundDomain_ne_zero {D : Set (SL2A F)} (hD : IsFundamentalDomain (SL(2, F)) D (muT F)) :
    muT F D ≠ 0 := by
  intro h0
  have h := lintegral_tsum_mulVec_eq hD (fun _ => 1) measurable_const
  rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure, lintegral_const, one_mul] at h
  exact (NeZero.ne (muAddVec F (Fin 2) Set.univ)) h.symm

/-- **$\operatorname{vol}_{\mu_T}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F))$ is finite and positive.** -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) := vol(G_𝔸/G_k))"]
theorem covolume_muT_lt_top :
    covolume (SL(2, F)) (SL2A F) (muT F) < ∞ ∧ covolume (SL(2, F)) (SL2A F) (muT F) ≠ 0 := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  have hFD : IsFundamentalDomain (SL(2, F)) D (muT F) := IsFundamentalDomain.mk' hD.nullMeasurableSet h
  rw [hFD.covolume_eq_volume]
  exact ⟨muT_fundDomain_lt_top hFD, muT_fundDomain_ne_zero hFD⟩

/-- **Finiteness of $\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F))$ for every Haar measure.** -/
@[kb "weil1982" "§2.4, p. 23"]
theorem haar_fundDomain_lt_top (μ : Measure (SL2A F)) [μ.IsHaarMeasure] {D : Set (SL2A F)}
    (hD : IsFundamentalDomain (SL(2, F)) D μ) : μ D < ∞ ∧ μ D ≠ 0 := by
  have hT := haar_slNbhd_pos_lt_top (muT F)
  have hμ := haar_slNbhd_pos_lt_top μ
  have heq : μ = (μ (slNbhd F) / muT F (slNbhd F)) • muT F :=
    measure_eq_div_smul (μ' := μ) (ν' := muT F) (s := slNbhd F) hT.1 hT.2
  set k := μ (slNbhd F) / muT F (slNbhd F)
  have hk0 : k ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hμ.1, hT.2⟩
  have hktop : k ≠ ∞ := ENNReal.div_ne_top hμ.2 hT.1
  have hD' : IsFundamentalDomain (SL(2, F)) D (muT F) := by
    refine hD.mono ?_
    rw [heq]
    exact Measure.absolutelyContinuous_smul hk0
  rw [heq, Measure.smul_apply, smul_eq_mul]
  exact ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hktop) (muT_fundDomain_lt_top hD'),
    mul_ne_zero hk0 (muT_fundDomain_ne_zero hD')⟩

end

end QuadFormsKB.Tamagawa.Measure.Weil
