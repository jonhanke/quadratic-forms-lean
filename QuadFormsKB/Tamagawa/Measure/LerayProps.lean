import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayMeasure

/-!
# Volumes of the Leray measures: local densities and the cone factor

* `lerayMeasure_latL`: for $\rho \in \mathcal O_v\smallsetminus 0$, $\sigma_\rho(L_v) = \beta_v(L,\rho)\,\nu(\mathcal O_v)^{n-1}$
  (**the Leray volume of the lattice points of the sphere $T(\rho)_v$ is the local density**).
* `lerayMeasure_prim`: $\sigma_0(L_v\smallsetminus\mathfrak p_vL_v) = \nu(\mathcal O_v)^{n-1}\gamma_v(Q)$
  (**the Leray volume of the primitive vectors of the cone**; $\gamma_v$ = `LerayCone.coneFactor`).
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

lemma latL_eq_cosetP : latL v n = cosetP v 0 0 := by
  ext x; simp [latL, cosetP]

lemma pL_eq_cosetP : pL v (n := n) = cosetP v 0 1 := by
  ext x; simp [pL, cosetP]

lemma cosetP_anti (y : Fin n → Fv) {i j : ℕ} (h : i ≤ j) : cosetP v y j ⊆ cosetP v y i :=
  fun x hx l => (hx l).trans (by rw [exp_le_exp]; omega)

lemma latL_diff_mem_Cz (j : ℕ) : latL v n \ cosetP v 0 j ∈ Cz v n := by
  have hL : IsCompact (latL v n) := by
    rw [latL_eq_cosetP, cosetP_eq]; exact isCompact_closedBall _ _
  have hLo : IsOpen (latL v n) := by rw [latL_eq_cosetP]; exact isOpen_cosetP v 0 0
  exact ⟨hL.diff (isOpen_cosetP v 0 j), hLo.sdiff (by rw [cosetP_eq]; exact Metric.isClosed_closedBall), fun h => h.2 (mem_cosetP_self v 0 j)⟩

/-- On $\mathfrak p^jL$ the form is tiny: $|Q(x)| \le q^{-2j}$. -/
lemma valued_qv_le (Q : QuadForm 𝔬 n) (j : ℕ) {x : Fin n → Fv} (hx : x ∈ cosetP v 0 j) :
    Valued.v (Qv v Q x) ≤ exp (-(2 * j : ℤ)) := by
  set c : Fv := HN.ϖ v ^ j with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (HN.ϖ_ne_zero v)
  have hvc : Valued.v c = exp (-(j : ℤ)) := by
    have := valued_ϖ_zpow v (j : ℤ)
    simpa [hc, zpow_natCast] using this
  set y : Fin n → Fv := fun i => x i / c with hy
  have hxy : x = c • y := by
    funext i; simp only [hy, Pi.smul_apply, smul_eq_mul]; field_simp
  have hyL : y ∈ latL v n := by
    intro i
    simp only [hy, map_div₀, hvc]
    have := hx i
    simp only [Pi.zero_apply, sub_zero] at this
    rw [div_le_iff₀ (by simp)]
    simpa using this
  have h1 := valued_evalIn_le_one v Q hyL
  rw [hxy]
  show Valued.v (Qv v Q (c • y)) ≤ _
  rw [qv_smul, map_mul, map_pow, hvc]
  calc exp (-(j : ℤ)) ^ 2 * Valued.v (Qv v Q y) ≤ exp (-(j : ℤ)) ^ 2 * 1 := by gcongr
    _ = exp (-(2 * j : ℤ)) := by rw [mul_one, pow_two, ← exp_add]; congr 1; ring

/-- **Far from the origin the shell $Q \in \rho + \mathfrak p^k$ is empty** ($\rho \ne 0$). -/
lemma exists_far (Q : QuadForm 𝔬 n) {ρ : Fv} (hρ : ρ ≠ 0) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ k ≥ J, ∀ x ∈ cosetP v 0 j, Qv v Q x ∉ shell v ρ k := by
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v ρ := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hρ
  set m : ℤ := WithZero.log (Valued.v ρ) with hm
  have hvm : Valued.v ρ = exp m := (exp_log (by simpa using hpos.ne')).symm
  refine ⟨(-m).toNat + 1, fun j hj k hk x hx hxs => ?_⟩
  have h1 : Valued.v (Qv v Q x) ≤ exp (-(2 * j : ℤ)) := valued_qv_le v Q j hx
  have h2 : Valued.v (Qv v Q x - ρ) ≤ exp (-(k : ℤ)) := hxs
  have h3 : Valued.v ρ ≤ max (Valued.v (Qv v Q x)) (Valued.v (Qv v Q x - ρ)) := by
    have : ρ = Qv v Q x - (Qv v Q x - ρ) := by ring
    conv_lhs => rw [this]
    rw [sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg]
  have hjm : -(j : ℤ) < m := by omega
  have hkm : -(k : ℤ) < m := by omega
  have h4 : exp (-(2 * j : ℤ)) < exp m := by rw [exp_lt_exp]; omega
  have h5 : exp (-(k : ℤ)) < exp m := by rw [exp_lt_exp]; exact hkm
  rw [hvm] at h3
  have : max (Valued.v (Qv v Q x)) (Valued.v (Qv v Q x - ρ)) < exp m :=
    max_lt (lt_of_le_of_lt h1 h4) (lt_of_le_of_lt h2 h5)
  exact absurd h3 (not_le.mpr this)

lemma latL_diff_zero_eq_iUnion : latL v n \ {0} = ⋃ j : ℕ, (latL v n \ cosetP v 0 j) := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hx0⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (x i) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hi
    set m : ℤ := WithZero.log (Valued.v (x i)) with hm
    have hvm : Valued.v (x i) = exp m := (exp_log (by simpa using hpos.ne')).symm
    refine ⟨(-m).toNat + 1, hx, fun hP => ?_⟩
    have := hP i
    simp only [Pi.zero_apply, sub_zero, hvm] at this
    rw [exp_le_exp] at this
    omega
  · rintro ⟨j, hx, hP⟩
    exact ⟨hx, fun h0 => hP (by rw [h0]; exact mem_cosetP_self v 0 j)⟩

/-- **Measures killing $\{0\}$ are determined by their values on $C_0$.** -/
theorem measure_ext_Cz {μ₁ μ₂ : Measure (Fin n → Fv)} (h₁ : μ₁ {0} = 0) (h₂ : μ₂ {0} = 0)
    (hfin : ∀ U ∈ Cz v n, μ₁ U ≠ ⊤) (h : ∀ U ∈ Cz v n, μ₁ U = μ₂ U) : μ₁ = μ₂ := by
  obtain ⟨T₀, s, hT0c, -, hmem, hUeq⟩ := exists_countable_union_Cz v
    (isClosed_singleton (x := (0 : Fin n → Fv))).isOpen_compl (by simp)
  set T : Set (Set (Fin n → Fv)) := insert {0} ((fun x => cosetP v x (s x)) '' T₀) with hT
  have hTmem : ∀ t ∈ T, t = {0} ∨ t ∈ Cz v n := by
    intro t ht
    rcases ht with rfl | ⟨x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (hmem x hx)
  refine Measure.ext_of_generateFrom_of_cover (S := Cz v n) (T := T) (measurableSpace_eq_generateFrom_Cz v)
    ((hT0c.image _).insert _) (isSetRing_Cz v).isSetSemiring.isPiSystem ?_ ?_ ?_ ?_
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · exact ⟨{0}, Set.mem_insert _ _, by simp [hx]⟩
    · have : x ∈ ({0}ᶜ : Set (Fin n → Fv)) := hx
      rw [hUeq] at this
      simp only [Set.mem_iUnion] at this
      obtain ⟨y, hy, hxy⟩ := this
      exact ⟨_, Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩, hxy⟩
  · intro t ht
    rcases hTmem t ht with rfl | hU
    · rw [h₁]; exact ENNReal.zero_ne_top
    · exact hfin t hU
  · intro t ht u hu
    rcases hTmem t ht with rfl | hU
    · have : u ∩ {0} = ∅ := Set.inter_singleton_eq_empty.mpr hu.2.2
      rw [this]; simp
    · exact h _ ((isSetRing_Cz v).inter_mem hu hU)
  · intro t ht
    rcases hTmem t ht with rfl | hU
    · rw [h₁, h₂]
    · exact h t hU

section Props

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure] (Q : QuadForm (v.adicCompletionIntegers F) n)
  (hQ : Q.Nondegenerate)

lemma lerayThick_diff_of_far {A : Set (Fin n → Fv)} (hA : MeasurableSet A) (ρ : Fv) (k j : ℕ)
    (hfar : ∀ x ∈ cosetP v 0 j, Qv v Q x ∉ shell v ρ k) :
    lerayThick ν (Qv v Q) (shell v ρ k) (A \ cosetP v 0 j) = lerayThick ν (Qv v Q) (shell v ρ k) A := by
  rw [lerayThick_apply ν _ _ (hA.diff (measurableSet_cosetP v 0 j)), lerayThick_apply ν _ _ hA]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage]
  constructor
  · rintro ⟨⟨hxA, -⟩, hx⟩; exact ⟨hxA, hx⟩
  · rintro ⟨hxA, hx⟩
    exact ⟨⟨hxA, fun hP => hfar x hP hx⟩, hx⟩

/-- **The Leray volume of the lattice points of the sphere is the local density**:
$\sigma_\rho(L_v) = \beta_v(L,\rho)\,\nu(\mathcal O_v)^{n-1}$ for $\rho \in \mathcal O_v\smallsetminus0$. -/
@[kb "weil1982" "§2.4, §4.3 p. 89 (Leray volume of lattice points = local density) [unverified]"]
theorem lerayMeasure_latL (hn : 1 ≤ n) (ρ : v.adicCompletionIntegers F) (hρ : ρ ≠ 0) :
    lerayMeasure v ν Q hQ (ρ : Fv) (latL v n) =
      ENNReal.ofReal (DVR.localDensity Q (NF.π v) ρ * ν.real (latticeV v 0) ^ (n - 1)) := by
  set c := ENNReal.ofReal (DVR.localDensity Q (NF.π v) ρ * ν.real (latticeV v 0) ^ (n - 1)) with hc
  have hρ' : (ρ : Fv) ≠ 0 := by simpa using hρ
  obtain ⟨J, hJ⟩ := exists_far v Q hρ'
  have hmono : Monotone fun j : ℕ => latL v n \ cosetP v 0 j :=
    fun i j hij => Set.diff_subset_diff_right (cosetP_anti v 0 hij)
  have hval : ∀ j ≥ J, lerayMeasure v ν Q hQ (ρ : Fv) (latL v n \ cosetP v 0 j) = c := by
    intro j hj
    have hmeasL : MeasurableSet (latL v n) := measurableSet_latL v
    obtain ⟨k, hk1, hk2, hk3⟩ := ((lerayMeasure_eventually v ν Q hQ (ρ : Fv) (latL_diff_mem_Cz v j)).and
      ((lerayThick_latL_eq_localDensity v ν Q hQ hn ρ hρ).and (Filter.eventually_ge_atTop J))).exists
    rw [← hk1, lerayThick_diff_of_far v ν Q hmeasL _ k j (hJ j hj k hk3), hk2]
  have hz : lerayMeasure v ν Q hQ (ρ : Fv) (latL v n) = lerayMeasure v ν Q hQ (ρ : Fv) (latL v n \ {0}) :=
    (measure_diff_null (lerayMeasure_singleton_zero v ν Q hQ _)).symm
  rw [hz, latL_diff_zero_eq_iUnion, hmono.measure_iUnion]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    exact (measure_mono (hmono (le_max_left j J))).trans (hval _ (le_max_right _ _)).le
  · exact (hval J le_rfl).symm.le.trans (le_iSup (fun j => lerayMeasure v ν Q hQ (ρ : Fv) (latL v n \ cosetP v 0 j)) J)

/-- **The Leray volume of the primitive null cone** ($\rho = 0$): $\sigma_0(L_v\smallsetminus\mathfrak p_vL_v) =
\nu(\mathcal O_v)^{n-1}\gamma_v(Q)$, $\gamma_v$ the cone factor of `LerayCone`. -/
@[kb "weil1982" "§2.4 (Leray measure on the null cone) [unverified]"]
theorem lerayMeasure_prim (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 2 ≤ n) :
    lerayMeasure v ν (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) 0 (latL v n \ cosetP v 0 1) =
      ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * coneFactor Q v) := by
  obtain ⟨j, hj1, hj2⟩ := ((lerayMeasure_eventually v ν (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) 0
    (latL_diff_mem_Cz v 1)).and (lerayThick_prim_eq_coneFactor v ν Q hQ hn)).exists
  rw [← hj1, ← pL_eq_cosetP]
  simpa using hj2

lemma preimage_mulVec_mem_Cz (g : GL (Fin n) Fv) {U : Set (Fin n → Fv)} (hU : U ∈ Cz v n) :
    (fun x => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x) ⁻¹' U ∈ Cz v n := by
  have hc : Continuous fun x : Fin n → Fv => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Continuous fun x : Fin n → Fv => ((g⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x :=
    continuous_const.matrix_mulVec continuous_id
  have himg : (fun x => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x) ⁻¹' U =
      (fun x => ((g⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x) '' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx
      exact ⟨_, hx, by simp [Matrix.mulVec_mulVec]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [Matrix.mulVec_mulVec] using hy
  refine ⟨?_, hU.2.1.preimage hc, ?_⟩
  · rw [himg]; exact hU.1.image hinv
  · intro h; apply hU.2.2; simpa using h

/-- **Orthogonal invariance of the Leray measure**: for $g \in \mathrm{GL}_n(F_v)$ with $Q\circ g = Q$ and
$\Delta(\det g) = 1$ (automatic on $O(V_v)$: $\det g = \pm1$), $g_*\sigma_\rho = \sigma_\rho$. -/
theorem lerayMeasure_map_mulVec (ρ : Fv) (g : GL (Fin n) Fv)
    (hg : ∀ x, Qv v Q ((g : Matrix (Fin n) (Fin n) Fv) *ᵥ x) = Qv v Q x)
    (hdet : distribHaarChar Fv (GeneralLinearGroup.det g) = 1) :
    Measure.map (fun x => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x) (lerayMeasure v ν Q hQ ρ) =
      lerayMeasure v ν Q hQ ρ := by
  have hmeas : Measurable fun x : Fin n → Fv => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hpre0 : (fun x => (g : Matrix (Fin n) (Fin n) Fv) *ᵥ x) ⁻¹' {0} = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have := congrArg (fun y => ((g⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) h
      simpa [Matrix.mulVec_mulVec] using this
    · rintro rfl; simp
  refine measure_ext_Cz v ?_ (lerayMeasure_singleton_zero v ν Q hQ ρ) ?_ ?_
  · rw [Measure.map_apply hmeas (measurableSet_singleton _), hpre0]
    exact lerayMeasure_singleton_zero v ν Q hQ ρ
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet]
    exact (lerayMeasure_lt_top v ν Q hQ ρ (preimage_mulVec_mem_Cz v g hU)).ne
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet]
    obtain ⟨k, hk1, hk2⟩ := ((lerayMeasure_eventually v ν Q hQ ρ (preimage_mulVec_mem_Cz v g hU)).and
      (lerayMeasure_eventually v ν Q hQ ρ hU)).exists
    rw [← hk1, ← hk2, ← Measure.map_apply hmeas hU.2.1.measurableSet,
      map_mulVec_lerayThick ν (Qv v Q) g hg hdet]

/-- The shell relation $\varpi^2(\rho + \mathfrak p^k) = \varpi^2\rho + \mathfrak p^{k+2}$. -/
lemma smul_shell_general (ρ : Fv) (k : ℕ) :
    ((((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) • shell v ρ k) =
      shell v ((((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) * ρ) (k + 2) := by
  have hϖ : Valued.v (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) = exp (-2 : ℤ) := by
    simp [ϖU, HN.valued_ϖ, pow_two, ← exp_add]
  have hne : (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  set a : Fv := (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) with ha
  ext x
  simp only [Set.mem_smul_set, shell, Set.mem_ofPred_eq, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : a * y - a * ρ = a * (y - ρ) := by ring
    rw [this, map_mul, hϖ]
    calc exp (-2 : ℤ) * Valued.v (y - ρ) ≤ exp (-2 : ℤ) * exp (-(k : ℤ)) := by gcongr
      _ = exp (-((k + 2 : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
  · intro hx
    refine ⟨x / a, ?_, mul_div_cancel₀ _ hne⟩
    have : x / a - ρ = (x - a * ρ) / a := by field_simp
    rw [this, map_div₀, hϖ, div_le_iff₀ (by simp)]
    calc Valued.v (x - a * ρ) ≤ exp (-((k + 2 : ℕ) : ℤ)) := hx
      _ = exp (-(k : ℤ)) * exp (-2 : ℤ) := by rw [← exp_add]; congr 1; push_cast; ring

/-- The scalar matrix $\varpi\cdot I$. -/
def uniformizerGL : GL (Fin n) Fv := diagGL fun _ => ϖU v

lemma uniformizerGL_mulVec (x : Fin n → Fv) :
    ((uniformizerGL v : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x = ((ϖU v : Fvˣ) : Fv) • x := by
  funext i
  simp [uniformizerGL, coe_diagGL, Matrix.mulVec_diagonal]

/-- **Scaling of the Leray measure under $x \mapsto \varpi x$, $\rho \mapsto \varpi^2\rho$.** -/
theorem lerayMeasure_map_smul (ρ : Fv) :
    Measure.map (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) (lerayMeasure v ν Q hQ ρ) =
      ((modV v : ℝ≥0∞) ^ 2 / (modV v : ℝ≥0∞) ^ n) •
        lerayMeasure v ν Q hQ ((((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) * ρ) := by
  have hg : ∀ x : Fin n → Fv, (fun x => ((ϖU v : Fvˣ) : Fv) • x) x =
      ((uniformizerGL v : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x := fun x =>
    (uniformizerGL_mulVec v x).symm
  have hfun : (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) =
      fun x => ((uniformizerGL v : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x := funext hg
  have hmeas : Measurable fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x := by
    rw [hfun]; exact (continuous_const.matrix_mulVec continuous_id).measurable
  have hpre0 : (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) ⁻¹' {0} = {0} := by
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
    have hU' := preimage_mulVec_mem_Cz v (uniformizerGL v) hU
    have hev1 := lerayMeasure_eventually v ν Q hQ ρ hU'
    have hev2 := (tendsto_add_atTop_nat 2).eventually
      (lerayMeasure_eventually v ν Q hQ ((((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) * ρ) hU)
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    rw [← hk1, ← hk2]
    have hmap := map_smul_lerayThick ν (Qv v Q) (ϖU v) (fun x => qv_smul v Q _ x) (shell v ρ k)
    rw [smul_shell_general] at hmap
    have := congrArg (fun m => m U) hmap
    simp only [Measure.map_apply hmeas hU.2.1.measurableSet, Measure.smul_apply, smul_eq_mul] at this
    rw [← hfun]
    exact this

lemma smul_image_cosetP (i : ℕ) :
    (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) '' cosetP v 0 i = cosetP v 0 (i + 1) := by
  ext x
  simp only [Set.mem_image, cosetP, Set.mem_ofPred_eq, Pi.zero_apply, sub_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    simp only [Pi.smul_apply, smul_eq_mul, ϖU, Units.val_mk0, map_mul, HN.valued_ϖ]
    calc exp (-1 : ℤ) * Valued.v (y j) ≤ exp (-1 : ℤ) * exp (-(i : ℤ)) := by gcongr; exact hy j
      _ = exp (-((i + 1 : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
  · intro hx
    refine ⟨fun j => x j / HN.ϖ v, fun j => ?_, funext fun j => ?_⟩
    · rw [map_div₀, HN.valued_ϖ, div_le_iff₀ (by simp)]
      calc Valued.v (x j) ≤ exp (-((i + 1 : ℕ) : ℤ)) := hx j
        _ = exp (-(i : ℤ)) * exp (-1 : ℤ) := by rw [← exp_add]; congr 1; push_cast; ring
    · simp [ϖU, mul_div_cancel₀ _ (HN.ϖ_ne_zero v)]

lemma smul_injective : Function.Injective fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x :=
  fun x y h => by
    funext j
    have := congrFun h j
    simpa [Units.ne_zero] using this

lemma annulus_mem_Cz (i : ℕ) : cosetP v 0 i \ cosetP v 0 (i + 1) ∈ Cz v n :=
  ⟨(by rw [cosetP_eq]; exact isCompact_closedBall _ _ : IsCompact (cosetP v (0 : Fin n → Fv) i)).diff
      (isOpen_cosetP v 0 (i + 1)),
    (isOpen_cosetP v 0 i).sdiff (by rw [cosetP_eq]; exact Metric.isClosed_closedBall),
    fun h => h.2 (mem_cosetP_self v 0 (i + 1))⟩

/-- **Homogeneity of the cone measure**: $\Delta^2/\Delta^n\cdot\sigma_0(\varpi U) = \sigma_0(U)$, i.e.
$\sigma_0(\varpi U) = q^{-(n-2)}\sigma_0(U)$, for every measurable $U$. -/
theorem lerayMeasure_zero_smul (U : Set (Fin n → Fv)) :
    ((modV v : ℝ≥0∞) ^ 2 / (modV v : ℝ≥0∞) ^ n) *
      lerayMeasure v ν Q hQ 0 ((fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) '' U) =
      lerayMeasure v ν Q hQ 0 U := by
  have hemb : MeasurableEmbedding fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x := by
    have := (smulEquiv (K := Fv) (m := n) (ϖU v)).measurableEmbedding
    rwa [coe_smulEquiv] at this
  have hmap := lerayMeasure_map_smul v ν Q hQ (n := n) 0
  rw [mul_zero] at hmap
  have := congrArg (fun m => m ((fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) '' U)) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at this
  rw [← this, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]

lemma modV_ratio (hn : 2 ≤ n) :
    (modV v : ℝ≥0∞) ^ 2 / (modV v : ℝ≥0∞) ^ n = ENNReal.ofReal (((DVR.q 𝔬 : ℕ) : ℝ) ^ (n - 2)) := by
  have hq : (0 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast q_pos v
  have hmod : (modV v : ℝ≥0∞) = ENNReal.ofReal (((DVR.q 𝔬 : ℕ) : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_coe_nnreal]; congr 1; exact modV_eq v
  rw [hmod, ← ENNReal.ofReal_pow (inv_nonneg.mpr hq.le), ← ENNReal.ofReal_pow (inv_nonneg.mpr hq.le),
    ← ENNReal.ofReal_div_of_pos (pow_pos (inv_pos.mpr hq) n)]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [inv_pow, inv_pow, pow_add (((DVR.q 𝔬 : ℕ) : ℝ)) k 2]
  field_simp

lemma annulus_succ (i : ℕ) :
    (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) '' (cosetP v 0 i \ cosetP v 0 (i + 1)) =
      cosetP v 0 (i + 1) \ cosetP v 0 (i + 1 + 1) := by
  rw [Set.image_diff (smul_injective v), smul_image_cosetP, smul_image_cosetP]

lemma latL_diff_zero_eq_annuli : latL v n \ {0} = ⋃ i : ℕ, (cosetP v 0 i \ cosetP v 0 (i + 1)) := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hx0⟩
    obtain ⟨j, hj⟩ : ∃ j, x ∉ cosetP v 0 j := by
      have := (Set.ext_iff.mp (latL_diff_zero_eq_iUnion v (n := n)) x)
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_iUnion] at this
      obtain ⟨j, -, hj⟩ := this.mp ⟨hx, hx0⟩
      exact ⟨j, hj⟩
    have hex : ∃ i, x ∉ cosetP v 0 (i + 1) := ⟨j, fun h => hj (cosetP_anti v 0 (Nat.le_succ j) h)⟩
    classical
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, ← latL_eq_cosetP]; exact hx
    · have h := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [not_not] at h
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [e] at h
      exact h
  · rintro ⟨i, hi, hi'⟩
    refine ⟨by rw [latL_eq_cosetP]; exact cosetP_anti v 0 (Nat.zero_le i) hi, fun h0 => hi' ?_⟩
    rw [h0]; exact mem_cosetP_self v 0 _

lemma annuli_disjoint : Pairwise (Function.onFun Disjoint fun i : ℕ => (cosetP v (0 : Fin n → Fv) i \ cosetP v 0 (i + 1))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · refine Set.disjoint_left.mpr fun x hx hx' => hx.2 (cosetP_anti v 0 (by omega) hx'.1)
  · refine Set.disjoint_right.mpr fun x hx hx' => hx.2 (cosetP_anti v 0 (by omega) hx'.1)

/-- **The full Leray volume of the null cone in $L_v$**: $\sigma_0(L_v) = \nu(\mathcal O_v)^{n-1}\cdot\gamma_v/(1 - q^{2-n})$
(`coneTotal`), $n \ge 3$. -/
@[kb "weil1982" "§2.4 (Leray measure on the null cone) [unverified]"]
theorem lerayMeasure_latL_cone (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    lerayMeasure v ν (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) 0 (latL v n) =
      ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * coneTotal Q v) := by
  set σ := lerayMeasure v ν (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) 0 with hσ
  have hq : (0 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast q_pos v
  have hq2 : (2 : ℝ) ≤ ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast q_ge_two v
  set q : ℝ := ((DVR.q 𝔬 : ℕ) : ℝ) with hqdef
  set A : ℕ → Set (Fin n → Fv) := fun i => cosetP v 0 i \ cosetP v 0 (i + 1) with hA
  set r : ℝ := (q ^ (n - 2))⁻¹ with hr
  have hq1 : 1 < q ^ (n - 2) := one_lt_pow₀ (by linarith) (by omega)
  have hr0 : 0 < r := inv_pos.mpr (by positivity)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hq1
  have hstep : ∀ i, σ (A (i + 1)) = ENNReal.ofReal r * σ (A i) := by
    intro i
    have h := lerayMeasure_zero_smul v ν (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) (A i)
    rw [hA, annulus_succ, modV_ratio v (by omega)] at h
    show σ (cosetP v 0 (i + 1) \ cosetP v 0 (i + 1 + 1)) = _
    rw [← hσ] at h
    rw [← h, ← mul_assoc, hr, ENNReal.ofReal_inv_of_pos (pow_pos hq _), ENNReal.inv_mul_cancel, one_mul]
    · simpa using pow_pos hq (n - 2)
    · exact ENNReal.ofReal_ne_top
  have hgeo : ∀ i, σ (A i) = ENNReal.ofReal r ^ i * σ (A 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [hstep, ih, pow_succ]; ring
  have hA0 : σ (A 0) = ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * coneFactor Q v) := by
    have := lerayMeasure_prim v ν Q hQ (by omega)
    rw [hA]
    simpa [latL_eq_cosetP] using this
  have hz : σ (latL v n) = σ (latL v n \ {0}) := (measure_diff_null (lerayMeasure_singleton_zero v ν _ _ _)).symm
  rw [hz, latL_diff_zero_eq_annuli, measure_iUnion (annuli_disjoint v)
    (fun i => (annulus_mem_Cz v i).2.1.measurableSet)]
  show ∑' i, σ (A i) = _
  rw [tsum_congr hgeo, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hA0]
  have h1r : ENNReal.ofReal 1 - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := (ENNReal.ofReal_sub 1 hr0.le).symm
  rw [ENNReal.ofReal_one] at h1r
  rw [h1r, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]
  congr 1
  have hc : 0 ≤ ν.real (latticeV v 0) ^ (n - 1) := by
    have := real_latticeV_pos v ν 0
    positivity
  unfold coneTotal
  rw [hr]
  ring

end Props

end QuadFormsKB.Tamagawa.Measure.LerayFinite
