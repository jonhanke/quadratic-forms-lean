import QuadFormsKB.Analysis.LocalFourier

/-!
# The Weil index at a non-archimedean place

Let $K$ be a non-archimedean local field (here: any nontrivially normed field with an ultrametric norm that is
proper, i.e. locally compact), $\mu$ an additive Haar measure on $K$ and $\psi : K \to \mathbb{C}^1$ a continuous
nontrivial additive character (`IsStdChar`). For $t \in K^\times$ the **Gauss integral**
$$\gamma(t) = \int_{\|x\| \le R} \psi(t x^2)\,d\mu(x)$$
does not depend on $R$ once $R$ is large (`gaussInt_spec`); we write `gaussInt μ ψ t` for this value. It is the
Weil index of the character $x \mapsto \psi(t x^2)$ times $|2t|^{-1/2}$ (Weil 1964): in Weil's normalization the
index is $\gamma(t)/|\gamma(t)|$, and here we keep the unnormalized integral, which is all the product formula
needs.

Main results of this file (all for general $K$, $\mu$, $\psi$):

* `setIntegral_eq_zero_of_coset`: if $\int_{x+P} f = 0$ for every $x$ in a $P$-invariant set $B$, then
  $\int_B f = 0$ (averaging over the subgroup $P$; this replaces all coset decompositions);
* `gaussInt_spec`: stabilization of the Gauss integral;
* `gaussInt_mul_sq`: $\gamma(t s^2) = \operatorname{mod}(s)^{-1}\gamma(t)$, $\operatorname{mod}$ the Haar modulus;
* `gaussInt_mul_neg`: $\gamma(t)\gamma(-t)\operatorname{mod}(t) = \gamma(1)\gamma(-1) \ne 0$;
* `weil_identity_ball`: the defining identity of the Weil index for $\varphi = \mathbf 1_{\|x\|\le r}$,
  $$\mathcal F\big(\psi(bx^2)\,\mathcal F\varphi\big)(y) = \gamma(b)\,\psi(cy^2)\,\mathcal F\big(\varphi\,\psi(cx^2)\big)(2cy),
  \qquad c = -\tfrac1{4b},$$
  with $\mathcal F f(y) = \int f(x)\psi(xy)\,d\mu(x)$.

Sources: Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), §14 [unverified];
Rao, *On some explicit formulas in the theory of Weil representation*, Pacific J. Math. 157 (1993) [unverified].
-/

open MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Analysis.Weil

noncomputable section

/-! ### Averaging over a subgroup -/

section Avg

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]

/-- **Averaging over a subgroup.** Let $P$ be a measurable subgroup of positive finite measure and $B$ a measurable
set of finite measure with $B + P \subseteq B$. If $f$ is bounded and measurable and $\int_{P} f(x + h)\,dh = 0$ for
every $x \in B$, then $\int_B f = 0$. -/
theorem setIntegral_eq_zero_of_coset {f : G → ℂ} (P : AddSubgroup G) {B : Set G}
    (hP : MeasurableSet (P : Set G)) (hP0 : μ P ≠ 0) (hPf : μ P ≠ ∞)
    (hB : MeasurableSet B) (hBf : μ B ≠ ∞) (hBP : ∀ x ∈ B, ∀ h ∈ P, x + h ∈ B)
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (h0 : ∀ x ∈ B, ∫ h in (P : Set G), f (x + h) ∂μ = 0) :
    ∫ x in B, f x ∂μ = 0 := by
  have htr : ∀ h ∈ P, ∫ x in B, f (x + h) ∂μ = ∫ x in B, f x ∂μ := by
    intro h hh
    rw [← integral_indicator hB, ← integral_indicator hB,
      ← integral_add_right_eq_self (μ := μ) (fun x => B.indicator f x) h]
    congr 1
    ext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hBP x hx h hh)]
    · have : x + h ∉ B := fun h' => hx (by simpa using hBP _ h' (-h) (P.neg_mem hh))
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  have : IsFiniteMeasure (μ.restrict (P : Set G)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hPf.lt_top⟩
  have : IsFiniteMeasure (μ.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hBf.lt_top⟩
  have hint : Integrable (Function.uncurry fun (h x : G) => f (x + h))
      ((μ.restrict (P : Set G)).prod (μ.restrict B)) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hf.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable
  have hswap := integral_integral_swap hint
  have hL : ∫ h in (P : Set G), ∫ x in B, f (x + h) ∂μ ∂μ = μ.real P • ∫ x in B, f x ∂μ := by
    rw [← setIntegral_const]
    exact setIntegral_congr_fun hP fun h hh => htr h hh
  have hR : ∫ x in B, ∫ h in (P : Set G), f (x + h) ∂μ ∂μ = 0 := by
    rw [setIntegral_congr_fun hB fun x hx => h0 x hx]
    simp
  rw [hL, hR] at hswap
  have hPr : μ.real P ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]; exact ⟨hP0, hPf⟩
  exact (smul_eq_zero.mp hswap).resolve_left hPr

end Avg

/-! ### Balls in an ultrametric field -/

section Balls

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

variable (K) in
/-- The closed ball $\{x : \|x\| \le R\}$ as an additive subgroup (ultrametric inequality). -/
def bsub (R : ℝ≥0) : AddSubgroup K where
  carrier := {x | ‖x‖ ≤ R}
  add_mem' ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

lemma mem_bsub {R : ℝ≥0} {x : K} : x ∈ bsub K R ↔ ‖x‖ ≤ R := Iff.rfl

lemma coe_bsub (R : ℝ≥0) : (bsub K R : Set K) = closedBall 0 R := by
  ext x; simp [mem_bsub]

lemma bsub_mono {R R' : ℝ≥0} (h : R ≤ R') : bsub K R ≤ bsub K R' :=
  fun _ hx => (mem_bsub.mp hx).trans (by exact_mod_cast h)

variable [ProperSpace K] [MeasurableSpace K] [BorelSpace K]

lemma measurableSet_bsub (R : ℝ≥0) : MeasurableSet (bsub K R : Set K) := by
  rw [coe_bsub]; exact measurableSet_closedBall

lemma isCompact_bsub (R : ℝ≥0) : IsCompact (bsub K R : Set K) := by
  rw [coe_bsub]; exact isCompact_closedBall _ _

lemma measure_bsub_ne_top (μ : Measure K) [IsFiniteMeasureOnCompacts μ] (R : ℝ≥0) :
    μ (bsub K R : Set K) ≠ ∞ := (isCompact_bsub R).measure_lt_top.ne

lemma measure_bsub_pos (μ : Measure K) [μ.IsOpenPosMeasure] {R : ℝ≥0} (hR : 0 < R) :
    0 < μ (bsub K R : Set K) := by
  rw [coe_bsub]
  exact (IsUltrametricDist.isOpen_closedBall (0 : K) (by exact_mod_cast hR.ne')).measure_pos μ
    ⟨0, mem_closedBall_self (by positivity)⟩

end Balls

/-! ### Standard characters -/

section Char

variable {K : Type*} [NontriviallyNormedField K]

/-- A **standard character** of $K$: continuous, trivial on a ball around $0$, and nontrivial. -/
structure IsStdChar (ψ : AddChar K Circle) : Prop where
  cont : Continuous ψ
  triv : ∃ r : ℝ, 0 < r ∧ ∀ x : K, ‖x‖ ≤ r → ψ x = 1
  nontriv : ∃ x : K, ψ x ≠ 1

variable {ψ : AddChar K Circle}

/-- A nontrivial character is nontrivial on every large enough ball, uniformly in the scaling. -/
lemma IsStdChar.exists_large (hψ : IsStdChar ψ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (y : K) (R : ℝ), A ≤ ‖y‖ * R → ∃ x : K, ‖x‖ ≤ R ∧ ψ (y * x) ≠ 1 := by
  obtain ⟨x₁, hx₁⟩ := hψ.nontriv
  have hx₁0 : x₁ ≠ 0 := by rintro rfl; exact hx₁ (AddChar.map_zero_eq_one ψ)
  refine ⟨‖x₁‖, norm_pos_iff.mpr hx₁0, fun y R hyR => ?_⟩
  have hy : y ≠ 0 := by
    rintro rfl; rw [norm_zero, zero_mul] at hyR; linarith [norm_pos_iff.mpr hx₁0]
  refine ⟨x₁ / y, ?_, ?_⟩
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hy)]; linarith [mul_comm ‖y‖ R]
  · rwa [mul_div_cancel₀ _ hy]

end Char

/-! ### Gauss integrals -/

section Gauss

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K Circle)

lemma continuous_psi_comp {ψ : AddChar K Circle} (hψ : IsStdChar ψ) {X : Type*} [TopologicalSpace X]
    {f : X → K} (hf : Continuous f) : Continuous fun x => (ψ (f x) : ℂ) :=
  continuous_subtype_val.comp (hψ.cont.comp hf)

lemma integrableOn_bsub {g : K → ℂ} (hg : Continuous g) (R : ℝ≥0) :
    IntegrableOn g (bsub K R : Set K) μ :=
  hg.continuousOn.integrableOn_compact (isCompact_bsub R)

/-- **Integral of a character over a ball:** it vanishes as soon as the character is nontrivial on the ball. -/
lemma integral_bsub_char_eq_zero (y : K) {R : ℝ≥0} (h : ∃ x : K, ‖x‖ ≤ R ∧ ψ (y * x) ≠ 1) :
    ∫ x in (bsub K R : Set K), (ψ (y * x) : ℂ) ∂μ = 0 := by
  obtain ⟨x, hx, hne⟩ := h
  have := setIntegral_addChar_addSubgroup μ (bsub K R) (measurableSet_bsub R)
    (ψ.compAddMonoidHom (AddMonoidHom.mulLeft y))
  split_ifs at this with hc
  · exact absurd (hc x hx) hne
  · exact this

/-- Integral of a character over a ball on which it is trivial. -/
lemma integral_bsub_char_of_triv (y : K) {R : ℝ≥0} (h : ∀ x ∈ bsub K R, ψ (y * x) = 1) :
    ∫ x in (bsub K R : Set K), (ψ (y * x) : ℂ) ∂μ = μ.real (bsub K R : Set K) := by
  have := setIntegral_addChar_addSubgroup μ (bsub K R) (measurableSet_bsub R)
    (ψ.compAddMonoidHom (AddMonoidHom.mulLeft y))
  split_ifs at this with hc
  · exact this
  · exact absurd h hc

/-- Translation invariance of an integral over a ball by an element of the ball. -/
lemma setIntegral_bsub_add (f : K → ℂ) {R : ℝ≥0} {u : K} (hu : ‖u‖ ≤ R) :
    ∫ x in (bsub K R : Set K), f (x + u) ∂μ = ∫ x in (bsub K R : Set K), f x ∂μ := by
  rw [← integral_indicator (measurableSet_bsub R), ← integral_indicator (measurableSet_bsub R),
    ← integral_add_right_eq_self (μ := μ) (fun x => (bsub K R : Set K).indicator f x) u]
  congr 1
  ext x
  have hmem : x + u ∈ (bsub K R : Set K) ↔ x ∈ (bsub K R : Set K) := by
    constructor
    · intro h
      have := (bsub K R).sub_mem h hu
      simpa using this
    · intro h; exact (bsub K R).add_mem h hu
  by_cases hx : x ∈ (bsub K R : Set K)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]

/-- The Gauss integral over the ball of radius $R$: $\int_{\|x\| \le R}\psi(t x^2)\,d\mu(x)$. -/
def gaussI (t : K) (R : ℝ≥0) : ℂ := ∫ x in (bsub K R : Set K), (ψ (t * x ^ 2) : ℂ) ∂μ

open scoped Classical in
/-- **The Gauss integral** $\gamma(t) = \int_{\|x\| \le R}\psi(t x^2)\,d\mu(x)$ for $R$ large (`gaussInt_spec`):
the stable value of `gaussI μ ψ t R` ($0$ by convention if it does not stabilize, which happens only for
$t = 0$). For the self-dual measure this is $|2t|^{-1/2}$ times the Weil index of $x \mapsto \psi(tx^2)$. -/
def gaussInt (t : K) : ℂ :=
  if h : ∃ R₀ : ℝ≥0, ∀ R ≥ R₀, gaussI μ ψ t R = gaussI μ ψ t R₀ then gaussI μ ψ t h.choose else 0

variable {μ ψ}

lemma norm_add_eq_of_lt {x h : K} (hh : ‖h‖ < ‖x‖) : ‖x + h‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hh.ne', max_eq_left hh.le]

/-- **The Gauss integral stabilizes:** for $t \ne 0$ there is $R_0$ with
$\int_{\|x\|\le R}\psi(tx^2) = \int_{\|x\|\le R_0}\psi(tx^2)$ for all $R \ge R_0$. (On $R_0 < \|x\| \le R$, each coset
$x + P$ of a small ball $P$ contributes $\psi(tx^2)\int_P\psi(2txh)\,dh = 0$.) -/
theorem gaussI_stable (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) :
    ∃ R₀ : ℝ≥0, ∀ R ≥ R₀, gaussI μ ψ t R = gaussI μ ψ t R₀ := by
  obtain ⟨r, hr, hr1⟩ := hψ.triv
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have h2t : 0 < ‖2 * t‖ := norm_pos_iff.mpr (mul_ne_zero h2 ht)
  set ε : ℝ := min 1 (r / ‖t‖) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos hr htn)
  have hεt : ‖t‖ * ε ^ 2 ≤ r := by
    have h1 : ε ≤ 1 := min_le_left _ _
    have h2' : ε ≤ r / ‖t‖ := min_le_right _ _
    calc ‖t‖ * ε ^ 2 ≤ ‖t‖ * ε := by
          refine mul_le_mul_of_nonneg_left ?_ htn.le
          nlinarith
      _ ≤ ‖t‖ * (r / ‖t‖) := mul_le_mul_of_nonneg_left h2' htn.le
      _ = r := by field_simp
  set ε' : ℝ≥0 := ⟨ε, hε.le⟩
  have hε' : (0 : ℝ≥0) < ε' := by exact_mod_cast hε
  set R₀ : ℝ≥0 := ⟨max ε (A / (‖2 * t‖ * ε)), le_max_of_le_left hε.le⟩ with hR₀
  refine ⟨R₀, fun R hR => ?_⟩
  have hsub : (bsub K R₀ : Set K) ⊆ bsub K R := bsub_mono hR
  have hcont : Continuous fun x : K => (ψ (t * x ^ 2) : ℂ) :=
    continuous_psi_comp hψ (continuous_const.mul (continuous_pow 2))
  have hdiff : ∫ x in (bsub K R : Set K) \ bsub K R₀, (ψ (t * x ^ 2) : ℂ) ∂μ = 0 := by
    refine setIntegral_eq_zero_of_coset μ (bsub K ε') (measurableSet_bsub _)
      (measure_bsub_pos μ hε').ne' (measure_bsub_ne_top μ _)
      ((measurableSet_bsub R).diff (measurableSet_bsub R₀))
      (ne_top_of_le_ne_top (measure_bsub_ne_top μ R) (measure_mono Set.sdiff_subset))
      ?_ hcont.measurable (C := 1) (fun x => by simp) ?_
    · rintro x ⟨hxR, hxR₀⟩ h hh
      have hxR₀' : (R₀ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₀ h'
      have hh' : ‖h‖ < ‖x‖ := lt_of_le_of_lt ((mem_bsub.mp hh).trans (le_max_left _ _)) hxR₀'
      refine ⟨?_, ?_⟩
      · show ‖x + h‖ ≤ R
        rw [norm_add_eq_of_lt hh']; exact hxR
      · intro hc
        apply hxR₀
        show ‖x‖ ≤ R₀
        have : ‖x + h‖ ≤ R₀ := hc
        rwa [norm_add_eq_of_lt hh'] at this
    · rintro x ⟨-, hxR₀⟩
      have hxR₀' : (R₀ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₀ h'
      have hfun : ∀ h ∈ (bsub K ε' : Set K), (ψ (t * (x + h) ^ 2) : ℂ) =
          (ψ (t * x ^ 2) : ℂ) * (ψ ((2 * t * x) * h) : ℂ) := by
        intro h hh
        have hh2 : ψ (t * h ^ 2) = 1 := by
          refine hr1 _ ?_
          rw [norm_mul, norm_pow]
          have : ‖h‖ ≤ ε := hh
          calc ‖t‖ * ‖h‖ ^ 2 ≤ ‖t‖ * ε ^ 2 := by gcongr
            _ ≤ r := hεt
        rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul,
          show t * (x + h) ^ 2 = (t * x ^ 2 + 2 * t * x * h) + t * h ^ 2 by ring,
          AddChar.map_add_eq_mul ψ _ (t * h ^ 2), hh2, mul_one]
      rw [setIntegral_congr_fun (measurableSet_bsub _) hfun, integral_const_mul,
        integral_bsub_char_eq_zero μ ψ, mul_zero]
      refine hA1 _ _ ?_
      have hAle : A / (‖2 * t‖ * ε) ≤ ‖x‖ := (le_max_right _ _).trans hxR₀'.le
      calc A = ‖2 * t‖ * (A / (‖2 * t‖ * ε)) * ε := by field_simp
        _ ≤ ‖2 * t‖ * ‖x‖ * ε := by gcongr
        _ = ‖2 * t * x‖ * (ε' : ℝ) := by rw [norm_mul (2 * t)]; rfl
  have hunion : (bsub K R : Set K) = (bsub K R₀ : Set K) ∪ ((bsub K R : Set K) \ bsub K R₀) :=
    (Set.union_sdiff_cancel hsub).symm
  unfold gaussI
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right
    ((measurableSet_bsub R).diff (measurableSet_bsub R₀)) (integrableOn_bsub μ hcont R₀)
    ((integrableOn_bsub μ hcont R).mono_set Set.sdiff_subset), hdiff, add_zero]

/-- **Characterization of `gaussInt`:** for $t \ne 0$, $\int_{\|x\|\le R}\psi(tx^2)\,d\mu = \gamma(t)$ for all large $R$. -/
theorem gaussInt_spec (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) :
    ∃ R₀ : ℝ≥0, ∀ R ≥ R₀, gaussI μ ψ t R = gaussInt μ ψ t := by
  have h := gaussI_stable hψ h2 ht (μ := μ)
  refine ⟨h.choose, fun R hR => ?_⟩
  simp only [gaussInt, h, ↓reduceDIte]
  exact h.choose_spec R hR


end Gauss

/-! ### The Haar modulus -/

section Modulus

variable {K : Type*} [NontriviallyNormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]

open scoped Classical in
variable (K) in
/-- **The Haar modulus** $\operatorname{mod}(s)$ of $s \in K^\times$: $\mu(sA) = \operatorname{mod}(s)\,\mu(A)$ for every
Haar measure $\mu$ (Mathlib's `distribHaarChar`); $\operatorname{mod}(0) = 0$ by convention. -/
def modK (s : K) : ℝ := if hs : s = 0 then 0 else (distribHaarChar K (Units.mk0 s hs) : ℝ)

lemma modK_of_ne {s : K} (hs : s ≠ 0) : modK K s = (distribHaarChar K (Units.mk0 s hs) : ℝ) := by
  simp [modK, hs]

lemma modK_pos {s : K} (hs : s ≠ 0) : 0 < modK K s := by
  rw [modK_of_ne hs]; exact_mod_cast distribHaarChar_pos

lemma modK_mul {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) : modK K (s * t) = modK K s * modK K t := by
  rw [modK_of_ne hs, modK_of_ne ht, modK_of_ne (mul_ne_zero hs ht)]
  have : Units.mk0 (s * t) (mul_ne_zero hs ht) = Units.mk0 s hs * Units.mk0 t ht := Units.ext rfl
  rw [this, map_mul, NNReal.coe_mul]

lemma modK_one : modK K (1 : K) = 1 := by
  rw [modK_of_ne one_ne_zero]
  have : Units.mk0 (1 : K) one_ne_zero = 1 := Units.ext rfl
  rw [this, map_one, NNReal.coe_one]

lemma modK_inv {s : K} (hs : s ≠ 0) : modK K s⁻¹ = (modK K s)⁻¹ := by
  have h := modK_mul hs (inv_ne_zero hs)
  rw [mul_inv_cancel₀ hs, modK_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma modK_neg_one : modK K (-1 : K) = 1 := by
  have h := modK_mul (neg_ne_zero.mpr (one_ne_zero (α := K))) (neg_ne_zero.mpr (one_ne_zero (α := K)))
  rw [neg_one_mul, neg_neg, modK_one] at h
  have hp := modK_pos (neg_ne_zero.mpr (one_ne_zero (α := K)))
  nlinarith

lemma modK_neg (s : K) : modK K (-s) = modK K s := by
  by_cases hs : s = 0
  · simp [hs]
  rw [show -s = -1 * s by ring, modK_mul (neg_ne_zero.mpr one_ne_zero) hs, modK_neg_one, one_mul]

variable (μ : Measure K) [μ.IsAddHaarMeasure]

/-- $\mu(sA) = \operatorname{mod}(s)\,\mu(A)$. -/
lemma measure_smul_eq {s : K} (hs : s ≠ 0) (A : Set K) :
    μ ((fun x => s * x) '' A) = ENNReal.ofReal (modK K s) * μ A := by
  have h := distribHaarChar_mul μ (Units.mk0 s hs) A
  have himg : (Units.mk0 s hs) • A = (fun x => s * x) '' A := by
    ext x; simp [Set.mem_smul_set, Units.smul_def]
  rw [← himg, ← h, modK_of_ne hs, ENNReal.ofReal_coe_nnreal]

/-- The image of the Haar measure under $x \mapsto sx$ is $\operatorname{mod}(s)^{-1}\mu$. -/
lemma map_mul_left_eq {s : K} (hs : s ≠ 0) :
    Measure.map (fun x => s * x) μ = ENNReal.ofReal (modK K s)⁻¹ • μ := by
  ext A hA
  rw [Measure.map_apply (measurable_const_mul s) hA, Measure.smul_apply,
    smul_eq_mul]
  have hpre : (fun x => s * x) ⁻¹' A = (fun x => s⁻¹ * x) '' A := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨s * x, h, by field_simp⟩
    · rintro ⟨y, hy, rfl⟩; rwa [mul_inv_cancel_left₀ hs]
  rw [hpre, measure_smul_eq μ (inv_ne_zero hs), modK_inv hs]

/-- **Change of variables** $x \mapsto sx$: $\int f(sx)\,d\mu(x) = \operatorname{mod}(s)^{-1}\int f\,d\mu$. -/
lemma integral_comp_mul_left (f : K → ℂ) {s : K} (hs : s ≠ 0) :
    ∫ x, f (s * x) ∂μ = ((modK K s)⁻¹ : ℝ) • ∫ x, f x ∂μ := by
  have hemb : MeasurableEmbedding (fun x : K => s * x) :=
    (Homeomorph.mulLeft₀ s hs).toMeasurableEquiv.measurableEmbedding
  rw [← hemb.integral_map, map_mul_left_eq μ hs, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (modK_pos hs).le)]

end Modulus

/-! ### Scaling and the product $\gamma(t)\gamma(-t)$ -/

section GaussProps

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}

lemma gaussI_mul_sq {t s : K} (hs : s ≠ 0) (R : ℝ≥0) :
    gaussI μ ψ (t * s ^ 2) R = ((modK K s)⁻¹ : ℝ) • gaussI μ ψ t (‖s‖₊ * R) := by
  unfold gaussI
  rw [← integral_indicator (measurableSet_bsub _), ← integral_indicator (measurableSet_bsub _),
    ← integral_comp_mul_left μ _ hs]
  congr 1
  ext x
  have hiff : s * x ∈ (bsub K (‖s‖₊ * R) : Set K) ↔ x ∈ (bsub K R : Set K) := by
    simp only [SetLike.mem_coe, mem_bsub, NNReal.coe_mul, coe_nnnorm, norm_mul]
    exact mul_le_mul_iff_right₀ (norm_pos_iff.mpr hs)
  by_cases hx : x ∈ (bsub K R : Set K)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.mpr hx)]
    congr 2; ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.mp h))]

/-- **Scaling:** $\gamma(ts^2) = \operatorname{mod}(s)^{-1}\gamma(t)$. -/
theorem gaussInt_mul_sq (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t s : K} (ht : t ≠ 0) (hs : s ≠ 0) :
    gaussInt μ ψ (t * s ^ 2) = ((modK K s)⁻¹ : ℝ) • gaussInt μ ψ t := by
  obtain ⟨R₁, hR₁⟩ := gaussInt_spec (μ := μ) hψ h2 (mul_ne_zero ht (pow_ne_zero 2 hs))
  obtain ⟨R₂, hR₂⟩ := gaussInt_spec (μ := μ) hψ h2 ht
  have hsn : 0 < ‖s‖₊ := nnnorm_pos.mpr hs
  set R := max R₁ (R₂ / ‖s‖₊)
  rw [← hR₁ R (le_max_left _ _), gaussI_mul_sq hs, hR₂]
  calc R₂ = ‖s‖₊ * (R₂ / ‖s‖₊) := by field_simp
    _ ≤ ‖s‖₊ * R := by gcongr; exact le_max_right _ _

variable (ψ) in
/-- The annihilator $\{y : \psi(yx) = 1 \text{ for all } \|x\| \le R\}$ of the ball of radius $R$. -/
def annB (R : ℝ≥0) : Set K := {y | ∀ x ∈ bsub K R, ψ (y * x) = 1}

lemma isClosed_annB (hψ : IsStdChar ψ) (R : ℝ≥0) : IsClosed (annB ψ R) := by
  have : annB ψ R = ⋂ x ∈ bsub K R, {y : K | ψ (y * x) = 1} := by ext y; simp [annB]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_eq (hψ.cont.comp (continuous_id.mul continuous_const))
    continuous_const

lemma annB_subset {R : ℝ≥0} {A : ℝ} (hA : ∀ (y : K) (R : ℝ), A ≤ ‖y‖ * R →
    ∃ x : K, ‖x‖ ≤ R ∧ ψ (y * x) ≠ 1) {y : K} (hy : y ∈ annB ψ R) : ‖y‖ * R < A := by
  by_contra h
  obtain ⟨x, hx, hne⟩ := hA y R (not_lt.mp h)
  exact hne (hy x hx)


lemma measurableSet_annB (hψ : IsStdChar ψ) (R : ℝ≥0) : MeasurableSet (annB ψ R) :=
  (isClosed_annB hψ R).measurableSet

lemma measure_annB_ne_top (hψ : IsStdChar ψ) {R : ℝ≥0} (hR : 0 < R) : μ (annB ψ R) ≠ ∞ := by
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  refine ne_top_of_le_ne_top (isCompact_closedBall (0 : K) (A / R)).measure_lt_top.ne
    (measure_mono fun y hy => ?_)
  have := annB_subset hA1 hy
  rw [mem_closedBall, dist_zero_right, le_div_iff₀ (by exact_mod_cast hR)]
  exact this.le

lemma measure_annB_pos (hψ : IsStdChar ψ) {R : ℝ≥0} (hR : 0 < R) : 0 < μ (annB ψ R) := by
  obtain ⟨r, hr, hr1⟩ := hψ.triv
  have hrR : (0 : ℝ≥0) < ⟨r / R, by positivity⟩ := by
    show (0 : ℝ) < r / R; exact div_pos hr (by exact_mod_cast hR)
  refine lt_of_lt_of_le (measure_bsub_pos μ hrR) (measure_mono fun y hy x hx => hr1 _ ?_)
  have hy' : ‖y‖ ≤ r / R := hy
  have hx' : ‖x‖ ≤ R := hx
  rw [norm_mul]
  calc ‖y‖ * ‖x‖ ≤ (r / R) * R := mul_le_mul hy' hx' (norm_nonneg _) (by positivity)
    _ = r := by field_simp

/-- **The product $\gamma(t)\gamma(-t)$ over a large ball:**
$\int_{B_R}\psi(tx^2)\,dx\int_{B_R}\psi(-ty^2)\,dy\cdot\operatorname{mod}(-2t) = \mu(B_R)\,\mu(B_R^\perp)$ for large $R$
(substitute $y = x + h$, integrate over $x$ first). -/
theorem gaussI_mul_neg (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) :
    ∃ R₁ : ℝ≥0, 0 < R₁ ∧ ∀ R ≥ R₁, gaussI μ ψ t R * gaussI μ ψ (-t) R * modK K (-2 * t) =
      μ.real (bsub K R : Set K) * μ.real (annB ψ R) := by
  obtain ⟨r, hr, hr1⟩ := hψ.triv
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hu : (-2 * t) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) ht
  set c := ‖-2 * t‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hu
  set R₁r : ℝ := max 1 (max (Real.sqrt (A / c)) (A / (c * Real.sqrt (r / ‖t‖))))
  have hR₁r : 0 < R₁r := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨⟨R₁r, hR₁r.le⟩, by exact_mod_cast hR₁r, fun R hR => ?_⟩
  have hRr : R₁r ≤ R := hR
  have hRpos : 0 < (R : ℝ) := lt_of_lt_of_le hR₁r hRr
  set B : Set K := (bsub K R : Set K)
  set S : Set K := {h | -2 * t * h ∈ annB ψ R}
  -- points of `S` are small
  have hSsmall : ∀ h ∈ S, ‖h‖ ≤ A / (c * R) := by
    intro h hh
    have := annB_subset hA1 hh
    rw [norm_mul] at this
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  have hδR : A / (c * R) ≤ R := by
    have h1 : Real.sqrt (A / c) ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRr
    have h1' : A / c ≤ R * R := by
      have := Real.sqrt_le_sqrt (le_refl (A / c))
      calc A / c = Real.sqrt (A / c) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ R ^ 2 := by gcongr
        _ = R * R := sq _
    rw [div_le_iff₀ (by positivity)]
    calc A = A / c * c := by field_simp
      _ ≤ R * R * c := by gcongr
      _ = R * (c * R) := by ring
  have hδt : ‖t‖ * (A / (c * R)) ^ 2 ≤ r := by
    have hsq : 0 < Real.sqrt (r / ‖t‖) := Real.sqrt_pos.mpr (div_pos hr htn)
    have h1 : A / (c * Real.sqrt (r / ‖t‖)) ≤ R :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRr
    have h2' : A / (c * R) ≤ Real.sqrt (r / ‖t‖) := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h1
      nlinarith
    calc ‖t‖ * (A / (c * R)) ^ 2 ≤ ‖t‖ * Real.sqrt (r / ‖t‖) ^ 2 := by
          gcongr
      _ = r := by rw [Real.sq_sqrt (div_pos hr htn).le]; field_simp
  have hSB : S ⊆ B := fun h hh => (hSsmall h hh).trans hδR
  have hSone : ∀ h ∈ S, ψ (-t * h ^ 2) = 1 := by
    intro h hh
    refine hr1 _ ?_
    rw [norm_mul, norm_neg, norm_pow]
    calc ‖t‖ * ‖h‖ ^ 2 ≤ ‖t‖ * (A / (c * R)) ^ 2 := by gcongr; exact hSsmall h hh
      _ ≤ r := hδt
  have hcont1 : Continuous fun p : K × K => (ψ (-t * p.2 ^ 2) : ℂ) * (ψ (-2 * t * p.2 * p.1) : ℂ) :=
    (continuous_psi_comp hψ (continuous_const.mul (continuous_snd.pow 2))).mul
      (continuous_psi_comp hψ ((continuous_const.mul continuous_snd).mul continuous_fst))
  -- step 1: the product as an iterated integral
  have step1 : gaussI μ ψ t R * gaussI μ ψ (-t) R =
      ∫ x in B, ∫ h in B, (ψ (-t * h ^ 2) : ℂ) * (ψ (-2 * t * h * x) : ℂ) ∂μ ∂μ := by
    unfold gaussI
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_bsub R) fun x hx => ?_
    rw [← setIntegral_bsub_add μ (fun y => (ψ (-t * y ^ 2) : ℂ)) (u := x) hx, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  -- step 2: swap
  have : IsFiniteMeasure (μ.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_bsub_ne_top μ R).lt_top⟩
  have hint : Integrable (Function.uncurry fun (x h : K) =>
      (ψ (-t * h ^ 2) : ℂ) * (ψ (-2 * t * h * x) : ℂ)) ((μ.restrict B).prod (μ.restrict B)) := by
    refine Integrable.of_bound hcont1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry]
  have step2 := integral_integral_swap hint
  -- step 3: the inner integral
  have step3 : ∫ h in B, ∫ x in B, (ψ (-t * h ^ 2) : ℂ) * (ψ (-2 * t * h * x) : ℂ) ∂μ ∂μ =
      ∫ h, S.indicator (fun _ => (μ.real B : ℂ)) h ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
      (fun h hh => Set.indicator_of_notMem (fun h' => hh (hSB h')) _)]
    refine setIntegral_congr_fun (measurableSet_bsub R) fun h hh => ?_
    rw [integral_const_mul]
    by_cases hS : h ∈ S
    · rw [Set.indicator_of_mem hS, hSone h hS, Circle.coe_one, one_mul,
        integral_bsub_char_of_triv μ ψ _ hS]
    · rw [Set.indicator_of_notMem hS, integral_bsub_char_eq_zero μ ψ, mul_zero]
      by_contra hc'
      push Not at hc'
      exact hS fun x hx => hc' x hx
  -- step 4: the measure of `S`
  have hSeq : S = (fun h => -2 * t * h) ⁻¹' annB ψ R := rfl
  have hmS : μ S = ENNReal.ofReal (modK K (-2 * t))⁻¹ * μ (annB ψ R) := by
    rw [hSeq, ← Measure.map_apply (measurable_const_mul _) (measurableSet_annB hψ R),
      map_mul_left_eq μ hu, Measure.smul_apply, smul_eq_mul]
  have hSmeas : MeasurableSet S := (measurableSet_annB hψ R).preimage (measurable_const_mul _)
  rw [step1, step2, step3, integral_indicator_const _ hSmeas, Measure.real, hmS,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (modK_pos hu).le)]
  rw [Complex.real_smul]
  have hm : (modK K (-(2 * t)) : ℂ) ≠ 0 := by rw [← neg_mul]; exact_mod_cast (modK_pos hu).ne'
  simp only [Measure.real]
  push_cast
  field_simp

/-- **$\gamma(t)\,\gamma(-t)\,\operatorname{mod}(t) = \gamma(1)\,\gamma(-1)$** for $t \ne 0$. -/
theorem gaussInt_mul_neg (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) :
    gaussInt μ ψ t * gaussInt μ ψ (-t) * modK K t = gaussInt μ ψ 1 * gaussInt μ ψ (-1) := by
  obtain ⟨R₁, -, hR₁⟩ := gaussI_mul_neg (μ := μ) hψ h2 ht
  obtain ⟨R₂, -, hR₂⟩ := gaussI_mul_neg (μ := μ) hψ h2 (one_ne_zero (α := K))
  obtain ⟨R₃, hR₃⟩ := gaussInt_spec (μ := μ) hψ h2 ht
  obtain ⟨R₄, hR₄⟩ := gaussInt_spec (μ := μ) hψ h2 (neg_ne_zero.mpr ht)
  obtain ⟨R₅, hR₅⟩ := gaussInt_spec (μ := μ) hψ h2 (one_ne_zero (α := K))
  obtain ⟨R₆, hR₆⟩ := gaussInt_spec (μ := μ) hψ h2 (neg_ne_zero.mpr (one_ne_zero (α := K)))
  set R := max (max (max R₁ R₂) (max R₃ R₄)) (max R₅ R₆)
  have e1 := hR₁ R (by simp [R])
  have e2 := hR₂ R (by simp [R])
  rw [hR₃ R (by simp [R]), hR₄ R (by simp [R])] at e1
  rw [hR₅ R (by simp [R]), hR₆ R (by simp [R]), mul_one] at e2
  have hm2 : modK K (-2 : K) ≠ 0 := (modK_pos (neg_ne_zero.mpr h2)).ne'
  rw [modK_mul (neg_ne_zero.mpr h2) ht] at e1
  have : (gaussInt μ ψ t * gaussInt μ ψ (-t) * modK K t) * modK K (-2 : K) =
      (gaussInt μ ψ 1 * gaussInt μ ψ (-1)) * modK K (-2 : K) := by
    rw [e2]; push_cast at e1 ⊢; rw [← e1]; ring
  exact mul_right_cancel₀ (by exact_mod_cast hm2) this

/-- $\gamma(1)\gamma(-1) \ne 0$. -/
theorem gaussInt_one_mul_neg_one_ne_zero (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) :
    gaussInt μ ψ 1 * gaussInt μ ψ (-1) ≠ 0 := by
  obtain ⟨R₁, hR₁0, hR₁⟩ := gaussI_mul_neg (μ := μ) hψ h2 (one_ne_zero (α := K))
  obtain ⟨R₅, hR₅⟩ := gaussInt_spec (μ := μ) hψ h2 (one_ne_zero (α := K))
  obtain ⟨R₆, hR₆⟩ := gaussInt_spec (μ := μ) hψ h2 (neg_ne_zero.mpr (one_ne_zero (α := K)))
  set R := max R₁ (max R₅ R₆)
  have hRpos : 0 < R := lt_of_lt_of_le hR₁0 (le_max_left _ _)
  have e := hR₁ R (le_max_left _ _)
  rw [hR₅ R (by simp [R]), hR₆ R (by simp [R])] at e
  intro h0
  rw [h0, zero_mul] at e
  have hB : 0 < μ.real (bsub K R : Set K) :=
    ENNReal.toReal_pos (measure_bsub_pos μ hRpos).ne' (measure_bsub_ne_top μ R)
  have hA : 0 < μ.real (annB ψ R) :=
    ENNReal.toReal_pos (measure_annB_pos hψ hRpos).ne' (measure_annB_ne_top hψ hRpos)
  have : (μ.real (bsub K R : Set K) * μ.real (annB ψ R) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hB hA).ne'
  exact this e.symm

/-- **The Gauss integral does not vanish:** $\gamma(t) \ne 0$ for $t \ne 0$. -/
theorem gaussInt_ne_zero (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) :
    gaussInt μ ψ t ≠ 0 := by
  intro h0
  have := gaussInt_mul_neg (μ := μ) hψ h2 ht
  rw [h0, zero_mul, zero_mul] at this
  exact gaussInt_one_mul_neg_one_ne_zero hψ h2 this.symm

end GaussProps

/-! ### The defining identity of the Weil index -/

section WeilIdentity

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K Circle)

/-- The Fourier transform $\mathcal F f(y) = \int_K f(x)\,\psi(xy)\,d\mu(x)$. -/
def fourierK (f : K → ℂ) (y : K) : ℂ := ∫ x, f x * (ψ (x * y) : ℂ) ∂μ

variable {μ ψ}

lemma fourierK_indicator (r : ℝ≥0) (x : K) :
    fourierK μ ψ ((bsub K r : Set K).indicator 1) x = ∫ z in (bsub K r : Set K), (ψ (x * z) : ℂ) ∂μ := by
  unfold fourierK
  rw [← integral_indicator (measurableSet_bsub r)]
  congr 1; ext z
  by_cases hz : z ∈ (bsub K r : Set K)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, one_mul, mul_comm]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]

/-- **The Weil identity for a ball** (the defining property of the Weil index, for $\varphi = \mathbf 1_{B_r}$):
with $c = -1/(4b)$ and $\mathcal F f(y) = \int f(x)\psi(xy)\,d\mu(x)$,
$$\mathcal F\big(x \mapsto \psi(bx^2)\,\mathcal F\varphi(x)\big)(y) = \gamma(b)\,\psi(cy^2)\,
  \mathcal F\big(x \mapsto \varphi(x)\psi(cx^2)\big)(2cy).$$
*Proof:* write $\gamma(b) = \int_{B_R}\psi(b(x + w)^2)\,dx$ with $w = (z+y)/(2b)$, complete the square, and swap
the integrals (Fubini over $B_R \times B_r$). -/
theorem weil_identity_ball (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) {b : K} (hb : b ≠ 0) {r : ℝ≥0}
    (hr : 0 < r) (y : K) :
    fourierK μ ψ (fun x => (ψ (b * x ^ 2) : ℂ) * fourierK μ ψ ((bsub K r : Set K).indicator 1) x) y =
      gaussInt μ ψ b * (ψ (-(4 * b)⁻¹ * y ^ 2) : ℂ) *
        fourierK μ ψ (fun x => (bsub K r : Set K).indicator 1 x * (ψ (-(4 * b)⁻¹ * x ^ 2) : ℂ))
          (2 * (-(4 * b)⁻¹) * y) := by
  set c : K := -(4 * b)⁻¹ with hc
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  obtain ⟨R₀, hR₀⟩ := gaussInt_spec (μ := μ) hψ h2 hb
  have h2b : 0 < ‖2 * b‖ := norm_pos_iff.mpr (mul_ne_zero h2 hb)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  set R : ℝ≥0 := max R₀ (max ⟨A / r, by positivity⟩ ⟨max (r : ℝ) ‖y‖ / ‖2 * b‖, by positivity⟩)
  have hRA : A / r ≤ R := by
    have : (⟨A / r, by positivity⟩ : ℝ≥0) ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    exact_mod_cast this
  have hRw : max (r : ℝ) ‖y‖ / ‖2 * b‖ ≤ R := by
    have : (⟨max (r : ℝ) ‖y‖ / ‖2 * b‖, by positivity⟩ : ℝ≥0) ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    exact_mod_cast this
  set H : Set K := (bsub K r : Set K)
  set BR : Set K := (bsub K R : Set K)
  have hcontH : ∀ x : K, Continuous fun z : K => (ψ (x * z) : ℂ) := fun x =>
    continuous_psi_comp hψ (continuous_const.mul continuous_id)
  -- the transform of `1_H` vanishes outside `B_R`
  have hF0 : ∀ x : K, x ∉ BR → fourierK μ ψ (H.indicator 1) x = 0 := by
    intro x hx
    rw [fourierK_indicator]
    refine integral_bsub_char_eq_zero μ ψ x (hA1 x r ?_)
    have hxR : (R : ℝ) < ‖x‖ := lt_of_not_ge hx
    have : A / r < ‖x‖ := lt_of_le_of_lt hRA hxR
    rw [div_lt_iff₀ hrpos] at this
    exact this.le
  -- the left side as an iterated integral over `B_R × H`
  have hL : fourierK μ ψ (fun x => (ψ (b * x ^ 2) : ℂ) * fourierK μ ψ (H.indicator 1) x) y =
      ∫ x in BR, ∫ z in H, (ψ (b * x ^ 2 + x * z + x * y) : ℂ) ∂μ ∂μ := by
    show ∫ x, (ψ (b * x ^ 2) : ℂ) * fourierK μ ψ (H.indicator 1) x * (ψ (x * y) : ℂ) ∂μ = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := BR) (fun x hx => by
      rw [hF0 x hx]; simp)]
    refine setIntegral_congr_fun (measurableSet_bsub R) fun x _ => ?_
    rw [fourierK_indicator, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  -- the right side as an iterated integral over `H × B_R`
  have hR : gaussInt μ ψ b * (ψ (c * y ^ 2) : ℂ) *
      fourierK μ ψ (fun x => H.indicator 1 x * (ψ (c * x ^ 2) : ℂ)) (2 * c * y) =
      ∫ z in H, ∫ x in BR, (ψ (b * x ^ 2 + x * z + x * y) : ℂ) ∂μ ∂μ := by
    show gaussInt μ ψ b * (ψ (c * y ^ 2) : ℂ) *
      ∫ z, H.indicator 1 z * (ψ (c * z ^ 2) : ℂ) * (ψ (z * (2 * c * y)) : ℂ) ∂μ = _
    rw [← integral_const_mul, ← integral_indicator (measurableSet_bsub r)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : z ∈ H
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      have hw : ‖(z + y) / (2 * b)‖ ≤ R := by
        rw [norm_div]
        refine le_trans ?_ hRw
        gcongr
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
        exact hz
      rw [← hR₀ R (le_max_left _ _), gaussI,
        ← setIntegral_bsub_add μ (fun x => (ψ (b * x ^ 2) : ℂ)) hw, ← integral_mul_const,
        ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      rw [hc]
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
      field_simp
      ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp
  rw [hL, hR]
  have : IsFiniteMeasure (μ.restrict BR) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_bsub_ne_top μ R).lt_top⟩
  have : IsFiniteMeasure (μ.restrict H) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_bsub_ne_top μ r).lt_top⟩
  refine integral_integral_swap (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun p => ?_))
  · exact (continuous_psi_comp hψ ((continuous_const.mul (continuous_fst.pow 2)).add
      (continuous_fst.mul continuous_snd) |>.add (continuous_fst.mul continuous_const))).aestronglyMeasurable
  · simp [Function.uncurry]

end WeilIdentity

/-! ### Stabilization with explicit radii -/

section Explicit

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}

/-- **Stabilization with explicit radii:** if $\psi(th^2) = 1$ on $B_\varepsilon$ and $h \mapsto \psi(2txh)$ is
nontrivial on $B_\varepsilon$ whenever $\|x\| > R_1 \ge \varepsilon$, then
$\int_{B_{R_2}}\psi(tx^2) = \int_{B_{R_1}}\psi(tx^2)$ for $R_2 \ge R_1$. -/
theorem gaussI_eq_of_ge (hψc : Continuous ψ) {t : K} {ε : ℝ≥0} (hε : 0 < ε)
    (hεt : ∀ h : K, ‖h‖ ≤ ε → ψ (t * h ^ 2) = 1) {R₁ R₂ : ℝ≥0} (h₁ : ε ≤ R₁) (h12 : R₁ ≤ R₂)
    (hnt : ∀ x : K, (R₁ : ℝ) < ‖x‖ → ∃ h : K, ‖h‖ ≤ ε ∧ ψ (2 * t * x * h) ≠ 1) :
    gaussI μ ψ t R₂ = gaussI μ ψ t R₁ := by
  have hsub : (bsub K R₁ : Set K) ⊆ bsub K R₂ := bsub_mono h12
  have hcont : Continuous fun x : K => (ψ (t * x ^ 2) : ℂ) :=
    continuous_subtype_val.comp (hψc.comp (continuous_const.mul (continuous_pow 2)))
  have hdiff : ∫ x in (bsub K R₂ : Set K) \ bsub K R₁, (ψ (t * x ^ 2) : ℂ) ∂μ = 0 := by
    refine setIntegral_eq_zero_of_coset μ (bsub K ε) (measurableSet_bsub _)
      (measure_bsub_pos μ hε).ne' (measure_bsub_ne_top μ _)
      ((measurableSet_bsub R₂).diff (measurableSet_bsub R₁))
      (ne_top_of_le_ne_top (measure_bsub_ne_top μ R₂) (measure_mono Set.sdiff_subset))
      ?_ hcont.measurable (C := 1) (fun x => by simp) ?_
    · rintro x ⟨hxR, hxR₁⟩ h hh
      have hxR₁' : (R₁ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₁ h'
      have hh' : ‖h‖ < ‖x‖ := lt_of_le_of_lt ((mem_bsub.mp hh).trans (by exact_mod_cast h₁)) hxR₁'
      refine ⟨?_, ?_⟩
      · show ‖x + h‖ ≤ R₂
        rw [norm_add_eq_of_lt hh']; exact hxR
      · intro hc
        apply hxR₁
        show ‖x‖ ≤ R₁
        have : ‖x + h‖ ≤ R₁ := hc
        rwa [norm_add_eq_of_lt hh'] at this
    · rintro x ⟨-, hxR₁⟩
      have hxR₁' : (R₁ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₁ h'
      have hfun : ∀ h ∈ (bsub K ε : Set K), (ψ (t * (x + h) ^ 2) : ℂ) =
          (ψ (t * x ^ 2) : ℂ) * (ψ ((2 * t * x) * h) : ℂ) := by
        intro h hh
        rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul,
          show t * (x + h) ^ 2 = (t * x ^ 2 + 2 * t * x * h) + t * h ^ 2 by ring,
          AddChar.map_add_eq_mul ψ _ (t * h ^ 2), hεt h hh, mul_one]
      rw [setIntegral_congr_fun (measurableSet_bsub _) hfun, integral_const_mul,
        integral_bsub_char_eq_zero μ ψ, mul_zero]
      exact hnt x hxR₁'
  have hunion : (bsub K R₂ : Set K) = (bsub K R₁ : Set K) ∪ ((bsub K R₂ : Set K) \ bsub K R₁) :=
    (Set.union_sdiff_cancel hsub).symm
  unfold gaussI
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right
    ((measurableSet_bsub R₂).diff (measurableSet_bsub R₁)) (integrableOn_bsub μ hcont R₁)
    ((integrableOn_bsub μ hcont R₂).mono_set Set.sdiff_subset), hdiff, add_zero]

end Explicit

/-! ### Locally constant functions on a compact subgroup are finite sums of coset indicators -/

section Cosets

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- **Coset expansion.** If $L$ is a compact subgroup, $P \le L$ an open subgroup and $f$ is $P$-invariant on $L$,
then $\mathbf 1_L f = \sum_i f(c_i)\,\mathbf 1_{c_i + P}$ for finitely many $c_i \in L$ (representatives of $L/P$). -/
theorem exists_coset_sum (L P : AddSubgroup G) (hL : IsCompact (L : Set G)) (hP : IsOpen (P : Set G))
    (hPL : P ≤ L) (f : G → ℂ) (hf : ∀ x ∈ L, ∀ h ∈ P, f (x + h) = f x) :
    ∃ (n : ℕ) (c : Fin n → G), (∀ i, c i ∈ L) ∧ ∀ x, (L : Set G).indicator f x =
      ∑ i, f (c i) * {y : G | y - c i ∈ P}.indicator 1 x := by
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hopen : IsOpen ((P.addSubgroupOf L : AddSubgroup L) : Set L) :=
    hP.preimage continuous_subtype_val
  have hfin : Finite (L ⧸ P.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ hopen
  let _ : Fintype (L ⧸ P.addSubgroupOf L) := Fintype.ofFinite _
  set e := Fintype.equivFin (L ⧸ P.addSubgroupOf L)
  have hrel : ∀ (a : L) (q : L ⧸ P.addSubgroupOf L), (a : G) - (q.out : G) ∈ P ↔
      (QuotientAddGroup.mk a : L ⧸ P.addSubgroupOf L) = q := by
    intro a q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp [sub_eq_neg_add]
  refine ⟨Fintype.card _, fun i => ((e.symm i).out : G), fun i => (e.symm i).out.2, fun x => ?_⟩
  by_cases hx : x ∈ L
  · rw [Set.indicator_of_mem hx]
    set i0 := e (QuotientAddGroup.mk ⟨x, hx⟩)
    have hmem0 : x - ((e.symm i0).out : G) ∈ P := by
      rw [hrel ⟨x, hx⟩ (e.symm i0)]
      simp [i0]
    rw [Finset.sum_eq_single i0]
    · rw [Set.indicator_of_mem (show x ∈ {y : G | y - ((e.symm i0).out : G) ∈ P} from hmem0),
        Pi.one_apply, mul_one]
      have := hf _ (e.symm i0).out.2 _ hmem0
      rw [add_sub_cancel] at this
      exact this
    · intro i _ hi
      rw [Set.indicator_of_notMem, mul_zero]
      intro hmem
      apply hi
      have h' := (hrel ⟨x, hx⟩ (e.symm i)).mp hmem
      simp [i0, h']
    · simp
  · rw [Set.indicator_of_notMem hx]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Set.indicator_of_notMem, mul_zero]
    intro hmem
    apply hx
    have := L.add_mem (hPL hmem) (e.symm i).out.2
    simpa using this

end Cosets

end

end QuadFormsKB.Analysis.Weil
