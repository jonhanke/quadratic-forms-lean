import QuadFormsKB.Tamagawa.Measure.Weil.Fujisaki

/-!
# Weil's volume constant for $A = \mathbb H[F,a,b]$ (Lemma 3.1.2)

$\mathbb H = \mathbb H[F,a,b]$ with $a, b\in F^\times$ integral at every finite place, any number field $F$, any signature.
`tamQuat a b` is Weil's measure $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ on $(\mathbb H\otimes\mathbb A)^\times$ (the
global factor $\rho_F^{-1}$ kept separate) and `muQuatOneTam` the measure $\mu^1$ on $\mathbb H_{\mathbb A}^1$ with
$(\mathrm{quatSplit})_*\,\mathrm{tamQuat} = \mu^1\times dt/t$.

* **`quatVolConst`** $= c_A' = \mu^1(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1)$ (`muQuatClassTam univ`); for $\mathbb H$ a division
  algebra $0 < c_A' < \infty$ (Fujisaki): `quatVolConst_pos`, `quatVolConst_lt_top`.
* **`isFundamentalDomain_quatSplit_preimage`**: for an exact fundamental domain $D^1$ of $\mathbb H^\times$ in
  $\mathbb H_{\mathbb A}^1$, $\mathrm{quatSplit}^{-1}(D^1\times\mathbb R_{>0})$ is one of $\mathbb H^\times$ in $(\mathbb H\otimes\mathbb A)^\times$.
* **Weil's Lemma 3.1.2 in the form used by the zeta argument** (`setLIntegral_quatFD_logNorm`): for every fundamental
  domain $D$ of $\mathbb H^\times$ in $(\mathbb H\otimes\mathbb A)^\times$ and measurable $h\ge0$,
  $$\int_D h(\log\|\operatorname{nrd}x\|_{\mathbb A})\,d\mu(x) = c_A'\int_{\mathbb R}h(u)\,du,$$
  i.e. the Tamagawa measure disintegrates along $\|\operatorname{nrd}\|$ with fibre volume $c_A'$. Weil's $c_A$ is the
  same constant for the module $|x|_A = \|\operatorname{nrd}x\|^2$ in place of $\|\operatorname{nrd}x\|$; we keep $\|\operatorname{nrd}\|$
  throughout.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

variable {a b : F}

/-! ### Exact fundamental domains and the splitting -/

theorem quatLogNorm_eq_one_of_mem {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) : quatLogNorm a b γ = 1 :=
  (mem_quatOne_iff_logNorm a b γ).mp (quatUnitsSub_le_quatOne a b hγ)

/-- The first component of `quatSplit` is equivariant for left multiplication by $\mathbb H^\times$. -/
theorem quatSplit_fst_mul {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    ((quatSplit a b (γ * x)).1 : (QuatAdele a b)ˣ) = γ * ((quatSplit a b x).1 : (QuatAdele a b)ˣ) := by
  change γ * x * (quatSectionHom a b (quatLogNorm a b (γ * x)))⁻¹ =
    γ * (x * (quatSectionHom a b (quatLogNorm a b x))⁻¹)
  rw [map_mul, quatLogNorm_eq_one_of_mem hγ, one_mul, mul_assoc]

theorem quatSplit_snd_mul {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    (quatSplit a b (γ * x)).2 = (quatSplit a b x).2 := by
  change quatLogNorm a b (γ * x) = quatLogNorm a b x
  rw [map_mul, quatLogNorm_eq_one_of_mem hγ, one_mul]

variable (a b) in
/-- An exact measurable fundamental domain for $\mathbb H^\times$ in $\mathbb H_{\mathbb A}^1$. -/
theorem exists_exact_quatOneFD :
    ∃ D : Set (quatOne a b), MeasurableSet D ∧ ∀ x : quatOne a b, ∃! γ : quatUnitsOne a b, γ • x ∈ D :=
  exists_measurableSet_forall_existsUnique_smul_mem (quatUnitsOne a b)

/-- $\mathbb H^\times\le(\mathbb H\otimes\mathbb A)^\times$ as a subgroup of $\mathbb H_{\mathbb A}^1$. -/
def quatUnitsSubToOne (γ : quatUnitsSub a b) : quatUnitsOne a b :=
  ⟨⟨γ, quatUnitsSub_le_quatOne a b γ.2⟩, Subgroup.mem_subgroupOf.mpr γ.2⟩

theorem quatUnitsSubToOne_smul_val (γ : quatUnitsSub a b) (y : quatOne a b) :
    ((quatUnitsSubToOne γ • y : quatOne a b) : (QuatAdele a b)ˣ) = (γ : (QuatAdele a b)ˣ) * (y : (QuatAdele a b)ˣ) :=
  rfl

theorem quatSplit_fst_smul (γ : quatUnitsSub a b) (x : (QuatAdele a b)ˣ) :
    (quatSplit a b (γ • x)).1 = quatUnitsSubToOne γ • (quatSplit a b x).1 := by
  apply Subtype.ext
  rw [quatUnitsSubToOne_smul_val, Subgroup.smul_def, smul_eq_mul]
  exact quatSplit_fst_mul γ.2 x

/-- **The lift of a fundamental domain of $\mathbb H^\times$ in $\mathbb H_{\mathbb A}^1$**: if every $y\in\mathbb H_{\mathbb A}^1$ has
exactly one $\mathbb H^\times$-translate in $D^1$, then every $x\in(\mathbb H\otimes\mathbb A)^\times$ has exactly one in
$\mathrm{quatSplit}^{-1}(D^1\times\mathbb R_{>0})$. -/
theorem existsUnique_smul_mem_quatSplit_preimage {D : Set (quatOne a b)}
    (hD : ∀ x : quatOne a b, ∃! γ : quatUnitsOne a b, γ • x ∈ D) (x : (QuatAdele a b)ˣ) :
    ∃! γ : quatUnitsSub a b, γ • x ∈ quatSplit a b ⁻¹' (D ×ˢ univ) := by
  have key : ∀ γ : quatUnitsSub a b, (γ • x ∈ quatSplit a b ⁻¹' (D ×ˢ univ) ↔
      quatUnitsSubToOne γ • (quatSplit a b x).1 ∈ D) := by
    intro γ
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
    rw [quatSplit_fst_smul]
  obtain ⟨γ₀, hγ₀, huniq⟩ := hD (quatSplit a b x).1
  have hγ₀m : ((γ₀ : quatOne a b) : (QuatAdele a b)ˣ) ∈ quatUnitsSub a b := Subgroup.mem_subgroupOf.mp γ₀.2
  have he : quatUnitsSubToOne ⟨((γ₀ : quatOne a b) : (QuatAdele a b)ˣ), hγ₀m⟩ = γ₀ := rfl
  refine ⟨⟨((γ₀ : quatOne a b) : (QuatAdele a b)ˣ), hγ₀m⟩, (key _).mpr ?_, fun γ hγ => ?_⟩
  · rw [he]; exact hγ₀
  · have := huniq _ ((key γ).mp hγ)
    apply Subtype.ext
    exact congrArg (fun z : quatUnitsOne a b => ((z : quatOne a b) : (QuatAdele a b)ˣ)) this

theorem measurable_quatSplit : Measurable (quatSplit a b) := (quatSplit a b).continuous.measurable

/-- **$\mathrm{quatSplit}^{-1}(D^1\times\mathbb R_{>0})$ is a fundamental domain** for $\mathbb H^\times$ in
$(\mathbb H\otimes\mathbb A)^\times$, for every measure, when $D^1$ is an exact measurable one in $\mathbb H_{\mathbb A}^1$. -/
theorem isFundamentalDomain_quatSplit_preimage {D : Set (quatOne a b)} (hDm : MeasurableSet D)
    (hD : ∀ x : quatOne a b, ∃! γ : quatUnitsOne a b, γ • x ∈ D) (μ : Measure (QuatAdele a b)ˣ) :
    IsFundamentalDomain (quatUnitsSub a b) (quatSplit a b ⁻¹' (D ×ˢ univ)) μ :=
  IsFundamentalDomain.mk' ((hDm.prod MeasurableSet.univ).preimage measurable_quatSplit).nullMeasurableSet
    (existsUnique_smul_mem_quatSplit_preimage hD)

/-! ### The volume constant -/

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb ha0 hb0 in
/-- **The volume constant** $c_A' = \operatorname{vol}(\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1)$ for the canonical measure
$\mu^1$ (`muQuatClassTam`): Weil's constant of Lemma 3.1.2 in the normalization $t = \|\operatorname{nrd}x\|_{\mathbb A}$. -/
def quatVolConst : ℝ≥0∞ := muQuatClassTam ha hb ha0 hb0 univ

include ha hb ha0 hb0 in
theorem quatVolConst_ne_zero : quatVolConst ha hb ha0 hb0 ≠ 0 := muQuatClassTam_univ_ne_zero ha hb ha0 hb0

include ha hb ha0 hb0 in
theorem quatVolConst_pos : 0 < quatVolConst ha hb ha0 hb0 := pos_iff_ne_zero.mpr (quatVolConst_ne_zero ha hb ha0 hb0)

include ha hb ha0 hb0 in
/-- $c_A' < \infty$ for a division algebra (Fujisaki). -/
theorem quatVolConst_lt_top (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) : quatVolConst ha hb ha0 hb0 < ∞ :=
  muQuatClassTam_univ_lt_top ha hb ha0 hb0 hdiv

include ha hb ha0 hb0 in
theorem quatVolConst_eq {D : Set (quatOne a b)} (hDm : MeasurableSet D)
    (hD : ∀ x : quatOne a b, ∃! γ : quatUnitsOne a b, γ • x ∈ D) :
    quatVolConst ha hb ha0 hb0 = muQuatOneTam ha hb ha0 hb0 D :=
  muQuatClassTam_univ ha hb ha0 hb0 (IsFundamentalDomain.mk' hDm.nullMeasurableSet hD)

set_option maxHeartbeats 1000000 in
include ha hb ha0 hb0 in
/-- **Weil's Lemma 3.1.2, disintegration form.** For every fundamental domain $D$ of $\mathbb H^\times$ in
$(\mathbb H\otimes\mathbb A)^\times$ (for `tamQuat`) and every measurable $h : \mathbb R\to[0,\infty]$,
$$\int_D h(\log\|\operatorname{nrd}x\|_{\mathbb A})\,d\mu(x) = c_A'\int_{\mathbb R}h(u)\,du .$$
*Proof.* The integrand is $\mathbb H^\times$-invariant (product formula), so the integral does not depend on $D$
(`IsFundamentalDomain.setLIntegral_eq`); on $D = \mathrm{quatSplit}^{-1}(D^1\times\mathbb R_{>0})$ it is
$\mu^1(D^1)\int h\,du$ by the splitting $\mathrm{quatSplit}_*\mu = \mu^1\times dt/t$. -/
@[kb "weil1982" "§3.1, Lemma 3.1.2, p. 33 (the volume constant of A_𝔸^1/A^×)"]
theorem setLIntegral_quatFD_logNorm {D : Set (QuatAdele a b)ˣ}
    (hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b)) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x in D, h (Real.log (ideleNorm F (nrdUnit x))) ∂tamQuat a b = quatVolConst ha hb ha0 hb0 * ∫⁻ u, h u := by
  have hH := isHaarMeasure_tamQuat ha hb ha0 hb0
  obtain ⟨D₁, hD₁m, hD₁⟩ := exists_exact_quatOneFD a b
  set f : (QuatAdele a b)ˣ → ℝ≥0∞ := fun x => h (Multiplicative.toAdd (quatSplit a b x).2) with hf
  have hfx : ∀ x, h (Real.log (ideleNorm F (nrdUnit x))) = f x := fun x => by
    change _ = h (Multiplicative.toAdd (quatSplit a b x).2)
    rw [quatSplit_apply_snd, toAdd_ofAdd]
  simp_rw [hfx]
  have hinv : ∀ (γ : quatUnitsSub a b) x, f (γ • x) = f x := fun γ x => by
    simp only [hf]; rw [Subgroup.smul_def, smul_eq_mul, quatSplit_snd_mul γ.2]
  rw [hD.setLIntegral_eq (isFundamentalDomain_quatSplit_preimage hD₁m hD₁ _) f hinv]
  have hm : Measurable fun p : quatOne a b × Multiplicative ℝ => D₁.indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
      h (Multiplicative.toAdd p.2) :=
    ((measurable_const.indicator hD₁m).comp measurable_fst).mul (hh.comp (continuous_toAdd.measurable.comp measurable_snd))
  have hset : ∫⁻ x in quatSplit a b ⁻¹' (D₁ ×ˢ univ), f x ∂tamQuat a b =
      ∫⁻ x, (fun p : quatOne a b × Multiplicative ℝ => D₁.indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        h (Multiplicative.toAdd p.2)) (quatSplit a b x) ∂tamQuat a b := by
    rw [← lintegral_indicator ((hD₁m.prod MeasurableSet.univ).preimage measurable_quatSplit)]
    refine lintegral_congr fun x => ?_
    by_cases hx : (quatSplit a b x).1 ∈ D₁
    · rw [indicator_of_mem (by simp [hx])]
      change _ = D₁.indicator (fun _ => (1 : ℝ≥0∞)) (quatSplit a b x).1 * _
      rw [indicator_of_mem hx, one_mul]
    · rw [indicator_of_notMem (by simp [hx])]
      change _ = D₁.indicator (fun _ => (1 : ℝ≥0∞)) (quatSplit a b x).1 * _
      rw [indicator_of_notMem hx, zero_mul]
  rw [hset, ← lintegral_map hm measurable_quatSplit, map_quatSplit_tamQuat ha hb ha0 hb0]
  change ∫⁻ z : quatOne a b × Multiplicative ℝ, D₁.indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
    (h ∘ Multiplicative.toAdd) z.2 ∂_ = _
  rw [lintegral_prod_mul ((measurable_const.indicator hD₁m).aemeasurable)
      ((hh.comp continuous_toAdd.measurable).aemeasurable), lintegral_indicator_const hD₁m, one_mul,
    ← quatVolConst_eq ha hb ha0 hb0 hD₁m hD₁]
  congr 1
  rw [dtt, lintegral_map (hh.comp continuous_toAdd.measurable) continuous_ofAdd.measurable]
  rfl

include ha hb ha0 hb0 in
/-- **Lemma 3.1.2 in the variable $t = \|\operatorname{nrd}x\|_{\mathbb A}$**: $\int_D g(\|\operatorname{nrd}x\|)\,d\mu = c_A'\int_0^\infty g(t)\,dt/t$,
written with $t = e^u$. -/
theorem setLIntegral_quatFD_norm {D : Set (QuatAdele a b)ˣ}
    (hD : IsFundamentalDomain (quatUnitsSub a b) D (tamQuat a b)) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in D, g (ideleNorm F (nrdUnit x)) ∂tamQuat a b =
      quatVolConst ha hb ha0 hb0 * ∫⁻ u, g (Real.exp u) := by
  have := setLIntegral_quatFD_logNorm ha hb ha0 hb0 hD (hg.comp Real.measurable_exp)
  simp only [Function.comp_apply, Real.exp_log (ideleNorm_pos _)] at this
  exact this

end

end QuadFormsKB.Tamagawa.Measure.Weil
