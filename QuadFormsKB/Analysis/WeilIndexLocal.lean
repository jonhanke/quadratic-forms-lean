import QuadFormsKB.Analysis.WeilIndex

/-!
# The local identity for the Weil index

For a non-archimedean local field $K$ (as in `WeilIndex.lean`: ultrametric, proper, $2 \ne 0$), a standard character
$\psi$ and a Haar measure $\mu$, the Gauss integrals $\gamma(t)$ satisfy
$$\gamma(ab)\,\gamma(1) = (a, b)\,\gamma(a)\,\gamma(b), \qquad a, b \in K^\times$$
(`gaussInt_mul_identity`), where $\chi_a = (a, \cdot)$ is any $\pm1$-valued multiplicative function with
$\chi_a(s) = 1 \iff s = x^2 - ay^2$ (the Hilbert symbol; instantiated in `HasseNorm/WeilLocal.lean`). Dyadic places
are included: nothing below depends on the residue characteristic.

*Proof* for $a$ not a square. Let $N(x, y) = x^2 - ay^2$ on $K^2$ (anisotropic). For $\tau \in K^\times$,
$J(\tau) = \gamma(\tau)\gamma(-a\tau) = \int_{K^2}\psi(\tau N(z))\,dz$ (regularized over large regions). The image of the
Haar measure of $K^2$ under $N$ is $\kappa\,\mathbf 1_{N(K^2)}\,ds$ on annuli (`integral_comp_normForm`, by Fubini and the
change of variables $z \mapsto wz$ for $w \in K(\sqrt a)^\times$, whose modulus is $\operatorname{mod}(N(w))$). Writing
$\mathbf 1_{N(K^2)} = (1 + \chi_a)/2$ and substituting $s \mapsto s/\tau$ in the Gauss sum $\int\chi_a(s)\psi(s)\,ds$ gives
$J(\tau) = D + X\chi_a(\tau)\operatorname{mod}(\tau)^{-1}$; comparing with $J(\tau s^2) = \operatorname{mod}(s)^{-2}J(\tau)$
forces $D = 0$, so $J(\tau)\operatorname{mod}(\tau) = \chi_a(\tau)J(1)$. Combined with
$\gamma(t)\gamma(-t)\operatorname{mod}(t) = \gamma(1)\gamma(-1)$ this is the identity. For $a$ a square both sides agree by
scaling.

Sources: Weil, Acta Math. 111 (1964), §§14, 22–24 [unverified]; Rao (1993), Thm. A.4 [unverified].
-/

open MeasureTheory Metric
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Analysis.Weil

noncomputable section

/-! ### The norm form of $K(\sqrt a)$ -/

section NormFormDef

variable {K : Type*} [Field K] (a : K)

/-- The norm form $N(x, y) = x^2 - ay^2$ of $K(\sqrt a)/K$ on $K^2$. -/
def normForm (z : K × K) : K := z.1 ^ 2 - a * z.2 ^ 2

/-- Multiplication in $K(\sqrt a)$ in the basis $1, \sqrt a$: $(p + q\sqrt a)(x + y\sqrt a)$. -/
def mulE (w z : K × K) : K × K := (w.1 * z.1 + a * w.2 * z.2, w.2 * z.1 + w.1 * z.2)

lemma normForm_mulE (w z : K × K) : normForm a (mulE a w z) = normForm a w * normForm a z := by
  simp only [normForm, mulE]; ring

end NormFormDef

/-! ### Linear changes of variables in $K^2$ -/

section TwoDim

variable {K : Type*} [NontriviallyNormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

lemma map_prod_scale_fst {s : K} (hs : s ≠ 0) :
    (μ.prod μ).map (fun z : K × K => (s * z.1, z.2)) = ENNReal.ofReal (modK K s)⁻¹ • μ.prod μ := by
  have h := Measure.map_prod_map μ μ (measurable_const_mul s) measurable_id
  rw [map_mul_left_eq μ hs, Measure.map_id, Measure.prod_smul_left] at h
  rw [h]; rfl

lemma map_prod_scale_snd {s : K} (hs : s ≠ 0) :
    (μ.prod μ).map (fun z : K × K => (z.1, s * z.2)) = ENNReal.ofReal (modK K s)⁻¹ • μ.prod μ := by
  have h := Measure.map_prod_map μ μ measurable_id (measurable_const_mul s)
  rw [map_mul_left_eq μ hs, Measure.map_id, Measure.prod_smul_right] at h
  rw [h]; rfl

lemma map_prod_shear_snd (p : K) :
    (μ.prod μ).map (fun z : K × K => (z.1, z.2 + p * z.1)) = μ.prod μ := by
  have h := (MeasurePreserving.id μ).skew_product (μc := μ) (μd := μ) (g := fun x y => y + p * x)
    (by fun_prop) (Filter.Eventually.of_forall fun x => map_add_right_eq_self μ (p * x))
  exact h.map_eq

lemma map_prod_swap_self : (μ.prod μ).map Prod.swap = μ.prod μ := Measure.prod_swap

lemma map_prod_shear_fst (p : K) :
    (μ.prod μ).map (fun z : K × K => (z.1 + p * z.2, z.2)) = μ.prod μ := by
  have : (fun z : K × K => (z.1 + p * z.2, z.2)) =
      Prod.swap ∘ (fun z : K × K => (z.1, z.2 + p * z.1)) ∘ Prod.swap := by
    ext z <;> simp
  rw [this, ← Measure.map_map measurable_swap ((by fun_prop : Measurable fun z : K × K =>
      (z.1, z.2 + p * z.1)).comp measurable_swap), ← Measure.map_map (by fun_prop) measurable_swap,
    map_prod_swap_self, map_prod_shear_snd, map_prod_swap_self]

variable (a : K)

lemma measurable_mulE (w : K × K) : Measurable (mulE a w) := by
  unfold mulE; fun_prop

/-- **The modulus of multiplication by $w \in K(\sqrt a)^\times$ on $K^2$ is $\operatorname{mod}(N(w))$:** the image of
$\mu\otimes\mu$ under $z \mapsto wz$ is $\operatorname{mod}(N(w))^{-1}\,\mu\otimes\mu$ (for $N(w) \ne 0$). -/
theorem map_mulE {w : K × K} (hN : normForm a w ≠ 0) :
    (μ.prod μ).map (mulE a w) = ENNReal.ofReal (modK K (normForm a w))⁻¹ • μ.prod μ := by
  obtain ⟨p, q⟩ := w
  by_cases hq : q = 0
  · subst hq
    have hp : p ≠ 0 := by rintro rfl; simp [normForm] at hN
    have hfun : mulE a (p, 0) = (fun z : K × K => (z.1, p * z.2)) ∘ (fun z : K × K => (p * z.1, z.2)) := by
      ext z <;> simp [mulE]
    rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_prod_scale_fst μ hp,
      Measure.map_smul, map_prod_scale_snd μ hp, smul_smul, ← ENNReal.ofReal_mul (by
        exact inv_nonneg.mpr (modK_pos hp).le), ← mul_inv, ← modK_mul hp hp]
    · congr 3
      simp [normForm]; ring
    · fun_prop
  · set n := normForm a (p, q) with hn
    have hnq : -(n / q) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hN hq)
    have hfun : mulE a (p, q) = Prod.swap ∘ (fun z : K × K => (z.1, z.2 + p / q * z.1)) ∘
        (fun z : K × K => (z.1, -(n / q) * z.2)) ∘ (fun z : K × K => (z.1 + p * z.2, z.2)) ∘
          (fun z : K × K => (q * z.1, z.2)) := by
      ext z <;> simp only [mulE, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, hn, normForm] <;>
        field_simp <;> ring
    rw [hfun, ← Measure.map_map measurable_swap (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
      map_prod_scale_fst μ hq, Measure.map_smul, map_prod_shear_fst, Measure.map_smul,
      map_prod_scale_snd μ hnq, smul_smul, Measure.map_smul, map_prod_shear_snd, Measure.map_smul,
      map_prod_swap_self, ← ENNReal.ofReal_mul (inv_nonneg.mpr (modK_pos hq).le), ← mul_inv,
      modK_neg, mul_comm (modK K q), ← modK_mul (div_ne_zero hN hq) hq, div_mul_cancel₀ _ hq]
    all_goals fun_prop

end TwoDim

/-! ### The norm form: anisotropy and bounds -/

section NormBounds

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] {a : K}

lemma normForm_smul (c : K) (z : K × K) : normForm a (c • z) = c ^ 2 * normForm a z := by
  simp only [normForm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma normForm_ne_zero (ha : ¬ IsSquare a) {z : K × K} (hz : z ≠ 0) : normForm a z ≠ 0 := by
  obtain ⟨x, y⟩ := z
  intro h
  simp only [normForm] at h
  by_cases hy : y = 0
  · subst hy
    have : x = 0 := by simpa using h
    exact hz (by simp [this])
  · exact ha ⟨x / y, by field_simp; linear_combination -h⟩

lemma continuous_normForm : Continuous (normForm (K := K) a) := by unfold normForm; fun_prop

/-- **Anisotropy, quantitatively:** $\|N(z)\| \ge c\|z\|^2$ for some $c > 0$ when $a$ is not a square (compactness of
the annulus $\|\pi\| \le \|z\| \le 1$ and scaling by powers of $\pi$). -/
theorem exists_normForm_lower (ha : ¬ IsSquare a) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : K × K, c * ‖z‖ ^ 2 ≤ ‖normForm a z‖ := by
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one K
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set A : Set (K × K) := {z | ‖π‖ ≤ ‖z‖} ∩ closedBall 0 1
  have hAc : IsCompact A :=
    (isCompact_closedBall 0 1).inter_left (isClosed_le continuous_const continuous_norm)
  have hAne : A.Nonempty := ⟨(1, 0), by
    refine ⟨?_, ?_⟩
    · show ‖π‖ ≤ ‖((1 : K), (0 : K))‖; simp [Prod.norm_def]; exact hπ1.le
    · simp [Prod.norm_def]⟩
  obtain ⟨z₀, hz₀A, hmin⟩ := hAc.exists_isMinOn hAne (continuous_norm.comp (continuous_normForm (a := a))).continuousOn
  have hz₀ : z₀ ≠ 0 := by
    rintro rfl
    have := hz₀A.1; simp at this; exact hπne this
  set m := ‖normForm a z₀‖
  have hm : 0 < m := norm_pos_iff.mpr (normForm_ne_zero ha hz₀)
  refine ⟨m, hm, fun z => ?_⟩
  by_cases hz : z = 0
  · simp [hz, normForm]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hy : (1 : ℝ) < ‖π‖⁻¹ := one_lt_inv₀ hπ0 |>.mpr hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hzn hy
  set z' : K × K := (π ^ (n + 1)) • z
  have hpn : ‖π ^ (n + 1)‖ = ‖π‖ ^ (n + 1) := norm_zpow _ _
  have hz' : ‖z'‖ = ‖π‖ ^ (n + 1) * ‖z‖ := by rw [norm_smul, hpn]
  have hπn : ‖π‖ ^ (n + 1) * ‖π‖⁻¹ ^ (n + 1) = 1 := by
    rw [← mul_zpow, mul_inv_cancel₀ hπ0.ne', one_zpow]
  have hz'A : z' ∈ A := by
    refine ⟨?_, ?_⟩
    · show ‖π‖ ≤ ‖z'‖
      rw [hz']
      have : ‖π‖⁻¹ ^ n < ‖z‖ := hn1
      calc ‖π‖ = ‖π‖ ^ (n + 1) * ‖π‖⁻¹ ^ n := by
            rw [zpow_add₀ hπ0.ne', zpow_one, inv_zpow', mul_comm (‖π‖ ^ n), mul_assoc,
              ← zpow_add₀ hπ0.ne', add_neg_cancel, zpow_zero, mul_one]
        _ ≤ ‖π‖ ^ (n + 1) * ‖z‖ := by gcongr
    · rw [mem_closedBall, dist_zero_right, hz']
      calc ‖π‖ ^ (n + 1) * ‖z‖ ≤ ‖π‖ ^ (n + 1) * ‖π‖⁻¹ ^ (n + 1) := by gcongr
        _ = 1 := hπn
  have hle := hmin hz'A
  simp only [Set.mem_ofPred_eq, Function.comp_apply] at hle
  rw [normForm_smul, norm_mul, norm_pow, hpn] at hle
  have hz2 : ‖z‖ ^ 2 ≤ (‖π‖⁻¹ ^ (n + 1)) ^ 2 := by gcongr
  have hpos : 0 < ‖π‖ ^ (n + 1) := zpow_pos hπ0 _
  have key : (‖π‖ ^ (n + 1)) ^ 2 * (‖π‖⁻¹ ^ (n + 1)) ^ 2 = 1 := by rw [← mul_pow, hπn, one_pow]
  calc m * ‖z‖ ^ 2 ≤ m * (‖π‖⁻¹ ^ (n + 1)) ^ 2 := by gcongr
    _ ≤ (‖π‖ ^ (n + 1)) ^ 2 * ‖normForm a z‖ * (‖π‖⁻¹ ^ (n + 1)) ^ 2 := by gcongr
    _ = ‖normForm a z‖ := by rw [mul_comm _ ‖normForm a z‖, mul_assoc, key, mul_one]

lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

lemma norm_two_le_one : ‖(2 : K)‖ ≤ 1 := by
  rw [show (2 : K) = ((2 : ℕ) : K) by norm_num]; exact IsUltrametricDist.norm_natCast_le_one _ _

lemma norm_mul_le_of_le {x y : K} {r s : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ s) (hr : 0 ≤ r) :
    ‖x * y‖ ≤ r * s := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) hr

/-- $\|N(z)\| \le \max(1, \|a\|)\,\|z\|^2$. -/
lemma norm_normForm_le (z : K × K) : ‖normForm a z‖ ≤ max 1 ‖a‖ * ‖z‖ ^ 2 := by
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hM : (1 : ℝ) ≤ max 1 ‖a‖ := le_max_left _ _
  refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
  · rw [norm_pow]
    calc ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := by gcongr
      _ ≤ max 1 ‖a‖ * ‖z‖ ^ 2 := le_mul_of_one_le_left (by positivity) hM
  · rw [norm_mul, norm_pow]
    calc ‖a‖ * ‖z.2‖ ^ 2 ≤ max 1 ‖a‖ * ‖z‖ ^ 2 := by gcongr; exact le_max_right _ _

/-- The polarization: $N(z + h) = N(z) + 2(z_1h_1 - a z_2h_2) + N(h)$. -/
lemma normForm_add (z h : K × K) :
    normForm a (z + h) = normForm a z + 2 * (z.1 * h.1 - a * z.2 * h.2) + normForm a h := by
  simp only [normForm, Prod.fst_add, Prod.snd_add]; ring

lemma norm_polar_le (z h : K × K) :
    ‖2 * (z.1 * h.1 - a * z.2 * h.2)‖ ≤ max 1 ‖a‖ * (‖z‖ * ‖h‖) := by
  have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hh1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have hh2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_two_le_one).trans
    ((norm_sub_le_max' _ _).trans (max_le ?_ ?_))
  · rw [norm_mul]
    calc ‖z.1‖ * ‖h.1‖ ≤ ‖z‖ * ‖h‖ := by gcongr
      _ ≤ max 1 ‖a‖ * (‖z‖ * ‖h‖) := le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · rw [norm_mul, norm_mul]
    calc ‖a‖ * ‖z.2‖ * ‖h.2‖ = ‖a‖ * (‖z.2‖ * ‖h.2‖) := by ring
      _ ≤ max 1 ‖a‖ * (‖z‖ * ‖h‖) := by gcongr; exact le_max_right _ _

end NormBounds

/-! ### The modulus as a function of the norm -/

section ModNorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

lemma image_mul_closedBall {s : K} (hs : s ≠ 0) (r : ℝ) :
    (fun x => s * x) '' closedBall (0 : K) r = closedBall 0 (‖s‖ * r) := by
  ext y
  simp only [Set.mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · intro hy
    refine ⟨y / s, ?_, by field_simp⟩
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hs)]; linarith [mul_comm ‖s‖ r]

lemma measureReal_closedBall_one_pos : 0 < μ.real (closedBall (0 : K) 1) := by
  have h := measure_bsub_pos μ (K := K) (R := 1) one_pos
  rw [coe_bsub] at h
  exact ENNReal.toReal_pos h.ne' (isCompact_closedBall _ _).measure_lt_top.ne

/-- $\operatorname{mod}(s) = \mu(B_{\|s\|})/\mu(B_1)$. -/
lemma modK_eq_ratio {s : K} (hs : s ≠ 0) :
    modK K s = μ.real (closedBall (0 : K) ‖s‖) / μ.real (closedBall (0 : K) 1) := by
  have h := measure_smul_eq μ hs (closedBall (0 : K) 1)
  rw [image_mul_closedBall hs, mul_one] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (modK_pos hs).le] at h'
  rw [eq_div_iff (measureReal_closedBall_one_pos μ).ne']
  exact h'.symm

lemma measureReal_closedBall_mono {r r' : ℝ} (h : r ≤ r') :
    μ.real (closedBall (0 : K) r) ≤ μ.real (closedBall (0 : K) r') :=
  measureReal_mono (closedBall_subset_closedBall h) (isCompact_closedBall _ _).measure_lt_top.ne

omit [μ.IsAddHaarMeasure] in
lemma modK_mono {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) (h : ‖s‖ ≤ ‖t‖) : modK K s ≤ modK K t := by
  let μ : Measure K := Measure.addHaar
  rw [modK_eq_ratio μ hs, modK_eq_ratio μ ht]
  exact div_le_div_of_nonneg_right (measureReal_closedBall_mono μ h)
    (measureReal_closedBall_one_pos μ).le

lemma modK_eq_of_norm_eq {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) (h : ‖s‖ = ‖t‖) : modK K s = modK K t :=
  le_antisymm (modK_mono hs ht h.le) (modK_mono ht hs h.ge)

lemma modK_of_norm_eq_one {u : K} (hu : ‖u‖ = 1) : modK K u = 1 := by
  rw [modK_eq_of_norm_eq (norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)) one_ne_zero
    (by rw [hu, norm_one]), modK_one]

omit [μ.IsAddHaarMeasure] in
lemma measurable_modK : Measurable (modK K) := by
  classical
  let μ : Measure K := Measure.addHaar
  have hg : Monotone fun r : ℝ => μ.real (closedBall (0 : K) r) / μ.real (closedBall (0 : K) 1) :=
    fun r r' h => div_le_div_of_nonneg_right (measureReal_closedBall_mono μ h)
      (measureReal_closedBall_one_pos μ).le
  have : modK K = fun s => if s = 0 then 0 else
      (fun r : ℝ => μ.real (closedBall (0 : K) r) / μ.real (closedBall (0 : K) 1)) ‖s‖ := by
    ext s
    by_cases hs : s = 0
    · simp [hs, modK]
    · simp only [hs, ↓reduceIte]; exact modK_eq_ratio μ hs
  rw [this]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (hg.measurable.comp measurable_norm)

end ModNorm

/-! ### The set of norms -/

section NormSet

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] (a : K)

/-- The norms $N(K(\sqrt a))$ $= \{x^2 - ay^2\}$ (including $0$). -/
def normSet : Set K := Set.range (normForm a)

variable {a}

lemma mul_mem_normSet {s t : K} (hs : s ∈ normSet a) (ht : t ∈ normSet a) : s * t ∈ normSet a := by
  obtain ⟨z, rfl⟩ := hs; obtain ⟨w, rfl⟩ := ht
  exact ⟨mulE a z w, normForm_mulE a z w⟩

lemma sq_mem_normSet (c : K) : c ^ 2 ∈ normSet a := ⟨(c, 0), by simp [normForm]⟩

lemma mem_normSet_of_isSquare {u : K} (hu : IsSquare u) : u ∈ normSet a := by
  obtain ⟨c, rfl⟩ := hu; rw [← sq]; exact sq_mem_normSet c

lemma norm_eq_of_norm_sub_lt {x y : K} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := -y) (by simpa using hne)
  rw [← sub_eq_add_neg, norm_neg] at this
  rw [this] at h
  exact absurd h (not_lt.mpr (le_max_right _ _))

/-- For $\rho < 1$: $\|n - s\| \le \rho\|s\|$ iff $s = nu$ with $\|u - 1\| \le \rho$ (for $n \ne 0$). -/
lemma norm_sub_le_iff_mem_image {n s : K} (hn : n ≠ 0) {ρ : ℝ} (hρ1 : ρ < 1) :
    ‖n - s‖ ≤ ρ * ‖s‖ ↔ s ∈ (fun u => n * u) '' closedBall 1 ρ := by
  constructor
  · intro h
    have hs : s ≠ 0 := by
      rintro rfl; simp at h; exact hn h
    have hsn : ‖s‖ = ‖n‖ :=
      (norm_eq_of_norm_sub_lt (lt_of_le_of_lt h (by nlinarith [norm_pos_iff.mpr hs]))).symm
    refine ⟨s / n, ?_, by field_simp⟩
    rw [mem_closedBall, dist_eq_norm, show s / n - 1 = (s - n) / n by field_simp, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hn), norm_sub_rev, ← hsn]
    exact h
  · rintro ⟨u, hu, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hu
    have hu1 : ‖u‖ = 1 := by
      rw [← norm_one (α := K)]; exact norm_eq_of_norm_sub_lt (by rw [norm_one]; linarith)
    rw [norm_mul, hu1, mul_one, show n - n * u = n * (1 - u) by ring, norm_mul, norm_sub_rev]
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)

/-- Variant: $\|n - s\| \le \rho\|n\|$ iff $s \in nU$. -/
lemma norm_sub_le_iff_mem_image' {n s : K} (hn : n ≠ 0) {ρ : ℝ} (hρ1 : ρ < 1) :
    ‖n - s‖ ≤ ρ * ‖n‖ ↔ s ∈ (fun u => n * u) '' closedBall 1 ρ := by
  rw [← norm_sub_le_iff_mem_image hn hρ1]
  constructor
  · intro h
    have hsn : ‖s‖ = ‖n‖ := norm_eq_of_norm_sub_lt (by
      rw [norm_sub_rev]; exact lt_of_le_of_lt h (by nlinarith [norm_pos_iff.mpr hn]))
    rwa [hsn]
  · intro h
    have hs : s ≠ 0 := by rintro rfl; simp at h; exact hn h
    have hsn : ‖s‖ = ‖n‖ :=
      (norm_eq_of_norm_sub_lt (lt_of_le_of_lt h (by nlinarith [norm_pos_iff.mpr hs]))).symm
    rwa [← hsn]

lemma isClosed_image_mul {n : K} (hn : n ≠ 0) {S : Set K} (hS : IsClosed S) :
    IsClosed ((fun u => n * u) '' S) := (Homeomorph.mulLeft₀ n hn).isClosedMap S hS

end NormSet

/-! ### The image of the Haar measure of $K^2$ under the norm form -/

section Pushforward

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] {a : K}

/-- The constant $\kappa_\rho = \operatorname{vol}(N^{-1}(U_\rho))/\operatorname{vol}(U_\rho)$, $U_\rho = \{\|u - 1\| \le \rho\}$. -/
def kappaN (a : K) (ρ : ℝ) : ℝ :=
  (μ.prod μ).real (normForm a ⁻¹' closedBall 1 ρ) / μ.real (closedBall (1 : K) ρ)

lemma measurableSet_normForm_preimage {S : Set K} (hS : MeasurableSet S) :
    MeasurableSet (normForm a ⁻¹' S) := continuous_normForm.measurable hS

lemma isCompact_normForm_preimage_closedBall (ha : ¬ IsSquare a) (T : ℝ) :
    IsCompact (normForm a ⁻¹' closedBall 0 T) := by
  obtain ⟨c, hc, hlow⟩ := exists_normForm_lower (a := a) ha
  refine (isCompact_closedBall (0 : K × K) (Real.sqrt (|T| / c))).of_isClosed_subset
    (isClosed_closedBall.preimage continuous_normForm) fun z hz => ?_
  rw [Set.mem_preimage, mem_closedBall, dist_zero_right] at hz
  rw [mem_closedBall, dist_zero_right]
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ hc]
  nlinarith [hlow z, le_abs_self T]

/-- **The norm-form fibres scale by the modulus:** for $s = N(z_0) \ne 0$,
$\operatorname{vol}(N^{-1}(sU)) = \operatorname{mod}(s)\operatorname{vol}(N^{-1}(U))$ (change of variables $z \mapsto z_0^{-1}z$). -/
lemma measure_normForm_preimage_mul (ha : ¬ IsSquare a) {s : K} (hs : s ∈ normSet a) (hs0 : s ≠ 0)
    (U : Set K) (hU : MeasurableSet U) :
    (μ.prod μ) (normForm a ⁻¹' ((fun u => s * u) '' U)) =
      ENNReal.ofReal (modK K s) * (μ.prod μ) (normForm a ⁻¹' U) := by
  obtain ⟨z₀, rfl⟩ := hs
  set s := normForm a z₀
  set w : K × K := (z₀.1 / s, -z₀.2 / s)
  have hNw : normForm a w = s⁻¹ := by
    simp only [normForm, w, s] at hs0 ⊢; field_simp
  have hNw0 : normForm a w ≠ 0 := by rw [hNw]; exact inv_ne_zero hs0
  have hset : normForm a ⁻¹' ((fun u => s * u) '' U) = mulE a w ⁻¹' (normForm a ⁻¹' U) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_image, normForm_mulE, hNw]
    constructor
    · rintro ⟨u, hu, hz⟩; rw [← hz]; field_simp; exact hu
    · intro hz; exact ⟨s⁻¹ * normForm a z, hz, by field_simp⟩
  rw [hset, ← Measure.map_apply (measurable_mulE a w) (measurableSet_normForm_preimage hU),
    map_mulE μ a hNw0, Measure.smul_apply, smul_eq_mul, hNw, modK_inv hs0, inv_inv]

lemma normForm_preimage_mul_eq_empty {ρ : ℝ} (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u)
    {s : K} (hs : s ∉ normSet a) :
    normForm a ⁻¹' ((fun u => s * u) '' closedBall 1 ρ) = ∅ := by
  ext z
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro u hu hz
  apply hs
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_one] at hu
    linarith
  have : s = normForm a z * u⁻¹ := by rw [← hz]; field_simp
  rw [this]
  refine mul_mem_normSet ⟨z, rfl⟩ ?_
  rw [show u⁻¹ = u * (u⁻¹) ^ 2 by field_simp]
  exact mul_mem_normSet (mem_normSet_of_isSquare (hsq u hu)) (sq_mem_normSet _)

/-- **The image of the Haar measure of $K^2$ under $N$ on annuli** (for $a$ not a square): for $h$ bounded,
measurable, supported in $r \le \|s\| \le T$ ($r > 0$) and invariant under $U_\rho$ ($\rho < 1$, $U_\rho$ consisting of
squares),
$$\int_{K^2} h(N(z))\,dz = \kappa_\rho\int_K \mathbf 1_{N(K^2)}(s)\,h(s)\,ds.$$
*Proof:* Fubini on $K^2 \times K$ for $F(z, s) = h(s)\,\mathbf 1[N(z) \in sU_\rho]/(\operatorname{mod}(s)\operatorname{vol}(U_\rho))$:
the $s$-slices are $N(z)U_\rho$ (integral $h(N(z))$), the $z$-slices are $N^{-1}(sU_\rho)$, of volume
$\operatorname{mod}(s)\operatorname{vol}(N^{-1}U_\rho)$ for $s \in N(K^2)$ (`measure_normForm_preimage_mul`) and empty otherwise. -/
theorem integral_comp_normForm (ha : ¬ IsSquare a) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u)
    {h : K → ℂ} (hh : Measurable h) {C : ℝ} (hC : ∀ s, ‖h s‖ ≤ C) {r T : ℝ} (hr : 0 < r)
    (hsupp : ∀ s, h s ≠ 0 → r ≤ ‖s‖ ∧ ‖s‖ ≤ T)
    (hinv : ∀ s u, u ∈ closedBall (1 : K) ρ → h (s * u) = h s) :
    ∫ z, h (normForm a z) ∂(μ.prod μ) = kappaN μ a ρ * ∫ s, (normSet a).indicator h s ∂μ := by
  classical
  set U : Set K := closedBall 1 ρ with hUdef
  set μU : ℝ := μ.real U with hμU
  have hUpos : 0 < μU := by
    refine ENNReal.toReal_pos ?_ (isCompact_closedBall _ _).measure_lt_top.ne
    exact ((IsUltrametricDist.isOpen_closedBall (1 : K) hρ.ne').measure_pos μ
      ⟨1, mem_closedBall_self hρ.le⟩).ne'
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [← norm_one (α := K)]
    refine norm_eq_of_norm_sub_lt ?_
    rw [norm_one]; rw [mem_closedBall, dist_eq_norm] at hu; linarith
  have hU0 : ∀ u ∈ U, u ≠ 0 := fun u hu h0 => by
    have := hU1 u hu; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h0 : h 0 = 0 := by
    by_contra hne; have := (hsupp 0 hne).1; simp at this; linarith
  set Cs : Set ((K × K) × K) := {p | ‖normForm a p.1 - p.2‖ ≤ ρ * ‖p.2‖} with hCsdef
  have hCs : MeasurableSet Cs :=
    (isClosed_le (((continuous_normForm (a := a)).comp continuous_fst).sub continuous_snd).norm
      (continuous_const.mul continuous_snd.norm)).measurableSet
  set Fn : (K × K) × K → ℂ := fun p => h p.2 * Cs.indicator 1 p * ((modK K p.2 * μU)⁻¹ : ℝ) with hFn
  -- the `s`-integral
  have hin_s : ∀ z : K × K, ∫ s, Fn (z, s) ∂μ = h (normForm a z) := by
    intro z
    by_cases hz : normForm a z = 0
    · rw [hz, h0]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
      show h s * Cs.indicator 1 (z, s) * _ = 0
      by_cases hs : s = 0
      · rw [hs, h0, zero_mul, zero_mul]
      · rw [Set.indicator_of_notMem, mul_zero, zero_mul]
        simp only [hCsdef, Set.mem_ofPred_eq, hz, zero_sub, norm_neg, not_le]
        nlinarith [norm_pos_iff.mpr hs]
    · set n := normForm a z
      have hfun : ∀ s, Fn (z, s) = ((fun u => n * u) '' U).indicator
          (fun _ => h n * ((modK K n * μU)⁻¹ : ℝ)) s := by
        intro s
        by_cases hs : s ∈ (fun u => n * u) '' U
        · rw [Set.indicator_of_mem hs]
          obtain ⟨u, hu, rfl⟩ := hs
          show h (n * u) * Cs.indicator 1 (z, n * u) * _ = _
          rw [Set.indicator_of_mem (show (z, n * u) ∈ Cs from
              (norm_sub_le_iff_mem_image hz hρ1).mpr ⟨u, hu, rfl⟩), Pi.one_apply,
            mul_one, hinv n u hu, modK_mul hz (hU0 u hu), modK_of_norm_eq_one (hU1 u hu), mul_one]
        · rw [Set.indicator_of_notMem hs]
          show h s * Cs.indicator 1 (z, s) * _ = 0
          rw [Set.indicator_of_notMem (show (z, s) ∉ Cs from
              fun h' => hs ((norm_sub_le_iff_mem_image hz hρ1).mp h')), mul_zero, zero_mul]
      simp_rw [hfun]
      rw [integral_indicator_const _ (isClosed_image_mul hz isClosed_closedBall).measurableSet,
        Measure.real, measure_smul_eq μ hz, ENNReal.toReal_mul, ENNReal.toReal_ofReal (modK_pos hz).le,
        ← Measure.real, Complex.real_smul]
      have hm : (modK K n : ℂ) ≠ 0 := by exact_mod_cast (modK_pos hz).ne'
      have hμ0 : (μU : ℂ) ≠ 0 := by exact_mod_cast hUpos.ne'
      show ((modK K n * μU : ℝ) : ℂ) * (h n * ((modK K n * μU)⁻¹ : ℝ)) = h n
      push_cast
      field_simp
  -- the `z`-integral
  have hin_z : ∀ s : K, ∫ z, Fn (z, s) ∂(μ.prod μ) = kappaN μ a ρ * (normSet a).indicator h s := by
    intro s
    by_cases hs0 : s = 0
    · subst hs0
      rw [Set.indicator_of_mem (show (0 : K) ∈ normSet a from ⟨0, by simp [normForm]⟩), h0, mul_zero]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
      show h 0 * _ * _ = 0
      rw [h0, zero_mul, zero_mul]
    have hslice : ∀ z, (z, s) ∈ Cs ↔ z ∈ normForm a ⁻¹' ((fun u => s * u) '' U) := by
      intro z
      show ‖normForm a z - s‖ ≤ ρ * ‖s‖ ↔ _
      rw [norm_sub_rev]; exact norm_sub_le_iff_mem_image' hs0 hρ1
    have hfun : ∀ z, Fn (z, s) = (normForm a ⁻¹' ((fun u => s * u) '' U)).indicator
        (fun _ => h s * ((modK K s * μU)⁻¹ : ℝ)) z := by
      intro z
      show h s * Cs.indicator 1 (z, s) * _ = _
      by_cases hz : z ∈ normForm a ⁻¹' ((fun u => s * u) '' U)
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hslice z).mpr hz), Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hslice z).mp h')),
          mul_zero, zero_mul]
    simp_rw [hfun]
    rw [integral_indicator_const _ (measurableSet_normForm_preimage
      (isClosed_image_mul hs0 isClosed_closedBall).measurableSet), Complex.real_smul]
    by_cases hsN : s ∈ normSet a
    · rw [Set.indicator_of_mem hsN, Measure.real, measure_normForm_preimage_mul μ ha hsN hs0 U
        isClosed_closedBall.measurableSet, ENNReal.toReal_mul, ENNReal.toReal_ofReal (modK_pos hs0).le,
        kappaN, ← Measure.real]
      have hm : (modK K s : ℂ) ≠ 0 := by exact_mod_cast (modK_pos hs0).ne'
      have hμ0 : (μU : ℂ) ≠ 0 := by exact_mod_cast hUpos.ne'
      show ((modK K s * (μ.prod μ).real (normForm a ⁻¹' U) : ℝ) : ℂ) * (h s * ((modK K s * μU)⁻¹ : ℝ)) =
        (((μ.prod μ).real (normForm a ⁻¹' U) / μU : ℝ) : ℂ) * h s
      push_cast
      field_simp
    · rw [Set.indicator_of_notMem hsN, normForm_preimage_mul_eq_empty hρ1 hsq hsN]
      simp
  -- integrability
  obtain ⟨sr, hsr0, hsrr⟩ := NormedField.exists_norm_lt K hr
  have hsrne : sr ≠ 0 := norm_pos_iff.mp hsr0
  set M : ℝ := C * (modK K sr * μU)⁻¹
  have hbound : ∀ p, ‖Fn p‖ ≤ M := by
    intro p
    show ‖h p.2 * Cs.indicator 1 p * ((modK K p.2 * μU)⁻¹ : ℝ)‖ ≤ M
    by_cases hp : h p.2 = 0
    · rw [hp, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hC 0)) (inv_nonneg.mpr (mul_pos (modK_pos hsrne) hUpos).le)
    have hp2 : p.2 ≠ 0 := fun h' => hp (by rw [h', h0])
    have hmod : modK K sr ≤ modK K p.2 := modK_mono hsrne hp2 (hsrr.le.trans (hsupp _ hp).1)
    have hpos : 0 < modK K p.2 * μU := mul_pos (modK_pos hp2) hUpos
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    have hind : ‖Cs.indicator (1 : (K × K) × K → ℂ) p‖ ≤ 1 := by
      by_cases hpc : p ∈ Cs
      · rw [Set.indicator_of_mem hpc]; simp
      · rw [Set.indicator_of_notMem hpc]; simp
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    calc ‖h p.2‖ * ‖Cs.indicator 1 p‖ * (modK K p.2 * μU)⁻¹ ≤ C * 1 * (modK K sr * μU)⁻¹ :=
          mul_le_mul (mul_le_mul (hC _) hind (norm_nonneg _) hC0)
            (inv_anti₀ (mul_pos (modK_pos hsrne) hUpos) (mul_le_mul_of_nonneg_right hmod hUpos.le))
            (inv_nonneg.mpr hpos.le) (by positivity)
      _ = M := by ring
  set S : Set ((K × K) × K) := (normForm a ⁻¹' closedBall 0 T) ×ˢ closedBall 0 T
  have hSm : MeasurableSet S :=
    (measurableSet_normForm_preimage measurableSet_closedBall).prod measurableSet_closedBall
  have hSf : ((μ.prod μ).prod μ) S ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (isCompact_normForm_preimage_closedBall ha T).measure_lt_top.ne
      (isCompact_closedBall _ _).measure_lt_top.ne
  have hmeasF : Measurable Fn := by
    refine ((hh.comp measurable_snd).mul (measurable_const.indicator hCs)).mul ?_
    exact Complex.measurable_ofReal.comp
      (((measurable_modK.comp measurable_snd).mul measurable_const).inv)
  have hsuppF : ∀ p ∉ S, Fn p = 0 := by
    intro p hp
    show h p.2 * Cs.indicator 1 p * _ = 0
    by_cases hp2 : h p.2 = 0
    · rw [hp2, zero_mul, zero_mul]
    by_cases hpc : p ∈ Cs
    · exfalso
      apply hp
      have hT := (hsupp _ hp2).2
      refine ⟨?_, by rw [mem_closedBall, dist_zero_right]; exact hT⟩
      rw [Set.mem_preimage, mem_closedBall, dist_zero_right]
      have : ‖normForm a p.1‖ ≤ max ‖normForm a p.1 - p.2‖ ‖p.2‖ := by
        have := IsUltrametricDist.norm_add_le_max (normForm a p.1 - p.2) p.2
        rwa [sub_add_cancel] at this
      refine this.trans (max_le ?_ hT)
      have hpc' : ‖normForm a p.1 - p.2‖ ≤ ρ * ‖p.2‖ := hpc
      nlinarith [norm_nonneg p.2]
    · rw [Set.indicator_of_notMem hpc, mul_zero, zero_mul]
  have hint : Integrable Fn ((μ.prod μ).prod μ) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsuppF
    exact Measure.integrableOn_of_bounded hSf hmeasF.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hswap := integral_integral_swap (f := fun z s => Fn (z, s)) hint
  calc ∫ z, h (normForm a z) ∂(μ.prod μ) = ∫ z, ∫ s, Fn (z, s) ∂μ ∂(μ.prod μ) := by
        simp_rw [hin_s]
    _ = ∫ s, ∫ z, Fn (z, s) ∂(μ.prod μ) ∂μ := hswap
    _ = ∫ s, kappaN μ a ρ * (normSet a).indicator h s ∂μ := by simp_rw [hin_z]
    _ = kappaN μ a ρ * ∫ s, (normSet a).indicator h s ∂μ := integral_const_mul _ _

end Pushforward

/-! ### Regularizing the two-dimensional Gauss integral -/

section Regions

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} {a : K}

/-- $\gamma(\tau)\gamma(-a\tau)$ as a two-dimensional integral over $B_R \times B_R$. -/
lemma gaussI_mul_gaussI_eq (τ : K) (R : ℝ≥0) :
    gaussI μ ψ τ R * gaussI μ ψ (-a * τ) R =
      ∫ z in (bsub K R : Set K) ×ˢ (bsub K R : Set K), (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) := by
  rw [gaussI, gaussI, ← setIntegral_prod_mul]
  refine setIntegral_congr_fun ((measurableSet_bsub R).prod (measurableSet_bsub R)) fun z _ => ?_
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [normForm]; ring

variable (K) in
/-- The product subgroup $B_\varepsilon \times B_\varepsilon$ of $K^2$. -/
def bsub2 (ε : ℝ≥0) : AddSubgroup (K × K) := (bsub K ε).prod (bsub K ε)

lemma coe_bsub2 (ε : ℝ≥0) : (bsub2 K ε : Set (K × K)) = (bsub K ε : Set K) ×ˢ (bsub K ε : Set K) :=
  AddSubgroup.coe_prod _ _

lemma norm_le_of_mem_bsub2 {ε : ℝ≥0} {h : K × K} (hh : h ∈ bsub2 K ε) : ‖h‖ ≤ ε := by
  rw [← SetLike.mem_coe, coe_bsub2] at hh
  rw [Prod.norm_def]; exact max_le hh.1 hh.2

/-- **Region independence for the norm-form Gauss integral:** for $\tau \ne 0$ and $a$ not a square, the integrals
of $\psi(\tau N(z))$ over $B_R \times B_R$ and over $N^{-1}(B_T)$ agree once $R, T$ are large. -/
theorem setIntegral_box_eq_normBall (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) (ha : ¬ IsSquare a)
    {τ : K} (hτ : τ ≠ 0) :
    ∃ R₀ T₀ : ℝ, ∀ (R : ℝ≥0) (T : ℝ), R₀ ≤ R → T₀ ≤ T →
      ∫ z in (bsub K R : Set K) ×ˢ (bsub K R : Set K), (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) =
        ∫ z in normForm a ⁻¹' closedBall 0 T, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) := by
  obtain ⟨r₀, hr₀, hr₀1⟩ := hψ.triv
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  obtain ⟨c, hc, hlow⟩ := exists_normForm_lower (a := a) ha
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  set M : ℝ := max 1 ‖a‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  -- the small subgroup `P = B_ε × B_ε`
  set ε : ℝ := min 1 (r₀ / (‖τ‖ * M)) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos hr₀ (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεN : ‖τ‖ * (M * ε ^ 2) ≤ r₀ := by
    have : ε ≤ r₀ / (‖τ‖ * M) := min_le_right _ _
    calc ‖τ‖ * (M * ε ^ 2) ≤ ‖τ‖ * (M * ε) := by
          gcongr; nlinarith
      _ = (‖τ‖ * M) * ε := by ring
      _ ≤ (‖τ‖ * M) * (r₀ / (‖τ‖ * M)) := by gcongr
      _ = r₀ := by field_simp
  set ε' : ℝ≥0 := ⟨ε, hε.le⟩
  have hε' : (0 : ℝ≥0) < ε' := by exact_mod_cast hε
  set P := bsub2 K ε'
  -- the bad region `Z`: a box
  set Rz : ℝ := max ε (max (A / (‖2 * τ‖ * ε)) (A / (‖2 * τ * a‖ * ε)))
  have h2τ : 0 < ‖2 * τ‖ := norm_pos_iff.mpr (mul_ne_zero h2 hτ)
  have h2τa : 0 < ‖2 * τ * a‖ := norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero h2 hτ) ha0)
  -- big `T`
  set T₁ : ℝ := max (M * Rz ^ 2) (max (M * ε ^ 2) ((M * ε) ^ 2 / c))
  refine ⟨Rz, T₁, fun R T hR hT => ?_⟩
  set A₁ : Set (K × K) := (bsub K R : Set K) ×ˢ (bsub K R : Set K)
  set A₂ : Set (K × K) := normForm a ⁻¹' closedBall 0 T
  have hA₁m : MeasurableSet A₁ := (measurableSet_bsub R).prod (measurableSet_bsub R)
  have hA₂m : MeasurableSet A₂ := measurableSet_normForm_preimage measurableSet_closedBall
  have hA₁f : (μ.prod μ) A₁ ≠ ∞ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (measure_bsub_ne_top μ R) (measure_bsub_ne_top μ R)
  have hA₂f : (μ.prod μ) A₂ ≠ ∞ := (isCompact_normForm_preimage_closedBall ha T).measure_lt_top.ne
  have hf : Continuous fun z : K × K => (ψ (τ * normForm a z) : ℂ) :=
    continuous_psi_comp hψ (continuous_const.mul continuous_normForm)
  -- the coset integrals vanish outside the box
  have hcoset : ∀ z : K × K, (Rz < ‖z.1‖ ∨ Rz < ‖z.2‖) →
      ∫ h in (P : Set (K × K)), (ψ (τ * normForm a (z + h)) : ℂ) ∂(μ.prod μ) = 0 := by
    intro z hz
    have hfun : ∀ h ∈ (P : Set (K × K)), (ψ (τ * normForm a (z + h)) : ℂ) =
        (ψ (τ * normForm a z) : ℂ) * ((ψ ((2 * τ * z.1) * h.1) : ℂ) * (ψ ((-2 * τ * a * z.2) * h.2) : ℂ)) := by
      intro h hh
      have hhn : ‖h‖ ≤ ε := norm_le_of_mem_bsub2 hh
      have hNh : ψ (τ * normForm a h) = 1 := by
        refine hr₀1 _ ?_
        rw [norm_mul]
        calc ‖τ‖ * ‖normForm a h‖ ≤ ‖τ‖ * (M * ‖h‖ ^ 2) := by gcongr; exact norm_normForm_le h
          _ ≤ ‖τ‖ * (M * ε ^ 2) := by gcongr
          _ ≤ r₀ := hεN
      rw [normForm_add, show τ * (normForm a z + 2 * (z.1 * h.1 - a * z.2 * h.2) + normForm a h) =
        τ * normForm a z + (2 * τ * z.1 * h.1 + -2 * τ * a * z.2 * h.2) + τ * normForm a h by ring,
        AddChar.map_add_eq_mul, hNh, mul_one, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        Circle.coe_mul, Circle.coe_mul]
    rw [setIntegral_congr_fun (by rw [coe_bsub2]; exact (measurableSet_bsub _).prod (measurableSet_bsub _))
      hfun, integral_const_mul, coe_bsub2,
      setIntegral_prod_mul (fun x => (ψ ((2 * τ * z.1) * x) : ℂ)) (fun y => (ψ ((-2 * τ * a * z.2) * y) : ℂ))]
    rcases hz with hz | hz
    · rw [integral_bsub_char_eq_zero μ ψ (2 * τ * z.1) (hA1 _ _ ?_)]
      · simp
      have : A / (‖2 * τ‖ * ε) ≤ ‖z.1‖ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hz.le
      calc A = (‖2 * τ‖ * ε) * (A / (‖2 * τ‖ * ε)) := by field_simp
        _ ≤ (‖2 * τ‖ * ε) * ‖z.1‖ := by gcongr
        _ = ‖2 * τ * z.1‖ * (ε' : ℝ) := by
          rw [show ((ε' : ℝ≥0) : ℝ) = ε from rfl, norm_mul (2 * τ)]; ring
    · rw [integral_bsub_char_eq_zero μ ψ (-2 * τ * a * z.2) (hA1 _ _ ?_)]
      · simp
      have : A / (‖2 * τ * a‖ * ε) ≤ ‖z.2‖ := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hz.le
      calc A = (‖2 * τ * a‖ * ε) * (A / (‖2 * τ * a‖ * ε)) := by field_simp
        _ ≤ (‖2 * τ * a‖ * ε) * ‖z.2‖ := by gcongr
        _ = ‖-2 * τ * a * z.2‖ * (ε' : ℝ) := by
          rw [show -2 * τ * a * z.2 = -(2 * τ * a * z.2) by ring, norm_neg, norm_mul (2 * τ * a),
            show ((ε' : ℝ≥0) : ℝ) = ε from rfl]; ring
  -- invariance of the regions under `P`
  have hRε : ε ≤ R := (le_max_left _ _).trans hR
  have hA₁P : ∀ z ∈ A₁, ∀ h ∈ P, z + h ∈ A₁ := by
    intro z hz h hh
    rw [← SetLike.mem_coe, coe_bsub2] at hh
    exact ⟨(bsub K R).add_mem hz.1 (bsub_mono (show ε' ≤ R from hRε) hh.1),
      (bsub K R).add_mem hz.2 (bsub_mono (show ε' ≤ R from hRε) hh.2)⟩
  have hA₂P : ∀ z ∈ A₂, ∀ h ∈ P, z + h ∈ A₂ := by
    intro z hz h hh
    have hhn : ‖h‖ ≤ ε := norm_le_of_mem_bsub2 hh
    simp only [A₂, Set.mem_preimage, mem_closedBall, dist_zero_right] at hz ⊢
    have hzT : c * ‖z‖ ^ 2 ≤ T := (hlow z).trans hz
    have hT1 : (M * ε) ^ 2 / c ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hTpos : 0 ≤ T := le_trans (by positivity) hT1
    rw [normForm_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hz ?_)) ?_)
    · refine (norm_polar_le z h).trans ?_
      -- `M ‖z‖ ‖h‖ ≤ T`
      have hz' : ‖z‖ ≤ Real.sqrt (T / c) := Real.le_sqrt_of_sq_le (by rw [le_div_iff₀ hc]; linarith)
      have hsq : (M * ε) * Real.sqrt (T / c) ≤ T := by
        have h1 : (M * ε) ^ 2 ≤ T * c := by rwa [div_le_iff₀ hc] at hT1
        rw [show (M * ε) * Real.sqrt (T / c) = Real.sqrt ((M * ε) ^ 2 * (T / c)) by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
        have hTc : 0 ≤ T / c := div_nonneg hTpos hc.le
        calc Real.sqrt ((M * ε) ^ 2 * (T / c)) ≤ Real.sqrt ((T * c) * (T / c)) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h1 hTc)
          _ = T := by
            rw [show T * c * (T / c) = T ^ 2 by field_simp, Real.sqrt_sq hTpos]
      calc M * (‖z‖ * ‖h‖) ≤ M * (Real.sqrt (T / c) * ε) := by gcongr
        _ = (M * ε) * Real.sqrt (T / c) := by ring
        _ ≤ T := hsq
    · calc ‖normForm a h‖ ≤ M * ‖h‖ ^ 2 := norm_normForm_le h
        _ ≤ M * ε ^ 2 := by gcongr
        _ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hcompl : ∀ {B : Set (K × K)}, (∀ z ∈ B, ∀ h ∈ P, z + h ∈ B) → ∀ z ∉ B, ∀ h ∈ P, z + h ∉ B := by
    intro B hB z hz h hh hzh
    exact hz (by simpa using hB _ hzh (-h) (P.neg_mem hh))
  -- the box `|z_i| ≤ Rz` lies in both regions
  have hbox₁ : ∀ z : K × K, ¬ (Rz < ‖z.1‖ ∨ Rz < ‖z.2‖) → z ∈ A₁ := by
    intro z hz
    push Not at hz
    exact ⟨hz.1.trans hR, hz.2.trans hR⟩
  have hbox₂ : ∀ z : K × K, ¬ (Rz < ‖z.1‖ ∨ Rz < ‖z.2‖) → z ∈ A₂ := by
    intro z hz
    push Not at hz
    simp only [A₂, Set.mem_preimage, mem_closedBall, dist_zero_right]
    have hzn : ‖z‖ ≤ Rz := by rw [Prod.norm_def]; exact max_le hz.1 hz.2
    calc ‖normForm a z‖ ≤ M * ‖z‖ ^ 2 := norm_normForm_le z
      _ ≤ M * Rz ^ 2 := by gcongr
      _ ≤ T := le_trans (le_max_left _ _) hT
  have hmP : MeasurableSet (P : Set (K × K)) := by
    rw [coe_bsub2]; exact (measurableSet_bsub _).prod (measurableSet_bsub _)
  have hP0 : (μ.prod μ) (P : Set (K × K)) ≠ 0 := by
    rw [coe_bsub2, Measure.prod_prod]
    exact mul_ne_zero (measure_bsub_pos μ hε').ne' (measure_bsub_pos μ hε').ne'
  have hPf : (μ.prod μ) (P : Set (K × K)) ≠ ∞ := by
    rw [coe_bsub2, Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_bsub_ne_top μ _) (measure_bsub_ne_top μ _)
  -- `∫_{A₁ \ A₂} = 0` and `∫_{A₂ \ A₁} = 0`
  have hzero : ∀ {B B' : Set (K × K)}, MeasurableSet B → MeasurableSet B' → (μ.prod μ) B ≠ ∞ →
      (∀ z ∈ B, ∀ h ∈ P, z + h ∈ B) → (∀ z ∈ B', ∀ h ∈ P, z + h ∈ B') →
      (∀ z : K × K, ¬ (Rz < ‖z.1‖ ∨ Rz < ‖z.2‖) → z ∈ B') →
      ∫ z in B \ B', (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) = 0 := by
    intro B B' hBm hB'm hBf hBP hB'P hboxB'
    refine setIntegral_eq_zero_of_coset (μ.prod μ) P hmP hP0 hPf (hBm.diff hB'm)
      (ne_top_of_le_ne_top hBf (measure_mono Set.sdiff_subset)) ?_ hf.measurable (C := 1)
      (fun z => by simp) ?_
    · rintro z ⟨hzB, hzB'⟩ h hh
      exact ⟨hBP z hzB h hh, hcompl hB'P z hzB' h hh⟩
    · rintro z ⟨-, hzB'⟩
      refine hcoset z ?_
      by_contra hc'
      exact hzB' (hboxB' z hc')
  have hint : ∀ {B : Set (K × K)}, (μ.prod μ) B ≠ ∞ →
      IntegrableOn (fun z : K × K => (ψ (τ * normForm a z) : ℂ)) B (μ.prod μ) := fun hB =>
    Measure.integrableOn_of_bounded hB hf.aestronglyMeasurable (M := 1)
      (Filter.Eventually.of_forall fun z => by simp)
  have e₁ : ∫ z in A₁, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) =
      ∫ z in A₁ ∩ A₂, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) := by
    rw [← Set.inter_union_sdiff A₁ A₂, setIntegral_union (Set.disjoint_sdiff_inter.symm)
      (hA₁m.diff hA₂m) (hint (ne_top_of_le_ne_top hA₁f (measure_mono Set.inter_subset_left)))
      (hint (ne_top_of_le_ne_top hA₁f (measure_mono Set.sdiff_subset))),
      hzero hA₁m hA₂m hA₁f hA₁P hA₂P hbox₂, add_zero, Set.inter_union_sdiff]
  have e₂ : ∫ z in A₂, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) =
      ∫ z in A₁ ∩ A₂, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) := by
    rw [Set.inter_comm, ← Set.inter_union_sdiff A₂ A₁, setIntegral_union (Set.disjoint_sdiff_inter.symm)
      (hA₂m.diff hA₁m) (hint (ne_top_of_le_ne_top hA₂f (measure_mono Set.inter_subset_left)))
      (hint (ne_top_of_le_ne_top hA₂f (measure_mono Set.sdiff_subset))),
      hzero hA₂m hA₁m hA₂f hA₂P hA₁P hbox₁, add_zero, Set.inter_union_sdiff]
  rw [e₁, e₂]

end Regions

/-! ### The quadratic character $\chi_a$ and its Gauss sum -/

section Chi

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} {a : K}

/-- **The norm-residue character** $\chi_a$: $\pm1$-valued, $\chi_a(s) = 1$ iff $s$ is a norm $x^2 - ay^2$, and
multiplicative on $K^\times$. (The Hilbert symbol $(a, \cdot)$ is one, `HasseNorm/WeilLocal.lean`.) -/
structure IsNormChar (a : K) (χ : K → ℤ) : Prop where
  pm : ∀ s, χ s = 1 ∨ χ s = -1
  one_iff : ∀ s, χ s = 1 ↔ s ∈ normSet a
  mul : ∀ s t, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t

variable {χ : K → ℤ}

lemma IsNormChar.sq (hχ : IsNormChar a χ) (c : K) : χ (c ^ 2) = 1 := (hχ.one_iff _).mpr (sq_mem_normSet c)

lemma IsNormChar.eq_neg_one (hχ : IsNormChar a χ) {s : K} (hs : s ∉ normSet a) : χ s = -1 :=
  (hχ.pm s).resolve_left fun h => hs ((hχ.one_iff s).mp h)

lemma IsNormChar.mul_self (hχ : IsNormChar a χ) (s : K) : χ s * χ s = 1 := by
  rcases hχ.pm s with h | h <;> rw [h] <;> norm_num

lemma isOpen_normSet_diff {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) : IsOpen (normSet a \ {0}) := by
  rw [Metric.isOpen_iff]
  rintro s ⟨hs, hs0⟩
  have hs0' : s ≠ 0 := hs0
  refine ⟨ρ * ‖s‖, by positivity, fun s' hs' => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs'
  have hmem : s' ∈ (fun u => s * u) '' closedBall 1 ρ :=
    (norm_sub_le_iff_mem_image' hs0' hρ1).mp (by rw [norm_sub_rev]; exact hs'.le)
  obtain ⟨u, hu, rfl⟩ := hmem
  refine ⟨mul_mem_normSet hs (mem_normSet_of_isSquare (hsq u hu)), ?_⟩
  intro h0
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_one] at hu; linarith
  exact mul_ne_zero hs0' hu0 h0

lemma measurableSet_normSet {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) : MeasurableSet (normSet a) := by
  have : normSet a = (normSet a \ {0}) ∪ {0} := by
    ext s; by_cases h : s = 0
    · subst h; simp [show (0 : K) ∈ normSet a from ⟨0, by simp [normForm]⟩]
    · simp [h]
  rw [this]
  exact (isOpen_normSet_diff hρ hρ1 hsq).measurableSet.union (measurableSet_singleton 0)

open scoped Classical in
lemma IsNormChar.coe_eq (hχ : IsNormChar a χ) (s : K) :
    (χ s : ℂ) = if s ∈ normSet a then 1 else -1 := by
  split_ifs with h
  · rw [(hχ.one_iff s).mpr h]; simp
  · rw [hχ.eq_neg_one h]; simp

lemma IsNormChar.measurable (hχ : IsNormChar a χ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) : Measurable fun s => (χ s : ℂ) := by
  classical
  have : (fun s => (χ s : ℂ)) = fun s => if s ∈ normSet a then (1 : ℂ) else -1 := funext hχ.coe_eq
  rw [this]
  exact Measurable.ite (measurableSet_normSet hρ hρ1 hsq) measurable_const measurable_const

lemma IsNormChar.indicator_eq (hχ : IsNormChar a χ) (f : K → ℂ) (s : K) :
    (normSet a).indicator f s = f s * ((1 + (χ s : ℂ)) / 2) := by
  by_cases h : s ∈ normSet a
  · rw [Set.indicator_of_mem h, (hχ.one_iff s).mpr h]; push_cast; ring
  · rw [Set.indicator_of_notMem h, hχ.eq_neg_one h]; push_cast; ring

/-- $\chi_a$ is constant on cosets $x(1 + B_{\rho\|x\|})$. -/
lemma IsNormChar.add_small (hχ : IsNormChar a χ) {ρ : ℝ} (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) {x h : K} (hx : x ≠ 0)
    (hh : ‖h‖ ≤ ρ * ‖x‖) : χ (x + h) = χ x := by
  have hmem : x + h ∈ (fun u => x * u) '' closedBall 1 ρ :=
    (norm_sub_le_iff_mem_image' hx hρ1).mp (by simpa using hh)
  obtain ⟨u, hu, hxu⟩ := hmem
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_one] at hu; linarith
  rw [← hxu, hχ.mul x u hx hu0, (hχ.one_iff u).mpr (mem_normSet_of_isSquare (hsq u hu)), mul_one]

/-- **The Gauss sum of $\chi_a$ stabilizes:** $\int_{B_R}\chi_a(s)\psi(s)\,ds$ is constant for large $R$. -/
theorem gaussChi_stable (hψ : IsStdChar ψ) (hχ : IsNormChar a χ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsq : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) :
    ∃ R₀ : ℝ≥0, ∀ R ≥ R₀, ∫ s in (bsub K R : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ =
      ∫ s in (bsub K R₀ : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ := by
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  set ε' : ℝ≥0 := ⟨A, hA.le⟩
  have hε' : (0 : ℝ≥0) < ε' := by exact_mod_cast hA
  set R₀ : ℝ≥0 := ⟨max A (A / ρ), le_max_of_le_left hA.le⟩
  refine ⟨R₀, fun R hR => ?_⟩
  have hsub : (bsub K R₀ : Set K) ⊆ bsub K R := bsub_mono hR
  have hmeas : Measurable fun s : K => (ψ s : ℂ) * (χ s : ℂ) :=
    (continuous_psi_comp hψ continuous_id).measurable.mul (hχ.measurable hρ hρ1 hsq)
  have hint : ∀ R' : ℝ≥0, IntegrableOn (fun s : K => (ψ s : ℂ) * (χ s : ℂ)) (bsub K R' : Set K) μ := by
    intro R'
    refine Measure.integrableOn_of_bounded (measure_bsub_ne_top μ R') hmeas.aestronglyMeasurable
      (M := 1) (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    rcases hχ.pm s with h | h <;> simp [h]
  have hdiff : ∫ s in (bsub K R : Set K) \ bsub K R₀, (ψ s : ℂ) * (χ s : ℂ) ∂μ = 0 := by
    refine setIntegral_eq_zero_of_coset μ (bsub K ε') (measurableSet_bsub _)
      (measure_bsub_pos μ hε').ne' (measure_bsub_ne_top μ _)
      ((measurableSet_bsub R).diff (measurableSet_bsub R₀))
      (ne_top_of_le_ne_top (measure_bsub_ne_top μ R) (measure_mono Set.sdiff_subset))
      ?_ hmeas (C := 1) (fun s => by rw [norm_mul]; rcases hχ.pm s with h | h <;> simp [h]) ?_
    · rintro x ⟨hxR, hxR₀⟩ h hh
      have hxR₀' : (R₀ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₀ h'
      have hh' : ‖h‖ < ‖x‖ := lt_of_le_of_lt ((mem_bsub.mp hh).trans (le_max_left _ _)) hxR₀'
      refine ⟨?_, ?_⟩
      · show ‖x + h‖ ≤ R; rw [norm_add_eq_of_lt hh']; exact hxR
      · intro hc; apply hxR₀
        show ‖x‖ ≤ R₀
        have : ‖x + h‖ ≤ R₀ := hc
        rwa [norm_add_eq_of_lt hh'] at this
    · rintro x ⟨-, hxR₀⟩
      have hxR₀' : (R₀ : ℝ) < ‖x‖ := lt_of_not_ge fun h' => hxR₀ h'
      have hx0 : x ≠ 0 := by
        rintro rfl; rw [norm_zero] at hxR₀'; exact absurd hxR₀' (not_lt.mpr (NNReal.coe_nonneg _))
      have hfun : ∀ h ∈ (bsub K ε' : Set K), (ψ (x + h) : ℂ) * (χ (x + h) : ℂ) =
          ((ψ x : ℂ) * (χ x : ℂ)) * (ψ (1 * h) : ℂ) := by
        intro h hh
        have hh' : ‖h‖ ≤ ρ * ‖x‖ := by
          have h1 : ‖h‖ ≤ A := hh
          have h2 : A / ρ ≤ ‖x‖ := (le_max_right _ _).trans hxR₀'.le
          calc ‖h‖ ≤ A := h1
            _ = ρ * (A / ρ) := by field_simp
            _ ≤ ρ * ‖x‖ := by gcongr
        rw [hχ.add_small hρ1 hsq hx0 hh', AddChar.map_add_eq_mul, Circle.coe_mul, one_mul]
        ring
      rw [setIntegral_congr_fun (measurableSet_bsub _) hfun, integral_const_mul,
        integral_bsub_char_eq_zero μ ψ 1 (hA1 1 (ε' : ℝ) (by rw [norm_one, one_mul]; rfl)), mul_zero]
  have hunion : (bsub K R : Set K) = (bsub K R₀ : Set K) ∪ ((bsub K R : Set K) \ bsub K R₀) :=
    (Set.union_sdiff_cancel hsub).symm
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right
    ((measurableSet_bsub R).diff (measurableSet_bsub R₀)) (hint R₀) ((hint R).mono_set Set.sdiff_subset),
    hdiff, add_zero]

/-- **Twisting the Gauss sum:** $\int_{B_T}\psi(\tau s)\chi_a(s)\,ds = \chi_a(\tau)\operatorname{mod}(\tau)^{-1}
\int_{B_{\|\tau\|T}}\psi(s)\chi_a(s)\,ds$ (substitute $s \mapsto s/\tau$). -/
lemma integral_psi_chi_scale (hχ : IsNormChar a χ) {τ : K} (hτ : τ ≠ 0) (T : ℝ≥0) :
    ∫ s in (bsub K T : Set K), (ψ (τ * s) : ℂ) * (χ s : ℂ) ∂μ =
      (χ τ : ℂ) * (((modK K τ)⁻¹ : ℝ) • ∫ s in (bsub K (‖τ‖₊ * T) : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ) := by
  rw [← integral_indicator (measurableSet_bsub _), ← integral_indicator (measurableSet_bsub _),
    ← integral_comp_mul_left μ _ hτ, ← integral_const_mul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μ, s ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  filter_upwards [hae] with s hs0
  have hiff : τ * s ∈ (bsub K (‖τ‖₊ * T) : Set K) ↔ s ∈ (bsub K T : Set K) := by
    simp only [SetLike.mem_coe, mem_bsub, NNReal.coe_mul, coe_nnnorm, norm_mul]
    exact mul_le_mul_iff_right₀ (norm_pos_iff.mpr hτ)
  by_cases hs : s ∈ (bsub K T : Set K)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hiff.mpr hs)]
    rw [hχ.mul τ s hτ hs0]
    have : (χ τ : ℂ) * (χ τ : ℂ) = 1 := by exact_mod_cast hχ.mul_self τ
    push_cast
    linear_combination (-(ψ (τ * s) : ℂ) * (χ s : ℂ)) * this
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun h => hs (hiff.mp h)), mul_zero]

end Chi

/-! ### Assembly: $J(\tau)\operatorname{mod}(\tau) = \chi_a(\tau)J(1)$ -/

section Assembly

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} {a : K}
  {χ : K → ℤ}

/-- **The two-dimensional Gauss integral via the norm map.** For $\tau \ne 0$ and all admissible $T \ge T_0$,
$r$, $\rho$ (with $\psi$ trivial on $B_{\|\tau\|r}$ and on $B_{\|\tau\|T\rho}$, $U_\rho$ consisting of squares):
$$\gamma(\tau)\gamma(-a\tau) = \operatorname{vol}(N^{-1}B_r) + \kappa_\rho\Big(\tfrac12\chi_a(\tau)\operatorname{mod}(\tau)^{-1}
\int_{B_{\|\tau\|T}}\psi\chi_a - \int_{B_r}\mathbf 1_{N(K^2)}\Big).$$ -/
theorem gauss_two_eq (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) (ha : ¬ IsSquare a) (hχ : IsNormChar a χ)
    {τ : K} (hτ : τ ≠ 0) :
    ∃ T₀ : ℝ, ∀ (T : ℝ≥0) (r ρ : ℝ), T₀ ≤ T → 0 < r → r ≤ T →
      (∀ x : K, ‖x‖ ≤ ‖τ‖ * r → ψ x = 1) → 0 < ρ → ρ < 1 →
      (∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) → (∀ x : K, ‖x‖ ≤ ‖τ‖ * T * ρ → ψ x = 1) →
      gaussInt μ ψ τ * gaussInt μ ψ (-a * τ) =
        (μ.prod μ).real (normForm a ⁻¹' closedBall 0 r) +
          kappaN μ a ρ * ((1 / 2 : ℂ) * ((χ τ : ℂ) * (((modK K τ)⁻¹ : ℝ) •
            ∫ s in (bsub K (‖τ‖₊ * T) : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ)) -
            ∫ s in closedBall (0 : K) r, (normSet a).indicator (fun _ => (1 : ℂ)) s ∂μ) := by
  obtain ⟨R₀, T₀, hreg⟩ := setIntegral_box_eq_normBall (μ := μ) hψ h2 ha hτ
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  refine ⟨max T₀ (A / ‖τ‖), fun T r ρ hT hr hrT hψr hρ hρ1 hsq hψT => ?_⟩
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  obtain ⟨R₁, hR₁⟩ := gaussInt_spec (μ := μ) hψ h2 hτ
  obtain ⟨R₂, hR₂⟩ := gaussInt_spec (μ := μ) hψ h2 (mul_ne_zero (neg_ne_zero.mpr ha0) hτ)
  set R : ℝ≥0 := max (max R₁ R₂) (Real.toNNReal R₀)
  have hR0 : R₀ ≤ R := (Real.le_coe_toNNReal R₀).trans (by exact_mod_cast le_max_right _ _)
  have hcont : Continuous fun z : K × K => (ψ (τ * normForm a z) : ℂ) :=
    continuous_psi_comp hψ (continuous_const.mul continuous_normForm)
  -- step 1: the box and the norm ball
  rw [← hR₁ R (le_trans (le_max_left _ _) (le_max_left _ _)),
    ← hR₂ R (le_trans (le_max_right _ _) (le_max_left _ _)), gaussI_mul_gaussI_eq,
    hreg R T hR0 (le_trans (le_max_left _ _) hT)]
  -- step 2: split the norm ball at radius `r`
  have hsplit : normForm a ⁻¹' closedBall 0 (T : ℝ) = normForm a ⁻¹' closedBall 0 r ∪
      normForm a ⁻¹' (closedBall 0 (T : ℝ) \ closedBall 0 r) := by
    rw [← Set.preimage_union, Set.union_sdiff_cancel (closedBall_subset_closedBall hrT)]
  have hm1 : MeasurableSet (normForm a ⁻¹' closedBall (0 : K) r) :=
    measurableSet_normForm_preimage measurableSet_closedBall
  have hm2 : MeasurableSet (normForm a ⁻¹' (closedBall (0 : K) (T : ℝ) \ closedBall 0 r)) :=
    measurableSet_normForm_preimage (measurableSet_closedBall.diff measurableSet_closedBall)
  have hfin : ∀ {S : Set K}, S ⊆ closedBall 0 (T : ℝ) → (μ.prod μ) (normForm a ⁻¹' S) ≠ ∞ := fun hS =>
    ne_top_of_le_ne_top (isCompact_normForm_preimage_closedBall ha T).measure_lt_top.ne
      (measure_mono (Set.preimage_mono hS))
  have hint : ∀ {S : Set K}, S ⊆ closedBall 0 (T : ℝ) →
      IntegrableOn (fun z : K × K => (ψ (τ * normForm a z) : ℂ)) (normForm a ⁻¹' S) (μ.prod μ) :=
    fun hS => Measure.integrableOn_of_bounded (hfin hS) hcont.aestronglyMeasurable (M := 1)
      (Filter.Eventually.of_forall fun z => by simp)
  rw [hsplit, setIntegral_union (by
      exact Disjoint.preimage _ Set.disjoint_sdiff_right) hm2
    (hint (closedBall_subset_closedBall hrT)) (hint Set.sdiff_subset)]
  -- the inner part
  have hinner : ∫ z in normForm a ⁻¹' closedBall 0 r, (ψ (τ * normForm a z) : ℂ) ∂(μ.prod μ) =
      (μ.prod μ).real (normForm a ⁻¹' closedBall 0 r) := by
    rw [setIntegral_congr_fun hm1 (g := fun _ => (1 : ℂ)) (fun z hz => by
      rw [hψr _ (by
        rw [Set.mem_preimage, mem_closedBall, dist_zero_right] at hz
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz hτn.le), Circle.coe_one]),
      setIntegral_const, Complex.real_smul, mul_one]
  -- the annulus, via the image measure
  set hfun : K → ℂ := (closedBall (0 : K) (T : ℝ) \ closedBall 0 r).indicator fun s => (ψ (τ * s) : ℂ)
    with hhf
  have hann : ∫ z in normForm a ⁻¹' (closedBall 0 (T : ℝ) \ closedBall 0 r), (ψ (τ * normForm a z) : ℂ)
      ∂(μ.prod μ) = ∫ z, hfun (normForm a z) ∂(μ.prod μ) := by
    rw [← integral_indicator hm2]
    rfl
  have hmeash : Measurable hfun :=
    ((continuous_psi_comp hψ (continuous_const.mul continuous_id)).measurable).indicator
      (measurableSet_closedBall.diff measurableSet_closedBall)
  have hbd : ∀ s, ‖hfun s‖ ≤ 1 := by
    intro s; rw [hhf]; by_cases hs : s ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r
    · rw [Set.indicator_of_mem hs]; simp
    · rw [Set.indicator_of_notMem hs]; simp
  have hsupp : ∀ s, hfun s ≠ 0 → r ≤ ‖s‖ ∧ ‖s‖ ≤ T := by
    intro s hs
    rw [hhf] at hs
    by_cases hs' : s ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r
    · simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le] at hs'
      exact ⟨hs'.2.le, hs'.1⟩
    · exact absurd (Set.indicator_of_notMem hs' _) hs
  have hinvh : ∀ s u, u ∈ closedBall (1 : K) ρ → hfun (s * u) = hfun s := by
    intro s u hu
    rw [hhf]
    have hu1 : ‖u‖ = 1 := by
      rw [← norm_one (α := K)]
      refine norm_eq_of_norm_sub_lt ?_
      rw [norm_one]; rw [mem_closedBall, dist_eq_norm] at hu; linarith
    have hmem : s * u ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r ↔
        s ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r := by
      simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, norm_mul, hu1, mul_one]
    by_cases hs : s ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r
    · rw [Set.indicator_of_mem (hmem.mpr hs), Set.indicator_of_mem hs]
      have hsT : ‖s‖ ≤ T := by
        have := hs.1; rwa [mem_closedBall, dist_zero_right] at this
      rw [show τ * (s * u) = τ * s + τ * s * (u - 1) by ring, AddChar.map_add_eq_mul,
        hψT (τ * s * (u - 1)) ?_, mul_one]
      rw [norm_mul, norm_mul, ← dist_eq_norm]
      rw [mem_closedBall] at hu
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsT hτn.le) hu dist_nonneg (by positivity)
    · rw [Set.indicator_of_notMem (fun h => hs (hmem.mp h)), Set.indicator_of_notMem hs]
  rw [hinner, hann, integral_comp_normForm μ ha hρ hρ1 hsq hmeash hbd hr hsupp hinvh]
  congr 2
  -- `∫ 1_N h = ∫_{B_T} ψ(τ s) 1_N - ∫_{B_r} 1_N`
  have hT' : (closedBall (0 : K) (T : ℝ)) = (bsub K T : Set K) := (coe_bsub T).symm
  have hcN : ∀ s, (normSet a).indicator hfun s =
      (closedBall (0 : K) (T : ℝ) \ closedBall 0 r).indicator
        (fun s => (ψ (τ * s) : ℂ) * (normSet a).indicator (fun _ => (1 : ℂ)) s) s := by
    intro s
    by_cases h1 : s ∈ normSet a <;> by_cases h2 : s ∈ closedBall (0 : K) (T : ℝ) \ closedBall 0 r <;>
      simp [hfun, h1, h2]
  simp_rw [hcN]
  have hmN := measurableSet_normSet (a := a) hρ hρ1 hsq
  have hgm : Measurable fun s => (ψ (τ * s) : ℂ) * (normSet a).indicator (fun _ => (1 : ℂ)) s :=
    (continuous_psi_comp hψ (continuous_const.mul continuous_id)).measurable.mul
      (measurable_const.indicator hmN)
  have hgint : ∀ R' : ℝ, IntegrableOn (fun s => (ψ (τ * s) : ℂ) * (normSet a).indicator
      (fun _ => (1 : ℂ)) s) (closedBall (0 : K) R') μ := by
    intro R'
    refine Measure.integrableOn_of_bounded (isCompact_closedBall _ _).measure_lt_top.ne
      hgm.aestronglyMeasurable (M := 1) (Filter.Eventually.of_forall fun s => ?_)
    by_cases h1 : s ∈ normSet a
    · rw [Set.indicator_of_mem h1]; simp
    · rw [Set.indicator_of_notMem h1]; simp
  rw [integral_indicator (measurableSet_closedBall.diff measurableSet_closedBall),
    setIntegral_sdiff measurableSet_closedBall (hgint T) (closedBall_subset_closedBall hrT)]
  congr 1
  · -- `∫_{B_T} ψ(τs) 1_N(s) = ½ χ(τ) mod(τ)⁻¹ E`
    have hsplitχ : ∀ s, (ψ (τ * s) : ℂ) * (normSet a).indicator (fun _ => (1 : ℂ)) s =
        (1 / 2 : ℂ) * (ψ (τ * s) : ℂ) + (1 / 2 : ℂ) * ((ψ (τ * s) : ℂ) * (χ s : ℂ)) := by
      intro s; rw [hχ.indicator_eq]; ring
    have hIO : ∀ {g : K → ℂ}, Measurable g → (∀ s, ‖g s‖ ≤ 1) → IntegrableOn g (bsub K T : Set K) μ :=
      fun hg hb => Measure.integrableOn_of_bounded (measure_bsub_ne_top μ T) hg.aestronglyMeasurable
        (M := 1) (Filter.Eventually.of_forall hb)
    have hψm : Measurable fun s : K => (ψ (τ * s) : ℂ) :=
      (continuous_psi_comp hψ (continuous_const.mul continuous_id)).measurable
    have hI1 : IntegrableOn (fun s => (1 / 2 : ℂ) * (ψ (τ * s) : ℂ)) (bsub K T : Set K) μ :=
      hIO (hψm.const_mul _) fun s => by rw [norm_mul]; norm_num
    have hI2 : IntegrableOn (fun s => (1 / 2 : ℂ) * ((ψ (τ * s) : ℂ) * (χ s : ℂ))) (bsub K T : Set K) μ :=
      hIO ((hψm.mul (hχ.measurable hρ hρ1 hsq)).const_mul _) fun s => by
        rw [norm_mul, norm_mul]; rcases hχ.pm s with h | h <;> simp [h] <;> norm_num
    have hAT : A ≤ ‖τ‖ * T := by
      have : A / ‖τ‖ ≤ T := le_trans (le_max_right _ _) hT
      rw [div_le_iff₀ hτn] at this
      linarith [mul_comm (T : ℝ) ‖τ‖]
    rw [hT']
    simp_rw [hsplitχ]
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
      integral_bsub_char_eq_zero μ ψ τ (hA1 τ T hAT), integral_psi_chi_scale hχ hτ T]
    ring
  · -- `∫_{B_r} ψ(τs) 1_N(s) = ∫_{B_r} 1_N`
    refine setIntegral_congr_fun measurableSet_closedBall fun s hs => ?_
    have hs' : ‖τ * s‖ ≤ ‖τ‖ * r := by
      rw [mem_closedBall, dist_zero_right] at hs
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hs hτn.le
    rw [hψr _ hs', Circle.coe_one, one_mul]

omit [μ.IsAddHaarMeasure] in
lemma IsNormChar.one (hχ : IsNormChar a χ) : χ 1 = 1 := by simpa using hχ.sq 1

omit [μ.IsAddHaarMeasure] in
/-- $\operatorname{mod}(s) < 1$ for $0 < \|s\| < 1$. -/
lemma modK_lt_one {s : K} (hs : s ≠ 0) (hs1 : ‖s‖ < 1) : modK K s < 1 := by
  let μ : Measure K := Measure.addHaar
  rw [modK_eq_ratio μ hs, div_lt_one (measureReal_closedBall_one_pos μ)]
  have hdisj : Disjoint (closedBall (0 : K) ‖s‖) (ball (1 : K) 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_eq_norm] at hx'
    have : ‖x‖ = 1 := by
      rw [← norm_one (α := K)]; exact norm_eq_of_norm_sub_lt (by rw [norm_one]; exact hx')
    linarith
  have hsub : closedBall (0 : K) ‖s‖ ∪ ball (1 : K) 1 ⊆ closedBall 0 1 := by
    refine Set.union_subset (closedBall_subset_closedBall hs1.le) fun x hx => ?_
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    have : ‖x‖ = 1 := by
      rw [← norm_one (α := K)]; exact norm_eq_of_norm_sub_lt (by rw [norm_one]; exact hx)
    exact this.le
  have hball : 0 < μ.real (ball (1 : K) 1) :=
    ENNReal.toReal_pos (isOpen_ball.measure_pos μ ⟨1, mem_ball_self one_pos⟩).ne'
      (ne_top_of_le_ne_top (isCompact_closedBall (1 : K) 1).measure_lt_top.ne
        (measure_mono ball_subset_closedBall))
  have hfin : μ (closedBall (0 : K) 1) ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  have h := measureReal_mono hsub hfin
  rw [measureReal_union hdisj measurableSet_ball (isCompact_closedBall _ _).measure_lt_top.ne
    (ne_top_of_le_ne_top (isCompact_closedBall (1 : K) 1).measure_lt_top.ne
      (measure_mono ball_subset_closedBall))] at h
  linarith

/-- **$J(t)\operatorname{mod}(t) = \chi_a(t)J(1)$** for $a$ not a square: $\gamma(t)\gamma(-at)\operatorname{mod}(t) =
\chi_a(t)\gamma(1)\gamma(-a)$. -/
theorem gaussInt_mul_neg_mul (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) (ha : ¬ IsSquare a)
    (hχ : IsNormChar a χ)
    (hsq : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u) {t : K} (ht : t ≠ 0) :
    gaussInt μ ψ t * gaussInt μ ψ (-a * t) * modK K t =
      (χ t : ℂ) * (gaussInt μ ψ 1 * gaussInt μ ψ (-a * 1)) := by
  obtain ⟨ρ₀, hρ₀, hρ₀1, hsq₀⟩ := hsq
  obtain ⟨r₀, hr₀, hr₀1⟩ := hψ.triv
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one K
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  set q : K := π ^ 2 with hqdef
  have hq0 : q ≠ 0 := pow_ne_zero 2 hπne
  have hqn : ‖q‖ = ‖π‖ ^ 2 := norm_pow _ _
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  obtain ⟨RE, hRE⟩ := gaussChi_stable (μ := μ) hψ hχ hρ₀ hρ₀1 hsq₀
  obtain ⟨T₁, hT₁⟩ := gauss_two_eq (μ := μ) hψ h2 ha hχ ht
  obtain ⟨T₂, hT₂⟩ := gauss_two_eq (μ := μ) hψ h2 ha hχ (one_ne_zero (α := K))
  obtain ⟨T₃, hT₃⟩ := gauss_two_eq (μ := μ) hψ h2 ha hχ hq0
  set M : ℝ := max ‖t‖ (max 1 ‖q‖) with hM
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  set mn : ℝ := min ‖t‖ (min 1 ‖q‖) with hmn
  have hmn0 : 0 < mn := lt_min htn (lt_min one_pos hqpos)
  set Tr : ℝ := max (max T₁ (max T₂ T₃)) (max 1 (RE / mn)) with hTr
  have hTr1 : 1 ≤ Tr := le_trans (le_max_left _ _) (le_max_right _ _)
  set T : ℝ≥0 := ⟨Tr, by linarith⟩ with hTdef
  have hTT : (T : ℝ) = Tr := rfl
  set r : ℝ := min 1 (r₀ / M) with hr
  have hr0 : 0 < r := lt_min one_pos (div_pos hr₀ (by linarith))
  have hrT : r ≤ T := by rw [hTT]; exact (min_le_left _ _).trans hTr1
  set ρ : ℝ := min ρ₀ (min (1 / 2) (r₀ / (M * Tr))) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₀ (lt_min (by norm_num) (div_pos hr₀ (by positivity)))
  have hρ1 : ρ < 1 := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hsqρ : ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u := fun u hu =>
    hsq₀ u (closedBall_subset_closedBall (min_le_left _ _) hu)
  -- the conditions for `τ` with `‖τ‖ ≤ M`
  have hcondr : ∀ τ : K, ‖τ‖ ≤ M → ∀ x : K, ‖x‖ ≤ ‖τ‖ * r → ψ x = 1 := by
    intro τ hτ x hx
    refine hr₀1 x (hx.trans ?_)
    calc ‖τ‖ * r ≤ M * (r₀ / M) := mul_le_mul hτ (min_le_right _ _) hr0.le (by linarith)
      _ = r₀ := by field_simp
  have hcondT : ∀ τ : K, ‖τ‖ ≤ M → ∀ x : K, ‖x‖ ≤ ‖τ‖ * T * ρ → ψ x = 1 := by
    intro τ hτ x hx
    refine hr₀1 x (hx.trans ?_)
    rw [hTT]
    calc ‖τ‖ * Tr * ρ ≤ M * Tr * (r₀ / (M * Tr)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hτ (by linarith))
            (le_trans (min_le_right _ _) (min_le_right _ _)) hρ0.le (by positivity)
      _ = r₀ := by field_simp
  have hTge : ∀ T' : ℝ, T' ≤ Tr → T' ≤ (T : ℝ) := fun T' h => h
  have hE : ∀ τ : K, τ ≠ 0 → mn ≤ ‖τ‖ →
      ∫ s in (bsub K (‖τ‖₊ * T) : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ =
        ∫ s in (bsub K RE : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ := by
    intro τ hτ hmnτ
    refine hRE _ ?_
    show (RE : ℝ) ≤ ‖τ‖ * Tr
    have h1 : RE / mn ≤ Tr := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [div_le_iff₀ hmn0] at h1
    nlinarith
  have e1 := hT₁ T r ρ (hTge _ (le_trans (le_max_left _ _) (le_max_left _ _))) hr0 hrT
    (hcondr t (le_max_left _ _)) hρ0 hρ1 hsqρ (hcondT t (le_max_left _ _))
  have e2 := hT₂ T r ρ (hTge _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)))
    hr0 hrT (hcondr 1 (by rw [norm_one]; exact hM1)) hρ0 hρ1 hsqρ (hcondT 1 (by rw [norm_one]; exact hM1))
  have e3 := hT₃ T r ρ (hTge _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)))
    hr0 hrT (hcondr q (le_trans (le_max_right _ _) (le_max_right _ _))) hρ0 hρ1 hsqρ
    (hcondT q (le_trans (le_max_right _ _) (le_max_right _ _)))
  rw [hE t ht (min_le_left _ _)] at e1
  rw [hE 1 one_ne_zero (by rw [norm_one]; exact le_trans (min_le_right _ _) (min_le_left _ _))] at e2
  rw [hE q hq0 (le_trans (min_le_right _ _) (min_le_right _ _))] at e3
  rw [hχ.one, modK_one] at e2
  rw [hqdef, hχ.sq π] at e3
  generalize (∫ s in (bsub K RE : Set K), (ψ s : ℂ) * (χ s : ℂ) ∂μ) = E at e1 e2 e3
  generalize ((μ.prod μ).real (normForm a ⁻¹' closedBall 0 r) : ℂ) = W at e1 e2 e3
  generalize (kappaN μ a ρ : ℂ) = κ at e1 e2 e3
  generalize (∫ s in closedBall (0 : K) r, (normSet a).indicator (fun _ => (1 : ℂ)) s ∂μ) = I at e1 e2 e3
  -- scaling: `J(q) = mod(π)⁻² J(1)`
  have hmq : modK K (π ^ 2) = modK K π * modK K π := by rw [sq, modK_mul hπne hπne]
  have hm0 : 0 < modK K π := modK_pos hπne
  have hm1 : modK K π < 1 := modK_lt_one hπne hπ1
  have hJq : gaussInt μ ψ (π ^ 2) * gaussInt μ ψ (-a * π ^ 2) =
      (((modK K π)⁻¹ : ℝ) * ((modK K π)⁻¹ : ℝ) : ℂ) * (gaussInt μ ψ 1 * gaussInt μ ψ (-a * 1)) := by
    have h1 := gaussInt_mul_sq (μ := μ) hψ h2 (one_ne_zero (α := K)) hπne
    have h2' := gaussInt_mul_sq (μ := μ) hψ h2 (t := -a * 1) (by simpa using ha0) hπne
    rw [one_mul] at h1
    rw [show -a * 1 * π ^ 2 = -a * π ^ 2 by ring] at h2'
    rw [h1, h2']
    simp only [Complex.real_smul]; ring
  rw [e3, e2, hmq] at hJq
  simp only [Complex.real_smul] at hJq e1
  push_cast at hJq e1
  set u : ℂ := ((modK K π : ℝ) : ℂ)⁻¹ with hu
  have hu1 : u * u ≠ 1 := by
    intro h
    have h' : ((modK K π)⁻¹ * (modK K π)⁻¹ : ℝ) = 1 := by
      have : ((((modK K π)⁻¹ * (modK K π)⁻¹ : ℝ)) : ℂ) = 1 := by rw [← h, hu]; push_cast; ring
      exact_mod_cast this
    have : (1 : ℝ) < (modK K π)⁻¹ := (one_lt_inv₀ hm0).mpr hm1
    nlinarith
  have hD0 : (W - κ * I) * (1 - u * u) = 0 := by
    rw [mul_inv] at hJq
    linear_combination hJq
  have hWκ : W = κ * I := by
    rcases mul_eq_zero.mp hD0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h).symm hu1
  have hmt : (modK K t : ℂ) ≠ 0 := by exact_mod_cast (modK_pos ht).ne'
  rw [e1, e2, hWκ]
  simp only [inv_one, one_smul]
  field_simp
  ring

/-- **The local identity for the Weil index at a non-archimedean place:** for $a, b \in K^\times$,
$$\gamma(ab)\,\gamma(1) = \chi_a(b)\,\gamma(a)\,\gamma(b),$$
where $\chi_a$ is the norm-residue character of $a$ (for $a$ a square, $\chi_a = 1$). -/
theorem gaussInt_mul_identity (hψ : IsStdChar ψ) (h2 : (2 : K) ≠ 0) (hχ : IsNormChar a χ)
    (hsq : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ u : K, u ∈ closedBall (1 : K) ρ → IsSquare u)
    (ha : a ≠ 0) {b : K} (hb : b ≠ 0) :
    gaussInt μ ψ (a * b) * gaussInt μ ψ 1 = (χ b : ℂ) * gaussInt μ ψ a * gaussInt μ ψ b := by
  by_cases hsqa : IsSquare a
  · obtain ⟨c, rfl⟩ := hsqa
    have hc : c ≠ 0 := fun h => ha (by simp [h])
    have hχb : χ b = 1 := by
      refine (hχ.one_iff b).mpr ⟨((b + 1) / 2, (b - 1) / (2 * c)), ?_⟩
      simp only [normForm]
      field_simp
      ring
    rw [hχb, show c * c * b = b * c ^ 2 by ring, show c * c = 1 * c ^ 2 by ring,
      gaussInt_mul_sq hψ h2 hb hc, gaussInt_mul_sq hψ h2 one_ne_zero hc]
    simp only [Complex.real_smul]
    push_cast; ring
  · have e1 := gaussInt_mul_neg_mul (μ := μ) hψ h2 hsqa hχ hsq hb
    have e2 := gaussInt_mul_neg (μ := μ) hψ h2 (mul_ne_zero ha hb)
    have e3 := gaussInt_mul_neg (μ := μ) hψ h2 ha
    have hP := gaussInt_one_mul_neg_one_ne_zero (μ := μ) hψ h2
    have hmab : (modK K (a * b) : ℂ) = (modK K a : ℂ) * (modK K b : ℂ) := by
      rw [modK_mul ha hb]; push_cast; ring
    have hχ2 : (χ b : ℂ) * (χ b : ℂ) = 1 := by exact_mod_cast hχ.mul_self b
    rw [mul_one, show -a * b = -(a * b) by ring] at e1
    refine mul_right_cancel₀ hP ?_
    rw [hmab] at e2
    linear_combination (-(gaussInt μ ψ (a * b) * gaussInt μ ψ 1)) * e3 +
      ((χ b : ℂ) * gaussInt μ ψ a * gaussInt μ ψ b) * e2 -
      ((χ b : ℂ) * gaussInt μ ψ (a * b) * gaussInt μ ψ a * (modK K a : ℂ)) * e1 -
      (gaussInt μ ψ (a * b) * gaussInt μ ψ a * (modK K a : ℂ) * gaussInt μ ψ 1 * gaussInt μ ψ (-a)) * hχ2

end Assembly

end

end QuadFormsKB.Analysis.Weil
