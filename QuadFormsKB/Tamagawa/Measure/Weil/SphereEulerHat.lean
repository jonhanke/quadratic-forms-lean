import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerGaussHat

/-!
# The multiplicative transform of $\hat\Phi$ is bounded by that of $\Phi$

$F$ any number field (originally stated for totally real $F$), $Q_0$ nondegenerate in $n$ variables, $\Phi$ =
`gaussTest`, $\hat\Phi$ = `gaussTestHat Q₀`. There is an idele $t$ ($t_w = \varepsilon$ small at the infinite places, $t_v = d\in\mathcal O_F\setminus0$ at the finite places, with
$d\,H^{-1}\mathfrak d^{-1}\hat{\mathcal O}^n\subseteq\hat{\mathcal O}^n$) such that $\hat\Phi(x)\le\mu_f(\hat{\mathcal O}^n)\,\Phi(tx)$ for all
$x$; the substitution $z\mapsto t^{-1}z$ in the Haar measure `tamIdeles` then gives (**`mellinPhi_gaussTestHat_le`**)
$$M_s\hat\Phi(y)\le C\,M_s\Phi(y)\qquad(C = \mu_f(\hat{\mathcal O}^n)\,\|t\|^{-(n+2s)}<\infty)$$
for every $y$, $M_s$ = `mellinPhi`. This replaces the Euler identity for $\hat\Phi$ (`eulerHat`), which is false in
general: the consumers only need $Z^+_{\hat\Phi}(1)<\infty$.
-/

open MeasureTheory Set Matrix Filter
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Integral elements have valuation at most one at every finite place. -/
theorem val_algebraMap_le_one (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d) ≤ 1 := by
  have := (HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v d)
  exact this

/-- A bounded subset of $F_v^n$ is moved into $\mathcal O_v^n$ by a nonzero global integer, and by any local
element of valuation at most that of it. -/
theorem exists_mul_mem_latL (v : HeightOneSpectrum (𝓞 F)) {K : Set (Fin n → v.adicCompletion F)}
    (hK : Bornology.IsBounded K) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ c : v.adicCompletion F,
      Valued.v c ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) →
      ∀ z ∈ K, ∀ i, Valued.v (c * z i) ≤ 1 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set r : ℝ := ‖algebraMap (𝓞 F) (v.adicCompletion F) p‖ with hrdef
  have hr : r < 1 := by
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v p).mpr hp
    have h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) p) < 1 := by
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) (v := v) p).trans_lt h1
    exact Valued.toNormedField.norm_lt_one_iff.mpr h2
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (|R| + 1) by positivity) hr
  refine ⟨p ^ N, pow_ne_zero _ hp0, fun c hc z hz i => ?_⟩
  have hc' : ‖c‖ ≤ r ^ N := by
    have := Valued.toNormedField.norm_le_iff.mpr hc
    rwa [map_pow, norm_pow] at this
  have hzi : ‖z i‖ ≤ |R| := (norm_le_pi_norm z i).trans ((hR z hz).trans (le_abs_self R))
  have h3 : r ^ N * (|R| + 1) < 1 := by
    rwa [lt_div_iff₀ (by positivity)] at hN
  apply Valued.toNormedField.norm_le_one_iff.mp
  rw [norm_mul]
  have h4 : ‖c‖ * ‖z i‖ ≤ r ^ N * |R| :=
    mul_le_mul hc' hzi (norm_nonneg _) (by positivity)
  nlinarith [pow_nonneg (norm_nonneg (algebraMap (𝓞 F) (v.adicCompletion F) p)) N]

/-- A nonzero global integer moving every $K_v$, $v\in T$, into $\mathcal O_v^n$. -/
theorem exists_mul_mem_latL_finset (T : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) (hK : ∀ v, Bornology.IsBounded (K v)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ v ∈ T, ∀ z ∈ K v, ∀ i,
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * z i) ≤ 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  | insert a T ha ih =>
    obtain ⟨d, hd0, hd⟩ := ih
    obtain ⟨m, hm0, hm⟩ := exists_mul_mem_latL (n := n) a (hK a)
    refine ⟨m * d, mul_ne_zero hm0 hd0, fun v hv z hz i => ?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hvT
    · refine hm _ ?_ z hz i
      rw [map_mul, map_mul]
      exact mul_le_of_le_one_right' (val_algebraMap_le_one v d)
    · have e : algebraMap (𝓞 F) (v.adicCompletion F) (m * d) * z i =
          algebraMap (𝓞 F) (v.adicCompletion F) m * (algebraMap (𝓞 F) (v.adicCompletion F) d * z i) := by
        rw [map_mul, mul_assoc]
      rw [e]
      calc Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m * (algebraMap (𝓞 F) (v.adicCompletion F) d * z i))
          = Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) *
            Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * z i) := map_mul _ _ _
        _ ≤ 1 := mul_le_one' (val_algebraMap_le_one v m) (hd v hvT z hz i)

variable (F) in
/-- The idele with real components $\varepsilon$ (complex ones $\varepsilon$ too) and finite component $d\in F^\times$. -/
def scaleIdele (ε : ℝ) (hε : 0 < ε) (d : F) (hd : d ≠ 0) : (Adeles F)ˣ where
  val := ((fun _ => ε, fun _ => (ε : ℂ)), algebraMap F (FiniteAdeleRing (𝓞 F) F) d)
  inv := ((fun _ => ε⁻¹, fun _ => ((ε⁻¹ : ℝ) : ℂ)), algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹)
  val_inv := by
    refine Prod.ext (Prod.ext (funext fun _ => mul_inv_cancel₀ hε.ne') (funext fun _ => ?_)) ?_
    · change (ε : ℂ) * ((ε⁻¹ : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hε.ne', Complex.ofReal_one]
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) d * algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  inv_val := by
    refine Prod.ext (Prod.ext (funext fun _ => inv_mul_cancel₀ hε.ne') (funext fun _ => ?_)) ?_
    · change ((ε⁻¹ : ℝ) : ℂ) * (ε : ℂ) = 1
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hε.ne', Complex.ofReal_one]
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹ * algebraMap F (FiniteAdeleRing (𝓞 F) F) d = 1
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]

/-- A small positive scalar makes the Gaussian through $a\|z\|^2$ dominate a Gaussian: $\exists\varepsilon>0$ with
$\pi\varepsilon^2n\le a_w$ for all $w$. -/
theorem exists_small_eps {ι : Type} [Finite ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, Real.pi * (ε ^ 2 * n) ≤ a i := by
  have hc : Continuous fun ε : ℝ => Real.pi * (ε ^ 2 * n) := by fun_prop
  have h1 : ∀ᶠ ε in nhds (0 : ℝ), ∀ i, Real.pi * (ε ^ 2 * n) < a i :=
    eventually_all.mpr fun i => (hc.tendsto 0).eventually_lt_const (by simpa using ha i)
  obtain ⟨ε, h, hpos⟩ := ((h1.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0))).exists
  exact ⟨ε, hpos, fun i => (h i).le⟩

/-- The squared supremum norm is at most the sum of the squared entries. -/
theorem sq_pi_norm_le_sum {𝕜 : Type} [NormedField 𝕜] {n : ℕ} (z : Fin n → 𝕜) :
    ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have h : ‖z‖ ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **An invertible matrix is bounded below in the sum of squares**: $a\|z\|^2\le\sum_i\|(Mz)_i\|^2$ for some $a>0$,
over the real or the complex numbers. -/
theorem exists_sq_le_mulVec {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) (hM : M.det ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ z : Fin n → 𝕜, a * ‖z‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ z) i‖ ^ 2 := by
  set f := LinearMap.toContinuousLinearMap (Matrix.toLin' M⁻¹)
  set C := ‖f‖ + 1
  have hC : 0 < C := by positivity
  have hz : ∀ z, ‖z‖ ≤ C * ‖M *ᵥ z‖ := fun z => by
    have h1 : f (M *ᵥ z) = z := by
      simp only [f, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (Ne.isUnit hM), Matrix.one_mulVec]
    calc ‖z‖ = ‖f (M *ᵥ z)‖ := by rw [h1]
      _ ≤ ‖f‖ * ‖M *ᵥ z‖ := f.le_opNorm _
      _ ≤ C * ‖M *ᵥ z‖ := mul_le_mul_of_nonneg_right (by simp [C]) (norm_nonneg _)
  refine ⟨1 / C ^ 2, by positivity, fun z => ?_⟩
  have h2 : ‖z‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖(M *ᵥ z) i‖ ^ 2 := by
    calc ‖z‖ ^ 2 ≤ (C * ‖M *ᵥ z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz z) 2
      _ = C ^ 2 * ‖M *ᵥ z‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_pi_norm_le_sum _) (by positivity)
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  exact h2

/-- Scaling every entry by $c$ multiplies the sum of squared norms by at most $\|c\|^2n\|z\|^2$. -/
theorem sum_norm_mul_sq_le {𝕜 : Type} [NormedField 𝕜] {n : ℕ} (c : 𝕜) (z : Fin n → 𝕜) :
    ∑ i, ‖c * z i‖ ^ 2 ≤ ‖c‖ ^ 2 * n * ‖z‖ ^ 2 := by
  calc ∑ i, ‖c * z i‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ‖z i‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, mul_pow]
    _ ≤ ‖c‖ ^ 2 * ∑ _i : Fin n, ‖z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
    _ = ‖c‖ ^ 2 * n * ‖z‖ ^ 2 := by simp [mul_assoc]

/-- The sum of squared entries is at most $n\|z\|^2$. -/
theorem sum_norm_sq_le {𝕜 : Type} [NormedField 𝕜] {n : ℕ} (z : Fin n → 𝕜) :
    ∑ i, ‖z i‖ ^ 2 ≤ n * ‖z‖ ^ 2 := by
  simpa using sum_norm_mul_sq_le (1 : 𝕜) z

open Classical in
/-- The quadratic form of the Gaussian, read off from the components at the real and complex places. -/
theorem qV_fst_eq (y : AdeleSpace F (Fin n)) :
    qV (fun i => (y i).1) = ∑ w, ∑ i, ‖adR y w i‖ ^ 2 + 2 * ∑ w, ∑ i, ‖adC y w i‖ ^ 2 := by
  simp only [qV, adR, adC, Real.norm_eq_abs, sq_abs, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n))), Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]

theorem hessA_map_projC' (Q₀ : QuadForm (𝓞 F) n) (w : {w : InfinitePlace F // w.IsComplex}) :
    (hessA Q₀).map (adProjC F w) = hesAt Q₀ (σC w) := by
  rw [hessA, Matrix.map_map, ← RingHom.coe_comp, adProjC_diagRing]

theorem adC_mulVec' (M : Matrix (Fin n) (Fin n) (Adeles F)) (y : AdeleSpace F (Fin n))
    (w : {w : InfinitePlace F // w.IsComplex}) : adC (M *ᵥ y) w = M.map (adProjC F w) *ᵥ adC y w :=
  funext fun i => RingHom.map_mulVec (adProjC F w) M y i

open Classical in
/-- **$\hat\Phi$ with the archimedean Gaussian kept whole** (any number field). -/
theorem gaussTestHat_apply_gV (Q₀ : QuadForm (𝓞 F) n) (y : AdeleSpace F (Fin n)) :
    gaussTestHat Q₀ y = muFinVec F (Fin n) OHatVec *
      {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v}.indicator
        (fun y => ENNReal.ofReal (gV fun i => (hessA Q₀ *ᵥ y) i |>.1)) y := by
  classical
  rw [gaussTestHat, gaussDualTest]
  have hiff : (fun i => (hessA Q₀ *ᵥ y) i |>.2) ∈ {c : Fin n → FiniteAdeleRing (𝓞 F) F | ∀ i, c i ∈ DHat} ↔
      ∀ v, adV y v ∈ KH Q₀ v := by
    have : ∀ v, adV y v ∈ KH Q₀ v ↔ adV (hessA Q₀ *ᵥ y) v ∈ DV v := fun v => by
      rw [adV_mulVec', hessA_map_projV']; rfl
    simp only [this, mem_DV_iff, mem_ofPred_eq, DHat]
    exact forall_comm
  by_cases h : ∀ v, adV y v ∈ KH Q₀ v
  · rw [indicator_of_mem (hiff.mpr h), indicator_of_mem (show y ∈ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v}
      from h), one_mul]
  · rw [indicator_of_notMem (fun h' => h (hiff.mp h')),
      indicator_of_notMem (show y ∉ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v} from h), zero_mul, mul_zero]

/-- **Pointwise domination** $\hat\Phi(x)\le\mu_f(\hat{\mathcal O}^n)\,\Phi(tx)$ for a suitable idele $t$. -/
theorem exists_idele_gaussTestHat_le {Q₀ : QuadForm (𝓞 F) n}
    (hQ : Q₀.Nondegenerate) :
    ∃ t : (Adeles F)ˣ, ∀ x : AdeleSpace F (Fin n),
      gaussTestHat Q₀ x ≤ muFinVec F (Fin n) OHatVec * gaussTest F n (t • x) := by
  classical
  have hdet : ∀ {K : Type} [Field K] (σ : F →+* K), (hesAt Q₀ σ).det ≠ 0 := fun {K} _ σ => by
    rw [hesAt, show ((Q₀.map (algebraMap (𝓞 F) F)).hessian.map σ) =
      σ.mapMatrix (Q₀.map (algebraMap (𝓞 F) F)).hessian from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (hessF_det_ne_zero hQ)
  choose a ha hb using fun w : {w : InfinitePlace F // w.IsReal} => exists_sq_le_mulVec _ (hdet (σR w))
  choose b hb0 hbb using fun w : {w : InfinitePlace F // w.IsComplex} => exists_sq_le_mulVec _ (hdet (σC w))
  have hpos : ∀ i, 0 < Sum.elim (fun w => Real.pi * a w) (fun w => Real.pi * b w) i := by
    rintro (w | w)
    · exact mul_pos Real.pi_pos (ha w)
    · exact mul_pos Real.pi_pos (hb0 w)
  obtain ⟨ε, hε0, hε⟩ := exists_small_eps (Sum.elim (fun w => Real.pi * a w) (fun w => Real.pi * b w)) hpos n
  have hεa : ∀ w, ε ^ 2 * n ≤ a w := fun w => by
    have := hε (Sum.inl w)
    simp only [Sum.elim_inl] at this
    exact le_of_mul_le_mul_left this Real.pi_pos
  have hεb : ∀ w, ε ^ 2 * n ≤ b w := fun w => by
    have := hε (Sum.inr w)
    simp only [Sum.elim_inr] at this
    exact le_of_mul_le_mul_left this Real.pi_pos
  set T := (Filter.eventually_cofinite.mp (eventually_KH_eq_latL Q₀ hQ)).toFinset with hT
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_latL_finset (n := n) T (KH Q₀) (isBounded_KH Q₀ hQ)
  have hd0' : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  refine ⟨scaleIdele F ε hε0 (algebraMap (𝓞 F) F d) hd0', fun x => ?_⟩
  set t := scaleIdele F ε hε0 (algebraMap (𝓞 F) F d) hd0'
  rw [gaussTestHat_apply_gV, gaussTest]
  by_cases h : ∀ v, adV x v ∈ KH Q₀ v
  · have h' : ∀ v, adV (t • x) v ∈ LocalZeta.latL v n := fun v i => by
      have e : adV (t • x) v i = algebraMap (𝓞 F) (v.adicCompletion F) d * adV x v i := by
        change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) * adV x v i = _
        rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
      rw [e]
      by_cases hv : v ∈ T
      · exact hd v hv _ (h v) i
      · have hK : KH Q₀ v = LocalZeta.latL v n := by
          by_contra hne
          exact hv ((Set.Finite.mem_toFinset _).mpr hne)
        have := h v
        rw [hK] at this
        rw [map_mul]
        exact mul_le_one' (val_algebraMap_le_one v d) (this i)
    rw [indicator_of_mem (show x ∈ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v} from h),
      indicator_of_mem ((mem_OHatVec_iff _).mpr h'), one_mul]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    rw [gV_eq_exp, gV_eq_exp]
    refine Real.exp_le_exp.mpr ?_
    have e1 : ∀ w, adR (t • x) w = fun i => ε * adR x w i := fun w => rfl
    have e2 : ∀ w, adC (t • x) w = fun i => (ε : ℂ) * adC x w i := fun w => rfl
    have hR : ∀ w, ∑ i, ‖ε * adR x w i‖ ^ 2 ≤ ∑ i, ‖(hesAt Q₀ (σR w) *ᵥ adR x w) i‖ ^ 2 := fun w => by
      refine (sum_norm_mul_sq_le ε (adR x w)).trans ?_
      refine le_trans ?_ (hb w _)
      rw [Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_right (hεa w) (sq_nonneg _)
    have hC : ∀ w, ∑ i, ‖(ε : ℂ) * adC x w i‖ ^ 2 ≤ ∑ i, ‖(hesAt Q₀ (σC w) *ᵥ adC x w) i‖ ^ 2 := fun w => by
      refine (sum_norm_mul_sq_le (ε : ℂ) (adC x w)).trans ?_
      refine le_trans ?_ (hbb w _)
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_right (hεb w) (sq_nonneg _)
    have key : qV (fun i => ((t • x) i).1) ≤ qV (fun i => ((hessA Q₀ *ᵥ x) i).1) := by
      rw [qV_fst_eq, qV_fst_eq]
      simp only [e1, e2, adR_mulVec', adC_mulVec', hessA_map_projR', hessA_map_projC']
      exact add_le_add (Finset.sum_le_sum fun w _ => hR w)
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hC w) zero_le_two)
    nlinarith [Real.pi_pos]
  · rw [indicator_of_notMem (show x ∉ {y : AdeleSpace F (Fin n) | ∀ v, adV y v ∈ KH Q₀ v} from h), mul_zero]
    exact bot_le

/-- **$M_s\hat\Phi\le C\,M_s\Phi$ pointwise** (any number field $F$, any real $s$). -/
theorem mellinPhi_gaussTestHat_le {Q₀ : QuadForm (𝓞 F) n}
    (hQ : Q₀.Nondegenerate) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y, mellinPhi (gaussTestHat Q₀) s y ≤ C * mellinPhi (gaussTest F n) s y := by
  obtain ⟨t, ht⟩ := exists_idele_gaussTestHat_le hQ
  have hμ : muFinVec F (Fin n) OHatVec ≠ ⊤ := fun h => by
    have := muFinVec_OHatVec_toReal_pos (F := F) (n := n)
    rw [h, ENNReal.toReal_top] at this
    exact lt_irrefl 0 this
  have hw : ∀ z, zetaWeight (F := F) s n z =
      ENNReal.ofReal (ideleNorm F t ^ (-((n : ℝ) + 2 * s))) * zetaWeight s n (t * z) := fun z => by
    have h1 := ideleNorm_pos t
    have h2 := ideleNorm_pos z
    unfold zetaWeight
    rw [ideleNorm_mul, Real.mul_rpow h1.le h2.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg h1.le _), ← mul_assoc,
      ← Real.rpow_add h1, neg_add_cancel, Real.rpow_zero, one_mul]
  refine ⟨muFinVec F (Fin n) OHatVec * ENNReal.ofReal (ideleNorm F t ^ (-((n : ℝ) + 2 * s))),
    ENNReal.mul_ne_top hμ ENNReal.ofReal_ne_top, fun y => ?_⟩
  unfold mellinPhi
  calc ∫⁻ z, zetaWeight s n z * gaussTestHat Q₀ (z • y) ∂tamIdeles F
      ≤ ∫⁻ z, zetaWeight s n z * (muFinVec F (Fin n) OHatVec * gaussTest F n ((t * z) • y)) ∂tamIdeles F := by
        refine lintegral_mono fun z => mul_le_mul' le_rfl ?_
        have := ht (z • y)
        rwa [smul_smul] at this
    _ = muFinVec F (Fin n) OHatVec * ENNReal.ofReal (ideleNorm F t ^ (-((n : ℝ) + 2 * s))) *
          ∫⁻ z, zetaWeight s n (t * z) * gaussTest F n ((t * z) • y) ∂tamIdeles F := by
        rw [mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top), ← lintegral_const_mul' _ _ hμ]
        refine lintegral_congr fun z => ?_
        rw [hw z]
        ring
    _ = _ := by
        rw [lintegral_mul_left_eq_self (fun u => zetaWeight s n u * gaussTest F n (u • y)) t]

end QuadFormsKB.Tamagawa.Measure.Weil

end
