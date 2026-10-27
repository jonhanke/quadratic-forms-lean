/-
# Hilbert modular forms: reduction theory to finitely many cusps

Let $F$ be totally real of degree $d$, $\mathcal{O} = \mathcal{O}_F$, $\mathfrak N \ne 0$ an integral ideal, and $N(y) = \prod_vy_v$.

**Short vectors (Minkowski)** (`exists_short_vector`). There is $K > 0$ (depending only on $F$) such that for every
$z = x + iy \in \mathbb{H}^d$ there are $(c, d) \in \mathcal{O}^2\setminus 0$ with
$$|\sigma_v(c)z_v + \sigma_v(d)|^2 \le K\,y_v\qquad\text{for every place } v.$$
*Proof.* The image of $\mathcal{O}^2$ in $E = \mathbb{R}^d \times \mathbb{R}^d$ is a lattice (basis `pairBasis 1`). The linear map
$T_z(w, u) = (\sqrt y\,w,\ \sqrt y^{-1}(xw + u))$ (componentwise; `twistMap`) preserves Lebesgue measure: it is a shear
(a skew product of translations) followed by a diagonal map of determinant $\prod_v\sqrt{y_v}\cdot\prod_v\sqrt{y_v}^{-1} = 1$
(`measurePreserving_twistMap`). Minkowski's convex body theorem (Mathlib's
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) applied to the convex symmetric set
$T_z^{-1}(\text{ball of radius } r)$, with $r$ fixed by the covolume, gives a nonzero lattice point $(\sigma c, \sigma d)$
with $|\sqrt{y_v}\sigma_v(c)| \le r$ and $|\sigma_v(c)x_v + \sigma_v(d)| \le r\sqrt{y_v}$, whence $|\sigma_v(c)z_v + \sigma_v(d)|^2 \le 2r^2y_v$.

**Reduction to finitely many cusps** (`exists_cusp_reduction`). There are finitely many $A_1, \dots, A_r \in \mathrm{SL}_2(F)$
and $c_0 > 0$ such that every $z \in \mathbb{H}^d$ has some $A_j$ and $\gamma \in \Gamma(\mathfrak N)$ with
$$N(\operatorname{Im}(A_j\gamma z)) \ge c_0 .$$
*Proof.* Take a short vector $x = (c, d)$ for $z$; by `finite_cusps` (C5a) there are $s$ in a fixed finite set $S$,
$t \in F^\times$ and $\gamma_0 \in \Gamma(\mathfrak N)$ with $(tx)\gamma_0 = s$. Let $A_s$ be a matrix with bottom row $s$
(`bottomMat`) and $\gamma = \gamma_0^{-1}$; then $A_s\gamma$ has bottom row $tx$, so
$N(\operatorname{Im}(A_s\gamma z)) = N(y)/\prod_v|\sigma_v(t)|^2|\sigma_v(c)z_v + \sigma_v(d)|^2 \ge 1/(N(t)^2K^d)$. Finally
$|N(t)| \le N(\mathfrak b(s))$, where $\mathfrak b(s)$ is the ideal of $s$: $\mathfrak b(s) = t\,\mathfrak b(x)$ ($\mathfrak b$ is
$\mathrm{SL}_2(\mathcal{O})$-invariant, `cuspIdeal_rowMul_SL2O`) and $N(\mathfrak b(x)) \ge 1$ because $\mathfrak b(x)$ is integral.

This is the reduction step of the classical theory (a weak form of "every point is equivalent to a point of a Siegel set
at one of the cusps"); the unit part of the Siegel set is handled in `CuspBound.lean`.

Sources: Siegel, *Lectures on Advanced Analytic Number Theory* (Tata, 1961/65), Ch. III (reduction for Hilbert modular groups)
[unverified]; van der Geer, *Hilbert Modular Surfaces* (1988), Ch. I §2–3 [unverified]; Garrett, *Holomorphic Hilbert Modular
Forms* (1990), Ch. 1 [unverified]; Freitag, *Hilbert Modular Forms* (1990), Ch. I §2 (fundamental domains) [unverified].
-/
import QuadFormsKB.HilbertModular.CuspFinite

open MeasureTheory Matrix NumberField UpperHalfPlane Complex
open scoped MatrixGroups nonZeroDivisors ENNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### The twisting map and Minkowski's theorem -/

section Minkowski

variable {ι : Type*} [Fintype ι]

/-- **The twisting map** $T_{x,s}(w, u) = (s\,w,\ s^{-1}(xw + u))$ on $\mathbb{R}^\iota \times \mathbb{R}^\iota$ (componentwise products). For
$z = x + iy$ and $s = \sqrt y$ it sends the lattice point $(\sigma c, \sigma d)$ to $(\sqrt y\,\sigma c,\ (\sigma c\,x + \sigma d)/\sqrt y)$. -/
noncomputable def twistMap (x s : ι → ℝ) : ((ι → ℝ) × (ι → ℝ)) →ₗ[ℝ] ((ι → ℝ) × (ι → ℝ)) where
  toFun p := (s * p.1, s⁻¹ * (x * p.1 + p.2))
  map_add' p q := by ext v <;> simp <;> ring
  map_smul' c p := by ext v <;> simp <;> ring

lemma twistMap_apply (x s : ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) :
    twistMap x s p = (s * p.1, s⁻¹ * (x * p.1 + p.2)) := rfl

lemma map_mul_left_volume_pi {s : ι → ℝ} (hs : ∀ v, s v ≠ 0) :
    Measure.map (fun w : ι → ℝ => s * w) volume = ENNReal.ofReal |(∏ v, s v)⁻¹| • volume := by
  classical
  have h : (fun w : ι → ℝ => s * w) = ⇑(Matrix.toLin' (Matrix.diagonal s)) := by
    funext w v; simp [Matrix.mulVec_diagonal]
  rw [h, Real.map_matrix_volume_pi_eq_smul_volume_pi (by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun v _ => hs v), det_diagonal]

/-- **The twisting map preserves Lebesgue measure** for $s > 0$: a shear $(w, u) \mapsto (w, xw + u)$ (a skew product of
translations) followed by $(w, u) \mapsto (sw, s^{-1}u)$, of determinant $\prod_vs_v\cdot\prod_vs_v^{-1} = 1$. -/
theorem measurePreserving_twistMap (x s : ι → ℝ) (hs : ∀ v, 0 < s v) :
    MeasurePreserving (twistMap x s) volume volume := by
  have hsh : MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, x * p.1 + p.2))
      volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).skew_product (g := fun a b => x * a + b)
      (by fun_prop) (Filter.Eventually.of_forall fun a =>
        (measurePreserving_add_left volume (x * a)).map_eq)
  have hd : MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => (s * p.1, s⁻¹ * p.2))
      volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have h1 := map_mul_left_volume_pi (fun v => (hs v).ne')
    have h2 := map_mul_left_volume_pi (s := s⁻¹) (fun v => inv_ne_zero (hs v).ne')
    rw [Measure.volume_eq_prod]
    rw [show (fun p : (ι → ℝ) × (ι → ℝ) => (s * p.1, s⁻¹ * p.2)) =
      Prod.map (fun w => s * w) (fun w => s⁻¹ * w) from rfl,
      ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, h2,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    have hP : 0 < ∏ v, s v := Finset.prod_pos fun v _ => hs v
    rw [show (∏ v, (s⁻¹) v) = (∏ v, s v)⁻¹ by simp [Finset.prod_inv_distrib], inv_inv,
      abs_of_pos hP, abs_of_pos (inv_pos.mpr hP), ← ENNReal.ofReal_mul (inv_pos.mpr hP).le,
      inv_mul_cancel₀ hP.ne', ENNReal.ofReal_one, one_smul]
  have := hd.comp hsh
  convert this using 1
  funext p
  simp [twistMap_apply, Function.comp_apply]

/-- **Minkowski for twisted boxes.** For a basis $b$ of $E = \mathbb{R}^\iota \times \mathbb{R}^\iota$ ($\iota \ne \emptyset$) there is $r > 0$
such that for all $x$ and all $s > 0$ some nonzero point $p$ of the lattice $\bigoplus\mathbb{Z}b_j$ has $\|T_{x,s}(p)\| \le r$
(sup norm). -/
theorem exists_twist_short {J : Type*} [Finite J] [Nonempty ι]
    (b : Module.Basis J ℝ ((ι → ℝ) × (ι → ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x s : ι → ℝ, (∀ v, 0 < s v) →
      ∃ p ∈ Submodule.span ℤ (Set.range b), p ≠ 0 ∧ ‖twistMap x s p‖ ≤ r := by
  set D := ZSpan.fundamentalDomain b
  have hfund := ZSpan.isAddFundamentalDomain' b (volume : Measure ((ι → ℝ) × (ι → ℝ)))
  have hDfin : volume D ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  set n := Fintype.card ι
  have hn : 0 < n := Fintype.card_pos
  have hfr : Module.finrank ℝ ((ι → ℝ) × (ι → ℝ)) = n + n := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  set r : ℝ := (volume D).toReal + 1
  have hr1 : 1 ≤ r := by simp only [r]; linarith [ENNReal.toReal_nonneg (a := volume D)]
  have hr0 : 0 < r := by linarith
  refine ⟨r, hr0, fun x s hs => ?_⟩
  set S := (twistMap x s) ⁻¹' Metric.closedBall (0 : (ι → ℝ) × (ι → ℝ)) r
  have hmp := measurePreserving_twistMap x s hs
  have hvolS : volume S = ENNReal.ofReal (2 * r) ^ n * ENNReal.ofReal (2 * r) ^ n := by
    rw [hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet,
      show (0 : (ι → ℝ) × (ι → ℝ)) = ((0 : ι → ℝ), (0 : ι → ℝ)) from rfl,
      ← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_pi_closedBall _ hr0.le, ENNReal.ofReal_pow (by positivity)]
  have hsymm : ∀ p ∈ S, -p ∈ S := by
    intro p hp
    simp only [S, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, map_neg,
      norm_neg] at hp ⊢
    exact hp
  have hconv : Convex ℝ S := (convex_closedBall _ _).linear_preimage _
  have hlt : volume D * 2 ^ Module.finrank ℝ ((ι → ℝ) × (ι → ℝ)) < volume S := by
    have e : ENNReal.ofReal (2 * r) ^ n * ENNReal.ofReal (2 * r) ^ n =
        2 ^ (n + n) * ENNReal.ofReal r ^ (n + n) := by
      rw [← pow_add, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
    rw [hvolS, hfr, e]
    -- `volume D < ofReal r ≤ ofReal r ^ (n + n)`
    have h1 : volume D < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_toReal hDfin]
      exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr (by simp only [r]; linarith)
    have h2 : ENNReal.ofReal r ≤ ENNReal.ofReal r ^ (n + n) := by
      have h1r : 1 ≤ ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr1
      calc ENNReal.ofReal r = ENNReal.ofReal r ^ 1 := (pow_one _).symm
        _ ≤ ENNReal.ofReal r ^ (n + n) := pow_le_pow_right₀ h1r (by omega)
    exact (ENNReal.mul_lt_mul_left (a := 2 ^ (n + n)) (by simp) (by simp) (h1.trans_le h2)).trans_eq
      (mul_comm _ _)
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    (inferInstance : Countable (Submodule.span ℤ (Set.range b)))
  have : (volume : Measure ((ι → ℝ) × (ι → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨p, hp0, hpS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hlt
  refine ⟨p, p.2, ?_, ?_⟩
  · intro h; apply hp0; exact Subtype.ext h
  · simpa [S, Metric.mem_closedBall, dist_zero_right] using hpS

end Minkowski

/-! ### Short vectors over a totally real field -/

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-- A point of the lattice $\bigoplus\mathbb{Z}b_j$ of `pairBasis 1` is $(\sigma c, \sigma d)$ with $c, d \in \mathcal{O}_F$. -/
lemma exists_of_mem_span_pairBasis_one {p : (InfinitePlace F → ℝ) × (InfinitePlace F → ℝ)}
    (hp : p ∈ Submodule.span ℤ (Set.range (pairBasis (1 : FIˣ)))) :
    ∃ c d : 𝓞 F, p = (realVec (c : F), realVec (d : F)) := by
  obtain ⟨m, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
  have key : ∀ m₁ : Fin (Module.finrank ℚ F) → ℤ,
      ∑ j, m₁ j • koecherBasis (1 : FIˣ) j = realVec (QuadFormsKB.Analysis.latElt (1 : FIˣ) m₁) := by
    intro m₁
    rw [← koecherBasis_symm, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℝ (m₁ j) _).symm
  have hO : ∀ m₁ : Fin (Module.finrank ℚ F) → ℤ, ∃ c : 𝓞 F,
      (c : F) = QuadFormsKB.Analysis.latElt (1 : FIˣ) m₁ := by
    intro m₁
    have h := latElt_mem (1 : FIˣ) m₁
    rw [Units.val_one] at h
    exact (FractionalIdeal.mem_one_iff _).mp h
  obtain ⟨c, hc⟩ := hO (fun j => m (Sum.inl j))
  obtain ⟨d, hd⟩ := hO (fun j => m (Sum.inr j))
  refine ⟨c, d, ?_⟩
  rw [hc, hd, ← key, ← key]
  ext1
  · rw [Fintype.sum_sum_type, Prod.fst_add, Prod.fst_sum, Prod.fst_sum]
    simp only [Prod.smul_fst, pairBasis, Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inr_fst, smul_zero, Finset.sum_const_zero, add_zero]
  · rw [Fintype.sum_sum_type, Prod.snd_add, Prod.snd_sum, Prod.snd_sum]
    simp only [Prod.smul_snd, pairBasis, Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_snd, smul_zero, Finset.sum_const_zero, zero_add]

/-- **Short vectors (Minkowski).** There is $K > 0$ such that every $z \in \mathbb{H}^d$ admits $(c, d) \in \mathcal{O}_F^2\setminus 0$ with
$$|\sigma_v(c)z_v + \sigma_v(d)|^2 \le K\operatorname{Im}z_v\qquad\text{for every place } v.$$
($\sigma_v$ = `realEmb F v`.) -/
@[kb "vandergeer1988" "Ch. I §2 (reduction theory: Minkowski short vectors) [unverified]"]
theorem exists_short_vector : ∃ K : ℝ, 0 < K ∧ ∀ z : InfinitePlace F → ℍ, ∃ c d : 𝓞 F,
    ((c : F) ≠ 0 ∨ (d : F) ≠ 0) ∧ ∀ v, Complex.normSq ((realEmb F v (c : F) : ℂ) * (z v : ℂ) +
      (realEmb F v (d : F) : ℂ)) ≤ K * (z v).im := by
  obtain ⟨r, hr, hshort⟩ := exists_twist_short (pairBasis (1 : FIˣ))
  refine ⟨2 * r ^ 2, by positivity, fun z => ?_⟩
  set x : InfinitePlace F → ℝ := fun v => (z v).re
  set s : InfinitePlace F → ℝ := fun v => Real.sqrt (z v).im
  have hs : ∀ v, 0 < s v := fun v => Real.sqrt_pos.mpr (z v).im_pos
  obtain ⟨p, hp, hp0, hpr⟩ := hshort x s hs
  obtain ⟨c, d, rfl⟩ := exists_of_mem_span_pairBasis_one hp
  refine ⟨c, d, ?_, fun v => ?_⟩
  · by_contra h
    push Not at h
    apply hp0
    rw [h.1, h.2]
    ext v <;> simp [realVec]
  · have h1 : |s v * realEmb F v (c : F)| ≤ r := by
      have := (norm_le_pi_norm (twistMap x s (realVec (c : F), realVec (d : F))).1 v).trans
        ((norm_fst_le _).trans hpr)
      simpa [twistMap_apply, realVec, Real.norm_eq_abs] using this
    have h2 : |(s v)⁻¹ * (x v * realEmb F v (c : F) + realEmb F v (d : F))| ≤ r := by
      have := (norm_le_pi_norm (twistMap x s (realVec (c : F), realVec (d : F))).2 v).trans
        ((norm_snd_le _).trans hpr)
      simpa [twistMap_apply, realVec, Real.norm_eq_abs] using this
    have hsq : s v ^ 2 = (z v).im := Real.sq_sqrt (z v).im_pos.le
    have hsv := hs v
    set a := realEmb F v (c : F)
    set e := realEmb F v (d : F)
    have hns : Complex.normSq ((a : ℂ) * (z v : ℂ) + (e : ℂ)) =
        (a * x v + e) ^ 2 + (a * (z v).im) ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, x]
      change (a * (z v).re + e) * (a * (z v).re + e) + (a * (z v).im) * (a * (z v).im) = _
      ring
    have e1 : (a * (z v).im) ^ 2 = (s v * a) ^ 2 * (z v).im := by rw [← hsq]; ring
    have e2 : (a * x v + e) ^ 2 = ((s v)⁻¹ * (x v * a + e)) ^ 2 * (z v).im := by
      rw [← hsq]; field_simp
    have b1 : (s v * a) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have b2 : ((s v)⁻¹ * (x v * a + e)) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have him := (z v).im_pos
    rw [hns, e1, e2]
    nlinarith

/-! ### Matrices with a given bottom row; ideals of cusp vectors -/

open Classical in
/-- **A matrix with bottom row $s$**: $\begin{pmatrix}0&-s_0^{-1}\\s_0&s_1\end{pmatrix}$ if $s_0 \ne 0$,
$\begin{pmatrix}s_1^{-1}&0\\0&s_1\end{pmatrix}$ if $s_0 = 0 \ne s_1$ (and $1$ for $s = 0$, a junk value). Its bottom row is
$(s_0, s_1)$ (`bottomMat_row`), i.e. $(0,1)\,\mathrm{bottomMat}(s) = s$. -/
noncomputable def bottomMat (s : F × F) : SL(2, F) :=
  if h : s.1 = 0 then
    if h2 : s.2 = 0 then 1 else ⟨!![s.2⁻¹, 0; 0, s.2], by simp [det_fin_two_of, h2]⟩
  else ⟨!![0, -s.1⁻¹; s.1, s.2], by simp [det_fin_two_of, h]⟩

lemma bottomMat_row {s : F × F} (hs : s.1 ≠ 0 ∨ s.2 ≠ 0) :
    bottomMat s 1 0 = s.1 ∧ bottomMat s 1 1 = s.2 := by
  unfold bottomMat
  by_cases h : s.1 = 0
  · have h2 : s.2 ≠ 0 := hs.resolve_left (not_not.mpr h)
    simp only [h, h2, ↓reduceDIte]
    simp
  · simp only [h, ↓reduceDIte]
    simp

/-- The bottom row of $AB$ is (bottom row of $A$)$\cdot B$. -/
lemma mul_row (A B : SL(2, F)) :
    ((A * B) 1 0, (A * B) 1 1) = rowMul (A 1 0, A 1 1) B := by
  simp only [rowMul, sl2_mul_apply]

/-- **The ideal of a cusp vector is $\mathrm{SL}_2(\mathcal{O}_F)$-invariant** (right action): $\mathfrak b(xg) = \mathfrak b(x)$. -/
lemma cuspIdeal_rowMul_SL2O (g : SL(2, 𝓞 F)) (x : F × F) :
    cuspIdeal (rowMul x (toF F g)).1 (rowMul x (toF F g)).2 = cuspIdeal x.1 x.2 := by
  have hle : ∀ (g : SL(2, 𝓞 F)) (x : F × F),
      cuspIdeal (rowMul x (toF F g)).1 (rowMul x (toF F g)).2 ≤ cuspIdeal x.1 x.2 := by
    intro g x
    have := cuspIdeal_le_of (g 0 0) (g 1 0) (g 0 1) (g 1 1) x.1 x.2
    simpa only [rowMul_fst, rowMul_snd, toF_apply, Algebra.smul_def, mul_comm] using this
  refine le_antisymm (hle g x) ?_
  have h := hle g⁻¹ (rowMul x (toF F g))
  rwa [map_inv, rowMul_rowMul_inv] at h

/-- $N(\mathfrak b(c, d)) \ge 1$ for $(c, d) \in \mathcal{O}_F^2\setminus 0$: the ideal is integral and nonzero. -/
lemma one_le_absNorm_cuspIdeal (c d : 𝓞 F) (h : (c : F) ≠ 0 ∨ (d : F) ≠ 0) :
    1 ≤ FractionalIdeal.absNorm (cuspIdeal (c : F) (d : F)) := by
  have hle : cuspIdeal (c : F) (d : F) ≤ 1 := by
    rw [cuspIdeal, ← FractionalIdeal.sup_eq_add]
    refine sup_le ?_ ?_ <;> rw [FractionalIdeal.spanSingleton_le_iff_mem] <;>
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact cuspIdeal_ne_zero h (by rw [← hJ]; simp)
  rw [← hJ, FractionalIdeal.coeIdeal_absNorm]
  have : Ideal.absNorm J ≠ 0 := fun h0 => hJ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

/-- $\prod_v\sigma_v(t)^2 = N_{F/\mathbb{Q}}(t)^2$. -/
lemma prod_realEmb_sq (t : F) :
    ∏ v : InfinitePlace F, realEmb F v t ^ 2 = ((Algebra.norm ℚ t : ℚ) : ℝ) ^ 2 := by
  have h := InfinitePlace.prod_eq_abs_norm t
  have hm : ∀ v : InfinitePlace F, v.mult = 1 := fun v => by
    simp [InfinitePlace.mult, IsTotallyReal.isReal v]
  simp only [hm, pow_one] at h
  have e : ∀ v : InfinitePlace F, realEmb F v t ^ 2 = v t ^ 2 := fun v => by
    rw [← abs_realEmb, sq_abs]
  rw [Finset.prod_congr rfl fun v _ => e v, Finset.prod_pow, h, Rat.cast_abs, sq_abs]

/-- **The imaginary part after a matrix**: $\operatorname{Im}(Mz)_v = \operatorname{Im}z_v/|\sigma_v(c)z_v + \sigma_v(d)|^2$ for
$M = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F)$. -/
lemma im_slHom_smul (M : SL(2, F)) (z : InfinitePlace F → ℍ) (v : InfinitePlace F) :
    ((slHom (realEmb F) M • z) v).im = (z v).im /
      Complex.normSq (denom ((slHom (realEmb F) M v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)) := by
  rw [Pi.smul_apply', glPos_smul_eq, UpperHalfPlane.im_smul_eq_div_normSq, slHom_det, abs_one,
    one_mul]

lemma denom_slHom (M : SL(2, F)) (z : InfinitePlace F → ℍ) (v : InfinitePlace F) :
    denom ((slHom (realEmb F) M v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) =
      (realEmb F v (M 1 0) : ℂ) * (z v : ℂ) + (realEmb F v (M 1 1) : ℂ) := by
  simp [denom]

/-- **Reduction to finitely many cusps** ($\mathfrak N \ne 0$). There are a finite set $T \subseteq \mathrm{SL}_2(F)$ and $c_0 > 0$ such that
every $z \in \mathbb{H}^d$ has $A \in T$ and $\gamma \in \Gamma(\mathfrak N)$ with
$$N(\operatorname{Im}(A\gamma z)) = \prod_v\operatorname{Im}(A\gamma z)_v \ge c_0 .$$
($T$ consists of one matrix with bottom row $s$ for each $s$ in the finite set of cusp vectors of `finite_cusps`.) -/
@[kb "vandergeer1988" "Ch. I §2–3 (reduction theory; finitely many cusps) [unverified]"]
theorem exists_cusp_reduction {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) :
    ∃ T : Finset SL(2, F), ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : InfinitePlace F → ℍ, ∃ A ∈ T,
      ∃ γ ∈ GammaFull 𝔑, c₀ ≤ ∏ v, ((slHom (realEmb F) (A * γ) • z) v).im := by
  classical
  obtain ⟨K, hK, hshort⟩ := exists_short_vector (F := F)
  obtain ⟨S, hSfin, hS0, hScov⟩ := finite_cusps h𝔑
  set Sf := hSfin.toFinset
  set Nmax : ℝ := 1 + ∑ s ∈ Sf, (FractionalIdeal.absNorm (cuspIdeal s.1 s.2) : ℝ)
  have hN1 : 1 ≤ Nmax := by
    simp only [Nmax]
    linarith [Finset.sum_nonneg fun s (_ : s ∈ Sf) =>
      (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg (cuspIdeal s.1 s.2)) : (0:ℝ) ≤ _)]
  set n := Fintype.card (InfinitePlace F)
  refine ⟨Sf.image bottomMat, 1 / (Nmax ^ 2 * K ^ n), by positivity, fun z => ?_⟩
  obtain ⟨c, d, hcd, hb⟩ := hshort z
  obtain ⟨s, hsS, t, ht, γ₀, hγ₀, hrow⟩ := hScov ((c : F), (d : F)) hcd
  refine ⟨bottomMat s, Finset.mem_image_of_mem _ (hSfin.mem_toFinset.mpr hsS),
    (toF F γ₀)⁻¹, inv_mem (Subgroup.mem_map_of_mem _ hγ₀), ?_⟩
  -- the bottom row of `A γ` is `t (c, d)`
  have hrow' : ((bottomMat s * (toF F γ₀)⁻¹) 1 0, (bottomMat s * (toF F γ₀)⁻¹) 1 1) =
      (t * c, t * d) := by
    rw [mul_row, (bottomMat_row (hS0 s hsS)).1, (bottomMat_row (hS0 s hsS)).2]
    change rowMul s (toF F γ₀)⁻¹ = _
    rw [← hrow, rowMul_rowMul_inv]
  have h10 : (bottomMat s * (toF F γ₀)⁻¹) 1 0 = t * c := congrArg Prod.fst hrow'
  have h11 : (bottomMat s * (toF F γ₀)⁻¹) 1 1 = t * d := congrArg Prod.snd hrow'
  -- `|N(t)| ≤ Nmax`
  have hNt : |((Algebra.norm ℚ t : ℚ) : ℝ)| ≤ Nmax := by
    have hid : cuspIdeal s.1 s.2 = FractionalIdeal.spanSingleton (𝓞 F)⁰ t *
        cuspIdeal (c : F) (d : F) := by
      rw [← hrow, cuspIdeal_rowMul_SL2O]
      exact cuspIdeal_smul t _ _
    have habs := congrArg FractionalIdeal.absNorm hid
    rw [map_mul, FractionalIdeal.absNorm_span_singleton] at habs
    have h1 := one_le_absNorm_cuspIdeal c d hcd
    have hle : |(Algebra.norm ℚ t : ℚ)| ≤ FractionalIdeal.absNorm (cuspIdeal s.1 s.2) := by
      rw [habs]; exact le_mul_of_one_le_right (abs_nonneg _) h1
    have hle' : ((|(Algebra.norm ℚ t : ℚ)| : ℚ) : ℝ) ≤
        (FractionalIdeal.absNorm (cuspIdeal s.1 s.2) : ℝ) := Rat.cast_le.mpr hle
    have hmem : (FractionalIdeal.absNorm (cuspIdeal s.1 s.2) : ℝ) ≤
        ∑ s ∈ Sf, (FractionalIdeal.absNorm (cuspIdeal s.1 s.2) : ℝ) :=
      Finset.single_le_sum (f := fun s : F × F => (FractionalIdeal.absNorm (cuspIdeal s.1 s.2) : ℝ))
        (fun s _ => Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))
        (hSfin.mem_toFinset.mpr hsS)
    rw [← Rat.cast_abs]
    simp only [Nmax]; linarith
  -- termwise lower bound for the imaginary parts
  have hterm : ∀ v, 1 / (realEmb F v t ^ 2 * K) ≤
      ((slHom (realEmb F) (bottomMat s * (toF F γ₀)⁻¹) • z) v).im := by
    intro v
    rw [im_slHom_smul]
    have hden := denom_slHom (bottomMat s * (toF F γ₀)⁻¹) z v
    rw [h10, h11] at hden
    have hpos : 0 < Complex.normSq (denom ((slHom (realEmb F) (bottomMat s * (toF F γ₀)⁻¹) v :
        GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)) := Complex.normSq_pos.mpr (denom_ne_zero _ _)
    have hfac : Complex.normSq (denom ((slHom (realEmb F) (bottomMat s * (toF F γ₀)⁻¹) v :
        GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)) = realEmb F v t ^ 2 *
          Complex.normSq ((realEmb F v (c : F) : ℂ) * (z v : ℂ) + (realEmb F v (d : F) : ℂ)) := by
      rw [hden, show (realEmb F v (t * c) : ℂ) * (z v : ℂ) + (realEmb F v (t * d) : ℂ) =
        (realEmb F v t : ℂ) * ((realEmb F v (c : F) : ℂ) * (z v : ℂ) + (realEmb F v (d : F) : ℂ)) by
          simp only [map_mul, Complex.ofReal_mul]; ring, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have htv : 0 < realEmb F v t ^ 2 := by
      have : realEmb F v t ≠ 0 := (map_ne_zero_iff _ (realEmb_injective F v)).mpr ht
      positivity
    have hy := (z v).im_pos
    rw [div_le_div_iff₀ (by positivity) hpos, one_mul, hfac]
    have := hb v
    nlinarith
  calc 1 / (Nmax ^ 2 * K ^ n)
      ≤ 1 / (((Algebra.norm ℚ t : ℚ) : ℝ) ^ 2 * K ^ n) := by
        have hN0 : 0 < ((Algebra.norm ℚ t : ℚ) : ℝ) ^ 2 := by
          have : (Algebra.norm ℚ t : ℚ) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr ht
          positivity
        refine one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right ?_ (by positivity))
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hNt 2
    _ = ∏ v, 1 / (realEmb F v t ^ 2 * K) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_mul_distrib,
          prod_realEmb_sq, Finset.prod_const, Finset.card_univ]
    _ ≤ _ := Finset.prod_le_prod₀ (fun v _ => by
        have : realEmb F v t ≠ 0 := (map_ne_zero_iff _ (realEmb_injective F v)).mpr ht
        positivity) fun v _ => hterm v

end QuadFormsKB.HilbertModular
