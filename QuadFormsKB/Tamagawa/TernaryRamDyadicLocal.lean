/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryBadLocal
import QuadFormsKB.Tamagawa.TernaryRamDyadic

/-!
# The local factor of the trace-zero lattice at the ramified dyadic places; $\tau(SO_3) = 2$ unconditionally

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, a finite place $v \mid 2$ with $v \in \mathrm{Ram}_f(D)$, the completion
$\mathfrak o_v \subset F_v$; a maximal order $\mathcal O$ of $D = (a,b)_F$ with a trace-zero frame, $Q_0$ with $Q_0\otimes F = Q_{\mathcal O^0}$.

* **The shape** (`TZFrame.exists_GL_ramDyadic`): $\mathcal O_v^0 = \{x \in D_v^0 : \operatorname{nrd}x \in \mathfrak o_v\}$ is maximal
  (`TZFrame.isInteger_of_eval`) and $\det H_{Q_0} = 8(\det P\,ab)^2$, so `exists_ram_dyadic_shape` gives
  $Q_0 \cong \langle u\rangle\perp\varpi T$ over $\mathfrak o_v$ with $T$ unimodular, $\bar T$ anisotropic, and $-u\,\mathrm{disc}(T) = g^2$.
* **The trace** (`TZFrame.absV_two_mul_re_ramDyadic`): $|2\operatorname{re}e_0|_v = 1$. With $f_0 \in \mathcal O_v^0$ the first vector of the
  new basis ($\operatorname{nrd}f_0 = u$) and $\lambda = c_{01}(T)/g$, the element $x = \tfrac12(1 + \lambda f_0)$ has $\operatorname{trd}x = 1$ and
  $\operatorname{nrd}x = -c_{00}c_{11}/(c_{01}^2 - 4c_{00}c_{11}) \in \mathfrak o_v$, so $x \in \mathcal O_v$.
* **The density** (`TZFrame.siegelDensity_ram_dyadic`): `localDensityForm_ram_dyadic` gives $\alpha_v = 2q^{e+2}(q+1)$, which is
  `tzFactor` there ($|D'|_v = q^{2e-2}$, $|8|_v = q^{-3e}$, $|\operatorname{re}e_0|_v = q^e$).

**Proves** `traceZeroRamDyadicLocalFactors` (the reduced input, now a theorem), `traceZeroBadLocalFactors` (the input), and
the unconditional headlines `ternaryTamagawaTwo` ($F$ totally real, $\mathcal O_F$ a PID, $F = \mathbb Q$ included) and the all-rank
corollaries `tamagawaNumberTwo_all_ranks`, `massFormula_all_ranks`, `siegelFormulaAt_all_ranks` and their $\mathbb Q$/$\mathbb Z$ forms.

Sources: Voight 2021, §§13.3, 22.1 (the maximal order of a local division algebra) [unverified]; Weil 1982, §3.7(a), Thm 3.7.1;
Kitaoka 1993, §5.6 [unverified]. Indices are 0-based.
-/

open NumberField IsDedekindDomain Matrix Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.LocalDensity
  QuadFormsKB.QuatZeta QuadFormsKB.HilbertModular QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]

section RamDyadic

variable {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem pi_dvd_two_of_mem (h2 : (2 : 𝓞 F) ∈ v.asIdeal) : NF.π v ∣ (2 : 𝔬) := by
  have := (NF.π_pow_dvd_ι_iff v 1 2).2 (by rwa [pow_one])
  rwa [pow_one, map_ofNat] at this

/-- **Maximality of $\mathcal O_v^0$ in DVR form:** $\varpi^2 \mid Q_0(z) \Rightarrow \varpi \mid z$ at a ramified place. -/
theorem TZFrame.hmax_ram (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (hv : v ∈ ramFin ha hb)
    {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∀ z : Fin 3 → 𝔬, NF.π v ^ 2 ∣ (NF.Qp v Q₀).eval z → ∀ i, NF.π v ∣ z i := by
  have hdiv := hdiv_of_mem_ramFin v ha hb hv
  have heq := localOrder_eq_valOrder ha hb hO hdiv
  have hπ := NF.irreducible_π v
  have hπF : algebraMap 𝔬 Fv (NF.π v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hπ.ne_zero
  intro z hz
  obtain ⟨c, hc⟩ := hz
  set x : Fin 3 → Fv := fun j => algebraMap 𝔬 Fv (z j) with hx
  have hint : IsLocalization.IsInteger 𝔬
      ((fr.QF.map (algebraMap F Fv)).eval ((algebraMap 𝔬 Fv (NF.π v))⁻¹ • x)) := by
    rw [eval_smul_vec, hx, ← fr.eval_Qp_coe v hQ, hc]
    refine ⟨c, ?_⟩
    rw [map_mul, map_pow]
    field_simp
  have hy := fr.isInteger_of_eval v hdiv heq _ hint
  intro i
  obtain ⟨d, hd⟩ := hy i
  refine ⟨d, IsFractionRing.injective 𝔬 Fv ?_⟩
  rw [map_mul, hd]
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **The discriminant of $Q_0$ in DVR form:** $\varpi^{2i}\det H_{Q_0} = 8\varpi^{2j}w^2$ with $w$ a unit. -/
theorem TZFrame.hdisc (ha : a ≠ 0) (hb : b ≠ 0) {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∃ (i j : ℕ) (w : 𝔬), IsUnit w ∧ NF.π v ^ (2 * i) * (NF.Qp v Q₀).hessian.det = 8 * NF.π v ^ (2 * j) * w ^ 2 := by
  have hπ := NF.irreducible_π v
  set r : F := fr.Pm.det * algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b with hr
  have hr0 : r ≠ 0 := by
    have := fr.detHalf_ne_zero ha hb hQ
    rw [fr.detHalf_eq hQ] at this
    intro h0; apply this; rw [show fr.Pm.det ^ 2 * (algebraMap (𝓞 F) F a) ^ 2 * (algebraMap (𝓞 F) F b) ^ 2 =
      r ^ 2 by rw [hr]; ring, h0]; ring
  have hdetF : algebraMap (𝓞 F) F Q₀.hessian.det = 8 * r ^ 2 := by
    have h2' := fr.detHalf_eq hQ
    rw [detHalf] at h2'
    rw [hr]; field_simp at h2'; linear_combination h2'
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝔬) (algebraMap F Fv r)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hxy
    exact (map_ne_zero _).mpr hr0 hxy.symm
  obtain ⟨m₁, w₁, rfl, hw₁⟩ : ∃ m w, x = NF.π v ^ m * w ∧ IsUnit w := by
    obtain ⟨m, hm, hm'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hx0
    obtain ⟨w, hw, hwu⟩ := DVR.dvr_exact hπ hm hm'
    exact ⟨m, w, hw, hwu⟩
  obtain ⟨m₂, w₂, rfl, hw₂⟩ : ∃ m w, y = NF.π v ^ m * w ∧ IsUnit w := by
    obtain ⟨m, hm, hm'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hy0
    obtain ⟨w, hw, hwu⟩ := DVR.dvr_exact hπ hm hm'
    exact ⟨m, w, hw, hwu⟩
  refine ⟨m₂, m₁, w₁ * ↑hw₂.unit⁻¹, hw₁.mul (Units.isUnit _), ?_⟩
  have hcomm : algebraMap 𝔬 Fv (NF.ι v Q₀.hessian.det) = algebraMap F Fv (algebraMap (𝓞 F) F Q₀.hessian.det) := rfl
  have hyF : algebraMap 𝔬 Fv (NF.π v ^ m₂ * w₂) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hy0
  have key : NF.ι v Q₀.hessian.det * (NF.π v ^ m₂ * w₂) ^ 2 = 8 * (NF.π v ^ m₁ * w₁) ^ 2 := by
    apply IsFractionRing.injective 𝔬 Fv
    rw [map_mul, hcomm, hdetF]
    simp only [map_mul, map_pow, map_ofNat]
    rw [← hxy]
    simp only [map_mul, map_pow] at hyF ⊢
    field_simp
    rw [div_eq_iff hyF]; ring
  rw [NF.det_hessian_Qp]
  have hinv : w₂ * ↑hw₂.unit⁻¹ = 1 := hw₂.mul_val_inv
  calc NF.π v ^ (2 * m₂) * NF.ι v Q₀.hessian.det
      = NF.π v ^ (2 * m₂) * NF.ι v Q₀.hessian.det * (w₂ * ↑hw₂.unit⁻¹) ^ 2 := by rw [hinv]; ring
    _ = (NF.ι v Q₀.hessian.det * (NF.π v ^ m₂ * w₂) ^ 2) * (↑hw₂.unit⁻¹) ^ 2 := by ring
    _ = 8 * NF.π v ^ (2 * m₁) * (w₁ * ↑hw₂.unit⁻¹) ^ 2 := by rw [key]; ring

/-- **The shape of $\mathcal O_v^0$ at a ramified dyadic place:** $Q_0 \cong \langle u\rangle\perp\varpi T$ over $\mathfrak o_v$. -/
theorem TZFrame.exists_GL_ramDyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∃ (W : Matrix (Fin 3) (Fin 3) 𝔬) (u : 𝔬) (T : QuadForm 𝔬 2), IsUnit W.det ∧ IsUnit u ∧ IsUnit T.hessian.det ∧
      (∀ x : Fin 2 → 𝔬, NF.π v ∣ T.eval x → ∀ i, NF.π v ∣ x i) ∧ (NF.Qp v Q₀).compMat W = splitForm u (NF.π v • T) ∧
      ∃ g : 𝔬, IsUnit g ∧ -u * (T.coeff 0 1 ^ 2 - 4 * T.coeff 0 0 * T.coeff 1 1) = g ^ 2 :=
  exists_ram_dyadic_shape (NF.irreducible_π v) two_ne_zero (pi_dvd_two_of_mem v h2) _
    (fr.hmax_ram v ha hb hO hv hQ) (fr.hdisc v ha hb hQ)

/-- **At a ramified dyadic place $|2\operatorname{re}e_0|_v = 1$.** The element $x = \tfrac12 + \tfrac{\lambda}2f_0$ ($f_0$ the first new basis
vector, $\operatorname{nrd}f_0 = u$, $\lambda = c_{01}(T)/g$) has $\operatorname{nrd}x = uc_{00}c_{11}/g^2 \in \mathfrak o_v$ and $\operatorname{re}x = \tfrac12$, so $x \in \mathcal O_v$
and its $e_0$-coordinate $c$ satisfies $c\cdot2\operatorname{re}e_0 = 1$. -/
theorem TZFrame.absV_two_mul_re_ramDyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    absV v (2 * (fr.e 0 : QuatF F a b).re) = 1 := by
  obtain ⟨W, u, T, hWu, huu, hTu, haniso, hW, g, hg, hgu⟩ := fr.exists_GL_ramDyadic v ha hb hO hv h2 hQ
  have hdiv := hdiv_of_mem_ramFin v ha hb hv
  have heq := localOrder_eq_valOrder ha hb hO hdiv
  set ρ := (fr.e 0 : QuatF F a b).re
  set ι' := algebraMap 𝔬 Fv with hι'
  -- `f₀` and its norm
  set z0 : Fin 3 → 𝔬 := fun l => W l 0 with hz0
  set f0 : QuatV v a b := fr.psiv v (fun l => ι' (z0 l)) with hf0
  have hSz0 : (NF.Qp v Q₀).eval z0 = u := by
    have := congrArg (fun S : QuadForm 𝔬 3 => S.coeff 0 0) hW
    simp only [compMat_coeff, le_refl, ite_true] at this
    rw [this]; simp [splitForm_coeff]
  have hnrd0 : nrd f0 = ι' u := by
    rw [hf0, ← fr.eval_QF_map, ← fr.eval_Qp_coe v hQ, hSz0]
  have hre0 : f0.re = 0 := fr.re_psiv v _
  -- the element `x`
  set B := T.coeff 0 1 with hB
  have hg0 : ι' g ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hg.ne_zero
  set c : Fv := ι' B / (2 * ι' g) with hc
  set x : QuatV v a b := ⟨1 / 2, 0, 0, 0⟩ + c • f0 with hx
  have hxre : x.re = 1 / 2 := by
    simp only [hx, QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hre0, mul_zero, add_zero]
  have hnrdx : nrd x = ι' (u * T.coeff 0 0 * T.coeff 1 1 * ↑hg.unit⁻¹ ^ 2) := by
    have h2F : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    have hgi : ι' g * ι' ↑hg.unit⁻¹ = 1 := by rw [← map_mul, hg.mul_val_inv, map_one]
    have hgu' : -ι' u * (ι' B ^ 2 - 4 * ι' (T.coeff 0 0) * ι' (T.coeff 1 1)) = ι' g ^ 2 := by
      have := congrArg ι' hgu
      simpa [map_mul, map_sub, map_pow, map_neg, map_ofNat] using this
    have hn : nrd x = 1 / 4 + c ^ 2 * nrd f0 := by
      simp only [nrd, hx, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
        QuaternionAlgebra.imK_smul, smul_eq_mul, hre0]
      ring
    rw [hn, hnrd0, hc]
    simp only [map_mul, map_pow]
    have hginv : ι' ↑hg.unit⁻¹ = (ι' g)⁻¹ := eq_inv_of_mul_eq_one_right hgi
    rw [hginv]
    field_simp
    linear_combination (-4 : Fv) * hgu'
  have hxmem : x ∈ localOrder (v := v) a b O := by
    rw [heq, mem_valOrder, hnrdx]; exact ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ := (mem_localOrder_iff fr.e fr.isOrder x).1 hxmem 0
  have hre := fr.re_eq_repr v x
  rw [complHom_re, hxre] at hre
  have h1 : ι' c0 * algebraMap F Fv (2 * ρ) = 1 := by
    rw [hc0, map_mul, map_ofNat]
    have h2F : (2 : Fv) ≠ 0 := two_ne_zero_Fv v
    linear_combination (2 : Fv) * hre.symm
  have hle : ‖ι' c0‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c0.2)
  have hge : 1 ≤ absV v (2 * ρ) := by
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 : absV v (2 * ρ) = ‖algebraMap F Fv (2 * ρ)‖ := rfl
    rw [h3]
    nlinarith [norm_nonneg (ι' c0), norm_nonneg (algebraMap F Fv (2 * ρ))]
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd fr.isOrder (fr.e 0).2).1
  have hle' : absV v (2 * ρ) ≤ 1 := by
    have := absV_int_le_one v t; rwa [ht, trd] at this
  exact le_antisymm hle' hge

/-- **The local factor at a ramified dyadic place** ($v \mid 2$, $v \in \mathrm{Ram}_f$): $\alpha_v(Q_0, Q_0) = 2q^{e+2}(q+1)$, which is
`tzFactor` there: $(1 - q^{-2})\frac{2}{1 - q^{-1}}\cdot|8|_v^{-1}|D'|_v^{-3/2}|\operatorname{re}e_0|_v = 2(1 + q^{-1})q\cdot q^{3e}\cdot q^{3-3e}\cdot q^e$
($\det H_{Q_0} \sim 2\varpi^2$, so $|D'|_v = q^{2e-2}$). -/
theorem TZFrame.siegelDensity_ram_dyadic (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∈ ramFin ha hb) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) {_inst : Decidable (v ∈ ramFin ha hb)} :
    NF.siegelDensity v Q₀ Q₀ = tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re) := by
  obtain ⟨W, u, T, hWu, huu, hTu, haniso, hW, -⟩ := fr.exists_GL_ramDyadic v ha hb hO hv h2 hQ
  have hπ := NF.irreducible_π v
  obtain ⟨e, he, he'⟩ := exists_ord_two v
  have he1 : 1 ≤ e := by
    by_contra h0
    push Not at h0
    interval_cases e
    apply he'
    rw [zero_add, pow_one]
    exact pi_dvd_two_of_mem v h2
  rw [siegelDensity_eq_of_compMat v Q₀ W hWu hW,
    localDensityForm_ram_dyadic hπ two_ne_zero ⟨he, he'⟩ he1 huu T hTu haniso]
  set X : ℝ := (normP v : ℝ) ^ e with hX
  have hX0 : 0 < X := pow_pos (normP_pos v) e
  have hq := normP_pos v
  have h2v := absV_two_eq v he he'
  rw [← hX] at h2v
  -- `|re e₀| = |2|⁻¹`
  have hρ : absV v (fr.e 0 : QuatF F a b).re = X := by
    have h := fr.absV_two_mul_re_ramDyadic v ha hb hO hv h2 hQ
    rw [absV_mul, h2v] at h
    field_simp at h
    linarith
  -- `det H_{Q₀} ∼ 2 ϖ²`
  obtain ⟨t, ht, htu⟩ := DVR.dvr_exact hπ he he'
  have hdet : NF.ι v Q₀.hessian.det * W.det ^ 2 = NF.π v ^ (e + 2) * (t * u * T.hessian.det) := by
    have h1 := congrArg Matrix.det (hessian_compMat (NF.Qp v Q₀) W)
    rw [hW, det_hessian_splitForm, show (NF.π v • T).hessian = NF.π v • T.hessian by
      ext i j; simp only [hessian, smul_coeff, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
        smul_eq_mul, mul_add], det_smul, Fintype.card_fin, det_mul, det_mul, det_transpose,
      NF.det_hessian_Qp] at h1
    rw [pow_add]
    linear_combination -h1 + (u * NF.π v ^ 2 * T.hessian.det) * ht
  have hunit : IsUnit (t * u * T.hessian.det) := (htu.mul huu).mul hTu
  have hc2 : NF.π v ^ (e + 2) ∣ NF.π v ^ (e + 2) * (t * u * T.hessian.det) := dvd_mul_right _ _
  have hc3 : ¬ NF.π v ^ (e + 2 + 1) ∣ NF.π v ^ (e + 2) * (t * u * T.hessian.det) := by
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)]
    exact DVR.dvr_not_dvd_of_isUnit hπ hunit
  obtain ⟨hde, hde'⟩ := pow_dvd_of_mul_unit v (hWu.pow 2) hdet hc2 hc3
  have hD : absV v (detHalf Q₀) = (X * (normP v : ℝ)⁻¹) ^ 2 := by
    rw [detHalf, absV_div, absV_of_pow_dvd v hde hde', absV_eight_eq v he he', ← hX, hX]
    field_simp
    ring
  unfold tzFactor
  rw [if_pos hv, absV_eight_eq v he he', ← hX, hρ, hD, rpow_sq_neg_three_halves (by positivity),
    normP_rpow_neg_two, Real.rpow_neg_one, NF.q_completion]
  have hq1 : (normP v : ℝ)⁻¹ < 1 := by
    have := two_le_normP v
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < normP v))
  have hne : 1 - (normP v : ℝ)⁻¹ ≠ 0 := by linarith
  have hq2 : (2 : ℝ) ≤ normP v := by exact_mod_cast two_le_normP v
  have hne2 : (normP v : ℝ) - 1 ≠ 0 := by linarith
  rw [show 1 - (normP v : ℝ)⁻¹ = ((normP v : ℝ) - 1) / normP v by field_simp, hX]
  field_simp
  ring

end RamDyadic

/-! ### The inputs are theorems: $\tau(SO_3) = 2$ unconditionally -/

section Unconditional

open Classical in
/-- **The reduced input holds:** the local factors of the trace-zero lattices at the ramified dyadic places
(`TraceZeroRamDyadicLocalFactors F` is now a theorem). -/
theorem traceZeroRamDyadicLocalFactors : TraceZeroRamDyadicLocalFactors F :=
  ⟨fun _a _b ha hb _hdef _O hO fr _Q₀ hQ v h2 hv => fr.siegelDensity_ram_dyadic v ha hb hO hv h2 hQ⟩

/-- **The input holds:** `TraceZeroBadLocalFactors F` for every number field $F$ with $\mathcal O_F$ a PID. -/
theorem traceZeroBadLocalFactors : TraceZeroBadLocalFactors F :=
  TraceZeroBadLocalFactors.of_ramDyadic traceZeroRamDyadicLocalFactors

/-- **$\tau(SO_3) = 2$ for the trace-zero forms, unconditionally** ($F$ totally real, $\mathcal O_F$ a PID, $F = \mathbb Q$ included):
`TernaryTamagawaTwo F`. -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65"]
theorem ternaryTamagawaTwo_pid [IsTotallyReal F] : TernaryTamagawaTwo F :=
  ternaryTamagawaTwo_of_ramDyadicLocalFactors traceZeroRamDyadicLocalFactors

end Unconditional

end QuadFormsKB.QuatOrder

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.QuatOrder

section NFUncond

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **$\tau(SO(Q_0)) = 2$ in every rank $N \ge 3$, unconditionally** ($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a PID, $Q_0$ totally
positive definite). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; §3.7, Thm 3.7.1, p. 65"]
theorem tamagawaNumberTwo_all_ranks_uncond (hd : 2 ≤ Fintype.card (InfinitePlace F)) {N : ℕ} (hN : 3 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_ramDyadic hd traceZeroRamDyadicLocalFactors hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 3$, unconditionally** ($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a PID). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem massFormula_all_ranks_uncond (hd : 2 ≤ Fintype.card (InfinitePlace F)) {N : ℕ} (hN : 3 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_ramDyadic hd traceZeroRamDyadicLocalFactors hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N \ge 4$, unconditionally** ($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a
PID). -/
@[kb "weil1982" "§4.5, p. 100, Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_all_ranks_uncond (hd : 2 ≤ Fintype.card (InfinitePlace F)) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_of_ramDyadic hd traceZeroRamDyadicLocalFactors hN Q₀ hpd hm

end NFUncond

section RatUncond

/-- **$\tau(SO) = 2$ over $\mathbb Q$ in every rank $N \ge 3$, unconditionally.** -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 and Thm. 3.7.1, p. 65, over ℚ"]
theorem tamagawaNumberTwo_rat_all_ranks_uncond {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_rat_all_ranks_of_ramDyadic traceZeroRamDyadicLocalFactors hN Q₀ hpd

/-- **Siegel's formula over $\mathbb Q$ in every rank $N \ge 4$, unconditionally.** -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every rank ≥ 4 [unverified]"]
theorem siegelFormulaAt_rat_all_ranks_uncond {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ} (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_rat_all_ranks_of_ramDyadic traceZeroRamDyadicLocalFactors hN Q₀ hpd hm

/-- **Hanke's Siegel formula over $\mathbb Z$ in every rank $N \ge 4$, unconditionally:** for every positive definite integral
quadratic form $Q$ in $N \ge 4$ variables, `Siegel.SiegelFormula Q`. -/
@[kb "siegel1935" "Hauptsatz, every rank ≥ 4, Hanke's (5.3) form over ℤ [unverified]"]
theorem siegelFormula_int_all_ranks_uncond {N : ℕ} (hN : 4 ≤ N) (Q : QuadForm ℤ N) (hQ : IntQF.PosDef Q) :
    Siegel.SiegelFormula Q :=
  siegelFormula_int_all_ranks_of_ramDyadic traceZeroRamDyadicLocalFactors hN Q hQ

end RatUncond

end QuadFormsKB.Tamagawa

