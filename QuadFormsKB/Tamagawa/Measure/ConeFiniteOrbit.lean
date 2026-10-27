import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.ConeFiniteGroup
import QuadFormsKB.Tamagawa.Measure.ConeFiniteChart
import QuadFormsKB.Tamagawa.Measure.ConeRealOrbit

/-!
# The cone orbital identity at a finite place

Let $v$ be a finite place of a number field $F$ (dyadic places included), $c_0 \in \mathcal O_F\setminus\{0\}$,
$Q_0'$ a nondegenerate form over $\mathcal O_F$ in $k \ge 1$ variables, and
$$Q_{m,0} = \langle -c_0\rangle\perp Q_0',\qquad Q_0 = \langle c_0\rangle\perp Q_{m,0} = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'.$$
This file is the finite-place counterpart of `ConeReal.lean` (parametric identity, steps P1--P3) and `ConeRealOrbit.lean`
(cone type, orbit section, the cone orbital identity).

**The parametric identity** (`lintegral_cone_param`): with $\mu_{SO(Q)}$ = `muLocSO`, $\sigma'$ the Leray measure of the
sphere of $Q_{m,0}$ at $-c_0$ (`nuS`), $s'(y) = \mathrm{orb}(y, 1)$ the reflection section, and
$d(q)$, $n(w)$, $\mathrm{diag}(1,1,h)$ the elements of `ConeFiniteGroup`,
$$\int f\,d\mu_{SO(Q_0)} = |2c_0|_v^{-(k+1)}|2c_0|_v^{-k}\int_{F_v}\frac{|q|_v^k}{|2c_0q|_v}\int_{S'_{-c_0}}\int_{SO(Q_0')}
  \int_{F_v^k} f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,dw\,d\mu_{SO(Q_0')}(h)\,d\sigma'(y)\,dq.$$
The proof is the one at the real places: the sphere identity (for an arbitrary section) for $S_{c_0}$ with the
parabolic section $s(x) = d((x_0-x_1)^{-1})\,n(x')$, inversion (unimodularity), the hyperbolic-split chart of $S_{c_0}$,
the sphere identity for $S'_{-c_0}$, the commutation rules of the parabolic, and the substitution $w = h(-q^{-1}y)$ on
$F_v^k$ (Jacobian $|q|_v^{k}$ since $\det h = 1$).

**The cone orbital identity** (`lerayMeasure_cone_orbital_finitePlace`): $\mu_{SO(Q_0)} = |2c_0|_v^{-(2k+2)}\cdot
\Psi_*(\sigma_C\otimes\mu_P)$, with $\sigma_C$ the Leray measure of the punctured cone, $\mu_P$ the Haar measure of the
stabilizer $P = N\rtimes SO(Q_0')$ of $e = e_0+e_1$, and $\Psi(z, p) = s(z)\,p$ the explicit orbit section.
-/

open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal Pointwise
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm QuadFormsKB.LocalDensity QuadFormsKB.Analysis QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open QuadFormsKB.Tamagawa.Measure.FibreDecomp QuadFormsKB.Tamagawa.Measure.FibreConst
open QuadFormsKB.Tamagawa.Measure.LerayFinite QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.Weil

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### The form over $F_v$ and the integral models -/

section Bridge

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k)

/-- The values of the form $Q'_v$ over $F_v$ are the values of $Q_0'\otimes\mathfrak o_v$. -/
theorem eval_QFv (y : Fin k → Fv) : (QFv v Q₀').eval y = Qv v (NF.Qp v Q₀') y := by
  simp only [Qv, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, RingHom.id_apply,
    Algebra.algebraMap_self, QFv]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- **The shape of the cone form**: $Q(x) = c x_0^2 - c x_1^2 + Q'(x')$. -/
theorem qv_cone (x : Fin (k + 1 + 1) → Fv) :
    Qv v (NF.Qp v (Qcone c₀ Q₀')) x = cv v c₀ * x 0 ^ 2 - cv v c₀ * x 1 ^ 2 + Qv v (NF.Qp v Q₀') (tl x) := by
  have e : (Fin.cons (x 0) (Fin.cons (x 1) (tl x) : Fin (k + 1) → Fv) : Fin (k + 1 + 1) → Fv) = x := v3_eta x
  have hc : algebraMap (𝓞 F) Fv c₀ = cv v c₀ := IsScalarTower.algebraMap_apply (𝓞 F) F Fv c₀
  simp only [Qv, NF.evalIn_Qp]
  calc (Qcone c₀ Q₀').evalIn Fv x = (Qcone c₀ Q₀').evalIn Fv (Fin.cons (x 0) (Fin.cons (x 1) (tl x))) := by
        rw [e]
    _ = _ := by
        rw [Qcone, evalIn_splitForm, evalIn_splitForm, map_neg, hc]
        ring

/-- **The slicing of the cone form**: $Q(x) = c x_0^2 + Q_m(x_1, \dots)$. -/
theorem qv_cone_mid (x : Fin (k + 1 + 1) → Fv) :
    Qv v (NF.Qp v (Qcone c₀ Q₀')) x = cv v c₀ * x 0 ^ 2 + Qv v (NF.Qp v (Qmid c₀ Q₀')) (Fin.tail x) := by
  have hc : algebraMap (𝓞 F) Fv c₀ = cv v c₀ := IsScalarTower.algebraMap_apply (𝓞 F) F Fv c₀
  simp only [Qv, NF.evalIn_Qp]
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [Qcone, evalIn_splitForm, hc]
  ring

/-- The image of $c_0$ in $F_v$ through the integral model equals the image through $F$. -/
theorem cF_eq : ((NF.ι v c₀ : 𝔬) : Fv) = cv v c₀ :=
  (show ((NF.ι v c₀ : 𝔬) : Fv) = algebraMap (𝓞 F) Fv c₀ from rfl).trans
    (IsScalarTower.algebraMap_apply (𝓞 F) F Fv c₀)

theorem algebraMap_mid : algebraMap F Fv (mm (-c₀)) = -cv v c₀ := by
  simp [mm, cv]

/-- $|2c_0|_v$ as the norm of $2c$ in $F_v$. -/
theorem absTwoM_eq_norm : absTwoM v c₀ = ‖2 * cv v c₀‖ := by
  have : absTwoM v c₀ = ‖algebraMap F Fv (algebraMap (𝓞 F) F (2 * c₀))‖ := rfl
  rw [this]
  simp only [map_mul, map_ofNat, cv]

theorem absTwoM_neg : absTwoM v (-c₀) = absTwoM v c₀ := by
  simp only [absTwoM, mul_neg, map_neg, norm_neg]

end Bridge

/-! ### The parabolic section of the sphere $S_{c_0}$ -/

section Sec

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k)

/-- $Q_{m,0}$ is nondegenerate. -/
theorem nondeg_mid (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) : (Qmid c₀ Q₀').Nondegenerate :=
  hQ0 (-c₀) Q₀' (neg_ne_zero.2 hc) hQ'

/-- Membership in the sphere $\{Q_0 = c_0\}\subset F_v^{k+2}$ in terms of the value of $Q_0$. -/
theorem mem_sphC_iff (x : Fin (k + 1 + 1) → Fv) :
    x ∈ FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀) ↔
      Qv v (NF.Qp v (Qcone c₀ Q₀')) x = cv v c₀ := by
  simp only [FibreO.sphereSet, Set.mem_ofPred_eq, Qv, NF.evalIn_Qp]
  rw [evalIn_QF]

variable (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

include hc in
/-- **The graph point lies on the sphere** $S_{c_0}$ (for $q \ne 0$). -/
theorem graphV_mem {q : Fv} (hq : q ≠ 0) (y : Fin k → Fv) :
    graphV v (NF.Qp v Q₀') (cv v c₀) q y ∈ FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀) := by
  rw [mem_sphC_iff]
  have h := qv_line v (NF.Qp v Q₀') (cv_ne v c₀ hc) (qv_cone v c₀ Q₀') (Q := NF.Qp v (Qcone c₀ Q₀'))
    (graphB v (NF.Qp v Q₀') (cv v c₀) q y + q) hq y
  rw [← graphV_eq_v3] at h
  rw [sub_self, mul_zero] at h
  exact sub_eq_zero.mp h

include hc in
/-- **On the sphere the graph map recovers $x$** (when $x_0 \ne x_1$). -/
theorem graphV_of_mem {x : Fin (k + 1 + 1) → Fv} (hx : Qv v (NF.Qp v (Qcone c₀ Q₀')) x = cv v c₀)
    (hq : x 0 - x 1 ≠ 0) :
    graphV v (NF.Qp v Q₀') (cv v c₀) (x 0 - x 1) (tl x) = x := by
  have hline := qv_line v (NF.Qp v Q₀') (cv_ne v c₀ hc) (qv_cone v c₀ Q₀') (Q := NF.Qp v (Qcone c₀ Q₀'))
    (x 0) hq (tl x)
  have hv3 : v3 (x 0) (x 0 - (x 0 - x 1)) (tl x) = x := by rw [sub_sub_cancel]; exact v3_eta x
  rw [hv3, hx, sub_self] at hline
  have h2 : x 0 - (graphB v (NF.Qp v Q₀') (cv v c₀) (x 0 - x 1) (tl x) + (x 0 - x 1)) = 0 :=
    (mul_eq_zero.mp hline.symm).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero (cv_ne v c₀ hc)) hq)
  have hb : graphB v (NF.Qp v Q₀') (cv v c₀) (x 0 - x 1) (tl x) = x 1 := by linear_combination -h2
  rw [graphV, hb]
  conv_rhs => rw [← v3_eta x]
  exact v3_congr (by ring) rfl rfl

include hc in
/-- **The graph point is $d(q^{-1})\,n(y)\,e_0$.** -/
theorem dM_nM_e₀ {q : Fv} (hq : q ≠ 0) (y : Fin k → Fv) :
    dM q⁻¹ *ᵥ (nM (cv v c₀) (QFv v Q₀') y *ᵥ (e₀ : Fin (k + 1 + 1) → Fv)) =
      graphV v (NF.Qp v Q₀') (cv v c₀) q y := by
  have hc' := cv_ne v c₀ hc
  rw [nM_mulVec_e₀ _ _ hc', dM_mulVec_v3, graphV, graphB, inv_inv, eval_QFv]
  refine v3_congr ?_ ?_ rfl <;> field_simp <;> ring

/-- The orbit coordinate $\mathrm{orb}(x, 1)$ maps $e_0$ to $x$. -/
theorem mat_orbSO_mulVec {n : ℕ} (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₁ : QuadForm (𝓞 F) n) (hQ₁ : Q₁.Nondegenerate)
    (hn : 1 ≤ n) (x : FibreO.sphereSet v (QQ m₀ Q₁) (mm m₀)) :
    mat v (splitForm m₀ Q₁) (FibreSO.orbSO v m₀ hm Q₁ hQ₁ hn (x, 1)) *ᵥ (e₀ : Fin (n + 1) → Fv) =
      (x : Fin (n + 1) → Fv) := by
  have hosec : ((FibreSO.orbSO v m₀ hm Q₁ hQ₁ hn (x, 1)).1 : orthGroup (QQ m₀ Q₁) Fv) =
      FibreO.secOrth v (QQ m₀ Q₁) (mm m₀) (QQ' Q₁) (hEE m₀ Q₁) (mm_ne m₀ hm) (QQ'_nondeg Q₁ hQ₁) hn x := by
    simp [FibreSO.orbSO, FibreO.orb]
  have h1 := congrArg Subtype.val
    ((FibreO.orbitSection v (QQ m₀ Q₁) (mm m₀) (QQ' Q₁) (hEE m₀ Q₁) (mm_ne m₀ hm)
      (QQ'_nondeg Q₁ hQ₁) hn).sec_smul x)
  have h2 : mat v (splitForm m₀ Q₁) (FibreSO.orbSO v m₀ hm Q₁ hQ₁ hn (x, 1)) =
      ((FibreO.secOrth v (QQ m₀ Q₁) (mm m₀) (QQ' Q₁) (hEE m₀ Q₁) (mm_ne m₀ hm) (QQ'_nondeg Q₁ hQ₁) hn x :
        orthGroup (QQ m₀ Q₁) Fv) : GL (Fin (n + 1)) Fv).val :=
    congrArg (fun y : orthGroup (QQ m₀ Q₁) Fv => (y : GL (Fin (n + 1)) Fv).val) hosec
  rw [h2]
  exact h1

/-- The orbit coordinates factor: $\mathrm{orb}(x, h) = \mathrm{orb}(x, 1)\,\mathrm{diag}(1, h)$ in $SO$. -/
theorem orbSO_eq_mul {n : ℕ} (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₁ : QuadForm (𝓞 F) n) (hQ₁ : Q₁.Nondegenerate)
    (hn : 1 ≤ n) (x : FibreO.sphereSet v (QQ m₀ Q₁) (mm m₀)) (h : SOv v Q₁) :
    FibreSO.orbSO v m₀ hm Q₁ hQ₁ hn (x, h) = FibreSO.orbSO v m₀ hm Q₁ hQ₁ hn (x, 1) * iotaSO v m₀ Q₁ h := by
  apply Subtype.ext
  simp [FibreSO.orbSO, FibreO.orb, iotaSO_val]

open scoped Classical in
/-- **The parabolic section** of $SO(Q_0)(F_v)\to S_{c_0}$: $s(x) = d((x_0-x_1)^{-1})\,n(x')$ on $\{x_0 \ne x_1\}$
(the graph chart), and the reflection section $\mathrm{orb}(x, 1)$ on the $\sigma_{c_0}$-null set $\{x_0 = x_1\}$. -/
def secC (x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀)) : SOv v (Qcone c₀ Q₀') :=
  if h : (x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 ≠ 0 then
    dG v c₀ Q₀' (inv_ne_zero h) * nG v c₀ Q₀' hc hQ' (tl (x : Fin (k + 1 + 1) → Fv))
  else FibreSO.orbSO v c₀ hc (Qmid c₀ Q₀') (nondeg_mid c₀ Q₀' hc hQ') (Nat.succ_pos k) (x, 1)

theorem secC_of_ne {x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀)}
    (h : (x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 ≠ 0) :
    secC v c₀ Q₀' hc hQ' x = dG v c₀ Q₀' (inv_ne_zero h) * nG v c₀ Q₀' hc hQ' (tl (x : Fin (k + 1 + 1) → Fv)) :=
  dite_eq_left_of_eq_true (eq_true h)

theorem secC_of_eq {x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀)}
    (h : ¬ ((x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 ≠ 0)) :
    secC v c₀ Q₀' hc hQ' x =
      FibreSO.orbSO v c₀ hc (Qmid c₀ Q₀') (nondeg_mid c₀ Q₀' hc hQ') (Nat.succ_pos k) (x, 1) :=
  dite_eq_right_of_eq_false (eq_false h)

/-- **$s(x)\,e_0 = x$.** -/
theorem secC_spec (x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀)) :
    mat v (Qcone c₀ Q₀') (secC v c₀ Q₀' hc hQ' x) *ᵥ (e₀ : Fin (k + 1 + 1) → Fv) = (x : Fin (k + 1 + 1) → Fv) := by
  by_cases h : (x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 ≠ 0
  · rw [secC_of_ne v c₀ Q₀' hc hQ' h, mat_mul, mat_dG, mat_nG, ← mulVec_mulVec, dM_nM_e₀ v c₀ Q₀' hc h,
      graphV_of_mem v c₀ Q₀' hc ((mem_sphC_iff v c₀ Q₀' x).1 x.2) h]
  · rw [secC_of_eq v c₀ Q₀' hc hQ' h]
    exact mat_orbSO_mulVec v c₀ hc (Qmid c₀ Q₀') (nondeg_mid c₀ Q₀' hc hQ') (Nat.succ_pos k) x

/-- **$s$ is measurable.** -/
theorem measurable_secC : Measurable (secC v c₀ Q₀' hc hQ') := by
  classical
  set U : Set (FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀)) :=
    {x | (x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 ≠ 0} with hUdef
  have hcont : Continuous fun x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀) =>
      (x : Fin (k + 1 + 1) → Fv) 0 - (x : Fin (k + 1 + 1) → Fv) 1 :=
    ((continuous_apply 0).comp continuous_subtype_val).sub ((continuous_apply 1).comp continuous_subtype_val)
  have hU : MeasurableSet U := (isOpen_ne_fun hcont continuous_const).measurableSet
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  swap
  · have e : Uᶜ.domRestrict (secC v c₀ Q₀' hc hQ') = fun y : ↥Uᶜ =>
        FibreSO.orbSO v c₀ hc (Qmid c₀ Q₀') (nondeg_mid c₀ Q₀' hc hQ') (Nat.succ_pos k) ((y : _), 1) := by
      funext y
      exact secC_of_eq v c₀ Q₀' hc hQ' y.2
    rw [e]
    exact (FibreSO.measurable_orbSO v c₀ hc (Qmid c₀ Q₀') (nondeg_mid c₀ Q₀' hc hQ') (Nat.succ_pos k)).comp
      (measurable_subtype_coe.prodMk measurable_const)
  · have e : U.domRestrict (secC v c₀ Q₀' hc hQ') = fun y : ↥U =>
        dG v c₀ Q₀' (inv_ne_zero y.2) * nG v c₀ Q₀' hc hQ' (tl ((y : _) : Fin (k + 1 + 1) → Fv)) := by
      funext y
      exact secC_of_ne v c₀ Q₀' hc hQ' y.2
    rw [e]
    have hq : Continuous fun y : ↥U => ((y : _) : Fin (k + 1 + 1) → Fv) 0 - ((y : _) : Fin (k + 1 + 1) → Fv) 1 :=
      hcont.comp continuous_subtype_val
    have hqi : Continuous fun y : ↥U =>
        (⟨(((y : _) : Fin (k + 1 + 1) → Fv) 0 - ((y : _) : Fin (k + 1 + 1) → Fv) 1)⁻¹, inv_ne_zero y.2⟩ :
          {a : Fv // a ≠ 0}) :=
      (hq.inv₀ fun y => y.2).subtype_mk _
    have h1 := (continuous_dG v c₀ Q₀' hc hQ').comp hqi
    have h2 : Continuous fun y : ↥U => nG v c₀ Q₀' hc hQ' (tl (((y : _) : Fin (k + 1 + 1) → Fv))) :=
      (continuous_nG v c₀ Q₀' hc hQ').comp (continuous_tl.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact (h1.mul h2).measurable

end Sec

/-! ### Volume on $F_v^k$: orthogonal invariance and scaling -/

section Volume

variable {k : ℕ}

/-- **Scaling on $F_v^k$**: $\int\Psi(ty)\,dy = |t|_v^{-k}\int\Psi$. -/
theorem lintegral_smul_vecV (t : Fvˣ) {Ψ : (Fin k → Fv) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ y, Ψ ((t : Fv) • y) ∂volV (haarV v) k =
      ENNReal.ofReal ((‖(t : Fv)‖ ^ k)⁻¹) * ∫⁻ y, Ψ y ∂volV (haarV v) k := by
  have hmeas : Measurable fun y : Fin k → Fv => (t : Fv) • y := (continuous_const_smul _).measurable
  rw [← lintegral_map hΨ hmeas, map_smul_volV (haarV v) t, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [distribHaarChar_eq_norm v t]

/-- **Special orthogonal invariance of the volume on $F_v^k$**: $\int\Psi(hy)\,dy = \int\Psi$ for $h \in SO(Q_0')(F_v)$
($\det h = 1$, so $h$ has modulus $1$). -/
theorem lintegral_mulVec_so (Q₁ : QuadForm (𝓞 F) k) (h : SOv v Q₁) {Ψ : (Fin k → Fv) → ℝ≥0∞}
    (hΨ : Measurable Ψ) :
    ∫⁻ y, Ψ (mat v Q₁ h *ᵥ y) ∂volV (haarV v) k = ∫⁻ y, Ψ y ∂volV (haarV v) k := by
  set g : GL (Fin k) Fv := ((h.1 : orthGroup (Q₁.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin k) Fv) with hg
  have hdet : distribHaarChar Fv (GeneralLinearGroup.det g) = 1 := by
    have : GeneralLinearGroup.det g = 1 := Units.ext (det_mat v Q₁ h)
    rw [this, map_one]
  have hmeas : Measurable fun y : Fin k → Fv => (g : Matrix (Fin k) (Fin k) Fv) *ᵥ y :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hmap : Measure.map (fun y : Fin k → Fv => (g : Matrix (Fin k) (Fin k) Fv) *ᵥ y) (volV (haarV v) k) =
      volV (haarV v) k := by
    have h1 := map_mulVec_eq_glHaarChar_inv (volV (haarV v) k) g
    rw [glHaarChar_eq_of_field, hdet] at h1
    simpa using h1
  show ∫⁻ y, Ψ ((g : Matrix (Fin k) (Fin k) Fv) *ᵥ y) ∂volV (haarV v) k = _
  rw [← lintegral_map hΨ hmeas, hmap]

end Volume

/-! ### The parametric identity -/

section Param

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

include hc hQ' in
/-- $(d(q^{-1})\,n(y))^{-1} = d(q)\,n(-q^{-1}y)$. -/
theorem inv_dG_nG {q : Fv} (hq : q ≠ 0) (y : Fin k → Fv) :
    (dG v c₀ Q₀' (inv_ne_zero hq) * nG v c₀ Q₀' hc hQ' y)⁻¹ =
      dG v c₀ Q₀' hq * nG v c₀ Q₀' hc hQ' (-(q⁻¹ • y)) := by
  rw [_root_.mul_inv_rev, nG_neg, dG_inv, dG_mul_nG v c₀ Q₀' hc hQ' hq, smul_neg, smul_smul, mul_inv_cancel₀ hq,
    one_smul]
  congr 1
  exact mat_injective v _ (by rw [mat_dG, mat_dG, inv_inv])

/-- **Step 1** (sphere identity for $S_{c_0}$ with the parabolic section, inversion, hyperbolic-split chart). -/
theorem lintegral_cone_P1 {f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂muLocSO v (Qcone c₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v c₀ ^ (k + 1))⁻¹) *
        ∫⁻ q, ∫⁻ y, rhoS v (cv v c₀) q *
          ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀') h * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' (-(q⁻¹ • y)))
            ∂muLocSO v (Qmid c₀ Q₀') 1 ∂volV (haarV v) k ∂haarV v := by
  have hQm := nondeg_mid c₀ Q₀' hc hQ'
  have hQc := nondeg_cone c₀ Q₀' hc hQ'
  have hmid : (muLocSO v (Qmid c₀ Q₀') 1).IsHaarMeasure := isHaarMeasure_muLocSO v _ hQm
  rw [← lintegral_inv_muLocSO v (Qcone c₀ Q₀') hQc (by omega) hf,
    lintegral_orbital_section v c₀ hc (Qmid c₀ Q₀') hQm (Nat.succ_pos k) (secC v c₀ Q₀' hc hQ')
      (secC_spec v c₀ Q₀' hc hQ') (f := fun g => f g⁻¹) (hf.comp measurable_inv)]
  congr 1
  obtain ⟨Gf, hGf⟩ : ∃ G : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀) → ℝ≥0∞,
      G = fun x => ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀') h * (secC v c₀ Q₀' hc hQ' x)⁻¹)
        ∂muLocSO v (Qmid c₀ Q₀') 1 := ⟨_, rfl⟩
  have step3 : ∀ x : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀),
      ∫⁻ h, f ((secC v c₀ Q₀' hc hQ' x * iotaSO v c₀ (Qmid c₀ Q₀') h)⁻¹) ∂muLocSO v (Qmid c₀ Q₀') 1 = Gf x := by
    intro x
    have hF : Measurable fun h : SOv v (Qmid c₀ Q₀') =>
        f (iotaSO v c₀ (Qmid c₀ Q₀') h * (secC v c₀ Q₀' hc hQ' x)⁻¹) :=
      hf.comp ((continuous_iotaSO v c₀ _).measurable.mul_const _)
    rw [hGf]
    simp only
    rw [← lintegral_inv_muLocSO v (Qmid c₀ Q₀') hQm (Nat.succ_pos k) hF]
    refine lintegral_congr fun h => ?_
    rw [_root_.mul_inv_rev, map_inv]
  simp_rw [step3]
  have hGm : Measurable Gf := by
    rw [hGf]
    have : Measurable fun p : FibreO.sphereSet v (QQ c₀ (Qmid c₀ Q₀')) (mm c₀) × SOv v (Qmid c₀ Q₀') =>
        f (iotaSO v c₀ (Qmid c₀ Q₀') p.2 * (secC v c₀ Q₀' hc hQ' p.1)⁻¹) :=
      hf.comp (((continuous_iotaSO v c₀ _).measurable.comp measurable_snd).mul
        ((measurable_secC v c₀ Q₀' hc hQ').comp measurable_fst).inv)
    exact this.lintegral_prod_right'
  have hSmeas := FibreLeray.measurableSet_sphereSet v (Qcone c₀ Q₀') (mm c₀)
  have hemb := MeasurableEmbedding.subtype_coe hSmeas
  have hGEm : Measurable (Function.extend Subtype.val Gf 0) := hemb.measurable_extend hGm measurable_const
  have e1 : ∫⁻ x, Gf x ∂nuS v c₀ hc (Qmid c₀ Q₀') hQm =
      ∫⁻ z, Function.extend Subtype.val Gf 0 z ∂(nuS v c₀ hc (Qmid c₀ Q₀') hQm).map Subtype.val := by
    rw [lintegral_map hGEm measurable_subtype_coe]
    exact lintegral_congr fun x => (Subtype.val_injective.extend_apply Gf 0 x).symm
  rw [e1, FibreSO.map_val_nuS v c₀ hc (Qmid c₀ Q₀') hQm, cF_eq v c₀,
    lintegral_lerayMeasure_sphere v (NF.Qp v Q₀') (NF.nondegenerate_Qp v hQc) (NF.nondegenerate_Qp v hQ')
      (cv_ne v c₀ hc) (qv_cone v c₀ Q₀') hGEm]
  refine lintegral_congr fun q => lintegral_congr fun y => ?_
  by_cases hq : q = 0
  · simp [rhoS, hq]
  · congr 1
    have hmem := graphV_mem v c₀ Q₀' hc hq y
    have e : Function.extend Subtype.val Gf 0 (graphV v (NF.Qp v Q₀') (cv v c₀) q y) =
        Gf ⟨graphV v (NF.Qp v Q₀') (cv v c₀) q y, hmem⟩ :=
      Subtype.val_injective.extend_apply Gf 0 ⟨_, hmem⟩
    rw [e]
    have h0 : (graphV v (NF.Qp v Q₀') (cv v c₀) q y) 0 - (graphV v (NF.Qp v Q₀') (cv v c₀) q y) 1 ≠ 0 := by
      rw [graphV_sub]; exact hq
    have hsec : secC v c₀ Q₀' hc hQ' ⟨graphV v (NF.Qp v Q₀') (cv v c₀) q y, hmem⟩ =
        dG v c₀ Q₀' (inv_ne_zero hq) * nG v c₀ Q₀' hc hQ' y := by
      rw [secC_of_ne v c₀ Q₀' hc hQ' (x := ⟨graphV v (NF.Qp v Q₀') (cv v c₀) q y, hmem⟩) h0]
      congr 1
      · exact mat_injective v _ (by rw [mat_dG, mat_dG]; simp only [graphV_sub])
    rw [hGf]
    simp only
    simp only [hsec, inv_dG_nG v c₀ Q₀' hc hQ' hq, dGt_of_ne v c₀ Q₀' hq, mul_assoc]

/-- **Step 2** (sphere identity for $SO(\langle -c_0\rangle\perp Q_0')$ on $S'_{-c_0}$, and the commutation rules of
the parabolic subgroup). -/
theorem lintegral_cone_P2 (hk : 1 ≤ k) {f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞} (hf : Measurable f) (q : Fv)
    (w₀ : Fin k → Fv) :
    ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀') h * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' w₀)
        ∂muLocSO v (Qmid c₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) *
        ∫⁻ y, ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀')
            (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) * dGt v c₀ Q₀' q *
            nG v c₀ Q₀' hc hQ' (mat v Q₀' h *ᵥ w₀) * mG v c₀ Q₀' h) ∂muLocSO v Q₀' 1
          ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' := by
  have hF : Measurable fun h : SOv v (Qmid c₀ Q₀') =>
      f (iotaSO v c₀ (Qmid c₀ Q₀') h * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' w₀) :=
    hf.comp (((continuous_iotaSO v c₀ _).measurable.mul_const _).mul_const _)
  rw [lintegral_orbital_section v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk
    (fun y => FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1))
    (fun y => mat_orbSO_mulVec v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk y) hF, absTwoM_neg]
  congr 1
  refine lintegral_congr fun y => lintegral_congr fun h => ?_
  congr 1
  rw [map_mul, ← mG_eq]
  set s := iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1))
  calc s * mG v c₀ Q₀' h * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' w₀
      = s * (mG v c₀ Q₀' h * dGt v c₀ Q₀' q) * nG v c₀ Q₀' hc hQ' w₀ := by simp only [mul_assoc]
    _ = s * (dGt v c₀ Q₀' q * mG v c₀ Q₀' h) * nG v c₀ Q₀' hc hQ' w₀ := by rw [mG_mul_dGt]
    _ = s * dGt v c₀ Q₀' q * (mG v c₀ Q₀' h * nG v c₀ Q₀' hc hQ' w₀) := by simp only [mul_assoc]
    _ = s * dGt v c₀ Q₀' q * (nG v c₀ Q₀' hc hQ' (mat v Q₀' h *ᵥ w₀) * mG v c₀ Q₀' h) := by
        rw [mG_mul_nG]
    _ = s * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' (mat v Q₀' h *ᵥ w₀) * mG v c₀ Q₀' h := by
        simp only [mul_assoc]

/-- **Step 3** (the substitution $w = h\,(-q^{-1}y)$ on $F_v^k$: $\det h = 1$ and scaling by $-q^{-1}$ has Jacobian
$|q|_v^k$). -/
theorem lintegral_cone_P3 {q : Fv} (hq : q ≠ 0)
    {Φ : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) × SOv v Q₀' × (Fin k → Fv) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ y, ∫⁻ x, ∫⁻ h, Φ (x, h, mat v Q₀' h *ᵥ (-(q⁻¹ • y))) ∂muLocSO v Q₀' 1
        ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' ∂volV (haarV v) k =
      ENNReal.ofReal (‖q‖ ^ k) * ∫⁻ x, ∫⁻ h, ∫⁻ w, Φ (x, h, w) ∂volV (haarV v) k ∂muLocSO v Q₀' 1
        ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' := by
  have := isHaarMeasure_muLocSO v Q₀' hQ'
  have hM : Continuous fun h : SOv v Q₀' => mat v Q₀' h := continuous_mat v
  have hm3 : Measurable fun p : ((Fin k → Fv) × FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀))) × SOv v Q₀' =>
      Φ (p.1.2, p.2, mat v Q₀' p.2 *ᵥ (-(q⁻¹ • p.1.1))) := by
    refine hΦ.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk ?_))
    exact ((hM.comp continuous_snd).matrix_mulVec
      ((continuous_const_smul _).comp (continuous_fst.comp continuous_fst)).neg).measurable
  rw [lintegral_lintegral_swap hm3.lintegral_prod_right'.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  have hm2 : Measurable fun p : (Fin k → Fv) × SOv v Q₀' =>
      Φ (x, p.2, mat v Q₀' p.2 *ᵥ (-(q⁻¹ • p.1))) :=
    hm3.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun h => ?_
  have e : ∀ y : Fin k → Fv, mat v Q₀' h *ᵥ (-(q⁻¹ • y)) = (-q⁻¹) • (mat v Q₀' h *ᵥ y) := by
    intro y; rw [mulVec_neg, mulVec_smul, neg_smul]
  simp_rw [e]
  have hΨ : Measurable fun z : Fin k → Fv => Φ (x, h, (-q⁻¹) • z) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk (continuous_const_smul _).measurable))
  rw [lintegral_mulVec_so v Q₀' h (Ψ := fun z => Φ (x, h, (-q⁻¹) • z)) hΨ]
  have hu : (-q⁻¹ : Fv) ≠ 0 := neg_ne_zero.2 (inv_ne_zero hq)
  have := lintegral_smul_vecV v (Units.mk0 (-q⁻¹) hu) (Ψ := fun w => Φ (x, h, w))
    (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  simp only [Units.val_mk0] at this
  rw [this, norm_neg, norm_inv, inv_pow, inv_inv]

/-- **The parametric cone identity at a finite place** (every $v$, dyadic included; $c_0 \ne 0$, $Q_0'$ nondegenerate in
$k \ge 1$ variables; $s'(y) = \mathrm{orb}(y, 1)$ the reflection section):
$$\int f\,d\mu_{SO(Q_0)} = |2c_0|_v^{-(k+1)}|2c_0|_v^{-k}\int_{F_v}\frac{|q|_v^k}{|2c_0q|_v}\int_{S'_{-c_0}}\int_{SO(Q_0')}
  \int_{F_v^k}f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,dw\,d\mu_{SO(Q_0')}(h)\,d\sigma'_{-c_0}(y)\,dq.$$
So $SO(Q_0)(F_v)$ is, up to a null set, $\iota(SO(\langle -c_0\rangle\perp Q_0'))\cdot A\cdot N\cdot SO(Q_0')$. -/
@[kb "weil1982" "§2.4 (Lemma 2.4.1 / Theorem 2.4.3 for the cone orbit, parametric form at a finite place) [unverified]"]
theorem lintegral_cone_param (hk : 1 ≤ k) {f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂muLocSO v (Qcone c₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v c₀ ^ (k + 1))⁻¹) * ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) *
        ∫⁻ q, rhoS v (cv v c₀) q * ENNReal.ofReal (‖q‖ ^ k) *
          ∫⁻ y, ∫⁻ h, ∫⁻ w, f (iotaSO v c₀ (Qmid c₀ Q₀')
              (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) * dGt v c₀ Q₀' q *
              nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h) ∂volV (haarV v) k ∂muLocSO v Q₀' 1
            ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' ∂haarV v := by
  have hmuH := isHaarMeasure_muLocSO v Q₀' hQ'
  rw [lintegral_cone_P1 v c₀ Q₀' hc hQ' hf, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  by_cases hq : q = 0
  · simp [rhoS, hq]
  set Φ : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) × SOv v Q₀' × (Fin k → Fv) → ℝ≥0∞ :=
    fun p => f (iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (p.1, 1)) *
      dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' p.2.2 * mG v c₀ Q₀' p.2.1) with hΦdef
  have hΦ : Measurable Φ := by
    have hA : Measurable fun p : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) × SOv v Q₀' × (Fin k → Fv) =>
        iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (p.1, 1)) :=
      (continuous_iotaSO v c₀ _).measurable.comp
        ((FibreSO.measurable_orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk).comp
          (measurable_fst.prodMk measurable_const))
    have hB : Measurable fun p : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) × SOv v Q₀' × (Fin k → Fv) =>
        nG v c₀ Q₀' hc hQ' p.2.2 :=
      (continuous_nG v c₀ Q₀' hc hQ').measurable.comp (measurable_snd.comp measurable_snd)
    have hC : Measurable fun p : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) × SOv v Q₀' × (Fin k → Fv) =>
        mG v c₀ Q₀' p.2.1 :=
      (continuous_mG v c₀ Q₀').measurable.comp (measurable_fst.comp measurable_snd)
    exact hf.comp (((hA.mul_const _).mul hB).mul hC)
  calc ∫⁻ y, rhoS v (cv v c₀) q *
        ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀') h * dGt v c₀ Q₀' q * nG v c₀ Q₀' hc hQ' (-(q⁻¹ • y)))
          ∂muLocSO v (Qmid c₀ Q₀') 1 ∂volV (haarV v) k
      = rhoS v (cv v c₀) q * ∫⁻ y, ∫⁻ h, f (iotaSO v c₀ (Qmid c₀ Q₀') h * dGt v c₀ Q₀' q *
          nG v c₀ Q₀' hc hQ' (-(q⁻¹ • y))) ∂muLocSO v (Qmid c₀ Q₀') 1 ∂volV (haarV v) k :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = rhoS v (cv v c₀) q * ∫⁻ y, ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) *
          ∫⁻ x, ∫⁻ h, Φ (x, h, mat v Q₀' h *ᵥ (-(q⁻¹ • y))) ∂muLocSO v Q₀' 1
            ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' ∂volV (haarV v) k := by
        congr 1
        refine lintegral_congr fun y => ?_
        exact lintegral_cone_P2 v c₀ Q₀' hc hQ' hk hf q _
    _ = rhoS v (cv v c₀) q * (ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) *
          ∫⁻ y, ∫⁻ x, ∫⁻ h, Φ (x, h, mat v Q₀' h *ᵥ (-(q⁻¹ • y))) ∂muLocSO v Q₀' 1
            ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' ∂volV (haarV v) k) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = rhoS v (cv v c₀) q * (ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) * (ENNReal.ofReal (‖q‖ ^ k) *
          ∫⁻ x, ∫⁻ h, ∫⁻ w, Φ (x, h, w) ∂volV (haarV v) k ∂muLocSO v Q₀' 1
            ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ')) := by
        rw [lintegral_cone_P3 v c₀ Q₀' hc hQ' hq hΦ]
    _ = _ := by ring

end Param

/-! ### The punctured cone and the action of $SO(V)(F_v)$ -/

section ConeType

variable {N : ℕ} (Q₀ : QuadForm (𝓞 F) N)

/-- **The punctured cone** $C^\circ_v = \{z \in F_v^N : Q_0(z) = 0,\ z \ne 0\}$ (the values of $Q_0$ are taken on
$Q_0\otimes\mathfrak o_v$). -/
def coneSetV : Set (Fin N → Fv) := {z | Qv v (NF.Qp v Q₀) z = 0 ∧ z ≠ 0}

/-- $C^\circ_v$ as a type (Borel structure). -/
abbrev ConeTV : Type := ↥(coneSetV v Q₀)

theorem measurableSet_coneSetV : MeasurableSet (coneSetV v Q₀) :=
  ((isClosed_singleton.preimage (continuous_qv v _)).measurableSet).inter (measurableSet_singleton 0).compl

/-- Elements of $O(V)(F_v)$, in particular of $SO(V)(F_v)$, preserve the values of $Q_0$. -/
theorem qv_mat_mulVec (g : SOv v Q₀) (z : Fin N → Fv) :
    Qv v (NF.Qp v Q₀) (mat v Q₀ g *ᵥ z) = Qv v (NF.Qp v Q₀) z := by
  simp only [Qv, NF.evalIn_Qp]
  exact evalIn_orthGroup v Q₀ g.1 z

theorem mat_mulVec_ne_zero (g : SOv v Q₀) {z : Fin N → Fv} (hz : z ≠ 0) : mat v Q₀ g *ᵥ z ≠ 0 := by
  intro h
  apply hz
  have : mat v Q₀ g⁻¹ *ᵥ (mat v Q₀ g *ᵥ z) = z := by
    rw [mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, one_mulVec]
  rw [← this, h, mulVec_zero]

/-- **The action of $SO(V)(F_v)$ on the punctured cone**, through the matrices. -/
instance : MulAction (SOv v Q₀) (ConeTV v Q₀) where
  smul g z := ⟨mat v Q₀ g *ᵥ (z : Fin N → Fv), by rw [qv_mat_mulVec]; exact z.2.1,
    mat_mulVec_ne_zero v Q₀ g z.2.2⟩
  one_smul z := Subtype.ext (by
    show mat v Q₀ 1 *ᵥ (z : Fin N → Fv) = z
    rw [mat_one, one_mulVec])
  mul_smul g h z := Subtype.ext (by
    show mat v Q₀ (g * h) *ᵥ (z : Fin N → Fv) = mat v Q₀ g *ᵥ (mat v Q₀ h *ᵥ (z : Fin N → Fv))
    rw [mat_mul, mulVec_mulVec])

theorem coe_smul_coneV (g : SOv v Q₀) (z : ConeTV v Q₀) :
    ((g • z : ConeTV v Q₀) : Fin N → Fv) = mat v Q₀ g *ᵥ (z : Fin N → Fv) := rfl

theorem continuous_smul_coneV : Continuous fun p : SOv v Q₀ × ConeTV v Q₀ => p.1 • p.2 :=
  (((continuous_mat v).comp continuous_fst).matrix_mulVec (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem measurable_smul_coneV (g : SOv v Q₀) : Measurable fun z : ConeTV v Q₀ => g • z :=
  ((continuous_smul_coneV v Q₀).comp (continuous_const.prodMk continuous_id)).measurable

/-- **The Leray measure of the punctured cone** $\sigma_C$: the Leray measure $\sigma_0$ of the cone (a measure on
$F_v^N\smallsetminus\{0\}$ carried by $\{Q_0 = 0\}$), restricted to $C^\circ_v$. -/
def sigConeV (hQ : Q₀.Nondegenerate) : Measure (ConeTV v Q₀) :=
  (lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) 0).comap Subtype.val

/-- **Integrals over `sigConeV`** are integrals over the ambient Leray measure of the extension by zero (the ambient
measure is carried by the punctured cone). -/
theorem lintegral_sigConeV (hQ : Q₀.Nondegenerate) {G : ConeTV v Q₀ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂sigConeV v Q₀ hQ =
      ∫⁻ x, Function.extend Subtype.val G 0 x
        ∂lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) 0 := by
  set μ := lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) 0 with hμ
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_coneSetV v Q₀)
  have hae : ∀ᵐ x ∂μ, x ∈ coneSetV v Q₀ := by
    rw [ae_iff]
    refine measure_mono_null (t := {x | Qv v (NF.Qp v Q₀) x ≠ 0} ∪ {0}) ?_ ?_
    · intro x hx
      by_cases h : Qv v (NF.Qp v Q₀) x = 0
      · right
        simp only [Set.mem_ofPred_eq, coneSetV, not_and, not_not] at hx
        exact hx h
      · left; exact h
    · exact measure_union_null (lerayMeasure_compl_level v (haarV v) (NF.Qp v Q₀)
        (NF.nondegenerate_Qp v hQ) 0) (lerayMeasure_singleton_zero v _ _ _ 0)
  have hmap : (μ.comap (Subtype.val : ConeTV v Q₀ → Fin N → Fv)).map (Subtype.val : ConeTV v Q₀ → Fin N → Fv) = μ := by
    rw [hemb.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  have hext : Measurable (Function.extend Subtype.val G 0) := hemb.measurable_extend hG measurable_const
  calc ∫⁻ z, G z ∂sigConeV v Q₀ hQ
      = ∫⁻ z, Function.extend Subtype.val G 0 (z : Fin N → Fv) ∂μ.comap (Subtype.val : ConeTV v Q₀ → Fin N → Fv) :=
        lintegral_congr fun z => (Subtype.val_injective.extend_apply G 0 z).symm
    _ = ∫⁻ x, Function.extend Subtype.val G 0 x ∂(μ.comap (Subtype.val : ConeTV v Q₀ → Fin N → Fv)).map (Subtype.val : ConeTV v Q₀ → Fin N → Fv) :=
        (lintegral_map hext measurable_subtype_coe).symm
    _ = _ := by rw [hmap]

/-- **$\sigma_C$ is $SO(V)(F_v)$-invariant**: the ambient Leray measure is invariant under the orthogonal group
and the action preserves the cone. -/
@[kb "weil1982" "§2.2 (invariance of the Leray measure dx/dQ on the cone) [unverified]"]
theorem smulInvariantMeasure_sigConeV (hQ : Q₀.Nondegenerate) :
    SMulInvariantMeasure (SOv v Q₀) (ConeTV v Q₀) (sigConeV v Q₀ hQ) := by
  refine ⟨fun g t ht => ?_⟩
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_coneSetV v Q₀)
  unfold sigConeV
  rw [hemb.comap_apply, hemb.comap_apply]
  have hset : Subtype.val '' ((fun z => g • z) ⁻¹' t) =
      (fun x : Fin N → Fv => mat v Q₀ g *ᵥ x) ⁻¹' (Subtype.val '' t) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : (y : Fin N → Fv) = mat v Q₀ g *ᵥ x := hyx
      have hx : x ∈ coneSetV v Q₀ := by
        have : x = mat v Q₀ g⁻¹ *ᵥ (y : Fin N → Fv) := by
          rw [hyx', mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, one_mulVec]
        rw [this]
        exact (g⁻¹ • y : ConeTV v Q₀).2
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have : g • (⟨x, hx⟩ : ConeTV v Q₀) = y := Subtype.ext hyx.symm
      show g • (⟨x, hx⟩ : ConeTV v Q₀) ∈ t
      rw [this]; exact hy
  have hmeas : Measurable fun x : Fin N → Fv => mat v Q₀ g *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hset, ← Measure.map_apply hmeas (hemb.measurableSet_image.2 ht)]
  have h := FibreLeray.sig_map_orth v Q₀ hQ 0 g.1
  exact congrArg (fun m => m (Subtype.val '' t)) h

/-- **Scaling of the punctured cone** by $a \in F_v^\times$. -/
def smulCone (a : Fvˣ) (z : ConeTV v Q₀) : ConeTV v Q₀ :=
  ⟨(a : Fv) • (z : Fin N → Fv), by
    refine ⟨?_, ?_⟩
    · rw [qv_smul, z.2.1, mul_zero]
    · intro h
      exact z.2.2 (by simpa [smul_eq_zero, a.ne_zero] using h)⟩

theorem measurable_smulCone (a : Fvˣ) : Measurable (smulCone v Q₀ a) :=
  ((continuous_const_smul (a : Fv)).comp continuous_subtype_val).measurable.subtype_mk

/-- **Homogeneity of $\sigma_C$**: $(z \mapsto az)_*\sigma_C = |a|_v^{2-N}\sigma_C$, i.e. $|a|_v^{-k}\sigma_C$ for
$N = k+2$ (the scaling law of the Leray measures at $\rho = 0$). -/
@[kb "weil1982" "§2.2 (homogeneity of degree n-2 of the Leray measure on the cone) [unverified]"]
theorem map_smul_sigConeV (hQ : Q₀.Nondegenerate) (a : Fvˣ) :
    (sigConeV v Q₀ hQ).map (smulCone v Q₀ a) =
      ((distribHaarChar Fv a : ℝ≥0∞) ^ 2 / (distribHaarChar Fv a : ℝ≥0∞) ^ N) • sigConeV v Q₀ hQ := by
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_coneSetV v Q₀)
  have hmeasA : Measurable fun x : Fin N → Fv => (a : Fv) • x := (continuous_const_smul (a : Fv)).measurable
  have h := lerayMeasure_map_smul_units v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) a 0
  rw [mul_zero] at h
  ext t ht
  rw [Measure.map_apply (measurable_smulCone v Q₀ a) ht, Measure.smul_apply, smul_eq_mul]
  unfold sigConeV
  rw [hemb.comap_apply, hemb.comap_apply]
  have hset : Subtype.val '' (smulCone v Q₀ a ⁻¹' t) = (fun x : Fin N → Fv => (a : Fv) • x) ⁻¹' (Subtype.val '' t) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨smulCone v Q₀ a y, hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : (y : Fin N → Fv) = (a : Fv) • x := hyx
      have hx : x ∈ coneSetV v Q₀ := by
        have : x = ((a⁻¹ : Fvˣ) : Fv) • (y : Fin N → Fv) := by
          rw [hyx', smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ a.ne_zero, one_smul]
        rw [this]
        exact (smulCone v Q₀ a⁻¹ y).2
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have : smulCone v Q₀ a ⟨x, hx⟩ = y := Subtype.ext hyx.symm
      show smulCone v Q₀ a ⟨x, hx⟩ ∈ t
      rw [this]; exact hy
  rw [hset, ← Measure.map_apply hmeasA (hemb.measurableSet_image.2 ht), h, Measure.smul_apply, smul_eq_mul]

end ConeType

/-! ### An explicit section of $SO(V)(F_v)\to C^\circ_v$ -/

section ConeOrbit

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 1 ≤ k)

/-- The cone form vanishes at $0$. -/
theorem qv_zero_vec {n : ℕ} (Q : QuadForm 𝔬 n) : Qv v Q (0 : Fin n → Fv) = 0 := by
  have := qv_smul v Q 0 (0 : Fin n → Fv)
  simpa using this

omit hc hQ' hk in
/-- The isotropic vector $e = e_0 + e_1$ lies on the cone. -/
theorem eV_mem : (eV : Fin (k + 1 + 1) → Fv) ∈ coneSetV v (Qcone c₀ Q₀') := by
  refine ⟨?_, fun h => ?_⟩
  · rw [qv_cone v c₀ Q₀' eV, eV, v3_zero', v3_one', tl_v3, qv_zero_vec]; ring
  · have := congrFun h 0
    rw [eV, v3_zero'] at this
    exact one_ne_zero this

omit hc hQ' hk in
/-- The base point $e \in C^\circ_v$. -/
def eConeV : ConeTV v (Qcone c₀ Q₀') := ⟨eV, eV_mem v c₀ Q₀'⟩

omit hc hQ' hk in
/-- Membership in the sphere $\{Q_{m,0} = -c_0\}$ in terms of the value of $Q_{m,0}$. -/
theorem mem_sphM_iff (y : Fin (k + 1) → Fv) :
    y ∈ FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) ↔ Qv v (NF.Qp v (Qmid c₀ Q₀')) y = -cv v c₀ := by
  simp only [FibreO.sphereSet, Set.mem_ofPred_eq, Qv, NF.evalIn_Qp]
  rw [evalIn_QF, algebraMap_mid v c₀]

omit hc hQ' hk in
theorem yOf_mem {z : Fin (k + 1 + 1) → Fv} (hz : z ∈ coneSetV v (Qcone c₀ Q₀')) (h0 : z 0 ≠ 0) :
    (fun i : Fin (k + 1) => z i.succ / z 0) ∈ FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) := by
  rw [mem_sphM_iff]
  have hz1 := hz.1
  rw [qv_cone_mid v c₀ Q₀' z] at hz1
  have e : (fun i : Fin (k + 1) => z i.succ / z 0) = (z 0)⁻¹ • Fin.tail z := by
    ext i; simp [Fin.tail, div_eq_inv_mul]
  rw [e, qv_smul]
  have h2 : Qv v (NF.Qp v (Qmid c₀ Q₀')) (Fin.tail z) = -cv v c₀ * z 0 ^ 2 := by linear_combination hz1
  rw [h2]; field_simp

/-- The point $y = z'/z_0 \in S'_{-c_0}$ of $z \in C^\circ_v$ with $z_0 \ne 0$ ($z = z_0(1, y)$). -/
def yOfV {z : ConeTV v (Qcone c₀ Q₀')} (h0 : (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0) :
    FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)) :=
  ⟨fun i => (z : Fin (k + 1 + 1) → Fv) i.succ / (z : Fin (k + 1 + 1) → Fv) 0, yOf_mem v c₀ Q₀' z.2 h0⟩

omit hc hQ' hk in
theorem coneVecV_yOf {z : ConeTV v (Qcone c₀ Q₀')} (h0 : (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0) :
    coneVecV v ((z : Fin (k + 1 + 1) → Fv) 0) ((yOfV v c₀ Q₀' h0 : _) : Fin (k + 1) → Fv) = z := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [coneVecV_zero]
  · simp only [coneVecV, yOfV, Pi.smul_apply, Fin.cons_succ, smul_eq_mul]
    field_simp

omit hc hQ' hk in
/-- $q(1, y)$ lies on the cone for $y \in S'_{-c_0}$, $q \ne 0$. -/
theorem coneVecV_mem {q : Fv} (hq : q ≠ 0) {y : Fin (k + 1) → Fv}
    (hy : y ∈ FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀))) :
    coneVecV v q y ∈ coneSetV v (Qcone c₀ Q₀') := by
  refine ⟨?_, fun h => hq ?_⟩
  · rw [qv_cone_mid v c₀ Q₀' _, coneVecV_zero, tail_coneVecV, qv_smul, (mem_sphM_iff v c₀ Q₀' y).1 hy]
    ring
  · have := congrFun h 0
    rwa [coneVecV_zero] at this

include hc hQ' hk in
/-- $\iota(s'(y))\,e = (1, y)$. -/
theorem mat_iotaSO_orb_eV (y : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀))) :
    mat v (Qcone c₀ Q₀') (iotaSO v c₀ (Qmid c₀ Q₀')
        (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1))) *ᵥ (eV : Fin (k + 1 + 1) → Fv) =
      Fin.cons 1 (y : Fin (k + 1) → Fv) := by
  rw [mat_iotaSO, eV, v3, cornerMat_mulVec, one_mul]
  congr 1
  exact mat_orbSO_mulVec v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk y

open scoped Classical in
/-- **The section on $\{z_0 \ne 0\}$**: $s_0(z) = \iota(s'(z'/z_0))\,d(z_0)$, $s'(y) = \mathrm{orb}(y, 1)$. -/
def coneSec₀ (z : ConeTV v (Qcone c₀ Q₀')) : SOv v (Qcone c₀ Q₀') :=
  if h : (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0 then
    iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (yOfV v c₀ Q₀' h, 1)) *
      dG v c₀ Q₀' h
  else 1

theorem coneSec₀_of_ne {z : ConeTV v (Qcone c₀ Q₀')} (h : (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0) :
    coneSec₀ v c₀ Q₀' hc hQ' hk z =
      iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (yOfV v c₀ Q₀' h, 1)) *
        dG v c₀ Q₀' h :=
  dite_eq_left_of_eq_true (eq_true h)

theorem coneSec₀_of_eq {z : ConeTV v (Qcone c₀ Q₀')} (h : ¬ ((z : Fin (k + 1 + 1) → Fv) 0 ≠ 0)) :
    coneSec₀ v c₀ Q₀' hc hQ' hk z = 1 :=
  dite_eq_right_of_eq_false (eq_false h)

theorem coneSec₀_smul {z : ConeTV v (Qcone c₀ Q₀')} (h0 : (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0) :
    coneSec₀ v c₀ Q₀' hc hQ' hk z • eConeV v c₀ Q₀' = z := by
  apply Subtype.ext
  rw [coe_smul_coneV, coneSec₀_of_ne v c₀ Q₀' hc hQ' hk h0, mat_mul, mat_dG, ← mulVec_mulVec]
  show _ *ᵥ (dM _ *ᵥ (eV : Fin (k + 1 + 1) → Fv)) = _
  rw [dM_mulVec_eV h0, mulVec_smul, mat_iotaSO_orb_eV v c₀ Q₀' hc hQ' hk]
  conv_rhs => rw [← coneVecV_yOf v c₀ Q₀' h0]
  rfl

theorem measurable_coneSec₀ : Measurable (coneSec₀ v c₀ Q₀' hc hQ' hk) := by
  classical
  set U : Set (ConeTV v (Qcone c₀ Q₀')) := {z | (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0} with hUdef
  have hz0 : Continuous fun z : ConeTV v (Qcone c₀ Q₀') => (z : Fin (k + 1 + 1) → Fv) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have hU : MeasurableSet U := (isOpen_ne_fun hz0 continuous_const).measurableSet
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  · have e : U.domRestrict (coneSec₀ v c₀ Q₀' hc hQ' hk) = fun z : ↥U =>
        iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk
            (yOfV v c₀ Q₀' (z := z.1) z.2, 1)) *
          dG v c₀ Q₀' (show (z.1 : Fin (k + 1 + 1) → Fv) 0 ≠ 0 from z.2) := by
      funext z
      exact coneSec₀_of_ne v c₀ Q₀' hc hQ' hk z.2
    rw [e]
    have hz0' : Continuous fun z : ↥U => ((z : ConeTV v (Qcone c₀ Q₀')) : Fin (k + 1 + 1) → Fv) 0 :=
      hz0.comp continuous_subtype_val
    have hy : Continuous fun z : ↥U => (yOfV v c₀ Q₀' (z := z.1) z.2 :
        FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀))) := by
      refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
      exact ((continuous_apply i.succ).comp (continuous_subtype_val.comp continuous_subtype_val)).div hz0'
        (fun z => z.2)
    have h1 : Measurable fun z : ↥U => iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk
        (yOfV v c₀ Q₀' (z := z.1) z.2, 1)) :=
      (continuous_iotaSO v c₀ _).measurable.comp
        ((FibreSO.measurable_orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk).comp
          (hy.measurable.prodMk measurable_const))
    have hf : Continuous fun z : ↥U => (⟨((z : ConeTV v (Qcone c₀ Q₀')) : Fin (k + 1 + 1) → Fv) 0, z.2⟩ :
        {a : Fv // a ≠ 0}) := hz0'.subtype_mk _
    have h2 := ((continuous_dG v c₀ Q₀' hc hQ').comp hf).measurable
    simp only [Function.comp_def] at h2
    exact h1.mul h2
  · have e : Uᶜ.domRestrict (coneSec₀ v c₀ Q₀' hc hQ' hk) = fun _ => 1 := by
      funext z
      exact coneSec₀_of_eq v c₀ Q₀' hc hQ' hk z.2
    rw [e]; exact measurable_const

/-- The finite list $1,\ d(2),\ n(\varepsilon_1), \dots, n(\varepsilon_k)$: every $z \in C^\circ_v$ is moved into
$\{z_0 \ne 0\}$ by one of them. -/
def coneList : List (SOv v (Qcone c₀ Q₀')) :=
  1 :: dG v c₀ Q₀' (two_ne_zero : (2 : Fv) ≠ 0) ::
    List.ofFn (fun j : Fin k => nG v c₀ Q₀' hc hQ' (Pi.single j 1))

include hc hQ' in
theorem cone_cover (z : ConeTV v (Qcone c₀ Q₀')) :
    ∃ g ∈ coneList v c₀ Q₀' hc hQ', ((g • z : ConeTV v (Qcone c₀ Q₀')) : Fin (k + 1 + 1) → Fv) 0 ≠ 0 := by
  obtain ⟨x, hx⟩ := z
  by_cases h0 : x 0 ≠ 0
  · exact ⟨1, List.mem_cons_self .., by rw [one_smul]; exact h0⟩
  push Not at h0
  by_cases h1 : x 1 ≠ 0
  · refine ⟨dG v c₀ Q₀' (two_ne_zero : (2 : Fv) ≠ 0), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [coe_smul_coneV, mat_dG]
    show (dM 2 *ᵥ x) 0 ≠ 0
    rw [← v3_eta x, dM_mulVec_v3, v3_zero', h0]
    intro h; apply h1; linear_combination (4 / 3 : Fv) * h
  push Not at h1
  have hy : tl x ≠ 0 := by
    intro hy; apply hx.2
    rw [← v3_eta x, h0, h1, hy]
    ext i; refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i
  have hdet : (QFv v Q₀').hessian.det ≠ 0 := by
    rw [← hessV_base]
    exact FibreO.det_hessV_ne_zero v _ (nondegenerate_QF Q₀' hQ')
  have hHy : (QFv v Q₀').hessian *ᵥ tl x ≠ 0 := fun h => hy (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hHy
  refine ⟨nG v c₀ Q₀' hc hQ' (Pi.single j 1), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_ofFn.mpr ⟨j, rfl⟩)), ?_⟩
  rw [coe_smul_coneV, mat_nG]
  show (nM (cv v c₀) (QFv v Q₀') (Pi.single j 1) *ᵥ x) 0 ≠ 0
  rw [← v3_eta x, nM_mulVec_v3, v3_zero', h0, h1, hess_dot_comm, dotProduct_single, mul_one]
  simp only [sub_zero, zero_mul, add_zero, zero_sub, neg_ne_zero]
  exact div_ne_zero hj (mul_ne_zero two_ne_zero (cv_ne v c₀ hc))

/-- **An explicit measurable section** of $g \mapsto ge$, $SO(V)(F_v)\to C^\circ_v$, as the `OrbitSection`:
$s(z) = \iota(s'(z'/z_0))\,d(z_0)$ when $z_0 \ne 0$, else $g^{-1}s(gz)$ for the first $g \in \{d(2), n(\varepsilon_j)\}$
with $(gz)_0 \ne 0$. (In particular $SO(V)(F_v)$ is transitive on $C^\circ_v$.) -/
def coneOrbitSectionV : Weil.OrbitSection (SOv v (Qcone c₀ Q₀')) (ConeTV v (Qcone c₀ Q₀')) where
  base := eConeV v c₀ Q₀'
  sec := ConeReal.extSec {z | (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0} (coneSec₀ v c₀ Q₀' hc hQ' hk)
    (coneList v c₀ Q₀' hc hQ')
  sec_smul z := ConeReal.extSec_smul (fun _ hz => coneSec₀_smul v c₀ Q₀' hc hQ' hk hz) _
    (cone_cover v c₀ Q₀' hc hQ' z)
  measurable_sec := ConeReal.measurable_extSec
    (isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val) continuous_const).measurableSet
    (measurable_coneSec₀ v c₀ Q₀' hc hQ' hk) (measurable_smul_coneV v _) _
  measurable_orbit := ((continuous_smul_coneV v _).comp (continuous_id.prodMk continuous_const)).measurable

/-- On a cone point $q(1, y)$ with $q \ne 0$ the section is $\iota(s'(y))\,d(q)$. -/
theorem sec_coneVecV {q : Fv} (hq : q ≠ 0) (y : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)))
    (hmem : coneVecV v q (y : Fin (k + 1) → Fv) ∈ coneSetV v (Qcone c₀ Q₀')) :
    (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec ⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ =
      iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) *
        dGt v c₀ Q₀' q := by
  have h0 : ((⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ : ConeTV v (Qcone c₀ Q₀')) :
      Fin (k + 1 + 1) → Fv) 0 ≠ 0 := by
    show coneVecV v q (y : Fin (k + 1) → Fv) 0 ≠ 0
    rw [coneVecV_zero]; exact hq
  have e : (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec ⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ =
      ConeReal.extSec {z : ConeTV v (Qcone c₀ Q₀') | (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0}
        (coneSec₀ v c₀ Q₀' hc hQ' hk) (1 :: (dG v c₀ Q₀' (two_ne_zero : (2 : Fv) ≠ 0) ::
          List.ofFn (fun j : Fin k => nG v c₀ Q₀' hc hQ' (Pi.single j 1)))) ⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ :=
    rfl
  rw [e, ConeReal.extSec_cons_of_mem _ (show (⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ :
    ConeTV v (Qcone c₀ Q₀')) ∈ {z : ConeTV v (Qcone c₀ Q₀') | (z : Fin (k + 1 + 1) → Fv) 0 ≠ 0} from h0),
    coneSec₀_of_ne v c₀ Q₀' hc hQ' hk h0, dGt_of_ne v c₀ Q₀' hq]
  have hy : yOfV v c₀ Q₀' h0 = y := by
    apply Subtype.ext
    funext i
    simp only [yOfV, coneVecV, Pi.smul_apply, Fin.cons_succ, smul_eq_mul, Fin.cons_zero, mul_one]
    field_simp
  congr 1
  · rw [hy]
  · exact mat_injective v _ (by rw [mat_dG, mat_dG]; simp only [coneVecV_zero])

end ConeOrbit

/-! ### The Haar measure of the stabilizer and the cone orbital identity -/

section Headline

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 1 ≤ k)

/-- **The parametrization** $(w, h) \mapsto n(w)\,\mathrm{diag}(1,1,h)$ of $P = \mathrm{Stab}(e) = N \rtimes SO(Q_0')$,
as a map into the stabilizer of the orbit section (the same as `pElem`, with the stabilizer of the base point). -/
def pElemV (p : (Fin k → Fv) × SOv v Q₀') : (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).stab :=
  ⟨nG v c₀ Q₀' hc hQ' p.1 * mG v c₀ Q₀' p.2,
    (Weil.OrbitSection.mem_stab_iff _).2
      (Subtype.ext ((mem_stabE_iff v c₀ Q₀' _).1 (nG_mG_mem v c₀ Q₀' hc hQ' p.1 p.2)))⟩

theorem continuous_pElemV : Continuous (pElemV v c₀ Q₀' hc hQ' hk) :=
  (((continuous_nG v c₀ Q₀' hc hQ').comp continuous_fst).mul
    ((continuous_mG v c₀ Q₀').comp continuous_snd)).subtype_mk _

/-- **The Haar measure of the stabilizer $P$ of $e$**: the image of $dw\otimes\mu_{SO(Q_0')}$ under
$(w, h) \mapsto n(w)\,\mathrm{diag}(1,1,h)$ ($dw$ = the product of the standard Haar measures of $F_v^k$). -/
def muPV : Measure ((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).stab) :=
  ((volV (haarV v) k).prod (muLocSO v Q₀' 1)).map (pElemV v c₀ Q₀' hc hQ' hk)

include hQ' in
theorem sFinite_muPV : SFinite (muPV v c₀ Q₀' hc hQ' hk) := by
  have := isHaarMeasure_muLocSO v Q₀' hQ'
  unfold muPV; infer_instance

include hQ' in
theorem lintegral_muPV {φ : (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).stab → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ p, φ p ∂muPV v c₀ Q₀' hc hQ' hk =
      ∫⁻ w, ∫⁻ h, φ (pElemV v c₀ Q₀' hc hQ' hk (w, h)) ∂muLocSO v Q₀' 1 ∂volV (haarV v) k := by
  have := isHaarMeasure_muLocSO v Q₀' hQ'
  rw [muPV, lintegral_map hφ (continuous_pElemV v c₀ Q₀' hc hQ' hk).measurable,
    lintegral_prod (fun p => φ (pElemV v c₀ Q₀' hc hQ' hk p))
      (hφ.comp (continuous_pElemV v c₀ Q₀' hc hQ' hk).measurable).aemeasurable]

omit hQ' hk in
theorem cF_neg : ((NF.ι v (-c₀) : 𝔬) : Fv) = -cv v c₀ := by
  rw [cF_eq v (-c₀)]; simp [cv]

include hc in
/-- **The constants**: $|2c_0|^{-(k+1)}|2c_0|^{-k}\cdot\frac{1}{|2c_0q|}|q|^k = |2c_0|^{-(2k+2)}|q|^{k-1}$. -/
theorem const_identity {q : Fv} (hq : q ≠ 0) :
    ENNReal.ofReal ((absTwoM v c₀ ^ (k + 1))⁻¹) * ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹) *
        (rhoS v (cv v c₀) q * ENNReal.ofReal (‖q‖ ^ k)) =
      ENNReal.ofReal ((absTwoM v c₀ ^ (2 * k + 2))⁻¹) * rhoC v k q := by
  have ha : 0 < absTwoM v c₀ := absTwoM_pos v hc
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hn : ‖2 * cv v c₀ * q‖ = absTwoM v c₀ * ‖q‖ := by rw [norm_mul, ← absTwoM_eq_norm]
  unfold rhoS rhoC
  rw [hn, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

include hc hQ' hk in
/-- **The fibre integral over $P$ at a cone point $q(1, y)$**: $\int_P f(s(z)\,p)\,d\mu_P(p)$ with
$s(q(1, y)) = \iota(s'(y))\,d(q)$ and $p = n(w)\,\mathrm{diag}(1,1,h)$. -/
theorem cone_slice {f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞} (hf : Measurable f) {q : Fv} (hq : q ≠ 0)
    (y : FibreO.sphereSet v (QQ (-c₀) Q₀') (mm (-c₀)))
    (hmem : coneVecV v q (y : Fin (k + 1) → Fv) ∈ coneSetV v (Qcone c₀ Q₀')) :
    ∫⁻ p, f ((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec ⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ *
        (p : SOv v (Qcone c₀ Q₀'))) ∂muPV v c₀ Q₀' hc hQ' hk =
      ∫⁻ h, ∫⁻ w, f (iotaSO v c₀ (Qmid c₀ Q₀')
          (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) * dGt v c₀ Q₀' q *
          nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h) ∂volV (haarV v) k ∂muLocSO v Q₀' 1 := by
  have := isHaarMeasure_muLocSO v Q₀' hQ'
  rw [sec_coneVecV v c₀ Q₀' hc hQ' hk hq y hmem]
  have hφ : Measurable fun p : (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).stab =>
      f (iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) *
        dGt v c₀ Q₀' q * (p : SOv v (Qcone c₀ Q₀'))) :=
    hf.comp (measurable_const.mul measurable_subtype_coe)
  rw [lintegral_muPV v c₀ Q₀' hc hQ' hk hφ]
  have hF : Measurable (Function.uncurry fun (w : Fin k → Fv) (h : SOv v Q₀') =>
      f (iotaSO v c₀ (Qmid c₀ Q₀') (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) *
        dGt v c₀ Q₀' q * (nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h))) :=
    hf.comp (measurable_const.mul (((continuous_nG v c₀ Q₀' hc hQ').measurable.comp measurable_fst).mul
      ((continuous_mG v c₀ Q₀').measurable.comp measurable_snd)))
  have hpe : ∀ (w : Fin k → Fv) (h : SOv v Q₀'),
      ((pElemV v c₀ Q₀' hc hQ' hk (w, h) : _) : SOv v (Qcone c₀ Q₀')) =
        nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h := fun _ _ => rfl
  simp only [hpe]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun h => lintegral_congr fun w => ?_
  simp only [mul_assoc]

set_option maxHeartbeats 1600000 in
include hc hQ' hk in
/-- **The fibration integral through the cone chart**: for measurable $f \ge 0$ on $SO(V)(F_v)$,
$$\int f\,d\Psi_*(\sigma_C\otimes\mu_P) = \int_{F_v}|q|_v^{k-1}\int_{S'_{-c_0}}\int_{SO(Q_0')}\int_{F_v^k}
  f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,dw\,d\mu(h)\,d\sigma'(y)\,dq.$$ -/
theorem lintegral_fib_cone_chart {f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂(coneOrbitSectionV v c₀ Q₀' hc hQ' hk).fibMeasure
        (sigConeV v (Qcone c₀ Q₀') (nondeg_cone c₀ Q₀' hc hQ')) (muPV v c₀ Q₀' hc hQ' hk) =
      ∫⁻ q, rhoC v k q * ∫⁻ y, ∫⁻ h, ∫⁻ w, f (iotaSO v c₀ (Qmid c₀ Q₀')
          (FibreSO.orbSO v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' hk (y, 1)) * dGt v c₀ Q₀' q *
          nG v c₀ Q₀' hc hQ' w * mG v c₀ Q₀' h) ∂volV (haarV v) k ∂muLocSO v Q₀' 1
        ∂nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ' ∂haarV v := by
  have hQm := nondeg_mid c₀ Q₀' hc hQ'
  have hQc := nondeg_cone c₀ Q₀' hc hQ'
  have := sFinite_muPV v c₀ Q₀' hc hQ' hk
  rw [(coneOrbitSectionV v c₀ Q₀' hc hQ' hk).lintegral_fibMeasure _ _ hf]
  obtain ⟨H, hH⟩ : ∃ H : ConeTV v (Qcone c₀ Q₀') → ℝ≥0∞,
      H = fun z => ∫⁻ p, f ((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec z * (p : SOv v (Qcone c₀ Q₀')))
        ∂muPV v c₀ Q₀' hc hQ' hk := ⟨_, rfl⟩
  have hHm : Measurable H := by
    rw [hH]
    have : Measurable fun p : ConeTV v (Qcone c₀ Q₀') × (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).stab =>
        f ((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec p.1 * (p.2 : SOv v (Qcone c₀ Q₀'))) :=
      hf.comp (((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).measurable_sec.comp measurable_fst).mul
        (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hstep : ∫⁻ z, ∫⁻ p, f ((coneOrbitSectionV v c₀ Q₀' hc hQ' hk).sec z * (p : SOv v (Qcone c₀ Q₀')))
      ∂muPV v c₀ Q₀' hc hQ' hk ∂sigConeV v (Qcone c₀ Q₀') hQc =
      ∫⁻ z, H z ∂sigConeV v (Qcone c₀ Q₀') hQc := by rw [hH]
  rw [hstep, lintegral_sigConeV v (Qcone c₀ Q₀') hQc hHm]
  have hHext : Measurable (Function.extend Subtype.val H 0) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_coneSetV v (Qcone c₀ Q₀'))).measurable_extend hHm
      measurable_const
  rw [lintegral_lerayMeasure_cone v (NF.Qp v (Qmid c₀ Q₀')) (NF.nondegenerate_Qp v hQm)
    (NF.nondegenerate_Qp v hQc) (cv_ne v c₀ hc) (qv_cone_mid v c₀ Q₀') hHext]
  have hmapval := FibreSO.map_val_nuS v (-c₀) (neg_ne_zero.2 hc) Q₀' hQ'
  rw [cF_neg v c₀] at hmapval
  rw [← hmapval]
  refine lintegral_congr fun q => ?_
  by_cases hq : q = 0
  · simp [rhoC, hq]
  congr 1
  have hmeasy : Measurable fun y : Fin (k + 1) → Fv => Function.extend Subtype.val H 0 (coneVecV v q y) :=
    hHext.comp ((measurable_coneVecV v).comp (measurable_const.prodMk measurable_id))
  rw [lintegral_map hmeasy measurable_subtype_coe]
  refine lintegral_congr fun y => ?_
  have hmem := coneVecV_mem v c₀ Q₀' hq y.2
  have e : Function.extend Subtype.val H 0 (coneVecV v q (y : Fin (k + 1) → Fv)) =
      H ⟨coneVecV v q (y : Fin (k + 1) → Fv), hmem⟩ :=
    Subtype.val_injective.extend_apply H 0 ⟨_, hmem⟩
  rw [e, hH]
  exact cone_slice v c₀ Q₀' hc hQ' hk hf hq y hmem

include hc hQ' hk in
/-- **The cone orbital identity at a finite place** (every $v$, dyadic included; $c_0 \ne 0$, $Q_0'$ nondegenerate in
$k \ge 1$ variables; $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$):
$$\mu_{SO(Q_0)} = |2c_0|_v^{-(2k+2)}\cdot\Psi_*(\sigma_C\otimes\mu_P),\qquad \Psi(z, p) = s(z)\,p,$$
with $\mu_{SO(Q_0)}$ the local measure `muLocSO` on $SO(V)(F_v)$, $\sigma_C$ the Leray measure of the punctured cone
(`sigConeV`), $\mu_P$ the Haar measure of the stabilizer $P = N \rtimes SO(Q_0')$ of $e = e_0+e_1$ (`muPV`), and $s$ the
explicit section `coneOrbitSectionV` (the fibration measure `OrbitSection.fibMeasure`). With $n = k+2 = \dim V$ the
constant is $|2c_0|_v^{-2(n-1)}$. -/
@[kb "weil1982" "§2.4 (Lemma 2.4.1 / Theorem 2.4.3 for the cone orbit at a finite place) [unverified]"]
theorem lerayMeasure_cone_orbital_finitePlace :
    muLocSO v (Qcone c₀ Q₀') 1 =
      ENNReal.ofReal ((absTwoM v c₀ ^ (2 * k + 2))⁻¹) •
        (coneOrbitSectionV v c₀ Q₀' hc hQ' hk).fibMeasure
          (sigConeV v (Qcone c₀ Q₀') (nondeg_cone c₀ Q₀' hc hQ')) (muPV v c₀ Q₀' hc hQ' hk) := by
  have key : ∀ f : SOv v (Qcone c₀ Q₀') → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂muLocSO v (Qcone c₀ Q₀') 1 =
        ENNReal.ofReal ((absTwoM v c₀ ^ (2 * k + 2))⁻¹) *
          ∫⁻ g, f g ∂(coneOrbitSectionV v c₀ Q₀' hc hQ' hk).fibMeasure
            (sigConeV v (Qcone c₀ Q₀') (nondeg_cone c₀ Q₀' hc hQ')) (muPV v c₀ Q₀' hc hQ' hk) := by
    intro f hf
    rw [lintegral_fib_cone_chart v c₀ Q₀' hc hQ' hk hf, lintegral_cone_param v c₀ Q₀' hc hQ' hk hf,
      ← lintegral_const_mul' (ENNReal.ofReal ((absTwoM v c₀ ^ (k + 1))⁻¹) *
        ENNReal.ofReal ((absTwoM v c₀ ^ k)⁻¹)) _
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun q => ?_
    by_cases hq : q = 0
    · simp [rhoS, rhoC, hq]
    rw [← mul_assoc (ENNReal.ofReal _) (rhoC v k q), ← const_identity v c₀ hc hq]
    try ring
  ext A hA
  rw [Measure.smul_apply, ← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    key _ (measurable_one.indicator hA), smul_eq_mul]

end Headline

/-! ### The product formula for the constants of the cone orbital identity -/

section Product

/-- **The archimedean constant** of the cone orbital identity at an infinite place $w$ (real: $|2c_0|_w^{-(2k+2)}$ with
$|x|_w = w(x)$; complex: $|2c_0|_w^{-(2k+2)}$ with $|x|_w = w(x)^2$): $\big(w(2c_0)^{\mathrm{mult}\,w}\big)^{-(2k+2)}$. -/
def coneConstArch (w : NumberField.InfinitePlace F) (c₀ : 𝓞 F) (k : ℕ) : ℝ :=
  ((w (algebraMap (𝓞 F) F (2 * c₀)) ^ w.mult) ^ (2 * k + 2))⁻¹

/-- At a real place the constant is $w(2c_0)^{-(2k+2)}$ (as in `ConeNF.lerayMeasure_cone_orbital_realPlace`). -/
theorem coneConstArch_real {w : NumberField.InfinitePlace F} (hw : w.IsReal) (c₀ : 𝓞 F) (k : ℕ) :
    coneConstArch w c₀ k = (w (algebraMap (𝓞 F) F (2 * c₀)) ^ (2 * k + 2))⁻¹ := by
  simp [coneConstArch, hw.mult_eq_one]

/-- At a complex place the constant is $(w(2c_0)^2)^{-(2k+2)}$ (as in
`ConeNF.lerayMeasureC_cone_orbital_complexPlace`). -/
theorem coneConstArch_complex {w : NumberField.InfinitePlace F} (hw : w.IsComplex) (c₀ : 𝓞 F) (k : ℕ) :
    coneConstArch w c₀ k = ((w (algebraMap (𝓞 F) F (2 * c₀)) ^ 2) ^ (2 * k + 2))⁻¹ := by
  simp [coneConstArch, hw.mult_eq_two]

/-- At a finite place not dividing $2c_0$ the constant is $1$. -/
theorem absTwoM_pow_inv_eq_one (c₀ : 𝓞 F) (hc : c₀ ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badSet c₀ hc) (n : ℕ) : (absTwoM v c₀ ^ n)⁻¹ = 1 := by
  rw [absTwoM_eq_one v fun h => hv ((mem_badSet c₀ hc).2 h), one_pow, inv_one]

/-- **The product of the constants is $1$** (product formula): the constants $|2c_0|_w^{-(2k+2)}$ of the cone orbital
identity, at the infinite places `coneConstArch` (`ConeNF.lerayMeasure_cone_orbital_realPlace`,
`ConeNF.lerayMeasureC_cone_orbital_complexPlace`) and at the finite places
`lerayMeasure_cone_orbital_finitePlace` (equal to $1$ outside the finitely many places dividing $2c_0$), multiply to $1$.
A corollary of the corresponding statement for the sphere identities (`FibreSO.prod_orbital_constants_eq_one`, with
$n = 2k+2$). -/
@[kb "weil1982" "§2.1 (product formula); §4.5 [unverified]"]
theorem prod_cone_constants_eq_one (c₀ : 𝓞 F) (hc : c₀ ≠ 0) (k : ℕ) :
    (∏ w : NumberField.InfinitePlace F, coneConstArch w c₀ k) *
      ∏ v ∈ badSet c₀ hc, (absTwoM v c₀ ^ (2 * k + 2))⁻¹ = 1 :=
  FibreSO.prod_orbital_constants_eq_one c₀ hc (2 * k + 2)

end Product

end QuadFormsKB.Tamagawa.Measure.ConeFinite
