import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.ConeFiniteChart
import QuadFormsKB.Tamagawa.Measure.ConeArchFinite
import QuadFormsKB.Tamagawa.Measure.ConeNF
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO

/-!
# The adelic cone measure and the finiteness of the cone integral

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n$ variables, $L = \mathcal O_F^n$. At a finite place
$v$ the cone measure is the Leray measure $\sigma_{0,v}$ = `lerayMeasure v (haarV v) (NF.Qp v Q₀) _ 0` on $F_v^n$
(`coneMeas`), carried by the punctured cone $C^\circ_v$.

**Local finiteness.** `coneMeas_latL`: $\sigma_{0,v}(L_v) = \gamma_v/(1-q_v^{2-n})$ (`coneTotal`, $n \ge 3$);
`coneMeas_lt_top_of_bounded`: $\sigma_{0,v}(K) < \infty$ for every bounded $K$ (homogeneity of degree $n-2$, from the
scaling law `lerayMeasure_map_smul_units`).

**The Euler product.** `multipliable_coneTotal_off`: for every finite set $S$ of places the product
$\prod_{v\notin S}\sigma_{0,v}(L_v)$ converges ($n \ge 5$; the good-place bound $|\gamma_v - 1| \le 2N\mathfrak p_v^{-2}$).

**The adelic cone measure on a box.** For a finite set $S$ of finite places and bounded measurable $K_v \subseteq F_v^n$
($v \in S$), with $K_v = L_v$ for $v \notin S$, `coneBoxMeasure S K` is the measure on $\prod_v F_v^n$
$$\sigma_{C,f}^{S,K} = \Big(\prod_v\sigma_{0,v}(K_v)\Big)\cdot\bigotimes_v\frac{\sigma_{0,v}|_{K_v}}{\sigma_{0,v}(K_v)}$$
(Mathlib's `Measure.infinitePi`; a factor with $\sigma_{0,v}(K_v) = 0$ is replaced by a Dirac mass, and then the total mass is
$0$): it is $\bigotimes_v\sigma_{0,v}$ on the box $\prod_vK_v$ (`coneBoxMeasure_cylinder`). Its total mass `boxMass` is
finite (`boxMass_lt_top`, $n \ge 5$).

**The cone integral.** For $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ and a test function
$\Phi = \bigotimes_{w\mid\infty}\Phi_w\otimes\mathbf 1_{\prod_vK_v}$ with each $\Phi_w$ bounded by a Gaussian
$C_we^{-a_w\|z\|^2}$ (the Gaussian of a positive majorant at every infinite place, and also its Fourier transform),
`coneIntegral` $= \prod_{w\mid\infty}\int\Phi_w\,d\sigma_{C,w}\cdot\sigma_{C,f}^{S,K}(\prod_v K_v)$ and
**`coneIntegral_lt_top`**: $I_C(\Phi) < \infty$ ($k \ge 3$, i.e. $n = k + 2 \ge 5$). The family $K_v$ is arbitrary at the
finitely many places of $S$, so this covers $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ ($S = \emptyset$) and its Fourier
transform $\hat\Phi = \hat\Phi_\infty\otimes\mathrm{vol}(\hat L)\mathbf 1_{\hat L^\#}$ ($L_v^\# = L_v$ off the places dividing
$2\det H_Q\,\mathfrak d_F$), as well as all the dilates $\Phi(z\,\cdot)$, $z \in \mathbb A^\times$.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeAdelic

open IsDedekindDomain NumberField QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayFinite QuadFormsKB.Tamagawa.Measure.LerayCone QuadFormsKB.Tamagawa
open QuadFormsKB.GlobalZeta QuadFormsKB.NFEuler QuadFormsKB.Tamagawa.Measure.ConeFinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "qv" v => ((DVR.q (HeightOneSpectrum.adicCompletionIntegers F v) : ℕ) : ℝ)

/-- **The cone measure at a finite place** $v$: the Leray measure $\sigma_{0,v}$ of $Q_0$ at the level $0$. -/
abbrev coneMeas (v : HeightOneSpectrum (𝓞 F)) : Measure (Fin n → v.adicCompletion F) :=
  lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) 0

/-! ### Local volumes -/

include hQ in
theorem coneTotal_nonneg (hn : 3 ≤ n) (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ coneTotal Q₀ v := by
  unfold coneTotal
  refine mul_nonneg (coneFactor_nonneg Q₀ hQ (by omega) v) (inv_nonneg.mpr ?_)
  have hq2 : (2 : ℝ) ≤ qv v := by exact_mod_cast q_ge_two v
  have h1 : (1 : ℝ) ≤ (qv v) ^ (n - 2) := one_le_pow₀ (by linarith)
  have : ((qv v) ^ (n - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  linarith

/-- **The cone volume of the lattice points**: $\sigma_{0,v}(L_v) = $ `coneTotal Q₀ v` ($n \ge 3$, `haarV`). -/
theorem coneMeas_latL (hn : 3 ≤ n) (v : HeightOneSpectrum (𝓞 F)) :
    coneMeas Q₀ hQ v (latL v n) = ENNReal.ofReal (coneTotal Q₀ v) := by
  rw [coneMeas, lerayMeasure_latL_cone v (haarV v) Q₀ hQ hn]
  congr 1
  have : (haarV v).real (latticeV v 0 : Set (v.adicCompletion F)) = 1 := by
    rw [Measure.real, haarV_latticeV_zero]; rfl
  rw [this, one_pow, one_mul]

/-- **Bounded sets have finite cone measure** ($n \ge 3$): a bounded $K$ lies in $\varpi^{-m}L_v$, and
$\sigma_{0,v}(\varpi^{-m}L_v) = q^{m(n-2)}\sigma_{0,v}(L_v) < \infty$ (scaling, degree $n - 2$). -/
theorem coneMeas_lt_top_of_bounded (hn : 3 ≤ n) (v : HeightOneSpectrum (𝓞 F)) {K : Set (Fin n → v.adicCompletion F)}
    (hK : Bornology.IsBounded K) : coneMeas Q₀ hQ v K < ⊤ := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  set R' := max R 1
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hR'pos) (norm_ϖ_lt_one v)
  set t : (v.adicCompletion F)ˣ := Units.mk0 (HN.ϖ v ^ m) (pow_ne_zero _ (HN.ϖ_ne_zero v))
  have hmap := lerayMeasure_map_smul_units v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) t 0
  rw [mul_zero] at hmap
  have hmeas : Measurable fun x : Fin n → v.adicCompletion F => (t : v.adicCompletion F) • x :=
    (continuous_const_smul _).measurable
  have hL : MeasurableSet (latL v n) := measurableSet_latL v
  have h2 := congrArg (fun μ => μ (latL v n)) hmap
  simp only [Measure.map_apply hmeas hL, Measure.smul_apply, smul_eq_mul] at h2
  have hsub : K ⊆ (fun x : Fin n → v.adicCompletion F => (t : v.adicCompletion F) • x) ⁻¹' latL v n := by
    intro x hx i
    simp only [Set.mem_preimage, Pi.smul_apply, smul_eq_mul, t, Units.val_mk0]
    have hxi : ‖x i‖ ≤ R' := (norm_le_pi_norm x i).trans ((hR x hx).trans (le_max_left _ _))
    have hle : ‖HN.ϖ v ^ m * x i‖ ≤ ‖HN.ϖ v‖ ^ 0 := by
      rw [pow_zero, norm_mul, norm_pow]
      calc ‖HN.ϖ v‖ ^ m * ‖x i‖ ≤ R'⁻¹ * R' := by gcongr
        _ = 1 := inv_mul_cancel₀ hR'pos.ne'
    have := (norm_le_iff_v v).mp hle
    simpa using this
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  show coneMeas Q₀ hQ v _ < ⊤
  rw [coneMeas, h2]
  refine ENNReal.mul_lt_top ?_ ?_
  · refine ENNReal.div_lt_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (pow_ne_zero _ ?_)
    simpa using (distribHaarChar_pos (A := v.adicCompletion F) (g := t)).ne'
  · have hl := coneMeas_latL Q₀ hQ hn v
    rw [coneMeas] at hl
    rw [hl]; exact ENNReal.ofReal_lt_top

/-! ### The Euler product -/

/-- The homogeneity factor $(1 - q_v^{2-n})^{-1}$ is within $4N\mathfrak p_v^{-2}$ of $1$ ($n \ge 4$). -/
theorem abs_homog_sub_one_le (hn : 4 ≤ n) (v : HeightOneSpectrum (𝓞 F)) :
    |(1 - ((qv v) ^ (n - 2))⁻¹)⁻¹ - 1| ≤ 4 * (normP v : ℝ) ^ (-(2 : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ qv v := by exact_mod_cast q_ge_two v
  have hq0 : (0 : ℝ) < qv v := by linarith
  have hnorm : (normP v : ℝ) ^ (-(2 : ℝ)) = ((qv v) ^ 2)⁻¹ := by
    rw [← qv_eq, Real.rpow_neg hq0.le, Real.rpow_two]
  rw [hnorm]
  set q : ℝ := qv v
  set x : ℝ := (q ^ (n - 2))⁻¹ with hx
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hx0 : 0 < x := inv_pos.mpr (pow_pos hq0 _)
  have hxle : x ≤ ((q) ^ 2)⁻¹ := inv_anti₀ (pow_pos hq0 2) (pow_le_pow_right₀ hq1 (by omega))
  have hq4 : ((q) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have h1x : 0 < 1 - x := by linarith
  have : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [this, abs_of_pos (div_pos hx0 h1x), div_le_iff₀ h1x]
  nlinarith [inv_pos.mpr (pow_pos hq0 2)]

include hQ in
open Classical in
/-- **The Euler product of the cone volumes converges away from any finite set** ($n \ge 5$):
$v \mapsto \sigma_{0,v}(L_v)$ for $v \notin S$, $1$ for $v \in S$, is multipliable. -/
@[kb "weil1982" "§4.5, p. 108 and §2.4 (cone term converges, m > 4) [unverified]"]
theorem multipliable_coneTotal_off (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Multipliable fun v => if v ∈ S then (1 : ℝ) else coneTotal Q₀ v := by
  classical
  have h1 : Multipliable fun v => if v ∈ S then (1 : ℝ) else coneFactor Q₀ v := by
    refine multipliable_of_abs_sub_one_le _ (C := 2) (σ := 2) (by norm_num) ?_
    filter_upwards [isGoodPlace_cofinite Q₀ hQ] with v hv
    split_ifs
    · simp only [sub_self, abs_zero]; positivity
    · exact abs_coneFactor_sub_one_le Q₀ hQ hn hv
  have h2 : Multipliable fun v => if v ∈ S then (1 : ℝ) else (1 - ((qv v) ^ (n - 2))⁻¹)⁻¹ := by
    refine multipliable_of_abs_sub_one_le _ (C := 4) (σ := 2) (by norm_num) (Eventually.of_forall fun v => ?_)
    split_ifs
    · simp only [sub_self, abs_zero]; positivity
    · exact abs_homog_sub_one_le (by omega) v
  convert h1.mul h2 using 1
  funext v
  show _ = (if v ∈ S then (1 : ℝ) else coneFactor Q₀ v) * (if v ∈ S then (1 : ℝ) else (1 - ((qv v) ^ (n - 2))⁻¹)⁻¹)
  split_ifs <;> simp [coneTotal]

/-! ### The adelic cone measure on a box -/

variable {Q₀ hQ}

/-- The box $K_v$ ($v \in S$), $L_v$ ($v \notin S$). -/
def boxSet (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin n → v.adicCompletion F) :=
  open Classical in if v ∈ S then K v else latL v n

variable (Q₀ hQ) in
/-- **The total mass** $\prod_v\sigma_{0,v}(K_v) = \prod_{v\in S}\sigma_{0,v}(K_v)\cdot\prod'_{v\notin S}\sigma_{0,v}(L_v)$. -/
def boxMass (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) :
    ℝ≥0∞ :=
  open Classical in
  (∏ v ∈ S, coneMeas Q₀ hQ v (K v)) * ENNReal.ofReal (∏' v, if v ∈ S then (1 : ℝ) else coneTotal Q₀ v)

variable (Q₀ hQ) in
/-- The normalized local factor $\sigma_{0,v}|_{K_v}/\sigma_{0,v}(K_v)$ (a Dirac mass if $\sigma_{0,v}(K_v) = 0$). -/
def probV (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F))
    (v : HeightOneSpectrum (𝓞 F)) : Measure (Fin n → v.adicCompletion F) :=
  open Classical in
  if coneMeas Q₀ hQ v (boxSet S K v) = 0 ∨ coneMeas Q₀ hQ v (boxSet S K v) = ⊤ then Measure.dirac 0
  else (coneMeas Q₀ hQ v (boxSet S K v))⁻¹ • (coneMeas Q₀ hQ v).restrict (boxSet S K v)

instance (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F))
    (v : HeightOneSpectrum (𝓞 F)) : IsProbabilityMeasure (probV Q₀ hQ S K v) := by
  classical
  unfold probV
  split_ifs with h
  · infer_instance
  · push_neg at h
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel h.1 h.2]

variable (Q₀ hQ) in
/-- **The adelic cone measure on the box** $\prod_vK_v$ ($K_v = L_v$ for $v \notin S$):
$\big(\prod_v\sigma_{0,v}(K_v)\big)\cdot\bigotimes_v\sigma_{0,v}|_{K_v}/\sigma_{0,v}(K_v)$, a measure on $\prod_v F_v^n$. -/
@[kb "weil1982" "§2.3, p. 21 (product measures on the restricted product); §4.5 (the cone term) [unverified]"]
def coneBoxMeasure (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) :
    Measure (∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F) :=
  boxMass Q₀ hQ S K • Measure.infinitePi (probV Q₀ hQ S K)

theorem coneBoxMeasure_univ (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) :
    coneBoxMeasure Q₀ hQ S K Set.univ = boxMass Q₀ hQ S K := by
  rw [coneBoxMeasure, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]

/-- **$\sigma_{C,f}^{S,K}$ is the product of the local cone measures on the box**: on a cylinder
$\{x : x_v \in U_v\ (v \in T)\}$ ($T$ finite, $U_v$ measurable) it is the total mass times
$\prod_{v\in T}\sigma_{0,v}(U_v\cap K_v)/\sigma_{0,v}(K_v)$ (when the $\sigma_{0,v}(K_v)$, $v \in T$, are in $(0,\infty)$). -/
theorem coneBoxMeasure_cylinder (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) (hU : ∀ v ∈ T, MeasurableSet (U v))
    (hK : ∀ v ∈ T, MeasurableSet (boxSet S K v))
    (hpos : ∀ v ∈ T, coneMeas Q₀ hQ v (boxSet S K v) ≠ 0 ∧ coneMeas Q₀ hQ v (boxSet S K v) ≠ ⊤) :
    coneBoxMeasure Q₀ hQ S K {x | ∀ v ∈ T, x v ∈ U v} =
      boxMass Q₀ hQ S K * ∏ v ∈ T,
        coneMeas Q₀ hQ v (U v ∩ boxSet S K v) / coneMeas Q₀ hQ v (boxSet S K v) := by
  classical
  have hcyl : {x : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F | ∀ v ∈ T, x v ∈ U v} =
      Set.pi (T : Set (HeightOneSpectrum (𝓞 F))) U := by
    ext x; simp [Set.mem_pi]
  rw [coneBoxMeasure, Measure.smul_apply, smul_eq_mul, hcyl,
    Measure.infinitePi_pi (probV Q₀ hQ S K) (s := T) (fun v hv => hU v hv)]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨h0, ht⟩ := hpos v hv
  have hne : ¬(coneMeas Q₀ hQ v (boxSet S K v) = 0 ∨ coneMeas Q₀ hQ v (boxSet S K v) = ⊤) := by
    push_neg; exact ⟨h0, ht⟩
  rw [probV, if_neg hne, Measure.smul_apply, Measure.restrict_apply (hU v hv), smul_eq_mul, ENNReal.div_eq_inv_mul]

/-- **The total mass is finite** ($n \ge 5$, $K_v$ bounded for $v \in S$): the cone Euler product converges. -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral converges for m ≥ 5) [unverified]"]
theorem boxMass_lt_top (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F))
    (hK : ∀ v ∈ S, Bornology.IsBounded (K v)) : boxMass Q₀ hQ S K < ⊤ := by
  classical
  unfold boxMass
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  exact ENNReal.prod_lt_top fun v hv => coneMeas_lt_top_of_bounded Q₀ hQ (by omega) v (hK v hv)

/-- **The Euler product identity for the total mass** ($n \ge 5$): $\prod'_{v\notin S}\sigma_{0,v}(L_v)$ is a convergent
product (`multipliable_coneTotal_off`), so `boxMass` is the genuine infinite product $\prod_v\sigma_{0,v}(K_v)$ (for
$S = \emptyset$: $\prod_v\sigma_{0,v}(L_v)$, the cone Euler product). -/
theorem boxMass_empty (hn : 5 ≤ n) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) :
    boxMass Q₀ hQ ∅ K = ENNReal.ofReal (∏' v, coneTotal Q₀ v) := by
  simp [boxMass]

/-! ### The cone integral $I_C(\Phi)$ for $\Phi = \bigotimes_{w\mid\infty}\Phi_w\otimes\mathbf 1_{\prod_vK_v}$ -/

section Integral

open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.ConeAlgebra NumberField.InfinitePlace
open scoped Classical

variable {k : ℕ} {c₀ : 𝓞 F} (hc₀ : c₀ ≠ 0) {Q₀' : QuadForm (𝓞 F) k}

/-- The image $c_w$ of $c_0$ at a real place. -/
abbrev cRe (c₀ : 𝓞 F) (w : {w : InfinitePlace F // w.IsReal}) : ℝ :=
  embedding_of_isReal w.2 (algebraMap (𝓞 F) F c₀)

/-- The image $c_w$ of $c_0$ at a complex place. -/
abbrev cCx (c₀ : 𝓞 F) (w : {w : InfinitePlace F // w.IsComplex}) : ℂ := w.1.embedding (algebraMap (𝓞 F) F c₀)

include hc₀ in
theorem cRe_ne_zero (w : {w : InfinitePlace F // w.IsReal}) : cRe c₀ w ≠ 0 :=
  (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc₀)

include hc₀ in
theorem cCx_ne_zero (w : {w : InfinitePlace F // w.IsComplex}) : cCx c₀ w ≠ 0 :=
  (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc₀)

/-- At a real place the cone form is the cone form of the local data:
$(\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0')_w = \langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$. -/
theorem QRe_cone (w : {w : InfinitePlace F // w.IsReal}) :
    QRe (splitForm c₀ (splitForm (-c₀) Q₀')) w = coneForm (cRe c₀ w) (QRe Q₀' w) := by
  rw [QRe, coneForm, map_splitForm, map_splitForm, map_splitForm, map_splitForm, map_neg, map_neg]

/-- The same at a complex place. -/
theorem QCx_cone (w : {w : InfinitePlace F // w.IsComplex}) :
    QCx (splitForm c₀ (splitForm (-c₀) Q₀')) w = coneForm (cCx c₀ w) (QCx Q₀' w) := by
  rw [QCx, coneForm, map_splitForm, map_splitForm, map_splitForm, map_splitForm, map_neg, map_neg]

variable (Q₀') in
/-- **The archimedean factor** $\prod_{w\mid\infty}\int\Phi_w\,d\sigma_{C,w}$ of the cone integral, with $\sigma_{C,w}$ the
Leray measure of the punctured cone of $\langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$ (the
`ConeReal.sigCone`, `ConeComplex.sigCone`). -/
def coneIntegralArch
    (Φr : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (coneForm (cRe c₀ w) (QRe Q₀' w)) → ℝ≥0∞)
    (Φc : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (coneForm (cCx c₀ w) (QCx Q₀' w)) → ℝ≥0∞) :
    ℝ≥0∞ :=
  (∏ w, ∫⁻ z, Φr w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne_zero hc₀ w)) *
    ∏ w, ∫⁻ z, Φc w z ∂ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne_zero hc₀ w)

variable (Q₀') in
/-- **The cone integral** $I_C(\Phi) = \int_{C^\circ(\mathbb A)}\Phi\,d\sigma_C$ of
$\Phi = \bigotimes_{w\mid\infty}\Phi_w\otimes\mathbf 1_{\prod_vK_v}$: the archimedean factor times the mass of the box for the
adelic cone measure `coneBoxMeasure` (on which $\mathbf 1_{\prod_v K_v} = 1$ almost everywhere). -/
def coneIntegral (hQ : (splitForm c₀ (splitForm (-c₀) Q₀')).Nondegenerate)
    (Φr : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (coneForm (cRe c₀ w) (QRe Q₀' w)) → ℝ≥0∞)
    (Φc : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (coneForm (cCx c₀ w) (QCx Q₀' w)) → ℝ≥0∞)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) : ℝ≥0∞ :=
  coneIntegralArch hc₀ Q₀' Φr Φc * coneBoxMeasure (splitForm c₀ (splitForm (-c₀) Q₀')) hQ S K Set.univ

/-- **Finiteness of the cone integral** ($k \ge 3$, i.e. $\dim V = k + 2 \ge 5$; every number field, every signature):
if every archimedean factor $\Phi_w$ is bounded by a Gaussian $C_we^{-a_w\|z\|^2}$ and the $K_v$ ($v \in S$) are bounded,
then $I_C(\Phi) < \infty$. In particular $I_C(\Phi) < \infty$ and $I_C(\hat\Phi) < \infty$ for
$\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ with $\Phi_\infty$ the Gaussian of a positive majorant ($\hat\Phi$ is again of this
shape, with the dual lattices $L_v^\#$ at the finitely many places dividing $2\det H_Q\,\mathfrak d_F$). -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral converges for m ≥ 5) [unverified]"]
theorem coneIntegral_lt_top (hk : 3 ≤ k) (hQ' : Q₀'.Nondegenerate)
    (hQ : (splitForm c₀ (splitForm (-c₀) Q₀')).Nondegenerate)
    (Φr : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (coneForm (cRe c₀ w) (QRe Q₀' w)) → ℝ≥0∞)
    (Φc : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (coneForm (cCx c₀ w) (QCx Q₀' w)) → ℝ≥0∞)
    (ar Cr : {w : InfinitePlace F // w.IsReal} → ℝ) (har : ∀ w, 0 < ar w) (hCr : ∀ w, 0 ≤ Cr w)
    (hΦr : ∀ w z, Φr w z ≤ ENNReal.ofReal (Cr w * Real.exp (-(ar w * ‖(z : Fin (k + 1 + 1) → ℝ)‖ ^ 2))))
    (ac Cc : {w : InfinitePlace F // w.IsComplex} → ℝ) (hac : ∀ w, 0 < ac w) (hCc : ∀ w, 0 ≤ Cc w)
    (hΦc : ∀ w z, Φc w z ≤ ENNReal.ofReal (Cc w * Real.exp (-(ac w * ‖(z : Fin (k + 1 + 1) → ℂ)‖ ^ 2))))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F))
    (hK : ∀ v ∈ S, Bornology.IsBounded (K v)) :
    coneIntegral hc₀ Q₀' hQ Φr Φc S K < ⊤ := by
  unfold coneIntegral coneIntegralArch
  rw [coneBoxMeasure_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) (boxMass_lt_top (by omega) S K hK)
  · exact ENNReal.prod_lt_top fun w _ => ConeReal.lintegral_sigCone_gaussian_lt_top (cRe_ne_zero hc₀ w)
      (gramDetR_QRe_ne_zero Q₀' hQ' w) (by omega) (har w) (hCr w) (Φr w) (hΦr w)
  · exact ENNReal.prod_lt_top fun w _ => ConeComplex.lintegral_sigCone_gaussian_lt_top (cCx_ne_zero hc₀ w)
      (gramDetC_QCx_ne_zero Q₀' hQ' w) (by omega) (hac w) (hCc w) (Φc w) (hΦc w)

end Integral

end QuadFormsKB.Tamagawa.Measure.ConeAdelic
