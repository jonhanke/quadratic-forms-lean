/-
# Siegel's formula in one variable: corank zero and corank one for $N = 1$

**Layer:** number fields. $F$ **any** number field, $Q_0 = \langle a\rangle$ a nondegenerate form over $\mathcal O_F$ in $N = 1$
variable ($Q_0(x) = ax^2$, $a\ne0$), $L = \mathcal O_F$. Here $SO(V) = SO_1$ is trivial over every ring: the genus of $L$ has one
proper class (`subsingleton_DC_rankOne`), the unit group is trivial, and Weil's Tamagawa number is $\tau(SO_1) = 1$
(`covolume_muTam_rankOne`), not $2$. Notation as in `SiegelCorankZero.lean`: $n(M_i,T_0)$ = `repCount`, $v(M_i)$ =
`unitVolume`, $\beta_\mathfrak p$ = `NF.localDensityForm`, normalized absolute values $|x|_w$ at the infinite places
($|\sigma_wx|$ real, $|\sigma_wx|^2$ complex).

**Statements (unconditional):**
* `tsum_unitVolume_rankOne` (the mass formula, $\tau(SO_1) = 1$): $\sum_iv(M_i) = \prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}$
  ($\det H_{Q_0} = 2a$);
* **`siegelUnary_corank0_uncond`** (corank zero, $T_0 = \langle b\rangle$ with a rational frame $\Xi = (c)$, $b = ac^2$):
  $$\sum_in(M_i,T_0) = 2\prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i);$$
* `siegelUnary_corank0_self_iff_tau`: at $T_0 = Q_0$, $\Xi = 1$ the formula is $\tau(SO_1) = 1$;
* **`siegelUnary_corank1_uncond`** (corank one, $r = 0$: the empty frame, $n(M_i,\emptyset) = 1$ by `repCount_formZero`):
  $$c^{(1)}_\infty(Q_0)\sum_in(M_i,\emptyset) = \prod_\mathfrak p\beta_\mathfrak p(L,\emptyset)\cdot\sum_iv(M_i).$$

**The factor $2$.** For $N\ge2$ (`siegelIndefiniteForms_corank0_uncond`, $\tau(SO(V)) = 2$) Weil's factor
$\tau(SO_0)/\tau(SO(V)) = \tfrac12$ cancels the two $SO(V)(F)$-orbits of rational frames ($\det X = \pm\det\Xi$). For $N = 1$ the
two orbits $\{c\}$, $\{-c\}$ remain while $\tau(SO_0)/\tau(SO_1) = 1$, so the factor $2$ stays: classically
$n(L,\langle ac^2\rangle) = \#\{x\in\mathcal O_F : ax^2 = ac^2\} = 2$ when $c\in\mathcal O_F$ and $0$ otherwise, and for
$c\in\mathcal O_F$ one has $\tfrac12\beta_\mathfrak p = |2ac|_\mathfrak p^{-1}$, so the right side is
$2\prod_w|c|_w^{-1}|2ac|_w|2a|_w^{-1} = 2$ by the product formula.

**Proof:** the count `count_mul_tprod_zero` (which holds for $N\ge1$), the count `count_mul_tprod` (for $r = 0$), and
$\tau(SO_1) = 1$ in the form $\mu_f(SO(\hat L))\sum_iv(M_i) = 1$.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankZero
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

section Unary

variable (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate)

/-- **One proper class in the genus of a unary lattice**: $SO_1(\mathbb A_f)$ is trivial. -/
theorem subsingleton_DC_rankOne : Subsingleton (DC Q₀) := by
  have := subsingleton_SOAf Q₀
  refine ⟨fun i j => ?_⟩
  induction i using Quotient.inductionOn
  induction j using Quotient.inductionOn
  exact congrArg _ (Subsingleton.elim _ _)

include hQ in
/-- The local factors $a_v = \mu_v(SO(L_v))$ of a unary form have a finitely supported product. -/
theorem multipliable_aSO_rankOne : Multipliable fun v => aSO Q₀ v / (fun _ => (1 : ℝ)) v := by
  simp only [div_one]
  exact multipliable_of_hasFiniteMulSupport (mulSupport_aSO_rankOne_finite Q₀ hQ)

include hQ in
/-- **$\tau(SO_1) = 1$ in the form $\mu_f(SO(\hat L))\sum_iv(M_i) = 1$.** -/
theorem tprod_aSO_mul_tsum_unitVolume_rankOne :
    ENNReal.ofReal (∏' v, aSO Q₀ v) * ∑' i, unitVolume Q₀ hQ i = 1 := by
  have h := covolume_muTam_rankOne Q₀ hQ
  rw [covolume_muTam_eq_muFin_mul, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ (fun _ => one_pos)] at h
  simpa only [div_one] using h

open Classical in
/-- **The mass formula in one variable** ($\tau(SO_1) = 1$): $\sum_iv(M_i) = \prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}$,
normalized absolute values ($\det H_{Q_0} = 2a$ for $Q_0 = \langle a\rangle$). -/
@[kb "weil1982" "§3.7 (rank one: SO_1 trivial, τ = 1), mass formula for unary lattices [unverified page]"]
theorem tsum_unitVolume_rankOne :
    ∑' i, unitVolume Q₀ hQ i = ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
        |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹) := by
  have h := tprod_aSO_mul_tsum_unitVolume_rankOne Q₀ hQ
  rw [tprod_aSO_rankOne Q₀ hQ] at h
  set d := algebraMap (𝓞 F) F Q₀.hessian.det with hd
  have hd0 : d ≠ 0 := algebraMap_det_ne_zero Q₀ hQ
  set G := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w d|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w d‖ ^ 2 with hG
  have hGpos : 0 < G := by
    refine mul_pos (Finset.prod_pos fun w _ => abs_pos.2 ((map_ne_zero _).2 hd0))
      (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hd0)) 2)
  have hinv : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w d|⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w d‖ ^ 2)⁻¹ = G⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, hG, mul_inv]
  rw [hinv]
  have hG0 : ENNReal.ofReal G ≠ 0 := (ENNReal.ofReal_pos.2 hGpos).ne'
  calc ∑' i, unitVolume Q₀ hQ i
      = (ENNReal.ofReal G)⁻¹ * (ENNReal.ofReal G * ∑' i, unitVolume Q₀ hQ i) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hG0 ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal G⁻¹ := by rw [h, mul_one, ENNReal.ofReal_inv_of_pos hGpos]

open Classical in
/-- **Siegel's formula for isometries of unary forms, every number field — unconditional** (corank zero, $N = r = 1$;
Siegel's Hauptsatz with $\tau(SO_1) = 1$): for $F$ a number field, $Q_0$ and $T_0$ nondegenerate forms in one variable over
$\mathcal O_F$ with a rational frame $\Xi$ ($Q_0\circ\Xi = T_0$, i.e. $T_0 = \langle ac^2\rangle$ for $Q_0 = \langle a\rangle$,
$\Xi = (c)$, $c\in F^\times$),
$$\sum_in(M_i,T_0) = 2\prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F$ (there is one); $n(M_i,T_0)$ = `repCount` (the number
of $x\in M_i$ with $Q_0(x) = ac^2$, the unit group being trivial: $2$ if $c\in\mathcal O_F$, else $0$), $v(M_i)$ = `unitVolume`,
$|\cdot|_w$ normalized, $\beta_\mathfrak p$ = `NF.localDensityForm`. The factor $2$: two $SO(V)(F)$-orbits of rational frames
($\pm c$) and Weil's factor $\tau(SO_0)/\tau(SO_1) = 1$ (for $N\ge2$ it is $\tfrac12$ and cancels the $2$). -/
@[kb "siegel1935" "Hauptsatz for n = m = 1 (corank zero, τ(SO_1) = 1; every number field) [unverified]"]
theorem siegelUnary_corank0_uncond (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    ∑' i, repCount Q₀ T₀ i =
      2 * ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2) * ∑' i, unitVolume Q₀ hQ i := by
  have hApos : 0 < ∏' v, aSO Q₀ v := by
    rw [tprod_aSO_rankOne Q₀ hQ]
    have hd0 : algebraMap (𝓞 F) F Q₀.hessian.det ≠ 0 := algebraMap_det_ne_zero Q₀ hQ
    exact mul_pos (Finset.prod_pos fun w _ => abs_pos.2 ((map_ne_zero _).2 hd0))
      (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hd0)) 2)
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hτ := tprod_aSO_mul_tsum_unitVolume_rankOne Q₀ hQ
  obtain ⟨-, hcount⟩ := count_mul_tprod_zero Q₀ hQ T₀ hT one_pos Ξ (fun _ => 1) (multipliable_aSO_rankOne Q₀ hQ)
  simp only [div_one] at hcount
  refine (ENNReal.mul_left_inj hA0 hAt).mp (hcount.trans ?_)
  calc 2 * ENNReal.ofReal _ = 2 * ENNReal.ofReal _ * (A * ∑' i, unitVolume Q₀ hQ i) := by rw [hτ, mul_one]
    _ = _ := by ring

include hQ in
/-- **The corank-zero formula for $T_0 = Q_0$ is $\tau(SO_1) = 1$** ($N = 1$): with $\Xi = 1$ the left side is $2$
(`tsum_repCount_self`), so the formula reads $\mu_f(SO(\hat L))\sum_iv(M_i) = 1$, i.e. the covolume of $SO_1(F)$ in
$SO_1(\mathbb A)$ for Weil's measure is $1$. -/
theorem siegelUnary_corank0_self_iff_tau :
    ∑' i, repCount Q₀ Q₀ i =
        2 * ENNReal.ofReal (∏' v, NF.localDensityForm v Q₀ Q₀ / 2) * ∑' i, unitVolume Q₀ hQ i ↔
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 1 := by
  have ha : ∏' v, NF.localDensityForm v Q₀ Q₀ / 2 = ∏' v, aSO Q₀ v / 1 := tprod_congr fun v => by
    rw [aSO_eq_siegelDensity Q₀ hQ v]; simp only [NF.siegelDensity, ↓reduceIte]; ring
  rw [covolume_muTam_eq_muFin_mul, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ (fun _ => one_pos),
    tsum_repCount_self Q₀ hQ one_pos, ha, mul_assoc]
  constructor
  · intro h
    have h2 : (2 : ℝ≥0∞) * 1 = 2 * (ENNReal.ofReal (∏' v, aSO Q₀ v / 1) * ∑' i, unitVolume Q₀ hQ i) := by
      rw [mul_one]; exact h
    exact ((ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp h2).symm
  · intro h; rw [h, mul_one]

/-- The empty frame: the rational frame of the form in zero variables. -/
def ratFrameZero : RatFrame (r := 0) Q₀ (formZero (𝓞 F)) :=
  ⟨0, QuadForm.ext (Matrix.ext fun i => i.elim0)⟩

/-- **$n(M_i,\emptyset) = 1$**: the empty frame is the only representation of the form in zero variables. -/
theorem repCount_formZero (i : DC Q₀) : repCount (r := 0) Q₀ (formZero (𝓞 F)) i = 1 := by
  classical
  have hmem : ratAT Q₀ (formZero (𝓞 F)) (ratFrameZero Q₀) ∈ repsT Q₀ (formZero (𝓞 F)) i := by
    refine ⟨ratFrameZero Q₀, ?_, rfl⟩
    show ratFT Q₀ (formZero (𝓞 F)) (ratFrameZero Q₀) ∈ dcRep Q₀ i • latHatT F 1 0
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact fun j => j.elim0
  have hss : Subsingleton (repsT Q₀ (formZero (𝓞 F)) i) :=
    ⟨fun a b => Subtype.ext (funext fun j => j.elim0)⟩
  set q : orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ (formZero (𝓞 F)) i) := Quotient.mk _ ⟨_, hmem⟩
  have hq : ∀ q' : orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ (formZero (𝓞 F)) i), q' = q := by
    intro q'
    induction q' using Quotient.inductionOn
    exact congrArg _ (Subsingleton.elim _ _)
  unfold repCount
  rw [tsum_eq_single q fun q' h => absurd (hq q') h]

open Classical in
/-- **Siegel's formula for frames of corank one in one variable, every number field — unconditional** ($N = 1$, $r = 0$:
the empty frame): for $F$ a number field and $Q_0$ a nondegenerate form in one variable over $\mathcal O_F$,
$$c^{(1)}_\infty(Q_0)\sum_in(M_i,\emptyset) = |d_F|^{0}\prod_\mathfrak p\beta_\mathfrak p(L,\emptyset)\cdot\sum_iv(M_i),$$
$c^{(1)}_\infty(Q_0) = c_F(1)\prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}$ (`cInfCorankOne`, $c_F(1) = 1$), the right side
`frameDensityProduct` with $n' = 1$. Since $n(M_i,\emptyset) = 1$ (`repCount_formZero`), the genus has one class and
$\beta_\mathfrak p(L,\emptyset) = 1$, this is the mass formula `tsum_unitVolume_rankOne`; Weil's factor is
$\tau(SO_1)/\tau(SO_1) = 1$. -/
@[kb "siegel1935" "Hauptsatz for n = 1, m = 0 (corank one in one variable: the mass formula, τ(SO_1) = 1) [unverified]"]
theorem siegelUnary_corank1_uncond :
    cInfCorankOne Q₀ * ∑' i, repCount (r := 0) Q₀ (formZero (𝓞 F)) i =
      ENNReal.ofReal (frameDensityProduct (r := 0) (n' := 1) Q₀ (formZero (𝓞 F))) * ∑' i, unitVolume Q₀ hQ i := by
  set Ξ := ratFrameZero Q₀ with hΞ
  have hT := formZero_nondegenerate (F := F)
  set D := towerCorankOne (r := 0) Q₀ hQ (formZero (𝓞 F)) hT Ξ with hD
  have hApos : 0 < ∏' v, aSO Q₀ v := by
    rw [tprod_aSO_rankOne Q₀ hQ]
    have hd0 : algebraMap (𝓞 F) F Q₀.hessian.det ≠ 0 := algebraMap_det_ne_zero Q₀ hQ
    exact mul_pos (Finset.prod_pos fun w _ => abs_pos.2 ((map_ne_zero _).2 hd0))
      (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 hd0)) 2)
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hτ := tprod_aSO_mul_tsum_unitVolume_rankOne Q₀ hQ
  obtain ⟨hmf, hcount⟩ := count_mul_tprod (r := 0) Q₀ hQ (formZero (𝓞 F)) hT Ξ (fun _ => 1) (fun _ => one_pos)
    (multipliable_aSO_rankOne Q₀ hQ)
  have hid := densityIdentity_corankOne (r := 0) Q₀ hQ (formZero (𝓞 F)) Ξ D hT (fun _ => 1)
    (fun _ => one_ne_zero) hmf
  simp only [div_one] at hid hcount
  have hfdp : frameDensityProduct (r := 0) (n' := 1) Q₀ (formZero (𝓞 F)) =
      cF F 1 * ∏' v, NF.localDensityForm v Q₀ (formZero (𝓞 F)) := by
    unfold frameDensityProduct cF
    congr 2
    push_cast
    ring
  have key1 : cInfCorankOne Q₀ * (∑' i, repCount (r := 0) Q₀ (formZero (𝓞 F)) i) * A =
      ENNReal.ofReal (frameDensityProduct (r := 0) (n' := 1) Q₀ (formZero (𝓞 F))) := by
    rw [mul_assoc, hcount, cInfCorankOne_eq, ← ENNReal.ofReal_mul (mul_nonneg (cF_pos' (F := F) _).le (mul_nonneg
      (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity))), hfdp, ← hid]
    congr 1
    ring
  refine (ENNReal.mul_left_inj hA0 hAt).mp (key1.trans ?_)
  calc ENNReal.ofReal _ = ENNReal.ofReal _ * (A * ∑' i, unitVolume Q₀ hQ i) := by rw [hτ, mul_one]
    _ = _ := by ring

end Unary

end QuadFormsKB.Tamagawa.Indefinite
