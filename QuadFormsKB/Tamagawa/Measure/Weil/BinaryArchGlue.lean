import QuadFormsKB.Tamagawa.Measure.Weil.BinaryComparisonGlue
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchIntegrals
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryArchLeray
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSShellRatio
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSPlaces
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSTestAny
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSConstAny

/-!
# The archimedean part of the measure comparison for the binary torus
**Layer:** as in `BinaryComparisonGlue.lean`. $F$ is a number field, $D\in\mathcal O_F\setminus0$, $d = -D$ (`dD D`),
$Q_0 = \langle1,D\rangle$ (`diagForm1 D`), $E = F(\delta)$, $\delta^2 = d$, with $F$-basis $(1,\delta)$ = `b`
(`hb0 : b 0 = 1`, `hb1 : b 1 * b 1 = algebraMap F E (dD D)`; this forces $-D$ not to be a square in $F$). Indices are 0-based:
$x_{00}$ and $x_{10}$ are the two entries of the first column of a $2\times2$ matrix $x$.

**Defines**
* `shellE E` $= \{y\in(E_\infty)^\times : 1\le|y_W|\le e$ at the real places $W$ of $E$, $1\le\|y_W\|^2\le e$ at the complex
  places $W\}$ ($e = \exp 1$; $\|y_W\|^2$ is the normalized absolute value at a complex place);
* `fibPR`, `fibPC`: the conditions on $c\in F_w^\times$ at a real, resp. complex, place $w$ of $F$ for $y\,\iota(c)$ to lie in
  `shellE E`, one condition for each place $W$ of $E$ over $w$; `logShellR`, `logShellC`: the logarithmic shells
  $\{x\ne0 : a\le\log|x|\le b\}$; `orientEmb`: the embedding of $E$ over a complex place of $F$ oriented to restrict to the
  chosen embedding of $F$;
* `splitCoordG`, `complexCoordG`: $t(x) = x_{00} + \sqrt\delta\,x_{10}$, resp. $x_{00} + s\,x_{10}$, for $x\in SO(Q)(\mathbb R)$,
  resp. $SO(Q)(\mathbb C)$, for an arbitrary binary form $Q$ (the formulas of `BinaryArchIntegrals`);
* the weights `wReal` (at a real place $w$: $2\max(0,1-|\log|t||)$ if $\sigma_w(d)>0$, else $1$) and `wCpx` (at a complex place:
  $2\pi\max(0,1-2|\log\|t\||)$, $s^2 = \tau_w(d)$ = `sqrtDC`), and their integrals `realLocalR`, `cpxLocalR`;
* `shellRatio D` $= |N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}$.

**Proves**
1. **`omegaInf_shellE`**: $\omega_{\infty,E}(\mathrm{Sh}_E) = 2^{r_2(E)}\cdot2^{r_1(E)}\cdot\pi^{r_2(E)}$ (real factor
   $\int_{1\le|x|\le e}dx/|x| = 2$, complex factor $\int_{1\le\|z\|^2\le e}d^2z/\|z\|^2 = \pi$; `lintegral_logShellR`,
   `lintegral_logShellC`).
2. **`fibInfSO_shellE`**: the fibre function $K_\infty(x) = \omega_{\infty,F}\{c : y\,\iota(c)\in\mathrm{Sh}_E\}$ ($\mathrm{tor}(y) = x$)
   of `fibInfSO` is the product $\prod_{w\ \mathrm{real}}\mathrm{wReal}_w(x_w)\cdot\prod_{w\ \mathrm{complex}}\mathrm{wCpx}_w(x_w)$.
   *Proof.* The fibre is a box over the places of $F$ (`fibre_set_eq`, `omegaInf_box`); at a real place with $\sigma_w(d)>0$ it
   is the intersection of the two shells for the two real places $W_1,W_2$ over $w$, a logarithmic shell of length
   $1-|\log|y_{W_1}/y_{W_2}||$ (`fibPR_two_real`); $y_{W_1}/y_{W_2} = (x+\sqrt\delta y)/(x-\sqrt\delta y)$ is the split
   coordinate $t$ of $\mathrm{tor}(z)$ (`splitCoordG_torR`, since $u = z/\bar z$); at a real place with $\sigma_w(d)<0$
   (one complex place over $w$) it is a logarithmic shell of length $\tfrac12$ (`fibPR_one_complex`); at a complex place it is
   the intersection of the two shells for the two complex places over $w$, with the orientation `orientEmb` making the two
   values of $\delta$ opposite (`fibPC_two`, `orientEmb_delta_neg`).
3. **`lintegral_fibInfSO_shellE`**: $\int K_\infty\,d\mu^{\mathrm{Tam}}_\infty = c_F\,2^{r_2(F)}\prod_{w\ \mathrm{real}}\mathrm{realLocal}_w
   \prod_{w\ \mathrm{complex}}\mathrm{cpxLocal}_w$, with $\mathrm{realLocal}_w = 1/(2\delta_w\sqrt{\delta_w})$ if $\delta_w = \sigma_w(d)>0$
   and $\pi/(4D_w^{3/2})$ otherwise, $\mathrm{cpxLocal}_w = \pi^2/(32\|D_w\|^3)$, from `lintegral_splitWeight`,
   `lerayMeasure_diag_one_D_univ`, `lintegral_complexWeight` (transported along $Q^{\sigma_w} = \langle1,\sigma_w(D)\rangle$) and the
   product structure of `muArchTamSO`.
4. **`omegaInf_shellE_eq_mul`** and **`omegaInf_shellE_div`**:
   $\omega_{\infty,E}(\mathrm{Sh}_E) = |N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}\cdot\int K_\infty\,d\mu^{\mathrm{Tam}}_\infty$ (per place
   the ratio is $|4d|_w^{3/2}$; `shell_ratio_real`: $r_1(E) = 2\#\{\sigma_w(d)>0\}$, $r_2(E) = \#\{\sigma_w(d)<0\}+2r_2(F)$,
   `cF F 2` $= |d_F|^{-1/2}$, `cxWeil F 2` $= 2^{r_2(F)}$, $|N_{F/\mathbb Q}(x)| = \prod_{w\ \mathrm{real}}|\sigma_w x|
   \prod_{w\ \mathrm{complex}}\|\tau_w x\|^2$).

Source: Weil 1982, §2.2, §2.3 (gauge forms and the
archimedean factors) [unverified locator].
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

/-! ### One-variable integrals over logarithmic shells -/

section OneVariable

/-- The real logarithmic shell $\{x : x\ne0,\ a\le\log|x|\le b\}$. -/
def logShellR (a b : ℝ) : Set ℝ := {x | x ≠ 0 ∧ a ≤ Real.log |x| ∧ Real.log |x| ≤ b}

/-- The complex logarithmic shell $\{z : z\ne0,\ a\le\log\|z\|\le b\}$. -/
def logShellC (a b : ℝ) : Set ℂ := {z | z ≠ 0 ∧ a ≤ Real.log ‖z‖ ∧ Real.log ‖z‖ ≤ b}

theorem measurableSet_logShellR (a b : ℝ) : MeasurableSet (logShellR a b) := by
  have : logShellR a b = {x : ℝ | x ≠ 0} ∩ ((fun x : ℝ => Real.log |x|) ⁻¹' Icc a b) := by
    ext x; simp [logShellR]
  rw [this]
  exact (measurableSet_singleton 0).compl.inter (measurableSet_Icc.preimage (by fun_prop))

theorem measurableSet_logShellC (a b : ℝ) : MeasurableSet (logShellC a b) := by
  have : logShellC a b = {x : ℂ | x ≠ 0} ∩ ((fun x : ℂ => Real.log ‖x‖) ⁻¹' Icc a b) := by
    ext x; simp [logShellC]
  rw [this]
  exact (measurableSet_singleton 0).compl.inter (measurableSet_Icc.preimage (by fun_prop))

theorem zero_notMem_logShellR (a b : ℝ) : (0 : ℝ) ∉ logShellR a b := fun h => h.1 rfl

theorem zero_notMem_logShellC (a b : ℝ) : (0 : ℂ) ∉ logShellC a b := fun h => h.1 rfl

/-- $\int_{[e^a,e^b]}dx/|x| = \max(0,b-a)$. -/
theorem lintegral_Icc_exp_inv (a b : ℝ) :
    ∫⁻ x in Icc (Real.exp a) (Real.exp b), ENNReal.ofReal |x|⁻¹ = ENNReal.ofReal (max 0 (b - a)) := by
  rcases lt_or_ge a b with h | h
  · rw [setLIntegral_congr Ioo_ae_eq_Icc.symm, lintegral_Ioo_inv (Real.exp_pos a) (Real.exp_lt_exp.2 h),
      ← Real.exp_sub, Real.log_exp, max_eq_right (by linarith)]
  · have h0 : volume (Icc (Real.exp a) (Real.exp b)) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.2 (by linarith [Real.exp_le_exp.2 h])
    rw [setLIntegral_measure_zero _ _ h0, max_eq_left (by linarith)]
    simp

/-- The set $\{x : \log|x|\in[a,b]\}$ is the union of $[e^a,e^b]$ and its negative. -/
theorem logShellR_eq (a b : ℝ) : logShellR a b = Icc (-Real.exp b) (-Real.exp a) ∪ Icc (Real.exp a) (Real.exp b) := by
  ext x
  simp only [logShellR, mem_ofPred_eq, mem_union, mem_Icc]
  constructor
  · rintro ⟨hx, h1, h2⟩
    have hpos : 0 < |x| := abs_pos.2 hx
    have h1' : Real.exp a ≤ |x| := (Real.le_log_iff_exp_le hpos).1 h1
    have h2' : |x| ≤ Real.exp b := (Real.log_le_iff_le_exp hpos).1 h2
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at h1' h2'; exact Or.inr ⟨h1', h2'⟩
    · rw [abs_of_nonpos h] at h1' h2'; exact Or.inl ⟨by linarith, by linarith⟩
  · have hea := Real.exp_pos a
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hx : x < 0 := by linarith
      have hpos : 0 < |x| := abs_pos.2 hx.ne
      rw [abs_of_neg hx] at hpos ⊢
      exact ⟨hx.ne, (Real.le_log_iff_exp_le hpos).2 (by linarith), (Real.log_le_iff_le_exp hpos).2 (by linarith)⟩
    · have hx : 0 < x := by linarith
      rw [abs_of_pos hx]
      exact ⟨hx.ne', (Real.le_log_iff_exp_le hx).2 h1, (Real.log_le_iff_le_exp hx).2 h2⟩

/-- **The real shell integral**: $\int_{\log|x|\in[a,b]}dx/|x| = 2\max(0,b-a)$. -/
theorem lintegral_logShellR (a b : ℝ) :
    ∫⁻ x in logShellR a b, ENNReal.ofReal |x|⁻¹ = ENNReal.ofReal (2 * max 0 (b - a)) := by
  have hea := Real.exp_pos a
  have hdisj : Disjoint (Icc (-Real.exp b) (-Real.exp a)) (Icc (Real.exp a) (Real.exp b)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]
  have hneg : ∫⁻ x in Icc (-Real.exp b) (-Real.exp a), ENNReal.ofReal |x|⁻¹ =
      ∫⁻ x in Icc (Real.exp a) (Real.exp b), ENNReal.ofReal |x|⁻¹ := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun x : ℝ => ENNReal.ofReal |x|⁻¹) (Icc (Real.exp a) (Real.exp b))
    rw [← this]
    have e : (fun x : ℝ => -x) ⁻¹' Icc (Real.exp a) (Real.exp b) = Icc (-Real.exp b) (-Real.exp a) := by
      ext x; simp only [mem_preimage, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [abs_neg]
    rw [e]
  rw [logShellR_eq, lintegral_union measurableSet_Icc hdisj, hneg, lintegral_Icc_exp_inv, ← two_mul,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]

/-- **Radial integrals over $\mathbb C$**: $\int_{\mathbb C}g(\|z\|)\,d^2z = 2\pi\int_0^\infty g(r)\,r\,dr$. -/
theorem lintegral_complex_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z : ℂ, g ‖z‖ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hT : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  rw [hT]
  have h1 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ = ENNReal.ofReal p.1 * g p.1 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h1, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
  rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  congr 2
  ring

/-- **The complex shell integral**: $\int_{\log\|z\|\in[a,b]}d^2z/\|z\|^2 = 2\pi\max(0,b-a)$. -/
theorem lintegral_logShellC (a b : ℝ) :
    ∫⁻ z in logShellC a b, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ = ENNReal.ofReal (2 * Real.pi * max 0 (b - a)) := by
  set g : ℝ → ℝ≥0∞ := (logShellR a b).indicator fun r => ENNReal.ofReal (r ^ 2)⁻¹ with hg
  have hgm : Measurable g := by
    refine Measurable.indicator ?_ (measurableSet_logShellR a b)
    exact Measurable.ennreal_ofReal ((measurable_id.pow_const 2).inv)
  have h1 : ∫⁻ z in logShellC a b, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ = ∫⁻ z : ℂ, g ‖z‖ := by
    rw [← lintegral_indicator (measurableSet_logShellC a b)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ logShellC a b
    · have hz' : ‖z‖ ∈ logShellR a b := ⟨norm_ne_zero_iff.2 hz.1, by simpa [abs_norm] using hz.2.1,
        by simpa [abs_norm] using hz.2.2⟩
      rw [indicator_of_mem hz, hg, indicator_of_mem hz']
    · have hz' : ‖z‖ ∉ logShellR a b := fun h => hz ⟨norm_ne_zero_iff.1 h.1, by simpa [abs_norm] using h.2.1,
        by simpa [abs_norm] using h.2.2⟩
      rw [indicator_of_notMem hz, hg, indicator_of_notMem hz']
  rw [h1, lintegral_complex_radial g hgm]
  have h2 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r =
      ∫⁻ r in logShellR a b ∩ Ioi 0, ENNReal.ofReal |r|⁻¹ := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator
      ((measurableSet_logShellR a b).inter measurableSet_Ioi)]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ logShellR a b ∩ Ioi 0
    · rw [indicator_of_mem hr.2, indicator_of_mem hr, hg, indicator_of_mem hr.1, ← ENNReal.ofReal_mul hr.2.out.le,
        abs_of_pos hr.2]
      congr 1
      have := hr.2.out.ne'
      field_simp
    · by_cases h0 : 0 < r
      · have : r ∉ logShellR a b := fun h => hr ⟨h, h0⟩
        rw [indicator_of_notMem hr, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from h0), hg, indicator_of_notMem this,
          mul_zero]
      · rw [indicator_of_notMem hr, indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from h0)]
  have h3 : logShellR a b ∩ Ioi 0 = Icc (Real.exp a) (Real.exp b) := by
    ext x
    rw [logShellR_eq]
    simp only [mem_inter_iff, mem_union, mem_Icc, mem_Ioi]
    have hea := Real.exp_pos a
    constructor
    · rintro ⟨h | h, hx⟩
      · linarith [h.2]
      · exact h
    · intro h
      exact ⟨Or.inr h, by linarith [h.1]⟩
  rw [h2, h3, lintegral_Icc_exp_inv, ← ENNReal.ofReal_mul (by positivity)]

end OneVariable

/-! ### The shell over the places of $E$ -/

section Shell

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

/-- The real shell $\{x\in\mathbb R : 1\le|x|\le e\}$. -/
def shellOneR : Set ℝ := {x | |x| ∈ Icc 1 (Real.exp 1)}

/-- The complex shell $\{z\in\mathbb C : 1\le\|z\|^2\le e\}$ ($\|z\|^2$ is the normalized absolute value at a complex place). -/
def shellOneC : Set ℂ := {z | ‖z‖ ^ 2 ∈ Icc 1 (Real.exp 1)}

theorem shellR_eq : shellOneR = logShellR 0 1 := by
  ext x
  simp only [shellOneR, logShellR, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < |x| := by linarith
    exact ⟨abs_pos.1 hpos, Real.log_nonneg h1, (Real.log_le_iff_le_exp hpos).2 h2⟩
  · rintro ⟨hx, h1, h2⟩
    have hpos : 0 < |x| := abs_pos.2 hx
    exact ⟨by simpa using (Real.le_log_iff_exp_le hpos).1 h1, (Real.log_le_iff_le_exp hpos).1 h2⟩

theorem shellC_eq : shellOneC = logShellC 0 (1 / 2) := by
  ext z
  simp only [shellOneC, logShellC, mem_ofPred_eq, mem_Icc]
  have hs : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : 1 ≤ ‖z‖ := by
      by_contra h
      push Not at h
      nlinarith [norm_nonneg z]
    have hpos : 0 < ‖z‖ := by linarith
    have h2' : ‖z‖ ≤ Real.exp (1 / 2) := by
      rw [← hs] at h2
      exact (sq_le_sq₀ (norm_nonneg z) (Real.exp_pos _).le).1 h2
    exact ⟨norm_pos_iff.1 hpos, Real.log_nonneg h1', (Real.log_le_iff_le_exp hpos).2 h2'⟩
  · rintro ⟨hx, h1, h2⟩
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hx
    have h1' : 1 ≤ ‖z‖ := by simpa using (Real.le_log_iff_exp_le hpos).1 h1
    have h2' : ‖z‖ ≤ Real.exp (1 / 2) := (Real.log_le_iff_le_exp hpos).1 h2
    refine ⟨by nlinarith, ?_⟩
    rw [← hs]
    exact (sq_le_sq₀ (norm_nonneg z) (Real.exp_pos _).le).2 h2'

variable (E : Type) [Field E] [NumberField E]

/-- **The shell over the places of $E$**: $\{y\in(E_\infty)^\times : 1\le|y_W|\le e$ at the real places $W$,
$1\le\|y_W\|^2\le e$ at the complex places $W\}$. -/
def shellE : Set (mixedSpace E)ˣ :=
  Units.val ⁻¹' infBoxSet (fun _ : {w : InfinitePlace E // w.IsReal} => shellOneR)
    (fun _ : {w : InfinitePlace E // w.IsComplex} => shellOneC)

/-- **$\omega_{\infty,E}$ of the shell**: $2^{r_2(E)}\cdot2^{r_1(E)}\cdot\pi^{r_2(E)}$ (real factor
$\int_{1\le|x|\le e}dx/|x| = 2$, complex factor $\int_{1\le\|z\|^2\le e}d^2z/\|z\|^2 = \pi$). -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors) [unverified]"]
theorem omegaInf_shellE : omegaInf E (shellE E) =
    (2 : ℝ≥0∞) ^ nrComplexPlaces E * ((2 : ℝ≥0∞) ^ nrRealPlaces E * ENNReal.ofReal Real.pi ^ nrComplexPlaces E) := by
  rw [shellE, omegaInf_box (fun _ => by rw [shellR_eq]; exact measurableSet_logShellR 0 1)
    (fun _ => by rw [shellC_eq]; exact measurableSet_logShellC 0 (1 / 2))
    (fun _ => by rw [shellR_eq]; exact zero_notMem_logShellR 0 1)
    (fun _ => by rw [shellC_eq]; exact zero_notMem_logShellC 0 (1 / 2))]
  have h1 : ∫⁻ x in shellOneR, ENNReal.ofReal |x|⁻¹ = 2 := by
    rw [shellR_eq, lintegral_logShellR]
    norm_num
  have h2 : ∫⁻ z in shellOneC, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ = ENNReal.ofReal Real.pi := by
    rw [shellC_eq, lintegral_logShellC]
    congr 1
    norm_num
    ring
  simp only [h1, h2, Finset.prod_const, Finset.card_univ]

end Shell

/-! ### Components of the base change at the infinite places of $E$ -/

section Components

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {d : F}
  {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E d)

/-- At a real place $W$ of $E$: $\iota(t)_W = t_{W|_F}$. -/
theorem infRingHom_fst_apply (t : mixedSpace F) (W : {W : InfinitePlace E // W.IsReal}) :
    (infRingHom F E t).1 W = t.1 ⟨W.1.comap (algebraMap F E), IsReal.comap _ W.2⟩ :=
  adeleMap_fst_fst (k := F) (K := E) (t, 0) W

/-- At a complex place $W$ of $E$ over a real place of $F$: $\iota(t)_W = t_{W|_F}$ (as a complex number). -/
theorem infRingHom_snd_apply_of_real (t : mixedSpace F) (W : {W : InfinitePlace E // W.IsComplex})
    (hv : (W.1.comap (algebraMap F E)).IsReal) :
    (infRingHom F E t).2 W = ((t.1 ⟨W.1.comap (algebraMap F E), hv⟩ : ℝ) : ℂ) :=
  adeleMap_fst_snd_of_isReal_comap (F := F) (K := E) (t, 0) W hv

/-- At a complex place $W$ of $E$ over a complex place of $F$: $\|\iota(t)_W\| = \|t_{W|_F}\|$. -/
theorem norm_infRingHom_snd_of_complex (t : mixedSpace F) (W : {W : InfinitePlace E // W.IsComplex})
    (hv : (W.1.comap (algebraMap F E)).IsComplex) :
    ‖(infRingHom F E t).2 W‖ = ‖t.2 ⟨W.1.comap (algebraMap F E), hv⟩‖ := by
  rcases (embedding_comp_eq_or_conj W.1 hv).1 with h | h
  · have e : (infRingHom F E t).2 W = t.2 ⟨W.1.comap (algebraMap F E), hv⟩ :=
      adeleMap_fst_snd_of_comp_eq (F := F) (K := E) (t, 0) W hv h
    rw [e]
  · have e : (infRingHom F E t).2 W = starRingEnd ℂ (t.2 ⟨W.1.comap (algebraMap F E), hv⟩) :=
      adeleMap_fst_snd_of_comp_eq_conj (F := F) (K := E) (t, 0) W hv h
    rw [e]
    simp

/-- The real components of $x + y\omega\mapsto\iota(x) + \delta\,\iota(y)$. -/
theorem quadInfBC_fst_apply (z : QuadInf F d) (W : {W : InfinitePlace E // W.IsReal}) :
    (quadInfBC hb1 z).1 W = z.re.1 ⟨W.1.comap (algebraMap F E), IsReal.comap _ W.2⟩ +
      embedding_of_isReal W.2 (b 1) * z.im.1 ⟨W.1.comap (algebraMap F E), IsReal.comap _ W.2⟩ := by
  change (infRingHom F E z.re + mixedEmbedding E (b 1) * infRingHom F E z.im).1 W = _
  simp only [Prod.fst_add, Prod.fst_mul, Pi.add_apply, Pi.mul_apply, infRingHom_fst_apply,
    mixedEmbedding_apply_isReal]

/-- The complex components over a real place of $F$. -/
theorem quadInfBC_snd_apply_of_real (z : QuadInf F d) (W : {W : InfinitePlace E // W.IsComplex})
    (hv : (W.1.comap (algebraMap F E)).IsReal) :
    (quadInfBC hb1 z).2 W = ((z.re.1 ⟨W.1.comap (algebraMap F E), hv⟩ : ℝ) : ℂ) +
      W.1.embedding (b 1) * ((z.im.1 ⟨W.1.comap (algebraMap F E), hv⟩ : ℝ) : ℂ) := by
  change (infRingHom F E z.re + mixedEmbedding E (b 1) * infRingHom F E z.im).2 W = _
  simp only [Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, infRingHom_snd_apply_of_real _ _ hv,
    mixedEmbedding_apply_isComplex]

open Classical in
variable (F) in
/-- **The oriented embedding** of a complex place $W$ of $E$ over a complex place $v$ of $F$: the one of
$W.\mathrm{embedding}$, $\overline{W.\mathrm{embedding}}$ that restricts to the chosen embedding of $v$ on $F$. -/
def orientEmb (W : {W : InfinitePlace E // W.IsComplex}) : E →+* ℂ :=
  if W.1.embedding.comp (algebraMap F E) = (W.1.comap (algebraMap F E)).embedding then W.1.embedding
  else ComplexEmbedding.conjugate W.1.embedding

theorem orientEmb_comp (W : {W : InfinitePlace E // W.IsComplex}) (hv : (W.1.comap (algebraMap F E)).IsComplex) :
    (orientEmb F W).comp (algebraMap F E) = (W.1.comap (algebraMap F E)).embedding := by
  unfold orientEmb
  split_ifs with h
  · exact h
  · have h2 := ((embedding_comp_eq_or_conj W.1 hv).1).resolve_left h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h2
    simp only [RingHom.comp_apply] at this ⊢
    simp [ComplexEmbedding.conjugate, this]

theorem mk_orientEmb (W : {W : InfinitePlace E // W.IsComplex}) : mk (orientEmb F W) = W.1 := by
  unfold orientEmb
  split_ifs with h
  · exact mk_embedding W.1
  · rw [mk_conjugate_eq, mk_embedding]

include hb1 in
theorem orientEmb_delta_sq (W : {W : InfinitePlace E // W.IsComplex}) (hv : (W.1.comap (algebraMap F E)).IsComplex) :
    (orientEmb F W (b 1)) ^ 2 = (W.1.comap (algebraMap F E)).embedding d := by
  rw [sq_delta_emb b hb1, ← RingHom.comp_apply, orientEmb_comp W hv]

/-- The norm of the component at a complex place $W$ over a complex place $v$ of $F$. -/
theorem norm_quadInfBC_snd_of_complex (z : QuadInf F d) (W : {W : InfinitePlace E // W.IsComplex})
    (hv : (W.1.comap (algebraMap F E)).IsComplex) :
    ‖(quadInfBC hb1 z).2 W‖ = ‖z.re.2 ⟨W.1.comap (algebraMap F E), hv⟩ +
      orientEmb F W (b 1) * z.im.2 ⟨W.1.comap (algebraMap F E), hv⟩‖ := by
  have hQ : (quadInfBC hb1 z).2 W = (infRingHom F E z.re).2 W + W.1.embedding (b 1) * (infRingHom F E z.im).2 W := by
    change (infRingHom F E z.re + mixedEmbedding E (b 1) * infRingHom F E z.im).2 W = _
    simp only [Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, mixedEmbedding_apply_isComplex]
  rw [hQ]
  unfold orientEmb
  split_ifs with h
  · have e1 : (infRingHom F E z.re).2 W = z.re.2 ⟨W.1.comap (algebraMap F E), hv⟩ :=
      adeleMap_fst_snd_of_comp_eq (F := F) (K := E) (z.re, 0) W hv h
    have e2 : (infRingHom F E z.im).2 W = z.im.2 ⟨W.1.comap (algebraMap F E), hv⟩ :=
      adeleMap_fst_snd_of_comp_eq (F := F) (K := E) (z.im, 0) W hv h
    rw [e1, e2]
  · have h' := ((embedding_comp_eq_or_conj W.1 hv).1).resolve_left h
    have e1 : (infRingHom F E z.re).2 W = starRingEnd ℂ (z.re.2 ⟨W.1.comap (algebraMap F E), hv⟩) :=
      adeleMap_fst_snd_of_comp_eq_conj (F := F) (K := E) (z.re, 0) W hv h'
    have e2 : (infRingHom F E z.im).2 W = starRingEnd ℂ (z.im.2 ⟨W.1.comap (algebraMap F E), hv⟩) :=
      adeleMap_fst_snd_of_comp_eq_conj (F := F) (K := E) (z.im, 0) W hv h'
    rw [e1, e2]
    have : starRingEnd ℂ (z.re.2 ⟨W.1.comap (algebraMap F E), hv⟩) +
        W.1.embedding (b 1) * starRingEnd ℂ (z.im.2 ⟨W.1.comap (algebraMap F E), hv⟩) =
        starRingEnd ℂ (z.re.2 ⟨W.1.comap (algebraMap F E), hv⟩ +
          (ComplexEmbedding.conjugate W.1.embedding) (b 1) * z.im.2 ⟨W.1.comap (algebraMap F E), hv⟩) := by
      simp [ComplexEmbedding.conjugate]
    rw [this, RCLike.norm_conj]

include hb1 in
/-- **Two distinct complex places of $E$ over a complex place of $F$ have opposite $\delta$-values** (oriented). -/
theorem orientEmb_delta_neg [Module.Finite F E] (hb0 : b 0 = 1) {W₁ W₂ : {W : InfinitePlace E // W.IsComplex}}
    (hne : W₁ ≠ W₂) (hv : (W₁.1.comap (algebraMap F E)).IsComplex) (h12 : W₂.1.comap (algebraMap F E) = W₁.1.comap (algebraMap F E)) :
    orientEmb F W₂ (b 1) = - orientEmb F W₁ (b 1) := by
  have hv2 : (W₂.1.comap (algebraMap F E)).IsComplex := h12 ▸ hv
  have hsq : (orientEmb F W₂ (b 1)) ^ 2 = (orientEmb F W₁ (b 1)) ^ 2 := by
    rw [orientEmb_delta_sq hb1 W₁ hv, orientEmb_delta_sq hb1 W₂ hv2, h12]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exfalso
    apply hne
    have hφ : orientEmb F W₂ = orientEmb F W₁ := by
      refine hom_ext_delta b hb0 _ _ (fun a => ?_) h
      have e1 := congrArg (fun f : F →+* ℂ => f a) (orientEmb_comp W₁ hv)
      have e2 := congrArg (fun f : F →+* ℂ => f a) (orientEmb_comp W₂ hv2)
      simp only [RingHom.comp_apply] at e1 e2
      rw [e1, e2, h12]
    apply Subtype.ext
    rw [← mk_orientEmb (F := F) W₁, ← mk_orientEmb (F := F) W₂, hφ]
  · exact h

/-- At a complex place $W$ of $E$ over a real place of $F$: $\|\iota(t)_W\| = |t_{W|_F}|$. -/
theorem norm_infRingHom_snd_of_real (t : mixedSpace F) (W : {W : InfinitePlace E // W.IsComplex})
    (hv : (W.1.comap (algebraMap F E)).IsReal) :
    ‖(infRingHom F E t).2 W‖ = |t.1 ⟨W.1.comap (algebraMap F E), hv⟩| := by
  rw [infRingHom_snd_apply_of_real t W hv, Complex.norm_real, Real.norm_eq_abs]

end Components

/-! ### The fibre of the shell is a box over the places of $F$ -/

section FibreBox

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-- The conditions at a real place $w$ of $F$ on $r\in\mathbb R^\times = F_w^\times$ for $y\,\iota(c)$ to lie in the shell:
$1\le|y_Wr|\le e$ at the real places $W\mid w$ and $1\le(\|y_W\|\,|r|)^2\le e$ at the complex places $W\mid w$ of $E$. -/
def fibPR (y : mixedSpace E) (w : {w : InfinitePlace F // w.IsReal}) : Set ℝ :=
  {r | (∀ W : {W : InfinitePlace E // W.IsReal}, W.1.comap (algebraMap F E) = w.1 →
      |y.1 W * r| ∈ Icc 1 (Real.exp 1)) ∧
    ∀ W : {W : InfinitePlace E // W.IsComplex}, W.1.comap (algebraMap F E) = w.1 →
      (‖y.2 W‖ * |r|) ^ 2 ∈ Icc 1 (Real.exp 1)}

/-- The conditions at a complex place $w$ of $F$ on $z\in\mathbb C^\times = F_w^\times$: $1\le(\|y_W\|\,\|z\|)^2\le e$ at the
(complex) places $W\mid w$ of $E$. -/
def fibPC (y : mixedSpace E) (w : {w : InfinitePlace F // w.IsComplex}) : Set ℂ :=
  {z | ∀ W : {W : InfinitePlace E // W.IsComplex}, W.1.comap (algebraMap F E) = w.1 →
    (‖y.2 W‖ * ‖z‖) ^ 2 ∈ Icc 1 (Real.exp 1)}

/-- **The fibre of the shell is a box over the places of $F$.** -/
theorem fibre_set_eq (y : (mixedSpace E)ˣ) :
    {c : (mixedSpace F)ˣ | y * Units.map (infRingHom F E).toMonoidHom c ∈ shellE E} =
      Units.val ⁻¹' infBoxSet (fibPR (y : mixedSpace E)) (fibPC (y : mixedSpace E)) := by
  ext c
  simp only [mem_ofPred_eq, mem_preimage, shellE, infBoxSet, shellOneR, shellOneC, Units.val_mul,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, abs_mul, fibPR, fibPC]
  constructor
  · rintro ⟨hR, hC⟩
    refine ⟨fun w => ⟨fun W hW => ?_, fun W hW => ?_⟩, fun w W hW => ?_⟩
    · have h := hR W
      rw [infRingHom_fst_apply] at h
      have e : (⟨W.1.comap (algebraMap F E), IsReal.comap _ W.2⟩ : {w : InfinitePlace F // w.IsReal}) = w :=
        Subtype.ext hW
      rwa [e] at h
    · have hv : (W.1.comap (algebraMap F E)).IsReal := hW ▸ w.2
      have h := hC W
      rw [norm_infRingHom_snd_of_real _ _ hv] at h
      have e : (⟨W.1.comap (algebraMap F E), hv⟩ : {w : InfinitePlace F // w.IsReal}) = w := Subtype.ext hW
      rwa [e] at h
    · have hv : (W.1.comap (algebraMap F E)).IsComplex := hW ▸ w.2
      have h := hC W
      rw [norm_infRingHom_snd_of_complex _ _ hv] at h
      have e : (⟨W.1.comap (algebraMap F E), hv⟩ : {w : InfinitePlace F // w.IsComplex}) = w := Subtype.ext hW
      rwa [e] at h
  · rintro ⟨hR, hC⟩
    refine ⟨fun W => ?_, fun W => ?_⟩
    · have h := (hR ⟨W.1.comap (algebraMap F E), IsReal.comap _ W.2⟩).1 W rfl
      rwa [infRingHom_fst_apply]
    · rcases (W.1.comap (algebraMap F E)).isReal_or_isComplex with hv | hv
      · have h := (hR ⟨_, hv⟩).2 W rfl
        rwa [norm_infRingHom_snd_of_real _ _ hv]
      · have h := hC ⟨_, hv⟩ W rfl
        rwa [norm_infRingHom_snd_of_complex _ _ hv]

end FibreBox

/-! ### The fibre conditions are logarithmic shells -/

section FibreShells

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

theorem sq_mem_Icc_iff {x : ℝ} (hx : 0 < x) :
    x ^ 2 ∈ Icc 1 (Real.exp 1) ↔ 0 ≤ Real.log x ∧ Real.log x ≤ 1 / 2 := by
  have hs : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  simp only [mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : 1 ≤ x := by
      by_contra h
      push Not at h
      nlinarith
    have h2' : x ≤ Real.exp (1 / 2) := by
      rw [← hs] at h2
      exact (sq_le_sq₀ hx.le (Real.exp_pos _).le).1 h2
    exact ⟨Real.log_nonneg h1', (Real.log_le_iff_le_exp hx).2 h2'⟩
  · rintro ⟨h1, h2⟩
    have h1' : 1 ≤ x := (Real.log_nonneg_iff hx).1 h1
    have h2' : x ≤ Real.exp (1 / 2) := (Real.log_le_iff_le_exp hx).1 h2
    refine ⟨by nlinarith, ?_⟩
    rw [← hs]
    exact (sq_le_sq₀ hx.le (Real.exp_pos _).le).2 h2'

theorem mem_Icc_one_exp_iff {x : ℝ} (hx : 0 < x) : x ∈ Icc 1 (Real.exp 1) ↔ 0 ≤ Real.log x ∧ Real.log x ≤ 1 := by
  rw [mem_Icc, Real.log_nonneg_iff hx, Real.log_le_iff_le_exp hx]

theorem core_one {p u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    p * u ∈ Icc 1 (Real.exp 1) ↔ -Real.log p ≤ Real.log u ∧ Real.log u ≤ 1 - Real.log p := by
  rw [mem_Icc_one_exp_iff (mul_pos hp hu), Real.log_mul hp.ne' hu.ne']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem core_two {p u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    (p * u) ^ 2 ∈ Icc 1 (Real.exp 1) ↔ -Real.log p ≤ Real.log u ∧ Real.log u ≤ 1 / 2 - Real.log p := by
  rw [sq_mem_Icc_iff (mul_pos hp hu), Real.log_mul hp.ne' hu.ne']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem min_sub_max_aux (c α β : ℝ) : min (c - α) (c - β) - max (-α) (-β) = c - |α - β| := by
  rcases le_total α β with h | h
  · rw [max_eq_left (by linarith), min_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_right (by linarith), min_eq_left (by linarith), abs_of_nonneg (by linarith)]; ring

/-- Two real places $W_1,W_2$ over $w$: the fibre is a logarithmic shell. -/
theorem logShell_pair_real {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    {r : ℝ | |p * r| ∈ Icc 1 (Real.exp 1) ∧ |q * r| ∈ Icc 1 (Real.exp 1)} =
      logShellR (max (-Real.log |p|) (-Real.log |q|)) (min (1 - Real.log |p|) (1 - Real.log |q|)) := by
  ext r
  simp only [mem_ofPred_eq, logShellR, max_le_iff, le_min_iff]
  by_cases hr : r = 0
  · subst hr
    simp
  · have hu : 0 < |r| := abs_pos.2 hr
    have hp' : 0 < |p| := abs_pos.2 hp
    have hq' : 0 < |q| := abs_pos.2 hq
    rw [abs_mul, abs_mul, core_one hp' hu, core_one hq' hu]
    simp only [ne_eq, hr, not_false_eq_true, true_and]
    tauto

/-- One complex place $W$ over a real place: the fibre is a logarithmic shell. -/
theorem logShell_single_complex_real {ρ : ℝ} (hρ : 0 < ρ) :
    {r : ℝ | (ρ * |r|) ^ 2 ∈ Icc 1 (Real.exp 1)} = logShellR (-Real.log ρ) (1 / 2 - Real.log ρ) := by
  ext r
  simp only [mem_ofPred_eq, logShellR]
  by_cases hr : r = 0
  · subst hr
    simp
  · have hu : 0 < |r| := abs_pos.2 hr
    rw [core_two hρ hu]
    simp [hr]

/-- Two complex places over a complex place: the fibre is a logarithmic shell. -/
theorem logShell_pair_complex {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) :
    {z : ℂ | (ρ₁ * ‖z‖) ^ 2 ∈ Icc 1 (Real.exp 1) ∧ (ρ₂ * ‖z‖) ^ 2 ∈ Icc 1 (Real.exp 1)} =
      logShellC (max (-Real.log ρ₁) (-Real.log ρ₂)) (min (1 / 2 - Real.log ρ₁) (1 / 2 - Real.log ρ₂)) := by
  ext z
  simp only [mem_ofPred_eq, logShellC, max_le_iff, le_min_iff]
  by_cases hz : z = 0
  · subst hz
    simp
  · have hu : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [core_two h1 hu, core_two h2 hu]
    simp only [ne_eq, hz, not_false_eq_true, true_and]
    tauto

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem fibPR_two_real (y : mixedSpace E) (w : {w : InfinitePlace F // w.IsReal})
    (W₁ W₂ : {W : InfinitePlace E // W.IsReal}) (h1 : W₁.1.comap (algebraMap F E) = w.1)
    (h2 : W₂.1.comap (algebraMap F E) = w.1)
    (hall : ∀ W : InfinitePlace E, W.comap (algebraMap F E) = w.1 → W = W₁.1 ∨ W = W₂.1)
    (hcx : ∀ W : {W : InfinitePlace E // W.IsComplex}, W.1.comap (algebraMap F E) ≠ w.1)
    (hy1 : y.1 W₁ ≠ 0) (hy2 : y.1 W₂ ≠ 0) :
    fibPR y w = logShellR (max (-Real.log |y.1 W₁|) (-Real.log |y.1 W₂|))
      (min (1 - Real.log |y.1 W₁|) (1 - Real.log |y.1 W₂|)) := by
  rw [← logShell_pair_real hy1 hy2]
  ext r
  simp only [fibPR, mem_ofPred_eq]
  constructor
  · rintro ⟨hR, -⟩
    exact ⟨hR W₁ h1, hR W₂ h2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨fun W hW => ?_, fun W hW => (hcx W hW).elim⟩
    rcases hall W.1 hW with h | h
    · rwa [show W = W₁ from Subtype.ext h]
    · rwa [show W = W₂ from Subtype.ext h]

theorem fibPR_one_complex (y : mixedSpace E) (w : {w : InfinitePlace F // w.IsReal})
    (W : {W : InfinitePlace E // W.IsComplex}) (h : W.1.comap (algebraMap F E) = w.1)
    (hall : ∀ W' : InfinitePlace E, W'.comap (algebraMap F E) = w.1 → W' = W.1)
    (hre : ∀ W' : {W : InfinitePlace E // W.IsReal}, W'.1.comap (algebraMap F E) ≠ w.1)
    (hy : y.2 W ≠ 0) :
    fibPR y w = logShellR (-Real.log ‖y.2 W‖) (1 / 2 - Real.log ‖y.2 W‖) := by
  rw [← logShell_single_complex_real (norm_pos_iff.2 hy)]
  ext r
  simp only [fibPR, mem_ofPred_eq]
  constructor
  · rintro ⟨-, hC⟩
    exact hC W h
  · intro hr
    refine ⟨fun W' hW' => (hre W' hW').elim, fun W' hW' => ?_⟩
    rwa [show W' = W from Subtype.ext (hall W'.1 hW')]

theorem fibPC_two (y : mixedSpace E) (w : {w : InfinitePlace F // w.IsComplex})
    (W₁ W₂ : {W : InfinitePlace E // W.IsComplex}) (h1 : W₁.1.comap (algebraMap F E) = w.1)
    (h2 : W₂.1.comap (algebraMap F E) = w.1)
    (hall : ∀ W : InfinitePlace E, W.comap (algebraMap F E) = w.1 → W = W₁.1 ∨ W = W₂.1)
    (hy1 : y.2 W₁ ≠ 0) (hy2 : y.2 W₂ ≠ 0) :
    fibPC y w = logShellC (max (-Real.log ‖y.2 W₁‖) (-Real.log ‖y.2 W₂‖))
      (min (1 / 2 - Real.log ‖y.2 W₁‖) (1 / 2 - Real.log ‖y.2 W₂‖)) := by
  rw [← logShell_pair_complex (norm_pos_iff.2 hy1) (norm_pos_iff.2 hy2)]
  ext z
  simp only [fibPC, mem_ofPred_eq]
  constructor
  · intro hC
    exact ⟨hC W₁ h1, hC W₂ h2⟩
  · rintro ⟨ha, hb⟩ W hW
    rcases hall W.1 hW with h | h
    · rwa [show W = W₁ from Subtype.ext h]
    · rwa [show W = W₂ from Subtype.ext h]

end FibreShells

/-! ### The torus coordinate of $\mathrm{tor}(z)$ -/

section TorCoords

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

/-- **The torus coordinate**: for $s^2 = d$ and a unit $z = x + y\omega$ of $K[\omega]$ ($\omega^2 = d$),
$p(z) + s\,q(z) = (x + sy)/(x - sy)$, the value of $u(z) = z/\bar z$ at the place $\omega\mapsto s$. -/
theorem torP_add_mul_torQ {K : Type*} [Field K] {d s : K} (hs : s * s = d) (z : (QuadraticAlgebra K d 0)ˣ) :
    (z : QuadraticAlgebra K d 0).re + s * (z : QuadraticAlgebra K d 0).im ≠ 0 ∧
    (z : QuadraticAlgebra K d 0).re - s * (z : QuadraticAlgebra K d 0).im ≠ 0 ∧
    torP (z : QuadraticAlgebra K d 0) + s * torQ (z : QuadraticAlgebra K d 0) =
      ((z : QuadraticAlgebra K d 0).re + s * (z : QuadraticAlgebra K d 0).im) /
        ((z : QuadraticAlgebra K d 0).re - s * (z : QuadraticAlgebra K d 0).im) := by
  subst hs
  have hN := norm_ne_zero_of_unit z
  rw [norm_eq] at hN
  have hfac : (z : QuadraticAlgebra K (s * s) 0).re * (z : QuadraticAlgebra K (s * s) 0).re -
      (s * s) * (z : QuadraticAlgebra K (s * s) 0).im * (z : QuadraticAlgebra K (s * s) 0).im =
      ((z : QuadraticAlgebra K (s * s) 0).re + s * (z : QuadraticAlgebra K (s * s) 0).im) *
        ((z : QuadraticAlgebra K (s * s) 0).re - s * (z : QuadraticAlgebra K (s * s) 0).im) := by
    ring
  rw [hfac] at hN
  have hA := left_ne_zero_of_mul hN
  have hB := right_ne_zero_of_mul hN
  refine ⟨hA, hB, ?_⟩
  unfold torP torQ
  rw [norm_eq, hfac]
  field_simp
  ring

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

/-- The coordinate $x_{00} + \sqrt\delta\,x_{10}$ of an element of $SO(Q)(\mathbb R)$ for a real binary form $Q$ (the same
formula as `splitCoord`, for an arbitrary form). -/
def splitCoordG (δ : ℝ) {Q : QuadForm ℝ 2} (x : ArchSO Q) : ℝ :=
  ArchSOInst.mat Q x 0 0 + Real.sqrt δ * ArchSOInst.mat Q x 1 0

/-- The coordinate $x_{00} + s\,x_{10}$ of an element of $SO(Q)(\mathbb C)$ for a complex binary form $Q$ (the same formula as
`complexCoord`, for an arbitrary form). -/
def complexCoordG (s : ℂ) {Q : QuadForm ℂ 2} (x : ArchSOC Q) : ℂ :=
  ArchSOC.mat Q x 0 0 + s * ArchSOC.mat Q x 1 0

theorem splitCoordG_diag (δ : ℝ) (x : ArchSO (QuadForm.diag ![1, -δ])) : splitCoordG δ x = splitCoord δ x := rfl

theorem complexCoordG_diag (D s : ℂ) (x : ArchSOC (QuadForm.diag ![1, D])) : complexCoordG s x = complexCoord D s x :=
  rfl

theorem mat_torR_zero_zero (w : {w : InfinitePlace F // w.IsReal}) (z : (QuadInf F (dD D))ˣ) :
    ArchSOInst.mat _ (torR D w z) 0 0 = torP (projQR (dD D) w (z : QuadInf F (dD D))) := by
  change (ArchSO.incl _ (torR D w z) : GL (Fin 2) ℝ).val 0 0 = _
  rw [torR_incl, torGLK_val]
  simp [rotMat]

theorem mat_torR_one_zero (w : {w : InfinitePlace F // w.IsReal}) (z : (QuadInf F (dD D))ˣ) :
    ArchSOInst.mat _ (torR D w z) 1 0 = torQ (projQR (dD D) w (z : QuadInf F (dD D))) := by
  change (ArchSO.incl _ (torR D w z) : GL (Fin 2) ℝ).val 1 0 = _
  rw [torR_incl, torGLK_val]
  simp [rotMat]

theorem mat_torC_zero_zero (w : {w : InfinitePlace F // w.IsComplex}) (z : (QuadInf F (dD D))ˣ) :
    ArchSOC.mat _ (torC D w z) 0 0 = torP (projQC (dD D) w (z : QuadInf F (dD D))) := by
  change (ArchSOC.incl _ (torC D w z) : GL (Fin 2) ℂ).val 0 0 = _
  rw [torC_incl, torGLK_val]
  simp [rotMat]

theorem mat_torC_one_zero (w : {w : InfinitePlace F // w.IsComplex}) (z : (QuadInf F (dD D))ˣ) :
    ArchSOC.mat _ (torC D w z) 1 0 = torQ (projQC (dD D) w (z : QuadInf F (dD D))) := by
  change (ArchSOC.incl _ (torC D w z) : GL (Fin 2) ℂ).val 1 0 = _
  rw [torC_incl, torGLK_val]
  simp [rotMat]

/-- **The split coordinate of $\mathrm{tor}(z)$ at a real place** with $\sigma_w(d) > 0$:
$(x + \sqrt\delta\,y)/(x - \sqrt\delta\,y)$ ($x$, $y$ the coordinates of $z$ at $w$). -/
theorem splitCoordG_torR (w : {w : InfinitePlace F // w.IsReal}) (z : (QuadInf F (dD D))ˣ)
    (hσ : 0 < embedding_of_isReal w.2 (dD D)) :
    z.1.re.1 w + Real.sqrt (embedding_of_isReal w.2 (dD D)) * z.1.im.1 w ≠ 0 ∧
    z.1.re.1 w - Real.sqrt (embedding_of_isReal w.2 (dD D)) * z.1.im.1 w ≠ 0 ∧
    splitCoordG (embedding_of_isReal w.2 (dD D)) (torR D w z) =
      (z.1.re.1 w + Real.sqrt (embedding_of_isReal w.2 (dD D)) * z.1.im.1 w) /
        (z.1.re.1 w - Real.sqrt (embedding_of_isReal w.2 (dD D)) * z.1.im.1 w) := by
  have hs : Real.sqrt (embedding_of_isReal w.2 (dD D)) * Real.sqrt (embedding_of_isReal w.2 (dD D)) =
      embedding_of_isReal w.2 (dD D) := Real.mul_self_sqrt hσ.le
  have h := torP_add_mul_torQ hs (Units.map (projQR (dD D) w).toMonoidHom z)
  refine ⟨h.1, h.2.1, ?_⟩
  unfold splitCoordG
  rw [mat_torR_zero_zero, mat_torR_one_zero]
  exact h.2.2

/-- **The coordinate of $\mathrm{tor}(z)$ at a complex place**. -/
theorem complexCoordG_torC (w : {w : InfinitePlace F // w.IsComplex}) (z : (QuadInf F (dD D))ˣ) {s : ℂ}
    (hs : s * s = w.1.embedding (dD D)) :
    z.1.re.2 w + s * z.1.im.2 w ≠ 0 ∧ z.1.re.2 w - s * z.1.im.2 w ≠ 0 ∧
    complexCoordG s (torC D w z) = (z.1.re.2 w + s * z.1.im.2 w) / (z.1.re.2 w - s * z.1.im.2 w) := by
  have h := torP_add_mul_torQ hs (Units.map (projQC (dD D) w).toMonoidHom z)
  refine ⟨h.1, h.2.1, ?_⟩
  unfold complexCoordG
  rw [mat_torC_zero_zero, mat_torC_one_zero]
  exact h.2.2

end TorCoords

/-! ### The weights and the local fibre integrals -/

section Weights

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

/-- **A square root of $\tau_w(d)$** at a complex place $w$ of $F$ (the value of $\delta$ at one of the two places of
$E = F(\delta)$ over $w$, up to complex conjugation), chosen once and for all. -/
def sqrtDC (w : {w : InfinitePlace F // w.IsComplex}) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (w.1.embedding (dD D)) (two_pos : 0 < 2))

theorem sqrtDC_mul_self (w : {w : InfinitePlace F // w.IsComplex}) :
    sqrtDC D w * sqrtDC D w = w.1.embedding (dD D) := by
  rw [← sq]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (w.1.embedding (dD D)) (two_pos : 0 < 2))

open Classical in
/-- **The weight at a real place $w$ of $F$** (the fibre function of the shell, as a function on
$SO(Q^{\sigma_w})(\mathbb R)$, $Q = \langle1,D\rangle$): $2\max(0,\ 1-|\log|t(x)||)$ with $t(x) = x_{00}+\sqrt{\sigma_w(d)}\,x_{10}$
if $\sigma_w(d)>0$ ($w$ splits in $E$), and $1$ if $\sigma_w(d)<0$ ($w$ ramifies to a complex place of $E$). -/
def wReal (w : {w : InfinitePlace F // w.IsReal}) (x : ArchSO (QRe (diagForm1 D) w)) : ℝ≥0∞ :=
  if 0 < embedding_of_isReal w.2 (dD D) then
    ENNReal.ofReal (2 * max 0 (1 - |Real.log (|splitCoordG (embedding_of_isReal w.2 (dD D)) x|)|))
  else 1

/-- **The weight at a complex place $w$ of $F$**: $2\pi\max(0,\ 1-2|\log\|t(x)\||)$, $t(x) = x_{00}+s\,x_{10}$, $s^2 = \tau_w(d)$
(`sqrtDC`). -/
def wCpx (w : {w : InfinitePlace F // w.IsComplex}) (x : ArchSOC (QCx (diagForm1 D) w)) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖complexCoordG (sqrtDC D w) x‖|))

theorem unit_comp_ne_zero {E : Type} [Field E] [NumberField E] (y : (mixedSpace E)ˣ) :
    (∀ W : {W : InfinitePlace E // W.IsReal}, (y : mixedSpace E).1 W ≠ 0) ∧
      ∀ W : {W : InfinitePlace E // W.IsComplex}, (y : mixedSpace E).2 W ≠ 0 := by
  obtain ⟨h1, h2⟩ := Prod.isUnit_iff.1 y.isUnit
  exact ⟨fun W => (Pi.isUnit_iff.1 h1 W).ne_zero, fun W => (Pi.isUnit_iff.1 h2 W).ne_zero⟩

theorem abs_log_div_abs {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    |Real.log (|A / B|)| = |Real.log (|A|) - Real.log (|B|)| := by
  rw [abs_div, Real.log_div (abs_ne_zero.2 hA) (abs_ne_zero.2 hB)]

theorem abs_log_div_norm {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    |Real.log ‖A / B‖| = |Real.log ‖A‖ - Real.log ‖B‖| := by
  rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hA) (norm_ne_zero_iff.2 hB)]

theorem two_mul_max_half (Δ : ℝ) : 2 * max 0 (1 / 2 - Δ) = max 0 (1 - 2 * Δ) := by
  rcases le_total Δ (1 / 2) with h | h
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

include hb0 hb1 in
open scoped Classical in
/-- **The fibre at a real place**: a logarithmic shell whose length is given by the weight `wReal`. -/
theorem fibre_real_place (hD : D ≠ 0) (z : (QuadInf F (dD D))ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ∃ a c : ℝ, fibPR (quadInfBC hb1 (z : QuadInf F (dD D))) w = logShellR a c ∧
      ENNReal.ofReal (2 * max 0 (c - a)) = wReal D w (torR D w z) := by
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨hy1, hy2⟩ := unit_comp_ne_zero (Units.map (quadInfBC hb1).toMonoidHom z)
  have hy1' : ∀ W : {W : InfinitePlace E // W.IsReal}, (quadInfBC hb1 (z : QuadInf F (dD D))).1 W ≠ 0 := hy1
  have hy2' : ∀ W : {W : InfinitePlace E // W.IsComplex}, (quadInfBC hb1 (z : QuadInf F (dD D))).2 W ≠ 0 := hy2
  have hσ0 : embedding_of_isReal w.2 (dD D) ≠ 0 := by
    rw [dD_map D (embedding_of_isReal w.2)]
    exact neg_ne_zero.2 (ringHom_D_ne_zero D hD _)
  rcases lt_or_gt_of_ne hσ0 with hneg | hpos
  · obtain ⟨W', h', hall, hre, -, -⟩ := exists_unique_complex_place b hb0 hb1 w hneg
    refine ⟨_, _, fibPR_one_complex _ w W' h' hall hre (hy2' W'), ?_⟩
    unfold wReal
    simp only [show ¬ (0 < embedding_of_isReal w.2 (dD D)) from not_lt.2 hneg.le, ↓reduceIte]
    have : (1 / 2 - Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W'‖) -
        (-Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W'‖) = 1 / 2 := by ring
    rw [this, max_eq_right (by norm_num)]
    norm_num
  · obtain ⟨W₁, W₂, hne, h1, h2, hall, hcx, hδ⟩ := exists_two_real_places b hb0 hb1 w hpos
    refine ⟨_, _, fibPR_two_real _ w W₁ W₂ h1 h2 hall hcx (hy1' W₁) (hy1' W₂), ?_⟩
    unfold wReal
    simp only [hpos, ↓reduceIte]
    obtain ⟨hA, hB, hcoord⟩ := splitCoordG_torR D w z hpos
    have e1 : (quadInfBC hb1 (z : QuadInf F (dD D))).1 W₁ =
        z.1.re.1 w + embedding_of_isReal W₁.2 (b 1) * z.1.im.1 w := by
      rw [quadInfBC_fst_apply]
      have hw1 : (⟨W₁.1.comap (algebraMap F E), IsReal.comap _ W₁.2⟩ : {w : InfinitePlace F // w.IsReal}) = w :=
        Subtype.ext h1
      rw [hw1]
    have e2 : (quadInfBC hb1 (z : QuadInf F (dD D))).1 W₂ =
        z.1.re.1 w + embedding_of_isReal W₂.2 (b 1) * z.1.im.1 w := by
      rw [quadInfBC_fst_apply]
      have hw2 : (⟨W₂.1.comap (algebraMap F E), IsReal.comap _ W₂.2⟩ : {w : InfinitePlace F // w.IsReal}) = w :=
        Subtype.ext h2
      rw [hw2]
    have hsq : embedding_of_isReal W₁.2 (b 1) ^ 2 = Real.sqrt (embedding_of_isReal w.2 (dD D)) ^ 2 := by
      rw [embedding_of_isReal_delta_sq b hb1 w W₁ h1, Real.sq_sqrt hpos.le]
    have hkey : min (1 - Real.log |(quadInfBC hb1 (z : QuadInf F (dD D))).1 W₁|)
          (1 - Real.log |(quadInfBC hb1 (z : QuadInf F (dD D))).1 W₂|) -
        max (-Real.log |(quadInfBC hb1 (z : QuadInf F (dD D))).1 W₁|)
          (-Real.log |(quadInfBC hb1 (z : QuadInf F (dD D))).1 W₂|) =
        1 - |Real.log (|splitCoordG (embedding_of_isReal w.2 (dD D)) (torR D w z)|)| := by
      rw [min_sub_max_aux, hcoord, abs_log_div_abs hA hB]
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
      · have e2' : embedding_of_isReal W₂.2 (b 1) = - Real.sqrt (embedding_of_isReal w.2 (dD D)) := by
          rw [hδ, h]
        rw [e1, e2, h, e2']
        ring_nf
      · have e2' : embedding_of_isReal W₂.2 (b 1) = Real.sqrt (embedding_of_isReal w.2 (dD D)) := by
          rw [hδ, h, neg_neg]
        rw [e1, e2, h, e2', abs_sub_comm]
        ring_nf
    rw [hkey]

include hb0 hb1 in
open scoped Classical in
/-- **The fibre at a complex place**: a logarithmic shell whose length is given by the weight `wCpx`. -/
theorem fibre_complex_place (z : (QuadInf F (dD D))ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    ∃ a c : ℝ, fibPC (quadInfBC hb1 (z : QuadInf F (dD D))) w = logShellC a c ∧
      2 * ENNReal.ofReal (2 * Real.pi * max 0 (c - a)) = wCpx D w (torC D w z) := by
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨hy1, hy2⟩ := unit_comp_ne_zero (Units.map (quadInfBC hb1).toMonoidHom z)
  have hy2' : ∀ W : {W : InfinitePlace E // W.IsComplex}, (quadInfBC hb1 (z : QuadInf F (dD D))).2 W ≠ 0 := hy2
  obtain ⟨W₁, W₂, hne, h1, h2, hall⟩ := exists_two_complex_places b hb0 hb1 w
  refine ⟨_, _, fibPC_two _ w W₁ W₂ h1 h2 hall (hy2' W₁) (hy2' W₂), ?_⟩
  have hv1 : (W₁.1.comap (algebraMap F E)).IsComplex := h1 ▸ w.2
  have hv2 : (W₂.1.comap (algebraMap F E)).IsComplex := h2 ▸ w.2
  have hw1 : (⟨W₁.1.comap (algebraMap F E), hv1⟩ : {w : InfinitePlace F // w.IsComplex}) = w := Subtype.ext h1
  have hw2 : (⟨W₂.1.comap (algebraMap F E), hv2⟩ : {w : InfinitePlace F // w.IsComplex}) = w := Subtype.ext h2
  have n1 := norm_quadInfBC_snd_of_complex hb1 (z : QuadInf F (dD D)) W₁ hv1
  have n2 := norm_quadInfBC_snd_of_complex hb1 (z : QuadInf F (dD D)) W₂ hv2
  rw [hw1] at n1
  rw [hw2] at n2
  have hneg : orientEmb F W₂ (b 1) = - orientEmb F W₁ (b 1) :=
    orientEmb_delta_neg hb1 hb0 hne hv1 (h2.trans h1.symm)
  have hsq : (orientEmb F W₁ (b 1)) ^ 2 = sqrtDC D w ^ 2 := by
    rw [orientEmb_delta_sq hb1 W₁ hv1, h1, sq]
    have := sqrtDC_mul_self D w
    simpa using this.symm
  obtain ⟨hA, hB, hcoord⟩ := complexCoordG_torC D w z (sqrtDC_mul_self D w)
  have hkey : min (1 / 2 - Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W₁‖)
        (1 / 2 - Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W₂‖) -
      max (-Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W₁‖)
        (-Real.log ‖(quadInfBC hb1 (z : QuadInf F (dD D))).2 W₂‖) =
      1 / 2 - |Real.log ‖complexCoordG (sqrtDC D w) (torC D w z)‖| := by
    rw [min_sub_max_aux, hcoord, abs_log_div_norm hA hB]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [n1, n2, hneg, h]
      ring_nf
    · rw [n1, n2, hneg, h, abs_sub_comm]
      ring_nf
  rw [hkey, wCpx]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [← mul_assoc, mul_comm 2 (2 * Real.pi), mul_assoc, two_mul_max_half]

include hb0 hb1 in
open scoped Classical in
/-- **The fibre function of the shell is a product over the places of $F$.**

For $x\in G_\infty = SO(\langle1,D\rangle)(F\otimes\mathbb R)$ (with $-D$ not a square in $F$, so that $E = F(\sqrt{-D})$ is a
field), the archimedean fibre function of the shell over the places of $E$,
$$K_\infty(x) = \omega_{\infty,F}\{c\in F_\infty^\times : y\,\iota(c)\in\mathrm{Sh}_E\}\quad(\mathrm{tor}(y) = x),$$
equals $\prod_{w\ \mathrm{real}}\mathrm{wReal}_w(x_w)\cdot\prod_{w\ \mathrm{complex}}\mathrm{wCpx}_w(x_w)$: at a real place $w$ with
$\sigma_w(d)>0$ it is $2\max(0,1-|\log|t||)$ with $t = x_{00}+\sqrt{\sigma_w(d)}\,x_{10}$ (two real places of $E$ over $w$), at a
real place with $\sigma_w(d)<0$ it is $1$ (one complex place of $E$ over $w$), and at a complex place it is
$2\pi\max(0,1-2|\log\|t\||)$ (two complex places of $E$ over $w$; the factor $2$ is that of $\omega_{\infty,F}$ at a complex
place). -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors) [unverified]"]
theorem fibInfSO_shellE (hD : D ≠ 0) (x : GInfSO (diagForm1 D)) :
    fibInfSO E hb1 hD (shellE E) x = (∏ w, wReal D w (x.1 w)) * ∏ w, wCpx D w (x.2 w) := by
  obtain ⟨z, rfl⟩ := torInf_surjective D hD x
  rw [fibInfSO_torInf hb1 hD]
  unfold fibreInf
  rw [fibre_set_eq]
  choose a c hac using fun w => fibre_real_place D hb0 hb1 hD z w
  choose a' c' hac' using fun w => fibre_complex_place D hb0 hb1 z w
  have hPR : fibPR ((Units.map (quadInfBC hb1).toMonoidHom z : (mixedSpace E)ˣ) : mixedSpace E) =
      fun w => logShellR (a w) (c w) := funext fun w => (hac w).1
  have hPC : fibPC ((Units.map (quadInfBC hb1).toMonoidHom z : (mixedSpace E)ˣ) : mixedSpace E) =
      fun w => logShellC (a' w) (c' w) := funext fun w => (hac' w).1
  rw [hPR, hPC, omegaInf_box (fun w => measurableSet_logShellR _ _) (fun w => measurableSet_logShellC _ _)
    (fun w => zero_notMem_logShellR _ _) (fun w => zero_notMem_logShellC _ _)]
  have hR : ∀ w, ∫⁻ x in logShellR (a w) (c w), ENNReal.ofReal |x|⁻¹ = wReal D w (torR D w z) := fun w => by
    rw [lintegral_logShellR]; exact (hac w).2
  have hC : ∀ w, 2 * ∫⁻ x in logShellC (a' w) (c' w), ENNReal.ofReal (‖x‖ ^ 2)⁻¹ = wCpx D w (torC D w z) :=
    fun w => by
      rw [lintegral_logShellC]; exact (hac' w).2
  change _ = (∏ w, wReal D w (torR D w z)) * ∏ w, wCpx D w (torC D w z)
  simp only [hR]
  rw [← Finset.prod_congr rfl (fun w _ => hC w), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [nrComplexPlaces]
  ring

end Weights

/-! ### The archimedean integral -/

section ArchIntegral

open QuadFormsKB.Siegel NumberField NumberField.InfinitePlace NumberField.mixedEmbedding QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

theorem continuous_splitCoordG (δ : ℝ) {Q : QuadForm ℝ 2} : Continuous (splitCoordG δ (Q := Q)) := by
  have h := ArchSOInst.continuous_mat Q
  exact (h.matrix_elem 0 0).add (continuous_const.mul (h.matrix_elem 1 0))

theorem continuous_complexCoordG (s : ℂ) {Q : QuadForm ℂ 2} : Continuous (complexCoordG s (Q := Q)) := by
  have h := ArchSOC.continuous_mat Q
  exact (h.matrix_elem 0 0).add (continuous_const.mul (h.matrix_elem 1 0))

theorem measurable_wReal (w : {w : InfinitePlace F // w.IsReal}) : Measurable (wReal D w) := by
  unfold wReal
  split_ifs
  · have h : Measurable fun r : ℝ => ENNReal.ofReal (2 * max 0 (1 - |Real.log (|r|)|)) := by fun_prop
    exact h.comp (continuous_splitCoordG _).measurable
  · exact measurable_const

theorem measurable_wCpx (w : {w : InfinitePlace F // w.IsComplex}) : Measurable (wCpx D w) := by
  have h : Measurable fun r : ℂ => ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖r‖|)) := by fun_prop
  exact h.comp (continuous_complexCoordG _).measurable

/-- The real form $Q^{\sigma_w}$ of $\langle1,D\rangle$ is $\langle1,\sigma_w(D)\rangle$. -/
theorem QRe_diagForm1 (w : {w : InfinitePlace F // w.IsReal}) :
    QRe (diagForm1 D) w = QuadForm.diag ![1, embedding_of_isReal w.2 (algebraMap (𝓞 F) F D)] := by
  have h := diag_map_map (F := F) ![1, D] (embedding_of_isReal w.2)
  unfold QRe
  rw [diagForm1, h]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The complex form $Q^{\tau_w}$ of $\langle1,D\rangle$ is $\langle1,\tau_w(D)\rangle$. -/
theorem QCx_diagForm1 (w : {w : InfinitePlace F // w.IsComplex}) :
    QCx (diagForm1 D) w = QuadForm.diag ![1, w.1.embedding (algebraMap (𝓞 F) F D)] := by
  have h := diag_map_map (F := F) ![1, D] w.1.embedding
  unfold QCx
  rw [diagForm1, h]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Transport of `lintegral_splitWeight` along an equality of forms. -/
theorem lintegral_wReal_split {Q : QuadForm ℝ 2} {δ : ℝ} (hδ : 0 < δ) (h : Q = QuadForm.diag ![1, -δ])
    (hQ : gramDetR Q ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (2 * max 0 (1 - |Real.log (|splitCoordG δ x|)|)) ∂(lerayMeasure Q hQ) =
      ENNReal.ofReal (1 / (2 * δ * Real.sqrt δ)) := by
  subst h
  exact lintegral_splitWeight hδ

/-- Transport of the total mass `lerayMeasure_diag_one_D_univ` along an equality of forms. -/
theorem lerayMeasure_univ_of_eq {Q : QuadForm ℝ 2} {D' : ℝ} (hD' : 0 < D') (h : Q = QuadForm.diag ![1, D'])
    (hQ : gramDetR Q ≠ 0) :
    lerayMeasure Q hQ univ = ENNReal.ofReal (Real.pi / (4 * D' ^ ((3 : ℝ) / 2))) := by
  subst h
  exact lerayMeasure_diag_one_D_univ hD'

/-- Transport of `lintegral_complexWeight` along an equality of forms. -/
theorem lintegral_wCpx_of_eq {Q : QuadForm ℂ 2} {D' s : ℂ} (hD' : D' ≠ 0) (hs : s ^ 2 = -D')
    (h : Q = QuadForm.diag ![1, D']) (hQ : gramDetC Q ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (2 * Real.pi * max 0 (1 - 2 * |Real.log ‖complexCoordG s x‖|)) ∂(lerayMeasureC Q hQ) =
      ENNReal.ofReal (Real.pi ^ 2 / (32 * ‖D'‖ ^ 3)) := by
  subst h
  exact lintegral_complexWeight hD' hs

open Classical in
/-- **The local value at a real place** (a real number): $1/(2\delta\sqrt\delta)$ if $\delta = \sigma_w(d)>0$ (split), and the
total Leray mass $\pi/(4D_w^{3/2})$ of the compact group $SO(\langle1,D_w\rangle)(\mathbb R)$, $D_w = \sigma_w(D) = -\delta>0$,
otherwise. -/
def realLocalR (w : {w : InfinitePlace F // w.IsReal}) : ℝ :=
  if 0 < embedding_of_isReal w.2 (dD D) then
    1 / (2 * embedding_of_isReal w.2 (dD D) * Real.sqrt (embedding_of_isReal w.2 (dD D)))
  else Real.pi / (4 * (embedding_of_isReal w.2 (algebraMap (𝓞 F) F D)) ^ ((3 : ℝ) / 2))

/-- **The local value at a real place**, as an element of $[0,\infty]$ (`realLocalR`). -/
def realLocal (w : {w : InfinitePlace F // w.IsReal}) : ℝ≥0∞ := ENNReal.ofReal (realLocalR D w)

/-- **The local value at a complex place** (a real number): $\pi^2/(32\|D_w\|^3)$, $D_w = \tau_w(D)$. -/
def cpxLocalR (w : {w : InfinitePlace F // w.IsComplex}) : ℝ :=
  Real.pi ^ 2 / (32 * ‖w.1.embedding (algebraMap (𝓞 F) F D)‖ ^ 3)

/-- **The local value at a complex place**, as an element of $[0,\infty]$ (`cpxLocalR`). -/
def cpxLocal (w : {w : InfinitePlace F // w.IsComplex}) : ℝ≥0∞ := ENNReal.ofReal (cpxLocalR D w)

theorem lintegral_wReal (hD : D ≠ 0) (hQ : (diagForm1 D).Nondegenerate) (w : {w : InfinitePlace F // w.IsReal}) :
    ∫⁻ x, wReal D w x ∂(lerayMeasure (QRe (diagForm1 D) w) (gramDetR_QRe_ne_zero (diagForm1 D) hQ w)) =
      realLocal D w := by
  have hdD : embedding_of_isReal w.2 (dD D) = -embedding_of_isReal w.2 (algebraMap (𝓞 F) F D) :=
    dD_map D (embedding_of_isReal w.2)
  have hσ0 : embedding_of_isReal w.2 (dD D) ≠ 0 := by
    rw [hdD]; exact neg_ne_zero.2 (ringHom_D_ne_zero D hD _)
  unfold realLocal realLocalR wReal
  by_cases hpos : 0 < embedding_of_isReal w.2 (dD D)
  · simp only [hpos, ↓reduceIte]
    refine lintegral_wReal_split hpos ?_ _
    rw [QRe_diagForm1 D w, hdD, neg_neg]
  · have hneg : embedding_of_isReal w.2 (dD D) < 0 := lt_of_le_of_ne (not_lt.1 hpos) hσ0
    simp only [hpos, ↓reduceIte]
    rw [lintegral_one]
    refine lerayMeasure_univ_of_eq ?_ (QRe_diagForm1 D w) _
    rw [hdD] at hneg
    linarith

theorem lintegral_wCpx (hD : D ≠ 0) (hQ : (diagForm1 D).Nondegenerate) (w : {w : InfinitePlace F // w.IsComplex}) :
    ∫⁻ x, wCpx D w x ∂(lerayMeasureC (QCx (diagForm1 D) w) (gramDetC_QCx_ne_zero (diagForm1 D) hQ w)) =
      cpxLocal D w := by
  unfold cpxLocal cpxLocalR
  have hdD : w.1.embedding (dD D) = -w.1.embedding (algebraMap (𝓞 F) F D) := dD_map D w.1.embedding
  refine lintegral_wCpx_of_eq (ringHom_D_ne_zero D hD _) ?_ (QCx_diagForm1 D w) _
  rw [sq, sqrtDC_mul_self, hdD]

open scoped Classical in
/-- **The archimedean integral of the fibre function of the shell.**

$$\int K_\infty\,d\mu^{\mathrm{Tam}}_\infty = c_F\,2^{r_2(F)}\prod_{w\ \mathrm{real}}\Bigl(\frac{1}{2\delta_w\sqrt{\delta_w}}\ \text{or}\
\frac{\pi}{4D_w^{3/2}}\Bigr)\prod_{w\ \mathrm{complex}}\frac{\pi^2}{32\|D_w\|^3},$$
where $\delta_w = \sigma_w(d) = -\sigma_w(D) = -D_w$ and the first alternative at a real place is for $\delta_w>0$. -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors) [unverified]"]
theorem lintegral_fibInfSO_shellE {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
    (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) (hQ : (diagForm1 D).Nondegenerate) :
    ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) =
      ENNReal.ofReal (cF F 2 * cxWeil F 2) * ((∏ w, realLocal D w) * ∏ w, cpxLocal D w) := by
  have hfun : (fun x => fibInfSO E hb1 hD (shellE E) x) =
      fun x : GInfSO (diagForm1 D) => (∏ w, wReal D w (x.1 w)) * ∏ w, wCpx D w (x.2 w) :=
    funext (fibInfSO_shellE D hb0 hb1 hD)
  rw [hfun, muArchTamSO, lintegral_smul_measure, smul_eq_mul]
  congr 1
  have hfm : Measurable fun a : (∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe (diagForm1 D) w)) =>
      ∏ w, wReal D w (a w) :=
    Finset.measurable_prod _ fun w _ => (measurable_wReal D w).comp (measurable_pi_apply w)
  have hgm : Measurable fun a : (∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx (diagForm1 D) w)) =>
      ∏ w, wCpx D w (a w) :=
    Finset.measurable_prod _ fun w _ => (measurable_wCpx D w).comp (measurable_pi_apply w)
  have hsf : ∀ w : {w : InfinitePlace F // w.IsReal},
      SigmaFinite (lerayMeasure (QRe (diagForm1 D) w) (gramDetR_QRe_ne_zero (diagForm1 D) hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero (diagForm1 D) hQ w); infer_instance
  have hsfC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (lerayMeasureC (QCx (diagForm1 D) w) (gramDetC_QCx_ne_zero (diagForm1 D) hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero (diagForm1 D) hQ w); infer_instance
  rw [LerayArch.muArchNF, LerayArch.muArchLeray]
  rw [lintegral_prod_mul (f := fun a : (∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe (diagForm1 D) w)) =>
      ∏ w, wReal D w (a w)) (g := fun a : (∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx (diagForm1 D) w)) =>
      ∏ w, wCpx D w (a w)) hfm.aemeasurable hgm.aemeasurable,
    lintegral_pi_prod _ (fun w => measurable_wReal D w), lintegral_pi_prod _ (fun w => measurable_wCpx D w)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => lintegral_wReal D hD hQ w
  · exact Finset.prod_congr rfl fun w _ => lintegral_wCpx D hD hQ w

end ArchIntegral

/-! ### The ratio of the two archimedean volumes -/

section Ratio

open QuadFormsKB.Siegel NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

theorem realLocalR_pos (hD : D ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) : 0 < realLocalR D w := by
  have hdD : embedding_of_isReal w.2 (dD D) = -embedding_of_isReal w.2 (algebraMap (𝓞 F) F D) :=
    dD_map D (embedding_of_isReal w.2)
  have hσ0 : embedding_of_isReal w.2 (dD D) ≠ 0 := by
    rw [hdD]; exact neg_ne_zero.2 (ringHom_D_ne_zero D hD _)
  unfold realLocalR
  split_ifs with h
  · have := Real.sqrt_pos.2 h
    positivity
  · have hneg : embedding_of_isReal w.2 (dD D) < 0 := lt_of_le_of_ne (not_lt.1 h) hσ0
    rw [hdD] at hneg
    have : 0 < embedding_of_isReal w.2 (algebraMap (𝓞 F) F D) := by linarith
    have := Real.rpow_pos_of_pos this ((3 : ℝ) / 2)
    positivity

theorem cpxLocalR_pos (hD : D ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) : 0 < cpxLocalR D w := by
  have := norm_pos_iff.2 (ringHom_D_ne_zero D hD w.1.embedding)
  unfold cpxLocalR
  positivity

open scoped Classical in
/-- `lintegral_fibInfSO_shellE` with the right-hand side as the image of a real number. -/
theorem lintegral_fibInfSO_shellE_real {E : Type} [Field E] [NumberField E] [Algebra F E]
    {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0)
    (hQ : (diagForm1 D).Nondegenerate) :
    ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) =
      ENNReal.ofReal (cF F 2 * cxWeil F 2 * ((∏ w, realLocalR D w) * ∏ w, cpxLocalR D w)) := by
  rw [lintegral_fibInfSO_shellE D hb0 hb1 hD hQ]
  have h1 : 0 ≤ ∏ w, realLocalR D w := Finset.prod_nonneg fun w _ => (realLocalR_pos D hD w).le
  have h2 : 0 ≤ ∏ w, cpxLocalR D w := Finset.prod_nonneg fun w _ => (cpxLocalR_pos D hD w).le
  have hc : 0 ≤ cF F 2 * cxWeil F 2 := by
    have : 0 < cF F 2 := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero (K := F))) _
    exact (mul_pos this cxWeil_pos).le
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul h1, ENNReal.ofReal_prod_of_nonneg fun w _ => (realLocalR_pos D hD w).le,
    ENNReal.ofReal_prod_of_nonneg fun w _ => (cpxLocalR_pos D hD w).le]
  rfl

theorem rpow_four_three_halves : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The split place: $(4\delta)^{3/2}\cdot\frac{1}{2\delta\sqrt\delta} = 4$. -/
theorem split_identity {δ : ℝ} (hδ : 0 < δ) : (4 * δ) ^ ((3 : ℝ) / 2) * (1 / (2 * δ * Real.sqrt δ)) = 2 ^ 2 := by
  have hs : δ * Real.sqrt δ = δ ^ ((3 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hδ, Real.rpow_one, Real.sqrt_eq_rpow]
  have hp := Real.rpow_pos_of_pos hδ ((3 : ℝ) / 2)
  have h2 : 2 * δ * Real.sqrt δ = 2 * δ ^ ((3 : ℝ) / 2) := by rw [mul_assoc, hs]
  rw [Real.mul_rpow (by norm_num) hδ.le, rpow_four_three_halves, h2]
  field_simp
  norm_num

/-- The compact place: $(4x)^{3/2}\cdot\frac{\pi}{4x^{3/2}} = 2\pi$. -/
theorem compact_identity {x : ℝ} (hx : 0 < x) :
    (4 * x) ^ ((3 : ℝ) / 2) * (Real.pi / (4 * x ^ ((3 : ℝ) / 2))) = 2 * Real.pi := by
  have hp := Real.rpow_pos_of_pos hx ((3 : ℝ) / 2)
  rw [Real.mul_rpow (by norm_num) hx.le, rpow_four_three_halves]
  field_simp
  norm_num

/-- The complex place: $(4t)^3\cdot2\cdot\frac{\pi^2}{32t^3} = 4\pi^2$. -/
theorem cpx_identity {t : ℝ} (ht : 0 < t) : (4 * t) ^ 3 * 2 * (Real.pi ^ 2 / (32 * t ^ 3)) = 2 ^ 2 * Real.pi ^ 2 := by
  field_simp
  norm_num

open scoped Classical in
/-- $|N_{F/\mathbb Q}(x)| = \prod_{w\ \mathrm{real}}|\sigma_w(x)|\prod_{w\ \mathrm{complex}}\|\tau_w(x)\|^2$. -/
theorem abs_norm_eq (x : F) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) =
    (∏ v : {v : InfinitePlace F // v.IsReal}, |embedding_of_isReal v.2 x|) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖w.1.embedding x‖ ^ 2 := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [prod_eq_prod_mul_prod] at h
  rw [← h]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by rw [mult_isReal, pow_one, abs_embedding_isReal]
  · exact Finset.prod_congr rfl fun w _ => by rw [mult_isComplex, norm_embedding_eq]

theorem sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ ((3 : ℝ) / 2) = x ^ 3 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem ratio_aux (A B C P c e : ℝ) (h : c * e = 1) : A * B * C * P = (A * B * e) * (c * C * P) := by
  rw [show (A * B * e) * (c * C * P) = (c * e) * (A * B * C * P) by ring, h, one_mul]

open scoped Classical in
/-- **The ratio of the two archimedean volumes, as an identity of real numbers**:
$2^{r_2(E)}\cdot2^{r_1(E)}\cdot\pi^{r_2(E)} = |N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}\cdot
c_F\,2^{r_2(F)}\prod_{w\ \mathrm{real}}\mathrm{realLocalR}_w\prod_{w\ \mathrm{complex}}\mathrm{cpxLocalR}_w$. -/
theorem shell_ratio_real {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
    (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) :
    (2 : ℝ) ^ nrComplexPlaces E * ((2 : ℝ) ^ nrRealPlaces E * Real.pi ^ nrComplexPlaces E) =
      (((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) ^ ((3 : ℝ) / 2) * |(discr F : ℝ)| ^ ((1 : ℝ) / 2)) *
        (cF F 2 * cxWeil F 2 * ((∏ w, realLocalR D w) * ∏ w, cpxLocalR D w)) := by
  have hnr := nrRealPlaces_eq b hb0 hb1
  have hnc := nrComplexPlaces_eq b hb0 hb1
  have hdD : ∀ v : {v : InfinitePlace F // v.IsReal},
      embedding_of_isReal v.2 (dD D) = -embedding_of_isReal v.2 (algebraMap (𝓞 F) F D) := fun v => dD_map D _
  have hne : ∀ v : {v : InfinitePlace F // v.IsReal}, embedding_of_isReal v.2 (dD D) ≠ 0 := fun v => by
    rw [hdD v]; exact neg_ne_zero.2 (ringHom_D_ne_zero D hD _)
  have hfil : (Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} => ¬ 0 < embedding_of_isReal v.2 (dD D)) =
      Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} => embedding_of_isReal v.2 (dD D) < 0 :=
    Finset.filter_congr fun v _ => ⟨fun hv => lt_of_le_of_ne (not_lt.1 hv) (hne v), fun hv => not_lt.2 hv.le⟩
  -- the left side as a product over the places of `F`
  have hL : (2 : ℝ) ^ nrComplexPlaces E * ((2 : ℝ) ^ nrRealPlaces E * Real.pi ^ nrComplexPlaces E) =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (if 0 < embedding_of_isReal v.2 (dD D) then (2 : ℝ) ^ 2
        else 2 * Real.pi)) * ∏ w : {w : InfinitePlace F // w.IsComplex}, ((2 : ℝ) ^ 2 * Real.pi ^ 2) := by
    rw [hnr, hnc, Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.prod_const, Finset.card_univ, hfil]
    unfold nrComplexPlaces
    generalize (2 : ℝ) = t
    ring
  -- the local identities
  have hRp : ∀ v : {v : InfinitePlace F // v.IsReal},
      (4 * |embedding_of_isReal v.2 (dD D)|) ^ ((3 : ℝ) / 2) * realLocalR D v =
        if 0 < embedding_of_isReal v.2 (dD D) then (2 : ℝ) ^ 2 else 2 * Real.pi := by
    intro v
    unfold realLocalR
    by_cases h : 0 < embedding_of_isReal v.2 (dD D)
    · simp only [h, ↓reduceIte]
      rw [abs_of_pos h]
      exact split_identity h
    · have hneg : embedding_of_isReal v.2 (dD D) < 0 := lt_of_le_of_ne (not_lt.1 h) (hne v)
      simp only [h, ↓reduceIte]
      have hx : 0 < embedding_of_isReal v.2 (algebraMap (𝓞 F) F D) := by
        have := hdD v; linarith
      rw [abs_of_neg hneg, hdD v, neg_neg]
      exact compact_identity hx
  have hCp : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (4 * ‖w.1.embedding (dD D)‖) ^ 3 * 2 * cpxLocalR D w = (2 : ℝ) ^ 2 * Real.pi ^ 2 := by
    intro w
    have hdD' : w.1.embedding (dD D) = -w.1.embedding (algebraMap (𝓞 F) F D) := dD_map D w.1.embedding
    have ht := norm_pos_iff.2 (ringHom_D_ne_zero D hD w.1.embedding)
    unfold cpxLocalR
    rw [hdD', norm_neg]
    exact cpx_identity ht
  -- the norm
  have hN : ((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) ^ ((3 : ℝ) / 2) =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (4 * |embedding_of_isReal v.2 (dD D)|) ^ ((3 : ℝ) / 2)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (4 * ‖w.1.embedding (dD D)‖) ^ 3 := by
    have e1 : ∀ v : {v : InfinitePlace F // v.IsReal},
        |embedding_of_isReal v.2 (4 * dD D)| = 4 * |embedding_of_isReal v.2 (dD D)| := fun v => by
      rw [map_mul, map_ofNat, abs_mul]; norm_num
    have e2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
        ‖w.1.embedding (4 * dD D)‖ = 4 * ‖w.1.embedding (dD D)‖ := fun w => by
      rw [map_mul, map_ofNat, norm_mul]; norm_num
    rw [abs_norm_eq, Real.mul_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _)
      (Finset.prod_nonneg fun w _ => sq_nonneg _),
      ← Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _), ← Real.finsetProd_rpow _ _ (fun w _ => sq_nonneg _)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ => by rw [e1]
    · exact Finset.prod_congr rfl fun w _ => by rw [e2, sq_rpow_three_halves (norm_nonneg _ |> fun h => by positivity)]
  have hcF : cF F 2 * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) = 1 := by
    have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
    rw [cF, ← Real.rpow_add hd]
    norm_num
  have hcx : cxWeil F 2 = ∏ w : {w : InfinitePlace F // w.IsComplex}, (2 : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ]
    norm_num [cxWeil, nrComplexPlaces]
  rw [hL, hN, hcx]
  have h1 : (∏ v : {v : InfinitePlace F // v.IsReal}, (if 0 < embedding_of_isReal v.2 (dD D) then (2 : ℝ) ^ 2
        else 2 * Real.pi)) * ∏ w : {w : InfinitePlace F // w.IsComplex}, ((2 : ℝ) ^ 2 * Real.pi ^ 2) =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (4 * |embedding_of_isReal v.2 (dD D)|) ^ ((3 : ℝ) / 2) * realLocalR D v) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ((4 * ‖w.1.embedding (dD D)‖) ^ 3 * 2 * cpxLocalR D w) := by
    congr 1
    · exact Finset.prod_congr rfl fun v _ => (hRp v).symm
    · exact Finset.prod_congr rfl fun w _ => (hCp w).symm
  rw [h1]
  simp only [Finset.prod_mul_distrib]
  rw [show ∀ (A B C D' E' : ℝ), A * D' * (B * C * E') = A * B * C * (D' * E') from fun A B C D' E' => by ring]
  exact ratio_aux _ _ _ _ _ _ hcF

/-- The factor $|N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}$ comparing the two archimedean volumes (`d = -D`). -/
def shellRatio : ℝ :=
  ((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) ^ ((3 : ℝ) / 2) * |(discr F : ℝ)| ^ ((1 : ℝ) / 2)

theorem shellRatio_nonneg : 0 ≤ shellRatio D :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (abs_nonneg _) _)

open scoped Classical in
/-- **The archimedean comparison of the two volumes**: with $d = -D$ and $E = F(\sqrt{d})$,
$$\omega_{\infty,E}(\mathrm{Sh}_E) = |N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}\cdot\int_{G_\infty}K_\infty\,d\mu^{\mathrm{Tam}}_\infty,$$
$K_\infty$ the fibre function of the shell (`fibInfSO`), $\mu^{\mathrm{Tam}}_\infty$ = `muArchTamSO`. (For a unit ball of $SO(\langle1,D\rangle)$
this is the archimedean ratio $|4d|^{3/2}_\infty$ at every infinite place, times the discriminant factor $c_F^{-1}$.) -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors) [unverified]"]
theorem omegaInf_shellE_eq_mul {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
    (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) (hQ : (diagForm1 D).Nondegenerate) :
    omegaInf E (shellE E) = ENNReal.ofReal (shellRatio D) *
      ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) := by
  have h : omegaInf E (shellE E) =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces E * ((2 : ℝ) ^ nrRealPlaces E * Real.pi ^ nrComplexPlaces E)) := by
    rw [omegaInf_shellE, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow Real.pi_pos.le,
      ENNReal.ofReal_ofNat]
  have hc : 0 ≤ cF F 2 * cxWeil F 2 := by
    have : 0 < cF F 2 := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero (K := F))) _
    exact (mul_pos this cxWeil_pos).le
  have h1 : 0 ≤ ∏ w, realLocalR D w := Finset.prod_nonneg fun w _ => (realLocalR_pos D hD w).le
  have h2 : 0 ≤ ∏ w, cpxLocalR D w := Finset.prod_nonneg fun w _ => (cpxLocalR_pos D hD w).le
  rw [h, lintegral_fibInfSO_shellE_real D hb0 hb1 hD hQ, ← ENNReal.ofReal_mul (shellRatio_nonneg D), shellRatio,
    shell_ratio_real D hb0 hb1 hD]

open scoped Classical in
/-- **The ratio of the archimedean volumes** (the quotient form of `omegaInf_shellE_eq_mul`):
$\omega_{\infty,E}(\mathrm{Sh}_E)\Big/\int_{G_\infty}K_\infty\,d\mu^{\mathrm{Tam}}_\infty = |N_{F/\mathbb Q}(4d)|^{3/2}\,|d_F|^{1/2}$. -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors) [unverified]"]
theorem omegaInf_shellE_div {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
    (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) (hQ : (diagForm1 D).Nondegenerate) :
    omegaInf E (shellE E) / ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) =
      ENNReal.ofReal (shellRatio D) := by
  have hpos : 0 < cF F 2 * cxWeil F 2 * ((∏ w, realLocalR D w) * ∏ w, cpxLocalR D w) := by
    have : 0 < cF F 2 := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero (K := F))) _
    exact mul_pos (mul_pos this cxWeil_pos) (mul_pos (Finset.prod_pos fun w _ => realLocalR_pos D hD w)
      (Finset.prod_pos fun w _ => cpxLocalR_pos D hD w))
  have h0 : ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) ≠ 0 := by
    rw [lintegral_fibInfSO_shellE_real D hb0 hb1 hD hQ]
    exact (ENNReal.ofReal_pos.2 hpos).ne'
  have htop : ∫⁻ x, fibInfSO E hb1 hD (shellE E) x ∂(muArchTamSO (diagForm1 D) hQ) ≠ ⊤ := by
    rw [lintegral_fibInfSO_shellE_real D hb0 hb1 hD hQ]
    exact ENNReal.ofReal_ne_top
  rw [omegaInf_shellE_eq_mul D hb0 hb1 hD hQ, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]

end Ratio

end QuadFormsKB.Tamagawa.Measure.Weil
