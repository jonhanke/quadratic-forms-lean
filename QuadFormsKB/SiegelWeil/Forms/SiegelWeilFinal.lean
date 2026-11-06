/-
# The Siegel–Weil formula for forms by forms, degree $\le R$, unconditional

**Layer:** global over a totally real number field $F$ whose ring of integers $\mathcal O_F$ is a principal ideal domain.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite with $b_i \in \mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$, $\Phi_v = \mathbf 1_{L_v^r}$ at every
finite place; a degree bound $R$ with $m > 4R^2$; $s_0 = m - \frac{r+1}2$; $\mathcal E^{(r)}(Z) = \prod_w\det(\operatorname{Im}Z_w)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$
(`eisHolR`); the genus theta series $\theta^{(r)}_{\mathrm{gen}(L)} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\theta_M/|O(M)|$ (`thetaGenR`),
$\theta_M(Z) = \sum_{X\in M^r}e(\operatorname{tr}(Q_0[X]Z))$.

**Results.**
* **`hasSum_eisHolR_expansion`** (item (D)): for $1 \le r$, $m > 4r^2$, $\mathcal E^{(r)}(Z) = \sum_Ta_r(T)e_T(Z)$ absolutely on $\mathbb H_r^d$, with $a_r(T) \ne 0$
  only for totally positive semidefinite $T$. *Proof:* in the coordinates $t$ (`zC`, `HolExpCoord`), $f = \mathcal E\circ Z$ is
  $\mathbb Z^J$-periodic (`fC_add_int`), continuous on slices and separately holomorphic (`continuous_fC_slice`, `differentiableAt_fC_update`), and
  bounded on $\{\operatorname{Im}t - y_0 \in K\}$ (`exists_bound_eisHolR`); so its torus coefficients $c_n$ are independent of the height
  (`HolExp.coeffY_const`), vanish off the dual cone (Koecher, `HolExp.coeffY_eq_zero_of_bounded`), are absolutely summable against
  $e(n\cdot t)$ (`HolExp.summable_exp_dualCone`), and $f(t) = \sum_nc_ne(n\cdot t)$ (`HolExp.hasSum_expansion`, Mathlib's Fourier inversion on the
  torus); finally $e(n\cdot t) = e_{T_n}(Z(t))$ (`eT_formZ_zC`) with $n \mapsto T_n$ injective and the dual cone mapping to totally positive
  semidefinite forms (`isTotPSD_formZ`).
* **`siegelWeil_forms`** (**the Siegel–Weil formula of degree $r \le R$**): for every $r \le R$ and $Z \in \mathbb H_r^d$,
  $$E^{(r)}(g_Z, s_0, \Phi) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\theta^{(r)}_{\mathrm{gen}(L)}(Z),$$
  i.e. $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$ (**`eisHolR_eq_thetaGenR`**). Unconditional (no named input); the hypotheses are
  $\mathcal O_F$ a principal ideal domain (used only to move a radical vector of a singular $T$ to the first coordinate, `SingularRadical.lean`)
  and the crude convergence range $m > 4R^2$ of `summable_norm_globalSecR`.

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified]; Kudla–Rallis,
*On the Weil–Siegel formula*, J. reine angew. Math. 387 (1988) [unverified]; Siegel, *Über die analytische Theorie der quadratischen Formen*,
Ann. of Math. 36 (1935) [unverified]; Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpEisHol
import QuadFormsKB.SiegelWeil.Forms.HolExpEisForms
import QuadFormsKB.SiegelWeil.Forms.SiegelWeilOfExpansion

open Matrix NumberField
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames
  QuadFormsKB.SiegelWeil.Forms.HolExp
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma coneK_eq_Kc : coneK F r = Kc F r := rfl

variable (F r) in
/-- A base point $y_0$ of the cone $K$. -/
def yBase : JR F r → ℝ := Classical.choose (exists_mem_Kc (F := F) (r := r))

lemma yBase_mem : yBase F r ∈ coneK F r := Classical.choose_spec (exists_mem_Kc (F := F) (r := r))

/-- The torus coefficient $c_n$ of $f = \mathcal E\circ Z$ (at the base height; independent of the height, `coeffY_fC_eq`). -/
def eisCoeffZ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (r : ℕ) (n : JR F r → ℤ) : ℂ :=
  coeffY (fC (r := r) b hb hbpos) n (yBase F r)

section Fixed


lemma coeffY_fC_eq (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) (n : JR F r → ℤ) {y : JR F r → ℝ} (hy : y ∈ coneK F r) :
    coeffY (fC (r := r) b hb hbpos) n y = eisCoeffZ b hb hbpos r n :=
  coeffY_const isOpen_coneK convex_coneK (fun t n => fC_add_int b hb hbpos t n)
    (fun y hy => continuous_fC_slice b hb hbpos hr hm hy)
    (fun x y hy i => differentiableAt_fC_update b hb hbpos hr hm x y hy i) n hy yBase_mem

lemma exists_bound_fC_slice (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) {y : JR F r → ℝ} (hy : y ∈ coneK F r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fC (r := r) b hb hbpos (cplx x y)‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_eisHolR b hb hbpos hr hm (Y0 := fun w => xMat y w) hy
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [fC_cplx b hb hbpos x hy]
  refine (hM _ (zPt_mem_siegelHF _ hy x) fun w => ?_).trans (le_max_left _ _)
  rw [zPt_im _ hy, sub_self]; exact PosSemidef.zero

/-- **Koecher**: $c_n = 0$ unless $n\cdot y \ge 0$ on the whole cone. -/
lemma eisCoeffZ_eq_zero (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) (n : JR F r → ℤ) (hn : ¬ ∀ y ∈ coneK F r, 0 ≤ ∑ q, (n q : ℝ) * y q) :
    eisCoeffZ b hb hbpos r n = 0 := by
  obtain ⟨M, hM⟩ := exists_bound_eisHolR b hb hbpos hr hm (Y0 := fun w => xMat (yBase F r) w) yBase_mem
  refine coeffY_eq_zero_of_bounded isOpen_coneK convex_coneK (fun y hy c hc => smul_mem_coneK hy hc)
    (fun t n => fC_add_int b hb hbpos t n) (fun y hy => continuous_fC_slice b hb hbpos hr hm hy)
    (fun x y hy i => differentiableAt_fC_update b hb hbpos hr hm x y hy i) yBase_mem (M := M) (fun t ht => ?_) n hn
  have himK : imC t ∈ coneK F r := by
    have : imC t = yBase F r + ((fun i => (t i).im) - yBase F r) := by funext q; simp [imC]
    rw [this]; exact add_mem_Kc yBase_mem ht
  have hmem : zC t ∈ siegelHF F r := (zC_mem_iff t).mpr himK
  unfold fC
  rw [if_pos hmem]
  refine hM _ hmem fun w => ?_
  rw [zC_map_im]
  have e : xMat (imC t) w - xMat (yBase F r) w = xMat ((fun i => (t i).im) - yBase F r) w := by
    have h := xMat_add ((fun i => (t i).im) - yBase F r) (yBase F r) w
    rw [sub_add_cancel] at h
    rw [show imC t = fun i => (t i).im from rfl, h]; abel
  rw [e]
  exact (ht w).posSemidef

open Classical in
/-- **Absolute convergence** of $\sum_nc_ne(n\cdot t)$ on the tube. -/
lemma summable_eisCoeffZ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) (t : JR F r → ℂ) (ht : imC t ∈ coneK F r) :
    Summable fun n : JR F r → ℤ => ‖eisCoeffZ b hb hbpos r n * charZ n t‖ := by
  set y := imC t
  have hy2 : (1 / 2 : ℝ) • y ∈ coneK F r := smul_mem_coneK ht (by norm_num)
  obtain ⟨M, hM0, hM⟩ := exists_bound_fC_slice b hb hbpos hr hm hy2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_coneK (F := F) (r := r)) y ht
  have hball' : ∀ z : JR F r → ℝ, (∀ i, |z i - y i| ≤ ε / 2) → z ∈ coneK F r := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    linarith [hz i]
  have hsum := summable_exp_dualCone (K := coneK F r) (half_pos hε) hball' (c := π) Real.pi_pos
  refine (hsum.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  have htc : t = cplx (reC t) y := (cplx_re_im t).symm
  split_ifs with hn
  · rw [norm_mul, ← coeffY_fC_eq b hb hbpos hr hm n hy2, htc, norm_charZ_cplx]
    have hc := norm_coeffY_le hM0 hM n
    calc ‖coeffY (fC b hb hbpos) n ((1 / 2 : ℝ) • y)‖ * Real.exp (-(2 * π * ∑ i, (n i : ℝ) * y i))
        ≤ M * Real.exp (2 * π * ∑ i, (n i : ℝ) * ((1 / 2 : ℝ) • y) i) *
            Real.exp (-(2 * π * ∑ i, (n i : ℝ) * y i)) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = M * Real.exp (-π * ∑ i, (n i : ℝ) * y i) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ i, (n i : ℝ) * (1 / 2 * y i) = (1 / 2) * ∑ i, (n i : ℝ) * y i by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
          ring
  · rw [eisCoeffZ_eq_zero b hb hbpos hr hm n hn, zero_mul, norm_zero, mul_zero]

end Fixed

variable (F) in
/-- The form in $0$ variables. -/
def qf0 : QuadForm F 0 := ⟨0, fun i => i.elim0⟩

/-- **The Fourier coefficients of $\mathcal E^{(r)}$** over forms $T$: $a(T_n) = c_n$ and $a(T) = 0$ for $T$ not of the form $T_n$; in degree $0$,
$a = 1$. -/
def eisCoeff (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) :
    ∀ r : ℕ, QuadForm F r → ℂ
  | 0 => fun _ => 1
  | r + 1 => Function.extend formZ (eisCoeffZ b hb hbpos (r + 1)) 0

lemma eisCoeff_succ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (r : ℕ) (n : JR F (r + 1) → ℤ) : eisCoeff b hb hbpos (r + 1) (formZ n) = eisCoeffZ b hb hbpos (r + 1) n :=
  formZ_injective.extend_apply _ _ n

lemma eisCoeff_succ_of_not_mem (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (r : ℕ) (T : QuadForm F (r + 1))
    (hT : T ∉ Set.range (formZ (F := F) (r := r + 1))) : eisCoeff b hb hbpos (r + 1) T = 0 := by
  show Function.extend formZ (eisCoeffZ b hb hbpos (r + 1)) 0 T = 0
  rw [Function.extend_apply' _ _ _ (fun ⟨n, hn⟩ => hT ⟨n, hn⟩)]
  rfl

/-- **The Fourier expansion of $\mathcal E^{(r)}$** ($1 \le r$, $m > 4r^2$; see the module docstring). -/
@[kb "freitag1983" "Ch. I (Fourier expansion of Siegel modular forms; Koecher's principle) [unverified]"]
theorem hasSum_eisHolR_expansion (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (r : ℕ) (hm : 4 * ((r + 1 : ℕ) : ℝ) ^ 2 < m) :
    (∀ Z ∈ siegelHF F (r + 1), Summable fun T => ‖eisCoeff b hb hbpos (r + 1) T * eT T Z‖) ∧
    (∀ Z ∈ siegelHF F (r + 1), HasSum (fun T => eisCoeff b hb hbpos (r + 1) T * eT T Z) (eisHolR b hb hbpos Z)) ∧
    (∀ T, eisCoeff b hb hbpos (r + 1) T ≠ 0 → IsTotPSD T) := by
  have hr : 1 ≤ r + 1 := Nat.succ_pos r
  have hoff : ∀ (Z : InfinitePlace F → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T : QuadForm F (r + 1)),
      T ∉ Set.range (formZ (F := F) (r := r + 1)) → eisCoeff b hb hbpos (r + 1) T * eT T Z = 0 :=
    fun Z T hT => by rw [eisCoeff_succ_of_not_mem b hb hbpos r T hT, zero_mul]
  have hcomp : ∀ (Z : InfinitePlace F → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (t : JR F (r + 1) → ℂ), zC t = Z →
      ((fun T => eisCoeff b hb hbpos (r + 1) T * eT T Z) ∘ formZ) =
        fun n => eisCoeffZ b hb hbpos (r + 1) n * charZ n t := by
    intro Z t ht
    funext n
    simp only [Function.comp, eisCoeff_succ, ← ht, eT_formZ_zC]
  refine ⟨fun Z hZ => ?_, fun Z hZ => ?_, fun T hT => ?_⟩
  · obtain ⟨t, ht⟩ := exists_zC_eq hZ
    have hK : imC t ∈ coneK F (r + 1) := (zC_mem_iff t).mp (ht ▸ hZ)
    have h := summable_eisCoeffZ b hb hbpos hr hm t hK
    rw [← formZ_injective.summable_iff (f := fun T => ‖eisCoeff b hb hbpos (r + 1) T * eT T Z‖)
      (fun T hT => by rw [hoff Z T hT, norm_zero])]
    have e := congrArg (fun g => fun n => ‖g n‖) (hcomp Z t ht)
    refine h.congr fun n => ?_
    exact (congrFun e n).symm
  · obtain ⟨t, ht⟩ := exists_zC_eq hZ
    have hK : imC t ∈ coneK F (r + 1) := (zC_mem_iff t).mp (ht ▸ hZ)
    rw [← formZ_injective.hasSum_iff (hoff Z), hcomp Z t ht]
    have hexp := hasSum_expansion (K := coneK F (r + 1)) (fun t n => fC_add_int b hb hbpos t n)
      (fun y hy => continuous_fC_slice b hb hbpos hr hm hy) t hK
      (by
        have h := summable_eisCoeffZ b hb hbpos hr hm t hK
        refine h.congr fun n => ?_
        show _ = ‖coeffY (fC b hb hbpos) n (imC t) * charZ n t‖
        rw [coeffY_fC_eq b hb hbpos hr hm n hK])
    have hf : fC b hb hbpos t = eisHolR b hb hbpos Z := by
      unfold fC; rw [if_pos (ht ▸ hZ), ht]
    rw [hf] at hexp
    refine hexp.congr_fun fun n => ?_
    show _ = coeffY (fC b hb hbpos) n (imC t) * charZ n t
    rw [coeffY_fC_eq b hb hbpos hr hm n hK]
  · by_cases hT' : T ∈ Set.range (formZ (F := F) (r := r + 1))
    · obtain ⟨n, rfl⟩ := hT'
      rw [eisCoeff_succ] at hT
      refine isTotPSD_formZ n ?_
      by_contra hn
      exact hT (eisCoeffZ_eq_zero b hb hbpos hr hm n hn)
    · exact absurd (eisCoeff_succ_of_not_mem b hb hbpos r T hT') hT

/-- **The Siegel–Weil formula for forms by forms, degree $\le R$** (holomorphic normalization): $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$ on
$\mathbb H_r^d$ for every $r \le R$, when $\mathcal O_F$ is a principal ideal domain and $m > 4R^2$. Unconditional. -/
@[kb "weil1965" "Ch. IV (Siegel–Weil formula) [unverified]; kudlaRallis1988 [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem eisHolR_eq_thetaGenR [IsPrincipalIdealRing (𝓞 F)] (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) (R : ℕ)
    (hm : 4 * (R : ℝ) ^ 2 < m) :
    ∀ r ≤ R, ∀ Z ∈ siegelHF F r,
      eisHolR b hb hbpos Z = thetaGenR ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) Z := by
  have hmr : ∀ r, r ≤ R → 4 * (r : ℝ) ^ 2 < m := fun r hr => by
    have h1 : (r : ℝ) ≤ R := by exact_mod_cast hr
    have h0 : (0 : ℝ) ≤ r := by positivity
    nlinarith
  refine eisHolR_eq_thetaGenR_of_expansion_only b hb hbpos hpd R hm (eisCoeff b hb hbpos) ?_ ?_ ?_
  · intro r hr Z hZ
    cases r with
    | zero =>
      simp only [eisCoeff, eT_zero, mul_one, norm_one]
      exact (hasSum_single (qf0 F) fun T hT => absurd (Subsingleton.elim T _) hT).summable
    | succ r => exact (hasSum_eisHolR_expansion b hb hbpos r (hmr _ hr)).1 Z hZ
  · intro r hr Z hZ
    cases r with
    | zero =>
      rw [eisHolR_zero b hb hbpos hZ]
      simp only [eisCoeff, eT_zero, mul_one]
      have := hasSum_single (f := fun _ : QuadForm F 0 => (1 : ℂ)) (qf0 F)
        fun T hT => absurd (Subsingleton.elim T _) hT
      exact this
    | succ r => exact (hasSum_eisHolR_expansion b hb hbpos r (hmr _ hr)).2.1 Z hZ
  · intro r hr T hT
    cases r with
    | zero => exact fun w => PosSemidef.of_dotProduct_mulVec_nonneg (by ext i j; exact i.elim0) fun x => by simp [dotProduct]
    | succ r => exact (hasSum_eisHolR_expansion b hb hbpos r (hmr _ hr)).2.2 T hT

/-- **The Siegel–Weil formula for forms by forms** (adelic normalization): for every $r \le R$ and $Z \in \mathbb H_r^d$,
$E^{(r)}(g_Z, s_0, \Phi) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\theta^{(r)}_{\mathrm{gen}(L)}(Z)$, the genus average of the degree-$r$ theta
series of $L = \mathcal O_F^n$ for $Q_0 = \sum_ib_ix_i^2$ ($\mathcal O_F$ a principal ideal domain, $m > 4R^2$). Unconditional. -/
@[kb "weil1965" "Ch. IV (Siegel–Weil formula) [unverified]; kudlaRallis1988 [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem siegelWeil_forms [IsPrincipalIdealRing (𝓞 F)] (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) (R : ℕ)
    (hm : 4 * (R : ℝ) ^ 2 < m) (r : ℕ) (hr : r ≤ R) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) :
    eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
        (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) =
      prodIm m Z * thetaGenR ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) Z := by
  rw [eisensteinR_eq_prodIm_mul b hb hbpos hZ, eisHolR_eq_thetaGenR b hb hbpos hpd R hm r hr Z hZ]

end QuadFormsKB.SiegelWeil.Forms
