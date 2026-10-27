/-
# The Fourier coefficients of $E_Q$ over a totally real field

**Setting.** $F$ totally real of degree $d$, $\mathcal O = \mathcal O_F$, $Q_0$ a totally positive definite form over $\mathcal O$ in
$n = 2k$ variables, $k \ge 3$; $E_Q$ = `eisQ Q₀ k`, the Eisenstein series whose weight is the constant term of
$\theta_{\mathrm{Gen}}$ at each cusp (`eisGenWeight`). Conventions: $e(x) = e^{2\pi ix}$, $\operatorname{Tr} = \operatorname{Tr}_{F/\mathbb Q}$,
$N(z) = \prod_v z_v$ for $z \in \mathbb C^d$, $\mathfrak d^{-1}$ the inverse different (the trace dual of $\mathcal O$),
Lebesgue measure on $\mathbb R^d$.

**Row expansion over $\mathcal O$ (Lipschitz)** (`hasSum_lipschitz`): for $z \in \mathbb H^d$ and $u \in F$,
$$\sum_{b\in\mathcal O}N(z + u + b)^{-k} = c_{\mathcal O}\sum_{\mu\in\mathfrak d^{-1},\ \mu\gg0}
  \Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^dN(\mu)^{k-1}e(\operatorname{Tr}\mu(z + u)),$$
$c_{\mathcal O}$ = `latConst` of the lattice $\sigma(\mathcal O) \subset \mathbb R^d$ $= \operatorname{covol}(\sigma(\mathcal O))^{-1} = |d_F|^{-1/2}$ (`latConst_one`).
This is `hasSum_row` with $c = 1$ and the weight $1$ on $\mathcal O$ (which is not unit equivariant for odd $k$, hence the
separate statement; the proof is the same Poisson summation, `hasSum_lattice_fourier`).

Sources: Shimura, *The special values of the zeta functions associated with Hilbert modular forms*, Duke Math. J. 45
(1978), §3, (3.4)–(3.11) [unverified]; Siegel, *Über die analytische Theorie der quadratischen Formen III*, Ann. Math. 38
(1937) [unverified].
-/
import QuadFormsKB.HilbertModular.Cuspidal
import QuadFormsKB.HilbertModular.EisensteinQExp
import QuadFormsKB.HilbertModular.KoecherBounded
import QuadFormsKB.SiegelWeil.SingularSeriesNF

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The lattice $\sigma(\mathcal O)$ -/

variable (F) in
/-- The lattice basis of $\sigma(\mathcal O_F) \subset \mathbb R^d$ (`koecherBasis` of the unit ideal). -/
abbrev oBasis : Module.Basis (Fin (Module.finrank ℚ F)) ℝ (InfinitePlace F → ℝ) :=
  koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- The lattice point $b_m = \sum_jm_jb_j \in \mathcal O$ with coordinates $m$. -/
abbrev oElt (m : Fin (Module.finrank ℚ F) → ℤ) : F := QuadFormsKB.Analysis.latElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m

lemma oElt_mem (m : Fin (Module.finrank ℚ F) → ℤ) : ∃ e : 𝓞 F, ιO e = oElt m := by
  have := latElt_mem (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m
  rw [Units.val_one] at this
  obtain ⟨e, he⟩ := (FractionalIdeal.mem_one_iff _).mp this
  exact ⟨e, he⟩

/-- The frequency $\mu_m = \sum_jm_jb_j^\vee \in \mathfrak d^{-1}$ (the dual basis for the trace form). -/
abbrev oDual (m : Fin (Module.finrank ℚ F) → ℤ) : F :=
  QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m

lemma dualVec_oBasis (m : Fin (Module.finrank ℚ F) → ℤ) : dualVec (oBasis F) m = realVec (oDual m) :=
  dualVec_koecherBasis _ m

lemma oDual_mem (m : Fin (Module.finrank ℚ F) → ℤ) : oDual m ∈ invDifferent F := by
  have := (QuadFormsKB.Analysis.dualEquiv (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) m).2
  rw [QuadFormsKB.Analysis.dualEquiv_coe] at this
  simpa [invDifferent] using this

/-! ### Lipschitz's formula over $\mathcal O_F$ -/

lemma heckeTerm_one_eq_rowPhi (k : ℕ) (s : ℝ) (d : F) (z : InfinitePlace F → ℍ) :
    heckeTerm (fun _ => (1 : ℂ)) k s ((1 : F), d) (fun v => (z v : ℂ)) =
      rowPhi k s (fun v => (z v).re) (fun v => (z v).im) (realVec d) := by
  rw [heckeTerm_eq_rowPhi, one_mul]
  congr 1 <;> funext v <;> rw [map_one, one_mul]

/-- **Exponential decay of the Lipschitz coefficients**: $\sum_m\big|\prod_vT_{k,0}(\nu_{m,v}, y_v)\big| < \infty$ ($k \ge 2$, $y \gg 0$). -/
lemma summable_norm_prod_lineFT {k : ℕ} (hk : 3 ≤ k) (z : InfinitePlace F → ℍ) :
    Summable fun n : Fin (Module.finrank ℚ F) → ℤ => ‖∏ v, lineFT k 0 (dualVec (oBasis F) n v) (z v).im‖ := by
  set kb := oBasis F
  set h : InfinitePlace F → ℝ := fun v => (z v).im with hh_def
  have hh : ∀ v, h v ≠ 0 := fun v => (z v).im_pos.ne'
  have hk2 : 2 ≤ k := by omega
  set M := ∏ v, (|h v| * (|h v| ^ k)⁻¹ * max 1 (|h v| ^ 2)⁻¹ *
    (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)))
  obtain ⟨hmin, hhmin, hhminv⟩ := min_abs_pos h hh
  refine ((summable_exp_neg_l1 kb (a := π * hmin) (by positivity)).mul_left M).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_prod]
  calc ∏ v, ‖lineFT k 0 (dualVec kb n v) (h v)‖
      ≤ ∏ v, (|h v| * (|h v| ^ k)⁻¹ * max 1 (|h v| ^ 2)⁻¹ *
          (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) *
            Real.exp (-π * (|dualVec kb n v| * |h v|))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun v _ => norm_lineFT_le hk2 le_rfl zero_le_one _ (hh v)
    _ = M * Real.exp (-π * ∑ v, |dualVec kb n v| * |h v|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, ← Real.exp_sum]
    _ ≤ M * Real.exp (-(π * hmin) * l1 (dualVec kb n)) := by
        have hM0 : 0 ≤ M := Finset.prod_nonneg fun v _ => by
          have : 0 ≤ ∫ u : ℝ, (1 + u ^ 2)⁻¹ := integral_nonneg fun u => by positivity
          positivity
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM0
        simp only [l1]
        rw [Finset.mul_sum, Finset.mul_sum]
        have : ∑ v, π * hmin * |dualVec kb n v| ≤ ∑ v, π * (|dualVec kb n v| * |h v|) :=
          Finset.sum_le_sum fun v _ => by
            have := mul_le_mul_of_nonneg_left (hhminv v) (abs_nonneg (dualVec kb n v))
            nlinarith [Real.pi_pos, abs_nonneg (dualVec kb n v)]
        have e1 : ∑ v, -(π * hmin) * |dualVec kb n v| = -∑ v, π * hmin * |dualVec kb n v| := by
          rw [← Finset.sum_neg_distrib]; congr 1; funext v; ring
        have e2 : ∑ v, -π * (|dualVec kb n v| * |h v|) = -∑ v, π * (|dualVec kb n v| * |h v|) := by
          rw [← Finset.sum_neg_distrib]; congr 1; funext v; ring
        rw [e1, e2]; linarith

/-- **Lipschitz's formula over $\mathcal O_F$** ($k \ge 3$, $z \in \mathbb H^d$, $u \in F$): with $\nu_m$ the dual lattice vectors,
$$\sum_m N(z + u + b_m)^{-k} = \sum_m c_{\mathcal O}\Big(\prod_vT_{k,0}(\nu_{m,v}, y_v)\Big)e(\langle\nu_m, x\rangle)\,e(\langle\nu_m, \sigma(u)\rangle),$$
$z = x + iy$, $T_{k,0}$ = `lineFT k 0`, the left side as `heckeTerm` with the weight $1$ (row $c = 1$). -/
theorem hasSum_lipschitz {k : ℕ} (hk : 3 ≤ k) (u : F) (z : InfinitePlace F → ℍ) :
    HasSum (fun m : Fin (Module.finrank ℚ F) → ℤ =>
        (latConst (oBasis F) : ℂ) * ((∏ v, lineFT k 0 (dualVec (oBasis F) m v) (z v).im) *
          cexp (2 * π * Complex.I * (pair (dualVec (oBasis F) m) (fun v => (z v).re) : ℂ))) *
            cexp (2 * π * Complex.I * (pair (dualVec (oBasis F) m) (realVec u) : ℂ)))
      (∑' m : Fin (Module.finrank ℚ F) → ℤ,
        heckeTerm (fun _ => (1 : ℂ)) k 0 ((1 : F), u + oElt m) (fun v => (z v : ℂ))) := by
  classical
  set kb := oBasis F with hkb
  set a : InfinitePlace F → ℝ := fun v => (z v).re with ha
  set h : InfinitePlace F → ℝ := fun v => (z v).im with hh_def
  have hh : ∀ v, h v ≠ 0 := fun v => (z v).im_pos.ne'
  have hk2 : 2 ≤ k := by omega
  obtain ⟨ymin, hymin, hyminv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  have hterm : ∀ m, heckeTerm (fun _ => (1 : ℂ)) k 0 ((1 : F), u + oElt m) (fun v => (z v : ℂ)) =
      rowPhi k 0 a h (realVec u + kb.equivFun.symm fun j => (m j : ℝ)) := by
    intro m
    rw [heckeTerm_one_eq_rowPhi, realVec_add, hkb, koecherBasis_symm]
  simp_rw [hterm]
  have hFT : ∀ ν : InfinitePlace F → ℝ, ∫ x, rowPhi k 0 a h x * cexp (-(2 * π * Complex.I) * (pair ν x : ℂ)) =
      (∏ v, lineFT k 0 (ν v) (h v)) * cexp (2 * π * Complex.I * (pair ν a : ℂ)) :=
    fun ν => integral_rowPhi_mul_exp k 0 a h ν
  have hP := hasSum_lattice_fourier kb (continuous_rowPhi k 0 a hh)
    (integrable_rowPhi hk2 le_rfl zero_le_one a hh) (realVec u) ?_ ?_
  · simp_rw [hFT] at hP
    exact hP
  · -- local uniform summability, from the row majorant at shifted points
    intro R
    set Cop := ‖(kb.equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
      (InfinitePlace F → ℝ))‖
    set A' := ∑ v, |(z v).re| + ∑ v, |realEmb F v u| + Cop * |R| + 1
    have hks : 2 < (k : ℝ) + 2 * 0 := by norm_num; omega
    obtain ⟨U, hU, hU0, hUb⟩ := exists_row_majorant (one_ne_zero (α := F)) hks A' hymin
    refine ⟨fun m => U (oElt m), hU.comp_injective (latElt_injective _), fun t ht m => ?_⟩
    set δ := kb.equivFun.symm t
    set z' : InfinitePlace F → ℍ := fun v => (realEmb F v u + δ v) +ᵥ z v
    obtain ⟨e, he⟩ := oElt_mem m
    have hΦeq : rowPhi k 0 a h (realVec u + kb.equivFun.symm (t + fun j => (m j : ℝ))) =
        heckeTerm (fun _ => (1 : ℂ)) k 0 ((1 : F), ιO e) fun v => (z' v : ℂ) := by
      rw [heckeTerm_one_eq_rowPhi, he, map_add, hkb, koecherBasis_symm]
      simp only [rowPhi]
      refine Finset.prod_congr rfl fun v _ => ?_
      congr 2
      · congr 1
        simp only [z', δ, UpperHalfPlane.vadd_re, Pi.add_apply, realVec, hkb, ha]
        ring
      · simp only [z', UpperHalfPlane.vadd_im, hh_def]
    rw [hΦeq, norm_heckeTerm_of_fst one_ne_zero, norm_one, one_mul]
    show _ ≤ U (oElt m)
    rw [← he]
    refine hUb z' (fun v => ⟨?_, ?_⟩) e
    · have hre : (z' v).re = (z v).re + (realEmb F v u + δ v) := by
        simp only [z', UpperHalfPlane.vadd_re]; ring
      rw [hre]
      have hδ : |δ v| ≤ Cop * |R| := by
        refine (norm_le_pi_norm δ v).trans ?_
        calc ‖δ‖ = ‖(kb.equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
              (InfinitePlace F → ℝ)) t‖ := rfl
          _ ≤ Cop * ‖t‖ := ContinuousLinearMap.le_opNorm _ t
          _ ≤ Cop * |R| := by gcongr; exact ht.trans (le_abs_self R)
      have h2 := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ v)
      have h3 := Finset.single_le_sum (f := fun v => |realEmb F v u|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ v)
      have h4 := abs_add_le (z v).re (realEmb F v u + δ v)
      have h5 := abs_add_le (realEmb F v u) (δ v)
      simp only [A']; linarith
    · show ymin ≤ (z' v).im
      simp only [z', UpperHalfPlane.vadd_im]; exact (hyminv v).le
  · -- summability of the transforms: exponential decay
    refine (summable_norm_prod_lineFT hk z).congr fun n => ?_
    rw [hFT, norm_mul, show (2 * π * Complex.I * (pair (dualVec kb n) a : ℂ)) =
      ((2 * π * pair (dualVec kb n) a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ### The theta constant at the cusp $-u$ is a normalized Gauss sum -/

/-- **The archimedean and lattice constant of the theta series**:
$K_Q = \big(\prod_v\sqrt{\det\sigma_v(A_Q)}\big)^{-1}\,\Delta(\mathcal O_F)^{-n}$, $A_Q = H/2$ the Gram matrix and
$\Delta(\mathcal O_F) = \sqrt{d_F}$ the covolume of $\sigma(\mathcal O_F)$ (`embDet_one`). -/
def thetaK (Q : QuadForm (𝓞 F) n) : ℝ :=
  (∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ * (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹

/-- $N((c)) = \prod_v|\sigma_v(c)|$ for $c \in \mathcal O_F$ ($F$ totally real). -/
lemma absNorm_span_eq_prod_abs (c : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {c}) : ℝ) = ∏ v, |realEmb F v (ιO c)| := by
  rw [QuadFormsKB.Siegel.absNorm_span_eq_abs_norm, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, IsTotallyReal.isReal v]
  rw [hm, pow_one, abs_realEmb]

lemma eTrO_eq_eTr (y c : 𝓞 F) : eTrO y c = SiegelWeil.SingularNF.eTr (ιO y / ιO c) := rfl

/-- **The theta constant term at a cusp of denominator $D$, through the Gauss average**: if $D \ne 0$, $a = Du$, $c = -D$
($a, c, D \in \mathcal O_F$, $u \in F$) and $n = 2k$, then
$$K_Q\prod_v\Big(\frac{-i}{2\sigma_v(c)\sigma_v(D)}\Big)^kG_Q(a, 0, c) = K_Q\Big(\frac i2\Big)^{kd}\,G_Q(-u),$$
$G_Q(a, 0, c)$ = `gaussSumF` and $G_Q(-u)$ = `SingularNF.gaussAvg` the normalized Gauss sum. -/
theorem thetaCuspConst_mul_gaussSumF {Q : QuadForm (𝓞 F) n} {k : ℕ} (hn : n = 2 * k) {D a c : 𝓞 F}
    (hD : D ≠ 0) {u : F} (ha : ιO a = ιO D * u) (hc : ιO c = ιO D * (-1)) :
    thetaCuspConst Q k D c * gaussSumF Q a c 0 =
      (thetaK Q : ℂ) * (Complex.I / 2) ^ (k * Fintype.card (InfinitePlace F)) *
        SiegelWeil.SingularNF.gaussAvg Q (-u) := by
  classical
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc
    have := SiegelWeil.SingularNF.algebraMap_ne_zero hD
    exact this (by linear_combination hc)
  have hcD : ιO c = -ιO D := by rw [hc]; ring
  have hden : SiegelWeil.SingularNF.IsDen c (-u) := ⟨a, by rw [ha, hcD]; ring⟩
  haveI := SiegelWeil.SingularNF.finite_quot_span hc0
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  -- the Gauss sum as N(c)^n times the Gauss average
  have hG : gaussSumF Q a c 0 = ((Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n) *
      SiegelWeil.SingularNF.gaussAvg Q (-u) := by
    rw [SiegelWeil.SingularNF.gaussAvg_eq Q hc0 hden, SiegelWeil.SingularNF.gAvg, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (by
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact SiegelWeil.SingularNF.span_ne_bot hc0)),
      one_mul, gaussSumF_eq_sum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [gsTermF_zero_eq, eTrO_eq_eTr]
    have h1 : ιO (a * Q.eval fun i => qlift (r i)) / ιO c = -u * ιO (Q.eval fun i => qlift (r i)) := by
      have hD' := SiegelWeil.SingularNF.algebraMap_ne_zero hD
      rw [map_mul, ha, hcD]; field_simp
    rw [h1]
    refine SiegelWeil.SingularNF.eTr_eval_congr Q hden fun i => ?_
    rw [mk_qlift]; simp [SiegelWeil.SingularNF.liftV]
  rw [hG, thetaCuspConst]
  have hσ : ∀ v, (realEmb F v (ιO c) : ℂ) = -(realEmb F v (ιO D) : ℂ) := fun v => by
    rw [hcD, map_neg, Complex.ofReal_neg]
  have hDv : ∀ v, (realEmb F v (ιO D) : ℂ) ≠ 0 := fun v => by
    rw [Complex.ofReal_ne_zero]
    exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr (SiegelWeil.SingularNF.algebraMap_ne_zero hD)
  have hN : (Ideal.absNorm (Ideal.span {c}) : ℂ) ^ n = ∏ v, ((realEmb F v (ιO D) : ℂ) ^ 2) ^ k := by
    have h := absNorm_span_eq_prod_abs c
    have h' : ((Ideal.absNorm (Ideal.span {c}) : ℝ) : ℂ) = ((∏ v, |realEmb F v (ιO c)| : ℝ) : ℂ) := by rw [h]
    push_cast at h'
    rw [h', hn, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [pow_mul, ← Complex.ofReal_pow, sq_abs, hcD, map_neg, neg_sq, Complex.ofReal_pow]
  rw [hN, thetaK]
  simp_rw [hσ]
  rw [show (Complex.I / 2) ^ (k * Fintype.card (InfinitePlace F)) =
      ∏ v : InfinitePlace F, (Complex.I / 2) ^ k by
    rw [Finset.prod_const, Finset.card_univ, pow_mul]]
  have : ∀ v : InfinitePlace F, (-Complex.I / (2 * -(realEmb F v (ιO D) : ℂ) * (realEmb F v (ιO D) : ℂ))) ^ k *
      ((realEmb F v (ιO D) : ℂ) ^ 2) ^ k = (Complex.I / 2) ^ k := by
    intro v
    rw [← mul_pow]
    congr 1
    field_simp [hDv v]
  rw [mul_assoc, mul_assoc, ← mul_assoc (∏ v, _), ← Finset.prod_mul_distrib]
  simp_rw [this]

/-- **The theta constant term at the cusp $-u$** ($n = 2k$): with $A_u$ = `cuspMat u (-1)` (first column $(u, -1)$, so
$A_u\infty = -u$),
$$\mathrm{c}_{\theta_Q}(A_u) = K_Q\Big(\frac i2\Big)^{kd}\,G_Q(-u).$$ -/
@[kb "siegel1935" "constant term of θ_Q at the cusp −u as a normalized Gauss sum, over F [unverified]"]
theorem thetaCuspVal_cuspMat {Q : QuadForm (𝓞 F) n} {k : ℕ} (hn : n = 2 * k) (u : F) :
    thetaCuspVal Q k (cuspMat u (-1)) =
      (thetaK Q : ℂ) * (Complex.I / 2) ^ (k * Fintype.card (InfinitePlace F)) *
        SiegelWeil.SingularNF.gaussAvg Q (-u) := by
  obtain ⟨c0, c1⟩ := cuspMat_col (α := u) (γ := (-1 : F)) (Or.inr (neg_ne_zero.mpr one_ne_zero))
  unfold thetaCuspVal
  split_ifs with h0
  · exact absurd (h0.symm.trans c1) (by norm_num)
  set A := cuspMat u (-1 : F)
  have hD := (exists_cuspDenom A).choose_spec.1
  have ha := (exists_cuspDenom A).choose_spec.2.choose_spec.choose_spec.1
  have hc := (exists_cuspDenom A).choose_spec.2.choose_spec.choose_spec.2
  exact thetaCuspConst_mul_gaussSumF hn hD (ha.trans (congrArg _ c0)) (hc.trans (congrArg _ c1))

/-! ### Reduced vectors with $c \ne 0$ are indexed by $F$ -/

/-- The scalar $t_u$ with $t_u(1, u)$ reduced (`exists_isRedVec_smul`). -/
def redT (u : F) : F := (exists_isRedVec_smul (x := ((1 : F), u)) (Or.inl one_ne_zero)).choose

lemma redT_ne_zero (u : F) : redT u ≠ 0 :=
  (exists_isRedVec_smul (x := ((1 : F), u)) (Or.inl one_ne_zero)).choose_spec.1

lemma isRedVec_redT (u : F) : IsRedVec (redT u * 1, redT u * u) :=
  (exists_isRedVec_smul (x := ((1 : F), u)) (Or.inl one_ne_zero)).choose_spec.2

/-- **The orbit of the reduced vector with ratio $u$**: $U\cdot t_u(1, u)$, the unique reduced orbit $(c, d)$ with $d/c = u$. -/
def rho (u : F) : UOrbit F := Quotient.mk _ (redT u * 1, redT u * u)

lemma rho_injective : Function.Injective (rho (F := F)) := by
  intro u u' h
  obtain ⟨ε, hε⟩ := orbitRel_iff.mp (Quotient.exact h)
  have h1 : (ε : F) * (redT u' * 1) = redT u * 1 := by have := congrArg Prod.fst hε; rwa [smul_fst] at this
  have h2 : (ε : F) * (redT u' * u') = redT u * u := by have := congrArg Prod.snd hε; rwa [smul_snd] at this
  have ht : redT u ≠ 0 := redT_ne_zero u
  simp only [mul_one] at h1
  rw [← mul_assoc, h1] at h2
  exact (mul_left_cancel₀ ht h2).symm

lemma rho_out_fst_ne_zero (u : F) : (rho u).out.1 ≠ 0 := by
  obtain ⟨ε, hε⟩ := exists_smul_out (redT u * 1, redT u * u)
  rw [rho, ← hε, smul_fst]
  refine mul_ne_zero ?_ (by rw [mul_one]; exact redT_ne_zero u)
  exact (map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero

lemma eisDen_smul_scalar (t : F) (x : F × F) (Z : InfinitePlace F → ℂ) :
    eisDen (t * x.1, t * x.2) Z = (∏ v, (realEmb F v t : ℂ)) * eisDen x Z := by
  simp only [eisDen, map_mul, ofReal_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => by ring

variable {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ}

/-- **The term of $E_f$ at the reduced orbit with ratio $u$**: $W_f(\rho(u))N(\rho(u)z)^{-k} = \varphi_f(1, u)\,N(z + u)^{-k}$. -/
theorem eisTerm_rho (hf : HasCuspLimits f k) (u : F) (Z : InfinitePlace F → ℂ) :
    eisTerm (eisGenWeight f k) k (rho u).out Z = phiF f k ((1 : F), u) * eisDen ((1 : F), u) Z ^ (-k) := by
  obtain ⟨ε, hε⟩ := exists_smul_out (redT u * 1, redT u * u)
  rw [rho, ← hε, eisTerm_smul (isUnitEquivariant_eisGenWeight hf), eisTerm,
    eisGenWeight_of_red (isRedVec_redT u)]
  have ht := redT_ne_zero u
  have hN := prod_realEmb_ne_zero ht
  rw [show (redT u * 1, redT u * u) = (redT u * ((1 : F), u).1, redT u * ((1 : F), u).2) from rfl,
    phiF_smul hf (Or.inl one_ne_zero) ht, eisDen_smul_scalar, mul_zpow]
  have h1 : (∏ v, (realEmb F v (redT u) : ℂ)) ^ k * (∏ v, (realEmb F v (redT u) : ℂ)) ^ (-k) = 1 := by
    rw [← zpow_add₀ hN, add_neg_cancel, zpow_zero]
  linear_combination (phiF f k ((1 : F), u) * eisDen ((1 : F), u) Z ^ (-k)) * h1

/-- **The Eisenstein series of a weight supported on reduced vectors, as a sum over $F$** (absolute convergence assumed):
$E_{W,k}(z) = \mathrm{c}_\infty(W) + \sum_{u\in F}W(\rho(u))N(\rho(u)z)^{-k}$. -/
theorem eisSeriesC_eq_const_add (Z : InfinitePlace F → ℂ)
    (hsum : Summable fun o : UOrbit F => ‖eisTerm (eisGenWeight f k) k o.out Z‖) :
    eisSeriesC (eisGenWeight f k) k Z = eisConst (eisGenWeight f k) k +
      ∑' u : F, eisTerm (eisGenWeight f k) k (rho u).out Z := by
  classical
  set W := eisGenWeight f k
  set g : UOrbit F → ℂ := fun o => eisTerm W k o.out Z
  have hs : Summable g := hsum.of_norm
  set f0 : UOrbit F → ℂ := fun o => if o.out.1 = 0 then g o else 0
  set f1 : UOrbit F → ℂ := fun o => if o.out.1 = 0 then 0 else g o
  have hs0 : Summable f0 := hs.indicator {o | o.out.1 = 0} |>.congr fun o => by
    simp only [f0, Set.indicator]; split_ifs <;> simp_all
  have hs1 : Summable f1 := hs.indicator {o | o.out.1 ≠ 0} |>.congr fun o => by
    simp only [f1, Set.indicator]; split_ifs <;> simp_all
  have hsplit : eisSeriesC W k Z = ∑' o, f0 o + ∑' o, f1 o := by
    rw [eisSeriesC, ← hs0.tsum_add hs1]
    congr 1; funext o; simp only [f0, f1, g]; split_ifs <;> simp
  rw [hsplit]
  congr 1
  · -- the `c = 0` part is the constant term
    rw [eisConst]
    refine tsum_congr fun o => ?_
    simp only [f0, g]
    split_ifs with h
    · rw [eisTerm, eisDen_of_fst_eq_zero h]
    · rfl
  · -- the rows: one reduced orbit per ratio `u = d/c`
    have hsupp : Function.support f1 ⊆ Set.range rho := by
      intro o ho
      have h1 : o.out.1 ≠ 0 := by intro h; exact ho (by simp only [f1, h, ↓reduceIte])
      have hW : W o.out ≠ 0 := by
        intro h; apply ho; simp only [f1, h1, ↓reduceIte, g, eisTerm, h, zero_mul]
      have hred : IsRedVec o.out := by
        by_contra h; exact hW (eisGenWeight_of_not_red h)
      set u := o.out.2 / o.out.1
      have hx : (o.out.1 * ((1 : F), u).1, o.out.1 * ((1 : F), u).2) = o.out := by
        refine Prod.ext (mul_one _) ?_
        simp only [u]; field_simp
      obtain ⟨ε, hε⟩ := isRedVec_smul_unique (x := ((1 : F), u)) (Or.inl one_ne_zero) (redT_ne_zero u) h1
        (isRedVec_redT u) (by rw [hx]; exact hred)
      refine ⟨u, ?_⟩
      conv_rhs => rw [← Quotient.out_eq o]
      refine (Quotient.sound (orbitRel_iff.mpr ⟨ε, ?_⟩)).symm
      rw [← hx]
      refine Prod.ext ?_ ?_
      · change ((ε : 𝓞 F) : F) * (redT u * 1) = o.out.1 * 1
        rw [← mul_assoc, hε]
      · change ((ε : 𝓞 F) : F) * (redT u * u) = o.out.1 * u
        rw [← mul_assoc, hε]
    rw [← rho_injective.tsum_eq hsupp]
    refine tsum_congr fun u => ?_
    simp only [f1, rho_out_fst_ne_zero u, ↓reduceIte, g]

/-! ### $F = F/\mathcal O \times \mathcal O$ -/

open SiegelWeil.SingularNF (FO OSub mem_OSub)

lemma oElt_mem_OSub (m : Fin (Module.finrank ℚ F) → ℤ) : oElt m ∈ OSub F := by
  obtain ⟨e, he⟩ := oElt_mem m
  exact mem_OSub.mpr ⟨e, he⟩

lemma mk_out_add_oElt (x : FO F) (m : Fin (Module.finrank ℚ F) → ℤ) :
    (QuotientAddGroup.mk (Quotient.out x + oElt m) : FO F) = x := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (oElt m)).mpr (oElt_mem_OSub m), add_zero]

lemma sub_out_mem_one (u : F) :
    u - Quotient.out (QuotientAddGroup.mk u : FO F) ∈
      (((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) : Set F) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk u : FO F)) : FO F) = QuotientAddGroup.mk u :=
    QuotientAddGroup.out_eq' _
  obtain ⟨b, hb⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  rw [Units.val_one, SetLike.mem_coe, FractionalIdeal.mem_one_iff]
  exact ⟨b, by rw [hb]; ring⟩

/-- **$F \cong F/\mathcal O \times \mathbb Z^d$**: $(x, m) \mapsto \tilde x + b_m$ ($\tilde x$ = `Quotient.out`). -/
def splitF : FO F × (Fin (Module.finrank ℚ F) → ℤ) ≃ F where
  toFun p := Quotient.out p.1 + oElt p.2
  invFun u := (QuotientAddGroup.mk u,
    (QuadFormsKB.Analysis.latEquiv (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)).symm ⟨_, sub_out_mem_one u⟩)
  left_inv p := by
    obtain ⟨x, m⟩ := p
    simp only
    have h1 := mk_out_add_oElt x m
    refine Prod.ext h1 ?_
    simp only
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [QuadFormsKB.Analysis.latEquiv_coe]
    simp only [h1, add_sub_cancel_left]
  right_inv u := by
    simp only
    rw [oElt, ← QuadFormsKB.Analysis.latEquiv_coe, Equiv.apply_symm_apply]
    simp

/-! ### Bounded representatives of $F/\mathcal O$ -/

/-- The representative of $x \in F/\mathcal O$ with coordinates in $[0, 1)$ for the basis of $\sigma(\mathcal O)$. -/
def bRep (x : FO F) : F :=
  Quotient.out x + oElt (fun j => -⌊(oBasis F).equivFun (realVec (Quotient.out x)) j⌋)

lemma mk_bRep (x : FO F) : (QuotientAddGroup.mk (bRep x) : FO F) = x := mk_out_add_oElt x _

lemma bRep_injective : Function.Injective (bRep (F := F)) := fun x x' h => by
  rw [← mk_bRep x, ← mk_bRep x', h]

/-- The representatives `bRep` are bounded: $|\sigma_v(\mathrm{bRep}(x))| \le C$ for a constant $C$. -/
lemma exists_bound_bRep : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : FO F) (v : InfinitePlace F), |realEmb F v (bRep x)| ≤ C := by
  set Cop := ‖((oBasis F).equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
      (InfinitePlace F → ℝ))‖
  refine ⟨Cop, norm_nonneg _, fun x v => ?_⟩
  set t := (oBasis F).equivFun (realVec (Quotient.out x))
  have hrv : realVec (bRep x) = (oBasis F).equivFun.symm (fun j => Int.fract (t j)) := by
    rw [bRep, realVec_add, oElt, ← koecherBasis_symm]
    have : realVec (Quotient.out x) = (oBasis F).equivFun.symm t := by simp [t]
    rw [this, ← map_add]
    congr 1
    funext j
    simp only [Pi.add_apply, Int.cast_neg, LinearEquiv.apply_symm_apply]
    rw [Int.fract]; ring
  have hle : ‖(fun j => Int.fract (t j) : Fin (Module.finrank ℚ F) → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  calc |realEmb F v (bRep x)| = |realVec (bRep x) v| := rfl
    _ ≤ ‖realVec (bRep x)‖ := by
        have := norm_le_pi_norm (realVec (bRep x)) v; rwa [Real.norm_eq_abs] at this
    _ = ‖((oBasis F).equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
          (InfinitePlace F → ℝ)) (fun j => Int.fract (t j))‖ := by rw [hrv]; rfl
    _ ≤ Cop * ‖(fun j => Int.fract (t j) : Fin (Module.finrank ℚ F) → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Cop * 1 := by gcongr
    _ = Cop := mul_one _

/-- **Summability over $F/\mathcal O$ from summability over $F$**: if $\sum_{u\in F}|g(u)|\,|N(z + u)|^{-k} < \infty$ and $g$ is
$\mathcal O$-periodic, then $\sum_{x\in F/\mathcal O}|g(\tilde x)| < \infty$. -/
theorem summable_FO_of_summable {g : F → ℂ} (hper : ∀ x : FO F, g (Quotient.out x) = g (bRep x))
    {k : ℕ} (z : InfinitePlace F → ℍ)
    (hs : Summable fun u : F => ‖g u‖ * ‖eisDen ((1 : F), u) (fun v => (z v : ℂ))‖ ^ (-(k : ℝ))) :
    Summable fun x : FO F => ‖g (Quotient.out x)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_bRep (F := F)
  set B := ∏ v : InfinitePlace F, (‖(z v : ℂ)‖ + C)
  have hBpos : 0 < B := Finset.prod_pos fun v _ => by
    have : 0 < ‖(z v : ℂ)‖ := norm_pos_iff.mpr (UpperHalfPlane.ne_zero (z v))
    linarith
  have hden : ∀ x : FO F, ‖eisDen ((1 : F), bRep x) (fun v => (z v : ℂ))‖ ≤ B := by
    intro x
    rw [eisDen, norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
    rw [map_one, ofReal_one, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hC x v]
  have hden0 : ∀ x : FO F, 0 < ‖eisDen ((1 : F), bRep x) (fun v => (z v : ℂ))‖ := fun x =>
    norm_pos_iff.mpr (eisDen_ne_zero_of_fst one_ne_zero _ z)
  refine ((hs.comp_injective bRep_injective).mul_left (B ^ (k : ℝ))).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun x => ?_
  simp only [Function.comp, hper x]
  have h1 : 1 ≤ B ^ (k : ℝ) * ‖eisDen ((1 : F), bRep x) (fun v => (z v : ℂ))‖ ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (hden0 x).le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos (hden0 x) _), one_mul]
    exact Real.rpow_le_rpow (hden0 x).le (hden x) (Nat.cast_nonneg k)
  calc ‖g (bRep x)‖ = ‖g (bRep x)‖ * 1 := (mul_one _).symm
    _ ≤ ‖g (bRep x)‖ * (B ^ (k : ℝ) * ‖eisDen ((1 : F), bRep x) (fun v => (z v : ℂ))‖ ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

lemma norm_eTr (x : F) : ‖SiegelWeil.SingularNF.eTr x‖ = 1 := by
  rw [SiegelWeil.SingularNF.eTr, show (2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) =
    ((2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- $G_Q$ is a function on $F/\mathcal O$. -/
lemma gaussAvg_congr_mk (Q : QuadForm (𝓞 F) n) {a b : F}
    (h : (QuotientAddGroup.mk a : FO F) = QuotientAddGroup.mk b) :
    SiegelWeil.SingularNF.gaussAvg Q a = SiegelWeil.SingularNF.gaussAvg Q b := by
  obtain ⟨e, he⟩ := mem_OSub.mp (QuotientAddGroup.eq.mp h)
  rw [show b = a + ιO e by rw [he]; ring, SiegelWeil.SingularNF.gaussAvg_add_int]

/-! ### The Lipschitz coefficients in exponential form -/

/-- **The Lipschitz coefficient** $\Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^d\prod_v\nu_v^{k-1}$ if $\nu \gg 0$, and $0$ otherwise. -/
def lipCoeff (k : ℕ) (ν : InfinitePlace F → ℝ) : ℂ :=
  if ∀ v, 0 < ν v then ((-2 * π * Complex.I) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) *
    ∏ v, ((ν v : ℂ) ^ (k - 1)) else 0

/-- $\prod_vT_{k,0}(\nu_v, y_v)\,e(\langle\nu, x\rangle) = $ `lipCoeff k ν` $\cdot\,e(\langle\nu, z\rangle)$ ($k \ge 2$, $z = x + iy$). -/
lemma prod_lineFT_mul_exp {k : ℕ} (hk : 2 ≤ k) (ν : InfinitePlace F → ℝ) (z : InfinitePlace F → ℍ) :
    (∏ v, lineFT k 0 (ν v) (z v).im) * cexp (2 * π * Complex.I * (pair ν (fun v => (z v).re) : ℂ)) =
      lipCoeff k ν * qTerm ν z := by
  have hh : ∀ v, (z v).im ≠ 0 := fun v => (z v).im_pos.ne'
  simp_rw [lineFT_zero_eq hk _ (hh _)]
  have hpos : ∀ v, (0 < ν v * (z v).im ↔ 0 < ν v) := fun v => mul_pos_iff_of_pos_right (z v).im_pos
  rw [lipCoeff]
  by_cases hall : ∀ v, 0 < ν v
  · rw [if_pos hall]
    have hall' : ∀ v, 0 < ν v * (z v).im := fun v => (hpos v).mpr (hall v)
    simp only [hall', ↓reduceIte, (z _).im_pos, ofReal_one, one_mul]
    rw [qTerm_eq]
    have hprod : ∏ v, ((-2 * π * Complex.I) ^ k / (k - 1).factorial * (ν v : ℂ) ^ (k - 1) *
        ((Real.exp (-2 * π * ν v * (z v).im)) : ℂ)) =
        ((-2 * π * Complex.I) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) *
          (∏ v, (ν v : ℂ) ^ (k - 1)) * ((Real.exp (-2 * π * pair ν (imVec z)) : ℝ) : ℂ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← ofReal_prod, ← Real.exp_sum]
      congr 3
      simp only [pair, imVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hprod, show reVec z = fun v => (z v).re from rfl]
    ring
  · rw [if_neg hall, zero_mul]
    push Not at hall
    obtain ⟨v₀, hv₀⟩ := hall
    have : ¬ 0 < ν v₀ * (z v₀).im := fun h => (not_lt.mpr hv₀) ((hpos v₀).mp h)
    rw [Finset.prod_eq_zero (Finset.mem_univ v₀) (by rw [if_neg this]), zero_mul]

lemma embDet_one_pos : 0 < embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) := by
  have h := embDet_sq_eq (F := F) 1
  rw [Units.val_one, FractionalIdeal.absNorm_one] at h
  simp only [Rat.cast_one, one_pow, one_mul] at h
  have h0 : embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) ≠ 0 := by
    intro h0; rw [h0] at h
    exact NumberField.discr_ne_zero F (by exact_mod_cast (by simpa using h.symm))
  exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)

/-! ### The covolume constant $c_{\mathcal O} = |d_F|^{-1/2}$ -/

/-- **The Lipschitz constant is the inverse covolume of $\sigma(\mathcal O_F)$**: $c_{\mathcal O} = \Delta(\mathcal O_F)^{-1}$, where
$c_{\mathcal O}$ = `latConst` is defined by $\sigma_*(\text{Lebesgue on coordinates}) = c_{\mathcal O}\cdot\text{Lebesgue}$. -/
theorem latConst_oBasis : (latConst (oBasis F) : ℝ) = (embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))⁻¹ := by
  classical
  set kb := oBasis F
  set L : (Fin (Module.finrank ℚ F) → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := kb.equivFun.symm.toLinearMap
  set e := LinearEquiv.funCongrLeft ℝ ℝ (placeEquiv (F := F))
  set M : (Fin (Module.finrank ℚ F) → ℝ) →ₗ[ℝ] (Fin (Module.finrank ℚ F) → ℝ) := e.toLinearMap ∘ₗ L
  -- the matrix of `M` is the embedding matrix of the basis of `𝓞`
  have hmat : LinearMap.toMatrix' M = embMat (QuadFormsKB.Analysis.bq (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) := by
    ext j l
    rw [LinearMap.toMatrix'_apply, embMat, Matrix.of_apply]
    simp only [M, L, e, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply]
    rw [Module.Basis.equivFun_symm_apply]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [koecherBasis_apply]
    rfl
  have hdet : LinearMap.det M = (embMat (QuadFormsKB.Analysis.bq (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))).det := by
    rw [← LinearMap.det_toMatrix', hmat]
  have hpos := embDet_one_pos (F := F)
  have hdet0 : LinearMap.det M ≠ 0 := by
    rw [hdet]; intro h; rw [embDet, h, abs_zero] at hpos; exact lt_irrefl _ hpos
  -- `e` preserves volume
  have he : MeasurePreserving (fun x : InfinitePlace F → ℝ => fun j => x (placeEquiv j)) volume volume := by
    have := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) (placeEquiv (F := F))).symm
    exact this
  -- two expressions for `M_* vol`
  have h1 : Measure.map M (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) =
      (latConst kb : ENNReal) • (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) := by
    have hL : Measure.map L (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) = latConst kb • volume :=
      map_basis_volume kb
    have hM : (M : (Fin (Module.finrank ℚ F) → ℝ) → (Fin (Module.finrank ℚ F) → ℝ)) =
        (fun x : InfinitePlace F → ℝ => fun j => x (placeEquiv j)) ∘ L := by
      funext x; rfl
    rw [hM, ← Measure.map_map he.measurable L.continuous_of_finiteDimensional.measurable, hL,
      Measure.map_smul, he.map_eq]
    · rfl
    · exact he.measurable.aemeasurable
  have h2 := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) hdet0
  rw [h1] at h2
  -- evaluate on the unit cube
  have hcube : (volume : Measure (Fin (Module.finrank ℚ F) → ℝ)) (Set.Icc 0 1) = 1 := by
    rw [Real.volume_Icc_pi]; simp
  have h3 := congrArg (fun μ : Measure (Fin (Module.finrank ℚ F) → ℝ) => μ (Set.Icc 0 1)) h2
  simp only [Measure.smul_apply, hcube, smul_eq_mul, mul_one] at h3
  have h4 : ((latConst kb : NNReal) : ℝ) = |(LinearMap.det M)⁻¹| := by
    have := congrArg ENNReal.toReal h3
    rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [h4, hdet, abs_inv, embDet]

/-- **$c_{\mathcal O} = d_F^{-1/2}$.** -/
theorem latConst_oBasis_eq : (latConst (oBasis F) : ℝ) = (Real.sqrt (NumberField.discr F : ℝ))⁻¹ := by
  rw [latConst_oBasis, embDet_one]

/-! ### The $q$-expansion of $E_Q$ -/

open QuadFormsKB.Lattices

/-- **The constant $C_Q = K_Q(i/2)^{kd}$** of the theta constant terms (`thetaCuspVal_cuspMat`). -/
def eisCst (Q₀ : QuadForm (𝓞 F) n) (k : ℕ) : ℂ :=
  (thetaK Q₀ : ℂ) * (Complex.I / 2) ^ (k * Fintype.card (InfinitePlace F))

/-- **The $\mu$-th Fourier coefficient of $E_Q$** ($\mu \in \mathfrak d^{-1}$), as given by its $q$-expansion (`hasSum_eisQ`,
`qCoeff_eisQ`):
$$a_{E_Q}(\mu) = C_Q\,c_{\mathcal O}\,\Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^d N(\mu)^{k-1}[\mu \gg 0]\cdot\mathfrak S_Q(\mu),$$
$C_Q = K_Q(i/2)^{kd}$ (`eisCst`), $c_{\mathcal O}$ = `latConst` of $\sigma(\mathcal O)$, $\mathfrak S_Q$ = `singSeries`. -/
@[kb "siegel1935" "the Fourier coefficients of the genus Eisenstein series over F, as a singular series [unverified]"]
def eisQCoeff (Q₀ : QuadForm (𝓞 F) n) (k : ℕ) (μ : F) : ℂ :=
  eisCst Q₀ k * (latConst (oBasis F) : ℂ) * lipCoeff k (realVec μ) * SiegelWeil.SingularNF.singSeries Q₀ μ

lemma thetaK_pos {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q₀)) : 0 < thetaK Q₀ := by
  unfold thetaK
  refine mul_pos (inv_pos.mpr (Finset.prod_pos fun v _ => Real.sqrt_pos.mpr (hQ v).det_pos))
    (inv_pos.mpr (Finset.prod_pos fun i _ => ?_))
  exact embDet_one_pos

lemma eisCst_ne_zero {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q₀)) (k : ℕ) : eisCst Q₀ k ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (thetaK_pos hQ).ne')
    (pow_ne_zero _ (div_ne_zero Complex.I_ne_zero two_ne_zero))

section QExp

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF Q₀) stdLat)

include hQ hn hlev h𝔑 hfree in
/-- The cusp values of $\theta_{\mathrm{Gen}}$ at $-u$: $\varphi(1, u) = C_QG_Q(-u)$. -/
lemma phiF_thetaGen (u : F) :
    phiF (thetaGen (formF Q₀) stdLat) (k : ℤ) ((1 : F), u) = eisCst Q₀ k * SiegelWeil.SingularNF.gaussAvg Q₀ (-u) := by
  rw [phiF, cuspVal_eq_of_tendsto (tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree _), thetaCuspVal_cuspMat hn,
    eisCst]

include hQ hn hlev h𝔑 hfree in
/-- The constant term of $E_Q$ at $\infty$ is $1$. -/
lemma eisConst_eisQ_eq_one :
    eisConst (eisGenWeight (thetaGen (formF Q₀) stdLat) (k : ℤ)) (k : ℤ) = 1 := by
  have h := eisConst_eisGenWeight (hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree) 1
  rw [slashWeight_one] at h
  rw [h, cuspVal_eq_of_tendsto (tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree _), thetaCuspVal]
  simp

include hQ hn hlev h𝔑 hfree in
/-- **The $q$-expansion of $E_Q$, with absolute convergence** ($k \ge 3$, $z \in \mathbb H^d$): the terms
$a_{E_Q}(\mu_m)e(\operatorname{Tr}\mu_mz)$ are absolutely summable, the singular series converges absolutely at every $\mu$,
and $E_Q(z) = 1 + \sum_ma_{E_Q}(\mu_m)e(\operatorname{Tr}\mu_mz)$. -/
theorem eisQ_qexp (hk : 3 ≤ k) (z : InfinitePlace F → ℍ) :
    (Summable fun m => ‖eisQCoeff Q₀ k (oDual m) * qTerm (realVec (oDual m)) z‖) ∧
      (∀ μ : F, Summable fun x => ‖SiegelWeil.SingularNF.ssFun Q₀ μ x‖) ∧
      HasSum (fun m => eisQCoeff Q₀ k (oDual m) * qTerm (realVec (oDual m)) z) (eisQ Q₀ k z - 1) := by
  classical
  set f := thetaGen (formF Q₀) stdLat
  set W := eisGenWeight f (k : ℤ)
  set C := eisCst Q₀ k
  have hf : HasCuspLimits f (k : ℤ) := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hW : EisWeight W (k : ℤ) :=
    eisWeight_eisGenWeight h𝔑 hf (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  have hQ' := isTotPosGram_Q₀ hQ
  have hC := eisCst_ne_zero hQ' k
  -- absolute convergence of the orbit sum at `z`
  have hsumO : Summable fun o : UOrbit F => ‖eisTerm W (k : ℤ) o.out (fun v => (z v : ℂ))‖ := by
    obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
    obtain ⟨h, hs, hb⟩ := exists_summable_bound_hecke hW (s := 0) (by norm_num; omega)
      (∑ v, |(z v).re| + 1) hB
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun o => ?_
    rw [← heckeTerm_zero]
    refine hb z (fun v => ⟨?_, (hBv v).le⟩) o
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith
  -- the terms over `F`
  set g : F → ℂ := fun u => SiegelWeil.SingularNF.gaussAvg Q₀ (-u)
  set b : F → ℂ := fun u => g u * eisDen ((1 : F), u) (fun v => (z v : ℂ)) ^ (-(k : ℤ))
  have hterm : ∀ u, eisTerm W (k : ℤ) (rho u).out (fun v => (z v : ℂ)) = C * b u := by
    intro u
    rw [eisTerm_rho hf, phiF_thetaGen hQ hn hlev h𝔑 hfree, mul_assoc]
  have hbsum : Summable fun u => ‖b u‖ := by
    have h1 := (hsumO.comp_injective rho_injective).mul_left ‖C‖⁻¹
    refine h1.congr fun u => ?_
    simp only [Function.comp, hterm, norm_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hC), one_mul]
  have hE : eisQ Q₀ k z = 1 + C * ∑' u, b u := by
    rw [eisQ, eisGen, eisSeries, eisSeriesC_eq_const_add (fun v => (z v : ℂ)) hsumO, eisConst_eisQ_eq_one hQ hn hlev h𝔑 hfree,
      tsum_congr hterm, tsum_mul_left]
  -- periodicity of the Gauss averages
  have hgper : ∀ (u : F) (m : Fin (Module.finrank ℚ F) → ℤ), g (u + oElt m) = g u := by
    intro u m
    obtain ⟨e, he⟩ := oElt_mem m
    simp only [g]
    rw [neg_add, ← he, ← map_neg, SiegelWeil.SingularNF.gaussAvg_add_int]
  -- the Lipschitz expansion of each coset sum
  set L : (Fin (Module.finrank ℚ F) → ℤ) → ℂ := fun m =>
    (latConst (oBasis F) : ℂ) * (lipCoeff k (realVec (oDual m)) * qTerm (realVec (oDual m)) z)
  set E : (Fin (Module.finrank ℚ F) → ℤ) → FO F → ℂ := fun m x =>
    SiegelWeil.SingularNF.eTr (oDual m * Quotient.out x)
  have hlip : ∀ x : FO F, HasSum (fun m => L m * E m x)
      (∑' m, eisDen ((1 : F), Quotient.out x + oElt m) (fun v => (z v : ℂ)) ^ (-(k : ℤ))) := by
    intro x
    have h := hasSum_lipschitz hk (Quotient.out x) z
    have hl : ∀ m, heckeTerm (fun _ => (1 : ℂ)) k 0 ((1 : F), Quotient.out x + oElt m) (fun v => (z v : ℂ)) =
        eisDen ((1 : F), Quotient.out x + oElt m) (fun v => (z v : ℂ)) ^ (-(k : ℤ)) := fun m => by
      rw [heckeTerm_zero, eisTerm, one_mul]
    simp_rw [hl] at h
    convert h using 2 with m
    simp only [L, E]
    rw [prod_lineFT_mul_exp (by omega), dualVec_oBasis, pair_realVec, SiegelWeil.SingularNF.eTr]
    push_cast
    ring
  -- the double sum
  have hgsum : Summable fun x : FO F => ‖g (Quotient.out x)‖ := by
    refine summable_FO_of_summable (k := k) (fun x => (hgper _ _).symm) z ?_
    refine hbsum.congr fun u => ?_
    simp only [b, norm_mul, _root_.zpow_neg, zpow_natCast, norm_inv, norm_pow]
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  have hLsum : Summable fun m => ‖L m‖ := by
    refine ((summable_norm_prod_lineFT hk z).mul_left (latConst (oBasis F) : ℝ)).congr fun m => ?_
    simp only [L]
    rw [← dualVec_oBasis, ← prod_lineFT_mul_exp (by omega), norm_mul, norm_mul,
      show (2 * π * Complex.I * (pair (dualVec (oBasis F) m) (fun v => (z v).re) : ℂ)) =
        ((2 * π * pair (dualVec (oBasis F) m) (fun v => (z v).re) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    simp
  have hE1 : ∀ m x, ‖E m x‖ = 1 := fun m x => by
    simp only [E, SiegelWeil.SingularNF.eTr]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F (oDual m * Quotient.out x) : ℚ) : ℂ)) =
      ((2 * Real.pi * ((Algebra.trace ℚ F (oDual m * Quotient.out x) : ℚ) : ℝ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hprod : Summable (Function.uncurry fun (x : FO F) (m : Fin (Module.finrank ℚ F) → ℤ) =>
      g (Quotient.out x) * (L m * E m x)) := by
    refine (summable_mul_of_summable_norm (f := fun x : FO F => ‖g (Quotient.out x)‖)
      (g := fun m => ‖L m‖) (by simpa using hgsum) (by simpa using hLsum)).of_norm_bounded ?_
    intro p
    simp only [Function.uncurry, norm_mul, hE1, mul_one]
    exact le_rfl
  -- assemble
  have hsplit : ∑' u, b u = ∑' x : FO F, ∑' m, g (Quotient.out x) * (L m * E m x) := by
    have hs : Summable fun p => b (splitF p) := (hbsum.of_norm).comp_injective splitF.injective
    rw [← splitF.tsum_eq, hs.tsum_prod' (fun x => hs.comp_injective (Prod.mk_right_injective x))]
    refine tsum_congr fun x => ?_
    simp only [splitF, Equiv.coe_fn_mk, b]
    simp_rw [hgper]
    rw [tsum_mul_left, tsum_mul_left, (hlip x).tsum_eq]
  have hswap : ∑' x : FO F, ∑' m, g (Quotient.out x) * (L m * E m x) =
      ∑' m, L m * SiegelWeil.SingularNF.singSeries Q₀ (oDual m) := by
    rw [← hprod.tsum_comm]
    refine tsum_congr fun m => ?_
    rw [SiegelWeil.SingularNF.singSeries, ← tsum_mul_left]
    conv_rhs => rw [← (Equiv.neg (FO F)).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply]
    have hmk : -x = (QuotientAddGroup.mk (-Quotient.out x) : FO F) := by
      rw [QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq']
    rw [hmk, SiegelWeil.SingularNF.ssFun_mk Q₀ (oDual_mem m)]
    simp only [g, E, neg_neg, mul_neg]
    ring
  -- the q-expansion
  have hcoeff : ∀ m, eisQCoeff Q₀ k (oDual m) * qTerm (realVec (oDual m)) z =
      C * (L m * SiegelWeil.SingularNF.singSeries Q₀ (oDual m)) := by
    intro m; simp only [eisQCoeff, L, C]; ring
  have hn1 : ∀ (μ : F) (x : FO F), ‖SiegelWeil.SingularNF.ssFun Q₀ μ x‖ = ‖g (Quotient.out (-x))‖ := by
      intro μ x
      rw [SiegelWeil.SingularNF.ssFun, norm_mul, norm_eTr, mul_one]
      simp only [g]
      have e1 : (QuotientAddGroup.mk (Quotient.out x) : FO F) = x := QuotientAddGroup.out_eq' x
      have e2 : (QuotientAddGroup.mk (-Quotient.out (-x)) : FO F) = x := by
        rw [QuotientAddGroup.mk_neg, QuotientAddGroup.out_eq' (-x), neg_neg]
      rw [gaussAvg_congr_mk Q₀ (e1.trans e2.symm)]
  have hs' : ∀ μ : F, Summable fun x : FO F => ‖SiegelWeil.SingularNF.ssFun Q₀ μ x‖ := by
    intro μ
    simp_rw [hn1 μ]
    exact (Equiv.neg (FO F)).summable_iff.mpr hgsum
  have hss : ∀ m, ‖SiegelWeil.SingularNF.singSeries Q₀ (oDual m)‖ ≤ ∑' x : FO F, ‖g (Quotient.out x)‖ := by
    intro m
    rw [SiegelWeil.SingularNF.singSeries]
    refine (norm_tsum_le_tsum_norm (hs' _)).trans (le_of_eq ?_)
    simp_rw [hn1 (oDual m)]
    exact (Equiv.neg (FO F)).tsum_eq (fun x => ‖g (Quotient.out x)‖)
  have hsumN : Summable fun m => ‖eisQCoeff Q₀ k (oDual m) * qTerm (realVec (oDual m)) z‖ := by
    refine ((hLsum.mul_right (∑' x : FO F, ‖g (Quotient.out x)‖)).mul_left ‖C‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun m => ?_
    rw [hcoeff, norm_mul, norm_mul]
    gcongr
    exact hss m
  refine ⟨hsumN, hs', ?_⟩
  convert hsumN.of_norm.hasSum using 1
  rw [hE, hsplit, hswap, add_sub_cancel_left, ← tsum_mul_left]
  exact tsum_congr fun m => (hcoeff m).symm

include hQ hn hlev h𝔑 hfree in
/-- **The $q$-expansion of $E_Q$** ($k \ge 3$): for every $z \in \mathbb H^d$,
$$E_Q(z) = 1 + \sum_{\mu\in\mathfrak d^{-1}}a_{E_Q}(\mu)\,e(\operatorname{Tr}\mu z)$$
(absolutely convergent; indexed by the coordinates $m$ of $\mu = \mu_m$ in the dual basis), with $a_{E_Q}$ = `eisQCoeff`. -/
@[kb "siegel1935" "the q-expansion of the genus Eisenstein series over F [unverified]"]
theorem hasSum_eisQ (hk : 3 ≤ k) (z : InfinitePlace F → ℍ) :
    HasSum (fun m => eisQCoeff Q₀ k (oDual m) * qTerm (realVec (oDual m)) z) (eisQ Q₀ k z - 1) :=
  (eisQ_qexp hQ hn hlev h𝔑 hfree hk z).2.2

include hQ hn hlev h𝔑 hfree in
/-- $E_Q$ is periodic for $\sigma(\mathcal O_F)$ (from its $q$-expansion: every frequency is in $\mathfrak d^{-1}$). -/
theorem isLatticePeriodic_eisQ (hk : 3 ≤ k) : IsLatticePeriodic (eisQ Q₀ k) (oBasis F) := by
  intro m x y hy
  have h1 := hasSum_eisQ hQ hn hlev h𝔑 hfree hk (ptXY (x + (oBasis F).equivFun.symm fun j => (m j : ℝ)) y)
  have h2 := hasSum_eisQ hQ hn hlev h𝔑 hfree hk (ptXY x y)
  have hq : ∀ n, qTerm (realVec (oDual n)) (ptXY (x + (oBasis F).equivFun.symm fun j => (m j : ℝ)) y) =
      qTerm (realVec (oDual n)) (ptXY x y) := by
    intro n
    rw [qTerm_eq, qTerm_eq, imVec_ptXY hy, imVec_ptXY hy, reVec_ptXY hy, reVec_ptXY hy, ← dualVec_oBasis,
      pair_add, pair_dualVec_symm]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    have : (2 * π * Complex.I * ∑ j, ((n j : ℂ)) * ((m j : ℂ))) =
        ((∑ j, n j * m j : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hq] at h1
  have := h1.unique h2
  linear_combination this

include hQ hn hlev h𝔑 hfree in
/-- **$a_{E_Q}(\mu)$ is the $\mu$-th Fourier coefficient of $E_Q$** ($k \ge 3$, $\mu \in \mathfrak d^{-1}\setminus 0$): with `qCoeff` (the coefficient defined by integration over $\mathbb R^d/\sigma(\mathcal O)$, normalized by $e(\operatorname{Tr}\mu z)$),
$$\mathrm{qCoeff}(E_Q, \mu) = a_{E_Q}(\mu)\quad(\texttt{eisQCoeff}).$$ -/
@[kb "siegel1935" "the Fourier coefficients of the genus Eisenstein series over F [unverified]"]
theorem qCoeff_eisQ (hk : 3 ≤ k) {m : Fin (Module.finrank ℚ F) → ℤ} (hm : m ≠ 0) :
    qCoeff (eisQ Q₀ k) (oBasis F) (dualVec (oBasis F) m) = eisQCoeff Q₀ k (oDual m) := by
  classical
  set f := thetaGen (formF Q₀) stdLat
  have hf : HasCuspLimits f (k : ℤ) := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hW : EisWeight (eisGenWeight f (k : ℤ)) (k : ℤ) :=
    eisWeight_eisGenWeight h𝔑 hf (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  have hhol : IsHolomorphic (eisQ Q₀ k) := isHolomorphic_eisSeries hW (by exact_mod_cast hk)
  set α : (Fin (Module.finrank ℚ F) → ℤ) → ℂ := fun n => eisQCoeff Q₀ k (oDual n) + if n = 0 then 1 else 0
  have hy : ∀ v : InfinitePlace F, (0 : ℝ) < (1 : InfinitePlace F → ℝ) v := fun _ => one_pos
  have hq0 : ∀ z : InfinitePlace F → ℍ, qTerm (dualVec (oBasis F) 0) z = 1 := fun z => by
    have : dualVec (oBasis F) 0 = 0 := by
      rw [dualVec]; convert map_zero (pairEquiv (oBasis F)).symm; simp
    rw [this, qTerm]; simp
  have hexp : ∀ x, HasSum (fun n => α n * qTerm (dualVec (oBasis F) n) (ptXY x 1)) (eisQ Q₀ k (ptXY x 1)) := by
    intro x
    have h := (hasSum_eisQ hQ hn hlev h𝔑 hfree hk (ptXY x 1)).add
      (hasSum_ite_eq (0 : Fin (Module.finrank ℚ F) → ℤ) (1 : ℂ))
    rw [sub_add_cancel] at h
    convert h using 1
    funext n
    simp only [α, add_mul, dualVec_oBasis]
    congr 1
    split_ifs with hn0
    · subst hn0; rw [one_mul, ← dualVec_oBasis, hq0]
    · rw [zero_mul]
  have hsum : Summable fun n => ‖α n‖ * Real.exp (-2 * π * pair (dualVec (oBasis F) n) 1) := by
    have h := (eisQ_qexp hQ hn hlev h𝔑 hfree hk (ptXY 0 1)).1
    have h' : Summable fun n : Fin (Module.finrank ℚ F) → ℤ =>
        ‖eisQCoeff Q₀ k (oDual n)‖ * Real.exp (-2 * π * pair (dualVec (oBasis F) n) 1) := by
      refine h.congr fun n => ?_
      rw [norm_mul, norm_qTerm, imVec_ptXY hy, dualVec_oBasis]
    have h0 : Summable fun n : Fin (Module.finrank ℚ F) → ℤ =>
        ‖(if n = 0 then (1 : ℂ) else 0)‖ * Real.exp (-2 * π * pair (dualVec (oBasis F) n) 1) := by
      refine (summable_of_ne_finset_zero (s := {0}) fun n hn => ?_)
      rw [Finset.mem_singleton] at hn
      simp [hn]
    refine (h'.add h0).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
  have hper := isLatticePeriodic_eisQ hQ hn hlev h𝔑 hfree hk
  have := qCoeff_unique hhol hper hy hsum hexp m
  rw [← this]
  simp [α, hm]

end QExp

end QuadFormsKB.HilbertModular
