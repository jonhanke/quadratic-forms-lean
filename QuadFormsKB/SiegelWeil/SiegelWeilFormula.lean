/-
# The Siegel–Weil formula in degree one over a totally real field

**Layer:** global, over a totally real number field $F$ of degree $d$; built on the Weil representation (`Weil/`), the Siegel
Eisenstein series of `SiegelWeil/Eisenstein.lean` and the classical Hilbert modular forms of `HilbertModular/`.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$ with $b_i \in \mathcal O_F$ totally positive, $n = 2m$ (0-based indices), $L = \mathcal O_F^n$,
$\Phi_f = \bigotimes_v\mathbf 1_{L_v}$, $\Phi_\infty$ the Gaussian; $s_0 = m - 1$; $z \in \mathbb H^d$, $y_w = \operatorname{Im}z_w$.

**Results.**
* `gammaV_inf_eq`: $\gamma_{V,\infty} = i^{md}$ ($Q$ totally positive); `cB_inf_eq`: $c_{B,\infty} = 2^{md}\prod_v\sqrt{\det A_v}$.
* `kappaF_eq`: the finite constant of the big cell is $\kappa_f = (-1)^{md}\,C_Q$, with $C_Q = K_Q(i/2)^{md}$ (`eisCst`).
* `archSec`, `isArchSection_archSec`: the archimedean section $f_\infty(\gamma g_z, s_0) = \prod_wy_w^{m/2}\prod_w(c_wz_w + d_w)^{-m}$ has the Borel law.
* **`eisenstein_archSec_eq_eisQ`**: $E(g_z, s_0, \Phi)$ converges absolutely and equals $\prod_wy_w^{m/2}E_Q(z)$ ($n \ge 6$, `GenusFree`).
* **`siegelWeil_formula`** (any class number; inputs `PrincipalPrimeSupply F` and the condition `GenusFree`) and
  **`siegelWeil_formula_of_pid`** ($h_F = 1$, unconditional): $E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\,\mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}\theta_M(z)/|O(M)|$.
* **`eisenstein_fourier_eq_whittaker`** (the unfolding at $s_0$): the $\nu$-th Fourier term of $E(g_z, s_0, \Phi)$ is $W_\infty(\nu, z)\prod_vW_v(\nu)$.

**Proof route** (Weil's, made explicit in degree one): Bruhat (`eisenstein_eq_bruhat`); the finite section on the big cell is a
Gauss average (`finSec_wMat_nMat`, local and purely finite); the constants by the product formulas (`globalConst_eq`) and the
archimedean Weil index; then the result is the Eisenstein series $E_Q$ term by term, and the comparison with the
theta series gives $E_Q = \theta_{\mathrm{Gen}}$.

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified];
Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Siegel, Ann. Math. 36 (1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.GaussIntegral
import QuadFormsKB.HilbertModular.SiegelFormulaNF
import QuadFormsKB.HilbertModular.SiegelFormulaNP

open IsDedekindDomain NumberField MeasureTheory Filter Complex
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups Classical
open NumberField.mixedEmbedding

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

open HilbertModular QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "RP" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ιO" => algebraMap (𝓞 F) F

/-! ### Real places -/

/-- For $F$ totally real a product over the real places is a product over all infinite places. -/
lemma prod_RP_eq {M : Type*} [CommMonoid M] (f : InfinitePlace F → M) :
    ∏ w : RP, f w.1 = ∏ v, f v :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun _ => rfl

lemma card_RP : Fintype.card RP = Fintype.card (InfinitePlace F) :=
  Fintype.card_congr (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v)

lemma ew_eq_realEmbF (w : RP) (x : F) : ew w x = realEmb F w.1 x := by
  rw [ew_eq_realEmb]; rfl

/-! ### The archimedean constants -/

variable {m : ℕ}

lemma cpow_half_inv_ofReal {x : ℝ} (hx : 0 < x) :
    ((x : ℂ)⁻¹) ^ (1 / 2 : ℂ) = ((Real.sqrt x : ℝ) : ℂ)⁻¹ := by
  have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, ← Complex.ofReal_inv, ← Complex.ofReal_cpow (inv_nonneg.mpr hx.le), Real.sqrt_eq_rpow,
    Real.inv_rpow hx.le, Complex.ofReal_inv]

/-- **The Weil index at infinity** for totally positive $Q$: $\gamma_{V,\infty} = i^{md}$. -/
@[kb "weil1964" "§14, Thm. 2 and §26 (the Weil index of a positive definite form at a real place) [unverified]"]
theorem gammaV_inf_eq (a : Fin (2 * m) → Fˣ) (hpos : ∀ i (w : RP), 0 < ew w (a i : F)) :
    (localDataInf (F := F)).gammaV (aInf a) = Complex.I ^ (m * Fintype.card (InfinitePlace F)) := by
  have hpos' : ∀ i (w : RP), 0 < (aInf a i : mixedSpace F).1 w :=
    fun i w => hpos i w
  have h := gammaV_mul_prod_C hpos' (fun _ => Complex.I) (fun _ => by simp)
  have hC : ∀ i, (Real.sqrt (mixedEmbedding.norm (2 * (aInf a i : mixedSpace F))) : ℂ) *
      ∏ w : RP, (-2 * Complex.I * ((((aInf a i : mixedSpace F).1 w : ℝ) : ℂ) * Complex.I))⁻¹ ^ (1 / 2 : ℂ) = 1 := by
    intro i
    set x : RP → ℝ := fun w => (aInf a i : mixedSpace F).1 w
    have hx : ∀ w, 0 < x w := hpos' i
    have e1 : ∀ w : RP, (-2 * Complex.I * (((x w : ℝ) : ℂ) * Complex.I))⁻¹ ^ (1 / 2 : ℂ) =
        ((Real.sqrt (2 * x w) : ℝ) : ℂ)⁻¹ := by
      intro w
      have : -2 * Complex.I * (((x w : ℝ) : ℂ) * Complex.I) = ((2 * x w : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [this, cpow_half_inv_ofReal (by linarith [hx w])]
    simp only [x] at e1
    rw [Finset.prod_congr rfl fun w _ => e1 w, Finset.prod_inv_distrib]
    have hN : mixedEmbedding.norm (2 * (aInf a i : mixedSpace F)) = ∏ w : RP, 2 * x w := by
      rw [norm_eq_prod_real]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [abs_of_pos]
      · rfl
      · show 0 < 2 * x w; linarith [hx w]
    rw [hN, ← real_sqrt_finset_prod _ _ (fun w => by linarith [hx w]), Complex.ofReal_prod,
      mul_inv_cancel₀]
    exact Finset.prod_ne_zero_iff.mpr fun w _ => by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr (by linarith [hx w])).ne'
  simp only [hC, Finset.prod_const_one, mul_one] at h
  rw [h]
  have hχ := chiV_mul_md_pow hpos' (-1 : mixedSpace F) (fun w => by
    rw [neg_one_fst]; norm_num)
  rw [md_neg_one_inf, Complex.ofReal_one, one_pow, mul_one] at hχ
  rw [hχ]
  simp only [neg_one_fst]
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, card_RP]
  push_cast
  rw [Complex.inv_I, ← pow_mul, ← pow_mul, ← mul_pow]
  congr 1; ring

/-! ### The finite constant of the big cell -/

lemma gramF_diag {n : ℕ} (b : Fin n → 𝓞 F) : gramF (QuadForm.diag b) = Matrix.diagonal fun i => ιO (b i) := by
  ext i j
  simp only [gramF, QuadForm.hessian, QuadForm.diag, Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h h' h'
  · subst h; rw [map_add]; ring
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · simp

/-- $\sqrt{\det}$ of the Gram matrix of $\sum_ib_ix_i^2$ at a real place: $\prod_i\sigma_v(b_i)$. -/
lemma det_gramF_diag {n : ℕ} (b : Fin n → 𝓞 F) (v : InfinitePlace F) :
    ((gramF (QuadForm.diag b)).map (realEmb F v)).det = ∏ i, realEmb F v (ιO (b i)) := by
  rw [gramF_diag, Matrix.diagonal_map (map_zero _), Matrix.det_diagonal]

/-- **The archimedean constant $c_{B,\infty}$** for $Q = \sum_ib_ix_i^2$ totally positive: $c_{B,\infty} = 2^{md}\prod_v\sqrt{\prod_i\sigma_v(b_i)}$. -/
lemma cB_inf_eq (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) :
    (localDataInf (F := F)).cB (aInf (unitsOfInt b hb)) =
      (((2 : ℝ) ^ (m * Fintype.card (InfinitePlace F)) *
        ∏ v, Real.sqrt (∏ i, realEmb F v (ιO (b i))) : ℝ) : ℂ) := by
  unfold LocalData.cB
  rw [← Complex.ofReal_prod]
  congr 1
  have hN : ∀ i, (localDataInf (F := F)).md (2 * ((aInf (unitsOfInt b hb) i : (mixedSpace F)ˣ) : mixedSpace F)) =
      ∏ v, 2 * realEmb F v (ιO (b i)) := by
    intro i
    show mixedEmbedding.norm _ = _
    rw [norm_eq_prod_real, ← prod_RP_eq]
    refine Finset.prod_congr rfl fun w _ => ?_
    have e : ((2 * ((aInf (unitsOfInt b hb) i : (mixedSpace F)ˣ) : mixedSpace F)).1 w) =
        2 * realEmb F w.1 (ιO (b i)) := by
      rw [← ew_eq_realEmbF]
      simp [aInf, unitsOfInt, ew_apply]
    rw [e, abs_of_pos (by linarith [hbpos i w.1])]
  simp_rw [hN]
  have h2 : ∀ i v, Real.sqrt (2 * realEmb F v (ιO (b i))) = Real.sqrt 2 * Real.sqrt (realEmb F v (ιO (b i))) :=
    fun i v => Real.sqrt_mul (by norm_num) _
  calc ∏ i, Real.sqrt (∏ v, 2 * realEmb F v (ιO (b i)))
      = ∏ i, ∏ v, (Real.sqrt 2 * Real.sqrt (realEmb F v (ιO (b i)))) :=
        Finset.prod_congr rfl fun i _ => by
          rw [← real_sqrt_finset_prod _ _ (fun v => by linarith [hbpos i v])]
          exact Finset.prod_congr rfl fun v _ => h2 i v
    _ = ∏ v, ((Real.sqrt 2) ^ (2 * m) * ∏ i, Real.sqrt (realEmb F v (ιO (b i)))) := by
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul, Real.sq_sqrt (by norm_num),
          ← pow_mul]
        congr 1
        exact Finset.prod_congr rfl fun v _ => real_sqrt_finset_prod _ _ fun i => (hbpos i v).le

/-- **The theta constant** $K_Q$ (`thetaK`) for $Q = \sum_ib_ix_i^2$: $K_Q = \big(\prod_v\sqrt{\prod_i\sigma_v(b_i)}\big)^{-1}d_F^{-m}$. -/
lemma thetaK_diag (b : Fin (2 * m) → 𝓞 F) :
    thetaK (QuadForm.diag b) = (∏ v, Real.sqrt (∏ i, realEmb F v (ιO (b i))))⁻¹ *
      ((Real.sqrt (discr F : ℝ)) ^ (2 * m))⁻¹ := by
  unfold thetaK
  simp_rw [det_gramF_diag]
  rw [show (∏ i : Fin (2 * m), embDet (oneIdeals (F := F) (n := 2 * m) i)) = Real.sqrt (discr F : ℝ) ^ (2 * m) by
    simp [oneIdeals, embDet_one]]

/-- **The finite constant of the big cell** (every finite place, dyadic included): for $Q = \sum_{i<n}b_ix_i^2$ totally
positive, $n = 2m \ge 2$,
$$\kappa_f = \prod_{v<\infty}\gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^n = (-1)^{md}\,C_Q,\qquad C_Q = K_Q\Big(\frac i2\Big)^{md}$$
(the constant of the theta series at the cusps, `eisCst`). *Proof:* $\gamma_{V,\infty}c_{B,\infty}\kappa_f = |d_F|^{-n/2}$
(`globalConst_eq` and $\prod_v\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}$), $\gamma_{V,\infty} = i^{md}$ (`gammaV_inf_eq`),
$c_{B,\infty} = 2^{md}\prod_v\sqrt{\det A_v}$ (`cB_inf_eq`), and $(2i)^{-1} = -i/2$. -/
@[kb "weil1965" "Ch. II–IV (the constants of Siegel's formula) [unverified]; Siegel (1935) [unverified]"]
theorem kappaF_eq (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) :
    kappaF m (unitsOfInt b hb) =
      (-1) ^ (m * Fintype.card (InfinitePlace F)) * eisCst (QuadForm.diag b) m := by
  set a := unitsOfInt b hb
  set d := Fintype.card (InfinitePlace F)
  set P : ℝ := ∏ v, Real.sqrt (∏ i, realEmb F v (ιO (b i)))
  have hP : 0 < P := Finset.prod_pos fun v _ => Real.sqrt_pos.mpr (Finset.prod_pos fun i _ => hbpos i v)
  have hD := discr_pos (F := F)
  set D : ℝ := Real.sqrt (discr F : ℝ)
  have hD0 : 0 < D := Real.sqrt_pos.mpr hD
  have hpos : ∀ i (w : RP), 0 < ew w (a i : F) := fun i w => by
    rw [ew_eq_realEmbF]; exact hbpos i w.1
  have hγ := gammaV_inf_eq a hpos
  have hc := cB_inf_eq b hb hbpos
  have hG := globalConst_eq a
  -- κ_f = C_f · ∏ vol(𝒪_v)
  have hvolC : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; exact_mod_cast h')
  have hvol1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hκ : kappaF m a = constFin a * ((D⁻¹ : ℝ) : ℂ) := by
    have hfv : (∏ᶠ v : HeightOneSpectrum (𝓞 F), (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ)) = ((D⁻¹ : ℝ) : ℂ) := by
      rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ)) =
        ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (selfDualV v).real (latticeV v 0) : ℝ) : ℂ) from
        (map_finprod Complex.ofRealHom (hasFiniteMulSupport_vol (F := F))).symm, finprod_vol]
      simp [D, abs_of_pos hD]
    have hsplit : kappaF m a = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ((localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
          (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ)) *
            (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) := by
      unfold kappaF
      refine finprod_congr fun v => ?_
      have h2m : 2 * m = (2 * m - 1) + 1 := by omega
      rw [h2m, pow_succ, Nat.add_sub_cancel]
      push_cast; ring
    have hA : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
          (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) :=
      ((hasFiniteMulSupport_gammaV a).mul (hasFiniteMulSupport_cB a)).mul hvol1
    rw [hsplit, finprod_mul_distrib hA hvolC, hfv]
    rfl
  rw [hκ, eisCst, thetaK_diag]
  rw [hγ, hc] at hG
  have hdD : (Real.sqrt |(discr F : ℝ)|)⁻¹ = D⁻¹ := by simp [D, abs_of_pos hD]
  rw [hdD] at hG
  have hI : (Complex.I : ℂ) ^ d ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hCf : constFin a = (((D⁻¹ ^ (2 * m - 1) : ℝ)) : ℂ) /
      (Complex.I ^ (m * d) * (((2 : ℝ) ^ (m * d) * P : ℝ) : ℂ)) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (by exact_mod_cast (by positivity :
      (0 : ℝ) < 2 ^ (m * d) * P).ne'))]
    rw [← hG]; ring
  rw [hCf]
  have key : (-1 : ℂ) ^ (m * d) * (Complex.I / 2) ^ (m * d) = ((2 * Complex.I) ^ (m * d))⁻¹ := by
    rw [← mul_pow, ← inv_pow]
    congr 1
    field_simp
    rw [Complex.I_sq]
    norm_num
  have hD0' : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
  have hP0' : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  calc (((D⁻¹ ^ (2 * m - 1) : ℝ)) : ℂ) / (Complex.I ^ (m * d) * (((2 : ℝ) ^ (m * d) * P : ℝ) : ℂ)) *
        ((D⁻¹ : ℝ) : ℂ)
      = ((2 * Complex.I) ^ (m * d))⁻¹ * ((P : ℂ)⁻¹ * ((D : ℂ) ^ (2 * m))⁻¹) := by
        rw [mul_pow]
        push_cast
        conv_rhs => rw [h2m, pow_succ]
        field_simp
        ring_nf
        rw [← mul_pow, mul_inv_cancel₀ hD0', one_pow]
    _ = (-1) ^ (m * d) * (((P⁻¹ * (D ^ (2 * m))⁻¹ : ℝ) : ℂ) * (Complex.I / 2) ^ (m * d)) := by
        rw [← key]; push_cast; ring

/-! ### The archimedean section at $s_0$ through $g_z$ -/

variable (m) in
/-- **The archimedean section at $s_0 = m - 1$ through $g_z$** ($z \in \mathbb H^d$):
$$f_\infty(\gamma g_z, s_0) = \prod_wy_w^{m/2}\cdot\prod_w(c_wz_w + d_w)^{-m},\qquad \gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F).$$
It is the Weil-representation section $(\omega_\infty(\gamma g_z)\varphi_\infty)(0)$ of the Gaussian $\varphi_\infty$: $\omega_\infty(g_z)\varphi_\infty =
\prod_wy_w^{m/2}G_z$ and $\omega_\infty(\gamma)G_z = \prod_w(c_wz_w + d_w)^{-m}G_{\gamma z}$ (`omegaG_inf_gOrb`), $G_{\gamma z}(0) = 1$. -/
@[kb "kudla2008" "§1 (the archimedean component of the standard section: weight m at s₀) [unverified]"]
def archSec (z : InfinitePlace F → UpperHalfPlane) (γ : SL(2, F)) : ℂ :=
  (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) *
    eisDen ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1) (fun v => (z v : ℂ)) ^ (-(m : ℤ))

/-- $Q_0 = \sum_ib_ix_i^2$ totally positive definite forces $b_i \gg 0$. -/
lemma pos_of_isTotallyPosDef {b : Fin (2 * m) → 𝓞 F} (hQ : IsTotallyPosDef (formF (QuadForm.diag b))) (i : Fin (2 * m))
    (v : InfinitePlace F) : 0 < realEmb F v (ιO (b i)) := by
  have h := isTotPosGram_Q₀ hQ v
  rw [gramF_diag, Matrix.diagonal_map (map_zero _)] at h
  simpa using h.diag_pos (i := i)

lemma bottom_nMat_mMat_mul (β : F) (t : Fˣ) (γ : SL(2, F)) :
    ((nMat β * mMat t * γ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = (t⁻¹ : Fˣ) * (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
    ((nMat β * mMat t * γ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = (t⁻¹ : Fˣ) * (γ : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  constructor <;>
    (simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [nMat, mMat, Matrix.mul_apply, Fin.sum_univ_two])

/-- **The archimedean section has the Borel law of $I(s_0, \chi_V)$**: $f_\infty(n(\beta)m(t)\gamma g_z) = \chi_{V,\infty}(t)|t|_\infty^{s_0+1}
f_\infty(\gamma g_z)$, so `archSec` is an `IsArchSection` at $s = s_0$. -/
theorem isArchSection_archSec (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (z : InfinitePlace F → UpperHalfPlane) :
    IsArchSection (unitsOfInt b hb) (archSec m z) ((m : ℂ) - 1) := by
  intro β t γ
  have hpos : ∀ i (w : RP), 0 < ((aInf (unitsOfInt b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w := fun i w => by
    show 0 < ew w _
    rw [ew_eq_realEmbF]; exact hbpos i w.1
  have hχ := chiV_mul_md_pow hpos (mixedEmbedding F (t : F)) (fun w => by
    rw [mixedEmbedding_fst]; exact (map_ne_zero _).mpr t.ne_zero)
  have hcp : ((mixedEmbedding.norm (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ ((m : ℂ) - 1 + 1) =
      (((localDataInf (F := F)).md (mixedEmbedding F (t : F)) : ℝ) : ℂ) ^ m := by
    rw [sub_add_cancel, Complex.cpow_natCast]; rfl
  rw [hcp, hχ]
  obtain ⟨h0, h1⟩ := bottom_nMat_mMat_mul β t γ
  unfold archSec
  rw [h0, h1, eisDen_smul_scalar (((t⁻¹ : Fˣ) : F))
    ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1), mul_zpow]
  simp_rw [mixedEmbedding_fst]
  have hRP : ∏ w : RP, ((ew w (t : F) : ℝ) : ℂ) ^ m = ∏ v, ((realEmb F v (t : F) : ℝ) : ℂ) ^ m := by
    rw [← prod_RP_eq]; exact Finset.prod_congr rfl fun w _ => by rw [ew_eq_realEmbF]
  rw [hRP]
  · have e : (∏ v, (realEmb F v ((t⁻¹ : Fˣ) : F) : ℂ)) ^ (-(m : ℤ)) = ∏ v, (realEmb F v (t : F) : ℂ) ^ m := by
      rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.ofReal_inv, inv_pow, inv_inv]
    rw [e]; ring

/-! ### The Siegel Eisenstein series at $s_0$ is $\prod_wy_w^{m/2}\,E_Q$ -/

/-- $f_\infty(g_z, s_0) = \prod_wy_w^{m/2}$. -/
lemma archSec_one (z : InfinitePlace F → UpperHalfPlane) :
    archSec m z 1 = ∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2) := by
  unfold archSec
  simp [eisDen]

/-- $f_\infty(wn(u)g_z, s_0) = (-1)^{md}\prod_wy_w^{m/2}\,N(z + u)^{-m}$ (the bottom row of $wn(u)$ is $(-1, -u)$). -/
lemma archSec_wMat_nMat (z : InfinitePlace F → UpperHalfPlane) (u : F) :
    archSec m z (wMat * nMat u) = (-1) ^ (m * Fintype.card (InfinitePlace F)) *
      ((∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * eisDen ((1 : F), u) (fun v => (z v : ℂ)) ^ (-(m : ℤ))) := by
  unfold archSec
  have h0 : ((wMat * nMat u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = (-1) * ((1 : F), u).1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [wMat, nMat, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ((wMat * nMat u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = (-1) * ((1 : F), u).2 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [wMat, nMat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h0, h1, eisDen_smul_scalar, mul_zpow]
  have e : (∏ v, (realEmb F v (-1 : F) : ℂ)) ^ (-(m : ℤ)) = (-1) ^ (m * Fintype.card (InfinitePlace F)) := by
    simp only [map_neg, map_one, Complex.ofReal_neg, Complex.ofReal_one, Finset.prod_const, Finset.card_univ]
    rw [zpow_neg, zpow_natCast, ← pow_mul, mul_comm, ← inv_pow, inv_neg, inv_one]
  rw [e]; ring

variable {b : Fin (2 * m) → 𝓞 F} (hb : ∀ i, b i ≠ 0) (hQ : IsTotallyPosDef (formF (QuadForm.diag b)))

include hQ in
/-- **The Siegel Eisenstein series at $s_0$ is $\prod_wy_w^{m/2}$ times the Eisenstein series of the genus** ($F$ totally real;
$Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m \ge 6$; $\mathfrak N \ne 0$ a theta level; the genus free,
`GenusFree`, which holds for $h_F = 1$). For $z \in \mathbb H^d$, the adelic series
$$E(g_z, s_0, \Phi) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma g_z, s_0)\,f_f(\gamma, s_0),\qquad \Phi = \varphi_\infty\otimes\textstyle\bigotimes_v\mathbf 1_{L_v},$$
converges absolutely (its big-cell terms are absolutely summable) and
$$E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\cdot E_Q(z),$$
$E_Q$ = `eisQ` (the Eisenstein series whose value at each cusp is the constant term of $\theta_{\mathrm{Gen}}$).
*Proof:* Bruhat (`eisenstein_eq_bruhat`); on the big cell $f_f(wn(u), s_0) = \kappa_fG_Q(-u)$ (`finSec_wMat_nMat`, a finite product of local
Gauss integrals), $\kappa_f = (-1)^{md}C_Q$ (`kappaF_eq`), and $f_\infty(wn(u)g_z) = (-1)^{md}\prod_wy_w^{m/2}N(z + u)^{-m}$; this is
$\prod_wy_w^{m/2}$ times the term of $E_Q$ at the cusp $-u$ (`eisTerm_rho`, `phiF_thetaGen`). -/
@[kb "weil1965" "Ch. II–IV (the Siegel Eisenstein series of the Weil representation, at s₀) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisenstein_archSec_eq_eisQ (hm : 3 ≤ m) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF (QuadForm.diag b) 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF (QuadForm.diag b)) stdLat) (z : InfinitePlace F → UpperHalfPlane) :
    (Summable fun u : F => ‖globalSec (unitsOfInt b hb) (archSec m z) ((m : ℂ) - 1) (wMat * nMat u)‖) ∧
      eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb (pos_of_isTotallyPosDef hQ) z) =
        (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * eisQ (QuadForm.diag b) m z := by
  classical
  set Q₀ := QuadForm.diag b
  have hn : 2 * m = 2 * m := rfl
  set f := thetaGen (formF Q₀) stdLat
  set W := eisGenWeight f (m : ℤ)
  set C := eisCst Q₀ m
  set Y := ∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)
  have hf : HasCuspLimits f (m : ℤ) := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hW : EisWeight W (m : ℤ) :=
    eisWeight_eisGenWeight h𝔑 hf (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  -- absolute convergence of the orbit sum at `z` (as in `eisQ_qexp`)
  have hsumO : Summable fun o : UOrbit F => ‖eisTerm W (m : ℤ) o.out (fun v => (z v : ℂ))‖ := by
    obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
    obtain ⟨h, hs, hbd⟩ := exists_summable_bound_hecke hW (s := 0) (by norm_num; omega)
      (∑ v, |(z v).re| + 1) hB
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun o => ?_
    rw [← heckeTerm_zero]
    refine hbd z (fun v => ⟨?_, (hBv v).le⟩) o
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith
  set g : F → ℂ := fun u => SingularNF.gaussAvg Q₀ (-u)
  set bt : F → ℂ := fun u => g u * eisDen ((1 : F), u) (fun v => (z v : ℂ)) ^ (-(m : ℤ))
  have hterm : ∀ u, eisTerm W (m : ℤ) (rho u).out (fun v => (z v : ℂ)) = C * bt u := by
    intro u
    rw [eisTerm_rho hf, phiF_thetaGen hQ hn hlev h𝔑 hfree, mul_assoc]
  have hC : C ≠ 0 := eisCst_ne_zero (isTotPosGram_Q₀ hQ) m
  have hbsum : Summable fun u => ‖bt u‖ := by
    have h1 := (hsumO.comp_injective rho_injective).mul_left ‖C‖⁻¹
    refine h1.congr fun u => ?_
    simp only [Function.comp, hterm, norm_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hC), one_mul]
  have hE : eisQ Q₀ m z = 1 + C * ∑' u, bt u := by
    rw [eisQ, eisGen, eisSeries, eisSeriesC_eq_const_add (fun v => (z v : ℂ)) hsumO,
      eisConst_eisQ_eq_one hQ hn hlev h𝔑 hfree, tsum_congr hterm, tsum_mul_left]
  -- the big-cell terms of the adelic series
  have hκ := kappaF_eq (by omega) b hb (pos_of_isTotallyPosDef hQ)
  have hglob : ∀ u : F, globalSec (unitsOfInt b hb) (archSec m z) ((m : ℂ) - 1) (wMat * nMat u) =
      Y * C * bt u := by
    intro u
    rw [globalSec, archSec_wMat_nMat, finSec_wMat_nMat, hκ]
    have hsq : ((-1 : ℂ) ^ (m * Fintype.card (InfinitePlace F))) * (-1) ^ (m * Fintype.card (InfinitePlace F)) = 1 := by
      rw [← mul_pow]; norm_num
    simp only [bt, g, C, Y]
    linear_combination (Y * C * bt u) * hsq
  have hsum : Summable fun u : F => ‖globalSec (unitsOfInt b hb) (archSec m z) ((m : ℂ) - 1) (wMat * nMat u)‖ := by
    refine (hbsum.mul_left ‖Y * C‖).congr fun u => ?_
    rw [hglob, norm_mul (Y * C)]
  refine ⟨hsum, ?_⟩
  rw [eisenstein_eq_bruhat _ _ hsum.of_norm, archSec_one, tsum_congr hglob, tsum_mul_left, hE]
  ring

/-! ### The Siegel–Weil formula -/

include hQ in
/-- **The Siegel–Weil formula in degree one, any class number** (given the named input `PrincipalPrimeSupply F` and the scope
condition `GenusFree`): for $F$ totally real, $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m \ge 6$,
$\Phi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L_v}$ and $z \in \mathbb H^d$,
$$E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\cdot\theta_{\mathrm{Gen}}(z),\qquad
  \theta_{\mathrm{Gen}} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M}{|O(M)|}:$$
the Eisenstein series of the Weil representation at $s_0 = n/2 - 1$ is the theta integral, in Siegel's form of the genus average
of the theta series. (`eisenstein_archSec_eq_eisQ` and $\theta_{\mathrm{Gen}} = E_Q$, `thetaGen_eq_eisQ'`.) -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula: Eisenstein series = theta integral), degree one, n ≥ 6 [unverified]; Siegel (1935), Hauptsatz [unverified]"]
theorem siegelWeil_formula (hm : 3 ≤ m) (hfree : GenusFree (formF (QuadForm.diag b)) stdLat)
    (hPS : PrincipalPrimeSupply F) (z : InfinitePlace F → UpperHalfPlane) :
    eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb (pos_of_isTotallyPosDef hQ) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * thetaGen (formF (QuadForm.diag b)) stdLat z := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [(eisenstein_archSec_eq_eisQ hb hQ hm hlev h𝔑 hfree z).2,
    thetaGen_eq_eisQ' hQ rfl hlev h𝔑 hPS hm]

include hQ in
/-- **The Siegel–Weil formula in degree one, class number one** (unconditional): for $F$ totally real with $\mathcal O_F$ a PID,
$Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m \ge 6$, and $z \in \mathbb H^d$,
$$E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\cdot\mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M(z)}{|O(M)|},$$
$E$ = `eisenstein` with the Weil-representation sections ($f_\infty$ = `archSec`, $f_v$ = `secS` of $\mathbf 1_{L_v}$), absolutely convergent. -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula), degree one, n ≥ 6, h_F = 1 [unverified]; Siegel (1935), Hauptsatz [unverified]"]
theorem siegelWeil_formula_of_pid [IsPrincipalIdealRing (𝓞 F)] (hm : 3 ≤ m) (z : InfinitePlace F → UpperHalfPlane) :
    eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb (pos_of_isTotallyPosDef hQ) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) *
        (((mass (formF (QuadForm.diag b)) stdLat : ℝ) : ℂ)⁻¹ *
          ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat (QuadForm.diag b))).toFinset,
            ((LatClass.autCard (formF (QuadForm.diag b)) c : ℂ))⁻¹ * thetaLatt (formF (QuadForm.diag b)) c.out.1 z) := by
  rw [siegelWeil_formula hb hQ hm (genusFree_of_isPrincipalIdealRing _ _) (principalPrimeSupply_of_pid F) z,
    thetaGen_eq_sum (genusClasses_finite hQ stdLat (isIntegral_stdLat (QuadForm.diag b)))]
  simp [Finset.sum_apply, smul_eq_mul]

/-! ### The Fourier coefficients of $E(g_z, s_0)$ are products of local Whittaker integrals (the unfolding at $s_0$) -/

include hQ in
/-- **The unfolding identity at $s_0$** ($F$ totally real, $Q_0 = \sum_ib_ix_i^2$ totally positive definite, $n = 2m \ge 6$, the genus free,
$\nu \in \mathcal O_F$ totally positive): the $\nu$-th Fourier term of $x \mapsto E(g_{x+iy}, s_0, \Phi)$ is the product of the local Whittaker
integrals,
$$\prod_wy_w^{m/2}\,a_\nu\,e\big(\textstyle\sum_w\sigma_w(\nu)z_w\big) = W_\infty(\nu, z)\cdot\prod_{v<\infty}W_v(\nu),$$
where $a_\nu$ is the $\nu$-th Fourier coefficient (`qCoeff`, normalized by $e(\operatorname{Tr}\nu z)$) of $z \mapsto E(g_z, s_0, \Phi)/\prod_wy_w^{m/2}$,
$W_\infty$ = `archWhittakerInf` and $W_v$ = `whittakerV` (the product converges, `HasProd`, to $C_f\prod_v\beta_v(\nu)$). This is Weil's
$E_\nu(g, s_0) = \prod_vW_v(\nu, g_v, s_0)$ in degree one at $g = (g_z, 1)$; it is proved through the Bruhat expansion, the local Gauss
integrals (`finSec_wMat_nMat`), Lipschitz's formula over $\mathcal O_F$ (the Poisson summation over $\mathfrak d^{-1}$) and the singular series. -/
@[kb "weil1965" "Ch. II–IV (the Fourier coefficients of the Eisenstein series as Euler products of local Whittaker integrals) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisenstein_fourier_eq_whittaker (hm : 3 ≤ m) (hfree : GenusFree (formF (QuadForm.diag b)) stdLat)
    {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) (z : InfinitePlace F → UpperHalfPlane) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerV v (aOfInt v b hb) ((LocalDensity.NF.ι v ν : v.adicCompletionIntegers F) : v.adicCompletion F))
      (constFin (unitsOfInt b hb) * Siegel.eulerProductNF (QuadForm.diag b) ν) ∧
    (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) *
        qCoeff (fun z' => eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb (pos_of_isTotallyPosDef hQ) z') /
          ∏ v, ((z' v).im : ℂ) ^ ((m : ℂ) / 2)) (oBasis F) (realVec (ιO ν)) *
        ∏ w : RP, Complex.exp (2 * Real.pi * Complex.I * ew w (ιO ν) * (z w.1 : ℂ)) =
      archWhittakerInf b hb (fun w : RP => (z w.1 : ℂ)) (ιO ν) *
        (constFin (unitsOfInt b hb) * Siegel.eulerProductNF (QuadForm.diag b) ν) := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have hbpos := pos_of_isTotallyPosDef hQ
  have hQnd : (QuadForm.diag b).Nondegenerate := det_hessian_ne_zero (isTotPosGram_Q₀ hQ)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa using hν v
  have hP := Siegel.hasProd_eulerProductNF_uncond hQnd (by omega : 4 ≤ 2 * m) hν0
  have hY : ∀ z' : InfinitePlace F → UpperHalfPlane, (∏ v, ((z' v).im : ℂ) ^ ((m : ℂ) / 2)) ≠ 0 := fun z' =>
    Finset.prod_ne_zero_iff.mpr fun v _ => by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (Complex.ofReal_ne_zero.mpr (z' v).im_pos.ne') h.1
  have hfun : (fun z' => eisenstein (unitsOfInt b hb) (isArchSection_archSec b hb hbpos z') /
      ∏ v, ((z' v).im : ℂ) ^ ((m : ℂ) / 2)) = eisQ (QuadForm.diag b) m := by
    funext z'
    rw [(eisenstein_archSec_eq_eisQ hb hQ hm hlev h𝔑 hfree z').2, mul_div_cancel_left₀ _ (hY z')]
  have hpos : ∀ (w : RP) i, 0 < ew w (b i : F) := fun w i => by rw [ew_eq_realEmbF]; exact hbpos i w.1
  have htpos : ∀ w : RP, 0 < ew w (ν : F) := fun w => by rw [ew_eq_realEmbF]; exact hν w.1
  obtain ⟨hW, hWeq⟩ := whittakerEuler_eq_siegel (by omega) b hb hpos ν hν0 htpos (fun w : RP => (z w.1 : ℂ))
    (fun w => (z w.1).im_pos) hP
  refine ⟨hW, ?_⟩
  rw [hWeq, hfun, eisQ_coeff_eq_discr_mul_aENF hQ rfl hlev h𝔑 hfree hm hν, Siegel.aENF, Siegel.aEWithNF,
    Siegel.betaInfNF]
  have hb2 : ∀ w : RP, Siegel.betaInfR (QuadForm.diag fun i => ew w (b i : F)) (ew w (ν : F)) =
      Siegel.betaInfAt (QuadForm.diag b) w (ν : F) := fun w => betaInfR_ew_eq_betaInfAt b w _
  simp_rw [hb2]
  rw [show 2 * m - 1 = 2 * m - 1 from rfl, ← prod_RP_eq (fun v => ((z v).im : ℂ) ^ ((m : ℂ) / 2))]
  push_cast
  simp only [Finset.prod_mul_distrib, UpperHalfPlane.coe_im]
  ring

end QuadFormsKB.SiegelWeil
