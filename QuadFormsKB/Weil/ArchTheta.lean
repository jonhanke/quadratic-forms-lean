/-
# The archimedean Gaussian orbit and the automorphy factor

**Layer:** local, archimedean, for a totally real field $F$ ($F_\infty = \mathbb R^d$; the complex places are empty).

**The Gaussian orbit.** For $V = \langle a_0, \dots, a_{2m-1}\rangle$ with $a_i \in F_\infty^\times$ totally positive
($a_{i,w} > 0$ at every real place $w$), and $\tau = (\tau_w)_w$ with $\operatorname{Im}\tau_w > 0$, let
$$G_\tau(x) = \prod_{i<2m}\prod_w e^{2\pi i\,a_{i,w}\tau_wx_{i,w}^2}\qquad(\texttt{gOrb}),$$
the image of the standard Gaussian $\varphi_\infty = G_{(i,\dots,i)}$ under $n(x)m(y^{1/2})$ up to the factor $\prod_wy_w^{m/2}$
(`borelInf_phiStd_inf`): $\omega_\infty(g_z)\varphi_\infty = \prod_wy_w^{m/2}\,G_z$, $g_z = n(x)m(y^{1/2})$.

**The generators on the orbit** (`opNf_gOrb`, `opMf_gOrb`, `opWf_gOrb`): $\omega_\infty(n(r))G_\tau = G_{\tau + r}$,
$\omega_\infty(m(t))G_\tau = \chi_V(t)|t|^mG_{t^2\tau}$, $\omega_\infty(w)G_\tau = \chi_V(-1)\prod_w\tau_w^{-m}\,G_{-1/\tau}$
(`gammaV_mul_prod_C`: the Weil index $\gamma_V$ and the $2m$ square roots $(-2ia_{i,w}\tau_w)^{-1/2}$ of the Gaussian
Fourier transforms combine to $\chi_V(-1)\prod_w\tau_w^{-m}$, *exactly*: $n = 2m$ is even, so no branch of a square
root survives).

**Archimedean equivariance** (`omegaG_inf_gOrb`): for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F)$ acting on
$F_\infty$ by the cell formula,
$$\omega_\infty(\gamma)\,G_z = \prod_w(c_wz_w + d_w)^{-m}\;G_{\gamma z},\qquad (\gamma z)_w = \frac{a_wz_w + b_w}{c_wz_w + d_w}.$$
This is the archimedean half of Route 2: it says that $\omega_\infty(\gamma g_z)\varphi_\infty = \omega_\infty(g_{\gamma z}k)\varphi_\infty$
with $k \in \mathrm{SO}_2(F_\infty)$ acting on $\varphi_\infty$ by the character
$\prod_w\big(\frac{|c_wz_w + d_w|}{c_wz_w + d_w}\big)^m$ of weight $m = n/2$; the two statements are equivalent (Iwasawa
$\gamma g_z = g_{\gamma z}k_\theta$), and the form proved here is the one needed for the theta law. The per-place identity behind
the scalar is $(t, (-1)^m\det V)_{\mathbb R}\,|t|^m = t^m$ (`hilbR_mul_abs_pow`), since $\det V$ has sign $(-1)^m$... i.e.
$(-1)^m\det V$ has sign $(-1)^m$ at every real place.

Sources: Weil, Acta Math. 111 (1964), §§14, 26 [unverified]; Kudla, *Notes on the local theta correspondence*
(1996), §I.4 (the Gaussian is the $K_\infty$-type of weight $n/2$) [unverified]; Bump (1997), §4.8 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.ThetaKernel

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Complex
open QuadFormsKB.Analysis
open scoped MatrixGroups Real Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "RP" => {w : InfinitePlace F // IsReal w}

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

/-! ### Complex Gaussians on $F_\infty$ -/

/-- **A complex Gaussian on $F_\infty$** with parameter $s = (s_w)_w$: $g_s(u) = \prod_we^{2\pi i\,s_wu_w^2}$. -/
def gs (s : RP → ℂ) (u : mixedSpace F) : ℂ := ∏ w, cexp (2 * π * I * s w * ((u.1 w : ℝ) : ℂ) ^ 2)

lemma chirpR_eq (β x : ℝ) : chirpR β x = cexp (2 * π * I * (β : ℂ) * (x : ℂ) ^ 2) := by
  rw [chirpR, fourierChar_coe]; push_cast; ring_nf

lemma chirp_gs (r : mixedSpace F) (s : RP → ℂ) :
    (localDataInf (F := F)).chirp r (gs s) = gs (fun w => s w + (r.1 w : ℂ)) := by
  funext u
  simp only [LocalData.chirp, ψInf_eq, gs]
  rw [show r * u ^ 2 = r * u * u by ring, psiInf_chirp_eq_prod]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [chirpR_eq, ← Complex.exp_add]
  congr 1; ring

lemma dil_gs (t : mixedSpace F) (s : RP → ℂ) :
    dil t (gs s) = gs (fun w => s w * ((t.1 w : ℝ) : ℂ) ^ 2) := by
  funext u
  simp only [dil, gs, Prod.fst_mul, Pi.mul_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1; push_cast; ring

/-- The Fourier transform of $g_s$, $\operatorname{Im}s_w > 0$:
$\hat g_s(\eta) = \prod_w(-2is_w)^{-1/2}e^{-\pi\eta_w^2/(-2is_w)}$. -/
lemma fourierInf_gs (s : RP → ℂ) (hs : ∀ w, 0 < (s w).im) (η : mixedSpace F) :
    fourierInf (gs s) η = ∏ w, (-2 * I * s w)⁻¹ ^ (1 / 2 : ℂ) *
      cexp (-π * ((η.1 w : ℝ) : ℂ) ^ 2 / (-2 * I * s w)) := by
  have hfun : gs s = fun x : mixedSpace F => (∏ w, (fun w (t : ℝ) => cexp (-(π * (-2 * I * s w)) * (t : ℂ) ^ 2))
      w (x.1 w)) * ∏ w : {w : InfinitePlace F // IsComplex w}, (fun _ (_ : ℂ) => (1 : ℂ)) w (x.2 w) := by
    funext x
    simp only [gs, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 1; ring_nf
  rw [hfun, fourierInf_prod (fun w (t : ℝ) => cexp (-(π * (-2 * I * s w)) * (t : ℂ) ^ 2)) (fun _ _ => 1)]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact fourierR_cexp_sq _ (by simpa using mul_pos two_pos (hs w)) _

/-- The modulus $|t|_\infty = \prod_w|t_w|$ ($F$ totally real). -/
lemma norm_eq_prod_real (t : mixedSpace F) : mixedEmbedding.norm t = ∏ w : RP, |t.1 w| := by
  rw [mixedEmbedding.norm_apply]
  refine (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => ?_).symm
  have hm : w.1.mult = 1 := by simp [mult, w.2]
  simp only [Equiv.subtypeUnivEquiv_apply, hm, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]

/-- $F_\alpha g_s = |2\alpha|^{1/2}\prod_w(-2is_w)^{-1/2}\;g_{-\alpha^2/s}$ ($\operatorname{Im}s_w > 0$). -/
lemma Fa_gs (α : mixedSpace F) (s : RP → ℂ) (hs : ∀ w, 0 < (s w).im) :
    (localDataInf (F := F)).Fa α (gs s) =
      ((Real.sqrt (mixedEmbedding.norm (2 * α)) : ℂ) * ∏ w, (-2 * I * s w)⁻¹ ^ (1 / 2 : ℂ)) •
        gs (fun w => -((α.1 w : ℝ) : ℂ) ^ 2 / s w) := by
  funext y
  simp only [LocalData.Fa, Pi.smul_apply, dil, localDataInf_four, smul_eq_mul, fourierInf_gs s hs]
  show (Real.sqrt (mixedEmbedding.norm (2 * α)) : ℂ) * _ = _
  rw [Finset.prod_mul_distrib, mul_assoc, gs]
  have key : ∀ w, cexp (-π * (((2 * (α * y)).1 w : ℝ) : ℂ) ^ 2 / (-2 * I * s w)) =
      cexp (2 * π * I * (-((α.1 w : ℝ) : ℂ) ^ 2 / s w) * ((y.1 w : ℝ) : ℂ) ^ 2) := fun w => ?_
  · simp only [key]; ring
  have hs0 : s w ≠ 0 := fun h => by have := hs w; rw [h] at this; simp at this
  congr 1
  simp only [Prod.fst_mul, Pi.mul_apply]
  have h2 : ((2 : mixedSpace F).1 w : ℝ) = 2 := rfl
  rw [h2]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-! ### The Gaussian orbit -/

variable {m : ℕ}

/-- **The Gaussian orbit** $G_\tau(x) = \prod_{i<2m}g_{a_i\tau}(x_i) = \prod_i\prod_we^{2\pi i\,a_{i,w}\tau_wx_{i,w}^2}$ on $F_\infty^{2m}$
(0-based $i$). -/
@[kb "kudla1996" "§I.4 (the Gaussian and its translates $\\omega(g_z)\\varphi_\\infty$) [unverified]"]
def gOrb (a : Fin (2 * m) → (mixedSpace F)ˣ) (τ : RP → ℂ) : (Fin (2 * m) → mixedSpace F) → ℂ :=
  ptensor fun i => gs (fun w => (((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w)

variable (a : Fin (2 * m) → (mixedSpace F)ˣ)

/-- $\omega_\infty(n(r))G_\tau = G_{\tau + r}$. -/
lemma opNf_gOrb (r : mixedSpace F) (τ : RP → ℂ) :
    (localDataInf (F := F)).opNf a r (gOrb a τ) = gOrb a (fun w => τ w + (r.1 w : ℂ)) := by
  rw [gOrb, opNf_ptensor, gOrb]
  refine congrArg ptensor (funext fun i => ?_)
  rw [chirp_gs]
  congr 1; funext w
  simp only [Prod.fst_mul, Pi.mul_apply]; push_cast; ring

/-- $\omega_\infty(m(t))G_\tau = \chi_V(t)|t|^mG_{t^2\tau}$. -/
lemma opMf_gOrb (t : mixedSpace F) (τ : RP → ℂ) :
    (localDataInf (F := F)).opMf a t (gOrb a τ) =
      ((localDataInf (F := F)).chiV a t * ((localDataInf (F := F)).md t : ℂ) ^ m) •
        gOrb a (fun w => τ w * ((t.1 w : ℝ) : ℂ) ^ 2) := by
  rw [gOrb, opMf_ptensor, gOrb]
  congr 1
  refine congrArg ptensor (funext fun i => ?_)
  rw [dil_gs]
  congr 1; funext w; ring

variable {a}

/-- $\omega_\infty(w)G_\tau = \gamma_V\prod_iC_i(\tau)\;G_{-1/\tau}$, $C_i(\tau) = |2a_i|^{1/2}\prod_w(-2ia_{i,w}\tau_w)^{-1/2}$. -/
lemma opWf_gOrb (hpos : ∀ i w, 0 < (a i : mixedSpace F).1 w) (τ : RP → ℂ) (hτ : ∀ w, 0 < (τ w).im) :
    (localDataInf (F := F)).opWf a (gOrb a τ) =
      ((localDataInf (F := F)).gammaV a * ∏ i, ((Real.sqrt (mixedEmbedding.norm (2 * (a i : mixedSpace F))) : ℂ) *
        ∏ w, (-2 * I * ((((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w))⁻¹ ^ (1 / 2 : ℂ))) •
        gOrb a (fun w => -(τ w)⁻¹) := by
  rw [gOrb, opWf_ptensor', gOrb]
  have hF : ∀ i, (localDataInf (F := F)).Fa (a i) (gs fun w => (((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w) =
      ((Real.sqrt (mixedEmbedding.norm (2 * (a i : mixedSpace F))) : ℂ) *
        ∏ w, (-2 * I * ((((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w))⁻¹ ^ (1 / 2 : ℂ)) •
        gs (fun w => (((a i : mixedSpace F).1 w : ℝ) : ℂ) * -(τ w)⁻¹) := by
    intro i
    rw [Fa_gs (a i : mixedSpace F) (fun w => (((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w) (fun w => by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos (hpos i w) (hτ w))]
    refine congrArg _ (congrArg gs (funext fun w => ?_))
    have hβ : (((a i : mixedSpace F).1 w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i w).ne'
    have hτ0 : τ w ≠ 0 := fun h => by have := hτ w; rw [h] at this; simp at this
    field_simp
  simp only [hF]
  rw [ptensor_smul_fun, smul_smul]

/-! ### The constant of $\omega_\infty(w)$ -/

lemma re_inv_neg_I_mul_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < ((-I * τ)⁻¹).re := by
  rw [Complex.inv_re]
  have h1 : (-I * τ).re = τ.im := by simp
  rw [h1]
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have : 0 < Complex.normSq (-I * τ) := Complex.normSq_pos.mpr (mul_ne_zero (by simp) hτ0)
  positivity

/-- The ratio $\rho(\tau) = (-i\tau)^{-1/2}/i^{1/2}$: the per-coordinate archimedean constant, with $\rho(\tau)^2 = \tau^{-1}$. -/
def rhoW (τ : ℂ) : ℂ := (-I * τ)⁻¹ ^ (1 / 2 : ℂ) / I ^ (1 / 2 : ℂ)

lemma rhoW_sq {τ : ℂ} (hτ : τ ≠ 0) : rhoW τ ^ 2 = τ⁻¹ := by
  have h1 : ((-I * τ)⁻¹ ^ (1 / 2 : ℂ)) ^ 2 = (-I * τ)⁻¹ := by
    have := Complex.cpow_nat_inv_pow ((-I * τ)⁻¹) (n := 2) two_ne_zero
    simpa [one_div] using this
  have h2 : (I ^ (1 / 2 : ℂ)) ^ 2 = I := by
    have := Complex.cpow_nat_inv_pow I (n := 2) two_ne_zero
    simpa [one_div] using this
  have hI : I ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; rw [h] at h2; simp at h2; exact I_ne_zero h2.symm
  rw [rhoW, div_pow, h1, h2]
  field_simp
  ring_nf
  rw [I_sq]

/-- For $\beta > 0$ and $\operatorname{Im}\tau > 0$: $(-2i\beta\tau)^{-1/2} = \gamma_{\mathbb R}(\beta)\,\rho(\tau)$, $\gamma_{\mathbb R}(\beta) = (i/2\beta)^{1/2}$. -/
lemma cpow_eq_weilR_mul_rhoW {β : ℝ} (hβ : 0 < β) {τ : ℂ} (hτ : 0 < τ.im) :
    (-2 * I * ((β : ℂ) * τ))⁻¹ ^ (1 / 2 : ℂ) = weilR β * rhoW τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hu : (0 : ℝ) < (((2 * β : ℝ) : ℂ)⁻¹).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]; positivity
  have hu0 : (((2 * β : ℝ) : ℂ)⁻¹) ≠ 0 := by
    rw [← Complex.ofReal_inv]; exact_mod_cast (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * β)).ne'
  have e1 : (-2 * I * ((β : ℂ) * τ))⁻¹ = ((2 * β : ℝ) : ℂ)⁻¹ * (-I * τ)⁻¹ := by
    push_cast; field_simp
  have e2 : I / (2 * (β : ℂ)) = I * ((2 * β : ℝ) : ℂ)⁻¹ := by push_cast; ring
  rw [e1, cpow_mul_of_re hu.le hu0 (re_inv_neg_I_mul_pos hτ), weilR, e2,
    cpow_mul_of_re (by simp) I_ne_zero hu, rhoW]
  have hI : I ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp
  field_simp

lemma prod_complex_eq_one {M : Type*} [CommMonoid M] (f : {w : InfinitePlace F // IsComplex w} → M) :
    ∏ w, f w = 1 := by
  simp [Finset.univ_eq_empty]

/-- **The constant of $\omega_\infty(w)$ on the orbit:** $\gamma_V\prod_iC_i(\tau) = \chi_V(-1)\prod_w\tau_w^{-m}$.
The $2m$ square roots per place pair off exactly: $(-2ia_{i,w}\tau_w)^{-1/2} = \gamma_{\mathbb R}(a_{i,w})\rho(\tau_w)$ with
$\rho(\tau)^2 = \tau^{-1}$, and the $\gamma_{\mathbb R}(a_{i,w})$, $|2a_i|^{1/2}$ cancel against $\gamma_V$. -/
lemma gammaV_mul_prod_C (hpos : ∀ i w, 0 < (a i : mixedSpace F).1 w) (τ : RP → ℂ) (hτ : ∀ w, 0 < (τ w).im) :
    (localDataInf (F := F)).gammaV a * ∏ i, ((Real.sqrt (mixedEmbedding.norm (2 * (a i : mixedSpace F))) : ℂ) *
        ∏ w, (-2 * I * ((((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w))⁻¹ ^ (1 / 2 : ℂ)) =
      (localDataInf (F := F)).chiV a (-1) * ∏ w, (τ w)⁻¹ ^ m := by
  have hτ0 : ∀ w, τ w ≠ 0 := fun w h => by have := hτ w; rw [h] at this; simp at this
  have hC : ∀ i, (Real.sqrt (mixedEmbedding.norm (2 * (a i : mixedSpace F))) : ℂ) *
      ∏ w, (-2 * I * ((((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w))⁻¹ ^ (1 / 2 : ℂ) =
      (localDataInf (F := F)).gN (a i) * ∏ w, rhoW (τ w) := by
    intro i
    have hw : ∀ w, (-2 * I * ((((a i : mixedSpace F).1 w : ℝ) : ℂ) * τ w))⁻¹ ^ (1 / 2 : ℂ) =
        weilR ((a i : mixedSpace F).1 w) * rhoW (τ w) := fun w => cpow_eq_weilR_mul_rhoW (hpos i w) (hτ w)
    simp only [hw, Finset.prod_mul_distrib]
    unfold LocalData.gN
    show _ = weilInf _ * _ * _
    rw [weilInf, prod_complex_eq_one, mul_one]
    show _ = _ * (Real.sqrt (mixedEmbedding.norm (2 * (a i : mixedSpace F))) : ℂ) * _
    ring
  simp only [hC, Finset.prod_mul_distrib]
  have hgN : ∀ i, (localDataInf (F := F)).gN (a i) ≠ 0 := by
    intro i
    unfold LocalData.gN
    refine mul_ne_zero ?_ ?_
    · show weilInf _ ≠ 0
      rw [weilInf, prod_complex_eq_one, mul_one]
      refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
      rw [weilR, Ne, Complex.cpow_eq_zero_iff]
      have : (2 * (((a i : mixedSpace F).1 w : ℝ) : ℂ)) ≠ 0 := by
        have := (hpos i w).ne'; exact_mod_cast mul_ne_zero two_ne_zero this
      simp [this]
    · have : 0 < mixedEmbedding.norm (2 * (a i : mixedSpace F)) := by
        rw [norm_eq_prod_real]
        refine Finset.prod_pos fun w _ => abs_pos.mpr ?_
        simp only [Prod.fst_mul, Pi.mul_apply]
        exact mul_ne_zero (by norm_num [show ((2 : mixedSpace F).1 w : ℝ) = 2 from rfl]) (hpos i w).ne'
      exact_mod_cast (Real.sqrt_pos.mpr this).ne'
  have hrho : ∏ i : Fin (2 * m), ∏ w, rhoW (τ w) = ∏ w, (τ w)⁻¹ ^ m := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pow_mul, rhoW_sq (hτ0 w)]
  have hP : ∏ i, (localDataInf (F := F)).gN (a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hgN i
  rw [hrho, LocalData.gammaV]
  field_simp

/-! ### The quadratic character at the real places -/

/-- $(t, d)_{\mathbb R}\,|t|^m = t^m$ when $d$ has sign $(-1)^m$. -/
lemma hilbR_mul_abs_pow {t d : ℝ} (ht : t ≠ 0) (hd : d ≠ 0) (hsign : d < 0 ↔ Odd m) :
    (hilbertSymbol ℝ t d : ℂ) * ((|t| : ℝ) : ℂ) ^ m = (t : ℂ) ^ m := by
  rcases lt_or_gt_of_ne ht with htn | htp
  · rw [abs_of_neg htn]
    by_cases hm : Odd m
    · have h : hilbertSymbol ℝ t d = -1 := (hilbertSymbol_real t d ht hd).mpr ⟨htn, hsign.mpr hm⟩
      rw [h]; push_cast; rw [neg_pow, hm.neg_one_pow]; ring
    · have h : hilbertSymbol ℝ t d = 1 := by
        rcases HN.hilbertSymbol_eq_one_or ℝ t d with h | h
        · exact h
        · exact absurd (hsign.mp ((hilbertSymbol_real t d ht hd).mp h).2) hm
      have he : Even m := Nat.not_odd_iff_even.mp hm
      rw [h]; push_cast; rw [neg_pow, he.neg_one_pow]; ring
  · have h : hilbertSymbol ℝ t d = 1 := by
      rcases HN.hilbertSymbol_eq_one_or ℝ t d with h | h
      · exact h
      · exact absurd ((hilbertSymbol_real t d ht hd).mp h).1 (not_lt.mpr htp.le)
    rw [h, abs_of_pos htp]; push_cast; ring

lemma discV_fst (w : RP) :
    ((discV a : (mixedSpace F)ˣ) : mixedSpace F).1 w = (-1) ^ m * ∏ i, (a i : mixedSpace F).1 w := by
  simp only [discV, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Units.coe_prod,
    Prod.fst_mul, Pi.mul_apply, Prod.fst_prod, Finset.prod_apply]
  congr 1

lemma discV_fst_neg_iff (hpos : ∀ i w, 0 < (a i : mixedSpace F).1 w) (w : RP) :
    ((discV a : (mixedSpace F)ˣ) : mixedSpace F).1 w < 0 ↔ Odd m := by
  rw [discV_fst]
  have hP : 0 < ∏ i, (a i : mixedSpace F).1 w := Finset.prod_pos fun i _ => hpos i w
  constructor
  · intro h
    by_contra hm
    rw [(Nat.not_odd_iff_even.mp hm).neg_one_pow, one_mul] at h
    exact absurd h (not_lt.mpr hP.le)
  · intro hm; rw [hm.neg_one_pow]; linarith

lemma discV_fst_ne_zero (hpos : ∀ i w, 0 < (a i : mixedSpace F).1 w) (w : RP) :
    ((discV a : (mixedSpace F)ˣ) : mixedSpace F).1 w ≠ 0 := by
  rw [discV_fst]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_pos fun i _ => hpos i w).ne'

/-- **$\chi_V(t)|t|^m = \prod_wt_w^m$** at the real places, for totally positive $a_i$. -/
lemma chiV_mul_md_pow (hpos : ∀ i w, 0 < (a i : mixedSpace F).1 w) (t : mixedSpace F) (ht : ∀ w, t.1 w ≠ 0) :
    (localDataInf (F := F)).chiV a t * ((localDataInf (F := F)).md t : ℂ) ^ m = ∏ w, ((t.1 w : ℝ) : ℂ) ^ m := by
  simp only [LocalData.chiV, LocalData.hC]
  show (hilbInf t (discV a) : ℂ) * ((mixedEmbedding.norm t : ℝ) : ℂ) ^ m = _
  rw [hilbInf, norm_eq_prod_real]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ =>
    hilbR_mul_abs_pow (ht w) (discV_fst_ne_zero hpos w) (discV_fst_neg_iff hpos w)

lemma md_neg_one_inf : (localDataInf (F := F)).md (-1) = 1 := by
  show mixedEmbedding.norm (-1 : mixedSpace F) = 1
  rw [norm_eq_prod_real]; simp

/-! ### The archimedean equivariance -/

/-- The real embedding at a real place $w$, $F \to \mathbb R$, $x \mapsto x_w$. -/
def ew (w : RP) : F →+* ℝ := (Pi.evalRingHom (fun _ : RP => ℝ) w).comp ((RingHom.fst _ _).comp (mixedEmbedding F))

lemma ew_apply (w : RP) (x : F) : ew w x = (mixedEmbedding F x).1 w := rfl

lemma mixedEmbedding_fst (w : RP) (x : F) : (mixedEmbedding F x).1 w = ew w x := rfl

lemma neg_one_fst (w : RP) : ((-1 : mixedSpace F).1 w) = -1 := rfl

/-- **Archimedean equivariance of the Gaussian orbit** (the archimedean half of Route 2): for $V = \langle a_0, \dots,
a_{2m-1}\rangle$ with $a_i \in F^\times$ totally positive, $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F)$ acting on
the archimedean component by the cell formula (`omegaG`), and $\operatorname{Im}\tau_w > 0$:
$$\omega_\infty(\gamma)\,G_\tau = \prod_w(c_w\tau_w + d_w)^{-m}\;G_{\gamma\tau},\qquad
  (\gamma\tau)_w = \frac{a_w\tau_w + b_w}{c_w\tau_w + d_w}.$$
For $c \ne 0$: $n(d/c)$ moves $\tau$ to $\tau' = \tau + d/c$, $\omega_\infty(w)$ gives $\chi_V(-1)\prod_w\tau_w'^{-m}G_{-1/\tau'}$
(`gammaV_mul_prod_C`), $m(-c^{-1})$ gives $\chi_V(-c^{-1})|c|^{-m}G_{-1/(c^2\tau')}$ and $n(a/c)$ the Möbius point; the
constants combine by $(t, (-1)^m\det V)_{\mathbb R}|t|^m = t^m$ (`chiV_mul_md_pow`). For $c = 0$ it is $m(a)n(b/a)$. -/
@[kb "kudla1996" "§I.4 (the archimedean component: weight $n/2$) [unverified]"]
theorem omegaG_inf_gOrb (a : Fin (2 * m) → Fˣ) (hpos : ∀ i w, 0 < ew w (a i : F)) (γ : SL(2, F))
    {Φ : GDatum F (2 * m)} {τ : RP → ℂ} (hτ : ∀ w, 0 < (τ w).im) (hΦ : Φ.inf = gOrb (aInf a) τ) :
    (omegaG a γ Φ).inf =
      (∏ w, ((ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (γ 1 1)) ^ (-(m : ℤ))) •
        gOrb (aInf a) (fun w => ((ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) : ℂ) * τ w + ew w (γ 0 1)) /
          ((ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (γ 1 1))) := by
  have hpos' : ∀ i w, 0 < ((aInf a i : (mixedSpace F)ˣ) : mixedSpace F).1 w := fun i w => hpos i w
  have hdet := det_eq γ
  have hdetw : ∀ w, ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) * ew w (γ 1 1) -
      ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 1) * ew w (γ 1 0) = 1 := fun w => by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  have hτ0 : ∀ w, τ w ≠ 0 := fun w h => by have := hτ w; rw [h] at this; simp at this
  unfold omegaG
  by_cases hc : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have ha0 := a_ne_zero_of_c_eq_zero hc
    rw [cellRep_of_c_eq_zero hc, Aof_of_ne ha0]
    show (localDataInf (F := F)).opMf (aInf a) (mixedEmbedding F _)
      ((localDataInf (F := F)).opNf (aInf a) (mixedEmbedding F _) Φ.inf) = _
    rw [hΦ, opNf_gOrb, opMf_gOrb, Units.val_mk0,
      chiV_mul_md_pow hpos' _ (fun w => by rw [← ew_apply]; exact (map_ne_zero _).mpr ha0)]
    have had : ∀ w, ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) * ew w (γ 1 1) = 1 := fun w => by
      have := hdetw w; rw [hc, map_zero, mul_zero, sub_zero] at this; exact this
    have hew0 : ∀ w, (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) : ℂ) ≠ 0 := fun w => by
      exact_mod_cast (map_ne_zero (ew w)).mpr ha0
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← ew_apply, hc, map_zero, Complex.ofReal_zero, zero_mul, zero_add, zpow_neg, zpow_natCast]
      have h1 : (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1) : ℂ) = (ew w (γ 0 0) : ℂ)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast had w)
      rw [h1, inv_pow, inv_inv]
    · congr 1; funext w
      rw [← ew_apply, ← ew_apply, map_div₀, hc, map_zero, Complex.ofReal_zero, zero_mul, zero_add]
      have h1 : (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1) : ℂ) = (ew w (γ 0 0) : ℂ)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast had w)
      rw [h1]
      push_cast
      have := hew0 w
      field_simp
  · rw [cellRep_of_c_ne_zero hc, Aof_of_ne (unit_ne_zero_aux hc)]
    show (localDataInf (F := F)).opNf (aInf a) (mixedEmbedding F _)
      ((localDataInf (F := F)).opMf (aInf a) (mixedEmbedding F _)
        ((localDataInf (F := F)).opWf (aInf a)
          ((localDataInf (F := F)).opNf (aInf a) (mixedEmbedding F _) Φ.inf))) = _
    have hτ' : ∀ w, 0 < (τ w + (((mixedEmbedding F ((γ : Matrix (Fin 2) (Fin 2) F) 1 1 / γ 1 0)).1 w : ℝ) :
        ℂ)).im := fun w => by rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hτ w
    rw [hΦ, opNf_gOrb, opWf_gOrb hpos' _ hτ', gammaV_mul_prod_C hpos' _ hτ', opMf_smul, opMf_gOrb,
      smul_smul, opNf_smul, opNf_gOrb, Units.val_mk0,
      chiV_mul_md_pow hpos' _ (fun w => by
        rw [← ew_apply]; exact (map_ne_zero _).mpr (unit_ne_zero_aux hc))]
    have hm1 := chiV_mul_md_pow hpos' (-1 : mixedSpace F) (fun w => by simp)
    rw [md_neg_one_inf, Complex.ofReal_one, one_pow, mul_one] at hm1
    simp only [neg_one_fst, Complex.ofReal_neg, Complex.ofReal_one] at hm1
    rw [hm1]
    have hcw : ∀ w, (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) ≠ 0 := fun w => by
      exact_mod_cast (map_ne_zero (ew w)).mpr hc
    have hden : ∀ w, (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (γ 1 1) ≠ 0 := by
      intro w h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.zero_im] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact hcw w (by exact_mod_cast h')
      · exact absurd h' (hτ w).ne'
    congr 1
    · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [mixedEmbedding_fst]
      simp only [map_neg, map_inv₀, map_div₀, map_one, Complex.ofReal_neg, Complex.ofReal_inv,
        Complex.ofReal_div, Complex.ofReal_one]
      rw [zpow_neg, zpow_natCast, ← mul_pow, ← mul_pow, ← inv_pow]
      congr 1
      have := hcw w
      have := hden w
      field_simp
    · congr 1; funext w
      simp only [mixedEmbedding_fst]
      simp only [map_neg, map_inv₀, map_div₀, Complex.ofReal_neg, Complex.ofReal_inv,
        Complex.ofReal_div]
      have := hcw w
      have := hden w
      have hD' : τ w * (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) + ew w (γ 1 1) ≠ 0 := by
        rw [mul_comm]; exact hden w
      have hdC : (ew w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) : ℂ) * ew w (γ 1 1) -
          ew w (γ 0 1) * ew w (γ 1 0) = 1 := by exact_mod_cast hdetw w
      field_simp
      ring_nf
      field_simp
      linear_combination hdC

end QuadFormsKB.WeilRep
