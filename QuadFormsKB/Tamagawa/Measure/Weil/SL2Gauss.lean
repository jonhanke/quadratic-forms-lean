import QuadFormsKB.Tamagawa.Measure.Weil.SL2Theta
import QuadFormsKB.Analysis.WeilIndexInf
import QuadFormsKB.Tamagawa.Measure.Weil.AdditivePoisson

/-!
# Scaled Gaussians on $F_\infty^2$ and their Fourier transforms

$F$ any number field, $V = F_\infty$, $W = V^2$ with the self-dual measure and the trace pairing (`SL2Theta.lean`).
For a unit $u\in V^\times$ the scaled Gaussian $G_u(y) = g(uy_0)\,g(uy_1)$, with
$g(x) = \exp(-\pi(\sum_{w\ \mathrm{real}}x_w^2 + 2\sum_{w\ \mathrm{complex}}|x_w|^2))$ the self-dual Gaussian on $V$
(`gaussInfFun`, `fourierInf_gaussInfFun`), is a Schwartz function (`gaussW`), and
**`fourierW_gaussW`**: $\hat G_u(z) = \Delta(u)^{-2}g(u^{-1}z_0)\,g(u^{-1}z_1)$, $\Delta(u) = $ `distribHaarChar V u`.
Consequences: $\int_W G_u = \Delta(u)^{-2}$ (`integral_gaussWR`), $\int_W\hat G_u = 1$ (`integral_gaussWHat`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Real
open scoped ENNReal NNReal Pointwise Classical MatrixGroups FourierTransform

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

/-- The real self-dual Gaussian on $V$. -/
def gR (x : V) : ℝ := Real.exp (-π * ((∑ w, (x.1 w) ^ 2) + 2 * ∑ w, ‖x.2 w‖ ^ 2))

theorem gR_pos (x : V) : 0 < gR x := Real.exp_pos _

theorem gaussInfFun_eq_gR (x : V) : Analysis.gaussInfFun x = (gR x : ℂ) := by
  rw [← Analysis.gaussInf_apply, Analysis.gaussInf, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, Analysis.gaussianSchwartz_apply, Analysis.norm_gaussT_sq, gR, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem gR_zero : gR (0 : V) = 1 := by simp [gR]

/-- The Euclidean structure used to build the Gaussian on $W$. -/
def gaussTW : (Fin 2 → V) ≃L[ℝ] PiLp 2 (fun _ : Fin 2 => euclidean.mixedSpace F) :=
  (ContinuousLinearEquiv.piCongrRight fun _ => Analysis.gaussT (F := F)).trans
    (PiLp.continuousLinearEquiv 2 ℝ _).symm

theorem norm_gaussTW_sq (y : Fin 2 → V) :
    ‖gaussTW y‖ ^ 2 = ‖Analysis.gaussT (y 0)‖ ^ 2 + ‖Analysis.gaussT (y 1)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  rfl

/-- The self-dual Gaussian on $W$ as a Schwartz function. -/
def gaussW₁ : SchwartzMap (Fin 2 → V) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussTW (F := F))
    (Analysis.gaussianSchwartz (π : ℂ) (by simp [Real.pi_pos]))

theorem gaussW₁_apply (y : Fin 2 → V) : gaussW₁ y = ((gR (y 0) * gR (y 1) : ℝ) : ℂ) := by
  rw [gaussW₁, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Analysis.gaussianSchwartz_apply, norm_gaussTW_sq, Analysis.norm_gaussT_sq, Analysis.norm_gaussT_sq, gR, gR,
    ← Real.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Multiplication by a unit $u$ on $V$, as a continuous linear equivalence. -/
def mulUnitCLE (u : Vˣ) : V ≃L[ℝ] V :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (u : V) * x
      invFun := fun x => ((u⁻¹ : Vˣ) : V) * x
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun c x => mul_smul_comm c _ _
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc] }

/-- The scaled Gaussian $G_u(y) = g(uy_0)g(uy_1)$ on $W$. -/
def gaussW (u : Vˣ) : SchwartzMap (Fin 2 → V) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.piCongrRight fun _ => mulUnitCLE u)
    (gaussW₁ (F := F))

/-- The real values of $G_u$. -/
def gaussWR (u : Vˣ) (y : Fin 2 → V) : ℝ := gR ((u : V) * y 0) * gR ((u : V) * y 1)

theorem gaussW_apply (u : Vˣ) (y : Fin 2 → V) : gaussW u y = (gaussWR u y : ℂ) := by
  rw [gaussW, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussW₁_apply]
  rfl

theorem gaussWR_pos (u : Vˣ) (y : Fin 2 → V) : 0 < gaussWR u y := mul_pos (gR_pos _) (gR_pos _)

theorem gaussWR_zero (u : Vˣ) : gaussWR u 0 = 1 := by simp [gaussWR, gR_zero]

/-- The modulus $\Delta(u)$ of a unit of $V$ (as a real number). -/
abbrev modInf (u : Vˣ) : ℝ := (distribHaarChar V u : ℝ)

theorem modInf_pos (u : Vˣ) : 0 < modInf u := by
  have h := map_mul (distribHaarChar V) u u⁻¹
  rw [mul_inv_cancel, map_one] at h
  have hne : distribHaarChar V u ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hne)

/-- The real values of $\hat G_u$. -/
def gaussWHat (u : Vˣ) (z : Fin 2 → V) : ℝ :=
  (modInf u)⁻¹ ^ 2 * (gR (((u⁻¹ : Vˣ) : V) * z 0) * gR (((u⁻¹ : Vˣ) : V) * z 1))

theorem gaussWHat_pos (u : Vˣ) (z : Fin 2 → V) : 0 < gaussWHat u z :=
  mul_pos (pow_pos (inv_pos.mpr (modInf_pos u)) 2) (mul_pos (gR_pos _) (gR_pos _))

theorem gaussWHat_zero (u : Vˣ) : gaussWHat u 0 = (modInf u)⁻¹ ^ 2 := by
  simp [gaussWHat, gR_zero]

theorem fourierInf_gR_mul (u : Vˣ) (z : V) :
    Analysis.fourierInf (fun y => (gR ((u : V) * y) : ℂ)) z =
      (((modInf u)⁻¹ * gR (((u⁻¹ : Vˣ) : V) * z) : ℝ) : ℂ) := by
  have h := fourierInf_comp_mul (F := F) u (Analysis.gaussInfFun) z
  simp_rw [gaussInfFun_eq_gR] at h
  rw [h, Analysis.fourierInf_gaussInfFun, gaussInfFun_eq_gR, Complex.real_smul]
  push_cast
  ring

/-- **The Fourier transform of the scaled Gaussian on $W$.** -/
theorem fourierW_gaussW (u : Vˣ) (z : Fin 2 → V) : fourierW F (gaussW u) z = (gaussWHat u z : ℂ) := by
  unfold fourierW
  have hfun : (fun y : Fin 2 → V => gaussW u y * ((𝐞 (betaW F y z) : Circle) : ℂ)) =
      fun y => ∏ i, ((gR ((u : V) * y i) : ℂ) * (Analysis.psiInf (y i * z i) : ℂ)) := by
    funext y
    rw [gaussW_apply, gaussWR, betaW_apply, Fin.sum_univ_two, AddChar.map_add_eq_mul, Fin.prod_univ_two]
    push_cast
    simp only [Analysis.psiInf]
    ring
  rw [hfun, muInfVec, integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (i : Fin 2) (y : V) => (gR ((u : V) * y) : ℂ) * (Analysis.psiInf (y * z i) : ℂ))]
  have hi : ∀ i : Fin 2, ∫ y, (gR ((u : V) * y) : ℂ) * (Analysis.psiInf (y * z i) : ℂ) ∂Analysis.selfDualInf =
      (((modInf u)⁻¹ * gR (((u⁻¹ : Vˣ) : V) * z i) : ℝ) : ℂ) := fun i => fourierInf_gR_mul u (z i)
  simp_rw [hi]
  rw [Fin.prod_univ_two, gaussWHat]
  push_cast
  ring

theorem integral_gR_mul (u : Vˣ) :
    ∫ y, (gR ((u : V) * y) : ℂ) ∂Analysis.selfDualInf = (((modInf u)⁻¹ : ℝ) : ℂ) := by
  have h := fourierInf_gR_mul (F := F) u 0
  rw [mul_zero, gR_zero, mul_one] at h
  rw [← h, Analysis.fourierInf]
  congr 1
  funext y
  simp [Analysis.psiInf, traceInf_zero']

theorem modInf_inv (u : Vˣ) : modInf u⁻¹ = (modInf u)⁻¹ := by
  rw [modInf, modInf, map_inv, NNReal.coe_inv]

/-- $\int_W\hat G_u = 1$. -/
theorem integral_gaussWHat (u : Vˣ) :
    ∫ z, (gaussWHat u z : ℂ) ∂muInfVec F (Fin 2) = 1 := by
  have hfun : (fun z : Fin 2 → V => (gaussWHat u z : ℂ)) =
      fun z => ∏ i, ((((modInf u)⁻¹ : ℝ) : ℂ) * (gR (((u⁻¹ : Vˣ) : V) * z i) : ℂ)) := by
    funext z
    rw [gaussWHat, Fin.prod_univ_two]
    push_cast
    ring
  rw [hfun, muInfVec, integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (_ : Fin 2) (y : V) => (((modInf u)⁻¹ : ℝ) : ℂ) * (gR (((u⁻¹ : Vˣ) : V) * y) : ℂ))]
  simp_rw [integral_const_mul, integral_gR_mul, modInf_inv, inv_inv]
  rw [Fin.prod_univ_two]
  have hpos := modInf_pos u
  have hne : ((modInf u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp

/-- $\int_W G_u = \Delta(u)^{-2}$. -/
theorem integral_gaussW (u : Vˣ) :
    ∫ y, (gaussWR u y : ℂ) ∂muInfVec F (Fin 2) = ((modInf u)⁻¹ ^ 2 : ℝ) := by
  have h := fourierW_gaussW (F := F) u 0
  rw [gaussWHat_zero] at h
  rw [← h, fourierW]
  congr 1
  funext y
  simp [gaussW_apply, betaW_apply, traceInf_zero']

end

end QuadFormsKB.Tamagawa.Measure.Weil
