import QuadFormsKB.HilbertModular.ThetaChar

/-!
# Theta series over a totally real field IV: expansion at a cusp

Notation of `Theta.lean`, `ThetaInversion.lean`, `ThetaChar.lean`. The lattices $L = \bigoplus_iI_ie_i$ and
$L^\# = \bigoplus_iI_i^\vee e_i^*$ are used here as sets of vectors (`latSet`, `dualSet`), and the theta series as sums over
them (`thetaLat_eq_tsum_latSet`, `thetaLatDual_eq_tsum_dualSet`).

**Expansion at a cusp** (`tsum_latSet_cusp`). Let $\alpha, c \in F$, $c \neq 0$, and let $\rho : R \to F^n$ ($R$ finite) be
a system of representatives of $L/cL$, i.e. $R \times L \to L$, $(r, y) \mapsto \rho(r) + cy$ is a bijection. Assume
$\operatorname{Tr}\big(\tfrac{\alpha}{c}(Q(\rho(r) + cy) - Q(\rho(r)))\big) \in \mathbb{Z}$. Then for $u \in \mathbb{H}^d$,
$$\sum_{x\in L}e\Big(\sum_v\varphi_v(Q(x))\Big(\frac{\varphi_v(\alpha)}{\varphi_v(c)} - \frac{1}{\varphi_v(c)^2u_v}\Big)\Big)
  = C_L(u)\sum_{\mu\in L^\#}e\Big(\sum_v\varphi_v(Q^\#(\mu))u_v\Big)\,G(\alpha, \mu, c),$$
$$G(\alpha, \mu, c) = \sum_{r\in R}e\Big(\operatorname{Tr}\Big(\frac{\alpha Q(\rho(r)) + \mu\cdot\rho(r)}{c}\Big)\Big),\qquad
  C_L(u) = \frac{1}{\sqrt{N(\det A)}\prod_i\Delta(I_i)}\prod_v\Big(\frac{-iu_v}{2}\Big)^{n/2}.$$
*Proof.* Split $x = \rho(r) + cy$; then $Q(x)\frac{-1}{c^2u} = Q(y + \rho(r)/c)\frac{-1}{u}$, and apply the inversion with
characteristic $\eta = \rho(r)/c$ (`thetaLatChar_inversion`) to each class. This is `QuadFormsKB.Siegel.thetaGram_cusp` over $F$.
-/

open Matrix NumberField NumberField.InfinitePlace Complex
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-! ### Lattices as sets of vectors -/

/-- **The lattice** $L = \bigoplus_iI_ie_i \subset F^n$ as a set. -/
@[kb "freitag1990" "Ch. I §4, lattices in F^n [unverified]"]
def latSet (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Set (Fin n → F) :=
  {x | ∀ i, x i ∈ (((𝔞 i : FractionalIdeal (𝓞 F)⁰ F)) : Set F)}

/-- **The dual lattice** $L^\# = \bigoplus_iI_i^\vee e_i^*$, $I^\vee$ the trace dual. -/
@[kb "freitag1990" "Ch. I §4, dual lattice [unverified]"]
def dualSet (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Set (Fin n → F) :=
  {x | ∀ i, x i ∈ ((FractionalIdeal.dual ℤ ℚ (𝔞 i : FractionalIdeal (𝓞 F)⁰ F) :
    FractionalIdeal (𝓞 F)⁰ F) : Set F)}

/-- Coordinates $\mathbb{Z}^{n\times d} \simeq L$. -/
def latSetEquiv (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (Fin n → Fin (Module.finrank ℚ F) → ℤ) ≃ latSet 𝔞 :=
  (Equiv.piCongrRight fun i => QuadFormsKB.Analysis.latEquiv (𝔞 i)).trans
    (Equiv.subtypePiEquivPi (p := fun i (x : F) =>
      x ∈ (((𝔞 i : FractionalIdeal (𝓞 F)⁰ F)) : Set F))).symm

lemma latSetEquiv_coe (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (k : Fin n → Fin (Module.finrank ℚ F) → ℤ) :
    ((latSetEquiv 𝔞 k : latSet 𝔞) : Fin n → F) = latVec 𝔞 k := by
  funext i
  exact QuadFormsKB.Analysis.latEquiv_coe (𝔞 i) (k i)

/-- Coordinates $\mathbb{Z}^{n\times d} \simeq L^\#$. -/
def dualSetEquiv (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (Fin n → Fin (Module.finrank ℚ F) → ℤ) ≃ dualSet 𝔞 :=
  (Equiv.piCongrRight fun i => QuadFormsKB.Analysis.dualEquiv (𝔞 i)).trans
    (Equiv.subtypePiEquivPi (p := fun i (x : F) =>
      x ∈ ((FractionalIdeal.dual ℤ ℚ (𝔞 i : FractionalIdeal (𝓞 F)⁰ F) :
        FractionalIdeal (𝓞 F)⁰ F) : Set F))).symm

lemma dualSetEquiv_coe (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (m : Fin n → Fin (Module.finrank ℚ F) → ℤ) :
    ((dualSetEquiv 𝔞 m : dualSet 𝔞) : Fin n → F) = dualLatVec 𝔞 m := by
  funext i
  exact QuadFormsKB.Analysis.dualEquiv_coe (𝔞 i) (m i)

lemma thetaLat_eq_tsum_latSet (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℂ) :
    thetaLat A 𝔞 z = ∑' x : latSet 𝔞, thetaTerm A x z := by
  rw [thetaLat, ← (latSetEquiv 𝔞).tsum_eq]
  simp_rw [latSetEquiv_coe]

lemma thetaLatChar_eq_tsum_latSet (A : Matrix (Fin n) (Fin n) F)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F) (z : InfinitePlace F → ℂ) :
    thetaLatChar A 𝔞 η z = ∑' x : latSet 𝔞, thetaTerm A ((x : Fin n → F) + η) z := by
  rw [thetaLatChar, ← (latSetEquiv 𝔞).tsum_eq]
  simp_rw [latSetEquiv_coe]

lemma thetaLatDual_eq_tsum_dualSet (A : Matrix (Fin n) (Fin n) F)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : InfinitePlace F → ℂ) :
    thetaLatDual A 𝔞 z = ∑' μ : dualSet 𝔞, thetaTerm ((1 / 4 : F) • A⁻¹) μ z := by
  rw [thetaLatDual, ← (dualSetEquiv 𝔞).tsum_eq]
  simp_rw [dualSetEquiv_coe]

lemma summable_norm_thetaTerm_latSet {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) :
    Summable fun x : latSet 𝔞 => ‖thetaTerm A x z‖ := by
  rw [← (latSetEquiv 𝔞).summable_iff]
  refine (summable_norm_thetaTerm hA 𝔞 hz).congr fun k => ?_
  simp [latSetEquiv_coe]

lemma dualMat_det_ne_zero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : (dualMat A 𝔞).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (latMat_transpose_mul hA 𝔞)
  rw [det_mul, h, mul_zero, det_one] at this
  exact zero_ne_one this

/-- **Absolute convergence of the dual theta series** $\sum_{\mu\in L^\#}e(\sum_v\varphi_v(Q^\#(\mu))z_v)$. -/
theorem summable_norm_thetaTerm_dual {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) :
    Summable fun m : Fin n → Fin (Module.finrank ℚ F) → ℤ =>
      ‖thetaTerm ((1 / 4 : F) • A⁻¹) (dualLatVec 𝔞 m) z‖ := by
  set w : InfinitePlace F → ℂ := fun v => (-Complex.I * z v / 2)⁻¹
  have hb : ∀ p : Fin n × Fin dq, 0 < ((w (placeEquiv p.2))⁻¹).re := by
    intro p
    have := hz (placeEquiv p.2)
    simp only [w, inv_inv]
    simp [mul_re]
    linarith
  have h := summable_norm_gaussAt (dualMat A 𝔞) (dualMat_det_ne_zero hA 𝔞) _ hb
  rw [← (Equiv.curry (Fin n) (Fin dq) ℤ).summable_iff]
  refine h.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [gaussAt_dualMat hA 𝔞 w, thetaTerm]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [w, inv_inv, qv_smul, map_mul, map_div₀, map_one, map_ofNat]
  push_cast
  ring_nf

lemma summable_norm_thetaTerm_dualSet {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) :
    Summable fun μ : dualSet 𝔞 => ‖thetaTerm ((1 / 4 : F) • A⁻¹) μ z‖ := by
  rw [← (dualSetEquiv 𝔞).summable_iff]
  refine (summable_norm_thetaTerm_dual hA 𝔞 hz).congr fun k => ?_
  simp [dualSetEquiv_coe]

/-- **Inversion with characteristics, set form**: `thetaLatChar_inversion` with the sums over $L$ and $L^\#$. -/
theorem tsum_latSet_char_inversion {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F) {z : InfinitePlace F → ℂ}
    (hz : ∀ v, 0 < (z v).im) :
    ∑' x : latSet 𝔞, thetaTerm A ((x : Fin n → F) + η) (fun v => -(z v)⁻¹) =
      (((∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (𝔞 i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * z v / 2) ^ ((n : ℂ) / 2)) *
          ∑' μ : dualSet 𝔞, thetaTerm ((1 / 4 : F) • A⁻¹) μ z *
            cexp (2 * Real.pi * Complex.I *
              ((Algebra.trace ℚ F (∑ i, (μ : Fin n → F) i * η i) : ℚ) : ℂ)) := by
  rw [← thetaLatChar_eq_tsum_latSet, thetaLatChar_inversion hA 𝔞 η hz, ← (dualSetEquiv 𝔞).tsum_eq]
  simp_rw [dualSetEquiv_coe]

/-! ### The expansion at a cusp -/

lemma qv_smul_vec (A : Matrix (Fin n) (Fin n) F) (c : F) (w : Fin n → F) :
    qv A (c • w) = c ^ 2 * qv A w := by
  simp only [qv, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma im_neg_inv_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-w⁻¹).im := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hw (Complex.normSq_pos.2 hw0)

/-- **The cusp point** $\big(\frac{\varphi_v(\alpha)}{\varphi_v(c)} - \frac{1}{\varphi_v(c)^2u_v}\big)_v$ near the cusp $\alpha/c$. -/
@[kb "iwaniec1997" "§10.4, expansion at a cusp [unverified]"]
def cuspPt (α c : F) (u : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => (realEmb F v (α / c) : ℂ) - ((realEmb F v c : ℂ) ^ 2 * u v)⁻¹

lemma cuspPt_im_pos (α : F) {c : F} (hc : c ≠ 0) {u : InfinitePlace F → ℂ} (hu : ∀ v, 0 < (u v).im)
    (v : InfinitePlace F) : 0 < (cuspPt α c u v).im := by
  have hc' : (realEmb F v c : ℝ) ≠ 0 := by
    intro h; exact hc ((map_eq_zero_iff _ (realEmb F v).injective).mp h)
  have h1 : 0 < ((realEmb F v c : ℂ) ^ 2 * u v).im := by
    rw [show ((realEmb F v c : ℂ) ^ 2 * u v) = (((realEmb F v c) ^ 2 : ℝ) : ℂ) * u v by push_cast; ring,
      im_ofReal_mul]
    exact mul_pos (by positivity) (hu v)
  have := im_neg_inv_pos h1
  simp only [cuspPt, sub_eq_add_neg, add_im, ofReal_im, zero_add]
  exact this

/-- One term at the cusp: $e(\sum_v\varphi_v(Q(\rho + cy))P_v) = e(\operatorname{Tr}\frac{\alpha}{c}Q(\rho + cy))\,
e(\sum_v\varphi_v(Q(y + \rho/c))(-1/u_v))$. -/
lemma thetaTerm_cuspPt (A : Matrix (Fin n) (Fin n) F) (α : F) {c : F} (hc : c ≠ 0)
    (ρ y : Fin n → F) (u : InfinitePlace F → ℂ) :
    thetaTerm A (ρ + c • y) (cuspPt α c u) =
      cexp (2 * Real.pi * Complex.I *
        ((Algebra.trace ℚ F (α / c * qv A (ρ + c • y)) : ℚ) : ℂ)) *
      thetaTerm A (y + c⁻¹ • ρ) (fun v => -(u v)⁻¹) := by
  have hρ : ρ + c • y = c • (y + c⁻¹ • ρ) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
  rw [thetaTerm, thetaTerm, ← Complex.exp_add]
  congr 1
  have htr := sum_realEmb (α / c * qv A (ρ + c • y))
  have htr' : ((Algebra.trace ℚ F (α / c * qv A (ρ + c • y)) : ℚ) : ℂ) =
      ∑ v, ((realEmb F v (α / c * qv A (ρ + c • y)) : ℝ) : ℂ) := by
    rw [← ofReal_ratCast, ← htr]; push_cast; rfl
  rw [htr', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hc' : (realEmb F v c : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; intro h; exact hc ((map_eq_zero_iff _ (realEmb F v).injective).mp h)
  rw [cuspPt]
  conv_lhs => rw [hρ, qv_smul_vec]
  rw [hρ, qv_smul_vec]
  simp only [map_mul, map_pow, map_div₀]
  push_cast
  field_simp
  ring

/-- **The expansion of a theta series at a cusp.** Let $\alpha, c \in F$, $c \ne 0$, $\rho : R \to F^n$ ($R$ finite) with
$R \times L \simeq L$, $(r, y) \mapsto \rho(r) + cy$ (the equivalence `e`, with `he`), and
$\operatorname{Tr}(\frac{\alpha}{c}(Q(\rho(r) + cy) - Q(\rho(r)))) \in \mathbb{Z}$ (`hint`). For $\operatorname{Im}u_v > 0$:
$$\sum_{x\in L}e\Big(\sum_v\varphi_v(Q(x))\Big(\frac{\alpha_v}{c_v} - \frac{1}{c_v^2u_v}\Big)\Big)
  = C_L(u)\sum_{\mu\in L^\#}e\Big(\sum_v\varphi_v(Q^\#(\mu))u_v\Big)\sum_{r\in R}
    e\Big(\operatorname{Tr}\Big(\frac{\alpha}{c}Q(\rho(r)) + \sum_i\mu_i\frac{\rho(r)_i}{c}\Big)\Big),$$
$C_L(u) = (\prod_v\sqrt{\det\varphi_v(A)})^{-1}(\prod_i\Delta(I_i))^{-1}\prod_v(-iu_v/2)^{n/2}$, $Q^\#(\mu) = \frac14\mu^{\mathsf T}A^{-1}\mu$.
For $F = \mathbb{Q}$ this is `QuadFormsKB.Siegel.thetaGram_cusp` (with $u = w/c$). -/
@[kb "iwaniec1997" "§10.4, expansion at a cusp [unverified]"]
theorem tsum_latSet_cusp {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (α c : F) (hc : c ≠ 0) {R : Type*} [Fintype R]
    (ρ : R → Fin n → F) (e : R × latSet 𝔞 ≃ latSet 𝔞)
    (he : ∀ p, (e p : Fin n → F) = ρ p.1 + c • (p.2 : Fin n → F))
    (hint : ∀ r (y : latSet 𝔞), ∃ m : ℤ,
      Algebra.trace ℚ F (α / c * (qv A (ρ r + c • (y : Fin n → F)) - qv A (ρ r))) = m)
    {u : InfinitePlace F → ℂ} (hu : ∀ v, 0 < (u v).im) :
    ∑' x : latSet 𝔞, thetaTerm A x (cuspPt α c u) =
      (((∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (𝔞 i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * u v / 2) ^ ((n : ℂ) / 2)) *
          ∑' μ : dualSet 𝔞, thetaTerm ((1 / 4 : F) • A⁻¹) μ u *
            ∑ r, cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
              (α / c * qv A (ρ r) + ∑ i, (μ : Fin n → F) i * (c⁻¹ * ρ r i)) : ℚ) : ℂ)) := by
  have hu0 : ∀ v, u v ≠ 0 := fun v h => by have := hu v; rw [h] at this; simp at this
  set C := (((∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (𝔞 i))⁻¹ : ℝ) : ℂ) *
    (∏ v, (-Complex.I * u v / 2) ^ ((n : ℂ) / 2)) with hC
  set E : R → ℂ := fun r => cexp (2 * Real.pi * Complex.I *
    ((Algebra.trace ℚ F (α / c * qv A (ρ r)) : ℚ) : ℂ)) with hE
  have hsplit : ∀ p : R × latSet 𝔞, thetaTerm A (e p) (cuspPt α c u) =
      E p.1 * thetaTerm A ((p.2 : Fin n → F) + c⁻¹ • ρ p.1) (fun v => -(u v)⁻¹) := by
    intro p
    rw [he, thetaTerm_cuspPt A α hc _ _ u]
    congr 1
    obtain ⟨m, hm⟩ := hint p.1 p.2
    rw [hE]
    simp only
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    have : Algebra.trace ℚ F (α / c * qv A (ρ p.1 + c • (p.2 : Fin n → F))) =
        Algebra.trace ℚ F (α / c * qv A (ρ p.1)) + m := by
      rw [← hm, ← map_add]; ring_nf
    rw [this]; push_cast; ring
  have hsum : Summable fun p : R × latSet 𝔞 => thetaTerm A (e p) (cuspPt α c u) :=
    (e.summable_iff.mpr (summable_norm_thetaTerm_latSet hA 𝔞
      (cuspPt_im_pos α hc hu)).of_norm)
  rw [← e.tsum_eq, hsum.tsum_prod, tsum_fintype]
  simp_rw [hsplit, tsum_mul_left]
  simp_rw [tsum_latSet_char_inversion hA 𝔞 _ hu]
  -- move the finite sum inside
  have hsm : ∀ r : R, Summable fun μ : dualSet 𝔞 =>
      E r * (thetaTerm ((1 / 4 : F) • A⁻¹) μ u * cexp (2 * Real.pi * Complex.I *
        ((Algebra.trace ℚ F (∑ i, (μ : Fin n → F) i * (c⁻¹ • ρ r) i) : ℚ) : ℂ))) := by
    intro r
    refine Summable.mul_left _ ?_
    refine Summable.of_norm_bounded (summable_norm_thetaTerm_dualSet hA 𝔞 hu) fun μ => ?_
    rw [norm_mul]
    have : ‖cexp (2 * Real.pi * Complex.I *
        ((Algebra.trace ℚ F (∑ i, (μ : Fin n → F) i * (c⁻¹ • ρ r) i) : ℚ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, mul_one]
  rw [← hC]
  have : ∀ r : R, E r * (C * ∑' μ : dualSet 𝔞, thetaTerm ((1 / 4 : F) • A⁻¹) μ u *
        cexp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (∑ i, (μ : Fin n → F) i * (c⁻¹ • ρ r) i) : ℚ) : ℂ))) =
      C * ∑' μ : dualSet 𝔞, E r * (thetaTerm ((1 / 4 : F) • A⁻¹) μ u *
        cexp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (∑ i, (μ : Fin n → F) i * (c⁻¹ • ρ r) i) : ℚ) : ℂ))) := by
    intro r; rw [tsum_mul_left]; ring
  simp_rw [this]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun r _ => hsm r]
  congr 1
  refine tsum_congr fun μ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hE]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm, ← Complex.exp_add, map_add]
  congr 2
  push_cast
  ring

end

end QuadFormsKB.HilbertModular
