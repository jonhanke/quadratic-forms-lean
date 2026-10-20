import QuadFormsKB.HilbertModular.ThetaInversion

/-!
# Theta series over a totally real field III: theta with characteristics

Notation of `Theta.lean` / `ThetaInversion.lean`. For a shift $\eta \in F^n$ (a *characteristic*),
$$\theta_{A,L}(z;\eta) = \sum_{x\in L}e\Big(\sum_v\varphi_v\big((x+\eta)^{\mathsf T}A(x+\eta)\big)z_v\Big)\qquad(\texttt{thetaLatChar}).$$

**Inversion with characteristics** (`thetaLatChar_inversion`): for $\operatorname{Im}z_v > 0$,
$$\theta_{A,L}(-1/z;\eta) = \frac{1}{\sqrt{N(\det A)}\prod_i\Delta(I_i)}\prod_v\Big(\frac{-iz_v}{2}\Big)^{n/2}
  \sum_{\mu\in L^\#}e\Big(\sum_v\varphi_v(Q^\#(\mu))z_v\Big)\,e\Big(\operatorname{Tr}_{F/\mathbb{Q}}\sum_i\mu_i\eta_i\Big),$$
$Q^\#(\mu) = \frac14\mu^{\mathsf T}A^{-1}\mu$, $L^\# = \bigoplus_iI_i^\vee$. For $\eta = 0$ it is `thetaLat_inversion`. This is step 1 of
the $\mathbb{Q}$ proof of the $\Gamma_0(N)$ law (`QuadFormsKB.Siegel.thetaChar_S`), over $F$.

*Proof.* Shifted Poisson summation `tsum_gaussAtShift`; the shift in lattice coordinates is $c_{il} = $ the $\beta^{(i)}$-coordinates of
$\eta_i$ (`Module.Basis.repr`), and $\sum_{i,l}m_{il}c_{il} = \operatorname{Tr}\sum_i\mu_i\eta_i$ by trace duality (`sum_mul_repr_eq_trace`).
-/

open Matrix NumberField NumberField.InfinitePlace Complex
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-- **Theta series with characteristic** $\eta \in F^n$: $\theta_{A,L}(z;\eta) = \sum_{x\in L}e(\sum_v\varphi_v(Q(x+\eta))z_v)$. -/
@[kb "freitag1990" "Ch. I §4, theta series with characteristics [unverified]"]
def thetaLatChar (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (η : Fin n → F) (z : InfinitePlace F → ℂ) : ℂ :=
  ∑' k : Fin n → Fin (Module.finrank ℚ F) → ℤ, thetaTerm A (latVec 𝔞 k + η) z

lemma thetaLatChar_zero (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℂ) : thetaLatChar A 𝔞 0 z = thetaLat A 𝔞 z := by
  simp [thetaLatChar, thetaLat]

/-- The coordinates $c_{il}$ of the characteristic in the bases $\beta^{(i)}$, as a real vector. -/
def charCoord (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F) : Fin n × Fin dq → ℝ :=
  fun p => ((QuadFormsKB.Analysis.bq (𝔞 p.1)).repr (η p.1) p.2 : ℝ)

/-- The Gaussian at a real vector $u$ with $(Ku)_{(i,j)} = \varphi_{v_j}(x_i)$ is the theta term of $x$. -/
lemma gauss_blockMat_vec (S : Matrix (Fin n) (Fin n) F) (B : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ v, (B v)ᵀ * B v = S.map (realEmb F v)) (Y : Fin n → Fin (Module.finrank ℚ F) → F)
    (w : InfinitePlace F → ℂ) (u : Fin n × Fin dq → ℝ) (x : Fin n → F)
    (hu : ∀ i j, (coordMat Y *ᵥ u) (i, j) = realEmb F (placeEquiv j) (x i)) :
    cexp (-Real.pi * ∑ p : Fin n × Fin dq, w (placeEquiv p.2) *
        ((((blockMat B * coordMat Y) *ᵥ u) p : ℝ) : ℂ) ^ 2) =
      cexp (-Real.pi * ∑ v, w v * (realEmb F v (qv S x) : ℂ)) := by
  congr 2
  rw [← Matrix.mulVec_mulVec, Fintype.sum_prod_type, Finset.sum_comm]
  rw [← (placeEquiv (F := F)).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [blockMat_mulVec, hu]
  rw [← Finset.mul_sum]
  congr 1
  rw [realEmb_qv, ← hB, ← sum_sq_mulVec]
  push_cast
  rfl

lemma coordMat_shift (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F)
    (k : Fin n × Fin dq → ℤ) (i : Fin n) (j : Fin dq) :
    (coordMat (fun i => QuadFormsKB.Analysis.bq (𝔞 i)) *ᵥ fun p => (k p : ℝ) + charCoord 𝔞 η p) (i, j) =
      realEmb F (placeEquiv j) ((latVec 𝔞 (Equiv.curry _ _ _ k) + η) i) := by
  rw [coordMat_mulVec, Pi.add_apply, latVec_curry]
  have hη : η i = ∑ l, ((QuadFormsKB.Analysis.bq (𝔞 i)).repr (η i) l : F) *
      QuadFormsKB.Analysis.bq (𝔞 i) l := by
    conv_lhs => rw [← (QuadFormsKB.Analysis.bq (𝔞 i)).sum_repr (η i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def]; rfl
  rw [hη, ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [charCoord, ← add_mul, map_mul, map_add, map_intCast, map_ratCast]
  ring

lemma thetaTerm_shift_eq {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F) (z : InfinitePlace F → ℂ)
    (k : Fin n × Fin dq → ℤ) :
    thetaTerm A (latVec 𝔞 (Equiv.curry _ _ _ k) + η) z =
      gaussAtShift (fun p => -2 * Complex.I * z (placeEquiv p.2)) (latMat A 𝔞) (charCoord 𝔞 η) k := by
  rw [gaussAtShift, latMat, gauss_blockMat_vec A _ (gramSqrt_transpose_mul_self hA) _
    (fun v => -2 * Complex.I * z v) _ _ (coordMat_shift 𝔞 η k), thetaTerm]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring_nf

/-- $\sum_{i,l}m_{il}c_{il} = \operatorname{Tr}\sum_i\mu_i\eta_i$ for $\mu$ = `dualLatVec 𝔞 m`. -/
lemma sum_mul_repr_eq_trace (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F)
    (m : Fin n × Fin dq → ℤ) :
    ∑ p, (m p : ℝ) * charCoord 𝔞 η p =
      ((Algebra.trace ℚ F (∑ i, dualLatVec 𝔞 (Equiv.curry _ _ _ m) i * η i) : ℚ) : ℝ) := by
  rw [Fintype.sum_prod_type, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualLatVec_curry]
  simp only
  conv_rhs => rw [← (QuadFormsKB.Analysis.bq (𝔞 i)).sum_repr (η i)]
  rw [Finset.sum_mul, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, map_sum]
  have : ∀ l', Algebra.trace ℚ F ((m (i, l) : F) * (QuadFormsKB.Analysis.bq (𝔞 i)).traceDual l *
      ((QuadFormsKB.Analysis.bq (𝔞 i)).repr (η i) l' • QuadFormsKB.Analysis.bq (𝔞 i) l')) =
      if l = l' then (m (i, l) : ℚ) * (QuadFormsKB.Analysis.bq (𝔞 i)).repr (η i) l else 0 := by
    intro l'
    rw [Algebra.smul_def, show (m (i, l) : F) = algebraMap ℚ F (m (i, l)) by simp]
    rw [show algebraMap ℚ F (m (i, l)) * (QuadFormsKB.Analysis.bq (𝔞 i)).traceDual l *
        (algebraMap ℚ F ((QuadFormsKB.Analysis.bq (𝔞 i)).repr (η i) l') *
          QuadFormsKB.Analysis.bq (𝔞 i) l') =
        ((m (i, l) : ℚ) * (QuadFormsKB.Analysis.bq (𝔞 i)).repr (η i) l') •
          (QuadFormsKB.Analysis.bq (𝔞 i) l' * (QuadFormsKB.Analysis.bq (𝔞 i)).traceDual l) by
      rw [Algebra.smul_def, map_mul]; ring]
    rw [map_smul, Module.Basis.trace_mul_traceDual, smul_eq_mul]
    by_cases h : l = l'
    · subst h; simp
    · simp [h, Ne.symm h]
  simp_rw [this]
  simp [charCoord]

/-- **Inversion with characteristics.** For $\eta \in F^n$ and $\operatorname{Im} z_v > 0$:
$$\theta_{A,L}(-1/z;\eta) = \Big(\prod_v\sqrt{\det\varphi_v(A)}\Big)^{-1}\Big(\prod_i\Delta(I_i)\Big)^{-1}\prod_v\Big(\frac{-iz_v}{2}\Big)^{n/2}
  \sum_{\mu\in L^\#}e\Big(\sum_v\varphi_v(Q^\#(\mu))z_v\Big)e\Big(\operatorname{Tr}\sum_i\mu_i\eta_i\Big).$$ -/
@[kb "freitag1990" "Ch. I §4, theta series with characteristics [unverified]"]
theorem thetaLatChar_inversion {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (η : Fin n → F) {z : InfinitePlace F → ℂ}
    (hz : ∀ v, 0 < (z v).im) :
    thetaLatChar A 𝔞 η (fun v => -(z v)⁻¹) =
      (((∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (𝔞 i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * z v / 2) ^ ((n : ℂ) / 2)) *
          ∑' m : Fin n → Fin (Module.finrank ℚ F) → ℤ,
            thetaTerm ((1 / 4 : F) • A⁻¹) (dualLatVec 𝔞 m) z *
              cexp (2 * Real.pi * Complex.I *
                ((Algebra.trace ℚ F (∑ i, dualLatVec 𝔞 m i * η i) : ℚ) : ℂ)) := by
  have hz0 : ∀ v, z v ≠ 0 := fun v h => by have := hz v; rw [h] at this; simp at this
  have hw : ∀ v, 0 < (-(z v)⁻¹).im := fun v => by
    have := hz v
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos this (Complex.normSq_pos.2 (hz0 v))
  set w : InfinitePlace F → ℂ := fun v => -2 * Complex.I * (-(z v)⁻¹)
  have hwinv : ∀ v, (w v)⁻¹ = -Complex.I * z v / 2 := fun v => by
    simp only [w]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have h := tsum_gaussAtShift (latMat A 𝔞) (dualMat A 𝔞) (latMat_transpose_mul hA 𝔞)
    (fun p => w (placeEquiv p.2)) (rate_re_pos (n := n) hw) (charCoord 𝔞 η)
  rw [thetaLatChar, ← (Equiv.curry (Fin n) (Fin dq) ℤ).tsum_eq]
  simp_rw [thetaTerm_shift_eq hA 𝔞 η (fun v => -(z v)⁻¹)]
  rw [h, abs_det_latMat hA, ← (Equiv.curry (Fin n) (Fin dq) ℤ).tsum_eq]
  simp_rw [gaussAt_dualMat hA 𝔞 w, hwinv, prod_rate_cpow (fun v => -Complex.I * z v / 2),
    sum_mul_repr_eq_trace 𝔞 η]
  rw [mul_inv]
  push_cast
  congr 1
  refine tsum_congr fun m => ?_
  congr 1
  rw [thetaTerm]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [qv_smul, map_mul]
  simp only [map_div₀, map_one, map_ofNat]
  push_cast
  ring_nf

end

end QuadFormsKB.HilbertModular
