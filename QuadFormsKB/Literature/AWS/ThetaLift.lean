/-
# Hanke, AWS 2009 notes, §4.4 and §4.6: realizing $\Theta_{L_j}$ as a theta lift

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.4 (theta kernels
and theta lifts, pp. 60–61) and §4.6 (pp. 63–66). The list D1, D2, … of the notes' derivations is in
`AWS/Overview.lean`; this file is **D14, D20, D21, D22, D23** (and the corollary D24).

**Setting.** $Q$ is a quadratic form over $\mathbb{Q}$ in $n$ variables (`QuadForm ℚ n`; in the notes
a positive definite integer-valued form), $H = C + C^{\mathsf T}$ its Hessian (`QuadForm.hessian`),
$V = \mathbb{Q}^n$, $L = \mathbb{Z}^n$, and $G = O(V_\mathbb{A})$, $\Gamma = O(V)$, $K = K_\mathbb{A}$ as in
`AWS/Adelic.lean`. For $z = x + iy \in \mathcal{H}$, $g_{\infty,z} = \begin{pmatrix}1&x\\0&1\end{pmatrix}
\begin{pmatrix}\sqrt y&0\\0&\sqrt y^{-1}\end{pmatrix}$ (p. 65).

**What is formalized.**
- The archimedean Weil representation on the Borel subgroup, by the notes' transformation formulas
  1 and 2 (p. 59) at $v = \infty$: `weilN` ($W(n(x))$) and `weilM` ($W(m(a))$, $a > 0$, where
  $\chi_{V,\infty}(a) = (a, (-1)^{n/2}\det Q)_\mathbb{R} = 1$). No input is needed: we only use these
  elements, and $W(g_{\infty,z}) = W(n(x))\,W(m(\sqrt y))$ ((4.24)) is how $W(g_{\infty,z})$ is
  *defined* here (for the full Weil representation it is the homomorphism property).
- **D22** `weil_gaussian` ((4.24)–(4.30)): $(W(g_{\infty,z})\varphi_\infty)(h_\infty^{-1}\vec v) =
  y^{n/4} e^{2\pi i z Q(\vec v)}$ for $h_\infty \in O(V_\infty)$, $\varphi_\infty = e^{-2\pi Q}$.
- The theta kernel `thetaKernel` at $g_\mathbb{A} = (g_{\infty,z}, 1_f)$, and **D14** (the $O(V)$ half of
  Lemma 4.4.1) `thetaKernel_left_inv`: it is left $O(V)$-invariant.
- **D20** `thetaKernel_mul_mem` ((4.18)–(4.22)): $\theta(g_{\infty,z}, \alpha_j h) = \sum_{\vec v \in L_j}
  y^{n/4} e^{2\pi i z Q(\vec v)}$ for $h \in K_\mathbb{A}$, $\alpha_{j,\infty} = 1$.
- **D23** `thetaLift_indicator_eq`, `thetaLift_classical` ((4.31)–(4.37)): relative to the inputs
  (`QuotientIntegralInputs`, `AWSInputs`),
  $y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,\Theta_{L_j}(z)$.
- **D21** `thetaLift_depends_only_on_infty` ((4.23)): with strong approximation for $\mathrm{SL}_2$ and the
  invariance of the kernel as inputs, the lift depends only on $g_\infty$.

*Erratum (candidate; pending author):* §4.4, p. 60, defines $\varphi_\infty(\vec v) := e^{-\pi Q(\vec v)}$,
but (4.27) uses $\varphi_\infty(\vec w) = e^{-2\pi Q(\vec w)}$, which is what gives (4.30) and the
holomorphic $\Theta_{L_j}$. With $e^{-\pi Q}$ one gets $y^{n/4}e^{2\pi i x Q(\vec v)}e^{-\pi y Q(\vec v)}$
instead (`weil_gaussian_pi`, `weil_gaussian_pi_ne`).

*Erratum (candidate; pending author):* (4.25), p. 65, writes
$y^{n/4}\bigl(W(\begin{smallmatrix}1&x\\0&1\end{smallmatrix})\varphi_\infty\bigr)(\sqrt y\,h_\infty^{-1}\vec v)$;
this would give $e^{2\pi i x y Q(\vec v)}$ in (4.26). The correct intermediate step is
$e^{2\pi i x Q(h_\infty^{-1}\vec v)}\,\bigl(W(m(\sqrt y))\varphi_\infty\bigr)(h_\infty^{-1}\vec v) =
y^{n/4}e^{2\pi i xQ(\vec v)}\varphi_\infty(\sqrt y\,h_\infty^{-1}\vec v)$ (the operators must be applied
in the order $W(n(x))\,W(m(\sqrt y))$); (4.26) is then correct as printed.
-/
import QuadFormsKB.Literature.AWS.Unfolding
import QuadFormsKB.Literature.AWS.Adelic
import QuadFormsKB.Defs.QuadForm

open Matrix MeasureTheory Complex Real
open scoped Pointwise UpperHalfPlane

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-! ### The quadratic form over ℝ -/

/-- **Homogeneity:** $Q(c\vec w) = c^2 Q(\vec w)$. -/
theorem evalIn_smul (Q : QuadForm ℚ n) (c : ℝ) (w : Fin n → ℝ) :
    Q.evalIn ℝ (c • w) = c ^ 2 * Q.evalIn ℝ w := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- $2Q(\vec w) = \vec w^{\mathsf T} H \vec w$ with $H$ the Hessian. -/
theorem two_mul_evalIn (Q : QuadForm ℚ n) (w : Fin n → ℝ) :
    2 * Q.evalIn ℝ w = w ⬝ᵥ (Q.hessian.map (algebraMap ℚ ℝ) *ᵥ w) := by
  rw [← QuadForm.polar_eq_hessian, show w + w = (2 : ℝ) • w by rw [two_smul], evalIn_smul]
  ring

/-- **$O(V_\infty)$ preserves $Q$:** $Q(g\vec w) = Q(\vec w)$ for $g \in O(V)(\mathbb{R})$
(used in (4.28)–(4.29)). -/
theorem evalIn_orth (Q : QuadForm ℚ n) {g : GL (Fin n) ℝ} (hg : g ∈ orthGroup Q.hessian ℝ)
    (w : Fin n → ℝ) : Q.evalIn ℝ (g.val *ᵥ w) = Q.evalIn ℝ w := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [two_mul_evalIn, two_mul_evalIn]
  have hg' := mem_orthGroup.mp hg
  calc (g.val *ᵥ w) ⬝ᵥ (Q.hessian.map (algebraMap ℚ ℝ) *ᵥ (g.val *ᵥ w))
      = w ⬝ᵥ (g.valᵀ *ᵥ (Q.hessian.map (algebraMap ℚ ℝ) *ᵥ (g.val *ᵥ w))) := by
        rw [dotProduct_mulVec w (g.valᵀ), vecMul_transpose]
    _ = w ⬝ᵥ ((g.valᵀ * Q.hessian.map (algebraMap ℚ ℝ) * g.val) *ᵥ w) := by
        simp only [mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hg']

/-- The real vector of a rational vector. -/
noncomputable abbrev castR (v : Fin n → ℚ) : Fin n → ℝ := fun i => (v i : ℝ)

/-- The $p$-adic vector of a rational vector. -/
noncomputable abbrev castP (p : ℕ) [Fact p.Prime] (v : Fin n → ℚ) : Fin n → ℚ_[p] := fun i => (v i : ℚ_[p])

theorem evalIn_castR (Q : QuadForm ℚ n) (v : Fin n → ℚ) :
    Q.evalIn ℝ (castR v) = (Q.evalIn ℚ v : ℝ) := by
  simp only [QuadForm.evalIn, castR, eq_ratCast, Algebra.algebraMap_self, RingHom.id_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-! ### The archimedean Weil representation on the Borel subgroup (§4.3, formulas 1–2) -/

/-- **$W(n(x))$ at $v = \infty$** (§4.3, formula 2, p. 59):
$\bigl(W(\begin{smallmatrix}1&x\\0&1\end{smallmatrix})\Phi\bigr)(\vec w) = e^{2\pi i x Q(\vec w)}\,\Phi(\vec w)$. -/
@[kb "hanke2011aws" "§4.3, formula 2, p. 59"]
noncomputable def weilN (Q : QuadForm ℚ n) (x : ℝ) (Φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun w => cexp (2 * π * Complex.I * x * Q.evalIn ℝ w) * Φ w

/-- **$W(m(a))$ at $v = \infty$, $a > 0$** (§4.3, formula 1, p. 59):
$\bigl(W(\begin{smallmatrix}a&0\\0&a^{-1}\end{smallmatrix})\Phi\bigr)(\vec w) = |a|^{n/2}\,\Phi(a\vec w)$
(for $a > 0$, $\chi_{V,\infty}(a) = (a, (-1)^{n/2}\det Q)_\mathbb{R} = 1$). -/
@[kb "hanke2011aws" "§4.3, formula 1, p. 59"]
noncomputable def weilM (a : ℝ) (Φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun w => ((a ^ ((n : ℝ) / 2) : ℝ) : ℂ) * Φ (a • w)

/-- **The archimedean Gaussian** $\varphi_\infty(\vec w) = e^{-2\pi Q(\vec w)}$ (as used in (4.27);
see the erratum in the module docstring for the printed $e^{-\pi Q}$ of p. 60). -/
noncomputable def gaussian (Q : QuadForm ℚ n) : (Fin n → ℝ) → ℂ :=
  fun w => cexp (-2 * π * Q.evalIn ℝ w)

/-- **$W(g_{\infty,z})\varphi_\infty$** $:= W(n(x))\,W(m(\sqrt y))\,\varphi_\infty$, $z = x + iy$ ((4.24)). -/
noncomputable def weilGauss (Q : QuadForm ℚ n) (z : ℍ) : (Fin n → ℝ) → ℂ :=
  weilN Q z.re (weilM (Real.sqrt z.im) (gaussian Q))

theorem sqrt_rpow (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ^ ((n : ℝ) / 2) = y ^ ((n : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
  congr 1; ring

/-- **D22: (4.24)–(4.30), p. 65.** For $z = x+iy \in \mathcal{H}$, $h_\infty \in O(V_\infty)$ and
$\vec w \in \mathbb{R}^n$,
$$\bigl(W(g_{\infty,z})\varphi_\infty\bigr)(h_\infty^{-1}\vec w) = y^{n/4}\,e^{2\pi i z Q(\vec w)}.$$ -/
@[kb "hanke2011aws" "§4.6, (4.24)-(4.30), p. 65"]
theorem weil_gaussian (Q : QuadForm ℚ n) (z : ℍ) {h : GL (Fin n) ℝ}
    (hh : h ∈ orthGroup Q.hessian ℝ) (w : Fin n → ℝ) :
    weilGauss Q z (h⁻¹.val *ᵥ w) = ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
      cexp (2 * π * Complex.I * (z : ℂ) * Q.evalIn ℝ w) := by
  have hQ : Q.evalIn ℝ (h⁻¹.val *ᵥ w) = Q.evalIn ℝ w :=
    evalIn_orth Q ((orthGroup Q.hessian ℝ).inv_mem hh) w
  have hy : 0 ≤ z.im := z.im_pos.le
  simp only [weilGauss, weilN, weilM, gaussian, evalIn_smul, hQ, Real.sq_sqrt hy, sqrt_rpow _ hy]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  rw [show (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I from (re_add_im (z : ℂ)).symm]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- **The Gaussian as printed** $e^{-\pi Q}$ (§4.4, p. 60). -/
noncomputable def gaussianPi (Q : QuadForm ℚ n) : (Fin n → ℝ) → ℂ :=
  fun w => cexp (-π * Q.evalIn ℝ w)

/-- **Check of the erratum to p. 60:** with the printed $\varphi_\infty = e^{-\pi Q}$ the computation
(4.24)–(4.30) gives $y^{n/4} e^{2\pi i x Q(\vec w)} e^{-\pi y Q(\vec w)}$. -/
theorem weil_gaussian_pi (Q : QuadForm ℚ n) (z : ℍ) (w : Fin n → ℝ) :
    weilN Q z.re (weilM (Real.sqrt z.im) (gaussianPi Q)) w = ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
      (cexp (2 * π * Complex.I * z.re * Q.evalIn ℝ w) * cexp (-π * z.im * Q.evalIn ℝ w)) := by
  have hy : 0 ≤ z.im := z.im_pos.le
  simp only [weilN, weilM, gaussianPi, evalIn_smul, Real.sq_sqrt hy, sqrt_rpow _ hy]
  push_cast
  ring_nf

/-- **The printed Gaussian does not give (4.30):** for $Q(\vec w) \ne 0$ the two values differ (their
absolute values are $y^{n/4}e^{-\pi y Q(\vec w)} \ne y^{n/4}e^{-2\pi y Q(\vec w)}$). -/
theorem weil_gaussian_pi_ne (Q : QuadForm ℚ n) (z : ℍ) (w : Fin n → ℝ) (hw : Q.evalIn ℝ w ≠ 0) :
    weilN Q z.re (weilM (Real.sqrt z.im) (gaussianPi Q)) w ≠
      ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * Q.evalIn ℝ w) := by
  rw [weil_gaussian_pi]
  intro h
  have hy := z.im_pos
  have hc : ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hy _).ne'
  have h' := mul_left_cancel₀ hc h
  have hn := congrArg (fun c : ℂ => ‖c‖) h'
  simp only [norm_mul, Complex.norm_exp] at hn
  have e1 : (2 * π * Complex.I * (z.re : ℂ) * (Q.evalIn ℝ w : ℂ)).re = 0 := by simp
  have e2 : (-π * (z.im : ℂ) * (Q.evalIn ℝ w : ℂ)).re = -π * z.im * Q.evalIn ℝ w := by
    simp [mul_re]
  have e3 : (2 * π * Complex.I * (z : ℂ) * (Q.evalIn ℝ w : ℂ)).re = -2 * π * z.im * Q.evalIn ℝ w := by
    rw [show (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I from (re_add_im (z : ℂ)).symm]
    simp [mul_re, mul_im]
  rw [e1, e2, e3, Real.exp_zero, one_mul] at hn
  have := Real.exp_injective hn
  apply hw
  have hpi := Real.pi_pos
  nlinarith [mul_pos hpi hy, sq_nonneg (Q.evalIn ℝ w)]

/-! ### The theta kernel -/

variable (Q : QuadForm ℚ n)

open scoped Classical

/-- **The theta kernel** $\theta_\varphi(g_\mathbb{A}, h_\mathbb{A})$ (§4.4, p. 60) at
$g_\mathbb{A} = (g_{\infty,z}, 1_f)$, for $h_\mathbb{A} \in O(V_\mathbb{A})$:
$$\theta(z, h_\mathbb{A}) = \sum_{\vec v \in V(\mathbb{Q})} \bigl(W(g_{\infty,z})\varphi_\infty\bigr)(h_\infty^{-1}\vec v)
\cdot \mathbf{1}\bigl[h_p^{-1}\vec v \in \mathbb{Z}_p^n \text{ for all } p\bigr],$$
i.e. $\sum_{\vec v} (W(g_\mathbb{A})\varphi_\mathbb{A})(h_\mathbb{A}^{-1}\vec v)$ with
$\varphi_\mathbb{A} = \varphi_\infty \otimes \prod_p \mathbf{1}_{\mathbb{Z}_p^n}$ (the notes' "$F = \mathbb{Q}$ and the
standard lattice $L = \mathbb{Z}^n$") and $W(1_f)\varphi_f = \varphi_f$. -/
@[kb "hanke2011aws" "§4.4, p. 60"]
noncomputable def thetaKernel (z : ℍ) (h : OA Q.hessian) : ℂ :=
  ∑' v : Fin n → ℚ, weilGauss Q z (((h.1⁻¹ : orthGroup Q.hessian ℝ) : GL (Fin n) ℝ).val *ᵥ castR v) *
    (if ∀ p : PrimeIdx,
        IsIntVecP (p : ℕ) ((((h.2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]).val
          *ᵥ castP (p : ℕ) v) then 1 else 0)

/-- The summand of the theta kernel. -/
private noncomputable def kerTerm (z : ℍ) (h : OA Q.hessian) (v : Fin n → ℚ) : ℂ :=
  weilGauss Q z (((h.1⁻¹ : orthGroup Q.hessian ℝ) : GL (Fin n) ℝ).val *ᵥ castR v) *
    (if ∀ p : PrimeIdx,
        IsIntVecP (p : ℕ) ((((h.2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]).val
          *ᵥ castP (p : ℕ) v) then 1 else 0)

theorem castR_mulVec (M : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    M.map (algebraMap ℚ ℝ) *ᵥ castR v = castR (M *ᵥ v) := by
  funext i
  have := (RingHom.map_mulVec (algebraMap ℚ ℝ) M v i).symm
  simpa [Function.comp_def] using this

/-- **D14: the $O(V)$-half of Lemma 4.4.1 (p. 60–61).** The theta kernel is left-invariant under
$O(V)$: "it is also left-invariant under $O(V(F))$ because that action just permutes $V(F)$". -/
@[kb "hanke2011aws" "§4.4, Lemma 4.4.1, pp. 60-61"]
theorem thetaKernel_left_inv (z : ℍ) (γ : orthGroup Q.hessian ℚ) (h : OA Q.hessian) :
    thetaKernel Q z (diag Q.hessian γ * h) = thetaKernel Q z h := by
  -- reindex v ↦ γ v
  let e : (Fin n → ℚ) ≃ (Fin n → ℚ) :=
    { toFun := fun v => (γ : GL (Fin n) ℚ).val *ᵥ v
      invFun := fun v => (γ : GL (Fin n) ℚ)⁻¹.val *ᵥ v
      left_inv := fun v => by
        simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      right_inv := fun v => by
        simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] }
  unfold thetaKernel
  rw [← e.tsum_eq]
  congr 1
  funext v
  have hinf : (((diag Q.hessian γ * h).1⁻¹ : orthGroup Q.hessian ℝ) : GL (Fin n) ℝ).val *ᵥ castR (e v)
      = (((h.1⁻¹ : orthGroup Q.hessian ℝ) : GL (Fin n) ℝ)).val *ᵥ castR v := by
    simp only [e, Equiv.coe_fn_mk, Prod.fst_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
      ← mulVec_mulVec, ← castR_mulVec]
    congr 1
    simp only [diag, MonoidHom.prod_apply, ← map_inv, orthMap_val, mulVec_mulVec]
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one, Matrix.map_one _ (by simp) (by simp), one_mulVec]
  have hfin : ∀ p : PrimeIdx,
      (((diag Q.hessian γ * h).2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val *ᵥ castP (p : ℕ) (e v)
      = (((h.2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)])).1.val *ᵥ castP (p : ℕ) v := by
    intro p
    simp only [e, Equiv.coe_fn_mk, Prod.snd_mul, RestrictedProduct.mul_apply, _root_.mul_inv_rev,
      Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    congr 1
    have hc : castP (p : ℕ) ((γ : GL (Fin n) ℚ).val *ᵥ v) =
        (γ : GL (Fin n) ℚ).val.map (algebraMap ℚ ℚ_[(p : ℕ)]) *ᵥ castP (p : ℕ) v :=
      (mulVec_cast (p : ℕ) _ v).symm
    rw [hc, mulVec_mulVec]
    have : ((((diag Q.hessian γ).2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]).val
        = (γ : GL (Fin n) ℚ)⁻¹.val.map (algebraMap ℚ ℚ_[(p : ℕ)]) := by
      show ((orthMap Q.hessian ℚ_[(p : ℕ)] γ)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val = _
      rw [← map_inv, orthMap_val]; rfl
    rw [this, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (by simp) (by simp), one_mulVec]
  have hiff : (∀ p : PrimeIdx, IsIntVecP (p : ℕ)
      ((((diag Q.hessian γ * h).2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val *ᵥ
        castP (p : ℕ) (e v))) ↔
      (∀ p : PrimeIdx, IsIntVecP (p : ℕ)
        ((((h.2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)])).1.val *ᵥ castP (p : ℕ) v)) :=
    forall_congr' fun p => by rw [hfin p]
  rw [hinf, if_congr hiff rfl rfl]

/-- **The theta series of a lattice** $L \subset V$ (p. 63):
$\Theta_L(z) = \sum_{\vec v \in L} e^{2\pi i Q(\vec v) z}$ (as a `tsum` over $V(\mathbb{Q})$ of the terms
supported on $L$; for positive definite $Q$ it converges absolutely, which is not needed below). -/
@[kb "hanke2011aws" "§4.6, p. 63"]
noncomputable def thetaSeries (L : Lat n) (z : ℍ) : ℂ :=
  ∑' v : Fin n → ℚ, if v ∈ L.1 then cexp (2 * π * Complex.I * (z : ℂ) * (Q.evalIn ℚ v : ℂ)) else 0

/-- $\vec v \in \mathbb{Z}_p^n$ is unchanged by an element of $O(V)(\mathbb{Z}_p)$. -/
theorem isIntVecP_mulVec_iff {p : ℕ} [Fact p.Prime] {k : GL (Fin n) ℚ_[p]} (hk : IsIntP p k.val)
    (hk' : IsIntP p k⁻¹.val) (w : Fin n → ℚ_[p]) : IsIntVecP p (k.val *ᵥ w) ↔ IsIntVecP p w := by
  refine ⟨fun h => ?_, fun h => hk.mulVec h⟩
  have : w = k⁻¹.val *ᵥ (k.val *ᵥ w) := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [this]; exact hk'.mulVec h

/-- **D20: (4.18)–(4.22), p. 64.** For $\alpha \in O(V_\mathbb{A})$ with $\alpha_\infty = 1$ and
$h \in K_\mathbb{A}$, writing $L_\alpha = \alpha\mathbb{Z}^n$:
$$\theta(g_{\infty,z}, \alpha h) = \sum_{\vec v \in V(\mathbb{Q})} \mathbf 1_{L_\alpha}(\vec v)\,
y^{n/4}e^{2\pi i z Q(\vec v)}.$$
The finite part is (4.18)–(4.19) ("$h_p^{-1}\alpha_j^{-1}\vec v \in L_p$ for all $p \iff \vec v \in L_j$",
via Lemma 4.5.1), the archimedean part is (4.24)–(4.30) (`weil_gaussian`). In particular the
integrand of (4.17) is constant on $K_\mathbb{A}$.

*Update (candidate; pending author):* (4.22) already drops the finite components of
$W(g_\mathbb{A})\varphi_\mathbb{A}$, which is justified only after (4.23) (that $g_p$ acts trivially on
$\varphi_p$); here $g_\mathbb{A} = (g_{\infty,z}, 1_f)$, which is all that (4.31)–(4.37) use. -/
@[kb "hanke2011aws" "§4.6, (4.18)-(4.22), p. 64"]
theorem thetaKernel_mul_mem (hG : LatticeGluing n) (z : ℍ) (α : OA Q.hessian) (hα : α.1 = 1)
    {k : OA Q.hessian} (hk : k ∈ KA Q.hessian) :
    thetaKernel Q z (α * k) = ∑' v : Fin n → ℚ,
      if v ∈ (latSMul Q.hessian hG α stdLat).1 then
        ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (Q.evalIn ℚ v : ℂ))
      else 0 := by
  unfold thetaKernel
  congr 1; funext v
  have hinf : weilGauss Q z ((((α * k).1⁻¹ : orthGroup Q.hessian ℝ) : GL (Fin n) ℝ).val *ᵥ castR v)
      = ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (Q.evalIn ℚ v : ℂ)) := by
    have := weil_gaussian Q z ((α * k).1).2 (castR v)
    rw [evalIn_castR] at this
    exact this
  have hfin : (∀ p : PrimeIdx, IsIntVecP (p : ℕ)
      ((((α * k).2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val *ᵥ castP (p : ℕ) v)) ↔
      v ∈ (latSMul Q.hessian hG α stdLat).1 := by
    rw [mem_latSMul_std_iff]
    refine forall_congr' fun p => ?_
    have e : (((α * k).2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val =
        ((k.2 p)⁻¹ : orthGroup Q.hessian ℚ_[(p : ℕ)]).1.val *
          (((α.2 p) : orthGroup Q.hessian ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)])⁻¹.val := by
      simp [RestrictedProduct.mul_apply, _root_.mul_inv_rev]
    rw [e, ← mulVec_mulVec]
    have hkp := hk p
    exact isIntVecP_mulVec_iff (by simpa using hkp.2) (by simpa using hkp.1) _
  rw [hinf, if_congr hfin rfl rfl]
  split_ifs <;> simp

/-- **The inputs of the theta-lift computation** (besides the quotient integral,
`QuotientIntegralInputs`), for the form $Q$ with Hessian $H$:

- `gluing`: Lemma 4.5.1, existence half (`LatticeGluing`; cited from Shimura, *Arithmetic of
  Quadratic Forms*, Lem. 21.6, and Weil, *Basic Number Theory*, V Thm. 2);
- `finite_classes`: the class number is finite, $|O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A}| < \infty$
  (reduction theory; Borel–Harish-Chandra; for positive definite $Q$ also elementary, e.g. Cassels,
  *Rational Quadratic Forms*, Ch. 9, Thm. 1.1, p. 128, and Lemma 4.1, Cor. 1, p. 139);
- `finite_aut`: each $O(V) \cap \alpha K_\mathbb{A}\alpha^{-1} = \mathrm{Aut}(\alpha L)$ is finite (true for
  positive definite $Q$: $\mathrm{Aut}(L)$ permutes the finitely many vectors of bounded length;
  the notes, p. 64: "the finite group of rational automorphisms $\mathrm{Aut}(L_i)$").

Positive definiteness of $Q$ enters only through `finite_classes` and `finite_aut` (and the
convergence of $\Theta_L$, which is not needed). -/
structure AWSInputs (Q : QuadForm ℚ n) : Prop where
  gluing : LatticeGluing n
  finite_classes : Finite (DoubleCoset.Quotient (ratPoints Q.hessian : Set (OA Q.hessian)) (KA Q.hessian))
  finite_aut : ∀ α : OA Q.hessian, Finite (ratPoints Q.hessian ⊓ conjSub α (KA Q.hessian) : Subgroup _)

/-- **D23: (4.4)–(4.34), pp. 63–66.** Let $\alpha_i$ ($i \in I$) be representatives of the double
cosets $O(V)\alpha_iK_\mathbb{A}$ with trivial archimedean component, $L_i = \alpha_i\mathbb{Z}^n$ the
corresponding classes in the genus. Relative to the inputs,
$$\Theta(\Phi_{L_j})(g_{\infty,z}) = \int_{O(V)\backslash O(V_\mathbb{A})} \Phi_{L_j}(h)\,\theta(g_{\infty,z},h)\,dh
= \frac{1}{|\mathrm{Aut}(L_j)|}\,y^{n/4}\,\Theta_{L_j}(z).$$ -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.34), pp. 63-66"]
theorem thetaLift_indicator_eq [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)]
    {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    inp.I (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        (((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
          thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z) := by
  have hleft := inp.left_invariant
  set c : ℂ := ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) * thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z
    with hc
  have hθ : ∀ γ ∈ ratPoints Q.hessian, ∀ g, thetaKernel Q z (γ * g) = thetaKernel Q z g := by
    rintro _ ⟨γ, rfl⟩ g
    exact thetaKernel_left_inv Q z γ g
  have hconst : ∀ k ∈ KA Q.hessian, thetaKernel Q z (α j * k) = c := by
    intro k hk
    rw [thetaKernel_mul_mem Q I.gluing z (α j) (hα j) hk, hc, thetaSeries, ← tsum_mul_left]
    congr 1; funext v
    split_ifs <;> simp
  have hfin := fun i => I.finite_aut (α i)
  have hint : ∀ i, IntegrableOn (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h)
      (α i • (KA Q.hessian : Set (OA Q.hessian))) μ := by
    intro i
    have hμ : μ (α i • (KA Q.hessian : Set (OA Q.hessian))) ≠ ⊤ := by
      rw [measure_smul, inp.measure_K]; exact ENNReal.one_ne_top
    refine IntegrableOn.congr_fun (integrableOn_const (C := if i = j then c else 0) hμ) ?_
      (inp.measurableSet_K.const_smul _)
    rintro _ ⟨k, hk, rfl⟩
    simp only [smul_eq_mul, dosetIndicator]
    by_cases hij : i = j
    · subst hij
      rw [Set.indicator_of_mem ((mem_doset_mul_iff (ratPoints Q.hessian) (KA Q.hessian) α hdisj hk i i).mpr rfl), Pi.one_apply,
        one_mul, hconst k hk, if_pos rfl]
    · rw [Set.indicator_of_notMem (fun hm => hij ((mem_doset_mul_iff (ratPoints Q.hessian) (KA Q.hessian) α hdisj hk i j).mp hm)),
        zero_mul, if_neg hij]
  rw [integral_indicator_mul inp α hcov hdisj hfin j _ hθ hint,
    setIntegral_congr_fun inp.measurableSet_K (fun k hk => hconst k hk), setIntegral_const,
    Measure.real, inp.measure_K, card_aut_eq Q.hessian I.gluing (α j)]
  simp

/-- **D23, (4.35)–(4.37), p. 66: the classical form.** With $k = n/2$ and trivial character,
$f(z) := (c\,i + d)^k\,\Theta(\Phi_{L_j})(g_{\infty,z}) = y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z})$
($c = 0$, $d = y^{-1/2}$ for $g_{\infty,z}$, see `gInf_denom`) is the weighted theta series:
$$y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,\Theta_{L_j}(z).$$

*Clarification (candidate; pending author):* (4.35) writes the factor as $\chi(d)(cz+d)^k$; by (4.2)
it is the automorphy factor at the base point, $(c\,i+d)^k$ (the same here, since $c = 0$). -/
@[kb "hanke2011aws" "§4.6, (4.35)-(4.37), p. 66"]
theorem thetaLift_classical [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)]
    {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      inp.I (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z := by
  have hyy : ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add z.im_pos]
    simp [neg_div]
  rw [thetaLift_indicator_eq Q inp I α hα hcov hdisj j z]
  linear_combination ((Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
    thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z) * hyy

/-- **Representatives with trivial archimedean component exist** (p. 63: "to simplify our lives we
choose the $\alpha_{i,\mathbb{A}}$ to have trivial archimedean components"): every double coset
$O(V)\,g\,K_\mathbb{A}$ contains $g\,(g_\infty^{-1}, 1)$, whose archimedean component is $1$. -/
@[kb "hanke2011aws" "§4.6, p. 63"]
theorem exists_rep_infty_one (H : Matrix (Fin n) (Fin n) ℚ) (g : OA H) :
    ∃ a : OA H, a.1 = 1 ∧ DoubleCoset.mk (ratPoints H) (KA H) a = DoubleCoset.mk (ratPoints H) (KA H) g := by
  refine ⟨g * (g.1⁻¹, 1), by simp, ?_⟩
  rw [DoubleCoset.eq]
  refine ⟨1, (ratPoints H).one_mem, (g.1⁻¹, 1)⁻¹, (KA H).inv_mem fun p => (intStab H p).one_mem, ?_⟩
  group

/-- **D24 (with D23): the theta lift of the constant function $1$** is the mass-weighted genus theta
series (p. 62, "the constant function $1$ … play[s] a special role"):
$$y^{-n/4}\int_{O(V)\backslash O(V_\mathbb{A})}\theta(g_{\infty,z},h)\,dh
= \sum_{j \in I}\frac{\Theta_{L_j}(z)}{|\mathrm{Aut}(L_j)|}.$$
(At $z \to i\infty$ the constant terms give $\sum_j 1/|\mathrm{Aut}(L_j)| = \mathrm{Mass}(L)$,
`integral_one_eq_mass`.) -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem thetaLift_one [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)]
    {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ) (I : AWSInputs Q)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * inp.I (thetaKernel Q z) =
      ∑ j, (Nat.card (autLat Q.hessian (latSMul Q.hessian I.gluing (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian I.gluing (α j) stdLat) z := by
  have hleft := inp.left_invariant
  have hθ : ∀ γ ∈ ratPoints Q.hessian, ∀ g, thetaKernel Q z (γ * g) = thetaKernel Q z g := by
    rintro _ ⟨γ, rfl⟩ g
    exact thetaKernel_left_inv Q z γ g
  have hfin := fun i => I.finite_aut (α i)
  -- integrability: θ is constant on each α_i K
  have hconst : ∀ i, ∀ k ∈ KA Q.hessian, thetaKernel Q z (α i * k) = thetaKernel Q z (α i) := by
    intro i k hk
    rw [thetaKernel_mul_mem Q I.gluing z (α i) (hα i) hk]
    conv_rhs => rw [← mul_one (α i)]
    rw [thetaKernel_mul_mem Q I.gluing z (α i) (hα i) (KA Q.hessian).one_mem]
  have hμ : ∀ i, μ (α i • (KA Q.hessian : Set (OA Q.hessian))) ≠ ⊤ := fun i => by
    rw [measure_smul, inp.measure_K]; exact ENNReal.one_ne_top
  have hint : ∀ i, IntegrableOn (thetaKernel Q z) (α i • (KA Q.hessian : Set (OA Q.hessian))) μ := by
    intro i
    refine IntegrableOn.congr_fun (integrableOn_const (C := thetaKernel Q z (α i)) (hμ i)) ?_
      (inp.measurableSet_K.const_smul _)
    rintro _ ⟨k, hk, rfl⟩
    exact (hconst i k hk).symm
  have hint' : ∀ i j, IntegrableOn (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h)
      (α i • (KA Q.hessian : Set (OA Q.hessian))) μ := by
    intro i j
    refine IntegrableOn.congr_fun
      (integrableOn_const (C := if i = j then thetaKernel Q z (α i) else 0) (hμ i)) ?_
      (inp.measurableSet_K.const_smul _)
    rintro _ ⟨k, hk, rfl⟩
    simp only [smul_eq_mul, dosetIndicator]
    by_cases hij : i = j
    · subst hij
      rw [Set.indicator_of_mem ((mem_doset_mul_iff (ratPoints Q.hessian) (KA Q.hessian) α hdisj hk i i).mpr rfl), Pi.one_apply,
        one_mul, hconst i k hk, if_pos rfl]
    · rw [Set.indicator_of_notMem (fun hm => hij ((mem_doset_mul_iff (ratPoints Q.hessian) (KA Q.hessian) α hdisj hk i j).mp hm)),
        zero_mul, if_neg hij]
  rw [integral_eq_sum_integral_indicator_mul inp α hcov hdisj hfin _ hθ hint hint', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => thetaLift_classical Q inp I α hα hcov hdisj j z

/-! ### (4.23): reduction to the archimedean component -/

/-- **D21: (4.23), p. 65.** Let $S$ ($= \mathrm{SL}_2(\mathbb{A})$) be a group with subgroups
$S_\mathbb{Q}$ ($= \mathrm{SL}_2(\mathbb{Q})$), $U_\infty$ ($= \mathrm{SL}_2(\mathbb{R})$) and $K_f$
($= \prod_p \mathrm{SL}_2(\mathbb{Z}_p)$), and let $\theta : S \times O(V_\mathbb{A}) \to \mathbb{C}$. Assume

- `hSA` (*strong approximation* for $\mathrm{SL}_2$, p. 65): $S = S_\mathbb{Q}\,U_\infty\,K_f$;
- `hleft` (the $\mathrm{Sp}(W)$-half of Lemma 4.4.1; Poisson summation):
  $\theta(\gamma g, h) = \theta(g, h)$ for $\gamma \in S_\mathbb{Q}$;
- `hright` ("each component $g_p$ acts trivially on the characteristic function $\varphi_p$"):
  $\theta(gk, h) = \theta(g, h)$ for $k \in K_f$.

Then for any functional $I$ and any $\Phi$, the lift $\Theta(g) = I(h \mapsto \Phi(h)\theta(g,h))$
satisfies $\Theta(g) = \Theta(u)$ for some $u \in U_\infty$: it "depend[s] only on the archimedean
component $g_\infty$ of $g_\mathbb{A}$".

*Update (candidate; pending author):* `hright` holds for $g_p \in \mathrm{SL}_2(\mathbb{Z}_p)$ only when
$L_p$ is self-dual for the pairing $H(\vec v, \vec w)$ used in the Fourier transform (formula 3 sends
$\mathbf 1_{L_p}$ to $\mathrm{vol}(L_p)\mathbf 1_{L_p^\#}$); for a lattice of level $N$ it holds for
$p \nmid N$, while at $p \mid N$ only $g_p \in K_p(N)$ act, and by the character
$\chi_p(d_p)$ (this is where the nebentypus of $\Theta_L$ comes from). The theorem is stated with $K_f$
arbitrary, so it applies with $K_f = \prod_p K_p(N)$ once the character is trivial. Also, for $n$ odd
the Weil representation is a representation of the metaplectic cover, not of $\mathrm{SL}_2(\mathbb{A})$
(the notes' $\chi_V$ uses $(-1)^{n/2}$, so they implicitly assume $n$ even). -/
@[kb "hanke2011aws" "§4.6, (4.23), p. 65"]
theorem thetaLift_depends_only_on_infty {S G : Type*} [Group S] (SQ Uinf Kf : Subgroup S)
    (hSA : ∀ g : S, ∃ γ ∈ SQ, ∃ u ∈ Uinf, ∃ k ∈ Kf, g = γ * u * k)
    (θ : S → G → ℂ) (hleft : ∀ γ ∈ SQ, ∀ g h, θ (γ * g) h = θ g h)
    (hright : ∀ k ∈ Kf, ∀ g h, θ (g * k) h = θ g h) (I : (G → ℂ) → ℂ) (Φ : G → ℂ) (g : S) :
    ∃ u ∈ Uinf, I (fun h => Φ h * θ g h) = I (fun h => Φ h * θ u h) := by
  obtain ⟨γ, hγ, u, hu, k, hk, rfl⟩ := hSA g
  refine ⟨u, hu, ?_⟩
  congr 1; funext h
  rw [hright k hk, hleft γ hγ]

/-! ### The archimedean element $g_{\infty,z}$ -/

/-- **$g_{\infty,z} = \begin{pmatrix}1&x\\0&1\end{pmatrix}\begin{pmatrix}\sqrt y&0\\0&\sqrt y^{-1}\end{pmatrix}
= \begin{pmatrix}\sqrt y& x/\sqrt y\\0&1/\sqrt y\end{pmatrix}$** (p. 65), $z = x + iy$. -/
noncomputable def gInf (z : ℍ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![Real.sqrt z.im, z.re / Real.sqrt z.im; 0, 1 / Real.sqrt z.im], by
    have h := Real.sqrt_pos.mpr z.im_pos
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- **$g_{\infty,z}\cdot i = z$** (p. 65: "the elements $g_{\infty,z}$ satisfy $g_{\infty,z}\cdot i = x + iy$"). -/
@[kb "hanke2011aws" "§4.6, p. 65"]
theorem gInf_smul_I (z : ℍ) : gInf z • UpperHalfPlane.I = z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.specialLinearGroup_apply]
  have h := Real.sqrt_pos.mpr z.im_pos
  have hs : (Real.sqrt z.im : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [gInf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    UpperHalfPlane.coe_I, Algebra.algebraMap_self, RingHom.id_apply]
  rw [show (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I from (re_add_im (z : ℂ)).symm]
  have hsq : ((Real.sqrt z.im : ℝ) : ℂ) ^ 2 = (z.im : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt z.im_pos.le]
  push_cast
  rw [zero_mul, zero_add]
  field_simp
  linear_combination Complex.I * hsq

/-- **The automorphy factor at $g_{\infty,z}$** ((4.35)–(4.36), p. 66): $c = 0$ and $d = y^{-1/2}$,
so $(c\,i + d)^{n/2} = y^{-n/4}$. -/
@[kb "hanke2011aws" "§4.6, (4.35)-(4.36), p. 66"]
theorem gInf_denom (z : ℍ) :
    (gInf z : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧
      ((gInf z : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ ((n : ℝ) / 2) = z.im ^ (-(n : ℝ) / 4) := by
  refine ⟨by simp [gInf], ?_⟩
  simp only [gInf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  rw [one_div, Real.inv_rpow (Real.sqrt_nonneg _), sqrt_rpow _ z.im_pos.le,
    ← Real.rpow_neg z.im_pos.le, neg_div]

end QuadFormsKB.AWS
