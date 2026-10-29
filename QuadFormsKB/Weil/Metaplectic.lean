/-
# The Weil relation in arbitrary dimension and the metaplectic multiplier (odd $n$ included)

**Layer:** an abstract one-variable model `LocalData.IsModel` (every place of a number field: `isModel_V`,
`isModel_inf`), genus one, a diagonal quadratic space $V = \langle a_0, \dots, a_{n-1}\rangle$ of **any** dimension $n$
($a : $ `Fin n → Kˣ`; `Weil/Model.lean` treats only even $n = 2m$).

**Operators** (on functions on $K^n$; no character and no Weil index):
$$N_b\Phi(x) = \psi(bQ(x))\Phi(x),\qquad M_t\Phi(x) = |t|^{n/2}\Phi(tx),\qquad
  W\Phi(y) = \int_{K^n}\Phi(x)\psi(B(x,y))\,d\mu_B(x)$$
(`opNo`, `opMo`, `opWo`; $d\mu_B = \prod_i|2a_i|^{1/2}d\mu(x_i)$ is the self-dual measure).

**Results.** On every pure tensor $\Phi = \bigotimes_if_i$ of test functions $f_i \in S$ (these span $S(V)$):
* (R4), (R5) hold exactly: $WM_t = M_{t^{-1}}W$ (`opWo_opMo`), $W^2 = M_{-1}$ (`opWo_opWo`);
* (R6) holds **up to the multiplier** $\mu_V(b) = \prod_{i<n}g(a_ib)$ (`metaMult`, $g$ = `gN` the normalized Weil
  constant): $WN_bW = \mu_V(b)\,N_{-b^{-1}}M_{-b^{-1}}WN_{-b^{-1}}$ (`opWo_opNo_opWo`).
* **The metaplectic multiplier.** The normalized ratio $\nu_V(b) = \mu_V(b)/\mu_V(1)$ (`metaNu`) satisfies
  $$\nu_V(b) = (\textstyle\prod_ia_i,\, b)\,\lambda(b)^n,\qquad \lambda(b) = g(b)/g(1),\qquad
    \lambda(st) = (s,t)\,\lambda(s)\lambda(t)$$
  (`metaNu_eq`, `weilRatio_mul`), hence $\nu_V(st) = (s,t)^n\,\nu_V(s)\nu_V(t)$ (`metaNu_mul`): the Hilbert symbol
  $(s,t)$ is the $2$-cocycle of $\nu_V$, to the power $n$.
* **Even $n = 2m$:** $\nu_V(b) = (\prod_ia_i, b)(b,-1)^m$ is a quadratic character (`metaNu_even`); this is $\chi_V$ of
  `Weil/Model.lean`, which is why there a character in $\omega(m(t))$ and the constant $\gamma_V$ make (R6) exact.
* **Odd $n$, the obstruction** (`metaNu_not_multiplicative`): if $(s,t) = -1$ for some units $s, t$ (true at every
  real and every finite place of a number field, e.g. $s = t = -1$ at a real place; false at complex places), then $\nu_V$ is not multiplicative, so no rescaling
  of $M_t$ by a character absorbs the multiplier: the operators define only a projective representation of
  $\mathrm{SL}_2$, a genuine representation of the metaplectic double cover.
* **The Kubota cocycle** (`kubotaCocycle`): $\sigma(\gamma_1, \gamma_2) = (x(\gamma_1), x(\gamma_2))\,
  (-x(\gamma_1)x(\gamma_2), x(\gamma_1\gamma_2))$, $x\begin{pmatrix}a&b\\c&d\end{pmatrix} = c$ if $c \ne 0$, else $d$.
  On the diagonal torus $\sigma(m(s), m(t)) = (s, t)$ (`kubotaCocycle_diag`), the cocycle of $\nu_V$ for odd $n$.

**Not proved** (left as the statement above): that $\omega$, normalized by the metaplectic constants, satisfies
$\omega(\gamma_1)\omega(\gamma_2) = \sigma(\gamma_1,\gamma_2)\,\omega(\gamma_1\gamma_2)$ on all of $\mathrm{SL}_2(K)$
(Kubota 1969; Rao 1993 for $\mathrm{Sp}_{2g}$).

Sources: Weil, Acta Math. 111 (1964), §§14, 43 [unverified]; Kubota, *On automorphic functions and the reciprocity
law in a number field* (1969), §2 [unverified]; Rao, Pacific J. Math. 157 (1993), §5 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Model

open MeasureTheory

noncomputable section

namespace QuadFormsKB.WeilRep

namespace LocalData

variable {K : Type*} [CommRing K] [MeasurableSpace K] (D : LocalData K) {n : ℕ} (a : Fin n → Kˣ)

/-- **$N_b$ in dimension $n$:** $\Phi(x) \mapsto \psi(bQ(x))\Phi(x)$. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(n(b))$) [unverified]"]
def opNo (b : K) (Φ : (Fin n → K) → ℂ) (x : Fin n → K) : ℂ :=
  (D.ψ (b * Qform a x) : ℂ) * Φ x

/-- **$M_t$ in dimension $n$:** $\Phi(x) \mapsto |t|^{n/2}\Phi(tx)$ (no character). -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(m(a))$ without $\\chi_V$) [unverified]"]
def opMo (t : K) (Φ : (Fin n → K) → ℂ) (x : Fin n → K) : ℂ :=
  (Real.sqrt (D.md t) : ℂ) ^ n * Φ (fun i => t * x i)

/-- **$W$ in dimension $n$:** $\Phi \mapsto \hat\Phi$, $\hat\Phi(y) = \int\Phi(x)\psi(B(x,y))\,d\mu_B(x)$ (no Weil index). -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(w)$ without $\\gamma_V$) [unverified]"]
def opWo (Φ : (Fin n → K) → ℂ) (y : Fin n → K) : ℂ :=
  (∏ i, (Real.sqrt (D.md (2 * (a i : K))) : ℂ)) * ∫ x, Φ x * (D.ψ (Bform a x y) : ℂ) ∂D.muN n

/-- **The multiplier of the Weil relation in dimension $n$:** $\mu_V(b) = \prod_{i<n}g(a_ib)$. -/
@[kb "weil1964" "§14, Thm. 2 and §43 (the constant in the Weil relation; metaplectic for odd $\\dim V$) [unverified]"]
def metaMult (b : K) : ℂ := ∏ i, D.gN ((a i : K) * b)

/-- **The normalized multiplier** $\nu_V(b) = \mu_V(b)/\mu_V(1)$. -/
@[kb "weil1964" "§43 (the metaplectic multiplier) [unverified]"]
def metaNu (b : K) : ℂ := D.metaMult a b / D.metaMult a 1

/-- **The ratio of Weil constants** $\lambda(b) = g(b)/g(1)$. -/
@[kb "weil1964" "§26 (the Weil index of $bx^2$ relative to $x^2$) [unverified]"]
def weilRatio (b : K) : ℂ := D.gN b / D.gN 1

variable {D a}

lemma psi_Qform_n (b : K) (x : Fin n → K) :
    (D.ψ (b * Qform a x) : ℂ) = ∏ i, (D.ψ (b * (a i : K) * x i ^ 2) : ℂ) := by
  rw [Qform, Finset.mul_sum, addChar_sum, coe_prod_circle]
  simp only [mul_assoc]

lemma psi_Bform_n (x y : Fin n → K) :
    (D.ψ (Bform a x y) : ℂ) = ∏ i, (D.ψ (x i * (2 * (a i : K) * y i)) : ℂ) := by
  rw [Bform, addChar_sum, coe_prod_circle]
  congr 1; ext i; congr 2; ring

lemma opNo_ptensor (b : K) (f : Fin n → K → ℂ) :
    D.opNo a b (ptensor f) = ptensor (fun i => D.chirp (b * a i) (f i)) := by
  ext x; simp only [opNo, ptensor, chirp, psi_Qform_n, ← Finset.prod_mul_distrib]

lemma opMo_ptensor (t : K) (f : Fin n → K → ℂ) :
    D.opMo t (ptensor f) = ((Real.sqrt (D.md t) : ℂ) ^ n) • ptensor (fun i => dil t (f i)) := by
  ext x; simp only [opMo, ptensor, dil, Pi.smul_apply, smul_eq_mul]

lemma opWo_ptensor [SigmaFinite D.μ] (f : Fin n → K → ℂ) :
    D.opWo a (ptensor f) = ptensor (fun i => D.Fa (a i) (f i)) := by
  ext y
  simp only [opWo, ptensor, psi_Bform_n, ← Finset.prod_mul_distrib, muN]
  rw [integral_fintype_prod_eq_prod (fun i x => f i x * (D.ψ (x * (2 * (a i : K) * y i)) : ℂ)),
    ← Finset.prod_mul_distrib]
  rfl

lemma opNo_smul (b : K) (c : ℂ) (Φ : (Fin n → K) → ℂ) : D.opNo a b (c • Φ) = c • D.opNo a b Φ := by
  ext x; simp only [opNo, Pi.smul_apply, smul_eq_mul]; ring

lemma opMo_smul (t : K) (c : ℂ) (Φ : (Fin n → K) → ℂ) : D.opMo t (c • Φ) = c • D.opMo t Φ := by
  ext x; simp only [opMo, Pi.smul_apply, smul_eq_mul]; ring

lemma opWo_smul (c : ℂ) (Φ : (Fin n → K) → ℂ) : D.opWo a (c • Φ) = c • D.opWo a Φ := by
  ext y; simp only [opWo, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]; ring

section Relations

variable (hD : D.IsModel)
include hD

/-- **(R4) in dimension $n$:** $WM_t\Phi = M_{t^{-1}}W\Phi$ for every pure tensor $\Phi$ of test functions. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (the relation $w\\,m(a) = m(a^{-1})\\,w$) [unverified]"]
theorem opWo_opMo (t : Kˣ) {f : Fin n → K → ℂ} (hf : ∀ i, f i ∈ D.S) :
    D.opWo a (D.opMo t (ptensor f)) = D.opMo (↑t⁻¹ : K) (D.opWo a (ptensor f)) := by
  have := hD.sigmaFinite
  rw [opMo_ptensor, opWo_smul, opWo_ptensor, opWo_ptensor, opMo_ptensor]
  have hF : (fun i => D.Fa (a i) (dil (t : K) (f i))) =
      fun i => ((D.md t : ℂ)⁻¹) • dil (↑t⁻¹ : K) (D.Fa (a i) (f i)) :=
    funext fun i => Fa_dil hD (hf i) (a i) t
  rw [hF, ptensor_smul_fun, smul_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have hp := hD.md_pos t
  have hs : (Real.sqrt (D.md t) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  have hs2 : (Real.sqrt (D.md t) : ℂ) ^ 2 = D.md t := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hp.le]
  rw [md_inv hD, Real.sqrt_inv, Complex.ofReal_inv, ← hs2, inv_pow, ← pow_mul, pow_mul', sq]
  have hn : (Real.sqrt (D.md t) : ℂ) ^ n ≠ 0 := pow_ne_zero _ hs
  field_simp
  rw [← mul_pow, mul_one_div_cancel hs, one_pow]

/-- **(R5) in dimension $n$:** $W^2\Phi = M_{-1}\Phi$ for every pure tensor $\Phi$ of test functions. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (the relation $w^2 = m(-1)$) [unverified]"]
theorem opWo_opWo {f : Fin n → K → ℂ} (hf : ∀ i, f i ∈ D.S) :
    D.opWo a (D.opWo a (ptensor f)) = D.opMo (-1 : K) (ptensor f) := by
  have := hD.sigmaFinite
  rw [opWo_ptensor, opWo_ptensor, opMo_ptensor]
  have hF : (fun i => D.Fa (a i) (D.Fa (a i) (f i))) = fun i => dil (-1 : K) (f i) :=
    funext fun i => Fa_Fa hD (hf i) (a i)
  rw [hF, md_neg_one hD]
  simp

/-- **(R6) in dimension $n$, with the multiplier $\mu_V$:** for every unit $b$ and every pure tensor $\Phi$ of test
functions, $WN_bW\Phi = \mu_V(b)\,N_{-b^{-1}}M_{-b^{-1}}WN_{-b^{-1}}\Phi$, $\mu_V(b) = \prod_ig(a_ib)$ (`metaMult`). -/
@[kb "weil1964" "§14, Thm. 2 (the relation for $w\\,n(b)\\,w$ up to the constant) [unverified]"]
theorem opWo_opNo_opWo (b : Kˣ) {f : Fin n → K → ℂ} (hf : ∀ i, f i ∈ D.S) :
    D.opWo a (D.opNo a b (D.opWo a (ptensor f))) =
      D.metaMult a b • D.opNo a (-(↑b⁻¹ : K)) (D.opMo ((-b⁻¹ : Kˣ) : K)
        (D.opWo a (D.opNo a (-(↑b⁻¹ : K)) (ptensor f)))) := by
  have := hD.sigmaFinite
  rw [opWo_ptensor, opNo_ptensor, opWo_ptensor, opNo_ptensor, opWo_ptensor, opMo_ptensor, opNo_smul,
    opNo_ptensor, smul_smul]
  have hF : (fun i => D.Fa (a i) (D.chirp ((b : K) * a i) (D.Fa (a i) (f i)))) =
      fun i => (D.gN ((a i : K) * b) * ((Real.sqrt (D.md b) : ℂ))⁻¹) •
        D.chirp (-(↑b⁻¹ : K) * a i) (dil ((-b⁻¹ : Kˣ) : K)
          (D.Fa (a i) (D.chirp (-(↑b⁻¹ : K) * a i) (f i)))) := by
    funext i
    rw [mul_comm (b : K), Fa_chirp_Fa hD (hf i) (a i) b]
    congr 2 <;> simp [mul_comm]
  rw [hF, ptensor_smul_fun]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, metaMult]
  congr 1
  rw [Units.val_neg, md_neg hD, md_inv hD, Real.sqrt_inv, Complex.ofReal_inv, inv_pow]

/-! ### The multiplier -/

/-- $\lambda(st) = (s,t)\lambda(s)\lambda(t)$: the Hilbert symbol is the $2$-cocycle of $\lambda = g/g(1)$. -/
@[kb "weil1964" "§28, Prop. 4 ($\\gamma(st)\\gamma(1) = (s,t)\\gamma(s)\\gamma(t)$) [unverified]"]
theorem weilRatio_mul (s t : Kˣ) :
    D.weilRatio ((s : K) * t) = D.hC s t * D.weilRatio s * D.weilRatio t := by
  have h := gN_mul hD s t
  have h1 : D.gN ((1 : Kˣ) : K) ≠ 0 := gN_ne_zero hD 1
  simp only [Units.val_one] at h1
  unfold weilRatio
  field_simp
  linear_combination h

lemma metaMult_one_ne_zero : D.metaMult a 1 ≠ 0 := by
  unfold metaMult
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [mul_one]; exact gN_ne_zero hD (a i)

lemma weilRatio_ne_zero (b : Kˣ) : D.weilRatio b ≠ 0 := by
  have h1 : D.gN ((1 : Kˣ) : K) ≠ 0 := gN_ne_zero hD 1
  simp only [Units.val_one] at h1
  exact div_ne_zero (gN_ne_zero hD b) h1

/-- **The multiplier through the Weil ratio:** $\nu_V(b) = (\prod_ia_i, b)\,\lambda(b)^n$. -/
@[kb "weil1964" "§43 (the metaplectic multiplier) [unverified]"]
theorem metaNu_eq (b : Kˣ) :
    D.metaNu a b = D.hC ((∏ i, a i : Kˣ) : K) b * D.weilRatio b ^ n := by
  have hrat : ∀ i, D.gN ((a i : K) * b) = D.gN ((a i : K) * 1) * (D.hC (a i) b * D.weilRatio b) := by
    intro i
    have h := weilRatio_mul hD (a i) b
    have h1 : D.gN ((1 : Kˣ) : K) ≠ 0 := gN_ne_zero hD 1
    simp only [Units.val_one] at h1
    unfold weilRatio at h ⊢
    rw [mul_one]
    field_simp at h ⊢
    linear_combination h
  have hne := metaMult_one_ne_zero hD (a := a)
  unfold metaNu
  rw [div_eq_iff hne, hC_prod_left hD]
  unfold metaMult
  rw [Finset.prod_congr rfl fun i _ => hrat i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The cocycle of the multiplier:** $\nu_V(st) = (s,t)^n\,\nu_V(s)\nu_V(t)$. -/
@[kb "weil1964" "§43 (the metaplectic multiplier; its cocycle is the Hilbert symbol) [unverified]"]
theorem metaNu_mul (s t : Kˣ) :
    D.metaNu a ((s : K) * t) = D.hC s t ^ n * D.metaNu a s * D.metaNu a t := by
  rw [show ((s : K) * t) = ((s * t : Kˣ) : K) by simp, metaNu_eq hD, metaNu_eq hD, metaNu_eq hD,
    Units.val_mul, hC_mul_right hD, weilRatio_mul hD, mul_pow, mul_pow]
  ring

/-- **Even dimension $n = 2m$:** $\nu_V(b) = (\prod_ia_i, b)(b, -1)^m$, a quadratic character of $b$. -/
@[kb "weil1964" "§43 (for even $\\dim V$ the multiplier is a character) [unverified]"]
theorem metaNu_even {m : ℕ} (a : Fin (2 * m) → Kˣ) (b : Kˣ) :
    D.metaNu a b = D.hC ((∏ i, a i : Kˣ) : K) b * D.hC b (-1) ^ m := by
  rw [metaNu_eq hD, pow_mul]
  congr 1
  have h := gN_sq hD b
  have h1 : D.gN ((1 : Kˣ) : K) ≠ 0 := gN_ne_zero hD 1
  simp only [Units.val_one] at h1
  have : D.weilRatio b ^ 2 = D.hC b (-1) := by
    unfold weilRatio; field_simp; linear_combination h
  rw [this]

/-- **Odd dimension: the multiplier is not a character.** If $n$ is odd and $(s,t) = -1$ for some units $s, t$, then
$\nu_V(st) \ne \nu_V(s)\nu_V(t)$; so (R6) cannot be made exact by rescaling $M_t$ by a character: the Weil
representation of an odd-dimensional $V$ lives on the metaplectic cover. -/
@[kb "weil1964" "§43 (for odd $\\dim V$ the Weil representation is genuinely metaplectic) [unverified]"]
theorem metaNu_not_multiplicative (hn : Odd n) {s t : Kˣ} (hst : D.hilb s t = -1) :
    D.metaNu a ((s : K) * t) ≠ D.metaNu a s * D.metaNu a t := by
  rw [metaNu_mul hD]
  have hc : D.hC s t = -1 := by simp [hC, hst]
  rw [hc, hn.neg_one_pow]
  have h1 : D.metaNu a s ≠ 0 := by
    rw [metaNu_eq hD]
    refine mul_ne_zero ?_ (pow_ne_zero _ (weilRatio_ne_zero hD s))
    intro h0
    have := hC_sq hD (∏ i, a i) s
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h2 : D.metaNu a t ≠ 0 := by
    rw [metaNu_eq hD]
    refine mul_ne_zero ?_ (pow_ne_zero _ (weilRatio_ne_zero hD t))
    intro h0
    have := hC_sq hD (∏ i, a i) t
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  intro h
  have : (2 : ℂ) * (D.metaNu a s * D.metaNu a t) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h0 | h0
  · norm_num at h0
  · exact mul_ne_zero h1 h2 h0

end Relations

end LocalData

/-! ### The Kubota cocycle on $\mathrm{SL}_2$ -/

section Kubota

variable {K : Type*} [Field K]

open Classical in
/-- Kubota's function $x\begin{pmatrix}a&b\\c&d\end{pmatrix} = c$ if $c \ne 0$, else $d$. -/
def kubotaX (γ : Matrix.SpecialLinearGroup (Fin 2) K) : K :=
  if (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 then (γ : Matrix (Fin 2) (Fin 2) K) 1 0
  else (γ : Matrix (Fin 2) (Fin 2) K) 1 1

/-- **The Kubota cocycle** of $\mathrm{SL}_2(K)$ for a symbol `hilb` (the Hilbert symbol):
$\sigma(\gamma_1,\gamma_2) = (x(\gamma_1), x(\gamma_2))\,(-x(\gamma_1)x(\gamma_2), x(\gamma_1\gamma_2))$. -/
@[kb "kubota1969" "§2 (the cocycle $\\sigma(\\gamma_1, \\gamma_2)$ of the metaplectic cover of $\\mathrm{SL}_2$) [unverified]"]
def kubotaCocycle (hilb : K → K → ℤ) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) K) : ℤ :=
  hilb (kubotaX γ₁) (kubotaX γ₂) * hilb (-(kubotaX γ₁ * kubotaX γ₂)) (kubotaX (γ₁ * γ₂))

/-- The diagonal element $m(s) = \operatorname{diag}(s, s^{-1})$ of $\mathrm{SL}_2(K)$. -/
def kubotaDiag (s : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

lemma kubotaX_diag (s : Kˣ) : kubotaX (kubotaDiag s) = ((s⁻¹ : Kˣ) : K) := by
  simp [kubotaX, kubotaDiag]

lemma kubotaDiag_mul (s t : Kˣ) : kubotaDiag s * kubotaDiag t = kubotaDiag (s * t) := by
  apply Subtype.ext
  show !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] =
    !![((s * t : Kˣ) : K), 0; 0, (((s * t)⁻¹ : Kˣ) : K)]
  simp [mul_comm]

/-- **The Kubota cocycle on the diagonal torus is the Hilbert symbol:** for a symbol that is multiplicative in each
variable, $\pm1$-valued and satisfies $(u, -u) = 1$ on units, $\sigma(m(s), m(t)) = (s, t)$. -/
@[kb "kubota1969" "§2 (the cocycle on the diagonal torus) [unverified]"]
theorem kubotaCocycle_diag (hilb : K → K → ℤ)
    (hpm : ∀ s t : Kˣ, hilb s t = 1 ∨ hilb s t = -1)
    (hmul : ∀ s s' t : Kˣ, hilb ((s : K) * s') t = hilb s t * hilb s' t)
    (hcomm : ∀ s t : Kˣ, hilb s t = hilb t s)
    (hneg : ∀ s : Kˣ, hilb s (-(s : K)) = 1) (s t : Kˣ) :
    kubotaCocycle hilb (kubotaDiag s) (kubotaDiag t) = hilb s t := by
  -- `(u⁻¹, v) = (u, v)` from multiplicativity and `(u, v)² = 1`
  have hsq : ∀ u v : Kˣ, hilb u v * hilb u v = 1 := fun u v => by
    rcases hpm u v with h | h <;> simp [h]
  have hinv : ∀ u v : Kˣ, hilb ((u⁻¹ : Kˣ) : K) v = hilb u v := fun u v => by
    have h := hmul u u⁻¹ v
    have h1 : hilb (1 : K) v = 1 := by
      have := hmul 1 1 v
      simp only [Units.val_one, mul_one] at this
      have h2 := hsq 1 v
      simp only [Units.val_one] at h2
      rw [h2] at this
      exact this
    simp only [Units.mul_inv] at h
    rw [h1] at h
    have h2 := hsq u v
    calc hilb ((u⁻¹ : Kˣ) : K) v = hilb u v * (hilb u v * hilb ((u⁻¹ : Kˣ) : K) v) := by
          rw [← mul_assoc, h2, one_mul]
      _ = hilb u v := by rw [← h, mul_one]
  rw [kubotaCocycle, kubotaDiag_mul, kubotaX_diag, kubotaX_diag, kubotaX_diag]
  have e : -(((s⁻¹ : Kˣ) : K) * ((t⁻¹ : Kˣ) : K)) = -(((s * t)⁻¹ : Kˣ) : K) := by
    simp [mul_comm]
  have hn' : ∀ u : Kˣ, hilb (-(u : K)) u = 1 := fun u => by
    have := hcomm (-u) u
    rw [Units.val_neg] at this
    rw [this]; exact hneg u
  rw [e, hn', mul_one, hinv, hcomm, hinv, hcomm]

end Kubota

end QuadFormsKB.WeilRep
