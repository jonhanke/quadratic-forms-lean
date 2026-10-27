/-
# Weil's spherical zeta functions and the spherical sum

**Layer:** local factors (finite and real places) and their Euler product; the global sum over $F^\times/F^{\times2}$.

**Setting** (as in `ZetaResidue.lean`). $F$ a number field, $Q$ = `QuadForm (𝓞 F) n` nondegenerate, $V = F^n$. Finite
places $v$: $F_v$ = `v.adicCompletion F`, $L_v = \mathcal O_v^n$ (`latL`), $Q_v = Q\otimes\mathcal O_v$ (`NF.Qp v Q`), $dx_v$ the
standard Haar measure on $F_v^n$ (`haarV`, $\operatorname{vol}(\mathcal O_v) = 1$), $q_v = N\mathfrak p_v$, $|\cdot|_v$ normalized.
Real places $w$ (`RealPlace F`): $Q_w = \sigma_w(Q)$ (`realVal`), Lebesgue measure on $\mathbb R^n$. Test function
$\Phi = \bigotimes_w\Phi_w\otimes\bigotimes_v\mathbf 1_{L_v}$. Real $s$ only. (For $F$ totally real the real places are all the
infinite places; complex places are absent, exactly as in `globalZeta`.)

**Weil's definitions** (A. Weil, *Adeles and Algebraic Groups*, 1982, §4.5, pp. 101–102). For $\rho \in F^\times$ let
$T(\rho) = \{(x,y) : F(x) = \rho y^2,\ y \ne 0\}$, with the gauge form $dx_0\cdots dx_{n-1}$ and Weil's convergence factors
$1 - q_v^{-1}$. The projection $(x,y) \mapsto x$ is two-to-one from $T(\rho)_{F_v}$ onto $\{x : Q(x) \in \rho F_v^{\times2}\}$ and
carries the gauge form to $dx_v$, so $\int_{T(\rho)_v}f(x)\,|dx| = 2\int_{Q(x)\in\rho F_v^{\times2}}f(x)\,dx_v$ (Weil uses this
on p. 107: "$T(\rho)$ ... covers twice the subset ... $F(x) \in \rho k_v^{*2}$"). Hence:

* `sphInt Q v ρ s` $= \int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|_v^s\,dx_v$;
* `sphLocal Q v ρ s` $= Z_\mathfrak p(s,\rho) = (1 - q_v^{-1})^{-1}\int_{T(\rho)_v}|F(x)|_v^s\Phi_v(x)(dx)_v
  = \dfrac{2\,\texttt{sphInt}}{1 - q_v^{-1}}$ (**Weil's (3), p. 102**);
* `sphArchAt Q w φ ρ s` $= \int_{T(\rho)_w}|F(x)|^s\varphi(x)\,dx = 2\int_{Q_w(x)\in\rho\mathbb R^{\times2}}|Q_w(x)|^s\varphi(x)\,dx$;
* `sphericalZetaAt Q Φ ρ s` $= Z(s,\rho) = |d_F|^{-n/2}\prod_w Z_w(s,\sigma_w\rho)\prod_v Z_\mathfrak p(s,\rho)$ (**Weil's (1),
  p. 102**, computed as the product of the local integrals; the factor $|d_F|^{-n/2}$ is the Tamagawa normalization of
  `globalZeta`);
* **`sphericalZeta Q Φ s`** $= Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho)$ (**Weil's (2), p. 102**), the sum over the
  representatives `Quotient.out` of the classes of $F^\times$ modulo $F^{\times2}$ (Weil: "a full set of representatives").

*Remark:* Weil's (2) is $Z(s) = \sum_\rho Z(s,\rho)$ **without** a factor
$\frac12$ (p. 102). With the factor $\frac12$ the residue would be $\frac12\rho_k\int\Phi$.

The comparison theorem (Weil's (4)–(8), pp. 106–108) is in `SphericalResidue.lean`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.ZetaResidue

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalZeta

open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.GlobalZeta QuadFormsKB.Siegel

open Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The square class** $\rho K^{\times2} = \{\rho y^2 : y \in K^\times\}$ of $\rho$ in a field $K$. -/
def sqClass {K : Type*} [Field K] (ρ : K) : Set K := {t | ∃ y : K, y ≠ 0 ∧ t = ρ * y ^ 2}

lemma mem_sqClass {K : Type*} [Field K] {ρ t : K} : t ∈ sqClass ρ ↔ ∃ y : K, y ≠ 0 ∧ t = ρ * y ^ 2 := Iff.rfl

/-- The square class only depends on $\rho$ modulo squares: $\rho\lambda^2K^{\times2} = \rho K^{\times2}$ for $\lambda \ne 0$. -/
lemma sqClass_mul_sq {K : Type*} [Field K] (ρ : K) {l : K} (h : l ≠ 0) : sqClass (ρ * l ^ 2) = sqClass ρ := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨l * y, mul_ne_zero h hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y / l, div_ne_zero hy h, ?_⟩
    field_simp

/-! ### Local factors at the finite places -/

/-- $q_v = |\mathcal O_v/\mathfrak p_v|$ as a real number. -/
local notation "qv" v => ((DVR.q (HeightOneSpectrum.adicCompletionIntegers F v) : ℕ) : ℝ)

/-- **The spherical local integral** at a finite place $v$, for $\rho \in F_v$:
$$\int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|_v^s\,dx_v,$$
$L_v = \mathcal O_v^n$, $dx_v$ the standard Haar measure (`haarV`, $\operatorname{vol}(\mathcal O_v) = 1$), $|\cdot|_v$ normalized. -/
def sphInt (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : v.adicCompletion F) (s : ℝ) : ℝ :=
  ∫ x in latL v n ∩ (NF.Qp v Q).evalIn (v.adicCompletion F) ⁻¹' sqClass ρ,
    ‖(NF.Qp v Q).evalIn (v.adicCompletion F) x‖ ^ s ∂(Measure.pi fun _ : Fin n => haarV v)

/-- **Weil's local spherical zeta function** (Weil 1982, §4.5, (3), p. 102): for $\rho \in F_v^\times$,
$$Z_\mathfrak p(s,\rho) = (1-q_v^{-1})^{-1}\int_{T(\rho)_{F_v}}|F(x)|_v^s\,\Phi_v(x)\,(dx)_v
  = \frac{2}{1 - q_v^{-1}}\int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|_v^s\,dx_v,$$
the factor $2$ because $T(\rho)_{F_v} \to \{Q(x)\in\rho F_v^{\times2}\}$, $(x,y)\mapsto x$, is two-to-one and carries the gauge form
$dx_0\cdots dx_{n-1}$ of $T(\rho)$ to $dx_v$ (Weil, p. 107). Here $\Phi_v = \mathbf 1_{L_v}$. -/
@[kb "weil1982" "§4.5, (3), p. 102 (Z_p(s,u))"]
def sphLocal (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : v.adicCompletion F) (s : ℝ) : ℝ :=
  2 * sphInt Q v ρ s / (1 - (qv v)⁻¹)

/-! ### Local factors at the real places -/

/-- **The spherical integral at a real place** $w$, for $\rho \in \mathbb R^\times$ (the image $\sigma_w(\rho)$):
$$Z_w(s,\rho) = \int_{T(\rho)_{\mathbb R}}|F(x)|^s\varphi(x)\,dx = 2\int_{Q_w(x)\in\rho\mathbb R^{\times2}}|Q_w(x)|^s\,\varphi(x)\,dx,$$
Lebesgue measure on $\mathbb R^n$; for $\rho > 0$ the domain is $\{Q_w > 0\}$, for $\rho < 0$ it is $\{Q_w < 0\}$. -/
@[kb "weil1982" "§4.5, (1), p. 102 (the factor at an infinite place)"]
def sphArchAt (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (φ : (Fin n → ℝ) → ℝ) (ρ : ℝ) (s : ℝ) : ℝ :=
  2 * ∫ x in realVal Q w ⁻¹' sqClass ρ, |realVal Q w x| ^ s * φ x

/-! ### The global spherical zeta functions -/

/-- **Weil's spherical zeta function** $Z(s,\rho)$ (Weil 1982, §4.5, (1), p. 102), for $\rho \in F^\times$:
$$Z(s,\rho) = \int_{T(\rho)_{\mathbb A}}|F(x)|^s\,\Phi(x)\,d'x
  = |d_F|^{-n/2}\prod_w Z_w(s,\sigma_w\rho)\prod_v Z_\mathfrak p(s,\rho),$$
$d'x$ the Tamagawa measure of $T(\rho)$ (gauge form $dx_0\cdots dx_{n-1}$, convergence factors $1-q_v^{-1}$, Lemma 4.5.1), computed
**multiplicatively**: defined as the product of the local integrals (`sphArchAt`, `sphLocal`; `tprod` over the finite places,
absolutely convergent for $n \ge 5$ and $s \ge 0$, see `SphericalResidue.lean`). $Z(s,\rho)$ depends only on $\rho$ modulo
$F^{\times2}$ (`sphericalZetaAt_mul_sq`); it vanishes when $Q$ does not represent $\rho$ everywhere locally. -/
@[kb "weil1982" "§4.5, (1), p. 102 (spherical zeta-function)"]
def sphericalZetaAt (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (ρ : F) (s : ℝ) : ℝ :=
  |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * (∏ w, sphArchAt Q w (Φ w) (realEmb w ρ) s) *
    ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q v (algebraMap F (v.adicCompletion F) ρ) s

/-- The square classes $F^\times/F^{\times2}$. -/
abbrev SqClasses (F : Type) [Field F] : Type := Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range

/-- **Weil's zeta function of the quadratic form** (Weil 1982, §4.5, (2), p. 102):
$$Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho),$$
the sum over a full set of representatives of $F^\times$ modulo $F^{\times2}$ (here `Quotient.out` of each class; the terms do
not depend on the choice, `sphericalZetaAt_mul_sq`). Real $s$; the terms are $\ge 0$ for $\Phi_w \ge 0$, and the series converges
for $s > 0$ (`SphericalResidue.lean`). **No factor $\frac12$** (Weil's (2) as printed). -/
@[kb "weil1982" "§4.5, (2), p. 102 (Z(s) = Σ_ρ Z(s,ρ))"]
def sphericalZeta (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∑' c : SqClasses F, sphericalZetaAt Q Φ ((Quotient.out c : Fˣ) : F) s

/-! ### Basic properties -/

lemma sphInt_mul_sq (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : v.adicCompletion F)
    {l : v.adicCompletion F} (h : l ≠ 0) (s : ℝ) : sphInt Q v (ρ * l ^ 2) s = sphInt Q v ρ s := by
  rw [sphInt, sqClass_mul_sq ρ h, sphInt]

lemma sphArchAt_mul_sq (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (φ : (Fin n → ℝ) → ℝ) (ρ : ℝ) {l : ℝ}
    (h : l ≠ 0) (s : ℝ) : sphArchAt Q w φ (ρ * l ^ 2) s = sphArchAt Q w φ ρ s := by
  rw [sphArchAt, sqClass_mul_sq ρ h, sphArchAt]

/-- **$Z(s,\rho\lambda^2) = Z(s,\rho)$** for $\lambda \in F^\times$ (Weil 1982, p. 102: the change of variables
$(x,y) \mapsto (x,\lambda^{-1}y)$ maps $T(\rho)$ onto $T(\rho\lambda^2)$): every local factor depends only on the local square
class. -/
@[kb "weil1982" "§4.5, p. 102 (Z(s,ρλ²) = Z(s,ρ))"]
theorem sphericalZetaAt_mul_sq (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (ρ : F) {l : F}
    (h : l ≠ 0) (s : ℝ) : sphericalZetaAt Q Φ (ρ * l ^ 2) s = sphericalZetaAt Q Φ ρ s := by
  unfold sphericalZetaAt
  have h1 : ∏ w, sphArchAt Q w (Φ w) (realEmb w (ρ * l ^ 2)) s = ∏ w, sphArchAt Q w (Φ w) (realEmb w ρ) s :=
    Finset.prod_congr rfl fun w _ => by
      rw [map_mul, map_pow]; exact sphArchAt_mul_sq Q w _ _ ((map_ne_zero _).mpr h) s
  have h2 : ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q v (algebraMap F (v.adicCompletion F) (ρ * l ^ 2)) s =
      ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q v (algebraMap F (v.adicCompletion F) ρ) s :=
    tprod_congr fun v => by
      rw [sphLocal, sphLocal, map_mul, map_pow,
        sphInt_mul_sq Q v _ ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr h)]
  rw [h1, h2]

lemma sphInt_nonneg (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : v.adicCompletion F) (s : ℝ) :
    0 ≤ sphInt Q v ρ s :=
  setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)

lemma one_sub_inv_qv_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < 1 - (qv v)⁻¹ := by
  have : (1 : ℝ) < qv v := one_lt_qv v
  have := inv_lt_one_of_one_lt₀ this
  linarith

lemma sphLocal_nonneg (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : v.adicCompletion F) (s : ℝ) :
    0 ≤ sphLocal Q v ρ s :=
  div_nonneg (mul_nonneg zero_le_two (sphInt_nonneg Q v ρ s)) (one_sub_inv_qv_pos v).le

lemma sphArchAt_nonneg (Q : QuadForm (𝓞 F) n) (w : RealPlace F) {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ x, 0 ≤ φ x)
    (ρ : ℝ) (s : ℝ) : 0 ≤ sphArchAt Q w φ ρ s :=
  mul_nonneg zero_le_two (setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hφ x)))

lemma sphericalZetaAt_nonneg (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : ∀ w x, 0 ≤ Φ w x) (ρ : F) (s : ℝ) : 0 ≤ sphericalZetaAt Q Φ ρ s :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Finset.prod_nonneg fun w _ => sphArchAt_nonneg Q w (hΦ w) _ s))
    (tprod_nonneg fun v => sphLocal_nonneg Q v _ s)

end QuadFormsKB.SphericalZeta
