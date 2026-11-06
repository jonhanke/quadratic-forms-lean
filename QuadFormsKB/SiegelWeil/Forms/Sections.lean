/-
# Sections of the Siegel parabolic in degree $r$
**Layer:** abstract local harmonic analysis (every model `LocalData.IsModel` with the interface `IsGLModel`), specialized
to every finite place $v$ of a number field (`weilRepSpV`, dyadic places included).

**Setting.** $V = K^n$, $n = 2m$, $Q = \langle a_0, \dots, a_{n-1}\rangle$ (0-based indices), the degree $r$, and
$V^r = M_{n\times r}(K)$ (`PtG m r K`): column $j$ of $X$ is $x_j \in V$, and $Q[X] = X^{\mathsf T}\operatorname{diag}(a)X$ (`QX`) is the
Gram matrix $\big(\tfrac12B(x_j, x_l)\big)_{jl}$. $\omega$ is the Weil representation of $\mathrm{Sp}_{2r}(k)$ on $S(V^r)$
(`weilRepSpInf`; at a finite place `weilRepSpV`), with $n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix}$ (`spN`),
$m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}$ (`spM`) and $w = \begin{pmatrix}0&1\\-1&0\end{pmatrix}$ up to the sign convention of `spW`.

**Results.**
* `secR` (**the section**): $f_\Phi(g) = (\omega(g)\Phi)(0)$, $g \in \mathrm{Sp}_{2r}(k)$, $\Phi \in S(V^r)$.
* `secR_parabolic` (**$f_\Phi \in I(s_0, \chi_V)$**): for the Siegel parabolic $P = MN$,
  $$f_\Phi(n(B)m(A)g) = \chi_V(\det A)\,|\det A|^{m}\,f_\Phi(g),\qquad m = \tfrac n2 = s_0 + \rho_r,\quad s_0 = \tfrac n2 - \tfrac{r+1}2,\ \rho_r = \tfrac{r+1}2.$$
* `secR_spW_spN` (**the big cell**): $f_\Phi(w\,n(B)) = \gamma_V^{\,r}c_B^{\,r}\int_{V^r}\Phi(X)\,\psi(\operatorname{tr}(B\,Q[X]))\,dX$, with
  $c_B = \prod_i|2a_i|^{1/2}$ (`cB`) and $dX = \mu^{\otimes(n\times r)}$ (`muG`); the function whose Fourier transform in $B$ is the
  Whittaker integral (`SiegelWeil/Forms/LocalWhittaker.lean`).
* `secRV`: the same at a finite place, unconditionally (`weilRepSpV`).

For $r = 1$ these are `sec_borel` and `sec_wMat_nMat` (`SiegelWeil/Sections.lean`).

Sources: Kudla, *Notes on the local theta correspondence* (1996), §II.1 [unverified]; Kudla, *Some extensions of the
Siegel–Weil formula* (2008), §1 [unverified]; Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*,
Acta Math. 113 (1965), Ch. II [unverified]; Kudla–Rallis, J. reine angew. Math. 387 (1988), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.WeilRepUncond

open MeasureTheory Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep WeilRep.LocalData WeilRep.Genus

section Abstract

variable {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} (hD : D.IsModel) {m r : ℕ}
  {a : Fin (2 * m) → Kˣ} (hGL : IsGLModel D a r) {k : Type*} [Field k] [Infinite k] (ι : k →+* K)
  (h2 : (2 : k) ≠ 0)

/-- **The section attached to $\Phi \in S(V^r)$:** $f_\Phi(g) = (\omega(g)\Phi)(0)$ for $g \in \mathrm{Sp}_{2r}(k)$, with $\omega$ the
Weil representation of $\mathrm{Sp}_{2r}(k)$ on $S(V^r)$ in the Schrödinger model (`weilRepSpInf`). Arguments: `hD` (a model of
the local harmonic analysis), `hGL` (the interface `IsGLModel`), `ι : k → K`, `h2 : 2 ≠ 0` in $k$. -/
@[kb "kudla1996" "§II.1 (the map $\\varphi \\mapsto \\lambda(\\varphi)(g) = (\\omega(g)\\varphi)(0)$, $\\mathrm{Sp}_{2n}$) [unverified]"]
def secR (Φ : Sg D m r) (g : Sp r k) : ℂ :=
  ((weilRepSpInf hD hGL ι h2 g Φ : Sg D m r) : PtG m r K → ℂ) 0

lemma QX_zero : QX a (0 : PtG m r K) = 0 := by simp [QX]

variable {hD hGL ι h2}

/-- $f_\Phi(n(B)g) = f_\Phi(g)$: $\omega(n(B))$ multiplies by $\psi(\operatorname{tr}(B\,Q[X]))$, which is $1$ at $X = 0$. -/
theorem secR_spN_mul (Φ : Sg D m r) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) (g : Sp r k) :
    secR hD hGL ι h2 Φ (spN B hB * g) = secR hD hGL ι h2 Φ g := by
  simp only [secR, map_mul, Module.End.mul_apply, weilRepSpInf_spN, endN_apply hGL ι hB, opNg, QX_zero,
    Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

/-- $f_\Phi(m(A)g) = \chi_V(\det A)\,|\det A|^m\,f_\Phi(g)$. -/
theorem secR_spM_mul (Φ : Sg D m r) (A : GL (Fin r) k) (g : Sp r k) :
    secR hD hGL ι h2 Φ (spM A * g) =
      D.chiV a (ι (A : Matrix (Fin r) (Fin r) k).det) * (D.md (ι (A : Matrix (Fin r) (Fin r) k).det) : ℂ) ^ m *
        secR hD hGL ι h2 Φ g := by
  have hdet : ((Matrix.GeneralLinearGroup.map ι A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det =
      ι (A : Matrix (Fin r) (Fin r) k).det := by
    rw [show ((Matrix.GeneralLinearGroup.map ι A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      (A : Matrix (Fin r) (Fin r) k).map ι from rfl]
    exact (RingHom.map_det ι _).symm
  simp only [secR, map_mul, Module.End.mul_apply, weilRepSpInf_spM, endM_apply, opMg, Matrix.zero_mul, hdet]

/-- **$f_\Phi \in I(s_0, \chi_V)$ for the Siegel parabolic** (every model, so every finite place and the archimedean
block):
$$f_\Phi(n(B)\,m(A)\,g) = \chi_V(\det A)\,|\det A|^{m}\,f_\Phi(g)\qquad(B = {}^tB,\ A \in \mathrm{GL}_r(k)),$$
$|\det A|^m = |\det A|^{n/2} = |\det A|^{s_0 + \rho_r}$ with $s_0 = \tfrac n2 - \tfrac{r+1}2$ and $\rho_r = \tfrac{r+1}2$. -/
@[kb "kudla1996" "§II.1, (1.2) ($\\lambda(\\varphi) \\in I(s_0, \\chi_V)$, $s_0 = \\frac m2 - \\frac{n+1}2$ for $\\dim V = m$, $\\mathrm{Sp}_{2n}$) [unverified]"]
theorem secR_parabolic (Φ : Sg D m r) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) (A : GL (Fin r) k)
    (g : Sp r k) :
    secR hD hGL ι h2 Φ (spN B hB * spM A * g) =
      D.chiV a (ι (A : Matrix (Fin r) (Fin r) k).det) * (D.md (ι (A : Matrix (Fin r) (Fin r) k).det) : ℂ) ^ m *
        secR hD hGL ι h2 Φ g := by
  rw [mul_assoc, secR_spN_mul, secR_spM_mul]

/-- $f_\Phi(1) = \Phi(0)$. -/
@[simp] lemma secR_one (Φ : Sg D m r) : secR hD hGL ι h2 Φ 1 = (Φ : PtG m r K → ℂ) 0 := by
  simp [secR]

/-- $f_\Phi(gh) = f_{\omega(h)\Phi}(g)$ (right translation is the action on $\Phi$). -/
lemma secR_mul (Φ : Sg D m r) (g h : Sp r k) :
    secR hD hGL ι h2 Φ (g * h) = secR hD hGL ι h2 (weilRepSpInf hD hGL ι h2 h Φ) g := by
  simp [secR, map_mul, Module.End.mul_apply]

lemma BX_zero (X : PtG m r K) : BX a X 0 = 0 := by simp [BX]

/-- **The big cell:** $f_\Phi(w\,n(B)) = \gamma_V^{\,r}c_B^{\,r}\int_{V^r}\Phi(X)\,\psi(\operatorname{tr}(B\,Q[X]))\,dX$, $c_B = \prod_i|2a_i|^{1/2}$
(`cB`), $dX$ = `muG`. -/
@[kb "kudla2008" "§1 ($\\lambda(\\varphi)(wn(b)) = \\gamma\\int\\varphi(x)\\psi(\\operatorname{tr}(bQ(x)))dx$) [unverified]"]
theorem secR_spW_spN (Φ : Sg D m r) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    secR hD hGL ι h2 Φ (spW * spN B hB) = D.gammaV a ^ r * D.cB a ^ r *
      ∫ X, (Φ : PtG m r K → ℂ) X * (D.ψ (trace (B.map ι * QX a X)) : ℂ) ∂muG D m r := by
  simp only [secR, map_mul, Module.End.mul_apply, weilRepSpInf_spW, endW_apply, weilRepSpInf_spN,
    endN_apply hGL ι hB, opWg, opNg, BX_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  ring

end Abstract

/-! ### Finite places -/

section Place

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {m r : ℕ}

/-- **The section at a finite place** $v$ (every degree $r$, dyadic places included):
$f_\Phi(g) = (\omega_v(g)\Phi)(0)$, $g \in \mathrm{Sp}_{2r}(F_v)$, $\Phi \in S(V_v^r)$, for the unconditional Weil representation
`weilRepSpV`. -/
@[kb "kudla1996" "§II.1 [unverified]"]
def secRV (a : Fin (2 * m) → (Fv)ˣ) (Φ : Sg (localDataV v) m r) (g : Sp r Fv) : ℂ :=
  secR (isModel_V v) (isGLModel_V v a r) (RingHom.id Fv) two_ne_zero Φ g

lemma secRV_eq (a : Fin (2 * m) → (Fv)ˣ) (Φ : Sg (localDataV v) m r) (g : Sp r Fv) :
    secRV v a Φ g = ((weilRepSpV v a r g Φ : Sg (localDataV v) m r) : PtG m r Fv → ℂ) 0 := rfl

/-- $f_\Phi(n(B)m(A)g) = \chi_V(\det A)|\det A|_v^m f_\Phi(g)$ at a finite place. -/
theorem secRV_parabolic (a : Fin (2 * m) → (Fv)ˣ) (Φ : Sg (localDataV v) m r) (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B)
    (A : GL (Fin r) Fv) (g : Sp r Fv) :
    secRV v a Φ (spN B hB * spM A * g) =
      (localDataV v).chiV a (A : Matrix (Fin r) (Fin r) Fv).det *
        ((localDataV v).md (A : Matrix (Fin r) (Fin r) Fv).det : ℂ) ^ m * secRV v a Φ g :=
  secR_parabolic Φ B hB A g

/-- The big cell at a finite place: $f_\Phi(wn(B)) = \gamma_V^rc_B^r\int\Phi(X)\psi_v(\operatorname{tr}(BQ[X]))\,dX$. -/
theorem secRV_spW_spN (a : Fin (2 * m) → (Fv)ˣ) (Φ : Sg (localDataV v) m r) (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) :
    secRV v a Φ (spW * spN B hB) = (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
      ∫ X, (Φ : PtG m r Fv → ℂ) X * ((localDataV v).ψ (trace (B * QX a X)) : ℂ) ∂muG (localDataV v) m r := by
  rw [secRV, secR_spW_spN]
  rfl

end Place

end QuadFormsKB.SiegelWeil.Forms
