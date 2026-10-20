/-
# The zeta function of a quaternion algebra and the base case $\tau(SO_3) = 2$

Weil (1982, §3.1, pp. 30–41; §3.2, Thm. 3.2.1, p. 43; §3.7(a), p. 62, and Thm. 3.7.1, p. 65) proves $\tau(SO_3) = 2$ from the zeta function
of a quaternion algebra $D$:
$$Z_\Phi(s) = \int_{D_{\mathbb A}^\times}\Phi(x)\,|N(x)|^s\,\omega_{\mathbb A},\qquad \omega = N(x)^{-2}dx,$$
computed **multiplicatively** (an Euler product of local integrals, pp. 36–38: residue $\rho_k\int\Phi$ at $s = 2$) and
**additively** (unfolding over $D_k^\times$, which acts simply transitively on $D_k\setminus0$, Poisson on $D_{\mathbb A}$, pp. 39–40:
residue $c\,\Psi(0)$ with $c$ the volume constant of Lemma 3.1.2). Comparing gives $c = \rho_k$ (p. 40; Thm. 3.1.1 (iii), p. 41), then
$\tau(D^\times/k^\times) = 2$ (Thm. 3.2.1), and $SO_3 \cong D^\times/k^\times$ (`Quat.projUnitsEquivSO`).

**What this file does, in the repository's combinatorial setting** ($F$ totally real, $a, b \in \mathcal O_F$ with
$D = (a,b)_F$ totally definite, $\Lambda = \mathcal O_F\langle 1, i, j, k\rangle$ the standard order):
* the norm form $\langle 1, -a, -b, ab\rangle$ of $\Lambda$ as a form over $\mathcal O_F$, written as the split form
  $\langle 1\rangle \perp \langle -a, -b, ab\rangle$ (`normForm`, `pureFormO`; over $F$ they are `Quat.nrdForm` and
  `Quat.pureForm`: `map_normForm`, `map_pureFormO`);
* **the zeta function of $D$, multiplicatively** (`zetaD` = `globalZeta` of the norm form for the Gaussian
  $\Phi_w = e^{-\pi\,\mathrm{nrd}_w}$; Weil's (2), with $s \mapsto s + 2$ and without the convergence factors), and **its residue**
  $\lim_{s\to0^+}s\,Z_D(s) = \rho_F\int_{D_{\mathbb A}}\Phi\,dx$ (`tendsto_mul_zetaD`; `ZetaResidue` in rank $n = 4$);
* **the additive zeta of the $SO_4$-genus** of $\Lambda$ (`genusAdditiveZeta`) and its residue $\frac{\rho_F}2\,\tau(SO(\Lambda))\int\Phi$
  (`tendsto_mul_additiveZetaD`);
* **the reduction of the base case to Weil's comparison of residues** (`tamagawaNumberTwo_pureForm_iff`): for $h_F = 1$ and
  $[F:\mathbb Q] \ge 2$,
  $$\tau(SO(D^0, \mathrm{nrd})) = 2 \iff \tau(SO(D, \mathrm{nrd})) = 2 \iff \lim_{s\to0^+}s\,Z^+(s) = \lim_{s\to0^+}s\,Z_D(s),$$
  the first equivalence by `Tamagawa.tamagawaNumberTwo_three_iff_four` ($m_0 = 1$), the second by the two residues.

**What is not done** (the remaining content of Weil's base case): the additive calculation for $D$
*over $D^\times$* (Weil pp. 39–40) and its identification with the $SO_4$-genus sum $Z^+$, i.e. Weil's Theorem 3.1.1 (iii)
$\int_{D_{\mathbb A}^\times/D_k^\times}F(|N(x)|)\,\omega_{\mathbb A} = \rho_k\int_0^\infty F(t)\,dt/t$ in combinatorial form (the Eichler mass formula
$\sum_{[I]}|O_l(I)^\times/\mathcal O_F^\times|^{-1}$ for the left ideal classes of an order), plus the isogeny bookkeeping
$SO(D,\mathrm{nrd}) = (D^\times\times D^\times)/\ldots$ (Thm. 3.3.1). That needs orders, ideal classes and their unit groups in
quaternion algebras over $F$, which are not in Mathlib or this repository.

Sources: Weil 1982, §§3.1–3.2, 3.7 (printed page numbers are page headers); Vignéras 1980,
Ch. III §5 and Ch. V (zeta functions of orders, the mass formula) [unverified]; Voight 2021, Ch. 25–26 (zeta functions of
quaternion orders, Eichler's mass formula) [unverified].
-/
import QuadFormsKB.Tamagawa.TauFour
import QuadFormsKB.Tamagawa.TauTwo
import QuadFormsKB.Tamagawa.Quaternion

open NumberField Filter Topology
open scoped Real

noncomputable section

namespace QuadFormsKB.QuatZeta

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta QuadFormsKB.GlobalZeta QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

/-- **The ternary norm form $\langle -a, -b, ab\rangle$ over $\mathcal O_F$** ($a, b \in \mathcal O_F$): $\mathrm{nrd}$ on the pure part
$\mathcal O_Fi \oplus \mathcal O_Fj \oplus \mathcal O_Fk$ of the standard order of $(a,b)_F$ (coordinates $x_0, x_1, x_2$ for $i, j, k$). -/
def pureFormO (a b : 𝓞 F) : QuadForm (𝓞 F) 3 := QuadForm.diag ![-a, -b, a * b]

/-- **The quaternary norm form $\langle 1, -a, -b, ab\rangle$ over $\mathcal O_F$**, as the split form $\langle 1\rangle\perp\langle -a,-b,ab\rangle$:
$\mathrm{nrd}(x_0 + x_1i + x_2j + x_3k) = x_0^2 - ax_1^2 - bx_2^2 + abx_3^2$ on the standard order $\Lambda = \mathcal O_F\langle1,i,j,k\rangle$. -/
def normForm (a b : 𝓞 F) : QuadForm (𝓞 F) 4 := splitForm 1 (pureFormO a b)

omit [NumberField F] in
theorem map_pureFormO (a b : 𝓞 F) :
    (pureFormO a b).map (algebraMap (𝓞 F) F) = Quat.pureForm (a : F) (b : F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureFormO, Quat.pureForm, QuadForm.map, QuadForm.diag, Matrix.diagonal]

omit [NumberField F] in
theorem map_normForm (a b : 𝓞 F) :
    (normForm a b).map (algebraMap (𝓞 F) F) = Quat.nrdForm (a : F) (b : F) := by
  rw [normForm, map_splitForm, map_pureFormO]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The zeta function of $D = (a,b)_F$, multiplicatively** (Weil 1982, §3.1, (2), p. 36, and the Euler product pp. 36–38, for
the standard order and the Gaussian test function $\Phi_w(x) = e^{-\pi\,\mathrm{nrd}_w(x)}$, $\Phi_v = \mathbf 1_{\Lambda_v}$): the $$Z_D(s) = |d_F|^{-2}\prod_w\int_{D_w}|\mathrm{nrd}\,x|_w^s\Phi_w\,dx\prod_v\int_{\Lambda_v}|\mathrm{nrd}\,x|_v^s\,dx.$$
Weil's $Z_\Phi(s)$ is this at $s - 2$ ($\omega = N(x)^{-2}dx$), times his convergence factors $\prod_v(1 - N\mathfrak p^{-1})^{-1}$
(absorbed by `ZetaResidue` into $\zeta_F(1+s)$). Real $s > 0$. -/
@[kb "weil1982" "§3.1, (2), p. 36, and the multiplicative calculation, pp. 36-38"]
def zetaD (a b : 𝓞 F) (s : ℝ) : ℝ := globalZeta (normForm a b) (gaussian (normForm a b) π) s

variable [IsTotallyReal F]

/-- **The residue of the zeta function of $D$** (Weil 1982, §3.1, p. 38, shifted to $s = 0$): for $D = (a,b)_F$ totally
definite ($\langle 1,-a,-b,ab\rangle$ totally positive definite),
$$\lim_{s\to0^+}s\,Z_D(s) = \rho_F\int_{D_{\mathbb A}}\Phi\,dx,$$
$\rho_F$ = `dedekindZeta_residue F`. `tendsto_mul_globalZeta_zero_gaussian` with $n = 4$. -/
@[kb "weil1982" "§3.1, p. 38 (residue ρ_k ∫Φ of the multiplicative zeta of D)"]
theorem tendsto_mul_zetaD {a b : 𝓞 F} (hpd : IsTotallyPosDef (formF (normForm a b))) :
    Tendsto (fun s => s * zetaD a b s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian (normForm a b) π))) :=
  tendsto_mul_globalZeta_zero_gaussian _ (nondegenerate_of_map hpd.nondegenerate)
    (TauTwo.globalZeta_isTotallyPosDef _ hpd) le_rfl Real.pi_pos

/-- **The additive zeta of the $SO_4$-genus of the standard order, and its residue** ($n = 4$, $h_F = 1$):
$\lim_{s\to0^+}s\,Z^+(s) = \frac{\rho_F}2\,\tau(SO(D,\mathrm{nrd}))\int_{D_{\mathbb A}}\Phi\,dx$, $\tau$ = `tauSO (normForm a b)`. -/
@[kb "weil1982" "§4.4, pp. 97-98 (index 0); §4.5, p. 109 (residue ρ_kτ(G)/2)"]
theorem tendsto_mul_additiveZetaD [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
    (hpd : IsTotallyPosDef (formF (normForm a b))) :
    Tendsto (fun s => s * genusAdditiveZeta (normForm a b) s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * tauSO (normForm a b) * phiIntegral (gaussian (normForm a b) π))) :=
  tendsto_mul_genusAdditiveZeta_of_pid _ (nondegenerate_of_map hpd.nondegenerate) (by norm_num) hpd

/-- **$\tau(SO(D,\mathrm{nrd})) = 2$ iff the two zeta integrals of $D$ have the same residue** (Weil's comparison, §3.1, p. 40,
in the $SO_4$ form): $\tau(SO_4) = 2 \iff \lim s\,Z^+(s) = \lim s\,Z_D(s) = \rho_F\int\Phi$. -/
@[kb "weil1982" "§3.1, p. 40 (comparison of the residues, c = ρ_k); Thm. 3.7.1 (m = 4), p. 65"]
theorem tamagawaNumberTwo_normForm_iff [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
    (hpd : IsTotallyPosDef (formF (normForm a b))) :
    TamagawaNumberTwo (normForm a b) ↔
      Tendsto (fun s => s * genusAdditiveZeta (normForm a b) s) (𝓝[>] 0)
        (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian (normForm a b) π))) := by
  have hA := tendsto_mul_additiveZetaD hpd
  have hρ := dedekindZeta_residue_pos F
  have hI := TauTwo.phiIntegral_gaussian_pi_pos _ hpd
  constructor
  · intro h
    unfold TamagawaNumberTwo at h
    rw [h] at hA
    convert hA using 2; ring
  · intro h
    have heq := tendsto_nhds_unique hA h
    unfold TamagawaNumberTwo
    have h' : dedekindZeta_residue F * phiIntegral (gaussian (normForm a b) π) * (tauSO (normForm a b) - 2) = 0 := by
      linear_combination 2 * heq
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (mul_pos hρ hI).ne'
    · linarith

/-- **The base case $\tau(SO_3) = 2$ for $(D^0, \mathrm{nrd})$, reduced to Weil's comparison of residues** ($F$ totally real of degree
$\ge 2$, $h_F = 1$, $a, b \in \mathcal O_F$ with $D = (a,b)_F$ totally definite): the following are equivalent:
1. $\tau(SO(\langle -a,-b,ab\rangle)) = 2$ (the sense, the lattice $\mathcal O_Fi\oplus\mathcal O_Fj\oplus\mathcal O_Fk$);
2. the additive zeta of the $SO_4$-genus of the standard order has the residue of the zeta function of $D$:
   $\lim_{s\to0^+}s\,Z^+(s) = \rho_F\int_{D_{\mathbb A}}\Phi\,dx\ (= \lim_{s\to0^+}s\,Z_D(s))$.

*Proof.* `tamagawaNumberTwo_three_iff_four` with $m_0 = 1$ (rank-4 Siegel and the step, both directions) and
`tamagawaNumberTwo_normForm_iff`. -/
@[kb "weil1982" "§3.7(a), p. 62; Thm. 3.7.1, p. 65; via §3.1, pp. 36-41 (zeta of D)"]
theorem tamagawaNumberTwo_pureForm_iff [IsPrincipalIdealRing (𝓞 F)] (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {a b : 𝓞 F} (hpd : IsTotallyPosDef (formF (normForm a b))) :
    TamagawaNumberTwo (pureFormO a b) ↔
      Tendsto (fun s => s * genusAdditiveZeta (normForm a b) s) (𝓝[>] 0)
        (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian (normForm a b) π))) := by
  have h1 : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F 1) := fun v => by simp
  rw [tamagawaNumberTwo_three_iff_four hd h1 (pureFormO a b) hpd (isIntegral_stdLat _)]
  exact tamagawaNumberTwo_normForm_iff hpd

end QuadFormsKB.QuatZeta
