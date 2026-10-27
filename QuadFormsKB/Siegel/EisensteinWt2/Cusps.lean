/-
# Constant terms of weight-2 Eisenstein series at every cusp (deliverable 3)

For $W$ of total mass $0$ and $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, the constant term of
$E_W$ at the cusp $\gamma\infty = a/c$ is (`tendsto_eis2_slash`)
$$\lim_{\operatorname{Im}\tau\to\infty}(E_W\,|_2\,\gamma)(\tau) = \sum_{n \in \mathbb{Z}}\frac{W(-nc,\ na)}{n^2},$$
because $E_W|\gamma = E_{W\cdot\gamma}$ (`eis2_slash`) and the constant term of $E_{W'}$ is its $c = 0$ row
(`tendsto_eis2_atImInfty`), with $(W\cdot\gamma)(0, n) = W((0, n)\gamma^{-1}) = W(-nc, na)$.  For the
Diamond–Shurman series this reads (`tendsto_dsEisMF_cusp`)
$$\lim (E_2^{\psi,\varphi,t}|_2\gamma)(\tau) = \sum_{n}\mathbf{1}_{vt \mid nc}\;\psi\Big(\frac{-nc}{vt}\Big)\,
  \bar\varphi(na)\,n^{-2},$$
in the same shape as the theta-series constant terms `tendsto_theta_cusp` (there stated with
$\Theta((a\tau+b)/(c\tau+d))(c\tau+d)^{-k}$, which is $(\Theta\,|_k\,\gamma)(\tau)$).
-/
import QuadFormsKB.Siegel.EisensteinWt2.DSQExp

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

variable {N : ℕ} [NeZero N]

/-- **The constant term of $E_W$ at the cusp $\gamma\infty$** (total mass $0$). -/
@[kb "diamondshurman2005" "§4.6 (constant terms at cusps) [unverified]"]
theorem tendsto_eis2_slash (W : ZMod N → ZMod N → ℂ) (hW : totalSum W = 0) (γ : SL(2, ℤ)) :
    Tendsto (eis2 W ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : ℤ, wt W (-(n * γ 1 0)) (n * γ 0 0) * ((n : ℂ) ^ 2)⁻¹)) := by
  rw [eis2_slash W hW γ]
  convert tendsto_eis2_atImInfty (slashW W γ) using 3
  simp only [wt, slashW]
  funext n
  push_cast
  congr 2 <;> ring

/-- **The constant term of $E_2^{\psi,\varphi,t}$ at the cusp $\gamma\infty = \gamma_{00}/\gamma_{10}$.** -/
@[kb "diamondshurman2005" "§4.6 (constant terms at cusps) [unverified]"]
theorem tendsto_dsEisMF_cusp {u v : ℕ} {ψ : DirichletCharacter ℂ u} {φ : DirichletCharacter ℂ v} {t : ℕ}
    (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) (γ : SL(2, ℤ)) :
    Tendsto ((⇑(dsEisMF ψ φ t hN hne) : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : ℤ, dsF ψ φ (v * t) (-(n * γ 1 0)) (n * γ 0 0) * ((n : ℂ) ^ 2)⁻¹)) := by
  have hper := dsF_periodic (ψ := ψ) (φ := φ) hN
  have h := tendsto_eis2_slash (dsW (N := N) ψ φ t) (totalSum_dsW hN hne) γ
  simp only [dsW, wt_ofPer hper.1 hper.2] at h
  exact h

end QuadFormsKB.Siegel.EisensteinWt2
