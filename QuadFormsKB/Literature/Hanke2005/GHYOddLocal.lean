/-
# The local factor of a maximal lattice of odd rank whose determinant is not a unit times a square

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §6, (6.6), (6.10), (6.11),
Table 4 (odd rank, $\delta\notin A^\times$); J. Hanke, *An exact mass formula for quadratic forms over number fields*,
J. Reine Angew. Math. 584 (2005), (3.3) and Theorem 5.1 (locators: 1999 thesis).

Shimura's (3.3) assumes, for odd $n$, that $\det\varphi$ is locally a unit times a square (`ShimuraDetHyp`). GHY's Table 4
also covers the other case, $\delta\notin A^\times$. At a finite place $\mathfrak p$ where $n$ is odd and $\det H/2^n$ is **not** a
unit times a square (`DetUnitSqAt` fails), we prove, for the maximal lattice $\Lambda = \mathcal O_F^n$, with $m = \lfloor n/2\rfloor$
and $t = t_\mathfrak p$ (`anisoDim`):
$$t\in\{1,3\},\qquad \alpha_\mathfrak p(\Lambda,\Lambda) = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\;\xi',\qquad
\xi' = \begin{cases}2\,(1-q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i}) & t = 1,\\ 2\,(1+q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i}) & t = 3\end{cases}$$
(`siegelDensity_oddNonUnit`, `xiOddNonUnit`; $\alpha$ = `NF.siegelDensity`, Siegel's normalization). Every residue
characteristic, every ramification index; no named input.

*Proof:* $\Lambda_\mathfrak p\simeq\mathbb H^k\perp N$ with $N$ anisotropic and maximal (`exists_hypSum_shape`), $r = t$ odd and
$\le 4$; $N = \langle\pi u\rangle$ ($r = 1$) or $N\simeq\langle\pi c\rangle\perp T$ ($r = 3$) by `GHYOddKernel.lean`; the densities
are `localDensityForm_hypSum_piUnit_closed` and `localDensityForm_hypSum_piUnitT_closed` (`GHYOddNonUnitThree.lean`), and
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = |\det H|^{-1} = q^{e+1}$, $\pi^e\,\|\,2$.

Check: $A_2\perp A_1$ ($x_0^2+x_0x_2+x_2^2+x_1^2$) at $p = 3$ is $\langle1,1,3\rangle$, $t = 3$, $m = 1$:
$\alpha_3 = 3\cdot2(1+3^{-1}) = 8$, the brute-force value (counting solutions by computer, outside Lean).
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddKernel
import QuadFormsKB.Literature.Hanke2005.GHYOddNonUnitThree
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelShape

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Shimura's condition at one place** (Hanke thesis, abstract and §3, p. 7; Shimura 1999, (3.1.1)): $\det H/2^n$ (that is
$\det\varphi$) is a unit of $\mathfrak o_\mathfrak p$ times a square of $F_\mathfrak p$. `ShimuraDetHyp Q₀` says this holds at every
finite place when $n$ is odd (`shimuraDetHyp_iff`). -/
@[kb "hanke2005crelle" "abstract, p. 1; §3, p. 7 (Shimura's condition on det φ, at one place)"]
def DetUnitSqAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  ∃ c : v.adicCompletion F, c ≠ 0 ∧
    ‖algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n) * c ^ 2‖ = 1

theorem shimuraDetHyp_iff (Q₀ : QuadForm (𝓞 F) n) :
    ShimuraDetHyp Q₀ ↔ (Odd n → ∀ v : HeightOneSpectrum (𝓞 F), DetUnitSqAt v Q₀) := Iff.rfl

/-- **GHY's $\xi'$ for odd rank and $\delta\notin A^\times$** (GHY 2001, Table 4, in Shimura's normalization of $\xi$, i.e.
$\alpha_\mathfrak p = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi'$), $m = \lfloor n/2\rfloor$:
$t = 1$: $2(1-q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$; otherwise ($t = 3$): $2(1+q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$. -/
@[kb "ganhankeyu2001" "Table 4 (odd rank, δ ∉ A×; Shimura's normalization of ξ)"]
def xiOddNonUnit (q : ℝ) (n t : ℕ) : ℝ :=
  if t = 1 then 2 * (1 - q ^ (-((n / 2 : ℕ) : ℝ))) * ppow q (n / 2 - 1)
  else 2 * (1 + q ^ (-((n / 2 : ℕ) : ℝ))) * ppow q (n / 2 - 1)

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\mathrm{GL}$-equivalent kernels give $\mathrm{GL}$-equivalent hyperbolic sums. -/
theorem isGLEquiv_hypSum {r : ℕ} {N N' : QuadForm 𝔬 r} (h : DVR.IsGLEquiv N N') :
    ∀ k, DVR.IsGLEquiv (hypSum N k) (hypSum N' k)
  | 0 => h
  | k + 1 => isGLEquiv_orthSum_left _ (isGLEquiv_hypSum h k)

/-- **(3.3) without Shimura's hypothesis: the new places** (GHY 2001, Table 4, $\delta\notin A^\times$; Hanke thesis (3.3)). At a
finite place where $n\ge3$ is odd and $\det H/2^n$ is not a unit times a square, the maximal lattice $\mathcal O_F^n$ has
$t_\mathfrak p\in\{1,3\}$ and $\alpha_\mathfrak p = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi'$ (`xiOddNonUnit`). -/
@[kb "ganhankeyu2001" "(6.6), (6.10), (6.11), Table 4 (odd rank, δ ∉ A×, w = ±1: the local factor)"]
theorem siegelDensity_oddNonUnit (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (hv : ¬ DetUnitSqAt v Q₀) :
    (anisoDim v Q₀ = 1 ∨ anisoDim v Q₀ = 3) ∧
      NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiOddNonUnit (normQ v) n (anisoDim v Q₀) := by
  obtain ⟨k, r, h, N, hN, hNM, hNa, hE⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  subst h
  have ht := anisoDim_of_hypSum v Q₀ hQ N hNa hE
  have hr4 : r ≤ 4 := rank_le_four_of_aniso v _ hNa
  have hrodd : r = 1 ∨ r = 3 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hπ := NF.irreducible_π v
  obtain ⟨U, hU, hUe⟩ := hE
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) (hypSum N k) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUe x).symm⟩
  have hβ : DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) =
      DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) :=
    (DVR.localDensityForm_congr_left hiso (NF.Qp v Q₀) (NF.π v)).trans
      (DVR.localDensityForm_congr_right (hypSum N k) hiso (NF.π v))
  set DQ := (NF.Qp v Q₀).hessian.det with hDQ
  set DH := (hypSum N k).hessian.det with hDH
  have hHess := DVR.hessian_eq_of_eval hUe
  have hDHeq : DH = U.det * U.det * DQ := by
    rw [hDH, hHess, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hcoe : ((DH : 𝔬) : Fv) = ((U.det : 𝔬) : Fv) ^ 2 * ((DQ : 𝔬) : Fv) := by
    rw [hDHeq]; push_cast; ring
  have hnormU := norm_coe_unit v hU
  have hnormDH : ‖((DH : 𝔬) : Fv)‖ = ‖((DQ : 𝔬) : Fv)‖ := by
    rw [hcoe, norm_mul, norm_pow, hnormU, one_pow, one_mul]
  have hdual : dualIndexAt v Q₀ = ‖dN v N‖⁻¹ := by
    unfold dualIndexAt
    rw [← hDQ, ← hnormDH, hDH, norm_det_hypSum]
  have key : algebraMap F Fv ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) = ((DQ : 𝔬) : Fv) := by
    rw [hDQ, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  -- the determinant hypothesis for the kernel
  have hdetN : ¬ ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ r * c ^ 2‖ = 1 := by
    rintro hc
    obtain ⟨c, hc0, hc⟩ := (detHyp_hypSum v N k).2 hc
    apply hv
    have hs0 : ((U.det : 𝔬) : Fv) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnormU
      exact zero_ne_one hnormU
    refine ⟨c * ((U.det : 𝔬) : Fv), mul_ne_zero hc0 hs0, ?_⟩
    rw [map_div₀, map_pow, map_ofNat, key, ← hc, ← hDH, hcoe]
    congr 1
    ring
  -- `π^e ∥ 2`
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (two_ne_zero_O v)
  have hn2 : ‖((2 : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := Tamagawa.norm_coe_of_pow_dvd v he he'
  have hq := DensitySD.q_eq v
  have hQ0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast DVR.q_pos
  rw [NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion, hβ, hdual, ht]
  rcases hrodd with rfl | rfl
  · -- `r = 1`: `N = ⟨π u⟩`
    refine ⟨Or.inl rfl, ?_⟩
    obtain ⟨u, hu, rfl⟩ := kernel_one_of_not_detSq v N hN hNM hdetN
    have hk : 1 ≤ k := by omega
    rw [localDensityForm_hypSum_piUnit_closed hπ ⟨he, he'⟩ hu hk]
    have hdN : ‖dN v (DVR.unary (NF.π v * u))‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ := by
      unfold dN
      rw [hessian_unary_det, show (2 : 𝔬) * (NF.π v * u) = 2 * (NF.π v ^ 1 * u) by ring]
      push_cast
      rw [norm_mul, hn2, show ((NF.π v : 𝔬) : Fv) ^ 1 * ((u : 𝔬) : Fv) = (((NF.π v ^ 1 * u : 𝔬)) : Fv) by push_cast; ring,
        norm_pi_pow_mul_unit v 1 hu]
    have hn : (1 + 2 * k) / 2 = k := by omega
    rw [hdN, xiOddNonUnit, if_pos rfl, hn, hq]
    field_simp
    ring
  · -- `r = 3`: `N ≃ ⟨π c⟩ ⊥ T`
    refine ⟨Or.inr rfl, ?_⟩
    obtain ⟨c, T, hc, hTu, hTan, hNE⟩ : ∃ (c : 𝔬) (T : QuadForm 𝔬 2), IsUnit c ∧ IsUnit T.hessian.det ∧
        (∀ s : Fin 2 → 𝔬, NF.π v ∣ T.eval s → ∀ i, NF.π v ∣ s i) ∧
        DVR.IsGLEquiv N (splitForm (NF.π v * c) T) := by
      by_cases h2 : IsUnit (2 : 𝔬)
      · exact kernel_three_odd_of_not_detSq v h2 N hN hNM hNa hdetN
      · exact kernel_three_dyadic_of_not_detSq v h2 N hNM hNa hdetN
    rw [localDensityForm_of_isGLEquiv v (isGLEquiv_hypSum v hNE k),
      localDensityForm_hypSum_piUnitT_closed hπ ⟨he, he'⟩ hc T hTu hTan k]
    have hdN : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ := by
      unfold dN
      rw [norm_det_of_isGLEquiv v hNE, det_hessian_splitForm,
        show (2 : 𝔬) * (NF.π v * c) * T.hessian.det = 2 * (NF.π v ^ 1 * (c * T.hessian.det)) by ring]
      push_cast
      rw [norm_mul, hn2, show ((NF.π v : 𝔬) : Fv) ^ 1 * (((c : 𝔬) : Fv) * ((T.hessian.det : 𝔬) : Fv)) =
        (((NF.π v ^ 1 * (c * T.hessian.det) : 𝔬)) : Fv) by push_cast; ring,
        norm_pi_pow_mul_unit v 1 (hc.mul hTu)]
    have hn : (3 + 2 * k) / 2 = k + 1 := by omega
    rw [hdN, xiOddNonUnit, if_neg (by decide), hn, hq, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

end Local

end QuadFormsKB.Hanke2005
