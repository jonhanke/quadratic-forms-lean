/-
# Hanke 2005, (3.3) at dyadic places with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$: split into shape and density

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

The named statement `ShimuraDensityDyadicBad F` (a statement about the whole local factor (3.3) of a *global* form at a
dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$) is replaced by two smaller, purely local named statements,
mirroring the odd-place architecture of `DensityOddShape.lean`:

* `DyadicMaximalKernel F` (**shape**; O'Meara 91:2 with 63:?): the local form of a maximal lattice is
  $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to $\mathbb H^k\perp N$, $\mathbb H$ the hyperbolic plane $x_0x_1$, where $N$
  is a nondegenerate form in $r$ variables over $\mathfrak o_\mathfrak p$ with the extension property (`MaxProp`: $N$ is maximal)
  on an *anisotropic* space; $r=t_\mathfrak p$.
* `DyadicKernelDensity F` (**density**; Shimura, Thm 8.6(3), Prop. 3.9): for every such $\mathbb H^k\perp N$ with
  $[\widetilde\Lambda:\Lambda]\ne1$ and (for odd rank) Shimura's determinant hypothesis,
  $\alpha_\pi(\mathbb H^k\perp N)=\tfrac12\beta_\pi(\mathbb H^k\perp N,\mathbb H^k\perp N)=[\widetilde\Lambda:\Lambda]\,\xi$ with $\xi$ the case $t=r$ of `xiShimura`.

*Proved here*: `shimuraDensityDyadicBad_of_split : DyadicMaximalKernel F -> DyadicKernelDensity F -> ShimuraDensityDyadicBad F`
(transport along the $\mathrm{GL}$-equivalence of the densities, of $\det H$ ($\det U$ a unit), of $\mathrm{ord}$ of the discriminant
$\delta$ and of $\mathfrak p$-ramification in $K=F(\sqrt\delta)$ (unit squares do not change `IsUnramSqrt`), of Shimura's
determinant hypothesis, and the passage from Hanke's measure-theoretic $\beta$ to the form density).

*Checks against the dyadic examples of the thesis* (all over $\mathbb Q_2$): $x_0^2+x_1^2+x_2^2$ ($k=0$, $r=3$,
$N$ itself, $\alpha=48$); the Hurwitz order ($k=0$, $r=4$, $\alpha=36$); $A_2\perp A_1$, where $A_2$ is the norm form of the unramified
quadratic extension, which represents $-1$, so the space is isotropic and the lattice is $\mathbb H\perp\langle u\rangle$ ($k=1$,
$r=1$, $[\widetilde\Lambda:\Lambda]=2$, $\xi=1-2^{-2}=3/4$, $\alpha=3/2$).
-/
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.LocalDensity.FormDensityHyperbolic

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

section Defs

variable {R : Type*} [CommRing R]

/-- **$\mathbb H^k\perp N$**: $k$ hyperbolic planes $x_{2i}x_{2i+1}$ added to $N$ (in $r+2k$ variables). -/
def hypSum {r : ℕ} (N : QuadForm R r) : (k : ℕ) → QuadForm R (r + 2 * k)
  | 0 => N
  | k + 1 => QuadForm.orthSum (m := r + 2 * k) (n := 2) (hypSum N k) (DVR.hyperbolic R)

end Defs

variable {F : Type} [Field F] [NumberField F]

/-- **The Jordan shape of a maximal lattice at a dyadic place** (a **named input**; O'Meara 91:2: a maximal lattice on
$V=\mathbb H^k\perp V_0$, $V_0$ anisotropic, is $\mathbb H^k\perp N$ with $N$ the maximal lattice $\{x:Q(x)\in\mathfrak o\}$ of
$V_0$; Hanke thesis §3, p. 8). For $\mathfrak p\mid2$ with $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\ne1$ and $\Lambda=\mathcal O_F^n$
maximal (with Shimura's hypothesis), the local form $Q_\mathfrak p$ is $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to
`hypSum N k` ($n=r+2k$), with $N$ nondegenerate, $N\otimes F_\mathfrak p$ anisotropic, $N$ having the extension property `MaxProp`
(it is a maximal lattice), and $r=t_\mathfrak p=\dim\theta_\mathfrak p$ (`anisoDim`). Field: `kernel`.
*Status:* proved, `dyadicMaximalKernel` (DensityDyadicKernelShape.lean). -/
@[kb "omeara1963" "91:2 (maximal lattice H^k ⊥ N on an anisotropic kernel, dyadic)"]
structure DyadicMaximalKernel (F : Type) [Field F] [NumberField F] : Prop where
  /-- The shape of the local form and its anisotropic dimension. -/
  kernel : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ ≠ 1 →
      ∃ (k r : ℕ) (h : r + 2 * k = n) (N : QuadForm (v.adicCompletionIntegers F) r),
        N.Nondegenerate ∧ MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) ∧
        (∀ y : Fin r → v.adicCompletion F,
          (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) ∧
        IsGLEquiv (NF.Qp v Q₀) (h ▸ hypSum N k) ∧ anisoDim v Q₀ = r

/-- **Shimura's local density of $\mathbb H^k\perp N$ at a dyadic place** (a **named input**; Shimura, Thm 8.6(3),
Prop. 3.9, (3.1.9); Hanke thesis (3.3), p. 8, in the repository's normalization $\alpha_\mathfrak p=[\widetilde\Lambda:\Lambda]\,\xi$).
For $\mathfrak p\mid2$, $N$ a nondegenerate form in $r$ variables over $\mathfrak o_\mathfrak p$ with the extension property on an
anisotropic space, $n=r+2k\ge3$, $D=\det H(\mathbb H^k\perp N)$ with $|D|^{-1}\ne1$ and (for odd $n$) $D/2^n$ a unit times a
square: $\beta_\pi(\mathbb H^k\perp N)=2\,|D|^{-1}\,\xi$ (`localDensityForm` is twice Siegel's $\alpha_\mathfrak p$, which equals $|D|^{-1}\xi$), where $\xi=$ `xiShimura q n r ram (|D|^{-1}=1)`, $q=N\mathfrak p$, and `ram` is
"$\mathfrak p$ is ramified in $F_\mathfrak p(\sqrt\delta)$", $\delta=(-1)^{n/2}D/2^n$. Field: `density`. Not definitionally the
conclusion of (3.3): it concerns the local form density of a hyperbolic sum with an anisotropic maximal kernel only. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N with Λ̃_p ≠ Λ_p; quoting Shimura 1999, Thm 8.6(3), Prop. 3.9)"]
structure DyadicKernelDensity (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local density of $\mathbb H^k\perp N$. -/
  density : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) → ∀ {k r : ℕ}, 3 ≤ r + 2 * k →
    ∀ N : QuadForm (v.adicCompletionIntegers F) r, N.Nondegenerate →
      MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) →
      (∀ y : Fin r → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) →
      ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 →
      (Odd (r + 2 * k) → ∃ c : v.adicCompletion F, c ≠ 0 ∧
        ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) /
          2 ^ (r + 2 * k) * c ^ 2‖ = 1) →
      DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) =
        2 * ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ *
          xiShimura (normQ v) (r + 2 * k) r
            (¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
              ((((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k))))
            (‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ = 1)

/-- Multiplying by the square of a unit does not change `IsUnramSqrt`. -/
theorem isUnramSqrt_mul_unit_sq (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (s : v.adicCompletionIntegers F) (hs : IsUnit s) :
    IsUnramSqrt v (x * ((s : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2) ↔ IsUnramSqrt v x := by
  have hs0 : ((s : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    intro h
    have := norm_coe_unit v hs
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set t : v.adicCompletion F := ((s : v.adicCompletionIntegers F) : v.adicCompletion F) with ht
  constructor
  · rintro ⟨c, hc, y, hy, e⟩
    refine ⟨t * c, mul_ne_zero hs0 hc, y, hy, ?_⟩
    rw [← e]; ring
  · rintro ⟨c, hc, y, hy, e⟩
    refine ⟨c / t, div_ne_zero hc hs0, y, hy, ?_⟩
    rw [← e]; field_simp

open DensitySD in
/-- **Siegel's density at a dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, from the shape and the
density of the kernel sums:** $\alpha_\mathfrak p=[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p ≠ Λ_p; from shape and kernel density)"]
theorem siegelDensity_dyadicBad (IA : DyadicMaximalKernel F) (IB : DyadicKernelDensity F)
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) (h2 : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    (h1 : dualIndexAt v Q₀ ≠ 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  obtain ⟨k, r, h, N, hNnd, hNmax, hNan, hequiv, ht⟩ := IA.kernel hn Q₀ hQ hmax hdet v h2 h1
  subst h
  obtain ⟨U, hU, hUe⟩ := hequiv
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) (hypSum N k) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUe x).symm⟩
  have hβ : DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) =
      DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) :=
    (DVR.localDensityForm_congr_left hiso (NF.Qp v Q₀) (NF.π v)).trans
      (DVR.localDensityForm_congr_right (hypSum N k) hiso (NF.π v))
  -- the determinants
  set DQ := (NF.Qp v Q₀).hessian.det with hDQ
  set DH := (hypSum N k).hessian.det with hDH
  have hHess := DVR.hessian_eq_of_eval hUe
  have hDHeq : DH = U.det * U.det * DQ := by
    rw [hDH, hHess, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hcoe : ((DH : v.adicCompletionIntegers F) : v.adicCompletion F) =
      ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 *
        ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hDHeq]; push_cast; ring
  have hnormU := norm_coe_unit v hU
  have hnormDH : ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ‖((DQ : v.adicCompletionIntegers F) : v.adicCompletion F)‖ := by
    rw [hcoe, norm_mul, norm_pow, hnormU, one_pow, one_mul]
  have hdual : dualIndexAt v Q₀ = ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ := by
    unfold dualIndexAt
    rw [← hDQ, hnormDH]
  -- the cast of the global determinant
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) =
      ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hDQ, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hdisc : algebraMap F (v.adicCompletion F) (discK Q₀) =
      (-1) ^ ((r + 2 * k) / 2) * (((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k)) := by
    unfold discK
    rw [map_mul, map_div₀, map_pow, map_pow, map_neg, map_one, map_ofNat, key]
  -- ramification
  have hram : IsRamifiedAt v Q₀ ↔ ¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
      ((((DH : v.adicCompletionIntegers F) : v.adicCompletion F)) / 2 ^ (r + 2 * k))) := by
    unfold IsRamifiedAt
    rw [hdisc, hcoe]
    refine not_congr ?_
    have : (-1 : v.adicCompletion F) ^ ((r + 2 * k) / 2) *
        (((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 *
          ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k)) =
        ((-1) ^ ((r + 2 * k) / 2) *
          (((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k))) *
          ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 := by ring
    rw [this]
    exact (isUnramSqrt_mul_unit_sq v _ _ hU).symm
  -- Shimura's hypothesis for the kernel sum
  have hdetH : Odd (r + 2 * k) → ∃ c : v.adicCompletion F, c ≠ 0 ∧
      ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k) * c ^ 2‖ = 1 := by
    intro hodd
    obtain ⟨c, hc0, hc⟩ := hdet hodd v
    rw [map_div₀, map_pow, map_ofNat, key] at hc
    have hs0 : ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnormU
      exact zero_ne_one hnormU
    refine ⟨c / ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F), div_ne_zero hc0 hs0, ?_⟩
    rw [← hc, hcoe]
    congr 1
    field_simp
  have hB := IB.density v h2 hn N hNnd hNmax hNan (by rw [← hdual]; exact h1) hdetH
  have hxi : xiAt v Q₀ = xiShimura (normQ v) (r + 2 * k) r
      (¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
        ((((DH : v.adicCompletionIntegers F) : v.adicCompletion F)) / 2 ^ (r + 2 * k))))
      (‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ = 1) := by
    unfold xiAt
    rw [ht, hdual]
    congr 1
    exact propext hram
  rw [NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion, hβ, hB, hxi, hdual, ← hDH]
  ring

/-- **(3.3) at a dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, from the shape and the kernel density**
(Hanke thesis, (3.3), p. 8): `ShimuraDensityDyadicBad F` follows from `DyadicMaximalKernel F` and `DyadicKernelDensity F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p ≠ Λ_p; from shape and kernel density)"]
theorem shimuraDensityDyadicBad_of_split (IA : DyadicMaximalKernel F) (IB : DyadicKernelDensity F) :
    ShimuraDensityDyadicBad F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v h2 h1 => ?_⟩
  rw [hankeBeta_gramV v Q₀ hQ, siegelDensity_dyadicBad IA IB v hn Q₀ hQ hmax hdet h2 h1]
  unfold shimuraBetaRHS
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow]
  have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  generalize ‖(2 : v.adicCompletion F)‖ = a at *
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have e : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
    congr 1; ring
  rw [e]; ring

end QuadFormsKB.Hanke2005
