import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelativeQuadratic
import QuadFormsKB.Binary.LFactorization
import QuadFormsKB.Tamagawa.QuadraticTwist

/-!
# $\zeta_E(s) = \zeta_F(s)\,L(s, \chi_{E/F})$ for a relative quadratic extension

Let $E/F$ be an extension of number fields of degree $2$ and $\chi = \chi_{E/F}$ its splitting character on the primes
of $F$ (`relChar`, `RelativeQuadratic.lean`). Define, for real $\sigma > 1$,
$$L(\sigma, \chi_{E/F}) = \prod_{\mathfrak p}\big(1 - \chi(\mathfrak p)N\mathfrak p^{-\sigma}\big)^{-1}$$
(`relLR F E σ`, the Euler product over the nonzero primes of $\mathcal O_F$; it converges absolutely, `hasProd_relLR`).

**`dedekindZetaR_eq_mul`:** $\zeta_E(\sigma) = \zeta_F(\sigma)\,L(\sigma,\chi_{E/F})$ for real $\sigma > 1$. *Proof (local):* regroup
the Euler product of $\zeta_E$ (`NFEuler.hasProd_dedekindZeta`) by the primes of $F$ below
(`HasProd.sigma` over `Equiv.sigmaFiberEquiv below`) and apply the local factor identity `localFactor_eq` at each
$\mathfrak p$. This sharpens the inequality $\zeta_F^{(B)}L^{(B)} \le \zeta_E$ (`QTwist.prod_le_dedekindZetaR`) to an
equality, at every prime including the dyadic and ramified ones.

**`tendsto_relLR`:** $L(\sigma, \chi_{E/F}) \to \rho_E/\rho_F$ as $\sigma \to 1^+$, $\rho$ = `dedekindZeta_residue` (Mathlib's
residue $2^{r_1}(2\pi)^{r_2}hR/(w\sqrt{|d|})$). The explicit form for CM extensions is `RelativeCNF.lean`.

Sources: Neukirch, *Algebraic Number Theory*, Ch. VII §5 (Dedekind zeta, Euler product) [unverified locator];
Washington, *Introduction to Cyclotomic Fields*, Ch. 4, §4.3 ($\zeta_K = \prod_\chi L(s,\chi)$) [unverified locator].
-/

open NumberField IsDedekindDomain QuadFormsKB.NFEuler Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-! ### The prime of $F$ below a prime of $E$ -/

variable (F) in
/-- **The prime of $F$ below $\mathfrak P$:** $\mathfrak P \cap \mathcal O_F$ (Mathlib's `Ideal.under`), a nonzero prime of
$\mathcal O_F$. -/
def below (𝔓 : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) :=
  ⟨𝔓.asIdeal.under (𝓞 F), Ideal.IsPrime.under (𝓞 F) 𝔓.asIdeal, Ideal.under_ne_bot (𝓞 F) 𝔓.ne_bot⟩

/-- **The primes of $E$ over $\mathfrak p$**, two ways: the nonzero primes $\mathfrak P$ of $\mathcal O_E$ with
`below F 𝔓 = 𝔭`, and Mathlib's `Ideal.primesOver 𝔭 𝒪_E`. -/
def fiberEquiv (𝔭 : HeightOneSpectrum (𝓞 F)) :
    {𝔓 : HeightOneSpectrum (𝓞 E) // below F 𝔓 = 𝔭} ≃ 𝔭.asIdeal.primesOver (𝓞 E) where
  toFun 𝔓 := ⟨𝔓.1.asIdeal, 𝔓.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal 𝔓.2).symm⟩⟩
  invFun P := ⟨⟨P.1, P.2.1, by
      have := P.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P.1⟩,
    HeightOneSpectrum.ext (P.2.2.over.symm)⟩
  left_inv 𝔓 := by ext; rfl
  right_inv P := by ext; rfl

instance (𝔭 : HeightOneSpectrum (𝓞 F)) : Fintype {𝔓 : HeightOneSpectrum (𝓞 E) // below F 𝔓 = 𝔭} :=
  Fintype.ofEquiv _ (fiberEquiv 𝔭).symm

/-! ### The $L$-function of $\chi_{E/F}$ as an Euler product -/

variable (F E) in
/-- **The $L$-function of the splitting character** (real argument):
$$L(\sigma, \chi_{E/F}) = \prod_{\mathfrak p}\big(1 - \chi_{E/F}(\mathfrak p)\,N\mathfrak p^{-\sigma}\big)^{-1},$$
the product over all nonzero primes $\mathfrak p$ of $\mathcal O_F$ (`tprod`; it converges absolutely for $\sigma > 1$ when
$[E:F] = 2$, `hasProd_relLR`). -/
def relLR (σ : ℝ) : ℝ :=
  ∏' 𝔭 : HeightOneSpectrum (𝓞 F), (1 - (relChar E 𝔭 : ℝ) * (normP 𝔭 : ℝ) ^ (-σ))⁻¹

/-- **Absolute convergence of the Euler product of $L(\sigma, \chi_{E/F})$** for $\sigma > 1$. -/
theorem hasProd_relLR (hdeg : Module.finrank F E = 2) {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 F) => (1 - (relChar E 𝔭 : ℝ) * (normP 𝔭 : ℝ) ^ (-σ))⁻¹)
      (relLR F E σ) :=
  (multipliable_of_abs_sub_one_le _ (C := 2) hσ (Eventually.of_forall fun 𝔭 =>
    QTwist.abs_lfac_sub_one_le 𝔭 hσ.le (abs_relChar_le_one hdeg 𝔭))).hasProd

/-- **The Euler product of $\zeta_E$ grouped by the primes of $F$:**
$\zeta_E(\sigma) = \prod_{\mathfrak p}\prod_{\mathfrak P \mid \mathfrak p}(1 - N\mathfrak P^{-\sigma})^{-1}$ for $\sigma > 1$. -/
theorem hasProd_dedekindZeta_fiber {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 F) =>
      ∏ P : 𝔭.asIdeal.primesOver (𝓞 E), (1 - (Ideal.absNorm P.1 : ℝ) ^ (-σ))⁻¹) (dedekindZetaR E σ) := by
  have h0 := hasProd_dedekindZeta (F := E) hσ
  let e := Equiv.sigmaFiberEquiv (below F (E := E))
  have h2 := (e.hasProd_iff).mpr h0
  refine h2.sigma (fun 𝔭 => ?_)
  convert hasProd_fintype _ using 1
  exact (Fintype.prod_equiv (fiberEquiv 𝔭) _ _ (fun _ => rfl)).symm

/-- **$\zeta_E(\sigma) = \zeta_F(\sigma)\,L(\sigma, \chi_{E/F})$ for real $\sigma > 1$** ($[E:F] = 2$; $\zeta$ = Mathlib's
`dedekindZeta`, real part `dedekindZetaR`). *Proof:* `hasProd_dedekindZeta_fiber` and the local factor identity
`localFactor_eq` at every prime of $F$. -/
@[kb "neukirch1999" "Ch. VII §5 [unverified]"]
theorem dedekindZetaR_eq_mul (hdeg : Module.finrank F E = 2) {σ : ℝ} (hσ : 1 < σ) :
    dedekindZetaR E σ = dedekindZetaR F σ * relLR F E σ := by
  have h1 := hasProd_dedekindZeta_fiber (F := F) (E := E) hσ
  have h2 := (hasProd_dedekindZeta (F := F) hσ).mul (hasProd_relLR hdeg hσ)
  refine h1.unique (h2.congr_fun fun 𝔭 => ?_)
  exact localFactor_eq hdeg 𝔭 σ

/-- **The complex form**, at real $s > 1$: $\zeta_E(s) = \zeta_F(s)\,L(s, \chi_{E/F})$ with Mathlib's `dedekindZeta`. -/
theorem dedekindZeta_eq_mul (hdeg : Module.finrank F E = 2) {σ : ℝ} (hσ : 1 < σ) :
    dedekindZeta E σ = dedekindZeta F σ * (relLR F E σ : ℂ) := by
  rw [dedekindZeta_ofReal hσ, dedekindZeta_ofReal hσ, dedekindZetaR_eq_mul hdeg hσ]
  push_cast; rfl

theorem relLR_pos (hdeg : Module.finrank F E = 2) {σ : ℝ} (hσ : 1 < σ) : 0 < relLR F E σ := by
  have hF : 1 ≤ dedekindZetaR F σ := one_le_dedekindZetaR hσ
  have hE : 1 ≤ dedekindZetaR E σ := one_le_dedekindZetaR hσ
  rw [dedekindZetaR_eq_mul hdeg hσ] at hE
  by_contra h
  push Not at h
  nlinarith

/-! ### The value at $s = 1$ -/

/-- **$L(\sigma, \chi_{E/F}) \to \rho_E/\rho_F$ as $\sigma \to 1^+$**, $\rho_K$ = `dedekindZeta_residue K`
$= 2^{r_1(K)}(2\pi)^{r_2(K)}h_KR_K/(w_K\sqrt{|d_K|})$ (Mathlib's class number formula). In particular the Euler product
$L(\sigma,\chi_{E/F})$ has a finite nonzero limit at $1$: $\chi_{E/F}$ is "nontrivial" (`QTwist.tendsto_mul_LFunction_zero` is the weaker statement $(\sigma - 1)L(\sigma,\chi) \to 0$). -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 [unverified]"]
theorem tendsto_relLR (hdeg : Module.finrank F E = 2) :
    Tendsto (relLR F E) (𝓝[>] 1) (𝓝 (dedekindZeta_residue E / dedekindZeta_residue F)) := by
  have hE := GlobalZeta.tendsto_mul_dedekindZetaR_one_add (F := E)
  have hF := GlobalZeta.tendsto_mul_dedekindZetaR_one_add (F := F)
  have h0 : Tendsto (fun s : ℝ => relLR F E (1 + s)) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue E / dedekindZeta_residue F)) := by
    refine (hE.div hF (dedekindZeta_residue_pos F).ne').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have h1 : (1 : ℝ) < 1 + s := by linarith
    have hz : dedekindZetaR F (1 + s) ≠ 0 := by
      have := one_le_dedekindZetaR (F := F) h1; linarith
    show s * dedekindZetaR E (1 + s) / (s * dedekindZetaR F (1 + s)) = relLR F E (1 + s)
    rw [dedekindZetaR_eq_mul hdeg h1]
    field_simp
  have hshift : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · simp only [Set.mem_Ioi] at hs ⊢; linarith
  refine (h0.comp hshift).congr fun s => ?_
  simp only [Function.comp_apply, add_sub_cancel]

end QuadFormsKB.Binary.Rel
