import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTauTwoUncond
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFinal
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFacts

/-!
# $\tau(SO(V))$ for quadratic spaces of dimension $2$

**Layer:** number fields. $F$ is a number field, $V$ an $F$-vector space with $\dim_F V = 2$, $Q$ a nondegenerate quadratic
form on $V$ (Mathlib's `QuadraticForm F V`; nondegenerate: `(QuadraticMap.polarBilin Q).Nondegenerate`). This completes
`SpaceHeadlines.lean` (dimensions $1$ and $\ge3$) in dimension $2$, where Weil's Tamagawa measures carry convergence
factors: `muTamBin` (factors $L_v(1,\chi_E)$, $E$ the discriminant field) for anisotropic $V$, and `muTamIso`
(factors $1 - N(v)^{-1}$, norm-one shell) for isotropic $V$.

An integral model $(b, d, Q_0)$ of $(V, Q)$ (`IntegralModel`) has a form $Q_0$ in $\dim_F V$ variables, while the binary
measures are defined for forms in $2$ variables. **`IntegralModel.form₂`** is $Q_0$ read in $2$ variables along
$\dim_F V = 2$: the same coefficients, $Q_{0,ij}$ for $0\le i\le j\le1$ (`form₂_coeff`).

**Proves** (unconditional)
* `IntegralModel.anisotropicF_form₂`, `IntegralModel.isotropicF_form₂`: $Q_0\otimes F$ is anisotropic (isotropic) iff
  $(V, Q)$ is (`QuadraticMap.Anisotropic`);
* **`tauTwo_space_binary`**: for anisotropic $(V, Q)$, every integral model has $\tau = 2$ for `muTamBin`, for every
  discriminant field (`TauTwoBinaryAdelic`), from `tauTwoBinaryAll_uncond`;
* **`tauOne_space_binary_isotropic`**: for isotropic $(V, Q)$, every integral model has $\tau = 1$ for `muTamIso`, for
  every isotropic vector (`TauOneIsotropic`, `tauIso`), from `tauOne_binary_isotropic_uncond`.
-/

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

namespace IntegralModel

variable {Q : QuadraticForm F V} (M : IntegralModel Q)

/-- **The form of an integral model in $2$ variables** ($\dim_F V = 2$): $Q_0$ transported along
$\dim_F V = 2$; its coefficients are those of $Q_0$ (`form₂_coeff`). -/
def form₂ (hV : Module.finrank F V = 2) : QuadForm (𝓞 F) 2 := hV ▸ M.form

/-- The coefficients of `form₂` are those of the model's form. -/
theorem form₂_coeff (hV : Module.finrank F V = 2) (i j : Fin 2) :
    (M.form₂ hV).coeff i j = M.form.coeff (Fin.cast hV.symm i) (Fin.cast hV.symm j) := by
  have key : ∀ (n : ℕ) (h : n = 2) (Q₀ : QuadForm (𝓞 F) n) (i j : Fin 2),
      (h ▸ Q₀ : QuadForm (𝓞 F) 2).coeff i j = Q₀.coeff (Fin.cast h.symm i) (Fin.cast h.symm j) := by
    intro n h Q₀ i j
    subst h
    rfl
  exact key _ hV M.form i j

/-- `form₂` is nondegenerate when $Q$ is. -/
theorem nondegenerate_form₂ (hV : Module.finrank F V = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (M.form₂ hV).Nondegenerate := by
  have key : ∀ (n : ℕ) (h : n = 2) (Q₀ : QuadForm (𝓞 F) n), Q₀.Nondegenerate →
      (h ▸ Q₀ : QuadForm (𝓞 F) 2).Nondegenerate := by
    intro n h Q₀ hn
    subst h
    exact hn
  exact key _ hV M.form (M.nondegenerate hQ)

/-- **$Q_0\otimes F$ is anisotropic iff $(V, Q)$ is.** -/
theorem anisotropicF_form₂ (hV : Module.finrank F V = 2) : AnisotropicF (M.form₂ hV) ↔ Q.Anisotropic := by
  have key : ∀ (n : ℕ) (h : n = 2) (Q₀ : QuadForm (𝓞 F) n),
      AnisotropicF (h ▸ Q₀ : QuadForm (𝓞 F) 2) ↔ AnisotropicF Q₀ := by
    intro n h Q₀
    subst h
    exact Iff.rfl
  rw [form₂, key _ hV M.form]
  constructor
  · intro h x hx
    have h1 : qF M.form (M.basis.equivFun x) = 0 := by
      show (M.form.map (algebraMap (𝓞 F) F)).eval (M.basis.equivFun x) = 0
      rw [M.eval_apply, LinearEquiv.symm_apply_apply, hx, mul_zero]
    have := h _ h1
    simpa using this
  · intro h w hw
    -- (second direction)
    have h1 : Q (M.basis.equivFun.symm w) = 0 := by
      have : (M.scale : F) * Q (M.basis.equivFun.symm w) = 0 := by
        rw [← M.eval_apply]; exact hw
      exact (mul_eq_zero.mp this).resolve_left M.scale_ne_zero'
    have := congrArg M.basis.equivFun (h _ h1)
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this

/-- **$Q_0\otimes F$ is isotropic iff $(V, Q)$ is not anisotropic.** -/
theorem isotropicF_form₂ (hV : Module.finrank F V = 2) : IsotropicF (M.form₂ hV) ↔ ¬ Q.Anisotropic := by
  rw [isotropicF_iff_not_anisotropicF, anisotropicF_form₂]

end IntegralModel

/-- **Weil's $\tau(SO(V)) = 2$ for anisotropic quadratic spaces of dimension $2$** (Ono's $\tau(R^1_{E/F}\mathbb G_m) = 2$):
for every number field $F$, every $F$-vector space $V$ with $\dim_F V = 2$ and every nondegenerate anisotropic quadratic
form $Q$ on $V$, $(V, Q)$ has an integral model, and for every integral model $(b, d, Q_0)$ the form $Q_0$ (in $2$
variables, `form₂`) is nondegenerate and anisotropic over $F$, and
$\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu^{\chi_E}_{\mathrm{Tam}}) = 2$ for every discriminant field $E$ of $Q_0$
(`TauTwoBinaryAdelic`; `muTamBin`, convergence factors $L_v(1,\chi_E)$). **Unconditional**: from `tauTwoBinaryAll_uncond`. -/
@[kb "weil1982" "§2.4, p. 23; Thm 3.2.1, p. 43; ono1963 (τ of the norm-one torus) [unverified]"]
theorem tauTwo_space_binary (hV : Module.finrank F V = 2) (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hA : Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      AnisotropicF (M.form₂ hV) ∧ TauTwoBinaryAdelic (M.form₂ hV) hM := by
  refine ⟨integralModel_nonempty Q, fun M => ?_⟩
  have hM := M.nondegenerate_form₂ hV hQ
  have hA' := (M.anisotropicF_form₂ hV).mpr hA
  exact ⟨hM, hA', tauTwoBinaryAll_uncond F _ hM hA'⟩

/-- **$\tau(SO(V)) = 1$ for isotropic quadratic spaces of dimension $2$** (Ono's $\tau(\mathbb G_m) = 1$): for every number
field $F$, every $F$-vector space $V$ with $\dim_F V = 2$ and every nondegenerate isotropic quadratic form $Q$ on $V$ (not
`QuadraticMap.Anisotropic`), $(V, Q)$ has an integral model, and for every integral model $(b, d, Q_0)$ the form $Q_0$ (in
$2$ variables, `form₂`) is nondegenerate and isotropic over $F$, and for every isotropic vector $e$ of $Q_0$,
$\tau = \operatorname{covol}(SO(V)(F), SO(V)(\mathbb A)^1) = 1$ for Weil's measure with the convergence factors
$1 - N(v)^{-1}$ restricted to the norm-one shell (`TauOneIsotropic`, `tauIso`, `muTamIso`). **Unconditional**: from
`tauOne_binary_isotropic_uncond`. -/
@[kb "weil1982" "§2.4, §3.1 [unverified] (τ(G_m) = 1); ono1963 [unverified] (τ of tori)"]
theorem tauOne_space_binary_isotropic (hV : Module.finrank F V = 2) (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hI : ¬ Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      IsotropicF (M.form₂ hV) ∧ TauOneIsotropic (M.form₂ hV) hM := by
  refine ⟨integralModel_nonempty Q, fun M => ?_⟩
  have hM := M.nondegenerate_form₂ hV hQ
  have hI' := (M.isotropicF_form₂ hV).mpr hI
  exact ⟨hM, hI', tauOne_binary_isotropic_uncond F _ hM hI'⟩

end QuadFormsKB.Tamagawa.Measure.Weil
