import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Analysis.NFLFunctions
import QuadFormsKB.Binary.RelativeLFactor

/-!
# The $\chi$-regularized Euler product and the natural order

**Layer:** functions on the nonzero primes of $\mathcal O_F$, $F$ a number field (`HeightOneSpectrum (𝓞 F)`), with
$N\mathfrak p$ = `normP`. This file fixes the product convention for Siegel's formula in rank $3$: the rank-3 local densities $\beta_\mathfrak p = 1 + \chi(\mathfrak p)/N\mathfrak p$
(at good $\mathfrak p$) are **not** unconditionally multipliable, so Mathlib's `tprod` of them is junk.

**Definitions.**
* `normOrder F`: the primes ordered by norm, as a Mathlib `SummationFilter` (partial products over
  $\{N\mathfrak p \le X\}$). It is `LeAtTop` (`normOrder_le_atTop`), so it agrees with `tprod` on unconditionally
  convergent products (`HasProd.normOrder`), and `HasProd f P (normOrder F)` is the repository's
  `IsEulerProductValueNF f P` (`hasProd_normOrder_iff`).
* `LOne χ` $= L_F(1,\chi) := \lim_{s\to1^+}\prod_\mathfrak p(1-\chi(\mathfrak p)N\mathfrak p^{-s})^{-1}$ (`limUnder`; `HasLOne χ c`
  says the limit exists and equals $c$).
* `regProd χ e f` $:= L_F(1,\chi)^e\cdot\prod_\mathfrak p f(\mathfrak p)\,(1-\chi(\mathfrak p)/N\mathfrak p)^e$ (`tprod`; meant for
  $f$ with $\prod f\,(1-\chi/N)^e$ absolutely convergent).

**Results (all proved).**
* `hasLOne_relChar`: for a quadratic extension $E/F$, $L_F(1,\chi_{E/F}) = \rho_E/\rho_F > 0$ exists ($\zeta_E = \zeta_F\,L(\cdot,\chi_{E/F})$, `Binary.Rel.tendsto_relLR`); `HasLOne.congr_finite` and `exists_hasLOne_of_almost_relChar`:
  the same for every $\chi$ that agrees with $\chi_{E/F}$ outside a finite set (with an explicit finite correction factor).
* `regProd_zero` ($e = 0$: the plain `tprod`), `regProd_zero_char` ($\chi = 0$: the plain `tprod`),
  `regProd_eq_of_hasProd` (**agreement**: if $\prod(1-\chi/N)^{-1}$ converges unconditionally to $L(1,\chi) \ne 0$ and
  $\prod f$ converges unconditionally, `regProd χ e f` is the plain product), `regProd_mul` (exponents add).
* `NaturalOrderEulerOne χ` (**named input** over $F$, a prime ideal theorem for $\chi$ in the form
  $\prod_{N\mathfrak p \le X}(1-\chi(\mathfrak p)/N\mathfrak p)^{-1} \to L_F(1,\chi)$) and `hasProd_normOrder_regProd`: under it, the
  natural-order product of $f$ is `regProd χ 1 f` whenever $\prod f\,(1-\chi/N)$ converges absolutely (the rank-3
  natural-order reading of Siegel/Hanke). Over $\mathbb Q$ the input is a theorem (`EulerOne.tendsto_prod_primesBelow`).

-/

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.RegProd

open NFEuler

variable {F : Type} [Field F] [NumberField F]

/-! ### The natural order on the primes -/

variable (F) in
/-- **The natural order on the primes of $F$** (Siegel's and Hanke's reading of $\prod_\mathfrak p$ in rank $3$): the
summation filter whose partial products are $\prod_{N\mathfrak p \le X}$, $X \to \infty$ (`primesNormLe`). -/
@[kb "hanke2004" "(5.3), p. 368 (natural order, n = 3)"]
def normOrder : SummationFilter (HeightOneSpectrum (𝓞 F)) where
  filter := atTop.map (primesNormLe F)

theorem normOrder_le_atTop : (normOrder F).filter ≤ atTop := tendsto_primesNormLe

instance : (normOrder F).LeAtTop := ⟨normOrder_le_atTop⟩

instance : (normOrder F).NeBot := ⟨Filter.map_neBot⟩

/-- `HasProd` for the natural order is the repository's `IsEulerProductValueNF`. -/
theorem hasProd_normOrder_iff {f : HeightOneSpectrum (𝓞 F) → ℝ} {P : ℝ} :
    HasProd f P (normOrder F) ↔ IsEulerProductValueNF f P :=
  tendsto_map'_iff

/-- An unconditionally convergent product has the same value in the natural order. -/
theorem _root_.HasProd.normOrder {f : HeightOneSpectrum (𝓞 F) → ℝ} {P : ℝ} (h : HasProd f P) :
    HasProd f P (normOrder F) :=
  Tendsto.mono_left h normOrder_le_atTop

/-! ### $L_F(1, \chi)$ -/

/-- **$L_F(s,\chi) \to c$ as $s \to 1^+$** (real $s$; $L_F(s,\chi)$ = `LFunctionNF`, the Euler product). -/
def HasLOne (χ : HeightOneSpectrum (𝓞 F) → ℝ) (c : ℝ) : Prop :=
  Tendsto (LFunctionNF χ) (𝓝[>] 1) (𝓝 c)

/-- **$L_F(1,\chi) := \lim_{s\to1^+}L_F(s,\chi)$** (`limUnder`; a junk value when the limit does not exist). For a
quadratic character $\chi = \chi_{E/F}$, up to finitely many primes, the limit exists and is positive
(`exists_hasLOne_of_almost_relChar`). -/
@[kb "neukirch1999" "Ch. VII §5 (L(1, χ) as a limit) [unverified]"]
def LOne (χ : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  limUnder (𝓝[>] (1 : ℝ)) (LFunctionNF χ)

theorem HasLOne.lOne_eq {χ : HeightOneSpectrum (𝓞 F) → ℝ} {c : ℝ} (h : HasLOne χ c) : LOne χ = c :=
  h.limUnder_eq

/-- $L_F(1, 0) = 1$. -/
theorem LOne_zero : LOne (fun _ : HeightOneSpectrum (𝓞 F) => (0 : ℝ)) = 1 := by
  refine HasLOne.lOne_eq ?_
  have : LFunctionNF (fun _ : HeightOneSpectrum (𝓞 F) => (0 : ℝ)) = fun _ => 1 := by
    funext s; simp [LFunctionNF, lFactor]
  rw [HasLOne, this]
  exact tendsto_const_nhds

/-- For $s \ge 1$ and $|c| \le 1$: $0 < 1 - c\,N\mathfrak p^{-s}$. -/
theorem one_sub_mul_rpow_pos {c s : ℝ} (hc : |c| ≤ 1) (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    0 < 1 - c * (normP v : ℝ) ^ (-s) := by
  obtain ⟨h0, h1⟩ := rpow_neg_mem (two_le_normP v) hs
  exact one_sub_mul_pos hc h0 h1

/-- $0 < 1 - c/N\mathfrak p$ for $|c| \le 1$. -/
theorem one_sub_div_pos {c : ℝ} (hc : |c| ≤ 1) (v : HeightOneSpectrum (𝓞 F)) :
    0 < 1 - c / (normP v : ℝ) := by
  have h := one_sub_mul_rpow_pos hc le_rfl v
  rwa [Real.rpow_neg_one, ← div_eq_mul_inv] at h

theorem lFactor_pos_of_one_le {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) {s : ℝ} (hs : 1 ≤ s)
    (v : HeightOneSpectrum (𝓞 F)) : 0 < lFactor χ s v :=
  inv_pos.mpr (one_sub_mul_rpow_pos (hχ v) hs v)

theorem continuousAt_lFactor {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) : ContinuousAt (fun s => lFactor χ s v) 1 := by
  have hN : (normP v : ℝ) ≠ 0 := by have := two_le_normP v; positivity
  have hr : ContinuousAt (fun s : ℝ => (normP v : ℝ) ^ (-s)) 1 :=
    (Real.continuousAt_const_rpow hN).comp continuous_neg.continuousAt
  exact (continuousAt_const.sub (continuousAt_const.mul hr)).inv₀
    (one_sub_mul_rpow_pos (hχ v) le_rfl v).ne'

/-- **Changing $\chi$ at finitely many primes** changes $L_F(1,\chi)$ by the explicit finite factor
$\prod_{\mathfrak p \in S}\ell_\mathfrak p(\chi)/\ell_\mathfrak p(\chi')$, $\ell_\mathfrak p = (1-\chi(\mathfrak p)/N\mathfrak p)^{-1}$. -/
theorem HasLOne.congr_finite {χ χ' : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (hχ' : ∀ v, |χ' v| ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, χ v = χ' v) {c : ℝ}
    (h : HasLOne χ' c) : HasLOne χ (c * ∏ v ∈ S, lFactor χ 1 v / lFactor χ' 1 v) := by
  have heq : ∀ s : ℝ, 1 < s →
      LFunctionNF χ' s * ∏ v ∈ S, lFactor χ s v / lFactor χ' s v = LFunctionNF χ s := by
    intro s hs
    set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => lFactor χ s v / lFactor χ' s v with hr
    have h3 : HasProd r (∏ v ∈ S, r v) := hasProd_prod_of_ne_finset_one fun v hv => by
      simp only [hr, lFactor, hS v hv]
      exact div_self (lFactor_pos hχ' hs v).ne'
    have h4 := (hasProd_LFunctionNF hχ' hs).mul h3
    refine (h4.congr_fun fun v => ?_).unique (hasProd_LFunctionNF hχ hs)
    simp only [hr]
    exact (mul_div_cancel₀ _ (lFactor_pos hχ' hs v).ne').symm
  have hcont : Tendsto (fun s => ∏ v ∈ S, lFactor χ s v / lFactor χ' s v) (𝓝[>] 1)
      (𝓝 (∏ v ∈ S, lFactor χ 1 v / lFactor χ' 1 v)) := by
    refine tendsto_finsetProd _ fun v _ => ?_
    exact (((continuousAt_lFactor hχ v).div (continuousAt_lFactor hχ' v)
      (lFactor_pos_of_one_le hχ' le_rfl v).ne').tendsto).mono_left nhdsWithin_le_nhds
  refine (h.mul hcont).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact heq s hs

open Binary.Rel in
/-- **$L_F(1,\chi_{E/F}) = \rho_E/\rho_F$** for a quadratic extension $E/F$ (`Binary.Rel.tendsto_relLR`, from
$\zeta_E = \zeta_F\,L(\cdot,\chi_{E/F})$ and the residues of the Dedekind zeta functions). -/
theorem hasLOne_relChar {E : Type} [Field E] [NumberField E] [Algebra F E] (hdeg : Module.finrank F E = 2) :
    HasLOne (fun v : HeightOneSpectrum (𝓞 F) => (relChar E v : ℝ))
      (dedekindZeta_residue E / dedekindZeta_residue F) :=
  tendsto_relLR hdeg

/-- **$\chi$ is $\chi_{E/F}$ up to finitely many primes** (a condition; for the ternary character $\chi_m$ the field
is $E = F(\sqrt{-m\,d_Q})$, and the identification is left to a later step). -/
def IsAlmostRelChar (χ : HeightOneSpectrum (𝓞 F) → ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E] : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, χ v = (Binary.Rel.relChar E v : ℝ)

/-- **Existence of $L_F(1,\chi)$ for quadratic $\chi$:** if $|\chi| \le 1$ and $\chi = \chi_{E/F}$ outside a finite set
($[E:F] = 2$), then $L_F(s,\chi)$ has a positive limit at $s = 1^+$. -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 (L(1, χ_{E/F}) = ρ_E/ρ_F) [unverified]"]
theorem exists_hasLOne_of_almost_relChar {E : Type} [Field E] [NumberField E] [Algebra F E]
    (hdeg : Module.finrank F E = 2) {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (h : IsAlmostRelChar χ E) : 0 < LOne χ ∧ HasLOne χ (LOne χ) := by
  obtain ⟨S, hS⟩ := h
  have hrel : ∀ v : HeightOneSpectrum (𝓞 F), |(Binary.Rel.relChar E v : ℝ)| ≤ 1 := fun v => by
    have := Binary.Rel.abs_relChar_le_one hdeg v
    exact_mod_cast this
  have hL := (hasLOne_relChar hdeg).congr_finite hχ hrel S hS
  have hpos : 0 < dedekindZeta_residue E / dedekindZeta_residue F * ∏ v ∈ S,
      lFactor χ 1 v / lFactor (fun v => (Binary.Rel.relChar E v : ℝ)) 1 v :=
    mul_pos (div_pos (dedekindZeta_residue_pos E) (dedekindZeta_residue_pos F))
      (Finset.prod_pos fun v _ => div_pos (lFactor_pos_of_one_le hχ le_rfl v)
        (lFactor_pos_of_one_le hrel le_rfl v))
  rw [hL.lOne_eq]
  exact ⟨hpos, hL⟩

/-! ### The regularized product -/

/-- **The $\chi$-regularized product** (the rank-3 convention):
$$\mathrm{regProd}(\chi, e, f) = L_F(1,\chi)^e\cdot\prod_\mathfrak p f(\mathfrak p)\,\bigl(1-\chi(\mathfrak p)N\mathfrak p^{-1}\bigr)^e,$$
the product being Mathlib's `tprod`. *Use* when $\prod_\mathfrak p f\,(1-\chi/N)^e$ converges absolutely (rank-3
$\beta_\mathfrak p$ with $e = 1$, rank-2 $\alpha_\mathfrak p$ with $e = -1$); it is then the natural-order product of $f$ given
`NaturalOrderEulerOne χ` (`hasProd_normOrder_regProd`). Changing $\chi$ to $0$ at finitely many primes does not change
the value (both $L_F(1,\chi)$ and the correction factors move by the same finite factor), so $\chi$ may be taken to vanish
at the bad primes. -/
@[kb "siegel1935" "Hauptsatz, n = 3 (regularized Euler product) [unverified]"]
def regProd (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ) (f : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  LOne χ ^ e * ∏' v, f v * (1 - χ v / (normP v : ℝ)) ^ e

theorem regProd_zero (χ f : HeightOneSpectrum (𝓞 F) → ℝ) : regProd χ 0 f = ∏' v, f v := by
  simp [regProd]

/-- **The trivial character:** `regProd 0 e f` is the plain product. -/
theorem regProd_zero_char (e : ℤ) (f : HeightOneSpectrum (𝓞 F) → ℝ) :
    regProd (fun _ => (0 : ℝ)) e f = ∏' v, f v := by
  simp [regProd, LOne_zero]

/-- Integer powers of a convergent product with a nonzero value (any summation filter). -/
theorem hasProd_zpow {ι : Type*} {L : SummationFilter ι} {g : ι → ℝ} {c : ℝ} (h : HasProd g c L) (hc : c ≠ 0)
    (e : ℤ) : HasProd (fun i => g i ^ e) (c ^ e) L := by
  have := h.zpow₀ e (Or.inl hc)
  unfold HasProd
  simpa only [Finset.prod_zpow] using this

/-- **Agreement with the plain product:** if $\prod_\mathfrak p(1-\chi(\mathfrak p)/N\mathfrak p)^{-1}$ converges unconditionally
to $L_F(1,\chi) \ne 0$ and $\prod f$ converges unconditionally to $P$, then `regProd χ e f = P` for every $e$. So the
regularization never changes a product that already converges absolutely. -/
theorem regProd_eq_of_hasProd {χ f : HeightOneSpectrum (𝓞 F) → ℝ} {P : ℝ}
    (hL : HasProd (fun v => (1 - χ v / (normP v : ℝ))⁻¹) (LOne χ)) (hL0 : LOne χ ≠ 0) (hf : HasProd f P)
    (e : ℤ) : regProd χ e f = P := by
  have h1 := hasProd_zpow hL hL0 (-e)
  simp only [inv_zpow', neg_neg] at h1
  rw [regProd, (hf.mul h1).tprod_eq, zpow_neg]
  field_simp

/-- **Exponents add:** $\mathrm{regProd}(\chi,e_1,f)\,\mathrm{regProd}(\chi,e_2,g) = \mathrm{regProd}(\chi,e_1+e_2,fg)$ when
$|\chi| \le 1$, $L_F(1,\chi) \ne 0$ and both corrected products converge (unconditionally). -/
theorem regProd_mul {χ f g : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) (hL0 : LOne χ ≠ 0) {e₁ e₂ : ℤ}
    (hf : Multipliable fun v => f v * (1 - χ v / (normP v : ℝ)) ^ e₁)
    (hg : Multipliable fun v => g v * (1 - χ v / (normP v : ℝ)) ^ e₂) :
    regProd χ e₁ f * regProd χ e₂ g = regProd χ (e₁ + e₂) (fun v => f v * g v) := by
  have h := (hf.hasProd.mul hg.hasProd).tprod_eq
  have e : (fun v => f v * g v * (1 - χ v / (normP v : ℝ)) ^ (e₁ + e₂)) =
      (fun v => f v * (1 - χ v / (normP v : ℝ)) ^ e₁) * (fun v => g v * (1 - χ v / (normP v : ℝ)) ^ e₂) := by
    funext v
    simp only [Pi.mul_apply, zpow_add₀ (one_sub_div_pos (hχ v) v).ne']
    ring
  rw [regProd, regProd, regProd, e, Pi.mul_def, h, zpow_add₀ hL0]
  ring

/-! ### The natural order: a named input over $F$ -/

/-- **Input: the Euler product of $L_F(1,\chi)$ converges in the natural order** to $L_F(1,\chi)$:
$$\prod_{N\mathfrak p \le X}\bigl(1-\chi(\mathfrak p)N\mathfrak p^{-1}\bigr)^{-1} \longrightarrow L_F(1,\chi)\qquad(X \to \infty).$$

Field:
- `hasProd`: the displayed limit, as `HasProd … (normOrder F)`.

*Status.* For a nontrivial quadratic (Hecke) character this follows from the prime ideal theorem for $\chi$ with an error
term (Landau; Neukirch, Ch. VII [unverified]), which is in neither Mathlib nor the repository. Over $\mathbb Q$
it is a theorem (`EulerOne.tendsto_prod_primesBelow`, any nontrivial Dirichlet character).

*Independence (hypothesis hygiene):* it concerns the character $\chi$ alone (no quadratic form, no local density, no
class or mass); it is used only to identify the natural-order reading of $\prod_\mathfrak p\beta_\mathfrak p$ with the
regularized definition (`hasProd_normOrder_regProd`), never to prove Siegel's formula itself. It is
`IsEulerProductValueNF (lFactor χ 1) (LOne χ)` (`naturalOrderEulerOne_iff`). -/
@[kb "neukirch1999" "Ch. VII §13 (prime ideal theorem for χ) [unverified]"]
structure NaturalOrderEulerOne (χ : HeightOneSpectrum (𝓞 F) → ℝ) : Prop where
  hasProd : HasProd (fun v => (1 - χ v / (normP v : ℝ))⁻¹) (LOne χ) (normOrder F)

theorem naturalOrderEulerOne_iff (χ : HeightOneSpectrum (𝓞 F) → ℝ) :
    NaturalOrderEulerOne χ ↔ IsEulerProductValueNF (lFactor χ 1) (LOne χ) := by
  have e : (fun v => (1 - χ v / (normP v : ℝ))⁻¹) = lFactor χ 1 := by
    funext v; simp only [lFactor, Real.rpow_neg_one, div_eq_mul_inv]
  rw [← hasProd_normOrder_iff, ← e]
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- **The natural-order product is the regularized product:** given `NaturalOrderEulerOne χ`, $|\chi| \le 1$, and
$\prod_\mathfrak p f(\mathfrak p)(1-\chi(\mathfrak p)/N\mathfrak p) = P$ unconditionally,
$$\prod_{N\mathfrak p \le X}f(\mathfrak p) \longrightarrow \mathrm{regProd}(\chi, 1, f) = L_F(1,\chi)\cdot P.$$ -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3: natural order = L(1, χ) × absolutely convergent product)"]
theorem hasProd_normOrder_regProd {χ f : HeightOneSpectrum (𝓞 F) → ℝ} (hN : NaturalOrderEulerOne χ)
    (hχ : ∀ v, |χ v| ≤ 1) {P : ℝ} (hf : HasProd (fun v => f v * (1 - χ v / (normP v : ℝ))) P) :
    HasProd f (regProd χ 1 f) (normOrder F) := by
  have h := hf.normOrder.mul hN.hasProd
  have e : regProd χ 1 f = P * LOne χ := by
    simp only [regProd, zpow_one, hf.tprod_eq]; ring
  rw [e]
  refine h.congr_fun fun v => ?_
  rw [mul_assoc, mul_inv_cancel₀ (one_sub_div_pos (hχ v) v).ne', mul_one]

end QuadFormsKB.RegProd
