/-
# Weil's (8) over every number field, every signature, every Schwartz $\Phi_\infty$

**Layer:** global assembly on top of `ZetaResidue.lean`, `SphericalResidue.lean` and the archimedean lemmas of
`ArchTestFn.lean`. Weil 1982, §4.5, (1)–(2), p. 102 and (8), p. 108 (KB-checked locators).

**What is added to `SphericalResidue.lean`.**
1. **Complex places.** At a complex place $w$ the form is $Q_w = \sigma_w(Q)$ on $\mathbb C^n$ (`cplxForm`, $\sigma_w$ = Mathlib's
   `InfinitePlace.embedding`), the absolute value is $|z|_{\mathbb C} = |z|^2$ and the measure is $2^n$ times Lebesgue measure
   ($2\,dx\,dy$ on each coordinate, the self-dual measure for $z \mapsto e^{2\pi i\,\mathrm{Tr}_{\mathbb C/\mathbb R}z}$; Weil §2.1.1 [unverified]
   for the page). The local zeta integral is `cplxZetaAt` $Z_w(s) = \int_{\mathbb C^n}|Q_w(x)|_{\mathbb C}^s\Psi_w(x)\,2^ndx$. Every $\rho \in \mathbb C^\times$
   is a square, and $T(\rho)_{\mathbb C} = \{(x,y) : Q_w(x) = \rho y^2\} \to \{Q_w \ne 0\}$, $(x,y) \mapsto x$, is two-to-one and carries the gauge-form
   measure to $2^ndx$, so Weil's local spherical factor is $Z_w(s,\rho) = 2Z_w(s)$, **independent of $\rho$** (as at a finite place,
   `sphLocal`, and a real place, `sphArchAt`). Hence `sphericalZetaAtNF` $= Z(s,\rho)\cdot\prod_{w\ \mathrm{complex}}2Z_w(s)$.
   The real-places-only residue over a general $F$ is $2^{-r_2}\rho_F\int\Phi$
   (`tendsto_mul_sphericalZeta_zero_real`), the $2^{-r_2}$ coming from $|\Lambda_S| = 2^{|S| + r_1 + r_2}$; the complex
   factors supply $2^{r_2}$.
2. **Any sign of $\Phi_\infty$.** The sandwich needs $\Phi_w \ge 0$. All objects are multilinear in $(\Phi_w)_w$, so writing
   $\Phi_w = \Phi_w^+ - \Phi_w^-$ expands $Z(s)$ and $\int\Phi$ into $2^{r_1+r_2}$ signed terms with nonnegative data (`sel`, `sgn`), each
   summable and with the right residue.
3. **No null-cone hypothesis**: proved for every nondegenerate $Q$ (`ArchTest.ae_realVal_ne_zero_of_nondegenerate`,
   `ae_cplxVal_ne_zero`).

**Headlines.**
* **`tendsto_mul_sphericalZetaNF_zero`** (Weil's (8)): $F$ any number field, $Q$ nondegenerate over $\mathcal O_F$, $n \ge 5$,
  $\Phi_w$ admissible at the real places (`IsArchTestFn`) and $\Psi_w$ admissible at the complex places (`IsArchTestFnC`), any sign:
  $$\lim_{s\to0^+}s\sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) = \rho_F\int_{V(\mathbb A)}\Phi\,dx.$$
* **`tendsto_mul_sphericalZetaNF_zero_schwartz`**: the same for Schwartz $\Phi_w \in \mathcal S(\mathbb R^n)$, $\Psi_w \in \mathcal S(\mathbb C^n)$, unconditional.
* `tendsto_mul_globalZetaNF_zero(_schwartz)`: the residue with the complex places, $n \ge 4$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.ArchTestFn
import QuadFormsKB.Tamagawa.SphericalResidue

open IsDedekindDomain NumberField MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalNF

open scoped Classical

open QuadFormsKB.GlobalZeta QuadFormsKB.SphericalZeta QuadFormsKB.ArchTest QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Signed expansions -/

section Expand

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- $\prod_i(p_i - m_i) = \sum_{\varepsilon\in\{\pm\}^\iota}\operatorname{sgn}(\varepsilon)\prod_i(\varepsilon_i ? p_i : m_i)$. -/
lemma prod_sub_expand (x p m : ι → ℝ) (h : ∀ i, x i = p i - m i) :
    ∏ i, x i = ∑ ε : ι → Bool, (∏ i, if ε i then (1 : ℝ) else -1) * ∏ i, (if ε i then p i else m i) := by
  have hx : ∀ i, x i = ∑ b : Bool, (if b then p i else -m i) := fun i => by
    rw [Fintype.sum_bool, if_pos rfl, if_neg Bool.false_ne_true, h i, sub_eq_add_neg]
  rw [Finset.prod_congr rfl fun i _ => hx i, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases ε i <;> simp

/-- The positive part $\varphi^+ = \max(\varphi, 0)$. -/
def posPart (φ : X → ℝ) : X → ℝ := fun x => max (φ x) 0

/-- The negative part $\varphi^- = \max(-\varphi, 0)$. -/
def negPart (φ : X → ℝ) : X → ℝ := fun x => max (-φ x) 0

lemma posPart_sub_negPart (φ : X → ℝ) (x : X) : posPart φ x - negPart φ x = φ x :=
  max_zero_sub_max_neg_zero_eq_self (φ x)

/-- **The sign selection** $\Phi^\varepsilon_w = \Phi_w^{+}$ if $\varepsilon_w$, else $\Phi_w^-$. -/
def sel (Φ : ι → X → ℝ) (ε : ι → Bool) : ι → X → ℝ := fun w => if ε w then posPart (Φ w) else negPart (Φ w)

/-- $\operatorname{sgn}(\varepsilon) = \prod_w(\pm1)$. -/
def sgn (ε : ι → Bool) : ℝ := ∏ i, if ε i then (1 : ℝ) else -1

lemma sel_nonneg (Φ : ι → X → ℝ) (ε : ι → Bool) (w : ι) (x : X) : 0 ≤ sel Φ ε w x := by
  unfold sel posPart negPart; split_ifs <;> exact le_max_right _ _

/-- **Multilinear expansion**: if each $A_w$ is additive on $\Phi_w = \Phi_w^+ - \Phi_w^-$, then
$\prod_wA_w(\Phi_w) = \sum_\varepsilon\operatorname{sgn}(\varepsilon)\prod_wA_w(\Phi^\varepsilon_w)$. -/
lemma prod_expand (A : ι → (X → ℝ) → ℝ) (Φ : ι → X → ℝ)
    (hA : ∀ i, A i (Φ i) = A i (posPart (Φ i)) - A i (negPart (Φ i))) :
    ∏ i, A i (Φ i) = ∑ ε : ι → Bool, sgn ε * ∏ i, A i (sel Φ ε i) := by
  rw [prod_sub_expand _ _ _ hA]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold sel; split_ifs <;> rfl

end Expand

/-! ### Admissibility of the sign selections at the real places -/

lemma isArchTestFn_sel {Q : QuadForm (𝓞 F) n} {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    (ε : RealPlace F → Bool) : IsArchTestFn Q (sel Φ ε) where
  integrable w := by
    unfold sel posPart negPart; split_ifs
    · exact (hΦ.integrable w).pos_part
    · exact (hΦ.integrable w).neg_part
  integrable_mul w := by
    unfold sel posPart negPart; split_ifs
    · refine (hΦ.integrable_mul w).pos_part.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [mul_max_of_nonneg _ _ (abs_nonneg _), mul_zero]
    · refine (hΦ.integrable_mul w).neg_part.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [mul_max_of_nonneg _ _ (abs_nonneg _), mul_zero, mul_neg]

/-- The positive and negative parts are admissible (the selections with all $\varepsilon_w$ equal). -/
lemma integrable_rpow_mul_posPart {Q : QuadForm (𝓞 F) n} {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : IsArchTestFn Q Φ) (w : RealPlace F) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Integrable fun x => |realVal Q w x| ^ s * posPart (Φ w) x := by
  simpa [sel] using integrable_rpow_mul Q (isArchTestFn_sel hΦ fun _ => true) w hs

lemma integrable_rpow_mul_negPart {Q : QuadForm (𝓞 F) n} {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : IsArchTestFn Q Φ) (w : RealPlace F) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Integrable fun x => |realVal Q w x| ^ s * negPart (Φ w) x := by
  simpa [sel] using integrable_rpow_mul Q (isArchTestFn_sel hΦ fun _ => false) w hs

/-! ### The complex places -/

/-- **The complex places of $F$** (complex infinite places, Mathlib's `InfinitePlace.IsComplex`). -/
abbrev ComplexPlace (F : Type) [Field F] [NumberField F] := {w : InfinitePlace F // w.IsComplex}

/-- **The form $Q_w = \sigma_w(Q)$ at a complex place** $w$ ($\sigma_w$ = `InfinitePlace.embedding`, one of the two conjugate
embeddings; the other gives the conjugate form and the same integrals). -/
def cplxForm (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) : QuadForm ℂ n :=
  Q.map (w.1.embedding.comp (algebraMap (𝓞 F) F))

/-- $Q_w(x)$ for $x \in \mathbb C^n$. -/
def cplxVal (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) (x : Fin n → ℂ) : ℂ := (cplxForm Q w).evalIn ℂ x

lemma continuous_cplxVal (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) : Continuous (cplxVal Q w) := by
  unfold cplxVal QuadForm.evalIn
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop

/-- **The local archimedean zeta integral at a complex place** (Weil 1982, §4.4–4.5, the factor at an infinite place):
$$Z_w(s) = \int_{\mathbb C^n}|Q_w(x)|_{\mathbb C}^s\,\psi(x)\,2^n\,dx,\qquad |z|_{\mathbb C} = |z|^2,$$
$dx$ Lebesgue measure on $\mathbb C^n = \mathbb R^{2n}$ (`volume`), so $2^ndx$ is the self-dual measure ($2\,dx\,dy$ per coordinate). -/
@[kb "weil1982" "§4.5, (1), p. 102 (the factor at an infinite place; complex case)"]
def cplxZetaAt (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) (ψ : (Fin n → ℂ) → ℝ) (s : ℝ) : ℝ :=
  2 ^ n * ∫ x, (‖cplxVal Q w x‖ ^ 2) ^ s * ψ x

/-- **Admissible test functions at the complex places** (a condition on the chosen data): $\Psi_w$ and $|Q_w|_{\mathbb C}\Psi_w$
are Lebesgue integrable on $\mathbb C^n$. Every Schwartz function satisfies it (`isArchTestFnC_schwartz`). -/
structure IsArchTestFnC (Q : QuadForm (𝓞 F) n) (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) : Prop where
  /-- $\Psi_w \in L^1(\mathbb C^n)$. -/
  integrable : ∀ w, Integrable (Ψ w)
  /-- $|Q_w|_{\mathbb C}\,\Psi_w = |Q_w|^2\Psi_w \in L^1(\mathbb C^n)$. -/
  integrable_mul : ∀ w, Integrable fun x => ‖cplxVal Q w x‖ ^ 2 * Ψ w x

/-- The complex form of a nondegenerate $Q$ is nondegenerate. -/
theorem nondegenerate_cplxForm {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (w : ComplexPlace F) :
    (cplxForm Q w).Nondegenerate := by
  set f : 𝓞 F →+* ℂ := w.1.embedding.comp (algebraMap (𝓞 F) F)
  have hf : Function.Injective f :=
    w.1.embedding.injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hH : (cplxForm Q w).hessian = f.mapMatrix Q.hessian := by
    ext i j; simp [cplxForm, QuadForm.hessian, QuadForm.map, f]
  unfold QuadForm.Nondegenerate
  rw [hH, ← RingHom.map_det]
  exact fun h => hQ (hf (h.trans f.map_zero.symm))

/-- **The complex null cones of a nondegenerate form are null** ($n \ge 1$). -/
theorem ae_cplxVal_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (w : ComplexPlace F) :
    ∀ᵐ x : Fin n → ℂ, cplxVal Q w x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_evalIn_ne_zero (nondegenerate_cplxForm hQ w) hn
  rw [ae_iff]
  simpa [cplxVal] using measure_evalIn_eq_zero (cplxForm Q w) hv volume

lemma integrable_cplx_rpow_mul {Q : QuadForm (𝓞 F) n} {ψ : (Fin n → ℂ) → ℝ} {w : ComplexPlace F}
    (hψ : Integrable ψ) (hψQ : Integrable fun x => ‖cplxVal Q w x‖ ^ 2 * ψ x) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Integrable fun x => (‖cplxVal Q w x‖ ^ 2) ^ s * ψ x := by
  have hc := continuous_cplxVal Q w
  refine (hψ.abs.add (by simpa [abs_mul] using hψQ.abs)).mono'
    ((((continuous_norm.comp hc).pow 2).measurable.pow_const s).aestronglyMeasurable.mul
      hψ.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have := rpow_le_one_add (by positivity : (0 : ℝ) ≤ ‖cplxVal Q w x‖ ^ 2) hs
  simp only [Pi.add_apply]
  nlinarith [abs_nonneg (ψ x)]

/-- **Continuity of the complex local zeta integral at $s = 0^+$** (dominated convergence): $Z_w(s) \to 2^n\int\psi$. -/
theorem continuousWithinAt_cplxZetaAt (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) {ψ : (Fin n → ℂ) → ℝ}
    (hψ : Integrable ψ) (hψQ : Integrable fun x => ‖cplxVal Q w x‖ ^ 2 * ψ x)
    (hnull : ∀ᵐ x : Fin n → ℂ, cplxVal Q w x ≠ 0) :
    ContinuousWithinAt (cplxZetaAt Q w ψ) (Set.Icc 0 1) 0 := by
  have hc := continuous_cplxVal Q w
  refine continuousWithinAt_const.mul ?_
  refine continuousWithinAt_of_dominated (bound := fun x => |ψ x| + ‖cplxVal Q w x‖ ^ 2 * |ψ x|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s =>
      (((continuous_norm.comp hc).pow 2).measurable.pow_const s).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun s hs => Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have := rpow_le_one_add (by positivity : (0 : ℝ) ≤ ‖cplxVal Q w x‖ ^ 2) hs
    nlinarith [abs_nonneg (ψ x)]
  · exact hψ.abs.add (by simpa [abs_mul] using hψQ.abs)
  · filter_upwards [hnull] with x hx
    have h0 : ‖cplxVal Q w x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    exact ((Real.continuousAt_const_rpow h0).mul continuousAt_const).continuousWithinAt

theorem cplxZetaAt_zero (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) (ψ : (Fin n → ℂ) → ℝ) :
    cplxZetaAt Q w ψ 0 = 2 ^ n * ∫ x, ψ x := by
  simp [cplxZetaAt]

lemma cplxZetaAt_nonneg (Q : QuadForm (𝓞 F) n) (w : ComplexPlace F) {ψ : (Fin n → ℂ) → ℝ} (hψ : ∀ x, 0 ≤ ψ x)
    (s : ℝ) : 0 ≤ cplxZetaAt Q w ψ s :=
  mul_nonneg (by positivity) (integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hψ x))

lemma isArchTestFnC_sel {Q : QuadForm (𝓞 F) n} {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : IsArchTestFnC Q Ψ)
    (δ : ComplexPlace F → Bool) : IsArchTestFnC Q (sel Ψ δ) where
  integrable w := by
    unfold sel posPart negPart; split_ifs
    · exact (hΨ.integrable w).pos_part
    · exact (hΨ.integrable w).neg_part
  integrable_mul w := by
    unfold sel posPart negPart; split_ifs
    · refine (hΨ.integrable_mul w).pos_part.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
    · refine (hΨ.integrable_mul w).neg_part.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [mul_max_of_nonneg _ _ (by positivity), mul_zero, mul_neg]

/-! ### The global objects with the complex places -/

/-- $\prod_{w\ \mathrm{complex}}Z_w(s)$. -/
def cplxZeta (Q : QuadForm (𝓞 F) n) (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) (s : ℝ) : ℝ :=
  ∏ w, cplxZetaAt Q w (Ψ w) s

/-- **The global zeta integral with all archimedean places**
$Z(s) = |d_F|^{-n/2}\prod_{w\ \mathrm{real}}Z_w(s)\prod_{w\ \mathrm{complex}}Z_w(s)\prod_vZ_\mathfrak p(s)$ (`globalZeta` times the complex
factors; Weil 1982, §4.5, p. 106, with $\lambda = 1$). -/
@[kb "weil1982" "§4.5, p. 106 (∫_{V_A}|F(x)|^sλ(F(x))Φ(x)d'x with λ = 1); §4.4, (1), p. 92"]
def globalZetaNF (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) (s : ℝ) : ℝ :=
  globalZeta Q Φ s * cplxZeta Q Ψ s

/-- **$\int_{V(\mathbb A)}\Phi\,dx$** for $\Phi = \bigotimes_{w\ \mathrm{real}}\Phi_w\otimes\bigotimes_{w\ \mathrm{complex}}\Psi_w\otimes\bigotimes_v\mathbf 1_{L_v}$ and the
Tamagawa (self-dual) measure: $|d_F|^{-n/2}\prod_{w\ \mathrm{real}}\int_{\mathbb R^n}\Phi_w\prod_{w\ \mathrm{complex}}2^n\int_{\mathbb C^n}\Psi_w$. -/
def phiIntegralNF (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) : ℝ :=
  phiIntegral Φ * ∏ w, 2 ^ n * ∫ x, Ψ w x

/-- **Weil's spherical zeta function with the complex places** $Z(s,\rho)$ (Weil 1982, §4.5, (1), p. 102): the
`sphericalZetaAt` (real and finite places) times the complex local factors $Z_w(s,\rho) = 2Z_w(s)$, which do not depend on $\rho$
(every $\rho \in \mathbb C^\times$ is a square; $T(\rho)_{\mathbb C} \to \{Q_w \ne 0\}$ is two-to-one). -/
@[kb "weil1982" "§4.5, (1), p. 102 (spherical zeta-function)"]
def sphericalZetaAtNF (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) (ρ : F) (s : ℝ) : ℝ :=
  sphericalZetaAt Q Φ ρ s * ∏ w, 2 * cplxZetaAt Q w (Ψ w) s

/-- **Weil's zeta function of the quadratic form, all places** (Weil 1982, §4.5, (2), p. 102):
$Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho)$ (no factor $\frac12$). -/
@[kb "weil1982" "§4.5, (2), p. 102 (Z(s) = Σ_ρ Z(s,ρ))"]
def sphericalZetaNF (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) (s : ℝ) : ℝ :=
  ∑' c : SqClasses F, sphericalZetaAtNF Q Φ Ψ ((Quotient.out c : Fˣ) : F) s

lemma sphericalZetaNF_eq (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ) (s : ℝ) :
    sphericalZetaNF Q Φ Ψ s = sphericalZeta Q Φ s * ∏ w, 2 * cplxZetaAt Q w (Ψ w) s := by
  rw [sphericalZetaNF, sphericalZeta, ← tsum_mul_right]; rfl

lemma tendsto_prod_cplxZetaAt (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : IsArchTestFnC Q Ψ) (c : ℝ) :
    Tendsto (fun s => ∏ w, c * cplxZetaAt Q w (Ψ w) s) (𝓝[>] 0) (𝓝 (∏ w, c * (2 ^ n * ∫ x, Ψ w x))) := by
  refine tendsto_finsetProd _ fun w _ => (tendsto_const_nhds (x := c)).mul ?_
  have h : Tendsto (cplxZetaAt Q w (Ψ w)) (𝓝[Set.Icc 0 1] 0) (𝓝 (cplxZetaAt Q w (Ψ w) 0)) :=
    continuousWithinAt_cplxZetaAt Q w (hΨ.integrable w) (hΨ.integrable_mul w) (ae_cplxVal_ne_zero hQ hn w)
  rw [cplxZetaAt_zero] at h
  exact h.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩))

/-- **The residue with all archimedean places** (Weil 1982, §4.5, p. 106; $n \ge 4$, any number field, any signature,
any sign of $\Phi_\infty$): $\lim_{s\to0^+}s\,Z(s) = \rho_F\int_{V(\mathbb A)}\Phi\,dx$. -/
@[kb "weil1982" "§4.5, p. 106 (residue ρ_k∫Φ(x)dx at s = 0 for λ = 1); cf. (8), p. 108"]
theorem tendsto_mul_globalZetaNF_zero (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : IsArchTestFnC Q Ψ) :
    Tendsto (fun s => s * globalZetaNF Q Φ Ψ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegralNF Φ Ψ)) := by
  have h1 := tendsto_mul_globalZeta_zero Q hQ hn hΦ fun w =>
    ae_realVal_ne_zero_of_nondegenerate hQ (by omega) w
  have h2 := tendsto_prod_cplxZetaAt Q hQ (by omega) hΨ 1
  simp only [one_mul] at h2
  rw [phiIntegralNF, ← mul_assoc]
  refine (h1.mul h2).congr fun s => ?_
  rw [globalZetaNF, cplxZeta]; ring

/-! ### Weil's (8) with the complex places: nonnegative data -/

/-- $2^{-r_2}\prod_{w\ \mathrm{complex}}2a_w = \prod_wa_w$. -/
lemma cplxFac_mul_prod (a : ComplexPlace F → ℝ) : cplxFac F * ∏ w, 2 * a w = ∏ w, a w := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, cplxFac, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- **Weil's (8) over any number field, nonnegative data.** -/
theorem tendsto_mul_sphericalZetaNF_zero_of_nonneg (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : IsArchTestFnC Q Ψ) :
    Tendsto (fun s => s * sphericalZetaNF Q Φ Ψ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegralNF Φ Ψ)) := by
  have h1 := tendsto_mul_sphericalZeta_zero_real Q hQ hn hΦ hΦ0 fun w =>
    ae_realVal_ne_zero_of_nondegenerate hQ (by omega) w
  have h2 := tendsto_prod_cplxZetaAt Q hQ (by omega) hΨ 2
  have hlim : cplxFac F * (dedekindZeta_residue F * phiIntegral Φ) * ∏ w, 2 * (2 ^ n * ∫ x, Ψ w x) =
      dedekindZeta_residue F * phiIntegralNF Φ Ψ := by
    rw [phiIntegralNF, ← cplxFac_mul_prod (fun w => 2 ^ n * ∫ x, Ψ w x)]; ring
  rw [← hlim]
  refine (h1.mul h2).congr fun s => ?_
  rw [sphericalZetaNF_eq]; ring

lemma summable_sphericalZetaAtNF (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x) (Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun c : SqClasses F => sphericalZetaAtNF Q Φ Ψ ((Quotient.out c : Fˣ) : F) s) :=
  (summable_sphericalZetaAt Q hQ hn hΦ0 hs).mul_right _

/-! ### Any sign: the multilinear expansion -/

section Signed

variable {Q : QuadForm (𝓞 F) n} {Φ : RealPlace F → (Fin n → ℝ) → ℝ} {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ}

lemma sphArchAt_split (hΦ : IsArchTestFn Q Φ) (w : RealPlace F) (r : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    sphArchAt Q w (Φ w) r s = sphArchAt Q w (posPart (Φ w)) r s - sphArchAt Q w (negPart (Φ w)) r s := by
  unfold sphArchAt
  rw [← mul_sub, ← integral_sub (integrable_rpow_mul_posPart hΦ w hs).integrableOn
    (integrable_rpow_mul_negPart hΦ w hs).integrableOn]
  congr 2; ext x; rw [← mul_sub, posPart_sub_negPart]

lemma cplxZetaAt_split (hΨ : IsArchTestFnC Q Ψ) (w : ComplexPlace F) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    2 * cplxZetaAt Q w (Ψ w) s =
      2 * cplxZetaAt Q w (posPart (Ψ w)) s - 2 * cplxZetaAt Q w (negPart (Ψ w)) s := by
  have hp := isArchTestFnC_sel hΨ (fun _ => true)
  have hm := isArchTestFnC_sel hΨ (fun _ => false)
  unfold cplxZetaAt
  rw [← mul_sub, ← mul_sub, ← integral_sub
    (by simpa [sel] using integrable_cplx_rpow_mul (hp.integrable w) (hp.integrable_mul w) hs)
    (by simpa [sel] using integrable_cplx_rpow_mul (hm.integrable w) (hm.integrable_mul w) hs)]
  congr 3; ext x; rw [← mul_sub, posPart_sub_negPart]

lemma integral_split_real (hΦ : IsArchTestFn Q Φ) (w : RealPlace F) :
    ∫ x, Φ w x = (∫ x, posPart (Φ w) x) - ∫ x, negPart (Φ w) x := by
  have h := integral_sub (hΦ.integrable w).pos_part (hΦ.integrable w).neg_part
  simp only [posPart, negPart] at h ⊢
  rw [← h]
  congr 1; ext x; exact (max_zero_sub_max_neg_zero_eq_self _).symm

lemma integral_split_cplx (hΨ : IsArchTestFnC Q Ψ) (w : ComplexPlace F) :
    2 ^ n * ∫ x, Ψ w x = (2 ^ n * ∫ x, posPart (Ψ w) x) - 2 ^ n * ∫ x, negPart (Ψ w) x := by
  have h := integral_sub (hΨ.integrable w).pos_part (hΨ.integrable w).neg_part
  simp only [posPart, negPart] at h ⊢
  rw [← mul_sub, ← h]
  congr 2; ext x; exact (max_zero_sub_max_neg_zero_eq_self _).symm

/-- **Expansion of $Z(s,\rho)$**: $Z(s,\rho) = \sum_{\varepsilon,\delta}\operatorname{sgn}\varepsilon\operatorname{sgn}\delta\,Z^{\varepsilon,\delta}(s,\rho)$, $s \in [0,1]$. -/
lemma sphericalZetaAtNF_expand (hΦ : IsArchTestFn Q Φ) (hΨ : IsArchTestFnC Q Ψ) (ρ : F) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    sphericalZetaAtNF Q Φ Ψ ρ s = ∑ e : (RealPlace F → Bool) × (ComplexPlace F → Bool),
      sgn e.1 * sgn e.2 * sphericalZetaAtNF Q (sel Φ e.1) (sel Ψ e.2) ρ s := by
  have hR := prod_expand (fun w φ => sphArchAt Q w φ (realEmb w ρ) s) Φ
    fun w => sphArchAt_split hΦ w _ hs
  have hC := prod_expand (fun w ψ => 2 * cplxZetaAt Q w ψ s) Ψ fun w => cplxZetaAt_split hΨ w hs
  rw [Fintype.sum_prod_type]
  simp only [sphericalZetaAtNF, sphericalZetaAt]
  rw [hR, hC]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun δ _ => by ring

lemma phiIntegralNF_expand (hΦ : IsArchTestFn Q Φ) (hΨ : IsArchTestFnC Q Ψ) :
    phiIntegralNF Φ Ψ = ∑ e : (RealPlace F → Bool) × (ComplexPlace F → Bool),
      sgn e.1 * sgn e.2 * phiIntegralNF (sel Φ e.1) (sel Ψ e.2) := by
  have hR := prod_expand (fun _ φ => ∫ x, φ x) Φ fun w => integral_split_real hΦ w
  have hC := prod_expand (fun _ ψ => 2 ^ n * ∫ x, ψ x) Ψ fun w => integral_split_cplx hΨ w
  rw [Fintype.sum_prod_type]
  simp only [phiIntegralNF, phiIntegral]
  rw [hR, hC]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun δ _ => by ring

end Signed

/-! ### Weil's (8): every number field, every signature, any sign of $\Phi_\infty$ -/

/-- **Weil's (8) in full generality for the library's test functions** (A. Weil, *Adeles and Algebraic Groups*, 1982, §4.5, (8),
p. 108). Let $F$ be any number field, $Q$ a nondegenerate quadratic form over $\mathcal O_F$ in $n \ge 5$ variables (any signature at
every real place), and $\Phi = \bigotimes_{w\ \mathrm{real}}\Phi_w\otimes\bigotimes_{w\ \mathrm{complex}}\Psi_w\otimes\bigotimes_v\mathbf 1_{L_v}$ with
$\Phi_w$, $\Psi_w$ admissible (`IsArchTestFn`, `IsArchTestFnC`; real-valued, any sign). Then
$$\lim_{s\to0^+}s\sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) = \rho_F\int_{V(\mathbb A)}\Phi(x)\,dx,$$
$Z(s,\rho)$ Weil's spherical zeta function with all places (`sphericalZetaAtNF`), $\rho_F$ = `dedekindZeta_residue F`, $dx$ the
Tamagawa measure (`phiIntegralNF`). No null-cone hypothesis (proved from nondegeneracy).

*Proof.* For nonnegative data, the residue statement of `SphericalResidue.lean` over a general field (`tendsto_mul_sphericalZeta_zero_real`, residue $2^{-r_2}\rho_F\int\Phi$
from the real places) times the continuous complex factors $\prod_w2Z_w(s) \to 2^{r_2}\prod_w2^n\int\Psi_w$. In general, expand
$\Phi_w = \Phi_w^+ - \Phi_w^-$, $\Psi_w = \Psi_w^+ - \Psi_w^-$ multilinearly; every term is summable over $\rho$ for $s > 0$. -/
@[kb "weil1982" "§4.5, (8), p. 108 (residue of Z(s) = Σ_ρ Z(s,ρ) at s = 0)"]
theorem tendsto_mul_sphericalZetaNF_zero (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : IsArchTestFnC Q Ψ) :
    Tendsto (fun s => s * sphericalZetaNF Q Φ Ψ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegralNF Φ Ψ)) := by
  set E := (RealPlace F → Bool) × (ComplexPlace F → Bool)
  have hterm : ∀ e : E, Tendsto (fun s => sgn e.1 * sgn e.2 * (s * sphericalZetaNF Q (sel Φ e.1) (sel Ψ e.2) s))
      (𝓝[>] 0) (𝓝 (sgn e.1 * sgn e.2 * (dedekindZeta_residue F * phiIntegralNF (sel Φ e.1) (sel Ψ e.2)))) :=
    fun e => (tendsto_mul_sphericalZetaNF_zero_of_nonneg Q hQ hn (isArchTestFn_sel hΦ e.1)
      (sel_nonneg Φ e.1) (isArchTestFnC_sel hΨ e.2)).const_mul _
  have hsum := tendsto_finsetSum (Finset.univ : Finset E) fun e _ => hterm e
  have hL : dedekindZeta_residue F * phiIntegralNF Φ Ψ = ∑ e : E,
      sgn e.1 * sgn e.2 * (dedekindZeta_residue F * phiIntegralNF (sel Φ e.1) (sel Ψ e.2)) := by
    rw [phiIntegralNF_expand hΦ hΨ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hL]
  refine hsum.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  rw [sphericalZetaNF]
  simp_rw [sphericalZetaAtNF_expand hΦ hΨ _ hs']
  have hsm : ∀ e ∈ (Finset.univ : Finset E), Summable fun c : SqClasses F =>
      sgn e.1 * sgn e.2 * sphericalZetaAtNF Q (sel Φ e.1) (sel Ψ e.2) ((Quotient.out c : Fˣ) : F) s :=
    fun e _ => (summable_sphericalZetaAtNF Q hQ hn (sel_nonneg Φ e.1) (sel Ψ e.2) hs.1).mul_left _
  rw [Summable.tsum_finsetSum hsm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [tsum_mul_left, sphericalZetaNF]; ring

/-! ### Schwartz test functions -/

/-- **Every Schwartz function on $\mathbb C^n$ is admissible at a complex place**: $|Q_w|^2|\Psi_w| \le C^2\|x\|^4|\Psi_w| \in L^1$. -/
theorem isArchTestFnC_schwartz (Q : QuadForm (𝓞 F) n) (Ψ : ComplexPlace F → SchwartzMap (Fin n → ℂ) ℝ) :
    IsArchTestFnC Q (fun w => Ψ w) where
  integrable w := (Ψ w).integrable
  integrable_mul w := by
    set C := ∑ i, ∑ j, ‖(cplxForm Q w).coeff i j‖
    refine (((Ψ w).integrable_pow_mul volume 4).const_mul (C ^ 2)).mono'
      (((continuous_norm.comp (continuous_cplxVal Q w)).pow 2).mul (Ψ w).continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h := norm_evalIn_le (cplxForm Q w) x
    have h0 : 0 ≤ ‖cplxVal Q w x‖ := norm_nonneg _
    have hsq : ‖cplxVal Q w x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 4 := by
      have : ‖cplxVal Q w x‖ ≤ C * ‖x‖ ^ 2 := h
      calc ‖cplxVal Q w x‖ ^ 2 ≤ (C * ‖x‖ ^ 2) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = C ^ 2 * ‖x‖ ^ 4 := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), ← Real.norm_eq_abs (Ψ w x), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)

/-- **Weil's (8), unconditional for Schwartz data** (Weil 1982, §4.5, (8), p. 108): $F$ any number field, $Q$ nondegenerate over
$\mathcal O_F$ (any signature), $n \ge 5$, $\Phi_w \in \mathcal S(\mathbb R^n)$ and $\Psi_w \in \mathcal S(\mathbb C^n)$ real-valued (any sign):
$\lim_{s\to0^+}s\sum_\rho Z(s,\rho) = \rho_F\int_{V(\mathbb A)}\Phi\,dx$. -/
@[kb "weil1982" "§4.5, (8), p. 108 (Schwartz Φ_∞, every signature, every number field)"]
theorem tendsto_mul_sphericalZetaNF_zero_schwartz (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    (Φ : RealPlace F → SchwartzMap (Fin n → ℝ) ℝ) (Ψ : ComplexPlace F → SchwartzMap (Fin n → ℂ) ℝ) :
    Tendsto (fun s => s * sphericalZetaNF Q (fun w => Φ w) (fun w => Ψ w) s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegralNF (fun w => Φ w) (fun w => Ψ w))) :=
  tendsto_mul_sphericalZetaNF_zero Q hQ hn (isArchTestFn_schwartz Q Φ) (isArchTestFnC_schwartz Q Ψ)

/-- **The residue, unconditional for Schwartz data** ($n \ge 4$, any number field, any signature). -/
@[kb "weil1982" "§4.5, p. 106 (residue at s = 0, Schwartz Φ_∞); cf. (8), p. 108"]
theorem tendsto_mul_globalZetaNF_zero_schwartz (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (Φ : RealPlace F → SchwartzMap (Fin n → ℝ) ℝ) (Ψ : ComplexPlace F → SchwartzMap (Fin n → ℂ) ℝ) :
    Tendsto (fun s => s * globalZetaNF Q (fun w => Φ w) (fun w => Ψ w) s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegralNF (fun w => Φ w) (fun w => Ψ w))) :=
  tendsto_mul_globalZetaNF_zero Q hQ hn (isArchTestFn_schwartz Q Φ) (isArchTestFnC_schwartz Q Ψ)

end QuadFormsKB.SphericalNF
