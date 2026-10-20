/-
# Hilbert modular forms: constant terms at the cusps as limits

For $f : \mathbb{H}^d \to \mathbb{C}$, a weight $k$ and $A \in \mathrm{SL}_2(F)$, the **constant term of $f$ at the cusp $A\infty$** is
$$\mathrm{cv}_k(f, A) = \lim_{\min_v\operatorname{Im}z_v\to\infty}(f\,|_k\,A)(z)\qquad(\texttt{cuspVal}),$$
when the limit exists (`HasCuspLimits f k`: at every $A$). This file proves the elementary rules:
* `atImInftyPi` is a proper filter (`atImInftyPi_neBot`), so limits are unique;
* `tendsto_slash_of_c_eq_zero`: if $g \to L$ and $A_{10} = 0$ then $g\,|_k\,A \to N(A_{00})^kL$, $N(x) = \prod_v\sigma_v(x)$;
* `cuspVal_eq_of_col`: $\mathrm{cv}_k(f, A)$ depends only on the first column $(A_{00}, A_{10})$ of $A$, i.e. on the vector
  $(0, 1)A^{-1} = (-A_{10}, A_{00})$;
* `cuspVal_mul_diagU`: $\mathrm{cv}_k(f, A\,\mathrm{diag}(t, t^{-1})) = N(t)^k\,\mathrm{cv}_k(f, A)$;
* `cuspVal_mul_left`: if $f\,|_k\,\gamma = c f$ then $\mathrm{cv}_k(f, \gamma A) = c\,\mathrm{cv}_k(f, A)$;
* `isZeroAtImInftyPi_sub`: two functions with the same limit at $A\infty$ differ by a function vanishing there.

Sources: Freitag, *Hilbert Modular Forms* (1990), Ch. I §§2–4 (cusps, Fourier expansions at cusps) [unverified];
Garrett (1990), Ch. 1 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinForms

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

section General

variable {ι : Type*} [Fintype ι]

/-- **The filter $\min_v\operatorname{Im}z_v \to \infty$ is proper.** -/
instance atImInftyPi_neBot : (atImInftyPi : Filter (ι → ℍ)).NeBot := by
  set f : ℝ → ι → ℍ := fun t _ => ⟨Complex.I * (max t 1 : ℝ), by simp⟩
  have hf : Tendsto f atTop atImInftyPi := by
    refine tendsto_iInf.mpr fun v => tendsto_comap_iff.mpr ?_
    have : (fun t => (f t v).im) = fun t => max t 1 := by
      funext t; simp [f, UpperHalfPlane.im]
    rw [Function.comp_def, this]
    exact tendsto_atTop_mono (fun t => le_max_left t 1) tendsto_id
  exact hf.neBot

/-- $(f - g)\,|_k\,\gamma = f\,|_k\,\gamma - g\,|_k\,\gamma$. -/
lemma sub_slash' (k : ℤ) (γ : ι → GL(2, ℝ)⁺) (f g : (ι → ℍ) → ℂ) :
    (f - g) ∣[k] γ = f ∣[k] γ - g ∣[k] γ := by
  funext z
  simp only [slash_apply, Pi.sub_apply, sub_mul]

/-- $(\sum_i f_i)\,|_k\,\gamma = \sum_i f_i\,|_k\,\gamma$. -/
lemma sum_slash' {α : Type*} (k : ℤ) (γ : ι → GL(2, ℝ)⁺) (s : Finset α) (f : α → (ι → ℍ) → ℂ) :
    (∑ i ∈ s, f i) ∣[k] γ = ∑ i ∈ s, f i ∣[k] γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

end General

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Constant terms at cusps -/

lemma tendsto_im_atImInftyPi' (v : InfinitePlace F) :
    Tendsto (fun z : InfinitePlace F → ℍ => (z v).im) atImInftyPi atTop :=
  tendsto_comap.mono_left (iInf_le _ v)

/-- **The constant term of $f$ at the cusp $A\infty$** in weight $k$: $\lim(f\,|_k\,A)(z)$ as $\min_v\operatorname{Im}z_v \to \infty$
(Mathlib's `limUnder`; a junk value if the limit does not exist). -/
@[kb "freitag1990" "Ch. I §4, the constant term at a cusp [unverified]"]
noncomputable def cuspVal (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ) (A : SL(2, F)) : ℂ :=
  limUnder atImInftyPi (f ∣[k] slHom (realEmb F) A)

/-- **$f$ has a constant term at every cusp**: $f\,|_k\,A$ has a limit at $\infty$ for every $A \in \mathrm{SL}_2(F)$. -/
def HasCuspLimits (f : (InfinitePlace F → ℍ) → ℂ) (k : ℤ) : Prop :=
  ∀ A : SL(2, F), ∃ L, Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L)

lemma tendsto_cuspVal {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} (hf : HasCuspLimits f k) (A : SL(2, F)) :
    Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 (cuspVal f k A)) :=
  tendsto_nhds_limUnder (hf A)

lemma cuspVal_eq_of_tendsto {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {A : SL(2, F)} {L : ℂ}
    (h : Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L)) : cuspVal f k A = L :=
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, h⟩) h

/-- **Slashing by an upper triangular matrix at $\infty$**: if $g \to L$ and $A_{10} = 0$ then
$g\,|_k\,A \to N(A_{00})^kL$ (here $Az = (\sigma_v(A_{00})^2z_v + \sigma_v(A_{00}A_{01}))_v$). -/
theorem tendsto_slash_of_c_eq_zero {g : (InfinitePlace F → ℍ) → ℂ} {L : ℂ}
    (hg : Tendsto g atImInftyPi (𝓝 L)) (k : ℤ) (A : SL(2, F)) (hc : A 1 0 = 0) :
    Tendsto (g ∣[k] slHom (realEmb F) A) atImInftyPi
      (𝓝 ((∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k * L)) := by
  have hdet := sl2_det A
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ∀ v, realEmb F v (A 1 1) ≠ 0 := fun v h => by
    have := congrArg (realEmb F v) hdet; rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  have hfac : ∀ z : InfinitePlace F → ℍ, ∏ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) :
      GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ) : ℂ) *
      denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-k) =
      (∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k := by
    intro z
    have hprod : (∏ v, (realEmb F v (A 0 0) : ℂ)) * ∏ v, (realEmb F v (A 1 1) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [← ofReal_mul, ← map_mul, hdet, map_one, ofReal_one]
    have : ∀ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ) : ℂ) *
        denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-k) =
        ((realEmb F v (A 1 1) : ℂ)) ^ (-k) := by
      intro v
      rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul]
      simp [denom, hc]
    simp_rw [this]
    rw [Finset.prod_zpow, _root_.zpow_neg, ← _root_.inv_zpow, ← eq_inv_of_mul_eq_one_left hprod]
  have him : ∀ v, Tendsto (fun z : InfinitePlace F → ℍ =>
      ((slHom (realEmb F) A • z) v : ℍ).im) atImInftyPi atTop := by
    intro v
    have heq : ∀ z : InfinitePlace F → ℍ, ((slHom (realEmb F) A • z) v : ℍ).im =
        (z v).im / (realEmb F v (A 1 1)) ^ 2 := by
      intro z
      rw [Pi.smul_apply', glPos_smul_eq, UpperHalfPlane.im_smul_eq_div_normSq,
        GeneralLinearGroup.val_det_apply]
      have hdet1 := slHom_det (realEmb F) A v
      rw [GeneralLinearGroup.val_det_apply] at hdet1
      rw [hdet1, abs_one, one_mul]
      congr 1
      simp [denom, hc, Complex.normSq_ofReal, sq]
    simp_rw [heq]
    exact (tendsto_im_atImInftyPi' v).atTop_div_const (pow_pos (lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (hd v)))) 1 |>.trans_eq (pow_one _))
  have hθ : Tendsto (fun z => g (slHom (realEmb F) A • z)) atImInftyPi (𝓝 L) := by
    refine hg.comp ?_
    exact tendsto_iInf.mpr fun v => tendsto_comap_iff.mpr (him v)
  have := hθ.const_mul ((∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k)
  refine this.congr fun z => ?_
  rw [slash_apply, hfac z, mul_comm]

/-- If $f\,|_k\,A \to L$ and $B_{10} = 0$ then $f\,|_k\,AB \to N(B_{00})^kL$. -/
lemma tendsto_slash_mul_of_c_eq_zero {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {A : SL(2, F)} {L : ℂ}
    (h : Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L)) (B : SL(2, F)) (hB : B 1 0 = 0) :
    Tendsto (f ∣[k] slHom (realEmb F) (A * B)) atImInftyPi
      (𝓝 ((∏ v, (realEmb F v (B 0 0) : ℂ)) ^ k * L)) := by
  rw [map_mul, SlashAction.slash_mul]
  exact tendsto_slash_of_c_eq_zero h k B hB

/-- **The constant term depends only on the first column**: if $A, B \in \mathrm{SL}_2(F)$ have the same first column then
$B = AT(\beta)$ for some $\beta$, and $f\,|_k\,A \to L$ implies $f\,|_k\,B \to L$. -/
theorem tendsto_slash_of_col_eq {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {A B : SL(2, F)} {L : ℂ}
    (h : Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L)) (h0 : A 0 0 = B 0 0)
    (h1 : A 1 0 = B 1 0) :
    Tendsto (f ∣[k] slHom (realEmb F) B) atImInftyPi (𝓝 L) := by
  have hB : B = A * (A⁻¹ * B) := by group
  have hc : (A⁻¹ * B) 1 0 = 0 := by
    rw [sl2_mul_apply, sl2_inv_10, sl2_inv_11, ← h0, ← h1]; ring
  have hd : (A⁻¹ * B) 0 0 = 1 := by
    rw [sl2_mul_apply, sl2_inv_00, sl2_inv_01, ← h0, ← h1]
    have := sl2_det A
    linear_combination this
  have := tendsto_slash_mul_of_c_eq_zero h (A⁻¹ * B) hc
  rw [hd] at this
  simp only [map_one, ofReal_one, Finset.prod_const_one, _root_.one_zpow, one_mul] at this
  rwa [← hB] at this

lemma cuspVal_eq_of_col {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} (hf : HasCuspLimits f k) {A B : SL(2, F)}
    (h0 : A 0 0 = B 0 0) (h1 : A 1 0 = B 1 0) : cuspVal f k A = cuspVal f k B :=
  (cuspVal_eq_of_tendsto (tendsto_slash_of_col_eq (tendsto_cuspVal hf A) h0 h1)).symm

/-- $\mathrm{cv}_k(f, A\,\mathrm{diag}(t, t^{-1})) = N(t)^k\,\mathrm{cv}_k(f, A)$. -/
lemma cuspVal_mul_diagU {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} (hf : HasCuspLimits f k) (A : SL(2, F))
    (t : Fˣ) : cuspVal f k (A * diagU t) = (∏ v, (realEmb F v (t : F) : ℂ)) ^ k * cuspVal f k A :=
  cuspVal_eq_of_tendsto (tendsto_slash_mul_of_c_eq_zero (tendsto_cuspVal hf A) (diagU t) rfl)

/-- If $f\,|_k\,\gamma = c f$ then $\mathrm{cv}_k(f, \gamma A) = c\,\mathrm{cv}_k(f, A)$. -/
lemma cuspVal_mul_left {f : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} (hf : HasCuspLimits f k) {γ : SL(2, F)}
    {c : ℂ} (hγ : f ∣[k] slHom (realEmb F) γ = c • f) (A : SL(2, F)) :
    cuspVal f k (γ * A) = c * cuspVal f k A := by
  refine cuspVal_eq_of_tendsto ?_
  rw [map_mul, SlashAction.slash_mul, hγ, smul_slash]
  exact (tendsto_cuspVal hf A).const_smul c

/-- **Equal constant terms give a function vanishing at the cusp.** -/
lemma isZeroAtImInftyPi_sub {f g : (InfinitePlace F → ℍ) → ℂ} {k : ℤ} {A : SL(2, F)} {L : ℂ}
    (hf : Tendsto (f ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L))
    (hg : Tendsto (g ∣[k] slHom (realEmb F) A) atImInftyPi (𝓝 L)) :
    IsZeroAtImInftyPi ((f - g) ∣[k] slHom (realEmb F) A) := by
  rw [sub_slash']
  have := hf.sub hg
  rwa [sub_self] at this

end QuadFormsKB.HilbertModular
