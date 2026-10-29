import QuadFormsKB.Analysis.AdelicPoisson
import QuadFormsKB.Analysis.MinkowskiPoissonPi

/-!
# Adelic Poisson summation in $n$ variables with a coordinate-pure finite part

The $n$-variable form of `adelicPoisson` and `adelicPoisson_factorizable` (`Analysis/AdelicPoisson.lean`) for an
**arbitrary** Schwartz function $f_\infty$ on $F_\infty^n$ (not a sum of pure tensors) and a finite part that is a
product over the coordinates, $\prod_v\prod_{i<n}f_{v,i}(\gamma_i)$.

* **`adelicPoisson_pi`**: for $\xi \in F^n$ and exponents $k_{i,v}$ ($k_{i,v} = 0$ for almost all $v$),
  $$\sum_{\gamma\in F^n} f_\infty(\gamma)\prod_{i<n}\prod_v\mathbf 1_{\xi_i+\mathfrak p_v^{k_{i,v}}}(\gamma_i) =
    \sum_{\gamma\in F^n}\hat f_\infty(\gamma)\prod_{i<n}\prod_v\widehat{\mathbf 1_{\xi_i+\mathfrak p_v^{k_{i,v}}}}(\gamma_i),$$
  $\hat f_\infty$ = `fourierInfPi`; both sides converge absolutely.
* **`adelicPoisson_factorizable_pi`**: the same for Schwartz–Bruhat $f_{v,i}$ (`IsSchwartzBruhatV`) with
  $f_{v,i} = \mathbf 1_{\mathcal O_v}$ for $v \notin S$.

*Proof.* Coordinatewise, the finite part is the indicator of $\xi + \prod_i\mathfrak a_i$ (`finprod_ballIndV`), resp.
$\prod_i\operatorname{vol}(\hat{\mathfrak a}_i)\,e(-\operatorname{Tr}(\xi_i\gamma_i))\mathbf 1_{\mathfrak a_i^\vee}(\gamma_i)$
(`finprod_fourierV_ballIndV`); then `poisson_fractionalIdeal_pi`. The factorizable case expands each coordinate by
`factorizable_expansion`.

Sources: as for `adelicPoisson` (Cassels–Fröhlich Ch. XV, §4.2, Lemma 4.2.4, p. 333), in $n$ variables.
-/

open IsDedekindDomain NumberField WithZero MeasureTheory NumberField.InfinitePlace
open NumberField.mixedEmbedding
open scoped Real FourierTransform nonZeroDivisors Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "V" => mixedSpace F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

lemma prod_ite_eq_indicator {α : Type*} (S : Fin n → Set α) (g : Fin n → α → ℂ) (x : Fin n → α) :
    ∏ i, (if x i ∈ S i then g i (x i) else 0) =
      (Set.univ.pi S).indicator (fun x => ∏ i, g i (x i)) x := by
  by_cases h : x ∈ Set.univ.pi S
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_congr rfl fun i _ => if_pos (h i (Set.mem_univ i))
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma tsum_indicator_pi {α : Type*} (S : Fin n → Set α) (G : (Fin n → α) → ℂ) :
    ∑' x : Fin n → α, (Set.univ.pi S).indicator G x = ∑' y : ((i : Fin n) → S i), G fun i => y i := by
  rw [← tsum_subtype, ← (Equiv.Set.univPi S).symm.tsum_eq]
  rfl

lemma summable_indicator_pi_iff {α : Type*} (S : Fin n → Set α) (G : (Fin n → α) → ℂ) :
    Summable (fun x : Fin n → α => (Set.univ.pi S).indicator G x) ↔
      Summable fun y : ((i : Fin n) → S i) => G fun i => y i := by
  rw [← summable_subtype_iff_indicator, ← (Equiv.Set.univPi S).symm.summable_iff]
  rfl

lemma coe_prod_circle' {ι : Type*} (s : Finset ι) (f : ι → Circle) :
    ((∏ i ∈ s, f i : Circle) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod Circle.coeHom f s

lemma fourierChar_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    𝐞 (∑ i ∈ s, f i) = ∏ i ∈ s, 𝐞 (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

variable {k : Fin n → HeightOneSpectrum (𝓞 F) → ℤ}

lemma lhs_pi_eq_indicator (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F)
    (hk : ∀ i, (Function.support (k i)).Finite) :
    (fun γ : Fin n → F => f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
        ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v) (algebraMap F (v.adicCompletion F) (γ i))) =
      fun γ => (Set.univ.pi fun i => ((idealOfExps (k i) : FI) : Set F)).indicator
        (fun x => f (fun i => mixedEmbedding F (ξ i + x i))) (γ - ξ) := by
  funext γ
  simp_rw [finprod_ballIndV (hk _)]
  by_cases h : γ - ξ ∈ Set.univ.pi fun i => ((idealOfExps (k i) : FI) : Set F)
  · have hi : ∀ i, γ i - ξ i ∈ idealOfExps (k i) := fun i => by simpa using h i (Set.mem_univ i)
    rw [Set.indicator_of_mem h]
    simp only [hi, ite_true, Finset.prod_const_one, mul_one]
    congr 1; funext i; simp
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
    obtain ⟨i, hi⟩ := h
    simp only [SetLike.mem_coe] at hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg (by simpa using hi)]), mul_zero]

/-- The constant $\prod_i\operatorname{vol}(\hat{\mathfrak a}_i)$. -/
def cPi (k : Fin n → HeightOneSpectrum (𝓞 F) → ℤ) : ℝ :=
  ∏ i, (((FractionalIdeal.absNorm (idealOfExps (k i)) : ℝ) * Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ)

lemma rhs_pi_eq_indicator (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F)
    (hk : ∀ i, (Function.support (k i)).Finite) :
    (fun γ : Fin n → F => fourierInfPi f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
        fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v))
          (algebraMap F (v.adicCompletion F) (γ i))) =
      fun γ => (Set.univ.pi fun i => ((FractionalIdeal.dual ℤ ℚ (idealOfExps (k i)) : FI) : Set F)).indicator
        (fun μ => (cPi k : ℂ) * (fourierInfPi f (fun i => mixedEmbedding F (μ i)) *
          ((𝐞 (-∑ i, ((Algebra.trace ℚ F (ξ i * μ i) : ℚ) : ℝ)) : Circle) : ℂ))) γ := by
  funext γ
  simp_rw [finprod_fourierV_ballIndV (hk _)]
  by_cases h : γ ∈ Set.univ.pi fun i => ((FractionalIdeal.dual ℤ ℚ (idealOfExps (k i)) : FI) : Set F)
  · have hi : ∀ i, γ i ∈ FractionalIdeal.dual ℤ ℚ (idealOfExps (k i)) := fun i => by
      simpa using h i (Set.mem_univ i)
    rw [Set.indicator_of_mem h]
    simp only [hi, ite_true]
    rw [Finset.prod_mul_distrib, cPi]
    push_cast
    rw [← Finset.sum_neg_distrib, fourierChar_sum', coe_prod_circle']
    ring
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
    obtain ⟨i, hi⟩ := h
    simp only [SetLike.mem_coe] at hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]

/-- The fractional ideals $\mathfrak a_i = \prod_v\mathfrak p_v^{k_{i,v}}$ as units. -/
def idealsPi (k : Fin n → HeightOneSpectrum (𝓞 F) → ℤ) : Fin n → FIˣ :=
  fun i => Units.mk0 (idealOfExps (k i)) (idealOfExps_ne_zero (k i))

lemma cPi_eq : (cPi k : ℝ) =
    (∏ i, ((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F (idealsPi k i))))⁻¹ := by
  rw [cPi, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [selfDual_covolume_idealLattice]
  rfl

/-- **Adelic Poisson summation in $n$ variables** (finite part: products of coset indicators). Let $f_\infty$ be a
Schwartz function on $F_\infty^n$, $\xi \in F^n$, and $k_{i,v} \in \mathbb{Z}$ ($i < n$, $v$ finite) with
$k_{i,v} = 0$ for almost all $v$. Then
$$\sum_{\gamma\in F^n} f_\infty(\gamma)\prod_{i<n}\prod_v\mathbf 1_{\xi_i+\mathfrak p_v^{k_{i,v}}}(\gamma_i) =
  \sum_{\gamma\in F^n}\hat f_\infty(\gamma)\prod_{i<n}\prod_v\widehat{\mathbf 1_{\xi_i+\mathfrak p_v^{k_{i,v}}}}(\gamma_i),$$
$\hat f_\infty$ = `fourierInfPi` and the local transforms `fourierV` (self-dual measures); both sides converge absolutely
(`summable_adelicPoisson_pi_lhs`, `_rhs`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2, Lemma 4.2.4 (Poisson formula), p. 333 (n-variable form)"]
theorem adelicPoisson_pi (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F)
    (hk : ∀ i, (Function.support (k i)).Finite) :
    ∑' γ : Fin n → F, f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
        ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v) (algebraMap F (v.adicCompletion F) (γ i)) =
      ∑' γ : Fin n → F, fourierInfPi f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
        fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v))
          (algebraMap F (v.adicCompletion F) (γ i)) := by
  rw [lhs_pi_eq_indicator f ξ hk, rhs_pi_eq_indicator f ξ hk]
  rw [← (Equiv.subRight ξ).symm.tsum_eq]
  simp only [Equiv.subRight_symm_apply, add_sub_cancel_right]
  rw [tsum_indicator_pi, tsum_indicator_pi, tsum_mul_left]
  have h := poisson_fractionalIdeal_pi (idealsPi k) f ξ
  rw [cPi_eq]
  exact h

/-- The left side of `adelicPoisson_pi` converges absolutely. -/
theorem summable_adelicPoisson_pi_lhs (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F)
    (hk : ∀ i, (Function.support (k i)).Finite) :
    Summable fun γ : Fin n → F => f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
      ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v) (algebraMap F (v.adicCompletion F) (γ i)) := by
  rw [lhs_pi_eq_indicator f ξ hk, ← (Equiv.subRight ξ).symm.summable_iff]
  simp only [Function.comp_def, Equiv.subRight_symm_apply, add_sub_cancel_right]
  rw [summable_indicator_pi_iff]
  exact summable_poisson_pi_lhs (idealsPi k) f ξ

/-- The right side of `adelicPoisson_pi` converges absolutely. -/
theorem summable_adelicPoisson_pi_rhs (f : SchwartzMap (Fin n → V) ℂ) (ξ : Fin n → F)
    (hk : ∀ i, (Function.support (k i)).Finite) :
    Summable fun γ : Fin n → F => fourierInfPi f (fun i => mixedEmbedding F (γ i)) * ∏ i, ∏ᶠ v,
      fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ i)) (k i v))
        (algebraMap F (v.adicCompletion F) (γ i)) := by
  rw [rhs_pi_eq_indicator f ξ hk, summable_indicator_pi_iff]
  exact (summable_poisson_pi_rhs (idealsPi k) f ξ).mul_left _

/-! ### Coordinate-pure Schwartz–Bruhat finite parts -/

section Factorizable

variable (fv : Fin n → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
  (S : Finset (HeightOneSpectrum (𝓞 F)))
  (hS : ∀ i, ∀ v ∈ S, IsSchwartzBruhatV v (fv i v)) (hout : ∀ i, ∀ v ∉ S, fv i v = ballIndV v 0 0)

include hS hout in
/-- **Expansion of a coordinate-pure finite part** into products of coset indicators with global centers. -/
lemma factorizable_expansion_pi : ∃ (ι : Type) (_ : Fintype ι) (A : ι → ℂ) (ξ : ι → Fin n → F)
    (k : ι → Fin n → HeightOneSpectrum (𝓞 F) → ℤ), (∀ J i, (Function.support (k J i)).Finite) ∧
    (∀ γ : Fin n → F, ∏ i, ∏ᶠ v, fv i v (algebraMap F (v.adicCompletion F) (γ i)) =
      ∑ J, A J * ∏ i, ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) (ξ J i)) (k J i v)
        (algebraMap F (v.adicCompletion F) (γ i))) ∧
    (∀ γ : Fin n → F, ∏ i, ∏ᶠ v, fourierV v (fv i v) (algebraMap F (v.adicCompletion F) (γ i)) =
      ∑ J, A J * ∏ i, ∏ᶠ v, fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ J i)) (k J i v))
        (algebraMap F (v.adicCompletion F) (γ i))) := by
  choose ι hι A ξ kJ hfin hL hR using fun i => factorizable_expansion (fv i) S (hS i) (hout i)
  let _ := hι
  refine ⟨(i : Fin n) → ι i, inferInstance, fun J => ∏ i, A i (J i), fun J i => ξ i (J i),
    fun J i => kJ i (J i), fun J i => hfin i (J i), fun γ => ?_, fun γ => ?_⟩
  · simp_rw [hL, Finset.prod_univ_sum, Finset.prod_mul_distrib, Fintype.piFinset_univ]
  · simp_rw [hR, Finset.prod_univ_sum, Finset.prod_mul_distrib, Fintype.piFinset_univ]

include hS hout in
/-- **Adelic Poisson summation in $n$ variables for a Schwartz archimedean part and a coordinate-pure finite part.**
Let $f_\infty$ be an arbitrary Schwartz function on $F_\infty^n$ (not necessarily a sum of pure tensors), and for each
coordinate $i < n$ and finite place $v$ let $f_{v,i}$ be a Schwartz–Bruhat function on $F_v$ (`IsSchwartzBruhatV`),
with $f_{v,i} = \mathbf 1_{\mathcal O_v}$ for $v \notin S$, $S$ finite. Then
$$\sum_{\gamma\in F^n} f_\infty(\gamma)\prod_{i<n}\prod_v f_{v,i}(\gamma_i) =
  \sum_{\gamma\in F^n}\hat f_\infty(\gamma)\prod_{i<n}\prod_v\hat f_{v,i}(\gamma_i),$$
$\hat f_\infty$ = `fourierInfPi`, $\hat f_{v,i}$ = `fourierV` (self-dual measures, standard characters); both sides
converge absolutely (`summable_adelicPoisson_factorizable_pi_lhs`, `_rhs`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2, Lemma 4.2.4 (Poisson formula), p. 333 (n-variable form)"]
theorem adelicPoisson_factorizable_pi (f : SchwartzMap (Fin n → V) ℂ) :
    ∑' γ : Fin n → F, f (fun i => mixedEmbedding F (γ i)) *
        ∏ i, ∏ᶠ v, fv i v (algebraMap F (v.adicCompletion F) (γ i)) =
      ∑' γ : Fin n → F, fourierInfPi f (fun i => mixedEmbedding F (γ i)) *
        ∏ i, ∏ᶠ v, fourierV v (fv i v) (algebraMap F (v.adicCompletion F) (γ i)) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion_pi fv S hS hout
  simp_rw [hL, hR, Finset.mul_sum]
  rw [Summable.tsum_finsetSum, Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun J _ => ?_
    simp_rw [mul_left_comm (f _), mul_left_comm (fourierInfPi f _)]
    rw [tsum_mul_left, tsum_mul_left, adelicPoisson_pi f (ξ J) (hfinJ J)]
  · intro J _
    simp_rw [mul_left_comm (fourierInfPi f _)]
    exact (summable_adelicPoisson_pi_rhs f (ξ J) (hfinJ J)).mul_left _
  · intro J _
    simp_rw [mul_left_comm (f _)]
    exact (summable_adelicPoisson_pi_lhs f (ξ J) (hfinJ J)).mul_left _

include hS hout in
/-- The left side of `adelicPoisson_factorizable_pi` converges absolutely. -/
theorem summable_adelicPoisson_factorizable_pi_lhs (f : SchwartzMap (Fin n → V) ℂ) :
    Summable fun γ : Fin n → F => f (fun i => mixedEmbedding F (γ i)) *
      ∏ i, ∏ᶠ v, fv i v (algebraMap F (v.adicCompletion F) (γ i)) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion_pi fv S hS hout
  simp_rw [hL, Finset.mul_sum]
  refine summable_sum fun J _ => ?_
  simp_rw [mul_left_comm (f _)]
  exact (summable_adelicPoisson_pi_lhs f (ξ J) (hfinJ J)).mul_left _

include hS hout in
/-- The right side of `adelicPoisson_factorizable_pi` converges absolutely. -/
theorem summable_adelicPoisson_factorizable_pi_rhs (f : SchwartzMap (Fin n → V) ℂ) :
    Summable fun γ : Fin n → F => fourierInfPi f (fun i => mixedEmbedding F (γ i)) *
      ∏ i, ∏ᶠ v, fourierV v (fv i v) (algebraMap F (v.adicCompletion F) (γ i)) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion_pi fv S hS hout
  simp_rw [hR, Finset.mul_sum]
  refine summable_sum fun J _ => ?_
  simp_rw [mul_left_comm (fourierInfPi f _)]
  exact (summable_adelicPoisson_pi_rhs f (ξ J) (hfinJ J)).mul_left _

end Factorizable

end

end QuadFormsKB.Analysis
