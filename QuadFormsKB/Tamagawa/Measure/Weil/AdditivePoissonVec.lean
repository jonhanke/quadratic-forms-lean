import QuadFormsKB.Tamagawa.Measure.Weil.AdditivePoisson

/-!
# Poisson summation on $\mathbb A_F^\iota$ twisted by $(F^\iota\otimes\mathbb A)^\times$

For $A = F^\iota$ (coordinatewise structure, trace form $\sum_i x_iy_i$, self-dual measure `muAddVec`) and a pure tensor
$\Phi = \bigotimes_i\Phi_i$ of factorizable Schwartz–Bruhat functions $\Phi_i = f_{i,\infty}\otimes\bigotimes_v f_{i,v}$,
$$\sum_{\xi\in F^\iota}\prod_i\Phi_i(g_i\xi_i) = \|N_{A/F}(g)\|_{\mathbb A}^{-1}\sum_{\xi\in F^\iota}\prod_i\hat\Phi_i(g_i^{-1}\xi_i)$$
(`adelicPoissonVec_smul`; for $A = F^\iota$ the inverse adjoint of $g$ for the trace form is $g^{-1}$). The proof is the
one-variable twisted formula `adelicPoisson_smul` in each coordinate, together with the generic
`summable_norm_and_tsum_pi_prod` (a finite product of absolutely convergent series is the sum over the product index
set), which Mathlib v4.35 lacks. General factorizable $\Phi$ (finite sums of pure tensors) follow by linearity.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped Classical ENNReal NNReal

namespace MeasureTheory

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {β : Type*}

/-- Finite products of absolutely convergent series over `Fin n`: `Σ_{ξ : Fin n → β} ∏_i h_i(ξ_i) = ∏_i Σ_b h_i(b)`,
with absolute convergence of the left side. -/
theorem summable_norm_and_tsum_fin_prod (n : ℕ) :
    ∀ (h : Fin n → β → R), (∀ i, Summable fun b => ‖h i b‖) →
      (Summable fun ξ : Fin n → β => ‖∏ i, h i (ξ i)‖) ∧
        ∑' ξ : Fin n → β, ∏ i, h i (ξ i) = ∏ i, ∑' b, h i b := by
  induction n with
  | zero => intro h _; exact ⟨Summable.of_finite, by simp⟩
  | succ n ih =>
    intro h hs
    obtain ⟨ih1, ih2⟩ := ih (fun i => h i.succ) (fun i => hs i.succ)
    set g : (Fin n → β) → R := fun η => ∏ i, h i.succ (η i) with hg
    have hg1 : Summable fun η => ‖g η‖ := ih1
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => β)
    have hfun : ∀ p : β × (Fin n → β), ∏ i, h i (e p i) = h 0 p.1 * g p.2 := by
      intro p
      simp [e, g, Fin.consEquiv, Fin.prod_univ_succ]
    have hm : Summable fun p : β × (Fin n → β) => ‖h 0 p.1 * g p.2‖ := (hs 0).mul_norm hg1
    constructor
    · rw [← e.summable_iff]
      refine hm.congr fun p => ?_
      show ‖h 0 p.1 * g p.2‖ = ‖∏ i, h i (e p i)‖
      rw [hfun]
    · rw [← e.tsum_eq, Fin.prod_univ_succ]
      have h2 : ∑' η, g η = ∏ i : Fin n, ∑' b, h i.succ b := ih2
      rw [← h2, tsum_mul_tsum_of_summable_norm (hs 0) hg1]
      exact tsum_congr fun p => hfun p

/-- **Finite products of absolutely convergent series.** For a finite index type `ι` and absolutely summable
`h_i : β → R`, the family `ξ ↦ ∏_i h_i(ξ_i)` on `ι → β` is absolutely summable and
`Σ_{ξ : ι → β} ∏_i h_i(ξ_i) = ∏_i Σ_b h_i(b)`. -/
theorem summable_norm_and_tsum_pi_prod {ι : Type*} [Fintype ι] (h : ι → β → R)
    (hs : ∀ i, Summable fun b => ‖h i b‖) :
    (Summable fun ξ : ι → β => ‖∏ i, h i (ξ i)‖) ∧
      ∑' ξ : ι → β, ∏ i, h i (ξ i) = ∏ i, ∑' b, h i b := by
  classical
  set n := Fintype.card ι
  let σ : ι ≃ Fin n := Fintype.equivFin ι
  obtain ⟨h1, h2⟩ := summable_norm_and_tsum_fin_prod n (fun j => h (σ.symm j)) (fun j => hs _)
  let e : (Fin n → β) ≃ (ι → β) := Equiv.arrowCongr σ.symm (Equiv.refl β)
  have hprod : ∀ η : Fin n → β, ∏ i, h i (e η i) = ∏ j, h (σ.symm j) (η j) := fun η => by
    refine (Fintype.prod_equiv σ _ _ fun i => ?_)
    simp [e, Equiv.arrowCongr_apply]
  constructor
  · rw [← e.summable_iff]
    convert h1 using 2 with η
    exact congrArg _ (hprod η)
  · rw [← e.tsum_eq]
    simp_rw [hprod]
    rw [h2]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl

end MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

/-- The summand $f_\infty(g_\infty\gamma)\prod_v f_v(g_v\gamma)$ of the left side of `adelicPoisson_smul`. -/
def twistedLHS (f : SchwartzMap V ℂ) (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (g : (Adeles F)ˣ) (γ : F) : ℂ :=
  f ((infPart g : V) * mixedEmbedding F γ) *
    ∏ᶠ v, fv v ((unitAt (finPart g) v : v.adicCompletion F) * algebraMap F _ γ)

/-- The summand $\hat f_\infty(g_\infty^{-1}\gamma)\prod_v\hat f_v(g_v^{-1}\gamma)$ of the right side of
`adelicPoisson_smul`. -/
def twistedRHS (f : SchwartzMap V ℂ) (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (g : (Adeles F)ˣ) (γ : F) : ℂ :=
  Analysis.fourierInf f (((infPart g)⁻¹ : Vˣ) * mixedEmbedding F γ) *
    ∏ᶠ v, Analysis.fourierV v (fv v)
      (((unitAt (finPart g) v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ)

section Vec

set_option synthInstance.maxHeartbeats 200000

variable {ι : Type} [Fintype ι]

/-- The $i$-th component $g_i\in\mathbb A_F^\times$ of $g\in(\mathbb A_F^\iota)^\times$. -/
abbrev unitComp (g : (AdeleSpace F ι)ˣ) (i : ι) : (Adeles F)ˣ := Units.map (Pi.evalMonoidHom _ i) g

/-- **Poisson summation on $\mathbb A_F^\iota$, twisted by $g\in(F^\iota\otimes\mathbb A)^\times$.** For each coordinate $i$ let $f_i$ be Schwartz on $F_\infty$ and $f_{i,v}$ Schwartz–Bruhat with
$f_{i,v} = \mathbf 1_{\mathcal O_v}$ off a finite set $S_i$. Then, with $\Phi = \bigotimes_i(f_i\otimes\bigotimes_vf_{i,v})$,
$$\sum_{\xi\in F^\iota}\prod_i\Phi_i(g_i\xi_i) = \|N_{A/F}(g)\|^{-1}_{\mathbb A}\sum_{\xi\in F^\iota}\prod_i\hat\Phi_i(g_i^{-1}\xi_i),$$
both sides absolutely convergent. -/
@[kb "weil1982" "§2.1 [unverified page]; Poisson as in casselsfrohlich1967 Ch. XV (Tate), Thm. 4.2.1 [unverified]"]
theorem adelicPoissonVec_smul (fv : ι → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (S : ι → Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ i, ∀ v ∈ S i, Analysis.IsSchwartzBruhatV v (fv i v))
    (hout : ∀ i, ∀ v ∉ S i, fv i v = Analysis.ballIndV v 0 0) (f : ι → SchwartzMap V ℂ)
    (g : (AdeleSpace F ι)ˣ) :
    ∑' ξ : ι → F, ∏ i, twistedLHS (f i) (fv i) (unitComp g i) (ξ i) =
      ((ideleNormVec g)⁻¹ : ℝ) • ∑' ξ : ι → F, ∏ i, twistedRHS (f i) (fv i) (unitComp g i) (ξ i) := by
  have hL : ∀ i, Summable fun γ => ‖twistedLHS (f i) (fv i) (unitComp g i) γ‖ := fun i =>
    summable_norm_iff.mpr (summable_adelicPoisson_smul_lhs (fv i) (S i) (hS i) (hout i) (f i) _)
  have hR : ∀ i, Summable fun γ => ‖twistedRHS (f i) (fv i) (unitComp g i) γ‖ := fun i =>
    summable_norm_iff.mpr (summable_adelicPoisson_smul_rhs (fv i) (S i) (hS i) (hout i) (f i) _)
  rw [(summable_norm_and_tsum_pi_prod _ hL).2, (summable_norm_and_tsum_pi_prod _ hR).2]
  have h1 : ∀ i, ∑' γ, twistedLHS (f i) (fv i) (unitComp g i) γ =
      (((ideleNorm F (unitComp g i))⁻¹ : ℝ) : ℂ) * ∑' γ, twistedRHS (f i) (fv i) (unitComp g i) γ :=
    fun i => by
      rw [← Complex.real_smul]
      exact adelicPoisson_smul (fv i) (S i) (hS i) (hout i) (f i) _
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Complex.real_smul, ideleNormVec]
  push_cast
  rw [Finset.prod_inv_distrib]

/-- Both sides of `adelicPoissonVec_smul` converge absolutely (the left side shown; the right side is the same
statement for the transforms). -/
theorem summable_adelicPoissonVec_smul_lhs (fv : ι → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (S : ι → Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ i, ∀ v ∈ S i, Analysis.IsSchwartzBruhatV v (fv i v))
    (hout : ∀ i, ∀ v ∉ S i, fv i v = Analysis.ballIndV v 0 0) (f : ι → SchwartzMap V ℂ)
    (g : (AdeleSpace F ι)ˣ) :
    Summable fun ξ : ι → F => ∏ i, twistedLHS (f i) (fv i) (unitComp g i) (ξ i) :=
by
  have h := (summable_norm_and_tsum_pi_prod (fun i γ => twistedLHS (f i) (fv i) (unitComp g i) γ) fun i =>
    summable_norm_iff.mpr (summable_adelicPoisson_smul_lhs (fv i) (S i) (hS i) (hout i) (f i) _)).1
  exact Summable.of_norm h

theorem summable_adelicPoissonVec_smul_rhs (fv : ι → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (S : ι → Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ i, ∀ v ∈ S i, Analysis.IsSchwartzBruhatV v (fv i v))
    (hout : ∀ i, ∀ v ∉ S i, fv i v = Analysis.ballIndV v 0 0) (f : ι → SchwartzMap V ℂ)
    (g : (AdeleSpace F ι)ˣ) :
    Summable fun ξ : ι → F => ∏ i, twistedRHS (f i) (fv i) (unitComp g i) (ξ i) :=
by
  have h := (summable_norm_and_tsum_pi_prod (fun i γ => twistedRHS (f i) (fv i) (unitComp g i) γ) fun i =>
    summable_norm_iff.mpr (summable_adelicPoisson_smul_rhs (fv i) (S i) (hS i) (hout i) (f i) _)).1
  exact Summable.of_norm h

end Vec

end

end QuadFormsKB.Tamagawa.Measure.Weil
