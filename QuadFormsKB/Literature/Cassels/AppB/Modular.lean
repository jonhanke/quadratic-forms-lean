/-
# Cassels, Appendix B, §5 (modular forms): formal Mellin transform, $\varepsilon(-1) = (-1)^k$, integer relations

Cassels, *Rational Quadratic Forms* (1978), Appendix B, §5, pp. 382-387.

**Formalized.**
* (5.2)-(5.3), p. 382: the Mellin transform of a power series $g(z) = \sum_{m \ge 0} g_m z^m$ is the formal Dirichlet series
  $\sum_{m \ge 1} g_m m^{-s}$, which ignores the constant term (`mellinFormal`, `mellinFormal_update_zero`). It is
  Mathlib's `LSeries` applied to the coefficient sequence $m \mapsto g_m$.
* (5.14), p. 385: if a nonzero modular form $\phi$ of weight $k$ for $\Gamma_1(N)$ satisfies the transformation law of
  $M(k, N, \varepsilon)$ for all of $\Gamma_0(N)$, then $\varepsilon(-1) = (-1)^k$ (`char_neg_one_eq_pow`). The library's
  law `Siegel.EisensteinWt2.IsModularFormWithChar` evaluates the character at the lower right entry $d$ of the matrix, while
  Cassels writes $\varepsilon(\sigma) = \varepsilon(a)$ (upper left entry); for $\sigma = -I$ both entries equal $-1$,
  and in general $ad \equiv 1 \pmod N$ on $\Gamma_0(N)$, so the two conventions differ by $\varepsilon \leftrightarrow
  \bar\varepsilon$ (not by anything affecting this statement). The space $M(k, N, \varepsilon)$ is packaged as the
  submodule `modularFormsWithChar`.
* (5.26), p. 387: if $J$ integer coefficient sequences all lie in a complex vector space of dimension less than $J$, then
  there is a nontrivial integer relation (`exists_int_relation`). Instantiation to modular forms for $\Gamma_1(N)$
  whose $q$-expansions have integer coefficients (`exists_int_relation_modularForm`,
  `exists_int_relation_modularFormsWithChar`), and to theta series of positive definite integral quadratic forms
  (`exists_int_relation_theta`), whose coefficients are the representation numbers (`qExpansion_thetaMFGamma1_coeff`).

**Not formalized / hypotheses.** Mathlib knows the finite dimensionality of spaces of modular forms only for level one
(`ModularForm 𝒮ℒ k`). Cassels' hypothesis "$J > \dim M(k, N, \varepsilon)$" is therefore kept as the explicit
hypothesis `finrank ℂ V < J` together with `FiniteDimensional ℂ V`, for $V$ any finite-dimensional subspace
(for instance $M(k, N, \varepsilon)$ once its finite dimensionality is available) containing the forms.

**Conventions.** Indices are 0-based: the coefficient sequence of a series $\sum_{m \ge 0} g_m z^m$ is `g : ℕ → ℂ` with
`g m` $= g_m$, and the $J$ forms $\Theta(f_1, t), \dots, \Theta(f_J, t)$ of the book are `f 0, …, f (J-1)` here.
-/
import QuadFormsKB.Siegel.EisensteinWt2.Forms
import QuadFormsKB.Siegel.ThetaGamma0
import QuadFormsKB.Siegel.Thm63Inputs
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import QuadFormsKB.Citation

open Complex ModularForm
open UpperHalfPlane (qExpansion)
open scoped UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Cassels

/-! ### (a) The formal Mellin transform -/

/-- **The formal Mellin transform** (Cassels, App. B, (5.2)-(5.3)): for a power series $g(z) = \sum_{m \ge 0} g_m z^m$ with
coefficient sequence `g : ℕ → ℂ` (`g m` $= g_m$), the formal Dirichlet series $\mathcal M(g)(s) = \sum_{m \ge 1} g_m m^{-s}$,
as a function of the complex variable `s`. This is Mathlib's `LSeries g`; the term at $m = 0$ is defined to be $0$, so the
constant term $g_0$ is ignored (`mellinFormal_update_zero`). -/
noncomputable abbrev mellinFormal (g : ℕ → ℂ) : ℂ → ℂ := LSeries g

/-- **The formal Mellin transform ignores the constant term** (Cassels, App. B, (5.2)-(5.3): "a purely formal operation that
ignores the constant term"). Arguments: `g`, the coefficient sequence; `c`, any replacement for the constant coefficient
$g_0$ (the function `Function.update g 0 c` changes only the entry at index $0$). -/
@[kb "cassels1978" "App. B, §5, (5.2)–(5.3), p. 382 (the Mellin transform of a power series)"]
theorem mellinFormal_update_zero (g : ℕ → ℂ) (c : ℂ) :
    mellinFormal (Function.update g 0 c) = mellinFormal g := by
  funext s
  unfold mellinFormal LSeries
  congr 1
  funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [LSeries.term_zero]
  · simp [LSeries.term_of_ne_zero hm.ne', Function.update_of_ne hm.ne']

/-! ### (b) The character at $-I$ -/

namespace Aux

open Siegel.EisensteinWt2

variable {N : ℕ} [NeZero N]

/-- Helper: slashing by $-I$ multiplies by $(-1)^k$ pointwise. -/
lemma slash_neg_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ k) • f := by
  ext τ
  rw [SL_slash_apply]
  have h1 : (-1 : SL(2, ℤ)) • τ = τ := by simp
  have h2 : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : SL(2, ℤ)) τ = -1 := by
    simp [UpperHalfPlane.denom]
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul, zpow_neg]
  rw [mul_comm]
  congr 1
  rw [← inv_zpow]; simp

end Aux

open Siegel.EisensteinWt2 in
/-- **$\varepsilon(-1) = (-1)^k$** (Cassels, App. B, (5.14), p. 385). Let $\phi$ = `f` be a nonzero modular form of weight `k`
for $\Gamma_1(N)$ that satisfies the transformation law of $M(k, N, \varepsilon)$ with the Dirichlet character
`χ` $= \varepsilon$ modulo $N$, i.e. `IsModularFormWithChar χ f` ($\phi|_k\sigma = \varepsilon(d)\phi$ for all
$\sigma \in \Gamma_0(N)$; Cassels evaluates at $a$, which agrees at $\sigma = -I$). Then $\varepsilon(-1) = (-1)^k$ in
$\mathbb C$. -/
@[kb "cassels1978" "App. B, §5, (5.14), p. 385"]
theorem char_neg_one_eq_pow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k) (hf : IsModularFormWithChar χ f) (hne : f ≠ 0) :
    χ (-1) = (-1 : ℂ) ^ k := by
  have hmem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have h := hf (-1) hmem
  rw [Aux.slash_neg_one] at h
  have hd : (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = -1 := by simp
  rw [hd] at h
  by_contra hcon
  apply hne
  ext τ
  have := congrFun h τ
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have hz : ((-1 : ℂ) ^ k - χ (-1)) * f τ = 0 := by rw [sub_mul]; linear_combination this
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hcon
  · simpa using h0

open Siegel.EisensteinWt2 in
/-- **The space $M(k, N, \varepsilon)$** (Cassels, App. B, (5.11)) as a complex subspace of Mathlib's modular forms for
$\Gamma_1(N)$: the forms satisfying `IsModularFormWithChar χ`. Arguments: `N`, the level; `χ`, the Dirichlet character
modulo $N$; `k`, the weight. (Mathlib has no spaces with character.) -/
noncomputable def modularFormsWithChar (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℤ) :
    Submodule ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k) where
  carrier := {f | IsModularFormWithChar χ f}
  zero_mem' := by
    intro γ _
    simp
  add_mem' := by
    intro f g hf hg γ hγ
    have h1 := hf γ hγ
    have h2 := hg γ hγ
    simp only [FunLike.coe_add, SlashAction.add_slash, h1, h2, smul_add]
  smul_mem' := by
    intro c f hf γ hγ
    have h1 := hf γ hγ
    simp only [FunLike.coe_smul, SL_smul_slash, h1, smul_comm c]

/-! ### (c) Integer relations among forms with integer coefficients -/

/-- **Integer relations from a dimension count** (the linear algebra behind Cassels, App. B, (5.26)). Let `θ 0, …, θ (J-1)` be
integer coefficient sequences (`θ j m` is the $m$-th coefficient of the $j$-th series) whose images in $\mathbb C$ lie in a
finite-dimensional complex subspace `W` of the space of coefficient sequences, with $\dim_{\mathbb C} W < J$. Then
there are integers `b 0, …, b (J-1)`, not all zero, with $\sum_j b_j\,\theta_j(m) = 0$ for every $m$. -/
@[kb "cassels1978" "App. B, §5, (5.26), p. 387 (a nontrivial integer relation when J exceeds the dimension)"]
theorem exists_int_relation {J : ℕ} (θ : Fin J → ℕ → ℤ) (W : Submodule ℂ (ℕ → ℂ)) [FiniteDimensional ℂ W]
    (hJ : Module.finrank ℂ W < J) (hW : ∀ j, (fun m => ((θ j m : ℤ) : ℂ)) ∈ W) :
    ∃ b : Fin J → ℤ, b ≠ 0 ∧ ∀ m, ∑ j, b j * θ j m = 0 := by
  classical
  by_contra hne
  push Not at hne
  -- truncation maps over ℚ
  let T : (M : ℕ) → (Fin J → ℚ) →ₗ[ℚ] (Fin M → ℚ) := fun M =>
    { toFun := fun c i => ∑ j, c j * ((θ j i : ℤ) : ℚ)
      map_add' := by intro c d; ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; ext i; simp [Finset.mul_sum, mul_assoc] }
  have hanti : ∀ M M', M ≤ M' → LinearMap.ker (T M') ≤ LinearMap.ker (T M) := by
    intro M M' hMM' c hc
    rw [LinearMap.mem_ker] at hc ⊢
    ext i
    have := congrFun hc ⟨i, lt_of_lt_of_le i.2 hMM'⟩
    simpa [T] using this
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ∀ M, Module.finrank ℚ (LinearMap.ker (T M₀)) ≤
      Module.finrank ℚ (LinearMap.ker (T M)) := by
    obtain ⟨_, ⟨M₀, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := ℕ))
      (Set.range fun M => Module.finrank ℚ (LinearMap.ker (T M))) ⟨_, ⟨0, rfl⟩⟩
    exact ⟨M₀, fun M => not_lt.mp (hmin _ ⟨M, rfl⟩)⟩
  -- the kernel at M₀ is trivial
  have hker : LinearMap.ker (T M₀) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    -- c satisfies all relations
    have hall : ∀ m : ℕ, ∑ j, c j * ((θ j m : ℤ) : ℚ) = 0 := by
      intro m
      have hle : LinearMap.ker (T (max M₀ (m + 1))) ≤ LinearMap.ker (T M₀) := hanti _ _ (le_max_left _ _)
      have heq : LinearMap.ker (T (max M₀ (m + 1))) = LinearMap.ker (T M₀) :=
        Submodule.eq_of_le_of_finrank_le hle (hM₀ _)
      have hc' : c ∈ LinearMap.ker (T (max M₀ (m + 1))) := heq ▸ hc
      rw [LinearMap.mem_ker] at hc'
      have := congrFun hc' ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _)⟩
      simpa [T] using this
    by_contra hc0
    -- clear denominators
    obtain ⟨d, hd0, hd⟩ : ∃ d : ℤ, d ≠ 0 ∧ ∀ j, ∃ z : ℤ, (d : ℚ) * c j = z := by
      refine ⟨∏ j, ((c j).den : ℤ), ?_, fun j => ?_⟩
      · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz
      · have hdvd : ((c j).den : ℤ) ∣ ∏ j, ((c j).den : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        obtain ⟨e, he⟩ := hdvd
        refine ⟨(c j).num * e, ?_⟩
        have hden : ((c j).den : ℚ) ≠ 0 := by exact_mod_cast (c j).den_nz
        have : ((∏ j, ((c j).den : ℤ) : ℤ) : ℚ) = ((c j).den : ℚ) * e := by exact_mod_cast congrArg (Int.cast (R := ℚ)) he
        rw [this]
        have hnd := Rat.num_div_den (c j)
        push_cast
        calc ((c j).den : ℚ) * e * c j = e * (((c j).den : ℚ) * c j) := by ring
          _ = e * (c j).num := by rw [mul_comm ((c j).den : ℚ), Rat.mul_den_eq_num]
          _ = _ := by ring
    choose z hz using hd
    obtain ⟨m, hm⟩ := hne z (by
      intro hz0
      apply hc0
      funext j
      have h1 := hz j
      rw [hz0] at h1
      simp at h1
      rcases h1 with h1 | h1
      · exact absurd (by exact_mod_cast h1) hd0
      · simpa using h1)
    apply hm
    have : ((∑ j, z j * θ j m : ℤ) : ℚ) = 0 := by
      push_cast
      calc ∑ j, (z j : ℚ) * (θ j m : ℚ) = ∑ j, (d : ℚ) * (c j * (θ j m : ℚ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hz j]; ring
        _ = (d : ℚ) * ∑ j, c j * (θ j m : ℚ) := by rw [Finset.mul_sum]
        _ = 0 := by rw [hall m, mul_zero]
    exact_mod_cast this
  -- ℚ-independence of the truncated sequences
  have hQ : LinearIndependent ℚ (fun j : Fin J => fun i : Fin M₀ => ((θ j i : ℤ) : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : g ∈ LinearMap.ker (T M₀) := by
      rw [LinearMap.mem_ker]
      ext i
      have := congrFun hg i
      simpa [T, mul_comm] using this
    rw [hker] at this
    intro j
    exact congrFun (Submodule.mem_bot ℚ |>.mp this) j
  have hC : LinearIndependent ℂ (fun j : Fin J => fun i : Fin M₀ => ((θ j i : ℤ) : ℂ)) := by
    have := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
      (v := fun j : Fin J => fun i : Fin M₀ => ((θ j i : ℤ) : ℚ))).mpr hQ
    convert this using 2 with j
    ext i
    simp
  -- lift to ℕ → ℂ and to W
  let R : (ℕ → ℂ) →ₗ[ℂ] (Fin M₀ → ℂ) := LinearMap.funLeft ℂ ℂ (fun i : Fin M₀ => (i : ℕ))
  have hu : LinearIndependent ℂ (fun j : Fin J => (fun m => ((θ j m : ℤ) : ℂ) : ℕ → ℂ)) := by
    refine LinearIndependent.of_comp R ?_
    exact hC
  have hW' : LinearIndependent ℂ (fun j : Fin J => (⟨_, hW j⟩ : W)) := by
    refine LinearIndependent.of_comp W.subtype ?_
    exact hu
  have := hW'.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

/-- Helper: the map sending a modular form for $\Gamma_1(N)$ to its sequence of $q$-expansion coefficients
(Mathlib's `qExpansion 1`), as a complex-linear map; injective by `ModularForm.qExpansion_injective`. -/
noncomputable def qCoeffLM (N : ℕ) (k : ℤ) :
    ModularForm (CongruenceSubgroup.Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun f m := (qExpansion 1 f).coeff m
  map_add' f g := by
    ext m
    have := ModularForm.qExpansion_add (h := 1) one_pos (Siegel.one_mem_strictPeriods_Gamma1 N) f g
    simp [this]
  map_smul' c f := by
    ext m
    have := ModularForm.qExpansion_smul (h := 1) one_pos (Siegel.one_mem_strictPeriods_Gamma1 N) c f
    simp [this]

/-- Helper: `qCoeffLM` is injective. -/
lemma qCoeffLM_injective (N : ℕ) (k : ℤ) : Function.Injective (qCoeffLM N k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  have h0 : qExpansion 1 f = 0 := by
    ext m
    simpa [qCoeffLM] using congrFun (LinearMap.mem_ker.mp hf) m
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (Siegel.one_mem_strictPeriods_Gamma1 N) f).mp h0

/-- **Integer relations among modular forms with integer $q$-expansions** (Cassels, App. B, (5.26), p. 387). Arguments: `N`
the level, `k` the weight, `f 0, …, f (J-1)` modular forms of weight `k` for $\Gamma_1(N)$ whose $q$-expansion coefficients
(Mathlib's `qExpansion 1`) are all integers (`hint`), `V` a finite-dimensional complex subspace containing every `f j`
(for instance $M(k, N, \varepsilon)$, `modularFormsWithChar`, when it is known to be finite-dimensional), with
$\dim V < J$. Then there are integers $b_j$, not all zero, with $\sum_j b_j f_j = 0$. -/
@[kb "cassels1978" "App. B, §5, (5.26), p. 387"]
theorem exists_int_relation_modularForm {N : ℕ} {k : ℤ} {J : ℕ}
    (f : Fin J → ModularForm (CongruenceSubgroup.Gamma1 N) k)
    (hint : ∀ j m, ∃ z : ℤ, (qExpansion 1 (f j)).coeff m = z)
    (V : Submodule ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) k)) [FiniteDimensional ℂ V]
    (hJ : Module.finrank ℂ V < J) (hV : ∀ j, f j ∈ V) :
    ∃ b : Fin J → ℤ, b ≠ 0 ∧ ∑ j, (b j : ℂ) • f j = 0 := by
  choose θ hθ using hint
  have : FiniteDimensional ℂ (V.map (qCoeffLM N k)) := Module.Finite.map V (qCoeffLM N k)
  have hle : Module.finrank ℂ (V.map (qCoeffLM N k)) ≤ Module.finrank ℂ V :=
    Submodule.finrank_map_le (qCoeffLM N k) V
  obtain ⟨b, hb0, hb⟩ := exists_int_relation θ (V.map (qCoeffLM N k)) (lt_of_le_of_lt hle hJ) (fun j => by
    refine ⟨f j, hV j, ?_⟩
    funext m
    simp [qCoeffLM, hθ])
  refine ⟨b, hb0, qCoeffLM_injective N k ?_⟩
  rw [map_sum, map_zero]
  funext m
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (hb m)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [qCoeffLM, hθ]

open Siegel.EisensteinWt2 in
/-- **(5.26) for $M(k, N, \varepsilon)$** (Cassels, App. B, p. 387): if `J` forms in $M(k, N, \varepsilon)$ (the subspace
`modularFormsWithChar N χ k`, assumed finite-dimensional, which is Cassels' dimension hypothesis) have integer
$q$-expansion coefficients and $J > \dim M(k, N, \varepsilon)$, there is a nontrivial integer relation among them. -/
@[kb "cassels1978" "App. B, §5, (5.26), p. 387"]
theorem exists_int_relation_modularFormsWithChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {k : ℤ} {J : ℕ}
    [FiniteDimensional ℂ (modularFormsWithChar N χ k)]
    (f : Fin J → ModularForm (CongruenceSubgroup.Gamma1 N) k) (hf : ∀ j, f j ∈ modularFormsWithChar N χ k)
    (hint : ∀ j m, ∃ z : ℤ, (qExpansion 1 (f j)).coeff m = z)
    (hJ : Module.finrank ℂ (modularFormsWithChar N χ k) < J) :
    ∃ b : Fin J → ℤ, b ≠ 0 ∧ ∑ j, (b j : ℂ) • f j = 0 :=
  exists_int_relation_modularForm f hint _ hJ hf

/-- **The $q$-expansion coefficients of $\Theta_Q$ on $\Gamma_1(N)$ are the representation numbers:** the $m$-th coefficient of
`qExpansion 1 (thetaMFGamma1 …)` is $r_Q(m)$ (`repNum Q m`, the number of $\vec x \in \mathbb Z^n$ with $Q(\vec x) = m$).
Arguments: `Q` the integral quadratic form in `n` variables, positive definite (`hQ`), `n = 2 * k` (`hn`), `hN0 : 0 < N`,
`hN` that `N` is a level of `Q`, `m` the index. -/
theorem qExpansion_thetaMFGamma1_coeff {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : Siegel.IsThetaLevel Q N) (m : ℕ) :
    (qExpansion 1 (Siegel.thetaMFGamma1 hQ hn hN0 hN)).coeff m = (Siegel.repNum Q m : ℂ) := by
  refine (ModularFormClass.qExpansion_coeff_unique (k := (k : ℤ)) (c := fun j => (Siegel.repNum Q j : ℂ))
    one_pos (Siegel.one_mem_strictPeriods_Gamma1 N) (f := Siegel.thetaMFGamma1 hQ hn hN0 hN) (fun τ => ?_) m).symm
  convert Siegel.hasSum_theta hQ τ.im_pos using 2 with j
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  · congr 2; push_cast; ring
  · exact Siegel.thetaMFGamma1_apply hQ hn hN0 hN τ

/-- **(5.26) for theta series** (Cassels, App. B, p. 387): let `Q 0, …, Q (J-1)` be positive definite integral quadratic
forms in `n = 2k` variables with common level `N`, and `V` a finite-dimensional complex subspace of the modular forms of
weight `k` for $\Gamma_1(N)$ containing every $\Theta_{Q_j}$ (`thetaMFGamma1`), for instance $M(k, N, \varepsilon)$ when the
character is $\varepsilon$ and its finite dimensionality is available, with $\dim V < J$. Then there are integers $b_j$, not all
zero, with $\sum_j b_j\Theta_{Q_j} = 0$; equivalently $\sum_j b_j r_{Q_j}(m) = 0$ for all $m$ (the coefficients are the
representation numbers, `qExpansion_thetaMFGamma1_coeff`). -/
@[kb "cassels1978" "App. B, §5, (5.26), p. 387 (theta series of forms of level N)"]
theorem exists_int_relation_theta {n : ℕ} {k : ℕ} (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N) {J : ℕ}
    (Q : Fin J → IntQF n) (hQ : ∀ j, (Q j).PosDef) (hN : ∀ j, Siegel.IsThetaLevel (Q j) N)
    (V : Submodule ℂ (ModularForm (CongruenceSubgroup.Gamma1 N) (k : ℤ))) [FiniteDimensional ℂ V]
    (hJ : Module.finrank ℂ V < J) (hV : ∀ j, Siegel.thetaMFGamma1 (hQ j) hn hN0 (hN j) ∈ V) :
    ∃ b : Fin J → ℤ, b ≠ 0 ∧ ∑ j, (b j : ℂ) • Siegel.thetaMFGamma1 (hQ j) hn hN0 (hN j) = 0 ∧
      ∀ m : ℕ, ∑ j, b j * (Siegel.repNum (Q j) m : ℤ) = 0 := by
  obtain ⟨b, hb0, hb⟩ := exists_int_relation_modularForm (fun j => Siegel.thetaMFGamma1 (hQ j) hn hN0 (hN j))
    (fun j m => ⟨Siegel.repNum (Q j) m, by rw [qExpansion_thetaMFGamma1_coeff]; simp⟩) V hJ hV
  refine ⟨b, hb0, hb, fun m => ?_⟩
  have h := congrArg (fun g => (qCoeffLM N (k : ℤ) g) m) hb
  simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    qCoeffLM, LinearMap.coe_mk, AddHom.coe_mk, qExpansion_thetaMFGamma1_coeff] at h
  have h' : ((∑ j, b j * (Siegel.repNum (Q j) m : ℤ) : ℤ) : ℂ) = 0 := by
    push_cast; simpa using h
  exact_mod_cast h'

end QuadFormsKB.Cassels
