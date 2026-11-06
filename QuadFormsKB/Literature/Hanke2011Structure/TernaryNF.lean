/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryTupleSum
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummedDirichlet
import QuadFormsKB.Literature.Hanke2011Ternary.NegOneHilbert
import QuadFormsKB.Literature.Hanke2011Ternary.TwoSplit
import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.Tamagawa.AlphaLawSplit

/-!
# Paper 6, Theorem 4.8 for the true ternary local genera over a number field $F$; paper 7, Theorem 8.1

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 4.8, p. 17, Rem. 4.14, p. 20, Cor. 6.4, p. 27; and J. Hanke,
*Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), §§2–8, Theorems 7.1 and 8.1, pp. 25–27.

This file is the number-field analogue of `TernaryAssembly.lean` (which treats $F = \mathbb Q$).

* **Part A** (`totalMassM_eq_half_nf`): Theorem 4.8 (sign-sum form, eqs. (11)–(12)) for the true local genera over any
  number field, $n = 3$, with arbitrary nonzero normalizing weights at the finitely many primes of a set $P$.
* **Part B** (`TernaryLocalTablesNF`, a **named input**): paper 7's local computations over the completions $F_{\mathfrak p}$
  for the true local genera: at $\mathfrak p \nmid 2$ the values of Table 2 (Thm. 2.4, with $q = N\mathfrak p$) for the
  normalized local mass sums $A^*_{\mathfrak p}$, $B^*_{\mathfrak p}$ and the unimodular case; at $\mathfrak p \mid 2$, when $2$
  splits completely (so $F_{\mathfrak p} \cong \mathbb Q_2$), Table 5.3 normalized by the generic density $3/16$. Over
  $\mathbb Q$ every field of this input is **proved** (`Odd7.*`, `Dyadic7.dyadicTernaryLocalMassTable_holds`); over $F$ the
  odd part needs the Conway–Sloane/Pall local mass formula over non-dyadic local fields (paper 7, Lemma 2.3), which is not
  generalized to number fields here, and the dyadic part needs the transport of the $\mathbb Q_2$ results along
  $F_{\mathfrak p} \cong \mathbb Q_2$.
* **Part C** (`hasProd_baseNF`): the generic density product $\beta^{-1}_{3,f} = 4^{[F:\mathbb Q]}\zeta_F(2)$ (Theorem 7.1, first
  claim; Rem. 4.14), from the Euler product of $\zeta_F$, **proved** given the local values $1 - q^{-2}$ and $3/16$.
* **Part D** (`totalMassM_ternary_nf`, `theorem_8_1_coeff`): $M^*_{1;3}(\lambda(\mathfrak a)) =
  2^{2[F:\mathbb Q]-1}\zeta_F(2)\,(A^*_3 + B^*_3)$ and **Theorem 8.1** coefficientwise, conditional on `TernaryLocalTablesNF`.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.NFEuler QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF

open Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "ordS" v => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-! ### Part A: Theorem 4.8 for the true local genera over $F$, $n = 3$ -/

section Assembly

/-- **The local density of a nondegenerate local genus is positive** (over any number field). -/
theorem LocGenus.beta_pos_nf (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v 3) (hG : G.Nondeg) : 0 < G.beta := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  have hne : Q.hessian.det ≠ 0 := (LocGenus.nondeg_mk Q).mp hG
  have hpos := Tamagawa.localDensityForm_self_pos' v Q hne
  rw [LocGenus.beta_mk]
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v Q hne]
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  unfold LocalDensity.DVR.siegelDensity
  simp only [ite_true]
  exact mul_pos (pow_pos h2 _) (mul_pos (by norm_num) hpos)

/-- **The Hasse invariant of a ternary local genus is $\pm 1$** (over any number field). -/
theorem LocGenus.hasse_pm_nf (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v 3) : G.hasse = 1 ∨ G.hasse = -1 := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  rw [LocGenus.hasse_mk]
  exact Composition.hasseC_pm _

/-- The admissible ternary local genera at $\mathfrak p$ for the adelic squareclass $S$: nondegenerate, primitive,
$\det_H = S_{\mathfrak p}$ (the set $\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},+;3)\cup\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},-;3)$). -/
def admGenF (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) : Set (LocGenus v 3) :=
  {G | G.Nondeg ∧ G.Prim ∧ G.det = AdelicSqCl.comp v S}

theorem admGenF_eq_union (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    admGenF S v = {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} ∪
      {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
  ext G
  simp only [admGenF, LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_union]
  rcases LocGenus.hasse_pm_nf v G with h | h <;> simp [h]

theorem finsum_admGenF_split (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) (f : LocGenus v 3 → ℝ)
    (hfin : (admGenF S v).Finite) :
    ∑ᶠ G ∈ admGenF S v, f G = (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) +
      ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have hD : Disjoint {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}
      {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
    rw [Set.disjoint_left]
    rintro G ⟨-, -, -, h1⟩ ⟨-, -, -, h2⟩
    rw [h1] at h2; exact absurd h2 (by decide)
  rw [admGenF_eq_union] at hfin ⊢
  exact finsum_mem_union hD (hfin.subset Set.subset_union_left) (hfin.subset Set.subset_union_right)

theorem finsum_admGenF_split_hasse (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) (f : LocGenus v 3 → ℝ)
    (hfin : (admGenF S v).Finite) :
    ∑ᶠ G ∈ admGenF S v, ((G.hasse : ℤ) : ℝ) * f G =
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) -
        ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have h2fin : {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}.Finite := by
    rw [admGenF_eq_union] at hfin; exact hfin.subset Set.subset_union_right
  rw [finsum_admGenF_split S v _ hfin, sub_eq_add_neg, ← finsum_mem_neg_distrib _ h2fin]
  congr 1
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp

/-- **Theorem 4.8 for the true ternary local genera over $F$** (sign-sum form, proof of Thm. 4.8, eqs. (11)–(12)): let
$(b_{\mathfrak p})$ be a tuple of local genera that is the only admissible genus outside a finite set $P$, with
$c_{\mathfrak p}(b_{\mathfrak p}) = 1$ there; let $w_{\mathfrak p} \ne 0$ be weights with $w_{\mathfrak p} = \beta(b_{\mathfrak p})$ for
$\mathfrak p \notin P$ and $\prod_{\mathfrak p}w_{\mathfrak p}^{-1} = C$. Then
$$M^*_{1;3}(S) = C\cdot\frac12\Bigl[\prod_{\mathfrak p\in P}\sum_{G}\frac{w_{\mathfrak p}}{\beta(G)} +
\prod_{\mathfrak p\in P}\sum_{G}c_{\mathfrak p}(G)\frac{w_{\mathfrak p}}{\beta(G)}\Bigr],$$
the sums over the admissible genera at $\mathfrak p$. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, and its proof, eqs. (11)-(12), p. 18 (n = 3, true local genera over F)"]
theorem totalMassM_eq_half_nf (S : AdelicSqCl F) (P : Finset (HeightOneSpectrum (𝓞 F))) (b : LocTuple F 3)
    (w : HeightOneSpectrum (𝓞 F) → ℝ) (C : ℝ)
    (hout : ∀ v ∉ P, admGenF S v = {b v}) (hb1 : ∀ v ∉ P, (b v).hasse = 1)
    (hw : ∀ v ∉ P, w v = (b v).beta) (hw0 : ∀ v, w v ≠ 0)
    (hfin : ∀ v ∈ P, (admGenF S v).Finite) (hprod : HasProd (fun v => (w v)⁻¹) C) :
    totalMassM 3 S 1 ∅ (fun _ => 1) = C * ((∏ v ∈ P, ∑ᶠ G ∈ admGenF S v, w v / G.beta) +
      ∏ v ∈ P, ∑ᶠ G ∈ admGenF S v, ((G.hasse : ℤ) : ℝ) * (w v / G.beta)) / 2 := by
  unfold totalMassM
  have hgen : (GenStarF S 1 ∅ (fun _ => 1) : Set (LocTuple F 3)) =
      {t | (∀ v, t v ∈ admGenF S v) ∧ (Function.mulSupport fun v => (t v).hasse).Finite ∧
        ∏ᶠ v, (t v).hasse = 1} := by
    ext t; simp [GenStarF, admGenF]
  rw [hgen]
  have hT : ∀ t ∈ {t : LocTuple F 3 | (∀ v, t v ∈ admGenF S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1},
      invDensityTuple t = C * ∏ v ∈ P, w v / (t v).beta := by
    rintro t ⟨hA, -⟩
    have hout' : ∀ v ∉ P, (t v).beta = w v := fun v hv => by
      have h := hA v
      rw [hout v hv] at h
      rw [Set.mem_singleton_iff.mp h, hw v hv]
    obtain ⟨hm, he⟩ := invDensity_factor P w (fun v => (t v).beta) hout' hw0
      (fun v => (LocGenus.beta_pos_nf v _ (hA v).1).ne') hprod.multipliable
    unfold invDensityTuple
    rw [if_pos hm, he, hprod.tprod_eq]
  rw [finsum_mem_congr rfl hT, ← mul_finsum_mem,
    finsum_tuple_sign P b (admGenF S) (fun v G => G.hasse) (fun v G => w v / G.beta) hout hb1 hfin
      (fun v G => LocGenus.hasse_pm_nf v G)]
  ring

end Assembly

/-! ### Part B: the named local input over $F$ -/

/-- The integer $\pm1$ as a unit (`1` for `1`, `-1` otherwise). -/
def toSign (z : ℤ) : ℤˣ := if z = 1 then 1 else -1

theorem toSign_val {z : ℤ} (hz : z = 1 ∨ z = -1) : ((toSign z : ℤˣ) : ℤ) = z := by
  rcases hz with rfl | rfl <;> simp [toSign]

/-- **Paper 7's local computations over the completions of $F$, for the true ternary local genera** (named input; Hanke 2011,
ternary paper, Thm. 2.4 / Table 2 (with Lemmas 2.1–2.3) at $\mathfrak p \nmid 2$ and Lemmas 5.1–5.2 / Table 5.3 at
$\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb Q_2$). For $S_{\mathfrak p} \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ with
$\nu = \operatorname{ord}_{\mathfrak p}S_{\mathfrak p} \ge 0$ and $\mathrm{Gen}^{*}_{\mathfrak p}(S_{\mathfrak p},\pm;3)$ the primitive nondegenerate ternary
local genera of Hessian determinant $S_{\mathfrak p}$ and Hasse invariant $\pm1$:

* `fin`: each $\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},\pm;3)$ is finite;
* `odd_A`, `odd_B` ($\mathfrak p \nmid 2$, $q = N\mathfrak p$): $\sum_{G\in\mathrm{Gen}^{*,+}}\frac{1-q^{-2}}{\beta(G)} \pm
  \sum_{G\in\mathrm{Gen}^{*,-}}\frac{1-q^{-2}}{\beta(G)}$ equals $A^*(q,\varepsilon',\nu)$, resp. $B^*(q,\varepsilon',\nu)$ of Table 2
  (`Astar`, `Bstar`), $\varepsilon' = \left(\frac{-1}{\mathfrak p}\right)$;
* `odd_unimod` ($\mathfrak p \nmid 2$, $\nu = 0$): one genus, of Hasse invariant $1$ and density $1 - q^{-2}$;
* `dy_zero`, `dy_A`, `dy_B` ($\mathfrak p \mid 2$, **when $2$ splits completely in $F$**): no genus for $\nu = 0$; for
  $\nu \ge 1$ the sums normalized by $3/16$ are `dyadicA ν` and `dyadicB ε ν` with $\varepsilon = (-1, x)_{\mathfrak p}$ for
  any $x \in F_{\mathfrak p}^\times$ in the rational square class of $S_{\mathfrak p}$ (Table 5.3).

Over $\mathbb Q$ all fields are proved (`Odd7.odd_finite`, `odd_A`, `odd_B`, `odd_unimodular`,
`Dyadic7.dyadicTernaryLocalMassTable_holds`). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7; §5, Lemmas 5.1-5.2, Table 5.3, pp. 19-21 (over F_p)"]
structure TernaryLocalTablesNF (F : Type) [Field F] [NumberField F] : Prop where
  fin : ∀ (v : HeightOneSpectrum (𝓞 F)) (S : LocalSqCl v) (c : ℤ), {G : LocGenus v 3 | G.IsGenStar S c}.Finite
  odd_A : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ S : LocalSqCl v, 0 ≤ (ordS v) S →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Astar (qv v) (epsOdd v) ((ordS v) S).toNat 1 : ℚ) : ℝ)
  odd_B : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ S : LocalSqCl v, 0 ≤ (ordS v) S →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Bstar (qv v) (epsOdd v) ((ordS v) S).toNat 1 : ℚ) : ℝ)
  odd_unimod : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ S : LocalSqCl v, (ordS v) S = 0 →
    {G : LocGenus v 3 | G.IsGenStar S (-1)} = ∅ ∧
      ∃ G₀ : LocGenus v 3, {G : LocGenus v 3 | G.IsGenStar S 1} = {G₀} ∧ G₀.beta = 1 - ((qv v : ℝ) ^ 2)⁻¹
  dy_zero : TwoSplitsCompletely F → ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → ∀ S : LocalSqCl v,
    (ordS v) S = 0 → ∀ c : ℤ, {G : LocGenus v 3 | G.IsGenStar S c} = ∅
  dy_A : TwoSplitsCompletely F → ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → ∀ S : LocalSqCl v,
    1 ≤ (ordS v) S →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (3 / 16 : ℝ) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (3 / 16 : ℝ) / G.beta) =
      ((dyadicA ((ordS v) S).toNat : ℚ) : ℝ)
  dy_B : TwoSplitsCompletely F → ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → ∀ S : LocalSqCl v,
    1 ≤ (ordS v) S → ∀ x : (v.adicCompletion F)ˣ, rhoLocal v S = SqCl.mk x →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (3 / 16 : ℝ) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (3 / 16 : ℝ) / G.beta) =
      ((dyadicB (toSign (hilbertSymbol (v.adicCompletion F) (-1) (x : v.adicCompletion F)))
        ((ordS v) S).toNat : ℚ) : ℝ)

/-! ### Part C: the generic density product $4^{[F:\mathbb Q]}\zeta_F(2)$ -/

/-- The base (generic) local densities for $n = 3$: $\beta_{3,\mathfrak p} = 1 - q^{-2}$ at $\mathfrak p \nmid 2$ and $3/16$ at
$\mathfrak p \mid 2$ ($F_{\mathfrak p} = \mathbb Q_2$; Rem. 4.14, Table 2 case 1 and Table 5.3 case 5 of paper 7). -/
def wbase (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (2 : 𝓞 F) ∈ v.asIdeal then 3 / 16 else 1 - ((qv v : ℝ) ^ 2)⁻¹

theorem wbase_ne_zero (v : HeightOneSpectrum (𝓞 F)) : wbase v ≠ 0 := by
  unfold wbase
  split_ifs
  · norm_num
  · have h : (2 : ℝ) ≤ qv v := by exact_mod_cast one_lt_qv v
    have : ((qv v : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    linarith

/-- **Theorem 7.1, first claim** (Hanke 2011, ternary paper, p. 26; paper 6, Rem. 4.14): if every prime above $2$ has norm
$2$, $\prod_{\mathfrak p}\beta_{3,\mathfrak p}^{-1} = 4^{\#\{\mathfrak p\mid2\}}\zeta_F(2)$, i.e. $\beta^{-1}_{3,f} = 4^{[F:\mathbb Q]}\zeta_F(2)$ when
$2$ splits completely. -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26 (generic density product)"]
theorem hasProd_baseNF (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => (wbase v)⁻¹) (4 ^ numDyadic F * dedekindZetaR F 2) := by
  have h0 := hasProd_dedekindZeta (F := F) (s := 2) (by norm_num)
  have hc : HasProd (fun v : HeightOneSpectrum (𝓞 F) => if (2 : 𝓞 F) ∈ v.asIdeal then (4 : ℝ) else 1)
      (4 ^ numDyadic F) := by
    have : HasProd (fun v : HeightOneSpectrum (𝓞 F) => if (2 : 𝓞 F) ∈ v.asIdeal then (4 : ℝ) else 1)
        (∏ v ∈ finite_dyadic.toFinset, if (2 : 𝓞 F) ∈ v.asIdeal then (4 : ℝ) else 1) :=
      hasProd_prod_of_ne_finset_one (fun v hv => by
        rw [Set.Finite.mem_toFinset] at hv; exact if_neg hv)
    rw [Finset.prod_congr rfl (g := fun _ => (4 : ℝ)) fun v hv => by
      rw [Set.Finite.mem_toFinset] at hv; exact if_pos hv, Finset.prod_const] at this
    exact this
  have h := hc.mul h0
  refine h.congr_fun fun v => ?_
  have hrp : ((normP v : ℕ) : ℝ) ^ (-(2 : ℝ)) = ((qv v : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; rfl
  simp only [wbase, hrp]
  split_ifs with hv
  · rw [h2 v hv]; norm_num
  · rw [one_mul]

/-! ### Part D: $M^*_{1;3}(\lambda(\mathfrak a))$ and Theorem 8.1 -/

/-- $\varepsilon_{\mathfrak p} = (-1,\alpha)_{\mathfrak p}$ as a unit. -/
def epsAlpha (α : Fˣ) : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ :=
  fun _ v => toSign ((NFPlace.finite v).hilbert (-1 : F) (α : F))

theorem ordS_comp_lam (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) (v : HeightOneSpectrum (𝓞 F)) :
    (ordS v) (AdelicSqCl.comp v (lam.toHom a)) = (ordI v a : ℤ) := by
  have := lam.ord_eq a v
  rw [ordI_eq_idealOrd]; exact this

theorem dyadicA_zero' : dyadicA 0 = 0 := by rw [dyadicA_eq_coeff]; simp
theorem dyadicB_zero' (ε : ℤˣ) : dyadicB ε 0 = 0 := by rw [dyadicB_eq_coeff]; simp

theorem locA_zero (v : HeightOneSpectrum (𝓞 F)) (hv : (2 : 𝓞 F) ∉ v.asIdeal) : locA v 0 = 1 := by
  rw [locA, if_neg hv, Astar_eq_coeff_EA (one_lt_qv_rat v)]; simp [constantCoeff_EA]

theorem locB_zero (v : HeightOneSpectrum (𝓞 F)) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (ε : ℤˣ) : locB v ε 0 = 1 := by
  have h := Bstar_eq_coeff_EB (one_lt_qv_rat v) (epsOdd v) 0
  rw [pow_zero, one_mul] at h
  rw [locB, if_neg hv, h]; simp [constantCoeff_EB]

/-- **Theorem 4.8 with Remark 4.14 for the true ternary local genera over $F$, from paper 7's local tables:** if $2$
splits completely in $F$ and $\lambda(\mathfrak a)$ is the square class of $\alpha \in F^\times$ at every prime,
$$M^*_{1;3}(\lambda(\mathfrak a)) = 4^{[F:\mathbb Q]}\zeta_F(2)\cdot\tfrac12\bigl(A^*_3(\mathfrak a) + B^*_3(\mathfrak a)\bigr),$$
$A^*_3$, $B^*_3$ the coefficients of $D_{A^*,\lambda;3}$, $D_{B^*,\lambda;3}$ (`coeffA`, `coeffB` with $\varepsilon_{\mathfrak p} = (-1,\alpha)_{\mathfrak p}$),
given the named input `TernaryLocalTablesNF`. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, Cor. 4.15, p. 20; hanke2011ternary §7, Thm. 7.1 (n = 3, over F)"]
theorem totalMassM_ternary_nf (H : TernaryLocalTablesNF F) (hs : TwoSplitsCompletely F) (lam : DistinguishedFamily F)
    (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α)) :
    totalMassM 3 (lam.toHom a) 1 ∅ (fun _ => 1) =
      4 ^ numDyadic F * dedekindZetaR F 2 * ((coeffA a + coeffB (epsAlpha α) a : ℚ) : ℝ) / 2 := by
  set S := lam.toHom a with hS
  set P := (finite_bad a).toFinset with hP
  have hmemP : ∀ v, v ∉ P → (2 : 𝓞 F) ∉ v.asIdeal ∧ ordI v a = 0 := fun v hv => by
    rw [Set.Finite.mem_toFinset] at hv
    simp only [Set.mem_setOf_eq, not_or, not_not] at hv
    exact hv
  have hord := ordS_comp_lam lam a
  -- the base tuple
  have hbase : ∀ v, ∃ G : LocGenus v 3, v ∉ P → admGenF S v = {G} ∧ G.hasse = 1 ∧ G.beta = wbase v := by
    intro v
    by_cases hv : v ∈ P
    · exact ⟨LocGenus.mk ⟨0, fun _ _ _ => rfl⟩, fun h => absurd hv h⟩
    · obtain ⟨h2, h0⟩ := hmemP v hv
      obtain ⟨he, G₀, hs1, hb⟩ := H.odd_unimod v h2 _ (by rw [hord, h0]; rfl)
      have hmem : G₀ ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} := by rw [hs1]; rfl
      refine ⟨G₀, fun _ => ⟨?_, hmem.2.2.2, by rw [hb, wbase, if_neg h2]⟩⟩
      rw [admGenF_eq_union, hs1, he, Set.union_empty]
  choose b hb using hbase
  have hfin : ∀ v ∈ P, (admGenF S v).Finite := fun v _ => by
    rw [admGenF_eq_union]; exact (H.fin v _ 1).union (H.fin v _ (-1))
  rw [totalMassM_eq_half_nf S P b wbase _ (fun v hv => (hb v hv).1) (fun v hv => (hb v hv).2.1)
    (fun v hv => (hb v hv).2.2.symm) wbase_ne_zero hfin (hasProd_baseNF hs.qv_eq_two)]
  -- the local factors
  have hloc : ∀ v ∈ P, (∑ᶠ G ∈ admGenF S v, wbase v / G.beta) = ((locA v (ordI v a) : ℚ) : ℝ) ∧
      (∑ᶠ G ∈ admGenF S v, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta)) =
        ((locB v (epsAlpha α a v) (ordI v a) : ℚ) : ℝ) := by
    intro v hvP
    rw [finsum_admGenF_split S v _ (hfin v hvP), finsum_admGenF_split_hasse S v _ (hfin v hvP)]
    by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
    · simp only [wbase, if_pos h2, locA, locB]
      by_cases h0 : ordI v a = 0
      · have e1 := H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) 1
        have e2 := H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) (-1)
        rw [e1, e2, h0, dyadicA_zero', dyadicB_zero']
        simp
      · have h1 : 1 ≤ (ordS v) (AdelicSqCl.comp v S) := by rw [hord]; omega
        refine ⟨?_, ?_⟩
        · rw [H.dy_A hs v h2 _ h1, hord, Int.toNat_natCast]
        · rw [H.dy_B hs v h2 _ h1 (unitsToLocal v α) (hα v), hord, Int.toNat_natCast]
          simp only [epsAlpha, NFPlace.hilbert, map_neg, map_one]
          rfl
    · simp only [wbase, if_neg h2, locA, locB]
      have hnn : 0 ≤ (ordS v) (AdelicSqCl.comp v S) := by rw [hord]; positivity
      have hA := H.odd_A v h2 _ hnn
      have hB := H.odd_B v h2 _ hnn
      rw [hord, Int.toNat_natCast] at hA hB
      exact ⟨hA, hB⟩
  rw [Finset.prod_congr rfl fun v hv => (hloc v hv).1, Finset.prod_congr rfl fun v hv => (hloc v hv).2]
  have hA : coeffA a = ∏ v ∈ P, locA v (ordI v a) := by
    unfold coeffA
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hn
    obtain ⟨h2, h0⟩ := hmemP v hn
    exact hv (by simp only; rw [h0, locA_zero v h2])
  have hB : coeffB (epsAlpha α) a = ∏ v ∈ P, locB v (epsAlpha α a v) (ordI v a) := by
    unfold coeffB
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hn
    obtain ⟨h2, h0⟩ := hmemP v hn
    exact hv (by simp only; rw [h0, locB_zero v h2])
  rw [hA, hB]
  push_cast
  ring

/-- **Parity of the order of a global representative:** if $\lambda(\mathfrak a)_{\mathfrak p}$ and $\alpha$ have the same rational
square class in $F_{\mathfrak p}$, then $\operatorname{ord}_{\mathfrak p}\alpha \equiv \operatorname{ord}_{\mathfrak p}\mathfrak a \pmod 2$
(`ordL` is minus the order). -/
theorem even_ordL_add_ordI (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) (α : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hα : rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α)) :
    Even (SqDual.ordL v α + (ordI v a : ℤ)) := by
  obtain ⟨x, hx⟩ := SqCl.mk_surjective (AdelicSqCl.comp v (lam.toHom a))
  have hord := ordS_comp_lam lam a v
  rw [← hx, SqCl.ordZ_mk] at hord
  rw [← hx, rhoLocal_mk] at hα
  obtain ⟨y, -, hy⟩ := QuotientGroup.eq.mp hα
  have h1 := congrArg (fun z => Multiplicative.toAdd (localOrd v z)) hy
  simp only [powMonoidHom_apply, map_pow, map_mul, map_inv, toAdd_pow, toAdd_mul, toAdd_inv] at h1
  have hαv : Multiplicative.toAdd (localOrd v (unitsToLocal v α)) = -SqDual.ordL v α := by
    show -WithZero.log (Valued.v ((unitsToLocal v α : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = _
    rw [show ((unitsToLocal v α : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (α : F) from rfl, HN.valued_algebraMap]
    rfl
  rw [hαv, hord, nsmul_eq_mul] at h1
  push_cast at h1
  exact ⟨-Multiplicative.toAdd (localOrd v y), by linarith⟩

theorem unit_zpow_eq_pow_of_even (e : ℤˣ) (m : ℤ) (k : ℕ) (h : Even (m + (k : ℤ))) : e ^ m = e ^ k := by
  obtain ⟨j, hj⟩ := h
  have hm : m = (j + j) - k := by omega
  have he2 : e ^ (2 : ℤ) = 1 := by rcases Int.units_eq_one_or e with rfl | rfl <;> decide
  rw [hm, zpow_sub, show j + j = 2 * j by ring, zpow_mul, he2, one_zpow, one_mul, zpow_natCast]
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp
  · rw [Int.units_inv_eq_self]

/-- The Hilbert symbol $(a, b)_K = 1$ when $b \ne 0$ is a square in $K$ ($z^2 = a\cdot0^2 + b\cdot1^2$). -/
theorem hilbertSymbol_of_isSquare_right (K : Type*) [Field K] (a b : K) (hb : IsSquare b) : hilbertSymbol K a b = 1 := by
  obtain ⟨s, hs⟩ := hb
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨0, 1, s, by simp [Prod.ext_iff], by rw [hs]; ring⟩

theorem epsInf_totPosSig_three : epsInf (totPosSig F 3) = 1 := by
  simp [epsInf, totPosSig, hasseReal]

/-- **Theorem 8.1, primitive formula, coefficientwise** (Hanke 2011, ternary paper, p. 27), for a totally real number field
$F$ in which $2$ splits completely, the totally positive definite signature, and $\lambda(\mathfrak a)$ globally rational with a
totally positive representative $\alpha$: the total mass of the primitive $\mathcal O_F$-valued ternary lattices of Hessian
determinant squareclass $\lambda(\mathfrak a)$ is
$$\sum_{L}\frac1{|\mathrm{Aut}(L)|} = \frac{|\Delta_F|^{3/2}}{(64\pi^2)^{[F:\mathbb Q]}}\,N(\mathfrak a)^2\cdot
\frac{4^{[F:\mathbb Q]}\zeta_F(2)}{2}\Bigl([\mathfrak a^{-s}]\frac{\zeta_F(s+1)\zeta_F(2s+3)}{N(2\mathcal O_F)^s\zeta_F(3s+6)} +
(-1)^{[F:\mathbb Q]}[\mathfrak a^{-s}]\frac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^s\zeta_F(3s+6)}\Bigr),$$
the coefficient of $N(\mathfrak a)^{-s}$ in the paper's
$\frac{|\Delta_F|^{3/2}\zeta_F(2)}{2(\pi^2 2^{s+2})^{[F:\mathbb Q]}}\bigl[\frac{\zeta_F(s-1)\zeta_F(2s-1)}{\zeta_F(3s)} +
\varepsilon\frac{\zeta_F(2s-2)\zeta_F(s)}{\zeta_F(3s)}\bigr]$, $\varepsilon = (-1)^{[F:\mathbb Q]}$ (the shift $s \mapsto s-2$ gives
$N(\mathfrak a)^2$ and $N(2\mathcal O_F)^{2} = 4^{[F:\mathbb Q]}$). Conditional on the named input `TernaryLocalTablesNF`.
*Scope:* the paper allows any totally definite signature vector; this statement is for the totally positive definite one
(the case of paper 6's Cor. 6.4 formalized as `cor_6_4_coeff`). -/
@[kb "hanke2011ternary" "§8, Thm. 8.1, p. 27 (primitive formula, coefficientwise; F totally real, 2 split completely)"]
theorem theorem_8_1_coeff [IsTotallyReal F] (H : TernaryLocalTablesNF F) (hs : TwoSplitsCompletely F)
    (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenStar (lam.toHom a) (totPosSig F 3) ∅ (fun _ => 1),
        massOfTuple (lam.toHom a) (totPosSig F 3) ∅ (fun _ => 1) t =
      |(discr F : ℝ)| ^ ((3 : ℝ) / 2) / (64 * Real.pi ^ 2) ^ Module.finrank ℚ F *
        (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 *
        (4 ^ Module.finrank ℚ F * dedekindZetaR F 2 / 2) *
        ((eulerCoeff EA a + (-1) ^ Module.finrank ℚ F * eulerCoeff EB a : ℚ) : ℝ) := by
  have hc := cor_6_4_coeff (n := 3) (by norm_num) lam ∅ (fun _ => 1) a α hα hsign
  rw [epsInf_totPosSig_three, totalMassM_ternary_nf H hs lam a α hα, volV_three] at hc
  rw [hc]
  have hA := theorem_7_1_A hs.qv_eq_two a
  have hodd : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal →
      (NFPlace.finite v).hilbert (-1 : F) (α : F) = ((epsOdd v ^ ordI v a : ℤˣ) : ℤ) := fun v h2 => by
    rw [hilbert_neg_one_nondyadic v h2 α, unit_zpow_eq_pow_of_even _ _ _ (even_ordL_add_ordI lam a α v (hα v))]
  have hdy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal →
      ((epsAlpha α a v : ℤˣ) : ℤ) = (NFPlace.finite v).hilbert (-1 : F) (α : F) := fun v _ =>
    toSign_val (NFPlace.hilbert_eq_one_or _ _ _)
  have hB := theorem_7_1_B hs.qv_eq_two (epsAlpha α) a α hodd hdy
  have hinf : ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) = 1 :=
    Finset.prod_eq_one fun w _ => hilbertSymbol_of_isSquare_right _ _ _ (hsign ⟨w, IsTotallyReal.isReal w⟩)
  rw [hA, hB, hinf, mul_one, hs.numDyadic_eq]
  have e1 : (3 : ℝ) * (3 - 1) / 4 = 3 / 2 := by norm_num
  have e2 : ((2 : ℝ) ^ ((3 : ℝ) * (3 + 1) / 2)) = 64 := by
    rw [show (3 : ℝ) * (3 + 1) / 2 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have e3 : (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ (((3 : ℝ) + 1) / 2) =
      (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 := by
    rw [show ((3 : ℝ) + 1) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  push_cast
  ring

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.totalMassM_eq_half_nf
#print axioms QuadFormsKB.Hanke2011Structure.hasProd_baseNF
#print axioms QuadFormsKB.Hanke2011Structure.totalMassM_ternary_nf
#print axioms QuadFormsKB.Hanke2011Structure.theorem_8_1_coeff
