/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryNF

/-!
# Paper 6, Theorem 4.8 for the true local genera of every rank $n$ over a number field

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 4.8, p. 17, and its proof, eqs. (6)–(12), pp. 17–18.

The rank-$n$ form of `totalMassM_eq_half_nf` (`TernaryNF.lean`, $n = 3$): for the **true** local genera
(`LocGenus`: $\mathcal O_{\mathfrak p}$-valued forms up to $\mathrm{GL}_n(\mathcal O_{\mathfrak p})$, with Hanke's local density) over any
number field $F$, every rank $n$, the primitive total adelic mass $M^*_{1;n}(S)$ (Def. 3.5, `totalMassM`, $\varepsilon_\infty = 1$,
$\mathbb S = \emptyset$) is
$$M^*_{1;n}(S) = C\cdot\frac12\Bigl[\prod_{\mathfrak p\in P}\sum_G\frac{w_{\mathfrak p}}{\beta(G)} +
\prod_{\mathfrak p\in P}\sum_G c_{\mathfrak p}(G)\frac{w_{\mathfrak p}}{\beta(G)}\Bigr]$$
(`totalMassM_eq_half_rank`), for a tuple $(b_{\mathfrak p})$ of local genera that is the only admissible genus outside the finite
set $P$, with $c_{\mathfrak p}(b_{\mathfrak p}) = 1$ there, weights $w_{\mathfrak p} \ne 0$ with $w_{\mathfrak p} = \beta(b_{\mathfrak p})$ outside
$P$ and $\prod_{\mathfrak p}w_{\mathfrak p}^{-1} = C$; the sums run over the admissible genera at $\mathfrak p$ (`admGenRank`:
nondegenerate, primitive, $\det_H = S_{\mathfrak p}$). The two inner sums are $A^*_{\mathfrak p;n}(S_{\mathfrak p})$ and
$B^*_{\mathfrak p;n}(S_{\mathfrak p})$ of Definition 4.6 when $w_{\mathfrak p} = \beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})$
(`sum_admGenRank_split`, `sum_admGenRank_split_hasse`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset

namespace QuadFormsKB.Hanke2011Structure

open Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The local density of a nondegenerate local genus is positive** (every rank, every number field). -/
theorem LocGenus.beta_pos_rank (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) (hG : G.Nondeg) : 0 < G.beta := by
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

/-- **The Hasse invariant of a local genus is $\pm 1$** (every rank, every number field). -/
theorem LocGenus.hasse_pm_rank (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) : G.hasse = 1 ∨ G.hasse = -1 := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  rw [LocGenus.hasse_mk]
  exact Composition.hasseC_pm _

variable (n) in
/-- The admissible local genera of rank $n$ at $\mathfrak p$ for the non-archimedean squareclass $S$: nondegenerate, primitive,
$\det_H = S_{\mathfrak p}$ (the set $\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},+;n)\cup\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},-;n)$). -/
def admGenRank (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) : Set (LocGenus v n) :=
  {G | G.Nondeg ∧ G.Prim ∧ G.det = AdelicSqCl.comp v S}

theorem admGenRank_eq_union (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    admGenRank n S v = {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) 1} ∪
      {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
  ext G
  simp only [admGenRank, LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_union]
  rcases LocGenus.hasse_pm_rank v G with h | h <;> simp [h]

/-- $A^*_{\mathfrak p;n} = \widetilde M^{*,+}_{\mathfrak p;n} + \widetilde M^{*,-}_{\mathfrak p;n}$ (Definition 4.6) for the true local genera. -/
theorem sum_admGenRank_split (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) (f : LocGenus v n → ℝ)
    (hfin : (admGenRank n S v).Finite) :
    ∑ᶠ G ∈ admGenRank n S v, f G = (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) +
      ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have hD : Disjoint {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) 1}
      {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
    rw [Set.disjoint_left]
    rintro G ⟨-, -, -, h1⟩ ⟨-, -, -, h2⟩
    rw [h1] at h2; exact absurd h2 (by decide)
  rw [admGenRank_eq_union] at hfin ⊢
  exact finsum_mem_union hD (hfin.subset Set.subset_union_left) (hfin.subset Set.subset_union_right)

/-- $B^*_{\mathfrak p;n} = \widetilde M^{*,+}_{\mathfrak p;n} - \widetilde M^{*,-}_{\mathfrak p;n}$ (Definition 4.6) for the true local genera. -/
theorem sum_admGenRank_split_hasse (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) (f : LocGenus v n → ℝ)
    (hfin : (admGenRank n S v).Finite) :
    ∑ᶠ G ∈ admGenRank n S v, ((G.hasse : ℤ) : ℝ) * f G =
      (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) -
        ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have h2fin : {G : LocGenus v n | G.IsGenStar (AdelicSqCl.comp v S) (-1)}.Finite := by
    rw [admGenRank_eq_union] at hfin; exact hfin.subset Set.subset_union_right
  rw [sum_admGenRank_split S v _ hfin, sub_eq_add_neg, ← finsum_mem_neg_distrib _ h2fin]
  congr 1
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp

/-- **Theorem 4.8 for the true local genera of rank $n$ over a number field $F$** (sign-sum form, proof of Thm. 4.8,
eqs. (11)–(12)), with $\varepsilon_\infty = 1$, $\mathbb S = \emptyset$: let $(b_{\mathfrak p})$ be a tuple of local genera that is the only
admissible genus outside a finite set $P$, with $c_{\mathfrak p}(b_{\mathfrak p}) = 1$ there; let $w_{\mathfrak p} \ne 0$ be weights with
$w_{\mathfrak p} = \beta(b_{\mathfrak p})$ for $\mathfrak p \notin P$ and $\prod_{\mathfrak p}w_{\mathfrak p}^{-1} = C$. Then
$$M^*_{1;n}(S) = C\cdot\frac12\Bigl[\prod_{\mathfrak p\in P}\sum_{G}\frac{w_{\mathfrak p}}{\beta(G)} +
\prod_{\mathfrak p\in P}\sum_{G}c_{\mathfrak p}(G)\frac{w_{\mathfrak p}}{\beta(G)}\Bigr],$$
the sums over the admissible genera at $\mathfrak p$. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, and its proof, eqs. (11)-(12), p. 18 (every n, true local genera over F)"]
theorem totalMassM_eq_half_rank (S : AdelicSqCl F) (P : Finset (HeightOneSpectrum (𝓞 F))) (b : LocTuple F n)
    (w : HeightOneSpectrum (𝓞 F) → ℝ) (C : ℝ)
    (hout : ∀ v ∉ P, admGenRank n S v = {b v}) (hb1 : ∀ v ∉ P, (b v).hasse = 1)
    (hw : ∀ v ∉ P, w v = (b v).beta) (hw0 : ∀ v, w v ≠ 0)
    (hfin : ∀ v ∈ P, (admGenRank n S v).Finite) (hprod : HasProd (fun v => (w v)⁻¹) C) :
    totalMassM n S 1 ∅ (fun _ => 1) = C * ((∏ v ∈ P, ∑ᶠ G ∈ admGenRank n S v, w v / G.beta) +
      ∏ v ∈ P, ∑ᶠ G ∈ admGenRank n S v, ((G.hasse : ℤ) : ℝ) * (w v / G.beta)) / 2 := by
  unfold totalMassM
  have hgen : (GenStarF S 1 ∅ (fun _ => 1) : Set (LocTuple F n)) =
      {t | (∀ v, t v ∈ admGenRank n S v) ∧ (Function.mulSupport fun v => (t v).hasse).Finite ∧
        ∏ᶠ v, (t v).hasse = 1} := by
    ext t; simp [GenStarF, admGenRank]
  rw [hgen]
  have hT : ∀ t ∈ {t : LocTuple F n | (∀ v, t v ∈ admGenRank n S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1},
      invDensityTuple t = C * ∏ v ∈ P, w v / (t v).beta := by
    rintro t ⟨hA, -⟩
    have hout' : ∀ v ∉ P, (t v).beta = w v := fun v hv => by
      have h := hA v
      rw [hout v hv] at h
      rw [Set.mem_singleton_iff.mp h, hw v hv]
    obtain ⟨hm, he⟩ := invDensity_factor P w (fun v => (t v).beta) hout' hw0
      (fun v => (LocGenus.beta_pos_rank v _ (hA v).1).ne') hprod.multipliable
    unfold invDensityTuple
    rw [if_pos hm, he, hprod.tprod_eq]
  rw [finsum_mem_congr rfl hT, ← mul_finsum_mem,
    finsum_tuple_sign P b (admGenRank n S) (fun v G => G.hasse) (fun v G => w v / G.beta) hout hb1 hfin
      (fun v G => LocGenus.hasse_pm_rank v G)]
  ring

end

end QuadFormsKB.Hanke2011Structure
