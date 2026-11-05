/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.BinaryMassLocal
import QuadFormsKB.Literature.Hanke2011Structure.TernaryTupleSum

/-!
# Hanke 2011, Lemma 7.8 for $n = 2$ (totally real $F$, totally positive definite signature)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §7, Lemma 7.8, p. 32 (with Definitions 4.5, 4.6 and Theorem 4.8).

**Setting.** $F$ totally real of degree $d = [F:\mathbb Q]$, $S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$,
$\vec\sigma_\infty = ((2,0))_v$ the totally positive definite signature vector of rank $2$ (`totPosSig F 2`), and
$\mathrm{Cls}^*(S,\vec\sigma_\infty;2)$ the classes of primitive $\mathcal O_F$-valued binary lattices of Hessian determinant
squareclass $S$ and signature $\vec\sigma_\infty$, grouped into genera by their tuples of local genera
($\mathrm{Gen}^*(S,\vec\sigma_\infty,\emptyset;2)$, `GenStar`; the mass of a genus is `massOfTuple`).

**Definitions.**
* `admGenTwo S v`: the nondegenerate primitive binary local genera $G$ at $\mathfrak p$ with $\det_H(G) = S_{\mathfrak p}$
  ($\mathrm{Gen}^{*,+}_{\mathfrak p}(S_{\mathfrak p};2)\cup\mathrm{Gen}^{*,-}_{\mathfrak p}(S_{\mathfrak p};2)$).
* `IsGenericFamily S βgen χ`: $\beta_{\mathrm{gen}}(\mathfrak p) \ne 0$ is a choice of generic local densities
  (Definition 4.5) which is correct at almost every prime (there every genus of `admGenTwo S v` has density
  $\beta_{\mathrm{gen}}(\mathfrak p)$), and $\chi$ is a character with $|\chi| \le 1$ and
  $\beta_{\mathrm{gen}}(\mathfrak p) = 1 - \chi(\mathfrak p)/N\mathfrak p$ at almost every prime. (Definition 4.5 fixes
  $\beta_{\mathrm{gen}}$ at the remaining finitely many primes, with Definition 7.5's convention where no normalized genus
  exists; Lemma 7.8 holds for every such choice, since only $\beta_{\mathrm{gen}}(\mathfrak p)^{-1}A^*_{\mathfrak p}$ and
  $\beta_{\mathrm{gen}}(\mathfrak p)^{-1}B^*_{\mathfrak p}$ enter.)
* `astarLoc`, `bstarLoc` (Definition 4.6): $A^*_{\mathfrak p;2}(S_{\mathfrak p}) = \sum_G\beta_{\mathrm{gen}}(\mathfrak p)/\beta(G)$,
  $B^*_{\mathfrak p;2}(S_{\mathfrak p}) = \sum_Gc_{\mathfrak p}(G)\,\beta_{\mathrm{gen}}(\mathfrak p)/\beta(G)$ over $G \in$ `admGenTwo S v`;
  `astarTwo`, `bstarTwo`: the products over all primes (finite products, `astarLoc = bstarLoc = 1` at almost every prime).
* `betaInvReg χ βgen` $= \beta^{-1}_{2,f}(\widetilde S)$, see the clarification below.

**Clarification (the generic density product for $n = 2$).** The paper writes $\beta^{-1}_{n=2,f}(\widetilde S) =
\prod_{\mathfrak p}\beta_{2,\mathfrak p}(\widetilde S_{\mathfrak p})^{-1}$. For $n = 2$ the factors are $(1 - \chi(\mathfrak p)/N\mathfrak p)^{-1}$ at
almost every prime, $\chi$ the quadratic character of $F(\sqrt{-S})/F$, so the product converges only conditionally (the
paper's proof of Lemma 3.6: it is $L^T_F(1,\chi)$ up to finitely many factors). Here it is the regularized product
$$\beta^{-1}_{2,f}(\widetilde S) := \mathrm{regProd}(\chi, 1, \beta_{\mathrm{gen}}^{-1}) = L_F(1,\chi)\cdot
  \prod_{\mathfrak p}\beta_{\mathrm{gen}}(\mathfrak p)^{-1}\bigl(1 - \chi(\mathfrak p)/N\mathfrak p\bigr)$$
(the second product has finite support), with $L_F(1,\chi) = \lim_{s\to1^+}L_F(s,\chi)$. It is the limit of the partial
products over $N\mathfrak p \le X$ given the prime ideal theorem for $\chi$ (`RegProd.NaturalOrderEulerOne`,
`RegProd.hasProd_normOrder_regProd`), and it does not depend on the choice of $\chi$ (`Tamagawa.regProd_congr_finite`).

**Headline.**
* **`lemma_7_8_two`** (Lemma 7.8, $n = 2$, $\vec\sigma_\infty$ totally positive definite, so $\varepsilon_\infty = 1$):
  if $\mathrm{Cls}^*(S,\vec\sigma_\infty;2) \ne \emptyset$, then
  $$\sum_{L\in\mathrm{Cls}^*(S,\vec\sigma_\infty;2)}\frac1{|\mathrm{Aut}(L)|} =
    \frac{\beta^{-1}_{2,f}(\widetilde S)\,|\Delta_F|^{1/2}\,N_{F/\mathbb Q}(I(S))^{3/2}\,[A^*_2(S) + \varepsilon_\infty B^*_2(S)]}
    {2\,(4\pi)^{[F:\mathbb Q]}}.$$
  *Conditional on* the named input `BinaryLocalGeneraFinite F` (finiteness of the binary local genera of given
  $\det_H$ at a prime, used to make $A^*_{\mathfrak p}$, $B^*_{\mathfrak p}$ finite sums at the finitely many bad primes).
* `exists_isGenericFamily`: generic families exist (so the statement is not vacuous).

*Scope:* the paper allows every totally definite signature vector ($\varepsilon_\infty = (-1)^\alpha$); this statement is for
the totally positive definite one, as the repository's `cor_6_3_summed` (the repository's mass formula is for totally
positive definite forms).
-/

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real
open QuadFormsKB.NFEuler QuadFormsKB.RegProd

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### Local genera of rank 2 -/

/-- **The admissible binary local genera at $\mathfrak p$** for $S$: nondegenerate primitive local genera $G$ of
$\mathcal O_{\mathfrak p}$-valued binary forms with $\det_H(G) = S_{\mathfrak p}$ (both Hasse invariants). -/
def admGenTwo (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) : Set (LocGenus v 2) :=
  {G | G.Nondeg ∧ G.Prim ∧ G.det = AdelicSqCl.comp v S}

/-- **Finiteness of the binary local genera of given Hessian determinant** (named input): at every prime $\mathfrak p$ of
$F$ and for every $s \in \mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times)$ there are only finitely many
nondegenerate primitive local genera of $\mathcal O_{\mathfrak p}$-valued binary quadratic forms with $\det_H = s$.

Field:
- `finite`: for every prime `v` and every local squareclass `s`, the set
  $\{G : G\ \text{nondegenerate, primitive},\ \det_H(G) = s\}$ is finite.

A classical fact (Jordan decompositions over $\mathcal O_{\mathfrak p}$: the scales and dimensions of the Jordan components are
bounded by $\operatorname{ord}_{\mathfrak p}(s)$ and each component has finitely many classes; O'Meara 1963, §91–§93; Cassels
1978, Ch. 8, Lemma 3.? [unverified]). It is not proved in the repository for general number fields. Used only to make the
local sums $A^*_{\mathfrak p}$, $B^*_{\mathfrak p}$ finite sums; it is not equivalent to any mass formula. -/
@[kb "omeara1963" "§92-§93 (finitely many local integral classes of given discriminant) [unverified]"]
structure BinaryLocalGeneraFinite (F : Type) [Field F] [NumberField F] : Prop where
  finite : ∀ (v : HeightOneSpectrum (𝓞 F)) (s : LocalSqCl v),
    {G : LocGenus v 2 | G.Nondeg ∧ G.Prim ∧ G.det = s}.Finite

/-- The local density of a nondegenerate local genus (any rank) is positive. -/
theorem LocGenus.beta_pos_rank {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) (hG : G.Nondeg) :
    0 < G.beta := by
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

/-- The Hasse invariant of a local genus (any rank) is $\pm1$. -/
theorem LocGenus.hasse_pm_rank {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) :
    G.hasse = 1 ∨ G.hasse = -1 := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  rw [LocGenus.hasse_mk]
  exact Composition.hasseC_pm _

/-- **Uniqueness at the good primes** (Theorem 2.6, $\mathfrak p \nmid 2$): if $\mathfrak p \nmid 2$ and $S_{\mathfrak p}$ is a unit
class, there is at most one admissible binary local genus. -/
theorem admGenTwo_subsingleton (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (h0 : adelicOrd v S = 0) {G G' : LocGenus v 2} (hG : G ∈ admGenTwo S v) (hG' : G' ∈ admGenTwo S v) :
    G = G' := by
  have hSv : AdelicSqCl.comp v S ∈ localUnitSqCl F v := mem_localUnitSqCl_of_ordZ v h0
  have key : ∀ {T : QuadForm (v.adicCompletionIntegers F) 2}, LocGenus.mk T ∈ admGenTwo S v →
      IsPrimitiveForm T ∧ ∃ hTne : algebraMap _ (v.adicCompletion F) T.hessian.det ≠ 0,
        IsUnit T.hessian.det ∧ SqCl.mk (Units.mk0 _ hTne) = AdelicSqCl.comp v S := by
    intro T hT
    obtain ⟨hnd, hpr, hdet⟩ := hT
    rw [LocGenus.nondeg_mk] at hnd
    rw [LocGenus.prim_mk] at hpr
    rw [LocGenus.det_mk] at hdet
    have hTne : algebraMap _ (v.adicCompletion F) T.hessian.det ≠ 0 := (algebraMap_ne_zero_iff (v := v)).mpr hnd
    rw [detSqForm_of_ne hTne] at hdet
    have hTunitF : Units.mk0 _ hTne ∈ localUnits v := mem_localUnits_of_mk_mem v (hdet ▸ hSv)
    refine ⟨hpr, hTne, ?_, hdet⟩
    refine HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ?_
    have h := (mem_localUnits_iff v).mp hTunitF
    rwa [Units.val_mk0] at h
  obtain ⟨T, hT⟩ := Quotient.exists_rep G
  obtain ⟨T', hT'⟩ := Quotient.exists_rep G'
  have e : G = LocGenus.mk T := hT.symm
  have e' : G' = LocGenus.mk T' := hT'.symm
  subst e e'
  obtain ⟨hpr, hne, hu, hd⟩ := key hG
  obtain ⟨hpr', hne', hu', hd'⟩ := key hG'
  obtain ⟨w, ⟨u0, hu0⟩, hwe⟩ := SqCl.exists_eq_mul_sq (hd.trans hd'.symm)
  have hdetT : T'.hessian.det = (u0 : v.adicCompletionIntegers F) ^ 2 * T.hessian.det := by
    apply IsFractionRing.injective (v.adicCompletionIntegers F) (v.adicCompletion F)
    have := congrArg Units.val hwe
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← hu0] at this
    change algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) T'.hessian.det =
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) T.hessian.det *
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (u0 : v.adicCompletionIntegers F)) ^ 2 at this
    rw [map_mul, map_pow, this, mul_comm]
  have hiso := (uniqueNormalizedLocalGenus_completion v h2 2).unique T T' hpr hpr'
    (by
      unfold IsNormalizedHessian
      rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, if_pos even_two])
    u0 u0.isUnit hdetT
  exact LocGenus.mk_eq_mk.mpr hiso

/-- The dyadic primes form a finite set. -/
theorem finite_dyadic_two : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)).subset fun _ hv =>
    Ideal.dvd_span_singleton.mpr hv

/-! ### Generic densities and the normalized local mass sums -/

/-- **An admissible family of generic local densities with its character** (Definition 4.5, $n = 2$): `βgen` is nonzero
everywhere and is the density of the admissible genera at almost every prime, and `χ` is a character with $|\chi| \le 1$
and $\beta_{\mathrm{gen}}(\mathfrak p) = 1 - \chi(\mathfrak p)/N\mathfrak p$ at almost every prime.

Fields (of the conjunction):
- `ne_zero`: $\beta_{\mathrm{gen}}(\mathfrak p) \ne 0$ for every $\mathfrak p$;
- `abs_le`: $|\chi(\mathfrak p)| \le 1$ for every $\mathfrak p$;
- `generic`: for all but finitely many $\mathfrak p$, every $G \in$ `admGenTwo S v` has $\beta(G) = \beta_{\mathrm{gen}}(\mathfrak p)$;
- `euler`: for all but finitely many $\mathfrak p$, $\beta_{\mathrm{gen}}(\mathfrak p) = 1 - \chi(\mathfrak p)/N\mathfrak p$.

A *condition* (a choice of conventions at finitely many primes); such families exist when
$\mathrm{Gen}^*(S,\vec\sigma_\infty,\emptyset;2) \ne \emptyset$ (`exists_isGenericFamily`). -/
def IsGenericFamily (S : AdelicSqCl F) (βgen χ : HeightOneSpectrum (𝓞 F) → ℝ) : Prop :=
  (∀ v, βgen v ≠ 0) ∧ (∀ v, |χ v| ≤ 1) ∧ {v | ¬ ∀ G ∈ admGenTwo S v, G.beta = βgen v}.Finite ∧
    {v | βgen v ≠ 1 - χ v / (normP v : ℝ)}.Finite

/-- **The generic density product** $\beta^{-1}_{2,f}(\widetilde S)$ for $n = 2$ (Definition 4.5, Lemma 7.8), read as the
regularized product $L_F(1,\chi)\prod_{\mathfrak p}\beta_{\mathrm{gen}}(\mathfrak p)^{-1}(1-\chi(\mathfrak p)/N\mathfrak p)$.
*Clarification:* the printed infinite product converges only conditionally for $n = 2$; see the module docstring. -/
@[kb "hanke2011structure" "Def. 4.5, p. 16 (n = 2, regularized generic density product)"]
def betaInvReg (χ βgen : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ := regProd χ 1 fun v => (βgen v)⁻¹

/-- **$A^*_{\mathfrak p;2}(S_{\mathfrak p})$** (Definition 4.6): $\sum_{G}\beta_{\mathrm{gen}}(\mathfrak p)/\beta(G)$ over
$G \in$ `admGenTwo S v`. -/
@[kb "hanke2011structure" "Def. 4.6, p. 16 (A*_p, n = 2)"]
def astarLoc (S : AdelicSqCl F) (βgen : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ∑ᶠ G ∈ admGenTwo S v, βgen v / G.beta

/-- **$B^*_{\mathfrak p;2}(S_{\mathfrak p})$** (Definition 4.6): $\sum_{G}c_{\mathfrak p}(G)\,\beta_{\mathrm{gen}}(\mathfrak p)/\beta(G)$. -/
@[kb "hanke2011structure" "Def. 4.6, p. 16 (B*_p, n = 2)"]
def bstarLoc (S : AdelicSqCl F) (βgen : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ∑ᶠ G ∈ admGenTwo S v, ((G.hasse : ℤ) : ℝ) * (βgen v / G.beta)

/-- **$A^*_2(S) = \prod_{\mathfrak p}A^*_{\mathfrak p;2}(S_{\mathfrak p})$** (a finite product for admissible data). -/
@[kb "hanke2011structure" "Def. 4.6 and Thm. 4.8, pp. 16-17 (A*(S), n = 2)"]
def astarTwo (S : AdelicSqCl F) (βgen : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ := ∏ᶠ v, astarLoc S βgen v

/-- **$B^*_2(S) = \prod_{\mathfrak p}B^*_{\mathfrak p;2}(S_{\mathfrak p})$** (a finite product for admissible data). -/
@[kb "hanke2011structure" "Def. 4.6 and Thm. 4.8, pp. 16-17 (B*(S), n = 2)"]
def bstarTwo (S : AdelicSqCl F) (βgen : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ := ∏ᶠ v, bstarLoc S βgen v

/-! ### The constant and the sign -/

/-- **The constant of Lemma 7.8:** $C(S) = |\Delta_F|^{1/2}N_{F/\mathbb Q}(I(S))^{3/2}/(4\pi)^{[F:\mathbb Q]}$ for $n = 2$
($V(2) = \pi/2$, `lemma_7_8_constant`). -/
theorem massConst_two (S : AdelicSqCl F) :
    massConst F 2 S = |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((3 : ℝ) / 2) /
      (4 * π) ^ Module.finrank ℚ F := by
  have hc := lemma_7_8_constant (Module.finrank ℚ F)
  have hV : 0 < volV 2 := by rw [volV_two]; positivity
  unfold massConst
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (2 - 1) / 4 = 1 / 2 by norm_num, show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) * (2 + 1) / 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← hc]
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ Module.finrank ℚ F) ^ 3 := by positivity
  field_simp

theorem epsInf_totPosSig_two : epsInf (totPosSig F 2) = 1 := by
  simp [epsInf, totPosSig, hasseReal]

/-! ### The mass of a tuple of local genera -/

section Mass

variable [IsTotallyReal F]

/-- **The mass of a binary tuple of local genera** $t \in \mathrm{Gen}^*$ (totally positive signature), for a regularizing
character $\chi$: `massOfTuple t` $= C(S)\cdot\mathrm{regProd}(\chi, 1, \beta(t_\cdot)^{-1})$. -/
theorem massOfTuple_eq_two (S : AdelicSqCl F) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) {t : LocTuple F 2} (ht : t ∈ GenStar S (totPosSig F 2) 𝕊 c)
    {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : IsRegChar t χ) :
    massOfTuple S (totPosSig F 2) 𝕊 c t = massConst F 2 S * invDensityReg χ t := by
  have h := (mem_genStar_iff S (totPosSig F 2) 𝕊 c t).mp ht
  unfold massOfTuple
  rw [dif_pos h]
  obtain ⟨hQ, hL, hσ, hS, -, -, ht'⟩ := h.choose_spec
  have hχ' := cast (congrArg (fun s => IsRegChar s χ) ht').symm hχ
  have e := congrArg (invDensityReg χ) ht'.symm
  rw [e, mass_of_rep_two hQ _ hL hσ hχ', hS]

/-- A positive real embedding gives a square in the completion at a real place. -/
theorem isSquare_completion_of_pos (w : {w : InfinitePlace F // w.IsReal}) (y : F)
    (hy : 0 < realEmb F w.1 y) : IsSquare (algebraMap F w.1.Completion y) := by
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal w.2
  have h := algebraMap_completion_real' w.2 y
  refine ⟨ψ.symm (Real.sqrt (realEmb F w.1 y)), ?_⟩
  apply ψ.injective
  rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hy.le, h]
  rfl

/-- **The global class of $S$ from one lattice** (the hypotheses of Lemma 3.7): if
$\mathrm{Gen}^*(S,\vec\sigma_\infty,\mathbb S;2) \ne \emptyset$ for the totally positive signature, there is $\alpha \in F^\times$
(the Hessian determinant of a realization) with $\rho_{\mathfrak p}(S_{\mathfrak p}) = [\alpha]$ at every prime and $\alpha$
totally positive. -/
theorem exists_alpha_of_mem_genStar (S : AdelicSqCl F) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) {t : LocTuple F 2} (ht : t ∈ GenStar S (totPosSig F 2) 𝕊 c) :
    ∃ α : Fˣ, (∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α)) ∧
      ∀ w : {w : InfinitePlace F // w.IsReal},
        IsSquare (algebraMap F w.1.Completion ((-1) ^ ((totPosSig F 2) w).1.2 * (α : F))) := by
  obtain ⟨Q, hQ, L, hL, hσ, hS, -, -, -⟩ := ht
  obtain ⟨g, Q₀, hQ₀⟩ := exists_integral_model Q
  have hQ' := hessian_det_compMat_ne Q g hQ
  have hS' : detH (Q.compMat g.val) hQ' (Lat.image g⁻¹ L) = S := (detH_transport Q g hQ L).trans hS
  have hpd : IsTotallyPosDef (formF Q₀) := by
    rw [hQ₀]; exact isTotallyPosDef_of_hasSignature (hasSignature_compMat Q g hσ)
  refine ⟨Units.mk0 _ hQ', fun v => ?_, fun w => ?_⟩
  · rw [← hS', detH_comp _ hQ' _ v (locBasis_spec v _), rhoLocal_mk]
    have he : localHessDet (Q.compMat g.val) hQ' v (locBasis v (Lat.image g⁻¹ L)) =
        unitsToLocal v (Units.mk0 _ hQ') * (Units.map detMonoidHom (locBasis v (Lat.image g⁻¹ L))) ^ 2 := by
      apply Units.ext
      simp [localHessDet, unitsToLocal]
    rw [he, map_mul, SqCl.mk_sq_of_mem (Subgroup.mem_top _), mul_one]
  · have h0 : ((totPosSig F 2) w).1.2 = 0 := rfl
    rw [h0, pow_zero, one_mul, Units.val_mk0]
    apply isSquare_completion_of_pos
    have hpos := Tamagawa.realEmb_det_hessian_pos hpd w.1
    have hd : (Q.compMat g.val).hessian.det = algebraMap (𝓞 F) F Q₀.hessian.det := by
      rw [← hQ₀, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [hd]; exact hpos

end Mass

/-! ### Lemma 7.8 -/

section Main

variable [IsTotallyReal F]

/-- **Generic families exist**: if $\mathrm{Gen}^*(S,\vec\sigma_\infty,\emptyset;2) \ne \emptyset$, the densities of the local genera
of one lattice and the character of an $\mathcal O_F$-model form an admissible family (`IsGenericFamily`). -/
theorem exists_isGenericFamily (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty) :
    ∃ βgen χ : HeightOneSpectrum (𝓞 F) → ℝ, IsGenericFamily S βgen χ := by
  obtain ⟨t₀, ht₀⟩ := hne
  have hF := genStar_subset_genStarF S (totPosSig F 2) ∅ (fun _ => 1) ht₀
  obtain ⟨Q, hQ, L, hL, hσ, hS, -, -, ht⟩ := ht₀
  obtain ⟨χ, hχ⟩ := exists_isRegChar_of_rep L hL hσ
  rw [ht] at hχ
  refine ⟨fun v => (t₀ v).beta, χ, fun v => (LocGenus.beta_pos_rank v _ (hF.1 v).1).ne', hχ.1, ?_, hχ.2⟩
  refine (finite_dyadic_two.union (supp_finite S)).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, supp, not_or, not_not] at h
  simp only [Set.mem_setOf_eq] at hv
  apply hv
  intro G hG
  rw [admGenTwo_subsingleton S v h.1 h.2 hG ⟨(hF.1 v).1, (hF.1 v).2.1, (hF.1 v).2.2⟩]

/-- **Lemma 7.8 for $n = 2$** (Hanke 2011, p. 32), totally real $F$, the totally positive definite signature
$\vec\sigma_\infty = ((2,0))_v$ (so $\varepsilon_\infty = 1$): for every $S$ with $\mathrm{Cls}^*(S,\vec\sigma_\infty;2) \ne \emptyset$ and every
admissible family of generic densities $\beta_{\mathrm{gen}}$ with character $\chi$ (`IsGenericFamily`),
$$\sum_{L\in\mathrm{Cls}^*(S,\vec\sigma_\infty;2)}\frac1{|\mathrm{Aut}(L)|} =
  \frac{\beta^{-1}_{2,f}(\widetilde S)\,|\Delta_F|^{1/2}\,N_{F/\mathbb Q}(I(S))^{3/2}\,[A^*_2(S) + \varepsilon_\infty B^*_2(S)]}
  {2\,(4\pi)^{[F:\mathbb Q]}},$$
the left side as the sum over the genera of their masses (`massOfTuple`, `Lattices.mass` $= \sum1/|O(M)|$),
$\beta^{-1}_{2,f}(\widetilde S)$ = `betaInvReg χ βgen` (*Clarification:* the regularized product
$L_F(1,\chi)\prod_{\mathfrak p}\beta_{\mathrm{gen}}(\mathfrak p)^{-1}(1-\chi(\mathfrak p)/N\mathfrak p)$, since the printed product converges
only conditionally for $n = 2$), $A^*_2$, $B^*_2$ = `astarTwo`, `bstarTwo`.

*Proof:* Corollary 6.3 for $n = 2$ with the regularized product (`mass_of_rep_two`, from $\tau^{\mathrm{reg}}(SO_2) = 2$, not
Hanke 2005's Theorem 2.1, which needs $n \ge 3$), Lemma 3.7 (`lemma_3_7`, its sign hypothesis from the given lattice),
Theorem 2.6 at $\mathfrak p \nmid 2$ and the sign-constrained tuple sum of Theorem 4.8 (`finsum_tuple_sign`).
*Conditional on* `BinaryLocalGeneraFinite F`. -/
@[kb "hanke2011structure" "Lemma 7.8, p. 32 (n = 2)"]
theorem lemma_7_8_two (H : BinaryLocalGeneraFinite F) (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {βgen χ : HeightOneSpectrum (𝓞 F) → ℝ} (hg : IsGenericFamily S βgen χ) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      betaInvReg χ βgen * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((3 : ℝ) / 2) *
        (astarTwo S βgen + (epsInf (totPosSig F 2) : ℝ) * bstarTwo S βgen) /
          (2 * (4 * π) ^ Module.finrank ℚ F) := by
  classical
  obtain ⟨hβ0, hχ1, hgen, heul⟩ := hg
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨α, hα, hsign⟩ := exists_alpha_of_mem_genStar S ∅ (fun _ => 1) ht₀
  have h37 := lemma_3_7 (n := 2) (by norm_num) S (totPosSig F 2) ∅ (fun _ => 1) α hα hsign
  rw [epsInf_totPosSig_two] at h37
  have hset : GenStar S (totPosSig F 2) ∅ (fun _ => (1 : ℤ)) = {t : LocTuple F 2 | (∀ v, t v ∈ admGenTwo S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1} := by
    rw [h37.1]; ext t; simp [GenStarF, admGenTwo]
  have ht₀' : t₀ ∈ {t : LocTuple F 2 | (∀ v, t v ∈ admGenTwo S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1} := hset ▸ ht₀
  -- the finite set of bad primes
  set P : Finset (HeightOneSpectrum (𝓞 F)) :=
    (finite_dyadic_two.union ((supp_finite S).union (ht₀'.2.1.union hgen))).toFinset with hPdef
  have hPout : ∀ v ∉ P, (2 : 𝓞 F) ∉ v.asIdeal ∧ adelicOrd v S = 0 ∧ (t₀ v).hasse = 1 ∧
      ∀ G ∈ admGenTwo S v, G.beta = βgen v := by
    intro v hv
    simp only [hPdef, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, supp,
      not_or, not_not] at hv
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  have hout : ∀ v ∉ P, admGenTwo S v = {t₀ v} := fun v hv => by
    obtain ⟨h2, h0, -, -⟩ := hPout v hv
    ext G
    constructor
    · intro hG; exact Set.mem_singleton_iff.mpr (admGenTwo_subsingleton S v h2 h0 hG (ht₀'.1 v))
    · intro hG; rw [Set.mem_singleton_iff.mp hG]; exact ht₀'.1 v
  have hfin : ∀ v ∈ P, (admGenTwo S v).Finite := fun v _ => H.finite v _
  -- the corrected generic product has finite support
  have hgfin : Function.HasFiniteMulSupport fun v => (βgen v)⁻¹ * (1 - χ v / (normP v : ℝ)) ^ (1 : ℤ) := by
    refine heul.subset fun v hv => ?_
    by_contra h
    apply hv
    simp only [Set.mem_setOf_eq, not_not] at h
    show (βgen v)⁻¹ * (1 - χ v / (normP v : ℝ)) ^ (1 : ℤ) = 1
    rw [zpow_one, ← h, inv_mul_cancel₀ (hβ0 v)]
  -- the mass of each genus
  have hterm : ∀ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => (1 : ℤ)),
      massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
        massConst F 2 S * betaInvReg χ βgen * ∏ v ∈ P, βgen v / (t v).beta := by
    intro t ht
    have htA : ∀ v, t v ∈ admGenTwo S v := by
      have h2 := ht
      rw [hset] at h2
      exact h2.1
    have hβt : ∀ v ∉ P, (t v).beta = βgen v := fun v hv => (hPout v hv).2.2.2 _ (htA v)
    have hreg : IsRegChar t χ := by
      refine ⟨hχ1, (heul.union P.finite_toSet).subset fun v hv => ?_⟩
      by_contra h
      rw [Set.mem_union, not_or] at h
      simp only [Set.mem_setOf_eq, not_not, Finset.mem_coe] at h hv
      exact hv (by rw [hβt v h.2]; exact h.1)
    rw [massOfTuple_eq_two S ∅ _ ht hreg, mul_assoc]
    congr 1
    unfold invDensityReg betaInvReg regProd
    have hβtpos : ∀ v, (t v).beta ≠ 0 := fun v => (LocGenus.beta_pos_rank v _ (htA v).1).ne'
    have hsupp : Function.mulSupport (fun v => βgen v / (t v).beta) ⊆ P := by
      intro v hv
      by_contra h
      exact hv (by simp only; rw [hβt v h, div_self (hβ0 v)])
    have hr : Multipliable fun v => βgen v / (t v).beta :=
      multipliable_of_hasFiniteMulSupport (P.finite_toSet.subset hsupp)
    have e : (fun v => ((t v).beta)⁻¹ * (1 - χ v / (normP v : ℝ)) ^ (1 : ℤ)) =
        fun v => ((βgen v)⁻¹ * (1 - χ v / (normP v : ℝ)) ^ (1 : ℤ)) * (βgen v / (t v).beta) := by
      funext v
      field_simp [hβ0 v, hβtpos v]
    rw [e, (multipliable_of_hasFiniteMulSupport hgfin).tprod_mul hr, tprod_eq_prod' hsupp]
    ring
  rw [finsum_mem_congr rfl hterm, ← mul_finsum_mem, hset,
    finsum_tuple_sign P t₀ (admGenTwo S) (fun v G => G.hasse) (fun v G => βgen v / G.beta) hout
      (fun v hv => (hPout v hv).2.2.1) hfin (fun v G => LocGenus.hasse_pm_rank v G)]
  have hA : astarTwo S βgen = ∏ v ∈ P, ∑ᶠ G ∈ admGenTwo S v, βgen v / G.beta := by
    unfold astarTwo astarLoc
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    apply hv
    simp only
    rw [hout v h, finsum_mem_singleton, (hPout v h).2.2.2 _ (ht₀'.1 v), div_self (hβ0 v)]
  have hB : bstarTwo S βgen = ∏ v ∈ P, ∑ᶠ G ∈ admGenTwo S v, ((G.hasse : ℤ) : ℝ) * (βgen v / G.beta) := by
    unfold bstarTwo bstarLoc
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    apply hv
    simp only
    rw [hout v h, finsum_mem_singleton, (hPout v h).2.2.1, (hPout v h).2.2.2 _ (ht₀'.1 v), div_self (hβ0 v)]
    norm_num
  rw [hA, hB, massConst_two, epsInf_totPosSig_two]
  have hπ : (4 * π) ^ Module.finrank ℚ F ≠ 0 := by positivity
  push_cast
  field_simp

end Main

end

end QuadFormsKB.Hanke2011Structure
