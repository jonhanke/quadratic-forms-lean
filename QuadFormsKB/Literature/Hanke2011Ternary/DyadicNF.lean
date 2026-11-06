/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryNFRat
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoNFSeries
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicFamilyGlobal

/-!
# Paper 7, Table 5.3 at the dyadic primes of a number field in which $2$ splits completely

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), §5, Table 5.3, pp. 20–21, and the standing hypothesis (abstract, Theorems 7.1
and 8.1) that $2$ splits completely in $F$.

Let $F$ be a number field in which $2$ splits completely and $\mathfrak p \mid 2$ a prime of $F$.  Then
$e_{\mathfrak p} = f_{\mathfrak p} = 1$ (`TwoSplitsCompletely.ramificationIdx_eq_one`, `TwoSplitsCompletely.qv_eq_two`),
so $2 \notin \mathfrak p^2$ and $N\mathfrak p = 2$ (`TwoSplitsCompletely.isQ2Prime`), and there is a ring isomorphism
$\sigma : \mathcal O_{\mathfrak p} \cong \mathbb Z_2$ (`RatTwoNF.IsQ2Prime.equiv`).  Transporting along $\sigma$ (the local genera,
their Hessian determinant squareclasses, Hasse invariants and densities $\beta$ are carried to those over $\mathbb Q_2$:
`RatTwoNF.isGenStar_locMap`, `RatTwoNF.invBetaSum_transport`) the proved $\mathbb Q_2$ tables
(`ternaryLocalTablesNF_rat`, from `Dyadic7.dyadicTernaryLocalMassTable_holds`) gives the dyadic fields of the
named input `TernaryLocalTablesNF F`:

* `dyNF_finite`: $\mathrm{Gen}^*_{\mathfrak p}(S,\varepsilon;3)$ is finite;
* `dyNF_zero`: it is empty when $\operatorname{ord}_{\mathfrak p}S = 0$;
* `dyNF_A`, `dyNF_B`: for $\nu = \operatorname{ord}_{\mathfrak p}S \ge 1$,
  $\sum_{G\in\mathrm{Gen}^{*,+}}\frac{3/16}{\beta(G)} \pm \sum_{G\in\mathrm{Gen}^{*,-}}\frac{3/16}{\beta(G)}$ are the entries
  `dyadicA ν` and `dyadicB ε ν` of Table 5.3, $\varepsilon = (-1, x)_{\mathfrak p}$ for $x$ in the rational squareclass of $S$.

The valuation is preserved: $\operatorname{ord}_2\hat\sigma(S) = \operatorname{ord}_{\mathfrak p}S$ (`ordS_sqMap`), since $2$ is a
uniformizer on both sides; and $(-1, \hat\sigma x)_{\mathbb Q_2} = (-1, x)_{\mathfrak p}$ since the Hilbert symbol is defined
algebraically (`RatTwoNF.hilbertSymbol_equiv`).  All unconditional.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF RatTwoNF

noncomputable section

local notation "ordS" v => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-! ### Two splits completely: $e = f = 1$ above $2$ -/

section Split

variable {F : Type} [Field F] [NumberField F]

/-- **Fundamental identity for $2$, ramification part:** if $2$ splits completely in $F$, every prime
$\mathfrak p \mid 2$ has ramification index $e_{\mathfrak p} = 1$. -/
theorem _root_.QuadFormsKB.Hanke2011Ternary.NF.TwoSplitsCompletely.ramificationIdx_eq_one (h : TwoSplitsCompletely F) (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) : v.asIdeal.ramificationIdx ℤ = 1 := by
  set p : Ideal ℤ := Ideal.span {(2 : ℤ)} with hpdef
  have hp : p.IsPrime := (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  let e := dyadicEquivPrimesOver F
  have hfin : Finite {v : HeightOneSpectrum (𝓞 F) // (2 : 𝓞 F) ∈ v.asIdeal} :=
    (finite_dyadic (F := F)).to_subtype
  have : Finite (p.primesOver (𝓞 F)) := Finite.of_equiv _ e
  let _ : Fintype (p.primesOver (𝓞 F)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : numDyadic F = Nat.card {v : HeightOneSpectrum (𝓞 F) // (2 : 𝓞 F) ∈ v.asIdeal} := by
    rw [numDyadic, ← Set.ncard_eq_toFinset_card _ finite_dyadic, ← Nat.card_coe_set_eq]
    rfl
  have hcard : Fintype.card (p.primesOver (𝓞 F)) = Module.finrank ℚ F := by
    rw [← h, h1, Nat.card_congr e, Nat.card_eq_fintype_card]
  have hge : ∀ q : p.primesOver (𝓞 F), 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := fun q => by
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver p := q.2.2
    exact Nat.mul_pos (q.1.ramificationIdx_pos ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
  have hone : ∀ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq⟩ := hcon
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : p.primesOver (𝓞 F) => 1)
      (g := fun q => q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ)
      (fun i _ => hge i) ⟨q, Finset.mem_univ _, lt_of_le_of_ne (hge q) (Ne.symm hq)⟩
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt
    omega
  exact Nat.eq_one_of_mul_eq_one_right (hone (e ⟨v, hv⟩))

/-- If $2$ splits completely in $F$, then $2 \notin \mathfrak p^2$ for every prime $\mathfrak p \mid 2$. -/
theorem _root_.QuadFormsKB.Hanke2011Ternary.NF.TwoSplitsCompletely.two_not_mem_sq (h : TwoSplitsCompletely F) (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) : (2 : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro h2
  have : v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := (liesOver_two_iff (F := F) v.asIdeal).2 hv
  have he := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(2 : ℤ)}) v.asIdeal (by simp)
  rw [h.ramificationIdx_eq_one v hv] at he
  have hmap : ∀ I : Ideal (𝓞 F), (2 : 𝓞 F) ∈ I →
      Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(2 : ℤ)}) ≤ I := fun I hI => by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_singleton_iff.1 hx]
    simpa using hI
  exact (Ideal.ramificationIdx'_ne_one_iff (hmap _ hv)).2 (hmap _ h2) he

/-- **If $2$ splits completely in $F$, every dyadic completion is $\mathbb Q_2$:** each prime $\mathfrak p \mid 2$ has
$2 \notin \mathfrak p^2$ and $N\mathfrak p = 2$ (`RatTwoNF.IsQ2Prime`). -/
@[kb "hanke2011ternary" "abstract and §7, Thm. 7.1, p. 26 (2 splits completely, so F_p = Q_2 for p | 2)"]
theorem _root_.QuadFormsKB.Hanke2011Ternary.NF.TwoSplitsCompletely.isQ2Prime (h : TwoSplitsCompletely F) (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) : IsQ2Prime v :=
  ⟨hv, h.two_not_mem_sq v hv, h.qv_eq_two v hv⟩

/-- $2$ splits completely in $\mathbb Q$. -/
theorem twoSplitsCompletely_rat : TwoSplitsCompletely ℚ := by
  obtain ⟨w, hw⟩ := exists_dyadic_rat
  unfold TwoSplitsCompletely numDyadic
  rw [Module.finrank_self, Finset.card_eq_one]
  refine ⟨w, ?_⟩
  ext v
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
  constructor
  · intro hv
    have a := (two_mem_iff_pv v).1 hv
    have b := (two_mem_iff_pv w).1 hw
    exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext (a.trans b.symm))
  · rintro rfl
    exact hw

end Split

/-! ### Valuations and squareclasses at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ -/

section Sq

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem two_ne_zero_o : (2 : 𝔬) ≠ 0 := by
  intro h
  have := congrArg (fun z : 𝔬 => (z : Fv)) h
  simp at this

theorem RatTwoNF.IsQ2Prime.ordZ_sqNF_two (h : IsQ2Prime v) : (ordS v) (RatND.sqNF (2 : 𝔬)) = 1 := by
  rw [RatND.sqNF_of_ne two_ne_zero_o, SqCl.ordZ_mk]
  change -WithZero.log (Valued.v (((2 : 𝔬) : Fv))) = 1
  have e : (((2 : 𝔬) : Fv)) = 2 := by norm_cast
  rw [e, h.valued_two, WithZero.log_exp]
  rfl

/-- A squareclass of valuation $\nu \ge 0$ at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ is $[2^\nu w]$, $w$ a unit. -/
theorem RatTwoNF.IsQ2Prime.exists_two_pow_unit (h : IsQ2Prime v) (S : LocalSqCl v) (ν : ℕ) (hS : (ordS v) S = ν) :
    ∃ w : 𝔬, IsUnit w ∧ S = RatND.sqNF ((2 : 𝔬) ^ ν * w) := by
  have ht : (ordS v) (S * (RatND.sqNF (2 : 𝔬)) ^ (-(ν : ℤ))) = 0 := by
    rw [SqCl.ordZ_mul, SqCl.ordZ_zpow, hS, h.ordZ_sqNF_two]
    ring
  obtain ⟨w, hw, hwt⟩ := RatND.exists_unit_of_ordZ_zero ht
  refine ⟨w, hw, ?_⟩
  rw [RatTwoNF.sqNF_mul (pow_ne_zero _ two_ne_zero_o) hw.ne_zero, RatND.sqNF_pow two_ne_zero_o, ← hwt,
    zpow_neg, zpow_natCast, mul_comm S, mul_inv_cancel_left]

/-- **The valuation is preserved by $\hat\sigma$** ($\operatorname{ord}S \ge 0$). -/
theorem ordS_sqMap (h : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal)
    (σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ) (S : LocalSqCl v) (hS : 0 ≤ (ordS v) S) :
    (ordS w₂) (sqMap σ S) = (ordS v) S := by
  obtain ⟨w, hw, hSw⟩ := h.exists_two_pow_unit S ((ordS v) S).toNat (Int.toNat_of_nonneg hS).symm
  obtain ⟨w', hw', hcl⟩ := sqMap_two_pow_mul h w₂ h2 σ hw
  conv_lhs => rw [hSw]
  rw [hcl, Dyadic7.ordZ_zSqCl w₂ h2 _ hw', Int.toNat_of_nonneg hS]

/-- **The rational squareclass is transported:** if $\rho_{\mathfrak p}(S) = [x]$ then $\rho(\hat\sigma S) = [\hat\sigma x]$. -/
theorem rhoLocal_sqMap {F' : Type} [Field F'] [NumberField F'] {v' : HeightOneSpectrum (𝓞 F')}
    (σ : 𝔬 ≃+* v'.adicCompletionIntegers F') (S : LocalSqCl v) (x : Fvˣ) (hx : rhoLocal v S = SqCl.mk x) :
    rhoLocal v' (sqMap σ S) = SqCl.mk (unitsMap σ x) := by
  obtain ⟨y, rfl⟩ := SqCl.mk_surjective S
  rw [sqMap_mk, rhoLocal_mk]
  rw [rhoLocal_mk] at hx
  obtain ⟨t, -, ht⟩ := QuotientGroup.eq.mp hx
  refine QuotientGroup.eq.mpr ⟨unitsMap σ t, Subgroup.mem_top _, ?_⟩
  simp only [powMonoidHom_apply] at ht ⊢
  rw [← map_pow, ht, map_mul, map_inv]

end Sq

/-! ### The dyadic fields of `TernaryLocalTablesNF` -/

section Fields

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝔬" => v.adicCompletionIntegers F

/-- The transport data: a dyadic prime $w_2$ of $\mathbb Q$ and $\sigma : \mathcal O_{\mathfrak p} \cong \mathbb Z_{w_2}$. -/
theorem exists_transport (h : IsQ2Prime v) :
    ∃ w₂ : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ w₂.asIdeal ∧
      Nonempty (𝔬 ≃+* w₂.adicCompletionIntegers ℚ) := by
  obtain ⟨w₂, h2⟩ := exists_dyadic_rat
  exact ⟨w₂, h2, ⟨h.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm⟩⟩

theorem genStar_eq_preimage {w₂ : HeightOneSpectrum (𝓞 ℚ)} (σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ)
    (S : LocalSqCl v) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c} = locMap σ ⁻¹' {G : LocGenus w₂ 3 | G.IsGenStar (sqMap σ S) c} := by
  ext G
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact (isGenStar_locMap σ S c G).symm

theorem finsum_const_div_beta (k : ℝ) (v₀ : HeightOneSpectrum (𝓞 F)) (S : LocalSqCl v₀) (c : ℤ) :
    ∑ᶠ G ∈ {G : LocGenus v₀ 3 | G.IsGenStar S c}, k / G.beta = k * invBetaSum v₀ 3 S c := by
  unfold invBetaSum
  simp only [div_eq_mul_inv]
  rw [mul_finsum_mem]

/-- **Finiteness of $\mathrm{Gen}^*_{\mathfrak p}(S,\varepsilon;3)$ at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$.** -/
@[kb "hanke2011ternary" "§4, Lemma 4.2 and Thm. 4.12, pp. 10, 15 (finitely many genera at p | 2, F_p = Q_2)"]
theorem dyNF_finite (h : IsQ2Prime v) (S : LocalSqCl v) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c}.Finite := by
  obtain ⟨w₂, h2, ⟨σ⟩⟩ := exists_transport h
  rw [genStar_eq_preimage σ]
  exact (ternaryLocalTablesNF_rat.fin w₂ (sqMap σ S) c).preimage (locMap σ).injective.injOn

/-- **No primitive ternary genus of unit Hessian determinant at $\mathfrak p \mid 2$** ($F_{\mathfrak p} \cong \mathbb Q_2$). -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 20-21 (no genus for ν = 0, F_p = Q_2)"]
theorem dyNF_zero (h : IsQ2Prime v) (S : LocalSqCl v) (hS : (ordS v) S = 0) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c} = ∅ := by
  obtain ⟨w₂, h2, ⟨σ⟩⟩ := exists_transport h
  have ho := ordS_sqMap h w₂ h2 σ S (by rw [hS])
  rw [hS] at ho
  rw [genStar_eq_preimage σ, ternaryLocalTablesNF_rat.dy_zero twoSplitsCompletely_rat w₂ h2 _ ho c,
    Set.preimage_empty]

/-- **Table 5.3, $A^*$ column, at a prime $\mathfrak p \mid 2$ with $F_{\mathfrak p} \cong \mathbb Q_2$, for the true local
genera:** $\sum_{G\in\mathrm{Gen}^{*,+}}\frac{3/16}{\beta(G)} + \sum_{G\in\mathrm{Gen}^{*,-}}\frac{3/16}{\beta(G)} = $ `dyadicA ν`,
$\nu = \operatorname{ord}_{\mathfrak p}S \ge 1$.  Unconditional (transport from $\mathbb Q_2$). -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 20-21 (A* column, true local genera, F_p = Q_2)"]
theorem dyNF_A (h : IsQ2Prime v) (S : LocalSqCl v) (hS : 1 ≤ (ordS v) S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (3 / 16 : ℝ) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (3 / 16 : ℝ) / G.beta) =
      ((dyadicA ((ordS v) S).toNat : ℚ) : ℝ) := by
  obtain ⟨w₂, h2, ⟨σ⟩⟩ := exists_transport h
  have hv₂ := isQ2Prime_rat w₂ h2
  have ho := ordS_sqMap h w₂ h2 σ S (by omega)
  have hQ := ternaryLocalTablesNF_rat.dy_A twoSplitsCompletely_rat w₂ h2 (sqMap σ S) (by rw [ho]; exact hS)
  rw [finsum_const_div_beta, finsum_const_div_beta] at hQ
  rw [finsum_const_div_beta, finsum_const_div_beta, invBetaSum_transport h hv₂ σ S 1,
    invBetaSum_transport h hv₂ σ S (-1), ← ho]
  exact hQ

/-- **Table 5.3, $B^*$ column, at a prime $\mathfrak p \mid 2$ with $F_{\mathfrak p} \cong \mathbb Q_2$, for the true local
genera:** $\sum_{G\in\mathrm{Gen}^{*,+}}\frac{3/16}{\beta(G)} - \sum_{G\in\mathrm{Gen}^{*,-}}\frac{3/16}{\beta(G)} = $
`dyadicB ε ν`, $\nu = \operatorname{ord}_{\mathfrak p}S \ge 1$, $\varepsilon = (-1, x)_{\mathfrak p}$ for any $x$ in the rational
squareclass of $S$.  Unconditional (transport from $\mathbb Q_2$). -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 20-21 (B* column, true local genera, F_p = Q_2)"]
theorem dyNF_B (h : IsQ2Prime v) (S : LocalSqCl v) (hS : 1 ≤ (ordS v) S) (x : (v.adicCompletion F)ˣ)
    (hx : rhoLocal v S = SqCl.mk x) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (3 / 16 : ℝ) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (3 / 16 : ℝ) / G.beta) =
      ((dyadicB (toSign (hilbertSymbol (v.adicCompletion F) (-1) (x : v.adicCompletion F)))
        ((ordS v) S).toNat : ℚ) : ℝ) := by
  obtain ⟨w₂, h2, ⟨σ⟩⟩ := exists_transport h
  have hv₂ := isQ2Prime_rat w₂ h2
  have ho := ordS_sqMap h w₂ h2 σ S (by omega)
  have hQ := ternaryLocalTablesNF_rat.dy_B twoSplitsCompletely_rat w₂ h2 (sqMap σ S) (by rw [ho]; exact hS)
    (unitsMap σ x) (rhoLocal_sqMap σ S x hx)
  rw [finsum_const_div_beta, finsum_const_div_beta] at hQ
  have hh : hilbertSymbol (w₂.adicCompletion ℚ) (-1) ((unitsMap σ x : (w₂.adicCompletion ℚ)ˣ) : w₂.adicCompletion ℚ) =
      hilbertSymbol (v.adicCompletion F) (-1) (x : v.adicCompletion F) := by
    rw [unitsMap_val, ← hilbertSymbol_equiv (fracIso σ) (-1) (x : v.adicCompletion F), map_neg, map_one]
  rw [hh, ho] at hQ
  rw [finsum_const_div_beta, finsum_const_div_beta, invBetaSum_transport h hv₂ σ S 1,
    invBetaSum_transport h hv₂ σ S (-1)]
  exact hQ

end Fields

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Ternary.NF.TwoSplitsCompletely.isQ2Prime
#print axioms QuadFormsKB.Hanke2011Structure.dyNF_finite
#print axioms QuadFormsKB.Hanke2011Structure.dyNF_zero
#print axioms QuadFormsKB.Hanke2011Structure.dyNF_A
#print axioms QuadFormsKB.Hanke2011Structure.dyNF_B
