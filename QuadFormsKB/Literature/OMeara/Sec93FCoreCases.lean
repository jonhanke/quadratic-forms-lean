/-
# O'Meara 93:28, sufficiency: the cases where conditions (i)–(iii) decide $FK_1$

**Setting** (as in `Sec93E.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275)
* `isSquare_of_sqEquivMod`: $y \cong 1 \bmod \mathfrak f$ with $\mathfrak f \subseteq 4\mathfrak p$ makes $y$ a
  square (Local Square Theorem 63:1);
* `exists_lagrangian_of_cond`: if $dL_1/dK_1 \cong 1 \bmod \mathfrak f$ with $\mathfrak f \subseteq 4\mathfrak p$ and
  $FL_1 \to FK_1 \perp \langle c\rangle$ ($c \ne 0$), then a hyperbolic $FL_1$ makes $FK_1$ hyperbolic
  ("condition (ii) holds. Hence in this case we have $FL_1 \cong FK_1$", p. 274).
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreSpace

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreCases

section Square

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- **Local Square Theorem, congruence form** (O'Meara 1963, 63:1, p. 159): if $y \cong 1 \bmod \mathfrak f$
(`SqEquivMod`) and every element of $\mathfrak f$ is $4m$ with $m \in \mathfrak p$, then $y$ is a square in $F$. -/
@[kb "omeara1963" "§63A, 63:1, p. 159 (y ≅ 1 mod 4p is a square), as used in §93F, p. 274"]
theorem isSquare_of_sqEquivMod {X : Submodule R F}
    (hX : ∀ x ∈ X, ∃ m ∈ maximalIdeal R, x = 4 * algebraMap R F m) {y : F} (hy : SqEquivMod X y 1) :
    ∃ r : F, y = r ^ 2 := by
  obtain ⟨-, ε, hε, hmem⟩ := hy
  obtain ⟨m, hm, hx⟩ := hX _ hmem
  obtain ⟨v, rfl⟩ := hε
  set e : R := (v : R) with he
  have hm' : m * (↑v⁻¹ : R) ^ 2 ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hm
  obtain ⟨s, hs⟩ := QuadFormsKB.OMeara.isSquare_one_add_four_mul (R := R) hm'
  refine ⟨algebraMap R F (e * s), ?_⟩
  have hy' : y = algebraMap R F e ^ 2 + 4 * algebraMap R F m := by
    rw [one_mul] at hx; linear_combination hx
  have hev : e * (↑v⁻¹ : R) = 1 := by rw [he]; exact Units.mul_inv v
  have key : (e * s) ^ 2 = e ^ 2 + 4 * m := by
    have : (e * s) ^ 2 = e ^ 2 * (s * s) := by ring
    rw [this, ← hs]
    linear_combination (4 * m) * (e * (↑v⁻¹ : R) + 1) * hev
  rw [hy', ← map_pow (algebraMap R F) (e * s), key, map_add, map_pow, map_mul, map_ofNat]

end Square

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$FK_1$ hyperbolic from the conditions** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7,
pp. 274–275): let $M$, $N$ be regular finitely generated lattices of the same rank with
$dM/dN \cong 1 \bmod \mathfrak f$, $\mathfrak f \subseteq 4\mathfrak p$, and $FM \to FN \perp \langle c\rangle$ for
some $c \ne 0$. Then $FM \cong FN$, so if $FM$ contains a totally isotropic subspace $T$ with
$\operatorname{rank} M \le 2\dim T$, so does $FN$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (condition (ii) gives FL₁ ≅ FK₁)"]
theorem exists_lagrangian_of_cond {M N : Submodule R V} (hMfg : M.FG) (hNfg : N.FG) (hMreg : IsRegular Q M)
    (hNreg : IsRegular Q N) (hrk : finrank R M = finrank R N) {X : Submodule R F}
    (hX : ∀ x ∈ X, ∃ m ∈ maximalIdeal R, x = 4 * algebraMap R F m) (hd : DiscQuotSqEquivMod Q M N X) {c : F}
    (hc : c ≠ 0) (hrep : SpanRepresents Q M N c)
    (hT : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (M : Set V)) ∧
      finrank R M ≤ 2 * finrank F T) :
    ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (N : Set V)) ∧
      finrank R N ≤ 2 * finrank F T := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hMfg
  obtain ⟨b₀⟩ := exists_basis (R := R) (F := F) hNfg
  let b' : Basis (Fin (finrank R M)) R N := b₀.reindex (finCongr hrk.symm)
  have hdN := Transfer28.det_gram_ne_zero_of_isRegular Q hNreg b'
  obtain ⟨r, hr⟩ := isSquare_of_sqEquivMod hX (Transfer28.discQuot_bases Q hd b b' hdN)
  have hr' : (gram Q fun i => (b i : V)).det = r ^ 2 * (gram Q fun i => (b' i : V)).det := by
    rw [← hr]; field_simp
  obtain ⟨e⟩ := CoreSpace.spanIso_of_spanRepresents Q b b' hMreg hNreg hr' hc hrep
  exact CoreSpace.exists_lagrangian_of_spanIso Q e hrk hT

end Main

section Rest

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

open Suff28

/-- **The core of 93:28 outside the directly decided cases** (O'Meara 1963, §93F, proof of the sufficiency, steps
4–8, pp. 274–276), *named statement*: `CoreHyp.SuffCoreHyp` with the additional hypothesis that the conditions at the
first index do not already decide $FK_1$, i.e. it is not the case that $\mathfrak f_1 \subseteq 4\mathfrak p$ and one
of the representations (ii), (iii) is required ($\mathfrak f_1 \subsetneq 4a_2\mathfrak w_2^{-1}$ or
$\mathfrak f_1 \subsetneq 4a_1\mathfrak w_1^{-1}$; $0$-based indices `0`, `1` here). In the excluded cases
$FK_1 \cong FL_1$ by the discriminant and Witt's theorem (`exists_lagrangian_of_cond`; O'Meara p. 274, "condition
(ii) holds. Hence in this case we have $FL_1 \cong FK_1$"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276 (cases not decided by (i)–(iii))"]
structure SuffCoreHypRest : Prop where
  core : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ¬ ((∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
        (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))) →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

variable {R F}

/-- **`SuffCoreHyp` from `SuffCoreHypRest`**: in the cases decided by the conditions at the first index, the given
splitting of $K$ already has $FK_1$ hyperbolic (`exists_lagrangian_of_cond`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (FL₁ ≅ FK₁ when (i) and (ii) or (iii) decide)"]
theorem suffCoreHyp_of_rest (h : SuffCoreHypRest.{u, v} R F) : CoreHyp.SuffCoreHyp.{u, v} R F := by
  refine ⟨fun {V} _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC => ?_⟩
  by_cases hdec : (∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
      (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
        fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))
  · refine ⟨Ks, hKs, ?_⟩
    have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
    have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
    have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
    have ha0 : ∀ k, a k ≠ 0 := fun k =>
      (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
    have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
    have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKs.1.split.iSup_eq ▸ le_iSup Ks 0)
    have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
    have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
    obtain ⟨⟨h0, hTy⟩, -, -⟩ := hS
    have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
    have hrk : finrank R (Ls 0) = finrank R (Ks 0) := by have := (hTy 0).1; rwa [hc] at this
    obtain ⟨h1, h2, h3⟩ := hC 0 1 (by simp)
    have hjL : jordanChain Ls 0 = Ls 0 := jordanChain_zero Ls 0 rfl
    have hjK : jordanChain Ks 0 = Ks 0 := jordanChain_zero Ks 0 rfl
    rw [hjL, hjK] at h1 h2 h3
    rcases hdec with ⟨hX, hlt | hlt⟩
    · exact exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 1) (h2 hlt) (hT 0)
    · exact exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 0) (h3 hlt) (hT 0)
  · exact h.core Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC hdec

end Rest

section Final

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 from the remaining core** (O'Meara 1963, §93F, pp. 267–276): over a dyadic field with
`LocalHilbertField`, the named statement `SuffCoreHypRest` implies `DyadicClassification`. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276"]
theorem dyadicClassification_of_rest (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], PadicClass.LocalHilbertField F)
    (h : ∀ [CharZero F], SuffCoreHypRest.{u, v} R F) : DyadicClassification R Q :=
  CoreSpace.dyadicClassification_of_hyp Q hHil (fun [CharZero F] => suffCoreHyp_of_rest h)

end Final

section NumberField

open NumberField IsDedekindDomain

universe v

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field, from the remaining core** (O'Meara 1963,
§93F, pp. 267–276): only the named statement `SuffCoreHypRest` for $F_\mathfrak p$ is assumed. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field)"]
theorem dyadicClassification_rest_nf
    (h : SuffCoreHypRest.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_of_rest Q (HasseIsoNF.localHilbertField_adicCompletion v) h

end NumberField

end QuadFormsKB.OMeara.CoreCases
