/-
# O'Meara §63: dyadic fields, residues, and binary spaces over a local field

**Setting** (as in `Sec63A.lean`, `Sec63B.lean`). $R$ is a Henselian discrete valuation ring (O'Meara's $\mathfrak o$) with
finite residue field $k$, $F$ its fraction field (a local field: $F = F_v$ for a number field, or $\mathbb Q_p$), $\pi$ a
prime element (`Irreducible π`), $2 \ne 0$ in $R$ (characteristic of $F$ not $2$); $\Delta \in R$ is a unit of quadratic
defect $\mathfrak d(\Delta) = 4\mathfrak o$ (O'Meara's fixed unit, 63:4). `dord hπ` is the order function at $\pi$
(`Sec63A.lean`). For 63:15 (iii), (iv) the local field is any field $K$ of characteristic $0$ satisfying the abstract
Hilbert-symbol axioms `PadicClass.LocalHilbertField K` (`PadicClassification.lean`); these hold for $\mathbb Q_p$ and
for every completion $F_v$ of a number field at a finite place, dyadic included
(`HasseIsoNF.localHilbertField_adicCompletion`). Quadratic spaces are Mathlib `QuadraticForm K V`; *regular* is
`Q.radical = ⊥`.

**Defines**
* `IsDyadic R`, `IsNonDyadic R` (§63, p. 158): the residue field has characteristic $2$, resp. not;
* `unitSqClass R F` ($\mathfrak u\dot F^{2}$) and `primeUnitSqClass hπ` ($\pi\mathfrak u\dot F^{2}$), the sets of §63C, p. 168.

**Proves**
* 63.r2 (p. 158): `isDyadic_iff_not_isUnit_two` (comparison with the hypotheses $2 \in \mathfrak p$ used in `Sec63A`),
  `isDyadic_adicCompletionIntegers_iff` (for the completion of a number field at a finite place $v$:
  dyadic iff `(2 : 𝓞 F) ∈ v.asIdeal`);
* 63.r4 (p. 159): `card_sq_residue_nondyadic`, `index_sq_residue_nondyadic`;
* 63.r5 (p. 159): `isSquare_residue_of_dyadic`, `exists_unit_sq_congr_of_dyadic`;
* 63:15 (i) (p. 168): `values_of_disc_neg_delta`;
* 63:15 (iii), (iv) (pp. 168-169): `equivalent_iff_values_eq`, `equivalent_of_values_subset`;
* 63.r27, inside 63:16 (p. 169), for $E = F(\sqrt\Delta)$ with $\Delta$ a unit of defect $4\mathfrak o$:
  `isUnit_iff_norm_isUnit` ($N_{E/F}\alpha$ is a unit iff $\alpha$ is a unit of the integral closure of $R$ in $E$;
  by a Hensel argument, no use of Theorem 14:1) and `exists_unit_norm_eq` ($N_{E/F}\mathfrak U = \mathfrak u$).
-/
import QuadFormsKB.Literature.OMeara.Sec63B
import QuadFormsKB.Literature.OMeara.Sec62Rest
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open Submodule IsLocalRing QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### 63.r2: dyadic and non-dyadic -/

section Dyadic

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- **Dyadic local ring** (O'Meara 1963, §63, p. 158): the local field with ring of integers $R$ is *dyadic* if its
residue class field $R/\mathfrak p$ has characteristic $2$. -/
@[kb "omeara1963" "§63, p. 158 (dyadic local field: the residue field has characteristic 2)"]
def IsDyadic : Prop := CharP (ResidueField R) 2

/-- **Non-dyadic local ring** (O'Meara 1963, §63, p. 158): not dyadic. -/
@[kb "omeara1963" "§63, p. 158 (non-dyadic local field: the residue field has characteristic ≠ 2)"]
def IsNonDyadic : Prop := ¬ IsDyadic R

/-- **Comparison with the hypotheses used elsewhere** (O'Meara 1963, §63, p. 158): $R$ is dyadic iff $2$ is not a unit
of $R$, i.e. $2 \in \mathfrak p$ (the form in which dyadic and non-dyadic are used in `Sec63A.lean`, `Sec63B.lean`
and for number fields, `(2 : 𝓞 F) ∈ v.asIdeal`). -/
@[kb "omeara1963" "§63, p. 158 (dyadic iff 2 ∈ 𝔭)"]
theorem isDyadic_iff_not_isUnit_two : IsDyadic R ↔ ¬ IsUnit (2 : R) := by
  unfold IsDyadic
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  have : ((2 : ℕ) : ResidueField R) = residue R 2 := by
    rw [Nat.cast_ofNat, map_ofNat]
  rw [this, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]

end Dyadic

section NumberFieldDyadic

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- **Dyadic completions of a number field** (O'Meara 1963, §63, p. 158): the completion $F_v$ of a number field at a
finite place $v$ is dyadic (its ring of integers `v.adicCompletionIntegers F` has residue field of characteristic $2$)
if and only if $2 \in \mathfrak p_v$, i.e. `(2 : 𝓞 F) ∈ v.asIdeal`; this is the form of the condition used in the library
for number fields (e.g. `SqDual.hilbert_units_nondyadic`). -/
@[kb "omeara1963" "§63, p. 158 (dyadic iff 2 ∈ 𝔭, for the completion of a number field)"]
theorem isDyadic_adicCompletionIntegers_iff : IsDyadic (v.adicCompletionIntegers F) ↔ (2 : 𝓞 F) ∈ v.asIdeal := by
  rw [isDyadic_iff_not_isUnit_two, ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have hint := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
  have h2 : Valued.v ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = v.intValuation (2 : 𝓞 F) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
    simp only [map_ofNat] at h
    have e2 : HeightOneSpectrum.valuation F v (2 : F) = v.intValuation (2 : 𝓞 F) := by
      have e0 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
      rw [e0, HeightOneSpectrum.valuation_of_algebraMap]
    rw [e2] at h
    exact h
  have hu : IsUnit (2 : v.adicCompletionIntegers F) ↔
      Valued.v ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 :=
    hint.isUnit_iff_valuation_eq_one (x := (2 : v.adicCompletionIntegers F))
  rw [hu, h2]
  have hle : v.intValuation (2 : 𝓞 F) ≤ 1 := HeightOneSpectrum.intValuation_le_one v 2
  constructor
  · intro h; exact lt_of_le_of_ne hle h
  · intro h; exact h.ne

end NumberFieldDyadic

/-! ### 63.r4, 63.r5: squares among the residues -/

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]

private lemma ringChar_residue_ne_two (h : IsNonDyadic R) : ringChar (ResidueField R) ≠ 2 := by
  intro h2
  have := ringChar.charP (ResidueField R)
  rw [h2] at this
  exact h this

/-- **Half of the nonzero residues are squares, non-dyadic case** (O'Meara 1963, §63, p. 159, from §62): if $F$ is
non-dyadic, its residue class field $k = R/\mathfrak p$ is a finite field of odd characteristic with $q = Nk$ elements,
and the group $\dot k^{2}$ of nonzero squares (range of the squaring map of $k^\times$) has $(q-1)/2$ elements, here
$2\,\lvert\dot k^{2}\rvert = q - 1$. -/
@[kb "omeara1963" "§63, p. 159 (non-dyadic: exactly half of the nonzero residues are squares)"]
theorem card_sq_residue_nondyadic (h : IsNonDyadic R) :
    2 * Nat.card (powMonoidHom 2 : (ResidueField R)ˣ →* (ResidueField R)ˣ).range =
      Nat.card (ResidueField R) - 1 := by
  have := Fintype.ofFinite (ResidueField R)
  have := card_sq_units (F := ResidueField R) (ringChar_residue_ne_two h)
  rwa [← Nat.card_eq_fintype_card] at this

/-- **The squares of the residue field have index $2$, non-dyadic case** (O'Meara 1963, §63, p. 159, from §62):
$(\dot k : \dot k^{2}) = 2$ for the residue class field $k$ of a non-dyadic local field. -/
@[kb "omeara1963" "§63, p. 159 (non-dyadic: the nonzero residues modulo squares have order 2)"]
theorem index_sq_residue_nondyadic (h : IsNonDyadic R) :
    (powMonoidHom 2 : (ResidueField R)ˣ →* (ResidueField R)ˣ).range.index = 2 := by
  have := Fintype.ofFinite (ResidueField R)
  exact index_sq_units (F := ResidueField R) (ringChar_residue_ne_two h)

/-- **Every residue is a square, dyadic case** (O'Meara 1963, §63, p. 159): if $F$ is dyadic, its residue class field
is a finite field of characteristic $2$, hence perfect, and every residue is a square. -/
@[kb "omeara1963" "§63, p. 159 (dyadic: every residue is a square)"]
theorem isSquare_residue_of_dyadic (h : IsDyadic R) (x : ResidueField R) : IsSquare x := by
  have := Fintype.ofFinite (ResidueField R)
  exact FiniteField.isSquare_of_char_two (ringChar.eq_iff.2 h) x

/-- **Units are congruent up to squares mod $\pi$, dyadic case** (O'Meara 1963, §63, p. 159): if $F$ is dyadic, for
units $\varepsilon, \varepsilon'$ of $R$ there is a unit $\delta$ with $\varepsilon \equiv \varepsilon'\delta^{2}
\pmod{\pi}$, i.e. $\pi \mid \varepsilon - \varepsilon'\delta^{2}$. -/
@[kb "omeara1963" "§63, p. 159 (dyadic: for units ε, ε' there is a unit δ with ε ≡ ε'δ² mod π)"]
theorem exists_unit_sq_congr_of_dyadic [IsDomain R] [IsDiscreteValuationRing R] (h : IsDyadic R) {π : R}
    (hπ : Irreducible π) {ε ε' : R} (hε : IsUnit ε) (hε' : IsUnit ε') :
    ∃ δ : R, IsUnit δ ∧ π ∣ ε - ε' * δ ^ 2 := by
  obtain ⟨r, hr⟩ := isSquare_residue_of_dyadic h (residue R ε / residue R ε')
  obtain ⟨δ, hδ⟩ := residue_surjective r
  have hε0 : residue R ε ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hε
  have hε'0 : residue R ε' ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hε'
  have hres : residue R ε = residue R ε' * (r * r) := by
    rw [← hr]; field_simp
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hε0 (by rw [hres]; simp)
  refine ⟨δ, (residue_ne_zero_iff_isUnit _).1 (by rw [hδ]; exact hr0), ?_⟩
  rw [← B63.mem_max_iff hπ, ← residue_eq_zero_iff, map_sub, map_mul, map_pow, hδ, hres]
  ring

end Residue

/-! ### The classes $\mathfrak u\dot F^{2}$ and $\pi\mathfrak u\dot F^{2}$ -/

section Classes

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- **$\mathfrak u\dot F^{2}$** (O'Meara 1963, §63C, p. 168): the set of elements $\varepsilon z^{2}$ with $\varepsilon$ a
unit of $R$ and $z \in F^\times$, i.e. the nonzero elements of even order. -/
@[kb "omeara1963" "§63C, 63:15 (i), p. 168 (the set 𝔲Ḟ²)"]
def unitSqClass : Set F := {γ | ∃ ε : R, IsUnit ε ∧ ∃ z : F, z ≠ 0 ∧ γ = algebraMap R F ε * z ^ 2}

variable {R F}

/-- **$\pi\mathfrak u\dot F^{2}$** (O'Meara 1963, §63C, p. 168): the set of elements $\pi\varepsilon z^{2}$ with
$\varepsilon$ a unit of $R$ and $z \in F^\times$, i.e. the elements of odd order, for the prime element $\pi$. -/
@[kb "omeara1963" "§63C, 63:15 (i), p. 168 (the set π𝔲Ḟ²)"]
def primeUnitSqClass {π : R} (_ : Irreducible π) : Set F :=
  {γ | ∃ ε : R, IsUnit ε ∧ ∃ z : F, z ≠ 0 ∧ γ = algebraMap R F π * algebraMap R F ε * z ^ 2}

variable {π : R}

theorem mem_unitSqClass_iff (hπ : Irreducible π) {γ : F} :
    γ ∈ unitSqClass R F ↔ γ ≠ 0 ∧ Even (dord hπ γ) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  constructor
  · rintro ⟨ε, hε, z, hz, rfl⟩
    have h1 : algebraMap R F ε ≠ 0 := (map_ne_zero_iff _ alg_inj).2 hε.ne_zero
    refine ⟨mul_ne_zero h1 (pow_ne_zero 2 hz), ?_⟩
    rw [dord_mul hπ h1 (pow_ne_zero 2 hz), dord_unit hπ hε, dord_sq hπ hz]
    exact ⟨dord hπ z, by ring⟩
  · rintro ⟨hγ, m, hm⟩
    obtain ⟨u, hu, e⟩ := dord_spec hπ hγ
    rw [hm, zpow_add₀ hne] at e
    exact ⟨u, hu, algebraMap R F π ^ m, zpow_ne_zero _ hne, by rw [e, _root_.sq]⟩

theorem mem_primeUnitSqClass_iff (hπ : Irreducible π) {γ : F} :
    γ ∈ primeUnitSqClass hπ ↔ γ ≠ 0 ∧ Odd (dord hπ γ) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  constructor
  · rintro ⟨ε, hε, z, hz, rfl⟩
    have h1 : algebraMap R F ε ≠ 0 := (map_ne_zero_iff _ alg_inj).2 hε.ne_zero
    have h2 : algebraMap R F π * algebraMap R F ε ≠ 0 := mul_ne_zero hne h1
    refine ⟨mul_ne_zero h2 (pow_ne_zero 2 hz), ?_⟩
    have h3 : dord hπ (algebraMap R F π * algebraMap R F ε) = 1 :=
      dord_eq hπ hε (by rw [zpow_one]; ring)
    rw [dord_mul hπ h2 (pow_ne_zero 2 hz), h3, dord_sq hπ hz]
    exact ⟨dord hπ z, by ring⟩
  · rintro ⟨hγ, m, hm⟩
    obtain ⟨u, hu, e⟩ := dord_spec hπ hγ
    rw [hm, zpow_add₀ hne, zpow_one, two_mul, zpow_add₀ hne] at e
    exact ⟨u, hu, algebraMap R F π ^ m, zpow_ne_zero _ hne, by rw [e, _root_.sq]; ring⟩

end Classes

/-! ### 63:15 (i): binary spaces of discriminant $-\Delta$ -/

section DiscNegDelta

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
variable {π : R}

private lemma two_ne_zero_F (h2 : (2 : R) ≠ 0) : (2 : F) ≠ 0 := by
  rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
  exact (map_ne_zero_iff _ alg_inj).2 h2

/-- $(\Delta, c) = 1$ iff $\operatorname{ord} c$ is even, for $\Delta$ a unit of quadratic defect $4\mathfrak o$ and
$c \ne 0$: by 63:11a, $(\varepsilon, \Delta) = 1$ for units and $(\pi', \Delta) = -1$ for prime elements. -/
private lemma hilbertSymbol_delta_eq_one_iff (h2 : (2 : R) ≠ 0) (hπ : Irreducible π) {Δ : R}
    (hΔ : IsUnit Δ) (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {c : F} (hc : c ≠ 0) :
    hilbertSymbol F (algebraMap R F Δ) c = 1 ↔ Even (dord hπ c) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨u, hu, e⟩ := dord_spec hπ hc
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (dord hπ c)
  · have hev : Even (dord hπ c) := ⟨m, by omega⟩
    have hc' : c = algebraMap R F u * (algebraMap R F π ^ m) ^ 2 := by
      have : algebraMap R F π ^ (dord hπ c) = (algebraMap R F π ^ m) ^ 2 := by
        rw [hm, two_mul, zpow_add₀ hne, _root_.sq]
      rw [← this]; exact e
    have h1 : hilbertSymbol F (algebraMap R F Δ) c = 1 := by
      rw [hilbertSymbol_comm, hc', HM3.hilbertSymbol_mul_sq_left _ _ _ _ (zpow_ne_zero _ hne),
        hilbertSymbol_unit_delta h2 hΔ hΔd hu]
    exact iff_of_true h1 hev
  · have hodd : ¬ Even (dord hπ c) := by
      rw [Int.not_even_iff_odd]; exact ⟨m, hm⟩
    have hirr : Irreducible (π * u) := (irreducible_mul_isUnit hu).2 hπ
    have hc' : c = algebraMap R F (π * u) * (algebraMap R F π ^ m) ^ 2 := by
      have : algebraMap R F π ^ (dord hπ c) = algebraMap R F π * (algebraMap R F π ^ m) ^ 2 := by
        rw [hm, zpow_add₀ hne, zpow_one, two_mul, zpow_add₀ hne, _root_.sq]; ring
      rw [map_mul, mul_comm (algebraMap R F π), mul_assoc, ← this]; exact e
    have h1 : hilbertSymbol F (algebraMap R F Δ) c = -1 := by
      rw [hilbertSymbol_comm, hc', HM3.hilbertSymbol_mul_sq_left _ _ _ _ (zpow_ne_zero _ hne),
        hilbertSymbol_prime_delta h2 hΔ hΔd hirr]
    rw [h1]
    exact iff_of_false (by norm_num) hodd

/-- **63:15 (i): binary spaces of discriminant $-\Delta$** (O'Meara 1963, §63C, p. 168). Let $V$ be a regular binary
quadratic space over the local field $F$ (the fraction field of $R$) with discriminant $dV = -\Delta$, where $\Delta$
is a unit of quadratic defect $4\mathfrak o$: with respect to a base $b$ of $V$, $\det(B(b_i, b_j)) = t^{2}(-\Delta)$
for some $t \in F^\times$ (`hd`; the discriminant is a square class). Then the set $Q(\dot V)$ of nonzero values of $Q$ is
either $\mathfrak u\dot F^{2}$ or $\pi\mathfrak u\dot F^{2}$.

*Remark.* Such $V$ is anisotropic ($-dV = \Delta$ is not a square), so the nonzero values are the values at nonzero
vectors. The book proves this after scaling so that $1 \in Q(V)$ and shows $V$ represents exactly the units there;
unscaled, it is $Q(\dot V) = \alpha\,\mathfrak u\dot F^{2}$ for some $\alpha$, and $\alpha\mathfrak u\dot F^{2}$ is one of the
two sets of the statement (the elements of even, resp. odd, order). -/
@[kb "omeara1963" "§63C, 63:15 (i), p. 168 (dV = −Δ: Q(V) is 𝔲Ḟ² or π𝔲Ḟ²)"]
theorem values_of_disc_neg_delta [Invertible (2 : F)] (h2 : (2 : R) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module F V] (Q : QuadraticForm F V) (b : Basis (Fin 2) F V) (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)})
    (hd : ∃ t : F, t ≠ 0 ∧ (gram Q b).det = t ^ 2 * (-algebraMap R F Δ)) :
    {γ : F | γ ≠ 0 ∧ ∃ x : V, Q x = γ} = unitSqClass R F ∨
      {γ : F | γ ≠ 0 ∧ ∃ x : V, Q x = γ} = primeUnitSqClass hπ := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  have h2F : (2 : F) ≠ 0 := two_ne_zero_F h2
  obtain ⟨t, ht, hdet⟩ := hd
  have hΔ0 : algebraMap R F Δ ≠ 0 := alg_ne_zero_of_unit hΔ
  have hd0 : t ^ 2 * (-algebraMap R F Δ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ht) (neg_ne_zero.2 hΔ0)
  obtain ⟨a, ha, hrep⟩ := B63.rep_NF Q b h2F hdet hd0
  have key : ∀ γ : F, γ ≠ 0 → ((∃ x : V, Q x = γ) ↔ Even (dord hπ γ - dord hπ a)) := by
    intro γ hγ
    rw [hrep γ]
    have hc : γ / a ≠ 0 := div_ne_zero hγ ha
    have hdiv : dord hπ (γ / a) = dord hπ γ - dord hπ a := by
      rw [div_eq_mul_inv, dord_mul hπ hγ (inv_ne_zero ha), B63.dord_inv' hπ ha]; ring
    rw [← hdiv, ← hilbertSymbol_delta_eq_one_iff h2 hπ hΔ hΔd hc,
      HN.hilbertSymbol_eq_one_iff_norm F h2F hΔ0]
    constructor
    · rintro ⟨s, u, h⟩
      exact ⟨s, t * u, by rw [← h]; ring⟩
    · rintro ⟨x₀, x₁, h⟩
      exact ⟨x₀, x₁ / t, by rw [h]; field_simp; ring⟩
  rcases Int.even_or_odd (dord hπ a) with hev | hodd
  · left
    ext γ
    rw [mem_unitSqClass_iff hπ]
    refine and_congr_right fun hγ => ?_
    rw [key γ hγ, Int.even_sub]
    simp [hev]
  · right
    ext γ
    rw [mem_primeUnitSqClass_iff hπ]
    refine and_congr_right fun hγ => ?_
    rw [key γ hγ, Int.even_sub, ← Int.not_even_iff_odd]
    have : ¬ Even (dord hπ a) := Int.not_even_iff_odd.2 hodd
    simp [this]

end DiscNegDelta

/-! ### 63:15 (iii), (iv): isometry of binary spaces and their values -/

section Binary

open PadicClass

variable {K : Type*} [Field K] [CharZero K]

private lemma hasseVec_two (a₀ a₁ : K) : hasseVec ![a₀, a₁] = hilbertSymbol K a₀ a₁ := by
  simp [hasseVec, Fin.prod_univ_two]

private lemma ne_zero_two {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) : ∀ i, (![a₀, a₁] : Fin 2 → K) i ≠ 0 :=
  fun i => by fin_cases i <;> simpa

/-- Two binary diagonal forms with the same Hasse symbol and the same character $x \mapsto (x, -d)$ are isometric. -/
private lemma isometric_of_chi_eq (hK : LocalHilbertField K) {a₀ a₁ b₀ b₁ : K} (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0)
    (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) (hε : hilbertSymbol K a₀ a₁ = hilbertSymbol K b₀ b₁)
    (hχ : ∀ x : K, x ≠ 0 → hilbertSymbol K x (-(a₀ * a₁)) = hilbertSymbol K x (-(b₀ * b₁))) :
    (QuadForm.diag ![a₀, a₁]).IsometricIn K (QuadForm.diag ![b₀, b₁]) := by
  have hda : -(a₀ * a₁) ≠ 0 := neg_ne_zero.2 (mul_ne_zero ha₀ ha₁)
  have hdb : -(b₀ * b₁) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hb₀ hb₁)
  rw [isometric_iff_invariants hK (ne_zero_two ha₀ ha₁) (ne_zero_two hb₀ hb₁), hasseVec_two, hasseVec_two]
  refine ⟨?_, hε⟩
  have hsq : IsSquare (-(a₀ * a₁) * -(b₀ * b₁)) := by
    by_contra hns
    obtain ⟨y, hy, hy1⟩ := hK.exists_neg_one _ (mul_ne_zero hda hdb) hns
    rw [hK.mul_left _ _ _ hda hdb hy, hilbertSymbol_comm K (-(a₀ * a₁)) y,
      hilbertSymbol_comm K (-(b₀ * b₁)) y, ← hχ y hy] at hy1
    rcases hs_pm y (-(a₀ * a₁)) with h | h <;> rw [h] at hy1 <;> norm_num at hy1
  obtain ⟨r, hr⟩ := hsq
  have hprod : a₀ * a₁ * (b₀ * b₁) = r * r := by rw [← hr]; ring
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero ha₀ ha₁) (mul_ne_zero hb₀ hb₁) (by simpa using hprod)
  refine ⟨r / (a₀ * a₁), div_ne_zero hr0 (mul_ne_zero ha₀ ha₁), ?_⟩
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : a₀ * a₁ ≠ 0 := mul_ne_zero ha₀ ha₁
  field_simp
  linear_combination hprod

/-- The $\pm 1$-valued function $x \mapsto (x, -d)\,(a_0, a_1)$ takes the value $1$ exactly on the nonzero values
represented by $\langle a_0, a_1 \rangle$. -/
private lemma isometric_of_values_eq (hK : LocalHilbertField K) {a₀ a₁ b₀ b₁ : K} (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0)
    (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0)
    (h : ∀ x : K, x ≠ 0 → ((QuadForm.diag ![a₀, a₁]).RepresentsIn K x ↔
      (QuadForm.diag ![b₀, b₁]).RepresentsIn K x)) :
    (QuadForm.diag ![a₀, a₁]).IsometricIn K (QuadForm.diag ![b₀, b₁]) := by
  have hχ' : ∀ x : K, x ≠ 0 → (hilbertSymbol K x (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ ↔
      hilbertSymbol K x (-(b₀ * b₁)) = hilbertSymbol K b₀ b₁) := fun x hx => by
    rw [← represents_two_iff hK ha₀ ha₁ hx, ← represents_two_iff hK hb₀ hb₁ hx]; exact h x hx
  have hf : ∀ x : K, x ≠ 0 → hilbertSymbol K x (-(a₀ * a₁)) * hilbertSymbol K a₀ a₁ =
      hilbertSymbol K x (-(b₀ * b₁)) * hilbertSymbol K b₀ b₁ := fun x hx => by
    have := hχ' x hx
    rcases hs_pm x (-(a₀ * a₁)) with h1 | h1 <;> rcases hs_pm a₀ a₁ with h2 | h2 <;>
      rcases hs_pm x (-(b₀ * b₁)) with h3 | h3 <;> rcases hs_pm b₀ b₁ with h4 | h4 <;>
      (revert this; simp only [h1, h2, h3, h4]; try norm_num)
  have hε : hilbertSymbol K a₀ a₁ = hilbertSymbol K b₀ b₁ := by
    have := hf 1 one_ne_zero
    rwa [hs_one_left, hs_one_left, one_mul, one_mul] at this
  refine isometric_of_chi_eq hK ha₀ ha₁ hb₀ hb₁ hε fun x hx => ?_
  have := hf x hx
  rw [hε] at this
  have hne : hilbertSymbol K b₀ b₁ ≠ 0 := by
    rcases hs_pm b₀ b₁ with h | h <;> rw [h] <;> norm_num
  exact mul_right_cancel₀ hne this

/-- If the nonzero values of $\langle a_0, a_1\rangle$ are among those of $\langle b_0, b_1\rangle$ and the second form is
anisotropic ($-b_0b_1$ not a square), the two forms are isometric. -/
private lemma isometric_of_values_subset (hK : LocalHilbertField K) {a₀ a₁ b₀ b₁ : K} (ha₀ : a₀ ≠ 0)
    (ha₁ : a₁ ≠ 0) (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) (hnb : ¬ IsSquare (-(b₀ * b₁)))
    (h : ∀ x : K, x ≠ 0 → ((QuadForm.diag ![a₀, a₁]).RepresentsIn K x →
      (QuadForm.diag ![b₀, b₁]).RepresentsIn K x)) :
    (QuadForm.diag ![a₀, a₁]).IsometricIn K (QuadForm.diag ![b₀, b₁]) := by
  have hda : -(a₀ * a₁) ≠ 0 := neg_ne_zero.2 (mul_ne_zero ha₀ ha₁)
  have hdb : -(b₀ * b₁) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hb₀ hb₁)
  have hsub : ∀ x : K, x ≠ 0 → (hilbertSymbol K x (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ →
      hilbertSymbol K x (-(b₀ * b₁)) = hilbertSymbol K b₀ b₁) := fun x hx => by
    rw [← represents_two_iff hK ha₀ ha₁ hx, ← represents_two_iff hK hb₀ hb₁ hx]; exact h x hx
  have hεa : hilbertSymbol K a₀ (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ :=
    (represents_two_iff hK ha₀ ha₁ ha₀).1 (by simpa using represents_coeff (![a₀, a₁]) 0)
  have hεb : hilbertSymbol K a₀ (-(b₀ * b₁)) = hilbertSymbol K b₀ b₁ := hsub a₀ ha₀ hεa
  have hmul : ∀ (x y d : K), x ≠ 0 → y ≠ 0 → d ≠ 0 →
      hilbertSymbol K (x * y) d = hilbertSymbol K x d * hilbertSymbol K y d :=
    fun x y d hx hy hd => hK.mul_left x y d hx hy hd
  have hne : ∀ x y : K, hilbertSymbol K x y ≠ 0 := fun x y => by
    rcases hs_pm x y with h | h <;> rw [h] <;> norm_num
  -- the kernel of the first character lies in the kernel of the second
  have hker : ∀ x : K, x ≠ 0 → hilbertSymbol K x (-(a₀ * a₁)) = 1 → hilbertSymbol K x (-(b₀ * b₁)) = 1 := by
    intro x hx hx1
    have h1 : hilbertSymbol K (a₀ * x) (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ := by
      rw [hmul _ _ _ ha₀ hx hda, hεa, hx1, mul_one]
    have h2 := hsub (a₀ * x) (mul_ne_zero ha₀ hx) h1
    rw [hmul _ _ _ ha₀ hx hdb, hεb] at h2
    exact mul_left_cancel₀ (hne b₀ b₁) (by rw [mul_one]; exact h2)
  obtain ⟨w, hw0, hw⟩ := hK.exists_neg_one _ hdb hnb
  rw [hilbertSymbol_comm] at hw
  have hwa : hilbertSymbol K w (-(a₀ * a₁)) = -1 := by
    rcases hs_pm w (-(a₀ * a₁)) with h1 | h1
    · have := hker w hw0 h1
      rw [hw] at this; norm_num at this
    · exact h1
  have hχ : ∀ x : K, x ≠ 0 → hilbertSymbol K x (-(a₀ * a₁)) = hilbertSymbol K x (-(b₀ * b₁)) := by
    intro x hx
    rcases hs_pm x (-(a₀ * a₁)) with h1 | h1
    · rw [h1, hker x hx h1]
    · have h2 : hilbertSymbol K (x * w) (-(a₀ * a₁)) = 1 := by
        rw [hmul _ _ _ hx hw0 hda, h1, hwa]; norm_num
      have h3 := hker (x * w) (mul_ne_zero hx hw0) h2
      rw [hmul _ _ _ hx hw0 hdb, hw] at h3
      rw [h1]
      rcases hs_pm x (-(b₀ * b₁)) with h4 | h4 <;> rw [h4] at h3 <;> simp at h3 ⊢ <;> omega
  have hε : hilbertSymbol K a₀ a₁ = hilbertSymbol K b₀ b₁ := by
    rw [← hεa, ← hεb]; exact hχ a₀ ha₀
  exact isometric_of_chi_eq hK ha₀ ha₁ hb₀ hb₁ hε hχ

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private lemma values_eq_of_equivalent (Q : QuadraticForm K V) (Q' : QuadraticForm K W) (h : Q.Equivalent Q') :
    {γ : K | γ ≠ 0 ∧ ∃ x, Q x = γ} = {γ : K | γ ≠ 0 ∧ ∃ x, Q' x = γ} := by
  obtain ⟨e⟩ := h
  ext γ
  constructor
  · rintro ⟨hγ, x, rfl⟩
    exact ⟨hγ, e x, e.map_app x⟩
  · rintro ⟨hγ, y, rfl⟩
    refine ⟨hγ, e.symm y, ?_⟩
    have := e.map_app (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm

private lemma exists_diag (Q : QuadraticForm K V) (hV : finrank K V = 2) (hQ : Q.radical = ⊥) :
    ∃ a₀ a₁ : K, a₀ ≠ 0 ∧ a₁ ≠ 0 ∧
      Q.Equivalent ((QuadForm.diag ![a₀, a₁]).toQuadraticFormIn K) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hnd : (QuadraticMap.associated (R := K) Q).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr (QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr hQ)
  have key := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hnd.1
  rw [hV] at key
  obtain ⟨w, hw⟩ := key
  refine ⟨w 0, w 1, (w 0).ne_zero, (w 1).ne_zero, hw.trans ?_⟩
  have e : QuadraticMap.weightedSumSquares K w =
      (QuadForm.diag ![(w 0 : K), (w 1 : K)]).toQuadraticFormIn K := by
    ext x
    rw [QuadForm.toQuadraticFormIn_apply, PadicClass.evalIn_diag_self, QuadraticMap.weightedSumSquares_apply]
    simp only [Fin.sum_univ_two, Units.smul_def, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [e]

private lemma rep_iff_value (a : Fin 2 → K) (γ : K) :
    (∃ x, (QuadForm.diag a).toQuadraticFormIn K x = γ) ↔ (QuadForm.diag a).RepresentsIn K γ := by
  rw [representsIn_diag_iff]
  simp only [QuadForm.toQuadraticFormIn_apply, PadicClass.evalIn_diag_self]

private lemma not_isSquare_of_anisotropic (Q : QuadraticForm K V) (hA : Q.Anisotropic) {a₀ a₁ : K}
    (ha₀ : a₀ ≠ 0) (hQe : Q.Equivalent ((QuadForm.diag ![a₀, a₁]).toQuadraticFormIn K)) :
    ¬ IsSquare (-(a₀ * a₁)) := by
  rintro ⟨r, hr⟩
  obtain ⟨e⟩ := hQe
  have hy : (QuadForm.diag ![a₀, a₁]).toQuadraticFormIn K ![r, a₀] = 0 := by
    rw [QuadForm.toQuadraticFormIn_apply, PadicClass.evalIn_diag_self]
    simp [Fin.sum_univ_two]
    linear_combination (-a₀) * hr
  have hx := e.map_app (e.symm ![r, a₀])
  rw [e.apply_symm_apply, hy] at hx
  have hx0 := hA _ hx.symm
  have : (![r, a₀] : Fin 2 → K) = 0 := by
    rw [← e.apply_symm_apply ![r, a₀], hx0, map_zero]
  exact ha₀ (by simpa using congrFun this 1)

/-- **63:15 (iii): a binary space is determined by its values** (O'Meara 1963, §63C, pp. 168–169): let $V, W$ be regular
binary quadratic spaces over a local field $K$ (here: a field of characteristic $0$ satisfying the Hilbert-symbol
axioms `PadicClass.LocalHilbertField`, e.g. $\mathbb Q_p$ or any completion $F_v$ of a number field at a finite
place, dyadic included). Then $V \cong W$ if and only if $Q(\dot V) = Q(\dot W)$, where $Q(\dot V)$ is the set of nonzero
values of $Q$ (spelled `{γ | γ ≠ 0 ∧ ∃ x, Q x = γ}`). The book proves "if" assuming neither space isotropic and
scaling; here no assumption is needed (both spaces are isotropic exactly when their value sets are all of $\dot K$). -/
@[kb "omeara1963" "§63C, 63:15 (iii), pp. 168–169 (binary V ≅ W iff Q(V) = Q(W))"]
theorem equivalent_iff_values_eq (hK : LocalHilbertField K) (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (hV : finrank K V = 2) (hW : finrank K W = 2) (hQ : Q.radical = ⊥) (hQ' : Q'.radical = ⊥) :
    Q.Equivalent Q' ↔
      {γ : K | γ ≠ 0 ∧ ∃ x, Q x = γ} = {γ : K | γ ≠ 0 ∧ ∃ x, Q' x = γ} := by
  refine ⟨values_eq_of_equivalent Q Q', fun hset => ?_⟩
  obtain ⟨a₀, a₁, ha₀, ha₁, hA⟩ := exists_diag Q hV hQ
  obtain ⟨b₀, b₁, hb₀, hb₁, hB⟩ := exists_diag Q' hW hQ'
  have hvA := values_eq_of_equivalent _ _ hA
  have hvB := values_eq_of_equivalent _ _ hB
  have key : ∀ x : K, x ≠ 0 → ((QuadForm.diag ![a₀, a₁]).RepresentsIn K x ↔
      (QuadForm.diag ![b₀, b₁]).RepresentsIn K x) := by
    intro x hx
    rw [← rep_iff_value, ← rep_iff_value]
    have : x ∈ {γ : K | γ ≠ 0 ∧ ∃ y, (QuadForm.diag ![a₀, a₁]).toQuadraticFormIn K y = γ} ↔
        x ∈ {γ : K | γ ≠ 0 ∧ ∃ y, (QuadForm.diag ![b₀, b₁]).toQuadraticFormIn K y = γ} := by
      rw [← hvA, ← hvB, hset]
    simpa [hx] using this
  have hiso := isometric_of_values_eq hK ha₀ ha₁ hb₀ hb₁ key
  have hAB := (QuadForm.isometricIn_iff_equivalent K _ _).1 hiso
  exact hA.trans (hAB.symm.trans hB.symm)

/-- **63:15 (iv): containment of values implies isometry for anisotropic binary spaces** (O'Meara 1963, §63C, p. 169):
let $V, W$ be regular binary quadratic spaces over a local field $K$ (as in `equivalent_iff_values_eq`), with $W$ not
isotropic (`Q'.Anisotropic`). If $Q(\dot V) \subseteq Q(\dot W)$ then $V \cong W$. *Update (unneeded hypothesis):*
the book assumes both spaces not isotropic; the hypothesis on $V$ is not needed, since an isotropic $V$ has
$Q(\dot V) = \dot K$, which no anisotropic $W$ contains. -/
@[kb "omeara1963" "§63C, 63:15 (iv), p. 169 (anisotropic binary: Q(V) ⊆ Q(W) implies V ≅ W)"]
theorem equivalent_of_values_subset (hK : LocalHilbertField K) (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (hV : finrank K V = 2) (hW : finrank K W = 2) (hQ : Q.radical = ⊥) (hQ' : Q'.radical = ⊥)
    (hA' : Q'.Anisotropic)
    (hsub : {γ : K | γ ≠ 0 ∧ ∃ x, Q x = γ} ⊆ {γ : K | γ ≠ 0 ∧ ∃ x, Q' x = γ}) :
    Q.Equivalent Q' := by
  obtain ⟨a₀, a₁, ha₀, ha₁, hA⟩ := exists_diag Q hV hQ
  obtain ⟨b₀, b₁, hb₀, hb₁, hB⟩ := exists_diag Q' hW hQ'
  have hvA := values_eq_of_equivalent _ _ hA
  have hvB := values_eq_of_equivalent _ _ hB
  have key : ∀ x : K, x ≠ 0 → ((QuadForm.diag ![a₀, a₁]).RepresentsIn K x →
      (QuadForm.diag ![b₀, b₁]).RepresentsIn K x) := by
    intro x hx hrep
    rw [← rep_iff_value] at hrep ⊢
    have : x ∈ {γ : K | γ ≠ 0 ∧ ∃ y, (QuadForm.diag ![b₀, b₁]).toQuadraticFormIn K y = γ} := by
      rw [← hvB]; exact hsub (by rw [hvA]; exact ⟨hx, hrep⟩)
    exact this.2
  have hiso := isometric_of_values_subset hK ha₀ ha₁ hb₀ hb₁
    (not_isSquare_of_anisotropic Q' hA' hb₀ hB) key
  have hAB := (QuadForm.isometricIn_iff_equivalent K _ _).1 hiso
  exact hA.trans (hAB.symm.trans hB.symm)

end Binary

/-! ### 63.r27: norms of units in an unramified quadratic extension (63:16) -/

section Unramified

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
variable {E : Type*} [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
variable {Δ : R} {δ : E}

/-- The norm of $x + y\delta$ in the quadratic extension $E = F(\delta)$, $\delta^2 = \Delta$: $x^2 - \Delta y^2$. -/
private lemma norm_formula (hδ : δ ^ 2 = algebraMap R E Δ)
    (hspan : ∀ z : E, ∃ b₀ b₁ : F, z = algebraMap F E b₀ + algebraMap F E b₁ * δ)
    (hnsq : ¬ IsSquare (algebraMap R F Δ)) (x y : F) :
    Algebra.norm F (algebraMap F E x + algebraMap F E y * δ) = x ^ 2 - algebraMap R F Δ * y ^ 2 := by
  classical
  have hδF : δ ^ 2 = algebraMap F E (algebraMap R F Δ) := by
    rw [hδ, ← IsScalarTower.algebraMap_apply]
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro c₀ c₁ h
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    by_cases h1 : c₁ = 0
    · subst h1; simp at h; exact ⟨h, rfl⟩
    · exfalso; apply hnsq
      refine ⟨-c₀ / c₁, ?_⟩
      apply (algebraMap F E).injective
      have h1' : algebraMap F E c₁ ≠ 0 := by simpa using h1
      have hs' : δ = algebraMap F E (-c₀ / c₁) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [← hδF, map_mul, ← hs']
      ring
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), δ]) := by
    intro y _
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![b₀, b₁], ?_⟩
    simp [Fin.sum_univ_two, Algebra.smul_def]
  let bE := Module.Basis.mk hli hsp
  have hb0 : bE 0 = 1 := by simp [bE]
  have hb1 : bE 1 = δ := by simp [bE]
  have hrepr : ∀ c₀ c₁ : F, ∀ i, bE.repr (algebraMap F E c₀ + algebraMap F E c₁ * δ) i = ![c₀, c₁] i := by
    intro c₀ c₁ i
    have : algebraMap F E c₀ + algebraMap F E c₁ * δ = c₀ • bE 0 + c₁ • bE 1 := by
      rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [this]
    fin_cases i <;> simp
  rw [Algebra.norm_eq_matrix_det bE, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one]
  have : (algebraMap F E x + algebraMap F E y * δ) * δ =
      algebraMap F E (algebraMap R F Δ * y) + algebraMap F E x * δ := by
    rw [map_mul]; linear_combination (algebraMap F E y) * hδF
  rw [this, hrepr, hrepr, hrepr, hrepr]
  simp; ring

variable {π : R}

/-- **Hensel step**: if $t \in F$ is not in $R$ and $u \in R$ is a unit, then $X^2 - tX + u$ has a root in $F$. -/
private lemma exists_root_of_not_mem (hπ : Irreducible π) {t : F} (ht : ∀ r : R, algebraMap R F r ≠ t)
    (u : R) : ∃ r : F, r ^ 2 - t * r + algebraMap R F u = 0 := by
  have ht0 : t ≠ 0 := fun h => ht 0 (by rw [h]; simp)
  have hneg : dord hπ t < 0 := by
    by_contra hge
    obtain ⟨r, hr⟩ := exists_alg_of_nonneg hπ ht0 (not_lt.1 hge)
    exact ht r hr
  have hinv : 1 ≤ dord hπ t⁻¹ := by
    rw [B63.dord_inv' hπ ht0]; omega
  obtain ⟨σ, hσ, hσt⟩ := exists_max_of_pos hπ (inv_ne_zero ht0) hinv
  have hf : (X ^ 2 - X + C (u * σ ^ 2) : R[X]).Monic := by monicity!
  have hder : (derivative (X ^ 2 - X + C (u * σ ^ 2) : R[X])).eval 0 = -1 := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C]
    simp
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - X + C (u * σ ^ 2) : R[X]) hf 0
    (by simpa using Ideal.mul_mem_left _ u (Ideal.pow_mem_of_mem _ hσ 2 (by norm_num)))
    (by rw [hder]; exact isUnit_one.neg)
  have ha' : a ^ 2 - a + u * σ ^ 2 = 0 := by simpa using ha
  have h1 := congrArg (algebraMap R F) ha'
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h1
  refine ⟨t * algebraMap R F a, ?_⟩
  rw [hσt] at h1
  field_simp at h1
  field_simp
  linear_combination h1

/-- In $E = F(\delta)$ with $\delta \notin F$, an element $x + y\delta$ with $y \ne 0$ is not in $F$. -/
private lemma not_mem_range (hδ : δ ^ 2 = algebraMap R E Δ) (hnsq : ¬ IsSquare (algebraMap R F Δ))
    {x y : F} (hy : y ≠ 0) (r : F) :
    algebraMap F E x + algebraMap F E y * δ ≠ algebraMap F E r := by
  intro h
  apply hnsq
  refine ⟨(r - x) / y, (algebraMap F E).injective ?_⟩
  have hδF : δ ^ 2 = algebraMap F E (algebraMap R F Δ) := by
    rw [hδ, ← IsScalarTower.algebraMap_apply]
  have hy' : algebraMap F E y ≠ 0 := by simpa using hy
  have hd : δ = algebraMap F E ((r - x) / y) := by
    rw [map_div₀, map_sub]
    field_simp
    linear_combination h
  rw [← hδF, map_mul, ← hd]
  ring

/-- If $\alpha^2 - t\alpha + n = 0$ and $r^2 - tr + n = 0$ then $(\alpha - r)(\alpha - (t - r)) = 0$. -/
private lemma factor_aux {α : E} {t r n : F}
    (heq : α ^ 2 - algebraMap F E t * α + algebraMap F E n = 0) (hr : r ^ 2 - t * r + n = 0) :
    (α - algebraMap F E r) * (α - algebraMap F E (t - r)) = 0 := by
  have := congrArg (algebraMap F E) hr
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at this ⊢
  linear_combination heq - this

/-- **A norm that is a unit forces an integral unit.** Let $E = F(\delta)$, $\delta^2 = \Delta \in R$, with $\Delta$ not
a square in $F$. If $N_{E/F}\alpha$ is a unit of $R$ then $\alpha$ and $\alpha^{-1}$ are integral over $R$. -/
private lemma isIntegral_of_norm_unit (hπ : Irreducible π) (hδ : δ ^ 2 = algebraMap R E Δ)
    (hspan : ∀ z : E, ∃ b₀ b₁ : F, z = algebraMap F E b₀ + algebraMap F E b₁ * δ)
    (hnsq : ¬ IsSquare (algebraMap R F Δ)) {α : E} {u : R} (hu : IsUnit u)
    (hN : Algebra.norm F α = algebraMap R F u) : α ≠ 0 ∧ IsIntegral R α ∧ IsIntegral R α⁻¹ := by
  obtain ⟨x, y, hα⟩ := hspan α
  have hN' : x ^ 2 - algebraMap R F Δ * y ^ 2 = algebraMap R F u := by
    rw [← norm_formula hδ hspan hnsq, ← hα, hN]
  have hδF : δ ^ 2 = algebraMap F E (algebraMap R F Δ) := by
    rw [hδ, ← IsScalarTower.algebraMap_apply]
  -- the quadratic equation satisfied by α
  have hu' : algebraMap R E u = algebraMap F E (algebraMap R F u) :=
    IsScalarTower.algebraMap_apply R F E u
  have hinj : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective R F)
  have heq : α ^ 2 - algebraMap F E (2 * x) * α + algebraMap F E (algebraMap R F u) = 0 := by
    rw [← hN', hα]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (algebraMap F E y) ^ 2 * hδF
  -- 2x ∈ R
  have ht : ∃ t₀ : R, algebraMap R F t₀ = 2 * x := by
    by_cases hy : y = 0
    · -- then α ∈ F and x is integral
      subst hy
      have hx2 : x ^ 2 = algebraMap R F u := by simpa using hN'
      have hxint : IsIntegral R x := by
        refine ⟨X ^ 2 - C u, by monicity!, ?_⟩
        simp [Polynomial.eval₂_sub, hx2]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxint
      exact ⟨2 * r, by rw [map_mul, hr, map_ofNat]⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨r₁, hr₁⟩ := exists_root_of_not_mem hπ (t := 2 * x) hcon u
      have hfac := factor_aux heq hr₁
      rcases mul_eq_zero.1 hfac with h | h
      · exact not_mem_range hδ hnsq hy r₁ (by rw [← hα]; linear_combination h)
      · exact not_mem_range hδ hnsq hy (2 * x - r₁) (by rw [← hα]; linear_combination h)
  obtain ⟨t₀, ht₀⟩ := ht
  have ht₀E : algebraMap R E t₀ = algebraMap F E (2 * x) := by
    rw [IsScalarTower.algebraMap_apply R F E, ht₀]
  rw [← hu', ← ht₀E] at heq
  have hαint : IsIntegral R α := by
    refine ⟨X ^ 2 - C t₀ * X + C u, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, eval₂_X_pow, eval₂_C,
      eval₂_X]
    linear_combination heq
  have hmul : α * (algebraMap R E t₀ - α) = algebraMap R E u := by linear_combination -heq
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hu0 : algebraMap R E u ≠ 0 := fun h => hu.ne_zero (hinj (by rw [h, map_zero]))
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hmul]; ring)
  refine ⟨hα0, hαint, ?_⟩
  have hu1 : algebraMap R E u * algebraMap R E w = 1 := by rw [← map_mul, hw, map_one]
  have hinv : α⁻¹ = (algebraMap R E t₀ - α) * algebraMap R E w := by
    apply inv_eq_of_mul_eq_one_right
    calc α * ((algebraMap R E t₀ - α) * algebraMap R E w)
        = (α * (algebraMap R E t₀ - α)) * algebraMap R E w := by ring
      _ = 1 := by rw [hmul, hu1]
  rw [hinv]
  exact ((isIntegral_algebraMap).sub hαint).mul isIntegral_algebraMap

/-- **63:16 (first part), $N_{E/F}\alpha$ is a unit iff $\alpha$ is** (O'Meara 1963, §63C, p. 169, by Theorem 14:1):
let $R$ be a Henselian discrete valuation ring with fraction field $F$ (a local field) and $E = F(\sqrt\Delta)$ a
quadratic extension of $F$, presented as in the book's proof of 63:16: $\delta \in E$ with $\delta^2 = \Delta \in R$
(`hδ`), every element of $E$ is $b_0 + b_1\delta$ (`hspan`), and $\Delta$ is not a square in $F$ (`hnsq`). For
$\alpha \in E$: $\alpha$ is a unit of the ring of integers $\mathfrak O$ of $E$ (the integral closure of $R$ in $E$)
if and only if $N_{E/F}\alpha$ is a unit of $R$. No unramifiedness is used here (the book quotes Theorem 14:1,
valid for every extension of complete fields). -/
@[kb "omeara1963" "§63C, 63:16, p. 169 (N_{E/F}α is a unit iff α is)"]
theorem isUnit_iff_norm_isUnit (hπ : Irreducible π) (hδ : δ ^ 2 = algebraMap R E Δ)
    (hspan : ∀ z : E, ∃ b₀ b₁ : F, z = algebraMap F E b₀ + algebraMap F E b₁ * δ)
    (hnsq : ¬ IsSquare (algebraMap R F Δ)) (α : E) :
    (∃ w : (integralClosure R E)ˣ, ((w : integralClosure R E) : E) = α) ↔
      ∃ v : Rˣ, algebraMap R F v = Algebra.norm F α := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : IsIntegral R ((w : integralClosure R E) : E) := (w : integralClosure R E).2
    have h2 : IsIntegral R (((w⁻¹ : (integralClosure R E)ˣ) : integralClosure R E) : E) :=
      ((w⁻¹ : (integralClosure R E)ˣ) : integralClosure R E).2
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F h1)
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F h2)
    have hmul : Algebra.norm F ((w : integralClosure R E) : E) *
        Algebra.norm F (((w⁻¹ : (integralClosure R E)ˣ) : integralClosure R E) : E) = 1 := by
      have h12 : ((w : integralClosure R E) : E) *
          (((w⁻¹ : (integralClosure R E)ˣ) : integralClosure R E) : E) = 1 := by
        exact congrArg Subtype.val (Units.mul_inv w)
      rw [← map_mul, h12, map_one]
    rw [← hr, ← hr', ← map_mul, ← map_one (algebraMap R F)] at hmul
    have : r * r' = 1 := (IsFractionRing.injective R F) hmul
    exact ⟨Units.mk r r' this (by rw [mul_comm]; exact this), by simpa using hr⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hα0, h1, h2⟩ := isIntegral_of_norm_unit hπ hδ hspan hnsq v.isUnit hv.symm
    exact ⟨⟨⟨α, h1⟩, ⟨α⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hα0), Subtype.ext (inv_mul_cancel₀ hα0)⟩, rfl⟩

/-- **63:16 (second part), $N_{E/F}\mathfrak U = \mathfrak u$** (O'Meara 1963, §63C, p. 169): for the unramified quadratic
extension $E = F(\sqrt\Delta)$ of the local field $F$, with $\Delta$ a unit of quadratic defect $4\mathfrak o$ (the
fixed unit of 63:4; the book shows an unramified quadratic extension has this form, 63:3) and $\delta^2 = \Delta$,
every unit $v$ of $R$ is the norm of a unit of the ring of integers $\mathfrak O$ of $E$; the other inclusion
$N_{E/F}\mathfrak U \subseteq \mathfrak u$ is `isUnit_iff_norm_isUnit`. -/
@[kb "omeara1963" "§63C, 63:16, p. 169 (N_{E/F}𝔘 = 𝔲)"]
theorem exists_unit_norm_eq [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0) (hπ : Irreducible π)
    (hΔ : IsUnit Δ) (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)})
    (hδ : δ ^ 2 = algebraMap R E Δ)
    (hspan : ∀ z : E, ∃ b₀ b₁ : F, z = algebraMap F E b₀ + algebraMap F E b₁ * δ) (v : Rˣ) :
    ∃ w : (integralClosure R E)ˣ, Algebra.norm F ((w : integralClosure R E) : E) = algebraMap R F v := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero_F h2
  have hnsq : ¬ IsSquare (algebraMap R F Δ) := by
    rw [isSquare_iff_quadDefect_eq_bot h2, hΔd]
    intro h
    have h4 : (4 : F) ≠ 0 := four_F_ne h2
    have : (4 : F) ∈ span R {(4 : F)} := Submodule.mem_span_singleton_self _
    rw [h] at this
    exact h4 (by simpa using this)
  have hΔ0 : algebraMap R F Δ ≠ 0 := alg_ne_zero_of_unit hΔ
  have h1 := hilbertSymbol_unit_delta (F := F) h2 hΔ hΔd v.isUnit
  rw [hilbertSymbol_comm] at h1
  obtain ⟨x₀, x₁, hx⟩ := (HN.hilbertSymbol_eq_one_iff_norm F h2F hΔ0).1 h1
  have hN : Algebra.norm F (algebraMap F E x₀ + algebraMap F E x₁ * δ) = algebraMap R F v := by
    rw [norm_formula hδ hspan hnsq, hx]
  obtain ⟨w, hw⟩ := (isUnit_iff_norm_isUnit hπ hδ hspan hnsq (algebraMap F E x₀ + algebraMap F E x₁ * δ)).2
    ⟨v, hN.symm⟩
  exact ⟨w, by rw [hw]; exact hN⟩

end Unramified

end QuadFormsKB.OMeara
