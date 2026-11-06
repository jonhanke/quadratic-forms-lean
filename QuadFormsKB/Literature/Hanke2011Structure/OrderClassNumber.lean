/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelativeQuadratic
import QuadFormsKB.Literature.Hanke2011Structure.OrderUnitsCount

/-!
# Paper 6, Remark 8.8 corrected: class numbers of the orders $\mathcal O_F + \mathfrak f\mathcal O_K$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Remark 8.8, p. 37. The printed relation
$h(R_K) = h(\mathcal O_K)\prod_{\mathfrak p \mid I(S')/I(S)}(1 - \chi_S(\mathfrak p)/q)$ is not integral in general
(`remark_8_8_printed_not_integral`, `ClassNumber.lean`). The corrected relation (the one of Shimura's formula cited by the
remark, and of Neukirch I (12.12)) is
$$h(R)\,[\mathcal O_K^\times : R^\times] = h(\mathcal O_K)\,N(\mathfrak f)\prod_{\mathfrak p \mid \mathfrak f}\Bigl(1 - \frac{\chi_{K/F}(\mathfrak p)}{N\mathfrak p}\Bigr),$$
for the order $R = \mathcal O_F + \mathfrak f\mathcal O_K$ of conductor $\mathfrak f$ (an $\mathcal O_F$-order, as the remark
needs: $\det_H(R_K, N_{K/F})$ is the Hessian determinant of an $\mathcal O_F$-lattice). The primes
$\mathfrak p \mid I(S')/I(S)$ of the remark are the primes dividing $\mathfrak f$ ($I(S') = \mathfrak f^2 I(S)$), and
$\chi_S = \chi_{K/F}$ is the splitting character of $K/F$ (`Binary.Rel.relChar`; $-S$ is the discriminant of $K/F$, proof of
Thm. 8.6).

Here $E/F$ is any quadratic extension of number fields ($K/F$ CM in the paper; neither the CM hypothesis nor
"$2$ splits completely in $F$" is used).

* `orderOf 𝔣` $= \mathcal O_F + \mathfrak f\mathcal O_E$, a subalgebra of $\mathcal O_E$ containing $\mathfrak f\mathcal O_E$;
* `comap_map_eq`: $\mathfrak f\mathcal O_E \cap \mathcal O_F = \mathfrak f$ (via the relative norm);
* `card_units_orderQuot`: $(R/\mathfrak f\mathcal O_E)^\times \cong (\mathcal O_F/\mathfrak f)^\times$;
* `card_units_ratio` (**proved**): $\#(\mathcal O_E/\mathfrak f\mathcal O_E)^\times =
  \#(\mathcal O_F/\mathfrak f)^\times\cdot N(\mathfrak f)\prod_{\mathfrak p\mid\mathfrak f}(1 - \chi(\mathfrak p)/N\mathfrak p)$;
* `OrderClassNumberFormula R 𝔪` (**named input**, Neukirch I (12.12)): for an $\mathcal O_E$-ideal $\mathfrak m \ne 0$
  contained in an order $R$, $h(R)\,[\mathcal O_E^\times : R^\times]\,\#(R/\mathfrak m)^\times = h(\mathcal O_E)\,
  \#(\mathcal O_E/\mathfrak m)^\times$;
* `remark_8_8_corrected`: the corrected relation, conditional on that input.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid Module
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-- $[\mathcal O_E : \mathcal O_F] = [E : F]$ as a rank. -/
theorem finrank_O (hdeg : finrank F E = 2) : finrank (𝓞 F) (𝓞 E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hdeg]

/-- $N(\mathfrak f\mathcal O_E) = N(\mathfrak f)^2$. -/
theorem absNorm_map (hdeg : finrank F E = 2) (𝔣 : Ideal (𝓞 F)) :
    Ideal.absNorm (𝔣.map (algebraMap (𝓞 F) (𝓞 E))) = Ideal.absNorm 𝔣 ^ 2 := by
  rw [Ideal.absNorm_algebraMap, finrank_O hdeg]

/-- **$\mathfrak f\mathcal O_E \cap \mathcal O_F = \mathfrak f$**: if $x \in \mathcal O_F$ lies in $\mathfrak f\mathcal O_E$ then
$(x)^2 = N_{E/F}(x\mathcal O_E) \subseteq N_{E/F}(\mathfrak f\mathcal O_E) = \mathfrak f^2$, so $\mathfrak f \mid (x)$. -/
theorem comap_map_eq (hdeg : finrank F E = 2) (𝔣 : Ideal (𝓞 F)) :
    (𝔣.map (algebraMap (𝓞 F) (𝓞 E))).comap (algebraMap (𝓞 F) (𝓞 E)) = 𝔣 := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  have h1 : (Ideal.span {x}).map (algebraMap (𝓞 F) (𝓞 E)) ≤ 𝔣.map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hx
  have h2 := Ideal.relNorm_mono (𝓞 F) h1
  rw [Ideal.relNorm_algebraMap, Ideal.relNorm_algebraMap, finrank_O hdeg] at h2
  have h3 : 𝔣 ^ 2 ∣ Ideal.span {x} ^ 2 := Ideal.dvd_iff_le.mpr h2
  have h4 : 𝔣 ∣ Ideal.span {x} := (pow_dvd_pow_iff_dvd two_ne_zero).mp h3
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd h4)

/-! ### The primes of $\mathcal O_E$ dividing $\mathfrak f\mathcal O_E$ -/

theorem map_ne_bot {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) : 𝔣.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot h𝔣

theorem mem_factors_iff {A : Type*} [CommRing A] [IsDedekindDomain A] {I P : Ideal A} (hI : I ≠ ⊥) :
    P ∈ factors I ↔ P.IsPrime ∧ I ≤ P := by
  rw [factors_eq_normalizedFactors, Ideal.mem_normalizedFactors_iff hI]

/-- The primes of $\mathcal O_E$ over the primes dividing $\mathfrak f$ are the primes dividing $\mathfrak f\mathcal O_E$. -/
theorem factors_map_eq_biUnion [DecidableEq (Ideal (𝓞 E))] {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) :
    (factors (𝔣.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset =
      (factors 𝔣).toFinset.biUnion fun 𝔭 => (factors (𝔭.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset := by
  ext P
  simp only [Multiset.mem_toFinset, Finset.mem_biUnion]
  rw [mem_factors_iff (map_ne_bot h𝔣)]
  constructor
  · rintro ⟨hP, hle⟩
    have hP0 : P ≠ ⊥ := fun h => map_ne_bot (E := E) h𝔣 (le_bot_iff.mp (h ▸ hle))
    refine ⟨P.comap (algebraMap (𝓞 F) (𝓞 E)), ?_, ?_⟩
    · rw [mem_factors_iff h𝔣]
      exact ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hle⟩
    · have hne : P.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
      rw [mem_factors_iff (Ideal.map_ne_bot_of_ne_bot hne)]
      exact ⟨hP, Ideal.map_comap_le⟩
  · rintro ⟨𝔭, h𝔭, hP⟩
    rw [mem_factors_iff h𝔣] at h𝔭
    have h𝔭0 : 𝔭 ≠ ⊥ := fun h => h𝔣 (le_bot_iff.mp (h ▸ h𝔭.2))
    rw [mem_factors_iff (Ideal.map_ne_bot_of_ne_bot h𝔭0)] at hP
    exact ⟨hP.1, le_trans (Ideal.map_mono h𝔭.2) hP.2⟩

theorem factors_map_disjoint {𝔭 𝔭' : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (h𝔭' : 𝔭'.IsMaximal) (h0 : 𝔭 ≠ ⊥)
    (h0' : 𝔭' ≠ ⊥) (hne : 𝔭 ≠ 𝔭') :
    Disjoint (factors (𝔭.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset
      (factors (𝔭'.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rw [Multiset.mem_toFinset, mem_factors_iff (Ideal.map_ne_bot_of_ne_bot h0)] at hP
  rw [Multiset.mem_toFinset, mem_factors_iff (Ideal.map_ne_bot_of_ne_bot h0')] at hP'
  have hc : P.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊤ := Ideal.comap_ne_top _ hP.1.ne_top
  have e1 := h𝔭.eq_of_le hc (Ideal.map_le_iff_le_comap.mp hP.2)
  have e2 := h𝔭'.eq_of_le hc (Ideal.map_le_iff_le_comap.mp hP'.2)
  exact hne (e1.trans e2.symm)

/-! ### The splitting character on the prime factors of $\mathfrak f$ -/

/-- A nonzero prime ideal of $\mathcal O_F$ as a point of the height-one spectrum. -/
def toHOS (𝔭 : Ideal (𝓞 F)) (hp : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) : HeightOneSpectrum (𝓞 F) := ⟨𝔭, hp, h0⟩

open Classical in
/-- The splitting character $\chi_{E/F}(\mathfrak p)$ (`Binary.Rel.relChar`) of an ideal $\mathfrak p$ of $\mathcal O_F$
($0$ unless $\mathfrak p$ is a nonzero prime). -/
def chiI (E : Type) [Field E] [NumberField E] [Algebra F E] (𝔭 : Ideal (𝓞 F)) : ℤ :=
  if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ then QuadFormsKB.Binary.Rel.relChar E (toHOS 𝔭 h.1 h.2) else 0

/-- **The local factor:** for a nonzero prime $\mathfrak p$ of $\mathcal O_F$ with $q = N\mathfrak p$,
$\prod_{\mathfrak P \mid \mathfrak p\mathcal O_E}(1 - N\mathfrak P^{-1}) = (1 - q^{-1})(1 - \chi_{E/F}(\mathfrak p)q^{-1})$. -/
theorem prod_factors_map_prime (hdeg : finrank F E = 2) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) :
    ∏ P ∈ (factors (𝔭.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset, (1 - 1 / (Ideal.absNorm P : ℚ)) =
      (1 - 1 / (Ideal.absNorm 𝔭 : ℚ)) * (1 - (chiI E 𝔭 : ℚ) / Ideal.absNorm 𝔭) := by
  classical
  haveI : 𝔭.IsMaximal := hp.isMaximal h0
  have hiff : ∀ P, P ∈ (factors (𝔭.map (algebraMap (𝓞 F) (𝓞 E)))).toFinset ↔ P ∈ 𝔭.primesOver (𝓞 E) := by
    intro P
    rw [Multiset.mem_toFinset, factors_eq_normalizedFactors,
      ← Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 E) h0]
  rw [Finset.prod_subtype _ hiff (fun P => (1 - 1 / (Ideal.absNorm P : ℚ)))]
  have hχ : chiI E 𝔭 = QuadFormsKB.Binary.Rel.relChar E (toHOS 𝔭 hp h0) := by
    unfold chiI; rw [dif_pos ⟨hp, h0⟩]
  rw [hχ]
  have hq : (Ideal.absNorm 𝔭 : ℚ) ≠ 0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr h0
  have hfin : ∀ (inst₁ inst₂ : Fintype {P // P ∈ 𝔭.primesOver (𝓞 E)}),
      @Finset.univ _ inst₁ = @Finset.univ _ inst₂ := fun i₁ i₂ => by congr; exact Subsingleton.elim _ _
  rcases QuadFormsKB.Binary.Rel.prod_fiber (E := E) hdeg (toHOS 𝔭 hp h0) (fun n => (1 - 1 / (n : ℚ))) with
    ⟨hc, hprod⟩ | ⟨hc, hprod⟩ | ⟨hc, hprod⟩ <;>
  · simp only [NFEuler.normP] at hprod
    rw [hc]
    refine (Eq.trans ?_ hprod).trans ?_
    · congr 1
    · rw [show Ideal.absNorm (toHOS 𝔭 hp h0).asIdeal = Ideal.absNorm 𝔭 from rfl]
      push_cast; field_simp; try ring

/-- **The unit-count ratio** (proved): for a quadratic extension $E/F$ and a nonzero ideal $\mathfrak f$ of $\mathcal O_F$,
$$\#(\mathcal O_E/\mathfrak f\mathcal O_E)^\times = \#(\mathcal O_F/\mathfrak f)^\times\cdot N(\mathfrak f)
\prod_{\mathfrak p\mid\mathfrak f}\Bigl(1 - \frac{\chi_{E/F}(\mathfrak p)}{N\mathfrak p}\Bigr).$$ -/
@[kb "hanke2011structure" "Rem. 8.8, p. 37 (the local factors 1 - χ(p)/q)"]
theorem card_units_ratio (hdeg : finrank F E = 2) {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) :
    (Nat.card (𝓞 E ⧸ 𝔣.map (algebraMap (𝓞 F) (𝓞 E)))ˣ : ℚ) =
      Nat.card (𝓞 F ⧸ 𝔣)ˣ * Ideal.absNorm 𝔣 *
        ∏ 𝔭 ∈ (factors 𝔣).toFinset, (1 - (chiI E 𝔭 : ℚ) / Ideal.absNorm 𝔭) := by
  classical
  rw [card_units_quot (map_ne_bot h𝔣), card_units_quot h𝔣, absNorm_map hdeg, factors_map_eq_biUnion h𝔣,
    Finset.prod_biUnion]
  · rw [Finset.prod_congr rfl fun 𝔭 h𝔭 => prod_factors_map_prime (E := E) hdeg
      (mem_factors_isPrime (Multiset.mem_toFinset.mp h𝔭)) (mem_factors_ne_bot (Multiset.mem_toFinset.mp h𝔭)),
      Finset.prod_mul_distrib]
    push_cast; ring
  · intro 𝔭 h𝔭 𝔭' h𝔭' hne
    have hm := Multiset.mem_toFinset.mp h𝔭
    have hm' := Multiset.mem_toFinset.mp h𝔭'
    haveI := mem_factors_isPrime hm
    haveI := mem_factors_isPrime hm'
    exact factors_map_disjoint (Ideal.IsPrime.isMaximal inferInstance (mem_factors_ne_bot hm))
      (Ideal.IsPrime.isMaximal inferInstance (mem_factors_ne_bot hm')) (mem_factors_ne_bot hm)
      (mem_factors_ne_bot hm') hne

/-! ### The order $\mathcal O_F + \mathfrak f\mathcal O_E$ -/

/-- **The order of conductor $\mathfrak f$**: $R = \mathcal O_F + \mathfrak f\mathcal O_E \subseteq \mathcal O_E$. -/
@[kb "hanke2011structure" "Rem. 8.8, p. 37 (the order R_K = O_F + f O_K)"]
def orderOf (𝔣 : Ideal (𝓞 F)) : Subalgebra (𝓞 F) (𝓞 E) where
  carrier := {x | ∃ a : 𝓞 F, x - algebraMap (𝓞 F) (𝓞 E) a ∈ 𝔣.map (algebraMap (𝓞 F) (𝓞 E))}
  mul_mem' {x y} hx hy := by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have e : x * y - algebraMap (𝓞 F) (𝓞 E) (a * b) =
        (x - algebraMap (𝓞 F) (𝓞 E) a) * y + algebraMap (𝓞 F) (𝓞 E) a * (y - algebraMap (𝓞 F) (𝓞 E) b) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
  add_mem' {x y} hx hy := by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have e : x + y - algebraMap (𝓞 F) (𝓞 E) (a + b) =
        (x - algebraMap (𝓞 F) (𝓞 E) a) + (y - algebraMap (𝓞 F) (𝓞 E) b) := by
      rw [map_add]; ring
    rw [e]
    exact Ideal.add_mem _ ha hb
  algebraMap_mem' r := ⟨r, by simp⟩

theorem map_le_orderOf (𝔣 : Ideal (𝓞 F)) {x : 𝓞 E} (hx : x ∈ 𝔣.map (algebraMap (𝓞 F) (𝓞 E))) :
    x ∈ orderOf (E := E) 𝔣 := ⟨0, by simpa using hx⟩

/-- The ideal $\mathfrak m \cap R$ of a subring $R \subseteq \mathcal O_E$. -/
abbrev idealIn (R : Subalgebra (𝓞 F) (𝓞 E)) (𝔪 : Ideal (𝓞 E)) : Ideal R := 𝔪.comap R.val.toRingHom

/-- $\mathcal O_F \to R/\mathfrak f\mathcal O_E$. -/
def toOrderQuot (𝔣 : Ideal (𝓞 F)) :
    𝓞 F →+* orderOf (E := E) 𝔣 ⧸ idealIn (orderOf 𝔣) (𝔣.map (algebraMap (𝓞 F) (𝓞 E))) :=
  (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (orderOf (E := E) 𝔣))

theorem toOrderQuot_surjective (𝔣 : Ideal (𝓞 F)) : Function.Surjective (toOrderQuot (E := E) 𝔣) := by
  intro y
  obtain ⟨⟨x, a, ha⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ (algebraMap (𝓞 F) (orderOf (E := E) 𝔣) a) = _
  rw [Ideal.Quotient.eq]
  show (algebraMap (𝓞 F) (𝓞 E) a - x) ∈ 𝔣.map (algebraMap (𝓞 F) (𝓞 E))
  rw [← neg_sub]
  exact neg_mem ha

theorem ker_toOrderQuot (hdeg : finrank F E = 2) (𝔣 : Ideal (𝓞 F)) :
    RingHom.ker (toOrderQuot (E := E) 𝔣) = 𝔣 := by
  ext a
  rw [RingHom.mem_ker, toOrderQuot, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  show algebraMap (𝓞 F) (𝓞 E) a ∈ 𝔣.map (algebraMap (𝓞 F) (𝓞 E)) ↔ _
  rw [← Ideal.mem_comap, comap_map_eq hdeg]

/-- **$R/\mathfrak f\mathcal O_E \cong \mathcal O_F/\mathfrak f$.** -/
def orderQuotEquiv (hdeg : finrank F E = 2) (𝔣 : Ideal (𝓞 F)) :
    𝓞 F ⧸ 𝔣 ≃+* orderOf (E := E) 𝔣 ⧸ idealIn (orderOf 𝔣) (𝔣.map (algebraMap (𝓞 F) (𝓞 E))) :=
  (Ideal.quotEquivOfEq (ker_toOrderQuot hdeg 𝔣).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toOrderQuot_surjective 𝔣))

theorem card_units_orderQuot (hdeg : finrank F E = 2) (𝔣 : Ideal (𝓞 F)) :
    Nat.card (orderOf (E := E) 𝔣 ⧸ idealIn (orderOf 𝔣) (𝔣.map (algebraMap (𝓞 F) (𝓞 E))))ˣ =
      Nat.card (𝓞 F ⧸ 𝔣)ˣ :=
  (Nat.card_congr (Units.mapEquiv (orderQuotEquiv hdeg 𝔣).toMulEquiv).toEquiv).symm

/-! ### The class number formula for orders (named input) and Remark 8.8 corrected -/

/-- The unit index $[\mathcal O_E^\times : R^\times]$ of a subring $R \subseteq \mathcal O_E$. -/
def unitIndex (R : Subalgebra (𝓞 F) (𝓞 E)) : ℕ := (Units.map R.val.toRingHom.toMonoidHom).range.index

variable (F E) in
/-- **The class number formula for orders** (named input; Neukirch, *Algebraic Number Theory*, Ch. I, (12.12), p. 79,
from the exact sequence (12.9)–(12.11)
$1 \to R^\times \to \mathcal O_E^\times \to (\mathcal O_E/\mathfrak m)^\times/(R/\mathfrak m)^\times \to \mathrm{Pic}(R)
\to \mathrm{Pic}(\mathcal O_E) \to 1$): for every subring $R$ of $\mathcal O_E$ containing $\mathcal O_F$ and every nonzero
ideal $\mathfrak m$ of $\mathcal O_E$ contained in $R$,
$$h(R)\,[\mathcal O_E^\times : R^\times]\,\#(R/\mathfrak m)^\times = h(\mathcal O_E)\,\#(\mathcal O_E/\mathfrak m)^\times,$$
$h(R) = \#\mathrm{Pic}(R)$ (Mathlib's `ClassGroup R`: invertible fractional ideals modulo principal ones). Neukirch states it
for $\mathfrak m = \mathfrak f$ the conductor of $R$; for an $\mathcal O_E$-ideal $\mathfrak m \subseteq R$ (so
$\mathfrak m \subseteq \mathfrak f$) the ratio $\#(\mathcal O_E/\mathfrak m)^\times/\#(R/\mathfrak m)^\times$ is the same, both
kernels of reduction modulo $\mathfrak f$ being $(1 + \mathfrak f)/(1 + \mathfrak m)$. A statement about orders and their
Picard groups, independent of Remark 8.8's conclusion (which also needs `card_units_ratio`). -/
@[kb "neukirch1999" "Ch. I, (12.12), p. 79 (class number of an order)"]
structure OrderClassNumberFormula : Prop where
  formula : ∀ (R : Subalgebra (𝓞 F) (𝓞 E)) (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → (∀ x ∈ 𝔪, x ∈ R) →
    Nat.card (ClassGroup R) * unitIndex R * Nat.card (R ⧸ idealIn R 𝔪)ˣ =
      classNumber E * Nat.card (𝓞 E ⧸ 𝔪)ˣ

/-- **Remark 8.8, corrected** (Hanke 2011, p. 37; *erratum*): for a
quadratic extension $E/F$ (CM in the paper), a nonzero ideal $\mathfrak f$ of $\mathcal O_F$ and the order
$R = \mathcal O_F + \mathfrak f\mathcal O_E$,
$$h(R)\,[\mathcal O_E^\times : R^\times] = h(\mathcal O_E)\,N(\mathfrak f)\prod_{\mathfrak p\mid\mathfrak f}
\Bigl(1 - \frac{\chi_{E/F}(\mathfrak p)}{N\mathfrak p}\Bigr),$$
conditional on the class number formula for orders (`OrderClassNumberFormula`, Neukirch I (12.12)). The printed formula
lacks the factor $N(\mathfrak f)/[\mathcal O_E^\times : R^\times]$ (`remark_8_8_printed_not_integral`). The primes
$\mathfrak p \mid I(S')/I(S)$ of the remark are those dividing $\mathfrak f$. -/
@[kb "hanke2011structure" "Rem. 8.8, p. 37 (corrected)"]
theorem remark_8_8_corrected (H : OrderClassNumberFormula F E) (hdeg : finrank F E = 2) {𝔣 : Ideal (𝓞 F)}
    (h𝔣 : 𝔣 ≠ ⊥) :
    (Nat.card (ClassGroup (orderOf (E := E) 𝔣)) : ℚ) * unitIndex (orderOf (E := E) 𝔣) =
      classNumber E * Ideal.absNorm 𝔣 *
        ∏ 𝔭 ∈ (factors 𝔣).toFinset, (1 - (chiI E 𝔭 : ℚ) / Ideal.absNorm 𝔭) := by
  have h := H.formula (orderOf 𝔣) (𝔣.map (algebraMap (𝓞 F) (𝓞 E))) (map_ne_bot h𝔣)
    (fun x hx => map_le_orderOf 𝔣 hx)
  rw [card_units_orderQuot hdeg] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hq
  rw [card_units_ratio hdeg h𝔣] at hq
  have hU : (Nat.card (𝓞 F ⧸ 𝔣)ˣ : ℚ) ≠ 0 := by
    have := finite_quot h𝔣
    exact_mod_cast Nat.card_pos.ne'
  apply mul_right_cancel₀ hU
  linear_combination hq

end

end QuadFormsKB.Hanke2011Structure.OrderCN

#print axioms QuadFormsKB.Hanke2011Structure.OrderCN.card_units_ratio
#print axioms QuadFormsKB.Hanke2011Structure.OrderCN.remark_8_8_corrected
