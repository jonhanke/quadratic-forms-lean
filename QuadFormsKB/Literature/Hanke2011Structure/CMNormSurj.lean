/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.CMKneserGroup

/-!
# Paper 6, Lemma 8.4: the norm on class groups of a CM extension, without class field theory where possible

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 8.4, proof, p. 35, which quotes Washington, *Introduction to cyclotomic
fields*, Thm. 10.1, p. 184, for the surjectivity of the norm
$\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$, $[I] \mapsto [N_{K/F}I]$ (`CMUnits.nuHom`), for a CM field $K$
with maximal totally real subfield $F = K^+$. In the library this is the named input `CMUnits.CMNormSurjective`.

This file proves, with no class field theory:

* `relNorm_map_OF`: $N_{K/F}(J\mathcal O_K) = J^2$ for every ideal $J$ of $\mathcal O_F$ ($[K:F] = 2$);
* `sq_mem_range_nuHom`: every square $c^2$ of $\mathrm{Cl}(\mathcal O_F)$ is a norm; equivalently the cokernel
  $\mathrm{Cl}(\mathcal O_F)/\nu(\mathrm{Cl}(\mathcal O_K))$ is an elementary abelian $2$-group;
* `mem_range_nuHom_of_odd_order`: every class of odd order is a norm;
* `cmNormSurjective_of_odd`: **if $h(\mathcal O_F)$ is odd, `CMNormSurjective K` holds** (unconditionally), and hence
  Lemma 8.4 holds unconditionally in that case (`lemma_8_4_of_odd`, `lemma_8_4_div_of_odd`);
* `cmNormSurjective_iff_two`: the input is equivalent to its $2$-primary part: `CMNormSurjective K` holds iff every
  class of $2$-power order is a norm (the smaller named input `TwoPrimaryNorms`, Washington Thm. 10.1 restricted to the
  $2$-primary part); `lemma_8_4_of_twoPrimary`, `lemma_8_4_div_of_twoPrimary` are Lemma 8.4 conditional only on it.

What remains is class field theory proper: a class $c$ of $2$-power order outside $\nu(\mathrm{Cl}(\mathcal O_K))$ would
give, through the Hilbert class field $H_F$, an unramified quadratic subextension of $H_F/F$ equal to $K$, impossible
since $K/F$ is ramified at the real places. Mathlib has no Hilbert class field or Artin map, so this stays an input.
-/

open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.CMUnits

set_option linter.unusedSectionVars false

noncomputable section

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- $[\mathcal O_K : \mathcal O_F] = 2$ as a rank. -/
theorem finrank_OF_OK : finrank (OF K) (𝓞 K) = 2 := by
  rw [← IsFractionRing.finrank_eq (OF K) (maximalRealSubfield K) (𝓞 K) K]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

/-- $N_{K/F}(J\mathcal O_K) = J^2$ for every ideal $J$ of $\mathcal O_F$. -/
theorem relNorm_map_OF (J : Ideal (OF K)) :
    Ideal.relNorm (OF K) (J.map (algebraMap (OF K) (𝓞 K))) = J ^ 2 := by
  rw [Ideal.relNorm_algebraMap, finrank_OF_OK]

/-- **Every square class is a norm**: for $c \in \mathrm{Cl}(\mathcal O_F)$, $c^2 = \nu([J\mathcal O_K])$ where $c = [J]$. -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (Cl(O_F)² ⊆ N(Cl(O_K)), no class field theory)"]
theorem sq_mem_range_nuHom (c : ClassGroup (OF K)) : c ^ 2 ∈ (nuHom K).range := by
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  have hJ : (J : Ideal (OF K)).map (algebraMap (OF K) (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have h' := congrArg (Ideal.relNorm (OF K)) h
    rw [relNorm_map_OF, map_zero] at h'
    exact nonZeroDivisors.coe_ne_zero J (pow_eq_zero_iff two_ne_zero |>.mp h')
  refine ⟨ClassGroup.mk0 ⟨_, hJ⟩, ?_⟩
  rw [nuHom_mk0, ← map_pow]
  show ClassGroup.mk0 (nrmIdl K ⟨_, hJ⟩) = _
  congr 1
  exact Subtype.ext (by simp [nrmIdl, relNorm_map_OF])

/-- **Every class of odd order is a norm.** -/
theorem mem_range_nuHom_of_odd_order (c : ClassGroup (OF K)) (h : Odd (orderOf c)) : c ∈ (nuHom K).range := by
  obtain ⟨k, hk⟩ := h
  have : c = (c ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, ← hk, pow_orderOf_eq_one, one_mul]
  rw [this]
  exact sq_mem_range_nuHom K _

/-- **If $h(\mathcal O_F)$ is odd, the norm $\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$ is surjective**, with no
class field theory: every class has odd order and is therefore a norm (`mem_range_nuHom_of_odd_order`). -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (surjectivity of the norm when h(O_F) is odd)"]
theorem cmNormSurjective_of_odd (h : Odd (classNumber (maximalRealSubfield K))) : CMNormSurjective K := by
  refine ⟨fun c => ?_⟩
  obtain ⟨d, hd⟩ := mem_range_nuHom_of_odd_order K c (Odd.of_dvd_nat h (by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard c))
  exact ⟨d, hd⟩

/-- **Lemma 8.4, unconditional when $h(\mathcal O_F)$ is odd** (Hanke 2011, p. 35), for $G = $ `KneserGroup K`:
$|G|\cdot h(\mathcal O_F)\cdot Q_{K/F} = h(\mathcal O_K)\cdot 2^{[F:\mathbb Q]}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35 (h(O_F) odd)"]
theorem lemma_8_4_of_odd (h : Odd (classNumber (maximalRealSubfield K))) :
    Nat.card (KneserGroup K) * classNumber (maximalRealSubfield K) * indexRealUnits K =
      classNumber K * 2 ^ finrank ℚ (maximalRealSubfield K) :=
  lemma_8_4_kneser K (cmNormSurjective_of_odd K h)

/-- **Lemma 8.4 in the paper's form, unconditional when $h(\mathcal O_F)$ is odd**:
$|G| = \dfrac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\dfrac{2^{[F:\mathbb Q]}}{Q_{K/F}}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35 (h(O_F) odd)"]
theorem lemma_8_4_div_of_odd (h : Odd (classNumber (maximalRealSubfield K))) :
    (Nat.card (KneserGroup K) : ℚ) = (classNumber K : ℚ) / classNumber (maximalRealSubfield K) *
      (2 ^ finrank ℚ (maximalRealSubfield K) / indexRealUnits K) :=
  lemma_8_4_kneser_div K (cmNormSurjective_of_odd K h)

/-- **The $2$-primary part of the class-field-theory input** (named input, the smallest form of Washington Thm. 10.1
needed for Lemma 8.4): every class of $\mathrm{Cl}(\mathcal O_F)$ whose order is a power of $2$ is a norm
$\nu(d)$, $d \in \mathrm{Cl}(\mathcal O_K)$ (`nuHom`). Washington, *Introduction to cyclotomic fields*, Thm. 10.1,
p. 184 (with $K \cap H_F = F$ for a CM extension). It is a statement about the $2$-primary part of class groups only
and is not equivalent to the conclusion of Lemma 8.4; with `cmNormSurjective_iff_two` it implies the earlier input
`CMNormSurjective K` (and conversely). -/
@[kb "washington1997" "Thm. 10.1, p. 184 (2-primary part: norm on class groups of a CM extension)"]
structure TwoPrimaryNorms : Prop where
  mem_range : ∀ c : ClassGroup (OF K), (∃ k : ℕ, orderOf c = 2 ^ k) → c ∈ (nuHom K).range

/-- **The input `CMNormSurjective K` is equivalent to its $2$-primary part** `TwoPrimaryNorms K`: every class is the
product of a class of $2$-power order and a class of odd order, and classes of odd order are norms. -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (reduction of Washington Thm. 10.1 to the 2-part)"]
theorem cmNormSurjective_iff_two : CMNormSurjective K ↔ TwoPrimaryNorms K := by
  constructor
  · intro H
    refine ⟨fun c _ => ?_⟩
    obtain ⟨d, hd⟩ := H.surjective c
    exact ⟨d, hd⟩
  · intro H
    refine ⟨fun c => ?_⟩
    -- write `orderOf c = 2 ^ a * m` with `m` odd
    have hpos : 0 < orderOf c := orderOf_pos c
    obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
    -- `c ^ m` has order `2 ^ a`, `c ^ (2 ^ a)` has order `m`
    have h1 : orderOf (c ^ m) = 2 ^ a := by
      rw [orderOf_pow' c (by rintro rfl; simp at hm), hcm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hm.pos]
    have h2 : orderOf (c ^ (2 ^ a)) = m := by
      rw [orderOf_pow' c (by positivity), hcm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hm)
    -- Bézout: `c` lies in the subgroup generated by `c ^ m` and `c ^ (2 ^ a)`
    have hA : c ^ m ∈ (nuHom K).range := H.mem_range _ ⟨a, h1⟩
    have hB : c ^ (2 ^ a) ∈ (nuHom K).range := mem_range_nuHom_of_odd_order K _ (by rw [h2]; exact hm)
    have hgcd : Nat.gcd m (2 ^ a) = 1 := Nat.Coprime.symm hcop
    have key : c ∈ Subgroup.closure {c ^ m, c ^ (2 ^ a)} := by
      have e := Nat.gcd_eq_gcd_ab m (2 ^ a)
      rw [hgcd] at e
      have : c = (c ^ m) ^ (Nat.gcdA m (2 ^ a)) * (c ^ (2 ^ a)) ^ (Nat.gcdB m (2 ^ a)) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
        nth_rewrite 1 [← zpow_one c]
        congr 1
      have hm1 : c ^ m ∈ Subgroup.closure ({c ^ m, c ^ (2 ^ a)} : Set (ClassGroup (OF K))) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hm2 : c ^ (2 ^ a) ∈ Subgroup.closure ({c ^ m, c ^ (2 ^ a)} : Set (ClassGroup (OF K))) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      have hmem := Subgroup.mul_mem _ (Subgroup.zpow_mem _ hm1 (Nat.gcdA m (2 ^ a)))
        (Subgroup.zpow_mem _ hm2 (Nat.gcdB m (2 ^ a)))
      rwa [← this] at hmem
    have hle : Subgroup.closure {c ^ m, c ^ (2 ^ a)} ≤ (nuHom K).range := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hA
      · exact hB
    obtain ⟨d, hd⟩ := hle key
    exact ⟨d, hd⟩

/-- **Lemma 8.4 conditional only on the $2$-primary input** `TwoPrimaryNorms K` (Hanke 2011, p. 35), for
$G = $ `KneserGroup K`: $|G|\cdot h(\mathcal O_F)\cdot Q_{K/F} = h(\mathcal O_K)\cdot 2^{[F:\mathbb Q]}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4_of_twoPrimary (H : TwoPrimaryNorms K) :
    Nat.card (KneserGroup K) * classNumber (maximalRealSubfield K) * indexRealUnits K =
      classNumber K * 2 ^ finrank ℚ (maximalRealSubfield K) :=
  lemma_8_4_kneser K ((cmNormSurjective_iff_two K).mpr H)

/-- **Lemma 8.4 in the paper's form, conditional only on** `TwoPrimaryNorms K`:
$|G| = \dfrac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\dfrac{2^{[F:\mathbb Q]}}{Q_{K/F}}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4_div_of_twoPrimary (H : TwoPrimaryNorms K) :
    (Nat.card (KneserGroup K) : ℚ) = (classNumber K : ℚ) / classNumber (maximalRealSubfield K) *
      (2 ^ finrank ℚ (maximalRealSubfield K) / indexRealUnits K) :=
  lemma_8_4_kneser_div K ((cmNormSurjective_iff_two K).mpr H)

/-- `TwoPrimaryNorms K` holds unconditionally when $h(\mathcal O_F)$ is odd (the only class of $2$-power order is $1$). -/
theorem twoPrimaryNorms_of_odd (h : Odd (classNumber (maximalRealSubfield K))) : TwoPrimaryNorms K :=
  (cmNormSurjective_iff_two K).mp (cmNormSurjective_of_odd K h)

end

end QuadFormsKB.Hanke2011Structure.CMUnits

#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.sq_mem_range_nuHom
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.cmNormSurjective_of_odd
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_of_odd
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_div_of_odd
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.cmNormSurjective_iff_two
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_of_twoPrimary
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_div_of_twoPrimary
