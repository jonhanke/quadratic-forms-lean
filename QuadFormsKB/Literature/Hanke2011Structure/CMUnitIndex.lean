/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.HasseNorm.Herbrand

/-!
# Paper 6, Lemma 8.4: the unit index $[\mathcal O_F^\times : N_{K/F}\mathcal O_K^\times] = 2^{[F:\mathbb Q]}/Q_{K/F}$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 8.4 and its proof, p. 35.

Lemma 8.4 states $|G(\mathcal O_K)| = \frac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\frac{2^{[F:\mathbb Q]}}{Q_{K/F}}$ for a CM extension $K/F$,
$Q_{K/F} = [\mathcal O_K^\times : \mathcal O_F^\times\mu_K]$. Its proof has two steps: Kneser's exact sequence (with the surjectivity of
the norm on class groups) gives $|G(\mathcal O_K)| = \frac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot|\mathcal O_F^\times/N_{K/F}(\mathcal O_K^\times)|$, and
then
$$|\mathcal O_F^\times/N_{K/F}(\mathcal O_K^\times)| = \frac{2^{[F:\mathbb Q]}}{Q_{K/F}},$$
because the norm induces $\mathcal O_K^\times/\mathcal O_F^\times\mu_K \cong N(\mathcal O_K^\times)/N(\mathcal O_F^\times)$ and
$N(\mathcal O_F^\times) = (\mathcal O_F^\times)^2$ has index $2^{([F:\mathbb Q]-1)+1}$ (Dirichlet's unit theorem, $\mu_F = \{\pm1\}$).

This file proves the **second step** (`lemma_8_4_unit_index`, `lemma_8_4_unit_index_div`), for a CM field $K$ with maximal
totally real subfield $F = K^+$ (Mathlib's `IsCMField`, `maximalRealSubfield`; every CM extension $K/F$ has $F = K^+$), all
inside $\mathcal O_K^\times$: $\mathcal O_F^\times$ is `IsCMField.realUnits K`, the norm is $u \mapsto u\bar u$ (`unitsNorm`), and
$Q_{K/F}$ is `IsCMField.indexRealUnits K` $= [\mathcal O_K^\times : \mathcal O_F^\times\mu_K]$:
$$[\mathcal O_F^\times : N_{K/F}(\mathcal O_K^\times)]\cdot Q_{K/F} = 2^{[F:\mathbb Q]}.$$
Ingredients: `index_sq_units` ($[\mathcal O_F^\times : (\mathcal O_F^\times)^2] = 2^{[F:\mathbb Q]}$ for $F$ totally real, from the library's
$[A : 2A] = 2^{\operatorname{rk}A}|A[2]|$, `HN.index_range_two`), `ker_unitsNorm` (the norm-one units of a CM field are the roots of
unity), `map_unitsNorm_sup` ($N(\mathcal O_F^\times\mu_K) = (\mathcal O_F^\times)^2$).

The first step (Kneser's exact sequence for the group $G(\mathcal O_K)$ of Lemma 8.3, and the surjectivity of the norm map
$\mathrm{Pic}(\mathcal O_K) \to \mathrm{Pic}(\mathcal O_F)$, Washington Thm. 10.1) is not formalized here: $G(\mathcal O_K)$ (Kneser's group of
binary lattices with an $\mathcal O_K$-module structure) is not defined in the library.

Indices are 0-based.
-/

namespace QuadFormsKB.Hanke2011Structure.CMUnits

open NumberField NumberField.Units NumberField.IsCMField Module

noncomputable section

/-! ### The index of the squares in the units of a totally real field -/

section TotallyReal

variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

/-- The squares of the units, as the range of the additive doubling map on `Additive (𝓞 F)ˣ`. -/
theorem toAddSubgroup_range_pow :
    Subgroup.toAddSubgroup (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range =
      (nsmulAddMonoidHom (α := Additive (𝓞 F)ˣ) 2).range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [nsmulAddMonoidHom_apply, ← ofMul_toMul x, ← hy]
    rfl
  · rintro ⟨y, hy⟩
    change Additive.toMul x ∈ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range
    refine ⟨Additive.toMul y, ?_⟩
    rw [← hy, nsmulAddMonoidHom_apply]
    rfl

omit [IsTotallyReal F] in
/-- A unit with $u^2 = 1$ is $\pm1$. -/
theorem units_sq_eq_one_iff (u : (𝓞 F)ˣ) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    have h' : (u : 𝓞 F) * u = 1 := by rw [← Units.val_mul, ← sq, h, Units.val_one]
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))
  · rintro (rfl | rfl) <;> simp

omit [IsTotallyReal F] in
/-- The $2$-torsion of `Additive (𝓞 F)ˣ` has two elements ($\pm1$). -/
theorem card_ker_two : Nat.card (nsmulAddMonoidHom (α := Additive (𝓞 F)ˣ) 2).ker = 2 := by
  have hmem : ∀ u : (𝓞 F)ˣ, Additive.ofMul u ∈ (nsmulAddMonoidHom (α := Additive (𝓞 F)ˣ) 2).ker ↔
      u ^ 2 = 1 := by
    intro u
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩
  have h1 : (1 : (𝓞 F)ˣ) ≠ -1 := by
    intro h
    have := congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h
    simp only [Units.val_one, Units.val_neg, map_one, map_neg] at this
    norm_num at this
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨Additive.ofMul 1, (hmem 1).mpr (one_pow 2)⟩, ⟨Additive.ofMul (-1), (hmem (-1)).mpr (by simp)⟩,
    fun h => h1 (congrArg (fun x => Additive.toMul x.1) h), ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  have hx' : Additive.toMul x ^ 2 = 1 := (hmem (Additive.toMul x)).mp hx
  rcases (units_sq_eq_one_iff F _).mp hx' with h | h
  · left; apply Subtype.ext; show x = Additive.ofMul 1; rw [← h]; rfl
  · right; apply Subtype.ext; show x = Additive.ofMul (-1); rw [← h]; rfl

/-- **$[\mathcal O_F^\times : (\mathcal O_F^\times)^2] = 2^{[F:\mathbb Q]}$** for a totally real number field $F$ (Dirichlet's unit theorem:
$\mathcal O_F^\times \cong \{\pm1\}\times\mathbb Z^{[F:\mathbb Q]-1}$). -/
theorem index_sq_units : (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range.index = 2 ^ finrank ℚ F := by
  rw [← Subgroup.index_toAddSubgroup, toAddSubgroup_range_pow, HN.index_range_two, Units.finrank_eq]
  rw [card_ker_two, Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank]
  have hpos : 0 < finrank ℚ F := Module.finrank_pos
  rw [← pow_succ, Nat.sub_add_cancel hpos]

end TotallyReal

/-! ### The norm of units of a CM field -/

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

theorem unitsComplexConj_unitsComplexConj (u : (𝓞 K)ˣ) : unitsComplexConj K (unitsComplexConj K u) = u := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp [complexConj_apply_apply]

/-- **The relative norm of units** $N_{K/K^+}(u) = u\bar u$, as an endomorphism of $\mathcal O_K^\times$ (its values lie in
$\mathcal O_{K^+}^\times$, `unitsNorm_mem_realUnits`). -/
def unitsNorm : (𝓞 K)ˣ →* (𝓞 K)ˣ where
  toFun u := u * unitsComplexConj K u
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _

theorem unitsNorm_apply (u : (𝓞 K)ˣ) : unitsNorm K u = u * unitsComplexConj K u := rfl

theorem unitsNorm_mem_realUnits (u : (𝓞 K)ˣ) : unitsNorm K u ∈ realUnits K := by
  rw [← unitsComplexConj_eq_self_iff, unitsNorm_apply, map_mul, unitsComplexConj_unitsComplexConj, mul_comm]

theorem unitsNorm_of_mem_realUnits {r : (𝓞 K)ˣ} (hr : r ∈ realUnits K) : unitsNorm K r = r ^ 2 := by
  rw [unitsNorm_apply, (unitsComplexConj_eq_self_iff K r).mpr hr, sq]

/-- **The norm-one units of a CM field are the roots of unity** (Lemma 8.4's proof: $\ker N = \mu_K$). -/
theorem ker_unitsNorm : (unitsNorm K).ker = torsion K := by
  ext u
  rw [MonoidHom.mem_ker, unitsNorm_apply]
  constructor
  · intro h
    have hc : unitsComplexConj K u = u⁻¹ := eq_inv_of_mul_eq_one_right h
    have ht := (unitsMulComplexConjInv K u).2
    rw [unitsMulComplexConjInv_apply, hc, inv_inv, ← sq] at ht
    rw [torsion, CommGroup.mem_torsion] at ht ⊢
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp ht
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * m, by omega, by rw [pow_mul, hpow]⟩
  · intro h
    have := unitsComplexConj_torsion K ⟨u, h⟩
    simp only at this
    rw [this]
    exact mul_inv_cancel _

/-- **$N_{K/K^+}(\mathcal O_{K^+}^\times\mu_K) = (\mathcal O_{K^+}^\times)^2$.** -/
theorem map_unitsNorm_sup :
    (realUnits K ⊔ torsion K).map (unitsNorm K) = (realUnits K).map (powMonoidHom 2) := by
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (ker_unitsNorm K).symm), sup_bot_eq]
  ext x
  simp only [Subgroup.mem_map, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, (unitsNorm_of_mem_realUnits K hr).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, unitsNorm_of_mem_realUnits K hr⟩

theorem realUnits_index_ne_zero : (realUnits K).index ≠ 0 := by
  rw [← Subgroup.relIndex_mul_index (le_sup_left : realUnits K ≤ realUnits K ⊔ torsion K),
    Subgroup.relIndex_sup_left]
  refine mul_ne_zero ?_ ?_
  · rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  · rcases indexRealUnits_eq_one_or_two K with h | h <;> rw [indexRealUnits] at h <;> rw [h] <;> norm_num

/-- The units of $K^+$ inside $\mathcal O_K^\times$, as the image of the injective map $\mathcal O_{K^+}^\times \to \mathcal O_K^\times$. -/
theorem injective_unitsMap :
    Function.Injective (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at h'
  exact FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield K)) (𝓞 K) h'

/-- **$[\mathcal O_{K^+}^\times : (\mathcal O_{K^+}^\times)^2] = 2^{[K^+:\mathbb Q]}$**, inside $\mathcal O_K^\times$. -/
theorem relIndex_sq_realUnits :
    ((realUnits K).map (powMonoidHom 2)).relIndex (realUnits K) = 2 ^ finrank ℚ (maximalRealSubfield K) := by
  set f := Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  have hR : realUnits K = (⊤ : Subgroup (𝓞 (maximalRealSubfield K))ˣ).map f := by
    rw [← MonoidHom.range_eq_map]; rfl
  have hSq : (realUnits K).map (powMonoidHom 2) =
      (powMonoidHom 2 : (𝓞 (maximalRealSubfield K))ˣ →* _).range.map f := by
    rw [hR, Subgroup.map_map, MonoidHom.range_eq_map, Subgroup.map_map]
    congr 1
  rw [hSq, hR, Subgroup.relIndex_map_map_of_injective _ _ (injective_unitsMap K), Subgroup.relIndex_top_right]
  exact index_sq_units (maximalRealSubfield K)

/-- **Lemma 8.4, the unit index** (Hanke 2011, proof of Lemma 8.4, p. 35): for a CM field $K$ with maximal totally real
subfield $F = K^+$,
$$[\mathcal O_F^\times : N_{K/F}(\mathcal O_K^\times)]\cdot Q_{K/F} = 2^{[F:\mathbb Q]},\qquad Q_{K/F} = [\mathcal O_K^\times : \mathcal O_F^\times\mu_K],$$
with $\mathcal O_F^\times$ = `realUnits K` $\subseteq \mathcal O_K^\times$, $N(u) = u\bar u$ (`unitsNorm`) and $Q_{K/F}$ = `indexRealUnits K`. -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (|O_F^×/N(O_K^×)| = 2^[F:Q]/Q_{K/F})"]
theorem lemma_8_4_unit_index :
    (unitsNorm K).range.relIndex (realUnits K) * indexRealUnits K = 2 ^ finrank ℚ (maximalRealSubfield K) := by
  set R := realUnits K
  set T := torsion K
  set N := (unitsNorm K).range
  set Sq := R.map (powMonoidHom 2)
  have hSqN : Sq ≤ N := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, unitsNorm_of_mem_realUnits K hr⟩
  have hNR : N ≤ R := by
    rintro _ ⟨u, rfl⟩
    exact unitsNorm_mem_realUnits K u
  -- `index_map`: `[U : N(R ⊔ T)] = [U : R ⊔ T ⊔ ker N] · [U : N(U)]`
  have hidx : Sq.index = indexRealUnits K * N.index := by
    have h := Subgroup.index_map (R ⊔ T) (unitsNorm K)
    rw [map_unitsNorm_sup, ker_unitsNorm, sup_assoc, sup_idem] at h
    exact h
  have h1 := Subgroup.relIndex_mul_index (hSqN.trans hNR)
  have h2 := Subgroup.relIndex_mul_index hNR
  have hR0 := realUnits_index_ne_zero K
  have key : Sq.relIndex R = indexRealUnits K * N.relIndex R := by
    have : Sq.relIndex R * R.index = indexRealUnits K * N.relIndex R * R.index := by
      rw [h1, hidx, ← h2, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR0) this
  rw [mul_comm, ← key]
  exact relIndex_sq_realUnits K

/-- **Lemma 8.4, the unit index, as printed** (p. 35): $|\mathcal O_F^\times/N_{K/F}(\mathcal O_K^\times)| = 2^{[F:\mathbb Q]}/Q_{K/F}$. -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (unit index, quotient form)"]
theorem lemma_8_4_unit_index_div :
    ((unitsNorm K).range.relIndex (realUnits K) : ℚ) =
      2 ^ finrank ℚ (maximalRealSubfield K) / indexRealUnits K := by
  have hQ : (indexRealUnits K : ℚ) ≠ 0 := by
    rcases indexRealUnits_eq_one_or_two K with h | h <;> rw [h] <;> norm_num
  rw [eq_div_iff hQ]
  exact_mod_cast lemma_8_4_unit_index K

end

end QuadFormsKB.Hanke2011Structure.CMUnits

#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_unit_index
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_unit_index_div
