/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Beta
import QuadFormsKB.Tamagawa.Dyadic7Units
import QuadFormsKB.Tamagawa.Dyadic7Hasse
import QuadFormsKB.Tamagawa.Dyadic7Classify
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal

/-!
# Paper 7 at $p = 2$: Theorem 4.12 / Table 5.3 from Conway–Sloane's 2-adic symbols

**Main result.** `dyadicTernaryLocalMassTable_of`: the named statement `Dyadic7.DyadicTernaryLocalMassTable` (Hanke 2011,
Thm. 4.12 and Table 5.3: the normalized local mass sums $\widetilde M^{\pm}(S)$ of the primitive ternary
$\mathbb Z_2$-valued genera of Hessian determinant class $S$, for every valuation $h \ge 1$) holds, **conditional on**

* `ConwaySloane.Mass.PMassFormulaTwo` (Conway–Sloane 1988, formula (3) at $p = 2$: the 2-mass of a form from its
  2-adic symbol; now **proved**, `Two.pMassFormulaTwo_holds`, so `dyadicTernaryLocalMassTable_of_count` below has it
  discharged), and
* `Dyadic7.TernaryDyadicMassCount` (`Dyadic7Blocks.lean`): the purely combinatorial statement that the class-weighted
  sums of the 2-masses (and of Hasse invariant times 2-mass) over the admissible ternary block decompositions are the
  entries of Table 5.3. It involves no forms, genera or densities; it is checked numerically for $h \le 12$.

**Proof.** For $S = [2^h u]$ (`exists_zSqCl_eq`):
1. the genera in $\mathrm{Gen}^*_2(S,\varepsilon;3)$ are exactly the genera of the admissible block lists with Hasse
   invariant $\varepsilon$ (`genStar_eq_image`: every nondegenerate genus has an even block decomposition,
   `exists_genusOf`; nondegeneracy, primitivity, determinant and Hasse invariant are read off the blocks:
   `nondeg_genusOf`, `prim_genusOf_iff`, `det_genusOf`, `zSqCl_eq_iff`, `hasse_genusOf`);
2. two lists give the same genus iff their symbols are related by the Conway–Sloane moves (`genusOf_eq_iff`, from
   Theorem 10), so the sum over genera is the class-weighted sum over lists (`sum_image_eq_sum_div_card`);
3. $G_0$ is the genus of `baseList u` (Theorem 2.6, `locGenus_eq_of_det_ordZ_one`) and
   $\beta(G_0)/\beta(G_D) = 4^{1-h}m_2(D)/m_2(D_0) = $ `massWt h u D` (`beta_genusOf_three`, from Hanke's Lemma 3.1 and
   `PMassFormulaTwo`);
4. splitting by the Hasse invariant gives $\widetilde M^+ \pm \widetilde M^-$, and `TernaryDyadicMassCount` finishes.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal

noncomputable section

/-- A sum over the image of a finite set, as a sum over the set with each element weighted by the inverse size of its
fiber. -/
theorem sum_image_eq_sum_div_card {α β : Type*} [DecidableEq β] (s : Finset α) (φ : α → β) (g : β → ℝ) :
    ∑ y ∈ s.image φ, g y = ∑ x ∈ s, g (φ x) / ((s.filter fun x' => φ x' = φ x).card : ℝ) := by
  classical
  refine Finset.sum_image' _ fun c hc => ?_
  have hpos : 0 < (s.filter fun x' => φ x' = φ c).card :=
    Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩
  rw [Finset.sum_congr rfl fun x hx => by
    rw [(Finset.mem_filter.mp hx).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem tildeTernary_zSqCl (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (h : ℕ) {u : ℤ} (hu : Odd u) :
    tildeTernary v (zSqCl v (2 ^ h * u)) = zSqCl v (2 * u) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  have hpow : ∀ k : ℕ, zSqCl v (2 ^ k) = zSqCl v 2 ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, zSqCl_of_ne v one_ne_zero]; simp
    | succ k ih => rw [pow_succ, zSqCl_mul v (pow_ne_zero _ two_ne_zero) two_ne_zero, ih, pow_succ]
  unfold tildeTernary
  rw [ordZ_zSqCl v h2 h hu, twoSqCl_eq, zSqCl_mul v (pow_ne_zero _ two_ne_zero) hu0, hpow,
    zSqCl_mul v two_ne_zero hu0]
  rw [← zpow_natCast, mul_comm (zSqCl v 2 ^ (h : ℤ)), mul_assoc, ← _root_.zpow_add,
    show (h : ℤ) + (1 - h) = 1 by ring, zpow_one, mul_comm]

/-- The local genus $G_0$ of Hessian valuation $1$ and unit class $u$ is the genus of `baseList u`. -/
theorem genus_eq_base (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) (h : ℕ) (G₀ : LocGenus v 3)
    (hn₀ : G₀.Nondeg) (hp₀ : G₀.Prim) (hd₀ : G₀.det = tildeTernary v (zSqCl v (2 ^ h * u))) :
    G₀ = genusOf v 3 (baseList u) := by
  obtain ⟨hv, h0, hn, hev, hpr, hval, hunit, -⟩ := baseList_props hu
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  rw [tildeTernary_zSqCl h2 h huo] at hd₀
  have hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v (2 * u)) = 1 := by
    have := ordZ_zSqCl v h2 1 huo
    simpa using this
  have hdB : (genusOf v 3 (baseList u)).det = zSqCl v (2 * u) := by
    rw [det_genusOf v hv h0 hn hev, hval]
    have hpo : Odd (unitProd (baseList u)) := Int.not_even_iff_odd.mp (fun he =>
      odd_unitProd _ hv (even_iff_two_dvd.mp he))
    have := (zSqCl_eq_iff v h2 1 hpo huo).mpr hunit
    simpa using this
  exact (locGenus_eq_of_det_ordZ_one v h2 hS G₀ (genusOf v 3 (baseList u)) hn₀ hp₀ hd₀
    (nondeg_genusOf v hv h0 hn hev) ((prim_genusOf_iff v h2 hn).mpr hpr) hdB).symm

open Classical in
/-- **The local genera in $\mathrm{Gen}^*_2(S, \varepsilon; 3)$ are the genera of the admissible block lists** with Hasse
invariant $\varepsilon$, for $S = [2^h u]$. -/
@[kb "hanke2011ternary" "§4, Lemma 4.2 and Def. 4.5, pp. 10–11 (the genera of Gen*_2(S, ε; 3))"]
theorem genStar_eq_image (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (h : ℕ) {u : ℤ} (hu : u ∈ sqUnits) (ε : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar (zSqCl v (2 ^ h * u)) ε} =
      ↑(((admSet h u).filter fun D => hasseQ D = ε).image (genusOf v 3)) := by
  classical
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  ext G
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image]
  constructor
  · rintro ⟨hn, hp, hd, hh⟩
    obtain ⟨D, hD, h0, hdim, hev, rfl⟩ := exists_genusOf v h2 G hn
    have hpo : Odd (unitProd D) := Int.not_even_iff_odd.mp (fun he => odd_unitProd _ hD (even_iff_two_dvd.mp he))
    rw [det_genusOf v hD h0 hdim hev] at hd
    have hval : valSum D = h := by
      have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) hd
      rw [ordZ_zSqCl v h2 _ hpo, ordZ_zSqCl v h2 _ huo] at this
      exact_mod_cast this
    rw [hval] at hd
    have hunit := (zSqCl_eq_iff v h2 h hpo huo).mp hd
    refine ⟨D, ⟨mem_admSet_iff.mpr ⟨hD, h0, hdim, hev, (prim_genusOf_iff v h2 hdim).mp hp, hval, hunit⟩, ?_⟩, rfl⟩
    simpa [hasse_genusOf v h2 hD h0 hdim hev] using hh
  · rintro ⟨D, ⟨hDm, hh⟩, rfl⟩
    obtain ⟨hD, h0, hdim, hev, hpr, hval, hunit⟩ := mem_admSet_iff.mp hDm
    have hpo : Odd (unitProd D) := Int.not_even_iff_odd.mp (fun he => odd_unitProd _ hD (even_iff_two_dvd.mp he))
    refine ⟨nondeg_genusOf v hD h0 hdim hev, (prim_genusOf_iff v h2 hdim).mpr hpr, ?_, ?_⟩
    · rw [det_genusOf v hD h0 hdim hev, hval]
      exact (zSqCl_eq_iff v h2 h hpo huo).mpr hunit
    · rw [hasse_genusOf v h2 hD h0 hdim hev]; exact hh

/-- The ratio $\beta(G_0)/\beta(G_D)$ is the mass weight of $D$ (given Conway–Sloane's (3) at $2$). -/
theorem beta_ratio_eq_massWt (hCS : PMassFormulaTwo) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {h : ℕ} (hh : 1 ≤ h) {u : ℤ}
    (hu : u ∈ sqUnits) {D : List DyBlock} (hDm : D ∈ admSet h u) :
    (genusOf v 3 (baseList u)).beta / (genusOf v 3 D).beta = massWt h u D := by
  obtain ⟨hv, h0, hn, hev, -, hval, -, hsupp⟩ := baseList_props hu
  obtain ⟨hD, hD0, hDn, hDev, -, hDval, -⟩ := mem_admSet_iff.mp hDm
  have hb0 := beta_genusOf_three v hCS h2 hv h0 hn hev hsupp
  have hb := beta_genusOf_three v hCS h2 hD hD0 hDn hDev (supportedBelow_of_mem_admSet hDm)
  have hp0 : 0 < (genusOf v 3 (baseList u)).beta := LocGenus.beta_pos v _ (nondeg_genusOf v hv h0 hn hev)
  have hp : 0 < (genusOf v 3 D).beta := LocGenus.beta_pos v _ (nondeg_genusOf v hD hD0 hDn hDev)
  rw [hval] at hb0
  rw [hDval] at hb
  have hm0 : pMassTwo (blockSymbol (baseList u)) 2 ≠ 0 := by
    intro h0'; rw [hb0, h0', div_zero] at hp0; exact lt_irrefl _ hp0
  have hm : pMassTwo (blockSymbol D) (h + 1) ≠ 0 := by
    intro h0'; rw [hb, h0', div_zero] at hp; exact lt_irrefl _ hp
  rw [hb0, hb]
  unfold massWt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [show 1 + k - 1 = k by omega]
  have e1 : (2 : ℝ) ^ (2 * 1) = 4 := by norm_num
  have e2 : (2 : ℝ) ^ (2 * (1 + k)) = 4 * 4 ^ k := by
    rw [pow_mul, pow_add]; norm_num
  rw [e1, e2, _root_.one_div_pow]
  generalize pMassTwo (blockSymbol D) (1 + k + 1) = m at hm ⊢
  generalize pMassTwo (blockSymbol (baseList u)) 2 = m0 at hm0 ⊢
  have h4 : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

open Classical in
/-- **The mass sums of Table 5.3 as sums over admissible block lists** (given Conway–Sloane's (3) at $2$). -/
@[kb "hanke2011ternary" "Thm. 4.12, p. 15 (the mass sums as sums over genus symbols)"]
theorem massSum_eq_sum (hCS : PMassFormulaTwo) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {h : ℕ} (hh : 1 ≤ h) {u : ℤ}
    (hu : u ∈ sqUnits) (G₀ : LocGenus v 3) (hG₀ : G₀ = genusOf v 3 (baseList u)) (ε : ℤ) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (zSqCl v (2 ^ h * u)) ε}, G₀.beta / G.beta) =
      ∑ D ∈ (admSet h u).filter (fun D => hasseQ D = ε), massWt h u D / (classCount h u D : ℝ) := by
  classical
  rw [genStar_eq_image h2 h hu ε, finsum_mem_coe_finset, sum_image_eq_sum_div_card]
  refine Finset.sum_congr rfl fun D hD => ?_
  obtain ⟨hDm, hDh⟩ := Finset.mem_filter.mp hD
  obtain ⟨hDv, hD0, hDn, hDev, -⟩ := mem_admSet_iff.mp hDm
  rw [hG₀, beta_ratio_eq_massWt hCS h2 hh hu hDm]
  congr 2
  unfold classCount
  congr 1
  ext D'
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hD'm, -⟩, he⟩
    obtain ⟨hv', h0', hn', hev', -⟩ := mem_admSet_iff.mp hD'm
    exact ⟨hD'm, Relation.EqvGen.symm _ _ ((genusOf_eq_iff v h2 hv' h0' hn' hev' hDv hD0 hDn hDev).mp he)⟩
  · rintro ⟨hD'm, hm⟩
    obtain ⟨hv', h0', hn', hev', -⟩ := mem_admSet_iff.mp hD'm
    have he : genusOf v 3 D' = genusOf v 3 D :=
      (genusOf_eq_iff v h2 hv' h0' hn' hev' hDv hD0 hDn hDev).mpr (Relation.EqvGen.symm _ _ hm)
    refine ⟨⟨hD'm, ?_⟩, he⟩
    rw [← hasse_genusOf v h2 hv' h0' hn' hev', he, hasse_genusOf v h2 hDv hD0 hDn hDev, hDh]

/-- **Theorem 4.12 / Table 5.3 at $p = 2$ (Hanke 2011), conditional on Conway–Sloane's (3) at $2$ and the named
combinatorial statement `TernaryDyadicMassCount`.** -/
@[kb "hanke2011ternary" "Thm. 4.12 and Tables 5.1–5.3, pp. 15–22"]
theorem dyadicTernaryLocalMassTable_of (hCS : PMassFormulaTwo) (hC : TernaryDyadicMassCount) :
    DyadicTernaryLocalMassTable := by
  classical
  have key : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ (S : LocalSqCl v) (G₀ : LocGenus v 3), 1 ≤ SqCl.ordZ (localOrd v) (localUnits_le_ker v) S →
        G₀.Nondeg → G₀.Prim → G₀.det = tildeTernary v S →
        ∃ h : ℕ, 1 ≤ h ∧ SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = h ∧ ∃ u ∈ sqUnits,
          S = zSqCl v (2 ^ h * u) ∧ G₀ = genusOf v 3 (baseList u) := by
    intro v h2 S G₀ hS hn₀ hp₀ hd₀
    obtain ⟨h, hh⟩ : ∃ h : ℕ, SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = h :=
      ⟨(SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat, by omega⟩
    obtain ⟨u, hu, rfl⟩ := exists_zSqCl_eq v h2 S h hh
    exact ⟨h, by omega, hh, u, hu, rfl, genus_eq_base h2 hu h G₀ hn₀ hp₀ hd₀⟩
  constructor
  · intro v h2 S G₀ hS hn₀ hp₀ hd₀
    obtain ⟨h, hh1, hh, u, hu, rfl, hG₀⟩ := key v h2 S G₀ hS hn₀ hp₀ hd₀
    rw [massSum_eq_sum hCS h2 hh1 hu G₀ hG₀, massSum_eq_sum hCS h2 hh1 hu G₀ hG₀, hh, Int.toNat_natCast,
      ← hC.A_eq h hh1 u hu, ← Finset.sum_filter_add_sum_filter_not (admSet h u) (fun D => hasseQ D = 1)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext D
    simp only [Finset.mem_filter]
    rcases hasseQ_eq_one_or_neg_one D with hD | hD <;> simp [hD]
  · intro v h2 S G₀ hS hn₀ hp₀ hd₀
    obtain ⟨h, hh1, hh, u, hu, rfl, hG₀⟩ := key v h2 S G₀ hS hn₀ hp₀ hd₀
    obtain ⟨hv, h0, hn, hev, -⟩ := baseList_props hu
    rw [massSum_eq_sum hCS h2 hh1 hu G₀ hG₀, massSum_eq_sum hCS h2 hh1 hu G₀ hG₀, hh, Int.toNat_natCast, hG₀,
      hasse_genusOf v h2 hv h0 hn hev, ← hC.B_eq h hh1 u hu,
      ← Finset.sum_filter_add_sum_filter_not (admSet h u) (fun D => hasseQ D = 1)]
    have h1 : ∑ D ∈ (admSet h u).filter (fun D => hasseQ D = 1), (hasseQ D : ℝ) * massWt h u D /
        (classCount h u D : ℝ) = ∑ D ∈ (admSet h u).filter (fun D => hasseQ D = 1),
          massWt h u D / (classCount h u D : ℝ) :=
      Finset.sum_congr rfl fun D hD => by rw [(Finset.mem_filter.mp hD).2]; simp
    have h2' : ∑ D ∈ (admSet h u).filter (fun D => ¬ hasseQ D = 1), (hasseQ D : ℝ) * massWt h u D /
        (classCount h u D : ℝ) = -∑ D ∈ (admSet h u).filter (fun D => hasseQ D = -1),
          massWt h u D / (classCount h u D : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      have hs : (admSet h u).filter (fun D => ¬ hasseQ D = 1) = (admSet h u).filter (fun D => hasseQ D = -1) := by
        ext D
        simp only [Finset.mem_filter]
        rcases hasseQ_eq_one_or_neg_one D with hD | hD <;> simp [hD]
      rw [hs]
      refine Finset.sum_congr rfl fun D hD => ?_
      rw [(Finset.mem_filter.mp hD).2]; push_cast; ring
    rw [h1, h2']
    ring

/-- **Theorem 4.12 / Table 5.3 at $p = 2$ (Hanke 2011), conditional only on the named combinatorial statement
`TernaryDyadicMassCount`.** Conway–Sloane's formula (3) at $p = 2$ is now proved
(`ConwaySloane.Mass.Two.pMassFormulaTwo_holds`), so the hypothesis `PMassFormulaTwo` of
`dyadicTernaryLocalMassTable_of` is discharged. -/
@[kb "hanke2011ternary" "Thm. 4.12 and Tables 5.1–5.3, pp. 15–22"]
theorem dyadicTernaryLocalMassTable_of_count (hC : TernaryDyadicMassCount) :
    DyadicTernaryLocalMassTable :=
  dyadicTernaryLocalMassTable_of ConwaySloane.Mass.Two.pMassFormulaTwo_holds hC

end

end QuadFormsKB.Dyadic7

#print axioms QuadFormsKB.Dyadic7.genStar_eq_image
#print axioms QuadFormsKB.Dyadic7.massSum_eq_sum
#print axioms QuadFormsKB.Dyadic7.dyadicTernaryLocalMassTable_of
#print axioms QuadFormsKB.Dyadic7.dyadicTernaryLocalMassTable_of_count
