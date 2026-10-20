/-
# Dyadic bridge checks over $\mathbb{Z}_2$ ($e = f = 1$)

**Layer:** bridge between the ℚ layer at $p = 2$ and the dyadic DVR results of `DVRDyadic.lean` and
`DVRDyadicTable.lean`, at $R = \mathbb{Z}_2$ ($\pi = 2$, $e = \mathrm{ord}_2 2 = 1$, $q = 2$). The ℚ layer has no explicit
$p = 2$ results of its own (Tables 1–2 there are for odd $p$), so these are checks of the dyadic formulas against
direct counts:
- `localDensity_hyperbolic_two`: $\beta_2(1) = 1/2$ for $x_0x_1$ ($\varepsilon = +1$, $1 - \varepsilon/q^r$);
- `localDensity_anisoPlane_two`: $\beta_2(1) = 3/2$ for $x_0^2 + x_0x_1 + x_1^2$ ($\varepsilon = -1$);
- `localDensity_sumTwoSq_two`: $\beta_2(1) = 2$ for $x_0^2 + x_1^2$, computed at the level $2e + 1 = 3$
  ($r_8(1) = 16$, by enumeration), whereas the level-1 value $r_2(1)/2 = 1$ is wrong: with 1-dimensional unimodular
  blocks the residue-field count does not determine the density at $p = 2$.
**Depends on** `Bridge.lean`, `DVRDyadicTable.lean`.
-/
import QuadFormsKB.LocalDensity.Bridge
import QuadFormsKB.LocalDensity.DVRDyadicTable

namespace QuadFormsKB.LocalDensity

open QuadForm

/-- `pairSumForm` commutes with change of coefficient ring. -/
theorem DVR.pairSumForm_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) {r : ℕ}
    (A : Fin r → S × S × S) :
    (DVR.pairSumForm A).map f = DVR.pairSumForm (fun i => (f (A i).1, f (A i).2.1, f (A i).2.2)) := by
  ext k l
  simp only [QuadForm.map, DVR.pairSumForm, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- $\#\mathbb{Z}_2/2 = 2$: a `Fintype` structure on the residue field of $\mathbb{Z}_2$ (via $\mathbb{F}_2$; local). -/
@[instance_reducible]
noncomputable def fintypeResidueTwo : Fintype (IsLocalRing.ResidueField ℤ_[2]) :=
  Fintype.ofEquiv (ZMod 2) PadicInt.residueField.symm.toEquiv

attribute [local instance] fintypeResidueTwo Classical.decEq

local notation "res2" => IsLocalRing.residue ℤ_[2]

/-- The Arf sign of $x_0x_1$ over $\mathbb{Z}_2$ is $+1$. -/
theorem pairArf_hyperbolic_two :
    DVR.pairArf (R := ℤ_[2]) ![((0 : ℤ_[2]), (1 : ℤ_[2]), (0 : ℤ_[2]))] = 1 := by
  unfold DVR.pairArf DVR.arfSign
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
    Finset.prod_singleton, map_zero, zero_mul, zero_div]
  exact ite_eq_left_iff.2 fun h => absurd ⟨0, by simp⟩ h

/-- The Arf sign of $x_0^2 + x_0x_1 + x_1^2$ over $\mathbb{Z}_2$ is $-1$. -/
theorem pairArf_anisoPlane_two :
    DVR.pairArf (R := ℤ_[2]) ![((1 : ℤ_[2]), (1 : ℤ_[2]), (1 : ℤ_[2]))] = -1 := by
  unfold DVR.pairArf DVR.arfSign
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
    map_one, one_mul, one_pow, div_one, Finset.prod_singleton, ite_eq_right_iff]
  rintro ⟨z, hz⟩
  have h := congrArg (PadicInt.residueField (p := 2)) hz
  simp only [map_add, map_pow, map_one] at h
  revert h
  generalize PadicInt.residueField (p := 2) z = w
  revert w
  decide


theorem padic_two_irreducible : Irreducible (2 : ℤ_[2]) := by
  exact_mod_cast PadicInt.irreducible_p (p := 2)

theorem not_two_dvd_one_padic : ¬ (2 : ℤ_[2]) ∣ 1 := fun h =>
  padic_two_irreducible.not_isUnit (isUnit_of_dvd_one h)

/-- **Bridge check, $e = f = 1$: the hyperbolic plane over $\mathbb{Z}_2$** (ℚ layer). For $Q = x_0x_1$ over $\mathbb{Z}$,
$\beta_2(1) = 1/2$: `DVR.localDensity_unit_pairSum` with $q = 2$, $r = 1$, $\varepsilon = +1$, through the bridge
`localDensity_eq_padic`. (Directly: $x_0x_1 \equiv 1 \pmod{2^k}$ has $2^{k-1}$ solutions.) -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (p = 2 check)"]
theorem localDensity_hyperbolic_two :
    localDensity (DVR.pairSumForm ![((0 : ℤ), (1 : ℤ), (0 : ℤ))]) 2 1 = 1 / 2 := by
  rw [localDensity_eq_padic, DVR.pairSumForm_map]
  have h := DVR.localDensity_unit_pairSum (R := ℤ_[2]) ![((0 : ℤ_[2]), (1 : ℤ_[2]), (0 : ℤ_[2]))] 2
    padic_two_irreducible (dvd_refl 2) (fun i => by fin_cases i; exact not_two_dvd_one_padic) le_rfl 1
    not_two_dvd_one_padic
  rw [pairArf_hyperbolic_two, q_padicInt] at h
  convert h using 2
  · congr 1; funext i; fin_cases i; simp
  · simp
  · norm_num

/-- **Bridge check, $e = f = 1$: the anisotropic plane over $\mathbb{Z}_2$** (ℚ layer). For $Q = x_0^2 + x_0x_1 + x_1^2$,
$\beta_2(1) = 3/2$ ($\varepsilon = -1$: $z^2 + z = 1$ has no root in $\mathbb{F}_2$); directly, $r_2(1) = 3$. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (p = 2 check)"]
theorem localDensity_anisoPlane_two :
    localDensity (DVR.pairSumForm ![((1 : ℤ), (1 : ℤ), (1 : ℤ))]) 2 1 = 3 / 2 := by
  rw [localDensity_eq_padic, DVR.pairSumForm_map]
  have h := DVR.localDensity_unit_pairSum (R := ℤ_[2]) ![((1 : ℤ_[2]), (1 : ℤ_[2]), (1 : ℤ_[2]))] 2
    padic_two_irreducible (dvd_refl 2) (fun i => by fin_cases i; exact not_two_dvd_one_padic) le_rfl 1
    not_two_dvd_one_padic
  rw [pairArf_anisoPlane_two, q_padicInt] at h
  convert h using 2
  · congr 1; funext i; fin_cases i; simp
  · simp
  · norm_num

/-- $r_{8}(1) = 16$ for $x_0^2 + x_1^2$ (by enumeration of $(\mathbb{Z}/8)^2$). -/
theorem repCount_sumTwoSq_eight : repCount (QuadForm.diag ![(1 : ℤ), 1]) 2 3 1 = 16 := by
  unfold repCount
  have : ∀ x : Fin 2 → ZMod (2 ^ 3), (QuadForm.diag ![(1 : ℤ), 1]).evalIn (ZMod (2 ^ 3)) x =
      ((1 : ℤ) : ZMod (2 ^ 3)) ↔ x 0 ^ 2 + x 1 ^ 2 = 1 := by
    intro x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal_apply, sq]
  rw [Nat.card_congr (Equiv.subtypeEquivRight this), Nat.card_eq_fintype_card]
  decide

/-- $r_{2}(1) = 2$ for $x_0^2 + x_1^2$. -/
theorem repCount_sumTwoSq_two : repCount (QuadForm.diag ![(1 : ℤ), 1]) 2 1 1 = 2 := by
  unfold repCount
  have : ∀ x : Fin 2 → ZMod (2 ^ 1), (QuadForm.diag ![(1 : ℤ), 1]).evalIn (ZMod (2 ^ 1)) x =
      ((1 : ℤ) : ZMod (2 ^ 1)) ↔ x 0 ^ 2 + x 1 ^ 2 = 1 := by
    intro x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal_apply, sq]
  rw [Nat.card_congr (Equiv.subtypeEquivRight this), Nat.card_eq_fintype_card]
  decide

/-- **At $p = 2$ the unit density is not $r_p(m)/p^{n-1}$** (the non-dyadic Remark 3.4.1(a) formula
`localDensity_unit` fails at $p = 2$; Lemma 3.2's level $2e + 1 = 3$ is needed for 1-dimensional blocks).
For $Q = x_0^2 + x_1^2$ over $\mathbb{Z}$: $\beta_2(1) = r_8(1)/8 = 2$ (`DVR.localDensity_unit_unimodular` with
$t = e = 1$, $K = 3$), while $r_2(1)/2 = 1$ and $r_4(1)/4 = 2$; level $1$ is wrong. -/
@[kb "hanke2004" "Lemma 3.2, p. 358; Remark 3.4.1(a), p. 361 (p = 2 check)"]
theorem localDensity_sumTwoSq_two :
    localDensity (QuadForm.diag ![(1 : ℤ), 1]) 2 1 = 2 ∧
      (repCount (QuadForm.diag ![(1 : ℤ), 1]) 2 1 1 : ℝ) / (2 : ℝ) ^ (2 - 1) = 1 := by
  refine ⟨?_, by rw [repCount_sumTwoSq_two]; norm_num⟩
  have hd : (QuadForm.diag ![(1 : ℤ), 1]).map (Int.castRingHom ℤ_[2]) =
      QuadForm.diag ![(1 : ℤ_[2]), 1] := by
    ext i j; simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> fin_cases i <;> simp
  have hJ := DVR.isJordanFormW_diag_unit ![(1 : ℤ_[2]), 1] padic_two_irreducible
    (fun i => by fin_cases i <;> exact not_two_dvd_one_padic)
  have he : (2 : ℤ_[2]) ^ 1 ∣ 2 ∧ ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ 2 := by
    have := padicInt_not_sq_dvd_two 2
    exact ⟨by simp, by exact_mod_cast this⟩
  have h := DVR.localDensity_unit_unimodular (QuadForm.diag ![(1 : ℤ_[2]), 1]) 2 padic_two_irreducible
    ∅ hJ 1 (DVR.gradBound_ord_two hJ 1 he) 1 not_two_dvd_one_padic 3 le_rfl
  rw [localDensity_eq_padic]
  have hr := (repCount_eq_padic (QuadForm.diag ![(1 : ℤ), 1]) 2 ∅ 3 1).1
  rw [hd] at hr
  have hm : ((1 : ℤ) : ℤ_[2]) = 1 := by simp
  rw [hm, hd, Nat.cast_ofNat, h, q_padicInt]
  push_cast at hr
  rw [← hr, repCount_sumTwoSq_eight]
  norm_num

end QuadFormsKB.LocalDensity
