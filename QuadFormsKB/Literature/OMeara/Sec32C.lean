/-
# O'Meara §32A–§32B: extensions of local fields; unramified and fully ramified extensions (32:3, 32:6, 32:6a, 32:9–32:15)

**Setting.** The valuation framework of `Sec13B.lean` and `Sec16.lean`: for a finite extension $E/F$ and a valuation
$w$ of $E$, the induced valuation of $F$ is `w.under F`. O'Meara's local field (32:1) at a spot $\mathfrak p$ is a field
complete at a discrete spot with finite residue class field: here the hypotheses `IsDiscreteAbs (w.under F)`,
`CompleteSpace (WithAbs (w.under F))` and finiteness of `residueFieldOf`. (`IsLocalFieldSpot` of `Sec32A.lean` is the
same notion for a field with a $\mathbb Z_{m0}$-valued valuation, the encoding used for completions of number fields;
the valuation encoding is the one in which extensions, $e$ and $f$ are available.) $N\mathfrak p$ is the number of
elements of the residue class field.

**Defines**
* `IsNormalizedAbs v` (§32A, p. 59): $v$ is the *normalized valuation* of its spot: non-archimedean, $N\mathfrak p$
  finite, and $N\mathfrak p$ generates the value group;
* `IsUnramifiedAbs`, `IsFullyRamifiedAbs` (§32B, p. 60): $e = 1, f = n$, respectively $e = n, f = 1$;
* `frobeniusAbs` (**32:13**): the Frobenius automorphism of an unramified extension.

**Proves** `exists_unique_isNormalizedAbs` (§32A), `isLocal_of_finite` (**32:3**), `isUnramifiedAbs_of_derivative`
(**32:6**), `isUnramifiedAbs_adjoin_root_of_unity` (**32:6a**), `isUnramifiedAbs_of_isSplittingField` (**32:9**),
`isSplittingField_of_isUnramifiedAbs` (**32:10**), `unramified_subfield_unique`, `unramified_subfield_le` (**32:11**),
`isGalois_isCyclic_frobenius` (**32:12**), `frobeniusAbs_rootOfUnity` (**32:12a**), `isUnramifiedAbs_sup`
(**32:14**), `isFullyRamifiedAbs_of_eisenstein` (**32:15**), and the tower rules of §32B, p. 61
(`isUnramifiedAbs_tower_iff`, `isFullyRamifiedAbs_tower_iff`).
-/
import QuadFormsKB.Citation
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import QuadFormsKB.Literature.OMeara.Sec16
import QuadFormsKB.Literature.OMeara.Sec14A
import QuadFormsKB.Literature.OMeara.Sec32B

open Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace QuadFormsKB.OMeara

section Normalized

variable {F : Type*} [Field F]

/-- Equivalent valuations have residue class fields of the same cardinality. -/
theorem natCard_residueFieldOf_of_isEquiv {v w : AbsoluteValue F ℝ} (h : v.IsEquiv w)
    (hv : IsNonarchimedean v) (hw : IsNonarchimedean w) :
    Nat.card (residueFieldOf v hv) = Nat.card (residueFieldOf w hw) :=
  Nat.card_congr ((ResidueData.of_isEquiv h).resEquiv hv hw).toEquiv

/-- The *normalized valuation* at a discrete spot with finite residue class field (§32A, p. 59): the valuation $v$ of
the spot under which $N\mathfrak p$ (the number of elements of the residue class field) generates the value group,
i.e. $|\pi| = N\mathfrak p^{-1}$ for a prime element $\pi$. -/
@[kb "omeara1963" "§32A, p. 59 (the normalized valuation at p)"]
def IsNormalizedAbs (v : AbsoluteValue F ℝ) : Prop :=
  ∃ hv : IsNonarchimedean v, ∃ h : (Nat.card (residueFieldOf v hv) : ℝ) ≠ 0,
    absValueGroup v = Subgroup.zpowers (Units.mk0 _ h)

/-- **The normalized valuation exists and is unique** (§32A, p. 59): a discrete spot with finite residue class field
contains exactly one normalized valuation. -/
@[kb "omeara1963" "§32A, p. 59 (canonical choice of the normalized valuation)"]
theorem exists_unique_isNormalizedAbs {v : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v)
    [Finite (residueFieldOf v hd.isNonarchimedean)] :
    ∃! v' : AbsoluteValue F ℝ, v'.IsEquiv v ∧ IsNormalizedAbs v' := by
  have hna := hd.isNonarchimedean
  set N := Nat.card (residueFieldOf v hna) with hN
  have hN2 : 2 ≤ N := Finite.one_lt_card
  have hNpos : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hg0 := genAbs_pos hd
  have hg1 := genAbs_lt_one hd
  have hlg : Real.log (genAbs hd) < 0 := Real.log_neg hg0 hg1
  set c : ℝ := Real.log N / (- Real.log (genAbs hd)) with hc
  have hcpos : 0 < c := div_pos (Real.log_pos hN1) (by linarith)
  refine ⟨rpowAbs v hna c hcpos, ⟨?_, ?_⟩, ?_⟩
  · exact AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hcpos, rfl⟩ |>.symm
  · have hna' : IsNonarchimedean (rpowAbs v hna c hcpos) := by
      intro x y
      have h1 := hna x y
      show v (x + y) ^ c ≤ max (v x ^ c) (v y ^ c)
      rcases le_max_iff.1 h1 with h | h
      · exact (Real.rpow_le_rpow (v.nonneg _) h hcpos.le).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow (v.nonneg _) h hcpos.le).trans (le_max_right _ _)
    have heq : v.IsEquiv (rpowAbs v hna c hcpos) :=
      AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hcpos, rfl⟩
    have hcard := natCard_residueFieldOf_of_isEquiv heq.symm hna' hna
    refine ⟨hna', ?_, ?_⟩
    · rw [hcard]; exact hNpos.ne'
    · rw [absValueGroup_rpow v (rpowAbs v hna c hcpos) (c := c) (fun x => rfl),
        absValueGroup_eq_zpowers_genAbs hd, MonoidHom.map_zpowers]
      have hgc : (rpowUnitHom c (Units.mk0 (genAbs hd) hg0.ne') : ℝˣ) = (Units.mk0 (N : ℝ) hNpos.ne')⁻¹ := by
        apply Units.ext
        rw [rpowUnitHom_val, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, abs_of_pos hg0]
        have : (genAbs hd) ^ c = ((N : ℝ))⁻¹ := by
          rw [Real.rpow_def_of_pos hg0, hc]
          have h3 : Real.log (genAbs hd) * (Real.log N / (- Real.log (genAbs hd))) = - Real.log N := by
            have : Real.log (genAbs hd) ≠ 0 := hlg.ne
            field_simp
          rw [h3, Real.exp_neg, Real.exp_log hNpos]
        exact this
      rw [hgc, Subgroup.zpowers_inv]
      congr 1
      apply Units.ext
      simp [hcard, hN]
  · intro v1 ⟨h1, h2⟩
    obtain ⟨hna1, hne1, hgrp1⟩ := h2
    obtain ⟨c1, hc1, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h1.symm
    have hv1 : ∀ x, v1 x = v x ^ c1 := fun x => (congrFun hcv x).symm
    have hcard1 := natCard_residueFieldOf_of_isEquiv h1 hna1 hna
    rw [absValueGroup_rpow v v1 hv1, absValueGroup_eq_zpowers_genAbs hd, MonoidHom.map_zpowers] at hgrp1
    set a := rpowUnitHom c1 (Units.mk0 (genAbs hd) hg0.ne') with ha
    set Nu : ℝˣ := Units.mk0 (Nat.card (residueFieldOf v1 hna1) : ℝ) hne1 with hNu
    have hNu' : (Nu : ℝ) = N := by simp [hNu, hcard1, hN]
    have haval : (a : ℝ) = genAbs hd ^ c1 := by
      rw [ha, rpowUnitHom_val, Units.val_mk0, abs_of_pos hg0]
    have hapos : 0 < (a : ℝ) := by rw [haval]; exact Real.rpow_pos_of_pos hg0 _
    have ha1 : (a : ℝ) < 1 := by rw [haval]; exact Real.rpow_lt_one hg0.le hg1 hc1
    have hamem : a ∈ Subgroup.zpowers Nu := by rw [← hgrp1]; exact Subgroup.mem_zpowers _
    have hNmem : Nu ∈ Subgroup.zpowers a := by rw [hgrp1]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hamem
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hNmem
    have hk' : (a : ℝ) = (N : ℝ) ^ k := by
      rw [← hk, Units.val_zpow_eq_zpow_val, hNu']
    have hl' : (N : ℝ) = (a : ℝ) ^ l := by
      rw [← hNu', ← hl, Units.val_zpow_eq_zpow_val]
    have hkl : (N : ℝ) ^ (k * l) = (N : ℝ) ^ (1 : ℤ) := by
      rw [zpow_mul, ← hk', ← hl', zpow_one]
    have hkl1 : k * l = 1 := zpow_right_injective₀ hNpos hN1.ne' hkl
    have hk1 : k = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hkl1 with h | h
      · exfalso
        rw [h, zpow_one] at hk'
        linarith
      · exact h
    rw [hk1, zpow_neg_one] at hk'
    have hlog : c1 * Real.log (genAbs hd) = - Real.log N := by
      have := congrArg Real.log (haval.symm.trans hk')
      rw [Real.log_rpow hg0, Real.log_inv] at this
      linarith
    have hc1c : c1 = c := by
      rw [hc, eq_div_iff (neg_ne_zero.2 hlg.ne)]; linarith
    subst hc1c
    ext x
    exact hv1 x

end Normalized

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A valuation of $E$ inducing a non-archimedean valuation of $F$ is non-archimedean (§11B, p. 4: the natural
integers of $E$ lie in $F$, and 11:1). -/
theorem isNonarchimedean_of_under {w : AbsoluteValue E ℝ} (h : IsNonarchimedean (w.under F)) :
    IsNonarchimedean w := by
  rw [isNonarchimedean_iff_natCast_bounded]
  refine ⟨1, fun n => ?_⟩
  have h1 : w (n : E) = (w.under F) (n : F) := by rw [under_apply_eq]; simp
  rw [h1]; exact h.apply_natCast_le_one (by simp) (map_one _)

/-- The valuation of the field `WithAbs v` (for discrete `v`) as a nontrivially normed field. -/
@[reducible] noncomputable def nntfOf {v : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v) :
    NontriviallyNormedField (WithAbs v) :=
  { (inferInstance : NormedField (WithAbs v)) with
    non_trivial := by
      obtain ⟨π, hπ0, hπ⟩ := exists_apply_eq_genAbs hd
      refine ⟨WithAbs.toAbs v π⁻¹, ?_⟩
      have := genAbs_lt_one hd
      rw [WithAbs.norm_toAbs_eq]
      simp [hπ]
      exact (one_lt_inv₀ (genAbs_pos hd)).2 this }

theorem isUltrametricDist_withAbs {v : AbsoluteValue F ℝ} (hv : IsNonarchimedean v) :
    IsUltrametricDist (WithAbs v) := by
  rw [IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm]
  intro x y
  exact hv x.ofAbs y.ofAbs

theorem completeSpace_of_under [FiniteDimensional F E] {w : AbsoluteValue E ℝ}
    (hd : IsDiscreteAbs (w.under F)) [CompleteSpace (WithAbs (w.under F))] :
    CompleteSpace (WithAbs w) := by
  letI := nntfOf hd
  haveI := isUltrametricDist_withAbs hd.isNonarchimedean
  exact extension_complete (K := WithAbs (w.under F)) (L := E) w (fun x => rfl)

/-- **14:1 for discrete complete `F`**: $|\alpha|_w = |N_{E/F}\alpha|^{1/n}$. -/
theorem apply_eq_norm_rpow [FiniteDimensional F E] {w : AbsoluteValue E ℝ}
    (hd : IsDiscreteAbs (w.under F)) [CompleteSpace (WithAbs (w.under F))] (α : E) :
    w α = (w.under F (Algebra.norm F α)) ^ (1 / (Module.finrank F E : ℝ)) := by
  letI := nntfOf hd
  haveI := isUltrametricDist_withAbs hd.isNonarchimedean
  have h1 : w = spectralAbs (K := WithAbs (w.under F)) (L := E) :=
    eq_spectralAbs_of_extends (K := WithAbs (w.under F)) (L := E) w (fun x => rfl)
  have h2 := (prolongation_formula (K := WithAbs (w.under F)) (L := E)).2.1 α
  rw [← h1] at h2
  rw [h2]
  have e1 : Module.finrank (WithAbs (w.under F)) E = Module.finrank F E :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv (w.under F)) (RingEquiv.refl E) rfl
  have e2 : ‖(Algebra.norm (WithAbs (w.under F))) α‖ = w.under F (Algebra.norm F α) := by
    have := Algebra.norm_eq_of_ringEquiv (WithAbs.equiv (w.under F)) (C := E) rfl α
    rw [← this]
    rfl
  rw [e1, e2]

/-- A subgroup of `ℝˣ` generated by a unit `a < 1` and by a unit `N > 1` has `a = N⁻¹`. -/
theorem eq_inv_of_zpowers_eq {a N : ℝˣ} (h : Subgroup.zpowers a = Subgroup.zpowers N) (ha : (a : ℝ) < 1)
    (hN : 1 < (N : ℝ)) : (a : ℝ) = (N : ℝ)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hamem : a ∈ Subgroup.zpowers N := by rw [← h]; exact Subgroup.mem_zpowers _
  have hNmem : N ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hamem
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hNmem
  have hk' : (a : ℝ) = (N : ℝ) ^ k := by rw [← hk, Units.val_zpow_eq_zpow_val]
  have hl' : (N : ℝ) = (a : ℝ) ^ l := by rw [← hl, Units.val_zpow_eq_zpow_val]
  have hkl : (N : ℝ) ^ (k * l) = (N : ℝ) ^ (1 : ℤ) := by
    rw [zpow_mul, ← hk', ← hl', zpow_one]
  have hkl1 : k * l = 1 := zpow_right_injective₀ hNpos hN.ne' hkl
  have hk1 : k = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkl1 with h | h
    · exfalso
      rw [h, zpow_one] at hk'
      linarith
    · exact h
  rw [hk', hk1, zpow_neg_one]

/-- If `v' = v ^ b` is normalized and `v` is discrete with normalized generator `g`, then `g ^ b = (N v')⁻¹`. -/
theorem genAbs_rpow_eq_inv {F : Type*} [Field F] {v v' : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v) {b : ℝ}
    (hb : 0 < b) (hv' : ∀ x, v' x = v x ^ b) {hna' : IsNonarchimedean v'}
    {hne : (Nat.card (residueFieldOf v' hna') : ℝ) ≠ 0}
    (hgrp : absValueGroup v' = Subgroup.zpowers (Units.mk0 _ hne))
    [Finite (residueFieldOf v' hna')] :
    genAbs hd ^ b = ((Nat.card (residueFieldOf v' hna') : ℝ))⁻¹ := by
  have hg0 := genAbs_pos hd
  have hg1 := genAbs_lt_one hd
  have hN1 : (1 : ℝ) < (Nat.card (residueFieldOf v' hna') : ℝ) := by
    exact_mod_cast Finite.one_lt_card
  rw [absValueGroup_rpow v v' hv', absValueGroup_eq_zpowers_genAbs hd, MonoidHom.map_zpowers] at hgrp
  have := eq_inv_of_zpowers_eq (a := rpowUnitHom b (Units.mk0 (genAbs hd) hg0.ne'))
    (N := Units.mk0 _ hne) hgrp (by
      rw [rpowUnitHom_val, Units.val_mk0, abs_of_pos hg0]; exact Real.rpow_lt_one hg0.le hg1 hb)
    (by simpa using hN1)
  rw [rpowUnitHom_val, Units.val_mk0, abs_of_pos hg0] at this
  simpa using this

/-- A root of a monic polynomial with integral coefficients is integral (domination). -/
theorem apply_le_one_of_aeval_eq_zero {w : AbsoluteValue E ℝ} (hw : IsNonarchimedean w) {f : F[X]}
    (hf : f.Monic) (hint : ∀ i, w (algebraMap F E (f.coeff i)) ≤ 1) {α : E} (hroot : aeval α f = 0) :
    w α ≤ 1 := by
  by_contra h
  push Not at h
  have hd : 0 < f.natDegree := by
    by_contra h0
    have h0' : f.natDegree = 0 := by omega
    have := hf.natDegree_eq_zero.1 h0'
    simp [this] at hroot
  have hsplit : α ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * α ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ] at hroot
    simp only [Algebra.smul_def, hf.coeff_natDegree, map_one, one_mul] at hroot
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hroot)
  have hbound : w (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * α ^ i) ≤
      w α ^ (f.natDegree - 1) := by
    apply sum_le_of_nonarch hw _ _ (by positivity)
    intro i hi
    have hi' : i ≤ f.natDegree - 1 := by have := Finset.mem_range.1 hi; omega
    rw [map_mul, map_pow]
    calc w (algebraMap F E (f.coeff i)) * w α ^ i ≤ 1 * w α ^ (f.natDegree - 1) :=
          mul_le_mul (hint i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have h1 : w α ^ f.natDegree ≤ w α ^ (f.natDegree - 1) := by
    rw [← map_pow, hsplit, AbsoluteValue.map_neg]; exact hbound
  have h2 : w α ^ (f.natDegree - 1) < w α ^ f.natDegree :=
    pow_lt_pow_right₀ h (by omega)
  linarith

/-- Uniqueness of the prolongation of a complete discrete valuation to a finite extension. -/
theorem ext_unique {v : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v) [CompleteSpace (WithAbs v)]
    {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L] (W W' : AbsoluteValue L ℝ)
    (h : ∀ x : F, W (algebraMap F L x) = v x) (h' : ∀ x : F, W' (algebraMap F L x) = v x) :
    W = W' := by
  letI := nntfOf hd
  haveI := isUltrametricDist_withAbs hd.isNonarchimedean
  exact extension_unique (K := WithAbs v) (L := L) W W' (fun x => h x.ofAbs) (fun x => h' x.ofAbs)

/-- Existence of the prolongation of a complete discrete valuation to a finite extension. -/
theorem exists_ext {v : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v) [CompleteSpace (WithAbs v)]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] :
    ∃ W : AbsoluteValue L ℝ, (∀ x : F, W (algebraMap F L x) = v x) ∧ CompleteSpace (WithAbs W) := by
  letI := nntfOf hd
  haveI := isUltrametricDist_withAbs hd.isNonarchimedean
  exact ⟨spectralAbs (K := WithAbs v) (L := L), fun x => spectralAbs_extends (K := WithAbs v) (L := L) (WithAbs.toAbs v x),
    completeSpace_spectralAbs⟩

/-- A prolongation of a complete discrete valuation is complete. -/
theorem completeSpace_of_ext {v : AbsoluteValue F ℝ} (hd : IsDiscreteAbs v) [CompleteSpace (WithAbs v)]
    {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L] (W : AbsoluteValue L ℝ)
    (h : ∀ x : F, W (algebraMap F L x) = v x) : CompleteSpace (WithAbs W) := by
  letI := nntfOf hd
  haveI := isUltrametricDist_withAbs hd.isNonarchimedean
  exact extension_complete (K := WithAbs v) (L := L) W (fun x => h x.ofAbs)

/-- A prolongation of a non-archimedean valuation is non-archimedean. -/
theorem isNonarchimedean_of_ext {v : AbsoluteValue F ℝ} (hv : IsNonarchimedean v)
    {L : Type*} [Field L] [Algebra F L] (W : AbsoluteValue L ℝ)
    (h : ∀ x : F, W (algebraMap F L x) = v x) : IsNonarchimedean W :=
  isNonarchimedean_of_under (F := F) (fun a b => by
    show (W.under F) (a + b) ≤ max ((W.under F) a) ((W.under F) b)
    rw [under_apply_eq, under_apply_eq, under_apply_eq, h, h, h]
    exact hv a b)

/-- The extension $E/F$ of local fields at $\mathfrak P$ is *unramified* (§32B, p. 60): $e(\mathfrak P|\mathfrak p) = 1$
and $f(\mathfrak P|\mathfrak p) = n = [E:F]$. -/
@[kb "omeara1963" "§32B, p. 60 (unramified extension)"]
def IsUnramifiedAbs (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) : Prop :=
  ramificationIndexAbs (F := F) w = 1 ∧ inertiaDegAbs (F := F) w hw = Module.finrank F E

/-- The extension $E/F$ of local fields at $\mathfrak P$ is *fully ramified* (§32B, p. 60): $e = n$ and $f = 1$. -/
@[kb "omeara1963" "§32B, p. 60 (fully ramified extension)"]
def IsFullyRamifiedAbs (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w) : Prop :=
  ramificationIndexAbs (F := F) w = Module.finrank F E ∧ inertiaDegAbs (F := F) w hw = 1

variable [FiniteDimensional F E] {w : AbsoluteValue E ℝ} (hd : IsDiscreteAbs (w.under F))
  [CompleteSpace (WithAbs (w.under F))] [Finite (residueFieldOf (w.under F) hd.isNonarchimedean)]

/-- **32:3.** Let $E/F$ be a finite extension with spots $\mathfrak P \mid \mathfrak p$ and $F$ a local field at
$\mathfrak p$. Then (1) $E$ is a local field at $\mathfrak P$; (2) $N\mathfrak P = (N\mathfrak p)^{f(\mathfrak P|\mathfrak p)}$;
(3) $|\alpha|_{\mathfrak P} = |N_{E/F}\alpha|_{\mathfrak p}$ for all $\alpha \in E$, both valuations normalized. -/
@[kb "omeara1963" "§32A, 32:3, p. 60"]
theorem isLocal_of_finite :
    ∃ hdw : IsDiscreteAbs w, CompleteSpace (WithAbs w) ∧ Finite (residueFieldOf w hdw.isNonarchimedean) ∧
      Nat.card (residueFieldOf w hdw.isNonarchimedean) =
        Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^
          inertiaDegAbs (F := F) w hdw.isNonarchimedean ∧
      ∀ (w' : AbsoluteValue E ℝ) (v' : AbsoluteValue F ℝ), w'.IsEquiv w → v'.IsEquiv (w.under F) →
        IsNormalizedAbs w' → IsNormalizedAbs v' → ∀ α : E, w' α = v' (Algebra.norm F α) := by
  have hdw : IsDiscreteAbs w := (isDiscreteAbs_iff_under (F := F) w).2 hd
  haveI : CompleteSpace (WithAbs w) := completeSpace_of_under hd
  have hna := hdw.isNonarchimedean
  have h164 := ramificationIndexAbs_mul_inertiaDegAbs_eq (F := F) hdw
  obtain ⟨he0, hf0, -⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) w hna
  letI := residueAlgebra (F := F) w hna
  haveI : Module.Finite (residueFieldOf (w.under F) (isNonarchimedean_under hna))
      (residueFieldOf w hna) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hf0)
  haveI hfin : Finite (residueFieldOf w hna) :=
    Module.finite_of_finite (residueFieldOf (w.under F) (isNonarchimedean_under hna))
  have hcard : Nat.card (residueFieldOf w hna) =
      Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ inertiaDegAbs (F := F) w hna :=
    Module.natCard_eq_pow_finrank
  refine ⟨hdw, inferInstance, hfin, hcard, ?_⟩
  intro w' v' hw' hv' ⟨hnaw', hnew', hgw'⟩ ⟨hnav', hnev', hgv'⟩ α
  haveI : Finite (residueFieldOf w' hnaw') := Nat.finite_of_card_ne_zero (by exact_mod_cast hnew')
  haveI : Finite (residueFieldOf v' hnav') := Nat.finite_of_card_ne_zero (by exact_mod_cast hnev')
  obtain ⟨a, ha, haw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hw'.symm
  obtain ⟨b, hb, hbv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hv'.symm
  have haw' : ∀ x, w' x = w x ^ a := fun x => (congrFun haw x).symm
  have hbv' : ∀ x, v' x = (w.under F) x ^ b := fun x => (congrFun hbv x).symm
  set N := Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) with hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast Finite.one_lt_card
  have hG1 := genAbs_rpow_eq_inv hdw ha haw' hgw'
  have hG2 := genAbs_rpow_eq_inv hd hb hbv' hgv'
  rw [natCard_residueFieldOf_of_isEquiv hw' hnaw' hna, hcard] at hG1
  rw [natCard_residueFieldOf_of_isEquiv hv' hnav' hd.isNonarchimedean] at hG2
  have hgFE := genAbs_under_eq_pow hdw hd
  have hg0 := genAbs_pos hdw
  have hg1 := genAbs_lt_one hdw
  have hL : Real.log (genAbs hdw) < 0 := Real.log_neg hg0 hg1
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlog1 : a * Real.log (genAbs hdw) = - (inertiaDegAbs (F := F) w hna * Real.log N) := by
    have := congrArg Real.log hG1
    rw [Real.log_rpow hg0, Real.log_inv] at this
    push_cast at this
    rw [Real.log_pow] at this
    linarith
  have hlog2 : b * (ramificationIndexAbs (F := F) w * Real.log (genAbs hdw)) = - Real.log N := by
    rw [hgFE] at hG2
    have := congrArg Real.log hG2
    rw [Real.log_rpow (pow_pos hg0 _), Real.log_pow, Real.log_inv] at this
    linarith
  have hab : a = b * (inertiaDegAbs (F := F) w hna * ramificationIndexAbs (F := F) w) := by
    have hLne : Real.log (genAbs hdw) ≠ 0 := hL.ne
    apply mul_right_cancel₀ hLne
    nlinarith
  have hn : (Module.finrank F E : ℝ) = ramificationIndexAbs (F := F) w * inertiaDegAbs (F := F) w hna := by
    exact_mod_cast h164.symm
  have hn0 : (0 : ℝ) < Module.finrank F E := by
    rw [hn]; exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero he0 hf0)
  rw [haw' α, hbv', apply_eq_norm_rpow hd α, ← Real.rpow_mul (by positivity)]
  congr 1
  rw [hab, hn]
  field_simp

section TowerHelpers

variable {H : Type*} [Field H] [Algebra F H]

theorem under_under_eq (u : AbsoluteValue H ℝ) (K : IntermediateField F H) :
    (u.under K).under F = u.under F := by
  ext x; rfl

/-- $e$ is multiplicative in towers. -/
theorem ramificationIndexAbs_tower (u : AbsoluteValue H ℝ) (K : IntermediateField F H) :
    ramificationIndexAbs (F := F) u =
      ramificationIndexAbs (F := F) (u.under K) * ramificationIndexAbs (F := K) u := by
  unfold ramificationIndexAbs
  have hle : absValueGroup (u.under F) ≤ absValueGroup (u.under K) := by
    rw [← under_under_eq u K]; exact absValueGroup_under_le (u.under K)
  rw [under_under_eq, Subgroup.relIndex_mul_relIndex _ _ _ hle (absValueGroup_under_le u)]

/-- $f$ is multiplicative in towers. -/
theorem inertiaDegAbs_tower (u : AbsoluteValue H ℝ) (hu : IsNonarchimedean u) (K : IntermediateField F H) :
    inertiaDegAbs (F := F) u hu =
      inertiaDegAbs (F := F) (u.under K) (fun _ _ => hu _ _) * inertiaDegAbs (F := K) u hu := by
  have hw1 : IsNonarchimedean (u.under K) := fun _ _ => hu _ _
  unfold inertiaDegAbs
  letI A01 := (residueMap (F := F) (u.under K) hw1).toAlgebra
  letI A12 := (residueMap (F := K) u hu).toAlgebra
  letI A02 : Algebra (residueFieldOf ((u.under K).under F) (isNonarchimedean_under hw1))
      (residueFieldOf u hu) :=
    ((residueMap (F := K) u hu).comp (residueMap (F := F) (u.under K) hw1)).toAlgebra
  haveI : IsScalarTower (residueFieldOf ((u.under K).under F) (isNonarchimedean_under hw1))
      (residueFieldOf (u.under K) hw1) (residueFieldOf u hu) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  refine Eq.trans ?_ (Module.finrank_mul_finrank (residueFieldOf ((u.under K).under F) (isNonarchimedean_under hw1))
    (residueFieldOf (u.under K) hw1) (residueFieldOf u hu)).symm
  have hres : ResidueData ((u.under K).under F) (u.under F) (RingHom.id F) :=
    ResidueData.of_isEquiv (by rw [under_under_eq]; exact fun _ _ => Iff.rfl)
  letI A0 := (residueMap (F := F) u hu).toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv (hres.resEquiv (isNonarchimedean_under hw1)
    (isNonarchimedean_under hu)) (RingEquiv.refl _) ?_).symm
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingHom.algebraMap_toAlgebra, hres.resEquiv_mk, residueMap_mk, RingEquiv.refl_apply]
  congr 1

theorem nat_aux {f1 f2 n1 n2 : ℕ} (h1 : f1 ≤ n1) (h2 : f2 ≤ n2) (hp1 : 0 < n1) (hp2 : 0 < n2)
    (b1 : 0 < f1) (b2 : 0 < f2) (h : f1 * f2 = n1 * n2) : f1 = n1 ∧ f2 = n2 := by
  constructor
  · by_contra hne
    have : f1 < n1 := lt_of_le_of_ne h1 hne
    nlinarith [Nat.mul_le_mul_left f1 h2, Nat.mul_lt_mul_of_pos_right this hp2]
  · by_contra hne
    have : f2 < n2 := lt_of_le_of_ne h2 hne
    nlinarith [Nat.mul_le_mul_right f2 h1, Nat.mul_lt_mul_of_pos_left this hp1]

end TowerHelpers

/-- **Towers** (§32B, p. 61): for finite extensions $F \subseteq E \subseteq H$ of local fields, $H/F$ is unramified if
and only if $H/E$ and $E/F$ are; the same holds for fully ramified. Here $E$ is an intermediate field of $H/F$ and
$w$ a valuation of $H$. -/
@[kb "omeara1963" "§32B, p. 61 (unramified and fully ramified in towers)"]
theorem isUnramifiedAbs_tower_iff {H : Type*} [Field H] [Algebra F H] [FiniteDimensional F H]
    {u : AbsoluteValue H ℝ} (hdu : IsDiscreteAbs (u.under F)) [CompleteSpace (WithAbs (u.under F))]
    (K : IntermediateField F H) (hu : IsNonarchimedean u) :
    IsUnramifiedAbs (F := F) u hu ↔
      IsUnramifiedAbs (F := K) u hu ∧ IsUnramifiedAbs (F := F) (u.under K) (by
        exact fun a b => hu _ _) := by
  obtain ⟨he1, hf1, hle1⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) (u.under K)
    (fun a b => hu _ _)
  obtain ⟨he2, hf2, hle2⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := K) u hu
  have hE := ramificationIndexAbs_tower (F := F) u K
  have hI := inertiaDegAbs_tower (F := F) u hu K
  have hD : Module.finrank F H = Module.finrank F K * Module.finrank K H :=
    (Module.finrank_mul_finrank F K H).symm
  unfold IsUnramifiedAbs
  rw [hE, hI, hD]
  have hp1 : 0 < Module.finrank F K := Module.finrank_pos
  have hp2 : 0 < Module.finrank K H := Module.finrank_pos
  have a1 := Nat.pos_of_ne_zero he1
  have a2 := Nat.pos_of_ne_zero he2
  have b1 := Nat.pos_of_ne_zero hf1
  have b2 := Nat.pos_of_ne_zero hf2
  have c1 : inertiaDegAbs (F := F) (u.under K) (fun a b => hu _ _) ≤ Module.finrank F K :=
    le_trans (Nat.le_mul_of_pos_left _ a1) hle1
  have c2 : inertiaDegAbs (F := K) u hu ≤ Module.finrank K H :=
    le_trans (Nat.le_mul_of_pos_left _ a2) hle2
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : ramificationIndexAbs (F := F) (u.under K) = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have e2 : ramificationIndexAbs (F := K) u = 1 := Nat.eq_one_of_mul_eq_one_left h1
    obtain ⟨g1, g2⟩ := nat_aux c1 c2 hp1 hp2 b1 b2 h2
    exact ⟨⟨e2, g2⟩, ⟨e1, g1⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [h1, h3, h2, h4]
    simp

/-- Fully ramified extensions in towers (§32B, p. 61). -/
@[kb "omeara1963" "§32B, p. 61 (unramified and fully ramified in towers)"]
theorem isFullyRamifiedAbs_tower_iff {H : Type*} [Field H] [Algebra F H] [FiniteDimensional F H]
    {u : AbsoluteValue H ℝ} (hdu : IsDiscreteAbs (u.under F)) [CompleteSpace (WithAbs (u.under F))]
    (K : IntermediateField F H) (hu : IsNonarchimedean u) :
    IsFullyRamifiedAbs (F := F) u hu ↔
      IsFullyRamifiedAbs (F := K) u hu ∧ IsFullyRamifiedAbs (F := F) (u.under K) (by
        exact fun a b => hu _ _) := by
  obtain ⟨he1, hf1, hle1⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) (u.under K)
    (fun a b => hu _ _)
  obtain ⟨he2, hf2, hle2⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := K) u hu
  have hE := ramificationIndexAbs_tower (F := F) u K
  have hI := inertiaDegAbs_tower (F := F) u hu K
  have hD : Module.finrank F H = Module.finrank F K * Module.finrank K H :=
    (Module.finrank_mul_finrank F K H).symm
  unfold IsFullyRamifiedAbs
  rw [hE, hI, hD]
  have hp1 : 0 < Module.finrank F K := Module.finrank_pos
  have hp2 : 0 < Module.finrank K H := Module.finrank_pos
  have a1 := Nat.pos_of_ne_zero he1
  have a2 := Nat.pos_of_ne_zero he2
  have b1 := Nat.pos_of_ne_zero hf1
  have b2 := Nat.pos_of_ne_zero hf2
  have c1 : ramificationIndexAbs (F := F) (u.under K) ≤ Module.finrank F K :=
    le_trans (Nat.le_mul_of_pos_right _ b1) hle1
  have c2 : ramificationIndexAbs (F := K) u ≤ Module.finrank K H :=
    le_trans (Nat.le_mul_of_pos_right _ b2) hle2
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : inertiaDegAbs (F := F) (u.under K) (fun a b => hu _ _) = 1 :=
      Nat.eq_one_of_mul_eq_one_right h2
    have e2 : inertiaDegAbs (F := K) u hu = 1 := Nat.eq_one_of_mul_eq_one_left h2
    obtain ⟨g1, g2⟩ := nat_aux c1 c2 hp1 hp2 a1 a2 h1
    exact ⟨⟨g2, e2⟩, ⟨g1, e1⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [h1, h3, h2, h4]
    simp

section ResidueIso

variable {K L : Type*} [Field K] [Field L] {u : AbsoluteValue K ℝ} {u' : AbsoluteValue L ℝ}

/-- The map of integers induced by a ring homomorphism that preserves the valuation. -/
def isoIntMap (hu : IsNonarchimedean u) (hu' : IsNonarchimedean u') (φ : K →+* L)
    (h : ∀ x, u' (φ x) = u x) : integers u hu →+* integers u' hu' :=
  (φ.comp (integers u hu).subtype).codRestrict (integers u' hu') (fun a => by
    show u' (φ a) ≤ 1
    rw [h]; exact a.2)

/-- The map of residue class fields induced by a ring homomorphism that preserves the valuation. -/
noncomputable def isoResidueHom (hu : IsNonarchimedean u) (hu' : IsNonarchimedean u') (φ : K →+* L)
    (h : ∀ x, u' (φ x) = u x) : residueFieldOf u hu →+* residueFieldOf u' hu' :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (isoIntMap hu hu' φ h)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    show u' (φ a) < 1
    rw [h]; exact ha)

theorem isoResidueHom_mk (hu : IsNonarchimedean u) (hu' : IsNonarchimedean u') (φ : K →+* L)
    (h : ∀ x, u' (φ x) = u x) (a : integers u hu) :
    isoResidueHom hu hu' φ h (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (isoIntMap hu hu' φ h a) := rfl

end ResidueIso

theorem prod_mem_unitInterval (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1) : 0 ≤ s.prod ∧ s.prod ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.prod_cons]
    exact ⟨mul_nonneg ha.1 hs.1, by nlinarith [ha.1, ha.2, hs.1, hs.2]⟩

/-- A product of reals in $[0,1]$ equal to $1$ has all factors equal to $1$. -/
theorem eq_one_of_prod_eq_one (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1) (hp : s.prod = 1) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    intro x hx
    have ha := h a (Multiset.mem_cons_self a s)
    have hs : ∀ y ∈ s, 0 ≤ y ∧ y ≤ 1 := fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.prod_cons] at hp
    obtain ⟨hP0, hP1⟩ := prod_mem_unitInterval s hs
    have ha1 : a = 1 := by nlinarith [ha.1, ha.2]
    have hP : s.prod = 1 := by nlinarith [ha.1, ha.2]
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha1
    · exact ih hs hP x hx

theorem mul_le_one_aux {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := by
  nlinarith

/-- A polynomial with integral coefficients takes integral values at integral elements. -/
theorem apply_aeval_le_one {w : AbsoluteValue E ℝ} (hw : IsNonarchimedean w) (p : F[X])
    (hp : ∀ i, w (algebraMap F E (p.coeff i)) ≤ 1) {α : E} (hα : w α ≤ 1) : w (aeval α p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply sum_le_of_nonarch hw _ _ zero_le_one
  intro i _
  rw [Algebra.smul_def, map_mul, map_pow]
  exact mul_le_one_aux (hp i) (by positivity) (pow_le_one₀ (w.nonneg _) hα)

/-- The derivative of a polynomial with integral coefficients has integral coefficients. -/
theorem coeff_derivative_le_one {w : AbsoluteValue E ℝ} (hw : IsNonarchimedean w) (p : F[X])
    (hp : ∀ i, w (algebraMap F E (p.coeff i)) ≤ 1) (i : ℕ) :
    w (algebraMap F E ((derivative p).coeff i)) ≤ 1 := by
  rw [coeff_derivative, map_mul, map_mul]
  refine mul_le_one_aux (hp _) (w.nonneg _) ?_
  have : (algebraMap F E ((i : F) + 1)) = ((i + 1 : ℕ) : E) := by simp
  rw [this]
  exact hw.apply_natCast_le_one (by simp) (map_one _)

/-- **Core of 32:6**: for $E = F(\alpha)$ with minimal polynomial $g$ of $\alpha$ integral and $g'(\alpha)$ a unit,
$E/F$ is unramified and $\bar E = \bar F(\bar\alpha)$. -/
theorem unramified_core (hd' : IsDiscreteAbs (w.under F)) {α : E} (hα : F⟮α⟯ = ⊤) (hα1 : w α ≤ 1)
    (hgint : ∀ i, w.under F ((minpoly F α).coeff i) ≤ 1)
    (hder : w (aeval α (derivative (minpoly F α))) = 1) :
    IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd'.isNonarchimedean) ∧
      letI := (residueMap (F := F) w (isNonarchimedean_of_under hd'.isNonarchimedean)).toAlgebra
      Algebra.adjoin (residueFieldOf (w.under F) hd'.isNonarchimedean)
        {Ideal.Quotient.mk (maximalIdealOf w (isNonarchimedean_of_under hd'.isNonarchimedean))
          ⟨α, hα1⟩} = ⊤ := by
  classical
  have hv := hd'.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  set g := minpoly F α with hg
  have hgmonic : g.Monic := minpoly.monic hint
  have hn : g.natDegree = Module.finrank F E := by
    have h1 := IntermediateField.adjoin.finrank hint
    have h2 : Module.finrank F F⟮α⟯ = Module.finrank F E := by
      rw [hα]; exact IntermediateField.finrank_top'
    rw [← h1, h2]
  have hg'ne : derivative g ≠ 0 := by
    intro h0
    rw [h0] at hder
    simp at hder
  have hsep : g.Separable := (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)).2 hg'ne
  -- the splitting field of g
  let M := g.SplittingField
  obtain ⟨W, hW, -⟩ := exists_ext (F := F) hd' M
  have hWna : IsNonarchimedean W := isNonarchimedean_of_ext hv W hW
  -- power basis of E
  let pb : PowerBasis F E := (IntermediateField.adjoin.powerBasis hint).map
    ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  have hpbgen : pb.gen = α := by simp [pb]
  have hroot_lift : ∀ r ∈ g.rootSet M, ∃ φ : E →ₐ[F] M, φ α = r ∧ ∀ x, W (φ x) = w x := by
    intro r hr
    have hy : aeval r (minpoly F pb.gen) = 0 := by
      rw [hpbgen]; exact (mem_rootSet.1 hr).2
    refine ⟨pb.lift r hy, by rw [← hpbgen]; exact pb.lift_gen r hy, ?_⟩
    have := ext_unique (F := F) hd' (L := E) (W.comp (pb.lift r hy).toRingHom.injective) w
      (fun x => by
        show W ((pb.lift r hy) (algebraMap F E x)) = _
        rw [AlgHom.commutes]; exact hW x) (fun x => rfl)
    intro x
    exact congrArg (fun A : AbsoluteValue E ℝ => A x) this
  have hrint : ∀ r ∈ g.rootSet M, W r ≤ 1 := by
    intro r hr
    obtain ⟨φ, h1, h2⟩ := hroot_lift r hr
    rw [← h1, h2]; exact hα1
  -- distinct roots have distinct residues
  have hdist : ∀ r ∈ g.rootSet M, ∀ r' ∈ g.rootSet M, r ≠ r' → W (r - r') = 1 := by
    intro r hr r' hr' hne
    obtain ⟨φ, h1, h2⟩ := hroot_lift r hr
    have hgr : W (aeval r (derivative g)) = 1 := by
      rw [← h1, aeval_algHom_apply, h2]; exact hder
    have hsplit : (g.map (algebraMap F M)).Splits := IsSplittingField.splits M g
    have hmem : ∀ x ∈ g.rootSet M, x ∈ (g.map (algebraMap F M)).roots := by
      intro x hx
      rw [mem_rootSet] at hx
      rw [mem_roots (hgmonic.map _).ne_zero]
      simpa [IsRoot, eval_map_algebraMap] using hx.2
    have hderiv := hsplit.eval_root_derivative (hgmonic.map (algebraMap F M)) (hmem r hr)
    rw [derivative_map, eval_map_algebraMap] at hderiv
    have hprod : (((g.map (algebraMap F M)).roots.erase r).map (fun a => W (r - a))).prod = 1 := by
      have := congrArg W hderiv
      rw [map_multiset_prod, Multiset.map_map, hgr] at this
      simpa [Function.comp_def] using this.symm
    have hrootint : ∀ a ∈ (g.map (algebraMap F M)).roots, W a ≤ 1 := by
      intro a ha
      apply hrint
      rw [mem_rootSet]
      rw [mem_roots (hgmonic.map _).ne_zero] at ha
      exact ⟨hgmonic.ne_zero, by simpa [IsRoot, eval_map_algebraMap] using ha⟩
    have hall := eq_one_of_prod_eq_one _ (by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
      have ha' := hrootint a (Multiset.mem_of_mem_erase ha)
      have hr1 := hrint r hr
      refine ⟨W.nonneg _, ?_⟩
      have := hWna r (-a)
      rw [← sub_eq_add_neg, map_neg_eq_map] at this
      exact this.trans (max_le hr1 ha')) hprod
    apply hall
    refine Multiset.mem_map.2 ⟨r', ?_, rfl⟩
    rw [Multiset.mem_erase_of_ne hne.symm]
    exact hmem r' hr'
  -- residue fields
  obtain ⟨he0, hf0, hle⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) w hw
  letI := residueAlgebra (F := F) w hw
  haveI : Module.Finite (residueFieldOf (w.under F) hv) (residueFieldOf w hw) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hf0)
  set ᾱ : residueFieldOf w hw := Ideal.Quotient.mk _ ⟨α, hα1⟩ with hᾱ
  set pbar := minpoly (residueFieldOf (w.under F) hv) ᾱ with hpbar
  have hpbardeg : pbar.natDegree ≤ inertiaDegAbs (F := F) w hw := minpoly.natDegree_le ᾱ
  have hι : ∀ x, W (algebraMap F M x) = (w.under F) x := hW
  let ιM : residueFieldOf (w.under F) hv →+* residueFieldOf W hWna :=
    isoResidueHom hv hWna (algebraMap F M) hι
  let resid : M → residueFieldOf W hWna := fun r =>
    if h : W r ≤ 1 then Ideal.Quotient.mk _ ⟨r, h⟩ else 0
  have hinj : Set.InjOn resid (g.rootSet M) := by
    intro r hr r' hr' heq
    by_contra hne
    have h1 := hdist r hr r' hr' hne
    simp only [resid, dif_pos (hrint r hr), dif_pos (hrint r' hr')] at heq
    rw [Ideal.Quotient.eq] at heq
    have : W (r - r') < 1 := heq
    linarith
  have hrootres : ∀ r ∈ g.rootSet M, (pbar.map ιM).IsRoot (resid r) := by
    intro r hr
    obtain ⟨φ, h1, h2⟩ := hroot_lift r hr
    have hres : resid r = isoResidueHom hw hWna φ.toRingHom h2 ᾱ := by
      simp only [resid, dif_pos (hrint r hr)]
      rw [hᾱ, isoResidueHom_mk]
      congr 1
      exact Subtype.ext h1.symm
    have hcomp : (isoResidueHom hw hWna φ.toRingHom h2).comp (residueMap (F := F) w hw) = ιM := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.comp_apply, residueMap_mk, isoResidueHom_mk]
      show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
      exact Subtype.ext (φ.commutes _)
    rw [IsRoot, eval_map, hres]
    have h3 : pbar.eval₂ (residueMap (F := F) w hw) ᾱ = 0 := minpoly.aeval _ ᾱ
    have h4 := Polynomial.hom_eval₂ pbar (residueMap (F := F) w hw) (isoResidueHom hw hWna φ.toRingHom h2) ᾱ
    rw [h3, hcomp, map_zero] at h4
    exact h4.symm
  have hpint : IsIntegral (residueFieldOf (w.under F) hv) ᾱ := IsIntegral.of_finite _ ᾱ
  have hmain : g.natDegree ≤ pbar.natDegree := by
    have hsplit : (g.map (algebraMap F M)).Splits := IsSplittingField.splits M g
    have hcardroots : Fintype.card (g.rootSet M) = g.natDegree := card_rootSet_eq_natDegree hsep hsplit
    set S : Finset (residueFieldOf W hWna) := (g.rootSet M).toFinset.image resid with hS
    have hSc : S.card = g.natDegree := by
      rw [hS, Finset.card_image_of_injOn (by simpa using hinj), Set.toFinset_card]; exact hcardroots
    have hpne : pbar.map ιM ≠ 0 :=
      (Polynomial.map_ne_zero_iff ιM.injective).2 (minpoly.ne_zero hpint)
    have hsub : S ⊆ (pbar.map ιM).roots.toFinset := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      rw [Multiset.mem_toFinset, mem_roots hpne]
      exact hrootres r (by simpa using hr)
    calc g.natDegree = S.card := hSc.symm
      _ ≤ (pbar.map ιM).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (pbar.map ιM).roots := Multiset.toFinset_card_le _
      _ ≤ (pbar.map ιM).natDegree := card_roots' _
      _ = pbar.natDegree := natDegree_map _
  have hfn : inertiaDegAbs (F := F) w hw = Module.finrank F E := by
    have h1 : g.natDegree ≤ inertiaDegAbs (F := F) w hw := hmain.trans hpbardeg
    have h2 : inertiaDegAbs (F := F) w hw ≤ ramificationIndexAbs (F := F) w * inertiaDegAbs (F := F) w hw :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he0)
    omega
  have he1 : ramificationIndexAbs (F := F) w = 1 := by
    have hf1 : 0 < inertiaDegAbs (F := F) w hw := Nat.pos_of_ne_zero hf0
    rw [hfn] at hle hf1
    have := Nat.pos_of_ne_zero he0
    nlinarith
  refine ⟨⟨he1, hfn⟩, ?_⟩
  have hdeg : pbar.natDegree = inertiaDegAbs (F := F) w hw := by
    have h1 : g.natDegree ≤ inertiaDegAbs (F := F) w hw := hmain.trans hpbardeg
    omega
  have hfr : Module.finrank (residueFieldOf (w.under F) hv) (Algebra.adjoin (residueFieldOf (w.under F) hv) {ᾱ}) =
      Module.finrank (residueFieldOf (w.under F) hv) (residueFieldOf w hw) := by
    rw [(Algebra.adjoin.powerBasis' hpint).finrank, Algebra.adjoin.powerBasis'_dim]
    exact hdeg
  exact Algebra.toSubmodule_eq_top.1 (Submodule.eq_top_of_finrank_eq
    ((Subalgebra.finrank_toSubmodule _).trans hfr))

/-- **32:6.** Let $E/F$ be a finite extension of local fields with $E = F(\alpha)$, where $\alpha$ is a root of a monic
polynomial $f$ with integral coefficients over $F$ such that $f'(\alpha)$ is a unit. Then $\alpha$ is integral, $E/F$ is
unramified, and the residue class field of $E$ is $\bar F(\bar\alpha)$. -/
@[kb "omeara1963" "§32B, 32:6, p. 61"]
theorem isUnramifiedAbs_of_derivative {α : E} (hα : F⟮α⟯ = ⊤) {f : F[X]} (hf : f.Monic)
    (hint : ∀ i, w.under F (f.coeff i) ≤ 1) (hroot : aeval α f = 0) (hder : w (aeval α (derivative f)) = 1) :
    ∃ hα1 : w α ≤ 1,
      IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) ∧
      letI := (residueMap (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)).toAlgebra
      Algebra.adjoin (residueFieldOf (w.under F) hd.isNonarchimedean)
        {Ideal.Quotient.mk (maximalIdealOf w (isNonarchimedean_of_under hd.isNonarchimedean)) ⟨α, hα1⟩} = ⊤ := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  have hint' : ∀ i, w (algebraMap F E (f.coeff i)) ≤ 1 := hint
  have hα1 : w α ≤ 1 := apply_le_one_of_aeval_eq_zero hw hf hint' hroot
  have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hgmonic : (minpoly F α).Monic := minpoly.monic hαint
  have hdvd : minpoly F α ∣ f := minpoly.dvd F α hroot
  have hgint : ∀ i, w.under F ((minpoly F α).coeff i) ≤ 1 := monic_factor_integral (w.under F) hv hf hgmonic hdvd hint
  obtain ⟨h, hh⟩ := hdvd
  have hhmonic : h.Monic := Monic.of_mul_monic_left hgmonic (hh ▸ hf)
  have hhint : ∀ i, w.under F (h.coeff i) ≤ 1 :=
    monic_factor_integral (w.under F) hv hf hhmonic ⟨minpoly F α, by rw [hh, mul_comm]⟩ hint
  have hgint' : ∀ i, w (algebraMap F E ((minpoly F α).coeff i)) ≤ 1 := hgint
  have hhint' : ∀ i, w (algebraMap F E (h.coeff i)) ≤ 1 := hhint
  have h1 : w (aeval α (derivative (minpoly F α))) ≤ 1 :=
    apply_aeval_le_one hw _ (coeff_derivative_le_one hw _ hgint') hα1
  have h2 : w (aeval α h) ≤ 1 := apply_aeval_le_one hw h hhint' hα1
  have h3 : aeval α (derivative f) = aeval α (derivative (minpoly F α)) * aeval α h := by
    rw [hh, derivative_mul]
    simp [minpoly.aeval]
  rw [h3, map_mul] at hder
  have hder' : w (aeval α (derivative (minpoly F α))) = 1 := by
    have hn0 := w.nonneg (aeval α (derivative (minpoly F α)))
    have hn1 := w.nonneg (aeval α h)
    nlinarith
  exact ⟨hα1, unramified_core hd hα hα1 hgint hder'⟩

/-- **32:6a.** If $m$ is a unit of $F$ and $\zeta$ an $m$-th root of unity, then the local field $F(\zeta)$ is
unramified over $F$ (here $E = F(\zeta)$). -/
@[kb "omeara1963" "§32B, 32:6a, p. 61"]
theorem isUnramifiedAbs_adjoin_root_of_unity {m : ℕ} (hm : w.under F (m : F) = 1) {ζ : E} (hζ : ζ ^ m = 1)
    (hE : F⟮ζ⟯ = ⊤) : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hwm : w (m : E) = 1 := by
    have : w (m : E) = w.under F (m : F) := by rw [under_apply_eq]; simp
    rw [this, hm]
  have hwζ : w ζ = 1 := by
    have : w ζ ^ m = 1 := by rw [← map_pow, hζ, map_one]
    exact (pow_eq_one_iff_of_nonneg (w.nonneg _) hm0).1 this
  have hf : (X ^ m - C (1 : F) : F[X]).Monic := monic_X_pow_sub_C 1 hm0
  have hint : ∀ i, w.under F ((X ^ m - C (1 : F) : F[X]).coeff i) ≤ 1 := by
    intro i
    rw [coeff_sub, coeff_X_pow, coeff_C]
    by_cases h1 : i = m <;> by_cases h2 : i = 0 <;> simp [h1, h2, hm0, hm0.symm]
  have hroot : aeval ζ (X ^ m - C (1 : F) : F[X]) = 0 := by simp [hζ]
  have hder : w (aeval ζ (derivative (X ^ m - C (1 : F) : F[X]))) = 1 := by
    simp [derivative_X_pow, hwm, hwζ]
  exact (isUnramifiedAbs_of_derivative hd hE hf hint hroot hder).2.1

section HenselianBridge

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

theorem isLocalRing_integers (hv : IsNonarchimedean v) : IsLocalRing (integers v hv) := by
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add (fun a b hab => ?_)
  have h1 : v ((a : K) + (b : K)) = 1 := by
    rw [← Subring.coe_add]; exact (isUnit_integers_iff hv _).1 hab
  have h2 := hv (a : K) (b : K)
  rw [h1] at h2
  have ha : v (a : K) ≤ 1 := a.2
  have hb : v (b : K) ≤ 1 := b.2
  rcases le_max_iff.1 h2 with h | h
  · exact Or.inl ((isUnit_integers_iff hv a).2 (le_antisymm ha h))
  · exact Or.inr ((isUnit_integers_iff hv b).2 (le_antisymm hb h))

theorem maximalIdeal_integers (hv : IsNonarchimedean v) :
    letI := isLocalRing_integers hv
    IsLocalRing.maximalIdeal (integers v hv) = maximalIdealOf v hv := by
  haveI := isLocalRing_integers hv
  exact (IsLocalRing.eq_maximalIdeal (maximalIdealOf_isMaximal v hv)).symm

theorem mem_pow_maximalIdealOf_iff (hd : IsDiscreteAbs v) (n : ℕ) (a : integers v hd.isNonarchimedean) :
    a ∈ (maximalIdealOf v hd.isNonarchimedean) ^ n ↔ v (a : K) ≤ genAbs hd ^ n := by
  obtain ⟨π, hπ0, hπ⟩ := exists_apply_eq_genAbs hd
  have hprime : IsPrimeElt v hd.isNonarchimedean π := (isPrimeElt_iff_apply_eq hd).2 ⟨hπ0, hπ⟩
  rw [maximalIdealOf_eq_span hd hprime, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hg0 := genAbs_pos hd
  have hπle : v π ≤ 1 := hprime.1
  constructor
  · rintro ⟨c, hc⟩
    have : (a : K) = π ^ n * (c : K) := by
      have := congrArg (fun y : integers v hd.isNonarchimedean => (y : K)) hc
      simpa using this
    rw [this, map_mul, map_pow, hπ]
    have hc1 : v (c : K) ≤ 1 := c.2
    calc genAbs hd ^ n * v (c : K) ≤ genAbs hd ^ n * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    by_cases ha0 : (a : K) = 0
    · have : a = 0 := Subtype.ext ha0
      rw [this]; exact dvd_zero _
    · have hpn : (π ^ n : K) ≠ 0 := pow_ne_zero _ hπ0
      have hle : v ((a : K) / π ^ n) ≤ 1 := by
        rw [map_div₀, map_pow, hπ, div_le_one (pow_pos hg0 n)]
        exact h
      refine ⟨⟨(a : K) / π ^ n, hle⟩, Subtype.ext ?_⟩
      show (a : K) = π ^ n * ((a : K) / π ^ n)
      field_simp

theorem isAdicComplete_integers (hd : IsDiscreteAbs v) [CompleteSpace (WithAbs v)] :
    letI := isLocalRing_integers hd.isNonarchimedean
    IsAdicComplete (IsLocalRing.maximalIdeal (integers v hd.isNonarchimedean))
      (integers v hd.isNonarchimedean) := by
  letI := isLocalRing_integers hd.isNonarchimedean
  have hv := hd.isNonarchimedean
  have hmax := maximalIdeal_integers hv
  have hg0 := genAbs_pos hd
  have hg1 := genAbs_lt_one hd
  have key : ∀ (n : ℕ) (a : integers v hv),
      a ∈ (IsLocalRing.maximalIdeal (integers v hv)) ^ n • (⊤ : Submodule (integers v hv) (integers v hv)) ↔
        v (a : K) ≤ genAbs hd ^ n := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, hmax]
    exact mem_pow_maximalIdealOf_iff hd n a
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n : ℕ, v (x : K) ≤ genAbs hd ^ n := fun n => by
      have := hx n
      rw [SModEq.sub_mem, sub_zero, key] at this
      exact this
    by_contra hne
    have hxK : (x : K) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (v.pos hxK) hg1
    exact absurd (hx' n) (not_le.2 hn)
  · intro f hf
    set u : ℕ → WithAbs v := fun k => WithAbs.toAbs v ((f k : integers v hv) : K) with hu
    have hd' : ∀ a b, a ≤ b → v ((f a : K) - (f b : K)) ≤ genAbs hd ^ a := by
      intro a b hab
      have := hf hab
      rw [SModEq.sub_mem, key] at this
      exact this
    have hc : CauchySeq u := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hg1
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm]
      show v ((f n : K) - (f N : K)) < ε
      rw [← AbsoluteValue.map_neg v, neg_sub]
      exact lt_of_le_of_lt (hd' N n hn) hN
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hlim : ∀ N : ℕ, v (WithAbs.ofAbs (u N - L)) ≤ genAbs hd ^ N := by
      intro N
      have h1 : Filter.Tendsto (fun j => ‖u N - u j‖) Filter.atTop (nhds ‖u N - L‖) :=
        (tendsto_const_nhds.sub hL).norm
      refine le_of_tendsto h1 ?_
      filter_upwards [Filter.eventually_ge_atTop N] with j hj
      exact hd' N j hj
    have hL1 : v (WithAbs.ofAbs L) ≤ 1 := by
      have h0 := hlim 0
      have hu0 : v ((f 0 : integers v hv) : K) ≤ 1 := (f 0).2
      have : WithAbs.ofAbs L = ((f 0 : integers v hv) : K) - WithAbs.ofAbs (u 0 - L) := by
        simp [hu]
      rw [this, sub_eq_add_neg]
      refine (hv _ _).trans (max_le hu0 ?_)
      rw [AbsoluteValue.map_neg]
      simpa using h0
    refine ⟨⟨WithAbs.ofAbs L, hL1⟩, fun N => ?_⟩
    rw [SModEq.sub_mem, key]
    show v ((f N : K) - WithAbs.ofAbs L) ≤ _
    have := hlim N
    simpa [hu] using this

theorem henselianLocalRing_integers (hd : IsDiscreteAbs v) [CompleteSpace (WithAbs v)] :
    HenselianLocalRing (integers v hd.isNonarchimedean) := by
  letI := isLocalRing_integers hd.isNonarchimedean
  haveI := isAdicComplete_integers hd
  exact { toIsLocalRing := inferInstance
          is_henselian := fun f hf a₀ h1 h2 =>
            HenselianRing.is_henselian f hf a₀ h1 (h2.map _) }

section LocalFieldFacts

variable [CompleteSpace (WithAbs v)]

theorem natCard_residueField_integers (hd : IsDiscreteAbs v) :
    letI := isLocalRing_integers hd.isNonarchimedean
    Nat.card (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) =
      Nat.card (residueFieldOf v hd.isNonarchimedean) := by
  letI := isLocalRing_integers hd.isNonarchimedean
  exact Nat.card_congr (Ideal.quotEquivOfEq (maximalIdeal_integers hd.isNonarchimedean)).toEquiv

/-- **32:8 for a local field**, in terms of the field. -/
theorem exists_isPrimitiveRoot_localField (hd : IsDiscreteAbs v)
    [Finite (residueFieldOf v hd.isNonarchimedean)] :
    ∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (residueFieldOf v hd.isNonarchimedean) - 1) := by
  letI := isLocalRing_integers hd.isNonarchimedean
  haveI := henselianLocalRing_integers hd
  have hcard := natCard_residueField_integers hd
  haveI : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) := by
    have : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) :=
      Finite.of_equiv _ (Ideal.quotEquivOfEq (maximalIdeal_integers hd.isNonarchimedean)).symm.toEquiv
    exact this
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_residueCard_sub_one (integers v hd.isNonarchimedean)
  have hrc : residueCard (integers v hd.isNonarchimedean) =
      Nat.card (residueFieldOf v hd.isNonarchimedean) := hcard
  rw [hrc] at hζ
  exact ⟨(ζ : K), hζ.map_of_injective (f := (integers v hd.isNonarchimedean).subtype.toMonoidHom)
    Subtype.val_injective⟩

theorem dvd_card_sub_one_of_isPrimitiveRoot (hd : IsDiscreteAbs v)
    [Finite (residueFieldOf v hd.isNonarchimedean)] {y : K} {n : ℕ} (hy : IsPrimitiveRoot y n)
    (hn : v (n : K) = 1) : n ∣ Nat.card (residueFieldOf v hd.isNonarchimedean) - 1 := by
  letI := isLocalRing_integers hd.isNonarchimedean
  haveI := henselianLocalRing_integers hd
  have hcard := natCard_residueField_integers hd
  haveI : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) := by
    have : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) :=
      Finite.of_equiv _ (Ideal.quotEquivOfEq (maximalIdeal_integers hd.isNonarchimedean)).symm.toEquiv
    exact this
  have hrc : residueCard (integers v hd.isNonarchimedean) =
      Nat.card (residueFieldOf v hd.isNonarchimedean) := hcard
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hy1 : v y = 1 := by
    have : v y ^ n = 1 := by rw [← map_pow, hy.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (v.nonneg _) hn0).1 this
  have hyO : y ∈ integers v hd.isNonarchimedean := hy1.le
  have hyP : IsPrimitiveRoot (⟨y, hyO⟩ : integers v hd.isNonarchimedean) n := by
    refine ⟨Subtype.ext ?_, fun l hl => hy.dvd_of_pow_eq_one l ?_⟩
    · simpa using hy.pow_eq_one
    · simpa using congrArg (fun z : integers v hd.isNonarchimedean => (z : K)) hl
  have hnu : IsUnit ((n : ℕ) : integers v hd.isNonarchimedean) := by
    rw [isUnit_integers_iff]
    simpa using hn
  have := (rootsOfUnity_residueCard_sub_one (integers v hd.isNonarchimedean)).2 _ n hyP hnu
  rwa [hrc] at this

/-- **32:8a (injectivity)**: two `(N-1)`-st roots of unity congruent modulo the maximal ideal are equal. -/
theorem eq_of_rootsOfUnity_of_apply_sub_lt (hd : IsDiscreteAbs v)
    [Finite (residueFieldOf v hd.isNonarchimedean)] {y₁ y₂ : K}
    (h₁ : y₁ ^ (Nat.card (residueFieldOf v hd.isNonarchimedean) - 1) = 1)
    (h₂ : y₂ ^ (Nat.card (residueFieldOf v hd.isNonarchimedean) - 1) = 1) (h : v (y₁ - y₂) < 1) :
    y₁ = y₂ := by
  letI := isLocalRing_integers hd.isNonarchimedean
  haveI := henselianLocalRing_integers hd
  have hcard := natCard_residueField_integers hd
  haveI : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) := by
    have : Finite (IsLocalRing.ResidueField (integers v hd.isNonarchimedean)) :=
      Finite.of_equiv _ (Ideal.quotEquivOfEq (maximalIdeal_integers hd.isNonarchimedean)).symm.toEquiv
    exact this
  have hrc : residueCard (integers v hd.isNonarchimedean) =
      Nat.card (residueFieldOf v hd.isNonarchimedean) := hcard
  rw [← hrc] at h₁ h₂
  have hN : 0 < residueCard (integers v hd.isNonarchimedean) - 1 := by
    have := residueCard_ge_two (integers v hd.isNonarchimedean); omega
  have hv1 : ∀ y : K, y ^ (residueCard (integers v hd.isNonarchimedean) - 1) = 1 → v y ≤ 1 := by
    intro y hy
    have : v y ^ (residueCard (integers v hd.isNonarchimedean) - 1) = 1 := by
      rw [← map_pow, hy, map_one]
    exact ((pow_eq_one_iff_of_nonneg (v.nonneg _) hN.ne').1 this).le
  have hy1 : v y₁ ≤ 1 := hv1 _ h₁
  have hy2 : v y₂ ≤ 1 := hv1 _ h₂
  have hbij := bijOn_residue_teichmuller (integers v hd.isNonarchimedean)
  have hmem : (⟨y₁, hy1⟩ - ⟨y₂, hy2⟩ : integers v hd.isNonarchimedean) ∈
      IsLocalRing.maximalIdeal (integers v hd.isNonarchimedean) := by
    rw [maximalIdeal_integers hd.isNonarchimedean]
    exact h
  have hres : IsLocalRing.residue (integers v hd.isNonarchimedean) ⟨y₁, hy1⟩ =
      IsLocalRing.residue (integers v hd.isNonarchimedean) ⟨y₂, hy2⟩ := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hmem
  have := hbij.injOn (x₁ := (⟨y₁, hy1⟩ : integers v hd.isNonarchimedean))
    (x₂ := ⟨y₂, hy2⟩) (Or.inr (Subtype.ext (by simpa using h₁)) : _) (Or.inr (Subtype.ext (by simpa using h₂)) : _) hres
  exact congrArg Subtype.val this

end LocalFieldFacts

end HenselianBridge

section RootsHelpers

theorem exists_isPrimitiveRoot_of_splits {m : ℕ} (hm0 : m ≠ 0) (hm : (m : F) ≠ 0)
    (hs : Splits ((X ^ m - C (1 : F)).map (algebraMap F E))) : ∃ ζ : E, IsPrimitiveRoot ζ m := by
  haveI : NeZero m := ⟨hm0⟩
  rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
  have hsep : ((X ^ m - C (1 : F)).map (algebraMap F E)).Separable :=
    (separable_X_pow_sub_C (1 : F) hm one_ne_zero).map
  have hmap : (X ^ m - C (1 : F)).map (algebraMap F E) = (X : E[X]) ^ m - C 1 := by simp
  rw [hmap] at hs hsep
  have hcard : (nthRoots m (1 : E)).card = m := by
    have := splits_iff_card_roots.1 hs
    rw [natDegree_X_pow_sub_C] at this
    exact this
  have hnd : (nthRoots m (1 : E)).Nodup := nodup_roots hsep
  classical
  rw [Nat.card_congr (rootsOfUnityEquivNthRoots E m),
    Nat.card_congr (Equiv.subtypeEquivRight (q := fun x => x ∈ (nthRoots m (1 : E)).toFinset) (by simp)),
    Nat.card_eq_fintype_card, Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard]

end RootsHelpers

section FiniteFieldHelpers

theorem card_le_of_adjoin_pow_eq {k L : Type*} [Field k] [Field L] [Fintype k] [Fintype L] [Algebra k L]
    {ζ : L} (hζ : Algebra.adjoin k {ζ} = ⊤) (n : ℕ) (hn : 0 < n)
    (hpow : ζ ^ (Fintype.card k ^ n) = ζ) :
    Fintype.card L ≤ Fintype.card k ^ n := by
  obtain ⟨p, hpk, r, hp, hr⟩ := FiniteField.card' k
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have hall : ∀ x : L, x ^ (Fintype.card k ^ n) = x := by
    intro x
    have hx : x ∈ Algebra.adjoin k {ζ} := by rw [hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hpow
    | algebraMap a =>
        rw [← map_pow]
        congr 1
        exact FiniteField.pow_card_pow n a
    | add x y _ _ hx hy =>
        rw [hr, ← pow_mul, add_pow_char_pow, pow_mul, ← hr, hx, hy]
    | mul x y _ _ hx hy => rw [mul_pow, hx, hy]
  classical
  have hgt : 1 < Fintype.card k ^ n :=
    Nat.one_lt_pow hn.ne' Fintype.one_lt_card
  have hsub : (Finset.univ : Finset L) ⊆ ((X ^ (Fintype.card k ^ n) - X : L[X]).roots.toFinset) := by
    intro x _
    rw [Multiset.mem_toFinset, mem_roots]
    · simp [hall x]
    · intro h0
      have := congrArg natDegree h0
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hgt] at this
      simp at this
  calc Fintype.card L = (Finset.univ : Finset L).card := Finset.card_univ.symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ Multiset.card (X ^ (Fintype.card k ^ n) - X : L[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ (Fintype.card k ^ n) - X : L[X]).natDegree := card_roots' _
    _ = _ := FiniteField.X_pow_card_sub_X_natDegree_eq _ hgt

end FiniteFieldHelpers

section ValueHelpers

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

theorem apply_natCast_card_lt_one (hv : IsNonarchimedean v) [Finite (residueFieldOf v hv)] :
    v ((Nat.card (residueFieldOf v hv) : ℕ) : K) < 1 := by
  classical
  haveI : Fintype (residueFieldOf v hv) := Fintype.ofFinite _
  have h0 : (Ideal.Quotient.mk (maximalIdealOf v hv)) ((Nat.card (residueFieldOf v hv) : ℕ) : integers v hv) = 0 := by
    rw [map_natCast, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  have : v (((Nat.card (residueFieldOf v hv) : ℕ) : integers v hv) : K) < 1 := h0
  simpa using this

theorem apply_natCast_card_pow_sub_one (hv : IsNonarchimedean v) [Finite (residueFieldOf v hv)] {n : ℕ}
    (hn : 0 < n) : v (((Nat.card (residueFieldOf v hv) ^ n - 1 : ℕ) : K)) = 1 := by
  have h2 : 2 ≤ Nat.card (residueFieldOf v hv) := Finite.one_lt_card
  have h1 : 1 ≤ Nat.card (residueFieldOf v hv) ^ n := Nat.one_le_pow _ _ (by omega)
  have hlt : v (((Nat.card (residueFieldOf v hv) ^ n : ℕ) : K)) < 1 := by
    rw [Nat.cast_pow, map_pow]
    exact pow_lt_one₀ (v.nonneg _) (apply_natCast_card_lt_one hv) hn.ne'
  rw [Nat.cast_sub h1, Nat.cast_one]
  set N : K := ((Nat.card (residueFieldOf v hv) ^ n : ℕ) : K) with hN
  apply le_antisymm
  · rw [sub_eq_add_neg]
    refine (hv _ _).trans ?_
    rw [map_neg_eq_map, map_one]
    exact max_le hlt.le le_rfl
  · have h3 : (1 : K) = N + -(N - 1) := by ring
    have h4 : v (1 : K) ≤ max (v N) (v (-(N - 1))) := by
      conv_lhs => rw [h3]
      exact hv _ _
    rw [map_one, map_neg_eq_map] at h4
    rcases le_max_iff.1 h4 with h | h
    · exact absurd h (not_le.2 hlt)
    · exact h

end ValueHelpers

theorem unramified_adjoin_root_of_unity_aux {m : ℕ} (hm : w.under F (m : F) = 1) {ζ : E} (hζ : ζ ^ m = 1)
    (hE : F⟮ζ⟯ = ⊤) :
    ∃ hα1 : w ζ ≤ 1, IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) ∧
      letI := (residueMap (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)).toAlgebra
      Algebra.adjoin (residueFieldOf (w.under F) hd.isNonarchimedean)
        {Ideal.Quotient.mk (maximalIdealOf w (isNonarchimedean_of_under hd.isNonarchimedean))
          ⟨ζ, hα1⟩} = ⊤ := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hwm : w (m : E) = 1 := by
    have : w (m : E) = w.under F (m : F) := by rw [under_apply_eq]; simp
    rw [this, hm]
  have hwζ : w ζ = 1 := by
    have : w ζ ^ m = 1 := by rw [← map_pow, hζ, map_one]
    exact (pow_eq_one_iff_of_nonneg (w.nonneg _) hm0).1 this
  have hf : (X ^ m - C (1 : F) : F[X]).Monic := monic_X_pow_sub_C 1 hm0
  have hint : ∀ i, w.under F ((X ^ m - C (1 : F) : F[X]).coeff i) ≤ 1 := by
    intro i
    rw [coeff_sub, coeff_X_pow, coeff_C]
    by_cases h1 : i = m <;> by_cases h2 : i = 0 <;> simp [h1, h2, hm0, hm0.symm]
  have hroot : aeval ζ (X ^ m - C (1 : F) : F[X]) = 0 := by simp [hζ]
  have hder : w (aeval ζ (derivative (X ^ m - C (1 : F) : F[X]))) = 1 := by
    simp [derivative_X_pow, hwm, hwζ]
  exact isUnramifiedAbs_of_derivative hd hE hf hint hroot hder

/-- A primitive $(N\mathfrak p^n - 1)$-st root of unity in $E$ forces $f \ge n$ (32:8 for $E$). -/
theorem le_inertiaDegAbs_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ n - 1)) :
    n ≤ inertiaDegAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  obtain ⟨hdw, hc, hfin, hcard, -⟩ := isLocal_of_finite hd
  haveI := hc
  haveI := hfin
  set q := Nat.card (residueFieldOf (w.under F) hv) with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hm : w (((q ^ n - 1 : ℕ)) : E) = 1 := by
    have : w (((q ^ n - 1 : ℕ)) : E) = w.under F (((q ^ n - 1 : ℕ)) : F) := by
      rw [under_apply_eq]; simp
    rw [this]
    exact apply_natCast_card_pow_sub_one hv hn
  have hdvd := dvd_card_sub_one_of_isPrimitiveRoot hdw hζ hm
  rw [hcard] at hdvd
  obtain ⟨he0, hf0, -⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) w hw
  have hfpos : 0 < inertiaDegAbs (F := F) w hdw.isNonarchimedean := Nat.pos_of_ne_zero hf0
  have h1 : 1 ≤ q ^ inertiaDegAbs (F := F) w hdw.isNonarchimedean := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ≤ q ^ inertiaDegAbs (F := F) w hdw.isNonarchimedean :=
    le_trans hq2 (by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) hfpos)
  have h3 := Nat.le_of_dvd (by omega) hdvd
  have h4 : q ^ n ≤ q ^ inertiaDegAbs (F := F) w hdw.isNonarchimedean := by
    have : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    omega
  exact (Nat.pow_le_pow_iff_right (by omega)).1 h4

/-- (Stub, proved from 32:8, 32:9 below.) An unramified extension of degree $n$ is generated by a primitive
$(N\mathfrak p^n - 1)$-st root of unity. -/
theorem exists_primitiveRoot_of_unramified
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) :
    ∃ ζ : E, IsPrimitiveRoot ζ
      (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ Module.finrank F E - 1) ∧ F⟮ζ⟯ = ⊤ := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  obtain ⟨hdw, hc, hfin, hcard, -⟩ := isLocal_of_finite hd
  haveI := hc
  haveI := hfin
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_localField hdw
  have h2 : inertiaDegAbs (F := F) w hdw.isNonarchimedean = Module.finrank F E := h.2
  rw [hcard, h2] at hζ
  refine ⟨ζ, hζ, ?_⟩
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  set H : IntermediateField F E := F⟮ζ⟯ with hH
  have hmem : ζ ∈ H := IntermediateField.mem_adjoin_simple_self F ζ
  have hunH := ((isUnramifiedAbs_tower_iff hd H hw).1 h).2
  have hζH : IsPrimitiveRoot (⟨ζ, hmem⟩ : H)
      (Nat.card (residueFieldOf ((w.under H).under F) hd.isNonarchimedean) ^ Module.finrank F E - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := H.val.toMonoidHom) hζ Subtype.val_injective
  haveI : CompleteSpace (WithAbs ((w.under H).under F)) := inferInstanceAs (CompleteSpace (WithAbs (w.under F)))
  haveI : Finite (residueFieldOf ((w.under H).under F) hd.isNonarchimedean) :=
    inferInstanceAs (Finite (residueFieldOf (w.under F) hd.isNonarchimedean))
  have hle := le_inertiaDegAbs_of_isPrimitiveRoot (E := H) (w := w.under H) hd hn hζH
  have hfH : inertiaDegAbs (F := F) (w.under H) (isNonarchimedean_under hw) = Module.finrank F H := hunH.2
  have hle2 : Module.finrank F H ≤ Module.finrank F E := Submodule.finrank_le (H.toSubalgebra.toSubmodule)
  have hEq : Module.finrank F H = Module.finrank F E := le_antisymm hle2 (hfH ▸ hle)
  exact IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hEq, IntermediateField.finrank_top'])

/-- **32:9.** If $E$ is a splitting field of $x^{(N\mathfrak p)^n} - x$ over $F$, then $E/F$ is unramified of degree
$n$. -/
@[kb "omeara1963" "§32B, 32:9, p. 62"]
theorem isUnramifiedAbs_of_isSplittingField {n : ℕ} (hn : 0 < n)
    (hE : IsSplittingField F E
      (X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ n) - X : F[X])) :
    IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) ∧
      Module.finrank F E = n := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  set q := Nat.card (residueFieldOf (w.under F) hv) with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hqn : q ≤ q ^ n := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hn
  set m := q ^ n - 1 with hm
  have hm0 : m ≠ 0 := by omega
  haveI : NeZero m := ⟨hm0⟩
  have hmN : m + 1 = q ^ n := by omega
  have hvm : w.under F (m : F) = 1 := apply_natCast_card_pow_sub_one hv hn
  have hmF : (m : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvm
    exact zero_ne_one hvm
  have hfac : (X ^ (q ^ n) - X : F[X]) = X * (X ^ m - C (1 : F)) := by
    rw [mul_sub, ← pow_succ', hmN]; simp
  have hspl : Splits ((X ^ m - C (1 : F)).map (algebraMap F E)) := by
    have h1 := IsSplittingField.splits E (X ^ (q ^ n) - X : F[X])
    refine Splits.of_dvd h1 ?_ ?_
    · rw [hfac, Polynomial.map_mul]
      exact mul_ne_zero (by simp) ((Polynomial.map_ne_zero_iff (algebraMap F E).injective).2
        (monic_X_pow_sub_C (1 : F) hm0).ne_zero)
    · rw [hfac, Polynomial.map_mul]
      exact dvd_mul_left _ _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_splits hm0 hmF hspl
  have hgen : F⟮ζ⟯ = ⊤ := by
    have h1 : Algebra.adjoin F ((X ^ (q ^ n) - X : F[X]).rootSet E) = ⊤ := hE.adjoin_rootSet'
    have hle : Algebra.adjoin F ((X ^ (q ^ n) - X : F[X]).rootSet E) ≤ (F⟮ζ⟯).toSubalgebra := by
      apply Algebra.adjoin_le
      intro x hx
      rw [mem_rootSet] at hx
      have hx0 : x ^ (q ^ n) = x := by
        have := hx.2
        simpa [sub_eq_zero] using this
      by_cases hz : x = 0
      · simp [hz]
      · have hxm : x ^ m = 1 := by
          have : x * x ^ m = x * 1 := by rw [← pow_succ', hmN, hx0, mul_one]
          exact mul_left_cancel₀ hz this
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hxm
        exact pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) i
    rw [h1] at hle
    exact eq_top_iff.2 (fun x _ => hle Algebra.mem_top)
  obtain ⟨hα1, hun, hadj⟩ := unramified_adjoin_root_of_unity_aux hd hvm hζ.pow_eq_one hgen
  refine ⟨hun, ?_⟩
  have hge := le_inertiaDegAbs_of_isPrimitiveRoot hd hn hζ
  have hle : inertiaDegAbs (F := F) w hw ≤ n := by
    obtain ⟨hdw, hc, hfin, hcard, -⟩ := isLocal_of_finite hd
    haveI := hfin
    letI := (residueMap (F := F) w hw).toAlgebra
    classical
    haveI : Fintype (residueFieldOf (w.under F) hv) := Fintype.ofFinite _
    haveI : Fintype (residueFieldOf w hw) := Fintype.ofFinite _
    have hcardk : Fintype.card (residueFieldOf (w.under F) hv) = q := (Nat.card_eq_fintype_card).symm
    have hpow : (Ideal.Quotient.mk (maximalIdealOf w hw) ⟨ζ, hα1⟩) ^
        (Fintype.card (residueFieldOf (w.under F) hv) ^ n) =
        Ideal.Quotient.mk (maximalIdealOf w hw) ⟨ζ, hα1⟩ := by
      rw [hcardk, ← map_pow]
      congr 1
      apply Subtype.ext
      show ζ ^ (q ^ n) = ζ
      rw [← hmN, pow_succ, hζ.pow_eq_one, one_mul]
    have := card_le_of_adjoin_pow_eq hadj n hn hpow
    rw [hcardk, ← Nat.card_eq_fintype_card, hcard] at this
    exact (Nat.pow_le_pow_iff_right (by omega)).1 this
  have hfn : inertiaDegAbs (F := F) w hw = n := le_antisymm hle hge
  rw [← hun.2, hfn]

/-- **32:10.** If $E/F$ is unramified of degree $n$, then $E$ is a splitting field over $F$ of
$x^{(N\mathfrak p)^n} - x$. -/
@[kb "omeara1963" "§32B, 32:10, p. 63"]
theorem isSplittingField_of_isUnramifiedAbs
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) :
    IsSplittingField F E
      (X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ Module.finrank F E) - X : F[X]) := by
  obtain ⟨ζ, hζ, hgen⟩ := exists_primitiveRoot_of_unramified hd h
  set q := Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) with hq
  set n := Module.finrank F E with hn
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hnpos : 0 < n := Module.finrank_pos
  have hqn : q ≤ q ^ n := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hnpos
  set m := q ^ n - 1 with hm
  have hm0 : m ≠ 0 := by omega
  have hmN : m + 1 = q ^ n := by omega
  have hfac : (X ^ (q ^ n) - X : F[X]) = X * (X ^ m - C (1 : F)) := by
    rw [mul_sub, ← pow_succ', hmN]; simp
  have hspl : Splits ((X ^ (q ^ n) - X : F[X]).map (algebraMap F E)) := by
    rw [hfac, Polynomial.map_mul]
    refine Splits.mul (by simpa using (Splits.X : Splits (X : E[X]))) ?_
    have : Splits (X ^ m - C (1 : E)) := by
      rw [splits_iff_card_roots, ← nthRoots, IsPrimitiveRoot.card_nthRoots_one hζ, natDegree_X_pow_sub_C]
    simpa using this
  refine ⟨hspl, ?_⟩
  have hzr : ζ ∈ (X ^ (q ^ n) - X : F[X]).rootSet E := by
    rw [mem_rootSet]
    refine ⟨?_, ?_⟩
    · rw [hfac]; exact mul_ne_zero X_ne_zero (monic_X_pow_sub_C (1 : F) hm0).ne_zero
    · have : ζ ^ (q ^ n) = ζ := by rw [← hmN, pow_succ, hζ.pow_eq_one, one_mul]
      simp [this]
  have hint : IsAlgebraic F ζ := Algebra.IsAlgebraic.isAlgebraic ζ
  have h1 : Algebra.adjoin F {ζ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint, hgen]; rfl
  rw [eq_top_iff, ← h1]
  exact Algebra.adjoin_mono (by simpa using hzr)

/-- $X^{q^n} - X$ is separable over $F$ for $n > 0$ ($q^n - 1$ is a unit). -/
theorem separable_X_pow_sub_X_aux {n : ℕ} (hn : 0 < n) :
    (X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ n) - X : F[X]).Separable := by
  have hv := hd.isNonarchimedean
  set q := Nat.card (residueFieldOf (w.under F) hv) with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hqn : q ≤ q ^ n := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hn
  set m := q ^ n - 1 with hm
  have hm0 : m ≠ 0 := by omega
  have hmN : m + 1 = q ^ n := by omega
  have hvm : w.under F (m : F) = 1 := apply_natCast_card_pow_sub_one hv hn
  have hmF : (m : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvm
    exact zero_ne_one hvm
  have hfac : (X ^ (q ^ n) - X : F[X]) = X * (X ^ m - C (1 : F)) := by
    rw [mul_sub, ← pow_succ', hmN]; simp
  rw [hfac]
  refine Polynomial.Separable.mul separable_X (separable_X_pow_sub_C (1 : F) hmF one_ne_zero) ?_
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨X ^ k, -1, ?_⟩
  rw [hk]
  simp only [pow_succ, map_one]
  ring

/-- An unramified extension is Galois (it is the splitting field of the separable polynomial $x^{q^n} - x$). -/
theorem isGalois_of_unramified
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) : IsGalois F E := by
  haveI := isSplittingField_of_isUnramifiedAbs hd h
  exact IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_X_aux hd (Module.finrank_pos (R := F) (M := E)))
    (p := (X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ Module.finrank F E) - X : F[X]))

theorem splits_X_pow_sub_X_of_isPrimitiveRoot {L : Type*} [Field L] [Algebra F L] {N : ℕ} (hN : 2 ≤ N)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (N - 1)) : Splits ((X ^ N - X : F[X]).map (algebraMap F L)) := by
  have hfac : (X ^ N - X : F[X]) = X * (X ^ (N - 1) - C (1 : F)) := by
    rw [mul_sub, ← pow_succ']
    have : N - 1 + 1 = N := by omega
    rw [this]; simp
  rw [hfac, Polynomial.map_mul]
  refine Splits.mul (by simpa using (Splits.X : Splits (X : L[X]))) ?_
  have : Splits (X ^ (N - 1) - C (1 : L)) := by
    rw [splits_iff_card_roots, ← nthRoots, IsPrimitiveRoot.card_nthRoots_one hζ, natDegree_X_pow_sub_C]
  simpa using this

theorem mem_of_isRoot_of_unramified (K' : IntermediateField F E)
    (hK' : IsUnramifiedAbs (F := F) (w.under K')
      (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _))
    {r : ℕ} (hr : 0 < r) (hrm : r ∣ Module.finrank F K') {x : E}
    (hx : x ∈ (X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^ r) - X : F[X]).rootSet E) :
    x ∈ K' := by
  set q := Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  haveI : CompleteSpace (WithAbs ((w.under K').under F)) :=
    inferInstanceAs (CompleteSpace (WithAbs (w.under F)))
  haveI : Finite (residueFieldOf ((w.under K').under F) hd.isNonarchimedean) :=
    inferInstanceAs (Finite (residueFieldOf (w.under F) hd.isNonarchimedean))
  obtain ⟨ζ, hζ, -⟩ := exists_primitiveRoot_of_unramified (E := K') (w := w.under K') hd hK'
  obtain ⟨s, hs⟩ := hrm
  have hζ' : IsPrimitiveRoot ζ (q ^ (r * s) - 1) := by rw [← hs]; exact hζ
  have hmpos : 0 < Module.finrank F K' := Module.finrank_pos
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, mul_zero] at hs; omega
    · exact h0
  have hqr : 2 ≤ q ^ r := le_trans hq2 (by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hr)
  have hdvd : q ^ r - 1 ∣ q ^ (r * s) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (q ^ r) 1 s
  have hk0 : 0 < q ^ (r * s) - 1 := by
    have : q ^ r ≤ q ^ (r * s) := Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right r hspos)
    omega
  have hd0 : (q ^ (r * s) - 1) / (q ^ r - 1) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hk0 hdvd) (by omega)).ne'
  have hζ2 := hζ'.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hdvd)
  rw [Nat.div_div_self hdvd hk0.ne'] at hζ2
  have hspl := splits_X_pow_sub_X_of_isPrimitiveRoot (F := F) hqr hζ2
  rw [mem_rootSet] at hx
  have hp0 : (X ^ (q ^ r) - X : F[X]) ≠ 0 := hx.1
  have hmem := Splits.mem_range_of_isRoot (f := (X ^ (q ^ r) - X : F[X]).map (algebraMap F K')) hspl
    ((Polynomial.map_ne_zero_iff (algebraMap F K').injective).2 hp0) (i := K'.val.toRingHom) (x := x) (by
      rw [Polynomial.map_map]
      have : K'.val.toRingHom.comp (algebraMap F K') = algebraMap F E := rfl
      rw [this]
      have := hx.2
      rw [aeval_def, eval₂_eq_eval_map] at this
      exact this)
  obtain ⟨y, hy⟩ := hmem
  rw [← hy]
  exact y.2

theorem eq_adjoin_rootSet_of_unramified (K : IntermediateField F E)
    (hK : IsUnramifiedAbs (F := F) (w.under K)
      (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _)) :
    K = IntermediateField.adjoin F ((X ^ (Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) ^
      Module.finrank F K) - X : F[X]).rootSet E) := by
  haveI : CompleteSpace (WithAbs ((w.under K).under F)) :=
    inferInstanceAs (CompleteSpace (WithAbs (w.under F)))
  haveI : Finite (residueFieldOf ((w.under K).under F) hd.isNonarchimedean) :=
    inferInstanceAs (Finite (residueFieldOf (w.under F) hd.isNonarchimedean))
  have := isSplittingField_of_isUnramifiedAbs (E := K) (w := w.under K) hd hK
  exact (IntermediateField.isSplittingField_iff.1 this).2

/-- **32:11 (Example), uniqueness.** Two intermediate fields $K, K'$ of $E/F$ that are unramified of the same degree
$m$ over $F$ are equal (each is the splitting field in $E$ of $x^{(N\mathfrak p)^m} - x$). -/
@[kb "omeara1963" "§32B, 32:11, p. 63"]
theorem unramified_subfield_unique (K K' : IntermediateField F E)
    (hK : IsUnramifiedAbs (F := F) (w.under K) (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _))
    (hK' : IsUnramifiedAbs (F := F) (w.under K') (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _))
    (hdeg : Module.finrank F K = Module.finrank F K') : K = K' := by
  rw [eq_adjoin_rootSet_of_unramified hd K hK, eq_adjoin_rootSet_of_unramified hd K' hK', hdeg]

/-- **32:11 (Example), inclusion.** If $K_r, K_m \subseteq E$ are unramified over $F$ of degrees $r \mid m$, then
$K_r \subseteq K_m$. -/
@[kb "omeara1963" "§32B, 32:11, p. 63"]
theorem unramified_subfield_le (K K' : IntermediateField F E)
    (hK : IsUnramifiedAbs (F := F) (w.under K) (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _))
    (hK' : IsUnramifiedAbs (F := F) (w.under K') (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _))
    (hdeg : Module.finrank F K ∣ Module.finrank F K') : K ≤ K' := by
  rw [eq_adjoin_rootSet_of_unramified hd K hK, IntermediateField.adjoin_le_iff]
  intro x hx
  exact mem_of_isRoot_of_unramified hd K' hK' Module.finrank_pos hdeg hx

section Frob12

include hd

attribute [local instance] residueAlgebra

local notation "hw'" => isNonarchimedean_of_under (F := F) hd.isNonarchimedean

theorem frob12_apply_eq (σ : E ≃ₐ[F] E) (x : E) : w (σ x) = w x := by
  have := ext_unique (F := F) hd (L := E) (w.comp σ.toAlgHom.toRingHom.injective) w
    (fun y => by
      show w (σ (algebraMap F E y)) = _
      rw [AlgEquiv.commutes]; rfl) (fun y => rfl)
  exact congrArg (fun A : AbsoluteValue E ℝ => A x) this

/-- The automorphism of the residue class field induced by `σ` (it preserves `w`). -/
noncomputable def frob12_alg (σ : E ≃ₐ[F] E) :
    residueFieldOf w hw' →ₐ[residueFieldOf (w.under F) hd.isNonarchimedean] residueFieldOf w hw' :=
  { isoResidueHom hw' hw' σ.toAlgHom.toRingHom (fun x => frob12_apply_eq hd σ x) with
    commutes' := fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (σ.commutes _)) }

theorem frob12_alg_mk (σ : E ≃ₐ[F] E) (a : integers w hw') :
    frob12_alg hd σ (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (isoIntMap hw' hw' σ.toAlgHom.toRingHom (fun x => frob12_apply_eq hd σ x) a) := rfl

noncomputable def frob12_psi : (E ≃ₐ[F] E) →*
    (residueFieldOf w hw' →ₐ[residueFieldOf (w.under F) hd.isNonarchimedean] residueFieldOf w hw') where
  toFun := frob12_alg hd
  map_one' := AlgHom.ext fun y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [frob12_alg_mk]
    show _ = Ideal.Quotient.mk _ a
    congr 1
  map_mul' σ τ := AlgHom.ext fun y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    show frob12_alg hd (σ * τ) (Ideal.Quotient.mk _ a) =
      frob12_alg hd σ (frob12_alg hd τ (Ideal.Quotient.mk _ a))
    rw [frob12_alg_mk, frob12_alg_mk, frob12_alg_mk]
    congr 1

theorem frob12_le_one_of_pow_eq_one {m : ℕ} (hm : 0 < m) {ζ : E} (hζ : ζ ^ m = 1) : w ζ ≤ 1 := by
  have : w ζ ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact ((pow_eq_one_iff_of_nonneg (w.nonneg _) hm.ne').1 this).le

theorem frob12_main
    (h : IsUnramifiedAbs (F := F) w hw') :
    IsCyclic (E ≃ₐ[F] E) ∧
      ∃! σ : E ≃ₐ[F] E, (∀ x : E, w x ≤ 1 →
          w (σ x - x ^ Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean)) < 1) ∧
        Subgroup.zpowers σ = ⊤ := by
  classical
  haveI hG : IsGalois F E := isGalois_of_unramified hd h
  obtain ⟨hdw, hcomp, hfin, hcard, -⟩ := isLocal_of_finite hd
  haveI := hcomp
  haveI := hfin
  set k := residueFieldOf (w.under F) hd.isNonarchimedean with hk
  set A := residueFieldOf w hw' with hA
  set n := Module.finrank F E with hn
  have hf : inertiaDegAbs (F := F) w hw' = n := h.2
  have hn0 : 0 < n := Module.finrank_pos
  haveI : Finite A := hfin
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Module.Finite k A := Module.finite_of_finrank_pos (by
    show 0 < inertiaDegAbs (F := F) w hw'
    rw [hf]; exact hn0)
  haveI : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.of_finite k A
  have hfr : Module.finrank k A = n := hf
  have hq : Nat.card (residueFieldOf w hdw.isNonarchimedean) = Nat.card k ^ n := by
    rw [hcard]; rw [hf]
  let Φ : A ≃ₐ[k] A := FiniteField.frobeniusAlgEquivOfAlgebraic k A
  have hΦ : ∀ y : A, Φ y = y ^ Nat.card k := fun y => by
    rw [Nat.card_eq_fintype_card]; rfl
  let Ψ : (E ≃ₐ[F] E) →* (A ≃ₐ[k] A) :=
    ((Algebra.IsAlgebraic.algEquivEquivAlgHom k A).symm : (A →ₐ[k] A) ≃* (A ≃ₐ[k] A)).toMonoidHom.comp
      (frob12_psi hd)
  have hΨ : ∀ σ y, Ψ σ y = frob12_alg hd σ y := fun σ y => rfl
  have hΨmk : ∀ (σ : E ≃ₐ[F] E) (a : integers w hw'),
      Ψ σ (Ideal.Quotient.mk _ a) = Φ (Ideal.Quotient.mk _ a) ↔ w (σ a - a ^ Nat.card k) < 1 := by
    intro σ a
    rw [hΨ, frob12_alg_mk, hΦ, ← map_pow, Ideal.Quotient.eq]
    rfl
  -- injectivity
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨ζ, hζ, hgen⟩ := exists_primitiveRoot_of_unramified hd h
    have hm : 0 < Nat.card k ^ n - 1 := by
      have : 2 ≤ Nat.card k := Finite.one_lt_card
      have : 2 ≤ Nat.card k ^ n := by
        calc 2 ≤ Nat.card k := this
          _ = Nat.card k ^ 1 := (pow_one _).symm
          _ ≤ Nat.card k ^ n := Nat.pow_le_pow_right (by omega) hn0
      omega
    have hζ1 : w ζ ≤ 1 := frob12_le_one_of_pow_eq_one hd hm hζ.pow_eq_one
    have hσζ : w (σ ζ - ζ) < 1 := by
      have e : Ψ σ (Ideal.Quotient.mk _ (⟨ζ, hζ1⟩ : integers w hw')) =
          Ideal.Quotient.mk _ (⟨ζ, hζ1⟩ : integers w hw') := by rw [hσ]; rfl
      rw [hΨ, frob12_alg_mk, Ideal.Quotient.eq] at e
      exact e
    have hN : Nat.card (residueFieldOf w hdw.isNonarchimedean) - 1 = Nat.card k ^ n - 1 := by rw [hq]
    have h1 : (σ ζ) ^ (Nat.card (residueFieldOf w hdw.isNonarchimedean) - 1) = 1 := by
      rw [hN, ← map_pow, hζ.pow_eq_one, map_one]
    have h2 : ζ ^ (Nat.card (residueFieldOf w hdw.isNonarchimedean) - 1) = 1 := by
      rw [hN]; exact hζ.pow_eq_one
    have hfix : σ ζ = ζ := eq_of_rootsOfUnity_of_apply_sub_lt hdw h1 h2 hσζ
    have hS : Algebra.adjoin F {ζ} = ⊤ := by
      have hint : IsIntegral F ζ := Algebra.IsIntegral.isIntegral ζ
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hgen]
      simp
    have : σ.toAlgHom = (1 : E ≃ₐ[F] E).toAlgHom := AlgHom.ext_of_adjoin_eq_top hS (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hfix)
    exact AlgEquiv.ext fun x => congrArg (fun f => f x) this
  have hcardG : Nat.card (E ≃ₐ[F] E) = n := IsGalois.card_aut_eq_finrank F E
  have hbijΦ := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k A
  have hcardA : Nat.card (A ≃ₐ[k] A) = n := by
    rw [← Nat.card_eq_of_bijective _ hbijΦ, Nat.card_eq_fintype_card, Fintype.card_fin, hfr]
  haveI : Finite (A ≃ₐ[k] A) := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact hn0.ne')
  have hbij : Function.Bijective Ψ := hinjΨ.bijective_of_nat_card_le (by rw [hcardG, hcardA])
  have hcyc : IsCyclic (E ≃ₐ[F] E) := by
    haveI : IsCyclic (A ≃ₐ[k] A) := inferInstance
    exact isCyclic_of_surjective (MulEquiv.ofBijective Ψ hbij).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨σ0, hσ0⟩ := hbij.2 Φ
  have hcong : ∀ σ : E ≃ₐ[F] E, (∀ x : E, w x ≤ 1 → w (σ x - x ^ Nat.card k) < 1) ↔ Ψ σ = Φ := by
    intro σ
    constructor
    · intro hc
      ext y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact (hΨmk σ a).2 (hc a a.2)
    · intro he x hx
      exact (hΨmk σ ⟨x, hx⟩).1 (by rw [he])
  refine ⟨hcyc, σ0, ⟨(hcong σ0).2 hσ0, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro τ _
    obtain ⟨i, hi⟩ := hbijΦ.2 (Ψ τ)
    have : τ = σ0 ^ i.1 := hinjΨ (by rw [map_pow, hσ0]; exact hi.symm)
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rintro σ' ⟨hc, -⟩
    exact hinjΨ (((hcong σ').1 hc).trans hσ0.symm)

end Frob12

/-- **32:12.** An unramified extension $E/F$ of local fields is Galois with cyclic Galois group, and there is a unique
$\sigma \in G(E/F)$ with $\sigma x \equiv x^{N\mathfrak p} \bmod \mathfrak m(\mathfrak P)$ for all $x \in \mathfrak o(\mathfrak P)$;
this $\sigma$ generates $G(E/F)$. -/
@[kb "omeara1963" "§32B, 32:12, p. 63"]
theorem isGalois_isCyclic_frobenius
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) :
    IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E) ∧
      ∃! σ : E ≃ₐ[F] E, (∀ x : E, w x ≤ 1 →
          w (σ x - x ^ Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean)) < 1) ∧
        Subgroup.zpowers σ = ⊤ := by
  exact ⟨isGalois_of_unramified hd h, frob12_main hd h⟩

/-- **32:13 (Definition).** The *Frobenius automorphism* of an unramified extension $E/F$ of local fields: the
automorphism $\sigma$ of 32:12. -/
@[kb "omeara1963" "§32B, 32:13, p. 64"]
noncomputable def frobeniusAbs
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) : E ≃ₐ[F] E :=
  (isGalois_isCyclic_frobenius hd h).2.2.exists.choose

/-- **32:12a.** The Frobenius automorphism satisfies $\sigma\zeta = \zeta^{N\mathfrak p}$ for every
$(N\mathfrak P - 1)$-st root of unity $\zeta$ of $E$. -/
@[kb "omeara1963" "§32B, 32:12a, p. 64"]
theorem frobeniusAbs_rootOfUnity
    (h : IsUnramifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean)) {ζ : E}
    (hζ : ζ ^ (Nat.card (residueFieldOf w (isNonarchimedean_of_under hd.isNonarchimedean)) - 1) = 1) :
    frobeniusAbs hd h ζ = ζ ^ Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean) := by
  classical
  obtain ⟨hdw, hcomp, hfin, -, -⟩ := isLocal_of_finite hd
  haveI := hcomp
  haveI := hfin
  have hspec : ∀ x : E, w x ≤ 1 → w (frobeniusAbs hd h x -
      x ^ Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean)) < 1 :=
    (isGalois_isCyclic_frobenius hd h).2.2.exists.choose_spec.1
  have hN : 2 ≤ Nat.card (residueFieldOf w (isNonarchimedean_of_under hd.isNonarchimedean)) :=
    Finite.one_lt_card
  have hm : 0 < Nat.card (residueFieldOf w (isNonarchimedean_of_under hd.isNonarchimedean)) - 1 := by
    omega
  have hζ1 : w ζ ≤ 1 := frob12_le_one_of_pow_eq_one hd hm hζ
  have h1 : (frobeniusAbs hd h ζ) ^ (Nat.card (residueFieldOf w hdw.isNonarchimedean) - 1) = 1 := by
    rw [← map_pow, hζ, map_one]
  have h2 : (ζ ^ Nat.card (residueFieldOf (w.under F) hd.isNonarchimedean)) ^
      (Nat.card (residueFieldOf w hdw.isNonarchimedean) - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  exact eq_of_rootsOfUnity_of_apply_sub_lt hdw h1 h2 (hspec ζ hζ1)

/-- **32:14.** Let $\Omega/F$ be a finite extension of local fields (here $\Omega = E$) with subextensions $K/F$ and
$H/F$. If $K/F$ is unramified, then $KH/H$ is unramified. -/
@[kb "omeara1963" "§32B, 32:14, p. 64"]
theorem isUnramifiedAbs_sup (K H : IntermediateField F E)
    (hK : IsUnramifiedAbs (F := F) (w.under K) (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _)) :
    IsUnramifiedAbs (F := H) (w.under (IntermediateField.extendScalars (le_sup_right : H ≤ K ⊔ H)))
      (fun a b => isNonarchimedean_of_under hd.isNonarchimedean _ _) := by
  have hv := hd.isNonarchimedean
  set q := Nat.card (residueFieldOf (w.under F) hv) with hq
  haveI : CompleteSpace (WithAbs ((w.under K).under F)) :=
    inferInstanceAs (CompleteSpace (WithAbs (w.under F)))
  haveI : Finite (residueFieldOf ((w.under K).under F) hd.isNonarchimedean) :=
    inferInstanceAs (Finite (residueFieldOf (w.under F) hd.isNonarchimedean))
  obtain ⟨ζ, hζ, hgen⟩ := exists_primitiveRoot_of_unramified (E := K) (w := w.under K) hd hK
  set k := Module.finrank F K with hk
  have hkpos : 0 < k := Module.finrank_pos
  have hζ' : IsPrimitiveRoot ζ (q ^ k - 1) := hζ
  set L : IntermediateField H E := IntermediateField.extendScalars (le_sup_right : H ≤ K ⊔ H) with hL
  have hζL : (ζ : E) ∈ L := (le_sup_left : K ≤ K ⊔ H) ζ.2
  -- the base H is a local field
  haveI : CompleteSpace (WithAbs ((w.under H).under F)) :=
    inferInstanceAs (CompleteSpace (WithAbs (w.under F)))
  haveI : Finite (residueFieldOf ((w.under H).under F) hd.isNonarchimedean) :=
    inferInstanceAs (Finite (residueFieldOf (w.under F) hd.isNonarchimedean))
  obtain ⟨hdH, hcH, hfinH, -, -⟩ := isLocal_of_finite (F := F) (E := H) (w := w.under H) hd
  haveI : FiniteDimensional H E := FiniteDimensional.right F H E
  -- generation
  have hKeq : K = F⟮(ζ : E)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hgen]
    simp
  have hsup : ∀ x ∈ K ⊔ H, x ∈ (IntermediateField.adjoin H {(ζ : E)}) := by
    have : K ⊔ H ≤ (IntermediateField.adjoin H {(ζ : E)}).restrictScalars F := by
      refine sup_le ?_ ?_
      · exact hKeq.le.trans ((IntermediateField.adjoin_simple_le_iff).2
          (IntermediateField.mem_adjoin_simple_self H (ζ : E)))
      · intro x hx
        exact IntermediateField.algebraMap_mem (IntermediateField.adjoin H {(ζ : E)}) (⟨x, hx⟩ : H)
    exact fun x hx => this hx
  have hE : IntermediateField.adjoin H {(⟨(ζ : E), hζL⟩ : L)} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← IntermediateField.mem_lift, IntermediateField.lift_adjoin_simple]
    exact hsup x.1 x.2
  have hm : (w.under L).under H ((q ^ k - 1 : ℕ) : H) = 1 := by
    have h1 : (w.under L).under H ((q ^ k - 1 : ℕ) : H) = w (((q ^ k - 1 : ℕ)) : E) := by
      rw [under_apply_eq, under_apply_eq]; simp
    rw [h1]
    have : w (((q ^ k - 1 : ℕ)) : E) = w.under F (((q ^ k - 1 : ℕ)) : F) := by
      rw [under_apply_eq]; simp
    rw [this]
    exact apply_natCast_card_pow_sub_one hv hkpos
  have hpow : (⟨(ζ : E), hζL⟩ : L) ^ (q ^ k - 1) = 1 := by
    apply Subtype.ext
    have := hζ'.pow_eq_one
    have h2 := congrArg (fun z : K => (z : E)) this
    simpa using h2
  haveI : CompleteSpace (WithAbs ((w.under L).under H)) := hcH
  haveI : Finite (residueFieldOf ((w.under L).under H) hdH.isNonarchimedean) := hfinH
  exact isUnramifiedAbs_adjoin_root_of_unity (F := H) (E := L) (w := w.under L) hdH hm hpow hE

/-- **32:15.** Let $E = F(\alpha)$ with $\alpha$ a root of an Eisenstein polynomial
$x^r + a_1x^{r-1} + \dots + a_r$: all $a_i \in \mathfrak m(\mathfrak p)$ and $a_r$ a prime element at $\mathfrak p$. Then
$E/F$ is fully ramified of degree $r$, and $\alpha$ is a prime element at $\mathfrak P$. Here $f$ is monic of degree
$r$, its coefficients below the leading one have value $< 1$, and its constant term is a prime element. -/
@[kb "omeara1963" "§32B, 32:15, p. 64"]
theorem isFullyRamifiedAbs_of_eisenstein {α : E} (hα : F⟮α⟯ = ⊤) {f : F[X]} (hf : f.Monic)
    (hcoeff : ∀ i < f.natDegree, w.under F (f.coeff i) < 1)
    (hprime : IsPrimeElt (w.under F) hd.isNonarchimedean (f.coeff 0)) (hroot : aeval α f = 0) :
    IsFullyRamifiedAbs (F := F) w (isNonarchimedean_of_under hd.isNonarchimedean) ∧
      Module.finrank F E = f.natDegree ∧
      IsPrimeElt w (isNonarchimedean_of_under hd.isNonarchimedean) α := by
  have hv := hd.isNonarchimedean
  have hw : IsNonarchimedean w := isNonarchimedean_of_under hv
  have hdw : IsDiscreteAbs w := (isDiscreteAbs_iff_under (F := F) w).2 hd
  obtain ⟨hc0ne, hc0val⟩ := (isPrimeElt_iff_apply_eq hd).1 hprime
  have hgF := genAbs_pos hd
  have hgF1 := genAbs_lt_one hd
  have hle_gen : ∀ x : F, w.under F x < 1 → w.under F x ≤ genAbs hd := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simpa using hgF.le
    · obtain ⟨n, hn⟩ := exists_zpow_genAbs hd hx0
      rw [hn] at hx ⊢
      have h1 : genAbs hd ^ n < genAbs hd ^ (0 : ℤ) := by simpa using hx
      have h2 := (genAbs_zpow_lt_iff hd).1 h1
      have : genAbs hd ^ n ≤ genAbs hd ^ (1 : ℤ) := (genAbs_zpow_le_iff hd).2 (by omega)
      simpa using this
  have hint : ∀ i, w (algebraMap F E (f.coeff i)) ≤ 1 := by
    intro i
    rcases lt_trichotomy i f.natDegree with h | h | h
    · exact (hcoeff i h).le
    · rw [h, hf.coeff_natDegree]; simp
    · rw [coeff_eq_zero_of_natDegree_lt h]; simp
  have hα1 : w α ≤ 1 := apply_le_one_of_aeval_eq_zero hw hf hint hroot
  have hr0 : f.natDegree ≠ 0 := by
    intro h0
    have := hf.natDegree_eq_zero.1 h0
    simp [this] at hroot
  obtain ⟨r', hr'⟩ : ∃ r', f.natDegree = r' + 1 := ⟨f.natDegree - 1, by omega⟩
  have hsum : α ^ (r' + 1) = - ∑ i ∈ Finset.range (r' + 1), algebraMap F E (f.coeff i) * α ^ i := by
    have h := hroot
    rw [aeval_eq_sum_range, hr', Finset.sum_range_succ] at h
    simp only [Algebra.smul_def, hr' ▸ hf.coeff_natDegree, map_one, one_mul] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  set t := w α with ht
  have ht0 : 0 ≤ t := w.nonneg _
  have hterm : ∀ i < r' + 1, w (algebraMap F E (f.coeff i) * α ^ i) ≤ genAbs hd * t ^ i := by
    intro i hi
    rw [map_mul, map_pow]
    exact mul_le_mul (hle_gen _ (hcoeff i (by omega))) le_rfl (by positivity) hgF.le
  have hteq : t ^ (r' + 1) = genAbs hd := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have hb : w (∑ i ∈ Finset.range (r' + 1), algebraMap F E (f.coeff i) * α ^ i) ≤ genAbs hd := by
        apply sum_le_of_nonarch hw _ _ hgF.le
        intro i hi
        refine (hterm i (Finset.mem_range.1 hi)).trans ?_
        calc genAbs hd * t ^ i ≤ genAbs hd * 1 :=
              mul_le_mul le_rfl (pow_le_one₀ ht0 hα1) (by positivity) hgF.le
          _ = genAbs hd := mul_one _
      have : t ^ (r' + 1) ≤ genAbs hd := by
        rw [ht, ← map_pow, hsum, AbsoluteValue.map_neg]; exact hb
      linarith
    · by_contra hlt
      push Not at hlt
      have ht1 : t < 1 := by
        by_contra h1
        have : t = 1 := le_antisymm hα1 (not_lt.1 h1)
        rw [this, one_pow] at hlt
        linarith
      rw [Finset.sum_range_succ'] at hsum
      have hc0 : algebraMap F E (f.coeff 0) = - α ^ (r' + 1) - ∑ i ∈ Finset.range r',
          algebraMap F E (f.coeff (i + 1)) * α ^ (i + 1) := by
        simp only [pow_zero, mul_one] at hsum
        linear_combination hsum
      have hS : w (∑ i ∈ Finset.range r', algebraMap F E (f.coeff (i + 1)) * α ^ (i + 1)) < genAbs hd := by
        apply sum_lt_of_nonarch hw _ _ hgF
        intro i hi
        refine lt_of_le_of_lt (hterm (i + 1) (by have := Finset.mem_range.1 hi; omega)) ?_
        calc genAbs hd * t ^ (i + 1) ≤ genAbs hd * t :=
              mul_le_mul le_rfl (pow_le_of_le_one ht0 ht1.le (by omega)) (by positivity) hgF.le
          _ < genAbs hd := by nlinarith
      have h2 : w (algebraMap F E (f.coeff 0)) < genAbs hd := by
        rw [hc0, sub_eq_add_neg]
        refine lt_of_le_of_lt (hw _ _) (max_lt ?_ ?_)
        · rw [AbsoluteValue.map_neg, map_pow]; exact hlt
        · rw [AbsoluteValue.map_neg]; exact hS
      have h3 : w (algebraMap F E (f.coeff 0)) = genAbs hd := hc0val
      linarith
  have hα0 : α ≠ 0 := by
    intro h0
    rw [ht, h0, map_zero, zero_pow (by omega)] at hteq
    exact hgF.ne hteq
  obtain ⟨k, hk⟩ := exists_zpow_genAbs hdw hα0
  have hgFE := genAbs_under_eq_pow hdw hd
  have hkr : k * ((r' + 1 : ℕ) : ℤ) = ((ramificationIndexAbs (F := F) w : ℕ) : ℤ) := by
    apply genAbs_zpow_injective hdw
    show genAbs hdw ^ (k * ((r' + 1 : ℕ) : ℤ)) = genAbs hdw ^ ((ramificationIndexAbs (F := F) w : ℕ) : ℤ)
    rw [zpow_mul, zpow_natCast, zpow_natCast, ← hk, hteq, hgFE]
  obtain ⟨he0, hf0, hle⟩ := ramificationIndexAbs_mul_inertiaDegAbs_le (F := F) w hw
  have hnle : Module.finrank F E ≤ r' + 1 := by
    have hint' : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have h1 := IntermediateField.adjoin.finrank hint'
    have h2 : Module.finrank F F⟮α⟯ = Module.finrank F E := by
      rw [hα]; exact IntermediateField.finrank_top'
    rw [← h2, h1, ← hr']
    exact Polynomial.natDegree_le_of_dvd (minpoly.dvd F α hroot) hf.ne_zero
  have he1 := Nat.pos_of_ne_zero he0
  have hf1 := Nat.pos_of_ne_zero hf0
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have : k * ((r' + 1 : ℕ) : ℤ) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg <;> omega
    omega
  have hre : r' + 1 ≤ ramificationIndexAbs (F := F) w := by
    have : (1 : ℤ) * ((r' + 1 : ℕ) : ℤ) ≤ k * ((r' + 1 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hk1 (by positivity)
    omega
  have hef : ramificationIndexAbs (F := F) w ≤ ramificationIndexAbs (F := F) w *
      inertiaDegAbs (F := F) w hw := Nat.le_mul_of_pos_right _ hf1
  have he_eq : ramificationIndexAbs (F := F) w = Module.finrank F E := by omega
  have hf_eq : inertiaDegAbs (F := F) w hw = 1 := by
    have : ramificationIndexAbs (F := F) w * inertiaDegAbs (F := F) w hw ≤
        ramificationIndexAbs (F := F) w * 1 := by rw [mul_one]; omega
    exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left this he1) hf1
  have hk_eq : k = 1 := by
    have : k * ((r' + 1 : ℕ) : ℤ) = 1 * ((r' + 1 : ℕ) : ℤ) := by
      rw [hkr]; omega
    exact mul_right_cancel₀ (by positivity) this
  refine ⟨⟨he_eq, hf_eq⟩, by omega, ?_⟩
  refine (isPrimeElt_iff_apply_eq hdw).2 ⟨hα0, ?_⟩
  rw [hk, hk_eq, zpow_one]

end Extension

end QuadFormsKB.OMeara
