/-
# O'Meara 93:28, proof of the sufficiency: step 3, peeling off the first component

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2\in F^\times$, a finite
dimensional quadratic space $(V,Q)$, lattices `Submodule R V`; indices are $0$-based.

For a Jordan splitting $L=L_1\perp\cdots\perp L_t$ write $L^*=L_2\perp\cdots\perp L_t$ (`tailLat Ls`, with the splitting
`fun k => Ls k.succ`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 3, p. 273)
* `fund_tail` and its corollaries: for a saturated splitting the fundamental norm groups, norm ideals, weights and the
  ideals $\mathfrak f$ of $L^*$ are those of $L$ shifted by one;
* `isJordanSplitting_tail`: the tail splitting is a Jordan splitting;
* `isOrthSum_chain_tail`: $L_{(k+2)}=L_1\perp L^*_{(k+1)}$;
* `cond1_tail`, `cond2_tail`, `cond3_tail`: conditions (i), (ii), (iii) of 93:28 at the index $k+1$ for $(L,K)$ are equivalent
  to the same conditions at the index $k$ for $(L^*,K^*)$ when $L_1=K_1$;
* `isometricLat_of_tail`: $L^*\cong K^*$ implies $P\perp L^*\cong P\perp K^*$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuff
import QuadFormsKB.Literature.OMeara.Sec93FTransfer
import QuadFormsKB.Literature.OMeara.Sec93FRepTransfer
import QuadFormsKB.Literature.OMeara.Sec93FNecMerge
import QuadFormsKB.Literature.OMeara.Sec92Jordan
import QuadFormsKB.Literature.OMeara.Sec92Chain

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffStep

open QuadFormsKB.OMeara.NecMerge QuadFormsKB.OMeara.Transfer28 QuadFormsKB.OMeara.RepTransfer

section Tail

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The tail lattice** $L^*=L_2\perp\cdots\perp L_t$ of a splitting `Ls : Fin (m+1) → _` (components `Ls 1, …, Ls m`). -/
def tailLat {m : ℕ} (Ls : Fin (m + 1) → Submodule R V) : Submodule R V := ⨆ k : Fin m, Ls k.succ

theorem iSup_eq_zero_sup {m : ℕ} (Ls : Fin (m + 1) → Submodule R V) :
    ⨆ i, Ls i = Ls 0 ⊔ tailLat Ls := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.cases le_sup_left (fun k => le_sup_of_le_right (le_iSup (fun k : Fin m => Ls k.succ) k)) i
  · exact sup_le (le_iSup Ls 0) (iSup_le fun k => le_iSup Ls k.succ)

theorem orth_zero_tail {m : ℕ} {L : Submodule R V} {Ls : Fin (m + 1) → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {x y : V} (hx : x ∈ Ls 0) (hy : y ∈ tailLat Ls) : bil Q x y = 0 := by
  refine Submodule.iSup_induction _ (motive := fun y => bil Q x y = 0) hy (fun k z hz => ?_) (by simp [bil])
    (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
  exact hL.orth 0 k.succ (Fin.succ_ne_zero k).symm x hx z hz

theorem orth_tail_zero {m : ℕ} {L : Submodule R V} {Ls : Fin (m + 1) → Submodule R V} (hL : IsOrthSplit Q L Ls)
    {x y : V} (hx : x ∈ tailLat Ls) (hy : y ∈ Ls 0) : bil Q x y = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => bil Q x y = 0) hx (fun k z hz => ?_) (by simp [bil])
    (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
  exact hL.orth k.succ 0 (Fin.succ_ne_zero k) z hz y hy

theorem tailLat_le {m : ℕ} {L : Submodule R V} {Ls : Fin (m + 1) → Submodule R V} (hL : IsOrthSplit Q L Ls) :
    tailLat Ls ≤ L := by
  rw [← hL.iSup_eq, iSup_eq_zero_sup]; exact le_sup_right

/-- **The tail of a Jordan splitting is a Jordan splitting** of the tail lattice. -/
theorem isJordanSplitting_tail {m : ℕ} {L : Submodule R V} {Ls : Fin (m + 1) → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : IsJordanSplitting Q (tailLat Ls) (fun k : Fin m => Ls k.succ) where
  split :=
    { orth := fun i j hij x hx y hy => hL.split.orth i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) x hx y hy
      indep := hL.split.indep.comp (Fin.succ_injective m)
      iSup_eq := rfl }
  modular := fun i => hL.modular i.succ
  scale_strictAnti := hL.scale_strictAnti.comp_strictMono (Fin.strictMono_succ)

/-! ### (S1) The fundamental invariants of the tail -/

variable {m : ℕ} {L : Submodule R V} {Ls : Fin (m + 1) → Submodule R V}

theorem le_subA_tail (hL : IsJordanSplitting Q L Ls) (k : Fin m) :
    Ls k.succ ≤ subA Q (scale Q (Ls k.succ)) (tailLat Ls) := by
  intro x hx
  refine ⟨le_iSup (fun k : Fin m => Ls k.succ) k hx, fun y hy => ?_⟩
  refine Submodule.iSup_induction _ (motive := fun y => bil Q x y ∈ scale Q (Ls k.succ)) hy
    (fun j z hz => ?_) (by simp [bil]) (fun a b ha hb => by rw [bil_add_right]; exact add_mem ha hb)
  by_cases hjk : j = k
  · subst hjk; exact bil_mem_scale Q hx hz
  · rw [hL.split.orth k.succ j.succ (fun h => hjk (Fin.succ_injective _ h).symm) x hx z hz]
    exact zero_mem _

theorem subA_tail_le (hL : IsJordanSplitting Q L Ls) (a : Submodule R F) :
    subA Q a (tailLat Ls) ≤ subA Q a L := by
  have hsum : L = Ls 0 ⊔ tailLat Ls := by rw [← hL.split.iSup_eq, iSup_eq_zero_sup]
  rw [hsum, subA_sup_of_orth Q (fun x hx y hy => orth_zero_tail Q hL.split hx hy) a]
  exact le_sup_right

/-- **The fundamental norm groups of the tail** (O'Meara 1963, p. 273: "since the splittings are saturated"): for a
saturated Jordan splitting, $\mathfrak g_k(L^*)=\mathfrak g_{k+1}(L)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (the fundamental invariants of L*)"]
theorem fund_tail (hS : IsSaturated Q L Ls) (k : Fin m) :
    fundNormGroup Q (tailLat Ls) (fun j : Fin m => Ls j.succ) k = fundNormGroup Q L Ls k.succ := by
  have h1 := subA_tail_le Q hS.1 (scale Q (Ls k.succ))
  have h2 := le_subA_tail Q hS.1 k
  apply le_antisymm
  · exact normGroup_mono Q h1
  · calc fundNormGroup Q L Ls k.succ = normGroup Q (Ls k.succ) := (hS.2 k.succ).symm
      _ ≤ normGroup Q (subA Q (scale Q (Ls k.succ)) (tailLat Ls)) := normGroup_mono Q h2

theorem scale_fundSub_tail (hS : IsSaturated Q L Ls) (k : Fin m) :
    scale Q (fundSub Q (tailLat Ls) (fun j : Fin m => Ls j.succ) k) = scale Q (Ls k.succ) :=
  le_antisymm (scale_subA_le Q _ _) (scale_mono Q (le_subA_tail Q hS.1 k))

theorem scale_fundSub (hS : IsSaturated Q L Ls) (k : Fin m) :
    scale Q (fundSub Q L Ls k.succ) = scale Q (Ls k.succ) :=
  le_antisymm (scale_subA_le Q _ _) (scale_mono Q ((le_subA_tail Q hS.1 k).trans (subA_tail_le Q hS.1 _)))

theorem fundNormIdeal_tail (hS : IsSaturated Q L Ls) (k : Fin m) :
    fundNormIdeal Q (tailLat Ls) (fun j : Fin m => Ls j.succ) k = fundNormIdeal Q L Ls k.succ := by
  unfold fundNormIdeal
  rw [normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup]
  have := fund_tail Q hS k
  unfold fundNormGroup at this
  rw [this]

theorem normGroupIdeal_congr {A B : Submodule R V} (h : normGroup Q A = normGroup Q B) :
    normGroupIdeal Q A = normGroupIdeal Q B := by
  ext z
  show (∀ r : R, r • z ∈ normGroup Q A) ↔ ∀ r : R, r • z ∈ normGroup Q B
  rw [h]

theorem fundWeight_tail (hS : IsSaturated Q L Ls) (k : Fin m) :
    fundWeight Q (tailLat Ls) (fun j : Fin m => Ls j.succ) k = fundWeight Q L Ls k.succ := by
  unfold fundWeight weight
  rw [normGroupIdeal_congr Q (fund_tail Q hS k), scale_fundSub_tail Q hS k, scale_fundSub Q hS k]

theorem fIdeal_tail (hS : IsSaturated Q L Ls) (k l : Fin m) :
    fIdeal Q (tailLat Ls) (fun j : Fin m => Ls j.succ) k l = fIdeal Q L Ls k.succ l.succ := by
  unfold fIdeal
  rw [fund_tail Q hS k, fund_tail Q hS l, fundNormIdeal_tail Q hS k, fundNormIdeal_tail Q hS l]

theorem isFundNormGenerators_tail (hS : IsSaturated Q L Ls) (a : Fin (m + 1) → F)
    (ha : IsFundNormGenerators Q L Ls a) : IsFundNormGenerators Q (tailLat Ls) (fun j : Fin m => Ls j.succ)
      (fun j => a j.succ) := by
  intro k
  obtain ⟨h1, h2⟩ := ha k.succ
  refine ⟨?_, ?_⟩
  · have : a k.succ ∈ fundNormGroup Q L Ls k.succ := h1
    rw [← fund_tail Q hS k] at this; exact this
  · have := fundNormIdeal_tail Q hS k
    unfold fundNormIdeal at this
    rw [this]; exact h2

/-! ### (S2) The conditions of 93:28 for the tail -/

/-- $L_{(k+2)} = L^*_{(k+1)} \perp L_1$ (the Jordan chain of $L$ is the first component plus the chain of the tail). -/
theorem isOrthSum_chain_tail (hfg : L.FG) (hL : IsJordanSplitting Q L Ls) (k : Fin m) :
    IsOrthSum Q (jordanChain Ls k.succ) (jordanChain (fun j : Fin m => Ls j.succ) k) (Ls 0) := by
  have hle : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  have hreg : IsRegular Q (Ls 0) := (hL.modular 0).isRegular Q (Submodule.FG.of_le hfg (hle 0))
  have horth : ∀ x ∈ jordanChain (fun j : Fin m => Ls j.succ) k, ∀ y ∈ Ls 0, bil Q x y = 0 := by
    intro x hx y hy
    refine bil_eq_zero_of_mem_iSup Q (P := fun j => j ≤ k) (fun j _ z hz => ?_) hx
    exact hL.split.orth j.succ 0 (Fin.succ_ne_zero j) z hz y hy
  refine ⟨horth, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hreg x hx2 fun y hy => horth x hx1 y hy)
  · apply le_antisymm
    · refine sup_le (iSup₂_le fun j hj => ?_) ?_
      · exact le_iSup₂_of_le j.succ (Fin.succ_le_succ_iff.2 hj) le_rfl
      · exact le_iSup₂_of_le 0 (Fin.zero_le _) le_rfl
    · refine iSup₂_le fun j hj => ?_
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact le_sup_right
      · exact le_sup_of_le_left (le_iSup₂_of_le j' (Fin.succ_le_succ_iff.1 hj) le_rfl)

variable {K : Submodule R V} {Ks : Fin (m + 1) → Submodule R V}

/-- Condition (i) of 93:28. -/
def Cond1 {t : ℕ} (L : Submodule R V) (Ls : Fin t → Submodule R V) (K : Submodule R V) (Ks : Fin t → Submodule R V)
    (i j : Fin t) : Prop :=
  DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j)

/-- Condition (ii) of 93:28. -/
def Cond2 {t : ℕ} (L : Submodule R V) (Ls : Fin t → Submodule R V) (K : Submodule R V) (Ks : Fin t → Submodule R V)
    (a : Fin t → F) (i j : Fin t) : Prop :=
  fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j) →
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a j)

/-- Condition (iii) of 93:28. -/
def Cond3 {t : ℕ} (L : Submodule R V) (Ls : Fin t → Submodule R V) (K : Submodule R V) (Ks : Fin t → Submodule R V)
    (a : Fin t → F) (i j : Fin t) : Prop :=
  fIdeal Q L Ls i j < (4 * a i) • (1 / fundWeight Q L Ls i) →
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a i)

/-- The common data for peeling off the first component. -/
structure TailData (L K : Submodule R V) (Ls Ks : Fin (m + 1) → Submodule R V) : Prop where
  satL : IsSaturated Q L Ls
  jordK : IsJordanSplitting Q K Ks
  fgL : L.FG
  fgK : K.FG
  first : Ls 0 = Ks 0

theorem TailData.regFirst {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) : IsRegular Q (Ls 0) :=
  (h.satL.1.modular 0).isRegular Q (Submodule.FG.of_le h.fgL (h.satL.1.split.iSup_eq ▸ le_iSup Ls 0))

theorem TailData.regFirst' {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) : IsRegular Q (Ks 0) :=
  (h.jordK.modular 0).isRegular Q (Submodule.FG.of_le h.fgK (h.jordK.split.iSup_eq ▸ le_iSup Ks 0))

theorem TailData.fgFirst {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) : (Ls 0).FG :=
  Submodule.FG.of_le h.fgL (h.satL.1.split.iSup_eq ▸ le_iSup Ls 0)

theorem TailData.fgFirst' {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) : (Ks 0).FG :=
  Submodule.FG.of_le h.fgK (h.jordK.split.iSup_eq ▸ le_iSup Ks 0)

theorem TailData.iso {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) : IsometricLat Q Q (Ls 0) (Ks 0) := by
  rw [← h.first]; exact ⟨LinearEquiv.refl R _, fun x => rfl⟩

theorem TailData.fgChain {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) (k : Fin m) :
    (jordanChain (fun j : Fin m => Ls j.succ) k).FG ∧ (jordanChain (fun j : Fin m => Ks j.succ) k).FG := by
  refine ⟨Submodule.FG.of_le h.fgL (iSup₂_le fun j _ => ?_), Submodule.FG.of_le h.fgK (iSup₂_le fun j _ => ?_)⟩
  · exact h.satL.1.split.iSup_eq ▸ le_iSup Ls j.succ
  · exact h.jordK.split.iSup_eq ▸ le_iSup Ks j.succ

theorem TailData.fgChainSucc {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) (k : Fin m) : (jordanChain Ls k.succ).FG ∧ (jordanChain Ks k.succ).FG := by
  refine ⟨Submodule.FG.of_le h.fgL (iSup₂_le fun j _ => ?_), Submodule.FG.of_le h.fgK (iSup₂_le fun j _ => ?_)⟩
  · exact h.satL.1.split.iSup_eq ▸ le_iSup Ls j
  · exact h.jordK.split.iSup_eq ▸ le_iSup Ks j

theorem TailData.orthSums {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) (k : Fin m) :
    IsOrthSum Q (jordanChain Ls k.succ) (jordanChain (fun j : Fin m => Ls j.succ) k) (Ls 0) ∧
      IsOrthSum Q (jordanChain Ks k.succ) (jordanChain (fun j : Fin m => Ks j.succ) k) (Ks 0) :=
  ⟨isOrthSum_chain_tail Q h.fgL h.satL.1 k, isOrthSum_chain_tail Q h.fgK h.jordK k⟩

theorem TailData.regChain {L K : Submodule R V} {Ls Ks : Fin (m + 1) → Submodule R V}
    (h : TailData Q L K Ls Ks) (k : Fin m) :
    IsRegular Q (jordanChain (fun j : Fin m => Ls j.succ) k) ∧ IsRegular Q (jordanChain (fun j : Fin m => Ks j.succ) k) := by
  refine ⟨?_, ?_⟩
  · refine isRegular_jordanChain Q ?_ (isJordanSplitting_tail Q h.satL.1) k
    exact Submodule.FG.of_le h.fgL (tailLat_le Q h.satL.1.split)
  · refine isRegular_jordanChain Q ?_ (isJordanSplitting_tail Q h.jordK) k
    exact Submodule.FG.of_le h.fgK (tailLat_le Q h.jordK.split)

/-- **Condition (i) for the tail** (O'Meara 1963, p. 273): with $L_1=K_1$ (and $L$ saturated),
$dL_{(k+2)}/dK_{(k+2)}\cong1\bmod\mathfrak f_{k+2}$ holds iff $dL^*_{(k+1)}/dK^*_{(k+1)}\cong1\bmod\mathfrak f_{k+1}(L^*)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (condition (i) for L*, K*)"]
theorem cond1_tail (h : TailData Q L K Ls Ks) (k l : Fin m) :
    Cond1 Q L Ls K Ks k.succ l.succ ↔
      Cond1 Q (tailLat Ls) (fun j : Fin m => Ls j.succ) (tailLat Ks) (fun j : Fin m => Ks j.succ) k l := by
  unfold Cond1
  rw [fIdeal_tail Q h.satL k l]
  obtain ⟨hM, hN⟩ := h.orthSums Q k
  obtain ⟨hMfg, hNfg⟩ := h.fgChain Q k
  exact (discQuot_isOrthSum_iff Q hM hN (h.iso Q) hMfg hNfg (h.fgFirst Q) (h.regChain Q k).2 (h.regFirst Q)
    (h.regFirst' Q))

/-- **Condition (ii) for the tail.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (condition (ii) for L*, K*)"]
theorem cond2_tail (h : TailData Q L K Ls Ks) (a : Fin (m + 1) → F) (k l : Fin m) (hc : a l.succ ≠ 0) :
    Cond2 Q L Ls K Ks a k.succ l.succ ↔
      Cond2 Q (tailLat Ls) (fun j : Fin m => Ls j.succ) (tailLat Ks) (fun j : Fin m => Ks j.succ)
        (fun j => a j.succ) k l := by
  unfold Cond2
  rw [fIdeal_tail Q h.satL k l, fundWeight_tail Q h.satL l]
  obtain ⟨hM, hN⟩ := h.orthSums Q k
  obtain ⟨hMreg, hNreg⟩ := h.regChain Q k
  have := spanRepresents_iff_of_orthSum Q hM hN hMreg hNreg (h.regFirst Q) (h.fgFirst Q) (h.iso Q) hc
  rw [this]

/-- **Condition (iii) for the tail.** -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (condition (iii) for L*, K*)"]
theorem cond3_tail (h : TailData Q L K Ls Ks) (a : Fin (m + 1) → F) (k l : Fin m) (hc : a k.succ ≠ 0) :
    Cond3 Q L Ls K Ks a k.succ l.succ ↔
      Cond3 Q (tailLat Ls) (fun j : Fin m => Ls j.succ) (tailLat Ks) (fun j : Fin m => Ks j.succ)
        (fun j => a j.succ) k l := by
  unfold Cond3
  rw [fIdeal_tail Q h.satL k l, fundWeight_tail Q h.satL k]
  obtain ⟨hM, hN⟩ := h.orthSums Q k
  obtain ⟨hMreg, hNreg⟩ := h.regChain Q k
  have := spanRepresents_iff_of_orthSum Q hM hN hMreg hNreg (h.regFirst Q) (h.fgFirst Q) (h.iso Q) hc
  rw [this]

/-! ### (S3) Gluing the isometry of the tails -/

theorem isOrthSplit_two {L P L' : Submodule R V} (h : IsOrthSum Q L P L') : IsOrthSplit Q L ![P, L'] where
  orth := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h.orth x hx y hy
    · rw [bil_comm]; exact h.orth y hy x hx
    · exact absurd rfl hij
  indep := by
    rw [iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide) (by intro k; fin_cases k <;> simp)]
    exact h.disjoint
  iSup_eq := by
    rw [← h.sup_eq]
    apply le_antisymm
    · exact iSup_le fun i => by fin_cases i <;> simp
    · exact sup_le (le_iSup ![P, L'] 0) (le_iSup ![P, L'] 1)

/-- **Gluing** (O'Meara 1963, p. 273): if $L=P\perp L^*$, $K=P\perp K^*$ and $L^*\cong K^*$ then $L\cong K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (L ≅ K from L* ≅ K*)"]
theorem isometricLat_of_tail {L P L' K K' : Submodule R V} (hfgP : P.FG) (hfgL' : L'.FG)
    (hL : IsOrthSum Q L P L') (hK : IsOrthSum Q K P K') (h : IsometricLat Q Q L' K') :
    IsometricLat Q Q L K := by
  refine isometricLat_of_isOrthSplit Q Q (isOrthSplit_two Q hL) (isOrthSplit_two Q hK) ?_ ?_
  · intro i; fin_cases i
    · exact hfgP
    · exact hfgL'
  · intro i; fin_cases i
    · exact ⟨LinearEquiv.refl R _, fun x => rfl⟩
    · exact h

end Tail

end QuadFormsKB.OMeara.SuffStep
