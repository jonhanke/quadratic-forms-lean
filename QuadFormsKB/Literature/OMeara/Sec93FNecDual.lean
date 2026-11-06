/-
# O'Meara 93:28, proof of the necessity, step 2: condition (i) at the last index, by duality

**Setting** (as in `Sec93Dual.lean`): $R$ a Henselian discrete valuation ring with finite residue field, $F$ its fraction
field of characteristic $0$ with the Hilbert-symbol axioms `LocalHilbertField`, $2$ not a unit; $(V, Q)$ a regular
quadratic space; $L$ a lattice on $V$ with two Jordan splittings $L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots
\perp K_t$ (indices $0$-based). $L^\#$ is `dual Q L` with the splittings `dualSplit σ Ls` of 93:24.

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity, step 2, p. 271)
* `nec_disc_last`: if all $\dim L_k \ge 3$, the splitting $L_1 \perp \cdots \perp L_t$ is saturated, and $L_t$ is
  unimodular with a base of matrix $A(a', 0) \perp A(a'', 0)$, then $dL_{(t-1)}/dK_{(t-1)} \cong 1 \bmod
  \mathfrak f_{t-1}$. "Form $L^\#$. Then $L_t$ and $K_t$ are first components in the Jordan splittings of $L^\#$ ...
  $L^\#$ satisfies (i) ... So $dL_t/dK_t \cong 1 \bmod \mathfrak f_1^\#$. But $\mathfrak f_1^\# = \mathfrak f_{t-1}$
  by Example 93:24, and $dL_{(t-1)}\cdot dL_t = dK_{(t-1)}\cdot dK_t$."
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecBase
import QuadFormsKB.Literature.OMeara.Sec93FNecBlock
import QuadFormsKB.Literature.OMeara.Sec93FTransfer
import QuadFormsKB.Literature.OMeara.Sec93Dual

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecDual

open Sat93 Transfer28 NecBase D18 NecBlock

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- $(R\cdot 1)\, L = L$. -/
theorem span_one_smul (L : Submodule R V) : (R ∙ (1 : F)) • L = L := by
  ext v
  rw [mem_span_singleton_smul_iff]
  exact ⟨fun ⟨x, hx, hxv⟩ => by rw [← hxv, one_smul]; exact hx, fun hv => ⟨v, hv, one_smul F v⟩⟩

/-- **93:28, necessity, condition (i) at the last index, by duality** (O'Meara 1963, p. 271). -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 2, p. 271 (condition (i) via L^#)"]
theorem nec_disc_last (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hjt : j.val + 1 = t) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {a' a'' : F} (hblk : HasBlk Q (Ls j) a' 0 a'' 0) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  classical
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hS := saturatedSplittingExistence (R := R) hK Q
  -- scale generators, with `σ j = 1`
  have hsc0 : ∀ k, ∃ σ : F, σ ≠ 0 ∧ scale Q (Ls k) = R ∙ σ := fun k =>
    exists_eq_span_singleton (R := R)
      ((hL.modular k).2.1 ▸ scale_fg Q (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k))) (hL.modular k).1
  choose σ₀ hσ₀0 hσ₀ using hsc0
  set σ : Fin t → F := Function.update σ₀ j 1 with hσdef
  have hσ : ∀ k, scale Q (Ls k) = R ∙ σ k := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hσdef, Function.update_self, hU, Submodule.one_eq_span]
    · rw [hσdef, Function.update_of_ne hk]; exact hσ₀ k
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hc : ∀ k, Fin.cast hT k = k := fun k => Fin.ext (by simp)
  have hscK : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [hc] at this; exact this.symm
  have hσK : ∀ k, scale Q (Ks k) = R ∙ σ k := fun k => (hscK k).trans (hσ k)
  -- the dual lattice and its two splittings
  have hreg : IsRegular Q L := isRegular_of_isJordanSplitting Q hfg hL
  have : (dual Q L).IsLattice F := Dual93.isLattice_dual Q hreg
  obtain ⟨hM, hMsc⟩ := isJordanSplitting_dual Q hL hσ
  obtain ⟨hN, -⟩ := isJordanSplitting_dual Q hK' hσK
  have ht : 0 < t := by omega
  set j' : Fin t := ⟨0, ht⟩ with hj'
  set i' : Fin t := ⟨1, by omega⟩ with hi'
  have hrj : Fin.rev j' = j := Fin.ext (by simp [hj', Fin.val_rev]; omega)
  have hri : Fin.rev i' = i := Fin.ext (by simp [hi', Fin.val_rev]; omega)
  have hMj : Dual93.dualSplit σ Ls j' = Ls j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ls j)
  have hNj : Dual93.dualSplit σ Ks j' = Ks j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ks j)
  have hUM : scale Q (Dual93.dualSplit σ Ls j') = 1 := by rw [hMj, hU]
  have hblkM : HasBlk Q (Dual93.dualSplit σ Ls j') a' 0 a'' 0 := by rw [hMj]; exact hblk
  have haM := isFundNormGenerators_dual Q hS h2p hQ hL hdim hsat hσ ha
  have hbase := nec_base_disc Q h2 (dual_fg Q hfg hreg) hM hN j' i' rfl rfl haM hUM hblkM
  rw [jordanChain_zero _ j' rfl, jordanChain_zero _ j' rfl] at hbase
  change DiscQuotSqEquivMod Q (Dual93.dualSplit σ Ls j') (Dual93.dualSplit σ Ks j')
    (fIdeal Q (dual Q L) (Dual93.dualSplit σ Ls) j' i') at hbase
  rw [hMj, hNj, fIdeal_dual Q hS h2p hQ hL hdim hsat hσ, hri, hrj] at hbase
  -- back to the Jordan chains: `L = L_(i) ⊥ L_j = K_(i) ⊥ K_j`
  have hsL := isOrthSum_jordanChain Q hL.split i j hij
  have hsK := isOrthSum_jordanChain Q hK'.split i j hij
  rw [invJordanChain_last' Ls j hjt] at hsL
  rw [invJordanChain_last' Ks j hjt] at hsK
  have hregK : IsRegular Q (jordanChain Ks i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsK.sup_eq ▸ le_sup_left))
      (isJordanSplitting_jordanChain Q hK' i)
  have hLjfg : (Ls j).FG := FG.of_le hfg (hsL.sup_eq ▸ le_sup_right)
  have hKjfg : (Ks j).FG := FG.of_le hfg (hsK.sup_eq ▸ le_sup_right)
  exact discQuot_of_compl Q hfg hsL hsK hregK ((hL.modular j).isRegular Q hLjfg)
    ((hK'.modular j).isRegular Q hKjfg) hbase

/-- **93:28, necessity, condition (i) at the last index, by duality**, for a last component spanned by $m$ blocks
$A(c_k, 0)$ (O'Meara 1963, p. 271, with `nec_base_disc_blocks` in place of the cancellation to dimension $4$). -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 2, p. 271 (condition (i) via L^#)"]
theorem nec_disc_last_blocks (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hjt : j.val + 1 = t) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {m : ℕ} (x : Fin m → V × V) (hspan : pairSpan R x = Ls j)
    (hx2 : ∀ k, Q (x k).2 = 0) (hx12 : ∀ k, bil Q (x k).1 (x k).2 = 1)
    (hx11 : ∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) (hx12' : ∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0)
    (hx22 : ∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0) :
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := by
  classical
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hS := saturatedSplittingExistence (R := R) hK Q
  -- scale generators, with `σ j = 1`
  have hsc0 : ∀ k, ∃ σ : F, σ ≠ 0 ∧ scale Q (Ls k) = R ∙ σ := fun k =>
    exists_eq_span_singleton (R := R)
      ((hL.modular k).2.1 ▸ scale_fg Q (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k))) (hL.modular k).1
  choose σ₀ hσ₀0 hσ₀ using hsc0
  set σ : Fin t → F := Function.update σ₀ j 1 with hσdef
  have hσ : ∀ k, scale Q (Ls k) = R ∙ σ k := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hσdef, Function.update_self, hU, Submodule.one_eq_span]
    · rw [hσdef, Function.update_of_ne hk]; exact hσ₀ k
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hc : ∀ k, Fin.cast hT k = k := fun k => Fin.ext (by simp)
  have hscK : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [hc] at this; exact this.symm
  have hσK : ∀ k, scale Q (Ks k) = R ∙ σ k := fun k => (hscK k).trans (hσ k)
  -- the dual lattice and its two splittings
  have hreg : IsRegular Q L := isRegular_of_isJordanSplitting Q hfg hL
  have : (dual Q L).IsLattice F := Dual93.isLattice_dual Q hreg
  obtain ⟨hM, hMsc⟩ := isJordanSplitting_dual Q hL hσ
  obtain ⟨hN, -⟩ := isJordanSplitting_dual Q hK' hσK
  have ht : 0 < t := by omega
  set j' : Fin t := ⟨0, ht⟩ with hj'
  set i' : Fin t := ⟨1, by omega⟩ with hi'
  have hrj : Fin.rev j' = j := Fin.ext (by simp [hj', Fin.val_rev]; omega)
  have hri : Fin.rev i' = i := Fin.ext (by simp [hi', Fin.val_rev]; omega)
  have hMj : Dual93.dualSplit σ Ls j' = Ls j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ls j)
  have hNj : Dual93.dualSplit σ Ks j' = Ks j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ks j)
  have hUM : scale Q (Dual93.dualSplit σ Ls j') = 1 := by rw [hMj, hU]
  have hspanM : pairSpan R x = Dual93.dualSplit σ Ls j' := by rw [hMj]; exact hspan
  have haM := isFundNormGenerators_dual Q hS h2p hQ hL hdim hsat hσ ha
  have hbase := nec_base_disc_blocks Q h2 (dual_fg Q hfg hreg) hM hN j' i' rfl rfl haM hUM x hspanM hx2 hx12
    hx11 hx12' hx22
  rw [jordanChain_zero _ j' rfl, jordanChain_zero _ j' rfl] at hbase
  change DiscQuotSqEquivMod Q (Dual93.dualSplit σ Ls j') (Dual93.dualSplit σ Ks j')
    (fIdeal Q (dual Q L) (Dual93.dualSplit σ Ls) j' i') at hbase
  rw [hMj, hNj, fIdeal_dual Q hS h2p hQ hL hdim hsat hσ, hri, hrj] at hbase
  -- back to the Jordan chains: `L = L_(i) ⊥ L_j = K_(i) ⊥ K_j`
  have hsL := isOrthSum_jordanChain Q hL.split i j hij
  have hsK := isOrthSum_jordanChain Q hK'.split i j hij
  rw [invJordanChain_last' Ls j hjt] at hsL
  rw [invJordanChain_last' Ks j hjt] at hsK
  have hregK : IsRegular Q (jordanChain Ks i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsK.sup_eq ▸ le_sup_left))
      (isJordanSplitting_jordanChain Q hK' i)
  have hLjfg : (Ls j).FG := FG.of_le hfg (hsL.sup_eq ▸ le_sup_right)
  have hKjfg : (Ks j).FG := FG.of_le hfg (hsK.sup_eq ▸ le_sup_right)
  exact discQuot_of_compl Q hfg hsL hsK hregK ((hL.modular j).isRegular Q hLjfg)
    ((hK'.modular j).isRegular Q hKjfg) hbase

end QuadFormsKB.OMeara.NecDual
