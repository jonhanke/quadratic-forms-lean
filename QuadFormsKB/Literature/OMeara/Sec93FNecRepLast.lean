/-
# O'Meara 93:28, necessity of (ii), step 2: the representation at the last index, by duality

**Setting** (as in `Sec93FNecDual.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity of (ii), p. 271)
* `nec_rep_last_blocks`: if all $\dim L_k \ge 3$, the splitting $L = L_1 \perp \cdots \perp L_t$ is saturated, and
  $L_t$ is unimodular spanned by blocks $A(c_k, 0)$ whose first vectors $x_k$ have $\mathfrak o\,Q(x_k) = \mathfrak o a_t$,
  and $\mathfrak f_{t-1} \subsetneq 4a_t\mathfrak w_t^{-1}$, then $FK_{(t-1)} \to FL_{(t-1)} \perp \langle a_t\rangle$.
  Here $L^\#$ has first components $L_t$ and $K_t$ (`nec_base_rep_blocks` gives $FL_t \to FK_t \perp \langle a_t\rangle$,
  with $\mathfrak f^\#_1 = \mathfrak f_{t-1}$, $\mathfrak w^\#_1 = \mathfrak w_t$, $a^\#_1 = a_t$ by 93:24), and the
  complement step (Witt, `spanRepresents_of_orthSum_complement`) passes to $K_{(t-1)} \to L_{(t-1)} \perp \langle a_t\rangle$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecDual
import QuadFormsKB.Literature.OMeara.Sec93FNecRepBlocks
import QuadFormsKB.Literature.OMeara.Sec93FRepTransfer

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepLast

open Sat93 Transfer28 NecBase D18 NecBlock NecDual NecBlocks RepTransfer

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

set_option maxHeartbeats 1000000 in
/-- **93:28, necessity of (ii), at the last index, by duality** (O'Meara 1963, p. 271). -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of (ii), p. 271 (via L^#)"]
theorem nec_rep_last_blocks (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hjt : j.val + 1 = t) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {m : ℕ} (x : Fin m → V × V) (hspan : pairSpan R x = Ls j)
    (hx2 : ∀ k, Q (x k).2 = 0) (hx12 : ∀ k, bil Q (x k).1 (x k).2 = 1)
    (hx11 : ∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) (hx12' : ∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0)
    (hx22 : ∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0) (hxN : ∀ k, R ∙ Q (x k).1 = R ∙ a j)
    (hlt : fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j)) :
    SpanRepresents Q (jordanChain Ks i) (jordanChain Ls i) (a j) := by
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
  have hσj : σ j = 1 := by rw [hσdef, Function.update_self]
  have hMj : Dual93.dualSplit σ Ls j' = Ls j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ls j)
  have hNj : Dual93.dualSplit σ Ks j' = Ks j := by
    simp only [Dual93.dualSplit, hrj, hσdef, Function.update_self, inv_one]
    exact span_one_smul (R := R) (F := F) (Ks j)
  have hUM : scale Q (Dual93.dualSplit σ Ls j') = 1 := by rw [hMj, hU]
  have hspanM : pairSpan R x = Dual93.dualSplit σ Ls j' := by rw [hMj]; exact hspan
  have haM := isFundNormGenerators_dual Q hS h2p hQ hL hdim hsat hσ ha
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  have haeq : (σ (Fin.rev j'))⁻¹ ^ 2 * a (Fin.rev j') = a j := by rw [hrj, hσj]; simp
  have hxNM : ∀ k, IsNormGenerator Q (fundSub Q (dual Q L) (Dual93.dualSplit σ Ls) j') (Q (x k).1) := by
    intro k
    refine ⟨?_, ?_⟩
    · show Q (x k).1 ∈ fundNormGroup Q (dual Q L) (Dual93.dualSplit σ Ls) j'
      rw [← hsatM.2 j']
      exact Q_mem_normGroup Q (hspanM ▸ subset_span (Or.inl ⟨k, rfl⟩))
    · rw [hxN k, ← haeq]; exact (haM j').2
  have hwt : fundWeight Q (dual Q L) (Dual93.dualSplit σ Ls) j' = fundWeight Q L Ls j := by
    rw [fundWeight_dual Q hS h2p hQ hL hdim hsat hσ, hrj, hσj]; simp
  have hltM : fIdeal Q (dual Q L) (Dual93.dualSplit σ Ls) j' i' <
      (4 * ((σ (Fin.rev j'))⁻¹ ^ 2 * a (Fin.rev j'))) • (1 / fundWeight Q (dual Q L) (Dual93.dualSplit σ Ls) j') := by
    rw [haeq, hwt, fIdeal_dual Q hS h2p hQ hL hdim hsat hσ, hri, hrj]; exact hlt
  have hbase := nec_base_rep_blocks Q h2p h2 (dual_fg Q hfg hreg) hM hN j' i' rfl rfl haM hUM x hspanM hx2 hx12
    hx11 hx12' hx22 hxNM hltM
  rw [jordanChain_zero _ j' rfl, jordanChain_zero _ j' rfl] at hbase
  change SpanRepresents Q (Dual93.dualSplit σ Ls j') (Dual93.dualSplit σ Ks j')
    ((σ (Fin.rev j'))⁻¹ ^ 2 * a (Fin.rev j')) at hbase
  rw [hMj, hNj, haeq] at hbase
  -- back to the Jordan chains: `L = L_(i) ⊥ L_j = K_(i) ⊥ K_j`
  have hsL := isOrthSum_jordanChain Q hL.split i j hij
  have hsK := isOrthSum_jordanChain Q hK'.split i j hij
  rw [invJordanChain_last' Ls j hjt] at hsL
  rw [invJordanChain_last' Ks j hjt] at hsK
  have hregK : IsRegular Q (jordanChain Ks i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsK.sup_eq ▸ le_sup_left))
      (isJordanSplitting_jordanChain Q hK' i)
  have hregL : IsRegular Q (jordanChain Ls i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsL.sup_eq ▸ le_sup_left))
      (isJordanSplitting_jordanChain Q hL i)
  have hLjfg : (Ls j).FG := FG.of_le hfg (hsL.sup_eq ▸ le_sup_right)
  have ha0 : a j ≠ 0 := by
    rintro h0
    rw [h0] at hlt
    simp at hlt
  exact spanRepresents_of_orthSum_complement Q hsL hsK hregL hregK ((hL.modular j).isRegular Q hLjfg) ha0 hbase

end QuadFormsKB.OMeara.NecRepLast
