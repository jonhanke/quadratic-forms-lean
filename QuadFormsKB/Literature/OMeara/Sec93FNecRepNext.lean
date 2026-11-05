/-
# O'Meara 93:28, the necessity of condition (ii)

**Setting** (as in `Sec93FNecI.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity of (ii), pp. 270-271)
* `nec_rep_core`: for Jordan splittings `Ls`, `Ks` of the same lattice, `Ls` arbitrary, $\mathfrak f_i \subsetneq
  4a_j\mathfrak w_j^{-1}$ ($j = i+1$) implies $FK_{(i)} \to FL_{(i)} \perp \langle a_j\rangle$ (the adjunctions of
  `nec_disc`, then `nec_rep_sat`);
* `nec_rep_next`: condition (ii) of 93:28, with the roles of the two splittings exchanged (the construction of $J$ is
  carried out on the splitting whose chain receives the representation).
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecRepAdjoin

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepNext

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual NecMerge Adjoin28 NecI NecII RepTransfer NecRepMerge NecRepSat NecRepAdjoin

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **93:28, necessity of (ii), for a prescribed first splitting** (O'Meara 1963, pp. 270-271): the adjunctions of
`adjoin_sat` (all dimensions $\ge 3$, saturated), then `nec_rep_sat`. -/
theorem nec_rep_core {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (h2 : (2 : R) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : i.val + 1 = j.val)
    (hlt : fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j)) :
    SpanRepresents Q (jordanChain Ks i) (jordanChain Ls i) (a j) := by
  have ha0 : a j ≠ 0 := by
    rintro h0
    rw [h0] at hlt
    simp at hlt
  obtain ⟨L₂, hl, Ls₂, Ks₂, hnd, hJ, hJK, hdim, hsat, ha₂, hfI, hfw, -, hD2⟩ := adjoin_sat Q hK h2p hQ hL hK' ha
  haveI := hl
  have h := nec_rep_sat _ hK h2p h2 hnd hJ hJK hdim hsat ha₂ i j hij (by rw [hfI, hfw]; exact hlt)
  exact hD2 _ ha0 i h

/-- **93:28, necessity of condition (ii)** (O'Meara 1963, §93F, pp. 270-271): for two Jordan splittings
$L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ of the same lattice on a regular quadratic space over a
dyadic local field, with fundamental norm generators $a_k$, and $j = i+1$: if $\mathfrak f_i \subsetneq
4a_j\mathfrak w_j^{-1}$ then $FL_{(i)} \to FK_{(i)} \perp \langle a_j\rangle$. The construction of $J$ is made on the
splitting `Ks` (`nec_rep_core` with the two splittings exchanged); the fundamental invariants do not depend on the
splitting. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of condition (ii), pp. 270–271"]
theorem nec_rep_next {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (h2 : (2 : R) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : i.val + 1 = j.val)
    (hlt : fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j)) :
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a j) := by
  have hfg : L.FG := hLl.fg
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hscKL : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [show Fin.cast hT k = k from Fin.ext (by simp)] at this; exact this.symm
  have hfs : ∀ k, fundSub Q L Ks k = fundSub Q L Ls k := fun k => by simp only [fundSub, hscKL k]
  have ha' : IsFundNormGenerators Q L Ks a := fun k => by rw [hfs k]; exact ha k
  have hfI : fIdeal Q L Ks i j = fIdeal Q L Ls i j := by simp only [fIdeal, fundNormGroup, fundNormIdeal, hfs, hscKL]
  have hfw : fundWeight Q L Ks j = fundWeight Q L Ls j := by simp only [fundWeight, hfs]
  exact nec_rep_core Q hK h2p h2 hQ hK' hL ha' i j hij (by rw [hfI, hfw]; exact hlt)

end Main

end QuadFormsKB.OMeara.NecRepNext
