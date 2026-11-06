/-
# O'Meara 93:28, necessity of (ii): reduction to the last index

**Setting** (as in `Sec93FNecMerge.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, step 2, pp. 270-271, for condition (ii))
* `nec_rep_merge`: the analogue of `nec_disc_merge` for representations: with the data of `nec_merge_data` ($L' =
  L_{(i)} \perp J$), the block base of $J$ is normalised (`NecRepDual.exists_normGenerator_blocks`) so that each
  $Q(x_k^{(1)})$ is a norm generator, and `nec_rep_last_blocks` gives $FK_{(i)} \to FL_{(i)} \perp \langle a_j\rangle$
  when $\mathfrak f_i \subsetneq 4a_j\mathfrak w_j^{-1}$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecMerge
import QuadFormsKB.Literature.OMeara.Sec93FNecRepLast
import QuadFormsKB.Literature.OMeara.Sec93FNecRepDual

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepMerge

open Sat93 Transfer28 NecBase NecBlock Merge28 NecMerge NecRepLast NecRepDual

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **93:28, necessity of (ii), reduced to the last index** (O'Meara 1963, §93F, proof of 93:28, step 2,
pp. 270-271): in the situation of `nec_disc_merge`, if $\mathfrak f_i \subsetneq 4a_j\mathfrak w_j^{-1}$ then
$FK_{(i)} \to FL_{(i)} \perp \langle a_j\rangle$. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of (ii), step 2, pp. 270–271 (reduction to i = t-1)"]
theorem nec_rep_merge (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (i j : Fin t) (hij : i.val + 1 = j.val) (hdim : ∀ k, 3 ≤ finrank R (Ls k))
    (hsat : IsSaturated Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls j) = 1) {T : Submodule F V} (hTiso : ∀ x ∈ T, Q x = 0)
    (hTL : ∀ x ∈ T, x ∈ span F (invJordanChain Ls j : Set V))
    (hTdim : finrank R (invJordanChain Ls j) ≤ 2 * finrank F T)
    (hlt : fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j)) :
    SpanRepresents Q (jordanChain Ks i) (jordanChain Ls i) (a j) := by
  obtain ⟨L', hlat, Ms, Ns, a', m, x, hMs, hNs, hdim', hsat', ha', hU', hxspan, hx2, hx12, hx11, hx12', hx22,
    hc1, hc2, hfI, hfw, ha'j⟩ := nec_merge_data Q hL hK' i j hij hdim hsat ha hU hTiso hTL hTdim
  haveI := hlat
  have hnorm : R ∙ a' (Fin.last (i.val + 1)) = normIdeal Q (Ms (Fin.last (i.val + 1))) := by
    have h1 := (ha' (Fin.last (i.val + 1))).2
    have h2' := Dual93.fundNormIdeal_eq_of_sat Q hsat' (Fin.last (i.val + 1))
    exact h1.trans h2'
  obtain ⟨x', hx', hxN⟩ := exists_normGenerator_blocks Q hU' ⟨hxspan, hx2, hx12, hx11, hx12', hx22⟩ hnorm
  obtain ⟨hs', h2'', h12'', h11'', h12''', h22''⟩ := hx'
  have hlt' : fIdeal Q L' Ms (Fin.last i.val).castSucc (Fin.last (i.val + 1)) <
      (4 * a' (Fin.last (i.val + 1))) • (1 / fundWeight Q L' Ms (Fin.last (i.val + 1))) := by
    rw [hfI, hfw, ha'j]; exact hlt
  have hres := nec_rep_last_blocks Q hK h2p h2 hQ hMs hNs (Fin.last i.val).castSucc (Fin.last (i.val + 1))
    (by simp) (by simp) hdim' hsat' ha' hU' x' hs' h2'' h12'' h11'' h12''' h22'' hxN hlt'
  rw [hc1, hc2, ha'j] at hres
  exact hres

end QuadFormsKB.OMeara.NecRepMerge
