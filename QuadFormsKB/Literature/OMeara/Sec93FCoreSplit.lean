/-
# O'Meara 93:28, sufficiency: changing the first Jordan component

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$.

**Proves** (used in O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276, and §93G, p. 278:
"Hence $K_1 \perp K_2$ has a splitting $K_1' \perp K_2'$ ...")
* `isJordanSplitting_cons`: prepending a modular component of larger scale to a Jordan splitting;
* `exists_jordan_cons_of_compl`: if $K = K_1 \perp \cdots \perp K_t$ is a Jordan splitting and $K = A \perp C$ with
  $A$ modular of scale $\mathfrak sK_1$ and $\operatorname{rank} A = \operatorname{rank} K_1$, then $C$ has a Jordan
  splitting $C = C_2 \perp \cdots \perp C_t$ with $\mathfrak sC_i = \mathfrak sK_i$, $\dim C_i = \dim K_i$, and
  $K = A \perp C_2 \perp \cdots \perp C_t$ is a Jordan splitting (91:9).
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreCases

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreSplit

open SuffStep SuffMain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Prepending a component** (O'Meara 1963, §91C, p. 243): if $L = J \perp K$, $J$ is modular, and
$K = K_1 \perp \cdots \perp K_t$ is a Jordan splitting with $\mathfrak sK_i \subsetneq \mathfrak sJ$, then
$L = J \perp K_1 \perp \cdots \perp K_t$ is a Jordan splitting. -/
theorem isJordanSplitting_cons {L J K : Submodule R V} (hfg : L.FG) (hK : IsOrthSum Q L J K)
    (hJ : IsModular Q (scale Q J) J) {t : ℕ} {Ks : Fin t → Submodule R V} (hKs : IsJordanSplitting Q K Ks)
    (hlt : ∀ i, scale Q (Ks i) < scale Q J) :
    IsJordanSplitting Q L (Fin.cons J Ks : Fin (t + 1) → Submodule R V) := by
  have hJL : J ≤ L := hK.sup_eq ▸ le_sup_left
  have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
  have hKsle : ∀ i, Ks i ≤ K := fun i => hKs.split.iSup_eq ▸ le_iSup Ks i
  have hJreg : IsRegular Q J := hJ.isRegular Q (FG.of_le hfg hJL)
  have hKreg : ∀ i, IsRegular Q (Ks i) := fun i =>
    (hKs.modular i).isRegular Q (FG.of_le hfg ((hKsle i).trans hKL))
  refine ⟨u93_isOrthSplit_cons Q hK hKs.split hJreg hKreg, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hJ
    · simpa using hKs.modular i
  · intro i j hij
    refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hij)
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact hlt j
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij))
      simp only [Fin.cons_succ]
      exact hKs.scale_strictAnti (Fin.succ_lt_succ_iff.mp hij)

/-- The empty family is a Jordan splitting of the zero lattice. -/
theorem isJordanSplitting_bot : IsJordanSplitting Q (⊥ : Submodule R V) (Fin.elim0 : Fin 0 → Submodule R V) :=
  ⟨⟨fun i => i.elim0, fun i => i.elim0, by simp⟩, fun i => i.elim0, fun i => i.elim0⟩

/-- The scale of a lattice with a Jordan splitting is at most the scale of the first component. -/
theorem scale_le_scale_zero {L : Submodule R V} {t : ℕ} {Ls : Fin (t + 1) → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : scale Q L ≤ scale Q (Ls 0) := by
  rw [← hL.split.iSup_eq]
  refine (scale_iSup_le Q hL.split.orth).trans (iSup_le fun i => ?_)
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact le_rfl
  · exact (hL.scale_strictAnti (Fin.succ_pos j)).le

/-- **Changing the first Jordan component** (O'Meara 1963, §91C, 91:9, p. 244, as used in §93F, pp. 274–276): if
$K = K_1 \perp \cdots \perp K_t$ is a Jordan splitting and $K = A \perp C$ with $A$ modular of scale
$\mathfrak sK_1$ and $\operatorname{rank} A = \operatorname{rank} K_1$, then $C$ has a Jordan splitting
$C = C_2 \perp \cdots \perp C_t$ ($0$-based: `Cs i` for `Ks i.succ`) with the same scales and ranks as
$K_2, \dots, K_t$, and $K = A \perp C_2 \perp \cdots \perp C_t$ is a Jordan splitting. -/
@[kb "omeara1963" "§91C, 91:9, p. 244 (Jordan splittings with a prescribed first component), as used in §93F, pp. 274–276"]
theorem exists_jordan_cons_of_compl {K A C : Submodule R V} (hKfg : K.FG) {t : ℕ}
    {Ks : Fin (t + 1) → Submodule R V} (hK : IsJordanSplitting Q K Ks) (hAC : IsOrthSum Q K A C)
    (hA : IsModular Q (scale Q (Ks 0)) A) (hrk : finrank R A = finrank R (Ks 0)) :
    ∃ Cs : Fin t → Submodule R V, IsJordanSplitting Q C Cs ∧
      IsJordanSplitting Q K (Fin.cons A Cs : Fin (t + 1) → Submodule R V) ∧
      ∀ i, scale Q (Cs i) = scale Q (Ks i.succ) ∧ finrank R (Cs i) = finrank R (Ks i.succ) := by
  have hAs : scale Q A = scale Q (Ks 0) := hA.2.1
  have hAK : A ≤ K := hAC.sup_eq ▸ le_sup_left
  have hCK : C ≤ K := hAC.sup_eq ▸ le_sup_right
  have hAfg : A.FG := FG.of_le hKfg hAK
  have hCfg : C.FG := FG.of_le hKfg hCK
  have hKreg : IsRegular Q K := isRegular_of_isJordanSplitting Q hKfg hK
  have hCreg : IsRegular Q C := IsOrthSum.isRegular_right Q hAC hKreg
  have hsK := scale_le_scale_zero Q hK
  obtain ⟨t', Cs', hCs'⟩ : ∃ t', ∃ Cs' : Fin t' → Submodule R V, IsJordanSplitting Q C Cs' := by
    by_cases hC0 : C = ⊥
    · subst hC0; exact ⟨0, Fin.elim0, isJordanSplitting_bot Q⟩
    · exact exists_isJordanSplitting Q hCfg hCreg hC0
  have hCsle : ∀ i, Cs' i ≤ C := fun i => hCs'.split.iSup_eq ▸ le_iSup Cs' i
  have hle : ∀ i, scale Q (Cs' i) ≤ scale Q (Ks 0) := fun i =>
    (scale_mono Q ((hCsle i).trans hCK)).trans hsK
  -- the first scale of `C` is strictly smaller
  have hlt : ∀ i, scale Q (Cs' i) < scale Q A := by
    intro i
    rw [hAs]
    refine lt_of_le_of_ne (hle i) fun heq => ?_
    -- merge `A` with the first component of `C`
    cases t' with
    | zero => exact i.elim0
    | succ m =>
    have h0 : scale Q (Cs' 0) = scale Q (Ks 0) := by
      refine le_antisymm (hle 0) ?_
      rw [← heq]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact le_rfl
      · exact (hCs'.scale_strictAnti (Fin.succ_pos j)).le
    have hoC := isOrthSum_zero_tail Q hCfg hCs'
    obtain ⟨hX, hAB⟩ := adj_isOrthSum_assoc_left Q hAC hoC
    have hC0fg : (Cs' 0).FG := FG.of_le hCfg (hCsle 0)
    obtain ⟨hXmod, hXr⟩ := isModular_sup Q hA (h0 ▸ hCs'.modular 0) hAfg hC0fg hAB.orth
    have hXs : scale Q (A ⊔ Cs' 0) = scale Q (Ks 0) := hXmod.2.1
    have hJ := isJordanSplitting_cons Q hKfg hX (hXs.symm ▸ hXmod) (isJordanSplitting_tail Q hCs')
      (fun k => by rw [hXs, ← h0]; exact hCs'.scale_strictAnti (Fin.succ_pos k))
    obtain ⟨hT, hTy⟩ := hK.sameJordanType Q hKfg hJ
    have hr0 := (hTy 0).2.1
    have hc : Fin.cast hT 0 = 0 := Fin.ext (by simp)
    rw [hc, Fin.cons_zero] at hr0
    have hpos : 0 < finrank R (Cs' 0) := by
      rcases Nat.eq_zero_or_pos (finrank R (Cs' 0)) with hz | hz
      · exfalso
        obtain ⟨b⟩ := exists_basis (R := R) (F := F) hC0fg
        have hsc : scale Q (Cs' 0) = ⊥ := by
          rw [← span_basis_eq b, scale_span, span_eq_bot]
          rintro _ ⟨p, rfl⟩; exact Fin.elim0 (hz ▸ p.1)
        exact (hCs'.modular 0).1 hsc
      · exact hz
    omega
  have hJ := isJordanSplitting_cons Q hKfg hAC (hAs.symm ▸ hA) hCs' hlt
  obtain ⟨hT, hTy⟩ := hK.sameJordanType Q hKfg hJ
  have ht : t' = t := by omega
  subst ht
  refine ⟨Cs', hCs', hJ, fun i => ?_⟩
  obtain ⟨h1, h2, -⟩ := hTy i.succ
  have hc : Fin.cast hT i.succ = i.succ := Fin.ext (by simp)
  rw [hc, Fin.cons_succ] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

end QuadFormsKB.OMeara.CoreSplit
