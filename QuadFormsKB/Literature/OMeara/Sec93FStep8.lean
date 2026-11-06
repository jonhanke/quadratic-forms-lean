/-
# O'Meara 93:28 over every dyadic field: step 8 and the induction on the scale gap

**Setting** (as in `Sec93FCore8.lean`): $R$ a Henselian discrete valuation ring with finite residue field, $F$ its
fraction field of characteristic $0$, $2$ not a unit of $R$ (a dyadic local field); lattices `Submodule R V` in a
regular quadratic space $(V, Q)$. **Indices are $0$-based**: O'Meara's $L_1, L_2$, $a_1, a_2$ are `Ls 0`, `Ls 1`,
`a 0`, `a 1`.

O'Meara's proof of the sufficiency in 93:28 (pp. 272–276) is an induction on $s_t - s_1$. In step 8 (p. 276:
$\mathfrak s_2 \subseteq \mathfrak p^2$, $a_2\mathfrak o \subseteq a_1\mathfrak p^2$, $a_1\mathfrak o \supsetneq
2\mathfrak o$) he adjoins $J \cong \langle\pi A(0,0)\rangle$ to $L$ and $K$: $L' = L \perp J$, $K' = K \perp J$ have
one more Jordan component, the same $s_t - s_1$, and $\mathfrak s'_2 = \mathfrak p$, so that "$L'$ and $K'$ will be
isometric by steps 2) and 7)", and then $L \cong K$ by 93:14. Formally:
* `SuffP P t` (`Sec93FGapChain.lean`) is the sufficiency for splittings whose scales satisfy `P`; here
  `P = gapP R G` ($\mathfrak p^G\mathfrak s_i \subseteq \mathfrak s_j$, a bound for $s_t - s_1$) and
  `P = gapP R G ∧ firstP R` (moreover $\mathfrak p\mathfrak s_1 \subseteq \mathfrak s_2$: step 8 cannot occur);
* for the bound $G$, assuming the sufficiency for all bounds $G' < G$: the splittings with `firstP` are handled by
  steps 4–7 (`CoreGen`, `CoreRouteD`) and the induction hypothesis for the tail $L_2 \perp \cdots \perp L_t$ (bound
  $G - 1$); then all splittings with bound $G$: step 8 inserts $J$ (`Insert.cond93_insLs`, `Insert.sameFund_insLs`)
  and uses the `firstP` case for $L', K'$ (same bound $G$), and cancels $J$ (`InsertJ.isometricLat_cancel_latJ`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 1–8, pp. 272–276)
* `core_or_step8`: steps 4–7, or the configuration of step 8;
* `finish_of_core`: step 3 (from $K'_1 \cong L_1$ to $L \cong K$ through the tails), for any scale predicate;
* `step8_iso`: step 8;
* `suff_gap`, `suff_all`: the sufficiency in 93:28, unconditional (over a dyadic field with `LocalHilbertField`);
* `suff_down`: moving the sufficiency from spaces in `Type (max u v)` (needed to adjoin $J$, a lattice in $F \times F$)
  to spaces in any universe;
* `dyadicClassification_all`, `dyadicClassification_nf`: **Theorem 93:28**, the second for every completion of a
  number field at a dyadic place, with no named input;
* `coreStep8`: the former named statement `CoreStep8.CoreStep8` is a theorem.
-/
import QuadFormsKB.Literature.OMeara.Sec93FGapChain
import QuadFormsKB.Literature.OMeara.Sec93FInsert
import QuadFormsKB.Literature.OMeara.Sec93FInsertJ

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Step8

universe u v

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass Core8 Gap Insert InsertJ

section Core

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **Steps 4–7 of the sufficiency, or step 8** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8,
pp. 274–276): in the good situation (both splittings saturated, components of rank $8$ with hyperbolic spaces, $L_1$
unimodular, the same fundamental invariants and (i)–(iii)), either $K$ has a new saturated Jordan splitting with
$K'_1 \cong L_1$ satisfying (i)–(iii) (steps 4–7: `CoreGen.case_split`, `CoreGen.exists_sat_sq`,
`CoreGen.route_cond`, `CoreRouteD.route_aniso`, and the cases decided by the conditions at the first index), or we are
in the configuration of step 8: $u_1 < \operatorname{ord} 2$, $u_2 \ge u_1 + 2$, $\mathfrak s_2 \subseteq \mathfrak
p^2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276"]
theorem core_or_step8 (hHil : LocalHilbertField F) {V : Type*} [AddCommGroup V] [Module F V] [Module R V]
    [IsScalarTower R F V] [FiniteDimensional F V] (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {m : ℕ} {Ls Ks : Fin (m + 2) → Submodule R V} {a : Fin (m + 2) → F}
    (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks) (hd : ∀ k, finrank R (Ls k) = 8)
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    (∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
        Cond93 Q L Ls Ks' a) ∨
    ∃ (π : R) (hπ : Irreducible π), dord hπ (a 0) < dord hπ (2 : F) ∧ dord hπ (a 0) + 2 ≤ dord hπ (a 1) ∧
        ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  suffices H : (∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T) ∨
      (dord hπ (a 0) < dord hπ (2 : F) ∧ dord hπ (a 0) + 2 ≤ dord hπ (a 1) ∧
        ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ) by
    rcases H with ⟨Ks', hKs', hTK⟩ | h8
    · left
      refine ⟨Ks', hKs', ?_, Resplit.cond93_resplit Q hHil h2p hQ hLs.1 hKs.1 hKs'.1 hS hC⟩
      have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
      obtain ⟨⟨h0, hTy⟩, -, -⟩ := hS'
      have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
      obtain ⟨hrk, hsc', hg⟩ := hTy 0
      rw [hc] at hrk hsc' hg
      have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'.1.split.iSup_eq ▸ le_iSup Ks' 0)
      have hLU : IsUnimodular Q (Ls 0) := by
        have := hLs.1.modular 0; rwa [hsc] at this
      have hKU : IsUnimodular Q (Ks' 0) := by
        have := hKs'.1.modular 0; rwa [← hsc', hsc] at this
      exact CoreHyp.isometricLat_of_hyp Q hQ hL0fg hK0fg hLU hKU hrk (by rw [hLs.2 0, hKs'.2 0, hg]) (hT 0) hTK
    · exact Or.inr ⟨π, hπ, h8⟩
  have hL0reg : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  by_cases hdec : (∀ x ∈ fIdeal Q L Ls 0 1, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
      (fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
        fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0))
  · left
    refine ⟨Ks, hKs, ?_⟩
    have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
    have ha0 : ∀ k, a k ≠ 0 := fun k =>
      (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
    have hK0fg : (Ks 0).FG := FG.of_le hKfg (hKs.1.split.iSup_eq ▸ le_iSup Ks 0)
    have hK0reg : IsRegular Q (Ks 0) := (hKs.1.modular 0).isRegular Q hK0fg
    obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
    have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
    have hrk : finrank R (Ls 0) = finrank R (Ks 0) := by have := (hTy 0).1; rwa [hc] at this
    obtain ⟨h1, h2, h3⟩ := hC 0 1 (by simp)
    have hjL : jordanChain Ls 0 = Ls 0 := jordanChain_zero Ls 0 rfl
    have hjK : jordanChain Ks 0 = Ks 0 := jordanChain_zero Ks 0 rfl
    rw [hjL, hjK] at h1 h2 h3
    rcases hdec with ⟨hX, hlt | hlt⟩
    · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 1) (h2 hlt) (hT 0)
    · exact CoreCases.exists_lagrangian_of_cond Q hL0fg hK0fg hL0reg hK0reg hrk hX h1 (ha0 0) (h3 hlt) (hT 0)
  · rcases CoreGen.case_split Q hπ hLfg hLs.1 hS.2.1 hsc with hcase | h8
    · left
      obtain ⟨Ks', hKs', hsq, x, y, D, hQx, hQy, hxy, hPD⟩ :=
        CoreGen.exists_sat_sq Q hHil h2p hQ hLs hKs hd hsc hS hC hπ hcase
      by_cases hlt : fIdeal Q L Ls 0 1 < (4 * a 1) • (1 / fundWeight Q L Ls 1) ∨
          fIdeal Q L Ls 0 1 < (4 * a 0) • (1 / fundWeight Q L Ls 0)
      · exact ⟨Ks', hKs', CoreGen.route_cond Q hHil h2p hQ hLs hKs.1 hKs'.1 hS hC (hT 0) hsq hlt⟩
      · push Not at hlt
        have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
        exact CoreRouteD.route_aniso Q hHil h2p hQ hLs hKs' hd (hT 0) hsc hS' hπ hcase hlt.1 hlt.2
          hsq hQx hQy hxy hPD
    · exact Or.inr h8

/-- **Step 3: from $K'_1 \cong L_1$ to $L \cong K$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 3,
p. 273; as `Core8.good_succN`, for splittings restricted by a scale predicate `P`): Witt's theorem moves $K'_1$ onto
$L_1$, the tails $L^*_{(2)}$, $K^*_{(2)}$ lie in the same space $(FL_1)^\perp$ and satisfy (i)–(iii), so the
sufficiency for $t - 1$ components (`ih`, for scales with `P`) gives $L \cong K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273"]
theorem finish_of_core {P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop} (hPc : ScaleClosed P) {m : ℕ}
    (ih : SuffP.{u, v} R F P (m + 1)) {V : Type v} [AddCommGroup V] [Module F V] [Module R V]
    [IsScalarTower R F V] [FiniteDimensional F V] (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {Ls Ks : Fin (m + 2) → Submodule R V} {a : Fin (m + 2) → F}
    (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hPt : P (m + 1) fun k => scale Q (Ls k.succ))
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hcore : ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
        Cond93 Q L Ls Ks' a) : IsometricLat Q Q L K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨Ks', hKs', hiso0, hC'⟩ := hcore
  have hS' := sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
  have hKle : ∀ k, Ks' k ≤ K := fun k => hKs'.1.split.iSup_eq ▸ le_iSup Ks' k
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKle 0)
  have hK0reg : IsRegular Q (Ks' 0) := (hKs'.1.modular 0).isRegular Q hK0fg
  obtain ⟨σ, hσ, hσK⟩ := SuffWitt.exists_orth_latMap_eq Q hQ hK0fg hK0reg (adj_isometricLat_symm Q Q hiso0)
  set Ks'' : Fin (m + 2) → Submodule R V := fun k => latMap σ (Ks' k) with hKs''
  have hK'lat : (latMap σ K).IsLattice F := SuffSub.isLattice_latMap
  have hK'fg : (latMap σ K).FG := Submodule.IsLattice.fg (A := F)
  have hK'sat : IsSaturated Q (latMap σ K) Ks'' := SuffSub.isSaturated_latMap Q hσ hKle hKfg hKs'
  have hS'' : SameFundamentalInvariants Q Q L (latMap σ K) Ls Ks'' a := sameFund_moveK Q hσ hKle hS'
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin (m + 2) → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hC'' : Cond93 Q L Ls Ks'' a := cond93_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
    (fun i => by rw [hKs'', ← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC'
  have h0 : Ls 0 = Ks'' 0 := hσK.symm
  obtain ⟨hSt, hCt⟩ := tail_conds Q hLfg hK'fg hLs hK'sat h0 ha0 hS'' hC''
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLle 0)
  have hLreg0 : IsRegular Q (Ls 0) := (hLs.1.modular 0).isRegular Q hL0fg
  have hoL := isOrthSum_zero_tail Q hLfg hLs.1
  have hoK := isOrthSum_zero_tail Q hK'fg hK'sat.1
  rw [← h0] at hoK
  set W := perpF Q (Ls 0) with hW
  have hspL : span F (tailLat Ls : Set V) = W := span_eq_perpF Q hLreg0 hoL
  have hspK : span F (tailLat Ks'' : Set V) = W := span_eq_perpF Q hLreg0 hoK
  have hLW : tailLat Ls ≤ W.restrictScalars R := fun x hx => hspL ▸ subset_span hx
  have hKW : tailLat Ks'' ≤ W.restrictScalars R := fun x hx => hspK ▸ subset_span hx
  have hLtfg : (tailLat Ls).FG := FG.of_le hLfg (tailLat_le Q hLs.1.split)
  have hKtfg : (tailLat Ks'').FG := FG.of_le hK'fg (tailLat_le Q hK'sat.1.split)
  have hLWl := SuffSub.isLattice_subLatIn hLW hLtfg hspL
  have hKWl := SuffSub.isLattice_subLatIn hKW hKtfg hspK
  have hQW : (QuadraticMap.associated (SuffSub.QW Q W)).Nondegenerate :=
    SuffSub.nondegenerate_QW Q hQ (span_sup_perpF Q hLreg0 hoL) fun w hw u hu => perpF_orth_span Q hw hu
  have hsLs : ∀ i : Fin (m + 1), Ls i.succ ≤ tailLat Ls := fun i => le_iSup (fun k : Fin (m + 1) => Ls k.succ) i
  have hsKs : ∀ i : Fin (m + 1), Ks'' i.succ ≤ tailLat Ks'' := fun i =>
    le_iSup (fun k : Fin (m + 1) => Ks'' k.succ) i
  have hJL := SuffSub.isJordanSplitting_subLatIn Q hLW hsLs hLtfg (isJordanSplitting_tail Q hLs.1)
  have hJK := SuffSub.isJordanSplitting_subLatIn Q hKW hsKs hKtfg (isJordanSplitting_tail Q hK'sat.1)
  have hSW := (SuffSub.sameFundamentalInvariants_subLatIn Q hLW hKW hsLs hsKs _).mp hSt
  have hCW := (SuffSub.cond93_subLatIn Q hLW hKW hsLs hsKs hLtfg hKtfg _).mp hCt
  have hPW : P (m + 1) fun k => scale (SuffSub.QW Q W) (SuffSub.subLatIn W (Ls k.succ)) :=
    hPc.of_eq (fun k => SuffSub.scale_subLatIn Q hLW (hsLs k)) hPt
  have hisoW := ih (SuffSub.QW Q W) h2p hQW _ _ _ _ _ hJL hJK hPW hSW hCW
  have hisoT := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK' := isometricLat_of_tail Q hL0fg hLtfg hoL hoK hisoT
  exact adj_isometricLat_trans Q Q Q hLK' (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))

end Core

section Gap

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type u} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- A gap bound for at least two components is positive, and the tail $L_2 \perp \cdots \perp L_t$ has bound
$G - 1$ (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 1, p. 272: the induction on $s_t - s_1$). -/
theorem gap_tail (Q : QuadraticForm F V) {L : Submodule R V} (hfg : L.FG) {m : ℕ}
    {Ls : Fin (m + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) {G : ℕ}
    (hG : gapP R G (m + 2) fun k => scale Q (Ls k)) :
    1 ≤ G ∧ gapP R (G - 1) (m + 1) fun k => scale Q (Ls k.succ) := by
  have hG1 : 1 ≤ G := by
    by_contra h0
    obtain rfl : G = 0 := by omega
    have hlt : scale Q (Ls (Fin.succ 0)) < scale Q (Ls 0) := hL.scale_strictAnti (Fin.succ_pos 0)
    refine hlt.not_ge fun x hx => ?_
    have := hG 0 (Fin.succ 0) 1 (by simp) x hx
    rwa [one_smul] at this
  exact ⟨hG1, gapLe_tail Q hfg hL hG1 hG⟩

/-- **Step 8 does not occur when $\mathfrak p\mathfrak s_1 \subseteq \mathfrak s_2$**: with $\mathfrak s_1 =
\mathfrak o$ this forces $\operatorname{ord}\mathfrak s_2 \le 1$. -/
theorem not_step8_of_firstP (Q : QuadraticForm F V) {m : ℕ} {Ls : Fin (m + 2) → Submodule R V}
    (hP : firstP R (m + 2) fun k => scale Q (Ls k)) (hsc : scale Q (Ls 0) = 1) {π : R} (hπ : Irreducible π) :
    ¬ ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ := by
  rintro ⟨τ, hτ, hd⟩
  have hπm : π ∈ maximalIdeal R := (mem_maximalIdeal _).2 hπ.not_isUnit
  have h1 : (1 : F) ∈ scale Q (Ls 0) := by rw [hsc]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have hm := hP 0 1 rfl rfl π hπm 1 h1
  beta_reduce at hm
  rw [hτ, Algebra.smul_def, mul_one] at hm
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
  have hϖ0 : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have hr0 : r ≠ 0 := by rintro rfl; rw [zero_smul] at hr; exact hϖ0 hr.symm
  have hτ0 : τ ≠ 0 := by rintro rfl; rw [smul_zero] at hr; exact hϖ0 hr.symm
  rw [Algebra.smul_def] at hr
  have := congrArg (dord hπ) hr
  rw [dord_mul hπ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hr0) hτ0, dord_pi hπ] at this
  have := dord_alg_nonneg (F := F) hπ hr0
  omega

/-- **The scales of $L \perp J$ have the same gap bound and satisfy `firstP`** ($\mathfrak s'_1 = \mathfrak o$,
$\mathfrak s'_{1\frac12} = \mathfrak p$). -/
theorem gapP_insLs (Q : QuadraticForm F V) {π : R} (hπ : Irreducible π) {W : Type*} [AddCommGroup W]
    [Module F W] [Module R W] [IsScalarTower R F W] (QW : QuadraticForm F W) {J : Submodule R W}
    (hJs : scale QW J = R ∙ algebraMap R F π) {L : Submodule R V} {m : ℕ}
    {Ls : Fin (m + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hsc : scale Q (Ls 0) = 1) {G : ℕ}
    (hG1 : 1 ≤ G) (hG : gapP R G (m + 2) fun k => scale Q (Ls k)) :
    gapP R G (m + 3) (fun k => scale (Q.prod QW) (insLs Ls J k)) ∧
      firstP R (m + 3) (fun k => scale (Q.prod QW) (insLs Ls J k)) := by
  have hmax : maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have hmem : ∀ r ∈ maximalIdeal R, ∀ x ∈ (1 : Submodule R F), r • x ∈ R ∙ algebraMap R F π := by
    intro r hr x hx
    rw [hmax, Ideal.mem_span_singleton'] at hr
    obtain ⟨r', rfl⟩ := hr
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    exact Submodule.mem_span_singleton.2 ⟨r' * y, by simp [Algebra.smul_def]; ring⟩
  have hle1 : ∀ i, scale Q (Ls i) ≤ 1 := fun i => hsc ▸ hL.scale_strictAnti.antitone (Fin.zero_le i)
  have hp1 : R ∙ algebraMap R F π ≤ (1 : Submodule R F) := by
    rw [span_singleton_le_iff_mem]; exact Submodule.mem_one.2 ⟨π, rfl⟩
  have hpowG : maximalIdeal R ^ G ≤ maximalIdeal R := Ideal.pow_le_self (by omega)
  have hs1 : scale (Q.prod QW) (insLs Ls J 1) = R ∙ algebraMap R F π := by rw [scale_insLs_one]; exact hJs
  refine ⟨fun i j r hr x hx => ?_, fun i j hi hj r hr x hx => ?_⟩
  · beta_reduce at hx ⊢
    by_cases hi : i = 1
    · subst hi
      rw [hs1] at hx
      by_cases hj : j = 1
      · subst hj; rw [hs1]; exact Submodule.smul_mem _ r hx
      · rw [scale_insLs_of_ne_one Q QW hj]
        exact hG 0 _ r hr x (show x ∈ scale Q (Ls 0) by rw [hsc]; exact hp1 hx)
    · rw [scale_insLs_of_ne_one Q QW hi] at hx
      by_cases hj : j = 1
      · subst hj; rw [hs1]; exact hmem r (hpowG hr) x (hle1 _ hx)
      · rw [scale_insLs_of_ne_one Q QW hj]; exact hG _ _ r hr x hx
  · beta_reduce at hx ⊢
    obtain rfl : i = 0 := Fin.ext hi
    obtain rfl : j = 1 := Fin.ext (by simpa using hj)
    rw [hs1]
    rw [scale_insLs_of_ne_one Q QW Fin.zero_ne_one] at hx
    exact hmem r hr x (hle1 _ hx)

end Gap

section Induction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **Step 8** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, pp. 275–276): in the configuration
$\mathfrak s_1 = \mathfrak o$, $\mathfrak s_2 \subseteq \mathfrak p^2$, $u_1 < \operatorname{ord} 2$, $u_2 \ge u_1 + 2$,
the lattices $L' = L \perp J$, $K' = K \perp J$ ($J = \pi A(0,0)$, `InsertJ.latJ`) with the inserted Jordan splittings
have the same fundamental invariants and satisfy (i)–(iii) (`Insert.sameFund_insLs`, `Insert.cond93_insLs`), have the
same gap bound and $\mathfrak s'_2 = \mathfrak p$; so the sufficiency for such splittings (`hB`) gives $L' \cong K'$,
and 93:14 cancels $J$ (`InsertJ.isometricLat_cancel_latJ`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, pp. 275–276"]
theorem step8_iso {G m : ℕ}
    (hB : SuffP.{u, max u v} R F (fun t s => gapP R G t s ∧ firstP R t s) (m + 3))
    {V : Type (max u v)} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {L K : Submodule R V} [hLl : L.IsLattice F] [hKl : K.IsLattice F] {Ls Ks : Fin (m + 2) → Submodule R V}
    {a : Fin (m + 2) → F} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a)
    (hG : gapP R G (m + 2) fun k => scale Q (Ls k)) {π : R} (hπ : Irreducible π)
    (h8a : dord hπ (a 0) < dord hπ (2 : F)) (h8b : dord hπ (a 0) + 2 ≤ dord hπ (a 1))
    (h8c : ∃ τ : F, scale Q (Ls 1) = R ∙ τ ∧ 2 ≤ dord hπ τ) : IsometricLat Q Q L K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hϖ0 : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ0
  set QW : QuadraticForm F (F × F) := QJ (R := R) π with hQW
  set J : Submodule R (F × F) := latJ with hJdef
  have hJs : scale QW J = R ∙ algebraMap R F π := scale_latJ π hπ0
  have hJ : InsHyp QW π J := ⟨latJ_fg, hJs, by rw [hJs]; exact isModular_latJ π hπ0, normGroup_latJ_le π hπ0,
    fun s hs => normGroup_subA_latJ_le π s hs⟩
  have h8 : Step8Conf Q π hπ Ls a := by
    refine ⟨hsc, ?_, h8a, h8b⟩
    obtain ⟨τ, hτ, hdτ⟩ := h8c
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      exact (hL.modular 1).1 (by rw [hτ, span_singleton_eq_bot.2 rfl])
    rw [hτ, span_singleton_le_iff_mem]
    refine CoreFactor.mem_span_of_dord Q hπ (pow_ne_zero 2 hϖ0) fun _ => ?_
    rw [pow_two, dord_mul hπ hϖ0 hϖ0, dord_pi hπ]; omega
  have hG1 := (gap_tail Q hLfg hL hG).1
  have hL' := h8.jordan Q QW hJ hLfg hL
  have hK' := (h8.of_sameFund Q hS).jordan Q QW hJ hKfg hK
  have hLJ : (L.prod J).IsLattice F := isLattice_prod hLl isLattice_latJ
  have hKJ : (K.prod J).IsLattice F := isLattice_prod hKl isLattice_latJ
  have hQn : (QuadraticMap.associated (Q.prod QW)).Nondegenerate :=
    nondegenerate_prod Q QW hQ (nondegenerate_QJ π hπ0)
  have hreg : IsRegular (Q.prod QW) (L.prod J) := isRegular_of_lattice_max (Q.prod QW) hQn hLJ
  have hiso := hB (Q.prod QW) h2p hQn (L.prod J) (K.prod J) (insLs Ls J) (insLs Ks J)
    (insA a (algebraMap R F π ^ 2 * a 0)) hL' hK' (gapP_insLs Q hπ QW hJs hL hsc hG1 hG)
    (sameFund_insLs Q QW hπ hLfg hKfg hL hK hJs hsc (h8.sc1_lt Q).le hJ.normGroup_le hJ.normGroup_subA_le hS
      h8a h8b)
    (cond93_insLs Q QW h2p h8 hJ hLfg hKfg hL hK hreg hS hC)
  exact isometricLat_cancel_latJ Q hπ0 hiso

/-- The sufficiency for at most one component holds for every scale predicate. -/
theorem suffP_of_suff {P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop} {t : ℕ} (h : Suff.{u, v} R F t) :
    SuffP.{u, v} R F P t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hL hK _ hS hC
  exact h Q h2p hQ L K Ls Ks a hL hK hS hC

/-- **The good case with $\mathfrak p\mathfrak s_1 \subseteq \mathfrak s_2$** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, steps 3–7, pp. 273–275): for splittings with gap bound $G$ whose first two scales satisfy `firstP`, from
the sufficiency for all smaller bounds; step 8 cannot occur (`not_step8_of_firstP`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 3–7, pp. 273–275 (induction on s_t − s_1)"]
theorem good_first (hHil : LocalHilbertField F) {G m : ℕ}
    (ih : ∀ G' < G, ∀ t, SuffP.{u, v} R F (gapP R G') t) :
    GoodSuffNP.{u, v} R F 8 (fun t s => gapP R G t s ∧ firstP R t s) (m + 2) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hP hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  obtain ⟨hG1, hGt⟩ := gap_tail Q hLfg hLs.1 hP.1
  rcases core_or_step8 hHil Q h2p hQ hLs hKs hd hT (hsc 0 rfl) hS hC with hcore | ⟨π, hπ, -, -, h8c⟩
  · exact finish_of_core (scaleClosed_gapP (G - 1)) (ih (G - 1) (by omega) (m + 1)) Q h2p hQ hLs hKs hGt hS hcore
  · exact absurd h8c (not_step8_of_firstP Q hP.2 (hsc 0 rfl) hπ)

/-- **The good case, all splittings with gap bound $G$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
steps 3–8, pp. 273–276): steps 4–7 and the induction hypothesis for the tail, or step 8 (`step8_iso`) with the case
`good_first` of the same bound for the enlarged lattices. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 3–8, pp. 273–276 (induction on s_t − s_1)"]
theorem good_all (hHil : LocalHilbertField F) {G m : ℕ}
    (ih : ∀ G' < G, ∀ t, SuffP.{u, max u v} R F (gapP R G') t)
    (hB : ∀ t, SuffP.{u, max u v} R F (fun t s => gapP R G t s ∧ firstP R t s) t) :
    GoodSuffNP.{u, max u v} R F 8 (gapP R G) (m + 2) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hP hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  obtain ⟨hG1, hGt⟩ := gap_tail Q hLfg hLs.1 hP
  rcases core_or_step8 hHil Q h2p hQ hLs hKs hd hT (hsc 0 rfl) hS hC with hcore | ⟨π, hπ, h8a, h8b, h8c⟩
  · exact finish_of_core (scaleClosed_gapP (G - 1)) (ih (G - 1) (by omega) (m + 1)) Q h2p hQ hLs hKs hGt hS hcore
  · exact step8_iso (hB (m + 3)) Q h2p hQ hLs.1 hKs.1 (hsc 0 rfl) hS hC hP hπ h8a h8b h8c

/-- The sufficiency for splittings with gap bound $G$ and `firstP`, from all smaller bounds (the reduction chain
`Gap.suff_of_goodP` applied to `good_first`). -/
theorem suff_first (hHil : LocalHilbertField F) {G : ℕ} (ih : ∀ G' < G, ∀ t, SuffP.{u, v} R F (gapP R G') t) :
    ∀ t, SuffP.{u, v} R F (fun t s => gapP R G t s ∧ firstP R t s) t
  | 0 => suffP_of_suff.{u, v} (P := fun t s => gapP R G t s ∧ firstP R t s) suff_zero.{u, v}
  | 1 => suffP_of_suff.{u, v} (P := fun t s => gapP R G t s ∧ firstP R t s) suff_one.{u, v}
  | m + 2 => by
    have hPc := (scaleClosed_gapP (R := R) (F := F) G).and (scaleClosed_firstP (R := R) (F := F))
    exact suff_of_goodP.{u, v} hHil hPc (goodSuff_of_goodSuff4P.{u, v} hHil hPc
      (goodSuff4_of_goodSuff8P.{u, v} hPc (good_first.{u, v} (m := m) hHil ih)))

/-- The sufficiency for gap bound $G$ from all smaller bounds (the reduction chain applied to `good_all`, with
`suff_first` for the enlarged lattices of step 8). -/
theorem suff_gap_step (hHil : LocalHilbertField F) (G : ℕ)
    (ih : ∀ G' < G, ∀ t, SuffP.{u, max u v} R F (gapP R G') t) : ∀ t, SuffP.{u, max u v} R F (gapP R G) t
  | 0 => suffP_of_suff.{u, max u v} (P := gapP R G) suff_zero.{u, max u v}
  | 1 => suffP_of_suff.{u, max u v} (P := gapP R G) suff_one.{u, max u v}
  | m + 2 => by
    have hPc := scaleClosed_gapP (R := R) (F := F) G
    exact suff_of_goodP.{u, max u v} hHil hPc (goodSuff_of_goodSuff4P.{u, max u v} hHil hPc
      (goodSuff4_of_goodSuff8P.{u, max u v} hPc (good_all.{u, v} (m := m) hHil ih (suff_first hHil ih))))

/-- **The sufficiency in 93:28 for splittings with gap bound $G$** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 1, p. 272: "by induction on $s_t - s_1$"), by strong induction on $G$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 1–8, pp. 272–276 (induction on s_t − s_1)"]
theorem suff_gap (hHil : LocalHilbertField F) (G : ℕ) : ∀ t, SuffP.{u, max u v} R F (gapP R G) t :=
  Nat.strong_induction_on G fun G ih => suff_gap_step hHil G ih

/-- **The sufficiency in 93:28** (O'Meara 1963, §93F, pp. 272–276), unconditional over a dyadic field with
`LocalHilbertField`: every Jordan splitting has a gap bound (`Gap.exists_gapLe`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, pp. 272–276"]
theorem suff_all (hHil : LocalHilbertField F) (t : ℕ) : Suff.{u, max u v} R F t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hL hK hS hC
  obtain ⟨G, hG⟩ := exists_gapLe Q (Submodule.IsLattice.fg (A := F)) hL
  exact suff_gap hHil G t Q h2p hQ L K Ls Ks a hL hK hG hS hC

/-- **Changing the universe of the space** (the device of `Sat93.saturatedSplittingExistence`): the sufficiency for
spaces in `Type (max u v)` gives it for spaces in `Type v`, by moving everything to `ULift V` along the isometry
$V \to$ `ULift V` (`SuffSub` transport lemmas). -/
theorem suff_down {t : ℕ} (h : Suff.{u, max u v} R F t) : Suff.{u, v} R F t := by
  intro V _ _ _ _ _ Q h2p hQ L K hLl hKl Ls Ks a hL hK hS hC
  let eF : ULift.{u} V ≃ₗ[F] V := ULift.moduleEquiv
  have : FiniteDimensional F (ULift.{u} V) := Module.Finite.equiv eF.symm
  let Q₁ : QuadraticForm F (ULift.{u} V) := Q.comp eF.toLinearMap
  let φ : V →ₗ[F] ULift.{u} V := eF.symm.toLinearMap
  have hinj : Function.Injective φ := eF.symm.injective
  have hφ : ∀ x, Q₁ (φ x) = Q x := fun x => by simp [Q₁, φ]
  have hb : ∀ x y, QuadraticMap.associated Q₁ x y = QuadraticMap.associated Q (eF x) (eF y) := fun x y => by
    simp [Q₁, QuadraticMap.associated_comp]
  have hQ₁ : (QuadraticMap.associated Q₁).Nondegenerate := by
    refine ⟨fun x hx => eF.injective ?_, fun y hy => eF.injective ?_⟩
    · rw [map_zero]
      exact hQ.1 _ fun z => by have := hx (eF.symm z); rwa [hb, eF.apply_symm_apply] at this
    · rw [map_zero]
      exact hQ.2 _ fun z => by have := hy (eF.symm z); rwa [hb, eF.apply_symm_apply] at this
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hlat : ∀ {X : Submodule R V}, X.IsLattice F → (SuffSub.mapLat φ X).IsLattice F := fun {X} hX => by
    refine ⟨hX.fg.map _, ?_⟩
    have e : ((SuffSub.mapLat φ X : Submodule R (ULift.{u} V)) : Set (ULift.{u} V)) = φ '' (X : Set V) := by
      ext y; simp [SuffSub.mapLat]
    rw [e, ← Submodule.map_span, hX.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact eF.symm.surjective
  have hLs : ∀ i, Ls i ≤ L := fun i => hL.split.iSup_eq ▸ le_iSup Ls i
  have hKs : ∀ i, Ks i ≤ K := fun i => hK.split.iSup_eq ▸ le_iSup Ks i
  have hJL := SuffSub.isJordanSplitting_map Q₁ Q hinj hφ hLfg hL
  have hJK := SuffSub.isJordanSplitting_map Q₁ Q hinj hφ hKfg hK
  have hS' := (SuffSub.sameFundamentalInvariants_map Q₁ Q hinj hφ hLs hKs a).2 hS
  have hC' := (SuffSub.cond93_map Q₁ Q hinj hφ hLs hKs hLfg hKfg a).2 hC
  have := @h (ULift.{u} V) _ _ _ _ _ Q₁ h2p hQ₁ _ _ (hlat hLl) (hlat hKl) _ _ a hJL hJK hS' hC'
  exact (SuffSub.isometricLat_map_iff Q₁ Q hinj hφ).1 this

end Induction

section Final

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28** (O'Meara 1963, §93F, pp. 267–276), over a dyadic field with `LocalHilbertField`, with no named
input: necessity `Main28.necessity`, sufficiency `suff_all` (moved to the universe of $V$ by `suff_down`). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276"]
theorem dyadicClassification_all (Q : QuadraticForm F V) (hHil : ∀ [CharZero F], LocalHilbertField F) :
    DyadicClassification R Q := by
  refine ⟨fun h2p hQ L K _ _ t Ls Ks a hL hK hS => ?_⟩
  have : CharZero F := Main28.charZero_of_dyadic (R := R) h2p
  refine ⟨Main28.necessity Q hHil h2p hQ hL hK hS, fun hC => ?_⟩
  exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q
    (suff_down.{u, v} (suff_all.{u, v} hHil t) Q h2p hQ L K Ls Ks a hL hK hS hC))).symm

/-- **The former named input `CoreStep8.CoreStep8` is a theorem** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 8, pp. 275–276): in its situation $L \cong K$ by `suff_all`; Witt's theorem extends the isometry to $\sigma \in
O(V)$ with $\sigma L = K$, and $K = \sigma L_1 \perp \cdots \perp \sigma L_t$ is a saturated splitting whose first space
$\sigma(FL_1)$ is hyperbolic. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, pp. 275–276"]
theorem coreStep8 [CharZero F] (hHil : LocalHilbertField F) : CoreStep8.CoreStep8.{u, v} R F := by
  refine ⟨fun {V} _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs _ hT _ hS hC _ π hπ _ _ _ => ?_⟩
  have hiso := suff_down.{u, v} (suff_all.{u, v} hHil (m + 2)) Q h2p hQ L K Ls Ks a hLs.1 hKs.1 hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hLreg := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  obtain ⟨σ, hσ, hσL⟩ := SuffWitt.exists_orth_latMap_eq Q hQ hLfg hLreg hiso
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  refine ⟨fun k => latMap σ (Ls k), by rw [← hσL]; exact SuffSub.isSaturated_latMap Q hσ hLle hLfg hLs, ?_⟩
  obtain ⟨T, hT0, hTs, hTd⟩ := hT 0
  refine ⟨T.map (σ : V →ₗ[F] V), ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hσ x).trans (hT0 x hx)
  · rintro _ ⟨x, hx, rfl⟩
    show σ x ∈ span F (latMap σ (Ls 0) : Set V)
    rw [span_latMap]
    exact ⟨x, hTs x hx, rfl⟩
  · obtain ⟨f, -⟩ := isometricLat_latMap Q hσ (Ls 0)
    rw [← f.finrank_eq, LinearEquiv.finrank_map_eq]
    exact hTd

end Final

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (w.adicCompletion F) V] [FiniteDimensional (w.adicCompletion F) V]
  [Module (w.adicCompletionIntegers F) V] [IsScalarTower (w.adicCompletionIntegers F) (w.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field at a dyadic place** (O'Meara 1963, §93F,
pp. 267–276), unconditional: two lattices $L$, $K$ on a regular quadratic space with Jordan splittings of the same
fundamental invariants are isometric if and only if conditions (i)–(iii) hold. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field)"]
theorem dyadicClassification_nf (Q : QuadraticForm (w.adicCompletion F) V) :
    DyadicClassification (w.adicCompletionIntegers F) Q :=
  dyadicClassification_all.{0, v} Q (HasseIsoNF.localHilbertField_adicCompletion w)

end NumberField

end QuadFormsKB.OMeara.Step8
