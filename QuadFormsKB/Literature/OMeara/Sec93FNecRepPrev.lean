/-
# O'Meara 93:28, the necessity of condition (iii)

**Setting** (as in `Sec93FNecI.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity of (iii), step 3, p. 272: "condition (ii) for $L^\#$ ...
adjoining $V$ to each side ... by Witt's theorem")
* `spanRepresents_congr_span`, `spanRepresents_sq_mul`: `SpanRepresents` depends only on the spans, and
  $\langle\alpha^2 c\rangle \cong \langle c\rangle$;
* `span_jordanChain_dualSplit`: the span of the Jordan chain of $L^\#$ is the span of the inverse Jordan chain of $L$;
* `nec_rep_prev_sat`: for a saturated `Ls` with all dimensions $\ge 3$, $\mathfrak f_i \subsetneq 4a_i\mathfrak w_i^{-1}$
  implies $FL_{(i)} \to FK_{(i)} \perp \langle a_i\rangle$ (condition (ii) for $L^\#$, `nec_rep_sat`, then Witt);
* `nec_rep_prev`: condition (iii) of 93:28, for arbitrary Jordan splittings (`adjoin_sat` first).
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecRepNext

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecRepPrev

open Sat93 Transfer28 NecBase NecBlock Merge28 NecDual NecMerge Adjoin28 NecI NecII RepTransfer NecRepMerge NecRepSat
  NecRepAdjoin Dual93

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- `SpanRepresents` depends only on the $F$-spans of the lattices. -/
theorem spanRepresents_congr_span {M M₁ N N₁ : Submodule R V} (h1 : span F (M : Set V) = span F (M₁ : Set V))
    (h2 : span F (N : Set V) = span F (N₁ : Set V)) (c : F) :
    SpanRepresents Q M N c ↔ SpanRepresents Q M₁ N₁ c := by
  unfold SpanRepresents
  rw [h1, h2]

/-- $\langle \alpha^2 c\rangle \cong \langle c\rangle$ for representations. -/
theorem spanRepresents_sq_mul {α : F} (hα : α ≠ 0) (M N : Submodule R V) (c : F) :
    SpanRepresents Q M N (α ^ 2 * c) ↔ SpanRepresents Q M N c := by
  have key : ∀ (β : F) (hβ : β ≠ 0) (c' : F), SpanRepresents Q M N c' → SpanRepresents Q M N (β ^ 2 * c') := by
    intro β hβ c' ⟨f, hf, h⟩
    refine ⟨(LinearMap.prodMap (LinearMap.id : ↥(span F (N : Set V)) →ₗ[F] _) (β⁻¹ • (LinearMap.id : F →ₗ[F] F))).comp f,
      ?_, fun x => ?_⟩
    · intro x y hxy
      apply hf
      have h1 := congrArg Prod.fst hxy
      have h2 := congrArg Prod.snd hxy
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply,
        smul_eq_mul] at h1 h2
      exact Prod.ext h1 (mul_left_cancel₀ (inv_ne_zero hβ) h2)
    · have := h x
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [← this]
      field_simp
  constructor
  · intro h
    have := key α⁻¹ (inv_ne_zero hα) _ h
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hα, one_pow, one_mul] at this
  · exact key α hα c

end Aux

section Dual

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- The span of the Jordan chain of $L^\#$ is the span of the inverse Jordan chain of $L$ (index reversed). -/
theorem span_jordanChain_dualSplit {t : ℕ} (σ : Fin t → F) (hσ : ∀ k, σ k ≠ 0) (Ls : Fin t → Submodule R V)
    (i : Fin t) :
    span F (jordanChain (dualSplit σ Ls) i : Set V) = span F (invJordanChain Ls (Fin.rev i) : Set V) := by
  apply le_antisymm
  · rw [span_le]
    intro v hv
    have hle : jordanChain (dualSplit σ Ls) i ≤ (span F (invJordanChain Ls (Fin.rev i) : Set V)).restrictScalars R := by
      refine iSup₂_le fun k hk => ?_
      intro w hw
      obtain ⟨x, hx, rfl⟩ := mem_span_singleton_smul_iff.1 hw
      have hxI : x ∈ invJordanChain Ls (Fin.rev i) :=
        (le_iSup₂_of_le (Fin.rev k) (Fin.rev_le_rev.2 hk) le_rfl : Ls (Fin.rev k) ≤ invJordanChain Ls (Fin.rev i)) hx
      exact Submodule.smul_mem _ _ (subset_span hxI)
    exact hle hv
  · rw [span_le]
    intro v hv
    have hle : invJordanChain Ls (Fin.rev i) ≤ (span F (jordanChain (dualSplit σ Ls) i : Set V)).restrictScalars R := by
      refine iSup₂_le fun k hk => ?_
      intro w hw
      have hM : (σ k)⁻¹ • w ∈ jordanChain (dualSplit σ Ls) i := by
        have h1 : (σ k)⁻¹ • w ∈ dualSplit σ Ls (Fin.rev k) := by
          show (σ k)⁻¹ • w ∈ (R ∙ (σ (Fin.rev (Fin.rev k)))⁻¹) • Ls (Fin.rev (Fin.rev k))
          rw [Fin.rev_rev]
          exact mem_span_singleton_smul_iff.2 ⟨w, hw, rfl⟩
        exact (le_iSup₂_of_le (Fin.rev k) (by simpa using Fin.rev_le_rev.2 hk) le_rfl :
          dualSplit σ Ls (Fin.rev k) ≤ jordanChain (dualSplit σ Ls) i) h1
      have : w = σ k • ((σ k)⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ (hσ k), one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (subset_span hM)
    exact hle hv

end Dual

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

set_option maxHeartbeats 1000000 in
/-- **93:28, necessity of (iii), for a saturated splitting** (O'Meara 1963, p. 272, step 3): condition (ii) for
$L^\#$, then Witt. -/
theorem nec_rep_prev_sat (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    (hdim : ∀ k, 3 ≤ finrank R (Ls k)) (hsat : IsSaturated Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : i.val + 1 = j.val)
    (hlt : fIdeal Q L Ls i j < (4 * a i) • (1 / fundWeight Q L Ls i)) :
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a i) := by
  classical
  have hfg : L.FG := hLl.fg
  have hS := saturatedSplittingExistence (R := R) hK Q
  have ha0 : a i ≠ 0 := by
    rintro h0
    rw [h0] at hlt
    simp at hlt
  have hsc0 : ∀ k, ∃ σ : F, σ ≠ 0 ∧ scale Q (Ls k) = R ∙ σ := fun k =>
    exists_eq_span_singleton (R := R)
      ((hL.modular k).2.1 ▸ scale_fg Q (FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls k))) (hL.modular k).1
  choose σ hσ0 hσ using hsc0
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK'
  have hc : ∀ k, Fin.cast hT k = k := fun k => Fin.ext (by simp)
  have hscK : ∀ k, scale Q (Ks k) = scale Q (Ls k) := fun k => by
    have := (hJT k).1; rw [hc] at this; exact this.symm
  have hσK : ∀ k, scale Q (Ks k) = R ∙ σ k := fun k => (hscK k).trans (hσ k)
  -- the dual lattice and its two splittings
  have hreg : IsRegular Q L := isRegular_of_isJordanSplitting Q hfg hL
  have : (dual Q L).IsLattice F := Dual93.isLattice_dual Q hreg
  obtain ⟨hM, -⟩ := isJordanSplitting_dual Q hL hσ
  obtain ⟨hN, -⟩ := isJordanSplitting_dual Q hK' hσK
  have hdimM : ∀ k, 3 ≤ finrank R (dualSplit σ Ls k) := fun k => by
    have hmod : IsModular Q (R ∙ σ (Fin.rev k)) (Ls (Fin.rev k)) := by
      have := hL.modular (Fin.rev k); rwa [hσ] at this
    have hd : dualSplit σ Ls k = dual Q (Ls (Fin.rev k)) :=
      (dual_eq_smul Q (hσ0 _) hmod (fg_component Q hfg hL _)).symm
    rw [hd, finrank_dual Q (fg_component Q hfg hL _) (isRegular_of_isModular Q hmod (fg_component Q hfg hL _))]
    exact hdim _
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  have haM := isFundNormGenerators_dual Q hS h2p hQ hL hdim hsat hσ ha
  -- condition (ii) for `L^#` at the indices `rev j`, `rev i`
  have hij' : (Fin.rev j).val + 1 = (Fin.rev i).val := by
    simp only [Fin.val_rev]; have := i.isLt; have := j.isLt; omega
  have hασ : (σ i)⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero (hσ0 i))
  have e1 : fIdeal Q (dual Q L) (dualSplit σ Ls) (Fin.rev j) (Fin.rev i) = fIdeal Q L Ls i j := by
    rw [fIdeal_dual Q hS h2p hQ hL hdim hsat hσ, Fin.rev_rev, Fin.rev_rev]
  have e2 : fundWeight Q (dual Q L) (dualSplit σ Ls) (Fin.rev i) = (σ i)⁻¹ ^ 2 • fundWeight Q L Ls i := by
    rw [fundWeight_dual Q hS h2p hQ hL hdim hsat hσ, Fin.rev_rev]
  have hltM : fIdeal Q (dual Q L) (dualSplit σ Ls) (Fin.rev j) (Fin.rev i) <
      (4 * ((σ (Fin.rev (Fin.rev i)))⁻¹ ^ 2 * a (Fin.rev (Fin.rev i)))) •
        (1 / fundWeight Q (dual Q L) (dualSplit σ Ls) (Fin.rev i)) := by
    rw [e1, e2, Fin.rev_rev, threshold_smul' hασ]
    exact hlt
  have hrep := nec_rep_sat Q hK h2p h2 hQ hM hN hdimM hsatM haM (Fin.rev j) (Fin.rev i) hij' hltM
  change SpanRepresents Q (jordanChain (dualSplit σ Ks) (Fin.rev j)) (jordanChain (dualSplit σ Ls) (Fin.rev j))
    ((σ (Fin.rev (Fin.rev i)))⁻¹ ^ 2 * a (Fin.rev (Fin.rev i))) at hrep
  rw [Fin.rev_rev] at hrep
  -- the spans are the spans of the inverse Jordan chains
  have hrep' : SpanRepresents Q (invJordanChain Ks j) (invJordanChain Ls j) ((σ i)⁻¹ ^ 2 * a i) := by
    refine (spanRepresents_congr_span Q ?_ ?_ _).mp hrep
    · rw [span_jordanChain_dualSplit σ hσ0 Ks (Fin.rev j), Fin.rev_rev]
    · rw [span_jordanChain_dualSplit σ hσ0 Ls (Fin.rev j), Fin.rev_rev]
  have hrep'' : SpanRepresents Q (invJordanChain Ks j) (invJordanChain Ls j) (a i) :=
    (spanRepresents_sq_mul Q (inv_ne_zero (hσ0 i)) _ _ _).mp hrep'
  -- Witt: `L = L_(i) ⊥ L^(j) = K_(i) ⊥ K^(j)`
  have hsL := isOrthSum_jordanChain Q hL.split i j hij
  have hsK := isOrthSum_jordanChain Q hK'.split i j hij
  have hregL : IsRegular Q (jordanChain Ls i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsL.sup_eq ▸ le_sup_left)) (isJordanSplitting_jordanChain Q hL i)
  have hregK : IsRegular Q (jordanChain Ks i) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsK.sup_eq ▸ le_sup_left)) (isJordanSplitting_jordanChain Q hK' i)
  have hregKB : IsRegular Q (invJordanChain Ks j) :=
    isRegular_of_isJordanSplitting Q (FG.of_le hfg (hsK.sup_eq ▸ le_sup_right))
      (isJordanSplitting_invJordanChain Q hK' j)
  exact spanRepresents_of_orthSum_complement Q hsK hsL hregK hregL hregKB ha0 hrep''

set_option maxHeartbeats 1000000 in
/-- **93:28, necessity of condition (iii)** (O'Meara 1963, §93F, pp. 270-272): for two Jordan splittings
$L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ of the same lattice on a regular quadratic space over a
dyadic local field, with fundamental norm generators $a_k$, and $j = i+1$: if $\mathfrak f_i \subsetneq
4a_i\mathfrak w_i^{-1}$ then $FL_{(i)} \to FK_{(i)} \perp \langle a_i\rangle$. (The hyperbolic adjunctions of
`adjoin_sat`, then `nec_rep_prev_sat`.) -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity of condition (iii), pp. 270–272"]
theorem nec_rep_prev (hK : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [hLl : L.IsLattice F] {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK' : IsJordanSplitting Q L Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : i.val + 1 = j.val)
    (hlt : fIdeal Q L Ls i j < (4 * a i) • (1 / fundWeight Q L Ls i)) :
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a i) := by
  have ha0 : a i ≠ 0 := by
    rintro h0
    rw [h0] at hlt
    simp at hlt
  obtain ⟨L₂, hl, Ls₂, Ks₂, hnd, hJ, hJK, hdim, hsat, ha₂, hfI, hfw, hD1, -⟩ := adjoin_sat Q hK h2p hQ hL hK' ha
  haveI := hl
  have h := nec_rep_prev_sat _ hK h2p h2 hnd hJ hJK hdim hsat ha₂ i j hij (by rw [hfI, hfw]; exact hlt)
  exact hD1 _ ha0 i h

end Main

end QuadFormsKB.OMeara.NecRepPrev
