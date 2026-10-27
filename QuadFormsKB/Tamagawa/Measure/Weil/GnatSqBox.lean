/-
# The compact open subgroup $K'$ of $SO(V)(\mathbb A)$

**Layer:** a number field $F$ (totally real for compactness), a nondegenerate $Q_0$ over $\mathcal O_F$, a finite set $S$ of
finite places and levels $m_v$.

* `boxSub`: $\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$ as a subgroup of $SO(V)(\mathbb A_f)$, equal to
  `boxSO Q₀ S K_m` (`coe_boxSub`); it is open (hence closed) and contained in $SO(\hat L)$, hence compact.
* For $Q_0 = \langle1,-a,-b,ab\rangle$ totally definite: `boxK S m` $= G_\infty\times\mathrm{box}$ is compact, open and nonempty.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArch

open MeasureTheory Set Topology NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)
  (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- $K_{m_v}$ as a subgroup of $SO(V)(F_v)$. -/
def congSubSO (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Measure.SOv v Q₀) :=
  (congSub v Q₀ (m v) (hm1 v)).subgroupOf (soSub QF (v.adicCompletion F))

/-- $\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$. -/
def boxSub : Subgroup (SOAf Q₀) :=
  KSO Q₀ ⊓ ⨅ v ∈ S, (congSubSO Q₀ m hm1 v).comap (QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v)

/-- The local sets of the box. -/
def congSOgen (v : HeightOneSpectrum (𝓞 F)) : Set (Measure.SOv v Q₀) :=
  Subtype.val ⁻¹' (congSub v Q₀ (m v) (hm1 v) : Set (orthGroup QF (v.adicCompletion F)))

theorem coe_boxSub :
    (boxSub Q₀ S m hm1 : Set (SOAf Q₀)) = QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOgen Q₀ m hm1) := by
  ext g
  simp only [boxSub, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap,
    QuadFormsKB.Tamagawa.Measure.boxSO, mem_setOf_eq, QuadFormsKB.Tamagawa.Measure.mem_KSO_iff]
  constructor
  · rintro ⟨hK, hS⟩
    exact ⟨fun v hv => hS v hv, fun v _ => hK v⟩
  · rintro ⟨hS, hnS⟩
    refine ⟨fun v => ?_, fun v hv => hS v hv⟩
    by_cases hv : v ∈ S
    · exact congSub_le_stdStab v Q₀ (m v) (hm1 v) (hS v hv)
    · exact hnS v hv

theorem isOpen_boxSub : IsOpen (boxSub Q₀ S m hm1 : Set (SOAf Q₀)) := by
  rw [boxSub, Subgroup.coe_inf]
  refine (isOpen_KSO Q₀).inter ?_
  simp only [Subgroup.coe_iInf]
  refine isOpen_biInter_finset fun v _ => ?_
  exact ((isOpen_congSub v Q₀ (m v) (hm1 v)).preimage continuous_subtype_val).preimage
    (QuadFormsKB.Tamagawa.Measure.continuous_evalSO Q₀ v)

theorem isCompact_boxSub : IsCompact (boxSub Q₀ S m hm1 : Set (SOAf Q₀)) :=
  (isCompact_KSO Q₀).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_boxSub Q₀ S m hm1)) inf_le_left

section Sq

variable {a b : 𝓞 F}

theorem boxK_eq : boxK S m hm1 = univ ×ˢ (boxSub (qSq a b) S m hm1 : Set (SOAf (qSq a b))) := by
  rw [boxK, coe_boxSub]; rfl

theorem isOpen_boxK : IsOpen (boxK (a := a) (b := b) S m hm1) := by
  rw [boxK_eq]; exact isOpen_univ.prod (isOpen_boxSub _ S m hm1)

theorem nonempty_boxK : (boxK (a := a) (b := b) S m hm1).Nonempty := by
  rw [boxK_eq]; exact ⟨1, mem_univ _, (boxSub _ S m hm1).one_mem⟩

theorem isCompact_boxK [IsTotallyReal F] (hQ : (qSq a b).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qSq a b))) :
    IsCompact (boxK (a := a) (b := b) S m hm1) := by
  have : ∀ w, Fact (QuadFormsKB.Siegel.IsPosDefR (QRe (qSq a b) w)) := fun w => ⟨isPosDefR_QRe (qSq a b) hQ hpd w⟩
  have : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩
  have : CompactSpace (GInfSO (qSq a b)) := by
    unfold GInfSO QuadFormsKB.Tamagawa.Measure.LerayArch.ArchGroup; infer_instance
  rw [boxK_eq]
  exact isCompact_univ.prod (isCompact_boxSub _ S m hm1)

end Sq

end QuadFormsKB.Tamagawa.Measure.Weil
