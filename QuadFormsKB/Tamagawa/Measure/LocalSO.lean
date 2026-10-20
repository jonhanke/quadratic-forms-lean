/-
# Local Tamagawa measures at a finite place

**Layer:** a number field $F$, a finite prime $\mathfrak p = v$, the completion $F_v$ with its topology
(`Analysis/LocalFourierNF.lean`: locally compact, Borel, proper); the KB's concrete orthogonal group
$O(V)(F_v) = $ `orthGroup QF Fv` $\le \mathrm{GL}_n(F_v)$ for $V = (F^n, Q_0\otimes F)$, with $L = \mathcal O_F^n$, $O(L_v) = $ `stdStab`, $SO(L_v) = $ `soStab`.

**Defines**
* the topology of $O(V)(F_v)$: the subspace topology from $\mathrm{GL}_n(F_v)$, which carries Mathlib's topology on units
  (induced from $M_n(F_v)\times M_n(F_v)^{\mathrm{op}}$); the Borel $\sigma$-algebra on it;
* `haarNorm K c`: for a compact open subgroup $K$ of a topological group, the Haar measure with $\mu(K) = c$;
* `muLoc v Q₀ λ` $= \mu_v$: the **local Tamagawa measure** at $v$ with convergence factor $\lambda_v$ (default $\lambda_v = 1$): the Haar measure on $O(V)(F_v)$ with $\mu_v(O(L_v)) = \beta_v(L, L)/\lambda_v$, equivalently
  $\mu_v(SO(L_v)) = \alpha_v(L,L)/\lambda_v$ (`muLoc_soStab`; the density normalization).
* `muLocSO v Q₀ λ`: the same measure on the group $SO(V)(F_v)$ (`SOv v Q₀`), normalized by
  $\mu(SO(L_v)) = \alpha_v(L,L)/\lambda_v$; it is the restriction of `muLoc` (`muLocSO_eq_comap`).

**Proves**
* topology: `isClosed_orthGroup`, `LocallyCompactSpace`, `SecondCountableTopology`, `TotallyDisconnectedSpace`,
  `BorelSpace`; `stdStab`, `soStab` and every lattice stabilizer $O(gL_v)$ are **compact open** (`isCompact_stdStab`,
  `isOpen_stdStab`, `isCompact_soStab`, `isOpen_soStab`, `isCompact_stabLat`, `isOpen_stabLat`);
* abstract Haar facts: $\mu(A) = [A:B]\,\mu(B)$ for open subgroups $B \le A$ (`measure_subgroup_eq_relIndex_mul`), the change of
  reference subgroup by `relRatio` (`haarNorm_eq_haarNorm`), uniqueness (`eq_haarNorm`), $\mu(\bigsqcup_{i\le N} g_iH) = N\mu(H)$
  (`measure_cosetUnion`);
* `isHaarMeasure_muLoc`: $\mu_v$ is a Haar measure (nondegenerate $Q_0$, $\lambda_v > 0$);
* **the bridge** (`muLoc_eq_volLoc`, `muLoc_eq_volLoc_of_isCompact_isOpen`): $\mu_v(U) = $ `volLoc v Q₀ U` $/\lambda_v$ for every
  KB compact open set $U$ (a finite union of left cosets of a subgroup commensurable with $O(L_v)$) whose subgroup is
  open, and for **every** compact open $U \subseteq O(V)(F_v)$, which is automatically a KB compact open set
  (`exists_isCosetUnion_of_isCompact_isOpen`). Hence `volSO_eq` and `volO_eq` are statements about $\mu_v$
  (`muLoc_soStab`, `muLoc_stdStab`);
* **independence of the lattice** (`muLoc_eq_haarNorm_latOf`): for $L'_v = P\mathfrak o_v^n$ ($\det P \ne 0$), the Haar measure
  normalized by $\mu(O(L'_v)) = \beta_v(Q_0\circ P)\,\|\det P\|_v^{n+1}/\lambda_v$ (the density of $L'_v$ in its own
  coordinates, times the Jacobian of the change of coordinates) **is** $\mu_v$; this is the $\alpha$ law
  (`latLocalFactor_eq`, `alphaLaw_global`) read as an equality of measures.

**Sources.** Weil 1982, §2.1–§2.2 (Haar measures and gauge-form measures on $p$-adic groups) and §2.3, p. 21 (convergence
factors $\lambda_v$). The coset-counting lemma `measure_subgroup_eq_relIndex_mul` is the same statement as FLT's
`MeasureTheory.Measure.relIndex_mul_measure` (ImperialCollegeLondon/FLT, `FLT/Mathlib/MeasureTheory/Group/ModularCharacter.lean`,
Apache-2.0); it is reproved here to keep the development self-contained.

*Caveat.* $\mu_v$ is a genuine Haar measure whose value on $SO(L_v)$ is Siegel's density $\alpha_v$;
that $\alpha_v$ is the gauge-form volume $|\omega|_v(SO(L_v))$ is Weil's fibration (`fiberVolume_eq`), not a statement about
$\mu_v$ (that needs the $p$-adic Leray functional, in `LerayPadic.lean`).
-/
import QuadFormsKB.Tamagawa.LocalVolume
import QuadFormsKB.Tamagawa.LatticeChangeNF
import QuadFormsKB.Analysis.LocalFourierNF

open MeasureTheory Measure TopologicalSpace Topology
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

/-! ### Haar measures of open subgroups (abstract) -/

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- **Coset counting:** for open subgroups $B \le A$ of finite index $[A : B]$ and a left-invariant measure $\mu$,
$\mu(A) = [A:B]\,\mu(B)$ ($A$ is the disjoint union of $[A:B]$ left translates of $B$). Same statement as FLT's
`relIndex_mul_measure` (ImperialCollegeLondon/FLT, Apache-2.0), reproved. -/
@[kb "weil1982" "§2.1 (Haar measures on p-adic groups) [unverified]"]
theorem measure_subgroup_eq_relIndex_mul (μ : Measure G) [IsMulLeftInvariant μ] {A B : Subgroup G}
    (hB : IsOpen (B : Set G)) (hBA : B ≤ A) (hfin : B.relIndex A ≠ 0) :
    μ (A : Set G) = (B.relIndex A : ℝ≥0∞) * μ (B : Set G) := by
  classical
  set B' := B.subgroupOf A
  have : B'.FiniteIndex := ⟨hfin⟩
  have : Finite (A ⧸ B') := Subgroup.finite_quotient_of_finiteIndex
  have : Fintype (A ⧸ B') := Fintype.ofFinite _
  let r : A ⧸ B' → G := fun q => ((Quotient.out q : A) : G)
  have hU : (A : Set G) = ⋃ q, r q • (B : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk ⟨x, hx⟩ : A ⧸ B'), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul B' ⟨x, hx⟩
      refine ⟨((h : A) : G)⁻¹, B.inv_mem (Subgroup.mem_subgroupOf.mp h.2), ?_⟩
      simp only [r, hh, Subgroup.coe_mul, mul_inv_cancel_right]
    · rintro ⟨q, b, hb, rfl⟩
      exact A.mul_mem (Quotient.out q).2 (hBA hb)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => r q • (B : Set G)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', he⟩
    apply hqq'
    have hrel : (r q)⁻¹ * r q' = b * b'⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc]
      change (r q)⁻¹ * (r q' * b') = b
      rw [show r q' * b' = r q * b from he, inv_mul_cancel_left]
    have : (QuotientGroup.mk (Quotient.out q) : A ⧸ B') = QuotientGroup.mk (Quotient.out q') := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      change (r q)⁻¹ * r q' ∈ B
      rw [hrel]; exact B.mul_mem hb (B.inv_mem hb')
    simpa only [QuotientGroup.out_eq'] using this
  rw [hU, measure_iUnion hdisj (fun q => (hB.smul (r q)).measurableSet), tsum_fintype]
  simp only [measure_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- **The ratio of the measures of two commensurable open subgroups** is the index ratio
$r(A, B) = [A : A\cap B]/[B : A \cap B]$ (`relRatio`): $\mu(A) = r(A,B)\,\mu(B)$. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem measure_toReal_eq_relRatio_mul (μ : Measure G) [IsMulLeftInvariant μ] {A B : Subgroup G}
    (hA : IsOpen (A : Set G)) (hB : IsOpen (B : Set G)) (hAB : B.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0) :
    (μ (A : Set G)).toReal = relRatio A B * (μ (B : Set G)).toReal := by
  have hI : IsOpen ((A ⊓ B : Subgroup G) : Set G) := hA.inter hB
  have e1 := measure_subgroup_eq_relIndex_mul μ hI inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact hAB)
  have e2 := measure_subgroup_eq_relIndex_mul μ hI inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact hBA)
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right] at e2
  rw [e1, e2, ENNReal.toReal_mul, ENNReal.toReal_mul, relRatio]
  simp only [ENNReal.toReal_natCast]
  have : (A.relIndex B : ℝ) ≠ 0 := by exact_mod_cast hBA
  field_simp

/-- A compact open subgroup as a compact set with nonempty interior. -/
def subgroupPC (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) : PositiveCompacts G :=
  ⟨⟨K, hc⟩, by rw [ho.interior_eq]; exact ⟨1, K.one_mem⟩⟩

/-- **The Haar measure normalized on a compact open subgroup:** $\mu(K) = c$. -/
@[kb "weil1982" "§2.1 [unverified]"]
def haarNorm (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) (c : ℝ≥0) : Measure G :=
  c • haarMeasure (subgroupPC K hc ho)

variable {K : Subgroup G} (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))

instance (c : ℝ≥0) : IsMulLeftInvariant (haarNorm K hc ho c) := by unfold haarNorm; infer_instance

instance (c : ℝ≥0) : IsFiniteMeasureOnCompacts (haarNorm K hc ho c) := by unfold haarNorm; infer_instance

theorem haarNorm_self (c : ℝ≥0) : haarNorm K hc ho c (K : Set G) = c := by
  have : haarMeasure (subgroupPC K hc ho) (K : Set G) = 1 := haarMeasure_self
  rw [haarNorm, Measure.smul_apply, this, ENNReal.smul_def, smul_eq_mul, mul_one]

/-- **Uniqueness:** a $\sigma$-finite left-invariant measure is the Haar measure normalized by its value on $K$. -/
theorem eq_haarNorm [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] (hfin : μ (K : Set G) ≠ ∞) :
    μ = haarNorm K hc ho (μ (K : Set G)).toNNReal := by
  rw [haarNorm, ENNReal.smul_def, ENNReal.coe_toNNReal hfin]
  exact haarMeasure_unique μ (subgroupPC K hc ho)

/-- **Change of the reference subgroup:** the Haar measure with $\mu(K_1) = c_1$ is the Haar measure with
$\mu(K_2) = r(K_2, K_1)\,c_1$, for compact open subgroups $K_1$, $K_2$. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem haarNorm_eq_haarNorm [LocallyCompactSpace G] [SecondCountableTopology G] {K₂ : Subgroup G}
    (hc₂ : IsCompact (K₂ : Set G)) (ho₂ : IsOpen (K₂ : Set G)) (h12 : K.relIndex K₂ ≠ 0) (h21 : K₂.relIndex K ≠ 0)
    (c : ℝ≥0) :
    haarNorm K hc ho c = haarNorm K₂ hc₂ ho₂ (Real.toNNReal (relRatio K₂ K * c)) := by
  set μ := haarNorm K hc ho c
  have hK2 : μ (K₂ : Set G) ≠ ∞ := hc₂.measure_lt_top.ne
  rw [eq_haarNorm hc₂ ho₂ μ hK2]
  congr 1
  have e := measure_toReal_eq_relRatio_mul μ ho₂ ho h12 h21
  rw [haarNorm_self, ENNReal.coe_toReal] at e
  rw [← e]
  exact (Real.toNNReal_coe).symm

/-- **Open subgroups of a compact subgroup have finite index in it.** -/
theorem relIndex_ne_zero_of_isOpen {H K : Subgroup G} (hK : IsCompact (K : Set G)) (hH : IsOpen (H : Set G)) :
    H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hU : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) := hH.preimage continuous_subtype_val
  have : DiscreteTopology (K ⧸ H.subgroupOf K) := QuotientGroup.discreteTopology hU
  have : Finite (K ⧸ H.subgroupOf K) := finite_of_compact_of_discrete
  exact Subgroup.index_ne_zero_of_finite

/-- **The measure of a finite union of left cosets** $U = \bigsqcup_{i=1}^N g_iH$ of an open subgroup $H$:
$\mu(U) = N\,\mu(H)$ (the measure-theoretic counterpart of `cosetVol`). -/
theorem measure_cosetUnion (μ : Measure G) [IsMulLeftInvariant μ] {H : Subgroup G} (hH : IsOpen (H : Set G))
    {U : Set G} (hU : IsCosetUnion H U) :
    μ U = (Nat.card (QuotientGroup.mk '' U : Set (G ⧸ H)) : ℝ≥0∞) * μ (H : Set G) := by
  classical
  set S := hU.2.toFinset
  let r : G ⧸ H → G := fun q => Quotient.out q
  have hUe : U = ⋃ q ∈ S, r q • (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe, S, Set.Finite.mem_toFinset,
      exists_prop]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk x, ⟨x, hx, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x
      exact ⟨(h : G)⁻¹, H.inv_mem h.2, by simp only [r, hh, mul_inv_cancel_right]⟩
    · rintro ⟨q, ⟨u, hu, rfl⟩, h, hh, rfl⟩
      obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul H u
      simp only [r, hh', mul_assoc]
      exact hU.1 u hu _ (H.mul_mem h'.2 hh)
  have hdisj : Set.PairwiseDisjoint (↑S) fun q => r q • (H : Set G) := by
    intro q _ q' _ hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', he⟩
    apply hqq'
    have hrel : (r q)⁻¹ * r q' = b * b'⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc]
      change (r q)⁻¹ * (r q' * b') = b
      rw [show r q' * b' = r q * b from he, inv_mul_cancel_left]
    have : (QuotientGroup.mk (r q) : G ⧸ H) = QuotientGroup.mk (r q') := by
      rw [QuotientGroup.eq, hrel]; exact H.mul_mem hb (H.inv_mem hb')
    simpa only [r, QuotientGroup.out_eq'] using this
  have hμ : μ U = μ (⋃ q ∈ S, r q • (H : Set G)) := congrArg μ hUe
  rw [hμ, measure_biUnion_finset hdisj (fun q _ => (hH.smul (r q)).measurableSet)]
  simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hU.2]

/-- **Compact open sets are finite unions of cosets of a small open subgroup.** In a totally disconnected Hausdorff group
with a compact open subgroup $K_0$, every compact open set $U$ is a finite union of left cosets of an open subgroup
$H \le K_0$ (so $U$ is a KB "compact open" set, `IsCompactOpen`). -/
theorem exists_isCosetUnion_of_isCompact_isOpen [T2Space G] [TotallyDisconnectedSpace G] {K₀ : Subgroup G}
    (hK₀c : IsCompact (K₀ : Set G)) (hK₀o : IsOpen (K₀ : Set G)) {U : Set G} (hUc : IsCompact U) (hUo : IsOpen U) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ H ≤ K₀ ∧ IsCosetUnion H U := by
  obtain ⟨V, hV, hUV⟩ := compact_open_separated_mul_right hUc hUo subset_rfl
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c
  set W : Set K₀ := Subtype.val ⁻¹' interior V
  have hWo : IsOpen W := isOpen_interior.preimage continuous_subtype_val
  have hW1 : (1 : K₀) ∈ W := by
    change ((1 : K₀) : G) ∈ interior V
    rw [OneMemClass.coe_one]; exact mem_interior_iff_mem_nhds.mpr hV
  obtain ⟨H', hH'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  set H : Subgroup G := H'.toSubgroup.map K₀.subtype
  have hHo : IsOpen (H : Set G) := by
    have : (H : Set G) = Subtype.val '' (H'.toSubgroup : Set K₀) := by
      ext x; simp [H]
    rw [this]; exact hK₀o.isOpenEmbedding_subtypeVal.isOpenMap _ H'.isOpen'
  have hHV : (H : Set G) ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hH' hy)
  refine ⟨H, hHo, Subgroup.map_subtype_le _, fun u hu h hh => hUV (Set.mul_mem_mul hu (hHV hh)), ?_⟩
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hHo
  exact (hUc.image QuotientGroup.continuous_mk).finite_of_discrete

end Abstract

/-! ### The topology of $O(V)(F_v)$ -/

section Local

open NumberField IsDedekindDomain QuadFormsKB.Lattices LocalDensity Matrix

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The integral matrices $M_n(\mathfrak o_v) \subseteq M_n(F_v)$. -/
def intMat : Set (Matrix (Fin n) (Fin n) Fv) := {M | ∀ i j, Valued.v (M i j) ≤ 1}

theorem coe_latticeV_zero : (Analysis.latticeV v 0 : Set Fv) = {x : Fv | Valued.v x ≤ 1} := by
  ext x
  simp [Analysis.mem_latticeV]

theorem intMat_eq : (intMat v : Set (Matrix (Fin n) (Fin n) Fv)) =
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (Analysis.latticeV v 0 : Set Fv) := by
  ext M
  rw [coe_latticeV_zero]
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩

theorem isCompact_intMat : IsCompact (intMat v : Set (Matrix (Fin n) (Fin n) Fv)) := by
  rw [intMat_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => Analysis.isCompact_latticeV v 0

theorem isOpen_latticeV_zero : IsOpen (Analysis.latticeV v 0 : Set Fv) := by
  rw [Analysis.coe_latticeV]
  exact IsUltrametricDist.isOpen_closedBall _
    (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))).ne'

theorem isOpen_intMat : IsOpen (intMat v : Set (Matrix (Fin n) (Fin n) Fv)) := by
  rw [intMat_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latticeV_zero v

/-- $\mathrm{GL}_n(\mathfrak o_v) = \mathrm{Stab}(\mathfrak o_v^n) \subseteq \mathrm{GL}_n(F_v)$. -/
def glInt : Set (GL (Fin n) Fv) := {g | locAct v g (std v) = std v}

theorem entries_le_one_of_locAct {R : GL (Fin n) Fv} (hR : locAct v R (std v) = std v) (i j : Fin n) :
    Valued.v (R.val i j) ≤ 1 := by
  have hm : R.val *ᵥ Pi.single j 1 ∈ std v := hR ▸ ⟨_, single_one_mem_std v j, rfl⟩
  have := hm i
  rw [neg_zero, WithZero.exp_zero] at this
  simpa [mulVec_single_one] using this

theorem glInt_eq : (glInt v : Set (GL (Fin n) Fv)) =
    Units.embedProduct _ ⁻¹' (intMat v ×ˢ (MulOpposite.unop ⁻¹' intMat v)) := by
  ext g
  simp only [glInt, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    MulOpposite.unop_op]
  constructor
  · intro h
    have h' : locAct v g⁻¹ (std v) = std v := by
      conv_lhs => rw [← h]
      rw [locAct_inv_locAct]
    exact ⟨entries_le_one_of_locAct v h, entries_le_one_of_locAct v h'⟩
  · rintro ⟨h1, h2⟩
    ext y
    rw [mem_locAct]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mulVec_mem_std v h1 hz
    · intro hy
      exact ⟨g⁻¹.val *ᵥ y, mulVec_mem_std v h2 hy, mulVec_inv_mulVec g y⟩

theorem isOpen_glInt : IsOpen (glInt v : Set (GL (Fin n) Fv)) := by
  rw [glInt_eq]
  exact ((isOpen_intMat v).prod ((isOpen_intMat v).preimage MulOpposite.continuous_unop)).preimage
    Units.continuous_embedProduct

theorem isCompact_glInt : IsCompact (glInt v : Set (GL (Fin n) Fv)) := by
  rw [glInt_eq]
  refine Units.isClosedEmbedding_embedProduct.isCompact_preimage ((isCompact_intMat v).prod ?_)
  exact (MulOpposite.opHomeomorph.symm.isCompact_preimage).mpr (isCompact_intMat v)

/-- The stabilizer of $g\,\mathfrak o_v^n$ in $\mathrm{GL}_n(F_v)$ is $g\,\mathrm{GL}_n(\mathfrak o_v)\,g^{-1}$. -/
theorem stab_locAct_eq (g : GL (Fin n) Fv) :
    {x : GL (Fin n) Fv | locAct v x (locAct v g (std v)) = locAct v g (std v)} =
      (fun x => g⁻¹ * x * g) ⁻¹' glInt v := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, glInt]
  constructor
  · intro h
    rw [locAct_mul, locAct_mul, h, locAct_inv_locAct]
  · intro h
    have : locAct v g (locAct v (g⁻¹ * x * g) (std v)) = locAct v g (std v) := by rw [h]
    rwa [← locAct_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, locAct_mul] at this

theorem isOpen_stab_locAct (g : GL (Fin n) Fv) :
    IsOpen {x : GL (Fin n) Fv | locAct v x (locAct v g (std v)) = locAct v g (std v)} := by
  rw [stab_locAct_eq]
  exact (isOpen_glInt v).preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_stab_locAct (g : GL (Fin n) Fv) :
    IsCompact {x : GL (Fin n) Fv | locAct v x (locAct v g (std v)) = locAct v g (std v)} := by
  rw [stab_locAct_eq]
  exact ((Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)).isCompact_preimage.mpr (isCompact_glInt v)

variable (Q : QuadForm F n)

/-- **$O(V)(F_v)$ is closed in $\mathrm{GL}_n(F_v)$** (it is cut out by $g^{\mathsf T}Hg = H$). -/
theorem isClosed_orthGroup : IsClosed (orthGroup Q Fv : Set (GL (Fin n) Fv)) := by
  have hc : Continuous fun g : GL (Fin n) Fv => g.valᵀ * Q.hessian.map (algebraMap F Fv) * g.val :=
    ((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq hc continuous_const

instance : LocallyCompactSpace (Matrix (Fin n) (Fin n) Fv) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv))

instance : SecondCountableTopology (Matrix (Fin n) (Fin n) Fv) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv))

instance : SecondCountableTopology (Matrix (Fin n) (Fin n) Fv)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

instance : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) Fv) :=
  inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → Fv))

instance : LocallyCompactSpace (orthGroup Q Fv) :=
  (isClosed_orthGroup v Q).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (GL (Fin n) Fv) :=
  Units.isEmbedding_embedProduct.secondCountableTopology

instance : SecondCountableTopology (orthGroup Q Fv) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance : TotallyDisconnectedSpace (orthGroup Q Fv) := by
  refine ⟨isTotallyDisconnected_of_image (f := fun g : orthGroup Q Fv => (g : GL (Fin n) Fv).val)
    (Units.continuous_val.comp continuous_subtype_val).continuousOn
    (fun a b h => Subtype.ext (Units.ext h)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- The Borel $\sigma$-algebra on $O(V)(F_v)$. -/
instance : MeasurableSpace (orthGroup Q Fv) := borel _

instance : BorelSpace (orthGroup Q Fv) := ⟨rfl⟩

/-- **Preimages of compact sets of $\mathrm{GL}_n(F_v)$ are compact** in $O(V)(F_v)$ (it is closed). -/
theorem isCompact_preimage_val {T : Set (GL (Fin n) Fv)} (hT : IsCompact T) :
    IsCompact (Subtype.val ⁻¹' T : Set (orthGroup Q Fv)) :=
  (isClosed_orthGroup v Q).isClosedEmbedding_subtypeVal.isCompact_preimage hT

/-- **$O(L_v)$ is compact.** -/
theorem isCompact_stdStab : IsCompact (stdStab Q v : Set (orthGroup Q Fv)) :=
  isCompact_preimage_val v Q (isCompact_glInt v)

/-- **$O(L_v)$ is open.** -/
theorem isOpen_stdStab : IsOpen (stdStab Q v : Set (orthGroup Q Fv)) :=
  (isOpen_glInt v).preimage continuous_subtype_val

/-- **The stabilizer $O(\Lambda)$ of a lattice $\Lambda = g\,\mathfrak o_v^n$ is compact.** -/
theorem isCompact_stabLat (g : GL (Fin n) Fv) :
    IsCompact (stabLat v (orthGroup Q Fv).subtype (locAct v g (std v)) : Set (orthGroup Q Fv)) :=
  isCompact_preimage_val v Q (isCompact_stab_locAct v g)

/-- **The stabilizer $O(\Lambda)$ of a lattice $\Lambda = g\,\mathfrak o_v^n$ is open.** -/
theorem isOpen_stabLat (g : GL (Fin n) Fv) :
    IsOpen (stabLat v (orthGroup Q Fv).subtype (locAct v g (std v)) : Set (orthGroup Q Fv)) :=
  (isOpen_stab_locAct v g).preimage continuous_subtype_val

theorem continuous_det_orth : Continuous fun g : orthGroup Q Fv => (g : GL (Fin n) Fv).val.det :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_det

theorem isClosed_soSub : IsClosed (soSub Q Fv : Set (orthGroup Q Fv)) :=
  isClosed_eq (continuous_det_orth v Q) continuous_const

/-- **$SO(V)(F_v)$ is open in $O(V)(F_v)$** for nondegenerate $Q$ ($\det = \pm1$ and $1 \ne -1$). -/
theorem isOpen_soSub (hQ : Q.Nondegenerate) : IsOpen (soSub Q Fv : Set (orthGroup Q Fv)) := by
  have : (soSub Q Fv : Set (orthGroup Q Fv)) = {g : orthGroup Q Fv | (g : GL (Fin n) Fv).val.det ≠ -1} := by
    ext g
    simp only [SetLike.mem_coe, mem_soSub, Set.mem_ofPred_eq]
    have h1 : (1 : Fv) ≠ -1 := by
      intro h; have : (2 : Fv) = 0 := by linear_combination h
      exact two_ne_zero this
    rcases det_eq_one_or_neg_one Q hQ g with h | h <;> simp [h, h1, h1.symm]
  rw [this]
  exact isOpen_ne_fun (continuous_det_orth v Q) continuous_const

end Local

/-! ### The local Tamagawa measure $\mu_v$ -/

section Measure

open NumberField IsDedekindDomain QuadFormsKB.Lattices LocalDensity Matrix

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem nondegenerate_QF (hQ : Q₀.Nondegenerate) : (QF).Nondegenerate := by
  rw [QuadForm.Nondegenerate]
  have : (QF).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (RingOfIntegers.coe_injective)).mpr hQ

/-- **$SO(L_v)$ is compact.** -/
theorem isCompact_soStab : IsCompact (soStab v Q₀ : Set (orthGroup QF Fv)) :=
  (isCompact_stdStab v QF).inter_left (isClosed_soSub v QF)

/-- **$SO(L_v)$ is open** (for nondegenerate $Q_0$). -/
theorem isOpen_soStab (hQ : Q₀.Nondegenerate) : IsOpen (soStab v Q₀ : Set (orthGroup QF Fv)) :=
  (isOpen_soSub v QF (nondegenerate_QF Q₀ hQ)).inter (isOpen_stdStab v QF)

/-- **The local Tamagawa measure at a finite place $v$** with convergence factor $\lambda_v$ (default $\lambda_v = 1$;
Weil 1982, §2.3, p. 21: the Tamagawa measure is $\prod_v \lambda_v^{-1}\omega_v$): the Haar measure $\mu_v$ on
$O(V)(F_v)$, $V = (F^n, Q_0)$, normalized by
$$\mu_v(O(L_v)) = \beta_v(L, L)/\lambda_v,\qquad L = \mathcal O_F^n,$$
equivalently $\mu_v(SO(L_v)) = \alpha_v(L,L)/\lambda_v$ (`muLoc_soStab`), the density normalization. It agrees with the KB's combinatorial `volLoc` on compact open sets (`muLoc_eq_volLoc`) and
does not depend on the lattice (`muLoc_eq_haarNorm_latOf`). -/
@[kb "weil1982" "§2.2 (local measures), §2.3, p. 21 (convergence factors λ_v)"]
def muLoc (lam : ℝ := 1) : Measure (orthGroup QF Fv) :=
  haarNorm (stdStab QF v) (isCompact_stdStab v QF) (isOpen_stdStab v QF)
    (Real.toNNReal (NF.localDensityForm v Q₀ Q₀ / lam))

instance (lam : ℝ) : IsMulLeftInvariant (muLoc v Q₀ lam) := by unfold muLoc; infer_instance

instance (lam : ℝ) : IsFiniteMeasureOnCompacts (muLoc v Q₀ lam) := by unfold muLoc; infer_instance

/-- **$\mu_v$ is a Haar measure** (left invariant, finite on compact sets, positive on open sets) for nondegenerate
$Q_0$ and $\lambda_v > 0$. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem isHaarMeasure_muLoc (hQ : Q₀.Nondegenerate) {lam : ℝ} (hlam : 0 < lam) : IsHaarMeasure (muLoc v Q₀ lam) := by
  have h : Real.toNNReal (NF.localDensityForm v Q₀ Q₀ / lam) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact div_pos (LatChange.localDensityForm_self_pos v Q₀ hQ) hlam
  unfold muLoc haarNorm
  exact IsHaarMeasure.nnreal_smul _ h

/-- **$\mu_v(O(L_v)) = \beta_v(L,L)/\lambda_v$** (the normalization; cf. `volO_eq`). -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLoc_stdStab (lam : ℝ) :
    muLoc v Q₀ lam (stdStab QF v : Set (orthGroup QF Fv)) = ENNReal.ofReal (NF.localDensityForm v Q₀ Q₀ / lam) :=
  haarNorm_self _ _ _

/-- **The bridge to the combinatorial Haar measure:** for a subgroup $H \le O(V)(F_v)$ that is open and commensurable with
$O(L_v)$, and a finite union $U$ of left $H$-cosets (a KB compact open set), $\mu_v(U) = $ `volLoc v Q₀ U` $/\lambda_v$. -/
@[kb "weil1982" "§2.1–§2.2 [unverified]"]
theorem muLoc_eq_volLoc (hQ : Q₀.Nondegenerate) {lam : ℝ} (hlam : 0 < lam) {H : Subgroup (orthGroup QF Fv)}
    (hHo : IsOpen (H : Set (orthGroup QF Fv))) (hH : H.Commensurable (stdStab QF v))
    {U : Set (orthGroup QF Fv)} (hU : IsCosetUnion H U) :
    muLoc v Q₀ lam U = ENNReal.ofReal (volLoc v Q₀ U / lam) := by
  have hβ := LatChange.localDensityForm_self_pos v Q₀ hQ
  set μ := muLoc v Q₀ lam
  rw [measure_cosetUnion μ hHo hU, volLoc, haarVol_eq _ _ hH hU, cosetVol, idxVol]
  have hK := isOpen_stdStab v QF
  have e := measure_toReal_eq_relRatio_mul μ hHo hK hH.2.relIndex_ne_zero hH.1.relIndex_ne_zero
  rw [show μ (stdStab QF v : Set _) = _ from muLoc_stdStab v Q₀ lam,
    ENNReal.toReal_ofReal (div_nonneg hβ.le hlam.le)] at e
  have hHfin : μ (H : Set (orthGroup QF Fv)) ≠ ∞ := by
    intro h; rw [h, ENNReal.toReal_top] at e
    have hr : 0 < relRatio H (stdStab QF v) := relRatio_pos ⟨hH.2.relIndex_ne_zero, hH.1.relIndex_ne_zero⟩
    have := mul_pos hr (div_pos hβ hlam)
    linarith
  rw [← ENNReal.ofReal_toReal hHfin, e, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [relRatio]
  ring

/-- **$\mu_v(SO(L_v)) = \alpha_v(L,L)/\lambda_v$**, Siegel's density: the KB's `volSO_eq` as a statement about the Haar
measure $\mu_v$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem muLoc_soStab (hQ : Q₀.Nondegenerate) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    muLoc v Q₀ lam (soStab v Q₀ : Set (orthGroup QF Fv)) = ENNReal.ofReal (NF.siegelDensity v Q₀ Q₀ / lam) := by
  have h2 := relIndex_soStab v Q₀ hQ hn
  have hcomm : (soStab v Q₀).Commensurable (stdStab QF v) :=
    ⟨⟨by rw [h2]; norm_num⟩, ⟨by
      rw [Subgroup.relIndex_eq_one.mpr (show soStab v Q₀ ≤ stdStab QF v from inf_le_right)]; norm_num⟩⟩
  have hU : IsCosetUnion (soStab v Q₀) (soStab v Q₀ : Set (orthGroup QF Fv)) := by
    refine ⟨fun u hu h hh => (soStab v Q₀).mul_mem hu hh, ?_⟩
    refine (Set.finite_singleton (QuotientGroup.mk 1 : _ ⧸ soStab v Q₀)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff, QuotientGroup.eq, mul_one, inv_mem_iff]; exact hu
  rw [muLoc_eq_volLoc v Q₀ hQ hlam (isOpen_soStab v Q₀ hQ) hcomm hU, volSO_eq v Q₀ hQ hn]

/-- **$\mu_v$ is the Haar measure normalized by $\mu_v(SO(L_v)) = \alpha_v(L, L)/\lambda_v$** (the form of the definition). -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLoc_eq_haarNorm_soStab (hQ : Q₀.Nondegenerate) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    muLoc v Q₀ lam = haarNorm (soStab v Q₀) (isCompact_soStab v Q₀) (isOpen_soStab v Q₀ hQ)
      (Real.toNNReal (NF.siegelDensity v Q₀ Q₀ / lam)) := by
  rw [eq_haarNorm (isCompact_soStab v Q₀) (isOpen_soStab v Q₀ hQ) (muLoc v Q₀ lam)
    ((isCompact_soStab v Q₀).measure_lt_top.ne), muLoc_soStab v Q₀ hQ hn hlam]
  rfl

/-- **The bridge for every compact open set:** a compact open $U \subseteq O(V)(F_v)$ is a KB compact open set
(`IsCompactOpen`, for the reference subgroup $O(L_v)$), and $\mu_v(U) = $ `volLoc v Q₀ U` $/\lambda_v$. -/
@[kb "weil1982" "§2.1–§2.2 [unverified]"]
theorem muLoc_eq_volLoc_of_isCompact_isOpen (hQ : Q₀.Nondegenerate) {lam : ℝ} (hlam : 0 < lam)
    {U : Set (orthGroup QF Fv)} (hUc : IsCompact U) (hUo : IsOpen U) :
    IsCompactOpen (stdStab QF v) U ∧ muLoc v Q₀ lam U = ENNReal.ofReal (volLoc v Q₀ U / lam) := by
  obtain ⟨H, hHo, hHle, hU⟩ :=
    exists_isCosetUnion_of_isCompact_isOpen (isCompact_stdStab v QF) (isOpen_stdStab v QF) hUc hUo
  have hH : H.Commensurable (stdStab QF v) :=
    ⟨⟨relIndex_ne_zero_of_isOpen (isCompact_stdStab v QF) hHo⟩,
      ⟨by rw [Subgroup.relIndex_eq_one.mpr hHle]; norm_num⟩⟩
  exact ⟨⟨H, hH, hU⟩, muLoc_eq_volLoc v Q₀ hQ hlam hHo hH hU⟩

/-- **Independence of the lattice.** For a local lattice $L'_v = P\,\mathfrak o_v^n$ ($\det P \ne 0$), the Haar measure on
$O(V)(F_v)$ normalized at $O(L'_v)$ by the density of $L'_v$ in its own coordinates times the Jacobian of the coordinate
change, $\mu(O(L'_v)) = \beta_v(Q_0\circ P, Q_0\circ P)\,\|\det P\|_v^{n+1}/\lambda_v$ ($= 2\,$`latLocalFactor`$/\lambda_v$),
**is** $\mu_v$. This is the $\alpha$ law (`latLocalFactor_eq`) read as an equality of measures. -/
@[kb "weil1982" "§2.2.1, p. 14 (the local measure does not depend on the coordinates)"]
theorem muLoc_eq_haarNorm_latOf (hQ : Q₀.Nondegenerate) {lam : ℝ} (hlam : 0 < lam)
    (P : Matrix (Fin n) (Fin n) 𝔬) (hP : P.det ≠ 0) :
    muLoc v Q₀ lam = haarNorm (stabLat v (orthGroup QF Fv).subtype (latOf v P))
      (isCompact_stabLat v QF (glOf v P hP)) (isOpen_stabLat v QF (glOf v P hP))
      (Real.toNNReal (2 * LatChange.latLocalFactor v Q₀ P / lam)) := by
  have hβ := LatChange.localDensityForm_self_pos v Q₀ hQ
  set K' := stabLat v (orthGroup QF Fv).subtype (latOf v P)
  have hc' := isCompact_stabLat v QF (glOf v P hP)
  have ho' := isOpen_stabLat v QF (glOf v P hP)
  rw [muLoc, haarNorm_eq_haarNorm (isCompact_stdStab v QF) (isOpen_stdStab v QF) hc' ho'
    (relIndex_ne_zero_of_isOpen hc' (isOpen_stdStab v QF)) (relIndex_ne_zero_of_isOpen
      (isCompact_stdStab v QF) ho')]
  congr 1
  rw [Real.coe_toNNReal _ (div_nonneg hβ.le hlam.le), LatChange.latLocalFactor_eq v Q₀ hQ P hP,
    ← LatChange.relRatio_stab_eq_KL, NF.siegelDensity]
  simp only [↓reduceIte]
  congr 1
  ring

/-- **Two lattices give the same measure:** for local lattices $P_1\mathfrak o_v^n$, $P_2\mathfrak o_v^n$, the Haar measures
normalized by their densities (with Jacobians) coincide. -/
@[kb "weil1982" "§2.2.1, p. 14"]
theorem haarNorm_latOf_eq (hQ : Q₀.Nondegenerate) {lam : ℝ} (hlam : 0 < lam)
    (P₁ P₂ : Matrix (Fin n) (Fin n) 𝔬) (hP₁ : P₁.det ≠ 0) (hP₂ : P₂.det ≠ 0) :
    haarNorm (stabLat v (orthGroup QF Fv).subtype (latOf v P₁))
        (isCompact_stabLat v QF (glOf v P₁ hP₁)) (isOpen_stabLat v QF (glOf v P₁ hP₁))
        (Real.toNNReal (2 * LatChange.latLocalFactor v Q₀ P₁ / lam)) =
      haarNorm (stabLat v (orthGroup QF Fv).subtype (latOf v P₂))
        (isCompact_stabLat v QF (glOf v P₂ hP₂)) (isOpen_stabLat v QF (glOf v P₂ hP₂))
        (Real.toNNReal (2 * LatChange.latLocalFactor v Q₀ P₂ / lam)) := by
  rw [← muLoc_eq_haarNorm_latOf v Q₀ hQ hlam P₁ hP₁, ← muLoc_eq_haarNorm_latOf v Q₀ hQ hlam P₂ hP₂]

/-! ### The measure on $SO(V)(F_v)$ -/

/-- $SO(V)(F_v)$ (the type of the open subgroup `soSub` of $O(V)(F_v)$). -/
abbrev SOv : Type := soSub QF Fv

instance : LocallyCompactSpace (SOv v Q₀) :=
  (isClosed_soSub v QF).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (SOv v Q₀) := Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- $SO(V)(F_v)$ carries the subspace $\sigma$-algebra (Mathlib's `Subtype.instMeasurableSpace`), which is its Borel
$\sigma$-algebra. -/
instance : BorelSpace (SOv v Q₀) := inferInstanceAs (BorelSpace (soSub QF Fv : Set (orthGroup QF Fv)))

/-- **$SO(L_v)$ as a subgroup of $SO(V)(F_v)$.** -/
def soStabSO : Subgroup (SOv v Q₀) := (stdStab QF v).subgroupOf (soSub QF Fv)

theorem isCompact_soStabSO : IsCompact (soStabSO v Q₀ : Set (SOv v Q₀)) :=
  (isClosed_soSub v QF).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_stdStab v QF)

theorem isOpen_soStabSO : IsOpen (soStabSO v Q₀ : Set (SOv v Q₀)) :=
  (isOpen_stdStab v QF).preimage continuous_subtype_val

/-- **The local Tamagawa measure on $SO(V)(F_v)$** with convergence factor $\lambda_v$ (default $1$): the Haar measure
normalized by $\mu(SO(L_v)) = \alpha_v(L, L)/\lambda_v$ (this is the local factor of the measure on
$SO(V)(\mathbb A)$). It is the restriction of `muLoc` to the open subgroup $SO(V)(F_v)$ (`muLocSO_eq_comap`). -/
@[kb "weil1982" "§2.2 (local measures), §2.3, p. 21 (convergence factors λ_v)"]
def muLocSO (lam : ℝ := 1) : Measure (SOv v Q₀) :=
  haarNorm (soStabSO v Q₀) (isCompact_soStabSO v Q₀) (isOpen_soStabSO v Q₀)
    (Real.toNNReal (NF.siegelDensity v Q₀ Q₀ / lam))

/-- **$\mu_v(SO(L_v)) = \alpha_v(L,L)/\lambda_v$** on $SO(V)(F_v)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem muLocSO_soStabSO (lam : ℝ) :
    muLocSO v Q₀ lam (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (NF.siegelDensity v Q₀ Q₀ / lam) :=
  haarNorm_self _ _ _

theorem measurableEmbedding_soSub (hQ : Q₀.Nondegenerate) :
    MeasurableEmbedding (Subtype.val : SOv v Q₀ → orthGroup QF Fv) :=
  (isOpen_soSub v QF (nondegenerate_QF Q₀ hQ)).isOpenEmbedding_subtypeVal.measurableEmbedding

/-- **$\mu_v$ on $SO(V)(F_v)$ is the restriction of $\mu_v$ on $O(V)(F_v)$**: $\mu^{SO}_v(S) = \mu_v(S)$ for every set
$S \subseteq SO(V)(F_v)$ (nondegenerate $Q_0$, $n > 0$, $\lambda_v > 0$). -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLocSO_eq_comap (hQ : Q₀.Nondegenerate) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    muLocSO v Q₀ lam = (muLoc v Q₀ lam).comap Subtype.val := by
  have hE := measurableEmbedding_soSub v Q₀ hQ
  set μ := (muLoc v Q₀ lam).comap (Subtype.val : SOv v Q₀ → orthGroup QF Fv)
  have hμ : ∀ S : Set (SOv v Q₀), μ S = muLoc v Q₀ lam (Subtype.val '' S) := fun S => hE.comap_apply _ S
  have : IsMulLeftInvariant μ := by
    refine ⟨fun g => ?_⟩
    ext S hS
    rw [map_apply (measurable_const_mul g) hS, hμ, hμ]
    have : Subtype.val '' ((fun x => g * x) ⁻¹' S) = (g : orthGroup QF Fv)⁻¹ • (Subtype.val '' S) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(g * y : SOv v Q₀), ⟨_, hy, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨g⁻¹ * y, by simpa using hy, by simp⟩
    rw [this, measure_smul]
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [hμ]; exact (hK.image continuous_subtype_val).measure_lt_top⟩
  rw [eq_haarNorm (isCompact_soStabSO v Q₀) (isOpen_soStabSO v Q₀) μ
    (isCompact_soStabSO v Q₀).measure_lt_top.ne, hμ]
  have himg : Subtype.val '' (soStabSO v Q₀ : Set (SOv v Q₀)) = (soStab v Q₀ : Set (orthGroup QF Fv)) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, soStabSO, Subgroup.mem_subgroupOf, soStab, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, h2, rfl⟩
  rw [himg, muLoc_soStab v Q₀ hQ hn hlam, muLocSO]
  rfl

end Measure

end QuadFormsKB.Tamagawa.Measure
