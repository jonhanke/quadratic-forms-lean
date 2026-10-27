import QuadFormsKB.Tamagawa.Measure.Weil.FibrationTwoWays
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleShell
import QuadFormsKB.Tamagawa.Measure.Weil.Fujisaki

/-!
# $G^\natural$ abstractly: $\tau(G^\natural/\mathbb G_m) = 2\,\tau(\ker\nu)$ by Weil's two fibrations

**Layer:** a number field $k$, its ideles $\mathbb A_k^\times$ with the Tamagawa measure `tamIdeles`, and abstract data
(`GnatData`): a locally compact second countable group $M$ with a continuous homomorphism $\nu : M\to T$ ("reduced norm"),
a continuous injective $\iota : \mathbb A_k^\times\to T$, a central closed embedding $s : \mathbb A_k^\times\to M$ with
$\nu(s(u)) = \iota(u^2)$, an open subgroup $A_+\le\mathbb A_k^\times$ which is exactly $\iota^{-1}(\nu(M))$, and a discrete
countable subgroup $\Gamma_M\le M$ ("global points").

From these data:
* $G^\natural := \{(m, a)\in M\times\mathbb A_k^\times : \nu(m) = \iota(a)\}$ (`G`), a closed subgroup (the group
  $\{\alpha\in(D\otimes E\otimes\mathbb A_k)^\times : \operatorname{nrd}\alpha\in\mathbb A_k^\times\}$ when
  $M = (D_E\otimes\mathbb A_k)^\times$);
* $p : G^\natural\to A_+$, $(m,a)\mapsto a$, surjective, with kernel $\cong\ker\nu$ (`kerSEquiv`);
* the centre $Z = \{(s(u), u^2)\}\cong\mathbb A_k^\times$ (`zHom`, `kerZEquiv`) and $P := G^\natural/Z$ (`P`, the group
  $SO(V)(\mathbb A_k)$), $\pi : G^\natural\to P$;
* the Tamagawa-type measure $\mu_G$ := the fibred measure of $\mu_S$ (on $\ker\nu$) over `tamIdeles` restricted to $A_+$ (`muG`),
  and Weil's quotient measure $\mu_P = \mu_G/\mu_Z$, $\mu_Z$ = `tamIdeles` on the centre (`muP`, `fibMeas_muP`);
* $\Gamma := \{(\gamma, f) : \gamma\in\Gamma_M,\ f\in k^\times\}\le G^\natural$ (`gam`) and its image $\pi(\Gamma)$ in $P$
  (`gamP`), discrete (`discreteTopology_gamP`, via Fujisaki's compactness of $k^\times\backslash\mathbb A^1$).

**Main theorem (`covolume_muP`).** If $\operatorname{covol}(\Gamma_M\cap\ker\nu,\ \mu_S) = \tau$, $\mu_S$ is invariant under
conjugation by $M$, $\nu(\Gamma_M)\cap\iota(k^\times) = \iota(k^\times\cap A_+)$ (Eichler) and every $k^\times$-orbit in
$\mathbb A_k^\times$ meets $A_+$ (weak approximation of signs), then
$$\operatorname{covol}(\pi(\Gamma)\backslash P,\ \mu_P) = 2\tau.$$
*Proof* (Weil 1982, §3.2, proof of Thm 3.2.1, p. 43): compute $\mu_G(D\cap\{0\le\log\|p(g)\|<1\})$ in two
ways (`NormalFib.two_ways`). Along $p$ it is $\tau\cdot\operatorname{vol}(k^\times\backslash\mathbb A^1)$ (`IdeleShell`); along $\pi$ it
is $\mu_P(D_P)\cdot\tfrac12\operatorname{vol}(k^\times\backslash\mathbb A^1)$, since $\|p(z(u)g)\| = \|u\|^2\|p(g)\|$ on the centre.
-/

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- **The abstract data of $G^\natural$** over a number field $k$.

Fields:
- `ν`: the "reduced norm" $M\to T$ (continuous homomorphism);
- `ι`: the embedding $\mathbb A_k^\times\to T$ (continuous homomorphism), `ι_injective`;
- `s`: the scalars $\mathbb A_k^\times\to M$ (continuous homomorphism), `s_closedEmbedding`, `s_central`, `ν_s`:
  $\nu(s(u)) = \iota(u^2)$;
- `Apos`: the open subgroup $A_+ = \iota^{-1}(\nu(M))$ of $\mathbb A_k^\times$ (`isOpen_Apos`, `mem_Apos`, `surj_Apos`);
- `ΓM`: the global points, a subgroup of $M$. -/
structure GnatData (k : Type) [Field k] [NumberField k] (M T : Type*) [Group M] [TopologicalSpace M]
    [Group T] [TopologicalSpace T] where
  ν : M →ₜ* T
  ι : (Adeles k)ˣ →ₜ* T
  s : (Adeles k)ˣ →ₜ* M
  ι_injective : Injective ι
  s_closedEmbedding : IsClosedEmbedding s
  s_central : ∀ u m, s u * m = m * s u
  ν_s : ∀ u, ν (s u) = ι (u ^ 2)
  Apos : Subgroup (Adeles k)ˣ
  isOpen_Apos : IsOpen (Apos : Set (Adeles k)ˣ)
  mem_Apos : ∀ m a, ν m = ι a → a ∈ Apos
  surj_Apos : ∀ a ∈ Apos, ∃ m, ν m = ι a
  ΓM : Subgroup M

namespace GnatData

variable {k : Type} [Field k] [NumberField k] {M T : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [Group T] [TopologicalSpace T]
  [IsTopologicalGroup T] [T2Space T]
  (d : GnatData k M T)

/-! ### The group $G^\natural$ -/

/-- $G^\natural = \{(m, a) : \nu(m) = \iota(a)\}\le M\times\mathbb A_k^\times$. -/
def gnat : Subgroup (M × (Adeles k)ˣ) where
  carrier := {x | d.ν x.1 = d.ι x.2}
  mul_mem' {x y} hx hy := by
    simp only [mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at hx hy ⊢; rw [hx, hy]
  one_mem' := by simp
  inv_mem' {x} hx := by simp only [mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at hx ⊢; rw [hx]

theorem mem_gnat {x : M × (Adeles k)ˣ} : x ∈ d.gnat ↔ d.ν x.1 = d.ι x.2 := Iff.rfl

/-- The group $G^\natural$ as a type. -/
abbrev G : Type _ := d.gnat

theorem isClosed_gnat : IsClosed (d.gnat : Set (M × (Adeles k)ˣ)) :=
  isClosed_eq (d.ν.continuous.comp continuous_fst) (d.ι.continuous.comp continuous_snd)

instance : LocallyCompactSpace d.G := d.isClosed_gnat.isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : SecondCountableTopology d.G := TopologicalSpace.Subtype.secondCountableTopology _
instance : StandardBorelSpace d.G := by
  have := polishSpace_of_isTopologicalGroup d.G
  infer_instance

theorem ν_fst (g : d.G) : d.ν (g : M × (Adeles k)ˣ).1 = d.ι (g : M × (Adeles k)ˣ).2 := g.2

/-! ### The norm map $p : G^\natural\to A_+$ and its kernel -/

instance : SecondCountableTopology d.Apos := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace d.Apos := d.isOpen_Apos.isOpenEmbedding_subtypeVal.locallyCompactSpace
instance : StandardBorelSpace d.Apos := by
  have := polishSpace_of_isTopologicalGroup d.Apos
  infer_instance

/-- $p : G^\natural\to A_+$, $(m, a)\mapsto a$. -/
def p : d.G →* d.Apos where
  toFun g := ⟨(g : M × (Adeles k)ˣ).2, d.mem_Apos _ _ g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coe_p (g : d.G) : ((d.p g : d.Apos) : (Adeles k)ˣ) = (g : M × (Adeles k)ˣ).2 := rfl

theorem continuous_p : Continuous d.p :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

theorem measurable_p : Measurable d.p := d.continuous_p.measurable

theorem p_surjective : Surjective d.p := fun a => by
  obtain ⟨m, hm⟩ := d.surj_Apos a a.2
  exact ⟨⟨(m, a), hm⟩, rfl⟩

theorem mem_ker_p {g : d.G} : g ∈ d.p.ker ↔ (g : M × (Adeles k)ˣ).2 = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

theorem isClosed_ker_p : IsClosed (d.p.ker : Set d.G) := by
  have : (d.p.ker : Set d.G) = (fun g : d.G => (g : M × (Adeles k)ˣ).2) ⁻¹' {1} := by
    ext g; exact d.mem_ker_p
  rw [this]; exact isClosed_singleton.preimage (continuous_snd.comp continuous_subtype_val)

theorem fst_mem_ker_ν (g : d.p.ker) : ((g : d.G) : M × (Adeles k)ˣ).1 ∈ (d.ν : M →* T).ker := by
  rw [MonoidHom.mem_ker]
  have h1 := d.ν_fst (g : d.G)
  rw [d.mem_ker_p.1 g.2, map_one] at h1
  exact h1

theorem pair_mem_gnat (m : (d.ν : M →* T).ker) : ((m : M), (1 : (Adeles k)ˣ)) ∈ d.gnat := by
  rw [mem_gnat, map_one]; exact m.2

/-- **$\ker p\cong\ker\nu$**, $(m, 1)\mapsto m$. -/
def kerSEquiv : d.p.ker ≃ₜ* (d.ν : M →* T).ker where
  toFun g := ⟨((g : d.G) : M × (Adeles k)ˣ).1, d.fst_mem_ker_ν g⟩
  invFun m := ⟨⟨((m : M), 1), d.pair_mem_gnat m⟩, d.mem_ker_p.2 rfl⟩
  left_inv g := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext rfl (d.mem_ker_p.1 g.2).symm
  right_inv m := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _).subtype_mk _

@[simp] theorem coe_kerSEquiv (g : d.p.ker) :
    ((d.kerSEquiv g : (d.ν : M →* T).ker) : M) = ((g : d.G) : M × (Adeles k)ˣ).1 := rfl

instance : SecondCountableTopology d.p.ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace d.p.ker := d.isClosed_ker_p.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### The centre $Z\cong\mathbb A_k^\times$ and $P = G^\natural/Z$ -/

/-- The centre $u\mapsto(s(u), u^2)$. -/
def zHom : (Adeles k)ˣ →* d.G where
  toFun u := ⟨(d.s u, u ^ 2), d.ν_s u⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) (one_pow 2))
  map_mul' u v := Subtype.ext (Prod.ext (map_mul _ u v) (mul_pow u v 2))

@[simp] theorem coe_zHom (u : (Adeles k)ˣ) : ((d.zHom u : d.G) : M × (Adeles k)ˣ) = (d.s u, u ^ 2) := rfl

theorem continuous_zHom : Continuous d.zHom :=
  (d.s.continuous.prodMk (continuous_pow 2)).subtype_mk _

theorem s_injective : Injective d.s := d.s_closedEmbedding.injective

theorem zHom_central (u : (Adeles k)ˣ) (g : d.G) : d.zHom u * g = g * d.zHom u :=
  Subtype.ext (Prod.ext (d.s_central u _) (mul_comm _ _))

/-- $Z = \{g : g_1\in s(\mathbb A_k^\times)\}$ (by injectivity of $\iota$). -/
theorem mem_range_zHom_iff (g : d.G) :
    g ∈ d.zHom.range ↔ (g : M × (Adeles k)ˣ).1 ∈ Set.range d.s := by
  constructor
  · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, Subtype.ext (Prod.ext hu ?_)⟩
    apply d.ι_injective
    change d.ι (u ^ 2) = d.ι (g : M × (Adeles k)ˣ).2
    rw [← d.ν_s, ← d.ν_fst, hu]

theorem isClosed_range_zHom : IsClosed (d.zHom.range : Set d.G) := by
  have : (d.zHom.range : Set d.G) = (fun g : d.G => (g : M × (Adeles k)ˣ).1) ⁻¹' Set.range d.s := by
    ext g; exact d.mem_range_zHom_iff g
  rw [this]
  exact d.s_closedEmbedding.isClosed_range.preimage (continuous_fst.comp continuous_subtype_val)

instance normal_range_zHom : d.zHom.range.Normal :=
  ⟨fun n hn g => by
    obtain ⟨u, rfl⟩ := hn
    refine ⟨u, ?_⟩
    rw [← d.zHom_central u g, mul_assoc, mul_inv_cancel, mul_one]⟩

/-- $P = G^\natural/Z$ ($= SO(V)(\mathbb A_k)$). -/
abbrev P : Type _ := d.G ⧸ d.zHom.range

instance : MeasurableSpace d.P := borel _
instance : BorelSpace d.P := ⟨rfl⟩
instance : T2Space d.P := by
  have : IsClosed (d.zHom.range : Set d.G) := d.isClosed_range_zHom
  infer_instance
instance : StandardBorelSpace d.P := by
  have := polishSpace_of_isTopologicalGroup d.P
  infer_instance

/-- The projection $\pi : G^\natural\to P$. -/
abbrev π : d.G →* d.P := QuotientGroup.mk' _

theorem π_surjective : Surjective d.π := QuotientGroup.mk'_surjective _
theorem continuous_π : Continuous d.π := continuous_quot_mk
theorem measurable_π : Measurable d.π := d.continuous_π.measurable

theorem mem_ker_π {g : d.G} : g ∈ d.π.ker ↔ g ∈ d.zHom.range := by rw [QuotientGroup.ker_mk']

theorem isClosed_ker_π : IsClosed (d.π.ker : Set d.G) := by
  rw [QuotientGroup.ker_mk']; exact d.isClosed_range_zHom

instance : SecondCountableTopology d.π.ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace d.π.ker := d.isClosed_ker_π.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The scalar part $Z\to\mathbb A_k^\times$ (inverse of $s$ on its range). -/
def scalarOf (g : d.π.ker) : (Adeles k)ˣ :=
  (d.s_closedEmbedding.isEmbedding.toHomeomorph).symm
    ⟨((g : d.G) : M × (Adeles k)ˣ).1, (d.mem_range_zHom_iff _).1 (d.mem_ker_π.1 g.2)⟩

theorem s_scalarOf (g : d.π.ker) : d.s (d.scalarOf g) = ((g : d.G) : M × (Adeles k)ˣ).1 := by
  have := (d.s_closedEmbedding.isEmbedding.toHomeomorph).apply_symm_apply
    ⟨((g : d.G) : M × (Adeles k)ˣ).1, (d.mem_range_zHom_iff _).1 (d.mem_ker_π.1 g.2)⟩
  exact congrArg Subtype.val this

theorem zHom_scalarOf (g : d.π.ker) : d.zHom (d.scalarOf g) = g := by
  obtain ⟨u, hu⟩ := d.mem_ker_π.1 g.2
  have h1 : d.scalarOf g = u := d.s_injective (by
    rw [d.s_scalarOf, ← hu]; rfl)
  rw [h1, hu]

theorem continuous_scalarOf : Continuous d.scalarOf :=
  (d.s_closedEmbedding.isEmbedding.toHomeomorph).symm.continuous.comp
    (((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _)

/-- **$\mathbb A_k^\times\cong Z = \ker\pi$** as topological groups. -/
def kerZEquiv : (Adeles k)ˣ ≃ₜ* d.π.ker where
  toFun u := ⟨d.zHom u, d.mem_ker_π.2 ⟨u, rfl⟩⟩
  invFun := d.scalarOf
  left_inv u := d.s_injective (by rw [d.s_scalarOf]; rfl)
  right_inv g := Subtype.ext (d.zHom_scalarOf g)
  map_mul' u v := Subtype.ext (map_mul _ u v)
  continuous_toFun := d.continuous_zHom.subtype_mk _
  continuous_invFun := d.continuous_scalarOf

@[simp] theorem coe_kerZEquiv (u : (Adeles k)ˣ) : ((d.kerZEquiv u : d.π.ker) : d.G) = d.zHom u := rfl

/-! ### The measures -/

omit [IsTopologicalGroup M] [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [IsTopologicalGroup T]
  [T2Space T] in
/-- Linearity of the fibred measure in the base measure (as `fibMeas_smul_base`). -/
theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.fibMeas_smul_base' {G Q : Type*} [Group G] [Group Q]
    [MeasurableSpace G] [MeasurableSpace Q] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q]
    [StandardBorelSpace G] [MeasurableSpace.CountablySeparated Q] (N : G →* Q) (hN : Function.Surjective N)
    (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] (c : ℝ≥0∞) :
    NormalFib.fibMeas N hN (c • μQ) μK = c • NormalFib.fibMeas N hN μQ μK := by
  ext s hs
  rw [NormalFib.fibMeas_apply N hN hNm _ μK hs, Measure.smul_apply, NormalFib.fibMeas_apply N hN hNm μQ μK hs,
    lintegral_smul_measure, smul_eq_mul]

theorem isClosed_ker_ν : IsClosed ((d.ν : M →* T).ker : Set M) := by
  have : ((d.ν : M →* T).ker : Set M) = d.ν ⁻¹' {1} := by ext m; simp [MonoidHom.mem_ker]
  rw [this]; exact isClosed_singleton.preimage d.ν.continuous

instance : SecondCountableTopology (d.ν : M →* T).ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace (d.ν : M →* T).ker :=
  d.isClosed_ker_ν.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The base measure on $A_+$: `tamIdeles` restricted to the open subgroup $A_+$. -/
def muA : Measure d.Apos := (tamIdeles k).comap Subtype.val

theorem measurableEmbedding_Apos : MeasurableEmbedding (Subtype.val : d.Apos → (Adeles k)ˣ) :=
  MeasurableEmbedding.subtype_coe d.isOpen_Apos.measurableSet

theorem muA_apply (s : Set d.Apos) : d.muA s = tamIdeles k (Subtype.val '' s) :=
  d.measurableEmbedding_Apos.comap_apply _ _

instance : d.muA.IsMulLeftInvariant :=
  isMulLeftInvariant_comap_subgroup (tamIdeles k) d.Apos d.isOpen_Apos

instance : IsFiniteMeasureOnCompacts d.muA := by
  refine ⟨fun K hK => ?_⟩
  rw [muA_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top


theorem muA_univ_ne_zero : d.muA univ ≠ 0 := by
  rw [muA_apply, image_univ, Subtype.range_coe]
  exact (d.isOpen_Apos.measure_pos (tamIdeles k) ⟨1, d.Apos.one_mem⟩).ne'

variable (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]


/-- The fibre measure on $\ker p\cong\ker\nu$. -/
def muS : Measure d.p.ker := μSν.map d.kerSEquiv.symm

instance : (d.muS μSν).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _


/-- **The measure on $G^\natural$**: fibred along $p$, fibre $\mu_S$, base `tamIdeles` on $A_+$ (Weil 1982, §2.4, Thm 2.4.4). -/
def muG : Measure d.G := NormalFib.fibMeas d.p d.p_surjective d.muA (d.muS μSν)

instance : (d.muG μSν).IsMulLeftInvariant :=
  NormalFib.isMulLeftInvariant_fibMeas _ _ d.measurable_p _ _

instance : IsFiniteMeasureOnCompacts (d.muG μSν) :=
  ⟨fun _ hC => NormalFib.fibMeas_compact_lt_top _ _ d.continuous_p _ _ d.isClosed_ker_p hC⟩


theorem muG_univ_ne_zero : d.muG μSν univ ≠ 0 := by
  rw [muG, NormalFib.fibMeas_univ _ _ d.measurable_p]
  exact mul_ne_zero (isOpen_univ.measure_pos (d.muS μSν) univ_nonempty).ne' d.muA_univ_ne_zero

/-- The Tamagawa measure of the centre: `tamIdeles` on $Z\cong\mathbb A_k^\times$. -/
def muZ : Measure d.π.ker := (tamIdeles k).map d.kerZEquiv

instance : d.muZ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _


/-- A reference Haar measure on $P$. -/
def muPRef : Measure d.P := Measure.haar

instance : d.muPRef.IsHaarMeasure := by unfold muPRef; infer_instance

/-- The fibred measure of the reference measure along $\pi$. -/
def nuRef : Measure d.G := NormalFib.fibMeas d.π d.π_surjective d.muPRef d.muZ

instance : d.nuRef.IsMulLeftInvariant := NormalFib.isMulLeftInvariant_fibMeas _ _ d.measurable_π _ _

instance : IsFiniteMeasureOnCompacts d.nuRef :=
  ⟨fun _ hC => NormalFib.fibMeas_compact_lt_top _ _ d.continuous_π _ _ d.isClosed_ker_π hC⟩


theorem nuRef_univ_ne_zero : d.nuRef univ ≠ 0 := by
  rw [nuRef, NormalFib.fibMeas_univ _ _ d.measurable_π]
  exact mul_ne_zero (isOpen_univ.measure_pos d.muZ univ_nonempty).ne'
    (isOpen_univ.measure_pos d.muPRef univ_nonempty).ne'

/-- A reference compact set with nonempty interior in $G^\natural$. -/
def refSet : Set d.G := (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.G))

theorem isCompact_refSet : IsCompact d.refSet :=
  (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.G)).isCompact

theorem haar_refSet_ne_zero : (Measure.haar : Measure d.G) d.refSet ≠ 0 :=
  (measure_pos_of_nonempty_interior _
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.G)).interior_nonempty).ne'

theorem haar_refSet_ne_top : (Measure.haar : Measure d.G) d.refSet ≠ ∞ :=
  d.isCompact_refSet.measure_lt_top.ne

/-- A left-invariant measure, finite on compacts, nonzero, is a positive finite multiple of Haar measure on
$G^\natural$, with constant $\mu(R)/\operatorname{haar}(R)$. -/
theorem eq_smul_haar (μ : Measure d.G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [SigmaFinite μ]
    (h0 : μ univ ≠ 0) :
    μ = (μ d.refSet / (Measure.haar : Measure d.G) d.refSet) • Measure.haar ∧ μ d.refSet ≠ 0 ∧
      μ d.refSet ≠ ∞ := by
  have h := measure_eq_div_smul μ (Measure.haar : Measure d.G) d.haar_refSet_ne_zero d.haar_refSet_ne_top
  refine ⟨h, fun hz => h0 ?_, d.isCompact_refSet.measure_lt_top.ne⟩
  rw [h, hz, ENNReal.zero_div, zero_smul]; rfl

/-- The constant $c$ with $\nu_{\mathrm{ref}} = c\,\mu_G$. -/
def pConst : ℝ≥0∞ := d.nuRef d.refSet / d.muG μSν d.refSet

theorem pConst_ne_zero : d.pConst μSν ≠ 0 :=
  ENNReal.div_ne_zero.2 ⟨(d.eq_smul_haar d.nuRef d.nuRef_univ_ne_zero).2.1,
    (d.eq_smul_haar _ (d.muG_univ_ne_zero μSν)).2.2⟩

theorem pConst_ne_top : d.pConst μSν ≠ ∞ :=
  ENNReal.div_ne_top (d.eq_smul_haar d.nuRef d.nuRef_univ_ne_zero).2.2
    (d.eq_smul_haar _ (d.muG_univ_ne_zero μSν)).2.1

theorem nuRef_eq_smul_muG : d.nuRef = d.pConst μSν • d.muG μSν := by
  obtain ⟨h1, h10, h1t⟩ := d.eq_smul_haar d.nuRef d.nuRef_univ_ne_zero
  obtain ⟨h2, h20, h2t⟩ := d.eq_smul_haar _ (d.muG_univ_ne_zero μSν)
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  rw [smul_smul, pConst]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc (d.muG μSν d.refSet)⁻¹,
    ENNReal.inv_mul_cancel h20 h2t, one_mul]

/-- **Weil's quotient measure $\mu_P = \mu_G/\mu_Z$ on $P = G^\natural/Z$** (`fibMeas_muP`). -/
def muP : Measure d.P := (d.pConst μSν)⁻¹ • d.muPRef

theorem isHaarMeasure_muP : (d.muP μSν).IsHaarMeasure :=
  IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (d.pConst_ne_top μSν)) (ENNReal.inv_ne_top.2 (d.pConst_ne_zero μSν))

instance : (d.muP μSν).IsMulLeftInvariant := by
  have := d.isHaarMeasure_muP μSν; infer_instance

/-- **The quotient fibration**: $\mu_G = \int_P(g_q\cdot)_*\mu_Z\,d\mu_P(q)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page] (quotient measure on G/Z)"]
theorem fibMeas_muP : NormalFib.fibMeas d.π d.π_surjective (d.muP μSν) d.muZ = d.muG μSν := by
  rw [muP, fibMeas_smul_base' _ _ d.measurable_π]
  change (d.pConst μSν)⁻¹ • d.nuRef = _
  rw [d.nuRef_eq_smul_muG μSν, smul_smul, ENNReal.inv_mul_cancel (d.pConst_ne_zero μSν) (d.pConst_ne_top μSν),
    one_smul]

/-- **Uniqueness of the quotient measure.** -/
theorem muP_unique (μ' : Measure d.P) [μ'.IsHaarMeasure]
    (h : NormalFib.fibMeas d.π d.π_surjective μ' d.muZ = d.muG μSν) : μ' = d.muP μSν := by
  have h1 := measure_eq_div_smul μ' d.muPRef (s := (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.P)))
    (measure_pos_of_nonempty_interior _
      (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.P)).interior_nonempty).ne'
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.P)).isCompact.measure_lt_top.ne
  set c := μ' (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.P)) /
    d.muPRef (Classical.arbitrary (TopologicalSpace.PositiveCompacts d.P))
  have hc : NormalFib.fibMeas d.π d.π_surjective μ' d.muZ = c • d.nuRef := by
    rw [h1, fibMeas_smul_base' _ _ d.measurable_π]; rfl
  rw [h, d.nuRef_eq_smul_muG μSν, smul_smul] at hc
  have hR := congrArg (fun μ => μ d.refSet) hc
  simp only [Measure.smul_apply, smul_eq_mul] at hR
  obtain ⟨-, h20, h2t⟩ := d.eq_smul_haar _ (d.muG_univ_ne_zero μSν)
  have hc1 : c * d.pConst μSν = 1 := by
    have : 1 * d.muG μSν d.refSet = c * d.pConst μSν * d.muG μSν d.refSet := by rw [one_mul]; exact hR
    exact ((ENNReal.mul_left_inj h20 h2t).1 this).symm
  rw [h1, muP]
  congr 1
  exact (ENNReal.eq_inv_of_mul_eq_one_left hc1)

/-! ### Global points -/

/-- $\Gamma = \{(\gamma, f) : \gamma\in\Gamma_M,\ f\in k^\times\}\le G^\natural$. -/
def gam : Subgroup d.G where
  carrier := {g | (g : M × (Adeles k)ˣ).1 ∈ d.ΓM ∧ (g : M × (Adeles k)ˣ).2 ∈ diagUnitsSub k}
  mul_mem' hx hy := ⟨d.ΓM.mul_mem hx.1 hy.1, (diagUnitsSub k).mul_mem hx.2 hy.2⟩
  one_mem' := ⟨d.ΓM.one_mem, (diagUnitsSub k).one_mem⟩
  inv_mem' hx := ⟨d.ΓM.inv_mem hx.1, (diagUnitsSub k).inv_mem hx.2⟩

theorem mem_gam {g : d.G} :
    g ∈ d.gam ↔ (g : M × (Adeles k)ˣ).1 ∈ d.ΓM ∧ (g : M × (Adeles k)ˣ).2 ∈ diagUnitsSub k := Iff.rfl

/-- The first coordinate determines a point of $G^\natural$ ($\iota$ is injective). -/
theorem fst_injective : Injective fun g : d.G => (g : M × (Adeles k)ˣ).1 := fun g h hgh => by
  apply Subtype.ext
  refine Prod.ext hgh (d.ι_injective ?_)
  rw [← d.ν_fst, ← d.ν_fst]; exact congrArg d.ν hgh

variable [DiscreteTopology d.ΓM] [Countable d.ΓM]

instance : Countable d.gam :=
  Injective.countable (f := fun g : d.gam => (⟨((g : d.G) : M × (Adeles k)ˣ).1, g.2.1⟩ : d.ΓM))
    fun g h hgh => Subtype.ext (d.fst_injective (congrArg Subtype.val hgh))

instance : DiscreteTopology d.gam :=
  DiscreteTopology.of_continuous_injective
    (f := fun g : d.gam => (⟨((g : d.G) : M × (Adeles k)ˣ).1, g.2.1⟩ : d.ΓM))
    (((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _)
    fun g h hgh => Subtype.ext (d.fst_injective (congrArg Subtype.val hgh))

/-- $\pi(\Gamma)$, the global points of $P$. -/
abbrev gamP : Subgroup d.P := NormalFib.gammaQ d.π d.gam

instance : DiscreteTopology (NormalFib.gammaK d.p d.gam) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : NormalFib.gammaK d.p d.gam => (⟨((x : d.p.ker) : d.G), x.2⟩ : d.gam))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

instance : DiscreteTopology (NormalFib.gammaK d.π d.gam) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : NormalFib.gammaK d.π d.gam => (⟨((x : d.π.ker) : d.G), x.2⟩ : d.gam))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

theorem coe_mem_diagUnitsSub_of_gammaQ_p (δ : NormalFib.gammaQ d.p d.gam) :
    ((δ : d.Apos) : (Adeles k)ˣ) ∈ diagUnitsSub k := by
  obtain ⟨_, ⟨g, hg, rfl⟩⟩ := δ
  exact hg.2

instance : DiscreteTopology (NormalFib.gammaQ d.p d.gam) :=
  DiscreteTopology.of_continuous_injective
    (f := fun δ : NormalFib.gammaQ d.p d.gam => (⟨_, d.coe_mem_diagUnitsSub_of_gammaQ_p δ⟩ : diagUnitsSub k))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

theorem log_norm_p_gam {g : d.G} (hg : g ∈ d.gam) :
    Real.log (ideleNorm k ((d.p g : d.Apos) : (Adeles k)ˣ)) = 0 := by
  obtain ⟨f, hf⟩ := hg.2
  rw [coe_p, ← hf, ideleNorm_diagUnits, Real.log_one]

theorem zHom_diag_mem_gam (hsΓ : ∀ u, d.s u ∈ d.ΓM ↔ u ∈ diagUnitsSub k) {u : (Adeles k)ˣ}
    (hu : u ∈ diagUnitsSub k) : d.zHom u ∈ d.gam :=
  ⟨(hsΓ u).2 hu, (diagUnitsSub k).pow_mem hu 2⟩

theorem log_norm_p_zHom_mul (u : (Adeles k)ˣ) (g : d.G) :
    Real.log (ideleNorm k ((d.p (d.zHom u * g) : d.Apos) : (Adeles k)ˣ)) =
      2 * Real.log (ideleNorm k u) + Real.log (ideleNorm k ((d.p g : d.Apos) : (Adeles k)ˣ)) := by
  rw [map_mul, Subgroup.coe_mul, ideleNorm_mul, Real.log_mul (ideleNorm_pos _).ne' (ideleNorm_pos _).ne', coe_p,
    coe_zHom, sq, ideleNorm_mul, Real.log_mul (ideleNorm_pos _).ne' (ideleNorm_pos _).ne']
  ring

/-- **$\pi(\Gamma)$ is discrete in $P$.** If $\pi(\gamma)\in\pi(U)$ for a small neighbourhood $U$ of $1$, then $\gamma = u\,z(w)$ with
$\|w\|$ bounded; Fujisaki's compactness of $k^\times\backslash\mathbb A^1$ (`exists_isCompact_ideleOne_mul_mem`) gives
$w = f\,c$ with $f\in k^\times$ and $c$ in a compact set, so $\gamma z(f)^{-1}$ lies in $\Gamma\cap K$ for a compact $K$, a finite set. -/
theorem discreteTopology_gamP (hsΓ : ∀ u, d.s u ∈ d.ΓM ↔ u ∈ diagUnitsSub k) : DiscreteTopology d.gamP := by
  classical
  -- the neighbourhood `U`
  obtain ⟨K0, hK0, hK0n⟩ := exists_compact_mem_nhds (1 : d.G)
  set L : d.G → ℝ := fun g => Real.log (ideleNorm k ((d.p g : d.Apos) : (Adeles k)ˣ))
  have hLc : Continuous L :=
    Real.continuousOn_log.comp_continuous (continuous_ideleNorm.comp (continuous_subtype_val.comp d.continuous_p))
      fun g => (ideleNorm_pos _).ne'
  set U : Set d.G := interior K0 ∩ L ⁻¹' Ioo (-1) 1
  have hUo : IsOpen U := isOpen_interior.inter (isOpen_Ioo.preimage hLc)
  have h1U : (1 : d.G) ∈ U := ⟨mem_interior_iff_mem_nhds.2 hK0n, by
    simp only [mem_preimage, L, map_one, OneMemClass.coe_one, ideleNorm_one, Real.log_one, mem_Ioo]; norm_num⟩
  -- the compact set `C3 ⊆ 𝔸^×`
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem k
  set I : Set (Multiplicative ℝ) := Multiplicative.toAdd ⁻¹' Icc (-1) 1
  have hI : IsCompact I := by
    have : I = Multiplicative.ofAdd '' Icc (-1 : ℝ) 1 := by
      ext t; simp [I]
    rw [this]; exact isCompact_Icc.image continuous_ofAdd
  set C3 : Set (Adeles k)ˣ := (ideleSplit k).symm '' (C ×ˢ I)
  have hC3 : IsCompact C3 := (hC.prod hI).image (ideleSplit k).symm.continuous
  set K : Set d.G := (fun x : d.G × (Adeles k)ˣ => x.1 * d.zHom x.2) '' (K0 ×ˢ C3)
  have hK : IsCompact K := (hK0.prod hC3).image (continuous_fst.mul (d.continuous_zHom.comp continuous_snd))
  -- `Γ ∩ K` is finite
  have hfin : ((Subtype.val : d.gam → d.G) ⁻¹' K).Finite := by
    have hcl : IsClosed (d.gam : Set d.G) := Subgroup.isClosed_of_discrete
    have : DiscreteTopology (d.gam : Set d.G) := inferInstanceAs (DiscreteTopology d.gam)
    exact (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  -- every element of `π(Γ) ∩ π(U)` is `π` of an element of `Γ ∩ K`
  have hkey : ∀ γ : d.G, γ ∈ d.gam → d.π γ ∈ d.π '' U →
      ∃ γ' : d.gam, (γ' : d.G) ∈ K ∧ d.π γ' = d.π γ := by
    rintro γ hγ ⟨u, hu, huγ⟩
    have hz : u⁻¹ * γ ∈ d.zHom.range := by
      rw [← d.mem_ker_π, MonoidHom.mem_ker, map_mul, map_inv, huγ, inv_mul_cancel]
    obtain ⟨w, hw⟩ := hz
    have hγeq : γ = u * d.zHom w := by rw [hw, mul_inv_cancel_left]
    -- `log ‖w‖ ∈ (-1/2, 1/2)`
    have hLw : Real.log (ideleNorm k w) ∈ Icc (-1 : ℝ) 1 := by
      have h0 := d.log_norm_p_gam hγ
      rw [hγeq, ← d.zHom_central, d.log_norm_p_zHom_mul] at h0
      have hu' := hu.2
      simp only [mem_preimage, mem_Ioo, L] at hu'
      constructor <;> linarith
    -- `w = f · c3`
    set w1 := ((ideleSplit k) w).1
    obtain ⟨f, hf, hfc⟩ := hCx w1
    obtain ⟨f', hf'⟩ := Subgroup.mem_subgroupOf.1 hf
    set c3 := (ideleSplit k).symm ((f⁻¹ * w1), ((ideleSplit k) w).2)
    have hc3 : c3 ∈ C3 := ⟨_, ⟨hfc, by
      simp only [I, mem_preimage, ideleSplit_apply_snd, toAdd_ofAdd]; exact hLw⟩, rfl⟩
    have hwfc : w = (f : (Adeles k)ˣ) * c3 := by
      have hw' : ((w1 : ideleOne k) : (Adeles k)ˣ) * normSectionHom k ((ideleSplit k) w).2 = w :=
        (ideleSplit k).symm_apply_apply w
      calc w = ((w1 : ideleOne k) : (Adeles k)ˣ) * normSectionHom k ((ideleSplit k) w).2 := hw'.symm
        _ = (f : (Adeles k)ˣ) * c3 := by
          simp only [c3, ideleSplit_symm_apply', Subgroup.coe_mul, Subgroup.coe_inv]; group
    have hfΓ : ((f : ideleOne k) : (Adeles k)ˣ) ∈ diagUnitsSub k := Subgroup.mem_subgroupOf.1 hf
    refine ⟨⟨γ * (d.zHom (f : (Adeles k)ˣ))⁻¹, d.gam.mul_mem hγ (d.gam.inv_mem (d.zHom_diag_mem_gam hsΓ hfΓ))⟩,
      ⟨(u, c3), ⟨interior_subset hu.1, hc3⟩, ?_⟩, ?_⟩
    · simp only
      rw [hγeq, hwfc, mul_comm (f : (Adeles k)ˣ) c3, map_mul, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    · change d.π (γ * (d.zHom (f : (Adeles k)ˣ))⁻¹) = d.π γ
      rw [map_mul, map_inv, show d.π (d.zHom (f : (Adeles k)ˣ)) = 1 from d.mem_ker_π.2 ⟨_, rfl⟩, inv_one,
        mul_one]
  -- conclude: `{1}` is open in `π(Γ)`
  set Fin0 : Set d.P := (fun γ : d.gam => d.π γ) '' ((Subtype.val : d.gam → d.G) ⁻¹' K) \ {1}
  have hFin0 : Fin0.Finite := (hfin.image _).diff
  set V : Set d.P := d.π '' U \ Fin0
  have hVo : IsOpen V := (QuotientGroup.isOpenMap_coe _ hUo).sdiff hFin0.isClosed
  have h1V : (1 : d.P) ∈ V := ⟨⟨1, h1U, map_one _⟩, fun h => h.2 rfl⟩
  apply discreteTopology_of_isOpen_singleton_one
  refine ⟨V, hVo, ?_⟩
  ext ⟨q, γ, hγ, rfl⟩
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨hqU, hqF⟩
    obtain ⟨γ', hγ'K, hγ'π⟩ := hkey γ hγ hqU
    by_contra hne
    apply hqF
    refine ⟨⟨γ', hγ'K, hγ'π⟩, fun h => hne (Subtype.ext h)⟩
  · intro h
    have : d.π γ = 1 := congrArg Subtype.val h
    rw [this]; exact h1V

/-! ### The main theorem: $\operatorname{covol}(\pi(\Gamma)\backslash P,\mu_P) = 2\tau$ -/

omit [IsTopologicalGroup M] [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] [IsTopologicalGroup T] [T2Space T] [DiscreteTopology d.ΓM] [Countable d.ΓM] in
/-- Transport of an exact fundamental domain along a group isomorphism matching the subgroups (as
`isExactFD_image_mulEquiv`). -/
theorem _root_.QuadFormsKB.Tamagawa.Measure.Weil.isExactFD_image_mulEquiv' {H K : Type*} [Group H] [Group K]
    [MeasurableSpace H] [MeasurableSpace K] (e : H ≃* K) (hem : Measurable e.symm) (A : Subgroup H)
    (B : Subgroup K) (hAB : ∀ x, e x ∈ B ↔ x ∈ A) {E : Set H} (hE : IsExactFD (Γ := A) E) :
    IsExactFD (Γ := B) (e '' E) := by
  have himg : e '' E = e.symm ⁻¹' E := e.toEquiv.image_eq_preimage_symm E
  refine ⟨himg ▸ hE.1.preimage hem, fun y => ?_⟩
  obtain ⟨α, hα, huniq⟩ := hE.2 (e.symm y)
  refine ⟨⟨e α, (hAB α).2 α.2⟩, ?_, fun β hβ => ?_⟩
  · refine ⟨α • e.symm y, hα, ?_⟩
    change e ((α : H) * e.symm y) = e α * y
    rw [map_mul, e.apply_symm_apply]
  · rw [himg] at hβ
    have hβA : e.symm β ∈ A := by rw [← hAB, e.apply_symm_apply]; exact β.2
    have h1 : (⟨e.symm β, hβA⟩ : A) • e.symm y ∈ E := by
      change e.symm (β : K) * e.symm y ∈ E
      rw [← map_mul]; exact hβ
    have h2 := huniq _ h1
    apply Subtype.ext
    change (β : K) = e α
    rw [← h2]
    exact (e.apply_symm_apply _).symm

theorem kerSEquiv_mem_iff (x : d.p.ker) :
    d.kerSEquiv x ∈ d.ΓM.subgroupOf (d.ν : M →* T).ker ↔ x ∈ NormalFib.gammaK d.p d.gam := by
  rw [Subgroup.mem_subgroupOf, coe_kerSEquiv]
  change _ ↔ ((x : d.G)) ∈ d.gam
  rw [mem_gam, d.mem_ker_p.1 x.2]
  exact ⟨fun h => ⟨h, (diagUnitsSub k).one_mem⟩, fun h => h.1⟩

theorem kerZEquiv_mem_iff (hsΓ : ∀ u, d.s u ∈ d.ΓM ↔ u ∈ diagUnitsSub k) (u : (Adeles k)ˣ) :
    d.kerZEquiv u ∈ NormalFib.gammaK d.π d.gam ↔ u ∈ diagUnitsSub k := by
  change d.zHom u ∈ d.gam ↔ _
  rw [mem_gam, coe_zHom]
  exact ⟨fun h => (hsΓ u).1 h.1, fun h => ⟨(hsΓ u).2 h, (diagUnitsSub k).pow_mem h 2⟩⟩

/-- $\operatorname{Ad}(g)$ on $\ker p$ corresponds to $\operatorname{Ad}(g_1)$ on $\ker\nu$. -/
theorem adK_p_kerSEquiv_symm (g : d.G) (m : (d.ν : M →* T).ker) :
    NormalFib.adK d.p g (d.kerSEquiv.symm m) =
      d.kerSEquiv.symm (NormalFib.adK (d.ν : M →* T) (g : M × (Adeles k)ˣ).1 m) := by
  apply Subtype.ext; apply Subtype.ext
  refine Prod.ext rfl ?_
  change (g : M × (Adeles k)ˣ).2 * 1 * ((g : M × (Adeles k)ˣ).2)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem measurable_adK_ν (m : M) : Measurable (NormalFib.adK (d.ν : M →* T) m) :=
  ((((continuous_const_mul m).comp continuous_subtype_val).mul continuous_const).subtype_mk _).measurable

instance : Countable (d.ΓM.subgroupOf (d.ν : M →* T).ker) :=
  Injective.countable (f := fun x : d.ΓM.subgroupOf (d.ν : M →* T).ker => (⟨((x : (d.ν : M →* T).ker) : M), x.2⟩ : d.ΓM))
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

theorem map_adK_muS (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]
    (hconj : ∀ m : M, μSν.map (NormalFib.adK (d.ν : M →* T) m) = μSν) (g : d.G) :
    (d.muS μSν).map (NormalFib.adK d.p g) = d.muS μSν := by
  have h1 : NormalFib.adK d.p g ∘ d.kerSEquiv.symm =
      d.kerSEquiv.symm ∘ NormalFib.adK (d.ν : M →* T) (g : M × (Adeles k)ˣ).1 :=
    funext (d.adK_p_kerSEquiv_symm g)
  have hm : Measurable (d.kerSEquiv.symm : (d.ν : M →* T).ker → d.p.ker) := d.kerSEquiv.symm.continuous.measurable
  rw [muS, Measure.map_map (NormalFib.measurable_adK _ _) hm, h1,
    ← Measure.map_map hm (d.measurable_adK_ν _), hconj]

theorem map_adK_muZ (g : d.G) : d.muZ.map (NormalFib.adK d.π g) = d.muZ := by
  have : NormalFib.adK d.π g = id := by
    funext z
    apply Subtype.ext
    obtain ⟨u, hu⟩ := d.mem_ker_π.1 z.2
    change g * (z : d.G) * g⁻¹ = z
    rw [← hu, ← d.zHom_central, mul_assoc, mul_inv_cancel, mul_one]
  rw [this, Measure.map_id]

/-- The shell $B = \{a\in A_+ : 0\le\log\|a\|<1\}$. -/
def shellB : Set d.Apos := {a | Real.log (ideleNorm k (a : (Adeles k)ˣ)) ∈ Ico (0 : ℝ) 1}

theorem measurableSet_shellB : MeasurableSet d.shellB :=
  measurableSet_Ico.preimage (Real.measurable_log.comp (continuous_ideleNorm.measurable.comp measurable_subtype_coe))

/-- **The base.** An exact fundamental domain of $p(\Gamma) = k^\times\cap A_+$ in $A_+$ is one of $k^\times$ in
$\mathbb A_k^\times$ (weak approximation of signs `hsign`, Eichler `heich`), so its shell has mass
$\operatorname{vol}(k^\times\backslash\mathbb A^1)$. -/
theorem muA_shell (heich : ∀ f : kˣ, diagUnits k f ∈ d.Apos → ∃ γ ∈ d.ΓM, d.ν γ = d.ι (diagUnits k f))
    (hsign : ∀ x : (Adeles k)ˣ, ∃ f : kˣ, diagUnits k f * x ∈ d.Apos)
    {DA : Set d.Apos} (hDA : IsExactFD (Γ := NormalFib.gammaQ d.p d.gam) DA) :
    d.muA (DA ∩ d.shellB) = muIdeleClass k univ := by
  -- membership in `p(Γ)`
  have hmemQ : ∀ (f : kˣ) (hf : diagUnits k f ∈ d.Apos),
      (⟨diagUnits k f, hf⟩ : d.Apos) ∈ NormalFib.gammaQ d.p d.gam := by
    intro f hf
    obtain ⟨γ, hγ, hνγ⟩ := heich f hf
    exact ⟨⟨(γ, diagUnits k f), hνγ⟩, ⟨hγ, ⟨f, rfl⟩⟩, rfl⟩
  have hFD : IsExactFD (Γ := diagUnitsSub k) (Subtype.val '' DA : Set (Adeles k)ˣ) := by
    refine ⟨d.measurableEmbedding_Apos.measurableSet_image.2 hDA.1, fun x => ?_⟩
    obtain ⟨f₀, hf₀⟩ := hsign x
    obtain ⟨δ, hδ, huniq⟩ := hDA.2 ⟨_, hf₀⟩
    obtain ⟨_, ⟨g, hg, rfl⟩⟩ := δ
    obtain ⟨f₁, hf₁⟩ := hg.2
    refine ⟨⟨diagUnits k (f₁ * f₀), ⟨_, rfl⟩⟩, ⟨_, hδ, ?_⟩, fun η hη => ?_⟩
    · change ((d.p g : d.Apos) : (Adeles k)ˣ) * (diagUnits k f₀ * x) = diagUnits k (f₁ * f₀) * x
      rw [coe_p, ← hf₁, map_mul, mul_assoc]
    · obtain ⟨y, hy, hyx⟩ := hη
      obtain ⟨η', f₂, rfl⟩ := η
      have hyA : (y : (Adeles k)ˣ) = diagUnits k f₂ * x := hyx
      -- `f₂ f₀⁻¹ ∈ A_+`
      have hA : diagUnits k (f₂ * f₀⁻¹) ∈ d.Apos := by
        have : diagUnits k (f₂ * f₀⁻¹) = (y : (Adeles k)ˣ) * (diagUnits k f₀ * x)⁻¹ := by
          rw [hyA, map_mul, map_inv]; group
        rw [this]; exact d.Apos.mul_mem y.2 (d.Apos.inv_mem hf₀)
      have h1 := huniq ⟨_, hmemQ _ hA⟩ (by
        change (⟨diagUnits k (f₂ * f₀⁻¹), hA⟩ : d.Apos) * ⟨_, hf₀⟩ ∈ DA
        convert hy using 1
        apply Subtype.ext
        change diagUnits k (f₂ * f₀⁻¹) * (diagUnits k f₀ * x) = y
        rw [hyA, map_mul, map_inv]; group)
      have h2 := congrArg (fun δ : NormalFib.gammaQ d.p d.gam => ((δ : d.Apos) : (Adeles k)ˣ)) h1
      simp only at h2
      apply Subtype.ext
      change diagUnits k f₂ = diagUnits k (f₁ * f₀)
      have h3 : diagUnits k f₂ = diagUnits k (f₂ * f₀⁻¹) * diagUnits k f₀ := by rw [map_mul, map_inv]; group
      rw [h3, h2, coe_p, ← hf₁, map_mul]
  rw [muA_apply]
  have himg : Subtype.val '' (DA ∩ d.shellB) =
      (Subtype.val '' DA) ∩ (fun x => Real.log (ideleNorm k x)) ⁻¹' Ico 0 1 := by
    ext x
    constructor
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hb⟩
    · rintro ⟨⟨a, ha, rfl⟩, hb⟩; exact ⟨a, ⟨ha, hb⟩, rfl⟩
  rw [himg, tamIdeles_exactFD_logShell hFD, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **The centre.** The $Z$-fibres of $p^{-1}(B)$ have mass
$\tfrac12\operatorname{vol}(k^\times\backslash\mathbb A^1)$, since $\log\|p(z(u)g)\| = 2\log\|u\| + \log\|p(g)\|$. -/
theorem muZ_shell (hsΓ : ∀ u, d.s u ∈ d.ΓM ↔ u ∈ diagUnitsSub k) {DZ : Set d.π.ker}
    (hDZ : IsExactFD (Γ := NormalFib.gammaK d.π d.gam) DZ) (g : d.G) :
    d.muZ (DZ ∩ {z : d.π.ker | (z : d.G) * g ∈ d.p ⁻¹' d.shellB}) =
      muIdeleClass k univ * ENNReal.ofReal (1 / 2) := by
  have hFD : IsExactFD (Γ := diagUnitsSub k) (d.kerZEquiv.symm '' DZ) :=
    isExactFD_image_mulEquiv' d.kerZEquiv.symm.toMulEquiv d.kerZEquiv.continuous.measurable _ _
      (fun z => by
        rw [← d.kerZEquiv_mem_iff hsΓ]
        change d.kerZEquiv (d.kerZEquiv.symm z) ∈ _ ↔ _
        rw [ContinuousMulEquiv.apply_symm_apply]) hDZ
  set L := Real.log (ideleNorm k ((d.p g : d.Apos) : (Adeles k)ˣ))
  have hset : d.kerZEquiv ⁻¹' (DZ ∩ {z : d.π.ker | (z : d.G) * g ∈ d.p ⁻¹' d.shellB}) =
      (d.kerZEquiv.symm '' DZ) ∩ (fun x => Real.log (ideleNorm k x)) ⁻¹' Ico (-L / 2) ((1 - L) / 2) := by
    ext u
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, coe_kerZEquiv, shellB, mem_Ico]
    rw [d.log_norm_p_zHom_mul]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨⟨_, hu, d.kerZEquiv.symm_apply_apply u⟩, by linarith, by linarith⟩
    · rintro ⟨⟨z, hz, rfl⟩, h0, h1⟩
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact ⟨hz, by linarith, by linarith⟩
  have he : (d.kerZEquiv : (Adeles k)ˣ → d.π.ker) = d.kerZEquiv.toHomeomorph.toMeasurableEquiv := rfl
  rw [muZ, he, MeasurableEquiv.map_apply, ← he, hset, tamIdeles_exactFD_logShell hFD]
  congr 2
  ring

variable (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]

/-- **$\tau(G^\natural/\mathbb G_m) = 2\,\tau(\ker\nu)$** (Weil's centre argument): under the hypotheses
* `hsΓ`: $s(u)\in\Gamma_M\iff u\in k^\times$ (scalars among global points are global scalars);
* `heich`: every $f\in k^\times\cap A_+$ is $\nu$ of a global point (Eichler's norm theorem);
* `hsign`: every $k^\times$-orbit in $\mathbb A_k^\times$ meets $A_+$ (weak approximation of signs);
* `hconj`: $\mu_S$ is invariant under conjugation by $M$;
* `hτ`: $\operatorname{covol}(\Gamma_M\cap\ker\nu\backslash\ker\nu,\ \mu_S) = \tau$;

Weil's quotient measure $\mu_P = \mu_G/\mu_Z$ has $\operatorname{covol}(\pi(\Gamma)\backslash P,\ \mu_P) = 2\tau$. -/
@[kb "weil1982" "§3.2, proof of Thm 3.2.1, p. 43 (centre argument); §3.7 [unverified page]"]
theorem covolume_muP (hsΓ : ∀ u, d.s u ∈ d.ΓM ↔ u ∈ diagUnitsSub k)
    (heich : ∀ f : kˣ, diagUnits k f ∈ d.Apos → ∃ γ ∈ d.ΓM, d.ν γ = d.ι (diagUnits k f))
    (hsign : ∀ x : (Adeles k)ˣ, ∃ f : kˣ, diagUnits k f * x ∈ d.Apos)
    (hconj : ∀ m : M, μSν.map (NormalFib.adK (d.ν : M →* T) m) = μSν) {τ : ℝ≥0∞}
    (hτ : covolume (d.ΓM.subgroupOf (d.ν : M →* T).ker) (d.ν : M →* T).ker μSν = τ) :
    covolume d.gamP d.P (d.muP μSν) = 2 * τ := by
  have := d.discreteTopology_gamP hsΓ
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem d.gam
  obtain ⟨DS, hDSm, hDS⟩ := exists_measurableSet_forall_existsUnique_smul_mem (NormalFib.gammaK d.p d.gam)
  obtain ⟨DA, hDAm, hDA⟩ := exists_measurableSet_forall_existsUnique_smul_mem (NormalFib.gammaQ d.p d.gam)
  obtain ⟨DZ, hDZm, hDZ⟩ := exists_measurableSet_forall_existsUnique_smul_mem (NormalFib.gammaK d.π d.gam)
  obtain ⟨DP, hDPm, hDP⟩ := exists_measurableSet_forall_existsUnique_smul_mem d.gamP
  -- `μ_S(D_S) = τ`
  have hSν : d.muS μSν DS = τ := by
    have hFD : IsExactFD (Γ := d.ΓM.subgroupOf (d.ν : M →* T).ker) (d.kerSEquiv '' DS) :=
      isExactFD_image_mulEquiv' d.kerSEquiv.toMulEquiv d.kerSEquiv.symm.continuous.measurable _ _
        d.kerSEquiv_mem_iff ⟨hDSm, hDS⟩
    have : SMulInvariantMeasure (d.ΓM.subgroupOf (d.ν : M →* T).ker) (d.ν : M →* T).ker μSν :=
      ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
    have hm : Measurable (d.kerSEquiv.symm : (d.ν : M →* T).ker → d.p.ker) :=
      d.kerSEquiv.symm.continuous.measurable
    rw [← hτ, (hFD.isFundamentalDomain _).covolume_eq_volume, muS, Measure.map_apply hm hDSm]
    congr 1
    exact (d.kerSEquiv.toEquiv.image_eq_preimage_symm DS).symm
  -- the two fibrations
  have hB : ∀ δ ∈ NormalFib.gammaQ d.p d.gam, ∀ y, δ * y ∈ d.shellB ↔ y ∈ d.shellB := by
    rintro _ ⟨g, hg, rfl⟩ y
    simp only [shellB, mem_ofPred_eq, Subgroup.coe_mul, ideleNorm_mul,
      Real.log_mul (ideleNorm_pos _).ne' (ideleNorm_pos _).ne', d.log_norm_p_gam hg, zero_add]
  have h2 := NormalFib.two_ways d.gam d.p d.p_surjective d.measurable_p d.π d.π_surjective d.measurable_π
    d.muA (d.muS μSν) (d.muP μSν) d.muZ (d.fibMeas_muP μSν).symm (d.map_adK_muS μSν hconj) d.map_adK_muZ
    ⟨hDm, hD⟩ ⟨hDSm, hDS⟩ ⟨hDAm, hDA⟩ ⟨hDZm, hDZ⟩ ⟨hDPm, hDP⟩ d.measurableSet_shellB hB _
    (d.muZ_shell hsΓ ⟨hDZm, hDZ⟩)
  rw [hSν, d.muA_shell heich hsign ⟨hDAm, hDA⟩] at h2
  -- solve `τ ρ = (ρ/2) μ_P(D_P)`
  have hρ0 := muIdeleClass_univ_ne_zero k
  have hρt := (muIdeleClass_univ_lt_top k).ne
  have hμP : d.muP μSν DP = 2 * τ := by
    have h2' : muIdeleClass k univ * (ENNReal.ofReal (1 / 2) * d.muP μSν DP) =
        muIdeleClass k univ * τ := by rw [← mul_assoc, ← h2, mul_comm]
    have h3 := (ENNReal.mul_right_inj hρ0 hρt).1 h2'
    have hhalf : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [hhalf] at h3
    calc d.muP μSν DP = 2 * (2⁻¹ * d.muP μSν DP) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ = 2 * τ := by rw [h3]
  have : SMulInvariantMeasure d.gamP d.P (d.muP μSν) := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  rw [((IsExactFD.isFundamentalDomain ⟨hDPm, hDP⟩) _).covolume_eq_volume, hμP]

end GnatData

end

end QuadFormsKB.Tamagawa.Measure.Weil
