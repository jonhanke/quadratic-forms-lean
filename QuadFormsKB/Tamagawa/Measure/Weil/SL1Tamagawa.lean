import QuadFormsKB.Tamagawa.Measure.Weil.NormalFibration
import QuadFormsKB.Tamagawa.Measure.Weil.NrdSurjective

/-!
# The Tamagawa measure of $\mathrm{SL}_1(D)$ and the fibration $c_A' = \tau(\mathrm{SL}_1)\cdot\operatorname{vol}(F^\times\backslash\mathbb A^1)$

$\mathbb H = \mathbb H[F,a,b]$ over any number field $F$ ($a, b\in F^\times$ integral at every finite place),
any signature. Notation:
* $G^1 = \mathbb H_{\mathbb A}^1$ (`quatOne`) with the canonical Haar measure $\mu^1$ (`muQuatOneTam`), the norm-one
  part of $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$, $\omega = \|\operatorname{nrd}x\|^{-2}dx$;
* $\mathbb A^1_+ = \{u\in\mathbb A^1 : u_w > 0$ at the real places $w$ where $\mathbb H$ ramifies$\}$ (`posOne`), an
  open subgroup of $\mathbb A^1$, with the restriction $\mu_+$ of the $\mu^1_{\mathbb A}$ (`muIdeleOne`);
* $N = \operatorname{nrd} : G^1\to\mathbb A^1_+$ (`nrdOne`), **surjective** (`nrdOne_surjective`, from
  `exists_nrdUnit_eq`), with kernel $\mathrm{SL}_1(\mathbb H)(\mathbb A)$ (`SL1A`).

**The Tamagawa measure** $\mu_{\mathrm{SL}_1}$ (`muSL1`) is the Haar measure on $\mathrm{SL}_1(\mathbb A)$ for which
$\mu^1$ is the fibred measure of $\mu_+$ and $\mu_{\mathrm{SL}_1}$ along $N$ (Weil 1982, §2.4, Thm 2.4.4: the gauge
form $\omega_{\mathbb H^\times} = \omega_{\mathrm{SL}_1}\wedge\operatorname{nrd}^*(dx/x)$, the convergence factors
$\lambda_v$ cancelling between $\mathbb H^\times$ and $\mathbb G_m$; the $\mathbb R_{>0}$ factors $dt/t$ of
$\mathbb H_{\mathbb A}^\times = G^1\times\mathbb R_{>0}$ and $\mathbb A^\times = \mathbb A^1\times\mathbb R_{>0}$ match because
$\|\operatorname{nrd}x\|_{\mathbb A}$ is the splitting variable of both). **`fibMeas_muSL1`**:
$\mu^1 = \int_{\mathbb A^1_+}(g_q\cdot)_*\mu_{\mathrm{SL}_1}\,d\mu_+(q)$; **`muSL1_unique`**: it is the only Haar measure
with this property. The normalization is uniform in $F$ and in the signature of $\mathbb H$.

**The covolume identity** (`quatVolConst_eq_covolume_mul`, for $\mathbb H$ a division algebra):
$$c_A' = \operatorname{covol}(\mathrm{SL}_1(F)\backslash\mathrm{SL}_1(\mathbb A),\mu_{\mathrm{SL}_1})\cdot
\mu_+(D_+),$$
$D_+$ an exact fundamental domain of $\operatorname{nrd}(\mathbb H^\times)$ in $\mathbb A^1_+$, from the section-free
fibration theorem `NormalFib.fibMeas_exactFD`; the conjugation invariance of $\mu_{\mathrm{SL}_1}$ it needs comes from
the unimodularity of $G^1$ (a lattice with finite covolume, Fujisaki).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace MeasureTheory Measure Filter Topology Set
open scoped ENNReal NNReal Quaternion Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] {a b : F}

/-! ### The reduced norm as a continuous homomorphism -/

theorem nrdUnit_mul (x y : (QuatAdele a b)ˣ) : nrdUnit (x * y) = nrdUnit x * nrdUnit y := by
  refine Units.ext ?_
  simp only [nrdUnit_val, Units.val_mul]
  have hx := QuaternionAlgebra.mul_star_eq_coe (x : QuatAdele a b)
  have hy := QuaternionAlgebra.mul_star_eq_coe (y : QuatAdele a b)
  rw [star_mul, show (x : QuatAdele a b) * y * (star (y : QuatAdele a b) * star (x : QuatAdele a b)) =
    (x : QuatAdele a b) * (y * star (y : QuatAdele a b)) * star (x : QuatAdele a b) by noncomm_ring, hy,
    ← QuaternionAlgebra.coe_commutes, mul_assoc, hx, ← QuaternionAlgebra.coe_mul, QuaternionAlgebra.re_coe]
  simp only [QuaternionAlgebra.re_coe, mul_comm]

theorem nrdUnit_one : nrdUnit (1 : (QuatAdele a b)ˣ) = 1 := Units.ext (by simp)

variable (a b) in
/-- $\operatorname{nrd} : (\mathbb H\otimes\mathbb A)^\times\to\mathbb A^\times$ as a homomorphism. -/
def nrdHom : (QuatAdele a b)ˣ →* (Adeles F)ˣ where
  toFun := nrdUnit
  map_one' := nrdUnit_one
  map_mul' := nrdUnit_mul

theorem continuous_star_quatAdele : Continuous (star : QuatAdele a b → QuatAdele a b) := by
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩
  · simpa using continuous_re a b
  · exact (continuous_imI a b).neg.congr fun x => by simp
  · exact (continuous_imJ a b).neg.congr fun x => by simp
  · exact (continuous_imK a b).neg.congr fun x => by simp

theorem continuous_nrdHom : Continuous (nrdHom a b) := by
  have hval : Continuous fun x : (QuatAdele a b)ˣ => ((nrdUnit x : (Adeles F)ˣ) : Adeles F) := by
    simp only [nrdUnit_val]
    exact (continuous_re a b).comp (Units.continuous_val.mul (continuous_star_quatAdele.comp Units.continuous_val))
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : (fun x : (QuatAdele a b)ˣ => (((nrdHom a b x)⁻¹ : (Adeles F)ˣ) : Adeles F)) =
      (fun x => ((nrdUnit x : (Adeles F)ˣ) : Adeles F)) ∘ (fun x => x⁻¹) := by
    funext x; exact congrArg Units.val (map_inv (nrdHom a b) x).symm
  rw [this]; exact hval.comp continuous_inv

/-! ### $\mathbb A^1_+$ -/

theorem idele_mul_fst_fst (u v : (Adeles F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((u * v : (Adeles F)ˣ) : Adeles F).1.1 w = (u : Adeles F).1.1 w * (v : Adeles F).1.1 w := rfl

theorem idele_inv_fst_fst (u : (Adeles F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((u⁻¹ : (Adeles F)ˣ) : Adeles F).1.1 w = ((u : Adeles F).1.1 w)⁻¹ := by
  have h : (u : Adeles F).1.1 w * ((u⁻¹ : (Adeles F)ˣ) : Adeles F).1.1 w = 1 :=
    congrArg (fun z : Adeles F => z.1.1 w) u.mul_inv
  exact eq_inv_of_mul_eq_one_right h

variable (a b) in
/-- **$\mathbb A^1_+$**: ideles of norm $1$, positive at the real places where $\mathbb H$ ramifies. -/
def posOne : Subgroup (ideleOne F) where
  carrier := {u | PosAtRamified a b (u : (Adeles F)ˣ)}
  one_mem' := fun w hw _ => by simp
  mul_mem' := fun {u v} hu hv w hw hram => by
    change 0 < (((u : (Adeles F)ˣ) * (v : (Adeles F)ˣ) : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
    rw [idele_mul_fst_fst]; exact mul_pos (hu w hw hram) (hv w hw hram)
  inv_mem' := fun {u} hu w hw hram => by
    change 0 < (((u : (Adeles F)ˣ)⁻¹ : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
    rw [idele_inv_fst_fst]; exact inv_pos.2 (hu w hw hram)

theorem mem_posOne {u : ideleOne F} : u ∈ posOne a b ↔ PosAtRamified a b (u : (Adeles F)ˣ) := Iff.rfl

theorem continuous_idele_fst_fst (w : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun u : (Adeles F)ˣ => (u : Adeles F).1.1 w :=
  (continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp Units.continuous_val))

theorem isOpen_posOne : IsOpen (posOne a b : Set (ideleOne F)) := by
  have : (posOne a b : Set (ideleOne F)) = ⋂ (w : InfinitePlace F) (hw : w.IsReal)
      (_ : QuadFormsKB.Quat.IsRamifiedReal a b w hw),
      (fun u : ideleOne F => ((u : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩) ⁻¹' Ioi 0 := by
    ext u; simp [mem_posOne, PosAtRamified]
  rw [this]
  refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun hw => isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_Ioi.preimage ((continuous_idele_fst_fst ⟨w, hw⟩).comp continuous_subtype_val)

theorem isClosed_posOne : IsClosed (posOne a b : Set (ideleOne F)) :=
  Subgroup.isClosed_of_isOpen _ isOpen_posOne

instance : SecondCountableTopology (posOne a b) := TopologicalSpace.Subtype.secondCountableTopology _

instance : LocallyCompactSpace (posOne a b) :=
  (isClosed_posOne (a := a) (b := b)).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### $N = \operatorname{nrd} : \mathbb H_{\mathbb A}^1\to\mathbb A^1_+$ -/

variable (a b) in
/-- $\operatorname{nrd} : \mathbb H_{\mathbb A}^1\to\mathbb A^1_+$. -/
def nrdOne : quatOne a b →* posOne a b where
  toFun x := ⟨⟨nrdUnit (x : (QuatAdele a b)ˣ), mem_ideleOne.2 ((mem_quatOne a b).1 x.2)⟩,
    nrdUnit_pos_of_ramified (x : (QuatAdele a b)ˣ)⟩
  map_one' := by ext1; ext1; exact nrdUnit_one
  map_mul' x y := by ext1; ext1; exact nrdUnit_mul _ _

theorem coe_nrdOne (x : quatOne a b) :
    (((nrdOne a b x : posOne a b) : ideleOne F) : (Adeles F)ˣ) = nrdUnit (x : (QuatAdele a b)ˣ) := rfl

theorem continuous_nrdOne : Continuous (nrdOne a b) :=
  ((continuous_nrdHom.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem measurable_nrdOne : Measurable (nrdOne a b) := continuous_nrdOne.measurable

theorem nrdOne_surjective (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Function.Surjective (nrdOne a b) := by
  rintro ⟨⟨u, hu1⟩, hu⟩
  obtain ⟨x, hx⟩ := exists_nrdUnit_eq ha0 hb0 u hu
  have hx1 : x ∈ quatOne a b := by rw [mem_quatOne, hx]; exact mem_ideleOne.1 hu1
  exact ⟨⟨x, hx1⟩, Subtype.ext (Subtype.ext hx)⟩

variable (a b) in
/-- **$\mathrm{SL}_1(\mathbb H)(\mathbb A) = \ker(\operatorname{nrd})$**, as a subgroup of $\mathbb H_{\mathbb A}^1$. -/
abbrev SL1A : Subgroup (quatOne a b) := (nrdOne a b).ker

theorem mem_SL1A {x : quatOne a b} : x ∈ SL1A a b ↔ nrdUnit (x : (QuatAdele a b)ˣ) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact congrArg (fun y : posOne a b => ((y : ideleOne F) : (Adeles F)ˣ)) h
  · intro h; exact Subtype.ext (Subtype.ext h)

theorem isClosed_SL1A : IsClosed (SL1A a b : Set (quatOne a b)) :=
  isClosed_eq continuous_nrdOne continuous_const

instance : LocallyCompactSpace (SL1A a b) :=
  (isClosed_SL1A (a := a) (b := b)).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (SL1A a b) := TopologicalSpace.Subtype.secondCountableTopology _

instance : StandardBorelSpace (quatOne a b) := by
  have := polishSpace_of_isTopologicalGroup (quatOne a b)
  infer_instance

variable (a b) in
/-- **$\mathrm{SL}_1(\mathbb H)(F) = \mathbb H^\times\cap\mathrm{SL}_1(\mathbb A)$**, as a subgroup of $\mathrm{SL}_1(\mathbb A)$. -/
abbrev SL1F : Subgroup (SL1A a b) := NormalFib.gammaK (nrdOne a b) (quatUnitsOne a b)

/-! ### The measure on $\mathbb A^1_+$ -/

/-- The comap of a left-invariant measure to an open subgroup is left invariant. -/
theorem isMulLeftInvariant_comap_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : (μ.comap (Subtype.val : H → G)).IsMulLeftInvariant := by
  have he : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  refine ⟨fun h => ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_const_mul h) hs, he.comap_apply, he.comap_apply]
  have : (Subtype.val '' ((fun x : H => h * x) ⁻¹' s)) = (fun x : G => (h : G) * x) ⁻¹' (Subtype.val '' s) := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨h * x, hx, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨h⁻¹ * z, by simpa using hz, ?_⟩
      simp [hzy]
  rw [this, measure_preimage_mul]

variable (a b) in
/-- **The measure $\mu_+$ on $\mathbb A^1_+$**: the restriction of the $\mu^1_{\mathbb A}$ (`muIdeleOne`). -/
def muPosOne : Measure (posOne a b) := (muIdeleOne F).comap Subtype.val

theorem measurableEmbedding_posOne : MeasurableEmbedding (Subtype.val : posOne a b → ideleOne F) :=
  MeasurableEmbedding.subtype_coe isOpen_posOne.measurableSet

theorem muPosOne_apply (s : Set (posOne a b)) : muPosOne a b s = muIdeleOne F (Subtype.val '' s) :=
  measurableEmbedding_posOne.comap_apply _ _

instance : (muPosOne a b).IsMulLeftInvariant :=
  isMulLeftInvariant_comap_subgroup (muIdeleOne F) (posOne a b) isOpen_posOne

instance : IsFiniteMeasureOnCompacts (muPosOne a b) := by
  refine ⟨fun K hK => ?_⟩
  rw [muPosOne_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

/-! ### Discreteness of $\mathrm{SL}_1(F)$ and of $\operatorname{nrd}(\mathbb H^\times)$ -/

instance : DiscreteTopology (SL1F a b) :=
  DiscreteTopology.of_continuous_injective
    (f := fun ε : SL1F a b => (⟨((ε : SL1A a b) : quatOne a b), ε.2⟩ : quatUnitsOne a b))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

theorem nrdUnit_quatUnitsSub {γ : (QuatAdele a b)ˣ} (hγ : γ ∈ quatUnitsSub a b) :
    nrdUnit γ ∈ diagUnitsSub F := by
  obtain ⟨ξ, rfl⟩ := hγ
  have hdet : IsUnit (LinearMap.det (LinearMap.mulLeft F (ξ : ℍ[F,a,b]))) :=
    (ξ.isUnit.map (Algebra.lmul F ℍ[F,a,b])).map LinearMap.det
  rw [QuaternionAlgebra.det_mulLeft] at hdet
  have hn : IsUnit (((ξ : ℍ[F,a,b]) * star (ξ : ℍ[F,a,b])).re) := (isUnit_pow_iff two_ne_zero).mp hdet
  refine ⟨hn.unit, Units.ext ?_⟩
  rw [nrdUnit_val, diagUnits_val, IsUnit.unit_spec]
  change _ = ((quatDiagRing a b ξ) * star (quatDiagRing a b ξ)).re
  rw [← quatDiagRing_star, ← map_mul]
  rfl

variable (a b) in
/-- $\operatorname{nrd}(\mathbb H^\times)\subseteq\mathbb A^1_+$. -/
abbrev nrdGlobal : Subgroup (posOne a b) := NormalFib.gammaQ (nrdOne a b) (quatUnitsOne a b)

theorem mem_diagUnitsSub_of_mem_nrdGlobal (δ : nrdGlobal a b) :
    (((δ : posOne a b) : ideleOne F) : (Adeles F)ˣ) ∈ diagUnitsSub F := by
  obtain ⟨_, ⟨γ, hγ, rfl⟩⟩ := δ
  exact nrdUnit_quatUnitsSub hγ

instance : DiscreteTopology (nrdGlobal a b) :=
  DiscreteTopology.of_continuous_injective
    (f := fun δ : nrdGlobal a b => (⟨_, mem_diagUnitsSub_of_mem_nrdGlobal δ⟩ : diagUnitsSub F))
    ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
    fun x y h => Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))

theorem exists_exactFD_SL1F : ∃ DK : Set (SL1A a b), IsExactFD (Γ := SL1F a b) DK :=
  exists_measurableSet_forall_existsUnique_smul_mem (SL1F a b)

theorem exists_exactFD_nrdGlobal : ∃ DQ : Set (posOne a b), IsExactFD (Γ := nrdGlobal a b) DQ :=
  exists_measurableSet_forall_existsUnique_smul_mem (nrdGlobal a b)

/-! ### Index cancellation: $F^\times\mathbb A^1_+ = \mathbb A^1$ and $F^\times\cap\mathbb A^1_+ = \operatorname{nrd}(\mathbb H^\times)$ -/

theorem nrdUnit_map_quatDiagRing (ξ : (ℍ[F,a,b])ˣ) :
    ((nrdUnit (Units.map (quatDiagRing a b).toMonoidHom ξ) : (Adeles F)ˣ) : Adeles F) =
      diag F (QuadFormsKB.Quat.nrd (ξ : ℍ[F,a,b])) := by
  rw [nrdUnit_val]
  change ((quatDiagRing a b ξ) * star (quatDiagRing a b ξ)).re = _
  rw [← quatDiagRing_star, ← map_mul, QuadFormsKB.Quat.mul_star_eq_nrd]
  rfl

/-- **Every idele class of norm one meets $\mathbb A^1_+$**: for $y\in\mathbb A^1$ there is $c\in F^\times$ with
$cy\in\mathbb A^1_+$ (weak approximation at the real places, `exists_signs`). -/
theorem exists_diag_mul_mem_posOne (y : ideleOne F) : ∃ f : diagUnitsOne F, (f : ideleOne F) * y ∈ posOne a b := by
  obtain ⟨c, hc0, hc⟩ := QuadFormsKB.Quat.exists_signs (F := F)
    (fun w hw => 0 < ((y : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩)
  set cu : Fˣ := Units.mk0 c hc0
  have hmem : diagUnits F cu ∈ ideleOne F := diagUnitsSub_le_ideleOne ⟨cu, rfl⟩
  refine ⟨⟨⟨diagUnits F cu, hmem⟩, ⟨cu, rfl⟩⟩, fun w hw _ => ?_⟩
  change 0 < ((diagUnits F cu * (y : (Adeles F)ˣ) : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
  rw [idele_mul_fst_fst, diagUnits_val]
  have hσ : (diag F (cu : F)).1.1 ⟨w, hw⟩ = embedding_of_isReal hw c := diag_fst_fst c ⟨w, hw⟩
  rw [hσ]
  have hy0 : ((y : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩ ≠ 0 := idele_fst_fst_ne_zero _ _
  have hc0' : embedding_of_isReal hw c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have : ¬ 0 < embedding_of_isReal hw c := fun h => absurd ((hc w hw).1 h) (not_lt.2 hneg.le)
    exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 this) hc0') hneg
  · exact mul_pos ((hc w hw).2 hpos) hpos

/-- **Hasse–Schilling–Maass norm theorem, adelic form**: an element of $F^\times$ lying in $\mathbb A^1_+$ is a reduced
norm of $\mathbb H^\times$ (`eichler_norm_theorem_general`). -/
theorem mem_nrdGlobal_of_diag (ha0 : a ≠ 0) (hb0 : b ≠ 0) {f : posOne a b}
    (hf : ((f : ideleOne F) : (Adeles F)ˣ) ∈ diagUnitsSub F) : f ∈ nrdGlobal a b := by
  obtain ⟨c, hc⟩ := hf
  have hpos : ∀ (w : InfinitePlace F) (hw : w.IsReal), QuadFormsKB.Quat.IsRamifiedReal a b w hw →
      0 < embedding_of_isReal hw (c : F) := by
    intro w hw hram
    have := f.2 w hw hram
    rw [← hc, diagUnits_val, diag_fst_fst] at this
    exact this
  obtain ⟨α, hαu, hα⟩ := (QuadFormsKB.Quat.eichler_norm_theorem_general ha0 hb0 (c : F)).2 ⟨c.ne_zero, hpos⟩
  set γ : (QuatAdele a b)ˣ := Units.map (quatDiagRing a b).toMonoidHom hαu.unit
  have hγ : γ ∈ quatUnitsSub a b := ⟨hαu.unit, rfl⟩
  have hγ1 : γ ∈ quatOne a b := quatUnitsSub_le_quatOne a b hγ
  refine ⟨⟨γ, hγ1⟩, (by exact hγ : (⟨γ, hγ1⟩ : quatOne a b) ∈ quatUnitsOne a b), ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rw [coe_nrdOne, nrdUnit_map_quatDiagRing, IsUnit.unit_spec, hα, ← hc, diagUnits_val]

/-- **The index cancellation**: an exact fundamental domain of $\operatorname{nrd}(\mathbb H^\times)$ in $\mathbb A^1_+$ is
an exact fundamental domain of $F^\times$ in $\mathbb A^1$ ($[F^\times : F^\times_+] = [\mathbb A^1 : \mathbb A^1_+]$). -/
theorem isExactFD_image_posOne (ha0 : a ≠ 0) (hb0 : b ≠ 0) {DQ : Set (posOne a b)}
    (hDQ : IsExactFD (Γ := nrdGlobal a b) DQ) :
    IsExactFD (Γ := diagUnitsOne F) (Subtype.val '' DQ : Set (ideleOne F)) := by
  refine ⟨measurableEmbedding_posOne.measurableSet_image.2 hDQ.1, fun y => ?_⟩
  obtain ⟨f, hf⟩ := exists_diag_mul_mem_posOne (a := a) (b := b) y
  obtain ⟨δ, hδ, huniq⟩ := hDQ.2 ⟨(f : ideleOne F) * y, hf⟩
  have hδdiag := mem_diagUnitsSub_of_mem_nrdGlobal δ
  set δ' : diagUnitsOne F := ⟨((δ : posOne a b) : ideleOne F), hδdiag⟩
  refine ⟨δ' * f, ?_, fun f' hf' => ?_⟩
  · refine ⟨_, hδ, ?_⟩
    change ((δ : posOne a b) : ideleOne F) * ((f : ideleOne F) * y) = ((δ' * f : diagUnitsOne F) : ideleOne F) * y
    simp only [δ', Subgroup.coe_mul, mul_assoc]
  · obtain ⟨z, hz, hzy⟩ := hf'
    -- z = f' y ∈ posOne, f y ∈ posOne ⇒ f' f⁻¹ ∈ posOne ∩ F^× = nrdGlobal
    have hq : ((f' : ideleOne F) * (f : ideleOne F)⁻¹) ∈ posOne a b := by
      have : (f' : ideleOne F) * (f : ideleOne F)⁻¹ = (z : ideleOne F) * ((f : ideleOne F) * y)⁻¹ := by
        rw [hzy]; change _ = (f' : ideleOne F) * y * ((f : ideleOne F) * y)⁻¹; group
      rw [this]; exact (posOne a b).mul_mem z.2 ((posOne a b).inv_mem hf)
    set q : posOne a b := ⟨_, hq⟩
    have hqdiag : ((q : ideleOne F) : (Adeles F)ˣ) ∈ diagUnitsSub F := by
      change (((f' : ideleOne F) * (f : ideleOne F)⁻¹ : ideleOne F) : (Adeles F)ˣ) ∈ diagUnitsSub F
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (diagUnitsSub F).mul_mem f'.2 ((diagUnitsSub F).inv_mem f.2)
    have hqN := mem_nrdGlobal_of_diag ha0 hb0 hqdiag
    set ε : nrdGlobal a b := ⟨q, hqN⟩
    have hεmem : ε • (⟨(f : ideleOne F) * y, hf⟩ : posOne a b) ∈ DQ := by
      have : ε • (⟨(f : ideleOne F) * y, hf⟩ : posOne a b) = z := by
        apply Subtype.ext
        change (f' : ideleOne F) * (f : ideleOne F)⁻¹ * ((f : ideleOne F) * y) = z
        rw [hzy]; change _ = (f' : ideleOne F) * y; group
      rw [this]; exact hz
    have hεδ : ε = δ := huniq ε hεmem
    have hq' : (f' : ideleOne F) * (f : ideleOne F)⁻¹ = ((δ : posOne a b) : ideleOne F) := by
      have := congrArg (fun x : nrdGlobal a b => ((x : posOne a b) : ideleOne F)) hεδ
      exact this
    apply Subtype.ext
    change (f' : ideleOne F) = ((δ : posOne a b) : ideleOne F) * (f : ideleOne F)
    rw [← hq']; group

/-! ### The Tamagawa measure of $\mathrm{SL}_1$ -/

section Tamagawa

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

variable (a b) in
/-- A reference Haar measure on $\mathrm{SL}_1(\mathbb A)$ (only used to construct `muSL1`). -/
def muSL1Ref : Measure (SL1A a b) := Measure.haar

instance : (muSL1Ref a b).IsHaarMeasure := by unfold muSL1Ref; infer_instance

variable (a b) in
/-- A fixed compact set with nonempty interior in $\mathbb H_{\mathbb A}^1$ (only used to normalize `muSL1`). -/
def quatOneRefSet : Set (quatOne a b) := (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quatOne a b)))

theorem isCompact_quatOneRefSet : IsCompact (quatOneRefSet a b) :=
  (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quatOne a b))).isCompact

theorem interior_quatOneRefSet_nonempty : (interior (quatOneRefSet a b)).Nonempty :=
  (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quatOne a b))).interior_nonempty

include ha0 hb0 in
/-- The fibred measure of $\mu_+$ and the reference Haar measure. -/
def nuSL1Ref : Measure (quatOne a b) :=
  NormalFib.fibMeas (nrdOne a b) (nrdOne_surjective ha0 hb0) (muPosOne a b) (muSL1Ref a b)

include ha0 hb0 in
theorem isMulLeftInvariant_nuSL1Ref : (nuSL1Ref ha0 hb0).IsMulLeftInvariant :=
  NormalFib.isMulLeftInvariant_fibMeas _ _ measurable_nrdOne _ _

include ha0 hb0 in
theorem nuSL1Ref_compact_lt_top {C : Set (quatOne a b)} (hC : IsCompact C) : nuSL1Ref ha0 hb0 C < ∞ :=
  NormalFib.fibMeas_compact_lt_top _ _ continuous_nrdOne _ _ isClosed_SL1A hC

include ha0 hb0 in
instance isFiniteMeasureOnCompacts_nuSL1Ref : IsFiniteMeasureOnCompacts (nuSL1Ref ha0 hb0) :=
  ⟨fun _ hC => nuSL1Ref_compact_lt_top ha0 hb0 hC⟩

include ha0 hb0 in
theorem nuSL1Ref_univ_ne_zero : nuSL1Ref ha0 hb0 univ ≠ 0 := by
  rw [nuSL1Ref, NormalFib.fibMeas_univ _ _ measurable_nrdOne]
  refine mul_ne_zero (isOpen_univ.measure_pos (muSL1Ref a b) univ_nonempty).ne' ?_
  rw [muPosOne_apply, image_univ, Subtype.range_coe]
  exact (isOpen_posOne.measure_pos (muIdeleOne F) ⟨1, (posOne a b).one_mem⟩).ne'

include ha hb ha0 hb0 in
theorem isHaarMeasure_muQuatOneTam : (muQuatOneTam ha hb ha0 hb0).IsHaarMeasure := by
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  unfold muQuatOneTam; infer_instance

include ha hb ha0 hb0 in
theorem muQuatOneTam_refSet_ne_zero : muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b) ≠ 0 := by
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  exact (measure_pos_of_nonempty_interior _ interior_quatOneRefSet_nonempty).ne'

include ha hb ha0 hb0 in
theorem muQuatOneTam_refSet_ne_top : muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b) ≠ ∞ := by
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  exact isCompact_quatOneRefSet.measure_lt_top.ne

include ha hb ha0 hb0 in
/-- The normalization constant $r$ with $\nu_{\mathrm{ref}} = r\,\mu^1$. -/
def sl1Const : ℝ≥0∞ := nuSL1Ref ha0 hb0 (quatOneRefSet a b) / muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b)

include ha hb ha0 hb0 in
theorem nuSL1Ref_eq_smul : nuSL1Ref ha0 hb0 = sl1Const ha hb ha0 hb0 • muQuatOneTam ha hb ha0 hb0 := by
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  have := isMulLeftInvariant_nuSL1Ref ha0 hb0
  exact measure_eq_div_smul _ _ (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0)
    (muQuatOneTam_refSet_ne_top ha hb ha0 hb0)

include ha hb ha0 hb0 in
theorem sl1Const_ne_zero : sl1Const ha hb ha0 hb0 ≠ 0 := by
  intro h
  apply nuSL1Ref_univ_ne_zero ha0 hb0
  rw [nuSL1Ref_eq_smul ha hb ha0 hb0, h, zero_smul]; rfl

include ha hb ha0 hb0 in
theorem sl1Const_ne_top : sl1Const ha hb ha0 hb0 ≠ ∞ :=
  ENNReal.div_ne_top (nuSL1Ref_compact_lt_top ha0 hb0 isCompact_quatOneRefSet).ne
    (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0)

include ha hb ha0 hb0 in
/-- **Weil's Tamagawa measure on $\mathrm{SL}_1(\mathbb H)(\mathbb A)$**: the Haar measure whose fibred measure with
$\mu_+$ along $\operatorname{nrd} : \mathbb H_{\mathbb A}^1\to\mathbb A^1_+$ is the canonical $\mu^1$ (`fibMeas_muSL1`,
`muSL1_unique`). Any number field, any signature. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 (Tamagawa measures in an exact sequence) [unverified page]"]
def muSL1 : Measure (SL1A a b) := (sl1Const ha hb ha0 hb0)⁻¹ • muSL1Ref a b

include ha hb ha0 hb0 in
theorem isHaarMeasure_muSL1 : (muSL1 ha hb ha0 hb0).IsHaarMeasure :=
  IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (sl1Const_ne_top ha hb ha0 hb0))
    (ENNReal.inv_ne_top.2 (sl1Const_ne_zero ha hb ha0 hb0))

include ha hb ha0 hb0 in
/-- **The fibration identity**: $\mu^1 = \int_{\mathbb A^1_+}(g_q\cdot)_*\mu_{\mathrm{SL}_1}\,d\mu_+(q)$, i.e.
$\mu^1 = \mu_+\times\mu_{\mathrm{SL}_1}$ along $\operatorname{nrd}$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]"]
theorem fibMeas_muSL1 :
    NormalFib.fibMeas (nrdOne a b) (nrdOne_surjective ha0 hb0) (muPosOne a b) (muSL1 ha hb ha0 hb0) =
      muQuatOneTam ha hb ha0 hb0 := by
  rw [muSL1, NormalFib.fibMeas_smul _ _ measurable_nrdOne _ _ _
    (ENNReal.inv_ne_top.2 (sl1Const_ne_zero ha hb ha0 hb0))]
  change (sl1Const ha hb ha0 hb0)⁻¹ • nuSL1Ref ha0 hb0 = _
  rw [nuSL1Ref_eq_smul ha hb ha0 hb0, smul_smul, ENNReal.inv_mul_cancel (sl1Const_ne_zero ha hb ha0 hb0)
    (sl1Const_ne_top ha hb ha0 hb0), one_smul]

include ha hb ha0 hb0 in
/-- **Uniqueness of the Tamagawa measure**: a Haar measure $\mu'$ on $\mathrm{SL}_1(\mathbb A)$ whose fibred measure is
$\mu^1$ is `muSL1`. -/
theorem muSL1_unique (μ' : Measure (SL1A a b)) [μ'.IsHaarMeasure]
    (h : NormalFib.fibMeas (nrdOne a b) (nrdOne_surjective ha0 hb0) (muPosOne a b) μ' =
      muQuatOneTam ha hb ha0 hb0) : μ' = muSL1 ha hb ha0 hb0 := by
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  set c := μ'.haarScalarFactor (muSL1 ha hb ha0 hb0)
  have hc : μ' = (c : ℝ≥0∞) • muSL1 ha hb ha0 hb0 := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 := fibMeas_muSL1 ha hb ha0 hb0
  rw [hc, NormalFib.fibMeas_smul _ _ measurable_nrdOne _ _ _ ENNReal.coe_ne_top, h2] at h
  have h0 := muQuatOneTam_refSet_ne_zero ha hb ha0 hb0
  have ht := muQuatOneTam_refSet_ne_top ha hb ha0 hb0
  have := congrArg (fun μ => μ (quatOneRefSet a b)) h
  simp only [Measure.smul_apply, smul_eq_mul] at this
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h' : (c : ℝ≥0∞) * muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b) =
      1 * muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b) := by rw [one_mul]; exact this
    exact (ENNReal.mul_left_inj h0 ht).1 h'
  rw [hc, hc1, one_smul]

/-! ### Conjugation invariance (unimodularity) and the covolume identity -/

include ha hb ha0 hb0 in
/-- **$\mathbb H_{\mathbb A}^1$ is unimodular** (it has the lattice $\mathbb H^\times$ of finite covolume). -/
theorem isMulRightInvariant_muQuatOneTam (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    (muQuatOneTam ha hb ha0 hb0).IsMulRightInvariant := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (quatUnitsOne a b)
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  have heq := quatVolConst_eq ha hb ha0 hb0 hDm hD
  exact NormalFib.isMulRightInvariant_of_exactFD _ (quatUnitsOne a b) ⟨hDm, hD⟩
    (heq ▸ quatVolConst_ne_zero ha hb ha0 hb0) (heq ▸ (quatVolConst_lt_top ha hb ha0 hb0 hdiv).ne)

include ha hb ha0 hb0 in
/-- **Conjugation preserves the Tamagawa measure of $\mathrm{SL}_1$.** -/
theorem map_adK_muSL1 (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) (g : quatOne a b) :
    (muSL1 ha hb ha0 hb0).map (NormalFib.adK (nrdOne a b) g) = muSL1 ha hb ha0 hb0 := by
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  have := isMulRightInvariant_muQuatOneTam ha hb ha0 hb0 hdiv
  have hH : ((muSL1 ha hb ha0 hb0).map (NormalFib.adKEquiv (nrdOne a b) g)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ _
  have hm := Measure.isMulLeftInvariant_eq_smul ((muSL1 ha hb ha0 hb0).map (NormalFib.adKEquiv (nrdOne a b) g))
    (muSL1 ha hb ha0 hb0)
  refine NormalFib.map_adK_eq_of_conj (nrdOne a b) (nrdOne_surjective ha0 hb0) measurable_nrdOne
    (muPosOne a b) _ g (fun _ => mul_comm _ _) _ hm ?_
    (s := quatOneRefSet a b) ?_ ?_
  · rw [fibMeas_muSL1]; exact NormalFib.map_conj_eq_self _ g
  · rw [fibMeas_muSL1]; exact muQuatOneTam_refSet_ne_zero ha hb ha0 hb0
  · rw [fibMeas_muSL1]; exact muQuatOneTam_refSet_ne_top ha hb ha0 hb0

include ha hb ha0 hb0 in
/-- **The covolume identity** $c_A' = \mu_{\mathrm{SL}_1}(D_K)\cdot\mu_+(D_+)$ for exact fundamental domains $D_K$ of
$\mathrm{SL}_1(F)$ in $\mathrm{SL}_1(\mathbb A)$ and $D_+$ of $\operatorname{nrd}(\mathbb H^\times)$ in $\mathbb A^1_+$
(division algebra). -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]"]
theorem quatVolConst_eq_muSL1_mul (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) {DK : Set (SL1A a b)}
    (hDK : IsExactFD (Γ := SL1F a b) DK) {DQ : Set (posOne a b)} (hDQ : IsExactFD (Γ := nrdGlobal a b) DQ) :
    quatVolConst ha hb ha0 hb0 = muSL1 ha hb ha0 hb0 DK * muPosOne a b DQ := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (quatUnitsOne a b)
  rw [quatVolConst_eq ha hb ha0 hb0 hDm hD, ← fibMeas_muSL1 ha hb ha0 hb0]
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  exact NormalFib.fibMeas_exactFD _ _ (quatUnitsOne a b) measurable_nrdOne _ _
    (map_adK_muSL1 ha hb ha0 hb0 hdiv) ⟨hDm, hD⟩ hDK hDQ

include ha hb ha0 hb0 in
/-- The covolume of $\mathrm{SL}_1(F)$ in $\mathrm{SL}_1(\mathbb A)$ is the measure of any exact fundamental domain. -/
theorem covolume_SL1_eq {DK : Set (SL1A a b)} (hDK : IsExactFD (Γ := SL1F a b) DK) :
    covolume (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) = muSL1 ha hb ha0 hb0 DK := by
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have : SMulInvariantMeasure (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  exact (hDK.isFundamentalDomain _).covolume_eq_volume _

include ha hb ha0 hb0 in
/-- **$c_A' = \tau(\mathrm{SL}_1(\mathbb H))\cdot\operatorname{vol}(F^\times\backslash\mathbb A^1)$** for a quaternion
division algebra over any number field (any signature): Weil's fibration of $\mathbb H^\times\backslash\mathbb H_{\mathbb A}^1$
over $F^\times_+\backslash\mathbb A^1_+$ with fibre $\mathrm{SL}_1(F)\backslash\mathrm{SL}_1(\mathbb A)$; the indices
$[F^\times : F^\times_+] = [\mathbb A^1 : \mathbb A^1_+] = 2^{r_{\mathrm{ram}}}$ cancel (`isExactFD_image_posOne`). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.1 (c_A = τ(SL₁)·ρ) [unverified pages]"]
theorem quatVolConst_eq_covolume_mul (hdiv : ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) :
    quatVolConst ha hb ha0 hb0 =
      covolume (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) * muIdeleClass F univ := by
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := a) (b := b)
  obtain ⟨DQ, hDQ⟩ := exists_exactFD_nrdGlobal (a := a) (b := b)
  rw [quatVolConst_eq_muSL1_mul ha hb ha0 hb0 hdiv hDK hDQ, covolume_SL1_eq ha hb ha0 hb0 hDK, muPosOne_apply,
    muIdeleClass_univ ((isExactFD_image_posOne ha0 hb0 hDQ).isFundamentalDomain _)]

end Tamagawa

/-! ### $\tau(\mathrm{SL}_1(D)) = 1$ -/

variable (F) in
/-- **Input (named): the volume of the idele class group of norm one is the residue $\rho_F$** for the measure
$\mu^1_{\mathbb A}$ on $F^\times\backslash\mathbb A^1$ (`muIdeleClass`). This is Weil's Thm 3.1.1 (iii) for $\mathbb G_m$
(p. 41). The library proves it (`IdeleClass.ideleClassLIntegral_comp_ideleNorm`) in a concrete model of the unramified
ideles; this is bridged to `muIdeleClass` and proves this input for every number field
(`IdeleClassVolume.lean`, `idelesClassVolumeResidue`; then `tamagawa_SL1_division_unconditional`). It is not
equivalent to $\tau(\mathrm{SL}_1) = 1$ (it does not mention quaternions). -/
structure IdeleClassVolumeResidue : Prop where
  /-- $\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$. -/
  muIdeleClass_univ_eq : muIdeleClass F univ = ENNReal.ofReal (dedekindZeta_residue F)

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ for every quaternion division algebra $D = \mathbb H[F,a,b]$ over every number field**
($a, b\in\mathcal O_F\setminus0$, any signature), for Weil's Tamagawa measure $\mu_{\mathrm{SL}_1}$ (`muSL1`):
$$\operatorname{covol}(\mathrm{SL}_1(D)(F)\backslash\mathrm{SL}_1(D)(\mathbb A),\ \mu_{\mathrm{SL}_1}) = 1,$$
conditional on the named input `IdeleClassVolumeResidue F` ($\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$).
*Proof.* $c_A' = \tau(\mathrm{SL}_1)\cdot\operatorname{vol}(F^\times\backslash\mathbb A^1)$ (`quatVolConst_eq_covolume_mul`) and
$c_A' = \rho_F$ (`quatVolConst_eq_residue`), and $0 < \rho_F < \infty$. -/
@[kb "weil1982" "§3.1, Thm 3.1.1 (iii), p. 41 and §3.7 (τ(SL₁(D)) = 1) [unverified page for §3.7]"]
theorem tamagawa_SL1_division {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) (hF : IdeleClassVolumeResidue F) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 1 := by
  have h1 := quatVolConst_eq_covolume_mul (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0)
    (by simpa using hb0) hdiv
  rw [quatVolConst_eq_residue ha0 hb0 hdiv, hF.muIdeleClass_univ_eq] at h1
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact dedekindZeta_residue_pos F
  have h1' : 1 * ENNReal.ofReal (dedekindZeta_residue F) = _ := (one_mul _).trans h1
  exact ((ENNReal.mul_left_inj hρ0 ENNReal.ofReal_ne_top).1 h1'.symm)

end

end QuadFormsKB.Tamagawa.Measure.Weil
