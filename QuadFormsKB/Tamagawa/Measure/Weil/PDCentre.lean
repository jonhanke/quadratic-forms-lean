import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume
import QuadFormsKB.Tamagawa.Measure.Weil.PDMeasure

/-!
# $\tau(PD^\times) = 2$ for quaternion division algebras over number fields

$F$ is any number field, $D = \mathbb H[F,a,b]$ ($a,b\in\mathcal O_F\setminus0$), $G = (D\otimes\mathbb A)^\times$,
$Z = \mathbb A^\times$ its centre (`quatScalar`), $PD^\times(\mathbb A) = G/Z$ (`PDAdele`).

* **`muPD`**: Weil's Tamagawa measure on $PD^\times(\mathbb A)$, the quotient of `tamQuat` by `tamIdeles`:
  the Haar measure with $\int_G f\,d\mu_G = \int_{G/Z}\int_Z f(gz)\,d\mu_Z\,d\mu_{PD}$ (**`fibMeas_muPD`**; the section-free fibration `NormalFib.fibMeas`, generalized to a non-commutative base). The global factors
  $\rho_F^{-1}$ and the convergence factors $\lambda_v$ of the two measures cancel in the quotient.
* **`muPDOne`**: the same quotient for the norm-one groups, $G^1 = \mathbb H_{\mathbb A}^1\to PD^\times(\mathbb A)$ with
  kernel $\mathbb A^1$ (`fibMeas_muPDOne`), and **`muPD_eq`**: $\mu_{PD} = 2\,\mu^1_{PD}$. The 2 is Weil's: on the
  centre $\|\operatorname{nrd}z\| = \|z\|^2$, so $dt/t$ in $t = \|z\|$ is twice $dt/t$ in $\|\operatorname{nrd}\|$.
* **`covolume_muPDOne`**: $c_A' = \operatorname{vol}(F^\times\backslash\mathbb A^1)\cdot\operatorname{vol}(PD^\times(F)\backslash
  PD^\times(\mathbb A),\mu^1_{PD})$ (Weil's fibration with fibre $F^\times\backslash\mathbb A^1$).
* **`tamagawa_PD_division`**: for a division algebra $D$,
  $$\tau(PD^\times) = \operatorname{vol}(PD^\times(F)\backslash PD^\times(\mathbb A),\ \mu_{PD}) = 2,$$
  from $c_A' = \rho_F$ and $\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$. Weil 1982, Thm 3.2.1,
  p. 43 (the centre argument, §3.2).
-/

open MeasureTheory Measure Set Function IsDedekindDomain NumberField
open scoped ENNReal NNReal Quaternion Pointwise

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### The centre $Z = \mathbb A^\times$ of $(D\otimes\mathbb A)^\times$ -/

section Scalars

variable {a b : F}

theorem val_quatScalar (c : (Adeles F)ˣ) :
    ((quatScalar a b c : (QuatAdele a b)ˣ) : QuatAdele a b) = ((c : Adeles F) : QuatAdele a b) := rfl

theorem re_quatScalar (c : (Adeles F)ˣ) : ((quatScalar a b c : (QuatAdele a b)ˣ) : QuatAdele a b).re = c := by
  rw [val_quatScalar, QuaternionAlgebra.re_coe]

/-- The scalars are the units with vanishing imaginary parts. -/
theorem mem_range_quatScalar_iff (g : (QuatAdele a b)ˣ) :
    g ∈ (quatScalar a b).range ↔ (g : QuatAdele a b).imI = 0 ∧ (g : QuatAdele a b).imJ = 0 ∧
      (g : QuatAdele a b).imK = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [val_quatScalar]
  · rintro ⟨h1, h2, h3⟩
    have hre : ∀ h : QuatAdele a b, (g * h : QuatAdele a b).re = (g : QuatAdele a b).re * h.re := by
      intro h; simp [QuaternionAlgebra.re_mul, h1, h2, h3]
    have hu1 : (g : QuatAdele a b).re * ((g⁻¹ : (QuatAdele a b)ˣ) : QuatAdele a b).re = 1 := by
      rw [← hre, Units.mul_inv, QuaternionAlgebra.re_one]
    let c : (Adeles F)ˣ := ⟨(g : QuatAdele a b).re, ((g⁻¹ : (QuatAdele a b)ˣ) : QuatAdele a b).re, hu1,
      by rw [mul_comm]; exact hu1⟩
    refine ⟨c, Units.ext ?_⟩
    rw [val_quatScalar]
    ext <;> simp [c, h1, h2, h3]

theorem isClosed_range_quatScalar : IsClosed ((quatScalar a b).range : Set (QuatAdele a b)ˣ) := by
  have : ((quatScalar a b).range : Set (QuatAdele a b)ˣ) =
      (fun g : (QuatAdele a b)ˣ => (g : QuatAdele a b).imI) ⁻¹' {0} ∩
      ((fun g : (QuatAdele a b)ˣ => (g : QuatAdele a b).imJ) ⁻¹' {0} ∩
      (fun g : (QuatAdele a b)ˣ => (g : QuatAdele a b).imK) ⁻¹' {0}) := by
    ext g
    simp only [SetLike.mem_coe, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact mem_range_quatScalar_iff g
  rw [this]
  exact (isClosed_singleton.preimage ((continuous_imI a b).comp Units.continuous_val)).inter
    ((isClosed_singleton.preimage ((continuous_imJ a b).comp Units.continuous_val)).inter
      (isClosed_singleton.preimage ((continuous_imK a b).comp Units.continuous_val)))

instance : IsClosed ((quatScalar a b).range : Set (QuatAdele a b)ˣ) := isClosed_range_quatScalar

theorem quatScalar_injective : Function.Injective (quatScalar a b) := by
  intro c d h
  have := congrArg (fun g : (QuatAdele a b)ˣ => (g : QuatAdele a b).re) h
  simp only [re_quatScalar] at this
  exact Units.ext this

/-- The scalar part $\operatorname{re} : Z\to\mathbb A^\times$ (inverse of `quatScalar` on its range). -/
def scalarPart (g : (quatScalar a b).range) : (Adeles F)ˣ := (Classical.choose g.2)

theorem quatScalar_scalarPart (g : (quatScalar a b).range) : quatScalar a b (scalarPart g) = g :=
  Classical.choose_spec g.2

theorem coe_scalarPart (g : (quatScalar a b).range) :
    ((scalarPart g : (Adeles F)ˣ) : Adeles F) = ((g : (QuatAdele a b)ˣ) : QuatAdele a b).re := by
  conv_rhs => rw [← quatScalar_scalarPart g]
  rw [re_quatScalar]

/-- **$\mathbb A^\times\cong Z$ as topological groups.** -/
def scalarEquiv : (Adeles F)ˣ ≃ₜ* (quatScalar a b).range where
  toFun c := ⟨quatScalar a b c, c, rfl⟩
  invFun := scalarPart
  left_inv c := quatScalar_injective (a := a) (b := b) (quatScalar_scalarPart _)
  right_inv g := Subtype.ext (quatScalar_scalarPart g)
  map_mul' c d := Subtype.ext (map_mul _ c d)
  continuous_toFun := (continuous_quatScalar a b).subtype_mk _
  continuous_invFun := by
    have hinv : ∀ g : (quatScalar a b).range, scalarPart g⁻¹ = (scalarPart g)⁻¹ := fun g =>
      quatScalar_injective (a := a) (b := b)
        (by rw [map_inv (quatScalar a b), quatScalar_scalarPart, quatScalar_scalarPart, Subgroup.coe_inv])
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun g : (quatScalar a b).range => ((scalarPart g : (Adeles F)ˣ) : Adeles F)
      simp_rw [coe_scalarPart]
      exact (continuous_re a b).comp (Units.continuous_val.comp continuous_subtype_val)
    · show Continuous fun g : (quatScalar a b).range => (((scalarPart g)⁻¹ : (Adeles F)ˣ) : Adeles F)
      simp_rw [← hinv, coe_scalarPart, Subgroup.coe_inv]
      exact (continuous_re a b).comp (Units.continuous_coe_inv.comp continuous_subtype_val)

@[simp] theorem coe_scalarEquiv (c : (Adeles F)ˣ) :
    ((scalarEquiv c : (quatScalar a b).range) : (QuatAdele a b)ˣ) = quatScalar a b c := rfl

theorem quatScalar_scalarEquiv_symm (g : (quatScalar a b).range) :
    quatScalar a b (scalarEquiv.symm g) = g :=
  congrArg Subtype.val (scalarEquiv.apply_symm_apply g)

end Scalars

/-! ### $PD^\times(\mathbb A) = G/Z$ and the two fibrations -/

section Quotient

variable (a b : F)

instance quatScalar_range_normal' : ((quatScalar a b).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, ?_⟩
  rw [← quatScalar_comm, mul_assoc, mul_inv_cancel, mul_one]

/-- $PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$ (`PDAdele` for $a, b\in\mathcal O_F$). -/
abbrev PDA : Type := (QuatAdele a b)ˣ ⧸ (quatScalar a b).range

instance : MeasurableSpace (PDA a b) := borel _
instance : BorelSpace (PDA a b) := ⟨rfl⟩

instance : StandardBorelSpace (QuatAdele a b)ˣ := by
  have := polishSpace_of_isTopologicalGroup ((QuatAdele a b)ˣ)
  infer_instance

/-- The projection $N : G\to PD^\times(\mathbb A)$. -/
abbrev pdMk : (QuatAdele a b)ˣ →* PDA a b := QuotientGroup.mk' _

theorem pdMk_surjective : Function.Surjective (pdMk a b) := QuotientGroup.mk'_surjective _

theorem continuous_pdMk : Continuous (pdMk a b) := continuous_quot_mk

theorem measurable_pdMk : Measurable (pdMk a b) := (continuous_pdMk a b).measurable

theorem mem_ker_pdMk {g : (QuatAdele a b)ˣ} : g ∈ (pdMk a b).ker ↔ g ∈ (quatScalar a b).range := by
  rw [QuotientGroup.ker_mk']

theorem isClosed_ker_pdMk : IsClosed ((pdMk a b).ker : Set (QuatAdele a b)ˣ) := by
  rw [QuotientGroup.ker_mk']; exact isClosed_range_quatScalar

/-- The restriction $N^1 : \mathbb H_{\mathbb A}^1\to PD^\times(\mathbb A)$. -/
def pdMkOne : quatOne a b →* PDA a b := (pdMk a b).comp (quatOne a b).subtype

theorem pdMkOne_apply (x : quatOne a b) : pdMkOne a b x = pdMk a b (x : (QuatAdele a b)ˣ) := rfl

theorem quatSectionHom_mem (t : Multiplicative ℝ) : quatSectionHom a b t ∈ (quatScalar a b).range := ⟨_, rfl⟩

theorem pdMkOne_quatSplit (g : (QuatAdele a b)ˣ) : pdMkOne a b (quatSplit a b g).1 = pdMk a b g := by
  rw [pdMkOne_apply]
  change pdMk a b (g * (quatSectionHom a b (quatLogNorm a b g))⁻¹) = _
  exact QuotientGroup.mk_mul_of_mem g ((quatScalar a b).range.inv_mem (quatSectionHom_mem a b _))

/-- **$G = Z\,G^1$**: $N^1$ is surjective. -/
theorem pdMkOne_surjective : Function.Surjective (pdMkOne a b) := fun q => by
  obtain ⟨g, rfl⟩ := pdMk_surjective a b q
  exact ⟨_, pdMkOne_quatSplit a b g⟩

theorem continuous_pdMkOne : Continuous (pdMkOne a b) := (continuous_pdMk a b).comp continuous_subtype_val

theorem measurable_pdMkOne : Measurable (pdMkOne a b) := (continuous_pdMkOne a b).measurable

theorem mem_ker_pdMkOne {x : quatOne a b} :
    x ∈ (pdMkOne a b).ker ↔ (x : (QuatAdele a b)ˣ) ∈ (quatScalar a b).range := by
  rw [MonoidHom.mem_ker, pdMkOne_apply, ← MonoidHom.mem_ker, mem_ker_pdMk]

theorem isClosed_ker_pdMkOne : IsClosed ((pdMkOne a b).ker : Set (quatOne a b)) := by
  have : ((pdMkOne a b).ker : Set (quatOne a b)) = Subtype.val ⁻¹' ((quatScalar a b).range : Set _) := by
    ext x; exact mem_ker_pdMkOne a b
  rw [this]; exact isClosed_range_quatScalar.preimage continuous_subtype_val

theorem quatScalar_mem_quatOne {c : (Adeles F)ˣ} : quatScalar a b c ∈ quatOne a b ↔ c ∈ ideleOne F := by
  rw [mem_quatOne, nrdUnit_quatScalar, sq, ideleNorm_mul, mem_ideleOne]
  have := ideleNorm_pos c
  constructor
  · intro h; nlinarith [sq_nonneg (ideleNorm F c - 1)]
  · intro h; rw [h, one_mul]

/-- **$\mathbb A^\times\cong\ker N = Z$.** -/
def kerEquiv : (Adeles F)ˣ ≃ₜ* (pdMk a b).ker where
  toFun c := ⟨quatScalar a b c, (mem_ker_pdMk a b).2 ⟨c, rfl⟩⟩
  invFun k := scalarEquiv.symm ⟨(k : (QuatAdele a b)ˣ), (mem_ker_pdMk a b).1 k.2⟩
  left_inv c := scalarEquiv.symm_apply_apply c
  right_inv k := Subtype.ext (by
    change ((scalarEquiv (scalarEquiv.symm ⟨(k : (QuatAdele a b)ˣ), (mem_ker_pdMk a b).1 k.2⟩) :
      (quatScalar a b).range) : (QuatAdele a b)ˣ) = k
    rw [scalarEquiv.apply_symm_apply])
  map_mul' c d := Subtype.ext (map_mul _ c d)
  continuous_toFun := (continuous_quatScalar a b).subtype_mk _
  continuous_invFun := scalarEquiv.symm.continuous.comp (continuous_subtype_val.subtype_mk _)

@[simp] theorem coe_kerEquiv (c : (Adeles F)ˣ) :
    ((kerEquiv a b c : (pdMk a b).ker) : (QuatAdele a b)ˣ) = quatScalar a b c := rfl

theorem scalarEquiv_symm_mem_ideleOne (k : (pdMkOne a b).ker) :
    scalarEquiv.symm (⟨((k : quatOne a b) : (QuatAdele a b)ˣ), (mem_ker_pdMkOne a b).1 k.2⟩ :
      (quatScalar a b).range) ∈ ideleOne F := by
  rw [← quatScalar_mem_quatOne a b, quatScalar_scalarEquiv_symm]; exact (k : quatOne a b).2

/-- **$\mathbb A^1\cong\ker N^1 = Z\cap G^1$.** -/
def kerOneEquiv : ideleOne F ≃ₜ* (pdMkOne a b).ker where
  toFun u := ⟨⟨quatScalar a b u, (quatScalar_mem_quatOne a b).2 u.2⟩, (mem_ker_pdMkOne a b).2 ⟨u, rfl⟩⟩
  invFun k := ⟨scalarEquiv.symm ⟨((k : quatOne a b) : (QuatAdele a b)ˣ), (mem_ker_pdMkOne a b).1 k.2⟩,
    scalarEquiv_symm_mem_ideleOne a b k⟩
  left_inv u := Subtype.ext (scalarEquiv.symm_apply_apply (u : (Adeles F)ˣ))
  right_inv _ := Subtype.ext (Subtype.ext (quatScalar_scalarEquiv_symm _))
  map_mul' u v := Subtype.ext (Subtype.ext (map_mul _ (u : (Adeles F)ˣ) v))
  continuous_toFun := (((continuous_quatScalar a b).comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := (scalarEquiv.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _

@[simp] theorem coe_kerOneEquiv (u : ideleOne F) :
    (((kerOneEquiv a b u : (pdMkOne a b).ker) : quatOne a b) : (QuatAdele a b)ˣ) = quatScalar a b u := rfl

end Quotient

/-! ### The measures -/

/-- **Linearity of the fibred measure in the base measure.** -/
theorem fibMeas_smul_base {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q] [StandardBorelSpace G]
    [MeasurableSpace.CountablySeparated Q] (N : G →* Q) (hN : Function.Surjective N) (hNm : Measurable N)
    (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] (c : ℝ≥0∞) :
    NormalFib.fibMeas N hN (c • μQ) μK = c • NormalFib.fibMeas N hN μQ μK := by
  ext s hs
  rw [NormalFib.fibMeas_apply N hN hNm _ μK hs, Measure.smul_apply, NormalFib.fibMeas_apply N hN hNm μQ μK hs,
    lintegral_smul_measure, smul_eq_mul]

section Measures

variable (a b : F)

instance : SecondCountableTopology (pdMk a b).ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace (pdMk a b).ker :=
  (isClosed_ker_pdMk a b).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : SecondCountableTopology (pdMkOne a b).ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace (pdMkOne a b).ker :=
  (isClosed_ker_pdMkOne a b).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The Tamagawa measure of the centre: `tamIdeles` on $Z = \ker N$. -/
def muZ : Measure (pdMk a b).ker := (tamIdeles F).map (kerEquiv a b)

instance : (muZ a b).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

/-- The measure $\mu^1$ of $\mathbb A^1$ on $Z\cap G^1 = \ker N^1$. -/
def muZOne : Measure (pdMkOne a b).ker := (muIdeleOne F).map (kerOneEquiv a b)

instance : (muZOne a b).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

/-- A reference Haar measure on $PD^\times(\mathbb A)$ (only used to construct `muPDOne`). -/
def muPDRef : Measure (PDA a b) := Measure.haar

instance : (muPDRef a b).IsHaarMeasure := by unfold muPDRef; infer_instance

/-- The fibred measure on $\mathbb H_{\mathbb A}^1$ of the reference measure and $\mu^1_Z$. -/
def nuPDRef : Measure (quatOne a b) :=
  NormalFib.fibMeas (pdMkOne a b) (pdMkOne_surjective a b) (muPDRef a b) (muZOne a b)

theorem isMulLeftInvariant_nuPDRef : (nuPDRef a b).IsMulLeftInvariant :=
  NormalFib.isMulLeftInvariant_fibMeas _ _ (measurable_pdMkOne a b) _ _

theorem nuPDRef_compact_lt_top {C : Set (quatOne a b)} (hC : IsCompact C) : nuPDRef a b C < ∞ :=
  NormalFib.fibMeas_compact_lt_top _ _ (continuous_pdMkOne a b) _ _ (isClosed_ker_pdMkOne a b) hC

instance isFiniteMeasureOnCompacts_nuPDRef : IsFiniteMeasureOnCompacts (nuPDRef a b) :=
  ⟨fun _ hC => nuPDRef_compact_lt_top a b hC⟩

theorem nuPDRef_univ_ne_zero : nuPDRef a b univ ≠ 0 := by
  rw [nuPDRef, NormalFib.fibMeas_univ _ _ (measurable_pdMkOne a b)]
  exact mul_ne_zero (isOpen_univ.measure_pos (muZOne a b) univ_nonempty).ne'
    (isOpen_univ.measure_pos (muPDRef a b) univ_nonempty).ne'

variable {a b} (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb ha0 hb0 in
/-- The normalization constant $r$ with $\nu_{\mathrm{ref}} = r\,\mu^1$. -/
def pdConst : ℝ≥0∞ := nuPDRef a b (quatOneRefSet a b) / muQuatOneTam ha hb ha0 hb0 (quatOneRefSet a b)

include ha hb ha0 hb0 in
theorem nuPDRef_eq_smul : nuPDRef a b = pdConst ha hb ha0 hb0 • muQuatOneTam ha hb ha0 hb0 := by
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  have := isMulLeftInvariant_nuPDRef a b
  exact measure_eq_div_smul _ _ (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0)
    (muQuatOneTam_refSet_ne_top ha hb ha0 hb0)

include ha hb ha0 hb0 in
theorem pdConst_ne_zero : pdConst ha hb ha0 hb0 ≠ 0 := by
  intro h
  apply nuPDRef_univ_ne_zero a b
  rw [nuPDRef_eq_smul ha hb ha0 hb0, h, zero_smul]; rfl

include ha hb ha0 hb0 in
theorem pdConst_ne_top : pdConst ha hb ha0 hb0 ≠ ∞ :=
  ENNReal.div_ne_top (nuPDRef_compact_lt_top a b isCompact_quatOneRefSet).ne
    (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0)

include ha hb ha0 hb0 in
/-- **The quotient measure $\mu^1_{PD} = \mu^1_{\mathbb H}/\mu^1_{\mathbb A}$ on $PD^\times(\mathbb A) = G^1/\mathbb A^1$**
(`fibMeas_muPDOne`). -/
def muPDOne : Measure (PDA a b) := (pdConst ha hb ha0 hb0)⁻¹ • muPDRef a b

include ha hb ha0 hb0 in
theorem isHaarMeasure_muPDOne : (muPDOne ha hb ha0 hb0).IsHaarMeasure :=
  IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (pdConst_ne_top ha hb ha0 hb0))
    (ENNReal.inv_ne_top.2 (pdConst_ne_zero ha hb ha0 hb0))

include ha hb ha0 hb0 in
/-- **The norm-one fibration identity**: $\mu^1_{\mathbb H} = \int_{PD^\times(\mathbb A)}(g_q\cdot)_*\mu^1_{\mathbb A}\,
d\mu^1_{PD}(q)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43"]
theorem fibMeas_muPDOne :
    NormalFib.fibMeas (pdMkOne a b) (pdMkOne_surjective a b) (muPDOne ha hb ha0 hb0) (muZOne a b) =
      muQuatOneTam ha hb ha0 hb0 := by
  rw [muPDOne, fibMeas_smul_base _ _ (measurable_pdMkOne a b)]
  change (pdConst ha hb ha0 hb0)⁻¹ • nuPDRef a b = _
  rw [nuPDRef_eq_smul ha hb ha0 hb0, smul_smul, ENNReal.inv_mul_cancel (pdConst_ne_zero ha hb ha0 hb0)
    (pdConst_ne_top ha hb ha0 hb0), one_smul]

end Measures

/-! ### $\Gamma\cap Z = F^\times$ -/

section Global

variable (a b : F)

theorem diag_zero : diag F (0 : F) = 0 := by rw [← diagRing_apply, map_zero]

/-- **A scalar idele is a global quaternion iff it is a principal idele**: $\mathbb A^\times\cap D^\times = F^\times$. -/
theorem quatScalar_mem_quatUnitsSub_iff (u : (Adeles F)ˣ) :
    quatScalar a b u ∈ quatUnitsSub a b ↔ u ∈ diagUnitsSub F := by
  constructor
  · rintro ⟨η, hη⟩
    have hv := congrArg (fun g : (QuatAdele a b)ˣ => (g : QuatAdele a b)) hη
    change quatDiagRing a b (η : ℍ[F,a,b]) = ((u : Adeles F) : QuatAdele a b) at hv
    rw [quatDiagRing_apply] at hv
    have hre := congrArg QuaternionAlgebra.re hv
    have hI := congrArg QuaternionAlgebra.imI hv
    have hJ := congrArg QuaternionAlgebra.imJ hv
    have hK := congrArg QuaternionAlgebra.imK hv
    simp only [quatDiag, QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
      QuaternionAlgebra.imK_coe] at hre hI hJ hK
    have hinj : Function.Injective (diag F) := fun x y h => (diagRing F).injective (by
      rw [diagRing_apply, diagRing_apply]; exact h)
    have hI0 : (η : ℍ[F,a,b]).imI = 0 := hinj (by rw [hI, diag_zero])
    have hJ0 : (η : ℍ[F,a,b]).imJ = 0 := hinj (by rw [hJ, diag_zero])
    have hK0 : (η : ℍ[F,a,b]).imK = 0 := hinj (by rw [hK, diag_zero])
    have hre0 : (η : ℍ[F,a,b]).re ≠ 0 := by
      intro h0
      apply η.ne_zero
      ext <;> simp [h0, hI0, hJ0, hK0]
    refine ⟨Units.mk0 _ hre0, Units.ext ?_⟩
    rw [diagUnits_val, Units.val_mk0]
    exact hre
  · rintro ⟨ξ, rfl⟩
    refine ⟨Units.map (algebraMap F ℍ[F,a,b]).toMonoidHom ξ, Units.ext ?_⟩
    change quatDiagRing a b (algebraMap F ℍ[F,a,b] (ξ : F)) = (((diagUnits F ξ : (Adeles F)ˣ) : Adeles F) :
      QuatAdele a b)
    rw [quatDiagRing_apply, diagUnits_val]
    ext <;> simp [quatDiag, diag_zero]

end Global

/-! ### The covolume identity for $\mu^1_{PD}$ -/

/-- Transport of an exact fundamental domain along a group isomorphism matching the subgroups. -/
theorem isExactFD_image_mulEquiv {H K : Type*} [Group H] [Group K] [MeasurableSpace H] [MeasurableSpace K]
    (e : H ≃* K) (hem : Measurable e.symm) (A : Subgroup H) (B : Subgroup K) (hAB : ∀ x, e x ∈ B ↔ x ∈ A)
    {E : Set H} (hE : IsExactFD (Γ := A) E) : IsExactFD (Γ := B) (e '' E) := by
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

section Covolume

variable {a b : F} (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

variable (a b) in
/-- $D^\times\cap\mathbb A^1 = F^\times$ inside $\ker N^1$. -/
abbrev gammaZ : Subgroup (pdMkOne a b).ker := NormalFib.gammaK (pdMkOne a b) (quatUnitsOne a b)

variable (a b) in
/-- $PD^\times(F) = N^1(D^\times)$. -/
abbrev gammaPD : Subgroup (PDA a b) := NormalFib.gammaQ (pdMkOne a b) (quatUnitsOne a b)

theorem kerOneEquiv_mem_gammaZ_iff (u : ideleOne F) : kerOneEquiv a b u ∈ gammaZ a b ↔ u ∈ diagUnitsOne F := by
  change ((kerOneEquiv a b u : (pdMkOne a b).ker) : quatOne a b) ∈ (quatUnitsSub a b).subgroupOf (quatOne a b) ↔
    u ∈ (diagUnitsSub F).subgroupOf (ideleOne F)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_kerOneEquiv, quatScalar_mem_quatUnitsSub_iff]

theorem map_adK_muZOne (g : quatOne a b) : (muZOne a b).map (NormalFib.adK (pdMkOne a b) g) = muZOne a b := by
  have : NormalFib.adK (pdMkOne a b) g = id := by
    funext k
    apply Subtype.ext; apply Subtype.ext
    obtain ⟨c, hc⟩ := (mem_ker_pdMkOne a b).1 k.2
    change (g : (QuatAdele a b)ˣ) * ((k : quatOne a b) : (QuatAdele a b)ˣ) * ((g⁻¹ : quatOne a b) :
      (QuatAdele a b)ˣ) = ((k : quatOne a b) : (QuatAdele a b)ˣ)
    rw [← hc, ← quatScalar_comm, mul_assoc, Subgroup.coe_inv, mul_inv_cancel, mul_one]
  rw [this, Measure.map_id]

theorem exists_exactFD_gammaZ :
    ∃ DK : Set (pdMkOne a b).ker, IsExactFD (Γ := gammaZ a b) DK ∧ muZOne a b DK = muIdeleClass F univ := by
  obtain ⟨E, hEm, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (diagUnitsOne F)
  refine ⟨kerOneEquiv a b '' E, isExactFD_image_mulEquiv (kerOneEquiv a b).toMulEquiv
    (kerOneEquiv a b).symm.continuous.measurable _ _ (kerOneEquiv_mem_gammaZ_iff) ⟨hEm, hE⟩, ?_⟩
  have he : ((kerOneEquiv a b) : ideleOne F → (pdMkOne a b).ker) =
      (kerOneEquiv a b).toHomeomorph.toMeasurableEquiv := rfl
  rw [muZOne, he, MeasurableEquiv.map_apply, ← he,
    (kerOneEquiv a b).injective.preimage_image, muIdeleClass_univ ((IsExactFD.isFundamentalDomain ⟨hEm, hE⟩) _)]

include ha hb ha0 hb0 in
/-- **Weil's fibration of $D^\times\backslash\mathbb H_{\mathbb A}^1$ over $PD^\times(F)\backslash PD^\times(\mathbb A)$ with fibre
$F^\times\backslash\mathbb A^1$**: $c_A' = \operatorname{vol}(F^\times\backslash\mathbb A^1)\cdot\mu^1_{PD}(D_Q)$ for every exact
fundamental domain $D_Q$ of $PD^\times(F)$ (any quaternion algebra, any number field). -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]; §3.2, p. 43"]
theorem quatVolConst_eq_mul_muPDOne {DQ : Set (PDA a b)} (hDQ : IsExactFD (Γ := gammaPD a b) DQ) :
    quatVolConst ha hb ha0 hb0 = muIdeleClass F univ * muPDOne ha hb ha0 hb0 DQ := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (quatUnitsOne a b)
  obtain ⟨DK, hDK, hDKm⟩ := exists_exactFD_gammaZ (a := a) (b := b)
  have := isHaarMeasure_muPDOne ha hb ha0 hb0
  rw [quatVolConst_eq ha hb ha0 hb0 hDm hD, ← fibMeas_muPDOne ha hb ha0 hb0, ← hDKm]
  exact NormalFib.fibMeas_exactFD _ _ (quatUnitsOne a b) (measurable_pdMkOne a b) _ _
    map_adK_muZOne ⟨hDm, hD⟩ hDK hDQ

end Covolume

/-! ### The factor $2$: $\mu_{PD} = 2\,\mu^1_{PD}$ -/

section FactorTwo

variable {a b : F}

theorem quatSplit_snd_mul_scalar (x : quatOne a b) (u : (Adeles F)ˣ) :
    (quatSplit a b ((x : (QuatAdele a b)ˣ) * quatScalar a b u)).2 = (ideleSplit F u).2 ^ 2 := by
  rw [quatSplit_apply_snd, ideleSplit_apply_snd, nrdUnit_mul, nrdUnit_quatScalar, ideleNorm_mul,
    (mem_quatOne a b).mp x.2, one_mul, sq, ideleNorm_mul, Real.log_mul (ideleNorm_pos u).ne' (ideleNorm_pos u).ne', sq]
  rfl

theorem quatSectionHom_sq (t : Multiplicative ℝ) : quatSectionHom a b (t ^ 2) = quatScalar a b (normSectionHom F t) := by
  change quatScalar a b (normSectionHom F (Multiplicative.ofAdd (Multiplicative.toAdd (t ^ 2) / 2))) = _
  congr 2
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

theorem quatSplit_fst_mul_scalar (x : quatOne a b) (u : (Adeles F)ˣ) :
    ((quatSplit a b ((x : (QuatAdele a b)ˣ) * quatScalar a b u)).1 : (QuatAdele a b)ˣ) =
      (x : (QuatAdele a b)ˣ) * quatScalar a b ((ideleSplit F u).1 : (Adeles F)ˣ) := by
  have h2 := quatSplit_snd_mul_scalar x u
  change (x : (QuatAdele a b)ˣ) * quatScalar a b u *
      (quatSectionHom a b (quatSplit a b ((x : (QuatAdele a b)ˣ) * quatScalar a b u)).2)⁻¹ = _
  rw [h2, quatSectionHom_sq, mul_assoc, ← map_inv, ← map_mul]
  rfl

/-- The set $\{u\in\mathbb A^\times : x\,u\in S\}$ for the shell $S = \{g : g\,s(\|g\|)^{-1}\in E,\ 1\le\|\operatorname{nrd}g\|\le e\}$:
in the splitting $u = (u^1,\|u\|)$ it is $E'_x\times\{1\le\|u\|\le e^{1/2}\}$. -/
theorem preimage_shell (x : quatOne a b) (E : Set (quatOne a b)) :
    {u : (Adeles F)ˣ | (x : (QuatAdele a b)ˣ) * quatScalar a b u ∈
      quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))} =
    ideleSplit F ⁻¹' (((fun w => x * ((kerOneEquiv a b w : (pdMkOne a b).ker) : quatOne a b)) ⁻¹' E) ×ˢ
      (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, mem_prod]
  have h1 : (quatSplit a b ((x : (QuatAdele a b)ˣ) * quatScalar a b u)).1 =
      x * ((kerOneEquiv a b (ideleSplit F u).1 : (pdMkOne a b).ker) : quatOne a b) :=
    Subtype.ext (quatSplit_fst_mul_scalar x u)
  rw [h1, quatSplit_snd_mul_scalar, toAdd_pow, nsmul_eq_mul]
  simp only [mem_Icc]
  constructor
  · rintro ⟨hE, h0, h1⟩; exact ⟨hE, by push_cast at h0; linarith, by push_cast at h1; linarith⟩
  · rintro ⟨hE, h0, h1⟩; exact ⟨hE, by push_cast; linarith, by push_cast; linarith⟩

theorem dtt_toAdd_Icc_half : dtt (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2)) = 2⁻¹ := by
  rw [dtt_apply]
  change volume (Icc (0 : ℝ) (1 / 2)) = 2⁻¹
  rw [Real.volume_Icc, sub_zero, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- **The fibre computation**: for $x\in\mathbb H_{\mathbb A}^1$ and the shell $S$ over $E\subseteq\mathbb H_{\mathbb A}^1$,
$\mu_Z\{z : xz\in S\} = \tfrac12\,\mu^1_Z\{k : xk\in E\}$ (since $\|\operatorname{nrd}z\| = \|z\|^2$). -/
theorem fibK_shell (x : quatOne a b) {E : Set (quatOne a b)} (hE : MeasurableSet E) :
    NormalFib.fibK (pdMk a b) (muZ a b) (x : (QuatAdele a b)ˣ)
      (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) =
      2⁻¹ * NormalFib.fibK (pdMkOne a b) (muZOne a b) x E := by
  have hS : MeasurableSet (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) :=
    (hE.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))).preimage (quatSplit a b).continuous.measurable
  set E' := (fun w => x * ((kerOneEquiv a b w : (pdMkOne a b).ker) : quatOne a b)) ⁻¹' E with hE'
  have hE'm : MeasurableSet E' := hE.preimage
    ((continuous_const.mul (continuous_subtype_val.comp (kerOneEquiv a b).continuous)).measurable)
  have hT : MeasurableSet (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2)) :=
    (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) (1 / 2)))
  rw [NormalFib.fibK_apply _ _ _ hS, NormalFib.fibK_apply _ _ _ hE]
  have hm1 : Measurable (kerEquiv a b) := (kerEquiv a b).continuous.measurable
  have hm2 : Measurable (kerOneEquiv a b) := (kerOneEquiv a b).continuous.measurable
  rw [muZ, muZOne, Measure.map_apply hm1 (hS.preimage (NormalFib.measurable_mul_val _ _)),
    Measure.map_apply hm2 (hE.preimage (NormalFib.measurable_mul_val _ _))]
  have hset : (kerEquiv a b) ⁻¹' ((fun k : (pdMk a b).ker => (x : (QuatAdele a b)ˣ) * (k : (QuatAdele a b)ˣ)) ⁻¹'
      (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)))) =
      ideleSplit F ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) := by
    rw [hE', ← preimage_shell]
    ext u
    simp only [mem_preimage, mem_ofPred_eq, coe_kerEquiv]
  rw [hset]
  have hmeas : (tamIdeles F) (ideleSplit F ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2)))) =
      ((tamIdeles F).map (ideleSplit F)) (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) :=
    (Measure.map_apply (ideleSplit F).continuous.measurable (hE'm.prod hT)).symm
  rw [hmeas, map_ideleSplit_tamIdeles, Measure.prod_prod, dtt_toAdd_Icc_half, mul_comm]
  rfl

end FactorTwo

/-! ### Weil's Tamagawa measure on $PD^\times(\mathbb A)$ -/

section MuPD

variable {a b : F} (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

theorem kern_shell (q : PDA a b) {E : Set (quatOne a b)} (hE : MeasurableSet E) :
    NormalFib.kern (pdMk a b) (pdMk_surjective a b) (muZ a b) q
      (quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) =
      2⁻¹ * NormalFib.kern (pdMkOne a b) (pdMkOne_surjective a b) (muZOne a b) q E := by
  obtain ⟨x, rfl⟩ := pdMkOne_surjective a b q
  rw [NormalFib.kern_apply_N, pdMkOne_apply, NormalFib.kern_apply_N, fibK_shell x hE]

include ha hb ha0 hb0 in
/-- **The full fibration of $\mu^1_{PD}$ is half of `tamQuat`**: $\int_{PD}\int_Z\cdots\,d\mu_Z\,d\mu^1_{PD} = \tfrac12\mu_G$. -/
theorem fibMeas_muPDOne_full :
    NormalFib.fibMeas (pdMk a b) (pdMk_surjective a b) (muPDOne ha hb ha0 hb0) (muZ a b) =
      (2 : ℝ≥0∞)⁻¹ • tamQuat a b := by
  have := isHaarMeasure_muPDOne ha hb ha0 hb0
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  have := isHaarMeasure_muQuatOneTam ha hb ha0 hb0
  set ν := NormalFib.fibMeas (pdMk a b) (pdMk_surjective a b) (muPDOne ha hb ha0 hb0) (muZ a b) with hν
  have hνl : ν.IsMulLeftInvariant := NormalFib.isMulLeftInvariant_fibMeas _ _ (measurable_pdMk a b) _ _
  have hνc : IsFiniteMeasureOnCompacts ν :=
    ⟨fun _ hC => NormalFib.fibMeas_compact_lt_top _ _ (continuous_pdMk a b) _ _ (isClosed_ker_pdMk a b) hC⟩
  set E := quatOneRefSet a b
  have hEm : MeasurableSet E := isCompact_quatOneRefSet.isClosed.measurableSet
  set S := quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)) with hS
  have hSm : MeasurableSet S :=
    (hEm.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))).preimage (quatSplit a b).continuous.measurable
  have hT : tamQuat a b S = muQuatOneTam ha hb ha0 hb0 E := (muQuatOneTam_apply ha hb ha0 hb0 E).symm
  have h0 : tamQuat a b S ≠ 0 := hT ▸ muQuatOneTam_refSet_ne_zero ha hb ha0 hb0
  have htop : tamQuat a b S ≠ ∞ := hT ▸ muQuatOneTam_refSet_ne_top ha hb ha0 hb0
  have hνS : ν S = 2⁻¹ * muQuatOneTam ha hb ha0 hb0 E := by
    rw [hν, NormalFib.fibMeas_apply _ _ (measurable_pdMk a b) _ _ hSm, hS]
    simp_rw [kern_shell _ hEm]
    rw [lintegral_const_mul _ (NormalFib.measurable_kern_apply _ _ (measurable_pdMkOne a b) _ hEm),
      ← NormalFib.fibMeas_apply _ _ (measurable_pdMkOne a b) _ _ hEm, fibMeas_muPDOne]
  rw [measure_eq_div_smul ν (tamQuat a b) h0 htop, hνS, hT,
    ENNReal.mul_div_cancel_right (muQuatOneTam_refSet_ne_zero ha hb ha0 hb0)
      (muQuatOneTam_refSet_ne_top ha hb ha0 hb0)]

include ha hb ha0 hb0 in
/-- **Weil's Tamagawa measure on $PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$**: the quotient of
`tamQuat` by `tamIdeles` (`fibMeas_muPD`, `muPD_unique`). It is $2\,\mu^1_{PD}$: the norm-one quotient measure
undercounts by the factor $\int dt/t$ in $t = \|z\|$ versus $\|\operatorname{nrd}z\| = t^2$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43 (centre argument, ‖N(z)‖ = ‖z‖²)"]
def muPD : Measure (PDA a b) := (2 : ℝ≥0∞) • muPDOne ha hb ha0 hb0

include ha hb ha0 hb0 in
theorem isHaarMeasure_muPD : (muPD ha hb ha0 hb0).IsHaarMeasure := by
  have := isHaarMeasure_muPDOne ha hb ha0 hb0
  exact IsHaarMeasure.smul _ two_ne_zero ENNReal.ofNat_ne_top

include ha hb ha0 hb0 in
/-- **The fibration identity defining Weil's measure on $PD^\times(\mathbb A)$**:
$\int_G f\,d\mu_G = \int_{G/Z}\int_Z f(gz)\,d\mu_Z(z)\,d\mu_{PD}(gZ)$ with $\mu_G$ = `tamQuat`, $\mu_Z$ = `tamIdeles`. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43"]
theorem fibMeas_muPD :
    NormalFib.fibMeas (pdMk a b) (pdMk_surjective a b) (muPD ha hb ha0 hb0) (muZ a b) = tamQuat a b := by
  rw [muPD, fibMeas_smul_base _ _ (measurable_pdMk a b), fibMeas_muPDOne_full, smul_smul,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]

include ha hb ha0 hb0 in
/-- **Uniqueness**: a Haar measure on $PD^\times(\mathbb A)$ whose fibred measure with `tamIdeles` is `tamQuat` is
`muPD`. -/
theorem muPD_unique (μ' : Measure (PDA a b)) [μ'.IsHaarMeasure]
    (h : NormalFib.fibMeas (pdMk a b) (pdMk_surjective a b) μ' (muZ a b) = tamQuat a b) :
    μ' = muPD ha hb ha0 hb0 := by
  have := isHaarMeasure_muPD ha hb ha0 hb0
  have := isHaarMeasure_tamQuat ha hb ha0 hb0
  set c := μ'.haarScalarFactor (muPD ha hb ha0 hb0)
  have hc : μ' = (c : ℝ≥0∞) • muPD ha hb ha0 hb0 := Measure.isMulLeftInvariant_eq_smul _ _
  rw [hc, fibMeas_smul_base _ _ (measurable_pdMk a b), fibMeas_muPD] at h
  set E := quatOneRefSet a b
  have hT := (muQuatOneTam_apply ha hb ha0 hb0 E).symm
  have h0 := muQuatOneTam_refSet_ne_zero ha hb ha0 hb0
  have htop := muQuatOneTam_refSet_ne_top ha hb ha0 hb0
  set S := quatSplit a b ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))
  have := congrArg (fun μ => μ S) h
  simp only [Measure.smul_apply, smul_eq_mul, hT] at this
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h' : (c : ℝ≥0∞) * muQuatOneTam ha hb ha0 hb0 E = 1 * muQuatOneTam ha hb ha0 hb0 E := by
      rw [one_mul]; exact this
    exact (ENNReal.mul_left_inj h0 htop).1 h'
  rw [hc, hc1, one_smul]

end MuPD

/-! ### $\tau(PD^\times) = 2$ -/

section Tau

variable (a b : 𝓞 F)

theorem gammaPD_eq_pdGamma : gammaPD (a : F) (b : F) = pdGamma a b := by
  ext q
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(γ : (QuatAdele (a : F) (b : F))ˣ), Subgroup.mem_subgroupOf.mp hγ, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, quatUnitsSub_le_quatOne _ _ hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem countable_pdGamma : Countable (pdGamma a b) := by
  refine Function.Surjective.countable (f := fun g : quatUnitsSub (a : F) (b : F) =>
    (⟨QuotientGroup.mk' _ g, g, g.2, rfl⟩ : pdGamma a b)) ?_
  rintro ⟨_, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

/-- **$PD^\times(F)$ is discrete in $PD^\times(\mathbb A)$** (transport of `discreteTopology_GammaSOAdele` along
`pdAdeleEquiv`). -/
theorem discreteTopology_pdGamma (ha0 : a ≠ 0) (hb0 : b ≠ 0) : DiscreteTopology (pdGamma a b) := by
  set e := pdAdeleEquiv a b ha0 hb0
  have hmem : ∀ x : pdGamma a b, e x ∈ GammaSOAdele (QuatZeta.pureFormO a b) := fun x => by
    rw [← map_pdGamma a b ha0 hb0]; exact ⟨x, x.2, rfl⟩
  have := discreteTopology_GammaSOAdele (QuatZeta.pureFormO a b)
  exact DiscreteTopology.of_continuous_injective (f := fun x : pdGamma a b => (⟨e x, hmem x⟩ :
    GammaSOAdele (QuatZeta.pureFormO a b))) ((e.continuous.comp continuous_subtype_val).subtype_mk _)
    fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))

theorem exists_exactFD_gammaPD (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ DQ : Set (PDA (a : F) (b : F)), IsExactFD (Γ := gammaPD (a : F) (b : F)) DQ := by
  have := discreteTopology_pdGamma a b ha0 hb0
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (pdGamma a b)
  rw [gammaPD_eq_pdGamma]
  exact ⟨D, hDm, hD⟩

/-- **$\tau(PD^\times) = 2$ for every quaternion division algebra $D = \mathbb H[F,a,b]$ over every number field**
($a, b\in\mathcal O_F\setminus0$, any signature), for Weil's Tamagawa measure `muPD` on
$PD^\times(\mathbb A) = (D\otimes\mathbb A)^\times/\mathbb A^\times$ (the quotient of `tamQuat` by `tamIdeles`, `fibMeas_muPD`):
$$\operatorname{vol}(PD^\times(F)\backslash PD^\times(\mathbb A),\ \mu_{PD}) = 2.$$
*Proof* (Weil, Thm 3.2.1, the centre argument): $c_A' = \operatorname{vol}(F^\times\backslash\mathbb A^1)\cdot\mu^1_{PD}(D_Q)$
(`quatVolConst_eq_mul_muPDOne`), $c_A' = \rho_F$ (`quatVolConst_eq_residue`), $\operatorname{vol}(F^\times\backslash
\mathbb A^1) = \rho_F$ (`muIdeleClass_univ_eq_residue`), so $\mu^1_{PD}(D_Q) = 1$, and $\mu_{PD} = 2\mu^1_{PD}$
(`fibMeas_muPDOne_full`: $\|\operatorname{nrd}z\| = \|z\|^2$ on the centre). Unconditional. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (τ(PD^×) = 2 via τ(SL₁) and the centre)"]
theorem tamagawa_PD_division (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    covolume (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 2 := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  obtain ⟨DQ, hDQ⟩ := exists_exactFD_gammaPD a b ha0 hb0
  have h1 := quatVolConst_eq_mul_muPDOne (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hDQ
  rw [quatVolConst_eq_residue ha0 hb0 hdiv, muIdeleClass_univ_eq_residue] at h1
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact dedekindZeta_residue_pos F
  have hμ1 : muPDOne (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' DQ = 1 := by
    have h1' : ENNReal.ofReal (dedekindZeta_residue F) * 1 = _ := (mul_one _).trans h1
    exact ((ENNReal.mul_right_inj hρ0 ENNReal.ofReal_ne_top).1 h1').symm
  have := countable_pdGamma a b
  rw [gammaPD_eq_pdGamma] at hDQ
  have : SMulInvariantMeasure (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0') :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  rw [(hDQ.isFundamentalDomain _).covolume_eq_volume, muPD, Measure.smul_apply, hμ1, smul_eq_mul, mul_one]

/-- **`TamagawaNumberTwoAdelic` for the pure ternary form $\langle-a,-b,ab\rangle$ of a quaternion division algebra over
any number field**, conditional only on the **local measure comparison**: if Weil's measure $\mu_{PD}$ splits as
$\mu_\infty\times\mu_f$ along $PD^\times(\mathbb A)\cong PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$ with
$(c_\infty)_*\mu_\infty = r_\infty\,\mu^{\mathrm{Tam}}_\infty$, $(c_f)_*\mu_f = r_f\,\mu_f^{SO}$ and $r_\infty r_f = 1$
(Weil's Thm 2.3.1: $\prod_v r_v = 1$; the local ratios), then $\tau(SO(V)) = 2$ for `muTam`.
*Proof.* $\tau(PD^\times) = 2$ (`tamagawa_PD_division`), transported by `covolume_eq_of_map` and `tamagawaNumberTwoAdelic_iff_covolume_pd`. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem tamagawaNumberTwoAdelic_of_division (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) (hQ : (QuatZeta.pureFormO a b).Nondegenerate)
    (μI : Measure (PDInf a b)) (μF : Measure (PDFin a b)) [SFinite μI] [SFinite μF] [μI.IsMulLeftInvariant]
    [μF.IsMulLeftInvariant]
    (hsplit : (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)).map
      (pdSplit a b ha0 hb0) = μI.prod μF)
    {rI rF : ℝ≥0∞} (hI : μI.map (pdInfEquiv a b ha0 hb0) = rI • muArchTamSO (QuatZeta.pureFormO a b) hQ)
    (hF : μF.map (pdFinEquiv a b ha0 hb0) = rF • QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b)
      (fun _ => 1)) (hr : rI * rF = 1) :
    TamagawaNumberTwoAdelic (QuatZeta.pureFormO a b) hQ := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  have := countable_pdGamma a b
  refine (tamagawaNumberTwoAdelic_iff_covolume_pd a b ha0 hb0 hQ μI μF hI hF hr).2 ?_
  rw [← covolume_eq_of_map (pdGamma a b) (pdGammaSplit a b ha0 hb0) (pdSplit a b ha0 hb0).toMulEquiv
    (pdSplit a b ha0 hb0).continuous.measurable (pdSplit a b ha0 hb0).symm.continuous.measurable rfl _ _ hsplit]
  exact tamagawa_PD_division a b ha0 hb0 hdiv

end Tau

end

end QuadFormsKB.Tamagawa.Measure.Weil
