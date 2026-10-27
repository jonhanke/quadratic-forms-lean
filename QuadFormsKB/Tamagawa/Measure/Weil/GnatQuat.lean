import QuadFormsKB.Tamagawa.Measure.Weil.GnatAbstract
import QuadFormsKB.Tamagawa.Measure.Weil.PDCentre

/-!
# Quaternion inputs for $G^\natural$: $\mathrm{SL}_1$ as $\ker\operatorname{nrd}$, $A_+$, signs, Eichler

**Layer:** $F$ any number field, $D = \mathbb H[F,a,b]$ with $a, b\in\mathcal O_F\setminus0$ (the library's standard order). The data
that `GnatData` (`GnatAbstract.lean`) needs from a quaternion algebra, in terms of the full unit group
$(D\otimes\mathbb A)^\times$ and $\operatorname{nrd} = $ `nrdHom` instead of the norm-one group:

* `posA a b`: $A_+ = \{u\in\mathbb A^\times : u_w > 0$ at the real places where $D$ ramifies$\}$, open (`isOpen_posA`), and
  **`mem_posA_iff_exists_nrd`**: $A_+ = \operatorname{nrd}((D\otimes\mathbb A)^\times)$ (`exists_nrdUnit_eq`, `nrdUnit_pos_of_ramified`);
* `exists_diag_mul_mem_posA`: every $F^\times$-orbit in $\mathbb A^\times$ meets $A_+$ (weak approximation of signs);
* `exists_global_nrd`: $F^\times\cap A_+\subseteq\operatorname{nrd}(D^\times)$ (Hasse–Schilling–Maass/Eichler,
  `eichler_norm_theorem_general`);
* `kerNrdEquiv`: $\ker(\operatorname{nrd})\cong$ the `SL1A`, matching the global points (`kerNrdEquiv_mem_iff`);
* `muSL1N`: the Tamagawa measure `muSL1` on $\ker\operatorname{nrd}$; `adK_nrdHom_eq`: conjugation by a unit only
  depends on its norm-one part (the central section `quatSplit`). Its covolume $1$ (`covolume_muSL1N`) and its conjugation
  invariance (`map_adK_muSL1N`), for every quaternion algebra, are in `GnatSquare.lean` (they use the split
  $\tau(\mathrm{SL}_1) = 1$, which is downstream of this file);
* `hdiv_of_totallyNeg`: a totally definite $D$ ($a, b$ negative at every real place) over a totally real $F$ is a division algebra.
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

section Pos

variable (a b : F)

/-- $A_+$: ideles positive at the real places where $\mathbb H[F,a,b]$ ramifies. -/
def posA : Subgroup (Adeles F)ˣ where
  carrier := {u | PosAtRamified a b u}
  one_mem' := fun w hw _ => by simp
  mul_mem' := fun {u v} hu hv w hw hram => by
    change 0 < ((u * v : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
    rw [idele_mul_fst_fst]; exact mul_pos (hu w hw hram) (hv w hw hram)
  inv_mem' := fun {u} hu w hw hram => by
    change 0 < ((u⁻¹ : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
    rw [idele_inv_fst_fst]; exact inv_pos.2 (hu w hw hram)

theorem mem_posA {u : (Adeles F)ˣ} : u ∈ posA a b ↔ PosAtRamified a b u := Iff.rfl

theorem isOpen_posA : IsOpen (posA a b : Set (Adeles F)ˣ) := by
  have : (posA a b : Set (Adeles F)ˣ) = ⋂ (w : InfinitePlace F) (hw : w.IsReal)
      (_ : QuadFormsKB.Quat.IsRamifiedReal a b w hw),
      (fun u : (Adeles F)ˣ => (u : Adeles F).1.1 ⟨w, hw⟩) ⁻¹' Ioi 0 := by
    ext u; simp [mem_posA, PosAtRamified]
  rw [this]
  exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun hw => isOpen_iInter_of_finite fun _ =>
    isOpen_Ioi.preimage (continuous_idele_fst_fst ⟨w, hw⟩)

variable {a b}

/-- **$A_+ = \operatorname{nrd}((D\otimes\mathbb A)^\times)$.** -/
theorem mem_posA_iff_exists_nrd (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) :
    u ∈ posA a b ↔ ∃ x : (QuatAdele a b)ˣ, nrdHom a b x = u :=
  ⟨fun h => exists_nrdUnit_eq ha0 hb0 u h, fun ⟨x, hx⟩ => hx ▸ nrdUnit_pos_of_ramified x⟩

/-- **Every $F^\times$-orbit in $\mathbb A^\times$ meets $A_+$** (weak approximation at the real places, `exists_signs`). -/
theorem exists_diag_mul_mem_posA (x : (Adeles F)ˣ) : ∃ f : Fˣ, diagUnits F f * x ∈ posA a b := by
  obtain ⟨c, hc0, hc⟩ := QuadFormsKB.Quat.exists_signs (F := F)
    (fun w hw => 0 < (x : Adeles F).1.1 ⟨w, hw⟩)
  refine ⟨Units.mk0 c hc0, fun w hw _ => ?_⟩
  change 0 < ((diagUnits F (Units.mk0 c hc0) * x : (Adeles F)ˣ) : Adeles F).1.1 ⟨w, hw⟩
  rw [idele_mul_fst_fst, diagUnits_val]
  have hσ : (diag F ((Units.mk0 c hc0 : Fˣ) : F)).1.1 ⟨w, hw⟩ = embedding_of_isReal hw c := diag_fst_fst c ⟨w, hw⟩
  rw [hσ]
  have hy0 : (x : Adeles F).1.1 ⟨w, hw⟩ ≠ 0 := idele_fst_fst_ne_zero _ _
  have hc0' : embedding_of_isReal hw c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have : ¬ 0 < embedding_of_isReal hw c := fun h => absurd ((hc w hw).1 h) (not_lt.2 hneg.le)
    exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 this) hc0') hneg
  · exact mul_pos ((hc w hw).2 hpos) hpos

/-- **Eichler's norm theorem, adelic form**: $F^\times\cap A_+\subseteq\operatorname{nrd}(D^\times)$. -/
theorem exists_global_nrd (ha0 : a ≠ 0) (hb0 : b ≠ 0) (f : Fˣ) (hf : diagUnits F f ∈ posA a b) :
    ∃ γ ∈ quatUnitsSub a b, nrdHom a b γ = diagUnits F f := by
  have hpos : ∀ (w : InfinitePlace F) (hw : w.IsReal), QuadFormsKB.Quat.IsRamifiedReal a b w hw →
      0 < embedding_of_isReal hw (f : F) := by
    intro w hw hram
    have := hf w hw hram
    rw [diagUnits_val, diag_fst_fst] at this
    exact this
  obtain ⟨α, hαu, hα⟩ := (QuadFormsKB.Quat.eichler_norm_theorem_general ha0 hb0 (f : F)).2 ⟨f.ne_zero, hpos⟩
  refine ⟨Units.map (quatDiagRing a b).toMonoidHom hαu.unit, ⟨hαu.unit, rfl⟩, Units.ext ?_⟩
  change ((nrdUnit (Units.map (quatDiagRing a b).toMonoidHom hαu.unit) : (Adeles F)ˣ) : Adeles F) = _
  rw [nrdUnit_map_quatDiagRing, IsUnit.unit_spec, hα, diagUnits_val]

end Pos

/-! ### $\ker\operatorname{nrd}\cong\mathrm{SL}_1$ and its Tamagawa measure -/

section Kernel

variable (a b : F)

theorem mem_quatOne_of_mem_ker {x : (QuatAdele a b)ˣ} (hx : x ∈ (nrdHom a b).ker) : x ∈ quatOne a b := by
  rw [mem_quatOne]
  have : nrdUnit x = 1 := hx
  rw [this, ideleNorm_one]

/-- **$\ker(\operatorname{nrd} : (D\otimes\mathbb A)^\times\to\mathbb A^\times)\cong$ the `SL1A`** (inside $\mathbb H_{\mathbb A}^1$). -/
def kerNrdEquiv : (nrdHom a b).ker ≃ₜ* SL1A a b where
  toFun x := ⟨⟨x, mem_quatOne_of_mem_ker a b x.2⟩, mem_SL1A.2 x.2⟩
  invFun y := ⟨(y : quatOne a b), mem_SL1A.1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

@[simp] theorem coe_kerNrdEquiv (x : (nrdHom a b).ker) :
    (((kerNrdEquiv a b x : SL1A a b) : quatOne a b) : (QuatAdele a b)ˣ) = x := rfl

theorem kerNrdEquiv_mem_iff (x : (nrdHom a b).ker) :
    kerNrdEquiv a b x ∈ SL1F a b ↔ x ∈ (quatUnitsSub a b).subgroupOf (nrdHom a b).ker := by
  rw [Subgroup.mem_subgroupOf]
  change ((kerNrdEquiv a b x : SL1A a b) : quatOne a b) ∈ (quatUnitsSub a b).subgroupOf (quatOne a b) ↔ _
  rw [Subgroup.mem_subgroupOf]; rfl

instance : SecondCountableTopology (nrdHom a b).ker := TopologicalSpace.Subtype.secondCountableTopology _

instance : Countable ((quatUnitsSub a b).subgroupOf (nrdHom a b).ker) :=
  Injective.countable (f := fun x : (quatUnitsSub a b).subgroupOf (nrdHom a b).ker =>
    (⟨((x : (nrdHom a b).ker) : (QuatAdele a b)ˣ), x.2⟩ : quatUnitsSub a b))
    fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')

theorem isClosed_ker_nrdHom : IsClosed ((nrdHom a b).ker : Set (QuatAdele a b)ˣ) := by
  have : ((nrdHom a b).ker : Set (QuatAdele a b)ˣ) = nrdHom a b ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
  rw [this]; exact isClosed_singleton.preimage continuous_nrdHom

instance : LocallyCompactSpace (nrdHom a b).ker :=
  (isClosed_ker_nrdHom a b).isClosedEmbedding_subtypeVal.locallyCompactSpace

set_option maxHeartbeats 1000000 in
/-- $\operatorname{Ad}(m)$ on $\ker\operatorname{nrd}$ only depends on the norm-one part of $m$ (the scalars are central). -/
theorem adK_nrdHom_eq (m : (QuatAdele a b)ˣ) :
    NormalFib.adK (nrdHom a b) m =
      (kerNrdEquiv a b).symm ∘ NormalFib.adK (nrdOne a b) (quatSplit a b m).1 ∘ kerNrdEquiv a b := by
  funext x
  apply Subtype.ext
  set z := quatSectionHom a b (quatLogNorm a b m)
  have hm1 : ((quatSplit a b m).1 : (QuatAdele a b)ˣ) = m * z⁻¹ := rfl
  have hz : z * (x : (QuatAdele a b)ˣ) = (x : (QuatAdele a b)ˣ) * z := quatScalar_comm a b _ _
  show m * (x : (QuatAdele a b)ˣ) * m⁻¹ =
    ((quatSplit a b m).1 : (QuatAdele a b)ˣ) * (x : (QuatAdele a b)ˣ) * ((quatSplit a b m).1 : (QuatAdele a b)ˣ)⁻¹
  rw [hm1]
  calc m * (x : (QuatAdele a b)ˣ) * m⁻¹ = m * z⁻¹ * (z * (x : (QuatAdele a b)ˣ)) * m⁻¹ := by group
    _ = m * z⁻¹ * ((x : (QuatAdele a b)ˣ) * z) * m⁻¹ := by rw [hz]
    _ = m * z⁻¹ * (x : (QuatAdele a b)ˣ) * (m * z⁻¹)⁻¹ := by group

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha0 hb0 in
theorem coe_ne_zero_of (h : a ≠ 0) : (a : F) ≠ 0 := by simpa using h

/-- **the Tamagawa measure of $\mathrm{SL}_1$ on $\ker\operatorname{nrd}$.** -/
def muSL1N : Measure (nrdHom (a : F) (b : F)).ker :=
  (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)).map
    (kerNrdEquiv (a : F) (b : F)).symm

instance : (muSL1N ha0 hb0).IsHaarMeasure := by
  have := isHaarMeasure_muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (F := F)
    (by simpa using ha0) (by simpa using hb0)
  exact ContinuousMulEquiv.isHaarMeasure_map _ _

end Kernel

/-! ### Totally definite quaternion algebras are division algebras -/

/-- **A totally definite quaternion algebra over a totally real field is a division algebra**: if $a, b$ are negative at
every real place, then $\operatorname{nrd}\xi = x_0^2 - ax_1^2 - bx_2^2 + abx_3^2$ is positive at any real place for $\xi\ne0$. -/
theorem hdiv_of_totallyNeg [IsTotallyReal F] {a b : F}
    (ha : ∀ w : InfinitePlace F, ∀ hw : w.IsReal, embedding_of_isReal hw a < 0)
    (hb : ∀ w : InfinitePlace F, ∀ hw : w.IsReal, embedding_of_isReal hw b < 0) :
    ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ := by
  refine isUnit_of_nrd_ne_zero a b fun ξ hξ h0 => hξ ?_
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw : w.IsReal := IsTotallyReal.isReal w
  set σ := embedding_of_isReal hw
  have hre : (ξ * star ξ).re = ξ.re ^ 2 - a * ξ.imI ^ 2 - b * ξ.imJ ^ 2 + a * b * ξ.imK ^ 2 := by
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
      QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
    ring
  have hσ : σ ((ξ * star ξ).re) = σ ξ.re ^ 2 + (-σ a) * σ ξ.imI ^ 2 + (-σ b) * σ ξ.imJ ^ 2 +
      (σ a * σ b) * σ ξ.imK ^ 2 := by
    rw [hre]; simp only [map_add, map_sub, map_mul, map_pow]; ring
  rw [h0, map_zero] at hσ
  have hA := ha w hw
  have hB := hb w hw
  have h1 : 0 ≤ σ ξ.re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (-σ a) * σ ξ.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (-σ b) * σ ξ.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ (σ a * σ b) * σ ξ.imK ^ 2 := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hA.le hB.le) (sq_nonneg _)
  have e1 : σ ξ.re = 0 := by nlinarith
  have e2 : σ ξ.imI = 0 := by
    have : (-σ a) * σ ξ.imI ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  have e3 : σ ξ.imJ = 0 := by
    have : (-σ b) * σ ξ.imJ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  have e4 : σ ξ.imK = 0 := by
    have : (σ a * σ b) * σ ξ.imK ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · nlinarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  have hinj : Function.Injective σ := σ.injective
  ext
  · exact hinj (by rw [e1]; simp)
  · exact hinj (by rw [e2]; simp)
  · exact hinj (by rw [e3]; simp)
  · exact hinj (by rw [e4]; simp)

end

end QuadFormsKB.Tamagawa.Measure.Weil
