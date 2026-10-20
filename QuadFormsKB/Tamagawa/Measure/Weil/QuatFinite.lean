import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocal
import QuadFormsKB.Tamagawa.Measure.Weil.QuatUnits
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleChart
import QuadFormsKB.Tamagawa.Measure.Weil.ChartAbstract

/-!
# $(\mathbb H\otimes\mathbb A_f)^\times$ as a restricted product of the $(\mathbb H\otimes F_v)^\times$

$\mathbb H = \mathbb H[F,a,b]$ over a number field $F$; `QuatFin a b` $=\mathbb H[\mathbb A_f,a,b]$ with the coordinate
topology ($1,i,j,k$), and `QuatLoc` $=\mathbb H[F_v,a,b]$ (`QuatLocal.lean`).

* `projQ v : ℍ[𝔸_f] →+* ℍ[F_v]` (coordinatewise evaluation), `unitAtQ v` on units; `singleQ v y` is the element equal
  to $y$ at $v$ and $1$ elsewhere (**`projQ_singleQ`**), multiplicative (`singleQHom`), on units `singleQUnit`.
* The standard order $\Lambda = \mathcal O_F\langle 1,i,j,k\rangle$: locally $\Lambda_v$ (`lamLoc`) and its units
  $\Lambda_v^\times$ (`lamLocUnits` $=\{u : u, u^{-1}\in\Lambda_v\}$), open and compact in $(\mathbb H\otimes F_v)^\times$;
  globally $\hat\Lambda$ (`lamHat`) and $\hat\Lambda^\times$ (`lamHatUnits`), open and compact
  (**`isCompact_lamHatUnits`**), so $(\mathbb H\otimes\mathbb A_f)^\times$ is locally compact.
* For $a, b$ integral at every place ($v(a), v(b)\le1$), $\Lambda_v$ is a ring, $\hat\Lambda^\times$ is a subgroup
  (`lamHatUnitsSub`), and $\Lambda_v^\times = \{x\in\Lambda_v : \operatorname{nrd}(x)\in\mathcal O_v^\times\}$
  (**`mem_lamLocUnits_iff`**).
* `quatChart a b` : the chart data (`ChartData`) $(p_v, s_v, \Lambda_v^\times)$; its box over $S = \emptyset$ is
  $\hat\Lambda^\times$ (**`chartBox_empty_quatChart`**).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

variable (a b : F)

/-- $\mathbb H[\mathbb A_f,a,b]$. -/
abbrev QuatFin := ℍ[AF, algebraMap F AF a, 0, algebraMap F AF b]

/-- $\mathbb H[F_v,a,b]$. -/
abbrev QuatV (v : HeightOneSpectrum (𝓞 F)) :=
  QuatLoc (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)

/-! ### Topology on $\mathbb H[\mathbb A_f,a,b]$ -/

/-- The coordinates $1,i,j,k$. -/
abbrev quatFinCoord : QuatFin a b ≃ₗ[AF] (Fin 4 → AF) := QuaternionAlgebra.linearEquivTuple _ _ _

instance : TopologicalSpace (QuatFin a b) := TopologicalSpace.induced (quatFinCoord a b) inferInstance

theorem isInducing_quatFinCoord : IsInducing (quatFinCoord a b) := ⟨rfl⟩

theorem isEmbedding_quatFinCoord : IsEmbedding (quatFinCoord a b) :=
  ⟨isInducing_quatFinCoord a b, (quatFinCoord a b).injective⟩

theorem continuous_quatFinCoord : Continuous (quatFinCoord a b) := (isInducing_quatFinCoord a b).continuous

theorem continuous_fre : Continuous fun x : QuatFin a b => x.re :=
  (continuous_apply 0).comp (continuous_quatFinCoord a b)
theorem continuous_fimI : Continuous fun x : QuatFin a b => x.imI :=
  (continuous_apply 1).comp (continuous_quatFinCoord a b)
theorem continuous_fimJ : Continuous fun x : QuatFin a b => x.imJ :=
  (continuous_apply 2).comp (continuous_quatFinCoord a b)
theorem continuous_fimK : Continuous fun x : QuatFin a b => x.imK :=
  (continuous_apply 3).comp (continuous_quatFinCoord a b)

theorem continuous_quatFin_iff {X : Type*} [TopologicalSpace X] {f : X → QuatFin a b} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  refine ⟨fun h => ⟨(continuous_fre a b).comp h, (continuous_fimI a b).comp h, (continuous_fimJ a b).comp h,
    (continuous_fimK a b).comp h⟩, fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  rw [(isInducing_quatFinCoord a b).continuous_iff, continuous_pi_iff]
  intro i; fin_cases i
  exacts [h0, h1, h2, h3]

instance : ContinuousMul (QuatFin a b) := ⟨by
  set P := QuatFin a b × QuatFin a b
  have hf : Continuous fun p : P => p.1.re := (continuous_fre a b).comp continuous_fst
  have hs : Continuous fun p : P => p.2.re := (continuous_fre a b).comp continuous_snd
  have hf1 : Continuous fun p : P => p.1.imI := (continuous_fimI a b).comp continuous_fst
  have hs1 : Continuous fun p : P => p.2.imI := (continuous_fimI a b).comp continuous_snd
  have hf2 : Continuous fun p : P => p.1.imJ := (continuous_fimJ a b).comp continuous_fst
  have hs2 : Continuous fun p : P => p.2.imJ := (continuous_fimJ a b).comp continuous_snd
  have hf3 : Continuous fun p : P => p.1.imK := (continuous_fimK a b).comp continuous_fst
  have hs3 : Continuous fun p : P => p.2.imK := (continuous_fimK a b).comp continuous_snd
  refine (continuous_quatFin_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul] <;> fun_prop⟩

instance : T2Space (QuatFin a b) := (isEmbedding_quatFinCoord a b).t2Space

instance : SecondCountableTopology (QuatFin a b) := (isInducing_quatFinCoord a b).secondCountableTopology

instance : SecondCountableTopology (QuatFin a b)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuatFin a b)).symm.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuatFin a b)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology

instance measurableSpace_quatFinUnits : MeasurableSpace (QuatFin a b)ˣ := borel _

instance : BorelSpace (QuatFin a b)ˣ := ⟨rfl⟩

/-! ### Local projections and single-place elements -/

theorem evalAt_algebraMap (v : HeightOneSpectrum (𝓞 F)) (c : F) :
    evalAt v (algebraMap F AF c) = algebraMap F (v.adicCompletion F) c := rfl

/-- The projection $\mathbb H[\mathbb A_f]\to\mathbb H[F_v]$. -/
def projQ (v : HeightOneSpectrum (𝓞 F)) : QuatFin a b →+* QuatV a b v :=
  QuaternionAlgebra.mapRingHom (evalAt v) (evalAt_algebraMap v a) (map_zero _) (evalAt_algebraMap v b)

@[simp] theorem projQ_re (v : HeightOneSpectrum (𝓞 F)) (x : QuatFin a b) : (projQ a b v x).re = x.re v := rfl
@[simp] theorem projQ_imI (v : HeightOneSpectrum (𝓞 F)) (x : QuatFin a b) : (projQ a b v x).imI = x.imI v := rfl
@[simp] theorem projQ_imJ (v : HeightOneSpectrum (𝓞 F)) (x : QuatFin a b) : (projQ a b v x).imJ = x.imJ v := rfl
@[simp] theorem projQ_imK (v : HeightOneSpectrum (𝓞 F)) (x : QuatFin a b) : (projQ a b v x).imK = x.imK v := rfl

theorem projQ_injective {x y : QuatFin a b} (h : ∀ v, projQ a b v x = projQ a b v y) : x = y := by
  have hre : x.re = y.re := Subtype.ext (funext fun v => congrArg QuaternionAlgebra.re (h v))
  have hI : x.imI = y.imI := Subtype.ext (funext fun v => congrArg QuaternionAlgebra.imI (h v))
  have hJ : x.imJ = y.imJ := Subtype.ext (funext fun v => congrArg QuaternionAlgebra.imJ (h v))
  have hK : x.imK = y.imK := Subtype.ext (funext fun v => congrArg QuaternionAlgebra.imK (h v))
  exact QuaternionAlgebra.ext hre hI hJ hK

theorem continuous_projQ (v : HeightOneSpectrum (𝓞 F)) : Continuous (projQ a b v) := by
  refine (continuous_quatLoc_iff _ _).mpr ⟨?_, ?_, ?_, ?_⟩
  · exact (RestrictedProduct.continuous_eval v).comp (continuous_fre a b)
  · exact (RestrictedProduct.continuous_eval v).comp (continuous_fimI a b)
  · exact (RestrictedProduct.continuous_eval v).comp (continuous_fimJ a b)
  · exact (RestrictedProduct.continuous_eval v).comp (continuous_fimK a b)

/-- The local component of a unit. -/
def unitAtQ (v : HeightOneSpectrum (𝓞 F)) : (QuatFin a b)ˣ →* (QuatV a b v)ˣ := Units.map (projQ a b v).toMonoidHom

@[simp] theorem unitAtQ_val (v : HeightOneSpectrum (𝓞 F)) (u : (QuatFin a b)ˣ) :
    ((unitAtQ a b v u : (QuatV a b v)ˣ) : QuatV a b v) = projQ a b v u := rfl

theorem continuous_unitAtQ (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitAtQ a b v) :=
  Units.continuous_iff.mpr ⟨(continuous_projQ a b v).comp Units.continuous_val,
    (continuous_projQ a b v).comp Units.continuous_coe_inv⟩

/-- The element of $\mathbb H[\mathbb A_f]$ equal to $y$ at $v$ and $1$ elsewhere. -/
def singleQ (v : HeightOneSpectrum (𝓞 F)) (y : QuatV a b v) : QuatFin a b :=
  ⟨1 + singleAt v (y.re - 1), singleAt v y.imI, singleAt v y.imJ, singleAt v y.imK⟩

theorem projQ_singleQ (v w : HeightOneSpectrum (𝓞 F)) (y : QuatV a b v) :
    projQ a b w (singleQ a b v y) = Pi.mulSingle (M := fun w => QuatV a b w) v y w := by
  by_cases h : w = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · change (1 : w.adicCompletion F) + singleAt w (y.re - 1) w = y.re
      rw [singleAt_apply, Pi.single_eq_same]; ring
    · change singleAt w y.imI w = y.imI; rw [singleAt_apply, Pi.single_eq_same]
    · change singleAt w y.imJ w = y.imJ; rw [singleAt_apply, Pi.single_eq_same]
    · change singleAt w y.imK w = y.imK; rw [singleAt_apply, Pi.single_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h]
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · change (1 : w.adicCompletion F) + singleAt v (y.re - 1) w = 1
      rw [singleAt_apply, Pi.single_eq_of_ne h, add_zero]
    · change singleAt v y.imI w = 0; rw [singleAt_apply, Pi.single_eq_of_ne h]
    · change singleAt v y.imJ w = 0; rw [singleAt_apply, Pi.single_eq_of_ne h]
    · change singleAt v y.imK w = 0; rw [singleAt_apply, Pi.single_eq_of_ne h]

/-- `singleQ v` as a monoid homomorphism. -/
def singleQHom (v : HeightOneSpectrum (𝓞 F)) : QuatV a b v →* QuatFin a b where
  toFun := singleQ a b v
  map_one' := projQ_injective a b fun w => by
    rw [projQ_singleQ, Pi.mulSingle_one, map_one]; rfl
  map_mul' y z := projQ_injective a b fun w => by
    rw [map_mul, projQ_singleQ, projQ_singleQ, projQ_singleQ, Pi.mulSingle_mul]; rfl

/-- The single-place unit section $s_v : (\mathbb H\otimes F_v)^\times\to(\mathbb H\otimes\mathbb A_f)^\times$. -/
def singleQUnit (v : HeightOneSpectrum (𝓞 F)) : (QuatV a b v)ˣ →* (QuatFin a b)ˣ := Units.map (singleQHom a b v)

theorem unitAtQ_singleQUnit_self (v : HeightOneSpectrum (𝓞 F)) (x : (QuatV a b v)ˣ) :
    unitAtQ a b v (singleQUnit a b v x) = x :=
  Units.ext (by
    change projQ a b v (singleQ a b v x) = x
    rw [projQ_singleQ, Pi.mulSingle_eq_same])

theorem unitAtQ_singleQUnit_of_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : (QuatV a b v)ˣ) :
    unitAtQ a b w (singleQUnit a b v x) = 1 :=
  Units.ext (by
    change projQ a b w (singleQ a b v x) = 1
    rw [projQ_singleQ, Pi.mulSingle_eq_of_ne h])

/-! ### The standard order locally: $\Lambda_v$ and $\Lambda_v^\times$ -/

/-- $\Lambda_v = \mathcal O_v\langle1,i,j,k\rangle\subseteq\mathbb H[F_v]$: all four coordinates integral. -/
def lamLoc (v : HeightOneSpectrum (𝓞 F)) : Set (QuatV a b v) :=
  {x | x.re ∈ v.adicCompletionIntegers F ∧ x.imI ∈ v.adicCompletionIntegers F ∧
    x.imJ ∈ v.adicCompletionIntegers F ∧ x.imK ∈ v.adicCompletionIntegers F}

theorem lamLoc_eq (v : HeightOneSpectrum (𝓞 F)) :
    lamLoc a b v = quatLocCoord _ _ ⁻¹' Set.pi univ fun _ => (v.adicCompletionIntegers F : Set _) := by
  ext x
  simp only [lamLoc, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_imp_iff, Fin.forall_fin_succ,
    IsEmpty.forall_iff, SetLike.mem_coe]
  simp [QuaternionAlgebra.linearEquivTuple]
  tauto

theorem isOpen_lamLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (lamLoc a b v) := by
  rw [lamLoc_eq]
  exact (isOpen_set_pi finite_univ fun _ _ => isOpen_adicCompletionIntegers v).preimage
    (continuous_quatLocCoord _ _)

theorem isCompact_lamLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (lamLoc a b v) := by
  rw [lamLoc_eq, (isClosedEmbedding_quatLocCoord _ _).isCompact_preimage_iff]
  · exact isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v
  · rw [(quatLocCoord _ _).surjective.range_eq]; exact subset_univ _

theorem one_mem_lamLoc (v : HeightOneSpectrum (𝓞 F)) : (1 : QuatV a b v) ∈ lamLoc a b v := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩ <;> simp [zero_mem]

/-- $\Lambda_v^\times = \{u : u, u^{-1}\in\Lambda_v\}$. -/
def lamLocUnits (v : HeightOneSpectrum (𝓞 F)) : Set (QuatV a b v)ˣ :=
  {u | (u : QuatV a b v) ∈ lamLoc a b v ∧ ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) ∈ lamLoc a b v}

theorem isOpen_lamLocUnits (v : HeightOneSpectrum (𝓞 F)) : IsOpen (lamLocUnits a b v) :=
  ((isOpen_lamLoc a b v).preimage Units.continuous_val).inter
    ((isOpen_lamLoc a b v).preimage Units.continuous_coe_inv)

theorem one_mem_lamLocUnits (v : HeightOneSpectrum (𝓞 F)) : (1 : (QuatV a b v)ˣ) ∈ lamLocUnits a b v :=
  ⟨one_mem_lamLoc a b v, by rw [inv_one]; exact one_mem_lamLoc a b v⟩

/-- Compactness of $\{u : u, u^{-1}\in C\}$ in $M^\times$ for compact $C$ (closed in $M\times M^{\mathrm{op}}$). -/
theorem isCompact_units_of_isCompact {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] [T2Space M]
    {C : Set M} (hC : IsCompact C) : IsCompact {u : Mˣ | (u : M) ∈ C ∧ ((u⁻¹ : Mˣ) : M) ∈ C} := by
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hK : IsCompact (C ×ˢ (MulOpposite.op '' C)) := hC.prod (hC.image MulOpposite.continuous_op)
  have hCl : IsClosed {p : M × Mᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} :=
    (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
      (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  have hset : Units.embedProduct M '' {u : Mˣ | (u : M) ∈ C ∧ ((u⁻¹ : Mˣ) : M) ∈ C} =
      (C ×ˢ (MulOpposite.op '' C)) ∩ {p : M × Mᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, ⟨hu, hu'⟩, h⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨hu, ⟨_, hu', rfl⟩⟩, u.mul_inv, u.inv_mul⟩
    · rintro ⟨⟨hx, ⟨y', hy', rfl⟩⟩, h1, h2⟩
      exact ⟨⟨x, y', h1, h2⟩, ⟨hx, hy'⟩, rfl⟩
  rw [hset]
  exact hK.inter_right hCl

theorem isCompact_lamLocUnits (v : HeightOneSpectrum (𝓞 F)) : IsCompact (lamLocUnits a b v) :=
  isCompact_units_of_isCompact (isCompact_lamLoc a b v)

/-! ### The standard order globally: $\hat\Lambda$ and $\hat\Lambda^\times$ -/

/-- $\hat\Lambda = \hat{\mathcal O}\langle1,i,j,k\rangle\subseteq\mathbb H[\mathbb A_f]$. -/
def lamHat : Set (QuatFin a b) := {x | x.re ∈ OHat ∧ x.imI ∈ OHat ∧ x.imJ ∈ OHat ∧ x.imK ∈ OHat}

theorem mem_lamHat_iff (x : QuatFin a b) : x ∈ lamHat a b ↔ ∀ v, projQ a b v x ∈ lamLoc a b v := by
  simp only [lamHat, lamLoc, mem_ofPred_eq, OHat, projQ_re, projQ_imI, projQ_imJ, projQ_imK]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ v; exact ⟨h0 v, h1 v, h2 v, h3 v⟩
  · intro h; exact ⟨fun v => (h v).1, fun v => (h v).2.1, fun v => (h v).2.2.1, fun v => (h v).2.2.2⟩

theorem lamHat_eq : lamHat a b = quatFinCoord a b ⁻¹' Set.pi univ fun _ => OHat := by
  ext x
  simp only [lamHat, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_imp_iff, Fin.forall_fin_succ,
    IsEmpty.forall_iff]
  simp [QuaternionAlgebra.linearEquivTuple]
  tauto

theorem isOpen_lamHat : IsOpen (lamHat a b) := by
  rw [lamHat_eq]
  exact (isOpen_set_pi finite_univ fun _ _ => isOpen_OHat).preimage (continuous_quatFinCoord a b)

theorem isCompact_lamHat : IsCompact (lamHat a b) := by
  rw [lamHat_eq, (isEmbedding_quatFinCoord a b).isCompact_preimage_iff]
  · exact isCompact_univ_pi fun _ => isCompact_OHat
  · rw [(quatFinCoord a b).surjective.range_eq]; exact subset_univ _

/-- $\hat\Lambda^\times = \{u : u, u^{-1}\in\hat\Lambda\}$. -/
def lamHatUnits : Set (QuatFin a b)ˣ := {u | (u : QuatFin a b) ∈ lamHat a b ∧ ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) ∈ lamHat a b}

theorem isOpen_lamHatUnits : IsOpen (lamHatUnits a b) :=
  ((isOpen_lamHat a b).preimage Units.continuous_val).inter ((isOpen_lamHat a b).preimage Units.continuous_coe_inv)

theorem isCompact_lamHatUnits : IsCompact (lamHatUnits a b) := isCompact_units_of_isCompact (isCompact_lamHat a b)

theorem one_mem_lamHatUnits : (1 : (QuatFin a b)ˣ) ∈ lamHatUnits a b := by
  have h1 : (1 : QuatFin a b) ∈ lamHat a b := by
    rw [mem_lamHat_iff]; intro v; rw [map_one]; exact one_mem_lamLoc a b v
  exact ⟨h1, by rw [inv_one]; exact h1⟩

theorem mem_lamHatUnits_iff (u : (QuatFin a b)ˣ) : u ∈ lamHatUnits a b ↔ ∀ v, unitAtQ a b v u ∈ lamLocUnits a b v := by
  have hinv : ∀ v, (((unitAtQ a b v u)⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) =
      projQ a b v ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) := fun v => by rw [← map_inv]; rfl
  simp only [lamHatUnits, lamLocUnits, mem_ofPred_eq, mem_lamHat_iff, hinv, unitAtQ_val]
  exact ⟨fun ⟨h1, h2⟩ v => ⟨h1 v, h2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

/-- **$(\mathbb H\otimes\mathbb A_f)^\times$ is locally compact** ($\hat\Lambda^\times$ is a compact neighbourhood of $1$). -/
instance : LocallyCompactSpace (QuatFin a b)ˣ := by
  obtain ⟨K, hK, hKs, hKn⟩ : ∃ K : Set (QuatFin a b)ˣ, IsCompact K ∧ K ⊆ lamHatUnits a b ∧ K ∈ 𝓝 1 :=
    ⟨lamHatUnits a b, isCompact_lamHatUnits a b, subset_rfl,
      (isOpen_lamHatUnits a b).mem_nhds (one_mem_lamHatUnits a b)⟩
  exact hK.locallyCompactSpace_of_mem_nhds_of_group hKn

/-! ### Measurability on the local unit groups -/

instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (QuatV a b v)ˣ :=
  (isOpenEmbedding_val_quatLoc _ _).locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (QuatV a b v)ˣ :=
  (isOpenEmbedding_val_quatLoc _ _).isEmbedding.secondCountableTopology

/-! ### The chart data -/

/-- **The chart data of $(\mathbb H\otimes\mathbb A_f)^\times$**: projections `unitAtQ`, sections `singleQUnit`, standard
open sets $\Lambda_v^\times$. -/
def quatChart : ChartData (QuatFin a b)ˣ (HeightOneSpectrum (𝓞 F)) fun v => (QuatV a b v)ˣ where
  p := unitAtQ a b
  s := singleQUnit a b
  K := lamLocUnits a b
  p_s_self := unitAtQ_singleQUnit_self a b
  p_s_of_ne v w h x := unitAtQ_singleQUnit_of_ne a b v w h x
  isOpen_K := isOpen_lamLocUnits a b
  one_mem_K := one_mem_lamLocUnits a b

theorem chartBox_empty_quatChart :
    (quatChart a b).chartBox ∅ (fun v => (quatChart a b).K v) = lamHatUnits a b := by
  ext u
  simp only [ChartData.chartBox, Finset.notMem_empty, ite_false, mem_ofPred_eq, mem_lamHatUnits_iff]
  rfl

/-! ### Integral $a, b$: $\Lambda_v$ is a ring and $\Lambda_v^\times = \{\operatorname{nrd}\in\mathcal O_v^\times\}$ -/

section Integral

variable {a b}
variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

include ha hb

theorem mul_mem_lamLoc {v : HeightOneSpectrum (𝓞 F)} {x y : QuatV a b v} (hx : x ∈ lamLoc a b v)
    (hy : y ∈ lamLoc a b v) : x * y ∈ lamLoc a b v := by
  have hav : algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ha v)
  have hbv : algebraMap F (v.adicCompletion F) b ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hb v)
  set O := (v.adicCompletionIntegers F).toSubring
  let φ : ℍ[O, ⟨_, hav⟩, 0, ⟨_, hbv⟩] →+* QuatV a b v :=
    QuaternionAlgebra.mapRingHom O.subtype (c₁ := ⟨_, hav⟩) (c₂ := 0) (c₃ := ⟨_, hbv⟩)
      (d₁ := algebraMap F (v.adicCompletion F) a) (d₂ := 0) (d₃ := algebraMap F (v.adicCompletion F) b)
      rfl rfl rfl
  have hφ : ∀ z : QuatV a b v, z ∈ lamLoc a b v → ∃ z', φ z' = z := by
    rintro z ⟨z0, z1, z2, z3⟩
    exact ⟨⟨⟨_, z0⟩, ⟨_, z1⟩, ⟨_, z2⟩, ⟨_, z3⟩⟩, rfl⟩
  obtain ⟨x', rfl⟩ := hφ x hx
  obtain ⟨y', rfl⟩ := hφ y hy
  rw [← map_mul]
  exact ⟨(x' * y').re.2, (x' * y').imI.2, (x' * y').imJ.2, (x' * y').imK.2⟩

theorem nrdLoc_mem_of_mem_lamLoc {v : HeightOneSpectrum (𝓞 F)} {x : QuatV a b v} (hx : x ∈ lamLoc a b v) :
    nrdLoc _ _ x ∈ v.adicCompletionIntegers F := by
  have hav : algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ha v)
  have hbv : algebraMap F (v.adicCompletion F) b ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hb v)
  set O := (v.adicCompletionIntegers F).toSubring
  let φ : ℍ[O, ⟨_, hav⟩, 0, ⟨_, hbv⟩] →+* QuatV a b v :=
    QuaternionAlgebra.mapRingHom O.subtype (c₁ := ⟨_, hav⟩) (c₂ := 0) (c₃ := ⟨_, hbv⟩)
      (d₁ := algebraMap F (v.adicCompletion F) a) (d₂ := 0) (d₃ := algebraMap F (v.adicCompletion F) b)
      rfl rfl rfl
  obtain ⟨x0, x1, x2, x3⟩ := hx
  set z : ℍ[O, ⟨_, hav⟩, 0, ⟨_, hbv⟩] := ⟨⟨_, x0⟩, ⟨_, x1⟩, ⟨_, x2⟩, ⟨_, x3⟩⟩ with hz
  have hxz : φ z = x := rfl
  have hstar : φ (star z) = star x := by
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [φ, z, QuaternionAlgebra.mapRingHom]
  have hxx : x * star x = φ (z * star z) := by rw [map_mul, hxz, hstar]
  rw [nrdLoc, hxx]
  exact (z * star z).re.2

theorem lamLocUnits_mul_mem {v : HeightOneSpectrum (𝓞 F)} {x y : (QuatV a b v)ˣ} (hx : x ∈ lamLocUnits a b v)
    (hy : y ∈ lamLocUnits a b v) : x * y ∈ lamLocUnits a b v := by
  refine ⟨mul_mem_lamLoc ha hb hx.1 hy.1, ?_⟩
  rw [mul_inv_rev, Units.val_mul]
  exact mul_mem_lamLoc ha hb hy.2 hx.2

/-- **$\hat\Lambda^\times$ is a subgroup** ($a, b$ integral). -/
def lamHatUnitsSub : Subgroup (QuatFin a b)ˣ where
  carrier := lamHatUnits a b
  one_mem' := one_mem_lamHatUnits a b
  mul_mem' {x y} hx hy := by
    rw [mem_lamHatUnits_iff] at hx hy ⊢
    intro v; rw [map_mul]; exact lamLocUnits_mul_mem ha hb (hx v) (hy v)
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

/-- **$\Lambda_v^\times = \{x\in\Lambda_v : \operatorname{nrd}(x)\in\mathcal O_v^\times\}$** ($a, b$ integral; the inverse is
$\operatorname{nrd}(x)^{-1}\bar x$). -/
theorem mem_lamLocUnits_iff {v : HeightOneSpectrum (𝓞 F)} (u : (QuatV a b v)ˣ) :
    u ∈ lamLocUnits a b v ↔ (u : QuatV a b v) ∈ lamLoc a b v ∧ Valued.v (nrdLoc _ _ (u : QuatV a b v)) = 1 := by
  have hmul : nrdLoc _ _ (u : QuatV a b v) * nrdLoc _ _ ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) = 1 := by
    rw [← nrdLoc_mul, Units.mul_inv, nrdLoc_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have n1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (nrdLoc_mem_of_mem_lamLoc ha hb h1)
    have n2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (nrdLoc_mem_of_mem_lamLoc ha hb h2)
    have hv := congrArg Valued.v hmul
    rw [map_mul, map_one] at hv
    refine le_antisymm n1 ?_
    by_contra hlt
    push Not at hlt
    have : Valued.v (nrdLoc _ _ (u : QuatV a b v)) *
        Valued.v (nrdLoc _ _ ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v)) < 1 := mul_lt_one_of_lt_of_le hlt n2
    rw [hv] at this
    exact lt_irrefl _ this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    set n := nrdLoc _ _ (u : QuatV a b v)
    have hn0 : n ≠ 0 := (isUnit_iff_nrdLoc_ne_zero _ _ _).mp u.isUnit
    have hinv : ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) = n⁻¹ • star (u : QuatV a b v) := by
      refine (Units.inv_eq_of_mul_eq_one_right ?_)
      rw [mul_smul_comm, mul_star_eq_nrdLoc, coe_smul_coe, inv_mul_cancel₀ hn0, QuaternionAlgebra.coe_one]
    have hn' : n⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
    obtain ⟨x0, x1, x2, x3⟩ := h1
    rw [hinv]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
        QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
        QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, smul_eq_mul]
    · exact mul_mem hn' (by simpa using x0)
    · exact mul_mem hn' (neg_mem x1)
    · exact mul_mem hn' (neg_mem x2)
    · exact mul_mem hn' (neg_mem x3)

end Integral

end

end QuadFormsKB.Tamagawa.Measure.Weil
