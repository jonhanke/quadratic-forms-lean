import QuadFormsKB.Tamagawa.Measure.LerayOrbital
import QuadFormsKB.Tamagawa.Measure.Weil.OrbitFibration
import QuadFormsKB.Tamagawa.Measure.Weil.ReflectionSection
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Lattices MeasureTheory NumberField IsDedekindDomain Matrix

noncomputable section
namespace QuadFormsKB.Tamagawa.Measure.FibreO
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (Q : QuadForm F N)
local notation "Fv" => v.adicCompletion F

/-- The pair (g, g⁻¹) of matrices. -/
def orthPair (g : orthGroup Q Fv) : Matrix (Fin N) (Fin N) Fv × Matrix (Fin N) (Fin N) Fv :=
  ((g : GL (Fin N) Fv).val, ((g⁻¹ : orthGroup Q Fv) : GL (Fin N) Fv).val)

theorem isEmbedding_orthPair : Topology.IsEmbedding (orthPair v Q) := by
  have h1 : Topology.IsEmbedding (fun g : orthGroup Q Fv => Units.embedProduct (Matrix (Fin N) (Fin N) Fv) (g : GL (Fin N) Fv)) :=
    (Units.isClosedEmbedding_embedProduct.isEmbedding).comp Topology.IsEmbedding.subtypeVal
  have h2 : Topology.IsEmbedding (Prod.map (id : Matrix (Fin N) (Fin N) Fv → _) (MulOpposite.unop : (Matrix (Fin N) (Fin N) Fv)ᵐᵒᵖ → _)) :=
    Topology.IsEmbedding.prodMap Topology.IsEmbedding.id MulOpposite.opHomeomorph.symm.isEmbedding
  exact h2.comp h1

/-- Measurability criterion into `O(V)(F_v)`: measurable matrix and inverse matrix. -/
theorem measurable_of_pair {α : Type*} [MeasurableSpace α] {f : α → orthGroup Q Fv}
    (h1 : Measurable fun a => ((f a : orthGroup Q Fv) : GL (Fin N) Fv).val)
    (h2 : Measurable fun a => (((f a)⁻¹ : orthGroup Q Fv) : GL (Fin N) Fv).val) : Measurable f := by
  have hind := (isEmbedding_orthPair v Q).isInducing
  have hb : borel (orthGroup Q Fv) =
      MeasurableSpace.comap (orthPair v Q) (borel (Matrix (Fin N) (Fin N) Fv × Matrix (Fin N) (Fin N) Fv)) := by
    have := @borel_comap _ _ (orthPair v Q) (inferInstance : TopologicalSpace (Matrix (Fin N) (Fin N) Fv × Matrix (Fin N) (Fin N) Fv))
    rw [← hind.eq_induced] at this
    exact this
  have hbs : borel (Matrix (Fin N) (Fin N) Fv × Matrix (Fin N) (Fin N) Fv) = Prod.instMeasurableSpace :=
    (inferInstance : BorelSpace (Matrix (Fin N) (Fin N) Fv × Matrix (Fin N) (Fin N) Fv)).measurable_eq.symm
  have hpair : Measurable fun a => orthPair v Q (f a) := h1.prodMk h2
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap f (borel (orthGroup Q Fv)) ≤ _
  rw [hb, hbs, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 hpair


/-- The Hessian over `F_v`. -/
abbrev hessV : Matrix (Fin N) (Fin N) Fv := Q.hessian.map (algebraMap F Fv)

theorem det_hessV_ne_zero (hQ : Q.Nondegenerate) : (hessV v Q).det ≠ 0 := by
  unfold hessV
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 hQ

theorem hessV_transpose : (hessV v Q)ᵀ = hessV v Q := by
  unfold hessV
  ext i j
  simp [QuadForm.hessian, Matrix.transpose_apply, add_comm]


theorem mem_orthGroup_iff' (g : GL (Fin N) Fv) :
    g ∈ orthGroup Q Fv ↔ (g : GL (Fin N) Fv).valᵀ * hessV v Q * g.val = hessV v Q := Iff.rfl

theorem det_ne_zero_of_orth (hQ : Q.Nondegenerate) {A : Matrix (Fin N) (Fin N) Fv}
    (hA : Aᵀ * hessV v Q * A = hessV v Q) : A.det ≠ 0 := by
  have h := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hd := det_hessV_ne_zero v Q hQ
  intro h0
  rw [h0, mul_zero] at h
  exact hd h.symm

/-- The element of `O(V)(F_v)` with matrix `A`. -/
def mkOrth (hQ : Q.Nondegenerate) (A : Matrix (Fin N) (Fin N) Fv) (hA : Aᵀ * hessV v Q * A = hessV v Q) :
    orthGroup Q Fv :=
  ⟨Matrix.nonsingInvUnit A (isUnit_iff_ne_zero.2 (det_ne_zero_of_orth v Q hQ hA)), hA⟩

theorem val_mkOrth (hQ : Q.Nondegenerate) (A : Matrix (Fin N) (Fin N) Fv) (hA : Aᵀ * hessV v Q * A = hessV v Q) :
    ((mkOrth v Q hQ A hA : orthGroup Q Fv) : GL (Fin N) Fv).val = A := rfl

theorem inv_val_eq (hQ : Q.Nondegenerate) (g : orthGroup Q Fv) :
    (((g⁻¹ : orthGroup Q Fv)) : GL (Fin N) Fv).val = (hessV v Q)⁻¹ * (g : GL (Fin N) Fv).valᵀ * hessV v Q := by
  have hd := det_hessV_ne_zero v Q hQ
  have hg : (g : GL (Fin N) Fv).valᵀ * hessV v Q * (g : GL (Fin N) Fv).val = hessV v Q := g.2
  set B := (hessV v Q)⁻¹ * (g : GL (Fin N) Fv).valᵀ * hessV v Q with hB
  have hBg : B * (g : GL (Fin N) Fv).val = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g : GL (Fin N) Fv).valᵀ, hg]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)
  have hgB : (g : GL (Fin N) Fv).val * B = 1 := mul_eq_one_comm.1 hBg
  have hinv : (((g⁻¹ : orthGroup Q Fv)) : GL (Fin N) Fv).val * (g : GL (Fin N) Fv).val = 1 := by
    rw [Subgroup.coe_inv, Units.inv_mul]  
  calc (((g⁻¹ : orthGroup Q Fv)) : GL (Fin N) Fv).val
      = (((g⁻¹ : orthGroup Q Fv)) : GL (Fin N) Fv).val * ((g : GL (Fin N) Fv).val * B) := by rw [hgB, Matrix.mul_one]
    _ = B := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

section Meas

theorem measurable_of_val (hQ : Q.Nondegenerate) {α : Type*} [MeasurableSpace α] {f : α → orthGroup Q Fv}
    (h : Measurable fun a => ((f a : orthGroup Q Fv) : GL (Fin N) Fv).val) : Measurable f := by
  refine measurable_of_pair v Q h ?_
  simp_rw [inv_val_eq v Q hQ]
  have ht : Measurable fun a => ((f a : orthGroup Q Fv) : GL (Fin N) Fv).valᵀ :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      (measurable_pi_apply i).comp ((measurable_pi_apply j).comp h)
  exact Weil.measurable_matMul (Weil.measurable_matMul measurable_const ht) measurable_const

end Meas


/-! ### The quadric `{Q = m}` as a homogeneous space of `O(V)(F_v)` -/

section Sphere

variable {n : ℕ} (Q : QuadForm F (n + 1)) (mF : F) (Q' : QuadForm F n)

/-- The quadric `{x : Q(x) = m}` in `F_v^{n+1}`. -/
def sphereSet : Set (Fin (n + 1) → Fv) := {x | Q.evalIn Fv x = algebraMap F Fv mF}

theorem qH_eq (x : Fin (n + 1) → Fv) : Weil.qH (hessV v Q) x = 2 * Q.evalIn Fv x :=
  (Lattices.two_mul_evalIn (Q := Q) x).symm

theorem evalIn_e₀ (hE : Q = splitForm mF Q') : Q.evalIn Fv (e₀ : Fin (n + 1) → Fv) = algebraMap F Fv mF := by
  subst hE; exact evalIn_splitForm_e₀ _ _ _

theorem mem_sphereSet_iff (hE : Q = splitForm mF Q') (x : Fin (n + 1) → Fv) :
    x ∈ sphereSet v Q mF ↔ Weil.qH (hessV v Q) x = Weil.qH (hessV v Q) (e₀ : Fin (n + 1) → Fv) := by
  rw [qH_eq, qH_eq, evalIn_e₀ v Q mF Q' hE]
  exact ⟨fun h => by rw [show Q.evalIn Fv x = _ from h], fun h => mul_left_cancel₀ two_ne_zero h⟩

theorem e₀_mem_sphereSet (hE : Q = splitForm mF Q') : (e₀ : Fin (n + 1) → Fv) ∈ sphereSet v Q mF :=
  evalIn_e₀ v Q mF Q' hE

theorem orth_qH (g : orthGroup Q Fv) (x : Fin (n + 1) → Fv) :
    Weil.qH (hessV v Q) ((g : GL (Fin (n + 1)) Fv).val *ᵥ x) = Weil.qH (hessV v Q) x := by
  unfold Weil.qH
  set M := (g : GL (Fin (n + 1)) Fv).val
  set H := hessV v Q
  have hg : Mᵀ * H * M = H := g.2
  have key : (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x)) = x ⬝ᵥ (Mᵀ *ᵥ (H *ᵥ (M *ᵥ x))) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [key, mulVec_mulVec, mulVec_mulVec, hg]

theorem orth_evalIn (g : orthGroup Q Fv) (x : Fin (n + 1) → Fv) :
    Q.evalIn Fv ((g : GL (Fin (n + 1)) Fv).val *ᵥ x) = Q.evalIn Fv x := by
  have h := orth_qH v Q g x
  rw [qH_eq, qH_eq] at h
  exact mul_left_cancel₀ two_ne_zero h

instance : MulAction (orthGroup Q Fv) (sphereSet v Q mF) where
  smul g x := ⟨(g : GL (Fin (n + 1)) Fv).val *ᵥ x.1, by
    show Q.evalIn Fv _ = _
    rw [orth_evalIn v Q g x.1]; exact x.2⟩
  one_smul x := Subtype.ext (by
    show ((1 : orthGroup Q Fv) : GL (Fin (n + 1)) Fv).val *ᵥ x.1 = x.1
    simp)
  mul_smul a b x := Subtype.ext (by
    show ((a * b : orthGroup Q Fv) : GL (Fin (n + 1)) Fv).val *ᵥ x.1 =
      (a : GL (Fin (n + 1)) Fv).val *ᵥ ((b : GL (Fin (n + 1)) Fv).val *ᵥ x.1)
    simp [mulVec_mulVec])

theorem smul_val (g : orthGroup Q Fv) (x : sphereSet v Q mF) :
    ((g • x : sphereSet v Q mF) : Fin (n + 1) → Fv) = (g : GL (Fin (n + 1)) Fv).val *ᵥ (x : Fin (n + 1) → Fv) := rfl

theorem nondegenerate_split (hE : Q = splitForm mF Q') (hm : mF ≠ 0) (hQ' : Q'.Nondegenerate) : Q.Nondegenerate := by
  subst hE
  rw [QuadForm.Nondegenerate, det_hessian_splitForm]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'

theorem qH_e₀_ne_zero (hE : Q = splitForm mF Q') (hm : mF ≠ 0) :
    Weil.qH (hessV v Q) (e₀ : Fin (n + 1) → Fv) ≠ 0 := by
  rw [qH_eq, evalIn_e₀ v Q mF Q' hE]
  exact mul_ne_zero two_ne_zero ((map_ne_zero _).2 hm)

section Section

variable (hE : Q = splitForm mF Q') (hm : mF ≠ 0) (hQ' : Q'.Nondegenerate) (hn : 1 ≤ n)
include hE hm hQ' hn

/-- The data of the section: base point `e₀` and an anisotropic vector orthogonal to it. -/
def sphereData : Weil.SphereData (hessV v Q) :=
  { x₀ := e₀
    w := (Weil.exists_orth_anisotropic (hessV_transpose v Q) two_ne_zero
      (det_hessV_ne_zero v Q (nondegenerate_split Q mF Q' hE hm hQ')) (by omega)
      (qH_e₀_ne_zero v Q mF Q' hE hm)).choose
    hx₀ := qH_e₀_ne_zero v Q mF Q' hE hm
    hw := (Weil.exists_orth_anisotropic (hessV_transpose v Q) two_ne_zero
      (det_hessV_ne_zero v Q (nondegenerate_split Q mF Q' hE hm hQ')) (by omega)
      (qH_e₀_ne_zero v Q mF Q' hE hm)).choose_spec.1
    horth := (Weil.exists_orth_anisotropic (hessV_transpose v Q) two_ne_zero
      (det_hessV_ne_zero v Q (nondegenerate_split Q mF Q' hE hm hQ')) (by omega)
      (qH_e₀_ne_zero v Q mF Q' hE hm)).choose_spec.2 }

theorem sphereSec_orth {x : Fin (n + 1) → Fv} (hx : x ∈ sphereSet v Q mF) :
    (Weil.sphereSec (sphereData v Q mF Q' hE hm hQ' hn) x)ᵀ * hessV v Q *
        Weil.sphereSec (sphereData v Q mF Q' hE hm hQ' hn) x = hessV v Q :=
  (Weil.sphereSec_mem (hessV_transpose v Q) two_ne_zero (sphereData v Q mF Q' hE hm hQ' hn)
    ((mem_sphereSet_iff v Q mF Q' hE x).1 hx)).1

/-- The section `x ↦ s(x)` as an element of `O(V)(F_v)` (on the quadric). -/
def secOrth (x : sphereSet v Q mF) : orthGroup Q Fv :=
  mkOrth v Q (nondegenerate_split Q mF Q' hE hm hQ') (Weil.sphereSec (sphereData v Q mF Q' hE hm hQ' hn) x.1)
    (sphereSec_orth v Q mF Q' hE hm hQ' hn x.2)

/-- **The orbit section** of `O(V)(F_v)` acting on the quadric `{Q = m}`: base point `e₀`, section `sphereSec`. -/
def orbitSection : Weil.OrbitSection (orthGroup Q Fv) (sphereSet v Q mF) where
  base := ⟨e₀, e₀_mem_sphereSet v Q mF Q' hE⟩
  sec := secOrth v Q mF Q' hE hm hQ' hn
  sec_smul x := Subtype.ext (by
    show (Weil.sphereSec (sphereData v Q mF Q' hE hm hQ' hn) x.1) *ᵥ (e₀ : Fin (n + 1) → Fv) = x.1
    exact Weil.sphereSec_mulVec (hessV_transpose v Q) two_ne_zero (sphereData v Q mF Q' hE hm hQ' hn)
      ((mem_sphereSet_iff v Q mF Q' hE x.1).1 x.2))
  measurable_sec := by
    refine measurable_of_val v Q (nondegenerate_split Q mF Q' hE hm hQ') ?_
    exact (Weil.measurable_sphereSec (sphereData v Q mF Q' hE hm hQ' hn)).comp measurable_subtype_coe
  measurable_orbit := by
    refine Continuous.measurable ?_
    refine Continuous.subtype_mk ?_ _
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const

end Section

section Stab

/-- The corner embedding of matrices `A ↦ diag(1, A)`. -/
def cornerΦ : Matrix (Fin n) (Fin n) Fv → Matrix (Fin (n + 1)) (Fin (n + 1)) Fv := cornerMat 1

theorem continuous_cornerΦ : Continuous (cornerΦ v (n := n)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cornerΦ, cornerMat] <;> fun_prop

theorem isEmbedding_cornerΦ : Topology.IsEmbedding (cornerΦ v (n := n)) := by
  refine Function.LeftInverse.isEmbedding (f := fun A => A.submatrix Fin.succ Fin.succ) ?_
    (continuous_id.matrix_submatrix _ _) (continuous_cornerΦ v)
  intro A
  ext i j
  simp [cornerΦ]

theorem mem_orth_of_eq (hE : Q = splitForm mF Q') {g : GL (Fin (n + 1)) Fv} (hg : g ∈ orthGroup (splitForm mF Q') Fv) :
    g ∈ orthGroup Q Fv := by subst hE; exact hg

theorem mem_orth_of_eq' (hE : Q = splitForm mF Q') {g : GL (Fin (n + 1)) Fv} (hg : g ∈ orthGroup Q Fv) :
    g ∈ orthGroup (splitForm mF Q') Fv := by subst hE; exact hg

theorem orthGroup_le_of_eq (hE : Q = splitForm mF Q') : orthGroup (splitForm mF Q') Fv ≤ orthGroup Q Fv := by
  subst hE; exact le_rfl

/-- **The embedding `O(Q') → O(Q)`, `h ↦ diag(1, h)`.** -/
def iota (hE : Q = splitForm mF Q') : orthGroup Q' Fv →* orthGroup Q Fv :=
  (Subgroup.inclusion (orthGroup_le_of_eq v Q mF Q' hE)).comp (orthEmb mF Q' Fv)

theorem iota_coe (hE : Q = splitForm mF Q') (h : orthGroup Q' Fv) :
    ((iota v Q mF Q' hE h : orthGroup Q Fv) : GL (Fin (n + 1)) Fv) = (orthEmb mF Q' Fv h : GL (Fin (n + 1)) Fv) := by
  simp [iota]

theorem iota_val (hE : Q = splitForm mF Q') (h : orthGroup Q' Fv) :
    ((iota v Q mF Q' hE h : orthGroup Q Fv) : GL (Fin (n + 1)) Fv).val = cornerMat 1 (h : GL (Fin n) Fv).val := rfl

theorem iota_mulVec_e₀ (hE : Q = splitForm mF Q') (h : orthGroup Q' Fv) :
    ((iota v Q mF Q' hE h : orthGroup Q Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
  rw [iota_val]
  rw [cornerMat_mulVec, one_mul, mulVec_zero]

theorem two_mul_ne_zero_Fv (hm : mF ≠ 0) : algebraMap F Fv (2 * mF) ≠ 0 := by
  rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm

theorem exists_iota_eq (hE : Q = splitForm mF Q') (hm : mF ≠ 0) (g : orthGroup Q Fv)
    (hg : (g : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀) : ∃ h, iota v Q mF Q' hE h = g := by
  set γ : orthGroup (splitForm mF Q') Fv := ⟨(g : GL (Fin (n + 1)) Fv), mem_orth_of_eq' v Q mF Q' hE g.2⟩ with hγ
  have hγe : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := hg
  obtain ⟨h, hh⟩ := exists_orthEmb_eq mF Q' Fv (two_mul_ne_zero_Fv v mF hm) γ hγe
  refine ⟨h, Subtype.ext ?_⟩
  have := congrArg (fun x : orthGroup (splitForm mF Q') Fv => (x : GL (Fin (n + 1)) Fv)) hh
  rw [iota_coe]
  exact this

theorem orthPair_iota (hE : Q = splitForm mF Q') (h : orthGroup Q' Fv) :
    orthPair v Q (iota v Q mF Q' hE h) = Prod.map (cornerΦ v) (cornerΦ v) (orthPair v Q' h) := by
  refine Prod.ext (by simp [orthPair, cornerΦ, iota_val]) ?_
  show ((((iota v Q mF Q' hE h)⁻¹ : orthGroup Q Fv)) : GL (Fin (n + 1)) Fv).val =
    cornerMat 1 (((h⁻¹ : orthGroup Q' Fv)) : GL (Fin n) Fv).val
  rw [← map_inv]
  rfl

theorem isEmbedding_iota (hE : Q = splitForm mF Q') : Topology.IsEmbedding (iota v Q mF Q' hE) := by
  have hdiag : orthPair v Q ∘ iota v Q mF Q' hE = Prod.map (cornerΦ v) (cornerΦ v) ∘ orthPair v Q' := by
    funext h; exact orthPair_iota v Q mF Q' hE h
  have hc : Continuous (iota v Q mF Q' hE) := by
    refine (isEmbedding_orthPair v Q).isInducing.continuous_iff.2 ?_
    rw [hdiag]
    exact ((continuous_cornerΦ v).prodMap (continuous_cornerΦ v)).comp (isEmbedding_orthPair v Q').continuous
  refine Topology.IsEmbedding.of_comp hc (isEmbedding_orthPair v Q).continuous ?_
  rw [hdiag]
  exact ((isEmbedding_cornerΦ v).prodMap (isEmbedding_cornerΦ v)).comp (isEmbedding_orthPair v Q')

end Stab

/-- Measurable equivalence between equal subsets. -/
def setCongrM {α : Type*} [MeasurableSpace α] {s t : Set α} (h : s = t) : s ≃ᵐ t := by
  subst h; exact MeasurableEquiv.refl _

theorem setCongrM_val {α : Type*} [MeasurableSpace α] {s t : Set α} (h : s = t) (x : s) :
    ((setCongrM h x : t) : α) = x := by
  subst h; rfl

section StabEquiv

variable (hE : Q = splitForm mF Q') (hm : mF ≠ 0) (hQ' : Q'.Nondegenerate) (hn : 1 ≤ n)
include hE hm hQ' hn

theorem mem_stab_iff (g : orthGroup Q Fv) :
    g ∈ (orbitSection v Q mF Q' hE hm hQ' hn).stab ↔
      (g : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
  rw [Weil.OrbitSection.mem_stab_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem range_iota_eq : Set.range (iota v Q mF Q' hE) =
    ((orbitSection v Q mF Q' hE hm hQ' hn).stab : Set (orthGroup Q Fv)) := by
  ext g
  rw [SetLike.mem_coe, mem_stab_iff v Q mF Q' hE hm hQ' hn]
  exact ⟨fun ⟨h, hh⟩ => hh ▸ iota_mulVec_e₀ v Q mF Q' hE h, fun hg => exists_iota_eq v Q mF Q' hE hm g hg⟩

theorem isClosedEmbedding_iota : Topology.IsClosedEmbedding (iota v Q mF Q' hE) := by
  refine ⟨isEmbedding_iota v Q mF Q' hE, ?_⟩
  rw [range_iota_eq v Q mF Q' hE hm hQ' hn]
  have : ((orbitSection v Q mF Q' hE hm hQ' hn).stab : Set (orthGroup Q Fv)) =
      {g : orthGroup Q Fv | (g : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀} := by
    ext g; exact mem_stab_iff v Q mF Q' hE hm hQ' hn g
  rw [this]
  exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const) continuous_const

/-- **`O(Q') ≅ Stab(e₀)`** as a measurable equivalence, `h ↦ diag(1, h)`. -/
def stabEquiv : orthGroup Q' Fv ≃ᵐ (orbitSection v Q mF Q' hE hm hQ' hn).stab :=
  ((isClosedEmbedding_iota v Q mF Q' hE hm hQ' hn).measurableEmbedding.equivRange).trans
    (setCongrM (range_iota_eq v Q mF Q' hE hm hQ' hn))

theorem stabEquiv_val (h : orthGroup Q' Fv) :
    ((stabEquiv v Q mF Q' hE hm hQ' hn h : (orbitSection v Q mF Q' hE hm hQ' hn).stab) : orthGroup Q Fv) =
      iota v Q mF Q' hE h := by
  unfold stabEquiv
  rw [MeasurableEquiv.trans_apply, setCongrM_val, MeasurableEmbedding.equivRange_apply]

end StabEquiv

section Fibre

variable (hE : Q = splitForm mF Q') (hm : mF ≠ 0) (hQ' : Q'.Nondegenerate) (hn : 1 ≤ n)
include hE hm hQ' hn

theorem smul_base_val (g : orthGroup Q Fv) :
    (((g • (orbitSection v Q mF Q' hE hm hQ' hn).base : sphereSet v Q mF)) : Fin (n + 1) → Fv) =
      (g : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) := rfl

/-- `orb (x, h) = s(x) · diag(1, h)`. -/
def orb (p : sphereSet v Q mF × orthGroup Q' Fv) : orthGroup Q Fv :=
  secOrth v Q mF Q' hE hm hQ' hn p.1 * iota v Q mF Q' hE p.2

theorem orb_eq : orb v Q mF Q' hE hm hQ' hn =
    (orbitSection v Q mF Q' hE hm hQ' hn).ofCoord ∘ Prod.map id (stabEquiv v Q mF Q' hE hm hQ' hn) := by
  funext p
  show _ = (orbitSection v Q mF Q' hE hm hQ' hn).sec p.1 *
    ((stabEquiv v Q mF Q' hE hm hQ' hn p.2 : (orbitSection v Q mF Q' hE hm hQ' hn).stab) : orthGroup Q Fv)
  rw [stabEquiv_val]
  rfl

theorem measurable_orb : Measurable (orb v Q mF Q' hE hm hQ' hn) := by
  rw [orb_eq]
  exact (orbitSection v Q mF Q' hE hm hQ' hn).measurable_ofCoord.comp
    (measurable_id.prodMap (stabEquiv v Q mF Q' hE hm hQ' hn).measurable)

/-- The pushforward of a left-invariant measure on `O(Q')` to the stabilizer is left-invariant. -/
theorem isMulLeftInvariant_map_stabEquiv (μ' : Measure (orthGroup Q' Fv)) [μ'.IsMulLeftInvariant] :
    (μ'.map (stabEquiv v Q mF Q' hE hm hQ' hn)).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨h₁, rfl⟩ := (stabEquiv v Q mF Q' hE hm hQ' hn).surjective g
  have hmul : ∀ h, (stabEquiv v Q mF Q' hE hm hQ' hn) (h₁ * h) =
      (stabEquiv v Q mF Q' hE hm hQ' hn h₁) * (stabEquiv v Q mF Q' hE hm hQ' hn h) := by
    intro h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, stabEquiv_val, map_mul]
  have e1 : (fun x => (stabEquiv v Q mF Q' hE hm hQ' hn h₁) * x) ∘ (stabEquiv v Q mF Q' hE hm hQ' hn) =
      (stabEquiv v Q mF Q' hE hm hQ' hn) ∘ (fun h => h₁ * h) := by
    funext h; exact (hmul h).symm
  have hm1 : Measurable (fun x : (orbitSection v Q mF Q' hE hm hQ' hn).stab =>
      (stabEquiv v Q mF Q' hE hm hQ' hn h₁) * x) := measurable_const_mul _
  rw [Measure.map_map hm1 (stabEquiv v Q mF Q' hE hm hQ' hn).measurable, e1,
    ← Measure.map_map (stabEquiv v Q mF Q' hE hm hQ' hn).measurable (measurable_const_mul h₁),
    map_mul_left_eq_self]

/-- **The group-level fibre form, constant undetermined** (Weil 1982, §2.4 Thm 2.4.3 [unverified page]): for a
`O(V)(F_v)`-invariant σ-finite measure `ν` on the quadric, a Haar measure `μ'` on `O(Q')` and a Haar measure `μ_G`
on `O(V)(F_v)`, `orb_*(ν × μ') = c · μ_G`, `c = orb_*(ν × μ')(U) / μ_G(U)`. -/
@[kb "weil1982" "§2.4 Thm 2.4.3 p. 25 [unverified]"]
theorem map_orb_eq_smul (ν : Measure (sphereSet v Q mF)) [SigmaFinite ν]
    [SMulInvariantMeasure (orthGroup Q Fv) (sphereSet v Q mF) ν]
    (μ' : Measure (orthGroup Q' Fv)) [SigmaFinite μ'] [μ'.IsMulLeftInvariant]
    (μG : Measure (orthGroup Q Fv)) [SigmaFinite μG] [μG.IsMulLeftInvariant] {U : Set (orthGroup Q Fv)}
    (h0 : μG U ≠ 0) (htop : μG U ≠ ∞) :
    (ν.prod μ').map (orb v Q mF Q' hE hm hQ' hn) =
      (((ν.prod μ').map (orb v Q mF Q' hE hm hQ' hn)) U / μG U) • μG := by
  have hI := isMulLeftInvariant_map_stabEquiv v Q mF Q' hE hm hQ' hn μ'
  have hsf : SigmaFinite (μ'.map (stabEquiv v Q mF Q' hE hm hQ' hn)) :=
    (stabEquiv v Q mF Q' hE hm hQ' hn).symm.symm.sigmaFinite_map
  have hfib : (ν.prod μ').map (orb v Q mF Q' hE hm hQ' hn) =
      (orbitSection v Q mF Q' hE hm hQ' hn).fibMeasure ν (μ'.map (stabEquiv v Q mF Q' hE hm hQ' hn)) := by
    rw [orb_eq, Weil.OrbitSection.fibMeasure,
      ← Measure.map_map (orbitSection v Q mF Q' hE hm hQ' hn).measurable_ofCoord
      (measurable_id.prodMap (stabEquiv v Q mF Q' hE hm hQ' hn).measurable)]
    congr 1
    rw [← Measure.map_prod_map ν μ' measurable_id (stabEquiv v Q mF Q' hE hm hQ' hn).measurable, Measure.map_id]
  rw [hfib]
  exact (orbitSection v Q mF Q' hE hm hQ' hn).fibMeasure_eq_smul ν _ μG h0 htop

/-- The `U`-orbit of the base point `e₀` in the quadric. -/
def orbitSetU (U : Subgroup (orthGroup Q Fv)) : Set (sphereSet v Q mF) :=
  {x | ∃ u ∈ U, u • (orbitSection v Q mF Q' hE hm hQ' hn).base = x}

/-- **The fibre measure of a subgroup**: `orb_*(ν × μ')(U) = ν(U e₀)·μ'(ι⁻¹U)`. -/
theorem map_orb_subgroup (ν : Measure (sphereSet v Q mF)) [SigmaFinite ν]
    (μ' : Measure (orthGroup Q' Fv)) [SigmaFinite μ'] [μ'.IsMulLeftInvariant]
    (U : Subgroup (orthGroup Q Fv)) (hU : MeasurableSet (U : Set (orthGroup Q Fv)))
    (hO : MeasurableSet (orbitSetU v Q mF Q' hE hm hQ' hn U)) :
    ((ν.prod μ').map (orb v Q mF Q' hE hm hQ' hn)) U =
      ν (orbitSetU v Q mF Q' hE hm hQ' hn U) * μ' (iota v Q mF Q' hE ⁻¹' (U : Set (orthGroup Q Fv))) := by
  set S := orbitSection v Q mF Q' hE hm hQ' hn with hS
  have hmeas := measurable_orb v Q mF Q' hE hm hQ' hn
  rw [Measure.map_apply hmeas hU, Measure.prod_apply (hmeas hU)]
  have key : ∀ x, μ' (Prod.mk x ⁻¹' (orb v Q mF Q' hE hm hQ' hn ⁻¹' (U : Set (orthGroup Q Fv)))) =
      (orbitSetU v Q mF Q' hE hm hQ' hn U).indicator (fun _ => μ' (iota v Q mF Q' hE ⁻¹' (U : Set (orthGroup Q Fv)))) x := by
    intro x
    by_cases hx : x ∈ orbitSetU v Q mF Q' hE hm hQ' hn U
    · rw [Set.indicator_of_mem hx]
      obtain ⟨u, hu, hux⟩ := hx
      have hmem : (S.sec x)⁻¹ * u ∈ S.stab := by
        rw [Weil.OrbitSection.mem_stab_iff, mul_smul, hux, inv_smul_eq_iff, S.sec_smul]
      obtain ⟨h₀, hh₀⟩ := exists_iota_eq v Q mF Q' hE hm _ ((mem_stab_iff v Q mF Q' hE hm hQ' hn _).1 hmem)
      have hset : Prod.mk x ⁻¹' (orb v Q mF Q' hE hm hQ' hn ⁻¹' (U : Set (orthGroup Q Fv))) =
          (fun h => h₀⁻¹ * h) ⁻¹' (iota v Q mF Q' hE ⁻¹' (U : Set (orthGroup Q Fv))) := by
        ext h
        simp only [Set.mem_preimage, SetLike.mem_coe, orb, map_mul, map_inv, hh₀]
        show S.sec x * iota v Q mF Q' hE h ∈ U ↔ _
        have : ((S.sec x)⁻¹ * u)⁻¹ * iota v Q mF Q' hE h = u⁻¹ * (S.sec x * iota v Q mF Q' hE h) := by group
        rw [this]
        exact (U.mul_mem_cancel_left (U.inv_mem hu)).symm
      rw [hset, measure_preimage_mul]
    · rw [Set.indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' (orb v Q mF Q' hE hm hQ' hn ⁻¹' (U : Set (orthGroup Q Fv))) = ∅ := by
        ext h
        simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
        intro hh
        apply hx
        refine ⟨_, hh, ?_⟩
        have hfix : iota v Q mF Q' hE h • S.base = S.base :=
          Subtype.ext (iota_mulVec_e₀ v Q mF Q' hE h)
        show (S.sec x * iota v Q mF Q' hE h) • S.base = x
        rw [mul_smul, hfix, S.sec_smul]
      rw [this]; simp
  simp_rw [key]
  rw [lintegral_indicator_const hO, mul_comm]

end Fibre

end Sphere

end QuadFormsKB.Tamagawa.Measure.FibreO
