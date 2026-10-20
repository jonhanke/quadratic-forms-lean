import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# Weil's local measure $\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$ on $\mathbb H_v^\times$

**Generic in the base field.** $K$ is a locally compact, second countable topological field (e.g. $F_v$, $\mathbb R$,
$\mathbb C$), $\mathbb H_K = \mathbb H[K,a,0,b]$ = `QuatLoc a b` with the coordinate topology ($1,i,j,k$), and
$\operatorname{nrd}(x) = \operatorname{re}(x\bar x)$ (`nrdLoc`).

* $\mathbb H_K$ is a locally compact topological ring; **`isUnit_iff_nrdLoc_ne_zero`**; the units are open and
  **`isOpenEmbedding_val_quatLoc`** (inverse $x^{-1} = \operatorname{nrd}(x)^{-1}\bar x$).
* **`distribHaarChar_quatLoc`**: the modulus of left multiplication by $u\in\mathbb H_K^\times$ is
  $\Delta_{\mathbb H}(u) = \Delta_K(\operatorname{nrd}u)^2$, i.e. $|\operatorname{nrd}u|^2$ (via $\det L_u = \operatorname{nrd}(u)^2$
  and `glHaarChar_eq_of_field`). This is Weil's $\|N(x)\|^{r/d}$ for $A = \mathbb H$, $r = 4$, $d = 2$.
* **`omegaQuatLoc ν`** $=\Delta_{\mathbb H}(x)^{-1}dx$ for the coordinate measure $dx = \nu^{\otimes4}$: a Haar measure on
  $\mathbb H_K^\times$ (**`isHaarMeasure_omegaQuatLoc`**) with density $\Delta_K(\operatorname{nrd}x)^{-2}$
  (**`omegaQuatLoc_eq`**): Weil's $\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$ (AAG §2.3 [unverified page]).
-/

open MeasureTheory Topology Set Matrix
open scoped ENNReal NNReal Quaternion Matrix.GLmulVec Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {K : Type*} [Field K] (a b : K)

/-- $\mathbb H[K,a,b] = \mathbb H[K,a,0,b]$ over a field. -/
abbrev QuatLoc := ℍ[K, a, 0, b]

/-- The reduced norm $\operatorname{nrd}(x) = \operatorname{re}(x\bar x) = x_0^2 - ax_1^2 - bx_2^2 + abx_3^2$. -/
def nrdLoc (x : QuatLoc a b) : K := (x * star x).re

theorem nrdLoc_one : nrdLoc a b 1 = 1 := by simp [nrdLoc]

theorem mul_star_eq_nrdLoc (x : QuatLoc a b) : x * star x = (↑(nrdLoc a b x) : QuatLoc a b) :=
  QuaternionAlgebra.mul_star_eq_coe x

theorem star_mul_eq_nrdLoc (x : QuatLoc a b) : star x * x = (↑(nrdLoc a b x) : QuatLoc a b) := by
  rw [QuaternionAlgebra.star_mul_eq_coe, nrdLoc]
  congr 1
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

theorem nrdLoc_mul (x y : QuatLoc a b) : nrdLoc a b (x * y) = nrdLoc a b x * nrdLoc a b y := by
  have h : x * y * star (x * y) = (↑(nrdLoc a b y * nrdLoc a b x) : QuatLoc a b) := by
    rw [star_mul, mul_assoc, ← mul_assoc y, mul_star_eq_nrdLoc a b y, ← mul_assoc,
      ← QuaternionAlgebra.coe_commutes, mul_assoc, mul_star_eq_nrdLoc, ← QuaternionAlgebra.coe_mul]
  rw [nrdLoc, h, QuaternionAlgebra.re_coe, mul_comm]

/-- $\operatorname{nrd}$ as a monoid homomorphism. -/
def nrdLocHom : QuatLoc a b →* K where
  toFun := nrdLoc a b
  map_one' := nrdLoc_one a b
  map_mul' := nrdLoc_mul a b

theorem coe_smul_coe (r s : K) : r • (↑s : QuatLoc a b) = (↑(r * s) : QuatLoc a b) := by
  ext <;> simp

theorem isUnit_iff_nrdLoc_ne_zero (x : QuatLoc a b) : IsUnit x ↔ nrdLoc a b x ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ h0
    have := nrdLoc_mul a b (u : QuatLoc a b) ↑u⁻¹
    rw [Units.mul_inv, nrdLoc_one, h0, zero_mul] at this
    exact zero_ne_one this.symm
  · intro h
    set n := nrdLoc a b x
    refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, mul_star_eq_nrdLoc, coe_smul_coe, inv_mul_cancel₀ h, QuaternionAlgebra.coe_one]
    · rw [smul_mul_assoc, star_mul_eq_nrdLoc, coe_smul_coe, inv_mul_cancel₀ h, QuaternionAlgebra.coe_one]

/-! ### Topology -/

section Top

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The coordinates $1,i,j,k$. -/
abbrev quatLocCoord : QuatLoc a b ≃ₗ[K] (Fin 4 → K) := QuaternionAlgebra.linearEquivTuple a 0 b

instance : TopologicalSpace (QuatLoc a b) := TopologicalSpace.induced (quatLocCoord a b) inferInstance

theorem isInducing_quatLocCoord : IsInducing (quatLocCoord a b) := ⟨rfl⟩

theorem continuous_quatLocCoord : Continuous (quatLocCoord a b) := (isInducing_quatLocCoord a b).continuous

theorem continuous_quatLoc_iff {X : Type*} [TopologicalSpace X] {f : X → QuatLoc a b} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  rw [(isInducing_quatLocCoord a b).continuous_iff, continuous_pi_iff]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3]

theorem continuous_re_loc : Continuous fun x : QuatLoc a b => x.re :=
  (continuous_apply 0).comp (continuous_quatLocCoord a b)
theorem continuous_imI_loc : Continuous fun x : QuatLoc a b => x.imI :=
  (continuous_apply 1).comp (continuous_quatLocCoord a b)
theorem continuous_imJ_loc : Continuous fun x : QuatLoc a b => x.imJ :=
  (continuous_apply 2).comp (continuous_quatLocCoord a b)
theorem continuous_imK_loc : Continuous fun x : QuatLoc a b => x.imK :=
  (continuous_apply 3).comp (continuous_quatLocCoord a b)

theorem continuous_symm_quatLocCoord : Continuous (quatLocCoord a b).symm :=
  (isInducing_quatLocCoord a b).continuous_iff.mpr (by
    have : (quatLocCoord a b) ∘ (quatLocCoord a b).symm = id := funext fun p => (quatLocCoord a b).apply_symm_apply p
    rw [this]; exact continuous_id)

instance : IsTopologicalRing (QuatLoc a b) where
  continuous_add := by
    set P := QuatLoc a b × QuatLoc a b
    have := (continuous_re_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_re_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imI_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imI_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imJ_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imJ_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imK_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imK_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    refine (continuous_quatLoc_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add] <;> fun_prop
  continuous_mul := by
    have := (continuous_re_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_re_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imI_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imI_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imJ_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imJ_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imK_loc a b).comp (continuous_fst (X := QuatLoc a b) (Y := QuatLoc a b))
    have := (continuous_imK_loc a b).comp (continuous_snd (X := QuatLoc a b) (Y := QuatLoc a b))
    refine (continuous_quatLoc_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul] <;> fun_prop
  continuous_neg := by
    have := continuous_re_loc a b
    have := continuous_imI_loc a b
    have := continuous_imJ_loc a b
    have := continuous_imK_loc a b
    refine (continuous_quatLoc_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg,
        QuaternionAlgebra.imK_neg] <;> fun_prop

theorem continuous_star_loc : Continuous (star : QuatLoc a b → QuatLoc a b) := by
  have := continuous_re_loc a b
  have := continuous_imI_loc a b
  have := continuous_imJ_loc a b
  have := continuous_imK_loc a b
  refine (continuous_quatLoc_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star] <;> fun_prop

theorem continuous_nrdLoc : Continuous (nrdLoc a b) :=
  (continuous_re_loc a b).comp (continuous_id.mul (continuous_star_loc a b))

/-- The coordinate map as a continuous linear equivalence. -/
def quatLocCLE : QuatLoc a b ≃L[K] (Fin 4 → K) where
  toLinearEquiv := quatLocCoord a b
  continuous_toFun := continuous_quatLocCoord a b
  continuous_invFun := continuous_symm_quatLocCoord a b

theorem isClosedEmbedding_quatLocCoord : IsClosedEmbedding (quatLocCoord a b) :=
  (quatLocCLE a b).toHomeomorph.isClosedEmbedding

instance [LocallyCompactSpace K] : LocallyCompactSpace (QuatLoc a b) :=
  (isClosedEmbedding_quatLocCoord a b).locallyCompactSpace

instance [T2Space K] : T2Space (QuatLoc a b) := (isClosedEmbedding_quatLocCoord a b).isEmbedding.t2Space

instance [SecondCountableTopology K] : SecondCountableTopology (QuatLoc a b) :=
  (isInducing_quatLocCoord a b).secondCountableTopology

/-- **Units are open, and $x\mapsto x^{-1} = \operatorname{nrd}(x)^{-1}\bar x$ is continuous**, so `Units.val` is an open
embedding. -/
theorem isOpenEmbedding_val_quatLoc [T1Space K] [ContinuousInv₀ K] :
    IsOpenEmbedding (Units.val : (QuatLoc a b)ˣ → QuatLoc a b) := by
  have hrange : range (Units.val : (QuatLoc a b)ˣ → QuatLoc a b) = nrdLoc a b ⁻¹' {0}ᶜ := by
    ext x
    simp only [mem_range, mem_preimage, mem_compl_iff, mem_singleton_iff, ← isUnit_iff_nrdLoc_ne_zero]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
  refine ⟨Units.isEmbedding_val_mk' (f := fun x => (nrdLoc a b x)⁻¹ • star x) ?_ ?_, ?_⟩
  · have hinv : ContinuousOn (fun x => (nrdLoc a b x)⁻¹) {x : QuatLoc a b | IsUnit x} :=
      (continuous_nrdLoc a b).continuousOn.inv₀ fun x hx => (isUnit_iff_nrdLoc_ne_zero a b x).mp hx
    rw [(isInducing_quatLocCoord a b).continuousOn_iff, continuousOn_pi]
    intro i
    simp only [Function.comp_def, map_smul, Pi.smul_apply, smul_eq_mul]
    exact hinv.mul ((continuous_apply i).comp ((continuous_quatLocCoord a b).comp
      (continuous_star_loc a b))).continuousOn
  · intro u
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    have h := (isUnit_iff_nrdLoc_ne_zero a b u).mp u.isUnit
    rw [mul_smul_comm, mul_star_eq_nrdLoc, coe_smul_coe, inv_mul_cancel₀ h, QuaternionAlgebra.coe_one]
  · rw [hrange]
    exact (isOpen_compl_singleton).preimage (continuous_nrdLoc a b)

end Top

/-! ### The modulus $\Delta_{\mathbb H}(u) = \Delta_K(\operatorname{nrd}u)^2$ -/

section Modulus

variable [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

instance measurableSpace_quatLoc : MeasurableSpace (QuatLoc a b) := borel _

instance : BorelSpace (QuatLoc a b) := ⟨rfl⟩

instance measurableSpace_quatLocUnits : MeasurableSpace (QuatLoc a b)ˣ := borel _

instance : BorelSpace (QuatLoc a b)ˣ := ⟨rfl⟩

/-- $\operatorname{nrd}:\mathbb H_K^\times\to K^\times$. -/
def nrdLocUnit : (QuatLoc a b)ˣ →* Kˣ := Units.map (nrdLocHom a b)

@[simp] theorem nrdLocUnit_val (u : (QuatLoc a b)ˣ) : ((nrdLocUnit a b u : Kˣ) : K) = nrdLoc a b u := rfl

/-- $L_u\in\mathrm{GL}_4(K)$, left multiplication in the basis $1,i,j,k$. -/
def quatLocLmat (u : (QuatLoc a b)ˣ) : GL (Fin 4) K :=
  Units.map (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK a 0 b)).toMonoidHom u

theorem quatLocLmat_mulVec (u : (QuatLoc a b)ˣ) (x : QuatLoc a b) :
    (quatLocLmat a b u : Matrix (Fin 4) (Fin 4) K) *ᵥ quatLocCoord a b x = quatLocCoord a b ((u : QuatLoc a b) * x) :=
  Algebra.leftMulMatrix_mulVec_repr _ _ _

theorem quatLocLmat_inv (u : (QuatLoc a b)ˣ) : quatLocLmat a b u⁻¹ = (quatLocLmat a b u)⁻¹ :=
  map_inv (Units.map (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK a 0 b)).toMonoidHom) u

theorem det_quatLocLmat (u : (QuatLoc a b)ˣ) : GeneralLinearGroup.det (quatLocLmat a b u) = nrdLocUnit a b u ^ 2 := by
  refine Units.ext ?_
  change (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK a 0 b) (u : QuatLoc a b)).det = _
  rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix, Units.val_pow_eq_pow_val, nrdLocUnit_val]
  exact QuaternionAlgebra.det_mulLeft a b _

/-- **The modulus of $\mathbb H_K^\times$ acting on $\mathbb H_K$ by left multiplication**:
$\Delta_{\mathbb H}(u) = \Delta_K(\operatorname{nrd}u)^2$ ($=|\operatorname{nrd}u|^2$; Weil's $\|N\|^{r/d}$, $r = 4$, $d = 2$). -/
@[kb "weil1982" "§2.3 [unverified page] (ω_v = ‖N(x)‖_v^{-r/d}dx_v, A = ℍ: r = 4, d = 2)"]
theorem distribHaarChar_quatLoc (u : (QuatLoc a b)ˣ) :
    distribHaarChar (QuatLoc a b) u = distribHaarChar K (nrdLocUnit a b u) ^ 2 := by
  set μ : Measure (Fin 4 → K) := Measure.addHaar
  have : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  set e := (quatLocCLE a b).toHomeomorph.toMeasurableEquiv
  set ν : Measure (QuatLoc a b) := μ.map e.symm
  have : ν.IsAddHaarMeasure := (quatLocCLE a b).symm.isAddHaarMeasure_map μ
  obtain ⟨C⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Fin 4 → K)) := inferInstance
  have hC0 : μ C ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ C.interior_nonempty).ne'
  have hCT : μ C ≠ ⊤ := C.isCompact.measure_lt_top.ne
  have hνs : ∀ T : Set (Fin 4 → K), ν (e ⁻¹' T) = μ T := fun T => by
    rw [MeasurableEquiv.map_apply, ← preimage_comp, show (e ∘ e.symm) = id from funext e.apply_symm_apply,
      preimage_id]
  have hset : e ⁻¹' ((quatLocLmat a b u) • (C : Set (Fin 4 → K))) = u • (e ⁻¹' C) := by
    ext x
    simp only [mem_preimage, mem_smul_set]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨u⁻¹ • x, ?_, smul_inv_smul u x⟩
      change quatLocCoord a b ((u⁻¹ : (QuatLoc a b)ˣ) * x) ∈ (C : Set (Fin 4 → K))
      rw [← quatLocLmat_mulVec]
      change (quatLocLmat a b u⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ e x ∈ (C : Set (Fin 4 → K))
      rw [← hyx, quatLocLmat_inv]
      change ((quatLocLmat a b u)⁻¹ : GL (Fin 4) K) • ((quatLocLmat a b u) • y) ∈ (C : Set (Fin 4 → K))
      rwa [inv_smul_smul]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, hy, (quatLocLmat_mulVec a b u y)⟩
  have h := distribHaarChar_mul μ (quatLocLmat a b u) C
  rw [← hνs (C : Set (Fin 4 → K)), ← hνs ((quatLocLmat a b u) • (C : Set (Fin 4 → K))), hset] at h
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) (s := e ⁻¹' C) (by rwa [hνs]) (by rwa [hνs]) h.symm]
  change glHaarChar K (Fin 4) (quatLocLmat a b u) = _
  rw [glHaarChar_eq_of_field, det_quatLocLmat, map_pow]

end Modulus

/-! ### Weil's $\omega = \|\operatorname{nrd}\|^{-2}dx$ on $\mathbb H_K^\times$ -/

section Omega

variable [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [T1Space K] [ContinuousInv₀ K]

/-- The coordinate measure $dx = \nu(dx_0)\,\nu(dx_1)\,\nu(dx_2)\,\nu(dx_3)$ on $\mathbb H_K$. -/
def quatLocVol (ν : Measure K) : Measure (QuatLoc a b) :=
  (Measure.pi fun _ : Fin 4 => ν).map (quatLocCLE a b).symm

instance (ν : Measure K) [ν.IsAddHaarMeasure] : (quatLocVol a b ν).IsAddHaarMeasure :=
  (quatLocCLE a b).symm.isAddHaarMeasure_map _

instance (ν : Measure K) [ν.IsAddHaarMeasure] : (quatLocVol a b ν).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- **Weil's $\omega = \|\operatorname{nrd}x\|^{-2}dx$ on $\mathbb H_K^\times$** ($dx$ the coordinate measure for $\nu$). -/
def omegaQuatLoc (ν : Measure K) : Measure (QuatLoc a b)ˣ := unitsHaar (QuatLoc a b) (quatLocVol a b ν)

theorem continuous_nrdLocUnit : Continuous (nrdLocUnit a b) :=
  Units.continuous_iff.mpr ⟨(continuous_nrdLoc a b).comp Units.continuous_val,
    (continuous_nrdLoc a b).comp Units.continuous_coe_inv⟩

theorem continuous_distribHaarChar_quatLoc (hΔ : Continuous (distribHaarChar K : Kˣ → ℝ≥0)) :
    Continuous (distribHaarChar (QuatLoc a b) : (QuatLoc a b)ˣ → ℝ≥0) := by
  have : (distribHaarChar (QuatLoc a b) : (QuatLoc a b)ˣ → ℝ≥0) =
      fun u => distribHaarChar K (nrdLocUnit a b u) ^ 2 := funext (distribHaarChar_quatLoc a b)
  rw [this]
  exact (hΔ.comp (continuous_nrdLocUnit a b)).pow 2

/-- **$\omega$ is a Haar measure on $\mathbb H_K^\times$** (given continuity of $|\cdot|_K = \Delta_K$). -/
theorem isHaarMeasure_omegaQuatLoc (hΔ : Continuous (distribHaarChar K : Kˣ → ℝ≥0)) (ν : Measure K)
    [ν.IsAddHaarMeasure] : (omegaQuatLoc a b ν).IsHaarMeasure :=
  isHaarMeasure_unitsHaar (isOpenEmbedding_val_quatLoc a b) (continuous_distribHaarChar_quatLoc a b hΔ) _

/-- **$\omega = \Delta_K(\operatorname{nrd}x)^{-2}\,dx$** on $\mathbb H_K^\times$ (Weil's $\|\operatorname{nrd}x\|_v^{-2}dx_v$). -/
@[kb "weil1982" "§2.3 [unverified page] (ω_v = ‖nrd x‖_v^{-2}dx_v on (ℍ⊗F_v)^×)"]
theorem omegaQuatLoc_eq (ν : Measure K) :
    omegaQuatLoc a b ν = ((quatLocVol a b ν).comap Units.val).withDensity
      fun u => ((distribHaarChar K (nrdLocUnit a b u) : ℝ≥0∞) ^ 2)⁻¹ := by
  rw [omegaQuatLoc, unitsHaar]
  congr 1
  funext u
  rw [distribHaarChar_quatLoc, map_inv, map_inv, inv_pow, ENNReal.coe_inv (pow_ne_zero 2
    (distribHaarChar_ne_zero _)), ENNReal.coe_pow]

end Omega

/-! ### The finite places of a number field -/

section NumberField

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

/-- **Weil's $\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$ on $(\mathbb H[F,a,b]\otimes F_v)^\times$**, $dx_v$ the self-dual
coordinate measure. -/
def omegaQuatV (v : HeightOneSpectrum (𝓞 F)) (a b : F) :
    Measure (QuatLoc (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b))ˣ :=
  omegaQuatLoc _ _ (Analysis.selfDualV v)

instance (v : HeightOneSpectrum (𝓞 F)) (a b : F) : (omegaQuatV v a b).IsHaarMeasure :=
  isHaarMeasure_omegaQuatLoc _ _ (continuous_distribHaarChar_adic v) _

end NumberField

end

end QuadFormsKB.Tamagawa.Measure.Weil
