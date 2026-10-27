import QuadFormsKB.Tamagawa.Measure.Weil.Ideles

/-!
# The unit group $(\mathbb H\otimes\mathbb A)^\times$

* `QuaternionAlgebra.mapRingHom` (generic): a ring homomorphism $f : R\to S$ induces
  $\mathbb H[R,c_1,c_2,c_3]\to\mathbb H[S,d_1,d_2,d_3]$ when $f(c_i) = d_i$.
* `quatDiagRing a b : ℍ[F,a,b] →+* QuatAdele a b`, the diagonal embedding (coordinates `quatDiag`).
* Topology on $\mathbb H[\mathbb A_F,a,b]$ = `QuatAdele a b`: induced by the coordinates $1,i,j,k$ from $\mathbb A_F^4$;
  multiplication is continuous, so the unit group (units topology) is a topological group; it is second countable
  and Borel.
* **`discreteTopology_quatUnitsSub`**: $\mathbb H[F,a,b]^\times$ is discrete in $(\mathbb H\otimes\mathbb A)^\times$.
* `quatNormSqHom` $x\mapsto\|\det L_x\|_{\mathbb A} = \|\operatorname{nrd}x\|_{\mathbb A}^2$, a continuous homomorphism
  (**`continuous_quatNormSqHom`**); $\mathbb H_{\mathbb A}^1$ = `quatOne` = its kernel $=\{x : \|\operatorname{nrd}x\|_{\mathbb A} = 1\}$
  (`mem_quatOne`) is a closed subgroup containing $\mathbb H^\times$ (**`quatUnitsSub_le_quatOne`**, from the product
  formula: $\det L_\xi\in F^\times$ for $\xi\in\mathbb H^\times$).
* Measurable fundamental domains for $\mathbb H^\times$ in $(\mathbb H\otimes\mathbb A)^\times$ and in $\mathbb H_{\mathbb A}^1$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Pointwise Classical Quaternion

namespace QuaternionAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism $f : R\to S$ induces $\mathbb H[R,c_1,c_2,c_3]\to\mathbb H[S,d_1,d_2,d_3]$ when $f(c_i) = d_i$
(coordinatewise). -/
def mapRingHom (f : R →+* S) {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S} (h₁ : f c₁ = d₁) (h₂ : f c₂ = d₂) (h₃ : f c₃ = d₃) :
    ℍ[R,c₁,c₂,c₃] →+* ℍ[S,d₁,d₂,d₃] where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by subst h₁ h₂ h₃; ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

end QuaternionAlgebra

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

variable (a b : F)

/-- The diagonal ring embedding $\mathbb H[F,a,b]\to\mathbb H[\mathbb A_F,a,b]$. -/
def quatDiagRing : ℍ[F,a,b] →+* QuatAdele a b :=
  QuaternionAlgebra.mapRingHom (diagRing F) rfl (map_zero _) rfl

theorem quatDiagRing_apply (ξ : ℍ[F,a,b]) : quatDiagRing a b ξ = quatDiag a b ξ := rfl

/-! ### Topology on $\mathbb H[\mathbb A_F,a,b]$ -/

/-- The coordinates $1,i,j,k$: $\mathbb H[\mathbb A_F,a,b]\to\mathbb A_F^4$. -/
abbrev quatCoord : QuatAdele a b ≃ₗ[Adeles F] (Fin 4 → Adeles F) := QuaternionAlgebra.linearEquivTuple _ _ _

instance : TopologicalSpace (QuatAdele a b) := TopologicalSpace.induced (quatCoord a b) inferInstance

theorem isInducing_quatCoord : IsInducing (quatCoord a b) := ⟨rfl⟩

theorem isEmbedding_quatCoord : IsEmbedding (quatCoord a b) :=
  ⟨isInducing_quatCoord a b, (quatCoord a b).injective⟩

theorem continuous_quatCoord : Continuous (quatCoord a b) := (isInducing_quatCoord a b).continuous

theorem continuous_re : Continuous fun x : QuatAdele a b => x.re := (continuous_apply 0).comp (continuous_quatCoord a b)
theorem continuous_imI : Continuous fun x : QuatAdele a b => x.imI :=
  (continuous_apply 1).comp (continuous_quatCoord a b)
theorem continuous_imJ : Continuous fun x : QuatAdele a b => x.imJ :=
  (continuous_apply 2).comp (continuous_quatCoord a b)
theorem continuous_imK : Continuous fun x : QuatAdele a b => x.imK :=
  (continuous_apply 3).comp (continuous_quatCoord a b)

theorem continuous_quat_iff {X : Type*} [TopologicalSpace X] {f : X → QuatAdele a b} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  refine ⟨fun h => ⟨(continuous_re a b).comp h, (continuous_imI a b).comp h, (continuous_imJ a b).comp h,
    (continuous_imK a b).comp h⟩, fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  rw [(isInducing_quatCoord a b).continuous_iff, continuous_pi_iff]
  intro i; fin_cases i
  exacts [h0, h1, h2, h3]

instance : ContinuousMul (QuatAdele a b) := ⟨by
  set P := QuatAdele a b × QuatAdele a b
  have hf : Continuous fun p : P => p.1.re := (continuous_re a b).comp continuous_fst
  have hs : Continuous fun p : P => p.2.re := (continuous_re a b).comp continuous_snd
  have hf1 : Continuous fun p : P => p.1.imI := (continuous_imI a b).comp continuous_fst
  have hs1 : Continuous fun p : P => p.2.imI := (continuous_imI a b).comp continuous_snd
  have hf2 : Continuous fun p : P => p.1.imJ := (continuous_imJ a b).comp continuous_fst
  have hs2 : Continuous fun p : P => p.2.imJ := (continuous_imJ a b).comp continuous_snd
  have hf3 : Continuous fun p : P => p.1.imK := (continuous_imK a b).comp continuous_fst
  have hs3 : Continuous fun p : P => p.2.imK := (continuous_imK a b).comp continuous_snd
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul] <;> fun_prop⟩

instance : T2Space (QuatAdele a b) := (isEmbedding_quatCoord a b).t2Space

instance : SecondCountableTopology (QuatAdele a b) := (isInducing_quatCoord a b).secondCountableTopology

instance : SecondCountableTopology (QuatAdele a b)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuatAdele a b)).symm.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuatAdele a b)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology

instance measurableSpace_quatUnits : MeasurableSpace (QuatAdele a b)ˣ := borel _

instance : BorelSpace (QuatAdele a b)ˣ := ⟨rfl⟩

/-! ### $\mathbb H^\times$ is discrete in $(\mathbb H\otimes\mathbb A)^\times$ -/

theorem quatCoord_quatDiagRing (ξ : ℍ[F,a,b]) : quatCoord a b (quatDiagRing a b ξ) = diagQuat a b ξ :=
  linearEquivTuple_quatDiag a b ξ

/-- $\mathbb H[F,a,b]^\times\le(\mathbb H\otimes\mathbb A)^\times$. -/
def quatUnitsSub : Subgroup (QuatAdele a b)ˣ := (Units.map (quatDiagRing a b).toMonoidHom).range

/-- **$\mathbb H[F,a,b]^\times$ is discrete in $(\mathbb H\otimes\mathbb A)^\times$.** -/
theorem discreteTopology_quatUnitsSub : DiscreteTopology (quatUnitsSub a b) := by
  have := discreteTopology_diagVecSub (F := F) (ι := Fin 4)
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set (diagVecSub F (Fin 4))))
  have hW0 : (0 : AdeleSpace F (Fin 4)) ∈ W := by
    have : (0 : diagVecSub F (Fin 4)) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; rfl
    exact this
  set V : Set (QuatAdele a b)ˣ :=
    (fun u : (QuatAdele a b)ˣ => quatCoord a b (u : QuatAdele a b) - quatCoord a b 1) ⁻¹' W
  have hV : IsOpen V :=
    hW.preimage (((continuous_quatCoord a b).comp Units.continuous_val).sub continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr ⟨V, hV, ?_⟩)
  ext ⟨u, hu⟩
  obtain ⟨ξ, rfl⟩ := hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, V]
  have hcoord : quatCoord a b ((Units.map (quatDiagRing a b).toMonoidHom ξ : (QuatAdele a b)ˣ) : QuatAdele a b) -
      quatCoord a b 1 = diagQuat a b ((ξ : ℍ[F,a,b]) - 1) := by
    rw [← quatCoord_quatDiagRing, map_sub (quatDiagRing a b), map_sub (quatCoord a b), (quatDiagRing a b).map_one]
    rfl
  rw [hcoord]
  constructor
  · intro h
    have hmem : diagQuat a b ((ξ : ℍ[F,a,b]) - 1) ∈ diagVecSub F (Fin 4) := by
      rw [← range_diagQuat a b]; exact ⟨_, rfl⟩
    have h1 : (⟨_, hmem⟩ : diagVecSub F (Fin 4)) ∈ Subtype.val ⁻¹' W := h
    rw [hWeq] at h1
    have h2 : diagQuat a b ((ξ : ℍ[F,a,b]) - 1) = diagQuat a b 0 := by
      rw [map_zero]; exact congrArg Subtype.val h1
    have hξ : ξ = 1 := Units.ext (sub_eq_zero.mp (diagQuat_injective a b h2))
    subst hξ
    exact Subtype.ext (map_one _)
  · intro h
    have h1 : Units.map (quatDiagRing a b).toMonoidHom ξ = 1 := congrArg Subtype.val h
    have hξ : (ξ : ℍ[F,a,b]) = 1 := by
      have := congrArg (fun u : (QuatAdele a b)ˣ => quatCoord a b (u : QuatAdele a b)) h1
      simp only [Units.val_one] at this
      have h3 : diagQuat a b (ξ : ℍ[F,a,b]) = diagQuat a b 1 := by
        rw [← quatCoord_quatDiagRing, ← quatCoord_quatDiagRing, map_one]; exact this
      exact diagQuat_injective a b h3
    rw [hξ, sub_self, map_zero]; exact hW0

instance : DiscreteTopology (quatUnitsSub a b) := discreteTopology_quatUnitsSub a b

instance : Countable (quatUnitsSub a b) := by
  have : Countable ℍ[F,a,b] :=
    (QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).injective.countable
  have : Countable (ℍ[F,a,b])ˣ := Function.Injective.countable (f := fun u : (ℍ[F,a,b])ˣ => (u : ℍ[F,a,b]))
    Units.val_injective
  exact (Units.map (quatDiagRing a b).toMonoidHom).rangeRestrict_surjective.countable

/-! ### The reduced norm and $\mathbb H_{\mathbb A}^1$ -/

/-- $x\mapsto L_x$ as a homomorphism $(\mathbb H\otimes\mathbb A)^\times\to\mathrm{GL}_4(\mathbb A_F)$. -/
def quatLmatHom : (QuatAdele a b)ˣ →* GL (Fin 4) (Adeles F) :=
  Units.map (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _)).toMonoidHom

theorem quatLmatHom_apply (x : (QuatAdele a b)ˣ) : quatLmatHom a b x = quatLmat x := rfl

theorem continuous_leftMulMatrix :
    Continuous fun x : QuatAdele a b =>
      Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK (diag F a) 0 (diag F b)) x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact (continuous_apply i).comp ((continuous_quatCoord a b).comp (continuous_id.mul continuous_const))

theorem continuous_quatLmatHom : Continuous (quatLmatHom a b) := by
  refine Units.continuous_iff.mpr ⟨(continuous_leftMulMatrix a b).comp Units.continuous_val, ?_⟩
  have : (fun x : (QuatAdele a b)ˣ => (((quatLmatHom a b x)⁻¹ : GL (Fin 4) (Adeles F)) :
      Matrix (Fin 4) (Fin 4) (Adeles F))) = fun x => Algebra.leftMulMatrix
        (QuaternionAlgebra.basisOneIJK (diag F a) 0 (diag F b)) ((x⁻¹ : (QuatAdele a b)ˣ) : QuatAdele a b) := by
    funext x; rw [← map_inv]; rfl
  rw [this]
  exact (continuous_leftMulMatrix a b).comp Units.continuous_coe_inv

theorem continuous_glDet {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (GeneralLinearGroup.det : GL ι R → Rˣ) := by
  refine Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, ?_⟩
  have : (fun M : GL ι R => (((GeneralLinearGroup.det M)⁻¹ : Rˣ) : R)) =
      fun M => ((M⁻¹ : GL ι R) : Matrix ι ι R).det := by
    funext M; rw [← map_inv]; rfl
  rw [this]
  exact Units.continuous_coe_inv.matrix_det

/-- $x\mapsto\|\det L_x\|_{\mathbb A} = \|\operatorname{nrd}x\|_{\mathbb A}^2$, a homomorphism to $\mathbb R_{>0}$. -/
def quatNormSqHom : (QuatAdele a b)ˣ →* ℝ≥0 :=
  (ideleNormHom F).comp ((GeneralLinearGroup.det).comp (quatLmatHom a b))

theorem coe_quatNormSqHom (x : (QuatAdele a b)ˣ) :
    (quatNormSqHom a b x : ℝ) = ideleNorm F (nrdUnit x) ^ 2 := by
  change (ideleNormHom F (GeneralLinearGroup.det (quatLmat x)) : ℝ) = _
  rw [coe_ideleNormHom, ideleNorm_det_quatLmat]

/-- **The reduced norm is continuous**: $x\mapsto\|\operatorname{nrd}x\|_{\mathbb A}^2$ is a continuous homomorphism. -/
theorem continuous_quatNormSqHom : Continuous (quatNormSqHom a b) :=
  continuous_ideleNormHom.comp (continuous_glDet.comp (continuous_quatLmatHom a b))

/-- **$\mathbb H_{\mathbb A}^1$**: the units of reduced norm of idele norm $1$. -/
def quatOne : Subgroup (QuatAdele a b)ˣ := (quatNormSqHom a b).ker

theorem mem_quatOne {x : (QuatAdele a b)ˣ} : x ∈ quatOne a b ↔ ideleNorm F (nrdUnit x) = 1 := by
  rw [quatOne, MonoidHom.mem_ker, ← NNReal.coe_eq_one, coe_quatNormSqHom,
    pow_eq_one_iff_of_nonneg (ideleNorm_pos _).le two_ne_zero]

theorem isClosed_quatOne : IsClosed (quatOne a b : Set (QuatAdele a b)ˣ) :=
  isClosed_eq (continuous_quatNormSqHom a b) continuous_const

theorem quatDiagRing_star (ξ : ℍ[F,a,b]) : quatDiagRing a b (star ξ) = star (quatDiagRing a b ξ) := by
  ext <;> simp [quatDiagRing, QuaternionAlgebra.mapRingHom]

/-- **$\mathbb H^\times\le\mathbb H_{\mathbb A}^1$** (product formula: $\operatorname{nrd}(\xi)\in F^\times$). -/
theorem quatUnitsSub_le_quatOne : quatUnitsSub a b ≤ quatOne a b := by
  rintro _ ⟨ξ, rfl⟩
  rw [mem_quatOne]
  have hdet : IsUnit (LinearMap.det (LinearMap.mulLeft F (ξ : ℍ[F,a,b]))) := by
    have := (ξ.isUnit.map (Algebra.lmul F ℍ[F,a,b])).map LinearMap.det
    exact this
  rw [QuaternionAlgebra.det_mulLeft] at hdet
  have hn : IsUnit (((ξ : ℍ[F,a,b]) * star (ξ : ℍ[F,a,b])).re) := (isUnit_pow_iff two_ne_zero).mp hdet
  have : nrdUnit (Units.map (quatDiagRing a b).toMonoidHom ξ) = diagUnits F hn.unit := by
    refine Units.ext ?_
    rw [nrdUnit_val, diagUnits_val, IsUnit.unit_spec]
    change ((quatDiagRing a b ξ) * star (quatDiagRing a b ξ)).re = _
    rw [← quatDiagRing_star, ← map_mul]
    rfl
  rw [this, ideleNorm_diagUnits]

/-! ### Fundamental domains -/

/-- A measurable fundamental domain for $\mathbb H^\times$ in $(\mathbb H\otimes\mathbb A)^\times$, for every measure. -/
theorem exists_isFundamentalDomain_quatUnits (μ : Measure (QuatAdele a b)ˣ) :
    ∃ D : Set (QuatAdele a b)ˣ, IsFundamentalDomain (quatUnitsSub a b) D μ :=
  exists_isFundamentalDomain _ μ

instance : SecondCountableTopology (quatOne a b) := TopologicalSpace.Subtype.secondCountableTopology _

/-- $\mathbb H^\times$ as a subgroup of $\mathbb H_{\mathbb A}^1$. -/
def quatUnitsOne : Subgroup (quatOne a b) := (quatUnitsSub a b).subgroupOf (quatOne a b)

instance : DiscreteTopology (quatUnitsOne a b) := by
  refine DiscreteTopology.of_continuous_injective (f := fun x : quatUnitsOne a b =>
    (⟨(x : quatOne a b), x.2⟩ : quatUnitsSub a b)) ?_ ?_
  · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  · intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : quatUnitsSub a b => (z : (QuatAdele a b)ˣ)) h))

/-- A measurable fundamental domain for $\mathbb H^\times$ in $\mathbb H_{\mathbb A}^1$, for every measure. -/
theorem exists_isFundamentalDomain_quatOne (μ : Measure (quatOne a b)) :
    ∃ D : Set (quatOne a b), IsFundamentalDomain (quatUnitsOne a b) D μ :=
  exists_isFundamentalDomain _ μ

end

end QuadFormsKB.Tamagawa.Measure.Weil
