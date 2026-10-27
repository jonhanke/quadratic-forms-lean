import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeNorm
import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawaGlobal

/-!
# Base change for a quadratic extension: rings, quaternion units, transport of covolumes

$k' = K$ is a quadratic extension of $k$ given by a $k$-basis $b = (1,\delta)$ with $\delta^2 = d\in k$
(`hb0 : b 0 = 1`, `hb1 : b 1 * b 1 = algebraMap k K d`). Then $E = k[\delta] = $ `QuadraticAlgebra k d 0`
and $E\otimes_k\mathbb A_k = $ `QuadAdele d` $=$ `QuadraticAlgebra (Adeles k) d 0` (topology from the coordinates
$(\mathrm{re},\mathrm{im})\in\mathbb A_k^2$, i.e. from the $k$-structure only).

* **`quadBaseChange`** : `QuadAdele d ≃+* Adeles K`, $x + y\omega\mapsto\iota(x) + \delta\,\iota(y)$, a ring isomorphism
  and a homeomorphism (`continuous_quadBaseChange`, `continuous_quadBaseChange_symm`); it is `adeleBaseChange b` in
  coordinates (`quadBaseChange_eq`), and maps $E$ onto $K$ (`quadBaseChange_quadDiag`).
* **`quatBaseChange`** : for $\alpha,\beta\in k$, $\mathbb H[E\otimes\mathbb A_k,\alpha,\beta] = D_E\otimes_k\mathbb A_k$
  (`QuatQuadAdele d α β`) $\cong\mathbb H[\mathbb A_K,\alpha,\beta] = D'\otimes_K\mathbb A_K$ (`QuatAdele`), a ring isomorphism
  and homeomorphism, hence **`quatUnitsBaseChange`** : $(D_E\otimes_k\mathbb A_k)^\times\cong(D'\otimes_K\mathbb A_K)^\times$
  as topological groups, mapping $D_E^\times$ onto $D'^\times$ (`map_quatUnitsSub_quatUnitsBaseChange_symm`) and
  commuting with the reduced norm (`normSq_quatBaseChange`), so also $\mathrm{SL}_1$ onto $\mathrm{SL}_1$.
* **`covolume_map_continuousMulEquiv`** (generic) and **`covolume_quatUnitsBaseChange`**: for any left-invariant
  measure $\mu$ on $(D'\otimes\mathbb A_K)^\times$ for which $D'^\times$ has a fundamental domain, the covolume of
  $(R_{K/k}D'^\times)(k) = D_E^\times$ in $(R_{K/k}D'^\times)(\mathbb A_k)$ for the transported measure equals the covolume
  of $D'^\times$ in $(D'\otimes\mathbb A_K)^\times$ for $\mu$ (the Weil-restriction viewpoint).
* `basisOneDelta`: the basis $(1,\delta)$ of $K = k(\delta)$; **`quadSplit`**: the split case $d = c^2$,
  $E\otimes_k\mathbb A_k\cong\mathbb A_k\times\mathbb A_k$ (ring isomorphism and homeomorphism).
-/

open IsDedekindDomain NumberField Topology Filter MeasureTheory NumberField.mixedEmbedding
open scoped ENNReal Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section CovolumeTransport


variable {G G' : Type*} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [IsTopologicalGroup G] [IsTopologicalGroup G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

/-- **Transport of covolumes** along an isomorphism of topological groups: if $\Phi : G\cong G'$ maps $\Gamma$ onto
$\Gamma'$ and $s$ is a fundamental domain for $\Gamma$, then $\Phi(s)$ is one for $\Gamma'$ and
$\operatorname{covol}(\Gamma', \Phi_*\mu) = \operatorname{covol}(\Gamma,\mu)$. -/
@[kb "weil1982" "§1.3 (restriction of scalars) [unverified page]"]
theorem covolume_map_continuousMulEquiv (Φ : G ≃ₜ* G') (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {s : Set G} (hs : IsFundamentalDomain Γ s μ) :
    covolume (Γ.map Φ.toMulEquiv.toMonoidHom) G' (μ.map Φ) = covolume Γ G μ := by
  set Γ' := Γ.map Φ.toMulEquiv.toMonoidHom
  have hm : Measurable (⇑Φ : G → G') := (map_continuous Φ).measurable
  have hms : Measurable (⇑Φ.symm : G' → G) := (map_continuous Φ.symm).measurable
  have hinv : (μ.map Φ).IsMulLeftInvariant :=
    isMulLeftInvariant_map Φ.toMulEquiv.toMonoidHom.toMulHom hm Φ.surjective
  let e : Γ' ≃ Γ := (Γ.equivMapOfInjective Φ.toMulEquiv.toMonoidHom Φ.injective).symm.toEquiv
  let Φm : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
  have hmap : ∀ t : Set G', (μ.map Φ) t = μ (Φ ⁻¹' t) := fun t => Φm.map_apply t
  have hqmp : Measure.QuasiMeasurePreserving Φ.toEquiv.symm (μ.map Φ) μ := by
    refine ⟨hms, Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_⟩
    have h2 : (Measure.map Φ.toEquiv.symm (μ.map Φ)) t = (μ.map Φ) (Φ.toEquiv.symm ⁻¹' t) :=
      Φm.symm.map_apply t
    rw [h2, hmap]
    convert h0 using 2
    ext x; simp
  have hef : ∀ g : Γ', Function.Semiconj Φ.toEquiv (e g • ·) (g • ·) := by
    intro g x
    have hg : Φ ((e g : Γ) : G) = (g : G') := by
      have h1 := Subgroup.coe_equivMapOfInjective_apply Γ Φ.toMulEquiv.toMonoidHom Φ.injective (e g)
      have h2 : (Γ.equivMapOfInjective Φ.toMulEquiv.toMonoidHom Φ.injective) (e g) = g :=
        MulEquiv.apply_symm_apply _ g
      rw [h2] at h1
      exact h1.symm
    show Φ ((e g : G) * x) = (g : G') * Φ x
    rw [map_mul, hg]
  have hs' : IsFundamentalDomain Γ' (Φ.toEquiv '' s) (μ.map Φ) := hs.image_of_equiv Φ.toEquiv hqmp e hef
  have : SMulInvariantMeasure Γ G μ := inferInstance
  have : SMulInvariantMeasure Γ' G' (μ.map Φ) := inferInstance
  have : Countable Γ' := e.injective.countable
  rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, hmap]
  exact congrArg μ (Set.preimage_image_eq s Φ.toEquiv.injective)

end CovolumeTransport

section Quadratic

set_option synthInstance.maxHeartbeats 400000

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

variable (k) in
/-- $E\otimes_k\mathbb A_k$ for $E = k[\omega]/(\omega^2 - d)$: `QuadraticAlgebra (Adeles k) d 0`. -/
abbrev QuadAdele (d : k) : Type := QuadraticAlgebra (Adeles k) (diagRing k d) 0

/-- The topology of $E\otimes_k\mathbb A_k$: induced by the coordinates $(\mathrm{re},\mathrm{im})\in\mathbb A_k^2$. -/
instance (d : k) : TopologicalSpace (QuadAdele k d) :=
  TopologicalSpace.induced (fun z => (z.re, z.im)) inferInstance

theorem continuous_quadCoord (d : k) : Continuous fun z : QuadAdele k d => (z.re, z.im) :=
  continuous_induced_dom

theorem continuous_quad_re (d : k) : Continuous fun z : QuadAdele k d => z.re := (continuous_quadCoord d).fst

theorem continuous_quad_im (d : k) : Continuous fun z : QuadAdele k d => z.im := (continuous_quadCoord d).snd

theorem continuous_quad_iff {X : Type*} [TopologicalSpace X] (d : k) {f : X → QuadAdele k d} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).im) :=
  ⟨fun h => ⟨(continuous_quad_re d).comp h, (continuous_quad_im d).comp h⟩,
    fun ⟨h0, h1⟩ => continuous_induced_rng.mpr (h0.prodMk h1)⟩

instance (d : k) : ContinuousAdd (QuadAdele k d) := ⟨by
  have h0 := continuous_quad_re d; have h1 := continuous_quad_im d
  refine (continuous_quad_iff d).mpr ⟨?_, ?_⟩ <;>
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> fun_prop⟩

instance (d : k) : ContinuousNeg (QuadAdele k d) := ⟨by
  have h0 := continuous_quad_re d; have h1 := continuous_quad_im d
  refine (continuous_quad_iff d).mpr ⟨?_, ?_⟩ <;>
    simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg] <;> fun_prop⟩

instance (d : k) : ContinuousMul (QuadAdele k d) := ⟨by
  have h0 := continuous_quad_re d; have h1 := continuous_quad_im d
  refine (continuous_quad_iff d).mpr ⟨?_, ?_⟩ <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> fun_prop⟩

instance (d : k) : IsTopologicalRing (QuadAdele k d) := {}

variable {d : k} {b : Module.Basis (Fin 2) k K}

/-- $x + y\omega\mapsto\iota(x) + \delta\,\iota(y)$, $\delta = b_1$. -/
def quadBaseChangeHom (hb1 : b 1 * b 1 = algebraMap k K d) : QuadAdele k d →+* Adeles K where
  toFun z := adeleMap k K z.re + diagRing K (b 1) * adeleMap k K z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    have hδ : diagRing K (b 1) * diagRing K (b 1) = adeleMap k K (diagRing k d) := by
      rw [← map_mul, hb1, diagRing_apply, diagRing_apply, adeleMap_diag]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero,
      map_zero]
    linear_combination (adeleMap k K z.im * adeleMap k K w.im) * hδ.symm
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

theorem quadBaseChangeHom_eq (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d) (z : QuadAdele k d) :
    quadBaseChangeHom hb1 z = adeleBaseChange b ![z.re, z.im] := by
  rw [adeleBaseChange_apply, Fin.sum_univ_two, hb0, map_one, one_mul]
  rfl

theorem quadBaseChangeHom_bijective (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d) :
    Function.Bijective (quadBaseChangeHom hb1) := by
  refine ⟨fun z w h => ?_, fun y => ?_⟩
  · rw [quadBaseChangeHom_eq hb0, quadBaseChangeHom_eq hb0] at h
    have h' := (adeleBaseChange b).injective h
    exact QuadraticAlgebra.ext (congrFun h' 0) (congrFun h' 1)
  · refine ⟨⟨(adeleBaseChange b).symm y 0, (adeleBaseChange b).symm y 1⟩, ?_⟩
    rw [quadBaseChangeHom_eq hb0]
    have : (![(adeleBaseChange b).symm y 0, (adeleBaseChange b).symm y 1] : Fin 2 → Adeles k) =
        (adeleBaseChange b).symm y := by
      funext i; fin_cases i <;> rfl
    simp only [this, ContinuousAddEquiv.apply_symm_apply]

/-- **$E\otimes_k\mathbb A_k\cong\mathbb A_K$ as rings** for a quadratic extension $K = k(\delta)$, $\delta^2 = d$. -/
def quadBaseChange (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d) : QuadAdele k d ≃+* Adeles K :=
  RingEquiv.ofBijective _ (quadBaseChangeHom_bijective hb0 hb1)

variable (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d)

theorem quadBaseChange_apply (z : QuadAdele k d) :
    quadBaseChange hb0 hb1 z = adeleMap k K z.re + diagRing K (b 1) * adeleMap k K z.im := rfl

theorem quadBaseChange_eq (z : QuadAdele k d) :
    quadBaseChange hb0 hb1 z = adeleBaseChange b ![z.re, z.im] := quadBaseChangeHom_eq hb0 hb1 z

theorem continuous_quadBaseChange : Continuous (quadBaseChange hb0 hb1) := by
  have : (quadBaseChange hb0 hb1 : QuadAdele k d → Adeles K) =
      (adeleBaseChange b) ∘ fun z => ![z.re, z.im] := funext (quadBaseChange_eq hb0 hb1)
  rw [this]
  refine (adeleBaseChange b).continuous.comp (continuous_pi fun i => ?_)
  fin_cases i
  exacts [continuous_quad_re d, continuous_quad_im d]

theorem quadBaseChange_symm_apply (y : Adeles K) :
    (quadBaseChange hb0 hb1).symm y = ⟨(adeleBaseChange b).symm y 0, (adeleBaseChange b).symm y 1⟩ := by
  apply (quadBaseChange hb0 hb1).injective
  rw [RingEquiv.apply_symm_apply, quadBaseChange_eq]
  have : (![(adeleBaseChange b).symm y 0, (adeleBaseChange b).symm y 1] : Fin 2 → Adeles k) =
      (adeleBaseChange b).symm y := by
    funext i; fin_cases i <;> rfl
  simp only [this, ContinuousAddEquiv.apply_symm_apply]

theorem continuous_quadBaseChange_symm : Continuous (quadBaseChange hb0 hb1).symm := by
  have : ((quadBaseChange hb0 hb1).symm : Adeles K → QuadAdele k d) =
      fun y => ⟨(adeleBaseChange b).symm y 0, (adeleBaseChange b).symm y 1⟩ :=
    funext (quadBaseChange_symm_apply hb0 hb1)
  rw [this]
  refine continuous_induced_rng.mpr ?_
  exact ((continuous_apply 0).comp (adeleBaseChange b).symm.continuous).prodMk
    ((continuous_apply 1).comp (adeleBaseChange b).symm.continuous)

variable (d) in
/-- The $k$-points: $E = $ `QuadraticAlgebra k d 0` $\to E\otimes_k\mathbb A_k$, coordinatewise diagonal. -/
def quadDiag : QuadraticAlgebra k d 0 →+* QuadAdele k d where
  toFun z := ⟨diagRing k z.re, diagRing k z.im⟩
  map_one' := QuadraticAlgebra.ext (by simp [QuadraticAlgebra.re_one]) (by simp [QuadraticAlgebra.im_one])
  map_mul' z w := QuadraticAlgebra.ext (by simp) (by simp)
  map_zero' := QuadraticAlgebra.ext (by simp) (by simp)
  map_add' z w := QuadraticAlgebra.ext (by simp) (by simp)

/-- $E\to K$, $x + y\omega\mapsto x + y\delta$ (an isomorphism, `quadField_bijective`). -/
def quadField : QuadraticAlgebra k d 0 →+* K where
  toFun z := algebraMap k K z.re + b 1 * algebraMap k K z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (algebraMap k K z.im * algebraMap k K w.im) * hb1.symm
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

include hb0 in
theorem quadField_eq (z : QuadraticAlgebra k d 0) :
    quadField hb1 z = b.equivFun.symm ![z.re, z.im] := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, hb0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one]
  rw [mul_comm]; rfl

include hb0 in
theorem quadField_bijective : Function.Bijective (quadField (d := d) hb1) := by
  refine ⟨fun z w h => ?_, fun y => ⟨⟨b.equivFun y 0, b.equivFun y 1⟩, ?_⟩⟩
  · rw [quadField_eq hb0, quadField_eq hb0] at h
    have h' := b.equivFun.symm.injective h
    exact QuadraticAlgebra.ext (congrFun h' 0) (congrFun h' 1)
  · rw [quadField_eq hb0]
    have : (![b.equivFun y 0, b.equivFun y 1] : Fin 2 → k) = b.equivFun y := by
      funext i; fin_cases i <;> rfl
    rw [this, LinearEquiv.symm_apply_apply]

/-- $\Theta$ maps $E$ onto $K$: $\Theta(\mathrm{diag}\,z) = \mathrm{diag}(x + y\delta)$. -/
theorem quadBaseChange_quadDiag (z : QuadraticAlgebra k d 0) :
    quadBaseChange hb0 hb1 (quadDiag d z) = diagRing K (quadField hb1 z) := by
  rw [quadBaseChange_apply]
  change adeleMap k K (diag k z.re) + diagRing K (b 1) * adeleMap k K (diag k z.im) = _
  rw [adeleMap_diag, adeleMap_diag, ← diagRing_apply, ← diagRing_apply, ← map_mul, ← map_add]
  rfl

end Quadratic

section Quaternion

set_option synthInstance.maxHeartbeats 400000

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

variable (k) in
/-- $D_E\otimes_k\mathbb A_k = \mathbb H[E\otimes_k\mathbb A_k,\alpha,\beta]$ for $\alpha,\beta\in k$. -/
abbrev QuatQuadAdele (d α β : k) : Type :=
  ℍ[QuadAdele k d, (⟨diagRing k α, 0⟩ : QuadAdele k d), 0, (⟨diagRing k β, 0⟩ : QuadAdele k d)]

/-- Coordinates $1,i,j,k$ of $D_E\otimes_k\mathbb A_k$. -/
abbrev quatQuadCoord (d α β : k) : QuatQuadAdele k d α β ≃ₗ[QuadAdele k d] (Fin 4 → QuadAdele k d) :=
  QuaternionAlgebra.linearEquivTuple _ _ _

/-- The topology of $D_E\otimes_k\mathbb A_k$: from the coordinates in $(E\otimes\mathbb A_k)^4 = \mathbb A_k^8$. -/
instance (d α β : k) : TopologicalSpace (QuatQuadAdele k d α β) :=
  TopologicalSpace.induced (quatQuadCoord d α β) inferInstance

theorem continuous_quatQuadCoord (d α β : k) (i : Fin 4) :
    Continuous fun x : QuatQuadAdele k d α β => quatQuadCoord d α β x i :=
  (continuous_apply i).comp continuous_induced_dom

variable {d : k} {b : Module.Basis (Fin 2) k K} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d)
  (α β : k)

theorem quadBaseChange_const (t : k) :
    quadBaseChange hb0 hb1 ⟨diagRing k t, 0⟩ = diag K (algebraMap k K t) := by
  rw [quadBaseChange_apply]
  change adeleMap k K (diag k t) + diagRing K (b 1) * adeleMap k K 0 = _
  rw [adeleMap_diag, map_zero, mul_zero, add_zero]

theorem quadBaseChange_symm_const (t : k) :
    (quadBaseChange hb0 hb1).symm (diag K (algebraMap k K t)) = ⟨diagRing k t, 0⟩ := by
  rw [RingEquiv.symm_apply_eq, quadBaseChange_const]

/-- **$D_E\otimes_k\mathbb A_k\cong D'\otimes_K\mathbb A_K$** ($D' = \mathbb H[K,\alpha,\beta]$), coordinatewise
`quadBaseChange`. -/
def quatBaseChange :
    QuatQuadAdele k d α β ≃+* QuatAdele (F := K) (algebraMap k K α) (algebraMap k K β) :=
  RingEquiv.ofRingHom
    (QuaternionAlgebra.mapRingHom (quadBaseChange hb0 hb1).toRingHom (quadBaseChange_const hb0 hb1 α)
      (map_zero _) (quadBaseChange_const hb0 hb1 β))
    (QuaternionAlgebra.mapRingHom (quadBaseChange hb0 hb1).symm.toRingHom
      (quadBaseChange_symm_const hb0 hb1 α) (map_zero _) (quadBaseChange_symm_const hb0 hb1 β))
    (RingHom.ext fun x => QuaternionAlgebra.ext ((quadBaseChange hb0 hb1).apply_symm_apply x.re)
      ((quadBaseChange hb0 hb1).apply_symm_apply x.imI) ((quadBaseChange hb0 hb1).apply_symm_apply x.imJ)
      ((quadBaseChange hb0 hb1).apply_symm_apply x.imK))
    (RingHom.ext fun x => QuaternionAlgebra.ext ((quadBaseChange hb0 hb1).symm_apply_apply x.re)
      ((quadBaseChange hb0 hb1).symm_apply_apply x.imI) ((quadBaseChange hb0 hb1).symm_apply_apply x.imJ)
      ((quadBaseChange hb0 hb1).symm_apply_apply x.imK))

@[simp] theorem quatBaseChange_re (x : QuatQuadAdele k d α β) :
    (quatBaseChange hb0 hb1 α β x).re = quadBaseChange hb0 hb1 x.re := rfl
@[simp] theorem quatBaseChange_imI (x : QuatQuadAdele k d α β) :
    (quatBaseChange hb0 hb1 α β x).imI = quadBaseChange hb0 hb1 x.imI := rfl
@[simp] theorem quatBaseChange_imJ (x : QuatQuadAdele k d α β) :
    (quatBaseChange hb0 hb1 α β x).imJ = quadBaseChange hb0 hb1 x.imJ := rfl
@[simp] theorem quatBaseChange_imK (x : QuatQuadAdele k d α β) :
    (quatBaseChange hb0 hb1 α β x).imK = quadBaseChange hb0 hb1 x.imK := rfl

theorem continuous_quatBaseChange : Continuous (quatBaseChange hb0 hb1 α β) := by
  have hq := continuous_quadBaseChange hb0 hb1
  refine (continuous_quat_iff _ _).mpr ⟨?_, ?_, ?_, ?_⟩
  · exact hq.comp (continuous_quatQuadCoord d α β 0)
  · exact hq.comp (continuous_quatQuadCoord d α β 1)
  · exact hq.comp (continuous_quatQuadCoord d α β 2)
  · exact hq.comp (continuous_quatQuadCoord d α β 3)

theorem continuous_quatBaseChange_symm : Continuous (quatBaseChange hb0 hb1 α β).symm := by
  have hq := continuous_quadBaseChange_symm hb0 hb1
  refine continuous_induced_rng.mpr (continuous_pi fun i => ?_)
  fin_cases i
  · exact hq.comp (continuous_re _ _)
  · exact hq.comp (continuous_imI _ _)
  · exact hq.comp (continuous_imJ _ _)
  · exact hq.comp (continuous_imK _ _)

/-- **$(D_E\otimes_k\mathbb A_k)^\times\cong(D'\otimes_K\mathbb A_K)^\times$ as topological groups.** -/
def quatUnitsBaseChange :
    (QuatQuadAdele k d α β)ˣ ≃ₜ* (QuatAdele (F := K) (algebraMap k K α) (algebraMap k K β))ˣ :=
  unitsContinuousMulEquiv (quatBaseChange hb0 hb1 α β) (continuous_quatBaseChange hb0 hb1 α β)
    (continuous_quatBaseChange_symm hb0 hb1 α β)

/-- $\Theta_{\mathbb H}$ commutes with the reduced norm $x\mapsto x\bar x$ (so it maps $\mathrm{SL}_1$ onto $\mathrm{SL}_1$). -/
theorem quatBaseChange_mul_star (x : QuatQuadAdele k d α β) :
    quatBaseChange hb0 hb1 α β (x * star x) =
      quatBaseChange hb0 hb1 α β x * star (quatBaseChange hb0 hb1 α β x) := by
  rw [map_mul]
  congr 1
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star]

/-- $\mathrm{SL}_1$ of a quaternion algebra over a commutative ring: units with $x\bar x = 1$. -/
def quatSL1 {R : Type*} [CommRing R] (c₁ c₃ : R) : Subgroup (ℍ[R, c₁, 0, c₃])ˣ where
  carrier := {u | (u : ℍ[R, c₁, 0, c₃]) * star (u : ℍ[R, c₁, 0, c₃]) = 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, star_mul] at hu hv ⊢
    calc (u : ℍ[R, c₁, 0, c₃]) * v * (star (v : ℍ[R, c₁, 0, c₃]) * star (u : ℍ[R, c₁, 0, c₃]))
        = u * (v * star (v : ℍ[R, c₁, 0, c₃])) * star (u : ℍ[R, c₁, 0, c₃]) := by noncomm_ring
      _ = 1 := by rw [hv, mul_one, hu]
  inv_mem' {u} hu := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    have hc : star (u : ℍ[R, c₁, 0, c₃]) * u = 1 := by rw [star_comm_self']; exact hu
    have h1 : star (u : ℍ[R, c₁, 0, c₃]) = ((u⁻¹ : (ℍ[R, c₁, 0, c₃])ˣ) : ℍ[R, c₁, 0, c₃]) := by
      calc star (u : ℍ[R, c₁, 0, c₃]) = star (u : ℍ[R, c₁, 0, c₃]) * (u * ↑u⁻¹) := by simp
        _ = ↑u⁻¹ := by rw [← mul_assoc, hc, one_mul]
    rw [← h1, star_star, hc]

/-! ### $k$-points and $K$-points; transport of covolumes -/

theorem continuous_quatQuad_iff {X : Type*} [TopologicalSpace X] (d α β : k) {f : X → QuatQuadAdele k d α β} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  refine ⟨fun h => ⟨(continuous_quatQuadCoord d α β 0).comp h, (continuous_quatQuadCoord d α β 1).comp h,
    (continuous_quatQuadCoord d α β 2).comp h, (continuous_quatQuadCoord d α β 3).comp h⟩,
    fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  refine continuous_induced_rng.mpr (continuous_pi fun i => ?_)
  fin_cases i
  exacts [h0, h1, h2, h3]

instance (d α β : k) : ContinuousMul (QuatQuadAdele k d α β) := ⟨by
  set P := QuatQuadAdele k d α β × QuatQuadAdele k d α β
  have c0 := continuous_quatQuadCoord d α β 0
  have c1 := continuous_quatQuadCoord d α β 1
  have c2 := continuous_quatQuadCoord d α β 2
  have c3 := continuous_quatQuadCoord d α β 3
  have hf : Continuous fun p : P => p.1.re := c0.comp continuous_fst
  have hs : Continuous fun p : P => p.2.re := c0.comp continuous_snd
  have hf1 : Continuous fun p : P => p.1.imI := c1.comp continuous_fst
  have hs1 : Continuous fun p : P => p.2.imI := c1.comp continuous_snd
  have hf2 : Continuous fun p : P => p.1.imJ := c2.comp continuous_fst
  have hs2 : Continuous fun p : P => p.2.imJ := c2.comp continuous_snd
  have hf3 : Continuous fun p : P => p.1.imK := c3.comp continuous_fst
  have hs3 : Continuous fun p : P => p.2.imK := c3.comp continuous_snd
  refine (continuous_quatQuad_iff d α β).mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul] <;> fun_prop⟩

instance measurableSpace_quatQuadUnits (d α β : k) : MeasurableSpace (QuatQuadAdele k d α β)ˣ := borel _

instance (d α β : k) : BorelSpace (QuatQuadAdele k d α β)ˣ := ⟨rfl⟩

variable (d) in
/-- $D_E = \mathbb H[E,\alpha,\beta]\to D_E\otimes_k\mathbb A_k$ (the $k$-points of $R_{K/k}D'$). -/
def quatQuadDiag :
    ℍ[QuadraticAlgebra k d 0, (⟨α, 0⟩ : QuadraticAlgebra k d 0), 0, (⟨β, 0⟩ : QuadraticAlgebra k d 0)] →+*
      QuatQuadAdele k d α β :=
  QuaternionAlgebra.mapRingHom (quadDiag d) (QuadraticAlgebra.ext rfl (map_zero _)) (map_zero _)
    (QuadraticAlgebra.ext rfl (map_zero _))

/-- $D_E\to D' = \mathbb H[K,\alpha,\beta]$, coordinatewise `quadField` (an isomorphism). -/
def quatField :
    ℍ[QuadraticAlgebra k d 0, (⟨α, 0⟩ : QuadraticAlgebra k d 0), 0, (⟨β, 0⟩ : QuadraticAlgebra k d 0)] →+*
      ℍ[K, algebraMap k K α, 0, algebraMap k K β] :=
  QuaternionAlgebra.mapRingHom (quadField hb1) (by simp [quadField]) (map_zero _) (by simp [quadField])

include hb0 in
theorem quatField_bijective : Function.Bijective (quatField hb1 α β) := by
  have hq := quadField_bijective (d := d) hb0 hb1
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h0 := congrArg QuaternionAlgebra.re h
    have h1 := congrArg QuaternionAlgebra.imI h
    have h2 := congrArg QuaternionAlgebra.imJ h
    have h3 := congrArg QuaternionAlgebra.imK h
    exact QuaternionAlgebra.ext (hq.1 h0) (hq.1 h1) (hq.1 h2) (hq.1 h3)
  · obtain ⟨x0, h0⟩ := hq.2 y.re
    obtain ⟨x1, h1⟩ := hq.2 y.imI
    obtain ⟨x2, h2⟩ := hq.2 y.imJ
    obtain ⟨x3, h3⟩ := hq.2 y.imK
    exact ⟨⟨x0, x1, x2, x3⟩, QuaternionAlgebra.ext h0 h1 h2 h3⟩

/-- $\Theta_{\mathbb H}$ maps $D_E$ onto $D'$: $\Theta_{\mathbb H}\circ\mathrm{diag} = \mathrm{diag}\circ$ `quatField`. -/
theorem quatBaseChange_quatQuadDiag (x) :
    quatBaseChange hb0 hb1 α β (quatQuadDiag d α β x) = quatDiagRing _ _ (quatField hb1 α β x) :=
  QuaternionAlgebra.ext (quadBaseChange_quadDiag hb0 hb1 _) (quadBaseChange_quadDiag hb0 hb1 _)
    (quadBaseChange_quadDiag hb0 hb1 _) (quadBaseChange_quadDiag hb0 hb1 _)

variable (d) in
/-- $D_E^\times\le(D_E\otimes_k\mathbb A_k)^\times$: the $k$-points of $R_{K/k}D'^\times$. -/
def quatQuadUnitsSub : Subgroup (QuatQuadAdele k d α β)ˣ :=
  (Units.map (quatQuadDiag d α β).toMonoidHom).range

/-- **$\Theta_{\mathbb H}^{-1}$ maps $D'^\times$ onto $D_E^\times$.** -/
theorem map_quatUnitsSub_quatUnitsBaseChange_symm :
    (quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)).map
      (quatUnitsBaseChange hb0 hb1 α β).symm.toMulEquiv.toMonoidHom = quatQuadUnitsSub d α β := by
  set e := RingEquiv.ofBijective _ (quatField_bijective hb0 hb1 α β)
  have hΦ : ∀ w, quatUnitsBaseChange hb0 hb1 α β (Units.map (quatQuadDiag d α β).toMonoidHom w) =
      Units.map (quatDiagRing _ _).toMonoidHom (Units.map e.toMonoidHom w) := fun w =>
    Units.ext (quatBaseChange_quatQuadDiag hb0 hb1 α β (w : _))
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range, quatQuadUnitsSub, quatUnitsSub]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨Units.map e.symm.toMonoidHom u, ?_⟩
    apply (quatUnitsBaseChange hb0 hb1 α β).injective
    rw [hΦ]
    refine Units.ext ?_
    change quatDiagRing _ _ (e (e.symm (u : ℍ[K, algebraMap k K α, 0, algebraMap k K β]))) =
      ((quatUnitsBaseChange hb0 hb1 α β ((quatUnitsBaseChange hb0 hb1 α β).symm
        (Units.map (quatDiagRing _ _).toMonoidHom u)) : _) : QuatAdele (F := K) _ _)
    rw [RingEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨w, rfl⟩
    refine ⟨_, ⟨Units.map e.toMonoidHom w, rfl⟩, ?_⟩
    apply (quatUnitsBaseChange hb0 hb1 α β).injective
    rw [hΦ]
    exact ContinuousMulEquiv.apply_symm_apply _ _

/-- **Transport of covolumes for $R_{K/k}D'^\times$** (the Weil-restriction viewpoint): for a left-invariant
measure $\mu$ on $(D'\otimes_K\mathbb A_K)^\times$ and a fundamental domain of $D'^\times$, the covolume of
$D_E^\times = (R_{K/k}D'^\times)(k)$ in $(D_E\otimes_k\mathbb A_k)^\times = (R_{K/k}D'^\times)(\mathbb A_k)$ for the transported
measure $(\Theta_{\mathbb H}^{-1})_*\mu$ equals the covolume of $D'^\times$ for $\mu$. -/
@[kb "weil1982" "§1.3 (restriction of scalars) [unverified page]"]
theorem covolume_quatUnitsBaseChange
    (μ : Measure (QuatAdele (F := K) (algebraMap k K α) (algebraMap k K β))ˣ) [μ.IsMulLeftInvariant]
    {s : Set (QuatAdele (F := K) (algebraMap k K α) (algebraMap k K β))ˣ}
    (hs : IsFundamentalDomain (quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)) s μ) :
    covolume (quatQuadUnitsSub d α β) (QuatQuadAdele k d α β)ˣ (μ.map (quatUnitsBaseChange hb0 hb1 α β).symm) =
      covolume (quatUnitsSub (F := K) (algebraMap k K α) (algebraMap k K β)) _ μ := by
  rw [← map_quatUnitsSub_quatUnitsBaseChange_symm hb0 hb1 α β]
  exact covolume_map_continuousMulEquiv (quatUnitsBaseChange hb0 hb1 α β).symm _ μ hs

theorem mem_quatSL1_iff {R : Type*} [CommRing R] {c₁ c₃ : R} (u : (ℍ[R, c₁, 0, c₃])ˣ) :
    u ∈ quatSL1 c₁ c₃ ↔ (u : ℍ[R, c₁, 0, c₃]) * star (u : ℍ[R, c₁, 0, c₃]) = 1 := Iff.rfl

/-- **$\Theta_{\mathbb H}$ maps $\mathrm{SL}_1(D_E\otimes\mathbb A_k)$ onto $\mathrm{SL}_1(D'\otimes\mathbb A_K)$.** -/
theorem map_quatSL1_quatUnitsBaseChange :
    (quatSL1 (⟨diagRing k α, 0⟩ : QuadAdele k d) ⟨diagRing k β, 0⟩).map
      (quatUnitsBaseChange hb0 hb1 α β).toMulEquiv.toMonoidHom =
      quatSL1 (diag K (algebraMap k K α)) (diag K (algebraMap k K β)) := by
  have key : ∀ u : (QuatQuadAdele k d α β)ˣ,
      ((quatUnitsBaseChange hb0 hb1 α β u : (QuatAdele (F := K) _ _)ˣ) : QuatAdele (F := K) _ _) *
        star ((quatUnitsBaseChange hb0 hb1 α β u : (QuatAdele (F := K) _ _)ˣ) : QuatAdele (F := K) _ _) =
      quatBaseChange hb0 hb1 α β ((u : QuatQuadAdele k d α β) * star (u : QuatQuadAdele k d α β)) :=
    fun u => (quatBaseChange_mul_star hb0 hb1 α β u).symm
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, mem_quatSL1_iff] at hu
    rw [mem_quatSL1_iff]
    have : ((quatUnitsBaseChange hb0 hb1 α β).toMulEquiv.toMonoidHom u) = quatUnitsBaseChange hb0 hb1 α β u :=
      rfl
    rw [this, key, hu, map_one]
  · intro hg
    refine ⟨(quatUnitsBaseChange hb0 hb1 α β).symm g, ?_, ContinuousMulEquiv.apply_symm_apply _ g⟩
    rw [mem_quatSL1_iff] at hg
    rw [SetLike.mem_coe, mem_quatSL1_iff]
    apply (quatBaseChange hb0 hb1 α β).injective
    rw [← key, map_one, ContinuousMulEquiv.apply_symm_apply]
    exact hg

end Quaternion

/-! ### The basis $(1,\delta)$, and the split case $E = k\times k$ -/

section Basis

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The $k$-basis $(1,\delta)$ of a quadratic extension $K = k(\delta)$: $\delta\notin k$, $[K:k] = 2$. -/
def basisOneDelta (δ : K) (hδ : δ ∉ Set.range (algebraMap k K)) (hK : Module.finrank k K = 2) :
    Module.Basis (Fin 2) k K :=
  basisOfLinearIndependentOfCardEqFinrank
    (LinearIndependent.pair_iff.mpr fun s t hst => by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      by_cases ht : t = 0
      · subst ht
        rw [map_zero, zero_mul, add_zero, map_eq_zero_iff _ (algebraMap k K).injective] at hst
        exact ⟨hst, rfl⟩
      · exfalso
        apply hδ
        have ht' : algebraMap k K t ≠ 0 := (map_ne_zero_iff _ (algebraMap k K).injective).mpr ht
        refine ⟨-(t⁻¹ * s), ?_⟩
        rw [map_neg, map_mul, map_inv₀]
        field_simp
        linear_combination -hst)
    (by simp [hK])

theorem basisOneDelta_zero (δ : K) (hδ : δ ∉ Set.range (algebraMap k K)) (hK : Module.finrank k K = 2) :
    basisOneDelta δ hδ hK 0 = 1 := by
  simp [basisOneDelta]

theorem basisOneDelta_one (δ : K) (hδ : δ ∉ Set.range (algebraMap k K)) (hK : Module.finrank k K = 2) :
    basisOneDelta δ hδ hK 1 = δ := by
  simp [basisOneDelta]

end Basis

section Split

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [NumberField k] {d : k}

/-- **The split case** $E = k\times k$ ($d = c^2$, $c\ne0$): $E\otimes_k\mathbb A_k\cong\mathbb A_k\times\mathbb A_k$,
$x + y\omega\mapsto(x + cy, x - cy)$. -/
def quadSplitHom (c : k) (hd : d = c * c) : QuadAdele k d →+* Adeles k × Adeles k where
  toFun z := (z.re + diagRing k c * z.im, z.re - diagRing k c * z.im)
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    have hc : diagRing k d = diagRing k c * diagRing k c := by rw [hd, map_mul]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero, hc, Prod.mk_mul_mk]
    refine Prod.ext ?_ ?_ <;> ring
  map_zero' := by simp
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> ring

/-- The inverse of the split isomorphism: $(u,v)\mapsto\frac{u+v}2 + \frac{u-v}{2c}\,\omega$. -/
def quadSplitInv (c : k) (p : Adeles k × Adeles k) : QuadAdele k d :=
  ⟨diagRing k (2 : k)⁻¹ * (p.1 + p.2), diagRing k (2 : k)⁻¹ * diagRing k c⁻¹ * (p.1 - p.2)⟩

theorem quadSplitHom_quadSplitInv (c : k) (hc : c ≠ 0) (hd : d = c * c) (p : Adeles k × Adeles k) :
    quadSplitHom (d := d) c hd (quadSplitInv c p) = p := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  set i2 := diagRing k (2 : k)⁻¹
  set ic := diagRing k c⁻¹
  have hi2 : i2 * 2 = 1 := by rw [← map_ofNat (diagRing k) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have hic : ic * diagRing k c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  refine Prod.ext ?_ ?_
  · change i2 * (p.1 + p.2) + diagRing k c * (i2 * ic * (p.1 - p.2)) = p.1
    linear_combination i2 * (p.1 - p.2) * hic + p.1 * hi2
  · change i2 * (p.1 + p.2) - diagRing k c * (i2 * ic * (p.1 - p.2)) = p.2
    linear_combination -(i2 * (p.1 - p.2)) * hic + p.2 * hi2

theorem quadSplitHom_bijective (c : k) (hc : c ≠ 0) (hd : d = c * c) :
    Function.Bijective (quadSplitHom (d := d) c hd) := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  set i2 := diagRing k (2 : k)⁻¹
  set ic := diagRing k c⁻¹
  have hi2 : i2 * 2 = 1 := by rw [← map_ofNat (diagRing k) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have hic : ic * diagRing k c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  refine ⟨fun z w h => ?_, fun p => ⟨quadSplitInv c p, quadSplitHom_quadSplitInv c hc hd p⟩⟩
  have h1 := congrArg Prod.fst h
  have h2' := congrArg Prod.snd h
  change z.re + diagRing k c * z.im = w.re + diagRing k c * w.im at h1
  change z.re - diagRing k c * z.im = w.re - diagRing k c * w.im at h2'
  refine QuadraticAlgebra.ext ?_ ?_
  · linear_combination i2 * h1 + i2 * h2' - (z.re - w.re) * hi2
  · linear_combination (i2 * ic) * h1 - (i2 * ic) * h2' - (z.im - w.im) * (ic * diagRing k c) * hi2 -
      (z.im - w.im) * hic

/-- The split case as a ring isomorphism $E\otimes_k\mathbb A_k\cong\mathbb A_k\times\mathbb A_k$ (`continuous_quadSplit`,
`continuous_quadSplit_symm`: a homeomorphism). -/
def quadSplit (c : k) (hc : c ≠ 0) (hd : d = c * c) : QuadAdele k d ≃+* Adeles k × Adeles k :=
  RingEquiv.ofBijective _ (quadSplitHom_bijective c hc hd)

theorem continuous_quadSplit (c : k) (hc : c ≠ 0) (hd : d = c * c) : Continuous (quadSplit c hc hd) := by
  have h0 := continuous_quad_re d; have h1 := continuous_quad_im d
  change Continuous fun z : QuadAdele k d => (z.re + diagRing k c * z.im, z.re - diagRing k c * z.im)
  fun_prop

theorem continuous_quadSplit_symm (c : k) (hc : c ≠ 0) (hd : d = c * c) :
    Continuous (quadSplit c hc hd).symm := by
  have hf : ((quadSplit c hc hd).symm : Adeles k × Adeles k → QuadAdele k d) = quadSplitInv c :=
    funext fun p => (quadSplit c hc hd).symm_apply_eq.mpr (quadSplitHom_quadSplitInv c hc hd p).symm
  rw [hf]
  refine (continuous_quad_iff d).mpr ⟨?_, ?_⟩ <;> simp only [quadSplitInv] <;> fun_prop

end Split

end

end QuadFormsKB.Tamagawa.Measure.Weil
