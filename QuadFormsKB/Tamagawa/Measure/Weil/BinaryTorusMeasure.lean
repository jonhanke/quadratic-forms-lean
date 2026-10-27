import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusBase
import QuadFormsKB.Tamagawa.Measure.Weil.PDCentre
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeNorm
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume

/-!
# Weil's quotient Tamagawa measure on the torus $T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$ and its covolume $2\rho_E/\rho_F$

**Layer:** number fields. $F$ is a number field, $E = F(\delta)$ a quadratic extension with $F$-basis $(1,\delta)$,
$\delta^2 = d\in F$ (`b 0 = 1`, `b 1 * b 1 = algebraMap F E d`), $G = (E\otimes_F\mathbb A_F)^\times$ = `(QuadAdele F d)ˣ`,
$Z = \mathbb A_F^\times\subset G$ the scalars (`quadScalar`) and $T(\mathbb A) = G/Z$ (`QuadT d`; for $d = -D$ this is
`TorA D`, by definition). Everything is the exact analogue of `PDCentre.lean` (the centre argument of Weil's Thm 3.2.1 for
$PD^\times = D^\times/F^\times$) with the quaternion algebra $D$ replaced by $E$ and its reduced norm by the norm of $E$;
the role of $\operatorname{vol}(\mathbb H^1_{\mathbb A}/\mathbb H^\times) = \rho_F$ is played by
$\operatorname{vol}(\mathbb A_E^1/E^\times) = \rho_E$.

**Defines**
* `quadUnitsBC` : $G\cong\mathbb A_E^\times$ (units of `quadBaseChange`), and `tamQuad` $= $ `tamIdeles E` transported to $G$;
* `quadOne` $= G^1 = \{g : \|g\|_E = 1\}$ (the preimage of $\mathbb A_E^1$), `quadOneEquiv` : $G^1\cong\mathbb A_E^1$, the splitting
  `quadNormSplit` : $G\cong G^1\times\mathbb R_{>0}$ along the central section of scalars $s\mapsto\mathrm{normSection}(s^{1/2})$;
* `quadMk` : $G\to T(\mathbb A)$, `quadKerEquiv` : $\mathbb A_F^\times\cong\ker$, `quadMkOne` : $G^1\to T(\mathbb A)$ with kernel
  `quadKerOneEquiv` $\cong\mathbb A_F^1$;
* `muQuadOne`, `muZQuad`, `muZQuadOne`, **`muTorOne`** (the norm-one quotient $\mu^1_E/\mu^1_F$) and **`muTor`** $=2\mu^1_T$,
  Weil's quotient measure `tamQuad`/`tamIdeles F` on $T(\mathbb A)$;
* `quadUnitsSub` $= E^\times\subseteq G$, `quadGamma d` $= T(F) = $ image of $E^\times$ in $T(\mathbb A)$ (`torGamma D` is
  `quadGamma (dD D)` by `rfl`).

**Proves**
* `ideleNorm_quadUnitsBC_quadScalar`: $\|c\|_E = \|c\|_F^2$ on scalars ($[E:F] = 2$);
* `map_quadNormSplit_tamQuad` : $(\text{split})_*\mu_G = \mu^1_E\times dt/t$ for the section of scalars (a shear argument
  comparing with the section of $E$);
* **`fibMeas_muTor`**: $\int_G f\,d\mu_G = \int_T\int_Z f(gz)\,d\mu_Z(z)\,d\mu_T(gZ)$, i.e. `NormalFib.fibMeas` of `muTor` and
  `muZQuad` is `tamQuad`; `isHaarMeasure_muTor`; **`muTor_unique`**. The factor $2$ is Weil's: on the centre
  $\|z\|_E = \|z\|_F^2$, so $dt/t$ in $t = \|z\|_F$ is twice $dt/t$ in $\|z\|_E$ (`fibMeas_muTorOne_full`: the fibration of $\mu^1_T$
  is $\tfrac12\mu_G$);
* `quadScalar_mem_quadUnitsSub_iff`: $\mathbb A_F^\times\cap E^\times = F^\times$; `quadUnitsSub_le_quadOne`: $E^\times\subseteq G^1$
  (product formula for $E$); `mem_quadUnitsSub_iff`: $g\in E^\times$ iff $\Phi(g)$ is principal;
* **`covolume_muTor`**: $\operatorname{vol}(T(F)\backslash T(\mathbb A),\mu_T) = 2\rho_E/\rho_F$, from Weil's fibration of
  $E^\times\backslash G^1$ over $T(F)\backslash T(\mathbb A)$ with fibre $F^\times\backslash\mathbb A_F^1$
  (`muIdeleClass_eq_mul_muTorOne`) and `muIdeleClass_univ_eq_residue` for $E$ and for $F$.
  *Hypothesis:* `[DiscreteTopology (quadGamma d)]` ($T(F)$ is discrete in $T(\mathbb A)$; it is needed only to have an exact
  fundamental domain, and is obtained by transport from `discreteTopology_GammaSOAdele`).

**Source:** Weil 1982, Thm 3.2.1 (p. 43) and §2.4 (Thm 2.4.4) [unverified page]; Ono 1963 [unverified].
-/

open MeasureTheory Measure Set Function IsDedekindDomain NumberField
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]



section Scalars

variable (d : F)

theorem val_quadScalar (c : (Adeles F)ˣ) :
    ((quadScalar d c : (QuadAdele F d)ˣ) : QuadAdele F d) = algebraMap (Adeles F) (QuadAdele F d) c := rfl

@[simp] theorem re_quadScalar (c : (Adeles F)ˣ) :
    ((quadScalar d c : (QuadAdele F d)ˣ) : QuadAdele F d).re = c := by
  rw [val_quadScalar, QuadraticAlgebra.algebraMap_re]

@[simp] theorem im_quadScalar (c : (Adeles F)ˣ) :
    ((quadScalar d c : (QuadAdele F d)ˣ) : QuadAdele F d).im = 0 := by
  rw [val_quadScalar, QuadraticAlgebra.algebraMap_im]

theorem continuous_algebraMap_quad : Continuous (algebraMap (Adeles F) (QuadAdele F d)) := by
  refine (continuous_quad_iff d).2 ⟨?_, ?_⟩
  · simp only [QuadraticAlgebra.algebraMap_re]; exact continuous_id
  · simp only [QuadraticAlgebra.algebraMap_im]; exact continuous_const

theorem continuous_quadScalar : Continuous (quadScalar d) :=
  Units.continuous_iff.mpr ⟨(continuous_algebraMap_quad d).comp Units.continuous_val,
    (continuous_algebraMap_quad d).comp Units.continuous_coe_inv⟩

/-- The scalars are the units with vanishing $\omega$-coordinate. -/
theorem mem_range_quadScalar_iff (g : (QuadAdele F d)ˣ) :
    g ∈ (quadScalar d).range ↔ (g : QuadAdele F d).im = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h1
    have hre : ∀ h : QuadAdele F d, (g * h : QuadAdele F d).re = (g : QuadAdele F d).re * h.re := by
      intro h; simp [QuadraticAlgebra.re_mul, h1]
    have hu1 : (g : QuadAdele F d).re * ((g⁻¹ : (QuadAdele F d)ˣ) : QuadAdele F d).re = 1 := by
      rw [← hre, Units.mul_inv, QuadraticAlgebra.re_one]
    let c : (Adeles F)ˣ := ⟨(g : QuadAdele F d).re, ((g⁻¹ : (QuadAdele F d)ˣ) : QuadAdele F d).re, hu1,
      by rw [mul_comm]; exact hu1⟩
    refine ⟨c, Units.ext ?_⟩
    exact QuadraticAlgebra.ext (by simp [c]) (by simp [h1])

theorem isClosed_range_quadScalar : IsClosed ((quadScalar d).range : Set (QuadAdele F d)ˣ) := by
  have : ((quadScalar d).range : Set (QuadAdele F d)ˣ) =
      (fun g : (QuadAdele F d)ˣ => (g : QuadAdele F d).im) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_preimage, mem_singleton_iff]
    exact mem_range_quadScalar_iff d g
  rw [this]
  exact isClosed_singleton.preimage ((continuous_quad_im d).comp Units.continuous_val)

instance : IsClosed ((quadScalar d).range : Set (QuadAdele F d)ˣ) := isClosed_range_quadScalar d

theorem quadScalar_injective : Function.Injective (quadScalar d) := by
  intro c e h
  have := congrArg (fun g : (QuadAdele F d)ˣ => (g : QuadAdele F d).re) h
  simp only [re_quadScalar] at this
  exact Units.ext this

/-- The scalar part (inverse of `quadScalar` on its range). -/
def quadScalarPart (g : (quadScalar d).range) : (Adeles F)ˣ := (Classical.choose g.2)

theorem quadScalar_quadScalarPart (g : (quadScalar d).range) : quadScalar d (quadScalarPart d g) = g :=
  Classical.choose_spec g.2

theorem coe_quadScalarPart (g : (quadScalar d).range) :
    ((quadScalarPart d g : (Adeles F)ˣ) : Adeles F) = ((g : (QuadAdele F d)ˣ) : QuadAdele F d).re := by
  conv_rhs => rw [← quadScalar_quadScalarPart d g]
  rw [re_quadScalar]

/-- **$\mathbb A_F^\times\cong Z$ as topological groups.** -/
def quadScalarEquiv : (Adeles F)ˣ ≃ₜ* (quadScalar d).range where
  toFun c := ⟨quadScalar d c, c, rfl⟩
  invFun := quadScalarPart d
  left_inv c := quadScalar_injective d (quadScalar_quadScalarPart d _)
  right_inv g := Subtype.ext (quadScalar_quadScalarPart d g)
  map_mul' c e := Subtype.ext (map_mul _ c e)
  continuous_toFun := (continuous_quadScalar d).subtype_mk _
  continuous_invFun := by
    have hinv : ∀ g : (quadScalar d).range, quadScalarPart d g⁻¹ = (quadScalarPart d g)⁻¹ := fun g =>
      quadScalar_injective d
        (by rw [map_inv (quadScalar d), quadScalar_quadScalarPart, quadScalar_quadScalarPart, Subgroup.coe_inv])
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun g : (quadScalar d).range => ((quadScalarPart d g : (Adeles F)ˣ) : Adeles F)
      simp_rw [coe_quadScalarPart]
      exact (continuous_quad_re d).comp (Units.continuous_val.comp continuous_subtype_val)
    · show Continuous fun g : (quadScalar d).range => (((quadScalarPart d g)⁻¹ : (Adeles F)ˣ) : Adeles F)
      simp_rw [← hinv, coe_quadScalarPart, Subgroup.coe_inv]
      exact (continuous_quad_re d).comp (Units.continuous_coe_inv.comp continuous_subtype_val)

@[simp] theorem coe_quadScalarEquiv (c : (Adeles F)ˣ) :
    ((quadScalarEquiv d c : (quadScalar d).range) : (QuadAdele F d)ˣ) = quadScalar d c := rfl

theorem quadScalar_quadScalarEquiv_symm (g : (quadScalar d).range) :
    quadScalar d ((quadScalarEquiv d).symm g) = g :=
  congrArg Subtype.val ((quadScalarEquiv d).apply_symm_apply g)

end Scalars

/-! ### The quotient $T(\mathbb A)$ -/

section Quotient

variable (d : F)

/-- $T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$ for a general $d$ (`TorA D` is the case $d = -D$). -/
abbrev QuadT : Type := (QuadAdele F d)ˣ ⧸ (quadScalar d).range

instance : MeasurableSpace (QuadAdele F d)ˣ := borel _
instance : BorelSpace (QuadAdele F d)ˣ := ⟨rfl⟩
instance : MeasurableSpace (QuadT d) := borel _
instance : BorelSpace (QuadT d) := ⟨rfl⟩

instance : StandardBorelSpace (QuadAdele F d)ˣ := by
  have := polishSpace_of_isTopologicalGroup ((QuadAdele F d)ˣ)
  infer_instance

/-- The projection $N : G\to T(\mathbb A)$. -/
abbrev quadMk : (QuadAdele F d)ˣ →* QuadT d := QuotientGroup.mk' _

theorem quadMk_surjective : Function.Surjective (quadMk d) := QuotientGroup.mk'_surjective _

theorem continuous_quadMk : Continuous (quadMk d) := continuous_quot_mk

theorem measurable_quadMk : Measurable (quadMk d) := (continuous_quadMk d).measurable

theorem mem_ker_quadMk {g : (QuadAdele F d)ˣ} : g ∈ (quadMk d).ker ↔ g ∈ (quadScalar d).range := by
  rw [QuotientGroup.ker_mk']

theorem isClosed_ker_quadMk : IsClosed ((quadMk d).ker : Set (QuadAdele F d)ˣ) := by
  rw [QuotientGroup.ker_mk']; exact isClosed_range_quadScalar d

/-- **$\mathbb A_F^\times\cong\ker N = Z$.** -/
def quadKerEquiv : (Adeles F)ˣ ≃ₜ* (quadMk d).ker where
  toFun c := ⟨quadScalar d c, (mem_ker_quadMk d).2 ⟨c, rfl⟩⟩
  invFun k := (quadScalarEquiv d).symm ⟨(k : (QuadAdele F d)ˣ), (mem_ker_quadMk d).1 k.2⟩
  left_inv c := (quadScalarEquiv d).symm_apply_apply c
  right_inv k := Subtype.ext (by
    change ((quadScalarEquiv d ((quadScalarEquiv d).symm ⟨(k : (QuadAdele F d)ˣ), (mem_ker_quadMk d).1 k.2⟩) :
      (quadScalar d).range) : (QuadAdele F d)ˣ) = k
    rw [(quadScalarEquiv d).apply_symm_apply])
  map_mul' c e := Subtype.ext (map_mul _ c e)
  continuous_toFun := (continuous_quadScalar d).subtype_mk _
  continuous_invFun := (quadScalarEquiv d).symm.continuous.comp (continuous_subtype_val.subtype_mk _)

@[simp] theorem coe_quadKerEquiv (c : (Adeles F)ˣ) :
    ((quadKerEquiv d c : (quadMk d).ker) : (QuadAdele F d)ˣ) = quadScalar d c := rfl

end Quotient


section Sections

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}

theorem adeleLmat_adeleMap (c : Adeles F) :
    adeleLmat b (adeleMap F E c) = Matrix.scalar (Fin 2) c :=
  adeleLmat_ext b fun a => by
    rw [adeleBaseChange_mulVec_adeleLmat, ← adeleBaseChange_smul]
    congr 1
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Sections

section HalfLog

/-- $s\mapsto s^{1/2}$ on $\mathbb R_{>0}$ (logarithmically, $s\mapsto s/2$). -/
def halfLog : Multiplicative ℝ →* Multiplicative ℝ where
  toFun s := Multiplicative.ofAdd (Multiplicative.toAdd s / 2)
  map_one' := by simp
  map_mul' s t := by rw [toAdd_mul, add_div]; rfl

theorem continuous_halfLog : Continuous halfLog :=
  continuous_ofAdd.comp (continuous_toAdd.div_const 2)

theorem halfLog_mul_self (s : Multiplicative ℝ) : halfLog s * halfLog s = s := by
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd s / 2 + Multiplicative.toAdd s / 2 = Multiplicative.toAdd s
  ring

/-- The central section $s\mapsto\operatorname{normSection}(s^{1/2})$ of $\|\cdot\|_E$ on the scalars (as
$\|c\|_E = \|c\|_F^2$). -/
def quadSectionHom (d : F) : Multiplicative ℝ →* (QuadAdele F d)ˣ :=
  (quadScalar d).comp ((normSectionHom F).comp halfLog)


theorem continuous_quadSectionHom (d : F) : Continuous (quadSectionHom d) :=
  (continuous_quadScalar d).comp (continuous_normSectionHom.comp continuous_halfLog)

theorem quadSectionHom_mem (d : F) (t : Multiplicative ℝ) : quadSectionHom d t ∈ (quadScalar d).range := ⟨_, rfl⟩

theorem halfLog_sq (t : Multiplicative ℝ) : halfLog (t ^ 2) = t := by
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (t ^ 2) / 2 = Multiplicative.toAdd t
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  ring

theorem quadSectionHom_sq (d : F) (t : Multiplicative ℝ) :
    quadSectionHom d (t ^ 2) = quadScalar d (normSectionHom F t) := by
  change quadScalar d (normSectionHom F (halfLog (t ^ 2))) = _
  rw [halfLog_sq]

end HalfLog


section BaseChange

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {d : F} {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E d)

include hb0 hb1

/-- **$(E\otimes\mathbb A_F)^\times\cong\mathbb A_E^\times$** (units of `quadBaseChange`). -/
def quadUnitsBC : (QuadAdele F d)ˣ ≃ₜ* (Adeles E)ˣ where
  toFun := Units.map (quadBaseChange hb0 hb1).toMonoidHom
  invFun := Units.map (quadBaseChange hb0 hb1).symm.toMonoidHom
  left_inv g := Units.ext (by simp)
  right_inv g := Units.ext (by simp)
  map_mul' g h := map_mul _ g h
  continuous_toFun := Units.continuous_iff.mpr ⟨(continuous_quadBaseChange hb0 hb1).comp Units.continuous_val,
    (continuous_quadBaseChange hb0 hb1).comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr ⟨(continuous_quadBaseChange_symm hb0 hb1).comp Units.continuous_val,
    (continuous_quadBaseChange_symm hb0 hb1).comp Units.continuous_coe_inv⟩

theorem coe_quadUnitsBC (g : (QuadAdele F d)ˣ) :
    ((quadUnitsBC hb0 hb1 g : (Adeles E)ˣ) : Adeles E) = quadBaseChange hb0 hb1 (g : QuadAdele F d) := rfl

/-- **Weil's Tamagawa measure on $(E\otimes\mathbb A_F)^\times$**: `tamIdeles E` transported by `quadUnitsBC`. -/
def tamQuad : Measure (QuadAdele F d)ˣ := (tamIdeles E).map (quadUnitsBC hb0 hb1).symm

instance : (tamQuad hb0 hb1).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

theorem quadUnitsBC_quadScalar (c : (Adeles F)ˣ) :
    ((quadUnitsBC hb0 hb1 (quadScalar d c) : (Adeles E)ˣ) : Adeles E) = adeleMap F E (c : Adeles F) := by
  rw [coe_quadUnitsBC, val_quadScalar, quadBaseChange_apply]
  simp [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]

theorem adeleNorm_quadUnitsBC_quadScalar (c : (Adeles F)ˣ) :
    adeleNorm b (quadUnitsBC hb0 hb1 (quadScalar d c)) = c ^ 2 := by
  refine Units.ext ?_
  change (adeleLmat b ((quadUnitsBC hb0 hb1 (quadScalar d c) : (Adeles E)ˣ) : Adeles E)).det = _
  rw [quadUnitsBC_quadScalar, adeleLmat_adeleMap, Matrix.scalar_apply, Matrix.det_diagonal]
  simp [sq]

/-- **On scalars the norm of $\mathbb A_E$ is the square of the norm of $\mathbb A_F$**:
$\|c\|_E = \|c\|_F^2$ ($[E:F] = 2$). -/
@[kb "weil1982" "§2.1, ‖N(z)‖ = ‖z‖² on the centre; Thm 3.2.1, p. 43 [unverified page]"]
theorem ideleNorm_quadUnitsBC_quadScalar (c : (Adeles F)ˣ) :
    ideleNorm E (quadUnitsBC hb0 hb1 (quadScalar d c)) = ideleNorm F c ^ 2 := by
  rw [← ideleNorm_adeleNorm b, adeleNorm_quadUnitsBC_quadScalar, sq, sq, ideleNorm_mul]

/-- $g\mapsto\log\|g\|_E$ (the idele norm of the base-changed element), as a homomorphism to
$\mathbb R_{>0}$ = `Multiplicative ℝ`. -/
def quadLogNorm : (QuadAdele F d)ˣ →* Multiplicative ℝ :=
  (ideleLogNorm E).comp (quadUnitsBC hb0 hb1).toMulEquiv.toMonoidHom

theorem quadLogNorm_apply (g : (QuadAdele F d)ˣ) :
    quadLogNorm hb0 hb1 g = ideleLogNorm E (quadUnitsBC hb0 hb1 g) := rfl

theorem continuous_quadLogNorm : Continuous (quadLogNorm hb0 hb1) :=
  continuous_ideleLogNorm.comp (quadUnitsBC hb0 hb1).continuous

theorem quadLogNorm_quadScalar (c : (Adeles F)ˣ) :
    quadLogNorm hb0 hb1 (quadScalar d c) = ideleLogNorm F c * ideleLogNorm F c := by
  change Multiplicative.ofAdd (Real.log (ideleNorm E (quadUnitsBC hb0 hb1 (quadScalar d c)))) =
    Multiplicative.ofAdd (Real.log (ideleNorm F c)) * Multiplicative.ofAdd (Real.log (ideleNorm F c))
  rw [ideleNorm_quadUnitsBC_quadScalar, sq, Real.log_mul (ideleNorm_pos c).ne' (ideleNorm_pos c).ne']
  rfl

theorem quadLogNorm_quadSectionHom (s : Multiplicative ℝ) :
    quadLogNorm hb0 hb1 (quadSectionHom d s) = s := by
  change quadLogNorm hb0 hb1 (quadScalar d (normSectionHom F (halfLog s))) = s
  rw [quadLogNorm_quadScalar, ideleLogNorm_normSectionHom, halfLog_mul_self]

/-- **$G^1 = \{g \in (E\otimes\mathbb A_F)^\times : \|g\|_E = 1\}$** (the preimage of $\mathbb A_E^1$). -/
def quadOne : Subgroup (QuadAdele F d)ˣ := (quadLogNorm hb0 hb1).ker

theorem mem_quadOne {g : (QuadAdele F d)ˣ} : g ∈ quadOne hb0 hb1 ↔ ideleNorm E (quadUnitsBC hb0 hb1 g) = 1 := by
  rw [← mem_ideleOne, mem_ideleOne_iff_logNorm]
  exact MonoidHom.mem_ker

theorem isClosed_quadOne : IsClosed (quadOne hb0 hb1 : Set (QuadAdele F d)ˣ) :=
  isClosed_singleton.preimage (continuous_quadLogNorm hb0 hb1)

instance : SecondCountableTopology (quadOne hb0 hb1) := TopologicalSpace.Subtype.secondCountableTopology _

instance : LocallyCompactSpace (quadOne hb0 hb1) :=
  (isClosed_quadOne hb0 hb1).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : StandardBorelSpace (quadOne hb0 hb1) := by
  have := polishSpace_of_isTopologicalGroup (quadOne hb0 hb1)
  infer_instance

theorem quadLogNorm_symm (y : ideleOne E) :
    quadLogNorm hb0 hb1 ((quadUnitsBC hb0 hb1).symm (y : (Adeles E)ˣ)) = 1 := by
  rw [quadLogNorm_apply, ContinuousMulEquiv.apply_symm_apply]
  exact (mem_ideleOne_iff_logNorm _).1 y.2

/-- **$G^1\cong\mathbb A_E^1$** (restriction of `quadUnitsBC`). -/
def quadOneEquiv : quadOne hb0 hb1 ≃ₜ* ideleOne E where
  toFun g := ⟨quadUnitsBC hb0 hb1 g, (mem_ideleOne_iff_logNorm _).2 g.2⟩
  invFun y := ⟨(quadUnitsBC hb0 hb1).symm y, quadLogNorm_symm hb0 hb1 y⟩
  left_inv g := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (map_mul _ (g : (QuadAdele F d)ˣ) h)
  continuous_toFun := ((quadUnitsBC hb0 hb1).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((quadUnitsBC hb0 hb1).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_quadOneEquiv (g : quadOne hb0 hb1) :
    ((quadOneEquiv hb0 hb1 g : ideleOne E) : (Adeles E)ˣ) = quadUnitsBC hb0 hb1 (g : (QuadAdele F d)ˣ) := rfl

@[simp] theorem coe_quadOneEquiv_symm (y : ideleOne E) :
    (((quadOneEquiv hb0 hb1).symm y : quadOne hb0 hb1) : (QuadAdele F d)ˣ) =
      (quadUnitsBC hb0 hb1).symm (y : (Adeles E)ˣ) := rfl

set_option maxHeartbeats 1000000 in
/-- **$G\cong G^1\times\mathbb R_{>0}$** via $\|\cdot\|_E$ with the section of scalars `quadSectionHom`. -/
def quadNormSplit : (QuadAdele F d)ˣ ≃ₜ* (quadOne hb0 hb1 × Multiplicative ℝ) :=
  splitEquiv (quadLogNorm hb0 hb1) (quadSectionHom d) (quadOne hb0 hb1) (fun _ => MonoidHom.mem_ker)
    (quadLogNorm_quadSectionHom hb0 hb1) (fun _ _ => mul_comm _ _) (continuous_quadLogNorm hb0 hb1)
    (continuous_quadSectionHom d)

theorem quadNormSplit_apply_snd (g : (QuadAdele F d)ˣ) :
    (quadNormSplit hb0 hb1 g).2 = Multiplicative.ofAdd (Real.log (ideleNorm E (quadUnitsBC hb0 hb1 g))) := rfl

/-! ### The measures on $G$ and $G^1$ -/

/-- **The Haar measure $\mu^1_E$ on $G^1\cong\mathbb A_E^1$**: `muIdeleOne E` transported. -/
def muQuadOne : Measure (quadOne hb0 hb1) := (muIdeleOne E).map (quadOneEquiv hb0 hb1).symm

instance : (muQuadOne hb0 hb1).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

/-- The section of $\|\cdot\|_E$ coming from $E$: $s\mapsto\Phi^{-1}(\operatorname{normSection}_E(s))$. -/
def quadSectionE : Multiplicative ℝ →* (QuadAdele F d)ˣ :=
  (quadUnitsBC hb0 hb1).symm.toMulEquiv.toMonoidHom.comp (normSectionHom E)

theorem quadLogNorm_quadSectionE (s : Multiplicative ℝ) : quadLogNorm hb0 hb1 (quadSectionE hb0 hb1 s) = s := by
  rw [quadLogNorm_apply]
  change ideleLogNorm E ((quadUnitsBC hb0 hb1) ((quadUnitsBC hb0 hb1).symm (normSectionHom E s))) = s
  rw [ContinuousMulEquiv.apply_symm_apply, ideleLogNorm_normSectionHom]

theorem continuous_quadSectionE : Continuous (quadSectionE hb0 hb1) :=
  (quadUnitsBC hb0 hb1).symm.continuous.comp continuous_normSectionHom

set_option maxHeartbeats 1000000 in
/-- The splitting of $G$ through the section of $E$ (the transport of `ideleSplit E`). -/
def quadSplitE : (QuadAdele F d)ˣ ≃ₜ* (quadOne hb0 hb1 × Multiplicative ℝ) :=
  splitEquiv (quadLogNorm hb0 hb1) (quadSectionE hb0 hb1) (quadOne hb0 hb1) (fun _ => MonoidHom.mem_ker)
    (quadLogNorm_quadSectionE hb0 hb1) (fun _ _ => mul_comm _ _) (continuous_quadLogNorm hb0 hb1)
    (continuous_quadSectionE hb0 hb1)

theorem quadSplitE_eq (g : (QuadAdele F d)ˣ) :
    quadSplitE hb0 hb1 g = ((quadOneEquiv hb0 hb1).symm (ideleSplit E (quadUnitsBC hb0 hb1 g)).1,
      (ideleSplit E (quadUnitsBC hb0 hb1 g)).2) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  change g * (quadSectionE hb0 hb1 (quadLogNorm hb0 hb1 g))⁻¹ =
    (quadUnitsBC hb0 hb1).symm (quadUnitsBC hb0 hb1 g * (normSectionHom E (ideleLogNorm E (quadUnitsBC hb0 hb1 g)))⁻¹)
  rw [map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem map_quadSplitE_tamQuad : (tamQuad hb0 hb1).map (quadSplitE hb0 hb1) = (muQuadOne hb0 hb1).prod dtt := by
  have h1 : (quadSplitE hb0 hb1 : (QuadAdele F d)ˣ → _) =
      (fun p : ideleOne E × Multiplicative ℝ => ((quadOneEquiv hb0 hb1).symm p.1, p.2)) ∘ (ideleSplit E) ∘
        (quadUnitsBC hb0 hb1) := funext fun g => quadSplitE_eq hb0 hb1 g
  have hm1 : Measurable (quadOneEquiv hb0 hb1).symm := (quadOneEquiv hb0 hb1).symm.continuous.measurable
  have hmψ : Measurable fun p : ideleOne E × Multiplicative ℝ => ((quadOneEquiv hb0 hb1).symm p.1, p.2) :=
    (hm1.comp measurable_fst).prodMk measurable_snd
  have hq : Measurable (quadSplitE hb0 hb1 : (QuadAdele F d)ˣ → _) := (quadSplitE hb0 hb1).continuous.measurable
  have hΦs : Measurable ((quadUnitsBC hb0 hb1).symm : (Adeles E)ˣ → (QuadAdele F d)ˣ) :=
    (quadUnitsBC hb0 hb1).symm.continuous.measurable
  have hΦ : Measurable (quadUnitsBC hb0 hb1 : (QuadAdele F d)ˣ → (Adeles E)ˣ) :=
    (quadUnitsBC hb0 hb1).continuous.measurable
  rw [tamQuad, Measure.map_map hq hΦs, h1]
  have h2 : ((fun p : ideleOne E × Multiplicative ℝ => ((quadOneEquiv hb0 hb1).symm p.1, p.2)) ∘ (ideleSplit E) ∘
        (quadUnitsBC hb0 hb1)) ∘ (quadUnitsBC hb0 hb1).symm =
      (fun p : ideleOne E × Multiplicative ℝ => ((quadOneEquiv hb0 hb1).symm p.1, p.2)) ∘ (ideleSplit E) := by
    funext g; simp
  have hsp : Measurable (ideleSplit E : (Adeles E)ˣ → _) := (ideleSplit E).continuous.measurable
  rw [h2, ← Measure.map_map hmψ hsp, map_ideleSplit_tamIdeles, muQuadOne]
  have := Measure.map_prod_map (muIdeleOne E) dtt hm1 (measurable_id)
  rw [Measure.map_id] at this
  rw [this]
  rfl

/-- The shear element $c(t) = s_E(t)\,s(t)^{-1}\in G^1$ comparing the two sections. -/
def quadShearElt (t : Multiplicative ℝ) : quadOne hb0 hb1 :=
  ⟨quadSectionE hb0 hb1 t * (quadSectionHom d t)⁻¹, MonoidHom.mem_ker.2 (by
    rw [map_mul, map_inv, quadLogNorm_quadSectionE, quadLogNorm_quadSectionHom, mul_inv_cancel])⟩

theorem continuous_quadShearElt : Continuous (quadShearElt hb0 hb1) :=
  Continuous.subtype_mk ((continuous_quadSectionE hb0 hb1).mul (continuous_quadSectionHom d).inv) _

/-- $(x,t)\mapsto(x\,c(t),t)$. -/
def quadShear (p : quadOne hb0 hb1 × Multiplicative ℝ) : quadOne hb0 hb1 × Multiplicative ℝ :=
  (p.1 * quadShearElt hb0 hb1 p.2, p.2)

theorem quadNormSplit_eq_shear (g : (QuadAdele F d)ˣ) :
    quadNormSplit hb0 hb1 g = quadShear hb0 hb1 (quadSplitE hb0 hb1 g) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  change g * (quadSectionHom d (quadLogNorm hb0 hb1 g))⁻¹ =
    g * (quadSectionE hb0 hb1 (quadLogNorm hb0 hb1 g))⁻¹ *
      (quadSectionE hb0 hb1 (quadLogNorm hb0 hb1 g) * (quadSectionHom d (quadLogNorm hb0 hb1 g))⁻¹)
  simp [mul_assoc]

theorem measurePreserving_quadShear :
    MeasurePreserving (quadShear hb0 hb1) ((muQuadOne hb0 hb1).prod dtt) ((muQuadOne hb0 hb1).prod dtt) := by
  have hmeas : Measurable (Function.uncurry fun (t : Multiplicative ℝ) (x : quadOne hb0 hb1) =>
      x * quadShearElt hb0 hb1 t) :=
    (continuous_snd.mul ((continuous_quadShearElt hb0 hb1).comp continuous_fst)).measurable
  have h1 : MeasurePreserving (fun p : Multiplicative ℝ × quadOne hb0 hb1 =>
      (id p.1, p.2 * quadShearElt hb0 hb1 p.1)) (dtt.prod (muQuadOne hb0 hb1)) (dtt.prod (muQuadOne hb0 hb1)) :=
    MeasurePreserving.skew_product (MeasurePreserving.id dtt) hmeas
      (ae_of_all _ fun t => by
        have : (fun x : quadOne hb0 hb1 => x * quadShearElt hb0 hb1 t) =
            fun x => quadShearElt hb0 hb1 t * x := funext fun x => mul_comm _ _
        rw [this]
        exact MeasureTheory.map_mul_left_eq_self _ _)
  have h2 := (measurePreserving_swap (μ := dtt) (ν := muQuadOne hb0 hb1)).comp h1
  have h3 := h2.comp (measurePreserving_swap (μ := muQuadOne hb0 hb1) (ν := dtt))
  exact h3

@[kb "weil1982" "§2.3 [unverified page] (measure splitting A^× = A^1 × ℝ_{>0}, for the scalar section)"]
theorem map_quadNormSplit_tamQuad :
    (tamQuad hb0 hb1).map (quadNormSplit hb0 hb1) = (muQuadOne hb0 hb1).prod dtt := by
  have hq : Measurable (quadSplitE hb0 hb1 : (QuadAdele F d)ˣ → _) := (quadSplitE hb0 hb1).continuous.measurable
  have h1 : (quadNormSplit hb0 hb1 : (QuadAdele F d)ˣ → _) = quadShear hb0 hb1 ∘ quadSplitE hb0 hb1 :=
    funext fun g => quadNormSplit_eq_shear hb0 hb1 g
  rw [h1, ← Measure.map_map (measurePreserving_quadShear hb0 hb1).measurable hq, map_quadSplitE_tamQuad,
    (measurePreserving_quadShear hb0 hb1).map_eq]

/-! ### The norm-one fibration $G^1\to T(\mathbb A)$ -/

/-- The restriction $N^1 : G^1\to T(\mathbb A)$. -/
def quadMkOne : quadOne hb0 hb1 →* QuadT d := (quadMk d).comp (quadOne hb0 hb1).subtype

theorem quadMkOne_apply (x : quadOne hb0 hb1) : quadMkOne hb0 hb1 x = quadMk d (x : (QuadAdele F d)ˣ) := rfl

theorem quadMkOne_quadNormSplit (g : (QuadAdele F d)ˣ) :
    quadMkOne hb0 hb1 (quadNormSplit hb0 hb1 g).1 = quadMk d g := by
  rw [quadMkOne_apply]
  change quadMk d (g * (quadSectionHom d (quadLogNorm hb0 hb1 g))⁻¹) = _
  exact QuotientGroup.mk_mul_of_mem g ((quadScalar d).range.inv_mem (quadSectionHom_mem d _))

/-- **$G = Z\,G^1$**: $N^1$ is surjective. -/
theorem quadMkOne_surjective : Function.Surjective (quadMkOne hb0 hb1) := fun q => by
  obtain ⟨g, rfl⟩ := quadMk_surjective d q
  exact ⟨_, quadMkOne_quadNormSplit hb0 hb1 g⟩

theorem continuous_quadMkOne : Continuous (quadMkOne hb0 hb1) := (continuous_quadMk d).comp continuous_subtype_val

theorem measurable_quadMkOne : Measurable (quadMkOne hb0 hb1) := (continuous_quadMkOne hb0 hb1).measurable

theorem mem_ker_quadMkOne {x : quadOne hb0 hb1} :
    x ∈ (quadMkOne hb0 hb1).ker ↔ (x : (QuadAdele F d)ˣ) ∈ (quadScalar d).range := by
  rw [MonoidHom.mem_ker, quadMkOne_apply, ← MonoidHom.mem_ker, mem_ker_quadMk]

theorem isClosed_ker_quadMkOne : IsClosed ((quadMkOne hb0 hb1).ker : Set (quadOne hb0 hb1)) := by
  have : ((quadMkOne hb0 hb1).ker : Set (quadOne hb0 hb1)) = Subtype.val ⁻¹' ((quadScalar d).range : Set _) := by
    ext x; exact mem_ker_quadMkOne hb0 hb1
  rw [this]; exact (isClosed_range_quadScalar d).preimage continuous_subtype_val

/-- **A scalar has $\|c\|_E = 1$ iff $\|c\|_F = 1$** (as $\|c\|_E = \|c\|_F^2$). -/
theorem quadScalar_mem_quadOne {c : (Adeles F)ˣ} : quadScalar d c ∈ quadOne hb0 hb1 ↔ c ∈ ideleOne F := by
  rw [mem_quadOne, ideleNorm_quadUnitsBC_quadScalar, mem_ideleOne]
  have := ideleNorm_pos c
  constructor
  · intro h; nlinarith [sq_nonneg (ideleNorm F c - 1)]
  · intro h; rw [h, one_pow]

theorem quadScalarEquiv_symm_mem_ideleOne (k : (quadMkOne hb0 hb1).ker) :
    (quadScalarEquiv d).symm ⟨((k : quadOne hb0 hb1) : (QuadAdele F d)ˣ), (mem_ker_quadMkOne hb0 hb1).1 k.2⟩ ∈
      ideleOne F := by
  rw [← quadScalar_mem_quadOne hb0 hb1, quadScalar_quadScalarEquiv_symm]; exact (k : quadOne hb0 hb1).2

/-- **$\mathbb A_F^1\cong\ker N^1 = Z\cap G^1$.** -/
def quadKerOneEquiv : ideleOne F ≃ₜ* (quadMkOne hb0 hb1).ker where
  toFun u := ⟨⟨quadScalar d u, (quadScalar_mem_quadOne hb0 hb1).2 u.2⟩, (mem_ker_quadMkOne hb0 hb1).2 ⟨u, rfl⟩⟩
  invFun k := ⟨(quadScalarEquiv d).symm ⟨((k : quadOne hb0 hb1) : (QuadAdele F d)ˣ), (mem_ker_quadMkOne hb0 hb1).1 k.2⟩,
    quadScalarEquiv_symm_mem_ideleOne hb0 hb1 k⟩
  left_inv u := Subtype.ext ((quadScalarEquiv d).symm_apply_apply (u : (Adeles F)ˣ))
  right_inv _ := Subtype.ext (Subtype.ext (quadScalar_quadScalarEquiv_symm d _))
  map_mul' u v := Subtype.ext (Subtype.ext (map_mul _ (u : (Adeles F)ˣ) v))
  continuous_toFun := (((continuous_quadScalar d).comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((quadScalarEquiv d).symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _

@[simp] theorem coe_quadKerOneEquiv (u : ideleOne F) :
    (((quadKerOneEquiv hb0 hb1 u : (quadMkOne hb0 hb1).ker) : quadOne hb0 hb1) : (QuadAdele F d)ˣ) =
      quadScalar d u := rfl

/-! ### The measures on the centre and on $T(\mathbb A)$ -/

instance : SecondCountableTopology (quadMk d).ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace (quadMk d).ker :=
  (isClosed_ker_quadMk d).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (quadMkOne hb0 hb1).ker := TopologicalSpace.Subtype.secondCountableTopology _
instance : LocallyCompactSpace (quadMkOne hb0 hb1).ker :=
  (isClosed_ker_quadMkOne hb0 hb1).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit hb0 hb1 in
/-- **The Tamagawa measure of the centre**: `tamIdeles F` on $Z = \ker N$. -/
def muZQuad (d : F) : Measure (quadMk d).ker := (tamIdeles F).map (quadKerEquiv d)

instance : (muZQuad d).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

/-- The measure $\mu^1$ of $\mathbb A_F^1$ on $Z\cap G^1 = \ker N^1$. -/
def muZQuadOne : Measure (quadMkOne hb0 hb1).ker := (muIdeleOne F).map (quadKerOneEquiv hb0 hb1)

instance : (muZQuadOne hb0 hb1).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

omit hb0 hb1 in
/-- A reference Haar measure on $T(\mathbb A)$ (only used to construct `muTorOne`). -/
def muTorRef (d : F) : Measure (QuadT d) := Measure.haar

instance : (muTorRef d).IsHaarMeasure := by unfold muTorRef; infer_instance

/-- The fibred measure on $G^1$ of the reference measure and $\mu^1_Z$. -/
def nuTorRef : Measure (quadOne hb0 hb1) :=
  NormalFib.fibMeas (quadMkOne hb0 hb1) (quadMkOne_surjective hb0 hb1) (muTorRef d) (muZQuadOne hb0 hb1)

theorem isMulLeftInvariant_nuTorRef : (nuTorRef hb0 hb1).IsMulLeftInvariant :=
  NormalFib.isMulLeftInvariant_fibMeas _ _ (measurable_quadMkOne hb0 hb1) _ _

theorem nuTorRef_compact_lt_top {C : Set (quadOne hb0 hb1)} (hC : IsCompact C) : nuTorRef hb0 hb1 C < ∞ :=
  NormalFib.fibMeas_compact_lt_top _ _ (continuous_quadMkOne hb0 hb1) _ _ (isClosed_ker_quadMkOne hb0 hb1) hC

instance isFiniteMeasureOnCompacts_nuTorRef : IsFiniteMeasureOnCompacts (nuTorRef hb0 hb1) :=
  ⟨fun _ hC => nuTorRef_compact_lt_top hb0 hb1 hC⟩

theorem nuTorRef_univ_ne_zero : nuTorRef hb0 hb1 univ ≠ 0 := by
  rw [nuTorRef, NormalFib.fibMeas_univ _ _ (measurable_quadMkOne hb0 hb1)]
  exact mul_ne_zero (isOpen_univ.measure_pos (muZQuadOne hb0 hb1) univ_nonempty).ne'
    (isOpen_univ.measure_pos (muTorRef d) univ_nonempty).ne'

/-- A fixed compact set of positive Haar measure in $G^1$. -/
def quadOneRefSet : Set (quadOne hb0 hb1) :=
  (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quadOne hb0 hb1)))

theorem isCompact_quadOneRefSet : IsCompact (quadOneRefSet hb0 hb1) :=
  (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quadOne hb0 hb1))).isCompact

theorem muQuadOne_refSet_ne_zero : muQuadOne hb0 hb1 (quadOneRefSet hb0 hb1) ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior _
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts (quadOne hb0 hb1))).interior_nonempty).ne'

theorem muQuadOne_refSet_ne_top : muQuadOne hb0 hb1 (quadOneRefSet hb0 hb1) ≠ ∞ :=
  (isCompact_quadOneRefSet hb0 hb1).measure_lt_top.ne

/-- The normalization constant $r$ with $\nu_{\mathrm{ref}} = r\,\mu^1_E$. -/
def torConst : ℝ≥0∞ := nuTorRef hb0 hb1 (quadOneRefSet hb0 hb1) / muQuadOne hb0 hb1 (quadOneRefSet hb0 hb1)

theorem nuTorRef_eq_smul : nuTorRef hb0 hb1 = torConst hb0 hb1 • muQuadOne hb0 hb1 := by
  have := isMulLeftInvariant_nuTorRef hb0 hb1
  exact measure_eq_div_smul _ _ (muQuadOne_refSet_ne_zero hb0 hb1) (muQuadOne_refSet_ne_top hb0 hb1)

theorem torConst_ne_zero : torConst hb0 hb1 ≠ 0 := by
  intro h
  apply nuTorRef_univ_ne_zero hb0 hb1
  rw [nuTorRef_eq_smul hb0 hb1, h, zero_smul]; rfl

theorem torConst_ne_top : torConst hb0 hb1 ≠ ∞ :=
  ENNReal.div_ne_top (nuTorRef_compact_lt_top hb0 hb1 (isCompact_quadOneRefSet hb0 hb1)).ne
    (muQuadOne_refSet_ne_zero hb0 hb1)

/-- **The quotient measure $\mu^1_T = \mu^1_E/\mu^1_F$ on $T(\mathbb A) = G^1/\mathbb A_F^1$** (`fibMeas_muTorOne`). -/
def muTorOne : Measure (QuadT d) := (torConst hb0 hb1)⁻¹ • muTorRef d

theorem isHaarMeasure_muTorOne : (muTorOne hb0 hb1).IsHaarMeasure :=
  IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (torConst_ne_top hb0 hb1))
    (ENNReal.inv_ne_top.2 (torConst_ne_zero hb0 hb1))

/-- **The norm-one fibration identity**: $\mu^1_E = \int_{T(\mathbb A)}(g_q\cdot)_*\mu^1_F\,d\mu^1_T(q)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43"]
theorem fibMeas_muTorOne :
    NormalFib.fibMeas (quadMkOne hb0 hb1) (quadMkOne_surjective hb0 hb1) (muTorOne hb0 hb1) (muZQuadOne hb0 hb1) =
      muQuadOne hb0 hb1 := by
  rw [muTorOne, fibMeas_smul_base _ _ (measurable_quadMkOne hb0 hb1)]
  change (torConst hb0 hb1)⁻¹ • nuTorRef hb0 hb1 = _
  rw [nuTorRef_eq_smul hb0 hb1, smul_smul, ENNReal.inv_mul_cancel (torConst_ne_zero hb0 hb1)
    (torConst_ne_top hb0 hb1), one_smul]

/-! ### The factor $2$: $\mu_T = 2\,\mu^1_T$ -/

theorem quadNormSplit_snd_mul_scalar (x : quadOne hb0 hb1) (u : (Adeles F)ˣ) :
    (quadNormSplit hb0 hb1 ((x : (QuadAdele F d)ˣ) * quadScalar d u)).2 = (ideleSplit F u).2 ^ 2 := by
  rw [quadNormSplit_apply_snd, ideleSplit_apply_snd, map_mul, ideleNorm_mul,
    (mem_quadOne hb0 hb1).1 x.2, one_mul, ideleNorm_quadUnitsBC_quadScalar, sq,
    Real.log_mul (ideleNorm_pos u).ne' (ideleNorm_pos u).ne', sq]
  rfl

theorem quadNormSplit_fst_mul_scalar (x : quadOne hb0 hb1) (u : (Adeles F)ˣ) :
    ((quadNormSplit hb0 hb1 ((x : (QuadAdele F d)ˣ) * quadScalar d u)).1 : (QuadAdele F d)ˣ) =
      (x : (QuadAdele F d)ˣ) * quadScalar d ((ideleSplit F u).1 : (Adeles F)ˣ) := by
  have h2 := quadNormSplit_snd_mul_scalar hb0 hb1 x u
  change (x : (QuadAdele F d)ˣ) * quadScalar d u *
      (quadSectionHom d (quadNormSplit hb0 hb1 ((x : (QuadAdele F d)ˣ) * quadScalar d u)).2)⁻¹ = _
  rw [h2, quadSectionHom_sq, mul_assoc, ← map_inv, ← map_mul]
  rfl

/-- The set $\{u\in\mathbb A_F^\times : x\,u\in S\}$ for the shell
$S = \{g : g\,s(\|g\|_E)^{-1}\in E',\ 1\le\|g\|_E\le e\}$: in the splitting $u = (u^1,\|u\|_F)$ it is
$E''_x\times\{1\le\|u\|_F\le e^{1/2}\}$. -/
theorem preimage_shell_quad (x : quadOne hb0 hb1) (E' : Set (quadOne hb0 hb1)) :
    {u : (Adeles F)ˣ | (x : (QuadAdele F d)ˣ) * quadScalar d u ∈
      quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))} =
    ideleSplit F ⁻¹' (((fun w => x * ((quadKerOneEquiv hb0 hb1 w : (quadMkOne hb0 hb1).ker) : quadOne hb0 hb1)) ⁻¹' E') ×ˢ
      (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) := by
  ext u
  simp only [mem_ofPred_eq, mem_preimage, mem_prod]
  have h1 : (quadNormSplit hb0 hb1 ((x : (QuadAdele F d)ˣ) * quadScalar d u)).1 =
      x * ((quadKerOneEquiv hb0 hb1 (ideleSplit F u).1 : (quadMkOne hb0 hb1).ker) : quadOne hb0 hb1) :=
    Subtype.ext (quadNormSplit_fst_mul_scalar hb0 hb1 x u)
  rw [h1, quadNormSplit_snd_mul_scalar, toAdd_pow, nsmul_eq_mul]
  simp only [mem_Icc]
  constructor
  · rintro ⟨hE, h0, h1⟩; exact ⟨hE, by push_cast at h0; linarith, by push_cast at h1; linarith⟩
  · rintro ⟨hE, h0, h1⟩; exact ⟨hE, by push_cast; linarith, by push_cast; linarith⟩

/-- **The fibre computation**: for $x\in G^1$ and the shell $S$ over $E'\subseteq G^1$,
$\mu_Z\{z : xz\in S\} = \tfrac12\,\mu^1_Z\{k : xk\in E'\}$ (since $\|z\|_E = \|z\|_F^2$). -/
theorem fibK_shell_quad (x : quadOne hb0 hb1) {E' : Set (quadOne hb0 hb1)} (hE : MeasurableSet E') :
    NormalFib.fibK (quadMk d) (muZQuad d) (x : (QuadAdele F d)ˣ)
      (quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) =
      2⁻¹ * NormalFib.fibK (quadMkOne hb0 hb1) (muZQuadOne hb0 hb1) x E' := by
  have hS : MeasurableSet (quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) :=
    (hE.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))).preimage
      (quadNormSplit hb0 hb1).continuous.measurable
  set E'' := (fun w => x * ((quadKerOneEquiv hb0 hb1 w : (quadMkOne hb0 hb1).ker) : quadOne hb0 hb1)) ⁻¹' E' with hE''
  have hE''m : MeasurableSet E'' := hE.preimage
    ((continuous_const.mul (continuous_subtype_val.comp (quadKerOneEquiv hb0 hb1).continuous)).measurable)
  have hT : MeasurableSet (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2)) :=
    (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) (1 / 2)))
  rw [NormalFib.fibK_apply _ _ _ hS, NormalFib.fibK_apply _ _ _ hE]
  have hm1 : Measurable (quadKerEquiv d) := (quadKerEquiv d).continuous.measurable
  have hm2 : Measurable (quadKerOneEquiv hb0 hb1) := (quadKerOneEquiv hb0 hb1).continuous.measurable
  rw [muZQuad, muZQuadOne, Measure.map_apply hm1 (hS.preimage (NormalFib.measurable_mul_val _ _)),
    Measure.map_apply hm2 (hE.preimage (NormalFib.measurable_mul_val _ _))]
  have hset : (quadKerEquiv d) ⁻¹' ((fun k : (quadMk d).ker => (x : (QuadAdele F d)ˣ) * (k : (QuadAdele F d)ˣ)) ⁻¹'
      (quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)))) =
      ideleSplit F ⁻¹' (E'' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) := by
    rw [hE'', ← preimage_shell_quad]
    ext u
    simp only [mem_preimage, mem_ofPred_eq, coe_quadKerEquiv]
  rw [hset]
  have hmeas : (tamIdeles F) (ideleSplit F ⁻¹' (E'' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2)))) =
      ((tamIdeles F).map (ideleSplit F)) (E'' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (1 / 2))) :=
    (Measure.map_apply (ideleSplit F).continuous.measurable (hE''m.prod hT)).symm
  rw [hmeas, map_ideleSplit_tamIdeles, Measure.prod_prod, dtt_toAdd_Icc_half, mul_comm]
  rfl

theorem kern_shell_quad (q : QuadT d) {E' : Set (quadOne hb0 hb1)} (hE : MeasurableSet E') :
    NormalFib.kern (quadMk d) (quadMk_surjective d) (muZQuad d) q
      (quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) =
      2⁻¹ * NormalFib.kern (quadMkOne hb0 hb1) (quadMkOne_surjective hb0 hb1) (muZQuadOne hb0 hb1) q E' := by
  obtain ⟨x, rfl⟩ := quadMkOne_surjective hb0 hb1 q
  rw [NormalFib.kern_apply_N, quadMkOne_apply, NormalFib.kern_apply_N, fibK_shell_quad hb0 hb1 x hE]

/-- **$\mu^1_E(E') = \mu_G(\text{shell over }E')$**, from the splitting `quadNormSplit`. -/
theorem muQuadOne_apply (E' : Set (quadOne hb0 hb1)) (hE : MeasurableSet E') :
    muQuadOne hb0 hb1 E' =
      tamQuad hb0 hb1 (quadNormSplit hb0 hb1 ⁻¹' (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) := by
  have hm : MeasurableSet (E' ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)) :=
    hE.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))
  have hq : Measurable (quadNormSplit hb0 hb1 : (QuadAdele F d)ˣ → _) :=
    (quadNormSplit hb0 hb1).continuous.measurable
  rw [← Measure.map_apply hq hm, map_quadNormSplit_tamQuad, Measure.prod_prod, dtt_ofAdd_Icc, mul_one]

/-- **The full fibration of $\mu^1_T$ is half of `tamQuad`**:
$\int_{T}\int_Z\cdots\,d\mu_Z\,d\mu^1_T = \tfrac12\mu_G$. -/
theorem fibMeas_muTorOne_full :
    NormalFib.fibMeas (quadMk d) (quadMk_surjective d) (muTorOne hb0 hb1) (muZQuad d) =
      (2 : ℝ≥0∞)⁻¹ • tamQuad hb0 hb1 := by
  have := isHaarMeasure_muTorOne hb0 hb1
  set ν := NormalFib.fibMeas (quadMk d) (quadMk_surjective d) (muTorOne hb0 hb1) (muZQuad d) with hν
  have hνl : ν.IsMulLeftInvariant := NormalFib.isMulLeftInvariant_fibMeas _ _ (measurable_quadMk d) _ _
  have hνc : IsFiniteMeasureOnCompacts ν :=
    ⟨fun _ hC => NormalFib.fibMeas_compact_lt_top _ _ (continuous_quadMk d) _ _ (isClosed_ker_quadMk d) hC⟩
  set R := quadOneRefSet hb0 hb1
  have hRm : MeasurableSet R := (isCompact_quadOneRefSet hb0 hb1).isClosed.measurableSet
  set S := quadNormSplit hb0 hb1 ⁻¹' (R ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)) with hS
  have hSm : MeasurableSet S :=
    (hRm.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))).preimage
      (quadNormSplit hb0 hb1).continuous.measurable
  have hT : tamQuad hb0 hb1 S = muQuadOne hb0 hb1 R := (muQuadOne_apply hb0 hb1 R hRm).symm
  have h0 : tamQuad hb0 hb1 S ≠ 0 := hT ▸ muQuadOne_refSet_ne_zero hb0 hb1
  have htop : tamQuad hb0 hb1 S ≠ ∞ := hT ▸ muQuadOne_refSet_ne_top hb0 hb1
  have hνS : ν S = 2⁻¹ * muQuadOne hb0 hb1 R := by
    rw [hν, NormalFib.fibMeas_apply _ _ (measurable_quadMk d) _ _ hSm, hS]
    simp_rw [kern_shell_quad hb0 hb1 _ hRm]
    rw [lintegral_const_mul _ (NormalFib.measurable_kern_apply _ _ (measurable_quadMkOne hb0 hb1) _ hRm),
      ← NormalFib.fibMeas_apply _ _ (measurable_quadMkOne hb0 hb1) _ _ hRm, fibMeas_muTorOne]
  rw [measure_eq_div_smul ν (tamQuad hb0 hb1) h0 htop, hνS, hT,
    ENNReal.mul_div_cancel_right (muQuadOne_refSet_ne_zero hb0 hb1) (muQuadOne_refSet_ne_top hb0 hb1)]

/-- **Weil's Tamagawa measure on $T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$**: the quotient of
`tamQuad` by `tamIdeles F` (`fibMeas_muTor`, `muTor_unique`). It is $2\,\mu^1_T$: the norm-one quotient measure
undercounts by the factor $\int dt/t$ in $t = \|z\|_F$ versus $\|z\|_E = t^2$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43 (centre argument, ‖N(z)‖ = ‖z‖²)"]
def muTor : Measure (QuadT d) := (2 : ℝ≥0∞) • muTorOne hb0 hb1

theorem isHaarMeasure_muTor : (muTor hb0 hb1).IsHaarMeasure := by
  have := isHaarMeasure_muTorOne hb0 hb1
  exact IsHaarMeasure.smul _ two_ne_zero ENNReal.ofNat_ne_top

/-- **The fibration identity defining Weil's measure on $T(\mathbb A)$**:
$\int_G f\,d\mu_G = \int_{G/Z}\int_Z f(gz)\,d\mu_Z(z)\,d\mu_T(gZ)$ with $\mu_G$ = `tamQuad`, $\mu_Z$ = `tamIdeles F`. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]; §3.2, p. 43"]
theorem fibMeas_muTor :
    NormalFib.fibMeas (quadMk d) (quadMk_surjective d) (muTor hb0 hb1) (muZQuad d) = tamQuad hb0 hb1 := by
  rw [muTor, fibMeas_smul_base _ _ (measurable_quadMk d), fibMeas_muTorOne_full, smul_smul,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]

/-- **Uniqueness**: a Haar measure on $T(\mathbb A)$ whose fibred measure with `tamIdeles F` is `tamQuad` is `muTor`. -/
theorem muTor_unique (μ' : Measure (QuadT d)) [μ'.IsHaarMeasure]
    (h : NormalFib.fibMeas (quadMk d) (quadMk_surjective d) μ' (muZQuad d) = tamQuad hb0 hb1) :
    μ' = muTor hb0 hb1 := by
  have := isHaarMeasure_muTor hb0 hb1
  set c := μ'.haarScalarFactor (muTor hb0 hb1)
  have hc : μ' = (c : ℝ≥0∞) • muTor hb0 hb1 := Measure.isMulLeftInvariant_eq_smul _ _
  rw [hc, fibMeas_smul_base _ _ (measurable_quadMk d), fibMeas_muTor] at h
  set R := quadOneRefSet hb0 hb1
  have hRm : MeasurableSet R := (isCompact_quadOneRefSet hb0 hb1).isClosed.measurableSet
  have hT := (muQuadOne_apply hb0 hb1 R hRm).symm
  have h0 := muQuadOne_refSet_ne_zero hb0 hb1
  have htop := muQuadOne_refSet_ne_top hb0 hb1
  set S := quadNormSplit hb0 hb1 ⁻¹' (R ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))
  have := congrArg (fun μ => μ S) h
  simp only [Measure.smul_apply, smul_eq_mul, hT] at this
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h' : (c : ℝ≥0∞) * muQuadOne hb0 hb1 R = 1 * muQuadOne hb0 hb1 R := by
      rw [one_mul]; exact this
    exact (ENNReal.mul_left_inj h0 htop).1 h'
  rw [hc, hc1, one_smul]

/-! ### Global points: $E^\times\cap\mathbb A_F^\times = F^\times$ and $E^\times\subseteq G^1$ -/

omit hb0 hb1 in
/-- **$E^\times$ inside $(E\otimes\mathbb A_F)^\times$**: the image of the diagonal embedding on units. -/
def quadUnitsSub (d : F) : Subgroup (QuadAdele F d)ˣ := (quadDiagUnit d).range

omit hb0 hb1 in
/-- **A scalar idele is a global point of $E$ iff it is a principal idele**: $\mathbb A_F^\times\cap E^\times = F^\times$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 [unverified page]; Thm 3.2.1, p. 43 (A_F^× ∩ E^× = F^×)"]
theorem quadScalar_mem_quadUnitsSub_iff (u : (Adeles F)ˣ) :
    quadScalar d u ∈ quadUnitsSub d ↔ u ∈ diagUnitsSub F := by
  constructor
  · rintro ⟨η, hη⟩
    have hv := congrArg (fun g : (QuadAdele F d)ˣ => (g : QuadAdele F d)) hη
    change quadDiag d (η : QuadraticAlgebra F d 0) = algebraMap (Adeles F) (QuadAdele F d) (u : Adeles F) at hv
    have hre := congrArg QuadraticAlgebra.re hv
    have him := congrArg QuadraticAlgebra.im hv
    simp only [quadDiag, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im] at hre him
    have hI0 : (η : QuadraticAlgebra F d 0).im = 0 :=
      (diagRing F).injective (by rw [him, map_zero])
    have hre0 : (η : QuadraticAlgebra F d 0).re ≠ 0 := by
      intro h0
      apply η.ne_zero
      exact QuadraticAlgebra.ext (by simpa using h0) (by simpa using hI0)
    refine ⟨Units.mk0 _ hre0, Units.ext ?_⟩
    rw [diagUnits_val, Units.val_mk0]
    exact hre
  · rintro ⟨ξ, rfl⟩
    refine ⟨Units.map (algebraMap F (QuadraticAlgebra F d 0)).toMonoidHom ξ, Units.ext ?_⟩
    change quadDiag d (algebraMap F (QuadraticAlgebra F d 0) (ξ : F)) =
      algebraMap (Adeles F) (QuadAdele F d) ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F)
    rw [diagUnits_val]
    refine QuadraticAlgebra.ext ?_ ?_
    · show diag F ((algebraMap F (QuadraticAlgebra F d 0) (ξ : F)).re) = _
      simp
    · simp [quadDiag]

theorem quadUnitsBC_quadDiagUnit (η : (QuadraticAlgebra F d 0)ˣ) :
    quadUnitsBC hb0 hb1 (quadDiagUnit d η) = diagUnits E (Units.map (quadField hb1).toMonoidHom η) :=
  Units.ext (by
    rw [coe_quadUnitsBC, diagUnits_val]
    exact quadBaseChange_quadDiag hb0 hb1 _)

/-- **$E^\times\subseteq G^1$** (the product formula for $E$). -/
theorem quadUnitsSub_le_quadOne : quadUnitsSub d ≤ quadOne hb0 hb1 := by
  rintro _ ⟨η, rfl⟩
  rw [mem_quadOne, quadUnitsBC_quadDiagUnit, ideleNorm_diagUnits]

/-- **$g\in E^\times$ iff its image in $\mathbb A_E^\times$ is principal.** -/
theorem mem_quadUnitsSub_iff (g : (QuadAdele F d)ˣ) :
    g ∈ quadUnitsSub d ↔ quadUnitsBC hb0 hb1 g ∈ diagUnitsSub E := by
  constructor
  · rintro ⟨η, rfl⟩
    exact ⟨_, (quadUnitsBC_quadDiagUnit hb0 hb1 η).symm⟩
  · rintro ⟨ζ, hζ⟩
    let e := RingEquiv.ofBijective (quadField hb1) (quadField_bijective hb0 hb1)
    refine ⟨Units.map e.symm.toMonoidHom ζ, (quadUnitsBC hb0 hb1).injective ?_⟩
    rw [quadUnitsBC_quadDiagUnit, ← hζ]
    congr 1
    refine Units.ext ?_
    exact e.apply_symm_apply (ζ : E)

/-! ### Countability, discreteness and fundamental domains -/

omit hb0 hb1 in
instance countable_quadUnits (d : F) : Countable (QuadraticAlgebra F d 0)ˣ :=
  Function.Injective.countable (f := fun η : (QuadraticAlgebra F d 0)ˣ =>
    (((η : QuadraticAlgebra F d 0).re, (η : QuadraticAlgebra F d 0).im) : F × F))
    fun _ _ h => Units.ext (QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

omit hb0 hb1 in
instance countable_quadUnitsSub (d : F) : Countable (quadUnitsSub d) := by
  have : Function.Surjective fun η : (QuadraticAlgebra F d 0)ˣ => (⟨quadDiagUnit d η, η, rfl⟩ : quadUnitsSub d) := by
    rintro ⟨_, η, rfl⟩; exact ⟨η, rfl⟩
  exact this.countable

/-- **$E^\times$ as a subgroup of $G^1$.** -/
def quadUnitsOne : Subgroup (quadOne hb0 hb1) := (quadUnitsSub d).subgroupOf (quadOne hb0 hb1)

instance : Countable (quadUnitsOne hb0 hb1) :=
  Function.Injective.countable (f := fun x : quadUnitsOne hb0 hb1 =>
    (⟨((x : quadOne hb0 hb1) : (QuadAdele F d)ˣ), x.2⟩ : quadUnitsSub d))
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : quadUnitsSub d => (z : (QuadAdele F d)ˣ)) h))

theorem quadUnitsOne_map_mem (x : quadUnitsOne hb0 hb1) :
    quadUnitsBC hb0 hb1 ((x : quadOne hb0 hb1) : (QuadAdele F d)ˣ) ∈ ideleOne E :=
  (mem_ideleOne).2 ((mem_quadOne hb0 hb1).1 (x : quadOne hb0 hb1).2)

/-- **$E^\times$ is discrete in $G^1$** (it embeds in the discrete $E^\times\subseteq\mathbb A_E^1$). -/
instance : DiscreteTopology (quadUnitsOne hb0 hb1) := by
  refine DiscreteTopology.of_continuous_injective (f := fun x : quadUnitsOne hb0 hb1 =>
    (⟨⟨quadUnitsBC hb0 hb1 ((x : quadOne hb0 hb1) : (QuadAdele F d)ˣ), quadUnitsOne_map_mem hb0 hb1 x⟩,
      Subgroup.mem_subgroupOf.2 ((mem_quadUnitsSub_iff hb0 hb1 _).1 (Subgroup.mem_subgroupOf.1 x.2))⟩ :
        diagUnitsOne E)) ?_ ?_
  · exact (((quadUnitsBC hb0 hb1).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  · intro x y h
    have := congrArg (fun z : diagUnitsOne E => ((z : ideleOne E) : (Adeles E)ˣ)) h
    exact Subtype.ext (Subtype.ext ((quadUnitsBC hb0 hb1).injective this))

theorem quadOneEquiv_symm_mem_iff (y : ideleOne E) :
    (quadOneEquiv hb0 hb1).symm y ∈ quadUnitsOne hb0 hb1 ↔ y ∈ diagUnitsOne E := by
  change ((quadOneEquiv hb0 hb1).symm y : (QuadAdele F d)ˣ) ∈ quadUnitsSub d ↔ (y : (Adeles E)ˣ) ∈ diagUnitsSub E
  rw [mem_quadUnitsSub_iff hb0 hb1, coe_quadOneEquiv_symm, ContinuousMulEquiv.apply_symm_apply]

/-- **An exact fundamental domain of $E^\times$ in $G^1$ of volume $\mathrm{vol}(E^\times\backslash\mathbb A_E^1)$.** -/
theorem exists_exactFD_quadUnitsOne :
    ∃ D : Set (quadOne hb0 hb1), IsExactFD (Γ := quadUnitsOne hb0 hb1) D ∧
      muQuadOne hb0 hb1 D = muIdeleClass E univ := by
  obtain ⟨E0, hE0m, hE0⟩ := exists_measurableSet_forall_existsUnique_smul_mem (diagUnitsOne E)
  refine ⟨(quadOneEquiv hb0 hb1).symm '' E0, isExactFD_image_mulEquiv (quadOneEquiv hb0 hb1).symm.toMulEquiv
    (quadOneEquiv hb0 hb1).continuous.measurable _ _ (quadOneEquiv_symm_mem_iff hb0 hb1) ⟨hE0m, hE0⟩, ?_⟩
  have he : ((quadOneEquiv hb0 hb1).symm : ideleOne E → quadOne hb0 hb1) =
      (quadOneEquiv hb0 hb1).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [muQuadOne, he, MeasurableEquiv.map_apply, ← he,
    (quadOneEquiv hb0 hb1).symm.injective.preimage_image,
    muIdeleClass_univ ((IsExactFD.isFundamentalDomain ⟨hE0m, hE0⟩) _)]

/-- $\mathbb A_F^1\cap F^\times$ inside $\ker N^1$: $F^\times$. -/
abbrev quadGammaZ : Subgroup (quadMkOne hb0 hb1).ker :=
  NormalFib.gammaK (quadMkOne hb0 hb1) (quadUnitsOne hb0 hb1)

theorem quadKerOneEquiv_mem_gammaZ_iff (u : ideleOne F) :
    quadKerOneEquiv hb0 hb1 u ∈ quadGammaZ hb0 hb1 ↔ u ∈ diagUnitsOne F := by
  change ((quadKerOneEquiv hb0 hb1 u : (quadMkOne hb0 hb1).ker) : quadOne hb0 hb1) ∈
      (quadUnitsSub d).subgroupOf (quadOne hb0 hb1) ↔ u ∈ (diagUnitsSub F).subgroupOf (ideleOne F)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_quadKerOneEquiv, quadScalar_mem_quadUnitsSub_iff]

theorem map_adK_muZQuadOne (g : quadOne hb0 hb1) :
    (muZQuadOne hb0 hb1).map (NormalFib.adK (quadMkOne hb0 hb1) g) = muZQuadOne hb0 hb1 := by
  have : NormalFib.adK (quadMkOne hb0 hb1) g = id := by
    funext k
    apply Subtype.ext
    change g * (k : quadOne hb0 hb1) * g⁻¹ = (k : quadOne hb0 hb1)
    rw [mul_comm g, mul_inv_cancel_right]
  rw [this, Measure.map_id]

/-- **An exact fundamental domain of $F^\times$ in $\mathbb A_F^1 = \ker N^1\cap\ldots$ of volume
$\mathrm{vol}(F^\times\backslash\mathbb A_F^1)$.** -/
theorem exists_exactFD_quadGammaZ :
    ∃ DK : Set (quadMkOne hb0 hb1).ker, IsExactFD (Γ := quadGammaZ hb0 hb1) DK ∧
      muZQuadOne hb0 hb1 DK = muIdeleClass F univ := by
  obtain ⟨E0, hEm, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (diagUnitsOne F)
  refine ⟨quadKerOneEquiv hb0 hb1 '' E0, isExactFD_image_mulEquiv (quadKerOneEquiv hb0 hb1).toMulEquiv
    (quadKerOneEquiv hb0 hb1).symm.continuous.measurable _ _ (quadKerOneEquiv_mem_gammaZ_iff hb0 hb1) ⟨hEm, hE⟩, ?_⟩
  have he : ((quadKerOneEquiv hb0 hb1) : ideleOne F → (quadMkOne hb0 hb1).ker) =
      (quadKerOneEquiv hb0 hb1).toHomeomorph.toMeasurableEquiv := rfl
  rw [muZQuadOne, he, MeasurableEquiv.map_apply, ← he, (quadKerOneEquiv hb0 hb1).injective.preimage_image,
    muIdeleClass_univ ((IsExactFD.isFundamentalDomain ⟨hEm, hE⟩) _)]

/-- **$T(F) = N^1(E^\times)$** as a subgroup of $T(\mathbb A)$. -/
abbrev quadGammaT : Subgroup (QuadT d) := NormalFib.gammaQ (quadMkOne hb0 hb1) (quadUnitsOne hb0 hb1)

omit hb0 hb1 in
/-- **The global points $T(F) = E^\times F^\times/F^\times$ inside $T(\mathbb A)$**: the image of $E^\times$
(`TorA D`'s `torGamma D` is the case $d = -D$). -/
abbrev quadGamma (d : F) : Subgroup (QuadT d) := (quadDiagUnit d).range.map (quadMk d)

theorem quadGammaT_eq : quadGammaT hb0 hb1 = quadGamma d := by
  ext q
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(γ : (QuadAdele F d)ˣ), Subgroup.mem_subgroupOf.mp hγ, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, quadUnitsSub_le_quadOne hb0 hb1 hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

omit hb0 hb1 in
instance countable_quadGamma (d : F) : Countable (quadGamma d) := by
  refine Function.Surjective.countable (f := fun g : quadUnitsSub d =>
    (⟨quadMk d g, g, g.2, rfl⟩ : quadGamma d)) ?_
  rintro ⟨_, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

/-! ### The covolume $2\rho_E/\rho_F$ -/

/-- **Weil's fibration of $E^\times\backslash G^1$ over $T(F)\backslash T(\mathbb A)$ with fibre $F^\times\backslash\mathbb A_F^1$**:
$\mathrm{vol}(E^\times\backslash\mathbb A_E^1) = \mathrm{vol}(F^\times\backslash\mathbb A_F^1)\cdot\mu^1_T(D_T)$ for every
exact fundamental domain $D_T$ of $T(F)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]; §3.2, p. 43"]
theorem muIdeleClass_eq_mul_muTorOne {DQ : Set (QuadT d)} (hDQ : IsExactFD (Γ := quadGammaT hb0 hb1) DQ) :
    muIdeleClass E univ = muIdeleClass F univ * muTorOne hb0 hb1 DQ := by
  obtain ⟨D, hD, hDvol⟩ := exists_exactFD_quadUnitsOne hb0 hb1
  obtain ⟨DK, hDK, hDKvol⟩ := exists_exactFD_quadGammaZ hb0 hb1
  have := isHaarMeasure_muTorOne hb0 hb1
  rw [← hDvol, ← hDKvol, ← fibMeas_muTorOne hb0 hb1]
  exact NormalFib.fibMeas_exactFD _ _ (quadUnitsOne hb0 hb1) (measurable_quadMkOne hb0 hb1) _ _
    (map_adK_muZQuadOne hb0 hb1) hD hDK hDQ

/-- **$\mathrm{vol}(T(F)\backslash T(\mathbb A),\mu_T) = 2\rho_E/\rho_F$** for Weil's Tamagawa measure `muTor` on
$T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$, given that $T(F)$ is discrete in $T(\mathbb A)$.
*Proof.* $\rho_E = \rho_F\cdot\mu^1_T(D_T)$ (`muIdeleClass_eq_mul_muTorOne`, with
$\mathrm{vol}(E^\times\backslash\mathbb A_E^1) = \rho_E$ and $\mathrm{vol}(F^\times\backslash\mathbb A_F^1) = \rho_F$ from
`muIdeleClass_univ_eq_residue`), and $\mu_T = 2\mu^1_T$. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (centre argument); §2.4, Thm 2.4.4 [unverified page]"]
theorem covolume_muTor [DiscreteTopology (quadGamma d)] :
    covolume (quadGamma d) (QuadT d) (muTor hb0 hb1) =
      2 * (ENNReal.ofReal (dedekindZeta_residue E) / ENNReal.ofReal (dedekindZeta_residue F)) := by
  have hH := isHaarMeasure_muTor hb0 hb1
  obtain ⟨DQ, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (quadGamma d)
  have hDQ : IsExactFD (Γ := quadGamma d) DQ := ⟨hDm, hD⟩
  have hDQ' : IsExactFD (Γ := quadGammaT hb0 hb1) DQ := by rw [quadGammaT_eq hb0 hb1]; exact hDQ
  have h1 := muIdeleClass_eq_mul_muTorOne hb0 hb1 hDQ'
  rw [muIdeleClass_univ_eq_residue, muIdeleClass_univ_eq_residue] at h1
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact dedekindZeta_residue_pos F
  have hx : muTorOne hb0 hb1 DQ = ENNReal.ofReal (dedekindZeta_residue E) / ENNReal.ofReal (dedekindZeta_residue F) :=
    (ENNReal.eq_div_iff hρ0 ENNReal.ofReal_ne_top).2 h1.symm
  have : SMulInvariantMeasure (quadGamma d) (QuadT d) (muTor hb0 hb1) :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  rw [(hDQ.isFundamentalDomain _).covolume_eq_volume, muTor, Measure.smul_apply, hx, smul_eq_mul]

end BaseChange

/-! ### The case $d = -D$: `TorA D` and `torGamma D` -/

section TorA

variable {D : 𝓞 F} {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

omit hb0 hb1 in
/-- `torGamma D` is `quadGamma (dD D)`, and `TorA D` is `QuadT (dD D)` (by definition). -/
theorem torGamma_eq_quadGamma (D : 𝓞 F) : torGamma D = quadGamma (dD D) := rfl

/-- **$\operatorname{vol}(T(F)\backslash T(\mathbb A),\mu_T) = 2\rho_E/\rho_F$ for $T = R_{E/F}\mathbb G_m/\mathbb G_m$,
$E = F(\sqrt{-D})$**, Weil's Tamagawa measure `muTor` on `TorA D`, given that `torGamma D` is discrete. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (centre argument); §2.4, Thm 2.4.4 [unverified page]"]
theorem covolume_muTor_torGamma [DiscreteTopology (torGamma D)] :
    covolume (torGamma D) (TorA D) (muTor hb0 hb1) =
      2 * (ENNReal.ofReal (dedekindZeta_residue E) / ENNReal.ofReal (dedekindZeta_residue F)) :=
  covolume_muTor hb0 hb1

end TorA

end

end QuadFormsKB.Tamagawa.Measure.Weil
