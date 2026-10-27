import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusLocal
import QuadFormsKB.Tamagawa.Measure.Weil.PDMeasure

/-!
# The adelic isomorphism $(E\otimes\mathbb A_F)^\times/\mathbb A_F^\times\cong SO(\langle1,D\rangle)(\mathbb A)$ and the global points

**Layer:** number fields. $F$ is a number field, $D\in\mathcal O_F\setminus0$, $Q_0 = \langle1,D\rangle$ = `diagForm1 D`,
$d = -D$ = `dD D`, $E = F[\omega]$, $\omega^2 = d$ (a field iff $-D$ is not a square; the statements below do not need this),
$E\otimes\mathbb A_F$ = `QuadAdele F d`, and $V = (F^2, \langle1,D\rangle)$. Any signature, any number field.
Template: `PDArch`, `PDAdelic`, `PDGlobal` for $D^\times/F^\times\cong SO_3$.

**Defines**
* `QuadInf F d` $= E\otimes F_\infty = F_\infty[\omega]$ (`QuadraticAlgebra (mixedSpace F) …`), `QuadFin F d` $= E\otimes\mathbb A_f$,
  `QuadV F d v` $= E\otimes F_v$, each with the topology of its coordinates $(\mathrm{re},\mathrm{im})$; `quadAdeleRingEquiv` and
  **`quadUnitsSplit`** $: (E\otimes\mathbb A_F)^\times\cong_{\mathrm{top.\ grp.}}(E\otimes F_\infty)^\times\times(E\otimes\mathbb A_f)^\times$
  (with simp lemmas for the coordinates of both directions); the scalars `infScalarQ`, `finScalarQ`;
* the projections `projQR`, `projQC` (to $\mathbb R[\omega]$, $\mathbb C[\omega]$ at the real and complex places) and `projQV`
  (to $F_v[\omega]$), and `unitAtD v` on units;
* **`torInf`** $: (E\otimes F_\infty)^\times\to G_\infty$ (`GInfSO`), **`torFin`** $: (E\otimes\mathbb A_f)^\times\to SO(V)(\mathbb A_f)$
  and **`torAdele`** $=$ (`torInf` $\times$ `torFin`) $\circ$ `quadUnitsSplit`, $z\mapsto(\mathrm{tor}(z_w))_w$ with
  $\mathrm{tor}(z)$ = the matrix of multiplication by $z/\bar z$ in the basis $(1,\omega)$ (`BinaryTorusLocal`);
* **`torAdeleEquiv`** $: T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times\cong SO(V)(\mathbb A)$ (topological groups);
* the global points `torF` $: E^\times\to SO(V)(F)$.

**Proves**
* `continuous_torInf`, `continuous_torFin` (on the open subgroup $\hat{\mathcal O}[\omega]^\times$ it factors through
  $\prod_vO(\mathfrak o_v^2)$), `continuous_torAdele`;
* `torInf_surjective`, `torFin_surjective` (integral lifts at the cofinitely many good places, `exists_integral_lift`),
  **`torAdele_surjective`**; **`torAdele_eq_one_iff`** / `ker_torAdele` (kernel $=\mathbb A_F^\times$); **`isOpenMap_torAdele`**
  (open mapping theorem for $\sigma$-compact groups);
* `torF_surjective` (Hilbert 90 over $F$), **`torAdele_diag`** ($\mathrm{tor}_{\mathbb A}(\xi) = (\mathrm{tor}_F(\xi))_{\mathrm{diag}}$),
  **`map_torGamma`**: $T(F) = E^\times\mathbb A_F^\times/\mathbb A_F^\times$ maps onto $\Gamma = SO(V)(F)$ = `GammaSOAdele`.

Source: Weil 1982, §2.4 (adelic points of the torus $R_{E/F}\mathbb G_m/\mathbb G_m\cong SO_2$, $G_k\subset G_{\mathbb A}$ discrete)
[unverified locator]; Ono 1963 (Tamagawa numbers of tori) [unverified].
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology Filter Matrix
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### $E\otimes F_\infty$ and $E\otimes\mathbb A_f$ -/

section InfFin

variable (F) in
/-- $E\otimes_FF_\infty = F_\infty[\omega]$, $\omega^2 = d$: `QuadraticAlgebra (mixedSpace F) d 0`. -/
abbrev QuadInf (d : F) : Type := QuadraticAlgebra (mixedSpace F) (mixedEmbedding F d) 0

variable (F) in
/-- $E\otimes_F\mathbb A_f = \mathbb A_f[\omega]$, $\omega^2 = d$: `QuadraticAlgebra AF d 0`. -/
abbrev QuadFin (d : F) : Type := QuadraticAlgebra AF (algebraMap F AF d) 0

variable (F) in
/-- $E\otimes_FF_v = F_v[\omega]$, $\omega^2 = d$, at a finite place $v$. -/
abbrev QuadV (d : F) (v : HeightOneSpectrum (𝓞 F)) : Type :=
  QuadraticAlgebra (v.adicCompletion F) (algebraMap F (v.adicCompletion F) d) 0

variable (d : F)

instance : TopologicalSpace (QuadInf F d) := TopologicalSpace.induced (fun z => (z.re, z.im)) inferInstance

instance : TopologicalSpace (QuadFin F d) := TopologicalSpace.induced (fun z => (z.re, z.im)) inferInstance

theorem continuous_quadInf_iff {X : Type*} [TopologicalSpace X] {f : X → QuadInf F d} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).im) :=
  ⟨fun h => ⟨(continuous_fst.comp (continuous_induced_dom (f := fun z : QuadInf F d => (z.re, z.im)))).comp h,
      (continuous_snd.comp (continuous_induced_dom (f := fun z : QuadInf F d => (z.re, z.im)))).comp h⟩,
    fun ⟨h0, h1⟩ => continuous_induced_rng.mpr (h0.prodMk h1)⟩

theorem continuous_quadFin_iff {X : Type*} [TopologicalSpace X] {f : X → QuadFin F d} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).im) :=
  ⟨fun h => ⟨(continuous_fst.comp (continuous_induced_dom (f := fun z : QuadFin F d => (z.re, z.im)))).comp h,
      (continuous_snd.comp (continuous_induced_dom (f := fun z : QuadFin F d => (z.re, z.im)))).comp h⟩,
    fun ⟨h0, h1⟩ => continuous_induced_rng.mpr (h0.prodMk h1)⟩

theorem continuous_quadInf_re : Continuous fun z : QuadInf F d => z.re := ((continuous_quadInf_iff d).1 continuous_id).1

theorem continuous_quadInf_im : Continuous fun z : QuadInf F d => z.im := ((continuous_quadInf_iff d).1 continuous_id).2

theorem continuous_quadFin_re : Continuous fun z : QuadFin F d => z.re := ((continuous_quadFin_iff d).1 continuous_id).1

theorem continuous_quadFin_im : Continuous fun z : QuadFin F d => z.im := ((continuous_quadFin_iff d).1 continuous_id).2

instance : IsTopologicalRing (QuadInf F d) where
  continuous_add := by
    have h0 := continuous_quadInf_re d; have h1 := continuous_quadInf_im d
    refine (continuous_quadInf_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> fun_prop
  continuous_mul := by
    have h0 := continuous_quadInf_re d; have h1 := continuous_quadInf_im d
    refine (continuous_quadInf_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> fun_prop
  continuous_neg := by
    have h0 := continuous_quadInf_re d; have h1 := continuous_quadInf_im d
    refine (continuous_quadInf_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg] <;> fun_prop

instance : IsTopologicalRing (QuadFin F d) where
  continuous_add := by
    have h0 := continuous_quadFin_re d; have h1 := continuous_quadFin_im d
    refine (continuous_quadFin_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> fun_prop
  continuous_mul := by
    have h0 := continuous_quadFin_re d; have h1 := continuous_quadFin_im d
    refine (continuous_quadFin_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> fun_prop
  continuous_neg := by
    have h0 := continuous_quadFin_re d; have h1 := continuous_quadFin_im d
    refine (continuous_quadFin_iff d).mpr ⟨?_, ?_⟩ <;>
      simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg] <;> fun_prop

/-- The coordinates $z\mapsto(\mathrm{re}\,z,\mathrm{im}\,z)$ as a homeomorphism $E\otimes F_\infty\cong F_\infty^2$. -/
def quadInfCoordHomeo : QuadInf F d ≃ₜ mixedSpace F × mixedSpace F where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The coordinates as a homeomorphism $E\otimes\mathbb A_f\cong\mathbb A_f^2$. -/
def quadFinCoordHomeo : QuadFin F d ≃ₜ AF × AF where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance : T2Space (QuadInf F d) := (quadInfCoordHomeo d).isEmbedding.t2Space
instance : T2Space (QuadFin F d) := (quadFinCoordHomeo d).isEmbedding.t2Space

instance : LocallyCompactSpace (QuadInf F d) := (quadInfCoordHomeo d).isClosedEmbedding.locallyCompactSpace
instance : LocallyCompactSpace (QuadFin F d) := (quadFinCoordHomeo d).isClosedEmbedding.locallyCompactSpace

instance : SecondCountableTopology (QuadInf F d) := (quadInfCoordHomeo d).isEmbedding.secondCountableTopology
instance : SecondCountableTopology (QuadFin F d) := (quadFinCoordHomeo d).isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuadInf F d)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuadInf F d)).symm.isEmbedding.secondCountableTopology
instance : SecondCountableTopology (QuadFin F d)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuadFin F d)).symm.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuadInf F d)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
instance : SecondCountableTopology (QuadFin F d)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology

example : LocallyCompactSpace (QuadInf F d)ˣ := inferInstance
example : LocallyCompactSpace (QuadFin F d)ˣ := inferInstance
example : SigmaCompactSpace (QuadInf F d)ˣ := inferInstance
example : SigmaCompactSpace (QuadFin F d)ˣ := inferInstance

/-! ### The splitting $E\otimes\mathbb A_F = (E\otimes F_\infty)\times(E\otimes\mathbb A_f)$ -/

/-- $E\otimes\mathbb A_F\cong(E\otimes F_\infty)\times(E\otimes\mathbb A_f)$ (coordinatewise), as rings. -/
def quadAdeleRingEquiv : QuadAdele F d ≃+* (QuadInf F d × QuadFin F d) where
  toFun z := (⟨z.re.1, z.im.1⟩, ⟨z.re.2, z.im.2⟩)
  invFun p := ⟨(p.1.re, p.2.re), (p.1.im, p.2.im)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    refine Prod.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_) <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> rfl
  map_add' x y := by
    refine Prod.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_) <;> simp

theorem continuous_quadAdeleRingEquiv : Continuous (quadAdeleRingEquiv d) := by
  refine Continuous.prodMk ?_ ?_
  · refine (continuous_quadInf_iff d).mpr ⟨?_, ?_⟩
    · exact continuous_fst.comp (continuous_quad_re d)
    · exact continuous_fst.comp (continuous_quad_im d)
  · refine (continuous_quadFin_iff d).mpr ⟨?_, ?_⟩
    · exact continuous_snd.comp (continuous_quad_re d)
    · exact continuous_snd.comp (continuous_quad_im d)

theorem continuous_quadAdeleRingEquiv_symm : Continuous (quadAdeleRingEquiv d).symm := by
  refine (continuous_quad_iff d).mpr ⟨?_, ?_⟩
  · exact ((continuous_quadInf_re d).comp continuous_fst).prodMk ((continuous_quadFin_re d).comp continuous_snd)
  · exact ((continuous_quadInf_im d).comp continuous_fst).prodMk ((continuous_quadFin_im d).comp continuous_snd)

/-- **$(E\otimes\mathbb A_F)^\times\cong(E\otimes F_\infty)^\times\times(E\otimes\mathbb A_f)^\times$** as topological groups. -/
def quadUnitsSplit : (QuadAdele F d)ˣ ≃ₜ* ((QuadInf F d)ˣ × (QuadFin F d)ˣ) :=
  (unitsContinuousMulEquiv (quadAdeleRingEquiv d) (continuous_quadAdeleRingEquiv d)
    (continuous_quadAdeleRingEquiv_symm d)).trans
  { toMulEquiv := MulEquiv.prodUnits
    continuous_toFun := Homeomorph.prodUnits.continuous
    continuous_invFun := Homeomorph.prodUnits.symm.continuous }

@[simp] theorem quadUnitsSplit_fst_re (z : (QuadAdele F d)ˣ) :
    ((quadUnitsSplit d z).1 : QuadInf F d).re = (z : QuadAdele F d).re.1 := rfl

@[simp] theorem quadUnitsSplit_fst_im (z : (QuadAdele F d)ˣ) :
    ((quadUnitsSplit d z).1 : QuadInf F d).im = (z : QuadAdele F d).im.1 := rfl

@[simp] theorem quadUnitsSplit_snd_re (z : (QuadAdele F d)ˣ) :
    ((quadUnitsSplit d z).2 : QuadFin F d).re = (z : QuadAdele F d).re.2 := rfl

@[simp] theorem quadUnitsSplit_snd_im (z : (QuadAdele F d)ˣ) :
    ((quadUnitsSplit d z).2 : QuadFin F d).im = (z : QuadAdele F d).im.2 := rfl

@[simp] theorem quadUnitsSplit_symm_re (p : (QuadInf F d)ˣ × (QuadFin F d)ˣ) :
    (((quadUnitsSplit d).symm p : (QuadAdele F d)ˣ) : QuadAdele F d).re =
      (((p.1 : QuadInf F d)).re, ((p.2 : QuadFin F d)).re) := rfl

@[simp] theorem quadUnitsSplit_symm_im (p : (QuadInf F d)ˣ × (QuadFin F d)ˣ) :
    (((quadUnitsSplit d).symm p : (QuadAdele F d)ˣ) : QuadAdele F d).im =
      (((p.1 : QuadInf F d)).im, ((p.2 : QuadFin F d)).im) := rfl

/-- The scalars $F_\infty^\times\to(E\otimes F_\infty)^\times$. -/
def infScalarQ : (mixedSpace F)ˣ →* (QuadInf F d)ˣ := Units.map (algebraMap (mixedSpace F) (QuadInf F d)).toMonoidHom

/-- The scalars $\mathbb A_f^\times\to(E\otimes\mathbb A_f)^\times$. -/
def finScalarQ : AFˣ →* (QuadFin F d)ˣ := Units.map (algebraMap AF (QuadFin F d)).toMonoidHom

theorem quadUnitsSplit_quadScalar (c : (Adeles F)ˣ) :
    quadUnitsSplit d (quadScalar d c) = (infScalarQ d (MulEquiv.prodUnits c).1, finScalarQ d (MulEquiv.prodUnits c).2) :=
  Prod.ext (Units.ext (QuadraticAlgebra.ext rfl rfl)) (Units.ext (QuadraticAlgebra.ext rfl rfl))

end InfFin

/-! ### Projections to the places -/

section Places

/-- A ring homomorphism $f : R\to S$ with $f(a) = a'$ induces $R[\omega]\to S[\omega']$, $x + y\omega\mapsto f(x) + f(y)\omega'$
($\omega^2 = a$, $\omega'^2 = a'$). -/
def quadMapHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {a : R} {a' : S} (h : f a = a') :
    QuadraticAlgebra R a 0 →+* QuadraticAlgebra S a' 0 where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := QuadraticAlgebra.ext (by simp [QuadraticAlgebra.re_one]) (by simp [QuadraticAlgebra.im_one])
  map_mul' z w := QuadraticAlgebra.ext (by simp [QuadraticAlgebra.re_mul, h]) (by simp [QuadraticAlgebra.im_mul])
  map_zero' := QuadraticAlgebra.ext (by simp) (by simp)
  map_add' z w := QuadraticAlgebra.ext (by simp) (by simp)

@[simp] theorem quadMapHom_re {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {a : R} {a' : S} (h : f a = a')
    (z : QuadraticAlgebra R a 0) : (quadMapHom f h z).re = f z.re := rfl

@[simp] theorem quadMapHom_im {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {a : R} {a' : S} (h : f a = a')
    (z : QuadraticAlgebra R a 0) : (quadMapHom f h z).im = f z.im := rfl

variable (d : F)

/-- $E\otimes F_\infty\to E\otimes_{F,\sigma_w}\mathbb R = \mathbb R[\omega]$ at a real place $w$ (embedding $\sigma_w$). -/
def projQR (w : {w : InfinitePlace F // w.IsReal}) :
    QuadInf F d →+* QuadraticAlgebra ℝ (embedding_of_isReal w.2 d) 0 :=
  quadMapHom ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)) (mixedEmbedding_apply_isReal F d w)

/-- $E\otimes F_\infty\to E\otimes_{F,\tau_w}\mathbb C = \mathbb C[\omega]$ at a complex place $w$ (embedding $\tau_w$). -/
def projQC (w : {w : InfinitePlace F // w.IsComplex}) :
    QuadInf F d →+* QuadraticAlgebra ℂ (w.1.embedding d) 0 :=
  quadMapHom ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)) (mixedEmbedding_apply_isComplex F d w)

/-- $E\otimes\mathbb A_f\to E\otimes_FF_v = F_v[\omega]$ at a finite place $v$. -/
def projQV (v : HeightOneSpectrum (𝓞 F)) : QuadFin F d →+* QuadV F d v :=
  quadMapHom (evalAt v) (evalAt_algebraMap v d)

@[simp] theorem projQR_re (w) (x : QuadInf F d) : (projQR d w x).re = x.re.1 w := rfl
@[simp] theorem projQR_im (w) (x : QuadInf F d) : (projQR d w x).im = x.im.1 w := rfl
@[simp] theorem projQC_re (w) (x : QuadInf F d) : (projQC d w x).re = x.re.2 w := rfl
@[simp] theorem projQC_im (w) (x : QuadInf F d) : (projQC d w x).im = x.im.2 w := rfl
@[simp] theorem projQV_re (v) (x : QuadFin F d) : (projQV d v x).re = x.re v := rfl
@[simp] theorem projQV_im (v) (x : QuadFin F d) : (projQV d v x).im = x.im v := rfl

/-- The local component of a unit of $E\otimes\mathbb A_f$ at $v$. -/
def unitAtD (v : HeightOneSpectrum (𝓞 F)) : (QuadFin F d)ˣ →* (QuadV F d v)ˣ := Units.map (projQV d v).toMonoidHom

@[simp] theorem unitAtD_val (v : HeightOneSpectrum (𝓞 F)) (u : (QuadFin F d)ˣ) :
    ((unitAtD d v u : (QuadV F d v)ˣ) : QuadV F d v) = projQV d v u := rfl

theorem unitAtD_inv_val (v : HeightOneSpectrum (𝓞 F)) (u : (QuadFin F d)ˣ) :
    (((unitAtD d v u)⁻¹ : (QuadV F d v)ˣ) : QuadV F d v) = projQV d v ((u⁻¹ : (QuadFin F d)ˣ) : QuadFin F d) := rfl

end Places

/-! ### Continuity of the matrix of $u(z)$ -/

section ContinuityGL

/-- **Continuity of $z\mapsto$ the matrix of $u(z)$**, in terms of the coordinates of $z$ and $z^{-1}$. -/
theorem continuous_torGLK_comp {X : Type*} [TopologicalSpace X] {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {d Dk : K} (hd : d = -Dk) (f : X → (QuadraticAlgebra K d 0)ˣ)
    (h0 : Continuous fun x => ((f x : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).re)
    (h1 : Continuous fun x => ((f x : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).im)
    (h0' : Continuous fun x => (((f x)⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).re)
    (h1' : Continuous fun x => (((f x)⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).im) :
    Continuous fun x => torGLK hd (f x) := by
  have hP : Continuous fun x => torP ((f x : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0) := by
    simp_rw [torP_eq_mul_norm_inv, norm_eq]
    fun_prop
  have hQ : Continuous fun x => torQ ((f x : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0) := by
    simp_rw [torQ_eq_mul_norm_inv, norm_eq]
    fun_prop
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [rotMat] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    simp only [torGLK_inv_val]
    fin_cases i <;> fin_cases j <;> simp [rotMatInv] <;> fun_prop

end ContinuityGL

/-! ### The torus map at the archimedean places -/

section Inf

variable (D : 𝓞 F)

/-- The real component $(E\otimes F_\infty)^\times\to SO(Q^{\sigma_w})(\mathbb R)$, $z\mapsto\mathrm{tor}(z_w)$. -/
def torR (w : {w : InfinitePlace F // w.IsReal}) : (QuadInf F (dD D))ˣ →* ArchSO (QRe (diagForm1 D) w) :=
  (MonoidHom.id (soReal (QRe (diagForm1 D) w)) : soReal (QRe (diagForm1 D) w) →* ArchSO (QRe (diagForm1 D) w)).comp
    ((torSOReal D (embedding_of_isReal w.2)).comp (Units.map (projQR (dD D) w).toMonoidHom))

theorem torR_incl (w : {w : InfinitePlace F // w.IsReal}) (z : (QuadInf F (dD D))ˣ) :
    ArchSO.incl _ (torR D w z) =
      torGLK (dD_map D (embedding_of_isReal w.2)) (Units.map (projQR (dD D) w).toMonoidHom z) := rfl

/-- The complex component $(E\otimes F_\infty)^\times\to SO(Q^{\tau_w})(\mathbb C)$, $z\mapsto\mathrm{tor}(z_w)$. -/
def torC (w : {w : InfinitePlace F // w.IsComplex}) : (QuadInf F (dD D))ˣ →* ArchSOC (QCx (diagForm1 D) w) :=
  (MonoidHom.id (soC (QCx (diagForm1 D) w)) : soC (QCx (diagForm1 D) w) →* ArchSOC (QCx (diagForm1 D) w)).comp
    ((torSOC D w.1.embedding).comp (Units.map (projQC (dD D) w).toMonoidHom))

theorem torC_incl (w : {w : InfinitePlace F // w.IsComplex}) (z : (QuadInf F (dD D))ˣ) :
    ArchSOC.incl _ (torC D w z) =
      torGLK (dD_map D w.1.embedding) (Units.map (projQC (dD D) w).toMonoidHom z) := rfl

/-- **The archimedean torus map** $(E\otimes F_\infty)^\times\to G_\infty = \prod_{w\ \mathrm{real}}SO(Q^{\sigma_w})(\mathbb R)\times
\prod_{w\ \mathrm{complex}}SO(Q^{\tau_w})(\mathbb C)$, $z\mapsto(\mathrm{tor}(z_w))_w$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torInf : (QuadInf F (dD D))ˣ →* GInfSO (diagForm1 D) :=
  (MonoidHom.pi fun w => torR D w).prod (MonoidHom.pi fun w => torC D w)

/-- **`torInf` is continuous.** -/
theorem continuous_torInf : Continuous (torInf D) := by
  have hc : ∀ (f : QuadInf F (dD D) → mixedSpace F), Continuous f →
      Continuous fun α : (QuadInf F (dD D))ˣ => f α := fun f hf => hf.comp Units.continuous_val
  have hc' : ∀ (f : QuadInf F (dD D) → mixedSpace F), Continuous f →
      Continuous fun α : (QuadInf F (dD D))ˣ => f ↑α⁻¹ := fun f hf => hf.comp Units.continuous_coe_inv
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · refine Continuous.subtype_mk ?_ _
    refine continuous_torGLK_comp (dD_map D (embedding_of_isReal w.2)) _ ?_ ?_ ?_ ?_
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_quadInf_re _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc _ (continuous_quadInf_im _)))
    all_goals simp only [← map_inv]
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_quadInf_re _)))
    · exact (continuous_apply w).comp (continuous_fst.comp (hc' _ (continuous_quadInf_im _)))
  · refine Continuous.subtype_mk ?_ _
    refine continuous_torGLK_comp (dD_map D w.1.embedding) _ ?_ ?_ ?_ ?_
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_quadInf_re _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc _ (continuous_quadInf_im _)))
    all_goals simp only [← map_inv]
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_quadInf_re _)))
    · exact (continuous_apply w).comp (continuous_snd.comp (hc' _ (continuous_quadInf_im _)))

end Inf

/-! ### The torus map at the finite places -/

section FinPart

/-- $\hat{\mathcal O}[\omega] = \hat{\mathcal O}\oplus\hat{\mathcal O}\omega\subseteq E\otimes\mathbb A_f$: both coordinates integral. -/
def quadHat (d : F) : Set (QuadFin F d) := {x | x.re ∈ OHat ∧ x.im ∈ OHat}

theorem isOpen_quadHat (d : F) : IsOpen (quadHat d) :=
  (isOpen_OHat.prod isOpen_OHat).preimage ((continuous_quadFin_re d).prodMk (continuous_quadFin_im d))

/-- $\hat{\mathcal O}[\omega]^\times = \{u : u, u^{-1}\in\hat{\mathcal O}[\omega]\}$, an open neighbourhood of $1$. -/
def quadHatUnits (d : F) : Set (QuadFin F d)ˣ := {u | (u : QuadFin F d) ∈ quadHat d ∧ ((u⁻¹ : (QuadFin F d)ˣ) : QuadFin F d) ∈ quadHat d}

theorem isOpen_quadHatUnits (d : F) : IsOpen (quadHatUnits d) :=
  ((isOpen_quadHat d).preimage Units.continuous_val).inter ((isOpen_quadHat d).preimage Units.continuous_coe_inv)

theorem one_mem_quadHatUnits (d : F) : (1 : (QuadFin F d)ˣ) ∈ quadHatUnits d := by
  have h1 : (1 : QuadFin F d) ∈ quadHat d := by
    refine ⟨?_, ?_⟩
    · intro v; exact (v.adicCompletionIntegers F).one_mem
    · intro v; exact (v.adicCompletionIntegers F).zero_mem
  exact ⟨h1, by rw [inv_one]; exact h1⟩

variable (D : 𝓞 F)

theorem valued_le_one_of_mem_int (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 hx

theorem torOrthK_unitAtD_mem_stdStab {u : (QuadFin F (dD D))ˣ} (hu : u ∈ quadHatUnits (dD D))
    (v : HeightOneSpectrum (𝓞 F)) :
    torOrthK D (v.adicCompletion F) (unitAtD (dD D) v u) ∈ stdStab (formF (diagForm1 D)) v := by
  have h := fun (x : AF) (hx : x ∈ OHat) => valued_le_one_of_mem_int v (hx v)
  exact torOrthK_mem_stdStab D v (h _ hu.1.1) (h _ hu.1.2) (h _ hu.2.1) (h _ hu.2.2)

/-- The local components of `torFin`. -/
def torFinFun (z : (QuadFin F (dD D))ˣ) : OAf (formF (diagForm1 D)) :=
  ⟨fun v => torOrthK D (v.adicCompletion F) (unitAtD (dD D) v z), by
    filter_upwards [(z : QuadFin F (dD D)).re.2, (z : QuadFin F (dD D)).im.2,
      ((z⁻¹ : (QuadFin F (dD D))ˣ) : QuadFin F (dD D)).re.2, ((z⁻¹ : (QuadFin F (dD D))ˣ) : QuadFin F (dD D)).im.2]
      with v h0 h1 h0' h1'
    exact torOrthK_mem_stdStab D v (valued_le_one_of_mem_int v h0) (valued_le_one_of_mem_int v h1)
      (valued_le_one_of_mem_int v h0') (valued_le_one_of_mem_int v h1')⟩

@[simp] theorem torFinFun_apply (z : (QuadFin F (dD D))ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    torFinFun D z v = torOrthK D (v.adicCompletion F) (unitAtD (dD D) v z) := rfl

/-- **The finite torus map** $(E\otimes\mathbb A_f)^\times\to SO(V)(\mathbb A_f)$, $z\mapsto(\mathrm{tor}(z_v))_v$ (it lands in the
restricted product because $z_v, z_v^{-1}\in\mathfrak o_v[\omega]$ for almost all $v$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torFin : (QuadFin F (dD D))ˣ →* SOAf (diagForm1 D) where
  toFun z := ⟨torFinFun D z, fun v => det_torGLK (dD_algebraMap D (v.adicCompletion F)) _⟩
  map_one' := by
    ext v : 2
    simp
  map_mul' α β := by
    ext v : 2
    simp

@[simp] theorem torFin_apply (z : (QuadFin F (dD D))ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((torFin D z : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D))) v =
      torOrthK D (v.adicCompletion F) (unitAtD (dD D) v z) := rfl

theorem continuous_torOrthK_unitAtD (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun z : (QuadFin F (dD D))ˣ => torOrthK D (v.adicCompletion F) (unitAtD (dD D) v z) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_torGLK_comp (dD_algebraMap D (v.adicCompletion F)) (fun z => unitAtD (dD D) v z) ?_ ?_ ?_ ?_
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_quadFin_re _).comp Units.continuous_val)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_quadFin_im _).comp Units.continuous_val)
  all_goals simp only [← map_inv]
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_quadFin_re _).comp Units.continuous_coe_inv)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_quadFin_im _).comp Units.continuous_coe_inv)

/-- **`torFin` is continuous.** On the open subgroup $\hat{\mathcal O}[\omega]^\times$ it factors through
$\prod_vO(\mathfrak o_v^2)$, where the restricted product topology is the product topology; a homomorphism continuous at $1$
is continuous. -/
theorem continuous_torFin : Continuous (torFin D) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : quadHatUnits (dD D) ∈ 𝓝 (1 : (QuadFin F (dD D))ˣ) :=
    (isOpen_quadHatUnits _).mem_nhds (one_mem_quadHatUnits _)
  let g : quadHatUnits (dD D) → ∀ v, (stdStab (formF (diagForm1 D)) v : Set (orthGroup (formF (diagForm1 D)) (v.adicCompletion F))) :=
    fun α v => ⟨_, torOrthK_unitAtD_mem_stdStab D α.2 v⟩
  have hg : Continuous g := continuous_pi fun v =>
    ((continuous_torOrthK_unitAtD D v).comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous fun α : quadHatUnits (dD D) => ((torFin D α.1 : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D))) := by
    have := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup (formF (diagForm1 D)) (v.adicCompletion F))
      (A := fun v => (stdStab (formF (diagForm1 D)) v : Set (orthGroup (formF (diagForm1 D)) (v.adicCompletion F))))
      (𝓕 := cofinite)).continuous.comp hg
    refine this.congr fun α => ?_
    ext v : 1
    rfl
  have hon : ContinuousOn (fun α => ((torFin D α : SOAf (diagForm1 D)) : OAf (formF (diagForm1 D)))) (quadHatUnits (dD D)) :=
    continuousOn_iff_continuous_domRestrict.2 hcomp
  have hat := hon.continuousAt hU
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff).2 hat

end FinPart

/-! ### The adelic torus map -/

section Adelic

variable (D : 𝓞 F)

/-- **The adelic torus map** $(E\otimes\mathbb A_F)^\times\to SO(V)(\mathbb A)$, $V = (F^2,\langle1,D\rangle)$:
$z\mapsto(\mathrm{tor}(z_w))_w$, componentwise at every place (`torInf` $\times$ `torFin` after `quadUnitsSplit`). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torAdele : (QuadAdele F (dD D))ˣ →* SOAdele (diagForm1 D) :=
  ((torInf D).prodMap (torFin D)).comp (quadUnitsSplit (dD D)).toMulEquiv.toMonoidHom

theorem torAdele_apply (z : (QuadAdele F (dD D))ˣ) :
    torAdele D z = (torInf D (quadUnitsSplit (dD D) z).1, torFin D (quadUnitsSplit (dD D) z).2) := rfl

/-- **`torAdele` is continuous.** -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem continuous_torAdele : Continuous (torAdele D) :=
  ((continuous_torInf D).prodMap (continuous_torFin D)).comp (quadUnitsSplit (dD D)).continuous

/-! ### Surjectivity -/

/-- Extensionality for `ArchSOC` (any dimension). -/
theorem archSOC_ext' {n : ℕ} {Q : QuadForm ℂ n} {g h : ArchSOC Q} (e : ArchSOC.incl Q g = ArchSOC.incl Q h) : g = h :=
  Subtype.ext e

theorem quadInf_ext {d : F} {x y : QuadInf F d} (hR : ∀ w, projQR d w x = projQR d w y)
    (hC : ∀ w, projQC d w x = projQC d w y) : x = y := by
  have e : ∀ s t : mixedSpace F, (∀ w, s.1 w = t.1 w) → (∀ w, s.2 w = t.2 w) → s = t :=
    fun s t h1 h2 => Prod.ext (funext h1) (funext h2)
  refine QuadraticAlgebra.ext ?_ ?_
  · exact e _ _ (fun w => congrArg QuadraticAlgebra.re (hR w)) (fun w => congrArg QuadraticAlgebra.re (hC w))
  · exact e _ _ (fun w => congrArg QuadraticAlgebra.im (hR w)) (fun w => congrArg QuadraticAlgebra.im (hC w))

theorem quadFin_ext {d : F} {x y : QuadFin F d} (h : ∀ v, projQV d v x = projQV d v y) : x = y :=
  QuadraticAlgebra.ext (Subtype.ext (funext fun v => congrArg QuadraticAlgebra.re (h v)))
    (Subtype.ext (funext fun v => congrArg QuadraticAlgebra.im (h v)))

/-- **`torInf` is surjective** ($D\ne0$; Hilbert 90 over $\mathbb R$ and $\mathbb C$ at each place). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torInf_surjective (hD : D ≠ 0) : Function.Surjective (torInf D) := by
  intro g
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      ∃ β : (QuadraticAlgebra ℝ (embedding_of_isReal w.2 (dD D)) 0)ˣ,
        torSOReal D (embedding_of_isReal w.2) β = (g.1 w : soReal (QRe (diagForm1 D) w)) := fun w =>
    torSOReal_surjective D hD _ _
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      ∃ β : (QuadraticAlgebra ℂ (w.1.embedding (dD D)) 0)ˣ,
        torSOC D w.1.embedding β = (g.2 w : soC (QCx (diagForm1 D) w)) := fun w =>
    torSOC_surjective D hD _ _
  choose βR hβR using hR
  choose βC hβC using hC
  let x : QuadInf F (dD D) :=
    ⟨((fun w => (βR w).val.re), (fun w => (βC w).val.re)), ((fun w => (βR w).val.im), (fun w => (βC w).val.im))⟩
  let y : QuadInf F (dD D) :=
    ⟨((fun w => ((βR w)⁻¹).val.re), (fun w => ((βC w)⁻¹).val.re)),
     ((fun w => ((βR w)⁻¹).val.im), (fun w => ((βC w)⁻¹).val.im))⟩
  have hxR : ∀ w, projQR (dD D) w x = βR w := fun w => QuadraticAlgebra.ext rfl rfl
  have hxC : ∀ w, projQC (dD D) w x = βC w := fun w => QuadraticAlgebra.ext rfl rfl
  have hyR : ∀ w, projQR (dD D) w y = ((βR w)⁻¹).val := fun w => QuadraticAlgebra.ext rfl rfl
  have hyC : ∀ w, projQC (dD D) w y = ((βC w)⁻¹).val := fun w => QuadraticAlgebra.ext rfl rfl
  have hxy : x * y = 1 := quadInf_ext (fun w => by rw [map_mul, map_one, hxR, hyR, Units.mul_inv])
    (fun w => by rw [map_mul, map_one, hxC, hyC, Units.mul_inv])
  have hyx : y * x = 1 := quadInf_ext (fun w => by rw [map_mul, map_one, hxR, hyR, Units.inv_mul])
    (fun w => by rw [map_mul, map_one, hxC, hyC, Units.inv_mul])
  refine ⟨⟨x, y, hxy, hyx⟩, Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)⟩
  · change torGLK (dD_map D (embedding_of_isReal w.2)) (Units.map (projQR (dD D) w).toMonoidHom ⟨x, y, hxy, hyx⟩) = _
    rw [show Units.map (projQR (dD D) w).toMonoidHom ⟨x, y, hxy, hyx⟩ = βR w from Units.ext (hxR w)]
    exact congrArg (fun h : soReal (QRe (diagForm1 D) w) => (h : GL (Fin 2) ℝ)) (hβR w)
  · change torGLK (dD_map D w.1.embedding) (Units.map (projQC (dD D) w).toMonoidHom ⟨x, y, hxy, hyx⟩) = _
    rw [show Units.map (projQC (dD D) w).toMonoidHom ⟨x, y, hxy, hyx⟩ = βC w from Units.ext (hxC w)]
    exact congrArg (fun h : soC (QCx (diagForm1 D) w) => (h : GL (Fin 2) ℂ)) (hβC w)

/-- **`torFin` is surjective** ($D\ne0$). Lift each $g_v$ (Hilbert 90 over $F_v$); at the cofinitely many $v$ with $|2|_v =
|D|_v = 1$ and $g_v\in O(\mathfrak o_v^2)$ the lift can be taken integral with integral inverse (`exists_integral_lift`), so the
lifts form an idele of $E$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torFin_surjective (hD : D ≠ 0) : Function.Surjective (torFin D) := by
  intro g
  have hD' : algebraMap (𝓞 F) F D ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD
  set gv : ∀ v : HeightOneSpectrum (𝓞 F), soSub (formF (diagForm1 D)) (v.adicCompletion F) :=
    fun v => ⟨(g : OAf (formF (diagForm1 D))) v, g.2 v⟩
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | Valued.v (2 : v.adicCompletion F) = 1 ∧
    Valued.v (dIn D (v.adicCompletion F)) = 1 ∧ (g : OAf (formF (diagForm1 D))) v ∈ stdStab (formF (diagForm1 D)) v}
  have hS : ∀ᶠ v in cofinite, v ∈ S := by
    have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 := by
      filter_upwards [eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hv
      rwa [map_ofNat] at hv
    filter_upwards [h2, eventually_valued_eq_one hD', (g : OAf (formF (diagForm1 D))).2] with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hlift : ∀ v : HeightOneSpectrum (𝓞 F), ∃ z : (QuadK D (v.adicCompletion F))ˣ, torSOK D _ z = gv v ∧
      (v ∈ S → Valued.v (z : QuadK D (v.adicCompletion F)).re ≤ 1 ∧ Valued.v (z : QuadK D (v.adicCompletion F)).im ≤ 1 ∧
        Valued.v ((z⁻¹ : (QuadK D (v.adicCompletion F))ˣ) : QuadK D (v.adicCompletion F)).re ≤ 1 ∧
        Valued.v ((z⁻¹ : (QuadK D (v.adicCompletion F))ˣ) : QuadK D (v.adicCompletion F)).im ≤ 1) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨h2, hDv, hst⟩ := hv
      obtain ⟨z, hz, h1, h2', h3, h4⟩ := exists_integral_lift D v h2 hDv (gv v) hst
      exact ⟨z, hz, fun _ => ⟨h1, h2', h3, h4⟩⟩
    · obtain ⟨z, hz⟩ := torSOK_surjective D (v.adicCompletion F) hD (gv v)
      exact ⟨z, hz, fun h => absurd h hv⟩
  choose β hβ hβS using hlift
  have hev : ∀ᶠ v in cofinite, Valued.v (β v : QuadK D (v.adicCompletion F)).re ≤ 1 ∧
      Valued.v (β v : QuadK D (v.adicCompletion F)).im ≤ 1 ∧
      Valued.v ((β v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.re ≤ 1 ∧
      Valued.v ((β v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.im ≤ 1 := by
    filter_upwards [hS] with v hv
    exact hβS v hv
  have hO : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F), Valued.v y ≤ 1 → y ∈ v.adicCompletionIntegers F :=
    fun v y hy => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy
  let x : QuadFin F (dD D) :=
    ⟨mkAF (fun v => (β v : QuadK D (v.adicCompletion F)).re) (by filter_upwards [hev] with v hv; exact hO v _ hv.1),
     mkAF (fun v => (β v : QuadK D (v.adicCompletion F)).im) (by filter_upwards [hev] with v hv; exact hO v _ hv.2.1)⟩
  let y : QuadFin F (dD D) :=
    ⟨mkAF (fun v => ((β v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.re)
        (by filter_upwards [hev] with v hv; exact hO v _ hv.2.2.1),
     mkAF (fun v => ((β v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val.im)
        (by filter_upwards [hev] with v hv; exact hO v _ hv.2.2.2)⟩
  have hx : ∀ v, projQV (dD D) v x = β v := fun v => QuadraticAlgebra.ext rfl rfl
  have hy : ∀ v, projQV (dD D) v y = ((β v)⁻¹ : (QuadK D (v.adicCompletion F))ˣ).val := fun v => QuadraticAlgebra.ext rfl rfl
  have hxy : x * y = 1 := quadFin_ext fun v => by rw [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := quadFin_ext fun v => by rw [map_mul, map_one, hx, hy, Units.inv_mul]
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  ext v : 2
  have hu : unitAtD (dD D) v ⟨x, y, hxy, hyx⟩ = β v := Units.ext (hx v)
  rw [torFin_apply, hu]
  exact congrArg Subtype.val (hβ v)

/-- **`torAdele` is surjective** ($D\ne0$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torAdele_surjective (hD : D ≠ 0) : Function.Surjective (torAdele D) := by
  intro g
  obtain ⟨x, hx⟩ := torInf_surjective D hD g.1
  obtain ⟨y, hy⟩ := torFin_surjective D hD g.2
  refine ⟨(quadUnitsSplit (dD D)).symm (x, y), ?_⟩
  rw [torAdele_apply, ContinuousMulEquiv.apply_symm_apply]
  exact Prod.ext hx hy

instance locallyCompactSpace_SOAf_diag : LocallyCompactSpace (SOAf (diagForm1 D)) :=
  (isClosed_soAf (formF (diagForm1 D))).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### Kernel, openness, and the isomorphism $T(\mathbb A)\cong SO(V)(\mathbb A)$ -/

/-- A unit of $R[\omega]$ with $\mathrm{im} = 0$ is a scalar. -/
theorem exists_scalar_of_im_eq_zero {R : Type*} [CommRing R] {a : R} (u : (QuadraticAlgebra R a 0)ˣ)
    (h : (u : QuadraticAlgebra R a 0).im = 0) :
    ∃ c : Rˣ, Units.map (algebraMap R (QuadraticAlgebra R a 0)).toMonoidHom c = u := by
  have h1 := congrArg QuadraticAlgebra.re (Units.mul_inv u)
  simp only [QuadraticAlgebra.re_mul, h, mul_zero, zero_mul, add_zero, QuadraticAlgebra.re_one] at h1
  refine ⟨⟨(u : QuadraticAlgebra R a 0).re, ((u⁻¹ : (QuadraticAlgebra R a 0)ˣ) : QuadraticAlgebra R a 0).re, h1,
    by rw [mul_comm]; exact h1⟩, Units.ext ?_⟩
  exact QuadraticAlgebra.ext rfl h.symm

/-- **The kernel of `torAdele` is $\mathbb A_F^\times$** (the scalars). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torAdele_eq_one_iff (z : (QuadAdele F (dD D))ˣ) : torAdele D z = 1 ↔ z ∈ (quadScalar (dD D)).range := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hIm1 : (z : QuadAdele F (dD D)).im.1 = 0 := by
      refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
      · have : torGLK (dD_map D (embedding_of_isReal w.2)) (Units.map (projQR (dD D) w).toMonoidHom
            (quadUnitsSplit (dD D) z).1) = 1 := congrArg (fun g : GInfSO (diagForm1 D) => ArchSO.incl _ (g.1 w)) h1
        exact (torGLK_eq_one_iff _ _).1 this
      · have : torGLK (dD_map D w.1.embedding) (Units.map (projQC (dD D) w).toMonoidHom
            (quadUnitsSplit (dD D) z).1) = 1 := congrArg (fun g : GInfSO (diagForm1 D) => ArchSOC.incl _ (g.2 w)) h1
        exact (torGLK_eq_one_iff _ _).1 this
    have hIm2 : (z : QuadAdele F (dD D)).im.2 = 0 := by
      refine Subtype.ext (funext fun v => ?_)
      have : torGLK (dD_algebraMap D (v.adicCompletion F)) (unitAtD (dD D) v (quadUnitsSplit (dD D) z).2) = 1 :=
        congrArg (fun g : SOAf (diagForm1 D) => (((g : OAf (formF (diagForm1 D))) v : orthGroup (formF (diagForm1 D)) (v.adicCompletion F)) : GL (Fin 2) (v.adicCompletion F))) h2
      exact (torGLK_eq_one_iff _ _).1 this
    obtain ⟨c, hc⟩ := exists_scalar_of_im_eq_zero z (Prod.ext hIm1 hIm2)
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rw [torAdele_apply, quadUnitsSplit_quadScalar]
    refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
    · exact (torGLK_eq_one_iff (dD_map D (embedding_of_isReal w.2)) _).2 rfl
    · exact (torGLK_eq_one_iff (dD_map D w.1.embedding) _).2 rfl
    · ext v : 2
      exact Subtype.ext ((torGLK_eq_one_iff (dD_algebraMap D (v.adicCompletion F)) _).2 rfl)

theorem ker_torAdele : (torAdele D).ker = (quadScalar (dD D)).range := by
  ext z; exact (MonoidHom.mem_ker).trans (torAdele_eq_one_iff D z)

/-- **`torAdele` is open** (open mapping theorem for $\sigma$-compact groups onto a Baire group). -/
theorem isOpenMap_torAdele (hD : D ≠ 0) : IsOpenMap (torAdele D) :=
  MonoidHom.isOpenMap_of_sigmaCompact _ (torAdele_surjective D hD) (continuous_torAdele D)

/-- **The adelic isomorphism $T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times\cong SO(\langle1,D\rangle)(\mathbb A)$**
as topological groups ($D\ne0$), $z\mapsto z/\bar z$. Placewise it is Hilbert 90. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torAdeleEquiv (hD : D ≠ 0) : TorA D ≃ₜ* SOAdele (diagForm1 D) :=
  quotientContinuousMulEquiv (torAdele D) _ (ker_torAdele D) (torAdele_surjective D hD) (continuous_torAdele D)
    (isOpenMap_torAdele D hD)

theorem torAdeleEquiv_mk (hD : D ≠ 0) (z : (QuadAdele F (dD D))ˣ) :
    torAdeleEquiv D hD (torMk D z) = torAdele D z := rfl

/-! ### Global points: $E^\times\to SO(V)(F)$ and the compatibility with the diagonal embeddings -/

/-- **The torus map commutes with base change**: if $z'$ has the images under $f : K\to L$ of the coordinates of $z$, then the
matrix of $u(z')$ is the entrywise image under $f$ of the matrix of $u(z)$. -/
theorem torGLK_val_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {d Dk : K} {d' Dk' : L}
    (hd : d = -Dk) (hd' : d' = -Dk') (hfd : f d = d') (hfD : f Dk = Dk')
    (z : (QuadraticAlgebra K d 0)ˣ) (z' : (QuadraticAlgebra L d' 0)ˣ)
    (hx : (z' : QuadraticAlgebra L d' 0).re = f (z : QuadraticAlgebra K d 0).re)
    (hy : (z' : QuadraticAlgebra L d' 0).im = f (z : QuadraticAlgebra K d 0).im) :
    (torGLK hd' z').val = (torGLK hd z).val.map f := by
  have hp := torP_map f hfd (z : QuadraticAlgebra K d 0) (z' : QuadraticAlgebra L d' 0) hx hy
  have hq := torQ_map f hfd (z : QuadraticAlgebra K d 0) (z' : QuadraticAlgebra L d' 0) hx hy
  rw [torGLK_val, torGLK_val, hp, hq, ← hfD]
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]

/-- **The global torus map** $E^\times\to SO(\langle1,D\rangle)(F)$, $z\mapsto$ the matrix of multiplication by $z/\bar z$
(`torSOK` for $K = F$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torF : (QuadraticAlgebra F (dD D) 0)ˣ →* soSub (formF (diagForm1 D)) F := torSOK D F

/-- **Hilbert 90 over $F$**: $E^\times\to SO(\langle1,D\rangle)(F)$ is surjective ($D\ne0$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torF_surjective (hD : D ≠ 0) : Function.Surjective (torF D) := torSOK_surjective D F hD

theorem torF_coe (z : (QuadraticAlgebra F (dD D) 0)ˣ) :
    (((torF D z : soSub (formF (diagForm1 D)) F) : orthGroup (formF (diagForm1 D)) F) : GL (Fin 2) F) =
      torGLK (dD_algebraMap D F) z := rfl

/-- **Compatibility with the diagonal embeddings:** $\mathrm{tor}_{\mathbb A}(\xi) = (\mathrm{tor}_F(\xi))_{\mathrm{diag}}$ for
$\xi\in E^\times$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torAdele_diag (z : (QuadraticAlgebra F (dD D) 0)ˣ) :
    torAdele D (quadDiagUnit (dD D) z) = diagSOAdele (diagForm1 D) (torF D z) := by
  refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
  · change torGLK (dD_map D (embedding_of_isReal w.2)) (Units.map (projQR (dD D) w).toMonoidHom
      (quadUnitsSplit (dD D) (quadDiagUnit (dD D) z)).1) =
      Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (torGLK (dD_algebraMap D F) z)
    ext : 1
    exact torGLK_val_map (embedding_of_isReal w.2) (dD_algebraMap D F) (dD_map D _) rfl (by simp [dIn]) z _
      (mixedEmbedding_apply_isReal F _ w) (mixedEmbedding_apply_isReal F _ w)
  · change torGLK (dD_map D w.1.embedding) (Units.map (projQC (dD D) w).toMonoidHom
      (quadUnitsSplit (dD D) (quadDiagUnit (dD D) z)).1) =
      Matrix.GeneralLinearGroup.map w.1.embedding (torGLK (dD_algebraMap D F) z)
    ext : 1
    exact torGLK_val_map w.1.embedding (dD_algebraMap D F) (dD_map D _) rfl (by simp [dIn]) z _
      (mixedEmbedding_apply_isComplex F _ w) (mixedEmbedding_apply_isComplex F _ w)
  · ext v : 3
    change torGLK (dD_algebraMap D (v.adicCompletion F)) (unitAtD (dD D) v (quadUnitsSplit (dD D) (quadDiagUnit (dD D) z)).2) =
      Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (torGLK (dD_algebraMap D F) z)
    ext : 1
    exact torGLK_val_map (algebraMap F (v.adicCompletion F)) (dD_algebraMap D F) (dD_algebraMap D _) rfl rfl z _ rfl rfl

/-- The image of the diagonal $E^\times$ under `torAdele` is $SO(V)(F)$, i.e. `GammaSOAdele`. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem map_quadDiagUnit_torAdele (hD : D ≠ 0) :
    (quadDiagUnit (dD D)).range.map (torAdele D) = GammaSOAdele (diagForm1 D) := by
  ext g
  constructor
  · rintro ⟨_, ⟨ξ, rfl⟩, rfl⟩
    exact ⟨torF D ξ, (torAdele_diag D ξ).symm⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨ξ, rfl⟩ := torF_surjective D hD γ
    exact ⟨_, ⟨ξ, rfl⟩, torAdele_diag D ξ⟩

/-- **The isomorphism carries $T(F) = E^\times F^\times/F^\times$ onto $SO(V)(F)$** (`GammaSOAdele`). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem map_torGamma (hD : D ≠ 0) :
    (torGamma D).map (torAdeleEquiv D hD).toMulEquiv.toMonoidHom = GammaSOAdele (diagForm1 D) := by
  rw [← map_quadDiagUnit_torAdele D hD, Subgroup.map_map]
  rfl

end Adelic

end QuadFormsKB.Tamagawa.Measure.Weil
