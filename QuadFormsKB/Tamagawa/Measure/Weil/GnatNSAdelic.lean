/-
# Non-square discriminant, adelically: components of $G^\natural(\mathbb A_k)\subset(D'\otimes\mathbb A_K)^\times$ at the places of $k$


**Layer:** a number field $F$, $a, b, d\in\mathcal O_F$, a number field $K\supseteq F$ with an $F$-basis $(1,\delta)$, $\delta^2 = d$, and
$A' = a$, $B' = b$ in $K$ (`gnatBC` for $D' = \mathbb H[K,A',B']$). Via the base change $\Theta : D_E\otimes_F\mathbb A_F\cong D'\otimes_K\mathbb A_K$
(`quatBaseChange`), a unit of $D'\otimes\mathbb A_K$ has components in $D_E\otimes F_v = $ `DE (ιa) (ιb) (ιd)` at every place $v$ of $F$ (finite,
real, complex), and $G^\natural$ maps into the $G^\natural(F_v)$ there.

**Defines/proves**
* `quatParamEquiv`: $\mathbb H[R,A',B']\cong\mathbb H[R,A'',B'']$ for $A' = A''$, $B' = B''$ (coordinatewise identity);
* `bcHom : (D'⊗𝔸_K)^× →* (D_E⊗𝔸_F)^×` (continuous), **`bcHom_nrd`**: $\operatorname{nrd}m = \iota(u)$ ⇒ $\operatorname{nrd}_E(\Theta^{-1}m) = u$;
* `qeAt`, `deAt` (finite places), `qeAtR`, `deAtR`, `qeAtC`, `deAtC` (archimedean places): the local ring homomorphisms
  $E\otimes\mathbb A_F\to E\otimes F_v$, $D_E\otimes\mathbb A_F\to D_E\otimes F_v$; `nrdE_deAt` etc.

Source: Weil 1982, §1.3 (restriction of scalars), §3.7, pp. 64–65 [unverified pages].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSLocal
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeQuat

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology
  Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Changing the parameters of a quaternion algebra along equalities -/

section Param

variable {R : Type*} [CommRing R] {c₁ c₃ c₁' c₃' : R}

/-- $\mathbb H[R,c_1,c_3]\cong\mathbb H[R,c_1',c_3']$ for $c_1 = c_1'$, $c_3 = c_3'$: the identity on coordinates. -/
def quatParamEquiv (h₁ : c₁ = c₁') (h₃ : c₃ = c₃') : ℍ[R, c₁, 0, c₃] ≃+* ℍ[R, c₁', 0, c₃'] :=
  RingEquiv.ofRingHom
    (QuaternionAlgebra.mapRingHom (RingHom.id R) (by simp [h₁]) rfl (by simp [h₃]))
    (QuaternionAlgebra.mapRingHom (RingHom.id R) (by simp [h₁]) rfl (by simp [h₃]))
    (RingHom.ext fun _ => QuaternionAlgebra.ext rfl rfl rfl rfl)
    (RingHom.ext fun _ => QuaternionAlgebra.ext rfl rfl rfl rfl)

@[simp] theorem quatParamEquiv_re (h₁ : c₁ = c₁') (h₃ : c₃ = c₃') (x : ℍ[R, c₁, 0, c₃]) :
    (quatParamEquiv h₁ h₃ x).re = x.re := rfl
@[simp] theorem quatParamEquiv_imI (h₁ : c₁ = c₁') (h₃ : c₃ = c₃') (x : ℍ[R, c₁, 0, c₃]) :
    (quatParamEquiv h₁ h₃ x).imI = x.imI := rfl
@[simp] theorem quatParamEquiv_imJ (h₁ : c₁ = c₁') (h₃ : c₃ = c₃') (x : ℍ[R, c₁, 0, c₃]) :
    (quatParamEquiv h₁ h₃ x).imJ = x.imJ := rfl
@[simp] theorem quatParamEquiv_imK (h₁ : c₁ = c₁') (h₃ : c₃ = c₃') (x : ℍ[R, c₁, 0, c₃]) :
    (quatParamEquiv h₁ h₃ x).imK = x.imK := rfl

end Param

/-! ### From $(D'\otimes\mathbb A_K)^\times$ to $(D_E\otimes\mathbb A_F)^\times$ -/

section BC

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)
  {a b : F} {A' B' : K} (hA' : A' = algebraMap F K a) (hB' : B' = algebraMap F K b)

theorem diag_eq_of_eq (hA' : A' = algebraMap F K a) : diag K A' = diag K (algebraMap F K a) := by rw [hA']

/-- $\Theta^{-1}\circ(\text{parameters})$ as a ring homomorphism $D'\otimes\mathbb A_K\to D_E\otimes\mathbb A_F$. -/
def bcRing : QuatAdele (F := K) A' B' →+* QuatQuadAdele F d a b :=
  (quatBaseChange hb₀ hb₁ a b).symm.toRingHom.comp (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB')).toRingHom

theorem bcRing_bijective : Function.Bijective (bcRing hb₀ hb₁ hA' hB') :=
  (quatBaseChange hb₀ hb₁ a b).symm.bijective.comp (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB')).bijective

theorem continuous_bcRing : Continuous (bcRing hb₀ hb₁ hA' hB') := by
  refine (continuous_quatBaseChange_symm hb₀ hb₁ a b).comp ?_
  refine (continuous_quat_iff _ _).mpr ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_re _ _
  · exact continuous_imI _ _
  · exact continuous_imJ _ _
  · exact continuous_imK _ _

/-- The units version. -/
def bcHom : (QuatAdele (F := K) A' B')ˣ →* (QuatQuadAdele F d a b)ˣ := Units.map (bcRing hb₀ hb₁ hA' hB').toMonoidHom

theorem continuous_bcHom : Continuous (bcHom hb₀ hb₁ hA' hB') :=
  Units.continuous_iff.mpr ⟨(continuous_bcRing hb₀ hb₁ hA' hB').comp Units.continuous_val,
    (continuous_bcRing hb₀ hb₁ hA' hB').comp Units.continuous_coe_inv⟩

theorem bcHom_injective : Function.Injective (bcHom hb₀ hb₁ hA' hB') := fun x y h =>
  Units.ext ((bcRing_bijective hb₀ hb₁ hA' hB').1 (congrArg Units.val h))

theorem quatBaseChange_star (z : QuatQuadAdele F d a b) :
    quatBaseChange hb₀ hb₁ a b (star z) = star (quatBaseChange hb₀ hb₁ a b z) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star, map_neg]

theorem bcRing_star (x : QuatAdele (F := K) A' B') :
    bcRing hb₀ hb₁ hA' hB' (star x) = star (bcRing hb₀ hb₁ hA' hB' x) := by
  apply (quatBaseChange hb₀ hb₁ a b).injective
  change quatBaseChange hb₀ hb₁ a b ((quatBaseChange hb₀ hb₁ a b).symm
      (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') (star x))) =
    quatBaseChange hb₀ hb₁ a b (star ((quatBaseChange hb₀ hb₁ a b).symm
      (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') x)))
  rw [RingEquiv.apply_symm_apply, quatBaseChange_star, RingEquiv.apply_symm_apply]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp

/-- **$\operatorname{nrd}m = \iota(u)$ in $\mathbb A_K$ ⇒ $\operatorname{nrd}_E(\Theta^{-1}m) = u$** (the reduced norm on $D_E\otimes\mathbb A_F$ with values in
$E\otimes\mathbb A_F$ has zero $\delta$-coordinate). -/
theorem bcHom_nrd (m : (QuatAdele (F := K) A' B')ˣ) (u : (Adeles F)ˣ) (h : nrdUnit m = adeleUnitsMap F K u) :
    (((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b) *
      star ((bcHom hb₀ hb₁ hA' hB' m : (QuatQuadAdele F d a b)ˣ) : QuatQuadAdele F d a b)).re =
      (⟨(u : Adeles F), 0⟩ : QuadAdele F d) := by
  apply (quadBaseChange hb₀ hb₁).injective
  have e1 : (bcHom hb₀ hb₁ hA' hB' m : QuatQuadAdele F d a b) = bcRing hb₀ hb₁ hA' hB' (m : QuatAdele (F := K) A' B') :=
    rfl
  rw [e1, ← bcRing_star, ← map_mul]
  change (quatBaseChange hb₀ hb₁ a b ((quatBaseChange hb₀ hb₁ a b).symm
    (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB')
      ((m : QuatAdele (F := K) A' B') * star (m : QuatAdele (F := K) A' B'))))).re = _
  rw [RingEquiv.apply_symm_apply, quatParamEquiv_re]
  have h' := congrArg Units.val h
  rw [nrdUnit_val] at h'
  rw [h', quadBaseChange_apply, map_zero, mul_zero, add_zero]
  rfl

end BC

/-! ### Local components: $E\otimes\mathbb A_F\to E\otimes L$ and $D_E\otimes\mathbb A_F\to D_E\otimes L$ for $f : \mathbb A_F\to L$ -/

section LocalMaps

variable {F : Type} [Field F] [NumberField F] {L : Type*} [Field L] (f : Adeles F →+* L) {d : F} {td : L}
  (hd : f (diagRing F d) = td)

/-- $E\otimes\mathbb A_F\to E\otimes L$, coordinatewise $f$. -/
def qeMap : QuadAdele F d →+* QE td where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := QuadraticAlgebra.ext (by simp [QuadraticAlgebra.re_one]) (by simp [QuadraticAlgebra.im_one])
  map_mul' z w := QuadraticAlgebra.ext (by simp [← hd]) (by simp)
  map_zero' := QuadraticAlgebra.ext (by simp) (by simp)
  map_add' z w := QuadraticAlgebra.ext (by simp) (by simp)

@[simp] theorem qeMap_re (z : QuadAdele F d) : (qeMap f hd z).re = f z.re := rfl
@[simp] theorem qeMap_im (z : QuadAdele F d) : (qeMap f hd z).im = f z.im := rfl

variable {a b : F} {ta tb : L} (ha : f (diagRing F a) = ta) (hb : f (diagRing F b) = tb)

theorem qeMap_const {t : F} {tt : L} (ht : f (diagRing F t) = tt) :
    qeMap f hd (⟨diagRing F t, 0⟩ : QuadAdele F d) = algebraMap L (QE td) tt :=
  QuadraticAlgebra.ext (by simp [ht]) (by simp)

/-- $D_E\otimes\mathbb A_F\to D_E\otimes L$ = `DE ta tb td`, coordinatewise `qeMap`. -/
def deMap : QuatQuadAdele F d a b →+* DE ta tb td :=
  QuaternionAlgebra.mapRingHom (qeMap f hd) (qeMap_const f hd ha) (map_zero _) (qeMap_const f hd hb)

@[simp] theorem deMap_re (x : QuatQuadAdele F d a b) : (deMap f hd ha hb x).re = qeMap f hd x.re := rfl
@[simp] theorem deMap_imI (x : QuatQuadAdele F d a b) : (deMap f hd ha hb x).imI = qeMap f hd x.imI := rfl
@[simp] theorem deMap_imJ (x : QuatQuadAdele F d a b) : (deMap f hd ha hb x).imJ = qeMap f hd x.imJ := rfl
@[simp] theorem deMap_imK (x : QuatQuadAdele F d a b) : (deMap f hd ha hb x).imK = qeMap f hd x.imK := rfl

theorem deMap_star (x : QuatQuadAdele F d a b) : deMap f hd ha hb (star x) = star (deMap f hd ha hb x) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star, map_neg]

/-- **The local reduced norm** is the component of the global one. -/
theorem nrdE_deMap (x : QuatQuadAdele F d a b) : nrdE (deMap f hd ha hb x) = qeMap f hd (x * star x).re := by
  have h := mul_star_eq_nrdE (deMap f hd ha hb x)
  rw [← deMap_star, ← map_mul] at h
  have := congrArg QuaternionAlgebra.re h
  rw [deMap_re, QuaternionAlgebra.re_coe] at this
  exact this.symm

/-- Units with $\operatorname{nrd}_E = u\in\mathbb A_F$ go into $G^\natural(L)$. -/
theorem deMap_mem_Gnat {m : (QuatQuadAdele F d a b)ˣ} {u : Adeles F}
    (hm : ((m : QuatQuadAdele F d a b) * star (m : QuatQuadAdele F d a b)).re = (⟨u, 0⟩ : QuadAdele F d)) :
    Units.map (deMap f hd ha hb).toMonoidHom m ∈ Gnat ta tb td := by
  rw [mem_Gnat]
  change (nrdE (deMap f hd ha hb (m : QuatQuadAdele F d a b))).im = 0
  rw [nrdE_deMap, hm, qeMap_im, map_zero]

theorem nrdK_deMap {m : (QuatQuadAdele F d a b)ˣ} {u : Adeles F}
    (hm : ((m : QuatQuadAdele F d a b) * star (m : QuatQuadAdele F d a b)).re = (⟨u, 0⟩ : QuadAdele F d)) :
    nrdK (deMap f hd ha hb (m : QuatQuadAdele F d a b)) = f u := by
  rw [nrdK, nrdE_deMap, hm, qeMap_re]

end LocalMaps

/-! ### The three kinds of places -/

section Places

variable {F : Type} [Field F] [NumberField F]

/-- Evaluation at a finite place. -/
def fAt (v : HeightOneSpectrum (𝓞 F)) : Adeles F →+* v.adicCompletion F := (evalAt v).comp (RingHom.snd _ _)

/-- Evaluation at a real place. -/
def fAtR (w : {w : InfinitePlace F // w.IsReal}) : Adeles F →+* ℝ :=
  (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp (RingHom.fst _ _))

/-- Evaluation at a complex place. -/
def fAtC (w : {w : InfinitePlace F // w.IsComplex}) : Adeles F →+* ℂ :=
  (Pi.evalRingHom _ w).comp ((RingHom.snd _ _).comp (RingHom.fst _ _))

@[simp] theorem fAt_apply (v : HeightOneSpectrum (𝓞 F)) (x : Adeles F) : fAt v x = x.2 v := rfl
@[simp] theorem fAtR_apply (w : {w : InfinitePlace F // w.IsReal}) (x : Adeles F) : fAtR w x = x.1.1 w := rfl
@[simp] theorem fAtC_apply (w : {w : InfinitePlace F // w.IsComplex}) (x : Adeles F) : fAtC w x = x.1.2 w := rfl

theorem fAt_diag (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    fAt v (diagRing F t) = algebraMap F (v.adicCompletion F) t := rfl

theorem fAtR_diag (w : {w : InfinitePlace F // w.IsReal}) (t : F) :
    fAtR w (diagRing F t) = embedding_of_isReal w.2 t := mixedEmbedding_apply_isReal F t w

theorem fAtC_diag (w : {w : InfinitePlace F // w.IsComplex}) (t : F) :
    fAtC w (diagRing F t) = w.1.embedding t := mixedEmbedding_apply_isComplex F t w

theorem continuous_fAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (fAt v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_fAtR (w : {w : InfinitePlace F // w.IsReal}) : Continuous (fAtR w) :=
  (continuous_apply w).comp (continuous_fst.comp continuous_fst)

theorem continuous_fAtC (w : {w : InfinitePlace F // w.IsComplex}) : Continuous (fAtC w) :=
  (continuous_apply w).comp (continuous_snd.comp continuous_fst)

/-- An idele is determined by its components. -/
theorem adeles_ext {x y : Adeles F} (hR : ∀ w, fAtR w x = fAtR w y) (hC : ∀ w, fAtC w x = fAtC w y)
    (hv : ∀ v, fAt v x = fAt v y) : x = y :=
  Prod.ext (Prod.ext (funext hR) (funext hC)) (Subtype.ext (funext hv))

end Places

end QuadFormsKB.Tamagawa.Measure.Weil
