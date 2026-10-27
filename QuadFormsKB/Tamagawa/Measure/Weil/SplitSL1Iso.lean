import QuadFormsKB.Tamagawa.Measure.Weil.PDSplitReduction
import QuadFormsKB.Tamagawa.Measure.Weil.QuatSplitIso
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Local

/-!
# $\mathrm{SL}_1(D)(\mathbb A)\cong\mathrm{SL}_2(\mathbb A_F)$ for split $D$

**Layer:** $F$ a number field, $a, b\in F^\times$, $x, y\in F$ with $x^2 - ay^2 = b$, so that
$D = \mathbb H[F,a,b]\cong M_2(F)$ (`quatMatEquiv`, `QuatSplitIso.lean`).

Base change of `quatMatEquiv` to the adeles (with $a, b, x, y$ replaced by their diagonal images) is an isomorphism
$\Phi : \mathbb H[\mathbb A_F,a,b]\to M_2(\mathbb A_F)$ of topological $\mathbb A_F$-algebras with
$\det\Phi(q) = \operatorname{nrd}(q)$. It restricts to an isomorphism of topological groups

$$\psi : \mathrm{SL}_1(D)(\mathbb A)\to\mathrm{SL}_2(\mathbb A_F)$$

(`sl1SplitEquiv`), which carries $\mathrm{SL}_1(D)(F)$ (`SL1F`) onto the diagonal image of $\mathrm{SL}_2(F)$ (`slSub`):
**`map_SL1F_sl1SplitEquiv`**. On diagonal elements $\Phi$ is the diagonal image of `quatMatEquiv` over $F$
(`quatAdeleMatEquiv_quatDiagRing`).
-/

open Matrix MeasureTheory
open scoped Quaternion MatrixGroups

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-! ### Invertibility of diagonal elements -/

/-- $\operatorname{diag}(c)$ is invertible in $\mathbb A_F$ for $c\ne 0$. -/
def invertibleDiag {c : F} (hc : c ≠ 0) : Invertible (diag F c) :=
  letI : Invertible c := invertibleOfNonzero hc
  Invertible.map (diagRing F) c

/-- $2$ is invertible in $\mathbb A_F$. -/
def invertibleTwoAdele : Invertible (2 : Adeles F) :=
  (invertibleDiag (F := F) (two_ne_zero : (2 : F) ≠ 0)).copy _
    (by rw [← diagRing_apply, map_ofNat])

/-! ### The adelic isomorphism $\Phi$ -/

variable {a b x y : F}

theorem diag_split (h : x ^ 2 - a * y ^ 2 = b) :
    diag F x ^ 2 - diag F a * diag F y ^ 2 = diag F b := by
  simp only [← diagRing_apply, ← map_pow, ← map_mul, ← map_sub, h]

variable (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

/-- **$\Phi : \mathbb H[\mathbb A_F,a,b]\cong M_2(\mathbb A_F)$**, the base change of `quatMatEquiv`. -/
def quatAdeleMatEquiv : QuatAdele a b ≃ₐ[Adeles F] Matrix (Fin 2) (Fin 2) (Adeles F) :=
  letI := invertibleTwoAdele (F := F)
  letI := invertibleDiag ha0
  letI := invertibleDiag hb0
  quatMatEquiv (diag F a) (diag F b) (diag F x) (diag F y) (diag_split h)

theorem quatAdeleMatEquiv_apply (q : QuatAdele a b) :
    quatAdeleMatEquiv ha0 hb0 h q = !![q.re + q.imJ * diag F x + q.imK * (diag F a * diag F y),
      q.imI * diag F a - q.imJ * (diag F a * diag F y) - q.imK * (diag F a * diag F x);
      q.imI + q.imJ * diag F y + q.imK * diag F x,
      q.re - q.imJ * diag F x - q.imK * (diag F a * diag F y)] :=
  quatMatHom_apply _ _ _ _ _ q

/-- $\det\Phi(q) = \operatorname{nrd}(q)$. -/
theorem det_quatAdeleMatEquiv (q : QuatAdele a b) : (quatAdeleMatEquiv ha0 hb0 h q).det = (q * star q).re :=
  det_quatMatHom _ _ _ _ _ q

theorem continuous_quatAdeleMatEquiv : Continuous (quatAdeleMatEquiv ha0 hb0 h) := by
  have h0 := continuous_re a b
  have h1 := continuous_imI a b
  have h2 := continuous_imJ a b
  have h3 := continuous_imK a b
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [quatAdeleMatEquiv_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;> fun_prop

theorem continuous_quatAdeleMatEquiv_symm : Continuous (quatAdeleMatEquiv ha0 hb0 h).symm := by
  let := invertibleTwoAdele (F := F)
  let := invertibleDiag ha0
  let := invertibleDiag hb0
  have he : ⇑(quatAdeleMatEquiv ha0 hb0 h).symm = quatMatInv (diag F a) (diag F b) (diag F x) (diag F y) := by
    funext m
    apply (quatAdeleMatEquiv ha0 hb0 h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (quatMatHom_quatMatInv _ _ _ _ (diag_split h) m).symm
  rw [he]
  have hc : ∀ i j : Fin 2, Continuous fun m : Matrix (Fin 2) (Fin 2) (Adeles F) => m i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have h00 := hc 0 0
  have h01 := hc 0 1
  have h10 := hc 1 0
  have h11 := hc 1 1
  refine (continuous_quat_iff a b).mpr ⟨?_, ?_, ?_, ?_⟩ <;> simp only [quatMatInv] <;> fun_prop

/-- $\Phi$ as a homeomorphism. -/
def quatAdeleMatHomeo : QuatAdele a b ≃ₜ Matrix (Fin 2) (Fin 2) (Adeles F) where
  toEquiv := (quatAdeleMatEquiv ha0 hb0 h).toEquiv
  continuous_toFun := continuous_quatAdeleMatEquiv ha0 hb0 h
  continuous_invFun := continuous_quatAdeleMatEquiv_symm ha0 hb0 h

/-! ### $\Phi$ on diagonal elements -/

/-- `quatMatEquiv` over $F$. -/
def quatFMatEquiv : ℍ[F,a,b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible a := invertibleOfNonzero ha0
  letI : Invertible b := invertibleOfNonzero hb0
  quatMatEquiv a b x y h

theorem det_quatFMatEquiv (q : ℍ[F,a,b]) : (quatFMatEquiv ha0 hb0 h q).det = (q * star q).re :=
  det_quatMatHom _ _ _ _ _ q

/-- **On diagonal elements, $\Phi$ is the diagonal image of `quatMatEquiv` over $F$.** -/
theorem quatAdeleMatEquiv_quatDiagRing (ξ : ℍ[F,a,b]) :
    quatAdeleMatEquiv ha0 hb0 h (quatDiagRing a b ξ) = (quatFMatEquiv ha0 hb0 h ξ).map (diagRing F) := by
  rw [quatAdeleMatEquiv_apply, quatFMatEquiv, quatMatEquiv_apply, quatMatHom_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.map_apply,
      quatDiagRing_apply, quatDiag] <;>
    simp only [← diagRing_apply, map_add, map_sub, map_mul]

/-! ### $\psi : \mathrm{SL}_1(D)(\mathbb A)\cong\mathrm{SL}_2(\mathbb A_F)$ -/

theorem nrdUnit_eq_one_iff (u : (QuatAdele a b)ˣ) :
    nrdUnit u = 1 ↔ (quatAdeleMatEquiv ha0 hb0 h (u : QuatAdele a b)).det = 1 := by
  rw [det_quatAdeleMatEquiv, ← nrdUnit_val, Units.val_eq_one]

/-- The forward map $\mathrm{SL}_1(D)(\mathbb A)\to\mathrm{SL}_2(\mathbb A_F)$. -/
def sl1SplitFun (k : SL1A a b) : SL2A F :=
  ⟨quatAdeleMatEquiv ha0 hb0 h (((k : quatOne a b) : (QuatAdele a b)ˣ) : QuatAdele a b),
    (nrdUnit_eq_one_iff ha0 hb0 h _).1 (mem_SL1A.1 k.2)⟩

/-- The unit $\Phi^{-1}(g)$ for $g\in\mathrm{SL}_2(\mathbb A_F)$. -/
def sl1SplitUnit (g : SL2A F) : (QuatAdele a b)ˣ where
  val := (quatAdeleMatEquiv ha0 hb0 h).symm (g : Matrix (Fin 2) (Fin 2) (Adeles F))
  inv := (quatAdeleMatEquiv ha0 hb0 h).symm ((g⁻¹ : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F))
  val_inv := by
    rw [← map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      map_one]
  inv_val := by
    rw [← map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      map_one]

theorem nrdUnit_sl1SplitUnit (g : SL2A F) : nrdUnit (sl1SplitUnit ha0 hb0 h g) = 1 := by
  rw [nrdUnit_eq_one_iff ha0 hb0 h]
  change (quatAdeleMatEquiv ha0 hb0 h ((quatAdeleMatEquiv ha0 hb0 h).symm _)).det = 1
  rw [AlgEquiv.apply_symm_apply]; exact g.2

/-- The inverse map $\mathrm{SL}_2(\mathbb A_F)\to\mathrm{SL}_1(D)(\mathbb A)$. -/
def sl1SplitInv (g : SL2A F) : SL1A a b :=
  ⟨⟨sl1SplitUnit ha0 hb0 h g, by rw [mem_quatOne, nrdUnit_sl1SplitUnit, ideleNorm_one]⟩,
    mem_SL1A.2 (nrdUnit_sl1SplitUnit ha0 hb0 h g)⟩

theorem continuous_sl1SplitFun : Continuous (sl1SplitFun ha0 hb0 h) :=
  ((continuous_quatAdeleMatEquiv ha0 hb0 h).comp
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

theorem continuous_sl1SplitInv : Continuous (sl1SplitInv ha0 hb0 h) := by
  refine (Continuous.subtype_mk ?_ _).subtype_mk _
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_quatAdeleMatEquiv_symm ha0 hb0 h).comp continuous_subtype_val
  · exact (continuous_quatAdeleMatEquiv_symm ha0 hb0 h).comp (continuous_subtype_val.comp continuous_inv)

/-- **$\psi : \mathrm{SL}_1(D)(\mathbb A)\cong\mathrm{SL}_2(\mathbb A_F)$** as topological groups ($D = \mathbb H[F,a,b]$
split by $x^2 - ay^2 = b$). -/
def sl1SplitEquiv : SL1A a b ≃ₜ* SL2A F where
  toFun := sl1SplitFun ha0 hb0 h
  invFun := sl1SplitInv ha0 hb0 h
  left_inv k := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact (quatAdeleMatEquiv ha0 hb0 h).symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    exact (quatAdeleMatEquiv ha0 hb0 h).apply_symm_apply _
  map_mul' k l := by
    apply Subtype.ext
    change quatAdeleMatEquiv ha0 hb0 h (_ * _) = _ * _
    exact map_mul _ _ _
  continuous_toFun := continuous_sl1SplitFun ha0 hb0 h
  continuous_invFun := continuous_sl1SplitInv ha0 hb0 h

theorem coe_sl1SplitEquiv (k : SL1A a b) :
    ((sl1SplitEquiv ha0 hb0 h k : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) =
      quatAdeleMatEquiv ha0 hb0 h (((k : quatOne a b) : (QuatAdele a b)ˣ) : QuatAdele a b) := rfl

/-! ### $\psi(\mathrm{SL}_1(D)(F)) = \mathrm{SL}_2(F)$ -/

theorem mem_SL1F_iff (k : SL1A a b) :
    k ∈ SL1F a b ↔ ∃ ξ : (ℍ[F,a,b])ˣ, Units.map (quatDiagRing a b).toMonoidHom ξ = (k : quatOne a b) := by
  rfl

/-- **$\psi$ carries $\mathrm{SL}_1(D)(F)$ onto $\mathrm{SL}_2(F)$**: $k\in\mathrm{SL}_1(D)(F)$ iff
$\psi(k)\in\mathrm{SL}_2(F)$. -/
theorem mem_SL1F_iff_sl1SplitEquiv_mem (k : SL1A a b) :
    k ∈ SL1F a b ↔ sl1SplitEquiv ha0 hb0 h k ∈ slSub F := by
  rw [mem_SL1F_iff]
  constructor
  · rintro ⟨ξ, hξ⟩
    have hk : ((k : quatOne a b) : (QuatAdele a b)ˣ) = quatDiagRing a b (ξ : ℍ[F,a,b]) := by
      rw [← hξ]; rfl
    have hdet : (quatFMatEquiv ha0 hb0 h (ξ : ℍ[F,a,b])).det = 1 := by
      apply diag_injective (F := F)
      have h1 := (sl1SplitEquiv ha0 hb0 h k).2
      rw [coe_sl1SplitEquiv, hk, quatAdeleMatEquiv_quatDiagRing, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det] at h1
      rw [← diagRing_apply, h1, ← diagRing_apply, map_one]
    refine ⟨⟨_, hdet⟩, ?_⟩
    apply Subtype.ext
    change (quatFMatEquiv ha0 hb0 h (ξ : ℍ[F,a,b])).map (diagRing F) = _
    rw [coe_sl1SplitEquiv, hk, quatAdeleMatEquiv_quatDiagRing]
  · rintro ⟨γ, hγ⟩
    set e := quatFMatEquiv ha0 hb0 h
    let ξ : (ℍ[F,a,b])ˣ :=
      ⟨e.symm (γ : Matrix (Fin 2) (Fin 2) F), e.symm ((γ⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F),
        by rw [← map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, map_one],
        by rw [← map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, map_one]⟩
    refine ⟨ξ, ?_⟩
    apply Units.ext
    apply (quatAdeleMatEquiv ha0 hb0 h).injective
    change quatAdeleMatEquiv ha0 hb0 h (quatDiagRing a b (e.symm (γ : Matrix (Fin 2) (Fin 2) F))) = _
    rw [quatAdeleMatEquiv_quatDiagRing, AlgEquiv.apply_symm_apply, ← coe_sl1SplitEquiv, ← hγ]
    rfl

/-- **$\psi(\mathrm{SL}_1(D)(F)) = \mathrm{SL}_2(F)$** as subgroups. -/
theorem map_SL1F_sl1SplitEquiv :
    (SL1F a b).map (sl1SplitEquiv ha0 hb0 h).toMulEquiv.toMonoidHom = slSub F := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩; exact (mem_SL1F_iff_sl1SplitEquiv_mem ha0 hb0 h k).1 hk
  · intro hg
    refine ⟨(sl1SplitEquiv ha0 hb0 h).symm g, ?_, (sl1SplitEquiv ha0 hb0 h).apply_symm_apply g⟩
    change _ ∈ SL1F a b
    rw [mem_SL1F_iff_sl1SplitEquiv_mem ha0 hb0 h, ContinuousMulEquiv.apply_symm_apply]
    exact hg

end QuadFormsKB.Tamagawa.Measure.Weil
