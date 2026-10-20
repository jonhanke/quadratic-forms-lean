/-
# Eichler's mass formula for a maximal order

**Layer:** $F$ totally real with $\mathcal O_F$ a PID, $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ a maximal
order with $\mathcal O_F$-basis $e$ and Gram matrix $A_{\mathcal O}$ of $\operatorname{nrd}$ in $e$ (`gramMat`).

* `qv_gramMat`, `gramMat_transform`, `isTotPosGram_gramMat`: the Gram matrix of $(\sum_i\xi_if_i, \operatorname{nrd})$ and its positivity.
* `epsteinSumIdeal_eq`: the Epstein sum of a left ideal $J$ (`epsteinSumIdeal`) is the Epstein zeta function of the lattice
  $(\mathcal O_F^4, A_J)$, $A_J$ the Gram matrix of a basis of $J$ (`epsteinLat`).
* **Eichler's mass formula** (`eichler_mass_formula`): with $\Lambda = \frac{\rho_F}2\,c_{\mathcal O}/K$,
  $$\Lambda\sum_{[J]\ne0}[\Gamma_J : \mathcal O_F^\times]^{-1} = \rho_F\,\zeta_F(2)\prod_{\mathfrak p\in\operatorname{Ram}_f(D)}(1 - N\mathfrak p^{-1}),$$
  $c_{\mathcal O} = (\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})})^{-1}|d_F|^{-2}$ (`latConst`), $K = |d_F|^{-1/2}\pi^{-2d}$ (`epsteinConst F 4 0`). Equivalently
  $\sum_{[J]}[\Gamma_J:\mathcal O_F^\times]^{-1} = 2\,|d_F|^{3/2}(\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})})\,\pi^{-2d}\zeta_F(2)\prod_{\mathfrak p\in\mathrm{Ram}_f}(1-N\mathfrak p^{-1})$.
  *Proof:* compare the residues at $s = 2$ of the two sides of the class decomposition (`zetaO_eq_tsum_class`): the Euler product on
  the left, and on the right $N(\nu_J)^{s}E'_J(s)$ (`epsteinSum_eq`) with $\operatorname{Res}E'_J = \frac{\rho_F}{2}c_J/K$ (`tendsto_sub_mul_epsteinLat`)
  and $c_J = c_{\mathcal O}N(\nu_J)^{-2}$ (the index–norm relation `span_det_eq_sq`); the class set is finite (`finite_classes`) and each
  $[\Gamma_J : \mathcal O_F^\times]$ is finite (`finiteIndex_centralUnitsIn`).

Source: Voight, *Quaternion Algebras* (2021), Thm. 26.5.4 and its proof (26.5.5)–(26.5.10) (there with right ideals, $h_F$ general,
and $\varphi(\mathfrak D)$, the evaluation of $\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})} = 4^{-d}N(\operatorname{disc}\mathcal O)$ being Thm. 15.5.5);
Weil 1982, §3.1, pp. 39–41 (Thm. 3.1.1). Locators checked in the authors' texts.
-/
import QuadFormsKB.Tamagawa.QuatEpstein

open NumberField NumberField.InfinitePlace Matrix Filter Topology
open scoped ENNReal Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.HilbertModular QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalUnfold
  QuadFormsKB.NFEuler

/-! ### The Gram matrix of the reduced norm -/

section Gram

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- **The bilinear form of $\operatorname{nrd}$**: $\langle x, y\rangle = x_0y_0 - ax_1y_1 - bx_2y_2 + abx_3y_3$. -/
def nrdBil (x y : QuatF F a b) : F :=
  x.re * y.re - algebraMap (𝓞 F) F a * x.imI * y.imI - algebraMap (𝓞 F) F b * x.imJ * y.imJ +
    algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b * x.imK * y.imK

theorem nrdBil_self (x : QuatF F a b) : nrdBil x x = nrd x := by simp only [nrdBil, nrd]; ring

theorem nrdBil_comm (x y : QuatF F a b) : nrdBil x y = nrdBil y x := by simp only [nrdBil]; ring

theorem nrdBil_sum_left (c : Fin 4 → F) (f : Fin 4 → QuatF F a b) (y : QuatF F a b) :
    nrdBil (∑ i, c i • f i) y = ∑ i, c i * nrdBil (f i) y := by
  simp only [nrdBil, re_finsetSum, imI_finsetSum, imJ_finsetSum, imK_finsetSum, QuaternionAlgebra.re_smul,
    QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem nrdBil_sum_right (c : Fin 4 → F) (f : Fin 4 → QuatF F a b) (x : QuatF F a b) :
    nrdBil x (∑ i, c i • f i) = ∑ i, c i * nrdBil x (f i) := by
  rw [nrdBil_comm, nrdBil_sum_left]; simp_rw [nrdBil_comm]

/-- **The Gram matrix** $(\langle f_i, f_j\rangle)$ of a family $f$. -/
def gramMat (f : Fin 4 → QuatF F a b) : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => nrdBil (f i) (f j)

theorem qv_gramMat (f : Fin 4 → QuatF F a b) (ξ : Fin 4 → F) : qv (gramMat f) ξ = nrd (∑ i, ξ i • f i) := by
  rw [← nrdBil_self, nrdBil_sum_left]
  simp only [qv, dotProduct, mulVec, gramMat, Matrix.of_apply, nrdBil_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gramMat_transform (e f : Fin 4 → QuatF F a b) (B : Matrix (Fin 4) (Fin 4) F)
    (hf : ∀ j, f j = ∑ i, B i j • e i) : gramMat f = Bᵀ * gramMat e * B := by
  ext i j
  simp only [gramMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hf, nrdBil_sum_left,
    nrdBil_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The coordinate matrix $C_{ri}$ = the $r$-th coordinate of $f_i$ in the basis $1, i, j, k$. -/
def coordMat (f : Fin 4 → QuatF F a b) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r i => ![(f i).re, (f i).imI, (f i).imJ, (f i).imK] r

/-- The diagonal $(1, -a, -b, ab)$ of the norm form. -/
def nrdDiag (a b : 𝓞 F) : Fin 4 → F :=
  ![1, -algebraMap (𝓞 F) F a, -algebraMap (𝓞 F) F b, algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b]

theorem gramMat_eq_coordMat (f : Fin 4 → QuatF F a b) :
    gramMat f = (coordMat f)ᵀ * Matrix.diagonal (nrdDiag a b) * coordMat f := by
  ext i j
  simp only [gramMat, Matrix.of_apply, nrdBil, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
    coordMat, nrdDiag, Fin.sum_univ_four, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  ring

theorem det_coordMat_ne_zero {f : Fin 4 → QuatF F a b} (hli : LinearIndependent F f) : (coordMat f).det ≠ 0 := by
  let fb := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
  have h := (QuaternionAlgebra.basisOneIJK (algebraMap (𝓞 F) F a) 0 (algebraMap (𝓞 F) F b)).isUnit_det fb
  rw [Module.Basis.det_apply] at h
  have hC : (QuaternionAlgebra.basisOneIJK (algebraMap (𝓞 F) F a) 0 (algebraMap (𝓞 F) F b)).toMatrix fb = coordMat f := by
    ext r i
    rw [Module.Basis.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank, QuaternionAlgebra.coe_basisOneIJK_repr]
    rfl
  rw [hC] at h
  exact h.ne_zero

/-- **The Gram matrix of a basis of a totally definite algebra is totally positive.** -/
theorem isTotPosGram_gramMat [IsTotallyReal F] (hdef : IsTotDefinite a b) {f : Fin 4 → QuatF F a b}
    (hli : LinearIndependent F f) : IsTotPosGram (gramMat f) := by
  intro v
  set σ := realEmb F v
  obtain ⟨ha, hb⟩ := hdef σ
  set C := (coordMat f).map σ
  set w : Fin 4 → ℝ := fun r => σ (nrdDiag a b r)
  have hw : ∀ r, 0 < w r := by
    intro r
    fin_cases r <;> simp [w, nrdDiag]
    · linarith
    · linarith
    · exact mul_pos_of_neg_of_neg ha hb
  have hM : (gramMat f).map σ = Cᵀ * Matrix.diagonal w * C := by
    rw [gramMat_eq_coordMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.diagonal_map (map_zero σ)]
  have hdetC : C.det ≠ 0 := by
    rw [show C.det = σ (coordMat f).det from (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ σ.injective).2 (det_coordMat_ne_zero hli)
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hM, Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]
  · set z := C *ᵥ y
    have hz : z ≠ 0 := by
      intro h0
      exact hdetC (Matrix.exists_mulVec_eq_zero_iff.1 ⟨y, hy, h0⟩)
    have hq : star y ⬝ᵥ ((gramMat f).map σ *ᵥ y) = ∑ r, w r * z r ^ 2 := by
      rw [hM, star_trivial, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hq]
    obtain ⟨r, hr⟩ : ∃ r, z r ≠ 0 := by
      by_contra hc; push Not at hc; exact hz (funext hc)
    exact Finset.sum_pos' (fun r _ => mul_nonneg (hw r).le (sq_nonneg _))
      ⟨r, Finset.mem_univ r, mul_pos (hw r) (by positivity)⟩

end Gram

/-! ### The lattice constant under change of basis -/

section LatConst

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}

variable (F) in
/-- The unit fractional ideals $(1,\dots,1)$: the standard lattice $\mathcal O_F^4$. -/
abbrev oneIdeals4 : Fin 4 → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun _ => 1

/-- $\prod_v|\sigma_v(x)| = |N_{F/\mathbb Q}(x)|$. -/
theorem prod_abs_realEmb_eq (x : F) : ∏ v : InfinitePlace F, |realEmb F v x| = |(Algebra.norm ℚ x : ℝ)| := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : v.mult = 1 := by unfold InfinitePlace.mult; rw [if_pos (IsTotallyReal.isReal v)]
  rw [hm, pow_one, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]
  rfl

/-- **The lattice constant of a sublattice** $f = eB$: $c_f\cdot|N(\det B)| = c_e$ (`latConst`, unit ideals). -/
theorem latConst_gramMat_mul (hdef : IsTotDefinite a b) {e f : Fin 4 → QuatF F a b} (hlie : LinearIndependent F e)
    (B : Matrix (Fin 4) (Fin 4) (𝓞 F)) (hf : ∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • e i) (hdet : B.det ≠ 0) :
    AdditiveZeta.latConst (gramMat f) (oneIdeals4 F) * |(Algebra.norm ℚ (algebraMap (𝓞 F) F B.det) : ℝ)| =
      AdditiveZeta.latConst (gramMat e) (oneIdeals4 F) := by
  set BF := B.map (algebraMap (𝓞 F) F)
  have hG : gramMat f = BFᵀ * gramMat e * BF := gramMat_transform e f BF hf
  have hdetBF : BF.det = algebraMap (𝓞 F) F B.det := (RingHom.map_det _ _).symm
  have hpe := isTotPosGram_gramMat hdef hlie
  have hsq : ∀ v : InfinitePlace F, Real.sqrt ((gramMat f).map (realEmb F v)).det =
      |realEmb F v (algebraMap (𝓞 F) F B.det)| * Real.sqrt ((gramMat e).map (realEmb F v)).det := by
    intro v
    have h1 : ((gramMat f).map (realEmb F v)).det = (realEmb F v BF.det) ^ 2 * ((gramMat e).map (realEmb F v)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hG,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul]; ring
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hdetBF]
  unfold AdditiveZeta.latConst
  rw [Finset.prod_congr rfl fun v _ => hsq v, Finset.prod_mul_distrib, prod_abs_realEmb_eq]
  have hP : 0 < ∏ v : InfinitePlace F, Real.sqrt ((gramMat e).map (realEmb F v)).det :=
    Finset.prod_pos fun v _ => Real.sqrt_pos.2 (hpe v).det_pos
  have hBF : algebraMap (𝓞 F) F B.det ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hdet
  have h0 : |(Algebra.norm ℚ (algebraMap (𝓞 F) F B.det) : ℝ)| ≠ 0 :=
    abs_ne_zero.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hBF)
  field_simp

end LatConst

/-! ### The Epstein sum of a left ideal as the Epstein zeta function of a lattice -/

section EpsteinIdeal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}


theorem latMem_one_iff {ξ : Fin 4 → F} : LatMem (oneIdeals4 F) ξ ↔ ∀ i, ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = ξ i := by
  simp only [LatMem, oneIdeals4, Units.val_one, SetLike.mem_coe, FractionalIdeal.mem_one_iff]

variable {J : Ideal O} {f : Fin 4 → QuatF F a b} (hfJ : ∀ j, f j ∈ idealSet J)
  (hspan : ∀ x ∈ idealSet J, ∃ c : Fin 4 → 𝓞 F, x = ∑ j, algebraMap (𝓞 F) F (c j) • f j)
  (hli : LinearIndependent F f) (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0)

include hfJ in
theorem sum_smul_mem_idealSet {ξ : Fin 4 → F} (hξ : LatMem (oneIdeals4 F) ξ) :
    ∑ i, ξ i • f i ∈ idealSet J := by
  have : ∑ i, ξ i • f i ∈ idealLat J := Submodule.sum_mem _ fun i _ => by
    obtain ⟨c, hc⟩ := latMem_one_iff.1 hξ i
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hfJ i)
  exact this

include hli in
theorem sum_smul_ne_zero {ξ : Fin 4 → F} (hξ : ξ ≠ 0) : ∑ i, ξ i • f i ≠ 0 := by
  intro h
  exact hξ (funext fun i => Fintype.linearIndependent_iff.1 hli ξ h i)

include hfJ hspan hli hdiv in
/-- **$\xi \mapsto \sum_i\xi_if_i$**: the nonzero points of $\mathcal O_F^4$ are the units of $J$. -/
def latIdealEquiv : LatPt (oneIdeals4 F) ≃ IdealUnits J where
  toFun ξ := ⟨((isUnit_iff_nrd_ne_zero _).2 fun h => sum_smul_ne_zero hli ξ.2.1 (hdiv _ h)).unit,
    sum_smul_mem_idealSet hfJ ξ.2.2⟩
  invFun x := ⟨fun j => algebraMap (𝓞 F) F ((hspan _ x.2).choose j), by
      intro h0
      apply Units.ne_zero x.1
      rw [(hspan _ x.2).choose_spec]
      exact Finset.sum_eq_zero fun j _ => by rw [show algebraMap (𝓞 F) F ((hspan _ x.2).choose j) = 0 from
        congrFun h0 j, zero_smul],
    latMem_one_iff.2 fun j => ⟨_, rfl⟩⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    have hx := (hspan _ (sum_smul_mem_idealSet hfJ ξ.2.2)).choose_spec
    simp only [IsUnit.unit_spec] at hx ⊢
    have h0 : ∑ j, (algebraMap (𝓞 F) F ((hspan _ (sum_smul_mem_idealSet hfJ ξ.2.2)).choose j) - ξ.1 j) • f j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hx, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ h0 i
    exact sub_eq_zero.1 this
  right_inv x := by
    apply Subtype.ext; apply Units.ext
    simp only [IsUnit.unit_spec]
    exact ((hspan _ x.2).choose_spec).symm

theorem latIdealEquiv_val (ξ : LatPt (oneIdeals4 F)) :
    (((latIdealEquiv hfJ hspan hli hdiv ξ).1 : (QuatF F a b)ˣ) : QuatF F a b) = ∑ i, ξ.1 i • f i := rfl

/-- **The orbits correspond** ($\mathcal O_F^\times$ acting on both sides). -/
def latIdealOrbitEquiv :
    MulAction.orbitRel.Quotient (unitsF F) (LatPt (oneIdeals4 F)) ≃
      MulAction.orbitRel.Quotient (centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b))
        (IdealUnits J) :=
  Quotient.congr (latIdealEquiv hfJ hspan hli hdiv) fun ξ ξ' => by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨w, hw⟩ := u.2
      refine ⟨⟨Units.map (algebraMap (𝓞 F) (QuatF F a b)).toMonoidHom w, w, rfl⟩, Subtype.ext (Units.ext ?_)⟩
      have hu' : u • ξ' = ξ := hu
      rw [smul_idealUnits_val, Units.val_mul, latIdealEquiv_val, latIdealEquiv_val, ← hu', smul_latPt_val]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hw, mul_smul, ← Algebra.smul_def]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
      rw [algebraMap_smul]
      exact (algebraMap_smul F (w : 𝓞 F) _).symm.trans (by rfl)
    · rintro ⟨g, hg⟩
      obtain ⟨w, hw⟩ := g.2
      refine ⟨⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom w, w, rfl⟩, ?_⟩
      apply (latIdealEquiv hfJ hspan hli hdiv).injective
      have hg' : g • latIdealEquiv hfJ hspan hli hdiv ξ' = latIdealEquiv hfJ hspan hli hdiv ξ := hg
      rw [← hg']
      apply Subtype.ext; apply Units.ext
      rw [smul_idealUnits_val, Units.val_mul, latIdealEquiv_val, latIdealEquiv_val, smul_latPt_val, ← hw]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, ← Algebra.smul_def, algebraMap_smul]
      rfl

include hfJ hspan hli hdiv in
/-- **$E'_J(t) = E_{(\mathcal O_F^4, A_J)}(t)$** for the Gram matrix $A_J$ of a basis of $J$. -/
theorem epsteinSumIdeal_eq (t : ℝ) :
    epsteinSumIdeal J t = epsteinLat (gramMat f) (oneIdeals4 F) t := by
  set e := latIdealOrbitEquiv hfJ hspan hli hdiv
  unfold epsteinSumIdeal epsteinLat
  rw [← e.tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨u, hu⟩ : ∃ u : centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b),
      u • latIdealEquiv hfJ hspan hli hdiv q.out = (e q).out := by
    have : (Quotient.mk _ (e q).out : MulAction.orbitRel.Quotient
        (centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)) (IdealUnits J)) =
        Quotient.mk _ (latIdealEquiv hfJ hspan hli hdiv q.out) := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    exact Quotient.exact this
  rw [← hu, smul_idealUnits_val, Units.val_mul, abs_norm_nrd_central, latIdealEquiv_val, ← qv_gramMat]

end EpsteinIdeal

/-! ### The residues of the class terms -/

section ClassTerm

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **The mass constant** $\Lambda = \frac{\rho_F}{2}c_{\mathcal O}/K$: $c_{\mathcal O}$ the lattice constant of $(\mathcal O, \operatorname{nrd})$ in the basis
$e$ (`latConst`), $K = |d_F|^{-1/2}\pi^{-2d}$ (`epsteinConst F 4 0`). -/
def massConst (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) : ℝ :=
  dedekindZeta_residue F / 2 * AdditiveZeta.latConst (gramMat fun i => (e i : QuatF F a b)) (oneIdeals4 F) /
    epsteinConst F 4 0

theorem linearIndependent_basis_order (hO : IsOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    LinearIndependent F fun i => (e i : QuatF F a b) := by
  have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  have h : ⇑(e.extendOfIsLattice F) = fun i => (e i : QuatF F a b) :=
    funext fun i => Module.Basis.extendOfIsLattice_apply F e i
  rw [← h]; exact (e.extendOfIsLattice F).linearIndependent

theorem abs_norm_algebraMap (x : 𝓞 F) :
    |(Algebra.norm ℚ (algebraMap (𝓞 F) F x) : ℝ)| = ((Algebra.norm ℤ x).natAbs : ℝ) := by
  rw [show (Algebra.norm ℚ (algebraMap (𝓞 F) F x) : ℝ) = ((Algebra.norm ℤ x : ℤ) : ℝ) by
    rw [← Algebra.coe_norm_int]; rfl, Nat.cast_natAbs, Int.cast_abs]

/-- **The class term of a nonzero left ideal**: $N(\operatorname{nrd}J)^{-s}E_J(s) = N^sE(s)$ with $E$ the Epstein zeta function of a
basis of $J$, and $(s-2)N^sE(s) \to \Lambda$ as $s \to 2^+$ (independent of $J$). -/
theorem exists_class_term (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    ∃ (N : ℝ) (E : ℝ → ℝ≥0∞), 0 < N ∧
      (∀ s : ℝ, 2 < s → nrdTerm J s * epsteinSum J s = ENNReal.ofReal (N ^ s) * E s ∧ E s < ⊤) ∧
      Tendsto (fun s : ℝ => (s - 2) * (N ^ s * (E s).toReal)) (𝓝[>] 2) (𝓝 (massConst e)) := by
  obtain ⟨ν, hν⟩ := (IsPrincipalIdealRing.principal (leftNrdIdeal J)).principal
  have hν' : leftNrdIdeal J = Ideal.span {ν} := hν
  have hν0 : ν ≠ 0 := by rintro rfl; exact hJ (by rw [hν', Ideal.span_singleton_eq_bot.2 rfl])
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
  obtain ⟨f, B, hfJ, hspan, -, hB, hdet, hli⟩ := exists_ideal_basis hO.1 e hν0 hν'
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  set N : ℝ := |(Algebra.norm ℚ (algebraMap (𝓞 F) F ν) : ℝ)|
  have hN : 0 < N := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hνF)
  set A := gramMat f
  have hA : IsTotPosGram A := isTotPosGram_gramMat hdef hli
  refine ⟨N, epsteinLat A (oneIdeals4 F), hN, fun s hs => ⟨?_, ?_⟩, ?_⟩
  · have h1 : nrdTerm J s = ENNReal.ofReal (N ^ (-s)) := by
      unfold nrdTerm
      rw [hν', Ideal.absNorm_span_singleton]
      congr 2
      simp only [N, abs_norm_algebraMap]
    rw [h1, epsteinSum_eq ha hb hO hν0 hν' s, epsteinSumIdeal_eq hfJ hspan hli hdiv s, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1; push_cast; ring
  · exact epsteinLat_lt_top hA (oneIdeals4 F) (by norm_num) (by push_cast; linarith)
  · have h := tendsto_sub_mul_epsteinLat hA (oneIdeals4 F) (n := 4) (by norm_num)
    have h42 : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
    rw [h42] at h
    have hpow : Tendsto (fun s : ℝ => N ^ s) (𝓝[>] 2) (𝓝 (N ^ (2 : ℝ))) :=
      ((Real.continuousAt_const_rpow hN.ne').tendsto).mono_left nhdsWithin_le_nhds
    have h2 := hpow.mul h
    have hlat := latConst_gramMat_mul hdef (linearIndependent_basis_order hO.1 e) B hB hdet
    have hNdet : |(Algebra.norm ℚ (algebraMap (𝓞 F) F B.det) : ℝ)| = N ^ 2 := by
      rw [abs_norm_algebraMap, natAbs_norm_det_eq ha hb hO e hν0 hν' f hspan hfJ B hB hdet, Nat.cast_pow]
      simp only [N, abs_norm_algebraMap]
    have hlim : N ^ (2 : ℝ) * (dedekindZeta_residue F / 2 * AdditiveZeta.latConst A (oneIdeals4 F) / epsteinConst F 4 0) =
        massConst e := by
      rw [massConst, ← hlat, hNdet, Real.rpow_two]
      ring
    rw [hlim] at h2
    exact h2.congr fun s => by ring

theorem nrdTerm_bot {s : ℝ} (hs : s ≠ 0) : nrdTerm (⊥ : Ideal O) s = 0 := by
  unfold nrdTerm
  have h : leftNrdIdeal (⊥ : Ideal O) = ⊥ := by
    unfold leftNrdIdeal
    rw [eq_bot_iff, Ideal.span_le]
    rintro r ⟨x, hx, hr⟩
    rw [(Submodule.mem_bot _).1 hx] at hr
    simp only [SetLike.mem_coe, Submodule.mem_bot] at hr ⊢
    have : algebraMap (𝓞 F) F r = 0 := by rw [hr]; simp [nrd]
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this
  rw [h, Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.2 hs), ENNReal.ofReal_zero]

theorem eq_bot_of_idealRel_bot {J' : Ideal O} (h : IdealRel (⊥ : Ideal O) J') : J' = ⊥ := by
  obtain ⟨β, hβ⟩ := h
  apply idealSet_injective
  rw [hβ]
  have h0 : idealSet (⊥ : Ideal O) = {0} := by
    ext x
    simp only [idealSet, Set.mem_ofPred_eq, Submodule.mem_bot, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, h⟩; exact congrArg Subtype.val h
    · rintro rfl; exact ⟨O.zero_mem, rfl⟩
  rw [h0]
  ext x
  simp [rTrans]

end ClassTerm

/-! ### Eichler's mass formula -/

section Mass

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- `nrdTerm` of `QuatClassSum`, restated with the `Algebra` instance of this file (definitionally equal). -/
def nrdTermR (J : Ideal O) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm (leftNrdIdeal J) : ℝ) ^ (-s))

/-- **Eichler's mass formula** (Voight 2021, Thm. 26.5.4; Weil 1982, Thm. 3.1.1): for a maximal order $\mathcal O \supseteq \mathcal O_F\langle
1,i,j,k\rangle$ of a totally definite quaternion algebra over a totally real field with $h_F = 1$,
$$\Lambda\sum_{[J]\ne0}\frac{1}{[\Gamma_J:\mathcal O_F^\times]} = \rho_F\,\zeta_F(2)\prod_{\mathfrak p\in\operatorname{Ram}_f(D)}(1 - N\mathfrak p^{-1}),
  \qquad \Lambda = \texttt{massConst}\ e = \frac{\rho_F}{2}\,\frac{c_{\mathcal O}}{|d_F|^{-1/2}\pi^{-2d}},$$
the sum over the (finitely many, `finite_classes`) classes of nonzero left ideals, $\Gamma_J$ the unit group of the right order of $J$. -/
@[kb "voight2021" "Thm. 26.5.4; (26.5.5)–(26.5.10)"]
theorem eichler_mass_formula (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    massConst e * ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
        (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      dedekindZeta_residue F * dedekindZetaR F 2 * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := finite_classes ha hb hO hdiv
  let _ : Fintype (Quotient (idealSetoid O)) := Fintype.ofFinite _
  set C := {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
  have hnrd : ∀ c : C, leftNrdIdeal c.1.out ≠ ⊥ := fun c => leftNrdIdeal_ne_bot hO.1 hdiv c.2
  choose N E hN hNE hlim using fun c : C => exists_class_term ha hb hdef hO e (hnrd c)
  have hfin : ∀ c : C, (centralUnitsIn (R := 𝓞 F) c.1.out).FiniteIndex := fun c =>
    finiteIndex_centralUnitsIn (O := O) hdef hO.1 hstd c.2
  set idx : C → ℝ := fun c => (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)
  have hidx : ∀ c, 0 < idx c := fun c => by
    have := (hfin c).index_ne_zero
    simp only [idx]; exact_mod_cast Nat.pos_of_ne_zero this
  -- the class decomposition, in ℝ, for s > 2
  have hdec : ∀ s : ℝ, 2 < s → ∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s) =
      ∑ c : C, (idx c)⁻¹ * (N c ^ s * (E c s).toReal) := by
    intro s hs
    have hs0 : s ≠ 0 := by linarith
    have h1 : ∑' J : Ideal O, nrdTermR J s =
        ENNReal.ofReal (∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)) :=
      tsum_nrdTerm_eq ha hb hO hs
    rw [tsum_ideal_eq_tsum_class (fun J => nrdTermR J s)] at h1
    have h2 : ∀ c : Quotient (idealSetoid O), ∑' J' : {J' : Ideal O // IdealRel c.out J'}, nrdTermR J'.1 s =
        if h : c.out = ⊥ then 0 else
          ENNReal.ofReal (idx ⟨c, h⟩)⁻¹ * (ENNReal.ofReal (N ⟨c, h⟩ ^ s) * E ⟨c, h⟩ s) := by
      intro c
      split_ifs with h
      · refine ENNReal.tsum_eq_zero.2 fun J' => ?_
        have : J'.1 = ⊥ := eq_bot_of_idealRel_bot (h ▸ J'.2)
        rw [this]; exact nrdTerm_bot hs0
      · have hfc : (centralUnitsIn (R := 𝓞 F) c.out).FiniteIndex := hfin ⟨c, h⟩
        have h3 : ((centralUnitsIn (R := 𝓞 F) c.out).index : ℝ≥0∞) *
            ∑' J' : {J' : Ideal O // IdealRel c.out J'}, nrdTermR J'.1 s =
            nrdTermR c.out s * epsteinSumColon c.out s := @index_mul_tsum_class_nrd F _ _ a b O hO.1 c.out hfc s
        have h3' : nrdTermR c.out s * epsteinSumColon c.out s = ENNReal.ofReal (N ⟨c, h⟩ ^ s) * E ⟨c, h⟩ s :=
          (hNE ⟨c, h⟩ s hs).1
        rw [h3'] at h3
        have hi0 : ((centralUnitsIn (R := 𝓞 F) c.out).index : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast hfc.index_ne_zero
        rw [← h3, ← mul_assoc, ENNReal.ofReal_inv_of_pos (hidx ⟨c, h⟩)]
        rw [show ENNReal.ofReal (idx ⟨c, h⟩) = ((centralUnitsIn (R := 𝓞 F) c.out).index : ℝ≥0∞) by
          simp only [idx]; exact ENNReal.ofReal_natCast _]
        rw [ENNReal.inv_mul_cancel hi0 (ENNReal.natCast_ne_top _), one_mul]
    simp_rw [h2] at h1
    rw [tsum_fintype] at h1
    have h4 : ∑ c : Quotient (idealSetoid O), (if h : c.out = ⊥ then (0 : ℝ≥0∞) else
        ENNReal.ofReal (idx ⟨c, h⟩)⁻¹ * (ENNReal.ofReal (N ⟨c, h⟩ ^ s) * E ⟨c, h⟩ s)) =
        ∑ c : C, ENNReal.ofReal (idx c)⁻¹ * (ENNReal.ofReal (N c ^ s) * E c s) := by
      rw [← Finset.sum_filter_of_ne (p := fun c : Quotient (idealSetoid O) => c.out ≠ ⊥) (fun c _ hc => by
        intro h0; apply hc; rw [dif_pos h0])]
      rw [Finset.sum_subtype (Finset.univ.filter fun c : Quotient (idealSetoid O) => c.out ≠ ⊥)
        (p := fun c : Quotient (idealSetoid O) => c.out ≠ ⊥) (fun c => by simp)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dif_neg c.2]
    rw [h4] at h1
    have hnn : 0 ≤ ∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s) :=
      tsum_nonneg fun 𝔫 => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h5 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_sum (fun c _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNE c s hs).2.ne))] at h5
    rw [← h5]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (hidx c).le),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hN c).le _)]
  -- the two limits
  have hL : Tendsto (fun s : ℝ => (s - 2) * ∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s))
      (𝓝[>] 2) (𝓝 (∑ c : C, (idx c)⁻¹ * massConst e)) := by
    have h := tendsto_finset_sum (Finset.univ : Finset C) fun c _ => (hlim c).const_mul (idx c)⁻¹
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hdec s hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hR := tendsto_sub_mul_zetaO ha hb hO
  have huniq := tendsto_nhds_unique hL hR
  rw [← huniq, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The mass constant in closed form**: $\Lambda = \frac{\rho_F}{2}\,|d_F|^{-3/2}\pi^{2d}\big(\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})}\big)^{-1}$,
$d$ = the number of real places. -/
theorem massConst_eq (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    massConst e = dedekindZeta_residue F / 2 * (NumberField.discr F : ℝ) ^ (-(3 / 2 : ℝ)) *
      π ^ (2 * Fintype.card (InfinitePlace F)) *
      (∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (e i : QuatF F a b)).map (realEmb F v)).det)⁻¹ := by
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  have hemb : embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) = Real.sqrt (NumberField.discr F) := by
    rw [AdditiveZeta.embDet_eq]; simp
  unfold massConst AdditiveZeta.latConst epsteinConst
  rw [SphericalFibration.ideleConst_eq]
  simp only [oneIdeals4, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hemb]
  have h2 : ((4 : ℕ) : ℝ) + 2 * 0 = 4 := by norm_num
  rw [h2, show (4 : ℝ) / 2 = 2 by norm_num, Real.Gamma_two, mul_one, abs_of_pos hd,
    show -(4 : ℝ) / 2 = -2 by norm_num]
  have hs : Real.sqrt (NumberField.discr F : ℝ) ^ 4 = (NumberField.discr F : ℝ) ^ (2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
  rw [hs]
  have hpi : (π ^ (-2 : ℝ)) ^ Fintype.card (InfinitePlace F) = (π ^ (2 * Fintype.card (InfinitePlace F)))⁻¹ := by
    rw [Real.rpow_neg Real.pi_pos.le, inv_pow, Real.rpow_two, ← pow_mul]
  rw [hpi]
  have hd32 : (NumberField.discr F : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((NumberField.discr F : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * ((NumberField.discr F : ℝ) ^ (2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hd.le, ← Real.rpow_neg hd.le, ← Real.rpow_add hd]; norm_num
  rw [hd32]
  have h1 : 0 < (NumberField.discr F : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hd _
  have h3 : 0 < (NumberField.discr F : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hd _
  have hπ : 0 < π ^ (2 * Fintype.card (InfinitePlace F)) := pow_pos Real.pi_pos _
  field_simp

/-- **Eichler's mass formula, closed form** (Voight 2021, Thm. 26.5.4 with $h_F = 1$):
$$\sum_{[J]\ne0}\frac1{[\Gamma_J:\mathcal O_F^\times]} = 2\,|d_F|^{3/2}\,\pi^{-2d}\Big(\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})}\Big)\,\zeta_F(2)
  \prod_{\mathfrak p\in\operatorname{Ram}_f(D)}(1 - N\mathfrak p^{-1}),$$
$A_{\mathcal O}$ the Gram matrix of $\operatorname{nrd}$ in an $\mathcal O_F$-basis of $\mathcal O$, $d$ the number of real places. (Voight's form follows from
$\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})} = 4^{-d}\prod_{\mathfrak p\in\mathrm{Ram}_f}N\mathfrak p$, his Thm. 15.5.5 on $\operatorname{disc}\mathcal O$, not
formalized here.) -/
@[kb "voight2021" "Thm. 26.5.4"]
theorem eichler_mass_formula' (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      2 * (NumberField.discr F : ℝ) ^ (3 / 2 : ℝ) * (π ^ (2 * Fintype.card (InfinitePlace F)))⁻¹ *
        (∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (e i : QuatF F a b)).map (realEmb F v)).det) *
        dedekindZetaR F 2 * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := by
  have h := eichler_mass_formula ha hb hdef hO hstd e
  have hρ := dedekindZeta_residue_pos F
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  have hP : 0 < ∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (e i : QuatF F a b)).map (realEmb F v)).det :=
    Finset.prod_pos fun v _ => Real.sqrt_pos.2
      ((isTotPosGram_gramMat hdef (linearIndependent_basis_order hO.1 e)) v).det_pos
  have hM : 0 < massConst e := by
    rw [massConst_eq]
    exact mul_pos (mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hd _)) (pow_pos Real.pi_pos _))
      (inv_pos.2 hP)
  have hsum : ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
      (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      (dedekindZeta_residue F * dedekindZetaR F 2 * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) /
        massConst e := by
    rw [eq_div_iff hM.ne', mul_comm]; exact h
  rw [hsum, massConst_eq]
  generalize ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) = R
  generalize ∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (e i : QuatF F a b)).map (realEmb F v)).det = Q at hP ⊢
  have h32 : (NumberField.discr F : ℝ) ^ (-(3 / 2 : ℝ)) = ((NumberField.discr F : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg hd.le _
  rw [h32]
  have h1 : 0 < (NumberField.discr F : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hd _
  have hπ : 0 < π ^ (2 * Fintype.card (InfinitePlace F)) := pow_pos Real.pi_pos _
  field_simp

end Mass

end QuadFormsKB.QuatOrder
