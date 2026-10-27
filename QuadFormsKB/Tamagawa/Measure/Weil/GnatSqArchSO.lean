import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqAdelic
import QuadFormsKB.Tamagawa.Measure.Weil.PDArch
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArch
import QuadFormsKB.Tamagawa.Measure.OrbitImage

/-!
# The archimedean SO side of the square model: $x\mapsto\alpha x\beta^{-1} = L_{\alpha\beta^{-1}}\circ c_\beta$

**Layer:** one archimedean place $w$ of a number field $F$ (real or complex, any signature), $D_w = \mathbb H[F_w,a,b]$ (`HRe`,
`HCx`), $Q = \langle1,-a,-b,ab\rangle^{\sigma_w}$ (`QRe (qSq a b) w`) $= \langle1\rangle\perp Q'$ with $Q' = \langle-a,-b,ab\rangle^{\sigma_w}$
(`qRe_qSq_eq`, `qCx_qSq_eq`).

* The **left multiplication section** $x\mapsto L_x$ of the orbit map $SO(Q)\to S_1 = \{Q = 1\}$, $g\mapsto g(1)$ (`lmulSecR`, `lmulSecC`):
  $L_x(1) = x$ (`lmulSecR_spec`).
* The conjugation $c_\beta\in SO(Q')$ (`conjRloc`, `conjCloc`) and the embedding $h\mapsto\mathrm{diag}(1,h)$ (`iotaR'`, `iotaC'`).
* **`sqMat_eq_sec_mul_iota`**: the matrix of $x\mapsto\alpha x\beta^{-1}$ ($\operatorname{nrd}\alpha = \operatorname{nrd}\beta$) is
  $L_{\alpha\beta^{-1}}\cdot\mathrm{diag}(1, c_\beta)$.
* **`lerayMeasure_boxR`**, **`lerayMeasureC_boxC`**: the Leray measure of the orbit box $U(A,W) = \{L_x\,\mathrm{diag}(1,h) : x\in A,\ h\in W\}$
  is $|2|_w^{-3}\,\sigma_w(A)\,\mu_{Q'}(W)$ (the orbital identity with the section $L$); and `mem_boxR_iff`: the
  decomposition is unique.
-/

open MeasureTheory Measure Matrix Set NumberField NumberField.InfinitePlace
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Quaternion matrices -/

section Generic

variable {K : Type*} [Field K] {A B : K}

theorem sqMat_mulVec (x y : ℍ[K,A,B]) (v : Fin 4 → K) : sqMat x y *ᵥ v = qVec (x * vecQ v * y) := by
  funext i
  fin_cases i <;>
  simp [sqMat, qVec, vecQ, mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem sqMat_mul (x y x' y' : ℍ[K,A,B]) : sqMat x y * sqMat x' y' = sqMat (x * x') (y' * y) := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← Matrix.mulVec_mulVec, sqMat_mulVec, sqMat_mulVec, sqMat_mulVec, vecQ_qVec]
  congr 1
  noncomm_ring

theorem sqMat_one_one : sqMat (1 : ℍ[K,A,B]) 1 = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [sqMat_mulVec, one_mul, mul_one, qVec_vecQ, Matrix.one_mulVec]

theorem vecQ_e₀ : (vecQ (e₀ : Fin 4 → K) : ℍ[K,A,B]) = 1 := by
  ext <;> simp [vecQ, e₀] <;> rfl

/-- **$x\mapsto\beta x\beta^{-1}$ is $\mathrm{diag}(1, c_\beta)$** in the basis $1, i, j, k$. -/
theorem sqMat_conj (β : (ℍ[K,A,B])ˣ) :
    sqMat (β : ℍ[K,A,B]) ((β⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) =
      cornerMat 1 ((conjGL β : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [sqMat_mulVec]
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (Pi.single 0 1 : Fin 4 → K) = e₀ := by
      funext i; fin_cases i <;> rfl
    rw [h0, vecQ_e₀, mul_one, Units.mul_inv, cornerMat_one_mulVec_e₀]
    funext i; fin_cases i <;> simp [qVec, e₀] <;> rfl
  · have hp : (vecQ (Pi.single j.succ 1 : Fin 4 → K) : ℍ[K,A,B]) = Quat.pure (Pi.single j 1) := by
      ext <;> fin_cases j <;> simp [vecQ, Quat.pure]
    rw [hp]
    have hre := QuadFormsKB.Quat.re_conj β (Pi.single j 1)
    have himv : conjLin β (Pi.single j 1) =
        imv ((β : ℍ[K,A,B]) * Quat.pure (Pi.single j 1) * ((β⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])) := rfl
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [qVec, Matrix.cons_val_zero]
      rw [hre]
      simp [mulVec, dotProduct, Fin.sum_univ_succ, cornerMat]
    · have e1 : (cornerMat 1 ((conjGL β : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (Pi.single j.succ 1 : Fin 4 → K)) i.succ =
          (((conjGL β : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j 1 : Fin 3 → K)) i := by
        simp only [mulVec, dotProduct, Fin.sum_univ_succ, cornerMat_succ_zero, cornerMat_succ_succ,
          Pi.single_apply, Fin.succ_ne_zero, if_false, mul_zero, zero_mul, zero_add, Fin.succ_inj]
      rw [e1, show ((conjGL β : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = LinearMap.toMatrix' (conjLin β) from rfl,
        LinearMap.toMatrix'_mulVec, himv]
      fin_cases i <;> rfl

/-- **$x\mapsto\alpha x\beta^{-1} = L_{\alpha\beta^{-1}}\circ c_\beta$** in matrices. -/
theorem sqMat_eq_sec_mul_iota (α β : (ℍ[K,A,B])ˣ) :
    sqMat (α : ℍ[K,A,B]) ((β⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) =
      sqMat (((α * β⁻¹ : (ℍ[K,A,B])ˣ)) : ℍ[K,A,B]) 1 *
        cornerMat 1 ((conjGL β : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [← sqMat_conj, sqMat_mul, mul_one, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

/-- A quaternion of reduced norm $1$ as a unit. -/
def unitOfNrdOne (x : ℍ[K,A,B]) (hx : nrd x = 1) : (ℍ[K,A,B])ˣ where
  val := x
  inv := star x
  val_inv := by rw [mul_star_eq_nrd, hx]; rfl
  inv_val := by rw [star_mul_eq_nrd, hx]; rfl

theorem nrd_vecQ (v : Fin 4 → K) :
    nrd (vecQ v : ℍ[K,A,B]) = v 0 ^ 2 - A * v 1 ^ 2 - B * v 2 ^ 2 + A * B * v 3 ^ 2 := rfl

end Generic

/-! ### The forms at an archimedean place -/

theorem cornerMat_diagonal' {R : Type*} [CommRing R] {m : ℕ} (c : R) (d : Fin m → R) :
    cornerMat c (Matrix.diagonal d) = Matrix.diagonal (Fin.cons c d : Fin (m + 1) → R) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj]

theorem diag_map_map {K : Type*} [Field K] {n : ℕ} (c : Fin n → 𝓞 F) (ρ : F →+* K) :
    ((QuadForm.diag c).map (algebraMap (𝓞 F) F)).map ρ = QuadForm.diag fun i => ρ (c i : F) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- **$\langle1,-a,-b,ab\rangle^\rho = \langle1\rangle\perp\langle-a,-b,ab\rangle^\rho$** for every embedding $\rho$. -/
theorem qSq_map_eq_splitForm {K : Type*} [Field K] (a b : 𝓞 F) (ρ : F →+* K) :
    ((qSq a b).map (algebraMap (𝓞 F) F)).map ρ =
      splitForm 1 (((QuatZeta.pureFormO a b).map (algebraMap (𝓞 F) F)).map ρ) := by
  rw [qSq, QuatZeta.pureFormO, diag_map_map, diag_map_map]
  ext i j
  rw [splitForm_coeff]
  change Matrix.diagonal _ i j = cornerMat 1 (Matrix.diagonal _) i j
  rw [cornerMat_diagonal']
  congr 2
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · rw [Fin.cons_succ]
    fin_cases k <;> simp

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

section Real

variable (w : {w : InfinitePlace F // w.IsReal})


local notation "Q4" => QRe (qSq a b) w
local notation "Q3" => QRe (QuatZeta.pureFormO a b) w

/-- **$\langle1,-a,-b,ab\rangle^{\sigma_w} = \langle1\rangle\perp\langle-a,-b,ab\rangle^{\sigma_w}$.** -/
theorem qRe_qSq_eq : Q4 = splitForm 1 Q3 := qSq_map_eq_splitForm a b (embedding_of_isReal w.2)

theorem eval_qRe_qSq (v : Fin 4 → ℝ) : (Q4).eval v = nrd (vecQ v : HRe a b w) := by
  rw [eval_QRe_qSq, nrd_vecQ]
  simp only [map_neg, map_mul]
  ring

/-- The point of $S_1$ given by a quaternion of reduced norm $1$. -/
def sphPtR (x : HRe a b w) (hx : nrd x = 1) : SphereLeray.Sph Q4 1 :=
  ⟨qVec x, by rw [SphereLeray.sph, Set.mem_ofPred_eq, eval_qRe_qSq, vecQ_qVec, hx]⟩

theorem nrd_of_sph (x : SphereLeray.Sph Q4 1) : nrd (vecQ (x : Fin 4 → ℝ) : HRe a b w) = 1 := by
  rw [← eval_qRe_qSq]; exact x.2

/-- The pair $(x, 1)$, $\operatorname{nrd}x = 1$. -/
def pairOne (x : SphereLeray.Sph Q4 1) : sqPair (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) :=
  ⟨(unitOfNrdOne _ (nrd_of_sph w x), 1), by rw [mem_sqPair]; exact (nrd_of_sph w x).trans nrd_one.symm⟩

/-- **The left multiplication section** $x\mapsto L_x\in SO(Q)(\mathbb R)$. -/
def lmulSecR (x : SphereLeray.Sph Q4 1) : ArchSO Q4 :=
  ⟨sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero (embedding_of_isReal w.2)).2 (coe_ne_zero' ha0)) (pairOne w x),
    sqSO_mem_soReal ha0 w (pairOne w x)⟩

theorem mat_lmulSecR (x : SphereLeray.Sph Q4 1) :
    ArchSOInst.mat _ (lmulSecR ha0 w x) = sqMat (vecQ (x : Fin 4 → ℝ) : HRe a b w) 1 := by
  change ((sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2))
    ((map_ne_zero (embedding_of_isReal w.2)).2 (coe_ne_zero' ha0)) (pairOne w x) : GL (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) = _
  rw [sqSO_val]
  show sqMat (vecQ (x : Fin 4 → ℝ)) (((1 : (HRe a b w)ˣ)⁻¹ : (HRe a b w)ˣ) : HRe a b w) = _
  rw [inv_one, Units.val_one]

theorem lmulSecR_spec (x : SphereLeray.Sph Q4 1) :
    ArchSOInst.mat _ (lmulSecR ha0 w x) *ᵥ (e₀ : Fin 4 → ℝ) = (x : Fin 4 → ℝ) := by
  rw [mat_lmulSecR, sqMat_mulVec, vecQ_e₀, mul_one, mul_one, qVec_vecQ]

theorem continuous_lmulSecR : Continuous (lmulSecR (b := b) ha0 w) := by
  have hv : Continuous fun x : SphereLeray.Sph Q4 1 => (x : Fin 4 → ℝ) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ x : SphereLeray.Sph Q4 1, ((ArchSO.incl _ (lmulSecR ha0 w x) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) =
        sqMat (vecQ (x : Fin 4 → ℝ) : HRe a b w) 1 := mat_lmulSecR ha0 w
    refine (continuous_congr e).2 ?_
    exact continuous_sqMat_comp _ _ ((continuous_apply 0).comp hv) ((continuous_apply 1).comp hv)
      ((continuous_apply 2).comp hv) ((continuous_apply 3).comp hv) continuous_const continuous_const
      continuous_const continuous_const
  · have e : ∀ x : SphereLeray.Sph Q4 1,
        (((ArchSO.incl _ (lmulSecR ha0 w x) : GL (Fin 4) ℝ))⁻¹ : GL (Fin 4) ℝ).val =
        sqMat (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)) 1 := fun x => by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_left_inv ?_
      change sqMat (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)) 1 * ArchSOInst.mat _ (lmulSecR ha0 w x) = 1
      rw [mat_lmulSecR, sqMat_mul, mul_one, star_mul_eq_nrd, nrd_of_sph w x]
      exact sqMat_one_one
    refine (continuous_congr e).2 ?_
    have h0 : Continuous fun x : SphereLeray.Sph Q4 1 => (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)).re := by
      simp only [QuaternionAlgebra.re_star, zero_mul, add_zero]; exact (continuous_apply 0).comp hv
    have h1 : Continuous fun x : SphereLeray.Sph Q4 1 => (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)).imI := by
      simp only [QuaternionAlgebra.imI_star]; exact ((continuous_apply 1).comp hv).neg
    have h2 : Continuous fun x : SphereLeray.Sph Q4 1 => (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)).imJ := by
      simp only [QuaternionAlgebra.imJ_star]; exact ((continuous_apply 2).comp hv).neg
    have h3 : Continuous fun x : SphereLeray.Sph Q4 1 => (star (vecQ (x : Fin 4 → ℝ) : HRe a b w)).imK := by
      simp only [QuaternionAlgebra.imK_star]; exact ((continuous_apply 3).comp hv).neg
    exact continuous_sqMat_comp _ _ h0 h1 h2 h3 continuous_const continuous_const continuous_const continuous_const

/-- The conjugation $c_\beta\in SO(Q')(\mathbb R)$ of a local unit. -/
def conjRloc (β : (HRe a b w)ˣ) : ArchSO Q3 :=
  ⟨conjGL β, by
    rw [mem_soReal_iff]
    exact conjGL_hessian_map _ (QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b)) (hQF a b) β⟩

theorem conjR_eq_conjRloc (α : (QuatInf (a : F) (b : F))ˣ) :
    conjR a b w α = conjRloc w (Units.map (projR (a : F) (b : F) w).toMonoidHom α) := rfl

/-- The embedding $h\mapsto\mathrm{diag}(1,h)$, $SO(Q')(\mathbb R)\to SO(Q)(\mathbb R)$. -/
def iotaR' (h : ArchSO Q3) : ArchSO Q4 :=
  ⟨blockGL (ArchSO.incl Q3 h), by
    rw [qRe_qSq_eq w]; exact OrbitalReal.blockGL_mem_soReal 1 _ (ArchSOInst.incl_mem Q3 h)⟩

theorem mat_iotaR' (h : ArchSO Q3) : ArchSOInst.mat _ (iotaR' w h) = cornerMat 1 (ArchSOInst.mat Q3 h) := by
  change ((blockGL (ArchSO.incl Q3 h) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = _
  rw [blockGL_val]; rfl

/-- **The orbit box** $U(A,W) = \{L_x\,\mathrm{diag}(1,h) : x\in A,\ h\in W\}\subseteq SO(Q)(\mathbb R)$. -/
def boxR (A : Set (SphereLeray.Sph Q4 1)) (W : Set (ArchSO Q3)) : Set (ArchSO Q4) :=
  (fun p : SphereLeray.Sph Q4 1 × ArchSO Q3 => lmulSecR ha0 w p.1 * iotaR' w p.2) '' (A ×ˢ W)

/-- **$\mu_Q(U(A,W)) = |2|^{-3}\,\sigma(A)\,\mu_{Q'}(W)$** at a real place. -/
theorem lerayMeasure_boxR (hQ : gramDetR Q4 ≠ 0) (hQ' : gramDetR Q3 ≠ 0) {A : Set (SphereLeray.Sph Q4 1)}
    (hA : MeasurableSet A) {W : Set (ArchSO Q3)} (hW : MeasurableSet W) :
    lerayMeasure Q4 hQ (boxR ha0 w A W) =
      ENNReal.ofReal (1 / 8) * (SphereLeray.sig Q4 1 A * lerayMeasure Q3 hQ' W) := by
  rw [boxR, lerayMeasure_image_sec one_ne_zero hQ' Q4 (qRe_qSq_eq w) hQ (lmulSecR ha0 w)
    (continuous_lmulSecR ha0 w).measurable (lmulSecR_spec ha0 w) (iotaR' w) (mat_iotaR' w) hA hW]
  norm_num

theorem lmulSecR_mul_iotaR'_injective :
    Function.Injective fun p : SphereLeray.Sph Q4 1 × ArchSO Q3 => lmulSecR ha0 w p.1 * iotaR' w p.2 := by
  rintro ⟨x, h⟩ ⟨x', h'⟩ hxh
  have e : ∀ (y : SphereLeray.Sph Q4 1) (k : ArchSO Q3),
      ArchSOInst.mat _ (lmulSecR ha0 w y * iotaR' w k) *ᵥ (e₀ : Fin 4 → ℝ) = (y : Fin 4 → ℝ) := fun y k => by
    rw [show ArchSOInst.mat _ (lmulSecR ha0 w y * iotaR' w k) =
      ArchSOInst.mat _ (lmulSecR ha0 w y) * ArchSOInst.mat _ (iotaR' w k) from rfl, ← mulVec_mulVec, mat_iotaR',
      cornerMat_one_mulVec_e₀, lmulSecR_spec]
  have hxh' : lmulSecR ha0 w x * iotaR' w h = lmulSecR ha0 w x' * iotaR' w h' := hxh
  have hx : x = x' := Subtype.ext (by rw [← e x h, ← e x' h', hxh'])
  subst hx
  have hk : iotaR' w h = iotaR' w h' := mul_left_cancel hxh'
  have := congrArg (ArchSOInst.mat _) hk
  rw [mat_iotaR', mat_iotaR'] at this
  rw [Prod.mk.injEq]
  exact ⟨rfl, Subtype.ext (Units.ext (cornerMat_one_injective this))⟩

end Real

section Complex

variable (w : {w : InfinitePlace F // w.IsComplex})


local notation "Q4" => QCx (qSq a b) w
local notation "Q3" => QCx (QuatZeta.pureFormO a b) w

theorem qCx_qSq_eq : Q4 = splitForm 1 Q3 := qSq_map_eq_splitForm a b w.1.embedding

open scoped Classical in
theorem eval_qCx_qSq (v : Fin 4 → ℂ) : (Q4).eval v = nrd (vecQ v : HCx a b w) := by
  rw [nrd_vecQ]
  simp [QCx, QuadForm.eval, QuadForm.evalIn, QuadForm.map, qSq, QuadForm.diag, Matrix.diagonal,
    Fin.sum_univ_four]
  ring

theorem nrd_of_sphC (x : SphereLerayC.SphC Q4 1) : nrd (vecQ (x : Fin 4 → ℂ) : HCx a b w) = 1 := by
  rw [← eval_qCx_qSq]; exact x.2

def pairOneC (x : SphereLerayC.SphC Q4 1) : sqPair (w.1.embedding (a : F)) (w.1.embedding (b : F)) :=
  ⟨(unitOfNrdOne _ (nrd_of_sphC w x), 1), by rw [mem_sqPair]; exact (nrd_of_sphC w x).trans nrd_one.symm⟩

/-- **The left multiplication section** at a complex place. -/
def lmulSecC (x : SphereLerayC.SphC Q4 1) : ArchSOC Q4 :=
  ⟨sqSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero w.1.embedding).2 (coe_ne_zero' ha0)) (pairOneC w x),
    sqSO_mem_soC ha0 w (pairOneC w x)⟩

theorem mat_lmulSecC (x : SphereLerayC.SphC Q4 1) :
    ArchSOC.mat _ (lmulSecC ha0 w x) = sqMat (vecQ (x : Fin 4 → ℂ) : HCx a b w) 1 := by
  change ((sqSO (two_ne_zero_of_ringHom w.1.embedding)
    ((map_ne_zero w.1.embedding).2 (coe_ne_zero' ha0)) (pairOneC w x) : GL (Fin 4) ℂ) :
      Matrix (Fin 4) (Fin 4) ℂ) = _
  rw [sqSO_val]
  show sqMat (vecQ (x : Fin 4 → ℂ)) (((1 : (HCx a b w)ˣ)⁻¹ : (HCx a b w)ˣ) : HCx a b w) = _
  rw [inv_one, Units.val_one]

theorem lmulSecC_spec (x : SphereLerayC.SphC Q4 1) :
    ArchSOC.mat _ (lmulSecC ha0 w x) *ᵥ (e₀ : Fin 4 → ℂ) = (x : Fin 4 → ℂ) := by
  rw [mat_lmulSecC, sqMat_mulVec, vecQ_e₀, mul_one, mul_one, qVec_vecQ]

theorem continuous_lmulSecC : Continuous (lmulSecC (b := b) ha0 w) := by
  have hv : Continuous fun x : SphereLerayC.SphC Q4 1 => (x : Fin 4 → ℂ) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ x : SphereLerayC.SphC Q4 1, ((ArchSOC.incl _ (lmulSecC ha0 w x) : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) =
        sqMat (vecQ (x : Fin 4 → ℂ) : HCx a b w) 1 := mat_lmulSecC ha0 w
    refine (continuous_congr e).2 ?_
    exact continuous_sqMat_comp _ _ ((continuous_apply 0).comp hv) ((continuous_apply 1).comp hv)
      ((continuous_apply 2).comp hv) ((continuous_apply 3).comp hv) continuous_const continuous_const
      continuous_const continuous_const
  · have e : ∀ x : SphereLerayC.SphC Q4 1,
        (((ArchSOC.incl _ (lmulSecC ha0 w x) : GL (Fin 4) ℂ))⁻¹ : GL (Fin 4) ℂ).val =
        sqMat (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)) 1 := fun x => by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_left_inv ?_
      change sqMat (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)) 1 * ArchSOC.mat _ (lmulSecC ha0 w x) = 1
      rw [mat_lmulSecC, sqMat_mul, mul_one, star_mul_eq_nrd, nrd_of_sphC w x]
      exact sqMat_one_one
    refine (continuous_congr e).2 ?_
    have h0 : Continuous fun x : SphereLerayC.SphC Q4 1 => (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)).re := by
      simp only [QuaternionAlgebra.re_star, zero_mul, add_zero]; exact (continuous_apply 0).comp hv
    have h1 : Continuous fun x : SphereLerayC.SphC Q4 1 => (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)).imI := by
      simp only [QuaternionAlgebra.imI_star]; exact ((continuous_apply 1).comp hv).neg
    have h2 : Continuous fun x : SphereLerayC.SphC Q4 1 => (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)).imJ := by
      simp only [QuaternionAlgebra.imJ_star]; exact ((continuous_apply 2).comp hv).neg
    have h3 : Continuous fun x : SphereLerayC.SphC Q4 1 => (star (vecQ (x : Fin 4 → ℂ) : HCx a b w)).imK := by
      simp only [QuaternionAlgebra.imK_star]; exact ((continuous_apply 3).comp hv).neg
    exact continuous_sqMat_comp _ _ h0 h1 h2 h3 continuous_const continuous_const continuous_const continuous_const

/-- The conjugation $c_\beta\in SO(Q')(\mathbb C)$ of a local unit. -/
def conjCloc (β : (HCx a b w)ˣ) : ArchSOC Q3 :=
  ⟨conjGL β, by
    rw [mem_soC_iff, gramC]
    obtain ⟨h1, h2⟩ := conjGL_hessian_map _ (QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b))
      (hQF a b) β
    refine ⟨?_, h2⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, h1]⟩

theorem conjC_eq_conjCloc (α : (QuatInf (a : F) (b : F))ˣ) :
    conjC a b w α = conjCloc w (Units.map (projC (a : F) (b : F) w).toMonoidHom α) := rfl

/-- The embedding $h\mapsto\mathrm{diag}(1,h)$, $SO(Q')(\mathbb C)\to SO(Q)(\mathbb C)$. -/
def iotaC' (h : ArchSOC Q3) : ArchSOC Q4 :=
  ⟨blockGL (ArchSOC.incl Q3 h), by
    rw [qCx_qSq_eq w]; exact OrbitalComplex.blockGL_mem_soC 1 _ (ArchSOC.incl_mem Q3 h)⟩

theorem mat_iotaC' (h : ArchSOC Q3) : ArchSOC.mat _ (iotaC' w h) = cornerMat 1 (ArchSOC.mat Q3 h) := by
  change ((blockGL (ArchSOC.incl Q3 h) : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = _
  rw [blockGL_val]; rfl

/-- **The orbit box** at a complex place. -/
def boxC (A : Set (SphereLerayC.SphC Q4 1)) (W : Set (ArchSOC Q3)) : Set (ArchSOC Q4) :=
  (fun p : SphereLerayC.SphC Q4 1 × ArchSOC Q3 => lmulSecC ha0 w p.1 * iotaC' w p.2) '' (A ×ˢ W)

/-- **$\mu_Q(U(A,W)) = |2|_{\mathbb C}^{-3}\,\sigma(A)\,\mu_{Q'}(W)$** at a complex place ($|2|_{\mathbb C} = 4$). -/
theorem lerayMeasureC_boxC (hQ : gramDetC Q4 ≠ 0) (hQ' : gramDetC Q3 ≠ 0) {A : Set (SphereLerayC.SphC Q4 1)}
    (hA : MeasurableSet A) {W : Set (ArchSOC Q3)} (hW : MeasurableSet W) :
    lerayMeasureC Q4 hQ (boxC ha0 w A W) =
      ENNReal.ofReal (1 / 64) * (SphereLerayC.sigC Q4 1 A * lerayMeasureC Q3 hQ' W) := by
  rw [boxC, lerayMeasureC_image_sec one_ne_zero hQ' Q4 (qCx_qSq_eq w) hQ (lmulSecC ha0 w)
    (continuous_lmulSecC ha0 w).measurable (lmulSecC_spec ha0 w) (iotaC' w) (mat_iotaC' w) hA hW]
  congr 1
  rw [mul_one, show ‖(2 : ℂ)‖₊ = 2 by ext; simp, ← ENNReal.ofReal_coe_nnreal]
  norm_num

theorem lmulSecC_mul_iotaC'_injective :
    Function.Injective fun p : SphereLerayC.SphC Q4 1 × ArchSOC Q3 => lmulSecC ha0 w p.1 * iotaC' w p.2 := by
  rintro ⟨x, h⟩ ⟨x', h'⟩ hxh
  have e : ∀ (y : SphereLerayC.SphC Q4 1) (k : ArchSOC Q3),
      ArchSOC.mat _ (lmulSecC ha0 w y * iotaC' w k) *ᵥ (e₀ : Fin 4 → ℂ) = (y : Fin 4 → ℂ) := fun y k => by
    rw [show ArchSOC.mat _ (lmulSecC ha0 w y * iotaC' w k) =
      ArchSOC.mat _ (lmulSecC ha0 w y) * ArchSOC.mat _ (iotaC' w k) from rfl, ← mulVec_mulVec, mat_iotaC',
      cornerMat_one_mulVec_e₀, lmulSecC_spec]
  have hxh' : lmulSecC ha0 w x * iotaC' w h = lmulSecC ha0 w x' * iotaC' w h' := hxh
  have hx : x = x' := Subtype.ext (by rw [← e x h, ← e x' h', hxh'])
  subst hx
  have hk : iotaC' w h = iotaC' w h' := mul_left_cancel hxh'
  have := congrArg (ArchSOC.mat _) hk
  rw [mat_iotaC', mat_iotaC'] at this
  rw [Prod.mk.injEq]
  exact ⟨rfl, Subtype.ext (Units.ext (cornerMat_one_injective this))⟩

end Complex

end QuadFormsKB.Tamagawa.Measure.Weil

end
