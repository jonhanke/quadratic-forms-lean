import QuadFormsKB.Tamagawa.Measure.Weil.NSArchRhoR
import QuadFormsKB.Tamagawa.Measure.OrbitImage
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArchSO

/-!
# The local ratio at a real place with $E_w = \mathbb R\times\mathbb R$

**Layer:** one real place $w$ of $F$ with $d_w = t^2 > 0$, so $E_w = \mathbb R\times\mathbb R$ and $D\otimes E_w = D_w\times D_w$,
$D_w = \mathbb H[\mathbb R,A,B]$; the two places of $K$ over $w$ give $\delta\mapsto t$ and $\delta\mapsto-t$.
$Q_0 = \langle1\rangle\perp\langle-Ad,-Bd,ABd\rangle$ (`splitForm 1 (pureFormD A B d)`), $T = \mathrm{diag}(1,t,t,t)$ (`tGL`), so
$N(Tv) = Q_0(v)$ for the norm form $N$.

* **`phiSplit`**: $L_w = S_1\times S_1\to SO(Q_0)(\mathbb R)$, $(x,y)\mapsto T^{-1}\,(v\mapsto xv\bar y)\,T$ (the map $\varphi_w$ of the
  non-square model in the coordinates of the two places over $w$); kernel $\pm(1,1)$ (`isLocInj_phiSplit`).
* **`leray_phiSplit_image`**: for every measurable $Y\subseteq S_1\times S_1$ on which `phiSplit` is injective,
  $$\mu_{Q_0}(\varphi(Y)) = \frac{1}{32\,|A|^3|B|^3\,|t|^3\,|d|^6}\,(\sigma\otimes\sigma)(Y).$$
  *Proof:* Haar uniqueness on $S_1\times S_1$ along $\varphi$; on $Y = \{(eh,h) : e\in C,\ h\in C\}$ ($C$ a Cayley ball) the image is
  the orbit box of the section $y\mapsto T^{-1}L_{Ty}T$ (orbital identity, factor $|2|^{-3}$), $\sigma_{Q_0}(T^{-1}C) = |t|^{-3}\sigma(C)$,
  $\mu_{\langle-Ad,-Bd,ABd\rangle} = |d|^{-6}\mu_{\langle-A,-B,AB\rangle}$ (`map_lerayMeasure_conjSO'`), and the
  $\mathrm{SL}_1\to SO_3$ ratio `leray_conjS_image`; $(\sigma\otimes\sigma)(Y) = \sigma(C)^2$ by the shear and right invariance.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.Leray
  QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.OrbitalReal

/-! ### Linear transport of the sphere measures -/

section Transport

variable {n : ℕ} {Q Q' : QuadForm ℝ n} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
  (hQ : ∀ v, Q.eval (M *ᵥ v) = Q'.eval v)

include hQ in
/-- $v\mapsto Mv$, $S_1(Q')\to S_1(Q)$. -/
def sphLin (x : Sph Q' 1) : Sph Q 1 := ⟨M *ᵥ (x : Fin n → ℝ), by show Q.eval _ = 1; rw [hQ]; exact x.2⟩

theorem continuous_sphLin : Continuous (sphLin M hQ) :=
  ((Matrix.toLin' M).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

include hM in
/-- **Transport of the cone measure**: $\nu_{Q'}(M^{-1}A) = |\det M|^{-1}\nu_Q(A)$. -/
theorem nu_preimage_sphLin {A : Set (Sph Q 1)} (hA : MeasurableSet A) :
    nu Q' 1 (sphLin M hQ ⁻¹' A) = ENNReal.ofReal |M.det|⁻¹ * nu Q 1 A := by
  have hm := (continuous_sphLin M hQ).measurable
  rw [nu_apply one_ne_zero (hm hA), nu_apply one_ne_zero hA]
  have himg : Matrix.toLin' M '' (pol Q' 1 '' (Iic 0 ×ˢ (sphLin M hQ ⁻¹' A))) = pol Q 1 '' (Iic 0 ×ˢ A) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      exact ⟨(t, sphLin M hQ x), ⟨ht, hx⟩, by simp [pol, sphLin, Matrix.mulVec_smul]⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
      have hy : Q'.eval (M⁻¹ *ᵥ (x : Fin n → ℝ)) = 1 := by
        rw [← hQ, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]; exact x.2
      refine ⟨pol Q' 1 (t, ⟨M⁻¹ *ᵥ (x : Fin n → ℝ), hy⟩), ⟨(t, ⟨_, hy⟩), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show sphLin M hQ ⟨_, hy⟩ ∈ A
        have : sphLin M hQ ⟨_, hy⟩ = x := Subtype.ext (by
          simp [sphLin, Matrix.mulVec_mulVec, hMi])
        rw [this]; exact hx
      · simp [pol, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMi]
  have hvol := addHaar_image_linearMap (volume : Measure (Fin n → ℝ)) (Matrix.toLin' M)
    (pol Q' 1 '' (Iic 0 ×ˢ (sphLin M hQ ⁻¹' A)))
  rw [himg, LinearMap.det_toLin'] at hvol
  rw [hvol, ← mul_assoc, ← mul_assoc, mul_comm (ENNReal.ofReal |M.det|⁻¹), mul_assoc, mul_assoc, ← mul_assoc _ _
    (volume _), ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)), inv_mul_cancel₀ (abs_ne_zero.2 hM),
    ENNReal.ofReal_one, one_mul]

include hM in
theorem sig_preimage_sphLin {A : Set (Sph Q 1)} (hA : MeasurableSet A) :
    sig Q' 1 (sphLin M hQ ⁻¹' A) = ENNReal.ofReal |M.det|⁻¹ * sig Q 1 A := by
  rw [sig, sig, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, nu_preimage_sphLin M hM hQ hA]
  ring

end Transport

/-! ### The forms -/

/-- $\langle-Ad,-Bd,ABd\rangle$. -/
def pureFormD (A B d : ℝ) : QuadForm ℝ 3 := QuadForm.diag ![-A * d, -B * d, A * B * d]

/-- $Q_0 = \langle1\rangle\perp\langle-Ad,-Bd,ABd\rangle$. -/
abbrev nsFormR (A B d : ℝ) : QuadForm ℝ 4 := splitForm 1 (pureFormD A B d)

variable {A B d t : ℝ}

theorem nsFormR_eq_diag : nsFormR A B d = QuadForm.diag ![1, -A * d, -B * d, A * B * d] := by
  apply QuadForm.ext
  rw [splitForm_coeff, pureFormD, QuadForm.diag, QuadForm.diag]
  show cornerMat 1 (Matrix.diagonal _) = Matrix.diagonal _
  rw [cornerMat_diagonal']
  congr 1

theorem eval_nsFormR (v : Fin 4 → ℝ) :
    (nsFormR A B d).eval v = v 0 ^ 2 - A * d * v 1 ^ 2 - B * d * v 2 ^ 2 + A * B * d * v 3 ^ 2 := by
  rw [nsFormR_eq_diag]
  simp only [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal_apply]
  simp
  ring

/-- $T = \mathrm{diag}(1,t,t,t)$. -/
def tMat (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, t, t, t]

theorem tMat_mulVec (v : Fin 4 → ℝ) : tMat t *ᵥ v = ![v 0, t * v 1, t * v 2, t * v 3] := by
  funext i; fin_cases i <;> simp [tMat, Matrix.mulVec_diagonal]

theorem det_tMat : (tMat t).det = t ^ 3 := by
  simp [tMat, Matrix.det_diagonal, Fin.prod_univ_four]; ring

theorem eval_normForm_tMat (ht : t ^ 2 = d) (v : Fin 4 → ℝ) :
    (normForm A B).eval (tMat t *ᵥ v) = (nsFormR A B d).eval v := by
  rw [eval_normForm, tMat_mulVec, eval_nsFormR, ← ht]
  simp [nrd, vecQ]; ring

theorem hessian_normForm : (normForm A B).hessian = Matrix.diagonal ![2, -(2 * A), -(2 * B), 2 * (A * B)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem hessian_nsFormR : (nsFormR A B d).hessian =
    Matrix.diagonal ![2, -(2 * (A * d)), -(2 * (B * d)), 2 * (A * B * d)] := by
  rw [nsFormR_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem hessian_nsFormR_eq (ht : t ^ 2 = d) :
    (nsFormR A B d).hessian = (1 : ℝ) • ((tMat t)ᵀ * (normForm A B).hessian * tMat t) := by
  rw [one_smul, hessian_nsFormR, hessian_normForm, tMat, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← ht]
  congr 1; funext i; fin_cases i <;> simp <;> ring

/-- $T$ as an invertible matrix. -/
def tGL (ht0 : t ≠ 0) : GL (Fin 4) ℝ :=
  ⟨tMat t, Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹], by
    rw [tMat, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0], by
    rw [tMat, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]⟩

theorem tGL_val (ht0 : t ≠ 0) : ((tGL ht0 : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = tMat t := rfl

theorem tGL_inv_val (ht0 : t ≠ 0) :
    (((tGL ht0)⁻¹ : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹] := rfl

theorem hessian_pureFormD : (pureFormD A B d).hessian = d • ((1 : GL (Fin 3) ℝ)ᵀ * (pureForm A B).hessian *
    ((1 : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureFormD, pureForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

/-! ### Quaternion algebra -/

section QuatAlg

variable {A B : ℝ}

/-- A norm-one quaternion conjugating every pure quaternion trivially is $\pm1$. -/
theorem eq_scalar_of_conj_trivial (hA : A ≠ 0) {a : ℍ[ℝ,A,B]} (ha : nrd a = 1)
    (h : ∀ y : Fin 3 → ℝ, a * Quat.pure y * star a = Quat.pure y) : ∃ r : ℝ, r ^ 2 = 1 ∧ a = (r : ℍ[ℝ,A,B]) := by
  have hc : conjSO (unitOfNrdOne a ha) = 1 := by
    apply Subtype.ext
    show conjGL (unitOfNrdOne a ha) = 1
    apply Units.ext
    change LinearMap.toMatrix' (conjLin (unitOfNrdOne a ha)) = 1
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    show imv (a * Quat.pure y * star a) = y
    rw [h, imv_pure]
  have hm : unitOfNrdOne a ha ∈ centerUnits A B := by
    rw [← ker_conjSO (two_ne_zero (α := ℝ)) hA, MonoidHom.mem_ker]; exact hc
  obtain ⟨r, hr⟩ := mem_centerUnits.1 hm
  refine ⟨r, ?_, hr⟩
  have := congrArg nrd hr
  rw [nrd_coe] at this
  exact this.symm.trans ha

theorem sq_eq_one_cases {r : ℝ} (h : r ^ 2 = 1) : r = 1 ∨ r = -1 := by
  have : (r - 1) * (r + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

theorem sqMat_eq_lmat_mul_rmat (x z : ℍ[ℝ,A,B]) : sqMat x z = lmat x * rmat z := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [sqMat_mulVec, ← Matrix.mulVec_mulVec, rmat_mulVec, lmat_mulVec, vecQ_qVec, mul_assoc]

theorem hessian_normForm_eq : (normForm A B).hessian = (2 : ℝ) • nDiag A B := by
  rw [hessian_normForm, nDiag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring

theorem sqMat_isometry (x z : ℍ[ℝ,A,B]) :
    (sqMat x z)ᵀ * (normForm A B).hessian * sqMat x z = (nrd x * nrd z) • (normForm A B).hessian := by
  rw [sqMat_eq_lmat_mul_rmat, hessian_normForm_eq, Matrix.transpose_mul]
  calc (rmat z)ᵀ * (lmat x)ᵀ * ((2 : ℝ) • nDiag A B) * (lmat x * rmat z)
      = (2 : ℝ) • ((rmat z)ᵀ * ((lmat x)ᵀ * nDiag A B * lmat x) * rmat z) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [lmat_isometry, Matrix.mul_smul, Matrix.smul_mul, rmat_isometry, smul_smul, smul_smul, smul_smul]
        congr 1; ring

theorem det_sqMat (x z : ℍ[ℝ,A,B]) : (sqMat x z).det = nrd x ^ 2 * nrd z ^ 2 := by
  rw [sqMat_eq_lmat_mul_rmat, Matrix.det_mul, det_lmat, det_rmat]

end QuatAlg

/-! ### Right invariance -/

section RightInv

variable {A B : ℝ}

theorem rmat_gram (x : Sph (normForm A B) 1) :
    (rmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]))ᵀ * gramMatrixR (normForm A B) *
        rmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = gramMatrixR (normForm A B) := by
  rw [gramMatrixR_normForm, rmat_isometry, nrd_sph, one_smul]

instance : (sig (normForm A B) 1).IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  have e : (fun y : Sph (normForm A B) 1 => y * x) = sphMap (normForm A B) 1
      (rmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B])) (rmat_gram x) := funext fun y => by
    apply Subtype.ext
    show qVec (vecQ (y : Fin 4 → ℝ) * vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = rmat _ *ᵥ (y : Fin 4 → ℝ)
    rw [rmat_mulVec]
  rw [e, map_sphMap_sig one_ne_zero]
  rw [det_rmat, nrd_sph, one_pow, abs_one]

/-- **The shear**: the product measure of the set of pairs $(x,y)$ with $y\in C$ and $xy^{-1}\in E$ is
$\sigma(E)\,\sigma(C)$. -/
theorem sig_prod_shear {C E : Set (Sph (normForm A B) 1)} (hC : MeasurableSet C) (hE : MeasurableSet E) :
    ((sig (normForm A B) 1).prod (sig (normForm A B) 1)) {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
      sig (normForm A B) 1 E * sig (normForm A B) 1 C := by
  haveI := sigmaFinite_sig (Q := normForm A B) one_ne_zero
  have hm : MeasurableSet {p : Sph (normForm A B) 1 × Sph (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} :=
    (measurable_snd hC).inter (hE.preimage (continuous_fst.mul (continuous_snd.inv)).measurable)
  rw [Measure.prod_apply_symm hm]
  have hsec : ∀ y : Sph (normForm A B) 1, sig (normForm A B) 1
      ((fun x => (x, y)) ⁻¹' {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E}) = C.indicator (fun _ => sig (normForm A B) 1 E) y := by
    intro y
    by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' {p : Sph (normForm A B) 1 × Sph (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
          (fun x => x * y⁻¹) ⁻¹' E := by ext x; simp [hy]
      rw [this, measure_preimage_mul_right]
    · rw [Set.indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' {p : Sph (normForm A B) 1 × Sph (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
          ∅ := by ext x; simp [hy]
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hC]

end RightInv

/-! ### The square map and $\varphi_w$ -/

section Phi

variable {A B : ℝ}

local notation "S1" => Sph (normForm A B) 1

/-- $(x, y)\mapsto(v\mapsto xv\bar y)$ as an invertible matrix. -/
def sqGL (p : S1 × S1) : GL (Fin 4) ℝ :=
  ⟨sqMat (vecQ (p.1 : Fin 4 → ℝ)) (star (vecQ (p.2 : Fin 4 → ℝ))),
    sqMat (star (vecQ (p.1 : Fin 4 → ℝ))) (vecQ (p.2 : Fin 4 → ℝ)), by
      rw [sqMat_mul, mul_star_eq_nrd, mul_star_eq_nrd, nrd_sph, nrd_sph]; simpa using sqMat_one_one, by
      rw [sqMat_mul, star_mul_eq_nrd, star_mul_eq_nrd, nrd_sph, nrd_sph]; simpa using sqMat_one_one⟩

theorem sqGL_mem (p : S1 × S1) : sqGL p ∈ soReal (normForm A B) := by
  rw [mem_soReal_iff]
  refine ⟨?_, ?_⟩
  · show (sqMat _ _)ᵀ * _ * sqMat _ _ = _
    rw [sqMat_isometry, nrd_star, nrd_sph, nrd_sph, one_mul, one_smul]
  · show (sqMat _ _).det = 1
    rw [det_sqMat, nrd_star, nrd_sph, nrd_sph]; norm_num

/-- **The square map** $S_1\times S_1\to SO(N)(\mathbb R)$. -/
def sqS : S1 × S1 →* ArchSO (normForm A B) where
  toFun p := ⟨sqGL p, sqGL_mem p⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show sqMat (vecQ (qVec (1 : ℍ[ℝ,A,B]))) (star (vecQ (qVec (1 : ℍ[ℝ,A,B])))) = 1
    rw [vecQ_qVec, star_one]; exact sqMat_one_one
  map_mul' p q := by
    apply Subtype.ext; apply Units.ext
    show sqMat (vecQ (qVec (vecQ (p.1 : Fin 4 → ℝ) * vecQ (q.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B])))
        (star (vecQ (qVec (vecQ (p.2 : Fin 4 → ℝ) * vecQ (q.2 : Fin 4 → ℝ) : ℍ[ℝ,A,B])))) =
      sqMat (vecQ (p.1 : Fin 4 → ℝ)) (star (vecQ (p.2 : Fin 4 → ℝ))) *
        sqMat (vecQ (q.1 : Fin 4 → ℝ)) (star (vecQ (q.2 : Fin 4 → ℝ)))
    rw [vecQ_qVec, vecQ_qVec, sqMat_mul, star_mul]

theorem mat_sqS (p : S1 × S1) :
    ArchSOInst.mat _ (sqS p) = sqMat (vecQ (p.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (p.2 : Fin 4 → ℝ))) := by
  change ((sqGL p : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = _
  rfl

theorem continuous_lmat_vec : Continuous fun v : Fin 4 → ℝ => lmat (vecQ v : ℍ[ℝ,A,B]) := by
  have e : (fun v : Fin 4 → ℝ => lmat (vecQ v : ℍ[ℝ,A,B])) = fun v => !![v 0, A * v 1, B * v 2, -(A * B) * v 3;
      v 1, v 0, B * v 3, -B * v 2; v 2, -A * v 3, v 0, A * v 1; v 3, -v 2, v 1, v 0] := by
    funext v; rw [lmat_eq]; rfl
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_rmat_star_vec : Continuous fun v : Fin 4 → ℝ => rmat (star (vecQ v : ℍ[ℝ,A,B])) := by
  have e : (fun v : Fin 4 → ℝ => rmat (star (vecQ v : ℍ[ℝ,A,B]))) = fun v => !![v 0, A * -v 1, B * -v 2,
      -(A * B) * -v 3; -v 1, v 0, -B * -v 3, B * -v 2; -v 2, A * -v 3, v 0, -A * -v 1; -v 3, -v 2, - -v 1, v 0] := by
    funext v; rw [rmat_eq]; simp [vecQ]
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_sqMat_vec : Continuous fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
    sqMat (vecQ q.1 : ℍ[ℝ,A,B]) (star (vecQ q.2)) := by
  simp only [sqMat_eq_lmat_mul_rmat]
  exact (continuous_lmat_vec.comp continuous_fst).matrix_mul (continuous_rmat_star_vec.comp continuous_snd)

theorem continuous_sqS : Continuous (sqS (A := A) (B := B)) := by
  have hv : Continuous fun p : S1 × S1 => ((p.1 : Fin 4 → ℝ), (p.2 : Fin 4 → ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ p : S1 × S1, ((ArchSO.incl _ (sqS p) : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) =
        sqMat (vecQ (p.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (p.2 : Fin 4 → ℝ))) := mat_sqS
    refine (continuous_congr e).2 ?_
    have h1 : Continuous fun p : S1 × S1 => lmat (vecQ (p.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) :=
      continuous_lmat_vec.comp (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : S1 × S1 => rmat (star (vecQ (p.2 : Fin 4 → ℝ) : ℍ[ℝ,A,B])) :=
      continuous_rmat_star_vec.comp (continuous_subtype_val.comp continuous_snd)
    simp only [sqMat_eq_lmat_mul_rmat]
    exact h1.matrix_mul h2
  · have e : ∀ p : S1 × S1, (((ArchSO.incl _ (sqS p) : GL (Fin 4) ℝ))⁻¹ : GL (Fin 4) ℝ).val =
        sqMat (vecQ ((p⁻¹).1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ ((p⁻¹).2 : Fin 4 → ℝ))) := fun p => by
      rw [← map_inv (ArchSO.incl _), ← map_inv sqS]; exact mat_sqS _
    refine (continuous_congr e).2 ?_
    have h1 : Continuous fun p : S1 × S1 => lmat (vecQ ((p⁻¹).1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) :=
      continuous_lmat_vec.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_inv))
    have h2 : Continuous fun p : S1 × S1 => rmat (star (vecQ ((p⁻¹).2 : Fin 4 → ℝ) : ℍ[ℝ,A,B])) :=
      continuous_rmat_star_vec.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_inv))
    simp only [sqMat_eq_lmat_mul_rmat]
    exact h1.matrix_mul h2

/-- **Kernel of the square map**: $\mathrm{sq}(x,y) = \mathrm{sq}(x',y')$ implies $(x',y') = r(x,y)$ with $r = \pm1$. -/
theorem eq_smul_of_sqS_eq (hA : A ≠ 0) {p p' : S1 × S1} (h : sqS p = sqS p') :
    ∃ r : ℝ, r ^ 2 = 1 ∧ (p'.1 : Fin 4 → ℝ) = r • (p.1 : Fin 4 → ℝ) ∧ (p'.2 : Fin 4 → ℝ) = r • (p.2 : Fin 4 → ℝ) := by
  set X := (vecQ (p.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B])
  set Y := (vecQ (p.2 : Fin 4 → ℝ) : ℍ[ℝ,A,B])
  set X' := (vecQ (p'.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B])
  set Y' := (vecQ (p'.2 : Fin 4 → ℝ) : ℍ[ℝ,A,B])
  have hX : nrd X = 1 := nrd_sph _
  have hY : nrd Y = 1 := nrd_sph _
  have hX' : nrd X' = 1 := nrd_sph _
  have hY' : nrd Y' = 1 := nrd_sph _
  have hM : sqMat X (star Y) = sqMat X' (star Y') := by
    have := congrArg (ArchSOInst.mat _) h
    rwa [mat_sqS, mat_sqS] at this
  have hv : ∀ v : ℍ[ℝ,A,B], X * v * star Y = X' * v * star Y' := fun v => by
    have := congrArg (· *ᵥ qVec v) hM
    simp only [sqMat_mulVec, vecQ_qVec] at this
    have := congrArg (vecQ (A := A) (B := B)) this
    rwa [vecQ_qVec, vecQ_qVec] at this
  have he := hv 1
  simp only [mul_one] at he
  -- `star Y = star X * e`
  have hsY : star Y = star X * (X * star Y) := by
    rw [← mul_assoc, star_mul_eq_nrd, hX]; simp
  have hsY' : star Y' = star X' * (X' * star Y') := by
    rw [← mul_assoc, star_mul_eq_nrd, hX']; simp
  have hcj : ∀ v : ℍ[ℝ,A,B], X * v * star X = X' * v * star X' := fun v => by
    have h1 := hv v
    rw [hsY, hsY', he] at h1
    have hu : IsUnit (X' * star Y') := by
      rw [isUnit_iff_nrd_ne_zero, nrd_mul, nrd_star, hX', hY']; norm_num
    have h1' : (X * v * star X) * (X' * star Y') = (X' * v * star X') * (X' * star Y') := by
      simpa only [mul_assoc] using h1
    exact hu.mul_left_inj.1 h1'
  set a := star X' * X
  have ha : nrd a = 1 := by rw [nrd_mul, nrd_star, hX', hX, one_mul]
  have hsa : star a = star X * X' := by rw [star_mul, star_star]
  obtain ⟨r, hr2, hr⟩ := eq_scalar_of_conj_trivial hA ha fun y => by
    rw [hsa]
    calc star X' * X * Quat.pure y * (star X * X') = star X' * (X * Quat.pure y * star X) * X' := by
          simp only [mul_assoc]
      _ = star X' * (X' * Quat.pure y * star X') * X' := by rw [hcj]
      _ = (star X' * X') * Quat.pure y * (star X' * X') := by simp only [mul_assoc]
      _ = _ := by rw [star_mul_eq_nrd, hX']; simp
  have hXr : X = (r : ℍ[ℝ,A,B]) * X' := by
    have : X' * a = X := by rw [← mul_assoc, mul_star_eq_nrd, hX']; simp
    rw [← this, hr, ← QuaternionAlgebra.coe_commutes]
  have hr1 : r * r = 1 := by rw [← sq]; exact hr2
  have hX'r : X' = (r : ℍ[ℝ,A,B]) * X := by
    rw [hXr, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hr1, QuaternionAlgebra.coe_one, one_mul]
  have hY'r : Y' = (r : ℍ[ℝ,A,B]) * Y := by
    have h2 : X * star Y = X * ((r : ℍ[ℝ,A,B]) * star Y') := by
      rw [he, hX'r, QuaternionAlgebra.coe_commutes, mul_assoc]
    have hu : IsUnit X := by rw [isUnit_iff_nrd_ne_zero, hX]; norm_num
    have h3 : star Y = (r : ℍ[ℝ,A,B]) * star Y' := hu.mul_right_inj.1 h2
    have h4 : star Y' = (r : ℍ[ℝ,A,B]) * star Y := by
      rw [h3, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hr1, QuaternionAlgebra.coe_one, one_mul]
    have := congrArg star h4
    rw [star_star, star_mul, star_star, QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_commutes] at this
    exact this
  refine ⟨r, hr2, ?_, ?_⟩
  · have := congrArg qVec hX'r
    rw [qVec_vecQ, QuaternionAlgebra.coe_mul_eq_smul] at this
    rw [this]; funext i; fin_cases i <;> simp [X, Y, qVec, vecQ]
  · have := congrArg qVec hY'r
    rw [qVec_vecQ, QuaternionAlgebra.coe_mul_eq_smul] at this
    rw [this]; funext i; fin_cases i <;> simp [X, Y, qVec, vecQ]

end Phi

/-! ### The map $\varphi_w$ and its ratio -/

section Split

variable {A B d t : ℝ} (ht0 : t ≠ 0) (ht : t ^ 2 = d)

local notation "S1" => Sph (normForm A B) 1
local notation "Q0" => nsFormR A B d

/-- $T^{-1} = \mathrm{diag}(1,t^{-1},t^{-1},t^{-1})$. -/
def tInv (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹]

theorem tMat_eq_corner (t : ℝ) : tMat t = cornerMat 1 (Matrix.diagonal ![t, t, t]) := by
  rw [tMat, cornerMat_diagonal']; congr 1

theorem tInv_eq_corner (t : ℝ) : tInv t = cornerMat 1 (Matrix.diagonal ![t⁻¹, t⁻¹, t⁻¹]) := by
  rw [tInv, cornerMat_diagonal']; congr 1

include ht0 in
theorem tMat_mul_tInv : tMat t * tInv t = 1 := by
  rw [tMat, tInv, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]

include ht0 in
theorem tInv_mul_tMat : tInv t * tMat t = 1 := by
  rw [tMat, tInv, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]

include ht0 in
theorem tInv_corner_tMat (C : Matrix (Fin 3) (Fin 3) ℝ) : tInv t * cornerMat 1 C * tMat t = cornerMat 1 C := by
  rw [tInv_eq_corner, tMat_eq_corner, cornerMat_mul, cornerMat_mul, one_mul, one_mul]
  congr 1
  rw [show Matrix.diagonal ![t⁻¹, t⁻¹, t⁻¹] = t⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal],
    show Matrix.diagonal ![t, t, t] = t • (1 : Matrix (Fin 3) (Fin 3) ℝ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  first | rw [inv_mul_cancel₀ ht0, one_smul] | rw [mul_inv_cancel₀ ht0, one_smul]

/-- $g\mapsto T^{-1}gT$, $SO(N)\cong SO(Q_0)$. -/
def cT : ArchSO (normForm A B) ≃ₜ* ArchSO Q0 :=
  conjSO (tGL ht0) 1 (by rw [tGL_val]; exact hessian_nsFormR_eq ht) one_ne_zero

/-- **The map $\varphi_w$ at a real place with $E_w = \mathbb R\times\mathbb R$**: $(x,y)\mapsto T^{-1}(v\mapsto xv\bar y)T$. -/
def phiSplit : S1 × S1 →* ArchSO Q0 := (cT ht0 ht).toMonoidHom.comp sqS

theorem mat_phiSplit (p : S1 × S1) :
    ArchSOInst.mat _ (phiSplit ht0 ht p) =
      tInv t * sqMat (vecQ (p.1 : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (p.2 : Fin 4 → ℝ))) * tMat t := by
  change ArchSOInst.mat _ (cT ht0 ht (sqS p)) = _
  rw [cT, conjSO_mat, mat_sqS]; rfl

theorem continuous_phiSplit : Continuous (phiSplit (A := A) (B := B) ht0 ht) :=
  (cT ht0 ht).continuous.comp continuous_sqS

theorem eq_smul_of_phiSplit_eq (hA : A ≠ 0) {p p' : S1 × S1} (h : phiSplit ht0 ht p = phiSplit ht0 ht p') :
    ∃ r : ℝ, r ^ 2 = 1 ∧ (p'.1 : Fin 4 → ℝ) = r • (p.1 : Fin 4 → ℝ) ∧ (p'.2 : Fin 4 → ℝ) = r • (p.2 : Fin 4 → ℝ) :=
  eq_smul_of_sqS_eq hA ((cT ht0 ht).injective h)

theorem isLocInj_phiSplit (hA : A ≠ 0) : IsLocInj (phiSplit (A := A) (B := B) ht0 ht) := by
  intro x
  set c := 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖)
  have hc : 0 < c := by positivity
  refine ⟨{y | dist y.1 x.1 < Real.sqrt c}, isOpen_lt ((continuous_fst).dist continuous_const) continuous_const,
    by simpa using Real.sqrt_pos.2 hc, fun y hy y' hy' hyy => ?_⟩
  obtain ⟨r, hr2, h1, h2⟩ := eq_smul_of_phiSplit_eq ht0 ht hA hyy
  rcases sq_eq_one_cases hr2 with rfl | rfl
  · exact (Prod.ext (Subtype.ext (by simpa using h1)) (Subtype.ext (by simpa using h2))).symm
  · exfalso
    have hd : dist ((y'.1 : S1) : Fin 4 → ℝ) ((y.1 : S1) : Fin 4 → ℝ) < 2 * Real.sqrt c := by
      calc dist ((y'.1 : S1) : Fin 4 → ℝ) ((y.1 : S1) : Fin 4 → ℝ)
          ≤ dist ((y'.1 : S1) : Fin 4 → ℝ) (x.1 : Fin 4 → ℝ) + dist ((y.1 : S1) : Fin 4 → ℝ) (x.1 : Fin 4 → ℝ) :=
            dist_triangle_right _ _ _
        _ < Real.sqrt c + Real.sqrt c := add_lt_add hy' hy
        _ = 2 * Real.sqrt c := by ring
    rw [h1, dist_eq_norm, show (-1 : ℝ) • ((y.1 : S1) : Fin 4 → ℝ) - (y.1 : Fin 4 → ℝ) =
      (-2 : ℝ) • ((y.1 : S1) : Fin 4 → ℝ) by module, norm_smul] at hd
    have hn := norm_ge_of_sph y.1
    have : ‖((y.1 : S1) : Fin 4 → ℝ)‖ < Real.sqrt c := by norm_num at hd; linarith
    have := (Real.lt_sqrt (norm_nonneg _)).1 this
    linarith

/-! #### The orbit decomposition -/

/-- $y\mapsto Ty$, $S_1(Q_0)\to S_1(N)$. -/
def sphT : Sph Q0 1 → S1 := sphLin (tMat t) (eval_normForm_tMat ht)

include ht0 ht in
theorem eval_tInv (x : S1) : (nsFormR A B d).eval (tInv t *ᵥ (x : Fin 4 → ℝ)) = 1 := by
  rw [← eval_normForm_tMat ht, Matrix.mulVec_mulVec, tMat_mul_tInv ht0, Matrix.one_mulVec]; exact x.2

/-- $x\mapsto T^{-1}x$. -/
def invT (x : S1) : Sph Q0 1 := ⟨tInv t *ᵥ (x : Fin 4 → ℝ), eval_tInv ht0 ht x⟩

include ht0 in
theorem sphT_invT (x : S1) : sphT ht (invT ht0 ht x) = x := by
  apply Subtype.ext
  show tMat t *ᵥ (tInv t *ᵥ (x : Fin 4 → ℝ)) = _
  rw [Matrix.mulVec_mulVec, tMat_mul_tInv ht0, Matrix.one_mulVec]

include ht0 in
theorem invT_sphT (y : Sph Q0 1) : invT ht0 ht (sphT ht y) = y := by
  apply Subtype.ext
  show tInv t *ᵥ (tMat t *ᵥ (y : Fin 4 → ℝ)) = _
  rw [Matrix.mulVec_mulVec, tInv_mul_tMat ht0, Matrix.one_mulVec]

/-- **The section** $y\mapsto T^{-1}L_{Ty}T$ of the orbit map of $SO(Q_0)$. -/
def secSplit (y : Sph Q0 1) : ArchSO Q0 := phiSplit ht0 ht (sphT ht y, 1)

theorem secSplit_spec (y : Sph Q0 1) :
    ArchSOInst.mat _ (secSplit ht0 ht y) *ᵥ (e₀ : Fin 4 → ℝ) = (y : Fin 4 → ℝ) := by
  rw [secSplit, mat_phiSplit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have he : (e₀ : Fin 4 → ℝ) = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
  have h1 : tMat t *ᵥ (e₀ : Fin 4 → ℝ) = e₀ := by
    rw [he, tMat_mulVec]; funext i; fin_cases i <;> simp
  have h2 : (star (vecQ ((1 : S1) : Fin 4 → ℝ)) : ℍ[ℝ,A,B]) = 1 := by
    rw [show ((1 : S1) : Fin 4 → ℝ) = qVec (1 : ℍ[ℝ,A,B]) from rfl, vecQ_qVec, star_one]
  rw [h1, sqMat_mulVec, h2, vecQ_e₀, mul_one, mul_one, qVec_vecQ]
  show tInv t *ᵥ (tMat t *ᵥ (y : Fin 4 → ℝ)) = _
  rw [Matrix.mulVec_mulVec, tInv_mul_tMat ht0, Matrix.one_mulVec]

theorem continuous_secSplit : Continuous (secSplit (A := A) (B := B) ht0 ht) :=
  (continuous_phiSplit ht0 ht).comp ((continuous_sphLin _ _).prodMk continuous_const)

/-- $SO(\langle-A,-B,AB\rangle)\cong SO(\langle-Ad,-Bd,ABd\rangle)$ (the same matrices). -/
def cS (hd0 : d ≠ 0) : ArchSO (pureForm A B) ≃ₜ* ArchSO (pureFormD A B d) :=
  conjSO (1 : GL (Fin 3) ℝ) d hessian_pureFormD hd0

theorem mat_cS (hd0 : d ≠ 0) (g : ArchSO (pureForm A B)) :
    ArchSOInst.mat _ (cS (A := A) (B := B) hd0 g) = ArchSOInst.mat _ g := by
  rw [cS, conjSO_mat]; simp

theorem mat_conjS_eq_conjGL (h : S1) :
    ArchSOInst.mat _ (conjS h) = ((conjGL (toUnit h) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := rfl

/-- **The decomposition** $\varphi(eh,h) = s(T^{-1}e)\,\mathrm{diag}(1,c_h)$. -/
theorem phiSplit_decomp (hd0 : d ≠ 0) (e h : S1) :
    phiSplit ht0 ht (e * h, h) = secSplit ht0 ht (invT ht0 ht e) * iota 1 (pureFormD A B d) (cS hd0 (conjS h)) := by
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (phiSplit ht0 ht (e * h, h)) =
    ArchSOInst.mat _ (secSplit ht0 ht (invT ht0 ht e)) * ArchSOInst.mat _ (iota 1 (pureFormD A B d) (cS hd0 (conjS h)))
  have h1 : (star (vecQ ((1 : S1) : Fin 4 → ℝ)) : ℍ[ℝ,A,B]) = 1 := by
    rw [show ((1 : S1) : Fin 4 → ℝ) = qVec (1 : ℍ[ℝ,A,B]) from rfl, vecQ_qVec, star_one]
  have h2 : (vecQ ((e * h : S1) : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = vecQ (e : Fin 4 → ℝ) * vecQ (h : Fin 4 → ℝ) := by
    rw [sph_mul_val, vecQ_qVec]
  have h3 : cornerMat 1 ((conjGL (toUnit h) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      sqMat (vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ))) := (sqMat_conj (toUnit h)).symm
  have L : ArchSOInst.mat _ (phiSplit ht0 ht (e * h, h)) = tInv t * sqMat (vecQ (e : Fin 4 → ℝ) *
      vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ))) * tMat t := by
    rw [mat_phiSplit]; simp only; rw [h2]
  have R1 : ArchSOInst.mat _ (secSplit ht0 ht (invT ht0 ht e)) =
      tInv t * sqMat (vecQ (e : Fin 4 → ℝ) : ℍ[ℝ,A,B]) 1 * tMat t := by
    rw [secSplit, mat_phiSplit]; simp only; rw [sphT_invT ht0, h1]
  have R2 : ArchSOInst.mat _ (iota 1 (pureFormD A B d) (cS hd0 (conjS h))) =
      tInv t * sqMat (vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ))) * tMat t := by
    rw [mat_iota, mat_cS, mat_conjS_eq_conjGL, h3, ← h3, tInv_corner_tMat ht0]
  rw [L, R1, R2]
  calc tInv t * sqMat (vecQ (e : Fin 4 → ℝ) * vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ))) * tMat t
      = tInv t * (sqMat (vecQ (e : Fin 4 → ℝ) : ℍ[ℝ,A,B]) 1 *
          sqMat (vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ)))) * tMat t := by
        rw [sqMat_mul, mul_one]
    _ = tInv t * sqMat (vecQ (e : Fin 4 → ℝ) : ℍ[ℝ,A,B]) 1 * (tMat t * tInv t) *
          sqMat (vecQ (h : Fin 4 → ℝ) : ℍ[ℝ,A,B]) (star (vecQ (h : Fin 4 → ℝ))) * tMat t := by
        rw [tMat_mul_tInv ht0, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-! #### The test set and the constant -/

/-- The test set $\{(x,y) : y\in C,\ xy^{-1}\in C\}$. -/
def shearSet (C : Set S1) : Set (S1 × S1) := {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ C}

theorem phiSplit_image_shearSet (hd0 : d ≠ 0) (C : Set S1) :
    phiSplit ht0 ht '' shearSet C =
      (fun q : Sph Q0 1 × ArchSO (pureFormD A B d) => secSplit ht0 ht q.1 * iota 1 (pureFormD A B d) q.2) ''
        ((sphT ht ⁻¹' C) ×ˢ (cS hd0 '' (conjS '' C))) := by
  ext g
  constructor
  · rintro ⟨p, ⟨h2, h1⟩, rfl⟩
    have hp : p = (p.1 * p.2⁻¹ * p.2, p.2) := by rw [inv_mul_cancel_right]
    refine ⟨(invT ht0 ht (p.1 * p.2⁻¹), cS hd0 (conjS p.2)), ⟨?_, ⟨conjS p.2, ⟨p.2, h2, rfl⟩, rfl⟩⟩, ?_⟩
    · show sphT ht (invT ht0 ht _) ∈ C
      rw [sphT_invT ht0]; exact h1
    · show _ = phiSplit ht0 ht p
      conv_rhs => rw [hp]
      rw [phiSplit_decomp ht0 ht hd0]
  · rintro ⟨⟨y, w⟩, ⟨hy, ⟨_, ⟨h, hh, rfl⟩, rfl⟩⟩, rfl⟩
    refine ⟨(sphT ht y * h, h), ⟨hh, by simpa using hy⟩, ?_⟩
    show phiSplit ht0 ht (sphT ht y * h, h) = _
    rw [phiSplit_decomp ht0 ht hd0, invT_sphT ht0]

theorem injOn_phiSplit_shearSet (hA : A ≠ 0) {δ : ℝ} :
    InjOn (phiSplit (A := A) (B := B) ht0 ht) (shearSet (cayBall A B δ)) := by
  intro p hp p' hp' h
  obtain ⟨r, hr2, h1, h2⟩ := eq_smul_of_phiSplit_eq ht0 ht hA h
  rcases sq_eq_one_cases hr2 with rfl | rfl
  · exact (Prod.ext (Subtype.ext (by simpa using h1)) (Subtype.ext (by simpa using h2))).symm
  · exfalso
    have a1 := hp.1.1; have a2 := hp'.1.1
    have := congrFun h2 0
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at this
    linarith

theorem measurableSet_shearSet {C : Set S1} (hC : MeasurableSet C) : MeasurableSet (shearSet C) :=
  (measurable_snd hC).inter (hC.preimage (continuous_fst.mul (continuous_snd.inv)).measurable)

theorem leray_cS_image (hd0 : d ≠ 0) (hQ3 : gramDetR (pureForm A B) ≠ 0) (hQ3d : gramDetR (pureFormD A B d) ≠ 0)
    (X : Set (ArchSO (pureForm A B))) (hX : MeasurableSet X) :
    lerayMeasure (pureFormD A B d) hQ3d (cS hd0 '' X) =
      ENNReal.ofReal (|d| ^ 6)⁻¹ * lerayMeasure (pureForm A B) hQ3 X := by
  have h := map_lerayMeasure_conjSO' (1 : GL (Fin 3) ℝ) d hessian_pureFormD hd0 hQ3 hQ3d
  have hm : MeasurableSet (cS (A := A) (B := B) hd0 '' X) :=
    (cS (A := A) (B := B) hd0).toHomeomorph.measurableEmbedding.measurableSet_image.2 hX
  have h2 := congrArg (fun μ => μ (cS (A := A) (B := B) hd0 '' X)) h
  change (lerayMeasure (pureForm A B) hQ3).map (cS (A := A) (B := B) hd0) (cS (A := A) (B := B) hd0 '' X) = _ at h2
  rw [Measure.map_apply (map_continuous (cS (A := A) (B := B) hd0)).measurable hm,
    (cS (A := A) (B := B) hd0).injective.preimage_image, Measure.smul_apply, smul_eq_mul] at h2
  have hd6 : (0 : ℝ) < |d| ^ 6 := pow_pos (abs_pos.2 hd0) 6
  have e : |d| ^ (3 * (3 + 1) / 2) * |((1 : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).det| ^ (3 + 1) = |d| ^ 6 := by
    simp
  rw [h2, show (cS (A := A) (B := B) hd0) = conjSO (1 : GL (Fin 3) ℝ) d hessian_pureFormD hd0 from rfl, e,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hd6.le), inv_mul_cancel₀ hd6.ne', ENNReal.ofReal_one, one_mul]

/-- **The local ratio at a real place with $E_w = \mathbb R\times\mathbb R$.** For every measurable $Y\subseteq S_1\times S_1$ on which
$\varphi_w$ is injective, $\mu_{Q_0}(\varphi_w(Y)) = (32|A|^3|B|^3|t|^3|d|^6)^{-1}(\sigma\otimes\sigma)(Y)$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio, real place, d > 0); §3.7, pp. 64-65 [unverified page]"]
theorem leray_phiSplit_image (hA : A ≠ 0) (hB : B ≠ 0) (hd0 : d ≠ 0) (hQ3 : gramDetR (pureForm A B) ≠ 0)
    (hQ3d : gramDetR (pureFormD A B d) ≠ 0) (hQ0 : gramDetR Q0 ≠ 0) {Y : Set (S1 × S1)} (hY : MeasurableSet Y)
    (hinj : InjOn (phiSplit ht0 ht) Y) :
    lerayMeasure Q0 hQ0 (phiSplit ht0 ht '' Y) =
      ENNReal.ofReal (1 / (32 * |A| ^ 3 * |B| ^ 3 * |t| ^ 3 * |d| ^ 6)) *
        ((sig (normForm A B) 1).prod (sig (normForm A B) 1)) Y := by
  have := isHaarMeasure_lerayMeasure hQ0
  obtain ⟨c, hc⟩ := exists_measure_image_eq_smul ((sig (normForm A B) 1).prod (sig (normForm A B) 1))
    (lerayMeasure Q0 hQ0) (phiSplit ht0 ht) (continuous_phiSplit ht0 ht) (isLocInj_phiSplit ht0 ht hA)
  -- a Cayley ball of positive measure
  obtain ⟨δ, hδ, hδr⟩ := ((eventually_nu_cayBall_pos (A := A) (B := B)).and
    (nhdsWithin_le_nhds (Iic_mem_nhds (radR_pos A B)))).exists
  set C := cayBall A B δ
  have hCm : MeasurableSet C := measurableSet_cayBall δ
  have hC0 : sig (normForm A B) 1 C ≠ 0 := by
    rw [sig, Measure.smul_apply, smul_eq_mul]
    refine mul_ne_zero (by simp) ?_
    intro h; rw [h] at hδ; simp at hδ
  have hCt : sig (normForm A B) 1 C ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono (cayBall_subset hδr))
    (IsCompact.measure_lt_top (isCompact_normLe 2)))
  -- the two evaluations on the shear set
  have h1 := hc (shearSet C) (measurableSet_shearSet hCm) (injOn_phiSplit_shearSet ht0 ht hA)
  rw [shearSet, sig_prod_shear hCm hCm] at h1
  have hW : MeasurableSet (conjS '' C) :=
    hCm.image_of_continuousOn_injOn continuous_conjS.continuousOn (injOn_conjS_cayBall hA δ)
  have hWm : MeasurableSet (cS (A := A) (B := B) hd0 '' (conjS '' C)) :=
    (cS (A := A) (B := B) hd0).toHomeomorph.measurableEmbedding.measurableSet_image.2 hW
  have h2 := lerayMeasure_image_sec one_ne_zero hQ3d Q0 rfl hQ0 (secSplit ht0 ht)
    (continuous_secSplit ht0 ht).measurable (secSplit_spec ht0 ht) (iota 1 (pureFormD A B d))
    (mat_iota 1 (pureFormD A B d))
    (hCm.preimage (continuous_sphLin (tMat t) (eval_normForm_tMat (A := A) (B := B) ht)).measurable) hWm
  have h2' : lerayMeasure Q0 hQ0 (phiSplit ht0 ht '' shearSet C) = ENNReal.ofReal ((|2 * 1| ^ 3)⁻¹) *
      (sig Q0 1 (sphLin (tMat t) (eval_normForm_tMat (A := A) (B := B) ht) ⁻¹' C) *
        lerayMeasure (pureFormD A B d) hQ3d (cS hd0 '' (conjS '' C))) := by
    rw [phiSplit_image_shearSet ht0 ht hd0]; exact h2
  clear h2
  have h2 := h2'
  rw [sig_preimage_sphLin (tMat t) (by rw [det_tMat]; exact pow_ne_zero 3 ht0)
    (eval_normForm_tMat ht) hCm, det_tMat, leray_cS_image hd0 hQ3 hQ3d _ hW,
    leray_conjS_image hA hB hQ3 hCm (injOn_conjS_cayBall hA δ)] at h2
  have hset : phiSplit ht0 ht '' shearSet C = phiSplit ht0 ht '' {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ C} := rfl
  rw [hset, h1] at h2
  -- solve for `c`
  have hk : (c : ℝ≥0∞) = ENNReal.ofReal (1 / (32 * |A| ^ 3 * |B| ^ 3 * |t| ^ 3 * |d| ^ 6)) := by
    have hCC : sig (normForm A B) 1 C * sig (normForm A B) 1 C ≠ 0 := mul_ne_zero hC0 hC0
    have hCCt : sig (normForm A B) 1 C * sig (normForm A B) 1 C ≠ ⊤ := ENNReal.mul_ne_top hCt hCt
    refine (ENNReal.mul_left_inj hCC hCCt).1 ?_
    rw [h2]
    have hA3 : 0 < |A| ^ 3 := pow_pos (abs_pos.2 hA) 3
    have hB3 : 0 < |B| ^ 3 := pow_pos (abs_pos.2 hB) 3
    have ht3 : 0 < |t ^ 3| := abs_pos.2 (pow_ne_zero 3 ht0)
    have hd6 : 0 < |d| ^ 6 := pow_pos (abs_pos.2 hd0) 6
    rw [show |(2 : ℝ) * 1| ^ 3 = 8 by norm_num]
    calc ENNReal.ofReal 8⁻¹ * (ENNReal.ofReal |t ^ 3|⁻¹ * sig (normForm A B) 1 C *
          (ENNReal.ofReal (|d| ^ 6)⁻¹ * (ENNReal.ofReal (1 / (4 * |A| ^ 3 * |B| ^ 3)) * sig (normForm A B) 1 C)))
        = ENNReal.ofReal (8⁻¹ * |t ^ 3|⁻¹ * (|d| ^ 6)⁻¹ * (1 / (4 * |A| ^ 3 * |B| ^ 3))) *
            (sig (normForm A B) 1 C * sig (normForm A B) 1 C) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
      _ = _ := by
          congr 2
          rw [abs_pow]
          field_simp
          ring
  rw [hc Y hY hinj, hk]

end Split

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
