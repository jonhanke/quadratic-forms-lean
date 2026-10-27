import QuadFormsKB.Tamagawa.Measure.Weil.NSArchRhoC
import QuadFormsKB.Tamagawa.Measure.OrbitImage
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArchSO

/-!
# The local ratio at a complex place with $E_w = \mathbb C\times\mathbb C$

**Layer:** one complex place $w$ of $F$, so $E_w = \mathbb C\times\mathbb C$ and $D\otimes E_w = D_w\times D_w$, $D_w = \mathbb H[\mathbb C,A,B]$;
$d = t^2$ ($t\in\mathbb C^\times$), $Q_0 = \langle1\rangle\perp\langle-Ad,-Bd,ABd\rangle$ (`nsFormC`), $T = \mathrm{diag}(1,t,t,t)$ (`tGLC`), so
$N(Tv) = Q_0(v)$ for the norm form $N$. Complex analogue of `NSArchSplitR.lean`.

* **`phiSplitC`**: $S_1\times S_1\to SO(Q_0)(\mathbb C)$, $(x,y)\mapsto T^{-1}\,(v\mapsto xv\bar y)\,T$; kernel $\pm(1,1)$ (`isLocInj_phiSplitC`).
* **`lerayC_phiSplitC_image`**: for every measurable $Y\subseteq S_1\times S_1$ on which `phiSplitC` is injective,
  $$\mu_{Q_0}(\varphi(Y)) = \frac{1}{1024\,|A|^6|B|^6|t|^6|d|^{12}}\,(\sigma_{\mathbb C}\otimes\sigma_{\mathbb C})(Y)$$
  (here $|\cdot|$ is the ordinary absolute value on $\mathbb C$; the complex absolute value $|\cdot|_{\mathbb C} = |\cdot|^2$ gives the exponents doubled).
  *Proof:* Haar uniqueness on $S_1\times S_1$ along $\varphi$; on $Y = \{(eh,h) : e\in C,\ h\in C\}$ ($C$ a Cayley ball) the image is
  the orbit box of the section $y\mapsto T^{-1}L_{Ty}T$ (orbital identity, factor $|2|_{\mathbb C}^{-3} = 1/64$), $\sigma_{Q_0}(T^{-1}C) = |\det T|^{-2}\sigma(C) = |t|^{-6}\sigma(C)$,
  $\mu_{\langle-Ad,-Bd,ABd\rangle} = |d|^{-12}\mu_{\langle-A,-B,AB\rangle}$ (`map_lerayMeasureC_conjSOC'`), and the
  $\mathrm{SL}_1\to SO_3$ ratio `leray_conjSC_image` ($1/(16|A|^6|B|^6)$).
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLerayC QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.Leray QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-! ### Linear transport of the sphere measures -/

section Transport

variable {n : ℕ} {Q Q' : QuadForm ℂ n} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0)
  (hQ : ∀ v, Q.eval (M *ᵥ v) = Q'.eval v)

include hQ in
/-- $v\mapsto Mv$, $S_1(Q')\to S_1(Q)$. -/
def sphLinC (x : SphC Q' 1) : SphC Q 1 := ⟨M *ᵥ (x : Fin n → ℂ), by show Q.eval _ = 1; rw [hQ]; exact x.2⟩

theorem continuous_sphLinC : Continuous (sphLinC M hQ) :=
  ((Matrix.toLin' M).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

include hM in
/-- **Transport of the cone measure**: $\nu_{Q'}(M^{-1}A) = \|\det M\|^{-2}\nu_Q(A)$. -/
theorem nuC_preimage_sphLinC {A : Set (SphC Q 1)} (hA : MeasurableSet A) :
    nuC Q' 1 (sphLinC M hQ ⁻¹' A) = ENNReal.ofReal (‖M.det‖ ^ 2)⁻¹ * nuC Q 1 A := by
  have hm := (continuous_sphLinC M hQ).measurable
  rw [nuC_apply_volume one_ne_zero (hm hA), nuC_apply_volume one_ne_zero hA]
  have himg : Matrix.toLin' M '' (polC Q' 1 '' (R0 ×ˢ (sphLinC M hQ ⁻¹' A))) = polC Q 1 '' (R0 ×ˢ A) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      exact ⟨(t, sphLinC M hQ x), ⟨ht, hx⟩, by simp [polC, sphLinC, Matrix.mulVec_smul]⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
      have hy : Q'.eval (M⁻¹ *ᵥ (x : Fin n → ℂ)) = 1 := by
        rw [← hQ, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]; exact x.2
      refine ⟨polC Q' 1 (t, ⟨M⁻¹ *ᵥ (x : Fin n → ℂ), hy⟩), ⟨(t, ⟨_, hy⟩), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show sphLinC M hQ ⟨_, hy⟩ ∈ A
        have : sphLinC M hQ ⟨_, hy⟩ = x := Subtype.ext (by
          simp [sphLinC, Matrix.mulVec_mulVec, hMi])
        rw [this]; exact hx
      · simp [polC, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMi]
  have hvol : ∀ E : Set (Fin n → ℂ), volume (Matrix.toLin' M '' E) = ENNReal.ofReal (‖M.det‖ ^ 2) * volume E := by
    intro E
    rw [show ⇑(Matrix.toLin' M) = ⇑((Matrix.toLin' M).restrictScalars ℝ) from rfl, addHaar_image_linearMap,
      LerayComplex.det_restrictScalars_complex, LinearMap.det_toLin', Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg _)]
  have hk0 : (‖M.det‖ ^ 2) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hM)
  have hk : ENNReal.ofReal (‖M.det‖ ^ 2)⁻¹ * ENNReal.ofReal (‖M.det‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg _)), inv_mul_cancel₀ hk0, ENNReal.ofReal_one]
  rw [← himg, hvol]
  set V := volume (polC Q' 1 '' (R0 ×ˢ (sphLinC M hQ ⁻¹' A)))
  calc (lamU n R0)⁻¹ * V
      = (ENNReal.ofReal (‖M.det‖ ^ 2)⁻¹ * ENNReal.ofReal (‖M.det‖ ^ 2)) * ((lamU n R0)⁻¹ * V) := by
        rw [hk, one_mul]
    _ = _ := by ring

include hM in
theorem sigC_preimage_sphLinC {A : Set (SphC Q 1)} (hA : MeasurableSet A) :
    sigC Q' 1 (sphLinC M hQ ⁻¹' A) = ENNReal.ofReal (‖M.det‖ ^ 2)⁻¹ * sigC Q 1 A := by
  rw [sigC, sigC, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    nuC_preimage_sphLinC M hM hQ hA]
  ring

end Transport

/-! ### The forms -/

/-- $\langle-Ad,-Bd,ABd\rangle$. -/
def pureFormDC (A B d : ℂ) : QuadForm ℂ 3 := QuadForm.diag ![-A * d, -B * d, A * B * d]

/-- $Q_0 = \langle1\rangle\perp\langle-Ad,-Bd,ABd\rangle$. -/
abbrev nsFormC (A B d : ℂ) : QuadForm ℂ 4 := splitForm 1 (pureFormDC A B d)

variable {A B d t : ℂ}

theorem nsFormC_eq_diag : nsFormC A B d = QuadForm.diag ![1, -A * d, -B * d, A * B * d] := by
  apply QuadForm.ext
  rw [splitForm_coeff, pureFormDC, QuadForm.diag, QuadForm.diag]
  show cornerMat 1 (Matrix.diagonal _) = Matrix.diagonal _
  rw [cornerMat_diagonal']
  congr 1

theorem eval_nsFormC (v : Fin 4 → ℂ) :
    (nsFormC A B d).eval v = v 0 ^ 2 - A * d * v 1 ^ 2 - B * d * v 2 ^ 2 + A * B * d * v 3 ^ 2 := by
  rw [nsFormC_eq_diag]
  simp only [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal_apply]
  simp
  ring

/-- $T = \mathrm{diag}(1,t,t,t)$. -/
def tMatC (t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, t, t, t]

theorem tMatC_mulVec (v : Fin 4 → ℂ) : tMatC t *ᵥ v = ![v 0, t * v 1, t * v 2, t * v 3] := by
  funext i; fin_cases i <;> simp [tMatC, Matrix.mulVec_diagonal]

theorem det_tMatC : (tMatC t).det = t ^ 3 := by
  simp [tMatC, Matrix.det_diagonal, Fin.prod_univ_four]; ring

theorem eval_normForm_tMatC (ht : t ^ 2 = d) (v : Fin 4 → ℂ) :
    (normForm A B).eval (tMatC t *ᵥ v) = (nsFormC A B d).eval v := by
  rw [eval_normForm, tMatC_mulVec, eval_nsFormC, ← ht]
  simp [nrd, vecQ]; ring

theorem hessian_normFormC : (normForm A B).hessian = Matrix.diagonal ![2, -(2 * A), -(2 * B), 2 * (A * B)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem hessian_nsFormC : (nsFormC A B d).hessian =
    Matrix.diagonal ![2, -(2 * (A * d)), -(2 * (B * d)), 2 * (A * B * d)] := by
  rw [nsFormC_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem hessian_nsFormC_eq (ht : t ^ 2 = d) :
    (nsFormC A B d).hessian = (1 : ℂ) • ((tMatC t)ᵀ * (normForm A B).hessian * tMatC t) := by
  rw [one_smul, hessian_nsFormC, hessian_normFormC, tMatC, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← ht]
  congr 1; funext i; fin_cases i <;> simp <;> ring

/-- $T$ as an invertible matrix. -/
def tGLC (ht0 : t ≠ 0) : GL (Fin 4) ℂ :=
  ⟨tMatC t, Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹], by
    rw [tMatC, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0], by
    rw [tMatC, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]⟩

theorem tGLC_val (ht0 : t ≠ 0) : ((tGLC ht0 : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = tMatC t := rfl

theorem hessian_pureFormDC : (pureFormDC A B d).hessian = d • ((1 : GL (Fin 3) ℂ)ᵀ * (pureForm A B).hessian *
    ((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureFormDC, pureForm, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

/-! ### Quaternion algebra -/

section QuatAlg

variable {A B : ℂ}

/-- A norm-one quaternion conjugating every pure quaternion trivially is $\pm1$. -/
theorem eq_scalar_of_conj_trivialC (hA : A ≠ 0) {a : ℍ[ℂ,A,B]} (ha : nrd a = 1)
    (h : ∀ y : Fin 3 → ℂ, a * Quat.pure y * star a = Quat.pure y) : ∃ r : ℂ, r ^ 2 = 1 ∧ a = (r : ℍ[ℂ,A,B]) := by
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
    rw [← ker_conjSO (two_ne_zero (α := ℂ)) hA, MonoidHom.mem_ker]; exact hc
  obtain ⟨r, hr⟩ := mem_centerUnits.1 hm
  refine ⟨r, ?_, hr⟩
  have := congrArg nrd hr
  rw [nrd_coe] at this
  exact this.symm.trans ha

theorem sq_eq_one_casesC {r : ℂ} (h : r ^ 2 = 1) : r = 1 ∨ r = -1 := by
  have : (r - 1) * (r + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem sqMat_eq_lmat_mul_rmatC (x z : ℍ[ℂ,A,B]) : sqMat x z = lmat x * rmat z := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [sqMat_mulVec, ← Matrix.mulVec_mulVec, rmat_mulVec, lmat_mulVec, vecQ_qVec, mul_assoc]

theorem sqMat_isometryC (x z : ℍ[ℂ,A,B]) :
    (sqMat x z)ᵀ * nDiag A B * sqMat x z = (nrd x * nrd z) • nDiag A B := by
  rw [sqMat_eq_lmat_mul_rmatC, Matrix.transpose_mul]
  calc (rmat z)ᵀ * (lmat x)ᵀ * nDiag A B * (lmat x * rmat z)
      = (rmat z)ᵀ * ((lmat x)ᵀ * nDiag A B * lmat x) * rmat z := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [lmat_isometry, Matrix.mul_smul, Matrix.smul_mul, rmat_isometry, smul_smul]

theorem det_sqMatC (x z : ℍ[ℂ,A,B]) : (sqMat x z).det = nrd x ^ 2 * nrd z ^ 2 := by
  rw [sqMat_eq_lmat_mul_rmatC, Matrix.det_mul, det_lmat, det_rmat]

end QuatAlg

/-! ### Right invariance -/

section RightInv

variable {A B : ℂ}

theorem rmat_gramC (x : SphC (normForm A B) 1) :
    (rmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]))ᵀ * gramC (normForm A B) *
        rmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = gramC (normForm A B) := by
  rw [gramC_normForm, rmat_isometry, nrd_sphC, one_smul]

instance : (sigC (normForm A B) 1).IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  have e : (fun y : SphC (normForm A B) 1 => y * x) = sphMapC (normForm A B) 1
      (rmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B])) (rmat_gramC x) := funext fun y => by
    apply Subtype.ext
    show qVec (vecQ (y : Fin 4 → ℂ) * vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = rmat _ *ᵥ (y : Fin 4 → ℂ)
    rw [rmat_mulVec]
  rw [e, map_sphMapC_sigC one_ne_zero]
  rw [det_rmat, nrd_sphC, one_pow, norm_one]

/-- **The shear**: the product measure of the set of pairs $(x,y)$ with $y\in C$ and $xy^{-1}\in E$ is
$\sigma(E)\,\sigma(C)$. -/
theorem sigC_prod_shear {C E : Set (SphC (normForm A B) 1)} (hC : MeasurableSet C) (hE : MeasurableSet E) :
    ((sigC (normForm A B) 1).prod (sigC (normForm A B) 1)) {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
      sigC (normForm A B) 1 E * sigC (normForm A B) 1 C := by
  haveI := sigmaFinite_sigC (Q := normForm A B) (c := 1) one_ne_zero (by norm_num)
  have hm : MeasurableSet {p : SphC (normForm A B) 1 × SphC (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} :=
    (measurable_snd hC).inter (hE.preimage (continuous_fst.mul (continuous_snd.inv)).measurable)
  rw [Measure.prod_apply_symm hm]
  have hsec : ∀ y : SphC (normForm A B) 1, sigC (normForm A B) 1
      ((fun x => (x, y)) ⁻¹' {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E}) = C.indicator (fun _ => sigC (normForm A B) 1 E) y := by
    intro y
    by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' {p : SphC (normForm A B) 1 × SphC (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
          (fun x => x * y⁻¹) ⁻¹' E := by ext x; simp [hy]
      rw [this, measure_preimage_mul_right]
    · rw [Set.indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' {p : SphC (normForm A B) 1 × SphC (normForm A B) 1 | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ E} =
          ∅ := by ext x; simp [hy]
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hC]

end RightInv

/-! ### The square map and $\varphi_w$ -/

section Phi

variable {A B : ℂ}

local notation "S1" => SphC (normForm A B) 1

/-- $(x, y)\mapsto(v\mapsto xv\bar y)$ as an invertible matrix. -/
def sqGLC (p : S1 × S1) : GL (Fin 4) ℂ :=
  ⟨sqMat (vecQ (p.1 : Fin 4 → ℂ)) (star (vecQ (p.2 : Fin 4 → ℂ))),
    sqMat (star (vecQ (p.1 : Fin 4 → ℂ))) (vecQ (p.2 : Fin 4 → ℂ)), by
      rw [sqMat_mul, mul_star_eq_nrd, mul_star_eq_nrd, nrd_sphC, nrd_sphC]; simpa using sqMat_one_one, by
      rw [sqMat_mul, star_mul_eq_nrd, star_mul_eq_nrd, nrd_sphC, nrd_sphC]; simpa using sqMat_one_one⟩

theorem sqGLC_mem (p : S1 × S1) : sqGLC p ∈ soC (normForm A B) := by
  rw [mem_soC_iff]
  refine ⟨?_, ?_⟩
  · show (sqMat _ _)ᵀ * _ * sqMat _ _ = _
    rw [gramC_normForm, sqMat_isometryC, nrd_star, nrd_sphC, nrd_sphC, one_mul, one_smul]
  · show (sqMat _ _).det = 1
    rw [det_sqMatC, nrd_star, nrd_sphC, nrd_sphC]; norm_num

/-- **The square map** $S_1\times S_1\to SO(N)(\mathbb C)$. -/
def sqSC : S1 × S1 →* ArchSOC (normForm A B) where
  toFun p := ArchSOC.mk _ (sqGLC p) (sqGLC_mem p)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show sqMat (vecQ (qVec (1 : ℍ[ℂ,A,B]))) (star (vecQ (qVec (1 : ℍ[ℂ,A,B])))) = 1
    rw [vecQ_qVec, star_one]; exact sqMat_one_one
  map_mul' p q := by
    apply Subtype.ext; apply Units.ext
    show sqMat (vecQ (qVec (vecQ (p.1 : Fin 4 → ℂ) * vecQ (q.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B])))
        (star (vecQ (qVec (vecQ (p.2 : Fin 4 → ℂ) * vecQ (q.2 : Fin 4 → ℂ) : ℍ[ℂ,A,B])))) =
      sqMat (vecQ (p.1 : Fin 4 → ℂ)) (star (vecQ (p.2 : Fin 4 → ℂ))) *
        sqMat (vecQ (q.1 : Fin 4 → ℂ)) (star (vecQ (q.2 : Fin 4 → ℂ)))
    rw [vecQ_qVec, vecQ_qVec, sqMat_mul, star_mul]

theorem mat_sqSC (p : S1 × S1) :
    ArchSOC.mat _ (sqSC p) = sqMat (vecQ (p.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (p.2 : Fin 4 → ℂ))) := by
  change ((sqGLC p : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = _
  rfl

theorem continuous_lmat_vecC : Continuous fun v : Fin 4 → ℂ => lmat (vecQ v : ℍ[ℂ,A,B]) := by
  have e : (fun v : Fin 4 → ℂ => lmat (vecQ v : ℍ[ℂ,A,B])) = fun v => !![v 0, A * v 1, B * v 2, -(A * B) * v 3;
      v 1, v 0, B * v 3, -B * v 2; v 2, -A * v 3, v 0, A * v 1; v 3, -v 2, v 1, v 0] := by
    funext v; rw [lmat_eq]; rfl
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_rmat_star_vecC : Continuous fun v : Fin 4 → ℂ => rmat (star (vecQ v : ℍ[ℂ,A,B])) := by
  have e : (fun v : Fin 4 → ℂ => rmat (star (vecQ v : ℍ[ℂ,A,B]))) = fun v => !![v 0, A * -v 1, B * -v 2,
      -(A * B) * -v 3; -v 1, v 0, -B * -v 3, B * -v 2; -v 2, A * -v 3, v 0, -A * -v 1; -v 3, -v 2, - -v 1, v 0] := by
    funext v; rw [rmat_eq]; simp [vecQ]
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_sqSC : Continuous (sqSC (A := A) (B := B)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ p : S1 × S1, ((ArchSOC.incl _ (sqSC p) : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) =
        sqMat (vecQ (p.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (p.2 : Fin 4 → ℂ))) := mat_sqSC
    refine (continuous_congr e).2 ?_
    have h1 : Continuous fun p : S1 × S1 => lmat (vecQ (p.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) :=
      continuous_lmat_vecC.comp (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : S1 × S1 => rmat (star (vecQ (p.2 : Fin 4 → ℂ) : ℍ[ℂ,A,B])) :=
      continuous_rmat_star_vecC.comp (continuous_subtype_val.comp continuous_snd)
    simp only [sqMat_eq_lmat_mul_rmatC]
    exact h1.matrix_mul h2
  · have e : ∀ p : S1 × S1, (((ArchSOC.incl _ (sqSC p) : GL (Fin 4) ℂ))⁻¹ : GL (Fin 4) ℂ).val =
        sqMat (vecQ ((p⁻¹).1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ ((p⁻¹).2 : Fin 4 → ℂ))) := fun p => by
      rw [← map_inv (ArchSOC.incl _), ← map_inv sqSC]; exact mat_sqSC _
    refine (continuous_congr e).2 ?_
    have h1 : Continuous fun p : S1 × S1 => lmat (vecQ ((p⁻¹).1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) :=
      continuous_lmat_vecC.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_inv))
    have h2 : Continuous fun p : S1 × S1 => rmat (star (vecQ ((p⁻¹).2 : Fin 4 → ℂ) : ℍ[ℂ,A,B])) :=
      continuous_rmat_star_vecC.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_inv))
    simp only [sqMat_eq_lmat_mul_rmatC]
    exact h1.matrix_mul h2

/-- **Kernel of the square map**: $\mathrm{sq}(x,y) = \mathrm{sq}(x',y')$ implies $(x',y') = r(x,y)$ with $r = \pm1$. -/
theorem eq_smul_of_sqSC_eq (hA : A ≠ 0) {p p' : S1 × S1} (h : sqSC p = sqSC p') :
    ∃ r : ℂ, r ^ 2 = 1 ∧ (p'.1 : Fin 4 → ℂ) = r • (p.1 : Fin 4 → ℂ) ∧ (p'.2 : Fin 4 → ℂ) = r • (p.2 : Fin 4 → ℂ) := by
  set X := (vecQ (p.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B])
  set Y := (vecQ (p.2 : Fin 4 → ℂ) : ℍ[ℂ,A,B])
  set X' := (vecQ (p'.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B])
  set Y' := (vecQ (p'.2 : Fin 4 → ℂ) : ℍ[ℂ,A,B])
  have hX : nrd X = 1 := nrd_sphC _
  have hY : nrd Y = 1 := nrd_sphC _
  have hX' : nrd X' = 1 := nrd_sphC _
  have hY' : nrd Y' = 1 := nrd_sphC _
  have hM : sqMat X (star Y) = sqMat X' (star Y') := by
    have := congrArg (ArchSOC.mat _) h
    rwa [mat_sqSC, mat_sqSC] at this
  have hv : ∀ v : ℍ[ℂ,A,B], X * v * star Y = X' * v * star Y' := fun v => by
    have := congrArg (· *ᵥ qVec v) hM
    simp only [sqMat_mulVec, vecQ_qVec] at this
    have := congrArg (vecQ (A := A) (B := B)) this
    rwa [vecQ_qVec, vecQ_qVec] at this
  have he := hv 1
  simp only [mul_one] at he
  have hsY : star Y = star X * (X * star Y) := by
    rw [← mul_assoc, star_mul_eq_nrd, hX]; simp
  have hsY' : star Y' = star X' * (X' * star Y') := by
    rw [← mul_assoc, star_mul_eq_nrd, hX']; simp
  have hcj : ∀ v : ℍ[ℂ,A,B], X * v * star X = X' * v * star X' := fun v => by
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
  obtain ⟨r, hr2, hr⟩ := eq_scalar_of_conj_trivialC hA ha fun y => by
    rw [hsa]
    calc star X' * X * Quat.pure y * (star X * X') = star X' * (X * Quat.pure y * star X) * X' := by
          simp only [mul_assoc]
      _ = star X' * (X' * Quat.pure y * star X') * X' := by rw [hcj]
      _ = (star X' * X') * Quat.pure y * (star X' * X') := by simp only [mul_assoc]
      _ = _ := by rw [star_mul_eq_nrd, hX']; simp
  have hXr : X = (r : ℍ[ℂ,A,B]) * X' := by
    have : X' * a = X := by rw [← mul_assoc, mul_star_eq_nrd, hX']; simp
    rw [← this, hr, ← QuaternionAlgebra.coe_commutes]
  have hr1 : r * r = 1 := by rw [← sq]; exact hr2
  have hX'r : X' = (r : ℍ[ℂ,A,B]) * X := by
    rw [hXr, ← mul_assoc, ← QuaternionAlgebra.coe_mul, hr1, QuaternionAlgebra.coe_one, one_mul]
  have hY'r : Y' = (r : ℍ[ℂ,A,B]) * Y := by
    have h2 : X * star Y = X * ((r : ℍ[ℂ,A,B]) * star Y') := by
      rw [he, hX'r, QuaternionAlgebra.coe_commutes, mul_assoc]
    have hu : IsUnit X := by rw [isUnit_iff_nrd_ne_zero, hX]; norm_num
    have h3 : star Y = (r : ℍ[ℂ,A,B]) * star Y' := hu.mul_right_inj.1 h2
    have h4 : star Y' = (r : ℍ[ℂ,A,B]) * star Y := by
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

variable {A B d t : ℂ} (ht0 : t ≠ 0) (ht : t ^ 2 = d)

local notation "S1" => SphC (normForm A B) 1
local notation "Q0" => nsFormC A B d

/-- $T^{-1} = \mathrm{diag}(1,t^{-1},t^{-1},t^{-1})$. -/
def tInvC (t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, t⁻¹, t⁻¹, t⁻¹]

theorem tMatC_eq_corner (t : ℂ) : tMatC t = cornerMat 1 (Matrix.diagonal ![t, t, t]) := by
  rw [tMatC, cornerMat_diagonal']; congr 1

theorem tInvC_eq_corner (t : ℂ) : tInvC t = cornerMat 1 (Matrix.diagonal ![t⁻¹, t⁻¹, t⁻¹]) := by
  rw [tInvC, cornerMat_diagonal']; congr 1

include ht0 in
theorem tMatC_mul_tInvC : tMatC t * tInvC t = 1 := by
  rw [tMatC, tInvC, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]

include ht0 in
theorem tInvC_mul_tMatC : tInvC t * tMatC t = 1 := by
  rw [tMatC, tInvC, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2; funext i; fin_cases i <;> simp [ht0]

include ht0 in
theorem tInvC_corner_tMatC (C : Matrix (Fin 3) (Fin 3) ℂ) : tInvC t * cornerMat 1 C * tMatC t = cornerMat 1 C := by
  rw [tInvC_eq_corner, tMatC_eq_corner, cornerMat_mul, cornerMat_mul, one_mul, one_mul]
  congr 1
  rw [show Matrix.diagonal ![t⁻¹, t⁻¹, t⁻¹] = t⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal],
    show Matrix.diagonal ![t, t, t] = t • (1 : Matrix (Fin 3) (Fin 3) ℂ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  first | rw [inv_mul_cancel₀ ht0, one_smul] | rw [mul_inv_cancel₀ ht0, one_smul]

/-- $g\mapsto T^{-1}gT$, $SO(N)\cong SO(Q_0)$. -/
def cTC : ArchSOC (normForm A B) ≃ₜ* ArchSOC Q0 :=
  conjSOC (tGLC ht0) 1 (by rw [tGLC_val]; exact hessian_nsFormC_eq ht) one_ne_zero

/-- **The map $\varphi_w$ at a complex place with $E_w = \mathbb C\times\mathbb C$**: $(x,y)\mapsto T^{-1}(v\mapsto xv\bar y)T$. -/
def phiSplitC : S1 × S1 →* ArchSOC Q0 := (cTC ht0 ht).toMonoidHom.comp sqSC

theorem mat_phiSplitC (p : S1 × S1) :
    ArchSOC.mat _ (phiSplitC ht0 ht p) =
      tInvC t * sqMat (vecQ (p.1 : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (p.2 : Fin 4 → ℂ))) * tMatC t := by
  change ArchSOC.mat _ (cTC ht0 ht (sqSC p)) = _
  rw [cTC, conjSOC_mat, mat_sqSC]; rfl

theorem continuous_phiSplitC : Continuous (phiSplitC (A := A) (B := B) ht0 ht) :=
  (cTC ht0 ht).continuous.comp continuous_sqSC

theorem eq_smul_of_phiSplitC_eq (hA : A ≠ 0) {p p' : S1 × S1} (h : phiSplitC ht0 ht p = phiSplitC ht0 ht p') :
    ∃ r : ℂ, r ^ 2 = 1 ∧ (p'.1 : Fin 4 → ℂ) = r • (p.1 : Fin 4 → ℂ) ∧ (p'.2 : Fin 4 → ℂ) = r • (p.2 : Fin 4 → ℂ) :=
  eq_smul_of_sqSC_eq hA ((cTC ht0 ht).injective h)

theorem isLocInj_phiSplitC (hA : A ≠ 0) : IsLocInj (phiSplitC (A := A) (B := B) ht0 ht) := by
  intro x
  set c := 1 / (1 + ‖A‖ + ‖B‖ + ‖A * B‖)
  have hc : 0 < c := by positivity
  refine ⟨{y | dist y.1 x.1 < Real.sqrt c}, isOpen_lt ((continuous_fst).dist continuous_const) continuous_const,
    by simpa using Real.sqrt_pos.2 hc, fun y hy y' hy' hyy => ?_⟩
  obtain ⟨r, hr2, h1, h2⟩ := eq_smul_of_phiSplitC_eq ht0 ht hA hyy
  rcases sq_eq_one_casesC hr2 with rfl | rfl
  · exact (Prod.ext (Subtype.ext (by simpa using h1)) (Subtype.ext (by simpa using h2))).symm
  · exfalso
    have hd : dist ((y'.1 : S1) : Fin 4 → ℂ) ((y.1 : S1) : Fin 4 → ℂ) < 2 * Real.sqrt c := by
      calc dist ((y'.1 : S1) : Fin 4 → ℂ) ((y.1 : S1) : Fin 4 → ℂ)
          ≤ dist ((y'.1 : S1) : Fin 4 → ℂ) (x.1 : Fin 4 → ℂ) + dist ((y.1 : S1) : Fin 4 → ℂ) (x.1 : Fin 4 → ℂ) :=
            dist_triangle_right _ _ _
        _ < Real.sqrt c + Real.sqrt c := add_lt_add hy' hy
        _ = 2 * Real.sqrt c := by ring
    rw [h1, dist_eq_norm, show (-1 : ℂ) • ((y.1 : S1) : Fin 4 → ℂ) - (y.1 : Fin 4 → ℂ) =
      (-2 : ℂ) • ((y.1 : S1) : Fin 4 → ℂ) by module, norm_smul] at hd
    have hn := norm_ge_of_sphC y.1
    have h2' : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [h2'] at hd
    have : ‖((y.1 : S1) : Fin 4 → ℂ)‖ < Real.sqrt c := by linarith
    have := (Real.lt_sqrt (norm_nonneg _)).1 this
    linarith

/-! #### The orbit decomposition -/

/-- $y\mapsto Ty$, $S_1(Q_0)\to S_1(N)$. -/
def sphTC : SphC Q0 1 → S1 := sphLinC (tMatC t) (eval_normForm_tMatC ht)

include ht0 ht in
theorem eval_tInvC (x : S1) : (nsFormC A B d).eval (tInvC t *ᵥ (x : Fin 4 → ℂ)) = 1 := by
  rw [← eval_normForm_tMatC ht, Matrix.mulVec_mulVec, tMatC_mul_tInvC ht0, Matrix.one_mulVec]; exact x.2

/-- $x\mapsto T^{-1}x$. -/
def invTC (x : S1) : SphC Q0 1 := ⟨tInvC t *ᵥ (x : Fin 4 → ℂ), eval_tInvC ht0 ht x⟩

include ht0 in
theorem sphTC_invTC (x : S1) : sphTC ht (invTC ht0 ht x) = x := by
  apply Subtype.ext
  show tMatC t *ᵥ (tInvC t *ᵥ (x : Fin 4 → ℂ)) = _
  rw [Matrix.mulVec_mulVec, tMatC_mul_tInvC ht0, Matrix.one_mulVec]

include ht0 in
theorem invTC_sphTC (y : SphC Q0 1) : invTC ht0 ht (sphTC ht y) = y := by
  apply Subtype.ext
  show tInvC t *ᵥ (tMatC t *ᵥ (y : Fin 4 → ℂ)) = _
  rw [Matrix.mulVec_mulVec, tInvC_mul_tMatC ht0, Matrix.one_mulVec]

/-- **The section** $y\mapsto T^{-1}L_{Ty}T$ of the orbit map of $SO(Q_0)$. -/
def secSplitC (y : SphC Q0 1) : ArchSOC Q0 := phiSplitC ht0 ht (sphTC ht y, 1)

theorem secSplitC_spec (y : SphC Q0 1) :
    ArchSOC.mat _ (secSplitC ht0 ht y) *ᵥ (e₀ : Fin 4 → ℂ) = (y : Fin 4 → ℂ) := by
  rw [secSplitC, mat_phiSplitC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have he : (e₀ : Fin 4 → ℂ) = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
  have h1 : tMatC t *ᵥ (e₀ : Fin 4 → ℂ) = e₀ := by
    rw [he, tMatC_mulVec]; funext i; fin_cases i <;> simp
  have h2 : (star (vecQ ((1 : S1) : Fin 4 → ℂ)) : ℍ[ℂ,A,B]) = 1 := by
    rw [show ((1 : S1) : Fin 4 → ℂ) = qVec (1 : ℍ[ℂ,A,B]) from rfl, vecQ_qVec, star_one]
  rw [h1, sqMat_mulVec, h2, vecQ_e₀, mul_one, mul_one, qVec_vecQ]
  show tInvC t *ᵥ (tMatC t *ᵥ (y : Fin 4 → ℂ)) = _
  rw [Matrix.mulVec_mulVec, tInvC_mul_tMatC ht0, Matrix.one_mulVec]

theorem continuous_secSplitC : Continuous (secSplitC (A := A) (B := B) ht0 ht) :=
  (continuous_phiSplitC ht0 ht).comp ((continuous_sphLinC _ _).prodMk continuous_const)

/-- $SO(\langle-A,-B,AB\rangle)\cong SO(\langle-Ad,-Bd,ABd\rangle)$ (the same matrices). -/
def cSC (hd0 : d ≠ 0) : ArchSOC (pureForm A B) ≃ₜ* ArchSOC (pureFormDC A B d) :=
  conjSOC (1 : GL (Fin 3) ℂ) d hessian_pureFormDC hd0

theorem mat_cSC (hd0 : d ≠ 0) (g : ArchSOC (pureForm A B)) :
    ArchSOC.mat _ (cSC (A := A) (B := B) hd0 g) = ArchSOC.mat _ g := by
  rw [cSC, conjSOC_mat]; simp

theorem mat_conjSC_eq_conjGL (h : S1) :
    ArchSOC.mat _ (conjSC h) = ((conjGL (toUnitC h) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) := rfl

/-- **The decomposition** $\varphi(eh,h) = s(T^{-1}e)\,\mathrm{diag}(1,c_h)$. -/
theorem phiSplitC_decomp (hd0 : d ≠ 0) (e h : S1) :
    phiSplitC ht0 ht (e * h, h) =
      secSplitC ht0 ht (invTC ht0 ht e) * iotaC 1 (pureFormDC A B d) (cSC hd0 (conjSC h)) := by
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (phiSplitC ht0 ht (e * h, h)) =
    ArchSOC.mat _ (secSplitC ht0 ht (invTC ht0 ht e)) * ArchSOC.mat _ (iotaC 1 (pureFormDC A B d) (cSC hd0 (conjSC h)))
  have h1 : (star (vecQ ((1 : S1) : Fin 4 → ℂ)) : ℍ[ℂ,A,B]) = 1 := by
    rw [show ((1 : S1) : Fin 4 → ℂ) = qVec (1 : ℍ[ℂ,A,B]) from rfl, vecQ_qVec, star_one]
  have h2 : (vecQ ((e * h : S1) : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = vecQ (e : Fin 4 → ℂ) * vecQ (h : Fin 4 → ℂ) := by
    rw [sphC_mul_val, vecQ_qVec]
  have h3 : cornerMat 1 ((conjGL (toUnitC h) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      sqMat (vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ))) := (sqMat_conj (toUnitC h)).symm
  have L : ArchSOC.mat _ (phiSplitC ht0 ht (e * h, h)) = tInvC t * sqMat (vecQ (e : Fin 4 → ℂ) *
      vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ))) * tMatC t := by
    rw [mat_phiSplitC]; simp only; rw [h2]
  have R1 : ArchSOC.mat _ (secSplitC ht0 ht (invTC ht0 ht e)) =
      tInvC t * sqMat (vecQ (e : Fin 4 → ℂ) : ℍ[ℂ,A,B]) 1 * tMatC t := by
    rw [secSplitC, mat_phiSplitC]; simp only; rw [sphTC_invTC ht0, h1]
  have R2 : ArchSOC.mat _ (iotaC 1 (pureFormDC A B d) (cSC hd0 (conjSC h))) =
      tInvC t * sqMat (vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ))) * tMatC t := by
    rw [mat_iotaC, mat_cSC, mat_conjSC_eq_conjGL, h3, ← h3, tInvC_corner_tMatC ht0]
  rw [L, R1, R2]
  calc tInvC t * sqMat (vecQ (e : Fin 4 → ℂ) * vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ))) * tMatC t
      = tInvC t * (sqMat (vecQ (e : Fin 4 → ℂ) : ℍ[ℂ,A,B]) 1 *
          sqMat (vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ)))) * tMatC t := by
        rw [sqMat_mul, mul_one]
    _ = tInvC t * sqMat (vecQ (e : Fin 4 → ℂ) : ℍ[ℂ,A,B]) 1 * (tMatC t * tInvC t) *
          sqMat (vecQ (h : Fin 4 → ℂ) : ℍ[ℂ,A,B]) (star (vecQ (h : Fin 4 → ℂ))) * tMatC t := by
        rw [tMatC_mul_tInvC ht0, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-! #### The test set and the constant -/

/-- The test set $\{(x,y) : y\in C,\ xy^{-1}\in C\}$. -/
def shearSetC (C : Set S1) : Set (S1 × S1) := {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ C}

theorem phiSplitC_image_shearSetC (hd0 : d ≠ 0) (C : Set S1) :
    phiSplitC ht0 ht '' shearSetC C =
      (fun q : SphC Q0 1 × ArchSOC (pureFormDC A B d) => secSplitC ht0 ht q.1 * iotaC 1 (pureFormDC A B d) q.2) ''
        ((sphTC ht ⁻¹' C) ×ˢ (cSC hd0 '' (conjSC '' C))) := by
  ext g
  constructor
  · rintro ⟨p, ⟨h2, h1⟩, rfl⟩
    have hp : p = (p.1 * p.2⁻¹ * p.2, p.2) := by rw [inv_mul_cancel_right]
    refine ⟨(invTC ht0 ht (p.1 * p.2⁻¹), cSC hd0 (conjSC p.2)), ⟨?_, ⟨conjSC p.2, ⟨p.2, h2, rfl⟩, rfl⟩⟩, ?_⟩
    · show sphTC ht (invTC ht0 ht _) ∈ C
      rw [sphTC_invTC ht0]; exact h1
    · show _ = phiSplitC ht0 ht p
      conv_rhs => rw [hp]
      rw [phiSplitC_decomp ht0 ht hd0]
  · rintro ⟨⟨y, w⟩, ⟨hy, ⟨_, ⟨h, hh, rfl⟩, rfl⟩⟩, rfl⟩
    refine ⟨(sphTC ht y * h, h), ⟨hh, by simpa using hy⟩, ?_⟩
    show phiSplitC ht0 ht (sphTC ht y * h, h) = _
    rw [phiSplitC_decomp ht0 ht hd0, invTC_sphTC ht0]

theorem injOn_phiSplitC_shearSetC (hA : A ≠ 0) {δ : ℝ} :
    InjOn (phiSplitC (A := A) (B := B) ht0 ht) (shearSetC (cayBallC A B δ)) := by
  intro p hp p' hp' h
  obtain ⟨r, hr2, h1, h2⟩ := eq_smul_of_phiSplitC_eq ht0 ht hA h
  rcases sq_eq_one_casesC hr2 with rfl | rfl
  · exact (Prod.ext (Subtype.ext (by simpa using h1)) (Subtype.ext (by simpa using h2))).symm
  · exfalso
    have a1 := hp.1.1; have a2 := hp'.1.1
    have := congrArg Complex.re (congrFun h2 0)
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, Complex.neg_re] at this
    linarith

theorem measurableSet_shearSetC {C : Set S1} (hC : MeasurableSet C) : MeasurableSet (shearSetC C) :=
  (measurable_snd hC).inter (hC.preimage (continuous_fst.mul (continuous_snd.inv)).measurable)

theorem leray_cSC_image (hd0 : d ≠ 0) (hQ3 : gramDetC (pureForm A B) ≠ 0) (hQ3d : gramDetC (pureFormDC A B d) ≠ 0)
    (X : Set (ArchSOC (pureForm A B))) (hX : MeasurableSet X) :
    lerayMeasureC (pureFormDC A B d) hQ3d (cSC hd0 '' X) =
      ENNReal.ofReal (‖d‖ ^ 12)⁻¹ * lerayMeasureC (pureForm A B) hQ3 X := by
  have h := map_lerayMeasureC_conjSOC' (1 : GL (Fin 3) ℂ) d hessian_pureFormDC hd0 hQ3 hQ3d
  have hm : MeasurableSet (cSC (A := A) (B := B) hd0 '' X) :=
    (cSC (A := A) (B := B) hd0).toHomeomorph.measurableEmbedding.measurableSet_image.2 hX
  have h2 := congrArg (fun μ => μ (cSC (A := A) (B := B) hd0 '' X)) h
  change (lerayMeasureC (pureForm A B) hQ3).map (cSC (A := A) (B := B) hd0) (cSC (A := A) (B := B) hd0 '' X) = _ at h2
  rw [Measure.map_apply (map_continuous (cSC (A := A) (B := B) hd0)).measurable hm,
    (cSC (A := A) (B := B) hd0).injective.preimage_image, Measure.smul_apply, smul_eq_mul] at h2
  have hd6 : (0 : ℝ) < ‖d‖ ^ 12 := pow_pos (norm_pos_iff.2 hd0) 12
  have e : ‖d‖ ^ (2 * (3 * (3 + 1) / 2)) * ‖((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ (2 * (3 + 1)) =
      ‖d‖ ^ 12 := by
    simp
  rw [h2, show (cSC (A := A) (B := B) hd0) = conjSOC (1 : GL (Fin 3) ℂ) d hessian_pureFormDC hd0 from rfl, e,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hd6.le), inv_mul_cancel₀ hd6.ne', ENNReal.ofReal_one, one_mul]

/-- **The local ratio at a complex place with $E_w = \mathbb C\times\mathbb C$.** For every measurable $Y\subseteq S_1\times S_1$ on which
$\varphi_w$ is injective, $\mu_{Q_0}(\varphi_w(Y)) = (1024|A|^6|B|^6|t|^6|d|^{12})^{-1}(\sigma_{\mathbb C}\otimes\sigma_{\mathbb C})(Y)$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratio, complex place); §3.7, pp. 64-65 [unverified page]"]
theorem lerayC_phiSplitC_image (hA : A ≠ 0) (hB : B ≠ 0) (hd0 : d ≠ 0) (hQ3 : gramDetC (pureForm A B) ≠ 0)
    (hQ3d : gramDetC (pureFormDC A B d) ≠ 0) (hQ0 : gramDetC Q0 ≠ 0) {Y : Set (S1 × S1)} (hY : MeasurableSet Y)
    (hinj : InjOn (phiSplitC ht0 ht) Y) :
    lerayMeasureC Q0 hQ0 (phiSplitC ht0 ht '' Y) =
      ENNReal.ofReal (1 / (1024 * ‖A‖ ^ 6 * ‖B‖ ^ 6 * ‖t‖ ^ 6 * ‖d‖ ^ 12)) *
        ((sigC (normForm A B) 1).prod (sigC (normForm A B) 1)) Y := by
  have := isHaarMeasure_lerayMeasureC (Q := Q0) (hQ := hQ0)
  obtain ⟨c, hc⟩ := exists_measure_image_eq_smul ((sigC (normForm A B) 1).prod (sigC (normForm A B) 1))
    (lerayMeasureC Q0 hQ0) (phiSplitC ht0 ht) (continuous_phiSplitC ht0 ht) (isLocInj_phiSplitC ht0 ht hA)
  -- a Cayley ball of positive measure
  obtain ⟨δ, hδ, hδr⟩ := ((eventually_nuC_cayBallC_pos (A := A) (B := B)).and
    (nhdsWithin_le_nhds (Iic_mem_nhds (radC_pos A B)))).exists
  set C := cayBallC A B δ
  have hCm : MeasurableSet C := measurableSet_cayBallC δ
  have hC0 : sigC (normForm A B) 1 C ≠ 0 := by
    rw [sigC, Measure.smul_apply, smul_eq_mul]
    refine mul_ne_zero (by simp) ?_
    intro h; rw [h] at hδ; simp at hδ
  have hCt : sigC (normForm A B) 1 C ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono (cayBallC_subset hδr))
    (IsCompact.measure_lt_top (isCompact_normLeC 2)))
  -- the two evaluations on the shear set
  have h1 := hc (shearSetC C) (measurableSet_shearSetC hCm) (injOn_phiSplitC_shearSetC ht0 ht hA)
  rw [shearSetC, sigC_prod_shear hCm hCm] at h1
  have hW : MeasurableSet (conjSC '' C) :=
    hCm.image_of_continuousOn_injOn continuous_conjSC.continuousOn (injOn_conjSC_cayBallC hA δ)
  have hWm : MeasurableSet (cSC (A := A) (B := B) hd0 '' (conjSC '' C)) :=
    (cSC (A := A) (B := B) hd0).toHomeomorph.measurableEmbedding.measurableSet_image.2 hW
  have h2 := lerayMeasureC_image_sec one_ne_zero hQ3d Q0 rfl hQ0 (secSplitC ht0 ht)
    (continuous_secSplitC ht0 ht).measurable (secSplitC_spec ht0 ht) (iotaC 1 (pureFormDC A B d))
    (mat_iotaC 1 (pureFormDC A B d))
    (hCm.preimage (continuous_sphLinC (tMatC t) (eval_normForm_tMatC (A := A) (B := B) ht)).measurable) hWm
  have h64 : (((‖(2 : ℂ) * 1‖₊ ^ (2 * 3))⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / 64) := by
    have h2' : ‖(2 : ℂ) * 1‖₊ = 2 := by ext; simp
    rw [h2', ← ENNReal.ofReal_coe_nnreal]
    push_cast
    norm_num
  have h2' : lerayMeasureC Q0 hQ0 (phiSplitC ht0 ht '' shearSetC C) = ENNReal.ofReal (1 / 64) *
      (sigC Q0 1 (sphLinC (tMatC t) (eval_normForm_tMatC (A := A) (B := B) ht) ⁻¹' C) *
        lerayMeasureC (pureFormDC A B d) hQ3d (cSC hd0 '' (conjSC '' C))) := by
    rw [phiSplitC_image_shearSetC ht0 ht hd0, ← h64]; exact h2
  clear h2
  have h2 := h2'
  rw [sigC_preimage_sphLinC (tMatC t) (by rw [det_tMatC]; exact pow_ne_zero 3 ht0)
    (eval_normForm_tMatC ht) hCm, det_tMatC, leray_cSC_image hd0 hQ3 hQ3d _ hW,
    leray_conjSC_image hA hB hQ3 hCm (injOn_conjSC_cayBallC hA δ)] at h2
  have hset : phiSplitC ht0 ht '' shearSetC C = phiSplitC ht0 ht '' {p | p.2 ∈ C ∧ p.1 * p.2⁻¹ ∈ C} := rfl
  rw [hset, h1] at h2
  -- solve for `c`
  have hk : (c : ℝ≥0∞) = ENNReal.ofReal (1 / (1024 * ‖A‖ ^ 6 * ‖B‖ ^ 6 * ‖t‖ ^ 6 * ‖d‖ ^ 12)) := by
    have hCC : sigC (normForm A B) 1 C * sigC (normForm A B) 1 C ≠ 0 := mul_ne_zero hC0 hC0
    have hCCt : sigC (normForm A B) 1 C * sigC (normForm A B) 1 C ≠ ⊤ := ENNReal.mul_ne_top hCt hCt
    refine (ENNReal.mul_left_inj hCC hCCt).1 ?_
    rw [h2]
    have hA6 : 0 < ‖A‖ ^ 6 := pow_pos (norm_pos_iff.2 hA) 6
    have hB6 : 0 < ‖B‖ ^ 6 := pow_pos (norm_pos_iff.2 hB) 6
    have ht3 : 0 < ‖t ^ 3‖ ^ 2 := pow_pos (norm_pos_iff.2 (pow_ne_zero 3 ht0)) 2
    have hd6 : 0 < ‖d‖ ^ 12 := pow_pos (norm_pos_iff.2 hd0) 12
    calc ENNReal.ofReal (1 / 64) * (ENNReal.ofReal (‖t ^ 3‖ ^ 2)⁻¹ * sigC (normForm A B) 1 C *
          (ENNReal.ofReal (‖d‖ ^ 12)⁻¹ * (ENNReal.ofReal (1 / (16 * ‖A‖ ^ 6 * ‖B‖ ^ 6)) * sigC (normForm A B) 1 C)))
        = ENNReal.ofReal (1 / 64 * (‖t ^ 3‖ ^ 2)⁻¹ * (‖d‖ ^ 12)⁻¹ * (1 / (16 * ‖A‖ ^ 6 * ‖B‖ ^ 6))) *
            (sigC (normForm A B) 1 C * sigC (normForm A B) 1 C) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
      _ = _ := by
          congr 2
          rw [norm_pow]
          field_simp
          ring
  rw [hc Y hY hinj, hk]

end Split

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
