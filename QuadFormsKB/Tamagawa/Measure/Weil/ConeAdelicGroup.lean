import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicFrame
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereMeas
import QuadFormsKB.Tamagawa.Measure.Weil.SOAdeleAction
import QuadFormsKB.Tamagawa.Measure.ConeFiniteGroup

/-!
# The parabolic subgroup of $SO(V)(\mathbb A)$ for the cone form

$F$ a number field, $c_0\in\mathcal O_F\setminus0$, $Q_0'$ nondegenerate over $\mathcal O_F$ in $k$ variables and
$Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ (`ConeFinite.Qcone c₀ Q₀'`, $n = k+2$ variables
$x_0, x_1, x_2,\dots,x_{k+1}$). With $e = e_0 + e_1$ (isotropic, rational):

* **`mkSOAdele`**: an element of $SO(V)(\mathbb A)$ from local matrices (isometries of determinant $1$, integral with
  integral inverse at almost every finite place); **`SOAdele.ext_mat`**: elements are determined by their local matrices.
* **`coneN`** ($n_{\mathbb A}(w)$, $w\in\mathbb A^k$), **`hA`** ($h\mapsto\mathrm{diag}(1,1,h)$ on $SO(Q_0')(\mathbb A)$, a
  homomorphism) and **`dA`** ($d(z)$, $z\in\mathbb A^\times$): the local elements `ConeAlgebra.nM`, `mM`, `dM` at every
  place; $n(w)$ is integral at $v\nmid 2c_0$ when $w_v$ is (`nM_mem_intMat`), $d(z)$ when $z_v$ is a unit.
* Relations: $n(w + w') = n(w)n(w')$ (`coneN_add`), $h\,n(w)\,h^{-1} = n(hw)$ (`hA_mul_coneN`), $d(z)n(w) = n(zw)d(z)$ (`dA_mul_coneN`),
  $d(z)h = h\,d(z)$ (`hA_mul_dA`), $n(w)e = e$, $h\,e = e$, $d(z)e = ze$ (`coneN_smul_eA`, `hA_smul_eA`, `dA_smul_eA`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {F : Type} [Field F] [NumberField F]

/-! ### Elements of $SO(V)(\mathbb A)$ from local matrices -/

section MkSO

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- The local isometry condition $M^{\mathsf T}H_\sigma M = H_\sigma$, $\det M = 1$. -/
def IsSOAt {K : Type*} [Field K] (σ : F →+* K) (M : GL (Fin n) K) : Prop :=
  M.valᵀ * hesAt Q₀ σ * M.val = hesAt Q₀ σ ∧ M.val.det = 1

/-- **An element of $SO(V)(\mathbb A)$ from local matrices** $M_w\in SO(Q)(\mathbb R)$, $M_w\in SO(Q)(\mathbb C)$,
$M_v\in SO(Q)(F_v)$ with $M_v, M_v^{-1}$ integral for almost all $v$. -/
def mkSOAdele (MR : ∀ w : {w : InfinitePlace F // w.IsReal}, GL (Fin n) ℝ) (hR : ∀ w, IsSOAt Q₀ (σR w) (MR w))
    (MC : ∀ w : {w : InfinitePlace F // w.IsComplex}, GL (Fin n) ℂ) (hC : ∀ w, IsSOAt Q₀ (σC w) (MC w))
    (MV : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F)) (hV : ∀ v, IsSOAt Q₀ (σV v) (MV v))
    (hint : ∀ᶠ v in Filter.cofinite, (MV v).val ∈ intMat v ∧ (MV v)⁻¹.val ∈ intMat v) : SOAdele Q₀ :=
  ((fun w => ⟨MR w, mem_soReal_of Q₀ (σR w) (hR w).1 (hR w).2⟩,
    fun w => ⟨MC w, mem_soC_of Q₀ (σC w) (hC w).1 (hC w).2⟩),
   ⟨⟨fun v => ⟨MV v, mem_orthGroup_of Q₀ v (hV v).1⟩, by
      filter_upwards [hint] with v hv
      show MV v ∈ glInt v
      rw [mem_glInt_iff v]; exact hv⟩, fun v => (hV v).2⟩)

variable {Q₀}

@[simp] theorem matR_mkSOAdele {MR hR MC hC MV hV hint} (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (mkSOAdele Q₀ MR hR MC hC MV hV hint) w = (MR w).val := rfl

@[simp] theorem matC_mkSOAdele {MR hR MC hC MV hV hint} (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (mkSOAdele Q₀ MR hR MC hC MV hV hint) w = (MC w).val := rfl

@[simp] theorem matV_mkSOAdele {MR hR MC hC MV hV hint} (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (mkSOAdele Q₀ MR hR MC hC MV hV hint) v = (MV v).val := rfl

/-- **Elements of $SO(V)(\mathbb A)$ are determined by their local matrices.** -/
theorem SOAdele.ext_mat {g h : SOAdele Q₀} (hR : ∀ w, matR Q₀ g w = matR Q₀ h w)
    (hC : ∀ w, matC Q₀ g w = matC Q₀ h w) (hV : ∀ v, matV Q₀ g v = matV Q₀ h v) : g = h := by
  refine Prod.ext (Prod.ext (funext fun w => Subtype.ext (Units.ext (hR w)))
    (funext fun w => Subtype.ext (Units.ext (hC w)))) ?_
  exact Subtype.ext (RestrictedProduct.ext _ _ fun v => Subtype.ext (Units.ext (hV v)))

theorem matR_inv (g : SOAdele Q₀) (w) : matR Q₀ g⁻¹ w = ((ArchSO.incl _ (g.1.1 w))⁻¹ : GL (Fin n) ℝ).val := rfl

theorem matC_inv (g : SOAdele Q₀) (w) :
    matC Q₀ g⁻¹ w = ((ArchSOC.incl _ (g.1.2 w))⁻¹ : GL (Fin n) ℂ).val := rfl

theorem matV_inv (g : SOAdele Q₀) (v) :
    matV Q₀ g⁻¹ v = (((((g.2 : OAf QF) v : orthGroup QF (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)))⁻¹ :
      GL (Fin n) (v.adicCompletion F)).val := rfl

/-- The action in components. -/
theorem smul_apply_fst_fst (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) (w : {w : InfinitePlace F // w.IsReal}) :
    adR (g • y) w = matR Q₀ g w *ᵥ adR y w := rfl

theorem smul_apply_fst_snd (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) (w : {w : InfinitePlace F // w.IsComplex}) :
    adC (g • y) w = matC Q₀ g w *ᵥ adC y w := rfl

theorem smul_apply_snd (g : SOAdele Q₀) (y : AdeleSpace F (Fin n)) (v : HeightOneSpectrum (𝓞 F)) :
    adV (g • y) v = matV Q₀ g v *ᵥ adV y v := rfl

/-- **Adelic vectors are determined by their components.** -/
theorem adeleSpace_ext {y y' : AdeleSpace F (Fin n)} (hR : ∀ w, adR y w = adR y' w) (hC : ∀ w, adC y w = adC y' w)
    (hV : ∀ v, adV y v = adV y' v) : y = y' := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => congrFun (hR w) i) (funext fun w => congrFun (hC w) i)) ?_
  exact Subtype.ext (funext fun v => congrFun (hV v) i)

end MkSO

/-! ### The cone form at the places -/

section ConeAt

variable (c₀ : 𝓞 F) {k : ℕ} (Q₀' : QuadForm (𝓞 F) k)

/-- $c_0$ at an embedding $\sigma$. -/
abbrev cAt {K : Type*} [Field K] (σ : F →+* K) : K := σ (algebraMap (𝓞 F) F c₀)

/-- $Q_0'$ at an embedding $\sigma$. -/
abbrev QAt {K : Type*} [Field K] (σ : F →+* K) : QuadForm K k := (Q₀'.map (algebraMap (𝓞 F) F)).map σ

theorem hesAt_cone {K : Type*} [Field K] (σ : F →+* K) :
    hesAt (ConeFinite.Qcone c₀ Q₀') σ = (coneForm (cAt c₀ σ) (QAt Q₀' σ)).hessian := by
  unfold hesAt
  rw [← Siegel.hessian_map_NF]
  congr 1
  simp only [ConeFinite.Qcone, map_splitForm, map_neg, coneForm]

theorem hesAt_base {K : Type*} [Field K] (σ : F →+* K) : hesAt Q₀' σ = (QAt Q₀' σ).hessian :=
  (Siegel.hessian_map_NF _ _).symm

variable {c₀}

theorem cAt_ne_zero (hc : c₀ ≠ 0) {K : Type*} [Field K] (σ : F →+* K) : cAt c₀ σ ≠ 0 :=
  (map_ne_zero σ).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc)

theorem det_hesAt_ne_zero {n : ℕ} {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) {K : Type*} [Field K]
    (σ : F →+* K) : (hesAt Q σ).det ≠ 0 := by
  rw [hesAt, show ((Q.map (algebraMap (𝓞 F) F)).hessian.map σ) = σ.mapMatrix (Q.map (algebraMap (𝓞 F) F)).hessian
    from rfl, ← RingHom.map_det]
  exact (map_ne_zero σ).mpr (nondegenerate_QF Q hQ)

theorem det_hess_cone_ne_zero (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) {K : Type*} [Field K] (σ : F →+* K) :
    (coneForm (cAt c₀ σ) (QAt Q₀' σ)).hessian.det ≠ 0 := by
  rw [← hesAt_cone]
  exact det_hesAt_ne_zero (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') σ

theorem det_hess_base_ne_zero (hQ' : Q₀'.Nondegenerate) {K : Type*} [Field K] (σ : F →+* K) :
    (QAt Q₀' σ).hessian.det ≠ 0 := by
  rw [← hesAt_base]
  exact det_hesAt_ne_zero hQ' σ

end ConeAt

/-! ### The local elements as invertible matrices -/

section LocalGL

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

/-- $n(w)$ in $\mathrm{GL}$. -/
def nGL (c : K) (Q' : QuadForm K k) (hc : c ≠ 0) (w : Fin k → K) : GL (Fin (k + 1 + 1)) K :=
  ⟨nM c Q' w, nM c Q' (-w), nM_mul_neg c Q' hc w, nM_neg_mul c Q' hc w⟩

/-- $\mathrm{diag}(1,1,h)$ in $\mathrm{GL}$. -/
def mGL (h : GL (Fin k) K) : GL (Fin (k + 1 + 1)) K :=
  ⟨mM h.val, mM h⁻¹.val, by rw [mM_mul, Units.mul_inv, mM_one], by rw [mM_mul, Units.inv_mul, mM_one]⟩

/-- $d(a)$ in $\mathrm{GL}$. -/
def dGL {a : K} (ha : a ≠ 0) : GL (Fin (k + 1 + 1)) K :=
  ⟨dM a, dM a⁻¹, dM_mul_inv ha, dM_inv_mul ha⟩

@[simp] theorem nGL_val (c : K) (Q' : QuadForm K k) (hc : c ≠ 0) (w : Fin k → K) : (nGL c Q' hc w).val = nM c Q' w :=
  rfl

@[simp] theorem nGL_inv_val (c : K) (Q' : QuadForm K k) (hc : c ≠ 0) (w : Fin k → K) :
    (nGL c Q' hc w)⁻¹.val = nM c Q' (-w) := rfl

@[simp] theorem mGL_val (h : GL (Fin k) K) : (mGL h).val = mM h.val := rfl

@[simp] theorem mGL_inv_val (h : GL (Fin k) K) : (mGL h)⁻¹.val = mM h⁻¹.val := rfl

@[simp] theorem dGL_val {a : K} (ha : a ≠ 0) : (dGL (k := k) ha).val = dM a := rfl

@[simp] theorem dGL_inv_val {a : K} (ha : a ≠ 0) : (dGL (k := k) ha)⁻¹.val = dM a⁻¹ := rfl

end LocalGL

/-! ### Integrality at the finite places -/

section Integral

variable (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- A matrix is integral if it maps the standard basis vectors to integral vectors. -/
theorem mem_intMat_of_mulVec {M : Matrix (Fin n) (Fin n) Fv} (h : ∀ j, IntVec v (M *ᵥ Pi.single j 1)) :
    M ∈ intMat v := fun i j => by
  have := h j i
  rwa [mulVec_single_one, Matrix.col_apply] at this

theorem intVec_single (j : Fin n) : IntVec v (Pi.single j (1 : Fv)) := fun i => by
  rw [Pi.single_apply]; split_ifs <;> simp

theorem IntVec.smul {a : Fv} (ha : Valued.v a ≤ 1) {x : Fin n → Fv} (hx : IntVec v x) : IntVec v (a • x) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_one' ha (hx i)

theorem valued_dotProduct_le_one {x y : Fin n → Fv} (hx : IntVec v x) (hy : IntVec v y) : Valued.v (x ⬝ᵥ y) ≤ 1 := by
  simp only [dotProduct]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]; exact mul_le_one' (hx l) (hy l)

theorem IntVec.v3 {k : ℕ} {a b : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) {y : Fin k → Fv} (hy : IntVec v y) :
    IntVec v (ConeAlgebra.v3 a b y) := fun i => by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simpa [ConeAlgebra.v3] using ha
  · simpa [ConeAlgebra.v3] using hb
  · simpa [ConeAlgebra.v3] using hy i

theorem IntVec.tl {k : ℕ} {x : Fin (k + 1 + 1) → Fv} (hx : IntVec v x) : IntVec v (ConeAlgebra.tl x) := fun i => hx _

variable {k : ℕ} (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k)

/-- **$n(w)$ is integral** at a place $v\nmid 2c_0$ when $w$ is integral. -/
theorem nM_mem_intMat (h2c : Valued.v (cAt c₀ (σV v) * 2) = 1) {w : Fin k → Fv} (hw : IntVec v w) :
    nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) w ∈ intMat v := by
  refine mem_intMat_of_mulVec v fun j => ?_
  have hx : IntVec v (Pi.single j (1 : Fv)) := intVec_single v j
  rw [← ConeAlgebra.v3_eta (Pi.single j (1 : Fv)), nM_mulVec_v3]
  set x := (Pi.single j (1 : Fv) : Fin (k + 1 + 1) → Fv)
  have hH' : (QAt Q₀' (σV v)).hessian ∈ intMat v := by rw [← hesAt_base]; exact hesAt_mem_intMat v Q₀'
  have hQw : Valued.v ((QAt Q₀' (σV v)).eval w * 2) ≤ 1 := by
    have h2 := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := Fv) (QAt Q₀' (σV v)) w
    rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h2
    rw [mul_comm, h2]
    exact qH_le_one v hH' hw
  have hnum : Valued.v (((QAt Q₀' (σV v)).hessian *ᵥ w) ⬝ᵥ ConeAlgebra.tl x + (x 0 - x 1) * (QAt Q₀' (σV v)).eval w)
      ≤ Valued.v (2 : Fv)⁻¹ := by
    have h1 : Valued.v (((QAt Q₀' (σV v)).hessian *ᵥ w) ⬝ᵥ ConeAlgebra.tl x) ≤ 1 :=
      valued_dotProduct_le_one v (hw.mulVec v hH') (hx.tl v)
    have h2 : Valued.v ((x 0 - x 1) * (QAt Q₀' (σV v)).eval w) ≤ Valued.v (2 : Fv)⁻¹ := by
      have : (x 0 - x 1) * (QAt Q₀' (σV v)).eval w = (x 0 - x 1) * ((QAt Q₀' (σV v)).eval w * 2) * (2 : Fv)⁻¹ := by
        field_simp
      rw [this, Valuation.map_mul, Valuation.map_mul]
      refine mul_le_of_le_one_left' (mul_le_one' ((Valuation.map_sub _ _ _).trans (max_le (hx 0) (hx 1))) hQw)
    have h2le : (1 : _) ≤ Valued.v (2 : Fv)⁻¹ := by
      rw [map_inv₀]; exact one_le_inv₀ (by
        have h := valued_two_le_one v
        exact (Valuation.pos_iff _).mpr two_ne_zero) |>.mpr (valued_two_le_one v)
    exact (Valuation.map_add _ _ _).trans (max_le (h1.trans h2le) h2)
  have hdiv : ∀ t : Fv, Valued.v t ≤ Valued.v (2 : Fv)⁻¹ → Valued.v (t / (2 * cAt c₀ (σV v))) ≤ 1 := by
    intro t ht
    have hc2 : Valued.v (2 * cAt c₀ (σV v)) = 1 := by rw [mul_comm]; exact h2c
    have hc : Valued.v (cAt c₀ (σV v)) = Valued.v (2 : Fv)⁻¹ := by
      rw [Valuation.map_mul] at hc2
      rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right hc2
    rw [map_div₀, hc2, div_one]
    calc Valued.v t ≤ Valued.v (2 : Fv)⁻¹ := ht
      _ = Valued.v (cAt c₀ (σV v)) := hc.symm
      _ ≤ 1 := sph_valued_int_le_one v c₀
  refine IntVec.v3 v ?_ ?_ ?_
  · exact (Valuation.map_sub _ _ _).trans (max_le (hx 0) (hdiv _ hnum))
  · exact (Valuation.map_sub _ _ _).trans (max_le (hx 1) (hdiv _ hnum))
  · exact (hx.tl v).add v ((hw).smul v ((Valuation.map_sub _ _ _).trans (max_le (hx 0) (hx 1))))

end Integral


/-! ### Integrality of $d(a)$ and of the Levi factor -/

section Integral2

variable (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}

local notation "Fv" => v.adicCompletion F

theorem v_add_le_one {a b : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) : Valued.v (a + b) ≤ 1 :=
  (Valuation.map_add _ _ _).trans (max_le ha hb)

theorem v_sub_le_one {a b : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) : Valued.v (a - b) ≤ 1 :=
  (Valuation.map_sub _ _ _).trans (max_le ha hb)

theorem v_mul_le_one {a b : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) : Valued.v (a * b) ≤ 1 := by
  rw [Valuation.map_mul]; exact mul_le_one' ha hb

theorem IntVec.neg {n : ℕ} {x : Fin n → Fv} (hx : IntVec v x) : IntVec v (-x) := fun i => by
  rw [Pi.neg_apply, Valuation.map_neg]; exact hx i

/-- **$d(a)$ is integral** when $a$ is a unit and $2$ is a unit. -/
theorem dM_mem_intMat (h2 : Valued.v (2 : Fv) = 1) {a : Fv} (ha : Valued.v a ≤ 1) (ha' : Valued.v a⁻¹ ≤ 1) :
    dM (k := k) a ∈ intMat v := by
  refine mem_intMat_of_mulVec v fun j => ?_
  have hx : IntVec v (Pi.single j (1 : Fv) : Fin (k + 1 + 1) → Fv) := intVec_single v j
  rw [← ConeAlgebra.v3_eta (Pi.single j (1 : Fv)), dM_mulVec_v3]
  have hdiv : ∀ t : Fv, Valued.v t ≤ 1 → Valued.v (t / 2) ≤ 1 := fun t ht => by
    rw [map_div₀, h2, div_one]; exact ht
  have h1 : Valued.v ((1 : Fv)) ≤ 1 := by simp
  have hx0 := hx 0
  have hx1 := hx 1
  refine IntVec.v3 v ?_ ?_ (hx.tl v)
  · exact v_add_le_one v (v_add_le_one v hx0 (v_mul_le_one v (hdiv _ (v_sub_le_one v ha h1))
      (v_add_le_one v hx0 hx1))) (v_mul_le_one v (hdiv _ (v_sub_le_one v ha' h1)) (v_sub_le_one v hx0 hx1))
  · exact v_sub_le_one v (v_add_le_one v hx1 (v_mul_le_one v (hdiv _ (v_sub_le_one v ha h1))
      (v_add_le_one v hx0 hx1))) (v_mul_le_one v (hdiv _ (v_sub_le_one v ha' h1)) (v_sub_le_one v hx0 hx1))

theorem mM_mem_intMat {M : Matrix (Fin k) (Fin k) Fv} (hM : M ∈ intMat v) : mM M ∈ intMat v :=
  cornerMat_mem_intMat v (cornerMat_mem_intMat v hM)

end Integral2

/-! ### The adelic elements $n_{\mathbb A}(w)$, $\mathrm{diag}(1,1,h)$, $d(z)$ -/

section Adelic

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

include hc hQ' in
theorem isSOAt_nGL {K : Type*} [Field K] [CharZero K] (σ : F →+* K) (w : Fin k → K) :
    IsSOAt QC σ (nGL (cAt c₀ σ) (QAt Q₀' σ) (cAt_ne_zero hc σ) w) := by
  unfold IsSOAt; rw [hesAt_cone]
  exact ⟨isometry_nM _ _ (cAt_ne_zero hc σ) w,
    det_nM _ _ (cAt_ne_zero hc σ) (det_hess_cone_ne_zero Q₀' hc hQ' σ) w⟩

theorem isSOAt_dGL {K : Type*} [Field K] [CharZero K] (σ : F →+* K) {a : K} (ha : a ≠ 0) :
    IsSOAt QC σ (dGL (k := k) ha) := by
  unfold IsSOAt; rw [hesAt_cone]
  exact ⟨isometry_dM _ _ ha, ConeFinite.det_dM_eq_one ha⟩

theorem isSOAt_mGL {K : Type*} [Field K] [CharZero K] (σ : F →+* K) {h : GL (Fin k) K}
    (hh : IsSOAt Q₀' σ h) : IsSOAt QC σ (mGL h) := by
  unfold IsSOAt at hh ⊢; rw [hesAt_cone]; rw [hesAt_base] at hh
  exact ⟨isometry_mM _ _ hh.1, by rw [mGL_val, det_mM, hh.2]⟩

include hc in
theorem eventually_two_c : ∀ᶠ v in Filter.cofinite, Valued.v (cAt c₀ (σV v) * 2) = 1 := by
  have h : (algebraMap (𝓞 F) F c₀ * 2) ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc) two_ne_zero
  filter_upwards [sph_eventually_valued_eq_one h] with v hv
  have e : cAt c₀ (σV v) * 2 = σV v (algebraMap (𝓞 F) F c₀ * 2) := by rw [map_mul, map_ofNat]
  rw [e]; exact hv

theorem eventually_two : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (2 : v.adicCompletion F) = 1 := by
  filter_upwards [sph_eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hv
  rwa [map_ofNat] at hv

/-- **The unipotent element** $n_{\mathbb A}(w)\in SO(V)(\mathbb A)$ for $w\in\mathbb A^k$ (at every place the Eichler
transformation `nM` of `ConeAlgebra`). -/
def coneN (y : AdeleSpace F (Fin k)) : SOAdele QC :=
  mkSOAdele QC (fun w => nGL _ _ (cAt_ne_zero hc (σR w)) (adR y w)) (fun w => isSOAt_nGL hc hQ' _ _)
    (fun w => nGL _ _ (cAt_ne_zero hc (σC w)) (adC y w)) (fun w => isSOAt_nGL hc hQ' _ _)
    (fun v => nGL _ _ (cAt_ne_zero hc (σV v)) (adV y v)) (fun v => isSOAt_nGL hc hQ' _ _) (by
      filter_upwards [eventually_two_c hc, eventually_intVec y] with v h2 hy
      exact ⟨nM_mem_intMat v c₀ Q₀' h2 hy, nM_mem_intMat v c₀ Q₀' h2 (hy.neg v)⟩)

@[simp] theorem matR_coneN (y : AdeleSpace F (Fin k)) (w) :
    matR QC (coneN hc hQ' y) w = nM (cAt c₀ (σR w)) (QAt Q₀' (σR w)) (adR y w) := rfl

@[simp] theorem matC_coneN (y : AdeleSpace F (Fin k)) (w) :
    matC QC (coneN hc hQ' y) w = nM (cAt c₀ (σC w)) (QAt Q₀' (σC w)) (adC y w) := rfl

@[simp] theorem matV_coneN (y : AdeleSpace F (Fin k)) (v) :
    matV QC (coneN hc hQ' y) v = nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (adV y v) := rfl

/-- The local components of $h\in SO(Q_0')(\mathbb A)$ are isometries of determinant $1$. -/
theorem isSOAt_R (h : SOAdele Q₀') (w : {w : InfinitePlace F // w.IsReal}) :
    IsSOAt Q₀' (σR w) (ArchSO.incl _ (h.1.1 w)) :=
  AdelicSphereSetup.hes_of_mem_soReal Q₀' (σR w) (h.1.1 w).2

theorem isSOAt_C (h : SOAdele Q₀') (w : {w : InfinitePlace F // w.IsComplex}) :
    IsSOAt Q₀' (σC w) (ArchSOC.incl _ (h.1.2 w)) :=
  AdelicSphereSetup.hes_of_mem_soC Q₀' (σC w) (h.1.2 w).2

theorem isSOAt_V (h : SOAdele Q₀') (v : HeightOneSpectrum (𝓞 F)) :
    IsSOAt Q₀' (σV v) ((((h.2 : OAf (Q₀'.map (algebraMap (𝓞 F) F))) v :
      orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin k) (v.adicCompletion F))) :=
  ⟨(mem_orthGroup _).mp ((h.2 : OAf (Q₀'.map (algebraMap (𝓞 F) F))) v).2, h.2.2 v⟩

/-- **The Levi factor** $h\mapsto\mathrm{diag}(1,1,h)$, $SO(Q_0')(\mathbb A)\to SO(V)(\mathbb A)$. -/
def hA : SOAdele Q₀' →* SOAdele QC where
  toFun h := mkSOAdele QC (fun w => mGL (ArchSO.incl _ (h.1.1 w))) (fun w => isSOAt_mGL _ (isSOAt_R h w))
    (fun w => mGL (ArchSOC.incl _ (h.1.2 w))) (fun w => isSOAt_mGL _ (isSOAt_C h w))
    (fun v => mGL ((((h.2 : OAf (Q₀'.map (algebraMap (𝓞 F) F))) v :
      orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin k) (v.adicCompletion F))))
    (fun v => isSOAt_mGL _ (isSOAt_V h v)) (by
      filter_upwards [(h.2 : OAf (Q₀'.map (algebraMap (𝓞 F) F))).2] with v hv
      have hv' := (mem_glInt_iff v).mp hv
      exact ⟨mM_mem_intMat v hv'.1, mM_mem_intMat v hv'.2⟩)
  map_one' := SOAdele.ext_mat (fun w => mM_one) (fun w => mM_one) (fun v => mM_one)
  map_mul' a b := SOAdele.ext_mat (fun w => (mM_mul _ _).symm) (fun w => (mM_mul _ _).symm)
    (fun v => (mM_mul _ _).symm)

@[simp] theorem matR_hA (h : SOAdele Q₀') (w) : matR QC (hA (c₀ := c₀) h) w = mM (matR Q₀' h w) := rfl

@[simp] theorem matC_hA (h : SOAdele Q₀') (w) : matC QC (hA (c₀ := c₀) h) w = mM (matC Q₀' h w) := rfl

@[simp] theorem matV_hA (h : SOAdele Q₀') (v) : matV QC (hA (c₀ := c₀) h) v = mM (matV Q₀' h v) := rfl

/-! #### The torus element $d(z)$ -/

section Torus

variable (z : (Adeles F)ˣ)

theorem ideleR_mul_inv (w : {w : InfinitePlace F // w.IsReal}) :
    (z : Adeles F).1.1 w * (z⁻¹ : (Adeles F)ˣ).val.1.1 w = 1 :=
  congrArg (fun a : Adeles F => a.1.1 w) (Units.mul_inv z)

theorem ideleC_mul_inv (w : {w : InfinitePlace F // w.IsComplex}) :
    (z : Adeles F).1.2 w * (z⁻¹ : (Adeles F)ˣ).val.1.2 w = 1 :=
  congrArg (fun a : Adeles F => a.1.2 w) (Units.mul_inv z)

theorem ideleV_mul_inv (v : HeightOneSpectrum (𝓞 F)) :
    (z : Adeles F).2 v * (z⁻¹ : (Adeles F)ˣ).val.2 v = 1 :=
  congrArg (fun a : Adeles F => a.2 v) (Units.mul_inv z)

theorem ideleR_ne (w : {w : InfinitePlace F // w.IsReal}) : (z : Adeles F).1.1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ideleR_mul_inv z w)

theorem ideleC_ne (w : {w : InfinitePlace F // w.IsComplex}) : (z : Adeles F).1.2 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ideleC_mul_inv z w)

theorem ideleV_ne (v : HeightOneSpectrum (𝓞 F)) : (z : Adeles F).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ideleV_mul_inv z v)

theorem ideleV_inv (v : HeightOneSpectrum (𝓞 F)) : ((z : Adeles F).2 v)⁻¹ = (z⁻¹ : (Adeles F)ˣ).val.2 v :=
  (eq_inv_of_mul_eq_one_right (ideleV_mul_inv z v)).symm

/-- **The torus element** $d(z)\in SO(V)(\mathbb A)$ for an idele $z$ ($d(z)e = ze$). -/
def dA : SOAdele QC :=
  mkSOAdele QC (fun w => dGL (ideleR_ne z w)) (fun w => isSOAt_dGL _ _)
    (fun w => dGL (ideleC_ne z w)) (fun w => isSOAt_dGL _ _)
    (fun v => dGL (ideleV_ne z v)) (fun v => isSOAt_dGL _ _) (by
      filter_upwards [eventually_two, (z : Adeles F).2.2, (z⁻¹ : (Adeles F)ˣ).val.2.2] with v h2 h1 h1'
      have ha : Valued.v ((z : Adeles F).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1
      have ha' : Valued.v ((z : Adeles F).2 v)⁻¹ ≤ 1 := by
        rw [ideleV_inv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1'
      refine ⟨dM_mem_intMat v h2 ha ha', ?_⟩
      show dM ((z : Adeles F).2 v)⁻¹ ∈ intMat v
      exact dM_mem_intMat v h2 ha' (by rw [inv_inv]; exact ha))

@[simp] theorem matR_dA (w) : matR QC (dA (c₀ := c₀) (Q₀' := Q₀') z) w = dM ((z : Adeles F).1.1 w) := rfl

@[simp] theorem matC_dA (w) : matC QC (dA (c₀ := c₀) (Q₀' := Q₀') z) w = dM ((z : Adeles F).1.2 w) := rfl

@[simp] theorem matV_dA (v) : matV QC (dA (c₀ := c₀) (Q₀' := Q₀') z) v = dM ((z : Adeles F).2 v) := rfl

end Torus

/-! #### Relations -/

theorem adR_add {n : ℕ} (y y' : AdeleSpace F (Fin n)) (w) : adR (y + y') w = adR y w + adR y' w := rfl
theorem adC_add {n : ℕ} (y y' : AdeleSpace F (Fin n)) (w) : adC (y + y') w = adC y w + adC y' w := rfl
theorem adV_add {n : ℕ} (y y' : AdeleSpace F (Fin n)) (v) : adV (y + y') v = adV y v + adV y' v := rfl

theorem adR_units_smul {n : ℕ} (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) (w) :
    adR (z • y) w = (z : Adeles F).1.1 w • adR y w := rfl
theorem adC_units_smul {n : ℕ} (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) (w) :
    adC (z • y) w = (z : Adeles F).1.2 w • adC y w := rfl
theorem adV_units_smul {n : ℕ} (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin n)) (v) :
    adV (z • y) v = (z : Adeles F).2 v • adV y v := rfl

/-- $n(w + w') = n(w)\,n(w')$. -/
theorem coneN_add (y y' : AdeleSpace F (Fin k)) : coneN hc hQ' (y + y') = coneN hc hQ' y * coneN hc hQ' y' :=
  SOAdele.ext_mat (fun w => by rw [matR_mul, matR_coneN, matR_coneN, matR_coneN, adR_add, nM_mul _ _ (cAt_ne_zero hc _)])
    (fun w => by rw [matC_mul, matC_coneN, matC_coneN, matC_coneN, adC_add, nM_mul _ _ (cAt_ne_zero hc _)])
    (fun v => by rw [matV_mul, matV_coneN, matV_coneN, matV_coneN, adV_add, nM_mul _ _ (cAt_ne_zero hc _)])

/-- **The Levi factor normalizes $N$**: $\mathrm{diag}(1,1,h)\,n(w) = n(hw)\,\mathrm{diag}(1,1,h)$. -/
theorem hA_mul_coneN (h : SOAdele Q₀') (y : AdeleSpace F (Fin k)) :
    hA h * coneN hc hQ' y = coneN hc hQ' (h • y) * hA h := by
  refine SOAdele.ext_mat (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [matR_mul, matR_mul, matR_hA, matR_coneN, matR_coneN, smul_apply_fst_fst]
    have hh := (isSOAt_R h w).1
    rw [hesAt_base] at hh
    exact mM_mul_nM _ _ hh _
  · rw [matC_mul, matC_mul, matC_hA, matC_coneN, matC_coneN, smul_apply_fst_snd]
    have hh := (isSOAt_C h w).1
    rw [hesAt_base] at hh
    exact mM_mul_nM _ _ hh _
  · rw [matV_mul, matV_mul, matV_hA, matV_coneN, matV_coneN, smul_apply_snd]
    have hh := (isSOAt_V h v).1
    rw [hesAt_base] at hh
    exact mM_mul_nM _ _ hh _

/-- **Conjugation by the torus**: $d(z)\,n(w) = n(zw)\,d(z)$. -/
theorem dA_mul_coneN (z : (Adeles F)ˣ) (y : AdeleSpace F (Fin k)) :
    dA z * coneN hc hQ' y = coneN hc hQ' (z • y) * dA z := by
  refine SOAdele.ext_mat (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [matR_mul, matR_mul, matR_dA, matR_coneN, matR_coneN, adR_units_smul]
    exact dM_mul_nM _ _ (cAt_ne_zero hc _) (ideleR_ne z w) _
  · rw [matC_mul, matC_mul, matC_dA, matC_coneN, matC_coneN, adC_units_smul]
    exact dM_mul_nM _ _ (cAt_ne_zero hc _) (ideleC_ne z w) _
  · rw [matV_mul, matV_mul, matV_dA, matV_coneN, matV_coneN, adV_units_smul]
    exact dM_mul_nM _ _ (cAt_ne_zero hc _) (ideleV_ne z v) _

/-- $\mathrm{diag}(1,1,h)$ commutes with $d(z)$. -/
theorem hA_mul_dA (h : SOAdele Q₀') (z : (Adeles F)ˣ) :
    hA (c₀ := c₀) h * dA z = dA z * hA h :=
  SOAdele.ext_mat (fun w => by rw [matR_mul, matR_mul, matR_hA, matR_dA, mM_mul_dM])
    (fun w => by rw [matC_mul, matC_mul, matC_hA, matC_dA, mM_mul_dM])
    (fun v => by rw [matV_mul, matV_mul, matV_hA, matV_dA, mM_mul_dM])

/-! #### Action on the isotropic vector $e = e_0 + e_1$ -/

/-- $e$ as an adelic vector. -/
abbrev eA (F : Type) [Field F] [NumberField F] (k : ℕ) : AdeleSpace F (Fin (k + 1 + 1)) :=
  diagVec F (Fin (k + 1 + 1)) eV

theorem map_eV {K : Type*} [Field K] (σ : F →+* K) :
    (fun j => σ ((eV : Fin (k + 1 + 1) → F) j)) = (eV : Fin (k + 1 + 1) → K) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> simp [eV, v3]

theorem adR_eA (w : {w : InfinitePlace F // w.IsReal}) : adR (eA F k) w = eV := by
  rw [← map_eV (σR w)]; rfl

theorem adC_eA (w : {w : InfinitePlace F // w.IsComplex}) : adC (eA F k) w = eV := by
  rw [← map_eV (σC w)]; rfl

theorem adV_eA (v : HeightOneSpectrum (𝓞 F)) : adV (eA F k) v = eV := by
  rw [← map_eV (σV v)]; rfl

theorem coneN_smul_eA (y : AdeleSpace F (Fin k)) : coneN hc hQ' y • eA F k = eA F k :=
  adeleSpace_ext (fun w => by rw [smul_apply_fst_fst, matR_coneN, adR_eA, nM_mulVec_eV])
    (fun w => by rw [smul_apply_fst_snd, matC_coneN, adC_eA, nM_mulVec_eV])
    (fun v => by rw [smul_apply_snd, matV_coneN, adV_eA, nM_mulVec_eV])

theorem hA_smul_eA (h : SOAdele Q₀') : hA (c₀ := c₀) h • eA F k = eA F k :=
  adeleSpace_ext (fun w => by rw [smul_apply_fst_fst, matR_hA, adR_eA, mM_mulVec_eV])
    (fun w => by rw [smul_apply_fst_snd, matC_hA, adC_eA, mM_mulVec_eV])
    (fun v => by rw [smul_apply_snd, matV_hA, adV_eA, mM_mulVec_eV])

theorem dA_smul_eA (z : (Adeles F)ˣ) : dA (c₀ := c₀) (Q₀' := Q₀') z • eA F k = z • eA F k :=
  adeleSpace_ext (fun w => by rw [smul_apply_fst_fst, matR_dA, adR_eA, dM_mulVec_eV (ideleR_ne z w),
      adR_units_smul, adR_eA])
    (fun w => by rw [smul_apply_fst_snd, matC_dA, adC_eA, dM_mulVec_eV (ideleC_ne z w), adC_units_smul, adC_eA])
    (fun v => by rw [smul_apply_snd, matV_dA, adV_eA, dM_mulVec_eV (ideleV_ne z v), adV_units_smul, adV_eA])

end Adelic

end QuadFormsKB.Tamagawa.Measure.Weil

end
