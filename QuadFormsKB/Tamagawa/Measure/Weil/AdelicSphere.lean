import QuadFormsKB.Tamagawa.Measure.Weil.SphereComplement
import QuadFormsKB.Tamagawa.Measure.Weil.SphereQuotient
import QuadFormsKB.Tamagawa.Measure.Weil.SphericalUnfoldAdelic

/-!
# The adelic sphere $T(\rho)_{\mathbb A}$, its section and the stabilizer embedding

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $N = k + 1$ variables (any signature), $H$ its Hessian,
$\rho\in F^\times$ represented over $F$ by $\xi$ (`RatSphere Q₀ ρ`). Fix (`AdelicSphereSetup`) the base point $\xi$, an
integral complement $G = [d\xi\mid G']$ with $Q_0\circ G = \langle m_0\rangle\perp Q'$ (`SphereComplement`), and $w\perp\xi$ with
$q(w)\ne0$ ($q(x) = x^{\mathsf T}Hx = 2Q_0(x)$).

* **The adelic sphere** `adelicSphere Q₀ ρ` $=\{y\in\mathbb A^N : q(y_v) = 2\rho \text{ at every place } v\}$.
* **The section** `sphereSection` $s : T(\rho)_{\mathbb A}\to SO(V)(\mathbb A)$, $s(y)\xi = y$: at the infinite places the
  two-reflection section; at a finite place the same reflections with the branch chosen by absolute values
  ($|q(y + \xi)|_v\ge|q(y - \xi)|_v$), which is integral at every place where $\xi, w$ are integral, $2q(\xi)$, $q(w)$ are units
  and $\det G$ is a unit — so $s(y)$ lies in the restricted product.
* **The stabilizer embedding** `sphereIota` $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$, $h\mapsto G\,\mathrm{diag}(1, h)\,G^{-1}$
  at every place.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- The real place $w$ as an embedding. -/
abbrev σR (w : {w : InfinitePlace F // w.IsReal}) : F →+* ℝ := embedding_of_isReal w.2

/-- The complex place $w$ as an embedding. -/
abbrev σC (w : {w : InfinitePlace F // w.IsComplex}) : F →+* ℂ := w.1.embedding

/-- The finite place $v$ as an embedding. -/
abbrev σV (v : HeightOneSpectrum (𝓞 F)) : F →+* v.adicCompletion F := algebraMap F (v.adicCompletion F)

/-! ### Hessians at the places -/

section Hess

variable {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- The Hessian of $Q_0$ at an embedding $\sigma : F\to K$. -/
abbrev hesAt {K : Type*} [CommRing K] (σ : F →+* K) : Matrix (Fin n) (Fin n) K := (QF).hessian.map σ

theorem hesAt_transpose {K : Type*} [CommRing K] (σ : F →+* K) : (hesAt Q₀ σ)ᵀ = hesAt Q₀ σ := by
  rw [hesAt, ← transpose_map, hessian_transpose Q₀]

theorem mem_soReal_of (σ : F →+* ℝ) {g : GL (Fin n) ℝ}
    (h1 : g.valᵀ * hesAt Q₀ σ * g.val = hesAt Q₀ σ) (h2 : g.val.det = 1) : g ∈ soReal ((QF).map σ) := by
  rw [mem_soReal_iff, Siegel.hessian_map_NF]; exact ⟨h1, h2⟩

theorem mem_soC_of (σ : F →+* ℂ) {g : GL (Fin n) ℂ}
    (h1 : g.valᵀ * hesAt Q₀ σ * g.val = hesAt Q₀ σ) (h2 : g.val.det = 1) : g ∈ soC ((QF).map σ) := by
  rw [mem_soC_iff, gramC, Siegel.hessian_map_NF, Matrix.mul_smul, Matrix.smul_mul, h1]; exact ⟨rfl, h2⟩

theorem mem_orthGroup_of (v : HeightOneSpectrum (𝓞 F)) {g : GL (Fin n) (v.adicCompletion F)}
    (h1 : g.valᵀ * hesAt Q₀ (algebraMap F (v.adicCompletion F)) * g.val =
      hesAt Q₀ (algebraMap F (v.adicCompletion F))) : g ∈ orthGroup QF (v.adicCompletion F) :=
  (mem_orthGroup QF).mpr h1

/-- $q_\sigma(\sigma\circ x) = \sigma(q(x))$. -/
theorem qH_hesAt_map {K : Type*} [Field K] (σ : F →+* K) (x : Fin n → F) :
    qH (hesAt Q₀ σ) (fun i => σ (x i)) = σ (qH (QF).hessian x) := by
  simp only [qH, hesAt, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]

theorem bH_hesAt_map {K : Type*} [Field K] (σ : F →+* K) (x y : Fin n → F) :
    bH (hesAt Q₀ σ) (fun i => σ (x i)) (fun i => σ (y i)) = σ (bH (QF).hessian x y) := by
  simp only [bH, hesAt, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]

end Hess

/-! ### Conjugated blocks in $GL$ -/

section ConjGL

variable {K : Type*} [Field K]

/-- $h\mapsto P\,\mathrm{diag}(1, h)\,P^{-1}$ on $GL$. -/
def conjBlockGL (P : GL (Fin (k + 1)) K) : GL (Fin k) K →* GL (Fin (k + 1)) K :=
  (MulAut.conj P).toMonoidHom.comp blockGL

theorem conjBlockGL_val (P : GL (Fin (k + 1)) K) (h : GL (Fin k) K) :
    (conjBlockGL P h : Matrix (Fin (k + 1)) (Fin (k + 1)) K) = conjBlock P.val h.val := by
  simp [conjBlockGL, conjBlock, MulAut.conj_apply, Matrix.coe_units_inv]

theorem conjBlockGL_injective (P : GL (Fin (k + 1)) K) : Function.Injective (conjBlockGL P) := by
  intro h h' e
  have e' := congrArg (fun g : GL (Fin (k + 1)) K => (P⁻¹ * g * P : GL (Fin (k + 1)) K)) e
  simp only [conjBlockGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply] at e'
  have e'' : blockGL h = blockGL h' := by simpa [mul_assoc] using e'
  ext i j
  have := congrArg (fun g : GL (Fin (k + 1)) K => g.val i.succ j.succ) e''
  simpa using this

end ConjGL

/-! ### Integral matrices at the finite places -/

section IntMat

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem mul_mem_intMat {A B : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intMat v) (hB : B ∈ intMat v) :
    A * B ∈ intMat v := fun i j => by
  rw [mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA i l) (hB l j)

theorem cornerMat_mem_intMat {A : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intMat v) :
    cornerMat (1 : Fv) A ∈ intMat v := fun i j => by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp
  · simp
  · simpa using hA i j

theorem mem_glInt_iff {g : GL (Fin n) Fv} : g ∈ glInt v ↔ g.val ∈ intMat v ∧ (g⁻¹ : GL (Fin n) Fv).val ∈ intMat v := by
  rw [glInt_eq]; simp [Units.embedProduct_apply]

theorem eventually_valued_le_one (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (v.adicCompletion F) x) ≤ 1 := by
  filter_upwards [eventually_valuation_le_one (F := F) x] with v hv
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans_le hv

/-- An $F$-matrix is integral at almost every place. -/
theorem eventually_map_mem_intMat (M : Matrix (Fin n) (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, M.map (algebraMap F (v.adicCompletion F)) ∈ intMat v := by
  have : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (algebraMap F (v.adicCompletion F) (M i j)) ≤ 1 := fun i j => eventually_valued_le_one (M i j)
  filter_upwards [Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (this i)] with v hv i j
  exact hv i j

end IntMat

section IntRefl

theorem sph_valued_int_le_one (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := by
  rw [← IsScalarTower.algebraMap_apply]
  exact valued_int_le_one v a

theorem sph_eventually_valued_eq_one {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  filter_upwards [eventually_valuation_le_one (F := F) x, eventually_valuation_le_one (F := F) x⁻¹] with v h1 h2
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := by simpa using hx
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans
    (le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2))

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- Integral vectors: all coordinates in $\mathfrak o_v$. -/
def IntVec (x : Fin n → v.adicCompletion F) : Prop := ∀ i, Valued.v (x i) ≤ 1

theorem IntVec.add {x y : Fin n → Fv} (hx : IntVec v x) (hy : IntVec v y) : IntVec v (x + y) := fun i =>
  (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))

theorem IntVec.sub {x y : Fin n → Fv} (hx : IntVec v x) (hy : IntVec v y) : IntVec v (x - y) := fun i =>
  (Valuation.map_sub _ _ _).trans (max_le (hx i) (hy i))

theorem IntVec.mulVec {A : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intMat v) {x : Fin n → Fv} (hx : IntVec v x) :
    IntVec v (A *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA i l) (hx l)

theorem qH_le_one {H : Matrix (Fin n) (Fin n) Fv} (hH : H ∈ intMat v) {x : Fin n → Fv} (hx : IntVec v x) :
    Valued.v (qH H x) ≤ 1 := by
  simp only [qH, dotProduct]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hx l) (hx.mulVec v hH l)

theorem valued_two_le_one : Valued.v (2 : Fv) ≤ 1 := by
  have := valued_int_le_one v (2 : 𝓞 F); rwa [map_ofNat] at this

/-- **An integral reflection**: $\tau_u$ is integral if $u$ and $H$ are and $q(u)$ is a unit. -/
theorem refl_mem_intMat {H : Matrix (Fin n) (Fin n) Fv} (hH : H ∈ intMat v) {u : Fin n → Fv} (hu : IntVec v u)
    (hq : Valued.v (qH H u) = 1) : refl H u ∈ intMat v := fun i j => by
  have h1 : Valued.v ((1 : Matrix (Fin n) (Fin n) Fv) i j) ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : Valued.v (2 / qH H u) ≤ 1 := by
    rw [map_div₀, hq, div_one]; exact valued_two_le_one v
  simp only [refl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  refine (Valuation.map_sub _ _ _).trans (max_le h1 ?_)
  rw [Valuation.map_mul, Valuation.map_mul]
  exact mul_le_one' h2 (mul_le_one' (hu i) (hu.mulVec v hH j))

theorem hesAt_mem_intMat (Q : QuadForm (𝓞 F) n) : hesAt Q (algebraMap F Fv) ∈ intMat v := fun i j => by
  rw [hesAt, Matrix.map_apply, Siegel.hessian_map_NF, Matrix.map_apply]
  exact sph_valued_int_le_one v _

end IntRefl

/-! ### The adelic sphere -/

section Sphere

variable {n : ℕ}

/-- The component of $y\in\mathbb A^n$ at a real place. -/
def adR (y : AdeleSpace F (Fin n)) (w : {w : InfinitePlace F // w.IsReal}) : Fin n → ℝ := fun j => (y j).1.1 w

/-- The component at a complex place. -/
def adC (y : AdeleSpace F (Fin n)) (w : {w : InfinitePlace F // w.IsComplex}) : Fin n → ℂ := fun j => (y j).1.2 w

/-- The component at a finite place. -/
def adV (y : AdeleSpace F (Fin n)) (v : HeightOneSpectrum (𝓞 F)) : Fin n → v.adicCompletion F := fun j => (y j).2 v

/-- **The adelic sphere** $T(\rho)_{\mathbb A} = \{y\in\mathbb A^n : q(y_v) = 2\rho$ at every place$\}$
($q = x^{\mathsf T}Hx = 2Q_0$). -/
@[kb "weil1982" "§4.5, p. 109 (the adelic sphere T(ρ)_A) [unverified page]"]
def adelicSphere (Q₀ : QuadForm (𝓞 F) n) (ρ : F) : Set (AdeleSpace F (Fin n)) :=
  {y | (∀ w, qH (hesAt Q₀ (σR w)) (adR y w) = σR w (2 * ρ)) ∧ (∀ w, qH (hesAt Q₀ (σC w)) (adC y w) = σC w (2 * ρ)) ∧
    ∀ v, qH (hesAt Q₀ (σV v)) (adV y v) = σV v (2 * ρ)}

theorem eventually_intVec (y : AdeleSpace F (Fin n)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, IntVec v (adV y v) := by
  filter_upwards [Filter.eventually_all.mpr fun j => (y j).2.2] with v hv j
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hv j)

end Sphere

/-! ### The setup -/

/-- **Data for the adelic sphere $T(\rho)$**: the base point $\xi$, an integral complement of $\xi$ and an auxiliary vector
$w\perp\xi$ with $q(w)\ne0$. Fields: `ξ`, `C`, `w`, `hw`, `horth`. -/
structure AdelicSphereSetup (Q₀ : QuadForm (𝓞 F) (k + 1)) (ρ : F) where
  /-- The base point. -/
  ξ : RatSphere Q₀ ρ
  /-- The integral complement. -/
  C : SphereComplement Q₀ ξ.1
  /-- The auxiliary vector. -/
  w : Fin (k + 1) → F
  hw : qH (Q₀.map (algebraMap (𝓞 F) F)).hessian w ≠ 0
  horth : bH (Q₀.map (algebraMap (𝓞 F) F)).hessian w ξ.1 = 0

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem exists_adelicSphereSetup (hQ : Q₀.Nondegenerate) (hρ : ρ ≠ 0) (ξ : RatSphere Q₀ ρ) (hk : 1 ≤ k) :
    Nonempty (AdelicSphereSetup Q₀ ρ) := by
  have hξ : qF Q₀ ξ.1 ≠ 0 := by rw [ξ.2]; exact hρ
  obtain ⟨C⟩ := exists_sphereComplement Q₀ hQ ξ.1 hξ
  have hdet : (QF).hessian.det ≠ 0 := by
    rw [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ
  have hx₀ : qH (QF).hessian ξ.1 ≠ 0 := by rw [qH_hessian]; exact mul_ne_zero two_ne_zero hξ
  obtain ⟨w, hw, horth⟩ := exists_orth_anisotropic (H := (QF).hessian) (hessian_transpose Q₀) two_ne_zero hdet
    (by omega) hx₀
  exact ⟨⟨ξ, C, w, hw, horth⟩⟩

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ)

theorem qH_ξ : qH (QF).hessian S.ξ.1 = 2 * ρ := by rw [qH_hessian, S.ξ.2]

/-- The sphere data over $F$. -/
def sphereDataF (hρ : ρ ≠ 0) : SphereData (QF).hessian :=
  ⟨S.ξ.1, S.w, by rw [S.qH_ξ]; exact mul_ne_zero two_ne_zero hρ, S.hw, S.horth⟩

/-- The sphere data at an embedding $\sigma : F\to K$ into a field. -/
def sphereDataAt (hρ : ρ ≠ 0) {K : Type*} [Field K] (σ : F →+* K) : SphereData (hesAt Q₀ σ) where
  x₀ := fun i => σ (S.ξ.1 i)
  w := fun i => σ (S.w i)
  hx₀ := by
    rw [qH_hesAt_map, (map_ne_zero σ)]; exact (S.sphereDataF hρ).hx₀
  hw := by rw [qH_hesAt_map, (map_ne_zero σ)]; exact S.hw
  horth := by rw [bH_hesAt_map, S.horth, map_zero]

theorem qH_sphereDataAt (hρ : ρ ≠ 0) {K : Type*} [Field K] (σ : F →+* K) :
    qH (hesAt Q₀ σ) (S.sphereDataAt hρ σ).x₀ = σ (2 * ρ) := by
  rw [sphereDataAt, qH_hesAt_map, S.qH_ξ]

/-- The complement matrix $G$ at $\sigma$, as an element of $GL_N(K)$. -/
def PAt {K : Type*} [Field K] (σ : F →+* K) : GL (Fin (k + 1)) K :=
  Matrix.GeneralLinearGroup.map σ (LatChange.glF S.C.G S.C.hG)

theorem PAt_val {K : Type*} [Field K] (σ : F →+* K) :
    (S.PAt σ).val = (S.C.G.map (algebraMap (𝓞 F) F)).map σ := rfl

/-- **The splitting at every place**: $G^{\mathsf T}HG = \mathrm{diag}(2m_0, H')$. -/
theorem PAt_hes {K : Type*} [Field K] (σ : F →+* K) :
    (S.PAt σ).valᵀ * hesAt Q₀ σ * (S.PAt σ).val =
      cornerMat (σ (algebraMap (𝓞 F) F (2 * S.C.m₀))) (hesAt S.C.Q' σ) := by
  have h := congrArg QuadForm.hessian S.C.split
  rw [QuadForm.hessian_compMat, hessian_splitForm] at h
  have h' := congrArg (fun M => (M.map (algebraMap (𝓞 F) F)).map σ) h
  simp only [Matrix.map_mul, transpose_map, cornerMat_map] at h'
  rw [PAt_val, hesAt, hesAt, Siegel.hessian_map_NF, Siegel.hessian_map_NF]
  exact h'

/-- The first column: $Ge_0 = d\xi$. -/
theorem PAt_mulVec_e0 {K : Type*} [Field K] (σ : F →+* K) :
    (S.PAt σ).val *ᵥ (e0 : Fin (k + 1) → K) = σ (algebraMap (𝓞 F) F S.C.d) • fun i => σ (S.ξ.1 i) := by
  ext i
  rw [PAt_val]
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  rw [S.C.col i, map_mul]

theorem isUnit_det_PAt {K : Type*} [Field K] (σ : F →+* K) : IsUnit (S.PAt σ).val.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (S.PAt σ).isUnit

/-! ### The stabilizer embedding at each place -/

section Iota

/-- **The isometry condition is preserved**: for $h$ an isometry of $H'_\sigma$ with $\det h = 1$, the conjugated block
$G\,\mathrm{diag}(1, h)\,G^{-1}$ is an isometry of $H_\sigma$ with determinant $1$. -/
theorem conj_mem {K : Type*} [Field K] (σ : F →+* K) {h : GL (Fin k) K}
    (h1 : h.valᵀ * hesAt S.C.Q' σ * h.val = hesAt S.C.Q' σ) :
    (conjBlockGL (S.PAt σ) h).valᵀ * hesAt Q₀ σ * (conjBlockGL (S.PAt σ) h).val = hesAt Q₀ σ ∧
      (conjBlockGL (S.PAt σ) h).val.det = h.val.det := by
  rw [conjBlockGL_val]
  exact ⟨conjBlock_orth (S.isUnit_det_PAt σ) (S.PAt_hes σ) h1, det_conjBlock (S.isUnit_det_PAt σ) _⟩

theorem hes_of_mem_soReal {n : ℕ} (Q : QuadForm (𝓞 F) n) (σ : F →+* ℝ) {g : GL (Fin n) ℝ}
    (hg : g ∈ soReal ((Q.map (algebraMap (𝓞 F) F)).map σ)) :
    g.valᵀ * hesAt Q σ * g.val = hesAt Q σ ∧ g.val.det = 1 := by
  rw [mem_soReal_iff, Siegel.hessian_map_NF] at hg; exact hg

theorem hes_of_mem_soC {n : ℕ} (Q : QuadForm (𝓞 F) n) (σ : F →+* ℂ) {g : GL (Fin n) ℂ}
    (hg : g ∈ soC ((Q.map (algebraMap (𝓞 F) F)).map σ)) :
    g.valᵀ * hesAt Q σ * g.val = hesAt Q σ ∧ g.val.det = 1 := by
  rw [mem_soC_iff, gramC, Siegel.hessian_map_NF, Matrix.mul_smul, Matrix.smul_mul] at hg
  refine ⟨?_, hg.2⟩
  have h := congrArg (fun M => (2 : ℂ) • M) hg.1
  simpa [smul_smul] using h

/-- **The embedding at a real place.** -/
def iotaR (w : {w : InfinitePlace F // w.IsReal}) : ArchSO (QRe S.C.Q' w) →* ArchSO (QRe Q₀ w) :=
  ((conjBlockGL (S.PAt (σR w))).comp (soReal (QRe S.C.Q' w)).subtype).codRestrict (soReal (QRe Q₀ w)) fun h => by
    have hh := hes_of_mem_soReal S.C.Q' (σR w) h.2
    have hc := S.conj_mem (σR w) hh.1
    exact mem_soReal_of Q₀ (σR w) hc.1 (hc.2.trans hh.2)

/-- **The embedding at a complex place.** -/
def iotaC (w : {w : InfinitePlace F // w.IsComplex}) : ArchSOC (QCx S.C.Q' w) →* ArchSOC (QCx Q₀ w) :=
  ((conjBlockGL (S.PAt (σC w))).comp (soC (QCx S.C.Q' w)).subtype).codRestrict (soC (QCx Q₀ w)) fun h => by
    have hh := hes_of_mem_soC S.C.Q' (σC w) h.2
    have hc := S.conj_mem (σC w) hh.1
    exact mem_soC_of Q₀ (σC w) hc.1 (hc.2.trans hh.2)

/-- **The embedding at a finite place** (on the orthogonal groups). -/
def iotaV (v : HeightOneSpectrum (𝓞 F)) :
    orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) →* orthGroup QF (v.adicCompletion F) :=
  ((conjBlockGL (S.PAt (σV v))).comp (orthGroup _ _).subtype).codRestrict (orthGroup QF (v.adicCompletion F))
    fun h => by
      have hh : (h : GL (Fin k) (v.adicCompletion F)).valᵀ * hesAt S.C.Q' (σV v) * (h : GL _ _).val =
          hesAt S.C.Q' (σV v) := (mem_orthGroup _).mp h.2
      exact mem_orthGroup_of Q₀ v (S.conj_mem (σV v) hh).1

theorem iotaV_val (v : HeightOneSpectrum (𝓞 F)) (h) :
    ((S.iotaV v h : orthGroup QF (v.adicCompletion F)) : GL (Fin (k + 1)) (v.adicCompletion F)).val =
      conjBlock (S.PAt (σV v)).val (h : GL (Fin k) (v.adicCompletion F)).val :=
  conjBlockGL_val _ _

theorem det_iotaV (v : HeightOneSpectrum (𝓞 F)) (h) :
    ((S.iotaV v h : orthGroup QF (v.adicCompletion F)) : GL (Fin (k + 1)) (v.adicCompletion F)).val.det =
      (h : GL (Fin k) (v.adicCompletion F)).val.det := by
  rw [iotaV_val, det_conjBlock (S.isUnit_det_PAt _)]

end Iota

/-- **$G$ and $G^{-1}$ are integral at almost every place.** -/
theorem eventually_PAt_glInt :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, S.PAt (σV v) ∈ glInt v := by
  filter_upwards [eventually_map_mem_intMat (LatChange.glF S.C.G S.C.hG).val,
    eventually_map_mem_intMat (LatChange.glF S.C.G S.C.hG)⁻¹.val] with v h1 h2
  rw [mem_glInt_iff]
  exact ⟨h1, h2⟩

theorem iotaV_mem_stdStab {v : HeightOneSpectrum (𝓞 F)} (hP : S.PAt (σV v) ∈ glInt v)
    {h : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)}
    (hh : h ∈ stdStab (S.C.Q'.map (algebraMap (𝓞 F) F)) v) : S.iotaV v h ∈ stdStab QF v := by
  rw [mem_glInt_iff] at hP
  have hh' : (h : GL (Fin k) (v.adicCompletion F)) ∈ glInt v := hh
  rw [mem_glInt_iff] at hh'
  show ((S.iotaV v h : orthGroup QF (v.adicCompletion F)) : GL (Fin (k + 1)) (v.adicCompletion F)) ∈ glInt v
  rw [mem_glInt_iff]
  have hinv : ((S.iotaV v h : orthGroup QF (v.adicCompletion F))⁻¹ : orthGroup QF _) = S.iotaV v h⁻¹ :=
    (map_inv _ _).symm
  constructor
  · rw [iotaV_val, conjBlock, ← Matrix.coe_units_inv]
    exact mul_mem_intMat v (mul_mem_intMat v hP.1 (cornerMat_mem_intMat v hh'.1)) hP.2
  · rw [show (((S.iotaV v h : orthGroup QF (v.adicCompletion F)) : GL (Fin (k + 1)) (v.adicCompletion F))⁻¹ :
        GL (Fin (k + 1)) (v.adicCompletion F)) = ((S.iotaV v h⁻¹ : orthGroup QF _) : GL _ _) by
      rw [← hinv]; rfl, iotaV_val, conjBlock, ← Matrix.coe_units_inv]
    exact mul_mem_intMat v (mul_mem_intMat v hP.1 (cornerMat_mem_intMat v hh'.2)) hP.2

/-- **The embedding on $O(\,\cdot\,)(\mathbb A_f)$.** -/
def iotaOAf : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) →* OAf QF where
  toFun := RestrictedProduct.map (fun v => (S.iotaV v : _ → _)) (S.eventually_PAt_glInt.mono fun v hv _ hh =>
    S.iotaV_mem_stdStab hv hh)
  map_one' := RestrictedProduct.ext _ _ fun v => map_one (S.iotaV v)
  map_mul' a b := RestrictedProduct.ext _ _ fun v => map_mul (S.iotaV v) _ _

theorem iotaOAf_apply (g : OAf (S.C.Q'.map (algebraMap (𝓞 F) F))) (v : HeightOneSpectrum (𝓞 F)) :
    S.iotaOAf g v = S.iotaV v (g v) := rfl

/-- **The embedding on $SO(\,\cdot\,)(\mathbb A_f)$.** -/
def iotaFin : SOAf S.C.Q' →* SOAf Q₀ :=
  (S.iotaOAf.comp (soAf _).subtype).codRestrict (soAf QF) fun h v => by
    show ((S.iotaV v ((h : OAf _) v) : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)).val.det = 1
    rw [det_iotaV]; exact h.2 v

/-- **The stabilizer embedding** $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$, $h\mapsto G\,\mathrm{diag}(1, h)\,G^{-1}$. -/
def iota : SOAdele S.C.Q' →* SOAdele Q₀ :=
  MonoidHom.prodMap (MonoidHom.prodMap (MonoidHom.piMap S.iotaR) (MonoidHom.piMap S.iotaC)) S.iotaFin


/-! ### The section at each place -/

section Sec

variable (hρ : ρ ≠ 0)

theorem qH_eq_x₀ {K : Type*} [Field K] (σ : F →+* K) {x : Fin (k + 1) → K}
    (hx : qH (hesAt Q₀ σ) x = σ (2 * ρ)) : qH (hesAt Q₀ σ) x = qH (hesAt Q₀ σ) (S.sphereDataAt hρ σ).x₀ := by
  rw [hx, S.qH_sphereDataAt]

/-- The archimedean branch:$q(x + x_0)\ne0$. -/
def bArch {K : Type*} [Field K] (σ : F →+* K) (x : Fin (k + 1) → K) : Prop :=
  qH (hesAt Q₀ σ) (x + (S.sphereDataAt hρ σ).x₀) ≠ 0

/-- **The section at an archimedean place** (as an element of $GL_N$). -/
def secArchGL {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (σ : F →+* K) (x : Fin (k + 1) → K)
    (hx : qH (hesAt Q₀ σ) x = σ (2 * ρ)) : GL (Fin (k + 1)) K :=
  secGL (hesAt Q₀ σ) (hesAt_transpose Q₀ σ) (S.sphereDataAt hρ σ) (S.bArch hρ σ) x id
    (branch_ne _ (hesAt_transpose Q₀ σ) h2 _ (S.qH_eq_x₀ hρ σ hx))

theorem secArchGL_mem {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (σ : F →+* K) (x : Fin (k + 1) → K)
    (hx : qH (hesAt Q₀ σ) x = σ (2 * ρ)) :
    (S.secArchGL hρ h2 σ x hx).valᵀ * hesAt Q₀ σ * (S.secArchGL hρ h2 σ x hx).val = hesAt Q₀ σ ∧
      (S.secArchGL hρ h2 σ x hx).val.det = 1 :=
  secP_mem _ (hesAt_transpose Q₀ σ) _ _ id (branch_ne _ (hesAt_transpose Q₀ σ) h2 _ (S.qH_eq_x₀ hρ σ hx))

theorem secArchGL_mulVec {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (σ : F →+* K) (x : Fin (k + 1) → K)
    (hx : qH (hesAt Q₀ σ) x = σ (2 * ρ)) :
    (S.secArchGL hρ h2 σ x hx).val *ᵥ (S.sphereDataAt hρ σ).x₀ = x :=
  secP_mulVec _ (hesAt_transpose Q₀ σ) h2 _ _ (S.qH_eq_x₀ hρ σ hx) id
    (branch_ne _ (hesAt_transpose Q₀ σ) h2 _ (S.qH_eq_x₀ hρ σ hx))

/-- The finite-place branch: $|q(x - x_0)|_v\le|q(x + x_0)|_v$. -/
def bFin (v : HeightOneSpectrum (𝓞 F)) (x : Fin (k + 1) → v.adicCompletion F) : Prop :=
  Valued.v (qH (hesAt Q₀ (σV v)) (x - (S.sphereDataAt hρ (σV v)).x₀)) ≤
    Valued.v (qH (hesAt Q₀ (σV v)) (x + (S.sphereDataAt hρ (σV v)).x₀))

theorem bFin_ne (v : HeightOneSpectrum (𝓞 F)) {x : Fin (k + 1) → v.adicCompletion F}
    (hx : qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ)) :
    S.bFin hρ v x → qH (hesAt Q₀ (σV v)) (x + (S.sphereDataAt hρ (σV v)).x₀) ≠ 0 := by
  intro hb h0
  rw [bFin, h0, map_zero, le_zero_iff, map_eq_zero] at hb
  have hs := qH_add_add_qH_sub (hesAt Q₀ (σV v)) (hesAt_transpose Q₀ (σV v)) (S.qH_eq_x₀ hρ (σV v) hx)
  rw [h0, hb, add_zero] at hs
  have h4 : (4 : v.adicCompletion F) ≠ 0 := by
    have : (4 : v.adicCompletion F) = algebraMap F _ 4 := (map_ofNat _ 4).symm
    rw [this, map_ne_zero]; norm_num
  exact (S.sphereDataAt hρ (σV v)).hx₀ ((mul_eq_zero.mp hs.symm).resolve_left h4)

theorem bFin_ne' (v : HeightOneSpectrum (𝓞 F)) {x : Fin (k + 1) → v.adicCompletion F} :
    ¬ S.bFin hρ v x → qH (hesAt Q₀ (σV v)) (x - (S.sphereDataAt hρ (σV v)).x₀) ≠ 0 := by
  intro hb h0
  apply hb
  rw [bFin, h0, map_zero]
  exact zero_le

/-- **The section at a finite place** (as an element of $GL_N(F_v)$). -/
def secFinGL (v : HeightOneSpectrum (𝓞 F)) (x : Fin (k + 1) → v.adicCompletion F)
    (hx : qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ)) : GL (Fin (k + 1)) (v.adicCompletion F) :=
  secGL (hesAt Q₀ (σV v)) (hesAt_transpose Q₀ (σV v)) (S.sphereDataAt hρ (σV v)) (S.bFin hρ v) x
    (S.bFin_ne hρ v hx) (S.bFin_ne' hρ v)

theorem secFinGL_mem (v : HeightOneSpectrum (𝓞 F)) (x : Fin (k + 1) → v.adicCompletion F)
    (hx : qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ)) :
    (S.secFinGL hρ v x hx).valᵀ * hesAt Q₀ (σV v) * (S.secFinGL hρ v x hx).val = hesAt Q₀ (σV v) ∧
      (S.secFinGL hρ v x hx).val.det = 1 :=
  secP_mem _ (hesAt_transpose Q₀ (σV v)) _ _ (S.bFin_ne hρ v hx) (S.bFin_ne' hρ v)

theorem secFinGL_mulVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin (k + 1) → v.adicCompletion F)
    (hx : qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ)) :
    (S.secFinGL hρ v x hx).val *ᵥ (S.sphereDataAt hρ (σV v)).x₀ = x :=
  secP_mulVec _ (hesAt_transpose Q₀ (σV v)) (by
    have : (2 : v.adicCompletion F) = algebraMap F _ 2 := (map_ofNat _ 2).symm
    rw [this, map_ne_zero]; norm_num) _ _ (S.qH_eq_x₀ hρ (σV v) hx) (S.bFin_ne hρ v hx) (S.bFin_ne' hρ v)

end Sec

/-- **Good finite places**: $\xi, w$ integral and $4q(\xi)$, $q(w)$ units. -/
def GoodV (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Valued.v (σV v (4 * qH (QF).hessian S.ξ.1)) = 1 ∧ Valued.v (σV v (qH (QF).hessian S.w)) = 1 ∧
    (∀ i, Valued.v (σV v (S.ξ.1 i)) ≤ 1) ∧ (∀ i, Valued.v (σV v (S.w i)) ≤ 1)

theorem eventually_goodV (hρ : ρ ≠ 0) : ∀ᶠ v in Filter.cofinite, S.GoodV v := by
  have h4 : 4 * qH (QF).hessian S.ξ.1 ≠ 0 := mul_ne_zero (by norm_num) (S.sphereDataF hρ).hx₀
  filter_upwards [sph_eventually_valued_eq_one h4, sph_eventually_valued_eq_one S.hw,
    Filter.eventually_all.mpr fun i => eventually_valued_le_one (S.ξ.1 i),
    Filter.eventually_all.mpr fun i => eventually_valued_le_one (S.w i)] with v h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **The finite section is integral at good places** on integral points of the sphere. -/
theorem secFinGL_mem_glInt (hρ : ρ ≠ 0) {v : HeightOneSpectrum (𝓞 F)} (hv : S.GoodV v) {x : Fin (k + 1) → v.adicCompletion F}
    (hxi : IntVec v x) (hx : qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ)) : S.secFinGL hρ v x hx ∈ glInt v := by
  classical
  set H := hesAt Q₀ (σV v)
  set D := S.sphereDataAt hρ (σV v)
  have hH := hesAt_mem_intMat v Q₀
  have hx₀ : IntVec v D.x₀ := hv.2.2.1
  have hw : IntVec v D.w := hv.2.2.2
  have hqx₀ : Valued.v (4 * qH H D.x₀) = 1 := by
    have : 4 * qH H D.x₀ = σV v (4 * qH (QF).hessian S.ξ.1) := by
      rw [map_mul, map_ofNat]
      exact congrArg (4 * ·) (qH_hesAt_map Q₀ (σV v) S.ξ.1)
    rw [this]; exact hv.1
  have hqw : Valued.v (qH H D.w) = 1 := by
    rw [show qH H D.w = σV v (qH (QF).hessian S.w) from qH_hesAt_map Q₀ (σV v) S.w]; exact hv.2.1
  have hsum := qH_add_add_qH_sub H (hesAt_transpose Q₀ (σV v)) (S.qH_eq_x₀ hρ (σV v) hx)
  have hp := qH_le_one v hH (hxi.add v hx₀)
  have hm := qH_le_one v hH (hxi.sub v hx₀)
  have hmax : 1 ≤ max (Valued.v (qH H (x + D.x₀))) (Valued.v (qH H (x - D.x₀))) := by
    rw [← hqx₀, ← hsum]; exact Valuation.map_add _ _ _
  rw [mem_glInt_iff]
  show secP H D (S.bFin hρ v) x ∈ intMat v ∧ secPInv H D (S.bFin hρ v) x ∈ intMat v
  unfold secP secPInv
  by_cases hb : S.bFin hρ v x
  · have hu : Valued.v (qH H (x + D.x₀)) = 1 :=
      le_antisymm hp (by rwa [max_eq_left hb] at hmax)
    have hq0 : Valued.v (qH H D.x₀) = 1 := by
      have h4 : Valued.v (4 : v.adicCompletion F) ≤ 1 := by
        have := valued_int_le_one v (4 : 𝓞 F); rwa [map_ofNat] at this
      refine le_antisymm (qH_le_one v hH hx₀) ?_
      rw [← hqx₀, Valuation.map_mul]
      exact mul_le_of_le_one_left' h4
    rw [if_pos hb, if_pos hb]
    exact ⟨mul_mem_intMat v (refl_mem_intMat v hH (hxi.add v hx₀) hu) (refl_mem_intMat v hH hx₀ hq0),
      mul_mem_intMat v (refl_mem_intMat v hH hx₀ hq0) (refl_mem_intMat v hH (hxi.add v hx₀) hu)⟩
  · have hlt : Valued.v (qH H (x + D.x₀)) < Valued.v (qH H (x - D.x₀)) := lt_of_not_ge hb
    have hu : Valued.v (qH H (x - D.x₀)) = 1 :=
      le_antisymm hm (by rwa [max_eq_right hlt.le] at hmax)
    rw [if_neg hb, if_neg hb]
    exact ⟨mul_mem_intMat v (refl_mem_intMat v hH (hxi.sub v hx₀) hu) (refl_mem_intMat v hH hw hqw),
      mul_mem_intMat v (refl_mem_intMat v hH hw hqw) (refl_mem_intMat v hH (hxi.sub v hx₀) hu)⟩


/-! ### The adelic section -/

section AdelicSec

variable (hρ : ρ ≠ 0)

/-- The archimedean part of the section. -/
def secInf (y : adelicSphere Q₀ ρ) : GInfSO Q₀ :=
  (fun w => (⟨S.secArchGL hρ two_ne_zero (σR w) (adR y.1 w) (y.2.1 w),
      mem_soReal_of Q₀ (σR w) (S.secArchGL_mem hρ two_ne_zero _ _ _).1 (S.secArchGL_mem hρ two_ne_zero _ _ _).2⟩ :
        soReal (QRe Q₀ w)),
    fun w => (⟨S.secArchGL hρ two_ne_zero (σC w) (adC y.1 w) (y.2.2.1 w),
      mem_soC_of Q₀ (σC w) (S.secArchGL_mem hρ two_ne_zero _ _ _).1 (S.secArchGL_mem hρ two_ne_zero _ _ _).2⟩ :
        soC (QCx Q₀ w)))

/-- The finite part of the section, in $O(V)(\mathbb A_f)$. -/
def secOAf (y : adelicSphere Q₀ ρ) : OAf QF :=
  ⟨fun v => ⟨S.secFinGL hρ v (adV y.1 v) (y.2.2.2 v), mem_orthGroup_of Q₀ v (S.secFinGL_mem hρ v _ _).1⟩, by
    filter_upwards [S.eventually_goodV hρ, eventually_intVec y.1] with v hv hy
    exact S.secFinGL_mem_glInt hρ hv hy (y.2.2.2 v)⟩

/-- **The section** $s : T(\rho)_{\mathbb A}\to SO(V)(\mathbb A)$. -/
def sphereSection (y : adelicSphere Q₀ ρ) : SOAdele Q₀ :=
  (S.secInf hρ y, ⟨S.secOAf hρ y, fun v => (S.secFinGL_mem hρ v (adV y.1 v) (y.2.2.2 v)).2⟩)

/-- The base point as an adelic vector. -/
abbrev ξA : AdeleSpace F (Fin (k + 1)) := diagVec F (Fin (k + 1)) S.ξ.1

/-- **$s(y)\,\xi = y$.** -/
theorem sphereSection_smul (y : adelicSphere Q₀ ρ) : S.sphereSection hρ y • S.ξA = y.1 := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · exact congrFun (S.secArchGL_mulVec hρ two_ne_zero (σR w) (adR y.1 w) (y.2.1 w)) i
  · exact congrFun (S.secArchGL_mulVec hρ two_ne_zero (σC w) (adC y.1 w) (y.2.2.1 w)) i
  · apply Subtype.ext; funext v
    exact congrFun (S.secFinGL_mulVec hρ v (adV y.1 v) (y.2.2.2 v)) i

end AdelicSec

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
