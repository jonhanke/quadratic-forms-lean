import QuadFormsKB.Tamagawa.Measure.Weil.IdeleShell
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryReduce
import QuadFormsKB.Tamagawa.Measure.Weil.PDAdelic
import QuadFormsKB.LocalDensity.FormDensityHyperbolic

/-!
# Weil's τ for isotropic binary $V$: $SO(V)\cong\mathbb G_m$, the norm-one subgroup, the measure, τ

**Layer:** number fields. $F$ is a number field, $Q_0$ a nondegenerate binary quadratic form over $\mathcal O_F$ whose
extension $Q = Q_0\otimes F$ is **isotropic**: $Q(e) = 0$ for some $e\in F^2\setminus0$ (`IsIsoVec Q₀ e`). Then $V = F^2$ is
a hyperbolic plane up to scaling and $SO(V)\cong\mathbb G_m$, $g\mapsto$ the eigenvalue of $g$ on the isotropic line
$Fe$. Unlike the anisotropic case, $SO(V)(F)$ is not cocompact in $SO(V)(\mathbb A)$, and Weil's/Ono's Tamagawa number
is the volume of $SO(V)(F)\backslash SO(V)(\mathbb A)^1$.

**Defines**
* `IsIsoVec Q₀ e`, `IsotropicF Q₀` (conditions): $e\ne0$ is isotropic; $Q_0\otimes F$ is isotropic.
* `isoIdx e`, `eigVal ι e M`: the eigenvalue $(M\,\iota(e))_i/\iota(e_i)$ of a matrix $M$ over an $F$-field $K$
  (embedding $\iota : F\to K$) on the line $K\iota(e)$, $i$ = `isoIdx e` (an index with $e_i\ne0$).
* **`isoChar Q₀ hQ he`** $=\chi_e : SO(V)(\mathbb A)\to\mathbb A_F^\times$, the eigenvalue on the isotropic line at every
  place (real, complex, finite); a homomorphism by **`mulVec_eq_eigVal_smul`** ($SO(V)(K)$ preserves the isotropic line).
* **`SOAdeleOne Q₀ hQ he`** $= SO(V)(\mathbb A)^1 = \{g : \|\chi_e(g)\|_{\mathbb A} = 1\}$.
* **`muTamIso Q₀ hQ`** $=\rho_F^{-1}\cdot$`muTam Q₀ hQ lamV`: Weil's Tamagawa measure with the convergence factors
  $\lambda_v = 1-N(v)^{-1} = L_v(1,\mathbf 1)^{-1}$ of $\mathbb G_m$ and the global factor $\rho_F^{-1}$,
  $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$.
* `isoShellIco Q₀ hQ he α β` $=\{g : \alpha\le\log\|\chi_e(g)\|_{\mathbb A}<\beta\}$, `isoShell` $=$ `isoShellIco … 0 1`.
* **`tauIso Q₀ hQ he`** $=\operatorname{covol}(SO(V)(F), \mu^{\mathrm{iso}}_{\mathrm{Tam}}|_{\mathrm{isoShell}})$, and the target
  **`TauOneIsotropic Q₀ hQ`**: $\tau = 1$ for every isotropic vector.

**Proves (here)** the eigenvalue lemma, `isoChar_smul` (only the line matters), `isoChar_other_line` (the other
isotropic line gives $\chi_e^{-1}$, hence the same $SO(V)(\mathbb A)^1$ and the same shells up to the reflection
$t\mapsto -t$ of $\log\|\cdot\|$), `isotropicF_iff_isSquare` ($Q_0\otimes F$ isotropic iff $-\det H_{Q_0}$ is a square
in $F$), and the non-vacuity facts for the hyperbolic plane $x_0x_1$ (`DVR.hyperbolic`).
-/

open MeasureTheory Measure Set Topology Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Linear algebra: rotations of a nondegenerate plane preserve its isotropic lines -/

section LinearAlgebra

variable {K : Type*} [Field K]

/-- The $2\times2$ Gram identity $B(x,x)B(y,y) - B(x,y)^2 = \det A\cdot(x_0y_1 - x_1y_0)^2$, $B(x,y) = x^{\mathsf T}Ay$,
for a symmetric $A$. -/
theorem gram_identity_two (A : Matrix (Fin 2) (Fin 2) K) (hA : A 1 0 = A 0 1) (x y : Fin 2 → K) :
    (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) - (x ⬝ᵥ (A *ᵥ y)) ^ 2 =
      A.det * (x 0 * y 1 - x 1 * y 0) ^ 2 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.det_fin_two, hA]
  ring

/-- **A rotation of a nondegenerate plane preserves every isotropic line**, in coordinates: if $A$ is symmetric with
$\det A\ne0$, $M^{\mathsf T}AM = A$, $\det M = 1$ and $e^{\mathsf T}Ae = 0$, then $\det(e, Me) = 0$.
*Proof.* $\beta = B(e,Me)$ satisfies $\beta = B(Me, M^2e) = B(Me, (\operatorname{tr}M)Me - e) = -\beta$
(Cayley–Hamilton, $\det M = 1$), so $\beta = 0$; then the Gram identity gives $\det A\cdot\det(e,Me)^2 = 0$. -/
theorem det_mulVec_eq_zero_of_iso [NeZero (2 : K)] {A M : Matrix (Fin 2) (Fin 2) K} (hA : A 1 0 = A 0 1)
    (hdet : A.det ≠ 0) (hM : Mᵀ * A * M = A) (hM1 : M.det = 1) {e : Fin 2 → K} (hiso : e ⬝ᵥ (A *ᵥ e) = 0) :
    e 0 * (M *ᵥ e) 1 - e 1 * (M *ᵥ e) 0 = 0 := by
  set u := M *ᵥ e with hu
  -- B is preserved by M
  have hB : ∀ x y : Fin 2 → K, (M *ᵥ x) ⬝ᵥ (A *ᵥ (M *ᵥ y)) = x ⬝ᵥ (A *ᵥ y) := fun x y => by
    have h00 := congrFun (congrFun hM 0) 0
    have h01 := congrFun (congrFun hM 0) 1
    have h10 := congrFun (congrFun hM 1) 0
    have h11 := congrFun (congrFun hM 1) 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    simp only [dotProduct, mulVec, Fin.sum_univ_two]
    linear_combination x 0 * y 0 * h00 + x 0 * y 1 * h01 + x 1 * y 0 * h10 + x 1 * y 1 * h11
  -- B is symmetric
  have hsym : ∀ x y : Fin 2 → K, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := fun x y => by
    simp only [dotProduct, mulVec, Fin.sum_univ_two, hA]; ring
  -- Cayley–Hamilton
  have hCH : M *ᵥ u = (M 0 0 + M 1 1) • u - e := by
    have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← hM1, Matrix.det_fin_two]
    rw [hu]
    funext i
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]; linear_combination (-(e 0)) * hdet'
    · simp [mulVec, dotProduct, Fin.sum_univ_two]; linear_combination (-(e 1)) * hdet'
  have huu : u ⬝ᵥ (A *ᵥ u) = 0 := by rw [hu, hB, hiso]
  have hβ : e ⬝ᵥ (A *ᵥ u) = 0 := by
    have h1 : u ⬝ᵥ (A *ᵥ (M *ᵥ u)) = e ⬝ᵥ (A *ᵥ u) := by rw [hu, hB]
    rw [hCH, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, huu, smul_zero, zero_sub, hsym u e] at h1
    have h2 : (2 : K) * (e ⬝ᵥ (A *ᵥ u)) = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left (NeZero.ne 2)
  have hg := gram_identity_two A hA e u
  rw [hiso, huu, hβ] at hg
  have : A.det * (e 0 * u 1 - e 1 * u 0) ^ 2 = 0 := by rw [← hg]; ring
  exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp this).resolve_left hdet)

/-- From $\det(e, u) = 0$ and $e_i\ne0$: $u = (u_i/e_i)\,e$. -/
theorem eq_smul_of_det_eq_zero {e u : Fin 2 → K} (h : e 0 * u 1 - e 1 * u 0 = 0) {i : Fin 2} (hi : e i ≠ 0) :
    u = (u i / e i) • e := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp at hi ⊢ <;> field_simp <;>
    first | linear_combination h | linear_combination -h

end LinearAlgebra

/-! ### Isotropic vectors and the eigenvalue on an isotropic line -/

section Eigen

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 2)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$e$ is an isotropic vector** of $Q = Q_0\otimes F$: $e\ne0$ and $Q(e) = 0$ (a condition). -/
@[kb "omeara1963" "§42 (isotropic vectors, hyperbolic plane) [unverified]"]
def IsIsoVec (e : Fin 2 → F) : Prop := e ≠ 0 ∧ qF Q₀ e = 0

/-- **$Q_0\otimes F$ is isotropic** (a condition): it has an isotropic vector. -/
@[kb "omeara1963" "§42 (isotropic spaces) [unverified]"]
def IsotropicF : Prop := ∃ e : Fin 2 → F, IsIsoVec Q₀ e

/-- The index of a nonzero coordinate of $e$: $0$ if $e_0\ne0$, else $1$. -/
def isoIdx (e : Fin 2 → F) : Fin 2 := by classical exact if e 0 ≠ 0 then 0 else 1

theorem isoIdx_ne_zero {e : Fin 2 → F} (he : e ≠ 0) : e (isoIdx e) ≠ 0 := by
  classical
  unfold isoIdx
  by_cases h0 : e 0 ≠ 0
  · simp [h0]
  · simp only [h0, ite_false]
    intro h1
    apply he
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1

theorem isoIdx_smul {e : Fin 2 → F} {c : F} (hc : c ≠ 0) : isoIdx (c • e) = isoIdx e := by
  classical
  simp [isoIdx, hc]

/-- **The eigenvalue on the line $K\iota(e)$**: $(M\,\iota(e))_i/\iota(e_i)$, $i$ = `isoIdx e`, for a matrix $M$ over a field
$K$ with an embedding $\iota : F\to K$. -/
def eigVal {K : Type*} [Field K] (ι : F →+* K) (e : Fin 2 → F) (M : Matrix (Fin 2) (Fin 2) K) : K :=
  (M *ᵥ (ι ∘ e)) (isoIdx e) / ι (e (isoIdx e))

variable {Q₀}

theorem iso_dotProduct_hessian {K : Type*} [Field K] (ι : F →+* K) {e : Fin 2 → F} (he : IsIsoVec Q₀ e) :
    (ι ∘ e) ⬝ᵥ ((QF).hessian.map ι *ᵥ (ι ∘ e)) = 0 := by
  have h := two_mul_evalIn (Q := QF) (R := F) e
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  have h0 : (QF).evalIn F e = 0 := he.2
  rw [h0, mul_zero] at h
  have : (ι ∘ e) ⬝ᵥ ((QF).hessian.map ι *ᵥ (ι ∘ e)) = ι (e ⬝ᵥ ((QF).hessian *ᵥ e)) := by
    simp only [dotProduct, mulVec, Fin.sum_univ_two, Function.comp, Matrix.map_apply, map_add, map_mul]
  rw [this, ← h, map_zero]

theorem det_hessian_map_ne_zero {K : Type*} [Field K] (ι : F →+* K) (hQ : Q₀.Nondegenerate) :
    ((QF).hessian.map ι).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero ι).mpr (nondegenerate_map Q₀ hQ)

theorem hessian_map_symm {K : Type*} [Field K] (ι : F →+* K) : ((QF).hessian.map ι) 1 0 = ((QF).hessian.map ι) 0 1 := by
  simp only [Matrix.map_apply]
  rw [show (QF).hessian 1 0 = (QF).hessian 0 1 by
    simp [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, add_comm]]

/-- **$SO(V)(K)$ preserves the isotropic line $K\iota(e)$**: $M\iota(e) = \chi_e(M)\,\iota(e)$ for every $M$ with
$M^{\mathsf T}HM = H$ ($H$ the Hessian of $Q\otimes K$) and $\det M = 1$. -/
theorem mulVec_eq_eigVal_smul {K : Type*} [Field K] [CharZero K] (ι : F →+* K) (hQ : Q₀.Nondegenerate)
    {e : Fin 2 → F} (he : IsIsoVec Q₀ e) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : Mᵀ * (QF).hessian.map ι * M = (QF).hessian.map ι) (hM1 : M.det = 1) :
    M *ᵥ (ι ∘ e) = eigVal ι e M • (ι ∘ e) := by
  have hd := det_mulVec_eq_zero_of_iso (hessian_map_symm ι) (det_hessian_map_ne_zero ι hQ) hM hM1
    (iso_dotProduct_hessian ι he)
  have hi : (ι ∘ e) (isoIdx e) ≠ 0 := by
    simpa using (map_ne_zero ι).mpr (isoIdx_ne_zero he.1)
  exact eq_smul_of_det_eq_zero hd hi

theorem eigVal_one {K : Type*} [Field K] (ι : F →+* K) {e : Fin 2 → F} (he : e ≠ 0) :
    eigVal ι e (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [eigVal, one_mulVec, Function.comp, div_self ((map_ne_zero ι).mpr (isoIdx_ne_zero he))]

theorem eigVal_mul {K : Type*} [Field K] [CharZero K] (ι : F →+* K) (hQ : Q₀.Nondegenerate)
    {e : Fin 2 → F} (he : IsIsoVec Q₀ e) {M N : Matrix (Fin 2) (Fin 2) K}
    (hN : Nᵀ * (QF).hessian.map ι * N = (QF).hessian.map ι) (hN1 : N.det = 1) :
    eigVal ι e (M * N) = eigVal ι e M * eigVal ι e N := by
  have hi : ι (e (isoIdx e)) ≠ 0 := (map_ne_zero ι).mpr (isoIdx_ne_zero he.1)
  rw [eigVal, ← mulVec_mulVec, mulVec_eq_eigVal_smul ι hQ he hN hN1, mulVec_smul, Pi.smul_apply, smul_eq_mul,
    eigVal, eigVal]
  field_simp

theorem eigVal_smul_vec {K : Type*} [Field K] (ι : F →+* K) {e : Fin 2 → F} {c : F} (hc : c ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) K) : eigVal ι (c • e) M = eigVal ι e M := by
  have hc' : ι c ≠ 0 := (map_ne_zero ι).mpr hc
  have h : (ι ∘ (c • e)) = ι c • (ι ∘ e) := by funext i; simp
  rw [eigVal, eigVal, isoIdx_smul hc, h, mulVec_smul, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul,
    map_mul]
  by_cases h0 : ι (e (isoIdx e)) = 0
  · simp [h0]
  · field_simp

end Eigen

/-! ### The character $\chi_e : SO(V)(\mathbb A)\to\mathbb A_F^\times$ -/

section Char

variable {F : Type} [Field F] [NumberField F] {Q₀ : QuadForm (𝓞 F) 2}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

theorem hessian_of_mem_soReal (w : {w : InfinitePlace F // w.IsReal}) (g : ArchSO (QRe Q₀ w)) :
    ((ArchSO.incl _ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (QF).hessian.map (embedding_of_isReal w.2) *
        ((ArchSO.incl _ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (QF).hessian.map (embedding_of_isReal w.2) ∧
      ((ArchSO.incl _ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  have h := ((mem_soReal_iff _ _).mp ((show soReal (QRe Q₀ w) from g).2))
  rwa [hessian_map_NF] at h

theorem hessian_of_mem_soC (w : {w : InfinitePlace F // w.IsComplex}) (g : ArchSOC (QCx Q₀ w)) :
    (ArchSOC.mat _ g)ᵀ * (QF).hessian.map w.1.embedding * ArchSOC.mat _ g = (QF).hessian.map w.1.embedding ∧
      (ArchSOC.mat _ g).det = 1 := by
  have h := (mem_soC_iff _ _).mp (ArchSOC.incl_mem _ g)
  refine ⟨?_, h.2⟩
  have h1 := h.1
  rw [gramC, hessian_map_NF, Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 : (2 : ℂ) • ((1 / 2 : ℂ) • ((ArchSOC.mat _ g)ᵀ * (QF).hessian.map w.1.embedding * ArchSOC.mat _ g)) =
      (2 : ℂ) • ((1 / 2 : ℂ) • (QF).hessian.map w.1.embedding) := by
    rw [← h1]; rfl
  simpa [smul_smul] using h2

theorem hessian_of_mem_soSub (v : HeightOneSpectrum (𝓞 F)) (g : soSub QF (v.adicCompletion F)) :
    (omat (g : orthGroup QF (v.adicCompletion F)))ᵀ * (QF).hessian.map (algebraMap F (v.adicCompletion F)) *
        omat (g : orthGroup QF (v.adicCompletion F)) = (QF).hessian.map (algebraMap F (v.adicCompletion F)) ∧
      (omat (g : orthGroup QF (v.adicCompletion F))).det = 1 :=
  ⟨(mem_orthGroup QF).mp (g : orthGroup QF (v.adicCompletion F)).2, mem_soSub.mp g.2⟩

variable (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e)

/-- $\chi_e$ at a real place $w$: the eigenvalue of $g_w\in SO(Q^{\sigma_w})(\mathbb R)$ on $\mathbb R\sigma_w(e)$. -/
def isoCharR (w : {w : InfinitePlace F // w.IsReal}) : ArchSO (QRe Q₀ w) →* ℝ where
  toFun g := eigVal (embedding_of_isReal w.2) e ((ArchSO.incl _ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  map_one' := by simp only [map_one, Units.val_one]; exact eigVal_one _ he.1
  map_mul' g h := by
    simp only [map_mul, Units.val_mul]
    exact eigVal_mul _ hQ he (hessian_of_mem_soReal w h).1 (hessian_of_mem_soReal w h).2

/-- $\chi_e$ at a complex place $w$: the eigenvalue of $g_w\in SO(Q^{\tau_w})(\mathbb C)$ on $\mathbb C\tau_w(e)$. -/
def isoCharC (w : {w : InfinitePlace F // w.IsComplex}) : ArchSOC (QCx Q₀ w) →* ℂ where
  toFun g := eigVal w.1.embedding e (ArchSOC.mat _ g)
  map_one' := by
    show eigVal w.1.embedding e ((ArchSOC.incl _ 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1
    simp only [map_one, Units.val_one]; exact eigVal_one _ he.1
  map_mul' g h := by
    rw [ArchSOC.mat_mul]
    exact eigVal_mul _ hQ he (hessian_of_mem_soC w h).1 (hessian_of_mem_soC w h).2

/-- $\chi_e$ at a finite place $v$: the eigenvalue of $g_v\in SO(V)(F_v)$ on $F_ve$. -/
def isoCharV (v : HeightOneSpectrum (𝓞 F)) : soSub QF (v.adicCompletion F) →* v.adicCompletion F where
  toFun g := eigVal (algebraMap F (v.adicCompletion F)) e (omat (g : orthGroup QF (v.adicCompletion F)))
  map_one' := by
    rw [OneMemClass.coe_one, omat_one]; exact eigVal_one _ he.1
  map_mul' g h := by
    rw [Subgroup.coe_mul, omat_mul]
    exact eigVal_mul _ hQ he (hessian_of_mem_soSub v h).1 (hessian_of_mem_soSub v h).2

theorem valued_algebraMap_le_one_eventually (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (v.adicCompletion F) x) ≤ 1 := by
  filter_upwards [eventually_valuation_le_one (F := F) x] with v hv
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans_le hv

/-- The component $g_v\in SO(V)(F_v)$ of $g\in SO(V)(\mathbb A_f)$. -/
def finComp (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) : soSub QF (v.adicCompletion F) := ⟨(g : OAf QF) v, g.2 v⟩

@[simp] theorem finComp_coe (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    (finComp g v : orthGroup QF (v.adicCompletion F)) = (g : OAf QF) v := rfl

theorem finComp_one (v : HeightOneSpectrum (𝓞 F)) : finComp (1 : SOAf Q₀) v = 1 := rfl

theorem finComp_mul (g h : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) : finComp (g * h) v = finComp g v * finComp h v :=
  rfl

/-- $\chi_e(g)_v$ is a $v$-adic integer for almost all $v$. -/
theorem eventually_isoCharV_mem (g : SOAf Q₀) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      isoCharV hQ he v (finComp g v) ∈ v.adicCompletionIntegers F := by
  filter_upwards [(g : OAf QF).2, valued_algebraMap_le_one_eventually (e 0),
    valued_algebraMap_le_one_eventually (e 1), eventually_valued_eq_one (isoIdx_ne_zero he.1)]
    with v hst h0 h1 hi
  have hst' : ((g : OAf QF) v : orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v := hst
  have hent := fun i j => entry_le_one_of_mem_stdStab v hst' i j
  have he' : ∀ j, algebraMap F (v.adicCompletion F) (e j) ∈ v.adicCompletionIntegers F := fun j => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F)]; fin_cases j
    · exact h0
    · exact h1
  have hM : ∀ i j, omat ((g : OAf QF) v : orthGroup QF (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F :=
    fun i j => hent i j
  show eigVal _ e (omat ((g : OAf QF) v : orthGroup QF (v.adicCompletion F))) ∈ _
  rw [eigVal, div_eq_mul_inv]
  refine mul_mem ?_ ?_
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, Function.comp]
    exact add_mem (mul_mem (hM _ _) (he' 0)) (mul_mem (hM _ _) (he' 1))
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F), map_inv₀, hi, inv_one]

/-- $\chi_e$ on $SO(V)(\mathbb A_f)$, with values in $\mathbb A_f$. -/
def isoCharFin : SOAf Q₀ →* AF where
  toFun g := mkAF (fun v => isoCharV hQ he v (finComp g v)) (eventually_isoCharV_mem hQ he g)
  map_one' := by
    ext v : 1
    rw [mkAF_apply, finComp_one, map_one]; rfl
  map_mul' g h := by
    ext v : 1
    change isoCharV hQ he v (finComp (g * h) v) = isoCharV hQ he v (finComp g v) * isoCharV hQ he v (finComp h v)
    rw [finComp_mul, map_mul]

/-- $\chi_e$ on $G_\infty$, with values in $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$. -/
def isoCharInf : GInfSO Q₀ →* mixedEmbedding.mixedSpace F :=
  (MonoidHom.pi fun w => (isoCharR hQ he w).comp (Pi.evalMonoidHom _ w)).prodMap
    (MonoidHom.pi fun w => (isoCharC hQ he w).comp (Pi.evalMonoidHom _ w))

/-- **The character $\chi_e : SO(V)(\mathbb A)\to\mathbb A_F^\times$** of an isotropic vector $e$: at every place $w$
(real, complex or finite) $\chi_e(g)_w$ is the eigenvalue of $g_w$ on the isotropic line $F_we$
(`isoCharR_spec`, `isoCharC_spec`, `isoCharV_spec`). This is the isomorphism $SO(V)\cong\mathbb G_m$ on adelic points. -/
@[kb "weil1982" "§2.4 [unverified] (characters of G and G_𝔸¹); omeara1963 §42 (hyperbolic plane) [unverified]"]
def isoChar : SOAdele Q₀ →* (Adeles F)ˣ := ((isoCharInf hQ he).prodMap (isoCharFin hQ he)).toHomUnits

@[simp] theorem isoChar_val (g : SOAdele Q₀) :
    ((isoChar hQ he g : (Adeles F)ˣ) : Adeles F) = (isoCharInf hQ he g.1, isoCharFin hQ he g.2) := rfl

/-- **$\chi_e$ is the eigenvalue on the isotropic line**, at every finite place. -/
theorem isoCharV_spec (v : HeightOneSpectrum (𝓞 F)) (g : soSub QF (v.adicCompletion F)) :
    omat (g : orthGroup QF (v.adicCompletion F)) *ᵥ (algebraMap F (v.adicCompletion F) ∘ e) =
      isoCharV hQ he v g • (algebraMap F (v.adicCompletion F) ∘ e) :=
  mulVec_eq_eigVal_smul _ hQ he (hessian_of_mem_soSub v g).1 (hessian_of_mem_soSub v g).2

/-- **$\chi_e$ is the eigenvalue on the isotropic line**, at every real place. -/
theorem isoCharR_spec (w : {w : InfinitePlace F // w.IsReal}) (g : ArchSO (QRe Q₀ w)) :
    ((ArchSO.incl _ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (embedding_of_isReal w.2 ∘ e) =
      isoCharR hQ he w g • (embedding_of_isReal w.2 ∘ e) :=
  mulVec_eq_eigVal_smul _ hQ he (hessian_of_mem_soReal w g).1 (hessian_of_mem_soReal w g).2

/-- **$\chi_e$ is the eigenvalue on the isotropic line**, at every complex place. -/
theorem isoCharC_spec (w : {w : InfinitePlace F // w.IsComplex}) (g : ArchSOC (QCx Q₀ w)) :
    ArchSOC.mat _ g *ᵥ (w.1.embedding ∘ e) = isoCharC hQ he w g • (w.1.embedding ∘ e) :=
  mulVec_eq_eigVal_smul _ hQ he (hessian_of_mem_soC w g).1 (hessian_of_mem_soC w g).2

end Char

/-! ### The norm-one subgroup, the measure and τ -/

section Tau

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) {e : Fin 2 → F}
  (he : IsIsoVec Q₀ e)

/-- **The norm-one subgroup** $SO(V)(\mathbb A)^1 = \{g : \|\chi_e(g)\|_{\mathbb A} = 1\}$, the kernel of $|\chi_e|$
($\mathbb A_F^1$ = `ideleOne F`). -/
@[kb "weil1982" "§2.4 [unverified] (G_𝔸¹ = ∩ ker |χ|_𝔸)"]
def SOAdeleOne : Subgroup (SOAdele Q₀) := (ideleOne F).comap (isoChar hQ he)

/-- **Weil's Tamagawa measure on $SO(V)(\mathbb A)$ for isotropic binary $V$**: the convergence factors
$\lambda_v = 1 - N(v)^{-1} = L_v(1,\mathbf 1)^{-1} = \zeta_{F,v}(1)^{-1}$ (`lamV`, those of $\mathbb G_m$; in the repository the
local measure is $\lambda_v^{-1}\omega_v$) and the global factor $\rho_F^{-1}$, $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$
(`dedekindZeta_residue`). `muTam` is the measure $c_F\,2^{r_2}\mu^{\mathrm{Leray}}_\infty\times\mu_f$ of `Weil/MuTamSO.lean`. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ρ⁻¹ ∏ λ_v⁻¹ ω_v); §2.4 [unverified]; ono1963 [unverified]"]
def muTamIso : Measure (SOAdele Q₀) := ENNReal.ofReal (dedekindZeta_residue F)⁻¹ • muTam Q₀ hQ lamV

/-- The log-norm shell $\{g : \alpha\le\log\|\chi_e(g)\|_{\mathbb A}<\beta\}$. -/
def isoShellIco (α β : ℝ) : Set (SOAdele Q₀) :=
  (fun g => Real.log (ideleNorm F (isoChar hQ he g))) ⁻¹' Ico α β

/-- The unit shell $\{g : 0\le\log\|\chi_e(g)\|_{\mathbb A}<1\}$. -/
def isoShell : Set (SOAdele Q₀) := isoShellIco Q₀ hQ he 0 1

/-- **Weil's/Ono's Tamagawa number of $SO(V)$, $V$ isotropic binary**: $\tau = \operatorname{vol}(SO(V)(F)\backslash
SO(V)(\mathbb A)^1)$ for Weil's measure on $SO(V)(\mathbb A)^1$ (the quotient of $\mu^{\mathrm{iso}}_{\mathrm{Tam}}$ by $dt/t$ on
$SO(V)(\mathbb A)/SO(V)(\mathbb A)^1\cong\mathbb R_{>0}$ via $|\chi_e|$). Since $\mu = \mu^1\times dt/t$ and $\int_1^e dt/t = 1$,
it is the $\mu^{\mathrm{iso}}_{\mathrm{Tam}}$-volume of $SO(V)(F)\backslash\{0\le\log|\chi_e|<1\}$, which is the definition
used here (no section of $|\chi_e|$ has to be chosen); `tauIso_eq_muIdeleClass` identifies it with
$\rho_F^{-1}\operatorname{vol}(F^\times\backslash\mathbb A_F^1,\mu^1)$ under $SO(V)\cong\mathbb G_m$. -/
@[kb "weil1982" "§2.4 [unverified] (τ(G) = vol(G_𝔸¹/G_k)); §3.2, proof of Thm 3.2.1, p. 43; ono1963 [unverified]"]
def tauIso : ℝ≥0∞ :=
  covolume (GammaSOAdele Q₀) (SOAdele Q₀) ((muTamIso Q₀ hQ).restrict (isoShell Q₀ hQ he))

/-- **Target statement:** $\tau(SO(V)) = 1$ for an isotropic binary $V$, for every isotropic vector $e$ (Ono's
$\tau(\mathbb G_m) = 1$; Weil 1982, §3.1 for $\mathbb G_m$ [unverified]). -/
@[kb "weil1982" "§2.4, §3.1 [unverified] (τ(G_m) = 1); ono1963 [unverified]"]
def TauOneIsotropic : Prop := ∀ (e : Fin 2 → F) (he : IsIsoVec Q₀ e), tauIso Q₀ hQ he = 1

end Tau

end QuadFormsKB.Tamagawa.Measure.Weil
