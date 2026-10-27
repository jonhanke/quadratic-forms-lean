/-
# The frame coordinates of a frame of corank one

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 1$ variables
(any signature), $T_0$ nondegenerate over $\mathcal O_F$ of rank $r$, and $\Xi = (\xi_0, \dots, \xi_{r-1})$ a rational
frame of $T_0$ (columns of $X\in F^{(r+1)\times r}$ with $Q_0\circ X = T_0$). The complement of the frame is
one-dimensional, and $SO_1$ is trivial, so the frame coordinates are the trivial ones: $SO(V)(\mathbb A)$ acts simply
transitively on its orbit of $\Xi$.

**Proves**
* `eq_one_of_mul_frame_corankOne`: over any field, an isometry $g$ of determinant $1$ fixing the columns of a frame
  $X$ with $X^{\mathsf T}HX$ invertible, in a space of dimension $r + 1$, is the identity;
* `eq_one_of_smul_ratAT`, `eq_one_of_smul_ratFT`, `eq_one_of_smul_ratFrameA`: the stabilizers of the archimedean,
  finite and adelic images of a rational frame of corank one are trivial;
* `exists_corankOne_complement`: a complement column $C\in F^{(r+1)\times 1}$ orthogonal to $\Xi$ with integral Gram
  form $Q''$ in one variable, nondegenerate;
* **`towerCorankOne`**: the `FrameTower` of $\Xi$ with $n' = 1$: parameter space $T = SO(V)(\mathbb A)$,
  $\sigma = \mu_{\mathrm{Tam}}$, $\tau(x) = x^{-1}\Xi$, coordinates the first projection, $\iota$ trivial (as
  $SO(Q'')(\mathbb A)$ is trivial), Weil's fibration because $\mu_{\mathrm{Tam}}(SO(Q'')(\mathbb A)) = 1$
  (`towerCorankOne_ιInf`, `towerCorankOne_ιFin`).

Indices are 0-based: the columns of $X$ are $\xi_0, \dots, \xi_{r-1}$ (`Fin r`), the complement column is the last
(index $r$) basis vector.
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Measure.Weil.RankOneAdelic

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Linear algebra over a field -/

section Algebra

variable {K : Type*} [Field K] {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin r) K) (c : Fin (r + 1) → K)

/-- **The square matrix $[X \mid c]$**: the columns $0, \dots, r-1$ are those of $X$, the last column ($r$) is $c$. -/
def snocCol : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => K) (c i) (fun k => X i k) j

@[simp] theorem snocCol_castSucc (i : Fin (r + 1)) (k : Fin r) : snocCol X c i k.castSucc = X i k := by
  simp [snocCol]

@[simp] theorem snocCol_last (i : Fin (r + 1)) : snocCol X c i (Fin.last r) = c i := by
  simp [snocCol]

/-- $[X\mid c]\,y = X\,(y_0,\dots,y_{r-1}) + y_r\,c$. -/
theorem snocCol_mulVec (y : Fin (r + 1) → K) :
    snocCol X c *ᵥ y = X *ᵥ (fun k => y k.castSucc) + y (Fin.last r) • c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, snocCol_castSucc, snocCol_last, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem snocCol_transpose_mulVec_castSucc (u : Fin (r + 1) → K) (k : Fin r) :
    ((snocCol X c)ᵀ *ᵥ u) k.castSucc = (Xᵀ *ᵥ u) k := by
  simp [Matrix.mulVec, dotProduct]

theorem snocCol_transpose_mulVec_last (u : Fin (r + 1) → K) :
    ((snocCol X c)ᵀ *ᵥ u) (Fin.last r) = c ⬝ᵥ u := by
  simp [Matrix.mulVec, dotProduct]

/-- **A nonzero kernel vector**: a matrix with $r$ rows and $r + 1$ columns has a nonzero vector in its kernel (rank
and nullity). -/
theorem exists_ne_zero_mulVec_eq_zero (M : Matrix (Fin r) (Fin (r + 1)) K) :
    ∃ c : Fin (r + 1) → K, c ≠ 0 ∧ M *ᵥ c = 0 := by
  have h : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨c, hc0, by simpa using hc⟩

/-- **$[X\mid c]$ is invertible** when $c\ne0$ is orthogonal to the columns of $X$ and $X^{\mathsf T}HX$ is
invertible: a relation $Xa + \mu c = 0$ gives, after applying $X^{\mathsf T}H$, $(X^{\mathsf T}HX)a = 0$, so $a = 0$,
then $\mu = 0$. -/
theorem snocCol_det_ne_zero (H : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hc : c ≠ 0)
    (hXc : (Xᵀ * H) *ᵥ c = 0) (hXX : (Xᵀ * H * X).det ≠ 0) : (snocCol X c).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [snocCol_mulVec] at hy0
  have h1 : (Xᵀ * H) *ᵥ (X *ᵥ (fun k => y k.castSucc) + y (Fin.last r) • c) = 0 := by
    rw [hy0, Matrix.mulVec_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hXc, smul_zero, add_zero, Matrix.mulVec_mulVec] at h1
  have ha : (fun k : Fin r => y k.castSucc) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hXX h1
  rw [ha, Matrix.mulVec_zero, zero_add] at hy0
  have hμ : y (Fin.last r) = 0 := by
    rcases smul_eq_zero.mp hy0 with h | h
    · exact h
    · exact absurd h hc
  apply hy
  funext j
  induction j using Fin.lastCases with
  | last => exact hμ
  | cast k => exact congrFun ha k

/-- **An isometry fixing a frame of corank one is the identity** (any field). Let $H$ be a matrix of size $r + 1$ and
$X$ of size $(r+1)\times r$ with $X^{\mathsf T}HX$ invertible. If $g^{\mathsf T}Hg = H$, $\det g = 1$ and $gX = X$, then
$g = 1$. *Proof:* choose $c \ne 0$ with $X^{\mathsf T}Hc = 0$ (rank and nullity); $P = [X\mid c]$ is invertible.
From $gX = X$ and $g^{\mathsf T}Hg = H$ one gets $X^{\mathsf T}H\,gc = X^{\mathsf T}Hc = 0$, so $gc = Xa + \mu c$ has
$a = 0$. Hence $gP = P\operatorname{diag}(1,\dots,1,\mu)$, $\det g = \mu = 1$, $gP = P$ and $g = 1$. -/
theorem eq_one_of_mul_frame_corankOne {K : Type*} [Field K] {r : ℕ} (H : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (X : Matrix (Fin (r + 1)) (Fin r) K) (hXX : (Xᵀ * H * X).det ≠ 0)
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hg : gᵀ * H * g = H) (hdet : g.det = 1) (hgX : g * X = X) :
    g = 1 := by
  classical
  obtain ⟨c, hc, hXc⟩ := exists_ne_zero_mulVec_eq_zero (Xᵀ * H)
  have hdetP := snocCol_det_ne_zero X c H hc hXc hXX
  have hPu : IsUnit (snocCol X c).det := isUnit_iff_ne_zero.mpr hdetP
  have e1 : Xᵀ * gᵀ = Xᵀ := by rw [← Matrix.transpose_mul, hgX]
  have e2 : Xᵀ * H * g = Xᵀ * H := by
    calc Xᵀ * H * g = Xᵀ * gᵀ * H * g := by rw [e1]
      _ = Xᵀ * (gᵀ * H * g) := by simp only [Matrix.mul_assoc]
      _ = Xᵀ * H := by rw [hg]
  have hgc : (Xᵀ * H) *ᵥ (g *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, e2]; exact hXc
  obtain ⟨y, hy⟩ : ∃ y, snocCol X c *ᵥ y = g *ᵥ c :=
    ⟨(snocCol X c)⁻¹ *ᵥ (g *ᵥ c), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]⟩
  rw [snocCol_mulVec] at hy
  have h1 : (Xᵀ * H) *ᵥ (X *ᵥ (fun k => y k.castSucc) + y (Fin.last r) • c) = 0 := by
    rw [hy]; exact hgc
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hXc, smul_zero, add_zero, Matrix.mulVec_mulVec] at h1
  have ha0 : (fun k : Fin r => y k.castSucc) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hXX h1
  have hgc' : g *ᵥ c = y (Fin.last r) • c := by
    rw [← hy, ha0, Matrix.mulVec_zero, zero_add]
  set μ : K := y (Fin.last r) with hμdef
  let d : Fin (r + 1) → K := fun i => if i = Fin.last r then μ else 1
  have hlast : d (Fin.last r) = μ := by simp [d]
  have hcast : ∀ k : Fin r, d k.castSucc = 1 := fun k => by
    simp [d, (Fin.castSucc_lt_last k).ne]
  have hgP : g * snocCol X c = snocCol X c * Matrix.diagonal d := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_diagonal]
    induction j using Fin.lastCases with
    | last =>
      have := congrFun hgc' i
      rw [hlast]
      simp only [Matrix.mul_apply, snocCol_last]
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    | cast k =>
      rw [hcast, mul_one]
      simp only [Matrix.mul_apply, snocCol_castSucc]
      have := congrFun (congrFun hgX i) k
      simpa [Matrix.mul_apply] using this
  have hprod : ∏ i, d i = μ := by
    rw [Fin.prod_univ_castSucc]
    simp [hcast, hlast]
  have h2 := congrArg Matrix.det hgP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hprod, hdet, one_mul] at h2
  have hμ1 : μ = 1 := by
    have : (snocCol X c).det * μ = (snocCol X c).det * 1 := by rw [mul_one, ← h2]
    exact mul_left_cancel₀ hdetP this
  have hd1 : d = fun _ => 1 := funext fun i => by simp [d, hμ1]
  rw [hd1, Matrix.diagonal_one, Matrix.mul_one] at hgP
  calc g = g * (snocCol X c * (snocCol X c)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
    _ = (g * snocCol X c) * (snocCol X c)⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [hgP, Matrix.mul_nonsing_inv _ hPu]

end Algebra

/-! ### Gram matrices of a rational frame -/

section Gram

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 1)) (T₀ : QuadForm (𝓞 F) r)

/-- The Gram determinant of a nondegenerate form over $\mathcal O_F$ is nonzero over $F$. -/
theorem det_hessian_map_ne_zero {m : ℕ} (S : QuadForm (𝓞 F) m) (h : S.Nondegenerate) :
    (S.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := by
  rw [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact algebraMap_det_ne_zero S h

/-- **The Gram matrix of a rational frame**: $X^{\mathsf T}HX = H_{T_0}$. -/
theorem gram_ratFrame (X : RatFrame Q₀ T₀) :
    X.1ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * X.1 = (T₀.map (algebraMap (𝓞 F) F)).hessian := by
  rw [← QuadForm.hessian_compMat, X.2]

/-- **The Gram matrix of a rational frame stays invertible under every embedding** $\sigma : F \to K$ into a field. -/
theorem gram_map_det_ne_zero (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀) {K : Type*} [Field K] (σ : F →+* K) :
    ((X.1.map σ)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map σ * X.1.map σ).det ≠ 0 := by
  have e : (X.1.map σ)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map σ * X.1.map σ =
      ((T₀.map (algebraMap (𝓞 F) F)).hessian).map σ := by
    rw [← gram_ratFrame Q₀ T₀ X, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero σ).mpr (det_hessian_map_ne_zero T₀ hT)

end Gram

/-! ### Stabilizers of rational frames of corank one are trivial -/

section Stabilizer

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 1)) (T₀ : QuadForm (𝓞 F) r)
  (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀)

/-- At a real place, $(\mathrm{diag}\,x)_w = \sigma_w(x)$. -/
theorem diag_real (x : F) (w : {w : InfinitePlace F // w.IsReal}) : (diag F x).1.1 w = σR w x :=
  mixedEmbedding.mixedEmbedding_apply_isReal F x w

/-- At a complex place, $(\mathrm{diag}\,x)_w = \tau_w(x)$. -/
theorem diag_complex (x : F) (w : {w : InfinitePlace F // w.IsComplex}) : (diag F x).1.2 w = σC w x :=
  mixedEmbedding.mixedEmbedding_apply_isComplex F x w

/-- At a finite place, $(\mathrm{diag}\,x)_v = x$ in $F_v$. -/
theorem diag_finite (x : F) (v : HeightOneSpectrum (𝓞 F)) : (diag F x).2 v = σV v x := rfl

/-- The real local matrix of $g\in SO(V)(\mathbb A)$ is orthogonal for $H$ and of determinant $1$. -/
theorem matR_gram (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    (matR Q₀ g w)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) * matR Q₀ g w =
        (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) ∧ (matR Q₀ g w).det = 1 := by
  have h := (mem_soReal_iff (QRe Q₀ w) _).mp (g.1.1 w).2
  have e : (QRe Q₀ w).hessian = (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) :=
    Siegel.hessian_map_NF _ _
  rw [e] at h
  exact h

/-- The complex local matrix of $g\in SO(V)(\mathbb A)$ is orthogonal for $H$ and of determinant $1$. -/
theorem matC_gram (g : SOAdele Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    (matC Q₀ g w)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) * matC Q₀ g w =
        (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) ∧ (matC Q₀ g w).det = 1 := by
  have h := (mem_soC_iff (QCx Q₀ w) _).mp (g.1.2 w).2
  have e : (QCx Q₀ w).hessian = (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) :=
    Siegel.hessian_map_NF _ _
  refine ⟨?_, h.2⟩
  have h1 := h.1
  simp only [gramC] at h1
  rw [e, Matrix.mul_smul, Matrix.smul_mul] at h1
  exact smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) h1

/-- The local matrix of $g\in SO(V)(\mathbb A)$ at a finite place is orthogonal for $H$ and of determinant $1$. -/
theorem matV_gram (g : SOAdele Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    (matV Q₀ g v)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σV v) * matV Q₀ g v =
        (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σV v) ∧ (matV Q₀ g v).det = 1 :=
  ⟨(mem_orthGroup (Q₀.map (algebraMap (𝓞 F) F))).mp ((g.2 : OAf (Q₀.map (algebraMap (𝓞 F) F))) v).2, g.2.2 v⟩

variable {Q₀ T₀ X}

/-- The local equation $g_w\,X = X$ at a real place from a fixed adelic frame. -/
theorem matR_mul_frame {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (w : {w : InfinitePlace F // w.IsReal}) : matR Q₀ g w * X.1.map (σR w) = X.1.map (σR w) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matR Q₀ g w *ᵥ fun k => σR w (X.1 k j)) i = σR w (X.1 i j) := by
    have := congrArg (fun y : Fin r → AdeleSpace F (Fin (r + 1)) => (y j i).1.1 w) h
    simpa [ratFrameA, smul_def, adeleSMul, diag_real] using this
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

/-- The local equation $g_w\,X = X$ at a complex place from a fixed adelic frame. -/
theorem matC_mul_frame {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (w : {w : InfinitePlace F // w.IsComplex}) : matC Q₀ g w * X.1.map (σC w) = X.1.map (σC w) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matC Q₀ g w *ᵥ fun k => σC w (X.1 k j)) i = σC w (X.1 i j) := by
    have := congrArg (fun y : Fin r → AdeleSpace F (Fin (r + 1)) => (y j i).1.2 w) h
    simpa [ratFrameA, smul_def, adeleSMul, diag_complex] using this
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

/-- The local equation $g_v\,X = X$ at a finite place from a fixed adelic frame. -/
theorem matV_mul_frame {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (v : HeightOneSpectrum (𝓞 F)) : matV Q₀ g v * X.1.map (σV v) = X.1.map (σV v) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matV Q₀ g v *ᵥ fun k => σV v (X.1 k j)) i = σV v (X.1 i j) := by
    exact congrArg (fun y : Fin r → AdeleSpace F (Fin (r + 1)) => (y j i).2 v) h
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

variable (Q₀ T₀ X)

include hT in
/-- **The stabilizer of the adelic image of a rational frame of corank one is trivial.** At every place the local
component of $g$ is an isometry of determinant $1$ fixing the $r$ columns of $X$ in an $(r+1)$-dimensional space, with
$X^{\mathsf T}HX$ invertible, so it is $1$ (`eq_one_of_mul_frame_corankOne`). -/
theorem eq_one_of_smul_ratFrameA {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X) : g = 1 := by
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · have hM := matR_gram Q₀ g w
    have e : matR Q₀ g w = 1 :=
      eq_one_of_mul_frame_corankOne _ (X.1.map (σR w)) (gram_map_det_ne_zero Q₀ T₀ hT X (σR w)) _ hM.1 hM.2
        (matR_mul_frame h w)
    exact Subtype.ext (Units.ext e)
  · have hM := matC_gram Q₀ g w
    have e : matC Q₀ g w = 1 :=
      eq_one_of_mul_frame_corankOne _ (X.1.map (σC w)) (gram_map_det_ne_zero Q₀ T₀ hT X (σC w)) _ hM.1 hM.2
        (matC_mul_frame h w)
    exact Subtype.ext (Units.ext e)
  · apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    have hM := matV_gram Q₀ g v
    have e : matV Q₀ g v = 1 :=
      eq_one_of_mul_frame_corankOne _ (X.1.map (σV v)) (gram_map_det_ne_zero Q₀ T₀ hT X (σV v)) _ hM.1 hM.2
        (matV_mul_frame h v)
    exact Subtype.ext (Units.ext e)

include hT in
/-- **The stabilizer of the archimedean image of a rational frame of corank one is trivial:**
$a\cdot\Xi_\infty = \Xi_\infty$ implies $a = 1$ in $G_\infty$. -/
theorem eq_one_of_smul_ratAT {a : GInfSO Q₀} (h : a • ratAT Q₀ T₀ X = ratAT Q₀ T₀ X) : a = 1 := by
  have h1 : ((a, 1) : SOAdele Q₀) • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X := by
    refine splitFrame_injective ?_
    rw [splitFrame_smul]
    show ((a, 1) : SOAdele Q₀) • (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X) = (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X)
    rw [prod_smul_def, h, one_smul]
  exact congrArg Prod.fst (eq_one_of_smul_ratFrameA Q₀ T₀ hT X h1)

include hT in
/-- **The stabilizer of the finite image of a rational frame of corank one is trivial:**
$b\cdot\Xi_f = \Xi_f$ implies $b = 1$ in $SO(V)(\mathbb A_f)$. -/
theorem eq_one_of_smul_ratFT {b : SOAf Q₀} (h : b • ratFT Q₀ T₀ X = ratFT Q₀ T₀ X) : b = 1 := by
  have h1 : (((1 : GInfSO Q₀), b) : SOAdele Q₀) • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X := by
    refine splitFrame_injective ?_
    rw [splitFrame_smul]
    show (((1 : GInfSO Q₀), b) : SOAdele Q₀) • (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X) = (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X)
    rw [prod_smul_def, h, one_smul]
  exact congrArg Prod.snd (eq_one_of_smul_ratFrameA Q₀ T₀ hT X h1)

end Stabilizer

/-! ### The complement of a frame of corank one -/

section Complement

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)

include hQ hT

/-- **Existence of the complement of a frame of corank one.** There are a nondegenerate form $Q'' = \langle c''\rangle$
over $\mathcal O_F$ in one variable and a column $C\in F^{(r+1)\times1}$ with $C^{\mathsf T}HC = H_{Q''}$ and
$C^{\mathsf T}H\xi_j = 0$ for all $j$. *Proof:* take $c \ne 0$ in the kernel of $X^{\mathsf T}H$ (rank and nullity), write
$c^{\mathsf T}Hc/2 = a/b$ with $a, b\in\mathcal O_F$ and put $C = b\,c$, $c'' = ab$; nondegeneracy because
$[X\mid c]$ is invertible and $Q_0$ is nondegenerate. -/
theorem exists_corankOne_complement :
    ∃ (Q'' : QuadForm (𝓞 F) 1) (Cm : Matrix (Fin (r + 1)) (Fin 1) F), Q''.Nondegenerate ∧
      Cmᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * Cm = (Q''.map (algebraMap (𝓞 F) F)).hessian ∧
      ∀ j, (Cmᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) *ᵥ cols Ξ.1 j = 0 := by
  classical
  set H := (Q₀.map (algebraMap (𝓞 F) F)).hessian with hH
  have hsymm : Hᵀ = H := by
    rw [hH]; ext i j; simp [QuadForm.hessian, add_comm]
  have hdetH : H.det ≠ 0 := det_hessian_map_ne_zero Q₀ hQ
  have hXX : (Ξ.1ᵀ * H * Ξ.1).det ≠ 0 := by
    rw [hH, gram_ratFrame]; exact det_hessian_map_ne_zero T₀ hT
  obtain ⟨c, hc, hXc⟩ := exists_ne_zero_mulVec_eq_zero (Ξ.1ᵀ * H)
  have hdetP := snocCol_det_ne_zero Ξ.1 c H hc hXc hXX
  -- the vector `c` is anisotropic
  have hs : c ⬝ᵥ (H *ᵥ c) ≠ 0 := by
    intro hs0
    have hPT : (snocCol Ξ.1 c)ᵀ *ᵥ (H *ᵥ c) = 0 := by
      funext j
      induction j using Fin.lastCases with
      | last => rw [snocCol_transpose_mulVec_last]; exact hs0
      | cast k => rw [snocCol_transpose_mulVec_castSucc, Matrix.mulVec_mulVec, hXc]; rfl
    have hu : H *ᵥ c = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hPT
    exact hdetH (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hu⟩)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c ⬝ᵥ (H *ᵥ c) / 2)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb0
  have haF : algebraMap (𝓞 F) F a = c ⬝ᵥ (H *ᵥ c) / 2 * algebraMap (𝓞 F) F b := by
    rw [← hab]; field_simp
  let Q'' : QuadForm (𝓞 F) 1 := QuadForm.ofUpper fun _ _ => b * a
  let Cm : Matrix (Fin (r + 1)) (Fin 1) F := Matrix.of fun i _ => algebraMap (𝓞 F) F b * c i
  have hCmcol : ∀ k : Fin 1, (fun l => Cm l k) = algebraMap (𝓞 F) F b • c := fun k => by
    funext l; simp [Cm]
  refine ⟨Q'', Cm, ?_, ?_, ?_⟩
  · show Q''.hessian.det ≠ 0
    rw [TauSOOne.hessian_det_rankOne]
    intro h0
    have h0' : (2 : 𝓞 F) * (b * a) = 0 := by simpa [Q'', QuadForm.ofUpper] using h0
    have h1 : (2 : F) * (algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F a) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0'
      rwa [map_mul, map_mul, map_zero, map_ofNat] at this
    rw [haF] at h1
    have h2 : algebraMap (𝓞 F) F b ^ 2 * (c ⬝ᵥ (H *ᵥ c)) = 0 := by linear_combination h1
    exact mul_ne_zero (pow_ne_zero 2 hbF) hs h2
  · ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    rw [QuadFormsKB.QuadForm.transpose_mul_mul_apply, hCmcol, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    simp only [QuadForm.hessian, QuadForm.map, Q'', QuadForm.ofUpper, Matrix.add_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.transpose_apply, le_refl, if_true, map_mul]
    linear_combination (-2 * algebraMap (𝓞 F) F b) * haF
  · have hM0 : Ξ.1ᵀ * H * Cm = 0 := by
      refine Matrix.ext fun i k => ?_
      calc (Ξ.1ᵀ * H * Cm) i k = ((Ξ.1ᵀ * H) *ᵥ fun l => Cm l k) i := by
            simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
        _ = 0 := by rw [hCmcol, Matrix.mulVec_smul, hXc, smul_zero]; rfl
    have hT0 : Cmᵀ * H * Ξ.1 = 0 := by
      have : (Cmᵀ * H * Ξ.1)ᵀ = 0 := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm, ← Matrix.mul_assoc]
        exact hM0
      rw [← Matrix.transpose_transpose (Cmᵀ * H * Ξ.1), this, Matrix.transpose_zero]
    intro j
    funext i
    have := congrFun (congrFun hT0 i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, cols] using this

/-- **The complement form** of the frame $\Xi$ of corank one: $Q'' = \langle c''\rangle$ in one variable. -/
def complForm : QuadForm (𝓞 F) 1 := (exists_corankOne_complement Q₀ hQ T₀ hT Ξ).choose

/-- **The complement column** $C\in F^{(r+1)\times1}$ of the frame $\Xi$, orthogonal to $\Xi$. -/
def complCol : Matrix (Fin (r + 1)) (Fin 1) F :=
  (exists_corankOne_complement Q₀ hQ T₀ hT Ξ).choose_spec.choose

theorem complForm_nondegenerate : (complForm Q₀ hQ T₀ hT Ξ).Nondegenerate :=
  (exists_corankOne_complement Q₀ hQ T₀ hT Ξ).choose_spec.choose_spec.1

theorem complCol_gram : (complCol Q₀ hQ T₀ hT Ξ)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * complCol Q₀ hQ T₀ hT Ξ =
    ((complForm Q₀ hQ T₀ hT Ξ).map (algebraMap (𝓞 F) F)).hessian :=
  (exists_corankOne_complement Q₀ hQ T₀ hT Ξ).choose_spec.choose_spec.2.1

theorem complCol_perp (j : Fin r) :
    ((complCol Q₀ hQ T₀ hT Ξ)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) *ᵥ cols Ξ.1 j = 0 :=
  (exists_corankOne_complement Q₀ hQ T₀ hT Ξ).choose_spec.choose_spec.2.2 j

end Complement

/-! ### Measure theory in rank one -/

section Measures

attribute [local instance] subsingleton_SOAdele

variable {F : Type} [Field F] [NumberField F]

/-- **The first projection** $\alpha\times\beta\cong\alpha$ for a subsingleton $\beta$ (with a chosen point). -/
def prodSubsingletonEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Subsingleton β] (b : β) :
    α × β ≃ᵐ α where
  toEquiv :=
    { toFun := Prod.fst
      invFun := fun a => (a, b)
      left_inv := fun p => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

/-- **Weil's measure in dimension one is the Dirac mass:** $SO(Q'')(\mathbb A)$ is a point and its Tamagawa measure has
total mass $1$ (`muTam_univ_rankOne`, `tamagawaK_rankOne_eq_one`). -/
theorem muTam_rankOne_eq_dirac (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) :
    muTam Q hQ 1 = Measure.dirac (1 : SOAdele Q) := by
  haveI := subsingleton_SOAdele Q
  have hu : muTam Q hQ (fun _ => 1) univ = 1 := by
    rw [muTam_univ_rankOne Q hQ, TauSOOne.tamagawaK_rankOne_eq_one Q hQ, ENNReal.ofReal_one]
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hsu : s = univ := eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
    subst hsu
    rw [Measure.dirac_apply_of_mem (mem_univ _)]
    exact hu

end Measures

/-! ### The tower of corank one -/

section Tower

attribute [local instance] subsingleton_SOAdele

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)

/-- The trivial embedding sends everything to $1$. -/
theorem prodMap_one_apply_eq_one (Q' : QuadForm (𝓞 F) 1) (h : SOAdele Q') :
    MonoidHom.prodMap (1 : GInfSO Q' →* GInfSO Q₀) (1 : SOAf Q' →* SOAf Q₀) h = 1 :=
  Prod.ext rfl rfl

/-- **Weil's fibration in corank one:** $\mu_{\mathrm{Tam}}(SO(V)) = \mathrm{pr}_{1*}(\mu_{\mathrm{Tam}}\otimes\mu_{\mathrm{Tam}}(SO_1))$,
since $\mu_{\mathrm{Tam}}(SO_1) = \delta_1$ and the first projection is inverted by $x\mapsto(x,1)$. -/
theorem towerCorankOne_fib (Q' : QuadForm (𝓞 F) 1) (hQ' : Q'.Nondegenerate) :
    muTam Q₀ hQ 1 = ((muTam Q₀ hQ 1).prod (muTam Q' hQ' 1)).map
      (prodSubsingletonEquiv (SOAdele Q₀) (SOAdele Q') 1) := by
  haveI := subsingleton_SOAdele Q'
  haveI : SFinite (muTam Q₀ hQ 1) := inferInstance
  rw [muTam_rankOne_eq_dirac Q' hQ', Measure.prod_dirac,
    Measure.map_map (prodSubsingletonEquiv (SOAdele Q₀) (SOAdele Q') 1).measurable
      measurable_prodMk_right]
  exact (Measure.map_id).symm

/-- **The frame coordinates of a frame of corank one** (Weil 1982, §2.4 / §4.5, in the trivial case $n' = 1$): the
complement $Q''$ is the one-variable form $\langle c''\rangle$ orthogonal to $\Xi$, and since $SO(Q'')(\mathbb A)$ is
trivial the embedding $\iota$ is trivial, the parameter space is $SO(V)(\mathbb A)$ itself with
$\sigma = \mu_{\mathrm{Tam}}$, $\tau(x) = x^{-1}\Xi$, and the coordinates are the first projection. Weil's fibration
holds because $\mu_{\mathrm{Tam}}(SO(Q'')(\mathbb A)) = 1$, and the stabilizers of $\Xi$ are trivial
(`eq_one_of_smul_ratFrameA`). **Unconditional.** -/
def towerCorankOne (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) : FrameTower Q₀ hQ 1 (cols Ξ.1) :=
  haveI : Subsingleton (SOAdele (complForm Q₀ hQ T₀ hT Ξ)) := subsingleton_SOAdele _
  { Q'' := complForm Q₀ hQ T₀ hT Ξ
    hQ'' := complForm_nondegenerate Q₀ hQ T₀ hT Ξ
    ιInf := 1
    ιFin := 1
    measurable_ιInf := measurable_const
    continuous_ιInf := continuous_const
    T := SOAdele Q₀
    σ := muTam Q₀ hQ 1
    τ := fun x => x⁻¹ • frameA (cols Ξ.1)
    C :=
      { coord := prodSubsingletonEquiv (SOAdele Q₀) (SOAdele (complForm Q₀ hQ T₀ hT Ξ)) 1
        mul := fun x h h' => by
          show x = _ * x
          rw [prodMap_one_apply_eq_one, one_mul]
        orbit := fun x h => rfl }
    sFinite := inferInstance
    fib := towerCorankOne_fib Q₀ hQ _ (complForm_nondegenerate Q₀ hQ T₀ hT Ξ)
    gamma_mem := fun h _ => by
      rw [prodMap_one_apply_eq_one]; exact one_mem _
    stabΓ := fun γ _ hγ =>
      ⟨1, one_mem _, by
        rw [prodMap_one_apply_eq_one]; exact (eq_one_of_smul_ratFrameA Q₀ T₀ hT Ξ hγ).symm⟩
    stab := fun g hg =>
      ⟨1, by
        rw [prodMap_one_apply_eq_one]; exact (eq_one_of_smul_ratFrameA Q₀ T₀ hT Ξ hg).symm⟩
    Cm := complCol Q₀ hQ T₀ hT Ξ
    hCR := fun h w => by
      rw [Subsingleton.elim h 1, map_one]
      simp
    hCC := fun h w => by
      rw [Subsingleton.elim h 1, map_one]
      simp
    hCV := fun h v => by
      rw [Subsingleton.elim h 1, map_one]
      simp
    hCH := complCol_gram Q₀ hQ T₀ hT Ξ
    hΞC := fun j => complCol_perp Q₀ hQ T₀ hT Ξ j }

/-- **The finite embedding of the corank one tower is trivial** ($SO_1$ has no nontrivial points). -/
theorem towerCorankOne_ιFin : (towerCorankOne Q₀ hQ T₀ hT Ξ).ιFin = 1 := rfl

/-- **The archimedean embedding of the corank one tower is trivial** ($SO_1$ has no nontrivial points). -/
theorem towerCorankOne_ιInf : (towerCorankOne Q₀ hQ T₀ hT Ξ).ιInf = 1 := rfl

end Tower

end QuadFormsKB.Tamagawa.Indefinite
