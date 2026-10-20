import QuadFormsKB.HilbertModular.DiagGaussian
import QuadFormsKB.HilbertModular.KoecherCusps
import QuadFormsKB.Defs.QuadForm

/-!
# Theta series over a totally real field I: definition, convergence, holomorphy, $q$-expansion

Let $F$ be totally real of degree $d$, with real embeddings $\varphi_v$ (`realEmb F v`, $v$ = `InfinitePlace F`), and
$e(t) = e^{2\pi it}$. A **lattice with a pseudo-basis** in $F^n$ is $L = \bigoplus_i I_ie_i$ for fractional ideals $I_0, \dots,
I_{n-1}$ (`I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ`); every $\mathcal{O}_F$-lattice has this form in a suitable $F$-basis
(Steinitz), and $L = \mathcal{O}_F^n$ is the case $I_i = \mathcal{O}_F$. Its points are $x = (x_i)$, $x_i = \sum_lk_{il}\beta^{(i)}_l$
with $k \in \mathbb{Z}^{n\times d}$ and $\beta^{(i)}$ = `QuadFormsKB.Analysis.bq (I i)` a $\mathbb{Z}$-basis of $I_i$ (`latVec I k`).
For a symmetric $A \in M_n(F)$ ("Gram matrix") with $\varphi_v(A)$ positive definite at every real place
(`IsTotPosGram A`) and $z \in \mathbb{C}^d$ with $\operatorname{Im}z_v > 0$:
$$\theta_{A,L}(z) = \sum_{x\in L}e\Big(\sum_v\varphi_v(x^{\mathsf T}Ax)\,z_v\Big) = \sum_{x \in L}e\big(\operatorname{Tr}(Q(x)z)\big)
  \qquad(\texttt{thetaLat A I z}).$$

* `summable_norm_thetaTerm`: **absolute convergence** (for $\operatorname{Im} z_v > 0$ at every place);
* `thetaTerm_eq_gaussAt`: each term is a diagonal complex Gaussian $G_b(M\vec k)$ with rates $b = -2iz_v$ and the real
  matrix $M = D\cdot K$ (`blockMat`, `coordMat`): $D$ is block diagonal with the blocks $\varphi_v(A)^{1/2}$, $K$ is block
  diagonal with the blocks $(\varphi_v(\beta^{(i)}_l))_{v,l}$ — the input for the inversion formula (`ThetaInversion.lean`);
* `isHolomorphic_thetaLatH`: $\theta_{A,L}$ is **holomorphic** on $\mathbb{H}^d$ (continuous, holomorphic in each variable);
* For a form $Q$ over $\mathcal{O}_F$ (`QuadForm (𝓞 F) n`): `thetaQ Q z` $= \sum_{x\in\mathcal{O}_F^n}e(\operatorname{Tr}(Q(x)z))$,
  `thetaQ_eq_thetaLat` (it is $\theta_{A,\mathcal{O}_F^n}$ for the Gram matrix $A = \frac12H$, `gramF`), and the
  **$q$-expansion** `hasSum_thetaQ`: $\theta_Q(z) = \sum_{\nu\in\mathcal{O}_F}r_Q(\nu)e(\operatorname{Tr}(\nu z))$ with
  $r_Q(\nu) = \#\{x \in \mathcal{O}_F^n : Q(x) = \nu\}$ finite (`finite_repSet`), and $r_Q(\nu) = 0$ unless $\nu = 0$ or
  $\nu \gg 0$ (`repNumF_eq_zero_of_not_totallyPos`).

Sources: Freitag, *Hilbert Modular Forms*, Ch. I §4 (theta series) [unverified]; Garrett, *Holomorphic Hilbert
Modular Forms*, Ch. 2 [unverified]; Shimura 1978 §1 [unverified]. The $\mathbb{Q}$ version is `QuadFormsKB.Siegel.theta`.
-/

open Matrix NumberField NumberField.InfinitePlace UpperHalfPlane Complex
open scoped MatrixGroups Real nonZeroDivisors Manifold ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-! ### Places indexed by `Fin d` -/

lemma card_infinitePlace : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  have h := (mixedEquiv (F := F)).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, NumberField.mixedEmbedding.finrank] at h
  exact h.symm

/-- An enumeration $\{0,\dots,d-1\} \simeq$ the real places (used only to index matrices; nothing depends on it). -/
def placeEquiv : Fin (Module.finrank ℚ F) ≃ InfinitePlace F :=
  (Fintype.equivFinOfCardEq (card_infinitePlace (F := F))).symm

/-! ### The real matrices $D$ (Gram square roots) and $K$ (embeddings of the ideal bases) -/

/-- $(\varphi_{v_j}(Y_l))_{j,l}$ for $Y \in F^d$, $v_j$ = `placeEquiv j`. -/
def embMat (Y : Fin (Module.finrank ℚ F) → F) : Matrix (Fin dq) (Fin dq) ℝ :=
  Matrix.of fun j l => realEmb F (placeEquiv j) (Y l)

/-- **The coordinate matrix** $K$ on $\mathbb{R}^{n\times d}$: $K_{(i,j),(i',l)} = \delta_{ii'}\varphi_{v_j}(Y^{(i)}_l)$; so
$(K\vec k)_{(i,j)} = \varphi_{v_j}(\sum_lk_{il}Y^{(i)}_l)$ (`coordMat_mulVec`). -/
def coordMat (Y : Fin n → Fin (Module.finrank ℚ F) → F) : Matrix (Fin n × Fin dq) (Fin n × Fin dq) ℝ :=
  Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Matrix.blockDiagonal fun i => embMat (Y i))

/-- **The block matrix** $D$ on $\mathbb{R}^{n\times d}$: $D_{(i,j),(i',j')} = \delta_{jj'}(B_{v_j})_{ii'}$. -/
def blockMat (B : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin dq) (Fin n × Fin dq) ℝ :=
  Matrix.blockDiagonal fun j => B (placeEquiv j)

lemma coordMat_mulVec (Y : Fin n → Fin (Module.finrank ℚ F) → F) (u : Fin n × Fin dq → ℝ)
    (i : Fin n) (j : Fin dq) :
    (coordMat Y *ᵥ u) (i, j) = ∑ l, realEmb F (placeEquiv j) (Y i l) * u (i, l) := by
  simp only [coordMat, Matrix.reindex_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, embMat, Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [Ne.symm hb]
  · simp

lemma coordMat_mulVec_int (Y : Fin n → Fin (Module.finrank ℚ F) → F) (k : Fin n × Fin dq → ℤ)
    (i : Fin n) (j : Fin dq) :
    (coordMat Y *ᵥ fun p => (k p : ℝ)) (i, j) =
      realEmb F (placeEquiv j) (∑ l, (k (i, l) : F) * Y i l) := by
  rw [coordMat_mulVec, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_intCast, mul_comm]

lemma blockMat_mulVec (B : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ) (u : Fin n × Fin dq → ℝ)
    (i : Fin n) (j : Fin dq) :
    (blockMat B *ᵥ u) (i, j) = (B (placeEquiv j) *ᵥ fun i' => u (i', j)) i := by
  simp only [blockMat, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [Ne.symm hb]
  · simp

lemma sum_sq_mulVec (B : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∑ i, ((B *ᵥ y) i) ^ 2 = y ⬝ᵥ (Bᵀ * B) *ᵥ y := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [dotProduct, sq]

/-- The value $x^{\mathsf T}Ax \in F$. -/
abbrev qv (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) : F := x ⬝ᵥ A *ᵥ x

lemma realEmb_qv (v : InfinitePlace F) (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) :
    realEmb F v (qv A x) = (fun i => realEmb F v (x i)) ⬝ᵥ (A.map (realEmb F v)) *ᵥ
      (fun i => realEmb F v (x i)) := by
  rw [qv, RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec _ _ _ i

/-- **The Gaussian at $M\vec k$, $M = DK$, is the theta term.** If $B_v^{\mathsf T}B_v = \varphi_v(S)$ at every place, then
$G_b(DK\vec k)$ with rates $b_{(i,j)} = w_{v_j}$ is $\exp(-\pi\sum_vw_v\varphi_v(x^{\mathsf T}Sx))$, $x_i = \sum_lk_{il}Y^{(i)}_l$. -/
theorem gaussAt_blockMat_coordMat (S : Matrix (Fin n) (Fin n) F)
    (B : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ v, (B v)ᵀ * B v = S.map (realEmb F v)) (Y : Fin n → Fin (Module.finrank ℚ F) → F)
    (w : InfinitePlace F → ℂ) (k : Fin n × Fin dq → ℤ) :
    gaussAt (fun p => w (placeEquiv p.2)) (blockMat B * coordMat Y) k =
      cexp (-Real.pi * ∑ v, w v *
        (realEmb F v (qv S fun i => ∑ l, (k (i, l) : F) * Y i l) : ℂ)) := by
  unfold gaussAt
  congr 2
  rw [← Matrix.mulVec_mulVec, Fintype.sum_prod_type, Finset.sum_comm]
  rw [← (placeEquiv (F := F)).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [blockMat_mulVec, coordMat_mulVec_int]
  rw [← Finset.mul_sum]
  congr 1
  rw [realEmb_qv, ← hB, ← sum_sq_mulVec]
  push_cast
  rfl

/-! ### Duality: $M^{\mathsf T}M' = 1$ -/

lemma embMat_transpose_mul (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (embMat (QuadFormsKB.Analysis.bq I))ᵀ * embMat (QuadFormsKB.Analysis.bq I).traceDual = 1 := by
  ext l l'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, embMat, Matrix.of_apply]
  rw [(placeEquiv (F := F)).sum_comp (fun v => realEmb F v (QuadFormsKB.Analysis.bq I l) *
    realEmb F v ((QuadFormsKB.Analysis.bq I).traceDual l'))]
  simp_rw [← map_mul]
  rw [sum_realEmb, Module.Basis.trace_mul_traceDual, Matrix.one_apply]
  split_ifs <;> simp

lemma coordMat_transpose_mul (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (coordMat fun i => QuadFormsKB.Analysis.bq (I i))ᵀ *
      coordMat (fun i => (QuadFormsKB.Analysis.bq (I i)).traceDual) = 1 := by
  rw [coordMat, coordMat, Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul]
  simp_rw [embMat_transpose_mul]
  rw [show (fun _ : Fin n => (1 : Matrix (Fin dq) (Fin dq) ℝ)) = 1 from rfl, Matrix.blockDiagonal_one,
    Matrix.submatrix_one_equiv]

lemma blockMat_transpose_mul (B B' : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ v, (B v)ᵀ * B' v = 1) : (blockMat B)ᵀ * blockMat B' = 1 := by
  rw [blockMat, blockMat, Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul]
  simp_rw [h]
  exact Matrix.blockDiagonal_one

lemma mat_transpose_mul (B B' : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ v, (B v)ᵀ * B' v = 1) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (blockMat B * coordMat fun i => QuadFormsKB.Analysis.bq (I i))ᵀ *
      (blockMat B' * coordMat fun i => (QuadFormsKB.Analysis.bq (I i)).traceDual) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockMat B)ᵀ,
    blockMat_transpose_mul B B' h, Matrix.one_mul, coordMat_transpose_mul]

/-! ### Gram matrices, lattice vectors, the theta series -/

/-- **Totally positive definite Gram matrix**: $\varphi_v(A)$ is a (symmetric) positive definite real matrix at every real
place $v$ (Mathlib's `Matrix.PosDef`, which includes symmetry). -/
def IsTotPosGram (A : Matrix (Fin n) (Fin n) F) : Prop := ∀ v, (A.map (realEmb F v)).PosDef

open scoped MatrixOrder in
/-- $B_v = \varphi_v(A)^{1/2}$ (continuous functional calculus). -/
def gramSqrt (A : Matrix (Fin n) (Fin n) F) (v : InfinitePlace F) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (A.map (realEmb F v))

open scoped MatrixOrder in
lemma gramSqrt_spec {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F) :
    (gramSqrt A v)ᵀ = gramSqrt A v ∧ gramSqrt A v * gramSqrt A v = A.map (realEmb F v) := by
  have h0 : 0 ≤ A.map (realEmb F v) := (nonneg_iff_posSemidef).2 (hA v).posSemidef
  have hsa : IsSelfAdjoint (gramSqrt A v) := (CFC.sqrt_nonneg _).isSelfAdjoint
  refine ⟨?_, CFC.sqrt_mul_sqrt_self _ h0⟩
  simpa [Matrix.star_eq_conjTranspose] using hsa.star_eq

open scoped MatrixOrder in
lemma gramSqrt_det_nonneg (A : Matrix (Fin n) (Fin n) F) (v : InfinitePlace F) :
    0 ≤ (gramSqrt A v).det :=
  ((nonneg_iff_posSemidef).1 (CFC.sqrt_nonneg (A.map (realEmb F v)))).det_nonneg

lemma gramSqrt_det {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F) :
    (gramSqrt A v).det = Real.sqrt (A.map (realEmb F v)).det := by
  rw [← (gramSqrt_spec hA v).2, det_mul, Real.sqrt_mul_self (gramSqrt_det_nonneg A v)]

lemma gramSqrt_det_ne_zero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F) :
    (gramSqrt A v).det ≠ 0 := by
  rw [gramSqrt_det hA]
  exact (Real.sqrt_pos.2 (hA v).det_pos).ne'

lemma gramSqrt_transpose_mul_inv {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (v : InfinitePlace F) : (gramSqrt A v)ᵀ * (gramSqrt A v)⁻¹ = 1 := by
  rw [(gramSqrt_spec hA v).1]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (gramSqrt_det_ne_zero hA v))

lemma gramSqrt_transpose_mul_self {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (v : InfinitePlace F) : (gramSqrt A v)ᵀ * gramSqrt A v = A.map (realEmb F v) := by
  rw [(gramSqrt_spec hA v).1, (gramSqrt_spec hA v).2]

/-- **The lattice point** $x = (x_i)$, $x_i = \sum_lk_{il}\beta^{(i)}_l \in I_i$ (`QuadFormsKB.Analysis.latElt`). -/
def latVec (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (k : Fin n → Fin (Module.finrank ℚ F) → ℤ) :
    Fin n → F :=
  fun i => QuadFormsKB.Analysis.latElt (𝔞 i) (k i)

/-- **The dual lattice point** $\mu = (\mu_i)$, $\mu_i = \sum_lm_{il}\beta^{(i)\vee}_l \in I_i^\vee = I_i^{-1}\mathfrak d^{-1}$
(trace-dual basis, `QuadFormsKB.Analysis.dualElt`). -/
def dualLatVec (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (m : Fin n → Fin (Module.finrank ℚ F) → ℤ) :
    Fin n → F :=
  fun i => QuadFormsKB.Analysis.dualElt (𝔞 i) (m i)

/-- **The theta term** $e\big(\sum_v\varphi_v(x^{\mathsf T}Ax)z_v\big)$ for $z \in \mathbb{C}^d$. -/
def thetaTerm (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) (z : InfinitePlace F → ℂ) : ℂ :=
  cexp (2 * Real.pi * Complex.I * ∑ v, (realEmb F v (qv A x) : ℂ) * z v)

/-- **The theta series of the lattice** $L = \bigoplus_iI_ie_i$ with Gram matrix $A$:
$$\theta_{A,L}(z) = \sum_{x\in L}e\Big(\sum_v\varphi_v(x^{\mathsf T}Ax)z_v\Big),\qquad z \in \mathbb{C}^d,\ \operatorname{Im}z_v > 0$$
(summed over the coordinates $k \in \mathbb{Z}^{n\times d}$ of $x$, `latVec`; junk value $0$ where the series diverges).

Parameters: `A` (Gram matrix over $F$; the form is $Q(x) = x^{\mathsf T}Ax$), `𝔞` (the coefficient ideals $I_i$), `z`. -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
def thetaLat (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℂ) : ℂ :=
  ∑' k : Fin n → Fin (Module.finrank ℚ F) → ℤ, thetaTerm A (latVec 𝔞 k) z

/-- **The theta series of the dual lattice** $L^\# = \bigoplus_iI_i^\vee e_i^*$ (trace dual for $B(x, y) = \operatorname{Tr}(x^{\mathsf T}y)$
in the coordinates $y = 2Ax$) with the dual form $Q^\#(\mu) = \tfrac14\mu^{\mathsf T}A^{-1}\mu$:
$\theta^\#_{A,L}(z) = \sum_{\mu\in L^\#}e\big(\sum_v\varphi_v(Q^\#(\mu))z_v\big)$. For $F = \mathbb{Q}$ this is
`QuadFormsKB.Siegel.thetaDual` ($Q^* = \frac14\vec y^{\mathsf T}A^{-1}\vec y$). -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
def thetaLatDual (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℂ) : ℂ :=
  ∑' m : Fin n → Fin (Module.finrank ℚ F) → ℤ, thetaTerm ((1 / 4 : F) • A⁻¹) (dualLatVec 𝔞 m) z

/-- $\theta_{A,L}$ as a function on $\mathbb{H}^d$. -/
def thetaLatH (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℍ) : ℂ :=
  thetaLat A 𝔞 fun v => (z v : ℂ)

/-- The real matrix $M = DK$ of the lattice: $(M\vec k)_{(i,j)} = (B_{v_j}\varphi_{v_j}(x))_i$. -/
def latMat (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Matrix (Fin n × Fin dq) (Fin n × Fin dq) ℝ :=
  blockMat (gramSqrt A) * coordMat fun i => QuadFormsKB.Analysis.bq (𝔞 i)

/-- The real matrix $M' = D^{-1}K^\vee$ of the dual lattice; $M^{\mathsf T}M' = 1$ (`latMat_transpose_mul`). -/
def dualMat (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Matrix (Fin n × Fin dq) (Fin n × Fin dq) ℝ :=
  blockMat (fun v => (gramSqrt A v)⁻¹) * coordMat fun i => (QuadFormsKB.Analysis.bq (𝔞 i)).traceDual

lemma latMat_transpose_mul {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : (latMat A 𝔞)ᵀ * dualMat A 𝔞 = 1 :=
  mat_transpose_mul _ _ (gramSqrt_transpose_mul_inv hA) 𝔞

lemma latMat_det_ne_zero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : (latMat A 𝔞).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (latMat_transpose_mul hA 𝔞)
  rw [det_mul, det_transpose, h, zero_mul, det_one] at this
  exact zero_ne_one this

lemma latVec_curry (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (k : Fin n × Fin dq → ℤ) :
    latVec 𝔞 (Equiv.curry _ _ _ k) =
      fun i => ∑ l, (k (i, l) : F) * QuadFormsKB.Analysis.bq (𝔞 i) l := rfl

lemma dualLatVec_curry (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (k : Fin n × Fin dq → ℤ) :
    dualLatVec 𝔞 (Equiv.curry _ _ _ k) =
      fun i => ∑ l, (k (i, l) : F) * (QuadFormsKB.Analysis.bq (𝔞 i)).traceDual l := rfl

/-- **Each theta term is a diagonal Gaussian**: $e(\sum_v\varphi_v(Q(x))z_v) = G_b(M\vec k)$ with $b_{(i,j)} = -2iz_{v_j}$. -/
theorem thetaTerm_eq_gaussAt {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : InfinitePlace F → ℂ) (k : Fin n × Fin dq → ℤ) :
    thetaTerm A (latVec 𝔞 (Equiv.curry _ _ _ k)) z =
      gaussAt (fun p => -2 * Complex.I * z (placeEquiv p.2)) (latMat A 𝔞) k := by
  rw [latMat, gaussAt_blockMat_coordMat A _ (gramSqrt_transpose_mul_self hA) _
    (fun v => -2 * Complex.I * z v), thetaTerm, latVec_curry]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring_nf

lemma rate_re_pos {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) (p : Fin n × Fin dq) :
    0 < (-2 * Complex.I * z (placeEquiv p.2)).re := by
  have := hz (placeEquiv p.2)
  simp [mul_re]
  linarith

/-- **Absolute convergence** of the theta series for $\operatorname{Im} z_v > 0$ at every place. -/
theorem summable_norm_thetaTerm {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) :
    Summable fun k : Fin n → Fin (Module.finrank ℚ F) → ℤ => ‖thetaTerm A (latVec 𝔞 k) z‖ := by
  have h := summable_norm_gaussAt (latMat A 𝔞) (latMat_det_ne_zero hA 𝔞) _ (rate_re_pos (n := n) hz)
  rw [← (Equiv.curry (Fin n) (Fin dq) ℤ).summable_iff]
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [← thetaTerm_eq_gaussAt hA]

lemma qv_nonneg {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F)
    (x : Fin n → F) : 0 ≤ realEmb F v (qv A x) := by
  rw [realEmb_qv]
  simpa using (hA v).posSemidef.dotProduct_mulVec_nonneg (fun i => realEmb F v (x i))

lemma norm_thetaTerm (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) (z : InfinitePlace F → ℂ) :
    ‖thetaTerm A x z‖ = Real.exp (-(2 * Real.pi) * ∑ v, realEmb F v (qv A x) * (z v).im) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  simp only [Finset.mul_sum, re_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [mul_re, mul_im]

/-- Monotonicity: increasing $\operatorname{Im} z$ decreases $|e(\sum_v\varphi_v(Q(x))z_v)|$. -/
lemma norm_thetaTerm_le {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (x : Fin n → F)
    {z z' : InfinitePlace F → ℂ} (h : ∀ v, (z' v).im ≤ (z v).im) :
    ‖thetaTerm A x z‖ ≤ ‖thetaTerm A x z'‖ := by
  rw [norm_thetaTerm, norm_thetaTerm]
  refine Real.exp_le_exp.2 ?_
  have : ∑ v, realEmb F v (qv A x) * (z' v).im ≤ ∑ v, realEmb F v (qv A x) * (z v).im :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h v) (qv_nonneg hA v x)
  nlinarith [Real.pi_pos]

/-! ### Holomorphy on $\mathbb{H}^d$ -/

lemma continuous_thetaTerm (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) :
    Continuous fun z : InfinitePlace F → ℍ => thetaTerm A x fun v => (z v : ℂ) := by
  unfold thetaTerm
  have : ∀ v : InfinitePlace F, Continuous fun z : InfinitePlace F → ℍ => ((z v : ℍ) : ℂ) :=
    fun v => UpperHalfPlane.continuous_coe.comp (continuous_apply v)
  fun_prop

/-- $\theta_{A,L}$ is **continuous** on $\mathbb{H}^d$ (locally uniform convergence, Weierstrass M-test). -/
theorem continuous_thetaLatH {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Continuous (thetaLatH A 𝔞) := by
  rw [continuous_iff_continuousAt]
  intro z0
  set U : Set (InfinitePlace F → ℍ) := {z | ∀ v, (z0 v).im / 2 < (z v).im} with hU
  have hUo : IsOpen U := by
    rw [hU, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun v =>
      isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp (continuous_apply v))
  have hz0 : z0 ∈ U := fun v => by have := (z0 v).im_pos; linarith
  set z' : InfinitePlace F → ℂ := fun v => (((z0 v).im / 2 : ℝ) : ℂ) * Complex.I
  have hz' : ∀ v, 0 < (z' v).im := fun v => by simp [z', (z0 v).im_pos]
  have hc : ContinuousOn (thetaLatH A 𝔞) U := by
    refine continuousOn_tsum (fun k => (continuous_thetaTerm A _).continuousOn)
      (summable_norm_thetaTerm hA 𝔞 hz') fun k z hz => norm_thetaTerm_le hA _ fun v => ?_
    have := hz v
    simp only [z', mul_im, ofReal_re, Complex.I_im, mul_one, ofReal_im, Complex.I_re, mul_zero,
      add_zero]
    exact this.le
  exact hc.continuousAt (hUo.mem_nhds hz0)

lemma differentiable_update_apply [DecidableEq (InfinitePlace F)] (Z : InfinitePlace F → ℂ)
    (v u : InfinitePlace F) : Differentiable ℂ fun w : ℂ => Function.update Z v w u := by
  by_cases h : u = v
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma differentiable_thetaTerm_update [DecidableEq (InfinitePlace F)] (A : Matrix (Fin n) (Fin n) F)
    (x : Fin n → F) (Z : InfinitePlace F → ℂ) (v : InfinitePlace F) :
    Differentiable ℂ fun w : ℂ => thetaTerm A x (Function.update Z v w) := by
  unfold thetaTerm
  have := differentiable_update_apply Z v
  fun_prop

/-- **$\theta_{A,L}$ is holomorphic on $\mathbb{H}^d$** (`IsHolomorphic`: continuous and holomorphic in each variable). -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
theorem isHolomorphic_thetaLatH {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : IsHolomorphic (thetaLatH A 𝔞) := by
  classical
  refine ⟨continuous_thetaLatH hA 𝔞, fun z v => ?_⟩
  rw [UpperHalfPlane.mdifferentiable_iff]
  set Z : InfinitePlace F → ℂ := fun u => (z u : ℂ)
  set g : ℂ → ℂ := fun w => thetaLat A 𝔞 (Function.update Z v w)
  have hg : DifferentiableOn ℂ g {w | 0 < w.im} := by
    intro w0 hw0
    have hw0' : 0 < w0.im := hw0
    set δ := w0.im / 2
    set U : Set ℂ := {w | δ < w.im}
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
    have hw0U : w0 ∈ U := by show δ < w0.im; simp only [δ]; linarith
    set z'' := Function.update Z v ((δ : ℂ) * Complex.I)
    have hz'' : ∀ u, 0 < (z'' u).im := by
      intro u
      by_cases h : u = v
      · subst h; simp [z'', δ, hw0']
      · simp [z'', Function.update_of_ne h, Z, (z u).im_pos]
    have hD : DifferentiableOn ℂ g U := by
      refine differentiableOn_tsum_of_summable_norm (summable_norm_thetaTerm hA 𝔞 hz'')
        (fun k => (differentiable_thetaTerm_update A _ Z v).differentiableOn) hUo
        fun k w hw => norm_thetaTerm_le hA _ fun u => ?_
      by_cases h : u = v
      · subst h; simp [z'']; exact (show δ < w.im from hw).le
      · simp [z'', Function.update_of_ne h]
    exact (hD.differentiableAt (hUo.mem_nhds hw0U)).differentiableWithinAt
  refine hg.congr fun w hw => ?_
  simp only [Function.comp_apply, thetaLatH, g]
  congr 1
  funext u
  by_cases h : u = v
  · subst h; simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  · simp [Function.update_of_ne h, Z]

/-! ### Translations -/

lemma thetaTerm_add (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) (z : InfinitePlace F → ℂ) (β : F)
    (hβ : ∃ m : ℤ, Algebra.trace ℚ F (β * qv A x) = m) :
    thetaTerm A x (fun v => z v + realEmb F v β) = thetaTerm A x z := by
  obtain ⟨m, hm⟩ := hβ
  have hsum : ∑ v, (realEmb F v (qv A x) : ℂ) * (realEmb F v β : ℂ) = (m : ℂ) := by
    have := sum_realEmb (β * qv A x)
    rw [hm] at this
    simp only [map_mul] at this
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) this
    simp only [ofReal_sum, ofReal_mul, Rat.cast_intCast, ofReal_intCast] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [thetaTerm, thetaTerm]
  simp_rw [mul_add, Finset.sum_add_distrib, mul_add, Complex.exp_add, hsum]
  have : cexp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) = m * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [this, mul_one]

/-- **Translation invariance.** If $\operatorname{Tr}_{F/\mathbb{Q}}(\beta Q(x)) \in \mathbb{Z}$ for all $x \in L$ (i.e. $\beta \in \mathfrak n^\vee$
for an ideal $\mathfrak n \supseteq Q(L)$), then $\theta_{A,L}(z + \beta) = \theta_{A,L}(z)$, where $z + \beta = (z_v + \varphi_v(\beta))_v$. -/
theorem thetaLat_add (A : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : InfinitePlace F → ℂ) (β : F)
    (hβ : ∀ k, ∃ m : ℤ, Algebra.trace ℚ F (β * qv A (latVec 𝔞 k)) = m) :
    thetaLat A 𝔞 (fun v => z v + realEmb F v β) = thetaLat A 𝔞 z := by
  unfold thetaLat
  exact tsum_congr fun k => thetaTerm_add A _ z β (hβ k)

/-! ### Forms over $\mathcal{O}_F$ -/

/-- **The Gram matrix over $F$** of a form $Q$ over $\mathcal{O}_F$: $A = \frac12H$, $H = C + C^{\mathsf T}$ the Hessian, so
$Q(x) = x^{\mathsf T}Ax$ (`algebraMap_eval_eq_qv`). -/
def gramF (Q : QuadForm (𝓞 F) n) : Matrix (Fin n) (Fin n) F :=
  (1 / 2 : F) • Q.hessian.map (algebraMap (𝓞 F) F)

lemma algebraMap_eval_eq_qv (Q : QuadForm (𝓞 F) n) (x : Fin n → 𝓞 F) :
    algebraMap (𝓞 F) F (Q.eval x) = qv (gramF Q) fun i => algebraMap (𝓞 F) F (x i) := by
  have h1 : algebraMap (𝓞 F) F (Q.eval x) = Q.evalIn F fun i => algebraMap (𝓞 F) F (x i) := by
    simp only [QuadForm.eval, QuadForm.evalIn, map_sum, apply_ite, map_mul, map_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, QuadForm.evalIn_eq_dotProduct, qv, gramF, QuadForm.hessian, Matrix.map_add _ (map_add _),
    Matrix.transpose_map, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  generalize Q.coeff.map (algebraMap (𝓞 F) F) = C
  generalize (fun i => algebraMap (𝓞 F) F (x i)) = y
  have : y ⬝ᵥ Cᵀ *ᵥ y = y ⬝ᵥ C *ᵥ y := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [this, smul_eq_mul]
  ring

/-- **The theta series of a form $Q$ over $\mathcal{O}_F$** on $\mathbb{H}^d$:
$$\theta_Q(z) = \sum_{x\in\mathcal{O}_F^n}e\big(\operatorname{Tr}(Q(x)z)\big),\qquad
  \operatorname{Tr}(\nu z) = \sum_v\varphi_v(\nu)z_v.$$
For $F = \mathbb{Q}$ it is `QuadFormsKB.Siegel.theta` (one variable). Parameters: `Q` (a form over $\mathcal{O}_F$), `z`. -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
def thetaQ (Q : QuadForm (𝓞 F) n) (z : InfinitePlace F → ℍ) : ℂ :=
  ∑' x : Fin n → 𝓞 F, cexp (2 * Real.pi * Complex.I *
    ∑ v, (realEmb F v (algebraMap (𝓞 F) F (Q.eval x)) : ℂ) * (z v : ℂ))

/-- $\mathcal{O}_F \simeq$ the fractional ideal $(1)$. -/
def oEquivOne : 𝓞 F ≃ ((((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) : Set F) :=
  Equiv.ofBijective (fun r => ⟨algebraMap (𝓞 F) F r, by
      rw [Units.val_one]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩⟩)
    ⟨fun r s h => by
      have := congrArg Subtype.val h
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F this,
    fun ⟨x, hx⟩ => by
      rw [Units.val_one] at hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      exact ⟨r, rfl⟩⟩

/-- Coordinates $\mathbb{Z}^{n\times d} \simeq \mathcal{O}_F^n$, $k \mapsto x$ with $x_i = \sum_lk_{il}\beta_l$. -/
def coordEquivO : (Fin n → Fin (Module.finrank ℚ F) → ℤ) ≃ (Fin n → 𝓞 F) :=
  Equiv.piCongrRight fun _ => (QuadFormsKB.Analysis.latEquiv 1).trans oEquivOne.symm

lemma algebraMap_coordEquivO (k : Fin n → Fin (Module.finrank ℚ F) → ℤ) (i : Fin n) :
    algebraMap (𝓞 F) F (coordEquivO k i) = latVec (fun _ => 1) k i := by
  have h : (oEquivOne (coordEquivO k i) : F) = algebraMap (𝓞 F) F (coordEquivO k i) := rfl
  rw [← h, latVec, ← QuadFormsKB.Analysis.latEquiv_coe]
  simp [coordEquivO]

/-- **$\theta_Q = \theta_{A,\mathcal{O}_F^n}$** for the Gram matrix $A$ = `gramF Q`. -/
theorem thetaQ_eq_thetaLatH (Q : QuadForm (𝓞 F) n) :
    thetaQ Q = thetaLatH (gramF Q) fun _ => 1 := by
  funext z
  rw [thetaQ, thetaLatH, thetaLat, ← (coordEquivO (F := F) (n := n)).tsum_eq]
  refine tsum_congr fun k => ?_
  have h : (fun i => algebraMap (𝓞 F) F (coordEquivO k i)) = latVec (fun _ => 1) k :=
    funext (algebraMap_coordEquivO k)
  rw [thetaTerm, algebraMap_eval_eq_qv, h]

/-- $\theta_Q$ is holomorphic on $\mathbb{H}^d$ for a totally positive definite form $Q$ over $\mathcal{O}_F$. -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
theorem isHolomorphic_thetaQ {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    IsHolomorphic (thetaQ Q) := by
  rw [thetaQ_eq_thetaLatH]; exact isHolomorphic_thetaLatH hQ _

/-- The term of $\theta_Q$ at $x$. -/
abbrev thetaQTerm (Q : QuadForm (𝓞 F) n) (z : InfinitePlace F → ℍ) (x : Fin n → 𝓞 F) : ℂ :=
  cexp (2 * Real.pi * Complex.I * ∑ v, (realEmb F v (algebraMap (𝓞 F) F (Q.eval x)) : ℂ) * (z v : ℂ))

/-- **Absolute convergence** of $\theta_Q$. -/
theorem summable_norm_thetaQTerm {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (z : InfinitePlace F → ℍ) : Summable fun x => ‖thetaQTerm Q z x‖ := by
  have h := summable_norm_thetaTerm hQ (fun _ => 1) (z := fun v => (z v : ℂ)) fun v => (z v).im_pos
  rw [← (coordEquivO (F := F) (n := n)).summable_iff]
  refine h.congr fun k => ?_
  have h' : (fun i => algebraMap (𝓞 F) F (coordEquivO k i)) = latVec (fun _ => 1) k :=
    funext (algebraMap_coordEquivO k)
  simp only [Function.comp_apply, thetaQTerm, thetaTerm, algebraMap_eval_eq_qv, h']

/-- **The representation number** $r_Q(\nu) = \#\{x \in \mathcal{O}_F^n : Q(x) = \nu\}$ (`Nat.card`; finite by `finite_repSetF`). -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
def repNumF (Q : QuadForm (𝓞 F) n) (ν : 𝓞 F) : ℕ := Nat.card {x : Fin n → 𝓞 F // Q.eval x = ν}

/-- **Finiteness of representation numbers** for totally positive definite $Q$. *Proof:* the terms of $\theta_Q$ at
$z = (i, \dots, i)$ have the constant nonzero norm $e^{-2\pi\operatorname{Tr}\nu}$ on $\{Q(x) = \nu\}$ and are summable. -/
theorem finite_repSetF {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (ν : 𝓞 F) :
    {x : Fin n → 𝓞 F | Q.eval x = ν}.Finite := by
  set z : InfinitePlace F → ℍ := fun _ => UpperHalfPlane.I
  have hs := summable_norm_thetaQTerm hQ z
  set c := ‖cexp (2 * Real.pi * Complex.I *
    ∑ v, (realEmb F v (algebraMap (𝓞 F) F ν) : ℂ) * (z v : ℂ))‖
  have hc : 0 < c := by simp [c]
  have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hc)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [thetaQTerm, hx]
  exact lt_irrefl c

/-- **The $q$-expansion of $\theta_Q$**: for $z \in \mathbb{H}^d$,
$$\theta_Q(z) = \sum_{\nu\in\mathcal{O}_F}r_Q(\nu)\,e\big(\operatorname{Tr}(\nu z)\big),$$
an absolutely convergent series (`HasSum` over $\nu \in \mathcal{O}_F$); $r_Q(\nu) = 0$ unless $\nu = 0$ or $\nu \gg 0$
(`repNumF_eq_zero_of_not_totallyPos`). For $F = \mathbb{Q}$: `QuadFormsKB.Siegel.hasSum_theta`. -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
theorem hasSum_thetaQ {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (z : InfinitePlace F → ℍ) :
    HasSum (fun ν : 𝓞 F => (repNumF Q ν : ℂ) *
      cexp (2 * Real.pi * Complex.I * ∑ v, (realEmb F v (algebraMap (𝓞 F) F ν) : ℂ) * (z v : ℂ)))
      (thetaQ Q z) := by
  have h := (summable_norm_thetaQTerm hQ z).of_norm.hasSum.tsum_fiberwise (fun x => Q.eval x)
  convert h using 1
  swap
  · rfl
  funext ν
  have : ∀ x : ((fun x : Fin n → 𝓞 F => Q.eval x) ⁻¹' {ν}),
      thetaQTerm Q z x = cexp (2 * Real.pi * Complex.I *
        ∑ v, (realEmb F v (algebraMap (𝓞 F) F ν) : ℂ) * (z v : ℂ)) := by
    rintro ⟨x, hx⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [thetaQTerm, hx]
  rw [tsum_congr this, tsum_const, nsmul_eq_mul]
  rfl

lemma realEmb_injective' (v : InfinitePlace F) : Function.Injective (realEmb F v) :=
  (realEmb F v).injective

/-- **Support of the $q$-expansion**: $r_Q(\nu) \ne 0 \Rightarrow \nu = 0$ or $\varphi_v(\nu) > 0$ at every place. -/
theorem repNumF_eq_zero_of_not_totallyPos {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    {ν : 𝓞 F} (hν : ν ≠ 0) (hpos : ∃ v, realEmb F v (algebraMap (𝓞 F) F ν) ≤ 0) :
    repNumF Q ν = 0 := by
  rw [repNumF, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx⟩ => ?_⟩
  obtain ⟨v, hv⟩ := hpos
  rw [← hx, algebraMap_eval_eq_qv, realEmb_qv] at hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hν
    rw [← hx]
    simp [QuadForm.eval, QuadForm.evalIn]
  have hy : (fun i => realEmb F v (algebraMap (𝓞 F) F (x i))) ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply, map_eq_zero_iff _ (realEmb_injective' v)] at this
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using this)
  have := (hQ v).dotProduct_mulVec_pos hy
  simp only [star_trivial] at this
  linarith

/-! ### Translations by the inverse different, and the translation part of $\Gamma_0(\mathfrak N)$ -/

lemma trace_mem_int_of_mem_invDifferent {β : F} (hβ : β ∈ invDifferent F) (r : 𝓞 F) :
    ∃ m : ℤ, Algebra.trace ℚ F (β * algebraMap (𝓞 F) F r) = m := by
  have h := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F)
    (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).mp hβ (algebraMap (𝓞 F) F r)
    ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  rw [← Algebra.traceForm_apply, ← hm]
  simp

/-- **$\theta_Q(z + \beta) = \theta_Q(z)$ for $\beta \in \mathfrak d^{-1}$** (the inverse different = trace dual of $\mathcal{O}_F$),
for every form $Q$ over $\mathcal{O}_F$: $\operatorname{Tr}(\beta Q(x)) \in \mathbb{Z}$ since $Q(x) \in \mathcal{O}_F$. Stated for the slash
operator: $\theta_Q\,|_k\,T(\beta) = \theta_Q$ for every weight $k$, $T(\beta) = \begin{pmatrix}1&\beta\\0&1\end{pmatrix}$. -/
@[kb "freitag1990" "Ch. I §4, theta series [unverified]"]
theorem thetaQ_slash_transl (Q : QuadForm (𝓞 F) n) (k : ℤ) {β : F} (hβ : β ∈ invDifferent F) :
    thetaQ Q ∣[k] slHom (realEmb F) (transl β) = thetaQ Q := by
  funext z
  rw [← ptXY_re_im z, slash_transl_ptXY k _ β (imVec_pos z), thetaQ_eq_thetaLatH, thetaLatH,
    thetaLatH]
  have hcoe : (fun v => ((ptXY (reVec z + realVec β) (imVec z) v : ℍ) : ℂ)) =
      fun v => ((ptXY (reVec z) (imVec z) v : ℍ) : ℂ) + realEmb F v β := by
    funext v
    rw [ptXY_coe (imVec_pos z), ptXY_coe (imVec_pos z)]
    simp [realVec]
    ring
  rw [hcoe]
  refine thetaLat_add _ _ _ β fun m => ?_
  have h : latVec (fun _ => 1) m = fun i => algebraMap (𝓞 F) F (coordEquivO m i) :=
    (funext (algebraMap_coordEquivO m)).symm
  rw [h, ← algebraMap_eval_eq_qv]
  exact trace_mem_int_of_mem_invDifferent hβ _

/-- **$\theta_Q$ is invariant under the translations of $\Gamma_0(\mathfrak N)$**: $\theta_Q\,|_k\,T(b) = \theta_Q$ for $b \in \mathcal{O}_F$
($\mathcal{O}_F \subseteq \mathfrak d^{-1}$; `transl_mem_Gamma0`: $T(b) \in \Gamma_0(\mathfrak N)$). -/
theorem thetaQ_slash_transl_int (Q : QuadForm (𝓞 F) n) (k : ℤ) (b : 𝓞 F) :
    thetaQ Q ∣[k] slHom (realEmb F) (transl (algebraMap (𝓞 F) F b)) = thetaQ Q := by
  refine thetaQ_slash_transl Q k ?_
  have h1 : algebraMap (𝓞 F) F b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩
  exact FractionalIdeal.one_le_dual_one ℤ ℚ (L := F) (B := 𝓞 F) h1

end

end QuadFormsKB.HilbertModular
