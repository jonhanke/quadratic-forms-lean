/-
# Complex coordinates on $\mathbb H_r^d$ for the Fourier expansion of Siegel modular forms over $F$
**Layer:** archimedean, over a totally real number field $F$ of degree $d$ (no arithmetic input beyond the basis `oBasis F`).

**Setting.** $J$ = `JR F r` (pairs $(p, k)$: an upper index $p = (i \le i')$ and a basis index $k < d$), $b_k = $ `oBasis F k` $\in \mathbb R^d$ the
real embeddings of a $\mathbb Z$-basis of $\mathcal O_F$ (as in `EisensteinUnfoldCoord.lean`). A complex coordinate vector $t \in \mathbb C^J$ gives the
family of complex symmetric matrices
$$Z(t)_w = \operatorname{symOf}\Big(p \mapsto \sum_kt_{p,k}\,(b_k)_w\Big)\qquad(\texttt{zC}),$$
complex linear in $t$; for $t = x + iy$ ($x, y \in \mathbb R^J$) it is $X(x) + iX(y)$ (`zC_cplx`, with $X$ = `xMat`). The **cone**
$K = \{y \in \mathbb R^J : X(y)_w \text{ positive definite for every } w\}$ (`Kc`) is open, convex and closed under positive scaling, and
$Z(t) \in \mathbb H_r^d$ exactly when $\operatorname{Im}t \in K$ (`zC_mem_iff`). Translation by $n \in \mathbb Z^J$ is translation by the integral
symmetric matrix $\operatorname{symOf}(u_n)$, $u_n \in \mathrm{Sym}_r(\mathcal O_F)$ (`zC_add_int`), and every $Z \in \mathbb H_r^d$ is some $Z(t)$
(`exists_zC_eq`).

Source: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (Fourier expansions of Siegel modular forms) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpTorus
import QuadFormsKB.SiegelWeil.Forms.HolExpPeriodic
import QuadFormsKB.SiegelWeil.Forms.EisensteinLowerCell

open Matrix NumberField Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **The complex coordinates** $Z(t)_w = \operatorname{symOf}(p \mapsto \sum_kt_{p,k}(b_k)_w)$ of a point of (a neighbourhood of) $\mathbb H_r^d$. -/
def zC (t : JR F r → ℂ) : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
  fun w => symOf fun p => ∑ k, t (p, k) * ((oBasis F k w : ℝ) : ℂ)

/-- Real part of a coordinate vector. -/
def reC (t : JR F r → ℂ) : JR F r → ℝ := fun q => (t q).re

/-- Imaginary part of a coordinate vector. -/
def imC (t : JR F r → ℂ) : JR F r → ℝ := fun q => (t q).im

variable (F r) in
/-- **The cone** $K = \{y : X(y)_w \succ 0\ \forall w\}$ of allowed imaginary parts. -/
def Kc : Set (JR F r → ℝ) := {y | ∀ w, (xMat y w).PosDef}

lemma xCoord_apply (x : JR F r → ℝ) (p : SymIdx r) (w : InfinitePlace F) :
    xCoord x p w = ∑ k, x (p, k) * oBasis F k w := by
  simp [xCoord, Module.Basis.equivFun_symm_apply, Finset.sum_apply, smul_eq_mul]

lemma cplx_re_im (t : JR F r → ℂ) : HolExp.cplx (reC t) (imC t) = t := by
  funext q; simp [HolExp.cplx, reC, imC, Complex.re_add_im]

lemma reC_cplx (x y : JR F r → ℝ) : reC (HolExp.cplx x y) = x := by
  funext q; simp [HolExp.cplx, reC]

lemma imC_cplx (x y : JR F r → ℝ) : imC (HolExp.cplx x y) = y := by
  funext q; simp [HolExp.cplx, imC]

/-- $Z(x + iy) = X(x) + iX(y)$. -/
lemma zC_cplx (x y : JR F r → ℝ) : zC (HolExp.cplx x y) = zPt (fun w => xMat y w) x := by
  funext w; ext i j
  simp only [zC, zPt, xMat, symOf, Matrix.add_apply, Matrix.map_apply, of_apply]
  split_ifs <;>
  · simp only [xCoord_apply, HolExp.cplx, add_mul, Finset.sum_add_distrib]
    push_cast
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

lemma zC_eq (t : JR F r → ℂ) : zC t = zPt (fun w => xMat (imC t) w) (reC t) := by
  rw [← zC_cplx, cplx_re_im]

lemma zPt_map_im (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (x : JR F r → ℝ) (w : InfinitePlace F) :
    (zPt Y x w).map Complex.im = Y w := by
  ext i j; simp [zPt]

lemma zC_map_im (t : JR F r → ℂ) (w : InfinitePlace F) : (zC t w).map Complex.im = xMat (imC t) w := by
  rw [zC_eq, zPt_map_im]

lemma zC_transpose (t : JR F r → ℂ) (w : InfinitePlace F) : (zC t w)ᵀ = zC t w := symOf_transpose _

/-- $Z(t) \in \mathbb H_r^d$ iff $\operatorname{Im}t \in K$. -/
lemma zC_mem_iff (t : JR F r → ℂ) : zC t ∈ siegelHF F r ↔ imC t ∈ Kc F r := by
  constructor
  · intro h w
    have := (h w).2
    rwa [zC_map_im] at this
  · intro h
    rw [zC_eq]
    exact zPt_mem_siegelHF _ h _

lemma zC_add (t s : JR F r → ℂ) : zC (t + s) = fun w => zC t w + zC s w := by
  funext w; ext i j
  simp only [zC, symOf, Matrix.add_apply, of_apply, Pi.add_apply]
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]

lemma zC_smul (c : ℂ) (t : JR F r → ℂ) : zC (c • t) = fun w => c • zC t w := by
  funext w; ext i j
  simp only [zC, symOf, Matrix.smul_apply, of_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Finset.mul_sum, mul_assoc]

/-- Moving one coordinate: $Z(t[q \mapsto s]) = Z(t) + (s - t_q)Z(e_q)$. -/
lemma zC_update (t : JR F r → ℂ) (q : JR F r) (s : ℂ) :
    zC (Function.update t q s) = fun w => zC t w + (s - t q) • zC (Pi.single q 1) w := by
  have : Function.update t q s = t + (s - t q) • Pi.single q 1 := by
    funext q'
    by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  rw [this, zC_add, zC_smul]

lemma zC_intCast (n : JR F r → ℤ) :
    zC (fun q => ((n q : ℤ) : ℂ)) = fun w => (symOf (symOEquiv n : SymIdx r → F)).map fun x => (realEmb F w x : ℂ) := by
  have h1 : (fun q => ((n q : ℤ) : ℂ)) = HolExp.cplx (fun q => (n q : ℝ)) 0 := by
    funext q; simp [HolExp.cplx]
  rw [h1, zC_cplx]
  funext w
  have h2 := xMat_tOf (symOEquiv n : SymIdx r → F) w
  rw [tOf_symOEquiv] at h2
  have h3 : xMat (0 : JR F r → ℝ) w = 0 := by
    have := xMat_add (0 : JR F r → ℝ) 0 w
    simp only [add_zero] at this
    exact left_eq_add.mp this
  rw [zPt, h2, h3]
  ext i j
  simp [realMat]

/-- Translation by $n \in \mathbb Z^J$ is translation by the integral symmetric matrix $\operatorname{symOf}(u_n)$. -/
lemma zC_add_int (t : JR F r → ℂ) (n : JR F r → ℤ) :
    zC (t + fun q => ((n q : ℤ) : ℂ)) = addB (symOf (symOEquiv n : SymIdx r → F)) (zC t) := by
  rw [zC_add, zC_intCast]; rfl

lemma imC_add_int (t : JR F r → ℂ) (n : JR F r → ℤ) : imC (t + fun q => ((n q : ℤ) : ℂ)) = imC t := by
  funext q; simp [imC]

lemma continuous_zC_apply (w : InfinitePlace F) : Continuous fun t : JR F r → ℂ => zC t w := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [zC, symOf, of_apply]
  split_ifs <;>
  · exact continuous_finsetSum _ fun k _ => (continuous_apply _).mul continuous_const

lemma continuous_imC : Continuous (imC : (JR F r → ℂ) → JR F r → ℝ) :=
  continuous_pi fun q => Complex.continuous_im.comp (continuous_apply q)

/-! ### The cone $K$ -/

lemma isOpen_posDef_of_continuous' {X : Type*} [TopologicalSpace X] {n : ℕ} {M : X → Matrix (Fin n) (Fin n) ℝ}
    (hM : Continuous M) (hsym : ∀ x, (M x)ᵀ = M x) : IsOpen {x | (M x).PosDef} := by
  refine isOpen_iff_mem_nhds.mpr fun x₀ hx₀ => ?_
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hcont : Continuous fun p : X × (Fin n → ℝ) => p.2 ⬝ᵥ (M p.1 *ᵥ p.2) :=
    continuous_snd.dotProduct ((hM.comp continuous_fst).matrix_mulVec continuous_snd)
  have hpd := (posDef_iff_dotProduct_mulVec.mp hx₀).2
  have h0 : ∀ v ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      ∀ᶠ p : X × (Fin n → ℝ) in 𝓝 (x₀, v), 0 < p.2 ⬝ᵥ (M p.1 *ᵥ p.2) := by
    intro v hv
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    refine hcont.continuousAt.eventually (lt_mem_nhds ?_)
    have := hpd hv0; rwa [star_trivial] at this
  have h1 := hS.eventually_forall_of_forall_eventually (P := fun x v => 0 < v ⬝ᵥ (M x *ᵥ v)) h0
  filter_upwards [h1] with x hx
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hsym x, fun v hv => ?_⟩
  rw [star_trivial]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have := hx _ hw
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  have h2 : 0 < ‖v‖⁻¹ * ‖v‖⁻¹ := by positivity
  nlinarith

lemma continuous_xMat (w : InfinitePlace F) : Continuous fun y : JR F r → ℝ => xMat y w :=
  continuous_pi fun i => continuous_pi fun j => continuous_xMat_apply w i j

lemma isOpen_Kc : IsOpen (Kc F r) := by
  have : Kc F r = ⋂ w, {y : JR F r → ℝ | (xMat y w).PosDef} := by
    ext y; simp [Kc]
  rw [this]
  exact isOpen_iInter_of_finite fun w =>
    isOpen_posDef_of_continuous' (continuous_xMat w) fun y => symOf_transpose _

lemma xMat_smul (c : ℝ) (y : JR F r → ℝ) (w : InfinitePlace F) : xMat (c • y) w = c • xMat y w := by
  ext i j
  simp only [xMat, symOf, of_apply, Matrix.smul_apply, xCoord_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Finset.mul_sum, mul_assoc]

lemma smul_mem_Kc {y : JR F r → ℝ} (hy : y ∈ Kc F r) {c : ℝ} (hc : 0 < c) : c • y ∈ Kc F r := fun w => by
  rw [xMat_smul]; exact (hy w).smul hc

lemma add_mem_Kc {y y' : JR F r → ℝ} (hy : y ∈ Kc F r) (hy' : y' ∈ Kc F r) : y + y' ∈ Kc F r := fun w => by
  rw [xMat_add]; exact (hy w).add (hy' w)

lemma convex_Kc : Convex ℝ (Kc F r) := by
  rw [convex_iff_forall_pos]
  intro y hy y' hy' a b ha hb _
  exact add_mem_Kc (smul_mem_Kc hy ha) (smul_mem_Kc hy' hb)

/-- Every $Z \in \mathbb H_r^d$ is $Z(t)$ for some $t$ (with $\operatorname{Im}t \in K$). -/
lemma exists_zC_eq {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    ∃ t : JR F r → ℂ, zC t = Z := by
  obtain ⟨sx, hsx⟩ := exists_xMat_eq (fun w => (Z w).map Complex.re) (fun w => by
    rw [← Matrix.transpose_map, (hZ w).1])
  obtain ⟨sy, hsy⟩ := exists_xMat_eq (fun w => (Z w).map Complex.im) (fun w => by
    rw [← Matrix.transpose_map, (hZ w).1])
  refine ⟨HolExp.cplx sx sy, ?_⟩
  rw [zC_cplx]
  funext w; ext i j
  simp only [zPt, Matrix.add_apply, Matrix.map_apply, hsx, hsy]
  exact Complex.re_add_im _

/-- A point of the cone: $X(y_1)_w = 1$ at every place. -/
lemma exists_mem_Kc : ∃ y : JR F r → ℝ, y ∈ Kc F r := by
  obtain ⟨y, hy⟩ := exists_xMat_eq (F := F) (r := r) (fun _ => 1) (fun _ => transpose_one)
  exact ⟨y, fun w => by rw [hy]; exact PosDef.one⟩

end QuadFormsKB.SiegelWeil.Forms
