/-
# The degree-$r$ theta series of a lattice over a totally real field and its Fourier expansion (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$; classical analysis (absolute convergence) on the product
$\mathbb H_r^d$ of Siegel upper half spaces, $d = [F:\mathbb Q]$.

**Setting.** $Q$ a totally positive definite quadratic form on $F^n$ (`Lattices.IsTotallyPosDef`), $M \subseteq F^n$ an
$\mathcal O_F$-lattice, $1 \le r$ not needed (every $r \ge 0$). Points of $M^r$ are matrices $X \in F^{n\times r}$ whose columns
$x_0, \dots, x_{r-1}$ lie in $M$ (0-based indices); $Q[X] = Q\circ X$ (`QuadForm.compMat`) is the form $y \mapsto Q(Xy)$ in $r$ variables,
with Gram matrix $\tfrac12H_{Q[X]} = X^{\mathsf T}(\tfrac12H_Q)X$, $H$ the Hessian. For $Z = (Z_v)_v$, $Z_v \in \mathbb H_r$ one per real place
$v$ (with embedding $\sigma_v$) and a form $T$ in $r$ variables over $F$,
$$e_T(Z) = \exp\Big(2\pi i\sum_v\operatorname{tr}\big(\sigma_v(T_G)Z_v\big)\Big),\qquad T_G = \tfrac12H_T\ \text{(the Gram matrix of $T$)}.$$

**Definitions.**
* `thetaR Q M Z` $= \theta_M(Z) = \sum_{X\in M^r}e_{Q[X]}(Z)$, the **degree-$r$ (Hilbert–Siegel) theta series** of $M$;
* `thetaGenR Q L Z` $= \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\theta_M(Z)/|O(M)|$, the genus average.

**Results.**
* `exists_coercive`: a real positive definite $Y$ has $w^{\mathsf T}Yw \ge c\,w^{\mathsf T}w$ for some $c > 0$.
* `summable_norm_thetaRTerm`: **absolute convergence** of $\theta_M$ on $\mathbb H_r^d$.
* **`hasSum_thetaR`** (the **Fourier expansion**): $\theta_M(Z) = \sum_Tr_M(T)\,e_T(Z)$, summed over all forms $T$ in $r$ variables over
  $F$, with $r_M(T) = \#\{X \in M^r : Q[X] = T\}$ (`Tamagawa.Frames.repCountT`).
* **`hasSum_thetaGenR`**: $\theta_{\mathrm{gen}(L)}(Z) = \sum_T\frac{\mathrm{repMassT}(L, T)}{\mathrm{Mass}(L)}\,e_T(Z)$, the coefficients being Siegel's
  weighted averages $\sum_{\mathrm{cls}(M)}r_M(T)/|O(M)|$ divided by the mass.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935), §1 (the genus average of
representation numbers of forms) [unverified]; Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (theta series of degree $r$)
[unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.SiegelFormsWhittaker
import QuadFormsKB.HilbertModular.GenusTheta
import QuadFormsKB.Weil.Genus.SiegelSpace

open Matrix NumberField Complex IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Coercivity of a positive definite matrix -/

/-- **Coercivity:** a real positive definite matrix $Y$ satisfies $w^{\mathsf T}Yw \ge c\,w^{\mathsf T}w$ for some $c > 0$ (the minimum of
$w^{\mathsf T}Yw$ on the compact unit sphere). -/
lemma exists_coercive {r : ℕ} {Y : Matrix (Fin r) (Fin r) ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin r → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ Y *ᵥ w := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, one_pos, fun w => by simp [dotProduct]⟩
  set S : Set (Fin r → ℝ) := {w | w ⬝ᵥ w = 1}
  have hcont : Continuous fun w : Fin r → ℝ => w ⬝ᵥ Y *ᵥ w := by
    simp only [dotProduct, mulVec]; fun_prop
  have hsq : ∀ (w : Fin r → ℝ) i, w i ^ 2 ≤ w ⬝ᵥ w := by
    intro w i
    have := Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg (w j))
      (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by simp only [dotProduct]; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℝ)) (r := 1)).subset fun w hw => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 := hsq w i
      have hw' : w ⬝ᵥ w = 1 := hw
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs (w i), abs_nonneg (w i)]
  have hS : S.Nonempty := ⟨Pi.single ⟨0, hr⟩ 1, by simp [S, dotProduct, Pi.single_apply]⟩
  obtain ⟨w0, hw0, hmin⟩ := hSc.exists_isMinOn hS hcont.continuousOn
  have hw0ne : w0 ≠ 0 := by
    rintro rfl
    simp [S, dotProduct] at hw0
  have hc : 0 < w0 ⬝ᵥ Y *ᵥ w0 := by simpa using hY.dotProduct_mulVec_pos hw0ne
  refine ⟨_, hc, fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw; simp
  have hpos : 0 < w ⬝ᵥ w := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have := hsq w i
    have hi' : w i ≠ 0 := hi
    have : 0 < w i ^ 2 := by positivity
    linarith
  set t := Real.sqrt (w ⬝ᵥ w)
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have htt : t * t = w ⬝ᵥ w := Real.mul_self_sqrt hpos.le
  have hu : t⁻¹ • w ∈ S := by
    show (t⁻¹ • w) ⬝ᵥ (t⁻¹ • w) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← htt]
    field_simp
  have h := hmin hu
  simp only [Set.mem_ofPred_eq] at h
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
  rw [← htt]
  have e : t⁻¹ * (t⁻¹ * (w ⬝ᵥ Y *ᵥ w)) * (t * t) = w ⬝ᵥ Y *ᵥ w := by field_simp
  calc w0 ⬝ᵥ Y *ᵥ w0 * (t * t) ≤ t⁻¹ * (t⁻¹ * (w ⬝ᵥ Y *ᵥ w)) * (t * t) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = w ⬝ᵥ Y *ᵥ w := e

lemma sum_gram_aux {n r : ℕ} (W : Matrix (Fin n) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin r) ℝ) :
    ∑ i, ∑ j, (Wᵀ * W) i j * Y i j = ∑ a, (fun j => W a j) ⬝ᵥ Y *ᵥ (fun j => W a j) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma sum_col_aux {n r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin r) ℝ) :
    ∑ j, (fun i => X i j) ⬝ᵥ (Cᵀ * C) *ᵥ (fun i => X i j) =
      ∑ a, (fun j => (C * X) a j) ⬝ᵥ (fun j => (C * X) a j) := by
  have h : ∀ j, (fun i => X i j) ⬝ᵥ (Cᵀ * C) *ᵥ (fun i => X i j) =
      ∑ a, (C * X) a j * (C * X) a j := by
    intro j
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct, mulVec, mul_apply]
  rw [Finset.sum_congr rfl fun j _ => h j]
  simp only [dotProduct]
  exact Finset.sum_comm

/-- **The trace bound:** for $A = C^{\mathsf T}C$ and $Y$ with $w^{\mathsf T}Yw \ge c\,w^{\mathsf T}w$,
$\sum_{i,j}(X^{\mathsf T}AX)_{ij}Y_{ij} \ge c\sum_jx_j^{\mathsf T}Ax_j$, $x_j$ the columns of $X$. -/
lemma sum_gram_mul_ge {n r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin r) (Fin r) ℝ) {c : ℝ}
    (hc : ∀ w : Fin r → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ Y *ᵥ w) (X : Matrix (Fin n) (Fin r) ℝ) :
    c * ∑ j, (fun i => X i j) ⬝ᵥ (Cᵀ * C) *ᵥ (fun i => X i j) ≤
      ∑ i, ∑ j, (Xᵀ * (Cᵀ * C) * X) i j * Y i j := by
  have hW : Xᵀ * (Cᵀ * C) * X = (C * X)ᵀ * (C * X) := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [hW, sum_gram_aux, sum_col_aux, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => hc _

/-- Finite products of a summable nonnegative family are summable over $\alpha^m$. -/
lemma summable_prod_fin' {α : Type*} (g : α → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    ∀ m : ℕ, Summable fun n : Fin m → α => ∏ i, g (n i)
  | 0 => Summable.of_finite
  | m + 1 => by
    have ih := summable_prod_fin' g hg0 hg m
    have h2 := Summable.mul_of_nonneg hg ih hg0 (fun n => Finset.prod_nonneg fun i _ => hg0 _)
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).summable_iff]
    convert h2 using 1
    funext p
    simp [Fin.prod_univ_succ, Fin.consEquiv]

/-! ### The degree-$r$ theta series over $F$ -/

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n r : ℕ}

/-- **The Gram matrix** $T_G = \tfrac12H_T$ of a form $T$ over $F$, $H_T = C + C^{\mathsf T}$ the Hessian; $T(y) = y^{\mathsf T}T_Gy$
(`eval_eq_gramT`). -/
def gramT (T : QuadForm F r) : Matrix (Fin r) (Fin r) F := (1 / 2 : F) • T.hessian

lemma gramT_transpose (T : QuadForm F r) : (gramT T)ᵀ = gramT T := by
  rw [gramT, transpose_smul, QuadForm.hessian, transpose_add, transpose_transpose, add_comm]

lemma eval_eq_gramT (T : QuadForm F r) (y : Fin r → F) : T.eval y = y ⬝ᵥ gramT T *ᵥ y := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct, gramT, QuadForm.hessian, smul_mulVec, dotProduct_smul,
    add_mulVec, dotProduct_add]
  have hm : T.coeff.map (algebraMap F F) = T.coeff := by ext; simp
  rw [hm]
  have : y ⬝ᵥ T.coeffᵀ *ᵥ y = y ⬝ᵥ T.coeff *ᵥ y := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [this, smul_eq_mul]
  ring

/-- $Q[X]_G = X^{\mathsf T}Q_GX$. -/
lemma gramT_compMat (Q : QuadForm F n) (X : Matrix (Fin n) (Fin r) F) :
    gramT (Q.compMat X) = Xᵀ * gramT Q * X := by
  rw [gramT, gramT, QuadForm.hessian_compMat, Matrix.mul_smul, Matrix.smul_mul]

/-- **The trace pairing** $\sum_v\operatorname{tr}\big(\sigma_v(T_G)Z_v\big) = \sum_v\sum_{i,j}\sigma_v(T_G)_{ij}(Z_v)_{ji}$ of a form $T$ in $r$ variables
over $F$ with $Z = (Z_v)_v$, $Z_v \in M_r(\mathbb C)$, one matrix per real place $v$. -/
def trPair (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑ v, ∑ i, ∑ j, (realEmb F v (gramT T i j) : ℂ) * Z v j i

/-- **The exponential** $e_T(Z) = \exp\big(2\pi i\sum_v\operatorname{tr}(\sigma_v(T_G)Z_v)\big)$. -/
def eT (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  cexp (2 * Real.pi * I * trPair T Z)

/-- **The product of Siegel upper half spaces** $\mathbb H_r^d$: $Z = (Z_v)_v$ with $Z_v \in \mathbb H_r$ (`WeilRep.Genus.siegelH`: symmetric,
positive definite imaginary part) at every real place $v$. -/
def siegelHF (F : Type) [Field F] [NumberField F] (r : ℕ) : Set (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :=
  {Z | ∀ v, Z v ∈ WeilRep.Genus.siegelH r}

/-- **$M^r$**: the matrices $X \in F^{n\times r}$ whose columns $x_0, \dots, x_{r-1}$ lie in $M$. -/
abbrev frames (M : Submodule (𝓞 F) (Fin n → F)) (r : ℕ) : Type :=
  {X : Matrix (Fin n) (Fin r) F // ∀ j, (fun i => X i j) ∈ M}

/-- **The degree-$r$ theta series of a lattice** $M \subseteq F^n$ for a form $Q$ on $F^n$:
$$\theta_M(Z) = \sum_{X\in M^r}e_{Q[X]}(Z) = \sum_{X\in M^r}\exp\Big(2\pi i\sum_v\operatorname{tr}\big(\sigma_v(X^{\mathsf T}Q_GX)Z_v\big)\Big),\qquad
  Z \in \mathbb H_r^d$$
(`tsum`; absolutely convergent for $Q$ totally positive definite, `summable_norm_thetaRTerm`). For $r = 1$ it is the Hilbert theta series
`HilbertModular.thetaLatt`. Parameters: `Q` (the form on $F^n$), `M` (the lattice), `Z` (a point of $\mathbb H_r^d$). -/
@[kb "freitag1983" "Ch. I (theta series of degree $r$), over a totally real field [unverified]"]
def thetaR (Q : QuadForm F n) (M : Submodule (𝓞 F) (Fin n → F)) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑' X : frames M r, eT (Q.compMat X.1) Z

lemma norm_eT (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    ‖eT T Z‖ = Real.exp (-(2 * Real.pi) * ∑ v, ∑ i, ∑ j, realEmb F v (gramT T i j) * (Z v j i).im) := by
  rw [eT, Complex.norm_exp]
  congr 1
  simp only [trPair, Finset.mul_sum, re_sum]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_re, mul_im]

/-- **Positive definiteness at every real place:** for $Q$ totally positive definite on $F^n$, $\sigma_v(Q_G)$ is positive definite. -/
lemma posDef_gramT {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (v : InfinitePlace F) :
    ((gramT Q).map (realEmb F v)).PosDef := by
  set B := (gramT Q).map (realEmb F v) with hBdef
  have hpos : ∀ x : Fin n → F, x ≠ 0 →
      0 < (fun i => realEmb F v (x i)) ⬝ᵥ B *ᵥ (fun i => realEmb F v (x i)) := by
    intro x hx
    have h := hQ x hx (complexEmb v)
    rw [complexEmb_apply] at h
    have h' : 0 < realEmb F v (Q.eval x) := by exact_mod_cast h
    rw [eval_eq_gramT] at h'
    have e : realEmb F v (x ⬝ᵥ gramT Q *ᵥ x) =
        (fun i => realEmb F v (x i)) ⬝ᵥ B *ᵥ (fun i => realEmb F v (x i)) := by
      simp only [B, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
    rwa [e] at h'
  have hB : B.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, hBdef, ← transpose_map, gramT_transpose]
  have hdet : (gramT Q).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hpos x hx
    have e : B *ᵥ (fun i => realEmb F v (x i)) = 0 := by
      funext i
      have := congrArg (realEmb F v) (congrFun hAx i)
      simpa [B, mulVec, dotProduct, map_sum] using this
    rw [e, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hdetB : B.det ≠ 0 := by
    rw [hBdef, show ((gramT Q).map (realEmb F v)).det = realEmb F v (gramT Q).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (realEmb F v).injective).mpr hdet
  have hsemi : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ B *ᵥ y := by
    have hdense : DenseRange (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    intro y
    refine hdense.induction_on y ?_ ?_
    · exact isClosed_le continuous_const (by simp only [dotProduct, mulVec]; fun_prop)
    · intro q
      by_cases hq : q = 0
      · subst hq; simp [Pi.map, dotProduct]
      · have hx : (fun i => ((q i : ℚ) : F)) ≠ 0 := by
          intro h0; apply hq; funext i
          have := congrFun h0 i
          simpa using this
        have h1 := (hpos _ hx).le
        have hφ : (fun i => realEmb F v ((q i : ℚ) : F)) = Pi.map (fun _ (q : ℚ) => (q : ℝ)) q := by
          funext i; simp [Pi.map]
        rw [hφ] at h1
        exact h1
  have hps : B.PosSemidef := posSemidef_iff_dotProduct_mulVec.mpr ⟨hB, fun y => by
    simpa [star_trivial] using hsemi y⟩
  exact hps.posDef_iff_det_ne_zero.mpr hdetB

/-- **A Gaussian sum over a lattice:** $\sum_{x\in M}\exp\big(-\kappa\sum_v\sum_i\sigma_v(x_i)^2\big) < \infty$ for $\kappa > 0$
($kM \subseteq \mathcal O_F^n$ for some $k \in \mathbb Z\setminus0$, and the theta series of $\sum_ix_i^2$ on $\mathcal O_F^n$ converges). -/
lemma summable_gauss_lat {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F) {κ : ℝ} (hκ : 0 < κ) :
    Summable fun x : M => Real.exp (-κ * ∑ v, ∑ i, realEmb F v ((x : Fin n → F) i) ^ 2) := by
  obtain ⟨k, hk0, -, hk⟩ := exists_int_global_bounds hM
  have hex : ∀ x : M, ∃ y : Fin n → 𝓞 F, intCoe y = (k : 𝓞 F) • (x : Fin n → F) :=
    fun x => mem_intVec_iff_exists.mp (hk _ x.2)
  choose φ hφ using hex
  have hkF : (k : F) ≠ 0 := by exact_mod_cast hk0
  have hsmul : ∀ x : M, (k : 𝓞 F) • (x : Fin n → F) = (k : F) • (x : Fin n → F) := by
    intro x; funext i; simp [Algebra.smul_def]
  have hinj : Function.Injective φ := by
    intro x x' h
    have := congrArg intCoe h
    rw [hφ, hφ, hsmul, hsmul] at this
    exact Subtype.ext (smul_right_injective _ hkF this)
  set t : ℝ := κ / (2 * Real.pi * (k : ℝ) ^ 2)
  have hkR : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have ht : 0 < t := by positivity
  set z : InfinitePlace F → ℂ := fun _ => (t : ℂ) * I
  have hz : ∀ v, 0 < (z v).im := fun v => by simpa [z] using ht
  have hA : IsTotPosGram (1 : Matrix (Fin n) (Fin n) F) := fun v => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]; exact PosDef.one
  have h0 := summable_norm_thetaTerm hA (fun _ => 1) hz
  rw [← (coordEquivO (F := F) (n := n)).symm.summable_iff] at h0
  have h1 := h0.comp_injective hinj
  refine h1.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [norm_thetaTerm]
  have hl : latVec (fun _ => 1) (coordEquivO.symm (φ x)) = intCoe (φ x) := by
    funext i
    rw [← algebraMap_coordEquivO, Equiv.apply_symm_apply]
  rw [hl, hφ, hsmul]
  congr 1
  simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
    zero_mul, add_zero, HilbertModular.qv, one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    map_intCast, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [t]
  field_simp

/-- **The main bound:** for $Q$ totally positive definite and $Z \in \mathbb H_r^d$ there is $\kappa > 0$ with
$|e_{Q[X]}(Z)| \le \prod_j\exp\big(-\kappa\sum_v\sum_i\sigma_v(X_{ij})^2\big)$ for every $X \in F^{n\times r}$. *Proof:* at each place
$\sigma_v(Q_G) = C^{\mathsf T}C$ (`WeilRep.Genus.exists_eq_transpose_mul`), $\operatorname{Im}Z_v \ge \lambda_v$ and $\sigma_v(Q_G) \ge \mu_v$ (`exists_coercive`), and
`sum_gram_mul_ge`. -/
lemma exists_bound_eT {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ X : Matrix (Fin n) (Fin r) F,
      ‖eT (Q.compMat X) Z‖ ≤ ∏ j, Real.exp (-κ * ∑ v, ∑ i, realEmb F v (X i j) ^ 2) := by
  have hC : ∀ v : InfinitePlace F, ∃ C : Matrix (Fin n) (Fin n) ℝ, (gramT Q).map (realEmb F v) = Cᵀ * C :=
    fun v => let ⟨C, hC, _⟩ := WeilRep.Genus.exists_eq_transpose_mul (posDef_gramT hQ v); ⟨C, hC⟩
  choose C hCeq using hC
  have hl : ∀ v : InfinitePlace F, ∃ c : ℝ, 0 < c ∧
      ∀ w : Fin r → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((Z v).map Complex.im) *ᵥ w :=
    fun v => exists_coercive (hZ v).2
  choose lam hlam0 hlam using hl
  have hm : ∀ v : InfinitePlace F, ∃ c : ℝ, 0 < c ∧
      ∀ w : Fin n → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((gramT Q).map (realEmb F v)) *ᵥ w :=
    fun v => exists_coercive (posDef_gramT hQ v)
  choose mu hmu0 hmu using hm
  set κ0 := Finset.univ.inf' Finset.univ_nonempty (fun v => lam v * mu v) with hκ0def
  have hκ0 : 0 < κ0 := (Finset.lt_inf'_iff _).mpr fun v _ => mul_pos (hlam0 v) (hmu0 v)
  refine ⟨2 * Real.pi * κ0, by positivity, fun X => ?_⟩
  rw [norm_eT, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hv : ∀ v, κ0 * ∑ j, ∑ i, realEmb F v (X i j) ^ 2 ≤
      ∑ i, ∑ j, realEmb F v (gramT (Q.compMat X) i j) * (Z v j i).im := by
    intro v
    set Xv := X.map (realEmb F v)
    set Y := (Z v).map Complex.im
    have hsym : ∀ i j, (Z v j i).im = Y i j := by
      intro i j
      have h := congrFun (congrFun (hZ v).1 i) j
      simp only [transpose_apply] at h
      simp only [Y, Matrix.map_apply, h]
    have hGm : (Xᵀ * gramT Q * X).map (realEmb F v) = Xvᵀ * ((C v)ᵀ * C v) * Xv := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hCeq v, transpose_map]
    have hG : ∀ i j, realEmb F v (gramT (Q.compMat X) i j) = (Xvᵀ * ((C v)ᵀ * C v) * Xv) i j := by
      intro i j
      rw [gramT_compMat, ← hGm, Matrix.map_apply]
    have hS : ∑ j, ∑ i, realEmb F v (X i j) ^ 2 = ∑ j, (fun i => Xv i j) ⬝ᵥ (fun i => Xv i j) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      simp [Xv, sq]
    have hS0 : 0 ≤ ∑ j, ∑ i, realEmb F v (X i j) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hle : κ0 ≤ lam v * mu v := Finset.inf'_le _ (Finset.mem_univ v)
    have hmu' : mu v * ∑ j, (fun i => Xv i j) ⬝ᵥ (fun i => Xv i j) ≤
        ∑ j, (fun i => Xv i j) ⬝ᵥ ((C v)ᵀ * C v) *ᵥ (fun i => Xv i j) := by
      rw [Finset.mul_sum, ← hCeq v]
      exact Finset.sum_le_sum fun j _ => hmu v _
    have hgram := sum_gram_mul_ge (C v) Y (hlam v) Xv
    calc κ0 * ∑ j, ∑ i, realEmb F v (X i j) ^ 2 ≤ lam v * mu v * ∑ j, ∑ i, realEmb F v (X i j) ^ 2 :=
          mul_le_mul_of_nonneg_right hle hS0
      _ = lam v * (mu v * ∑ j, (fun i => Xv i j) ⬝ᵥ (fun i => Xv i j)) := by rw [hS]; ring
      _ ≤ lam v * ∑ j, (fun i => Xv i j) ⬝ᵥ ((C v)ᵀ * C v) *ᵥ (fun i => Xv i j) :=
          mul_le_mul_of_nonneg_left hmu' (hlam0 v).le
      _ ≤ ∑ i, ∑ j, (Xvᵀ * ((C v)ᵀ * C v) * Xv) i j * Y i j := hgram
      _ = ∑ i, ∑ j, realEmb F v (gramT (Q.compMat X) i j) * (Z v j i).im := by
          simp only [hG, hsym]
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hv v
  rw [← Finset.mul_sum] at hsum
  calc -(2 * Real.pi) * ∑ v, ∑ i, ∑ j, realEmb F v (gramT (Q.compMat X) i j) * (Z v j i).im
        ≤ -(2 * Real.pi) * (κ0 * ∑ v, ∑ j, ∑ i, realEmb F v (X i j) ^ 2) :=
          mul_le_mul_of_nonpos_left hsum (by linarith [Real.pi_pos])
    _ = ∑ j, -(2 * Real.pi * κ0) * ∑ v, ∑ i, realEmb F v (X i j) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring

/-- $M^r \simeq (\text{Fin } r \to M)$, $X \mapsto$ its columns. -/
def framesEquiv (M : Submodule (𝓞 F) (Fin n → F)) (r : ℕ) : frames M r ≃ (Fin r → M) where
  toFun X j := ⟨fun i => X.1 i j, X.2 j⟩
  invFun c := ⟨Matrix.of fun i j => (c j : Fin n → F) i, fun j => by simp⟩
  left_inv X := rfl
  right_inv c := rfl

/-- **Absolute convergence** of the degree-$r$ theta series on $\mathbb H_r^d$ for $Q$ totally positive definite and $M$ a lattice. -/
@[kb "freitag1983" "Ch. I (convergence of theta series of degree $r$) [unverified]"]
theorem summable_norm_thetaRTerm {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hM : M.IsLattice F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Summable fun X : frames M r => ‖eT (Q.compMat X.1) Z‖ := by
  obtain ⟨κ, hκ, hb⟩ := exists_bound_eT hQ hZ
  have hg := summable_gauss_lat hM hκ
  have hp := summable_prod_fin' _ (fun _ => (Real.exp_pos _).le) hg r
  have hp' := (framesEquiv M r).summable_iff.mpr hp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun X => hb X.1) hp'

/-- **The Fourier expansion of the degree-$r$ theta series:** $\theta_M(Z) = \sum_Tr_M(T)\,e_T(Z)$, summed over all forms $T$ in $r$ variables
over $F$, with $r_M(T) = \#\{X \in M^r : Q[X] = T\}$ (`Tamagawa.Frames.repCountT`). *Proof:* group the absolutely convergent series by
the value of $Q[X]$ (`HasSum.tsum_fiberwise`). -/
@[kb "siegel1935" "§1 (Fourier coefficients of the theta series of degree $r$ = representation numbers) [unverified]"]
theorem hasSum_thetaR {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (M : Lat F n)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    HasSum (fun T : QuadForm F r => (repCountT Q M T : ℂ) * eT T Z) (thetaR Q M.1 Z) := by
  have hs : Summable fun X : frames M.1 r => eT (Q.compMat X.1) Z :=
    (summable_norm_thetaRTerm hQ M.2 hZ).of_norm
  have h := hs.hasSum.tsum_fiberwise (fun X : frames M.1 r => Q.compMat X.1)
  unfold thetaR
  convert h using 1
  funext T
  have e1 : (∑' b : (fun X : frames M.1 r => Q.compMat X.1) ⁻¹' {T}, eT (Q.compMat b.1.1) Z) =
      ∑' _ : (fun X : frames M.1 r => Q.compMat X.1) ⁻¹' {T}, eT T Z :=
    tsum_congr fun b => by rw [show Q.compMat b.1.1 = T from b.2]
  rw [e1, tsum_const, nsmul_eq_mul]
  congr 2
  refine Nat.card_congr
    { toFun := fun X => ⟨⟨X.1, X.2.1⟩, X.2.2⟩
      invFun := fun X => ⟨X.1.1, X.1.2, X.2⟩
      left_inv := fun X => rfl
      right_inv := fun X => rfl }

/-- **The genus average of the degree-$r$ theta series** (Siegel's average):
$$\theta_{\mathrm{gen}(L)}(Z) = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M(Z)}{|O(M)|},$$
over the classes in the genus (`Lattices.genusClasses`, a `finsum`), $\theta_M$ for the representative `c.out`, $O(M)$ the full orthogonal group
(`LatClass.autCard`). For $r = 1$ it is `HilbertModular.thetaGen`. Parameters: `Q` (the form on $F^n$), `L` (the lattice), `Z`. -/
@[kb "siegel1935" "the genus theta series of degree $r$ (Siegel's average) [unverified]"]
def thetaGenR (Q : QuadForm F n) (L : Lat F n) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ((mass Q L : ℝ) : ℂ)⁻¹ * ∑ᶠ c ∈ genusClasses Q L, ((LatClass.autCard Q c : ℂ))⁻¹ * thetaR Q c.out.1 Z

lemma latClass_repCountT_eq (Q : QuadForm F n) (c : LatClass Q) (T : QuadForm F r) :
    LatClass.repCountT Q c T = repCountT Q c.out T := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The Fourier expansion of the genus average:** $\theta_{\mathrm{gen}(L)}(Z) = \sum_T\frac{\mathrm{repMassT}(L, T)}{\mathrm{Mass}(L)}\,e_T(Z)$ with
$\mathrm{repMassT}(L, T) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}r_M(T)/|O(M)|$, for $Q$ totally positive definite and $L$ integral. -/
@[kb "siegel1935" "§1 (Fourier coefficients of the genus average = Siegel's weighted representation numbers) [unverified]"]
theorem hasSum_thetaGenR {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    HasSum (fun T : QuadForm F r => ((repMassT Q L T / mass Q L : ℝ) : ℂ) * eT T Z) (thetaGenR Q L Z) := by
  have hfin := genusClasses_finite hQ L hLi
  have hsum : HasSum (fun T : QuadForm F r => ∑ c ∈ hfin.toFinset,
      ((LatClass.autCard Q c : ℂ))⁻¹ * ((LatClass.repCountT Q c T : ℂ) * eT T Z))
      (∑ c ∈ hfin.toFinset, ((LatClass.autCard Q c : ℂ))⁻¹ * thetaR Q c.out.1 Z) := by
    refine hasSum_sum fun c _ => (HasSum.mul_left _ ?_)
    simp only [latClass_repCountT_eq]
    exact hasSum_thetaR hQ c.out hZ
  have h := hsum.mul_left (((mass Q L : ℝ) : ℂ)⁻¹)
  rw [thetaGenR, finsum_mem_eq_finite_toFinset_sum _ hfin]
  convert h using 2 with T
  rw [repMassT, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### The Fourier coefficients of the genus average as Euler products of Whittaker integrals -/

section Whittaker

open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.Tamagawa

variable {m : ℕ}

/-- **The Fourier expansion of the genus average of the degree-$r$ theta series, with its coefficients of full rank as Euler products of
the local Whittaker integrals** (degree $r$, every finite place, dyadic included; unconditional). For $F$ totally real,
$Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite over $\mathcal O_F$, $n = 2m$, $1 \le r$, $r + 3 \le n$, $L = \mathcal O_F^n$ and
$Z \in \mathbb H_r^d$:
$$\theta_{\mathrm{gen}(L)}(Z) = \sum_Ta(T)\,e_T(Z),\qquad a(T) = \frac1{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|},$$
and for every totally positive definite $T_0$ in $r$ variables over $\mathcal O_F$
$$a(T_0) = \prod_\sigma\beta_\sigma(Q_0, T_0)\cdot(\gamma_{V,\infty}c_{B,\infty})^r\prod_{v<\infty}W_{T_0,v}(\mathbf 1_{L_v^r}),$$
$W_{T_0,v}$ = `whittakerR`, $\beta_\sigma$ = `archDensityForm`, $\gamma_{V,\infty}$, $c_{B,\infty}$ the Weil index and the self-dual constant of the
archimedean model. This is the coefficient of $e_{T_0}$ in the Siegel–Weil identity of degree $r$: the right side is Weil's factorization of
the $T_0$-th Fourier coefficient of the Siegel Eisenstein series at $s_0 = n/2 - (r+1)/2$ (with the archimedean Whittaker integral written
as Siegel's density). *Proof:* `hasSum_thetaGenR` and `siegelForms_eq_whittaker`, divided by $\mathrm{Mass}(L) > 0$. -/
@[kb "weil1965" "Ch. II–IV (Siegel–Weil identity of degree $r$, Fourier coefficients of full rank) [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem thetaGenR_hasSum_whittaker (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hr : 1 ≤ r)
    (hrN : r + 3 ≤ 2 * m) (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    HasSum (fun T : QuadForm F r =>
        ((repMassT ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) T /
          mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) * eT T Z)
      (thetaGenR ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) Z) ∧
    ∀ T₀ : QuadForm (𝓞 F) r, IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)) →
      ((repMassT ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m))
          (T₀.map (algebraMap (𝓞 F) F)) /
          mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) =
        ((∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (2 * m) r (detGram (QuadForm.diag b) σ) (detGram T₀ σ) : ℝ) : ℂ) *
          (((localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) *
              (localDataInf (F := F)).cB (aInf (unitsOfInt b hb))) ^ r *
            ∏' v : HeightOneSpectrum (𝓞 F), whittakerR v (aOfInt v b hb)
              ((LocalDensity.NF.Qp v T₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))) := by
  have hLi := isIntegral_stdLat_map (F := F) (QuadForm.diag b)
  refine ⟨hasSum_thetaGenR hpd _ hLi hZ, fun T₀ hT₀ => ?_⟩
  have hmass := mass_pos hpd (Tamagawa.stdLat F (2 * m)) hLi
  have h := siegelForms_eq_whittaker b hb T₀ hr hrN hpd hT₀
  have hm0 : ((mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hmass.ne'
  push_cast
  rw [h]
  field_simp
  push_cast
  ring

end Whittaker

end QuadFormsKB.SiegelWeil.Forms
