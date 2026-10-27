/-
# The gauge-form volume of the real orthogonal group

**Layer:** real quadratic forms $Q$ in $n$ variables (`QuadForm ℝ n`, coefficients $c_{ij}$, $0 \le i \le j < n$,
$Q(\vec x) = \sum_{i \le j} c_{ij}x_ix_j$), their Gram matrix $A = H/2$ (`Siegel.gramMatrixR`, $Q(\vec x) = \vec x^{\mathsf T}A\vec x$,
$a_{ii} = c_{ii}$, $a_{ij} = c_{ij}/2$ for $i < j$) and $d = \det A$ (`Siegel.gramDetR`). Matrices $X \in M_n(\mathbb R)$ are given
by their columns: `X : Fin n → Fin n → ℝ`, `X j` = column $j$, with Lebesgue measure $dX = \prod_{i,j}dx_{ij}$.

**Turns the cited closed form `archVolSO` into a theorem.**

## Which measure (the definition)
Weil's gauge form $dX/dS$ on $O(S) = \{X : X^{\mathsf T}SX = S\}$ (Weil 1982, §2.2, gauge forms, and §2.4, p. 24, matching gauge
forms on $G$, $H$, $G/H$ [unverified locators]) is the form induced on the fibre $\Phi^{-1}(S)$ of
$$\Phi_Q : M_n(\mathbb R) \to \mathbb R^{n(n+1)/2},\qquad X \mapsto \text{the coefficients of } \vec y \mapsto Q(X\vec y)$$
(`pullCoeff`; on the diagonal $Q(X_i)$, off it the polar value $Q(X_i + X_j) - Q(X_i) - Q(X_j) = 2X_i^{\mathsf T}AX_j$) by
$dX$ and Lebesgue measure $dS$ **in the coefficient coordinates $c_{ij}$** (the coordinates of `repCountForm`).
Its total mass is the density of the push-forward $\Phi_*(dX)$ at the point $c_Q$ (`coeffU`), i.e. Siegel's limit
$$\mathrm{vol}(O(Q), dX/dS) = \lim_{\varepsilon \to 0^+}\frac{\mathrm{Leb}\{X : \|\Phi_Q(X) - c_Q\|_\infty \le \varepsilon\}}
{\mathrm{Leb}\{c : \|c - c_Q\|_\infty \le \varepsilon\}}$$
(`siegelRatio`, `archVolO`): the archimedean local density $\alpha_\infty(Q, Q)$ of $Q$ by itself (Siegel 1935;
Kitaoka 1993, §5.6 [unverified]), exactly as $\mathrm{vol}(SO(L_\mathfrak p)) = \beta_\mathfrak p(L, L)/2$ at the finite primes. The
$SO$ version counts only $\det X > 0$ (`siegelRatioSO`, `archVolSOLim`).

## Results
* `lintegral_gram` (**the co-area / disintegration formula**, unconditional): for every measurable $f \ge 0$ on the
  upper coordinates $t = (t_{ij})_{i \le j}$ of symmetric matrices,
  $$\int_{M_n(\mathbb R)} f(X^{\mathsf T}X)\,dX = \int f(t)\,\rho_n(t)\,dt,$$
  with an explicit density $\rho_n$ (`densR`), and `densR_of_piv`: $\rho_n(t) = c_n\det(t)^{-1/2}$ on positive definite $t$
  (and $\rho_n = 0$ off the set `piv` of matrices with positive Schur pivots), where
  $$c_n = \prod_{j=0}^{n-1}\frac{\pi^{(j+1)/2}}{\Gamma((j+1)/2)} \quad(\texttt{cprod}).$$
  So the fibre over $t$ carries mass $c_n\det(t)^{-1/2}$; for $\Phi_Q$ (substituting $X \mapsto PX$, $A = P^{\mathsf T}P$) it is
  $c_n\,d^{-n/2}\det(t)^{-1/2}$, which at $t = A$ is $c_n\,d^{-(n+1)/2}$.
* `tendsto_siegelRatio`: for positive definite $Q$, the Siegel ratio tends to $2\cdot$`archVolSO n d`
  ($n \ge 0$); `archVolSO_eq_archVolO`: `archVolSO n d` $= \mathrm{vol}(O(Q), dX/dS)/2$.
* `tendsto_siegelRatioSO`, **`archVolSO_eq_volume`** ($n \ge 1$): `archVolSO n d` $= \mathrm{vol}(SO(Q), dX/dS)$, the $\det > 0$
  half (`two_mul_volume_det_pos`: a reflection in $O(Q)$ swaps the two halves, and $\{\det X = 0\}$ is null,
  `volume_det_eq_zero`).
* `archVolSO_detGram_eq`: the factor `archVolSO n (detGram Q₀ σ)` at a real embedding $\sigma$ is $\mathrm{vol}(SO(Q_\sigma), dX/dS)$.
* Cross-checks: `archVolSOLim_one` ($\mathrm{vol}(SO_1) = 1/(2d)$, matching `archVolSO_one`), `archVolO_two`
  ($\mathrm{vol}(O_2(Q)) = \frac{\pi}{2}d^{-3/2}$ in coefficient coordinates, i.e. $\pi\,d^{-3/2}$ in Gram coordinates:
  $\mathrm{vol}(O_2(\mathbb R), dX/dS) = \pi$ at $S = I$). `archVolSO_succ` is now an identity between these limits.

## Normalizations (where each factor of `archVolSO` comes from)
$\mathrm{archVolSO}(n, d) = \tfrac12\cdot 2^{-n(n-1)/2}\cdot d^{-(n+1)/2}\cdot c_n$:
* $c_n$: the fibre mass at $S = I$ in Gram coordinates (`lintegral_gram`); $c_n = \prod_{j=1}^n\pi^{j/2}/\Gamma(j/2)$ is
  Siegel's $\mathrm{vol}(O_n(\mathbb R))$. Each step of the induction contributes $\tfrac12|S^{j}| = \pi^{(j+1)/2}/\Gamma((j+1)/2)$
  (`kap`): the sphere area $2\pi^{N/2}/\Gamma(N/2)$ comes from Mathlib's Euclidean ball volume (`map_dot_self`), and the
  $\tfrac12$ from $ds = 2r\,dr$, $s = r^2$.
* $d^{-(n+1)/2}$: $d^{-n/2}$ from $X \mapsto PX$ and $d^{-1/2}$ from $\det(t)^{-1/2}$ at $t = A$.
* $2^{-n(n-1)/2}$: the $n(n-1)/2$ off-diagonal coefficient coordinates are $c_{ij} = 2a_{ij}$ (`wt`, `prod_wt`).
* $\tfrac12$: $SO$ is half of $O$ (`two_mul_volume_det_pos`). For $n = 0$ this fails ($SO_0 = O_0$), so the $SO$
  statements assume $n \ge 1$; `archVolSO 0` $= \tfrac12$ is then $\mathrm{vol}(O_0)/2$, not $\mathrm{vol}(SO_0) = 1$ (only
  $n \ge 3$ is used downstream).

## The proof (induction on $n$, `lintegral_gram`)
Split off the first column $x$ of $X$ (`lintegral_cons_hh`): the Householder reflection $H_x$ (`hh`) with
$H_x x = (\|x\|, 0, \dots, 0)$ preserves $dX$ on the other columns and $X^{\mathsf T}X$. Then $X^{\mathsf T}X$ has $s = \|x\|^2$,
$u = \|x\|\,w$ and $V = ww^{\mathsf T} + Z^{\mathsf T}Z$ ($w$ the top row of the remaining columns, $Z$ the rest; `gramU_cons`).
Integrate $Z$ by induction, translate $V$, scale $w$ ($\|x\|^{-(n-1)}$), and push $x \mapsto s$ forward (`map_dot_self`). The
result is the recursive density $\rho_n(t) = [s > 0]\,\frac{\pi^{n/2}}{\Gamma(n/2)}s^{-1/2}\rho_{n-1}(V - uu^{\mathsf T}/s)$, and
$\det t = s\det(V - uu^{\mathsf T}/s)$ (`det_symU_succ`). Siegel's limit is the value of the continuous density at the point
(`tendsto_avg_box`).

## Inputs
None: everything is proved from Mathlib (no hypotheses beyond positive definiteness).
-/
import QuadFormsKB.Siegel.ArchimedeanNF
import QuadFormsKB.Tamagawa.RankOneNF

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Tamagawa.ArchVol

/-- **Upper index pairs** $(i, j)$ with $0 \le i \le j < n$: the coordinates of a symmetric $n \times n$ matrix
(or of the coefficients of a quadratic form); there are $n(n+1)/2$ of them. -/
abbrev UIdx (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- **Splitting the upper index set of size $n+1$:** $(0,0)$ (`inl`), $(0, j+1)$ for $0 \le j < n$ (`inr ∘ inl`), and
$(i+1, j+1)$ for $(i, j)$ an upper pair of size $n$ (`inr ∘ inr`). -/
def eU (n : ℕ) : Unit ⊕ (Fin n ⊕ UIdx n) ≃ UIdx (n + 1) where
  toFun
    | .inl _ => ⟨(0, 0), le_rfl⟩
    | .inr (.inl j) => ⟨(0, j.succ), Fin.zero_le _⟩
    | .inr (.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩
  invFun p :=
    if h : p.1.1 = 0 then
      (if h' : p.1.2 = 0 then .inl () else .inr (.inl (p.1.2.pred h')))
    else .inr (.inr ⟨(p.1.1.pred h, p.1.2.pred (fun h2 => h (by
        have := p.2; rw [h2] at this; exact Fin.le_zero_iff.mp this))),
        by rw [Fin.pred_le_pred_iff]; exact p.2⟩)
  left_inv q := by
    rcases q with _ | j | p <;> simp
  right_inv p := by
    obtain ⟨⟨i, j⟩, hij⟩ := p
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj]
    · simp [hi]

/-- **Assembling an upper vector of size $n+1$** from $s = t_{00}$, $u_j = t_{0,j+1}$ and $v_{ij} = t_{i+1,j+1}$. -/
def asm {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) : UIdx (n + 1) → ℝ :=
  fun p => Sum.elim (fun _ : Unit => s) (Sum.elim u v) ((eU n).symm p)

@[simp] theorem asm_zero {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) :
    asm s u v (eU n (.inl ())) = s := by simp [asm]
@[simp] theorem asm_u {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) (j : Fin n) :
    asm s u v (eU n (.inr (.inl j))) = u j := by simp [asm]
@[simp] theorem asm_v {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) (p : UIdx n) :
    asm s u v (eU n (.inr (.inr p))) = v p := by simp [asm]

theorem measurable_asm {n : ℕ} : Measurable fun x : ℝ × (Fin n → ℝ) × (UIdx n → ℝ) =>
    asm x.1 x.2.1 x.2.2 := by
  refine measurable_pi_iff.mpr fun p => ?_
  unfold asm
  rcases (eU n).symm p with _ | j | q
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  · exact (measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)

/-- **Fubini in upper coordinates:** Lebesgue measure on $\mathbb R^{\{(i,j) : i \le j\}}$, size $n+1$, is the product of
Lebesgue measures on $s$, $u \in \mathbb R^n$ and $v$ (size $n$). -/
theorem lintegral_split {n : ℕ} {F : (UIdx (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t, F t = ∫⁻ s : ℝ, ∫⁻ u : Fin n → ℝ, ∫⁻ v : UIdx n → ℝ, F (asm s u v) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : UIdx (n + 1) => ℝ) (eU n)
  rw [← h1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Unit ⊕ (Fin n ⊕ UIdx n) => ℝ)
  rw [← h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod _ (by fun_prop)]
  have h3 := (volume_preserving_funUnique Unit ℝ).symm
  rw [← h3.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine lintegral_congr fun s => ?_
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ UIdx n => ℝ)
  rw [← h4.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun u => lintegral_congr fun v => ?_
  congr 1
  funext p
  simp [asm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rcases (eU n).symm p with _ | j | q <;> rfl


/-- **The Gram vector** $(X_i \cdot X_j)_{i \le j}$ of the columns $X_0, \dots, X_{n-1} \in \mathbb R^m$, i.e. the upper
coordinates of $X^{\mathsf T}X$. -/
def gramU {n m : ℕ} (X : Fin n → Fin m → ℝ) : UIdx n → ℝ := fun p => X p.1.1 ⬝ᵥ X p.1.2

/-- The upper coordinates $(w_iw_j)_{i \le j}$ of $ww^{\mathsf T}$. -/
def outerU {n : ℕ} (w : Fin n → ℝ) : UIdx n → ℝ := fun p => w p.1.1 * w p.1.2

theorem continuous_gramU {n m : ℕ} : Continuous (gramU : (Fin n → Fin m → ℝ) → UIdx n → ℝ) := by
  refine continuous_pi fun p => ?_
  unfold gramU dotProduct
  fun_prop

/-- **The Gram vector after the Householder step:** if the first column is $(r, 0, \dots, 0)$ and column $j+1$ is
$(w_j, Z_j)$, then $s = r^2$, $u = r\,w$ and $V = ww^{\mathsf T} + Z^{\mathsf T}Z$. -/
theorem gramU_cons {n : ℕ} (r : ℝ) (w : Fin n → ℝ) (Z : Fin n → Fin n → ℝ) :
    gramU (Fin.cons (Fin.cons r 0) (fun j => Fin.cons (w j) (Z j)) : Fin (n + 1) → Fin (n + 1) → ℝ) =
      asm (r ^ 2) (r • w) (outerU w + gramU Z) := by
  funext p
  obtain ⟨q, rfl⟩ := (eU n).surjective p
  rcases q with _ | j | q
  · rw [asm_zero]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ, sq]
  · rw [asm_u]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ]
  · rw [asm_v]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ, outerU]

/-- Splitting each of $n$ columns in $\mathbb R^{n+1}$ into its top entry $w_j$ and the rest $Z_j \in \mathbb R^n$. -/
theorem lintegral_cols_split {n : ℕ} {G : (Fin n → Fin (n + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ Y, G Y = ∫⁻ w : Fin n → ℝ, ∫⁻ Z : Fin n → Fin n → ℝ, G (fun j => Fin.cons (w j) (Z j)) := by
  let E : (Fin n → Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
    (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin n))
  have hE : MeasurePreserving E volume volume :=
    (measurePreserving_arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin n) (fun _ => volume)
      (fun _ => volume)).comp
      (measurePreserving_pi _ _ (fun _ => volume_preserving_piFinSuccAbove (fun _ => ℝ) 0))
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun w => lintegral_congr fun Z => ?_
  congr 1
  funext j i
  simp [E, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.arrowProdEquivProdArrow]
  rfl


/-! ### Householder reflection -/

theorem dot_self_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The target $(\|x\|, 0, \dots, 0)$ of the Householder reflection ($\|x\| = \sqrt{x \cdot x}$). -/
def tgt {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := Fin.cons (Real.sqrt (x ⬝ᵥ x)) 0

/-- **The Householder reflection** $H_x = 1 - \frac{2}{v \cdot v}vv^{\mathsf T}$, $v = x - (\|x\|, 0, \dots, 0)$ (and $H_x = 1$
if $v = 0$): an orthogonal matrix with $H_x x = (\|x\|, 0, \dots, 0)$ (`hh_mulVec_self`, `hh_dot`). -/
def hh {n : ℕ} (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  if (x - tgt x) ⬝ᵥ (x - tgt x) = 0 then 1
  else 1 - (2 / ((x - tgt x) ⬝ᵥ (x - tgt x))) • vecMulVec (x - tgt x) (x - tgt x)

theorem hh_mulVec_apply {n : ℕ} (x a : Fin (n + 1) → ℝ) (hv : (x - tgt x) ⬝ᵥ (x - tgt x) ≠ 0) :
    hh x *ᵥ a = a - (2 / ((x - tgt x) ⬝ᵥ (x - tgt x)) * ((x - tgt x) ⬝ᵥ a)) • (x - tgt x) := by
  rw [hh, if_neg hv, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

theorem hh_dot {n : ℕ} (x a b : Fin (n + 1) → ℝ) : (hh x *ᵥ a) ⬝ᵥ (hh x *ᵥ b) = a ⬝ᵥ b := by
  by_cases hv : (x - tgt x) ⬝ᵥ (x - tgt x) = 0
  · simp [hh, hv]
  rw [hh_mulVec_apply x a hv, hh_mulVec_apply x b hv]
  set v := x - tgt x
  set c := 2 / (v ⬝ᵥ v)
  have hc : c * (v ⬝ᵥ v) = 2 := by simp only [c]; field_simp
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm a v, dotProduct_comm b v]
  linear_combination (c * (v ⬝ᵥ a) * (v ⬝ᵥ b)) * hc

theorem tgt_dot {n : ℕ} (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ tgt x = Real.sqrt (x ⬝ᵥ x) * x 0 ∧ tgt x ⬝ᵥ tgt x = x ⬝ᵥ x := by
  constructor
  · simp [tgt, dotProduct, Fin.sum_univ_succ, mul_comm]
  · have h := dot_self_nonneg x
    simp only [dotProduct, Fin.sum_univ_succ] at h
    simp [tgt, dotProduct, Fin.sum_univ_succ, Real.mul_self_sqrt h]

theorem hh_mulVec_self {n : ℕ} (x : Fin (n + 1) → ℝ) : hh x *ᵥ x = tgt x := by
  by_cases hv : (x - tgt x) ⬝ᵥ (x - tgt x) = 0
  · have : x - tgt x = 0 := by
      have := dotProduct_self_eq_zero.mp hv
      exact this
    rw [hh, if_pos hv, one_mulVec]; exact sub_eq_zero.mp this
  rw [hh_mulVec_apply x x hv]
  obtain ⟨h1, h2⟩ := tgt_dot x
  have hvx : (x - tgt x) ⬝ᵥ x = (x - tgt x) ⬝ᵥ (x - tgt x) / 2 := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (tgt x) x, h1, h2]; ring
  rw [hvx, show 2 / ((x - tgt x) ⬝ᵥ (x - tgt x)) * ((x - tgt x) ⬝ᵥ (x - tgt x) / 2) = 1 by
    field_simp, one_smul, sub_sub_cancel]

theorem hh_transpose_mul {n : ℕ} (x : Fin (n + 1) → ℝ) : (hh x)ᵀ * hh x = 1 := by
  ext i j
  have := hh_dot x (Pi.single i 1) (Pi.single j 1)
  rw [mulVec_single_one, mulVec_single_one, single_dotProduct, one_mul] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [transpose_apply]
  rw [show (∑ k, hh x k i * hh x k j) = (hh x).col i ⬝ᵥ (hh x).col j from rfl, this]
  by_cases h : i = j <;> simp [h, Pi.single_apply, eq_comm]

theorem abs_det_hh {n : ℕ} (x : Fin (n + 1) → ℝ) : |(hh x).det| = 1 := by
  have h := congrArg Matrix.det (hh_transpose_mul x)
  rw [det_mul, det_transpose, det_one, ← sq] at h
  nlinarith [abs_nonneg (hh x).det, sq_abs (hh x).det]

theorem measurePreserving_mulVec {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (hH : |H.det| = 1) :
    MeasurePreserving (fun y : Fin N → ℝ => H *ᵥ y) volume volume := by
  refine ⟨(Matrix.toLin' H).continuous_of_finiteDimensional.measurable, ?_⟩
  have h0 : H.det ≠ 0 := by intro h; rw [h, abs_zero] at hH; exact zero_ne_one hH
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi h0
  rw [abs_inv, hH, inv_one, ENNReal.ofReal_one, one_smul] at this
  exact this

theorem gramU_mulVec {n m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : ∀ a b, (H *ᵥ a) ⬝ᵥ (H *ᵥ b) = a ⬝ᵥ b) (X : Fin n → Fin m → ℝ) :
    gramU (fun k => H *ᵥ X k) = gramU X := by
  funext p; exact hH _ _

/-- **Rotating the first column to $(\|x\|, 0, \dots, 0)$:** for fixed $x$, $Y \mapsto H_xY$ preserves Lebesgue
measure on the remaining $n$ columns and the Gram vector of $(x, Y)$. -/
theorem lintegral_cons_hh {n : ℕ} {f : (UIdx (n + 1) → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (x : Fin (n + 1) → ℝ) :
    ∫⁻ Y : Fin n → Fin (n + 1) → ℝ, f (gramU (Fin.cons x Y : Fin (n + 1) → Fin (n + 1) → ℝ)) =
      ∫⁻ Y : Fin n → Fin (n + 1) → ℝ, f (gramU (Fin.cons (tgt x) Y : Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  have hP : MeasurePreserving (fun (Y : Fin n → Fin (n + 1) → ℝ) j => hh x *ᵥ Y j) volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec _ (abs_det_hh x)
  rw [← hP.lintegral_comp (f := fun Y => f (gramU (Fin.cons (tgt x) Y : Fin (n + 1) → Fin (n + 1) → ℝ)))
    (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)]
  refine lintegral_congr fun Y => ?_
  congr 1
  rw [← gramU_mulVec (hh x) (hh_dot x)]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [hh_mulVec_self]
  · simp



/-- $\kappa_N = \pi^{N/2}/\Gamma(N/2)$, half the area $2\pi^{N/2}/\Gamma(N/2)$ of the unit sphere $S^{N-1} \subset \mathbb R^N$. -/
def kap (N : ℕ) : ℝ := Real.pi ^ ((N : ℝ) / 2) / Real.Gamma ((N : ℝ) / 2)

theorem kap_pos (N : ℕ) (hN : 1 ≤ N) : 0 < kap N := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (0 : ℝ) < N / 2 := by linarith
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos this)

/-- $\mathrm{Leb}\{x \in \mathbb R^N : x \cdot x \le t\} = \frac{\kappa_N}{N/2}t^{N/2}$ ($N \ge 1$, $t \ge 0$; Mathlib's
`volume_sum_rpow_le`). -/
theorem volume_dot_le {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    volume {x : Fin N → ℝ | x ⬝ᵥ x ≤ t} =
      ENNReal.ofReal (kap N / (N / 2) * t ^ ((N : ℝ) / 2)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hset : {x : Fin N → ℝ | x ⬝ᵥ x ≤ t} =
      {x : Fin N → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt t} := by
    ext x
    simp only [mem_ofPred_eq]
    have e : (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (x ⬝ᵥ x) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_two, sq_abs, sq]
    rw [e, Real.sqrt_le_sqrt_iff ht]
  rw [hset, MeasureTheory.volume_sum_rpow_le (Fin N) (by norm_num : (1 : ℝ) ≤ 2), Fintype.card_fin,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hG : 2 * Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi := QuadFormsKB.Siegel.two_mul_Gamma_three_halves
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) / 2 ≠ 0 := by positivity
  have ht' : Real.sqrt t ^ N = t ^ ((N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
    ring_nf
  have hpi : Real.sqrt Real.pi ^ N = Real.pi ^ ((N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  rw [hG, ht', hpi, kap, show (N : ℝ) / 2 + 1 = (N : ℝ) / 2 + 1 from rfl, Real.Gamma_add_one hN0]
  field_simp

/-- **The push-forward of Lebesgue measure under $x \mapsto x \cdot x$** on $\mathbb R^N$, $N \ge 1$: it has density
$\kappa_N\,s^{N/2 - 1}$ on $s > 0$ (polar coordinates; $\kappa_N = \frac12|S^{N-1}|$). -/
theorem map_dot_self {N : ℕ} (hN : 1 ≤ N) :
    Measure.map (fun x : Fin N → ℝ => x ⬝ᵥ x) volume =
      (volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (kap N * s ^ ((N : ℝ) / 2 - 1))) := by
  have hq : Measurable (fun x : Fin N → ℝ => x ⬝ᵥ x) := by
    unfold dotProduct; fun_prop
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set V : ℝ → ℝ := fun t => kap N / (N / 2) * max t 0 ^ ((N : ℝ) / 2)
  have hL : ∀ t, Measure.map (fun x : Fin N → ℝ => x ⬝ᵥ x) volume (Iic t) = ENNReal.ofReal (V t) := by
    intro t
    rw [Measure.map_apply hq measurableSet_Iic]
    rcases le_or_gt 0 t with ht | ht
    · rw [show (fun x : Fin N → ℝ => x ⬝ᵥ x) ⁻¹' Iic t = {x | x ⬝ᵥ x ≤ t} from rfl,
        volume_dot_le hN ht]; simp only [V, max_eq_left ht]
    · have : (fun x : Fin N → ℝ => x ⬝ᵥ x) ⁻¹' Iic t = ∅ := by
        ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
        exact ht.trans_le (dot_self_nonneg x)
      rw [this, measure_empty]; simp only [V, max_eq_right ht.le]
      rw [Real.zero_rpow (by positivity), mul_zero, ENNReal.ofReal_zero]
  have hR : ∀ t, (volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (kap N * s ^ ((N : ℝ) / 2 - 1))) (Iic t) = ENNReal.ofReal (V t) := by
    intro t
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    rcases le_or_gt t 0 with ht | ht
    · have : Iic t ∩ Ioi (0 : ℝ) = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
          not_lt]; intro h; linarith
      rw [this, Measure.restrict_empty, lintegral_zero_measure]; simp only [V, max_eq_right ht]
      rw [Real.zero_rpow (by positivity), mul_zero, ENNReal.ofReal_zero]
    · rw [Iic_inter_Ioi, ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le ht.le,
        intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
      · simp only [V, max_eq_left ht.le]
        congr 1
        rw [show (N : ℝ) / 2 - 1 + 1 = N / 2 by ring, Real.zero_rpow (by positivity)]
        ring
      · exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < N / 2 - 1)).const_mul _
          |>.1)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (kap_pos N hN).le (Real.rpow_nonneg hs.1.le _)
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
  · exact ((measure_mono Ioc_subset_Iic_self).trans_lt (by rw [hL]; exact ENNReal.ofReal_lt_top)).ne
  · rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic
      (by rw [hL]; exact ENNReal.ofReal_ne_top),
      measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic
      (by rw [hR]; exact ENNReal.ofReal_ne_top), hL, hL, hR, hR]

/-- Integrals of radial functions: $\int_{\mathbb R^N} g(x \cdot x)\,dx = \int_0^\infty \kappa_N s^{N/2-1}g(s)\,ds$. -/
theorem lintegral_dot_self {N : ℕ} (hN : 1 ≤ N) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : Fin N → ℝ, g (x ⬝ᵥ x) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (kap N * s ^ ((N : ℝ) / 2 - 1)) * g s := by
  have hq : Measurable (fun x : Fin N → ℝ => x ⬝ᵥ x) := by
    unfold dotProduct; fun_prop
  rw [← lintegral_map hg hq, map_dot_self hN, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
  rfl


/-! ### The density -/

def sU {n : ℕ} (t : UIdx (n + 1) → ℝ) : ℝ := t (eU n (.inl ()))
def uU {n : ℕ} (t : UIdx (n + 1) → ℝ) : Fin n → ℝ := fun j => t (eU n (.inr (.inl j)))
def vU {n : ℕ} (t : UIdx (n + 1) → ℝ) : UIdx n → ℝ := fun p => t (eU n (.inr (.inr p)))
/-- **The Schur complement** $V - uu^{\mathsf T}/s$ of $t = \begin{pmatrix} s & u^{\mathsf T}\\ u & V\end{pmatrix}$, in upper
coordinates ($s = $ `sU t`, $u = $ `uU t`, $V = $ `vU t`). -/
def schurU {n : ℕ} (t : UIdx (n + 1) → ℝ) : UIdx n → ℝ := vU t - (sU t)⁻¹ • outerU (uU t)

@[simp] theorem sU_asm {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) : sU (asm s u v) = s := asm_zero s u v
@[simp] theorem uU_asm {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) : uU (asm s u v) = u :=
  funext fun j => asm_u s u v j
@[simp] theorem vU_asm {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) : vU (asm s u v) = v :=
  funext fun p => asm_v s u v p

theorem measurable_sU {n : ℕ} : Measurable (sU : (UIdx (n + 1) → ℝ) → ℝ) := measurable_pi_apply _
theorem measurable_schurU {n : ℕ} : Measurable (schurU : (UIdx (n + 1) → ℝ) → UIdx n → ℝ) := by
  refine measurable_pi_iff.mpr fun p => ?_
  simp only [schurU, vU, uU, sU, outerU, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- **The density of $X \mapsto X^{\mathsf T}X$** (recursive form, upper coordinates):
$\rho_0 = 1$ and $\rho_{n+1}(t) = [s > 0]\,\kappa_{n+1}\,s^{-1/2}\,\rho_n(V - uu^{\mathsf T}/s)$. On positive definite $t$ it is
$c_n\det(t)^{-1/2}$ (`densR_of_piv`). -/
def densR : (n : ℕ) → (UIdx n → ℝ) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, t => if 0 < sU t then ENNReal.ofReal (kap (n + 1) / Real.sqrt (sU t)) * densR n (schurU t)
      else 0

theorem measurable_densR : ∀ n, Measurable (densR n)
  | 0 => measurable_const
  | n + 1 => by
    refine Measurable.ite (measurableSet_lt measurable_const measurable_sU) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (measurable_const.div
      (Real.continuous_sqrt.measurable.comp measurable_sU))).mul
      ((measurable_densR n).comp measurable_schurU)


/-- $\int_{\mathbb R^n} G(rw)\,dw = r^{-n}\int G$ for $r > 0$. -/
theorem lintegral_comp_smul_pi {n : ℕ} {r : ℝ} (hr : 0 < r) {G : (Fin n → ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ w : Fin n → ℝ, G (r • w) = ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ u, G u := by
  rw [← lintegral_map hG (measurable_const_smul r), Measure.map_addHaar_smul _ hr.ne',
    lintegral_smul_measure, Module.finrank_fin_fun, abs_of_pos (by positivity)]
  rfl

theorem densR_succ_asm {n : ℕ} (s : ℝ) (u : Fin n → ℝ) (v : UIdx n → ℝ) :
    densR (n + 1) (asm s u v) = if 0 < s then
      ENNReal.ofReal (kap (n + 1) / Real.sqrt s) * densR n (v - s⁻¹ • outerU u) else 0 := by
  simp [densR, schurU]

theorem rpow_aux {n : ℕ} {s : ℝ} (hs : 0 < s) :
    kap (n + 1) * s ^ (((n + 1 : ℕ) : ℝ) / 2 - 1) * (Real.sqrt s ^ n)⁻¹ = kap (n + 1) / Real.sqrt s := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, mul_assoc, div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_neg hs.le, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
  congr 1; push_cast; ring

theorem continuous_outerU {n : ℕ} : Continuous (outerU : (Fin n → ℝ) → UIdx n → ℝ) := by
  refine continuous_pi fun p => ?_
  unfold outerU; fun_prop

theorem outerU_smul {n : ℕ} (c : ℝ) (u : Fin n → ℝ) : outerU (c • u) = c ^ 2 • outerU u := by
  funext p; simp only [outerU, Pi.smul_apply, smul_eq_mul]; ring

/-- **The disintegration of $dX$ along $X \mapsto X^{\mathsf T}X$** (the co-area formula for the Gram map; Siegel 1935
[unverified locator]; the square case of the Wishart integral): for every measurable $f \ge 0$ on upper coordinates
$t = (t_{ij})_{0 \le i \le j < n}$ of symmetric matrices (Lebesgue measure $dt = \prod_{i \le j}dt_{ij}$),
$$\int_{M_n(\mathbb R)} f\big((X_i \cdot X_j)_{i \le j}\big)\,dX = \int f(t)\,\rho_n(t)\,dt,\qquad \rho_n = \texttt{densR}\ n.$$
The fibre over $t$ (a coset of $O_n(\mathbb R)$) thus carries the measure of total mass $\rho_n(t) = c_n\det(t)^{-1/2}$
(`densR_of_piv`). -/
@[kb "siegel1935" "volume of O_n(R), dX/dS normalization [unverified]"]
theorem lintegral_gram : ∀ (n : ℕ) {f : (UIdx n → ℝ) → ℝ≥0∞}, Measurable f →
    ∫⁻ X : Fin n → Fin n → ℝ, f (gramU X) = ∫⁻ t, densR n t * f t
  | 0, f, hf => by
    have h1 : (volume : Measure (Fin 0 → Fin 0 → ℝ)) = Measure.dirac 0 := by
      rw [volume_pi]; exact Measure.pi_of_empty _ 0
    have h2 : (volume : Measure (UIdx 0 → ℝ)) = Measure.dirac 0 := by
      rw [volume_pi]; exact Measure.pi_of_empty _ 0
    rw [h1, h2, lintegral_dirac' (f := fun X => f (gramU X)) _ (hf.comp continuous_gramU.measurable),
      lintegral_dirac' (f := fun t => densR 0 t * f t) _ ((measurable_densR 0).mul hf)]
    simp only [densR, one_mul]
    exact congrArg f (Subsingleton.elim _ _)
  | n + 1, f, hf => by
    have hfg : Measurable fun X : Fin (n + 1) → Fin (n + 1) → ℝ => f (gramU X) :=
      hf.comp continuous_gramU.measurable
    -- split off the first column
    have hP := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) 0).symm
    rw [← hP.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
      lintegral_prod (f := fun a => f (gramU ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) 0).symm a)))
        (hfg.comp (MeasurableEquiv.measurable _)).aemeasurable]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
      Fin.insertNth_zero']
    rw [lintegral_congr (fun x => lintegral_cons_hh hf x)]
    set Φ : ℝ → ℝ≥0∞ := fun s => ∫⁻ Y : Fin n → Fin (n + 1) → ℝ,
      f (gramU (Fin.cons (Fin.cons (Real.sqrt s) 0 : Fin (n + 1) → ℝ) Y :
        Fin (n + 1) → Fin (n + 1) → ℝ)) with hΦdef
    have hΦ : Measurable Φ :=
      Measurable.lintegral_prod_right' (f := fun p : ℝ × (Fin n → Fin (n + 1) → ℝ) =>
        f (gramU (Fin.cons (Fin.cons (Real.sqrt p.1) 0 : Fin (n + 1) → ℝ) p.2 :
          Fin (n + 1) → Fin (n + 1) → ℝ)))
        (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)
    rw [show (∫⁻ x : Fin (n + 1) → ℝ, ∫⁻ Y : Fin n → Fin (n + 1) → ℝ,
        f (gramU (Fin.cons (tgt x) Y : Fin (n + 1) → Fin (n + 1) → ℝ))) = ∫⁻ x, Φ (x ⬝ᵥ x) from rfl,
      lintegral_dot_self (by omega) hΦ, lintegral_split (F := fun t => densR (n + 1) t * f t)
        ((measurable_densR _).mul hf)]
    set F : ℝ → (Fin n → ℝ) → (UIdx n → ℝ) → ℝ≥0∞ := fun s u v =>
      ENNReal.ofReal (kap (n + 1) / Real.sqrt s) * densR n (v - s⁻¹ • outerU u) * f (asm s u v)
    have hR : ∀ s, (∫⁻ u, ∫⁻ v, densR (n + 1) (asm s u v) * f (asm s u v)) =
        (Ioi 0).indicator (fun s => ∫⁻ u, ∫⁻ v, F s u v) s := by
      intro s
      by_cases hs : 0 < s
      · simp [densR_succ_asm, hs, F, mul_assoc]
      · simp [densR_succ_asm, hs]
    rw [lintegral_congr hR, lintegral_indicator measurableSet_Ioi]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) => ?_)
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hr2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have hΦs : Φ s = ENNReal.ofReal ((Real.sqrt s ^ n)⁻¹) *
        ∫⁻ u, ∫⁻ v, densR n (v - s⁻¹ • outerU u) * f (asm s u v) := by
      simp only [hΦdef]
      rw [lintegral_cols_split (G := fun Y => f (gramU (Fin.cons (Fin.cons (Real.sqrt s) 0 :
        Fin (n + 1) → ℝ) Y : Fin (n + 1) → Fin (n + 1) → ℝ)))
        (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)]
      simp only [gramU_cons, hr2]
      have h1 : ∀ w : Fin n → ℝ, ∫⁻ Z : Fin n → Fin n → ℝ,
          f (asm s (Real.sqrt s • w) (outerU w + gramU Z)) =
            ∫⁻ v, densR n (v - outerU w) * f (asm s (Real.sqrt s • w) v) := by
        intro w
        rw [lintegral_gram n (f := fun u => f (asm s (Real.sqrt s • w) (outerU w + u)))
          (hf.comp (measurable_asm.comp (measurable_const.prodMk (measurable_const.prodMk
            (measurable_const.add measurable_id)))))]
        rw [← lintegral_add_left_eq_self (fun v => densR n (v - outerU w) *
          f (asm s (Real.sqrt s • w) v)) (outerU w)]
        simp only [add_sub_cancel_left]
      rw [lintegral_congr h1]
      have h2 := lintegral_comp_smul_pi hr (G := fun u => ∫⁻ v, densR n (v - outerU ((Real.sqrt s)⁻¹ • u)) *
        f (asm s u v)) (Measurable.lintegral_prod_right'
          (f := fun p : (Fin n → ℝ) × (UIdx n → ℝ) =>
            densR n (p.2 - outerU ((Real.sqrt s)⁻¹ • p.1)) * f (asm s p.1 p.2))
          (Measurable.mul ((measurable_densR n).comp (Continuous.measurable
            (f := fun p : (Fin n → ℝ) × (UIdx n → ℝ) => p.2 - outerU ((Real.sqrt s)⁻¹ • p.1))
            (continuous_snd.sub (continuous_outerU.comp ((continuous_const_smul _).comp continuous_fst)))))
            (hf.comp (measurable_asm.comp (measurable_const.prodMk measurable_id)))))
      simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h2
      rw [h2]; simp only [outerU_smul, inv_pow, hr2]
    rw [hΦs, ← mul_assoc, ← ENNReal.ofReal_mul
      (mul_nonneg (kap_pos _ (by omega)).le (Real.rpow_nonneg hs.le _)), rpow_aux hs,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun u => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun v => ?_
    simp only [F, mul_assoc]


/-- **The symmetric matrix with upper coordinates** $t$: entries $t_{\min(i,j),\max(i,j)}$. -/
def symU {n : ℕ} (t : UIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if h : i ≤ j then t ⟨(i, j), h⟩ else t ⟨(j, i), le_of_not_ge h⟩

theorem symU_zero_zero {n : ℕ} (t : UIdx (n + 1) → ℝ) : symU t 0 0 = sU t := by
  simp [symU, sU, eU]

theorem symU_zero_succ {n : ℕ} (t : UIdx (n + 1) → ℝ) (j : Fin n) : symU t 0 j.succ = uU t j := by
  simp [symU, uU, eU]

theorem symU_succ_zero {n : ℕ} (t : UIdx (n + 1) → ℝ) (i : Fin n) : symU t i.succ 0 = uU t i := by
  simp [symU, uU, eU, Fin.succ_ne_zero]

theorem symU_succ_succ {n : ℕ} (t : UIdx (n + 1) → ℝ) (i j : Fin n) :
    symU t i.succ j.succ = symU (vU t) i j := by
  by_cases h : i ≤ j
  · simp [symU, vU, eU, h]
  · simp [symU, vU, eU, h]

theorem symU_schurU {n : ℕ} (t : UIdx (n + 1) → ℝ) (i j : Fin n) :
    symU (schurU t) i j = symU (vU t) i j - uU t i * uU t j / sU t := by
  by_cases h : i ≤ j
  · simp [symU, schurU, outerU, h]; ring
  · simp [symU, schurU, outerU, h]; ring

/-- **Schur's determinant formula:** $\det t = s\cdot\det(V - uu^{\mathsf T}/s)$ for $s \ne 0$. -/
theorem det_symU_succ {n : ℕ} (t : UIdx (n + 1) → ℝ) (hs : sU t ≠ 0) :
    (symU t).det = sU t * (symU (schurU t)).det := by
  set M := symU t
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
    (if i = j then 1 else 0) - (if j = 0 ∧ i ≠ 0 then M i 0 / sU t else 0)
  have hE : E.det = 1 := by
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have : E.submatrix Fin.succ Fin.succ = 1 := by
      ext i j; simp [E, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj]
    have h0 : ∀ j : Fin n, E 0 j.succ = 0 := fun j => by
      simp [E, (Fin.succ_ne_zero j).symm]
    have h00 : E 0 0 = 1 := by simp [E]
    simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, h00, Fin.succAbove_zero, this,
      det_one]
    simp
  have hEM : (E * M).det = M.det := by rw [det_mul, hE, one_mul]
  rw [← hEM, det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
  · have h00 : (E * M) 0 0 = sU t := by
      simp [E, Matrix.mul_apply, Fin.sum_univ_succ, M, symU_zero_zero]
    have hsub : (E * M).submatrix Fin.succ Fin.succ = symU (schurU t) := by
      ext i j
      rw [submatrix_apply, symU_schurU, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [E, M, Fin.succ_ne_zero, symU_succ_zero, symU_zero_succ, symU_succ_succ, Fin.succ_inj,
        Finset.sum_ite_eq']
      ring
    simp [h00, hsub, Fin.succAbove_zero]
  · intro i _
    have : (E * M) i.succ 0 = 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp [E, M, Fin.succ_ne_zero, symU_succ_zero, symU_zero_zero, Fin.succ_inj, Finset.sum_ite_eq']
      rw [div_mul_cancel₀ _ hs]; ring
    simp [this]


/-- **Positive Schur pivots:** $s > 0$ and (recursively) positive pivots of $V - uu^{\mathsf T}/s$. Equivalent to positive
definiteness (one direction is `piv_of_PDU`; the converse is not needed). -/
def piv : (n : ℕ) → (UIdx n → ℝ) → Prop
  | 0, _ => True
  | n + 1, t => 0 < sU t ∧ piv n (schurU t)

/-- $c_n = \prod_{j=0}^{n-1}\pi^{(j+1)/2}/\Gamma((j+1)/2) = \prod_{j=1}^{n}\pi^{j/2}/\Gamma(j/2)$, Siegel's
$\mathrm{vol}(O_n(\mathbb R), dX/dS)$ at $S = I$ in Gram coordinates. -/
def cprod (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, kap (j + 1)

theorem cprod_pos (n : ℕ) : 0 < cprod n :=
  Finset.prod_pos fun j _ => kap_pos _ (by omega)

/-- **The density is $c_n\det(t)^{-1/2}$:** if $t$ has positive Schur pivots then $\det t > 0$ and
$\rho_n(t) = c_n\det(t)^{-1/2}$. -/
@[kb "siegel1935" "vol(O_n(R)) = ∏ π^{j/2}/Γ(j/2) [unverified]"]
theorem densR_of_piv : ∀ (n : ℕ) (t : UIdx n → ℝ), piv n t →
    0 < (symU t).det ∧ densR n t = ENNReal.ofReal (cprod n * (symU t).det ^ (-(1 / 2 : ℝ)))
  | 0, t, _ => by simp [densR, cprod, Matrix.det_isEmpty]
  | n + 1, t, ⟨hs, hp⟩ => by
    obtain ⟨hd, he⟩ := densR_of_piv n _ hp
    rw [det_symU_succ t hs.ne']
    refine ⟨mul_pos hs hd, ?_⟩
    rw [densR, if_pos hs, he, ← ENNReal.ofReal_mul (div_nonneg (kap_pos _ (by omega)).le
      (Real.sqrt_nonneg _)), Real.mul_rpow hs.le hd.le, cprod, cprod, Finset.prod_range_succ,
      Real.sqrt_eq_rpow, Real.rpow_neg hs.le]
    congr 1
    rw [div_eq_mul_inv]; ring

theorem continuousOn_schurU {n : ℕ} :
    ContinuousOn (schurU : (UIdx (n + 1) → ℝ) → UIdx n → ℝ) {t | 0 < sU t} := by
  refine continuousOn_pi.mpr fun p => ?_
  simp only [schurU, vU, uU, sU, outerU, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine ((continuous_apply _).continuousOn).sub (ContinuousOn.mul ?_ (by fun_prop))
  exact ((continuous_apply _).continuousOn).inv₀ fun t ht => (ne_of_gt ht)

theorem isOpen_piv : ∀ n : ℕ, IsOpen {t : UIdx n → ℝ | piv n t}
  | 0 => by simp [piv]
  | n + 1 => by
    have : {t : UIdx (n + 1) → ℝ | piv (n + 1) t} = {t | 0 < sU t} ∩ schurU ⁻¹' {t | piv n t} := rfl
    rw [this]
    exact continuousOn_schurU.isOpen_inter_preimage (isOpen_lt continuous_const (continuous_apply _))
      (isOpen_piv n)

theorem continuous_det_symU {n : ℕ} : Continuous fun t : UIdx n → ℝ => (symU t).det := by
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  simp only [symU, Matrix.of_apply]
  split_ifs <;> exact continuous_apply _

/-! ### Positive definiteness implies positive pivots -/

/-- **Positive definiteness** of the symmetric matrix with upper coordinates $t$. -/
def PDU {n : ℕ} (t : UIdx n → ℝ) : Prop := ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (symU t *ᵥ x)

theorem symU_mulVec_cons {n : ℕ} (t : UIdx (n + 1) → ℝ) (a : ℝ) (y : Fin n → ℝ) :
    symU t *ᵥ (Fin.cons a y : Fin (n + 1) → ℝ) =
      Fin.cons (sU t * a + uU t ⬝ᵥ y) (a • uU t + symU (vU t) *ᵥ y) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, symU_zero_zero, symU_zero_succ]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, symU_succ_zero, symU_succ_succ]
    ring

theorem quad_cons {n : ℕ} (t : UIdx (n + 1) → ℝ) (a : ℝ) (y : Fin n → ℝ) :
    (Fin.cons a y : Fin (n + 1) → ℝ) ⬝ᵥ (symU t *ᵥ (Fin.cons a y : Fin (n + 1) → ℝ)) =
      sU t * a ^ 2 + 2 * a * (uU t ⬝ᵥ y) + y ⬝ᵥ (symU (vU t) *ᵥ y) := by
  rw [symU_mulVec_cons]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [show ∑ i, y i * (a * uU t i) = a * ∑ i, uU t i * y i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

theorem quad_schur {n : ℕ} (t : UIdx (n + 1) → ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ (symU (schurU t) *ᵥ y) = y ⬝ᵥ (symU (vU t) *ᵥ y) - (uU t ⬝ᵥ y) ^ 2 / sU t := by
  have : symU (schurU t) = symU (vU t) - (sU t)⁻¹ • vecMulVec (uU t) (uU t) := by
    ext i j; rw [symU_schurU]; simp [vecMulVec_apply]; ring
  rw [this, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm y (uU t)]
  ring

theorem piv_of_PDU : ∀ (n : ℕ) (t : UIdx n → ℝ), PDU t → piv n t
  | 0, _, _ => trivial
  | n + 1, t, h => by
    have hs : 0 < sU t := by
      have := h (Fin.cons 1 0) (by intro h0; have := congrFun h0 0; simp at this)
      rw [quad_cons] at this; simpa using this
    refine ⟨hs, piv_of_PDU n _ fun y hy => ?_⟩
    have hx : (Fin.cons (-(uU t ⬝ᵥ y) / sU t) y : Fin (n + 1) → ℝ) ≠ 0 := by
      intro h0; apply hy; funext i; have := congrFun h0 i.succ; simpa using this
    have := h _ hx
    rw [quad_cons] at this
    rw [quad_schur]
    have e : sU t * (-(uU t ⬝ᵥ y) / sU t) ^ 2 + 2 * (-(uU t ⬝ᵥ y) / sU t) * (uU t ⬝ᵥ y) =
        -((uU t ⬝ᵥ y) ^ 2 / sU t) := by field_simp; ring
    linarith


/-- $\int f(PX)\,dX = |\det P|^{-n}\int f$ on $M_n(\mathbb R)$ ($P$ acting on each column). -/
theorem lintegral_comp_mulVec_cols {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.det ≠ 0)
    {G : (Fin n → Fin n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X : Fin n → Fin n → ℝ, G (fun j => P *ᵥ X j) =
      ENNReal.ofReal (|P.det|⁻¹) ^ n * ∫⁻ Y, G Y := by
  have hmeas : Measurable fun y : Fin n → ℝ => P *ᵥ y :=
    (Matrix.toLin' P).continuous_of_finiteDimensional.measurable
  set c : NNReal := Real.toNNReal (|P.det|⁻¹)
  have h1 : Measure.map (fun y : Fin n → ℝ => P *ᵥ y) volume = c • (volume : Measure (Fin n → ℝ)) := by
    have := Real.map_matrix_volume_pi_eq_smul_volume_pi hP
    rw [abs_inv] at this
    rw [ENNReal.smul_def]
    exact this
  have hmap : Measure.map (fun (X : Fin n → Fin n → ℝ) j => P *ᵥ X j) volume =
      ENNReal.ofReal (|P.det|⁻¹) ^ n • (volume : Measure (Fin n → Fin n → ℝ)) := by
    rw [volume_pi, Measure.pi_map_pi (hμ := fun _ => by rw [h1]; infer_instance)
      (fun _ => hmeas.aemeasurable)]
    simp only [h1]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_congr rfl
      (fun i _ => Measure.smul_apply _ _ _), Finset.prod_congr rfl (fun i _ => ENNReal.smul_def _ _),
      Finset.prod_congr rfl (fun i _ => smul_eq_mul _ _),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  rw [← lintegral_map hG (g := fun (X : Fin n → Fin n → ℝ) j => P *ᵥ X j)
    (measurable_pi_iff.mpr fun j => hmeas.comp (measurable_pi_apply j)), hmap,
    lintegral_smul_measure, smul_eq_mul]


/-- **Boxes** $\prod_i[t_{0,i} - \varepsilon/w_i,\ t_{0,i} + \varepsilon/w_i]$. -/
def box {ι : Type*} (t0 : ι → ℝ) (w : ι → ℝ) (ε : ℝ) : Set (ι → ℝ) :=
  univ.pi fun i => Metric.closedBall (t0 i) (ε / w i)

theorem volume_box {ι : Type*} [Fintype ι] (t0 w : ι → ℝ) (ε : ℝ) :
    volume (box t0 w ε) = ∏ i, ENNReal.ofReal (2 * (ε / w i)) := by
  rw [box, volume_pi_pi]; simp [Real.volume_closedBall]

/-- **Averages over shrinking boxes:** if $g = \mathrm{ofReal}\circ G$ on $U$, with $G \ge 0$ continuous on an open
$U \ni t_0$, then $\frac{1}{|B_\varepsilon|}\int_{B_\varepsilon}g \to G(t_0)$ as $\varepsilon \to 0^+$. -/
theorem tendsto_avg_box {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ≥0∞} {G : (ι → ℝ) → ℝ}
    {U : Set (ι → ℝ)} (hU : IsOpen U) {t0 : ι → ℝ} (ht0 : t0 ∈ U) (hGc : ContinuousOn G U)
    (hG0 : ∀ t ∈ U, 0 ≤ G t) (hgG : ∀ t ∈ U, g t = ENNReal.ofReal (G t)) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun ε => (∫⁻ t in box t0 w ε, g t).toReal / (volume (box t0 w ε)).toReal)
      (𝓝[>] 0) (𝓝 (G t0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  have hcont : ContinuousAt G t0 := hGc.continuousAt (hU.mem_nhds ht0)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU t0 ht0
  set K := ∑ i, (w i)⁻¹ + 1
  have hwK : ∀ i, (w i)⁻¹ ≤ K - 1 := fun i => by
    simp only [K, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun i => (w i)⁻¹) (fun j _ => (inv_pos.mpr (hw j)).le)
      (Finset.mem_univ i)
  have hK : 0 < K := by
    have : 0 ≤ ∑ i, (w i)⁻¹ := Finset.sum_nonneg fun j _ => (inv_pos.mpr (hw j)).le
    simp only [K]; linarith
  refine ⟨min δ1 δ2 / K, by positivity, fun {ε} hε hεd => ?_⟩
  have hε : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε, lt_div_iff₀ hK] at hεd
  have hK1 : 0 ≤ K - 1 := by
    simp only [K, add_sub_cancel_right]; exact Finset.sum_nonneg fun j _ => (inv_pos.mpr (hw j)).le
  have hsub : ∀ t ∈ box t0 w ε, dist t t0 < min δ1 δ2 := by
    intro t ht
    have : dist t t0 ≤ ε * (K - 1) := by
      refine (dist_pi_le_iff (mul_nonneg hε.le hK1)).mpr fun i => ?_
      have hi := ht i (mem_univ i)
      rw [Metric.mem_closedBall, div_eq_mul_inv] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left (hwK i) hε.le)
    nlinarith
  have hU' : ∀ t ∈ box t0 w ε, t ∈ U := fun t ht =>
    h2 (Metric.mem_ball.mpr ((hsub t ht).trans_le (min_le_right _ _)))
  have hclose : ∀ t ∈ box t0 w ε, |G t - G t0| < η / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact h1 ((hsub t ht).trans_le (min_le_left _ _))
  have hmeasB : MeasurableSet (box t0 w ε) :=
    MeasurableSet.univ_pi fun i => measurableSet_closedBall
  have hV : volume (box t0 w ε) ≠ ∞ := by rw [volume_box]; exact ENNReal.prod_ne_top fun i _ =>
    ENNReal.ofReal_ne_top
  have hV0 : 0 < (volume (box t0 w ε)).toReal := by
    rw [volume_box, ENNReal.toReal_prod]
    exact Finset.prod_pos fun i _ => by
      rw [ENNReal.toReal_ofReal (by have := hw i; positivity)]
      have := hw i; positivity
  have hG0' := hG0 t0 ht0
  have hup : ∫⁻ t in box t0 w ε, g t ≤ ENNReal.ofReal (G t0 + η / 2) * volume (box t0 w ε) := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    rw [hgG t (hU' t ht)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).2])
  have hlo : ENNReal.ofReal (G t0 - η / 2) * volume (box t0 w ε) ≤ ∫⁻ t in box t0 w ε, g t := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    rw [hgG t (hU' t ht)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).1])
  have hfin : ∫⁻ t in box t0 w ε, g t ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hup' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hlo' := ENNReal.toReal_mono hfin hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (G t0 - η / 2) * (volume (box t0 w ε)).toReal ≤
      (∫⁻ t in box t0 w ε, g t).toReal :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _) hV0.le) hlo'
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hV0]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hV0]; nlinarith


/-! ### Coefficient coordinates -/

variable {n : ℕ}

/-- **Coefficient weights** $w_{ii} = 1$, $w_{ij} = 2$ ($i < j$): $c_{ij} = w_{ij}\,a_{ij}$. -/
def wt (p : UIdx n) : ℝ := if p.1.1 = p.1.2 then 1 else 2

theorem wt_pos (p : UIdx n) : 0 < wt p := by unfold wt; split_ifs <;> norm_num

/-- $\prod_{i \le j} w_{ij} = 2^{n(n-1)/2}$ (the number of off-diagonal pairs). -/
theorem prod_wt : ∀ n : ℕ, ∏ p : UIdx n, wt p = (2 : ℝ) ^ (n * (n - 1) / 2)
  | 0 => by simp
  | n + 1 => by
    have h1 : ∀ a, wt (eU n (.inl a)) = 1 := by intro a; simp [wt, eU]
    have h2 : ∀ j, wt (eU n (.inr (.inl j))) = 2 := by
      intro j; simp [wt, eU, (Fin.succ_ne_zero j).symm]
    have h3 : ∀ p, wt (eU n (.inr (.inr p))) = wt p := by intro p; simp [wt, eU, Fin.succ_inj]
    rw [← Equiv.prod_comp (eU n), Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [h1, h2, h3, prod_wt n, Finset.prod_const_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, one_mul, ← pow_add]
    congr 1
    rcases n with _ | k
    · simp
    · rw [show (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) by
        simp only [Nat.add_sub_cancel]; ring, Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- **The coefficient vector** $(c_{ij})_{0 \le i \le j < n}$ of a real form $Q$ (the point $c_Q$ of $\mathbb R^{n(n+1)/2}$). -/
def coeffU (Q : QuadForm ℝ n) : UIdx n → ℝ := fun p => Q.coeff p.1.1 p.1.2

/-- **The coefficient vector of $Q \circ X$**, $\vec y \mapsto Q(\sum_j y_jX_j)$ ($X_j$ = column $j$ of $X$):
$Q(X_i)$ at $(i,i)$ and $Q(X_i + X_j) - Q(X_i) - Q(X_j)$ at $(i,j)$, $i < j$. This is $\Phi_Q(X)$; $\Phi_Q^{-1}(c_Q) = O(Q)$. -/
def pullCoeff (Q : QuadForm ℝ n) (X : Fin n → Fin n → ℝ) : UIdx n → ℝ := fun p =>
  if p.1.1 = p.1.2 then Q.eval (X p.1.1)
  else Q.eval (X p.1.1 + X p.1.2) - Q.eval (X p.1.1) - Q.eval (X p.1.2)


/-- **Siegel's volume ratio** for $O(Q)$ (coefficient coordinates, sup-norm balls):
$$\frac{\mathrm{Leb}\{X \in M_n(\mathbb R) : \|\Phi_Q(X) - c_Q\|_\infty \le \varepsilon\}}{\mathrm{Leb}\{c \in \mathbb R^{n(n+1)/2} : \|c - c_Q\|_\infty \le \varepsilon\}}.$$ -/
@[kb "kitaoka1993" "§5.6 (archimedean local density α_∞(S,S)) [unverified]"]
def siegelRatio (Q : QuadForm ℝ n) (ε : ℝ) : ℝ :=
  (volume {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε}).toReal /
    (volume (Metric.closedBall (coeffU Q) ε)).toReal

/-- **$\mathrm{vol}(O(Q), dX/dS)$**, the total mass of the gauge form $dX/dS$ on $O(Q) = \Phi_Q^{-1}(c_Q)$, defined as
Siegel's limit $\lim_{\varepsilon \to 0^+}$ `siegelRatio Q ε` (the archimedean local density $\alpha_\infty(Q, Q)$). For
positive definite $Q$ the limit exists (`tendsto_siegelRatio`). -/
@[kb "weil1982" "§2.2, §2.4 (gauge forms; matching forms on G, H, G/H) [unverified]"]
def archVolO (Q : QuadForm ℝ n) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (siegelRatio Q)

section Link

open QuadFormsKB.Siegel

theorem gram_symm (Q : QuadForm ℝ n) (x y : Fin n → ℝ) :
    x ⬝ᵥ (gramMatrixR Q *ᵥ y) = y ⬝ᵥ (gramMatrixR Q *ᵥ x) := by
  have hT : (gramMatrixR Q)ᵀ = gramMatrixR Q := by
    have := gramMatrixR_isHermitian Q
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

theorem polar_gram (Q : QuadForm ℝ n) (a b : Fin n → ℝ) :
    Q.eval (a + b) - Q.eval a - Q.eval b = 2 * (a ⬝ᵥ (gramMatrixR Q *ᵥ b)) := by
  rw [eval_real_eq_gramR, eval_real_eq_gramR, eval_real_eq_gramR, mulVec_add, dotProduct_add,
    add_dotProduct, add_dotProduct, gram_symm Q b a]
  ring

theorem pullCoeff_eq (Q : QuadForm ℝ n) (X : Fin n → Fin n → ℝ) :
    pullCoeff Q X = fun p => wt p * (X p.1.1 ⬝ᵥ (gramMatrixR Q *ᵥ X p.1.2)) := by
  funext p
  by_cases h : p.1.1 = p.1.2
  · simp only [pullCoeff, wt, if_pos h, one_mul, eval_real_eq_gramR]; rw [h]
  · simp only [pullCoeff, wt, if_neg h, polar_gram]

theorem coeffU_eq (Q : QuadForm ℝ n) :
    coeffU Q = fun p => wt p * gramMatrixR Q p.1.1 p.1.2 := by
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only [coeffU, wt, gramMatrixR, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; ring
  · have : Q.coeff j i = 0 := Q.upper (show id i < id j from lt_of_le_of_ne hij h)
    simp [h, this]

/-- $A = P^{\mathsf T}P$ for positive definite $Q$, with $|\det P| = \sqrt d$ (from `Siegel.exists_sqrt_factor`). -/
theorem sqrt_factor_dot (Q : QuadForm ℝ n) (hQ : IsPosDefR Q) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ x y, x ⬝ᵥ (gramMatrixR Q *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) ∧
      0 < gramDetR Q ∧ |P.det| = Real.sqrt (gramDetR Q) := by
  obtain ⟨P, hP, hpos, hdet⟩ := exists_sqrt_factor (gramMatrixR Q) (gramMatrixR_isHermitian Q)
    (fun x hx => by rw [← eval_real_eq_gramR]; exact hQ x hx)
  refine ⟨P, fun x y => ?_, by rwa [gramDetR_eq_det], by rw [hdet, gramDetR_eq_det]⟩
  have hd : ∀ z, z ⬝ᵥ (gramMatrixR Q *ᵥ z) = (P *ᵥ z) ⬝ᵥ (P *ᵥ z) := fun z => by
    rw [hP]; simp only [dotProduct, sq]
  have e := hd (x + y)
  simp only [mulVec_add, dotProduct_add, add_dotProduct] at e
  rw [gram_symm Q y x, hd x, hd y, dotProduct_comm (P *ᵥ y) (P *ᵥ x)] at e
  linarith

/-- The upper coordinates $(a_{ij})_{i \le j}$ of the Gram matrix $A = H/2$. -/
def gramVec (Q : QuadForm ℝ n) : UIdx n → ℝ := fun p => gramMatrixR Q p.1.1 p.1.2

theorem symU_gramVec (Q : QuadForm ℝ n) : symU (gramVec Q) = gramMatrixR Q := by
  ext i j
  simp only [symU, gramVec, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have := gramMatrixR_isHermitian Q
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact (congrFun (congrFun this i) j)

theorem piv_gramVec {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) : piv n (gramVec Q) :=
  piv_of_PDU n _ fun x hx => by rw [symU_gramVec, ← eval_real_eq_gramR]; exact hQ x hx

theorem closedBall_eq_box (c : UIdx n → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    Metric.closedBall c ε = box c (fun _ => 1) ε := by
  rw [closedBall_pi _ hε, box]; simp

/-- $\{X : \Phi_Q(X) \in B_\varepsilon(c_Q)\} = \{X : (PX)^{\mathsf T}(PX) \in \text{box}\}$ in Gram coordinates. -/
theorem setOf_pullCoeff_eq (Q : QuadForm ℝ n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ x y, x ⬝ᵥ (gramMatrixR Q *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) {ε : ℝ} (hε : 0 ≤ ε) :
    {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε} =
      (fun X : Fin n → Fin n → ℝ => gramU (fun j => P *ᵥ X j)) ⁻¹' box (gramVec Q) wt ε := by
  ext X
  rw [Set.mem_preimage, box, Set.mem_univ_pi]
  show pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε ↔ _
  rw [closedBall_pi _ hε, Set.mem_univ_pi]
  refine forall_congr' fun p => ?_
  rw [Metric.mem_closedBall, Metric.mem_closedBall, Real.dist_eq, Real.dist_eq, pullCoeff_eq,
    coeffU_eq]
  simp only [gramU, gramVec, hP]
  rw [← mul_sub, abs_mul, abs_of_pos (wt_pos p), le_div_iff₀ (wt_pos p), mul_comm]

/-- $\mathrm{Leb}\{X : \Phi_Q(X) \in B_\varepsilon(c_Q)\} = |\det P|^{-n}\int_{\text{box}}\rho_n$ (`lintegral_gram`). -/
theorem volume_setOf_pullCoeff (Q : QuadForm ℝ n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ x y, x ⬝ᵥ (gramMatrixR Q *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) (hP0 : P.det ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) :
    volume {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε} =
      ENNReal.ofReal (|P.det|⁻¹) ^ n * ∫⁻ t in box (gramVec Q) wt ε, densR n t := by
  have hB : MeasurableSet (box (gramVec Q) wt ε) :=
    MeasurableSet.univ_pi fun i => measurableSet_closedBall
  have hc : Continuous fun X : Fin n → Fin n → ℝ => gramU (fun j => P *ᵥ X j) :=
    continuous_gramU.comp (continuous_pi fun j =>
      (Matrix.toLin' P).continuous_of_finiteDimensional.comp (continuous_apply j))
  rw [setOf_pullCoeff_eq Q P hP hε, ← lintegral_indicator_one (hB.preimage hc.measurable)]
  rw [show (fun X : Fin n → Fin n → ℝ => ((fun X : Fin n → Fin n → ℝ => gramU (fun j => P *ᵥ X j)) ⁻¹'
      box (gramVec Q) wt ε).indicator 1 X) = fun X => (box (gramVec Q) wt ε).indicator 1
        (gramU (fun j => P *ᵥ X j)) from rfl,
    lintegral_comp_mulVec_cols P hP0 (G := fun Y => (box (gramVec Q) wt ε).indicator 1 (gramU Y))
      ((measurable_one.indicator hB).comp continuous_gramU.measurable),
    lintegral_gram n (f := (box (gramVec Q) wt ε).indicator 1) (measurable_one.indicator hB),
    ← lintegral_indicator hB]
  congr 2
  funext t
  by_cases ht : t ∈ box (gramVec Q) wt ε <;> simp [ht]

theorem toReal_volume_closedBall (Q : QuadForm ℝ n) {ε : ℝ} (hε : 0 < ε) :
    (volume (Metric.closedBall (coeffU Q) ε)).toReal =
      (volume (box (gramVec Q) wt ε)).toReal * (2 : ℝ) ^ (n * (n - 1) / 2) := by
  rw [closedBall_eq_box _ hε.le, volume_box, volume_box, ENNReal.toReal_prod, ENNReal.toReal_prod,
    ← prod_wt, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  have := wt_pos p
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  field_simp

theorem cprod_eq (n : ℕ) : cprod n =
    ∏ j ∈ Finset.range n, Real.pi ^ (((j : ℝ) + 1) / 2) / Real.Gamma (((j : ℝ) + 1) / 2) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [kap]

theorem archVolSO_eq_aux {d : ℝ} (hd : 0 < d) :
    ((Real.sqrt d)⁻¹ ^ n / (2 : ℝ) ^ (n * (n - 1) / 2)) * (cprod n * d ^ (-(1 / 2 : ℝ))) =
      2 * Tamagawa.archVolSO n d := by
  rw [Tamagawa.archVolSO, ← cprod_eq]
  have h : (Real.sqrt d)⁻¹ ^ n * d ^ (-(1 / 2 : ℝ)) = d ^ (-((n : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hd.le,
      ← Real.rpow_add hd]
    congr 1; ring
  rw [← h]
  field_simp

/-- **Siegel's limit for $O(Q)$** ($Q$ positive definite, any $n \ge 0$, $d = \det(H/2)$):
$$\lim_{\varepsilon \to 0^+}\texttt{siegelRatio}\ Q\ \varepsilon = 2\cdot\texttt{archVolSO}\ n\ d
= 2^{-n(n-1)/2}\,d^{-(n+1)/2}\prod_{j=0}^{n-1}\frac{\pi^{(j+1)/2}}{\Gamma((j+1)/2)}.$$ -/
@[kb "siegel1935" "vol(O_n(R), dX/dS) = ∏_{j=1}^n π^{j/2}/Γ(j/2) [unverified]"]
theorem tendsto_siegelRatio {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) :
    Tendsto (siegelRatio Q) (𝓝[>] 0) (𝓝 (2 * Tamagawa.archVolSO n (gramDetR Q))) := by
  obtain ⟨P, hP, hd, hdetP⟩ := sqrt_factor_dot Q hQ
  have hP0 : P.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdetP; exact (Real.sqrt_pos.mpr hd).ne' hdetP.symm
  set G : (UIdx n → ℝ) → ℝ := fun t => cprod n * (symU t).det ^ (-(1 / 2 : ℝ))
  have hpiv := piv_gramVec hQ
  have havg := tendsto_avg_box (g := densR n) (G := G) (isOpen_piv n) hpiv
    (ContinuousOn.mul continuousOn_const (continuous_det_symU.continuousOn.rpow_const
      fun t ht => Or.inl (densR_of_piv n t ht).1.ne'))
    (fun t ht => mul_nonneg (cprod_pos n).le (Real.rpow_nonneg (densR_of_piv n t ht).1.le _))
    (fun t ht => (densR_of_piv n t ht).2) wt wt_pos
  have hG : G (gramVec Q) = cprod n * gramDetR Q ^ (-(1 / 2 : ℝ)) := by
    simp only [G, symU_gramVec, gramDetR_eq_det]
  rw [hG] at havg
  have hlim := havg.const_mul ((Real.sqrt (gramDetR Q))⁻¹ ^ n / (2 : ℝ) ^ (n * (n - 1) / 2))
  rw [archVolSO_eq_aux hd] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [siegelRatio, volume_setOf_pullCoeff Q P hP hP0 hε.le, toReal_volume_closedBall Q hε,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity), hdetP]
  have hV : 0 < (volume (box (gramVec Q) wt ε)).toReal := by
    rw [volume_box, ENNReal.toReal_prod]
    exact Finset.prod_pos fun i _ => by
      have := wt_pos i
      rw [ENNReal.toReal_ofReal (by positivity)]; positivity
  field_simp

/-- **The closed form is half the gauge-form volume of $O(Q)$:** `archVolSO n d` $= \mathrm{vol}(O(Q), dX/dS)/2$. -/
@[kb "siegel1935" "vol(O_n(R), dX/dS) [unverified]"]
theorem archVolSO_eq_archVolO {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) :
    Tamagawa.archVolSO n (gramDetR Q) = archVolO Q / 2 := by
  rw [archVolO, (tendsto_siegelRatio hQ).limUnder_eq]; ring

end Link


open QuadFormsKB.Siegel (IsPosDefR gramDetR gramMatrixR eval_real_eq_gramR continuous_eval_real)


theorem symU_gramU (X : Fin n → Fin n → ℝ) :
    symU (gramU X) = Matrix.of X * (Matrix.of X)ᵀ := by
  ext i j
  simp only [symU, gramU, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  split_ifs
  · rfl
  · rw [dotProduct_comm]; rfl

theorem det_symU_gramU (X : Fin n → Fin n → ℝ) :
    (symU (gramU X)).det = (Matrix.of X).det ^ 2 := by
  rw [symU_gramU, det_mul, det_transpose, sq]

theorem piv_of_densR_ne_zero : ∀ (n : ℕ) (t : UIdx n → ℝ), densR n t ≠ 0 → piv n t
  | 0, _, _ => trivial
  | n + 1, t, h => by
    simp only [densR] at h
    split_ifs at h with hs
    · exact ⟨hs, piv_of_densR_ne_zero n _ (right_ne_zero_of_mul h)⟩
    · exact absurd rfl h

/-- $\{X : \det X = 0\}$ is Lebesgue-null (from `lintegral_gram`: $\det(X^{\mathsf T}X) = \det(X)^2$ and $\rho_n = 0$ where
$\det t = 0$). -/
theorem volume_det_eq_zero :
    volume {X : Fin n → Fin n → ℝ | (Matrix.of X).det = 0} = 0 := by
  have hZ : MeasurableSet {t : UIdx n → ℝ | (symU t).det = 0} :=
    measurableSet_eq_fun continuous_det_symU.measurable measurable_const
  have hset : {X : Fin n → Fin n → ℝ | (Matrix.of X).det = 0} =
      gramU ⁻¹' {t : UIdx n → ℝ | (symU t).det = 0} := by
    ext X; simp [det_symU_gramU]
  rw [hset, ← lintegral_indicator_one (hZ.preimage continuous_gramU.measurable)]
  rw [show (fun X : Fin n → Fin n → ℝ => (gramU ⁻¹' {t : UIdx n → ℝ | (symU t).det = 0}).indicator 1 X)
      = fun X => {t : UIdx n → ℝ | (symU t).det = 0}.indicator 1 (gramU X) from rfl,
    lintegral_gram n (measurable_one.indicator hZ)]
  refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun t => ?_)
  by_cases h : densR n t = 0
  · simp [h]
  · have := (densR_of_piv n t (piv_of_densR_ne_zero n t h)).1
    have ht : t ∉ {t : UIdx n → ℝ | (symU t).det = 0} := by simp [this.ne']
    simp [ht]


section Reflection

open QuadFormsKB.Siegel

theorem continuous_pullCoeff (Q : QuadForm ℝ n) : Continuous (pullCoeff Q) := by
  refine continuous_pi fun p => ?_
  unfold pullCoeff
  have hc := continuous_eval_real Q
  split_ifs
  · exact hc.comp (continuous_apply _)
  · exact ((hc.comp (by fun_prop : Continuous fun a : Fin n → Fin n → ℝ => a p.1.1 + a p.1.2)).sub
      (hc.comp (continuous_apply _))).sub (hc.comp (continuous_apply _))

/-- **A reflection in $O(Q)$** ($Q$ positive definite, $n \ge 1$): $R = 1 - \frac{2}{e^{\mathsf T}Ae}e\,e^{\mathsf T}A$, $e = e_0$,
has $\det R = -1$ and $Q(Rv) = Q(v)$. -/
theorem exists_reflection {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, R.det = -1 ∧ ∀ v, Q.eval (R *ᵥ v) = Q.eval v := by
  set A := gramMatrixR Q
  set e : Fin n → ℝ := Pi.single ⟨0, hn⟩ 1
  have he : e ≠ 0 := by
    intro h; have := congrFun h ⟨0, hn⟩; simp [e] at this
  set a := e ⬝ᵥ (A *ᵥ e)
  have ha : 0 < a := by simp only [a, A, ← eval_real_eq_gramR]; exact hQ e he
  set u : Fin n → ℝ := -(2 / a) • e
  set w : Fin n → ℝ := e ᵥ* A
  refine ⟨1 + replicateCol Unit u * replicateRow Unit w, ?_, fun v => ?_⟩
  · rw [det_one_add_replicateCol_mul_replicateRow]
    simp only [u, w, dotProduct_smul, smul_eq_mul, ← dotProduct_mulVec]
    field_simp; ring
  · have hR : (1 + replicateCol Unit u * replicateRow Unit w) *ᵥ v = v + (e ⬝ᵥ (A *ᵥ v)) • u := by
      rw [add_mulVec, one_mulVec, ← vecMulVec_eq, vecMulVec_mulVec, op_smul_eq_smul]
      simp only [w, ← dotProduct_mulVec]
    rw [hR, eval_real_eq_gramR, eval_real_eq_gramR]
    simp only [u, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, gram_symm Q v e]
    field_simp
    ring


theorem pullCoeff_mulVec (Q : QuadForm ℝ n) (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : ∀ v, Q.eval (R *ᵥ v) = Q.eval v) (X : Fin n → Fin n → ℝ) :
    pullCoeff Q (fun j => R *ᵥ X j) = pullCoeff Q X := by
  funext p
  simp only [pullCoeff, ← mulVec_add, hR]

theorem det_of_mulVec (R : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Fin n → ℝ) :
    (Matrix.of fun j => R *ᵥ X j).det = (Matrix.of X).det * R.det := by
  have : (Matrix.of fun j => R *ᵥ X j) = Matrix.of X * Rᵀ := by
    ext j k
    simp [mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  rw [this, det_mul, det_transpose]

/-- **Half of the fibre lies in $SO$:** for positive definite $Q$, $n \ge 1$ and any measurable $E$,
$2\,\mathrm{Leb}\{X : \det X > 0,\ \Phi_Q(X) \in E\} = \mathrm{Leb}\{X : \Phi_Q(X) \in E\}$. -/
theorem two_mul_volume_det_pos {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n)
    {E : Set (UIdx n → ℝ)} (hE : MeasurableSet E) :
    2 * volume {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧ pullCoeff Q X ∈ E} =
      volume {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ E} := by
  obtain ⟨R, hRdet, hR⟩ := exists_reflection hQ hn
  have hmp : MeasurePreserving (fun (X : Fin n → Fin n → ℝ) j => R *ᵥ X j) volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec R (by rw [hRdet]; norm_num)
  have hdetc : Continuous fun X : Fin n → Fin n → ℝ => (Matrix.of X).det :=
    Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))
  have hmE : MeasurableSet {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ E} :=
    hE.preimage (continuous_pullCoeff Q).measurable
  have hmP : MeasurableSet {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det} :=
    measurableSet_lt measurable_const hdetc.measurable
  have hmN : MeasurableSet {X : Fin n → Fin n → ℝ | (Matrix.of X).det < 0} :=
    measurableSet_lt hdetc.measurable measurable_const
  set E' := {X : Fin n → Fin n → ℝ | pullCoeff Q X ∈ E}
  set Pos := {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det}
  set Neg := {X : Fin n → Fin n → ℝ | (Matrix.of X).det < 0}
  have hPN : volume (Pos ∩ E') = volume (Neg ∩ E') := by
    rw [← hmp.measure_preimage (hmN.inter hmE).nullMeasurableSet]
    congr 1
    ext X
    simp only [Pos, Neg, E', mem_preimage, mem_inter_iff, mem_ofPred_eq, det_of_mulVec, hRdet,
      pullCoeff_mulVec Q R hR]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
  have hdiff : volume (E' \ Pos) = volume (Neg ∩ E') := by
    refine le_antisymm ?_ (measure_mono fun X ⟨hN, hE'⟩ => ⟨hE', fun hP => by
      simp only [Pos, Neg, mem_ofPred_eq] at hN hP; linarith⟩)
    calc volume (E' \ Pos) ≤ volume ((Neg ∩ E') ∪ {X : Fin n → Fin n → ℝ | (Matrix.of X).det = 0}) :=
          measure_mono fun X ⟨hE', hP⟩ => by
            simp only [Pos, mem_ofPred_eq, not_lt] at hP
            rcases hP.lt_or_eq with h | h
            · exact Or.inl ⟨h, hE'⟩
            · exact Or.inr h
      _ ≤ volume (Neg ∩ E') + volume {X : Fin n → Fin n → ℝ | (Matrix.of X).det = 0} :=
          measure_union_le _ _
      _ = volume (Neg ∩ E') := by rw [volume_det_eq_zero, add_zero]
  rw [← measure_inter_add_sdiff E' hmP, hdiff, ← hPN, two_mul, inter_comm]
  rfl

end Reflection

/-- **Siegel's volume ratio for $SO(Q)$:** as `siegelRatio`, counting only $X$ with $\det X > 0$. -/
@[kb "kitaoka1993" "§5.6 (archimedean local density) [unverified]"]
def siegelRatioSO (Q : QuadForm ℝ n) (ε : ℝ) : ℝ :=
  (volume {X : Fin n → Fin n → ℝ | 0 < (Matrix.of X).det ∧
      pullCoeff Q X ∈ Metric.closedBall (coeffU Q) ε}).toReal /
    (volume (Metric.closedBall (coeffU Q) ε)).toReal

/-- **$\mathrm{vol}(SO(Q), dX/dS)$**, Siegel's limit of `siegelRatioSO`: the gauge-form volume of the identity
component $\Phi_Q^{-1}(c_Q) \cap \{\det X > 0\} = SO(Q)$. -/
@[kb "weil1982" "§2.2, §2.4 (gauge forms) [unverified]"]
def archVolSOLim (Q : QuadForm ℝ n) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (siegelRatioSO Q)

theorem siegelRatioSO_eq {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) (ε : ℝ) :
    siegelRatioSO Q ε = siegelRatio Q ε / 2 := by
  have h := two_mul_volume_det_pos hQ hn (E := Metric.closedBall (coeffU Q) ε)
    Metric.isClosed_closedBall.measurableSet
  rw [siegelRatioSO, siegelRatio, ← h, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofNat]
  ring

/-- **Siegel's limit for $SO(Q)$** ($Q$ positive definite, $n \ge 1$): `siegelRatioSO Q ε` $\to$ `archVolSO n d`. -/
@[kb "siegel1935" "vol(SO_n(R), dX/dS) [unverified]"]
theorem tendsto_siegelRatioSO {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) :
    Tendsto (siegelRatioSO Q) (𝓝[>] 0) (𝓝 (Tamagawa.archVolSO n (gramDetR Q))) := by
  have := (tendsto_siegelRatio hQ).div_const 2
  rw [mul_div_cancel_left₀ _ two_ne_zero] at this
  exact this.congr fun ε => (siegelRatioSO_eq hQ hn ε).symm

/-- **`archVolSO` is the gauge-form volume of $SO(Q)$** (headline): for positive definite $Q$ in $n \ge 1$
variables with $d = \det(H/2)$,
$$\texttt{archVolSO}\ n\ d = \mathrm{vol}(SO(Q), dX/dS) = \lim_{\varepsilon \to 0^+}
\frac{\mathrm{Leb}\{X : \det X > 0,\ \|\Phi_Q(X) - c_Q\|_\infty \le \varepsilon\}}{\mathrm{Leb}\{c : \|c - c_Q\|_\infty \le \varepsilon\}}.$$
This replaces the citation behind the definition by a proof. -/
@[kb "siegel1935" "vol(SO_n(R), dX/dS) [unverified]"]
theorem archVolSO_eq_volume {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) (hn : 1 ≤ n) :
    Tamagawa.archVolSO n (gramDetR Q) = archVolSOLim Q :=
  ((tendsto_siegelRatioSO hQ hn).limUnder_eq).symm


open QuadFormsKB.Siegel (gramDetR_pos hessian_map_NF)
open NumberField

/-- **Cross-check, $n = 1$:** $\mathrm{vol}(SO_1(Q)) = 1/(2d)$, `archVolSO_one`. Directly: $\{x : |dx^2 - d| \le \varepsilon,\ x > 0\}$ has
length $\approx \varepsilon/d$, over $2\varepsilon$. -/
@[kb "siegel1935" "vol(SO_1) [unverified]"]
theorem archVolSOLim_one {Q : QuadForm ℝ 1} (hQ : IsPosDefR Q) :
    archVolSOLim Q = 1 / (2 * gramDetR Q) := by
  rw [← archVolSO_eq_volume hQ le_rfl, RankOne.archVolSO_one]

/-- `archVolSO 2 d` $= \frac{\pi}{4}d^{-3/2}$. -/
theorem archVolSO_two (d : ℝ) : Tamagawa.archVolSO 2 d = Real.pi / 4 * d ^ (-(3 / 2 : ℝ)) := by
  rw [Tamagawa.archVolSO, Finset.prod_range_succ, Finset.prod_range_one]
  norm_num [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  have : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp

/-- **Cross-check, $n = 2$:** $\mathrm{vol}(O(Q), dX/dS) = \frac{\pi}{2}d^{-3/2}$ in coefficient coordinates, i.e.
$\pi\,d^{-3/2}$ in Gram coordinates; at $Q = x_0^2 + x_1^2$ this is the classical $\mathrm{vol}(O_2(\mathbb R)) = \pi^{1/2}/\Gamma(1/2)\cdot\pi/\Gamma(1) = \pi$. -/
@[kb "siegel1935" "vol(O_2(R)) [unverified]"]
theorem archVolO_two {Q : QuadForm ℝ 2} (hQ : IsPosDefR Q) :
    archVolO Q = Real.pi / 2 * gramDetR Q ^ (-(3 / 2 : ℝ)) := by
  have := archVolSO_eq_archVolO hQ
  rw [archVolSO_two] at this
  linarith

/-- **The archimedean factor is a volume:** for $Q_0$ over $\mathcal O_F$, a complex embedding $\sigma$ that is real
($\sigma = \rho$ for a ring map $\rho : F \to \mathbb R$) and $Q_\sigma = \rho(Q_0)$ positive definite ($n \ge 1$),
`archVolSO n (detGram Q₀ σ)` $= \mathrm{vol}(SO(Q_\sigma), dX/dS)$. So each factor of `tamagawaK`'s archimedean product
is a theorem. -/
@[kb "weil1982" "§2.3 (Tamagawa measure, archimedean factor) [unverified]"]
theorem archVolSO_detGram_eq {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) n)
    (σ : F →ₐ[ℚ] ℂ) (ρ : F →+* ℝ) (hσ : ∀ x, σ x = (ρ x : ℂ))
    (hQ : IsPosDefR (Q₀.map (ρ.comp (algebraMap (𝓞 F) F)))) (hn : 1 ≤ n) :
    Tamagawa.archVolSO n (Tamagawa.detGram Q₀ σ) =
      archVolSOLim (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))) := by
  have hdet : Tamagawa.detGram Q₀ σ = gramDetR (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))) := by
    have hpos := gramDetR_pos hQ
    rw [Tamagawa.detGram, hσ, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hpos]
    congr 1
    rw [gramDetR, hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp [map_ofNat]
  rw [hdet, archVolSO_eq_volume hQ hn]


/-! ### `pullCoeff` is the coefficient vector of $Q \circ X$ -/

/-- $\sum_{i,j}f_{ij} = \sum_{i \le j}w_{ij}f_{ij}$ for symmetric $f$. -/
theorem sum_symm_upper (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, ∑ j, if i ≤ j then (if i = j then 1 else 2) * f i j else 0 := by
  have h1 : ∀ i j, f i j = (if i ≤ j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j; by_cases h : i ≤ j
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i ≤ j then f i j else 0) + (if j < i then f i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    _ = ∑ i, ∑ j, (if i ≤ j then f i j else 0) + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (if i ≤ j then f i j else 0) + ∑ i, ∑ j, (if i < j then f i j else 0) := by
        rw [h2]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j
        · subst hij; simp
        · by_cases h : i ≤ j
          · simp [h, hij, lt_of_le_of_ne h hij]; ring
          · simp [h, hij]; intro h'; exact absurd h'.le h

/-- **The transformed form** $Q \circ X : \vec y \mapsto Q(\sum_j y_jX_j)$, as a `QuadForm` with coefficients `pullCoeff Q X`. -/
def pullForm (Q : QuadForm ℝ n) (X : Fin n → Fin n → ℝ) : QuadForm ℝ n :=
  QuadForm.ofUpper fun i j => if h : i ≤ j then pullCoeff Q X ⟨(i, j), h⟩ else 0

theorem coeffU_pullForm (Q : QuadForm ℝ n) (X : Fin n → Fin n → ℝ) :
    coeffU (pullForm Q X) = pullCoeff Q X := by
  funext p
  simp [coeffU, pullForm, QuadForm.ofUpper, p.2]

/-- **Faithfulness of `pullCoeff`:** the form with coefficients $\Phi_Q(X)$ is $\vec y \mapsto Q(\sum_j y_jX_j)$, so
$\Phi_Q(X) = c_Q$ iff $X$ is an isometry of $Q$ (`coeffU_pullForm`). -/
@[kb "omeara1963" "§41 (coefficients of a transformed form)"]
theorem eval_pullForm (Q : QuadForm ℝ n) (X : Fin n → Fin n → ℝ) (y : Fin n → ℝ) :
    (pullForm Q X).eval y = Q.eval (∑ j, y j • X j) := by
  set A := gramMatrixR Q
  rw [eval_real_eq_gramR Q]
  have hexp : (∑ j, y j • X j) ⬝ᵥ (A *ᵥ ∑ j, y j • X j) =
      ∑ i, ∑ j, y i * y j * (X i ⬝ᵥ (A *ᵥ X j)) := by
    simp only [mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [gram_symm Q (X j) (X i)]; ring
  rw [hexp, sum_symm_upper _ (fun i j => by rw [gram_symm Q (X i) (X j)]; ring)]
  simp only [QuadForm.evalIn, pullForm, QuadForm.ofUpper, Matrix.of_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i ≤ j
  · simp only [h, if_true, dif_pos h, pullCoeff_eq, wt]
    split_ifs <;> ring
  · simp [h]

end QuadFormsKB.Tamagawa.ArchVol
