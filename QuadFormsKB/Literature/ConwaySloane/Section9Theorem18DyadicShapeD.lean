/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for the shape $\langle a\rangle \perp 8K \perp 64\langle d\rangle$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** Over $\mathbb Q$ at the prime $v$ over $2$; a basis $\gamma$ of $L_2$ with Gram matrix $G$ =
`locGram Q v γ` of the bilinear form $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**The shape.** In Conway–Sloane's notation (form matrix $M$, $Q(x) = x^{\mathsf T}Mx$, $G = 2M$) the $2$-adic lattice
$\langle a\rangle \perp 8K \perp 64\langle d\rangle$, with $a, d$ $2$-adic units and $K$ a binary even unimodular
form, has in a Jordan basis $b_0, \dots, b_3$ the Gram matrix
$$G = \begin{pmatrix}2a&0&0&0\\0&16\cdot 2\alpha&16\beta&0\\0&16\beta&16\cdot 2\delta&0\\0&0&0&128d\end{pmatrix}
\quad (\texttt{shapeDG}),$$
with $\lvert a\rvert = \lvert\beta\rvert = \lvert d\rvert = 1$, $\lvert\alpha\rvert, \lvert\delta\rvert \le 1$ (so the
middle block is $16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}$, an even unimodular block scaled by
$16$, with $4\alpha\delta - \beta^2$ a unit: `valued_famD`).

**The chain** (`PeelChainPair Q v γ ∅ [(0, none)]`; $e_k$ the standard basis):
1. *Peel* $b_0$: $b_0 \perp b_1, b_2, b_3$ and the entries $32\alpha, 16\beta, 32\delta, 128d, 0$ of the complement
   have absolute value $\le \lvert 2G_{00}\rvert = \lvert 4\rvert$. Fixed set $T = \{0\}$.
2. *Rescale* the fixed vector (`RelChain.rescale`, $\Lambda = \operatorname{diag}(8, 1, 1, 1)$): the Gram matrix
   becomes $\operatorname{diag}(128a) \perp 16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix} \perp (128d)$.
3. *Halve* $b_0, b_3$ (`RelChain.half`, `HalfStep.Data` with $c = \tfrac1{16}$, $C = \{0, 3\}$, $D = \emptyset$): the
   matrix $A = \tfrac1{16}G$ is $\operatorname{diag}(8a) \perp \begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}
   \perp (8d)$, and $\hat A$ has determinant $4\alpha\delta - \beta^2$, a unit. The new basis
   $\tfrac12 b_0, b_1, b_2, \tfrac12 b_3$ has Gram matrix
   $\operatorname{diag}(32a) \perp 16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix} \perp (32d)$.
4. *Block base case* (`RelChain.blockGlue`, $c = \tfrac1{16}$, $l = 3$): on $\{1, 2, 3\}$ the block of $\tfrac1{16}G$
   is $\begin{pmatrix}2\alpha&\beta&0\\\beta&2\delta&0\\0&0&2d\end{pmatrix}$, of the form $E \perp \langle 2d\rangle$,
   $\lvert\det\rvert = \lvert 2\rvert$.
5. *Unit classes* (`UnitRootsBlock`, $T = \{0, 3\}$, $c = \tfrac1{16}$, $i_0 = 1$, $j = 2$): $\tfrac1{16}G$ on
   $\{1, 2\}$ is $\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}$, integral with even diagonal, and
   $\tfrac1{16}G_{12} = \beta$ is a unit.

**Defines** `shapeDG a α β δ d` (the Gram matrix above).

**Proves** `peelChainPair_shapeD`, `theorem18OnlyIf_of_shapeD` (**Theorem 18, "only if", at $p = 2$ for this shape**,
unconditional), `covered10_of_shapeD` (the shape is covered by `Theorem18DyadicCovered10`), and auxiliary lemmas
(Gram matrices of the intermediate bases, `shapeD_halfData`, `shapeD_relChain`, `shapeD_unitRootsBlock`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual10
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicShapeA

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The Gram matrix $G$ of the bilinear form $B$ in a Jordan basis of the $2$-adic lattice
$\langle a\rangle \perp 8K \perp 64\langle d\rangle$, $K = \begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}$
(Conway–Sloane's notation, $G = 2M$; see the module docstring). -/
def shapeDG {K' : Type*} [Field K'] (a α β δ d : K') : Matrix (Fin 4) (Fin 4) K' :=
  !![2 * a, 0, 0, 0; 0, 16 * (2 * α), 16 * β, 0; 0, 16 * β, 16 * (2 * δ), 0; 0, 0, 0, 128 * d]

/-- Evaluate the entries of an explicit `!![...]` matrix at numerals. -/
local macro "shapeD_ent" : tactic =>
  `(tactic| simp only [Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk])

section Aux

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- $e^k \le 1$ for $k \le 0$. -/
theorem shapeD_exp_le_one {k : ℤ} (hk : k ≤ 0) : exp k ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← exp_zero, exp_le_exp]; exact hk

/-- $\lvert 2x\rvert \le 1$ when $\lvert x\rvert \le 1$. -/
theorem shapeD_v_two_mul_le (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x ≤ 1) :
    Valued.v (2 * x) ≤ 1 := by
  rw [map_mul, valued_two_dyadic v h2]
  exact mul_le_one' (shapeD_exp_le_one (by norm_num)) hx

/-- $\lvert 2^k x\rvert \le e^{-k}$ when $\lvert x\rvert \le 1$. -/
theorem shapeD_v_pow_mul_le (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : ℕ) {x : Fv} (hx : Valued.v x ≤ 1) :
    Valued.v ((2 : Fv) ^ k * x) ≤ exp (-(k : ℤ)) := by
  rw [map_mul, map_pow, valued_two_dyadic v h2, ← WithZero.exp_nsmul]
  calc exp (k • (-1 : ℤ)) * Valued.v x ≤ exp (k • (-1 : ℤ)) * 1 := mul_le_mul' le_rfl hx
    _ = exp (-(k : ℤ)) := by rw [mul_one]; simp

/-- $\lvert 16\cdot(2\alpha)\rvert \le e^{-5}$ for $\lvert\alpha\rvert \le 1$. -/
theorem shapeD_v_32_le (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x ≤ 1) :
    Valued.v (16 * (2 * x)) ≤ exp (-5 : ℤ) := by
  have := shapeD_v_pow_mul_le h2 5 hx
  rw [show (2 : Fv) ^ 5 = 32 by norm_num] at this
  rw [show (16 : Fv) * (2 * x) = 32 * x by ring]
  simpa using this

/-- $\lvert 16u\rvert = e^{-4}$ for a unit $u$. -/
theorem shapeD_v_sixteen_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (16 * u) = exp (-4 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 4 hu
  rw [show (2 : Fv) ^ 4 = 16 by norm_num] at this
  simpa using this

/-- $\lvert 128u\rvert = e^{-7}$ for a unit $u$. -/
theorem shapeD_v_128_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (128 * u) = exp (-7 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 7 hu
  rw [show (2 : Fv) ^ 7 = 128 by norm_num] at this
  simpa using this

/-- **Step 2 (rescaling)**: if $G = $ `shapeDG`, then $\gamma\Lambda$, $\Lambda = \operatorname{diag}(8, 1, 1, 1)$,
has Gram matrix $\operatorname{diag}(128a) \perp 16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}
\perp (128d)$. -/
theorem shapeD_locGram_rescale {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) (lam : Fin 4 → Fv)
    (hlam : ∀ i, lam i ≠ 0) {a α β δ d : Fv} (hG : locGram Q v γ = shapeDG a α β δ d)
    (hlam' : lam = ![8, 1, 1, 1]) :
    locGram Q v (γ * diagGL lam hlam) =
      !![128 * a, 0, 0, 0; 0, 32 * α, 16 * β, 0; 0, 16 * β, 32 * δ, 0; 0, 0, 0, 128 * d] := by
  rw [locGram_mul, hG, diagGL_val, diagonal_transpose]
  refine Matrix.ext fun i j => ?_
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [shapeDG, hlam'] <;> ring

/-- The Gram matrix of `HalfStep.gamH γ C` is $W_C^{\mathsf T}GW_C$. -/
theorem shapeD_locGram_gamH {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) (C : Finset (Fin 4)) :
    locGram Q v (HalfStep.gamH γ C) = (HalfStep.W C)ᵀ * locGram Q v γ * HalfStep.W C := by
  unfold locGram
  rw [HalfStep.gamH_val]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **Step 3 (Gram matrix)**: halving $b_0, b_3$ gives $\operatorname{diag}(32a) \perp
16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix} \perp (32d)$. -/
theorem shapeD_locGram_gamH_shape {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) {a α β δ d : Fv}
    (hG : locGram Q v γ =
      !![128 * a, 0, 0, 0; 0, 32 * α, 16 * β, 0; 0, 16 * β, 32 * δ, 0; 0, 0, 0, 128 * d]) :
    locGram Q v (HalfStep.gamH γ {0, 3}) =
      !![32 * a, 0, 0, 0; 0, 32 * α, 16 * β, 0; 0, 16 * β, 32 * δ, 0; 0, 0, 0, 32 * d] := by
  rw [shapeD_locGram_gamH, hG]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [HalfStep.W, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

/-- **Step 3 (hypotheses)**: `HalfStep.Data` with $c = \tfrac1{16}$, $C = \{0, 3\}$, $D = \emptyset$. -/
theorem shapeD_halfData (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a α β δ d : Fv}
    (hG : locGram Q v γ =
      !![128 * a, 0, 0, 0; 0, 32 * α, 16 * β, 0; 0, 16 * β, 32 * δ, 0; 0, 0, 0, 128 * d])
    (ha : Valued.v a = 1) (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1)
    (hd : Valued.v d = 1) : HalfStep.Data Q v γ (1 / 16) {0, 3} ∅ := by
  have hA : ∀ i j, (1 / 16 : Fv) * locGram Q v γ i j =
      !![8 * a, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 8 * d] i j := by
    intro i j
    rw [hG]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hM : (1 / 16 : Fv) • locGram Q v γ =
      !![8 * a, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 8 * d] := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, hA]
  have h4 := shapeA_v_four h2
  have v8a := shapeA_v_eight_mul h2 ha
  have v8d := shapeA_v_eight_mul h2 hd
  have v4a := shapeA_v_four_mul h2 ha
  have v4d := shapeA_v_four_mul h2 hd
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, by simp, by simp, by simp, by simp, ?_⟩
  · intro i j
    rw [hA]
    fin_cases i <;> fin_cases j <;> shapeD_ent <;>
      first
        | (rw [map_zero]; exact zero_le)
        | (rw [v8a]; exact shapeD_exp_le_one (by norm_num))
        | (rw [v8d]; exact shapeD_exp_le_one (by norm_num))
        | with_reducible exact shapeD_v_two_mul_le h2 hα
        | with_reducible exact shapeD_v_two_mul_le h2 hδ
        | with_reducible exact hβ.le
  · intro i
    rw [hA]
    fin_cases i <;> shapeD_ent
    · rw [show (8 * a / 2 : Fv) = 4 * a by ring, v4a]; exact shapeD_exp_le_one (by norm_num)
    · rw [show (2 * α / 2 : Fv) = α by ring]; exact hα
    · rw [show (2 * δ / 2 : Fv) = δ by ring]; exact hδ
    · rw [show (8 * d / 2 : Fv) = 4 * d by ring, v4d]; exact shapeD_exp_le_one (by norm_num)
  · intro i hi j hj
    rw [hG]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hi (by decide)
        | exact absurd (by decide) hj
        | (shapeD_ent; done)
  · intro i hi j hj
    rw [hA]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hj (by decide)
        | (shapeD_ent; rw [map_zero]; exact zero_le)
        | (shapeD_ent; rw [v8a, h4, exp_le_exp]; norm_num)
        | (shapeD_ent; rw [v8d, h4, exp_le_exp]; norm_num)
  · intro i hi
    rw [hA]
    fin_cases i <;>
      first
        | exact absurd hi (by decide)
        | (shapeD_ent; rw [show (8 * a / 2 : Fv) = 4 * a by ring, v4a, h4])
        | (shapeD_ent; rw [show (8 * d / 2 : Fv) = 4 * d by ring, v4d, h4])
  · have hat : HalfStep.hatA ((1 / 16 : Fv) • locGram Q v γ) {0, 3} ∅ =
        !![1, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 1] := by
      rw [hM]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [HalfStep.hatA]
    have hdet : (!![1, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) Fv).det =
        4 * α * δ - β ^ 2 := by
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      ring
    rw [hat, hdet]
    exact valued_famD h2 hα hδ hβ

/-- **Step 4 (block base case)**: for the Gram matrix $\operatorname{diag}(32a) \perp
16\begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix} \perp (32d)$, `RelChain Q v {0} γ` holds by
`RelChain.blockGlue` ($c = \tfrac1{16}$, $l = 3$). -/
theorem shapeD_relChain_base (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a α β δ d : Fv}
    (hG : locGram Q v γ =
      !![32 * a, 0, 0, 0; 0, 32 * α, 16 * β, 0; 0, 16 * β, 32 * δ, 0; 0, 0, 0, 32 * d])
    (ha : Valued.v a = 1) (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1)
    (hd : Valued.v d = 1) : RelChain Q v {0} γ := by
  have hA : ∀ i j, (1 / 16 : Fv) * locGram Q v γ i j =
      !![2 * a, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 2 * d] i j := by
    intro i j
    rw [hG]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hM : (1 / 16 : Fv) • locGram Q v γ =
      !![2 * a, 0, 0, 0; 0, 2 * α, β, 0; 0, β, 2 * δ, 0; 0, 0, 0, 2 * d] := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, hA]
  have hfam := valued_famD h2 hα hδ hβ
  have hdet : (compBlock {0} ((1 / 16 : Fv) • locGram Q v γ)).det = (4 * α * δ - β ^ 2) * (2 * d) := by
    have h := det_eq_compBlock_single ((1 / 16 : Fv) • locGram Q v γ) 0
      (fun j hj => by
        rw [hM]; fin_cases j <;> first | exact absurd rfl hj | (shapeD_ent; done))
      (fun j hj => by
        rw [hM]; fin_cases j <;> first | exact absurd rfl hj | (shapeD_ent; done))
    have hd4 : ((1 / 16 : Fv) • locGram Q v γ).det = 2 * a * (2 * d) * (4 * α * δ - β ^ 2) := by
      rw [hM]
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      ring
    have h00 : ((1 / 16 : Fv) • locGram Q v γ) 0 0 = 2 * a := by rw [hM]; rfl
    rw [hd4, h00] at h
    have ha0 : (2 * a : Fv) ≠ 0 := mul_ne_zero (by norm_num) (shapeA_ne_zero_of_v_one ha)
    refine mul_left_cancel₀ ha0 ?_
    linear_combination (-1 : Fv) * h
  refine RelChain.blockGlue (c := 1 / 16) 3 ?_ (by norm_num) (by decide) ?_ ?_ ?_ ?_ ?_
  · intro t ht m hm
    have : t = 0 := by simpa using ht
    subst this
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (shapeD_ent; done)
  · intro i j hi hj
    rw [hA]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd (by decide) hi
        | exact absurd (by decide) hj
        | (shapeD_ent; rw [map_zero]; exact zero_le)
        | (shapeD_ent; with_reducible exact shapeD_v_two_mul_le h2 hα)
        | (shapeD_ent; with_reducible exact shapeD_v_two_mul_le h2 hδ)
        | (shapeD_ent; with_reducible exact hβ.le)
        | (shapeD_ent; rw [shapeA_v_two_mul h2 hd]; exact shapeD_exp_le_one (by norm_num))
  · intro i hi
    rw [hA]
    fin_cases i <;>
      first
        | exact absurd (by decide) hi
        | (shapeD_ent; rw [show (2 * α / 2 : Fv) = α by ring]; exact hα)
        | (shapeD_ent; rw [show (2 * δ / 2 : Fv) = δ by ring]; exact hδ)
        | (shapeD_ent; rw [show (2 * d / 2 : Fv) = d by ring, hd])
  · intro i hi hi3
    rw [hG]
    fin_cases i <;> first | exact absurd rfl hi3 | exact absurd (by decide) hi | (shapeD_ent; done)
  · rw [hA]; shapeD_ent; rw [show (2 * d / 2 : Fv) = d by ring, hd]
  · rw [hdet, map_mul, hfam, one_mul, shapeA_v_two_mul h2 hd, valued_two_dyadic v h2]

/-- **Steps 2–4**: `RelChain Q v {0} γ` for the Gram matrix `shapeDG a α β δ d`: rescale $b_0$ by $8$, halve
$b_0, b_3$, then the block base case. -/
theorem shapeD_relChain (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a α β δ d : Fv} (hG : locGram Q v γ = shapeDG a α β δ d)
    (ha : Valued.v a = 1) (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1)
    (hd : Valued.v d = 1) : RelChain Q v {0} γ := by
  have h8ne : (8 : Fv) ≠ 0 := by norm_num
  have hlam : ∀ i, (![8, 1, 1, 1] : Fin 4 → Fv) i ≠ 0 := by
    intro i; fin_cases i
    exacts [h8ne, one_ne_zero, one_ne_zero, one_ne_zero]
  have hG1 := shapeD_locGram_rescale γ _ hlam hG rfl
  have hD := shapeD_halfData h2 (γ * diagGL ![8, 1, 1, 1] hlam) hG1 ha hα hβ hδ hd
  have hG2 := shapeD_locGram_gamH_shape (γ * diagGL ![8, 1, 1, 1] hlam) hG1
  refine RelChain.rescale ![8, 1, 1, 1] hlam ?_ ?_ ?_
  · intro i hi
    fin_cases i <;> first | exact absurd (by decide) hi | rfl
  · intro t ht m hm
    have : t = 0 := by simpa using ht
    subst this
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeDG]; shapeD_ent; done)
  · exact RelChain.half hD (shapeD_relChain_base h2 _ hG2 ha hα hβ hδ hd)

/-- **Step 5**: `UnitRootsBlock Q v γ` ($T = \{0, 3\}$, $c = \tfrac1{16}$, $i_0 = 1$, $j = 2$). -/
theorem shapeD_unitRootsBlock {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) {a α β δ d : Fv}
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hG : locGram Q v γ = shapeDG a α β δ d)
    (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1) :
    UnitRootsBlock Q v γ := by
  refine ⟨{0, 3}, 1 / 16, 1, 2, ?_, by norm_num, ?_, ?_, by decide, by decide, ?_⟩
  · intro t ht m hm
    rw [hG]
    fin_cases t <;> fin_cases m <;>
      first
        | exact absurd ht (by decide)
        | exact absurd rfl hm
        | (simp only [shapeDG]; shapeD_ent; done)
  · intro i j hi hj
    rw [hG]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd (by decide) hi
        | exact absurd (by decide) hj
        | (simp only [shapeDG]; shapeD_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeDG]; shapeD_ent
           rw [show (1 / 16 : Fv) * (16 * (2 * α)) = 2 * α by ring]
           exact shapeD_v_two_mul_le h2 hα)
        | (simp only [shapeDG]; shapeD_ent
           rw [show (1 / 16 : Fv) * (16 * (2 * δ)) = 2 * δ by ring]
           exact shapeD_v_two_mul_le h2 hδ)
        | (simp only [shapeDG]; shapeD_ent
           rw [show (1 / 16 : Fv) * (16 * β) = β by ring]
           exact hβ.le)
  · intro i hi
    rw [hG]
    fin_cases i <;>
      first
        | exact absurd (by decide) hi
        | (simp only [shapeDG]; shapeD_ent
           rw [show (1 / 16 : Fv) * (16 * (2 * α)) / 2 = α by ring]
           exact hα)
        | (simp only [shapeDG]; shapeD_ent
           rw [show (1 / 16 : Fv) * (16 * (2 * δ)) / 2 = δ by ring]
           exact hδ)
  · rw [hG]
    simp only [shapeDG]; shapeD_ent
    rw [show (1 / 16 : Fv) * (16 * β) = β by ring, hβ]

end Aux

section Main

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **Shape D chain**: if $G = $ `shapeDG a α β δ d` with $\lvert a\rvert = \lvert\beta\rvert = \lvert d\rvert = 1$ and
$\lvert\alpha\rvert, \lvert\delta\rvert \le 1$, then `PeelChainPair Q v γ ∅ [(0, none)]`: peel $b_0$, then
(rescale, halve, block base case) `RelChain Q v {0} γ`, $b_3$ orthogonal to the rest, and `UnitRootsBlock`. -/
theorem peelChainPair_shapeD (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a α β δ d : Fv} (hG : locGram Q v γ = shapeDG a α β δ d) (ha : Valued.v a = 1)
    (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1) (hd : Valued.v d = 1) :
    PeelChainPair Q v γ ∅ [(0, none)] := by
  have v4a := shapeA_v_four_mul h2 ha
  have hα' := shapeD_v_32_le h2 hα
  have hδ' := shapeD_v_32_le h2 hδ
  have hβ' := shapeD_v_sixteen_mul h2 hβ
  have hd' := shapeD_v_128_mul h2 hd
  have hins : (insert (0 : Fin 4) ∅ : Finset (Fin 4)) = {0} := by decide
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro m hm
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeDG]; shapeD_ent; done)
  · intro i i' hi hi'
    rw [hG]
    have g00 : shapeDG a α β δ d 0 0 = 2 * a := rfl
    rw [g00, show (2 * (2 * a) : Fv) = 4 * a by ring, v4a]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd (by decide) hi
        | exact absurd (by decide) hi'
        | (simp only [shapeDG]; shapeD_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeDG]; shapeD_ent; exact hα'.trans (by rw [exp_le_exp]; norm_num))
        | (simp only [shapeDG]; shapeD_ent; exact hδ'.trans (by rw [exp_le_exp]; norm_num))
        | (simp only [shapeDG]; shapeD_ent; rw [hβ', exp_le_exp]; norm_num)
        | (simp only [shapeDG]; shapeD_ent; rw [hd', exp_le_exp]; norm_num)
  · rw [hins]
    refine Or.inr (Or.inr (Or.inr ⟨shapeD_relChain h2 γ hG ha hα hβ hδ hd, ⟨3, by decide, fun m hm => ?_⟩,
      Or.inr (shapeD_unitRootsBlock γ h2 hG hα hβ hδ)⟩))
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeDG]; shapeD_ent; done)

/-- **Theorem 18, "only if", at $p = 2$ for $\langle a\rangle \perp 8K \perp 64\langle d\rangle$** (Conway–Sloane §9.5,
p. 391; unconditional): if $L_2$ has a basis $\gamma$ with Gram matrix `shapeDG a α β δ d`
($\lvert a\rvert = \lvert\beta\rvert = \lvert d\rvert = 1$, $\lvert\alpha\rvert, \lvert\delta\rvert \le 1$), then every
element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root
vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': ⟨a⟩ ⊥ 8K ⊥ 64⟨d⟩)"]
theorem theorem18OnlyIf_of_shapeD {L : Lat ℚ 4} {Q : QuadForm ℚ 4} (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    {a α β δ d : Fv} (hG : locGram Q v γ = shapeDG a α β δ d) (ha : Valued.v a = 1)
    (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1) (hd : Valued.v d = 1) :
    Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_peelChainPair hQ h2 γ hγ _ (peelChainPair_shapeD h2 γ hG ha hα hβ hδ hd)

/-- **The shape $\langle a\rangle \perp 8K \perp 64\langle d\rangle$ is covered**, tenth version (a peeling chain
with a relative chain of canonical overlattices and `UnitRootsBlock`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: ⟨a⟩ ⊥ 8K ⊥ 64⟨d⟩ is a covered shape, tenth version)"]
theorem covered10_of_shapeD (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {L : Lat ℚ 4} {Q : QuadForm ℚ 4}
    (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a α β δ d : Fv}
    (hG : locGram Q v γ = shapeDG a α β δ d) (ha : Valued.v a = 1)
    (hα : Valued.v α ≤ 1) (hβ : Valued.v β = 1) (hδ : Valued.v δ ≤ 1) (hd : Valued.v d = 1) :
    Theorem18DyadicCovered10 Q L v :=
  Or.inr (Or.inl ⟨γ, _, hγ, peelChainPair_shapeD h2 γ hG ha hα hβ hδ hd⟩)

end Main

end QuadFormsKB.ConwaySloane
