/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for the shape $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** Over $\mathbb Q$ at the prime $v$ over $2$; a basis $\gamma$ of $L_2$ with Gram matrix $G$ =
`locGram Q v γ` of the bilinear form $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**The shape.** In Conway–Sloane's notation (form matrix $M$, $Q(x) = x^{\mathsf T}Mx$, $G = 2M$) the $2$-adic lattice
$\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$ with $a, b, c, d$ $2$-adic units and
$b + c \equiv 0 \pmod 4$ has, in a Jordan basis $b_0, \dots, b_3$ (Conway–Sloane's $a_1, \dots, a_4$ shifted to
$0$-based indices), the Gram matrix
$$G = \operatorname{diag}(2a,\ 8b,\ 8c,\ 32d) \quad (\texttt{shapeAG}),\qquad \lvert b + c\rvert \le \lvert 4\rvert.$$

**The chain** (all steps from `Section9Theorem18DyadicRelChain.lean`; $e_k$ the standard basis):
1. *Peel* $b_0$ (`PeelChainRel`, cons case): $b_0 \perp b_1, b_2, b_3$ and the entries $8b, 8c, 32d, 0$ of the
   complement have absolute value $\le \lvert 2G_{00}\rvert = \lvert 4\rvert$. Fixed set $T = \{0\}$.
2. *Rescale* the fixed vector: $b_0 \mapsto 4b_0$ (`RelChain.rescale`, $\Lambda = \operatorname{diag}(4, 1, 1, 1)$);
   the Gram matrix becomes $\operatorname{diag}(32a, 8b, 8c, 32d)$.
3. *Pair-glue and halve* (`RelChain.pairHalf`, `PairHalf.Data` with $c = \tfrac14$, $C = \{0, 3\}$, $l_1 = 1$,
   $l_2 = 2$): the new basis is $\tfrac12 b_0,\ \tfrac12(b_1 + b_2),\ b_2,\ \tfrac12 b_3$, with Gram matrix
   $$\begin{pmatrix}8a&0&0&0\\0&2(b+c)&4c&0\\0&4c&8c&0\\0&0&0&8d\end{pmatrix}.$$
4. *Block base case* (`RelChain.blockGlue`, $c = \tfrac14$, $l = 3$): on the complement $\{1, 2, 3\}$ of $T$ the block
   of $\tfrac14 G$ is $\begin{pmatrix}(b+c)/2&c&0\\c&2c&0\\0&0&2d\end{pmatrix}$, integral and even, of the form
   $E \perp \langle 2d\rangle$ with $\lvert\det\rvert = \lvert 2bcd\rvert = \lvert 2\rvert$.
5. *Unit classes*: `UnitRoots` with $c = \tfrac14$, $l_1 = 1$, $l_2 = 2$ ($\tfrac14G_{11}/2 = b$, $\tfrac14G_{22}/2 = c$
   units, $\lvert b + c\rvert \le \lvert 4\rvert$).

**Defines** `shapeAG a b c d` (the Gram matrix above).

**Proves**
* `peelChainRel_shapeA`, `unitRoots_shapeA`;
* `theorem18OnlyIf_of_shapeA` (**Theorem 18, "only if", at $p = 2$ for this shape**, unconditional);
* `covered9_of_shapeA` (the shape is covered by `Theorem18DyadicCovered9`);
* auxiliary lemmas: Gram matrices of the intermediate bases (`locGram_diagGL`, `locGram_gamP_shape`),
  `pairHalfData_shapeA`, `relChain_gamP_shapeA`, and `det_eq_compBlock_single` (the determinant of a matrix whose
  row and column $t$ vanish off the diagonal is $A_{tt}$ times the determinant of the block on the complement of
  $\{t\}$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual9

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The Gram matrix $G = \operatorname{diag}(2a,\ 8b,\ 8c,\ 32d)$ of the bilinear form $B$ in a Jordan basis of the
$2$-adic lattice $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$ (Conway–Sloane's notation,
$Q(x) = x^{\mathsf T}Mx$, $G = 2M$; see the module docstring). -/
def shapeAG {K : Type*} [Field K] (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![2 * a, 0, 0, 0; 0, 8 * b, 0, 0; 0, 0, 8 * c, 0; 0, 0, 0, 32 * d]

/-- Evaluate the entries of an explicit `!![...]` matrix at numerals. -/
local macro "shapeA_ent" : tactic =>
  `(tactic| simp only [Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk])

section Aux

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- $\lvert 2^ku\rvert = \lvert 2\rvert^k = e^{-k}$ for a unit $u$ (at the prime over $2$). -/
theorem shapeA_valued_two_pow_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : ℕ) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v ((2 : Fv) ^ k * u) = exp (-(k : ℤ)) := by
  rw [map_mul, map_pow, valued_two_dyadic v h2, hu, mul_one, ← WithZero.exp_nsmul]; simp

/-- $\lvert 2u\rvert = e^{-1}$ for a unit $u$. -/
theorem shapeA_v_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (2 * u) = exp (-1 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 1 hu
  rwa [pow_one, Nat.cast_one] at this

/-- $\lvert 4u\rvert = e^{-2}$ for a unit $u$. -/
theorem shapeA_v_four_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (4 * u) = exp (-2 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 2 hu
  rw [show (2 : Fv) ^ 2 = 4 by norm_num] at this
  simpa using this

/-- $\lvert 8u\rvert = e^{-3}$ for a unit $u$. -/
theorem shapeA_v_eight_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (8 * u) = exp (-3 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 3 hu
  rw [show (2 : Fv) ^ 3 = 8 by norm_num] at this
  simpa using this

/-- $\lvert 32u\rvert = e^{-5}$ for a unit $u$. -/
theorem shapeA_v_thirtytwo_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (32 * u) = exp (-5 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 5 hu
  rw [show (2 : Fv) ^ 5 = 32 by norm_num] at this
  simpa using this

/-- An element of absolute value $1$ is nonzero. -/
theorem shapeA_ne_zero_of_v_one {u : Fv} (hu : Valued.v u = 1) : u ≠ 0 := by
  intro h; rw [h, map_zero] at hu; exact zero_ne_one hu

/-- $\lvert 4\rvert = e^{-2}$. -/
theorem shapeA_v_four (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (4 : Fv) = exp (-2 : ℤ) := by
  simpa using shapeA_v_four_mul h2 (u := (1 : Fv)) (map_one _)

/-- **Step 2 (rescaling)**: if $G = \operatorname{diag}(2a, 8b, 8c, 32d)$ then the basis $\gamma\Lambda$,
$\Lambda = \operatorname{diag}(4, 1, 1, 1)$, has Gram matrix $\operatorname{diag}(32a, 8b, 8c, 32d)$. -/
theorem locGram_diagGL {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) (lam : Fin 4 → Fv) (hlam : ∀ i, lam i ≠ 0)
    {a b c d : Fv} (hG : locGram Q v γ = shapeAG a b c d) (hlam' : lam = ![4, 1, 1, 1]) :
    locGram Q v (γ * diagGL lam hlam) = !![32 * a, 0, 0, 0; 0, 8 * b, 0, 0; 0, 0, 8 * c, 0; 0, 0, 0, 32 * d] := by
  rw [locGram_mul, hG, diagGL_val, diagonal_transpose]
  refine Matrix.ext fun i j => ?_
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [shapeAG, hlam'] <;> ring

/-- The Gram matrix of the basis `PairHalf.gamP γ C hl` is $P^{\mathsf T}GP$ with $P = W_C W_{l_1l_2}$. -/
theorem locGram_gamP {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) (C : Finset (Fin 4)) {l₁ l₂ : Fin 4} (hl : l₁ ≠ l₂) :
    locGram Q v (PairHalf.gamP γ C hl) =
      (HalfStep.W C * PairGlue.W l₁ l₂)ᵀ * locGram Q v γ * (HalfStep.W C * PairGlue.W l₁ l₂) := by
  unfold locGram
  rw [PairHalf.gamP, PairGlue.gam_val, HalfStep.gamH_val]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The matrix $W_{\{0, 3\}}W_{12}$ of the step-3 basis change (columns $\tfrac12e_0,\ \tfrac12(e_1 + e_2),\ e_2,\
\tfrac12e_3$). -/
theorem shapeA_WP_eq : (HalfStep.W (v := v) ({0, 3} : Finset (Fin 4)) * PairGlue.W (1 : Fin 4) 2) =
    !![(1 / 2 : Fv), 0, 0, 0; 0, 1 / 2, 0, 0; 0, 1 / 2, 1, 0; 0, 0, 0, 1 / 2] := by
  refine Matrix.ext fun i j => ?_
  rw [HalfStep.W, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [PairGlue.W, PairGlue.wvec]

/-- **Step 3 (Gram matrix)**: from $\operatorname{diag}(32a, 8b, 8c, 32d)$ to the Gram matrix
$\begin{pmatrix}8a&0&0&0\\0&2(b+c)&4c&0\\0&4c&8c&0\\0&0&0&8d\end{pmatrix}$ of the pair-glue-and-halved basis. -/
theorem locGram_gamP_shape {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) (hl : (1 : Fin 4) ≠ 2) {a b c d : Fv}
    (hG : locGram Q v γ = !![32 * a, 0, 0, 0; 0, 8 * b, 0, 0; 0, 0, 8 * c, 0; 0, 0, 0, 32 * d]) :
    locGram Q v (PairHalf.gamP γ {0, 3} hl) =
      !![8 * a, 0, 0, 0; 0, 2 * (b + c), 4 * c, 0; 0, 4 * c, 8 * c, 0; 0, 0, 0, 8 * d] := by
  rw [locGram_gamP, hG, shapeA_WP_eq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **Step 3 (hypotheses)**: `PairHalf.Data` with $c = \tfrac14$, $C = \{0, 3\}$, $l_1 = 1$, $l_2 = 2$ for the Gram
matrix $\operatorname{diag}(32a, 8b, 8c, 32d)$ with $a, b, c, d$ units and $\lvert b + c\rvert \le \lvert 4\rvert$. -/
theorem pairHalfData_shapeA (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) {a b c d : Fv}
    (hG : locGram Q v γ = !![32 * a, 0, 0, 0; 0, 8 * b, 0, 0; 0, 0, 8 * c, 0; 0, 0, 0, 32 * d])
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) (hc : Valued.v c = 1) (hd : Valued.v d = 1)
    (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) :
    PairHalf.Data Q v γ (1 / 4) {0, 3} 1 2 := by
  have hA : ∀ i j, (1 / 4 : Fv) * locGram Q v γ i j =
      !![8 * a, 0, 0, 0; 0, 2 * b, 0, 0; 0, 0, 2 * c, 0; 0, 0, 0, 8 * d] i j := by
    intro i j
    rw [hG]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have h4 := shapeA_v_four h2
  have v8a := shapeA_v_eight_mul h2 ha
  have v8d := shapeA_v_eight_mul h2 hd
  have v2b := shapeA_v_two_mul h2 hb
  have v2c := shapeA_v_two_mul h2 hc
  have v4a := shapeA_v_four_mul h2 ha
  have v4d := shapeA_v_four_mul h2 hd
  have e1 : (1 : WithZero (Multiplicative ℤ)) = exp 0 := exp_zero.symm
  have hle : ∀ k : ℤ, k ≤ 0 → exp k ≤ (1 : WithZero (Multiplicative ℤ)) := fun k hk => by
    rw [e1, exp_le_exp]; exact hk
  have g11 : locGram Q v γ 1 1 = 8 * b := by rw [hG]; rfl
  have g22 : locGram Q v γ 2 2 = 8 * c := by rw [hG]; rfl
  refine ⟨by norm_num, by decide, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hA]
    fin_cases i <;> fin_cases j <;> shapeA_ent <;>
      first
        | (rw [map_zero]; exact zero_le)
        | (rw [v8a]; exact hle _ (by norm_num))
        | (rw [v2b]; exact hle _ (by norm_num))
        | (rw [v2c]; exact hle _ (by norm_num))
        | (rw [v8d]; exact hle _ (by norm_num))
  · intro i
    rw [hA]
    fin_cases i <;> shapeA_ent
    · rw [show (8 * a / 2 : Fv) = 4 * a by ring, v4a]; exact hle _ (by norm_num)
    · rw [show (2 * b / 2 : Fv) = b by ring, hb]
    · rw [show (2 * c / 2 : Fv) = c by ring, hc]
    · rw [show (8 * d / 2 : Fv) = 4 * d by ring, v4d]; exact hle _ (by norm_num)
  · intro i hi j hj
    rw [hG]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hi (by decide)
        | exact absurd (by decide) hj
        | (shapeA_ent; done)
  · intro i hi j hj
    rw [hA]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hj (by decide)
        | (shapeA_ent; rw [map_zero]; exact zero_le)
        | (shapeA_ent; rw [v8a, h4, exp_le_exp]; norm_num)
        | (shapeA_ent; rw [v8d, h4, exp_le_exp]; norm_num)
  · intro i hi
    rw [hA]
    fin_cases i <;>
      first
        | exact absurd hi (by decide)
        | (shapeA_ent; rw [show (8 * a / 2 : Fv) = 4 * a by ring, v4a, h4])
        | (shapeA_ent; rw [show (8 * d / 2 : Fv) = 4 * d by ring, v4d, h4])
  · intro i hi
    rw [hG]
    fin_cases i <;>
      first
        | exact absurd rfl hi
        | (shapeA_ent; done)
  · intro i hi
    rw [hG]
    fin_cases i <;>
      first
        | exact absurd rfl hi
        | (shapeA_ent; done)
  · rw [hA]; shapeA_ent; rw [show (2 * b / 2 : Fv) = b by ring, hb]
  · rw [hA]; shapeA_ent; rw [show (2 * c / 2 : Fv) = c by ring, hc]
  · rw [g11, g22, show (1 / 4 : Fv) * (8 * b + 8 * c) / 2 = b + c by ring]; exact hbc
  · have : HalfStep.hatA ((1 / 4 : Fv) • locGram Q v γ) {0, 3} {1, 2} = 1 := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [HalfStep.hatA]
    rw [this, det_one, map_one]

/-- The determinant of a matrix whose row and column $t$ vanish off the diagonal is $A_{tt}$ times the determinant
of its block on the complement of $\{t\}$ (`compBlock`). -/
theorem det_eq_compBlock_single {n : ℕ} {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K) (t : Fin n)
    (h1 : ∀ j, j ≠ t → A t j = 0) (h2 : ∀ j, j ≠ t → A j t = 0) :
    A.det = A t t * (compBlock {t} A).det := by
  classical
  let eq1 : {i // i ∈ ({t} : Finset (Fin n))} ⊕ {i // ¬ i ∈ ({t} : Finset (Fin n))} ≃ Fin n :=
    Equiv.sumCompl (· ∈ ({t} : Finset (Fin n)))
  have hblk : A.submatrix eq1 eq1 =
      fromBlocks (A.submatrix (Subtype.val : {i // i ∈ ({t} : Finset (Fin n))} → Fin n) Subtype.val) 0 0
        (A.submatrix (Subtype.val : {i // ¬ i ∈ ({t} : Finset (Fin n))} → Fin n) Subtype.val) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · have hx : x.1 = t := Finset.mem_singleton.mp x.2
      have hy : y.1 ≠ t := by simpa using y.2
      show A x.1 y.1 = 0
      rw [hx]; exact h1 _ hy
    · have hy : y.1 = t := Finset.mem_singleton.mp y.2
      have hx : x.1 ≠ t := by simpa using x.2
      show A x.1 y.1 = 0
      rw [hy]; exact h2 _ hx
    · rfl
  have : Unique {i // i ∈ ({t} : Finset (Fin n))} :=
    ⟨⟨⟨t, Finset.mem_singleton_self t⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
  have h1' : A.det = (A.submatrix eq1 eq1).det := (Matrix.det_submatrix_equiv_self eq1 A).symm
  rw [h1', hblk, Matrix.det_fromBlocks_zero₂₁, det_unique]
  congr 1
  · have hd : ((default : {i // i ∈ ({t} : Finset (Fin n))}) : Fin n) = t :=
      Finset.mem_singleton.mp (default : {i // i ∈ ({t} : Finset (Fin n))}).2
    simp only [submatrix_apply, hd]
  · have := Matrix.det_submatrix_equiv_self (compEquiv ({t} : Finset (Fin n)))
      (A.submatrix (Subtype.val : {i // ¬ i ∈ ({t} : Finset (Fin n))} → Fin n) Subtype.val)
    rw [← this]
    rfl

/-- **Step 4 (block base case)**: for the Gram matrix $\begin{pmatrix}8a&0&0&0\\0&2(b+c)&4c&0\\0&4c&8c&0\\
0&0&0&8d\end{pmatrix}$ ($a, b, c, d$ units, $\lvert b + c\rvert \le \lvert 4\rvert$), `RelChain Q v {0} γ` holds by
`RelChain.blockGlue` ($c = \tfrac14$, $l = 3$): the block on $\{1, 2, 3\}$ is $E \perp \langle 2d\rangle$ with
$\det = 2bcd$. -/
theorem relChain_gamP_shapeA (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv) {a b c d : Fv}
    (hG : locGram Q v γ = !![8 * a, 0, 0, 0; 0, 2 * (b + c), 4 * c, 0; 0, 4 * c, 8 * c, 0; 0, 0, 0, 8 * d])
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) (hc : Valued.v c = 1) (hd : Valued.v d = 1)
    (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) : RelChain Q v {0} γ := by
  have hA : ∀ i j, (1 / 4 : Fv) * locGram Q v γ i j =
      !![2 * a, 0, 0, 0; 0, (b + c) / 2, c, 0; 0, c, 2 * c, 0; 0, 0, 0, 2 * d] i j := by
    intro i j
    rw [hG]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have h4 := shapeA_v_four h2
  have hv2 := valued_two_dyadic v h2
  have v2c := shapeA_v_two_mul h2 hc
  have v2d := shapeA_v_two_mul h2 hd
  have e1 : (1 : WithZero (Multiplicative ℤ)) = exp 0 := exp_zero.symm
  have hle : ∀ k : ℤ, k ≤ 0 → exp k ≤ (1 : WithZero (Multiplicative ℤ)) := fun k hk => by
    rw [e1, exp_le_exp]; exact hk
  have hbc2 : Valued.v ((b + c) / 2) ≤ 1 := by
    rw [map_div₀, hv2, div_le_one₀ (by rw [← hv2]; exact (Valuation.pos_iff _).mpr (by norm_num))]
    exact hbc.trans (by rw [h4, exp_le_exp]; norm_num)
  have hbc4 : Valued.v ((b + c) / 2 / 2) ≤ 1 := by
    rw [div_div, map_div₀, show (2 * 2 : Fv) = 4 by norm_num,
      div_le_one₀ (by rw [h4]; exact exp_pos)]
    exact hbc
  have hdet : (compBlock {0} ((1 / 4 : Fv) • locGram Q v γ)).det = 2 * b * c * d := by
    have hM : (1 / 4 : Fv) • locGram Q v γ =
        !![2 * a, 0, 0, 0; 0, (b + c) / 2, c, 0; 0, c, 2 * c, 0; 0, 0, 0, 2 * d] := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.smul_apply, smul_eq_mul, hA]
    have h := det_eq_compBlock_single ((1 / 4 : Fv) • locGram Q v γ) 0
      (fun j hj => by
        rw [hM]; fin_cases j <;> first | exact absurd rfl hj | (shapeA_ent; done))
      (fun j hj => by
        rw [hM]; fin_cases j <;> first | exact absurd rfl hj | (shapeA_ent; done))
    have hd4 : ((1 / 4 : Fv) • locGram Q v γ).det = 4 * a * b * c * d := by
      rw [hM]
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      ring
    have h00 : ((1 / 4 : Fv) • locGram Q v γ) 0 0 = 2 * a := by rw [hM]; rfl
    rw [hd4, h00] at h
    have ha0 : (2 * a : Fv) ≠ 0 := mul_ne_zero (by norm_num) (shapeA_ne_zero_of_v_one ha)
    refine mul_left_cancel₀ ha0 ?_
    linear_combination (-1 : Fv) * h
  refine RelChain.blockGlue (c := 1 / 4) 3 ?_ (by norm_num) (by decide) ?_ ?_ ?_ ?_ ?_
  · intro t ht m hm
    have : t = 0 := by simpa using ht
    subst this
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (shapeA_ent; done)
  · intro i j hi hj
    rw [hA]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd (by decide) hi
        | exact absurd (by decide) hj
        | (shapeA_ent; rw [map_zero]; exact zero_le)
        | (shapeA_ent; exact hbc2)
        | (shapeA_ent; rw [hc])
        | (shapeA_ent; rw [v2c]; exact hle _ (by norm_num))
        | (shapeA_ent; rw [v2d]; exact hle _ (by norm_num))
  · intro i hi
    rw [hA]
    fin_cases i <;>
      first
        | exact absurd (by decide) hi
        | (shapeA_ent; exact hbc4)
        | (shapeA_ent; rw [show (2 * c / 2 : Fv) = c by ring, hc])
        | (shapeA_ent; rw [show (2 * d / 2 : Fv) = d by ring, hd])
  · intro i hi hi3
    rw [hG]
    fin_cases i <;> first | exact absurd rfl hi3 | exact absurd (by decide) hi | (shapeA_ent; done)
  · rw [hA]; shapeA_ent; rw [show (2 * d / 2 : Fv) = d by ring, hd]
  · rw [hdet, map_mul, map_mul, map_mul, hb, hc, hd]
    simp

/-- **Steps 1–4**: a basis $\gamma$ of $L_2$ with Gram matrix $\operatorname{diag}(2a, 8b, 8c, 32d)$
($a, b, c, d$ units, $\lvert b + c\rvert \le \lvert 4\rvert$) has a peeling chain `PeelChainRel Q v γ ∅ [0]`: peel
$b_0$, rescale it by $4$, glue $\tfrac12(b_1 + b_2)$ and halve $b_0, b_3$ (`RelChain.pairHalf`), then the block on
$\{1, 2, 3\}$ is $E \perp \langle 2d\rangle$. -/
theorem peelChainRel_shapeA (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a b c d : Fv} (hG : locGram Q v γ = shapeAG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) :
    PeelChainRel Q v γ ∅ [0] := by
  have v4a := shapeA_v_four_mul h2 ha
  have v8b := shapeA_v_eight_mul h2 hb
  have v8c := shapeA_v_eight_mul h2 hc
  have v32d := shapeA_v_thirtytwo_mul h2 hd
  have hins : (insert (0 : Fin 4) ∅ : Finset (Fin 4)) = {0} := by decide
  have h4ne : (4 : Fv) ≠ 0 := by norm_num
  have hlam : ∀ i, (![4, 1, 1, 1] : Fin 4 → Fv) i ≠ 0 := by
    intro i; fin_cases i
    exacts [h4ne, one_ne_zero, one_ne_zero, one_ne_zero]
  have hG1 := locGram_diagGL γ _ hlam hG rfl
  have hD := pairHalfData_shapeA h2 (γ * diagGL ![4, 1, 1, 1] hlam) hG1 ha hb hc hd hbc
  have hG2 := locGram_gamP_shape (γ * diagGL ![4, 1, 1, 1] hlam) hD.hl hG1
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro m hm
    rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeAG]; shapeA_ent; done)
  · intro i i' hi hi'
    rw [hG]
    have g00 : shapeAG a b c d 0 0 = 2 * a := rfl
    rw [g00, show (2 * (2 * a) : Fv) = 4 * a by ring, v4a]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd (by decide) hi
        | exact absurd (by decide) hi'
        | (simp only [shapeAG]; shapeA_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeAG]; shapeA_ent; rw [v8b, exp_le_exp]; norm_num)
        | (simp only [shapeAG]; shapeA_ent; rw [v8c, exp_le_exp]; norm_num)
        | (simp only [shapeAG]; shapeA_ent; rw [v32d, exp_le_exp]; norm_num)
  · rw [hins]
    refine ⟨?_, 3, by decide, fun m hm => ?_⟩
    · refine RelChain.rescale ![4, 1, 1, 1] hlam ?_ ?_ ?_
      · intro i hi
        fin_cases i <;> first | exact absurd (by decide) hi | rfl
      · intro t ht m hm
        have : t = 0 := by simpa using ht
        subst this
        rw [hG]
        fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeAG]; shapeA_ent; done)
      · exact RelChain.pairHalf hD (by decide)
          (relChain_gamP_shapeA h2 _ hG2 ha hb hc hd hbc)
    · rw [hG]
      fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeAG]; shapeA_ent; done)

/-- **Step 5**: `UnitRoots Q v γ` for the same Gram matrix (second alternative: scalar $\tfrac14$, $l_1 = 1$,
$l_2 = 2$). -/
theorem unitRoots_shapeA (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a b c d : Fv} (hG : locGram Q v γ = shapeAG a b c d) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) : UnitRoots Q v γ := by
  have g11 : locGram Q v γ 1 1 = 8 * b := by rw [hG]; rfl
  have g22 : locGram Q v γ 2 2 = 8 * c := by rw [hG]; rfl
  refine Or.inr ⟨1 / 4, 1, 2, by decide, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hG]
    fin_cases i <;> first | exact absurd rfl hi | (simp only [shapeAG]; shapeA_ent; done)
  · intro i hi
    rw [hG]
    fin_cases i <;> first | exact absurd rfl hi | (simp only [shapeAG]; shapeA_ent; done)
  · rw [g11, show (1 / 4 : Fv) * (8 * b) / 2 = b by ring, hb]
  · rw [g22, show (1 / 4 : Fv) * (8 * c) / 2 = c by ring, hc]
  · rw [g11, g22, show (1 / 4 : Fv) * (8 * b + 8 * c) / 2 = b + c by ring]; exact hbc

end Aux

section Main

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **Theorem 18, "only if", at $p = 2$ for $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$**
(Conway–Sloane §9.5, p. 391; unconditional): if $L_2$ has a basis $\gamma$ with Gram matrix
$\operatorname{diag}(2a, 8b, 8c, 32d)$, $a, b, c, d$ units and $b + c \equiv 0 \pmod 4$, then every element of
$\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': ⟨a⟩ ⊥ 4⟨b, c⟩ ⊥ 16⟨d⟩, b + c ≡ 0 mod 4)"]
theorem theorem18OnlyIf_of_shapeA {L : Lat ℚ 4} {Q : QuadForm ℚ 4} (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d : Fv}
    (hG : locGram Q v γ = shapeAG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) :
    Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_peelChainRel hQ h2 γ hγ [0] (peelChainRel_shapeA h2 γ hG ha hb hc hd hbc)
    (units_of_unitRoots h2 γ hγ (unitRoots_shapeA h2 γ hG hb hc hbc))

/-- **The shape $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$ is covered**, ninth version
(a peeling chain followed by a relative chain, and `UnitRoots`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: ⟨a⟩ ⊥ 4⟨b, c⟩ ⊥ 16⟨d⟩ is a covered shape, ninth version)"]
theorem covered9_of_shapeA (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {L : Lat ℚ 4} {Q : QuadForm ℚ 4}
    (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d : Fv}
    (hG : locGram Q v γ = shapeAG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (hbc : Valued.v (b + c) ≤ Valued.v (4 : Fv)) :
    Theorem18DyadicCovered9 Q L v :=
  Or.inr (Or.inl ⟨γ, [0], hγ, peelChainRel_shapeA h2 γ hG ha hb hc hd hbc,
    unitRoots_shapeA h2 γ hG hb hc hbc⟩)

end Main

end QuadFormsKB.ConwaySloane
