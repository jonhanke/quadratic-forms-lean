/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the family $K \perp 2\langle a\rangle \perp 8\langle b\rangle$ and the eighth residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Layer.** Over $\mathbb Q$ at the prime $v$ over $2$; a basis $\gamma$ of $L_2$ with Gram matrix $G$ =
`locGram Q v γ` $= \gamma^{\mathsf T}H\gamma$ of the bilinear form $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**The family.** An earlier computer check (outside Lean) left exactly one family of
$2$-adic Jordan forms of rank $\le 4$ with scales $1, 2, 4, 8$ outside `Theorem18DyadicCovered7`: in Conway–Sloane's
notation (form matrix $M$, $Q(x) = x^{\mathsf T}Mx$) $K \perp 2\langle a\rangle \perp 8\langle b\rangle$ with $K$ an
even unimodular binary block and $a \equiv b \pmod 4$. In terms of $G = 2M$ with
$K = \begin{pmatrix}2\alpha&\beta\\\beta&2\delta\end{pmatrix}$:
$$G = \begin{pmatrix}4\alpha&2\beta&0&0\\2\beta&4\delta&0&0\\0&0&4a&0\\0&0&0&16b\end{pmatrix},\qquad
\lvert\alpha\rvert, \lvert\delta\rvert \le 1,\ \lvert\beta\rvert = \lvert a\rvert = \lvert b\rvert = 1.$$
Its dual lattice has Gram matrix $N = G^{-1}$, and (scaled by $16$) is
$\langle b^{-1}\rangle \perp 4\langle a^{-1}\rangle \perp 8K^{-1}$ in Conway–Sloane's notation: a peeling chain
(peel $b_3$, then $b_2$, remainder of rank $2$). The congruence $a \equiv b \pmod 4$ is not needed.

**Defines**
* `famN α β δ a b` (the inverse Gram matrix $N$ of the family);
* `Theorem18DyadicCovered8 Q L v` (a **condition**): `Theorem18DyadicCovered7 Q L v`, or some lattice $L'$ with
  $L'_2 = L_2^\#$ and $L_2 = L_2'^\#$ satisfies `Theorem18DyadicCovered7 Q L' v`;
* `Theorem18DyadicResidual8` (a **named statement**): the "only if" direction at the prime over $2$ for every lattice
  not covered by `Theorem18DyadicCovered8`.

**What `Theorem18DyadicResidual8` still contains.** A computer check (outside Lean; all
Jordan forms of rank $3$–$5$ with scales $1, \dots, 16$; no counterexample to Theorem 18) leaves 138 forms in three
shapes outside `Theorem18DyadicCovered8`: $\langle a, b\rangle \perp 16\langle c, d\rangle$,
$\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$ and
$\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$. In
higher rank and at larger scales further shapes are expected; a complete proof needs the Earnest–Hsia computation of
$\theta(O^+(L_2))$ for every Jordan configuration.

**Proves**
* `theorem18OnlyIf_of_family` (**Theorem 18, "only if", for $K \perp 2\langle a\rangle \perp 8\langle b\rangle$**,
  unconditional) and `covered8_of_family`;
* `theorem18OnlyIf_of_covered8`, `theorem18DyadicResidual7_of_residual8`, `theorem18Dyadic_of_residual8`,
  `theorem18Statement_of_residual8`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicDual

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Family

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- The Gram matrix $G$ of the family $K \perp 2\langle a\rangle \perp 8\langle b\rangle$ (see the module docstring). -/
def famG {K : Type*} [Field K] (α β δ a b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![4 * α, 2 * β, 0, 0; 2 * β, 4 * δ, 0, 0; 0, 0, 4 * a, 0; 0, 0, 0, 16 * b]

/-- The inverse $N = G^{-1}$ of `famG`, with $d = 4\alpha\delta - \beta^2$. -/
def famN {K : Type*} [Field K] (α β δ a b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![δ / (4 * α * δ - β ^ 2), -β / (2 * (4 * α * δ - β ^ 2)), 0, 0;
     -β / (2 * (4 * α * δ - β ^ 2)), α / (4 * α * δ - β ^ 2), 0, 0;
     0, 0, 1 / (4 * a), 0; 0, 0, 0, 1 / (16 * b)]

theorem famG_mul_famN {K : Type*} [Field K] [CharZero K] {α β δ a b : K} (hd : 4 * α * δ - β ^ 2 ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    famG α β δ a b * famN α β δ a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [famG, famN, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem valued_famD {α β δ : Fv} (hα : Valued.v α ≤ 1) (hδ : Valued.v δ ≤ 1) (hβ : Valued.v β = 1) :
    Valued.v (4 * α * δ - β ^ 2) = 1 := by
  have h4 : Valued.v (4 : Fv) = exp (-2 : ℤ) := by
    rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, valued_two_dyadic v h2, ← exp_add]; norm_num
  have hlt : Valued.v (4 * α * δ) < Valued.v (β ^ 2) := by
    rw [map_pow, hβ, one_pow, map_mul, map_mul, h4]
    calc exp (-2 : ℤ) * Valued.v α * Valued.v δ ≤ exp (-2 : ℤ) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl hα) hδ
      _ < 1 := by rw [mul_one, mul_one, ← exp_zero, exp_lt_exp]; norm_num
  rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_pow, hβ, one_pow]

/-- **The dual of the family is a peeling chain**: `PeelChainTheta (famN α β δ a b) ∅ [3, 2]`. -/
theorem peelChainTheta_famN {α β δ a b : Fv} (hα : Valued.v α ≤ 1) (hδ : Valued.v δ ≤ 1) (hβ : Valued.v β = 1)
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) : PeelChainTheta (famN α β δ a b) ∅ [3, 2] := by
  have hd := valued_famD h2 hα hδ hβ
  have h2v := valued_two_dyadic v h2
  have hd0 : (4 * α * δ - β ^ 2) ≠ 0 := by intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hv00 : Valued.v (δ / (4 * α * δ - β ^ 2)) ≤ 1 := by rw [map_div₀, hd, div_one]; exact hδ
  have hv11 : Valued.v (α / (4 * α * δ - β ^ 2)) ≤ 1 := by rw [map_div₀, hd, div_one]; exact hα
  have hv01 : Valued.v (-β / (2 * (4 * α * δ - β ^ 2))) = exp (1 : ℤ) := by
    rw [map_div₀, Valuation.map_neg, map_mul, hd, hβ, h2v, mul_one, one_div, ← WithZero.exp_neg]; norm_num
  have hv22 : Valued.v ((1 : Fv) / (4 * a)) = exp (2 : ℤ) := by
    rw [map_div₀, map_one, map_mul, ha, mul_one, show (4 : Fv) = 2 * 2 by norm_num, map_mul, h2v, ← exp_add,
      one_div, ← WithZero.exp_neg]; norm_num
  have hv2_22 : Valued.v (2 * ((1 : Fv) / (4 * a))) = exp (1 : ℤ) := by
    rw [map_mul, hv22, h2v, ← exp_add]; norm_num
  have hv2_33 : Valued.v (2 * ((1 : Fv) / (16 * b))) = exp (3 : ℤ) := by
    rw [map_mul, map_div₀, map_one, map_mul, hb, mul_one,
      show (16 : Fv) = 2 * 2 * 2 * 2 by norm_num, map_mul, map_mul, map_mul, h2v, ← exp_add, ← exp_add, ← exp_add,
      one_div, ← WithZero.exp_neg, ← exp_add]; norm_num
  have e01 : (1 : WithZero (Multiplicative ℤ)) ≤ exp (1 : ℤ) := by rw [← exp_zero, exp_le_exp]; norm_num
  have e12 : exp (1 : ℤ) ≤ exp (2 : ℤ) := by rw [exp_le_exp]; norm_num
  have e23 : exp (2 : ℤ) ≤ exp (3 : ℤ) := by rw [exp_le_exp]; norm_num
  have z : Valued.v (0 : Fv) ≤ exp (1 : ℤ) := by rw [map_zero]; exact zero_le
  -- the entries of `famN` off the peeled indices
  have b1 : ∀ i i' : Fin 4, i ≠ 2 → i ≠ 3 → i' ≠ 2 → i' ≠ 3 →
      Valued.v (famN α β δ a b i i') ≤ exp (1 : ℤ) := by
    intro i i' h2' h3 h2'' h3'
    fin_cases i <;> fin_cases i' <;> first
      | exact absurd rfl h2' | exact absurd rfl h3 | exact absurd rfl h2'' | exact absurd rfl h3'
      | exact hv00.trans e01 | exact hv11.trans e01 | exact hv01.le
  have b2 : ∀ i i' : Fin 4, i ≠ 3 → i' ≠ 3 → Valued.v (famN α β δ a b i i') ≤ exp (2 : ℤ) := by
    intro i i' h3 h3'
    by_cases hi : i = 2
    · subst hi
      by_cases hi' : i' = 2
      · subst hi'; exact hv22.le
      · fin_cases i' <;> first | exact absurd rfl hi' | exact absurd rfl h3' | exact z.trans e12
    · by_cases hi' : i' = 2
      · subst hi'; fin_cases i <;> first | exact absurd rfl hi | exact absurd rfl h3 | exact z.trans e12
      · exact (b1 i i' hi h3 hi' h3').trans e12
  refine ⟨by simp, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · intro m hm; fin_cases m <;> first | exact absurd rfl hm | rfl
  · intro i i' hi hi'
    rw [show famN α β δ a b 3 3 = 1 / (16 * b) from rfl, hv2_33]
    simp only [insert_empty_eq] at hi hi'
    exact (b2 i i' (by simpa using hi) (by simpa using hi')).trans e23
  · intro m hm; fin_cases m <;> first | exact absurd rfl hm | rfl
  · intro i i' hi hi'
    rw [show famN α β δ a b 2 2 = 1 / (4 * a) from rfl, hv2_22]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, insert_empty_eq] at hi hi'
    exact b1 i i' hi.1 hi.2 hi'.1 hi'.2
  · left; decide

/-- **Theorem 18, "only if", at $p = 2$ for $K \perp 2\langle a\rangle \perp 8\langle b\rangle$** (Conway–Sloane
§9.5, p. 391; unconditional): if $L_2$ has a basis $\gamma$ with Gram matrix `famG α β δ a b`
($\lvert\alpha\rvert, \lvert\delta\rvert \le 1$, $\lvert\beta\rvert = \lvert a\rvert = \lvert b\rvert = 1$), then every
element of $\theta(O^+(L_2))$ is, up to squares, a product of the norms of an even number of root vectors. Proof:
the dual lattice $L_2^\#$ has Gram matrix `famN` in the dual basis, a peeling chain (`peelChainTheta_famN`), and
Theorem 18's condition passes from $L_2^\#$ to $L_2$ (`theorem18OnlyIf_of_dual_peelChainTheta`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': K ⊥ 2⟨a⟩ ⊥ 8⟨b⟩, through the dual lattice)"]
theorem theorem18OnlyIf_of_family {L : Lat ℚ 4} {Q : QuadForm ℚ 4} (hQ : Q.Nondegenerate)
    (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {α β δ a b : Fv}
    (hG : locGram Q v γ = famG α β δ a b) (hα : Valued.v α ≤ 1) (hδ : Valued.v δ ≤ 1) (hβ : Valued.v β = 1)
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) : Theorem18OnlyIf Q L v hQ := by
  have hd0 : (4 * α * δ - β ^ 2) ≠ 0 := by
    intro h; have := valued_famD h2 hα hδ hβ; rw [h, map_zero] at this; exact zero_ne_one this
  have ha0 : a ≠ 0 := by intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := by intro h; rw [h, map_zero] at hb; exact zero_ne_one hb
  have hN : locGram Q v γ * famN α β δ a b = 1 := by rw [hG]; exact famG_mul_famN hd0 ha0 hb0
  exact theorem18OnlyIf_of_dual_peelChainTheta hQ h2 γ hγ _ hN [3, 2] (peelChainTheta_famN h2 hα hδ hβ ha hb)

end Family

section Covered8

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, eighth version**: `Theorem18DyadicCovered7`, or
some lattice $L'$ whose localization is the dual of $L_2$ (and conversely) satisfies `Theorem18DyadicCovered7`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, eighth version: closed under duality)"]
def Theorem18DyadicCovered8 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered7 Q L v ∨
    ∃ L' : Lat ℚ n, IsDualLoc Q (loc v L.1) (loc v L'.1) ∧ IsDualLoc Q (loc v L'.1) (loc v L.1) ∧
      Theorem18DyadicCovered7 Q L' v

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, eighth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, eighth version)"]
theorem theorem18OnlyIf_of_covered8 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered8 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨L', h₁, h₂, hc⟩
  · exact theorem18OnlyIf_of_covered7 hQ h2 hc
  · exact theorem18OnlyIf_of_dual hQ h₁ h₂ (theorem18OnlyIf_of_covered7 hQ h2 hc)

/-- **The family $K \perp 2\langle a\rangle \perp 8\langle b\rangle$ is covered**, eighth version (through its dual,
a peeling chain). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: K ⊥ 2⟨a⟩ ⊥ 8⟨b⟩ is a covered shape, eighth version)"]
theorem covered8_of_family (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {L : Lat ℚ 4} {Q : QuadForm ℚ 4}
    (γ : GL (Fin 4) (v.adicCompletion ℚ)) (hγ : loc v L.1 = locAct v γ (std v)) {α β δ a b : v.adicCompletion ℚ}
    (hG : locGram Q v γ = famG α β δ a b) (hα : Valued.v α ≤ 1) (hδ : Valued.v δ ≤ 1) (hβ : Valued.v β = 1)
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) : Theorem18DyadicCovered8 Q L v := by
  have hd0 : (4 * α * δ - β ^ 2) ≠ 0 := by
    intro h; have := valued_famD h2 hα hδ hβ; rw [h, map_zero] at this; exact zero_ne_one this
  have ha0 : a ≠ 0 := by intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := by intro h; rw [h, map_zero] at hb; exact zero_ne_one hb
  have hN : locGram Q v γ * famN α β δ a b = 1 := by rw [hG]; exact famG_mul_famN hd0 ha0 hb0
  obtain ⟨L', hL', h₁, h₂⟩ := exists_dual_lat γ hγ _ hN
  refine Or.inr ⟨L', h₁, h₂, Or.inl (Or.inr (Or.inl ⟨dualGam Q v γ _ hN, [3, 2], hL', ?_⟩))⟩
  rw [locGram_dualGam]
  exact peelChainTheta_famN h2 hα hδ hβ ha hb

end Covered8

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, eighth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered8`, every $2$-adically automorphous number is, up to squares, the product of the norms of an
even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, eighth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual8 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered8 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The seventh residual statement from the eighth.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the eighth residual statement)"]
theorem theorem18DyadicResidual7_of_residual8 (h : Theorem18DyadicResidual8) : Theorem18DyadicResidual7 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered8 Q L v
    · exact theorem18OnlyIf_of_covered8 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the eighth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, eighth version)"]
theorem theorem18Dyadic_of_residual8 (h : Theorem18DyadicResidual8) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual7 (theorem18DyadicResidual7_of_residual8 h)

/-- **Conway–Sloane's Theorem 18 from the eighth residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual8`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, eighth version)"]
theorem theorem18Statement_of_residual8 (h : Theorem18DyadicResidual8) : Theorem18Statement :=
  theorem18Statement_of_residual7 (theorem18DyadicResidual7_of_residual8 h)

end QuadFormsKB.ConwaySloane
