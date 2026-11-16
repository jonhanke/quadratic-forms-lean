import QuadFormsKB.Historical.Gauss.Forms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Representations of binary forms by ternary forms (Disquisitiones Arithmeticae, Arts. 280, 290, 297)

the historical sources ids: (Art. 290, equivalent binary forms are represented by a ternary form equally
often) (Art. 297, the ternary proof of case V of quadratic reciprocity).

**Convention.** Gauss's forms have an even middle coefficient: his $(a, b, c)$ is
$a x^2 + 2 b x y + c y^2$ with integral symmetric Gram matrix `!![a, b; b, c]` (so `Φ` below is `!![a, b; b, c]`).
A ternary form is given by an integer matrix `F : Matrix (Fin 3) (Fin 3) ℤ` (symmetric in the application), and a
*representation* of the binary form with Gram matrix `Φ` by `F` is a matrix `M : Matrix (Fin 3) (Fin 2) ℤ`
(its columns are the two vectors the variables go to) with $M^{\mathsf T} F M = \Phi$. Indices are 0-based.

Part 1 (Art. 290) is proved unconditionally. Part 2 (Art. 297) proves the parity argument unconditionally, and
the deduction of case V conditionally on the named input `GaussArt288DiagonalInput`.
-/

namespace QuadFormsKB.Historical.Gauss

open Matrix

/-! ### Representations and the Art. 290 bijection -/

/-- **The $2 \times 2$ minors of a $3 \times 2$ matrix:** the minor of rows `i`, `j` of `M` is
$M_{i0} M_{j1} - M_{j0} M_{i1}$ (Gauss's three determinants of Art. 280). -/
def repMinor (M : Matrix (Fin 3) (Fin 2) ℤ) (i j : Fin 3) : ℤ := M i 0 * M j 1 - M j 0 * M i 1

/-- **Proper representation** (*Disq. Arith.* Art. 280): the three $2 \times 2$ minors of `M` (rows $0,1$; $0,2$;
$1,2$) have greatest common divisor $1$. -/
def IsProperRep (M : Matrix (Fin 3) (Fin 2) ℤ) : Prop :=
  Int.gcd (Int.gcd (repMinor M 0 1) (repMinor M 0 2)) (repMinor M 1 2) = 1

/-- **Representations of the binary form with Gram matrix `Φ` by the ternary form with Gram matrix `F`:**
the matrices `M` with $M^{\mathsf T} F M = \Phi$. -/
def Reps (F : Matrix (Fin 3) (Fin 3) ℤ) (Φ : Matrix (Fin 2) (Fin 2) ℤ) : Set (Matrix (Fin 3) (Fin 2) ℤ) :=
  {M | Mᵀ * F * M = Φ}

/-- **Proper representations** of `Φ` by `F`: the representations whose minors have gcd $1$. -/
def ProperReps (F : Matrix (Fin 3) (Fin 3) ℤ) (Φ : Matrix (Fin 2) (Fin 2) ℤ) :
    Set (Matrix (Fin 3) (Fin 2) ℤ) :=
  {M | Mᵀ * F * M = Φ ∧ IsProperRep M}

/-- **Minors under a substitution:** the minors of $M \Theta$ are $\det \Theta$ times those of $M$. -/
theorem repMinor_mul (M : Matrix (Fin 3) (Fin 2) ℤ) (Θ : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 3) :
    repMinor (M * Θ) i j = Θ.det * repMinor M i j := by
  simp only [repMinor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]; ring

/-- Properness is preserved by a substitution of determinant $1$ (the minors do not change). -/
theorem isProperRep_mul {M : Matrix (Fin 3) (Fin 2) ℤ} {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hΘ : Θ.det = 1) :
    IsProperRep (M * Θ) ↔ IsProperRep M := by
  simp [IsProperRep, repMinor_mul, hΘ]

/-- Composing a representation of $\Phi$ with $\Theta$ ($\Theta^{\mathsf T}\Phi\Theta = \Phi'$) gives a
representation of $\Phi'$. -/
theorem mul_mem_reps {F : Matrix (Fin 3) (Fin 3) ℤ} {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ}
    {Θ : Matrix (Fin 2) (Fin 2) ℤ} (h : Θᵀ * Φ * Θ = Φ') {M : Matrix (Fin 3) (Fin 2) ℤ}
    (hM : M ∈ Reps F Φ) : M * Θ ∈ Reps F Φ' := by
  simp only [Reps, Set.mem_setOf_eq] at *
  rw [← h, ← hM]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The inverse substitution: for $\det\Theta = 1$ the adjugate transforms $\Phi'$ back into $\Phi$. -/
theorem adjugate_transform {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ} {Θ : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : Θ.det = 1) (h : Θᵀ * Φ * Θ = Φ') : Θ.adjugateᵀ * Φ' * Θ.adjugate = Φ := by
  rw [← h]
  have h1 : Θ * Θ.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet]; simp
  have h2 : Θ.adjugateᵀ * Θᵀ = 1 := by rw [← Matrix.transpose_mul, h1]; simp
  calc Θ.adjugateᵀ * (Θᵀ * Φ * Θ) * Θ.adjugate
      = (Θ.adjugateᵀ * Θᵀ) * Φ * (Θ * Θ.adjugate) := by simp only [Matrix.mul_assoc]
    _ = Φ := by rw [h1, h2]; simp

/-- Right multiplication by $\Theta$ of determinant $1$ as an equivalence of $3 \times 2$ matrices
(inverse: right multiplication by the adjugate). -/
def substEquiv {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hdet : Θ.det = 1) :
    Matrix (Fin 3) (Fin 2) ℤ ≃ Matrix (Fin 3) (Fin 2) ℤ where
  toFun M := M * Θ
  invFun M := M * Θ.adjugate
  left_inv M := by
    have h1 : Θ * Θ.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet]; simp
    simp [Matrix.mul_assoc, h1]
  right_inv M := by
    have h1 : Θ.adjugate * Θ = 1 := by rw [Matrix.adjugate_mul, hdet]; simp
    simp [Matrix.mul_assoc, h1]

/-- **Equivalent binary forms are represented equally often, via an explicit bijection** (Gauss,
*Disq. Arith.* Art. 290): if $\Theta$ has determinant $1$ and transforms $\Phi$ into
$\Phi'$ (that is $\Theta^{\mathsf T} \Phi \Theta = \Phi'$, a proper equivalence), then $M \mapsto M \Theta$ is a
bijection from the representations of $\Phi$ by $F$ to those of $\Phi'$ by $F$. "Different representations go
to different ones, and every representation of $\Phi'$ arises" is the statement that this is an `Equiv`.
Gram-matrix convention: Gauss's $(a,b,c)$ is `!![a, b; b, c]`. Nothing is assumed about $F$. No difference from
the source. -/
@[kb "gauss1801" "Art. 290"]
def repsEquiv (F : Matrix (Fin 3) (Fin 3) ℤ) {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ}
    {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hdet : Θ.det = 1) (h : Θᵀ * Φ * Θ = Φ') :
    Reps F Φ ≃ Reps F Φ' :=
  (substEquiv hdet).subtypeEquiv (fun M => by
    show M ∈ Reps F Φ ↔ M * Θ ∈ Reps F Φ'
    refine ⟨fun hM => mul_mem_reps h hM, fun hM => ?_⟩
    have := mul_mem_reps (F := F) (adjugate_transform hdet h) hM
    have h1 : Θ * Θ.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet]; simp
    simpa [Matrix.mul_assoc, h1] using this)

/-- **Proper representations of equivalent forms correspond** (*Disq. Arith.* Art. 290, the historical sources
): under the hypotheses of `repsEquiv`, $M \mapsto M \Theta$ is a bijection
`ProperReps F Φ ≃ ProperReps F Φ'`. The minors of $M\Theta$ equal those of $M$ (`repMinor_mul`), so properness
is preserved in both directions. -/
@[kb "gauss1801" "Art. 290"]
def properRepsEquiv (F : Matrix (Fin 3) (Fin 3) ℤ) {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ}
    {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hdet : Θ.det = 1) (h : Θᵀ * Φ * Θ = Φ') :
    ProperReps F Φ ≃ ProperReps F Φ' :=
  (substEquiv hdet).subtypeEquiv (fun M => by
    have hr : M ∈ Reps F Φ ↔ M * Θ ∈ Reps F Φ' := by
      refine ⟨fun hM => mul_mem_reps h hM, fun hM => ?_⟩
      have := mul_mem_reps (F := F) (adjugate_transform hdet h) hM
      have h1 : Θ * Θ.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet]; simp
      simpa [Matrix.mul_assoc, h1] using this
    show (M ∈ Reps F Φ ∧ IsProperRep M) ↔ (M * Θ ∈ Reps F Φ' ∧ IsProperRep (M * Θ))
    rw [hr, isProperRep_mul hdet])

/-- **Equal numbers of representations** (*Disq. Arith.* Art. 290): properly equivalent
binary forms are represented by $F$ equally often (as cardinals, possibly both infinite). -/
@[kb "gauss1801" "Art. 290"]
theorem card_reps_eq (F : Matrix (Fin 3) (Fin 3) ℤ) {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ}
    {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hdet : Θ.det = 1) (h : Θᵀ * Φ * Θ = Φ') :
    Nat.card (Reps F Φ) = Nat.card (Reps F Φ') :=
  Nat.card_congr (repsEquiv F hdet h)

/-- **Equal numbers of proper representations** (*Disq. Arith.* Art. 290). -/
@[kb "gauss1801" "Art. 290"]
theorem card_properReps_eq (F : Matrix (Fin 3) (Fin 3) ℤ) {Φ Φ' : Matrix (Fin 2) (Fin 2) ℤ}
    {Θ : Matrix (Fin 2) (Fin 2) ℤ} (hdet : Θ.det = 1) (h : Θᵀ * Φ * Θ = Φ') :
    Nat.card (ProperReps F Φ) = Nat.card (ProperReps F Φ') :=
  Nat.card_congr (properRepsEquiv F hdet h)

/-! ### Art. 297: the ternary proof of case V of quadratic reciprocity -/

/-- Auxiliary: a square is $0$ mod $4$ with even root, or $1$ mod $4$ with odd root. -/
theorem sq_mod_four_cases (x : ℤ) :
    (x ^ 2 % 4 = 0 ∧ x % 2 = 0) ∨ (x ^ 2 % 4 = 1 ∧ x % 2 = 1) := by
  rcases Int.even_or_odd' x with ⟨k, hk | hk⟩
  · left
    have : x ^ 2 = 4 * (k ^ 2) := by subst hk; ring
    omega
  · right
    have : x ^ 2 = 4 * (k ^ 2 + k) + 1 := by subst hk; ring
    omega

/-- **Parity lemma** (*Disq. Arith.* Art. 297, end): there are no integer vectors
$\alpha, \beta \in \mathbb Z^3$ with $\sum \alpha_i^2 \equiv 3$, $\sum \beta_i^2 \equiv 3 \pmod 4$ and
$\sum \alpha_i \beta_i = 0$. (A sum of three squares is $\equiv 3 \pmod 4$ only if all three are odd, and then
$\sum \alpha_i \beta_i$ is a sum of three odd numbers, hence odd.) Proved unconditionally. -/
@[kb "gauss1801" "Art. 297"]
theorem no_orthogonal_three_mod_four (α β : Fin 3 → ℤ) (hα : (∑ i, α i ^ 2) % 4 = 3)
    (hβ : (∑ i, β i ^ 2) % 4 = 3) : ∑ i, α i * β i ≠ 0 := by
  simp only [Fin.sum_univ_three] at *
  have a0 := sq_mod_four_cases (α 0)
  have a1 := sq_mod_four_cases (α 1)
  have a2 := sq_mod_four_cases (α 2)
  have b0 := sq_mod_four_cases (β 0)
  have b1 := sq_mod_four_cases (β 1)
  have b2 := sq_mod_four_cases (β 2)
  have oa : α 0 % 2 = 1 ∧ α 1 % 2 = 1 ∧ α 2 % 2 = 1 := by omega
  have ob : β 0 % 2 = 1 ∧ β 1 % 2 = 1 ∧ β 2 % 2 = 1 := by omega
  have m0 : (α 0 * β 0) % 2 = 1 := by rw [Int.mul_emod, oa.1, ob.1]; rfl
  have m1 : (α 1 * β 1) % 2 = 1 := by rw [Int.mul_emod, oa.2.1, ob.2.1]; rfl
  have m2 : (α 2 * β 2) % 2 = 1 := by rw [Int.mul_emod, oa.2.2, ob.2.2]; rfl
  omega

/-- **Corollary for primes** (*Disq. Arith.* Art. 297): for primes $p, q \equiv 3 \pmod 4$ there are no
$\alpha, \beta \in \mathbb Z^3$ with $\sum\alpha_i^2 = p$, $\sum\beta_i^2 = q$, $\sum\alpha_i\beta_i = 0$. -/
theorem no_orthogonal_of_mod_four (p q : ℕ) (hp : p % 4 = 3) (hq : q % 4 = 3) (α β : Fin 3 → ℤ)
    (hα : ∑ i, α i ^ 2 = p) (hβ : ∑ i, β i ^ 2 = q) : ∑ i, α i * β i ≠ 0 :=
  no_orthogonal_three_mod_four α β (by rw [hα]; omega) (by rw [hβ]; omega)

/-- **The input from Arts. 288-292 for the form $(p, 0, q)$**: for primes
$p, q \equiv 3 \pmod 4$ with $p$ a non-residue of $q$ and $q$ a non-residue of $p$, there are
$\alpha, \beta \in \mathbb Z^3$ with $\alpha\cdot\alpha = p$, $\beta\cdot\beta = q$, $\alpha\cdot\beta = 0$, i.e.
$p t^2 + q u^2 = (\alpha_0 t + \beta_0 u)^2 + (\alpha_1 t + \beta_1 u)^2 + (\alpha_2 t + \beta_2 u)^2$. In Gauss this
is the special case of his theory of ternary representations of binary forms (Arts. 288-292) for the form
$(p, 0, q)$, whose characteristic number is $-1$.

This is **not proved here**: it is stated as a named proposition so that the deduction `art297_case_V` is
visibly conditional on it. By quadratic reciprocity the hypotheses are never both satisfied for distinct primes
(`gaussArt288DiagonalInput_of_reciprocity`), so the proposition is vacuously true and Gauss's deduction is not an
independent proof of reciprocity. -/
def GaussArt288DiagonalInput : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p % 4 = 3 → q % 4 = 3 →
    ¬ IsSquare ((p : ZMod q)) → ¬ IsSquare ((q : ZMod p)) →
    ∃ α β : Fin 3 → ℤ, ∑ i, α i ^ 2 = p ∧ ∑ i, β i ^ 2 = q ∧ ∑ i, α i * β i = 0

/-- **Case V of quadratic reciprocity, Gauss's ternary proof** (*Disq. Arith.* Art. 297, end; the historical sources
): *conditional on* `GaussArt288DiagonalInput` (the Art. 288-292 input), if $p \ne q$ are primes
$\equiv 3 \pmod 4$, then it is impossible that $p$ is a non-residue of $q$ and $q$ a non-residue of $p$.
Proof as in Gauss: the input would give $\alpha\cdot\alpha = p$, $\beta\cdot\beta = q$, $\alpha\cdot\beta = 0$,
contradicting the parity lemma. Not an independent proof of reciprocity (see the input's docstring). The case II
of the same article is not formalized. -/
@[kb "gauss1801" "Art. 297"]
theorem art297_case_V (h : GaussArt288DiagonalInput) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) :
    ¬ (¬ IsSquare ((p : ZMod q)) ∧ ¬ IsSquare ((q : ZMod p))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨α, β, ha, hb, hab⟩ := h p q hp hq hp3 hq3 h1 h2
  exact no_orthogonal_of_mod_four p q hp3 hq3 α β ha hb hab

/-- **The input is true (vacuously) by quadratic reciprocity:** for distinct primes $\equiv 3 \pmod 4$, exactly
one of "$q$ is a square mod $p$", "$p$ is a square mod $q$" holds, so the hypotheses of
`GaussArt288DiagonalInput` are never satisfied (and for $p = q$, $p$ is $0$, a square, mod $q$). Hence
`GaussArt288DiagonalInput` holds, via Mathlib's reciprocity. -/
theorem gaussArt288DiagonalInput_of_reciprocity : GaussArt288DiagonalInput := by
  intro p q hp hq hp3 hq3 h1 h2
  exfalso
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  by_cases hpq : p = q
  · subst hpq
    exact h1 ⟨0, by simp⟩
  · exact h2 ((ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp3 hq3 hpq).2 h1)

end QuadFormsKB.Historical.Gauss
