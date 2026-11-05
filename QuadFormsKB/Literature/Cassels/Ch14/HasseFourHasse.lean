/-
# Cassels, Chapter 14, §7: the Hasse–Minkowski invariants of the split-off binary forms

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §7, p. 354, step 1: if $f \cong g_v \perp H$ over $\mathbb Q_v$
then $\prod_v c_v(g_v) = 1$, so that Lemma 5.1 (`exists_rat_form_of_local`) applies. With
$f \cong \langle a_0, \dots, a_3 \rangle$ ($a_i \in \mathbb Q$) and $g_v \cong \langle b_0, b_1 \rangle$,
$b_0 b_1 = -a_0 a_1 a_2 a_3$:
$$c_v(g_v) = (b_0, b_1)_v = c_v(a) \cdot (-a_0 a_1 a_2 a_3, -1)_v \qquad (\texttt{splitSign}),$$
and both factors satisfy the product formula.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

namespace QuadFormsKB.Composition

open QuadForm

/-- The value $c_v(a) \cdot (-a_0 a_1 a_2 a_3, -1)_v$ at the place $v$ of $\mathbb Q$, for $a \in \mathbb Q^4$: the
Hasse–Minkowski invariant of the binary form split off from $\langle a_0, \dots, a_3 \rangle$ at $v$
(`hasseC_split_padic`, `hasseC_split_real`). -/
noncomputable def splitSign (a : Fin 4 → ℚ) : RatPlace → ℤ
  | .infinite => PadicClass.hasseVec (fun i => (a i : ℝ)) *
      hilbertSymbol ℝ (-((a 0 * a 1 * a 2 * a 3 : ℚ) : ℝ)) (-1)
  | .finite p => haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      PadicClass.hasseVec (fun i => (a i : ℚ_[p])) *
      hilbertSymbol ℚ_[p] (-((a 0 * a 1 * a 2 * a 3 : ℚ) : ℚ_[p])) (-1)

/-- Algebraic core: if $c(a) = c(\langle b_0, b_1, 1, -1\rangle)$, $b_0 b_1 = -a_0a_1a_2a_3$, and the symbol is
multiplicative in the first slot, then $(b_0, b_1) = c(a) \, (-a_0a_1a_2a_3, -1)$. -/
theorem split_core {K : Type*} [Field K] [CharZero K]
    (hml : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b)
    {a : Fin 4 → K} {b₀ b₁ : K} (h₀ : b₀ ≠ 0) (h₁ : b₁ ≠ 0) (hb : b₀ * b₁ = -(a 0 * a 1 * a 2 * a 3))
    (hv : PadicClass.hasseVec a = PadicClass.hasseVec ![b₀, b₁, 1, -1]) :
    hilbertSymbol K b₀ b₁ = PadicClass.hasseVec a * hilbertSymbol K (-(a 0 * a 1 * a 2 * a 3)) (-1) := by
  have hx : PadicClass.hasseVec ![b₀, b₁, 1, -1] =
      hilbertSymbol K b₀ b₁ * hilbertSymbol K (b₀ * b₁) (-1) := by
    rw [hml b₀ b₁ (-1) h₀ h₁ (by simp)]
    simp [PadicClass.hasseVec, Fin.prod_univ_succ, hilbertSymbol_one_right, PadicClass.hs_one_left]
    ring
  rw [hv, hx, ← hb, mul_assoc]
  rcases PadicClass.hs_pm b₀ b₁ with h | h <;> rcases PadicClass.hs_pm (b₀ * b₁) (-1) with h' | h' <;>
    rw [h, h'] <;> norm_num

/-- **The split-off binary form over $\mathbb Q_p$**: if $\langle a \rangle \cong \langle b_0, b_1, 1, -1 \rangle$
over $\mathbb Q_p$ with $b_0 b_1 = -a_0 a_1 a_2 a_3$, then
$c_p(\langle b_0, b_1 \rangle) = c_p(a) \, (-a_0 a_1 a_2 a_3, -1)_p$. -/
theorem hasseC_split_padic (p : ℕ) [Fact p.Prime] {a : Fin 4 → ℚ_[p]} (ha : ∀ i, a i ≠ 0) {b₀ b₁ : ℚ_[p]}
    (h₀ : b₀ ≠ 0) (h₁ : b₁ ≠ 0) (hb : b₀ * b₁ = -(a 0 * a 1 * a 2 * a 3))
    (hiso : (diag a).IsometricIn ℚ_[p] (diag ![b₀, b₁, 1, -1])) :
    hasseC (diag ![b₀, b₁]) = PadicClass.hasseVec a * hilbertSymbol ℚ_[p] (-(a 0 * a 1 * a 2 * a 3)) (-1) := by
  have hnd : (diag ![b₀, b₁]).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [Binary.hessian_det_two]; simp [QuadForm.diag]; exact ⟨h₀, h₁⟩
  have hne : ∀ i, (![b₀, b₁] : Fin 2 → ℚ_[p]) i ≠ 0 := by
    intro i; fin_cases i
    · simpa using h₀
    · simpa using h₁
  rw [hasseC_eq_of_isometric p hnd hne (QuadForm.isometricIn_refl _ _), PadicClass.hasseVec_two]
  refine split_core (PadicClass.localHilbertField_padic p).mul_left h₀ h₁ hb ?_
  refine PadicClass.hasseVec_eq_of_isometric (PadicClass.localHilbertField_padic p) 4 _ _ ha ?_ hiso
  intro i; fin_cases i <;> simp [h₀, h₁]

/-- **The split-off binary form over $\mathbb R$**: as `hasseC_split_padic`, over $\mathbb R$. -/
theorem hasseC_split_real {a : Fin 4 → ℝ} (ha : ∀ i, a i ≠ 0) {b₀ b₁ : ℝ}
    (h₀ : b₀ ≠ 0) (h₁ : b₁ ≠ 0) (hb : b₀ * b₁ = -(a 0 * a 1 * a 2 * a 3))
    (hiso : (diag a).IsometricIn ℝ (diag ![b₀, b₁, 1, -1])) :
    hasseC (diag ![b₀, b₁]) = PadicClass.hasseVec a * hilbertSymbol ℝ (-(a 0 * a 1 * a 2 * a 3)) (-1) := by
  rw [hasseC_diag_real h₀ h₁]
  refine split_core HilbertLocal.hilbertSymbol_real_mul_left h₀ h₁ hb ?_
  refine HasseIsoNF.hasseVec_real_isometric a _ ha ?_ hiso
  intro i; fin_cases i <;> simp [h₀, h₁]

/-- `splitSign` is Cassels' $c_v$ times $(-a_0a_1a_2a_3, -1)_v$ in terms of `RatPlace.hilbert`. -/
theorem splitSign_eq (a : Fin 4 → ℚ) (v : RatPlace) :
    splitSign a v = v.hasseCassels a * v.hilbert (-(a 0 * a 1 * a 2 * a 3)) (-1) := by
  cases v with
  | infinite =>
    simp [splitSign, RatPlace.hasseCassels, RatPlace.hilbert, PadicClass.hasseVec]
  | finite p =>
    simp [splitSign, RatPlace.hasseCassels, RatPlace.hilbert, PadicClass.hasseVec]

/-- Splitting a finitely supported product over the places of $\mathbb Q$ into the finite primes and $\infty$. -/
theorem finprod_places_split (f : RatPlace → ℤ) (hf : Function.HasFiniteMulSupport f) :
    ∏ᶠ v : RatPlace, f v = (∏ᶠ p : Nat.Primes, f (.finite p)) * f .infinite := by
  have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
  have hU : (Set.univ : Set RatPlace) = insert .infinite (Set.range RatPlace.finite) := by
    ext v; cases v <;> simp
  rw [← finprod_mem_univ, hU, finprod_mem_insert' f (by simp)
    (hf.subset Set.inter_subset_right), finprod_mem_range (g := RatPlace.finite) hinj, mul_comm]

/-- **Product formula for `splitSign`** (Hilbert reciprocity, Cassels, Ch. 6, Lemma 3.4): for non-zero
$a_0, \dots, a_3 \in \mathbb Q$, `splitSign a p` is $1$ for all but finitely many primes $p$ and
$\prod_p \mathtt{splitSign}\,a\,p \cdot \mathtt{splitSign}\,a\,\infty = 1$. -/
theorem splitSign_finite_prod (a : Fin 4 → ℚ) (ha : ∀ i, a i ≠ 0) :
    {p : Nat.Primes | splitSign a (.finite p) ≠ 1}.Finite ∧
      (∏ᶠ p : Nat.Primes, splitSign a (.finite p)) * splitSign a .infinite = 1 := by
  have hD : (-(a 0 * a 1 * a 2 * a 3) : ℚ) ≠ 0 := by
    have := ha 0; have := ha 1; have := ha 2; have := ha 3
    simp [*]
  obtain ⟨h1, h2⟩ := hasseCassels_product_formula a ha
  obtain ⟨h3, h4⟩ := finprod_hilbert (-(a 0 * a 1 * a 2 * a 3)) (-1) hD (by norm_num)
  have hf : Function.HasFiniteMulSupport (splitSign a) := by
    have : splitSign a = fun v => v.hasseCassels a * v.hilbert (-(a 0 * a 1 * a 2 * a 3)) (-1) :=
      funext (splitSign_eq a)
    rw [this]
    exact (h1.union h3).subset (Function.mulSupport_mul _ _)
  have hall : ∏ᶠ v : RatPlace, splitSign a v = 1 := by
    simp only [splitSign_eq]
    rw [finprod_mul_distrib h1 h3, h2, h4]; norm_num
  rw [finprod_places_split _ hf] at hall
  refine ⟨?_, hall⟩
  have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
  exact (hf.preimage hinj.injOn).subset (fun p hp => hp)

end QuadFormsKB.Composition
