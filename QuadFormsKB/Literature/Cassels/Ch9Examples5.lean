/-
# Cassels, Chapter 9, Examples 4 and 7: explicit ternary forms; prescribed Hasse–Minkowski invariants

**Layer:** Cassels' Hasse–Minkowski invariant $c_v$ of a diagonal form $\langle a_0, a_1, a_2\rangle$ over $\mathbb Q$
(`RatPlace.hasseCassels`, $c_v = \prod_{i<j}(a_i, a_j)_v$, Ch. 4, §1, p. 55); a ternary rational form is
$\mathbb Q$-equivalent to a diagonal one, and $c_v$ does not depend on the diagonalization.

**Proves** Example 7 (pp. 162–163), with the condition $(*)$ reconstructed from the garbled scan as
$$c_2(f) = c_3(f) = -1, \qquad c_p(f) = +1 \quad (p \ne 2, 3):$$
* (i) (`ex7_i`): the classically integral form $f = x_0^2 + 3x_1^2 - x_2^2$ is real-equivalent to $x^2 + y^2 - z^2$
  and satisfies $(*)$; its determinant is $d(f) = -3$ (`ex7_det`). *Not formalized:* that $\lvert d(f)\rvert = 3$ is the
  least possible (for odd $p \nmid d(f)$ the form is $\mathbb Z_p$-unimodular, so $c_p(f) = 1$; hence $3 \mid d(f)$).
* (ii) (`ex7_ii`): there is no ternary rational form real-equivalent to $x^2 - y^2 - z^2$ (diagonalization with exactly
  one positive coefficient) satisfying $(*)$: then $c_\infty = -1$ and $\prod_v c_v = -1$, contradicting the product
  formula (`RatPlace.hasseCassels_product_formula`, Cassels Ch. 6, Lemma 1.1).

Also Example 4 (p. 162) for the three forms legible in the scan (the last two forms of the list are lost):
$x^2 + y^2 - 10z^2$ and $x^2 - y^2 + 10z^2$ are properly equivalent (`ex4_properIntEquiv`, an explicit $T$), and neither
is equivalent to $x^2 + 2y^2 - 5z^2$ (`ex4_not_intEquiv`, `ex4_not_intEquiv'`: the numbers of zeros modulo $5$ are $45$
and $5$, an invariant of equivalence modulo $5$, `card_zeros_eq_of_isometricGL`).
-/
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open RatPlace

/-- $(1, b)_v = 1$ at every place $v$ of $\mathbb Q$. -/
theorem ratPlace_hilbert_one_left (v : RatPlace) (b : ℚ) : v.hilbert 1 b = 1 := by
  cases v with
  | infinite => simp only [RatPlace.hilbert, Rat.cast_one]; rw [hilbertSymbol_comm, hilbertSymbol_one_right]
  | finite p => simp only [RatPlace.hilbert, Rat.cast_one]; rw [hilbertSymbol_comm, hilbertSymbol_one_right]

/-- Cassels' $c_v$ of a ternary diagonal form: $c_v(\langle a_0, a_1, a_2\rangle) = (a_0,a_1)_v(a_0,a_2)_v(a_1,a_2)_v$. -/
theorem hasseCassels_three (v : RatPlace) (a : Fin 3 → ℚ) :
    v.hasseCassels a = v.hilbert (a 0) (a 1) * v.hilbert (a 0) (a 2) * v.hilbert (a 1) (a 2) := by
  simp [RatPlace.hasseCassels, Fin.prod_univ_three]

/-- The diagonal entries $(1, 3, -1)$ of Example 7 (i). -/
def ex7Diag : Fin 3 → ℚ := ![1, 3, -1]

/-- $c_v(\langle 1, 3, -1\rangle) = (3, -1)_v$. -/
theorem hasseCassels_ex7Diag (v : RatPlace) : v.hasseCassels ex7Diag = v.hilbert 3 (-1) := by
  rw [hasseCassels_three]
  simp [ex7Diag, ratPlace_hilbert_one_left]

/-- **Cassels, Ch. 9, Example 7 (i)** (p. 163): *find a classically integral ternary form $f$ which is real-equivalent
to $x^2 + y^2 - z^2$ and for which $(*)$ $c_2(f) = c_3(f) = -1$, $c_p(f) = +1$ ($p \ne 2, 3$).* The form
$f = x_0^2 + 3x_1^2 - x_2^2$ (`QuadForm.diag ![1, 3, -1]`, classically integral, real-equivalent to
$x_0^2 + x_1^2 - x_2^2$ by $x_1 \mapsto x_1/\sqrt 3$) has $c_v(f) = (3, -1)_v$, which is $-1$ at $v = 2, 3$ and $+1$
elsewhere. ($(*)$ is reconstructed from the scan; module docstring.) -/
@[kb "cassels1978" "Ch. 9, Ex. 7 (i), p. 163"]
theorem ex7_i :
    IsClassicallyIntegral (QuadForm.diag ![1, 3, -1] : QuadForm ℤ 3) ∧
    IsometricGL ((QuadForm.diag ![1, 3, -1] : QuadForm ℤ 3).map (Int.castRingHom ℝ))
      ((QuadForm.diag ![1, 1, -1] : QuadForm ℤ 3).map (Int.castRingHom ℝ)) ∧
    (finite ⟨2, Nat.prime_two⟩).hasseCassels ex7Diag = -1 ∧
    (finite ⟨3, Nat.prime_three⟩).hasseCassels ex7Diag = -1 ∧
    ∀ p : Nat.Primes, p.1 ≠ 2 → p.1 ≠ 3 → (finite p).hasseCassels ex7Diag = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [isClassicallyIntegral_iff]
    intro i j hij
    simp [QuadForm.diag, hij.ne]
  · have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    set d : Fin 3 → ℝ := ![1, (Real.sqrt 3)⁻¹, 1]
    have hd : IsUnit (Matrix.diagonal d).det := by
      rw [det_diagonal, Fin.prod_univ_three]
      simp [d, h3.ne']
    refine ⟨Matrix.nonsingInvUnit _ hd, fun x => ?_⟩
    show (QuadForm.map _ _).eval (Matrix.diagonal d *ᵥ x) = _
    simp [mulVec_diagonal, QuadForm.eval, QuadForm.evalIn, QuadForm.diag, QuadForm.map, Fin.sum_univ_three, Matrix.diagonal_apply, d]
    have : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [this]
  · rw [hasseCassels_ex7Diag]
    rw [ConwaySloane.hilbert_two_int 0 0 3 (-1) 3 (-1) (by decide) (by decide) (by norm_num) (by norm_num)]
    decide
  · rw [hasseCassels_ex7Diag]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [ConwaySloane.hilbert_odd_int 3 (by norm_num) 1 0 1 (-1) 3 (-1) (by decide) (by decide) (by norm_num)
      (by norm_num)]
    have : legendreSym 3 (-1) = -1 := by
      rw [legendreSym.at_neg_one (by norm_num)]
      decide
    simp [this]
  · intro p hp2 hp3
    rw [hasseCassels_ex7Diag]
    have : Fact p.1.Prime := ⟨p.2⟩
    have h := HilbertLocal.hilbert_eq_one_of_padicValRat (p := p.1) hp2 3 (-1) (by norm_num) (by norm_num) ?_ ?_
    · exact h
    · have : padicValRat p.1 3 = padicValNat p.1 3 := by exact_mod_cast padicValRat.of_nat (p := p.1) (n := 3)
      rw [this, padicValNat.eq_zero_of_not_dvd]
      · rfl
      · intro hd
        exact hp3 ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).1 hd)
    · rw [padicValRat.neg, padicValRat.one]

/-- The determinant of $x_0^2 + 3x_1^2 - x_2^2$ in Cassels' normalization: $d(f) = \det(f_{ij}) = -3$. -/
theorem ex7_det : (casselsMat (QuadForm.diag ![1, 3, -1] : QuadForm ℤ 3)).det = -3 := by
  rw [Matrix.det_fin_three]
  simp [casselsMat, QuadForm.hessian, QuadForm.diag, Matrix.diagonal_apply]

/-- **Cassels, Ch. 9, Example 7 (ii)** (p. 163): *there is no ternary form real-equivalent to $x^2 - y^2 - z^2$
satisfying $(*)$.* For a diagonal form $\langle a_0, a_1, a_2\rangle$ over $\mathbb Q$ with nonzero entries of which
exactly one is positive (real-equivalent to $x^2 - y^2 - z^2$ by Sylvester's law of inertia; every rational ternary
form is $\mathbb Q$-equivalent to such a diagonal form), $(*)$ cannot hold: $c_\infty = -1$, so
$\prod_v c_v = (-1)^3 \ne 1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 7 (ii), p. 163"]
theorem ex7_ii (a : Fin 3 → ℚ) (ha : ∀ i, a i ≠ 0) (hsign : (Finset.univ.filter fun i => 0 < a i).card = 1) :
    ¬ ((finite ⟨2, Nat.prime_two⟩).hasseCassels a = -1 ∧ (finite ⟨3, Nat.prime_three⟩).hasseCassels a = -1 ∧
      ∀ p : Nat.Primes, p.1 ≠ 2 → p.1 ≠ 3 → (finite p).hasseCassels a = 1) := by
  classical
  rintro ⟨h2, h3, hp⟩
  -- `c_∞ = -1`
  have hinf : infinite.hasseCassels a = -1 := by
    rw [hasseCassels_three]
    simp only [RatPlace.hilbert]
    have hr : ∀ i, ((a i : ℚ) : ℝ) ≠ 0 := fun i => by exact_mod_cast ha i
    rw [HasseIsoNF.hilbertSymbol_real_eq _ _ (hr 0) (hr 1), HasseIsoNF.hilbertSymbol_real_eq _ _ (hr 0) (hr 2),
      HasseIsoNF.hilbertSymbol_real_eq _ _ (hr 1) (hr 2)]
    have hlt : ∀ i, ((a i : ℚ) : ℝ) < 0 ↔ ¬ 0 < a i := fun i => by
      rw [Rat.cast_lt_zero]
      exact ⟨fun h h' => absurd (h.trans h') (lt_irrefl _), fun h => lt_of_le_of_ne (not_lt.1 h) (ha i)⟩
    simp only [hlt]
    rw [Finset.card_eq_one] at hsign
    obtain ⟨k, hk⟩ := hsign
    have hk' : ∀ i, 0 < a i ↔ i = k := fun i => by
      have := congrArg (i ∈ ·) hk
      simpa using this
    simp only [hk']
    fin_cases k <;> simp
  -- the product formula
  obtain ⟨-, hprod⟩ := hasseCassels_product_formula a ha
  have hsupp : Function.mulSupport (fun v : RatPlace => v.hasseCassels a) ⊆
      ({infinite, finite ⟨2, Nat.prime_two⟩, finite ⟨3, Nat.prime_three⟩} : Finset RatPlace) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases v with _ | p
    · exact Or.inl rfl
    · by_cases hp2 : p.1 = 2
      · exact Or.inr (Or.inl (by congr 1; exact Subtype.ext hp2))
      · by_cases hp3 : p.1 = 3
        · exact Or.inr (Or.inr (by congr 1; exact Subtype.ext hp3))
        · exact absurd (hp p hp2 hp3) hv
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp] at hprod
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by
    rw [Finset.mem_singleton]; intro h; injection h with h
    exact absurd (congrArg Subtype.val h) (by norm_num)), Finset.prod_singleton, hinf, h2, h3] at hprod
  norm_num at hprod

/-! ### Example 4 -/

/-- Evaluation of a ternary diagonal form $\langle d_0, d_1, d_2\rangle$ over a commutative ring. -/
theorem eval_map_diag_three {R : Type*} [CommRing R] (d : Fin 3 → ℤ) (x : Fin 3 → R) :
    ((QuadForm.diag d : QuadForm ℤ 3).map (Int.castRingHom R)).eval x =
      d 0 * x 0 ^ 2 + d 1 * x 1 ^ 2 + d 2 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, QuadForm.diag, QuadForm.map, Matrix.diagonal_apply]
  ring

/-- Evaluation of a ternary diagonal form over $\mathbb Z$. -/
theorem eval_diag_three (d : Fin 3 → ℤ) (x : Fin 3 → ℤ) :
    (QuadForm.diag d : QuadForm ℤ 3).eval x = d 0 * x 0 ^ 2 + d 1 * x 1 ^ 2 + d 2 * x 2 ^ 2 := by
  have h := eval_map_diag_three (R := ℤ) d x
  simpa [QuadForm.map] using h

/-- Equivalent forms over a finite commutative ring have equally many zeros. -/
theorem card_zeros_eq_of_isometricGL {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {n : ℕ}
    {Q Q' : QuadForm R n} (h : IsometricGL Q Q') :
    (Finset.univ.filter fun x => Q'.eval x = 0).card = (Finset.univ.filter fun x => Q.eval x = 0).card := by
  obtain ⟨g, hg⟩ := h
  refine Finset.card_bij (fun x _ => g.val *ᵥ x) (fun x hx => ?_) (fun x _ y _ hxy => ?_) (fun y hy => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hg]; exact hx
  · have := congrArg (fun v => (g⁻¹).val *ᵥ v) hxy
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  · refine ⟨(g⁻¹).val *ᵥ y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]; exact hy
    · rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **Cassels, Ch. 9, Example 4** (p. 162), first pair: $x^2 + y^2 - 10z^2$ and $x^2 - y^2 + 10z^2$ are properly
integrally equivalent, by the matrix $T$ with rows $(-1, 0, 0)$, $(0, -3, -10)$, $(0, -1, -3)$ ($\det T = 1$). -/
@[kb "cassels1978" "Ch. 9, Ex. 4, p. 162 (x²+y²−10z² ~ x²−y²+10z²)"]
theorem ex4_properIntEquiv :
    ProperIntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![1, -1, 10]) := by
  let T : GL (Fin 3) ℤ := ⟨!![-1, 0, 0; 0, -3, -10; 0, -1, -3], !![-1, 0, 0; 0, 3, -10; 0, -1, 3],
    by decide, by decide⟩
  refine ⟨T, by decide, fun x => ?_⟩
  rw [eval_diag_three, eval_diag_three]
  simp [T, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The number of zeros of $x^2 + y^2 - 10z^2$ modulo $5$ is $45$. -/
theorem card_zeros_ex4a :
    (Finset.univ.filter fun x : Fin 3 → ZMod 5 =>
      ((QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3).map (Int.castRingHom (ZMod 5))).eval x = 0).card = 45 := by
  simp only [eval_map_diag_three]
  decide

/-- The number of zeros of $x^2 + 2y^2 - 5z^2$ modulo $5$ is $5$. -/
theorem card_zeros_ex4c :
    (Finset.univ.filter fun x : Fin 3 → ZMod 5 =>
      ((QuadForm.diag ![1, 2, -5] : QuadForm ℤ 3).map (Int.castRingHom (ZMod 5))).eval x = 0).card = 5 := by
  simp only [eval_map_diag_three]
  decide

/-- **Cassels, Ch. 9, Example 4** (p. 162): $x^2 + y^2 - 10z^2$ and $x^2 + 2y^2 - 5z^2$ are not integrally equivalent
(not even equivalent modulo $5$: $45 \ne 5$ zeros). -/
@[kb "cassels1978" "Ch. 9, Ex. 4, p. 162 (x²+y²−10z² ≁ x²+2y²−5z²)"]
theorem ex4_not_intEquiv :
    ¬ IntEquiv (QuadForm.diag ![1, 1, -10] : QuadForm ℤ 3) (QuadForm.diag ![1, 2, -5]) := by
  intro h
  have h5 := h.sameGenus.isometricGL_zmod (c := 5) (by norm_num)
  have := card_zeros_eq_of_isometricGL h5
  rw [card_zeros_ex4a, card_zeros_ex4c] at this
  exact absurd this (by norm_num)

/-- **Cassels, Ch. 9, Example 4** (p. 162): $x^2 - y^2 + 10z^2$ and $x^2 + 2y^2 - 5z^2$ are not integrally equivalent. -/
theorem ex4_not_intEquiv' :
    ¬ IntEquiv (QuadForm.diag ![1, -1, 10] : QuadForm ℤ 3) (QuadForm.diag ![1, 2, -5]) := fun h =>
  ex4_not_intEquiv (ex4_properIntEquiv.intEquiv.trans h)

end QuadFormsKB.Siegel
