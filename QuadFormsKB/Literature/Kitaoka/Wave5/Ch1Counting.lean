/-
# Kitaoka 1993, Lemmas 1.3.1 and 1.3.2: counting values of a quadratic form over a finite field

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, pp. 14–15 (printed pages): the function
$\chi(U)$ (p. 14), Lemma 1.3.1 and Lemma 1.3.2 (p. 15).

**Setting.** $F = \mathbb F_q$ is a finite field with $q$ elements and $(U, Q)$ a regular quadratic space over $F$ of
dimension $u$ (polar form nondegenerate; Mathlib `QuadraticForm F (Fin u → F)`). For $t \in F$,
$a(t, U) = \#\{x \in U \mid Q(x) = t\}$ (`valCount Q t`). $\chi(U) = 0$ if $u$ is odd, $1$ if $U$ is hyperbolic and
$-1$ otherwise (`Kitaoka.chiV`, from `Wave3/Ch5Lemma569.lean`; hyperbolic means Witt index $u/2$).

**Proves** (unconditional)
* `lemma131` (Lemma 1.3.1): $a(0, U) = q^{u-1} - \chi(U)q^{u/2-1} + \chi(U)q^{u/2}$;
* `lemma132` (Lemma 1.3.2, the count): for $u$ even and $t \ne 0$, $a(t, U) = q^{u-1}(1 - \chi(U)q^{-u/2})$.
  Kitaoka's first assertion (an automorphism $f$ of the space with $Q(f(x)) = tQ(x)$) is not formalized; the count is
  proved without it.

**Proof.** By the Witt decomposition $U \cong H^m \perp U_a$ (`QuadraticForm.wittIndex_spec`, $m$ the Witt index,
$U_a$ anisotropic of dimension $w \le 2$, `Kitaoka.finrank_le_two_of_anisotropic`), and the recursion
$a(t, H \perp U') = (q-1)\,\#U' + q\,a(t, U')$ (Kitaoka's computation in the proof of Lemma 1.3.1), one gets
$a(t, U) = q^{u-1} + q^m\bigl(a(t, U_a) - q^{w-1}\bigr)$ (`valCount_wittDecomp`). Here $a(0, U_a) = 1$, and for $w = 2$,
$t \ne 0$: $a(t, U_a) = q + 1$. Kitaoka gets the last value from $U_a \cong (F', N)$; here it is counted directly: in
characteristic $2$ every $t$ is a square, so $a(t, U_a)$ does not depend on $t \ne 0$; otherwise the regular ternary
space $U_a \perp \langle -t\rangle$ has $q^2$ zeros (by the formula above, its Witt index being $1$), and
$q^2 = 1 + (q-1)\,a(t, U_a)$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch1FiniteField
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Lemma569
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F] [Finite F]

/-- $a(t, U) = \#\{x \in U \mid Q(x) = t\}$ (Kitaoka 1993, §1.3, p. 14). -/
@[kb "kitaoka1993" "§1.3, p. 14 (a(t, U))"]
def valCount {V : Type} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (t : F) : ℕ := Nat.card {x : V // Q x = t}

theorem valCount_congr {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] {Q : QuadraticForm F V} {P : QuadraticForm F W} (h : Q.Equivalent P)
    (t : F) : valCount Q t = valCount P t := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun x => by
    change Q x = t ↔ P (e x) = t
    rw [e.map_app])

open Classical in
/-- $\#\{(a, b) \in F^2 \mid ab = c\} = (q - 1) + q\,[c = 0]$. -/
theorem card_mul_eq (c : F) :
    (Nat.card {b : F × F // b.1 * b.2 = c} : ℝ) = (Nat.card F - 1 : ℝ) + if c = 0 then (Nat.card F : ℝ) else 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : F => a * b = c)), Nat.card_sigma]
  have hterm : ∀ a : F, (Nat.card {b : F // a * b = c} : ℝ) =
      if a = 0 then (if c = 0 then (Nat.card F : ℝ) else 0) else 1 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      by_cases hc : c = 0
      · subst hc; simp
      · simp only [zero_mul, if_true, hc, if_false]
        have : IsEmpty {b : F // (0 : F) = c} := ⟨fun b => hc b.2.symm⟩
        simp
    · rw [if_neg ha]
      have : Nat.card {b : F // a * b = c} = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨c / a, by field_simp⟩, fun b => Subtype.ext ?_⟩
        have := b.2
        simp only
        field_simp
        rw [mul_comm]; exact this
      rw [this, Nat.cast_one]
  push_cast
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have h0 : (Finset.univ.filter fun a : F => a = 0).card = 1 := Finset.card_eq_one.2 ⟨0, by ext; simp⟩
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
    (fun a : F => a = 0)
  rw [h0, Finset.card_univ, ← Nat.card_eq_fintype_card] at htot
  have hne : ((Finset.univ.filter fun a : F => ¬ a = 0).card : ℝ) = Nat.card F - 1 := by
    have := congrArg (Nat.cast : ℕ → ℝ) htot; push_cast at this; linarith
  simp only [h0, nsmul_eq_mul, one_smul, mul_one, hne, Nat.cast_one, one_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The orthogonal sum with a hyperbolic plane: $a(t, H \perp U') = (q - 1)\,\#U' + q\,a(t, U')$. -/
theorem valCount_hyp_prod (Q : QuadraticForm F V) (t : F) :
    (valCount ((QuadraticForm.hyperbolicPlane F).prod Q) t : ℝ) =
      (Nat.card F - 1 : ℝ) * Nat.card V + Nat.card F * valCount Q t := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Finite V := Module.finite_of_finite F
  have : Fintype V := Fintype.ofFinite V
  have e : {x : (F × F) × V // ((QuadraticForm.hyperbolicPlane F).prod Q) x = t} ≃
      Σ v : V, {b : F × F // b.1 * b.2 = t - Q v} :=
    (Equiv.subtypeEquiv (Equiv.prodComm (F × F) V) (fun x => by
      simp only [QuadraticMap.prod_apply, QuadraticForm.hyperbolicPlane_apply, Equiv.prodComm_apply,
        Prod.fst_swap, Prod.snd_swap]
      constructor <;> intro h <;> linear_combination h)).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun (v : V) (b : F × F) => b.1 * b.2 = t - Q v))
  rw [valCount, Nat.card_congr e, Nat.card_sigma]
  push_cast
  simp only [card_mul_eq, sub_eq_zero, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.univ.filter fun v : V => t = Q v).card : ℝ) = valCount Q t := by
    rw [valCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2; ext v; simp [eq_comm]
  rw [hc, Nat.card_eq_fintype_card (α := V)]
  ring

/-- The closed form for $H^m \perp U_a$: $a(t, H^m \perp U_a) = q^{2m}\#U_a/q + q^m\,(a(t, U_a) - \#U_a/q)$. -/
theorem valCount_hypSpace_prod {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (Qa : QuadraticForm F U) (t : F) (m : ℕ) :
    (valCount ((QuadraticForm.hyperbolicSpace F m).prod Qa) t : ℝ) =
      (Nat.card F : ℝ) ^ (2 * m) * Nat.card U / Nat.card F +
        (Nat.card F : ℝ) ^ m * (valCount Qa t - Nat.card U / Nat.card F) := by
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  induction m with
  | zero =>
    rw [valCount_congr ⟨QuadraticForm.Witt.hyperbolicSpaceZeroProd Qa⟩]
    field_simp; ring
  | succ m ih =>
    have e : ((QuadraticForm.hyperbolicSpace F (m + 1)).prod Qa).Equivalent
        ((QuadraticForm.hyperbolicPlane F).prod ((QuadraticForm.hyperbolicSpace F m).prod Qa)) :=
      ⟨(((QuadraticForm.Witt.hyperbolicSpaceSucc m).symm.prod (QuadraticMap.IsometryEquiv.refl Qa)).trans
        (QuadraticForm.Witt.prodAssoc _ _ _))⟩
    rw [valCount_congr e, valCount_hyp_prod, ih]
    have hcard : (Nat.card ((Fin m → F × F) × U) : ℝ) = (Nat.card F : ℝ) ^ (2 * m) * Nat.card U := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
      push_cast; ring
    rw [hcard]
    field_simp
    ring

/-- **The count from a Witt decomposition**: if $Q \cong H^m \perp U_a$ with $U_a$ of dimension $w$, then
$a(t, Q) = q^{u-1} + q^m(a(t, U_a) - q^{w-1})$, $u = 2m + w$. -/
theorem valCount_wittDecomp (Q : QuadraticForm F V) {U : Type} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] (Qa : QuadraticForm F U) (m : ℕ)
    (h : Q.Equivalent ((QuadraticForm.hyperbolicSpace F m).prod Qa)) (t : F) :
    (valCount Q t : ℝ) =
      (Nat.card F : ℝ) ^ ((finrank F V : ℤ) - 1) +
        (Nat.card F : ℝ) ^ m * (valCount Qa t - (Nat.card F : ℝ) ^ ((finrank F U : ℤ) - 1)) := by
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  have hdim : finrank F V = 2 * m + finrank F U := by
    obtain ⟨e⟩ := h
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype]
    simp [Module.finrank_prod]
    ring
  rw [valCount_congr h, valCount_hypSpace_prod, Module.natCard_eq_pow_finrank (K := F) (V := U), hdim,
    zpow_sub_one₀ hq.ne', zpow_sub_one₀ hq.ne', zpow_natCast, zpow_natCast, pow_add, Nat.cast_pow]
  ring

/-! ### Anisotropic parts -/

/-- An anisotropic form takes the value $0$ only at $0$: $a(0, U_a) = 1$. -/
theorem valCount_zero_of_anisotropic {U : Type} [AddCommGroup U] [Module F U] (Qa : QuadraticForm F U)
    (ha : Qa.Anisotropic) : valCount Qa 0 = 1 := by
  rw [valCount, Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, map_zero _⟩, fun x => Subtype.ext (ha _ x.2)⟩

/-- $a(t, U) = a(c^2 t, U)$ for $c \ne 0$ (the bijection $x \mapsto cx$). -/
theorem valCount_smul_sq {U : Type} [AddCommGroup U] [Module F U] (Qa : QuadraticForm F U) (t : F) {c : F}
    (hc : c ≠ 0) : valCount Qa (c ^ 2 * t) = valCount Qa t := by
  refine Nat.card_congr (Equiv.mk (fun x => ⟨c⁻¹ • x.1, ?_⟩) (fun x => ⟨c • x.1, ?_⟩) (fun x => ?_) (fun x => ?_) :
    {x : U // Qa x = c ^ 2 * t} ≃ {x : U // Qa x = t})
  · rw [QuadraticMap.map_smul, x.2, smul_eq_mul]; field_simp
  · rw [QuadraticMap.map_smul, x.2]; ring
  · ext; simp [smul_smul, hc]
  · ext; simp [smul_smul, hc]

/-- The values of $Q$ partition $U$: $\sum_t a(t, U) = \#U$. -/
theorem sum_valCount [Fintype F] {U : Type} [AddCommGroup U] [Module F U] [Finite U] (Qa : QuadraticForm F U) :
    ∑ t : F, (valCount Qa t : ℝ) = Nat.card U := by
  classical
  have e : (Σ t : F, {x : U // Qa x = t}) ≃ U :=
    { toFun := fun p => p.2.1
      invFun := fun x => ⟨Qa x, x, rfl⟩
      left_inv := fun p => by rcases p with ⟨t, x, rfl⟩; rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]
  push_cast
  rfl

/-- **The count for a space with zero radical**: with $m$ the Witt index and $U_a$ the anisotropic part
($\dim U_a = w \le 2$), $a(t, Q) = q^{u-1} + q^m(a(t, U_a) - q^{w-1})$. -/
theorem exists_valCount_formula (Q : QuadraticForm F V) (hQ : Q.radical = ⊥) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module F U) (_ : FiniteDimensional F U) (Qa : QuadraticForm F U),
      Qa.Anisotropic ∧ finrank F U ≤ 2 ∧ finrank F V = 2 * QuadraticForm.wittIndex Q + finrank F U ∧
      ∀ t : F, (valCount Q t : ℝ) =
        (Nat.card F : ℝ) ^ ((finrank F V : ℤ) - 1) + (Nat.card F : ℝ) ^ QuadraticForm.wittIndex Q *
          (valCount Qa t - (Nat.card F : ℝ) ^ ((finrank F U : ℤ) - 1)) := by
  obtain ⟨U, _, _, _, Qa, ha, h⟩ := QuadraticForm.wittIndex_spec Q hQ
  refine ⟨U, inferInstance, inferInstance, inferInstance, Qa, ha, finrank_le_two_of_anisotropic Qa ha, ?_,
    fun t => valCount_wittDecomp Q Qa _ h t⟩
  obtain ⟨e⟩ := h
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype]
  simp [Module.finrank_prod]
  ring

/-- $\sum_{z \in F} f(z) = f(0) + \sum_{z \ne 0} f(z)$, with $\#\{z \ne 0\} = q - 1$ for constant $f$ off $0$. -/
theorem sum_split_zero [Fintype F] (f : F → ℝ) (c : ℝ) (hf : ∀ z, z ≠ 0 → f z = c) :
    ∑ z, f z = f 0 + (Nat.card F - 1) * c := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  rw [Finset.sum_congr rfl fun z hz => hf z (Finset.ne_of_mem_erase hz), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have h1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  rw [Nat.cast_sub h1, Nat.cast_one]

/-- **An anisotropic plane takes every nonzero value $q + 1$ times**: $a(t, U_a) = q + 1$ for $t \ne 0$
(Kitaoka obtains this from $U_a \cong (F', N)$, Proposition 1.3.1). -/
theorem valCount_aniso_two {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (Qa : QuadraticForm F U) (ha : Qa.Anisotropic) (h2 : finrank F U = 2) {t : F} (ht : t ≠ 0) :
    (valCount Qa t : ℝ) = Nat.card F + 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Finite U := Module.finite_of_finite F
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  have hq1 : (1 : ℝ) < Nat.card F := by exact_mod_cast Finite.one_lt_card
  have hcardU : (Nat.card U : ℝ) = (Nat.card F : ℝ) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), h2]; push_cast; rfl
  by_cases hc : ringChar F = 2
  · -- characteristic 2: every element is a square, so `a(t)` does not depend on `t ≠ 0`
    have hconst : ∀ z : F, z ≠ 0 → (valCount Qa z : ℝ) = valCount Qa 1 := by
      intro z hz
      obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hc z
      have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hz hs
      have := valCount_smul_sq Qa 1 hs0
      rw [mul_one] at this
      rw [hs, ← pow_two, this]
    have hsum := sum_valCount Qa
    rw [sum_split_zero _ _ hconst, valCount_zero_of_anisotropic Qa ha, hcardU] at hsum
    rw [hconst t ht]
    have : ((Nat.card F : ℝ) - 1) * valCount Qa 1 = ((Nat.card F : ℝ) - 1) * (Nat.card F + 1) := by
      push_cast at hsum; linarith [hsum]
    exact mul_left_cancel₀ (by linarith) this
  · -- characteristic `≠ 2`: count the zeros of the ternary space `U_a ⊥ ⟨-t⟩` in two ways
    have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hc
    let P : QuadraticForm F (U × F) := Qa.prod ((-t) • QuadraticMap.sq)
    have hP : ∀ x : U × F, P x = Qa x.1 - t * (x.2 * x.2) := fun x => by
      simp [P, QuadraticMap.prod_apply, sub_eq_add_neg]
    have hrad : P.radical = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [QuadraticForm.Witt.mem_radical_iff, QuadraticForm.Witt.mem_ker_polarBilin] at hx
      have h1 := hx.2 (0, 1)
      simp only [polar, hP, Prod.fst_add, Prod.snd_add, add_zero, map_zero] at h1
      have hz : x.2 = 0 := by
        have : -(2 * t) * x.2 = 0 := by linear_combination h1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (neg_eq_zero.1 h) (mul_ne_zero h2F ht)
        · exact h
      have hu : x.1 = 0 := ha _ (by have := hx.1; rw [hP, hz] at this; simpa using this)
      exact (Submodule.mem_bot F).2 (Prod.ext hu hz)
    obtain ⟨U', _, _, _, Qa', ha', hw', hdim', hform⟩ := exists_valCount_formula P hrad
    have h3 : finrank F (U × F) = 3 := by rw [Module.finrank_prod, h2, Module.finrank_self]
    have hm : QuadraticForm.wittIndex P = 1 ∧ finrank F U' = 1 := by omega
    have hzeros : (valCount P 0 : ℝ) = (Nat.card F : ℝ) ^ 2 := by
      rw [hform, h3, hm.1, hm.2, valCount_zero_of_anisotropic Qa' ha']
      norm_num
    -- the other count: fibre over `z`
    have e : {x : U × F // P x = 0} ≃ Σ z : F, {u : U // Qa u = z ^ 2 * t} :=
      (Equiv.subtypeEquiv (Equiv.prodComm U F) (fun x => by
        rw [hP]; simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
        constructor <;> intro h <;> linear_combination h)).trans
        (Equiv.subtypeProdEquivSigmaSubtype (fun (z : F) (u : U) => Qa u = z ^ 2 * t))
    have hcount : (valCount P 0 : ℝ) = ∑ z : F, (valCount Qa (z ^ 2 * t) : ℝ) := by
      rw [valCount, Nat.card_congr e, Nat.card_sigma]; push_cast; rfl
    have hconst : ∀ z : F, z ≠ 0 → (valCount Qa (z ^ 2 * t) : ℝ) = valCount Qa t := fun z hz => by
      rw [valCount_smul_sq Qa t hz]
    rw [sum_split_zero _ _ hconst] at hcount
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      valCount_zero_of_anisotropic Qa ha, Nat.cast_one] at hcount
    rw [hzeros] at hcount
    have : ((Nat.card F : ℝ) - 1) * valCount Qa t = ((Nat.card F : ℝ) - 1) * (Nat.card F + 1) := by
      linarith [hcount]
    exact mul_left_cancel₀ (by linarith) this

/-- **Kitaoka 1993, Lemma 1.3.1** (p. 15): for a regular quadratic space $U$ of dimension $u$ over $F = \mathbb F_q$,
$$a(0, U) = q^{u-1} - \chi(U)q^{u/2-1} + \chi(U)q^{u/2}.$$
(For odd $u$, $\chi(U) = 0$ and $u/2$ is immaterial; here it is the integer part.) -/
@[kb "kitaoka1993" "§1.3, Lemma 1.3.1, p. 15"]
theorem lemma131 {u : ℕ} (Q : QuadraticForm F (Fin u → F)) (hQ : (polarBilin Q).Nondegenerate) :
    (valCount Q 0 : ℝ) = (Nat.card F : ℝ) ^ ((u : ℤ) - 1) -
      chiV Q * (Nat.card F : ℝ) ^ (((u / 2 : ℕ) : ℤ) - 1) + chiV Q * (Nat.card F : ℝ) ^ (u / 2) := by
  obtain ⟨U, _, _, _, Qa, ha, hw, hdim, hform⟩ :=
    exists_valCount_formula Q (QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ)
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  rw [hform, valCount_zero_of_anisotropic Qa ha, Module.finrank_fin_fun]
  rw [Module.finrank_fin_fun] at hdim
  set m := QuadraticForm.wittIndex Q with hm
  have hcases : finrank F U = 0 ∨ finrank F U = 1 ∨ finrank F U = 2 := by omega
  rcases hcases with hw0 | hw1 | hw2
  · have hu2 : u / 2 = m := by omega
    have hchi : chiV Q = 1 := by
      simp only [chiV]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨m, by omega⟩), if_pos (by rw [← hm]; omega)]
    rw [hchi, hw0, hu2]
    simp only [Nat.cast_zero, zero_sub, zpow_neg_one, zpow_sub_one₀ hq.ne', zpow_natCast, Nat.cast_one]
    ring
  · have hchi : chiV Q = 0 := by
      simp only [chiV]; rw [if_pos ⟨m, by omega⟩]
    rw [hchi, hw1]
    simp
  · have hu2 : u / 2 = m + 1 := by omega
    have hchi : chiV Q = -1 := by
      simp only [chiV]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨m + 1, by omega⟩), if_neg (by rw [← hm]; omega)]
    rw [hchi, hw2, hu2]
    simp only [Nat.cast_ofNat, zpow_sub_one₀ hq.ne', zpow_natCast, Nat.cast_add, Nat.cast_one]
    simp only [zpow_add_one₀ hq.ne', zpow_add_one₀ (pow_ne_zero 2 hq.ne'), zpow_natCast]
    field_simp
    ring

/-- **Kitaoka 1993, Lemma 1.3.2** (p. 15), the count: for a regular quadratic space $U$ of even dimension $u$ over
$F = \mathbb F_q$ and $t \in F^\times$, $a(t, U) = q^{u-1}(1 - \chi(U)q^{-u/2})$. (Kitaoka's first assertion, an
automorphism $f$ of the space with $Q(f(x)) = tQ(x)$, is not formalized; it is not needed for the count.) -/
@[kb "kitaoka1993" "§1.3, Lemma 1.3.2, p. 15"]
theorem lemma132 {u : ℕ} (Q : QuadraticForm F (Fin u → F)) (hQ : (polarBilin Q).Nondegenerate) (hu : Even u)
    {t : F} (ht : t ≠ 0) :
    (valCount Q t : ℝ) =
      (Nat.card F : ℝ) ^ ((u : ℤ) - 1) * (1 - chiV Q * (Nat.card F : ℝ) ^ (-((u / 2 : ℕ) : ℤ))) := by
  obtain ⟨U, _, _, _, Qa, ha, hw, hdim, hform⟩ :=
    exists_valCount_formula Q (QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ)
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  rw [hform, Module.finrank_fin_fun]
  rw [Module.finrank_fin_fun] at hdim
  set m := QuadraticForm.wittIndex Q with hm
  obtain ⟨k, hk⟩ := hu
  have hcases : finrank F U = 0 ∨ finrank F U = 2 := by omega
  rcases hcases with hw0 | hw2
  · have hu2 : u / 2 = m := by omega
    have hchi : chiV Q = 1 := by
      simp only [chiV]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨k, hk⟩), if_pos (by rw [← hm]; omega)]
    have hsub : Subsingleton U := Module.finrank_zero_iff.1 hw0
    have h0 : valCount Qa t = 0 := by
      rw [valCount, Nat.card_eq_zero]
      left
      exact ⟨fun x => ht (by rw [← x.2, Subsingleton.elim x.1 0, map_zero])⟩
    rw [hchi, hw0, hu2, h0]
    have hu' : (u : ℤ) = 2 * m := by omega
    rw [hu']
    simp only [Nat.cast_zero, zero_sub, zpow_neg_one, zpow_sub_one₀ hq.ne', zpow_neg, zpow_mul, zpow_natCast]
    field_simp
    ring
  · have hu2 : u / 2 = m + 1 := by omega
    have hchi : chiV Q = -1 := by
      simp only [chiV]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨k, hk⟩), if_neg (by rw [← hm]; omega)]
    rw [hchi, hw2, hu2, valCount_aniso_two Qa ha hw2 ht]
    have hu' : (u : ℤ) = ((2 * (m + 1) : ℕ) : ℤ) := by omega
    rw [hu', zpow_sub_one₀ hq.ne', zpow_natCast, zpow_neg, zpow_natCast,
      show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num, zpow_one]
    field_simp
    ring

end FqCount

end QuadFormsKB.Kitaoka
