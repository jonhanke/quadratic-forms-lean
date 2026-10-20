/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryBadDVR
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# The self-density of $\langle u\rangle\perp\pi T$ at a dyadic prime

**Layer:** a complete discrete valuation ring $R$ with finite residue field, uniformizer $\pi$, $\pi \mid 2$ (dyadic).

Let $u$ be a unit and $T$ a binary form with $\det H_T$ a unit whose reduction $\bar T$ is anisotropic. Put
$Q = \langle u\rangle\perp\pi T$ and $Q' = \langle\pi u\rangle\perp T$, so that $Q\circ P = \pi Q'$ for $P = \mathrm{diag}(\pi, 1, 1)$. This is
the shape of the trace-zero part of the maximal order of a quaternion division algebra over a dyadic field. We prove
$$\beta_\pi(Q, Q) = 4q^{e+2}(q+1), \qquad \pi^e \,\|\, 2 \qquad (\texttt{localDensityForm\_ram\_dyadic}).$$

*Proof.* Orbit–stabilizer for the frame $(e_1, e_2)$ in $O(Q \bmod \pi^k)$.
* The stabilizer is $\{x : ux^2 = u\}\times(\pi^{k-1}R/\pi^k)^2$ (`card_stab_ramFrame`).
* The orbit is every representation of $\pi T$ mod $\pi^k$ (`ramFrame_orbit_iff`): such a representation has first row
  divisible by $\pi$ ($\bar T$-anisotropy is not even needed here, only that $u$ is a unit), so it is $PZ$ with $Q'\circ Z \equiv T$
  mod $\pi^{k-1}$; Hensel ($T$ unimodular) and the exact frame lemma for $Q'$ (`exists_isometry_frame`) give an exact isometry
  $X'$ of $Q'$, and $X = PX'P^{-1}$ is integral because $\bar T$ is anisotropic; finally the frame may be moved by
  $\pi^{k-1}P(\cdot)$ without changing $Q\circ X$ mod $\pi^k$.
* Representations of $\pi T$ by $Q$ mod $\pi^k$ correspond to representations of $T$ by $Q'$ mod $\pi^{k-1}$:
  $A_{\pi^k}(Q, \pi T) = q^4A_{\pi^{k-1}}(Q', T)$ (`repCountForm_ram_piT`).
* $\beta_\pi(Q', T) = q^{-3}\cdot q^2|O(\bar T)| = 2(q+1)/q$, with $|O(\bar T)| = 2(q+1)$ for an anisotropic binary form in
  characteristic $2$ (`card_orth_binary_char2`, no Witt theorem: the second column is found explicitly from the first).

Sources: Kitaoka 1993, §5.6 [unverified] (densities); the counting is elementary. Indices are 0-based.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

/-! ### The orthogonal group of an anisotropic binary form in characteristic $2$ -/

section CharTwoBinary

variable {K : Type*} [Field K] [Finite K]

theorem eval_binary {A : Type*} [CommRing A] (T : QuadForm A 2) (x : Fin 2 → A) :
    T.eval x = T.coeff 0 0 * x 0 * x 0 + T.coeff 0 1 * x 0 * x 1 + T.coeff 1 1 * x 1 * x 1 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]

theorem bil_binary {A : Type*} [CommRing A] (T : QuadForm A 2) (x y : Fin 2 → A) :
    x ⬝ᵥ (T.hessian *ᵥ y) = 2 * T.coeff 0 0 * x 0 * y 0 + T.coeff 0 1 * (x 0 * y 1 + x 1 * y 0) +
      2 * T.coeff 1 1 * x 1 * y 1 := by
  have h10 : T.coeff 1 0 = 0 := T.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.hessian, dotProduct, mulVec, Fin.sum_univ_two, h10]
  ring

/-- All nonzero values of an anisotropic binary form are taken equally often when squaring is onto. -/
theorem card_fiber_eq_of_sq (h2 : (2 : K) = 0) (T : QuadForm K 2) {a t : K} (ha : a ≠ 0) (ht : t ≠ 0) :
    Nat.card {x : Fin 2 → K // T.eval x = t} = Nat.card {x : Fin 2 → K // T.eval x = a} := by
  obtain ⟨l, hl⟩ := (sq_bijective_of_two_eq_zero h2).2 (t / a)
  have hl' : l ^ 2 = t / a := hl
  have hl0 : l ≠ 0 := by
    rintro rfl; simp at hl'; exact div_ne_zero ht ha hl'.symm
  have hsm : ∀ (c : K) (x : Fin 2 → K), T.eval (c • x) = c ^ 2 * T.eval x := by
    intro c x; rw [eval_binary, eval_binary]; simp; ring
  refine Nat.card_congr
    { toFun := fun x => ⟨l⁻¹ • x.1, by rw [hsm, x.2, inv_pow, hl']; field_simp⟩
      invFun := fun x => ⟨l • x.1, by rw [hsm, x.2, hl']; field_simp⟩
      left_inv := fun x => Subtype.ext (by simp [smul_smul, hl0])
      right_inv := fun x => Subtype.ext (by simp [smul_smul, hl0]) }

/-- **An anisotropic binary form in characteristic $2$ takes each nonzero value $|K| + 1$ times.** -/
theorem card_fiber_aniso_char2 (h2 : (2 : K) = 0) (T : QuadForm K 2) (haniso : ∀ x, T.eval x = 0 → x = 0)
    {a : K} (ha : a ≠ 0) : Nat.card {x : Fin 2 → K // T.eval x = a} = Nat.card K + 1 := by
  classical
  have := Fintype.ofFinite K
  set N := Nat.card {x : Fin 2 → K // T.eval x = a} with hN
  -- count the nonzero vectors by their value
  have e : {x : Fin 2 → K // x ≠ 0} ≃ Σ t : {t : K // t ≠ 0}, {x : Fin 2 → K // T.eval x = t.1} :=
    { toFun := fun x => ⟨⟨T.eval x.1, fun h => x.2 (haniso _ h)⟩, ⟨x.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, fun h => p.1.2 (by rw [← p.2.2, h]; simp [QuadForm.eval, QuadForm.evalIn])⟩
      left_inv := fun x => rfl
      right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2) rfl }
  have h1 := Nat.card_congr e
  rw [Nat.card_sigma] at h1
  have hc : ∀ t : {t : K // t ≠ 0}, Nat.card {x : Fin 2 → K // T.eval x = t.1} = N :=
    fun t => card_fiber_eq_of_sq h2 T ha t.2
  simp_rw [hc] at h1
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  have hne : Nat.card {x : Fin 2 → K // x ≠ 0} = Nat.card K ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun,
      Fintype.card_fin, Nat.card_eq_fintype_card]
  have hne' : Fintype.card {t : K // t ≠ 0} = Nat.card K - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Nat.card_eq_fintype_card]
  rw [hne, hne'] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 2 := ⟨Nat.card K - 2, by omega⟩
    rw [hm, show m + 2 - 1 = m + 1 by omega]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [hq2] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h1).symm

/-- **The second column given the first** ($2 = 0$, $T$ anisotropic with $c_{01} \ne 0$): for $T(x) = c_{00}$, exactly two $y$
satisfy $T(y) = c_{11}$ and $B_T(x, y) = c_{01}$, namely $y^*$ (multiplication by $x$ in the quadratic algebra of $T$, applied to
the second basis vector) and $y^* + (c_{01}/c_{00})x$. -/
theorem card_second_col_char2 (h2 : (2 : K) = 0) (T : QuadForm K 2) (haniso : ∀ x, T.eval x = 0 → x = 0)
    (hb : T.coeff 0 1 ≠ 0) (x : Fin 2 → K) (hx : T.eval x = T.coeff 0 0) :
    Nat.card {y : Fin 2 → K // T.eval y = T.coeff 1 1 ∧ x ⬝ᵥ (T.hessian *ᵥ y) = T.coeff 0 1} = 2 := by
  classical
  set a := T.coeff 0 0 with ha_def
  set b := T.coeff 0 1 with hb_def
  set c := T.coeff 1 1 with hc_def
  have ha : a ≠ 0 := by
    intro h0
    have := haniso ![1, 0] (by rw [eval_binary]; simp [← ha_def, h0])
    simpa using congrFun this 0
  have hx0 : x ≠ 0 := by
    rintro rfl; apply ha; rw [← hx]; simp [QuadForm.eval, QuadForm.evalIn]
  have hneg : ∀ z : K, -z = z := fun z => by linear_combination (-z) * h2
  rw [eval_binary] at hx
  set ys : Fin 2 → K := ![-(c / a) * x 1, x 0 + (b / a) * x 1] with hys
  have hBs : x 0 * ys 1 + x 1 * ys 0 = 1 := by
    simp only [hys, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    linear_combination hx - (c * x 1 * x 1) * h2
  have hval : ∀ t : K, T.eval (ys + t • x) = c + t * b + t ^ 2 * a := by
    intro t
    rw [eval_binary]
    simp only [hys, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, ← ha_def, ← hb_def, ← hc_def]
    field_simp
    linear_combination (a * c + t * b * a + t ^ 2 * a ^ 2) * hx
  have hcond : ∀ y : Fin 2 → K, (T.eval y = c ∧ x ⬝ᵥ (T.hessian *ᵥ y) = b) ↔
      (y = ys ∨ y = ys + (b / a) • x) := by
    intro y
    have hBy : x ⬝ᵥ (T.hessian *ᵥ y) = b * (x 0 * y 1 + x 1 * y 0) := by
      rw [bil_binary, h2]; ring
    rw [hBy]
    constructor
    · rintro ⟨hTy, hB⟩
      have hB' : x 0 * (y 1 - ys 1) + x 1 * (y 0 - ys 0) = 0 := by
        have : b * (x 0 * y 1 + x 1 * y 0) = b * 1 := by rw [mul_one]; exact hB
        have h1 := mul_left_cancel₀ hb this
        linear_combination h1 - hBs
      obtain ⟨t, ht⟩ : ∃ t : K, y = ys + t • x := by
        by_cases h0 : x 0 = 0
        · have h1 : x 1 ≠ 0 := fun h1 => hx0 (by ext i; fin_cases i <;> simp [h0, h1])
          refine ⟨(y 1 - ys 1) / x 1, ?_⟩
          have hy0 : y 0 - ys 0 = 0 := by
            simp only [h0, zero_mul, zero_add] at hB'
            rcases mul_eq_zero.mp hB' with h | h
            · exact absurd h h1
            · exact h
          ext i; fin_cases i
          · simp [h0]; linear_combination hy0
          · simp; field_simp; ring
        · refine ⟨(y 0 - ys 0) / x 0, ?_⟩
          ext i; fin_cases i
          · simp; field_simp; ring
          · simp
            field_simp
            linear_combination hB' - (x 1 * (y 0 - ys 0)) * h2
      subst ht
      have hq : t * (b + t * a) = 0 := by linear_combination hTy - hval t
      rcases mul_eq_zero.mp hq with h | h
      · left; rw [h, zero_smul, add_zero]
      · right
        have : t = b / a := by
          field_simp; linear_combination h - b * h2
        rw [this]
    · rintro (rfl | rfl)
      · refine ⟨by simpa using hval 0, by rw [hBs, mul_one]⟩
      · refine ⟨?_, ?_⟩
        · rw [hval]
          have e : (b / a) ^ 2 * a = b / a * b := by field_simp
          rw [e]; linear_combination (b / a * b) * h2
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination b * hBs + (b * b / a * x 0 * x 1) * h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcond)]
  have hne : ys ≠ ys + (b / a) • x := by
    intro h
    have h' : (b / a) • x = 0 := by
      have := congrArg (· - ys) h; simpa using this.symm
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact div_ne_zero hb ha h''
    · exact hx0 h''
  rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun y => y ∈ ({ys, ys + (b / a) • x} : Set (Fin 2 → K)))
    fun y => by simp), Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **$|O(T)| = 2(|K| + 1)$ for an anisotropic binary form in characteristic $2$** (with $c_{01} \ne 0$, i.e. $\det H_T \ne 0$). -/
theorem card_orth_binary_char2 (h2 : (2 : K) = 0) (T : QuadForm K 2) (haniso : ∀ x, T.eval x = 0 → x = 0)
    (hb : T.coeff 0 1 ≠ 0) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // T.compMat X = T} = 2 * (Nat.card K + 1) := by
  classical
  have := Fintype.ofFinite K
  have ha : T.coeff 0 0 ≠ 0 := by
    intro h0
    have := haniso ![1, 0] (by rw [eval_binary]; simp [h0])
    simpa using congrFun this 0
  have h10 : T.coeff 1 0 = 0 := T.upper (show (0 : Fin 2) < 1 by decide)
  have hcond : ∀ X : Matrix (Fin 2) (Fin 2) K, T.compMat X = T ↔
      (T.eval (fun l => X l 0) = T.coeff 0 0 ∧ (T.eval (fun l => X l 1) = T.coeff 1 1 ∧
        (fun l => X l 0) ⬝ᵥ (T.hessian *ᵥ fun l => X l 1) = T.coeff 0 1)) := by
    intro X
    constructor
    · intro h
      have c00 := congrArg (fun S : QuadForm K 2 => S.coeff 0 0) h
      have c11 := congrArg (fun S : QuadForm K 2 => S.coeff 1 1) h
      have c01 := congrArg (fun S : QuadForm K 2 => S.coeff 0 1) h
      simp only [compMat_coeff] at c00 c11 c01
      exact ⟨by simpa using c00, by simpa using c11, by simpa using c01⟩
    · rintro ⟨h0, h1, h01⟩
      refine ext_upper fun i j hij => ?_
      fin_cases i <;> fin_cases j
      · simpa [compMat_coeff] using h0
      · simpa [compMat_coeff] using h01
      · exact absurd hij (by decide)
      · simpa [compMat_coeff] using h1
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcond)]
  let e : {X : Matrix (Fin 2) (Fin 2) K // T.eval (fun l => X l 0) = T.coeff 0 0 ∧ (T.eval (fun l => X l 1) =
      T.coeff 1 1 ∧ (fun l => X l 0) ⬝ᵥ (T.hessian *ᵥ fun l => X l 1) = T.coeff 0 1)} ≃
      Σ x : {x : Fin 2 → K // T.eval x = T.coeff 0 0},
        {y : Fin 2 → K // T.eval y = T.coeff 1 1 ∧ x.1 ⬝ᵥ (T.hessian *ᵥ y) = T.coeff 0 1} :=
    { toFun := fun X => ⟨⟨fun l => X.1 l 0, X.2.1⟩, ⟨fun l => X.1 l 1, X.2.2⟩⟩
      invFun := fun p => ⟨Matrix.of fun l j => if j = 0 then p.1.1 l else p.2.1 l, ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun X => Subtype.ext (by ext l j; fin_cases j <;> rfl)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun x : {x : Fin 2 → K // T.eval x = T.coeff 0 0} => card_second_col_char2 h2 T haniso hb x.1 x.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    card_fiber_aniso_char2 h2 T haniso ha, mul_comm]

/-- $(\langle 0\rangle\perp T)\circ Y = T\circ Y'$, $Y'$ the lower $2\times2$ block of $Y \in M_{3\times2}$. -/
theorem splitForm_zero_compMat {A : Type*} [CommRing A] (T : QuadForm A 2) (Y : Matrix (Fin 3) (Fin 2) A) :
    (splitForm 0 T).compMat Y = T.compMat (Matrix.of fun (i : Fin 2) (j : Fin 2) => Y i.succ j) :=
  eq_of_eval_eq fun w => by
    rw [eval_compMat, eval_compMat, ← Fin.cons_self_tail (Y *ᵥ w), eval_splitForm_cons]
    simp only [zero_mul, zero_add]
    congr 1

/-- $\#\{Y \in M_{3\times2}(K) : (\langle 0\rangle\perp T)\circ Y = T\} = |K|^2\cdot2(|K| + 1)$ for $T$ anisotropic, $2 = 0$. -/
theorem card_reps_splitForm_zero_char2 (h2 : (2 : K) = 0) (T : QuadForm K 2) (haniso : ∀ x, T.eval x = 0 → x = 0)
    (hb : T.coeff 0 1 ≠ 0) :
    Nat.card {Y : Matrix (Fin 3) (Fin 2) K // (splitForm 0 T).compMat Y = T} =
      Nat.card K ^ 2 * (2 * (Nat.card K + 1)) := by
  simp_rw [splitForm_zero_compMat]
  let e : {Y : Matrix (Fin 3) (Fin 2) K // T.compMat (Matrix.of fun (i : Fin 2) (j : Fin 2) => Y i.succ j) = T} ≃
      (Fin 2 → K) × {X : Matrix (Fin 2) (Fin 2) K // T.compMat X = T} :=
    { toFun := fun Y => (fun j => Y.1 0 j, ⟨Matrix.of fun i j => Y.1 i.succ j, Y.2⟩)
      invFun := fun p => ⟨Matrix.of fun i j => Fin.cases (p.1 j) (fun i' => p.2.1 i' j) i, by
        convert p.2.2 using 2
        ext i j; rfl⟩
      left_inv := fun Y => Subtype.ext (by ext i j; refine Fin.cases rfl (fun i => rfl) i)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_orth_binary_char2 h2 T haniso hb, Nat.card_fun, Nat.card_fin]

end CharTwoBinary

/-! ### The forms $Q = \langle u\rangle\perp\pi T$, $Q' = \langle\pi u\rangle\perp T$ and the frame stabilizer -/

section Forms

variable {A : Type*} [CommRing A]

theorem eval_smul_form_rd {n : ℕ} (c : A) (Q : QuadForm A n) (x : Fin n → A) : (c • Q).eval x = c * Q.eval x :=
  eval_of_coeff_mul c (fun i j => by simp [smul_coeff]) x

/-- $Q\circ\mathrm{diag}(p, 1, 1) = p\,Q'$ for $Q = \langle a\rangle\perp pT$, $Q' = \langle pa\rangle\perp T$. -/
theorem splitForm_smul_compMat_corner (a p : A) (T : QuadForm A 2) :
    (splitForm a (p • T)).compMat (cornerMat p 1) = p • splitForm (p * a) T :=
  eq_of_eval_eq fun x => by
    rw [eval_compMat, eval_smul_form_rd, ← Fin.cons_self_tail x, cornerMat_mulVec, one_mulVec, eval_splitForm_cons,
      eval_splitForm_cons, eval_smul_form_rd]
    ring

theorem hessian_transpose_gen {n : ℕ} (Q : QuadForm A n) : Q.hessianᵀ = Q.hessian := by
  simp only [QuadForm.hessian, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem mul_eval_eq_zero {n : ℕ} (p : A) (T : QuadForm A n) {s : Fin n → A} (hs : ∀ i, p * s i = 0) :
    p * T.eval s = 0 := by
  have h0 : p • s = 0 := funext hs
  rw [eval_eq_dotProduct', ← smul_eq_mul, ← smul_dotProduct, h0, zero_dotProduct]

theorem mul_bil_eq_zero {n : ℕ} (p : A) (H : Matrix (Fin n) (Fin n) A) (y : Fin n → A) {s : Fin n → A}
    (hs : ∀ i, p * s i = 0) : p * ((H *ᵥ y) ⬝ᵥ s) = 0 := by
  have h0 : p • s = 0 := funext hs
  rw [← smul_eq_mul, ← dotProduct_smul, h0, dotProduct_zero]

/-- The matrix $(\,(x, s)\,|\,e_1\,e_2)$. -/
def stabMat (x : A) (s : Fin 2 → A) : Matrix (Fin 3) (Fin 3) A :=
  Matrix.of fun i j => Fin.cases ((Fin.cons x s : Fin 3 → A) i) (fun j' => frameMat A 2 i j') j

theorem stabMat_mulVec (x : A) (s : Fin 2 → A) (t : A) (y : Fin 2 → A) :
    stabMat x s *ᵥ (Fin.cons t y : Fin 3 → A) = Fin.cons (x * t) (t • s + y) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [stabMat, mulVec, dotProduct, Fin.sum_univ_succ, frameMat]
  · simp [stabMat, mulVec, dotProduct, Fin.sum_univ_succ, frameMat, Fin.succ_inj]
    fin_cases i <;> simp <;> ring

theorem stabMat_frame (x : A) (s : Fin 2 → A) : stabMat x s * frameMat A 2 = frameMat A 2 := by
  ext i j
  rw [mul_frameMat_apply]
  rfl

/-- **The frame stabilizer for $\langle a\rangle\perp pT$** ($\det H_T$ a unit): $X = (c\,|\,e_1\,e_2)$ with $ac_0^2 = a$ and $pc_1 = pc_2 = 0$. -/
def stabRamEquiv (a p : A) (T : QuadForm A 2) (hT : IsUnit T.hessian.det) :
    {X : Matrix (Fin 3) (Fin 3) A // (splitForm a (p • T)).compMat X = splitForm a (p • T) ∧
        X * frameMat A 2 = frameMat A 2} ≃ {x : A // a * x * x = a} × {s : Fin 2 → A // ∀ i, p * s i = 0} where
  toFun X := by
    have hc : ∀ (i : Fin 3) (j : Fin 2), X.1 i j.succ = frameMat A 2 i j := fun i j => by
      rw [← mul_frameMat_apply X.1 i j, X.2.2]
    have hs : ∀ i : Fin 2, p * X.1 i.succ 0 = 0 := by
      have hs0 : (p • fun i : Fin 2 => X.1 i.succ 0) ᵥ* T.hessian = 0 := by
        ext j
        have h1 := compMat_coeff_zero_succ a (p • T) X.1 hc j
        rw [X.2.1] at h1
        have hH : (p • T).hessian = p • T.hessian := by ext; simp [hessian, smul_coeff]; ring
        rw [hH, vecMul_smul] at h1
        simp only [splitForm_coeff, cornerMat_zero_succ] at h1
        rw [smul_vecMul]; simpa using h1.symm
      have := congrArg (· ᵥ* T.hessian⁻¹) hs0
      have h' : (p • fun i : Fin 2 => X.1 i.succ 0) = 0 := by
        simpa [vecMul_vecMul, mul_nonsing_inv _ hT] using this
      exact fun i => by simpa using congrFun h' i
    refine ⟨⟨X.1 0 0, ?_⟩, ⟨fun i => X.1 i.succ 0, hs⟩⟩
    have h00 := congrArg (fun S : QuadForm A 3 => S.coeff 0 0) X.2.1
    simp only [compMat_coeff, le_refl, if_true] at h00
    rw [show (fun l => X.1 l 0) = Fin.cons (X.1 0 0) (fun i : Fin 2 => X.1 i.succ 0) from
      (Fin.cons_self_tail _).symm, eval_splitForm_cons, eval_smul_form_rd, mul_eval_eq_zero p T hs, add_zero] at h00
    simpa [splitForm_coeff] using h00
  invFun xs := ⟨stabMat xs.1.1 xs.2.1, by
      refine eq_of_eval_eq fun w => ?_
      rw [eval_compMat, ← Fin.cons_self_tail w, stabMat_mulVec, eval_splitForm_cons, eval_splitForm_cons,
        eval_smul_form_rd, eval_smul_form_rd, add_comm (w 0 • xs.2.1), eval_add_smul_gen, mul_add, mul_add,
        mul_left_comm p, mul_bil_eq_zero p _ _ xs.2.2, mul_left_comm p, mul_eval_eq_zero p T xs.2.2]
      have := xs.1.2
      linear_combination (w 0 * w 0) * this, stabMat_frame _ _⟩
  left_inv X := by
    have hc : ∀ (i : Fin 3) (j : Fin 2), X.1 i j.succ = frameMat A 2 i j := fun i j => by
      rw [← mul_frameMat_apply X.1 i j, X.2.2]
    apply Subtype.ext
    ext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases rfl (fun i => rfl) i
    · rw [hc]; rfl
  right_inv xs := rfl

end Forms

/-! ### Counts over $R/\pi^k$ -/

section DVRCounts

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]

/-- The kernel of $R/\pi^{k+1} \to R/\pi^k$ has $q$ elements. -/
theorem card_ker_factor {π : R} (hπ : Irreducible π) (k : ℕ) :
    Nat.card (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k)) :
      Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k})).toAddMonoidHom.ker = q R := by
  have := finite_quot_pow π hπ (k + 1)
  have hle : Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k))
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle).toAddMonoidHom :=
    Ideal.Quotient.factor_surjective hle
  have h2 := card_preimage_eq (Ideal.Quotient.factor hle).toAddMonoidHom Set.univ (fun Y _ => hsurj Y)
  simp only [Set.preimage_univ, Nat.card_univ] at h2
  rw [card_quot_pow π hπ, card_quot_pow π hπ] at h2
  have hq : 0 < q R ^ k := pow_pos q_pos _
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← pow_succ', h2]

/-- **The annihilator of $\pi$ in $R/\pi^k$ has $q$ elements** ($k \ge 1$). -/
theorem card_ann_pi {π : R} (hπ : Irreducible π) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card {t : R ⧸ Ideal.span {π ^ k} // Ideal.Quotient.mk _ π * t = 0} = q R := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hle : Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k))
  rw [← card_ker_factor hπ k]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Ideal.Quotient.factor_mk,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left hπ.ne_zero]

/-- **$\beta_\pi(\langle\pi u\rangle\perp T, T) = 2(q+1)/q$ at a dyadic prime** for $T$ unimodular with $\bar T$ anisotropic: the count mod $\pi$
is $q^2|O(\bar T)| = q^2\cdot2(q+1)$ (`card_reps_splitForm_zero_char2`). -/
theorem localDensityForm_piU_T {π : R} (hπ : Irreducible π) (h2π : π ∣ 2) (u : R) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm (splitForm (π * u) T) T π = 2 * ((q R : ℝ) + 1) / q R := by
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT (by norm_num)]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have hfin := finite_quot_pow π hπ 1
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have hmk0 : ∀ x : R, mk x = 0 ↔ π ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  have h2 : (2 : R ⧸ Ideal.span {π ^ 1}) = 0 := by rw [← map_ofNat mk 2, hmk0]; exact h2π
  have hπu : mk (π * u) = 0 := (hmk0 _).2 (dvd_mul_right _ _)
  have hanisoK : ∀ x : Fin 2 → R ⧸ Ideal.span {π ^ 1}, (T.map mk).eval x = 0 → x = 0 := by
    intro x hx
    choose f hf using fun i => Ideal.Quotient.mk_surjective (x i)
    have hxf : x = fun i => mk (f i) := funext fun i => (hf i).symm
    subst hxf
    have : mk (T.eval f) = 0 := by rw [← hx, eval_map_comp']
    have hd := haniso f ((hmk0 _).1 this)
    funext i; exact (hmk0 _).2 (hd i)
  have hb : (T.map mk).coeff 0 1 ≠ 0 := by
    intro h0
    have hdet : (T.map mk).hessian.det = mk T.hessian.det := by
      rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu := hT.map mk
    rw [← hdet] at hu
    have h10 : (T.map mk).coeff 1 0 = 0 := (T.map mk).upper (show (0 : Fin 2) < 1 by decide)
    have : (T.map mk).hessian.det = 0 := by
      simp only [hessian, det_fin_two, Matrix.add_apply, Matrix.transpose_apply, h0, h10]
      rw [show (T.map mk).coeff 0 0 + (T.map mk).coeff 0 0 = 2 * (T.map mk).coeff 0 0 by ring, h2]; ring
    rw [this] at hu; exact not_isUnit_zero hu
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  unfold repCountForm
  rw [map_splitForm, hπu, card_reps_splitForm_zero_char2 h2 _ hanisoK hb, hcard]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  push_cast
  field_simp

end DVRCounts

/-! ### Exact lifting: the frame orbit is every representation of $\pi T$ -/

section Orbit

variable {A : Type*} [CommRing A]

theorem smul_compMat_rd {n r : ℕ} (c : A) (S : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) :
    (c • S).compMat X = c • S.compMat X := by
  ext i j
  rw [compMat_coeff_of_coeff_mul c (Q := S) (fun a b => by simp [smul_coeff]) X i j]
  simp [smul_coeff]

/-- $(\mathrm{diag}(p, 1, 1)\,Z)_{ij}$. -/
theorem cornerMat_one_mul_apply_rd {r : ℕ} (p : A) (Z : Matrix (Fin 3) (Fin r) A) (i : Fin 3) (j : Fin r) :
    (cornerMat p (1 : Matrix (Fin 2) (Fin 2) A) * Z) i j = Fin.cases (p * Z 0 j) (fun i' => Z i'.succ j) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem cornerMat_one_mulVec (p : A) (v : Fin 3 → A) :
    cornerMat p (1 : Matrix (Fin 2) (Fin 2) A) *ᵥ v = Fin.cons (p * v 0) (Fin.tail v) := by
  conv_lhs => rw [← Fin.cons_self_tail v]
  rw [cornerMat_mulVec, one_mulVec]

theorem cornerMat_one_mul_frameMat (p : A) :
    cornerMat p (1 : Matrix (Fin 2) (Fin 2) A) * frameMat A 2 = frameMat A 2 := by
  ext i j
  rw [cornerMat_one_mul_apply_rd]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [frameMat, (Fin.succ_ne_zero j).symm]
  · rfl

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Cancelling $\mathrm{diag}(\pi, 1, 1)$:** $S\circ P = S'\circ P$ implies $S = S'$ ($\pi \ne 0$). -/
theorem compMat_corner_cancel {π : R} (hπ : π ≠ 0) {S S' : QuadForm R 3}
    (h : S.compMat (cornerMat π 1) = S'.compMat (cornerMat π 1)) : S = S' := by
  refine eq_of_eval_eq fun x => ?_
  have hx := congrArg (fun U : QuadForm R 3 => U.eval (Fin.cons (x 0) (π • Fin.tail x))) h
  simp only [eval_compMat, cornerMat_mulVec, one_mulVec] at hx
  have hv : (Fin.cons (π * x 0) (π • Fin.tail x) : Fin 3 → R) = π • x := by
    conv_rhs => rw [← Fin.cons_self_tail x]
    ext i; refine Fin.cases rfl (fun i => rfl) i
  rw [hv] at hx
  have hs : ∀ U : QuadForm R 3, U.eval (π • x) = π ^ 2 * U.eval x := fun U => by
    rw [eval_eq_dotProduct', eval_eq_dotProduct', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]; ring
  rw [hs, hs] at hx
  exact mul_left_cancel₀ (pow_ne_zero 2 hπ) hx

theorem dot_hessian_comm {n : ℕ} (S : QuadForm A n) (v w : Fin n → A) :
    v ⬝ᵥ (S.hessian *ᵥ w) = w ⬝ᵥ (S.hessian *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hessian_transpose_gen, dotProduct_comm]

theorem hessian_ram_mul_corner (u p : A) (T : QuadForm A 2) :
    (splitForm u (p • T)).hessian * cornerMat p 1 = p • cornerMat (2 * u) T.hessian := by
  have hH : (p • T).hessian = p • T.hessian := by ext; simp [hessian, smul_coeff]; ring
  rw [hessian_splitForm, hH, cornerMat_mul, mul_one]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cornerMat]
  ring

/-- **Moving columns by $p^{k-1}P(\cdot)$ does not change $Q\circ X$ mod $p^k$** for $Q = \langle u\rangle\perp pT$. -/
theorem compMat_ram_pert_dvd (u p : A) (T : QuadForm A 2) {k : ℕ} (hk : 1 ≤ k) (X N : Matrix (Fin 3) (Fin 3) A)
    (i j : Fin 3) :
    p ^ k ∣ ((splitForm u (p • T)).compMat (X + p ^ (k - 1) • (cornerMat p 1 * N))).coeff i j -
      ((splitForm u (p • T)).compMat X).coeff i j := by
  set Q := splitForm u (p • T) with hQ
  set P : Matrix (Fin 3) (Fin 3) A := cornerMat p 1 with hP
  set H'' : Matrix (Fin 3) (Fin 3) A := cornerMat (2 * u) T.hessian with hH''
  have hpk : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
  -- columns
  have hcol : ∀ m : Fin 3, (fun l => (X + p ^ (k - 1) • (P * N)) l m) =
      (fun l => X l m) + p ^ (k - 1) • (P *ᵥ fun l => N l m) := fun m => by
    ext l; simp [Matrix.add_apply, Matrix.smul_apply]; rfl
  have hF2 : ∀ v w : Fin 3 → A, v ⬝ᵥ (Q.hessian *ᵥ (p ^ (k - 1) • (P *ᵥ w))) = p ^ k * (v ⬝ᵥ (H'' *ᵥ w)) := by
    intro v w
    rw [mulVec_smul, mulVec_mulVec, hQ, hP, hessian_ram_mul_corner, smul_mulVec, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, hpk]; ring
  have hF3 : ∀ w : Fin 3 → A, p ^ k ∣ Q.eval (p ^ (k - 1) • (P *ᵥ w)) := by
    intro w
    have h1 : Q.eval (P *ᵥ w) = p * (splitForm (p * u) T).eval w := by
      rw [← eval_compMat, hQ, hP, splitForm_smul_compMat_corner, eval_smul_form_rd]
    rw [eval_eq_dotProduct', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← eval_eq_dotProduct', h1]
    exact ⟨p ^ (k - 1) * (splitForm (p * u) T).eval w, by rw [hpk]; ring⟩
  have hD : ∀ v w : Fin 3 → A, p ^ k ∣ v ⬝ᵥ (Q.hessian *ᵥ (p ^ (k - 1) • (P *ᵥ w))) :=
    fun v w => by rw [hF2]; exact dvd_mul_right _ _
  rw [compMat_coeff, compMat_coeff, hcol i, hcol j]
  split_ifs with h1 h2
  · subst h2
    have := eval_polar Q (fun l => X l i) (p ^ (k - 1) • (P *ᵥ fun l => N l i))
    rw [show Q.eval ((fun l => X l i) + p ^ (k - 1) • (P *ᵥ fun l => N l i)) - Q.eval (fun l => X l i) =
      (fun l => X l i) ⬝ᵥ (Q.hessian *ᵥ (p ^ (k - 1) • (P *ᵥ fun l => N l i))) +
        Q.eval (p ^ (k - 1) • (P *ᵥ fun l => N l i)) by linear_combination this]
    exact dvd_add (hD _ _) (hF3 _)
  · rw [add_dotProduct, mulVec_add, dotProduct_add, dotProduct_add,
      dot_hessian_comm Q (p ^ (k - 1) • (P *ᵥ fun l => N l i)) (fun l => X l j)]
    have e : ∀ a b c d : A, a + b + (c + d) - a = b + c + d := fun a b c d => by ring
    rw [e]
    exact dvd_add (dvd_add (hD _ _) (hD _ _)) (hD _ _)
  · simp

theorem mul_cornerMat_one_apply {r : ℕ} (p : A) (Z : Matrix (Fin r) (Fin 3) A) (i : Fin r) (j : Fin 3) :
    (Z * cornerMat p (1 : Matrix (Fin 2) (Fin 2) A)) i j = Fin.cases (Z i 0 * p) (fun j' => Z i j'.succ) j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

end Orbit

section OrbitDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A representation of $\pi T$ by $\langle u\rangle\perp\pi T$ mod $\pi^k$ ($k \ge 1$, $u$ a unit) has first row divisible by $\pi$. -/
theorem ram_row_dvd {π : R} (hπ : Irreducible π) {u : R} (hu : IsUnit u) (T : QuadForm R 2) {k : ℕ} (hk : 1 ≤ k)
    (Yh : Matrix (Fin 3) (Fin 2) R) (hx : ∀ i j, π ^ k ∣ ((splitForm u (π • T)).compMat Yh).coeff i j - (π • T).coeff i j) :
    ∀ j, π ∣ Yh 0 j := by
  intro j
  have h1 := hx j j
  rw [compMat_coeff, if_pos le_rfl, if_pos rfl,
    show (fun l => Yh l j) = Fin.cons (Yh 0 j) (fun i : Fin 2 => Yh i.succ j) from (Fin.cons_self_tail _).symm,
    eval_splitForm_cons, eval_smul_form_rd, smul_coeff, Matrix.smul_apply, smul_eq_mul] at h1
  have h3 : π ∣ u * Yh 0 j * Yh 0 j := by
    have h4 : π ∣ π ^ k := dvd_pow_self π (by omega)
    have := h4.trans h1
    have h5 : u * Yh 0 j * Yh 0 j = (u * Yh 0 j * Yh 0 j + π * T.eval (fun i : Fin 2 => Yh i.succ j) -
      π * T.coeff j j) - π * (T.eval (fun i : Fin 2 => Yh i.succ j) - T.coeff j j) := by ring
    rw [h5]; exact dvd_sub this (dvd_mul_right _ _)
  rcases hπ.prime.dvd_or_dvd h3 with h | h
  · rcases hπ.prime.dvd_or_dvd h with h' | h'
    · exact absurd h' (dvr_not_dvd_of_isUnit hπ hu)
    · exact h'
  · exact h

/-- **The frame orbit of $\langle u\rangle\perp\pi T$ mod $\pi^k$ is every representation of $\pi T$** ($k \ge 2$, $u$ a unit, $T$
unimodular with $\bar T$ anisotropic). -/
theorem ramFrame_orbit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (h2 : (2 : R) ≠ 0) {u : R} (hu : IsUnit u) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) {k : ℕ} (hk : 2 ≤ k)
    (Y : Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ k}))
    (hY : ((splitForm u (π • T)).map (Ideal.Quotient.mk _)).compMat Y = (π • T).map (Ideal.Quotient.mk _)) :
    ∃ X, ((splitForm u (π • T)).map (Ideal.Quotient.mk _)).compMat X = (splitForm u (π • T)).map (Ideal.Quotient.mk _) ∧
      X * frameMat _ 2 = Y := by
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  set Q := splitForm u (π • T) with hQdef
  set Q' := splitForm (π * u) T with hQ'def
  set P : Matrix (Fin 3) (Fin 3) R := cornerMat π 1 with hPdef
  have hπ0 := hπ.ne_zero
  -- lift `Y`
  choose f hf using fun (i : Fin 3) (j : Fin 2) => Ideal.Quotient.mk_surjective (Y i j)
  set Yh : Matrix (Fin 3) (Fin 2) R := Matrix.of f with hYh
  have hYm : Yh.map mk = Y := by ext i j; exact hf i j
  have hx : ∀ i j, π ^ k ∣ (Q.compMat Yh).coeff i j - (π • T).coeff i j := by
    rw [← map_mk_eq_iff, ← map_compMat, hYm]; exact hY
  have hrow := ram_row_dvd hπ hu T (by omega : 1 ≤ k) Yh hx
  choose c hc using hrow
  set Zh : Matrix (Fin 3) (Fin 2) R := Matrix.of fun i j => Fin.cases (c j) (fun i' => Yh i'.succ j) i with hZh
  have hPZ : P * Zh = Yh := by
    ext i j; rw [hPdef, cornerMat_one_mul_apply_rd]
    refine Fin.cases ?_ (fun i => rfl) i
    simp [hZh, hc j]
  have hcompP : ∀ Z : Matrix (Fin 3) (Fin 2) R, Q.compMat (P * Z) = π • Q'.compMat Z := fun Z => by
    rw [← compMat_mul, hQdef, hPdef, splitForm_smul_compMat_corner, smul_compMat_rd]
  have hxZ : ∀ p : DVR.UpperIdx 2, π ^ (k - 1) ∣ DVR.formF Q' (fun li => Zh li.1 li.2) p - T.coeff p.1.1 p.1.2 := by
    intro p
    have h1 := hx p.1.1 p.1.2
    rw [← hPZ, hcompP, smul_coeff, smul_coeff, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_sub, show k = k - 1 + 1 by omega, pow_succ', mul_dvd_mul_iff_left hπ0] at h1
    exact h1
  -- Hensel
  obtain ⟨y, hy, hyx⟩ := newton_lift hπ (DVR.formF Q') (DVR.formD Q') (DVR.formF_add_smul Q')
    (fun p => T.coeff p.1.1 p.1.2) 0 (k - 1) (by omega)
    (fun x hx c => DVR.formD_surj Q' T π hπ 0 (k - 1) (by simp)
      (by simpa using dvr_not_dvd_of_isUnit hπ hT) (by omega) x hx c) _ hxZ
  set Zt := DVR.toMat y with hZt
  have hQZt : Q'.compMat Zt = T := ext_upper fun i j hij => congrFun hy ⟨(i, j), hij⟩
  -- the exact isometry of `Q'`
  obtain ⟨X', hX', hX'F⟩ := exists_isometry_frame h2 (π * u) T hT Zt hQZt
  have hs' : ∀ i : Fin 2, π ∣ X' i.succ 0 := by
    have h00 := congrArg (fun S : QuadForm R 3 => S.coeff 0 0) hX'
    simp only [compMat_coeff, le_refl, if_true] at h00
    rw [show (fun l => X' l 0) = Fin.cons (X' 0 0) (fun i : Fin 2 => X' i.succ 0) from (Fin.cons_self_tail _).symm,
      eval_splitForm_cons] at h00
    have h1 : T.eval (fun i : Fin 2 => X' i.succ 0) = π * (u - u * X' 0 0 * X' 0 0) := by
      rw [splitForm_coeff, cornerMat_zero_zero] at h00; linear_combination h00
    exact haniso _ ⟨_, h1⟩
  choose d hd using hs'
  set X : Matrix (Fin 3) (Fin 3) R := Matrix.of fun i j =>
    Fin.cases (Fin.cases (X' 0 0) (fun j' => π * X' 0 j'.succ) j) (fun i' => Fin.cases (d i') (fun j' => X' i'.succ j'.succ) j) i
    with hXdef
  have hXP : X * P = P * X' := by
    ext i j
    rw [hPdef, mul_cornerMat_one_apply, cornerMat_one_mul_apply_rd]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hXdef]; ring
    · simp [hXdef]
    · simp [hXdef, hd i]; ring
    · simp [hXdef]
  have hQX : Q.compMat X = Q := by
    apply compMat_corner_cancel hπ0
    rw [compMat_mul, hXP, ← compMat_mul, hQdef, splitForm_smul_compMat_corner, smul_compMat_rd, ← hQ'def, hX']
  have hXF : X * frameMat R 2 = P * Zt := by
    rw [← cornerMat_one_mul_frameMat π, ← hPdef, ← Matrix.mul_assoc, hXP, Matrix.mul_assoc, hX'F]
  -- the correction
  have hdiff : ∀ i j, π ^ (k - 1) ∣ Zh i j - Zt i j := by
    intro i j
    have := hyx (i, j)
    rw [Nat.sub_zero] at this
    have e : Zh i j - Zt i j = -(y (i, j) - Zh i j) := by simp [hZt, DVR.toMat]
    rw [e]; exact (dvd_neg).mpr this
  choose M hM using hdiff
  set N : Matrix (Fin 3) (Fin 3) R := Matrix.of fun i j => Fin.cases 0 (fun j' => M i j') j with hNdef
  set Xc := X + π ^ (k - 1) • (P * N) with hXc
  have hXcF : Xc * frameMat R 2 = Yh := by
    have hNF : N * frameMat R 2 = Matrix.of M := by
      ext i j; rw [mul_frameMat_apply]; rfl
    rw [hXc, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hNF, hXF, ← hPZ, ← Matrix.mul_smul,
      ← Matrix.mul_add]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination -(hM i j)
  refine ⟨Xc.map mk, ?_, ?_⟩
  · rw [map_compMat, map_mk_eq_iff]
    intro i j
    have := compMat_ram_pert_dvd u π T (by omega : 1 ≤ k) X N i j
    rw [← hQdef, hQX] at this
    exact this
  · calc Xc.map mk * frameMat _ 2 = (Xc * frameMat R 2).map mk := by rw [Matrix.map_mul, frameMat_map]; rfl
      _ = Y := by rw [hXcF, hYm]

/-- **$A_{\pi^{k+1}}(\langle u\rangle\perp\pi T, \pi T) = q^4A_{\pi^k}(\langle\pi u\rangle\perp T, T)$** ($u$ a unit): a representation is $PZ$
($P = \mathrm{diag}(\pi, 1, 1)$, `ram_row_dvd`), and $Q\circ PZ = \pi(Q'\circ Z)$. -/
theorem repCountForm_ram_piT [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {u : R}
    (hu : IsUnit u) (T : QuadForm R 2) (k : ℕ) :
    repCountForm (splitForm u (π • T)) (π • T) π (k + 1) = q R ^ 4 * repCountForm (splitForm (π * u) T) T π k := by
  classical
  have := finite_quot_pow π hπ (k + 1)
  have := finite_quot_pow π hπ k
  have hπ0 := hπ.ne_zero
  set Q := splitForm u (π • T) with hQdef
  set Q' := splitForm (π * u) T with hQ'def
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) with hmk
  set mk' := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk'
  have hle : Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k))
  set ρ := Ideal.Quotient.factor hle with hρ
  set ρM : Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) →+ Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ k}) :=
    ρ.toAddMonoidHom.mapMatrix with hρM
  set Pb : Matrix (Fin 3) (Fin 3) (R ⧸ Ideal.span {π ^ (k + 1)}) := cornerMat (mk π) 1 with hPb
  set P : Matrix (Fin 3) (Fin 3) R := cornerMat π 1 with hPdef
  set φ : Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) →+ Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) :=
    { toFun := fun Z => Pb * Z
      map_zero' := Matrix.mul_zero _
      map_add' := fun Z Z' => Matrix.mul_add _ _ _ } with hφ
  set S : Set (Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)})) :=
    {Y | (Q.map mk).compMat Y = (π • T).map mk} with hS
  set S' : Set (Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ k})) :=
    {W | (Q'.map mk').compMat W = T.map mk'} with hS'
  have hPbmap : ∀ Z : Matrix (Fin 3) (Fin 2) R, φ (Z.map mk) = (P * Z).map mk := fun Z => by
    show Pb * Z.map mk = _
    rw [Matrix.map_mul, hPb, hPdef, cornerMat_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcompP : ∀ Z : Matrix (Fin 3) (Fin 2) R, Q.compMat (P * Z) = π • Q'.compMat Z := fun Z => by
    rw [← compMat_mul, hQdef, hPdef, splitForm_smul_compMat_corner, smul_compMat_rd]
  -- (a) every representation is in the image of `φ`
  have hrange : S ⊆ Set.range φ := by
    intro Y hY
    choose f hf using fun (i : Fin 3) (j : Fin 2) => Ideal.Quotient.mk_surjective (Y i j)
    set Yh : Matrix (Fin 3) (Fin 2) R := Matrix.of f with hYh
    have hYm : Yh.map mk = Y := by ext i j; exact hf i j
    have hx : ∀ i j, π ^ (k + 1) ∣ (Q.compMat Yh).coeff i j - (π • T).coeff i j := by
      rw [← map_mk_eq_iff, ← map_compMat, hYm]; exact hY
    choose c hc using ram_row_dvd hπ hu T (by omega : 1 ≤ k + 1) Yh hx
    refine ⟨(Matrix.of fun i j => Fin.cases (c j) (fun i' => Yh i'.succ j) i : Matrix (Fin 3) (Fin 2) R).map mk, ?_⟩
    rw [hPbmap, ← hYm]
    congr 1
    ext i j; rw [hPdef, cornerMat_one_mul_apply_rd]
    refine Fin.cases ?_ (fun i => rfl) i
    simp [hc j]
  -- (b) the preimages agree
  have hpre : φ ⁻¹' S = ρM ⁻¹' S' := by
    ext Z
    choose f hf using fun (i : Fin 3) (j : Fin 2) => Ideal.Quotient.mk_surjective (Z i j)
    have hZ : Z = (Matrix.of f).map mk := by ext i j; exact (hf i j).symm
    have hρZ : ρM Z = (Matrix.of f).map mk' := by
      rw [hZ]; ext i j
      simp only [hρM, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, hρ, hmk, hmk']
      exact Ideal.Quotient.factor_mk hle (f i j)
    rw [Set.mem_preimage, Set.mem_preimage, hρZ, hZ, hPbmap, hS, hS', Set.mem_setOf_eq, Set.mem_setOf_eq,
      map_compMat, map_compMat, map_mk_eq_iff, map_mk_eq_iff, hcompP]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [smul_coeff, smul_coeff, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub,
      pow_succ', mul_dvd_mul_iff_left hπ0]
  -- (c) kernels
  have hsurj : Function.Surjective ρM := fun Y => by
    choose f hf using fun i j => Ideal.Quotient.factor_surjective hle (Y i j)
    exact ⟨Matrix.of f, by ext i j; exact hf i j⟩
  have hc : ∀ j, Nat.card (R ⧸ Ideal.span {π ^ j}) = q R ^ j := fun j => card_quot_pow π hπ j
  have hM : ∀ j, Nat.card (Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ j})) = q R ^ (j * 6) := by
    intro j
    rw [show Matrix (Fin 3) (Fin 2) (R ⧸ Ideal.span {π ^ j}) = (Fin 3 → Fin 2 → R ⧸ Ideal.span {π ^ j}) from rfl,
      Nat.card_fun, Nat.card_fun, hc, Nat.card_fin, Nat.card_fin, ← pow_mul, ← pow_mul]
  have hkerρ : Nat.card ρM.ker = q R ^ 6 := by
    have h2 := card_preimage_eq ρM Set.univ (fun Y _ => hsurj Y)
    simp only [Set.preimage_univ, Nat.card_univ] at h2
    rw [hM, hM] at h2
    have hq : 0 < q R ^ (k * 6) := pow_pos q_pos _
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [← pow_add, show 6 + k * 6 = (k + 1) * 6 by ring, h2]
  have hkerφ : Nat.card φ.ker = q R ^ 2 := by
    have e : φ.ker ≃ (Fin 2 → {t : R ⧸ Ideal.span {π ^ (k + 1)} // mk π * t = 0}) :=
      { toFun := fun Z => fun j => ⟨Z.1 0 j, by
          have := congrFun (congrFun Z.2 0) j
          simpa [hφ, hPb, cornerMat_one_mul_apply_rd] using this⟩
        invFun := fun t => ⟨Matrix.of fun i j => Fin.cases (t j).1 (fun _ => 0) i, by
          rw [AddMonoidHom.mem_ker, hφ]
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ext i j
          rw [hPb, cornerMat_one_mul_apply_rd]
          refine Fin.cases ?_ (fun i => rfl) i
          simpa using (t j).2⟩
        left_inv := fun Z => by
          apply Subtype.ext
          ext i j
          refine Fin.cases rfl (fun i => ?_) i
          have := congrFun (congrFun Z.2 i.succ) j
          simp only [hφ, hPb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cornerMat_one_mul_apply_rd] at this
          simpa using this.symm
        right_inv := fun t => rfl }
    rw [Nat.card_congr e, Nat.card_fun, card_ann_pi hπ (by omega), Nat.card_fin]
  have h1 := card_preimage_eq φ S hrange
  have h2 := card_preimage_eq ρM S' (fun Y _ => hsurj Y)
  rw [hpre, h2, hkerρ, hkerφ] at h1
  unfold repCountForm
  change Nat.card S = q R ^ 4 * Nat.card S'
  have hq : 0 < q R ^ 2 := pow_pos q_pos _
  apply Nat.eq_of_mul_eq_mul_left hq
  rw [← h1, ← mul_assoc, ← pow_add]

theorem map_smul_form_rd {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (c : R) (T : QuadForm R n) :
    (c • T).map f = f c • T.map f := by
  ext i j; simp [QuadForm.map, smul_coeff]

/-- **The self-density of $\langle u\rangle\perp\pi T$ at a dyadic prime** ($\pi^e \,\|\, 2$, $e \ge 1$, $u$ a unit, $T$ binary with
$\det H_T$ a unit and $\bar T$ anisotropic):
$$\beta_\pi(\langle u\rangle\perp\pi T, \langle u\rangle\perp\pi T) = 4q^{e+2}(q+1).$$
This is the trace-zero lattice of the maximal order of a quaternion division algebra over a dyadic field. -/
theorem localDensityForm_ram_dyadic [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) {e : ℕ} (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (he1 : 1 ≤ e)
    {u : R} (hu : IsUnit u) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm (splitForm u (π • T)) (splitForm u (π • T)) π = 4 * (q R : ℝ) ^ (e + 2) * (q R + 1) := by
  classical
  have h2π : π ∣ 2 := (dvd_pow_self π (by omega)).trans he.1
  set Q := splitForm u (π • T) with hQdef
  set Q' := splitForm (π * u) T with hQ'def
  have hHpT : (π • T).hessian = π • T.hessian := by ext; simp [hessian, smul_coeff]; ring
  have hQnd : Q.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hQdef, det_hessian_splitForm, hHpT, det_smul]
    exact mul_ne_zero (mul_ne_zero h20 hu.ne_zero) (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hT.ne_zero)
  have hTnd : T.Nondegenerate := hT.ne_zero
  have hUnd : (unary u).Nondegenerate := by
    have : (unary u).hessian.det = 2 * u := by simp [hessian, unary, QuadForm.diag, Matrix.det_unique]; ring
    rw [QuadForm.Nondegenerate, this]; exact mul_ne_zero h20 hu.ne_zero
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd π hπ hQnd
  have e1 := localDensityForm_eventually_eq Q Q hQnd π hπ le_rfl
  have e2 := localDensityForm_eventually_eq Q' T hTnd π hπ (by norm_num)
  have e3 := localDensityForm_eventually_eq (unary u) (unary u) hUnd π hπ le_rfl
  obtain ⟨m, h1, h2, h3, hm⟩ := (((Filter.tendsto_add_atTop_nat 1).eventually e1).and (e2.and
    (((Filter.tendsto_add_atTop_nat 1).eventually e3).and (Filter.eventually_gt_atTop (d + 1))))).exists
  have hβ' := localDensityForm_piU_T hπ h2π u T hT haniso
  have hβu := localDensityForm_self_unary π hπ e he hu
  rw [← h2] at hβ'
  rw [← h3] at hβu
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  norm_num at hβ' hβu h1
  have hA' : (repCountForm Q' T π m : ℝ) = 2 * ((q R : ℝ) + 1) / q R * (q R : ℝ) ^ (m * 3) := by
    rw [← hβ']; field_simp
  rw [← h1]
  -- the orbit–stabilizer count at level `m + 1`
  have := finite_quot_pow π hπ (m + 1)
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) with hmk
  have hQmap : Q.map mk = splitForm (mk u) (mk π • T.map mk) := by
    rw [hQdef, map_splitForm, map_smul_form_rd]
  have hTu : IsUnit (T.map mk).hessian.det := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hT.map _
  have hcount : repCountForm Q Q π (m + 1) =
      (q R ^ 4 * repCountForm Q' T π m) * (repCountForm (unary u) (unary u) π (m + 1) * q R ^ 2) := by
    rw [← repCountForm_ram_piT hπ hu T m]
    unfold repCountForm
    rw [card_compMat_eq_frameOrbit_mul _ (fun X hX => isUnit_det_of_compMat_eq _ π hπ d (m + 1) hd hd'
      (by omega) X hX) (frameMat _ 2)]
    congr 1
    · unfold frameOrbit
      refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
      constructor
      · rintro ⟨X, hX, rfl⟩
        rw [← compMat_mul, hX, hQmap, splitForm_compMat_frameMat, map_smul_form_rd]
      · intro hY
        exact ramFrame_orbit hπ h20 hu T hT haniso (by omega) Y hY
    · rw [hQmap, Nat.card_congr (stabRamEquiv _ _ _ hTu), Nat.card_prod, map_unary,
        ← Nat.card_congr (unaryEquiv (mk u)), Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin 2 => R ⧸ Ideal.span {π ^ (m + 1)})
          (p := fun _ t => mk π * t = 0)), Nat.card_fun,
        card_ann_pi hπ (by omega), Nat.card_fin]
  rw [hcount]
  push_cast
  rw [hA', hβu]
  field_simp
  ring

end OrbitDVR

/-! ### The shape of an anisotropic maximal ternary lattice at a dyadic prime -/

section Chevalley

variable {K : Type*} [Field K] [Finite K]

/-- **Every ternary quadratic form over a finite field is isotropic** (Chevalley–Warning). -/
theorem exists_isotropic_ternary (S : QuadForm K 3) : ∃ z : Fin 3 → K, z ≠ 0 ∧ S.eval z = 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin 3) K, f = ∑ i, ∑ j, if i ≤ j then
      MvPolynomial.C (S.coeff i j) * MvPolynomial.X i * MvPolynomial.X j else 0 := ⟨_, rfl⟩
  have hev : ∀ z, MvPolynomial.eval z f = S.eval z := by
    intro z
    simp only [hf, map_sum, QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hterm : ∀ (c : K) (i j : Fin 3),
      (MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
    intro c i j
    calc _ ≤ (MvPolynomial.C c * MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree +
          (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C c : MvPolynomial (Fin 3) K).totalDegree +
          (MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree) +
          (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
            Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ = 2 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    rw [Fintype.card_fin, hf]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finset_sum _ _) ?_
    refine lt_of_le_of_lt (Finset.sup_le fun i _ => ?_ : _ ≤ 2) (by norm_num)
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le fun j _ => ?_)
    split_ifs
    · exact hterm _ _ _
    · simp
  set p := ringChar K with hp
  have hdvd := char_dvd_card_solutions (K := K) p hdeg
  have hp2 : 2 ≤ p := (CharP.char_is_prime K p).two_le
  by_contra hne
  push Not at hne
  have hsub : ∀ z : {z : Fin 3 → K // MvPolynomial.eval z f = 0}, z = ⟨0, by rw [hev]; simp [QuadForm.eval,
      QuadForm.evalIn]⟩ := by
    intro z
    apply Subtype.ext
    by_contra h
    exact hne z.1 h (by rw [← hev]; exact z.2)
  have h1 : Fintype.card {z : Fin 3 → K // MvPolynomial.eval z f = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨_, hsub⟩
  rw [h1] at hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

end Chevalley

section ShapeAlg

variable {A : Type*} [CommRing A]

theorem eval_single_rd {n : ℕ} (S : QuadForm A n) (i : Fin n) : S.eval (Pi.single i 1) = S.coeff i i := by
  rw [eval_eq_dotProduct', mulVec_single_one, single_dotProduct, one_mul]; rfl

theorem single_dot_hessian_single {n : ℕ} (S : QuadForm A n) (i j : Fin n) :
    Pi.single i 1 ⬝ᵥ (S.hessian *ᵥ Pi.single j 1) = S.hessian i j := by
  rw [mulVec_single_one, single_dotProduct, one_mul]; rfl

/-- The cyclic permutation matrix $e_j \mapsto e_{k+j}$. -/
def cycMat (k : Fin 3) : Matrix (Fin 3) (Fin 3) A := Matrix.of fun i j => if i = k + j then 1 else 0

theorem det_cycMat (k : Fin 3) : (cycMat k : Matrix (Fin 3) (Fin 3) A).det = 1 := by
  fin_cases k <;> simp [cycMat, Matrix.det_fin_three]

theorem cycMat_col (k j : Fin 3) : (fun l => (cycMat k : Matrix (Fin 3) (Fin 3) A) l j) = Pi.single (k + j) 1 := by
  ext l; simp [cycMat, Pi.single_apply]

theorem compMat_cycMat_coeff (S : QuadForm A 3) (k a b : Fin 3) (hab : a < b) :
    (S.compMat (cycMat k)).coeff a b = S.hessian (k + a) (k + b) := by
  rw [compMat_coeff, if_pos hab.le, if_neg hab.ne, cycMat_col, cycMat_col, single_dot_hessian_single]

theorem compMat_cycMat_coeff_self (S : QuadForm A 3) (k a : Fin 3) :
    (S.compMat (cycMat k)).coeff a a = S.coeff (k + a) (k + a) := by
  rw [compMat_coeff, if_pos le_rfl, if_pos rfl, cycMat_col, eval_single_rd]

/-- $Q(t, w) = c_{00}t^2 + t\,(c_{01}, c_{02})\cdot w + Q_{\mathrm{tail}}(w)$. -/
theorem eval_cons_three (S : QuadForm A 3) (t : A) (w : Fin 2 → A) :
    S.eval (Fin.cons t w) = S.coeff 0 0 * t * t + t * ((fun j : Fin 2 => S.coeff 0 j.succ) ⬝ᵥ w) + S.tail.eval w := by
  have h10 : S.coeff 1 0 = 0 := S.upper (show (0 : Fin 3) < 1 by decide)
  have h20 : S.coeff 2 0 = 0 := S.upper (show (0 : Fin 3) < 2 by decide)
  have h21 : S.coeff 2 1 = 0 := S.upper (show (1 : Fin 3) < 2 by decide)
  simp only [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, Fin.sum_univ_two, Algebra.algebraMap_self,
    RingHom.id_apply, tail_coeff, dotProduct]
  have e2 : (Fin.cons t w : Fin 3 → A) 2 = w 1 := rfl
  simp [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e2]
  ring

theorem tail_hessian (S : QuadForm A 3) (i j : Fin 2) : S.tail.hessian i j = S.hessian i.succ j.succ := rfl

/-- **Orthogonalizing $e_0$:** if $H_{\mathrm{tail}}z = (c_{01}, c_{02})$ then $Q\circ(e_0 - z\,|\,e_1\,e_2) = \langle Q(e_0 - z)\rangle\perp Q_{\mathrm{tail}}$. -/
theorem compMat_stabMat_orth (S : QuadForm A 3) (z : Fin 2 → A)
    (hz : S.tail.hessian *ᵥ z = fun j => S.coeff 0 j.succ) :
    S.compMat (stabMat 1 (-z)) = splitForm (S.eval (Fin.cons 1 (-z))) S.tail := by
  refine eq_of_eval_eq fun w => ?_
  rw [eval_compMat, ← Fin.cons_self_tail w, stabMat_mulVec, eval_splitForm_cons, eval_cons_three, eval_cons_three,
    one_mul, mul_one]
  set c : Fin 2 → A := fun j => S.coeff 0 j.succ with hc
  set y := Fin.tail w with hy
  set t := w 0 with ht
  rw [show t • -z + y = y + (-t) • z by rw [smul_neg, neg_smul]; abel, eval_add_smul_gen, ← hz]
  have hsym : (S.tail.hessian *ᵥ y) ⬝ᵥ z = y ⬝ᵥ (S.tail.hessian *ᵥ z) := by
    rw [dot_hessian_comm, dotProduct_comm]
  have hneg : S.tail.eval (-z) = S.tail.eval z := by
    rw [eval_eq_dotProduct', eval_eq_dotProduct', mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hsym, hneg, hz]
  simp only [dotProduct_add, dotProduct_smul, dotProduct_neg, smul_eq_mul]
  rw [dotProduct_comm y c]
  ring

theorem det_stabMat (x : A) (s : Fin 2 → A) : (stabMat x s).det = x := by
  rw [Matrix.det_fin_three]
  have e : ∀ i j, stabMat x s i j = !![x, 0, 0; s 0, 1, 0; s 1, 0, 1] i j := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [e]
  simp

end ShapeAlg

section ShapeDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem residue_eq_zero_iff_dvd_rd {π : R} (hπ : Irreducible π) (x : R) : IsLocalRing.residue R x = 0 ↔ π ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem vec_dvd_of_mulVec {π : R} {W : Matrix (Fin 3) (Fin 3) R} (hW : IsUnit W.det) {z : Fin 3 → R}
    (h : ∀ i, π ∣ (W *ᵥ z) i) : ∀ i, π ∣ z i := by
  have hz : z = W⁻¹ *ᵥ (W *ᵥ z) := by rw [mulVec_mulVec, nonsing_inv_mul _ hW, one_mulVec]
  intro i
  rw [hz]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l) _

theorem pow_unit_inj {π : R} (hπ : Irreducible π) {m m' : ℕ} {β β' : R} (hβ : IsUnit β) (hβ' : IsUnit β')
    (h : π ^ m * β = π ^ m' * β') : m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · obtain ⟨d, rfl⟩ : ∃ d, m' = m + (d + 1) := ⟨m' - m - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero m hπ.ne_zero) h
    exact dvr_not_dvd_of_isUnit hπ hβ ⟨π ^ d * β', by rw [h', pow_succ']; ring⟩
  · obtain ⟨d, rfl⟩ : ∃ d, m = m' + (d + 1) := ⟨m - m' - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero m' hπ.ne_zero) h
    exact dvr_not_dvd_of_isUnit hπ hβ' ⟨π ^ d * β, by rw [← h', pow_succ']; ring⟩

theorem exists_two_eq {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2) :
    ∃ (e : ℕ) (t : R), 1 ≤ e ∧ IsUnit t ∧ (2 : R) = π ^ e * t := by
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd π hπ h20
  obtain ⟨t, ht, htu⟩ := dvr_exact hπ he he'
  refine ⟨e, t, ?_, htu, ht⟩
  by_contra h0
  push Not at h0
  interval_cases e
  exact he' (by rw [zero_add, pow_one]; exact h2π)

/-- Maximality is invariant under $\mathrm{GL}_3(R)$. -/
theorem hmax_compMat {π : R} {S : QuadForm R 3} (hmax : ∀ z : Fin 3 → R, π ^ 2 ∣ S.eval z → ∀ i, π ∣ z i)
    {W : Matrix (Fin 3) (Fin 3) R} (hW : IsUnit W.det) :
    ∀ z : Fin 3 → R, π ^ 2 ∣ (S.compMat W).eval z → ∀ i, π ∣ z i := fun z hz =>
  vec_dvd_of_mulVec hW (hmax _ (by rwa [eval_compMat] at hz))

/-- The square class of $\det H$ (up to $8$) is invariant under $\mathrm{GL}_3(R)$. -/
theorem hdisc_compMat {π : R} {S : QuadForm R 3}
    (hdisc : ∃ (i j : ℕ) (w : R), IsUnit w ∧ π ^ (2 * i) * S.hessian.det = 8 * π ^ (2 * j) * w ^ 2)
    {W : Matrix (Fin 3) (Fin 3) R} (hW : IsUnit W.det) :
    ∃ (i j : ℕ) (w : R), IsUnit w ∧ π ^ (2 * i) * (S.compMat W).hessian.det = 8 * π ^ (2 * j) * w ^ 2 := by
  obtain ⟨i, j, w, hw, h⟩ := hdisc
  refine ⟨i, j, w * W.det, hw.mul hW, ?_⟩
  rw [hessian_compMat, det_mul, det_mul, det_transpose]
  linear_combination (W.det ^ 2) * h

/-- **No unimodular binary splits off** a maximal ternary lattice whose discriminant is $8\cdot\square$ ($\pi \mid 2$):
$\langle c\rangle\perp P$ with $\det H_P$ a unit is impossible. -/
theorem false_of_split_unimodular [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2) (c : R)
    (P : QuadForm R 2) (hP : IsUnit P.hessian.det)
    (hmax : ∀ z : Fin 3 → R, π ^ 2 ∣ (splitForm c P).eval z → ∀ i, π ∣ z i)
    (hdisc : ∃ (i j : ℕ) (w : R), IsUnit w ∧
      π ^ (2 * i) * (splitForm c P).hessian.det = 8 * π ^ (2 * j) * w ^ 2) : False := by
  classical
  set res := IsLocalRing.residue R with hres
  have hres0 := residue_eq_zero_iff_dvd_rd hπ
  by_cases hc : π ∣ c
  · obtain ⟨c₁, rfl⟩ := hc
    by_cases hc1 : π ∣ c₁
    · -- `Q(e₀) = c ∈ π²R`
      obtain ⟨c₂, rfl⟩ := hc1
      have := hmax (Fin.cons 1 0) ⟨c₂, by rw [eval_splitForm_cons]; simp [QuadForm.eval, QuadForm.evalIn]; ring⟩ 0
      exact hπ.not_isUnit (isUnit_of_dvd_unit this isUnit_one)
    · -- parity of the valuation of `det H`
      have hc1u := dvr_isUnit_of_not_dvd hπ hc1
      obtain ⟨e, t, he1, ht, h2e⟩ := exists_two_eq hπ h20 h2π
      obtain ⟨i, j, w, hw, h⟩ := hdisc
      rw [det_hessian_splitForm] at h
      have h' : π ^ (2 * i + e + 1) * (t * c₁ * P.hessian.det) = π ^ (3 * e + 2 * j) * (t ^ 3 * w ^ 2) := by
        have h8 : (8 : R) = 2 * 2 * 2 := by norm_num
        rw [h8, h2e] at h
        rw [pow_add, pow_add, pow_succ, pow_add, show 3 * e = e + e + e by ring, pow_add, pow_add]
        linear_combination h
      have := pow_unit_inj hπ ((ht.mul hc1u).mul hP) ((ht.pow 3).mul (hw.pow 2)) h'
      omega
  · -- `c` a unit: a nonsingular zero mod `π` gives a vector of value in `π²R`
    obtain ⟨zb, hz0, hz⟩ := exists_isotropic_ternary ((splitForm c P).map res)
    choose x hx using fun i => IsLocalRing.residue_surjective (zb i)
    have hzx : zb = fun i => res (x i) := funext fun i => (hx i).symm
    subst hzx
    have hSx : π ∣ (splitForm c P).eval x := by
      rw [← hres0, ← hz, eval_map_comp']
    -- the lower part `p` of `x` is nonzero mod `π`
    set p : Fin 2 → R := Fin.tail x with hp
    have hxcons : x = Fin.cons (x 0) p := (Fin.cons_self_tail x).symm
    have hpnd : ¬ ∀ l, π ∣ p l := by
      intro hpl
      apply hz0
      have hx0 : π ∣ x 0 := by
        have h1 : (splitForm c P).eval x = c * x 0 * x 0 + P.eval p := by rw [hxcons, eval_splitForm_cons]; rfl
        have h2 : π ∣ P.eval p := by
          rw [eval_eq_dotProduct']
          exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hpl l) _
        have h3 : π ∣ c * x 0 * x 0 := by
          have := dvd_sub hSx h2; rwa [h1, add_sub_cancel_right] at this
        rcases hπ.prime.dvd_or_dvd h3 with h4 | h4
        · rcases hπ.prime.dvd_or_dvd h4 with h5 | h5
          · exact absurd h5 hc
          · exact h5
        · exact h4
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · exact (hres0 _).2 hx0
      · exact (hres0 _).2 (hpl l)
    -- a coordinate of `H_P p` is a unit
    obtain ⟨m, hm⟩ : ∃ m, ¬ π ∣ (P.hessian *ᵥ p) m := by
      by_contra hall
      push Not at hall
      apply hpnd
      have : p = P.hessian⁻¹ *ᵥ (P.hessian *ᵥ p) := by rw [mulVec_mulVec, nonsing_inv_mul _ hP, one_mulVec]
      intro l
      rw [this]
      simp only [mulVec, dotProduct]
      exact Finset.dvd_sum fun l' _ => dvd_mul_of_dvd_right (hall l') _
    set y : Fin 3 → R := Fin.cons 0 (Pi.single m 1) with hy
    have hβ : ((splitForm c P).hessian *ᵥ x) ⬝ᵥ y = (P.hessian *ᵥ p) m := by
      rw [hxcons, hessian_splitForm, cornerMat_mulVec, hy]
      change (Matrix.vecCons _ _ : Fin 3 → R) ⬝ᵥ Matrix.vecCons _ _ = _
      rw [Matrix.cons_dotProduct_cons, dotProduct_single, mul_zero, zero_add, mul_one]
    have hβu : IsUnit ((splitForm c P).hessian *ᵥ x ⬝ᵥ y) := by rw [hβ]; exact dvr_isUnit_of_not_dvd hπ hm
    set s : R := -(splitForm c P).eval x * ↑hβu.unit⁻¹ with hs
    have hsβ : s * ((splitForm c P).hessian *ᵥ x ⬝ᵥ y) = -(splitForm c P).eval x := by
      rw [hs, mul_assoc, hβu.val_inv_mul, mul_one]
    have hsπ : π ∣ s := by rw [hs]; exact dvd_mul_of_dvd_left (dvd_neg.mpr hSx) _
    have hval : π ^ 2 ∣ (splitForm c P).eval (x + s • y) := by
      rw [eval_add_smul_gen, hsβ]
      simp only [add_neg_cancel, zero_add]
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hsπ 2) _
    have hdx := hmax _ hval
    apply hz0
    funext i
    have : π ∣ x i := by
      have := dvd_sub (hdx i) (dvd_mul_of_dvd_left hsπ (y i))
      simpa using this
    exact (hres0 _).2 this

theorem det_hessian_binary {A : Type*} [CommRing A] (T : QuadForm A 2) :
    T.hessian.det = 4 * T.coeff 0 0 * T.coeff 1 1 - T.coeff 0 1 ^ 2 := by
  have h10 : T.coeff 1 0 = 0 := T.upper (show (0 : Fin 2) < 1 by decide)
  simp [hessian, det_fin_two, h10]; ring

theorem isUnit_det_hessian_binary {π : R} (hπ : Irreducible π) (h2π : π ∣ 2) (T : QuadForm R 2)
    (hb : ¬ π ∣ T.coeff 0 1) : IsUnit T.hessian.det := by
  refine dvr_isUnit_of_not_dvd hπ fun h => hb ?_
  rw [det_hessian_binary] at h
  have h4 : π ∣ 4 * T.coeff 0 0 * T.coeff 1 1 :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (h2π.trans ⟨2, by norm_num⟩) _) _
  have := dvd_sub h4 h
  rw [sub_sub_cancel] at this
  exact hπ.prime.dvd_of_dvd_pow this

theorem hessian_dvd_of_polar {π : R} (h2π : π ∣ 2) (S : QuadForm R 3) (hpol : ∀ a b, a < b → π ∣ S.coeff a b) :
    ∀ a b, π ∣ S.hessian a b := by
  intro a b
  simp only [hessian, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [S.upper h, add_zero]; exact hpol a b h
  · rw [← two_mul]; exact dvd_mul_of_dvd_left h2π _
  · rw [S.upper h, zero_add]; exact hpol b a h

theorem dot_dvd_of_dvd {π : R} {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (hM : ∀ a b, π ∣ M a b) (v w : Fin n → R) :
    π ∣ v ⬝ᵥ (M *ᵥ w) := by
  simp only [dotProduct, mulVec]
  exact Finset.dvd_sum fun a _ => dvd_mul_of_dvd_right (Finset.dvd_sum fun b _ => dvd_mul_of_dvd_left (hM a b) _) _

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Step A: the polar form vanishes mod $\pi$.** -/
theorem polar_dvd_of_max {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2) (S : QuadForm R 3)
    (hmax : ∀ z : Fin 3 → R, π ^ 2 ∣ S.eval z → ∀ i, π ∣ z i)
    (hdisc : ∃ (i j : ℕ) (w : R), IsUnit w ∧ π ^ (2 * i) * S.hessian.det = 8 * π ^ (2 * j) * w ^ 2) :
    ∀ a b, a < b → π ∣ S.coeff a b := by
  intro a b hab
  by_contra hn
  have hH : ∀ k, (S.compMat (cycMat k)).coeff 1 2 = S.hessian (k + 1) (k + 2) := fun k =>
    compMat_cycMat_coeff S k 1 2 (by decide)
  have hup : ∀ a b : Fin 3, a < b → S.hessian a b = S.coeff a b ∧ S.hessian b a = S.coeff a b := by
    intro a b h
    simp [hessian, Matrix.add_apply, Matrix.transpose_apply, S.upper h]
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, ¬ π ∣ (S.compMat (cycMat k)).coeff 1 2 := by
    fin_cases a <;> fin_cases b <;> simp at hab
    · exact ⟨2, by rw [hH]; simpa [(hup 0 1 (by decide)).1] using hn⟩
    · exact ⟨1, by rw [hH]; simpa [(hup 0 2 (by decide)).2] using hn⟩
    · exact ⟨0, by rw [hH]; simpa [(hup 1 2 (by decide)).1] using hn⟩
  set S1 := S.compMat (cycMat k) with hS1
  have hW1 : IsUnit (cycMat k : Matrix (Fin 3) (Fin 3) R).det := by rw [det_cycMat]; exact isUnit_one
  have hP : IsUnit S1.tail.hessian.det :=
    isUnit_det_hessian_binary hπ h2π _ (by rw [tail_coeff]; exact hk)
  set z := S1.tail.hessian⁻¹ *ᵥ (fun j : Fin 2 => S1.coeff 0 j.succ) with hz
  have hz' : S1.tail.hessian *ᵥ z = fun j => S1.coeff 0 j.succ := by
    rw [hz, mulVec_mulVec, mul_nonsing_inv _ hP, one_mulVec]
  have horth := compMat_stabMat_orth S1 z hz'
  have hW2 : IsUnit (stabMat (1 : R) (-z)).det := by rw [det_stabMat]; exact isUnit_one
  have hmax2 := hmax_compMat (hmax_compMat hmax hW1) hW2
  have hdisc2 := hdisc_compMat (hdisc_compMat hdisc hW1) hW2
  rw [← hS1, horth] at hmax2 hdisc2
  exact false_of_split_unimodular hπ h20 h2π _ _ hP hmax2 hdisc2

/-- **Step B: some diagonal coefficient is a unit.** -/
theorem exists_diag_unit_of_max {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2) (S : QuadForm R 3)
    (hmax : ∀ z : Fin 3 → R, π ^ 2 ∣ S.eval z → ∀ i, π ∣ z i)
    (hdisc : ∃ (i j : ℕ) (w : R), IsUnit w ∧ π ^ (2 * i) * S.hessian.det = 8 * π ^ (2 * j) * w ^ 2) :
    ∃ k, ¬ π ∣ S.coeff k k := by
  classical
  by_contra hall
  push Not at hall
  have hpol := polar_dvd_of_max hπ h20 h2π S hmax hdisc
  have hdvd : ∀ a b, ∃ t, S.coeff a b = π * t := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact hpol a b h
    · exact hall a
    · exact ⟨0, by rw [S.upper h, mul_zero]⟩
  choose t ht using hdvd
  set S1 : QuadForm R 3 := QuadForm.ofUpper t with hS1
  have hcoeff : ∀ a b, S.coeff a b = π * S1.coeff a b := by
    intro a b
    simp only [hS1, QuadForm.ofUpper, Matrix.of_apply]
    split_ifs with h
    · exact ht a b
    · rw [S.upper (lt_of_not_ge h), mul_zero]
  set res := IsLocalRing.residue R
  obtain ⟨zb, hz0, hz⟩ := exists_isotropic_ternary (S1.map res)
  choose x hx using fun i => IsLocalRing.residue_surjective (zb i)
  have hzx : zb = fun i => res (x i) := funext fun i => (hx i).symm
  subst hzx
  have h1 : π ∣ S1.eval x := by rw [← residue_eq_zero_iff_dvd_rd hπ, ← hz, eval_map_comp']
  have h2 : π ^ 2 ∣ S.eval x := by
    rw [eval_of_coeff_mul π hcoeff, pow_two]; exact mul_dvd_mul_left π h1
  apply hz0
  funext i
  exact (residue_eq_zero_iff_dvd_rd hπ _).2 (hmax x h2 i)

/-- The upper unipotent matrix with first row $(1, -s_0, -s_1)$. -/
def uniMat {A : Type*} [CommRing A] (s : Fin 2 → A) : Matrix (Fin 3) (Fin 3) A := !![1, -s 0, -s 1; 0, 1, 0; 0, 0, 1]

theorem det_uniMat {A : Type*} [CommRing A] (s : Fin 2 → A) : (uniMat s).det = 1 := by
  simp [uniMat, Matrix.det_fin_three]

/-- **Steps C–E: the shape $\langle u\rangle\perp\pi T$.** A ternary form $S$ over a DVR with finite residue field of characteristic $2$
($\pi \mid 2$, $2 \ne 0$) that is *maximal* ($\pi^2 \mid S(z) \Rightarrow \pi \mid z$) and has $\det H_S \in 8\cdot\square$ (up to even powers
of $\pi$) is $\mathrm{GL}_3(R)$-equivalent to $\langle u\rangle\perp\pi T$ with $u$ a unit, $T$ unimodular and $\bar T$ anisotropic;
moreover $-u\,(c_{01}^2 - 4c_{00}c_{11})(T)$ is the square of a unit. -/
theorem exists_ram_dyadic_shape {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2) (S : QuadForm R 3)
    (hmax : ∀ z : Fin 3 → R, π ^ 2 ∣ S.eval z → ∀ i, π ∣ z i)
    (hdisc : ∃ (i j : ℕ) (w : R), IsUnit w ∧ π ^ (2 * i) * S.hessian.det = 8 * π ^ (2 * j) * w ^ 2) :
    ∃ (W : Matrix (Fin 3) (Fin 3) R) (u : R) (T : QuadForm R 2), IsUnit W.det ∧ IsUnit u ∧ IsUnit T.hessian.det ∧
      (∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) ∧ S.compMat W = splitForm u (π • T) ∧
      ∃ g : R, IsUnit g ∧ -u * (T.coeff 0 1 ^ 2 - 4 * T.coeff 0 0 * T.coeff 1 1) = g ^ 2 := by
  classical
  set res := IsLocalRing.residue R with hres
  have hres0 := residue_eq_zero_iff_dvd_rd hπ
  have h2F : (2 : IsLocalRing.ResidueField R) = 0 := by rw [← map_ofNat res 2, hres0]; exact h2π
  have hsq := sq_bijective_of_two_eq_zero h2F
  have hpol := polar_dvd_of_max hπ h20 h2π S hmax hdisc
  have hHS := hessian_dvd_of_polar h2π S hpol
  obtain ⟨k, hk⟩ := exists_diag_unit_of_max hπ h20 h2π S hmax hdisc
  -- Step C: move the unit to position `0` and kill the other diagonal entries mod `π`
  set S1 := S.compMat (cycMat k) with hS1
  have hW1 : IsUnit (cycMat k : Matrix (Fin 3) (Fin 3) R).det := by rw [det_cycMat]; exact isUnit_one
  have h00 : S1.coeff 0 0 = S.coeff k k := by rw [hS1, compMat_cycMat_coeff_self, add_zero]
  have hc00 : ¬ π ∣ S1.coeff 0 0 := by rw [h00]; exact hk
  have hHS1 : ∀ a b, π ∣ S1.hessian a b := by
    intro a b
    rw [hS1, hessian_compMat]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (Finset.dvd_sum fun m _ =>
      dvd_mul_of_dvd_right (hHS m l) _) _
  have hres00 : res (S1.coeff 0 0) ≠ 0 := fun h => hc00 ((hres0 _).1 h)
  have hroot : ∀ j : Fin 2, ∃ s : R, res s ^ 2 = res (S1.coeff j.succ j.succ) / res (S1.coeff 0 0) := by
    intro j
    obtain ⟨r, hr⟩ := hsq.2 (res (S1.coeff j.succ j.succ) / res (S1.coeff 0 0))
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨s, hr⟩
  choose sv hsv using hroot
  set S2 := S1.compMat (uniMat sv) with hS2
  have hW2 : IsUnit (uniMat sv).det := by rw [det_uniMat]; exact isUnit_one
  have hcol0 : (fun l => uniMat sv l 0) = Pi.single 0 1 := by
    ext l; fin_cases l <;> rfl
  have hcolj : ∀ j : Fin 2, (fun l => uniMat sv l j.succ) = Pi.single j.succ 1 + (-sv j) • Pi.single 0 1 := by
    intro j; ext l; fin_cases j <;> fin_cases l <;> simp [uniMat]
  have hS2_00 : S2.coeff 0 0 = S1.coeff 0 0 := by
    rw [hS2, compMat_coeff, if_pos le_rfl, if_pos rfl, hcol0, eval_single_rd]
  have hS2_jj : ∀ j : Fin 2, π ∣ S2.coeff j.succ j.succ := by
    intro j
    rw [hS2, compMat_coeff, if_pos le_rfl, if_pos rfl, hcolj, eval_add_smul_gen, eval_single_rd, eval_single_rd]
    have key : π ∣ S1.coeff j.succ j.succ + (-sv j) ^ 2 * S1.coeff 0 0 := by
      rw [← hres0, map_add, map_mul, map_pow, map_neg, neg_sq, hsv j, div_mul_cancel₀ _ hres00, ← two_mul, h2F,
        zero_mul]
    have hmid : π ∣ (-sv j) * ((S1.hessian *ᵥ Pi.single j.succ 1) ⬝ᵥ Pi.single 0 1) := by
      rw [dotProduct_comm]; exact dvd_mul_of_dvd_right (dot_dvd_of_dvd _ hHS1 _ _) _
    have e : ∀ a b c : R, a + b + c = (a + c) + b := fun a b c => by ring
    rw [e]; exact dvd_add key hmid
  have hS2_off : ∀ a b : Fin 3, a < b → π ∣ S2.coeff a b := by
    intro a b hab
    rw [hS2, compMat_coeff, if_pos hab.le, if_neg hab.ne]
    exact dot_dvd_of_dvd _ hHS1 _ _
  have hmax2 := hmax_compMat (hmax_compMat hmax hW1) hW2
  have hdisc2 := hdisc_compMat (hdisc_compMat hdisc hW1) hW2
  rw [← hS1, ← hS2] at hmax2 hdisc2
  -- Step D: `T = (S₂)_tail / π` is unimodular with anisotropic reduction
  have hdvdT : ∀ a b : Fin 2, ∃ t, S2.coeff a.succ b.succ = π * t := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact hS2_off _ _ (Fin.succ_lt_succ_iff.mpr h)
    · exact hS2_jj a
    · exact ⟨0, by rw [mul_zero]; exact S2.upper (Fin.succ_lt_succ_iff.mpr h)⟩
  choose t ht using hdvdT
  set T : QuadForm R 2 := QuadForm.ofUpper t with hT
  have htail : S2.tail = π • T := by
    ext a b
    simp only [tail_coeff, smul_coeff, Matrix.smul_apply, smul_eq_mul, hT, QuadForm.ofUpper, Matrix.of_apply]
    split_ifs with h
    · exact ht a b
    · rw [mul_zero]; exact S2.upper (Fin.succ_lt_succ_iff.mpr (lt_of_not_ge h))
  have hanisoT : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i := by
    intro x hx i
    have h1 : S2.eval (Fin.cons 0 x) = π * T.eval x := by
      rw [eval_cons_three, htail, eval_smul_form_rd]; ring
    have := hmax2 (Fin.cons 0 x) (by rw [h1, pow_two]; exact mul_dvd_mul_left π hx) i.succ
    simpa using this
  have hbT : ¬ π ∣ T.coeff 0 1 := by
    intro hb
    by_cases ha : π ∣ T.coeff 0 0
    · have := hanisoT ![1, 0] (by rw [eval_binary]; simpa using ha) 0
      exact hπ.not_isUnit (isUnit_of_dvd_unit (by simpa using this) isUnit_one)
    · obtain ⟨r, hr⟩ := hsq.2 (res (T.coeff 1 1) / res (T.coeff 0 0))
      obtain ⟨s', rfl⟩ := IsLocalRing.residue_surjective r
      have hr' : res s' ^ 2 = res (T.coeff 1 1) / res (T.coeff 0 0) := hr
      have hres0a : res (T.coeff 0 0) ≠ 0 := fun h => ha ((hres0 _).1 h)
      have hv : π ∣ T.eval ![s', 1] := by
        rw [eval_binary]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
        have h1 : π ∣ T.coeff 0 0 * s' * s' + T.coeff 1 1 := by
          rw [← hres0, map_add, map_mul, map_mul, show res (T.coeff 0 0) * res s' * res s' =
            res s' ^ 2 * res (T.coeff 0 0) by ring, hr', div_mul_cancel₀ _ hres0a, ← two_mul, h2F, zero_mul]
        have e : ∀ a b c : R, a + b + c = (a + c) + b := fun a b c => by ring
        rw [e]; exact dvd_add h1 (dvd_mul_of_dvd_left hb _)
      have := hanisoT _ hv 1
      exact hπ.not_isUnit (isUnit_of_dvd_unit (by simpa using this) isUnit_one)
  have hTu : IsUnit T.hessian.det := isUnit_det_hessian_binary hπ h2π T hbT
  -- Step E: orthogonalize `e₀`
  have hdvd0 : ∀ j : Fin 2, ∃ d, S2.coeff 0 j.succ = π * d := fun j => hS2_off 0 j.succ (Fin.succ_pos j)
  choose dv hdv using hdvd0
  set z := T.hessian⁻¹ *ᵥ dv with hz
  have hHtail : S2.tail.hessian = π • T.hessian := by rw [htail]; ext; simp [hessian, smul_coeff]; ring
  have hz' : S2.tail.hessian *ᵥ z = fun j => S2.coeff 0 j.succ := by
    rw [hHtail, smul_mulVec, hz, mulVec_mulVec, mul_nonsing_inv _ hTu, one_mulVec]
    ext j; simp [hdv]
  have horth := compMat_stabMat_orth S2 z hz'
  rw [htail] at horth
  have hW3 : IsUnit (stabMat (1 : R) (-z)).det := by rw [det_stabMat]; exact isUnit_one
  set u := S2.eval (Fin.cons 1 (-z)) with hu
  have huu : IsUnit u := by
    refine dvr_isUnit_of_not_dvd hπ fun h => hc00 ?_
    rw [hu, eval_cons_three, htail, eval_smul_form_rd, mul_one, one_mul, hS2_00] at h
    have h1 : π ∣ (fun j : Fin 2 => S2.coeff 0 j.succ) ⬝ᵥ -z := by
      simp only [dotProduct]
      exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left ⟨dv j, hdv j⟩ _
    have h2 := dvd_sub h (dvd_mul_right π (T.eval (-z)))
    rw [add_sub_cancel_right] at h2
    have h3 := dvd_sub h2 h1
    rwa [add_sub_cancel_right, mul_one] at h3
  have hdisc3 := hdisc_compMat hdisc2 hW3
  rw [horth] at hdisc3
  refine ⟨cycMat k * uniMat sv * stabMat 1 (-z), u, T, ?_, huu, hTu, hanisoT, ?_, ?_⟩
  · rw [det_mul, det_mul]; exact (hW1.mul hW2).mul hW3
  · rw [← compMat_mul, ← compMat_mul, ← hS1, ← hS2, horth]
  · -- the square class of `-u · disc T`
    obtain ⟨e, t2, he1, ht2, h2e⟩ := exists_two_eq hπ h20 h2π
    obtain ⟨i, j, w, hw, h⟩ := hdisc3
    rw [det_hessian_splitForm, show (π • T).hessian = π • T.hessian by ext; simp [hessian, smul_coeff]; ring,
      det_smul, Fintype.card_fin] at h
    have h' : π ^ (2 * i + 2 + e) * (t2 * u * T.hessian.det) = π ^ (2 * j + e + e + e) * (t2 ^ 3 * w ^ 2) := by
      have h8 : (8 : R) = 2 * 2 * 2 := by norm_num
      rw [h8, h2e] at h
      rw [pow_add, pow_add, pow_add, pow_add, pow_add]
      linear_combination h
    have hD := hTu
    have hval := pow_unit_inj hπ ((ht2.mul huu).mul hTu) ((ht2.pow 3).mul (hw.pow 2)) h'
    rw [hval] at h'
    have h'' := mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) h'
    refine ⟨t2 * w, ht2.mul hw, ?_⟩
    have h3 : t2 * (u * T.hessian.det - t2 ^ 2 * w ^ 2) = 0 := by linear_combination h''
    have h4 := (mul_eq_zero.mp h3).resolve_left ht2.ne_zero
    rw [det_hessian_binary] at h4
    linear_combination h4

end ShapeDVR

end QuadFormsKB.Tamagawa
