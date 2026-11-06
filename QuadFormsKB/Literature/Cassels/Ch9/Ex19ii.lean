/-
# Cassels, Chapter 9, Example 19 (ii): the integral automorphs of $x_0^2 + x_1^2 - x_2^2 - x_3^2$

Formalization of J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 9, *Examples*, Ex. 19 (ii), p. 167: determine
the group $O_{\mathbb Z}(f)$ for $f(x) = x_1^2 + x_2^2 - x_3^2 - x_4^2$ (the book cites Wall 1964 and gives no answer).

## Conventions

* Indices are 0-based: the book's $x_1, \dots, x_4$ are $x_0, \dots, x_3$ here.
* "The group of integral automorphs" is `Siegel.Aut f`, the subgroup of $\mathrm{GL}_4(\mathbb Z)$ of $g$ with
  $f(gx) = f(x)$; "determine" is answered by an explicit finite generating set.

## What is formalized

`ex19_ii`: `Siegel.Aut f4 = Subgroup.closure ex19iiGens`, where `f4` is $x_0^2 + x_1^2 - x_2^2 - x_3^2$ and the generators
(`ex19iiGens`) are the four sign changes, the transpositions of $(x_0,x_1)$ and of $(x_2,x_3)$, the symmetry `rA` in
$(1,1,1,0)$ (norm $1$), the symmetry `rB` in $(0,1,1,1)$ (norm $-1$) and one further automorph `tt` that maps $e_0$ to
$(1,1,1,0)$. Unconditional.

## What is reconstructed

The book gives only the reference. The method is that of Ex. 16--19 (i): a descent on the norm-$1$ vector $a = g e_0$.
After sign changes and transpositions ($a \ge 0$, $a_1 \le a_0$, $a_3 \le a_2$) the symmetry `rA` strictly lowers the
height $a_0^2 + a_1^2$ unless $a = e_0$ or $a = (1,1,1,0)$ (`arith_step`); the latter is moved to $e_0$ by $t^{-1}$.
The stabilizer of $e_0$ is the group of integral automorphs of $x_1^2 - x_2^2 - x_3^2$, which is Ex. 19 (i)
(`ex19_i`), transported by the block embedding `embGL` ($g \mapsto \operatorname{diag}(1,g)$). All proofs and the
generators (found by a numerical search) are new.
-/
import QuadFormsKB.Literature.Cassels.Ch9.Ex16to19

open Matrix QuadFormsKB QuadFormsKB.Cassels.Ch9Ex16

namespace QuadFormsKB.Cassels.Ch9Ex19ii

/-- The form $f(x_0,x_1,x_2,x_3) = x_0^2 + x_1^2 - x_2^2 - x_3^2$. -/
def f4 : QuadForm ℤ 4 :=
  QuadForm.ofUpper ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

/-- Helper: $f(v) = v_0^2 + v_1^2 - v_2^2 - v_3^2$. -/
theorem f4_eval (v : Fin 4 → ℤ) : f4.eval v = v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  simp [f4, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_four]
  ring

/-- Helper: the arithmetic of the descent. For integers $a \ge 0$ with $a_1 \le a_0$, $a_3 \le a_2$,
$a_0^2 + a_1^2 - a_2^2 - a_3^2 = 1$ and $a \ne e_0, (1,1,1,0)$ one has $a_2 < a_0 + a_1 < 2a_2$. -/
theorem arith_bounds (a0 a1 a2 a3 : ℤ) (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (s01 : a1 ≤ a0) (s23 : a3 ≤ a2) (hf : a0 ^ 2 + a1 ^ 2 - a2 ^ 2 - a3 ^ 2 = 1)
    (hne : ¬ (a0 = 1 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0)) (hne' : ¬ (a0 = 1 ∧ a1 = 1 ∧ a2 = 1 ∧ a3 = 0)) :
    a2 < a0 + a1 ∧ a0 + a1 < 2 * a2 := by
  have ha2 : 1 ≤ a2 := by
    by_contra hc
    have e2 : a2 = 0 := by omega
    have e3 : a3 = 0 := by omega
    subst e2 e3
    have : a0 ≤ 1 := by nlinarith
    have : a0 = 1 := by nlinarith
    have : a1 = 0 := by subst this; nlinarith
    exact hne ⟨by assumption, by assumption, rfl, rfl⟩
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [mul_nonneg h0 h1, mul_nonneg h2 h3]
  · by_contra hc
    push Not at hc
    -- d = a0 - a1
    have hd : (a0 - a1) ^ 2 ≤ 2 := by nlinarith
    have hd' : a0 - a1 ≤ 1 := by nlinarith
    rcases (by omega : a0 - a1 = 0 ∨ a0 - a1 = 1) with e | e
    · have : a0 = a1 := by omega
      subst this
      -- 2 a0^2 = 1 + a2^2 + a3^2 and 2 a0 >= 2 a2
      have : a2 ≤ a0 := by omega
      have h5 : a2 ^ 2 + a3 ^ 2 + 1 = 2 * a0 ^ 2 := by nlinarith
      have h6 : a0 = a2 := by nlinarith
      subst h6
      have : a3 ^ 2 + 1 = a0 ^ 2 := by nlinarith
      have hlt : a3 < a0 := by nlinarith
      have : a3 = 0 := by nlinarith
      subst this
      have : a0 = 1 := by nlinarith
      exact hne' ⟨this, this, this, rfl⟩
    · have : a0 = a1 + 1 := by omega
      subst this
      have : a2 ≤ a1 := by omega
      have h5 : a2 ^ 2 + a3 ^ 2 + 1 = 2 * a1 ^ 2 + 2 * a1 + 1 := by nlinarith
      have h6 : a2 ^ 2 + a3 ^ 2 = 2 * a1 ^ 2 + 2 * a1 := by omega
      nlinarith

/-- Helper: the key descent inequality. -/
theorem arith_step (a0 a1 a2 a3 : ℤ) (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (s01 : a1 ≤ a0) (s23 : a3 ≤ a2) (hf : a0 ^ 2 + a1 ^ 2 - a2 ^ 2 - a3 ^ 2 = 1)
    (hne : ¬ (a0 = 1 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0)) (hne' : ¬ (a0 = 1 ∧ a1 = 1 ∧ a2 = 1 ∧ a3 = 0)) :
    (a0 - 2 * (a0 + a1 - a2)) ^ 2 + (a1 - 2 * (a0 + a1 - a2)) ^ 2 < a0 ^ 2 + a1 ^ 2 := by
  obtain ⟨b1, b2⟩ := arith_bounds a0 a1 a2 a3 h0 h1 h2 h3 s01 s23 hf hne hne'
  nlinarith [mul_pos (show 0 < a0 + a1 - a2 by omega) (show 0 < 2 * a2 - (a0 + a1) by omega)]

/-! ### The generators -/

/-- Helper: the dot product of $\varphi = (2,2,-2,0)$ with $v = (1,1,1,0)$ is $2$. -/
theorem rA_dot : (![2, 2, -2, 0] : Fin 4 → ℤ) ⬝ᵥ ![1, 1, 1, 0] = 2 := by
  simp [dotProduct, Fin.sum_univ_four]

/-- Helper: the dot product of $\varphi = (0,-2,2,2)$ with $v = (0,1,1,1)$ is $2$. -/
theorem rB_dot : (![0, -2, 2, 2] : Fin 4 → ℤ) ⬝ᵥ ![0, 1, 1, 1] = 2 := by
  simp [dotProduct, Fin.sum_univ_four]

/-- The symmetry in $(1,1,1,0)$, a vector with $f = 1$: $x \mapsto x - 2(x_0 + x_1 - x_2)(1,1,1,0)$. -/
def rA : GL (Fin 4) ℤ := reflGL ![2, 2, -2, 0] ![1, 1, 1, 0] rA_dot

/-- The symmetry in $(0,1,1,1)$, a vector with $f = -1$: $x \mapsto x + 2(x_1 - x_2 - x_3)(0,1,1,1)$. -/
def rB : GL (Fin 4) ℤ := reflGL ![0, -2, 2, 2] ![0, 1, 1, 1] rB_dot

/-- Helper: coordinates of $r_A x$. -/
theorem rA_apply (x : Fin 4 → ℤ) : rA.val *ᵥ x =
    ![x 0 - 2 * (x 0 + x 1 - x 2), x 1 - 2 * (x 0 + x 1 - x 2), x 2 - 2 * (x 0 + x 1 - x 2), x 3] := by
  rw [rA, reflGL_apply]
  ext i; fin_cases i <;> simp [dotProduct, Fin.sum_univ_four] <;> ring

/-- Helper: coordinates of $r_B x$. -/
theorem rB_apply (x : Fin 4 → ℤ) : rB.val *ᵥ x =
    ![x 0, x 1 + 2 * (x 1 - x 2 - x 3), x 2 + 2 * (x 1 - x 2 - x 3), x 3 + 2 * (x 1 - x 2 - x 3)] := by
  rw [rB, reflGL_apply]
  ext i; fin_cases i <;> simp [dotProduct, Fin.sum_univ_four] <;> ring

/-- The automorph $t$ with columns $(1,1,1,0), (-1,1,0,-1), (-1,0,-1,-1), (0,-1,-1,1)$; it sends $e_0$ to $(1,1,1,0)$.
Its inverse is $F t^{\mathsf T} F$ with $F = \operatorname{diag}(1,1,-1,-1)$. -/
def tt : GL (Fin 4) ℤ where
  val := !![1, -1, -1, 0; 1, 1, 0, -1; 1, 0, -1, -1; 0, -1, -1, 1]
  inv := !![1, 1, -1, 0; -1, 1, 0, 1; 1, 0, -1, -1; 0, 1, -1, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- Helper: coordinates of $t x$. -/
theorem tt_apply (x : Fin 4 → ℤ) : tt.val *ᵥ x =
    ![x 0 - x 1 - x 2, x 0 + x 1 - x 3, x 0 - x 2 - x 3, -x 1 - x 2 + x 3] := by
  ext i; fin_cases i <;> simp [tt, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Helper: coordinates of $t^{-1} x$. -/
theorem tt_inv_apply (x : Fin 4 → ℤ) : (tt⁻¹).val *ᵥ x =
    ![x 0 + x 1 - x 2, -x 0 + x 1 + x 3, x 0 - x 2 - x 3, x 1 - x 2 + x 3] := by
  ext i; fin_cases i <;> simp [tt, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Helper: $\mathrm{swap}(x_0,x_1)$ on vectors. -/
theorem swap01_apply (v : Fin 4 → ℤ) : (swapGL 0 1).val *ᵥ v = ![v 1, v 0, v 2, v 3] := by
  rw [swapGL, permGL_apply]
  ext i; fin_cases i <;> simp [Equiv.swap_apply_def]

/-- Helper: $\mathrm{swap}(x_2,x_3)$ on vectors. -/
theorem swap23_apply (v : Fin 4 → ℤ) : (swapGL 2 3).val *ᵥ v = ![v 0, v 1, v 3, v 2] := by
  rw [swapGL, permGL_apply]
  ext i; fin_cases i <;> simp [Equiv.swap_apply_def]

/-- Helper: $r_A$ is an integral automorph of $f$. -/
theorem rA_mem : rA ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x; rw [rA_apply, f4_eval, f4_eval]; simp; ring

/-- Helper: $r_B$ is an integral automorph of $f$. -/
theorem rB_mem : rB ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x; rw [rB_apply, f4_eval, f4_eval]; simp; ring

/-- Helper: $t$ is an integral automorph of $f$. -/
theorem tt_mem : tt ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x; rw [tt_apply, f4_eval, f4_eval]; simp; ring

/-- Helper: the sign changes are integral automorphs of $f$. -/
theorem flip_mem4 (i : Fin 4) : flipGL i ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x
  rw [flipGL_apply, f4_eval, f4_eval]
  have hp : ∀ j, (Function.update x i (-x i) j) ^ 2 = x j ^ 2 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp only [hp]

/-- Helper: $\mathrm{swap}(x_0,x_1)$ is an integral automorph of $f$. -/
theorem swap01_mem : swapGL 0 1 ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x; rw [swap01_apply, f4_eval, f4_eval]; simp; ring

/-- Helper: $\mathrm{swap}(x_2,x_3)$ is an integral automorph of $f$. -/
theorem swap23_mem : swapGL 2 3 ∈ Siegel.Aut f4 := by
  rw [mem_Aut_iff]; intro x; rw [swap23_apply, f4_eval, f4_eval]; simp; ring

/-- **The generators of the integral automorphs of $x_0^2 + x_1^2 - x_2^2 - x_3^2$:** the four sign changes, the transpositions
of $(x_0,x_1)$ and of $(x_2,x_3)$, the symmetries `rA` in $(1,1,1,0)$ and `rB` in $(0,1,1,1)$, and the automorph `tt`. -/
def ex19iiGens : Set (GL (Fin 4) ℤ) :=
  {tt, rA, rB, swapGL 0 1, swapGL 2 3} ∪ Set.range (flipGL (n := 4))

/-- Helper: the generators are integral automorphs. -/
theorem ex19ii_closure_le : Subgroup.closure ex19iiGens ≤ Siegel.Aut f4 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (hg | ⟨i, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    exacts [tt_mem, rA_mem, rB_mem, swap01_mem, swap23_mem]
  · exact flip_mem4 i

/-- Helper: sign changes lie in the group generated by `ex19iiGens`. -/
theorem flip_G (i : Fin 4) : flipGL i ∈ Subgroup.closure ex19iiGens :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

/-- Helper: normalization. Some element of the group moves $a$ to a vector with non-negative coordinates, $b_1 \le b_0$,
$b_3 \le b_2$ and the same $a_0^2 + a_1^2$. -/
theorem normalize (a : Fin 4 → ℤ) : ∃ P ∈ Subgroup.closure ex19iiGens,
    (∀ i, 0 ≤ (P.val *ᵥ a) i) ∧ (P.val *ᵥ a) 1 ≤ (P.val *ᵥ a) 0 ∧ (P.val *ᵥ a) 3 ≤ (P.val *ᵥ a) 2 ∧
    (P.val *ᵥ a) 0 ^ 2 + (P.val *ᵥ a) 1 ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  obtain ⟨D, hD, hDa⟩ := abs_fix (Subgroup.closure ex19iiGens) flip_G a
  have s01 : swapGL 0 1 ∈ Subgroup.closure ex19iiGens := Subgroup.subset_closure (Or.inl (by simp))
  have s23 : swapGL 2 3 ∈ Subgroup.closure ex19iiGens := Subgroup.subset_closure (Or.inl (by simp))
  have c0 : (D.val *ᵥ a) 0 = |a 0| := by rw [hDa]
  have c1 : (D.val *ᵥ a) 1 = |a 1| := by rw [hDa]
  have c2 : (D.val *ᵥ a) 2 = |a 2| := by rw [hDa]
  have c3 : (D.val *ᵥ a) 3 = |a 3| := by rw [hDa]
  rcases le_total |a 1| |a 0| with h01 | h01 <;> rcases le_total |a 3| |a 2| with h23 | h23
  · refine ⟨D, hD, fun i => ?_, by rw [c0, c1]; exact h01, by rw [c2, c3]; exact h23, ?_⟩
    · rw [hDa]; exact abs_nonneg _
    · rw [c0, c1]; simp
  · refine ⟨swapGL 2 3 * D, mul_mem s23 hD, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec, swap23_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, c0, c1, c2, c3]
    · intro i; fin_cases i <;> simp [abs_nonneg]
    · exact h01
    · exact h23
    · simp
  · refine ⟨swapGL 0 1 * D, mul_mem s01 hD, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec, swap01_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, c0, c1, c2, c3]
    · intro i; fin_cases i <;> simp [abs_nonneg]
    · exact h01
    · exact h23
    · simp; ring
  · refine ⟨swapGL 2 3 * (swapGL 0 1 * D), mul_mem s23 (mul_mem s01 hD), ?_, ?_, ?_, ?_⟩ <;>
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec, swap01_apply, swap23_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, c0, c1, c2, c3]
    · intro i; fin_cases i <;> simp [abs_nonneg]
    · exact h01
    · exact h23
    · simp; ring

/-- Helper: $e_0 = (1,0,0,0)$. -/
theorem e0_eq : (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = ![1, 0, 0, 0] := by
  ext i; fin_cases i <;> simp

/-- Helper: descent. Every integer vector $a$ with $f(a) = 1$ is moved to $e_0$ by an element of the group generated by
`ex19iiGens`; induction on $a_0^2 + a_1^2$. -/
theorem ex19ii_desc : ∀ (N : ℕ) (a : Fin 4 → ℤ), (a 0 ^ 2 + a 1 ^ 2).toNat = N → f4.eval a = 1 →
    ∃ h ∈ Subgroup.closure ex19iiGens, h.val *ᵥ a = Pi.single 0 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a hN hf
    obtain ⟨P, hP, hnn, s01, s23, hsq⟩ := normalize a
    have hPA : P ∈ Siegel.Aut f4 := ex19ii_closure_le hP
    set c := P.val *ᵥ a with hc
    have hfc : f4.eval c = 1 := by rw [hc, hPA a]; exact hf
    rw [f4_eval] at hfc
    by_cases he : c 0 = 1 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0
    · refine ⟨P, hP, ?_⟩
      rw [e0_eq, ← hc]; ext i; fin_cases i <;> simp [he.1, he.2.1, he.2.2.1, he.2.2.2]
    by_cases he' : c 0 = 1 ∧ c 1 = 1 ∧ c 2 = 1 ∧ c 3 = 0
    · refine ⟨tt⁻¹ * P, mul_mem (inv_mem (Subgroup.subset_closure (Or.inl (by simp)))) hP, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hc, tt_inv_apply, e0_eq]
      ext i; fin_cases i <;> simp [he'.1, he'.2.1, he'.2.2.1, he'.2.2.2]
    have hstep := arith_step (c 0) (c 1) (c 2) (c 3) (hnn 0) (hnn 1) (hnn 2) (hnn 3) s01 s23 hfc he he'
    set b := rA.val *ᵥ c with hb
    have hbf : f4.eval b = 1 := by
      rw [hb, rA_mem c, f4_eval]; exact hfc
    have hlt : (b 0 ^ 2 + b 1 ^ 2).toNat < N := by
      rw [← hN, ← hsq]
      have : b 0 ^ 2 + b 1 ^ 2 < c 0 ^ 2 + c 1 ^ 2 := by
        rw [hb, rA_apply]; simpa using hstep
      have := sq_nonneg (b 0); have := sq_nonneg (b 1)
      omega
    obtain ⟨h', hh', hh'b⟩ := ih _ hlt b rfl hbf
    have hrA : rA ∈ Subgroup.closure ex19iiGens := Subgroup.subset_closure (Or.inl (by simp))
    refine ⟨h' * rA * P, mul_mem (mul_mem hh' hrA) hP, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hc, ← hb]
    exact hh'b

/-! ### The stabilizer of $e_0$ -/

/-- Helper: the block matrix $\operatorname{diag}(1, M)$ of size $4$ for a $3 \times 3$ matrix `M`. -/
def blk (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) (Fin.cases (motive := fun _ => ℤ) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℤ) 0 (fun j' => M i' j') j) i

/-- Helper: `blk M` has entry $M_{ij}$ at $(i+1, j+1)$. -/
@[simp] theorem blk_ss (M : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) : blk M i.succ j.succ = M i j := rfl
/-- Helper: the corner entry of `blk M` is $1$. -/
@[simp] theorem blk_00 (M : Matrix (Fin 3) (Fin 3) ℤ) : blk M 0 0 = 1 := rfl
/-- Helper: the first row of `blk M` is $e_0$. -/
@[simp] theorem blk_0s (M : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) : blk M 0 j.succ = 0 := rfl
/-- Helper: the first column of `blk M` is $e_0$. -/
@[simp] theorem blk_s0 (M : Matrix (Fin 3) (Fin 3) ℤ) (i : Fin 3) : blk M i.succ 0 = 0 := rfl

/-- Helper: `blk` is multiplicative. -/
theorem blk_mul (M N : Matrix (Fin 3) (Fin 3) ℤ) : blk (M * N) = blk M * blk N := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Helper: `blk 1 = 1`. -/
theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- Helper: `blk` is injective. -/
theorem blk_inj {M N : Matrix (Fin 3) (Fin 3) ℤ} (h : blk M = blk N) : M = N := by
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  simpa using this

/-- Helper: `blk` as a monoid homomorphism. -/
def blkHom : Matrix (Fin 3) (Fin 3) ℤ →* Matrix (Fin 4) (Fin 4) ℤ where
  toFun := blk
  map_one' := blk_one
  map_mul' := blk_mul

/-- Helper: the embedding $\mathrm{GL}_3(\mathbb Z) \to \mathrm{GL}_4(\mathbb Z)$, $g \mapsto \operatorname{diag}(1, g)$. -/
def embGL : GL (Fin 3) ℤ →* GL (Fin 4) ℤ := Units.map blkHom

/-- Helper: the action of `embGL g` on a vector `x` is `Fin.cons` of its first coordinate $x_0$ and the image under `g` of
the remaining coordinates. -/
theorem embGL_apply (g : GL (Fin 3) ℤ) (x : Fin 4 → ℤ) :
    (embGL g).val *ᵥ x = Fin.cons (x 0) (g.val *ᵥ fun i => x i.succ) := by
  ext i
  refine Fin.cases ?_ (fun i' => ?_) i <;>
    simp [embGL, blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Helper: `Fin.cons` on four coordinates as a literal vector. -/
theorem cons_four (a : ℤ) (w : Fin 3 → ℤ) : (Fin.cons a w : Fin 4 → ℤ) = ![a, w 0, w 1, w 2] := by
  ext i; fin_cases i <;> rfl

/-- Helper: the forms agree: $f(0, y) = y_0^2 - y_1^2 - y_2^2$. -/
theorem f4_cons (y : Fin 3 → ℤ) : f4.eval (Fin.cons 0 y : Fin 4 → ℤ) = (lorentz 2).eval y := by
  rw [cons_four, f4_eval, lorentz2_eval]; simp

/-- Helper: $f(e_0 + c) = 1 + 2c_0 + f(c)$. -/
theorem f4_e0_add (c : Fin 4 → ℤ) :
    f4.eval (Pi.single 0 (1 : ℤ) + c) = 1 + 2 * c 0 + f4.eval c := by
  rw [f4_eval, f4_eval]; simp; ring

/-- Helper: an automorph fixing $e_0$ has $T_{0j} = 0$ for all $j \ne 0$. -/
theorem stab_row (T : GL (Fin 4) ℤ) (hT : T ∈ Siegel.Aut f4)
    (he : T.val *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 0 1) (j : Fin 4) (hj : j ≠ 0) :
    T.val 0 j = 0 := by
  have h1 := hT (Pi.single 0 1 + Pi.single j 1)
  rw [Matrix.mulVec_add, he, f4_e0_add, f4_e0_add, hT] at h1
  have h2 : (Pi.single j (1 : ℤ) : Fin 4 → ℤ) 0 = 0 := by simp [Ne.symm hj]
  rw [h2] at h1
  have h3 : (T.val *ᵥ (Pi.single j (1 : ℤ) : Fin 4 → ℤ)) 0 = T.val 0 j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h3] at h1
  omega

/-- Helper: an automorph fixing $e_0$ is a block matrix $\operatorname{diag}(1, A)$. -/
theorem stab_blk (T : GL (Fin 4) ℤ) (hT : T ∈ Siegel.Aut f4)
    (he : T.val *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 0 1) :
    T.val = blk (Matrix.of fun i j => T.val i.succ j.succ) := by
  have col : ∀ i : Fin 4, T.val i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun he i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simpa using col 0
  · simpa using stab_row T hT he j'.succ (Fin.succ_ne_zero _)
  · simpa using col i'.succ
  · simp

/-- Helper: the embedding of the symmetry `rho2` is `rB`. -/
theorem emb_rho2 : embGL rho2 = rB := by
  apply gl_ext; intro v
  rw [embGL_apply, cons_four, rB_apply]
  ext i; fin_cases i <;> simp [rho2_apply]

/-- Helper: the embedding of a sign change is a sign change. -/
theorem emb_flip (i : Fin 3) : embGL (flipGL i) = flipGL i.succ := by
  apply gl_ext; intro v
  rw [embGL_apply, cons_four, flipGL_apply, flipGL_apply]
  fin_cases i <;> (ext j; fin_cases j <;> simp)

/-- Helper: the embedding of the transposition of $x_1, x_2$ is the transposition of $x_2, x_3$. -/
theorem emb_swap : embGL (permGL (Equiv.swap (1 : Fin 3) 2)) = swapGL 2 3 := by
  apply gl_ext; intro v
  rw [embGL_apply, cons_four, swap23_apply, permGL_apply]
  ext j; fin_cases j <;> simp [Equiv.swap_apply_def]

/-- Helper: a permutation of $\{0,1,2\}$ fixing $0$ is the identity or the transposition of $1, 2$. -/
theorem perm_fix0 : ∀ π : Equiv.Perm (Fin 3), π 0 = 0 → π = 1 ∨ π = Equiv.swap 1 2 := by decide

/-- Helper: the image of the generators of Ex. 19 (i) lies in the group generated by `ex19iiGens`. -/
theorem emb_gens : embGL '' ex19iGens ⊆ (Subgroup.closure ex19iiGens : Set (GL (Fin 4) ℤ)) := by
  rintro _ ⟨g, ((rfl | ⟨i, rfl⟩) | ⟨π, h0, rfl⟩), rfl⟩
  · rw [emb_rho2]; exact Subgroup.subset_closure (Or.inl (by simp))
  · rw [emb_flip]; exact flip_G _
  · rcases perm_fix0 π h0 with rfl | rfl
    · simp only [map_one]; exact one_mem _
    · rw [emb_swap]; exact Subgroup.subset_closure (Or.inl (by simp))

/-- Helper: **the stabilizer of $e_0$** lies in the group generated by `ex19iiGens`. -/
theorem stab_mem (T : GL (Fin 4) ℤ) (hT : T ∈ Siegel.Aut f4)
    (he : T.val *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 0 1) :
    T ∈ Subgroup.closure ex19iiGens := by
  have hTi : T⁻¹ ∈ Siegel.Aut f4 := inv_mem hT
  have hei : (T⁻¹).val *ᵥ (Pi.single 0 (1 : ℤ) : Fin 4 → ℤ) = Pi.single 0 1 := by
    have := congrArg (fun v => (T⁻¹).val *ᵥ v) he
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this.symm
  have hb := stab_blk T hT he
  have hbi := stab_blk T⁻¹ hTi hei
  set A : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => T.val i.succ j.succ with hA
  set Ai : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => (T⁻¹).val i.succ j.succ with hAi
  have h1 : A * Ai = 1 := by
    apply blk_inj
    rw [blk_mul, ← hb, ← hbi, blk_one]
    exact T.mul_inv
  have h2 : Ai * A = 1 := by
    apply blk_inj
    rw [blk_mul, ← hb, ← hbi, blk_one]
    exact T.inv_mul
  let T' : GL (Fin 3) ℤ := ⟨A, Ai, h1, h2⟩
  have hTT : embGL T' = T := by
    apply Units.ext
    show blk A = T.val
    exact hb.symm
  have hT'A : T' ∈ Siegel.Aut (lorentz 2) := by
    rw [mem_Aut_iff]; intro y
    have e1 : (embGL T').val *ᵥ (Fin.cons 0 y : Fin 4 → ℤ) = Fin.cons 0 (T'.val *ᵥ y) := by
      rw [embGL_apply]; simp [Fin.cons_succ]
    rw [← f4_cons, ← f4_cons y, ← e1, hTT, hT]
  have hmem : T' ∈ Subgroup.closure ex19iGens := by rw [← ex19_i]; exact hT'A
  have : embGL T' ∈ Subgroup.closure ex19iiGens := by
    have hm : embGL T' ∈ (Subgroup.closure ex19iGens).map embGL := Subgroup.mem_map_of_mem _ hmem
    rw [MonoidHom.map_closure] at hm
    exact (Subgroup.closure_le _ |>.2 emb_gens) hm
  rwa [hTT] at this

/-- **Cassels, Ch. 9, Ex. 19 (ii), p. 167.** The group of integral automorphs of $f = x_0^2 + x_1^2 - x_2^2 - x_3^2$ is
generated by the four sign changes, the transpositions of $(x_0,x_1)$ and of $(x_2,x_3)$, the symmetry in $(1,1,1,0)$, the
symmetry in $(0,1,1,1)$ and the automorph `tt` (`ex19iiGens`). *Answer computed (the book only cites Wall 1964), proved
by a descent on $a_0^2 + a_1^2$ for $a = g e_0$ and the stabilizer of $e_0$ (Ex. 19 (i)).* -/
@[kb "cassels1978" "Ch. 9, Ex. 19 (ii), p. 167"]
theorem ex19_ii : Siegel.Aut f4 = Subgroup.closure ex19iiGens := by
  refine le_antisymm (fun g hg => ?_) ex19ii_closure_le
  have hfe : f4.eval (g.val *ᵥ (Pi.single 0 1 : Fin 4 → ℤ)) = 1 := by
    rw [hg, e0_eq, f4_eval]; simp
  obtain ⟨h, hh, hhg⟩ := ex19ii_desc _ _ rfl hfe
  have hA : h * g ∈ Siegel.Aut f4 := mul_mem (ex19ii_closure_le hh) hg
  have hs := stab_mem (h * g) hA (by rw [Units.val_mul, ← Matrix.mulVec_mulVec]; exact hhg)
  have := mul_mem (inv_mem hh) hs
  simpa using this

end QuadFormsKB.Cassels.Ch9Ex19ii
