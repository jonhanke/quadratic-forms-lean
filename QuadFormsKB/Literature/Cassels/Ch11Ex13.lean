/-
# Cassels, Chapter 11, Example 13: a primitive $t$ in Lemma 9.3

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Example 13, p. 254, on Lemma 9.3
(pp. 243–245).

**What is proved.** `Cassels.lemma93Primitive_holds : Lemma93Primitive`: for an odd prime $p$ and a regular quaternary
form $Q$ over $\mathbb Z_p$ that is isotropic over $\mathbb Q_p$, the vector $t$ of Lemma 9.3 can be chosen primitive.

**Proof.** Cassels gives no hint. Since $p$ is odd, $Q$ has an orthogonal basis $e_0, \dots, e_3$ of $\mathbb Z_p^4$ with
$Q(e_i) = p^{a_i}\varepsilon_i$, $\varepsilon_i$ units (the local normal form, `LocalDensity.DVR.dvr_jinv_complete_aux`).
We take $t = e_j$ (primitive) and $\Delta$ with basis $p^{b_i}e_i, p^{b_k}e_k, p^{b_l}e_l$, $\{i, j, k, l\} = \{0, 1, 2, 3\}$,
where $a_i + 2b_i = a_k + 2b_k = m$:

* (ii) holds for every $c \in \Delta$, since the $e_j$-coordinate of $t + c$ is $1$;
* (iii): $\Delta$ has the orthogonal summand $p^m\langle\varepsilon_i, \varepsilon_k\rangle$, which represents $p^m u$ for
  every unit $u$; the reflections in two such vectors, of values $p^m\varepsilon_i$ and $p^m\varepsilon_iu$, map $\Delta$
  onto itself, and their product has spinor norm $u$ modulo squares (`units_of_diag`);
* (i): either $a_i, a_k \le a_j$ have the parity of $a_j$ (take $m = a_j$: the binary summand represents
  $-p^{a_j}\varepsilon_j$), or $a_l \le a_j$ has the parity of $a_j$ and $-\varepsilon_j\varepsilon_l$ is a square (take
  $a_l + 2b_l = a_j$).

A choice of $(i, k, j, l)$ always exists (`exists_good_perm`): if three of the $a$'s have the same parity, take $j$ the
largest of them; otherwise the $a$'s split $2 + 2$ by parity and, $Q$ being isotropic, one of the two pairs
$\{x, y\}$ has $-\varepsilon_x\varepsilon_y$ a square (`isSquare_of_split`: the two largest terms of
$\sum p^{a_i}\varepsilon_iw_i^2 = 0$ belong to the same pair); take $j$ the larger of that pair.
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma93
import QuadFormsKB.Literature.Cassels.Ch11Examples3
import QuadFormsKB.Literature.Cassels.Ch11Remarks2
import QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Cassels.Ch11Ex13

open QuadForm Matrix Ch11L93

variable {p : ℕ} [Fact p.Prime]

/-! ### The orthogonal basis of $Q$ over $\mathbb Z_p$, $p$ odd -/

/-- **An orthogonal basis over $\mathbb Z_p$, $p$ odd** (the local normal form, Cassels Ch. 8, Lemma 3.4; here from
`LocalDensity.DVR.dvr_jinv_complete_aux`): for a regular quaternary $Q$ over $\mathbb Z_p$ there are $V \in
\mathrm{GL}_4(\mathbb Z_p)$, exponents $a_i$ and units $\varepsilon_i$ with $Q(Vx) = \sum_i p^{a_i}\varepsilon_ix_i^2$.
Arguments: `hp2` ($p \ne 2$), `Q` the form, `hnd` regularity. -/
theorem exists_diag_basis (hp2 : p ≠ 2) (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate) :
    ∃ (V : Matrix (Fin 4) (Fin 4) ℤ_[p]) (a : Fin 4 → ℕ) (ε : Fin 4 → ℤ_[p]), IsUnit V.det ∧
      (∀ i, IsUnit (ε i)) ∧ ∀ x, Q.eval (V *ᵥ x) = ∑ i, (p : ℤ_[p]) ^ a i * ε i * x i ^ 2 := by
  classical
  have hπ := PadicInt.irreducible_p (p := p)
  have hp2' : ¬ (p : ℤ_[p]) ∣ 2 := Siegel.Kneser.not_p_dvd_two hp2
  have h2 : ¬ (p : ℤ_[p]) ^ 2 ∣ 2 := fun h => hp2' (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  have h20 : (2 : ℤ_[p]) ≠ 0 := fun h => hp2' (h ▸ dvd_zero _)
  have hJ0 : LocalDensity.DVR.DvrJInv (p : ℤ_[p]) (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P, ν, hV, hJ⟩ := LocalDensity.DVR.dvr_jinv_complete_aux hπ h2 _ Q.coeff ∅ ∅ (fun _ => 0) rfl hnd hJ0
  set Q' := LocalDensity.DVR.dvr_ofMatrix (Vᵀ * Q.coeff * V) with hQ'
  have hH : Q'.hessian = Vᵀ * (Q.coeff + Q.coeffᵀ) * V := by
    rw [hQ', LocalDensity.DVR.dvr_hessian_ofMatrix]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have heval : ∀ x, Q'.eval x = Q.eval (V *ᵥ x) := by
    intro x
    rw [hQ', LocalDensity.DVR.dvr_eval_ofMatrix]
    show _ = Q.evalIn ℤ_[p] (V *ᵥ x)
    rw [QuadForm.evalIn_eq_dotProduct]
    simp only [Algebra.algebraMap_self]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rfl
  have hJF := LocalDensity.DVR.dvr_isJordanForm_of_jinv h20 Q' P ν (hH ▸ hJ)
  obtain ⟨hP2, -, -, hoff, -, hdiag⟩ := hJF
  have hP : P = ∅ := by
    by_contra hne
    exact hp2' (hP2 (Finset.nonempty_iff_ne_empty.2 hne))
  have hunp : ∀ i, ¬ LocalDensity.IsPaired P i := by
    rintro i ⟨e, he, -⟩
    simp [hP] at he
  choose ε hε hεu using fun i => hdiag i (hunp i)
  refine ⟨V, ν, ε, hV, hεu, fun x => ?_⟩
  rw [← heval, eval_four]
  have z : ∀ i j : Fin 4, i < j → Q'.coeff i j = 0 := fun i j hij => hoff i j hij (by simp [hP])
  rw [z 0 1 (by decide), z 0 2 (by decide), z 0 3 (by decide), z 1 2 (by decide), z 1 3 (by decide),
    z 2 3 (by decide), hε 0, hε 1, hε 2, hε 3, Fin.sum_univ_four]
  ring

/-! ### The choice of the indices $(i, k, j, l)$ -/

/-- Helper: **the conditions on the indices** $(x, y, j, l)$ ($t = e_j$, binary summand on $e_x, e_y$, third basis vector
from $e_l$): $a_x \equiv a_y \pmod 2$, and either $a_x, a_y \le a_j$ have the parity of $a_j$, or $a_l \le a_j$ has the parity
of $a_j$ and $S(j, l)$ ($S(j, l)$ will be "$-\varepsilon_j\varepsilon_l$ is a square"). Arguments: `a` the exponents, `S` the
relation, `x`, `y`, `j`, `l` the indices. -/
def Good (a : Fin 4 → ℕ) (S : Fin 4 → Fin 4 → Prop) (x y j l : Fin 4) : Prop :=
  a x % 2 = a y % 2 ∧ ((a x % 2 = a j % 2 ∧ a x ≤ a j ∧ a y ≤ a j) ∨ (a l % 2 = a j % 2 ∧ a l ≤ a j ∧ S j l))

set_option hygiene false in
/-- Helper: try the $12 + 12$ candidate index tuples. -/
local macro "pick" : tactic => `(tactic| first
  | exact ⟨0, 1, 2, 3, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 1, 3, 2, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 2, 1, 3, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 2, 3, 1, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 3, 1, 2, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 3, 2, 1, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨1, 2, 0, 3, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨1, 2, 3, 0, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨1, 3, 0, 2, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨1, 3, 2, 0, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨2, 3, 0, 1, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨2, 3, 1, 0, by decide, by omega, Or.inl ⟨by omega, by omega, by omega⟩⟩
  | exact ⟨0, 1, 2, 3, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨0, 1, 3, 2, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨0, 2, 1, 3, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨0, 2, 3, 1, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨0, 3, 1, 2, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨0, 3, 2, 1, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨1, 2, 0, 3, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨1, 2, 3, 0, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨1, 3, 0, 2, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨1, 3, 2, 0, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨2, 3, 0, 1, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩
  | exact ⟨2, 3, 1, 0, by decide, by omega, Or.inr ⟨by omega, by omega, by first | exact hs | exact hS _ _ hs⟩⟩)

/-- Helper: **the choice of indices for increasing exponents** $a_0 \le a_1 \le a_2 \le a_3$, given that in every
$2 + 2$ split by parity one of the two pairs satisfies $S$ (`hsplit`). Arguments: `a`, `S` as in `Good`; `hS` symmetry
of `S`; `hm` monotonicity. -/
theorem exists_good_mono (a : Fin 4 → ℕ) (S : Fin 4 → Fin 4 → Prop) (hS : ∀ i j, S i j → S j i)
    (hm : a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3)
    (hsplit : ∀ x y u v : Fin 4, Function.Injective ![x, y, u, v] → a x % 2 = a y % 2 → a u % 2 = a v % 2 →
      a x % 2 ≠ a u % 2 → S x y ∨ S u v) :
    ∃ x y j l : Fin 4, Function.Injective ![x, y, j, l] ∧ Good a S x y j l := by
  obtain ⟨h01, h12, h23⟩ := hm
  unfold Good
  have e : ∀ i, a i % 2 = 0 ∨ a i % 2 = 1 := fun i => Nat.mod_two_eq_zero_or_one _
  by_cases c1 : a 0 % 2 = a 1 % 2 ∧ a 2 % 2 = a 3 % 2 ∧ a 0 % 2 ≠ a 2 % 2
  · rcases hsplit 0 1 2 3 (by decide) c1.1 c1.2.1 c1.2.2 with hs | hs <;>
    rcases e 0 with h0 | h0 <;> rcases e 1 with h1 | h1 <;> rcases e 2 with h2 | h2 <;> rcases e 3 with h3 | h3 <;>
    pick
  by_cases c2 : a 0 % 2 = a 2 % 2 ∧ a 1 % 2 = a 3 % 2 ∧ a 0 % 2 ≠ a 1 % 2
  · rcases hsplit 0 2 1 3 (by decide) c2.1 c2.2.1 c2.2.2 with hs | hs <;>
    rcases e 0 with h0 | h0 <;> rcases e 1 with h1 | h1 <;> rcases e 2 with h2 | h2 <;> rcases e 3 with h3 | h3 <;>
    pick
  by_cases c3 : a 0 % 2 = a 3 % 2 ∧ a 1 % 2 = a 2 % 2 ∧ a 0 % 2 ≠ a 1 % 2
  · rcases hsplit 0 3 1 2 (by decide) c3.1 c3.2.1 c3.2.2 with hs | hs <;>
    rcases e 0 with h0 | h0 <;> rcases e 1 with h1 | h1 <;> rcases e 2 with h2 | h2 <;> rcases e 3 with h3 | h3 <;>
    pick
  have hs : True := trivial
  rcases e 0 with h0 | h0 <;> rcases e 1 with h1 | h1 <;> rcases e 2 with h2 | h2 <;> rcases e 3 with h3 | h3 <;>
  pick

/-- Helper: **the choice of indices** (`exists_good_mono` after sorting the exponents with `Tuple.sort`). Arguments as
in `exists_good_mono`, without monotonicity. -/
theorem exists_good (a : Fin 4 → ℕ) (S : Fin 4 → Fin 4 → Prop) (hS : ∀ i j, S i j → S j i)
    (hsplit : ∀ x y u v : Fin 4, Function.Injective ![x, y, u, v] → a x % 2 = a y % 2 → a u % 2 = a v % 2 →
      a x % 2 ≠ a u % 2 → S x y ∨ S u v) :
    ∃ x y j l : Fin 4, Function.Injective ![x, y, j, l] ∧ Good a S x y j l := by
  set σ := Tuple.sort a with hσ
  have hmono := Tuple.monotone_sort a
  have hcomp : ∀ x y u v : Fin 4, ![σ x, σ y, σ u, σ v] = σ ∘ ![x, y, u, v] := by
    intro x y u v; funext i; fin_cases i <;> rfl
  obtain ⟨x, y, j, l, hinj, hg⟩ := exists_good_mono (a ∘ σ) (fun i j => S (σ i) (σ j)) (fun i j h => hS _ _ h)
    ⟨hmono (by decide), hmono (by decide), hmono (by decide)⟩
    (fun x y u v hi h1 h2 h3 => hsplit (σ x) (σ y) (σ u) (σ v)
      (by rw [hcomp]; exact σ.injective.comp hi) h1 h2 h3)
  exact ⟨σ x, σ y, σ j, σ l, by rw [hcomp]; exact σ.injective.comp hinj, hg⟩

/-! ### Part (iii): the binary summand gives every unit as a spinor norm -/

/-- **(iii) for a lattice with a modular binary summand** (Cassels, p. 244, the argument "represents all of $p^\mu U_p$"):
if $g(y) = p^m(e_0y_0^2 + e_1y_1^2) + dy_2^2$ with $e_0, e_1$ units and $p$ odd, then every unit $u$ is, modulo squares,
the spinor norm of a rotation of $\mathbb Z_p^3$: the product of the reflections in $\xi = (1, 0, 0)$, $g(\xi) = p^me_0$,
and $\xi' = (x, y, 0)$, $g(\xi') = p^me_0u$ (`Ch11Wave6.exists_binary_unit`); both map $\mathbb Z_p^3$ into itself since
$B(z, \xi) \in p^m\mathbb Z_p$ for integral $z$. Arguments: `m` the scale, `he0`, `he1` the units, `hp2` ($p \ne 2$), `d`
the third coefficient, `g` the form with its coefficients `h00` … `h22`. -/
theorem units_of_diag (m : ℕ) {e0 e1 : ℤ_[p]} (he0 : IsUnit e0) (he1 : IsUnit e1) (hp2 : p ≠ 2) (d : ℤ_[p])
    (g : QuadForm ℤ_[p] 3) (h00 : g.coeff 0 0 = (p : ℤ_[p]) ^ m * e0) (h01 : g.coeff 0 1 = 0)
    (h02 : g.coeff 0 2 = 0) (h11 : g.coeff 1 1 = (p : ℤ_[p]) ^ m * e1) (h12 : g.coeff 1 2 = 0)
    (h22 : g.coeff 2 2 = d) : UnitsInSpinorNorm p g := by
  set G := g.map PadicInt.Coe.ringHom with hGdef
  set π : ℚ_[p] := (p : ℚ_[p]) ^ m with hπ
  have hπ0 : π ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hG : ∀ v : Fin 3 → ℚ_[p], G.eval v =
      π * ((e0 : ℚ_[p]) * v 0 * v 0 + (e1 : ℚ_[p]) * v 1 * v 1) + (d : ℚ_[p]) * v 2 * v 2 := by
    intro v
    rw [eval_three]
    simp only [hGdef, QuadForm.map, Matrix.map_apply, h00, h01, h02, h11, h12, h22, PadicInt.Coe.ringHom_apply]
    rw [hπ]; push_cast; ring
  have hrefl : ∀ (ξ : Fin 3 → ℤ_[p]) (η : ℤ_[p]), IsUnit η → ξ 2 = 0 →
      G.eval (fun i => (ξ i : ℚ_[p])) = π * (η : ℚ_[p]) →
      ∀ z : Fin 3 → ℚ_[p], (∀ i, ‖z i‖ ≤ 1) →
        ∀ i, ‖reflectionBy G (fun i => (ξ i : ℚ_[p])) z i‖ ≤ 1 := by
    intro ξ η hη hξ2 hξ z hz
    obtain ⟨ηi, hηi⟩ := hη.exists_right_inv
    set ζ : Fin 3 → ℤ_[p] := fun i => ⟨z i, hz i⟩ with hζ
    have hzζ : z = fun i => (ζ i : ℚ_[p]) := rfl
    set Pz : ℤ_[p] := 2 * e0 * ζ 0 * ξ 0 + 2 * e1 * ζ 1 * ξ 1 with hPz
    have hηq : (η : ℚ_[p]) * (ηi : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hηi, PadicInt.coe_one]
    have hη0 : (η : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hηq
    have hξ2' : ((ξ 2 : ℤ_[p]) : ℚ_[p]) = 0 := by rw [hξ2]; simp
    intro i
    have hpol : G.eval (z + fun i => (ξ i : ℚ_[p])) - G.eval z - G.eval (fun i => (ξ i : ℚ_[p])) =
        π * (Pz : ℚ_[p]) := by
      have h2c : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
        rw [show (2 : ℤ_[p]) = 1 + 1 by norm_num, PadicInt.coe_add, PadicInt.coe_one]; norm_num
      rw [hG, hG, hG, hzζ]; simp only [Pi.add_apply]; rw [hξ2', hPz]; push_cast; rw [h2c]; ring
    have hdiv : π * (Pz : ℚ_[p]) / (π * (η : ℚ_[p])) = (Pz : ℚ_[p]) * (ηi : ℚ_[p]) := by
      rw [mul_div_mul_left _ _ hπ0, div_eq_iff hη0]; linear_combination (-(Pz : ℚ_[p])) * hηq
    have key : reflectionBy G (fun i => (ξ i : ℚ_[p])) z i = ((ζ i - Pz * ηi * ξ i : ℤ_[p]) : ℚ_[p]) := by
      rw [reflectionBy]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpol, hξ, hdiv, hzζ]; push_cast; ring
    rw [key]; exact (ζ i - Pz * ηi * ξ i).2
  intro u hu
  obtain ⟨x, y, hxy⟩ := Ch11Wave6.exists_binary_unit hp2 he0 he1 (he0.mul hu)
  set ξ1 : Fin 3 → ℤ_[p] := ![1, 0, 0] with hξ1
  set ξ2 : Fin 3 → ℤ_[p] := ![x, y, 0] with hξ2
  have hxyq : (e0 : ℚ_[p]) * (x : ℚ_[p]) ^ 2 + (e1 : ℚ_[p]) * (y : ℚ_[p]) ^ 2 = (e0 : ℚ_[p]) * (u : ℚ_[p]) := by
    exact_mod_cast congrArg (fun r : ℤ_[p] => (r : ℚ_[p])) hxy
  have hv1 : G.eval (fun i => (ξ1 i : ℚ_[p])) = π * (e0 : ℚ_[p]) := by
    rw [hG]; simp [hξ1]
  have hv2 : G.eval (fun i => (ξ2 i : ℚ_[p])) = π * ((e0 * u : ℤ_[p]) : ℚ_[p]) := by
    rw [hG]; simp only [hξ2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    push_cast; linear_combination π * hxyq
  have hunit0 : ∀ {c : ℤ_[p]}, IsUnit c → (c : ℚ_[p]) ≠ 0 := by
    intro c hc
    obtain ⟨ci, hci⟩ := hc.exists_right_inv
    have : (c : ℚ_[p]) * (ci : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hci, PadicInt.coe_one]
    exact left_ne_zero_of_mul_eq_one this
  have hn1 : G.eval (fun i => (ξ1 i : ℚ_[p])) ≠ 0 := by rw [hv1]; exact mul_ne_zero hπ0 (hunit0 he0)
  have hn2 : G.eval (fun i => (ξ2 i : ℚ_[p])) ≠ 0 := by rw [hv2]; exact mul_ne_zero hπ0 (hunit0 (he0.mul hu))
  have hr1 := hrefl ξ1 e0 he0 (by simp [hξ1]) hv1
  have hr2 := hrefl ξ2 (e0 * u) (he0.mul hu) (by simp [hξ2]) hv2
  refine ⟨[fun i => (ξ1 i : ℚ_[p]), fun i => (ξ2 i : ℚ_[p])], ⟨1, rfl⟩, ?_, ?_, π * (e0 : ℚ_[p]),
    mul_ne_zero hπ0 (hunit0 he0), ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hn1
    · exact hn2
  · intro z
    simp only [rotationBy, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Function.comp_apply,
      id_eq]
    constructor
    · intro hz; exact hr1 _ (hr2 z hz)
    · intro hz
      have h1 := hr1 _ hz
      rw [reflectionBy_invol G hn1] at h1
      have h2 := hr2 _ h1
      rwa [reflectionBy_invol G hn2] at h2
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hv1, hv2]; push_cast; ring

/-! ### Lemma 9.3 with a primitive $t$ for a diagonal form -/

/-- **The construction for a diagonal form** $Q_0(x) = \sum_i p^{a_i}\varepsilon_ix_i^2$ ($p$ odd): $t = e_2$ and $\Delta$
with basis $p^{b_0}e_0, p^{b_1}e_1, p^{b_3}e_3$, where $a_0 + 2b_0 = a_1 + 2b_1$, satisfy (i)–(iii) of Lemma 9.3
provided $-Q_0(e_2)$ is represented on $\Delta$ (`hrep`); $t$ is primitive. Arguments: `hp2` ($p \ne 2$), `Q0` the form,
`a`, `ε` the exponents and units (`hε`), `hQ0` the diagonal shape, `b0`, `b1`, `b3` the scaling exponents, `hm` the
equal scales, `hrep` the representation. -/
theorem diag_core (hp2 : p ≠ 2) (Q0 : QuadForm ℤ_[p] 4) (a : Fin 4 → ℕ) (ε : Fin 4 → ℤ_[p])
    (hε : ∀ i, IsUnit (ε i)) (hQ0 : ∀ x, Q0.eval x = ∑ i, (p : ℤ_[p]) ^ a i * ε i * x i ^ 2)
    (b0 b1 b3 : ℕ) (hm : a 0 + 2 * b0 = a 1 + 2 * b1)
    (hrep : ∃ y0 y1 y3 : ℤ_[p], (p : ℤ_[p]) ^ a 0 * ε 0 * ((p : ℤ_[p]) ^ b0 * y0) ^ 2 +
      (p : ℤ_[p]) ^ a 1 * ε 1 * ((p : ℤ_[p]) ^ b1 * y1) ^ 2 +
      (p : ℤ_[p]) ^ a 3 * ε 3 * ((p : ℤ_[p]) ^ b3 * y3) ^ 2 = -((p : ℤ_[p]) ^ a 2 * ε 2)) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3),
      Lemma93Data p Q0 t B g ∧ ∃ i, IsUnit (t i) := by
  have hP0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set m := a 0 + 2 * b0 with hmdef
  have e0 : (p : ℤ_[p]) ^ a 0 * ((p : ℤ_[p]) ^ b0) ^ 2 = (p : ℤ_[p]) ^ m := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have e1 : (p : ℤ_[p]) ^ a 1 * ((p : ℤ_[p]) ^ b1) ^ 2 = (p : ℤ_[p]) ^ m := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  set t : Fin 4 → ℤ_[p] := ![0, 0, 1, 0] with ht
  set B : Matrix (Fin 4) (Fin 3) ℤ_[p] := Matrix.of ![![(p : ℤ_[p]) ^ b0, 0, 0], ![0, (p : ℤ_[p]) ^ b1, 0],
    ![0, 0, 0], ![0, 0, (p : ℤ_[p]) ^ b3]] with hBdef
  set g : QuadForm ℤ_[p] 3 := QuadForm.ofUpper ![![(p : ℤ_[p]) ^ m * ε 0, 0, 0], ![0, (p : ℤ_[p]) ^ m * ε 1, 0],
    ![0, 0, (p : ℤ_[p]) ^ a 3 * ε 3 * ((p : ℤ_[p]) ^ b3) ^ 2]] with hgdef
  have hB : ∀ y : Fin 3 → ℤ_[p], B *ᵥ y = ![(p : ℤ_[p]) ^ b0 * y 0, (p : ℤ_[p]) ^ b1 * y 1, 0,
      (p : ℤ_[p]) ^ b3 * y 2] := by
    intro y; ext i; fin_cases i <;> simp [hBdef, mulVec, dotProduct, Fin.sum_univ_three]
  have hQB : ∀ y : Fin 3 → ℤ_[p], Q0.eval (B *ᵥ y) = (p : ℤ_[p]) ^ m * ε 0 * y 0 ^ 2 +
      (p : ℤ_[p]) ^ m * ε 1 * y 1 ^ 2 + (p : ℤ_[p]) ^ a 3 * ε 3 * ((p : ℤ_[p]) ^ b3) ^ 2 * y 2 ^ 2 := by
    intro y
    rw [hQ0, hB, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (ε 0 * y 0 ^ 2) * e0 + (ε 1 * y 1 ^ 2) * e1
  have hg : ∀ y : Fin 3 → ℤ_[p], g.eval y = Q0.eval (B *ᵥ y) := by
    intro y; rw [hQB, eval_three]; simp [hgdef, QuadForm.ofUpper]; ring
  have hQt : Q0.eval t = (p : ℤ_[p]) ^ a 2 * ε 2 := by
    rw [hQ0, Fin.sum_univ_four]; simp [ht]
  refine ⟨t, B, g, ⟨?_, ?_, ?_, hg, ?_, ?_, ?_⟩, 2, by simp [ht]⟩
  · rw [hQt]; exact mul_ne_zero (pow_ne_zero _ hP0) (hε 2).ne_zero
  · intro j
    fin_cases j <;> simp [hQ0, ht, hBdef, Fin.sum_univ_four] <;> ring
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have f0 := congrFun hc 0
    have f1 := congrFun hc 1
    have f3 := congrFun hc 3
    simp [Fin.sum_univ_three, hBdef] at f0 f1 f3
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    intro i; fin_cases i
    · simpa [hp0] using f0
    · simpa [hp0] using f1
    · simpa [hp0] using f3
  · obtain ⟨y0, y1, y3, hy⟩ := hrep
    refine ⟨![y0, y1, y3], ?_⟩
    rw [hg, hQB, hQt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination hy - (ε 0 * y0 ^ 2) * e0 - (ε 1 * y1 ^ 2) * e1
  · intro y _
    refine ⟨2, ?_⟩
    rw [hB]; simp [ht]
  · exact units_of_diag m (hε 0) (hε 1) hp2 _ g (by simp [hgdef, QuadForm.ofUpper])
      (by simp [hgdef, QuadForm.ofUpper]) (by simp [hgdef, QuadForm.ofUpper])
      (by simp [hgdef, QuadForm.ofUpper]) (by simp [hgdef, QuadForm.ofUpper]) rfl

/-! ### Where isotropy is used: a $2 + 2$ split by parity -/

/-- Helper: $p \mid x$ gives residue $0$. -/
theorem toZMod_eq_zero_of_dvd {x : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x) : PadicInt.toZMod x = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, Siegel.Kneser.toZMod_natCast_self, zero_mul]

/-- Helper: $p \nmid x$ gives a nonzero residue. -/
theorem toZMod_ne_zero_of_not_dvd {x : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ∣ x) : PadicInt.toZMod x ≠ 0 := by
  intro h0
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h0
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact hm

/-- Helper: **a zero of a binary unit form modulo $p$** ($p$ odd): if $ex^2 + fy^2 \equiv 0 \pmod p$ with $e, f$ units and
$x$ or $y$ a unit, then $-ef$ is a square in $\mathbb Z_p$ (Hensel, `Siegel.Kneser.exists_sq_eq_of_toZMod`). Arguments:
`hp2`, `he`, `hf` the units, `h` the congruence, `hxy` the unit coordinate. -/
theorem isSquare_of_residue (hp2 : p ≠ 2) {e f x y : ℤ_[p]} (he : IsUnit e) (hf : IsUnit f)
    (h : PadicInt.toZMod (e * x ^ 2 + f * y ^ 2) = 0)
    (hxy : PadicInt.toZMod x ≠ 0 ∨ PadicInt.toZMod y ≠ 0) : IsSquare (-(e * f)) := by
  have hE := Siegel.Kneser.toZMod_ne_zero_of_isUnit he
  have hF := Siegel.Kneser.toZMod_ne_zero_of_isUnit hf
  set E := PadicInt.toZMod e
  set F := PadicInt.toZMod f
  set X := PadicInt.toZMod x
  set Y := PadicInt.toZMod y
  have h' : E * X ^ 2 + F * Y ^ 2 = 0 := by simpa [map_add, map_mul, map_pow] using h
  have hc : PadicInt.toZMod (-(e * f)) = -(E * F) := by simp [E, F]
  rcases hxy with hX | hY
  · have hY : Y ≠ 0 := by
      intro hY; rw [hY] at h'; simp at h'
      rcases h' with h1 | h1
      · exact hE h1
      · exact hX h1
    have hs : E * X / Y ≠ 0 := div_ne_zero (mul_ne_zero hE hX) hY
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (-(e * f)) hs (by
      rw [hc, div_pow, eq_div_iff (pow_ne_zero 2 hY)]; linear_combination (-E) * h')
    exact ⟨z, by rw [← hz]; ring⟩
  · have hX : X ≠ 0 := by
      intro hX; rw [hX] at h'; simp at h'
      rcases h' with h1 | h1
      · exact hF h1
      · exact hY h1
    have hs : F * Y / X ≠ 0 := div_ne_zero (mul_ne_zero hF hY) hX
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (-(e * f)) hs (by
      rw [hc, div_pow, eq_div_iff (pow_ne_zero 2 hX)]; linear_combination (-F) * h')
    exact ⟨z, by rw [← hz]; ring⟩

/-- Helper: **descent for $\langle e_0, e_1\rangle \perp p\langle e_2, e_3\rangle$**: if
$e_0z_0^2 + e_1z_1^2 + p(e_2z_2^2 + e_3z_3^2) = 0$ with the $e_i$ units and some $z_i$ not divisible by $p^k$, then
$-e_0e_1$ or $-e_2e_3$ is a square (induction on $k$: divide by $p$ while all $z_i$ are divisible by $p$; at a primitive
zero reduce modulo $p$). Arguments: `hp2`, the units, `k`, `z`, the non-divisibility, the equation. -/
theorem split_prim (hp2 : p ≠ 2) {e0 e1 e2 e3 : ℤ_[p]} (h0 : IsUnit e0) (h1 : IsUnit e1) (h2 : IsUnit e2)
    (h3 : IsUnit e3) : ∀ (k : ℕ) (z : Fin 4 → ℤ_[p]), (∃ i, ¬ (p : ℤ_[p]) ^ k ∣ z i) →
      e0 * z 0 ^ 2 + e1 * z 1 ^ 2 + (p : ℤ_[p]) * (e2 * z 2 ^ 2 + e3 * z 3 ^ 2) = 0 →
      IsSquare (-(e0 * e1)) ∨ IsSquare (-(e2 * e3)) := by
  have hP0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro k
  induction k with
  | zero => rintro z ⟨i, hi⟩ -; exact (hi (by rw [pow_zero]; exact one_dvd _)).elim
  | succ k ih =>
    rintro z ⟨i, hi⟩ h
    by_cases hall : ∀ i, (p : ℤ_[p]) ∣ z i
    · choose z' hz' using hall
      apply ih z'
      · refine ⟨i, fun hk => hi ?_⟩
        rw [hz' i, pow_succ, mul_comm ((p : ℤ_[p]) ^ k)]
        exact mul_dvd_mul_left _ hk
      · have e : (p : ℤ_[p]) ^ 2 * (e0 * z' 0 ^ 2 + e1 * z' 1 ^ 2 +
            (p : ℤ_[p]) * (e2 * z' 2 ^ 2 + e3 * z' 3 ^ 2)) = 0 := by
          rw [← h, hz' 0, hz' 1, hz' 2, hz' 3]; ring
        exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ hP0)
    · push Not at hall
      obtain ⟨i0, hi0⟩ := hall
      by_cases h01 : (p : ℤ_[p]) ∣ z 0 ∧ (p : ℤ_[p]) ∣ z 1
      · obtain ⟨⟨s0, hs0⟩, ⟨s1, hs1⟩⟩ := h01
        right
        have e : (p : ℤ_[p]) * ((p : ℤ_[p]) * (e0 * s0 ^ 2 + e1 * s1 ^ 2) +
            (e2 * z 2 ^ 2 + e3 * z 3 ^ 2)) = 0 := by
          rw [← h, hs0, hs1]; ring
        have e' := (mul_eq_zero.mp e).resolve_left hP0
        have hr : PadicInt.toZMod (e2 * z 2 ^ 2 + e3 * z 3 ^ 2) = 0 := by
          have : e2 * z 2 ^ 2 + e3 * z 3 ^ 2 = (p : ℤ_[p]) * (-(e0 * s0 ^ 2 + e1 * s1 ^ 2)) := by
            linear_combination e'
          rw [this]; exact toZMod_eq_zero_of_dvd (dvd_mul_right _ _)
        refine isSquare_of_residue hp2 h2 h3 hr ?_
        fin_cases i0
        · exact absurd ⟨s0, hs0⟩ hi0
        · exact absurd ⟨s1, hs1⟩ hi0
        · exact Or.inl (toZMod_ne_zero_of_not_dvd hi0)
        · exact Or.inr (toZMod_ne_zero_of_not_dvd hi0)
      · left
        have hr : PadicInt.toZMod (e0 * z 0 ^ 2 + e1 * z 1 ^ 2) = 0 := by
          have : e0 * z 0 ^ 2 + e1 * z 1 ^ 2 = (p : ℤ_[p]) * (-(e2 * z 2 ^ 2 + e3 * z 3 ^ 2)) := by
            linear_combination h
          rw [this]; exact toZMod_eq_zero_of_dvd (dvd_mul_right _ _)
        refine isSquare_of_residue hp2 h0 h1 hr ?_
        by_contra hc
        push Not at hc
        apply h01
        constructor
        · by_contra hd; exact toZMod_ne_zero_of_not_dvd hd hc.1
        · by_contra hd; exact toZMod_ne_zero_of_not_dvd hd hc.2

/-- Helper: a nonzero $p$-adic integer is not divisible by some power of $p$. -/
theorem exists_not_pow_dvd {x : ℤ_[p]} (hx : x ≠ 0) : ∃ k : ℕ, ¬ (p : ℤ_[p]) ^ k ∣ x := by
  obtain ⟨k, u, hu, rfl⟩ := Ch11L93.decomp hx
  refine ⟨k + 1, ?_⟩
  rintro ⟨c, hc⟩
  have hP0 : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have : u = (p : ℤ_[p]) * c := by
    apply mul_left_cancel₀ hP0
    rw [hc]; ring
  exact PadicInt.p_nonunit (p := p) (isUnit_of_dvd_unit ⟨c, this⟩ hu)

/-- Helper: **the $2 + 2$ split, four explicit terms**: if $\sum_{i < 4} p^{a_i}e_iw_i^2 = 0$ with $w \ne 0$, $e_i$ units,
$a_0 \equiv a_1$, $a_2 \equiv a_3$, $a_0 \not\equiv a_2 \pmod 2$, then $-e_0e_1$ or $-e_2e_3$ is a square (rescale
$w_i$ by $p^{\lfloor a_i/2\rfloor}$ and apply `split_prim`). -/
theorem split4 (hp2 : p ≠ 2) {e0 e1 e2 e3 : ℤ_[p]} (h0 : IsUnit e0) (h1 : IsUnit e1) (h2 : IsUnit e2)
    (h3 : IsUnit e3) {a0 a1 a2 a3 : ℕ} {w0 w1 w2 w3 : ℤ_[p]} (hw : w0 ≠ 0 ∨ w1 ≠ 0 ∨ w2 ≠ 0 ∨ w3 ≠ 0)
    (h : (p : ℤ_[p]) ^ a0 * e0 * w0 ^ 2 + (p : ℤ_[p]) ^ a1 * e1 * w1 ^ 2 + (p : ℤ_[p]) ^ a2 * e2 * w2 ^ 2 +
      (p : ℤ_[p]) ^ a3 * e3 * w3 ^ 2 = 0)
    (h01 : a0 % 2 = a1 % 2) (h23 : a2 % 2 = a3 % 2) (h02 : a0 % 2 ≠ a2 % 2) :
    IsSquare (-(e0 * e1)) ∨ IsSquare (-(e2 * e3)) := by
  have hP0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ev : ∀ c : ℕ, c % 2 = 0 → (p : ℤ_[p]) ^ c = ((p : ℤ_[p]) ^ (c / 2)) ^ 2 := by
    intro c hc; rw [← pow_mul]; congr 1; omega
  have od : ∀ c : ℕ, c % 2 = 1 → (p : ℤ_[p]) ^ c = (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (c / 2)) ^ 2 := by
    intro c hc; rw [← pow_mul, ← pow_succ']; congr 1; omega
  have hne : ∀ (c : ℕ) {w : ℤ_[p]}, w ≠ 0 → (p : ℤ_[p]) ^ c * w ≠ 0 := fun c w hw =>
    mul_ne_zero (pow_ne_zero _ hP0) hw
  rcases Nat.mod_two_eq_zero_or_one a0 with ha0 | ha0
  · set z : Fin 4 → ℤ_[p] := ![(p : ℤ_[p]) ^ (a0 / 2) * w0, (p : ℤ_[p]) ^ (a1 / 2) * w1,
      (p : ℤ_[p]) ^ (a2 / 2) * w2, (p : ℤ_[p]) ^ (a3 / 2) * w3] with hz
    have hz0 : ∃ i, z i ≠ 0 := by
      rcases hw with h | h | h | h
      · exact ⟨0, hne _ h⟩
      · exact ⟨1, hne _ h⟩
      · exact ⟨2, hne _ h⟩
      · exact ⟨3, hne _ h⟩
    obtain ⟨i, hi⟩ := hz0
    obtain ⟨k, hk⟩ := exists_not_pow_dvd hi
    refine split_prim hp2 h0 h1 h2 h3 k z ⟨i, hk⟩ ?_
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [ev a0 ha0, ev a1 (by omega), od a2 (by omega), od a3 (by omega)] at h
    linear_combination h
  · set z : Fin 4 → ℤ_[p] := ![(p : ℤ_[p]) ^ (a2 / 2) * w2, (p : ℤ_[p]) ^ (a3 / 2) * w3,
      (p : ℤ_[p]) ^ (a0 / 2) * w0, (p : ℤ_[p]) ^ (a1 / 2) * w1] with hz
    have hz0 : ∃ i, z i ≠ 0 := by
      rcases hw with h | h | h | h
      · exact ⟨2, hne _ h⟩
      · exact ⟨3, hne _ h⟩
      · exact ⟨0, hne _ h⟩
      · exact ⟨1, hne _ h⟩
    obtain ⟨i, hi⟩ := hz0
    obtain ⟨k, hk⟩ := exists_not_pow_dvd hi
    refine (split_prim hp2 h2 h3 h0 h1 k z ⟨i, hk⟩ ?_).symm
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [od a0 ha0, od a1 (by omega), ev a2 (by omega), ev a3 (by omega)] at h
    linear_combination h

/-- Helper: **the $2 + 2$ split for a diagonal form** (indices $x, y \mid u, v$ in any order): if
$\sum_i p^{a_i}\varepsilon_iw_i^2 = 0$ with $w \ne 0$ and the exponents of $x, y$ (resp. $u, v$) have equal parities,
different between the two pairs, then $-\varepsilon_x\varepsilon_y$ or $-\varepsilon_u\varepsilon_v$ is a square. -/
theorem isSquare_of_split (hp2 : p ≠ 2) (a : Fin 4 → ℕ) (ε : Fin 4 → ℤ_[p]) (hε : ∀ i, IsUnit (ε i))
    (w : Fin 4 → ℤ_[p]) (hw : w ≠ 0) (hsum : ∑ i, (p : ℤ_[p]) ^ a i * ε i * w i ^ 2 = 0)
    {x y u v : Fin 4} (hinj : Function.Injective ![x, y, u, v]) (h1 : a x % 2 = a y % 2)
    (h2 : a u % 2 = a v % 2) (h3 : a x % 2 ≠ a u % 2) : IsSquare (-(ε x * ε y)) ∨ IsSquare (-(ε u * ε v)) := by
  have hbij : Function.Bijective ![x, y, u, v] := Finite.injective_iff_bijective.mp hinj
  have hsum' := hsum
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbij), Fin.sum_univ_four] at hsum'
  simp only [Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hsum'
  have hw' : w x ≠ 0 ∨ w y ≠ 0 ∨ w u ≠ 0 ∨ w v ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hw
    funext i
    obtain ⟨k, rfl⟩ := hbij.2 i
    fin_cases k
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2
  exact split4 hp2 (hε x) (hε y) (hε u) (hε v) hw' hsum' h1 h2 h3

/-! ### Example 13 -/

/-- Helper: $p^a(p^b)^2 = p^c$ when $a + 2b = c$. -/
theorem pow_mul_pow_sq {a b c : ℕ} (h : a + 2 * b = c) :
    (p : ℤ_[p]) ^ a * ((p : ℤ_[p]) ^ b) ^ 2 = (p : ℤ_[p]) ^ c := by
  rw [← pow_mul, ← pow_add, mul_comm b 2, h]

/-- **Cassels, Ch. 11, Example 13, for one prime** (p. 254): for an odd prime $p$ and a regular quaternary $Q$ over
$\mathbb Z_p$, isotropic over $\mathbb Q_p$, the data of Lemma 9.3 exist with $t$ primitive. Arguments: `hp2`
($p \ne 2$), `Q` the form, `hnd` regularity, `hiso` isotropy. -/
theorem lemma93_primitive (hp2 : p ≠ 2) (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate)
    (hiso : (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p]) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3),
      Lemma93Data p Q t B g ∧ ∃ i, IsUnit (t i) := by
  classical
  obtain ⟨V, a, ε, hV, hε, hdiag⟩ := exists_diag_basis hp2 Q hnd
  -- a primitive zero of `Q`, moved to the orthogonal basis
  have hiso' : Q.IsotropicIn ℚ_[p] := by
    obtain ⟨v, hv0, hv⟩ := hiso
    refine ⟨v, hv0, ?_⟩
    rw [← hv]
    simp [QuadForm.evalIn, QuadForm.map]
  obtain ⟨x, ⟨i, hi⟩, hx⟩ := LocalDensity.DVR.exists_primitive_of_isotropicIn ℚ_[p] Q (p : ℤ_[p])
    PadicInt.irreducible_p hiso'
  set w := V⁻¹ *ᵥ x with hwdef
  have hVw : V *ᵥ w = x := by rw [hwdef, mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec]
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw, mulVec_zero] at hVw
    apply hi
    rw [← hVw]
    exact dvd_zero _
  have hsum : ∑ i, (p : ℤ_[p]) ^ a i * ε i * w i ^ 2 = 0 := by rw [← hdiag, hVw, hx]
  -- the choice of indices
  obtain ⟨x', y', j, l, hinj, hgood⟩ := exists_good a (fun i j => IsSquare (-(ε i * ε j)))
    (fun i j h => by simpa only [mul_comm] using h)
    (fun x y u v hinj h1 h2 h3 => isSquare_of_split hp2 a ε hε w hw0 hsum hinj h1 h2 h3)
  set f : Fin 4 → Fin 4 := ![x', y', j, l] with hf
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  -- the permutation matrix `P` with `(P z) (f n) = z n`
  set P : Matrix (Fin 4) (Fin 4) ℤ_[p] := Matrix.of fun m n => if m = f n then 1 else 0 with hPdef
  set P' : Matrix (Fin 4) (Fin 4) ℤ_[p] := Matrix.of fun n m => if m = f n then 1 else 0 with hP'def
  have hPf : ∀ (z : Fin 4 → ℤ_[p]) (n : Fin 4), (P *ᵥ z) (f n) = z n := by
    intro z n
    simp only [hPdef, mulVec, dotProduct, Matrix.of_apply, hinj.eq_iff, ite_mul, one_mul, zero_mul]
    simp
  have hP'P : P' * P = 1 := by
    apply Siegel.Kneser.mul_eq_one_of_mulVec
    intro z
    ext n
    rw [← hPf z n]
    simp [hP'def, mulVec, dotProduct]
  have hPu : IsUnit P.det := by
    have := congrArg Matrix.det hP'P
    rw [det_mul, det_one] at this
    exact isUnit_iff_exists_inv.mpr ⟨P'.det, by rw [mul_comm]; exact this⟩
  set E := V * P with hEdef
  have hE : IsUnit E.det := by rw [hEdef, det_mul]; exact hV.mul hPu
  have hQ0 : ∀ z, (pull Q E).eval z = ∑ n, (p : ℤ_[p]) ^ (a ∘ f) n * (ε ∘ f) n * z n ^ 2 := by
    intro z
    rw [pull_eval, hEdef, ← mulVec_mulVec, hdiag, ← Equiv.sum_comp (Equiv.ofBijective f hbij)]
    simp only [Equiv.ofBijective_apply, hPf, Function.comp]
  have hf0 : f 0 = x' := rfl
  have hf1 : f 1 = y' := rfl
  have hf2 : f 2 = j := rfl
  have hf3 : f 3 = l := rfl
  -- the data for `pull Q E`
  have hdata : ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3),
      Lemma93Data p (pull Q E) t B g ∧ ∃ i, IsUnit (t i) := by
    obtain ⟨hxy, hA | hB⟩ := hgood
    · -- the binary summand represents `-Q(t)`
      obtain ⟨X, Y, hXY⟩ := Ch11Wave6.exists_binary_unit hp2 (hε x') (hε y') (hε j).neg
      refine diag_core hp2 (pull Q E) (a ∘ f) (ε ∘ f) (fun n => hε _) hQ0 ((a j - a x') / 2)
        ((a j - a y') / 2) 0 (by simp only [Function.comp, hf0, hf1]; omega) ⟨X, Y, 0, ?_⟩
      simp only [Function.comp, hf0, hf1, hf2, hf3]
      have e0 := pow_mul_pow_sq (p := p) (a := a x') (b := (a j - a x') / 2) (c := a j) (by omega)
      have e1 := pow_mul_pow_sq (p := p) (a := a y') (b := (a j - a y') / 2) (c := a j) (by omega)
      linear_combination (ε x' * X ^ 2) * e0 + (ε y' * Y ^ 2) * e1 + (p : ℤ_[p]) ^ a j * hXY
    · -- the third basis vector represents `-Q(t)`
      obtain ⟨hlj, hle, s, hs⟩ := hB
      obtain ⟨li, hli⟩ := (hε l).exists_right_inv
      refine diag_core hp2 (pull Q E) (a ∘ f) (ε ∘ f) (fun n => hε _) hQ0 ((max (a x') (a y') - a x') / 2)
        ((max (a x') (a y') - a y') / 2) ((a j - a l) / 2)
        (by simp only [Function.comp, hf0, hf1]; omega) ⟨0, 0, s * li, ?_⟩
      simp only [Function.comp, hf0, hf1, hf2, hf3]
      have el := pow_mul_pow_sq (p := p) (a := a l) (b := (a j - a l) / 2) (c := a j) (by omega)
      linear_combination (ε l * s ^ 2 * li ^ 2) * el - ((p : ℤ_[p]) ^ a j * ε l * li ^ 2) * hs -
        ((p : ℤ_[p]) ^ a j * ε j * (ε l * li + 1)) * hli
  obtain ⟨t, B, g, hD, ⟨i0, hi0⟩⟩ := hdata
  refine ⟨E *ᵥ t, E * B, g, transfer Q E hE hD, ?_⟩
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).mpr hE
  obtain ⟨k, hk⟩ := Siegel.exists_isUnit_coord_mulVec hEu.unit ⟨i0, hi0⟩
  exact ⟨k, by simpa using hk⟩

end QuadFormsKB.Cassels.Ch11Ex13

namespace QuadFormsKB.Cassels

/-- **Cassels, Ch. 11, Example 13** (p. 254), proved: *in Lemma 9.3, if $p \ne 2$, then $t$ can always be chosen to be
a primitive element of $\mathbb Z_p^4$.* The named statement `Lemma93Primitive`, discharged by an orthogonal basis of
$\mathbb Z_p^4$ for $Q$ and $t$ a suitable basis vector (`Ch11Ex13.lemma93_primitive`; see the module docstring). -/
@[kb "cassels1978" "Ch. 11, Ex. 13, p. 254 (proved)"]
theorem lemma93Primitive_holds : Lemma93Primitive :=
  ⟨fun _ _ hp2 Q hnd hiso => Ch11Ex13.lemma93_primitive hp2 Q hnd hiso⟩

end QuadFormsKB.Cassels
