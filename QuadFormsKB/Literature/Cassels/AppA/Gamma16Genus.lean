/-
# Cassels, Appendix A, Example 1 (iv): $\Gamma_{16}$ and $2\Gamma_8$ are in the same genus but not equivalent

**Layer:** integral forms `QuadForm ℤ n`; the genus `Siegel.SameGenus` (equivalence over every $\mathbb Z_p$ and over
$\mathbb R$); $\Gamma_8$ is the $E_8$ form `Siegel.e8` (Hessian the $E_8$ Cartan matrix, determinant $1$), and $2\Gamma_8$
is the orthogonal sum `QuadForm.orthSum e8 e8`; $\Gamma_{16}$ is the form `gamma16` of `Gamma16.lean`.

**Proves** Cassels, App. A, Ex. 1 (iv), p. 367:
* `gamma16_sameGenus`: $\Gamma_{16}$ and $2\Gamma_8$ are in the same genus;
* `gamma16_not_isometric`: they are not equivalent over $\mathbb Z$ (Cassels: from (iii), since $2\Gamma_8$ is
  decomposable).

*Proof of the genus statement* (not Cassels' route, which he leaves to the reader). Both lattices lie in
$\mathbb Q^{16}$ with $\phi = \sum x_i^2$: $\Gamma_{16} = D_{16}^+$ and $2\Gamma_8 = D_8^+ \perp D_8^+$, and they meet in a
sublattice of index $2$ in each. The reflection $s_w$ in $w = (\tfrac12, \dots, \tfrac12, 0, \dots, 0) - t$ with
$t = e_0 + e_8$ ($w \cdot w = 3$) or $t = -e_0 + e_8$ ($w \cdot w = 5$) maps $2\Gamma_8$ onto $\Gamma_{16}$ away from $3$,
resp. $5$. In the bases of the two forms this gives integral matrices $V_d$, $W_d$ ($d = 3, 5$) with
$$\gamma_{16}(V_dx) = d^2\,(e_8 \perp e_8)(x), \qquad V_dW_d = d^2 I,$$
so $d^{-1}V_d$ is an isometry over every commutative ring in which $d$ is a unit: over $\mathbb R$ and $\mathbb Z_p$ for
$p \ne 3$ take $d = 3$, over $\mathbb Z_3$ take $d = 5$. The matrices were computed by
a script (outside Lean); the identities are checked here by `ring`.
-/
import QuadFormsKB.Literature.Cassels.AppA.Gamma16
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Witt.Bridge

open NumberField Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel

/-- The form $2\Gamma_8 = E_8 \perp E_8$ in 16 variables. -/
def twoE8 : QuadForm ℤ 16 := QuadForm.orthSum e8 e8

/-- Evaluating a mapped integral form is `evalIn`. -/
private theorem map_eval_eq_evalIn {n : ℕ} {S : Type*} [CommRing S] (Q : QuadForm ℤ n) (x : Fin n → S) :
    (Q.map (Int.castRingHom S)).eval x = Q.evalIn S x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- **$E_8 \perp E_8$ explicitly**, over any commutative ring $S$. -/
theorem twoE8_map_eval {S : Type*} [CommRing S] (x : Fin 16 → S) :
    (twoE8.map (Int.castRingHom S)).eval x =
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
        - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7)
      + (x 8 ^ 2 + x 9 ^ 2 + x 10 ^ 2 + x 11 ^ 2 + x 12 ^ 2 + x 13 ^ 2 + x 14 ^ 2 + x 15 ^ 2
        - x 8 * x 10 - x 9 * x 11 - x 10 * x 11 - x 11 * x 12 - x 12 * x 13 - x 13 * x 14 - x 14 * x 15) := by
  rw [map_eval_eq_evalIn, twoE8, QuadForm.evalIn_orthSum]
  simp [QuadForm.evalIn, e8, QuadForm.ofUpper, Fin.sum_univ_eight, CartanMatrix.E, Fin.castAdd, Fin.natAdd]
  ring

/-- The matrix $V_3$: $\tfrac13V_3$ maps $\mathbb Z^{16}$ with $E_8 \perp E_8$ isometrically to $\gamma_{16}$ away
from $3$. -/
def gammaV3 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![0, 3, -2, 0, 0, 0, 0, 0, -14, 5, -2, 0, 0, 0, 0, 0;
      0, 3, -2, 0, 0, 0, 0, 0, -26, 11, -5, 0, 0, 0, 0, 0;
      0, 0, -4, 3, 0, 0, 0, 0, -25, 10, -4, 0, 0, 0, 0, 0;
      0, 0, -3, 0, 3, 0, 0, 0, -24, 9, -3, 0, 0, 0, 0, 0;
      0, 0, -2, 0, 0, 3, 0, 0, -23, 8, -2, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 3, 0, -22, 7, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 3, -21, 6, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, -20, 5, 1, 0, 0, 0, 0, 0;
      -3, 0, 2, 0, 0, 0, 0, 0, -19, 4, 2, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -18, 3, 3, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 3, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 3, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 3, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 3, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 3;
      0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]

/-- The matrix $W_3$ with $V_3W_3 = 9I$. -/
def gammaW3 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![2, -2, 0, 0, 0, 0, 0, 6, -3, -2, 0, 0, 0, 0, 0, 1;
      8, -5, 0, 0, 0, 0, 0, 6, 0, -5, 0, 0, 0, 0, 0, 4;
      4, -4, 0, 0, 0, 0, 0, 9, 0, -7, 0, 0, 0, 0, 0, 2;
      10, -10, 3, 0, 0, 0, 0, 12, 0, -10, 0, 0, 0, 0, 0, 5;
      8, -8, 0, 3, 0, 0, 0, 9, 0, -8, 0, 0, 0, 0, 0, 4;
      6, -6, 0, 0, 3, 0, 0, 6, 0, -6, 0, 0, 0, 0, 0, 3;
      4, -4, 0, 0, 0, 3, 0, 3, 0, -4, 0, 0, 0, 0, 0, 2;
      2, -2, 0, 0, 0, 0, 3, 0, 0, -2, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3;
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 10;
      1, -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 15;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 9;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3]

/-- The matrix $V_5$: $\tfrac15V_5$ maps $\mathbb Z^{16}$ with $E_8 \perp E_8$ isometrically to $\gamma_{16}$ away
from $5$. -/
def gammaV5 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![-3, -3, 4, 0, 0, 0, 0, 0, -23, 9, -4, 0, 0, 0, 0, 0;
      -10, -5, 10, 0, 0, 0, 0, 0, -45, 15, -5, 0, 0, 0, 0, 0;
      -8, -8, 4, 5, 0, 0, 0, 0, -43, 14, -4, 0, 0, 0, 0, 0;
      -6, -6, 3, 0, 5, 0, 0, 0, -41, 13, -3, 0, 0, 0, 0, 0;
      -4, -4, 2, 0, 0, 5, 0, 0, -39, 12, -2, 0, 0, 0, 0, 0;
      -2, -2, 1, 0, 0, 0, 5, 0, -37, 11, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 5, -35, 10, 0, 0, 0, 0, 0, 0;
      2, 2, -1, 0, 0, 0, 0, 0, -33, 9, 1, 0, 0, 0, 0, 0;
      -1, 4, -2, 0, 0, 0, 0, 0, -31, 8, 2, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -30, 5, 5, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -25, 0, 0, 5, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -20, 0, 0, 0, 5, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 5, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 5, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 5;
      0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]

/-- The matrix $W_5$ with $V_5W_5 = 25I$. -/
def gammaW5 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![-6, 2, 0, 0, 0, 0, 0, 10, -7, -2, 0, 0, 0, 0, 0, 1;
      -16, 7, 0, 0, 0, 0, 0, 10, -2, -7, 0, 0, 0, 0, 0, 1;
      -20, 10, 0, 0, 0, 0, 0, 15, -10, -5, 0, 0, 0, 0, 0, 5;
      -30, 10, 5, 0, 0, 0, 0, 20, -10, -10, 0, 0, 0, 0, 0, 5;
      -24, 8, 0, 5, 0, 0, 0, 15, -8, -8, 0, 0, 0, 0, 0, 4;
      -18, 6, 0, 0, 5, 0, 0, 10, -6, -6, 0, 0, 0, 0, 0, 3;
      -12, 4, 0, 0, 0, 5, 0, 5, -4, -4, 0, 0, 0, 0, 0, 2;
      -6, 2, 0, 0, 0, 0, 5, 0, -2, -2, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5;
      3, -1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 17;
      -3, 1, 0, 0, 0, 0, 0, 0, -1, 4, 0, 0, 0, 0, 0, 13;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 25;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 20;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 15;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 10;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5]

theorem gamma16_eval_V3 {S : Type*} [CommRing S] (x : Fin 16 → S) :
    (gamma16.map (Int.castRingHom S)).eval (gammaV3.map (Int.castRingHom S) *ᵥ x) =
      9 * (twoE8.map (Int.castRingHom S)).eval x := by
  rw [gamma16_map_eval, twoE8_map_eval]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, gammaV3]
  ring

theorem gamma16_eval_V5 {S : Type*} [CommRing S] (x : Fin 16 → S) :
    (gamma16.map (Int.castRingHom S)).eval (gammaV5.map (Int.castRingHom S) *ᵥ x) =
      25 * (twoE8.map (Int.castRingHom S)).eval x := by
  rw [gamma16_map_eval, twoE8_map_eval]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, gammaV5]
  ring

theorem gammaV3_mul_W3 : gammaV3 * gammaW3 = (9 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide +kernel

theorem gammaV5_mul_W5 : gammaV5 * gammaW5 = (25 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide +kernel

/-- Scaling: $Q(s\vec y) = s^2Q(\vec y)$ over any commutative ring. -/
private theorem eval_smul_sq {n : ℕ} {S : Type*} [CommRing S] (Q : QuadForm S n) (s : S) (y : Fin n → S) :
    Q.eval (s • y) = s ^ 2 * Q.eval y := by
  simp only [QuadForm.evalIn, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Generic isometry from $V$, $W$ with $VW = d^2$ and $Q(Vx) = d^2Q'(x)$, $d$ a unit. -/
private theorem isometricGL_of_V {S : Type*} [CommRing S] (V W : Matrix (Fin 16) (Fin 16) ℤ) (d : ℤ)
    (hd : IsUnit (d : S)) (hVW : V * W = (d * d : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ))
    (hev : ∀ x : Fin 16 → S, (gamma16.map (Int.castRingHom S)).eval (V.map (Int.castRingHom S) *ᵥ x) =
      ((d : S) * d) * (twoE8.map (Int.castRingHom S)).eval x) :
    IsometricGL (gamma16.map (Int.castRingHom S)) (twoE8.map (Int.castRingHom S)) := by
  obtain ⟨u, hu⟩ := hd
  have hmul : V.map (Int.castRingHom S) * W.map (Int.castRingHom S) = (((d * d : ℤ) : S)) • (1 : Matrix (Fin 16) (Fin 16) S) := by
    rw [← Matrix.map_mul, hVW]
    ext i j
    by_cases h : i = j <;> simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, h, ite_true, ite_false, smul_eq_mul, mul_one, mul_zero, eq_intCast, Int.cast_zero]
  have hui : (↑u⁻¹ : S) * (↑u⁻¹ : S) * ((d : S) * d) = 1 := by
    rw [← hu]
    have : (↑u⁻¹ : S) * (u : S) = 1 := u.inv_mul
    calc (↑u⁻¹ : S) * ↑u⁻¹ * (↑u * ↑u) = ((↑u⁻¹ : S) * ↑u) * ((↑u⁻¹ : S) * ↑u) := by ring
      _ = 1 := by rw [this]; ring
  have h1 : ((↑u⁻¹ : S) • V.map (Int.castRingHom S)) * ((↑u⁻¹ : S) • W.map (Int.castRingHom S)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hmul, smul_smul, Int.cast_mul, hui, one_smul]
  refine ⟨⟨(↑u⁻¹ : S) • V.map (Int.castRingHom S), (↑u⁻¹ : S) • W.map (Int.castRingHom S), h1,
    mul_eq_one_comm.mp h1⟩, fun x => ?_⟩
  show (gamma16.map (Int.castRingHom S)).eval (((↑u⁻¹ : S) • V.map (Int.castRingHom S)) *ᵥ x) = _
  rw [Matrix.smul_mulVec, eval_smul_sq, hev, ← mul_assoc, sq, hui, one_mul]

/-- **$\gamma_{16} \cong E_8 \perp E_8$ over any commutative ring in which $3$ is a unit.** -/
theorem isometricGL_gamma16_of_isUnit_three {S : Type*} [CommRing S] (h3 : IsUnit (3 : S)) :
    IsometricGL (gamma16.map (Int.castRingHom S)) (twoE8.map (Int.castRingHom S)) := by
  refine isometricGL_of_V gammaV3 gammaW3 3 (by simpa using h3) (by rw [gammaV3_mul_W3]; norm_num) fun x => ?_
  rw [gamma16_eval_V3]; norm_num

/-- **$\gamma_{16} \cong E_8 \perp E_8$ over any commutative ring in which $5$ is a unit.** -/
theorem isometricGL_gamma16_of_isUnit_five {S : Type*} [CommRing S] (h5 : IsUnit (5 : S)) :
    IsometricGL (gamma16.map (Int.castRingHom S)) (twoE8.map (Int.castRingHom S)) := by
  refine isometricGL_of_V gammaV5 gammaW5 5 (by simpa using h5) (by rw [gammaV5_mul_W5]; norm_num) fun x => ?_
  rw [gamma16_eval_V5]; norm_num

/-- **Cassels, App. A, Ex. 1 (iv), first part** (p. 367): $\Gamma_{16}$ and $2\Gamma_8$ are in the same genus.

*Update:* Cassels leaves this to the reader; the proof here uses the explicit isometries of the module docstring. -/
@[kb "cassels1978" "App. A, Ex. 1 (iv), p. 367 (Γ₁₆ and 2Γ₈ are in the same genus); §3, p. 365"]
theorem gamma16_sameGenus : Siegel.SameGenus gamma16 twoE8 := by
  refine ⟨fun p _ => ?_, isometricGL_gamma16_of_isUnit_three (by norm_num)⟩
  by_cases hp : p = 3
  · subst hp
    refine isometricGL_gamma16_of_isUnit_five ?_
    have h : IsUnit ((5 : ℕ) : ℤ_[3]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num))
    simpa using h
  · refine isometricGL_gamma16_of_isUnit_three ?_
    have h : IsUnit ((3 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes (Fact.out) Nat.prime_three).mpr hp))
    simpa using h

/-- The explicit value of $2\Gamma_8$ over $\mathbb Z$. -/
private theorem twoE8_eval_int (x : Fin 16 → ℤ) : twoE8.eval x =
    (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
        - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7)
      + (x 8 ^ 2 + x 9 ^ 2 + x 10 ^ 2 + x 11 ^ 2 + x 12 ^ 2 + x 13 ^ 2 + x 14 ^ 2 + x 15 ^ 2
        - x 8 * x 10 - x 9 * x 11 - x 10 * x 11 - x 11 * x 12 - x 12 * x 13 - x 13 * x 14 - x 14 * x 15) := by
  have h := twoE8_map_eval x
  rw [map_eval_eq_evalIn] at h
  exact h

/-- $2\Gamma_8$ is additive on vectors supported on the two blocks. -/
private theorem twoE8_add_orth (x y : Fin 16 → ℤ) (hx : ∀ i : Fin 16, 8 ≤ i.val → x i = 0)
    (hy : ∀ i : Fin 16, i.val < 8 → y i = 0) :
    twoE8.eval (x + y) = twoE8.eval x + twoE8.eval y := by
  rw [twoE8_eval_int, twoE8_eval_int, twoE8_eval_int]
  have h8 := hx 8 (by decide)
  have h9 := hx 9 (by decide)
  have h10 := hx 10 (by decide)
  have h11 := hx 11 (by decide)
  have h12 := hx 12 (by decide)
  have h13 := hx 13 (by decide)
  have h14 := hx 14 (by decide)
  have h15 := hx 15 (by decide)
  have g0 := hy 0 (by decide)
  have g1 := hy 1 (by decide)
  have g2 := hy 2 (by decide)
  have g3 := hy 3 (by decide)
  have g4 := hy 4 (by decide)
  have g5 := hy 5 (by decide)
  have g6 := hy 6 (by decide)
  have g7 := hy 7 (by decide)
  simp only [Pi.add_apply, h8, h9, h10, h11, h12, h13, h14, h15, g0, g1, g2, g3, g4, g5, g6, g7]
  ring

/-- The polar form of the sum of squares in terms of values. -/
private theorem bilSq_eq (x y : Fin 16 → ℚ) : bil (sumSqForm 16) x y =
    (sumSqForm 16).eval (x + y) - (sumSqForm 16).eval x - (sumSqForm 16).eval y := by
  have h := QuadForm.polar_eq_hessian ℚ (sumSqForm 16) x y
  have e : (sumSqForm 16).hessian.map (algebraMap ℚ ℚ) = (sumSqForm 16).hessian := by ext; simp
  rw [e] at h
  rw [bil]
  exact h.symm

private theorem bilQ_add_left (x y z : Fin 16 → ℚ) :
    bil (sumSqForm 16) (x + y) z = bil (sumSqForm 16) x z + bil (sumSqForm 16) y z := by
  simp [bil, add_dotProduct]

private theorem bilQ_add_right (x y z : Fin 16 → ℚ) :
    bil (sumSqForm 16) x (y + z) = bil (sumSqForm 16) x y + bil (sumSqForm 16) x z := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

/-- Orthogonality of two spans from orthogonality of generators. -/
private theorem latOrthQ_span {s t : Set (Fin 16 → ℚ)} (h : ∀ y ∈ s, ∀ z ∈ t, bil (sumSqForm 16) y z = 0) :
    LatOrth (sumSqForm 16) (Submodule.span (𝓞 ℚ) s) (Submodule.span (𝓞 ℚ) t) := by
  intro a ha b hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => simp [bil]
    | add b c _ _ ih1 ih2 => rw [bilQ_add_right, ih1, ih2, add_zero]
    | smul c b _ ih => rw [← algebraMap_smul ℚ c b, bil_smul_right, ih, mul_zero]
  | zero => simp [bil]
  | add a c _ _ ih1 ih2 => rw [bilQ_add_left, ih1, ih2, add_zero]
  | smul c a _ ih => rw [← algebraMap_smul ℚ c a, bil_smul_left, ih, mul_zero]

/-- The vector $\sum_i u_i b_i \in \mathbb Q^{16}$ for $u \in \mathbb Z^{16}$. -/
private def gvec (u : Fin 16 → ℤ) : Fin 16 → ℚ := gamma16Basis *ᵥ fun i => (u i : ℚ)

/-- `gvec` as an additive homomorphism. -/
private def gvecH : (Fin 16 → ℤ) →+ (Fin 16 → ℚ) where
  toFun := gvec
  map_zero' := by
    have h : (fun i : Fin 16 => (((0 : Fin 16 → ℤ) i : ℤ) : ℚ)) = 0 := by funext; simp
    simp only [gvec, h, Matrix.mulVec_zero]
  map_add' u v := by
    simp only [gvec]
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

/-- `gvec u` lies in the span of the basis vectors. -/
private theorem gvec_mem (u : Fin 16 → ℤ) :
    gvec u ∈ Submodule.span (𝓞 ℚ) (Set.range gamma16Vec) := by
  have : gvec u = ∑ i, (u i) • gamma16Vec i := by
    ext k
    simp [gvec, Matrix.mulVec, dotProduct, gamma16Vec, Finset.sum_apply, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

/-- The basis vector $b_k$ is `gvec` of the unit vector. -/
private theorem gamma16Vec_eq_gvec (k : Fin 16) : gamma16Vec k = gvec (Pi.single k 1) := by
  ext i
  simp [gvec, gamma16Vec, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **Cassels, App. A, Ex. 1 (iv), second part** (p. 367): $\Gamma_{16}$ and $2\Gamma_8$ are not equivalent over
$\mathbb Z$. *Proof:* an equivalence would split the basis of $\Gamma_{16}$ into two mutually orthogonal halves of
8 vectors each (the Hessian of $E_8 \perp E_8$ is block diagonal), contradicting the indecomposability of
$\Gamma_{16}$ (Ex. 1 (iii), `casselsGamma_indecomposable`). -/
@[kb "cassels1978" "App. A, Ex. 1 (iv), p. 367 (Γ₁₆ and 2Γ₈ are not equivalent); §3, p. 365"]
theorem gamma16_not_isometric : ¬ IsometricGL gamma16 twoE8 := by
  rintro ⟨g, hg⟩
  have hSq : ∀ u : Fin 16 → ℤ,
      (sumSqForm 16).eval (gvec (g.val *ᵥ u)) = 2 * ((twoE8.eval u : ℤ) : ℚ) := by
    intro u
    have := two_mul_gamma16_eval (g.val *ᵥ u)
    rw [hg] at this
    exact this.symm
  set m : Fin 16 → Fin 16 → ℚ := fun j => gvec (g.val *ᵥ Pi.single j 1) with hm
  have hsingle : ∀ (i : Fin 16), 8 ≤ i.val → ∀ k : Fin 16, k.val < 8 → (Pi.single i (1 : ℤ) : Fin 16 → ℤ) k = 0 := by
    intro i hi k hk
    exact Pi.single_eq_of_ne (by intro h; subst h; omega) _
  have hsingle' : ∀ (i : Fin 16), i.val < 8 → ∀ k : Fin 16, 8 ≤ k.val → (Pi.single i (1 : ℤ) : Fin 16 → ℤ) k = 0 := by
    intro i hi k hk
    exact Pi.single_eq_of_ne (by intro h; subst h; omega) _
  have horth : ∀ i j : Fin 16, i.val < 8 → 8 ≤ j.val → bil (sumSqForm 16) (m i) (m j) = 0 := by
    intro i j hi hj
    have h1 : m i + m j = gvec (g.val *ᵥ (Pi.single i 1 + Pi.single j 1)) := by
      simp only [hm]
      rw [Matrix.mulVec_add]
      exact (gvecH.map_add _ _).symm
    rw [bilSq_eq, h1, hm]
    simp only []
    rw [hSq, hSq, hSq, twoE8_add_orth _ _ (hsingle' i hi) (hsingle j hj)]
    push_cast
    ring
  have hne : ∀ j : Fin 16, twoE8.eval (Pi.single j (1 : ℤ)) = 1 → m j ≠ 0 := by
    intro j hj h0
    have := hSq (Pi.single j 1)
    rw [hj] at this
    have h00 : (sumSqForm 16).eval (gvec (g.val *ᵥ Pi.single j 1)) = 0 := by
      have : gvec (g.val *ᵥ Pi.single j 1) = 0 := h0
      rw [this]
      simp [QuadForm.evalIn]
    rw [h00] at this
    norm_num at this
  have h0 : twoE8.eval (Pi.single (0 : Fin 16) (1 : ℤ)) = 1 := by
    rw [twoE8_eval_int]
    simp
  have h8 : twoE8.eval (Pi.single (8 : Fin 16) (1 : ℤ)) = 1 := by
    rw [twoE8_eval_int]
    simp
  set K₁ : Submodule (𝓞 ℚ) (Fin 16 → ℚ) := Submodule.span (𝓞 ℚ) (m '' {j | j.val < 8}) with hK₁
  set K₂ : Submodule (𝓞 ℚ) (Fin 16 → ℚ) := Submodule.span (𝓞 ℚ) (m '' {j | 8 ≤ j.val}) with hK₂
  have hO : LatOrth (sumSqForm 16) K₁ K₂ := by
    apply latOrthQ_span
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact horth i j hi hj
  have hD : Disjoint K₁ K₂ := by
    rw [Submodule.disjoint_def]
    intro z hz1 hz2
    have h := hO z hz1 z hz2
    rw [bil_self] at h
    have h2 : (sumSqForm 16).eval z = 0 := by linarith
    have h3 : ∑ i, z i ^ 2 = 0 := by
      rw [← h2, sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp h3
    funext i
    simpa using h4 i (Finset.mem_univ i)
  have hSup : K₁ ⊔ K₂ = casselsGamma 16 := by
    rw [← span_gamma16Vec, hK₁, hK₂, ← Submodule.span_union, ← Set.image_union]
    have hU : ({j : Fin 16 | j.val < 8} ∪ {j | 8 ≤ j.val}) = Set.univ := by
      ext j; simp; omega
    rw [hU, Set.image_univ]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact gvec_mem _
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      rw [gamma16Vec_eq_gvec]
      have hw : Pi.single k (1 : ℤ) = g.val *ᵥ ((g⁻¹ : GL (Fin 16) ℤ).val *ᵥ Pi.single k 1) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [hw]
      set w : Fin 16 → ℤ := (g⁻¹ : GL (Fin 16) ℤ).val *ᵥ Pi.single k 1
      have hsum : g.val *ᵥ w = ∑ j, w j • (g.val *ᵥ Pi.single j 1) := by
        conv_lhs => rw [← Finset.univ_sum_single w]
        rw [Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Matrix.mulVec_smul]
        congr 1
        ext i
        simp [Pi.single_apply]
      rw [hsum]
      change gvecH (∑ j, w j • (g.val *ᵥ Pi.single j 1)) ∈ _
      rw [map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_zsmul]
        exact zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
  obtain ⟨-, hnd⟩ := casselsGamma_indecomposable (n := 16) (by norm_num) (by norm_num)
  refine hnd ⟨K₁, K₂, ?_, ?_, hO, hD, hSup⟩
  · intro h
    apply hne 0 h0
    have : m 0 ∈ K₁ := Submodule.subset_span ⟨0, by decide, rfl⟩
    rw [h] at this
    simpa using this
  · intro h
    apply hne 8 h8
    have : m 8 ∈ K₂ := Submodule.subset_span ⟨8, by decide, rfl⟩
    rw [h] at this
    simpa using this

end QuadFormsKB.Lattices
