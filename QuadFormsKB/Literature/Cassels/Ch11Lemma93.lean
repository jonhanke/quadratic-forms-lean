/-
# Cassels, Chapter 11, Lemma 9.3 and its Corollary

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Lemma 9.3 and Corollary, pp. 243–245.

**What is proved.** `lemma93_holds : Lemma93` and `lemma93Cor_holds : Lemma93Cor` (the named statements of
`Ch11Sec9.lean`), following Cassels' proof:

* a primitive isotropic vector $e_0$ is completed to a basis $e_0, \dots, e_3$ of $\mathbb Z_p^4$ with
  $B(e_0, e_1) \ne 0$, $B(e_0, e_2) = B(e_0, e_3) = 0$ and $Q(e_2) \ne 0$ ($B(x, y) = Q(x + y) - Q(x) - Q(y)$ is the
  polar form; Cassels' $f(x, y)$ is $B/2$); regularity is used twice, through "the radical is $0$" (`no_radical`);
* $r_0 = e_0$, $r_1 = p^re_1$, $r_2 = p^se_2$, $r_3 = p^Te_3$ with $r + \beta = 2s + \gamma = \mu$, where
  $B(e_0, e_1) = p^\beta u_1$, $Q(e_2) = p^\gamma u_2$; $t = r_2$ and $\Delta$ has the basis $v_0 = r_0$,
  $v_1 = r_1 - k_1r_2$, $v_2 = r_3 - k_3r_2$ with $k_j$ chosen so that $v_j \perp t$;
* on $\Delta$, $Q(y_0v_0 + y_1v_1 + y_2v_2) = p^\mu u_1y_0y_1 + p^{\mu + 1}(\dots)$, from which (i), (ii), (iii) and
  the Corollary follow; (iii) is witnessed by the product of the two reflections in vectors of $\Delta$ with values
  $p^\mu$ and $p^\mu u$, which map $\Delta$ onto itself.

*Deviation:* Cassels' $\lambda$ ($= 1$ if $p = 2$) absorbs the factor $2$ between $f(x, y)$ and the polar form; here the
polar form is used throughout and $2 = p^\lambda w$ ($w$ a unit) is written explicitly. The exponents $s, T$ are chosen
explicitly ($s = \beta + \lambda + \gamma + 2$, $T = \mu + 1$) instead of "so large that".
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9
import QuadFormsKB.Lattices.SAVectorsIsotropic
import QuadFormsKB.Literature.Cassels.Ch9Sec5Exist
import QuadFormsKB.LocalDensity.DVRExplicit

namespace QuadFormsKB.Cassels.Ch11L93

open QuadForm Matrix

/-! ### Generic helpers: the polar form -/

section Polar

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Helper: the **polar form** $B(x, y) = x^{\mathsf T}Hy$ of $Q$ ($H$ the Hessian), so that
$Q(x + y) = Q(x) + Q(y) + B(x, y)$ (`eval_add`). Arguments: `Q` the form, `x`, `y` the vectors. -/
def bl (Q : QuadForm R n) (x y : Fin n → R) : R := x ⬝ᵥ (Q.hessian *ᵥ y)

theorem eval_add (Q : QuadForm R n) (x y : Fin n → R) : Q.eval (x + y) = Q.eval x + Q.eval y + bl Q x y := by
  have h := Q.polar_eq_hessian R x y
  have hm : Q.hessian.map (algebraMap R R) = Q.hessian := by ext i j; simp
  rw [hm] at h
  rw [bl]; linear_combination h

theorem bl_comm (Q : QuadForm R n) (x y : Fin n → R) : bl Q x y = bl Q y x := by
  have hs : Q.hessianᵀ = Q.hessian := by simp [QuadForm.hessian, add_comm]
  rw [bl, bl, dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]

theorem bl_add_left (Q : QuadForm R n) (x y z : Fin n → R) : bl Q (x + y) z = bl Q x z + bl Q y z := by
  simp [bl, add_dotProduct]

theorem bl_add_right (Q : QuadForm R n) (x y z : Fin n → R) : bl Q x (y + z) = bl Q x y + bl Q x z := by
  simp [bl, mulVec_add, dotProduct_add]

theorem bl_smul_left (Q : QuadForm R n) (c : R) (x y : Fin n → R) : bl Q (c • x) y = c * bl Q x y := by
  simp [bl, smul_dotProduct]

theorem bl_smul_right (Q : QuadForm R n) (c : R) (x y : Fin n → R) : bl Q x (c • y) = c * bl Q x y := by
  simp [bl, mulVec_smul, dotProduct_smul]

theorem bl_sub_left (Q : QuadForm R n) (x y z : Fin n → R) : bl Q (x - y) z = bl Q x z - bl Q y z := by
  simp [bl, sub_dotProduct]

theorem bl_sub_right (Q : QuadForm R n) (x y z : Fin n → R) : bl Q x (y - z) = bl Q x y - bl Q x z := by
  simp [bl, mulVec_sub, dotProduct_sub]

theorem bl_zero_right (Q : QuadForm R n) (x : Fin n → R) : bl Q x 0 = 0 := by simp [bl]

theorem eval_smul (Q : QuadForm R n) (c : R) (x : Fin n → R) : Q.eval (c • x) = c ^ 2 * Q.eval x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem bl_self (Q : QuadForm R n) (x : Fin n → R) : bl Q x x = 2 * Q.eval x := by
  have h := eval_add Q x x
  have h2 : x + x = (2 : R) • x := by rw [two_smul]
  rw [h2, eval_smul] at h
  linear_combination -h

theorem eval_zero' (Q : QuadForm R n) : Q.eval 0 = 0 := by
  simpa using eval_smul Q 0 0

end Polar

/-! ### Explicit expansions in $3$ and $4$ variables -/

section Expand

variable {R : Type*} [CommRing R]

theorem eval_four (Q : QuadForm R 4) (x : Fin 4 → R) : Q.eval x =
    Q.coeff 0 0 * x 0 * x 0 + Q.coeff 0 1 * x 0 * x 1 + Q.coeff 0 2 * x 0 * x 2 + Q.coeff 0 3 * x 0 * x 3 +
    Q.coeff 1 1 * x 1 * x 1 + Q.coeff 1 2 * x 1 * x 2 + Q.coeff 1 3 * x 1 * x 3 +
    Q.coeff 2 2 * x 2 * x 2 + Q.coeff 2 3 * x 2 * x 3 + Q.coeff 3 3 * x 3 * x 3 := by
  simp only [QuadForm.evalIn, Fin.sum_univ_four, Algebra.algebraMap_self, RingHom.id_apply]
  simp (config := { decide := true })
  ring

theorem evalIn_three {S : Type*} [CommRing S] [Algebra R S] (Q : QuadForm R 3) (x : Fin 3 → S) :
    Q.evalIn S x =
    algebraMap R S (Q.coeff 0 0) * x 0 * x 0 + algebraMap R S (Q.coeff 0 1) * x 0 * x 1 +
    algebraMap R S (Q.coeff 0 2) * x 0 * x 2 + algebraMap R S (Q.coeff 1 1) * x 1 * x 1 +
    algebraMap R S (Q.coeff 1 2) * x 1 * x 2 + algebraMap R S (Q.coeff 2 2) * x 2 * x 2 := by
  simp only [QuadForm.evalIn, Fin.sum_univ_three]
  simp (config := { decide := true })
  ring

end Expand

theorem eval_three {R : Type*} [CommRing R] (Q : QuadForm R 3) (x : Fin 3 → R) : Q.eval x =
    Q.coeff 0 0 * x 0 * x 0 + Q.coeff 0 1 * x 0 * x 1 + Q.coeff 0 2 * x 0 * x 2 + Q.coeff 1 1 * x 1 * x 1 +
    Q.coeff 1 2 * x 1 * x 2 + Q.coeff 2 2 * x 2 * x 2 := by
  rw [QuadForm.eval, evalIn_three]; simp

/-! ### Reflections -/

section Refl

variable {K : Type*} [Field K] {m : ℕ}

theorem reflectionBy_eq (Q : QuadForm K m) (v x : Fin m → K) :
    reflectionBy Q v x = x - (bl Q x v / Q.eval v) • v := by
  simp only [reflectionBy, eval_add]; congr 2; ring

/-- Helper: a reflection is an involution. -/
theorem reflectionBy_invol (Q : QuadForm K m) {v : Fin m → K} (hv : Q.eval v ≠ 0) (x : Fin m → K) :
    reflectionBy Q v (reflectionBy Q v x) = x := by
  rw [reflectionBy_eq, reflectionBy_eq]
  have h : bl Q (x - (bl Q x v / Q.eval v) • v) v = - bl Q x v := by
    rw [bl_sub_left, bl_smul_left, bl_self]; field_simp; ring
  rw [h]; ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring

end Refl

/-! ### Part (iii): units in the spinor norm for a ternary lattice of the shape $p^\mu(u_1y_0y_1 + p(\dots))$ -/

section Units

variable {p : ℕ} [Fact p.Prime]

/-- Helper: $x \ne 0$ in $\mathbb Z_p$ is $p^k u$ with $u$ a unit. -/
theorem decomp {x : ℤ_[p]} (hx : x ≠ 0) : ∃ (k : ℕ) (u : ℤ_[p]), IsUnit u ∧ x = (p : ℤ_[p]) ^ k * u :=
  ⟨x.valuation, _, (PadicInt.unitCoeff hx).isUnit, by rw [mul_comm]; exact PadicInt.unitCoeff_spec hx⟩

theorem p_ne_zero' : ((p : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
  push_cast; exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- **Part (iii) of Lemma 9.3 for a lattice of the shape found in the proof** (Cassels, p. 244: "$f$ represents all of
$p^\mu U_p$ primitively on $\Delta$ … This implies (i) and (iii)"): if the ternary form $g$ over $\mathbb Z_p$ is
$g(y) = p^\mu(u_1y_0y_1 + p(A_{11}y_1^2 + A_{12}y_1y_2 + A_{22}y_2^2))$ with $u_1$ a unit, then every unit $u$ is the
spinor norm of a rotation of $\mathbb Z_p^3$: the product of the reflections in $x = (a, 1, 0)$, $g(x) = p^\mu$, and
$x' = (a', 1, 0)$, $g(x') = p^\mu u$; both reflections map $\mathbb Z_p^3$ into itself because $B(\mathbb Z_p^3,
\mathbb Z_p^3) \subseteq p^\mu\mathbb Z_p$. -/
theorem units_of_shape (μ : ℕ) {u1 : ℤ_[p]} (hu1 : IsUnit u1) (A11 A12 A22 : ℤ_[p]) (g : QuadForm ℤ_[p] 3)
    (h00 : g.coeff 0 0 = 0) (h01 : g.coeff 0 1 = (p : ℤ_[p]) ^ μ * u1) (h02 : g.coeff 0 2 = 0)
    (h11 : g.coeff 1 1 = (p : ℤ_[p]) ^ (μ + 1) * A11) (h12 : g.coeff 1 2 = (p : ℤ_[p]) ^ (μ + 1) * A12)
    (h22 : g.coeff 2 2 = (p : ℤ_[p]) ^ (μ + 1) * A22) : UnitsInSpinorNorm p g := by
  set G := g.map PadicInt.Coe.ringHom with hGdef
  set π : ℚ_[p] := (p : ℚ_[p]) ^ μ with hπ
  have hπ0 : π ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hG : ∀ v : Fin 3 → ℚ_[p], G.eval v = π * ((u1 : ℚ_[p]) * v 0 * v 1 + (p : ℚ_[p]) *
      ((A11 : ℚ_[p]) * v 1 * v 1 + (A12 : ℚ_[p]) * v 1 * v 2 + (A22 : ℚ_[p]) * v 2 * v 2)) := by
    intro v
    rw [eval_three]
    simp only [hGdef, QuadForm.map, Matrix.map_apply, h00, h01, h02, h11, h12, h22, PadicInt.Coe.ringHom_apply]
    rw [hπ]; push_cast; ring
  -- the reflection in an integral vector with value `π * ε` maps integral vectors to integral vectors
  have hrefl : ∀ (ξ : Fin 3 → ℤ_[p]) (ε : ℤ_[p]), IsUnit ε →
      G.eval (fun i => (ξ i : ℚ_[p])) = π * (ε : ℚ_[p]) →
      ∀ z : Fin 3 → ℚ_[p], (∀ i, ‖z i‖ ≤ 1) →
        ∀ i, ‖reflectionBy G (fun i => (ξ i : ℚ_[p])) z i‖ ≤ 1 := by
    intro ξ ε hε hξ z hz
    obtain ⟨εi, hεi⟩ := hε.exists_right_inv
    set ζ : Fin 3 → ℤ_[p] := fun i => ⟨z i, hz i⟩ with hζ
    have hzζ : z = fun i => (ζ i : ℚ_[p]) := rfl
    set Pz : ℤ_[p] := u1 * (ζ 0 * ξ 1 + ζ 1 * ξ 0) + (p : ℤ_[p]) * (2 * A11 * ζ 1 * ξ 1 +
      A12 * (ζ 1 * ξ 2 + ζ 2 * ξ 1) + 2 * A22 * ζ 2 * ξ 2) with hPz
    have hεq : (ε : ℚ_[p]) * (εi : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hεi, PadicInt.coe_one]
    have hε0 : (ε : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hεq
    intro i
    have hpol : G.eval (z + fun i => (ξ i : ℚ_[p])) - G.eval z - G.eval (fun i => (ξ i : ℚ_[p])) =
        π * (Pz : ℚ_[p]) := by
      have h2c : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
        rw [show (2 : ℤ_[p]) = 1 + 1 by norm_num, PadicInt.coe_add, PadicInt.coe_one]; norm_num
      rw [hG, hG, hG, hzζ]; simp only [Pi.add_apply]; rw [hPz]; push_cast; rw [h2c]; ring
    have hdiv : π * (Pz : ℚ_[p]) / (π * (ε : ℚ_[p])) = (Pz : ℚ_[p]) * (εi : ℚ_[p]) := by
      rw [mul_div_mul_left _ _ hπ0, div_eq_iff hε0]; linear_combination (-(Pz : ℚ_[p])) * hεq
    have key : reflectionBy G (fun i => (ξ i : ℚ_[p])) z i = ((ζ i - Pz * εi * ξ i : ℤ_[p]) : ℚ_[p]) := by
      rw [reflectionBy]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpol, hξ, hdiv, hzζ]; push_cast; ring
    rw [key]; exact (ζ i - Pz * εi * ξ i).2
  intro u hu
  obtain ⟨ui1, hui1⟩ := hu1.exists_right_inv
  -- the two vectors
  set ξ1 : Fin 3 → ℤ_[p] := ![ui1 * (1 - (p : ℤ_[p]) * A11), 1, 0] with hξ1
  set ξ2 : Fin 3 → ℤ_[p] := ![ui1 * (u - (p : ℤ_[p]) * A11), 1, 0] with hξ2
  have hv1 : G.eval (fun i => (ξ1 i : ℚ_[p])) = π * ((1 : ℤ_[p]) : ℚ_[p]) := by
    rw [hG]; simp only [hξ1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : (u1 : ℚ_[p]) * (ui1 : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hui1, PadicInt.coe_one]
    push_cast; linear_combination π * (1 - (p : ℚ_[p]) * (A11 : ℚ_[p])) * this
  have hv2 : G.eval (fun i => (ξ2 i : ℚ_[p])) = π * (u : ℚ_[p]) := by
    rw [hG]; simp only [hξ2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : (u1 : ℚ_[p]) * (ui1 : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hui1, PadicInt.coe_one]
    push_cast; linear_combination π * ((u : ℚ_[p]) - (p : ℚ_[p]) * (A11 : ℚ_[p])) * this
  have hu0 : (u : ℚ_[p]) ≠ 0 := by
    obtain ⟨ui, hui⟩ := hu.exists_right_inv
    have : (u : ℚ_[p]) * (ui : ℚ_[p]) = 1 := by rw [← PadicInt.coe_mul, hui, PadicInt.coe_one]
    exact left_ne_zero_of_mul_eq_one this
  have hn1 : G.eval (fun i => (ξ1 i : ℚ_[p])) ≠ 0 := by rw [hv1]; simpa using hπ0
  have hn2 : G.eval (fun i => (ξ2 i : ℚ_[p])) ≠ 0 := by rw [hv2]; exact mul_ne_zero hπ0 hu0
  have hr1 := hrefl ξ1 1 isUnit_one hv1
  have hr2 := hrefl ξ2 u hu hv2
  refine ⟨[fun i => (ξ1 i : ℚ_[p]), fun i => (ξ2 i : ℚ_[p])], ⟨1, rfl⟩, ?_, ?_, π, hπ0, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hn1
    · exact hn2
  · intro x
    simp only [rotationBy, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Function.comp_apply,
      id_eq]
    constructor
    · intro hx; exact hr1 _ (hr2 x hx)
    · intro hx
      have h1 := hr1 _ hx
      rw [reflectionBy_invol G hn1] at h1
      have h2 := hr2 _ h1
      rwa [reflectionBy_invol G hn2] at h2
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hv1, hv2]; push_cast; ring

end Units

/-! ### The construction of Cassels' proof, in coordinates adapted to $e_0, \dots, e_3$ -/

section Core

variable {p : ℕ} [Fact p.Prime]

/-- **Lemma 9.3 and its Corollary in adapted coordinates** (Cassels, pp. 243–245, from "Put $f(e_1, e_2) = p^\beta b$"):
if $Q(e_0) = 0$, $B(e_0, e_2) = B(e_0, e_3) = 0$, $B(e_0, e_1) \ne 0$ and $Q(e_2) \ne 0$ for the standard basis
(i.e. $c_{00} = c_{02} = c_{03} = 0$, $c_{01} \ne 0$, $c_{22} \ne 0$), then $t = p^se_2$ and the lattice $\Delta$ with
basis $e_0$, $p^re_1 - k_1p^se_2$, $p^Te_3 - k_3p^se_2$ have the properties (i)–(iii) of Lemma 9.3 and the property of
the Corollary. -/
theorem core (Q : QuadForm ℤ_[p] 4) (h00 : Q.coeff 0 0 = 0) (h02 : Q.coeff 0 2 = 0) (h03 : Q.coeff 0 3 = 0)
    (h01 : Q.coeff 0 1 ≠ 0) (h22 : Q.coeff 2 2 ≠ 0) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3),
      Lemma93Data p Q t B g ∧ ∀ z : ℤ_[p], ‖z‖ < ‖Q.eval t‖ → ∃ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = z := by
  obtain ⟨bb, u1, hu1, hc01⟩ := decomp h01
  obtain ⟨gg, u2, hu2, hc22⟩ := decomp h22
  obtain ⟨ll, w, hw, h2⟩ := decomp (two_ne_zero : (2 : ℤ_[p]) ≠ 0)
  obtain ⟨W, hW⟩ := (hw.mul hu2).exists_right_inv
  obtain ⟨ui1, hui1⟩ := hu1.exists_right_inv
  have hP0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- the multipliers `k₁ = k2`, `k₃ = k4` making the basis vectors orthogonal to `t`
  obtain ⟨k2, hk2⟩ : ∃ k : ℤ_[p], k = Q.coeff 1 2 * (p : ℤ_[p]) ^ (gg + 2) * W := ⟨_, rfl⟩
  obtain ⟨k4, hk4⟩ : ∃ k : ℤ_[p], k = Q.coeff 2 3 * (p : ℤ_[p]) ^ (bb + gg + 3) * W := ⟨_, rfl⟩
  -- the coefficients of `g` divided by `p ^ (μ + 1)`
  obtain ⟨A11, hA11⟩ : ∃ A : ℤ_[p], A = Q.coeff 1 1 * (p : ℤ_[p]) ^ (2 * ll + 3 * gg + 3) -
      Q.coeff 1 2 ^ 2 * W * (p : ℤ_[p]) ^ (ll + 2 * gg + 3) +
      Q.coeff 2 2 * Q.coeff 1 2 ^ 2 * W ^ 2 * (p : ℤ_[p]) ^ (gg + 3) := ⟨_, rfl⟩
  obtain ⟨A12, hA12⟩ : ∃ A : ℤ_[p], A = -(Q.coeff 1 2 * Q.coeff 2 3 * W * (p : ℤ_[p]) ^ (bb + ll + 2 * gg + 4)) +
      Q.coeff 1 3 * (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4) +
      2 * Q.coeff 2 2 * Q.coeff 1 2 * Q.coeff 2 3 * W ^ 2 * (p : ℤ_[p]) ^ (bb + gg + 4) -
      Q.coeff 2 3 * Q.coeff 1 2 * W * (p : ℤ_[p]) ^ (bb + ll + 2 * gg + 4) := ⟨_, rfl⟩
  obtain ⟨A22, hA22⟩ : ∃ A : ℤ_[p], A = Q.coeff 2 2 * Q.coeff 2 3 ^ 2 * W ^ 2 * (p : ℤ_[p]) ^ (2 * bb + gg + 5) -
      Q.coeff 2 3 ^ 2 * W * (p : ℤ_[p]) ^ (2 * bb + ll + 2 * gg + 5) +
      Q.coeff 3 3 * (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5) := ⟨_, rfl⟩
  -- exponents: s = bb+ll+gg+2, r = bb+2ll+3gg+4, μ = 2bb+2ll+3gg+4 = 2s+gg = r+bb, T = μ+1
  set t : Fin 4 → ℤ_[p] := ![0, 0, (p : ℤ_[p]) ^ (bb + ll + gg + 2), 0] with ht
  set B : Matrix (Fin 4) (Fin 3) ℤ_[p] := Matrix.of ![![1, 0, 0],
    ![0, (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4), 0],
    ![0, -(k2 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)), -(k4 * (p : ℤ_[p]) ^ (bb + ll + gg + 2))],
    ![0, 0, (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5)]] with hBdef
  set g : QuadForm ℤ_[p] 3 := QuadForm.ofUpper ![![0, (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 4) * u1, 0],
    ![0, (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 4 + 1) * A11,
      (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 4 + 1) * A12],
    ![0, 0, (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 4 + 1) * A22]] with hgdef
  have hB : ∀ y : Fin 3 → ℤ_[p], B *ᵥ y = ![y 0, (p : ℤ_[p]) ^ (bb + 2 * ll + 3 * gg + 4) * y 1,
      -(k2 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)) * y 1 + -(k4 * (p : ℤ_[p]) ^ (bb + ll + gg + 2)) * y 2,
      (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 3 * gg + 5) * y 2] := by
    intro y; ext i; fin_cases i <;> simp [hBdef, mulVec, dotProduct, Fin.sum_univ_three]
  set μ := 2 * bb + 2 * ll + 3 * gg + 4 with hμ
  have hQB : ∀ y : Fin 3 → ℤ_[p], Q.eval (B *ᵥ y) = (p : ℤ_[p]) ^ μ * u1 * y 0 * y 1 +
      (p : ℤ_[p]) ^ (μ + 1) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) := by
    intro y
    rw [hB, eval_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [h00, h02, h03, hc01, hA11, hA12, hA22, hk2, hk4, hμ]
    ring
  have hg : ∀ y : Fin 3 → ℤ_[p], g.eval y = Q.eval (B *ᵥ y) := by
    intro y; rw [hQB, eval_three]; simp [hgdef, QuadForm.ofUpper]; ring
  have hQt : ∀ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = (p : ℤ_[p]) ^ μ * u2 + Q.eval (B *ᵥ y) := by
    intro y
    rw [hB, ht, eval_four, eval_four]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [h00, h02, h03, hc22, hk2, hk4, hμ]
    linear_combination (-((p : ℤ_[p]) ^ gg * u2 * (p : ℤ_[p]) ^ (2 * bb + 2 * ll + 2 * gg + 4) *
      (Q.coeff 1 2 * (p : ℤ_[p]) ^ (gg + 2) * W * y 1 + Q.coeff 2 3 * (p : ℤ_[p]) ^ (bb + gg + 3) * W * y 2))) * h2 +
      (-(Q.coeff 1 2 * (p : ℤ_[p]) ^ (2 * bb + 3 * ll + 4 * gg + 6) * y 1 +
        Q.coeff 2 3 * (p : ℤ_[p]) ^ (3 * bb + 3 * ll + 4 * gg + 7) * y 2)) * hW
  have hQt0 : Q.eval t = (p : ℤ_[p]) ^ μ * u2 := by
    have := hQt 0
    rwa [mulVec_zero, add_zero, eval_zero', add_zero] at this
  have hPμ : (p : ℤ_[p]) ^ μ ≠ 0 := pow_ne_zero _ hP0
  have hnormt : ‖Q.eval t‖ = ‖(p : ℤ_[p]) ^ μ‖ := by
    rw [hQt0, norm_mul, PadicInt.isUnit_iff.mp hu2, mul_one]
  -- the values on `(a, 1, 0)`
  have hline : ∀ a : ℤ_[p], Q.eval (t + B *ᵥ ![a, 1, 0]) =
      (p : ℤ_[p]) ^ μ * (u2 + u1 * a + (p : ℤ_[p]) * A11) := by
    intro a; rw [hQt, hQB]; simp; ring
  refine ⟨t, B, g, ⟨?_, ?_, ?_, hg, ?_, ?_, ?_⟩, ?_⟩
  · -- `ne`
    rw [hQt0]; exact mul_ne_zero hPμ hu2.ne_zero
  · -- `orth`
    intro j
    have hcol : (fun i => B i j) = B *ᵥ Pi.single j 1 := by rw [mulVec_single_one]; rfl
    rw [hcol, hQt, hQt0]
  · -- `indep`
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    have e3 := congrFun hc 3
    simp [Fin.sum_univ_three, hBdef] at e0 e1 e3
    have hPq : ((p : ℤ_[p]) : ℚ_[p]) ≠ 0 := p_ne_zero'
    intro i; fin_cases i
    · simpa using e0
    · exact e1.resolve_right (Fact.out : p.Prime).ne_zero
    · exact e3.resolve_right (Fact.out : p.Prime).ne_zero
  · -- `rep` (i)
    refine ⟨![ui1 * (-u2 - (p : ℤ_[p]) * A11), 1, 0], ?_⟩
    rw [hg, hQB, hQt0]; simp
    linear_combination (p : ℤ_[p]) ^ μ * (-u2 - (p : ℤ_[p]) * A11) * hui1
  · -- `prim` (ii)
    intro y hy
    refine ⟨0, ?_⟩
    have hy0 : (t + B *ᵥ y) 0 = y 0 := by rw [hB, ht]; simp
    rw [hy0]
    rw [hnormt, hQt, hQB] at hy
    have hZ : ‖u2 + u1 * y 0 * y 1 + (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)‖ < 1 := by
      have e : (p : ℤ_[p]) ^ μ * u2 + ((p : ℤ_[p]) ^ μ * u1 * y 0 * y 1 + (p : ℤ_[p]) ^ (μ + 1) *
          (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)) = (p : ℤ_[p]) ^ μ * (u2 + u1 * y 0 * y 1 +
          (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2)) := by ring
      rw [e, norm_mul] at hy
      have hpos : 0 < ‖(p : ℤ_[p]) ^ μ‖ := norm_pos_iff.mpr hPμ
      nlinarith
    by_contra hnu
    have m1 : u2 + u1 * y 0 * y 1 + (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) ∈
        IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.mem_nonunits.mpr hZ
    have m2 : u1 * y 0 * y 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hnu)
    have m3 : (p : ℤ_[p]) * (A11 * y 1 * y 1 + A12 * y 1 * y 2 + A22 * y 2 * y 2) ∈
        IsLocalRing.maximalIdeal ℤ_[p] := Ideal.mul_mem_right _ _ PadicInt.p_nonunit
    have : u2 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      have := Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3
      convert this using 1; ring
    exact this hu2
  · -- `units` (iii)
    refine units_of_shape μ hu1 A11 A12 A22 g ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hgdef, QuadForm.ofUpper]
  · -- Corollary
    intro z hz
    rw [hnormt] at hz
    have hzμ : z ∈ Ideal.span {(p : ℤ_[p]) ^ μ} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [PadicInt.norm_p_pow] at hz; exact hz.le
    obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp hzμ
    refine ⟨![ui1 * (z' - u2 - (p : ℤ_[p]) * A11), 1, 0], ?_⟩
    rw [hline, ← hz']
    linear_combination (p : ℤ_[p]) ^ μ * (z' - u2 - (p : ℤ_[p]) * A11) * hui1

end Core

/-! ### Change of basis, and the reduction to adapted coordinates -/

section Reduce

/-- Helper: the form $y \mapsto Q(Ey)$ (the Gram form of the basis given by the columns of $E$), over any commutative
ring. (`Lattices.pullbackForm` is the same construction over a number field.) Arguments: `Q` the form, `E` the
matrix. -/
def pull {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) (E : Matrix (Fin n) (Fin n) R) : QuadForm R n :=
  QuadForm.ofUpper fun i j => if i = j then (Eᵀ * Q.coeff * E) i i else (Eᵀ * Q.coeff * E) i j + (Eᵀ * Q.coeff * E) j i

theorem pull_eval {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) (E : Matrix (Fin n) (Fin n) R)
    (y : Fin n → R) : (pull Q E).eval y = Q.eval (E *ᵥ y) := by
  unfold QuadForm.eval
  rw [pull, Lattices.evalIn_ofUpper_symm, QuadForm.evalIn_eq_dotProduct]
  have hm : ∀ M : Matrix (Fin n) (Fin n) R, M.map (algebraMap R R) = M := fun M => by ext; simp
  rw [hm, hm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem bl_eq {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) (x y : Fin n → R) :
    bl Q x y = Q.eval (x + y) - Q.eval x - Q.eval y := by rw [eval_add]; ring

theorem pull_bl {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) (E : Matrix (Fin n) (Fin n) R)
    (x y : Fin n → R) : bl (pull Q E) x y = bl Q (E *ᵥ x) (E *ᵥ y) := by
  rw [bl_eq, bl_eq, pull_eval, pull_eval, pull_eval, mulVec_add]

theorem coeff00 {R : Type*} [CommRing R] (Q : QuadForm R 4) : Q.coeff 0 0 = Q.eval (Pi.single 0 1) := by
  rw [eval_four]; simp

theorem coeff22 {R : Type*} [CommRing R] (Q : QuadForm R 4) : Q.coeff 2 2 = Q.eval (Pi.single 2 1) := by
  rw [eval_four]; simp

theorem coeff01 {R : Type*} [CommRing R] (Q : QuadForm R 4) :
    Q.coeff 0 1 = bl Q (Pi.single 0 1) (Pi.single 1 1) := by
  rw [bl_eq, eval_four, eval_four, eval_four]; simp; ring

theorem coeff02 {R : Type*} [CommRing R] (Q : QuadForm R 4) :
    Q.coeff 0 2 = bl Q (Pi.single 0 1) (Pi.single 2 1) := by
  rw [bl_eq, eval_four, eval_four, eval_four]; simp; ring

theorem coeff03 {R : Type*} [CommRing R] (Q : QuadForm R 4) :
    Q.coeff 0 3 = bl Q (Pi.single 0 1) (Pi.single 3 1) := by
  rw [bl_eq, eval_four, eval_four, eval_four]; simp; ring

variable {p : ℕ} [Fact p.Prime]

/-- **Transfer along a change of basis:** the data of Lemma 9.3 for $y \mapsto Q(Ey)$, $E \in \mathrm{GL}_4(\mathbb Z_p)$,
give the data for $Q$ (with $t \mapsto Et$, $\Delta \mapsto E\Delta$, the same Gram form $g$). -/
theorem transfer (Q : QuadForm ℤ_[p] 4) (E : Matrix (Fin 4) (Fin 4) ℤ_[p]) (hE : IsUnit E.det)
    {t : Fin 4 → ℤ_[p]} {B : Matrix (Fin 4) (Fin 3) ℤ_[p]} {g : QuadForm ℤ_[p] 3}
    (h : Lemma93Data p (pull Q E) t B g) : Lemma93Data p Q (E *ᵥ t) (E * B) g where
  ne := by rw [← pull_eval]; exact h.ne
  orth j := by
    have hc : (fun i => (E * B) i j) = E *ᵥ (fun i => B i j) := by
      ext i; simp [Matrix.mul_apply, mulVec, dotProduct]
    rw [hc, ← mulVec_add, ← pull_eval, ← pull_eval, ← pull_eval]; exact h.orth j
  indep := by
    set Eq : Matrix (Fin 4) (Fin 4) ℚ_[p] := E.map PadicInt.Coe.ringHom with hEq
    have hdet : IsUnit Eq.det := by
      rw [hEq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hE.map _
    have hinj : Function.Injective (Matrix.mulVecLin Eq) := by
      intro v w hvw
      have := congrArg (fun v => Eq⁻¹ *ᵥ v) hvw
      simpa [Matrix.mulVecLin_apply, mulVec_mulVec, nonsing_inv_mul _ hdet] using this
    have := h.indep.map' (Matrix.mulVecLin Eq) (LinearMap.ker_eq_bot.mpr hinj)
    convert this using 1
    ext j i
    simp [hEq, mulVec, dotProduct, Matrix.mul_apply]
  gram y := by rw [h.gram, pull_eval, mulVec_mulVec]
  rep := by
    obtain ⟨y, hy⟩ := h.rep
    exact ⟨y, by rw [hy, pull_eval]⟩
  prim y hy := by
    rw [← mulVec_mulVec, ← mulVec_add, ← pull_eval, ← pull_eval] at hy
    have hu := h.prim y hy
    have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).mpr hE
    obtain ⟨i, hi⟩ := Siegel.exists_isUnit_coord_mulVec hEu.unit hu
    refine ⟨i, ?_⟩
    simpa [mulVec_add, mulVec_mulVec] using hi
  units := h.units

/-- Helper: the matrix whose columns are $c_0, \dots, c_3$. -/
def colMat (c : Fin 4 → Fin 4 → ℤ_[p]) : Matrix (Fin 4) (Fin 4) ℤ_[p] := (Matrix.of c)ᵀ

theorem colMat_single (c : Fin 4 → Fin 4 → ℤ_[p]) (j : Fin 4) : colMat c *ᵥ Pi.single j 1 = c j := by
  rw [colMat, mulVec_single_one]; rfl

theorem colMat_mulVec (c : Fin 4 → Fin 4 → ℤ_[p]) (a : Fin 4 → ℤ_[p]) :
    colMat c *ᵥ a = a 0 • c 0 + a 1 • c 1 + a 2 • c 2 + a 3 • c 3 := by
  ext i; simp [colMat, mulVec, dotProduct, Fin.sum_univ_four]; ring

/-- **Regularity, used as "the radical is $0$"**: if $c_0, \dots, c_3$ is a basis of $\mathbb Z_p^4$ and the vector
$w = \sum a_jc_j \ne 0$ is orthogonal to every $c_j$, then $Q$ is degenerate. -/
theorem no_radical (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate) (c : Fin 4 → Fin 4 → ℤ_[p])
    (hc : IsUnit (Matrix.of c).det) (a : Fin 4 → ℤ_[p]) (ha : a ≠ 0)
    (h : ∀ j, bl Q (c j) (colMat c *ᵥ a) = 0) : False := by
  set w := colMat c *ᵥ a with hw
  have hE : IsUnit (colMat c).det := by rwa [colMat, det_transpose]
  have h1 : (Matrix.of c) *ᵥ (Q.hessian *ᵥ w) = 0 := by
    funext j; have := h j; simpa [bl, mulVec, dotProduct] using this
  have h2 : Q.hessian *ᵥ w = 0 := by
    have := congrArg (fun v => (Matrix.of c)⁻¹ *ᵥ v) h1
    rwa [mulVec_mulVec, nonsing_inv_mul _ hc, one_mulVec, mulVec_zero] at this
  have hw0 : w ≠ 0 := by
    intro hw0
    apply ha
    have := congrArg (fun v => (colMat c)⁻¹ *ᵥ v) hw0
    simp only [hw] at this
    rwa [mulVec_mulVec, nonsing_inv_mul _ hE, one_mulVec, mulVec_zero] at this
  exact hnd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, h2⟩)

end Reduce

/-! ### The adapted basis (Cassels, p. 243) -/

section Normal

variable {p : ℕ} [Fact p.Prime]

theorem quot_of_norm_le {a b : ℤ_[p]} (hb : b ≠ 0) (h : ‖a‖ ≤ ‖b‖) : ∃ l : ℤ_[p], a = l * b := by
  have hbq : (b : ℚ_[p]) ≠ 0 := fun h0 => hb (Subtype.ext (by simpa using h0))
  refine ⟨⟨(a : ℚ_[p]) / b, ?_⟩, ?_⟩
  · show ‖(a : ℚ_[p]) / b‖ ≤ 1
    rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
  · apply Subtype.ext
    show (a : ℚ_[p]) = ((a : ℚ_[p]) / b) * b
    rw [div_mul_cancel₀ _ hbq]

@[simp] theorem of_row (c : Fin 4 → Fin 4 → ℤ_[p]) (i : Fin 4) : Matrix.of c i = c i := rfl

theorem isUnit_det_perm (c : Fin 4 → Fin 4 → ℤ_[p]) (hc : IsUnit (Matrix.of c).det) (σ : Equiv.Perm (Fin 4)) :
    IsUnit (Matrix.of (fun j => c (σ j))).det := by
  have e : Matrix.of (fun j => c (σ j)) = (Matrix.of c).submatrix σ id := rfl
  rw [e, det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hc]

/-- Step 1: a primitive vector is the first vector of a basis. -/
theorem step1 {x : Fin 4 → ℤ_[p]} (hx : ∃ i, IsUnit (x i)) :
    ∃ c : Fin 4 → Fin 4 → ℤ_[p], IsUnit (Matrix.of c).det ∧ c 0 = x := by
  obtain ⟨i0, hi0⟩ := hx
  set M := (1 : Matrix (Fin 4) (Fin 4) ℤ_[p]).updateRow i0 x with hMdef
  have hM : M.det = x i0 := by
    have h := det_updateRow_sum (1 : Matrix (Fin 4) (Fin 4) ℤ_[p]) i0 x
    have e : (∑ k, x k • (1 : Matrix (Fin 4) (Fin 4) ℤ_[p]) k) = x := by
      funext j; simp [Finset.sum_apply, Matrix.one_apply]
    rw [e] at h; simpa using h
  refine ⟨fun j => M (Equiv.swap 0 i0 j), isUnit_det_perm (fun j => M j) (by show IsUnit M.det; rw [hM]; exact hi0) _, ?_⟩
  simp [hMdef]

/-- Step 2: after a permutation, $|B(c_0, c_1)| \ge |B(c_0, c_j)|$ for $j \ne 0$ and $B(c_0, c_1) \ne 0$. -/
theorem step2 (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate) (c : Fin 4 → Fin 4 → ℤ_[p])
    (hc : IsUnit (Matrix.of c).det) (h0 : Q.eval (c 0) = 0) :
    ∃ c' : Fin 4 → Fin 4 → ℤ_[p], IsUnit (Matrix.of c').det ∧ c' 0 = c 0 ∧ bl Q (c' 0) (c' 1) ≠ 0 ∧
      ∀ j, j ≠ 0 → ‖bl Q (c' 0) (c' j)‖ ≤ ‖bl Q (c' 0) (c' 1)‖ := by
  obtain ⟨j1, hj1, hmax⟩ := Finset.exists_max_image (Finset.univ.erase (0 : Fin 4))
    (fun j => ‖bl Q (c 0) (c j)‖) ⟨1, by simp⟩
  have hj10 : j1 ≠ 0 := (Finset.mem_erase.mp hj1).1
  have hne : bl Q (c 0) (c j1) ≠ 0 := by
    intro hz
    apply no_radical Q hnd c hc (Pi.single 0 1) (by simp)
    intro j
    rw [colMat_single, bl_comm]
    by_cases hj : j = 0
    · subst hj; rw [bl_self, h0, mul_zero]
    · have := hmax j (by simp [hj])
      rw [hz, norm_zero] at this
      exact norm_le_zero_iff.mp this
  have hs0 : Equiv.swap 1 j1 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 1 by decide) hj10.symm
  refine ⟨fun j => c (Equiv.swap 1 j1 j), isUnit_det_perm c hc _, ?_, ?_, ?_⟩
  · simp [hs0]
  · simpa [hs0] using hne
  · intro j hj
    simp only [hs0, Equiv.swap_apply_left]
    refine hmax _ ?_
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    exact hj ((Equiv.swap 1 j1).injective (h.trans hs0.symm))

/-- Step 3: replacing $c_j$ by $c_j - l_jc_1$ ($j = 2, 3$) gives $B(c_0, c_2) = B(c_0, c_3) = 0$. -/
theorem step3 (Q : QuadForm ℤ_[p] 4) (c : Fin 4 → Fin 4 → ℤ_[p]) (hc : IsUnit (Matrix.of c).det)
    (h1 : bl Q (c 0) (c 1) ≠ 0) (hmax : ∀ j, j ≠ 0 → ‖bl Q (c 0) (c j)‖ ≤ ‖bl Q (c 0) (c 1)‖) :
    ∃ c' : Fin 4 → Fin 4 → ℤ_[p], IsUnit (Matrix.of c').det ∧ c' 0 = c 0 ∧ c' 1 = c 1 ∧
      bl Q (c' 0) (c' 2) = 0 ∧ bl Q (c' 0) (c' 3) = 0 := by
  obtain ⟨l2, hl2⟩ := quot_of_norm_le h1 (hmax 2 (by decide))
  obtain ⟨l3, hl3⟩ := quot_of_norm_le h1 (hmax 3 (by decide))
  set A := Matrix.of c with hA
  set A' := A.updateRow 2 (A 2 + (-l2) • A 1) with hA'
  set A'' := A'.updateRow 3 (A' 3 + (-l3) • A' 1) with hA''
  have hd1 : A'.det = A.det := det_updateRow_add_smul_self A (by decide) _
  have hd2 : A''.det = A'.det := det_updateRow_add_smul_self A' (by decide) _
  have r0 : A'' 0 = c 0 := by simp [hA'', hA', hA, Matrix.updateRow_apply]
  have r1 : A'' 1 = c 1 := by simp [hA'', hA', hA, Matrix.updateRow_apply]
  have r2 : A'' 2 = c 2 + (-l2) • c 1 := by simp [hA'', hA', hA, Matrix.updateRow_apply]
  have r3 : A'' 3 = c 3 + (-l3) • c 1 := by simp [hA'', hA', hA, Matrix.updateRow_apply]
  refine ⟨fun j => A'' j, ?_, r0, r1, ?_, ?_⟩
  · show IsUnit A''.det
    rw [hd2, hd1]; exact hc
  · simp only [r0, r2]; rw [bl_add_right, bl_smul_right, hl2]; ring
  · simp only [r0, r3]; rw [bl_add_right, bl_smul_right, hl3]; ring

/-- Step 4: $Q$ does not vanish on the span of $c_2, c_3$ (regularity), so after a change $Q(c_2) \ne 0$. -/
theorem step4 (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate) (c : Fin 4 → Fin 4 → ℤ_[p])
    (hc : IsUnit (Matrix.of c).det) (h2 : bl Q (c 0) (c 2) = 0) (h3 : bl Q (c 0) (c 3) = 0) :
    ∃ c' : Fin 4 → Fin 4 → ℤ_[p], IsUnit (Matrix.of c').det ∧ c' 0 = c 0 ∧ c' 1 = c 1 ∧
      bl Q (c' 0) (c' 2) = 0 ∧ bl Q (c' 0) (c' 3) = 0 ∧ Q.eval (c' 2) ≠ 0 := by
  by_cases hq2 : Q.eval (c 2) ≠ 0
  · exact ⟨c, hc, rfl, rfl, h2, h3, hq2⟩
  push_neg at hq2
  by_cases hq3 : Q.eval (c 3) ≠ 0
  · refine ⟨fun j => c (Equiv.swap 2 3 j), isUnit_det_perm c hc _, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Equiv.swap_apply_of_ne_of_ne, h2, h3, hq3]
  push_neg at hq3
  by_cases hb : bl Q (c 2) (c 3) ≠ 0
  · set A := Matrix.of c with hA
    set A' := A.updateRow 2 (A 2 + A 3) with hA'
    have hd : A'.det = A.det := det_updateRow_add_self A (by decide)
    refine ⟨fun j => A' j, by show IsUnit A'.det; rw [hd]; exact hc, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hA', hA, Matrix.updateRow_apply]
    · simp [hA', hA, Matrix.updateRow_apply]
    · simp [hA', hA, Matrix.updateRow_apply, bl_add_right, h2, h3]
    · simp [hA', hA, Matrix.updateRow_apply, h3]
    · simp only [hA', hA, Matrix.updateRow_self, of_row]
      rw [eval_add, hq2, hq3]; simpa using hb
  push_neg at hb
  exfalso
  by_cases hαβ : bl Q (c 1) (c 3) = 0 ∧ bl Q (c 1) (c 2) = 0
  · apply no_radical Q hnd c hc (Pi.single 2 1) (by simp)
    intro j
    rw [colMat_single]
    fin_cases j
    · simp [h2]
    · simp [hαβ.2]
    · simp [bl_self, hq2]
    · simp [bl_comm Q (c 3), hb]
  · apply no_radical Q hnd c hc ![0, 0, bl Q (c 1) (c 3), -bl Q (c 1) (c 2)]
    · intro h
      apply hαβ
      have e2 := congrFun h 2
      have e3 := congrFun h 3
      simp at e2 e3
      exact ⟨e2, e3⟩
    intro j
    rw [colMat_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zero_smul, zero_add]
    rw [bl_add_right, bl_smul_right, bl_smul_right]
    fin_cases j
    · simp [h2, h3]
    · simp; ring
    · simp [bl_self, hq2, hb]
    · simp [bl_self, hq3, bl_comm Q (c 3) (c 2), hb]

/-- **The adapted basis** (Cassels, p. 243): for a regular $Q$ and a primitive $x$ with $Q(x) = 0$ there is a basis
$c_0 = x, c_1, c_2, c_3$ of $\mathbb Z_p^4$ with $B(c_0, c_1) \ne 0$, $B(c_0, c_2) = B(c_0, c_3) = 0$, $Q(c_2) \ne 0$. -/
theorem normal_form (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate) {x : Fin 4 → ℤ_[p]}
    (hx : ∃ i, IsUnit (x i)) (hQx : Q.eval x = 0) :
    ∃ c : Fin 4 → Fin 4 → ℤ_[p], IsUnit (Matrix.of c).det ∧ Q.eval (c 0) = 0 ∧ bl Q (c 0) (c 1) ≠ 0 ∧
      bl Q (c 0) (c 2) = 0 ∧ bl Q (c 0) (c 3) = 0 ∧ Q.eval (c 2) ≠ 0 := by
  obtain ⟨c1, hc1, hc10⟩ := step1 hx
  have h0 : Q.eval (c1 0) = 0 := by rw [hc10]; exact hQx
  obtain ⟨c2, hc2, hc20, hc21, hmax⟩ := step2 Q hnd c1 hc1 h0
  obtain ⟨c3, hc3, hc30, hc31, h32, h33⟩ := step3 Q c2 hc2 hc21 hmax
  have h31 : bl Q (c3 0) (c3 1) ≠ 0 := by rw [hc30, hc31]; exact hc21
  obtain ⟨c4, hc4, hc40, hc41, h42, h43, hq⟩ := step4 Q hnd c3 hc3 h32 h33
  refine ⟨c4, hc4, ?_, ?_, h42, h43, hq⟩
  · rw [hc40, hc30, hc20]; exact h0
  · rw [hc40, hc41]; exact h31

end Normal

/-! ### Lemma 9.3 and its Corollary -/

section Main

variable {p : ℕ} [Fact p.Prime]

/-- **Lemma 9.3 with its Corollary** (Cassels, Ch. 11, pp. 243–245), for one prime: the data $t$, $\Delta$ satisfy
(i)–(iii) and the Corollary simultaneously. -/
theorem lemma93_with_cor (Q : QuadForm ℤ_[p] 4) (hnd : Q.Nondegenerate)
    (hiso : (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p]) :
    ∃ (t : Fin 4 → ℤ_[p]) (B : Matrix (Fin 4) (Fin 3) ℤ_[p]) (g : QuadForm ℤ_[p] 3), Lemma93Data p Q t B g ∧
      ∀ z : ℤ_[p], ‖z‖ < ‖Q.eval t‖ → ∃ y : Fin 3 → ℤ_[p], Q.eval (t + B *ᵥ y) = z := by
  have hiso' : Q.IsotropicIn ℚ_[p] := by
    obtain ⟨v, hv0, hv⟩ := hiso
    refine ⟨v, hv0, ?_⟩
    rw [← hv]
    simp [QuadForm.evalIn, QuadForm.map]
  obtain ⟨x, ⟨i, hi⟩, hx⟩ := LocalDensity.DVR.exists_primitive_of_isotropicIn ℚ_[p] Q (p : ℤ_[p])
    PadicInt.irreducible_p hiso'
  have hxu : IsUnit (x i) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    exact hi ((PadicInt.norm_lt_one_iff_dvd _).mp (lt_of_not_ge hlt))
  obtain ⟨c, hc, hc0, hc01, hc02, hc03, hc2⟩ := normal_form Q hnd ⟨i, hxu⟩ hx
  set E := colMat c with hEdef
  have hE : IsUnit E.det := by rwa [hEdef, colMat, det_transpose]
  have k00 : (pull Q E).coeff 0 0 = 0 := by rw [coeff00, pull_eval, hEdef, colMat_single, hc0]
  have k01 : (pull Q E).coeff 0 1 ≠ 0 := by
    rw [coeff01, pull_bl, hEdef, colMat_single, colMat_single]; exact hc01
  have k02 : (pull Q E).coeff 0 2 = 0 := by
    rw [coeff02, pull_bl, hEdef, colMat_single, colMat_single]; exact hc02
  have k03 : (pull Q E).coeff 0 3 = 0 := by
    rw [coeff03, pull_bl, hEdef, colMat_single, colMat_single]; exact hc03
  have k22 : (pull Q E).coeff 2 2 ≠ 0 := by rw [coeff22, pull_eval, hEdef, colMat_single]; exact hc2
  obtain ⟨t, B, g, hD, hC⟩ := core (pull Q E) k00 k02 k03 k01 k22
  refine ⟨E *ᵥ t, E * B, g, transfer Q E hE hD, ?_⟩
  intro z hz
  rw [← pull_eval] at hz
  obtain ⟨y, hy⟩ := hC z hz
  exact ⟨y, by rw [← mulVec_mulVec, ← mulVec_add, ← pull_eval]; exact hy⟩

end Main

end QuadFormsKB.Cassels.Ch11L93

namespace QuadFormsKB.Cassels

/-- **Cassels, Ch. 11, Lemma 9.3** (p. 243), proved: *let $Q$ be a regular isotropic quaternary form over
$\mathbb Z_p$. Then there are $t \in \mathbb Z_p^4$ with $Q(t) \ne 0$ and a lattice $\Delta$ in the $3$-dimensional space
normal to $t$ with (i) $-Q(t)$ represented by $Q$ on $\Delta$; (ii) if $|Q(t+c)|_p < |Q(t)|_p$, $c \in \Delta$, then
$t + c$ is primitive in $\mathbb Z_p^4$; (iii) $\theta(\Delta) \supseteq U_p$.* The named statement `Lemma93` (formal
reading in `Lemma93Data`), discharged by Cassels' own construction (`Ch11L93.lemma93_with_cor`). -/
@[kb "cassels1978" "Ch. 11, Lemma 9.3, pp. 243–245 (proved)"]
theorem lemma93_holds : Lemma93 :=
  ⟨fun p _ Q hnd hiso => by
    obtain ⟨t, B, g, h, -⟩ := Ch11L93.lemma93_with_cor Q hnd hiso
    exact ⟨t, B, g, h⟩⟩

/-- **Cassels, Ch. 11, Corollary to Lemma 9.3** (p. 245), proved: *for every $z \in \mathbb Z_p$ with
$|z|_p < |Q(t)|_p$ there is $c \in \Delta$ with $Q(t + c) = z$* (Cassels: "Clear"; here $Q$ takes every value of
$p^\mu\mathbb Z_p$ on $t + \Delta$ and $|Q(t)|_p = p^{-\mu}$). The named statement `Lemma93Cor`. -/
@[kb "cassels1978" "Ch. 11, Corollary to Lemma 9.3, p. 245 (proved)"]
theorem lemma93Cor_holds : Lemma93Cor :=
  ⟨fun p _ Q hnd hiso => Ch11L93.lemma93_with_cor Q hnd hiso⟩

end QuadFormsKB.Cassels
