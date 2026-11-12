/-
# The even Clifford order of a ternary quadratic form (Voight, §22.3–22.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021
(open access), Chapter 22. Bibliography key `voight2021`.

**The construction.** Let $R$ be a commutative ring and
$$Q(x_0, x_1, x_2) = a x_0^2 + b x_1^2 + c x_2^2 + u x_1 x_2 + v x_0 x_2 + w x_0 x_1$$
a ternary quadratic form over $R$ (Voight (22.3.5), with variables $x, y, z$ renamed
$x_0, x_1, x_2$; in a `QuadForm R 3` these coefficients are $a = c_{00}$, $b = c_{11}$,
$c = c_{22}$, $u = c_{12}$, $v = c_{02}$, $w = c_{01}$). Its **even Clifford algebra**
$\operatorname{Clf}^0(Q)$ is the free $R$-module with basis $1, i, j, k$, where (Voight's
$e_1, e_2, e_3$ are $e_0, e_1, e_2$ here) $i = e_1 e_2$, $j = e_2 e_0$, $k = e_0 e_1$, and
multiplication table (Voight (22.1.2), (22.3.7), (22.3.8))
$$i^2 = u i - bc, \quad j^2 = v j - ac, \quad k^2 = w k - ab,$$
$$jk = a\bar i = a(u - i), \quad ki = b \bar j = b(v - j), \quad ij = c \bar k = c(w - k),$$
$$kj = -vw + a i + w j + v k, \quad ik = -uw + w i + b j + u k, \quad ji = -uv + v i + u j + c k,$$
where $\bar\alpha$ is the standard involution ($\bar i = u - i$, $\bar j = v - j$, $\bar k = w - k$).
Voight takes this table as the definition of $\operatorname{Clf}^0(Q)$ in the free case
("this could also be taken as the definition when $R$ is a principal ideal domain and $M = R^3$", 22.3.2).

Here the table is the definition (`EvenClf`, `Clf0`), and we prove (for every commutative ring $R$):
* it is an associative $R$-algebra (`EvenClf.instRing`, `EvenClf.instAlgebra`): the lattice
  $R + Ri + Rj + Rk$ is closed under an associative multiplication;
* the reversal map $\alpha \mapsto \operatorname{trd}(\alpha) - \alpha$ is a standard involution
  with the reduced trace and norm of Voight (22.3.18) (`EvenClf.mul_conj`, `EvenClf.conj_mul`,
  `EvenClf.conj_mul_conj`), Lemma 22.3.17;
* $\operatorname{trd}((ij - ji)k) = -N$ where $N = 4abc + uvw - au^2 - bv^2 - cw^2$ is the
  half-discriminant of $Q$ (`EvenClf.trd_commutator_mul_k`), Voight (22.3.20), the computation behind
  Lemma 22.3.19 $\operatorname{discrd}(\operatorname{Clf}^0(Q)) = N R$;
* the dual basis of the trace-zero part of the dual lattice, Voight (22.4.13), and the key identity
  (22.4.14): $\operatorname{nrd}(x\, Ni^\sharp + y\, Nj^\sharp + z\, Nk^\sharp) = N\, Q(x,y,z)$
  (`EvenClf.nrd_dualVec`), the computational heart of Proposition 22.4.12;
* Example 22.3.10 (the diagonal case: $\operatorname{Clf}^0$ of $b x_0^2 + a x_1^2 - x_2^2$ is the
  standard order $R\langle i, j\rangle$ of $(a,b)$, `EvenClf.diagEquiv`) and Example 22.3.12
  ($\operatorname{Clf}^0(x_0 x_1 - x_2^2) \cong M_2(R)$, `EvenClf.matrixEquiv`).

The identification of `EvenClf` with Mathlib's even Clifford algebra `CliffordAlgebra.even` of the
form is in `QuadFormsKB/Literature/Voight/EvenCliffordMathlib.lean`.

Indices are 0-based throughout (Voight's $e_1, e_2, e_3$ and $x, y, z$ are $e_0, e_1, e_2$ and
$x_0, x_1, x_2$); the names $i, j, k$ and $a, b, c, u, v, w$ are Voight's.
-/
import QuadFormsKB.Defs.QuadForm

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Quaternion

namespace QuadFormsKB.Voight

/-! ## The algebra given by the multiplication table -/

/-- **The even Clifford algebra by its multiplication table** (Voight 2021, 22.3.4, (22.3.7)).

For a commutative ring $R$ and $a, b, c, u, v, w \in R$ (the coefficients of
$Q = a x_0^2 + b x_1^2 + c x_2^2 + u x_1x_2 + v x_0x_2 + w x_0x_1$), an element is
$\alpha = t + x\, i + y\, j + z\, k$ with fields `re` $= t$, `i` $= x$, `j` $= y$, `k` $= z$, and the
multiplication is given by the table in the module docstring. The ring structure is
`EvenClf.instRing`; for a `QuadForm R 3` use `Clf0`. -/
@[ext]
structure EvenClf (R : Type*) (a b c u v w : R) where
  /-- The coefficient $t$ of $1$. -/
  re : R
  /-- The coefficient of $i = e_1 e_2$. -/
  i : R
  /-- The coefficient of $j = e_2 e_0$. -/
  j : R
  /-- The coefficient of $k = e_0 e_1$. -/
  k : R

namespace EvenClf

variable {R : Type*} [CommRing R] {a b c u v w : R}

/-- The equivalence with $R^4$ (coordinates $t, x, y, z$). -/
def equivProd (a b c u v w : R) : EvenClf R a b c u v w ≃ R × R × R × R where
  toFun x := ⟨x.1, x.2, x.3, x.4⟩
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

instance : Zero (EvenClf R a b c u v w) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (EvenClf R a b c u v w) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add (EvenClf R a b c u v w) := ⟨fun x y => ⟨x.1 + y.1, x.2 + y.2, x.3 + y.3, x.4 + y.4⟩⟩
instance : Neg (EvenClf R a b c u v w) := ⟨fun x => ⟨-x.1, -x.2, -x.3, -x.4⟩⟩
instance : Sub (EvenClf R a b c u v w) := ⟨fun x y => ⟨x.1 - y.1, x.2 - y.2, x.3 - y.3, x.4 - y.4⟩⟩
instance {S : Type*} [SMul S R] : SMul S (EvenClf R a b c u v w) :=
  ⟨fun s x => ⟨s • x.1, s • x.2, s • x.3, s • x.4⟩⟩

/-- **Multiplication** (Voight (22.3.7), (22.3.8)): for $\alpha = t + x i + y j + z k$ and
$\beta = t' + x' i + y' j + z' k$, expand bilinearly using the table in the module docstring. -/
instance : Mul (EvenClf R a b c u v w) := ⟨fun p q =>
  ⟨p.1 * q.1 - b * c * p.2 * q.2 - a * c * p.3 * q.3 - a * b * p.4 * q.4
      + a * u * p.3 * q.4 + b * v * p.4 * q.2 + c * w * p.2 * q.3
      - v * w * p.4 * q.3 - u * w * p.2 * q.4 - u * v * p.3 * q.2,
    p.1 * q.2 + p.2 * q.1 + u * p.2 * q.2 - a * p.3 * q.4 + a * p.4 * q.3
      + w * p.2 * q.4 + v * p.3 * q.2,
    p.1 * q.3 + p.3 * q.1 + v * p.3 * q.3 - b * p.4 * q.2 + w * p.4 * q.3
      + b * p.2 * q.4 + u * p.3 * q.2,
    p.1 * q.4 + p.4 * q.1 + w * p.4 * q.4 - c * p.2 * q.3 + v * p.4 * q.3
      + u * p.2 * q.4 + c * p.3 * q.2⟩⟩

@[simp] theorem zero_re : (0 : EvenClf R a b c u v w).re = 0 := rfl
@[simp] theorem zero_i : (0 : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem zero_j : (0 : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem zero_k : (0 : EvenClf R a b c u v w).k = 0 := rfl
@[simp] theorem one_re : (1 : EvenClf R a b c u v w).re = 1 := rfl
@[simp] theorem one_i : (1 : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem one_j : (1 : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem one_k : (1 : EvenClf R a b c u v w).k = 0 := rfl
section
variable (x y : EvenClf R a b c u v w)
@[simp] theorem add_re : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_i : (x + y).i = x.i + y.i := rfl
@[simp] theorem add_j : (x + y).j = x.j + y.j := rfl
@[simp] theorem add_k : (x + y).k = x.k + y.k := rfl
@[simp] theorem neg_re : (-x).re = -x.re := rfl
@[simp] theorem neg_i : (-x).i = -x.i := rfl
@[simp] theorem neg_j : (-x).j = -x.j := rfl
@[simp] theorem neg_k : (-x).k = -x.k := rfl
@[simp] theorem sub_re : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_i : (x - y).i = x.i - y.i := rfl
@[simp] theorem sub_j : (x - y).j = x.j - y.j := rfl
@[simp] theorem sub_k : (x - y).k = x.k - y.k := rfl
@[simp] theorem smul_re {S : Type*} [SMul S R] (s : S) : (s • x).re = s • x.re := rfl
@[simp] theorem smul_i {S : Type*} [SMul S R] (s : S) : (s • x).i = s • x.i := rfl
@[simp] theorem smul_j {S : Type*} [SMul S R] (s : S) : (s • x).j = s • x.j := rfl
@[simp] theorem smul_k {S : Type*} [SMul S R] (s : S) : (s • x).k = s • x.k := rfl
@[simp] theorem mul_re : (x * y).re = x.re * y.re - b * c * x.i * y.i - a * c * x.j * y.j
    - a * b * x.k * y.k + a * u * x.j * y.k + b * v * x.k * y.i + c * w * x.i * y.j
    - v * w * x.k * y.j - u * w * x.i * y.k - u * v * x.j * y.i := rfl
@[simp] theorem mul_i : (x * y).i = x.re * y.i + x.i * y.re + u * x.i * y.i - a * x.j * y.k
    + a * x.k * y.j + w * x.i * y.k + v * x.j * y.i := rfl
@[simp] theorem mul_j : (x * y).j = x.re * y.j + x.j * y.re + v * x.j * y.j - b * x.k * y.i
    + w * x.k * y.j + b * x.i * y.k + u * x.j * y.i := rfl
@[simp] theorem mul_k : (x * y).k = x.re * y.k + x.k * y.re + w * x.k * y.k - c * x.i * y.j
    + v * x.k * y.j + u * x.i * y.k + c * x.j * y.i := rfl
end

instance : AddCommGroup (EvenClf R a b c u v w) := by
  apply (equivProd a b c u v w).injective.addCommGroup <;> intros <;> rfl

instance : Module R (EvenClf R a b c u v w) := by
  refine (equivProd a b c u v w).injective.module R
    ⟨⟨equivProd a b c u v w, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

instance : AddCommGroupWithOne (EvenClf R a b c u v w) where
  natCast n := ⟨n, 0, 0, 0⟩
  natCast_zero := by show (⟨((0 : ℕ) : R), 0, 0, 0⟩ : EvenClf R a b c u v w) = ⟨0, 0, 0, 0⟩; simp
  natCast_succ n := by
    show (⟨((n + 1 : ℕ) : R), 0, 0, 0⟩ : EvenClf R a b c u v w) = ⟨(n : R) + 1, 0 + 0, 0 + 0, 0 + 0⟩
    simp
  intCast n := ⟨n, 0, 0, 0⟩
  intCast_ofNat n := by
    show (⟨((n : ℤ) : R), 0, 0, 0⟩ : EvenClf R a b c u v w) = ⟨(n : R), 0, 0, 0⟩; simp
  intCast_negSucc n := by
    show (⟨((Int.negSucc n : ℤ) : R), 0, 0, 0⟩ : EvenClf R a b c u v w) =
      ⟨-((n + 1 : ℕ) : R), -0, -0, -0⟩
    simp [Int.cast_negSucc]

@[simp] theorem natCast_re (n : ℕ) : (n : EvenClf R a b c u v w).re = n := rfl
@[simp] theorem natCast_i (n : ℕ) : (n : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem natCast_j (n : ℕ) : (n : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem natCast_k (n : ℕ) : (n : EvenClf R a b c u v w).k = 0 := rfl
@[simp] theorem intCast_re (n : ℤ) : (n : EvenClf R a b c u v w).re = n := rfl
@[simp] theorem intCast_i (n : ℤ) : (n : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem intCast_j (n : ℤ) : (n : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem intCast_k (n : ℤ) : (n : EvenClf R a b c u v w).k = 0 := rfl

/-- **The even Clifford algebra is an associative ring** (Voight 2021, 22.3.4 and Example 22.2.5:
the lattice $R + Ri + Rj + Rk$ "is closed under multiplication"). Associativity is a polynomial
identity in the coordinates and the six coefficients, valid over every commutative ring. -/
@[kb "voight2021" "22.3.4, (22.3.7), p. 360"]
instance instRing : Ring (EvenClf R a b c u v w) where
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

instance instAlgebra : Algebra R (EvenClf R a b c u v w) where
  algebraMap :=
  { toFun r := ⟨r, 0, 0, 0⟩
    map_one' := rfl
    map_zero' := rfl
    map_mul' x y := by ext <;> simp
    map_add' x y := by ext <;> simp }
  smul_def' s x := by ext <;> simp
  commutes' s x := by ext <;> simp <;> ring

@[simp] theorem algebraMap_re (r : R) : (algebraMap R (EvenClf R a b c u v w) r).re = r := rfl
@[simp] theorem algebraMap_i (r : R) : (algebraMap R (EvenClf R a b c u v w) r).i = 0 := rfl
@[simp] theorem algebraMap_j (r : R) : (algebraMap R (EvenClf R a b c u v w) r).j = 0 := rfl
@[simp] theorem algebraMap_k (r : R) : (algebraMap R (EvenClf R a b c u v w) r).k = 0 := rfl

/-! ## The basis $1, i, j, k$ -/

/-- The basis element $i = e_1 e_2$. -/
def ei : EvenClf R a b c u v w := ⟨0, 1, 0, 0⟩
/-- The basis element $j = e_2 e_0$. -/
def ej : EvenClf R a b c u v w := ⟨0, 0, 1, 0⟩
/-- The basis element $k = e_0 e_1$. -/
def ek : EvenClf R a b c u v w := ⟨0, 0, 0, 1⟩

@[simp] theorem ei_re : (ei : EvenClf R a b c u v w).re = 0 := rfl
@[simp] theorem ei_i : (ei : EvenClf R a b c u v w).i = 1 := rfl
@[simp] theorem ei_j : (ei : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem ei_k : (ei : EvenClf R a b c u v w).k = 0 := rfl
@[simp] theorem ej_re : (ej : EvenClf R a b c u v w).re = 0 := rfl
@[simp] theorem ej_i : (ej : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem ej_j : (ej : EvenClf R a b c u v w).j = 1 := rfl
@[simp] theorem ej_k : (ej : EvenClf R a b c u v w).k = 0 := rfl
@[simp] theorem ek_re : (ek : EvenClf R a b c u v w).re = 0 := rfl
@[simp] theorem ek_i : (ek : EvenClf R a b c u v w).i = 0 := rfl
@[simp] theorem ek_j : (ek : EvenClf R a b c u v w).j = 0 := rfl
@[simp] theorem ek_k : (ek : EvenClf R a b c u v w).k = 1 := rfl

/-- Every element is $t + x i + y j + z k$. -/
theorem eq_sum (x : EvenClf R a b c u v w) :
    x = algebraMap R _ x.re + x.i • ei + x.j • ej + x.k • ek := by
  ext <;> simp

/-- The $R$-basis $1, i, j, k$: `EvenClf` is free of rank $4$ (Voight 2021, 22.2.9 / 22.3.4). -/
noncomputable def basisOneIJK : Module.Basis (Fin 4) R (EvenClf R a b c u v w) :=
  .ofEquivFun
    { toFun := fun x => ![x.re, x.i, x.j, x.k]
      invFun := fun f => ⟨f 0, f 1, f 2, f 3⟩
      left_inv := fun _ => rfl
      right_inv := fun f => by ext n; fin_cases n <;> rfl
      map_add' := fun _ _ => by ext n; fin_cases n <;> rfl
      map_smul' := fun _ _ => by ext n; fin_cases n <;> rfl }

instance : Module.Free R (EvenClf R a b c u v w) := .of_basis basisOneIJK
instance : Module.Finite R (EvenClf R a b c u v w) := .of_basis basisOneIJK

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R (EvenClf R a b c u v w) = 4 := by
  rw [Module.finrank_eq_card_basis basisOneIJK, Fintype.card_fin]

/-- **The multiplication table** (Voight (22.1.2), (22.3.7)): $i^2 = ui - bc$, $j^2 = vj - ac$,
$k^2 = wk - ab$, $jk = a(u - i)$, $ki = b(v - j)$, $ij = c(w - k)$. -/
@[kb "voight2021" "(22.1.2), p. 354; (22.3.7), p. 360"]
theorem mul_table :
    (ei : EvenClf R a b c u v w) * ei = u • ei - algebraMap R _ (b * c) ∧
    (ej : EvenClf R a b c u v w) * ej = v • ej - algebraMap R _ (a * c) ∧
    (ek : EvenClf R a b c u v w) * ek = w • ek - algebraMap R _ (a * b) ∧
    (ej : EvenClf R a b c u v w) * ek = a • (algebraMap R _ u - ei) ∧
    (ek : EvenClf R a b c u v w) * ei = b • (algebraMap R _ v - ej) ∧
    (ei : EvenClf R a b c u v w) * ej = c • (algebraMap R _ w - ek) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

/-- **The skew products** (Voight (22.3.8)): $kj = -vw + ai + wj + vk$, $ik = -uw + wi + bj + uk$,
$ji = -uv + vi + uj + ck$. -/
@[kb "voight2021" "(22.3.8), p. 360"]
theorem mul_table_skew :
    (ek : EvenClf R a b c u v w) * ej = algebraMap R _ (-(v * w)) + a • ei + w • ej + v • ek ∧
    (ei : EvenClf R a b c u v w) * ek = algebraMap R _ (-(u * w)) + w • ei + b • ej + u • ek ∧
    (ej : EvenClf R a b c u v w) * ei = algebraMap R _ (-(u * v)) + v • ei + u • ej + c • ek := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

/-- Voight (22.3.9): $ijk = jki = kij = abc$. -/
@[kb "voight2021" "(22.3.9), p. 360"]
theorem ijk_eq :
    (ei : EvenClf R a b c u v w) * ej * ek = algebraMap R _ (a * b * c) ∧
    (ej : EvenClf R a b c u v w) * ek * ei = algebraMap R _ (a * b * c) ∧
    (ek : EvenClf R a b c u v w) * ei * ej = algebraMap R _ (a * b * c) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

/-! ## The standard involution, reduced trace and reduced norm -/

/-- **The reduced trace** (Voight (22.3.18)): $\tau(t + xi + yj + zk) = 2t + ux + vy + wz$. -/
def trd (x : EvenClf R a b c u v w) : R := 2 * x.re + u * x.i + v * x.j + w * x.k

/-- **The reduced norm** (Voight (22.3.18)):
$\nu(t + xi + yj + zk) = t^2 + utx + vty + wtz + bc x^2 + (uv - cw)xy + (uw - bv)xz + ac y^2
+ (vw - au) yz + ab z^2$. -/
@[kb "voight2021" "(22.3.18), p. 362"]
def nrd (x : EvenClf R a b c u v w) : R :=
  x.re ^ 2 + u * x.re * x.i + v * x.re * x.j + w * x.re * x.k + b * c * x.i ^ 2
    + (u * v - c * w) * x.i * x.j + (u * w - b * v) * x.i * x.k + a * c * x.j ^ 2
    + (v * w - a * u) * x.j * x.k + a * b * x.k ^ 2

/-- **The reversal involution** $\bar\alpha = \operatorname{trd}(\alpha) - \alpha$ (Voight 22.3.4 and
Lemma 22.3.17): $\bar i = u - i$, $\bar j = v - j$, $\bar k = w - k$. -/
def conj (x : EvenClf R a b c u v w) : EvenClf R a b c u v w :=
  ⟨x.re + u * x.i + v * x.j + w * x.k, -x.i, -x.j, -x.k⟩

@[simp] theorem conj_re (x : EvenClf R a b c u v w) :
    (conj x).re = x.re + u * x.i + v * x.j + w * x.k := rfl
@[simp] theorem conj_i (x : EvenClf R a b c u v w) : (conj x).i = -x.i := rfl
@[simp] theorem conj_j (x : EvenClf R a b c u v w) : (conj x).j = -x.j := rfl
@[simp] theorem conj_k (x : EvenClf R a b c u v w) : (conj x).k = -x.k := rfl

theorem conj_eq_trd_sub (x : EvenClf R a b c u v w) : conj x = algebraMap R _ (trd x) - x := by
  ext <;> simp [trd] <;> ring

theorem conj_conj (x : EvenClf R a b c u v w) : conj (conj x) = x := by
  ext <;> simp <;> ring

theorem conj_add (x y : EvenClf R a b c u v w) : conj (x + y) = conj x + conj y := by
  ext <;> simp <;> ring

/-- **The involution is an anti-automorphism**: $\overline{\alpha\beta} = \bar\beta\bar\alpha$. -/
theorem conj_mul (x y : EvenClf R a b c u v w) : conj (x * y) = conj y * conj x := by
  ext <;> simp <;> ring

/-- **Standard involution** (Voight Lemma 22.3.17, (22.3.18)):
$\alpha \bar\alpha = \nu(\alpha) \in R$. -/
@[kb "voight2021" "Lemma 22.3.17, p. 361"]
theorem mul_conj (x : EvenClf R a b c u v w) : x * conj x = algebraMap R _ (nrd x) := by
  ext <;> simp only [nrd, trd, mul_re, mul_i, mul_j, mul_k, conj_re, conj_i, conj_j, conj_k, algebraMap_re, algebraMap_i, algebraMap_j, algebraMap_k, sub_re, sub_i, sub_j, sub_k, add_re, add_i, add_j, add_k, smul_re, smul_i, smul_j, smul_k, smul_eq_mul, zero_re, zero_i, zero_j, zero_k] <;> ring

theorem conj_mul_self (x : EvenClf R a b c u v w) : conj x * x = algebraMap R _ (nrd x) := by
  ext <;> simp only [nrd, trd, mul_re, mul_i, mul_j, mul_k, conj_re, conj_i, conj_j, conj_k, algebraMap_re, algebraMap_i, algebraMap_j, algebraMap_k, sub_re, sub_i, sub_j, sub_k, add_re, add_i, add_j, add_k, smul_re, smul_i, smul_j, smul_k, smul_eq_mul, zero_re, zero_i, zero_j, zero_k] <;> ring

/-- **Every element satisfies its reduced characteristic polynomial** (Voight Lemma 22.3.17):
$\alpha^2 - \tau(\alpha)\alpha + \nu(\alpha) = 0$. -/
@[kb "voight2021" "Lemma 22.3.17, p. 361"]
theorem sq_sub_trd_mul_add_nrd (x : EvenClf R a b c u v w) :
    x * x - trd x • x + algebraMap R _ (nrd x) = 0 := by
  ext <;> simp only [nrd, trd, mul_re, mul_i, mul_j, mul_k, conj_re, conj_i, conj_j, conj_k, algebraMap_re, algebraMap_i, algebraMap_j, algebraMap_k, sub_re, sub_i, sub_j, sub_k, add_re, add_i, add_j, add_k, smul_re, smul_i, smul_j, smul_k, smul_eq_mul, zero_re, zero_i, zero_j, zero_k] <;> ring

/-- The reduced norm is multiplicative. -/
theorem nrd_mul (x y : EvenClf R a b c u v w) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd, mul_re, mul_i, mul_j, mul_k]; ring

theorem trd_add (x y : EvenClf R a b c u v w) : trd (x + y) = trd x + trd y := by
  simp [trd]; ring

theorem trd_smul (r : R) (x : EvenClf R a b c u v w) : trd (r • x) = r * trd x := by
  simp [trd]; ring

/-! ## The discriminant -/

/-- **The (half-)discriminant** of the ternary form with coefficients $a, b, c, u, v, w$
(Voight (22.3.6)): $N = 4abc + uvw - au^2 - bv^2 - cw^2$. It is half the determinant of the
Gram (Hessian) matrix $\begin{pmatrix} 2a & w & v \\ w & 2b & u \\ v & u & 2c\end{pmatrix}$. -/
def halfDisc (a b c u v w : R) : R := 4 * a * b * c + u * v * w - a * u ^ 2 - b * v ^ 2 - c * w ^ 2

/-- **The alternating trilinear form on $i, j, k$** (Voight (22.3.20)):
$m(i,j,k) = \operatorname{trd}((ij - ji)\bar k) = -N$ (equivalently
$\operatorname{trd}((ij - ji)k) = N$, since $\operatorname{trd}(ij - ji) = 0$). Together with Lemma 15.4.7 this gives
$\operatorname{discrd}(\operatorname{Clf}^0(Q)) = N R$ (Lemma 22.3.19). -/
@[kb "voight2021" "Lemma 22.3.19, (22.3.20), p. 362"]
theorem trd_commutator_mul_k :
    trd (((ei : EvenClf R a b c u v w) * ej - ej * ei) * conj ek) = -halfDisc a b c u v w ∧
    trd (((ei : EvenClf R a b c u v w) * ej - ej * ei) * ek) = halfDisc a b c u v w := by
  constructor <;> simp [trd, halfDisc] <;> ring

/-- **The discriminant of the basis $1, i, j, k$** (Voight (22.3.21)): the determinant of the
reduced-trace Gram matrix $(\operatorname{trd}(e_p e_q))_{p,q}$ is $-N^2$. -/
@[kb "voight2021" "(22.3.21), p. 362"]
theorem det_trd_gram :
    (Matrix.of fun p q : Fin 4 =>
      trd ((![1, ei, ej, ek] : Fin 4 → EvenClf R a b c u v w) p *
        (![1, ei, ej, ek] : Fin 4 → EvenClf R a b c u v w) q)).det = -(halfDisc a b c u v w) ^ 2 := by
  have hG : (Matrix.of fun p q : Fin 4 =>
      trd ((![1, ei, ej, ek] : Fin 4 → EvenClf R a b c u v w) p *
        (![1, ei, ej, ek] : Fin 4 → EvenClf R a b c u v w) q)) =
      !![2, u, v, w; u, u ^ 2 - 2 * b * c, c * w, b * v; v, c * w, v ^ 2 - 2 * a * c, a * u;
        w, b * v, a * u, w ^ 2 - 2 * a * b] := by
    ext p q; fin_cases p <;> fin_cases q <;> simp [trd] <;> ring
  rw [hG, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, halfDisc]
  ring

/-! ## The dual basis and the reduced norm on it (Proposition 22.4.12) -/

/-- $N i^\sharp = jk - kj$ (Voight (22.4.13)). -/
def dualI : EvenClf R a b c u v w := ej * ek - ek * ej
/-- $N j^\sharp = ki - ik$ (Voight (22.4.13)). -/
def dualJ : EvenClf R a b c u v w := ek * ei - ei * ek
/-- $N k^\sharp = ij - ji$ (Voight (22.4.13)). -/
def dualK : EvenClf R a b c u v w := ei * ej - ej * ei

/-- **Explicit dual basis** (Voight (22.4.13)):
$N i^\sharp = (au + vw) - 2ai - wj - vk$, $N j^\sharp = (bv + uw) - wi - 2bj - uk$,
$N k^\sharp = (cw + uv) - vi - uj - 2ck$. -/
@[kb "voight2021" "(22.4.13), p. 366"]
theorem dual_eq :
    (dualI : EvenClf R a b c u v w) = ⟨a * u + v * w, -2 * a, -w, -v⟩ ∧
    (dualJ : EvenClf R a b c u v w) = ⟨b * v + u * w, -w, -2 * b, -u⟩ ∧
    (dualK : EvenClf R a b c u v w) = ⟨c * w + u * v, -v, -u, -2 * c⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [dualI, dualJ, dualK] <;> ring

/-- **Dual basis property** (Voight, proof of Proposition 22.4.12): with respect to the reduced
trace pairing $\langle \alpha, \beta\rangle = \operatorname{trd}(\alpha\beta)$, the elements
$N i^\sharp, N j^\sharp, N k^\sharp$ pair with $1, i, j, k$ as $N$ times the dual basis of $i, j, k$:
$\operatorname{trd}(e_p \cdot N e_q^\sharp) = N \delta_{pq}$ for $e = (1, i, j, k)$ and
$q \in \{i, j, k\}$. In particular they have trace zero, so they span $(O^\sharp)^0$ up to $N$. -/
@[kb "voight2021" "Proposition 22.4.12, p. 366"]
theorem trd_mul_dual :
    let N := halfDisc a b c u v w
    let e : Fin 4 → EvenClf R a b c u v w := ![1, ei, ej, ek]
    let d : Fin 3 → EvenClf R a b c u v w := ![dualI, dualJ, dualK]
    ∀ p q, trd (e p * d q) = if p = q.succ then N else 0 := by
  intro N e d p q
  obtain ⟨h1, h2, h3⟩ := dual_eq (R := R) (a := a) (b := b) (c := c) (u := u) (v := v) (w := w)
  fin_cases p <;> fin_cases q <;>
    simp [e, d, h1, h2, h3, trd, N, halfDisc, Fin.ext_iff] <;> ring

/-- The vector $x\,(N i^\sharp) + y\,(N j^\sharp) + z\,(N k^\sharp)$ of $N (O^\sharp)^0$. -/
def dualVec (x y z : R) : EvenClf R a b c u v w := x • dualI + y • dualJ + z • dualK

/-- **The reduced norm on the trace-zero dual** (Voight (22.4.14), Proposition 22.4.12):
$$\operatorname{nrd}\bigl(x\,(Ni^\sharp) + y\,(Nj^\sharp) + z\,(Nk^\sharp)\bigr) = N\,Q(x,y,z),
\qquad Q = ax^2 + by^2 + cz^2 + uyz + vxz + wxy.$$
Dividing by $N$ (when $N \ne 0$): the ternary form $N \operatorname{nrd}^\sharp$ attached to
$\operatorname{Clf}^0(Q)$ in 22.4.8 is $Q$ itself, which is the first half of Proposition 22.4.12. -/
@[kb "voight2021" "(22.4.14), Proposition 22.4.12, p. 366"]
theorem nrd_dualVec (x y z : R) :
    nrd (dualVec x y z : EvenClf R a b c u v w) =
      halfDisc a b c u v w *
        (a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + u * y * z + v * x * z + w * x * y) := by
  obtain ⟨h1, h2, h3⟩ := dual_eq (R := R) (a := a) (b := b) (c := c) (u := u) (v := v) (w := w)
  simp only [dualVec, h1, h2, h3, nrd, add_re, add_i, add_j, add_k, smul_re, smul_i, smul_j,
    smul_k, smul_eq_mul, halfDisc]
  ring

/-- Voight (22.4.16): $(Ni^\sharp)^2 = -aN$, $(Nj^\sharp)^2 = -bN$, $(Nk^\sharp)^2 = -cN$. -/
@[kb "voight2021" "(22.4.16), p. 367"]
theorem dual_sq :
    (dualI : EvenClf R a b c u v w) * dualI = algebraMap R _ (-(a * halfDisc a b c u v w)) ∧
    (dualJ : EvenClf R a b c u v w) * dualJ = algebraMap R _ (-(b * halfDisc a b c u v w)) ∧
    (dualK : EvenClf R a b c u v w) * dualK = algebraMap R _ (-(c * halfDisc a b c u v w)) := by
  obtain ⟨h1, h2, h3⟩ := dual_eq (R := R) (a := a) (b := b) (c := c) (u := u) (v := v) (w := w)
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp only [h1, h2, h3, halfDisc, mul_re, mul_i, mul_j, mul_k, algebraMap_re, algebraMap_i, algebraMap_j, algebraMap_k] <;> ring

/-! ## Two worked examples -/

/-- **Example 22.3.10 (the diagonal case)**: for $a, b \in R$ the order $R\langle i, j\rangle =
R + Ri + Rj + Rij$ of the quaternion algebra $(a, b \mid R)$ (Mathlib's `ℍ[R,a,b]`, with
$i^2 = a$, $j^2 = b$, $k = ij$) is the even Clifford algebra of $b x_0^2 + a x_1^2 - x_2^2$:
the coefficients are $(a, b, c, u, v, w) = (b, a, -1, 0, 0, 0)$ in Voight's naming, so the
table (22.3.7) reads $i^2 = a$, $j^2 = b$, $k^2 = -ab$, $jk = b\bar i$, $ki = a\bar j$, $ij = -\bar k = k$
(Voight (22.3.11)). The isomorphism sends $1, i, j, k$ to $1, i, j, k$. -/
@[kb "voight2021" "Example 22.3.10, p. 361"]
def diagEquiv (a b : R) : EvenClf R b a (-1) 0 0 0 ≃ₐ[R] ℍ[R,a,b] where
  toFun x := ⟨x.re, x.i, x.j, x.k⟩
  invFun x := ⟨x.re, x.imI, x.imJ, x.imK⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := rfl
  commutes' r := rfl

/-- **Example 22.3.12**: for $Q = x_0 x_1 - x_2^2$, i.e. $(a,b,c,u,v,w) = (0,0,-1,0,0,1)$, with
$\operatorname{disc}(Q) = 1$, the even Clifford algebra is $M_2(R)$ (Voight (22.3.14)) via
$$i \mapsto \begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
j \mapsto \begin{pmatrix}0&0\\-1&0\end{pmatrix},\quad
k \mapsto \begin{pmatrix}0&0\\0&1\end{pmatrix}.$$ -/
@[kb "voight2021" "Example 22.3.12, (22.3.14), p. 361"]
def matrixEquiv : EvenClf R 0 0 (-1) 0 0 1 ≃ₐ[R] Matrix (Fin 2) (Fin 2) R where
  toFun x := !![x.re, x.i; -x.j, x.re + x.k]
  invFun m := ⟨m 0 0, m 0 1, -m 1 0, m 1 1 - m 0 0⟩
  left_inv x := by ext <;> simp
  right_inv m := by ext p q; fin_cases p <;> fin_cases q <;> simp
  map_mul' x y := by
    ext p q; fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_add' x y := by
    ext p q; fin_cases p <;> fin_cases q <;> simp <;> ring
  commutes' r := by
    ext p q; fin_cases p <;> fin_cases q <;> simp [Matrix.algebraMap_eq_diagonal]

theorem halfDisc_matrixExample : halfDisc (0 : R) 0 (-1) 0 0 1 = 1 := by
  simp [halfDisc]

end EvenClf

/-! ## The even Clifford algebra of a `QuadForm R 3` -/

section Clf0

variable {R : Type*} [CommRing R]

/-- **The even Clifford algebra $\operatorname{Clf}^0(Q)$ of a ternary form** $Q$ over a commutative
ring $R$ (Voight 2021, 22.1 and 22.3.4): `EvenClf` with Voight's coefficients
$a = c_{00}$, $b = c_{11}$, $c = c_{22}$, $u = c_{12}$, $v = c_{02}$, $w = c_{01}$, where
$Q = \sum_{p \le q} c_{pq} x_p x_q$ (0-based). -/
@[kb "voight2021" "22.1, (22.1.2), p. 354; 22.3.4, p. 360"]
abbrev Clf0 (Q : QuadForm R 3) : Type _ :=
  EvenClf R (Q.coeff 0 0) (Q.coeff 1 1) (Q.coeff 2 2) (Q.coeff 1 2) (Q.coeff 0 2) (Q.coeff 0 1)

/-- **The half-discriminant** $N = \operatorname{disc}(Q) = 4abc + uvw - au^2 - bv^2 - cw^2$ of a
ternary form (Voight (22.3.6)); a form is nondegenerate iff $N \ne 0$ (over a domain). -/
@[kb "voight2021" "(22.3.6), p. 360"]
def ternaryDisc (Q : QuadForm R 3) : R :=
  EvenClf.halfDisc (Q.coeff 0 0) (Q.coeff 1 1) (Q.coeff 2 2) (Q.coeff 1 2) (Q.coeff 0 2) (Q.coeff 0 1)

/-- The value of a ternary form in Voight's coordinates:
$Q(x_0, x_1, x_2) = a x_0^2 + b x_1^2 + c x_2^2 + u x_1 x_2 + v x_0 x_2 + w x_0 x_1$. -/
theorem eval_ternary (Q : QuadForm R 3) (x : Fin 3 → R) :
    Q.eval x = Q.coeff 0 0 * x 0 ^ 2 + Q.coeff 1 1 * x 1 ^ 2 + Q.coeff 2 2 * x 2 ^ 2
      + Q.coeff 1 2 * x 1 * x 2 + Q.coeff 0 2 * x 0 * x 2 + Q.coeff 0 1 * x 0 * x 1 := by
  simp only [QuadForm.evalIn, Fin.sum_univ_three, Fin.reduceLE, Algebra.algebraMap_self,
    RingHom.id_apply, ite_true, ite_false]
  ring

/-- $2N = \det$ of the Hessian (Gram) matrix $Q + Q^{\mathsf T}$ of the coefficient matrix. -/
theorem two_mul_ternaryDisc (Q : QuadForm R 3) : 2 * ternaryDisc Q = Q.hessian.det := by
  have h10 : Q.coeff 1 0 = 0 := Q.upper (by decide)
  have h20 : Q.coeff 2 0 = 0 := Q.upper (by decide)
  have h21 : Q.coeff 2 1 = 0 := Q.upper (by decide)
  simp [ternaryDisc, EvenClf.halfDisc, QuadForm.hessian, Matrix.det_fin_three, h10, h20, h21]
  ring

/-- **Proposition 22.4.12, first half, for $\operatorname{Clf}^0(Q)$**: the reduced norm on
$N (O^\sharp)^0 = R\,Ni^\sharp + R\,Nj^\sharp + R\,Nk^\sharp$ is $N$ times $Q$:
$\operatorname{nrd}(x_0\, Ni^\sharp + x_1\, Nj^\sharp + x_2\, Nk^\sharp) = N\, Q(x_0, x_1, x_2)$.
Hence the form $N\operatorname{nrd}^\sharp$ of 22.4.8 recovers $Q$ (exactly, in this basis). -/
@[kb "voight2021" "Proposition 22.4.12, (22.4.14), p. 366"]
theorem nrd_dualVec_eq (Q : QuadForm R 3) (x : Fin 3 → R) :
    EvenClf.nrd (EvenClf.dualVec (x 0) (x 1) (x 2) : Clf0 Q) = ternaryDisc Q * Q.eval x := by
  rw [EvenClf.nrd_dualVec, eval_ternary, ternaryDisc]

end Clf0

end QuadFormsKB.Voight
