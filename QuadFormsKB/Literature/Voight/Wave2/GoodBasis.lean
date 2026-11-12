/-
# Good bases: an order with a standard involution is an even Clifford algebra (Voight, 22.4.4 and 22.4.7)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, proof of Proposition 22.4.4 (p. 364) and 22.4.7
(p. 365) (key `voight2021`).

**Statement** (`exists_algEquiv_evenClf`). Let $R$ be a commutative ring and $O$ an $R$-algebra that is free with an
$R$-basis $1, i, j, k$ (`b : Module.Basis (Fin 4) R O` with `b 0 = 1`), equipped with an $R$-linear map
$\operatorname{trd} : O \to R$ and a map $\operatorname{nrd} : O \to R$ such that
* every element satisfies $x^2 = \operatorname{trd}(x)\,x - \operatorname{nrd}(x)$ (a standard involution,
  $\bar x = \operatorname{trd}(x) - x$; Voight 3.2), and
* the trace of left multiplication is $\operatorname{Tr}(L_x) = 2\operatorname{trd}(x)$ (true in a quaternion algebra;
  this is the fact Voight uses to kill the coefficients $\alpha, \beta, \gamma$).

Then $O \cong \operatorname{Clf}^0(Q)$ = `EvenClf R a b c u v w` as $R$-algebras for some $a, b, c, u, v, w \in R$, i.e. $O$ has a
**good basis** $1, i - \eta(i), j - \eta(j), k - \eta(k)$ satisfying the multiplication table (22.3.7). This is the
computational content of Proposition 22.4.4 (and of 22.4.7, over any commutative ring); what is left for
Proposition 22.4.4 itself is to produce the basis containing $1$ and the standard involution for a quaternion order
over a principal ideal domain.

**Proof** (Voight's, in coordinates). Write $X_{pq}^m$ for the $m$-th coordinate of $e_pe_q$ ($e = (1,i,j,k)$).
1. Translating $k \mapsto k - X_{23}^2$, $i \mapsto i - X_{31}^3$, $j \mapsto j - X_{12}^1$ (each translation changes only
   the constant coordinates) gives a basis with $X_{23}^2 = X_{31}^3 = X_{12}^1 = 0$ (`exists_normalized`).
2. Polarizing $x^2 = \operatorname{trd}(x)x - \operatorname{nrd}(x)$ gives $X_{pq}^m + X_{qp}^m$ for $m \ge 1$; the trace
   condition then gives $\gamma = X_{12}^2 = 0$, $\alpha = X_{23}^3 = 0$, $\beta = X_{31}^1 = 0$.
3. Associativity $(e_pe_q)e_r = e_p(e_qe_r)$ for $(p,q,r) = (2,3,3), (3,1,1), (1,2,2), (1,3,1), (2,1,2), (3,2,3)$
   determines the six remaining constant coordinates: with $a = -X_{23}^1$, $b = -X_{31}^2$, $c = -X_{12}^3$,
   $u, v, w$ the traces of $i, j, k$, the table is exactly (22.3.7).
-/
import QuadFormsKB.Literature.Voight.Wave2.SimilarOfIso

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

open Matrix

namespace QuadFormsKB.Voight

namespace GoodBasis

variable {R O : Type*} [CommRing R] [Ring O] [Algebra R O]

/-- The structure coordinates $X_{pq}^m$ of the basis $b$: the $m$-th coordinate of $b_p b_q$. -/
noncomputable def X (b : Module.Basis (Fin 4) R O) (p q m : Fin 4) : R := b.repr (b p * b q) m

section Coords

variable (b : Module.Basis (Fin 4) R O) (hb0 : b 0 = 1)
include hb0

theorem repr_one (m : Fin 4) : b.repr (1 : O) m = if m = 0 then 1 else 0 := by
  rw [← hb0, b.repr_self, Finsupp.single_apply]
  by_cases h : m = 0
  · subst h; rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem repr_algebraMap (r : R) (m : Fin 4) :
    b.repr (algebraMap R O r) m = if m = 0 then r else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, repr_one b hb0]
  split_ifs <;> simp

theorem X_zero_left (q m : Fin 4) : X b 0 q m = if q = m then 1 else 0 := by
  rw [X, hb0, one_mul, b.repr_self, Finsupp.single_apply]

theorem X_zero_right (p m : Fin 4) : X b p 0 m = if p = m then 1 else 0 := by
  rw [X, hb0, mul_one, b.repr_self, Finsupp.single_apply]

end Coords

theorem expand (b : Module.Basis (Fin 4) R O) (x : O) : x = ∑ m, b.repr x m • b m :=
  (b.sum_repr x).symm

/-- **Associativity in coordinates**: $\sum_{m'} X_{pq}^{m'}X_{m'r}^m = \sum_{m'} X_{qr}^{m'}X_{pm'}^m$. -/
theorem assoc (b : Module.Basis (Fin 4) R O) (p q r m : Fin 4) :
    ∑ m', X b p q m' * X b m' r m = ∑ m', X b q r m' * X b p m' m := by
  have h := congrArg (fun x => b.repr x m) (mul_assoc (b p) (b q) (b r))
  rw [expand b (b p * b q), Finset.sum_mul, map_sum, Finset.sum_apply'] at h
  rw [expand b (b q * b r), Finset.mul_sum, map_sum, Finset.sum_apply'] at h
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  simpa [X] using h

/-- The coordinates of a product: $(xy)_m = \sum_{p,q} x_p y_q X_{pq}^m$. -/
theorem repr_mul (b : Module.Basis (Fin 4) R O) (x y : O) (m : Fin 4) :
    b.repr (x * y) m = ∑ p, ∑ q, b.repr x p * b.repr y q * X b p q m := by
  conv_lhs => rw [expand b x, expand b y]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
    Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, X]
  rw [Finset.sum_comm]

section Involution

variable (t : O →ₗ[R] R) (nr : O → R) (hq : ∀ x : O, x * x = t x • x - algebraMap R O (nr x))
include hq

/-- **Polarization** of $x^2 = \operatorname{trd}(x)x - \operatorname{nrd}(x)$:
$xy + yx = \operatorname{trd}(x)y + \operatorname{trd}(y)x - (\operatorname{nrd}(x+y) - \operatorname{nrd}x - \operatorname{nrd}y)$. -/
theorem polar (x y : O) :
    x * y + y * x = t x • y + t y • x - algebraMap R O (nr (x + y) - nr x - nr y) := by
  have h := hq (x + y)
  rw [add_mul, mul_add, mul_add, hq x, hq y, map_add, add_smul, smul_add, smul_add] at h
  rw [map_sub, map_sub, ← sub_eq_zero, ← sub_eq_zero.2 h]
  abel

variable (b : Module.Basis (Fin 4) R O) (hb0 : b 0 = 1)
include hb0

/-- Squares in coordinates: $X_{pp}^m = \operatorname{trd}(e_p)\delta_{pm}$ for $m \ne 0$. -/
theorem X_self (p m : Fin 4) (hm : m ≠ 0) : X b p p m = if p = m then t (b p) else 0 := by
  rw [X, hq, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self,
    repr_algebraMap b hb0, if_neg hm, Finsupp.single_apply]
  split_ifs <;> simp

/-- Polarization in coordinates: $X_{pq}^m + X_{qp}^m = \operatorname{trd}(e_p)\delta_{qm} + \operatorname{trd}(e_q)\delta_{pm}$
for $m \ne 0$. -/
theorem X_add_X (p q m : Fin 4) (hm : m ≠ 0) :
    X b p q m + X b q p m = (if q = m then t (b p) else 0) + (if p = m then t (b q) else 0) := by
  have h := congrArg (fun x => b.repr x m) (polar t nr hq (b p) (b q))
  simp only [map_add, map_sub, map_smul, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    b.repr_self, repr_algebraMap b hb0, if_neg hm, Finsupp.single_apply, smul_eq_mul] at h
  rw [X, X, h]
  split_ifs <;> simp

end Involution

/-- **The trace of left multiplication in coordinates**: $\operatorname{Tr}(L_x) = \sum_m (x e_m)_m$. -/
theorem trace_mulLeft (b : Module.Basis (Fin 4) R O) (x : O) :
    LinearMap.trace R O (LinearMap.mulLeft R x) = ∑ m, b.repr (x * b m) m := by
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rfl

/-- The multiplication table (22.3.7) of `EvenClf R a b c u v w` in the basis $1, i, j, k$:
`T a b c u v w p q` is the coordinate vector of $e_pe_q$. -/
def T (a b c u v w : R) : Fin 4 → Fin 4 → Fin 4 → R :=
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
    ![![0, 1, 0, 0], ![-(b * c), u, 0, 0], ![c * w, 0, 0, -c], ![-(u * w), w, b, u]],
    ![![0, 0, 1, 0], ![-(u * v), v, u, c], ![-(a * c), 0, v, 0], ![a * u, -a, 0, 0]],
    ![![0, 0, 0, 1], ![b * v, 0, -b, 0], ![-(v * w), a, w, v], ![-(a * b), 0, 0, w]]]

theorem repr_basisOneIJK {a b c u v w : R} (x : EvenClf R a b c u v w) (m : Fin 4) :
    EvenClf.basisOneIJK.repr x m = (![x.re, x.i, x.j, x.k] : Fin 4 → R) m := by
  rw [EvenClf.basisOneIJK, Module.Basis.ofEquivFun_repr_apply]; rfl

theorem T_eq (a b c u v w : R) (p q m : Fin 4) :
    T a b c u v w p q m = (EvenClf.basisOneIJK.repr
      ((EvenClf.basisOneIJK p : EvenClf R a b c u v w) * EvenClf.basisOneIJK q)) m := by
  rw [repr_basisOneIJK, EvenClf.basisOneIJK_apply', EvenClf.basisOneIJK_apply']
  fin_cases p <;> fin_cases q <;> fin_cases m <;> simp [T, Pi.single_apply] <;> ring

/-- The coordinates of a product in `EvenClf`: $(xy)_m = \sum_{p,q} x_p y_q T_{pq}^m$. -/
theorem repr_mul_evenClf {a b c u v w : R} (x y : EvenClf R a b c u v w) (m : Fin 4) :
    EvenClf.basisOneIJK.repr (x * y) m = ∑ p, ∑ q, EvenClf.basisOneIJK.repr x p *
      EvenClf.basisOneIJK.repr y q * T a b c u v w p q m := by
  simp only [repr_basisOneIJK, Fin.sum_univ_four]
  fin_cases m <;> simp [T] <;> ring

section Table

variable (t : O →ₗ[R] R) (nr : O → R) (hq : ∀ x : O, x * x = t x • x - algebraMap R O (nr x))
  (htr : ∀ x : O, LinearMap.trace R O (LinearMap.mulLeft R x) = 2 * t x)
  (b : Module.Basis (Fin 4) R O) (hb0 : b 0 = 1)
include hq htr hb0

/-- **The table of a normalized basis** (Voight, proof of Proposition 22.4.4): if
$X_{23}^2 = X_{31}^3 = X_{12}^1 = 0$, then the structure coordinates are those of (22.3.7) with
$a = -X_{23}^1$, $b = -X_{31}^2$, $c = -X_{12}^3$ and $u, v, w$ the reduced traces of $i, j, k$. -/
theorem X_eq_T (h1 : X b 2 3 2 = 0) (h2 : X b 3 1 3 = 0) (h3 : X b 1 2 1 = 0) (p q m : Fin 4) :
    X b p q m = T (-X b 2 3 1) (-X b 3 1 2) (-X b 1 2 3) (t (b 1)) (t (b 2)) (t (b 3)) p q m := by
  have Z1 := X_zero_left b hb0
  have Z2 := X_zero_right b hb0
  have S := X_self t nr hq b hb0
  have P := X_add_X t nr hq b hb0
  have tr : ∀ p : Fin 4, X b p 0 0 + X b p 1 1 + X b p 2 2 + X b p 3 3 = 2 * t (b p) := fun p => by
    rw [← htr, trace_mulLeft b, Fin.sum_univ_four]; rfl
  -- squares
  have s11 := S 1 1 (by decide); have s12 := S 1 2 (by decide); have s13 := S 1 3 (by decide)
  have s21 := S 2 1 (by decide); have s22 := S 2 2 (by decide); have s23 := S 2 3 (by decide)
  have s31 := S 3 1 (by decide); have s32 := S 3 2 (by decide); have s33 := S 3 3 (by decide)
  simp only [Fin.reduceEq, if_true, if_false, Fin.isValue] at s11 s12 s13 s21 s22 s23 s31 s32 s33
  -- polarization
  have p131 := P 1 3 1 (by decide); have p132 := P 1 3 2 (by decide); have p133 := P 1 3 3 (by decide)
  have p211 := P 2 1 1 (by decide); have p212 := P 2 1 2 (by decide); have p213 := P 2 1 3 (by decide)
  have p321 := P 3 2 1 (by decide); have p322 := P 3 2 2 (by decide); have p323 := P 3 2 3 (by decide)
  simp only [Fin.reduceEq, if_true, if_false, Fin.isValue, add_zero, zero_add] at p131 p132 p133 p211 p212 p213 p321 p322 p323
  have z1 := Z2 1 0; have z2 := Z2 2 0; have z3 := Z2 3 0
  simp only [Fin.reduceEq, if_false, Fin.isValue] at z1 z2 z3
  have t1 := tr 1; have t2 := tr 2; have t3 := tr 3
  -- the coefficients γ, α, β vanish
  have x133 : X b 1 3 3 = t (b 1) := by linear_combination p133 - h2
  have x122 : X b 1 2 2 = 0 := by linear_combination t1 - z1 - s11 - x133
  have x211 : X b 2 1 1 = t (b 2) := by linear_combination p211 - h3
  have x233 : X b 2 3 3 = 0 := by linear_combination t2 - z2 - x211 - s22
  have x322 : X b 3 2 2 = t (b 3) := by linear_combination p322 - h1
  have x311 : X b 3 1 1 = 0 := by linear_combination t3 - z3 - x322 - s33
  have x131 : X b 1 3 1 = t (b 3) := by linear_combination p131 - x311
  have x132 : X b 1 3 2 = -X b 3 1 2 := by linear_combination p132
  have x212 : X b 2 1 2 = t (b 1) := by linear_combination p212 - x122
  have x213 : X b 2 1 3 = -X b 1 2 3 := by linear_combination p213
  have x321 : X b 3 2 1 = -X b 2 3 1 := by linear_combination p321
  have x323 : X b 3 2 3 = t (b 2) := by linear_combination p323 - x233
  -- associativity determines the constant coordinates
  have A := fun p q r m => assoc b p q r m
  have a2332 := A 2 3 3 2; have a2333 := A 2 3 3 3
  have a3113 := A 3 1 1 3; have a3111 := A 3 1 1 1
  have a1221 := A 1 2 2 1; have a1222 := A 1 2 2 2
  have a1311 := A 1 3 1 1; have a2122 := A 2 1 2 2; have a3233 := A 3 2 3 3
  simp only [Fin.sum_univ_four, Z1, Z2, Fin.reduceEq, if_true, if_false, Fin.isValue, mul_one, mul_zero,
    one_mul, zero_mul, add_zero, zero_add] at a2332 a2333 a3113 a3111 a1221 a1222 a1311 a2122 a3233
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a2332
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a2333
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a3113
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a3111
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a1221
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a1222
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a1311
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a2122
  simp only [s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233, x322, x311, x131, x132, x212, x213, x321, x323, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at a3233
  have x330 : X b 3 3 0 = -(-X b 2 3 1 * -X b 3 1 2) := by linear_combination -a2332
  have x230 : X b 2 3 0 = -X b 2 3 1 * t (b 1) := by linear_combination a2333
  have x110 : X b 1 1 0 = -(-X b 3 1 2 * -X b 1 2 3) := by linear_combination -a3113
  have x310 : X b 3 1 0 = -X b 3 1 2 * t (b 2) := by linear_combination a3111
  have x220 : X b 2 2 0 = -(-X b 2 3 1 * -X b 1 2 3) := by linear_combination -a1221
  have x120 : X b 1 2 0 = -X b 1 2 3 * t (b 3) := by linear_combination a1222
  have x130 : X b 1 3 0 = -(t (b 1) * t (b 3)) := by linear_combination a1311 + x310
  have x210 : X b 2 1 0 = -(t (b 1) * t (b 2)) := by linear_combination a2122 + x120
  have x320 : X b 3 2 0 = -(t (b 2) * t (b 3)) := by linear_combination a3233 + x230
  fin_cases p <;> fin_cases q <;> fin_cases m <;>
    simp [T, Z1, Z2, s11, s12, s13, s21, s22, s23, s31, s32, s33, h1, h2, h3, x133, x122, x211, x233,
      x322, x311, x131, x132, x212, x213, x321, x323, x330, x230, x110, x310, x220, x120, x130, x210, x320]

end Table


/-! ## Normalizing the basis by translations -/

section Normalize

variable (b : Module.Basis (Fin 4) R O) (hb0 : b 0 = 1)

/-- The translation amounts $\eta$: $\eta(i) = X_{31}^3$, $\eta(j) = X_{12}^1$, $\eta(k) = X_{23}^2$. -/
noncomputable def eta : Fin 4 → R := ![0, X b 3 1 3, X b 1 2 1, X b 2 3 2]

/-- The linear form $x \mapsto \sum_p \eta_p x_p$. -/
noncomputable def etaForm : O →ₗ[R] R := ∑ p, eta b p • b.coord p

include hb0

theorem etaForm_one : etaForm b (1 : O) = 0 := by
  simp [etaForm, Fin.sum_univ_four, ← hb0, eta, Finsupp.single_apply]

theorem etaForm_basis (p : Fin 4) : etaForm b (b p) = eta b p := by
  simp [etaForm, Finsupp.single_apply]

/-- The translation $x \mapsto x - \eta(x)$, an $R$-linear automorphism of $O$ fixing $1$. -/
noncomputable def shift : O ≃ₗ[R] O :=
  LinearEquiv.ofLinear (LinearMap.id - (etaForm b).smulRight (1 : O))
    (LinearMap.id + (etaForm b).smulRight (1 : O))
    (by ext x; simp [map_sub, map_smul, etaForm_one b hb0])
    (by ext x; simp [map_add, map_smul, etaForm_one b hb0])

theorem shift_apply (x : O) : shift b hb0 x = x - etaForm b x • 1 := rfl

theorem shift_symm_apply (x : O) : (shift b hb0).symm x = x + etaForm b x • 1 := rfl

/-- **Normalized basis** (Voight, proof of Proposition 22.4.4): the translated basis
$1, i - \eta(i), j - \eta(j), k - \eta(k)$ satisfies $X_{23}^2 = X_{31}^3 = X_{12}^1 = 0$. -/
theorem exists_normalized : ∃ b' : Module.Basis (Fin 4) R O, b' 0 = 1 ∧
    X b' 2 3 2 = 0 ∧ X b' 3 1 3 = 0 ∧ X b' 1 2 1 = 0 := by
  refine ⟨b.map (shift b hb0), ?_, ?_⟩
  · rw [Module.Basis.map_apply, shift_apply, hb0, etaForm_one b hb0, zero_smul, sub_zero]
  have key : ∀ p q m : Fin 4, m ≠ 0 → X (b.map (shift b hb0)) p q m =
      X b p q m - (if p = m then eta b q else 0) - (if q = m then eta b p else 0) := by
    intro p q m hm
    simp only [X, Module.Basis.map_repr, Module.Basis.map_apply, LinearEquiv.trans_apply,
      shift_symm_apply, shift_apply, etaForm_basis b hb0]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
      map_add, map_sub, map_smul, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      b.repr_self, repr_one b hb0, if_neg hm, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key 2 3 2 (by decide)]; simp [eta]
  · rw [key 3 1 3 (by decide)]; simp [eta]
  · rw [key 1 2 1 (by decide)]; simp [eta]

end Normalize

/-! ## The isomorphism -/

theorem basisOneIJK_zero {a b c u v w : R} : (EvenClf.basisOneIJK 0 : EvenClf R a b c u v w) = 1 := by
  rw [EvenClf.basisOneIJK_apply']; ext <;> rfl

/-- **Good bases (Voight 2021, Proposition 22.4.4 and 22.4.7)**: an $R$-algebra $O$ with an $R$-basis $1, i, j, k$,
a standard involution ($x^2 = \operatorname{trd}(x)x - \operatorname{nrd}(x)$ with $\operatorname{trd}$ $R$-linear) and
$\operatorname{Tr}(L_x) = 2\operatorname{trd}(x)$ is isomorphic to an even Clifford algebra `EvenClf R a b c u v w`
(the algebra with table (22.3.7)): after translating $i, j, k$ by elements of $R$, the basis is good. Over every
commutative ring $R$. -/
@[kb "voight2021" "Proposition 22.4.4, p. 364; 22.4.7, p. 365"]
theorem exists_algEquiv_evenClf (t : O →ₗ[R] R) (nr : O → R)
    (hq : ∀ x : O, x * x = t x • x - algebraMap R O (nr x))
    (htr : ∀ x : O, LinearMap.trace R O (LinearMap.mulLeft R x) = 2 * t x)
    (b : Module.Basis (Fin 4) R O) (hb0 : b 0 = 1) :
    ∃ a b c u v w : R, Nonempty (O ≃ₐ[R] EvenClf R a b c u v w) := by
  obtain ⟨e, he0, h1, h2, h3⟩ := exists_normalized b hb0
  set A := -X e 2 3 1; set B := -X e 3 1 2; set C := -X e 1 2 3
  set U := t (e 1); set V := t (e 2); set W := t (e 3)
  have hX := X_eq_T t nr hq htr e he0 h1 h2 h3
  let l : O ≃ₗ[R] EvenClf R A B C U V W := e.equivFun.trans EvenClf.basisOneIJK.equivFun.symm
  have hl : ∀ x m, EvenClf.basisOneIJK.repr (l x) m = e.repr x m := fun x m => by
    simp [l, Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self]
  refine ⟨A, B, C, U, V, W, ⟨AlgEquiv.ofLinearEquiv l ?_ ?_⟩⟩
  · apply EvenClf.basisOneIJK.repr.injective
    ext m
    rw [hl, ← he0, e.repr_self, ← basisOneIJK_zero, EvenClf.basisOneIJK.repr_self]
  · intro x y
    apply EvenClf.basisOneIJK.repr.injective
    ext m
    rw [hl, repr_mul e, repr_mul_evenClf]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hl, hl, hX]

end GoodBasis

end QuadFormsKB.Voight
