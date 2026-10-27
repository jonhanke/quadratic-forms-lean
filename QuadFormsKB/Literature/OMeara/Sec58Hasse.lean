/-
# O'Meara §58: the Hasse algebra (definition, 58:2, rules of 58:3) and 57:11 (first assertion)

**Setting.** $F$ a field with $2$ invertible (O'Meara's Chapter V: characteristic $\ne 2$).  The diagonal form
$\langle a_0\rangle \perp \cdots \perp \langle a_{n-1}\rangle$ is represented by its list of values
`a : List Fˣ` (0-based).  O'Meara's similarity $\sim$ is Mathlib's `IsBrauerEquivalent`; the bundled tensor
product `CSA52.tensor` and the quaternion algebras `CSA52.quaternion` come from Sec52F.  All declarations are in
`QuadFormsKB.OMeara.Hasse58`.

**Definitions**
* `Br F`, `cls`: the set of similarity classes of central simple algebras, a commutative monoid under $\otimes$
  (the Brauer group, written multiplicatively; proofs of the rules of 57:10, 57:11, 58:3 are computations there);
* `qs a b`, `B a b`: the quaternion algebra $(a,b)$ of two units and its class;
* `hasseAlg a`: the **Hasse algebra** $S V = \bigotimes_i (a_i, d_i)$, $d_i = a_0 a_1 \cdots a_i$ (prefix
  products, p. 150), implemented as `Rev.hasseAlg a.reverse` where `Rev.hasseAlg` uses suffix products (the
  working version; all proofs are done there);
* `hasseAlgPairs a`: the algebra $\bigotimes_{i \le j} (a_i, a_j)$ of the first rule of 58:3;
* `Rev.values`: the value list $(Q(X_0),\dots,Q(X_{n-1}))$ of an orthogonal basis of a regular space.

**Proves**
* **57:11, first assertion** `isBrauerEquivalent_quaternion_tensor_quaternion`:
  $(\alpha,\beta)\otimes(\alpha,\gamma) \sim (\alpha,\beta\gamma)$; and the bilinearity of the symbol,
  `B_mul_right`, `B_mul_left`, `B_comm`, `B_mul_self`, `B_self`, `B_sq_mul_left`;
* **58:2** `nonempty_algEquiv_hasseAlg_values`: $S V$ is well defined up to isomorphism (and the similarity
  version `isBrauerEquivalent_hasseAlg_values`);
* **58:3** (lists of values): `isBrauerEquivalent_hasseAlg_hasseAlgPairs` ($S V \sim \bigotimes_{i\le j}(a_i,a_j)$),
  `isBrauerEquivalent_hasseAlg_append` (orthogonal sums), `isBrauerEquivalent_hasseAlg_scale` (scaling),
  `isBrauerEquivalent_hasseAlg_ternary`, `isBrauerEquivalent_hasseAlg_quaternary`.

*Not formalized:* the $E$-ification rule $S(EV) \cong E\,S(V)$ of 58:3 (needs the base change of central simple
algebras and of quaternion algebras).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec52F
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Literature.OMeara.Sec58Bases

open scoped TensorProduct
open Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Hasse58

open CSA52

universe u

variable {F : Type u} [Field F]

/-! ### The Brauer monoid -/

/-- The set of similarity classes of central simple algebras over $F$ (Mathlib's `BrauerGroup`, kept as a
separate definition so that the multiplication, induced by the tensor product, is a local instance). -/
def Br (F : Type u) [Field F] : Type (u + 1) := Quotient (Brauer.CSA_Setoid.{u, u} F)

/-- The similarity class of a central simple algebra. -/
def cls (A : CSA.{u, u} F) : Br F := Quotient.mk (Brauer.CSA_Setoid.{u, u} F) A

theorem cls_eq_iff {A B : CSA.{u, u} F} : cls A = cls B ↔ IsBrauerEquivalent A B :=
  Quotient.eq (r := Brauer.CSA_Setoid.{u, u} F)

instance : CommMonoid (Br F) where
  mul := Quotient.map₂ tensor (fun _ _ h _ _ h' => isBrauerEquivalent_tensor h h')
  one := cls one
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    exact cls_eq_iff.2 (isBrauerEquivalent_tensor_assoc _ _ _)
  one_mul := by
    intro a
    induction a using Quotient.inductionOn
    exact cls_eq_iff.2 ((isBrauerEquivalent_tensor_comm _ _).trans (isBrauerEquivalent_tensor_one _))
  mul_one := by
    intro a
    induction a using Quotient.inductionOn
    exact cls_eq_iff.2 (isBrauerEquivalent_tensor_one _)
  mul_comm := by
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact cls_eq_iff.2 (isBrauerEquivalent_tensor_comm _ _)

theorem cls_tensor (A B : CSA.{u, u} F) : cls (tensor A B) = cls A * cls B := rfl

theorem cls_one : cls (one : CSA.{u, u} F) = 1 := rfl

section Quaternion

variable [Invertible (2 : F)]

/-- $(1,-1)$ splits (O'Meara 57:4), so it is similar to $1$ (`isBrauerEquivalent_one_iff`). -/
theorem isBrauerEquivalent_quaternion_one_neg_one :
    IsBrauerEquivalent (quaternion (1 : F) (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero)) one := by
  rw [isBrauerEquivalent_one_iff]
  obtain ⟨e⟩ := Quaternions57.nonempty_algEquiv_matrix_one_neg_one (F := F)
  exact ⟨2, two_ne_zero, ⟨e⟩⟩

/-- **O'Meara 57:11, first assertion** (§57C, p. 148): for $\alpha, \beta, \gamma \ne 0$,
$(\alpha,\beta) \otimes (\alpha,\gamma) \sim (\alpha,\beta\gamma)$.  The isomorphism of 57:10 (4),
$(\alpha,\beta)\otimes(\alpha,\gamma) \cong (\alpha,\beta\gamma)\otimes(1,-1)$, replaces the isomorphism symbol by
the similarity symbol, and $(1,-1)$ splits (57:4), so $(\alpha,\beta\gamma)\otimes(1,-1) \sim (\alpha,\beta\gamma)$. -/
@[kb "omeara1963" "§57C, 57:11, p. 148 (first assertion)"]
theorem isBrauerEquivalent_quaternion_tensor_quaternion (α β γ : F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) :
    IsBrauerEquivalent (tensor (quaternion α β hα hβ) (quaternion α γ hα hγ))
      (quaternion α (β * γ) hα (mul_ne_zero hβ hγ)) := by
  obtain ⟨e⟩ := QuatIso57.nonempty_algEquiv_tensor (F := F) (α := α) (β := β) (γ := γ) hα hβ hγ
  have e' : tensor (quaternion α β hα hβ) (quaternion α γ hα hγ) ≃ₐ[F]
      tensor (quaternion α (β * γ) hα (mul_ne_zero hβ hγ))
        (quaternion 1 (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero)) := e
  exact (isBrauerEquivalent_of_algEquiv e').trans
    ((isBrauerEquivalent_tensor (IsBrauerEquivalent.refl _)
      isBrauerEquivalent_quaternion_one_neg_one).trans (isBrauerEquivalent_tensor_one _))

/-! ### The symbol $(a,b)$ on units, as a class in the Brauer monoid -/

/-- The quaternion algebra $(a,b)$ for units $a, b \in F^\times$, bundled. -/
def qs (a b : Fˣ) : CSA.{u, u} F := quaternion (a : F) (b : F) a.ne_zero b.ne_zero

/-- The similarity class of $(a,b)$ for units $a,b$. -/
def B (a b : Fˣ) : Br F := cls (qs a b)

theorem cls_quaternion_congr {α β α' β' : F} (hα : α ≠ 0) (hβ : β ≠ 0) (hα' : α' ≠ 0) (hβ' : β' ≠ 0)
    (h1 : α = α') (h2 : β = β') : cls (quaternion α β hα hβ) = cls (quaternion α' β' hα' hβ') := by
  subst h1 h2; rfl

/-- $B(a, bc) = B(a,b) B(a,c)$ (57:11, first assertion). -/
theorem B_mul_right (a b c : Fˣ) : B a (b * c) = B a b * B a c := by
  unfold B qs
  rw [← cls_tensor]
  exact (cls_quaternion_congr _ _ _ _ rfl (Units.val_mul b c)).trans
    (cls_eq_iff.2 (isBrauerEquivalent_quaternion_tensor_quaternion (a : F) b c a.ne_zero b.ne_zero
      c.ne_zero)).symm

/-- $B(a,b) = B(b,a)$ (57:10 (2), swap). -/
theorem B_comm (a b : Fˣ) : B a b = B b a := by
  unfold B qs
  obtain ⟨e⟩ := QuatIso57.algEquiv_swap (F := F) a.ne_zero b.ne_zero
  exact (cls_eq_iff.2 (isBrauerEquivalent_of_algEquiv e)).symm

/-- $B(a,b) B(a,b) = 1$ (57:11, second assertion). -/
theorem B_mul_self (a b : Fˣ) : B a b * B a b = 1 := by
  unfold B qs
  rw [← cls_tensor, ← cls_one]
  exact cls_eq_iff.2 (isBrauerEquivalent_quaternion_tensor_self _ _ _ _)

theorem B_mul_left (a b c : Fˣ) : B (a * b) c = B a c * B b c := by
  rw [B_comm, B_mul_right, B_comm c a, B_comm c b]

theorem B_one_right (a : Fˣ) : B a 1 = 1 := by
  have h := B_mul_right a 1 1
  rw [mul_one] at h
  have h2 := B_mul_self a 1
  calc B a 1 = B a 1 * (B a 1 * B a 1) := by rw [h2, mul_one]
    _ = (B a 1 * B a 1) * B a 1 := by rw [mul_assoc]
    _ = 1 := by rw [← h, h2]

theorem B_one_left (a : Fˣ) : B 1 a = 1 := by rw [B_comm, B_one_right]

/-- $B(a,a) = B(a,-1)$ (57:10 (3): $(\alpha,-\alpha\beta) \cong (\alpha,\beta)$ for $\beta = -1$). -/
theorem B_self (a : Fˣ) : B a a = B a (-1) := by
  unfold B qs
  obtain ⟨e⟩ := QuatIso57.algEquiv_neg_mul (F := F) (α := a) (β := -1) a.ne_zero (neg_ne_zero.2 one_ne_zero)
  have h := cls_eq_iff.2 (isBrauerEquivalent_of_algEquiv
    (A := quaternion (a : F) (-((a : F) * -1)) a.ne_zero
      (neg_ne_zero.2 (mul_ne_zero a.ne_zero (neg_ne_zero.2 one_ne_zero))))
    (B := quaternion (a : F) (-1) a.ne_zero (neg_ne_zero.2 one_ne_zero)) e)
  refine Eq.trans ?_ h
  exact cls_quaternion_congr _ _ _ _ rfl (by simp)

theorem B_sq_mul (a b : Fˣ) (w : Br F) : B a b * (B a b * w) = w := by
  rw [← mul_assoc, B_mul_self, one_mul]

/-- $B(m^2 a, b) = B(a,b)$: the symbol only depends on square classes. -/
theorem B_sq_mul_left (m a b : Fˣ) : B (m ^ 2 * a) b = B a b := by
  rw [B_mul_left, sq, B_mul_left, B_mul_self, one_mul]

theorem B_sq_mul_right (a m b : Fˣ) : B a (m ^ 2 * b) = B a b := by
  rw [B_comm, B_sq_mul_left, B_comm]

theorem B_pow_right (a b : Fˣ) (k : ℕ) : B a (b ^ k) = B a b ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, B_one_right]
  | succ k ih => rw [pow_succ, B_mul_right, ih, pow_succ]

/-! ### The Hasse algebra with suffix products (auxiliary)

The sub-namespace `Rev` holds the construction with the *suffix* products $d_k = r_k r_{k+1} \cdots r_{m-1}$ of
a list $r$ (factors $(r_k, r_k \cdots r_{m-1})$).  O'Meara's Hasse algebra has *prefix* products
$d_i = a_0 \cdots a_i$; it is `Rev.hasseAlg` of the reversed list (below, after `end Rev`).  The statements in
`Rev` are the working versions; the book's statements are derived from them in the section after `end Rev`.
Declarations in `Rev` carry no knowledge-base tag. -/

namespace Rev

/-- Auxiliary: the tensor product $\bigotimes_k (r_k, r_k r_{k+1} \cdots r_{m-1})$ (suffix products) of a list
$r = (r_0,\dots,r_{m-1})$, by `hasseAlg [] = one`, `hasseAlg (x :: l) = tensor (qs x (x * l.prod)) (hasseAlg l)`.
O'Meara's Hasse algebra is this construction applied to the reversed list. -/
def hasseAlg : List Fˣ → CSA.{u, u} F
  | [] => one
  | x :: l => tensor (qs x (x :: l).prod) (hasseAlg l)

/-- The row $\bigotimes_{y \in l} (x, y)$. -/
def rowAlg (x : Fˣ) : List Fˣ → CSA.{u, u} F
  | [] => one
  | y :: l => tensor (qs x y) (rowAlg x l)

/-- **The product $\bigotimes_{i \le j} (a_i, a_j)$ over all pairs of positions** (the right-hand side of the
first rule of 58:3, p. 151; positions $0 \le i \le j < n$, 0-based): `hasseAlgPairs (x :: l)` is the row
$\bigotimes_{y \in x :: l} (x, y)$ tensored with `hasseAlgPairs l`. -/
def hasseAlgPairs : List Fˣ → CSA.{u, u} F
  | [] => one
  | x :: l => tensor (rowAlg x (x :: l)) (hasseAlgPairs l)

theorem cls_hasseAlg_nil : cls (hasseAlg ([] : List Fˣ)) = (1 : Br F) := rfl

theorem cls_hasseAlg_cons (x : Fˣ) (l : List Fˣ) :
    cls (hasseAlg (x :: l)) = B x (x * l.prod) * cls (hasseAlg l) := by
  show cls (tensor (qs x (x :: l).prod) (hasseAlg l)) = _
  rw [cls_tensor, List.prod_cons]
  rfl

theorem cls_rowAlg (x : Fˣ) (l : List Fˣ) : cls (rowAlg x l) = B x l.prod := by
  induction l with
  | nil => rw [List.prod_nil, B_one_right]; rfl
  | cons y l ih =>
    show cls (tensor (qs x y) (rowAlg x l)) = _
    rw [cls_tensor, ih, List.prod_cons, B_mul_right]
    rfl

theorem cls_hasseAlgPairs (l : List Fˣ) : cls (hasseAlgPairs l) = cls (hasseAlg l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show cls (tensor (rowAlg x (x :: l)) (hasseAlgPairs l)) = _
    rw [cls_tensor, cls_rowAlg, ih, cls_hasseAlg_cons, List.prod_cons]

/-- **O'Meara 58:3, first rule** (p. 151): the Hasse algebra is similar to $\bigotimes_{i \le j} (a_i, a_j)$,
the product over all pairs of positions.  (Both are computed in the Brauer monoid: the row $(x, x) \otimes
\bigotimes_{y \in l}(x,y)$ is $(x, x \cdot \prod l)$ by 57:11.) -/
theorem isBrauerEquivalent_hasseAlg_hasseAlgPairs (l : List Fˣ) :
    IsBrauerEquivalent (hasseAlg l) (hasseAlgPairs l) :=
  cls_eq_iff.1 (cls_hasseAlgPairs l).symm

/-! ### 58:3: rules for operating with the Hasse algebra -/

theorem cls_hasseAlg_append (a a' : List Fˣ) :
    cls (hasseAlg (a ++ a')) = cls (hasseAlg a) * B a.prod a'.prod * cls (hasseAlg a') := by
  induction a with
  | nil => rw [List.nil_append, List.prod_nil, B_one_left, cls_hasseAlg_nil, one_mul, one_mul]
  | cons x l ih =>
    rw [List.cons_append, cls_hasseAlg_cons, ih, cls_hasseAlg_cons, List.prod_append, List.prod_cons,
      ← mul_assoc x, B_mul_right x (x * l.prod), B_mul_left]
    ac_rfl

/-- **O'Meara 58:3, orthogonal sums** (p. 151): for a splitting $V = U \perp W$ into orthogonal diagonalizable
parts, with $U$ having orthogonal base values `a` and $W$ having `a'` (so that $V$ has the concatenated list),
$S V \sim S U \otimes (dU, dW) \otimes S W$, where $dU = \prod a$ and $dW = \prod a'$ are the discriminants
(determinants of the Gram matrices $\mathrm{diag}(a)$, `Sp58.det_gram_of_isOrthAniso`). -/
theorem isBrauerEquivalent_hasseAlg_append (a a' : List Fˣ) :
    IsBrauerEquivalent (hasseAlg (a ++ a'))
      (tensor (tensor (hasseAlg a) (qs a.prod a'.prod)) (hasseAlg a')) :=
  cls_eq_iff.1 (by rw [cls_tensor, cls_tensor, cls_hasseAlg_append]; rfl)

theorem prod_map_mul_left (α : Fˣ) (l : List Fˣ) : (l.map (α * ·)).prod = α ^ l.length * l.prod := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.prod_cons, ih, List.prod_cons, List.length_cons, pow_succ]; ac_rfl

theorem tri_succ (k : ℕ) : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

theorem cls_hasseAlg_scale (α : Fˣ) (l : List Fˣ) :
    cls (hasseAlg (l.map (α * ·))) =
      B α ((-1) ^ (l.length * (l.length + 1) / 2) * l.prod ^ (l.length + 1)) * cls (hasseAlg l) := by
  induction l with
  | nil => simp [cls_hasseAlg_nil, B_one_right]
  | cons x t ih =>
    rw [List.map_cons, cls_hasseAlg_cons, List.prod_cons, prod_map_mul_left, ih, cls_hasseAlg_cons,
      List.length_cons, tri_succ]
    have e : α * x * (α ^ t.length * t.prod) = α ^ (t.length + 1) * (x * t.prod) := by
      rw [pow_succ]; ac_rfl
    rw [e]
    simp only [B_mul_left, B_mul_right, B_pow_right, mul_pow, B_self, B_comm x α, pow_succ, pow_add]
    ac_rfl

/-- **O'Meara 58:3, scaling** (p. 151-152), reconstruction of the garbled formula.  If $V$ has an orthogonal
base of values `l` $= (a_0,\dots,a_{n-1})$ then $V^\alpha$ (the form $\alpha Q$) has the orthogonal base of values
$\alpha a_i$ (`l.map (α * ·)`), and
$$S(V^\alpha) \sim \bigl(\alpha,\ (-1)^{n(n+1)/2}\, (dV)^{n+1}\bigr) \otimes S V,\qquad dV = \prod a_i.$$
*Reconstruction note.*  The printed formula is illegible in the machine-read text (it contains
"$(-1)^{\ldots}$" and a power $n+1$ outside); this formula was derived by computation from the definition
and 57:10, 57:11: $S(V^\alpha)$ and $S V$ differ by the factor
$(\alpha,\alpha)^{n(n+1)/2}\,(\alpha,dV)^{n+1}$ (each of the $n(n+1)/2$ pairs $i \le j$ contributes $(\alpha,\alpha)$,
and each $a_k$ occurs in $n+1$ pairs), and $(\alpha,\alpha) \cong (\alpha,-1)$ (57:10 (3)), $(\alpha,b)\otimes(\alpha,c) \sim
(\alpha,bc)$ (57:11).  Since $(\alpha,b)\otimes(\alpha,b) \sim 1$ the exponent $n+1$ may be reduced modulo $2$. -/
theorem isBrauerEquivalent_hasseAlg_scale (α : Fˣ) (l : List Fˣ) :
    IsBrauerEquivalent (hasseAlg (l.map (α * ·)))
      (tensor (qs α ((-1) ^ (l.length * (l.length + 1) / 2) * l.prod ^ (l.length + 1))) (hasseAlg l)) :=
  cls_eq_iff.1 (by rw [cls_tensor, cls_hasseAlg_scale]; rfl)

theorem cls_hasseAlg_ternary (a b c : Fˣ) :
    B (-1) (-1) * cls (hasseAlg [a, b, c]) = B (-(a * b)) (-(b * c)) := by
  rw [neg_eq_neg_one_mul (a * b), neg_eq_neg_one_mul (b * c)]
  simp only [cls_hasseAlg_cons, cls_hasseAlg_nil, List.prod_cons, List.prod_nil, mul_one, B_mul_left,
    B_mul_right]
  rw [B_self a, B_self b, B_self c, B_comm (-1) b, B_comm (-1) c]
  simp only [mul_comm, mul_left_comm, B_mul_self, mul_one]

/-- **O'Meara 58:3, ternary spaces** (p. 152), reconstruction of the garbled formula.  For a ternary space with
an orthogonal base of values $a_0, a_1, a_2$ (0-based; the book's $a_1,a_2,a_3$):
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_1a_2).$$
*Reconstruction note.*  The machine-read text shows "$(-1,-1) \otimes S V \sim (-a_?, -a_?\, a_?)$" with
illegible arguments; the formula was derived (and is true) as stated here, by expanding both sides with
bimultiplicativity of the symbol, $(a,a) \cong (a,-1)$ and $(a,b)\otimes(a,b)\sim 1$.  No hypothesis on the
discriminant is needed. -/
theorem isBrauerEquivalent_hasseAlg_ternary (a b c : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c])) (qs (-(a * b)) (-(b * c))) :=
  cls_eq_iff.1 (by rw [cls_tensor]; exact cls_hasseAlg_ternary a b c)

theorem cls_hasseAlg_quaternary (a b c d : Fˣ) :
    B (-1) (-1) * cls (hasseAlg [a, b, c, d]) =
      B (-(a * b)) (-(b * c)) * B d (a * b * c * d) := by
  rw [neg_eq_neg_one_mul (a * b), neg_eq_neg_one_mul (b * c)]
  simp only [cls_hasseAlg_cons, cls_hasseAlg_nil, List.prod_cons, List.prod_nil, mul_one, B_mul_left,
    B_mul_right]
  rw [B_self a, B_self b, B_self c, B_self d, B_comm (-1) b, B_comm (-1) c, B_comm d a, B_comm d b,
    B_comm d c]
  simp only [mul_comm, mul_left_comm, B_mul_self, mul_one]

/-- **O'Meara 58:3, quaternary spaces** (p. 152), reconstruction of the garbled formula.  For a quaternary space
with an orthogonal base of values $a_0,a_1,a_2,a_3$ (0-based) and discriminant $dV = a_0a_1a_2a_3$:
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_1a_2) \otimes (a_3,\ dV).$$
*Reconstruction note.*  The machine-read text shows the ternary right-hand side times a factor "$(a_?, dV)$";
the index of the first entry is illegible.  Computing, the missing factor is $(a_3, dV)$ with $a_3$ the *last*
value: the ternary formula for the first three values leaves $(a_3,-a_0a_1a_2)$ (from the pairs involving $a_3$),
and $(a_3,-a_0a_1a_2) = (a_3,-1)\otimes(a_3,a_0a_1a_2) \sim (a_3,a_3)\otimes(a_3,a_0a_1a_2) \sim
(a_3, a_0a_1a_2a_3)$ by 57:10 (3) and 57:11. -/
theorem isBrauerEquivalent_hasseAlg_quaternary (a b c d : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c, d]))
      (tensor (qs (-(a * b)) (-(b * c))) (qs d (a * b * c * d))) :=
  cls_eq_iff.1 (by rw [cls_tensor, cls_tensor]; exact cls_hasseAlg_quaternary a b c d)

/-! ### Similar algebras of the same dimension are isomorphic -/

/-- **Similar central simple algebras of the same dimension are isomorphic** (consequence of 52:9 and the
definition of similarity, §52F, p. 127-128): if $A \sim A'$ then $A \cong M_n(D)$ and $A' \cong M_m(D)$ for the same
division algebra $D$ (`isBrauerEquivalent_iff_nonempty_algEquiv`), and $\dim A = n^2 \dim D$,
$\dim A' = m^2 \dim D$, so equal dimensions force $n = m$. -/
theorem nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq {A A' : CSA.{u, u} F}
    (h : IsBrauerEquivalent A A') (hd : Module.finrank F A = Module.finrank F A') :
    Nonempty (A ≃ₐ[F] A') := by
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  have : IsArtinianRing A' := IsArtinianRing.of_finite F A'
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
  obtain ⟨m, hm, D', _, _, _, ⟨e'⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A'
  obtain ⟨ε⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv (A := A) (A' := A') e e').1 h
  have h1 : Module.finrank F A = n * n * Module.finrank F D := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]; simp
  have h2 : Module.finrank F A' = m * m * Module.finrank F D' := by
    rw [e'.toLinearEquiv.finrank_eq, Module.finrank_matrix]; simp
  have h3 : Module.finrank F D = Module.finrank F D' := ε.toLinearEquiv.finrank_eq
  have hD : 0 < Module.finrank F D := Module.finrank_pos
  have h4 : n * n = m * m := by
    rw [h1, h2, h3] at hd
    exact Nat.eq_of_mul_eq_mul_right (h3 ▸ hD) hd
  have h5 : n = m := Nat.mul_self_inj.1 h4
  subst h5
  exact ⟨e.trans (ε.mapMatrix.trans e'.symm)⟩

theorem finrank_hasseAlg (l : List Fˣ) : Module.finrank F (hasseAlg l) = 4 ^ l.length := by
  induction l with
  | nil => exact Module.finrank_self F
  | cons x t ih =>
    show Module.finrank F (qs x (x :: t).prod ⊗[F] hasseAlg t) = _
    rw [Module.finrank_tensorProduct, ih, List.length_cons, pow_succ, mul_comm]
    congr 1
    exact QuaternionAlgebra.finrank_eq_four _ _ _

/-! ### 58:2: invariance under altering two adjacent values -/

theorem block_eq (p q D : Fˣ) :
    B p (p * (q * D)) * B q (q * D) = B p q * B (p * q) (-1 * D) := by
  simp only [B_mul_right, B_mul_left, B_self]
  ac_rfl

/-- Altering the first two values $p, q$ of a list to $p', q'$ with $p'q' \in (pq) F^{\times 2}$ and
$(p',q') \cong (p,q)$ does not change the class of the Hasse algebra. -/
theorem cls_hasseAlg_block (p q p' q' m : Fˣ) (r : List Fˣ) (hpq : p' * q' = m ^ 2 * (p * q))
    (hB : B p' q' = B p q) :
    cls (hasseAlg (p :: q :: r)) = cls (hasseAlg (p' :: q' :: r)) := by
  simp only [cls_hasseAlg_cons, List.prod_cons]
  rw [← mul_assoc (B p (p * (q * r.prod))), ← mul_assoc (B p' (p' * (q' * r.prod))), block_eq, block_eq,
    hpq, hB, B_sq_mul_left]

theorem cls_hasseAlg_adj : ∀ (i : ℕ) (l l' : List Fˣ) (m : Fˣ), l.length = l'.length →
    (∀ j, j ≠ i → j ≠ i + 1 → l[j]? = l'[j]?) → l'.prod = m ^ 2 * l.prod →
    (∀ p q p' q' : Fˣ, l[i]? = some p → l[i + 1]? = some q → l'[i]? = some p' → l'[i + 1]? = some q' →
      B p q = B p' q') →
    cls (hasseAlg l) = cls (hasseAlg l') := by
  intro i
  induction i with
  | zero =>
    intro l l' m hlen hagree hprod hB
    rcases l with _ | ⟨p, _ | ⟨q, r⟩⟩
    · have : l' = [] := List.eq_nil_of_length_eq_zero hlen.symm
      rw [this]
    · rcases l' with _ | ⟨p', _ | ⟨q', r'⟩⟩
      · simp at hlen
      · simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
        rw [cls_hasseAlg_cons, cls_hasseAlg_cons, hprod]
        simp only [List.prod_nil, mul_one, B_self, B_sq_mul_left]
      · simp at hlen
    · rcases l' with _ | ⟨p', _ | ⟨q', r'⟩⟩
      · simp at hlen
      · simp at hlen
      · have hr : r = r' := by
          refine List.ext_getElem? fun k => ?_
          have := hagree (k + 2) (by omega) (by omega)
          simpa using this
        subst hr
        simp only [List.prod_cons] at hprod
        have hpq : p' * q' = m ^ 2 * (p * q) := by
          have : p' * q' * r.prod = m ^ 2 * (p * q) * r.prod := by
            simpa only [mul_assoc] using hprod
          exact mul_right_cancel this
        exact cls_hasseAlg_block p q p' q' m r hpq
          (hB p q p' q' (by simp) (by simp) (by simp) (by simp)).symm
  | succ i ih =>
    intro l l' m hlen hagree hprod hB
    rcases l with _ | ⟨x, t⟩
    · have : l' = [] := List.eq_nil_of_length_eq_zero hlen.symm
      rw [this]
    · rcases l' with _ | ⟨y, t'⟩
      · simp at hlen
      · have hxy : x = y := by
          have := hagree 0 (by omega) (by omega)
          simpa using this
        subst hxy
        simp only [List.prod_cons] at hprod
        have hprod' : t'.prod = m ^ 2 * t.prod := by
          refine mul_left_cancel (a := x) ?_
          rw [hprod]; ac_rfl
        rw [cls_hasseAlg_cons, cls_hasseAlg_cons,
          ih t t' m (by simpa using hlen)
            (fun j hj1 hj2 => by simpa using hagree (j + 1) (by omega) (by omega)) hprod'
            (fun p q p' q' h1 h2 h3 h4 =>
              hB p q p' q' (by simpa using h1) (by simpa using h2) (by simpa using h3)
                (by simpa using h4))]
        rw [show B x (x * t'.prod) = B x (x * t.prod) by rw [hprod, B_sq_mul_right]]

/-! ### 58:2: the algebra $(a_i, a_{i+1})$ for two orthogonal bases of a plane -/

/-- If $x, y$ are orthogonal anisotropic vectors and $v = c_1 x + c_2 y$, $w = d_1 x + d_2 y$ are orthogonal
anisotropic vectors of the plane $Fx + Fy$ then $(Q(v), Q(w)) \cong (Q(x), Q(y))$.  This is the statement that both
are the Clifford algebra of the plane (57:5), proved directly by 57:7: the elements $c_1 i + c_2 j$ and
$d_1 i + d_2 j$ of $(Q(x),Q(y))$ square to $Q(v)$, $Q(w)$ and anticommute. -/
theorem nonempty_algEquiv_plane {α β α' β' c₁ c₂ d₁ d₂ : F} (hα' : α' ≠ 0) (hβ' : β' ≠ 0)
    (h1 : α' = c₁ ^ 2 * α + c₂ ^ 2 * β) (h2 : β' = d₁ ^ 2 * α + d₂ ^ 2 * β)
    (h3 : c₁ * d₁ * α + c₂ * d₂ * β = 0) :
    Nonempty (ℍ[F,α',β'] ≃ₐ[F] ℍ[F,α,β]) := by
  refine QuatIso57.nonempty_algEquiv_of_sq hα' hβ' (⟨0, c₁, c₂, 0⟩ : ℍ[F,α,β]) (⟨0, d₁, d₂, 0⟩ : ℍ[F,α,β])
    ?_ ?_ ?_
  · ext <;> simp [h1] <;> ring
  · ext <;> simp [h2] <;> ring
  · ext <;> simp <;> first | linear_combination 2 * h3 | ring

section Geometry

open Module Sp58

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- In a regular space with an orthogonal anisotropic basis family $x$ of length $\dim V$: a vector $v$ that
is orthogonal to all $x_j$ with $j \notin \{u, w\}$ lies in the plane $F x_u + F x_w$, with the expected
coordinates. -/
theorem expand_plane (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} {x : Fin n → V}
    (hx : IsOrthAniso Q x) (hn : n = finrank F V) {u w : Fin n} (huw : u ≠ w) {v : V}
    (hv : ∀ j, j ≠ u → j ≠ w → bil Q v (x j) = 0) :
    v = (bil Q v (x u) / Q (x u)) • x u + (bil Q v (x w) / Q (x w)) • x w := by
  have hu0 := hx.aniso u
  have hw0 := hx.aniso w
  have h : v - (bil Q v (x u) / Q (x u)) • x u - (bil Q v (x w) / Q (x w)) • x w = 0 := by
    refine eq_zero_of_orth hQ hx hn fun j => ?_
    simp only [bil_sub_left, bil_smul_left]
    by_cases hj1 : j = u
    · rw [hj1, hx.orth w u huw.symm, bil_self]
      field_simp
      ring
    · by_cases hj2 : j = w
      · rw [hj2, hx.orth u w huw, bil_self]
        field_simp
        ring
      · rw [hv j hj1 hj2, hx.orth u j (Ne.symm hj1), hx.orth w j (Ne.symm hj2)]
        ring
  rw [sub_sub, sub_eq_zero] at h
  exact h

/-- **The plane step of 58:2.**  Let $X, X'$ be orthogonal bases of a regular space $V$ ($\dim V = n$) with
$X'_j = X_j$ for $j \ne i, i+1$ ($i + 1 < n$).  Then $(Q(X'_i), Q(X'_{i+1})) \cong (Q(X_i), Q(X_{i+1}))$: both
$X_i, X_{i+1}$ and $X'_i, X'_{i+1}$ are orthogonal bases of the same plane (the orthogonal complement of the common
vectors), and the algebra is the Clifford algebra of that plane (`nonempty_algEquiv_plane`). -/
theorem nonempty_algEquiv_step (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X X' : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hX' : IsOrthogonalBasis Q X') (i : ℕ)
    (hi : i + 1 < n) (hadj : ∀ j : Fin n, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → X' j = X j) :
    Nonempty (ℍ[F,Q (X' ⟨i, by omega⟩),Q (X' ⟨i + 1, hi⟩)] ≃ₐ[F] ℍ[F,Q (X ⟨i, by omega⟩),Q (X ⟨i + 1, hi⟩)]) := by
  have hn : n = finrank F V := by rw [finrank_eq_card_basis X, Fintype.card_fin]
  have hXa := isOrthAniso_basis hQ X hX
  have hXa' := isOrthAniso_basis hQ X' hX'
  set u : Fin n := ⟨i, by omega⟩ with hu
  set w : Fin n := ⟨i + 1, hi⟩ with hw
  have huw : u ≠ w := by simp [hu, hw, Fin.ext_iff]
  have hpl : ∀ z : Fin n, (z = u ∨ z = w) → ∀ j, j ≠ u → j ≠ w → bil Q (X' z) (X j) = 0 := by
    intro z hz j hj1 hj2
    have hjz : j ≠ z := by rcases hz with rfl | rfl <;> assumption
    have : X j = X' j := (hadj j (fun h => hj1 (Fin.ext h)) (fun h => hj2 (Fin.ext h))).symm
    rw [this]
    exact hX' z j (Ne.symm hjz)
  have ev := expand_plane hQ hXa hn huw (hpl u (Or.inl rfl))
  have ew := expand_plane hQ hXa hn huw (hpl w (Or.inr rfl))
  have hxy : bil Q (X u) (X w) = 0 := hX u w huw
  have hxy' : bil Q (X w) (X u) = 0 := hX w u huw.symm
  set c₁ := bil Q (X' u) (X u) / Q (X u)
  set c₂ := bil Q (X' u) (X w) / Q (X w)
  set d₁ := bil Q (X' w) (X u) / Q (X u)
  set d₂ := bil Q (X' w) (X w) / Q (X w)
  have hQv : Q (X' u) = c₁ ^ 2 * Q (X u) + c₂ ^ 2 * Q (X w) := by
    conv_lhs => rw [ev]
    rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxy]; ring
  have hQw : Q (X' w) = d₁ ^ 2 * Q (X u) + d₂ ^ 2 * Q (X w) := by
    conv_lhs => rw [ew]
    rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxy]; ring
  have hvw : c₁ * d₁ * Q (X u) + c₂ * d₂ * Q (X w) = 0 := by
    have h0 : bil Q (X' u) (X' w) = 0 := hX' u w huw
    rw [ev, ew] at h0
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, hxy, hxy', bil_self] at h0
    simp only [c₁, c₂, d₁, d₂]
    linear_combination h0
  exact nonempty_algEquiv_plane (hXa'.aniso u) (hXa'.aniso w) hQv hQw hvw

/-- **The values of an orthogonal basis** of a regular space: the list $(Q(X_0), \dots, Q(X_{n-1}))$ of units
(all $Q(X_i) \ne 0$ in a regular space, `isOrthAniso_basis`).  This is the list $(a_0, \dots, a_{n-1})$ of the
decomposition $V = \langle a_0\rangle \perp \cdots \perp \langle a_{n-1}\rangle$ of O'Meara (§58, p. 149-150). -/
def values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) : List Fˣ :=
  List.ofFn fun i => Units.mk0 (Q (X i)) ((isOrthAniso_basis hQ X hX).aniso i)

theorem length_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) : (values hQ X hX).length = n := by
  simp [values]

theorem getElem?_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) (j : ℕ) (hj : j < n) :
    (values hQ X hX)[j]? = some (Units.mk0 (Q (X ⟨j, hj⟩)) ((isOrthAniso_basis hQ X hX).aniso _)) := by
  simp [values, hj]

/-- **The discriminant is well defined modulo squares:** for two orthogonal bases $X, X'$ of a regular space,
$\prod Q(X'_i) = t^2 \prod Q(X_i)$ with $t$ the determinant of the change of basis matrix (so the product of the
values of an orthogonal basis is a representative of the discriminant $dV$ modulo $F^{\times 2}$). -/
theorem exists_prod_values_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X X' : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hX' : IsOrthogonalBasis Q X') :
    ∃ t : Fˣ, (values hQ X' hX').prod = t ^ 2 * (values hQ X hX).prod := by
  have hXa := isOrthAniso_basis hQ X hX
  have hXa' := isOrthAniso_basis hQ X' hX'
  have h := det_gram_eq_sq_mul X X' (Q := Q)
  rw [det_gram_of_isOrthAniso hXa', det_gram_of_isOrthAniso hXa] at h
  have hne : (X.toMatrix X').det ≠ 0 := by
    intro h0
    rw [h0] at h
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hXa'.aniso i) (by simpa using h)
  refine ⟨Units.mk0 _ hne, Units.ext ?_⟩
  simp only [values, List.prod_ofFn, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
    Units.coe_prod]
  exact h

/-- One step of a chain of orthogonal bases: if $X'$ arises from $X$ by altering at most two adjacent basis
vectors (`AdjacentChange`) then the Hasse algebras of the value lists are similar.  (The class of the Hasse algebra
in the Brauer monoid is unchanged: `cls_hasseAlg_adj` with the plane step `nonempty_algEquiv_step`.) -/
theorem cls_hasseAlg_values_adj (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X X' : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hX' : IsOrthogonalBasis Q X')
    (hadj : AdjacentChange X X') :
    cls (hasseAlg (values hQ X hX)) = cls (hasseAlg (values hQ X' hX')) := by
  obtain ⟨i, hi⟩ := hadj
  obtain ⟨t, ht⟩ := exists_prod_values_eq hQ X X' hX hX'
  refine cls_hasseAlg_adj i _ _ t (by rw [length_values, length_values]) ?_ ht ?_
  · intro j hj1 hj2
    by_cases hjn : j < n
    · rw [getElem?_values hQ X hX j hjn, getElem?_values hQ X' hX' j hjn]
      congr 1
      refine Units.ext ?_
      simp only [Units.val_mk0]
      rw [hi ⟨j, hjn⟩ hj1 hj2]
    · rw [List.getElem?_eq_none (by rw [length_values]; omega),
        List.getElem?_eq_none (by rw [length_values]; omega)]
  · intro p q p' q' h1 h2 h3 h4
    have hi1 : i + 1 < n := by
      have := (List.getElem?_eq_some_iff.1 h2).1
      rwa [length_values] at this
    rw [getElem?_values hQ X hX i (by omega)] at h1
    rw [getElem?_values hQ X hX (i + 1) hi1] at h2
    rw [getElem?_values hQ X' hX' i (by omega)] at h3
    rw [getElem?_values hQ X' hX' (i + 1) hi1] at h4
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    obtain rfl := Option.some.inj h3
    obtain rfl := Option.some.inj h4
    obtain ⟨e⟩ := nonempty_algEquiv_step hQ X X' hX hX' i hi1 hi
    exact (cls_eq_iff.2 (isBrauerEquivalent_of_algEquiv
      (A := qs (Units.mk0 (Q (X' ⟨i, by omega⟩)) ((isOrthAniso_basis hQ X' hX').aniso _))
        (Units.mk0 (Q (X' ⟨i + 1, hi1⟩)) ((isOrthAniso_basis hQ X' hX').aniso _)))
      (B := qs (Units.mk0 (Q (X ⟨i, by omega⟩)) ((isOrthAniso_basis hQ X hX).aniso _))
        (Units.mk0 (Q (X ⟨i + 1, hi1⟩)) ((isOrthAniso_basis hQ X hX).aniso _))) e)).symm

/-- The Hasse algebras of the value lists of any two orthogonal bases of a regular space are similar (the
first half of 58:2; the book proves isomorphism, see `nonempty_algEquiv_hasseAlg_values`).  Proof as in the
book: 58:1 gives a chain of orthogonal bases in which consecutive bases differ in two adjacent vectors, and
each step preserves the class (`cls_hasseAlg_values_adj`). -/
theorem isBrauerEquivalent_hasseAlg_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    IsBrauerEquivalent (hasseAlg (values hQ X hX)) (hasseAlg (values hQ Y hY)) := by
  obtain ⟨k, Z, h0, hl, hZ, hadj⟩ := exists_adjacent_chain_of_orthogonal_bases hQ X Y hX hY
  subst h0 hl
  have key : ∀ m : Fin (k + 1), cls (hasseAlg (values hQ (Z 0) hX)) =
      cls (hasseAlg (values hQ (Z m) (hZ m))) := by
    intro m
    induction m using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [ih]
      exact cls_hasseAlg_values_adj hQ (Z i.castSucc) (Z i.succ) (hZ _) (hZ _) (hadj i)
  exact cls_eq_iff.1 (key (Fin.last k))

/-- **O'Meara 58:2** (§58, p. 151): *the Hasse algebra $S V$ is well defined, at least up to an algebra
isomorphism.*  For a regular quadratic space $V$ of dimension $n$ and two orthogonal bases $X, Y$ (the values
$Q(X_i)$, $Q(Y_i)$ are automatically nonzero), the Hasse algebras of the value lists are isomorphic $F$-algebras.

Proof, following the book: by 58:1 it suffices to compare bases altering two adjacent vectors (`cls_hasseAlg_adj`
via `cls_hasseAlg_values_adj`); the rules of 57:10/57:11 (here: bimultiplicativity, symmetry and square
invariance of the symbol, `B_mul_right`, `B_comm`, `B_sq_mul_left`) reduce this to
$(a_i,a_{i+1}) \cong (a_i',a_{i+1}')$, which holds as both are the Clifford algebra of the same plane
(`nonempty_algEquiv_step`, via 57:7/57:5).  The book concludes an isomorphism from the computations with the
rules; here the computations give *similarity* of the two algebras (`isBrauerEquivalent_hasseAlg_values`) and
isomorphism follows since similar central simple algebras of the same dimension $4^n$ are isomorphic
(`nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq`).  *Deviation:* the book has $(a_i, d_i)$ with $d_i$
the product of the later values; the comparison of the discriminants $d_i$ of the two bases (equal up to
squares, `exists_prod_values_eq`) is done inside `cls_hasseAlg_adj`. -/
theorem nonempty_algEquiv_hasseAlg_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    Nonempty (hasseAlg (values hQ X hX) ≃ₐ[F] hasseAlg (values hQ Y hY)) :=
  nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq (isBrauerEquivalent_hasseAlg_values hQ X Y hX hY)
    (by rw [finrank_hasseAlg, finrank_hasseAlg, length_values, length_values])

end Geometry

end Rev

/-! ### The Hasse algebra of O'Meara (prefix products) -/

theorem cls_rev_hasseAlg_reverse (l : List Fˣ) :
    cls (Rev.hasseAlg l.reverse) = cls (Rev.hasseAlg l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.reverse_cons, Rev.cls_hasseAlg_append, ih, Rev.cls_hasseAlg_cons x l,
      Rev.cls_hasseAlg_cons x [], List.prod_reverse]
    simp only [Rev.cls_hasseAlg_nil, List.prod_cons, List.prod_nil, mul_one, B_mul_right, B_self]
    rw [B_comm l.prod x]
    ac_rfl

/-- **The Hasse algebra** $S V$ of a diagonal quadratic space (O'Meara 1963, §58, p. 150: "the Hasse algebra
$S_F V = \bigotimes_{1 \le i \le n} (a_i, d_i)$ where $d_i = a_1 \cdots a_i$"): for the list `a`
$= (a_0, \dots, a_{n-1})$ of the values $a_i = Q(x_i)$ of an orthogonal base (0-based), `hasseAlg a` is the bundled
tensor product $\bigotimes_{i<n} (a_i, d_i)$ with the *prefix* products $d_i = a_0 a_1 \cdots a_i$ (the empty
tensor product is $F$).  It is central simple by 57:2 and 52:1 (this is why it is a bundled `CSA`).

*Implementation.*  `hasseAlg a := Rev.hasseAlg a.reverse`, whose factors are $(a_i, a_0 \cdots a_i)$ listed in
decreasing order of $i$; the order of the tensor factors is immaterial up to isomorphism (`A ⊗ B ≅ B ⊗ A`).

*Reading of the definition.*  The machine-read text of the displayed definition is garbled; the prefix products
$d_i = a_0 \cdots a_i$ are reconstructed from the surviving "where $d_i = \ldots$" and from the proof of 58:2, which
says that when $x_i, x_{i+1}$ change, $d_\lambda$ is unchanged for $\lambda < i$ and changes by a square factor for
$\lambda > i$, which is true for prefix products only.  The product over all pairs $i \le j$ of $(a_i,a_j)$ is the
first rule of 58:3, `hasseAlgPairs`; it is similar to this algebra
(`isBrauerEquivalent_hasseAlg_hasseAlgPairs`) but has a larger dimension. -/
@[kb "omeara1963" "§58, p. 150 (the Hasse algebra S V)"]
def hasseAlg (a : List Fˣ) : CSA.{u, u} F := Rev.hasseAlg a.reverse

/-- **The product $\bigotimes_{i \le j} (a_i, a_j)$ over all pairs of positions** $0 \le i \le j < n$ (the
right-hand side of the first rule of 58:3, p. 151). -/
@[kb "omeara1963" "§58, 58:3, p. 151 (the algebra ⊗_{i≤j} (a_i, a_j))"]
def hasseAlgPairs (a : List Fˣ) : CSA.{u, u} F := Rev.hasseAlgPairs a

/-- The class of the Hasse algebra does not depend on the use of prefix or suffix products. -/
theorem cls_hasseAlg_eq (a : List Fˣ) : cls (hasseAlg a) = cls (Rev.hasseAlg a) :=
  cls_rev_hasseAlg_reverse a

/-- **O'Meara 58:3, first rule** (p. 151): the Hasse algebra is similar to $\bigotimes_{i \le j} (a_i, a_j)$,
the product over all pairs of positions. -/
@[kb "omeara1963" "§58, 58:3, p. 151 (S V ~ ⊗_{i≤j} (a_i, a_j))"]
theorem isBrauerEquivalent_hasseAlg_hasseAlgPairs (a : List Fˣ) :
    IsBrauerEquivalent (hasseAlg a) (hasseAlgPairs a) :=
  cls_eq_iff.1 (by rw [cls_hasseAlg_eq]; exact (Rev.cls_hasseAlgPairs a).symm)

/-- **O'Meara 58:3, orthogonal sums** (p. 151): for a splitting $V = U \perp W$ into orthogonal diagonalizable
parts, with $U$ having orthogonal base values `a` and $W$ having `a'` (so that $V$ has the concatenated list),
$S V \sim S U \otimes (dU, dW) \otimes S W$, where $dU = \prod a$ and $dW = \prod a'$ are the discriminants.
(Proved from the suffix-product version; the class of the Hasse algebra does not depend on the variant.) -/
@[kb "omeara1963" "§58, 58:3, p. 151 (S V ~ S U ⊗ (dU, dW) ⊗ S W)"]
theorem isBrauerEquivalent_hasseAlg_append (a a' : List Fˣ) :
    IsBrauerEquivalent (hasseAlg (a ++ a'))
      (tensor (tensor (hasseAlg a) (qs a.prod a'.prod)) (hasseAlg a')) :=
  cls_eq_iff.1 (by
    simp only [cls_tensor, cls_hasseAlg_eq]
    rw [Rev.cls_hasseAlg_append]; rfl)

/-- **O'Meara 58:3, scaling** (p. 151-152), reconstruction of the garbled formula.  If $V$ has an orthogonal
base of values `l` $= (a_0,\dots,a_{n-1})$ then $V^\alpha$ has the orthogonal base of values $\alpha a_i$
(`l.map (α * ·)`), and
$$S(V^\alpha) \sim \bigl(\alpha,\ (-1)^{n(n+1)/2}\, (dV)^{n+1}\bigr) \otimes S V,\qquad dV = \prod a_i.$$
*Reconstruction note.*  The printed formula is illegible in the machine-read text; this formula was derived by
computation from the definition and 57:10, 57:11: $S(V^\alpha)$ and $S V$ differ by the factor
$(\alpha,\alpha)^{n(n+1)/2}\,(\alpha,dV)^{n+1}$ (each of the $n(n+1)/2$ pairs $i \le j$ contributes $(\alpha,\alpha)$,
and each $a_k$ occurs in $n+1$ pairs), and $(\alpha,\alpha) \cong (\alpha,-1)$ (57:10 (3)),
$(\alpha,b)\otimes(\alpha,c) \sim (\alpha,bc)$ (57:11).  Since $(\alpha,b)\otimes(\alpha,b) \sim 1$ the exponent
$n+1$ may be reduced modulo $2$. -/
@[kb "omeara1963" "§58, 58:3, pp. 151-152 (scaling) [garbled; reconstructed]"]
theorem isBrauerEquivalent_hasseAlg_scale (α : Fˣ) (l : List Fˣ) :
    IsBrauerEquivalent (hasseAlg (l.map (α * ·)))
      (tensor (qs α ((-1) ^ (l.length * (l.length + 1) / 2) * l.prod ^ (l.length + 1))) (hasseAlg l)) :=
  cls_eq_iff.1 (by
    simp only [cls_tensor, cls_hasseAlg_eq]
    rw [Rev.cls_hasseAlg_scale]; rfl)

/-- **O'Meara 58:3, ternary spaces** (p. 152), reconstruction of the garbled formula.  For a ternary space with
an orthogonal base of values $a_0, a_1, a_2$ (0-based; the book's $a_1,a_2,a_3$):
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_1a_2).$$
*Reconstruction note.*  The machine-read text has illegible arguments; the formula was derived (and is true) as
stated, by expanding both sides with bimultiplicativity of the symbol, $(a,a) \cong (a,-1)$ and
$(a,b)\otimes(a,b)\sim 1$.  The class of $S V$ is $(dV,-1)\otimes\bigotimes_{i<j}(a_i,a_j)$, symmetric in the
order of the values, so the formula holds for prefix and suffix products alike.  No hypothesis on the
discriminant is needed. -/
@[kb "omeara1963" "§58, 58:3, p. 152 (ternary) [garbled; reconstructed]"]
theorem isBrauerEquivalent_hasseAlg_ternary (a b c : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c])) (qs (-(a * b)) (-(b * c))) :=
  cls_eq_iff.1 (by
    simp only [cls_tensor, cls_hasseAlg_eq]
    exact Rev.cls_hasseAlg_ternary a b c)

/-- **O'Meara 58:3, quaternary spaces** (p. 152), reconstruction of the garbled formula.  For a quaternary space
with an orthogonal base of values $a_0,a_1,a_2,a_3$ (0-based) and discriminant $dV = a_0a_1a_2a_3$:
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_1a_2) \otimes (a_3,\ dV).$$
*Reconstruction note.*  The machine-read text shows the ternary right-hand side times a factor "$(a_?, dV)$";
the index of the first entry is illegible.  Computing, the missing factor is $(a_3, dV)$ with $a_3$ the *last*
value: the ternary formula for the first three values leaves $(a_3,-a_0a_1a_2)$ (from the pairs involving $a_3$),
and $(a_3,-a_0a_1a_2) = (a_3,-1)\otimes(a_3,a_0a_1a_2) \sim (a_3,a_3)\otimes(a_3,a_0a_1a_2) \sim
(a_3, a_0a_1a_2a_3)$ by 57:10 (3) and 57:11. -/
@[kb "omeara1963" "§58, 58:3, p. 152 (quaternary) [garbled; reconstructed]"]
theorem isBrauerEquivalent_hasseAlg_quaternary (a b c d : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c, d]))
      (tensor (qs (-(a * b)) (-(b * c))) (qs d (a * b * c * d))) :=
  cls_eq_iff.1 (by
    simp only [cls_tensor, cls_hasseAlg_eq]
    exact Rev.cls_hasseAlg_quaternary a b c d)

theorem finrank_hasseAlg (a : List Fˣ) : Module.finrank F (hasseAlg a) = 4 ^ a.length := by
  have := Rev.finrank_hasseAlg a.reverse
  rwa [List.length_reverse] at this

section Geometry

open Module

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- The Hasse algebras of the value lists of any two orthogonal bases of a regular space are similar (the
first half of 58:2; see `nonempty_algEquiv_hasseAlg_values`). -/
theorem isBrauerEquivalent_hasseAlg_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    IsBrauerEquivalent (hasseAlg (Rev.values hQ X hX)) (hasseAlg (Rev.values hQ Y hY)) :=
  cls_eq_iff.1 (by
    simp only [cls_hasseAlg_eq]
    exact cls_eq_iff.2 (Rev.isBrauerEquivalent_hasseAlg_values hQ X Y hX hY))

/-- **O'Meara 58:2** (§58, p. 151): *the Hasse algebra $S V$ is well defined, at least up to an algebra
isomorphism.*  For a regular quadratic space $V$ of dimension $n$ and two orthogonal bases $X, Y$ (the values
$Q(X_i)$, $Q(Y_i)$ are automatically nonzero), the Hasse algebras of the value lists are isomorphic $F$-algebras.

Proof, following the book: by 58:1 it suffices to compare bases altering two adjacent vectors; the rules of
57:10/57:11 (here: bimultiplicativity, symmetry and square invariance of the symbol, `B_mul_right`, `B_comm`,
`B_sq_mul_left`) reduce this to $(a_i,a_{i+1}) \cong (a_i',a_{i+1}')$, which holds as both are the Clifford algebra
of the same plane (`Rev.nonempty_algEquiv_step`, via 57:7/57:5), and the discriminants agree up to squares
(`Rev.exists_prod_values_eq`).  The computations give *similarity* of the two algebras
(`isBrauerEquivalent_hasseAlg_values`); an isomorphism follows since similar central simple algebras of the same
dimension $4^n$ are isomorphic (`Rev.nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq`).  The computation is
carried out in the Brauer monoid with suffix products, which gives the same class as the prefix products
(`cls_hasseAlg_eq`). -/
@[kb "omeara1963" "§58, 58:2, p. 151"]
theorem nonempty_algEquiv_hasseAlg_values (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    Nonempty (hasseAlg (Rev.values hQ X hX) ≃ₐ[F] hasseAlg (Rev.values hQ Y hY)) :=
  Rev.nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq
    (isBrauerEquivalent_hasseAlg_values hQ X Y hX hY)
    (by rw [finrank_hasseAlg, finrank_hasseAlg, Rev.length_values, Rev.length_values])

end Geometry

end Quaternion

end QuadFormsKB.OMeara.Hasse58
