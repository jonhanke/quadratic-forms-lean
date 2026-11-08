/-
# Watson (1963), §5: perfect forms represented by orthogonal sums

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576.

Watson's forms are integer-valued, as `QuadForm ℤ n` here (his matrix $A(f) = (\partial^2 f/\partial x_i \partial x_j)$ is
the Hessian `QuadForm.hessian`). A form $f$ in $n$ variables *represents* a form $\varphi$ in $v$ variables if
$f(H\vec y) = \varphi(\vec y)$ identically for an integral $n \times v$ matrix $H$ (`Rep`; over another ring $S$,
`RepOver S`).

**Proved here.**
* `Rep.trans`, `Rep.of_intEquiv_left`, `Rep.of_intEquiv_right`, `Rep.orthSum_left`, `Rep.orthSum_right`: composition,
  invariance under integral equivalence, and the obvious representations by orthogonal sums.
* `Rep.le_of_posDef`: a positive definite form in $v$ variables is represented only by forms in $n \ge v$ variables.
* `IsPerfectOne`: Watson's *perfect form with minimum $1$* (p. 557): $\varphi$ is positive definite, and every integral
  form $\varphi'$ in the same variables with $\varphi'(\vec y) = 1$ whenever $\varphi(\vec y) = 1$ equals $\varphi$.
* `rep_orthSum_of_perfect` (**Watson 1963, Lemma 3**): if a positive definite orthogonal sum $g \perp \psi$ represents
  a perfect form with minimum $1$, then $g$ or $\psi$ represents it.

Variables are $x_0, \dots, x_{n-1}$; in $g \perp \psi$ the first variables carry $g$.
-/
import QuadFormsKB.Literature.Cassels.AppA.WatsonTwoClassesCases
import QuadFormsKB.LocalDensity.FormDensitySelf

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n v : ℕ}

/-! ### Representations of forms by forms -/

/-- **Representation of a form by a form over a ring $S$** (Watson 1963, §4, proof of Lemma 2): the integral form $f$
in $n$ variables represents the integral form $\varphi$ in $v$ variables over the commutative ring $S$ if there is an
$n \times v$ matrix $H$ over $S$ with $f(H\vec y) = \varphi(\vec y)$ for all $\vec y \in S^v$. Arguments: the ring `S`,
the forms `f` and `φ`. -/
@[kb "watson1963" "§4, proof of Lemma 2, p. 555 (f(Hy) = φ(y))"]
def RepOver (S : Type*) [CommRing S] (f : QuadForm ℤ n) (φ : QuadForm ℤ v) : Prop :=
  ∃ H : Matrix (Fin n) (Fin v) S, ∀ y : Fin v → S, f.evalIn S (H *ᵥ y) = φ.evalIn S y

/-- **Representation over $\mathbb Z$** (Watson 1963, §4, p. 555): $f(H\vec y) = \varphi(\vec y)$ identically, for an
integral $n \times v$ matrix $H$. Arguments: the forms `f` and `φ`. -/
@[kb "watson1963" "§4, proof of Lemma 2, p. 555 (f represents φ)"]
def Rep (f : QuadForm ℤ n) (φ : QuadForm ℤ v) : Prop :=
  ∃ H : Matrix (Fin n) (Fin v) ℤ, ∀ y : Fin v → ℤ, f.eval (H *ᵥ y) = φ.eval y

/-- `Rep` is `RepOver ℤ`. -/
theorem rep_iff_repOver_int {f : QuadForm ℤ n} {φ : QuadForm ℤ v} : Rep f φ ↔ RepOver ℤ f φ := Iff.rfl

/-- Every form represents itself. -/
theorem Rep.refl (f : QuadForm ℤ n) : Rep f f := ⟨1, fun y => by rw [one_mulVec]⟩

/-- **Composition of representations:** if $f$ represents $g$ and $g$ represents $\varphi$, then $f$ represents
$\varphi$. -/
theorem Rep.trans {m : ℕ} {f : QuadForm ℤ n} {g : QuadForm ℤ m} {φ : QuadForm ℤ v} (h₁ : Rep f g) (h₂ : Rep g φ) :
    Rep f φ := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  exact ⟨H₁ * H₂, fun y => by rw [← mulVec_mulVec, hH₁, hH₂]⟩

/-- Composition of representations over a ring $S$. -/
theorem RepOver.trans {S : Type*} [CommRing S] {m : ℕ} {f : QuadForm ℤ n} {g : QuadForm ℤ m} {φ : QuadForm ℤ v}
    (h₁ : RepOver S f g) (h₂ : RepOver S g φ) : RepOver S f φ := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  exact ⟨H₁ * H₂, fun y => by rw [← mulVec_mulVec, hH₁, hH₂]⟩

/-- An integral equivalence is a representation. -/
theorem Rep.of_intEquiv {f f' : QuadForm ℤ n} (h : IntEquiv f f') : Rep f f' := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.val, hg⟩

/-- Representations are invariant under integral equivalence of the representing form. -/
theorem Rep.of_intEquiv_left {f f' : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : IntEquiv f f') (hr : Rep f φ) :
    Rep f' φ :=
  (Rep.of_intEquiv (IsometricGL.symm h)).trans hr

/-- An integral form represents itself over every ring. -/
theorem RepOver.refl (S : Type*) [CommRing S] (f : QuadForm ℤ n) : RepOver S f f :=
  ⟨1, fun y => by rw [one_mulVec]⟩

/-- Helper: evaluation of an integral form at an integer vector, computed in $S$. -/
theorem evalIn_intCast_vec {S : Type*} [CommRing S] (f : QuadForm ℤ n) (x : Fin n → ℤ) :
    f.evalIn S (fun i => (x i : S)) = ((f.eval x : ℤ) : S) := by
  simp only [QuadForm.evalIn, QuadForm.eval, algebraMap_int_eq, eq_intCast, Int.cast_sum, Int.cast_mul,
    Int.cast_ite, Int.cast_zero, Algebra.algebraMap_self, RingHom.id_apply, Int.cast_id]

/-- A representation over $\mathbb Z$ gives one over every ring $S$ (map the matrix). -/
theorem Rep.repOver {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : Rep f φ) (S : Type*) [CommRing S] :
    RepOver S f φ := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.map (Int.castRingHom S), fun y => ?_⟩
  -- both sides are polynomial identities; compare as compositions of forms
  have h1 : f.compMat H = φ := QuadForm.eq_of_eval_eq fun y => by rw [QuadForm.eval_compMat, hH]
  have h2 : (f.compMat H).evalIn S y = φ.evalIn S y := by rw [h1]
  rw [← h2]
  have h3 := QuadForm.map_compMat (Int.castRingHom S) f H
  have h4 : ((f.map (Int.castRingHom S)).compMat (H.map (Int.castRingHom S))).eval y =
      ((f.compMat H).map (Int.castRingHom S)).eval y := by rw [h3]
  rw [QuadForm.eval_compMat] at h4
  have e1 : ∀ (m : ℕ) (Q : QuadForm ℤ m) (x : Fin m → S), (Q.map (Int.castRingHom S)).eval x = Q.evalIn S x := by
    intro m Q x
    simp [QuadForm.evalIn, QuadForm.map]
  rw [e1, e1] at h4
  exact h4

/-! ### Orthogonal sums -/

/-- Helper: the value of an orthogonal sum over $S$. -/
theorem evalIn_orthSum' {S : Type*} [CommRing S] {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m)
    (x : Fin (k + m) → S) :
    (QuadForm.orthSum g ψ).evalIn S x = g.evalIn S (fun i => x (Fin.castAdd m i)) +
      ψ.evalIn S (fun j => x (Fin.natAdd k j)) :=
  QuadForm.evalIn_orthSum S g ψ x

/-- Helper: an integral form vanishes at $\vec 0$ over every ring. -/
theorem evalIn_zero' {S : Type*} [CommRing S] {m : ℕ} (Q : QuadForm ℤ m) : Q.evalIn S 0 = 0 := by
  simp [QuadForm.evalIn]

/-- **The first summand is represented by an orthogonal sum** (over every ring): $g \perp \psi$ represents $g$. -/
theorem RepOver.orthSum_left (S : Type*) [CommRing S] {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m) :
    RepOver S (QuadForm.orthSum g ψ) g := by
  refine ⟨Matrix.of fun i j => Fin.addCases (fun a => if a = j then 1 else 0) (fun _ => 0) i, fun y => ?_⟩
  rw [evalIn_orthSum']
  have h1 : (fun i => ((Matrix.of fun i j => Fin.addCases (motive := fun _ => S)
      (fun a => if a = j then 1 else 0) (fun _ => 0) i) *ᵥ y) (Fin.castAdd m i)) = y := by
    funext i
    simp [mulVec, dotProduct, Fin.addCases_left]
  have h2 : (fun j => ((Matrix.of fun i j => Fin.addCases (motive := fun _ => S)
      (fun a => if a = j then 1 else 0) (fun _ => 0) i) *ᵥ y) (Fin.natAdd k j)) = (0 : Fin m → S) := by
    funext j
    simp [mulVec, dotProduct, Fin.addCases_right]
  rw [h1, h2, evalIn_zero', add_zero]

/-- **The second summand is represented by an orthogonal sum** (over every ring): $g \perp \psi$ represents $\psi$. -/
theorem RepOver.orthSum_right (S : Type*) [CommRing S] {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m) :
    RepOver S (QuadForm.orthSum g ψ) ψ := by
  refine ⟨Matrix.of fun i j => Fin.addCases (fun _ => 0) (fun b => if b = j then 1 else 0) i, fun y => ?_⟩
  rw [evalIn_orthSum']
  have h1 : (fun i => ((Matrix.of fun i j => Fin.addCases (motive := fun _ => S)
      (fun _ => 0) (fun b => if b = j then 1 else 0) i) *ᵥ y) (Fin.castAdd m i)) = (0 : Fin k → S) := by
    funext i
    simp [mulVec, dotProduct, Fin.addCases_left]
  have h2 : (fun j => ((Matrix.of fun i j => Fin.addCases (motive := fun _ => S)
      (fun _ => 0) (fun b => if b = j then 1 else 0) i) *ᵥ y) (Fin.natAdd k j)) = y := by
    funext j
    simp [mulVec, dotProduct, Fin.addCases_right]
  rw [h1, h2, evalIn_zero', zero_add]

/-- $g \perp \psi$ represents $g$ over $\mathbb Z$. -/
theorem Rep.orthSum_left {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m) : Rep (QuadForm.orthSum g ψ) g :=
  RepOver.orthSum_left ℤ g ψ

/-- $g \perp \psi$ represents $\psi$ over $\mathbb Z$. -/
theorem Rep.orthSum_right {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m) : Rep (QuadForm.orthSum g ψ) ψ :=
  RepOver.orthSum_right ℤ g ψ

/-- **Orthogonal sums of representations** (over every ring): if $f_1$ represents $\varphi_1$ and $f_2$ represents
$\varphi_2$, then $f_1 \perp f_2$ represents $\varphi_1 \perp \varphi_2$ (block-diagonal matrix). -/
theorem RepOver.orthSum {S : Type*} [CommRing S] {n₁ n₂ v₁ v₂ : ℕ} {f₁ : QuadForm ℤ n₁} {f₂ : QuadForm ℤ n₂}
    {φ₁ : QuadForm ℤ v₁} {φ₂ : QuadForm ℤ v₂} (h₁ : RepOver S f₁ φ₁) (h₂ : RepOver S f₂ φ₂) :
    RepOver S (QuadForm.orthSum f₁ f₂) (QuadForm.orthSum φ₁ φ₂) := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  refine ⟨Matrix.of fun i j => Fin.addCases (fun a => Fin.addCases (fun b => H₁ a b) (fun _ => 0) j)
    (fun a => Fin.addCases (fun _ => 0) (fun b => H₂ a b) j) i, fun y => ?_⟩
  rw [evalIn_orthSum', evalIn_orthSum', ← hH₁, ← hH₂]
  congr 2
  · funext a
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      zero_mul, Finset.sum_const_zero, add_zero]
  · funext a
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      zero_mul, Finset.sum_const_zero, zero_add]

/-! ### Dimension -/

/-- **A positive definite form is represented only by forms in at least as many variables:** if $f$ in $n$ variables
represents a positive definite $\varphi$ in $v$ variables, then $v \le n$ (otherwise $H$ has a non-zero kernel vector
$\vec y$, and $\varphi(\vec y) = f(\vec 0) = 0$). Arguments: `hφ` positive definiteness of `φ`, `h` the
representation. -/
theorem Rep.le_of_posDef {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (hφ : IntQF.PosDef φ) (h : Rep f φ) : v ≤ n := by
  classical
  by_contra hlt
  push_neg at hlt
  obtain ⟨H, hH⟩ := h
  -- pad `H` with zero rows to a square matrix
  let H' : Matrix (Fin v) (Fin v) ℤ := fun i j => if hi : i.val < n then H ⟨i.val, hi⟩ j else 0
  have hdet : H'.det = 0 := by
    have hrow : ∀ j, H' ⟨n, hlt⟩ j = 0 := fun j => by simp [H']
    exact Matrix.det_eq_zero_of_row_eq_zero ⟨n, hlt⟩ hrow
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hHy : H *ᵥ y = 0 := by
    funext i
    have := congrFun hy ⟨i.val, by omega⟩
    simpa [H', mulVec, dotProduct, i.isLt] using this
  have h1 := hH y
  rw [hHy, eval_zero_int] at h1
  have h2 := hφ y hy0
  omega

/-! ### Perfect forms with minimum 1 -/

/-- **Perfect form with minimum $1$** (Watson 1963, §5, p. 557): $\varphi$ in $v$ variables is positive definite and
every integral form $\varphi'$ in the same variables with
$$\varphi(\vec y) = 1 \implies \varphi'(\vec y) = 1 \qquad (\vec y \in \mathbb Z^v)$$
is equal to $\varphi$. (Watson's (5.3). His $\varphi'$ are arbitrary forms; integral ones suffice for Lemma 3.)
Argument: the form `φ`. -/
@[kb "watson1963" "§5, (5.3), p. 557 (perfect form with minimum 1)"]
def IsPerfectOne (φ : QuadForm ℤ v) : Prop :=
  IntQF.PosDef φ ∧ ∀ φ' : QuadForm ℤ v, (∀ y, φ.eval y = 1 → φ'.eval y = 1) → φ' = φ

/-- Helper: the sum of two forms (coefficientwise), with value the sum of the values. -/
def addForm {m : ℕ} (Q₁ Q₂ : QuadForm ℤ m) : QuadForm ℤ m :=
  ⟨Q₁.coeff + Q₂.coeff, fun i j h => by simp [Q₁.upper h, Q₂.upper h]⟩

theorem eval_addForm {m : ℕ} (Q₁ Q₂ : QuadForm ℤ m) (x : Fin m → ℤ) :
    (addForm Q₁ Q₂).eval x = Q₁.eval x + Q₂.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, addForm, Matrix.add_apply, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Helper: the product of two linear forms $\vec y \mapsto (\vec u \cdot \vec y)(\vec w \cdot \vec y)$ as a form
(the hyperbolic form $z_0 z_1$ composed with the matrix with rows $\vec u, \vec w$). -/
def linProd {m : ℕ} (u w : Fin m → ℤ) : QuadForm ℤ m :=
  (QuadForm.ofUpper ![![0, 1], ![0, 0]] : QuadForm ℤ 2).compMat (Matrix.of ![u, w])

theorem eval_linProd {m : ℕ} (u w : Fin m → ℤ) (y : Fin m → ℤ) :
    (linProd u w).eval y = (u ⬝ᵥ y) * (w ⬝ᵥ y) := by
  rw [linProd, QuadForm.eval_compMat]
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two, mulVec]

/-- Helper: if $(\vec u \cdot \vec y)(\vec w \cdot \vec y) = 0$ for all integer $\vec y$, then $\vec u = 0$ or
$\vec w = 0$. -/
theorem eq_zero_or_eq_zero_of_linProd {m : ℕ} {u w : Fin m → ℤ} (h : ∀ y : Fin m → ℤ, (u ⬝ᵥ y) * (w ⬝ᵥ y) = 0) :
    u = 0 ∨ w = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hu, hw⟩ := hne
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h'; push_neg at h'; exact hu (funext h')
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h'; push_neg at h'; exact hw (funext h')
  have hd : ∀ (a : Fin m → ℤ) (k : Fin m), a ⬝ᵥ Pi.single k 1 = a k := fun a k => by
    simp [dotProduct_single]
  have hi' := h (Pi.single i 1)
  have hj' := h (Pi.single j 1)
  rw [hd, hd] at hi' hj'
  have hwi : w i = 0 := by
    rcases mul_eq_zero.mp hi' with h1 | h1
    · exact absurd h1 hi
    · exact h1
  have huj : u j = 0 := by
    rcases mul_eq_zero.mp hj' with h1 | h1
    · exact h1
    · exact absurd h1 hj
  have hij := h (Pi.single i 1 + Pi.single j 1)
  rw [dotProduct_add, dotProduct_add, hd, hd, hd, hd, hwi, huj, add_zero, zero_add] at hij
  rcases mul_eq_zero.mp hij with h1 | h1
  · exact hi h1
  · exact hj h1

/-- **Watson 1963, Lemma 3** (p. 556): *let $\varphi$ be a perfect form with minimum $1$, and suppose that the disjoint
positive form $f = g(x_0, \dots, x_{k-1}) + \psi(x_k, \dots, x_{n-1})$ represents $\varphi$. Then one at least of $g$,
$\psi$ represents $\varphi$.*

*Proof (Watson's):* let $f(H\vec y) = \varphi(\vec y)$. For $i < k \le j$ the form $\varphi'(\vec y) =
f(H\vec y) + (H\vec y)_i (H\vec y)_j$ takes the value $1$ wherever $\varphi$ does (a value $1$ of the positive
$g \perp \psi$ has one block zero), so $\varphi' = \varphi$ and row $i$ or row $j$ of $H$ vanishes. Hence all rows of
one block vanish. Arguments: `hg`, `hψ` positive definiteness of $g$, $\psi$; `hφ` perfection; `h` the
representation. -/
@[kb "watson1963" "§5, Lemma 3, p. 556"]
theorem rep_orthSum_of_perfect {k m : ℕ} {g : QuadForm ℤ k} {ψ : QuadForm ℤ m} {φ : QuadForm ℤ v}
    (hg : IntQF.PosDef g) (hψ : IntQF.PosDef ψ) (hφ : IsPerfectOne φ) (h : Rep (QuadForm.orthSum g ψ) φ) :
    Rep g φ ∨ Rep ψ φ := by
  classical
  obtain ⟨H, hH⟩ := h
  set f := QuadForm.orthSum g ψ with hf
  -- rows of the two blocks
  let row : Fin (k + m) → Fin v → ℤ := fun i => fun l => H i l
  have hrow : ∀ (i : Fin (k + m)) (y : Fin v → ℤ), (H *ᵥ y) i = row i ⬝ᵥ y := fun i y => rfl
  -- a value 1 of `f` has one block zero
  have hblock : ∀ x : Fin (k + m) → ℤ, f.eval x = 1 →
      (fun a => x (Fin.castAdd m a)) = 0 ∨ (fun b => x (Fin.natAdd k b)) = 0 := by
    intro x hx
    rw [hf, eval_orthSum_int] at hx
    have h1 := posDef_eval_nonneg hg (fun a => x (Fin.castAdd m a))
    have h2 := posDef_eval_nonneg hψ (fun b => x (Fin.natAdd k b))
    by_cases h0 : g.eval (fun a => x (Fin.castAdd m a)) = 0
    · exact Or.inl (posDef_eq_zero_of_eval hg h0)
    · right
      exact posDef_eq_zero_of_eval hψ (by omega)
  -- for each pair (a, b), row a or row b vanishes
  have hpair : ∀ (a : Fin k) (b : Fin m), row (Fin.castAdd m a) = 0 ∨ row (Fin.natAdd k b) = 0 := by
    intro a b
    apply eq_zero_or_eq_zero_of_linProd
    let φ' := addForm φ (linProd (row (Fin.castAdd m a)) (row (Fin.natAdd k b)))
    have hφ' : φ' = φ := by
      apply hφ.2
      intro y hy
      rw [eval_addForm, eval_linProd, hy, ← hrow, ← hrow]
      have hx : f.eval (H *ᵥ y) = 1 := by rw [hH, hy]
      rcases hblock _ hx with h0 | h0
      · have := congrFun h0 a
        simp only [Pi.zero_apply] at this
        rw [this]; ring
      · have := congrFun h0 b
        simp only [Pi.zero_apply] at this
        rw [this]; ring
    intro y
    have := congrArg (fun Q : QuadForm ℤ v => Q.eval y) hφ'
    simp only [φ', eval_addForm, eval_linProd] at this
    linarith
  by_cases hall : ∀ b : Fin m, row (Fin.natAdd k b) = 0
  · left
    refine ⟨Matrix.of fun a l => H (Fin.castAdd m a) l, fun y => ?_⟩
    rw [← hH, hf, eval_orthSum_int]
    have h2 : (fun b => (H *ᵥ y) (Fin.natAdd k b)) = 0 := by
      funext b
      rw [hrow, hall b, zero_dotProduct, Pi.zero_apply]
    rw [h2, eval_zero_int, add_zero]
    rfl
  · right
    push_neg at hall
    obtain ⟨b, hb⟩ := hall
    have hA : ∀ a : Fin k, row (Fin.castAdd m a) = 0 := fun a => (hpair a b).resolve_right hb
    refine ⟨Matrix.of fun b l => H (Fin.natAdd k b) l, fun y => ?_⟩
    rw [← hH, hf, eval_orthSum_int]
    have h1 : (fun a => (H *ᵥ y) (Fin.castAdd m a)) = 0 := by
      funext a
      rw [hrow, hA a, zero_dotProduct, Pi.zero_apply]
    rw [h1, eval_zero_int, zero_add]
    rfl

/-- **A perfect form is not represented by a positive definite form in fewer variables** (`Rep.le_of_posDef`). -/
theorem IsPerfectOne.not_rep_of_lt {m : ℕ} {φ : QuadForm ℤ v} (hφ : IsPerfectOne φ) (f : QuadForm ℤ m) (hm : m < v) :
    ¬ Rep f φ := fun h => absurd (h.le_of_posDef hφ.1) (by omega)

end QuadFormsKB.Watson1963
