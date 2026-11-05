/-
# Cassels, Chapter 2: Examples (exercises), pp. 28–33

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Examples*, pp. 28–33.

**Setting.** $k$ = `F` is a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`). A quadratic space $(U, \phi)$ is
a Mathlib quadratic form `Q : QuadraticForm F V` on a finite-dimensional space, Cassels' bilinear form
$\phi(u, v)$ (with $\phi(u, u) = \phi(u)$) is O'Meara's `OMeara.bil Q` (`QuadraticMap.associated Q`), and *regular* means
that it is nondegenerate. Autometries are the O'Meara group `OMeara.orth Q`, proper ones `OMeara.orthPlus Q`, and
$\tau_a$ = `OMeara.symmetry Q a ha`. A form in $n$ variables is a quadratic form on $k^{n}$ (`Fin n → F`); indices are
$0$-based.

**Proves.**
* Ex. 1 (p. 28): a rational point with $3x_0^{2} - 2x_1^{2} - x_2^{2} = 5$ (`ex1`).
* Ex. 2 (p. 29): a regular isotropic form takes the value $t$ identically on a line, $f(a + tb) = t$ (`ex2`).
* Ex. 3 (p. 29): the non-zero values of $x^{2} + by^{2}$ form a subgroup of $k^{\times}$ (`ex3`).
* Ex. 5 (p. 29): $\phi(\sigma a - a, b) + \phi(a, \sigma b - b) + \phi(\sigma a - a, \sigma b - b) = 0$ (`ex5`).
* Ex. 7, 16, 17: in `Ch2/ExercisesIsotropic.lean`.
* Ex. 8 (p. 30), the Cartan–Dieudonné theorem with the bound $n$: cited, `OMeara.exists_symmetry_prod_eq_length_le`
  (in `Ch2to4Citations.lean`).
* Ex. 9 (p. 30): a proper autometry of an odd-dimensional regular space fixes a non-zero vector (`ex9`).
* Ex. 10 (p. 30): a product of $n$ symmetries can be rewritten as one whose first symmetry is any given one
  (`ex10`).
* Ex. 11 (p. 31): $\det(T - \lambda I) = (-\lambda)^{n}\det(T - \lambda^{-1} I)$ for a proper automorph $T$, and
  $\det(T - I) = 0$ for $n$ odd (`ex11_i`, `ex11_ii`).
* Ex. 12 (p. 31): the order of $GL_n(\mathbb F_p)$ (`ex12`).
* Ex. 18 (p. 33): $\langle a\rangle + \langle -a\rangle = 0$ in $W(k)$ (`ex18`).

**Not formalized here** (recorded in the coverage table): Ex. 4 (the two forms are illegible in the machine-read
text), Ex. 13 (counting representations and automorphs over $\mathbb F_p$), Ex. 14 (topology of $O(V)$ over
$\mathbb R$), Ex. 15 (Springer's theorem), Ex. 19, 20 (Aubry–Brumer).
-/
import QuadFormsKB.Literature.OMeara.Sec43CD
import QuadFormsKB.Literature.Cassels.Ch2.WittGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch2Ex

open QuadFormsKB.OMeara

/-- **Cassels, Ch. 2, Ex. 1 (p. 28).** Find $a_1, a_2, a_3 \in \mathbb Q$ such that $f(a_1, a_2, a_3) = 5$, where
$f(x) = 3x_1^{2} - 2x_2^{2} - x_3^{2}$ (hint: $f(1, 1, 1) = 0$). Transcribed from the page image; indices are
0-based, so $a_1, a_2, a_3$ are `a 0`, `a 1`, `a 2`. Answer: $a = (3, 3, 2)$, since $27 - 18 - 4 = 5$. (General
method: the form is isotropic, hence universal over $\mathbb Q$, Lemma 2.1, Cor. 2.) -/
@[kb "cassels1978" "Ch. 2, Ex. 1, p. 28"]
theorem ex1 : ∃ a : Fin 3 → ℚ, 3 * a 0 ^ 2 - 2 * a 1 ^ 2 - a 2 ^ 2 = 5 := by
  exact ⟨![3, 3, 2], by norm_num⟩

variable {F : Type*} [Field F] [Invertible (2 : F)]

/-- **Cassels, Ch. 2, Ex. 2 (p. 29).** Let $f$ be a regular isotropic form in $n$ variables over $k$. Then there are
$a, b \in k^{n}$ with $f(a + tb) = t$ identically in $t$. *Reconstruction:* the displayed identity is garbled in the
machine-read text; this is the evident reading ($a_i + b_i t$ substituted for $x_i$). -/
@[kb "cassels1978" "Ch. 2, Ex. 2, p. 29"]
theorem ex2 {n : ℕ} (Q : QuadraticForm F (Fin n → F)) (hQ : (associated Q).Nondegenerate)
    (hiso : ∃ x, x ≠ 0 ∧ Q x = 0) :
    ∃ a b : Fin n → F, ∀ t : F, Q (a + t • b) = t := by
  obtain ⟨u, hu0, hu⟩ := hiso
  obtain ⟨w, hw⟩ : ∃ w, bil Q u w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hQ.1 u hcon)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨w', hb⟩ : ∃ w' : Fin n → F, bil Q w' u = 1 / 2 := by
    refine ⟨(2 * bil Q u w)⁻¹ • w, ?_⟩
    rw [bil_smul_left, bil_comm Q w u]
    field_simp
  refine ⟨w' - Q w' • u, u, fun t => ?_⟩
  have e : w' - Q w' • u + t • u = w' + (t - Q w') • u := by module
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [e, Q_add, Q_smul, bil_smul_right, hb, hu]
  linear_combination (t - Q w') * h22

/-- **Cassels, Ch. 2, Ex. 3 (p. 29).** Let $b \in k^{\times}$. The set $A$ of $a \in k^{\times}$ represented over $k$
by $x_0^{2} + b x_1^{2}$ is a subgroup of $k^{\times}$. (Any field; the hint refers to Ch. 3, Lemma 2.1.) -/
@[kb "cassels1978" "Ch. 2, Ex. 3, p. 29"]
theorem ex3 (b : F) (_hb : b ≠ 0) :
    ∃ A : Subgroup Fˣ, ∀ a : Fˣ, a ∈ A ↔ ∃ x y : F, x ^ 2 + b * y ^ 2 = a := by
  refine ⟨{ carrier := {a : Fˣ | ∃ x y : F, x ^ 2 + b * y ^ 2 = a}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun a => Iff.rfl⟩
  · rintro a c ⟨x, y, hxy⟩ ⟨z, w, hzw⟩
    exact ⟨x * z - b * y * w, x * w + y * z, by rw [Units.val_mul, ← hxy, ← hzw]; ring⟩
  · exact ⟨1, 0, by simp⟩
  · rintro a ⟨x, y, hxy⟩
    have ha : (a : F) ≠ 0 := a.ne_zero
    refine ⟨x * (a⁻¹ : Fˣ), y * (a⁻¹ : Fˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val]
    field_simp
    exact hxy

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- An autometry preserves the bilinear form. -/
theorem bil_map_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) :
    bil Q (σ x) (σ y) = bil Q x y := by
  have hσ' : ∀ x, Q (σ x) = Q x := hσ
  have h := hσ' (x + y)
  rw [map_add, Q_add, Q_add, hσ' x, hσ' y] at h
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have : (2 : F) * (bil Q (σ x) (σ y) - bil Q x y) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

/-- **Cassels, Ch. 2, Ex. 5 (p. 29).** If $\sigma$ is an autometry of $(U, \phi)$ and $a, b \in U$, then
$\phi(\sigma a - a, b) + \phi(a, \sigma b - b) + \phi(\sigma a - a, \sigma b - b) = 0$. -/
@[kb "cassels1978" "Ch. 2, Ex. 5, p. 29"]
theorem ex5 {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (a b : V) :
    bil Q (σ a - a) b + bil Q a (σ b - b) + bil Q (σ a - a) (σ b - b) = 0 := by
  simp only [bil_sub_left, bil_sub_right]
  rw [bil_map_orth Q hσ]
  ring

/-- The product $\tau_{u_1}\cdots\tau_{u_r}$ of the symmetries of a list of anisotropic vectors. -/
def prodSym (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) : V ≃ₗ[F] V :=
  (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod

/-- `prodSym` of the empty list is the identity. -/
theorem prodSym_nil (hl : ∀ u ∈ ([] : List V), Q u ≠ 0) : prodSym Q [] hl = 1 := by
  simp [prodSym]

/-- `prodSym` of a cons list is the symmetry times `prodSym` of the tail. -/
theorem prodSym_cons (a : V) (l : List V) (hl : ∀ u ∈ a :: l, Q u ≠ 0) :
    prodSym Q (a :: l) hl = symmetry Q a (hl a (by simp)) *
      prodSym Q l (fun u hu => hl u (by simp [hu])) := by
  simp only [prodSym, List.attach_cons, List.map_cons, List.map_map, List.prod_cons]
  rfl

/-- The determinant of `prodSym l` is $(-1)^{|l|}$. -/
theorem det_prodSym (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    LinearEquiv.det (prodSym Q l hl) = (-1 : Fˣ) ^ l.length := by
  induction l with
  | nil => simp [prodSym_nil]
  | cons a l ih =>
    rw [prodSym_cons, map_mul, det_symmetry, ih, List.length_cons, pow_succ']

/-- `prodSym l` is an autometry. -/
theorem prodSym_mem_orth (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) : prodSym Q l hl ∈ orth Q := by
  induction l with
  | nil => rw [prodSym_nil]; exact (orth Q).one_mem
  | cons a l ih =>
    rw [prodSym_cons]; exact (orth Q).mul_mem (symmetry_mem_orth Q _) (ih _)

/-- `prodSym l` fixes every vector orthogonal to all entries of `l`. -/
theorem prodSym_apply_of_orth (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) (x : V)
    (hx : ∀ u ∈ l, bil Q x u = 0) : prodSym Q l hl x = x := by
  induction l with
  | nil => rw [prodSym_nil]; rfl
  | cons a l ih =>
    rw [prodSym_cons, LinearEquiv.mul_apply, ih _ (fun u hu => hx u (by simp [hu])),
      symmetry_apply, hx a (by simp)]
    simp

/-- Two extra copies of an anisotropic vector can be added to a list without changing `prodSym`. -/
theorem exists_prodSym_pad {y : V} (hy : Q y ≠ 0) (k : ℕ) (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    ∃ l' : List V, ∃ hl' : ∀ u ∈ l', Q u ≠ 0, prodSym Q l' hl' = prodSym Q l hl ∧
      l'.length = l.length + 2 * k := by
  induction k with
  | zero => exact ⟨l, hl, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨l', hl', h1, h2⟩ := ih
    have hl'' : ∀ u ∈ y :: y :: l', Q u ≠ 0 := by
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact hy
      · exact hy
      · exact hl' u hu
    refine ⟨y :: y :: l', hl'', ?_, by simp [h2]; ring⟩
    rw [prodSym_cons, prodSym_cons]
    have : symmetry Q y hy * (symmetry Q y hy * prodSym Q l' hl') = prodSym Q l' hl' := by
      ext x; simp [symmetry_symmetry]
    rw [← h1]; exact this

/-- **Cassels, Ch. 2, Ex. 9 (p. 30).** Let $\sigma \in O^{+}(V)$ where $n = \dim V$ is odd ($V$ regular). Then
$\sigma a = a$ for some $a \ne 0$. -/
@[kb "cassels1978" "Ch. 2, Ex. 9, p. 30"]
theorem ex9 (hQ : (associated Q).Nondegenerate) (hodd : Odd (finrank F V)) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthPlus Q) : ∃ a : V, a ≠ 0 ∧ σ a = a := by
  obtain ⟨l, hl, hσl, hlen⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1
  have hσl' : σ = prodSym Q l hl := hσl
  have hdet : LinearEquiv.det σ = 1 := MonoidHom.mem_ker.mp hσ.2
  rw [hσl', det_prodSym] at hdet
  have hev := (neg_one_pow_eq_one_iff_even cd_neg_one_ne).mp hdet
  obtain ⟨j, hj⟩ := hev
  obtain ⟨i, hi⟩ := hodd
  let f : V →ₗ[F] (Fin l.length → F) :=
    LinearMap.pi fun i => (associated Q).flip (l.get i)
  have hlt : finrank F (Fin l.length → F) < finrank F V := by
    rw [Module.finrank_fin_fun]; omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, ?_⟩
  rw [hσl']
  apply prodSym_apply_of_orth
  intro u hu
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hu
  have := congrFun (LinearMap.mem_ker.mp hx) i
  simpa [f] using this

/-- **Cassels, Ch. 2, Ex. 10 (p. 30).** ($V$ regular of dimension $n$.) If $\sigma \in O(V)$ is a product of
$n$ symmetries, then for every anisotropic $y$ it is a product of $n$ symmetries the first of which is $\tau_y$:
$\sigma = \tau_y \tau_{y_1} \cdots \tau_{y_{n-1}}$. -/
@[kb "cassels1978" "Ch. 2, Ex. 10, p. 30"]
theorem ex10 (hQ : (associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length = finrank F V)
    {y : V} (hy : Q y ≠ 0) :
    ∃ l : List V, ∃ hl : ∀ u ∈ y :: l, Q u ≠ 0,
      σ = ((y :: l).attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length + 1 = finrank F V := by
  obtain ⟨l0, hl0, hσl, hlen⟩ := hσ
  have hσl' : σ = prodSym Q l0 hl0 := hσl
  have hσo : σ ∈ orth Q := hσl' ▸ prodSym_mem_orth Q l0 hl0
  have hτo : symmetry Q y hy ∈ orth Q := symmetry_mem_orth Q hy
  obtain ⟨l1, hl1, hρl, hlen1⟩ :=
    exists_symmetry_prod_eq_length_le Q hQ ((orth Q).mul_mem hτo hσo)
  have hρl' : symmetry Q y hy * σ = prodSym Q l1 hl1 := hρl
  have hd1 := congrArg LinearEquiv.det hρl'
  rw [det_prodSym, map_mul, det_symmetry, hσl', det_prodSym, hlen] at hd1
  have hpow : (-1 : Fˣ) ^ (l1.length + (finrank F V + 1)) = 1 := by
    have he : (-1 : Fˣ) ^ finrank F V * (-1) ^ finrank F V = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [pow_add, ← hd1, pow_succ', mul_mul_mul_comm, he]; simp
  have hev := (neg_one_pow_eq_one_iff_even cd_neg_one_ne).mp hpow
  obtain ⟨j, hj⟩ := hev
  obtain ⟨l2, hl2, h2, h3⟩ := exists_prodSym_pad Q hy (((finrank F V) - 1 - l1.length) / 2) l1 hl1
  have hl'' : ∀ u ∈ y :: l2, Q u ≠ 0 := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hy
    · exact hl2 u hu
  refine ⟨l2, hl'', ?_, by simp [h3]; omega⟩
  show σ = prodSym Q (y :: l2) hl''
  rw [prodSym_cons, h2, ← hρl']
  ext x
  simp [symmetry_symmetry]

/-- **Cassels, Ch. 2, Ex. 11 (i) (p. 31).** Let $T$ be a proper automorph of a regular form in $n$ variables with
symmetric matrix $\Phi$ ($T^{\mathsf T}\Phi T = \Phi$, $\det\Phi \ne 0$, $\det T = 1$), and
$\varphi(\lambda) = \det(T - \lambda I)$. Then $\varphi(\lambda) = (-\lambda)^{n}\varphi(\lambda^{-1})$ for
$\lambda \ne 0$. *Reconstruction:* "proper automorph" and the formula are partly garbled in the machine-read text;
part (ii) ($\varphi(1) = 0$ for odd $n$) requires $\det T = 1$. -/
@[kb "cassels1978" "Ch. 2, Ex. 11 (i), p. 31"]
theorem ex11_i {n : ℕ} (Φ T : Matrix (Fin n) (Fin n) F) (hΦ : Φ.det ≠ 0) (hT : T.transpose * Φ * T = Φ)
    (hdet : T.det = 1) {c : F} (hc : c ≠ 0) :
    (T - c • 1).det = (-c) ^ n * (T - c⁻¹ • 1).det := by
  have hmat : (T.transpose - c • 1) * Φ * T = Φ * ((-c) • (T - c⁻¹ • 1)) := by
    have h1 : (T.transpose - c • 1) * Φ * T = Φ - c • (Φ * T) := by
      rw [Matrix.sub_mul, Matrix.sub_mul, hT]
      simp
    have h2 : Φ * ((-c) • (T - c⁻¹ • 1)) = -c • (Φ * T) + Φ := by
      rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul,
        neg_mul, mul_inv_cancel₀ hc]
      simp [sub_eq_add_neg, add_comm]
    rw [h1, h2, neg_smul]
    abel
  have hd := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, hdet, mul_one] at hd
  have hT' : (T.transpose - c • 1).det = (T - c • 1).det := by
    rw [← Matrix.det_transpose (T - c • 1)]
    simp
  rw [hT'] at hd
  have : Φ.det * ((T - c • 1).det - (-c) ^ n * (T - c⁻¹ • 1).det) = 0 := by
    simp only [Fintype.card_fin] at hd
    linear_combination hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hΦ)

/-- **Cassels, Ch. 2, Ex. 11 (ii) (p. 31).** In the situation of (i), if $n$ is odd then $\varphi(1) = 0$, i.e. $T$
has the eigenvalue $1$ (another solution of Ex. 9). -/
@[kb "cassels1978" "Ch. 2, Ex. 11 (ii), p. 31"]
theorem ex11_ii {n : ℕ} (Φ T : Matrix (Fin n) (Fin n) F) (hΦ : Φ.det ≠ 0) (hT : T.transpose * Φ * T = Φ)
    (hdet : T.det = 1) (hn : Odd n) : (T - 1).det = 0 := by
  have h := ex11_i Φ T hΦ hT hdet (c := 1) one_ne_zero
  rw [inv_one, one_smul, hn.neg_pow, one_pow] at h
  have h2 : (2 : F) * (T - 1).det = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (Invertible.ne_zero (2 : F))

/-- **Cassels, Ch. 2, Ex. 12 (p. 31).** The group of invertible $n \times n$ matrices over the field of $p$ elements
has order $(p^{n} - 1)(p^{n} - p) \cdots (p^{n} - p^{n-1})$. -/
@[kb "cassels1978" "Ch. 2, Ex. 12, p. 31"]
theorem ex12 (p n : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) = ∏ i ∈ Finset.range n, (p ^ n - p ^ i) := by
  have : Fintype (ZMod p) := ZMod.fintype p
  rw [Matrix.card_GL_field, ZMod.card]
  exact Fin.prod_univ_eq_prod_range (fun i => p ^ n - p ^ i) n

/-- **Cassels, Ch. 2, Ex. 18 (p. 33).** $\langle a\rangle + \langle -a\rangle = 0$ in $W(k)$ for every
$a \in k^{\times}$. -/
@[kb "cassels1978" "Ch. 2, Ex. 18, p. 33"]
theorem ex18 (a : Fˣ) : toW F (toG F (unary F a)) + toW F (toG F (unary F (-a))) = 0 := by
  rw [← map_add, ← map_add, ← star_unary, unary_add_star, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_zmultiples _

end QuadFormsKB.Cassels.Ch2Ex
