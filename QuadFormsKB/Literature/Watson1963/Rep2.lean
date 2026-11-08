/-
# Watson (1963): representations over $\mathbb Z_2$

Tools for the local representations at $p = 2$ in Watson's Lemma 2. `Rep2 G φ` says that the form $G$ over
$\mathbb Z_2$ represents $\varphi$: $G(M\vec y) = \varphi(\vec y)$ for a matrix $M$ over $\mathbb Z_2$.

* basic closure properties (`Rep2.trans`, `Rep2.of_isometricGL`, `rep2_orthSum`: orthogonal pieces combine);
* `repOver_of_rep2`: the bridge to `RepOver ℤ_[2]` for integral forms;
* `rep2_of_compMat_odd`: an integral matrix $T$ of odd determinant with $\varphi \circ T = X$ makes $X$ represent
  $\varphi$ over $\mathbb Z_2$ (used with `ProbeDecomp.lean`);
* values of even unimodular forms over $\mathbb Z_2$ (`exists_eval_eq_unit`: rank $\ge 2$ represents every unit,
  through $A = x^2 + xy + y^2$ and Hensel's lemma in the form `isSquare_iff_dvd_eight`; `exists_orth_pair`: rank
  $\ge 4$ has orthogonal vectors with values $a$ (any) and $c$ (a unit)).
-/
import QuadFormsKB.Literature.Watson1963.Decomp2
import QuadFormsKB.Literature.Watson1963.ProbeDecomp

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {N v : ℕ}

/-! ### Representations -/

/-- **Representation over $\mathbb Z_2$:** $G(M\vec y) = \varphi(\vec y)$ for an $N \times v$ matrix $M$ over
$\mathbb Z_2$. Arguments: the forms `G` (in $N$ variables) and `φ` (in $v$ variables) over $\mathbb Z_2$. -/
def Rep2 (G : QuadForm ℤ_[2] N) (φ : QuadForm ℤ_[2] v) : Prop :=
  ∃ M : Matrix (Fin N) (Fin v) ℤ_[2], ∀ y, G.eval (M *ᵥ y) = φ.eval y

theorem Rep2.trans {w : ℕ} {G : QuadForm ℤ_[2] N} {φ : QuadForm ℤ_[2] v} {χ : QuadForm ℤ_[2] w}
    (h1 : Rep2 G φ) (h2 : Rep2 φ χ) : Rep2 G χ := by
  obtain ⟨M, hM⟩ := h1
  obtain ⟨M', hM'⟩ := h2
  exact ⟨M * M', fun y => by rw [← mulVec_mulVec, hM, hM']⟩

theorem Rep2.of_isometricGL {G G' : QuadForm ℤ_[2] N} (h : IsometricGL G G') : Rep2 G G' := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T.val, hT⟩

theorem Rep2.compMat (G : QuadForm ℤ_[2] N) (X : Matrix (Fin N) (Fin v) ℤ_[2]) : Rep2 G (G.compMat X) :=
  ⟨X, fun y => (QuadForm.eval_compMat G X y).symm⟩

theorem Rep2.congr {G : QuadForm ℤ_[2] N} {φ φ' : QuadForm ℤ_[2] v} (h : Rep2 G φ)
    (he : ∀ y, φ.eval y = φ'.eval y) : Rep2 G φ' := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun y => by rw [hM, he]⟩

/-- Helper: a representation preserves the polar form. -/
theorem dot_of_rep {G : QuadForm ℤ_[2] N} {φ : QuadForm ℤ_[2] v} {M : Matrix (Fin N) (Fin v) ℤ_[2]}
    (hM : ∀ y, G.eval (M *ᵥ y) = φ.eval y) (y z : Fin v → ℤ_[2]) :
    (M *ᵥ y) ⬝ᵥ (G.hessian *ᵥ (M *ᵥ z)) = y ⬝ᵥ (φ.hessian *ᵥ z) := by
  rw [← QuadForm.eval_polar, ← QuadForm.eval_polar, ← mulVec_add, hM, hM, hM]

/-- Helper: the matrix with columns those of $M_1$ followed by those of $M_2$. -/
def appendCols {a b : ℕ} (M₁ : Matrix (Fin N) (Fin a) ℤ_[2]) (M₂ : Matrix (Fin N) (Fin b) ℤ_[2]) :
    Matrix (Fin N) (Fin (a + b)) ℤ_[2] :=
  Matrix.of fun r c => Fin.append (fun i => M₁ r i) (fun i => M₂ r i) c

theorem appendCols_mulVec {a b : ℕ} (M₁ : Matrix (Fin N) (Fin a) ℤ_[2]) (M₂ : Matrix (Fin N) (Fin b) ℤ_[2])
    (x : Fin (a + b) → ℤ_[2]) :
    appendCols M₁ M₂ *ᵥ x = M₁ *ᵥ (fun i => x (Fin.castAdd b i)) + M₂ *ᵥ (fun i => x (Fin.natAdd a i)) := by
  ext r
  simp [appendCols, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- **Orthogonal pieces combine:** if $G$ represents $A$ by $M_1$ and $B$ by $M_2$, and the columns of $M_1$ and $M_2$
are orthogonal, then $G$ represents $A \perp B$. -/
theorem rep2_orthSum {a b : ℕ} {G : QuadForm ℤ_[2] N} {A : QuadForm ℤ_[2] a} {B : QuadForm ℤ_[2] b}
    (M₁ : Matrix (Fin N) (Fin a) ℤ_[2]) (M₂ : Matrix (Fin N) (Fin b) ℤ_[2])
    (h₁ : ∀ y, G.eval (M₁ *ᵥ y) = A.eval y) (h₂ : ∀ y, G.eval (M₂ *ᵥ y) = B.eval y)
    (horth : ∀ y z, (M₁ *ᵥ y) ⬝ᵥ (G.hessian *ᵥ (M₂ *ᵥ z)) = 0) : Rep2 G (QuadForm.orthSum A B) := by
  refine ⟨appendCols M₁ M₂, fun x => ?_⟩
  rw [appendCols_mulVec]
  have hpol := QuadForm.eval_polar G (M₁ *ᵥ (fun i => x (Fin.castAdd b i))) (M₂ *ᵥ (fun i => x (Fin.natAdd a i)))
  rw [horth, h₁, h₂] at hpol
  show _ = (QuadForm.orthSum A B).evalIn ℤ_[2] x
  rw [QuadForm.evalIn_orthSum]
  show _ = A.eval _ + B.eval _
  linear_combination hpol

/-- **A value gives a unary representation:** if $G(x) = c$ then $G$ represents $\langle c\rangle$. -/
theorem rep2_diag_one {G : QuadForm ℤ_[2] N} {c : ℤ_[2]} (x : Fin N → ℤ_[2]) (hx : G.eval x = c) :
    Rep2 G (QuadForm.diag ![c]) := by
  refine ⟨Matrix.of fun r _ => x r, fun y => ?_⟩
  have : (Matrix.of fun r (_ : Fin 1) => x r) *ᵥ y = y 0 • x := by
    ext r; simp [mulVec, dotProduct, mul_comm]
  rw [this, eval_smul_sq, hx, eval_diag']
  simp [mul_comm]

/-- **The bridge to `RepOver`:** for integral forms, a representation over $\mathbb Z_2$ of the base changes is a
`RepOver ℤ_[2]`. -/
theorem repOver_of_rep2 {n : ℕ} {f : QuadForm ℤ n} {φ : QuadForm ℤ v}
    (h : Rep2 (f.map (Int.castRingHom ℤ_[2])) (φ.map (Int.castRingHom ℤ_[2]))) : RepOver ℤ_[2] f φ := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun y => by rw [← eval_map_padic, ← eval_map_padic]; exact hM y⟩

theorem rep2_of_repOver {n : ℕ} {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : RepOver ℤ_[2] f φ) :
    Rep2 (f.map (Int.castRingHom ℤ_[2])) (φ.map (Int.castRingHom ℤ_[2])) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun y => by rw [eval_map_padic, eval_map_padic]; exact hM y⟩

/-- Helper: base change of an orthogonal sum, on values. -/
theorem eval_map_orthSum {a b : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (y : Fin (a + b) → ℤ_[2]) :
    ((QuadForm.orthSum A B).map (Int.castRingHom ℤ_[2])).eval y =
      (QuadForm.orthSum (A.map (Int.castRingHom ℤ_[2])) (B.map (Int.castRingHom ℤ_[2]))).eval y := by
  rw [eval_map_padic]
  show _ = (QuadForm.orthSum _ _).evalIn ℤ_[2] y
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum]
  show _ = (A.map _).eval _ + (B.map _).eval _
  rw [eval_map_padic, eval_map_padic]

/-- **Odd-index sublattices over $\mathbb Z_2$:** if $T$ is an integral matrix with odd determinant and
$\varphi \circ T = X$, then $X$ represents $\varphi$ over $\mathbb Z_2$ (by $T^{-1}$). -/
theorem rep2_of_compMat_odd {φ X : QuadForm ℤ v} (T : Matrix (Fin v) (Fin v) ℤ) (hT : Odd T.det)
    (h : φ.compMat T = X) : Rep2 (X.map (Int.castRingHom ℤ_[2])) (φ.map (Int.castRingHom ℤ_[2])) := by
  set Tq := T.map (Int.castRingHom ℤ_[2])
  have hTq : IsUnit Tq.det := by
    have : Tq.det = ((T.det : ℤ) : ℤ_[2]) := (RingHom.map_det (Int.castRingHom ℤ_[2]) T).symm
    rw [this]
    exact isUnit_intCast_two (Int.not_even_iff_odd.mpr hT ∘ fun h2 => even_iff_two_dvd.mpr h2)
  have hval : ∀ z, (X.map (Int.castRingHom ℤ_[2])).eval z = (φ.map (Int.castRingHom ℤ_[2])).eval (Tq *ᵥ z) := by
    intro z
    rw [← h, ← QuadForm.map_compMat, QuadForm.eval_compMat]
  refine ⟨Tq⁻¹, fun y => ?_⟩
  rw [hval, mulVec_mulVec, Matrix.mul_nonsing_inv _ hTq, one_mulVec]

/-! ### Values of even unimodular forms over $\mathbb Z_2$ -/

/-- **$A = x^2 + xy + y^2$ represents every unit of $\mathbb Z_2$** ($t^2 + t + 1 = u$ with $(2t+1)^2 = 4u - 3$, a
square as $4u - 3 \equiv 1 \pmod 8$). -/
theorem quadA_represents_unit {u : ℤ_[2]} (hu : IsUnit u) : ∃ x, (quadA : QuadForm ℤ_[2] 2).eval x = u := by
  have h4u : IsUnit (4 * u - 3) := by
    apply isUnit_of_toZMod_ne_zero
    have h2 : PadicInt.toZMod (u - 1) = 0 := toZMod_eq_zero_of_two_dvd (Composition.two_dvd_sub_one_of_isUnit hu)
    have : PadicInt.toZMod (4 * u - 3) = PadicInt.toZMod (u - 1) * 4 + 1 := by
      rw [show (4 * u - 3 : ℤ_[2]) = (u - 1) * 4 + 1 by ring, map_add, map_mul, map_one, map_ofNat]
    rw [this, h2]; decide
  have hsq : IsSquare (4 * u - 3) := by
    have h8 : (8 : ℤ_[2]) ∣ (4 * u - 3) - 1 := by
      obtain ⟨c, hc⟩ := Composition.two_dvd_sub_one_of_isUnit hu
      exact ⟨c, by linear_combination 4 * hc⟩
    have h4 : (4 : ℤ_[2]) ∣ (4 * u - 3) - 1 := ⟨u - 1, by ring⟩
    exact (isSquare_iff_dvd_eight h4u h4).2 h8
  obtain ⟨s, hs⟩ := hsq
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ h4u)
  obtain ⟨t, ht⟩ := Composition.two_dvd_sub_one_of_isUnit hsu
  refine ⟨![t, 1], ?_⟩
  unfold quadA
  rw [Composition.bq_eval]
  have : s = 2 * t + 1 := by linear_combination ht
  rw [this] at hs
  have h4 : (4 : ℤ_[2]) * (t ^ 2 + t + 1 - u) = 0 := by linear_combination -hs
  have h40 : (4 : ℤ_[2]) ≠ 0 := by norm_num
  have := (mul_eq_zero.1 h4).resolve_left h40
  linear_combination this

/-- Helper: the value of an orthogonal sum at a concatenated vector. -/
theorem eval_orthSum_append {R : Type*} [CommRing R] {a b : ℕ} (A : QuadForm R a) (B : QuadForm R b)
    (x : Fin a → R) (y : Fin b → R) : (QuadForm.orthSum A B).eval (Fin.append x y) = A.eval x + B.eval y := by
  show (QuadForm.orthSum A B).evalIn R _ = _
  rw [QuadForm.evalIn_orthSum]
  simp only [Fin.append_left, Fin.append_right]

theorem eval_zero_vec {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) : Q.eval 0 = 0 := by
  simp [QuadForm.eval, QuadForm.evalIn]

theorem hypPlane_eval (s t : ℤ_[2]) : (hypPlane : QuadForm ℤ_[2] 2).eval ![s, t] = s * t := by
  unfold hypPlane; rw [Composition.bq_eval]; ring

/-- Helper: orthogonality from additivity of values. -/
theorem dot_eq_zero_of_eval_add {R : Type*} [CommRing R] {n : ℕ} (Q : QuadForm R n) (x y : Fin n → R)
    (h : Q.eval (x + y) = Q.eval x + Q.eval y) : x ⬝ᵥ (Q.hessian *ᵥ y) = 0 := by
  rw [← QuadForm.eval_polar, h]; ring

theorem append_add_append {R : Type*} [AddCommMonoid R] {a b : ℕ} (x x' : Fin a → R) (y y' : Fin b → R) :
    Fin.append x y + Fin.append x' y' = Fin.append (x + x') (y + y') := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- **An even unimodular form of rank $2k \ge 2$ over $\mathbb Z_2$ represents every unit** (classification:
$H^k$ or $H^{k-1} \perp A$; use the last binary block). -/
theorem exists_eval_eq_unit {k : ℕ} (V : QuadForm ℤ_[2] (2 * k)) (hV : IsUnit V.hessian.det) (hk : 1 ≤ k)
    {u : ℤ_[2]} (hu : IsUnit u) : ∃ x, V.eval x = u := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases even_unimodular_classification V hV with ⟨-, ⟨T, hT⟩⟩ | ⟨-, -, ⟨T, hT⟩⟩
  · refine ⟨T.val *ᵥ Fin.append (0 : Fin (2 * j) → ℤ_[2]) ![1, u], ?_⟩
    rw [hT]
    show (QuadForm.orthSum (hypSum j) hypPlane).eval _ = u
    rw [eval_orthSum_append, hypPlane_eval, eval_zero_vec]; ring
  · obtain ⟨y, hy⟩ := quadA_represents_unit hu
    refine ⟨T.val *ᵥ Fin.append (0 : Fin (2 * j) → ℤ_[2]) y, ?_⟩
    rw [hT]
    show (QuadForm.orthSum (hypSum j) quadA).eval _ = u
    rw [eval_orthSum_append, hy, eval_zero_vec, zero_add]

/-- **An even unimodular form of rank $2k \ge 4$ over $\mathbb Z_2$ has orthogonal vectors with values $a$ (any) and
$c$ (a unit)** (a hyperbolic plane gives $a$; the last binary block gives $c$). -/
theorem exists_orth_pair {k : ℕ} (V : QuadForm ℤ_[2] (2 * k)) (hV : IsUnit V.hessian.det) (hk : 2 ≤ k)
    (a : ℤ_[2]) {c : ℤ_[2]} (hc : IsUnit c) :
    ∃ x y, V.eval x = a ∧ V.eval y = c ∧ x ⬝ᵥ (V.hessian *ᵥ y) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have key : ∀ (B : QuadForm ℤ_[2] 2) (y₀ : Fin 2 → ℤ_[2]), B.eval y₀ = c →
      ∀ (W : QuadForm ℤ_[2] (2 * (j + 2))), W = QuadForm.orthSum (QuadForm.orthSum (hypSum j) hypPlane) B →
      IsometricGL V W → ∃ x y, V.eval x = a ∧ V.eval y = c ∧ x ⬝ᵥ (V.hessian *ᵥ y) = 0 := by
    intro B y₀ hy₀ W hW ⟨T, hT⟩
    set x₁ : Fin (2 * (j + 2)) → ℤ_[2] := Fin.append (Fin.append (0 : Fin (2 * j) → ℤ_[2]) ![1, a]) 0
    set y₁ : Fin (2 * (j + 2)) → ℤ_[2] := Fin.append (0 : Fin (2 * j + 2) → ℤ_[2]) y₀
    have hx : W.eval x₁ = a := by
      rw [hW, eval_orthSum_append, eval_orthSum_append, hypPlane_eval, eval_zero_vec, eval_zero_vec]; ring
    have hy : W.eval y₁ = c := by
      rw [hW, eval_orthSum_append, hy₀, eval_zero_vec, zero_add]
    have hxy : W.eval (x₁ + y₁) = W.eval x₁ + W.eval y₁ := by
      have : x₁ + y₁ = Fin.append (Fin.append (0 : Fin (2 * j) → ℤ_[2]) ![1, a]) y₀ := by
        simp only [x₁, y₁]
        rw [append_add_append]
        simp
      rw [this, hx, hy, hW, eval_orthSum_append, eval_orthSum_append, hypPlane_eval, eval_zero_vec, hy₀]; ring
    refine ⟨T.val *ᵥ x₁, T.val *ᵥ y₁, by rw [hT, hx], by rw [hT, hy], ?_⟩
    rw [dot_of_rep hT]
    exact dot_eq_zero_of_eval_add W x₁ y₁ hxy
  rcases even_unimodular_classification V hV with ⟨-, hiso⟩ | ⟨-, -, hiso⟩
  · exact key hypPlane ![1, c] (by rw [hypPlane_eval]; ring) _ rfl hiso
  · obtain ⟨y₀, hy₀⟩ := quadA_represents_unit hc
    exact key quadA y₀ hy₀ _ rfl hiso

end QuadFormsKB.Watson1963
