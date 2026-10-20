/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.LocalOrbital
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.Tamagawa.OrbitCount
import QuadFormsKB.Tamagawa.OrthFq

/-!
# Self-densities of ternary lattices $\langle m\rangle\perp T$ with $T$ unimodular, at every prime

**Layer:** a complete discrete valuation ring $R$ with finite residue field (uniformizer $\pi$, any residue characteristic,
dyadic included), e.g. $\mathfrak o_v$.

**The frame lemma.** Let $T$ be a binary form with $\det H_T \in R^\times$ and $Q = \langle m\rangle\perp T$ ($m \ne 0$). Then
$$\beta_\pi(Q, Q) = \beta_\pi(Q, T)\cdot\beta_\pi(\langle m\rangle, \langle m\rangle)\qquad(\texttt{localDensityForm\_frame}).$$
*Proof.* Count $O(Q \bmod \pi^k)$ by the image of the frame $(e_1, e_2)$ (orbit–stabilizer, `card_compMat_eq_frameOrbit_mul`).
The stabilizer is $\{\mathrm{diag}(x, 1, 1) : mx^2 = m\}$ because $H_T$ is invertible (`stabFrameEquiv`). The orbit is every
representation of $T$ mod $\pi^k$: such a representation lifts to an exact one (Hensel with $d = 0$, `newton_lift`), and an exact
representation $Y = (y_1, y_2)$ is the frame of an exact isometry (`exists_isometry_frame`): $c = Hy_1\times Hy_2$ is orthogonal to
$y_1, y_2$, $\det(c\,|\,Y) = (Hy_1\times Hy_2)\cdot(y_1\times y_2) = \det H_T$ (Binet–Cauchy), and comparing $\det$ of Hessians gives
$Q(c) = m\,(\det H_T)^2$, so $(c/\det H_T\,|\,Y)$ is an isometry. No Witt theorem and no Jordan theory are used.

**Proves**
* `card_compMat_eq_frameOrbit_mul`, `stabFrameEquiv`, `exists_isometry_frame`, `repCountForm_frame`, **`localDensityForm_frame`**;
* **`localDensityForm_frame_dyadic`**: if $\pi \mid 2$ (residue characteristic $2$) and $m$ is a unit,
  $\beta_\pi(Q, T) = 1 - q^{-2}$, so $\beta_\pi(Q, Q) = 2q^{e}(1 - q^{-2})$, $e = \mathrm{ord}_\pi 2$; this is the self-density of
  $\mathfrak{sl}_2(\mathfrak o)$ with $\det$ at a dyadic prime;
* **`localDensityForm_smul_pi`**: $\beta_\pi(\pi Q, \pi Q) = q^{n(n+1)/2}\beta_\pi(Q, Q)$;
* **`localDensityForm_odd_ram`**: at $\pi \nmid 2$, for units $u_0, u_1, u_2$ with $\langle\bar u_1, \bar u_2\rangle$ anisotropic over the
  residue field, $\beta_\pi(\langle u_0, \pi u_1, \pi u_2\rangle) = 4q^2(q+1)$.

Sources: Kitaoka 1993, §5.6 [unverified] (densities); the counting is elementary. Indices are 0-based.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

/-! ### Orbit–stabilizer for frames -/

section Frame

variable {A : Type*} [CommRing A] {N r : ℕ}

/-- The orbit of a frame $Y_0$ under $\{X : Q\circ X = Q\}$. -/
def frameOrbit (Q : QuadForm A N) (Y₀ : Matrix (Fin N) (Fin r) A) : Type _ :=
  {Y : Matrix (Fin N) (Fin r) A // ∃ X : Matrix (Fin N) (Fin N) A, Q.compMat X = Q ∧ X * Y₀ = Y}

/-- **Orbit–stabilizer for frames:** if every isometry is invertible, $|O(Q)| = |O(Q)\,Y_0|\cdot|\mathrm{Stab}(Y_0)|$. -/
theorem card_compMat_eq_frameOrbit_mul [Finite A] (Q : QuadForm A N)
    (hinv : ∀ X : Matrix (Fin N) (Fin N) A, Q.compMat X = Q → IsUnit X.det) (Y₀ : Matrix (Fin N) (Fin r) A) :
    Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q} =
      Nat.card (frameOrbit Q Y₀) * Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X * Y₀ = Y₀} := by
  classical
  let fib : frameOrbit Q Y₀ → Type _ := fun Y => {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X * Y₀ = Y.1}
  let e : {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q} ≃ Σ Y : frameOrbit Q Y₀, fib Y :=
    { toFun := fun X => ⟨⟨X.1 * Y₀, X.1, X.2, rfl⟩, ⟨X.1, X.2, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1⟩
      left_inv := fun X => rfl
      right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2.2) rfl }
  have hfib : ∀ Y : frameOrbit Q Y₀, Nat.card (fib Y) =
      Nat.card {X : Matrix (Fin N) (Fin N) A // Q.compMat X = Q ∧ X * Y₀ = Y₀} := by
    intro Y
    obtain ⟨Z, hZ, hZY⟩ := Y.2
    have hu := hinv Z hZ
    have hZi : Q.compMat Z⁻¹ = Q := by
      conv_lhs => rw [← hZ]
      rw [compMat_mul, mul_nonsing_inv _ hu, compMat_one]
    have hinvY : Z⁻¹ * Y.1 = Y₀ := by
      rw [← hZY, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    refine Nat.card_congr
      { toFun := fun X => ⟨Z⁻¹ * X.1, by rw [← compMat_mul, hZi, X.2.1], by
          rw [Matrix.mul_assoc, X.2.2, hinvY]⟩
        invFun := fun X => ⟨Z * X.1, by rw [← compMat_mul, hZ, X.2.1], by
          rw [Matrix.mul_assoc, X.2.2, hZY]⟩
        left_inv := fun X => Subtype.ext (by
          show Z * (Z⁻¹ * X.1) = X.1
          rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul])
        right_inv := fun X => Subtype.ext (by
          show Z⁻¹ * (Z * X.1) = X.1
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]) }
  have : Finite (frameOrbit Q Y₀) := Subtype.finite
  have : ∀ Y, Finite (fib Y) := fun Y => Subtype.finite
  let _ : Fintype (frameOrbit Q Y₀) := Fintype.ofFinite _
  let _ : ∀ Y, Fintype (fib Y) := fun Y => Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card] at hfib ⊢
  rw [Finset.sum_congr rfl fun Y _ => hfib Y, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Frame

/-! ### The frame $(e_1, \dots, e_n)$ of $\langle m\rangle\perp T$ and its stabilizer -/

section SplitFrame

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The frame $(e_1, \dots, e_n)$ in $A^{n+1}$: column $j$ is $e_{j+1}$. -/
def frameMat (A : Type*) [CommRing A] (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) A :=
  Matrix.of fun i j => if i = j.succ then 1 else 0

theorem frameMat_map {B : Type*} [CommRing B] (f : A →+* B) : (frameMat A n).map f = frameMat B n := by
  ext i j; simp [frameMat, apply_ite f]

theorem mul_frameMat_apply (X : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (i : Fin (n + 1)) (j : Fin n) :
    (X * frameMat A n) i j = X i j.succ := by
  simp [frameMat, Matrix.mul_apply]

theorem frameMat_mulVec (x : Fin n → A) : frameMat A n *ᵥ x = Fin.cons 0 x := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [frameMat, mulVec, dotProduct, of_apply, ite_mul, one_mul, zero_mul, Fin.cons_zero]
    exact Finset.sum_eq_zero fun i _ => if_neg (Fin.succ_ne_zero i).symm
  · simp [frameMat, mulVec, dotProduct, Fin.succ_inj]

/-- $(\langle a\rangle\perp T)\circ(e_1,\dots,e_n) = T$. -/
theorem splitForm_compMat_frameMat (a : A) (T : QuadForm A n) : (splitForm a T).compMat (frameMat A n) = T :=
  eq_of_eval_eq fun x => by
    rw [eval_compMat, frameMat_mulVec, eval_splitForm_cons]; ring

theorem eval_splitForm_cornerMat_one (a x : A) (T : QuadForm A n) :
    (splitForm a T).compMat (cornerMat x 1) = splitForm (a * x * x) T :=
  eq_of_eval_eq fun y => by
    rw [eval_compMat, ← Fin.cons_self_tail y, cornerMat_mulVec, one_mulVec, eval_splitForm_cons, eval_splitForm_cons]
    ring

/-- The $(0, j+1)$ coefficient of $Q\circ X$ for $Q = \langle a\rangle\perp T$ when column $j+1$ of $X$ is $e_{j+1}$:
it is $(s\,H_T)_j$, $s$ the lower part of the first column. -/
theorem compMat_coeff_zero_succ (a : A) (T : QuadForm A n) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (hX : ∀ i j, X i j.succ = frameMat A n i j) (j : Fin n) :
    ((splitForm a T).compMat X).coeff 0 j.succ = ((fun i => X i.succ 0) ᵥ* T.hessian) j := by
  rw [compMat_coeff, if_pos (Fin.zero_le _), if_neg (Fin.succ_ne_zero j).symm, hessian_splitForm]
  have hcol : (fun l => X l j.succ) = Pi.single j.succ 1 := by
    ext l; rw [hX]; simp [frameMat, Pi.single_apply]
  rw [hcol, mulVec_single_one, dotProduct, Fin.sum_univ_succ]
  simp [vecMul, dotProduct, Matrix.col]

/-- **The stabilizer of the frame** of $\langle a\rangle\perp T$ with $\det H_T$ a unit: $X = \mathrm{diag}(x, 1, \dots, 1)$ with
$ax^2 = a$. -/
def stabFrameEquiv (a : A) (T : QuadForm A n) (hT : IsUnit T.hessian.det) :
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) A // (splitForm a T).compMat X = splitForm a T ∧
        X * frameMat A n = frameMat A n} ≃ {x : A // a * x * x = a} where
  toFun X := ⟨X.1 0 0, by
    obtain ⟨hQ, hF⟩ := X.2
    have hc : ∀ (i : Fin (n + 1)) (j : Fin n), X.1 i j.succ = frameMat A n i j := fun i j => by
      rw [← mul_frameMat_apply X.1 i j, hF]
    have hs : (fun i : Fin n => X.1 i.succ 0) = 0 := by
      have h0 : (fun i : Fin n => X.1 i.succ 0) ᵥ* T.hessian = 0 := by
        ext j
        rw [← compMat_coeff_zero_succ a T X.1 hc j, hQ]
        simp [splitForm_coeff]
      have := congrArg (· ᵥ* T.hessian⁻¹) h0
      simpa [vecMul_vecMul, mul_nonsing_inv _ hT] using this
    have h00 := congrArg (fun S : QuadForm A (n + 1) => S.coeff 0 0) hQ
    simp only [compMat_coeff, le_refl, if_true] at h00
    have hcol : (fun l => X.1 l 0) = Fin.cons (X.1 0 0) 0 := by
      ext l; refine Fin.cases rfl (fun i => ?_) l
      simpa using congrFun hs i
    rw [hcol, eval_splitForm_cons] at h00
    simpa [splitForm_coeff, QuadForm.eval, QuadForm.evalIn] using h00⟩
  invFun x := ⟨cornerMat x.1 1, by rw [eval_splitForm_cornerMat_one, x.2], by
    ext i j; rw [mul_frameMat_apply]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [frameMat, (Fin.succ_ne_zero j).symm]
    · simp [frameMat, Matrix.one_apply, Fin.succ_inj]⟩
  left_inv X := by
    obtain ⟨hQ, hF⟩ := X.2
    have hc : ∀ (i : Fin (n + 1)) (j : Fin n), X.1 i j.succ = frameMat A n i j := fun i j => by
      rw [← mul_frameMat_apply X.1 i j, hF]
    have hs : (fun i : Fin n => X.1 i.succ 0) = 0 := by
      have h0 : (fun i : Fin n => X.1 i.succ 0) ᵥ* T.hessian = 0 := by
        ext j
        rw [← compMat_coeff_zero_succ a T X.1 hc j, hQ]
        simp [splitForm_coeff]
      have := congrArg (· ᵥ* T.hessian⁻¹) h0
      simpa [vecMul_vecMul, mul_nonsing_inv _ hT] using this
    apply Subtype.ext
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rw [hc]; simp [frameMat, (Fin.succ_ne_zero j).symm]
    · simpa using (congrFun hs i).symm
    · rw [hc]; simp [frameMat, Matrix.one_apply, Fin.succ_inj]
  right_inv x := rfl

end SplitFrame

/-! ### Exact transitivity on representations of a unimodular binary $T$ -/

section Transitive

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Every exact representation of $T$ by $\langle m\rangle\perp T$ is the frame of an isometry** ($\det H_T$ a unit, $2 \ne 0$):
with $c = Hy_1\times Hy_2$, the matrix $Z = (c\,|\,Y)$ has $\det Z = \det H_T$ (Binet–Cauchy), $Q\circ Z = \langle Q(c)\rangle\perp T$,
and comparing determinants of Hessians gives $Q(c) = m(\det H_T)^2$; then $X = Z\,\mathrm{diag}((\det H_T)^{-1}, 1, 1)$. -/
theorem exists_isometry_frame (h2 : (2 : R) ≠ 0) (m : R) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    (Y : Matrix (Fin 3) (Fin 2) R) (hY : (splitForm m T).compMat Y = T) :
    ∃ X : Matrix (Fin 3) (Fin 3) R, (splitForm m T).compMat X = splitForm m T ∧ X * frameMat R 2 = Y := by
  set Q := splitForm m T with hQdef
  set H := Q.hessian with hHdef
  set y0 : Fin 3 → R := fun l => Y l 0 with hy0
  set y1 : Fin 3 → R := fun l => Y l 1 with hy1
  set c : Fin 3 → R := (H *ᵥ y0) ⨯₃ (H *ᵥ y1) with hcdef
  set Z : Matrix (Fin 3) (Fin 3) R := Matrix.of fun l j => Fin.cases (c l) (fun i => Y l i) j with hZdef
  have hG : ∀ i j, (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) = T.hessian i j := fun i j => by
    rw [← transpose_mul_mul_apply, ← hessian_compMat, hY]
  have hc0 : c ⬝ᵥ (H *ᵥ y0) = 0 := by rw [dotProduct_comm]; exact dot_self_cross _ _
  have hc1 : c ⬝ᵥ (H *ᵥ y1) = 0 := by rw [dotProduct_comm]; exact dot_cross_self _ _
  -- the determinant of `Z`
  have hZt : Zᵀ = (![c, y0, y1] : Matrix (Fin 3) (Fin 3) R) := by
    ext i j; fin_cases i <;> rfl
  have hdetZ : Z.det = T.hessian.det := by
    rw [← det_transpose, hZt, ← triple_product_eq_det, hcdef, cross_dot_cross, dotProduct_comm (H *ᵥ y0) y0,
      dotProduct_comm (H *ᵥ y1) y1, dotProduct_comm (H *ᵥ y0) y1, dotProduct_comm (H *ᵥ y1) y0, det_fin_two]
    rw [show y0 ⬝ᵥ (H *ᵥ y0) = T.hessian 0 0 from hG 0 0, show y1 ⬝ᵥ (H *ᵥ y1) = T.hessian 1 1 from hG 1 1,
      show y1 ⬝ᵥ (H *ᵥ y0) = T.hessian 1 0 from hG 1 0, show y0 ⬝ᵥ (H *ᵥ y1) = T.hessian 0 1 from hG 0 1]
    ring
  -- `Q ∘ Z = ⟨Q(c)⟩ ⊥ T`
  have hZv : ∀ t (x : Fin 2 → R), Z *ᵥ (Fin.cons t x : Fin 3 → R) = Y *ᵥ x + t • c := by
    intro t x; ext l
    simp [hZdef, mulVec, dotProduct, Fin.sum_univ_succ]; ring
  have hYx : ∀ x : Fin 2 → R, c ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = 0 := by
    intro x
    have : Y *ᵥ x = x 0 • y0 + x 1 • y1 := by
      ext l; simp [mulVec, dotProduct, Fin.sum_univ_two, hy0, hy1]; ring
    rw [this, mulVec_add, mulVec_smul, mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, hc0, hc1]
    simp
  have hQZ : Q.compMat Z = splitForm (Q.eval c) T := eq_of_eval_eq fun x => by
    rw [eval_compMat, ← Fin.cons_self_tail x, hZv, eval_add_smul', eval_splitForm_cons, ← eval_compMat, hY,
      dotProduct_comm, hYx]
    ring
  -- comparing determinants of Hessians
  have hγ : Q.eval c = m * T.hessian.det ^ 2 := by
    have h1 := congrArg Matrix.det (hessian_compMat Q Z)
    rw [hQZ, det_hessian_splitForm, det_mul, det_mul, det_transpose, hdetZ,
      show Q.hessian.det = 2 * m * T.hessian.det from det_hessian_splitForm m T] at h1
    have hd0 : (2 : R) * T.hessian.det ≠ 0 := mul_ne_zero h2 hT.ne_zero
    apply mul_left_cancel₀ hd0
    linear_combination h1
  -- normalize the first column
  obtain ⟨u, hu⟩ := hT
  refine ⟨Z * cornerMat (↑u⁻¹ : R) 1, ?_, ?_⟩
  · rw [← compMat_mul, hQZ, eval_splitForm_cornerMat_one, hγ, ← hu]
    congr 1
    calc m * (↑u : R) ^ 2 * ↑u⁻¹ * ↑u⁻¹ = m * ((↑u : R) * ↑u⁻¹) ^ 2 := by ring
      _ = m := by rw [Units.mul_inv, one_pow, mul_one]
  · ext i j
    rw [mul_frameMat_apply, Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hZdef, Matrix.one_apply]

end Transitive

/-! ### Rank one -/

section Unary

variable {A : Type*} [CommRing A]

theorem eval_unary (a : A) (y : Fin 1 → A) : (unary a).eval y = a * y 0 * y 0 := by
  simp [QuadForm.eval, QuadForm.evalIn, unary, QuadForm.diag]

theorem unary_compMat (a x : A) : (unary a).compMat (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) A) =
    unary (a * x * x) :=
  eq_of_eval_eq fun y => by
    rw [eval_compMat, eval_unary, eval_unary]
    simp [mulVec, dotProduct]; ring

theorem unary_injective {a b : A} (h : unary a = unary b) : a = b := by
  simpa [unary, QuadForm.diag] using congrArg (fun S : QuadForm A 1 => S.coeff 0 0) h

theorem map_unary {B : Type*} [CommRing B] (f : A →+* B) (a : A) : (unary a).map f = unary (f a) := by
  ext i j; simp [QuadForm.map, unary, QuadForm.diag, Matrix.diagonal_apply]

/-- $\{x : ax^2 = a\} \simeq \{X \in M_1 : \langle a\rangle\circ X = \langle a\rangle\}$. -/
def unaryEquiv (a : A) : {x : A // a * x * x = a} ≃
    {X : Matrix (Fin 1) (Fin 1) A // (unary a).compMat X = unary a} where
  toFun x := ⟨Matrix.of fun _ _ => x.1, by rw [unary_compMat, x.2]⟩
  invFun X := ⟨X.1 0 0, by
    have hX : X.1 = Matrix.of fun _ _ => X.1 0 0 := by
      ext i j; rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; rfl
    have h := X.2
    rw [hX, unary_compMat] at h
    exact unary_injective h⟩
  left_inv x := rfl
  right_inv X := by
    apply Subtype.ext
    ext i j; rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; rfl

end Unary

/-! ### The frame lemma -/

section FrameCount

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The frame count at level $\pi^k$** ($k > d = \mathrm{ord}_\pi\det H_Q$): for $Q = \langle m\rangle\perp T$ with $\det H_T$ a unit,
$A_{\pi^k}(Q, Q) = A_{\pi^k}(Q, T)\cdot A_{\pi^k}(\langle m\rangle, \langle m\rangle)$. -/
theorem repCountForm_frame [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) (m : R) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    {d k : ℕ} (hd : π ^ d ∣ (splitForm m T).hessian.det) (hd' : ¬ π ^ (d + 1) ∣ (splitForm m T).hessian.det)
    (hdk : d < k) :
    repCountForm (splitForm m T) (splitForm m T) π k =
      repCountForm (splitForm m T) T π k * repCountForm (unary m) (unary m) π k := by
  have := finite_quot_pow π hπ k
  have hk : 0 < k := by omega
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  have hsplit : (splitForm m T).map mk = splitForm (mk m) (T.map mk) := map_splitForm _ _ _
  have hTu : IsUnit (T.map mk).hessian.det := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hT.map _
  unfold repCountForm
  rw [card_compMat_eq_frameOrbit_mul _ (fun X hX => isUnit_det_of_compMat_eq _ π hπ d k hd hd' hdk X hX)
    (frameMat _ 2)]
  congr 1
  · unfold frameOrbit
    refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [← compMat_mul, hX, hsplit, splitForm_compMat_frameMat]
    · intro hY
      choose f hf using fun (i : Fin 3) (j : Fin 2) => Ideal.Quotient.mk_surjective (Y i j)
      set Yh : Matrix (Fin 3) (Fin 2) R := Matrix.of f with hYh
      have hYm : Yh.map mk = Y := by ext i j; exact hf i j
      have hx : ∀ p : DVR.UpperIdx 2, π ^ k ∣ DVR.formF (splitForm m T) (fun li => Yh li.1 li.2) p -
          T.coeff p.1.1 p.1.2 := by
        intro p
        have h1 := congrArg (fun S : QuadForm _ 2 => S.coeff p.1.1 p.1.2) hY
        rw [← hYm, map_compMat] at h1
        simp only [QuadForm.map] at h1
        rw [← Ideal.mem_span_singleton]
        exact Ideal.Quotient.eq.mp h1
      obtain ⟨y, hy, hyx⟩ := newton_lift hπ (DVR.formF (splitForm m T)) (DVR.formD (splitForm m T))
        (DVR.formF_add_smul (splitForm m T)) (fun p => T.coeff p.1.1 p.1.2) 0 k (by omega)
        (fun x hx c => DVR.formD_surj (splitForm m T) T π hπ 0 k (by simp)
          (by simpa using dvr_not_dvd_of_isUnit hπ hT) hk x hx c) _ hx
      have hyT : (splitForm m T).compMat (DVR.toMat y) = T := by
        refine ext_upper fun i j hij => ?_
        exact congrFun hy ⟨(i, j), hij⟩
      obtain ⟨X, hX, hXY⟩ := exists_isometry_frame h2 m T hT _ hyT
      refine ⟨X.map mk, by rw [map_compMat, hX], ?_⟩
      rw [← frameMat_map mk, ← Matrix.map_mul, hXY, ← hYm]
      ext i j
      simp only [Matrix.map_apply, DVR.toMat, Matrix.of_apply]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      simpa using hyx (i, j)
  · rw [hsplit, Nat.card_congr (stabFrameEquiv _ _ hTu), map_unary, Nat.card_congr (unaryEquiv _)]

/-- **The frame lemma** (every prime, dyadic included): for $Q = \langle m\rangle\perp T$, $m \ne 0$, $\det H_T$ a unit,
$$\beta_\pi(Q, Q) = \beta_\pi(Q, T)\cdot\beta_\pi(\langle m\rangle, \langle m\rangle).$$ -/
theorem localDensityForm_frame [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {m : R} (hm : m ≠ 0) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) :
    localDensityForm (splitForm m T) (splitForm m T) π =
      localDensityForm (splitForm m T) T π * localDensityForm (unary m) (unary m) π := by
  have hT0 : T.Nondegenerate := hT.ne_zero
  have hQ : (splitForm m T).Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]; exact mul_ne_zero (mul_ne_zero h2 hm) hT0
  have hU : (unary m).Nondegenerate := by
    have : (unary m).hessian.det = 2 * m := by
      simp [hessian, unary, QuadForm.diag, Matrix.det_unique]; ring
    rw [QuadForm.Nondegenerate, this]; exact mul_ne_zero h2 hm
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd π hπ hQ
  have e1 := localDensityForm_eventually_eq (splitForm m T) (splitForm m T) hQ π hπ le_rfl
  have e2 := localDensityForm_eventually_eq (splitForm m T) T hT0 π hπ (by norm_num)
  have e3 := localDensityForm_eventually_eq (unary m) (unary m) hU π hπ le_rfl
  obtain ⟨k, h1, h2', h3, hk⟩ := (e1.and (e2.and (e3.and (Filter.eventually_gt_atTop d)))).exists
  rw [← h1, ← h2', ← h3, repCountForm_frame hπ h2 m T hT hd hd' hk]
  push_cast
  norm_num
  ring

end FrameCount

/-! ### A count over a finite field of characteristic $2$ -/

section CharTwo

variable {K : Type*} [Field K] [Finite K]

theorem sq_bijective_of_two_eq_zero (h2 : (2 : K) = 0) : Function.Bijective (fun x : K => x ^ 2) := by
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have hxy' : x ^ 2 = y ^ 2 := hxy
  have h : (x - y) ^ 2 = 0 := by
    have e : (x - y) ^ 2 = x ^ 2 - y ^ 2 - 2 * y * (x - y) := by ring
    rw [e, hxy', h2]; ring
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

/-- An affine line $\{w \in K^2 : g\cdot w = b\}$, $g \ne 0$, has $|K|$ points. -/
theorem card_dotProduct_eq (g : Fin 2 → K) (hg : g ≠ 0) (b : K) :
    Nat.card {w : Fin 2 → K // g ⬝ᵥ w = b} = Nat.card K := by
  by_cases h0 : g 0 = 0
  · have h1 : g 1 ≠ 0 := fun h1 => hg (by ext i; fin_cases i <;> simp [h0, h1])
    refine Nat.card_congr
      { toFun := fun w => w.1 0
        invFun := fun t => ⟨![t, (b - g 0 * t) / g 1], by
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          field_simp; ring⟩
        left_inv := fun w => Subtype.ext (by
          have hw := w.2
          simp only [dotProduct, Fin.sum_univ_two] at hw
          ext i; fin_cases i
          · rfl
          · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            field_simp; linear_combination (-1 : K) * hw)
        right_inv := fun t => rfl }
  · refine Nat.card_congr
      { toFun := fun w => w.1 1
        invFun := fun t => ⟨![(b - g 1 * t) / g 0, t], by
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          field_simp; ring⟩
        left_inv := fun w => Subtype.ext (by
          have hw := w.2
          simp only [dotProduct, Fin.sum_univ_two] at hw
          ext i; fin_cases i
          · simp only [Fin.zero_eta, Matrix.cons_val_zero]
            field_simp; linear_combination (-1 : K) * hw
          · rfl)
        right_inv := fun t => rfl }

/-- $\#\{(u, w) \in K^2\times K^2 : u^{\mathsf T}Hw = b\} = |K|(|K|^2 - 1)$ for $H$ invertible and $b \ne 0$. -/
theorem card_bil_eq (H : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0) {b : K} (hb : b ≠ 0) :
    Nat.card {p : (Fin 2 → K) × (Fin 2 → K) // p.1 ⬝ᵥ (H *ᵥ p.2) = b} = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun u w => u ⬝ᵥ (H *ᵥ w) = b), Nat.card_sigma]
  have hfib : ∀ u : Fin 2 → K, Nat.card {w : Fin 2 → K // u ⬝ᵥ (H *ᵥ w) = b} = if u = 0 then 0 else Nat.card K := by
    intro u
    split_ifs with hu
    · subst hu
      simp only [zero_dotProduct]
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun w => hb w.2.symm⟩
    · have hg : u ᵥ* H ≠ 0 := by
        intro h0
        apply hu
        have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH
        have := congrArg (· ᵥ* H⁻¹) h0
        simpa [vecMul_vecMul, mul_nonsing_inv _ hHu] using this
      simp_rw [dotProduct_mulVec]
      exact card_dotProduct_eq _ hg b
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.card_eq_fintype_card, mul_comm]

/-- The columns of a $3\times2$ matrix, split as (first row, lower $2\times2$ block). -/
theorem col_eq_cons (Y : Matrix (Fin 3) (Fin 2) K) (j : Fin 2) :
    (fun l => Y l j) = Fin.cons (Y 0 j) (fun i : Fin 2 => Y i.succ j) :=
  (Fin.cons_self_tail _).symm

/-- **The residue count in characteristic $2$:** over a finite field $K$ with $2 = 0$, for $a \ne 0$ and $\det H_T \ne 0$,
$\#\{Y \in M_{3\times2}(K) : (\langle a\rangle\perp T)\circ Y = T\} = |K|(|K|^2 - 1)$. In characteristic $2$ the cross term of
$\langle a\rangle$ vanishes, the first row is determined by the other two (squaring is bijective), and the lower $2\times2$ block
only has to satisfy $B_T(W_0, W_1) = c_{01}(T)$. -/
theorem card_reps_splitForm_char2 (h2 : (2 : K) = 0) {a : K} (ha : a ≠ 0) (T : QuadForm K 2)
    (hT : T.hessian.det ≠ 0) :
    Nat.card {Y : Matrix (Fin 3) (Fin 2) K // (splitForm a T).compMat Y = T} =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  set b := T.coeff 0 1 with hbdef
  have h10 : T.coeff 1 0 = 0 := T.upper (by decide)
  have hb : b ≠ 0 := by
    intro hb0
    apply hT
    rw [det_fin_two]
    simp only [hessian, Matrix.add_apply, Matrix.transpose_apply, h10, ← hbdef, hb0]
    linear_combination (T.coeff 0 0 * T.coeff 1 1 * 2) * h2
  set sqE := Equiv.ofBijective _ (sq_bijective_of_two_eq_zero h2) with hsq
  have hsq_apply : ∀ x, sqE x = x ^ 2 := fun x => rfl
  have hsqs : ∀ x, (sqE.symm x) ^ 2 = x := fun x => by rw [← hsq_apply, Equiv.apply_symm_apply]
  -- the three coefficient conditions
  have hcoef : ∀ Y : Matrix (Fin 3) (Fin 2) K, (splitForm a T).compMat Y = T ↔
      (a * Y 0 0 * Y 0 0 + T.eval (fun i : Fin 2 => Y i.succ 0) = T.coeff 0 0 ∧
       a * Y 0 1 * Y 0 1 + T.eval (fun i : Fin 2 => Y i.succ 1) = T.coeff 1 1 ∧
       (fun i : Fin 2 => Y i.succ 0) ⬝ᵥ (T.hessian *ᵥ fun i : Fin 2 => Y i.succ 1) = b) := by
    intro Y
    have c00 : ((splitForm a T).compMat Y).coeff 0 0 = a * Y 0 0 * Y 0 0 + T.eval (fun i : Fin 2 => Y i.succ 0) := by
      rw [compMat_coeff, if_pos le_rfl, if_pos rfl, col_eq_cons Y 0, eval_splitForm_cons]
    have c11 : ((splitForm a T).compMat Y).coeff 1 1 = a * Y 0 1 * Y 0 1 + T.eval (fun i : Fin 2 => Y i.succ 1) := by
      rw [compMat_coeff, if_pos le_rfl, if_pos rfl, col_eq_cons Y 1, eval_splitForm_cons]
    have c01 : ((splitForm a T).compMat Y).coeff 0 1 =
        (fun i : Fin 2 => Y i.succ 0) ⬝ᵥ (T.hessian *ᵥ fun i : Fin 2 => Y i.succ 1) := by
      rw [compMat_coeff, if_pos (by decide), if_neg (by decide), col_eq_cons Y 0, col_eq_cons Y 1,
        hessian_splitForm, cornerMat_mulVec]
      simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero]
      linear_combination (Y 0 0 * a * Y 0 1) * h2
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · rw [← c00, h]
      · rw [← c11, h]
      · rw [← c01, h]
    · rintro ⟨h0, h1, h01⟩
      refine ext_upper fun i j hij => ?_
      fin_cases i <;> fin_cases j
      · simpa [c00] using h0
      · simpa [c01] using h01
      · exact absurd hij (by decide)
      · simpa [c11] using h1
  set P : (Fin 2 → K) × (Fin 2 → K) → Prop := fun p => p.1 ⬝ᵥ (T.hessian *ᵥ p.2) = b
  let row : (Fin 2 → K) × (Fin 2 → K) → Fin 2 → K := fun p =>
    ![sqE.symm ((T.coeff 0 0 - T.eval p.1) / a), sqE.symm ((T.coeff 1 1 - T.eval p.2) / a)]
  let mkY : (Fin 2 → K) × (Fin 2 → K) → Matrix (Fin 3) (Fin 2) K := fun p =>
    Matrix.of fun i j => Fin.cases (row p j) (fun i' : Fin 2 => if j = 0 then p.1 i' else p.2 i') i
  have hrow0 : ∀ p, a * row p 0 * row p 0 = T.coeff 0 0 - T.eval p.1 := fun p => by
    have := hsqs ((T.coeff 0 0 - T.eval p.1) / a)
    simp only [row, Matrix.cons_val_zero]
    rw [mul_assoc, ← sq, this]; field_simp
  have hrow1 : ∀ p, a * row p 1 * row p 1 = T.coeff 1 1 - T.eval p.2 := fun p => by
    have := hsqs ((T.coeff 1 1 - T.eval p.2) / a)
    simp only [row, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [mul_assoc, ← sq, this]; field_simp
  rw [← card_bil_eq T.hessian hT hb]
  refine Nat.card_congr
    { toFun := fun Y => ⟨((fun i : Fin 2 => Y.1 i.succ 0), (fun i : Fin 2 => Y.1 i.succ 1)), ((hcoef Y.1).1 Y.2).2.2⟩
      invFun := fun p => ⟨mkY p.1, (hcoef _).2 ⟨?_, ?_, ?_⟩⟩
      left_inv := fun Y => ?_
      right_inv := fun p => ?_ }
  · show a * row p.1 0 * row p.1 0 + T.eval p.1.1 = T.coeff 0 0
    rw [hrow0]; ring
  · show a * row p.1 1 * row p.1 1 + T.eval p.1.2 = T.coeff 1 1
    rw [hrow1]; ring
  · simpa [mkY] using p.2
  · obtain ⟨h0, h1, -⟩ := (hcoef Y.1).1 Y.2
    apply Subtype.ext
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [mkY, Matrix.of_apply, Fin.cases_zero]
      fin_cases j
      · simp only [row, Fin.zero_eta, Matrix.cons_val_zero]
        apply sqE.injective
        rw [Equiv.apply_symm_apply, hsq_apply]
        field_simp; linear_combination (-1 : K) * h0
      · simp only [row, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        apply sqE.injective
        rw [Equiv.apply_symm_apply, hsq_apply]
        field_simp; linear_combination (-1 : K) * h1
    · fin_cases j <;> simp [mkY]
  · apply Subtype.ext
    simp [mkY]

end CharTwo

/-! ### The split dyadic self-density -/

section Dyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **$\beta_\pi(\langle m\rangle\perp T, T) = 1 - q^{-2}$ at a dyadic prime** ($\pi \mid 2$, $m$ a unit, $\det H_T$ a unit): the count
mod $\pi$ is $q(q^2 - 1)$ (`card_reps_splitForm_char2`) and the counts are constant from $k = 1$. -/
theorem localDensityForm_splitForm_T_dyadic [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (h2π : π ∣ 2) {m : R} (hm : IsUnit m) (T : QuadForm R 2) (hT : IsUnit T.hessian.det) :
    localDensityForm (splitForm m T) T π = 1 - ((q R : ℝ) ^ 2)⁻¹ := by
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT (by norm_num)]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have hfin := finite_quot_pow π hπ 1
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have h2 : (2 : R ⧸ Ideal.span {π ^ 1}) = 0 := by
    rw [← map_ofNat mk 2, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]; exact h2π
  have hm' : mk m ≠ 0 := (hm.map mk).ne_zero
  have hT' : (T.map mk).hessian.det ≠ 0 := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (hT.map mk).ne_zero
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  unfold repCountForm
  rw [map_splitForm, card_reps_splitForm_char2 h2 hm' _ hT', hcard]
  have hq : (1 : ℕ) ≤ q R := q_pos
  have hq2 : 1 ≤ q R ^ 2 := Nat.one_le_pow _ _ hq
  have hq' : (0 : ℝ) < q R := by exact_mod_cast hq
  rw [Nat.cast_mul, Nat.cast_sub hq2]
  norm_num
  field_simp

/-- **The self-density of $\langle m\rangle\perp T$ at a dyadic prime** ($\pi^e \,\|\, 2$, $m$ a unit, $\det H_T$ a unit):
$$\beta_\pi(\langle m\rangle\perp T, \langle m\rangle\perp T) = 2q^e\,(1 - q^{-2}).$$
For $T = -x_1x_2$, $m = -1$ this is $\mathfrak{sl}_2(\mathfrak o)$ with $\det$, i.e. Siegel's $\alpha = (1 - q^{-2})\,|2|_\pi^{-1}$. -/
theorem localDensityForm_frame_dyadic [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (he1 : 1 ≤ e) {m : R} (hm : IsUnit m) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) :
    localDensityForm (splitForm m T) (splitForm m T) π = 2 * (q R : ℝ) ^ e * (1 - ((q R : ℝ) ^ 2)⁻¹) := by
  have h2π : π ∣ 2 := (dvd_pow_self π (by omega)).trans he.1
  rw [localDensityForm_frame hπ h20 hm.ne_zero T hT, localDensityForm_splitForm_T_dyadic hπ h2π hm T hT,
    localDensityForm_self_unary π hπ e he hm]
  ring

end Dyadic

/-! ### Scaling by $\pi$ -/

section Scale

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

theorem eval_of_coeff_mul {A : Type*} [CommRing A] (c : A) {Q Q' : QuadForm A n}
    (hQ' : ∀ i j, Q'.coeff i j = c * Q.coeff i j) (x : Fin n → A) : Q'.eval x = c * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, hQ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem compMat_coeff_of_coeff_mul {A : Type*} [CommRing A] (c : A) {Q Q' : QuadForm A n}
    (hQ' : ∀ i j, Q'.coeff i j = c * Q.coeff i j) {r : ℕ} (X : Matrix (Fin n) (Fin r) A) (i j : Fin r) :
    (Q'.compMat X).coeff i j = c * (Q.compMat X).coeff i j := by
  have hH : Q'.hessian = c • Q.hessian := by
    ext a b; simp [hessian, hQ']; ring
  rw [compMat_coeff, compMat_coeff, hH]
  split_ifs
  · exact eval_of_coeff_mul c hQ' _
  · rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  · ring

theorem map_mk_eq_iff {a : R} {r : ℕ} (S S' : QuadForm R r) :
    S.map (Ideal.Quotient.mk (Ideal.span {a})) = S'.map (Ideal.Quotient.mk (Ideal.span {a})) ↔
      ∀ i j, a ∣ S.coeff i j - S'.coeff i j := by
  constructor
  · intro h i j
    have := congrArg (fun U : QuadForm _ r => U.coeff i j) h
    simp only [QuadForm.map, Matrix.map_apply] at this
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)
  · intro h
    ext i j
    simp only [QuadForm.map, Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h i j))

/-- **Counts for $\pi Q$:** $A_{\pi^{k+1}}(\pi Q, \pi Q) = q^{n^2}A_{\pi^k}(Q, Q)$ (the condition only sees $X \bmod \pi^k$). -/
theorem repCountForm_smul_pi [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    {Q Q' : QuadForm R n} (hQ' : ∀ i j, Q'.coeff i j = π * Q.coeff i j) (k : ℕ) :
    repCountForm Q' Q' π (k + 1) = q R ^ (n * n) * repCountForm Q Q π k := by
  classical
  have := finite_quot_pow π hπ (k + 1)
  have := finite_quot_pow π hπ k
  have hle : Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k))
  set ρ := Ideal.Quotient.factor hle with hρ
  set ρM : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ (k + 1)}) →+ Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}) :=
    ρ.mapMatrix.toAddMonoidHom with hρM
  have hsurj : Function.Surjective ρM := fun Y => by
    choose f hf using fun i j => Ideal.Quotient.factor_surjective hle (Y i j)
    exact ⟨Matrix.of f, by ext i j; exact hf i j⟩
  set S : Set (Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k})) :=
    {Y | (Q.map (Ideal.Quotient.mk _)).compMat Y = Q.map (Ideal.Quotient.mk _)} with hS
  have key : ∀ X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ (k + 1)}),
      (Q'.map (Ideal.Quotient.mk _)).compMat X = Q'.map (Ideal.Quotient.mk _) ↔ ρM X ∈ S := by
    intro X
    choose f hf using fun i j => Ideal.Quotient.mk_surjective (X i j)
    have hX : X = (Matrix.of f).map (Ideal.Quotient.mk _) := by ext i j; exact (hf i j).symm
    have hρX : ρM X = (Matrix.of f).map (Ideal.Quotient.mk _) := by
      rw [hX]; ext i j; simp [hρM, hρ, Ideal.Quotient.factor_mk]
    rw [hρX, hX, Set.mem_setOf_eq, map_compMat, map_compMat, map_mk_eq_iff, map_mk_eq_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [compMat_coeff_of_coeff_mul π hQ', hQ', ← mul_sub, pow_succ', mul_dvd_mul_iff_left hπ.ne_zero]
  unfold repCountForm
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  have h1 := card_preimage_eq ρM S (fun Y _ => hsurj Y)
  have h2 := card_preimage_eq ρM Set.univ (fun Y _ => hsurj Y)
  simp only [Set.preimage_univ, Nat.card_univ] at h2
  have hc : ∀ j, Nat.card (R ⧸ Ideal.span {π ^ j}) = q R ^ j := fun j => card_quot_pow π hπ j
  have hM : ∀ j, Nat.card (Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ j})) = q R ^ (j * (n * n)) := by
    intro j
    rw [show Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ j}) = (Fin n → Fin n → R ⧸ Ideal.span {π ^ j}) from rfl,
      Nat.card_fun, Nat.card_fun, hc, Nat.card_fin, ← pow_mul, ← pow_mul]
  rw [hM, hM] at h2
  have hker : Nat.card ρM.ker = q R ^ (n * n) := by
    have hq : 0 < q R ^ (k * (n * n)) := pow_pos q_pos _
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [← pow_add, show n * n + k * (n * n) = (k + 1) * (n * n) by ring, h2]
  change Nat.card (ρM ⁻¹' S) = _
  rw [h1, hker]
  rfl

/-- **$\beta_\pi(\pi Q, \pi Q) = q^{n(n+1)/2}\beta_\pi(Q, Q)$** for nondegenerate $Q$. -/
theorem localDensityForm_smul_pi [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    {Q Q' : QuadForm R n} (hQ : Q.Nondegenerate) (hQ' : ∀ i j, Q'.coeff i j = π * Q.coeff i j) :
    localDensityForm Q' Q' π = (q R : ℝ) ^ (n * (n + 1) / 2) * localDensityForm Q Q π := by
  have hH : Q'.hessian = π • Q.hessian := by ext a b; simp [hessian, hQ']; ring
  have hQ'n : Q'.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hH, det_smul]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hQ
  have e1 := localDensityForm_eventually_eq Q' Q' hQ'n π hπ le_rfl
  have e2 := localDensityForm_eventually_eq Q Q hQ π hπ le_rfl
  obtain ⟨k, h1, h2⟩ := ((Filter.tendsto_add_atTop_nat 1).eventually e1).and e2 |>.exists
  rw [← h1, ← h2, repCountForm_smul_pi hπ hQ' k]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hle : n * (n + 1) / 2 ≤ n * n := by
    have : n * (n + 1) / 2 ≤ n * (n + 1) / 2 + n * (n - 1) / 2 := Nat.le_add_right _ _
    have h3 : n * (n + 1) / 2 + n * (n - 1) / 2 = n * n := by
      rw [← self_exp]; have : n * (n + 1) / 2 ≤ n * n := by
        rcases n with _ | n
        · simp
        · rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; nlinarith
      omega
    omega
  set e := n * n - n * (n + 1) / 2 with he
  have hsplit : n * n = e + n * (n + 1) / 2 := by omega
  push_cast
  rw [hsplit, pow_add, show (k + 1) * e = k * e + e by ring, pow_add]
  field_simp

end Scale

/-! ### The odd ramified self-density -/

section OddRam

variable {K : Type*} [Field K] [Finite K]

theorem card_mul_self_eq_one (h2 : (2 : K) ≠ 0) : Nat.card {t : K // t * t = 1} = 2 := by
  have h1 : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun t => t ∈ ({1, -1} : Set K)) fun t => by
    rw [mul_self_eq_one_iff]; simp), Nat.card_coe_set_eq, Set.ncard_pair h1]

/-- $\#\{X \in M_{3\times1}(K) : (\langle a\rangle\perp0)\circ X = \langle a\rangle\} = 2|K|^2$ ($2 \ne 0$, $a \ne 0$). -/
theorem card_reps_unary_split_zero (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (Q' : QuadForm K 2)
    (hQ' : ∀ i j, Q'.coeff i j = 0) :
    Nat.card {X : Matrix (Fin 3) (Fin 1) K // (splitForm a Q').compMat X = unary a} = 2 * Nat.card K ^ 2 := by
  have hz : ∀ y, Q'.eval y = 0 := fun y => by
    rw [eval_of_coeff_mul (Q := Q') 0 (fun i j => by rw [hQ', zero_mul]) y, zero_mul]
  have hcond : ∀ X : Matrix (Fin 3) (Fin 1) K, (splitForm a Q').compMat X = unary a ↔ X 0 0 * X 0 0 = 1 := by
    intro X
    have hc : ((splitForm a Q').compMat X).coeff 0 0 = a * X 0 0 * X 0 0 := by
      rw [compMat_coeff, if_pos le_rfl, if_pos rfl,
        show (fun l => X l 0) = Fin.cons (X 0 0) (fun i : Fin 2 => X i.succ 0) from (Fin.cons_self_tail _).symm,
        eval_splitForm_cons, hz, add_zero]
    constructor
    · intro h
      have := congrArg (fun S : QuadForm K 1 => S.coeff 0 0) h
      simp only [hc] at this
      have h' : a * (X 0 0 * X 0 0) = a * 1 := by
        rw [mul_one, ← mul_assoc]; simpa [unary, QuadForm.diag] using this
      exact mul_left_cancel₀ ha h'
    · intro h
      ext i j
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, hc, mul_assoc, h, mul_one]
      simp [unary, QuadForm.diag]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcond)]
  let e : {X : Matrix (Fin 3) (Fin 1) K // X 0 0 * X 0 0 = 1} ≃ {t : K // t * t = 1} × (Fin 2 → K) :=
    { toFun := fun X => (⟨X.1 0 0, X.2⟩, fun i : Fin 2 => X.1 i.succ 0)
      invFun := fun (p : {t : K // t * t = 1} × (Fin 2 → K)) =>
        ⟨Matrix.of fun (i : Fin 3) (_ : Fin 1) => (![p.1.1, p.2 0, p.2 1] i : K), by simpa using p.1.2⟩
      left_inv := fun X => by
        apply Subtype.ext; ext i j
        rw [Fin.fin_one_eq_zero j]
        fin_cases i <;> rfl
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext rfl) (funext fun i => ?_)
        fin_cases i <;> rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_mul_self_eq_one h2, Nat.card_fun, Nat.card_fin]

end OddRam

section OddRamDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-- **The self-density of $\langle u_0\rangle\perp\pi\langle u_1, u_2\rangle$ at $\pi \nmid 2$** ($u_i$ units, $\langle\bar u_1, \bar u_2\rangle$
anisotropic over the residue field):
$$\beta_\pi = q^3\cdot2(1 + q^{-1})\cdot2 = 4q^2(q+1),$$
from Weil's identity at a unit (`localIdentity_unit`), the scaling `localDensityForm_smul_pi`, the anisotropic unimodular
binary density $2(1 + q^{-1})$ (`localDensityForm_self_even`, $\chi_D = -1$) and $\beta_\pi(Q, u_0) = 2$. -/
theorem localDensityForm_odd_ram [Finite 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {u₀ u₁ u₂ : R}
    (h0 : IsUnit u₀) (h1 : IsUnit u₁) (hu2 : IsUnit u₂)
    (haniso : ∀ x y : 𝔽, res u₁ * x ^ 2 + res u₂ * y ^ 2 = 0 → x = 0 ∧ y = 0) :
    localDensityForm (splitForm u₀ (QuadForm.diag ![π * u₁, π * u₂]))
      (splitForm u₀ (QuadForm.diag ![π * u₁, π * u₂])) π = 4 * (q R : ℝ) ^ 2 * (q R + 1) := by
  classical
  have := Fintype.ofFinite 𝔽
  have h2u : IsUnit (2 : R) := dvr_isUnit_of_not_dvd hπ h2
  have h20 : (2 : R) ≠ 0 := h2u.ne_zero
  set B : QuadForm R 2 := QuadForm.diag ![u₁, u₂] with hB
  set B' : QuadForm R 2 := QuadForm.diag ![π * u₁, π * u₂] with hB'
  have hBB' : ∀ i j, B'.coeff i j = π * B.coeff i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hB, hB', QuadForm.diag]
  have hdetB : B.hessian.det = 4 * (u₁ * u₂) := by
    simp [hB, hessian, QuadForm.diag]; ring
  have hBu : IsUnit B.hessian.det := by
    rw [hdetB]; exact (show IsUnit (4 : R) by
      rw [show (4 : R) = 2 * 2 by norm_num]; exact h2u.mul h2u).mul (h1.mul hu2)
  have hBnd : B.Nondegenerate := hBu.ne_zero
  have hB'nd : B'.Nondegenerate := by
    have hH : B'.hessian = π • B.hessian := by ext a b; simp [hessian, hBB']; ring
    rw [QuadForm.Nondegenerate, hH, det_smul]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hBnd
  -- the three factors
  rw [← localIdentity_unit hπ (h2u.mul h0) h20 B' hB'nd, localDensityForm_smul_pi hπ hBnd hBB']
  have hχ : chiDisc (R := R) (n := 2) B = -1 := by
    unfold chiDisc resGramDet
    rw [quadraticChar_neg_one_iff_not_isSquare, hdetB]
    have h2F : (2 : 𝔽) ≠ 0 := by
      have := h2u.map res; rw [map_ofNat] at this; exact this.ne_zero
    have hu1F : res u₁ ≠ 0 := (h1.map res).ne_zero
    rintro ⟨s, hs⟩
    have hs' : -(res u₁ * res u₂) = s * s := by
      rw [← hs, map_mul, map_mul, map_ofNat]
      field_simp
      ring
    have := haniso s (res u₁) (by linear_combination (-(res u₁)) * hs')
    exact hu1F this.2
  have hself : localDensityForm B B π = 2 * (1 + ((q R : ℝ))⁻¹) := by
    have h := localDensityForm_self_even π 1 le_rfl B hπ h2 (dvr_not_dvd_of_isUnit hπ hBu)
    simp only [hχ, Nat.sub_self, Finset.range_zero, Finset.prod_empty, mul_one, pow_one, Int.cast_neg,
      Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at h
    exact h
  rw [hself]
  -- β(Q, u₀) = 2
  have hrep : localDensity (splitForm u₀ B') π u₀ = 2 := by
    rw [← localDensityForm_unary]
    have hU : IsUnit (unary u₀).hessian.det := by
      have : (unary u₀).hessian.det = 2 * u₀ := by simp [hessian, unary, QuadForm.diag, Matrix.det_unique]; ring
      rw [this]; exact h2u.mul h0
    rw [localDensityForm_eq_of_isUnit _ _ π hπ hU (by norm_num)]
    have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
      rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
    let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
    have hfin := finite_quot_pow π hπ 1
    set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
    have h2K : (2 : R ⧸ Ideal.span {π ^ 1}) ≠ 0 := by
      have := h2u.map mk; rw [map_ofNat] at this; exact this.ne_zero
    have hzero : ∀ i j, (B'.map mk).coeff i j = 0 := by
      intro i j
      simp only [QuadForm.map, Matrix.map_apply, hBB', map_mul]
      have : mk π = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self π
      rw [this, zero_mul]
    have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
    unfold repCountForm
    rw [map_splitForm, map_unary, card_reps_unary_split_zero h2K (h0.map mk).ne_zero _ hzero, hcard]
    have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
    push_cast
    field_simp
  rw [hrep]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  norm_num
  field_simp
  ring

end OddRamDVR

end QuadFormsKB.Tamagawa
