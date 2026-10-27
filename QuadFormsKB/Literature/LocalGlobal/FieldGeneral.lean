/-
# Quadratic-form lemmas over a general base field

The Hasse–Minkowski proof over $\mathbb{Q}$ used several lemmas that never needed $\mathbb{Q}$:
diagonalisation, invariance of isotropy under isometry, the ternary criterion via the Hilbert
symbol, and the reductions on diagonal forms. They are restated here over an arbitrary base field
$F$ of characteristic $0$, with $K$ any field that is an $F$-algebra (in the application: $F$ a
number field and $K$ either $F$ or a completion $F_v$). The $\mathbb{Q}$ versions
(`HM3.*`, `RankFive.*`, `HM4.*`) are the case $F = \mathbb{Q}$ and serve as proof templates.

Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiFour
import QuadFormsKB.Literature.LocalGlobal.RankFive

namespace QuadFormsKB.FieldGen

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- **Isotropy goes up** (the trivial direction of every local–global principle): if $Q$ over $F$
has a nonzero zero $\vec{x} \in F^n$, then it is isotropic over every field $K \supseteq F$. -/
@[kb "lam2005" "Ch. VI §3 [unverified]"]
theorem isotropicIn_of_base (K : Type*) [Field K] [Algebra F K] (Q : QuadForm F n)
    (h : Q.IsotropicIn F) : Q.IsotropicIn K := by
  obtain ⟨x, hx, hQ⟩ := h
  refine ⟨fun i => algebraMap F K (x i), ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  · have : QuadForm.evalIn K Q (fun i => algebraMap F K (x i)) = algebraMap F K (QuadForm.evalIn F Q x) := by
      unfold QuadForm.evalIn
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [this, hQ, map_zero]

/-- **Diagonalisation over a field of characteristic $0$:** every nondegenerate form $Q$ over $F$
is isometric over $F$ to a diagonal form $\langle a_0, \dots, a_{n-1} \rangle$ with all
$a_i \ne 0$. (The $F = \mathbb{Q}$ case is `HM3.exists_isometric_diag`.)

*Proof* (Lam I, Cor. 2.4; Serre IV §1.2). Since $2 \ne 0$ in $F$, a nonzero form takes a nonzero
value $Q(\vec{v}) = a_0$, and $Q \cong \langle a_0 \rangle \perp Q|_{\vec{v}^\perp}$; induct on $n$.
Nondegeneracy ($\det$ of the Hessian $\ne 0$) forces every $a_i \ne 0$. In Lean: view $Q$ as the
Mathlib form `(Matrix.toLinearMap₂' F Q.coeff).toQuadraticMap`, take an orthogonal basis $\vec{v}_i$
from `LinearMap.BilinForm.exists_orthogonal_basis` (applied to `QuadraticForm.associated_isSymm`),
reindex it by `finCongr (Module.finrank_fin_fun F)`, set $a_i = Q(\vec{v}_i)$, take the change of
basis matrix as $P$, and get $a_i \ne 0$ from `Matrix.exists_vecMul_eq_zero_iff` and
`QuadForm.polar_eq_hessian`. The proof of `HM3.exists_isometric_diag` does exactly this with
$\mathbb{Q}$ in place of $F$ and can be followed line by line. -/
@[kb "lam2005" "Ch. I, Cor. 2.4 [unverified]; cassels1978 Ch. 2, Lemma 1.4, p. 13 (normal basis)"]
theorem exists_isometric_diag (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    ∃ a : Fin n → F, (∀ i, a i ≠ 0) ∧ Q.IsometricIn F (QuadForm.diag a) := by
  classical
  letI : Invertible (2:F) := invertibleOfNonzero two_ne_zero
  set M : Matrix (Fin n) (Fin n) F := (1/2 : F) • Q.hessian with hM
  have hMt : M.transpose = M := by
    simp [hM, QuadForm.hessian, Matrix.transpose_add, add_comm]
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hQ
  set B : LinearMap.BilinForm F (Fin n → F) := Matrix.toLinearMap₂' F M with hB
  have hBapp : ∀ x y, B x y = x ⬝ᵥ M.mulVec y := fun x y => Matrix.toLinearMap₂'_apply' M x y
  have hsymm : LinearMap.IsSymm B := by
    refine ⟨fun x y => ?_⟩
    simp only [RingHom.id_apply, hBapp]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt, dotProduct_comm]
  have hsc : ∀ (c : F) (y : Fin n → F), QuadForm.evalIn F Q (c • y) = c^2 * QuadForm.evalIn F Q y := by
    intro c y
    unfold QuadForm.evalIn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp; ring
  have hkey : ∀ y, QuadForm.evalIn F Q y = B y y := by
    intro y
    have h := QuadForm.polar_eq_hessian F Q y y
    have h2 : y + y = (2:F) • y := by rw [two_smul]
    rw [h2, hsc] at h
    rw [hBapp, hM, Matrix.smul_mulVec, dotProduct_smul]
    have h3 : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
    rw [h3] at h
    rw [← h, smul_eq_mul]; ring
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set w := v.reindex (finCongr (Module.finrank_fin_fun F)) with hw
  have hwo : ∀ i j, i ≠ j → B (w i) (w j) = 0 := by
    intro i j hij
    simp only [hw, Module.Basis.reindex_apply]
    exact hv (by simpa using hij)
  refine ⟨fun i => B (w i) (w i), ?_, ?_⟩
  · intro i hi
    have hz : B (w i) = 0 := by
      apply w.ext
      intro j
      by_cases hij : i = j
      · subst hij; simpa using hi
      · simpa using hwo i j hij
    apply hMdet
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨w i, w.ne_zero i, ?_⟩
    funext j
    have := LinearMap.congr_fun hz (Pi.single j 1)
    rw [hBapp, Matrix.dotProduct_mulVec, dotProduct_single] at this
    simpa using this
  · refine ⟨(Pi.basisFun F (Fin n)).toMatrix w, ?_, ?_⟩
    · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
    · intro x
      have hmv : ((Pi.basisFun F (Fin n)).toMatrix w).mulVec x = ∑ j, x j • w j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
      rw [hkey, hmv]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      unfold QuadForm.evalIn QuadForm.diag
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
      · simp
      · intro j _ hj; simp [hwo j i hj]
      · simp

/-- **Isometry over $F$ persists over $K \supseteq F$:** if $Q \cong Q'$ over $F$ then
$Q \cong Q'$ over $K$. -/
@[kb "lam2005" "Ch. I §1 [unverified]"]
theorem isometricIn_of_base (K : Type*) [Field K] [Algebra F K] {Q Q' : QuadForm F n}
    (h : Q.IsometricIn F Q') : Q.IsometricIn K Q' := by
  obtain ⟨P, hP, hPx⟩ := h
  have keyF : ∀ (φ : MvPolynomial (Fin n) F →ₐ[F] F) (R : QuadForm F n) (v : Fin n → MvPolynomial (Fin n) F),
      φ (QuadForm.evalIn _ R v) = QuadForm.evalIn F R (fun i => φ (v i)) := by
    intro φ R v
    simp [QuadForm.evalIn, map_sum, apply_ite, map_mul]
  have keyK : ∀ (φ : MvPolynomial (Fin n) F →ₐ[F] K) (R : QuadForm F n) (v : Fin n → MvPolynomial (Fin n) F),
      φ (QuadForm.evalIn _ R v) = QuadForm.evalIn K R (fun i => φ (v i)) := by
    intro φ R v
    simp [QuadForm.evalIn, map_sum, apply_ite, map_mul]
  have mvF : ∀ (φ : MvPolynomial (Fin n) F →ₐ[F] F) (v : Fin n → MvPolynomial (Fin n) F),
      (fun i => φ ((P.map (algebraMap F _)).mulVec v i)) = P.mulVec (fun i => φ (v i)) := by
    intro φ v
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have mvK : ∀ (φ : MvPolynomial (Fin n) F →ₐ[F] K) (v : Fin n → MvPolynomial (Fin n) F),
      (fun i => φ ((P.map (algebraMap F _)).mulVec v i)) = (P.map (algebraMap F K)).mulVec (fun i => φ (v i)) := by
    intro φ v
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hF : QuadForm.evalIn (MvPolynomial (Fin n) F) Q
      ((P.map (algebraMap F (MvPolynomial (Fin n) F))).mulVec (fun i => MvPolynomial.X i))
      = QuadForm.evalIn (MvPolynomial (Fin n) F) Q' (fun i => MvPolynomial.X i) := by
    apply MvPolynomial.funext
    intro r
    rw [← MvPolynomial.coe_aeval_eq_eval]
    change (MvPolynomial.aeval r) _ = (MvPolynomial.aeval r) _
    rw [keyF, keyF, mvF]
    simp only [MvPolynomial.aeval_X]
    exact hPx r
  refine ⟨P.map (algebraMap F K), ?_, ?_⟩
  · have : (P.map (algebraMap F K)).det = algebraMap F K P.det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact hP.map _
  · intro x
    have e := congrArg (MvPolynomial.aeval (R := F) (S₁ := K) x) hF
    rw [keyK, keyK, mvK] at e
    simpa only [MvPolynomial.aeval_X] using e

/-- **Isotropy is an isometry invariant:** if $Q \cong Q'$ over $K$, then $Q$ is isotropic over
$K$ iff $Q'$ is. -/
@[kb "lam2005" "Ch. I §3 [unverified]"]
theorem isotropicIn_iff_of_isometricIn (K : Type*) [Field K] [Algebra F K]
    {Q Q' : QuadForm F n} (h : Q.IsometricIn K Q') : Q.IsotropicIn K ↔ Q'.IsotropicIn K := by
  obtain ⟨P, hP, hPx⟩ := h
  constructor
  · rintro ⟨x, hx, hx0⟩
    refine ⟨P⁻¹.mulVec x, ?_, ?_⟩
    · intro h0
      apply hx
      have := congrArg P.mulVec h0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    · rw [← hPx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
      exact hx0
  · rintro ⟨y, hy, hy0⟩
    refine ⟨P.mulVec y, ?_, ?_⟩
    · intro h0
      apply hy
      have := congrArg P⁻¹.mulVec h0
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    · rw [hPx]; exact hy0

/-- **Binary forms:** for $a, b \in F^\times$, the form $\langle a, b \rangle = a x_0^2 + b x_1^2$
is isotropic over $K$ iff $-ab$ is a square in $K$. -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 [unverified]"]
theorem isotropic_diag_two_iff (K : Type*) [Field K] [Algebra F K] (a b : F) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (QuadForm.diag ![a, b]).IsotropicIn K ↔ IsSquare (algebraMap F K (-(a * b))) := by
  have hev : ∀ x : Fin 2 → K, QuadForm.evalIn K (QuadForm.diag ![a, b]) x =
      algebraMap F K a * x 0 ^ 2 + algebraMap F K b * x 1 ^ 2 := by
    intro x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
    ring
  have hA : algebraMap F K a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact ha
  have hB : algebraMap F K b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hb
  rw [map_neg, map_mul]
  constructor
  · rintro ⟨x, hx, h0⟩
    rw [hev] at h0
    have hy : x 1 ≠ 0 := by
      intro hy
      apply hx
      have : x 0 = 0 := by
        rw [hy] at h0
        simp at h0
        rcases h0 with h | h
        · exact absurd h ha
        · exact h
      funext i; fin_cases i <;> simp [this, hy]
    refine ⟨algebraMap F K a * x 0 / x 1, ?_⟩
    have e : algebraMap F K a * x 0 / x 1 * (algebraMap F K a * x 0 / x 1)
        = algebraMap F K a * (algebraMap F K a * x 0 ^ 2) / x 1 ^ 2 := by ring
    rw [e, show algebraMap F K a * x 0 ^ 2 = -(algebraMap F K b * x 1 ^ 2) by
      linear_combination h0]
    field_simp
  · rintro ⟨r, hr⟩
    refine ⟨![r, algebraMap F K a], ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
      exact ha this
    · rw [hev]
      simp
      linear_combination (-(algebraMap F K a)) * hr

/-- **Ternary forms and the Hilbert symbol:** for $a_0, a_1, a_2 \in F^\times$, the form
$\langle a_0, a_1, a_2 \rangle$ is isotropic over $K$ iff
$\left(-\tfrac{a_1}{a_0}, -\tfrac{a_2}{a_0}\right)_K = 1$, the Hilbert symbol computed over $K$.
(The $F = \mathbb{Q}$ case is `HM3.isotropic_diag_three_iff`.) -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 [unverified]; cassels1978 Ch. 4, Lemma 2.5, p. 59"]
theorem isotropic_diag_three_iff (K : Type*) [Field K] [Algebra F K] (a₀ a₁ a₂ : F)
    (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    (QuadForm.diag ![a₀, a₁, a₂]).IsotropicIn K ↔
      hilbertSymbol K (algebraMap F K (-a₁ / a₀)) (algebraMap F K (-a₂ / a₀)) = 1 := by
  have hev : ∀ x : Fin 3 → K, QuadForm.evalIn K (QuadForm.diag ![a₀, a₁, a₂]) x = algebraMap F K a₀ * x 0 * x 0 + algebraMap F K a₁ * x 1 * x 1 + algebraMap F K a₂ * x 2 * x 2 := by
    intro x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
  have h0K : algebraMap F K a₀ ≠ 0 := (map_ne_zero (algebraMap F K)).mpr h₀
  unfold hilbertSymbol
  constructor
  · rintro ⟨x, hx, he⟩
    rw [hev] at he
    rw [if_pos]
    refine ⟨x 1, x 2, x 0, ?_, ?_⟩
    · intro hc
      simp only [Prod.mk_eq_zero] at hc
      apply hx
      funext i
      fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2]
    · simp only [map_div₀, map_neg]
      field_simp
      linear_combination he
  · intro h
    split_ifs at h with hc
    obtain ⟨x, y, z, hne, he⟩ := hc
    refine ⟨![z, x, y], ?_, ?_⟩
    · intro h0
      apply hne
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      have e2 := congrFun h0 2
      simp at e0 e1 e2
      simp [e0, e1, e2]
    · rw [hev]
      simp only [map_div₀, map_neg] at he
      field_simp at he
      simp
      linear_combination he

/-- **A common value of two binary forms:** for $a_1, a_2, a_3, a_4 \in F^\times$, if
$\langle a_1, a_2, -a_3, -a_4 \rangle$ is isotropic over $K$, then some $x \in K^\times$ satisfies
$(x, -a_1 a_2)_K = (a_1, a_2)_K$ and $(x, -a_3 a_4)_K = (a_3, a_4)_K$ (in the application, $x$ is a
common nonzero value of $\langle a_1, a_2 \rangle$ and $\langle a_3, a_4 \rangle$). The
$F = \mathbb{Q}$ case is `HM4.exists_common_value`. -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]"]
theorem exists_common_value (K : Type*) [Field K] [Algebra F K] (a₁ a₂ a₃ a₄ : F)
    (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0)
    (hiso : (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn K) :
    ∃ x : K, x ≠ 0 ∧
      hilbertSymbol K x (algebraMap F K (-(a₁ * a₂))) =
        hilbertSymbol K (algebraMap F K a₁) (algebraMap F K a₂) ∧
      hilbertSymbol K x (algebraMap F K (-(a₃ * a₄))) =
        hilbertSymbol K (algebraMap F K a₃) (algebraMap F K a₄) := by
  have hA : ∀ a b : K, a ≠ 0 → hilbertSymbol K a (-(a*b)) = hilbertSymbol K a b := by
    intro a b ha
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨z, a*y, a*x, ?_, ?_⟩
      · intro h0; apply hne
        simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
        tauto
      · linear_combination (-a) * h
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨z, y, a*x, ?_, ?_⟩
      · intro h0; apply hne
        simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
        tauto
      · linear_combination (-a) * h
  have hB : ∀ a b t X Y : K, a ≠ 0 → b ≠ 0 → t ≠ 0 → t = a * X^2 + b * Y^2 →
      hilbertSymbol K t (-(a*b)) = hilbertSymbol K a b := by
    intro a b t X Y ha hb htne ht
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨u, v, w, hne, h⟩
      refine ⟨X*w - b*Y*v, a*X*v + Y*w, t*u, ?_, ?_⟩
      · intro h0; apply hne
        simp only [Prod.mk_eq_zero] at h0 ⊢
        obtain ⟨e1, e2, e3⟩ := h0
        have hu : u = 0 := by simpa [htne] using e3
        have hw : t * w = 0 := by linear_combination (w) * ht + a*X*e1 + b*Y*e2
        have hv : t * v = 0 := by linear_combination (v) * ht - Y*e1 + X*e2
        simp [htne] at hw hv
        exact ⟨hu, hv, hw⟩
      · linear_combination (-t) * h + (w^2 + a*b*v^2) * ht
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨z, X*y - Y*x, a*X*x + b*Y*y, ?_, ?_⟩
      · intro h0; apply hne
        simp only [Prod.mk_eq_zero] at h0 ⊢
        obtain ⟨e3, e2, e1⟩ := h0
        have hx : t * x = 0 := by linear_combination (x) * ht + X*e1 - b*Y*e2
        have hy : t * y = 0 := by linear_combination (y) * ht + Y*e1 + a*X*e2
        simp [htne] at hx hy
        exact ⟨hx, hy, e3⟩
      · linear_combination (-t) * h - (a*x^2 + b*y^2) * ht
  have hC : ∀ a b x y : K, a ≠ 0 → a * x^2 + b * y^2 = 0 → ¬(x = 0 ∧ y = 0) →
      hilbertSymbol K a b = 1 ∧ ∀ c, hilbertSymbol K c (-(a*b)) = 1 := by
    intro a b x y ha h hxy
    constructor
    · unfold hilbertSymbol
      rw [if_pos]
      refine ⟨x, y, 0, ?_, ?_⟩
      · intro h0; apply hxy
        simp only [Prod.mk_eq_zero] at h0
        exact ⟨h0.1, h0.2.1⟩
      · linear_combination (-1:K) * h
    · intro c
      unfold hilbertSymbol
      rw [if_pos]
      refine ⟨0, y, a*x, ?_, ?_⟩
      · intro h0; apply hxy
        simp only [Prod.mk_eq_zero, mul_eq_zero] at h0
        tauto
      · linear_combination a * h
  have A1 : algebraMap F K a₁ ≠ 0 := by simpa using h₁
  have A2 : algebraMap F K a₂ ≠ 0 := by simpa using h₂
  have A3 : algebraMap F K a₃ ≠ 0 := by simpa using h₃
  have A4 : algebraMap F K a₄ ≠ 0 := by simpa using h₄
  obtain ⟨v, hv0, hv⟩ := hiso
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal] at hv
  simp only [map_neg, map_mul]
  set B1 := algebraMap F K a₁
  set B2 := algebraMap F K a₂
  set B3 := algebraMap F K a₃
  set B4 := algebraMap F K a₄
  by_cases ht : B1 * v 0 ^ 2 + B2 * v 1 ^ 2 = 0
  · by_cases h23 : v 2 = 0 ∧ v 3 = 0
    · have h01 : ¬ (v 0 = 0 ∧ v 1 = 0) := by
        rintro ⟨e0, e1⟩
        apply hv0
        funext i
        fin_cases i <;> simp [e0, e1, h23.1, h23.2]
      obtain ⟨c1, c2⟩ := hC B1 B2 (v 0) (v 1) A1 ht h01
      refine ⟨B3, A3, c2 _ |>.trans c1.symm, hA _ _ A3⟩
    · have ht' : B3 * v 2 ^ 2 + B4 * v 3 ^ 2 = 0 := by linear_combination ht - hv
      obtain ⟨c1, c2⟩ := hC B3 B4 (v 2) (v 3) A3 ht' h23
      exact ⟨B1, A1, hA _ _ A1, c2 _ |>.trans c1.symm⟩
  · refine ⟨_, ht, hB B1 B2 _ (v 0) (v 1) A1 A2 ht rfl, ?_⟩
    exact hB B3 B4 _ (v 2) (v 3) A3 A4 ht (by linear_combination hv)

/-- **Sub-forms:** if the diagonal form on the first $m$ coefficients $a_0, \dots, a_{m-1}$
($m \le n$) is isotropic over $K$, so is $\langle a_0, \dots, a_{n-1} \rangle$. -/
@[kb "lam2005" "Ch. I §3 [unverified]"]
theorem isotropicIn_diag_of_prefix (K : Type*) [Field K] [Algebra F K] (m : ℕ) (hm : m ≤ n)
    (a : Fin n → F)
    (h : (QuadForm.diag fun i : Fin m => a ⟨i, lt_of_lt_of_le i.2 hm⟩).IsotropicIn K) :
    (QuadForm.diag a).IsotropicIn K := by
  have hev : ∀ {k : ℕ} (b : Fin k → F) (x : Fin k → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i ^ 2 := by
    intro k b x
    unfold QuadForm.evalIn QuadForm.diag
    simp only [Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [sq, mul_assoc]
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  obtain ⟨x, hx0, hx⟩ := h
  rw [hev] at hx
  let y : Fin n → K := fun j => if hj : (j : ℕ) < m then x ⟨j, hj⟩ else 0
  let g : ℕ → K := fun j => if hj : j < m then
      algebraMap F K (a ⟨j, lt_of_lt_of_le hj hm⟩) * x ⟨j, hj⟩ ^ 2 else 0
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx0
    funext i
    have := congrFun hy ⟨i, lt_of_lt_of_le i.2 hm⟩
    simpa [y] using this
  · rw [hev]
    have h1 : ∑ i : Fin n, algebraMap F K (a i) * y i ^ 2 = ∑ i : Fin n, g i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (i : ℕ) < m
      · simp [y, g, hi]
      · simp [y, g, hi]
    have h2 : ∑ i : Fin m, algebraMap F K (a ⟨i, lt_of_lt_of_le i.2 hm⟩) * x i ^ 2
        = ∑ i : Fin m, g i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [g, i.2]
    rw [h1, Fin.sum_univ_eq_sum_range, ← Finset.sum_range_add_sum_Ico _ hm,
      ← Fin.sum_univ_eq_sum_range, ← h2, hx, zero_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : ¬ j < m := by simp at hj; omega
    simp [g, this]

/-- **Permuting coefficients:** $\langle a_{\sigma(0)}, \dots, a_{\sigma(n-1)} \rangle$ is isotropic
over $K$ iff $\langle a_0, \dots, a_{n-1} \rangle$ is, for every permutation $\sigma$ of
$\{0, \dots, n-1\}$. -/
@[kb "lam2005" "Ch. I §3 [unverified]"]
theorem isotropicIn_diag_perm_iff (K : Type*) [Field K] [Algebra F K] (a : Fin n → F)
    (σ : Equiv.Perm (Fin n)) :
    (QuadForm.diag (a ∘ σ)).IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K := by
  have key : ∀ (b : Fin n → F) (x : Fin n → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i * x i := by
    intro b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  constructor
  · rintro ⟨x, hx, h0⟩
    refine ⟨x ∘ σ.symm, ?_, ?_⟩
    · intro h
      apply hx
      funext i
      have := congrFun h (σ i)
      simpa using this
    · rw [key] at h0 ⊢
      rw [← h0, ← Equiv.sum_comp σ]
      simp
  · rintro ⟨x, hx, h0⟩
    refine ⟨x ∘ σ, ?_, ?_⟩
    · intro h
      apply hx
      funext i
      have := congrFun h (σ.symm i)
      simpa using this
    · rw [key] at h0 ⊢
      rw [← h0]
      exact Equiv.sum_comp σ (fun i => algebraMap F K (a i) * x i * x i)

/-- **Adding a coefficient keeps isotropy:** if $\langle a_0, \dots, a_{m-1} \rangle$ is isotropic over
$K$, then so is $\langle c, a_0, \dots, a_{m-1} \rangle$ for every $c \in F$. -/
@[kb "lam2005" "Ch. I §3 [unverified]"]
theorem isotropicIn_diag_cons_of (K : Type*) [Field K] [Algebra F K] (m : ℕ) (c : F)
    (a : Fin m → F) (h : (QuadForm.diag a).IsotropicIn K) :
    (QuadForm.diag (Fin.cons c a : Fin (m + 1) → F)).IsotropicIn K := by
  have hd : ∀ {k : ℕ} (b : Fin k → F) (x : Fin k → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i * x i := by
    intro k b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]
    · intro j _ hj
      split_ifs <;> simp [Matrix.diagonal, Ne.symm hj]
    · simp
  obtain ⟨x, hx, hx0⟩ := h
  refine ⟨Fin.cons 0 x, ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have := congrFun h0 i.succ
    simpa using this
  · rw [hd] at hx0 ⊢
    rw [Fin.sum_univ_succ]
    simpa using hx0

/-- **Splitting off a binary form, locally:** let $m \ge 1$ and $a_0, \dots, a_{m+1} \in F^\times$.
If $\langle a_0, \dots, a_{m+1} \rangle$ is isotropic over $K$, then some $t \in K^\times$ is a value
of $\langle a_0, a_1 \rangle$ over $K$ while $-t$ is a value of
$g = \langle a_2, \dots, a_{m+1} \rangle$ over $K$. -/
@[kb "lam2005" "Ch. VI, proof of Thm. 3.1 [unverified]"]
theorem exists_split_value (K : Type*) [Field K] [Algebra F K] (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (m + 2) → F) (ha : ∀ i, a i ≠ 0) (hiso : (QuadForm.diag a).IsotropicIn K) :
    ∃ t : K, t ≠ 0 ∧ (∃ X Y : K, algebraMap F K (a 0) * X ^ 2 + algebraMap F K (a 1) * Y ^ 2 = t) ∧
      ∃ z : Fin m → K, ∑ i, algebraMap F K (a (i.addNat 2)) * z i ^ 2 = -t := by
  have hev : ∀ {n : ℕ} (b : Fin n → F) (x : Fin n → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap F K (b i) * x i ^ 2 := by
    intro n b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  have h2 : (2:K) ≠ 0 := by
    intro h; apply two_ne_zero (α := F); apply (algebraMap F K).injective
    rw [map_ofNat, map_zero]; exact h
  have hA : ∀ i, algebraMap F K (a i) ≠ 0 := fun i => by
    have := (algebraMap F K).injective.ne (ha i); simpa using this
  obtain ⟨x, hx0, hx⟩ := hiso
  rw [hev] at hx
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hx
  have hidx : ∀ k : Fin m, (k.succ.succ : Fin (m+2)) = k.addNat 2 := fun k => by ext; simp
  simp only [hidx] at hx
  set S := ∑ k : Fin m, algebraMap F K (a (k.addNat 2)) * x (k.addNat 2) ^ 2 with hS
  have e0 : (0 : Fin (m+1)).succ = (1 : Fin (m+2)) := rfl
  rw [e0] at hx
  by_cases ht : algebraMap F K (a 0) * x 0 ^ 2 + algebraMap F K (a 1) * x 1 ^ 2 = 0
  · by_cases hx01 : x 0 = 0 ∧ x 1 = 0
    · obtain ⟨j, hj⟩ : ∃ j : Fin m, x (j.addNat 2) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hx0
        funext i
        refine Fin.cases hx01.1 (fun i => Fin.cases hx01.2 (fun k => ?_) i) i
        rw [hidx]; exact hcon k
      have hS0 : S = 0 := by linear_combination hx - ht
      set c := -algebraMap F K (a 0)
      set b := algebraMap F K (a (j.addNat 2))
      set α := (c / b - 1) / (2 * x (j.addNat 2))
      refine ⟨algebraMap F K (a 0), hA 0, ⟨1, 0, by ring⟩,
        fun k => α * x (k.addNat 2) + if k = j then 1 else 0, ?_⟩
      have hpt : ∀ k : Fin m, algebraMap F K (a (k.addNat 2)) * (α * x (k.addNat 2) + if k = j then 1 else 0) ^ 2
          = α ^ 2 * (algebraMap F K (a (k.addNat 2)) * x (k.addNat 2) ^ 2) +
            (if k = j then algebraMap F K (a (k.addNat 2)) * (2 * α * x (k.addNat 2) + 1) else 0) := by
        intro k; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← hS, hS0, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      have hb : b ≠ 0 := hA _
      have : 2 * α * x (j.addNat 2) + 1 = c / b := by
        simp only [α]; field_simp; ring
      rw [this]; field_simp; ring
    · have hx0' : x 0 ≠ 0 := by
        intro h0; apply hx01; refine ⟨h0, ?_⟩
        rw [h0] at ht
        have : algebraMap F K (a 1) * x 1 ^ 2 = 0 := by linear_combination ht
        simpa [hA 1] using this
      set j : Fin m := ⟨0, hm⟩
      set c := -algebraMap F K (a (j.addNat 2))
      set P := algebraMap F K (a 0) * x 0 ^ 2 with hPdef
      have hP : P ≠ 0 := mul_ne_zero (hA 0) (pow_ne_zero _ hx0')
      set s := c / P
      refine ⟨c, by simpa [c] using hA _, ⟨x 0 * ((1 + s) / 2), x 1 * ((1 - s) / 2), ?_⟩,
        Pi.single j 1, ?_⟩
      · have h1 : algebraMap F K (a 1) * x 1 ^ 2 = -P := by linear_combination ht
        have : s * P = c := by simp only [s]; field_simp
        have huv : ((1 + s) / 2)^2 - ((1 - s) / 2)^2 = s := by field_simp; ring
        linear_combination (((1 - s)/2)^2) * h1 + P * huv + this + ((1 + s) / 2)^2 * hPdef
      · rw [Finset.sum_eq_single j]
        · simp [c]
        · intro k _ hk; simp [hk]
        · simp
  · refine ⟨_, ht, ⟨x 0, x 1, rfl⟩, fun k => x (k.addNat 2), ?_⟩
    linear_combination hx

/-- **Splitting off a binary form, globally:** let $a_0, \dots, a_{m+1} \in F$. If
$\langle a_0, a_1 \rangle$ represents some $t \in F^\times$ over $F$ and
$\langle t, a_2, \dots, a_{m+1} \rangle$ is isotropic over $F$ (so $\langle a_2, \dots, a_{m+1} \rangle$
represents $-t$, or is itself isotropic), then $\langle a_0, \dots, a_{m+1} \rangle$ is isotropic over $F$.

*Correction (llmprove).* This was first stated with $\langle -t, a_2, \dots \rangle$, which is
false: over $\mathbb{Q}$, $a = (1,1,1)$ and $t = 1$ satisfy that hypothesis, yet $\langle 1,1,1 \rangle$
is anisotropic. -/
@[kb "lam2005" "Ch. VI, proof of Thm. 3.1 [unverified]"]
theorem isotropic_of_split (m : ℕ) (a : Fin (m + 2) → F) (t : F) (ht : t ≠ 0)
    (hrep : (QuadForm.diag ![a 0, a 1]).RepresentsIn F t)
    (hiso : (QuadForm.diag (Fin.cons t fun i : Fin m => a (i.addNat 2))).IsotropicIn F) :
    (QuadForm.diag a).IsotropicIn F := by
  have hev : ∀ {n : ℕ} (b : Fin n → F) (x : Fin n → F),
      QuadForm.evalIn F (QuadForm.diag b) x = ∑ i, b i * x i ^ 2 := by
    intro n b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  obtain ⟨u, hu⟩ := hrep
  obtain ⟨z, hz0, hz⟩ := hiso
  rw [hev] at hu hz
  simp only [Fin.sum_univ_two, Algebra.algebraMap_self, RingHom.id_apply] at hu
  rw [Fin.sum_univ_succ] at hz
  simp only [Fin.cons_zero, Fin.cons_succ] at hz
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu
  refine ⟨Fin.cons (u 0 * z 0) (Fin.cons (u 1 * z 0) (fun i => z i.succ)), ?_, ?_⟩
  · intro h0
    apply hz0
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    have e2 : ∀ i : Fin m, z i.succ = 0 := fun i => by
      have := congrFun h0 i.succ.succ
      simpa using this
    have hz00 : z 0 = 0 := by
      by_contra hne
      simp [hne] at e0 e1
      have : t = 0 := by rw [← hu, e0, e1]; ring
      exact ht this
    funext i
    refine Fin.cases hz00 (fun k => e2 k) i
  · rw [hev, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hidx : ∀ k : Fin m, (k.succ.succ : Fin (m+2)) = k.addNat 2 := fun k => by ext; simp
    simp only [hidx]
    have : a 1 = a (0 : Fin (m+1)).succ := rfl
    rw [← this]
    linear_combination hz + z 0 ^ 2 * hu

/-- **Pfister forms (Lam's $n = 4$, square discriminant):** for $x, y \in F^\times$, the form
$\langle 1, x, y, xy \rangle$ is isotropic over $K$ iff $\langle 1, x, y \rangle$ is.

*Proof* (Lam X, Thm. 1.7 for 2-fold Pfister forms; elementary). "If" is
`isotropicIn_diag_of_prefix`. For "only if", write the form as $\langle 1, x \rangle \perp y \langle 1, x \rangle$:
an isotropic vector gives $n_1 + y n_2 = 0$ with $n_1 = X_0^2 + x X_1^2$, $n_2 = X_2^2 + x X_3^2$. If
$(X_0, X_1) \ne 0$ and $n_1 = 0$, then $\langle 1, x \rangle$ (hence $\langle 1, x, y \rangle$) is isotropic;
similarly for $(X_2, X_3)$. Otherwise $n_1, n_2 \ne 0$ and $-y = n_1/n_2 = n_1 n_2 / n_2^2$; the values
of $\langle 1, x \rangle$ are closed under multiplication
($(a^2 + x b^2)(c^2 + x d^2) = (ac - x bd)^2 + x(ad + bc)^2$), so $\langle 1, x \rangle$ represents $-y$, i.e.
$\langle 1, x, y \rangle$ is isotropic. -/
@[kb "lam2005" "Ch. X, Thm. 1.7 [unverified]"]
theorem isotropic_pfister_iff (K : Type*) [Field K] [Algebra F K] (x y : F) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    (QuadForm.diag ![1, x, y, x * y]).IsotropicIn K ↔ (QuadForm.diag ![1, x, y]).IsotropicIn K := by
  have hev : ∀ {k : ℕ} (b : Fin k → F) (z : Fin k → K),
      QuadForm.evalIn K (QuadForm.diag b) z = ∑ i, algebraMap F K (b i) * z i ^ 2 := by
    intro k b z
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [hev] at hv
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, map_one, map_mul, Matrix.head_cons, Matrix.tail_cons] at hv
    by_cases hn2 : v 2 ^ 2 + algebraMap F K x * v 3 ^ 2 = 0
    · by_cases h23 : v 2 = 0 ∧ v 3 = 0
      · refine ⟨![v 0, v 1, 0], ?_, ?_⟩
        · intro h; apply hv0
          have e0 := congrFun h 0
          have e1 := congrFun h 1
          simp at e0 e1
          funext i; fin_cases i <;> simp [e0, e1, h23.1, h23.2]
        · rw [hev]; simp [Fin.sum_univ_three]; rw [h23.1, h23.2] at hv; linear_combination hv
      · refine ⟨![v 2, v 3, 0], ?_, ?_⟩
        · intro h; apply h23
          have e0 := congrFun h 0
          have e1 := congrFun h 1
          simp at e0 e1
          exact ⟨e0, e1⟩
        · rw [hev]; simp [Fin.sum_univ_three]; linear_combination hn2
    · refine ⟨![v 0 * v 2 - algebraMap F K x * v 1 * v 3, v 0 * v 3 + v 1 * v 2,
        v 2 ^ 2 + algebraMap F K x * v 3 ^ 2], ?_, ?_⟩
      · intro h; apply hn2; simpa using congrFun h 2
      · rw [hev]; simp [Fin.sum_univ_three]
        linear_combination (v 2 ^ 2 + algebraMap F K x * v 3 ^ 2) * hv
  · rintro ⟨v, hv0, hv⟩
    refine ⟨![v 0, v 1, v 2, 0], ?_, ?_⟩
    · intro h; apply hv0
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      simp at e0 e1 e2
      funext i; fin_cases i <;> simp [e0, e1, e2]
    · rw [hev] at hv ⊢
      simp [Fin.sum_univ_three, Fin.sum_univ_four] at hv ⊢
      linear_combination hv

/-- **Going down a quadratic extension in dimension 4** (Lam's $n = 4$, non-square discriminant):
let $a_0, \dots, a_3 \in F^\times$ with $d = a_0 a_1 a_2 a_3$ **not** a square in $F$, and let $L$ be a
field containing $F$ and an element $s$ with $s^2 = d$ such that every element of $L$ is $a + b s$
($a, b \in F$), i.e. $L = F(\sqrt d)$. If $\langle a_0, a_1, a_2, a_3 \rangle$ is isotropic over $L$, it is
isotropic over $F$.

*Proof* (Lam VII, Thm. 3.1 (ii) / VI §3). Suppose $q$ is anisotropic over $F$. An isotropic vector
over $L$ is $\vec u + s \vec w$ with $\vec u, \vec w \in F^4$, $\vec w \ne 0$; expanding,
$q(\vec u) + d\, q(\vec w) = 0$ and $B(\vec u, \vec w) = 0$ (the coefficients of $1$ and $s$). So
$c := q(\vec w) \ne 0$ and $q(\vec u) = -dc$ with $\vec u \perp \vec w$, giving
$q \cong \langle c, -cd \rangle \perp \langle e, f \rangle$ over $F$ (`exists_isometric_diag` on the
orthogonal complement). Comparing discriminants, $-c^2 d e f \equiv d$ modulo squares, so
$e f \equiv -1$ and $\langle e, f \rangle$ is isotropic: contradiction. -/
@[kb "lam2005" "Ch. VII, Thm. 3.1 [unverified]"]
theorem isotropic_four_of_quadExt (L : Type*) [Field L] [Algebra F L] (a : Fin 4 → F)
    (ha : ∀ i, a i ≠ 0) (hd : ¬ IsSquare (a 0 * a 1 * a 2 * a 3)) (s : L)
    (hs : s ^ 2 = algebraMap F L (a 0 * a 1 * a 2 * a 3))
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (hiso : (QuadForm.diag a).IsotropicIn L) : (QuadForm.diag a).IsotropicIn F := by
  classical
  have key : ∀ b0 b1 b2 b3 u0 u1 u2 u3 w0 w1 w2 w3 : F, b0 ≠ 0 → b1 ≠ 0 → b2 ≠ 0 → b3 ≠ 0 →
      b0*u0*w0 + b1*u1*w1 + b2*u2*w2 + b3*u3*w3 = 0 →
      (b0*u0^2 + b1*u1^2 + b2*u2^2 + b3*u3^2) + b0*b1*b2*b3*(b0*w0^2 + b1*w1^2 + b2*w2^2 + b3*w3^2) = 0 →
      u2*w3 - u3*w2 ≠ 0 →
      (∀ x0 x1 x2 x3 : F, b0*x0^2 + b1*x1^2 + b2*x2^2 + b3*x3^2 = 0 → x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0) → False := by
    intro b0 b1 b2 b3 u0 u1 u2 u3 w0 w1 w2 w3 h0 h1 h2 h3 hB hQ hp H
    obtain ⟨c, hc⟩ : ∃ c, c = b0*w0^2 + b1*w1^2 + b2*w2^2 + b3*w3^2 := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = b0*b1*b2*b3 := ⟨_, rfl⟩
    obtain ⟨P02, e02⟩ : ∃ P, P = b0*b2*(u0*w2 - u2*w0) := ⟨_, rfl⟩
    obtain ⟨P03, e03⟩ : ∃ P, P = b0*b3*(u0*w3 - u3*w0) := ⟨_, rfl⟩
    obtain ⟨P12, e12⟩ : ∃ P, P = b1*b2*(u1*w2 - u2*w1) := ⟨_, rfl⟩
    obtain ⟨P13, e13⟩ : ∃ P, P = b1*b3*(u1*w3 - u3*w1) := ⟨_, rfl⟩
    obtain ⟨P23, e23⟩ : ∃ P, P = b2*b3*(u2*w3 - u3*w2) := ⟨_, rfl⟩
    have hP : P23 ≠ 0 := by rw [e23]; exact mul_ne_zero (mul_ne_zero h2 h3) hp
    obtain ⟨qz, eqz⟩ : ∃ q, q = b1*P23^2 + b2*P13^2 + b3*P12^2 := ⟨_, rfl⟩
    obtain ⟨qz', eqz'⟩ : ∃ q, q = b0*P23^2 + b2*P03^2 + b3*P02^2 := ⟨_, rfl⟩
    obtain ⟨Bz, eBz⟩ : ∃ q, q = b2*(-P13)*P03 + b3*P12*(-P02) := ⟨_, rfl⟩
    obtain ⟨r, er⟩ : ∃ q, q = P23*d*c := ⟨_, rfl⟩
    have hqz : qz ≠ 0 := by
      intro h
      rw [eqz] at h
      have := (H 0 P23 (-P13) P12 (by linear_combination h)).2.1
      exact hP this
    have hid : r^2 - Bz^2 + qz*qz' = P23^2*d*c*((b0*u0^2 + b1*u1^2 + b2*u2^2 + b3*u3^2) + b0*b1*b2*b3*(b0*w0^2 + b1*w1^2 + b2*w2^2 + b3*w3^2)) - P23^2*d*(b0*u0*w0 + b1*u1*w1 + b2*u2*w2 + b3*u3*w3)^2 := by
      subst er eBz eqz eqz' e02 e03 e12 e13 e23 hc hd
      ring
    have := H (qz * (-P23)) (- (Bz + r) * P23) (qz * P03 - (Bz+r)*(-P13)) (qz*(-P02) - (Bz+r)*P12) ?_
    · exact mul_ne_zero hqz (neg_ne_zero.mpr hP) this.1
    · rw [hB, hQ] at hid
      linear_combination qz * hid - qz^2 * eqz' - (Bz+r)^2 * eqz + 2*qz*(Bz+r)*eBz
  have hevL : ∀ x : Fin 4 → L, QuadForm.evalIn L (QuadForm.diag a) x = algebraMap F L (a 0) * x 0 ^ 2 + algebraMap F L (a 1) * x 1 ^ 2 + algebraMap F L (a 2) * x 2 ^ 2 + algebraMap F L (a 3) * x 3 ^ 2 := by
    intro x; unfold QuadForm.evalIn QuadForm.diag; simp [Fin.sum_univ_four, Matrix.diagonal]; ring
  have hevF : ∀ x : Fin 4 → F, QuadForm.evalIn F (QuadForm.diag a) x = a 0 * x 0 ^ 2 + a 1 * x 1 ^ 2 + a 2 * x 2 ^ 2 + a 3 * x 3 ^ 2 := by
    intro x; unfold QuadForm.evalIn QuadForm.diag; simp [Fin.sum_univ_four, Matrix.diagonal]; ring
  have hind : ∀ b0 b1 : F, algebraMap F L b0 + algebraMap F L b1 * s = 0 → b0 = 0 ∧ b1 = 0 := by
    intro b0 b1 h
    by_cases hb1 : b1 = 0
    · subst hb1; simp at h; exact ⟨h, rfl⟩
    · exfalso; apply hd
      refine ⟨-b0/b1, ?_⟩
      apply (algebraMap F L).injective
      have hb1' : algebraMap F L b1 ≠ 0 := by simpa using hb1
      have hs' : s = algebraMap F L (-b0/b1) := by
        rw [map_div₀, map_neg]; field_simp; linear_combination h
      rw [← hs, hs', map_mul]; ring
  obtain ⟨v, hv0, hv⟩ := hiso
  rw [hevL] at hv
  obtain ⟨u0, w0, e0⟩ := hspan (v 0)
  obtain ⟨u1, w1, e1⟩ := hspan (v 1)
  obtain ⟨u2, w2, e2⟩ := hspan (v 2)
  obtain ⟨u3, w3, e3⟩ := hspan (v 3)
  rw [e0, e1, e2, e3] at hv
  have hexp : algebraMap F L ((a 0*u0^2 + a 1*u1^2 + a 2*u2^2 + a 3*u3^2) + a 0 * a 1 * a 2 * a 3*(a 0*w0^2 + a 1*w1^2 + a 2*w2^2 + a 3*w3^2)) + algebraMap F L (2 * (a 0*u0*w0 + a 1*u1*w1 + a 2*u2*w2 + a 3*u3*w3)) * s = 0 := by
    rw [← hv]
    simp only [map_add, map_mul, map_pow, map_ofNat] at hs ⊢
    linear_combination (-(algebraMap F L (a 0) * algebraMap F L w0 ^ 2 + algebraMap F L (a 1) * algebraMap F L w1 ^ 2 + algebraMap F L (a 2) * algebraMap F L w2 ^ 2 + algebraMap F L (a 3) * algebraMap F L w3 ^ 2)) * hs
  obtain ⟨hX, hY⟩ := hind _ _ hexp
  have hB := (mul_eq_zero.mp hY).resolve_left two_ne_zero
  by_contra hcon
  have H : ∀ x0 x1 x2 x3 : F, a 0*x0^2 + a 1*x1^2 + a 2*x2^2 + a 3*x3^2 = 0 → x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
    intro x0 x1 x2 x3 h
    by_contra hne
    apply hcon
    refine ⟨![x0, x1, x2, x3], ?_, ?_⟩
    · intro h0
      apply hne
      have f0 := congrFun h0 0
      have f1 := congrFun h0 1
      have f2 := congrFun h0 2
      have f3 := congrFun h0 3
      simp at f0 f1 f2 f3
      exact ⟨f0, f1, f2, f3⟩
    · rw [hevF]; simpa using h
  have hw : ¬ (w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0) := by
    rintro ⟨f0, f1, f2, f3⟩
    subst f0 f1 f2 f3
    obtain ⟨g0, g1, g2, g3⟩ := H u0 u1 u2 u3 (by linear_combination hX)
    subst g0 g1 g2 g3
    apply hv0
    funext i
    fin_cases i <;> simp [e0, e1, e2, e3]
  have hc : a 0*w0^2 + a 1*w1^2 + a 2*w2^2 + a 3*w3^2 ≠ 0 := fun h => hw (H _ _ _ _ h)
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  by_cases p23 : u2*w3 - u3*w2 ≠ 0
  · exact key _ _ _ _ u0 u1 u2 u3 w0 w1 w2 w3 h0 h1 h2 h3 hB hX p23 H
  by_cases p13 : u1*w3 - u3*w1 ≠ 0
  · exact key _ _ _ _ u0 u2 u1 u3 w0 w2 w1 w3 h0 h2 h1 h3 (by linear_combination hB)
      (by linear_combination hX) p13
      (fun x0 x1 x2 x3 h => by have := H x0 x2 x1 x3 (by linear_combination h); tauto)
  by_cases p12 : u1*w2 - u2*w1 ≠ 0
  · exact key _ _ _ _ u0 u3 u1 u2 w0 w3 w1 w2 h0 h3 h1 h2 (by linear_combination hB)
      (by linear_combination hX) p12
      (fun x0 x1 x2 x3 h => by have := H x0 x2 x3 x1 (by linear_combination h); tauto)
  by_cases p03 : u0*w3 - u3*w0 ≠ 0
  · exact key _ _ _ _ u1 u2 u0 u3 w1 w2 w0 w3 h1 h2 h0 h3 (by linear_combination hB)
      (by linear_combination hX) p03
      (fun x0 x1 x2 x3 h => by have := H x2 x0 x1 x3 (by linear_combination h); tauto)
  by_cases p02 : u0*w2 - u2*w0 ≠ 0
  · exact key _ _ _ _ u1 u3 u0 u2 w1 w3 w0 w2 h1 h3 h0 h2 (by linear_combination hB)
      (by linear_combination hX) p02
      (fun x0 x1 x2 x3 h => by have := H x2 x0 x3 x1 (by linear_combination h); tauto)
  by_cases p01 : u0*w1 - u1*w0 ≠ 0
  · exact key _ _ _ _ u2 u3 u0 u1 w2 w3 w0 w1 h2 h3 h0 h1 (by linear_combination hB)
      (by linear_combination hX) p01
      (fun x0 x1 x2 x3 h => by have := H x2 x3 x0 x1 (by linear_combination h); tauto)
  push Not at p23 p13 p12 p03 p02 p01
  set c := a 0*w0^2 + a 1*w1^2 + a 2*w2^2 + a 3*w3^2 with hcdef
  have q0 : u0 * c = 0 := by
    rw [hcdef]; linear_combination w0 * hB + (a 1 * w1) * p01 + (a 2 * w2) * p02 + (a 3 * w3) * p03
  have q1 : u1 * c = 0 := by
    rw [hcdef]; linear_combination w1 * hB - (a 0 * w0) * p01 + (a 2 * w2) * p12 + (a 3 * w3) * p13
  have q2 : u2 * c = 0 := by
    rw [hcdef]; linear_combination w2 * hB - (a 0 * w0) * p02 - (a 1 * w1) * p12 + (a 3 * w3) * p23
  have q3 : u3 * c = 0 := by
    rw [hcdef]; linear_combination w3 * hB - (a 0 * w0) * p03 - (a 1 * w1) * p13 - (a 2 * w2) * p23
  have g0 := (mul_eq_zero.mp q0).resolve_right hc
  have g1 := (mul_eq_zero.mp q1).resolve_right hc
  have g2 := (mul_eq_zero.mp q2).resolve_right hc
  have g3 := (mul_eq_zero.mp q3).resolve_right hc
  subst g0 g1 g2 g3
  have : a 0 * a 1 * a 2 * a 3 * c = 0 := by linear_combination hX
  simp [h0, h1, h2, h3, hc] at this

end QuadFormsKB.FieldGen
