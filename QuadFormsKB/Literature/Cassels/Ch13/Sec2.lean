/-
# Cassels, Chapter 13, §§1–2: Hermite reduction of anisotropic forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Chapter 13, *Automorphs of integral forms*, §1
(Introduction, p. 284) and §2 (*Hermite reduction: anisotropic forms*, pp. 285–289).

**Conventions** (as in Chapter 12, `Literature/Cassels/Ch12/Basic.lean`). A real form is given by its symmetric matrix
$F = (f_{ij})$, $f(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ (`val`); $F \mapsto T^{\mathsf T}FT$ is the substitution
$f(T\vec{x})$ (`act`). Indices are 0-based. An *integral* form is an integer-valued form `IntQF n`
(the library's convention; Cassels' "integral" in §2 is the same, see the proof of Thm. 2.1, which only uses
$f(\vec{a}) \in \mathbb{Z}$ and $2f_{ij} \in \mathbb{Z}$); its real matrix is `realMat Q` $= \tfrac12 H$ ($H$ the Hessian),
so Cassels' determinant $d(f) = \det F$ is `(realMat Q).det`. Cassels' $O(f)$, the group of integral automorphs, is
`Siegel.Aut Q`; a *real automorph* is a real matrix $S$ with $f(S\vec{x}) = f(\vec{x})$, i.e. $S^{\mathsf T}FS = F$.
"Anisotropic" means anisotropic over $\mathbb{Q}$ (Cassels, p. 284): `¬ Q.IsotropicIn ℚ`.

**Name.** Cassels' "Hermite-reduced" form of this chapter (a form with a Minkowski-reduced Hermite majorant) is
`IsMajorantReduced`; the name `IsHermiteReduced` is taken by Hermite's reduction of *definite* forms
(Ch. 12, p. 259), a different notion (Cassels' footnote, p. 285).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### The real matrix of a form -/

/-- $T \in \mathrm{GL}_n(\mathbb{Z})$ is an integral automorph of $Q$ iff $T^{\mathsf T}FT = F$, $F$ the real matrix. -/
theorem mem_aut_iff_act (Q : IntQF n) (T : GL (Fin n) ℤ) :
    T ∈ Siegel.Aut Q ↔ act T.val (realMat Q) = realMat Q := by
  have h1 : act T.val (realMat Q) = (1 / 2 : ℝ) • (T.valᵀ * Q.hessian * T.val).map (algebraMap ℤ ℝ) := by
    rw [← halfHessian_compMat, QuadForm.hessian_compMat]
  have h2 : T ∈ Siegel.Aut Q ↔ T.valᵀ * Q.hessian * T.val = Q.hessian :=
    Siegel.eval_mulVec_eq_iff_hessian Q Q T.val
  rw [h2, h1]
  constructor
  · intro h; rw [h]
  · intro h
    have h3 := smul_right_injective (Matrix (Fin n) (Fin n) ℝ) (by norm_num : (1 / 2 : ℝ) ≠ 0) h
    ext i j
    have := congrFun (congrFun h3 i) j
    simpa using this

/-! ### Hermite majorants (pp. 285–286) -/

/-- **Hermite majorant** (Cassels, Ch. 13, §2, (2.1)–(2.2), pp. 285–286). Let $f$ be a real regular form, written as
$$f = L_1^2 + \cdots + L_l^2 - L_{l+1}^2 - \cdots - L_n^2 \tag{2.1}$$
with linearly independent real linear forms $L_1, \dots, L_n$. The positive definite form
$$g = L_1^2 + \cdots + L_n^2 \tag{2.2}$$
is a *Hermite majorant* of $f$. In matrices: $G$ is a Hermite majorant of $F$ iff there are an invertible real matrix
$L$ (whose rows are the $L_j$) and signs $\varepsilon_j = \pm 1$ with $F = L^{\mathsf T}\operatorname{diag}(\varepsilon)L$ and
$G = L^{\mathsf T}L$. Cassels puts the $l$ positive signs first; the order is immaterial (permute the $L_j$), so the
signs are allowed in any order here. -/
@[kb "cassels1978" "Ch. 13, §2, (2.1)–(2.2), pp. 285–286 (Hermite majorant)"]
def IsHermiteMajorant (F G : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (L : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ), IsUnit L.det ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
    F = Lᵀ * diagonal ε * L ∧ G = Lᵀ * L

/-- Helper: an invertible matrix has trivial kernel. -/
private theorem eq_zero_of_mulVec_eq_zero {L : Matrix (Fin n) (Fin n) ℝ} (hL : IsUnit L.det) {x : Fin n → ℝ}
    (h : L *ᵥ x = 0) : x = 0 := by
  have := congrArg (fun z => L⁻¹ *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hL] using this

/-- Helper: the value of $L^{\mathsf T}\operatorname{diag}(\varepsilon)L$ is $\sum_i \varepsilon_i (L\vec{y})_i^2$. -/
private theorem val_conj_diagonal (L : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) (y : Fin n → ℝ) :
    val (Lᵀ * diagonal ε * L) y = ∑ i, ε i * (L *ᵥ y) i ^ 2 := by
  rw [val_conj, val_diagonal]

/-- Helper: the value of $L^{\mathsf T}L$ is $\sum_i (L\vec{y})_i^2$. -/
private theorem val_gram (L : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    val (Lᵀ * L) y = ∑ i, (L *ᵥ y) i ^ 2 := by
  have : Lᵀ * L = Lᵀ * diagonal (fun _ : Fin n => (1 : ℝ)) * L := by simp
  rw [this, val_conj_diagonal]; simp

/-- A Hermite majorant is strictly positive definite ("Clearly $g(\vec{x})$ is positive definite", p. 286). -/
@[kb "cassels1978" "Ch. 13, §2, p. 286 (g is positive definite)"]
theorem IsHermiteMajorant.posDef {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G) : G.PosDef := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · show Gᵀ = G
    rw [hG, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [hG, val_gram]
    have hne : L *ᵥ x ≠ 0 := fun h => hx (eq_zero_of_mulVec_eq_zero hL h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hi' : (L *ᵥ x) i ≠ 0 := hi
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => (L *ᵥ x) i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i))

/-- **(2.3)** (Cassels, Ch. 13, p. 286): $d(g) = |d(f)|$ for a Hermite majorant $g$ of $f$. -/
@[kb "cassels1978" "Ch. 13, §2, (2.3), p. 286"]
theorem IsHermiteMajorant.det_eq {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G) :
    G.det = |F.det| := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  have hp : |∏ i, ε i| = 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => by rcases hε i with h | h <;> rw [h] <;> simp
  rw [hF, hG]
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, abs_mul, hp, mul_one, abs_mul_abs_self]

/-- **(2.4)** (Cassels, Ch. 13, p. 286): $|f(\vec{a})| \le g(\vec{a})$ for every $\vec{a} \in \mathbb{R}^n$, $g$ a Hermite
majorant of $f$. -/
@[kb "cassels1978" "Ch. 13, §2, (2.4), p. 286"]
theorem IsHermiteMajorant.abs_val_le {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G)
    (a : Fin n → ℝ) : |val F a| ≤ val G a := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  rw [hF, hG, val_conj_diagonal, val_gram]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_sq]
  rcases hε i with h | h <;> rw [h] <;> simp

/-- The matrix of a form with a Hermite majorant is symmetric and regular. -/
theorem IsHermiteMajorant.isSymm_det_ne_zero {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G) :
    F.IsSymm ∧ F.det ≠ 0 := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  refine ⟨?_, ?_⟩
  · show Fᵀ = F
    rw [hF]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [hF, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    have h1 : ∏ i, ε i ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => by rcases hε i with h | h <;> rw [h] <;> simp
    exact mul_ne_zero (mul_ne_zero hL.ne_zero h1) hL.ne_zero

/-- **Every real regular form has a Hermite majorant** ("Any real regular form $f(\vec{x})$ can be written, in many
ways, in the shape (2.1)", Cassels, Ch. 13, p. 285): for a real symmetric $F$ with $\det F \ne 0$ there is a Hermite
majorant (Sylvester's law of inertia; here via the spectral theorem). -/
@[kb "cassels1978" "Ch. 13, §2, (2.1), p. 285 (every regular form has the shape (2.1))"]
theorem exists_isHermiteMajorant {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    ∃ G, IsHermiteMajorant F G := by
  classical
  have hH : F.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hF
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  set lam := hH.eigenvalues with hlam
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hspec : F = U * diagonal lam * Uᵀ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hUdef, hlam, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hne : ∀ i, lam i ≠ 0 := by
    intro i h
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h)
  set s : Fin n → ℝ := fun i => Real.sqrt |lam i| with hs
  set ε : Fin n → ℝ := fun i => if 0 < lam i then 1 else -1 with hε
  refine ⟨_, diagonal s * Uᵀ, ε, ?_, ?_, ?_, rfl⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    have h1 : Uᵀ.det ≠ 0 := by
      intro h
      have := congrArg Matrix.det hUU
      rw [Matrix.det_mul, h] at this
      simp at this
    refine (isUnit_iff_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_) h1))
    have : 0 < |lam i| := abs_pos.2 (hne i)
    exact (Real.sqrt_pos.2 this).ne'
  · intro i
    simp only [hε]
    split_ifs <;> simp
  · rw [hspec]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    have : diagonal s * diagonal ε * diagonal s = diagonal lam := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      have h2 : s i * s i = |lam i| := Real.mul_self_sqrt (abs_nonneg _)
      simp only [hε]
      split_ifs with h
      · rw [mul_one, h2, abs_of_pos h]
      · rw [show s i * -1 * s i = -(s i * s i) by ring, h2, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i))]; ring
    calc U * diagonal lam * Uᵀ = U * (diagonal s * diagonal ε * diagonal s) * Uᵀ := by rw [this]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- **Substitution:** if $g$ is a Hermite majorant of $f$ and $T$ is a real invertible matrix, then $g(T\vec{x})$ is a
Hermite majorant of $f(T\vec{x})$ (used in the proofs of Lemma 2.1 and Theorem 2.2, pp. 286–287). -/
theorem IsHermiteMajorant.conj {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G)
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : IsUnit T.det) :     IsHermiteMajorant (Tᵀ * F * T) (Tᵀ * G * T) := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  refine ⟨L * T, ε, ?_, hε, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hL.mul hT
  · rw [hF]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [hG]; simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **Integral substitution** (`act`): if $g$ is a Hermite majorant of $f$ and $T \in \mathrm{GL}_n(\mathbb{Z})$, then
$g(T\vec{x})$ is a Hermite majorant of $f(T\vec{x})$. -/
theorem IsHermiteMajorant.act {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G) (T : GL (Fin n) ℤ) :
    IsHermiteMajorant (act T.val F) (act T.val G) := by
  refine h.conj ?_
  have h1 : castM T.val * castM T⁻¹.val = 1 := by
    rw [← castM_mul, Units.mul_inv, castM_one]
  exact Matrix.isUnit_det_of_right_inverse h1

/-- **Real automorphs move majorants** (Cassels, Ch. 13, proof of Thm. 2.2, p. 287): if $g$ is a Hermite majorant of
$f$ and $S$ is a real automorph of $f$ ($S^{\mathsf T}FS = F$, $S$ invertible), then $g(S\vec{x})$ is also a Hermite
majorant of $f$. -/
@[kb "cassels1978" "Ch. 13, §2, proof of Thm. 2.2, p. 287 (g(Sx) is a Hermite majorant of f)"]
theorem IsHermiteMajorant.of_automorph {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * F * S = F) (hSu : IsUnit S.det) :
    IsHermiteMajorant F (Sᵀ * G * S) := by
  have := h.conj hSu
  rwa [hS] at this

/-! ### Hermite-reduced forms -/

/-- **Hermite-reduced form** (Cassels, Ch. 13, §2, Definition, p. 286): a real regular form $f$ is *Hermite-reduced*
("or just reduced") if it has a Hermite majorant $g$ which is Minkowski-reduced (`IsMinkowskiReduced`, Ch. 12,
p. 255). Cassels notes the definition is "slightly unhistorical", Hermite used a different reduction of definite
forms; that one is `IsHermiteReduced` (Ch. 12, p. 259), not used here. -/
@[kb "cassels1978" "Ch. 13, §2, Definition, p. 286 (Hermite-reduced form)"]
def IsMajorantReduced (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ G, IsHermiteMajorant F G ∧ IsMinkowskiReduced G

/-- **Lemma 2.1** (Cassels, Ch. 13, §2, p. 286): every real regular form is integrally equivalent to a
Hermite-reduced form: for real symmetric $F$ with $\det F \ne 0$ there is $T \in \mathrm{GL}_n(\mathbb{Z})$ with
$f(T\vec{x})$ Hermite-reduced. -/
@[kb "cassels1978" "Ch. 13, §2, Lemma 2.1, p. 286"]
theorem exists_act_isMajorantReduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    ∃ T : GL (Fin n) ℤ, IsMajorantReduced (act T.val F) := by
  obtain ⟨G, hG⟩ := exists_isHermiteMajorant hF hdet
  obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hG.posDef
  exact ⟨T, _, hG.act T, hT⟩

/-! ### Theorem 2.1 and its corollaries (pp. 286–287) -/

/-! #### Integral forms: values and anisotropy (helpers) -/

/-- Helper: the integer value $Q(\vec{a})$ is the real value $f(\vec{a})$ of the real matrix. -/
private theorem cast_eval (Q : IntQF n) (a : Fin n → ℤ) :
    ((Q.eval a : ℤ) : ℝ) = val (realMat Q) (cast a) := by
  rw [← QuadForm.evalIn_real_eq_val]
  simp [QuadForm.evalIn, cast]

/-- Helper: the integer value $Q(\vec{a})$ is the rational value. -/
private theorem cast_eval_rat (Q : IntQF n) (a : Fin n → ℤ) :
    ((Q.eval a : ℤ) : ℚ) = Q.evalIn ℚ (fun i => (a i : ℚ)) := by
  simp [QuadForm.evalIn]

/-- Helper: an integral form takes no zero value on nonzero integral vectors. This is what anisotropy over $\mathbb{Q}$
gives (and all that is used). -/
private def AnisoInt (Q : IntQF n) : Prop := ∀ a : Fin n → ℤ, a ≠ 0 → Q.eval a ≠ 0

private theorem AnisoInt.of_not_isotropic {Q : IntQF n} (hQ : ¬ Q.IsotropicIn ℚ) : AnisoInt Q := by
  intro a ha h
  apply hQ
  refine ⟨fun i => (a i : ℚ), ?_, ?_⟩
  · intro h0
    apply ha
    funext i
    have := congrFun h0 i
    simpa using this
  · rw [← cast_eval_rat, h]; simp

private theorem AnisoInt.one_le_abs {Q : IntQF n} (hQ : AnisoInt Q) {a : Fin n → ℤ} (ha : a ≠ 0) :
    1 ≤ |val (realMat Q) (cast a)| := by
  rw [← cast_eval]
  have : (1 : ℤ) ≤ |Q.eval a| := Int.one_le_abs (hQ a ha)
  exact_mod_cast this

private theorem AnisoInt.one_le_val {Q : IntQF n} (hQ : AnisoInt Q) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : IsHermiteMajorant (realMat Q) G) {a : Fin n → ℤ} (ha : a ≠ 0) : 1 ≤ val G (cast a) :=
  (hQ.one_le_abs ha).trans (hG.abs_val_le _)

/-- **(2.5)–(2.6)** (Cassels, Ch. 13, proof of Thm. 2.1, p. 286): for an integral anisotropic form, $|f(\vec{a})| \ge 1$
for $\vec{a} \in \mathbb{Z}^n \setminus 0$, hence $g(\vec{a}) \ge 1$ for every Hermite majorant $g$. -/
@[kb "cassels1978" "Ch. 13, §2, (2.5)–(2.6), p. 286"]
theorem one_le_val_of_anisotropic {Q : IntQF n} (hQ : ¬ Q.IsotropicIn ℚ) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : IsHermiteMajorant (realMat Q) G) {a : Fin n → ℤ} (ha : a ≠ 0) :
    1 ≤ |val (realMat Q) (cast a)| ∧ 1 ≤ val G (cast a) :=
  ⟨(AnisoInt.of_not_isotropic hQ).one_le_abs ha, (AnisoInt.of_not_isotropic hQ).one_le_val hG ha⟩

/-- Helper: a family of reals that are all $\ge 1$ is bounded by its product. -/
private theorem le_prod_of_one_le {f : Fin n → ℝ} (h : ∀ i, 1 ≤ f i) (j : Fin n) : f j ≤ ∏ i, f i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have : 1 ≤ ∏ i ∈ Finset.univ.erase j, f i := by
    calc (1 : ℝ) = ∏ i ∈ Finset.univ.erase j, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => by norm_num) (fun i _ => h i)
  nlinarith [h j]

/-- Helper: $e_i^{\mathsf T}Ae_j = a_{ij}$. -/
private theorem single_dot_mulVec_single {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Pi.single i 1 : Fin n → R) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Helper: if $|a(z)| \le g(z)$ for all $z$ ($a$, $g$ symmetric), then
$|\vec{x}^{\mathsf T}A\vec{y}| \le (g(\vec{x}) + g(\vec{y}))/2$ (polarization and the parallelogram law). -/
private theorem abs_bilin_le {A G : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hG : G.IsSymm)
    (h : ∀ z, |val A z| ≤ val G z) (x y : Fin n → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ (val G x + val G y) / 2 := by
  have e1 := val_add hA x y
  have e2 := val_add hA x ((-1 : ℝ) • y)
  have e3 := val_add hG x y
  have e4 := val_add hG x ((-1 : ℝ) • y)
  simp only [val_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at e2 e4
  have h1 := abs_le.1 (h (x + y))
  have h2 := abs_le.1 (h (x + (-1 : ℝ) • y))
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- Helper (the core of Thm. 2.1, Cor. 1), stated for `AnisoInt`. -/
private theorem cor1_aux (n : ℕ) : ∃ C : ℝ, ∀ (Q : IntQF n), AnisoInt Q →
    ∀ G, IsHermiteMajorant (realMat Q) G → IsMinkowskiReduced G →
      ∀ i j, |realMat Q i j| ≤ C * |(realMat Q).det| ∧ |G i j| ≤ C * |(realMat Q).det| := by
  refine ⟨(9 / 4 : ℝ) ^ n * (n : ℝ) ^ n, fun Q hQ G hG hred i j => ?_⟩
  have hn : 0 < n := Fin.pos i
  have hpd := hG.posDef
  have hdet := hG.det_eq
  obtain ⟨m, hli, hm⟩ := exists_succMin_vectors hred.1
  have h1 : ∀ k, 1 ≤ succMin G k := by
    intro k
    have hk : m k ≠ 0 := by
      intro h0
      apply hli.ne_zero k
      rw [h0]; funext x; simp
    rw [← hm k]; exact hQ.one_le_val hG hk
  have hprod := prod_succMin_le hpd (hermiteConstantBound_n hn)
  rw [hdet] at hprod
  set B : ℝ := (9 / 4 : ℝ) ^ n * (n : ℝ) ^ n * |(realMat Q).det| with hB
  have hdiag : ∀ k, G k k ≤ B := by
    intro k
    have a1 := hred.diag_le_succMin k
    have a2 := le_prod_of_one_le h1 k
    have a3 : (9 / 4 : ℝ) ^ k.val ≤ (9 / 4) ^ n := pow_le_pow_right₀ (by norm_num) k.2.le
    calc G k k ≤ (9 / 4) ^ k.val * succMin G k := a1
      _ ≤ (9 / 4) ^ n * succMin G k := mul_le_mul_of_nonneg_right a3 (by linarith [h1 k])
      _ ≤ (9 / 4) ^ n * ((n : ℝ) ^ n * |(realMat Q).det|) :=
          mul_le_mul_of_nonneg_left (a2.trans hprod) (by positivity)
      _ = B := by rw [hB]; ring
  have hFs := hG.isSymm_det_ne_zero.1
  have hGs := ((posDef_iff G).1 hpd).1
  constructor
  · have := abs_bilin_le hFs hGs hG.abs_val_le (Pi.single i 1) (Pi.single j 1)
    rw [single_dot_mulVec_single, val_single, val_single] at this
    linarith [hdiag i, hdiag j]
  · have hnn : ∀ z, |val G z| ≤ val G z := fun z => by
      exact (abs_of_nonneg (((posSemidef_iff G).1 hpd.posSemidef).2 z)).le
    have := abs_bilin_le hGs hGs hnn (Pi.single i 1) (Pi.single j 1)
    rw [single_dot_mulVec_single, val_single, val_single] at this
    linarith [hdiag i, hdiag j]

/-- **Theorem 2.1, Corollary 1** (Cassels, Ch. 13, §2, p. 287): there is $C''$ depending only on $n$ such that the
coefficients of an integral anisotropic form $f$ and of a Minkowski-reduced Hermite majorant $g$ of $f$ are at most
$C''|d|$ in absolute value, $d = d(f)$. -/
@[kb "cassels1978" "Ch. 13, §2, Thm. 2.1, Cor. 1, p. 287"]
theorem isMajorantReduced_entry_bound (n : ℕ) : ∃ C : ℝ, ∀ (Q : IntQF n), ¬ Q.IsotropicIn ℚ →
    ∀ G, IsHermiteMajorant (realMat Q) G → IsMinkowskiReduced G →
      ∀ i j, |realMat Q i j| ≤ C * |(realMat Q).det| ∧ |G i j| ≤ C * |(realMat Q).det| := by
  obtain ⟨C, hC⟩ := cor1_aux n
  exact ⟨C, fun Q hQ => hC Q (AnisoInt.of_not_isotropic hQ)⟩

/-- Helper: a form is determined by its real matrix. -/
private theorem eq_of_realMat_eq {Q Q' : IntQF n} (h : realMat Q = realMat Q') : Q = Q' := by
  apply QuadForm.eq_of_eval_eq
  intro x
  have := cast_eval Q x
  rw [h, ← cast_eval] at this
  exact_mod_cast this

/-- Helper (the core of Thm. 2.1), stated for `AnisoInt`. -/
private theorem thm21_aux (n : ℕ) (d : ℝ) :
    {Q : IntQF n | AnisoInt Q ∧ (realMat Q).det = d ∧ IsMajorantReduced (realMat Q)}.Finite := by
  obtain ⟨C, hC⟩ := cor1_aux n
  set N : ℕ := ⌈2 * C * |d|⌉₊ with hN
  have hinj : Set.InjOn (fun Q : IntQF n => Q.hessian)
      {Q : IntQF n | AnisoInt Q ∧ (realMat Q).det = d ∧ IsMajorantReduced (realMat Q)} := by
    intro Q _ Q' _ h
    apply eq_of_realMat_eq
    show (1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ) = (1 / 2 : ℝ) • Q'.hessian.map (algebraMap ℤ ℝ)
    have h' : Q.hessian = Q'.hessian := h
    rw [h']
  refine Set.Finite.of_finite_image ?_ hinj
  have hfin : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Set.Icc (-(N : ℤ)) N).Finite :=
    Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro _ ⟨Q, ⟨hQ, hd, G, hG, hred⟩, rfl⟩ i _ j _
  have h1 := (hC Q hQ G hG hred i j).1
  rw [hd] at h1
  have h2 : realMat Q i j = (1 / 2 : ℝ) * ((Q.hessian i j : ℤ) : ℝ) := by
    simp [realMat]
  rw [h2, abs_mul] at h1
  have h3 : |((Q.hessian i j : ℤ) : ℝ)| ≤ N := by
    have := Nat.le_ceil (2 * C * |d|)
    rw [← hN] at this
    norm_num at h1
    linarith
  have h4 : |Q.hessian i j| ≤ N := by exact_mod_cast h3
  exact abs_le.1 h4

/-- **Theorem 2.1** (Cassels, Ch. 13, §2, pp. 286–287): there are only finitely many Hermite-reduced integral
anisotropic forms $f$ of given determinant $d \ne 0$. (Theorem 11.1, p. 322, removes "anisotropic" for classically
integral forms.) -/
@[kb "cassels1978" "Ch. 13, §2, Thm. 2.1, pp. 286–287"]
theorem finite_isMajorantReduced (n : ℕ) (d : ℝ) (_hd : d ≠ 0) :
    {Q : IntQF n | ¬ Q.IsotropicIn ℚ ∧ (realMat Q).det = d ∧ IsMajorantReduced (realMat Q)}.Finite :=
  (thm21_aux n d).subset fun _ ⟨h1, h2, h3⟩ => ⟨AnisoInt.of_not_isotropic h1, h2, h3⟩

/-- Helper: the real matrix of a nondegenerate form is symmetric with nonzero determinant. -/
private theorem realMat_symm_det {R : Type*} [CommRing R] [Algebra R ℝ]
    (hinj : Function.Injective (algebraMap R ℝ)) (Q : QuadForm R n) (hQ : Q.Nondegenerate) :
    (realMat Q).IsSymm ∧ (realMat Q).det ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have hs : Q.hessian.transpose = Q.hessian := by
      simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
    show ((1 / 2 : ℝ) • Q.hessian.map (algebraMap R ℝ))ᵀ = _
    rw [Matrix.transpose_smul, ← Matrix.transpose_map, hs]
  · have h1 : (Q.hessian.map (algebraMap R ℝ)).det = algebraMap R ℝ Q.hessian.det := by
      have := (algebraMap R ℝ).map_det Q.hessian
      simpa [RingHom.mapMatrix_apply] using this.symm
    rw [Matrix.det_smul, h1]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) fun h => hQ (hinj (by rw [h, map_zero]))

/-- Helper: $\operatorname{act}$ is linear in the form. -/
private theorem act_smul (T : Matrix (Fin n) (Fin n) ℤ) (c : ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    act T (c • F) = c • act T F := by
  unfold act
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- Helper: a positive multiple of a Hermite-reduced form is Hermite-reduced. -/
private theorem IsMajorantReduced.smul {F : Matrix (Fin n) (Fin n) ℝ} (h : IsMajorantReduced F) {c : ℝ}
    (hc : 0 < c) : IsMajorantReduced (c • F) := by
  obtain ⟨G, ⟨L, ε, hL, hε, hF, hG⟩, hred⟩ := h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  refine ⟨c • G, ⟨Real.sqrt c • L, ε, ?_, hε, ?_, ?_⟩, ?_⟩
  · rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hs.ne')).mul hL
  · rw [hF]
    simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss]
  · rw [hG]
    simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss]
  · have hval : ∀ x, val (c • G) x = c * val G x := fun x => by
      simp [val, Matrix.smul_mulVec, dotProduct_smul]
    refine ⟨?_, fun j e he => ?_⟩
    · rw [posDef_iff]
      obtain ⟨hs', hp⟩ := (posDef_iff G).1 hred.1
      refine ⟨?_, fun x hx => ?_⟩
      · show (c • G)ᵀ = c • G
        rw [Matrix.transpose_smul]; congr 1
      · rw [hval]; exact mul_pos hc (hp x hx)
    · have := hred.2 j e he
      rw [hval]
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left this hc.le

/-- Helper: substitution by $T \in \mathrm{GL}_n(\mathbb{Z})$ preserves `AnisoInt`. -/
private theorem AnisoInt.compMat {Q : IntQF n} (hQ : AnisoInt Q) (T : GL (Fin n) ℤ) :
    AnisoInt (Q.compMat T.val) := by
  intro a ha h
  rw [QuadForm.eval_compMat] at h
  refine hQ _ (fun h0 => ha ?_) h
  have := congrArg (fun z => T⁻¹.val *ᵥ z) h0
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this

/-- Helper: clearing denominators of a rational form. -/
private theorem exists_scale_intQF (Q : QuadForm ℚ n) :
    ∃ (N : ℕ) (Q' : IntQF n), 0 < N ∧ ∀ i j, ((Q'.coeff i j : ℤ) : ℚ) = N * Q.coeff i j := by
  classical
  set N : ℕ := ∏ i, ∏ j, (Q.coeff i j).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Rat.den_pos _
  have hz : ∀ i j, ∃ z : ℤ, (z : ℚ) = N * Q.coeff i j := by
    intro i j
    have hd : (Q.coeff i j).den ∣ N :=
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (Q.coeff i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hd
    refine ⟨k * (Q.coeff i j).num, ?_⟩
    have := Rat.den_mul_eq_num (Q.coeff i j)
    rw [hk]
    push_cast
    rw [← this]; ring
  choose z hz using hz
  refine ⟨N, ⟨Matrix.of z, ?_⟩, hNpos, fun i j => hz i j⟩
  intro i j hij
  have h0 : Q.coeff i j = 0 := Q.upper hij
  have := hz i j
  rw [h0, mul_zero] at this
  simpa using this

/-- Helper: the real matrix of the scaled integral form is the scaled real matrix. -/
private theorem realMat_scale {Q : QuadForm ℚ n} {Q' : IntQF n} {N : ℕ}
    (h : ∀ i j, ((Q'.coeff i j : ℤ) : ℚ) = N * Q.coeff i j) : realMat Q' = (N : ℝ) • realMat Q := by
  ext i j
  have h1 : ∀ i j, ((Q'.coeff i j : ℤ) : ℝ) = N * algebraMap ℚ ℝ (Q.coeff i j) := by
    intro i j
    have := congrArg (algebraMap ℚ ℝ) (h i j)
    simpa using this
  simp [realMat, QuadForm.hessian, h1]
  ring

/-- Helper: scaling a rational form by $N$ preserves anisotropy (in the `AnisoInt` form). -/
private theorem aniso_scale {Q : QuadForm ℚ n} {Q' : IntQF n} {N : ℕ} (hN : 0 < N)
    (h : ∀ i j, ((Q'.coeff i j : ℤ) : ℚ) = N * Q.coeff i j) (hQ : ¬ Q.IsotropicIn ℚ) : AnisoInt Q' := by
  intro a ha h0
  have h1 : Q'.evalIn ℚ (fun i => (a i : ℚ)) = N * Q.evalIn ℚ (fun i => (a i : ℚ)) := by
    simp only [QuadForm.evalIn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · simp only [algebraMap_int_eq, eq_intCast, Algebra.algebraMap_self, RingHom.id_apply, h]
      ring
    · simp
  apply hQ
  refine ⟨fun i => (a i : ℚ), ?_, ?_⟩
  · intro h2
    apply ha
    funext i
    have := congrFun h2 i
    simpa using this
  · have h3 := cast_eval_rat Q' a
    rw [h0, h1] at h3
    simp at h3
    rcases h3 with h3 | h3
    · omega
    · exact h3

/-- **Theorem 2.1, Corollary 2** (Cassels, Ch. 13, §2, p. 287): a regular anisotropic quadratic form $f$ with rational
coefficients is integrally equivalent to at least one and to at most finitely many Hermite-reduced forms. -/
@[kb "cassels1978" "Ch. 13, §2, Thm. 2.1, Cor. 2, p. 287"]
theorem finite_isMajorantReduced_rat (Q : QuadForm ℚ n) (hreg : Q.Nondegenerate) (hQ : ¬ Q.IsotropicIn ℚ) :
    {G | IsMajorantReduced G ∧ ∃ T : GL (Fin n) ℤ, G = act T.val (realMat Q)}.Nonempty ∧
      {G | IsMajorantReduced G ∧ ∃ T : GL (Fin n) ℤ, G = act T.val (realMat Q)}.Finite := by
  obtain ⟨hs, hdet⟩ := realMat_symm_det (algebraMap ℚ ℝ).injective Q hreg
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT⟩ := exists_act_isMajorantReduced hs hdet
    exact ⟨_, hT, T, rfl⟩
  · obtain ⟨N, Q', hN, hq⟩ := exists_scale_intQF Q
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hQ' := aniso_scale hN hq hQ
    have hsc := realMat_scale hq
    refine Set.Finite.of_finite_image ?_ (fun G _ G' _ h => smul_right_injective _ hNR.ne' h)
    refine ((thm21_aux n ((N : ℝ) ^ n * (realMat Q).det)).image realMat).subset ?_
    rintro _ ⟨G, ⟨hG, T, rfl⟩, rfl⟩
    have hc : realMat (Q'.compMat T.val) = (N : ℝ) • act T.val (realMat Q) := by
      have := halfHessian_compMat Q' T.val
      change realMat _ = act _ (realMat Q') at this
      rw [hsc, act_smul] at this
      exact this
    refine ⟨Q'.compMat T.val, ⟨hQ'.compMat T, ?_, ?_⟩, hc⟩
    · rw [hc, Matrix.det_smul, det_act]; simp
    · rw [hc]; exact hG.smul hNR

/-! ### Theorem 2.2 and its corollary (pp. 287–289) -/

/-- Helper: entries of a fixed matrix are bounded. -/
private theorem exists_entry_bound (A : Matrix (Fin n) (Fin n) ℝ) : ∃ m : ℝ, ∀ i j, |A i j| ≤ m := by
  refine ⟨∑ i, ∑ j, |A i j|, fun i j => ?_⟩
  calc |A i j| ≤ ∑ j, |A i j| :=
        Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, |A i j| :=
        Finset.single_le_sum (f := fun i => ∑ j, |A i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

/-- Helper: entrywise bound for a product. -/
private theorem entry_mul_le {A B : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ} (hA : ∀ i j, |A i j| ≤ a)
    (hB : ∀ i j, |B i j| ≤ b) (i j : Fin n) : |(A * B) i j| ≤ n * a * b := by
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |A i k * B k j| ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ((abs_nonneg _).trans (hA i k))
    _ = n * a * b := by simp [mul_assoc]

/-- Helper: a real automorph of a regular form has unit determinant. -/
private theorem isUnit_det_of_automorph {F S : Matrix (Fin n) (Fin n) ℝ} (hdet : F.det ≠ 0)
    (hS : Sᵀ * F * S = F) : IsUnit S.det := by
  have h := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have : S.det * S.det = 1 := by
    apply mul_right_cancel₀ hdet
    linarith [h]
  exact IsUnit.of_mul_eq_one _ this

/-- Helper: the inverse of a real automorph is a real automorph. -/
private theorem automorph_inv {F S : Matrix (Fin n) (Fin n) ℝ} (hdet : F.det ≠ 0)
    (hS : Sᵀ * F * S = F) : (S⁻¹)ᵀ * F * S⁻¹ = F := by
  have hu := isUnit_det_of_automorph hdet hS
  have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc (S⁻¹)ᵀ * F * S⁻¹ = (S⁻¹)ᵀ * (Sᵀ * F * S) * S⁻¹ := by rw [hS]
    _ = (S * S⁻¹)ᵀ * F * (S * S⁻¹) := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = F := by rw [h1]; simp

/-- Helper: a product of real automorphs is a real automorph. -/
private theorem automorph_mul {F S T : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * F * S = F)
    (hT : Tᵀ * F * T = F) : (S * T)ᵀ * F * (S * T) = F := by
  calc (S * T)ᵀ * F * (S * T) = Tᵀ * (Sᵀ * F * S) * T := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = F := by rw [hS, hT]

/-- Helper: the inverse of a real automorph is $F^{-1}S^{\mathsf T}F$. -/
private theorem automorph_inv_eq {F S : Matrix (Fin n) (Fin n) ℝ} (hdet : F.det ≠ 0)
    (hS : Sᵀ * F * S = F) : S⁻¹ = F⁻¹ * Sᵀ * F := by
  apply Matrix.inv_eq_left_inv
  calc F⁻¹ * Sᵀ * F * S = F⁻¹ * (Sᵀ * F * S) := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [hS]; exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)

/-- Helper: $\det(\mathrm{castM}\,T)$ is a unit for $T \in \mathrm{GL}_n(\mathbb{Z})$. -/
private theorem isUnit_det_castM (T : GL (Fin n) ℤ) : IsUnit (castM T.val).det := by
  have h1 : castM T.val * castM T⁻¹.val = 1 := by
    rw [← castM_mul, Units.mul_inv, castM_one]
  exact Matrix.isUnit_det_of_right_inverse h1

/-- Helper: $\operatorname{act}_U(S^{\mathsf T}GS) = (S U)^{\mathsf T}G(SU)$. -/
private theorem act_conj (U : Matrix (Fin n) (Fin n) ℤ) (S G : Matrix (Fin n) (Fin n) ℝ) :
    act U (Sᵀ * G * S) = (S * castM U)ᵀ * G * (S * castM U) := by
  unfold act; simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Helper: the data $(S, U)$ used in the proof of Thm. 2.2: $S$ a real automorph of $F$ = `realMat Q`, with
$\operatorname{act}_U F = \varphi$ and $\operatorname{act}_U(S^{\mathsf T}G_0S)$ Minkowski-reduced. -/
private def Good (Q : IntQF n) (G0 φ S : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℤ) : Prop :=
  Sᵀ * realMat Q * S = realMat Q ∧ act U.val (realMat Q) = φ ∧
    IsMinkowskiReduced (act U.val (Sᵀ * G0 * S))

/-- Helper: `act U (SᵀG₀S)` is a Hermite majorant of `act U F`. -/
private theorem good_majorant {Q : IntQF n} (hdet : (realMat Q).det ≠ 0) {G0 : Matrix (Fin n) (Fin n) ℝ}
    (hG0 : IsHermiteMajorant (realMat Q) G0) {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : Sᵀ * realMat Q * S = realMat Q) (U : GL (Fin n) ℤ) :
    IsHermiteMajorant (act U.val (realMat Q)) (act U.val (Sᵀ * G0 * S)) :=
  (hG0.of_automorph hS (isUnit_det_of_automorph hdet hS)).act U

/-- Helper: the diagonal entries of the reduced majorant are bounded (Thm. 2.1, Cor. 1). -/
private theorem good_diag_bound {Q : IntQF n} (hQ : AnisoInt Q) (hdet : (realMat Q).det ≠ 0)
    {G0 : Matrix (Fin n) (Fin n) ℝ} (hG0 : IsHermiteMajorant (realMat Q) G0) {C : ℝ}
    (hC : ∀ (Q : IntQF n), AnisoInt Q → ∀ G, IsHermiteMajorant (realMat Q) G → IsMinkowskiReduced G →
      ∀ i j, |realMat Q i j| ≤ C * |(realMat Q).det| ∧ |G i j| ≤ C * |(realMat Q).det|)
    {φ S : Matrix (Fin n) (Fin n) ℝ} {U : GL (Fin n) ℤ} (h : Good Q G0 φ S U) (j : Fin n) :
    act U.val (Sᵀ * G0 * S) j j ≤ C * |(realMat Q).det| := by
  have hc : realMat (Q.compMat U.val) = act U.val (realMat Q) := halfHessian_compMat Q U.val
  have hmaj := good_majorant hdet hG0 h.1 U
  rw [← hc] at hmaj
  have := (hC (Q.compMat U.val) (hQ.compMat U) _ hmaj h.2.2 j j).2
  rw [hc, det_act] at this
  exact (le_abs_self _).trans this

/-- Helper: for fixed $(S_1, U_1)$ there is a bound valid for all $(S, U)$ with the same $\varphi$ (the
estimate in the proof of Thm. 2.2). -/
private theorem lemmaB {Q : IntQF n} (hQ : AnisoInt Q) (hdet : (realMat Q).det ≠ 0)
    {G0 : Matrix (Fin n) (Fin n) ℝ} (hG0 : IsHermiteMajorant (realMat Q) G0) {C : ℝ}
    (hC : ∀ (Q : IntQF n), AnisoInt Q → ∀ G, IsHermiteMajorant (realMat Q) G → IsMinkowskiReduced G →
      ∀ i j, |realMat Q i j| ≤ C * |(realMat Q).det| ∧ |G i j| ≤ C * |(realMat Q).det|)
    {φ S₁ : Matrix (Fin n) (Fin n) ℝ} {U₁ : GL (Fin n) ℤ} (h₁ : Good Q G0 φ S₁ U₁) :
    ∃ k : ℝ, ∀ S U, Good Q G0 φ S U →
      ∃ W ∈ Siegel.Aut Q, ∀ i j, |(S * castM W.val) i j| ≤ k := by
  have hS₁u := isUnit_det_of_automorph hdet h₁.1
  set P : Matrix (Fin n) (Fin n) ℝ := S₁ * castM U₁.val with hP
  have hPu : IsUnit P.det := by rw [hP, Matrix.det_mul]; exact hS₁u.mul (isUnit_det_castM U₁)
  have hG₁ : (Pᵀ * G0 * P).PosDef := by
    have := h₁.2.2.1
    rwa [act_conj] at this
  obtain ⟨K₁, hK₁, hKx⟩ := exists_val_ge hG₁
  obtain ⟨mP, hmP⟩ := exists_entry_bound P
  obtain ⟨mY, hmY⟩ := exists_entry_bound (castM (U₁⁻¹ : GL (Fin n) ℤ).val)
  set K₀ : ℝ := C * |(realMat Q).det| with hK₀
  set kV : ℝ := 1 + K₀ / K₁ with hkV
  refine ⟨n * (n * mP * kV) * mY, fun S U hSU => ?_⟩
  set R : Matrix (Fin n) (Fin n) ℝ := S * castM U.val with hR
  set V : Matrix (Fin n) (Fin n) ℝ := P⁻¹ * R with hV
  have hPV : P * V = R := by rw [hV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
  refine ⟨U * U₁⁻¹, ?_, ?_⟩
  · rw [mem_aut_iff_act, Units.val_mul, act_mul, hSU.2.1, ← h₁.2.1, ← act_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, act_one]
  · have hh : act U.val (Sᵀ * G0 * S) = Vᵀ * (Pᵀ * G0 * P) * V := by
      rw [act_conj, ← hR, ← hPV]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have hVb : ∀ i j, |V i j| ≤ kV := by
      intro i j
      have h1 := good_diag_bound hQ hdet hG0 hC hSU j
      rw [hh, ← val_single (Vᵀ * (Pᵀ * G0 * P) * V) j, val_conj] at h1
      have h2 := hKx (V *ᵥ Pi.single j 1)
      have h3 : (V *ᵥ Pi.single j 1) i = V i j := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      have h4 : (V *ᵥ (Pi.single j 1 : Fin n → ℝ)) i ^ 2 ≤ ∑ i, (V *ᵥ (Pi.single j 1 : Fin n → ℝ)) i ^ 2 :=
        Finset.single_le_sum (f := fun i => (V *ᵥ (Pi.single j 1 : Fin n → ℝ)) i ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
      rw [h3] at h4
      have h5 : V i j ^ 2 ≤ K₀ / K₁ := by
        rw [le_div_iff₀ hK₁]
        have : K₁ * V i j ^ 2 ≤ K₁ * ∑ i, (V *ᵥ (Pi.single j 1 : Fin n → ℝ)) i ^ 2 :=
          mul_le_mul_of_nonneg_left h4 hK₁.le
        linarith
      rw [hkV]
      nlinarith [abs_nonneg (V i j), sq_abs (V i j)]
    have hW : S * castM (U * U₁⁻¹).val = (P * V) * castM (U₁⁻¹ : GL (Fin n) ℤ).val := by
      rw [hPV, hR, Units.val_mul, castM_mul, Matrix.mul_assoc]
    intro i j
    rw [hW]
    exact entry_mul_le (entry_mul_le hmP hVb) hmY i j

/-- Helper: the one-sided form of Thm. 2.2: for every real automorph $S$ there is $W \in O(f)$ with $SW$ bounded
uniformly. -/
private theorem claimA {Q : IntQF n} (hQ : AnisoInt Q) (hs : (realMat Q).IsSymm) (hdet : (realMat Q).det ≠ 0) :
    ∃ k : ℝ, ∀ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * realMat Q * S = realMat Q →
      ∃ W ∈ Siegel.Aut Q, ∀ i j, |(S * castM W.val) i j| ≤ k := by
  classical
  obtain ⟨C, hC⟩ := cor1_aux n
  obtain ⟨G0, hG0⟩ := exists_isHermiteMajorant hs hdet
  set Φ : Set (Matrix (Fin n) (Fin n) ℝ) := realMat '' {Q' : IntQF n | AnisoInt Q' ∧
    (realMat Q').det = (realMat Q).det ∧ IsMajorantReduced (realMat Q')} with hΦdef
  have hΦ : Φ.Finite := (thm21_aux n _).image _
  have hex : ∀ φ ∈ Φ, ∃ k : ℝ, ∀ S U, Good Q G0 φ S U →
      ∃ W ∈ Siegel.Aut Q, ∀ i j, |(S * castM W.val) i j| ≤ k := by
    intro φ _
    by_cases h : ∃ S₁ U₁, Good Q G0 φ S₁ U₁
    · obtain ⟨S₁, U₁, h₁⟩ := h
      exact lemmaB hQ hdet hG0 hC h₁
    · exact ⟨0, fun S U hg => absurd ⟨S, U, hg⟩ h⟩
  choose! f hf using hex
  refine ⟨∑ φ ∈ hΦ.toFinset, |f φ|, fun S hS => ?_⟩
  have hSu := isUnit_det_of_automorph hdet hS
  obtain ⟨U, hU⟩ := exists_isMinkowskiReduced (hG0.of_automorph hS hSu).posDef
  have hg : Good Q G0 (act U.val (realMat Q)) S U := ⟨hS, rfl, hU⟩
  have hc : realMat (Q.compMat U.val) = act U.val (realMat Q) := halfHessian_compMat Q U.val
  have hmem : act U.val (realMat Q) ∈ Φ := by
    refine ⟨Q.compMat U.val, ⟨hQ.compMat U, ?_, ?_⟩, hc⟩
    · rw [hc, det_act]
    · rw [hc]; exact ⟨_, good_majorant hdet hG0 hS U, hU⟩
  obtain ⟨W, hW, h⟩ := hf _ hmem S U hg
  refine ⟨W, hW, fun i j => (h i j).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun φ => |f φ|) (fun _ _ => abs_nonneg _)
    (hΦ.mem_toFinset.2 hmem))

/-- **Theorem 2.2** (Cassels, Ch. 13, §2, pp. 287–288): let $f$ be integral, regular and anisotropic. There is a
constant $k$ depending only on $f$ such that for every real automorph $S$ of $f$ there are integral automorphs
$T, W \in O(f)$ such that all the elements of $TS^{-1}$ and $S^{-1}W$ are at most $k$ in absolute value.
(Cassels' Note: false for every isotropic $f$; e.g. $x_1x_2$.) A real automorph is a real $S$ with
$S^{\mathsf T}FS = F$; it is invertible because $F$ is. *Update* (gap): Cassels reduces
$T$ to $W$ by "$(TS^{-1})^{-1} = ST^{-1}$"; the bound on $TS^{-1} = (SW_1)^{-1}$ needs that the inverse of an automorph
$M$ is $F^{-1}M^{\mathsf T}F$, so its entries are bounded in terms of those of $M$ and of $F$. -/
@[kb "cassels1978" "Ch. 13, §2, Thm. 2.2, pp. 287–288"]
theorem exists_aut_mul_bounded (Q : IntQF n) (hreg : Q.Nondegenerate) (hQ : ¬ Q.IsotropicIn ℚ) :
    ∃ k : ℝ, ∀ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * realMat Q * S = realMat Q →
      ∃ T ∈ Siegel.Aut Q, ∃ W ∈ Siegel.Aut Q,
        ∀ i j, |(castM T.val * S⁻¹) i j| ≤ k ∧ |(S⁻¹ * castM W.val) i j| ≤ k := by
  have hAn := AnisoInt.of_not_isotropic hQ
  obtain ⟨hs, hdet⟩ := realMat_symm_det (algebraMap ℤ ℝ).injective_int Q hreg
  obtain ⟨k₀, hk₀⟩ := claimA hAn hs hdet
  obtain ⟨m₁, hm₁⟩ := exists_entry_bound (realMat Q)⁻¹
  obtain ⟨m₂, hm₂⟩ := exists_entry_bound (realMat Q)
  refine ⟨max k₀ (n * (n * m₁ * k₀) * m₂), fun S hS => ?_⟩
  obtain ⟨W₂, hW₂, h₂⟩ := hk₀ S⁻¹ (automorph_inv hdet hS)
  obtain ⟨W₁, hW₁, h₁⟩ := hk₀ S hS
  refine ⟨W₁⁻¹, inv_mem hW₁, W₂, hW₂, fun i j => ⟨?_, (h₂ i j).trans (le_max_left _ _)⟩⟩
  have hW₁' : (castM W₁.val)ᵀ * realMat Q * castM W₁.val = realMat Q := (mem_aut_iff_act Q W₁).1 hW₁
  have hMaut := automorph_mul hS hW₁'
  have h1 : castM (W₁⁻¹).val = (castM W₁.val)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← castM_mul, Units.inv_mul, castM_one]
  have h2 : castM (W₁⁻¹).val * S⁻¹ = (S * castM W₁.val)⁻¹ := by
    rw [h1, Matrix.mul_inv_rev]
  rw [h2, automorph_inv_eq hdet hMaut]
  refine (entry_mul_le (entry_mul_le hm₁ (fun i j => ?_)) hm₂ i j).trans (le_max_right _ _)
  rw [Matrix.transpose_apply]
  exact h₁ j i

/-- Helper: the reflection (symmetry) $\tau_c(\vec{x}) = \vec{x} - \frac{2B(\vec{x},\vec{c})}{f(\vec{c})}\vec{c}$ as a
matrix. -/
private noncomputable def reflMat (F : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - (2 / val F c) * c i * (F *ᵥ c) j

private theorem reflMat_mulVec (F : Matrix (Fin n) (Fin n) ℝ) (c x : Fin n → ℝ) :
    reflMat F c *ᵥ x = x - (2 / val F c * (x ⬝ᵥ (F *ᵥ c))) • c := by
  ext i
  simp only [reflMat, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ j, (if i = j then (1 : ℝ) else 0) * x j = x i := by simp
  rw [this]
  congr 1
  conv_rhs => rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Helper: a reflection in a non-isotropic vector is a real automorph. -/
private theorem reflMat_automorph {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) {c : Fin n → ℝ}
    (hc : val F c ≠ 0) : (reflMat F c)ᵀ * F * reflMat F c = F := by
  have hb : ∀ x y : Fin n → ℝ, x ⬝ᵥ (((reflMat F c)ᵀ * F * reflMat F c) *ᵥ y) =
      (reflMat F c *ᵥ x) ⬝ᵥ (F *ᵥ (reflMat F c *ᵥ y)) := by
    intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hcc : c ⬝ᵥ (F *ᵥ c) = val F c := rfl
  ext i j
  have h1 := hb (Pi.single i 1) (Pi.single j 1)
  rw [single_dot_mulVec_single] at h1
  rw [h1, reflMat_mulVec, reflMat_mulVec]
  have e1 : ∀ x : Fin n → ℝ, c ⬝ᵥ (F *ᵥ x) = x ⬝ᵥ (F *ᵥ c) := fun x => bilin_comm hs x c
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, e1, hcc]
  rw [← single_dot_mulVec_single F i j]
  field_simp
  ring

/-- Helper: two ways of expanding $f(\vec{a} - \vec{b})$ and $f(\vec{a}+\vec{b})$. -/
private theorem val_sub_eq {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) (a b : Fin n → ℝ) :
    val F (a - b) = val F a - 2 * (a ⬝ᵥ (F *ᵥ b)) + val F b := by
  have := bilin_comm hs a b
  simp only [val, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  linarith

/-- Helper: a real automorph moving $\vec{b}$ to $\vec{a}$ when $f(\vec{a}) = f(\vec{b}) \ne 0$ (at most two
symmetries, replacing Witt's theorem). -/
private theorem exists_automorph_move {F : Matrix (Fin n) (Fin n) ℝ} (hs : F.IsSymm) {a b : Fin n → ℝ}
    (hab : val F a = val F b) (h0 : val F a ≠ 0) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * F * S = F ∧ S *ᵥ b = a := by
  have e1 := bilin_comm hs a b
  have hsub := val_sub_eq hs a b
  have hadd := val_add hs a b
  by_cases h : val F (a - b) = 0
  · have hp : val F (a + b) ≠ 0 := by
      intro h'
      apply h0
      linarith
    refine ⟨reflMat F a * reflMat F (a + b), automorph_mul (reflMat_automorph hs h0) (reflMat_automorph hs hp), ?_⟩
    have hB : b ⬝ᵥ (F *ᵥ (a + b)) = b ⬝ᵥ (F *ᵥ a) + val F b := by
      simp [Matrix.mulVec_add, dotProduct_add, val]
    rw [← Matrix.mulVec_mulVec, reflMat_mulVec, reflMat_mulVec]
    have h2 : 2 / val F (a + b) * (b ⬝ᵥ (F *ᵥ (a + b))) = 1 := by
      rw [hB]; field_simp; linarith
    rw [h2, one_smul, show b - (a + b) = -a by abel, neg_dotProduct, show a ⬝ᵥ (F *ᵥ a) = val F a from rfl]
    have h4 : 2 / val F a * -val F a = -2 := by field_simp
    rw [h4]
    ext i
    simp
    ring
  · refine ⟨reflMat F (a - b), reflMat_automorph hs h, ?_⟩
    rw [reflMat_mulVec]
    have hB : b ⬝ᵥ (F *ᵥ (a - b)) = b ⬝ᵥ (F *ᵥ a) - val F b := by
      simp [Matrix.mulVec_sub, dotProduct_sub, val]
    have h2 : 2 / val F (a - b) * (b ⬝ᵥ (F *ᵥ (a - b))) = -1 := by
      rw [hB]; field_simp; linarith
    rw [h2]
    simp

/-- **Theorem 2.2, Corollary** (Cassels, Ch. 13, §2, p. 289): for $f$ integral, regular and anisotropic there is
$C = C(f)$ such that for every $\vec{b} \in \mathbb{R}^n$ with $f(\vec{b}) \ne 0$ some integral automorph $T$ of $f$ has
$$\lVert T\vec{b}\rVert \le C|f(\vec{b})|^{1/2}, \qquad \lVert\vec{x}\rVert = \max_i |x_i|.$$
Cassels' proof moves $\vec{b}$ to a multiple of a fixed vector by a real automorph (Witt's theorem, Ch. 2, Thm. 4.1);
here this is done with at most two symmetries. -/
@[kb "cassels1978" "Ch. 13, §2, Thm. 2.2, Cor., p. 289"]
theorem exists_aut_mulVec_le (Q : IntQF n) (hreg : Q.Nondegenerate) (hQ : ¬ Q.IsotropicIn ℚ) :
    ∃ C : ℝ, ∀ b : Fin n → ℝ, val (realMat Q) b ≠ 0 →
      ∃ T ∈ Siegel.Aut Q, ∀ i, |(castM T.val *ᵥ b) i| ≤ C * √|val (realMat Q) b| := by
  classical
  obtain ⟨hs, hdet⟩ := realMat_symm_det (algebraMap ℤ ℝ).injective_int Q hreg
  obtain ⟨k, hk⟩ := exists_aut_mul_bounded Q hreg hQ
  set F := realMat Q with hF
  let a : ℝ → Fin n → ℝ := fun σ => if h : ∃ x, val F x = σ then h.choose else 0
  have ha : ∀ σ, (∃ x, val F x = σ) → val F (a σ) = σ := by
    intro σ h
    simp only [a, dif_pos h]
    exact h.choose_spec
  obtain ⟨A₁, hA₁⟩ : ∃ A : ℝ, ∀ j, |a 1 j| ≤ A :=
    ⟨∑ j, |a 1 j|, fun j => Finset.single_le_sum (f := fun j => |a 1 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : ℝ, ∀ j, |a (-1) j| ≤ A :=
    ⟨∑ j, |a (-1) j|, fun j => Finset.single_le_sum (f := fun j => |a (-1) j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)⟩
  set A : ℝ := max (max A₁ A₂) 0 with hA
  set k' : ℝ := max k 0 with hk'
  refine ⟨n * k' * A, fun b hb => ?_⟩
  set r : ℝ := √|val F b| with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (abs_pos.2 hb)
  have hr2 : r ^ 2 = |val F b| := Real.sq_sqrt (abs_nonneg _)
  set σ : ℝ := if 0 < val F b then 1 else -1 with hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by
    by_cases h : 0 < val F b
    · left; simp [hσ, h]
    · right; simp [hσ, h]
  have hσ0 : σ ≠ 0 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
  set b' : Fin n → ℝ := r⁻¹ • b with hb'
  have hvb' : val F b' = σ := by
    rw [hb', val_smul, inv_pow, hr2]
    by_cases h : 0 < val F b
    · rw [hσ, if_pos h, abs_of_pos h]; field_simp
    · rw [hσ, if_neg h, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hb)]; field_simp
  have haσ : val F (a σ) = σ := ha σ ⟨b', hvb'⟩
  obtain ⟨S, hS, hSb⟩ := exists_automorph_move hs (haσ.trans hvb'.symm) (by rw [haσ]; exact hσ0)
  have hSu := isUnit_det_of_automorph hdet hS
  obtain ⟨T, hT, W, hW, hTS⟩ := hk S hS
  refine ⟨T, hT, fun i => ?_⟩
  have hb'S : b' = S⁻¹ *ᵥ a σ := by
    rw [← hSb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mulVec]
  have hbb : b = r • b' := by
    rw [hb', smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hTb : castM T.val *ᵥ b = r • ((castM T.val * S⁻¹) *ᵥ a σ) := by
    rw [hbb, Matrix.mulVec_smul, hb'S, Matrix.mulVec_mulVec]
  have haj : ∀ j, |a σ j| ≤ A := by
    intro j
    rcases hσ1 with h | h <;> rw [h]
    · exact (hA₁ j).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hA₂ j).trans ((le_max_right _ _).trans (le_max_left _ _))
  rw [hTb, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr0, mul_comm (n * k' * A) r]
  refine mul_le_mul_of_nonneg_left ?_ hr0.le
  rw [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |(castM T.val * S⁻¹) i j * a σ j| ≤ ∑ _j : Fin n, k' * A := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul ((hTS i j).1.trans (le_max_left _ _)) (haj j) (abs_nonneg _)
          ((abs_nonneg _).trans ((hTS i j).1.trans (le_max_left _ _)))
    _ = n * k' * A := by simp [mul_assoc]

end QuadFormsKB.Reduction
