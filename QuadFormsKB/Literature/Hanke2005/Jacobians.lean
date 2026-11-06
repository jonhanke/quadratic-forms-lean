/-
# Hanke 2005, the Jacobians of §2 and of the appendix: (2.10) and Lemmas A2–A5

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Translation of the wedge-product statements.** Hanke's Lemmas A2–A5 and (2.10) compare top wedge products of
linear combinations of linearly independent differentials: if $\omega'_i = \sum_jM_{ij}\omega_j$ then
$\bigwedge_i\omega'_i = \det(M)\bigwedge_i\omega_i$. They are therefore statements about the determinant of a linear
map, which is how they are stated here (`LinearMap.det`). In Lemmas A3 and A5 the phrase "plus terms containing at least
one factor $dx_{ik}$ with $i > k$" (resp. the skew-symmetry of $dx$) means that only the coordinates $dx_{ik}$ with
$i\le k$ (resp. $i > k$) are kept: the linear map is restricted to, and projected onto, those coordinates.

**Indices.** Hanke's matrices are indexed by $1,\dots,n$; here by `Fin n` ($0,\dots,n-1$). Hanke's $\det_l(A)$, the
determinant of the upper left $l\times l$ block ($1\le l\le n$), is `detLead A l` with `l : Fin (n + 1)`
(`detLead A 0 = 1`).

**Defines** `detLead`, the symmetric matrices `symMat`, the skew-symmetric matrices `skewMat`, the congruence map
`congrSym A` ($t\mapsto{}^tAtA$ on symmetric matrices, Hanke's $[A]$), `congrSkew A`, and the coordinate maps of
Lemmas A3 and A5.

**Proves** (2.10) `det_congrSym`, Lemma A2 `det_mulLeft_rect` / `det_mulRight_rect`, Lemma A3 `det_upperMulLeft`,
Lemma A4 `det_congrSkew`, Lemma A5 `det_skewMulRight`.
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

variable {K : Type*} [Field K] {n : ℕ}

/-- **Hanke's $\det_l(A)$** (thesis, Summary of Notation, p. 3): the determinant of the upper left $l\times l$
submatrix of an $n\times n$ matrix $A$, here for `l : Fin (n + 1)`, i.e. $0\le l\le n$, with $\det_0(A) = 1$ (Hanke
uses $1\le l\le n$). In 0-based indices it is the minor on the rows and columns $0,\dots,l-1$. -/
@[kb "hanke2005crelle" "Summary of Notation, p. 3 (det_l(A))"]
def detLead (A : Matrix (Fin n) (Fin n) K) (l : Fin (n + 1)) : K :=
  (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det

/-- The symmetric $n\times n$ matrices over $K$, Hanke's $T$ (thesis, Summary of Notation, p. 3). -/
@[kb "hanke2005crelle" "Summary of Notation, p. 3 (T = symmetric matrices)"]
def symMat (K : Type*) [Field K] (n : ℕ) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {t | tᵀ = t}
  add_mem' := by intro a b ha hb; simp_all [Matrix.transpose_add]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all [Matrix.transpose_smul]

/-- The skew-symmetric $n\times n$ matrices over $K$ (the matrices $dx$ of Lemmas A4, A5). -/
def skewMat (K : Type*) [Field K] (n : ℕ) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {t | tᵀ = -t}
  add_mem' := by intro a b ha hb; simp_all [Matrix.transpose_add, add_comm]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all [Matrix.transpose_smul]

/-- **Hanke's $[A]$** (thesis, proof of Lemma 2.2, p. 6): $[A](t) = {}^tAtA$ on the symmetric matrices, the change of
basis by $A$ for the quadratic form with matrix $t$. -/
@[kb "hanke2005crelle" "proof of Lemma 2.2, p. 6 ([A](t) = tA t A)"]
def congrSym (A : Matrix (Fin n) (Fin n) K) : symMat K n →ₗ[K] symMat K n where
  toFun t := ⟨Aᵀ * (t : Matrix (Fin n) (Fin n) K) * A, by
    show (Aᵀ * (t : Matrix (Fin n) (Fin n) K) * A)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, t.2, Matrix.mul_assoc]⟩
  map_add' s t := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c t := by ext1; simp

theorem prod_subtype_ite {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p] (G : α → K) :
    ∏ q : {q // p q}, G q.1 = ∏ q, if p q then G q else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter p) (by simp) G).symm

theorem diag_mul_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    diagonal (Function.update (1 : Fin n → K) i 2) * transvection i j c =
      transvection i j (2 * c) * diagonal (Function.update (1 : Fin n → K) i 2) := by
  classical
  ext a b
  simp only [transvection, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
  by_cases hai : a = i
  · subst hai
    by_cases hbj : b = j
    · subst hbj; simp [hij, Ne.symm hij]
    · by_cases hba : b = a
      · subst hba; simp [Ne.symm hij]
      · simp [hba, Ne.symm hba]
  · by_cases hab : a = b
    · subst hab; simp [hai, Ne.symm hai]
    · simp [hai, hab, Ne.symm hai]

/-- A multiplicative function on square matrices over a field of characteristic $0$ that is $\det(\cdot)^m$
on diagonal matrices is $\det(\cdot)^m$ everywhere (diagonal and transvection decomposition). -/
theorem eq_det_pow_of_mul [CharZero K] (m : ℕ) (f : Matrix (Fin n) (Fin n) K → K)
    (hmul : ∀ A B, f (A * B) = f A * f B) (h1 : f 1 = 1)
    (hdiag : ∀ d : Fin n → K, f (diagonal d) = (∏ i, d i) ^ m) (A : Matrix (Fin n) (Fin n) K) :
    f A = A.det ^ m := by
  classical
  have hT : ∀ (i j : Fin n), i ≠ j → ∀ c : K, f (transvection i j c) = 1 := by
    intro i j hij c
    have hD : f (diagonal (Function.update (1 : Fin n → K) i 2)) ≠ 0 := by
      rw [hdiag]
      have : ∏ x, Function.update (1 : Fin n → K) i 2 x = 2 := by
        rw [Finset.prod_update_of_mem (Finset.mem_univ i)]; simp
      rw [this]; exact pow_ne_zero _ two_ne_zero
    have hcomm := diag_mul_transvection i j hij c
    have h2 : f (transvection i j (2 * c)) = f (transvection i j c) := by
      apply mul_right_cancel₀ hD
      rw [← hmul, ← hcomm, hmul, mul_comm]
    have h3 : f (transvection i j (2 * c)) = f (transvection i j c) * f (transvection i j c) := by
      rw [← hmul, transvection_mul_transvection_same _ _ hij, two_mul]
    have h4 : f (transvection i j c) * f (transvection i j (-c)) = 1 := by
      rw [← hmul, transvection_mul_transvection_same _ _ hij, add_neg_cancel, transvection_zero, h1]
    have h5 : f (transvection i j c) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h4; exact zero_ne_one h4
    apply mul_left_cancel₀ h5
    rw [mul_one, ← h3, h2]
  refine Matrix.diagonal_transvection_induction (fun A => f A = A.det ^ m) A ?_ ?_ ?_
  · intro D hD
    rw [hdiag, det_diagonal]
  · intro t
    rw [Matrix.TransvectionStruct.toMatrix, hT t.i t.j t.hij, Matrix.det_transvection_of_ne _ _ t.hij]
    simp
  · intro A B hA hB
    rw [hmul, hA, hB, det_mul, mul_pow]

theorem det_eq_of_intertwine {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] V) (e : V ≃ₗ[K] W) (g : W →ₗ[K] W) (h : ∀ v, e (f v) = g (e v)) :
    LinearMap.det f = LinearMap.det g := by
  rw [← LinearMap.det_conj f e]
  congr 1
  apply LinearMap.ext; intro w
  simp [h]

theorem congrSym_mul (A B : Matrix (Fin n) (Fin n) K) :
    congrSym (A * B) = congrSym B ∘ₗ congrSym A := by
  apply LinearMap.ext; intro t
  apply Subtype.ext
  show (A * B)ᵀ * (t : Matrix (Fin n) (Fin n) K) * (A * B) =
    Bᵀ * (Aᵀ * (t : Matrix (Fin n) (Fin n) K) * A) * B
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem congrSym_one : congrSym (1 : Matrix (Fin n) (Fin n) K) = LinearMap.id := by
  apply LinearMap.ext; intro t
  apply Subtype.ext
  show (1 : Matrix (Fin n) (Fin n) K)ᵀ * (t : Matrix (Fin n) (Fin n) K) * 1 = t
  simp

/-- The coordinates $(t_{ik})_{i\le k}$ of a symmetric matrix. -/
def symCoord : symMat K n →ₗ[K] ({p : Fin n × Fin n // p.1 ≤ p.2} → K) where
  toFun t p := (t : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symCoord_bijective : Function.Bijective (symCoord (K := K) (n := n)) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    ext i j
    have hs : ∀ i j, (s : Matrix (Fin n) (Fin n) K) j i = (s : Matrix (Fin n) (Fin n) K) i j :=
      fun i j => congrFun (congrFun s.2 i) j
    have ht : ∀ i j, (t : Matrix (Fin n) (Fin n) K) j i = (t : Matrix (Fin n) (Fin n) K) i j :=
      fun i j => congrFun (congrFun t.2 i) j
    rcases le_total i j with h | h
    · exact congrFun hst ⟨(i, j), h⟩
    · rw [← hs, ← ht]; exact congrFun hst ⟨(j, i), h⟩
  · intro y
    refine ⟨⟨fun i j => if h : i ≤ j then y ⟨(i, j), h⟩ else y ⟨(j, i), (not_le.mp h).le⟩, ?_⟩, ?_⟩
    · ext i j
      show (if h : j ≤ i then y ⟨(j, i), h⟩ else y ⟨(i, j), (not_le.mp h).le⟩) =
        (if h : i ≤ j then y ⟨(i, j), h⟩ else y ⟨(j, i), (not_le.mp h).le⟩)
      by_cases h1 : i ≤ j <;> by_cases h2 : j ≤ i
      · have : i = j := le_antisymm h1 h2
        subst this; simp
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd (le_total i j) (by simp [h1, h2])
    · funext p
      show (if h : p.1.1 ≤ p.1.2 then y ⟨(p.1.1, p.1.2), h⟩ else _) = y p
      simp [p.2]

theorem prod_up (d : Fin n → K) :
    ∏ p : {p : Fin n × Fin n // p.1 ≤ p.2}, (d p.1.1 * d p.1.2) = (∏ i, d i) ^ (n + 1) := by
  rw [Finset.prod_mul_distrib]
  have e1 : ∏ p : {p : Fin n × Fin n // p.1 ≤ p.2}, d p.1.1 = ∏ i : Fin n, d i ^ (n - i.val) := by
    rw [prod_subtype_ite (p := fun q : Fin n × Fin n => q.1 ≤ q.2) (fun q => d q.1),
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun j : Fin n => i ≤ j) = Finset.Ici i by ext; simp, Fin.card_Ici]
  have e2 : ∏ p : {p : Fin n × Fin n // p.1 ≤ p.2}, d p.1.2 = ∏ j : Fin n, d j ^ (j.val + 1) := by
    rw [prod_subtype_ite (p := fun q : Fin n × Fin n => q.1 ≤ q.2) (fun q => d q.2),
      Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun i : Fin n => i ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]
  rw [e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  have := i.2
  omega

theorem det_congrSym_diag (d : Fin n → K) :
    LinearMap.det (congrSym (diagonal d)) = (∏ i, d i) ^ (n + 1) := by
  classical
  let e := LinearEquiv.ofBijective (symCoord (K := K) (n := n)) symCoord_bijective
  rw [det_eq_of_intertwine (congrSym (diagonal d)) e
    (Matrix.toLin' (diagonal fun p : {p : Fin n × Fin n // p.1 ≤ p.2} => d p.1.1 * d p.1.2)), 
    LinearMap.det_toLin', det_diagonal, prod_up]
  intro t
  funext p
  show (((diagonal d)ᵀ * (t : Matrix (Fin n) (Fin n) K) * diagonal d) p.1.1 p.1.2) =
    (Matrix.mulVec (diagonal fun p : {p : Fin n × Fin n // p.1 ≤ p.2} => d p.1.1 * d p.1.2)
      (symCoord t)) p
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change _ = _ * (t : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  ring

/-- **(2.10)** (Hanke thesis, p. 7): $[A]^*(\omega_T) = \det(A)^{n+1}\,\omega_T$, i.e.
$\bigwedge_{i\le j}d({}^tAtA)_{ij} = \det(A)^{n+1}\bigwedge_{i\le j}dt_{ij}$: the linear map $t\mapsto{}^tAtA$ on the
symmetric $n\times n$ matrices has determinant $\det(A)^{n+1}$. (Stated over a field of characteristic $0$, the case
used: $\mathbb R$, $\mathbb C$ and the completions $k_\mathfrak p$.) -/
@[kb "hanke2005crelle" "(2.10), p. 7"]
theorem det_congrSym [CharZero K] (A : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (congrSym A) = A.det ^ (n + 1) := by
  refine eq_det_pow_of_mul (n + 1) (fun A => LinearMap.det (congrSym A)) ?_ ?_ ?_ A
  · intro A B
    simp only [congrSym_mul, LinearMap.det_comp, mul_comm]
  · simp [congrSym_one]
  · exact det_congrSym_diag

/-- Left multiplication $x\mapsto ax$ on $r\times t$ matrices. -/
def mulLeftRect {r t : ℕ} (a : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r) (Fin t) K →ₗ[K] Matrix (Fin r) (Fin t) K where
  toFun x := a * x
  map_add' x y := Matrix.mul_add a x y
  map_smul' c x := by simp

/-- Right multiplication $x\mapsto xa'$ on $r\times t$ matrices. -/
def mulRightRect {r t : ℕ} (a' : Matrix (Fin t) (Fin t) K) :
    Matrix (Fin r) (Fin t) K →ₗ[K] Matrix (Fin r) (Fin t) K where
  toFun x := x * a'
  map_add' x y := Matrix.add_mul x y a'
  map_smul' c x := by simp

theorem det_mulRightAux {r t : ℕ} (a' : Matrix (Fin t) (Fin t) K) :
    LinearMap.det (mulRightRect (r := r) a') = a'.det ^ r := by
  have h : (mulRightRect (r := r) a' : (Fin r → Fin t → K) →ₗ[K] (Fin r → Fin t → K)) =
      (LinearMap.pi fun i => (Matrix.toLin' a'ᵀ) ∘ₗ LinearMap.proj i) := by
    ext x i j
    show (x * a') i j = (Matrix.toLin' a'ᵀ (x i)) j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  have e : LinearMap.det (LinearMap.pi fun i => (Matrix.toLin' a'ᵀ) ∘ₗ LinearMap.proj i :
      (Fin r → Fin t → K) →ₗ[K] (Fin r → Fin t → K)) = a'.det ^ r := by
    rw [LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [LinearMap.det_toLin']
  rw [← h] at e
  exact e

/-- **Lemma A2, first part** (Hanke thesis, p. 21): if $dx' = a\,(dx)$ for $r\times t$ matrices of differentials and a
constant $r\times r$ matrix $a$, then $\bigwedge_{i,k}dx'_{ik} = \det(a)^t\bigwedge_{i,k}dx_{ik}$: left multiplication
by $a$ on $r\times t$ matrices has determinant $\det(a)^t$. -/
@[kb "hanke2005crelle" "Lemma A2, p. 21"]
theorem det_mulLeftRect {r t : ℕ} (a : Matrix (Fin r) (Fin r) K) :
    LinearMap.det (mulLeftRect (t := t) a) = a.det ^ t := by
  have h : ((Matrix.transposeLinearEquiv (Fin r) (Fin t) K K : _ ≃ₗ[K] _) : _ →ₗ[K] _) ∘ₗ
      mulLeftRect (t := t) a ∘ₗ
      ((Matrix.transposeLinearEquiv (Fin r) (Fin t) K K).symm : _ →ₗ[K] _) = mulRightRect (r := t) aᵀ := by
    ext x i j
    simp [mulLeftRect, mulRightRect, Matrix.mul_apply, mul_comm]
  have := LinearMap.det_conj (mulLeftRect (t := t) a) (Matrix.transposeLinearEquiv (Fin r) (Fin t) K K)
  rw [h, det_mulRightAux, det_transpose] at this
  exact this.symm

/-- **Lemma A2, second part** (Hanke thesis, p. 21): if $dx' = (dx)\,a'$ for a constant $t\times t$ matrix $a'$, then
$\bigwedge_{i,k}dx'_{ik} = \det(a')^r\bigwedge_{i,k}dx_{ik}$. -/
@[kb "hanke2005crelle" "Lemma A2, p. 21"]
theorem det_mulRightRect {r t : ℕ} (a' : Matrix (Fin t) (Fin t) K) :
    LinearMap.det (mulRightRect (r := r) a') = a'.det ^ r := by
  exact det_mulRightAux a'

/-- The upper triangular coordinates $\{(i,k) : i\le k\}$ (Hanke's $i\le k$). -/
abbrev UpIdx (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The strictly lower triangular coordinates $\{(i,k) : i > k\}$ (Hanke's $i > k$). -/
abbrev LowIdx (n : ℕ) := {p : Fin n × Fin n // p.2 < p.1}

/-- The upper triangular matrix with entries $y_{ik}$ ($i\le k$) and $0$ below the diagonal. -/
def upMat (y : UpIdx n → K) : Matrix (Fin n) (Fin n) K :=
  fun i k => if h : i ≤ k then y ⟨(i, k), h⟩ else 0

/-- The skew-symmetric matrix with strictly lower entries $y_{ik}$ ($i > k$): $x_{ik} = y_{ik}$, $x_{ki} = -y_{ik}$,
$x_{ii} = 0$. -/
def skewOf (y : LowIdx n → K) : Matrix (Fin n) (Fin n) K :=
  fun i k => if h : k < i then y ⟨(i, k), h⟩ else if h' : i < k then -y ⟨(k, i), h'⟩ else 0

/-- **The map of Lemma A3**: $y\mapsto\big((a\cdot\mathrm{up}(y))_{ik}\big)_{i\le k}$, i.e. $dx\mapsto a\,dx$ with only the
coordinates $dx_{ik}$, $i\le k$, kept. -/
def upperMulLeft (a : Matrix (Fin n) (Fin n) K) : (UpIdx n → K) →ₗ[K] (UpIdx n → K) where
  toFun y p := (a * upMat y) p.1.1 p.1.2
  map_add' y z := by
    funext p
    simp only [Pi.add_apply]
    rw [show upMat (y + z) = upMat y + upMat z by
      funext i k; simp only [upMat, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp]
    rw [Matrix.mul_add, Matrix.add_apply]
  map_smul' c y := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show upMat (c • y) = c • upMat y by
      funext i k; simp only [upMat, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp]
    rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

theorem sum_subtype_ite {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p] (G : α → K) :
    ∑ q : {q // p q}, G q.1 = ∑ q, if p q then G q else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) G).symm

/-- Equivalence of the column-`k` block of `UpIdx n` with `Fin (k+1)`. -/
def upBlockEquiv (k : Fin n) : {p : UpIdx n // p.1.2 = k} ≃ Fin (k.succ : Fin (n + 1)).val where
  toFun p := ⟨p.1.1.1.val, by
    have := p.1.2; have h2 := p.2; rw [h2] at this
    simp only [Fin.val_succ]; have := Fin.le_def.mp this; omega⟩
  invFun j := ⟨⟨(Fin.castLE (k.succ : Fin (n + 1)).is_le j, k), by
    rw [Fin.le_def]; have := j.2; simp only [Fin.val_succ] at this; simp; omega⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · rfl
    · exact p.2.symm
  right_inv j := rfl

/-- Equivalence of the row-`i` block of `LowIdx n` with `Fin i`. -/
def lowBlockEquiv (i : Fin n) : {p : LowIdx n // p.1.1 = i} ≃ Fin (i.castSucc : Fin (n + 1)).val where
  toFun p := ⟨p.1.1.2.val, by
    have := p.1.2; have h2 := p.2; rw [h2] at this
    simp only [Fin.val_castSucc]; exact Fin.lt_def.mp this⟩
  invFun j := ⟨⟨(i, Fin.castLE (i.castSucc : Fin (n + 1)).is_le j), by
    rw [Fin.lt_def]; have := j.2; simp only [Fin.val_castSucc] at this; simp⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · exact p.2.symm
    · rfl
  right_inv j := rfl

/-- **Lemma A3** (Hanke thesis, pp. 21–22): if $dx' = a\,(dx)$ for $n\times n$ matrices of linearly independent
differentials and a constant matrix $a$, then
$$\bigwedge_{i\le k}dx'_{ik} = \prod_{l=1}^n\det_l(a)\bigwedge_{i\le k}dx_{ik} + (\text{terms containing some } dx_{ik},\ i>k).$$
Here: the map `upperMulLeft a` has determinant $\prod_{l=1}^n\det_l(a)$ (`l.succ` runs over $1,\dots,n$). -/
@[kb "hanke2005crelle" "Lemma A3, pp. 21–22"]
theorem det_upperMulLeft (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (upperMulLeft a) = ∏ l : Fin n, detLead a l.succ := by
  classical
  set M : Matrix (UpIdx n) (UpIdx n) K := fun p q => if q.1.2 = p.1.2 then a p.1.1 q.1.1 else 0 with hM
  have key : ∀ (y : UpIdx n → K) (p : UpIdx n), (a * upMat y) p.1.1 p.1.2 = ∑ q, M p q * y q := by
    intro y p
    have h1 : ∀ q : UpIdx n, M p q * y q =
        (fun q : Fin n × Fin n => (if q.2 = p.1.2 then a p.1.1 q.1 else 0) * upMat y q.1 q.2) q.1 := by
      intro q
      simp [hM, upMat, q.2]
    simp_rw [h1]
    rw [sum_subtype_ite (p := fun q : Fin n × Fin n => q.1 ≤ q.2)
      (fun q : Fin n × Fin n => (if q.2 = p.1.2 then a p.1.1 q.1 else 0) * upMat y q.1 q.2)]
    have h2 : ∀ q : Fin n × Fin n, (if q.1 ≤ q.2 then
        (if q.2 = p.1.2 then a p.1.1 q.1 else 0) * upMat y q.1 q.2 else 0) =
        (if q.2 = p.1.2 then a p.1.1 q.1 else 0) * upMat y q.1 q.2 := by
      intro q
      by_cases h : q.1 ≤ q.2
      · simp [h]
      · simp [h, upMat]
    simp_rw [h2]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.mul_apply]
  have hL : upperMulLeft a = Matrix.toLin' M := by
    apply LinearMap.ext; intro y; funext p
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    exact key y p
  have hT : M.BlockTriangular (fun p : UpIdx n => p.1.2) := by
    intro p q h
    simp [hM, h.ne]
  rw [hL, LinearMap.det_toLin', hT.det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [detLead, ← Matrix.det_submatrix_equiv_self (upBlockEquiv k)]
  congr 1
  ext p q
  simp only [Matrix.submatrix_apply]
  show M p.1 q.1 = _
  rw [hM]
  show (if q.1.1.2 = p.1.1.2 then a p.1.1.1 q.1.1.1 else 0) = _
  have hc : q.1.1.2 = p.1.1.2 := by rw [q.2, p.2]
  simp only [hc, ite_true]
  rfl

/-- The congruence $x\mapsto{}^tax\,a$ on skew-symmetric matrices (the map of Lemma A4). -/
def congrSkew (a : Matrix (Fin n) (Fin n) K) : skewMat K n →ₗ[K] skewMat K n where
  toFun x := ⟨aᵀ * (x : Matrix (Fin n) (Fin n) K) * a, by
    show (aᵀ * (x : Matrix (Fin n) (Fin n) K) * a)ᵀ = -(aᵀ * (x : Matrix (Fin n) (Fin n) K) * a)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, x.2, Matrix.mul_assoc]
    simp⟩
  map_add' s t := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c t := by ext1; simp

theorem congrSkew_mul (A B : Matrix (Fin n) (Fin n) K) :
    congrSkew (A * B) = congrSkew B ∘ₗ congrSkew A := by
  apply LinearMap.ext; intro t
  apply Subtype.ext
  show (A * B)ᵀ * (t : Matrix (Fin n) (Fin n) K) * (A * B) =
    Bᵀ * (Aᵀ * (t : Matrix (Fin n) (Fin n) K) * A) * B
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem congrSkew_one : congrSkew (1 : Matrix (Fin n) (Fin n) K) = LinearMap.id := by
  apply LinearMap.ext; intro t
  apply Subtype.ext
  show (1 : Matrix (Fin n) (Fin n) K)ᵀ * (t : Matrix (Fin n) (Fin n) K) * 1 = t
  simp

/-- The coordinates $(t_{ik})_{i>k}$ of a skew-symmetric matrix. -/
def skewCoord : skewMat K n →ₗ[K] (LowIdx n → K) where
  toFun t p := (t : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem skewOf_mem (y : LowIdx n → K) : skewOf y ∈ skewMat K n := by
  show (skewOf y)ᵀ = -skewOf y
  ext i j
  show skewOf y j i = -skewOf y i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewOf, h, not_lt.mpr h.le]
  · subst h; simp [skewOf]
  · simp [skewOf, h, not_lt.mpr h.le]

theorem skewCoord_bijective [CharZero K] : Function.Bijective (skewCoord (K := K) (n := n)) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    ext i j
    have hs : ∀ i j, (s : Matrix (Fin n) (Fin n) K) j i = -(s : Matrix (Fin n) (Fin n) K) i j :=
      fun i j => congrFun (congrFun s.2 i) j
    have ht : ∀ i j, (t : Matrix (Fin n) (Fin n) K) j i = -(t : Matrix (Fin n) (Fin n) K) i j :=
      fun i j => congrFun (congrFun t.2 i) j
    rcases lt_trichotomy i j with h | h | h
    · have this : (s : Matrix (Fin n) (Fin n) K) j i = (t : Matrix (Fin n) (Fin n) K) j i :=
        congrFun hst ⟨(j, i), h⟩
      have h1 := hs j i
      have h2 := ht j i
      linear_combination h1 - h2 - this
    · subst h
      have h1 := hs i i
      have h2 := ht i i
      have e1 : (s : Matrix (Fin n) (Fin n) K) i i = 0 := self_eq_neg.mp h1
      have e2 : (t : Matrix (Fin n) (Fin n) K) i i = 0 := self_eq_neg.mp h2
      rw [e1, e2]
    · exact congrFun hst ⟨(i, j), h⟩
  · intro y
    refine ⟨⟨skewOf y, skewOf_mem y⟩, ?_⟩
    funext p
    show skewOf y p.1.1 p.1.2 = y p
    simp [skewOf, p.2]

theorem prod_low (d : Fin n → K) :
    ∏ p : LowIdx n, (d p.1.1 * d p.1.2) = (∏ i, d i) ^ (n - 1) := by
  rw [Finset.prod_mul_distrib]
  have e1 : ∏ p : LowIdx n, d p.1.1 = ∏ i : Fin n, d i ^ i.val := by
    rw [prod_subtype_ite (p := fun q : Fin n × Fin n => q.2 < q.1) (fun q => d q.1),
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i by ext; simp, Fin.card_Iio]
  have e2 : ∏ p : LowIdx n, d p.1.2 = ∏ j : Fin n, d j ^ (n - 1 - j.val) := by
    rw [prod_subtype_ite (p := fun q : Fin n × Fin n => q.2 < q.1) (fun q => d q.2),
      Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun i : Fin n => j < i) = Finset.Ioi j by ext; simp, Fin.card_Ioi]
  rw [e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  have := i.2
  omega

theorem det_congrSkew_diag [CharZero K] (d : Fin n → K) :
    LinearMap.det (congrSkew (diagonal d)) = (∏ i, d i) ^ (n - 1) := by
  classical
  let e := LinearEquiv.ofBijective (skewCoord (K := K) (n := n)) skewCoord_bijective
  rw [det_eq_of_intertwine (congrSkew (diagonal d)) e
    (Matrix.toLin' (diagonal fun p : LowIdx n => d p.1.1 * d p.1.2)),
    LinearMap.det_toLin', det_diagonal, prod_low]
  intro t
  funext p
  show (((diagonal d)ᵀ * (t : Matrix (Fin n) (Fin n) K) * diagonal d) p.1.1 p.1.2) =
    (Matrix.mulVec (diagonal fun p : LowIdx n => d p.1.1 * d p.1.2) (skewCoord t)) p
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change _ = _ * (t : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
  ring

/-- **Lemma A4** (Hanke thesis, p. 22): if $dx$, $dx'$ are skew-symmetric $n\times n$ matrices of differentials with
linearly independent upper triangular coordinates and $dx' = {}^ta\,(dx)\,a$ for a constant matrix $a$, then
$\bigwedge_{i>k}dx'_{ik} = \det(a)^{n-1}\bigwedge_{i>k}dx_{ik}$: the congruence by $a$ on skew-symmetric matrices has
determinant $\det(a)^{n-1}$. (Characteristic $0$, as for (2.10).) -/
@[kb "hanke2005crelle" "Lemma A4, p. 22"]
theorem det_congrSkew [CharZero K] (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (congrSkew a) = a.det ^ (n - 1) := by
  refine eq_det_pow_of_mul (n - 1) (fun A => LinearMap.det (congrSkew A)) ?_ ?_ ?_ a
  · intro A B
    simp only [congrSkew_mul, LinearMap.det_comp, mul_comm]
  · simp [congrSkew_one]
  · exact det_congrSkew_diag

/-- **The map of Lemma A5**: $y\mapsto\big((\mathrm{skew}(y)\,a)_{ik}\big)_{i>k}$, i.e. $dx\mapsto(dx)\,a$ on skew-symmetric
$dx$ with only the coordinates $i > k$ of the product kept. -/
def skewMulRight (a : Matrix (Fin n) (Fin n) K) : (LowIdx n → K) →ₗ[K] (LowIdx n → K) where
  toFun y p := (skewOf y * a) p.1.1 p.1.2
  map_add' y z := by
    funext p
    simp only [Pi.add_apply]
    rw [show skewOf (y + z) = skewOf y + skewOf z by
      funext i k; simp only [skewOf, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp [add_comm]]
    rw [Matrix.add_mul, Matrix.add_apply]
  map_smul' c y := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show skewOf (c • y) = c • skewOf y by
      funext i k; simp only [skewOf, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp]
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- **Lemma A5** (Hanke thesis, p. 23): if $dx$ is a skew-symmetric $n\times n$ matrix of differentials with linearly
independent coordinates and $dx' = (dx)\,a$ for a constant matrix $a$, then
$\bigwedge_{i>k}dx'_{ik} = \prod_{l=1}^{n-1}\det_l(a)\bigwedge_{i>k}dx_{ik}$. Here: `skewMulRight a` has determinant
$\prod_{l=0}^{n-1}\det_l(a) = \prod_{l=1}^{n-1}\det_l(a)$ (`l.castSucc` runs over $0,\dots,n-1$; $\det_0 = 1$).
*Update:* Hanke also assumes that $dx'$ is skew-symmetric; this is not needed. -/
@[kb "hanke2005crelle" "Lemma A5, p. 23"]
theorem det_skewMulRight (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (skewMulRight a) = ∏ l : Fin n, detLead a l.castSucc := by
  classical
  set M : Matrix (LowIdx n) (LowIdx n) K := fun p q =>
    (if q.1.1 = p.1.1 then a q.1.2 p.1.2 else 0) + (if q.1.2 = p.1.1 then -a q.1.1 p.1.2 else 0) with hM
  have key : ∀ (y : LowIdx n → K) (p : LowIdx n), (skewOf y * a) p.1.1 p.1.2 = ∑ q, M p q * y q := by
    intro y p
    set Y : Fin n × Fin n → K := fun q => if h : q.2 < q.1 then y ⟨q, h⟩ else 0 with hY
    set G : Fin n × Fin n → K := fun q =>
      (if q.1 = p.1.1 then a q.2 p.1.2 else 0) * Y q + (if q.2 = p.1.1 then -a q.1 p.1.2 else 0) * Y q with hG
    have h1 : ∀ q : LowIdx n, M p q * y q = G q.1 := by
      intro q
      simp [hM, hG, hY, q.2, add_mul]
    simp_rw [h1]
    rw [sum_subtype_ite (p := fun q : Fin n × Fin n => q.2 < q.1) G]
    have h2 : ∀ q : Fin n × Fin n, (if q.2 < q.1 then G q else 0) = G q := by
      intro q
      by_cases h : q.2 < q.1
      · simp [h]
      · simp [h, hG, hY]
    simp_rw [h2]
    have h3 : ∀ i j : Fin n, skewOf y i j = Y (i, j) - Y (j, i) := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · simp [skewOf, hY, h, not_lt.mpr h.le]
      · subst h; simp [skewOf, hY]
      · simp [skewOf, hY, h, not_lt.mpr h.le]
    simp only [hG, Finset.sum_add_distrib, Fintype.sum_prod_type]
    simp [Matrix.mul_apply, h3, mul_comm, neg_mul]
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => mul_sub _ _ _
  have hL : skewMulRight a = Matrix.toLin' M := by
    apply LinearMap.ext; intro y; funext p
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    exact key y p
  have hT : M.BlockTriangular (fun p : LowIdx n => p.1.1) := by
    intro p q h
    have h' : q.1.2 < p.1.1 := q.2.trans h
    simp [hM, h.ne, h'.ne]
  rw [hL, LinearMap.det_toLin', hT.det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [detLead, ← Matrix.det_transpose, ← Matrix.det_submatrix_equiv_self (lowBlockEquiv k)]
  congr 1
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
  show M q.1 p.1 = _
  rw [hM]
  show (if p.1.1.1 = q.1.1.1 then a p.1.1.2 q.1.1.2 else 0) +
    (if p.1.1.2 = q.1.1.1 then -a p.1.1.1 q.1.1.2 else 0) = _
  have hq : p.1.1.2 ≠ q.1.1.1 := by
    intro h
    have h1 := Fin.lt_def.mp p.1.2
    have e1 := congrArg Fin.val p.2
    have e2 := congrArg Fin.val q.2
    have e3 := congrArg Fin.val h
    omega
  have hc : p.1.1.1 = q.1.1.1 := by rw [p.2, q.2]
  simp [hc, hq]
  rfl

end QuadFormsKB.Hanke2005
