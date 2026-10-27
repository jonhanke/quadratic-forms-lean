/-
# Cassels, Chapter 9, §6: the weight of a genus and Lemma 6.2

**Layer:** classically integral forms (`IsClassicallyIntegral`), positive definite (`IntQF.PosDef`), in $n = m + 1$
variables (the associated forms have $m = n - 1$ variables); Cassels' matrix $(f_{ij}) = H/2$ (`casselsMat`); proper
classes `PClass` and proper automorphs `AutPlus` (`Ch9Sec1.lean`), $o^{+}(f) = \lvert O^{+}(f)\rvert$; primitive
representations `primRepSet` (`Ch9Sec6.lean`).

**Defines**
* `ofGram A`: the form $\mathbf x^{\mathsf T}A\mathbf x$ of a symmetric integral matrix $A$;
* `assocGram f a T`, `assocClass f b` ((6.8)): for a primitive representation $b$ of $a$ and $T \in \mathrm{SL}_n(\mathbb Z)$
  with first column $b$, $h = f(T\mathbf x)$ satisfies $ah(\mathbf x) = (ax_1 + c_2x_2 + \dots + c_nx_n)^2 +
  g(x_2, \dots, x_n)$ with $g_{ij} = ah_{ij} - h_{1i}h_{1j}$; the representation is *associated* with the proper class
  of $g$;
* `pgenusClasses f`, `pweight f` ((6.9)): the proper classes of the genus and the weight $W(\mathcal F) =
  \sum 1/o^{+}(f)$ over them;
* `rhoCount f a G` ((6.10)): Cassels' $\rho$, the number of $\mathbf c \bmod a$ for which the form $h$ of (6.8) with
  given $g$ is integral and lies in the genus of $f$;
* `sigmaWeight f a C`, `sigmaGenus f a g` ((6.11)): the sum of the weights $1/o^{+}(f')$ of the primitive representations
  of $a$ by representatives $f'$ of the proper classes of the genus of $f$ associated with the proper class $C$, resp.
  with the proper classes of the genus of $g$.

**Proves**
* (6.8) the associated proper class does not depend on the completion of $b$ to a basis (`assocGram_properIntEquiv`);
* footnote to (6.9) (`pweight_eq_two_mul_mass`): $W(\mathcal F)$ is twice the library's mass $\sum 1/o(f)$ over
  $\mathrm{GL}_n(\mathbb Z)$-classes;
* Lemma 6.2 for one proper class (`sigmaWeight_eq`): $\sigma(a, \mathcal F, [g]) = \rho(\mathcal F, g)/o^{+}(g)$ — the
  content of (6.13)–(6.33);
* Lemma 6.2 (`sigmaGenus_eq`): $\sigma(a, \mathcal F, \mathcal G) = \rho\,W(\mathcal G)$ when $\rho(\mathcal F, g) = \rho$
  for every $g$ in the genus $\mathcal G$. Cassels shows this constancy (6.10) from Lemma 4.2, Corollary 1, and
  Lemma 4.3; Lemma 4.3 is not formalized, so the constancy is a hypothesis here.

*Proof of the one-class identity (Cassels' orbit–stabilizer count, as a double count):* let $C$ be a set of
representatives of $(\mathbb Z/a)^m$ and $H_g = \{h_{\mathbf c, g} : \mathbf c \in C\}$. For each representative $f'$
count the pairs $T \in \mathrm{SL}_n(\mathbb Z)$ with $f'(T\mathbf x) \in H_g$: grouping by $h$ gives
$o^{+}(f')\cdot\#\{\mathbf c : h_{\mathbf c, g} \sim^{+} f'\}$, grouping by the first column $b = Te_1$ gives
$o^{+}(g)\cdot\#\{b \text{ primitive}, f'(b) = a, b \text{ associated with } [g]\}$ (the matrices with first column $b$
are $T_b\begin{pmatrix}1 & \mathbf u^{\mathsf T}\\ 0 & S\end{pmatrix}$, and exactly one $\mathbf u$ per $S \in O^{+}(g)$
lands in $H_g$); summing over $f'$ gives the identity.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec6
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Siegel.Mass

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {m k : ℕ}

/-! ### Forms from Gram matrices -/

/-- **The form of a symmetric integral matrix** $A$: $\mathbf x \mapsto \mathbf x^{\mathsf T}A\mathbf x =
\sum_i A_{ii}x_i^2 + \sum_{i<j}(A_{ij} + A_{ji})x_ix_j$ (classically integral when $A$ is symmetric). -/
def ofGram (A : Matrix (Fin k) (Fin k) ℤ) : QuadForm ℤ k :=
  QuadForm.ofUpper fun i j => if i = j then A i i else A i j + A j i

/-- The Hessian of `ofGram A` is $A + A^{\mathsf T}$. -/
theorem hessian_ofGram (A : Matrix (Fin k) (Fin k) ℤ) : (ofGram A).hessian = A + Aᵀ := by
  ext i j
  simp only [ofGram, QuadForm.ofUpper, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.mpr h, h.ne]
  · simp
  · rw [ite_eq_right (not_le.mpr h), ite_eq_left h.le, ite_eq_right h.ne, zero_add, add_comm]

theorem eval_ofGram {A : Matrix (Fin k) (Fin k) ℤ} (_hA : A.IsSymm) (x : Fin k → ℤ) :
    (ofGram A).eval x = x ⬝ᵥ (A *ᵥ x) := by
  -- symmetry of `A` is not needed: the Hessian of `ofGram A` is `A + Aᵀ`
  have h2 := LocalDensity.two_mul_eval_eq_hessian (ofGram A) x
  rw [hessian_ofGram, add_mulVec, dotProduct_add, dotProduct_mulVec_transpose_self] at h2
  linarith

/-- **Cassels' matrix** $(f_{ij}) = H/2$ of a classically integral form ($f = \sum_{i,j} f_{ij}x_ix_j$). -/
def casselsMat (f : QuadForm ℤ k) : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => f.hessian i j / 2

/-- A classically integral form has even Hessian entries. -/
theorem two_dvd_hessian_of_ci {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) (i j : Fin k) :
    (2 : ℤ) ∣ f.hessian i j := by
  rw [isClassicallyIntegral_iff] at hf
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [f.upper h, add_zero]; exact even_iff_two_dvd.mp (hf i j h)
  · subst h; exact ⟨f.coeff i i, by ring⟩
  · rw [f.upper h, zero_add]; exact even_iff_two_dvd.mp (hf j i h)

/-- Even Hessian entries imply classical integrality. -/
theorem ci_of_two_dvd_hessian {f : QuadForm ℤ k} (h : ∀ i j, (2 : ℤ) ∣ f.hessian i j) :
    IsClassicallyIntegral f := by
  rw [isClassicallyIntegral_iff]
  intro i j hij
  have := h i j
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, f.upper hij, add_zero] at this
  exact even_iff_two_dvd.mpr this

/-- For classically integral $f$, $H = 2(f_{ij})$. -/
theorem hessian_eq_two_smul_casselsMat {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) :
    f.hessian = (2 : ℤ) • casselsMat f := by
  ext i j
  simp only [casselsMat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (Int.mul_ediv_cancel' (two_dvd_hessian_of_ci hf i j)).symm

/-- Cassels' matrix is symmetric. -/
theorem casselsMat_isSymm (f : QuadForm ℤ k) : (casselsMat f).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp [casselsMat, QuadForm.hessian, add_comm]

/-- For classically integral $f$, $f(\mathbf x) = \mathbf x^{\mathsf T}(f_{ij})\mathbf x$. -/
theorem eval_eq_casselsMat {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) (x : Fin k → ℤ) :
    f.eval x = x ⬝ᵥ (casselsMat f *ᵥ x) := by
  have h2 := LocalDensity.two_mul_eval_eq_hessian f x
  rw [hessian_eq_two_smul_casselsMat hf, smul_mulVec, dotProduct_smul, smul_eq_mul] at h2
  linarith

/-- An integral form is determined by its Hessian. -/
theorem eq_of_hessian_eq {Q Q' : QuadForm ℤ k} (h : Q.hessian = Q'.hessian) : Q = Q' := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at hij
  rcases lt_trichotomy i j with hl | rfl | hl
  · rwa [Q.upper hl, Q'.upper hl, add_zero, add_zero] at hij
  · linarith
  · rw [Q.upper hl, Q'.upper hl]

/-- For classically integral $f$, `ofGram (casselsMat f) = f`. -/
theorem ofGram_casselsMat {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) : ofGram (casselsMat f) = f := by
  apply eq_of_hessian_eq
  rw [hessian_ofGram, (casselsMat_isSymm f).eq, hessian_eq_two_smul_casselsMat hf, two_smul]

/-- For symmetric $A$, `casselsMat (ofGram A) = A`. -/
theorem casselsMat_ofGram {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.IsSymm) : casselsMat (ofGram A) = A := by
  ext i j
  simp only [casselsMat, hessian_ofGram, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply,
    hA.apply i j]
  omega

/-- `ofGram A` is classically integral for symmetric $A$. -/
theorem ci_ofGram {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.IsSymm) : IsClassicallyIntegral (ofGram A) :=
  ⟨A, hA, eval_ofGram hA⟩

/-- For classically integral $f, h$: $f(T\mathbf x) = h(\mathbf x)$ iff $T^{\mathsf T}(f_{ij})T = (h_{ij})$. -/
theorem eval_mulVec_iff_casselsMat {f h : QuadForm ℤ k} (hf : IsClassicallyIntegral f)
    (hh : IsClassicallyIntegral h) (T : Matrix (Fin k) (Fin k) ℤ) :
    (∀ x, f.eval (T *ᵥ x) = h.eval x) ↔ Tᵀ * casselsMat f * T = casselsMat h := by
  rw [eval_mulVec_eq_iff_hessian, hessian_eq_two_smul_casselsMat hf, hessian_eq_two_smul_casselsMat hh,
    Matrix.mul_smul, Matrix.smul_mul]
  exact ⟨fun e => smul_right_injective _ two_ne_zero e, fun e => by rw [e]⟩

/-- Symmetric integer matrices with the same quadratic values are equal. -/
theorem eq_of_forall_dotProduct {A B : Matrix (Fin k) (Fin k) ℤ} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  have h0 := (forall_dotProduct_eq_zero_iff (A - B)).mp fun x => by
    rw [sub_mulVec, dotProduct_sub, h, sub_self]
  rw [transpose_sub, hA.eq, hB.eq] at h0
  ext i j
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply] at this
  linarith

/-- $S^{\mathsf T}GS$ is symmetric for symmetric $G$. -/
theorem isSymm_conj {G : Matrix (Fin k) (Fin k) ℤ} (hG : G.IsSymm) (S : Matrix (Fin k) (Fin k) ℤ) :
    (Sᵀ * G * S).IsSymm := by
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hG.eq, Matrix.mul_assoc]

/-- A matrix as an element of $\mathrm{GL}_k(\mathbb Z)$ when its determinant is a unit (junk value $1$ otherwise). -/
def toGL (M : Matrix (Fin k) (Fin k) ℤ) : GL (Fin k) ℤ :=
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

/-- `toGL M` has underlying matrix $M$ when $\det M = 1$. -/
theorem toGL_val {M : Matrix (Fin k) (Fin k) ℤ} (h : M.det = 1) : (toGL M).val = M := by
  rw [toGL, dite_eq_left (by rw [h]; exact isUnit_one)]; rfl

/-- $\det T^{-1} = 1$ when $\det T = 1$. -/
theorem det_inv_val_eq_one {T : GL (Fin k) ℤ} (hT : T.val.det = 1) : (T⁻¹).val.det = 1 := by
  have := congrArg Matrix.det T.inv_val
  rw [det_mul, det_one, hT, mul_one] at this
  exact this

/-- $(T^{\mathsf T}AT)_{00} = (Te_0)^{\mathsf T}A(Te_0)$. -/
theorem conj_apply_zero_zero (A T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    (Tᵀ * A * T) 0 0 = (T *ᵥ Pi.single 0 1) ⬝ᵥ (A *ᵥ (T *ᵥ Pi.single 0 1)) := by
  rw [dotProduct_conj, mulVec_single_one, single_one_dotProduct]; rfl

/-! ### (6.8): the class associated with a primitive representation -/

/-- **The associated form of a basis** $T$ (Cassels, (6.8)): with $F' = T^{\mathsf T}(f_{ij})T$ (the matrix of
$h = f(T\mathbf x)$) and $a = h(e_0)$, the $m \times m$ matrix $g_{ij} = aF'_{i+1, j+1} - F'_{0, i+1}F'_{0, j+1}$
($ah = (ax_0 + \sum_j F'_{0j}x_j)^2 + g$). -/
@[kb "cassels1978" "Ch. 9, §6, (6.8), p. 145 (completing the square)"]
def assocGram (f : QuadForm ℤ (m + 1)) (a : ℤ) (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => a * (Tᵀ * casselsMat f * T) i.succ j.succ -
    (Tᵀ * casselsMat f * T) 0 i.succ * (Tᵀ * casselsMat f * T) 0 j.succ

/-- The matrix $aA_{i+1, j+1} - A_{0, i+1}A_{0, j+1}$ (so `assocGram f a T = assocMat a (Tᵀ (f_{ij}) T)`). -/
def assocMat (a : ℤ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => a * A i.succ j.succ - A 0 i.succ * A 0 j.succ

/-- `assocGram` in terms of `assocMat`. -/
theorem assocGram_eq (f : QuadForm ℤ (m + 1)) (a : ℤ) (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    assocGram f a T = assocMat a (Tᵀ * casselsMat f * T) := rfl

/-- `assocMat` of a symmetric matrix is symmetric. -/
theorem assocMat_isSymm {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm) (a : ℤ) :
    (assocMat a A).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    simp only [assocMat, Matrix.of_apply]; rw [hA.apply i.succ j.succ]; ring

/-- **Completing the square** (6.8): $A_{00}\,\mathbf x^{\mathsf T}A\mathbf x = ((A\mathbf x)_0)^2 +
\mathbf y^{\mathsf T}(\mathrm{assocMat}\,A_{00}\,A)\mathbf y$ with $\mathbf y = (x_1, \dots, x_m)$. -/
theorem complete_square {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm) (x : Fin (m + 1) → ℤ) :
    A 0 0 * (x ⬝ᵥ (A *ᵥ x)) = (A *ᵥ x) 0 ^ 2 + Fin.tail x ⬝ᵥ (assocMat (A 0 0) A *ᵥ Fin.tail x) := by
  have e3 : (A *ᵥ x) 0 = A 0 0 * x 0 + ∑ j : Fin m, A 0 j.succ * x j.succ := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ]
  have e1 : x ⬝ᵥ (A *ᵥ x) = x 0 * (A 0 0 * x 0 + ∑ j : Fin m, A 0 j.succ * x j.succ) +
      ∑ i : Fin m, x i.succ * (A i.succ 0 * x 0 + ∑ j : Fin m, A i.succ j.succ * x j.succ) := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ]
  have e2 : ∑ i : Fin m, x i.succ * (A i.succ 0 * x 0 + ∑ j : Fin m, A i.succ j.succ * x j.succ) =
      x 0 * ∑ j : Fin m, A 0 j.succ * x j.succ +
        ∑ i : Fin m, x i.succ * ∑ j : Fin m, A i.succ j.succ * x j.succ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.apply 0 i.succ]
    ring
  have e5 : ∀ i : Fin m, x i.succ * ∑ j : Fin m, (A 0 0 * A i.succ j.succ - A 0 i.succ * A 0 j.succ) * x j.succ =
      A 0 0 * (x i.succ * ∑ j : Fin m, A i.succ j.succ * x j.succ) -
        (A 0 i.succ * x i.succ) * ∑ j : Fin m, A 0 j.succ * x j.succ := by
    intro i
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e4 : Fin.tail x ⬝ᵥ (assocMat (A 0 0) A *ᵥ Fin.tail x) =
      A 0 0 * ∑ i : Fin m, x i.succ * ∑ j : Fin m, A i.succ j.succ * x j.succ -
        (∑ j : Fin m, A 0 j.succ * x j.succ) * ∑ j : Fin m, A 0 j.succ * x j.succ := by
    simp only [dotProduct, mulVec, assocMat, Matrix.of_apply, Fin.tail]
    rw [Finset.sum_congr rfl fun i _ => e5 i, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [e1, e2, e3, e4]
  ring

/-- For $M$ with first column $e_0$: $(M^{\mathsf T}\mathbf z)_0 = z_0$. -/
theorem transpose_mulVec_apply_zero {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) (z : Fin (m + 1) → ℤ) : (Mᵀ *ᵥ z) 0 = z 0 := by
  rw [mulVec_transpose, ← dotProduct_single_one (z ᵥ* M) 0, ← dotProduct_mulVec, hM, dotProduct_single_one]

/-- For $M$ with first column $e_0$, entrywise: $M_{i0} = \delta_{i0}$. -/
theorem apply_zero_of_firstCol {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) (i : Fin (m + 1)) :
    M i 0 = (Pi.single 0 1 : Fin (m + 1) → ℤ) i := by
  rw [← hM, mulVec_single_one]; rfl

/-- For $M$ with first column $e_0$: $M_{i+1, 0} = 0$. -/
theorem apply_succ_zero_of_firstCol {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) (i : Fin m) : M i.succ 0 = 0 := by
  rw [apply_zero_of_firstCol hM]; simp [Fin.succ_ne_zero]

/-- For $M$ with first column $e_0$: $M_{00} = 1$. -/
theorem apply_zero_zero_of_firstCol {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) : M 0 0 = 1 := by
  rw [apply_zero_of_firstCol hM]; simp

/-- For $M$ with first column $e_0$: the tail of $M\mathbf x$ is $S$ times the tail of $\mathbf x$, with $S$ the lower
right block. -/
theorem tail_mulVec {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (x : Fin (m + 1) → ℤ) : Fin.tail (M *ᵥ x) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail x := by
  funext i
  simp [Fin.tail, mulVec, dotProduct, Fin.sum_univ_succ, apply_succ_zero_of_firstCol hM]

/-- For $M$ with first column $e_0$: $\det M = \det S$, $S$ the lower right block. -/
theorem det_of_firstCol {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [apply_zero_zero_of_firstCol hM, apply_succ_zero_of_firstCol hM]

/-- For $M$ with first column $e_0$: $(M^{\mathsf T}AM)_{0j} = (AM)_{0j}$. -/
theorem conj_apply_zero {A M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (j : Fin (m + 1)) : (Mᵀ * A * M) 0 j = (A * M) 0 j := by
  have := transpose_mulVec_apply_zero hM ((A * M) *ᵥ Pi.single j 1)
  rwa [mulVec_mulVec, ← Matrix.mul_assoc, mulVec_single_one, mulVec_single_one] at this

/-- For $M$ with first column $e_0$: $(M^{\mathsf T}AM)_{00} = A_{00}$. -/
theorem conj_apply_zero_zero_of_firstCol {A M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) : (Mᵀ * A * M) 0 0 = A 0 0 := by
  rw [conj_apply_zero hM, Matrix.mul_apply, Fin.sum_univ_succ]
  simp [apply_zero_zero_of_firstCol hM, apply_succ_zero_of_firstCol hM]

/-- **The associated matrix under a change of basis fixing $e_0$** (6.8): for $M$ with first column $e_0$ and lower
right block $S$, $\mathrm{assocMat}(M^{\mathsf T}AM) = S^{\mathsf T}\,\mathrm{assocMat}(A)\,S$. -/
theorem assocMat_conj {A M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm)
    (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    assocMat (A 0 0) (Mᵀ * A * M) =
      (M.submatrix Fin.succ Fin.succ)ᵀ * assocMat (A 0 0) A * M.submatrix Fin.succ Fin.succ := by
  have hA' : (Mᵀ * A * M).IsSymm := isSymm_conj hA M
  refine eq_of_forall_dotProduct (assocMat_isSymm hA' _) (isSymm_conj (assocMat_isSymm hA _) _) fun y => ?_
  set x : Fin (m + 1) → ℤ := Fin.cons 0 y with hx
  have k1 := complete_square hA' x
  have k2 := complete_square hA (M *ᵥ x)
  rw [conj_apply_zero_zero_of_firstCol hM] at k1
  have q : x ⬝ᵥ ((Mᵀ * A * M) *ᵥ x) = (M *ᵥ x) ⬝ᵥ (A *ᵥ (M *ᵥ x)) := (dotProduct_conj M A x).symm
  have l : ((Mᵀ * A * M) *ᵥ x) 0 = (A *ᵥ (M *ᵥ x)) 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, transpose_mulVec_apply_zero hM]
  rw [tail_mulVec hM, hx, Fin.tail_cons] at k2
  rw [hx, Fin.tail_cons] at k1
  rw [← dotProduct_conj]
  rw [← hx] at k1 k2
  rw [q, l] at k1
  linarith

/-- For classically integral $f$: $f(Te_0) = (T^{\mathsf T}(f_{ij})T)_{00}$. -/
theorem eval_first_col {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f)
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    f.eval (T *ᵥ Pi.single 0 1) = (Tᵀ * casselsMat f * T) 0 0 := by
  rw [conj_apply_zero_zero, eval_eq_casselsMat hf]

/-- $T^{-1}T'$ fixes $e_0$ when $T, T'$ have the same first column. -/
theorem firstCol_inv_mul {T T' : GL (Fin (m + 1)) ℤ} (h0 : T.val *ᵥ Pi.single 0 1 = T'.val *ᵥ Pi.single 0 1) :
    (T⁻¹ * T').val *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [Units.val_mul, ← mulVec_mulVec, ← h0, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mulVec]

/-- $T'^{\mathsf T}CT' = M^{\mathsf T}(T^{\mathsf T}CT)M$ with $M = T^{-1}T'$. -/
theorem conj_inv_mul {k : ℕ} (C : Matrix (Fin k) (Fin k) ℤ) (T T' : GL (Fin k) ℤ) :
    T'.valᵀ * C * T'.val = ((T⁻¹ * T').val)ᵀ * (T.valᵀ * C * T.val) * (T⁻¹ * T').val := by
  have e : T'.val = T.val * (T⁻¹ * T').val := by rw [← Units.val_mul, mul_inv_cancel_left]
  conv_lhs => rw [e]
  rw [transpose_mul]; simp only [Matrix.mul_assoc]

/-- **Cassels, (6.8), p. 145:** *the class of $g$ for proper equivalence is independent of the choice of
$b_2, \dots, b_n$ and depends only on $b = b_1$.* -/
@[kb "cassels1978" "Ch. 9, §6, (6.8), p. 145 (the class of g depends only on b)"]
theorem assocGram_properIntEquiv (f : QuadForm ℤ (m + 1)) (hf : IsClassicallyIntegral f) (T T' : GL (Fin (m + 1)) ℤ)
    (hT : T.val.det = 1) (hT' : T'.val.det = 1) (h0 : T.val *ᵥ Pi.single 0 1 = T'.val *ᵥ Pi.single 0 1) :
    ProperIntEquiv (ofGram (assocGram f (f.eval (T.val *ᵥ Pi.single 0 1)) T.val))
      (ofGram (assocGram f (f.eval (T.val *ᵥ Pi.single 0 1)) T'.val)) := by
  have hM := firstCol_inv_mul h0
  have hA := isSymm_conj (casselsMat_isSymm f) T.val
  have hdet : ((T⁻¹ * T').val).det = 1 := by
    rw [Units.val_mul, det_mul, det_inv_val_eq_one hT, hT', mul_one]
  have hS : (((T⁻¹ * T').val).submatrix Fin.succ Fin.succ).det = 1 := by rw [← det_of_firstCol hM, hdet]
  refine ⟨toGL (((T⁻¹ * T').val).submatrix Fin.succ Fin.succ), by rw [toGL_val hS, hS], fun y => ?_⟩
  rw [toGL_val hS, eval_first_col hf, assocGram_eq, assocGram_eq, conj_inv_mul _ T T', assocMat_conj hA hM,
    eval_ofGram (assocMat_isSymm hA _), eval_ofGram (isSymm_conj (assocMat_isSymm hA _) _), dotProduct_conj]

open Classical in
/-- **The proper class associated with a representation** $b$ (Cassels, p. 145: *we shall say that the representation
of $a$ by $b$ is associated with the class of $g$*): the proper class of the associated form of any
$T \in \mathrm{SL}_n(\mathbb Z)$ with first column $b$ (a junk value if $b$ is not primitive). -/
@[kb "cassels1978" "Ch. 9, §6, p. 145 (representation associated with the class of g)"]
def assocClass (f : QuadForm ℤ (m + 1)) (b : Fin (m + 1) → ℤ) : PClass m :=
  if h : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b then
    pclassOf (ofGram (assocGram f (f.eval b) h.choose.val))
  else pclassOf (ofGram 0)

/-! ### (6.9): the weight of a genus -/

/-- **The proper classes of the genus of $f$.** -/
def pgenusClasses (f : QuadForm ℤ k) : Set (PClass k) := {C | ∃ f', pclassOf f' = C ∧ SameGenus f f'}

/-- **The weight of the genus** of $f$ (Cassels, (6.9), p. 146): $W(\mathcal F) = \sum 1/o^{+}(f')$ over representatives
$f'$ of the proper classes of the genus ($o^{+}$ the order of the group of proper automorphs; a `finsum`, $0$ if the
genus had infinitely many proper classes). -/
@[kb "cassels1978" "Ch. 9, §6, (6.9), p. 146 (the weight W of a genus)"]
def pweight (f : QuadForm ℤ k) : ℝ := ∑ᶠ C ∈ pgenusClasses f, ((Nat.card (AutPlus C.out) : ℝ))⁻¹

/-- The wide class of a proper class. -/
def toQClass : PClass k → QClass k :=
  Quotient.lift (s := properSetoid k) (fun Q => classOf Q)
    (fun _ _ h => classOf_eq_classOf_iff.mpr (ProperIntEquiv.intEquiv h))

/-- `toQClass C` is the class of the representative `C.out`. -/
theorem toQClass_eq_classOf_out (C : PClass k) : toQClass C = classOf C.out := by
  conv_lhs => rw [← Quotient.out_eq C]
  rfl

/-- `pclassOf C.out = C`. -/
theorem pclassOf_out (C : PClass k) : pclassOf C.out = C := Quotient.out_eq C

/-- A proper class lies in the genus of $f$ iff its representative does. -/
theorem mem_pgenusClasses_iff_out {f : QuadForm ℤ k} {C : PClass k} :
    C ∈ pgenusClasses f ↔ SameGenus f C.out := by
  constructor
  · rintro ⟨f', hf', hg⟩
    rw [← pclassOf_out C] at hf'
    exact hg.trans (pclassOf_eq_pclassOf_iff.mp hf').intEquiv.sameGenus
  · exact fun h => ⟨C.out, pclassOf_out C, h⟩

/-- The proper classes of the genus are those whose wide class lies in the genus. -/
theorem pgenusClasses_eq_preimage (f : QuadForm ℤ k) :
    pgenusClasses f = toQClass ⁻¹' genusClasses f := by
  ext C
  rw [Set.mem_preimage, toQClass_eq_classOf_out, classOf_mem_genusClasses_iff, mem_pgenusClasses_iff_out]

/-- The fibre of `toQClass` over $c$ is the set of proper classes in $c$. -/
theorem preimage_toQClass (c : QClass k) : toQClass ⁻¹' {c} = properClassesIn c.out := by
  ext C
  rw [Set.mem_preimage, Set.mem_singleton_iff, toQClass_eq_classOf_out]
  constructor
  · intro h
    refine ⟨C.out, pclassOf_out C, ?_⟩
    rw [← Quotient.out_eq c] at h
    exact (classOf_eq_classOf_iff.mp h).symm
  · rintro ⟨Q'', hQ'', hI⟩
    rw [← pclassOf_out C] at hQ''
    have h1 : classOf Q'' = classOf C.out := classOf_eq_classOf_iff.mpr (pclassOf_eq_pclassOf_iff.mp hQ'').intEquiv
    have h2 : classOf c.out = classOf Q'' := classOf_eq_classOf_iff.mpr hI
    rw [← h1, ← h2]
    exact Quotient.out_eq c

/-- The genus of a form with $\det H \ne 0$ has finitely many proper classes ($k \ge 1$). -/
theorem pgenusClasses_finite (hk : 0 < k) {f : QuadForm ℤ k} (hf : f.hessian.det ≠ 0) :
    (pgenusClasses f).Finite := by
  rw [pgenusClasses_eq_preimage]
  refine (genusClasses_finite hf).preimage' fun c _ => ?_
  rw [preimage_toQClass]
  refine Set.finite_of_ncard_ne_zero ?_
  rw [ncard_properClassesIn hk]
  split_ifs <;> norm_num

/-- Conjugation identifies the proper automorphs of equivalent forms. -/
def autPlusEquiv {Q Q' : QuadForm ℤ k} (g : GL (Fin k) ℤ) (hg : ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x) :
    AutPlus Q' ≃ AutPlus Q where
  toFun h := ⟨g * h.1 * g⁻¹, mem_autPlus_iff.mpr
    ⟨((autEquivOfIsometry g hg) ⟨h.1, (mem_autPlus_iff.mp h.2).1⟩).2, by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, (mem_autPlus_iff.mp h.2).2, mul_one, ← det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]⟩⟩
  invFun h := ⟨g⁻¹ * h.1 * g, mem_autPlus_iff.mpr
    ⟨((autEquivOfIsometry g hg).symm ⟨h.1, (mem_autPlus_iff.mp h.2).1⟩).2, by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, (mem_autPlus_iff.mp h.2).2, mul_one, ← det_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]⟩⟩
  left_inv h := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]

/-- $o^{+}$ is a class invariant. -/
theorem card_autPlus_eq_of_intEquiv {Q Q' : QuadForm ℤ k} (h : IntEquiv Q Q') :
    Nat.card (AutPlus Q) = Nat.card (AutPlus Q') := by
  obtain ⟨g, hg⟩ := h
  exact (Nat.card_congr (autPlusEquiv g hg)).symm

open Classical in
/-- $o(f) = [O(f) : O^{+}(f)]\,o^{+}(f)$. -/
theorem card_aut_eq_mul (Q : QuadForm ℤ k) :
    Nat.card (Aut Q) = Nat.card (AutPlus Q) * (if HasImproperAut Q then 2 else 1) := by
  rw [← index_autPlus, ← Subgroup.card_mul_index ((AutPlus Q).subgroupOf (Aut Q)), Subgroup.relIndex]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : AutPlus Q ≤ Aut Q)).toEquiv

/-- $O^{+}(f)$ is finite and nonempty for positive definite $f$. -/
theorem card_autPlus_pos {Q : QuadForm ℤ k} (hQ : IntQF.PosDef Q) : 0 < Nat.card (AutPlus Q) := by
  have := hQ.finite_aut
  have : Finite (AutPlus Q) := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : AutPlus Q ≤ Aut Q))
  exact Nat.card_pos

/-- **Cassels, footnote to (6.9)** (p. 146): *some authors use $\sum 1/o(f)$, where the sum is over the wide
equivalence classes and $o(f)$ is the total number of automorphs (proper and improper). This is half of (6.9).* Here
the library's `Siegel.mass` is that sum; for positive definite $f$ in $n \ge 1$ variables, $W = 2\,\mathrm{mass}$. -/
@[kb "cassels1978" "Ch. 9, §6, p. 146, footnote (the weight is twice the mass over wide classes)"]
theorem pweight_eq_two_mul_mass (hk : 0 < k) {f : QuadForm ℤ k} (hf : IntQF.PosDef f) :
    pweight f = 2 * mass f := by
  classical
  have hd : f.hessian.det ≠ 0 := hf.nondegenerate
  have hPG := pgenusClasses_finite hk hd
  have hGC := genusClasses_finite hd
  rw [pweight, mass, finsum_mem_eq_finite_toFinset_sum _ hPG, finsum_mem_eq_finite_toFinset_sum _ hGC,
    Finset.mul_sum]
  have hmaps : ∀ C ∈ hPG.toFinset, toQClass C ∈ hGC.toFinset := fun C hC => by
    rw [Set.Finite.mem_toFinset] at hC ⊢
    rw [pgenusClasses_eq_preimage] at hC
    exact hC
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Set.Finite.mem_toFinset] at hc
  have hc2 : classOf c.out = c := Quotient.out_eq c
  have hpd : IntQF.PosDef c.out := (classOf_mem_genusClasses_iff.mp (by rw [hc2]; exact hc)).posDef hf
  have hterm : ∀ C ∈ hPG.toFinset.filter (fun C => toQClass C = c),
      ((Nat.card (AutPlus C.out) : ℝ))⁻¹ = ((Nat.card (AutPlus c.out) : ℝ))⁻¹ := by
    intro C hC
    rw [Finset.mem_filter, toQClass_eq_classOf_out] at hC
    rw [card_autPlus_eq_of_intEquiv (classOf_eq_classOf_iff.mp (hc2.trans hC.2.symm))]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard : (hPG.toFinset.filter (fun C => toQClass C = c)).card = (properClassesIn c.out).ncard := by
    rw [← preimage_toQClass, ← Set.ncard_coe_finset]
    congr 1
    ext C
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff, pgenusClasses_eq_preimage]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
  have hA : c.autCard = Nat.card (Aut c.out) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [hcard, ncard_properClassesIn hk, hA, card_aut_eq_mul c.out]
  have hpos : (0 : ℝ) < Nat.card (AutPlus c.out) := by exact_mod_cast card_autPlus_pos hpd
  split_ifs <;> push_cast <;> field_simp

/-! ### (6.10), (6.11): Cassels' ρ and σ -/

/-- **The form $h$ of (6.8) from $(a, \mathbf c, g)$:** the $(m+1) \times (m+1)$ matrix with entries $a$ at $(0, 0)$,
$c_j$ at $(0, j+1)$ and $(j+1, 0)$, and $(c_ic_j + g_{ij})/a$ at $(i+1, j+1)$, so that
$a\,h(\mathbf x) = (ax_0 + \sum_j c_jx_{j+1})^2 + g(x_1, \dots, x_m)$ when $a \mid c_ic_j + g_{ij}$. -/
def hMat (a : ℤ) (c : Fin m → ℤ) (G : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (Fin.cases a c j) (fun i' => Fin.cases (c i') (fun j' => (c i' * c j' + G i' j') / a) j) i

/-- **Cassels' $\rho(\mathcal F, g)$** ((6.10), p. 146): the number of congruence classes $\mathbf c \bmod a$ for which
the form $h$ of (6.8) (`hMat a c G`) is integral and lies in the genus $\mathcal F$ of $f$. -/
@[kb "cassels1978" "Ch. 9, §6, (6.10), p. 146 (ρ)"]
def rhoCount (f : QuadForm ℤ (m + 1)) (a : ℕ) (G : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  Nat.card {v : Fin m → ZMod a // ∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v i) ∧
    (∀ i j, (a : ℤ) ∣ c i * c j + G i j) ∧ SameGenus f (ofGram (hMat a c G))}

/-- **Cassels' $\sigma(a, \mathcal F, [g])$** ((6.11), p. 146) for one proper class $C$ of $m$-ary forms: the sum over
representatives $f'$ of the proper classes of the genus of $f$ of $1/o^{+}(f')$ times the number of primitive
representations of $a$ by $f'$ associated with $C$. -/
@[kb "cassels1978" "Ch. 9, §6, (6.11), p. 146 (σ, for one class)"]
def sigmaWeight (f : QuadForm ℤ (m + 1)) (a : ℤ) (C : PClass m) : ℝ :=
  ∑ᶠ D ∈ pgenusClasses f,
    (Nat.card {b // b ∈ primRepSet D.out a ∧ assocClass D.out b = C} : ℝ) / Nat.card (AutPlus D.out)

/-- **Cassels' $\sigma(a, \mathcal F, \mathcal G)$** ((6.11), p. 146): the sum of the weights of all primitive
representations of $a$ by representatives of the classes of $\mathcal F$ associated with forms of the genus
$\mathcal G$ of $g$. -/
@[kb "cassels1978" "Ch. 9, §6, (6.11), p. 146 (σ)"]
def sigmaGenus (f : QuadForm ℤ (m + 1)) (a : ℤ) (g : QuadForm ℤ m) : ℝ :=
  ∑ᶠ C ∈ pgenusClasses g, sigmaWeight f a C

/-! ### Lemma 6.2 -/

section HMat

variable {a : ℤ} {c : Fin m → ℤ} {G : Matrix (Fin m) (Fin m) ℤ}

/-- Entry $(0, 0)$ of `hMat`. -/
@[simp] theorem hMat_zero_zero : hMat a c G 0 0 = a := rfl

/-- Entry $(0, j+1)$ of `hMat`. -/
@[simp] theorem hMat_zero_succ (j : Fin m) : hMat a c G 0 j.succ = c j := rfl

/-- Entry $(i+1, 0)$ of `hMat`. -/
@[simp] theorem hMat_succ_zero (i : Fin m) : hMat a c G i.succ 0 = c i := rfl

/-- Entry $(i+1, j+1)$ of `hMat`. -/
@[simp] theorem hMat_succ_succ (i j : Fin m) : hMat a c G i.succ j.succ = (c i * c j + G i j) / a := rfl

/-- `hMat` is symmetric for symmetric $G$. -/
theorem hMat_isSymm (hG : G.IsSymm) : (hMat a c G).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rw [hMat_succ_succ, hMat_succ_succ, hG.apply i j, mul_comm]

/-- The associated matrix of `hMat a c G` is $G$ (when $a \mid c_ic_j + g_{ij}$). -/
theorem assocMat_hMat (hdiv : ∀ i j, a ∣ c i * c j + G i j) : assocMat a (hMat a c G) = G := by
  ext i j
  simp only [assocMat, Matrix.of_apply, hMat_succ_succ, hMat_zero_succ, Int.mul_ediv_cancel' (hdiv i j)]
  ring

/-- **Uniqueness of $h$ in (6.8):** a symmetric $A$ with $A_{00} = a \ne 0$, first row $(a, \mathbf c)$ and associated
matrix $G$ is `hMat a c G` (and $a \mid c_ic_j + g_{ij}$). -/
theorem eq_hMat {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm) (ha : a ≠ 0)
    (h0 : A 0 0 = a) (h1 : ∀ j, A 0 j.succ = c j) (h2 : assocMat a A = G) :
    (∀ i j, a ∣ c i * c j + G i j) ∧ A = hMat a c G := by
  have key : ∀ i j, c i * c j + G i j = a * A i.succ j.succ := fun i j => by
    rw [← h2]; simp only [assocMat, Matrix.of_apply, h1]; ring
  refine ⟨fun i j => ⟨_, key i j⟩, ?_⟩
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [hA.apply 0 i.succ, h1]; rfl
  · rw [hMat_succ_succ, key, Int.mul_ediv_cancel_left _ ha]

end HMat

/-- The matrix $\begin{pmatrix}1 & \mathbf u^{\mathsf T}\\ 0 & S\end{pmatrix}$. -/
def blk (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 u j) (fun i' => Fin.cases 0 (fun j' => S i' j') j) i

/-- `blk u S` has first column $e_0$. -/
theorem blk_firstCol (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) :
    blk u S *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  funext i
  rw [mulVec_single_one]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [blk]
  · simp [blk, Fin.succ_ne_zero]

/-- The lower right block of `blk u S` is $S$. -/
theorem blk_submatrix (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) :
    (blk u S).submatrix Fin.succ Fin.succ = S := by
  ext i j; simp [blk]

/-- $\det$ `blk u S` $= \det S$. -/
theorem det_blk (u : Fin m → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) : (blk u S).det = S.det := by
  rw [det_of_firstCol (blk_firstCol u S), blk_submatrix]

/-- A matrix with first column $e_0$ is a `blk`. -/
theorem eq_blk {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    M = blk (fun j => M 0 j.succ) (M.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [apply_zero_zero_of_firstCol hM]; rfl
  · rfl
  · rw [apply_succ_zero_of_firstCol hM]; rfl
  · rfl

/-- $(A\,\mathrm{blk}(\mathbf u, S))_{0, j+1} = A_{00}u_j + \sum_l A_{0, l+1}S_{lj}$. -/
theorem mul_blk_zero_succ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (u : Fin m → ℤ)
    (S : Matrix (Fin m) (Fin m) ℤ) (j : Fin m) :
    (A * blk u S) 0 j.succ = A 0 0 * u j + ∑ l : Fin m, A 0 l.succ * S l j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [blk]

/-- **Changing $\mathbf c$ modulo $a$** gives a properly equivalent $h$ (substitute $x_0 \mapsto x_0 + \mathbf u \cdot
\mathbf y$). -/
theorem hMat_change {a : ℕ} [NeZero a] {G : Matrix (Fin m) (Fin m) ℤ} (hG : G.IsSymm) (c c' : Fin m → ℤ)
    (hcc : ∀ i, (a : ℤ) ∣ c' i - c i) (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) :
    (∀ i j, (a : ℤ) ∣ c' i * c' j + G i j) ∧
      ProperIntEquiv (ofGram (hMat a c G)) (ofGram (hMat a c' G)) := by
  set u : Fin m → ℤ := fun i => (c' i - c i) / a
  set M := blk u 1
  have hM := blk_firstCol u (1 : Matrix (Fin m) (Fin m) ℤ)
  have hH : (hMat (a : ℤ) c G).IsSymm := hMat_isSymm hG
  have h0 : (Mᵀ * hMat a c G * M) 0 0 = a := by rw [conj_apply_zero_zero_of_firstCol hM]; rfl
  have h1 : ∀ j, (Mᵀ * hMat a c G * M) 0 j.succ = c' j := fun j => by
    rw [conj_apply_zero hM, mul_blk_zero_succ]
    have e : ∑ l : Fin m, hMat (a : ℤ) c G 0 l.succ * (1 : Matrix (Fin m) (Fin m) ℤ) l j = c j := by
      simp [Matrix.one_apply]
    rw [e, hMat_zero_zero, Int.mul_ediv_cancel' (hcc j)]
    ring
  have h2 : assocMat a (Mᵀ * hMat a c G * M) = G := by
    have := assocMat_conj hH hM
    simp only [hMat_zero_zero] at this
    rw [this, blk_submatrix, transpose_one, Matrix.one_mul, Matrix.mul_one, assocMat_hMat hdiv]
  obtain ⟨hdiv', hEq⟩ := eq_hMat (isSymm_conj hH M) (Nat.cast_ne_zero.mpr (NeZero.ne a)) h0 h1 h2
  have hdetM : M.det = 1 := by rw [det_blk, det_one]
  refine ⟨hdiv', toGL M, by rw [toGL_val hdetM, hdetM], fun y => ?_⟩
  rw [toGL_val hdetM, eval_ofGram hH, dotProduct_conj, hEq, ← eval_ofGram (hMat_isSymm hG)]

/-! #### The double count: the set $X$ and its count by $\mathbf v$ -/

/-- The canonical lift $0 \le c_i < a$ of $\mathbf v \in (\mathbb Z/a)^m$. -/
def canLift {a : ℕ} (v : Fin m → ZMod a) : Fin m → ℤ := fun i => ((v i).val : ℤ)

/-- The canonical lift reduces to $\mathbf v$. -/
theorem cast_canLift {a : ℕ} [NeZero a] (v : Fin m → ZMod a) (i : Fin m) : ((canLift v i : ℤ) : ZMod a) = v i := by
  simp [canLift]

/-- The canonical lift of the reduction of $\mathbf w$ is $\mathbf w \bmod a$. -/
theorem canLift_cast {a : ℕ} [NeZero a] (w : Fin m → ℤ) (i : Fin m) :
    canLift (fun j => (w j : ZMod a)) i = w i % a := by
  simp only [canLift]; exact ZMod.val_intCast _

/-- $0 \le$ `canLift v i` $< a$. -/
theorem canLift_bounds {a : ℕ} [NeZero a] (v : Fin m → ZMod a) (i : Fin m) : 0 ≤ canLift v i ∧ canLift v i < a :=
  ⟨Nat.cast_nonneg _, by simp only [canLift]; exact_mod_cast ZMod.val_lt (v i)⟩

/-- The set $X$ of the double count: pairs $(T, \mathbf v)$ with $\det T = 1$, $a \mid c_ic_j + g_{ij}$ and
$T^{\mathsf T}FT = $ `hMat a c G` for the canonical lift $\mathbf c$ of $\mathbf v$. -/
def Xset (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ) :
    Set (GL (Fin (m + 1)) ℤ × (Fin m → ZMod a)) :=
  {p | p.1.val.det = 1 ∧ (∀ i j, (a : ℤ) ∣ canLift p.2 i * canLift p.2 j + G i j) ∧
    p.1.valᵀ * F * p.1.val = hMat a (canLift p.2) G}

/-- The proper stabilizer $\{\sigma : \det\sigma = 1,\ \sigma^{\mathsf T}F\sigma = F\}$. -/
def stabSet (F : Matrix (Fin k) (Fin k) ℤ) : Set (GL (Fin k) ℤ) := {σ | σ.val.det = 1 ∧ σ.valᵀ * F * σ.val = F}

/-- The proper stabilizer of $(f_{ij})$ is $O^{+}(f)$. -/
theorem card_stabSet {Q : QuadForm ℤ k} (hQ : IsClassicallyIntegral Q) :
    Nat.card (stabSet (casselsMat Q)) = Nat.card (AutPlus Q) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  rw [mem_autPlus_iff]
  show (σ.val.det = 1 ∧ _) ↔ (∀ x, Q.eval (σ.val *ᵥ x) = Q.eval x) ∧ σ.val.det = 1
  rw [eval_mulVec_iff_casselsMat hQ hQ]
  exact And.comm

/-- Admissible $\mathbf v$ for $F$: $a \mid c_ic_j + g_{ij}$ and some $T \in \mathrm{SL}$ carries $F$ to
`hMat a c G` ($\mathbf c$ the canonical lift). -/
def VPred (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ)
    (v : Fin m → ZMod a) : Prop :=
  (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + G i j) ∧
    ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.valᵀ * F * T.val = hMat a (canLift v) G

/-- $(\sigma T)^{\mathsf T}F(\sigma T) = T^{\mathsf T}(\sigma^{\mathsf T}F\sigma)T$. -/
theorem conj_mul' (F σ T : Matrix (Fin k) (Fin k) ℤ) : (σ * T)ᵀ * F * (σ * T) = Tᵀ * (σᵀ * F * σ) * T := by
  rw [transpose_mul]; simp only [Matrix.mul_assoc]

/-- Products of determinant-one elements have determinant one. -/
theorem det_mul_eq_one {σ T : GL (Fin k) ℤ} (h1 : σ.val.det = 1) (h2 : T.val.det = 1) : (σ * T).val.det = 1 := by
  rw [Units.val_mul, det_mul, h1, h2, one_mul]

/-- If $T^{\mathsf T}FT = T_0^{\mathsf T}FT_0$ then $TT_0^{-1}$ fixes $F$. -/
theorem conj_mul_inv_eq {F : Matrix (Fin k) (Fin k) ℤ} {T T0 : GL (Fin k) ℤ}
    (h : T.valᵀ * F * T.val = T0.valᵀ * F * T0.val) : (T * T0⁻¹).valᵀ * F * (T * T0⁻¹).val = F := by
  rw [Units.val_mul, conj_mul', h, ← conj_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one,
    Matrix.one_mul, Matrix.mul_one]

/-- A chosen $T_0$ for an admissible $\mathbf v$. -/
def T0of {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} {G : Matrix (Fin m) (Fin m) ℤ} {a : ℕ} {v : Fin m → ZMod a}
    (hv : VPred F G a v) : GL (Fin (m + 1)) ℤ := hv.2.choose

/-- The defining property of `T0of`. -/
theorem T0of_spec {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} {G : Matrix (Fin m) (Fin m) ℤ} {a : ℕ}
    {v : Fin m → ZMod a} (hv : VPred F G a v) :
    (T0of hv).val.det = 1 ∧ (T0of hv).valᵀ * F * (T0of hv).val = hMat a (canLift v) G := hv.2.choose_spec

/-- **Count of $X$ by $\mathbf v$:** $X \cong \{\mathbf v \text{ admissible}\} \times O^{+}(F)$. -/
def equivX1 (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ) :
    {v // VPred F G a v} × stabSet F ≃ Xset F G a where
  toFun p := ⟨(p.2.1 * T0of p.1.2, p.1.1), det_mul_eq_one p.2.2.1 (T0of_spec p.1.2).1, p.1.2.1, by
    show (p.2.1 * T0of p.1.2).valᵀ * F * (p.2.1 * T0of p.1.2).val = _
    rw [Units.val_mul, conj_mul', p.2.2.2, (T0of_spec p.1.2).2]⟩
  invFun x :=
    have hv : VPred F G a x.1.2 := ⟨x.2.2.1, x.1.1, x.2.1, x.2.2.2⟩
    (⟨x.1.2, hv⟩, ⟨x.1.1 * (T0of hv)⁻¹, det_mul_eq_one x.2.1 (det_inv_val_eq_one (T0of_spec hv).1),
      conj_mul_inv_eq (x.2.2.2.trans (T0of_spec hv).2.symm)⟩)
  left_inv p := Prod.ext (Subtype.ext rfl) (Subtype.ext (mul_inv_cancel_right _ _))
  right_inv x := Subtype.ext (Prod.ext (inv_mul_cancel_right _ _) rfl)

/-- $|X| = \#\{\mathbf v \text{ admissible}\}\cdot o^{+}(F)$. -/
theorem card_Xset_eq_v (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ) :
    Nat.card (Xset F G a) = Nat.card {v // VPred F G a v} * Nat.card (stabSet F) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (equivX1 F G a)).symm

/-! #### The count of $X$ by the first column $b = Te_0$ -/

open Classical in
/-- A chosen $T_b \in \mathrm{SL}_{m+1}(\mathbb Z)$ with first column $b$ (the one used by `assocClass`; $1$ if none). -/
def Tsel (b : Fin (m + 1) → ℤ) : GL (Fin (m + 1)) ℤ :=
  if h : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b then h.choose else 1

/-- The defining property of `Tsel`. -/
theorem Tsel_spec {b : Fin (m + 1) → ℤ}
    (h : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b) :
    (Tsel b).val.det = 1 ∧ (Tsel b).val *ᵥ Pi.single 0 1 = b := by
  rw [Tsel, dite_eq_left h]; exact h.choose_spec

/-- `assocClass` via `Tsel`. -/
theorem assocClass_eq (f : QuadForm ℤ (m + 1)) {b : Fin (m + 1) → ℤ}
    (h : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b) :
    assocClass f b = pclassOf (ofGram (assocGram f (f.eval b) (Tsel b).val)) := by
  rw [assocClass, Tsel, dite_eq_left h, dite_eq_left h]

open Classical in
/-- A chosen $S_b \in \mathrm{SL}_m(\mathbb Z)$ with $S_b^{\mathsf T}G_bS_b = G$, $G_b$ the associated matrix of $T_b$
($1$ if none). -/
def Ssel (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℤ)
    (b : Fin (m + 1) → ℤ) : GL (Fin m) ℤ :=
  if h : ∃ S : GL (Fin m) ℤ, S.val.det = 1 ∧
      S.valᵀ * assocMat a ((Tsel b).valᵀ * F * (Tsel b).val) * S.val = G then h.choose else 1

/-- The defining property of `Ssel`. -/
theorem Ssel_spec {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} {G : Matrix (Fin m) (Fin m) ℤ} {a : ℤ}
    {b : Fin (m + 1) → ℤ} (h : ∃ S : GL (Fin m) ℤ, S.val.det = 1 ∧
      S.valᵀ * assocMat a ((Tsel b).valᵀ * F * (Tsel b).val) * S.val = G) :
    (Ssel F G a b).val.det = 1 ∧
      (Ssel F G a b).valᵀ * assocMat a ((Tsel b).valᵀ * F * (Tsel b).val) * (Ssel F G a b).val = G := by
  rw [Ssel, dite_eq_left h]; exact h.choose_spec

/-- The representations counted by `sigmaWeight`: primitive, of $a$, associated with $[g]$. -/
def BPred (f : QuadForm ℤ (m + 1)) (g : QuadForm ℤ m) (a : ℕ) (b : Fin (m + 1) → ℤ) : Prop :=
  b ∈ primRepSet f a ∧ assocClass f b = pclassOf g

/-- The data attached to a representation $b$ counted by `sigmaWeight`. -/
theorem bdata (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} {b : Fin (m + 1) → ℤ} (hb : BPred f g a b) :
    (Tsel b).val.det = 1 ∧ (Tsel b).val *ᵥ Pi.single 0 1 = b ∧
      ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) 0 0 = a ∧
      (Ssel (casselsMat f) (casselsMat g) a b).val.det = 1 ∧
      (Ssel (casselsMat f) (casselsMat g) a b).valᵀ *
        assocMat a ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) * (Ssel (casselsMat f) (casselsMat g) a b).val =
          casselsMat g := by
  have hex : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b := by
    obtain ⟨T, hT, hTb⟩ := exists_sl_first_of_gcd (n := m + 1) (by omega) b hb.1.1
    exact ⟨T, hT, by simpa only [Fin.zero_eta] using hTb⟩
  obtain ⟨hT1, hT2⟩ := Tsel_spec hex
  have h00 : ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) 0 0 = a := by
    rw [← eval_first_col hf, hT2]; exact hb.1.2
  have hsymm : (assocMat (a : ℤ) ((Tsel b).valᵀ * casselsMat f * (Tsel b).val)).IsSymm :=
    assocMat_isSymm (isSymm_conj (casselsMat_isSymm f) _) _
  have hS : ∃ S : GL (Fin m) ℤ, S.val.det = 1 ∧
      S.valᵀ * assocMat a ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) * S.val = casselsMat g := by
    have h2 := hb.2
    rw [assocClass_eq f hex, hb.1.2, assocGram_eq] at h2
    obtain ⟨S, hSd, hSe⟩ := pclassOf_eq_pclassOf_iff.mp h2
    refine ⟨S, hSd, ?_⟩
    have := (eval_mulVec_iff_casselsMat (ci_ofGram hsymm) hg S.val).mp hSe
    rwa [casselsMat_ofGram hsymm] at this
  exact ⟨hT1, hT2, h00, Ssel_spec hS⟩

/-- The vector $w_j = \sum_l (T_b^{\mathsf T}FT_b)_{0, l+1}S_{lj}$. -/
def wvec (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (b : Fin (m + 1) → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) :
    Fin m → ℤ :=
  fun j => ∑ l : Fin m, ((Tsel b).valᵀ * F * (Tsel b).val) 0 l.succ * S l j

/-- The matrix $\begin{pmatrix}1 & \mathbf u^{\mathsf T}\\ 0 & S\end{pmatrix}$ with $u_j = -\lfloor w_j/a\rfloor$. -/
def Mof (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (a : ℕ) (b : Fin (m + 1) → ℤ) (S : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  blk (fun j => -(wvec F b S j / a)) S

/-- The map $(b, \tau) \mapsto (T, \mathbf v)$ of the count by first columns. -/
def phiX (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ)
    (b : Fin (m + 1) → ℤ) (τ : GL (Fin m) ℤ) : GL (Fin (m + 1)) ℤ × (Fin m → ZMod a) :=
  (Tsel b * toGL (Mof F a b (Ssel F G a b * τ).val), fun j => (wvec F b (Ssel F G a b * τ).val j : ZMod a))

/-- The map $T \mapsto \tau = S_b^{-1}S_T$ ($b = Te_0$, $S_T$ the lower right block of $T_b^{-1}T$). -/
def tauOf (F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (G : Matrix (Fin m) (Fin m) ℤ) (a : ℕ)
    (T : GL (Fin (m + 1)) ℤ) : GL (Fin m) ℤ :=
  (Ssel F G a (T.val *ᵥ Pi.single 0 1))⁻¹ *
    toGL ((((Tsel (T.val *ᵥ Pi.single 0 1))⁻¹ * T).val).submatrix Fin.succ Fin.succ)

/-- `toGL` of the matrix of a determinant-one unit is the unit. -/
theorem toGL_val_eq {T : GL (Fin k) ℤ} (h : T.val.det = 1) : toGL T.val = T := Units.ext (toGL_val h)

/-- If $P^{\mathsf T}AP = B$ then $P^{-\mathsf T}BP^{-1} = A$. -/
theorem conj_inv_eq {A B : Matrix (Fin k) (Fin k) ℤ} {P : GL (Fin k) ℤ} (h : P.valᵀ * A * P.val = B) :
    (P⁻¹).valᵀ * B * (P⁻¹).val = A := by
  rw [← h, ← conj_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one, Matrix.one_mul,
    Matrix.mul_one]

/-- The first column of `phiX` is $b$. -/
theorem phiX_first {F : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} {G : Matrix (Fin m) (Fin m) ℤ} {a : ℕ}
    {b : Fin (m + 1) → ℤ} (hTb : (Tsel b).val *ᵥ Pi.single 0 1 = b) (τ : GL (Fin m) ℤ)
    (hS : (Ssel F G a b * τ).val.det = 1) :
    (phiX F G a b τ).1.val *ᵥ Pi.single 0 1 = b := by
  have hdet : (Mof F a b (Ssel F G a b * τ).val).det = 1 := by rw [Mof, det_blk, hS]
  rw [phiX, Units.val_mul, toGL_val hdet, ← mulVec_mulVec, Mof, blk_firstCol, hTb]

/-- `phiX` lands in $X$. -/
theorem phiX_mem (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} [NeZero a] {b : Fin (m + 1) → ℤ} (hb : BPred f g a b)
    {τ : GL (Fin m) ℤ} (hτ : τ ∈ stabSet (casselsMat g)) :
    phiX (casselsMat f) (casselsMat g) a b τ ∈ Xset (casselsMat f) (casselsMat g) a := by
  obtain ⟨hT1, -, h00, hS1, hS2⟩ := bdata hm hf hg hb
  set A := (Tsel b).valᵀ * casselsMat f * (Tsel b).val with hAdef
  set S := (Ssel (casselsMat f) (casselsMat g) a b * τ).val with hSdef
  have hSdet : S.det = 1 := det_mul_eq_one hS1 hτ.1
  set M := Mof (casselsMat f) a b S with hMdef
  have hM : M *ᵥ Pi.single 0 1 = Pi.single 0 1 := blk_firstCol _ _
  have hdetM : M.det = 1 := by rw [hMdef, Mof, det_blk, hSdet]
  have hA : A.IsSymm := isSymm_conj (casselsMat_isSymm f) _
  have hT : (phiX (casselsMat f) (casselsMat g) a b τ).1.val = (Tsel b).val * M := by
    rw [phiX, Units.val_mul, toGL_val hdetM]
  have hconj : (phiX (casselsMat f) (casselsMat g) a b τ).1.valᵀ * casselsMat f *
      (phiX (casselsMat f) (casselsMat g) a b τ).1.val = Mᵀ * A * M := by
    rw [hT, conj_mul']
  have h0 : (Mᵀ * A * M) 0 0 = a := by rw [conj_apply_zero_zero_of_firstCol hM, h00]
  have h1 : ∀ j, (Mᵀ * A * M) 0 j.succ = canLift (phiX (casselsMat f) (casselsMat g) a b τ).2 j := fun j => by
    rw [conj_apply_zero hM, hMdef, Mof, mul_blk_zero_succ, h00, phiX, canLift_cast, Int.emod_def]
    simp only [wvec, hAdef, hSdef]
    ring
  have h2 : assocMat a (Mᵀ * A * M) = casselsMat g := by
    have := assocMat_conj hA hM
    rw [h00] at this
    rw [this, hMdef, Mof, blk_submatrix, hSdef, Units.val_mul, conj_mul', hS2, hτ.2]
  obtain ⟨hdiv, hEq⟩ := eq_hMat (isSymm_conj hA M) (Nat.cast_ne_zero.mpr (NeZero.ne a)) h0 h1 h2
  refine ⟨?_, hdiv, by rw [hconj, hEq]⟩
  rw [hT, det_mul, hT1, hdetM, one_mul]

/-- For $(T, \mathbf v) \in X$, the first column $b = Te_0$ is a representation counted by `sigmaWeight`. -/
theorem bpred_of_mem {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} {x : GL (Fin (m + 1)) ℤ × (Fin m → ZMod a)}
    (hx : x ∈ Xset (casselsMat f) (casselsMat g) a) : BPred f g a (x.1.val *ᵥ Pi.single 0 1) := by
  obtain ⟨hT, hdiv, hH⟩ := hx
  have hex : ∃ T : GL (Fin (m + 1)) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = x.1.val *ᵥ Pi.single 0 1 :=
    ⟨x.1, hT, rfl⟩
  have heval : f.eval (x.1.val *ᵥ Pi.single 0 1) = a := by rw [eval_first_col hf, hH]; rfl
  refine ⟨⟨?_, heval⟩, ?_⟩
  · exact (exists_basis_first_iff_gcd (n := m + 1) (Nat.succ_pos m) _).mp
      ⟨x.1, by simp only [Fin.zero_eta]⟩
  · rw [assocClass_eq f hex]
    obtain ⟨hT1, hT2⟩ := Tsel_spec hex
    have hP := assocGram_properIntEquiv f hf (Tsel (x.1.val *ᵥ Pi.single 0 1)) x.1 hT1 hT (hT2.trans rfl)
    rw [hT2] at hP
    refine pclassOf_eq_pclassOf_iff.mpr (hP.trans ?_)
    rw [assocGram_eq, hH, heval, assocMat_hMat hdiv, ofGram_casselsMat hg]
    exact ProperIntEquiv.refl _

/-- For $(T, \mathbf v) \in X$ with $b = Te_0$: $N = T_b^{-1}T$ has first column $e_0$, $\det N = 1$,
$T^{\mathsf T}FT = N^{\mathsf T}(T_b^{\mathsf T}FT_b)N$ and its lower right block $S_T$ has $S_T^{\mathsf T}G_bS_T = G$. -/
theorem ndata (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} {x : GL (Fin (m + 1)) ℤ × (Fin m → ZMod a)}
    (hx : x ∈ Xset (casselsMat f) (casselsMat g) a) :
    let b := x.1.val *ᵥ Pi.single 0 1
    let N := ((Tsel b)⁻¹ * x.1).val
    N *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ N.det = 1 ∧ (N.submatrix Fin.succ Fin.succ).det = 1 ∧
      x.1.valᵀ * casselsMat f * x.1.val = Nᵀ * ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) * N ∧
      (N.submatrix Fin.succ Fin.succ)ᵀ * assocMat a ((Tsel b).valᵀ * casselsMat f * (Tsel b).val) *
        N.submatrix Fin.succ Fin.succ = casselsMat g := by
  intro b N
  have hb := bpred_of_mem hf hg hx
  obtain ⟨hT1, hT2, h00, -, -⟩ := bdata hm hf hg hb
  obtain ⟨hT, hdiv, hH⟩ := hx
  have hN : N *ᵥ Pi.single 0 1 = Pi.single 0 1 := firstCol_inv_mul (hT2.trans rfl)
  have hdetN : N.det = 1 := by
    show ((Tsel b)⁻¹ * x.1).val.det = 1
    rw [Units.val_mul, det_mul, det_inv_val_eq_one hT1, hT, mul_one]
  have hconj := conj_inv_mul (casselsMat f) (Tsel b) x.1
  refine ⟨hN, hdetN, by rw [← det_of_firstCol hN, hdetN], hconj, ?_⟩
  have hA : ((Tsel b).valᵀ * casselsMat f * (Tsel b).val).IsSymm := isSymm_conj (casselsMat_isSymm f) _
  have := assocMat_conj hA hN
  rw [h00, ← hconj, hH, assocMat_hMat hdiv] at this
  exact this.symm

/-- `tauOf` lands in the proper stabilizer of $G$. -/
theorem tauOf_mem (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} {x : GL (Fin (m + 1)) ℤ × (Fin m → ZMod a)}
    (hx : x ∈ Xset (casselsMat f) (casselsMat g) a) :
    tauOf (casselsMat f) (casselsMat g) a x.1 ∈ stabSet (casselsMat g) := by
  obtain ⟨-, -, hSd, -, hSe⟩ := ndata hm hf hg hx
  obtain ⟨-, -, -, hS1, hS2⟩ := bdata hm hf hg (bpred_of_mem hf hg hx)
  refine ⟨?_, ?_⟩
  · rw [tauOf, Units.val_mul, det_mul, det_inv_val_eq_one hS1, toGL_val hSd, one_mul]
    exact hSd
  · rw [tauOf, Units.val_mul, toGL_val hSd, conj_mul', conj_inv_eq hS2, hSe]

/-- `tauOf ∘ phiX` recovers $\tau$. -/
theorem tauOf_phiX (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} {b : Fin (m + 1) → ℤ} (hb : BPred f g a b)
    {τ : GL (Fin m) ℤ} (hτ : τ ∈ stabSet (casselsMat g)) :
    tauOf (casselsMat f) (casselsMat g) a (phiX (casselsMat f) (casselsMat g) a b τ).1 = τ := by
  obtain ⟨-, hT2, -, hS1, -⟩ := bdata hm hf hg hb
  have hSdet := det_mul_eq_one hS1 hτ.1
  have hdetM : (Mof (casselsMat f) a b (Ssel (casselsMat f) (casselsMat g) a b * τ).val).det = 1 := by
    rw [Mof, det_blk, hSdet]
  rw [tauOf, phiX_first hT2 τ hSdet]
  simp only [phiX]
  rw [inv_mul_cancel_left, toGL_val hdetM, Mof, blk_submatrix, toGL_val_eq hSdet, inv_mul_cancel_left]

/-- `phiX ∘ (first column, tauOf)` is the identity on $X$. -/
theorem phiX_tauOf (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) {a : ℕ} [NeZero a] {x : GL (Fin (m + 1)) ℤ × (Fin m → ZMod a)}
    (hx : x ∈ Xset (casselsMat f) (casselsMat g) a) :
    phiX (casselsMat f) (casselsMat g) a (x.1.val *ᵥ Pi.single 0 1)
      (tauOf (casselsMat f) (casselsMat g) a x.1) = x := by
  obtain ⟨hN, hdetN, hSd, hconj, -⟩ := ndata hm hf hg hx
  obtain ⟨-, -, h00, -, -⟩ := bdata hm hf hg (bpred_of_mem hf hg hx)
  have hH := hx.2.2
  set b := x.1.val *ᵥ Pi.single 0 1 with hbdef
  set N := ((Tsel b)⁻¹ * x.1).val with hNdef
  set A := (Tsel b).valᵀ * casselsMat f * (Tsel b).val with hAdef
  have hS : Ssel (casselsMat f) (casselsMat g) a b * tauOf (casselsMat f) (casselsMat g) a x.1 =
      toGL (N.submatrix Fin.succ Fin.succ) := by
    rw [tauOf, mul_inv_cancel_left]
  have hw : ∀ j, wvec (casselsMat f) b (N.submatrix Fin.succ Fin.succ) j = canLift x.2 j - a * N 0 j.succ := by
    intro j
    have e1 := mul_blk_zero_succ A (fun j => N 0 j.succ) (N.submatrix Fin.succ Fin.succ) j
    rw [← eq_blk hN, h00] at e1
    have e2 : (A * N) 0 j.succ = canLift x.2 j := by
      rw [← conj_apply_zero hN, ← hconj, hH]; rfl
    have e3 : wvec (casselsMat f) b (N.submatrix Fin.succ Fin.succ) j =
        ∑ l : Fin m, A 0 l.succ * N.submatrix Fin.succ Fin.succ l j := rfl
    rw [e3]
    linarith
  have hu : ∀ j, -(wvec (casselsMat f) b (N.submatrix Fin.succ Fin.succ) j / a) = N 0 j.succ := by
    intro j
    rw [hw j, sub_eq_add_neg, ← mul_neg, Int.add_mul_ediv_left _ _ (Nat.cast_ne_zero.mpr (NeZero.ne a)),
      Int.ediv_eq_zero_of_lt (canLift_bounds _ _).1 (canLift_bounds _ _).2]
    ring
  have hMN : Mof (casselsMat f) a b (N.submatrix Fin.succ Fin.succ) = N := by
    calc Mof (casselsMat f) a b (N.submatrix Fin.succ Fin.succ)
        = blk (fun j => N 0 j.succ) (N.submatrix Fin.succ Fin.succ) := by
          rw [Mof]; congr 1; funext j; exact hu j
      _ = N := (eq_blk hN).symm
  refine Prod.ext ?_ ?_
  · show Tsel b * toGL (Mof (casselsMat f) a b
      (Ssel (casselsMat f) (casselsMat g) a b * tauOf (casselsMat f) (casselsMat g) a x.1).val) = x.1
    rw [hS, toGL_val hSd, hMN, hNdef, toGL_val_eq hdetN, mul_inv_cancel_left]
  · funext j
    show ((wvec (casselsMat f) b
      (Ssel (casselsMat f) (casselsMat g) a b * tauOf (casselsMat f) (casselsMat g) a x.1).val j : ℤ) :
        ZMod a) = x.2 j
    rw [hS, toGL_val hSd, hw j]
    push_cast
    rw [ZMod.natCast_self, zero_mul, sub_zero, cast_canLift]

/-- **Count of $X$ by first columns:** $X \cong \{b\} \times O^{+}(G)$. -/
def equivX2 (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) (a : ℕ) [NeZero a] :
    {b // BPred f g a b} × stabSet (casselsMat g) ≃ Xset (casselsMat f) (casselsMat g) a where
  toFun p := ⟨phiX (casselsMat f) (casselsMat g) a p.1.1 p.2.1, phiX_mem hm hf hg p.1.2 p.2.2⟩
  invFun x := (⟨x.1.1.val *ᵥ Pi.single 0 1, bpred_of_mem hf hg x.2⟩,
    ⟨tauOf (casselsMat f) (casselsMat g) a x.1.1, tauOf_mem hm hf hg x.2⟩)
  left_inv p := by
    obtain ⟨-, hT2, -, hS1, -⟩ := bdata hm hf hg p.1.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact phiX_first hT2 _ (det_mul_eq_one hS1 p.2.2.1)
    · exact tauOf_phiX hm hf hg p.1.2 p.2.2
  right_inv x := Subtype.ext (phiX_tauOf hm hf hg x.2)

/-- $|X| = \#\{b\}\cdot o^{+}(G)$. -/
theorem card_Xset_eq_b (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) (a : ℕ) [NeZero a] :
    Nat.card (Xset (casselsMat f) (casselsMat g) a) =
      Nat.card {b // BPred f g a b} * Nat.card (stabSet (casselsMat g)) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (equivX2 hm hf hg a)).symm


/-- **Classical integrality is a genus invariant** (the Hessian is even modulo $2$). -/
theorem SameGenus.isClassicallyIntegral {Q Q' : QuadForm ℤ k} (h : SameGenus Q Q') (hQ : IsClassicallyIntegral Q) :
    IsClassicallyIntegral Q' := by
  refine ci_of_two_dvd_hessian fun i j => ?_
  obtain ⟨g, hg⟩ := (h.isometricGL_zmod (c := 2) (by norm_num)).hessian_eq
  rw [hessian_map, hessian_map] at hg
  have h0 : Q.hessian.map (Int.castRingHom (ZMod 2)) = 0 := by
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (two_dvd_hessian_of_ci hQ a b)
  rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hg
  have := congrFun (congrFun hg i) j
  simp only [Matrix.map_apply, Matrix.zero_apply, eq_intCast] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this.symm

/-- Forms of one genus have the same $\det(f_{ij})$ (classically integral case). -/
theorem casselsMat_det_eq {Q Q' : QuadForm ℤ k} (hQ : IsClassicallyIntegral Q) (hQ' : IsClassicallyIntegral Q')
    (h : SameGenus Q Q') : (casselsMat Q).det = (casselsMat Q').det := by
  have := h.hessian_det_eq
  rw [hessian_eq_two_smul_casselsMat hQ, hessian_eq_two_smul_casselsMat hQ', det_smul, det_smul] at this
  exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) this

/-- Admissibility of $\mathbf v$ for $f$ is: $a \mid c_ic_j + g_{ij}$ and $h_{\mathbf v}$ is properly equivalent to $f$. -/
theorem vpred_iff {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) {G : Matrix (Fin m) (Fin m) ℤ}
    (hG : G.IsSymm) {a : ℕ} (v : Fin m → ZMod a) :
    VPred (casselsMat f) G a v ↔ (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + G i j) ∧
      ProperIntEquiv f (ofGram (hMat a (canLift v) G)) := by
  have hH : (hMat (a : ℤ) (canLift v) G).IsSymm := hMat_isSymm hG
  refine and_congr Iff.rfl (exists_congr fun T => and_congr Iff.rfl ?_)
  rw [eval_mulVec_iff_casselsMat hf (ci_ofGram hH), casselsMat_ofGram hH]

/-- The congruence classes counted by $\rho$, via the canonical lift. -/
theorem rho_iff {f : QuadForm ℤ (m + 1)} {G : Matrix (Fin m) (Fin m) ℤ} (hG : G.IsSymm) {a : ℕ} [NeZero a]
    (v : Fin m → ZMod a) :
    (∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v i) ∧ (∀ i j, (a : ℤ) ∣ c i * c j + G i j) ∧
      SameGenus f (ofGram (hMat a c G))) ↔
    (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + G i j) ∧ SameGenus f (ofGram (hMat a (canLift v) G)) := by
  constructor
  · rintro ⟨c, hc, hdiv, hs⟩
    have hcc : ∀ i, (a : ℤ) ∣ canLift v i - c i := fun i =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ((hc i).trans (cast_canLift v i).symm)
    obtain ⟨hdiv', hP⟩ := hMat_change hG c (canLift v) hcc hdiv
    exact ⟨hdiv', hs.trans hP.intEquiv.sameGenus⟩
  · rintro ⟨hdiv, hs⟩
    exact ⟨canLift v, cast_canLift v, hdiv, hs⟩

/-- **Cassels, Lemma 6.2, for one class** ((6.13)–(6.33), pp. 146–148): for $f$ positive definite and classically
integral in $m + 1 \ge 2$ variables, $a > 0$ and $g$ positive definite classically integral in $m$ variables with
$\det(g_{ij}) = a^{m-1}\det(f_{ij})$: $\sigma(a, \mathcal F, [g]) = \rho(\mathcal F, g)/o^{+}(g)$. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.2, pp. 146–149 (one proper class: σ = ρ/o⁺(g))"]
theorem sigmaWeight_eq (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) (hfpd : IntQF.PosDef f)
    {a : ℕ} (ha : 0 < a) {g : QuadForm ℤ m} (hg : IsClassicallyIntegral g) (hgpd : IntQF.PosDef g)
    (_hdet : (casselsMat g).det = (a : ℤ) ^ (m - 1) * (casselsMat f).det) :
    sigmaWeight f a (pclassOf g) = (rhoCount f a (casselsMat g) : ℝ) / Nat.card (AutPlus g) := by
  classical
  -- `hdet` (Cassels' determinant condition) is not needed for the identity itself
  have : NeZero a := ⟨ha.ne'⟩
  have hG : (casselsMat g).IsSymm := casselsMat_isSymm g
  have hPG := pgenusClasses_finite (Nat.succ_pos m) hfpd.nondegenerate
  have hog : (0 : ℝ) < Nat.card (AutPlus g) := by exact_mod_cast card_autPlus_pos hgpd
  -- the double count, for one proper class `D` of the genus
  have hD : ∀ D ∈ pgenusClasses f,
      (Nat.card {b // b ∈ primRepSet D.out a ∧ assocClass D.out b = pclassOf g} : ℝ) / Nat.card (AutPlus D.out) =
        ((Finset.univ.filter (fun v : Fin m → ZMod a =>
          (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + casselsMat g i j) ∧
            ProperIntEquiv D.out (ofGram (hMat a (canLift v) (casselsMat g))))).card : ℝ) /
          Nat.card (AutPlus g) := by
    intro D hD
    have hs := mem_pgenusClasses_iff_out.mp hD
    have hci := hs.isClassicallyIntegral hf
    have hpd := hs.posDef hfpd
    have h1 := card_Xset_eq_v (casselsMat D.out) (casselsMat g) a
    have h2 := card_Xset_eq_b hm hci hg a
    rw [card_stabSet hci] at h1
    rw [card_stabSet hg] at h2
    unfold BPred at h2
    have hV : Nat.card {v // VPred (casselsMat D.out) (casselsMat g) a v} =
        (Finset.univ.filter (fun v : Fin m → ZMod a =>
          (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + casselsMat g i j) ∧
            ProperIntEquiv D.out (ofGram (hMat a (canLift v) (casselsMat g))))).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact vpred_iff hci hG v
    have hoD : (0 : ℝ) < Nat.card (AutPlus D.out) := by exact_mod_cast card_autPlus_pos hpd
    rw [div_eq_div_iff hoD.ne' hog.ne', ← hV]
    exact_mod_cast h2.symm.trans h1
  rw [sigmaWeight, finsum_mem_eq_finite_toFinset_sum _ hPG,
    Finset.sum_congr rfl (fun D hD' => hD D ((Set.Finite.mem_toFinset _).mp hD')), ← Finset.sum_div]
  congr 1
  -- summing over the proper classes of the genus gives ρ
  have hρ : rhoCount f a (casselsMat g) = (Finset.univ.filter (fun v : Fin m → ZMod a =>
      (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + casselsMat g i j) ∧
        SameGenus f (ofGram (hMat a (canLift v) (casselsMat g))))).card := by
    rw [rhoCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rho_iff hG v
  have hmaps : ∀ v ∈ Finset.univ.filter (fun v : Fin m → ZMod a =>
      (∀ i j, (a : ℤ) ∣ canLift v i * canLift v j + casselsMat g i j) ∧
        SameGenus f (ofGram (hMat a (canLift v) (casselsMat g)))),
      pclassOf (ofGram (hMat a (canLift v) (casselsMat g))) ∈ hPG.toFinset := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Set.Finite.mem_toFinset]
    exact ⟨_, rfl, hv.2.2⟩
  rw [hρ, Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl fun D hD' => ?_
  have hDm := (Set.Finite.mem_toFinset _).mp hD'
  congr 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hdiv, hP⟩
    refine ⟨⟨hdiv, (mem_pgenusClasses_iff_out.mp hDm).trans hP.intEquiv.sameGenus⟩, ?_⟩
    rw [← pclassOf_out D]
    exact (pclassOf_eq_pclassOf_iff.mpr hP).symm
  · rintro ⟨⟨hdiv, -⟩, hcl⟩
    refine ⟨hdiv, pclassOf_eq_pclassOf_iff.mp ?_⟩
    rw [pclassOf_out D]
    exact hcl.symm

/-- **Cassels, Lemma 6.2** (Ch. 9, p. 146): *with the notation introduced above,
$\sigma(a, \mathcal F, \mathcal G) = \rho(\mathcal F, \mathcal G)\,W(\mathcal G)$ (6.12), where $W(\mathcal G)$ is the
weight of the genus $\mathcal G$.* Here $\rho(\mathcal F, g) = \rho$ for every $g$ in $\mathcal G$ is a hypothesis
(Cassels (6.10) derives it from Lemma 4.3, not formalized); the formula (6.12) is garbled in the scan and is the one
the proof establishes. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.2, (6.12), p. 146 (ρ constant on the genus assumed)"]
theorem sigmaGenus_eq (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f) (hfpd : IntQF.PosDef f)
    {a : ℕ} (ha : 0 < a) {g : QuadForm ℤ m} (hg : IsClassicallyIntegral g) (hgpd : IntQF.PosDef g)
    (hdet : (casselsMat g).det = (a : ℤ) ^ (m - 1) * (casselsMat f).det) {ρ : ℕ}
    (hρ : ∀ g', SameGenus g g' → rhoCount f a (casselsMat g') = ρ) :
    sigmaGenus f a g = ρ * pweight g := by
  have hPG := pgenusClasses_finite (show 0 < m by omega) hgpd.nondegenerate
  rw [sigmaGenus, pweight, mul_finsum_mem' (fun C : PClass m => ((Nat.card (AutPlus C.out) : ℝ))⁻¹) (ρ : ℝ) hPG]
  refine finsum_mem_congr rfl fun C hC => ?_
  have hs : SameGenus g C.out := mem_pgenusClasses_iff_out.mp hC
  have hci := hs.isClassicallyIntegral hg
  have hpd := hs.posDef hgpd
  have hdet' : (casselsMat C.out).det = (a : ℤ) ^ (m - 1) * (casselsMat f).det := by
    rw [← casselsMat_det_eq hg hci hs, hdet]
  have := sigmaWeight_eq hm hf hfpd ha hci hpd hdet'
  rw [pclassOf_out] at this
  rw [this, hρ _ hs, div_eq_mul_inv]

end QuadFormsKB.Siegel
