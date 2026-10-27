/-
# Cassels, Chapter 9, Example 5 for $c = 2, 3$; primitive representations by $x^2 + y^2 + cz^2$

**Layer:** integer-valued forms `QuadForm ℤ 3`, the genus `Siegel.SameGenus`, $\mathrm{GL}_3(\mathbb Z)$-equivalence
`IntEquiv` (`Ch9Sec1.lean`), Cassels' matrix $(f_{ij}) = H/2$ (`casselsMat`, `Ch9Sec6Weight.lean`), Hermite's bound
(`Hermite.exists_hermite_bound`, `FourSquaresClassNumber.lean`).

**Proves**
* Example 5 for $c = 2$ and $c = 3$ (`one_class_sumSqAdd_two`, `one_class_sumSqAdd_three`): $x^2 + y^2 + cz^2$ is in a
  genus of one class (the cases $c = 1, -1, -2, -3$ are `one_class_sumSqAdd`, `Ch9Examples.lean`);
* Example 5, second part (`primRep_sumSqAdd_iff`): for $c \in \{\pm1, \pm2, \pm3\}$ and $m \ne 0$, $m$ is primitively
  represented over $\mathbb Z$ by $x^2 + y^2 + cz^2$ iff it is so over $\mathbb R$ ($m > 0$ if $c > 0$) and over
  $\mathbb Z_p$ for $p = 2$ and each prime $p \mid c$.

*Proof for $c = 2, 3$ (Hermite reduction, not a quoted argument of Cassels):* a form $f'$ in the genus of
$x^2 + y^2 + cz^2$ is classically integral, positive definite and has $\det(f_{ij}) = c$ (genus invariants), so
$A = (f'_{ij})$ is a positive definite integral symmetric $3 \times 3$ matrix of determinant $c \in \{2, 3\}$.
Hermite's bound ($27h^3 \le 64c$) gives a congruent matrix with corner $1$ (`cong_ternary`); the corner splits off
(`cong_split_three`), and the $2 \times 2$ Schur complement, by the bound $3h^2 \le 4c$, is congruent to
$\mathrm{diag}(1, c)$ or (for $c = 3$, $h = 2$) to $\begin{pmatrix}2&1\\1&2\end{pmatrix}$ (`cong_two_corner_one`,
`cong_two_corner_two`). For $c = 3$ the second possibility, the form $x^2 + 2y^2 + 2yz + 2z^2$ (`sumSqEx`), is not in
the genus: modulo $4$ it has $8$ zeros in $(\mathbb Z/4)^3$, while $x^2 + y^2 + 3z^2$ has $24$
(`not_sameGenus_sumSqAdd_three_sumSqEx`, via `SameGenus.isometricGL_zmod`).
The criterion follows from Theorem 5.1, Corollary (`exists_primRep_of_one_class`) since $\det H = 8c$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples
import QuadFormsKB.Literature.Cassels.Ch9Examples5
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Literature.Cassels.Ch9Sec5Squares
import QuadFormsKB.Siegel.FourSquaresClassNumber

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel.Hermite

/-- **A symmetric $2 \times 2$ integral matrix with corner $1$ is congruent to $\mathrm{diag}(1, \det B)$:**
if $B^{\mathsf T} = B$ and $B_{00} = 1$ then $g^{\mathsf T}Bg = \mathrm{diag}(1, \det B)$ for
$g = \begin{pmatrix}1 & -B_{01}\\ 0 & 1\end{pmatrix} \in \mathrm{GL}_2(\mathbb Z)$. -/
theorem cong_two_corner_one (B : Matrix (Fin 2) (Fin 2) ℤ) (hs : B.IsSymm) (h : B 0 0 = 1) :
    ∃ g : GL (Fin 2) ℤ, g.valᵀ * B * g.val = !![1, 0; 0, B.det] := by
  have hsym : B 1 0 = B 0 1 := hs.apply 0 1
  let g : Matrix (Fin 2) (Fin 2) ℤ := !![1, -B 0 1; 0, 1]
  have hu : IsUnit g.det := by simp [g, Matrix.det_fin_two]
  refine ⟨Matrix.nonsingInvUnit _ hu, ?_⟩
  show gᵀ * B * g = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, hsym, h]
  ring

/-- **A symmetric $2 \times 2$ integral matrix with corner $2$ and determinant $3$ is congruent to
$\begin{pmatrix}2&1\\1&2\end{pmatrix}$:** if $B^{\mathsf T} = B$, $B_{00} = 2$, $\det B = 3$, then $B_{01}$ is odd
($B_{01} = 2k + 1$) and $g = \begin{pmatrix}1 & -k\\ 0 & 1\end{pmatrix}$ gives $g^{\mathsf T}Bg =
\begin{pmatrix}2&1\\1&2\end{pmatrix}$. -/
theorem cong_two_corner_two (B : Matrix (Fin 2) (Fin 2) ℤ) (hs : B.IsSymm) (h : B 0 0 = 2)
    (hd : B.det = 3) : ∃ g : GL (Fin 2) ℤ, g.valᵀ * B * g.val = !![2, 1; 1, 2] := by
  have hsym : B 1 0 = B 0 1 := hs.apply 0 1
  rw [Matrix.det_fin_two, hsym, h] at hd
  obtain ⟨k, hk⟩ : ∃ k, B 0 1 = 2 * k + 1 := by
    rcases Int.even_or_odd (B 0 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have : B 0 1 * B 0 1 = 4 * (k * k) := by rw [hk]; ring
      omega
    · exact ⟨k, hk⟩
  have he : B 1 1 = 2 + 2 * k * k + 2 * k := by
    have : B 0 1 * B 0 1 = (2 * k + 1) * (2 * k + 1) := by rw [hk]
    nlinarith
  let g : Matrix (Fin 2) (Fin 2) ℤ := !![1, -k; 0, 1]
  have hu : IsUnit g.det := by simp [g, Matrix.det_fin_two]
  refine ⟨Matrix.nonsingInvUnit _ hu, ?_⟩
  show gᵀ * B * g = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, Matrix.mul_apply, Fin.sum_univ_two, hsym, h, hk, he] <;> ring

/-- **The block matrix $(1) \oplus S$** ($S$ of size $2$): $\begin{pmatrix}1&0\\0&S\end{pmatrix}$ as a $3 \times 3$
matrix (indices $0, 1, 2$). -/
def lift (S : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![1, 0, 0], ![0, S 0 0, S 0 1], ![0, S 1 0, S 1 1]]

/-- **The block matrix $(1) \oplus u$** used as a change of basis (same shape as `lift`, kept separate to mark its
role as a transformation rather than a Gram matrix). -/
def liftG (u : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![1, 0, 0], ![0, u 0 0, u 0 1], ![0, u 1 0, u 1 1]]

/-- $\det\big((1) \oplus u\big) = \det u$. -/
theorem det_liftG (u : Matrix (Fin 2) (Fin 2) ℤ) : (liftG u).det = u.det := by
  simp [liftG, Matrix.det_fin_three, Matrix.det_fin_two]

/-- **Extension of $u \in \mathrm{GL}_2(\mathbb Z)$ to $(1) \oplus u \in \mathrm{GL}_3(\mathbb Z)$.** -/
def liftGL (u : GL (Fin 2) ℤ) : GL (Fin 3) ℤ :=
  Matrix.nonsingInvUnit (liftG u.val) (by
    rw [det_liftG]; exact (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit)

/-- The underlying matrix of `liftGL u` is `liftG u`. -/
theorem liftGL_val (u : GL (Fin 2) ℤ) : (liftGL u).val = liftG u.val := rfl

/-- **Congruence of block matrices:** $\big((1) \oplus u\big)^{\mathsf T}\big((1) \oplus S\big)\big((1) \oplus u\big) =
(1) \oplus u^{\mathsf T}Su$. -/
theorem conj_lift (S : Matrix (Fin 2) (Fin 2) ℤ) (u : Matrix (Fin 2) (Fin 2) ℤ) :
    (liftG u)ᵀ * lift S * liftG u = lift (uᵀ * S * u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lift, liftG, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

/-- **Splitting off a corner $1$:** if $A \in M_3(\mathbb Z)$ is symmetric with $A_{00} = 1$, then
$g^{\mathsf T}Ag = (1) \oplus S(A)$ for some $g \in \mathrm{GL}_3(\mathbb Z)$, $S(A)$ the (scaled, here unscaled)
Schur complement `schur A`, $S(A)_{ij} = A_{i+1,j+1} - A_{i+1,0}A_{0,j+1}$. Here $g$ is the elementary matrix clearing
the first row and column. -/
theorem cong_split_three (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : IsSymm A) (h : A 0 0 = 1) :
    ∃ g : GL (Fin 3) ℤ, g.valᵀ * A * g.val = lift (schur A) := by
  have s10 : A 1 0 = A 0 1 := hA.apply 0 1
  have s20 : A 2 0 = A 0 2 := hA.apply 0 2
  have s21 : A 2 1 = A 1 2 := hA.apply 1 2
  let g : Matrix (Fin 3) (Fin 3) ℤ := !![1, -A 0 1, -A 0 2; 0, 1, 0; 0, 0, 1]
  have hu : IsUnit g.det := by simp [g, Matrix.det_fin_three]
  refine ⟨Matrix.nonsingInvUnit _ hu, ?_⟩
  show gᵀ * A * g = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, lift, schur, colT, rowT, vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_three, s10, s20, s21, h] <;> ring

/-- **Composition of congruences:** if $g_2^{\mathsf T}A_1g_2 = (1) \oplus S$ and $u^{\mathsf T}Su = T$ with
$u \in \mathrm{GL}_2(\mathbb Z)$, then $g^{\mathsf T}A_1g = (1) \oplus T$ for $g = g_2\,((1) \oplus u)$. -/
theorem cong_lift_of (A1 : Matrix (Fin 3) (Fin 3) ℤ) (S T : Matrix (Fin 2) (Fin 2) ℤ) (g2 : GL (Fin 3) ℤ)
    (hg2 : g2.valᵀ * A1 * g2.val = lift S) (u : GL (Fin 2) ℤ) (hu : u.valᵀ * S * u.val = T) :
    ∃ g : GL (Fin 3) ℤ, g.valᵀ * A1 * g.val = lift T :=
  ⟨g2 * liftGL u, by rw [conj_mul, hg2, liftGL_val, conj_lift, hu]⟩

/-- **Ternary matrices with corner $1$ and determinant $2$ or $3$:** let $A_1$ be symmetric positive definite
(`IsPosDefInt`), $(A_1)_{00} = 1$ (`h00`), $\det A_1 = d$ (`hd`) with $d = 2$ or $d = 3$ (`hd2`). Then $A_1$ is
$\mathrm{GL}_3(\mathbb Z)$-congruent to $\mathrm{diag}(1, 1, d)$, or ($d = 3$ only) to
$\mathrm{diag}(1) \oplus \begin{pmatrix}2&1\\1&2\end{pmatrix}$.
*Proof:* split off the corner (`cong_split_three`); the Schur complement $S$ is positive definite of determinant $d$
(`det_schur`); Hermite's bound for $S$ ($3h^2 \le 4d$) gives a congruent matrix with corner $h \in \{1, 2\}$,
$h = 2$ only for $d = 3$; conclude by `cong_two_corner_one`, `cong_two_corner_two`. -/
theorem cong_ternary_of_corner (A1 : Matrix (Fin 3) (Fin 3) ℤ) (hA1 : IsPosDefInt A1) (h00 : A1 0 0 = 1)
    {d : ℤ} (hd : A1.det = d) (hd2 : d = 2 ∨ d = 3) :
    ∃ g : GL (Fin 3) ℤ, g.valᵀ * A1 * g.val = lift !![1, 0; 0, d] ∨
      (d = 3 ∧ g.valᵀ * A1 * g.val = lift !![2, 1; 1, 2]) := by
  obtain ⟨g2, hg2⟩ := cong_split_three A1 hA1.1 h00
  have hS := hA1.schur
  have hdS : (schur A1).det = d := by
    have := det_schur A1
    rw [h00] at this
    simpa [hd] using this.symm
  obtain ⟨g3, hg3⟩ := exists_hermite_bound 1 (schur A1) hS
  have hS' := hS.conj g3
  have hdS' : (g3.valᵀ * schur A1 * g3.val).det = d := (det_conj _ g3).trans hdS
  have hpos := hS'.pos00
  have ht : tri 1 = 1 := rfl
  rw [ht, hdS] at hg3
  have hsq : ((g3.valᵀ * schur A1 * g3.val) 0 0) ^ 2 ≤ 4 := by
    rcases hd2 with rfl | rfl <;> norm_num at hg3 <;> nlinarith
  have hle : (g3.valᵀ * schur A1 * g3.val) 0 0 ≤ 2 := by nlinarith
  have hcase : (g3.valᵀ * schur A1 * g3.val) 0 0 = 1 ∨ (g3.valᵀ * schur A1 * g3.val) 0 0 = 2 := by omega
  rcases hcase with h1 | h2
  · obtain ⟨g4, hg4⟩ := cong_two_corner_one _ hS'.1 h1
    rw [hdS'] at hg4
    obtain ⟨g, hg⟩ := cong_lift_of A1 (schur A1) _ g2 hg2 (g3 * g4) (by rw [conj_mul, hg4])
    exact ⟨g, Or.inl hg⟩
  · have hd3 : d = 3 := by
      rcases hd2 with rfl | rfl
      · exfalso
        rw [h2] at hg3
        norm_num at hg3
      · rfl
    subst hd3
    obtain ⟨g4, hg4⟩ := cong_two_corner_two _ hS'.1 h2 hdS'
    obtain ⟨g, hg⟩ := cong_lift_of A1 (schur A1) _ g2 hg2 (g3 * g4) (by rw [conj_mul, hg4])
    exact ⟨g, Or.inr ⟨rfl, hg⟩⟩

/-- **Positive definite ternary integral matrices of determinant $2$ or $3$** (Cassels' $F = (f_{ij})$,
$d = \det F$): if $A \in M_3(\mathbb Z)$ is symmetric positive definite (`hA`) with $\det A = d$ (`hd`),
$d \in \{2, 3\}$ (`hd2`), then $A$ is $\mathrm{GL}_3(\mathbb Z)$-congruent to $\mathrm{diag}(1, 1, d)$, or ($d = 3$
only) to $(1) \oplus \begin{pmatrix}2&1\\1&2\end{pmatrix}$.
*Proof:* Hermite's bound for $n = 3$ ($3^3h^3 \le 4^3d$) gives a congruent matrix with corner $h = 1$; then
`cong_ternary_of_corner`. -/
theorem cong_ternary (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : IsPosDefInt A) {d : ℤ} (hd : A.det = d)
    (hd2 : d = 2 ∨ d = 3) :
    ∃ g : GL (Fin 3) ℤ, g.valᵀ * A * g.val = lift !![1, 0; 0, d] ∨
      (d = 3 ∧ g.valᵀ * A * g.val = lift !![2, 1; 1, 2]) := by
  obtain ⟨g1, hg1⟩ := exists_hermite_bound 2 A hA
  have hA1 := hA.conj g1
  have hdet1 : (g1.valᵀ * A * g1.val).det = d := (det_conj A g1).trans hd
  have ht : tri 2 = 3 := rfl
  rw [ht, hd] at hg1
  have hpos := hA1.pos00
  have h00 : (g1.valᵀ * A * g1.val) 0 0 = 1 := by
    by_contra hne
    have h2 : 2 ≤ (g1.valᵀ * A * g1.val) 0 0 := by omega
    have h8 : (2 : ℤ) ^ 3 ≤ ((g1.valᵀ * A * g1.val) 0 0) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    rcases hd2 with rfl | rfl <;> norm_num at hg1 <;> nlinarith
  obtain ⟨g, hg⟩ := cong_ternary_of_corner _ hA1 h00 hdet1 hd2
  refine ⟨g1 * g, ?_⟩
  rw [conj_mul]
  exact hg

/-- $\det\big((1) \oplus S\big) = \det S$. -/
theorem det_lift (S : Matrix (Fin 2) (Fin 2) ℤ) : (lift S).det = S.det := det_liftG S

end QuadFormsKB.Siegel.Hermite

namespace QuadFormsKB.Siegel

open Hermite

/-- **The second ternary form of determinant $3$:** $x_0^2 + 2x_1^2 + 2x_1x_2 + 2x_2^2$ (variables $x_0, x_1, x_2$),
with Cassels' matrix $(1) \oplus \begin{pmatrix}2&1\\1&2\end{pmatrix}$; it is not in the genus of $x^2 + y^2 + 3z^2$
(`not_sameGenus_sumSqAdd_three_sumSqEx`). -/
def sumSqEx : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 2, 2], ![0, 0, 2]]

/-- **Evaluation of `sumSqEx` over any commutative ring $R$** (after base change):
$x_0^2 + 2x_1^2 + 2x_1x_2 + 2x_2^2$. -/
theorem eval_map_sumSqEx {R : Type*} [CommRing R] (x : Fin 3 → R) :
    (sumSqEx.map (Int.castRingHom R)).eval x = x 0 ^ 2 + 2 * x 1 ^ 2 + 2 * x 1 * x 2 + 2 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, sumSqEx, QuadForm.ofUpper, QuadForm.map]
  ring

/-- Cassels' matrix of `sumSqEx` is $(1) \oplus \begin{pmatrix}2&1\\1&2\end{pmatrix}$. -/
theorem casselsMat_sumSqEx : casselsMat sumSqEx = lift !![2, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [casselsMat, QuadForm.hessian, sumSqEx, QuadForm.ofUpper, lift]

/-- Cassels' matrix of $x^2 + y^2 + cz^2$ is $\mathrm{diag}(1, 1, c)$, i.e. $(1) \oplus \mathrm{diag}(1, c)$. -/
theorem casselsMat_sumSqAdd (c : ℤ) : casselsMat (sumSqAdd c) = lift !![1, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [casselsMat, QuadForm.hessian, sumSqAdd, QuadForm.diag, lift, Matrix.diagonal_apply]
  omega

/-- `sumSqEx` is classically integral (all cross coefficients are even). -/
theorem ci_sumSqEx : IsClassicallyIntegral sumSqEx := by
  rw [isClassicallyIntegral_iff]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sumSqEx, QuadForm.ofUpper]

/-- $x^2 + y^2 + cz^2$ is classically integral (it is diagonal). -/
theorem ci_sumSqAdd (c : ℤ) : IsClassicallyIntegral (sumSqAdd c) := by
  rw [isClassicallyIntegral_iff]
  intro i j hij
  simp [sumSqAdd, QuadForm.diag, hij.ne]

/-- $x^2 + y^2 + cz^2$ is positive definite for $c > 0$ (`hc`). -/
theorem posDef_sumSqAdd {c : ℤ} (hc : 0 < c) : IntQF.PosDef (sumSqAdd c) := by
  intro x hx
  show 0 < (QuadForm.diag ![1, 1, c] : QuadForm ℤ 3).eval x
  rw [eval_diag_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have h0 := sq_nonneg (x 0)
  have h1 := sq_nonneg (x 1)
  have h2 := mul_nonneg hc.le (sq_nonneg (x 2))
  fin_cases i
  · have := sq_pos_of_ne_zero (show x 0 ≠ 0 from hi)
    linarith
  · have := sq_pos_of_ne_zero (show x 1 ≠ 0 from hi)
    linarith
  · have := mul_pos hc (sq_pos_of_ne_zero (show x 2 ≠ 0 from hi))
    linarith

/-- **Forms in the genus of $x^2 + y^2 + cz^2$, $c = 2, 3$** (`hc`, genus hypothesis `h`): Cassels' matrix of $f'$ is
$\mathrm{GL}_3(\mathbb Z)$-congruent to that of $x^2 + y^2 + cz^2$ or, for $c = 3$ only, to that of `sumSqEx`.
*Proof:* $f'$ is classically integral and positive definite (genus invariants), $\det(f'_{ij}) = c$
(`casselsMat_det_eq`); apply `cong_ternary`. -/
theorem exists_cong_of_sameGenus {c : ℤ} (hc : c = 2 ∨ c = 3) {f' : QuadForm ℤ 3}
    (h : SameGenus (sumSqAdd c) f') :
    ∃ g : GL (Fin 3) ℤ, g.valᵀ * casselsMat f' * g.val = casselsMat (sumSqAdd c) ∨
        (c = 3 ∧ g.valᵀ * casselsMat f' * g.val = casselsMat sumSqEx) := by
  have hpos : IntQF.PosDef (sumSqAdd c) := posDef_sumSqAdd (by omega)
  have hci' := h.isClassicallyIntegral (ci_sumSqAdd c)
  have hpd' : IntQF.PosDef f' := h.posDef hpos
  have hA : IsPosDefInt (casselsMat f') := by
    refine ⟨casselsMat_isSymm f', fun x hx => ?_⟩
    rw [← eval_eq_casselsMat hci']
    exact hpd' x hx
  have hdet : (casselsMat f').det = c := by
    rw [← casselsMat_det_eq (ci_sumSqAdd c) hci' h, casselsMat_sumSqAdd, det_lift]
    simp
  obtain ⟨g, hg⟩ := cong_ternary _ hA hdet hc
  refine ⟨g, ?_⟩
  rw [casselsMat_sumSqAdd, casselsMat_sumSqEx]
  simpa using hg

/-- The number of zeros of $x^2 + y^2 + 3z^2$ modulo $4$ is $24$. -/
theorem card_zeros_sumSqAdd_three :
    (Finset.univ.filter fun x : Fin 3 → ZMod 4 =>
      ((sumSqAdd 3).map (Int.castRingHom (ZMod 4))).eval x = 0).card = 24 := by
  simp only [sumSqAdd, eval_map_diag_three]
  decide

/-- The number of zeros of $x^2 + 2y^2 + 2yz + 2z^2$ modulo $4$ is $8$. -/
theorem card_zeros_sumSqEx :
    (Finset.univ.filter fun x : Fin 3 → ZMod 4 =>
      (sumSqEx.map (Int.castRingHom (ZMod 4))).eval x = 0).card = 8 := by
  simp only [eval_map_sumSqEx]
  decide

/-- $x^2 + y^2 + 3z^2$ is not in the genus of $x^2 + 2y^2 + 2yz + 2z^2$. -/
theorem not_sameGenus_sumSqAdd_three_sumSqEx : ¬ SameGenus (sumSqAdd 3) sumSqEx := by
  intro h
  have := card_zeros_eq_of_isometricGL (h.isometricGL_zmod (c := 4) (by norm_num))
  rw [card_zeros_sumSqAdd_three, card_zeros_sumSqEx] at this
  exact absurd this (by norm_num)

/-- **Cassels, Ch. 9, Example 5** (p. 162), $c = 2$: $x^2 + y^2 + 2z^2$ is in a genus of one class. -/
@[kb "cassels1978" "Ch. 9, Ex. 5, p. 162 (c = 2)"]
theorem one_class_sumSqAdd_two (f' : QuadForm ℤ 3) (h : SameGenus (sumSqAdd 2) f') :
    IntEquiv (sumSqAdd 2) f' := by
  obtain ⟨g, hg | ⟨h3, -⟩⟩ := exists_cong_of_sameGenus (c := 2) (Or.inl rfl) h
  · have hci' := h.isClassicallyIntegral (ci_sumSqAdd 2)
    exact (show IntEquiv f' (sumSqAdd 2) from
      ⟨g, (eval_mulVec_iff_casselsMat hci' (ci_sumSqAdd 2) g.val).mpr hg⟩).symm
  · omega

/-- **Cassels, Ch. 9, Example 5** (p. 162), $c = 3$: $x^2 + y^2 + 3z^2$ is in a genus of one class. -/
@[kb "cassels1978" "Ch. 9, Ex. 5, p. 162 (c = 3)"]
theorem one_class_sumSqAdd_three (f' : QuadForm ℤ 3) (h : SameGenus (sumSqAdd 3) f') :
    IntEquiv (sumSqAdd 3) f' := by
  have hci' := h.isClassicallyIntegral (ci_sumSqAdd 3)
  obtain ⟨g, hg | ⟨-, hg⟩⟩ := exists_cong_of_sameGenus (c := 3) (Or.inr rfl) h
  · exact (show IntEquiv f' (sumSqAdd 3) from
      ⟨g, (eval_mulVec_iff_casselsMat hci' (ci_sumSqAdd 3) g.val).mpr hg⟩).symm
  · exfalso
    have he : IntEquiv f' sumSqEx :=
      ⟨g, (eval_mulVec_iff_casselsMat hci' ci_sumSqEx g.val).mpr hg⟩
    exact not_sameGenus_sumSqAdd_three_sumSqEx (h.trans he.sameGenus)

/-- **Example 5 for all six values:** for $c \in \{\pm1, \pm2, \pm3\}$ every form in the genus of
$x^2 + y^2 + cz^2$ is $\mathbb Z$-equivalent to it. -/
theorem one_class_sumSqAdd_six {c : ℤ} (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2 ∨ c = 3 ∨ c = -3)
    (f' : QuadForm ℤ 3) (h : SameGenus (sumSqAdd c) f') : IntEquiv (sumSqAdd c) f' := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_class_sumSqAdd (Or.inl rfl) f' h
  · exact one_class_sumSqAdd (Or.inr (Or.inl rfl)) f' h
  · exact one_class_sumSqAdd_two f' h
  · exact one_class_sumSqAdd (Or.inr (Or.inr (Or.inl rfl))) f' h
  · exact one_class_sumSqAdd_three f' h
  · exact one_class_sumSqAdd (Or.inr (Or.inr (Or.inr rfl))) f' h

/-- Evaluation of $x^2 + y^2 + cz^2$ over any commutative ring. -/
theorem eval_map_sumSqAdd {R : Type*} [CommRing R] (c : ℤ) (x : Fin 3 → R) :
    ((sumSqAdd c).map (Int.castRingHom R)).eval x = x 0 ^ 2 + x 1 ^ 2 + (c : R) * x 2 ^ 2 := by
  simp only [sumSqAdd, eval_map_diag_three]
  simp

/-- Evaluation of $x^2 + y^2 + cz^2$ over $\mathbb R$ (via `evalIn`). -/
theorem evalIn_real_sumSqAdd (c : ℤ) (x : Fin 3 → ℝ) :
    (sumSqAdd c).evalIn ℝ x = x 0 ^ 2 + x 1 ^ 2 + (c : ℝ) * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, sumSqAdd, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- **Cassels, Ch. 9, Example 5** (p. 162), second part: *deduce necessary and sufficient conditions for an integer
$m$ to be primitively represented by each of these forms.* For $c \in \{\pm1, \pm2, \pm3\}$ and an integer $m \ne 0$,
$m$ is primitively represented over $\mathbb Z$ by $x^2 + y^2 + cz^2$ (a vector $\mathbf x \in \mathbb Z^3$ with
$\gcd(x_0,x_1,x_2) = 1$) if and only if
* ($\mathbb R$) $m > 0$ when $c > 0$ (no condition when $c < 0$: the form is then indefinite), and
* ($\mathbb Z_p$) for $p = 2$ and every prime $p \mid c$, $m$ is primitively represented over $\mathbb Z_p$
  (some coordinate is a unit).

*Proof:* "only if": reduce the integral vector to $\mathbb Z_p$; some coordinate is prime to $p$, as the gcd is $1$.
"If": Theorem 5.1, Corollary (`exists_primRep_of_one_class`) for $f = x^2 + y^2 + cz^2$, $\det H = 8c$, in the genus of
one class (`one_class_sumSqAdd_six`); the primes $p \mid 8c$ are $2$ and the prime divisors of $c$. -/
@[kb "cassels1978" "Ch. 9, Ex. 5, p. 162 (primitive representations)"]
theorem primRep_sumSqAdd_iff {c : ℤ} (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2 ∨ c = 3 ∨ c = -3) {m : ℤ}
    (hm : m ≠ 0) :
    (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ (sumSqAdd c).eval x = m) ↔
      (0 < c → 0 < m) ∧ ∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ (p : ℤ) ∣ c) →
        ∃ x : Fin 3 → ℤ_[p], (∃ i, IsUnit (x i)) ∧
          ((sumSqAdd c).map (Int.castRingHom ℤ_[p])).eval x = m := by
  have hc0 : c ≠ 0 := by omega
  have hev : ∀ x : Fin 3 → ℤ, (sumSqAdd c).eval x = x 0 ^ 2 + x 1 ^ 2 + c * x 2 ^ 2 := fun x => by
    have h := eval_map_sumSqAdd (R := ℤ) c x
    simpa [QuadForm.map] using h
  constructor
  · rintro ⟨x, hg, hx⟩
    rw [hev] at hx
    refine ⟨fun hcpos => ?_, fun p _ _ => ?_⟩
    · have h1 := sq_nonneg (x 0)
      have h2 := sq_nonneg (x 1)
      have h3 := mul_nonneg hcpos.le (sq_nonneg (x 2))
      omega
    · refine ⟨fun i => (x i : ℤ_[p]), ?_, ?_⟩
      · by_contra hno
        have hall : ∀ i, (p : ℤ) ∣ x i := fun i =>
          (not_not.mp ((isUnit_intCast_padic (p := p) (x i)).not.mp (fun hi => hno ⟨i, hi⟩)))
        have : (p : ℤ) ∣ Finset.univ.gcd x := Finset.dvd_gcd fun i _ => hall i
        rw [hg] at this
        have := Int.le_of_dvd (by norm_num) this
        have := (Fact.out : p.Prime).two_le
        omega
      · rw [eval_map_sumSqAdd]
        have := congrArg (Int.cast : ℤ → ℤ_[p]) hx
        push_cast at this
        exact this
  · rintro ⟨hreal, hloc⟩
    have hf : (sumSqAdd c).hessian.det ≠ 0 := by
      rw [hessian_det_sumSqAdd]; exact mul_ne_zero (by norm_num) hc0
    refine exists_primRep_of_one_class (sumSqAdd c) (by norm_num) hf
      (fun f' h => one_class_sumSqAdd_six hc f' h) hm ?_ ?_
    · by_cases hpos : 0 < m
      · refine ⟨![Real.sqrt m, 0, 0], ?_⟩
        rw [evalIn_real_sumSqAdd]
        simp [Real.sq_sqrt (by exact_mod_cast hpos.le : (0 : ℝ) ≤ m)]
      · have hneg : m < 0 := by omega
        have hcneg : c < 0 := by
          by_contra hcn
          have := hreal (by omega)
          omega
        have hr : (0 : ℝ) ≤ (m : ℝ) / c := by
          have : (m : ℝ) < 0 := by exact_mod_cast hneg
          have : (c : ℝ) < 0 := by exact_mod_cast hcneg
          exact (div_pos_of_neg_of_neg ‹(m : ℝ) < 0› this).le
        refine ⟨![0, 0, Real.sqrt ((m : ℝ) / c)], ?_⟩
        rw [evalIn_real_sumSqAdd]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        rw [Real.sq_sqrt hr]
        have : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
        field_simp
        ring
    · intro p _ hp
      refine hloc p ?_
      rcases hp with h2 | hd | ⟨hn, -⟩
      · exact Or.inl h2
      · rw [hessian_det_sumSqAdd] at hd
        rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd hd with h8 | hcd
        · left
          have h2 : (p : ℤ) ∣ 2 := (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow
            (show (p : ℤ) ∣ 2 ^ 3 by norm_num; exact h8)
          have := Int.le_of_dvd (by norm_num) h2
          have := (Fact.out : p.Prime).two_le
          omega
        · exact Or.inr hcd
      · omega

end QuadFormsKB.Siegel
