/-
# Watson (1963): the probes as orthogonal sums over $\mathbb Z_2$

For each perfect form used in Watson's §8 (the root lattices $A_5, D_5, D_6, E_7, D_9$ in Watson's coordinates,
`Probes.lean`) and for $\Phi_4 = D_4$, an integral square matrix $T$ of **odd** determinant with
$\varphi \circ T = Y \perp S$, where $Y$ is a form `phiA k` (whose Hessian determinant $k + 1$ is odd) and $S$ is a
small diagonal (or scaled) form. As $T$ is invertible over $\mathbb Z_2$, this says that over $\mathbb Z_2$ the
probe is isometric to $Y \perp S$, with $Y$ even unimodular. All identities are finite computations
(`decide +kernel`, coefficientwise).

* $A_5 \cong A_4 \perp \langle 15\rangle$ (index $5$);
* $D_5 \cong A_4 \perp \langle 10\rangle$ (index $5$);
* $D_6 \cong A_4 \perp \langle 3, 15\rangle$ and $D_6 \cong A_4 \perp \langle 15, 3\rangle$ (index $15$);
* $E_7 \cong A_6 \perp \langle 7\rangle$ (index $7$);
* $D_9 \cong A_8 \perp \langle 18\rangle$ (index $9$);
* $D_4 \cong A_2 \perp 2A_2$ (index $3$).

(The matrices were found by a short computer search; the Lean proofs only check them.)
-/
import QuadFormsKB.Literature.Watson1963.Probes
import QuadFormsKB.Literature.Watson1963.TwoAdic

open Matrix

namespace QuadFormsKB.Watson1963

/-- Helper: if $T A = d \cdot 1$ for integral matrices and $d$ is odd, then $\det T$ is odd. -/
theorem odd_det_of_mul_eq_smul {n : ℕ} (T A : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (hd : Odd d)
    (h : T * A = d • (1 : Matrix (Fin n) (Fin n) ℤ)) : Odd T.det := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at e
  have : Odd (T.det * A.det) := e ▸ hd.pow
  exact (Int.odd_mul.mp this).1

/-- **$A_5$ over $\mathbb Z_2$:** $A_5 \circ T = A_4 \perp \langle c\rangle$ with $\det T$ odd and $c$ odd
($c = 15$, $\det T = -5$). -/
theorem phiA5_decomp : ∃ (T : Matrix (Fin 5) (Fin 5) ℤ) (c : ℤ), Odd T.det ∧ Odd c ∧
    (phiA 5).compMat T = QuadForm.orthSum (phiA 4) (QuadForm.diag ![c]) := by
  refine ⟨!![-1, -1, -1, -1, -1; 0, 0, 0, 1, -1; 0, 0, 1, 0, -1; 0, 1, 0, 0, -1; 1, 0, 0, 0, -1], 15,
    (odd_det_of_mul_eq_smul _ !![1, 1, 1, 1, -4; 1, 1, 1, -4, 1; 1, 1, -4, 1, 1; 1, -4, 1, 1, 1; 1, 1, 1, 1, 1] (-5) ⟨-3, by decide⟩ (by decide +kernel)), ⟨7, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$D_5$ over $\mathbb Z_2$:** $\Phi_5 \circ T = A_4 \perp \langle 2u\rangle$ with $\det T$ odd and $u$ odd
($u = 5$, $\det T = -5$). -/
theorem phiD4_decomp : ∃ (T : Matrix (Fin 5) (Fin 5) ℤ) (u : ℤ), Odd T.det ∧ Odd u ∧
    (phiD 4).compMat T = QuadForm.orthSum (phiA 4) (QuadForm.diag ![2 * u]) := by
  refine ⟨!![-1, -1, -1, -1, -2; -1, 0, 0, 0, 2; 0, -1, 0, 0, 2; 0, 0, -1, 0, 2; 1, 1, 1, 0, -1], 5,
    (odd_det_of_mul_eq_smul _ !![0, 3, -2, -2, -2; 0, -2, 3, -2, -2; 0, -2, -2, 3, -2; 5, 3, 3, 3, 8; 0, -1, -1, -1, -1] (-5) ⟨-3, by decide⟩ (by decide +kernel)), ⟨2, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$D_6$ over $\mathbb Z_2$, first version:** $\Phi_6 \circ T = A_4 \perp \langle a, c\rangle$ with $\det T$ odd,
$a \equiv 3 \pmod 8$, $c$ odd ($a = 3$, $c = 15$, $\det T = -15$). -/
theorem phiD5_decomp3 : ∃ (T : Matrix (Fin 6) (Fin 6) ℤ) (a c : ℤ), Odd T.det ∧ a % 8 = 3 ∧ Odd c ∧
    (phiD 5).compMat T = QuadForm.orthSum (phiA 4) (QuadForm.diag ![a, c]) := by
  refine ⟨!![-1, -1, -1, -1, -1, -1; -1, 0, 0, 0, 1, 1; 0, -1, 0, 0, 1, 1; 0, 0, -1, 0, 1, 1;
    0, 0, 0, -1, 1, 1; 1, 1, 1, 1, -2, 1], 3, 15, (odd_det_of_mul_eq_smul _ !![3, 12, -3, -3, -3, 0; 3, -3, 12, -3, -3, 0; 3, -3, -3, 12, -3, 0; 3, -3, -3, -3, 12, 0; 5, 0, 0, 0, 0, 5; -2, -3, -3, -3, -3, -5] (-15) ⟨-8, by decide⟩ (by decide +kernel)), by decide, ⟨7, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$D_6$ over $\mathbb Z_2$, second version:** $\Phi_6 \circ T = A_4 \perp \langle a, c\rangle$ with $\det T$
odd, $a \equiv 7 \pmod 8$, $c$ odd ($a = 15$, $c = 3$, $\det T = 15$). -/
theorem phiD5_decomp7 : ∃ (T : Matrix (Fin 6) (Fin 6) ℤ) (a c : ℤ), Odd T.det ∧ a % 8 = 7 ∧ Odd c ∧
    (phiD 5).compMat T = QuadForm.orthSum (phiA 4) (QuadForm.diag ![a, c]) := by
  refine ⟨!![-1, -1, -1, -1, -1, -1; -1, 0, 0, 0, 1, 1; 0, -1, 0, 0, 1, 1; 0, 0, -1, 0, 1, 1;
    0, 0, 0, -1, 1, 1; 1, 1, 1, 1, 1, -2], 15, 3, (odd_det_of_mul_eq_smul _ !![-3, -12, 3, 3, 3, 0; -3, 3, -12, 3, 3, 0; -3, 3, 3, -12, 3, 0; -3, 3, 3, 3, -12, 0; 2, 3, 3, 3, 3, 5; -5, 0, 0, 0, 0, -5] 15 ⟨7, by decide⟩ (by decide +kernel)), by decide, ⟨1, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$E_7$ over $\mathbb Z_2$:** $E_7 \circ T = A_6 \perp \langle c\rangle$ with $\det T$ odd and $c$ odd
($c = 7$, $\det T = -7$). -/
theorem formE7_decomp : ∃ (T : Matrix (Fin 7) (Fin 7) ℤ) (c : ℤ), Odd T.det ∧ Odd c ∧
    formE7.compMat T = QuadForm.orthSum (phiA 6) (QuadForm.diag ![c]) := by
  refine ⟨!![-1, -1, -1, -1, -1, 0, -1; -1, -1, 0, 0, 0, 0, 1; -1, 0, -1, 0, 0, 0, 1; 0, -1, -1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 1, 0, 1, -1; 1, 1, 1, 0, 0, -1, -1], 7,
    (odd_det_of_mul_eq_smul _ !![1, 4, 4, -3, 1, 1, 2; 1, 4, -3, 4, 1, 1, 2; 1, -3, 4, 4, 1, 1, 2; 1, -3, -3, -3, 1, -6, -5; 1, -3, -3, -3, -6, 1, -5; 1, 4, 4, 4, 1, 1, 9; 2, 1, 1, 1, 2, 2, 4] (-7) ⟨-4, by decide⟩ (by decide +kernel)), ⟨3, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$D_9$ over $\mathbb Z_2$:** $\Phi_9 \circ T = A_8 \perp \langle 2u\rangle$ with $\det T$ odd and $u$ odd
($T$ fixes $e_0, \dots, e_7$ and sends $e_8$ to $(2, \dots, 2, -9)$; $u = 9$, $\det T = -9$). -/
theorem phiD8_decomp : ∃ (T : Matrix (Fin 9) (Fin 9) ℤ) (u : ℤ), Odd T.det ∧ Odd u ∧
    (phiD 8).compMat T = QuadForm.orthSum (phiA 8) (QuadForm.diag ![2 * u]) := by
  refine ⟨!![1, 0, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 1, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 0, 0, 0, -9], 9, (odd_det_of_mul_eq_smul _ !![-9, 0, 0, 0, 0, 0, 0, 0, -2; 0, -9, 0, 0, 0, 0, 0, 0, -2; 0, 0, -9, 0, 0, 0, 0, 0, -2; 0, 0, 0, -9, 0, 0, 0, 0, -2; 0, 0, 0, 0, -9, 0, 0, 0, -2; 0, 0, 0, 0, 0, -9, 0, 0, -2; 0, 0, 0, 0, 0, 0, -9, 0, -2; 0, 0, 0, 0, 0, 0, 0, -9, -2; 0, 0, 0, 0, 0, 0, 0, 0, 1] (-9) ⟨-5, by decide⟩ (by decide +kernel)), ⟨4, by decide⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$D_4$ over $\mathbb Z_2$:** $\Phi_4 \circ T = A_2 \perp 2A_2$ (`phiA 2` and $2\cdot$`quadA`, both $A_2$) with
$\det T$ odd ($\det T = -3$). -/
theorem phiD3_decomp : ∃ T : Matrix (Fin 4) (Fin 4) ℤ, Odd T.det ∧
    (phiD 3).compMat T = QuadForm.orthSum (phiA 2) ((2 : ℤ) • (quadA : QuadForm ℤ 2)) := by
  refine ⟨!![-1, -1, -1, -1; -1, 0, 1, 1; 0, -1, 1, 1; 1, 1, -1, 0], (odd_det_of_mul_eq_smul _ !![1, 2, -1, 0; 1, -1, 2, 0; 2, 1, 1, 3; -1, -2, -2, -3] (-3) ⟨-2, by decide⟩ (by decide +kernel)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

end QuadFormsKB.Watson1963
