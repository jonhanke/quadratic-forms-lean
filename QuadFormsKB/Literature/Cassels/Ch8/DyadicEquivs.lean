import QuadFormsKB.Literature.Cassels.Ch8.Dyadic

/-!
# Cassels, Chapter 8, §4: the equivalences (4.4)–(4.7) and the failure of Witt cancellation over $\mathbb Z_2$

**Setting** (as in `Ch8/Dyadic.lean`): forms over $\mathbb Q_2$ given by symmetric matrices, $\sim$ is
$\mathbb Z_2$-equivalence `ZpEquiv` ($G = T^{t}FT$, $T \in \mathrm{GL}_n(\mathbb Z_2)$). Variables are $x_1, x_2, x_3$ as in
Cassels (matrix indices $0, 1, 2$).

**Source.** The Note after Lemma 4.1 (Cassels, p. 118), read from the page image on 2026-10-30 (the machine-read text
lost the formulas): *it is not asserted that the representation is unique; there are equivalences between sums of
forms (4.1), (4.2), (4.3), exemplified by*
$$x_1^2 + x_2^2 \sim 5x_1^2 + 5x_2^2 \quad (4.4),\qquad x_1^2 + 2x_2^2 \sim 3x_1^2 + 6x_2^2 \quad (4.5),\qquad
x_1^2 + 4x_2^2 \sim 5x_1^2 + 20x_2^2 \quad (4.6),$$
$$ux_1^2 + 2x_2x_3 \sim ux_1^2 + x_2^2 - x_3^2 \quad (\lvert u\rvert = 1) \quad (4.7),$$
$$ux_1^2 + (2x_2^2 + 2x_2x_3 + 2x_3^2) \sim u(3x_1^2 - x_2^2 - x_3^2) \quad (\lvert u\rvert = 1) \quad (4.8),$$
$$(2x_1^2 + 2x_1x_2 + 2x_2^2) + (2x_3^2 + 2x_3x_4 + 2x_4^2) \sim 2x_1x_2 + 2x_3x_4 \quad (4.9).$$
(4.8) and (4.9) are `equiv_4_8`, `equiv_4_9` in `Ch8/Dyadic.lean` (as printed). That file's `equiv_4_7` is the
variant $ux_1^2 + 2x_2x_3 \sim u(x_1^2 + x_2^2 - x_3^2)$; the printed form is `equiv_4_7_printed` here.

**Proves.** `equiv_4_4`, `equiv_4_5`, `equiv_4_6` (explicit integral substitutions of odd determinant),
`equiv_4_7_printed`, and `not_witt_cancellation` (Cassels, p. 120: *the obvious generalization of Witt's Lemma fails
for $p = 2$*, by (4.7)): $\langle u\rangle \perp 2x_2x_3 \sim \langle u\rangle \perp (x_2^2 - x_3^2)$ but
$2x_2x_3 \not\sim x_2^2 - x_3^2$.
-/

namespace QuadFormsKB.Cassels

open Matrix

/-- Helper: an exact substitution $T_0^{t}PT_0 = Q$ by an integer matrix of odd determinant gives a
$\mathbb Z_2$-equivalence. -/
theorem zpEquiv_of_int_exact {n : ℕ} (P Q T0 : Matrix (Fin n) (Fin n) ℤ) (hT : Odd T0.det)
    (h : T0ᵀ * P * T0 = Q) :
    ZpEquiv (P.map (Int.cast : ℤ → ℚ_[2])) (Q.map (Int.cast : ℤ → ℚ_[2])) := by
  have hTu : IsUnit (T0.map (Int.castRingHom ℤ_[2])) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (dyadic_unit_det_map T0 hT)
  refine ⟨hTu.unit, ?_⟩
  have hm : (T0.map (Int.castRingHom ℤ_[2])).map PadicInt.Coe.ringHom = T0.map (Int.cast : ℤ → ℚ_[2]) := by
    ext i j; simp
  rw [IsUnit.unit_spec, hm, ← h]
  change _ = (T0ᵀ * P * T0).map (Int.castRingHom ℚ_[2])
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl

/-- **Cassels, Ch. 8, (4.4)** (p. 118, read from the page image): *$x_1^{2} + x_2^{2} \sim 5x_1^{2} + 5x_2^{2}$* over
$\mathbb Z_2$ (substitution $x_1 = y_1 - 2y_2$, $x_2 = 2y_1 + y_2$). -/
@[kb "cassels1978" "Ch. 8, §4, (4.4), p. 118"]
theorem equiv_4_4 : ZpEquiv (p := 2) !![1, 0; 0, 1] !![5, 0; 0, 5] := by
  have := zpEquiv_of_int_exact (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) !![5, 0; 0, 5] !![1, -2; 2, 1]
    (by simp [Matrix.det_fin_two]; decide) (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply])
  convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- **Cassels, Ch. 8, (4.5)** (p. 118, read from the page image): *$x_1^{2} + 2x_2^{2} \sim 3x_1^{2} + 6x_2^{2}$* over
$\mathbb Z_2$ (substitution $x_1 = y_1 - 2y_2$, $x_2 = y_1 + y_2$). -/
@[kb "cassels1978" "Ch. 8, §4, (4.5), p. 118"]
theorem equiv_4_5 : ZpEquiv (p := 2) !![1, 0; 0, 2] !![3, 0; 0, 6] := by
  have := zpEquiv_of_int_exact (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) !![3, 0; 0, 6] !![1, -2; 1, 1]
    (by simp [Matrix.det_fin_two]; decide) (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply])
  convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- **Cassels, Ch. 8, (4.6)** (p. 118, read from the page image): *$x_1^{2} + 4x_2^{2} \sim 5x_1^{2} + 20x_2^{2}$* over
$\mathbb Z_2$ (substitution $x_1 = y_1 - 4y_2$, $x_2 = y_1 + y_2$). -/
@[kb "cassels1978" "Ch. 8, §4, (4.6), p. 118"]
theorem equiv_4_6 : ZpEquiv (p := 2) !![1, 0; 0, 4] !![5, 0; 0, 20] := by
  have := zpEquiv_of_int_exact (!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℤ) !![5, 0; 0, 20] !![1, -4; 1, 1]
    (by simp [Matrix.det_fin_two]; decide) (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply])
  convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- Helper: $ux_1^{2} + x_2^{2} - x_3^{2} \sim u(x_1^{2} + x_2^{2} - x_3^{2})$ for a $2$-adic unit $u$
(substitution $x_2 = ay_2 + cy_3$, $x_3 = cy_2 + ay_3$ with $a = (1 + u)/2$, $c = a - 1$, so $a^{2} - c^{2} = u$). -/
theorem zpEquiv_unit_hyp {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 1, 0; 0, 0, -1] !![u, 0, 0; 0, u, 0; 0, 0, -u] := by
  obtain ⟨w, -, rfl, hw, -, -⟩ := dyadic_exists_lift hu
  have h2 : (2 : ℤ_[2]) ∣ 1 + w := by
    have hz : PadicInt.toZMod w ≠ 0 := (hw.map PadicInt.toZMod).ne_zero
    have key : ∀ x : ZMod 2, x ≠ 0 → 1 + x = 0 := by decide
    have : PadicInt.toZMod (1 + w) = 0 := by rw [map_add, map_one]; exact key _ hz
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at this
    exact_mod_cast this
  obtain ⟨a, ha⟩ := h2
  set T : Matrix (Fin 3) (Fin 3) ℤ_[2] := !![1, 0, 0; 0, a, a - 1; 0, a - 1, a]
  have hdet : T.det = w := by
    simp [T, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    linear_combination (-1) * ha
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact hw)
  refine ⟨hTu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have hwq : ((w : ℤ_[2]) : ℚ_[2]) = 2 * (a : ℚ_[2]) - 1 := by
    have hw' : w = 2 * a - 1 := by linear_combination ha
    rw [hw']; simp; exact Or.inl rfl
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_succ, hwq] <;> ring

/-- **Cassels, Ch. 8, (4.7)** as printed (p. 118, read from the page image): *$ux_1^{2} + 2x_2x_3 \sim
ux_1^{2} + x_2^{2} - x_3^{2}$* over $\mathbb Z_2$, for a $2$-adic unit $u$ ($\lvert u\rvert = 1$). -/
@[kb "cassels1978" "Ch. 8, §4, (4.7), p. 118"]
theorem equiv_4_7_printed {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 0, 1; 0, 1, 0] !![u, 0, 0; 0, 1, 0; 0, 0, -1] :=
  (equiv_4_7 hu).trans (zpEquiv_unit_hyp hu).symm

/-- $2x_2x_3$ and $x_2^{2} - x_3^{2}$ are not $\mathbb Z_2$-equivalent: the first takes only even values on
$\mathbb Z_2^{2}$, the second takes the value $1$. -/
theorem not_zpEquiv_hyp_diag :
    ¬ ZpEquiv (p := 2) !![0, 1; 1, 0] !![1, 0; 0, -1] := by
  rintro ⟨T, hT⟩
  -- the $(0,0)$ entry of $T^{t}HT$ is $2t_{00}t_{10}$, of absolute value $\le 1/2$, but it equals $1$
  have h00 : ((T.val.map PadicInt.Coe.ringHom)ᵀ * !![(0 : ℚ_[2]), 1; 1, 0] * T.val.map PadicInt.Coe.ringHom) 0 0 =
      2 * ((T.val 0 0 * T.val 1 0 : ℤ_[2]) : ℚ_[2]) := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ]; ring
  rw [hT] at h00
  have hn := congrArg norm h00
  rw [norm_mul, dyadic_norm_two_q] at hn
  have := PadicInt.norm_le_one (T.val 0 0 * T.val 1 0)
  rw [← PadicInt.norm_coe] at this
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, norm_one] at hn
  linarith

/-- **Cassels, Ch. 8, §4** (p. 120): *the obvious generalization of Witt's Lemma fails for $p = 2$*: by (4.7),
$\langle u\rangle \perp 2x_2x_3 \sim \langle u\rangle \perp (x_2^{2} - x_3^{2})$ for every $2$-adic unit $u$, but
$2x_2x_3 \not\sim x_2^{2} - x_3^{2}$ over $\mathbb Z_2$. (Lemma 4.2 gives cancellation under extra hypotheses.) -/
@[kb "cassels1978" "Ch. 8, §4, p. 120 (Witt's Lemma fails for p = 2, by (4.7))"]
theorem not_witt_cancellation {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 0, 1; 0, 1, 0] !![u, 0, 0; 0, 1, 0; 0, 0, -1] ∧
      ¬ ZpEquiv (p := 2) !![0, 1; 1, 0] !![1, 0; 0, -1] :=
  ⟨equiv_4_7_printed hu, not_zpEquiv_hyp_diag⟩

end QuadFormsKB.Cassels
