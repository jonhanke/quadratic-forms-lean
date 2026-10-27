/-
# Classical special cases over $\mathbb Q$: auxiliary facts

**Layer:** $\mathbb Q$. Elementary computations used by the classical specializations: $\rho_{\mathbb Q} = 1$,
$\prod_{p > 2}(1 - p^{-2}) = 8/\pi^2$, fundamental-discriminant facts for `gaussDisc`/`realDisc`, $\beta_\infty$ of
$x_0^2 + x_1^2 + x_2^2$, and the stabilizer of $e_0$ in $\mathrm{SO}(x_0^2 + x_1^2 - x_2^2)$.
(File name: `Aux` is a reserved file name on Windows, so Lean rejects the module `...Classical.Aux`.)
-/
import QuadFormsKB.Tamagawa.Classical.Basic

namespace QuadFormsKB.Tamagawa.Classical

open NumberField Real in
/-- $\rho_{\mathbb Q} = 1$: Mathlib's residue $2^{r_1}(2\pi)^{r_2} h R/(w\sqrt{|d|})$ with $r_1 = 1$, $r_2 = 0$,
$h = R = 1$, $w = 2$, $d = 1$. -/
theorem dedekindZeta_residue_rat : NumberField.dedekindZeta_residue ℚ = 1 := by
  classical
  have hr1 : InfinitePlace.nrRealPlaces ℚ = 1 := by
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := ℚ)
    rw [IsTotallyReal.nrComplexPlaces_eq_zero ℚ, Fintype.card_unique] at this
    omega
  have hreg : Units.regulator ℚ = 1 := by
    have hcard : Fintype.card (InfinitePlace ℚ) = 1 := Fintype.card_unique
    have hs : ∀ a b : InfinitePlace ℚ, a = b := Fintype.card_le_one_iff.mp hcard.le
    have : IsEmpty {w : InfinitePlace ℚ // w ≠ Units.dirichletUnitTheorem.w₀} :=
      ⟨fun ⟨w, hw⟩ => hw (hs _ _)⟩
    rw [Units.regulator_eq_det']
    have h1 : (Matrix.of fun i j : {w : InfinitePlace ℚ // w ≠ Units.dirichletUnitTheorem.w₀} => (0:ℝ)).det = 1 :=
      Matrix.det_isEmpty
    convert abs_one (α := ℝ) using 2
    convert h1 using 2
    all_goals exact Subsingleton.elim _ _
  have htor : Units.torsionOrder ℚ = 2 := by
    apply Units.torsionOrder_eq_two_of_odd_finrank
    simp
  rw [dedekindZeta_residue_def, hr1, IsTotallyReal.nrComplexPlaces_eq_zero ℚ, hreg, Rat.classNumber_eq, htor,
    Rat.numberField_discr]
  simp

/-- $\prod_{p > 2}(1 - p^{-2}) = (6/\pi^2)/(3/4) = 8/\pi^2$, as an unconditional product over the finite places of
$\mathbb Q$ (the factor at $p = 2$ is replaced by $1$). -/
theorem hasProd_one_sub_inv_sq_odd :
    HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
      if Rat.HeightOneSpectrum.natGenerator v = 2 then (1 : ℝ)
      else 1 - 1 / (Rat.HeightOneSpectrum.natGenerator v : ℝ) ^ 2) (8 / Real.pi ^ 2) := by
  classical
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => ((n : ℝ) ^ 2)⁻¹
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by push_cast; rw [mul_pow, mul_inv] }
  have hsum : HasSum (fun n : ℕ => f n) (Real.pi ^ 2 / 6) := by
    simpa [f] using hasSum_zeta_two
  have hnorm : Summable fun n : ℕ => ‖f n‖ := by
    refine hsum.summable.congr fun n => ?_
    simp [f]
  have h1 := EulerProduct.eulerProduct_completely_multiplicative_hasProd hnorm
  rw [hsum.tsum_eq] at h1
  have h2 := h1.inv₀ (div_ne_zero (pow_ne_zero 2 Real.pi_ne_zero) (by norm_num))
  simp only [inv_inv] at h2
  obtain ⟨p2, hp2⟩ : ∃ p2 : Nat.Primes, (p2 : ℕ) = 2 := ⟨⟨2, Nat.prime_two⟩, rfl⟩
  have h3 : HasProd (fun p : Nat.Primes => if p = p2 then (4 / 3 : ℝ) else 1) (4 / 3) :=
    hasProd_ite_eq p2 (4 / 3)
  have h4 := h2.mul h3
  have h5 : HasProd (fun p : Nat.Primes => if (p : ℕ) = 2 then (1 : ℝ) else 1 - 1 / (p : ℝ) ^ 2)
      (8 / Real.pi ^ 2) := by
    convert h4 using 1
    · funext p
      by_cases hp : p = p2
      · subst hp
        simp [f, hp2]
        norm_num
      · have : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext (h.trans hp2.symm))
        simp [f, hp, this]
    · field_simp
      norm_num
  have := (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).hasProd_iff.mpr h5
  exact this

/-! ### The stabilizer of $e_0$ in $\mathrm{SO}(x_0^2 + x_1^2 - x_2^2)$ -/

open Matrix in
/-- **Core of the stabilizer computation** over a characteristic-zero domain: a determinant-one matrix preserving
$x_0^2 + x_1^2 - x_2^2$ and fixing $e_0$ is $1 \oplus \begin{psmallmatrix} a & b \\ b & a\end{psmallmatrix}$ with
$a^2 - b^2 = 1$ ($a = g_{11}$, $b = g_{12}$). -/
theorem stab_core {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (g : Matrix (Fin 3) (Fin 3) R)
    (hdet : g.det = 1)
    (hQ : ∀ x : Fin 3 → R, (g *ᵥ x) 0 ^ 2 + (g *ᵥ x) 1 ^ 2 - (g *ᵥ x) 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2)
    (h0 : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    g 1 1 ^ 2 - g 1 2 ^ 2 = 1 ∧ g = !![1, 0, 0; 0, g 1 1, g 1 2; 0, g 1 2, g 1 1] := by
  have a0 := congrFun h0 0
  have a1 := congrFun h0 1
  have a2 := congrFun h0 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a0 a1 a2
  have e1 := hQ ![0, 1, 0]
  have e2 := hQ ![0, 0, 1]
  have e01 := hQ ![1, 1, 0]
  have e02 := hQ ![1, 0, 1]
  have e12 := hQ ![0, 1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, a0, a1, a2] at e1 e2 e01 e02 e12
  rw [Matrix.det_fin_three] at hdet
  simp [a0, a1, a2] at hdet
  have h01 : g 0 1 = 0 := by
    have : 2 * g 0 1 = 0 := by linear_combination e01 - e1
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have h02 : g 0 2 = 0 := by
    have : 2 * g 0 2 = 0 := by linear_combination e02 - e2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  rw [h01] at e1 e12
  rw [h02] at e2 e12
  have hE3 : g 1 1 * g 1 2 - g 2 1 * g 2 2 = 0 := by
    have : 2 * (g 1 1 * g 1 2 - g 2 1 * g 2 2) = 0 := by linear_combination e12 - e1 - e2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have e1' : g 1 1 ^ 2 - g 2 1 ^ 2 = 1 := by linear_combination e1
  have hc : g 2 1 = g 1 2 := by
    linear_combination (-(g 1 1)) * hE3 - (g 2 1) * hdet + (g 1 2) * e1'
  have hd : g 2 2 = g 1 1 := by
    linear_combination (g 1 1) * hdet + (g 2 1) * hE3 - (g 2 2) * e1'
  refine ⟨by rw [← hc]; exact e1', ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, h01, h02, hc, hd]

/-- $Q(\vec x) = x_0^2 + x_1^2 - x_2^2$ for `qInd` over any commutative ring. -/
theorem qInd_evalIn {K : Type*} [CommRing K] (x : Fin 3 → K) :
    (qInd.map (Int.castRingHom K)).eval x = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map, qInd, QuadForm.diag, Fin.sum_univ_three,
    Matrix.diagonal_apply]
  ring

theorem qInd_eval_int (x : Fin 3 → ℤ) : qInd.eval x = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, qInd, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal_apply]
  ring

open Matrix in
/-- **Real stabilizer of $e_0$** for $x_0^2 + x_1^2 - x_2^2$: $g = 1 \oplus \begin{psmallmatrix} a & b \\ b & a
\end{psmallmatrix}$ with $a^2 - b^2 = 1$. -/
theorem stab_e0_qInd_real (g : Matrix (Fin 3) (Fin 3) ℝ) (hdet : g.det = 1)
    (hg : ∀ x : Fin 3 → ℝ, (qInd.map (Int.castRingHom ℝ)).eval (g *ᵥ x) = (qInd.map (Int.castRingHom ℝ)).eval x)
    (h0 : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    ∃ a b : ℝ, a ^ 2 - b ^ 2 = 1 ∧ g = !![1, 0, 0; 0, a, b; 0, b, a] := by
  obtain ⟨h1, h2⟩ := stab_core g hdet (fun x => by simpa [qInd_evalIn] using hg x) h0
  exact ⟨_, _, h1, h2⟩

open Matrix in
/-- Its eigenvalue on the isotropic vector $(0, 1, 1)$ is $a + b$. -/
theorem stab_e0_qInd_eigen (a b : ℝ) :
    !![(1 : ℝ), 0, 0; 0, a, b; 0, b, a] *ᵥ ![0, 1, 1] = (a + b) • ![0, 1, 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_comm]

/-- **Norm-one part:** $|a + b| = 1$ and $a^2 - b^2 = 1$ force $b = 0$, $a = \pm 1$. -/
theorem stab_e0_qInd_normOne {a b : ℝ} (h : a ^ 2 - b ^ 2 = 1) (h1 : |a + b| = 1) :
    b = 0 ∧ (a = 1 ∨ a = -1) := by
  have hm : (a + b) * (a - b) = 1 := by linear_combination h
  rcases (abs_eq zero_le_one).mp h1 with h2 | h2
  · rw [h2] at hm
    refine ⟨by linarith, Or.inl (by linarith)⟩
  · rw [h2] at hm
    refine ⟨by linarith, Or.inr (by linarith)⟩

open Matrix in
/-- **Integral stabilizer of $e_0$** in $\mathrm{SO}(x_0^2 + x_1^2 - x_2^2)(\mathbb Z)$ is
$\{1, \mathrm{diag}(1, -1, -1)\}$. -/
theorem stab_e0_qInd_int (g : Matrix (Fin 3) (Fin 3) ℤ) (hdet : g.det = 1)
    (hg : ∀ x : Fin 3 → ℤ, qInd.eval (g *ᵥ x) = qInd.eval x) (h0 : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    g = 1 ∨ g = Matrix.diagonal ![1, -1, -1] := by
  obtain ⟨h1, h2⟩ := stab_core g hdet (fun x => by simpa [qInd_eval_int] using hg x) h0
  have hm : (g 1 1 - g 1 2) * (g 1 1 + g 1 2) = 1 := by linear_combination h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hm with ⟨u, v⟩ | ⟨u, v⟩
  · left
    have ha : g 1 1 = 1 := by linarith
    have hb : g 1 2 = 0 := by linarith
    rw [h2, ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    have ha : g 1 1 = -1 := by linarith
    have hb : g 1 2 = 0 := by linarith
    rw [h2, ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- $\beta_\infty$ of $x_0^2 + x_1^2 + x_2^2$: $\tfrac32\,\omega_3\sqrt m = 2\pi\sqrt m$. -/
theorem betaInf_sumSq_three {m : ℝ} (_hm : 0 ≤ m) :
    Siegel.betaInf (Siegel.sumSq 3) m = 2 * Real.pi * Real.sqrt m := by
  have hG : Siegel.gramDet (Siegel.sumSq 3) = 1 := by
    rw [Siegel.gramDet, Siegel.hessian_sumSq, Matrix.det_smul]
    simp
    norm_num
  have hΓ : Real.Gamma ((3 : ℕ) / 2 + 1 : ℝ) = 3 / 4 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num)]
    rw [show ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [Siegel.betaInf, hG, Real.one_rpow, Siegel.unitBallVol_eq (by norm_num), hΓ]
  rw [show (((3 : ℕ) : ℝ) - 2) / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt Real.pi ^ 3 = Real.sqrt Real.pi * Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]; ring
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hs]
  push_cast
  field_simp
  norm_num

theorem squarefree_neg_of {m : ℤ} (hsf : Squarefree m) : Squarefree (-m) :=
  Int.squarefree_natAbs.mp (by simpa using Int.squarefree_natAbs.mpr hsf)

/-- A squarefree integer is not divisible by $4$. -/
theorem not_four_dvd_of_squarefree {m : ℤ} (hsf : Squarefree m) : ¬ (4 : ℤ) ∣ m := by
  intro h
  have h' : (2 * 2 : ℤ) ∣ m := by simpa using h
  exact absurd (Int.isUnit_iff.mp (hsf 2 h')) (by norm_num)

/-- $D_{\mathbb Q(\sqrt{-m})}$ is a quadratic-field discriminant for squarefree $m \ge 1$. -/
theorem isQuadDisc_gaussDisc {m : ℤ} (hm : 1 ≤ m) (hsf : Squarefree m) :
    Binary.IsQuadDisc (gaussDisc m) := by
  have h4 := not_four_dvd_of_squarefree hsf
  unfold gaussDisc
  split_ifs with h
  · exact ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by omega, (squarefree_neg_of hsf)⟩), by omega⟩
  · have e : -4 * m / 4 = -m := by omega
    exact ⟨Int.isFundamentalDiscr_iff_squarefree.mpr
      (Or.inr ⟨by omega, by rw [e]; exact (squarefree_neg_of hsf), by omega⟩), by omega⟩

/-- $D_{\mathbb Q(\sqrt m)}$ is a quadratic-field discriminant for squarefree $m \ne 1$. -/
theorem isQuadDisc_realDisc {m : ℤ} (hsf : Squarefree m) (hm1 : m ≠ 1) :
    Binary.IsQuadDisc (realDisc m) := by
  have h4 := not_four_dvd_of_squarefree hsf
  unfold realDisc
  split_ifs with h
  · exact ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hsf⟩), hm1⟩
  · have e : 4 * m / 4 = m := by omega
    exact ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inr ⟨by omega, by rwa [e], by omega⟩), by omega⟩

end QuadFormsKB.Tamagawa.Classical
