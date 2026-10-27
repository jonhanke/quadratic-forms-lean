/-
# O'Meara §106 introduction: a positive definite space with a unimodular $\mathbb Z$-lattice is $I_n$

**Layer:** integral forms `QuadForm ℤ n` (a $\mathbb Z$-lattice with a chosen base) and their rational spaces
`Q.map (Int.castRingHom ℚ)`; rational isometry `QuadForm.IsometricIn ℚ`; the sum of squares `QuadForm.diag (fun _ => 1)`.

O'Meara's unimodular lattice $L$ has an integral symmetric matrix $G = (B(x_i, x_j))$ with $\det G = \pm 1$, and
$Q(x) = B(x, x)$; as a form, $Q$ is classically integral (`IsClassicallyIntegral`) with Hessian $H_Q = 2G$, so
$\det H_Q = \pm 2^n$.

*Generalization.* O'Meara's matrix $G = \tfrac12H_Q$ is integral (the form is classically integral); the proof
uses only $\det H_Q = \pm 2^n$ and positive definiteness, so classical integrality is not assumed.

**Proves** the opening claim of §106 (O'Meara 1973, pp. 323–324, item 106.r1, `omeara106_r1`): if $V$ is positive
definite and carries a unimodular lattice, then $V \cong I_n = \langle 1, \dots, 1\rangle$ over $\mathbb Q$.
O'Meara's argument: $dV = 1$ (a positive definite unimodular matrix has determinant $1$); $S_pV = 1$ for odd $p$ (a
unimodular lattice over $\mathbb Z_p$ is diagonal with unit entries); $S_\infty V = 1$; hence $S_2V = 1$ by Hilbert
reciprocity, and $V \cong I_n$ by Theorem 63:20 and the Hasse–Minkowski Theorem.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Defs.Integral
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.LocalDensity.JordanForm

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

private lemma map_evalIn_aux {n : ℕ} (Q : QuadForm ℤ n) (x : Fin n → ℚ) :
    (Q.map (Int.castRingHom ℚ)).evalIn ℚ x = Q.evalIn ℚ x := by
  simp [QuadForm.evalIn, QuadForm.map]

private lemma map_hessian_aux {n : ℕ} (Q : QuadForm ℤ n) :
    (Q.map (Int.castRingHom ℚ)).hessian = Q.hessian.map (Int.castRingHom ℚ) := by
  simp [QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map]

private lemma eval_cast_aux {n : ℕ} (Q : QuadForm ℤ n) (z : Fin n → ℤ) :
    (Q.map (Int.castRingHom ℚ)).evalIn ℚ (fun j => (z j : ℚ)) = ((Q.eval z : ℤ) : ℚ) := by
  rw [map_evalIn_aux]
  simp [QuadForm.eval, QuadForm.evalIn]

private lemma two_mul_evalIn_aux {n : ℕ} (R : QuadForm ℚ n) (y : Fin n → ℚ) :
    2 * R.evalIn ℚ y = y ⬝ᵥ (R.hessian *ᵥ y) := by
  have h := QuadForm.polar_eq_hessian ℚ R y y
  have e : R.hessian.map (algebraMap ℚ ℚ) = R.hessian := by ext; simp
  rw [e] at h
  have h2 : y + y = (2 : ℚ) • y := by rw [two_smul]
  rw [h2, QuadForm.evalIn_smul] at h
  linarith

private lemma exists_diag_rat_aux {n : ℕ} (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    ∃ a : Fin n → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) ∧
      (Q.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag fun i => (a i : ℚ)) := by
  have hpp : (p : ℕ).Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hpv : ∀ a : ℤ, a ≠ 0 → ∃ v : ℕ, ∃ w, a = (p : ℤ) ^ v * w ∧ ¬ (p : ℤ) ∣ w := by
    intro a ha
    obtain ⟨w, hw⟩ := padicValInt_dvd (p := p) a
    refine ⟨padicValInt p a, w, hw, ?_⟩
    rintro ⟨w', rfl⟩
    have h1 : (p : ℤ) ^ (padicValInt p a + 1) ∣ a := ⟨w', hw.trans (by ring)⟩
    rcases (padicValInt_dvd_iff (p := p) (padicValInt p a + 1) a).1 h1 with h | h
    · exact ha h
    · omega
  obtain ⟨U, hU, D, hD⟩ := LocalDensity.exists_conj_diagonal_aux hpZ hp2 hpv _ Q.hessian
    Finset.univ rfl (LocalDensity.hessian_isSymm Q) (fun k l _ h => by simp at h)
  have hval : ∀ x : Fin n → ℤ, 2 * Q.eval (U *ᵥ x) = ∑ i, D i * x i * x i := by
    intro x
    have hc : (U *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ * Q.hessian * U) *ᵥ x) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Uᵀ, vecMul_transpose]
    rw [LocalDensity.two_mul_eval_eq_hessian, hc, hD]
    simp [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  set a : Fin n → ℤ := fun i => Q.eval (U *ᵥ Pi.single i 1) with ha
  have hDa : ∀ i, D i = 2 * a i := by
    intro i
    rw [ha]; dsimp only
    rw [hval]
    simp [Pi.single_apply]
  have hdetD : (Uᵀ * Q.hessian * U).det = U.det * Q.hessian.det * U.det := by
    rw [det_mul, det_mul, det_transpose]
  rw [hD, det_diagonal] at hdetD
  have hnd : ∀ i, ¬ (p : ℤ) ∣ a i := by
    intro i hai
    have hdvd : (p : ℤ) ∣ ∏ i, D i :=
      (hai.mul_left 2).trans ((hDa i).symm ▸ Finset.dvd_prod_of_mem D (Finset.mem_univ i))
    rw [hdetD] at hdvd
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact hU h
      · exact hdet h
    · exact hU h
  refine ⟨a, hnd, U.map (Int.castRingHom ℚ), ?_, fun x => ?_⟩
  · have h1 : (U.map (Int.castRingHom ℚ)).det = (U.det : ℚ) := by
      have := (Int.castRingHom ℚ).map_det U
      simpa using this.symm
    rw [h1]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr fun h => hU (h ▸ dvd_zero _))
  · set Uq := U.map (Int.castRingHom ℚ) with hUq
    set R := Q.map (Int.castRingHom ℚ) with hR
    have hH : R.hessian = Q.hessian.map (Int.castRingHom ℚ) := map_hessian_aux Q
    have hDq : Uqᵀ * R.hessian * Uq = diagonal (fun i => (D i : ℚ)) := by
      have := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map (Int.castRingHom ℚ)) hD
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      rw [hH, hUq]
      rw [this]
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have h2 : 2 * R.evalIn ℚ (Uq *ᵥ x) =
        2 * (QuadForm.diag fun i => (a i : ℚ)).evalIn ℚ x := by
      rw [two_mul_evalIn_aux]
      have hc : (Uq *ᵥ x) ⬝ᵥ (R.hessian *ᵥ (Uq *ᵥ x)) = x ⬝ᵥ ((Uqᵀ * R.hessian * Uq) *ᵥ x) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Uqᵀ, vecMul_transpose]
      rw [hc, hDq, QuadForm.evalIn_diag, Finset.mul_sum]
      simp only [dotProduct, mulVec_diagonal]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hDa i]
      simp
      ring
    exact mul_left_cancel₀ two_ne_zero h2

private lemma hilbert_real_pos_aux (x y : ℝ) (hx : 0 < x) : hilbertSymbol ℝ x y = 1 := by
  have h : ∃ a b c : ℝ, (a, b, c) ≠ 0 ∧ c ^ 2 = x * a ^ 2 + y * b ^ 2 :=
    ⟨1, 0, Real.sqrt x, by simp, by rw [Real.sq_sqrt hx.le]; ring⟩
  unfold hilbertSymbol
  split_ifs with hc
  · rfl
  · exact absurd h hc

/-- **§106, the space of a definite unimodular lattice** (O'Meara 1973, pp. 323–324): a positive definite form $Q$ over $\mathbb Z$ in $n$ variables whose matrix $G = \tfrac12 H_Q$ has determinant $\pm 1$
($\det H_Q = \pm 2^n$) is equivalent over $\mathbb Q$ to the sum of $n$ squares. -/
@[kb "omeara1963" "§106, pp. 323–324 (V ≅ I_n for a positive definite V with a unimodular lattice)"]
theorem omeara106_r1 {n : ℕ} (Q : QuadForm ℤ n)
    (hpos : ∀ x : Fin n → ℤ, x ≠ 0 → 0 < Q.eval x)
    (hdet : Q.hessian.det = 2 ^ n ∨ Q.hessian.det = -2 ^ n) :
    (Q.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag fun _ => 1) := by
  classical
  set R : QuadForm ℚ n := Q.map (Int.castRingHom ℚ) with hR
  have hHR : R.hessian = Q.hessian.map (Int.castRingHom ℚ) := map_hessian_aux Q
  have hdetR : R.hessian.det = (Q.hessian.det : ℚ) := by
    rw [hHR]
    have := (Int.castRingHom ℚ).map_det Q.hessian
    simpa using this.symm
  have hdetQ : (Q.hessian.det : ℚ) = 2 ^ n ∨ (Q.hessian.det : ℚ) = -2 ^ n := by
    rcases hdet with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hRnd : R.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hdetR]
    rcases hdetQ with h | h <;> rw [h] <;> simp
  obtain ⟨b, hb, hRb⟩ := FieldGen.exists_isometric_diag R hRnd
  obtain ⟨P, hPu, hP⟩ := hRb
  have hRb' : R.IsometricIn ℚ (QuadForm.diag b) := ⟨P, hPu, hP⟩
  -- the diagonal entries are positive
  have hbpos : ∀ i, 0 < b i := by
    intro i
    set v : Fin n → ℚ := P *ᵥ Pi.single i 1 with hv
    have hRv : R.evalIn ℚ v = b i := by
      rw [hv, hP, QuadForm.evalIn_diag]
      simp [Pi.single_apply]
    have hdex : ∃ d : ℕ, 0 < d ∧ ∀ j, ∃ z : ℤ, (z : ℚ) = d * v j := by
      refine ⟨∏ j, (v j).den, Finset.prod_pos fun j _ => (v j).den_pos, fun j => ?_⟩
      obtain ⟨k, hk⟩ : (v j).den ∣ ∏ j, (v j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      refine ⟨(v j).num * k, ?_⟩
      have h1 : ((v j).num : ℚ) = v j * (v j).den := (Rat.mul_den_eq_num _).symm
      have h2 : ((∏ j, (v j).den : ℕ) : ℚ) = ((v j).den : ℚ) * k := by exact_mod_cast hk
      push_cast at h2 ⊢
      rw [h2, h1]
      ring
    obtain ⟨d, hdpos, hz⟩ := hdex
    choose z hz using hz
    have hscale : R.evalIn ℚ (fun j => (z j : ℚ)) = (d : ℚ) ^ 2 * b i := by
      have : (fun j => (z j : ℚ)) = (d : ℚ) • v := funext fun j => by simp [hz]
      rw [this, QuadForm.evalIn_smul, hRv]
    rw [hR, eval_cast_aux] at hscale
    have hd2 : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hscale
      have : b i = 0 := by
        have h' : (d : ℚ) ^ 2 * b i = 0 := by
          rw [← hscale]; simp [QuadForm.eval, QuadForm.evalIn]
        exact (mul_eq_zero.mp h').resolve_left hd2.ne'
      exact hb i this
    have hq : (0 : ℚ) < ((Q.eval z : ℤ) : ℚ) := by exact_mod_cast hpos z hz0
    rw [hscale] at hq
    exact (mul_pos_iff_of_pos_left hd2).mp hq
  -- discriminant
  have hprodpos : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hbpos i
  have hdiagdet : (QuadForm.diag b).hessian.det = 2 ^ n * ∏ i, b i := by
    simp only [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add,
      Matrix.det_diagonal]
    simp [← two_mul, Finset.prod_mul_distrib]
  have e := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hP)
  rw [det_mul, det_mul, det_transpose, hdetR, hdiagdet] at e
  have hPd : P.det ≠ 0 := hPu.ne_zero
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  have hdp : 0 < P.det ^ 2 := by positivity
  have hdetpos : (Q.hessian.det : ℚ) = 2 ^ n := by
    rcases hdetQ with h | h
    · exact h
    · exfalso
      rw [h] at e
      nlinarith [mul_pos h2n hprodpos, mul_pos h2n hdp]
  have hprod : ∏ i, b i = P.det ^ 2 := by
    rw [hdetpos] at e
    apply mul_left_cancel₀ h2n.ne'
    rw [← e]; ring
  have hdetZ : Q.hessian.det = 2 ^ n := by exact_mod_cast hdetpos
  -- the Hasse invariants
  have hne2 : ∀ v : RatPlace, v ≠ RatPlace.finite ⟨2, Nat.prime_two⟩ → v.hasseSerre b = 1 := by
    intro v hv
    cases v with
    | infinite =>
      rw [RatPlace.hasseSerre_infinite]
      unfold hasseInvariant
      refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
      split_ifs
      · exact hilbert_real_pos_aux _ _ (by simpa using hbpos i)
      · rfl
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      have hp2 : p.1 ≠ 2 := fun h => hv (congrArg RatPlace.finite (Subtype.ext h))
      have hnd : ¬ (p.1 : ℤ) ∣ Q.hessian.det := by
        rw [hdetZ]
        intro h
        have h' := (Nat.prime_iff_prime_int.mp p.2).dvd_of_dvd_pow h
        have : p.1 ∣ 2 := by exact_mod_cast h'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp this)
      obtain ⟨a, ha, hRa⟩ := exists_diag_rat_aux Q p.1 hp2 hnd
      have ha0 : ∀ i, (a i : ℚ) ≠ 0 := fun i h =>
        ha i (by have : a i = 0 := by exact_mod_cast h
                 rw [this]; exact dvd_zero _)
      have hba : (QuadForm.diag b).IsometricIn ℚ (QuadForm.diag fun i => (a i : ℚ)) :=
        QuadForm.isometricIn_trans ℚ (QuadForm.isometricIn_symm ℚ hRb') hRa
      have hinv := hasseInvariant_isometric p.1 b (fun i => (a i : ℚ)) hb ha0
        (FieldGen.isometricIn_of_base ℚ_[p.1] hba)
      rw [RatPlace.hasseSerre_finite, hinv, ← RatPlace.hasseSerre_finite]
      unfold RatPlace.hasseSerre
      refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
      split_ifs
      · have := ConwaySloane.hilbert_odd_int p.1 hp2 0 0 (a i) (a j) (a i : ℚ) (a j : ℚ) (ha i) (ha j)
          (by simp) (by simp)
        simp only [mul_zero, zero_mul, pow_zero, mul_one] at this
        exact this
      · rfl
  have hall : ∀ v : RatPlace, v.hasseSerre b = 1 := by
    intro v
    by_cases hv : v = RatPlace.finite ⟨2, Nat.prime_two⟩
    · have h := (hasseSerre_product_formula b hb).2
      rw [finprod_eq_single _ _ hne2] at h
      rw [hv]; exact h
    · exact hne2 v hv
  have hbd : (QuadForm.diag b).IsometricIn ℚ (QuadForm.diag fun _ : Fin n => (1 : ℚ)) := by
    rw [isometric_iff_everywhere _ _ (QuadForm.nondegenerate_diag hb)
      (QuadForm.nondegenerate_diag (fun _ => one_ne_zero))]
    intro v
    cases v with
    | infinite =>
      show (QuadForm.diag b).IsometricIn ℝ (QuadForm.diag fun _ : Fin n => (1 : ℚ))
      have hbr : ∀ i, (0 : ℝ) < (b i : ℝ) := fun i => by exact_mod_cast hbpos i
      refine ⟨Matrix.diagonal fun i => (Real.sqrt (b i : ℝ))⁻¹, ?_, fun x => ?_⟩
      · rw [Matrix.det_diagonal]
        refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
        exact inv_ne_zero (Real.sqrt_pos.mpr (hbr i)).ne'
      · rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_diagonal]
        have hs : Real.sqrt (b i : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (hbr i)).ne'
        have hsq := Real.sq_sqrt (hbr i).le
        simp only [map_one, one_mul]
        rw [mul_pow, inv_pow, hsq]
        have hbi : (b i : ℝ) ≠ 0 := (hbr i).ne'
        simp
        field_simp
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      show (QuadForm.diag b).IsometricIn ℚ_[p.1] (QuadForm.diag fun _ : Fin n => (1 : ℚ))
      rw [isometric_padic_iff p.1 b _ hb (fun _ => one_ne_zero)]
      refine ⟨⟨algebraMap ℚ ℚ_[p.1] P.det, (map_ne_zero _).mpr hPd, ?_⟩, ?_⟩
      · rw [hprod]; simp
      · have h1 := hall (RatPlace.finite p)
        rw [RatPlace.hasseSerre_finite] at h1
        rw [h1]
        symm
        simp [hasseInvariant, PadicClass.hs_one_left]
  exact QuadForm.isometricIn_trans ℚ hRb' hbd

end QuadFormsKB.Lattices
