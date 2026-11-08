/-
# Watson (1963), Lemma 14 at $q = 2$: $\Phi_4$ splits off over $\mathbb Z_2$

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §9, Lemma 14 with
Lemmas 1, 9 ($g(4, 4) = \Phi_4 = D_4$), pp. 560, 565. **This proves the named input `WatsonPhi4SplitTwo`**
(`watsonPhi4SplitTwo_holds`).

Let $f$ be Watson-minimal positive definite in $n = 4 + m$ variables, $m \ge 8$, with $r_2(f) \le 9$, and
$F = U \perp \psi$ its shape over $\mathbb Z_2$ (`exists_decomp_two`). Then $6 \le 2k \le 8$ (minimality gives
$r_2 \ge n/2 \ge 6$), so $\psi$ has at least $4$ variables and contains $2A$ ((ψ3), `psi_exists_anisotropic_pair`).
Over $\mathbb Z_2$, $\Phi_4 \cong A_2 \perp 2A_2$ (`phiD3_decomp`). The sublattice spanned by a copy of $A_2$ in $U$
and the copy of $2A_2$ in $\psi$ is an orthogonal summand of $F$: its orthogonal projection is integral, since the
pairing of $2A_2 \subseteq \psi$ with every vector of $F$ is even (`exists_complement_of_left_inverse`).
-/
import QuadFormsKB.Literature.Watson1963.ProbesTwo
import QuadFormsKB.Literature.Watson1963.QuaternaryOdd
import QuadFormsKB.Literature.Watson1963.Final

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {N : ℕ}

theorem hessian_smul' {R : Type*} [CommRing R] {k : ℕ} (c : R) (Q : QuadForm R k) :
    (c • Q).hessian = c • Q.hessian := by
  rw [QuadForm.hessian, QuadForm.hessian, QuadForm.smul_coeff, Matrix.transpose_smul, smul_add]

theorem eval_smul_form' {R : Type*} [CommRing R] {k : ℕ} (c : R) (Q : QuadForm R k) (y : Fin k → R) :
    (c • Q).eval y = c * Q.eval y := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem quadA_eval' {R : Type*} [CommRing R] (z : Fin 2 → R) :
    (quadA : QuadForm R 2).eval z = z 0 ^ 2 + z 0 * z 1 + z 1 ^ 2 := by
  have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
  rw [hz]; unfold quadA; rw [Composition.bq_eval]; simp

theorem quadA_map : (quadA : QuadForm ℤ 2).map (Int.castRingHom ℤ_[2]) = (quadA : QuadForm ℤ_[2] 2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quadA, Composition.bq, QuadForm.map, QuadForm.ofUpper]

/-- $A = x^2 + xy + y^2$ is of type $A$ over $\mathbb Z_2$ (`hypA 1`): $-3$ is not a square. -/
theorem isometricGL_quadA_hypA : IsometricGL (quadA : QuadForm ℤ_[2] 2) (hypA (0 + 1)) := by
  have hdet : (quadA : QuadForm ℤ_[2] 2).hessian.det = 3 := hessian_det_quadA
  refine (isometricGL_hypA_iff (j := 0) quadA (by rw [hdet]; exact QuadFormsKB.Cassels.dyadic_isUnit_three)).2 ?_
  rw [hdet]
  intro hsq
  have hu : IsUnit ((-1 : ℤ_[2]) ^ (0 + 1) * 3) := isUnit_neg_one_pow.mul QuadFormsKB.Cassels.dyadic_isUnit_three
  have h8 := (isSquare_iff_dvd_eight hu ⟨-1, by ring⟩).1 hsq
  obtain ⟨c, hc⟩ := h8
  have : (4 : ℤ_[2]) * (1 + 2 * c) = 0 := by linear_combination -hc
  have h0 := (mul_eq_zero.1 this).resolve_left (by norm_num)
  exact not_two_dvd_one' ⟨-c, by linear_combination h0⟩

/-- A binary $a x^2 + b xy + a' y^2$ with $a, b, a'$ odd is of type $A$ over $\mathbb Z_2$. -/
theorem isometricGL_bq_hypA {a b a' : ℤ_[2]} (ha : ¬ (2 : ℤ_[2]) ∣ a) (hb : ¬ (2 : ℤ_[2]) ∣ b)
    (ha' : ¬ (2 : ℤ_[2]) ∣ a') : IsometricGL (Composition.bq a b a') (hypA (0 + 1)) := by
  have hdet : (Composition.bq a b a').hessian.det = 4 * a * a' - b ^ 2 := by
    have := Composition.neg_det_bq a b a'; linear_combination -this
  have hbu := isUnit_of_not_two_dvd hb
  have hdu : IsUnit (Composition.bq a b a').hessian.det := by
    rw [hdet]
    refine isUnit_of_not_two_dvd fun h => hb ?_
    have : (2 : ℤ_[2]) ∣ b ^ 2 := by
      have := dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (⟨2, by norm_num⟩ : (2 : ℤ_[2]) ∣ 4) a) a') h
      simpa using this
    exact Prime.dvd_of_dvd_pow (PadicInt.prime_p (p := 2) |> fun h => by exact_mod_cast h) this
  refine (isometricGL_hypA_iff (j := 0) _ hdu).2 ?_
  rw [hdet]
  intro hsq
  have hu : IsUnit ((-1 : ℤ_[2]) ^ (0 + 1) * (4 * a * a' - b ^ 2)) := isUnit_neg_one_pow.mul (hdet ▸ hdu)
  obtain ⟨t, ht⟩ := Composition.two_dvd_sub_one_of_isUnit hbu
  have h4 : (4 : ℤ_[2]) ∣ (-1 : ℤ_[2]) ^ (0 + 1) * (4 * a * a' - b ^ 2) - 1 :=
    ⟨-(a * a') + t * t + t, by
      have : b = 2 * t + 1 := by linear_combination ht
      rw [this]; ring⟩
  obtain ⟨c, hc⟩ := (isSquare_iff_dvd_eight hu h4).1 hsq
  obtain ⟨d, hd⟩ := eight_dvd_sq_sub_one hbu
  have : (4 : ℤ_[2]) * (a * a' + 2 * (c - d)) = 0 := by linear_combination -hc + hd
  have h0 := (mul_eq_zero.1 this).resolve_left (by norm_num)
  have hodd : ¬ (2 : ℤ_[2]) ∣ a * a' := fun h => by
    rcases (PadicInt.prime_p (p := 2) |> fun hp => (show Prime (2 : ℤ_[2]) by exact_mod_cast hp)).dvd_or_dvd h
      with h | h
    · exact ha h
    · exact ha' h
  exact hodd ⟨-(c - d), by linear_combination h0⟩

end QuadFormsKB.Watson1963
