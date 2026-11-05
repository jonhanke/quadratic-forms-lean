/-
# Cassels, Chapter 6, §4: Legendre's theorem by the geometry of numbers

**Setting.** Cassels, *Rational Quadratic Forms*, Ch. 6, §4: $g(\vec x) = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with
integers $a_j$ and $a_0a_1a_2$ squarefree (Cassels' $a_1, a_2, a_3$ are $a_0, a_1, a_2$ here; indices of `Fin 3` are
taken modulo $3$, so $j + 1$, $j + 2$ are the two other indices). A zero is $\vec b \in \mathbb Z^3$, $\vec b \ne \vec 0$,
with $g(\vec b) = 0$.

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6)
* Theorem 4.1 (Legendre), in Cassels' integral form with the congruence conditions (i)–(iii): `legendre`;
* Corollary 1 to Theorem 4.1 (a zero with $\lvert a_0\rvert b_0^2 + \lvert a_1\rvert b_1^2 + \lvert a_2\rvert b_2^2 <
  4\lvert a_0a_1a_2\rvert$): `legendre_small_zero`;
* Corollary 2 to Theorem 4.1 (a ternary form isotropic at all places but one is isotropic):
  `isotropic_of_isotropic_except`;
* the remark on quadratic reciprocity after Corollary 2 (6.r2): `legendre_reciprocity_remark`.

**Proof notes.** Theorem 4.1 and Corollary 1 follow Cassels: the conditions (i)–(iii) give congruences on $\vec z$ with
moduli of product $4\lvert a_0a_1a_2\rvert$ which force $g(\vec z) \equiv 0 \pmod{4\lvert a_0a_1a_2\rvert}$, and
Ch. 5, Theorem 2.3 (`minkowski_congruences`) applied to the ellipsoid $\lvert a_0\rvert x_0^2 + \lvert a_1\rvert x_1^2 +
\lvert a_2\rvert x_2^2 < 4\lvert a_0a_1a_2\rvert$, of volume $\frac{4\pi}{3}\cdot 8\lvert a_0a_1a_2\rvert >
2^3\cdot 4\lvert a_0a_1a_2\rvert$, gives a nonzero $\vec b$ with $\lvert g(\vec b)\rvert < 4\lvert a_0a_1a_2\rvert$,
hence $g(\vec b) = 0$. The odd primes $p \mid a_j$ are combined by the Chinese remainder theorem into one congruence
$z_{j+1} \equiv R_jz_{j+2}$ modulo the odd part of $\lvert a_j\rvert$. Corollary 2 is proved from the product formula for
the Hilbert symbol (`hilbert_product_formula`) and the Strong Hasse Principle for $n = 3$ (`hasseMinkowski_three`), as
Cassels does, except that the last step uses `hasseMinkowski_three` in place of Theorem 4.1 with Lemmas 4.2–4.3.
-/
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

namespace QuadFormsKB.Cassels.Ch6

section LegendreHelpers

open MeasureTheory Real

private lemma vol_unit_ball3 :
    volume {y : Fin 3 → ℝ | ∑ i, |y i| ^ (2:ℝ) < 1} = ENNReal.ofReal (4 * π / 3) := by
  rw [volume_sum_rpow_lt_one (Fin 3) (by norm_num : (1:ℝ) ≤ 2)]
  congr 1
  have h1 : Real.Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have h2 : Real.Gamma ((Fintype.card (Fin 3) : ℝ) / 2 + 1) = 3 * √π / 4 := by
    have : ((Fintype.card (Fin 3) : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 := by simp; norm_num
    rw [this, Real.Gamma_add_one (by norm_num), h1]; ring
  rw [h1, h2]
  simp only [Fintype.card_fin]
  have hs : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  field_simp
  have : √π ^ 3 = √π * π := by
    have e : √π ^ 3 = √π ^ 2 * √π := by ring
    rw [e, hsq]; ring
  nlinarith [this]

private lemma vol_ellipsoid (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) :
    volume {x : Fin 3 → ℝ | ∑ i, w i * x i ^ 2 < 4 * (w 0 * w 1 * w 2)} =
      ENNReal.ofReal (32 * π / 3 * (w 0 * w 1 * w 2)) := by
  set P := w 0 * w 1 * w 2 with hP
  have hP0 : 0 < P := by have := hw 0; have := hw 1; have := hw 2; positivity
  set d : Fin 3 → ℝ := fun i => √(w i / (4 * P)) with hd
  have hdpos : ∀ i, 0 < d i := fun i => Real.sqrt_pos.mpr (by have := hw i; positivity)
  have hd2 : ∀ i, d i ^ 2 = w i / (4 * P) := fun i =>
    Real.sq_sqrt (by have := hw i; positivity)
  set f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' (Matrix.diagonal d) with hf
  have hfx : ∀ x i, f x i = d i * x i := by
    intro x i; simp [hf, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det f = d 0 * d 1 * d 2 := by
    rw [hf, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
  have hdet' : d 0 * d 1 * d 2 = 1 / (8 * P) := by
    have h1 : (d 0 * d 1 * d 2) ^ 2 = (1 / (8 * P)) ^ 2 := by
      have : (d 0 * d 1 * d 2) ^ 2 = d 0 ^ 2 * d 1 ^ 2 * d 2 ^ 2 := by ring
      rw [this, hd2, hd2, hd2]
      field_simp
      rw [hP]; ring
    have := hdpos 0; have := hdpos 1; have := hdpos 2
    have hp : 0 < d 0 * d 1 * d 2 := by positivity
    exact (pow_left_inj₀ hp.le (by positivity) (by norm_num : (2:ℕ) ≠ 0)).1 h1
  have hset : {x : Fin 3 → ℝ | ∑ i, w i * x i ^ 2 < 4 * P} =
      f ⁻¹' {y : Fin 3 → ℝ | ∑ i, |y i| ^ (2:ℝ) < 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hfx]
    have : ∀ i, |d i * x i| ^ (2:ℝ) = (w i * x i ^ 2) / (4 * P) := by
      intro i
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs, mul_pow, hd2]
      ring
    simp_rw [this]
    rw [← Finset.sum_div, div_lt_one (by positivity)]
  rw [hset, Measure.addHaar_preimage_linearMap volume (by rw [hdet, hdet']; positivity), vol_unit_ball3,
    hdet, hdet']
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_pos (by positivity)]
  field_simp
  norm_num

end LegendreHelpers

private lemma dvd_poly_of_dvd_sub (b c q R R' : ℤ) (h : q ∣ R - R') (h' : q ∣ b * R' ^ 2 + c) :
    q ∣ b * R ^ 2 + c := by
  have : b * R ^ 2 + c = (b * R' ^ 2 + c) + (R - R') * (b * (R + R')) := by ring
  rw [this]
  exact dvd_add h' (Dvd.dvd.mul_right h _)

private lemma crt_root (b c : ℤ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ∃ r : ℤ, (p : ℤ) ∣ b * r ^ 2 + c) :
    ∃ R : ℤ, ∀ p ∈ S, (p : ℤ) ∣ b * R ^ 2 + c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert p S hpS ih =>
    obtain ⟨R₁, hR₁⟩ := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    obtain ⟨hp, r, hr⟩ := hS p (Finset.mem_insert_self p S)
    have hcop : IsCoprime (p : ℤ) ((∏ q ∈ S, q : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (hS q (Finset.mem_insert_of_mem hq)).1).2
        (fun h => hpS (h ▸ hq))
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨r * (v * ((∏ q ∈ S, q : ℕ) : ℤ)) + R₁ * (u * p), ?_⟩
    intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · refine dvd_poly_of_dvd_sub b c _ _ r ?_ hr
      exact ⟨(R₁ - r) * u, by linear_combination r * huv⟩
    · refine dvd_poly_of_dvd_sub b c _ _ R₁ ?_ (hR₁ q hq)
      have hqd : (q : ℤ) ∣ ((∏ q ∈ S, q : ℕ) : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem _ hq
      have : r * (v * ((∏ q ∈ S, q : ℕ) : ℤ)) + R₁ * (u * p) - R₁ =
          (r - R₁) * v * ((∏ q ∈ S, q : ℕ) : ℤ) := by
        linear_combination R₁ * huv
      rw [this]
      exact Dvd.dvd.mul_left hqd _

private lemma exists_root_of_squarefree (b c : ℤ) (P : ℕ) (hP : Squarefree P)
    (h : ∀ p : ℕ, p.Prime → p ∣ P → ∃ r : ℤ, (p : ℤ) ∣ b * r ^ 2 + c) :
    ∃ R : ℤ, (P : ℤ) ∣ b * R ^ 2 + c := by
  obtain ⟨R, hR⟩ := crt_root b c P.primeFactors (fun p hp => by
    have := Nat.mem_primeFactors.1 hp
    exact ⟨this.1, h p this.1 this.2.1⟩)
  refine ⟨R, ?_⟩
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, ← Nat.prod_primeFactors_of_squarefree hP]
  refine Finset.prod_primes_dvd _ (fun p hp => (Nat.mem_primeFactors.1 hp).1.prime) ?_
  intro p hp
  have := hR p hp
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at this
  exact this

private lemma sum_rot (a z : Fin 3 → ℤ) (j : Fin 3) :
    ∑ i, a i * z i ^ 2 = a j * z j ^ 2 + a (j + 1) * z (j + 1) ^ 2 + a (j + 2) * z (j + 2) ^ 2 := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

private lemma succ_ne (j : Fin 3) : j + 1 ≠ j ∧ j + 2 ≠ j ∧ j + 1 ≠ j + 2 := by
  fin_cases j <;> decide

/-- A coefficient row for the linear form `u p - c * u q`. -/
private def row2 (p q : Fin 3) (c : ℤ) : Fin 3 → ℤ :=
  fun k => if k = p then 1 else if k = q then -c else 0

private lemma row2_sum (p q : Fin 3) (c : ℤ) (hpq : p ≠ q) (u : Fin 3 → ℤ) :
    ∑ k, row2 p q c k * u k = u p - c * u q := by
  fin_cases p <;> fin_cases q <;> simp_all [row2, Fin.sum_univ_three] <;> ring

private lemma two_even (a0 a1 a2 s z0 z1 z2 : ℤ) (ha0 : (2 : ℤ) ∣ a0) (hs : s = 0 ∨ s = 1)
    (h8 : (8 : ℤ) ∣ a1 + a2 + s * a0) (h4 : (4 : ℤ) ∣ z1 - z2) (h2 : (2 : ℤ) ∣ z0 - s * z2) :
    (8 : ℤ) ∣ a0 * z0 ^ 2 + a1 * z1 ^ 2 + a2 * z2 ^ 2 := by
  obtain ⟨c, rfl⟩ := ha0
  obtain ⟨k, hk⟩ := h8
  obtain ⟨t, ht⟩ := h4
  obtain ⟨u, hu⟩ := h2
  have e1 : z1 = z2 + 4 * t := by linarith
  have e0 : z0 = s * z2 + 2 * u := by linarith
  have e2 : a2 = 8 * k - a1 - s * (2 * c) := by linarith
  subst e1 e0 e2
  rcases hs with rfl | rfl
  · exact ⟨k * z2 ^ 2 + c * u ^ 2 + a1 * t * z2 + 2 * a1 * t ^ 2, by ring⟩
  · exact ⟨k * z2 ^ 2 + c * (z2 * u + u ^ 2) + a1 * t * z2 + 2 * a1 * t ^ 2, by ring⟩

private lemma odd_case (x y w z0 z1 z2 : ℤ) (h4 : (4 : ℤ) ∣ x + y) (h1 : (2 : ℤ) ∣ z0 - z1)
    (h2 : (2 : ℤ) ∣ z2) : (4 : ℤ) ∣ x * z0 ^ 2 + y * z1 ^ 2 + w * z2 ^ 2 := by
  obtain ⟨k, hk⟩ := h4
  obtain ⟨t, ht⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have e0 : z0 = z1 + 2 * t := by linarith
  have e1 : y = 4 * k - x := by linarith
  subst e0 e1
  exact ⟨k * z1 ^ 2 + x * t * z1 + x * t ^ 2 + w * v ^ 2, by ring⟩

private lemma odd_part_dvd (P x y z u0 u1 u2 R : ℤ) (hx : P ∣ x) (hR : P ∣ y * R ^ 2 + z)
    (hu : P ∣ u1 - R * u2) : P ∣ x * u0 ^ 2 + y * u1 ^ 2 + z * u2 ^ 2 := by
  have : x * u0 ^ 2 + y * u1 ^ 2 + z * u2 ^ 2 =
      x * u0 ^ 2 + ((y * R ^ 2 + z) * u2 ^ 2 + (u1 - R * u2) * (y * (u1 + R * u2))) := by ring
  rw [this]
  exact dvd_add (Dvd.dvd.mul_right hx _)
    (dvd_add (Dvd.dvd.mul_right hR _) (Dvd.dvd.mul_right hu _))

private lemma isCoprime_of_sqfree_mul3 (x y z : ℤ) (h : Squarefree (x * y * z)) : IsCoprime x y := by
  have h1 : Squarefree (x * y) := h.of_mul_left
  exact (IsRelPrime.of_squarefree_mul h1).isCoprime

/-- Helper: the coefficients $a_0, a_1, a_2$ of a squarefree product $a_0a_1a_2$ are pairwise coprime. -/
theorem coprime_pairs (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2)) :
    ∀ j k : Fin 3, j ≠ k → IsCoprime (a j) (a k) := by
  have h01 : IsCoprime (a 0) (a 1) := isCoprime_of_sqfree_mul3 _ _ _ hsq
  have h02 : IsCoprime (a 0) (a 2) :=
    isCoprime_of_sqfree_mul3 _ _ (a 1) (by convert hsq using 1; ring)
  have h12 : IsCoprime (a 1) (a 2) :=
    isCoprime_of_sqfree_mul3 _ _ (a 0) (by convert hsq using 1; ring)
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp_all [IsCoprime.symm]

/-- Helper: each coefficient $a_j$ of a squarefree product $a_0a_1a_2$ is squarefree. -/
theorem sqfree_each (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2)) (j : Fin 3) :
    Squarefree (a j) := by
  refine hsq.squarefree_of_dvd ?_
  fin_cases j
  · exact ⟨a 1 * a 2, by simp; ring⟩
  · exact ⟨a 0 * a 2, by simp; ring⟩
  · exact ⟨a 0 * a 1, by simp; ring⟩

private lemma odd_part_data (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2)) :
    ∃ P : Fin 3 → ℕ, (∀ j, 0 < P j) ∧ (∀ j, Odd (P j)) ∧ (∀ j, (P j : ℤ) ∣ a j) ∧
      (∀ j, Squarefree (P j)) ∧ (∀ j k, j ≠ k → Nat.Coprime (P j) (P k)) ∧
      (∏ j, P j) * (if (2 : ℤ) ∣ a 0 * a 1 * a 2 then 2 else 1) = (a 0 * a 1 * a 2).natAbs := by
  have hcop := coprime_pairs a hsq
  have hne : ∀ j, a j ≠ 0 := fun j => (sqfree_each a hsq j).ne_zero
  have hpar : ∀ j k, j ≠ k → ¬ ((2 : ℤ) ∣ a j ∧ (2 : ℤ) ∣ a k) := by
    intro j k hjk ⟨h1, h2⟩
    have := (hcop j k hjk).isUnit_of_dvd' h1 h2
    exact absurd (Int.isUnit_iff.1 this) (by norm_num)
  set e : Fin 3 → ℕ := fun j => if (2 : ℤ) ∣ a j then 2 else 1 with he
  set P : Fin 3 → ℕ := fun j => (a j).natAbs / e j with hP
  have hPe : ∀ j, P j * e j = (a j).natAbs := by
    intro j
    simp only [hP, he]
    split_ifs with h
    · have : 2 ∣ (a j).natAbs := by
        have := Int.natAbs_dvd_natAbs.2 h
        simpa using this
      exact Nat.div_mul_cancel this
    · simp
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have := hPe j
    have h0 : (a j).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (hne j)
    exact Nat.pos_of_ne_zero (fun h => h0 (by rw [← this, h]; simp))
  · intro j
    have := hPe j
    have hsj := sqfree_each a hsq j
    by_cases h : (2 : ℤ) ∣ a j
    · have he2 : e j = 2 := by simp [he, h]
      rw [he2] at this
      rw [Nat.odd_iff]
      by_contra hc
      have h2 : 2 ∣ P j := by omega
      obtain ⟨q, hq⟩ := h2
      have : (2 : ℤ) * 2 ∣ a j := by
        rw [← Int.natAbs_dvd_natAbs]
        refine ⟨q, ?_⟩
        have e2 : Int.natAbs 2 = 2 := rfl
        simp only [Int.natAbs_mul, e2]
        omega
      have := hsj 2 this
      exact absurd (Int.isUnit_iff.1 this) (by norm_num)
    · have he1 : e j = 1 := by simp [he, h]
      rw [he1, mul_one] at this
      rw [Nat.odd_iff]
      have hd : (2 : ℤ) ∣ a j ↔ 2 ∣ (a j).natAbs := by
        simpa using (Int.natAbs_dvd_natAbs (a := 2) (b := a j)).symm
      rw [hd] at h
      omega
  · intro j
    exact Int.natCast_dvd.2 (Dvd.intro _ (hPe j))
  · intro j
    refine Squarefree.squarefree_of_dvd (Dvd.intro _ (hPe j))
      (Int.squarefree_natAbs.2 (sqfree_each a hsq j))
  · intro j k hjk
    have h1 : (P j : ℤ) ∣ a j := Int.natCast_dvd.2 (Dvd.intro _ (hPe j))
    have h2 : (P k : ℤ) ∣ a k := Int.natCast_dvd.2 (Dvd.intro _ (hPe k))
    exact Nat.isCoprime_iff_coprime.1
      (((hcop j k hjk).of_isCoprime_of_dvd_left h1).of_isCoprime_of_dvd_right h2)
  · have hprod : (a 0 * a 1 * a 2).natAbs = (∏ j, P j) * (∏ j, e j) := by
      simp only [Int.natAbs_mul, Fin.prod_univ_three, ← hPe]
      ring
    rw [hprod]
    congr 1
    have p01 := hpar 0 1 (by decide)
    have p02 := hpar 0 2 (by decide)
    have p12 := hpar 1 2 (by decide)
    by_cases h0 : (2 : ℤ) ∣ a 0 <;> by_cases h1 : (2 : ℤ) ∣ a 1 <;> by_cases h2 : (2 : ℤ) ∣ a 2 <;>
      simp [he, Fin.prod_univ_three, Int.prime_two.dvd_mul, h0, h1, h2] <;> tauto

private lemma two_adic (a : Fin 3 → ℤ)
    (hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j)
    (hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1)) :
    ∃ (m3 m4 : ℕ) (h3 h4 : Fin 3 → ℤ), 0 < m3 ∧ 0 < m4 ∧
      m3 * m4 = 4 * (if (2 : ℤ) ∣ a 0 * a 1 * a 2 then 2 else 1) ∧
      ∀ u : Fin 3 → ℤ, (m3 : ℤ) ∣ ∑ k, h3 k * u k → (m4 : ℤ) ∣ ∑ k, h4 k * u k →
        ((m3 * m4 : ℕ) : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
  by_cases hA : (2 : ℤ) ∣ a 0 * a 1 * a 2
  · obtain ⟨j, hj⟩ : ∃ j, (2 : ℤ) ∣ a j := by
      rcases Int.prime_two.dvd_mul.1 hA with h | h
      · rcases Int.prime_two.dvd_mul.1 h with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    obtain ⟨s, hs, h8⟩ := hii j hj
    refine ⟨4, 2, row2 (j + 1) (j + 2) 1, row2 j (j + 2) s, by norm_num, by norm_num,
      by simp [hA], ?_⟩
    intro u hu3 hu4
    rw [row2_sum _ _ _ (succ_ne j).2.2] at hu3
    rw [row2_sum _ _ _ (succ_ne j).2.1.symm] at hu4
    rw [sum_rot a u j]
    have := two_even (a j) (a (j + 1)) (a (j + 2)) s (u j) (u (j + 1)) (u (j + 2)) hj hs h8
      (by simpa using hu3) (by simpa using hu4)
    simpa using this
  · obtain ⟨j, hj⟩ := hiii hA
    refine ⟨2, 2, row2 j (j + 1) 1, row2 (j + 2) j 0, by norm_num, by norm_num,
      by simp [hA], ?_⟩
    intro u hu3 hu4
    rw [row2_sum _ _ _ (succ_ne j).1.symm] at hu3
    rw [row2_sum _ _ _ (succ_ne j).2.1] at hu4
    rw [sum_rot a u j]
    have := odd_case (a j) (a (j + 1)) (a (j + 2)) (u j) (u (j + 1)) (u (j + 2)) hj
      (by simpa using hu3) (by simpa using hu4)
    simpa using this

/-- Helper (proof of Theorem 4.1): from the conditions (i)–(iii), the congruences on $\vec z$ (moduli of product
$4\lvert a_0a_1a_2\rvert$) that force $g(\vec z) \equiv 0 \pmod{4\lvert a_0a_1a_2\rvert}$. Public for `Ch6/NotesLegendre.lean`. -/
theorem legendre_cong_data (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j)
    (hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1)) :
    ∃ (m : Fin 5 → ℕ) (h : Fin 5 → Fin 3 → ℤ), (∀ l, 0 < m l) ∧
      ∏ l, m l = 4 * (a 0 * a 1 * a 2).natAbs ∧
      ∀ u : Fin 3 → ℤ, (∀ l, (m l : ℤ) ∣ ∑ j, h l j * u j) →
        ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
  obtain ⟨P, hPpos, hPodd, hPdvd, hPsq, hPcop, hPprod⟩ := odd_part_data a hsq
  have hR : ∀ j, ∃ R : ℤ, (P j : ℤ) ∣ a (j + 1) * R ^ 2 + a (j + 2) := by
    intro j
    refine exists_root_of_squarefree _ _ (P j) (hPsq j) (fun p hp hpd => ?_)
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := hPodd j
      rw [Nat.odd_iff] at this
      omega
    exact hi p hp hp2 j (dvd_trans (Int.natCast_dvd_natCast.2 hpd) (hPdvd j))
  choose R hR using hR
  obtain ⟨m3, m4, h3, h4, hm3, hm4, hm34, htwo⟩ := two_adic a hii hiii
  have hprod3 := hPprod
  rw [Fin.prod_univ_three] at hprod3
  have hN : 4 * (a 0 * a 1 * a 2).natAbs = P 0 * P 1 * P 2 * (m3 * m4) := by
    rw [hm34, ← hprod3]; ring
  refine ⟨![P 0, P 1, P 2, m3, m4],
    ![row2 (0 + 1) (0 + 2) (R 0), row2 (1 + 1) (1 + 2) (R 1), row2 (2 + 1) (2 + 2) (R 2), h3, h4],
    ?_, ?_, ?_⟩
  · intro l
    fin_cases l <;> simp [hPpos, hm3, hm4]
  · rw [Fin.prod_univ_five, hN]
    simp
    ring
  · intro u hl
    have hP : ∀ j, (P j : ℤ) ∣ ∑ k, row2 (j + 1) (j + 2) (R j) k * u k →
        (P j : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
      intro j hj
      rw [row2_sum _ _ _ (succ_ne j).2.2] at hj
      rw [sum_rot a u j]
      exact odd_part_dvd _ _ _ _ _ _ _ _ (hPdvd j) (hR j) hj
    have d0 := hP 0 (by simpa using hl 0)
    have d1 := hP 1 (by simpa using hl 1)
    have d2 := hP 2 (by simpa using hl 2)
    have dt := htwo u (by simpa using hl 3) (by simpa using hl 4)
    have c01 : Nat.Coprime (P 0 * P 1) (P 2) := Nat.coprime_mul_iff_left.2 ⟨hPcop 0 2 (by decide), hPcop 1 2 (by decide)⟩
    have h2cop : ∀ j, Nat.Coprime (P j) 2 := fun j =>
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 (hPodd j)))
    have hE : m3 * m4 = 4 ∨ m3 * m4 = 8 := by
      rw [hm34]; split_ifs <;> simp
    have c3 : Nat.Coprime (P 0 * P 1 * P 2) (m3 * m4) := by
      have hj : ∀ j, Nat.Coprime (P j) (m3 * m4) := by
        intro j
        rcases hE with h | h
        · rw [h, show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.Coprime.pow_right 2 (h2cop j)
        · rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.Coprime.pow_right 3 (h2cop j)
      exact Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_mul_iff_left.2 ⟨hj 0, hj 1⟩, hj 2⟩
    have d01 : ((P 0 * P 1 : ℕ) : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
      push_cast
      exact (Nat.isCoprime_iff_coprime.2 (hPcop 0 1 (by decide))).mul_dvd d0 d1
    have d012 : ((P 0 * P 1 * P 2 : ℕ) : ℤ) ∣ ∑ i, a i * u i ^ 2 := by
      push_cast
      have := (Nat.isCoprime_iff_coprime.2 c01).mul_dvd d01 d2
      push_cast at this
      exact this
    rw [hN]
    push_cast
    have := (Nat.isCoprime_iff_coprime.2 c3).mul_dvd d012 dt
    push_cast at this
    exact this

private lemma ellipsoid_convex (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℝ) :
    Convex ℝ {x : Fin 3 → ℝ | ∑ i, w i * x i ^ 2 < c} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at *
  have key : ∀ i, w i * (s * x i + t * y i) ^ 2 ≤ s * (w i * x i ^ 2) + t * (w i * y i ^ 2) := by
    intro i
    have h1 : s * x i ^ 2 + t * y i ^ 2 - (s * x i + t * y i) ^ 2 = s * t * (x i - y i) ^ 2 := by
      have : t = 1 - s := by linarith
      subst this; ring
    have h2 : 0 ≤ s * t * (x i - y i) ^ 2 := by positivity
    have h3 : w i * (s * x i ^ 2 + t * y i ^ 2 - (s * x i + t * y i) ^ 2) = w i * (s * t * (x i - y i) ^ 2) := by rw [h1]
    nlinarith [mul_nonneg (hw i) h2, h3]
  calc ∑ i, w i * (s • x + t • y) i ^ 2
      ≤ ∑ i, (s * (w i * x i ^ 2) + t * (w i * y i ^ 2)) :=
        Finset.sum_le_sum (fun i _ => by simpa using key i)
    _ = s * ∑ i, w i * x i ^ 2 + t * ∑ i, w i * y i ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < c := by
        rcases hs.eq_or_lt with h0 | h0
        · have : t = 1 := by linarith
          subst this; rw [← h0]; simpa using hy
        · have := mul_lt_mul_of_pos_left hx h0
          have := mul_le_mul_of_nonneg_left hy.le ht
          have hc : (s + t) * c = c := by rw [hst]; ring
          nlinarith

/-- **Cassels, Ch. 6, Corollary 1 to Theorem 4.1**: *under the hypotheses of Theorem 4.1 there is a solution of
$g(\vec b) = 0$, $\vec b \ne \vec 0$, with $\lvert a_0\rvert b_0^2 + \lvert a_1\rvert b_1^2 + \lvert a_2\rvert b_2^2 <
4\lvert a_0a_1a_2\rvert$.* The hypotheses (Cassels' (4.3)–(4.5)), with $a_0a_1a_2$ squarefree:
(i) for an odd prime $p \mid a_j$ there is $r$ with $a_{j+1}r^2 + a_{j+2} \equiv 0 \pmod p$ (Cassels: "say
$p \mid a_1$, $a_2r_p^2 + a_3 \equiv 0$"; for $p \mid a_j$ the condition is symmetric in the other two coefficients);
(ii) if $2 \mid a_j$ there is $s \in \{0, 1\}$ with $a_{j+1} + a_{j+2} + sa_j \equiv 0 \pmod 8$;
(iii) if $2 \nmid a_0a_1a_2$ then $a_j + a_{j+1} \equiv 0 \pmod 4$ for some $j$ (Cassels: "on permuting").
The inequality is garbled in the machine-read text ("$= 4\lvert a_1a_2a_3\rvert$"); the page image (p. 82) shows the
strict inequality stated here. -/
@[kb "cassels1978" "Ch. 6, Cor. 1 to Thm. 4.1, p. 82"]
theorem legendre_small_zero (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j)
    (hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1)) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 ∧ ∑ i, |a i| * b i ^ 2 < 4 * |a 0 * a 1 * a 2| := by
  obtain ⟨m, h, hm, hprod, hdiv⟩ := legendre_cong_data a hsq hi hii hiii
  have ha : ∀ i, a i ≠ 0 := fun i => (sqfree_each a hsq i).ne_zero
  have hw : ∀ i, 0 < |(a i : ℝ)| := fun i => abs_pos.2 (by exact_mod_cast ha i)
  have habs : |((a 0 * a 1 * a 2 : ℤ) : ℝ)| = |(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)| := by
    push_cast; rw [abs_mul, abs_mul]
  set C : Set (Fin 3 → ℝ) :=
    {x | ∑ i, |(a i : ℝ)| * x i ^ 2 < 4 * |((a 0 * a 1 * a 2 : ℤ) : ℝ)|} with hC
  have hCvol : MeasureTheory.volume C =
      ENNReal.ofReal (32 * Real.pi / 3 * (|(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)|)) := by
    rw [hC, habs]
    exact vol_ellipsoid (fun i => |(a i : ℝ)|) hw
  have hNpos : (0 : ℝ) < |(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)| := by
    have := hw 0; have := hw 1; have := hw 2; positivity
  have hvol : 2 ^ 3 * ((∏ l, m l : ℕ) : ENNReal) < MeasureTheory.volume C := by
    rw [hCvol, hprod]
    have hcast : ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℝ) =
        4 * (|(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)|) := by
      rw [← habs]; push_cast; rw [Nat.cast_natAbs]; push_cast; ring
    have hL : (2 : ENNReal) ^ 3 * ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ENNReal) =
        ENNReal.ofReal (32 * (|(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)|)) := by
      have : (32 : ℝ) * (|(a 0 : ℝ)| * |(a 1 : ℝ)| * |(a 2 : ℝ)|) =
          8 * ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℝ) := by rw [hcast]; ring
      rw [this, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [hL, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [Real.pi_gt_three]
  obtain ⟨u, hu0, hudiv, huC⟩ := minkowski_congruences h m hm (C := C)
    (fun x hx => by simpa [hC] using hx)
    (ellipsoid_convex _ (fun i => (hw i).le) _) hvol
  have hlt : ∑ i, |a i| * u i ^ 2 < 4 * |a 0 * a 1 * a 2| := by
    have h1 : ∑ i, |(a i : ℝ)| * ((u i : ℤ) : ℝ) ^ 2 < 4 * |((a 0 * a 1 * a 2 : ℤ) : ℝ)| := huC
    exact_mod_cast h1
  refine ⟨u, hu0, ?_, hlt⟩
  have hd := hdiv u hudiv
  have hcast : ((4 * (a 0 * a 1 * a 2).natAbs : ℕ) : ℤ) = 4 * |a 0 * a 1 * a 2| := by
    push_cast; rfl
  rw [hcast] at hd
  refine Int.eq_zero_of_abs_lt_dvd hd ?_
  calc |∑ i, a i * u i ^ 2| ≤ ∑ i, |a i * u i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * u i ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_pow, sq_abs]
    _ < 4 * |a 0 * a 1 * a 2| := hlt

/-- **Cassels, Ch. 6, Theorem 4.1** (Legendre): *let $g = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with $a_j \in \mathbb Z$ and
$a_0a_1a_2$ squarefree, satisfying the conditions (i)–(iii) (see `legendre_small_zero`); then there are
$b_0, b_1, b_2 \in \mathbb Z$, not all $0$, with $g(\vec b) = 0$.* -/
@[kb "cassels1978" "Ch. 6, Thm. 4.1, p. 80 (Legendre; integral form with the congruence conditions)"]
theorem legendre (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j)
    (hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1)) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 := by
  obtain ⟨b, hb, h0, -⟩ := legendre_small_zero a hsq hi hii hiii
  exact ⟨b, hb, h0⟩

/-- **Cassels, Ch. 6, Corollary 2 to Theorem 4.1**: *let $f$ be a regular ternary form over $\mathbb Q$ which is
isotropic over $\mathbb Q_p$ for all $p$ (including $p = \infty$) with one possible exception $p_0$ (finite or
$\infty$); then $f$ is isotropic over $\mathbb Q$.* -/
@[kb "cassels1978" "Ch. 6, Cor. 2 to Thm. 4.1, p. 82"]
theorem isotropic_of_isotropic_except (Q : RatQF 3) (hQ : Q.Nondegenerate) (v₀ : RatPlace)
    (h : ∀ v : RatPlace, v ≠ v₀ → RatPlace.atPlace (fun K _ _ => Q.IsotropicIn K) v) : Q.IsotropicIn ℚ := by
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  have hae : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      hilbertSymbol K (algebraMap ℚ K (-a 1 / a 0)) (algebraMap ℚ K (-a 2 / a 0)) = 1 := by
    intro K _ _
    rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), hae,
      HM3.isotropic_diag_three_iff K _ _ _ (ha 0) (ha 1) (ha 2)]
    simp
  have hx : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 1)) (ha 0)
  have hy : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 2)) (ha 0)
  have hloc : ∀ v : RatPlace, RatPlace.atPlace (fun K _ _ => Q.IsotropicIn K) v ↔
      v.hilbert (-a 1 / a 0) (-a 2 / a 0) = 1 := by
    intro v
    cases v with
    | infinite =>
      change Q.IsotropicIn ℝ ↔ _
      rw [key ℝ]; simp [RatPlace.hilbert]
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      change Q.IsotropicIn ℚ_[p] ↔ _
      rw [key ℚ_[p]]; simp [RatPlace.hilbert]
  obtain ⟨hfin, heven⟩ := hilbert_product_formula _ _ hx hy
  have hsub : {v : RatPlace | v.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1} ⊆ {v₀} := by
    intro v hv
    by_contra hne
    have := (hloc v).1 (h v hne)
    rw [Set.mem_ofPred_eq, this] at hv
    norm_num at hv
  have hempty : {v : RatPlace | v.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1} = ∅ := by
    rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h1
    · exact h0
    · rw [h1, Set.ncard_singleton] at heven
      exact absurd heven (by decide)
  refine (hasseMinkowski_three Q hQ).2 fun v => (hloc v).2 ?_
  have hpm : v.hilbert (-a 1 / a 0) (-a 2 / a 0) = 1 ∨ v.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1 := by
    cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
  rcases hpm with h1 | h1
  · exact h1
  · have : v ∈ ({v : RatPlace | v.hilbert (-a 1 / a 0) (-a 2 / a 0) = -1} : Set RatPlace) := h1
    rw [hempty] at this
    exact absurd this (Set.notMem_empty v)

/-- **Cassels, Ch. 6, §4, p. 82** (remark after Corollary 2, 6.r2: Theorem 4.1 implies cases of quadratic
reciprocity): *there are no odd primes $q_1 \ne q_2$ with (α) $q_1 \equiv 3 \pmod 4$, (β) $-q_2$ a quadratic residue
of $q_1$ and (γ) $-q_1$ a quadratic residue of $q_2$*, since otherwise Theorem 4.1 would apply to
$q_1x_0^2 + q_2x_1^2 + x_2^2$, which is definite. The machine-read text garbles the conditions; the page image (p. 82)
confirms them (Cassels labels them (β) $-q_1$ a residue of $q_2$, (γ) $-q_2$ a residue of $q_1$: the same two conditions,
named in the other order). -/
@[kb "cassels1978" "Ch. 6, §4, p. 82 (Thm. 4.1 implies cases of quadratic reciprocity)"]
theorem legendre_reciprocity_remark (q₁ q₂ : ℕ) [hq₁ : Fact q₁.Prime] [hq₂ : Fact q₂.Prime] (hne : q₁ ≠ q₂) (h₂ : q₂ ≠ 2)
    (hα : q₁ % 4 = 3) (hβ : IsSquare (-(q₂ : ZMod q₁))) (hγ : IsSquare (-(q₁ : ZMod q₂))) : False := by
  have p₁ := hq₁.out
  have p₂ := hq₂.out
  set a : Fin 3 → ℤ := ![(q₁ : ℤ), (q₂ : ℤ), 1] with ha
  have hcop : Nat.Coprime q₁ q₂ := (Nat.coprime_primes p₁ p₂).2 hne
  have hsq : Squarefree (a 0 * a 1 * a 2) := by
    have : a 0 * a 1 * a 2 = ((q₁ * q₂ : ℕ) : ℤ) := by simp [ha]
    rw [this, Int.squarefree_natCast, Nat.squarefree_mul_iff]
    exact ⟨hcop, p₁.squarefree, p₂.squarefree⟩
  have hq₁odd : ¬ (2 : ℤ) ∣ (q₁ : ℤ) := by omega
  have hq₂odd : ¬ (2 : ℤ) ∣ (q₂ : ℤ) := by
    intro h
    have : 2 ∣ q₂ := by exact_mod_cast h
    exact h₂ ((Nat.prime_dvd_prime_iff_eq Nat.prime_two p₂).1 this).symm
  have hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2) := by
    intro p hp _ j hj
    fin_cases j
    · -- p = q₁, need q₁ ∣ q₂ r² + 1
      have hj' : (p : ℤ) ∣ (q₁ : ℤ) := by simpa [ha] using hj
      have hpq : p = q₁ := (Nat.prime_dvd_prime_iff_eq hp p₁).1 (by exact_mod_cast hj')
      subst hpq
      obtain ⟨s, hs⟩ := hβ
      have hq₂0 : (q₂ : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h; exact hne ((Nat.prime_dvd_prime_iff_eq p₁ p₂).1 h)
      refine ⟨((s * (q₂ : ZMod p)⁻¹ : ZMod p).val : ℤ), ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e : (q₂ : ZMod p) * (s * (q₂ : ZMod p)⁻¹) ^ 2 + 1 = 0 := by
        calc (q₂ : ZMod p) * (s * (q₂ : ZMod p)⁻¹) ^ 2 + 1
            = (s * s) * ((q₂ : ZMod p) * (q₂ : ZMod p)⁻¹) * (q₂ : ZMod p)⁻¹ + 1 := by ring
          _ = 0 := by rw [← hs, mul_inv_cancel₀ hq₂0]; field_simp; ring
      simpa [ha] using e
    · -- p = q₂, need q₂ ∣ r² + q₁
      have hj' : (p : ℤ) ∣ (q₂ : ℤ) := by simpa [ha] using hj
      have hpq : p = q₂ := (Nat.prime_dvd_prime_iff_eq hp p₂).1 (by exact_mod_cast hj')
      subst hpq
      obtain ⟨s, hs⟩ := hγ
      refine ⟨(s.val : ℤ), ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e : 1 * s ^ 2 + (q₁ : ZMod p) = 0 := by linear_combination -hs
      simpa [ha] using e
    · have hj' : (p : ℤ) ∣ 1 := by simpa [ha] using hj
      have : p ∣ 1 := by exact_mod_cast hj'
      exact absurd (Nat.eq_one_of_dvd_one this) hp.ne_one
  have hii : ∀ j : Fin 3, (2 : ℤ) ∣ a j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ (8 : ℤ) ∣ a (j + 1) + a (j + 2) + s * a j := by
    intro j hj
    fin_cases j
    · exact absurd (by simpa [ha] using hj) hq₁odd
    · exact absurd (by simpa [ha] using hj) hq₂odd
    · simp [ha] at hj
  have hiii : ¬ (2 : ℤ) ∣ a 0 * a 1 * a 2 → ∃ j : Fin 3, (4 : ℤ) ∣ a j + a (j + 1) := by
    intro _
    refine ⟨2, ?_⟩
    have : a 2 + a (2 + 1) = 1 + (q₁ : ℤ) := by simp [ha]
    rw [this]; omega
  obtain ⟨b, hb0, hb⟩ := legendre a hsq hi hii hiii
  simp only [Fin.sum_univ_three, ha] at hb
  simp at hb
  have q1pos : (0 : ℤ) < q₁ := by exact_mod_cast p₁.pos
  have q2pos : (0 : ℤ) < q₂ := by exact_mod_cast p₂.pos
  have h0 : b 0 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2), mul_pos q1pos q2pos]
  have h1 : b 1 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2)]
  have h2 : b 2 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2)]
  apply hb0
  funext i; fin_cases i <;> simp [h0, h1, h2]

end QuadFormsKB.Cassels.Ch6
