/-
# Integrality: coefficients, values, and the secondary "classically integral" notion

**Integral** means integer upper-triangular coefficients. Results:

* a rational form is integral $\iff$ it comes from an `IntQF` $\iff$ it is integer-valued on
  $\mathbb{Z}^n$;
* classically integral $\iff$ every cross coefficient $c_{ij}$ ($i < j$) is even
  (`isClassicallyIntegral_iff`);
* $2Q$ is always classically integral, with Gram matrix the Hessian
  (`two_smul_isClassicallyIntegral`);
* the inclusion is strict: $x_0^2 + x_0 x_1 + x_1^2$ is not classically integral.
-/
import QuadFormsKB.Defs.Integral

open Matrix

namespace QuadFormsKB

variable {n : ℕ}

/-- **Integral $\iff$ comes from $\mathbb{Z}$:** a rational form $Q$ is integral iff
$Q = Q'$ viewed over $\mathbb{Q}$ for some integral form $Q'$ (`IntQF n`), i.e. its
coefficients are the images of integers. -/
@[kb "bhargavahanke" "§1"]
theorem RatQF.isIntegral_iff_exists_intQF (Q : RatQF n) :
    Q.IsIntegral ↔ ∃ Q' : IntQF n, Q'.map (Int.castRingHom ℚ) = Q := by
  constructor
  · intro h
    refine ⟨⟨Matrix.of fun i j => (Q.coeff i j).num, ?_⟩, ?_⟩
    · intro i j hij
      simp [Q.upper hij]
    · cases Q with
      | mk c u =>
        simp only [QuadForm.map]
        ext i j
        obtain ⟨z, hz⟩ := h i j
        simp only at hz
        simp [hz]
  · rintro ⟨Q', rfl⟩ i j
    exact ⟨Q'.coeff i j, rfl⟩

/-- **Integral $\iff$ integer-valued:** a rational form has integer coefficients iff
$Q(\vec{x}) \in \mathbb{Z}$ for every $\vec{x} \in \mathbb{Z}^n$. No factor of $2$ is lost, since
$c_{ii} = Q(\vec{e}_i)$ and $c_{ij} = Q(\vec{e}_i + \vec{e}_j) - Q(\vec{e}_i) - Q(\vec{e}_j)$. -/
@[kb "bhargavahanke" "§1"]
theorem RatQF.isIntegral_iff_integerValued (Q : RatQF n) :
    Q.IsIntegral ↔ ∀ x : Fin n → ℤ, ∃ z : ℤ, Q.eval (fun i => (x i : ℚ)) = z := by
  constructor
  · intro h x
    choose c hc using h
    refine ⟨∑ i, ∑ j, if i ≤ j then c i j * x i * x j else 0, ?_⟩
    simp only [QuadForm.eval, QuadForm.evalIn, hc, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    rfl
  · intro h
    have hE : ∀ x : Fin n → ℤ, Q.eval (fun i => (x i : ℚ)) = ∑ i, ∑ j, Q.coeff i j * x i * x j := by
      intro x
      simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hh
      · rfl
      · rw [Q.upper (lt_of_not_ge hh)]; ring
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨a, ha⟩ := h (Pi.single i 1)
      obtain ⟨b, hb⟩ := h (Pi.single j 1)
      obtain ⟨d, hd⟩ := h (Pi.single i 1 + Pi.single j 1)
      have hne : i ≠ j := ne_of_lt hij
      rw [hE] at ha hb hd
      simp [Pi.single_apply, mul_ite, mul_add, Finset.sum_add_distrib, Q.upper hij] at ha hb hd
      exact ⟨d - a - b, by push_cast; linarith⟩
    · obtain ⟨a, ha⟩ := h (Pi.single i 1)
      rw [hE] at ha
      simp [Pi.single_apply, mul_ite] at ha
      exact ⟨a, ha⟩
    · exact ⟨0, by rw [Q.upper hij]; simp⟩

/-- **Classically integral $\iff$ even cross coefficients:** an integral form is classically
integral iff $2 \mid c_{ij}$ for all $i < j$. -/
@[kb "cassels1978" "Ch. 9, §1"]
theorem isClassicallyIntegral_iff (Q : IntQF n) :
    IsClassicallyIntegral Q ↔ ∀ i j, i < j → Even (Q.coeff i j) := by
  have hE : ∀ x, Q.eval x = x ⬝ᵥ Q.coeff *ᵥ x := by
    intro x
    simp only [QuadForm.eval, QuadForm.evalIn, dotProduct, mulVec, Finset.mul_sum, Algebra.algebraMap_self, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · ring
    · rw [Q.upper (lt_of_not_ge h)]; ring
  have h2 : ∀ (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n), i ≠ j →
      (Pi.single i 1 + Pi.single j 1 : Fin n → ℤ) ⬝ᵥ M *ᵥ (Pi.single i 1 + Pi.single j 1)
        = M i i + M i j + M j i + M j j := by
    intro M i j _
    simp [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single, single_dotProduct]
    ring
  have h1 : ∀ (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n),
      (Pi.single i 1 : Fin n → ℤ) ⬝ᵥ M *ᵥ (Pi.single i 1) = M i i := by
    intro M i
    simp [mulVec_single, single_dotProduct]
  constructor
  · rintro ⟨A, hA, hQ⟩ i j hij
    have hne : i ≠ j := ne_of_lt hij
    have e1 := hQ (Pi.single i 1)
    have e2 := hQ (Pi.single j 1)
    have e3 := hQ (Pi.single i 1 + Pi.single j 1)
    simp only [gramForm, hE] at e1 e2 e3
    rw [h1, h1] at e1
    rw [h1, h1] at e2
    rw [h2 _ _ _ hne, h2 _ _ _ hne] at e3
    have hji : Q.coeff j i = 0 := Q.upper hij
    have hAs : A j i = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.transpose_apply] using this
    exact ⟨A i j, by linarith⟩
  · intro hev
    set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
      if i = j then Q.coeff i i else if i < j then Q.coeff i j / 2 else Q.coeff j i / 2 with hAdef
    have hAs : A.IsSymm := by
      ext i j
      rw [Matrix.transpose_apply, hAdef, Matrix.of_apply, Matrix.of_apply]
      by_cases h : i = j
      · subst h; rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
        rcases lt_or_gt_of_ne h with h' | h'
        · rw [ite_eq_left h', ite_eq_right (not_lt_of_gt h')]
        · rw [ite_eq_left h', ite_eq_right (not_lt_of_gt h')]
    have h2A : (2 : ℤ) • A = Q.coeff + Q.coeffᵀ := by
      ext i j
      rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, hAdef, Matrix.of_apply]
      by_cases h : i = j
      · subst h; rw [ite_eq_left rfl]; ring
      · rw [ite_eq_right h]
        rcases lt_or_gt_of_ne h with h' | h'
        · rw [ite_eq_left h', Q.upper h', add_zero]
          exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hev i j h'))
        · rw [ite_eq_right (not_lt_of_gt h'), Q.upper h', zero_add]
          exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hev j i h'))
    refine ⟨A, hAs, fun x => ?_⟩
    simp only [gramForm, hE]
    have key : (2 : ℤ) * (x ⬝ᵥ A *ᵥ x) = 2 * (x ⬝ᵥ Q.coeff *ᵥ x) := by
      have : (2 : ℤ) * (x ⬝ᵥ A *ᵥ x) = x ⬝ᵥ ((2 : ℤ) • A) *ᵥ x := by
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      rw [this, h2A, Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_mulVec x Q.coeffᵀ x,
        Matrix.vecMul_transpose, dotProduct_comm (Q.coeff *ᵥ x) x]
      ring
    omega

/-- **$2Q$ is classically integral** for every integral form $Q$: its Gram matrix is the
Hessian $H = C + C^{\mathsf T}$, i.e. $2Q(\vec{x}) = \vec{x}^{\mathsf T} H\, \vec{x}$. -/
@[kb "cassels1978" "Ch. 9, §1"]
theorem two_smul_isClassicallyIntegral (Q : IntQF n) :
    IsClassicallyIntegral ((2 : ℤ) • Q) := by
  refine ⟨Q.coeff + Q.coeffᵀ, ?_, ?_⟩
  · simp [Matrix.IsSymm, Matrix.transpose_add, add_comm]
  · intro x
    have hU : ∀ i j, j < i → Q.coeff i j = 0 := fun i j h => Q.upper h
    have h1 : QuadForm.eval ((2:ℤ) • Q) x = 2 * ∑ i, ∑ j, Q.coeff i j * x i * x j := by
      simp only [QuadForm.eval, QuadForm.evalIn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · show (algebraMap ℤ ℤ) (2 * Q.coeff i j) * x i * x j = _
        simp; ring
      · rw [hU i j (not_le.mp h)]; ring
    rw [h1]
    simp only [gramForm, dotProduct, mulVec, Matrix.add_apply, Matrix.transpose_apply, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    rw [Finset.sum_comm (f := fun i j => x i * (Q.coeff j i * x j))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **The Eisenstein form** $x_0^2 + x_0 x_1 + x_1^2$, the norm form of $\mathbb{Z}[\omega]$
($\omega$ a primitive cube root of unity). -/
def eisensteinForm : IntQF 2 := QuadForm.ofUpper ![![1, 1], ![0, 1]]

/-- **The inclusion is strict:** $x_0^2 + x_0 x_1 + x_1^2$ is integral but **not** classically
integral (its cross coefficient $1$ is odd). -/
@[kb "conway1997" "Lecture 1"]
theorem eisensteinForm_not_isClassicallyIntegral : ¬ IsClassicallyIntegral eisensteinForm := by
  rintro ⟨A, hA, h⟩
  have h1 := h ![1, 0]
  have h2 := h ![0, 1]
  have h3 := h ![1, 1]
  have hs : A 1 0 = A 0 1 := by
    have := congrFun (congrFun hA 0) 1
    simpa [Matrix.transpose_apply] using this
  simp [eisensteinForm, QuadForm.evalIn, QuadForm.ofUpper, gramForm, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h1 h2 h3
  omega

end QuadFormsKB
