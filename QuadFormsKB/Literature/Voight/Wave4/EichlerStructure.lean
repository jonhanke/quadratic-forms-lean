/-
# Local Eichler orders are conjugate to standard ones (Voight, Proposition 23.4.3, Corollary 23.4.10)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 23.4.3 (p. 382),
Corollary 23.4.10 (p. 383), Definition 23.4.11 (p. 384).

**Setting.** $R$ is a discrete valuation ring with fraction field $F$ (written `K` in the code, as in
`Tamagawa/MatOrder.lean`) and uniformizer $\pi$; $B = \mathrm M_2(F)$; orders are `Subalgebra R (Matrix (Fin 2) (Fin 2) K)`
(`IsOrder`, `IsMaximalOrder`); $\mathcal O_0(\pi^e) = \begin{pmatrix} R & R\\ \pi^eR & R\end{pmatrix}$ is
`Wave3.stdEichlerOrder R K π e`; conjugation $x \mapsto PxP^{-1}$ is `QuatOrder.conjAlgEquiv P Q` with $Q = P^{-1}$.
Matrix entries are indexed $0, 1$ (Voight's $e_{11}, e_{22}$ are `single 0 0`, `single 1 1` here).

**Contents.**
* `exists_eq_smul_mul_diag_mul` (the Cartan decomposition used in the proof, "Smith normal form"): every
  $g \in \mathrm{GL}_2(F)$ is $g = c\,U\operatorname{diag}(1, \pi^e)V$ with $c \in F^\times$, $U, V \in \mathrm{GL}_2(R)$, $e \ge 0$.
* `localEichlerStructure` (Proposition 23.4.3, (i) $\Rightarrow$ (ii)): every Eichler order of $\mathrm M_2(F)$ is conjugate
  to some $\mathcal O_0(\pi^e)$. This proves the library's named proposition `Wave3.LocalEichlerStructure R K π`.
* `isEichler_iff_exists_conj` (Proposition 23.4.3, (i) $\Leftrightarrow$ (ii); the sentence after Definition 23.4.11): an
  order of $\mathrm M_2(F)$ is Eichler iff it is conjugate to a standard Eichler order.

All proved; no inputs.
-/
import QuadFormsKB.Literature.Voight.Wave3.EichlerLocal

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave4

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Integral matrices and conjugation -/

/-- An integral matrix, viewed in $\mathrm M_2(F)$. -/
abbrev mapR (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) K := A.map (algebraMap R K)

theorem mapR_mem_matOrder (A : Matrix (Fin 2) (Fin 2) R) : mapR (K := K) A ∈ matOrder R K := by
  rw [mem_matOrder]; intro i j; exact ⟨A i j, rfl⟩

theorem mapR_mul (A B : Matrix (Fin 2) (Fin 2) R) : mapR (K := K) (A * B) = mapR A * mapR B :=
  Matrix.map_mul

theorem mapR_one : mapR (K := K) (1 : Matrix (Fin 2) (Fin 2) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

/-- Conjugation by an element of $\mathrm{GL}_2(R)$ preserves $\mathrm M_2(R)$. -/
theorem conj_mem_matOrder_iff {W W' : Matrix (Fin 2) (Fin 2) R} (hW : W * W' = 1) (hW' : W' * W = 1)
    (y : Matrix (Fin 2) (Fin 2) K) : mapR W * y * mapR W' ∈ matOrder R K ↔ y ∈ matOrder R K := by
  constructor
  · intro h
    have : y = mapR W' * (mapR W * y * mapR W') * mapR W := by
      simp only [← mul_assoc, ← mapR_mul, hW', mapR_one, one_mul]
      rw [mul_assoc, ← mapR_mul, hW', mapR_one, mul_one]
    rw [this]
    exact (matOrder R K).mul_mem ((matOrder R K).mul_mem (mapR_mem_matOrder _) h) (mapR_mem_matOrder _)
  · intro h
    exact (matOrder R K).mul_mem ((matOrder R K).mul_mem (mapR_mem_matOrder _) h) (mapR_mem_matOrder _)

/-- Membership in a conjugate subalgebra: $x \in P\mathcal SP^{-1}$ iff $P^{-1}xP \in \mathcal S$. -/
theorem mem_map_conj {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (S : Subalgebra R (Matrix (Fin 2) (Fin 2) K)) (x : Matrix (Fin 2) (Fin 2) K) :
    x ∈ S.map (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) ↔ Q * x * P ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Q * (P * y * Q) * P ∈ S
    simp only [← mul_assoc, hQP, one_mul]; rw [mul_assoc, hQP, mul_one]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change P * (Q * x * P) * Q = x
    simp only [← mul_assoc, hPQ, one_mul]; rw [mul_assoc, hPQ, mul_one]

/-! ### The Cartan decomposition of $\mathrm{GL}_2(F)$ -/

section Cartan

variable [IsDiscreteValuationRing R]

/-- $\operatorname{diag}(1, \pi^e)$ over $R$. -/
abbrev diagR (π : R) (e : ℕ) : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, π ^ e]

/-- The swap matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, its own inverse. -/
abbrev swapR : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

theorem swapR_mul_swapR : (swapR : Matrix (Fin 2) (Fin 2) R) * swapR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mapR_diagR (π : R) (e : ℕ) : mapR (K := K) (diagR π e) = diagP π e := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagP, Matrix.diagonal]

/-- **Row and column reduction with a unit corner**: an integral matrix $A$ with $\det A \ne 0$ and $A_{00}$ a unit is
$U\operatorname{diag}(1,\pi^e)V$ with $U, V \in \mathrm{GL}_2(R)$. -/
theorem exists_factor_of_isUnit {π : R} (hπ : Irreducible π) (A : Matrix (Fin 2) (Fin 2) R) (hA : IsUnit (A 0 0))
    (hdet : A.det ≠ 0) :
    ∃ (e : ℕ) (U U' V V' : Matrix (Fin 2) (Fin 2) R), U * U' = 1 ∧ U' * U = 1 ∧ V * V' = 1 ∧ V' * V = 1 ∧
      A = U * diagR π e * V := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨ai, hai⟩ : ∃ ai : R, A 0 0 * ai = 1 := ⟨(a⁻¹ : Rˣ), by rw [← ha, Units.mul_inv]⟩
  have hdetA : A.det = A 0 0 * (A 1 1 - A 1 0 * A 0 1 * ai) := by
    rw [Matrix.det_fin_two]; linear_combination (A 1 0 * A 0 1) * hai
  have hΔ0 : A 1 1 - A 1 0 * A 0 1 * ai ≠ 0 := by
    intro h; apply hdet; rw [hdetA, h, mul_zero]
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hΔ0 hπ
  obtain ⟨wi, hwi⟩ : ∃ wi : R, (w : R) * wi = 1 := ⟨(w⁻¹ : Rˣ), Units.mul_inv w⟩
  refine ⟨e, !![A 0 0, 0; A 1 0, (w : R)], !![ai, 0; -(A 1 0 * ai * wi), wi],
    !![1, A 0 1 * ai; 0, 1], !![1, -(A 0 1 * ai); 0, 1], ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    refine Matrix.ext fun i j => ?_
    revert i j
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      (try simp [Matrix.mul_apply, Fin.sum_univ_two, diagR]) <;>
      first | ring1 | linear_combination hai | linear_combination hwi |
        linear_combination (-(A 1 0 * ai)) * hwi | linear_combination (-(wi * A 1 0)) * hai |
        linear_combination (-(A 0 1)) * hai | linear_combination hw | linear_combination -hw

/-- **Smith normal form for $2 \times 2$ integral matrices** over a discrete valuation ring: an integral $A$ with
$\det A \ne 0$ and some entry a unit is $U\operatorname{diag}(1,\pi^e)V$ with $U, V \in \mathrm{GL}_2(R)$. -/
theorem exists_factor {π : R} (hπ : Irreducible π) (A : Matrix (Fin 2) (Fin 2) R) (hA : ∃ i j, IsUnit (A i j))
    (hdet : A.det ≠ 0) :
    ∃ (e : ℕ) (U U' V V' : Matrix (Fin 2) (Fin 2) R), U * U' = 1 ∧ U' * U = 1 ∧ V * V' = 1 ∧ V' * V = 1 ∧
      A = U * diagR π e * V := by
  have hs := swapR_mul_swapR (R := R)
  have hdets : (swapR : Matrix (Fin 2) (Fin 2) R).det = -1 := by simp [Matrix.det_fin_two]
  obtain ⟨i, j, hij⟩ := hA
  fin_cases i <;> fin_cases j
  · exact exists_factor_of_isUnit hπ A hij hdet
  · -- `A * swap` has corner `A 0 1`
    have h1 : IsUnit ((A * swapR (R := R)) 0 0) := by
      convert hij using 1; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h2 : (A * swapR).det ≠ 0 := by rw [Matrix.det_mul, hdets]; simpa using hdet
    obtain ⟨e, U, U', V, V', h3, h4, h5, h6, h7⟩ := exists_factor_of_isUnit hπ _ h1 h2
    refine ⟨e, U, U', V * swapR, swapR * V', h3, h4, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc swapR, hs, one_mul, h5]
    · rw [mul_assoc, ← mul_assoc V', h6, one_mul, hs]
    · rw [← mul_assoc, ← h7, mul_assoc, hs, mul_one]
  · -- `swap * A` has corner `A 1 0`
    have h1 : IsUnit ((swapR (R := R) * A) 0 0) := by
      convert hij using 1; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h2 : (swapR * A).det ≠ 0 := by rw [Matrix.det_mul, hdets]; simpa using hdet
    obtain ⟨e, U, U', V, V', h3, h4, h5, h6, h7⟩ := exists_factor_of_isUnit hπ _ h1 h2
    refine ⟨e, swapR * U, U' * swapR, V, V', ?_, ?_, h5, h6, ?_⟩
    · rw [mul_assoc, ← mul_assoc U, h3, one_mul, hs]
    · rw [mul_assoc, ← mul_assoc swapR, hs, one_mul, h4]
    · rw [mul_assoc, mul_assoc, ← mul_assoc U, ← h7, ← mul_assoc, hs, one_mul]
  · -- `swap * A * swap` has corner `A 1 1`
    have h1 : IsUnit ((swapR (R := R) * A * swapR (R := R)) 0 0) := by
      convert hij using 1; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h2 : (swapR * A * swapR).det ≠ 0 := by rw [Matrix.det_mul, Matrix.det_mul, hdets]; simpa using hdet
    obtain ⟨e, U, U', V, V', h3, h4, h5, h6, h7⟩ := exists_factor_of_isUnit hπ _ h1 h2
    refine ⟨e, swapR * U, U' * swapR, V * swapR, swapR * V', ?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc U, h3, one_mul, hs]
    · rw [mul_assoc, ← mul_assoc swapR, hs, one_mul, h4]
    · rw [mul_assoc, ← mul_assoc swapR, hs, one_mul, h5]
    · rw [mul_assoc, ← mul_assoc V', h6, one_mul, hs]
    · have : A = swapR * (swapR * A * swapR) * swapR := by
        simp only [← mul_assoc, hs, one_mul]; rw [mul_assoc, hs, mul_one]
      rw [this, h7]; simp only [mul_assoc]

/-- Clearing denominators: a nonzero $g \in \mathrm M_2(F)$ is $c\,A$ with $c \in F^\times$ and $A$ integral. -/
theorem exists_eq_smul_mapR (g : Matrix (Fin 2) (Fin 2) K) :
    ∃ (c : K) (A : Matrix (Fin 2) (Fin 2) R), c ≠ 0 ∧ g = c • mapR A := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun p => g p.1 p.2)
  choose A hA using fun i j => hd (i, j) (Finset.mem_univ _)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero d.2)
  refine ⟨(algebraMap R K d)⁻¹, Matrix.of A, inv_ne_zero hd0, ?_⟩
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, hA i j, Algebra.smul_def]
  field_simp

/-- A nonzero integral matrix over a discrete valuation ring is $\pi^n A'$ with some entry of $A'$ a unit. -/
theorem exists_eq_pow_smul_isUnit {π : R} (hπ : Irreducible π) (A : Matrix (Fin 2) (Fin 2) R) (hA : A ≠ 0) :
    ∃ (n : ℕ) (A' : Matrix (Fin 2) (Fin 2) R), A = π ^ n • A' ∧ ∃ i j, IsUnit (A' i j) := by
  classical
  set f : Fin 2 × Fin 2 → R := fun p => A p.1 p.2
  have hI : Ideal.span (Set.range f) ≠ ⊥ := by
    intro h
    apply hA; ext i j
    have : f (i, j) ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨(i, j), rfl⟩
    rw [h, Ideal.mem_bot] at this; exact this
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
  have hdvd : ∀ p, π ^ n ∣ f p := fun p => by
    have : f p ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨p, rfl⟩
    rw [hn, Ideal.mem_span_singleton] at this; exact this
  choose A' hA' using hdvd
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
  refine ⟨n, Matrix.of fun i j => A' (i, j), ?_, ?_⟩
  · ext i j; simp [hA' (i, j), f]
  · have hmem : π ^ n ∈ Ideal.span (Set.range f) := by rw [hn]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hsum : ∑ p, c p * A' p = 1 := by
      apply mul_left_cancel₀ hπn
      rw [mul_one]
      conv_rhs => rw [← hc]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hA' p]; ring
    by_contra hnone
    push_neg at hnone
    have : ∑ p, c p * A' p ∈ IsLocalRing.maximalIdeal R := Ideal.sum_mem _ fun p _ =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnone p.1 p.2))
    rw [hsum] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this isUnit_one

/-- **Cartan decomposition of $\mathrm{GL}_2(F)$** (the Smith normal form step in the proof of Voight 2021,
Proposition 23.4.3): every invertible $g \in \mathrm M_2(F)$ is $g = c\,U\operatorname{diag}(1, \pi^e)V$ with $c \in F^\times$,
$e \ge 0$ and $U, V \in \mathrm{GL}_2(R)$ (integral with integral inverses $U', V'$). -/
@[kb "voight2021" "Proposition 23.4.3, p. 382"]
theorem exists_eq_smul_mul_diag_mul {π : R} (hπ : Irreducible π) {g h : Matrix (Fin 2) (Fin 2) K} (hgh : g * h = 1) :
    ∃ (c : K) (e : ℕ) (U U' V V' : Matrix (Fin 2) (Fin 2) R), c ≠ 0 ∧ U * U' = 1 ∧ U' * U = 1 ∧ V * V' = 1 ∧
      V' * V = 1 ∧ g = c • mapR (U * diagR π e * V) := by
  obtain ⟨c, A, hc, rfl⟩ := exists_eq_smul_mapR (R := R) g
  have hdetg : (c • mapR (K := K) A).det ≠ 0 := by
    intro h0; have := congrArg Matrix.det hgh; rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hA0 : A ≠ 0 := by rintro rfl; apply hdetg; simp
  obtain ⟨n, A', rfl, hunit⟩ := exists_eq_pow_smul_isUnit hπ A hA0
  have hdetA' : A'.det ≠ 0 := by
    intro h0; apply hdetg
    rw [Matrix.det_smul, mapR, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_smul, h0]; simp
  obtain ⟨e, U, U', V, V', h1, h2, h3, h4, h5⟩ := exists_factor hπ A' hunit hdetA'
  refine ⟨c * algebraMap R K (π ^ n), e, U, U', V, V', ?_, h1, h2, h3, h4, ?_⟩
  · exact mul_ne_zero hc ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (pow_ne_zero _ hπ.ne_zero))
  · rw [← h5, mul_smul]
    congr 1
    ext i j
    simp only [mapR, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

end Cartan

/-! ### Proposition 23.4.3, (i) ⇒ (ii) -/

section Structure

variable [IsDiscreteValuationRing R]

/-- **Local Eichler orders are standard** (Voight 2021, Proposition 23.4.3, (i) $\Rightarrow$ (ii)): over a discrete
valuation ring $R$ with uniformizer $\pi$, every Eichler order $\mathcal O = \mathcal O_1 \cap \mathcal O_2 \subseteq \mathrm M_2(F)$
is conjugate by some $P \in \mathrm{GL}_2(F)$ to the standard Eichler order $\mathcal O_0(\pi^e)$ for some $e \ge 0$.
This is the library's named proposition `Wave3.LocalEichlerStructure R K π`, now proved.

Proof (as in the book): $\mathcal O_i = P_i\mathrm M_2(R)P_i^{-1}$ (`exists_eq_conj_matOrder`); write
$P_1^{-1}P_2 = cU\operatorname{diag}(1,\pi^e)V$ (`exists_eq_smul_mul_diag_mul`); then
$\mathcal O = P_1U\,(\mathrm M_2(R) \cap D\,\mathrm M_2(R)D^{-1})\,(P_1U)^{-1}$ with $D = \operatorname{diag}(1,\pi^e)$, and the
middle order is $\mathcal O_0(\pi^e)$ (`stdEichlerOrder_eq_inf`, Lemma 23.5.15).

*Update:* the book assumes $R$ complete ("$R$ is local", 23.2.1); completeness is not used. -/
@[kb "voight2021" "Proposition 23.4.3, p. 382"]
theorem localEichlerStructure {π : R} (hπ : Irreducible π) : LocalEichlerStructure R K π := by
  rintro _ ⟨O₁, O₂, h₁, h₂, rfl⟩
  obtain ⟨P₁, Q₁, h₁₁, h₁₂, rfl⟩ := exists_eq_conj_matOrder h₁
  obtain ⟨P₂, Q₂, h₂₁, h₂₂, rfl⟩ := exists_eq_conj_matOrder h₂
  have hgh : (Q₁ * P₂) * (Q₂ * P₁) = 1 := by
    rw [mul_assoc, ← mul_assoc P₂, h₂₁, one_mul, h₁₂]
  obtain ⟨c, e, U, U', V, V', hc, hU, hU', hV, hV', hg⟩ := exists_eq_smul_mul_diag_mul (K := K) hπ hgh
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set mU := mapR (K := K) U
  set mU' := mapR (K := K) U'
  set mV := mapR (K := K) V
  set mV' := mapR (K := K) V'
  set dP := diagP (K := K) π e
  set dQ := diagQ (K := K) π e
  have hdPQ : dP * dQ = 1 := diagP_mul_diagQ hπ0 e
  have hdQP : dQ * dP = 1 := diagQ_mul_diagP hπ0 e
  have hmUU' : mU * mU' = 1 := by rw [← mapR_mul, hU, mapR_one]
  have hmU'U : mU' * mU = 1 := by rw [← mapR_mul, hU', mapR_one]
  have hmVV' : mV * mV' = 1 := by rw [← mapR_mul, hV, mapR_one]
  have hmV'V : mV' * mV = 1 := by rw [← mapR_mul, hV', mapR_one]
  have hg' : Q₁ * P₂ = c • (mU * dP * mV) := by rw [hg, mapR_mul, mapR_mul, mapR_diagR]
  -- the two key identities
  have key₁ : dQ * (mU' * Q₁) = c • (mV * Q₂) := by
    have : dQ * mU' * (Q₁ * P₂) = c • mV := by
      rw [hg', Matrix.mul_smul]; congr 1
      calc dQ * mU' * (mU * dP * mV) = dQ * (mU' * mU) * dP * mV := by simp only [mul_assoc]
        _ = mV := by rw [hmU'U, mul_one, hdQP, one_mul]
    calc dQ * (mU' * Q₁) = dQ * mU' * (Q₁ * P₂) * Q₂ := by
          simp only [mul_assoc]; rw [h₂₁, mul_one]
      _ = c • (mV * Q₂) := by rw [this, Matrix.smul_mul]
  have key₂ : P₁ * mU * dP = c⁻¹ • (P₂ * mV') := by
    have : Q₁ * P₂ * mV' = c • (mU * dP) := by
      rw [hg', Matrix.smul_mul]; congr 1; rw [mul_assoc, hmVV', mul_one]
    have h2 : P₂ * mV' = c • (P₁ * mU * dP) := by
      calc P₂ * mV' = P₁ * (Q₁ * P₂ * mV') := by simp only [← mul_assoc]; rw [h₁₁, one_mul]
        _ = c • (P₁ * mU * dP) := by rw [this, Matrix.mul_smul, ← mul_assoc]
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hPQ : (P₁ * mU) * (mU' * Q₁) = 1 := by
    rw [mul_assoc, ← mul_assoc mU, hmUU', one_mul, h₁₁]
  have hQP : (mU' * Q₁) * (P₁ * mU) = 1 := by
    rw [mul_assoc, ← mul_assoc Q₁, h₁₂, one_mul, hmU'U]
  refine ⟨e, P₁ * mU, mU' * Q₁, hPQ, hQP, ?_⟩
  ext x
  rw [mem_map_conj hPQ hQP, stdEichlerOrder_eq_inf hπ0]
  rw [Algebra.mem_inf, Algebra.mem_inf, mem_map_conj, mem_map_conj, mem_conjMatOrder]
  apply and_congr
  · rw [show mU' * Q₁ * x * (P₁ * mU) = mU' * (Q₁ * x * P₁) * mU by simp only [mul_assoc]]
    exact (conj_mem_matOrder_iff hU' hU _).symm
  · have : dQ * (mU' * Q₁ * x * (P₁ * mU)) * dP = mV * (Q₂ * x * P₂) * mV' := by
      calc dQ * (mU' * Q₁ * x * (P₁ * mU)) * dP
          = (dQ * (mU' * Q₁)) * x * (P₁ * mU * dP) := by simp only [mul_assoc]
        _ = (c • (mV * Q₂)) * x * (c⁻¹ • (P₂ * mV')) := by rw [key₁, key₂]
        _ = mV * (Q₂ * x * P₂) * mV' := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc,
            one_smul, mul_assoc]
    rw [this]
    exact (conj_mem_matOrder_iff hV hV' _).symm

/-- Eichler orders are preserved by conjugation. -/
theorem IsEichler.map_conj {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsEichler R K O)
    {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    IsEichler R K (O.map (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R)) := by
  obtain ⟨O₁, O₂, h₁, h₂, rfl⟩ := hO
  refine ⟨_, _, h₁.map (conjAlgEquiv P Q hPQ hQP), h₂.map (conjAlgEquiv P Q hPQ hQP), ?_⟩
  ext x
  rw [Algebra.mem_inf, mem_map_conj, mem_map_conj, mem_map_conj, Algebra.mem_inf]

/-- **Eichler orders of $\mathrm M_2(F)$ are the conjugates of the standard ones** (Voight 2021, Proposition 23.4.3,
(i) $\Leftrightarrow$ (ii), and the sentence after Definition 23.4.11): over a discrete valuation ring with uniformizer $\pi$,
an $R$-subalgebra $\mathcal O \subseteq \mathrm M_2(F)$ is an Eichler order iff $\mathcal O = P\,\mathcal O_0(\pi^e)P^{-1}$ for some
$e \ge 0$ and $P \in \mathrm{GL}_2(F)$. -/
@[kb "voight2021" "Proposition 23.4.3, p. 382; Definition 23.4.11, p. 384"]
theorem isEichler_iff_exists_conj {π : R} (hπ : Irreducible π) (O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)) :
    IsEichler R K O ↔ ∃ (e : ℕ) (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      O = (stdEichlerOrder R K π e).map (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) := by
  refine ⟨localEichlerStructure hπ O, ?_⟩
  rintro ⟨e, P, Q, hPQ, hQP, rfl⟩
  exact IsEichler.map_conj (isEichler_stdEichlerOrder hπ.ne_zero e) hPQ hQP

end Structure

/-! ### Proposition 23.4.3, (iii) ⇒ (ii), and Corollary 23.4.10 -/

section Diagonal

/-- The diagonal matrix $\operatorname{diag}(r, s)$ over $R$, viewed in $\mathrm M_2(F)$. -/
abbrev diagK (r s : R) : Matrix (Fin 2) (Fin 2) K := mapR !![r, 0; 0, s]

/-- The entries of an order containing the diagonal: $I_{ij} = \{c \in F : cE_{ij} \in \mathcal O\}$. -/
def entryIdeal (O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)) (i j : Fin 2) : Submodule R K where
  carrier := {c | Matrix.single i j c ∈ O}
  add_mem' {c d} hc hd := by
    show Matrix.single i j (c + d) ∈ O
    rw [Matrix.single_add]; exact O.add_mem hc hd
  zero_mem' := by
    show Matrix.single i j (0 : K) ∈ O
    rw [Matrix.single_zero]; exact O.zero_mem
  smul_mem' r c hc := by
    show Matrix.single i j (r • c) ∈ O
    rw [← Matrix.smul_single]; exact O.smul_mem hc r

theorem mem_entryIdeal {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} {i j : Fin 2} {c : K} :
    c ∈ entryIdeal O i j ↔ Matrix.single i j c ∈ O := Iff.rfl

theorem single_eq_diag_mul_mul_diag (x : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    Matrix.single i j (x i j) = Matrix.single i i 1 * x * Matrix.single j j 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp

theorem single_one_mem {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hD : ∀ r s : R, diagK r s ∈ O) (i : Fin 2) :
    Matrix.single i i (1 : K) ∈ O := by
  fin_cases i
  · convert hD 1 0 using 1; ext k l; fin_cases k <;> fin_cases l <;> simp
  · convert hD 0 1 using 1; ext k l; fin_cases k <;> fin_cases l <;> simp

/-- An order containing the diagonal is the sum of its four corners: $x \in \mathcal O$ iff every $x_{ij}E_{ij} \in \mathcal O$. -/
theorem mem_iff_forall_single {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hD : ∀ r s : R, diagK r s ∈ O)
    (x : Matrix (Fin 2) (Fin 2) K) : x ∈ O ↔ ∀ i j, x i j ∈ entryIdeal O i j := by
  constructor
  · intro hx i j
    rw [mem_entryIdeal, single_eq_diag_mul_mul_diag]
    exact O.mul_mem (O.mul_mem (single_one_mem hD i) hx) (single_one_mem hD j)
  · intro h
    rw [Matrix.matrix_eq_sum_single x]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => h i j

/-- The diagonal corners of an order containing the diagonal are $R$. -/
theorem mem_entryIdeal_diag_iff [IsIntegrallyClosed R] {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O)
    (hD : ∀ r s : R, diagK r s ∈ O) (i : Fin 2) (c : K) : c ∈ entryIdeal O i i ↔ IsInteger R c := by
  constructor
  · intro h
    have := (isInteger_trace_det hO h).1
    simpa [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply] using this
  · rintro ⟨r, rfl⟩
    rw [mem_entryIdeal]
    fin_cases i
    · convert hD r 0 using 1; ext k l; fin_cases k <;> fin_cases l <;> simp
    · convert hD 0 r using 1; ext k l; fin_cases k <;> fin_cases l <;> simp

theorem entryIdeal_mul_mem {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} {i j k : Fin 2} {c d : K}
    (hc : c ∈ entryIdeal O i j) (hd : d ∈ entryIdeal O j k) : c * d ∈ entryIdeal O i k := by
  rw [mem_entryIdeal] at *
  have := O.mul_mem hc hd
  rwa [Matrix.single_mul_single_same] at this

/-- The off-diagonal corner $I_{ij}$ is the image of $\mathcal O$ under $x \mapsto x_{ij}$, hence finitely generated. -/
theorem entryIdeal_fg {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O)
    (hD : ∀ r s : R, diagK r s ∈ O) (i j : Fin 2) : (entryIdeal O i j).FG := by
  have : entryIdeal O i j = (Subalgebra.toSubmodule O).map (Matrix.entryLinearMap R K i j) := by
    ext c
    constructor
    · intro hc; exact ⟨_, hc, by show (Matrix.single i j c) i j = c; simp⟩
    · rintro ⟨x, hx, rfl⟩; exact ((mem_iff_forall_single hD x).1 hx) i j
  rw [this]; exact hO.fg.map _

/-- The corners of an order are nonzero ($\mathcal O$ spans $\mathrm M_2(F)$). -/
theorem entryIdeal_ne_bot {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsOrder R K O)
    (hD : ∀ r s : R, diagK r s ∈ O) (i j : Fin 2) : ∃ c ∈ entryIdeal O i j, c ≠ 0 := by
  by_contra h
  push_neg at h
  have hle : Submodule.span K (O : Set (Matrix (Fin 2) (Fin 2) K)) ≤ LinearMap.ker (Matrix.entryLinearMap K K i j) := by
    rw [Submodule.span_le]
    intro x hx
    exact h _ (((mem_iff_forall_single hD x).1 hx) i j)
  rw [hO.span] at hle
  have := hle (Submodule.mem_top (x := Matrix.single i j 1))
  change (Matrix.single i j (1 : K)) i j = 0 at this
  simp at this

/-- A finitely generated nonzero $R$-submodule of $F$ is $Ru$ for some $u \ne 0$ ($R$ a principal ideal domain). -/
theorem exists_eq_span_of_fg [IsPrincipalIdealRing R] {I : Submodule R K} (hI : I.FG) (h0 : ∃ c ∈ I, c ≠ 0) :
    ∃ u : K, u ≠ 0 ∧ I = Submodule.span R {u} := by
  set J : FractionalIdeal (nonZeroDivisors R) K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hJ : (J : Submodule R K).IsPrincipal := inferInstance
  obtain ⟨u, hu⟩ := hJ
  refine ⟨u, ?_, hu⟩
  rintro rfl
  obtain ⟨c, hc, hc0⟩ := h0
  have : c ∈ (J : Submodule R K) := hc
  rw [hu, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
  exact hc0 this

variable [IsDiscreteValuationRing R]

/-- **An order containing the diagonal is standard** (Voight 2021, Proposition 23.4.3, (iii) $\Rightarrow$ (ii), in the
normalized form of (23.4.7)-(23.4.8)): over a discrete valuation ring with uniformizer $\pi$, an order
$\mathcal O \subseteq \mathrm M_2(F)$ containing $\{\operatorname{diag}(r, s) : r, s \in R\}$ is $P\mathcal O_0(\pi^e)P^{-1}$ for some
$e \ge 0$ and a diagonal $P = \operatorname{diag}(u, 1)$, $u \in F^\times$. -/
@[kb "voight2021" "Proposition 23.4.3, p. 382"]
theorem exists_eq_conj_of_diag_le {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsOrder R K O) (hD : ∀ r s : R, diagK r s ∈ O) :
    ∃ (e : ℕ) (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      O = (stdEichlerOrder R K π e).map (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) := by
  obtain ⟨u, hu0, hu⟩ := exists_eq_span_of_fg (entryIdeal_fg hO hD 0 1) (entryIdeal_ne_bot hO hD 0 1)
  obtain ⟨w, hw0, hw⟩ := exists_eq_span_of_fg (entryIdeal_fg hO hD 1 0) (entryIdeal_ne_bot hO hD 1 0)
  have hwu : IsInteger R (w * u) := by
    rw [← mem_entryIdeal_diag_iff hO hD 1]
    exact entryIdeal_mul_mem (hw ▸ Submodule.mem_span_singleton_self w)
      (hu ▸ Submodule.mem_span_singleton_self u)
  obtain ⟨N, hN⟩ := hwu
  have hN0 : N ≠ 0 := by
    rintro rfl; rw [map_zero] at hN; exact mul_ne_zero hw0 hu0 hN.symm
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN0 hπ
  set P : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![u, 1]
  set Q : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![u⁻¹, 1]
  have hPQ : P * Q = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp [hu0]
  have hQP : Q * P = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp [hu0]
  refine ⟨e, P, Q, hPQ, hQP, ?_⟩
  ext x
  rw [mem_map_conj hPQ hQP, mem_iff_forall_single hD, mem_stdEichlerOrder]
  have hQxP : ∀ i j, (Q * x * P) i j = ![u⁻¹, 1] i * x i j * ![u, 1] j := fun i j => by
    simp [P, Q, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have h00 : (Q * x * P) 0 0 = x 0 0 := by rw [hQxP]; simp; field_simp
  have h01 : (Q * x * P) 0 1 = u⁻¹ * x 0 1 := by rw [hQxP]; simp
  have h10 : (Q * x * P) 1 0 = x 1 0 * u := by rw [hQxP]; simp
  have h11 : (Q * x * P) 1 1 = x 1 1 := by rw [hQxP]; simp
  have E1 : (∃ a : R, a • u = x 0 1) ↔ IsInteger R (u⁻¹ * x 0 1) := by
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [← ha, Algebra.smul_def]; field_simp⟩
    · rintro ⟨r, hr⟩; exact ⟨r, by rw [Algebra.smul_def, hr]; field_simp⟩
  have E2 : (∃ a : R, a • w = x 1 0) ↔ ∃ r : R, x 1 0 * u = algebraMap R K (π ^ e * r) := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a * v, ?_⟩
      rw [← ha, Algebra.smul_def, mul_assoc, ← hN, hv]; simp only [map_mul, map_pow]; ring
    · rintro ⟨r, hr⟩
      refine ⟨r * (v⁻¹ : Rˣ), ?_⟩
      have hx : x 1 0 = algebraMap R K (π ^ e * r) * u⁻¹ := by rw [← hr]; field_simp
      have hw' : w = algebraMap R K N * u⁻¹ := by rw [hN]; field_simp
      rw [Algebra.smul_def, hx, hw', hv]
      simp only [map_mul, map_pow]
      have : (algebraMap R K (v⁻¹ : Rˣ)) * algebraMap R K (v : R) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (algebraMap R K π ^ e * algebraMap R K r * u⁻¹) * this
  have E3 : (∃ r : R, x 1 0 * u = algebraMap R K (π ^ e * r)) → IsInteger R (x 1 0 * u) := by
    rintro ⟨r, hr⟩; exact ⟨π ^ e * r, hr.symm⟩
  simp only [Fin.forall_fin_two, h00, h01, h10, h11]
  rw [mem_entryIdeal_diag_iff hO hD 0, mem_entryIdeal_diag_iff hO hD 1, hu, hw, Submodule.mem_span_singleton,
    Submodule.mem_span_singleton, E1, E2]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, E3 h3, h4⟩, h3⟩
  · rintro ⟨⟨⟨h1, h2⟩, -, h4⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- **Proposition 23.4.3, (iii) $\Rightarrow$ (i)** (Voight 2021): an order $\mathcal O \subseteq \mathrm M_2(F)$ containing a
$\mathrm{GL}_2(F)$-conjugate $P\{\operatorname{diag}(r,s)\}P^{-1}$ of the diagonal order is an Eichler order. -/
@[kb "voight2021" "Proposition 23.4.3, p. 382"]
theorem isEichler_of_conj_diag_le {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsOrder R K O) {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hD : ∀ r s : R, P * diagK r s * Q ∈ O) : IsEichler R K O := by
  set O' := O.map (((conjAlgEquiv Q P hQP hPQ) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R)
  have hO' : IsOrder R K O' := hO.map (conjAlgEquiv Q P hQP hPQ)
  have hD' : ∀ r s : R, diagK r s ∈ O' := fun r s => by
    rw [mem_map_conj]; exact hD r s
  obtain ⟨e, P', Q', h1, h2, hO'eq⟩ := exists_eq_conj_of_diag_le hπ hO' hD'
  have hE : IsEichler R K O' := hO'eq ▸ IsEichler.map_conj (isEichler_stdEichlerOrder hπ.ne_zero e) h1 h2
  have : O = O'.map (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) := by
    ext x; rw [mem_map_conj, mem_map_conj]
    rw [show P * (Q * x * P) * Q = x by
      simp only [← mul_assoc, hPQ, one_mul]; rw [mul_assoc, hPQ, mul_one]]
  rw [this]; exact IsEichler.map_conj hE hPQ hQP

/-- **Superorders of Eichler orders are Eichler** (Voight 2021, Corollary 23.4.10, local case): over a discrete valuation
ring, an order $\mathcal O' \subseteq \mathrm M_2(F)$ containing an Eichler order $\mathcal O$ is an Eichler order. -/
@[kb "voight2021" "Corollary 23.4.10, p. 383"]
theorem IsEichler.of_le {π : R} (hπ : Irreducible π) {O O' : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsEichler R K O) (hO' : IsOrder R K O') (hle : O ≤ O') : IsEichler R K O' := by
  obtain ⟨e, P, Q, hPQ, hQP, rfl⟩ := localEichlerStructure hπ O hO
  refine isEichler_of_conj_diag_le hπ hO' hPQ hQP fun r s => hle ?_
  rw [mem_map_conj, mem_stdEichlerOrder]
  rw [show Q * (P * diagK r s * Q) * P = diagK r s by
    simp only [← mul_assoc, hQP, one_mul]; rw [mul_assoc, hQP, mul_one]]
  refine ⟨fun i j => ⟨!![r, 0; 0, s] i j, rfl⟩, 0, ?_⟩
  simp

end Diagonal

end QuadFormsKB.Voight.Wave4
