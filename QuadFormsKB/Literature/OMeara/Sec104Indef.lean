/-
# O'Meara Example 104:12, first part: the space of an indefinite unimodular $\mathbb Z$-lattice

**Layer:** integral forms `QuadForm ℤ n` and their rational spaces `Q.map (Int.castRingHom ℚ)`, as in
`Literature/OMeara/Sec106A.lean`; the signature is given by an isometry over $\mathbb R$.

**Proves** the first part of Example 104:12 (O'Meara 1973, §104, p. 321, `omeara104_12_space`): if $L$ is a
unimodular $\mathbb Z$-lattice ($\det H_Q = \pm 2^n$, i.e. O'Meara's matrix $G = \tfrac12H_Q$ has determinant
$\pm 1$) on a space $V$ with $V_\infty \cong \langle 1\rangle^p \perp \langle -1\rangle^q$, then
$V \cong \langle 1\rangle^p \perp \langle -1\rangle^q$ over $\mathbb Q$ (by Hilbert reciprocity, 63:20 and the
Hasse–Minkowski Theorem, as O'Meara indicates). The second part of 104:12, $L \cong \langle 1\rangle^p \perp
\langle -1\rangle^q$ when $\mathfrak nL = \mathbb Z$ and $V_\infty$ is isotropic, needs the dyadic theory (93:29) and is not
formalized.

*Generalization.* Neither $\mathfrak nL = \mathbb Z$, nor isotropy of $V_\infty$, nor classical integrality is needed for
the first part.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.LocalDensity.JordanForm

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- The diagonal form $\langle 1\rangle^p \perp \langle -1\rangle^q$ in $n = p + q$ variables (the first $p$ entries
$1$, the others $-1$), over a commutative ring $R$. -/
def signDiag (R : Type*) [CommRing R] {n : ℕ} (p : ℕ) : QuadForm R n :=
  QuadForm.diag fun i => if i.val < p then 1 else -1

private lemma map_hessian_aux {n : ℕ} (Q : QuadForm ℤ n) :
    (Q.map (Int.castRingHom ℚ)).hessian = Q.hessian.map (Int.castRingHom ℚ) := by
  simp [QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map]

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

private lemma diag_hessian_det_aux {K : Type*} [Field K] {n : ℕ} (b : Fin n → K) :
    (QuadForm.diag b).hessian.det = 2 ^ n * ∏ i, b i := by
  simp only [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add,
    Matrix.det_diagonal]
  simp [← two_mul, Finset.prod_mul_distrib]

private lemma hasse_unit_aux (p : Nat.Primes) (hp2 : p.1 ≠ 2) {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, ¬ (p.1 : ℤ) ∣ a i) :
    (RatPlace.finite p).hasseSerre (fun i => (a i : ℚ)) = 1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  unfold RatPlace.hasseSerre
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · have := ConwaySloane.hilbert_odd_int p.1 hp2 0 0 (a i) (a j) (a i : ℚ) (a j : ℚ) (ha i) (ha j)
      (by simp) (by simp)
    simp only [mul_zero, zero_mul, pow_zero, mul_one] at this
    exact this
  · rfl

/-- If two diagonal forms have Hasse invariant $1$ at every odd prime and agree at $\infty$, they agree at $2$
(product formula). -/
private lemma hasse_two_eq_aux {n : ℕ} (b s : Fin n → ℚ) (hb : ∀ i, b i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (hinf : RatPlace.infinite.hasseSerre b = RatPlace.infinite.hasseSerre s)
    (hb1 : ∀ p : Nat.Primes, p.1 ≠ 2 → (RatPlace.finite p).hasseSerre b = 1)
    (hs1 : ∀ p : Nat.Primes, p.1 ≠ 2 → (RatPlace.finite p).hasseSerre s = 1) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre b =
      (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre s := by
  classical
  have key : ∀ c : Fin n → ℚ, (∀ i, c i ≠ 0) →
      (∀ p : Nat.Primes, p.1 ≠ 2 → (RatPlace.finite p).hasseSerre c = 1) →
      RatPlace.infinite.hasseSerre c * (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre c = 1 := by
    intro c hc h1
    have h := (hasseSerre_product_formula c hc).2
    rw [finprod_eq_prod_of_mulSupport_subset
      (s := {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩}) _ ?_] at h
    · rwa [Finset.prod_pair (by simp)] at h
    · intro v hv
      simp only [Function.mem_mulSupport] at hv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hne
      push Not at hne
      cases v with
      | infinite => exact hne.1 rfl
      | finite p =>
        exact hv (h1 p (fun h => hne.2 (congrArg RatPlace.finite (Subtype.ext h))))
  have hkb := key b hb hb1
  have hks := key s hs hs1
  rw [hinf] at hkb
  have hne : RatPlace.infinite.hasseSerre s ≠ 0 := by
    rw [hasseSerre_infinite_eq s hs]; simp
  exact mul_left_cancel₀ hne (hkb.trans hks.symm)

/-- **Example 104:12, first part** (O'Meara 1973, §104, p. 321): a form $Q$ over $\mathbb Z$ with
$\det H_Q = \pm 2^n$ whose real space is $\langle 1\rangle^p \perp \langle -1\rangle^{n-p}$ is equivalent over
$\mathbb Q$ to $\langle 1\rangle^p \perp \langle -1\rangle^{n-p}$. -/
@[kb "omeara1963" "§104, 104:12, p. 321 (first part: V ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨−1⟩; generalization)"]
theorem omeara104_12_space {n : ℕ} (Q : QuadForm ℤ n) (p : ℕ)
    (hdet : Q.hessian.det = 2 ^ n ∨ Q.hessian.det = -2 ^ n)
    (hreal : (Q.map (Int.castRingHom ℚ)).IsometricIn ℝ (signDiag ℚ p)) :
    (Q.map (Int.castRingHom ℚ)).IsometricIn ℚ (signDiag ℚ p) := by
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
  have hPd : P.det ≠ 0 := hPu.ne_zero
  -- the sign form as a rational diagonal form with entries ±1
  obtain ⟨sZ, hsZdef⟩ : ∃ sZ : Fin n → ℤ, sZ = fun i => if i.val < p then 1 else -1 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : Fin n → ℚ, s = fun i => (sZ i : ℚ) := ⟨_, rfl⟩
  have hsZ_pm : ∀ i, sZ i = 1 ∨ sZ i = -1 := by
    intro i
    rw [hsZdef]
    dsimp only
    split_ifs <;> simp
  have hs_pm : ∀ i, s i = 1 ∨ s i = -1 := by
    intro i
    rw [hsdef]
    rcases hsZ_pm i with h | h <;> simp [h]
  have hs0 : ∀ i, s i ≠ 0 := fun i => by rcases hs_pm i with h | h <;> rw [h] <;> norm_num
  have hS : (signDiag ℚ p : QuadForm ℚ n) = QuadForm.diag s := by
    unfold signDiag
    congr 1
    funext i
    rw [hsdef, hsZdef]
    dsimp only
    split_ifs <;> simp
  rw [hS] at hreal ⊢
  have hprods : ∏ i, s i = 1 ∨ ∏ i, s i = -1 := by
    have : (∏ i, s i) * (∏ i, s i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => by rcases hs_pm i with h | h <;> rw [h] <;> norm_num
    exact mul_self_eq_one_iff.mp this
  -- the real isometry
  have hbR : (QuadForm.diag b).IsometricIn ℝ (QuadForm.diag s) :=
    QuadForm.isometricIn_trans ℝ (QuadForm.isometricIn_symm ℝ (FieldGen.isometricIn_of_base ℝ hRb'))
      hreal
  -- the discriminants
  have e := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hP)
  rw [det_mul, det_mul, det_transpose, hdetR, diag_hessian_det_aux] at e
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  have h2nR : (0 : ℝ) < 2 ^ n := by positivity
  have hBS : ∏ i, b i = (∏ i, s i) * P.det ^ 2 := by
    obtain ⟨T, hTu, hT⟩ := hbR
    have hTd : T.det ≠ 0 := hTu.ne_zero
    have hevR : ∀ (c : Fin n → ℚ) (x : Fin n → ℝ), (QuadForm.diag c).evalIn ℝ x =
        (QuadForm.diag (fun i => (c i : ℝ))).evalIn ℝ x := by
      intro c x
      rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
      simp
    have hT' := PadicClass.transpose_mul_hessian_mul (K := ℝ)
      (Q := QuadForm.diag (fun i => (b i : ℝ))) (Q' := QuadForm.diag (fun i => (s i : ℝ)))
      (P := T) (fun x => by rw [← hevR, ← hevR]; exact hT x)
    have eT := congrArg Matrix.det hT'
    rw [det_mul, det_mul, det_transpose, diag_hessian_det_aux, diag_hessian_det_aux] at eT
    have c1 : ∏ i, (b i : ℝ) = ((∏ i, b i : ℚ) : ℝ) := by push_cast; rfl
    have c2 : ∏ i, (s i : ℝ) = ((∏ i, s i : ℚ) : ℝ) := by push_cast; rfl
    rw [c1, c2] at eT
    have hTT : 0 ≤ (T.det * T.det) := mul_self_nonneg _
    obtain ⟨d, hd⟩ : ∃ d : ℚ, d = P.det := ⟨_, rfl⟩
    rw [← hd] at e ⊢
    rcases hdetQ with h | h <;> rcases hprods with h' | h'
    · rw [h] at e
      have hB : ∏ i, b i = d ^ 2 := by
        apply mul_left_cancel₀ h2n.ne'; linarith
      rw [h', hB]; ring
    · exfalso
      rw [h] at e
      have hB : ∏ i, b i = d ^ 2 := by
        apply mul_left_cancel₀ h2n.ne'; linarith
      rw [hB, h'] at eT
      push_cast at eT
      nlinarith [mul_nonneg h2nR.le (mul_nonneg hTT (sq_nonneg (d : ℝ)))]
    · exfalso
      rw [h] at e
      have hB : ∏ i, b i = -d ^ 2 := by
        apply mul_left_cancel₀ h2n.ne'; linarith
      rw [hB, h'] at eT
      push_cast at eT
      nlinarith [mul_nonneg h2nR.le (mul_nonneg hTT (sq_nonneg (d : ℝ)))]
    · rw [h] at e
      have hB : ∏ i, b i = -d ^ 2 := by
        apply mul_left_cancel₀ h2n.ne'; linarith
      rw [h', hB]; ring
  -- Hasse invariants at odd primes
  have hnd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ (ℓ : ℤ) ∣ Q.hessian.det := by
    intro ℓ hℓ hne h
    have h2 : (ℓ : ℤ) ∣ 2 ^ n := by
      rcases hdet with hd | hd
      · rw [hd] at h; exact h
      · rw [hd] at h; exact dvd_neg.mp h
    have h' := (Nat.prime_iff_prime_int.mp hℓ).dvd_of_dvd_pow h2
    have : ℓ ∣ 2 := by exact_mod_cast h'
    exact hne ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  have hodd_b : ∀ q : Nat.Primes, q.1 ≠ 2 → (RatPlace.finite q).hasseSerre b = 1 := by
    intro q hq2
    have : Fact q.1.Prime := ⟨q.2⟩
    obtain ⟨a, ha, hRa⟩ := exists_diag_rat_aux Q q.1 hq2 (hnd q.1 q.2 hq2)
    have ha0 : ∀ i, (a i : ℚ) ≠ 0 := fun i h =>
      ha i (by have : a i = 0 := by exact_mod_cast h
               rw [this]; exact dvd_zero _)
    have hba : (QuadForm.diag b).IsometricIn ℚ (QuadForm.diag fun i => (a i : ℚ)) :=
      QuadForm.isometricIn_trans ℚ (QuadForm.isometricIn_symm ℚ hRb') hRa
    have hinv := hasseInvariant_isometric q.1 b (fun i => (a i : ℚ)) hb ha0
      (FieldGen.isometricIn_of_base ℚ_[q.1] hba)
    rw [RatPlace.hasseSerre_finite, hinv, ← RatPlace.hasseSerre_finite]
    exact hasse_unit_aux q hq2 a ha
  have hodd_s : ∀ q : Nat.Primes, q.1 ≠ 2 → (RatPlace.finite q).hasseSerre s = 1 := by
    intro q hq2
    have hsnd : ∀ i, ¬ (q.1 : ℤ) ∣ sZ i := by
      intro i h
      have h1 : (q.1 : ℤ) ∣ 1 := by
        rcases hsZ_pm i with h' | h' <;> rw [h'] at h
        · exact h
        · exact dvd_neg.mp h
      have h2 : q.1 ∣ 1 := by exact_mod_cast h1
      exact q.2.one_lt.ne' (Nat.dvd_one.mp h2)
    have := hasse_unit_aux q hq2 sZ hsnd
    rw [← hsdef] at this
    exact this
  have hinf : RatPlace.infinite.hasseSerre b = RatPlace.infinite.hasseSerre s :=
    RatPlace.hasseSerre_isometric RatPlace.infinite b s hb hs0 hbR
  have h2eq := hasse_two_eq_aux b s hb hs0 hinf hodd_b hodd_s
  have hbs : (QuadForm.diag b).IsometricIn ℚ (QuadForm.diag s) := by
    rw [isometric_iff_everywhere _ _ (QuadForm.nondegenerate_diag hb)
      (QuadForm.nondegenerate_diag hs0)]
    intro v
    cases v with
    | infinite => exact hbR
    | finite q =>
      have : Fact q.1.Prime := ⟨q.2⟩
      show (QuadForm.diag b).IsometricIn ℚ_[q.1] (QuadForm.diag s)
      rw [isometric_padic_iff q.1 b s hb hs0]
      refine ⟨⟨algebraMap ℚ ℚ_[q.1] P.det, (map_ne_zero _).mpr hPd, ?_⟩, ?_⟩
      · rw [hBS, map_mul, map_pow]; ring
      · have hq : (RatPlace.finite q).hasseSerre b = (RatPlace.finite q).hasseSerre s := by
          by_cases hq2 : q.1 = 2
          · have : q = ⟨2, Nat.prime_two⟩ := Subtype.ext hq2
            rw [this]; exact h2eq
          · rw [hodd_b q hq2, hodd_s q hq2]
        rwa [RatPlace.hasseSerre_finite, RatPlace.hasseSerre_finite] at hq
  exact QuadForm.isometricIn_trans ℚ hRb' hbs

end QuadFormsKB.Lattices
