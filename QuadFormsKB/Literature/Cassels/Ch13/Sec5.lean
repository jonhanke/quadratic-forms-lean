/-
# Cassels, Chapter 13, §5: isotropic ternary forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §5, *Isotropic ternary forms*, pp. 301–303: the
automorphs of $f_0(\vec{x}) = x_0x_2 - x_1^2$ come from $2 \times 2$ matrices acting on binary forms (Lemmas 5.1, 5.2),
and the orbits of representations of $m$ by $f_0$ correspond to proper classes of binary forms of determinant $m$
(Lemma 5.3, its Corollary, Lemma 5.4).

**Conventions.** Cassels' variables $x_1, x_2, x_3$ are $x_0, x_1, x_2$ here, so (5.1) reads
$f_0(\vec{x}) = x_0x_2 - x_1^2$, the determinant of the binary form (5.2)
$$\phi_{\vec{x}}(\vec{u}) = x_0u_0^2 + 2x_1u_0u_1 + x_2u_1^2.$$
A $2 \times 2$ matrix $S = \begin{pmatrix}\alpha & \beta\\ \gamma & \delta\end{pmatrix}$ (5.3) with
$\Delta = \alpha\delta - \beta\gamma \ne 0$ (5.5) gives the matrix $T(S)$ of (5.6) (`spinMat`). Binary forms
$\phi_{\vec{b}}$ are the classically integral forms `Siegel.ofGram !![b 0, b 1; b 1, b 2]`. Proper equivalence of
integral forms is `Siegel.ProperIntEquiv`.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight

open Matrix

namespace QuadFormsKB.Reduction

/-- **The form $f_0 = x_0x_2 - x_1^2$** (Cassels, Ch. 13, §5, (5.1), p. 301), the determinant of the binary form
$\phi_{\vec{x}}$ of (5.2). -/
@[kb "cassels1978" "Ch. 13, §5, (5.1)–(5.2), p. 301 (f₀ as an integral form; the polynomial function is Cassels.Ch13.f₀)"]
def fZero : IntQF 3 := QuadForm.ofUpper ![![0, 0, 1], ![0, -1, 0], ![0, 0, 0]]

/-- $f_0(\vec{x}) = x_0x_2 - x_1^2$, over any commutative ring. -/
theorem evalIn_fZero {K : Type*} [CommRing K] (x : Fin 3 → K) :
    fZero.evalIn K x = x 0 * x 2 - x 1 ^ 2 := by
  simp [fZero, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three]
  ring

/-- **The matrix $T(S)$ of (5.6)** (Cassels, Ch. 13, §5, p. 301): for
$S = \begin{pmatrix}\alpha & \beta\\ \gamma & \delta\end{pmatrix}$ with $\Delta = \det S$,
$$T(S) = \Delta^{-1}\begin{pmatrix}\alpha^2 & 2\alpha\gamma & \gamma^2\\ \alpha\beta & \alpha\delta + \beta\gamma &
\gamma\delta\\ \beta^2 & 2\beta\delta & \delta^2\end{pmatrix},$$
so that $\phi_{\vec{x}}(S\vec{u}) = \Delta\,\phi_{T(S)\vec{x}}(\vec{u})$. (The display (5.6) is partly garbled in the
machine-read text; the matrix is determined by $\phi_{\vec{x}}(S\vec{u})$.) -/
@[kb "cassels1978" "Ch. 13, §5, (5.3)–(5.6), p. 301"]
def spinMat {K : Type*} [Field K] (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  (S.det)⁻¹ • !![S 0 0 ^ 2, 2 * S 0 0 * S 1 0, S 1 0 ^ 2;
    S 0 0 * S 0 1, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 1 0 * S 1 1;
    S 0 1 ^ 2, 2 * S 0 1 * S 1 1, S 1 1 ^ 2]

/-- `spinMat` on an explicit matrix. -/
theorem spinMat_eq (a b c d : ℚ) :
    spinMat !![a, b; c, d] = (a * d - b * c)⁻¹ • !![a ^ 2, 2 * a * c, c ^ 2; a * b, a * d + b * c, c * d;
      b ^ 2, 2 * b * d, d ^ 2] := by
  simp [spinMat, Matrix.det_fin_two_of]

theorem spinMat_f0 (a b c d : ℚ) (h : a * d - b * c ≠ 0) (x : Fin 3 → ℚ) :
    fZero.evalIn ℚ (spinMat !![a, b; c, d] *ᵥ x) = fZero.evalIn ℚ x := by
  rw [spinMat_eq, evalIn_fZero, evalIn_fZero]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

theorem spinMat_det (a b c d : ℚ) (h : a * d - b * c ≠ 0) : (spinMat !![a, b; c, d]).det = 1 := by
  rw [spinMat_eq, Matrix.det_smul, Matrix.det_fin_three]
  simp
  field_simp
  ring

theorem spinMat_mul (a b c d a' b' c' d' : ℚ) (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0) :
    spinMat (!![a, b; c, d] * !![a', b'; c', d']) = spinMat !![a', b'; c', d'] * spinMat !![a, b; c, d] := by
  rw [Matrix.mul_fin_two, spinMat_eq, spinMat_eq, spinMat_eq]
  have h2 : (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') =
        (a * d - b * c) * (a' * d' - b' * c') := by ring
  rw [h2, mul_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

theorem spinMat_eq_one (a b c d : ℚ) (h : a * d - b * c ≠ 0) :
    spinMat !![a, b; c, d] = 1 ↔ ∃ e : ℚ, !![a, b; c, d] = e • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  constructor
  · intro hT
    rw [spinMat_eq] at hT
    have e02 := congrFun (congrFun hT 0) 2
    have e20 := congrFun (congrFun hT 2) 0
    simp [h] at e02 e20
    subst e02 e20
    have e00 := congrFun (congrFun hT 0) 0
    simp at e00
    have ha : a ≠ 0 := by rintro rfl; simp at h
    have hd : d ≠ 0 := by rintro rfl; simp at h
    refine ⟨a, ?_⟩
    have : a = d := by field_simp at e00; nlinarith [e00, ha, hd]
    subst this
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rintro ⟨e, he⟩
    have hb : b = 0 := by simpa using congrFun (congrFun he 0) 1
    have hc : c = 0 := by simpa using congrFun (congrFun he 1) 0
    have ha : a = e := by simpa using congrFun (congrFun he 0) 0
    have hd : d = e := by simpa using congrFun (congrFun he 1) 1
    have hne : e ≠ 0 := by rw [ha, hd, hb, hc] at h; rintro rfl; simp at h
    rw [spinMat_eq, ha, hd, hb, hc]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- Rational isotropic vectors of $f_0$ are $\lambda(p^2, pq, q^2)$. -/
theorem iso_param (v : Fin 3 → ℚ) (h : v 0 * v 2 = v 1 ^ 2) (hv : v ≠ 0) :
    ∃ l p q : ℚ, l ≠ 0 ∧ v 0 = l * p ^ 2 ∧ v 1 = l * p * q ∧ v 2 = l * q ^ 2 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 = 0 := by rw [h0] at h; simpa using h.symm
    have h2 : v 2 ≠ 0 := by
      intro h2; apply hv; ext i; fin_cases i <;> simp [h0, h1, h2]
    exact ⟨v 2, 0, 1, h2, by simp [h0], by simp [h1], by simp⟩
  · refine ⟨v 0, 1, v 1 / v 0, h0, by simp, by field_simp, ?_⟩
    field_simp
    linarith

/-- A proper automorph fixing $e_0$ and $e_2$ is the identity. -/
theorem eq_one_of_cols (U : Matrix (Fin 3) (Fin 3) ℚ)
    (hU : ∀ x : Fin 3 → ℚ, fZero.evalIn ℚ (U *ᵥ x) = fZero.evalIn ℚ x) (hdet : U.det = 1)
    (h00 : U 0 0 = 1) (h10 : U 1 0 = 0) (h20 : U 2 0 = 0) (h02 : U 0 2 = 0) (h12 : U 1 2 = 0) (h22 : U 2 2 = 1) :
    U = 1 := by
  have a := hU ![0, 1, 0]
  have b := hU ![1, 1, 0]
  have c := hU ![0, 1, 1]
  simp [evalIn_fZero, mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h20, h02, h12, h22] at a b c
  rw [Matrix.det_fin_three] at hdet
  simp [h00, h10, h20, h02, h12, h22] at hdet
  have v2 : U 2 1 = 0 := by nlinarith
  have v0 : U 0 1 = 0 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h02, h12, h22, v2, v0, hdet]

/-- **Lemma 5.1** (Cassels, Ch. 13, §5, p. 301): for $S \in \mathrm{GL}_2(\mathbb{Q})$, $T(S)$ is a rational proper
automorph of $f_0$ ($\det T(S) = 1$, (5.7)); every rational proper automorph of $f_0$ is a $T(S)$; and $T(S) = I$
iff $S$ is a scalar multiple of $I$. *Erratum*: Cassels calls $S \mapsto T(S)$ a group
homomorphism; with (5.6) it reverses products, $T(S_1S_2) = T(S_2)T(S_1)$ (an anti-homomorphism; $S \mapsto T(S^{\mathsf
T})$ is a homomorphism), as $\phi_{\vec{x}}(S_1S_2\vec{u})$ shows.

*Note*: Lemma 5.1 itself is tagged at `Cassels.Ch13.lemma_5_1` (over every field, for $S \mapsto T(S^{\mathsf T})$);
this declaration keeps the tag for Cassels' literal map and the erratum. -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.1, (5.7), p. 301"]
theorem spinMat_rat (S S' : Matrix (Fin 2) (Fin 2) ℚ) (hS : S.det ≠ 0) (hS' : S'.det ≠ 0) :
    (∀ x : Fin 3 → ℚ, fZero.evalIn ℚ (spinMat S *ᵥ x) = fZero.evalIn ℚ x) ∧ (spinMat S).det = 1 ∧
      spinMat (S * S') = spinMat S' * spinMat S ∧ (spinMat S = 1 ↔ ∃ c : ℚ, S = c • 1) := by
  rw [Matrix.eta_fin_two S] at hS ⊢
  rw [Matrix.eta_fin_two S'] at hS' ⊢
  rw [Matrix.det_fin_two_of] at hS hS'
  refine ⟨fun x => spinMat_f0 _ _ _ _ hS x, ?_, spinMat_mul _ _ _ _ _ _ _ _ hS hS',
    spinMat_eq_one _ _ _ _ hS⟩
  exact spinMat_det _ _ _ _ hS

/-- **Lemma 5.1, surjectivity** (Cassels, Ch. 13, §5, pp. 301–302): every rational proper automorph $T$ of $f_0$
($f_0(T\vec{x}) = f_0(\vec{x})$, $\det T = 1$) is $T(S)$ for some $S \in \mathrm{GL}_2(\mathbb{Q})$.

*Note*: Superseded by `Cassels.Ch13.lemma_5_1` (over every field; its map `spinRep S` is `spinMat` of
$S^{\mathsf T}$). -/
theorem exists_spinMat_eq_rat {T : Matrix (Fin 3) (Fin 3) ℚ}
    (hT : ∀ x : Fin 3 → ℚ, fZero.evalIn ℚ (T *ᵥ x) = fZero.evalIn ℚ x) (hdet : T.det = 1) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℚ, S.det ≠ 0 ∧ T = spinMat S := by
  have a0 := hT ![1, 0, 0]
  have a2 := hT ![0, 0, 1]
  have a02 := hT ![1, 0, 1]
  simp [evalIn_fZero, mulVec, dotProduct, Fin.sum_univ_three] at a0 a2 a02
  have iso0 : T 0 0 * T 2 0 = T 1 0 ^ 2 := by linarith
  have iso2 : T 0 2 * T 2 2 = T 1 2 ^ 2 := by linarith
  have hB : T 0 0 * T 2 2 + T 2 0 * T 0 2 - 2 * T 1 0 * T 1 2 = 1 := by nlinarith
  have hv0 : (fun i => T i 0) ≠ 0 := by
    intro h
    have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
    simp at e0 e1 e2
    rw [e0, e1, e2] at hB; simp at hB
  have hv2 : (fun i => T i 2) ≠ 0 := by
    intro h
    have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
    simp at e0 e1 e2
    rw [e0, e1, e2] at hB; simp at hB
  obtain ⟨l, p, q, hl, c00, c10, c20⟩ := iso_param _ iso0 hv0
  obtain ⟨m, r, s, hm, c02, c12, c22⟩ := iso_param _ iso2 hv2
  have hD : l * m * (p * s - q * r) ^ 2 = 1 := by
    rw [c00, c10, c20, c02, c12, c22] at hB; linarith
  have hD0 : p * s - q * r ≠ 0 := by
    intro h; rw [h] at hD; simp at hD
  have hm' : m = (l * (p * s - q * r) ^ 2)⁻¹ := by
    field_simp; linarith
  set k : ℚ := (l * (p * s - q * r))⁻¹ with hk
  have hkne : k ≠ 0 := by simp [hk, hl, hD0]
  have hdetS : (!![p, q; k * r, k * s] : Matrix (Fin 2) (Fin 2) ℚ).det = k * (p * s - q * r) := by
    rw [Matrix.det_fin_two_of]; ring
  have hdetS' : k * (p * s - q * r) ≠ 0 := mul_ne_zero hkne hD0
  set S : Matrix (Fin 2) (Fin 2) ℚ := !![p, q; k * r, k * s] with hS
  have hSdet : S.det ≠ 0 := by rw [hdetS]; exact hdetS'
  have hkD : (k * (p * s - q * r))⁻¹ = l := by
    simp only [hk]; field_simp
  have col0 : ∀ i, spinMat S i 0 = T i 0 := by
    intro i
    rw [hS, spinMat_eq]
    have : p * (k * s) - q * (k * r) = k * (p * s - q * r) := by ring
    rw [this, hkD]
    fin_cases i <;> simp [c00, c10, c20] <;> ring
  have col2 : ∀ i, spinMat S i 2 = T i 2 := by
    intro i
    rw [hS, spinMat_eq]
    have : p * (k * s) - q * (k * r) = k * (p * s - q * r) := by ring
    rw [this, hkD]
    fin_cases i <;> simp [c02, c12, c22, hm', hk] <;> field_simp <;> ring
  obtain ⟨hS1, hS2, hS3, hS4⟩ := spinMat_rat S S⁻¹ hSdet (by
    rw [Matrix.det_nonsing_inv]; simp [hSdet])
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hSdet)
  have hone : spinMat (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
    simp [spinMat]
    exact Matrix.one_fin_three.symm
  rw [hSS, hone] at hS3
  -- R * T(S) = 1
  obtain ⟨hR1, hR2, -, -⟩ := spinMat_rat S⁻¹ S (by
    rw [Matrix.det_nonsing_inv]; simp [hSdet]) hSdet
  have hSS' : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet)
  have hS3' := (spinMat_rat S⁻¹ S (by rw [Matrix.det_nonsing_inv]; simp [hSdet]) hSdet).2.2.1
  rw [hSS', hone] at hS3'
  -- U = R * T
  set R := spinMat S⁻¹ with hR
  have hRT : R * spinMat S = 1 := hS3.symm
  have hTR : spinMat S * R = 1 := hS3'.symm
  have key : ∀ j, (∀ i, spinMat S i j = T i j) → ∀ i, (R * T) i j = (1 : Matrix (Fin 3) (Fin 3) ℚ) i j := by
    intro j hj i
    rw [← hRT, Matrix.mul_apply, Matrix.mul_apply]
    simp_rw [hj]
  have hU : R * T = 1 := by
    apply eq_one_of_cols (R * T)
    · intro x
      rw [← Matrix.mulVec_mulVec, hR1, hT]
    · rw [Matrix.det_mul, hR2, hdet]; simp
    · simpa using key 0 col0 0
    · simpa using key 0 col0 1
    · simpa using key 0 col0 2
    · simpa using key 2 col2 0
    · simpa using key 2 col2 1
    · simpa using key 2 col2 2
  refine ⟨S, hSdet, ?_⟩
  calc T = (spinMat S * R) * T := by rw [hTR, Matrix.one_mul]
    _ = spinMat S := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]

theorem spinMat_one : spinMat (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  simp [spinMat]
  exact Matrix.one_fin_three.symm

/-- Casting an integral vector to `ℚ` commutes with `fZero`. -/
theorem cast_eval_fZero (y : Fin 3 → ℤ) :
    ((fZero.eval y : ℤ) : ℚ) = fZero.evalIn ℚ (fun i => (y i : ℚ)) := by
  simp [QuadForm.eval, evalIn_fZero]

theorem cast_mulVec (T : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) :
    T.map (Int.cast : ℤ → ℚ) *ᵥ (fun i => (x i : ℚ)) = fun i => ((T *ᵥ x) i : ℚ) := by
  ext i; simp [mulVec, dotProduct]

/-- An integral matrix preserving `fZero` on `ℚ³` preserves it on `ℤ³`. -/
theorem int_aut_of_cast (T : Matrix (Fin 3) (Fin 3) ℤ)
    (h : ∀ x : Fin 3 → ℚ, fZero.evalIn ℚ (T.map (Int.cast : ℤ → ℚ) *ᵥ x) = fZero.evalIn ℚ x)
    (x : Fin 3 → ℤ) : fZero.eval (T *ᵥ x) = fZero.eval x := by
  apply Int.cast_injective (α := ℚ)
  rw [cast_eval_fZero, cast_eval_fZero, ← cast_mulVec]
  exact h _

/-- An integral automorph of `fZero` preserves it on `ℚ³`. -/
theorem cast_aut_of_int (T : Matrix (Fin 3) (Fin 3) ℤ)
    (h : ∀ x : Fin 3 → ℤ, fZero.eval (T *ᵥ x) = fZero.eval x) (x : Fin 3 → ℚ) :
    fZero.evalIn ℚ (T.map (Int.cast : ℤ → ℚ) *ᵥ x) = fZero.evalIn ℚ x := by
  have a0 := congrArg (Int.cast : ℤ → ℚ) (h ![1, 0, 0])
  have a1 := congrArg (Int.cast : ℤ → ℚ) (h ![0, 1, 0])
  have a2 := congrArg (Int.cast : ℤ → ℚ) (h ![0, 0, 1])
  have b01 := congrArg (Int.cast : ℤ → ℚ) (h ![1, 1, 0])
  have b02 := congrArg (Int.cast : ℤ → ℚ) (h ![1, 0, 1])
  have b12 := congrArg (Int.cast : ℤ → ℚ) (h ![0, 1, 1])
  simp [QuadForm.eval, evalIn_fZero, mulVec, dotProduct, Fin.sum_univ_three] at a0 a1 a2 b01 b02 b12
  rw [evalIn_fZero, evalIn_fZero]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination (x 0) ^ 2 * a0 + (x 1) ^ 2 * a1 + (x 2) ^ 2 * a2 + x 0 * x 1 * (b01 - a0 - a1) +
    x 0 * x 2 * (b02 - a0 - a2) + x 1 * x 2 * (b12 - a1 - a2)

theorem spinMat_scale (e a b c d : ℚ) (he : e ≠ 0) :
    spinMat !![e * a, e * b; e * c, e * d] = spinMat !![a, b; c, d] := by
  rw [spinMat_eq, spinMat_eq]
  have h2 : e * a * (e * d) - e * b * (e * c) = e ^ 2 * (a * d - b * c) := by ring
  rw [h2]
  by_cases h : a * d - b * c = 0
  · simp [h]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- Primitive integral scaling of a nondegenerate rational $2 \times 2$ matrix. -/
theorem prim_scale (a b c d : ℚ) (h : a * d - b * c ≠ 0) :
    ∃ (a' b' c' d' : ℤ) (e : ℚ), e ≠ 0 ∧ a = e * a' ∧ b = e * b' ∧ c = e * c' ∧ d = e * d' ∧
      ∀ p : ℤ, Prime p → ¬ (p ∣ a' ∧ p ∣ b' ∧ p ∣ c' ∧ p ∣ d') := by
  set N : ℕ := a.den * b.den * c.den * d.den with hN
  have hNpos : (N : ℚ) ≠ 0 := by
    have : 0 < N := by positivity
    exact_mod_cast this.ne'
  have ha := Rat.mul_den_eq_num a
  have hb := Rat.mul_den_eq_num b
  have hc := Rat.mul_den_eq_num c
  have hd := Rat.mul_den_eq_num d
  set a₀ : ℤ := a.num * (b.den * c.den * d.den) with ha₀
  set b₀ : ℤ := b.num * (a.den * c.den * d.den) with hb₀
  set c₀ : ℤ := c.num * (a.den * b.den * d.den) with hc₀
  set d₀ : ℤ := d.num * (a.den * b.den * c.den) with hd₀
  have ea : (N : ℚ) * a = a₀ := by rw [ha₀, hN]; push_cast; rw [← ha]; ring
  have eb : (N : ℚ) * b = b₀ := by rw [hb₀, hN]; push_cast; rw [← hb]; ring
  have ec : (N : ℚ) * c = c₀ := by rw [hc₀, hN]; push_cast; rw [← hc]; ring
  have ed : (N : ℚ) * d = d₀ := by rw [hd₀, hN]; push_cast; rw [← hd]; ring
  set g : ℕ := Int.gcd (Int.gcd a₀ b₀) (Int.gcd c₀ d₀) with hg
  have hga : (g : ℤ) ∣ a₀ := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_left ..)
  have hgb : (g : ℤ) ∣ b₀ := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
  have hgc : (g : ℤ) ∣ c₀ := (Int.gcd_dvd_right ..).trans (Int.gcd_dvd_left ..)
  have hgd : (g : ℤ) ∣ d₀ := (Int.gcd_dvd_right ..).trans (Int.gcd_dvd_right ..)
  have hg0 : (g : ℚ) ≠ 0 := by
    intro h0
    have h0' : g = 0 := by exact_mod_cast h0
    simp only [hg, Int.gcd_eq_zero_iff, Nat.cast_eq_zero] at h0'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h0'
    have : (N : ℚ) * a = 0 := by rw [ea]; exact_mod_cast h1
    have : (N : ℚ) * b = 0 := by rw [eb]; exact_mod_cast h2
    have : (N : ℚ) * c = 0 := by rw [ec]; exact_mod_cast h3
    have : (N : ℚ) * d = 0 := by rw [ed]; exact_mod_cast h4
    have : a = 0 := by simp_all
    have : b = 0 := by simp_all
    simp_all
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hg0 : g ≠ 0)
  obtain ⟨a', ha'⟩ := hga
  obtain ⟨b', hb'⟩ := hgb
  obtain ⟨c', hc'⟩ := hgc
  obtain ⟨d', hd'⟩ := hgd
  refine ⟨a', b', c', d', (g : ℚ) / N, div_ne_zero hg0 hNpos, ?_, ?_, ?_, ?_, ?_⟩
  · have haq : (a₀ : ℚ) = g * a' := by exact_mod_cast ha'
    field_simp; linear_combination ea + haq
  · have hbq : (b₀ : ℚ) = g * b' := by exact_mod_cast hb'
    field_simp; linear_combination eb + hbq
  · have hcq : (c₀ : ℚ) = g * c' := by exact_mod_cast hc'
    field_simp; linear_combination ec + hcq
  · have hdq : (d₀ : ℚ) = g * d' := by exact_mod_cast hd'
    field_simp; linear_combination ed + hdq
  · rintro p hp ⟨h1, h2, h3, h4⟩
    have hdv : ∀ {x : ℤ} {y : ℤ}, (g : ℤ) * p ∣ x → (g : ℤ) * p ∣ y → (g : ℤ) * p ∣ ((Int.gcd x y : ℕ) : ℤ) :=
      fun hx hy => Int.dvd_coe_gcd hx hy
    have key : (g : ℤ) * p ∣ (g : ℤ) :=
      hdv (hdv (by rw [ha']; exact mul_dvd_mul_left _ h1) (by rw [hb']; exact mul_dvd_mul_left _ h2))
        (hdv (by rw [hc']; exact mul_dvd_mul_left _ h3) (by rw [hd']; exact mul_dvd_mul_left _ h4))
    have : p ∣ 1 := by
      obtain ⟨k, hk⟩ := key
      have : (g : ℤ) * (p * k) = (g : ℤ) * 1 := by rw [← mul_assoc, ← hk, mul_one]
      exact ⟨k, (mul_left_cancel₀ hgz this).symm⟩
    exact hp.not_isUnit (isUnit_of_dvd_one this)

/-- The integral matrix $\det(S)\cdot\Delta^{-1}\cdots$, i.e. $T(S)$ for $\det S = \pm 1$. -/
def tInt (S : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  S.det • !![S 0 0 ^ 2, 2 * S 0 0 * S 1 0, S 1 0 ^ 2;
    S 0 0 * S 0 1, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 1 0 * S 1 1;
    S 0 1 ^ 2, 2 * S 0 1 * S 1 1, S 1 1 ^ 2]

theorem map_fin2 (a b c d : ℤ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) = !![(a : ℚ), b; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem tInt_map (S : Matrix (Fin 2) (Fin 2) ℤ) (hD : S.det = 1 ∨ S.det = -1) :
    (tInt S).map (Int.cast : ℤ → ℚ) = spinMat (S.map (Int.cast : ℤ → ℚ)) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, S = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two S⟩
  rw [map_fin2, spinMat_eq]
  rw [Matrix.det_fin_two_of] at hD
  rcases hD with hD | hD
  · have hq : (a : ℚ) * d - b * c = 1 := by exact_mod_cast hD
    rw [hq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [tInt, hD, Matrix.det_fin_two_of]
  · have hq : (a : ℚ) * d - b * c = -1 := by exact_mod_cast hD
    rw [hq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [tInt, hD, Matrix.det_fin_two_of]

theorem tInt_det (S : Matrix (Fin 2) (Fin 2) ℤ) (hD : S.det = 1 ∨ S.det = -1) : (tInt S).det = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_det, tInt_map S hD]
  have hq : (S.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; rcases hD with h | h <;> simp [h]
  rw [Matrix.eta_fin_two (S.map (Int.cast : ℤ → ℚ))] at hq ⊢
  rw [Matrix.det_fin_two_of] at hq
  simpa using spinMat_det _ _ _ _ hq

/-- **Lemma 5.2** (Cassels, Ch. 13, §5, p. 302): $S \mapsto T(S)$ maps the integral $2 \times 2$ matrices of
determinant $\pm 1$ ($SL^{\pm}_2(\mathbb{Z})$ = `GL (Fin 2) ℤ`, (5.17)–(5.18)) onto the group $O^+(f_0)$ of proper
integral automorphs, with kernel $\pm I$.

*Note*: Equivalent to `Cassels.Ch13.lemma_5_2` (its map `spinRep S` is `spinMat` of $S^{\mathsf T}$), which carries
the tag. -/
theorem spinMat_int :
    (∀ S : GL (Fin 2) ℤ, ∃ T ∈ Siegel.AutPlus fZero,
      T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))) ∧
    (∀ T ∈ Siegel.AutPlus fZero, ∃ S : GL (Fin 2) ℤ,
      T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))) ∧
    (∀ S : GL (Fin 2) ℤ, spinMat (S.val.map (Int.cast : ℤ → ℚ)) = 1 ↔ S = 1 ∨ S = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    have hD := Siegel.det_GL_int_eq S
    have hdet := tInt_det S.val hD
    refine ⟨Matrix.GeneralLinearGroup.mk'' (tInt S.val) (by rw [hdet]; exact isUnit_one), ?_, ?_⟩
    · rw [Siegel.mem_autPlus_iff]
      refine ⟨?_, hdet⟩
      intro x
      apply int_aut_of_cast
      intro y
      show fZero.evalIn ℚ ((tInt S.val).map (Int.cast : ℤ → ℚ) *ᵥ y) = _
      rw [tInt_map _ hD]
      have hne : (S.val.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
        rw [← Int.cast_det]; rcases hD with h | h <;> simp [h]
      exact (spinMat_rat _ _ hne hne).1 y
    · exact tInt_map _ hD
  · intro T hT
    obtain ⟨hTa, hdet⟩ := Siegel.mem_autPlus_iff.mp hT
    have hTq := cast_aut_of_int T.val hTa
    have hdq : (T.val.map (Int.cast : ℤ → ℚ)).det = 1 := by rw [← Int.cast_det, hdet]; simp
    obtain ⟨S, hS, hTS⟩ := exists_spinMat_eq_rat hTq hdq
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, S = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two S⟩
    rw [Matrix.det_fin_two_of] at hS
    obtain ⟨a', b', c', d', e, he, ha, hb, hc, hd, hprim⟩ := prim_scale a b c d hS
    subst ha hb hc hd
    rw [spinMat_scale _ _ _ _ _ he] at hTS
    have hD'ne : ((a' : ℚ) * d' - b' * c') ≠ 0 := by
      intro h0; apply hS
      have : (e * a') * (e * d') - (e * b') * (e * c') = e ^ 2 * (a' * d' - b' * c') := by ring
      rw [this, h0, mul_zero]
    have ent : ∀ i j, (T.val i j : ℚ) = (spinMat !![(a' : ℚ), b'; c', d']) i j := fun i j => by
      rw [← hTS]; rfl
    have key : ∀ (x : ℤ) (i j : Fin 3) (r : ℚ), (spinMat !![(a' : ℚ), b'; c', d']) i j = r / (a' * d' - b' * c') →
        r = (x : ℚ) ^ 2 → (a' * d' - b' * c' : ℤ) ∣ x ^ 2 := by
      intro x i j r hij hr
      refine ⟨T.val i j, ?_⟩
      apply Int.cast_injective (α := ℚ)
      have := ent i j
      rw [hij] at this
      push_cast
      rw [← hr, this]; field_simp
    have h00 : (a' * d' - b' * c' : ℤ) ∣ a' ^ 2 :=
      key a' 0 0 ((a' : ℚ) ^ 2) (by rw [spinMat_eq]; simp; ring) (by rfl)
    have h02 : (a' * d' - b' * c' : ℤ) ∣ c' ^ 2 :=
      key c' 0 2 ((c' : ℚ) ^ 2) (by rw [spinMat_eq]; simp; ring) (by rfl)
    have h20 : (a' * d' - b' * c' : ℤ) ∣ b' ^ 2 :=
      key b' 2 0 ((b' : ℚ) ^ 2) (by rw [spinMat_eq]; simp; ring) (by rfl)
    have h22 : (a' * d' - b' * c' : ℤ) ∣ d' ^ 2 :=
      key d' 2 2 ((d' : ℚ) ^ 2) (by rw [spinMat_eq]; simp; ring) (by rfl)
    have hunit : a' * d' - b' * c' = 1 ∨ a' * d' - b' * c' = -1 := by
      by_contra hne
      have hn1 : (a' * d' - b' * c' : ℤ).natAbs ≠ 1 := fun h1 => hne (by omega)
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn1
      have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      have hpD : (q : ℤ) ∣ (a' * d' - b' * c' : ℤ) := Int.natCast_dvd.mpr hqd
      exact hprim q hp ⟨hp.dvd_of_dvd_pow (hpD.trans h00), hp.dvd_of_dvd_pow (hpD.trans h20),
        hp.dvd_of_dvd_pow (hpD.trans h02), hp.dvd_of_dvd_pow (hpD.trans h22)⟩
    have hunit' : IsUnit (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [Matrix.det_fin_two_of]; rcases hunit with h | h <;> rw [h] <;> simp
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![a', b'; c', d'] hunit', ?_⟩
    rw [hTS]
    show spinMat !![(a' : ℚ), b'; c', d'] = spinMat ((!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))
    rw [map_fin2]
  · intro S
    obtain ⟨a, b, c, d, hS⟩ : ∃ a b c d, S.val = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    have hD := Siegel.det_GL_int_eq S
    rw [hS, Matrix.det_fin_two_of] at hD
    rw [hS, map_fin2]
    have hne : (a : ℚ) * d - b * c ≠ 0 := by
      rcases hD with h | h
      · have : (a : ℚ) * d - b * c = 1 := by exact_mod_cast h
        rw [this]; norm_num
      · have : (a : ℚ) * d - b * c = -1 := by exact_mod_cast h
        rw [this]; norm_num
    rw [spinMat_eq_one _ _ _ _ hne]
    constructor
    · rintro ⟨e, he⟩
      have hb : (b : ℚ) = 0 := by simpa using congrFun (congrFun he 0) 1
      have hc : (c : ℚ) = 0 := by simpa using congrFun (congrFun he 1) 0
      have ha : (a : ℚ) = e := by simpa using congrFun (congrFun he 0) 0
      have hd : (d : ℚ) = e := by simpa using congrFun (congrFun he 1) 1
      have hb' : b = 0 := by exact_mod_cast hb
      have hc' : c = 0 := by exact_mod_cast hc
      have had : a = d := by
        have : (a : ℚ) = d := by rw [ha, hd]
        exact_mod_cast this
      subst hb' hc' had
      have h1 : (a - 1) * (a + 1) = 0 := by
        rcases hD with h | h <;> nlinarith
      rcases mul_eq_zero.mp h1 with h | h
      · left; apply Units.ext; rw [hS]; have : a = 1 := by omega
        subst this; ext i j; fin_cases i <;> fin_cases j <;> simp
      · right; apply Units.ext; rw [hS]; have : a = -1 := by omega
        subst this; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rintro (h | h)
      · have h1 := congrArg Units.val h
        rw [hS] at h1
        have h2 : (a = 1 ∧ b = 0) ∧ c = 0 ∧ d = 1 := by
          have e00 := congrFun (congrFun h1 0) 0
          have e01 := congrFun (congrFun h1 0) 1
          have e10 := congrFun (congrFun h1 1) 0
          have e11 := congrFun (congrFun h1 1) 1
          simp at e00 e01 e10 e11
          exact ⟨⟨e00, e01⟩, e10, e11⟩
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h2
        exact ⟨1, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
      · have h1 := congrArg Units.val h
        rw [hS] at h1
        have h2 : (a = -1 ∧ b = 0) ∧ c = 0 ∧ d = -1 := by
          have e00 := congrFun (congrFun h1 0) 0
          have e01 := congrFun (congrFun h1 0) 1
          have e10 := congrFun (congrFun h1 1) 0
          have e11 := congrFun (congrFun h1 1) 1
          simp at e00 e01 e10 e11
          exact ⟨⟨e00, e01⟩, e10, e11⟩
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h2
        exact ⟨-1, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem map_mul_cast {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) := by
  ext i j; simp [Matrix.mul_apply]

theorem det_map_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℚ)).det = (A.det : ℚ) := (Int.cast_det A).symm

theorem frakG_mul {T₁ T₂ : GL (Fin 3) ℤ} {S₁ S₂ : GL (Fin 2) ℤ}
    (h₁ : T₁.val.map (Int.cast : ℤ → ℚ) = spinMat (S₁.val.map (Int.cast : ℤ → ℚ)))
    (h₂ : T₂.val.map (Int.cast : ℤ → ℚ) = spinMat (S₂.val.map (Int.cast : ℤ → ℚ))) :
    (T₁ * T₂).val.map (Int.cast : ℤ → ℚ) = spinMat ((S₂ * S₁).val.map (Int.cast : ℤ → ℚ)) := by
  have hne : ∀ S : GL (Fin 2) ℤ, (S.val.map (Int.cast : ℤ → ℚ)).det ≠ 0 := fun S => by
    rw [det_map_cast]; rcases Siegel.det_GL_int_eq S with h | h <;> simp [h]
  rw [Units.val_mul, map_mul_cast, h₁, h₂, Units.val_mul, map_mul_cast]
  exact (spinMat_rat _ _ (hne S₂) (hne S₁)).2.2.1.symm

theorem frakG_inv {T : GL (Fin 3) ℤ} {S : GL (Fin 2) ℤ}
    (h : T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))) :
    (T⁻¹).val.map (Int.cast : ℤ → ℚ) = spinMat ((S⁻¹).val.map (Int.cast : ℤ → ℚ)) := by
  have hne : ∀ S : GL (Fin 2) ℤ, (S.val.map (Int.cast : ℤ → ℚ)).det ≠ 0 := fun S => by
    rw [det_map_cast]; rcases Siegel.det_GL_int_eq S with h | h <;> simp [h]
  have h1 : (T⁻¹).val.map (Int.cast : ℤ → ℚ) * T.val.map (Int.cast : ℤ → ℚ) = 1 := by
    rw [← map_mul_cast, ← Units.val_mul, inv_mul_cancel]; ext i j; simp [Matrix.one_apply]
  have h2 : spinMat ((S⁻¹).val.map (Int.cast : ℤ → ℚ)) * T.val.map (Int.cast : ℤ → ℚ) = 1 := by
    rw [h, ← (spinMat_rat _ _ (hne S) (hne S⁻¹)).2.2.1, ← map_mul_cast, ← Units.val_mul, mul_inv_cancel]
    simpa using spinMat_one
  exact (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)

/-- **The subgroup $\mathfrak{G}$** (Cassels, Ch. 13, §5, p. 303): the image in $O^+(f_0)$ of the integral matrices of
determinant $1$. -/
@[kb "cassels1978" "Ch. 13, §5, p. 303 (the subgroup 𝔊, image of SL₂(ℤ))"]
def frakG : Subgroup (GL (Fin 3) ℤ) where
  carrier := {T | T ∈ Siegel.AutPlus fZero ∧ ∃ S : GL (Fin 2) ℤ, S.val.det = 1 ∧
    T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))}
  mul_mem' := by
    rintro T₁ T₂ ⟨hT₁, S₁, hS₁, h₁⟩ ⟨hT₂, S₂, hS₂, h₂⟩
    refine ⟨(Siegel.AutPlus fZero).mul_mem hT₁ hT₂, S₂ * S₁, ?_, frakG_mul h₁ h₂⟩
    rw [Units.val_mul, Matrix.det_mul, hS₁, hS₂, one_mul]
  one_mem' := by
    refine ⟨(Siegel.AutPlus fZero).one_mem, 1, by simp, ?_⟩
    simp [spinMat_one]
  inv_mem' := by
    rintro T ⟨hT, S, hS, h⟩
    refine ⟨(Siegel.AutPlus fZero).inv_mem hT, S⁻¹, ?_, frakG_inv h⟩
    have := congrArg Matrix.det (S.inv_val)
    rw [Matrix.det_mul, hS, mul_one, Matrix.det_one] at this
    exact this

theorem spinMat_cast_det_ne (S : GL (Fin 2) ℤ) : (S.val.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  rw [det_map_cast]; rcases Siegel.det_GL_int_eq S with h | h <;> simp [h]

/-- $T(S_1) = T(S_2)$ for integral unimodular $S_i$ forces $\det S_1 = \det S_2$. -/
theorem det_eq_of_spinMat_eq {S₁ S₂ : GL (Fin 2) ℤ}
    (h : spinMat (S₁.val.map (Int.cast : ℤ → ℚ)) = spinMat (S₂.val.map (Int.cast : ℤ → ℚ))) :
    S₁.val.det = S₂.val.det := by
  have h1 : spinMat ((S₂ * S₁⁻¹).val.map (Int.cast : ℤ → ℚ)) = 1 := by
    rw [Units.val_mul, map_mul_cast,
      (spinMat_rat _ _ (spinMat_cast_det_ne S₂) (spinMat_cast_det_ne S₁⁻¹)).2.2.1, ← h,
      ← (spinMat_rat _ _ (spinMat_cast_det_ne S₁) (spinMat_cast_det_ne S₁⁻¹)).2.2.1, ← map_mul_cast,
      ← Units.val_mul, mul_inv_cancel]
    simpa using spinMat_one
  have h2 : S₂ * S₁⁻¹ = 1 ∨ S₂ * S₁⁻¹ = -1 := (spinMat_int.2.2 _).mp h1
  have h3 : (S₂ * S₁⁻¹).val.det = 1 := by
    rcases h2 with h2 | h2 <;> rw [h2] <;> simp [Matrix.det_neg]
  rw [Units.val_mul, Matrix.det_mul] at h3
  have h4 : S₁.val.det * (S₁⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]; simp
  have hne : (S₁⁻¹).val.det ≠ 0 := right_ne_zero_of_mul_eq_one h4
  exact (mul_right_cancel₀ hne (h3.trans h4.symm)).symm

/-- For $T = T(S)$ in $O^+(f_0)$: $T \in \mathfrak{G}$ iff $\det S = 1$. -/
theorem mem_frakG_iff {T : GL (Fin 3) ℤ} {S : GL (Fin 2) ℤ} (hT : T ∈ Siegel.AutPlus fZero)
    (h : T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))) :
    T ∈ frakG ↔ S.val.det = 1 := by
  constructor
  · rintro ⟨-, S', hS', h'⟩
    rw [← hS']
    exact det_eq_of_spinMat_eq (h.symm.trans h')
  · intro hS
    exact ⟨hT, S, hS, h⟩

/-- **$\mathfrak{G}$ has index $2$ in $O^+(f_0)$** (Cassels, Ch. 13, §5, p. 303). -/
@[kb "cassels1978" "Ch. 13, §5, p. 303 (𝔊 has index 2 in O⁺(f₀))"]
theorem frakG_index : frakG ≤ Siegel.AutPlus fZero ∧ (frakG.subgroupOf (Siegel.AutPlus fZero)).index = 2 := by
  refine ⟨fun T hT => hT.1, ?_⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : GL (Fin 2) ℤ, S₀.val = !![1, 0; 0, -1] :=
    ⟨Matrix.GeneralLinearGroup.mk'' !![1, 0; 0, -1] (by rw [Matrix.det_fin_two_of]; simp), rfl⟩
  have hdet₀ : S₀.val.det = -1 := by rw [hS₀, Matrix.det_fin_two_of]; simp
  obtain ⟨A, hA, hAS⟩ := spinMat_int.1 S₀
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨A, hA⟩, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨S, hS⟩ := spinMat_int.2.1 B hB
  have hBA := frakG_mul hS hAS
  have hBm := mem_frakG_iff hB hS
  have hBAm := mem_frakG_iff ((Siegel.AutPlus fZero).mul_mem hB hA) hBA
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rw [hBm, hBAm, Units.val_mul, Matrix.det_mul, hdet₀]
  rcases Siegel.det_GL_int_eq S with h | h <;> simp [h]

/-- The binary form $\phi_{\vec b}(\vec x) = b_0x_0^2 + 2b_1x_0x_1 + b_2x_1^2$ of (5.2). -/
def bq (b : Fin 3 → ℤ) (x : Fin 2 → ℤ) : ℤ := b 0 * x 0 ^ 2 + 2 * b 1 * x 0 * x 1 + b 2 * x 1 ^ 2

theorem eval_binGram (b : Fin 3 → ℤ) (x : Fin 2 → ℤ) :
    (Siegel.ofGram !![b 0, b 1; b 1, b 2]).eval x = bq b x := by
  have hA : (!![b 0, b 1; b 1, b 2] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Siegel.eval_ofGram hA]
  simp [bq, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem tInt_core (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1) (b b' : Fin 3 → ℤ) :
    tInt U *ᵥ b = b' ↔ ∀ x, bq b (U *ᵥ x) = bq b' x := by
  obtain ⟨a, c, e, d, rfl⟩ : ∃ a c e d, U = !![a, c; e, d] := ⟨_, _, _, _, Matrix.eta_fin_two U⟩
  rw [Matrix.det_fin_two_of] at hU
  constructor
  · rintro rfl x
    simp [bq, tInt, mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_two_of, hU]
    ring
  · intro h
    have h0 := h ![1, 0]
    have h1 := h ![0, 1]
    have h2 := h ![1, 1]
    simp [bq, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2
    ext i
    fin_cases i <;> simp [tInt, mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_two_of, hU]
    · linarith
    · linarith
    · linarith

theorem eq_tInt {T : GL (Fin 3) ℤ} {S : GL (Fin 2) ℤ}
    (h : T.val.map (Int.cast : ℤ → ℚ) = spinMat (S.val.map (Int.cast : ℤ → ℚ))) : T.val = tInt S.val :=
  Matrix.map_injective Int.cast_injective (h.trans (tInt_map _ (Siegel.det_GL_int_eq S)).symm)

/-- **Lemma 5.3** (Cassels, Ch. 13, §5, p. 303): the orbits under $\mathfrak{G}$ of the integral $\vec{b}$ with
$f_0(\vec{b}) = m$ correspond bijectively to the proper equivalence classes of classically integral binary forms of
determinant $m$, by $\vec{b} \mapsto \phi_{\vec{b}} = b_0u_0^2 + 2b_1u_0u_1 + b_2u_1^2$ (whose determinant is
$f_0(\vec{b})$; every such binary form is a $\phi_{\vec{b}}$). Stated: $\vec{b}, \vec{b}'$ are in the same
$\mathfrak{G}$-orbit iff $\phi_{\vec{b}}$, $\phi_{\vec{b}'}$ are properly equivalent. (Cassels assumes $m \ne 0$; not
needed.)

*Note*: Equivalent to `Cassels.Ch13.lemma_5_3` (the image of $SL_2(\mathbb Z)$ is the same group under
$S \mapsto S^{\mathsf T}$), which carries the tag. -/
theorem frakG_orbit_iff (b b' : Fin 3 → ℤ) :
    (∃ T ∈ frakG, T.val *ᵥ b = b') ↔
      Siegel.ProperIntEquiv (Siegel.ofGram !![b 0, b 1; b 1, b 2]) (Siegel.ofGram !![b' 0, b' 1; b' 1, b' 2]) := by
  constructor
  · rintro ⟨T, ⟨hTa, S, hS, hmap⟩, hTb⟩
    refine ⟨S, hS, fun x => ?_⟩
    rw [eval_binGram, eval_binGram]
    rw [eq_tInt hmap] at hTb
    exact (tInt_core S.val hS b b').mp hTb x
  · rintro ⟨S, hS, h⟩
    simp only [eval_binGram] at h
    obtain ⟨T, hT, hmap⟩ := spinMat_int.1 S
    refine ⟨T, (mem_frakG_iff hT hmap).mpr hS, ?_⟩
    rw [eq_tInt hmap]
    exact (tInt_core S.val hS b b').mpr h

/-- Proper equivalence of the binary forms $\phi_{\vec b}$, $\phi_{\vec b'}$. -/
def BE (b b' : Fin 3 → ℤ) : Prop :=
  Siegel.ProperIntEquiv (Siegel.ofGram !![b 0, b 1; b 1, b 2]) (Siegel.ofGram !![b' 0, b' 1; b' 1, b' 2])

/-- The substitution $x_0 \mapsto x_0 + t x_1$ on coefficients. -/
def shiftV (t : ℤ) (b : Fin 3 → ℤ) : Fin 3 → ℤ := ![b 0, b 1 + t * b 0, b 2 + 2 * t * b 1 + t ^ 2 * b 0]

/-- The substitution $(x_0, x_1) \mapsto (-x_1, x_0)$ on coefficients. -/
def swapV (b : Fin 3 → ℤ) : Fin 3 → ℤ := ![b 2, -b 1, b 0]

theorem BE_refl (b : Fin 3 → ℤ) : BE b b := Siegel.ProperIntEquiv.refl _

theorem BE_trans {b b' b'' : Fin 3 → ℤ} (h : BE b b') (h' : BE b' b'') : BE b b'' :=
  Siegel.ProperIntEquiv.trans h h'

theorem BE_shift (t : ℤ) (b : Fin 3 → ℤ) : BE b (shiftV t b) := by
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![1, t; 0, 1] (by rw [Matrix.det_fin_two_of]; simp), ?_, fun x => ?_⟩
  · show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1
    rw [Matrix.det_fin_two_of]; simp
  · rw [eval_binGram, eval_binGram]
    show bq b (!![1, t; 0, 1] *ᵥ x) = bq (shiftV t b) x
    simp [bq, shiftV, mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem BE_swap (b : Fin 3 → ℤ) : BE b (swapV b) := by
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![0, -1; 1, 0] (by rw [Matrix.det_fin_two_of]; simp), ?_, fun x => ?_⟩
  · show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1
    rw [Matrix.det_fin_two_of]; simp
  · rw [eval_binGram, eval_binGram]
    show bq b (!![0, -1; 1, 0] *ᵥ x) = bq (swapV b) x
    simp [bq, swapV, mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- Residue of smallest absolute value: $2|x + ty| \le |y|$ for some integer $t$. -/
theorem exists_res (x y : ℤ) (hy : y ≠ 0) : ∃ t : ℤ, 2 * |x + t * y| ≤ |y| := by
  rcases lt_or_gt_of_ne hy with h | h
  · have hc : 0 < -y := by omega
    have h1 := Int.ediv_mul_le (2 * x + -y) (show 2 * -y ≠ 0 by omega)
    have h2 := Int.lt_ediv_add_one_mul_self (2 * x + -y) (show 0 < 2 * -y by omega)
    refine ⟨(2 * x + -y) / (2 * -y), ?_⟩
    rw [abs_of_neg h]
    have : 2 * |x + (2 * x + -y) / (2 * -y) * y| = |2 * (x + (2 * x + -y) / (2 * -y) * y)| := by
      rw [abs_mul]; norm_num
    rw [this, abs_le]
    constructor <;> nlinarith
  · have h1 := Int.ediv_mul_le (2 * x + y) (show 2 * y ≠ 0 by omega)
    have h2 := Int.lt_ediv_add_one_mul_self (2 * x + y) (show 0 < 2 * y by omega)
    refine ⟨-((2 * x + y) / (2 * y)), ?_⟩
    rw [abs_of_pos h]
    have : 2 * |x + -((2 * x + y) / (2 * y)) * y| = |2 * (x + -((2 * x + y) / (2 * y)) * y)| := by
      rw [abs_mul]; norm_num
    rw [this, abs_le]
    constructor <;> nlinarith

theorem bounded_aux (m : ℤ) (hm : m ≠ 0) (b : Fin 3 → ℤ) (hb : b 0 * b 2 - b 1 ^ 2 = m) :
    ∃ b', BE b b' ∧ ∀ i, |b' i| ≤ 2 * |m| := by
  classical
  have hex : ∃ n, ∃ b', BE b b' ∧ b' 0 * b' 2 - b' 1 ^ 2 = m ∧ (b' 0).natAbs = n :=
    ⟨_, b, BE_refl b, hb, rfl⟩
  obtain ⟨c, hE, hm', hn⟩ := Nat.find_spec hex
  have hmin : ∀ b'', BE b b'' → b'' 0 * b'' 2 - b'' 1 ^ 2 = m → (c 0).natAbs ≤ (b'' 0).natAbs :=
    fun b'' h1 h2 => by rw [hn]; exact Nat.find_min' hex ⟨b'', h1, h2, rfl⟩
  clear hn hex
  have hmabs : 0 < |m| := abs_pos.mpr hm
  by_cases h0 : c 0 = 0
  · have h1 : c 1 ≠ 0 := by
      intro h; apply hm; rw [← hm', h0, h]; ring
    obtain ⟨t, ht⟩ := exists_res (c 2) (2 * c 1) (by omega)
    have habs : |2 * c 1| = 2 * |c 1| := by rw [abs_mul]; norm_num
    rw [habs] at ht
    have hm1 : |c 1| ≤ |m| := by
      have : |m| = |c 1| * |c 1| := by
        have e : c 0 * c 2 - c 1 ^ 2 = -(c 1 * c 1) := by rw [h0]; ring
        rw [← hm', e, abs_neg, abs_mul]
      have hp : 1 ≤ |c 1| := by have := abs_pos.mpr h1; omega
      nlinarith
    refine ⟨shiftV t c, BE_trans hE (BE_shift t c), fun i => ?_⟩
    fin_cases i
    · simp [shiftV, h0] <;> omega
    · simp [shiftV, h0] <;> omega
    · simp only [shiftV, h0]
      simp
      have : |c 2 + 2 * t * c 1| ≤ |c 1| := by
        have : c 2 + t * (2 * c 1) = c 2 + 2 * t * c 1 := by ring
        rw [this] at ht; omega
      omega
  · obtain ⟨t, ht⟩ := exists_res (c 1) (c 0) h0
    set d := shiftV t c with hd
    have hdm : d 0 * d 2 - d 1 ^ 2 = m := by
      rw [← hm']; simp [hd, shiftV]; ring
    have hdE : BE b d := BE_trans hE (BE_shift t c)
    have hd0 : d 0 = c 0 := by simp [hd, shiftV]
    have hd1 : d 1 = c 1 + t * c 0 := by simp [hd, shiftV]
    have hsw := hmin (swapV d) (BE_trans hdE (BE_swap d)) (by simp [swapV]; rw [← hdm]; ring)
    simp only [swapV] at hsw
    simp at hsw
    refine ⟨d, hdE, fun i => ?_⟩
    have hA : 1 ≤ |d 0| := by rw [hd0]; have := abs_pos.mpr h0; omega
    have hB : 2 * |d 1| ≤ |d 0| := by rw [hd1, hd0]; exact ht
    have hC : |d 0| ≤ |d 2| := by
      rw [hd0, Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast hsw
    have hprod : |d 0| * |d 2| ≤ |m| + |d 1| * |d 1| := by
      have : d 0 * d 2 = m + d 1 ^ 2 := by linarith
      calc |d 0| * |d 2| = |d 0 * d 2| := (abs_mul _ _).symm
        _ = |m + d 1 ^ 2| := by rw [this]
        _ ≤ |m| + |d 1 ^ 2| := abs_add_le _ _
        _ = |m| + |d 1| * |d 1| := by rw [abs_pow, sq]
    have hB0 := abs_nonneg (d 1)
    have hC2 : |d 2| ≤ 2 * |m| := by nlinarith
    fin_cases i
    · simp; nlinarith
    · simp; nlinarith
    · simpa using hC2

/-- **Lemma 5.3, Corollary** (Cassels, Ch. 13, §5, p. 303): the orbits under $\mathfrak{G}$ of the $\vec{b}$ with
$f_0(\vec{b}) = m \ne 0$ can be effectively determined. Effective form: each orbit contains a $\vec{b}$ with
$|b_i| \le 2|m|$ (a reduced binary form $\phi_{\vec{b}}$, by the reduction theory of binary forms), so the
representatives are found by a finite search, and the proper equivalence of the finitely many candidates is decided
by §3 (indefinite) or by the reduction of definite forms (Ch. 12). -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.3, Cor., p. 303"]
theorem exists_frakG_bounded {m : ℤ} (hm : m ≠ 0) {b : Fin 3 → ℤ} (hb : fZero.eval b = m) :
    ∃ T ∈ frakG, ∀ i, |(T.val *ᵥ b) i| ≤ 2 * |m| := by
  have hb' : b 0 * b 2 - b 1 ^ 2 = m := by simpa [QuadForm.eval, evalIn_fZero] using hb
  obtain ⟨b', hE, hbd⟩ := bounded_aux m hm b hb'
  obtain ⟨T, hT, hTb⟩ := (frakG_orbit_iff b b').mpr hE
  exact ⟨T, hT, fun i => by rw [hTb]; exact hbd i⟩

/-- **Lemma 5.4** (Cassels, Ch. 13, §5, p. 303): the orbits under $O^+(f_0)$ of the integral $\vec{b}$ with
$f_0(\vec{b}) = m \ne 0$ can be effectively determined; effective form as in the Corollary to Lemma 5.3. -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.4, p. 303"]
theorem exists_autPlus_fZero_bounded {m : ℤ} (hm : m ≠ 0) {b : Fin 3 → ℤ} (hb : fZero.eval b = m) :
    ∃ T ∈ Siegel.AutPlus fZero, ∀ i, |(T.val *ᵥ b) i| ≤ 2 * |m| := by
  obtain ⟨T, hT, h⟩ := exists_frakG_bounded hm hb
  exact ⟨T, hT.1, h⟩

end QuadFormsKB.Reduction
