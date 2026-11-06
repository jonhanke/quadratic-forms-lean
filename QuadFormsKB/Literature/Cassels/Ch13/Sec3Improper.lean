/-
# Cassels, Chapter 13, §3: improper integral automorphs of binary forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §3, Theorem 3.2 and Lemma 3.4 (p. 294): a real
regular binary form has an improper integral automorph iff it is integrally equivalent to a form
$ax^2 + 2bxy + cy^2$ with $b = 0$ or $2b = a$.

Conventions as in `Ch13/Sec2.lean`: a real form is its symmetric matrix $F$ (Cassels' (3.6):
$F = \begin{pmatrix} a & b \\ b & c\end{pmatrix}$ for $ax^2 + 2bxy + cy^2$), $f(T\vec{x})$ has matrix `act T F`, indices
are 0-based ($F_{00} = a$, $F_{01} = b$).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic

open Matrix

namespace QuadFormsKB.Reduction

/-- An integral matrix with unit determinant is (the underlying matrix of) an element of $\mathrm{GL}_2(\mathbb{Z})$. -/
theorem exists_gl_of_isUnit_det (S : Matrix (Fin 2) (Fin 2) ℤ) (h : IsUnit S.det) :
    ∃ U : GL (Fin 2) ℤ, U.val = S :=
  ⟨Matrix.nonsingInvUnit S h, rfl⟩

/-- Entries of an involution of determinant $-1$: trace zero. -/
theorem invol_entries {p q r s : ℤ} (hT : !![p, q; r, s] * !![p, q; r, s] = 1) (hdet : p * s - q * r = -1) :
    s = -p ∧ p * p + q * r = 1 := by
  have h00 := congrFun (congrFun hT 0) 0
  have h01 := congrFun (congrFun hT 0) 1
  have h10 := congrFun (congrFun hT 1) 0
  have h11 := congrFun (congrFun hT 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hs : s = -p := by
    by_contra hne
    have hne' : p + s ≠ 0 := fun h => hne (by linarith)
    have hq : q = 0 := by
      have : q * (p + s) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hne'
    have hr : r = 0 := by
      have : r * (p + s) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hne'
    subst hq hr
    have : p * s = -1 := by linarith
    have h1 : p * p = 1 := by linarith
    have h2 : s * s = 1 := by linarith
    apply hne'
    nlinarith [sq_nonneg (p + s)]
  exact ⟨hs, by linarith⟩

/-- A primitive fixed vector of an involution of determinant $-1$. -/
theorem exists_fixed_primitive {p q r s : ℤ} (hs : s = -p) (hpq : p * p + q * r = 1) :
    ∃ x y : ℤ, Int.gcd x y = 1 ∧ p * x + q * y = x ∧ r * x + s * y = y := by
  subst hs
  have key : ∀ v0 v1 : ℤ, (v0 ≠ 0 ∨ v1 ≠ 0) → p * v0 + q * v1 = v0 → r * v0 + -p * v1 = v1 →
      ∃ x y : ℤ, Int.gcd x y = 1 ∧ p * x + q * y = x ∧ r * x + -p * y = y := by
    intro v0 v1 hv h0 h1
    have hg : 0 < Int.gcd v0 v1 := by
      rcases hv with h | h
      · exact Int.gcd_pos_of_ne_zero_left _ h
      · exact Int.gcd_pos_of_ne_zero_right _ h
    obtain ⟨g, x, y, hg0, hxy, rfl, rfl⟩ := Int.exists_gcd_one' hg
    have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
    refine ⟨x, y, hxy, ?_, ?_⟩
    · apply mul_right_cancel₀ hg'; linear_combination h0
    · apply mul_right_cancel₀ hg'; linear_combination h1
  by_cases h : p + 1 = 0 ∧ r = 0
  · obtain ⟨h1, h2⟩ := h
    exact key q (1 - p) (Or.inr (by omega)) (by ring) (by linear_combination hpq)
  · refine key (p + 1) r (by tauto) (by linear_combination hpq) (by ring)

/-- The value of a real binary form with symmetric matrix. -/
private theorem val_fin2' {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (x : Fin 2 → ℝ) :
    val F x = F 0 0 * x 0 ^ 2 + 2 * F 0 1 * x 0 * x 1 + F 1 1 * x 1 ^ 2 := by
  have h : F 1 0 = F 0 1 := hF.apply 0 1
  simp [val, dotProduct, mulVec, Fin.sum_univ_two, h]
  ring

/-- Substitution preserves symmetry of the matrix. -/
theorem isSymm_act {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (T : Matrix (Fin 2) (Fin 2) ℤ) :
    (act T F).IsSymm := by
  unfold act
  have : Fᵀ = F := hF
  simp [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc, this]

/-- An improper integral automorph of a regular real binary form is an involution. -/
theorem improper_aut_sq {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0)
    {T : Matrix (Fin 2) (Fin 2) ℤ} (hT : T.det = -1) (hact : act T F = F) : T * T = 1 := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, T = !![p, q; r, s] :=
    ⟨T 0 0, T 0 1, T 1 0, T 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have hD : p * s - q * r = -1 := by simpa [Matrix.det_fin_two_of] using hT
  have hDR : (p : ℝ) * s - q * r = -1 := by exact_mod_cast hD
  have h10 : F 1 0 = F 0 1 := hF.apply 0 1
  have hdetF : F 0 0 * F 1 1 - F 0 1 * F 0 1 ≠ 0 := by
    rw [Matrix.det_fin_two, h10] at hdet; exact hdet
  have E00 := congrFun (congrFun hact 0) 0
  have E01 := congrFun (congrFun hact 0) 1
  have E11 := congrFun (congrFun hact 1) 1
  simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two, h10] at E00 E01 E11
  set a := F 0 0
  set b := F 0 1
  set c := F 1 1
  have n1 : a * (p + s) = 0 := by
    linear_combination (p * a + r * b) * hDR - (s : ℝ) * E00 + (r : ℝ) * E01
  have n2 : c * (p + s) = 0 := by
    linear_combination (q * b + s * c) * hDR + (q : ℝ) * E01 - (p : ℝ) * E11
  have n3 : 2 * p * b + r * c - a * q = 0 := by
    linear_combination (p * b + r * c) * hDR + (q : ℝ) * E00 - (p : ℝ) * E01
  have n4 : q * a + 2 * s * b - c * r = 0 := by
    linear_combination (q * a + s * b) * hDR - (s : ℝ) * E01 + (r : ℝ) * E11
  have hps : (p : ℝ) + s = 0 := by
    by_contra hne
    have ha : a = 0 := (mul_eq_zero.1 n1).resolve_right hne
    have hc : c = 0 := (mul_eq_zero.1 n2).resolve_right hne
    rw [ha, hc] at hdetF
    have hb : b ≠ 0 := by intro h; apply hdetF; rw [h]; ring
    have hp : (p : ℝ) = 0 := by
      rw [ha, hc] at n3
      have : 2 * b * p = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linarith : b = 0) hb
      · exact h
    have hs : (s : ℝ) = 0 := by
      rw [ha, hc] at n4
      have : 2 * b * s = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linarith : b = 0) hb
      · exact h
    apply hne; rw [hp, hs]; ring
  have hs : s = -p := by
    have : ((p + s : ℤ) : ℝ) = 0 := by push_cast; exact hps
    have := Int.cast_eq_zero.1 this
    linarith
  subst hs
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- **Lemma 3.4** (Cassels, Ch. 13, §3, p. 294): let $T$ be an integral $2 \times 2$ matrix with $T^2 = I$ and
$\det T = -1$ (3.29). Then there is an integral $S$ with $\det S = \pm 1$ such that
$$S^{-1}TS = \begin{pmatrix} 1 & w \\ 0 & -1\end{pmatrix}, \qquad w \in \{0, 1\}. \tag{3.30–3.31}$$
(The displays (3.30)–(3.31) are lost in the machine-read text; reconstructed from the proof: $T\vec{a} = \vec{a}$,
$T\vec{b} = w\vec{a} - \vec{b}$ in a basis $\vec{a}, \vec{b}$ of $\mathbb{Z}^2$, $S$ the matrix of that basis.)

Superseded by `Cassels.Ch13.lemma_3_4`, which gives $\det S = 1$. -/
theorem conj_involution_det_neg_one {T : Matrix (Fin 2) (Fin 2) ℤ} (hT : T * T = 1) (hdet : T.det = -1) :
    ∃ S : GL (Fin 2) ℤ, ∃ w : ℤ, (w = 0 ∨ w = 1) ∧ (S⁻¹).val * T * S.val = !![1, w; 0, -1] := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, T = !![p, q; r, s] :=
    ⟨T 0 0, T 0 1, T 1 0, T 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have hdet' : p * s - q * r = -1 := by simpa [Matrix.det_fin_two_of] using hdet
  obtain ⟨hs, hpq⟩ := invol_entries hT hdet'
  obtain ⟨x, y, hg, hx1, hx2⟩ := exists_fixed_primitive hs hpq
  have hbez := Int.gcd_eq_gcd_ab x y
  rw [hg] at hbez
  set b0 := -Int.gcdB x y with hb0
  set b1 := Int.gcdA x y with hb1
  have hdab : x * b1 - b0 * y = 1 := by rw [hb0, hb1]; push_cast at hbez; linarith
  -- c = T b + b is fixed
  set c0 := p * b0 + q * b1 + b0 with hc0
  set c1 := r * b0 + s * b1 + b1 with hc1
  have hf0 : p * c0 + q * c1 = c0 := by
    rw [hc0, hc1]; subst hs
    have e1 : p * p + q * r = 1 := hpq
    have e2 : p * q + q * -p = 0 := by ring
    have e3 : r * p + -p * r = 0 := by ring
    linear_combination (b0) * e1 + b1 * e2 + 0 * e3
  have hf1 : r * c0 + s * c1 = c1 := by
    rw [hc0, hc1]; subst hs
    have e1 : p * p + q * r = 1 := hpq
    linear_combination (b1) * e1 + 0 * hdet' - b1 * hpq + b1 * hpq
  -- c is parallel to a
  have hD : x * c1 - c0 * y = 0 := by
    have h : (p * x + q * y) * (r * c0 + s * c1) - (p * c0 + q * c1) * (r * x + s * y) =
        (p * s - q * r) * (x * c1 - c0 * y) := by ring
    rw [hx1, hx2, hf0, hf1, hdet'] at h
    linarith
  set α := c0 * b1 - c1 * b0 with hα
  have hca0 : c0 = α * x := by
    rw [hα]; linear_combination (-c0) * hdab + b0 * hD
  have hca1 : c1 = α * y := by
    rw [hα]; linear_combination (-c1) * hdab + b1 * hD
  -- adjust by multiples of a
  set v : ℤ := -(α / 2) with hv
  set w : ℤ := α + 2 * v with hw
  have hw01 : w = 0 ∨ w = 1 := by omega
  set B0 := b0 + v * x
  set B1 := b1 + v * y
  have hdS : (!![x, B0; y, B1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [Matrix.det_fin_two_of, B0, B1]; linarith
  obtain ⟨S, hS⟩ := exists_gl_of_isUnit_det _ (by rw [hdS]; exact isUnit_one)
  have hTS : !![p, q; r, s] * S.val = S.val * !![1, w; 0, -1] := by
    rw [hS]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, B0, B1]
    · linarith
    · linear_combination (v) * hx1 + hca0 - 0 * hw
    · linarith
    · linear_combination (v) * hx2 + hca1
  refine ⟨S, w, hw01, ?_⟩
  calc (S⁻¹).val * !![p, q; r, s] * S.val = (S⁻¹).val * (!![p, q; r, s] * S.val) := by rw [Matrix.mul_assoc]
    _ = (S⁻¹).val * (S.val * !![1, w; 0, -1]) := by rw [hTS]
    _ = ((S⁻¹).val * S.val) * !![1, w; 0, -1] := by rw [Matrix.mul_assoc]
    _ = !![1, w; 0, -1] := by rw [Units.inv_mul, Matrix.one_mul]

/-- **Theorem 3.2** (Cassels, Ch. 13, §3, p. 294): a regular real binary form $f$ has an improper integral automorph
(an integral $T$ with $\det T = -1$ and $f(T\vec{x}) = f(\vec{x})$) if and only if it is integrally equivalent to a form
$ax^2 + 2bxy + cy^2$ (3.26) with either $b = 0$ (3.27) or $2b = a$ (3.28). The theorem applies to definite and
indefinite, isotropic and anisotropic forms. *Erratum*: the proof says "let $S$ be
given by Lemma 3.3"; Lemma 3.4 is meant.

Equivalent to `Cassels.Ch13.thm_3_2` (coefficients instead of matrices), which carries the tag. -/
theorem exists_improper_aut_iff {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (∃ T : GL (Fin 2) ℤ, T.val.det = -1 ∧ act T.val F = F) ↔
      ∃ U : GL (Fin 2) ℤ, (act U.val F) 0 1 = 0 ∨ 2 * (act U.val F) 0 1 = (act U.val F) 0 0 := by
  constructor
  · rintro ⟨T, hT, hact⟩
    have hTT := improper_aut_sq hF hdet hT hact
    obtain ⟨S, w, hw, hSTS⟩ := conj_involution_det_neg_one hTT hT
    have hTS : T.val * S.val = S.val * !![1, w; 0, -1] := by
      have : S.val * ((S⁻¹).val * T.val * S.val) = T.val * S.val := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [← this, hSTS]
    have hMG : act !![1, w; 0, -1] (act S.val F) = act S.val F := by
      rw [← act_mul, ← hTS, act_mul, hact]
    have hG := isSymm_act hF S.val
    set G := act S.val F
    have hv : ∀ x, val G (castM !![1, w; 0, -1] *ᵥ x) = val G x := fun x => by rw [← val_act, hMG]
    have v1 := hv ![0, 1]
    have v2 := hv ![1, 1]
    rw [val_fin2' hG, val_fin2' hG] at v1 v2
    refine ⟨S, ?_⟩
    rcases hw with rfl | rfl
    · left
      simp [castM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at v1 v2
      linarith
    · right
      simp [castM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at v1 v2
      linarith
  · rintro ⟨U, hU⟩
    have key : ∀ G : Matrix (Fin 2) (Fin 2) ℝ, G.IsSymm → (G 0 1 = 0 ∨ 2 * G 0 1 = G 0 0) →
        ∃ w : ℤ, act !![1, w; 0, -1] G = G := by
      intro G hG hU
      have h10 : G 1 0 = G 0 1 := hG.apply 0 1
      rcases hU with h | h
      · refine ⟨0, ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two, h10, h]
      · refine ⟨1, ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two, h10] <;> linarith
    obtain ⟨w, hMG⟩ := key _ (isSymm_act hF U.val) hU
    have hdM : (!![1, w; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
      simp [Matrix.det_fin_two_of]
    obtain ⟨M, hM⟩ := exists_gl_of_isUnit_det _ (by rw [hdM]; exact Int.isUnit_iff.2 (Or.inr rfl))
    refine ⟨U * M * U⁻¹, ?_, ?_⟩
    · have h1 : U.val.det * (U⁻¹).val.det = 1 := by
        rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
      simp only [Units.val_mul, Matrix.det_mul, hM, hdM]
      linear_combination (-1 : ℤ) * h1
    · simp only [Units.val_mul]
      rw [act_mul, act_mul, hM, hMG, ← act_mul, Units.mul_inv, act_one]

end QuadFormsKB.Reduction
