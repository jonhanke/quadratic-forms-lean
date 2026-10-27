/-
# O'Meara Example 104:11: indefinite binary unimodular lattices over $\mathbb Z$

**Layer:** integral binary forms `QuadForm ℤ 2` (a $\mathbb Z$-lattice with a chosen base), integral equivalence
`Siegel.IntEquiv` (a change of variables in $\mathrm{GL}_2(\mathbb Z)$) and the genus `Siegel.SameGenus`
(equivalence over every $\mathbb Z_p$ and over $\mathbb R$).

O'Meara's unimodular lattice $L$ on a binary space has a symmetric integral matrix $(B(x_i, x_j))$ of determinant
$\pm 1$, with $Q(x) = B(x, x)$; as a form this is $Q = ax^2 + 2bxy + cy^2$, classically integral
(`IsClassicallyIntegral`), and the Hessian $\begin{pmatrix}2a&2b\\2b&2c\end{pmatrix}$ is twice O'Meara's matrix.
$V_\infty$ isotropic (the set of finite spots is indefinite for $V$) means $ac - b^2 < 0$, so unimodular and
indefinite together say $\det H_Q = -4$. (The determinant condition already forces the cross coefficient to be
even, so the hypothesis of classical integrality, kept to match the book, is not used in the proofs.)

**Proves** Example 104:11 (O'Meara 1973, §104, p. 321, an exercise "from first principles"):
* `omeara104_11`: such a form is equivalent over $\mathbb Z$ to $2xy$ (O'Meara's $\begin{pmatrix}0&1\\1&0\end{pmatrix}$,
  `omeara104_11H`) or to $x^2 - y^2$ ($\langle 1\rangle \perp \langle -1\rangle$);
* `omeara104_11_proper`: hence $\operatorname{cls}^+L = \operatorname{gen}L$: two such forms in the same genus are
  properly equivalent (by a matrix of determinant $1$).
-/
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Defs.Integral

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **The hyperbolic plane over $\mathbb Z$**, $2xy$ (O'Meara's matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$). -/
def omeara104_11H : QuadForm ℤ 2 := QuadForm.ofUpper ![![0, 2], ![0, 0]]

/-- Helper: the form $ax^2 + 2bxy + cy^2$. -/
private def F (a b c : ℤ) : QuadForm ℤ 2 := QuadForm.ofUpper ![![a, 2 * b], ![0, c]]

private theorem F_eval (a b c : ℤ) (x : Fin 2 → ℤ) :
    (F a b c).eval x = a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp [F, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  ring

private theorem F_map_eval {K : Type*} [CommRing K] (f : ℤ →+* K) (a b c : ℤ) (x : Fin 2 → K) :
    ((F a b c).map f).eval x = f a * x 0 ^ 2 + 2 * f b * x 0 * x 1 + f c * x 1 ^ 2 := by
  simp [F, QuadForm.map, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  ring

private theorem H_eq : omeara104_11H = F 0 1 0 := by
  simp [omeara104_11H, F]

private theorem D_eq : QuadForm.diag ![1, -1] = F 1 0 (-1) := by
  apply QuadForm.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.diag, F, QuadForm.ofUpper]

private def glMat (p q r s : ℤ) (h : p * s - q * r = 1 ∨ p * s - q * r = -1) : GL (Fin 2) ℤ :=
  Matrix.nonsingInvUnit !![p, q; r, s] (by
    rw [Matrix.det_fin_two_of]
    rcases h with h | h <;> rw [h]
    · exact isUnit_one
    · exact Int.isUnit_iff.mpr (Or.inr rfl))

private theorem glMat_val (p q r s : ℤ) (h : p * s - q * r = 1 ∨ p * s - q * r = -1) :
    (glMat p q r s h).val = !![p, q; r, s] := rfl

private theorem glMat_det (p q r s : ℤ) (h : p * s - q * r = 1 ∨ p * s - q * r = -1) :
    (glMat p q r s h).val.det = p * s - q * r := by
  rw [glMat_val, Matrix.det_fin_two_of]

private theorem eval_mat (a b c p q r s a' b' c' : ℤ) (ha : a' = a * p ^ 2 + 2 * b * p * r + c * r ^ 2)
    (hb : b' = a * p * q + b * (p * s + q * r) + c * r * s) (hc : c' = a * q ^ 2 + 2 * b * q * s + c * s ^ 2)
    (x : Fin 2 → ℤ) : (F a b c).eval (!![p, q; r, s] *ᵥ x) = (F a' b' c').eval x := by
  subst ha hb hc
  rw [F_eval, F_eval]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

private theorem intEquiv_mat (a b c p q r s a' b' c' : ℤ) (h : p * s - q * r = 1 ∨ p * s - q * r = -1)
    (ha : a' = a * p ^ 2 + 2 * b * p * r + c * r ^ 2)
    (hb : b' = a * p * q + b * (p * s + q * r) + c * r * s) (hc : c' = a * q ^ 2 + 2 * b * q * s + c * s ^ 2) :
    Siegel.IntEquiv (F a b c) (F a' b' c') :=
  ⟨glMat p q r s h, fun x => by rw [glMat_val]; exact eval_mat a b c p q r s a' b' c' ha hb hc x⟩

private theorem norm1 (c : ℤ) :
    Siegel.IntEquiv (F 0 1 c) (F 0 1 0) ∨ Siegel.IntEquiv (F 0 1 c) (F 1 0 (-1)) := by
  have h1 : Siegel.IntEquiv (F 0 1 c) (F 0 1 (c % 2)) :=
    intEquiv_mat 0 1 c 1 (-(c / 2)) 0 1 0 1 (c % 2) (Or.inl (by ring)) (by ring) (by ring)
      (by rw [Int.emod_def]; ring)
  have h2 : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · rw [h2] at h1
    exact Or.inl h1
  · rw [h2] at h1
    exact Or.inr (Siegel.IsometricGL.trans h1
      (intEquiv_mat 0 1 1 0 1 1 (-1) 1 0 (-1) (Or.inr (by ring)) (by ring) (by ring) (by ring)))

private theorem norm0 (b c : ℤ) (hb : b ^ 2 = 1) :
    Siegel.IntEquiv (F 0 b c) (F 0 1 0) ∨ Siegel.IntEquiv (F 0 b c) (F 1 0 (-1)) := by
  have h : (b - 1) * (b + 1) = 0 := by linear_combination hb
  rcases mul_eq_zero.mp h with h | h
  · have : b = 1 := by linarith
    subst this
    exact norm1 c
  · have : b = -1 := by linarith
    subst this
    have h1 : Siegel.IntEquiv (F 0 (-1) c) (F 0 1 c) :=
      intEquiv_mat 0 (-1) c (-1) 0 0 1 0 1 c (Or.inr (by ring)) (by ring) (by ring) (by ring)
    rcases norm1 c with h2 | h2
    · exact Or.inl (Siegel.IsometricGL.trans h1 h2)
    · exact Or.inr (Siegel.IsometricGL.trans h1 h2)

private theorem prim_of (a b c x y : ℤ) (hz : a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = 0) (hy : y ≠ 0) :
    ∃ u v : ℤ, IsCoprime u v ∧ a * u ^ 2 + 2 * b * u * v + c * v ^ 2 = 0 := by
  have hpos : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_right _ hy
  obtain ⟨g, m, n, hg, hmn, hm, hn⟩ := Int.exists_gcd_one' hpos
  refine ⟨m, n, Int.isCoprime_iff_gcd_eq_one.mpr hmn, ?_⟩
  have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  subst hm hn
  have : (g : ℤ) ^ 2 * (a * m ^ 2 + 2 * b * m * n + c * n ^ 2) = 0 := by linear_combination hz
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hg')

private theorem exists_prim (a b c : ℤ) (h : b ^ 2 - a * c = 1) :
    ∃ u v : ℤ, IsCoprime u v ∧ a * u ^ 2 + 2 * b * u * v + c * v ^ 2 = 0 := by
  by_cases ha : a = 0
  · exact ⟨1, 0, isCoprime_one_left, by simp [ha]⟩
  · refine prim_of a b c (1 - b) a ?_ ha
    linear_combination (-a) * h

private theorem classify (a b c : ℤ) (h : b ^ 2 - a * c = 1) :
    Siegel.IntEquiv (F a b c) (F 0 1 0) ∨ Siegel.IntEquiv (F a b c) (F 1 0 (-1)) := by
  obtain ⟨u, v, ⟨s, t, hst⟩, hz⟩ := exists_prim a b c h
  have hdet : u * s - -t * v = 1 := by linarith
  have h1 : Siegel.IntEquiv (F a b c)
      (F 0 (a * u * -t + b * (u * s + -t * v) + c * v * s) (a * t ^ 2 + 2 * b * -t * s + c * s ^ 2)) :=
    intEquiv_mat a b c u (-t) v s 0 _ _ (Or.inl hdet) hz.symm rfl (by ring)
  have e : (a * u * -t + b * (u * s + -t * v) + c * v * s) ^ 2
      - (a * u ^ 2 + 2 * b * u * v + c * v ^ 2) * (a * t ^ 2 + 2 * b * -t * s + c * s ^ 2)
      = (b ^ 2 - a * c) * (u * s - -t * v) ^ 2 := by ring
  rw [hz, hdet, h] at e
  have hb1 : (a * u * -t + b * (u * s + -t * v) + c * v * s) ^ 2 = 1 := by linarith
  rcases norm0 _ _ hb1 with h2 | h2
  · exact Or.inl (Siegel.IsometricGL.trans h1 h2)
  · exact Or.inr (Siegel.IsometricGL.trans h1 h2)

private theorem exists_F (Q : QuadForm ℤ 2) (hdet : Q.hessian.det = -4) :
    ∃ a b c : ℤ, Q = F a b c ∧ b ^ 2 - a * c = 1 := by
  have h10 : Q.coeff 1 0 = 0 := Q.upper (show id (0 : Fin 2) < id 1 by decide)
  simp [QuadForm.hessian, Matrix.det_fin_two, h10] at hdet
  have h2 : (2 : ℤ) ∣ Q.coeff 0 1 ^ 2 := ⟨2 * (Q.coeff 0 0 * Q.coeff 1 1 + 1), by linarith⟩
  obtain ⟨b, hb⟩ := Int.prime_two.dvd_of_dvd_pow h2
  refine ⟨Q.coeff 0 0, b, Q.coeff 1 1, ?_, ?_⟩
  · apply QuadForm.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [F, QuadForm.ofUpper, h10, hb]
  · rw [hb] at hdet h2
    nlinarith

private theorem improper_aut (Q : QuadForm ℤ 2)
    (h : Siegel.IntEquiv Q omeara104_11H ∨ Siegel.IntEquiv Q (QuadForm.diag ![1, -1])) :
    ∃ τ : GL (Fin 2) ℤ, τ.val.det = -1 ∧ ∀ x, Q.eval (τ.val *ᵥ x) = Q.eval x := by
  have key : ∀ R : QuadForm ℤ 2,
      (∃ σ : GL (Fin 2) ℤ, σ.val.det = -1 ∧ ∀ x, R.eval (σ.val *ᵥ x) = R.eval x) →
      Siegel.IntEquiv Q R → ∃ τ : GL (Fin 2) ℤ, τ.val.det = -1 ∧ ∀ x, Q.eval (τ.val *ᵥ x) = Q.eval x := by
    rintro R ⟨σ, hσd, hσ⟩ ⟨e, he⟩
    have hinv : ∀ y, Q.eval y = R.eval ((e⁻¹).val *ᵥ y) := fun y => by
      rw [← he, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨e * σ * e⁻¹, ?_, fun x => ?_⟩
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hσd]
      have : e.val.det * (e⁻¹).val.det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      linear_combination (-1) * this
    · simp only [Units.val_mul, ← mulVec_mulVec]
      rw [he, hσ, hinv x]
  rcases h with h | h
  · refine key _ ⟨glMat 0 1 1 0 (Or.inr (by norm_num)), by rw [glMat_det]; norm_num, fun x => ?_⟩ h
    rw [H_eq, glMat_val]
    exact eval_mat 0 1 0 0 1 1 0 0 1 0 (by ring) (by ring) (by ring) x
  · refine key _ ⟨glMat 1 0 0 (-1) (Or.inr (by norm_num)), by rw [glMat_det]; norm_num, fun x => ?_⟩ h
    rw [D_eq, glMat_val]
    exact eval_mat 1 0 (-1) 1 0 0 (-1) 1 0 (-1) (by ring) (by ring) (by ring) x

private theorem no_mixed {Q Q' : QuadForm ℤ 2} (hgen : Siegel.SameGenus Q Q')
    (h1 : Siegel.IntEquiv Q omeara104_11H) (h2 : Siegel.IntEquiv Q' (QuadForm.diag ![1, -1])) : False := by
  have e1 := Siegel.IsometricGL.map (Int.castRingHom ℤ_[2]) h1
  have e2 := Siegel.IsometricGL.map (Int.castRingHom ℤ_[2]) h2
  have e : Siegel.IsometricGL (omeara104_11H.map (Int.castRingHom ℤ_[2]))
      ((QuadForm.diag ![1, -1]).map (Int.castRingHom ℤ_[2])) :=
    Siegel.IsometricGL.trans (Siegel.IsometricGL.trans e1.symm (hgen.1 2)) e2
  obtain ⟨g, hg⟩ := e
  have := hg ![1, 0]
  rw [H_eq, D_eq, F_map_eval, F_map_eval] at this
  simp at this
  have hu : IsUnit (2 : ℤ_[2]) :=
    isUnit_iff_exists_inv.mpr ⟨g.val 0 0 * g.val 1 0, by linear_combination this⟩
  exact PadicInt.p_nonunit (p := 2) (by simpa using hu)

/-- **Example 104:11, classification** (O'Meara 1973, §104, p. 321): a classically integral binary form over
$\mathbb Z$ whose Hessian has determinant $-4$ (a unimodular lattice on an indefinite binary space) is equivalent over
$\mathbb Z$ to $2xy$ or to $x^2 - y^2$. -/
@[kb "omeara1963" "§104, 104:11, p. 321 (L ≅ ⟨1⟩ ⊥ ⟨−1⟩ or (0 1; 1 0))"]
theorem omeara104_11 (Q : QuadForm ℤ 2) (hQ : IsClassicallyIntegral Q) (hdet : Q.hessian.det = -4) :
    Siegel.IntEquiv Q omeara104_11H ∨ Siegel.IntEquiv Q (QuadForm.diag ![1, -1]) := by
  obtain ⟨a, b, c, rfl, h⟩ := exists_F Q hdet
  rw [H_eq, D_eq]
  exact classify a b c h

/-- **Example 104:11, $\operatorname{cls}^+L = \operatorname{gen}L$** (O'Meara 1973, §104, p. 321): two classically
integral binary forms with Hessian determinant $-4$ in the same genus are properly equivalent over $\mathbb Z$. -/
@[kb "omeara1963" "§104, 104:11, p. 321 (cls⁺ L = gen L)"]
theorem omeara104_11_proper (Q Q' : QuadForm ℤ 2) (hQ : IsClassicallyIntegral Q) (hdet : Q.hessian.det = -4)
    (hQ' : IsClassicallyIntegral Q') (hdet' : Q'.hessian.det = -4) (hgen : Siegel.SameGenus Q Q') :
    ∃ g : GL (Fin 2) ℤ, g.val.det = 1 ∧ ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x := by
  have h1 := omeara104_11 Q hQ hdet
  have h2 := omeara104_11 Q' hQ' hdet'
  have hQQ : Siegel.IntEquiv Q Q' := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Siegel.IsometricGL.trans h1 (Siegel.IsometricGL.symm h2)
    · exact (no_mixed hgen h1 h2).elim
    · exact (no_mixed hgen.symm h2 h1).elim
    · exact Siegel.IsometricGL.trans h1 (Siegel.IsometricGL.symm h2)
  obtain ⟨g, hg⟩ := hQQ
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rcases Int.isUnit_iff.mp hu with hd | hd
  · exact ⟨g, hd, hg⟩
  · obtain ⟨τ, hτd, hτ⟩ := improper_aut Q h1
    refine ⟨τ * g, ?_, fun x => ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hτd, hd]; norm_num
    · rw [Units.val_mul, ← mulVec_mulVec, hτ, hg]

end QuadFormsKB.Lattices
