import QuadFormsKB.Tamagawa.Measure.Weil.BinaryAdelic
import QuadFormsKB.Tamagawa.Measure.Weil.BinarySimilar

/-!
# Binary $\tau = 2$: reduction to $\langle1,D\rangle$, every totally definite form, non-vacuity
**Layer:** number fields. $F$ a number field, $Q_0 = ax_0^2+bx_0x_1+cx_1^2$ a binary form over $\mathcal O_F$,
$D = \det H_{Q_0} = 4ac-b^2$.

**Defines**
* `IsTotallyDefinite Q₀` (a condition): $Q_0$ is positive or negative definite at every real place (signs may differ
  from place to place).

**Proves**
* `anisotropicF_iff_not_isSquare`: $Q_0\otimes F$ is anisotropic iff $-\det H = b^2-4ac$ is not a square in $F$;
  `exists_isDiscField_of_anisotropicF`: every anisotropic $Q_0$ has a discriminant field (every number field);
* **`tauTwoBinaryAdelic_iff_diagForm1`**: for $a\ne0$, $\tau = 2$ for $Q_0$ iff $\tau = 2$ for $\langle1,D\rangle$
  (completion of the square $\langle1,D\rangle\circ\begin{pmatrix}2a&b\\0&1\end{pmatrix} = 4a\,Q_0$ and similarity invariance),
  hence **`tauTwoBinaryAll_iff_diagForm1`**: the headline target over $F$ is equivalent to its case $\langle1,D\rangle$,
  $-D$ not a square;
* **`tauTwo_binary_totallyDefinite`** (unconditional): $\tau(SO(V)) = 2$ for every totally definite binary form over every
  totally real field ($a\,Q_0$ is totally positive definite, then `tauTwo_binary_totallyPosDef` and similarity);
* non-vacuity: `isTotallyDefinite_of_isTotallyPosDef`, `exists_not_isSquare` (every number field has a non-square
  algebraic integer), `exists_anisotropicF_binary` (every number field has anisotropic binary forms).
-/

open MeasureTheory Measure Set Topology Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular QuadFormsKB.QuadForm QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F]

/-! ### The discriminant field under a change of the determinant by a square -/

theorem isDiscField_of_det {Q Q' : QuadForm (𝓞 F) 2} {E : Type} [Field E] [NumberField E] [Algebra F E]
    (h : IsDiscField Q E) {u : F} (hu : u ≠ 0)
    (hdet : algebraMap (𝓞 F) F Q'.hessian.det = u ^ 2 * algebraMap (𝓞 F) F Q.hessian.det) :
    IsDiscField Q' E := by
  obtain ⟨s, hs, hsF⟩ := h.exists_sqrt
  refine ⟨h.finrank_eq_two, algebraMap F E u * s, ?_, ?_⟩
  · rw [mul_pow, hs, ← map_pow, ← map_mul]
    congr 1
    rw [map_neg, map_neg, hdet]; ring
  · rintro ⟨r, hr⟩
    apply hsF
    refine ⟨r / u, ?_⟩
    rw [map_div₀, hr, mul_div_cancel_left₀ _ ((map_ne_zero _).mpr hu)]

/-- The covolume depends only on the form (not on the nondegeneracy proof). -/
theorem covolume_muTamBin_congr_form {Q Q' : QuadForm (𝓞 F) 2} (h : Q = Q') (hQ : Q.Nondegenerate)
    (hQ' : Q'.Nondegenerate) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    covolume (GammaSOAdele Q) (SOAdele Q) (muTamBin Q hQ E) =
      covolume (GammaSOAdele Q') (SOAdele Q') (muTamBin Q' hQ' E) := by
  subst h; rfl

/-! ### Reduction to $\langle1,D\rangle$ -/

theorem nondegenerate_diagForm1 {D : 𝓞 F} (hD : D ≠ 0) : (diagForm1 D).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_det_diagForm1]
  exact mul_ne_zero (by norm_num) hD

/-- **Reduction to the forms $\langle1,D\rangle$** ($D = \det H_{Q_0}$, $a = Q_0(e_0)\ne0$): $\tau = 2$ holds for $Q_0$
iff it holds for $\langle1,D\rangle$. -/
theorem tauTwoBinaryAdelic_iff_diagForm1 (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (ha : Q₀.coeff 0 0 ≠ 0) :
    TauTwoBinaryAdelic Q₀ hQ ↔ TauTwoBinaryAdelic (diagForm1 Q₀.hessian.det) (nondegenerate_diagForm1 hQ) := by
  set X := diagForm1 Q₀.hessian.det
  have hX : X.Nondegenerate := nondegenerate_diagForm1 hQ
  set M : Matrix (Fin 2) (Fin 2) (𝓞 F) := !![2 * Q₀.coeff 0 0, Q₀.coeff 0 1; 0, 1]
  have hM : M.det ≠ 0 := by
    simp only [M, Matrix.det_fin_two_of]; simpa using mul_ne_zero two_ne_zero ha
  have h4a : (4 * Q₀.coeff 0 0 : 𝓞 F) ≠ 0 := mul_ne_zero (by norm_num) ha
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  have hY : simForm X 1 M = simForm Q₀ (4 * Q₀.coeff 0 0) 1 := by
    rw [simForm, simForm, diagForm1_compMat Q₀, compMat_one]
    ext i j; simp
  -- the determinants: det H_X = 4 det H_Q
  have hdet : algebraMap (𝓞 F) F X.hessian.det = (2 : F) ^ 2 * algebraMap (𝓞 F) F Q₀.hessian.det := by
    rw [hessian_det_diagForm1, map_mul, map_ofNat]; norm_num
  have hdet' : algebraMap (𝓞 F) F Q₀.hessian.det = ((2 : F)⁻¹) ^ 2 * algebraMap (𝓞 F) F X.hessian.det := by
    rw [hdet, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (two_ne_zero : (2 : F) ≠ 0), one_pow, one_mul]
  constructor
  · intro hτ E _ _ _ hE
    have hE₀ : IsDiscField Q₀ E := isDiscField_of_det hE (inv_ne_zero two_ne_zero) hdet'
    rw [← covolume_muTamBin_simForm hX one_ne_zero hM hE,
      covolume_muTamBin_congr_form hY _ (nondegenerate_simForm hQ h4a h1) E,
      covolume_muTamBin_simForm hQ h4a h1 hE₀]
    exact hτ E hE₀
  · intro hτ E _ _ _ hE
    have hEX : IsDiscField X E := isDiscField_of_det hE two_ne_zero hdet
    rw [← covolume_muTamBin_simForm hQ h4a h1 hE,
      ← covolume_muTamBin_congr_form hY (nondegenerate_simForm hX one_ne_zero hM) _ E,
      covolume_muTamBin_simForm hX one_ne_zero hM hEX]
    exact hτ E hEX

/-! ### Anisotropy -/

/-- **An anisotropic binary form** has $a = Q_0(e_0)\ne0$. -/
theorem coeff_zero_zero_ne_zero_of_anisotropicF {Q₀ : QuadForm (𝓞 F) 2} (h : AnisotropicF Q₀) :
    Q₀.coeff 0 0 ≠ 0 := by
  intro h0
  have := h ![1, 0] (by
    simp [qF, QuadForm.map, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, h0])
  simpa using congrFun this 0

/-- **Anisotropy and the discriminant:** $Q_0\otimes F$ is anisotropic iff $-\det H_{Q_0} = b^2-4ac$ is not a square in $F$. -/
@[kb "omeara1963" "§42 (binary spaces: isotropic iff −det is a square) [unverified]"]
theorem anisotropicF_iff_not_isSquare (Q₀ : QuadForm (𝓞 F) 2) :
    AnisotropicF Q₀ ↔ ¬ IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)) := by
  have h10 : Q₀.coeff 1 0 = 0 := Q₀.upper (show (0:Fin 2) < 1 by decide)
  set a : F := algebraMap (𝓞 F) F (Q₀.coeff 0 0) with ha
  set b : F := algebraMap (𝓞 F) F (Q₀.coeff 0 1) with hb
  set c : F := algebraMap (𝓞 F) F (Q₀.coeff 1 1) with hc
  have hq : ∀ ξ : Fin 2 → F, qF Q₀ ξ = a * ξ 0 ^ 2 + b * ξ 0 * ξ 1 + c * ξ 1 ^ 2 := by
    intro ξ
    simp [qF, QuadForm.map, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, ha, hb, hc]
    ring
  have hd : algebraMap (𝓞 F) F (-Q₀.hessian.det) = b ^ 2 - 4 * a * c := by
    simp [QuadForm.hessian, Matrix.det_fin_two, h10, ha, hb, hc]
    ring
  rw [hd]
  constructor
  · rintro hA ⟨r, hr⟩
    by_cases ha0 : a = 0
    · have := hA ![1, 0] (by rw [hq]; simp [ha0])
      have h := congrFun this 0
      simp at h
    · have := hA ![r - b, 2 * a] (by
        rw [hq]; simp
        linear_combination (-a) * hr)
      have h := congrFun this 1
      simp at h
      exact ha0 h
  · intro hN ξ hξ
    rw [hq] at hξ
    by_contra hne
    apply hN
    by_cases ha0 : a = 0
    · exact ⟨b, by rw [ha0]; ring⟩
    · have hy : ξ 1 ≠ 0 := by
        intro hy
        rw [hy] at hξ
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hξ
        have : ξ 0 = 0 := by
          have : a * ξ 0 ^ 2 = 0 := hξ
          simpa [ha0] using this
        apply hne
        ext i; fin_cases i <;> simp [*]
      refine ⟨(2 * a * ξ 0 + b * ξ 1) / ξ 1, ?_⟩
      field_simp
      linear_combination (-4 * a) * hξ

theorem nondegenerate_of_anisotropicF {Q₀ : QuadForm (𝓞 F) 2} (h : AnisotropicF Q₀) : Q₀.Nondegenerate := by
  intro h0
  apply (anisotropicF_iff_not_isSquare Q₀).mp h
  rw [h0, neg_zero, map_zero]
  exact ⟨0, by rw [mul_zero]⟩

/-- **Every anisotropic binary form has a discriminant field** (every number field). -/
theorem exists_isDiscField_of_anisotropicF {Q₀ : QuadForm (𝓞 F) 2} (h : AnisotropicF Q₀) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E), IsDiscField Q₀ E :=
  exists_isDiscField Q₀ ((anisotropicF_iff_not_isSquare Q₀).mp h)

theorem anisotropicF_diagForm1_iff (D : 𝓞 F) :
    AnisotropicF (diagForm1 D) ↔ ¬ IsSquare (algebraMap (𝓞 F) F (-D)) := by
  rw [anisotropicF_iff_not_isSquare, hessian_det_diagForm1]
  have e : algebraMap (𝓞 F) F (-(4 * D)) = 4 * algebraMap (𝓞 F) F (-D) := by
    simp only [map_neg, map_mul, map_ofNat]; ring
  rw [e]
  constructor
  · rintro h ⟨r, hr⟩
    refine h ⟨2 * r, ?_⟩
    rw [hr]; ring
  · rintro h ⟨r, hr⟩
    refine h ⟨r / 2, ?_⟩
    field_simp
    linear_combination hr

/-- **The headline target over $F$ is equivalent to its case $\langle1,D\rangle$** ($-D$ not a square). -/
theorem tauTwoBinaryAll_iff_diagForm1 :
    TauTwoBinaryAll F ↔ ∀ (D : 𝓞 F) (hD : ¬ IsSquare (algebraMap (𝓞 F) F (-D))),
      TauTwoBinaryAdelic (diagForm1 D) (nondegenerate_of_anisotropicF ((anisotropicF_diagForm1_iff D).mpr hD)) := by
  constructor
  · intro h D hD
    exact h _ _ ((anisotropicF_diagForm1_iff D).mpr hD)
  · intro h Q₀ hQ hani
    have ha := coeff_zero_zero_ne_zero_of_anisotropicF hani
    rw [tauTwoBinaryAdelic_iff_diagForm1 Q₀ hQ ha]
    have hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)) := (anisotropicF_iff_not_isSquare Q₀).mp hani
    exact h _ hsq

/-! ### Totally definite forms over a totally real field -/

/-- **$Q_0$ is totally definite** (a condition): at every real place $w$ the real form $Q^{\sigma_w}$ is positive definite
or negative definite (the sign may depend on $w$). Over a totally real field this is the case where
$SO(V)(F\otimes\mathbb R)$ is compact. -/
def IsTotallyDefinite (Q₀ : QuadForm (𝓞 F) 2) : Prop :=
  ∀ w : {w : InfinitePlace F // w.IsReal},
    IsPosDefR (QRe Q₀ w) ∨ ∀ y : Fin 2 → ℝ, y ≠ 0 → (QRe Q₀ w).eval y < 0

theorem eval_QRe_comp [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 2) (σ : F →ₐ[ℚ] ℂ) (x : Fin 2 → F) :
    (QRe Q₀ (realPlaceEquiv σ)).eval (fun i => realEmb σ (x i)) = realEmb σ ((formF Q₀).eval x) := by
  rw [← realQ_eq_QRe Q₀ (rfl : realPlaceEquiv σ = _)]
  exact QuadFormsKB.Tamagawa.Measure.eval_map_real Q₀ (realEmb σ) x

/-- **A totally definite form times $a = Q_0(e_0)$ is totally positive definite.** -/
theorem isTotallyPosDef_smul_of_isTotallyDefinite [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) 2}
    (h : IsTotallyDefinite Q₀) : IsTotallyPosDef (formF (Q₀.coeff 0 0 • Q₀)) := by
  intro x hx σ
  set w := realPlaceEquiv σ
  set ρ := realEmb σ
  have e : (formF (Q₀.coeff 0 0 • Q₀)).eval x
      = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * (formF Q₀).eval x := by
    rw [show formF (Q₀.coeff 0 0 • Q₀) = (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) • formF Q₀ from by
      ext i j; simp [formF, QuadForm.map]]
    simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      Algebra.algebraMap_self, RingHom.id_apply, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have ha : (formF Q₀).eval ![1, 0] = algebraMap (𝓞 F) F (Q₀.coeff 0 0) := by
    simp [formF, QuadForm.map, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]
  have hy : (fun i => ρ (x i)) ≠ 0 := by
    intro h0; apply hx; funext i
    exact ρ.injective (by simpa using congrFun h0 i)
  have hy1 : (fun i => ρ ((![1, 0] : Fin 2 → F) i)) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have h1 := eval_QRe_comp Q₀ σ x
  have h2 := eval_QRe_comp Q₀ σ ![1, 0]
  rw [ha] at h2
  rw [e, map_mul, ← realEmb_apply, ← realEmb_apply, ← h1, ← h2]
  rw [← Complex.ofReal_mul, Complex.zero_lt_real]
  rcases h w with hp | hn
  · exact mul_pos (hp _ hy1) (hp _ hy)
  · exact mul_pos_of_neg_of_neg (hn _ hy1) (hn _ hy)

theorem coeff_zero_zero_ne_zero_of_isTotallyDefinite [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) 2}
    (h : IsTotallyDefinite Q₀) : Q₀.coeff 0 0 ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (F →ₐ[ℚ] ℂ) := Fintype.card_pos_iff.mp card_embeddings_pos
  intro h0
  have h2 := eval_QRe_comp Q₀ σ ![1, 0]
  have ha : (formF Q₀).eval ![1, 0] = algebraMap (𝓞 F) F (Q₀.coeff 0 0) := by
    simp [formF, QuadForm.map, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]
  rw [ha, h0, map_zero, map_zero] at h2
  have hy1 : (fun i => realEmb σ ((![1, 0] : Fin 2 → F) i)) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  rcases h (realPlaceEquiv σ) with hp | hn
  · exact (hp _ hy1).ne' h2
  · exact (hn _ hy1).ne h2

/-- **A totally positive definite form is totally definite.** -/
theorem isTotallyDefinite_of_isTotallyPosDef [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) 2}
    (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (formF Q₀)) : IsTotallyDefinite Q₀ :=
  fun w => Or.inl (isPosDefR_QRe Q₀ hQ hpd w)

/-- **$\tau(SO(V)) = 2$ for every totally definite binary form over every totally real field, adelic form**
(unconditional; every sign pattern at the real places): the covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for Weil's
Tamagawa measure with the convergence factors $L_v(1,\chi_E)$ is $2$. *Proof:* $aQ_0$ is totally positive definite
(`isTotallyPosDef_smul_of_isTotallyDefinite`), `tauTwo_binary_totallyPosDef` for it, and similarity invariance
(`tauTwoBinaryAdelic_simForm_iff`, $c = a$, $G = 1$). -/
@[kb "weil1982" "§2.4, p. 23; Thm. 3.7.1 (τ = 2), rank 2 with convergence factors; ono1963 [unverified]"]
theorem tauTwo_binary_totallyDefinite [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate)
    (hdef : IsTotallyDefinite Q₀) : TauTwoBinaryAdelic Q₀ hQ := by
  have ha := coeff_zero_zero_ne_zero_of_isTotallyDefinite hdef
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  have hY : simForm Q₀ (Q₀.coeff 0 0) 1 = Q₀.coeff 0 0 • Q₀ := by rw [simForm, compMat_one]
  have hpd := isTotallyPosDef_smul_of_isTotallyDefinite hdef
  have hY' : (Q₀.coeff 0 0 • Q₀).Nondegenerate := hY ▸ nondegenerate_simForm hQ ha h1
  refine (tauTwoBinaryAdelic_simForm_iff hQ ha h1).mp fun E _ _ _ hE => ?_
  rw [covolume_muTamBin_congr_form hY _ hY' E]
  refine tauTwo_binary_totallyPosDef _ hY' hpd E ?_
  exact hY ▸ isDiscField_simForm hE ha h1

/-! ### Non-vacuity -/

/-- **Every number field has a non-square algebraic integer** (e.g. an element of valuation $1$ at some prime). -/
theorem exists_not_isSquare (F : Type) [Field F] [NumberField F] :
    ∃ x : 𝓞 F, ¬ IsSquare (algebraMap (𝓞 F) F x) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  have hMb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hMb⟩
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
  refine ⟨π, ?_⟩
  rintro ⟨r, hr⟩
  have h := congrArg (v.valuation F) hr
  rw [hπ, map_mul] at h
  have h' : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) = v.valuation F r * v.valuation F r := h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v.valuation F r = WithZero.exp m := by
    have : v.valuation F r ≠ 0 := by
      intro h0; rw [h0] at h'; simp at h'
    exact ⟨_, (WithZero.coe_unzero this).symm⟩
  rw [hm, ← WithZero.exp_add] at h'
  have := WithZero.exp_injective h'
  omega

/-- **Every number field has anisotropic binary forms**: $\langle1,-x\rangle$ for a non-square $x$. -/
theorem exists_anisotropicF_binary (F : Type) [Field F] [NumberField F] :
    ∃ Q₀ : QuadForm (𝓞 F) 2, AnisotropicF Q₀ := by
  obtain ⟨x, hx⟩ := exists_not_isSquare F
  exact ⟨diagForm1 (-x), (anisotropicF_diagForm1_iff _).mpr (by rwa [neg_neg])⟩

end QuadFormsKB.Tamagawa.Measure.Weil
