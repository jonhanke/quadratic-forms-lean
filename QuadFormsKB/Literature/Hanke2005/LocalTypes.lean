/-
# Hanke 2005, §3 and §6: the local types of maximal lattices and similitudes of odd multiplier (proved)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves** the two former named inputs, at every finite place of every number field $F$, dyadic places included:
* `shimuraMaximalTypes : ShimuraMaximalTypes F` (Hanke thesis, §3, p. 8 and the proof of Theorem 5.1, pp. 17–18;
  [Shi, §3]; O'Meara §§92–93):
  - `selfDual`: if $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = 1$ ($\det H$ a unit), then $t_\mathfrak p\le2$
    (`anisoDim_le_two_of_dualIndexAt_eq_one`: non-dyadic, $\Lambda_\mathfrak p\cong\langle$units$\rangle$, O'Meara 92:1; dyadic,
    $\Lambda_\mathfrak p$ is an orthogonal sum of unimodular binary blocks, O'Meara 93:15) and, for $n$ even, $\mathfrak p$ is
    unramified in $K$ (`not_isRamifiedAt_of_dualIndexAt_eq_one`). Maximality is not needed for this field.
  - `even_two_iff`: for $n$ even, $t_\mathfrak p = 2$ iff $\delta$ is not a square in $F_\mathfrak p$ (`anisoDim_eq_two_iff`;
    `even_disc_of_anisoDim` with `LocalRankFive.isotropic_four_of_not_isSquare`). Neither maximality nor
    self-duality is needed.
* `similitudeOddMultiplier : SimilitudeOddMultiplier F` (proof of Theorem 6.3, p. 21, with [Shi, §3.2]): for $n\ge3$
  even, at a place with $t_\mathfrak p = 0$, or $t_\mathfrak p = 2$ and $\mathfrak p$ ramified in $K$, or $t_\mathfrak p = 4$,
  the Gram matrix has a similitude whose multiplier has valuation $1$ (`exists_mult_val_one`). The similitude is built on
  the normal form $\mathbb H^w\perp\langle a\rangle$ (`exists_witt_diag`): scaling on $\mathbb H^w$; on $\langle a\rangle$
  nothing ($t = 0$), multiplication by an element of $F_\mathfrak p(\sqrt{-a_1/a_0})$ of norm of valuation $1$ ($t = 2$,
  ramified: `exists_val_one_hilbert_of_not_isUnramSqrt`), left multiplication by a quaternion of reduced norm $\pi$
  ($t = 4$: the anisotropic quaternary form is a multiple of a quaternion norm form and is universal).
-/
import QuadFormsKB.Literature.Hanke2005.SelfDualNondyadic
import QuadFormsKB.Literature.Hanke2005.SelfDualDyadic
import QuadFormsKB.Literature.Hanke2005.SimilitudeModels
import QuadFormsKB.Literature.Hanke2005.Sec6Defs

open NumberField IsDedekindDomain QuadraticMap QuadraticForm Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Bookkeeping: the form over $F_\mathfrak p$ -/

theorem QV_eq_Qf (Q₀ : QuadForm (𝓞 F) n) : Tamagawa.Measure.LerayPadic.QV v Q₀ = Qf v Q₀ := by
  apply QuadForm.ext
  ext i j
  simp [QuadForm.map, NF.Qp]
  rfl

theorem anisoDim_eq (Q₀ : QuadForm (𝓞 F) n) :
    anisoDim v Q₀ = n - 2 * wittIndex (Qf v Q₀).toQuadraticForm := by
  unfold anisoDim; rw [QV_eq_Qf]

theorem det_hessian_Qf (Q₀ : QuadForm (𝓞 F) n) :
    (Qf v Q₀).hessian.det = algebraMap F Fv ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) := by
  rw [hessian_Qf, hessV, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem algebraMap_discK (Q₀ : QuadForm (𝓞 F) n) :
    algebraMap F Fv (discK Q₀) = (-1) ^ (n / 2) * (Qf v Q₀).hessian.det / 2 ^ n := by
  rw [det_hessian_Qf, discK]
  simp [map_mul, map_div₀, map_pow, map_neg, map_one, mul_div_assoc, map_ofNat]

theorem isSquare_algebraMap_discK_iff (Q₀ : QuadForm (𝓞 F) n) (hn : Even n) :
    IsSquare (algebraMap F Fv (discK Q₀)) ↔ IsSquare ((-1) ^ (n / 2) * (Qf v Q₀).hessian.det) := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : (2 : Fv) ^ (m + m) = (2 ^ m) ^ 2 := by ring
  have h2m : (2 : Fv) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [algebraMap_discK, h2]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r * 2 ^ m, ?_⟩
    rw [div_eq_iff (pow_ne_zero _ h2m)] at hr
    rw [hr]; ring
  · rintro ⟨r, hr⟩
    refine ⟨r / 2 ^ m, ?_⟩
    rw [hr]; field_simp

theorem nondegenerate_Qf' (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : (Qf v Q₀).Nondegenerate :=
  nondegenerate_Qf v Q₀ hQ

theorem anisoDim_parity (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    anisoDim v Q₀ % 2 = n % 2 := by
  have hw := two_mul_wittIndex_le v Q₀ hQ
  unfold anisoDim; omega

/-! ### `even_two_iff` -/

/-- Every diagonal quaternary form over $F_\mathfrak p$ of non-square determinant is isotropic. -/
theorem quat_hyp : ∀ b : Fin 4 → Fv, (∀ i, b i ≠ 0) → ¬ IsSquare (b 0 * b 1 * b 2 * b 3) →
    ∃ x : Fin 4 → Fv, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0 := by
  intro b hb hd
  obtain ⟨x, hx, h0⟩ := LocalRankFive.isotropic_four_of_not_isSquare v b hb hd
  refine ⟨x, hx, ?_⟩
  rw [LocalRankFive.evalIn_diag_four] at h0
  rw [Fin.sum_univ_four]; exact h0

/-- **$t_\mathfrak p = 2$ iff $\delta$ is not a square in $F_\mathfrak p$** ($n$ even; Hanke thesis, §3, p. 8 and the remark
after Theorem 6.3, p. 21). -/
@[kb "hanke2005crelle" "§3, p. 8; remark after Theorem 6.3, p. 21 (t_p = 2 iff K_p is a field, n even)"]
theorem anisoDim_eq_two_iff (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : Even n) :
    anisoDim v Q₀ = 2 ↔ ¬ IsSquare (algebraMap F Fv (discK Q₀)) := by
  have hQf := nondegenerate_Qf v Q₀ hQ
  obtain ⟨h0, h2, h4⟩ := even_disc_of_anisoDim (two_ne_zero : (2 : Fv) ≠ 0) (Qf v Q₀) hQf hn
  have h4' := h4 (quat_hyp v)
  have hle := anisoDim_le_four v Q₀ hQ
  have hpar := anisoDim_parity v Q₀ hQ
  rw [isSquare_algebraMap_discK_iff v Q₀ hn]
  rw [anisoDim_eq] at hle hpar ⊢
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hn
  constructor
  · exact h2
  · intro hns
    by_contra hne
    have : n - 2 * wittIndex (Qf v Q₀).toQuadraticForm = 0 ∨ n - 2 * wittIndex (Qf v Q₀).toQuadraticForm = 4 := by
      omega
    rcases this with h | h
    · exact hns (h0 h)
    · exact hns (h4' h)

/-! ### `selfDual` -/

/-- A $\mathrm{GL}_n(\mathfrak o)$-equivalence gives an equivalence of the forms over $F_\mathfrak p$. -/
theorem equivalent_map_of_isGLEquiv {Q Q' : QuadForm 𝔬 n} (h : DVR.IsGLEquiv Q Q') :
    (Q.map (algebraMap 𝔬 Fv)).toQuadraticForm.Equivalent (Q'.map (algebraMap 𝔬 Fv)).toQuadraticForm := by
  obtain ⟨U, hU, hQ⟩ := h
  have hH := DVR.hessian_eq_of_eval hQ
  set UK : Matrix (Fin n) (Fin n) Fv := U.map (algebraMap 𝔬 Fv)
  have hUK : IsUnit UK.det := by
    rw [show UK.det = algebraMap 𝔬 Fv U.det from (RingHom.map_det _ _).symm]
    exact hU.map _
  have hmapH : ∀ P : QuadForm 𝔬 n, (P.map (algebraMap 𝔬 Fv)).hessian = P.hessian.map (algebraMap 𝔬 Fv) := by
    intro P; ext i j; simp [QuadForm.hessian, QuadForm.map]
  have hHK : (Q'.map (algebraMap 𝔬 Fv)).hessian = UKᵀ * (Q.map (algebraMap 𝔬 Fv)).hessian * UK := by
    rw [hmapH, hmapH, hH]
    simp [UK, Matrix.map_mul, Matrix.transpose_map]
  have heval : ∀ x : Fin n → Fv, (Q.map (algebraMap 𝔬 Fv)).eval (UK *ᵥ x) = (Q'.map (algebraMap 𝔬 Fv)).eval x := by
    intro x
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    rw [two_mul_eval_gen, two_mul_eval_gen, hHK, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x UKᵀ,
      vecMul_transpose]
  let := UK.invertibleOfIsUnitDet hUK
  refine ⟨⟨(UK.toLinearEquiv' this).symm, fun x => ?_⟩⟩
  rw [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply, ← heval]
  congr 1
  have h := (UK.toLinearEquiv' this).apply_symm_apply x
  simpa using h

theorem radical_eq_bot_map (Q : QuadForm 𝔬 n) (hQ : (Q.map (algebraMap 𝔬 Fv)).Nondegenerate) :
    (Q.map (algebraMap 𝔬 Fv)).toQuadraticForm.radical = ⊥ :=
  QuadraticForm.radical_eq_bot_of_nondegenerate _ (polar_nondeg_toQuadraticForm _ hQ)

/-- **At a self-dual place the anisotropic kernel has dimension at most $2$** (Hanke thesis, §3, p. 8; O'Meara 92:1
and 93:15). -/
@[kb "hanke2005crelle" "§3, p. 8; proof of Theorem 5.1, pp. 17–18 (Λ̃_p = Λ_p ⇒ t_p ≤ 2)"]
theorem anisoDim_le_two_of_dualIndexAt_eq_one (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (h : dualIndexAt v Q₀ = 1) : anisoDim v Q₀ ≤ 2 := by
  have hdet := isUnit_det_of_dualIndexAt_eq_one v Q₀ h
  have hπ := NF.irreducible_π v
  have hw := two_mul_wittIndex_le v Q₀ hQ
  have hQV : (Tamagawa.Measure.LerayPadic.QV v Q₀) = (NF.Qp v Q₀).map (algebraMap 𝔬 Fv) := rfl
  have hnd : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).Nondegenerate := by
    rw [← hQV, QV_eq_Qf]; exact nondegenerate_Qf v Q₀ hQ
  unfold anisoDim at hw ⊢
  rw [hQV] at hw ⊢
  by_cases h2 : IsUnit (2 : 𝔬)
  · have h2' : ¬ NF.π v ∣ 2 := fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd h2)
    have hdet' : ¬ NF.π v ∣ (NF.Qp v Q₀).hessian.det := fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd hdet)
    obtain ⟨a, ha, hE, -⟩ := DVR.exists_diag_of_unimodular (NF.Qp v Q₀) (NF.π v) hπ h2' hdet'
    have hau : ∀ i, IsUnit (a i) := fun i => by
      by_contra hn
      exact hn (DVR.dvr_isUnit_of_not_dvd hπ (ha i))
    have h1 := wittIndex_eq_of_equivalent (equivalent_map_of_isGLEquiv v hE) (radical_eq_bot_map v _ hnd)
    have h3 := wittIndex_diag_units v h2 n a hau
    rw [← h1] at h3
    omega
  · have h2d : NF.π v ∣ 2 := by
      by_contra hd
      exact h2 (DVR.dvr_isUnit_of_not_dvd hπ hd)
    obtain ⟨r, A, hr, hb, hE⟩ := DVR.exists_pairSum_of_isLocalLevel_zero (NF.Qp v Q₀) hπ h2d (NF.two_ne_zero' v)
      (isLocalLevel_zero_of_isUnit_det _ _ hdet)
    subst hr
    have hbu : ∀ i, IsUnit (A i).2.1 := fun i => by
      by_contra hn
      exact hn (DVR.dvr_isUnit_of_not_dvd hπ (hb i))
    have h1 := wittIndex_eq_of_equivalent (equivalent_map_of_isGLEquiv v hE) (radical_eq_bot_map v _ hnd)
    have h3 := wittIndex_pairSum v h2 r A hbu
    rw [← h1] at h3
    omega

/-- **The local types of maximal lattices** (formerly a named input; Hanke thesis, §3, p. 8 and the proof of Theorem
5.1, pp. 17–18; [Shi, §3]; O'Meara §§92–93). Proved at every finite place, dyadic included. -/
@[kb "hanke2005crelle" "§3, p. 8; proof of Theorem 5.1, pp. 17–18 (local types; proved)"]
theorem shimuraMaximalTypes : ShimuraMaximalTypes F where
  selfDual := fun _ Q₀ hQ _ v h =>
    ⟨anisoDim_le_two_of_dualIndexAt_eq_one v Q₀ hQ h, fun he => not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ he h⟩
  even_two_iff := fun _ he Q₀ hQ v => anisoDim_eq_two_iff v Q₀ hQ he

/-! ### `SimilitudeOddMultiplier` -/

theorem wss_apply_two (a : Fin 2 → Fv) (y : Fin 2 → Fv) :
    weightedSumSquares Fv a y = a 0 * y 0 ^ 2 + a 1 * y 1 ^ 2 := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, _root_.sq]

theorem wss_apply_four (a : Fin 4 → Fv) (y : Fin 4 → Fv) :
    weightedSumSquares Fv a y = a 0 * y 0 ^ 2 + a 1 * y 1 ^ 2 + a 2 * y 2 ^ 2 + a 3 * y 3 ^ 2 := by
  simp [weightedSumSquares_apply, Fin.sum_univ_four, _root_.sq]

/-- Reindexing a diagonal form along `t = t'`. -/
theorem reindex_wss {K : Type*} [Field K] {t t' : ℕ} (h : t = t') (a : Fin t → K) :
    ∃ a' : Fin t' → K, (∏ i, a' i = ∏ i, a i) ∧
      ((∀ x : Fin t → K, ∑ i, a i * x i ^ 2 = 0 → x = 0) → ∀ x : Fin t' → K, ∑ i, a' i * x i ^ 2 = 0 → x = 0) ∧
      ∀ ξ : K, (∃ σ : (Fin t' → K) ≃ₗ[K] (Fin t' → K), ∀ x, weightedSumSquares K a' (σ x) = ξ * weightedSumSquares K a' x) →
        ∃ σ : (Fin t → K) ≃ₗ[K] (Fin t → K), ∀ x, weightedSumSquares K a (σ x) = ξ * weightedSumSquares K a x := by
  subst h
  exact ⟨a, rfl, id, fun _ h => h⟩

/-- **The binary case** ($t_\mathfrak p = 2$, $\mathfrak p$ ramified in $K$): $\langle a_0,a_1\rangle$ with
$x = -(a_1/a_0)s^2$ and $F_\mathfrak p(\sqrt x)$ ramified has a similitude of multiplier of valuation $1$. -/
theorem sim_two (a : Fin 2 → Fv) (ha0 : ∀ i, a i ≠ 0) {x : Fv} (hx : x ≠ 0) (hr : ¬ IsUnramSqrt v x) {s : Fv}
    (hs : s ≠ 0) (hxa : x = -(a 1 / a 0) * s ^ 2) :
    ∃ ξ : Fv, Valued.v ξ = WithZero.exp (-1 : ℤ) ∧
      ∃ σ : (Fin 2 → Fv) ≃ₗ[Fv] (Fin 2 → Fv), ∀ y, weightedSumSquares Fv a (σ y) = ξ * weightedSumSquares Fv a y := by
  obtain ⟨ξ, hξv, hξh⟩ := exists_val_one_hilbert_of_not_isUnramSqrt v hx hr
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hξv; exact WithZero.exp_ne_zero hξv.symm
  have hb : a 1 / a 0 ≠ 0 := div_ne_zero (ha0 1) (ha0 0)
  have hrep : ∃ X Y : Fv, 1 * X ^ 2 + (a 1 / a 0) * Y ^ 2 = ξ := by
    rw [LocalRankFive.represents_two_iff v one_ne_zero hb hξ0, LocalRankFive.hs_one_left, one_mul]
    rw [hxa, SqDual.hilbertSymbol_mul_sq_right _ _ _ _ hs] at hξh
    exact hξh
  obtain ⟨X, Y, hXY⟩ := hrep
  have hy : weightedSumSquares Fv a ![X, Y] = a 0 * ξ := by
    rw [wss_apply_two, ← hXY]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [ha0 0]
  obtain ⟨σ, hσ⟩ := wss_two_similitude a ha0 ![X, Y] (by rw [hy]; exact mul_ne_zero (ha0 0) hξ0)
  refine ⟨ξ, hξv, σ, fun y => ?_⟩
  rw [hσ, hy, mul_div_cancel_left₀ _ (ha0 0)]

/-- **The quaternary case** ($t_\mathfrak p = 4$): an anisotropic quaternary diagonal form over $F_\mathfrak p$ has a
similitude of multiplier $\pi$ (its determinant is a square, so it is a multiple of a quaternion norm form, and it is
universal by rank-$5$ isotropy). -/
theorem sim_four (a : Fin 4 → Fv) (ha : ∀ x : Fin 4 → Fv, ∑ i, a i * x i ^ 2 = 0 → x = 0) :
    ∃ σ : (Fin 4 → Fv) ≃ₗ[Fv] (Fin 4 → Fv),
      ∀ y, weightedSumSquares Fv a (σ y) = ((NF.π v : 𝔬) : Fv) * weightedSumSquares Fv a y := by
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  have hϖ0 : ϖ ≠ 0 := by
    have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := NF.valued_π v
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have ha0 : ∀ i, a i ≠ 0 := fun i hai => by
    have := ha (Pi.single i 1) (by simp [Pi.single_apply, hai])
    simpa using congrFun this i
  have hsq : IsSquare (a 0 * a 1 * a 2 * a 3) := by
    by_contra hns
    obtain ⟨x, hx, h0⟩ := quat_hyp v a ha0 hns
    exact hx (ha x h0)
  set b : Fin 5 → Fv := ![a 0, a 1, a 2, a 3, -(a 0 * ϖ)]
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    fin_cases i
    · exact ha0 0
    · exact ha0 1
    · exact ha0 2
    · exact ha0 3
    · exact neg_ne_zero.2 (mul_ne_zero (ha0 0) hϖ0)
  obtain ⟨x, hx, h0⟩ := LocalRankFive.isotropic_diag_five v b hb
  have h0' : a 0 * x 0 ^ 2 + a 1 * x 1 ^ 2 + a 2 * x 2 ^ 2 + a 3 * x 3 ^ 2 - a 0 * ϖ * x 4 ^ 2 = 0 := by
    rw [LocalRankFive.evalIn_diag_five] at h0
    simp [b] at h0
    linear_combination h0
  have hx4 : x 4 ≠ 0 := by
    intro h4
    rw [h4] at h0'
    have hz := ha ![x 0, x 1, x 2, x 3] (by
      simp [Fin.sum_univ_four]
      linear_combination h0')
    have hz' := congrFun hz
    apply hx
    funext i
    fin_cases i
    · simpa using hz' 0
    · simpa using hz' 1
    · simpa using hz' 2
    · simpa using hz' 3
    · simpa using h4
  set y : Fin 4 → Fv := ![x 0 / x 4, x 1 / x 4, x 2 / x 4, x 3 / x 4]
  have hy : weightedSumSquares Fv a y = a 0 * ϖ := by
    rw [wss_apply_four]
    simp [y]
    field_simp
    linear_combination h0'
  obtain ⟨σ, hσ⟩ := wss_four_similitude a ha0 hsq y (by rw [hy]; exact mul_ne_zero (ha0 0) hϖ0)
  refine ⟨σ, fun z => ?_⟩
  rw [hσ, hy, mul_div_cancel_left₀ _ (ha0 0)]

/-- **Similitudes of multiplier of valuation $1$** at places with $t_\mathfrak p = 0$, or $t_\mathfrak p = 2$ and $\mathfrak p$
ramified in $K$, or $t_\mathfrak p = 4$ ($n$ even; Hanke thesis, proof of Theorem 6.3, p. 21). -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (ord_p Ξ_p(θ_p) contains 1; proved)"]
theorem exists_mult_val_one (hn : 3 ≤ n) (he : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hcase : anisoDim v Q₀ = 0 ∨ (anisoDim v Q₀ = 2 ∧ IsRamifiedAt v Q₀) ∨ anisoDim v Q₀ = 4) :
    ∃ ξ ∈ multipliers (gramOf v (NF.Qp v Q₀)), Valued.v ξ = WithZero.exp (-1 : ℤ) := by
  have hQf := nondegenerate_Qf v Q₀ hQ
  have hw := two_mul_wittIndex_le v Q₀ hQ
  rw [QV_eq_Qf] at hw
  rw [gramOf_eq, ← hessian_Qf]
  rw [anisoDim_eq] at hcase
  obtain ⟨a, ha, ⟨c, hc0, hdet⟩, ⟨e⟩⟩ := exists_witt_diag (two_ne_zero : (2 : Fv) ≠ 0) (Qf v Q₀) hQf
  generalize hwdef : wittIndex (Qf v Q₀).toQuadraticForm = w at *
  -- a similitude of `wss a` with multiplier `ξ` of valuation 1 gives the result
  have key : ∀ ξ : Fv, Valued.v ξ = WithZero.exp (-1 : ℤ) →
      (∃ σ : (Fin (n - 2 * w) → Fv) ≃ₗ[Fv] (Fin (n - 2 * w) → Fv),
        ∀ x, weightedSumSquares Fv a (σ x) = ξ * weightedSumSquares Fv a x) →
      ∃ ξ ∈ multipliers ((1 / 2 : Fv) • (Qf v Q₀).hessian), Valued.v ξ = WithZero.exp (-1 : ℤ) := by
    intro ξ hξv ⟨σ, hσ⟩
    have hξ0 : ξ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hξv; exact WithZero.exp_ne_zero hξv.symm
    obtain ⟨τ, hτ⟩ := hyperbolicSpace_similitude (K := Fv) w hξ0
    obtain ⟨ρ, hρ⟩ := prod_similitude τ σ hτ hσ
    exact ⟨ξ, mem_multipliers_of_equivalent two_ne_zero (Qf v Q₀) ⟨e⟩ ρ hξ0 hρ, hξv⟩
  have hϖ : Valued.v ((NF.π v : 𝔬) : Fv) = WithZero.exp (-1 : ℤ) := NF.valued_π v
  rcases hcase with h0 | ⟨h2, hram⟩ | h4
  · -- t = 0
    refine key _ hϖ ⟨LinearEquiv.refl Fv _, fun x => ?_⟩
    have : ∀ y : Fin (n - 2 * w) → Fv, weightedSumSquares Fv a y = 0 := fun y => by
      rw [weightedSumSquares_apply]
      exact Finset.sum_eq_zero fun i _ => absurd i.2 (by omega)
    simp [this]
  · -- t = 2, ramified
    obtain ⟨a', hprod, hani, htr⟩ := reindex_wss h2 a
    have ha' := hani ha
    have ha'0 : ∀ i, a' i ≠ 0 := fun i hai => by
      have := ha' (Pi.single i 1) (by simp [Pi.single_apply, hai])
      simpa using congrFun this i
    have hn2 : n = 2 * w + 2 := by omega
    have hnh : n / 2 = w + 1 := by omega
    have hdet' : (Qf v Q₀).hessian.det = c ^ 2 * (-1) ^ w * 4 * (a' 0 * a' 1) := by
      rw [hdet, ← hprod, Fin.prod_univ_two, show (2 : Fv) ^ (n - 2 * w) = 4 by rw [h2]; norm_num]
    have hdet0 : (Qf v Q₀).hessian.det ≠ 0 := hQf
    have hx0 : algebraMap F Fv (discK Q₀) ≠ 0 := by
      rw [algebraMap_discK]
      exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdet0)
        (pow_ne_zero _ two_ne_zero)
    have h1 : ((-1 : Fv) ^ w) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    set s : Fv := 2 * c * a' 0 / 2 ^ (w + 1)
    have hs : s ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc0) (ha'0 0)) (pow_ne_zero _ two_ne_zero)
    have hxa : algebraMap F Fv (discK Q₀) = -(a' 1 / a' 0) * s ^ 2 := by
      rw [algebraMap_discK, hnh, hdet', hn2]
      simp only [s]
      have h1' : ((-1 : Fv) ^ w) * (-1) ^ w = 1 := by rw [← _root_.sq]; exact h1
      field_simp
      linear_combination (-(4 : Fv) * a' 0 * a' 1 * 2 ^ (2 * w + 2)) * h1'
    obtain ⟨ξ, hξv, σ, hσ⟩ := sim_two v a' ha'0 hx0 hram hs hxa
    exact key ξ hξv (htr ξ ⟨σ, hσ⟩)
  · -- t = 4
    obtain ⟨a', -, hani, htr⟩ := reindex_wss h4 a
    obtain ⟨σ, hσ⟩ := sim_four v a' (hani ha)
    exact key _ hϖ (htr _ ⟨σ, hσ⟩)

/-- **Similitudes of odd multiplier** (formerly a named input; Hanke thesis, proof of Theorem 6.3, p. 21, with
[Shi, §3.2]). Proved at every finite place, dyadic included. -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (similitudes of multiplier of valuation 1; proved)"]
theorem similitudeOddMultiplier : SimilitudeOddMultiplier F where
  exists_mult := fun hn he Q₀ hQ v hcase => exists_mult_val_one v hn he Q₀ hQ hcase

end QuadFormsKB.Hanke2005
