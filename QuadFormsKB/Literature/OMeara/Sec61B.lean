/-
# O'Meara §61A–§61B: quaternion algebras over complete archimedean fields, and the complex case

**Setting.** As in `Sec61.lean`, O'Meara's real (complex) complete field is replaced by `ℝ` (`ℂ`), to which it is
topologically isomorphic (§12). Quadratic spaces are Mathlib `QuadraticForm F V` with `V` finite dimensional;
*regular* means `Q.radical = ⊥`. O'Meara's quaternion algebra $\left(\frac{\alpha,\beta}{F}\right)$ (§57, p. 143:
generators $i, j$ with $i^2 = \alpha$, $j^2 = \beta$, $ij = -ji$) is Mathlib's `ℍ[F,α,β]`
(`QuaternionAlgebra F α 0 β`), defined for $\alpha, \beta \in \dot F$.

**Proves**
* over any field of characteristic $\ne 2$: if $\beta = x^2 - \alpha y^2$ then
  $\left(\frac{\alpha,\beta}{F}\right) \cong \left(\frac{1,-1}{F}\right)$ (`quatEquivOneNegOne`), and the scaling
  isomorphism $\left(\frac{\alpha,\beta}{F}\right) \cong \left(\frac{\alpha s^2,\beta t^2}{F}\right)$
  (`quatScaleEquiv`); these are the isomorphisms behind O'Meara 57:9 used in 61:2, 61.r10 and 62:3;
* Remark 61:2 (p. 156): $\langle -1\rangle \perp \langle -1\rangle$ does not represent $1$
  (`not_neg_sq_add_neg_sq_eq_one`), $\left(\frac{-1,-1}{\mathbb R}\right)$ is a division algebra
  (`quat_neg_one_neg_one_division`), every real quaternion algebra is isomorphic to $\left(\frac{1,-1}{\mathbb R}\right)$
  or $\left(\frac{-1,-1}{\mathbb R}\right)$ (`quat_real_equiv`), and these two are not isomorphic
  (`not_nonempty_quat_one_neg_one_equiv`);
* §61B (p. 156), the complex case: every regular space is $\langle 1\rangle \perp \cdots \perp \langle 1\rangle$
  (`equivalent_sum_squares_complex`), it is isotropic when $n \ge 2$ (`not_anisotropic_complex`),
  $U \to V$ if and only if $\dim U \le \dim V$ (`isRepresentedBy_iff_finrank_le_complex`), $U \cong V$ if and only if
  $\dim U = \dim V$ (`equivalent_iff_finrank_eq_complex`), and there is one quaternion algebra,
  $\left(\frac{1,-1}{\mathbb C}\right)$ (`quat_complex_equiv`).
-/
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Tamagawa.Measure.Weil.QuatSplitIso
import QuadFormsKB.Tamagawa.Quaternion

open QuadraticMap QuadraticForm Module
open scoped Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### Isomorphisms of quaternion algebras over a field -/

section Quat

variable {F : Type*} [Field F]

/-- Auxiliary: the quaternion basis of `ℍ[F,a',b']` for parameters `(a,b)` given by scaling the generators. -/
def quatScaleBasis (a b a' b' s t : F) (ha : s ^ 2 * a' = a) (hb : t ^ 2 * b' = b) :
    QuaternionAlgebra.Basis ℍ[F,a',b'] a 0 b where
  i := (s • (⟨0, 1, 0, 0⟩ : ℍ[F,a',b']))
  j := (t • (⟨0, 0, 1, 0⟩ : ℍ[F,a',b']))
  k := ((s * t) • (⟨0, 0, 0, 1⟩ : ℍ[F,a',b']))
  i_mul_i := by subst ha; ext <;> simp; ring
  j_mul_j := by subst hb; ext <;> simp; ring
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp; ring

theorem quatScaleHom_apply (a b a' b' s t : F) (ha : s ^ 2 * a' = a) (hb : t ^ 2 * b' = b)
    (q : ℍ[F,a,b]) :
    (quatScaleBasis a b a' b' s t ha hb).liftHom q = ⟨q.re, s * q.imI, t * q.imJ, s * t * q.imK⟩ := by
  rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
  ext <;> simp [quatScaleBasis, Algebra.algebraMap_eq_smul_one] <;> ring

/-- Auxiliary: equal parameters give isomorphic quaternion algebras. -/
def quatCongr {a a' b b' : F} (ha : a = a') (hb : b = b') : ℍ[F,a,b] ≃ₐ[F] ℍ[F,a',b'] := by
  subst ha hb; exact AlgEquiv.refl

/-- **A quaternion algebra with $\beta = x^2 - \alpha y^2$ is $\left(\frac{1,-1}{F}\right)$**: for $\alpha, \beta \ne 0$ in a
field of characteristic $\ne 2$ with $\beta = x^2 - \alpha y^2$ (i.e. $\langle \alpha \rangle \perp \langle \beta\rangle$
represents $1$, after O'Meara 57:9), $\left(\frac{\alpha,\beta}{F}\right) \cong M_2(F) \cong
\left(\frac{1,-1}{F}\right)$ (`Tamagawa.Measure.Weil.quatMatEquiv` twice). -/
def quatEquivOneNegOne (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {x y : F}
    (h : x ^ 2 - a * y ^ 2 = b) : ℍ[F,a,b] ≃ₐ[F] ℍ[F,1,-1] :=
  haveI : Invertible (2 : F) := invertibleOfNonzero h2
  haveI : Invertible a := invertibleOfNonzero ha
  haveI : Invertible b := invertibleOfNonzero hb
  haveI : Invertible (1 : F) := invertibleOfNonzero one_ne_zero
  haveI : Invertible (-1 : F) := invertibleOfNonzero (by simp)
  (Tamagawa.Measure.Weil.quatMatEquiv a b x y h).trans
    (Tamagawa.Measure.Weil.quatMatEquiv (1 : F) (-1) 0 1 (by ring)).symm

/-- **Scaling the generators**: $\left(\frac{\alpha,\beta}{F}\right) \cong \left(\frac{\alpha s^2,\beta t^2}{F}\right)$ for
$s, t \ne 0$ (send $i \mapsto s^{-1} i$, $j \mapsto t^{-1} j$). -/
def quatScaleEquiv (a b : F) {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ℍ[F,a,b] ≃ₐ[F] ℍ[F,a * s ^ 2,b * t ^ 2] :=
  AlgEquiv.ofAlgHom
    (quatScaleBasis a b (a * s ^ 2) (b * t ^ 2) s⁻¹ t⁻¹ (by field_simp) (by field_simp)).liftHom
    (quatScaleBasis (a * s ^ 2) (b * t ^ 2) a b s t (by ring) (by ring)).liftHom
    (by
      apply AlgHom.ext; intro q
      rw [AlgHom.comp_apply, quatScaleHom_apply, quatScaleHom_apply]
      ext <;> simp <;> field_simp)
    (by
      apply AlgHom.ext; intro q
      rw [AlgHom.comp_apply, quatScaleHom_apply, quatScaleHom_apply]
      ext <;> simp <;> field_simp)

end Quat

/-! ### Remark 61:2: the real quaternion algebras -/

/-- **$\langle -1\rangle \perp \langle -1\rangle$ does not represent $1$** (O'Meara 1963, Remark 61:2, p. 156):
$-x^2 - y^2 \ne 1$ for all real $x, y$. -/
@[kb "omeara1963" "§61A, 61:2, p. 156 (⟨−1⟩ ⊥ ⟨−1⟩ does not represent 1)"]
theorem not_neg_sq_add_neg_sq_eq_one (x y : ℝ) : -1 * x ^ 2 + -1 * y ^ 2 ≠ 1 := by
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- **$\left(\frac{-1,-1}{\mathbb R}\right)$ is a division algebra** (O'Meara 1963, Remark 61:2, p. 156, by
Proposition 57:9): every nonzero element of $\mathbb H[\mathbb R,-1,-1]$ is invertible. -/
@[kb "omeara1963" "§61A, 61:2, p. 156 ((−1,−1) is a division algebra)"]
theorem quat_neg_one_neg_one_division : ∀ q : ℍ[ℝ,-1,-1], q ≠ 0 → IsUnit q := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := Tamagawa.Measure.Weil.exists_norm_eq_of_not_division (-1 : ℝ) (-1)
    two_ne_zero (by norm_num) (by norm_num) h
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- **There are two real quaternion algebras** (O'Meara 1963, Remark 61:2, p. 156): for $\alpha, \beta \ne 0$ in
$\mathbb R$, $\left(\frac{\alpha,\beta}{\mathbb R}\right)$ is isomorphic to $\left(\frac{1,-1}{\mathbb R}\right)$ or to
$\left(\frac{-1,-1}{\mathbb R}\right)$. -/
@[kb "omeara1963" "§61A, 61:2, p. 156 (every real quaternion algebra is (1,−1) or (−1,−1))"]
theorem quat_real_equiv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[ℝ,a,b] ≃ₐ[ℝ] ℍ[ℝ,1,-1]) ∨ Nonempty (ℍ[ℝ,a,b] ≃ₐ[ℝ] ℍ[ℝ,-1,-1]) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rcases lt_or_gt_of_ne hb with hb' | hb'
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · right
      have hs : (0 : ℝ) < -a := by linarith
      have ht : (0 : ℝ) < -b := by linarith
      have e := quatScaleEquiv a b (s := 1 / Real.sqrt (-a)) (t := 1 / Real.sqrt (-b))
        (by positivity) (by positivity)
      have e1 : a * (1 / Real.sqrt (-a)) ^ 2 = -1 := by
        rw [div_pow, Real.sq_sqrt hs.le]; field_simp
      have e2 : b * (1 / Real.sqrt (-b)) ^ 2 = -1 := by
        rw [div_pow, Real.sq_sqrt ht.le]; field_simp
      exact ⟨e.trans (quatCongr e1 e2)⟩
    · left
      have ht : (0 : ℝ) < -b / a := div_pos (by linarith) ha'
      refine ⟨quatEquivOneNegOne h2 ha hb (x := 0) (y := Real.sqrt (-b / a)) ?_⟩
      rw [Real.sq_sqrt ht.le]; field_simp; ring
  · left
    refine ⟨quatEquivOneNegOne h2 ha hb (x := Real.sqrt b) (y := 0) ?_⟩
    rw [Real.sq_sqrt hb'.le]; ring

/-- **The two real quaternion algebras are distinct** (O'Meara 1963, Remark 61:2, p. 156, "essentially two distinct
quaternion algebras"): $\left(\frac{1,-1}{\mathbb R}\right) \not\cong \left(\frac{-1,-1}{\mathbb R}\right)$. -/
@[kb "omeara1963" "§61A, 61:2, p. 156 ((1,−1) and (−1,−1) are not isomorphic)"]
theorem not_nonempty_quat_one_neg_one_equiv : ¬ Nonempty (ℍ[ℝ,1,-1] ≃ₐ[ℝ] ℍ[ℝ,-1,-1]) := by
  rintro ⟨e⟩
  let q : ℍ[ℝ,1,-1] := ⟨1, 1, 0, 0⟩
  let q' : ℍ[ℝ,1,-1] := ⟨1, -1, 0, 0⟩
  have hq' : q' ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.re h; simp [q'] at this
  have hqq : q * q' = 0 := by ext <;> simp [q, q']
  have hq : e q ≠ 0 := by
    intro h
    have : q = 0 := e.injective (by rw [h, map_zero])
    have := congrArg QuaternionAlgebra.re this; simp [q] at this
  obtain ⟨u, hu⟩ := quat_neg_one_neg_one_division (e q) hq
  have h0 : e q * e q' = 0 := by rw [← map_mul, hqq, map_zero]
  have : e q' = 0 := by
    rw [← hu] at h0
    exact (u.mul_right_eq_zero).1 h0
  exact hq' (e.injective (by rw [this, map_zero]))

/-! ### §61B: the complex case -/

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

private theorem sepLeft_of_radical {W : Type*} [AddCommGroup W] [Module ℂ W] (Q : QuadraticForm ℂ W)
    (hQ : Q.radical = ⊥) : (associated (R := ℂ) Q).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, ← QuadraticMap.radical_eq_ker_associated]
  exact hQ

private theorem equivalent_wss_one_of_eq {m n : ℕ} (h : m = n) :
    (weightedSumSquares ℂ (1 : Fin m → ℂ)).Equivalent (weightedSumSquares ℂ (1 : Fin n → ℂ)) := by
  subst h; exact QuadraticMap.Equivalent.refl _

/-- Extension by zero `ℂ^m → ℂ^n` for `m ≤ n`. -/
private def extendZero {m n : ℕ} (_h : m ≤ n) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v j := if hj : j.val < m then v ⟨j.val, hj⟩ else 0
  map_add' v w := by ext j; by_cases hj : j.val < m <;> simp [hj]
  map_smul' c v := by ext j; by_cases hj : j.val < m <;> simp [hj]

private theorem isRepresentedBy_wss_one {m n : ℕ} (h : m ≤ n) :
    IsRepresentedBy (weightedSumSquares ℂ (1 : Fin m → ℂ)) (weightedSumSquares ℂ (1 : Fin n → ℂ)) := by
  refine ⟨⟨extendZero h, ?_⟩, ?_⟩
  · intro v
    simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro j hj
      have : ¬ j.val < m := fun hjm => hj ⟨⟨j.val, hjm⟩, by ext; simp⟩
      simp [extendZero, this]
    · intro i; simp [extendZero]
  · intro v w hvw
    ext i
    have hvw' : extendZero h v = extendZero h w := hvw
    have := congrFun hvw' (Fin.castLE h i)
    simpa [extendZero] using this

/-- **Every regular complex space is $\langle 1\rangle \perp \cdots \perp \langle 1\rangle$** (O'Meara 1963, §61B,
p. 156): $V \cong \langle 1\rangle^{n}$, $n = \dim V$. -/
@[kb "omeara1963" "§61B, p. 156 (V ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨1⟩ over ℂ)"]
theorem equivalent_sum_squares_complex (Q : QuadraticForm ℂ V) (hQ : Q.radical = ⊥) :
    Q.Equivalent (weightedSumSquares ℂ (1 : Fin (finrank ℂ V) → ℂ)) :=
  Q.equivalent_weightedSumSquares_of_isAlgClosed (sepLeft_of_radical Q hQ)

/-- **A complex space of dimension $n \ge 2$ is isotropic** (O'Meara 1963, §61B, p. 156). O'Meara states it for
regular spaces; it holds for all. -/
@[kb "omeara1963" "§61B, p. 156 (V is isotropic when n ≥ 2)"]
theorem not_anisotropic_complex (Q : QuadraticForm ℂ V) (hn : 2 ≤ finrank ℂ V) : ¬ Q.Anisotropic := by
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  let i0 : Fin (finrank ℂ V) := ⟨0, by omega⟩
  let i1 : Fin (finrank ℂ V) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  -- a nonzero vector `x` of the diagonal model with `∑ w i • (x i * x i) = 0`
  have key : ∃ x : Fin (finrank ℂ V) → ℂ, x ≠ 0 ∧ weightedSumSquares ℂ w x = 0 := by
    by_cases h0 : w i0 = 0
    · refine ⟨Pi.single i0 1, ?_, ?_⟩
      · intro h; have := congrFun h i0; simp at this
      · rw [weightedSumSquares_apply, Finset.sum_eq_single i0]
        · simp [h0]
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-(w i1) / w i0) (n := 2) (by norm_num)
      refine ⟨Pi.single i0 c + Pi.single i1 1, ?_, ?_⟩
      · intro h; have := congrFun h i1; simp [Pi.single_eq_of_ne hne.symm] at this
      · rw [weightedSumSquares_apply, Finset.sum_eq_add i0 i1 hne]
        · simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
          field_simp at hc
          linear_combination hc
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj.1, Pi.single_eq_of_ne hj.2]
        · simp
        · simp
  obtain ⟨x, hx0, hx⟩ := key
  intro hQ
  have h1 : Q (e.symm x) = 0 := by
    have := e.map_app (e.symm x)
    simp only [QuadraticMap.IsometryEquiv.apply_symm_apply] at this
    rw [← this]; exact hx
  have := hQ _ h1
  exact hx0 (by simpa using congrArg e this)

/-- **$U \to V$ if and only if $\dim U \le \dim V$** for regular complex spaces (O'Meara 1963, §61B, p. 156). -/
@[kb "omeara1963" "§61B, p. 156 (U is represented by V iff dim U ≤ dim V)"]
theorem isRepresentedBy_iff_finrank_le_complex (QU : QuadraticForm ℂ U) (Q : QuadraticForm ℂ V)
    (hU : QU.radical = ⊥) (hV : Q.radical = ⊥) : IsRepresentedBy QU Q ↔ finrank ℂ U ≤ finrank ℂ V := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact LinearMap.finrank_le_finrank_of_injective (f := σ.toLinearMap) hσ
  · intro h
    have eU := equivalent_sum_squares_complex QU hU
    have eV := equivalent_sum_squares_complex Q hV
    exact (IsRepresentedBy.of_equivalent eU).trans
      ((isRepresentedBy_wss_one h).trans (IsRepresentedBy.of_equivalent eV.symm))

/-- **$U \cong V$ if and only if $\dim U = \dim V$** for regular complex spaces (O'Meara 1963, §61B, p. 156). -/
@[kb "omeara1963" "§61B, p. 156 (U ≅ V iff dim U = dim V)"]
theorem equivalent_iff_finrank_eq_complex (QU : QuadraticForm ℂ U) (Q : QuadraticForm ℂ V)
    (hU : QU.radical = ⊥) (hV : Q.radical = ⊥) : QU.Equivalent Q ↔ finrank ℂ U = finrank ℂ V := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · intro h
    have eU := equivalent_sum_squares_complex QU hU
    have eV := equivalent_sum_squares_complex Q hV
    exact (eU.trans (equivalent_wss_one_of_eq h)).trans eV.symm

end Complex

/-- **There is one complex quaternion algebra** (O'Meara 1963, §61B, p. 156): for $\alpha, \beta \ne 0$ in
$\mathbb C$, $\left(\frac{\alpha,\beta}{\mathbb C}\right) \cong \left(\frac{1,-1}{\mathbb C}\right)$. -/
@[kb "omeara1963" "§61B, p. 156 (the one complex quaternion algebra (1,−1))"]
theorem quat_complex_equiv {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) : Nonempty (ℍ[ℂ,a,b] ≃ₐ[ℂ] ℍ[ℂ,1,-1]) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq b (n := 2) (by norm_num)
  exact ⟨quatEquivOneNegOne two_ne_zero ha hb (x := x) (y := 0) (by rw [hx]; ring)⟩

end QuadFormsKB.OMeara
