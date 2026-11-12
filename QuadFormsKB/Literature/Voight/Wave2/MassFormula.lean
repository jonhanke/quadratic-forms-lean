/-
# The Eichler mass formula from the discriminant of a maximal order (Voight, Ch. 15, 25, 26)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Theorem 15.5.5 (p. 249),
Lemma 15.4.7, Theorem 25.1.1 (p. 415), Main Theorem 26.1.5 (p. 432), Theorem 26.1.12 (p. 433) and
the proof in 26.5 (key `voight2021`).

**What is proved.** The repository proves Eichler's mass formula with an explicit lattice constant
(`QuatOrder.eichler_mass_formula'`, Voight Theorem 26.5.4 and (26.5.5)–(26.5.10)): for $F$ totally real with
$\mathbb Z_F$ a principal ideal domain, $B = (a,b)_F$ totally definite and a maximal order
$\mathcal O \supseteq \mathbb Z_F\langle i, j\rangle$ with $\mathbb Z_F$-basis $e$,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = 2\,|d_F|^{3/2}\pi^{-2n}
\Bigl(\prod_v \sqrt{\det \sigma_v(A_{\mathcal O})}\Bigr)\,\zeta_F(2)\prod_{\mathfrak p \mid \mathfrak D}(1 - N\mathfrak p^{-1}),$$
$A_{\mathcal O}$ the Gram matrix of $\operatorname{nrd}$ in $e$. Voight evaluates the product by the discriminant of a
maximal order (Theorem 15.5.5: $\operatorname{discrd}\mathcal O = \mathfrak D$, so
$\operatorname{disc}\mathcal O = \mathfrak D^2$ by Lemma 15.4.7). Here:
* `trdGramDet_eq`: $\det(\operatorname{trd}(e_pe_q)) = -16\det A_{\mathcal O}$ (algebra);
* `prod_sqrt_det_gramMat`: given $\operatorname{disc}\mathcal O = \mathfrak D^2$,
  $\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})} = N\mathfrak D/4^n$;
* `classMass_eq_of_maximalOrderDiscriminant`: **the Eichler mass formula of Theorem 26.1.12 (maximal orders)**,
  $$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F
  \prod_{\mathfrak p \mid \mathfrak D}(N\mathfrak p - 1),$$
  for maximal orders containing $\mathbb Z_F\langle i,j\rangle$, **conditional on the named input**
  `MaximalOrderDiscriminant F` (Voight Theorem 15.5.5, "only if" direction), and
  `classMass_eq_rat_of_maximalOrderDiscriminant`: over $\mathbb Q$, $\sum_{[J]} 1/w_J = \varphi(D)/12$
  (Theorem 25.1.1), under the same input.

**Inputs.** `MaximalOrderDiscriminant F` (Voight Theorem 15.5.5) is assumed, not proved: it rests on the local
structure of maximal orders (split places: $\mathcal O_{\mathfrak p} \cong \mathrm M_2(\mathbb Z_{F,\mathfrak p})$, Lemma 15.5.3;
ramified places: the valuation ring of the division algebra, $\operatorname{discrd} = \mathfrak p$, Theorem 13.3.11),
including the dyadic places. It is a statement about discriminants, not about masses.

**Restriction.** The hypothesis $\mathcal O \supseteq \mathbb Z_F\langle i,j\rangle$ (`stdOrder F a b ≤ O`) comes from
`QuatOrder.eichler_mass_formula'`; Voight's theorem holds for every maximal order.
-/
import QuadFormsKB.Literature.Voight.MassFormula
import QuadFormsKB.Literature.Hanke2011Enumerating.Bounds

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField Quaternion Matrix
open scoped Real

noncomputable section

namespace QuadFormsKB.Voight

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.NFEuler QuadFormsKB.HilbertModular

namespace MassWave2

variable {F : Type} [Field F] [NumberField F]

/-- **The discriminant of a family of four quaternions** (Voight Definition 15.2.2):
$d(f_0, \dots, f_3) = \det(\operatorname{trd}(f_pf_q))_{p,q}$. For an $\mathbb Z_F$-basis $f$ of an order $\mathcal O$, the
ideal it generates is $\operatorname{disc}(\mathcal O)$. -/
@[kb "voight2021" "Definition 15.2.2, p. 242"]
def trdGramDet {a b : 𝓞 F} (f : Fin 4 → QuatF F a b) : F :=
  (Matrix.of fun p q => QuatOrder.trd (f p * f q)).det

/-- The diagonal $(2, 2a, 2b, -2ab)$ of the trace form $(x, y) \mapsto \operatorname{trd}(xy)$. -/
def trdDiagF (a b : 𝓞 F) : Fin 4 → F :=
  ![2, 2 * algebraMap (𝓞 F) F a, 2 * algebraMap (𝓞 F) F b,
    -(2 * algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b)]

theorem trdGram_eq_coordMat {a b : 𝓞 F} (f : Fin 4 → QuatF F a b) :
    (Matrix.of fun p q => QuatOrder.trd (f p * f q)) =
      (QuatOrder.coordMat f)ᵀ * Matrix.diagonal (trdDiagF a b) * QuatOrder.coordMat f := by
  ext i j
  simp only [Matrix.of_apply, QuatOrder.trd, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, QuatOrder.coordMat, trdDiagF, Fin.sum_univ_four, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  ring

/-- **The trace discriminant is $-16$ times the norm Gram determinant**:
$\det(\operatorname{trd}(f_pf_q)) = -16\det A$, with $A$ = `gramMat f` the Gram matrix of $\operatorname{nrd}$. -/
theorem trdGramDet_eq {a b : 𝓞 F} (f : Fin 4 → QuatF F a b) :
    trdGramDet f = -16 * (gramMat f).det := by
  rw [trdGramDet, trdGram_eq_coordMat, gramMat_eq_coordMat, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_four,
    Fin.prod_univ_four]
  simp only [trdDiagF, nrdDiag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Theorem 15.5.5 (Voight 2021), "only if" direction, as a named input**: for every quaternion algebra
$B = (a, b)_F$ with $a, b \in \mathbb Z_F$ nonzero, every maximal $\mathbb Z_F$-order $\mathcal O \subset B$ and every
$\mathbb Z_F$-basis $e$ of $\mathcal O$, the discriminant $\det(\operatorname{trd}(e_pe_q))$ lies in $\mathbb Z_F$ and
generates $\mathfrak D^2$, where $\mathfrak D = \prod_{\mathfrak p \in \operatorname{Ram}_f B}\mathfrak p$ (`ramFin`):
$\operatorname{disc}(\mathcal O) = \operatorname{discrd}(\mathcal O)^2 = \mathfrak D^2$ (Lemma 15.4.7).
Assumed, not proved here. -/
@[kb "voight2021" "Theorem 15.5.5, p. 249; Lemma 15.4.7, p. 247"]
structure MaximalOrderDiscriminant (F : Type) [Field F] [NumberField F] : Prop where
  /-- $\operatorname{disc}(\mathcal O) = \mathfrak D^2$ for a maximal order with an $\mathbb Z_F$-basis $e$. -/
  disc_eq : ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) (O : Subalgebra (𝓞 F) (QuatF F a b)),
    IsMaximalOrder (𝓞 F) F O → ∀ e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O),
      ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = trdGramDet (fun i => (e i : QuatF F a b)) ∧
        Ideal.span {d} = (∏ v ∈ ramFin ha hb, v.asIdeal) ^ 2

section Totally

variable [IsTotallyReal F]

theorem card_infinitePlace_eq_finrank : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.nrComplexPlaces_eq_zero_iff.mpr inferInstance, add_zero, IsTotallyReal.finrank]

/-- **The archimedean product from the discriminant** (Voight Theorem 15.5.5 and (26.5.10)): if
$\operatorname{disc}\mathcal O = \mathfrak D^2$ then $\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})} = N\mathfrak D/4^n$,
$n = [F:\mathbb Q]$. -/
theorem prod_sqrt_det_gramMat [IsPrincipalIdealRing (𝓞 F)] (H : MaximalOrderDiscriminant F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdef : IsTotDefinite a b) {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    ∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (e i : QuatF F a b)).map (realEmb F v)).det =
      (∏ v ∈ ramFin ha hb, (normP v : ℝ)) / 4 ^ Module.finrank ℚ F := by
  obtain ⟨d, hd, hspan⟩ := H.disc_eq a b ha hb O hO e
  set A := gramMat fun i => (e i : QuatF F a b)
  have hli := linearIndependent_basis_order hO.1 e
  have hdetA : A.det = -(1 / 16) * algebraMap (𝓞 F) F d := by
    rw [hd, trdGramDet_eq]; ring
  have hpos : ∀ v : InfinitePlace F, 0 < realEmb F v A.det := fun v => by
    have := ((isTotPosGram_gramMat hdef hli) v).det_pos
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  have hv : ∀ v : InfinitePlace F, Real.sqrt (A.map (realEmb F v)).det = |realEmb F v A.det| ^ (1 / 2 : ℝ) :=
    fun v => by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, abs_of_pos (hpos v), Real.sqrt_eq_rpow]
  simp_rw [hv]
  rw [Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _), prod_abs_realEmb_eq, ← Real.sqrt_eq_rpow]
  set n := Module.finrank ℚ F
  have hnorm : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : ℝ) = (∏ v ∈ ramFin ha hb, (normP v : ℝ)) ^ 2 := by
    rw [hspan, map_pow, map_prod]; push_cast; rfl
  have hN : |((Algebra.norm ℚ A.det : ℚ) : ℝ)| =
      ((∏ v ∈ ramFin ha hb, (normP v : ℝ)) / 4 ^ n) ^ 2 := by
    rw [hdetA, map_mul, show (-(1 / 16) : F) = algebraMap ℚ F (-(1 / 16)) by simp,
      Algebra.norm_algebraMap, Rat.cast_mul, abs_mul, abs_norm_algebraMap,
      ← Ideal.absNorm_span_singleton, hnorm]
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    rw [div_pow, ← pow_mul, Rat.cast_pow, abs_pow]
    have : |((-(1 / 16) : ℚ) : ℝ)| = (4 ^ 2)⁻¹ := by norm_num
    rw [this]
    have h : ((4 : ℝ) ^ 2)⁻¹ ^ n * (4 : ℝ) ^ (n * 2) = 1 := by
      rw [mul_comm n 2, pow_mul, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
    rw [eq_div_iff (by positivity)]
    linear_combination (∏ v ∈ ramFin ha hb, (normP v : ℝ)) ^ 2 * h
  rw [hN, Real.sqrt_sq (by positivity)]

/-- **The Eichler mass formula for maximal orders** (Voight 2021, Theorem 26.1.12 with level $\mathfrak M = R$;
Main Theorem 26.1.5), conditional on the named input `MaximalOrderDiscriminant F` (Theorem 15.5.5): for a totally
real number field $F$ with $\mathbb Z_F$ a principal ideal domain, $B = (a,b)_F$ totally definite and a maximal order
$\mathcal O \supseteq \mathbb Z_F\langle i,j\rangle$,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F
\prod_{\mathfrak p \mid \mathfrak D}(N\mathfrak p - 1).$$
This is the identity of `EichlerMassFormulaMaximal F` for these orders. Conditional on `MaximalOrderDiscriminant F`. -/
@[kb "voight2021" "Main Theorem 26.1.5, p. 432; Theorem 26.1.12, p. 433; Theorem 15.5.5, p. 249"]
theorem classMass_eq_of_maximalOrderDiscriminant [IsPrincipalIdealRing (𝓞 F)]
    (H : MaximalOrderDiscriminant F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) :
    classMass O = 2 * dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
        |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) *
        ∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1) := by
  obtain ⟨e⟩ := exists_basis_order (a := a) (b := b) hO.1
  have hcl : NumberField.classNumber F = 1 := NumberField.classNumber_eq_one_iff.2 inferInstance
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  rw [classMass, eichler_mass_formula' ha hb hdef hO hstd e, prod_sqrt_det_gramMat H ha hb hdef hO e,
    card_infinitePlace_eq_finrank, hcl, abs_of_pos hd]
  set n := Module.finrank ℚ F
  have hprod : (∏ v ∈ ramFin ha hb, (normP v : ℝ)) * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) =
      ∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have h2 : (0 : ℝ) < normP v := by have := two_le_normP v; positivity
    rw [Real.rpow_neg_one, mul_sub, mul_one, mul_inv_cancel₀ h2.ne']
  rw [← hprod]
  have hπ : (2 * Real.pi) ^ (2 * n) = 4 ^ n * Real.pi ^ (2 * n) := by
    rw [mul_pow, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [hπ]
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hp : (0 : ℝ) < Real.pi ^ (2 * n) := by positivity
  field_simp
  ring

end Totally

/-- **The Eichler mass formula over $\mathbb Q$** (Voight 2021, Theorem 25.1.1 = Theorem 25.3.15), conditional on
`MaximalOrderDiscriminant ℚ` (Theorem 15.5.5 over $\mathbb Z$): for a definite quaternion algebra $B = (a,b)_{\mathbb Q}$
of discriminant $D$ and a maximal order $\mathcal O \supseteq \mathbb Z\langle i, j\rangle$,
$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \varphi(D)/12 = \prod_{p \mid D}(p - 1)/12$. This is the
identity of `EichlerMassFormulaRat` for these orders. -/
@[kb "voight2021" "Theorem 25.1.1, p. 415; Theorem 25.3.15, p. 422; Theorem 15.5.5, p. 249"]
theorem classMass_eq_rat_of_maximalOrderDiscriminant (H : MaximalOrderDiscriminant ℚ) {a b : 𝓞 ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) {O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b)}
    (hO : IsMaximalOrder (𝓞 ℚ) ℚ O) (hstd : stdOrder ℚ a b ≤ O) :
    classMass O = (∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  rw [classMass_eq_of_maximalOrderDiscriminant H ha hb hdef hO hstd,
    Hanke2011Enumerating.dedekindZetaR_rat (by norm_num), zetaR_two, Module.finrank_self,
    NumberField.discr_rat, NumberField.classNumber_eq_one_iff.2 inferInstance]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

end MassWave2

end QuadFormsKB.Voight
