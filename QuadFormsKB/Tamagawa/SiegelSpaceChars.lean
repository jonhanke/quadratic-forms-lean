/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelClassical

/-!
# Basis-free Siegel characters $\chi_q$, $\chi_m$ of a quadratic space

**Layer:** $F$ a number field; $(V, q)$ a quadratic space over $F$ (headlines: $F$ totally real, $q$ totally positive
definite, $\dim V = 3$ or $2$).

The rank-3 and rank-2 headlines of gd regularize with Siegel's characters `spaceChar3 Q m`, `spaceChar2 Q`, built from the
coordinate symbol `sqChar v d` ($d = -2m\det H_Q$, resp. $-\det H_Q$). Under a change of coordinates $Q \mapsto Q\circ g$,
$\det H_{Q\circ g} = (\det g)^2\det H_Q$, so `sqChar` is unchanged at every $\mathfrak p$ with $\mathrm{ord}_\mathfrak p\det g = 0$
(`eventually_spaceChar2_compMat`, `eventually_spaceChar3_compMat`) — but **not** exactly: `sqChar` is $0$ where $d$ is not
a $\mathfrak p$-unit, and $(\det g)^2d$ can be a non-unit where $d$ is a unit (e.g. $d = 1$, $\det g = \varpi$).

**The square-class symbol.** `sqClassChar v d` is $0$ at $\mathfrak p \mid 2$ and where $\mathrm{ord}_\mathfrak p d$ is odd (or $d = 0$),
and otherwise $\pm1$ according as $d$ is a square in $F_\mathfrak p$; "even order" is phrased as $\exists u,\ \mathrm{ord}_\mathfrak p(u^2d) = 0$.
It depends **only on the square class** $dF^{\times2}$ (`sqClassChar_mul_sq`, no condition on $u$), agrees with `sqChar` where $d$
is a $\mathfrak p$-unit (`sqChar_eq_sqClassChar`), hence off a finite set (`eventually_sqChar_eq_sqClassChar`). At the primes
$\mathfrak p \nmid 2$ with $d \in \mathfrak o_\mathfrak p^\times\cdot F_\mathfrak p^{\times2}$ it is the Frobenius sign of $F(\sqrt d)/F$
(Neukirch 1999, Ch. I §8 [unverified]).

**Intrinsic characters.** With the discriminant $\mathrm{disc}(q) = \det H_{q_e} \in F/F^{\times2}$ (any basis $e$; `hessDetV`
uses `Module.finBasis`): `spaceChar2V q v = sqClassChar v (-disc q)`, `spaceChar3V q m v = sqClassChar v (-2m disc q)`, equal
to the coordinate square-class symbol in every basis (`spaceChar2V_eq_basis`, `spaceChar3V_eq_basis`, exactly) and to the
coordinate characters `spaceChar2 (coordForm q e)`, `spaceChar3 (coordForm q e) m` off a finite set. The regularized products do
not see the difference (`regProd_congr_eventually`, from `regProd_congr_finite`), nor does the natural-order input
(`naturalOrderEulerOne_congr_eventually`).

**Headlines** (new names; gd's signatures unchanged): `siegelFormula3_quadraticSpace_classical'`,
`siegelFormula2_quadraticSpace_classical'`, and natural order `siegelFormula3_quadraticSpace_natural_classical'`,
`siegelFormula2_quadraticSpace_natural_classical'` with the input `NaturalOrderEulerOne` stated for the intrinsic character.

Sources: Siegel 1935, Hauptsatz [unverified]; Hanke 2004, p. 357 ($\chi(-2\det H\cdot m)$); O'Meara 1963, §63 (discriminant
$dV \in F^\times/F^{\times2}$) [unverified]; Neukirch 1999, Ch. I §8 [unverified].
-/

open NumberField IsDedekindDomain Module Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd QuadFormsKB.Tamagawa.SiegelLat LatChange

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/-! ### The square-class symbol -/

section SqClass

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **The square-class quadratic symbol of $d \in F$ at $\mathfrak p$**: $0$ at $\mathfrak p \mid 2$ and where $d \notin
\mathfrak o_\mathfrak p^\times F^{\times2}$ (odd order, or $d = 0$); otherwise $1$ if $d$ is a square in $F_\mathfrak p$ and $-1$ if not. A
function of the square class of $d$ (`sqClassChar_mul_sq`); equal to `sqChar` at $\mathfrak p$-units (Neukirch 1999, Ch. I §8
[unverified]). -/
@[kb "neukirch1999" "Ch. I §8 (decomposition of primes in F(√d), square-class form) [unverified]"]
def sqClassChar (d : F) : ℝ :=
  open Classical in
  if (2 : 𝓞 F) ∈ v.asIdeal ∨ ¬ ∃ u : F, v.valuation F (u ^ 2 * d) = 1 then 0
  else if IsSquare (algebraMap F Fv d) then 1 else -1

theorem abs_sqClassChar_le (d : F) : |sqClassChar v d| ≤ 1 := by
  unfold sqClassChar; split_ifs <;> simp

/-- **`sqClassChar` depends only on the square class**, exactly: $\chi(w^2d) = \chi(d)$ for every $w \ne 0$. -/
theorem sqClassChar_mul_sq {w : F} (hw : w ≠ 0) (d : F) : sqClassChar v (w ^ 2 * d) = sqClassChar v d := by
  classical
  unfold sqClassChar
  have hex : (∃ u : F, v.valuation F (u ^ 2 * (w ^ 2 * d)) = 1) ↔ ∃ u : F, v.valuation F (u ^ 2 * d) = 1 := by
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u * w, by rw [show (u * w) ^ 2 * d = u ^ 2 * (w ^ 2 * d) by ring]; exact hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u / w, by rw [show (u / w) ^ 2 * (w ^ 2 * d) = u ^ 2 * d by field_simp]; exact hu⟩
  have hsq : IsSquare (algebraMap F Fv (w ^ 2 * d)) ↔ IsSquare (algebraMap F Fv d) := by
    have hw' : algebraMap F Fv w ≠ 0 := (map_ne_zero _).mpr hw
    rw [map_mul, map_pow]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r / algebraMap F Fv w, ?_⟩
      field_simp
      linear_combination hr
    · rintro ⟨r, hr⟩
      exact ⟨algebraMap F Fv w * r, by rw [hr]; ring⟩
  simp only [hex, hsq]

/-- At a $\mathfrak p$-unit $d$, the square-class symbol is `sqChar`. -/
theorem sqChar_eq_sqClassChar {d : F} (h : v.valuation F d = 1) : sqChar v d = sqClassChar v d := by
  classical
  have hex : ∃ u : F, v.valuation F (u ^ 2 * d) = 1 := ⟨1, by rw [one_pow, one_mul, h]⟩
  unfold sqChar sqClassChar
  simp only [h, ne_eq, not_true_eq_false, or_false, hex, not_true_eq_false]

theorem sqChar_zero : sqChar v (0 : F) = 0 := by
  simp [sqChar]

theorem sqClassChar_zero : sqClassChar v (0 : F) = 0 := by
  simp [sqClassChar]

end SqClass

/-- **`sqChar` and `sqClassChar` agree off a finite set** (the primes where $d \ne 0$ is not a unit). -/
theorem eventually_sqChar_eq_sqClassChar (d : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, sqChar v d = sqClassChar v d := by
  by_cases hd : d = 0
  · subst hd; exact Eventually.of_forall fun v => by rw [sqChar_zero, sqClassChar_zero]
  · filter_upwards [(finite_valuation_ne_one hd).eventually_cofinite_notMem] with v hv
    simp only [not_not] at hv
    exact sqChar_eq_sqClassChar v hv

/-! ### Coordinate characters under a change of coordinates -/

section Coord

/-- **$\chi_Q$ is unchanged by a change of coordinates off a finite set**: `spaceChar2 (Q ∘ g) = spaceChar2 Q` at every
$\mathfrak p$ with $\mathrm{ord}_\mathfrak p\det g = 0$. (Not exactly: see the module docstring.) -/
theorem eventually_spaceChar2_compMat (Q : QuadForm F 2) (g : GL (Fin 2) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, spaceChar2 (Q.compMat g.val) v = spaceChar2 Q v := by
  have hdet : g.val.det ≠ 0 := (g.isUnit.map Matrix.detMonoidHom).ne_zero
  filter_upwards [(finite_valuation_ne_one hdet).eventually_cofinite_notMem] with v hv
  simp only [not_not] at hv
  rw [spaceChar2, spaceChar2, hessian_det_compMat', show -(g.val.det ^ 2 * Q.hessian.det) =
    g.val.det ^ 2 * -Q.hessian.det by ring, sqChar_mul_sq v hdet hv]

/-- **$\chi_m$ is unchanged by a change of coordinates off a finite set.** -/
theorem eventually_spaceChar3_compMat (Q : QuadForm F 3) (g : GL (Fin 3) F) (m : 𝓞 F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, spaceChar3 (Q.compMat g.val) m v = spaceChar3 Q m v := by
  have hdet : g.val.det ≠ 0 := (g.isUnit.map Matrix.detMonoidHom).ne_zero
  filter_upwards [(finite_valuation_ne_one hdet).eventually_cofinite_notMem] with v hv
  simp only [not_not] at hv
  rw [spaceChar3, spaceChar3, hessian_det_compMat', show -(2 * (g.val.det ^ 2 * Q.hessian.det) * algebraMap (𝓞 F) F m) =
    g.val.det ^ 2 * -(2 * Q.hessian.det * algebraMap (𝓞 F) F m) by ring, sqChar_mul_sq v hdet hv]

/-- **The square-class symbol of $c\det H_Q$ is exactly invariant** under $Q \mapsto Q\circ g$. -/
theorem sqClassChar_compMat (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N) (g : GL (Fin N) F) (c : F) :
    sqClassChar v (c * (Q.compMat g.val).hessian.det) = sqClassChar v (c * Q.hessian.det) := by
  have hdet : g.val.det ≠ 0 := (g.isUnit.map Matrix.detMonoidHom).ne_zero
  rw [hessian_det_compMat', show c * (g.val.det ^ 2 * Q.hessian.det) = g.val.det ^ 2 * (c * Q.hessian.det) by ring,
    sqClassChar_mul_sq v hdet]

end Coord

/-! ### The intrinsic characters of $(V, q)$ -/

section Intrinsic

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **The discriminant of $(V, q)$** as an element of $F$: $\det H_{q_e}$ in the basis $e$ = `Module.finBasis F V`. Its square
class $\mathrm{disc}(q)F^{\times2}$ does not depend on the basis (`hessDetV_eq_basis`; O'Meara 1963, §41B, p. 87, the discriminant $dV$; the Hessian determinant is $2^n dV$). -/
@[kb "omeara1963" "§41B, p. 87 (discriminant dV of a quadratic space)"]
def hessDetV (q : QuadraticForm F V) : F := (coordForm q (finBasis F V)).hessian.det

/-- In any basis $e$, $\det H_{q_e} = g^2\,\mathrm{disc}(q)$ with $g = \det$ of the change of basis, $g \ne 0$. -/
theorem hessDetV_eq_basis (q : QuadraticForm F V) {n : ℕ} (e : Basis (Fin n) F V) :
    ∃ g : F, g ≠ 0 ∧ (coordForm q e).hessian.det = g ^ 2 * hessDetV q := by
  obtain rfl : n = finrank F V := by rw [finrank_eq_card_basis e, Fintype.card_fin]
  let _ : Module (𝓞 F) V := Module.compHom V (algebraMap (𝓞 F) F)
  have _ : IsScalarTower (𝓞 F) F V := ⟨fun a b x => by
    show (a • b) • x = (algebraMap (𝓞 F) F a) • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  refine ⟨(basisChange (finBasis F V) e).val.det, ((basisChange (finBasis F V) e).isUnit.map
    Matrix.detMonoidHom).ne_zero, ?_⟩
  have hc : coordForm q e = (coordForm q (finBasis F V)).compMat (basisChange (finBasis F V) e).val := by
    refine QuadForm.ext_eval fun y => ?_
    obtain ⟨x, rfl⟩ := e.equivFun.surjective y
    rw [eval_compMat, basisChange_mulVec, eval_coordForm, eval_coordForm]
    simp only [LinearEquiv.symm_apply_apply]
  rw [hc, hessian_det_compMat']
  rfl

theorem sqClassChar_coordForm (v : HeightOneSpectrum (𝓞 F)) (q : QuadraticForm F V) {n : ℕ} (e : Basis (Fin n) F V)
    (c : F) : sqClassChar v (c * (coordForm q e).hessian.det) = sqClassChar v (c * hessDetV q) := by
  obtain ⟨g, hg, h⟩ := hessDetV_eq_basis q e
  rw [h, show c * (g ^ 2 * hessDetV q) = g ^ 2 * (c * hessDetV q) by ring, sqClassChar_mul_sq v hg]

/-- **Siegel's character $\chi_q$ of a binary quadratic space** (basis-free): the square-class symbol of $-\mathrm{disc}(q)$,
i.e. the character of $F(\sqrt{-\mathrm{disc}\,q})/F$ at the unramified odd primes (Siegel 1935 [unverified]). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (the character χ of F(√-d)), basis-free [unverified]"]
def spaceChar2V (q : QuadraticForm F V) (v : HeightOneSpectrum (𝓞 F)) : ℝ := sqClassChar v (-hessDetV q)

/-- **Siegel's character $\chi_m$ of a ternary quadratic space** (basis-free): the square-class symbol of
$-2m\,\mathrm{disc}(q)$ (Hanke 2004, p. 357). -/
@[kb "hanke2004" "Φ₃(𝔭) = χ(-2 det H · m), p. 357 (basis-free)"]
def spaceChar3V (q : QuadraticForm F V) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  sqClassChar v (-(2 * hessDetV q * algebraMap (𝓞 F) F m))

theorem abs_spaceChar2V_le (q : QuadraticForm F V) (v : HeightOneSpectrum (𝓞 F)) : |spaceChar2V q v| ≤ 1 :=
  abs_sqClassChar_le v _

theorem abs_spaceChar3V_le (q : QuadraticForm F V) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    |spaceChar3V q m v| ≤ 1 :=
  abs_sqClassChar_le v _

/-- **$\chi_q$ in any basis** (exact): the square-class symbol of $-\det H_{q_e}$. -/
theorem spaceChar2V_eq_basis (q : QuadraticForm F V) {n : ℕ} (e : Basis (Fin n) F V) (v : HeightOneSpectrum (𝓞 F)) :
    spaceChar2V q v = sqClassChar v (-(coordForm q e).hessian.det) := by
  rw [spaceChar2V, neg_eq_neg_one_mul, neg_eq_neg_one_mul (coordForm q e).hessian.det, sqClassChar_coordForm]

/-- **$\chi_m$ in any basis** (exact). -/
theorem spaceChar3V_eq_basis (q : QuadraticForm F V) {n : ℕ} (e : Basis (Fin n) F V) (m : 𝓞 F)
    (v : HeightOneSpectrum (𝓞 F)) :
    spaceChar3V q m v = sqClassChar v (-(2 * (coordForm q e).hessian.det * algebraMap (𝓞 F) F m)) := by
  rw [spaceChar3V, show -(2 * hessDetV q * algebraMap (𝓞 F) F m) = -(2 * algebraMap (𝓞 F) F m) * hessDetV q by ring,
    show -(2 * (coordForm q e).hessian.det * algebraMap (𝓞 F) F m) =
      -(2 * algebraMap (𝓞 F) F m) * (coordForm q e).hessian.det by ring, sqClassChar_coordForm]

/-- **The coordinate character $\chi_{q_e}$ is the intrinsic one off a finite set**, for every basis $e$. -/
theorem eventually_spaceChar2_eq_V (q : QuadraticForm F V) (e : Basis (Fin 2) F V) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, spaceChar2 (coordForm q e) v = spaceChar2V q v := by
  filter_upwards [eventually_sqChar_eq_sqClassChar (-(coordForm q e).hessian.det)] with v hv
  rw [spaceChar2, hv, spaceChar2V_eq_basis q e]

/-- **The coordinate character $\chi_{m, q_e}$ is the intrinsic one off a finite set.** -/
theorem eventually_spaceChar3_eq_V (q : QuadraticForm F V) (e : Basis (Fin 3) F V) (m : 𝓞 F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, spaceChar3 (coordForm q e) m v = spaceChar3V q m v := by
  filter_upwards [eventually_sqChar_eq_sqClassChar (-(2 * (coordForm q e).hessian.det * algebraMap (𝓞 F) F m))]
    with v hv
  rw [spaceChar3, hv, spaceChar3V_eq_basis q e]

end Intrinsic

/-! ### Regularized products and the natural-order input see characters only up to finite sets -/

section Congr

/-- **`regProd` is unchanged by a change of $\chi$ off a finite set** (`regProd_congr_finite`, cofinite form). -/
theorem regProd_congr_eventually {χ χ' : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) (hχ' : ∀ v, |χ' v| ≤ 1)
    (h : ∀ᶠ v in cofinite, χ v = χ' v) {c : ℝ} (hL : HasLOne χ' c) (e : ℤ) (f : HeightOneSpectrum (𝓞 F) → ℝ)
    (hf : Multipliable fun v => f v * (1 - χ' v / (normP v : ℝ)) ^ e) :
    regProd χ e f = regProd χ' e f := by
  have hfin := eventually_cofinite.mp h
  refine regProd_congr_finite hχ hχ' hfin.toFinset (fun v hv => ?_) ?_ e f hf
  · by_contra hc; exact hv (hfin.mem_toFinset.mpr hc)
  · rw [hL.lOne_eq]; exact hL

theorem lFactor_one_eq (χ : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    lFactor χ 1 v = (1 - χ v / (normP v : ℝ))⁻¹ := by
  simp only [lFactor, Real.rpow_neg_one, div_eq_mul_inv]

/-- **The natural-order input passes along a change of $\chi$ off a finite set** (given $L_F(1, \chi')$): the two Euler
products differ by finitely many factors, as do the two values $L_F(1,\cdot)$ (`HasLOne.congr_finite`). -/
theorem naturalOrderEulerOne_congr_eventually {χ χ' : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (hχ' : ∀ v, |χ' v| ≤ 1) (h : ∀ᶠ v in cofinite, χ v = χ' v) {c : ℝ} (hL : HasLOne χ' c)
    (hN : NaturalOrderEulerOne χ) : NaturalOrderEulerOne χ' := by
  have hfin := eventually_cofinite.mp h
  set S := hfin.toFinset
  have hS : ∀ v ∉ S, χ v = χ' v := fun v hv => by by_contra hc; exact hv (hfin.mem_toFinset.mpr hc)
  have e1 := (hL.congr_finite hχ hχ' S hS).lOne_eq
  have e2 := hL.lOne_eq
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (1 - χ v / (normP v : ℝ))⁻¹
  set b : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (1 - χ' v / (normP v : ℝ))⁻¹
  have ha : ∀ v, a v ≠ 0 := fun v => inv_ne_zero (one_sub_div_pos (hχ v) v).ne'
  have hb : ∀ v, b v ≠ 0 := fun v => inv_ne_zero (one_sub_div_pos (hχ' v) v).ne'
  have hr : HasProd (fun v => b v / a v) (∏ v ∈ S, b v / a v) (normOrder F) :=
    hasProd_prod_of_ne_finset_one fun v hv => by simp only [a, b, hS v hv]; exact div_self (hb v)
  have hprod := hN.hasProd.mul hr
  refine ⟨?_⟩
  convert hprod using 1
  · funext v; exact (mul_div_cancel₀ (b v) (ha v)).symm
  · rw [e2, e1]
    simp only [lFactor_one_eq]
    rw [mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun v _ => ?_, mul_one]
    show a v / b v * (b v / a v) = 1
    field_simp [ha v, hb v]

end Congr

/-! ### $L_F(1, \cdot)$ for the coordinate characters, and convergence of the classical corrected products -/

section Coords

variable [IsTotallyReal F]

/-- $L_F(1, \chi_m)$ exists for the coordinate ternary character of a totally positive definite form over $F$. -/
theorem hasLOne_spaceChar3 (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3) (hLi : Lattices.IsIntegral Q L.1)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    HasLOne (spaceChar3 Q m) (LOne (spaceChar3 Q m)) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 2) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hfin := eventually_cofinite.mp (eventually_chiTern_eq Q γ Q₀ hγ hQ₀ (ne_zero_of_totallyPos hm))
  have h' := (lOne_chiTern_pos hpd₀ hm).2.congr_finite (χ := spaceChar3 Q m) (fun v => abs_sqChar_le v _)
    (fun v => abs_chiTern_le v Q₀ m) hfin.toFinset
    (fun v hv => by by_contra hc; exact hv (hfin.mem_toFinset.mpr fun h => hc h.symm))
  rw [h'.lOne_eq]; exact h'

/-- $L_F(1, \chi_Q)$ exists for the coordinate binary character of a totally positive definite form over $F$. -/
theorem hasLOne_spaceChar2 (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2) (hLi : Lattices.IsIntegral Q L.1) :
    HasLOne (spaceChar2 Q) (LOne (spaceChar2 Q)) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 1) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hfin := eventually_cofinite.mp (eventually_chiP_eq Q γ Q₀ hγ hQ₀)
  have h' := (lOne_chiP_binary hpd₀).2.congr_finite (χ := spaceChar2 Q) (fun v => abs_sqChar_le v _)
    (fun v => abs_chiP_le Q₀ v) hfin.toFinset
    (fun v hv => by by_contra hc; exact hv (hfin.mem_toFinset.mpr fun h => hc h.symm))
  rw [h'.lOne_eq]; exact h'

/-- The corrected classical densities converge whenever the corrected coordinate densities do. -/
theorem multipliable_intrinsicBeta_of_spaceBeta (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F)
    (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ)
    (hmul : Multipliable fun v => spaceBeta v Q L m * (1 - χ v / (normP v : ℝ)) ^ e) :
    Multipliable fun v => intrinsicBeta v Q L m * (1 - χ v / (normP v : ℝ)) ^ e := by
  have hg : Multipliable fun v => (locIndex v L)⁻¹ :=
    multipliable_of_ne_finset_one fun v hv => by rw [locIndex_eq_one_of_notMem L hv, inv_one]
  refine (hmul.mul hg).congr fun v => ?_
  rw [spaceBeta_eq_locIndex_mul]
  field_simp [(locIndex_pos v L).ne']

end Coords

/-! ### The headlines with the intrinsic characters -/

section Headlines

variable [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
  [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **The ternary regularized product does not depend on the choice of character**: intrinsic $\chi_m$ vs. the
coordinate character in any basis $e$. -/
theorem regProd_spaceChar3V_eq (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) (e : Basis (Fin 3) F V) :
    regProd (spaceChar3V q m) 1 (fun v => intrinsicBetaV v q L m) =
      regProd (spaceChar3 (coordForm q e) m) 1 (fun v => intrinsicBetaV v q L m) := by
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  refine regProd_congr_eventually (abs_spaceChar3V_le q m) (fun v => abs_sqChar_le v _) ?_
    (hasLOne_spaceChar3 _ hpd _ hLi' hm) 1 _ ?_
  · filter_upwards [eventually_spaceChar3_eq_V q e m] with v hv; exact hv.symm
  · simp only [intrinsicBetaV_eq_basis _ q L e]
    exact multipliable_intrinsicBeta_of_spaceBeta _ _ _ _ _ (multipliable_spaceBeta_chiTern _ hpd _ hLi' hm)

/-- **The binary regularized product does not depend on the choice of character.** -/
theorem regProd_spaceChar2V_eq (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) (e : Basis (Fin 2) F V) :
    regProd (spaceChar2V q) (-1) (fun v => intrinsicBetaV v q L m) =
      regProd (spaceChar2 (coordForm q e)) (-1) (fun v => intrinsicBetaV v q L m) := by
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  refine regProd_congr_eventually (abs_spaceChar2V_le q) (fun v => abs_sqChar_le v _) ?_
    (hasLOne_spaceChar2 _ hpd _ hLi') (-1) _ ?_
  · filter_upwards [eventually_spaceChar2_eq_V q e] with v hv; exact hv.symm
  · simp only [intrinsicBetaV_eq_basis _ q L e]
    exact multipliable_intrinsicBeta_of_spaceBeta _ _ _ _ _ (multipliable_spaceBeta_chiP _ hpd _ hLi' hm)

/-- **Ternary Siegel formula, classical normalization, basis-free character** (unconditional): every term is attached to
$(V, q, L, m)$ without coordinates — the intrinsic genus, $N\mathfrak d(L)$, the classical densities $\beta_\mathfrak p(L_\mathfrak p, m)$
and Siegel's character $\chi_m$ = `spaceChar3V q m` of $F(\sqrt{-2m\,\mathrm{disc}\,q})/F$:
$\mathrm{repMass} = \mathrm{Mass}\cdot|d_F|^{-1}N\mathfrak d(L)^{-1/2}\prod_\sigma\beta_\sigma(1; \sigma m)\cdot\mathrm{regProd}_{\chi_m}(1, \beta_\mathfrak p(L_\mathfrak p, m))$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, classical normalization, basis-free character [unverified for F]"]
theorem siegelFormula3_quadraticSpace_classical' (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3V q m) 1 fun v => intrinsicBetaV v q L m) := by
  rw [siegelFormula3_quadraticSpace_classical h hq hLi hm, regProd_spaceChar3V_eq hq hLi hm]

/-- **Binary Siegel formula, classical normalization, basis-free character** (unconditional; $\varepsilon = \tfrac12$,
$\chi_q$ = `spaceChar2V q` of $F(\sqrt{-\mathrm{disc}\,q})/F$). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), classical normalization, basis-free character [unverified for F]"]
theorem siegelFormula2_quadraticSpace_classical' (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2V q) (-1) fun v => intrinsicBetaV v q L m) := by
  rw [siegelFormula2_quadraticSpace_classical h hq hLi hm, regProd_spaceChar2V_eq hq hLi hm]

/-- **Ternary, natural order, basis-free**: given `NaturalOrderEulerOne` of the intrinsic $\chi_m$ (convention input), the
natural-order Euler product of the classical densities converges to the regularized value, and Siegel's formula holds with
every term basis-free. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), classical normalization, basis-free character"]
theorem siegelFormula3_quadraticSpace_natural_classical' (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (spaceChar3V q m)) :
    HasProd (fun v => intrinsicBetaV v q L m)
        (regProd (spaceChar3V q m) 1 fun v => intrinsicBetaV v q L m) (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
        (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
          regProd (spaceChar3V q m) 1 fun v => intrinsicBetaV v q L m) := by
  set e := finBasisOfFinrankEq F V h
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  have hN' : NaturalOrderEulerOne (spaceChar3 (coordForm q e) m) :=
    naturalOrderEulerOne_congr_eventually (abs_spaceChar3V_le q m) (fun v => abs_sqChar_le v _)
      (by filter_upwards [eventually_spaceChar3_eq_V q e m] with v hv; exact hv.symm)
      (hasLOne_spaceChar3 _ hpd _ hLi' hm) hN
  refine ⟨?_, siegelFormula3_quadraticSpace_classical' h hq hLi hm⟩
  rw [regProd_spaceChar3V_eq hq hLi hm e]
  exact (siegelFormula3_quadraticSpace_natural_classical h hq hLi hm e hN').1

/-- **Binary, natural order, basis-free**: given `NaturalOrderEulerOne` of the intrinsic $\chi_q$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), classical normalization, basis-free character [unverified]"]
theorem siegelFormula2_quadraticSpace_natural_classical' (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (spaceChar2V q)) :
    HasProd (fun v => intrinsicBetaV v q L m)
        (regProd (spaceChar2V q) (-1) fun v => intrinsicBetaV v q L m) (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L *
        (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
          regProd (spaceChar2V q) (-1) fun v => intrinsicBetaV v q L m) := by
  set e := finBasisOfFinrankEq F V h
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  have hN' : NaturalOrderEulerOne (spaceChar2 (coordForm q e)) :=
    naturalOrderEulerOne_congr_eventually (abs_spaceChar2V_le q) (fun v => abs_sqChar_le v _)
      (by filter_upwards [eventually_spaceChar2_eq_V q e] with v hv; exact hv.symm)
      (hasLOne_spaceChar2 _ hpd _ hLi') hN
  refine ⟨?_, siegelFormula2_quadraticSpace_classical' h hq hLi hm⟩
  rw [regProd_spaceChar2V_eq hq hLi hm e]
  exact (siegelFormula2_quadraticSpace_natural_classical h hq hLi hm e hN').1

end Headlines

end QuadFormsKB.Tamagawa.SiegelSpace
