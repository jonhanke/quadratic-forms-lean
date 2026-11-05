/-
# O'Meara §13D: the Reducibility Criterion (13:9)

**Setting.** $K$ is a field with a complete non-archimedean valuation: a Mathlib `NormedField K` with
`CompleteSpace K` whose norm satisfies the strong triangle law (`IsNonarchimedean (norm : K → ℝ)`). For a polynomial
$f = a_0x^n + a_1x^{n-1} + \dots + a_n$ O'Meara writes $|f| = \max_i |a_i|$ (the Gauss norm of §13C).

**Index convention.** O'Meara's $a_i$ is the coefficient of $x^{n-i}$, i.e. Mathlib's `f.coeff (n - i)`; his
leading coefficient $a_0$ is `f.leadingCoeff`. His condition "$|a_i| = |f|$ for some $i < n$" (with $i > 0$ forced by
$|a_0| < |f|$) becomes "$\lVert$`f.coeff j`$\rVert = |f|$ for some $0 < j < n$" with $j = n - i$.

**Proves** `not_irreducible_of_norm_coeff_lt` (**13:9**). O'Meara deduces it from Hensel's lemma (13:8); the proof
here uses Mathlib's spectral norm instead: for a monic irreducible $g$ of degree $n$ every coefficient satisfies
$\lVert g_j\rVert^{1/(n-j)} \le \lVert g_0\rVert^{1/n}$ (`spectralNorm_eq_norm_coeff_zero_rpow`), which contradicts
the hypothesis after dividing $f$ by its leading coefficient. For the trivial valuation the hypothesis is never
satisfied.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.AdjoinRoot

open Polynomial

namespace QuadFormsKB.OMeara


open Polynomial in
private lemma coeff_zero_gt_of_monic_irreducible {K : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [IsUltrametricDist K] {g : K[X]} (hm : g.Monic) (hi : Irreducible g)
    {j : ℕ} (hj0 : 0 < j) (hjn : j < g.natDegree) (h1 : 1 < ‖g.coeff j‖) : ‖g.coeff j‖ < ‖g.coeff 0‖ := by
  have : Fact (Irreducible g) := ⟨hi⟩
  have : FiniteDimensional K (AdjoinRoot g) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  set x : AdjoinRoot g := AdjoinRoot.root g
  have hmin : minpoly K x = g := by
    have := AdjoinRoot.minpoly_root hi.ne_zero
    rwa [hm.leadingCoeff, inv_one, C_1, mul_one] at this
  have hsn := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K (AdjoinRoot g) x
  rw [hmin] at hsn
  have hsv : spectralNorm K (AdjoinRoot g) x = spectralValue g := by
    unfold spectralNorm; rw [hmin]
  have hle : spectralValueTerms g j ≤ spectralNorm K (AdjoinRoot g) x := by
    rw [hsv]; exact le_ciSup (spectralValueTerms_bddAbove g) j
  rw [spectralValueTerms_of_lt_natDegree g hjn, hsn] at hle
  set n := g.natDegree
  set a := ‖g.coeff j‖
  set b := ‖g.coeff 0‖
  have hn : 0 < n := by omega
  have h2 := pow_le_pow_left₀ (by positivity) hle n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)] at h2
  have e2 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp
  rw [e2, Real.rpow_one] at h2
  have hnj : (0 : ℝ) < (n - j : ℝ) := by
    have : (j : ℝ) < n := by exact_mod_cast hjn
    linarith
  have : (1 : ℝ) < 1 / (n - j : ℝ) * (n : ℝ) := by
    rw [one_div, inv_mul_eq_div, lt_div_iff₀ hnj]
    have : (0 : ℝ) < j := by exact_mod_cast hj0
    linarith
  calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
    _ < a ^ (1 / (n - j : ℝ) * (n : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt h1 this
    _ ≤ b := h2

/-- **13:9 (Reducibility Criterion).** Let $K$ be complete under a non-archimedean valuation and
$f = a_0x^n + \dots + a_n \in K[x]$ of degree $n$. If $|a_0| < |f| = |a_i|$ for some $i < n$, then $f$ is reducible.
Here: if some coefficient $f_j$ with $0 < j < n$ has the largest norm among all coefficients and
$\lVert$`f.leadingCoeff`$\rVert < \lVert f_j\rVert$, then $f$ is not irreducible. -/
@[kb "omeara1963" "§13D, 13:9, p. 28 (Reducibility Criterion)"]
theorem not_irreducible_of_norm_coeff_lt {K : Type*} [NormedField K] [CompleteSpace K]
    (hna : IsNonarchimedean (norm : K → ℝ)) {f : K[X]} {j : ℕ} (hj0 : 0 < j) (hjn : j < f.natDegree)
    (hmax : ∀ k, ‖f.coeff k‖ ≤ ‖f.coeff j‖) (hlt : ‖f.leadingCoeff‖ < ‖f.coeff j‖) :
    ¬ Irreducible f := by
  intro hirr
  have hc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hcpos : 0 < ‖f.leadingCoeff‖ := norm_pos_iff.mpr hc0
  have hex : ∃ x : K, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
    by_cases h : ‖f.leadingCoeff‖ = 1
    · refine ⟨f.coeff j, ?_, by linarith⟩
      intro h0; rw [h0, norm_zero] at hlt; linarith
    · exact ⟨f.leadingCoeff, hc0, h⟩
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne hex
  haveI : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hna
  set c := f.leadingCoeff
  set g : K[X] := C c⁻¹ * f with hg
  have hgm : g.Monic := by
    rw [hg]; exact monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc0)
  have hu : IsUltrametricDist K := inferInstance
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hgi : Irreducible g := by
    have : Associated g f := (associated_isUnit_mul_left_iff (isUnit_C.mpr hcinv.isUnit)).mpr
      (Associated.refl f)
    exact this.irreducible_iff.mpr hirr
  have hcoeff : ∀ k, g.coeff k = c⁻¹ * f.coeff k := fun k => by rw [hg, coeff_C_mul]
  have hdeg : g.natDegree = f.natDegree := by rw [hg, natDegree_C_mul hcinv]
  have hnorm : ∀ k, ‖g.coeff k‖ = ‖f.coeff k‖ / ‖c‖ := fun k => by
    rw [hcoeff, norm_mul, norm_inv]; field_simp
  have h1 : 1 < ‖g.coeff j‖ := by
    rw [hnorm, lt_div_iff₀ hcpos]; linarith
  have := coeff_zero_gt_of_monic_irreducible hgm hgi hj0 (hdeg ▸ hjn) h1
  rw [hnorm, hnorm] at this
  have := (div_lt_div_iff_of_pos_right hcpos).mp this
  linarith [hmax 0]

end QuadFormsKB.OMeara
