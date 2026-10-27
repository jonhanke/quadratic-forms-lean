import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.LFactorization

/-!
# Dirichlet's class number formula for quadratic fields

Combine $\zeta_K(s) = \zeta(s)L(s, \chi_D)$ (`LFactorization.lean`) with Mathlib's analytic class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: $(s-1)\zeta_K(s) \to \operatorname{res}_{s=1}\zeta_K =
2^{r_1}(2\pi)^{r_2}hR/(w\sqrt{|d_K|})$ as $s \to 1^+$) and $(s - 1)\zeta(s) \to 1$:

* `tendsto_LSeries_kronecker`: $L(s, \chi_D) \to \operatorname{res}_{s=1}\zeta_{K_D}$ as $s \to 1^+$;
* `kroneckerChar_ne_one`: $\chi_D$ is not the trivial character mod $|D|$ (else $L(s,\chi_D)$ would have a pole at $1$);
* `LFunction_kronecker_one`: $L(1, \chi_D) = \operatorname{res}_{s=1}\zeta_{K_D}$, with $L(1, \chi_D)$ the value at
  $s = 1$ of Mathlib's entire continuation `DirichletCharacter.LFunction` (equal to $\sum_n \chi_D(n)n^{-s}$ for
  $\operatorname{Re}s > 1$);
* **Dirichlet's class number formula**, with the constants of Mathlib's `dedekindZeta_residue`
  ($r_1, r_2$ from `nrRealPlaces_of_neg` etc., $|d_K| = |D|$ from `discr_eq`, $R = 1$ for $D < 0$, $w = 2$ for $D > 0$):
  $$L(1, \chi_D) = \frac{2\pi h(D)}{w(D)\sqrt{|D|}} \quad (D < 0), \qquad
    L(1, \chi_D) = \frac{2h(D)\,R(D)}{\sqrt{D}} = \frac{2h(D)\log\varepsilon_D}{\sqrt D} \quad (D > 0),$$
  where $h(D)$ = `classNumber (QField D)`, $w(D)$ = `torsionOrder (QField D)` (the number of roots of unity: $4, 6, 2$
  for $D = -4$, $D = -3$, $D < -4$), and $R(D)$ = `regulator (QField D)` $= \log\varepsilon_D$ for the fundamental unit
  $\varepsilon_D > 1$.

Sources: Davenport, *Multiplicative Number Theory*, Ch. 6, eqs. (15)–(17) (pp. 43–49 of the 3rd ed.) [locator
unverified]; Zagier, *Zetafunktionen und quadratische Körper*, §11; Marcus, *Number Fields*, Ch. 7; Cohen,
*A Course in Computational Algebraic Number Theory*, §5.3.
-/

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology QuadFormsKB.NFEuler
open scoped LSeries.notation Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

variable {D : ℤ} [IsQuadDisc D]

theorem tendsto_ofReal_nhdsGT_one :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast (ne_of_gt hs)

/-- **$L(s, \chi_D) \to \operatorname{res}_{s=1}\zeta_{K_D}$ as $s \to 1^+$** (real $s$):
$L(s,\chi_D) = (s-1)\zeta_K(s)\,/\,\big((s-1)\zeta(s)\big)$ for $s > 1$. -/
@[kb "davenport2000" "Ch. 6"]
theorem tendsto_LSeries_kronecker :
    Tendsto (fun s : ℝ => LSeries (fun n : ℕ => kroneckerChar D n) s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue (QField D) : ℂ)) := by
  have h1 := tendsto_sub_one_mul_dedekindZeta_nhdsGT (QField D)
  have h2 := riemannZeta_residue_one.comp (tendsto_ofReal_nhdsGT_one)
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hne : ((s : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hs))
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs'
  show ((s : ℂ) - 1) * dedekindZeta (QField D) s / (((s : ℂ) - 1) * riemannZeta s) = _
  rw [dedekindZeta_eq_mul hs']
  field_simp

instance : NeZero D.natAbs := ⟨by have := three_le_natAbs (D := D); omega⟩

/-- **$\chi_D$ is a nontrivial character mod $|D|$.** If $\chi_D = 1$, then $L(s, \chi_D) = L(s, 1_{|D|})$ has a pole
at $s = 1$ with residue $\prod_{p \mid D}(1 - p^{-1}) \neq 0$ (Mathlib's `LFunctionTrivChar_residue_one`), but
$L(s,\chi_D)$ has a finite limit as $s \to 1^+$ (`tendsto_LSeries_kronecker`). -/
theorem kroneckerChar_ne_one : kroneckerChar D ≠ 1 := by
  intro h
  have hres := DirichletCharacter.LFunctionTrivChar_residue_one (N := D.natAbs)
  have hres' := hres.comp tendsto_ofReal_nhdsGT_one
  -- (s - 1) L(s, χ_D) → 0 · res
  have hlim := (((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).sub_const (1 : ℂ)).mul
    (tendsto_LSeries_kronecker (D := D))
  simp only [Complex.ofReal_one, sub_self, zero_mul] at hlim
  have heq : ((fun s => (s - 1) * DirichletCharacter.LFunctionTrivChar D.natAbs s) ∘ fun s : ℝ => (s : ℂ))
      =ᶠ[𝓝[>] 1] fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n : ℕ => kroneckerChar D n) s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    simp only [Function.comp_apply, DirichletCharacter.LFunctionTrivChar]
    rw [← h, DirichletCharacter.LFunction_eq_LSeries _ hs']
  have := tendsto_nhds_unique (hres'.congr' heq) hlim
  rw [Finset.prod_eq_zero_iff] at this
  obtain ⟨p, hp, hp0⟩ := this
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have : (p : ℂ)⁻¹ = 1 := by rw [sub_eq_zero] at hp0; exact hp0.symm
  have h1 : ((p : ℝ)⁻¹ : ℂ) = 1 := by push_cast; exact this
  have h2 : (p : ℝ)⁻¹ = 1 := by exact_mod_cast h1
  have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- **$L(1, \chi_D) = \operatorname{res}_{s=1}\zeta_{K_D}$**, the value at $s = 1$ of the entire function
`DirichletCharacter.LFunction` ($\chi_D \ne 1$), which equals $\sum_n \chi_D(n)n^{-s}$ for $\operatorname{Re}s > 1$. -/
@[kb "davenport2000" "Ch. 6"]
theorem LFunction_kronecker_one :
    (kroneckerChar D).LFunction 1 = (dedekindZeta_residue (QField D) : ℂ) := by
  have hcont := (DirichletCharacter.differentiable_LFunction (kroneckerChar_ne_one (D := D))).continuous
  have h1 : Tendsto (fun s : ℝ => (kroneckerChar D).LFunction s) (𝓝[>] 1)
      (𝓝 ((kroneckerChar D).LFunction 1)) := by
    have := (hcont.tendsto 1).comp ((Complex.continuous_ofReal.tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ))))
    exact this
  refine tendsto_nhds_unique h1 (tendsto_LSeries_kronecker.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (DirichletCharacter.LFunction_eq_LSeries _ (by simpa using hs)).symm

/-- **Dirichlet's class number formula, imaginary quadratic fields ($D < 0$):**
$$L(1, \chi_D) = \frac{2\pi\,h(D)}{w(D)\sqrt{|D|}},$$
$h(D)$ = `classNumber (QField D)`, $w(D)$ = `torsionOrder (QField D)` the number of roots of unity in $K_D$.
(Mathlib's residue $2^{r_1}(2\pi)^{r_2}hR/(w\sqrt{|d_K|})$ with $r_1 = 0$, $r_2 = 1$, $R = 1$, $d_K = D$.) -/
@[kb "davenport2000" "Ch. 6, (15) [unverified locator]"]
theorem classNumberFormula_neg (hD : D < 0) :
    (kroneckerChar D).LFunction 1 =
      ((2 * π * classNumber (QField D) / (torsionOrder (QField D) * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ) := by
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, nrRealPlaces_of_neg hD, nrComplexPlaces_of_neg hD,
    regulator_of_neg hD, discr_eq]
  congr 1
  ring

/-- **Dirichlet's class number formula, real quadratic fields ($D > 0$):**
$$L(1, \chi_D) = \frac{2\,h(D)\,R(D)}{\sqrt D},$$
$h(D)$ = `classNumber (QField D)`, $R(D)$ = `regulator (QField D)` $= \log\varepsilon_D$ ($\varepsilon_D > 1$ the
fundamental unit). (Mathlib's residue with $r_1 = 2$, $r_2 = 0$, $w = 2$, $d_K = D$.) -/
@[kb "davenport2000" "Ch. 6, (17) [unverified locator]"]
theorem classNumberFormula_pos (hD : 0 < D) :
    (kroneckerChar D).LFunction 1 =
      ((2 * classNumber (QField D) * regulator (QField D) / Real.sqrt (D : ℝ) : ℝ) : ℂ) := by
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, nrRealPlaces_of_pos hD, nrComplexPlaces_of_pos hD,
    torsionOrder_of_pos hD, discr_eq, abs_of_pos (by exact_mod_cast hD : (0 : ℝ) < D)]
  congr 1
  push_cast; ring

/-- **Dirichlet's class number formula for $D > 0$ with the fundamental unit:**
$$L(1, \chi_D) = \frac{2\,h(D)\,\log\varepsilon_D}{\sqrt D}, \qquad \log\varepsilon_D = |\log w(\varepsilon)|,$$
for the fundamental unit $\varepsilon$ = `fundSystem (QField D) i` (unit rank $1$) and either real place $w$
(`regulator_of_pos`). -/
@[kb "davenport2000" "Ch. 6, (17) [unverified locator]"]
theorem classNumberFormula_pos_fundUnit (hD : 0 < D) (i : Fin (rank (QField D)))
    (w : InfinitePlace (QField D)) :
    (kroneckerChar D).LFunction 1 =
      ((2 * classNumber (QField D) * |Real.log (w (fundSystem (QField D) i : QField D))| /
        Real.sqrt (D : ℝ) : ℝ) : ℂ) := by
  rw [classNumberFormula_pos hD, regulator_of_pos hD i w]

end QuadFormsKB.Binary
