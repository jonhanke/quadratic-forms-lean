/-
# Hanke 2011, Corollary 6.4, coefficientwise, totally real $F$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, Corollary 6.4, p. 27.

For a distinguished family $\lambda$ (`DistinguishedFamily`, Def. 4.9: $I(\lambda(\mathfrak a)) = \mathfrak a$) with each
$\lambda(\mathfrak a)$ globally rational with an $\alpha$ of totally positive sign, the coefficient at $\mathfrak a$ of the
left Dirichlet series (the class sum $\sum_{L \in \mathrm{Cls}^*(\lambda(\mathfrak a),\vec\sigma_\infty,\vec c_{\mathbb S};n)}
1/|\mathrm{Aut}(L)|$, here `∑ᶠ t ∈ GenStar …, massOfTuple t`) equals
$$\frac{|\Delta_F|^{n(n-1)/4}}{\bigl(2^{n(n+1)/2}V(n)\bigr)^{[F:\mathbb Q]}}\cdot N(\mathfrak a)^{(n+1)/2}\cdot M^*(\lambda(\mathfrak a)),$$
the factor $N(\mathfrak a)^{(n+1)/2}$ being the shift $s \mapsto s - \tfrac{n+1}2$ of the Dirichlet series $D_{M^*}$.
The key lemma is `normAssoc_toHom`: $N_{F/\mathbb Q}(I(\lambda(\mathfrak a))) = N(\mathfrak a)$.

*Check of the constant.* The paper's constant $|\Delta_F|^{n(n-1)/4}\big/\bigl(2^{n(n+1)/2}V(n)\bigr)^{[F:\mathbb Q]}$ agrees
with the one obtained from `sum_massOfTuple_eq_totalMassM` ($N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$): no discrepancy.
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummed
import QuadFormsKB.Literature.Hanke2011Structure.SquareclassSeries

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem idealOrd_eq_count (v : HeightOneSpectrum (𝓞 F)) (a : Ideal (𝓞 F)) :
    idealOrd v a = ((UniqueFactorizationMonoid.normalizedFactors a).count v.asIdeal : ℤ) := rfl

/-- **$N_{F/\mathbb Q}(I(\lambda(\mathfrak a))) = N(\mathfrak a)$** for a distinguished family
($I(\lambda(\mathfrak a)) = \mathfrak a$, so $\prod_\mathfrak p N(\mathfrak p)^{\operatorname{ord}_\mathfrak p\mathfrak a} = N(\mathfrak a)$). -/
@[kb "hanke2011structure" "Def. 4.9, p. 18; Cor. 6.4, p. 27 (N(I(λ(a))) = N(a))"]
theorem normAssoc_toHom (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) :
    normAssoc (lam.toHom a) = (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) := by
  have ha : (a : Ideal (𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  have hfin := Ideal.hasFiniteMulSupport (R := 𝓞 F) ha
  have h1 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.maxPowDividing (a : Ideal (𝓞 F)) = a :=
    Ideal.finprod_heightOneSpectrum_factorization ha
  have hN : Ideal.absNorm (a : Ideal (𝓞 F)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm (v.maxPowDividing (a : Ideal (𝓞 F))) := by
    conv_lhs => rw [← h1]
    exact map_finprod (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ) hfin
  have hfin2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Ideal.absNorm (v.maxPowDividing (a : Ideal (𝓞 F))) :=
    Set.Finite.subset hfin fun v hv => by
      rw [Function.mem_mulSupport] at hv ⊢
      intro h
      exact hv (by simp [h])
  have e : ∀ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v (lam.toHom a) =
      ((Ideal.absNorm (v.maxPowDividing (a : Ideal (𝓞 F))) : ℕ) : ℝ) := by
    intro v
    rw [lam.ord_eq a v, idealOrd_eq_count, zpow_natCast,
      IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v ha, map_pow, Nat.cast_pow]
  unfold normAssoc
  rw [finprod_congr e, hN]
  exact (map_finprod (Nat.castRingHom ℝ) hfin2).symm

/-- **Corollary 6.4, coefficientwise** (totally real $F$, $n \ge 3$, totally positive definite signature
$\vec\sigma_\infty = ((n,0))_v$): for a distinguished family $\lambda$ and a nonzero ideal $\mathfrak a$ with $\lambda(\mathfrak a)$
globally rational ($\rho_\mathfrak p(\lambda(\mathfrak a)_\mathfrak p) = \alpha$, $\alpha$ a square at every real place),
$$\sum_{t \in \mathrm{Gen}^*(\lambda(\mathfrak a),\vec\sigma_\infty,\vec c_{\mathbb S};n)}\mathrm{Mass}(t) =
\frac{|\Delta_F|^{n(n-1)/4}}{\bigl(2^{n(n+1)/2}V(n)\bigr)^{[F:\mathbb Q]}}\cdot N(\mathfrak a)^{(n+1)/2}\cdot
M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(\lambda(\mathfrak a)).$$
(The coefficient at $\mathfrak a$ of the left series equals that of $\frac{|\Delta_F|^{n(n-1)/4}}{(2^{n(n+1)/2}V(n))^{[F:\mathbb Q]}}
D_{M^*}(s - \frac{n+1}2)$.) -/
@[kb "hanke2011structure" "Cor. 6.4, p. 27 (coefficientwise, totally real F)"]
theorem cor_6_4_coeff [IsTotallyReal F] (hn : 3 ≤ n) (lam : DistinguishedFamily F)
    (𝕊 : Set (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℤ) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenStar (lam.toHom a) (totPosSig F n) 𝕊 c, massOfTuple (lam.toHom a) (totPosSig F n) 𝕊 c t =
      |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) /
          (((2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2)) * volV n) ^ Module.finrank ℚ F *
        (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ (((n : ℝ) + 1) / 2) *
          totalMassM n (lam.toHom a) (epsInf (totPosSig F n)) 𝕊 c := by
  rw [sum_massOfTuple_eq_totalMassM (lam.toHom a) 𝕊 c hn α hα hsign, normAssoc_toHom]
  have hV : 0 < volV n := by rw [volV_eq_tauR]; exact Hanke2005.tauR_pos n
  have e : (((2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2)) * volV n) ^ Module.finrank ℚ F =
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) * volV n ^ Module.finrank ℚ F := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2)), ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [e]
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
  have h3 : (0 : ℝ) < volV n ^ Module.finrank ℚ F := by positivity
  field_simp

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.normAssoc_toHom
#print axioms QuadFormsKB.Hanke2011Structure.cor_6_4_coeff
