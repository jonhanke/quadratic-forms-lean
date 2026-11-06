/-
# Hanke 2005, (3.3) at non-dyadic self-dual places (proved), and the remaining named input

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves** Shimura's local factor (3.3) at every non-dyadic place $\mathfrak p$ where $\widetilde\Lambda_\mathfrak p = \Lambda_\mathfrak p$
(`siegelDensity_selfDual_nondyadic`; no maximality needed): there $\Lambda_\mathfrak p$ is unimodular, its self-density is
$|O(\bar Q)|/q^{n(n-1)/2}$ with the closed forms of `Tamagawa/OrthFq.lean`, and $t_\mathfrak p$ and $\chi$ match Hanke's $\xi$
(`anisoDim_le_two_of_dualIndexAt_eq_one`, `anisoDim_eq_two_iff`, `not_isRamifiedAt_of_dualIndexAt_eq_one`).
These are all but finitely many places of a given form.

**Named input (smaller)** `ShimuraMaximalDensityRest F`: (3.3) only at the remaining places (dyadic, or
$\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$). It implies `ShimuraMaximalDensity F`
(`shimuraMaximalDensity_of_rest`).
-/
import QuadFormsKB.Literature.Hanke2005.LocalTypes
import QuadFormsKB.Tamagawa.OrthFq

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

namespace DensitySD

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem ppow_eq {q : ℝ} (hq : 0 < q) (k : ℕ) :
    ppow q k = ∏ i ∈ Finset.range k, (1 - (q ^ (2 * (i + 1)))⁻¹) := by
  unfold ppow
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_neg hq.le, show (2 * ((i : ℝ) + 1)) = ((2 * (i + 1) : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem rpow_neg_nat {q : ℝ} (hq : 0 < q) (m : ℕ) : q ^ (-(m : ℝ)) = (q ^ m)⁻¹ := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]

theorem q_eq (v : HeightOneSpectrum (𝓞 F)) : ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) = normQ v := by
  rw [NF.q_completion]

theorem not_dvd_two (h2 : IsUnit (2 : 𝔬)) : ¬ NF.π v ∣ 2 :=
  fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit h h2)

theorem not_dvd_det {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (h : dualIndexAt v Q₀ = 1) :
    ¬ NF.π v ∣ (NF.Qp v Q₀).hessian.det :=
  fun hd => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit hd (isUnit_det_of_dualIndexAt_eq_one v Q₀ h))

/-- The character $\chi$ of the unimodular form is $+1$ if $\delta$ is a square and $-1$ otherwise. -/
theorem chiDisc_facts {m : ℕ} (Q₀ : QuadForm (𝓞 F) (2 * m)) (h2 : IsUnit (2 : 𝔬))
    (h : dualIndexAt v Q₀ = 1) :
    (IsSquare (algebraMap F Fv (discK Q₀)) → DVR.chiDisc (NF.Qp v Q₀) = 1) ∧
      (¬ IsSquare (algebraMap F Fv (discK Q₀)) → DVR.chiDisc (NF.Qp v Q₀) = -1) := by
  have hu := isUnit_det_of_dualIndexAt_eq_one v Q₀ h
  set d : 𝔬 := (NF.Qp v Q₀).hessian.det with hd
  have hπd : ¬ NF.π v ∣ d := not_dvd_det v Q₀ h
  have key : algebraMap F Fv ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) = (d : Fv) := by
    rw [hd, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hev : Even (2 * m) := even_two_mul m
  have hsq : IsSquare (algebraMap F Fv (discK Q₀)) ↔ IsSquare ((-1 : 𝔬) ^ m * d) := by
    rw [isSquare_algebraMap_discK_iff v Q₀ hev, det_hessian_Qf, key,
      show 2 * m / 2 = m by omega, ← DVR.isSquare_algebraMap_iff (v.adicCompletion F) ((-1 : 𝔬) ^ m * d)]
    simp
  have hnd : ¬ NF.π v ∣ ((-1 : 𝔬) ^ m * d) := fun hdv =>
    hπd ((((isUnit_one.neg).pow m).dvd_mul_left).1 hdv)
  have h2F : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have : IsUnit (IsLocalRing.residue 𝔬 (2 : 𝔬)) := h2.map _
    rw [map_ofNat] at this
    exact this.ne_zero
  have hres : IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ m * d) ≠ 0 := fun h0 =>
    hnd ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).1 h0)
  have hchi : DVR.chiDisc (NF.Qp v Q₀) = quadraticChar _ (IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ m * d)) := by
    unfold DVR.chiDisc DVR.resGramDet
    have e : (-1 : IsLocalRing.ResidueField 𝔬) ^ (2 * m / 2) *
        (IsLocalRing.residue 𝔬 (NF.Qp v Q₀).hessian.det / 2 ^ (2 * m)) =
        IsLocalRing.residue 𝔬 ((-1 : 𝔬) ^ m * d) * (((2 : IsLocalRing.ResidueField 𝔬) ^ m)⁻¹) ^ 2 := by
      rw [show 2 * m / 2 = m by omega, ← hd]
      simp only [map_mul, map_pow, map_neg, map_one]
      field_simp
      ring
    rw [e, map_mul, quadraticChar_sq_one' (inv_ne_zero (pow_ne_zero _ h2F)), mul_one]
  have hiff := DVR.isSquare_iff_quadraticChar_residue (NF.irreducible_π v) (not_dvd_two v h2) hnd
  refine ⟨fun hs => ?_, fun hns => ?_⟩
  · rw [hchi]; exact hiff.1 (hsq.1 hs)
  · rw [hchi]
    rcases quadraticChar_dichotomy hres with h1 | h1
    · exact absurd (hsq.2 (hiff.2 h1)) hns
    · exact h1

end DensitySD

open DensitySD in
/-- **(3.3) at a non-dyadic self-dual place** (Hanke thesis, (3.3), p. 8; [Shi, Thm 8.6(3)]): if $2$ is a unit of
$\mathfrak o_\mathfrak p$ and $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = 1$, Siegel's density is
$\alpha_\mathfrak p = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p = Λ_p; proved)"]
theorem siegelDensity_selfDual_nondyadic (v : HeightOneSpectrum (𝓞 F)) (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (h2 : IsUnit (2 : v.adicCompletionIntegers F)) (h : dualIndexAt v Q₀ = 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  have hπ := NF.irreducible_π v
  have hπ2 := not_dvd_two v h2
  have hπd := not_dvd_det v Q₀ h
  have hq := q_eq v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  have hle := anisoDim_le_two_of_dualIndexAt_eq_one v Q₀ hQ h
  have hpar := anisoDim_parity v Q₀ hQ
  rw [h, one_mul, NF.siegelDensity, if_pos (rfl : n = n), NF.localDensityForm_eq_completion]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    have hm2 : 2 ≤ m := by omega
    rw [DVR.localDensityForm_self_even (NF.π v) m (by omega) _ hπ hπ2 hπd, hq]
    obtain ⟨hs, hns⟩ := chiDisc_facts v Q₀ h2 h
    have hiff := anisoDim_eq_two_iff v Q₀ hQ (even_two_mul m)
    have hr := not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ (even_two_mul m) h
    have hm' : 2 * m / 2 = m := by omega
    have hpar' : anisoDim v Q₀ % 2 = 0 := by omega
    unfold xiAt
    by_cases ht : anisoDim v Q₀ = 2
    · have hn := hns (hiff.1 ht)
      rw [ht, hn]
      simp only [xiShimura, hr, ite_false, hm', h, ite_true, rpow_neg_nat (hq0), ppow_eq hq0]
      push_cast
      ring
    · have ht0 : anisoDim v Q₀ = 0 := by omega
      have hn := hs (by_contra fun hc => ht (hiff.2 hc))
      rw [ht0, hn]
      simp only [xiShimura, hm', rpow_neg_nat hq0, ppow_eq hq0]
      push_cast
      ring
  · subst hm
    have ht : anisoDim v Q₀ = 1 := by omega
    rw [DVR.localDensityForm_self_odd (NF.π v) m _ hπ hπ2 hπd, hq]
    unfold xiAt
    rw [ht]
    simp only [xiShimura, show (2 * m + 1) / 2 = m by omega, ppow_eq hq0]
    ring

/-- **(3.3) at the remaining places** (Hanke thesis, (3.3), p. 8, from [Shi, Thm 8.6(3), Prop. 3.9, (3.1.9)]) — a
**named input**, not proved: the statement of `ShimuraMaximalDensity` restricted to the places $\mathfrak p$ that are
dyadic or have $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$ (finitely many for a given form; at the other places it is
`siegelDensity_selfDual_nondyadic`). Not equivalent to Theorem 5.1: a statement about single local densities.
Field: `beta_eq`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places and places dividing the discriminant)"]
structure ShimuraMaximalDensityRest (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local factor (3.3) at a dyadic place or a place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$. -/
  beta_eq : ∀ {n : ℕ}, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ → ShimuraDetHyp Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), (¬ IsUnit (2 : v.adicCompletionIntegers F) ∨ dualIndexAt v Q₀ ≠ 1) →
      hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) =
        ‖((2 : v.adicCompletion F) • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))).det‖ ^ (((n : ℝ) + 1) / 2) *
          (‖(2 : v.adicCompletion F)‖ ^ n)⁻¹ * dualIndexAt v Q₀ * xiAt v Q₀

/-- **The remaining places suffice:** `ShimuraMaximalDensityRest F` implies `ShimuraMaximalDensity F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (reduction to the remaining places)"]
theorem shimuraMaximalDensity_of_rest (I : ShimuraMaximalDensityRest F) : ShimuraMaximalDensity F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v => ?_⟩
  by_cases hv : ¬ IsUnit (2 : v.adicCompletionIntegers F) ∨ dualIndexAt v Q₀ ≠ 1
  · exact I.beta_eq hn Q₀ hQ hmax hdet v hv
  · push Not at hv
    obtain ⟨h2, h1⟩ := hv
    rw [hankeBeta_gramV v Q₀ hQ, siegelDensity_selfDual_nondyadic v hn Q₀ hQ h2 h1]
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow]
    have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
    generalize ‖(2 : v.adicCompletion F)‖ = a at *
    have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
      have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
      rw [Nat.cast_div hev (by norm_num)]
      rcases n with _ | n
      · simp
      · push_cast; simp
    have e : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
        ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
      congr 1; ring
    rw [e]; ring

end QuadFormsKB.Hanke2005
