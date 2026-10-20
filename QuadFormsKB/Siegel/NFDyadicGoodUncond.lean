/-
# Theorem 5.7(b), (c) over $F$ with bad set $\{\mathfrak p \mid N\}$: hypothesis-free and global forms

**Layer:** number field. Composes `Siegel/NFDyadicGood.lean` (dyadic $\mathfrak p \nmid N$ are good) with
`Siegel/NFGoodPrime.lean` (the good-prime shape `GoodPrimeShape` holds at every $\mathfrak p \nmid 2\det H$).

**Which hypothesis is needed where.** The hypothesis `hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v` of
`NFDyadicGood.lean` is used only at *non-dyadic* $\mathfrak p \nmid N$ (`localConstC'NF_level_even`) and in the Euler product
(`isEulerProductValueNF_eulerProductNF`, again only at $\mathfrak p \nmid 2\det H$). The unit-diagonal shape is never asked of a
dyadic prime: the dyadic factors come from the pair-sum form (`NF.localConstC'_of_level_zero_dyadic`,
`NF.localDensity_ge_of_level_zero_dyadic`), which needs only `NF.NotDvdLevel`. So `hshape` is discharged completely by
`hshape_NF`, giving `_uncond` versions of the three theorems of `NFDyadicGood.lean`.

**Global forms.** With the bad set $B_N = \{\mathfrak p \mid N\} \subseteq \{\mathfrak p \mid 2\det H\}$ (`badLevelNF`) the lower
bounds `aENF_ge`, `aENF_four_ge`, `thm_5_7_b_global_NF`, `thm_5_7_c_global_NF` are re-proved as `*_level` versions: at a
dyadic $\mathfrak p \nmid N$ the factor $\beta_\mathfrak p(T') \ge 1 - \varepsilon N\mathfrak p^{-n/2} \ge 1 - N\mathfrak p^{-2}$
(`one_sub_le_localDensityNF_level`) replaces the (non-existent) good-prime bound, and similarly for $C'_\mathfrak p$.
-/
import QuadFormsKB.Siegel.NFDyadicGood
import QuadFormsKB.Siegel.NFGoodPrime

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-! ### `_uncond` versions of `NFDyadicGood.lean` -/

/-- `localConstC'NF_level_even` without the shape hypothesis. -/
theorem localConstC'NF_level_even_uncond (v : HeightOneSpectrum (𝓞 F)) {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n)
    (heven : Even n) (hN : NF.NotDvdLevel v Q) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1 :=
  localConstC'NF_level_even v hn heven hN
    (fun h2 => hshape_NF Q v ((notDvdLevel_iff_isGoodPrimeNF v h2).1 hN)) hT2

/-- **Theorem 5.7(c), $n \ge 4$ even, ratio form, bad primes $\mathfrak p \mid N$ only, unconditionally**:
`thm_5_7_c_even_level_NF` with the shape hypothesis discharged (`hshape_NF`). -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even, over F, bad set p | N, unconditional)"]
theorem thm_5_7_c_even_level_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal),
          (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_c_even_level_NF Q hQ hQnd hn heven (hshape_NF Q) hT0 hT hx hS hst hT2

/-- **Theorem 5.7(b), $n = 4$, ratio form, bad primes $\mathfrak p \mid N$ only, unconditionally**:
`thm_5_7_b_level_NF` with the shape hypothesis discharged (`hshape_NF`). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form, over F, bad set p | N, unconditional)"]
theorem thm_5_7_b_level_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_b_level_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2

/-! ### The bad set $\{\mathfrak p \mid N\}$ and local lower bounds -/

/-- **The primes dividing the level**: $\{\mathfrak p : \mathfrak p \mid N\} = \{\mathfrak p \mid 2\det H : \neg\,\mathfrak p \nmid N\}$
(`mem_badLevelNF`), a subset of `badPrimesNF Q`. -/
def badLevelNF (Q : QuadForm (𝓞 F) n) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (badPrimesNF Q).filter (fun v => ¬ NF.NotDvdLevel v Q)

theorem mem_badLevelNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ badLevelNF Q ↔ ¬ NF.NotDvdLevel v Q := by
  rw [badLevelNF, Finset.mem_filter, mem_badPrimesNF hQ]
  exact ⟨fun h => h.2, fun h => ⟨fun hG => h (notDvdLevel_of_isGoodPrimeNF v hG), h⟩⟩

theorem arfSignQ_cast_le_one (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm (𝓞 F) n) :
    ((DVR.arfSignQ (NF.Qp v Q) (NF.π v) : ℤ) : ℝ) ≤ 1 := by
  unfold DVR.arfSignQ; split_ifs <;> norm_num

/-- $1 - N\mathfrak p^{-2} \le \beta_\mathfrak p(T')$ at every $\mathfrak p \nmid N$ (dyadic included), $n \ge 4$, $T' \notin \mathfrak p$:
non-dyadic from Table 1 (`abs_localDensityNF_sub_one_le`), dyadic from `NF.localDensity_ge_of_level_zero_dyadic`
($1 - \varepsilon N\mathfrak p^{-n/2} \ge 1 - N\mathfrak p^{-2}$). -/
theorem one_sub_le_localDensityNF_level {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    (hN : NF.NotDvdLevel v Q) {T : 𝓞 F} (hT0 : T ≠ 0) (hTv : T ∉ v.asIdeal) :
    1 - (N𝔭 v) ^ (-(2 : ℝ)) ≤ NF.localDensity v Q T := by
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  · have h := NF.localDensity_ge_of_level_zero_dyadic v Q h2 hN (by omega) T hT0
    rw [ite_eq_right (fun h => hTv h.2), mul_one] at h
    refine le_trans ?_ h
    have hN2 := two_le_normP_real v
    have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
      rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
    rw [hr]
    have h1 := arfSignQ_cast_le_one v Q
    have hpos : (0 : ℝ) < (N𝔭 v) ^ (n / 2) := by positivity
    have hA : ((DVR.arfSignQ (NF.Qp v Q) (NF.π v) : ℤ) : ℝ) / (N𝔭 v) ^ (n / 2) ≤ 1 / (N𝔭 v) ^ (n / 2) :=
      div_le_div_of_nonneg_right h1 hpos.le
    have hB : 1 / (N𝔭 v) ^ (n / 2) ≤ 1 / (N𝔭 v) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
    linarith
  · have hG := (notDvdLevel_iff_isGoodPrimeNF v h2).1 hN
    have := abs_localDensityNF_sub_one_le v hn hG (hshape_NF Q v hG) hTv
    linarith [(abs_le.1 this).1]

/-- **$\beta_\mathfrak p(m)$ at every $\mathfrak p \nmid N$, $n = 4$** (Table 1 / L10, p. 374): as `localDensityNF_good_four_ge`
with $\chi(\mathfrak p) = $ `quadSymbolNF v (det H)`, valid at dyadic $\mathfrak p \nmid N$ too. -/
theorem localDensityNF_level_four_ge {Q : QuadForm (𝓞 F) 4} (v : HeightOneSpectrum (𝓞 F))
    (hN : NF.NotDvdLevel v Q) {m : 𝓞 F} (hm : m ≠ 0) :
    (1 - (N𝔭 v) ^ (-(2 : ℝ))) *
        (if quadSymbolNF v Q.hessian.det = -1 ∧ m ∈ v.asIdeal then ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1) ≤
      NF.localDensity v Q m := by
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  · have h := NF.localDensity_ge_of_level_zero_dyadic v Q h2 hN (by norm_num) m hm
    have harf := arfSignQ_eq_quadSymbolNF v h2 hN (n := 4) (by norm_num)
    have hε : quadSymbolNF v Q.hessian.det = DVR.arfSignQ (NF.Qp v Q) (NF.π v) := by
      rw [harf]; congr 1; norm_num
    rw [hε]
    simp only [show (4 : ℕ) / 2 = 2 from rfl, show (4 : ℕ) / 2 - 1 = 1 from rfl, pow_one] at h
    refine le_trans (mul_le_mul_of_nonneg_right ?_ ?_) h
    · have hN2 := two_le_normP_real v
      have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
        rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
      rw [hr]
      have h1 := arfSignQ_cast_le_one v Q
      have hpos : (0 : ℝ) < (N𝔭 v) ^ 2 := by positivity
      have : ((DVR.arfSignQ (NF.Qp v Q) (NF.π v) : ℤ) : ℝ) / (N𝔭 v) ^ 2 ≤ 1 / (N𝔭 v) ^ 2 :=
        div_le_div_of_nonneg_right h1 hpos.le
      linarith
    · have hN2 := two_le_normP_real v
      split_ifs
      · exact div_nonneg (by linarith) (by linarith)
      · exact zero_le_one
  · have hG := (notDvdLevel_iff_isGoodPrimeNF v h2).1 hN
    rw [quadSymbolNF_eq_charNF v h2]
    exact localDensityNF_good_four_ge_uncond v hG hm

/-- $1 - N\mathfrak p^{-2} \le C'_\mathfrak p(T')$ at every $\mathfrak p \nmid N$ (dyadic included), $n \ge 5$, $T' \notin \mathfrak p^2$. -/
theorem one_sub_le_localConstC'NF_level {Q : QuadForm (𝓞 F) n} (hn : 5 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (hN : NF.NotDvdLevel v Q) {T : 𝓞 F}
    (hT2 : T ∉ v.asIdeal ^ 2) : 1 - (N𝔭 v) ^ (-(2 : ℝ)) ≤ NF.localConstC' v Q T := by
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  · have he : Even n := by
      by_contra h
      exact not_notDvdLevel_of_odd v h2 (Nat.not_even_iff_odd.1 h) hN
    have hN2 := two_le_normP_real v
    have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
      rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
    have h0 : 0 ≤ 1 / (N𝔭 v) ^ 2 := by positivity
    rw [hr, localConstC'NF_level_even_uncond v (by omega) he hN hT2]
    split_ifs
    · set X := (N𝔭 v) ^ ((n - 2) / 2)
      have hX : 1 / X ≤ 1 / (N𝔭 v) ^ 2 :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by linarith) (by obtain ⟨j, rfl⟩ := he; omega))
      have hX0 : 0 < X := by positivity
      have : 1 - 1 / X ≤ X / (X + 1) := by
        rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
          le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · linarith
  · exact one_sub_le_localConstC'NF_good_uncond hn v ((notDvdLevel_iff_isGoodPrimeNF v h2).1 hN) hT2

/-! ### Global lower bounds with bad set $\{\mathfrak p \mid N\}$ -/

/-- **`aENF_ge` with bad set $\{\mathfrak p \mid N\}$** ($n \ge 4$): $a_E(T') \ge (6/\pi^2)^d\beta_\infty(T')
\prod_{\mathfrak p \in B_N \cup \mathrm{supp}(T')}\beta_\mathfrak p(T')$, with $B_N$ = `badLevelNF` (dyadic $\mathfrak p \nmid N$ are no
longer bad). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), pp. 374–375 (over F, ζ_F(2) bound, bad set p | N)"]
theorem aENF_ge_level (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T ≤
      aENF Q T := by
  have h := le_eulerProductNF hQnd hn hshape hT0 (badLevelNF Q ∪ primesDividing T) ∅ (fun _ => 1)
    (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun v hv => by
      rw [Finset.mem_union, not_or, mem_badLevelNF hQnd, not_not, mem_primesDividing hT0] at hv
      rw [mul_one]
      exact one_sub_le_localDensityNF_level hn v hv.1 hT0 hv.2)
  simp only [Finset.empty_sdiff, Finset.prod_empty, mul_one] at h
  rw [aENF, aEWithNF]
  calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T
      = betaInfNF Q (T : F) * ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F *
        ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (betaInfNF_nonneg hQ hT)

/-- `aENF_ge_level` unconditionally (shape hypothesis discharged by `hshape_NF`). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), pp. 374–375 (over F, ζ_F(2) bound, bad set p | N, unconditional)"]
theorem aENF_ge_level_uncond (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    (hn : 4 ≤ n) {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T ≤
      aENF Q T :=
  aENF_ge_level Q hQ hQnd hn (hshape_NF Q) hT0 hT

/-- **`aENF_four_ge` with bad set $\{\mathfrak p \mid N\}$** ($n = 4$): with $\chi(\mathfrak p) = \left(\frac{\det H}{\mathfrak p}\right)$
(`quadSymbolNF`),
$$a_E(T') \ge (6/\pi^2)^d\beta_\infty(T')\prod_{\mathfrak p \in B_N}\beta_\mathfrak p(T')
  \prod_{\mathfrak p \mid T',\ \mathfrak p \nmid N,\ \chi(\mathfrak p) = -1}\frac{N\mathfrak p - 1}{N\mathfrak p + 1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375 (over F, bad set p | N)"]
theorem aENF_four_ge_level (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1) ≤
      aENF Q T := by
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if quadSymbolNF v Q.hessian.det = -1 ∧ T ∈ v.asIdeal then ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1
    with hg
  have h := le_eulerProductNF hQnd le_rfl hshape hT0 (badLevelNF Q) (primesDividing T) g
    (fun v _ => by
      simp only [hg]; split_ifs
      · have := two_le_normP_real v; exact div_nonneg (by linarith) (by linarith)
      · exact zero_le_one)
    (fun v hv => by
      simp only [hg]; rw [ite_eq_right]; rintro ⟨-, h⟩; exact hv ((mem_primesDividing hT0).2 h))
    (fun v hv => by
      rw [mem_badLevelNF hQnd, not_not] at hv
      exact localDensityNF_level_four_ge v hv hT0)
  have hgp : ∏ v ∈ primesDividing T \ badLevelNF Q, g v =
      ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
        ((N𝔭 v) - 1) / ((N𝔭 v) + 1) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hTv : T ∈ v.asIdeal := (mem_primesDividing hT0).1 (Finset.mem_sdiff.1 hv).1
    simp only [hg, hTv, and_true]
  rw [hgp] at h
  rw [aENF, aEWithNF]
  calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)
      = betaInfNF Q (T : F) * ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (betaInfNF_nonneg hQ hT)

/-- `aENF_four_ge_level` unconditionally. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375 (over F, bad set p | N, unconditional)"]
theorem aENF_four_ge_level_uncond (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1) ≤
      aENF Q T :=
  aENF_four_ge_level Q hQ hQnd (hshape_NF Q) hT0 hT

/-- **Theorem 5.7(b), global form, bad set $\{\mathfrak p \mid N\}$** ($n = 4$): `thm_5_7_b_global_NF` with every $\mathfrak p \nmid N$
(dyadic included) good and $\chi(\mathfrak p) = $ `quadSymbolNF v (det H)`. The printed product over
$\mathfrak p \mid m,\ \mathfrak p \nmid N,\ \chi = -1$ is now reproduced exactly. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, over F, bad set p | N)"]
theorem thm_5_7_b_global_level_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) := by
  have hr := thm_5_7_b_level_NF Q hQ hQnd hshape hT0 hT hx hS hst hT2
  have hg := aENF_four_ge_level Q hQ hQnd hshape hT0 hT
  have hC : 0 ≤ ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
      NF.localConstC' v Q T := Finset.prod_nonneg fun v _ => localConstC'NF_nonneg v Q hQnd (by norm_num) hT0
  have hN : 0 ≤ (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 := by positivity
  have hI : 0 ≤ ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
      (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by
    positivity
  calc _ = ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by ring
    _ ≤ aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by
          gcongr
    _ ≤ _ := hr

/-- `thm_5_7_b_global_level_NF` unconditionally. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, over F, bad set p | N, unconditional)"]
theorem thm_5_7_b_global_level_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q, NF.localDensity v Q T) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badLevelNF Q).filter (fun v => quadSymbolNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_b_global_level_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2

/-- **Theorem 5.7(c), global form, $n \ge 5$, bad set $\{\mathfrak p \mid N\}$**: `thm_5_7_c_global_NF` with $B_N$ = `badLevelNF`
in place of $B$. (For odd $n$ every dyadic $\mathfrak p$ divides $N$, so only even $n$ gains.) -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (global, n ≥ 5, over F, bad set p | N)"]
theorem thm_5_7_c_global_level_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 5 ≤ n) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) := by
  have hr := aEWithNF_mul_sq_ge Q hQ hQnd (by omega) hT0 hT hx hS hst (fun v => NF.NotDvdLevel v Q)
    (fun v => 1 - (N𝔭 v) ^ (-(2 : ℝ)))
    (fun v hv hN => ⟨one_sub_normP_rpow_pos v, one_sub_le_localConstC'NF_level hn v hN (hT2 v hv hN)⟩)
    (isEulerProductValueNF_eulerProductNF hQnd (by omega) hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd (by omega) hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))
  have hg := aENF_ge_level Q hQ hQnd (by omega) hshape hT0 hT
  have hz := six_div_pi_sq_pow_le_prod (F := F) (S.filter (fun v => NF.NotDvdLevel v Q))
  have hC : 0 ≤ ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
      NF.localConstC' v Q T :=
    Finset.prod_nonneg fun v _ => localConstC'NF_nonneg v Q hQnd (by omega) hT0
  have hN : 0 ≤ (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) := by positivity
  have hA : 0 ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
      ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T :=
    mul_nonneg (mul_nonneg (by positivity) (betaInfNF_nonneg hQ hT))
      (Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQnd hT0)
  have hz0 : (0 : ℝ) ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F := by positivity
  have hE : (0 : ℝ) ≤ aENF Q T := hA.trans hg
  calc _ = ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) * (6 / Real.pi ^ 2) ^ Module.finrank ℚ F := by
        rw [pow_mul']; ring
    _ ≤ aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (fun v => NF.NotDvdLevel v Q), (1 - (N𝔭 v) ^ (-(2 : ℝ))) := by
          gcongr
    _ ≤ _ := hr

/-- `thm_5_7_c_global_level_NF` unconditionally. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (global, n ≥ 5, over F, bad set p | N, unconditional)"]
theorem thm_5_7_c_global_level_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 5 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ badLevelNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_c_global_level_NF Q hQ hQnd hn (hshape_NF Q) hT0 hT hx hS hst hT2

end QuadFormsKB.Siegel
