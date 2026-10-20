/-
# The good-prime shape over $F$ is a theorem

**Layer:** number field. $F$ is a number field, $Q$ = `QuadForm (𝓞 F) n`, $\mathfrak p$ = `v : HeightOneSpectrum (𝓞 F)`,
$\mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F` with uniformizer $\varpi$ = `NF.π v` and $\iota = $ `NF.ι v`.

`Siegel/NFMainTerm.lean` and `Siegel/NFGlobalLowerBound.lean` take the good-prime shape of $Q$ as the hypothesis
`hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v` (or `hsh : GoodPrimeShape Q v` at one good prime). Here it is
discharged: at $\mathfrak p \nmid 2\det H$ the completed form `NF.Qp v Q` is $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to a
unit diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with $2^n\prod_i a_i = u^2\,\iota(\det H)$, $u$ a unit
(`goodPrimeShape_of_isGoodPrimeNF`, from the DVR form of Hanke 2004, Lemma 2.1, `DVR.exists_diag_of_unimodular`).

Every theorem of those two files that takes the shape hypothesis then has a hypothesis-free corollary, named with the
suffix `_uncond`; the originals are unchanged.
-/
import QuadFormsKB.Siegel.NFGlobalLowerBound
import QuadFormsKB.LocalDensity.DVRUnimodular
import QuadFormsKB.LocalDensity.NFLocalGeneral

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Matrix Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-- **The good-prime shape holds at every good prime** (Hanke 2004, Lemma 2.1, p. 355, case $\mathfrak p \nmid 2$, with the
determinant tracked, over $F$): if $\mathfrak p \nmid 2\det H$ (`IsGoodPrimeNF Q v`), then over
$\mathfrak o_\mathfrak p$ the form $Q$ has the counts $r_{\varpi^k}(m)$ of a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with
unit $a_i$ and $2^n\prod_i a_i = u^2\,\iota(\det H)$ for a unit $u$ (`GoodPrimeShape Q v`). Proof: `DVR.exists_diag_of_unimodular`
applied to `NF.Qp v Q` at $\varpi$, with $\det H(Q_\mathfrak p) = \iota(\det H)$ (`NF.det_hessian_Qp`). -/
@[kb "hanke2004" "Lemma 2.1, p. 355, at p ∤ 2det H (over F)"]
theorem goodPrimeShape_of_isGoodPrimeNF {Q : QuadForm (𝓞 F) n} {v : HeightOneSpectrum (𝓞 F)}
    (hG : IsGoodPrimeNF Q v) : GoodPrimeShape Q v := by
  obtain ⟨a, ha, hE, u, hu, hdu⟩ := DVR.exists_diag_of_unimodular (NF.Qp v Q) (NF.π v) (NF.irreducible_π v)
    (NF.π_not_dvd_two v hG.1) (NF.π_not_dvd_det v Q hG.2)
  refine ⟨a, ha, fun k m => ((hE.sameCounts (NF.π v)) k m).1, u,
    DVR.dvr_not_dvd_of_isUnit (NF.irreducible_π v) hu, ?_⟩
  rw [hdu, NF.det_hessian_Qp]

/-- The shape hypothesis of `NFMainTerm` / `NFGlobalLowerBound`, as a theorem. -/
theorem hshape_NF (Q : QuadForm (𝓞 F) n) : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v :=
  fun _ hG => goodPrimeShape_of_isGoodPrimeNF hG

/-! ### Hypothesis-free corollaries: `Siegel/NFMainTerm.lean` -/

section MainTerm

variable (v : HeightOneSpectrum (𝓞 F))

/-- `abs_localDensityNF_sub_one_le` without the shape hypothesis: $|\beta_\mathfrak p(m) - 1| \le N\mathfrak p^{-2}$ at every
good $\mathfrak p \nmid m$, $n \ge 4$. -/
theorem abs_localDensityNF_sub_one_le_uncond {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (hG : IsGoodPrimeNF Q v)
    {m : 𝓞 F} (hm : m ∉ v.asIdeal) :
    |NF.localDensity v Q m - 1| ≤ 1 * (N𝔭 v) ^ (-(2 : ℝ)) :=
  abs_localDensityNF_sub_one_le v hn hG (goodPrimeShape_of_isGoodPrimeNF hG) hm

/-- `localConstC'NF_good_three` without the shape hypothesis: $C'_\mathfrak p(T') = 1$ at good $\mathfrak p$, $n = 3$,
$T' \notin \mathfrak p^2$. -/
theorem localConstC'NF_good_three_uncond {Q : QuadForm (𝓞 F) 3} (hG : IsGoodPrimeNF Q v)
    {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) : NF.localConstC' v Q T = 1 :=
  localConstC'NF_good_three v hG (goodPrimeShape_of_isGoodPrimeNF hG) hT2

end MainTerm

/-- **Absolute convergence of $\prod_\mathfrak p\beta_\mathfrak p(m)$ over $F$ for $n \ge 4$** (Hanke 2004, (5.3), p. 368),
unconditionally: `multipliable_eulerFactorNF` with the shape hypothesis discharged. -/
@[kb "hanke2004" "(5.3), p. 368 (n ≥ 4, over F, unconditional)"]
theorem multipliable_eulerFactorNF_uncond {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {m : 𝓞 F} (hm : m ≠ 0) : Multipliable (eulerFactorNF Q m) :=
  multipliable_eulerFactorNF hQ hn (hshape_NF Q) hm

/-- `hasProd_eulerProductNF` without the shape hypothesis. -/
theorem hasProd_eulerProductNF_uncond {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {m : 𝓞 F} (hm : m ≠ 0) : HasProd (eulerFactorNF Q m) (eulerProductNF Q m) :=
  hasProd_eulerProductNF hQ hn (hshape_NF Q) hm

/-- `isEulerProductValueNF_eulerProductNF` without the shape hypothesis. -/
theorem isEulerProductValueNF_eulerProductNF_uncond {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate)
    (hn : 4 ≤ n) {m : 𝓞 F} (hm : m ≠ 0) :
    IsEulerProductValueNF (eulerFactorNF Q m) (eulerProductNF Q m) :=
  isEulerProductValueNF_eulerProductNF hQ hn (hshape_NF Q) hm

/-- `aENF_mul_sq` (the ratio identity for `aENF`, $n \ge 4$) without the shape hypothesis. -/
theorem aENF_mul_sq_uncond [IsTotallyReal F] {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hβ : ∀ v ∈ S, NF.localDensity v Q T ≠ 0) :
    aENF Q (T * x ^ 2) = aENF Q T * ∏ v ∈ S, sqShiftFactorNF Q T v (ordNF v x) :=
  aENF_mul_sq hQ hn (hshape_NF Q) hT0 hT hx hS hβ

/-- **Theorem 5.4 over $F$ for `aENF`** (Hanke 2004, p. 369), $n \ge 4$, unconditionally: `thm_5_4_aENF` with the shape
hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.4, p. 369 (over F, unconditional)"]
theorem thm_5_4_aENF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) :
    aENF Q (T * x ^ 2) = aENF Q T *
      (∏ v ∈ S.filter (IsIsotropicNF Q),
        (NF.localConstC v Q T + (1 - NF.localConstC v Q T) / (N𝔭 v) ^ ((n - 2) * ordNF v x))) *
      (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) :=
  thm_5_4_aENF Q hQ hn (hshape_NF Q) hT0 hT hx hS hst

/-- **(5.13) over $F$ for `aENF`** (Hanke 2004, p. 373), $n \ge 4$, unconditionally: `eq_5_13_aENF` with the shape
hypothesis discharged. -/
@[kb "hanke2004" "(5.13), p. 373 (over F, unconditional)"]
theorem eq_5_13_aENF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) :=
  eq_5_13_aENF Q hQ hQnd hn (hshape_NF Q) hT0 hT hx hS hst

/-- **Theorem 5.7(a) over $F$, first part** (Hanke 2004, p. 372), $n = 3$, unconditionally: `thm_5_7_a_NF` with the
shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part, over F, unconditional)"]
theorem thm_5_7_a_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2)
    {P Pm : ℝ} (hP : IsEulerProductValueNF (eulerFactorNF Q T) P)
    (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    aEWithNF Q T P *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x ≤
      aEWithNF Q (T * x ^ 2) Pm :=
  thm_5_7_a_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2 hP hPm

/-! ### Hypothesis-free corollaries: `Siegel/NFGlobalLowerBound.lean` -/

section GlobalGood

variable (v : HeightOneSpectrum (𝓞 F))

/-- `localConstC'NF_good_even` without the shape hypothesis (Table 2 / corrected (5.12) at good $\mathfrak p$, $n \ge 4$
even). -/
theorem localConstC'NF_good_even_uncond {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (heven : Even n)
    (hG : IsGoodPrimeNF Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if charNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1 :=
  localConstC'NF_good_even v hn heven hG (goodPrimeShape_of_isGoodPrimeNF hG) hT2

/-- `localConstC'NF_good_odd` without the shape hypothesis (Table 2 / corrected (5.12) at good $\mathfrak p$, $n \ge 3$
odd). -/
theorem localConstC'NF_good_odd_uncond {Q : QuadForm (𝓞 F) n} (hn : 3 ≤ n) (hodd : Odd n)
    (hG : IsGoodPrimeNF Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if T ∉ v.asIdeal ∧ charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1 then
        (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) else 1 :=
  localConstC'NF_good_odd v hn hodd hG (goodPrimeShape_of_isGoodPrimeNF hG) hT2

end GlobalGood

/-- **Theorem 5.7(b),(c) over $F$, ratio form, $n \ge 4$ even** (Hanke 2004, p. 373), unconditionally:
`thm_5_7_c_even_NF` with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even, over F, unconditional)"]
theorem thm_5_7_c_even_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal),
          (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_c_even_NF Q hQ hQnd hn heven (hshape_NF Q) hT0 hT hx hS hst hT2

/-- **Theorem 5.7(b) over $F$, ratio form** (Hanke 2004, p. 373), $n = 4$, unconditionally: `thm_5_7_b_NF` with the
shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form, over F, unconditional)"]
theorem thm_5_7_b_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_b_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2

/-- **Theorem 5.7(c) over $F$, ratio form, $n \ge 5$ odd** (Hanke 2004, p. 373), unconditionally: `thm_5_7_c_odd_NF`
with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (ratio form, n odd, over F, unconditional)"]
theorem thm_5_7_c_odd_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (hodd : Odd n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter (fun v => T ∉ v.asIdeal ∧
            charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1),
          (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_c_odd_NF Q hQ hQnd hn hodd (hshape_NF Q) hT0 hT hx hS hst hT2

/-- `le_eulerProductNF` (the Euler-product lower bound engine, $n \ge 4$) without the shape hypothesis. -/
theorem le_eulerProductNF_uncond {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0)
    (A A' : Finset (HeightOneSpectrum (𝓞 F))) (g : HeightOneSpectrum (𝓞 F) → ℝ)
    (hg0 : ∀ v ∉ A, 0 ≤ g v) (hg1 : ∀ v ∉ A', g v = 1)
    (hge : ∀ v ∉ A, (1 - (N𝔭 v) ^ (-(2 : ℝ))) * g v ≤ NF.localDensity v Q T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * (∏ v ∈ A, NF.localDensity v Q T) *
        ∏ v ∈ A' \ A, g v ≤ eulerProductNF Q T :=
  le_eulerProductNF hQ hn (hshape_NF Q) hT0 A A' g hg0 hg1 hge

/-- **$a_E(T') \ge (6/\pi^2)^d\beta_\infty(T')\prod_{\mathfrak p \in B \cup \mathrm{supp}T'}\beta_\mathfrak p(T')$ over $F$**,
$n \ge 4$ (Hanke 2004, proof of Thm 5.7(b),(c), pp. 374–375), unconditionally: `aENF_ge` with the shape hypothesis
discharged. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), pp. 374–375 (over F, ζ_F(2) bound, unconditional)"]
theorem aENF_ge_uncond (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate) (hn : 4 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T ≤
      aENF Q T :=
  aENF_ge Q hQ hQnd hn (hshape_NF Q) hT0 hT

/-- `localDensityNF_good_four_ge` without the shape hypothesis ($n = 4$, good $\mathfrak p$). -/
theorem localDensityNF_good_four_ge_uncond {Q : QuadForm (𝓞 F) 4} (v : HeightOneSpectrum (𝓞 F))
    (hG : IsGoodPrimeNF Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    (1 - (N𝔭 v) ^ (-(2 : ℝ))) *
        (if charNF v Q.hessian.det = -1 ∧ m ∈ v.asIdeal then ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1) ≤
      NF.localDensity v Q m :=
  localDensityNF_good_four_ge v hG (goodPrimeShape_of_isGoodPrimeNF hG) hm

/-- **The $n = 4$ lower bound for $a_E(T')$ over $F$** (Hanke 2004, Thm 5.7(b), p. 373; proof pp. 374–375),
unconditionally: `aENF_four_ge` with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375 (over F, unconditional)"]
theorem aENF_four_ge_uncond (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1) ≤
      aENF Q T :=
  aENF_four_ge Q hQ hQnd (hshape_NF Q) hT0 hT

/-- **Theorem 5.7(b) over $F$, global form** (Hanke 2004, p. 373), $n = 4$, unconditionally: `thm_5_7_b_global_NF`
with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, over F, unconditional)"]
theorem thm_5_7_b_global_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_b_global_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2

/-- `one_sub_le_localConstC'NF_good` without the shape hypothesis: $C'_\mathfrak p(T') \ge 1 - N\mathfrak p^{-2}$ at good
$\mathfrak p$, $n \ge 5$, $T' \notin \mathfrak p^2$. -/
theorem one_sub_le_localConstC'NF_good_uncond {Q : QuadForm (𝓞 F) n} (hn : 5 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (hG : IsGoodPrimeNF Q v) {T : 𝓞 F}
    (hT2 : T ∉ v.asIdeal ^ 2) : 1 - (N𝔭 v) ^ (-(2 : ℝ)) ≤ NF.localConstC' v Q T :=
  one_sub_le_localConstC'NF_good hn v hG (goodPrimeShape_of_isGoodPrimeNF hG) hT2

/-- **Theorem 5.7(c) over $F$, global form** (Hanke 2004, p. 373), $n \ge 5$, unconditionally: `thm_5_7_c_global_NF`
with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (global, n ≥ 5, over F, unconditional)"]
theorem thm_5_7_c_global_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 5 ≤ n)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) :=
  thm_5_7_c_global_NF Q hQ hQnd hn (hshape_NF Q) hT0 hT hx hS hst hT2

/-- `localDensityNF_good_three_eq` without the shape hypothesis: $\beta_\mathfrak p(T') = (1 - N\mathfrak p^{-2})
L_\mathfrak p(1, \psi_{T'})$ at good $\mathfrak p$, $n = 3$, $T' \notin \mathfrak p^2$. -/
theorem localDensityNF_good_three_eq_uncond {Q : QuadForm (𝓞 F) 3} (v : HeightOneSpectrum (𝓞 F))
    (hG : IsGoodPrimeNF Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localDensity v Q T = (1 - (N𝔭 v) ^ (-(2 : ℝ))) * lFactor (psiNF Q T) 1 v :=
  localDensityNF_good_three_eq v hG (goodPrimeShape_of_isGoodPrimeNF hG) hT2

/-- **(5.14) over $F$** (Hanke 2004, p. 375), $n = 3$, unconditionally: `isEulerProductValueNF_three` with the shape
hypothesis discharged. -/
@[kb "hanke2004" "(5.14), p. 375 (n = 3, over F, unconditional)"]
theorem isEulerProductValueNF_three_uncond {Q : QuadForm (𝓞 F) 3} (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT2 : ∀ v, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) {L : ℝ}
    (hL : IsEulerProductValueNF (lFactor (psiNF Q T) 1) L) :
    IsEulerProductValueNF (eulerFactorNF Q T)
      ((∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ)))) *
        (dedekindZetaR F 2)⁻¹ * L) :=
  isEulerProductValueNF_three hQnd (hshape_NF Q) hT2 hL

/-- **Theorem 5.7(a) over $F$, second part** (Hanke 2004, p. 372), $n = 3$, with $c \le L_F(1, \psi_{T'})$ as hypothesis,
unconditionally in the good-prime shape: `thm_5_7_a_second_NF` with the shape hypothesis discharged. -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (second part, over F, unconditional)"]
theorem thm_5_7_a_second_NF_uncond [IsTotallyReal F] (Q : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2)
    {L : ℝ} (hL : IsEulerProductValueNF (lFactor (psiNF Q T) 1) L) {c : ℝ} (hc : c ≤ L)
    {Pm : ℝ} (hPm : IsEulerProductValueNF (eulerFactorNF Q (T * x ^ 2)) Pm) :
    c * betaInfNF Q (T : F) * (dedekindZetaR F 2)⁻¹ *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ)))) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x ≤
      aEWithNF Q (T * x ^ 2) Pm :=
  thm_5_7_a_second_NF Q hQ hQnd (hshape_NF Q) hT0 hT hx hS hst hT2 hL hc hPm

end QuadFormsKB.Siegel

end
