/-
# Theorem 5.7(b), (c) over a totally real field $F$: good-prime products and global factors

**Layer:** number field (continues `NFMainTerm.lean`; same notation: $Q$ over $\mathcal O_F$, $\mathfrak p$ = `v`,
$N\mathfrak p$ = `Ideal.absNorm v.asIdeal`, $d = [F:\mathbb{Q}]$). Every result here assumes the good-prime shape of $Q$
(`GoodPrimeShape`) at the good primes $\mathfrak p \nmid 2\det H$; dyadic $\mathfrak p$ are bad, as $p = 2$ is over
$\mathbb{Q}$ (`GlobalLowerBound.lean`).

**The character.** $\chi_\mathfrak p(x)$ = `charNF v x` is the quadratic character of the residue field $\mathcal O_F/\mathfrak p$ at
$x$ (the symbol $(\frac{x}{\mathfrak p})$). Hanke's $\Phi_n(\mathfrak p)$ (p. 357) at a good $\mathfrak p$ is
$\chi_\mathfrak p((-1)^{n/2}\det H)$ for $n$ even and $\chi_\mathfrak p((-1)^{(n-1)/2}\,2\det H\,T')$ for $n$ odd (`charNF_shape_even`,
`charNF_shape_odd`; $D = \det H/2^n$ differs from $\det H$ by a square for $n$ even, by $2\cdot$square for $n$ odd).

**Ratio form** (Table 2 at good $\mathfrak p$, (5.12) corrected): `localConstC'NF_good_even`, `localConstC'NF_good_odd`,
and `thm_5_7_c_even_NF`, `thm_5_7_b_NF`, `thm_5_7_c_odd_NF` (the number-field forms of `thm_5_7_c_even`, `thm_5_7_b`,
`thm_5_7_c_odd`).

**Global factors** (`NFEuler.six_div_pi_sq_pow_le_prod`: $\prod_{\mathfrak p \in S}(1 - N\mathfrak p^{-2}) \ge
\zeta_F(2)^{-1} \ge (6/\pi^2)^d$):
* `aENF_ge` ($n \ge 4$): $a_E(T') \ge (6/\pi^2)^d\,\beta_\infty(T')\prod_{\mathfrak p \in B \cup \mathrm{supp}(T')}\beta_\mathfrak p(T')$,
  $B$ the bad primes (`badPrimesNF`);
* `aENF_four_ge` ($n = 4$, Thm 5.7(b)): $a_E(T') \ge (6/\pi^2)^d\beta_\infty(T')\prod_{\mathfrak p \in B}\beta_\mathfrak p(T')
  \prod_{\mathfrak p \mid T'\ \text{good},\ \chi(\mathfrak p) = -1}\frac{N\mathfrak p - 1}{N\mathfrak p + 1}$, $\chi(\mathfrak p) = \chi_\mathfrak p(\det H)$;
* `thm_5_7_b_global_NF`, `thm_5_7_c_global_NF`: the two combined with the ratio forms;
* `betaInfNF_eq_norm`: $\beta_\infty(T') = \big(\prod_w\frac{n\omega_n}{2}D_w^{-1/2}\big)N(T')^{(n-2)/2}$.

**Theorem 5.7(a), second part** ($n = 3$): `psiNF` ($\psi_{T'}$), `isEulerProductValueNF_three` ($\prod_\mathfrak p\beta_\mathfrak p(T')
= L_F(1,\psi_{T'})\zeta_F(2)^{-1}\prod_{\mathfrak p \in B}\beta_\mathfrak p(T')/(1 - N\mathfrak p^{-2})$ in the natural order) and
`thm_5_7_a_second_NF`, with the effective lower bound for $L_F(1,\psi_{T'})$ as a hypothesis, as in the paper.

The constants are the explicit $(6/\pi^2)^d$-type ones (the paper's $1/L_F(2,\chi)$, $\zeta_F(n-2)/\zeta_F((n-2)/2)^2$,
… are bounded below by them; `NFEuler.hankeEX` is not needed for these bounds).
-/
import QuadFormsKB.Siegel.NFMainTerm

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-! ### The quadratic character at $\mathfrak p$ -/

/-- **The quadratic residue symbol $\left(\frac{x}{\mathfrak p}\right)$** = the quadratic character of the residue field
$\mathfrak o_\mathfrak p/\varpi \cong \mathcal O_F/\mathfrak p$ at the image of $x$ ($0$ for $x \in \mathfrak p$). -/
def charNF (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) : ℤ :=
  quadraticChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v x))

section Good

variable (v : HeightOneSpectrum (𝓞 F))

local notation "𝔽" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)
local notation "res" => IsLocalRing.residue (v.adicCompletionIntegers F)

theorem quadraticChar_res_sq {z : v.adicCompletionIntegers F} (hz : ¬ NF.π v ∣ z) :
    quadraticChar 𝔽 (res z) ^ 2 = 1 := by
  rw [← map_pow, ← map_pow]
  exact quadraticChar_sq_one' fun h => hz ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) z).1 h)

/-- **$\Phi_n$ from the shape, $n$ even:** if $2^n\prod_i a_i = u^2\det H$ ($u$ a unit, $\mathfrak p \nmid 2$), then
$\chi_\mathfrak p((-1)^s\prod_i a_i) = \chi_\mathfrak p((-1)^s\det H)$. -/
theorem charNF_shape_even {Q : QuadForm (𝓞 F) n} (heven : Even n)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {a : Fin n → v.adicCompletionIntegers F}
    {u : v.adicCompletionIntegers F} (hu : ¬ NF.π v ∣ u)
    (hprod : 2 ^ n * ∏ i, a i = u ^ 2 * NF.ι v Q.hessian.det) (s : ℕ) :
    quadraticChar 𝔽 (res ((-1) ^ s * ∏ i, a i)) = charNF v ((-1) ^ s * Q.hessian.det) := by
  have e := congrArg (fun z => quadraticChar 𝔽 (res z)) hprod
  simp only [map_mul, map_pow] at e
  have h2' := quadraticChar_res_sq v (not_π_dvd_two h2)
  have hu' := quadraticChar_res_sq v hu
  have hpow : quadraticChar 𝔽 (res 2) ^ n = 1 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, ← two_mul, pow_mul, h2', one_pow]
  rw [hpow, one_mul, hu', one_mul] at e
  simp only [charNF, map_mul, map_pow, map_neg, map_one, e]

/-- **$\Phi_n$ from the shape, $n$ odd:** if $2^n\prod_i a_i = u^2\det H$, then
$\chi_\mathfrak p((-1)^s\prod_i a_i\,T) = \chi_\mathfrak p((-1)^s\,2\det H\,T)$. -/
theorem charNF_shape_odd {Q : QuadForm (𝓞 F) n} (hodd : Odd n)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {a : Fin n → v.adicCompletionIntegers F}
    {u : v.adicCompletionIntegers F} (hu : ¬ NF.π v ∣ u)
    (hprod : 2 ^ n * ∏ i, a i = u ^ 2 * NF.ι v Q.hessian.det) (s : ℕ) (T : 𝓞 F) :
    quadraticChar 𝔽 (res ((-1) ^ s * (∏ i, a i) * NF.ι v T)) =
      charNF v ((-1) ^ s * (2 * Q.hessian.det) * T) := by
  have e := congrArg (fun z => quadraticChar 𝔽 (res z)) hprod
  simp only [map_mul, map_pow] at e
  have h2' := quadraticChar_res_sq v (not_π_dvd_two h2)
  have hu' := quadraticChar_res_sq v hu
  have hpow : quadraticChar 𝔽 (res 2) ^ n = quadraticChar 𝔽 (res 2) := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, h2', one_pow, one_mul]
  rw [hpow, hu', one_mul] at e
  have hA : quadraticChar 𝔽 (res (∏ i, a i)) =
      quadraticChar 𝔽 (res 2) * quadraticChar 𝔽 (res (NF.ι v Q.hessian.det)) := by
    linear_combination (-(quadraticChar 𝔽 (res (∏ i, a i)))) * h2' +
      quadraticChar 𝔽 (res 2) * e
  simp only [charNF, map_mul, map_pow, map_neg, map_one, map_ofNat (NF.ι v)]
  rw [hA]

/-- The cast of $\chi_\mathfrak p$ of a unit is $\pm 1$. -/
theorem quadraticChar_res_eq {z : v.adicCompletionIntegers F} (hz : ¬ NF.π v ∣ z) :
    quadraticChar 𝔽 (res z) = 1 ∨ quadraticChar 𝔽 (res z) = -1 :=
  quadraticChar_dichotomy fun h => hz ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) z).1 h)

theorem two_le_natAbsNorm : 2 ≤ Ideal.absNorm v.asIdeal := two_le_normP v

/-- **$C'_\mathfrak p(T')$ at good primes, $n \ge 4$ even, over $F$** (Table 2, p. 370; (5.12) corrected): with
$X = N\mathfrak p^{(n-2)/2}$, for $T' \notin \mathfrak p^2$, $C'_\mathfrak p(T') = X/(X+1)$ if $\Phi_n(\mathfrak p) =
\chi_\mathfrak p((-1)^{n/2}\det H) = -1$ and $T' \notin \mathfrak p$, and $C'_\mathfrak p(T') = 1$ otherwise. -/
theorem localConstC'NF_good_even {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (heven : Even n)
    (hG : IsGoodPrimeNF Q v) (hsh : GoodPrimeShape Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if charNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1 := by
  obtain ⟨a, ha, hc, u, hu, hprod⟩ := hsh
  have h2 := not_π_dvd_two hG.1
  have hπT2 : ¬ NF.π v ^ 2 ∣ NF.ι v T := by rw [NF.π_pow_dvd_ι_iff]; exact hT2
  rw [localConstC'NF_eq_diag v hc]
  by_cases hT : T ∈ v.asIdeal
  · rw [ite_eq_right (fun h => h.2 hT)]
    exact DVR.localConstC'_diag_ord_one a _ (NF.irreducible_π v) h2 ha (by omega) _
      ((NF.π_dvd_ι_iff v T).2 hT) hπT2
  · have hπT : ¬ NF.π v ∣ NF.ι v T := by rw [NF.π_dvd_ι_iff]; exact hT
    have hC := DVR.localConstC'_diag_even_unit a _ (NF.irreducible_π v) h2 ha hn heven _ hπT
    rw [NF.q_completion] at hC
    have hχ := charNF_shape_even v heven hG.1 hu hprod (n / 2)
    rcases quadraticChar_res_eq v (DVR.not_dvd_sign_prod a (NF.irreducible_π v) ha (n / 2)) with h | h
    · rw [hC.1 h, ite_eq_right]; rintro ⟨hc', -⟩; rw [← hχ, h] at hc'; exact absurd hc' (by decide)
    · rw [hC.2 h, ite_eq_left ⟨by rw [← hχ, h], hT⟩]

/-- **$C'_\mathfrak p(T')$ at good primes, $n \ge 3$ odd, over $F$** (Table 2, p. 370; (5.12) corrected): for
$T' \notin \mathfrak p^2$, $C'_\mathfrak p(T') = \frac{1 - N\mathfrak p^{-(n-1)/2}}{1 - N\mathfrak p^{-(n-2)}}$ if $T' \notin \mathfrak p$ and
$\Phi_n(\mathfrak p) = \chi_\mathfrak p((-1)^{(n-1)/2}\,2\det H\,T') = 1$, and $C'_\mathfrak p(T') = 1$ otherwise. -/
theorem localConstC'NF_good_odd {Q : QuadForm (𝓞 F) n} (hn : 3 ≤ n) (hodd : Odd n)
    (hG : IsGoodPrimeNF Q v) (hsh : GoodPrimeShape Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if T ∉ v.asIdeal ∧ charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1 then
        (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) else 1 := by
  obtain ⟨a, ha, hc, u, hu, hprod⟩ := hsh
  have h2 := not_π_dvd_two hG.1
  have hπT2 : ¬ NF.π v ^ 2 ∣ NF.ι v T := by rw [NF.π_pow_dvd_ι_iff]; exact hT2
  rw [localConstC'NF_eq_diag v hc]
  by_cases hT : T ∈ v.asIdeal
  · rw [ite_eq_right (fun h => h.1 hT)]
    exact DVR.localConstC'_diag_ord_one a _ (NF.irreducible_π v) h2 ha hn _
      ((NF.π_dvd_ι_iff v T).2 hT) hπT2
  · have hπT : ¬ NF.π v ∣ NF.ι v T := by rw [NF.π_dvd_ι_iff]; exact hT
    have hC := DVR.localConstC'_diag_odd_unit a _ (NF.irreducible_π v) h2 ha hn hodd _ hπT
    rw [NF.q_completion] at hC
    have hχ := charNF_shape_odd v hodd hG.1 hu hprod ((n - 1) / 2) T
    rcases quadraticChar_res_eq v (DVR.not_dvd_sign_prod_mul a (NF.irreducible_π v) ha _ _ hπT) with
      h | h
    · rw [(hC.2 h).1, (hC.2 h).2, ite_eq_left ⟨hT, by rw [← hχ, h]⟩]
    · rw [hC.1 h, ite_eq_right]; rintro ⟨-, hc'⟩; rw [← hχ, h] at hc'; exact absurd hc' (by decide)

end Good

/-! ### Theorem 5.7(b), (c) over $F$ in ratio form -/

/-- Positivity of $X/(X+1)$. -/
theorem div_add_one_pos' {X : ℝ} (hX : 0 < X) : 0 < X / (X + 1) := by positivity

/-- **Theorem 5.7(c), $n \ge 4$ even (and (b) for $n = 4$), ratio form, over $F$** (Hanke 2004, p. 373; proof
pp. 374–375). Let $F$ be totally real, $Q$ totally positive definite and nondegenerate in $n \ge 4$ (even) variables
with the good-prime shape at every good $\mathfrak p$, $T' \ne 0$ totally nonnegative, $x \ne 0$, $S \supseteq
\{\mathfrak p \mid x\}$ finite, $T'$ $\mathfrak p$-stable at every $\mathfrak p \in S$ and $T' \notin \mathfrak p^2$ at the good
$\mathfrak p \in S$. With $X_\mathfrak p = N\mathfrak p^{(n-2)/2}$ and $\Phi_n(\mathfrak p) = \chi_\mathfrak p((-1)^{n/2}\det H)$,
$$a_E(T'x^2) \;\ge\; a_E(T')\,N\big((x)_{\mathrm{Iso}}\big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \in S\ \mathrm{good},\ \mathfrak p \nmid T'\\ \Phi_n(\mathfrak p) = -1}}\frac{X_\mathfrak p}{X_\mathfrak p + 1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even, over F)"]
theorem thm_5_7_c_even_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal),
          (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) ≤
      aENF Q (T * x ^ 2) := by
  have h := aEWithNF_mul_sq_ge Q hQ hQnd (by omega) hT0 hT hx hS hst (IsGoodPrimeNF Q)
    (fun v => if charNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1)
    (fun v hv hG => by
      rw [localConstC'NF_good_even v hn heven hG (hshape v hG) (hT2 v hv hG)]
      refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < (N𝔭 v) ^ ((n - 2) / 2) := pow_pos (by linarith [two_le_normP_real v]) _
      split_ifs <;> positivity)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))
  rwa [← Finset.prod_filter] at h

/-- **Theorem 5.7(b) over $F$, ratio form** (Hanke 2004, p. 373; proof p. 375), $n = 4$: with
$\chi(\mathfrak p) = \chi_\mathfrak p(\det H)$ (the character of $F(\sqrt{D})/F$ at good $\mathfrak p$), under the hypotheses of
`thm_5_7_c_even_NF`,
$$a_E(T'x^2) \;\ge\; a_E(T')\,N\big((x)_{\mathrm{Iso}}\big)^2\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \in S\ \mathrm{good},\ \mathfrak p \nmid T'\\ \chi(\mathfrak p) = -1}}\Big(1 + \frac1{N\mathfrak p}\Big)^{-1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form, over F)"]
theorem thm_5_7_b_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) := by
  have h := thm_5_7_c_even_NF Q hQ hQnd le_rfl (by decide) hshape hT0 hT hx hS hst hT2
  simp only [show 4 / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, show 4 - 2 = 2 from rfl,
    pow_one, neg_one_sq, one_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (0 : ℝ) < N𝔭 v := by linarith [two_le_normP_real v]
  field_simp

/-- **Theorem 5.7(c), $n \ge 5$ odd, ratio form, over $F$** (Hanke 2004, p. 373; proof pp. 375–376). Under the
hypotheses of `thm_5_7_c_even_NF` with $n$ odd, and $\Phi_n(\mathfrak p) = \chi_\mathfrak p((-1)^{(n-1)/2}\,2\det H\,T')$,
$$a_E(T'x^2) \;\ge\; a_E(T')\,N\big((x)_{\mathrm{Iso}}\big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \in S\ \mathrm{good},\ \mathfrak p \nmid T'\\ \Phi_n(\mathfrak p) = 1}}\frac{1 - N\mathfrak p^{-(n-1)/2}}{1 - N\mathfrak p^{-(n-2)}}.$$ -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (ratio form, n odd, over F)"]
theorem thm_5_7_c_odd_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (hodd : Odd n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter (fun v => T ∉ v.asIdeal ∧
            charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1),
          (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) ≤
      aENF Q (T * x ^ 2) := by
  have h := aEWithNF_mul_sq_ge Q hQ hQnd (by omega) hT0 hT hx hS hst (IsGoodPrimeNF Q)
    (fun v => if T ∉ v.asIdeal ∧
        charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) = 1 then
        (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) else 1)
    (fun v hv hG => by
      rw [localConstC'NF_good_odd v (by omega) hodd hG (hshape v hG) (hT2 v hv hG)]
      refine ⟨?_, le_rfl⟩
      have h1 : (1 : ℝ) < N𝔭 v := by linarith [two_le_normP_real v]
      have h2 : 1 / (N𝔭 v) ^ ((n - 1) / 2) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ h1 (by omega)
      have h3 : 1 / (N𝔭 v) ^ (n - 2) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ h1 (by omega)
      split_ifs
      · exact div_pos (by linarith) (by linarith)
      · exact one_pos)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))
  rwa [← Finset.prod_filter] at h

/-! ### The global factors: lower bounds for $a_E(T')$ -/

/-- **The bad primes over $F$**: $\{\mathfrak p : \mathfrak p \mid 2\det H\}$ (`mem_badPrimesNF`: exactly the non-good ones). -/
def badPrimesNF (Q : QuadForm (𝓞 F) n) : Finset (HeightOneSpectrum (𝓞 F)) :=
  primesDividing (2 * Q.hessian.det)

theorem mem_badPrimesNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ badPrimesNF Q ↔ ¬ IsGoodPrimeNF Q v := by
  rw [badPrimesNF, mem_primesDividing (mul_ne_zero two_ne_zero hQ), IsGoodPrimeNF,
    v.isPrime.mul_mem_iff_mem_or_mem]
  tauto

/-- $1 - N\mathfrak p^{-2} > 0$. -/
theorem one_sub_normP_rpow_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < 1 - (N𝔭 v) ^ (-(2 : ℝ)) := by
  have h2 := two_le_normP_real v
  rw [Real.rpow_neg (by linarith), Real.rpow_two, sub_pos]
  exact inv_lt_one_of_one_lt₀ (by nlinarith)

/-- **The Euler-product lower bound engine over $F$.** Let $Q$ be nondegenerate, $n \ge 4$, with the good-prime shape,
$T' \ne 0$, $A$ a finite set of primes, and $g \ge 0$ off $A$ with $g = 1$ off a finite set $A'$, such that
$(1 - N\mathfrak p^{-2})g(\mathfrak p) \le \beta_\mathfrak p(T')$ for $\mathfrak p \notin A$. Then
$$(6/\pi^2)^d\prod_{\mathfrak p \in A}\beta_\mathfrak p(T')\prod_{\mathfrak p \in A' \setminus A}g(\mathfrak p) \;\le\; \prod_\mathfrak p\beta_\mathfrak p(T').$$ -/
theorem le_eulerProductNF {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (A A' : Finset (HeightOneSpectrum (𝓞 F))) (g : HeightOneSpectrum (𝓞 F) → ℝ)
    (hg0 : ∀ v ∉ A, 0 ≤ g v) (hg1 : ∀ v ∉ A', g v = 1)
    (hge : ∀ v ∉ A, (1 - (N𝔭 v) ^ (-(2 : ℝ))) * g v ≤ NF.localDensity v Q T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * (∏ v ∈ A, NF.localDensity v Q T) *
        ∏ v ∈ A' \ A, g v ≤ eulerProductNF Q T := by
  have hlim : Tendsto (eulerPartialProdNF (eulerFactorNF Q T)) atTop (𝓝 (eulerProductNF Q T)) :=
    isEulerProductValueNF_eulerProductNF hQ hn hshape hT0
  refine ge_of_tendsto hlim ?_
  filter_upwards [(tendsto_primesNormLe (F := F)).eventually (eventually_ge_atTop (A ∪ A'))] with X hsub
  set P := primesNormLe F X
  have hAP : A ⊆ P := fun v hv => hsub (Finset.mem_union_left _ hv)
  have hfA : 0 ≤ ∏ v ∈ A, NF.localDensity v Q T :=
    Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQ hT0
  have hgA : 0 ≤ ∏ v ∈ A' \ A, g v :=
    Finset.prod_nonneg fun v hv => hg0 v (Finset.mem_sdiff.1 hv).2
  have hsplit : eulerPartialProdNF (eulerFactorNF Q T) X =
      (∏ v ∈ A, NF.localDensity v Q T) * ∏ v ∈ P \ A, NF.localDensity v Q T := by
    rw [eulerPartialProdNF, ← Finset.prod_sdiff hAP, mul_comm]
    simp only [eulerFactorNF]
  have hg : ∏ v ∈ P \ A, g v = ∏ v ∈ A' \ A, g v := by
    refine (Finset.prod_subset (fun v hv => ?_) fun v hv hv' => ?_).symm
    · rw [Finset.mem_sdiff] at hv ⊢
      exact ⟨hsub (Finset.mem_union_right _ hv.1), hv.2⟩
    · rw [Finset.mem_sdiff] at hv hv'
      exact hg1 v fun h => hv' ⟨h, hv.2⟩
  have hrest : (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * ∏ v ∈ A' \ A, g v ≤
      ∏ v ∈ P \ A, NF.localDensity v Q T := by
    calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * ∏ v ∈ A' \ A, g v
        ≤ (∏ v ∈ P \ A, (1 - (N𝔭 v) ^ (-(2 : ℝ)))) * ∏ v ∈ P \ A, g v := by
          rw [hg]; exact mul_le_mul_of_nonneg_right (six_div_pi_sq_pow_le_prod _) hgA
      _ = ∏ v ∈ P \ A, (1 - (N𝔭 v) ^ (-(2 : ℝ))) * g v := (Finset.prod_mul_distrib).symm
      _ ≤ _ := Finset.prod_le_prod₀
          (fun v hv => mul_nonneg (one_sub_normP_rpow_pos v).le (hg0 v (Finset.mem_sdiff.1 hv).2))
          fun v hv => hge v (Finset.mem_sdiff.1 hv).2
  rw [hsplit]
  calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * (∏ v ∈ A, NF.localDensity v Q T) *
        ∏ v ∈ A' \ A, g v
      = (∏ v ∈ A, NF.localDensity v Q T) *
          ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * ∏ v ∈ A' \ A, g v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrest hfA

/-- **The generic part of $\prod_\mathfrak p\beta_\mathfrak p(T')$ over $F$, $n \ge 4$** (Hanke 2004, proof of Thm 5.7, pp. 374–375,
with $1/L_F(\cdot) \ge 1/\zeta_F(2) \ge (6/\pi^2)^d$): with $B$ the bad primes and $\mathrm{supp}(T') = \{\mathfrak p \mid T'\}$,
$$a_E(T') \;\ge\; (6/\pi^2)^d\,\beta_\infty(T')\prod_{\mathfrak p \in B \cup \mathrm{supp}(T')}\beta_\mathfrak p(T').$$
($\beta_\mathfrak p(T') \ge 1 - N\mathfrak p^{-2}$ at good $\mathfrak p \nmid T'$, from Table 1.) -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), pp. 374–375 (over F, ζ_F(2) bound)"]
theorem aENF_ge (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate) (hn : 4 ≤ n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T ≤
      aENF Q T := by
  have h := le_eulerProductNF hQnd hn hshape hT0 (badPrimesNF Q ∪ primesDividing T) ∅ (fun _ => 1)
    (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun v hv => by
      rw [Finset.mem_union, not_or, mem_badPrimesNF hQnd, not_not, mem_primesDividing hT0] at hv
      rw [mul_one]
      have := abs_localDensityNF_sub_one_le v hn hv.1 (hshape v hv.1) hv.2
      rw [one_mul] at this
      linarith [(abs_le.1 this).1])
  simp only [Finset.empty_sdiff, Finset.prod_empty, mul_one] at h
  rw [aENF, aEWithNF]
  calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T
      = betaInfNF Q (T : F) * ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F *
        ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (betaInfNF_nonneg hQ hT)

/-- **Lower bound for $\beta_\mathfrak p(m)$ at a good prime, $n = 4$, over $F$** (Hanke 2004, Table 1, p. 363, and the proof
of Thm 5.7(b), p. 374): with $\chi(\mathfrak p) = \chi_\mathfrak p(\det H)$,
$\beta_\mathfrak p(m) \ge (1 - N\mathfrak p^{-2})\cdot\frac{N\mathfrak p - 1}{N\mathfrak p + 1}$ if $\chi(\mathfrak p) = -1$ and $m \in \mathfrak p$, and
$\ge 1 - N\mathfrak p^{-2}$ otherwise. From `DVR.localDensity_ge_even`. -/
theorem localDensityNF_good_four_ge {Q : QuadForm (𝓞 F) 4} (v : HeightOneSpectrum (𝓞 F))
    (hG : IsGoodPrimeNF Q v) (hsh : GoodPrimeShape Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    (1 - (N𝔭 v) ^ (-(2 : ℝ))) *
        (if charNF v Q.hessian.det = -1 ∧ m ∈ v.asIdeal then ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1) ≤
      NF.localDensity v Q m := by
  obtain ⟨a, ha, hc, u, hu, hprod⟩ := hsh
  have h2 := not_π_dvd_two hG.1
  have hge := DVR.localDensity_ge_even a _ (NF.irreducible_π v) h2 ha le_rfl (by decide) _
    (NF.ι_ne_zero v hm)
  have hχ := charNF_shape_even v (by decide : Even 4) hG.1 hu hprod (4 / 2)
  simp only [show (4 : ℕ) / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, pow_one, neg_one_sq,
    one_mul, NF.q_completion, NF.π_dvd_ι_iff] at hge hχ
  rw [hχ] at hge
  rw [localDensityNF_eq_diag v hc]
  refine le_trans ?_ hge
  have hN := two_le_normP_real v
  have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  have hif : 0 ≤ (if charNF v Q.hessian.det = -1 ∧ m ∈ v.asIdeal then
      ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1) := by
    split_ifs
    · exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  refine mul_le_mul_of_nonneg_right ?_ hif
  rw [hr]
  have hχ1 : ((charNF v Q.hessian.det : ℤ) : ℝ) ≤ 1 := (abs_le.1 (abs_quadraticChar_le _)).2
  have hpos : (0 : ℝ) < (N𝔭 v) ^ 2 := by positivity
  have : ((charNF v Q.hessian.det : ℤ) : ℝ) / (N𝔭 v) ^ 2 ≤ 1 / (N𝔭 v) ^ 2 :=
    div_le_div_of_nonneg_right hχ1 hpos.le
  linarith

/-- **The global lower bound for $a_E(T')$, $n = 4$, over $F$** (Hanke 2004, Thm 5.7(b), p. 373; proof pp. 374–375, with
$1/L_F(2,\chi) \ge 1/\zeta_F(2) \ge (6/\pi^2)^d$): for $Q$ totally positive definite quaternary with the good-prime shape,
$T' \ne 0$ totally nonnegative,
$$a_E(T') \;\ge\; (6/\pi^2)^d\,\beta_\infty(T')\prod_{\mathfrak p \in B}\beta_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \mid T'\ \mathrm{good}\\ \chi(\mathfrak p) = -1}}\frac{N\mathfrak p - 1}{N\mathfrak p + 1}, \qquad \chi(\mathfrak p) = \chi_\mathfrak p(\det H).$$
The number-field form of `aE_four_ge` (there $\beta_\infty(T') = \pi^2D^{-1/2}T'$ and $d = 1$). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373; proof pp. 374–375 (over F)"]
theorem aENF_four_ge (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1) ≤
      aENF Q T := by
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if charNF v Q.hessian.det = -1 ∧ T ∈ v.asIdeal then ((N𝔭 v) - 1) / ((N𝔭 v) + 1) else 1 with hg
  have h := le_eulerProductNF hQnd le_rfl hshape hT0 (badPrimesNF Q) (primesDividing T) g
    (fun v _ => by
      simp only [hg]; split_ifs
      · have := two_le_normP_real v; exact div_nonneg (by linarith) (by linarith)
      · exact zero_le_one)
    (fun v hv => by
      simp only [hg]; rw [ite_eq_right]; rintro ⟨-, h⟩; exact hv ((mem_primesDividing hT0).2 h))
    (fun v hv => by
      rw [mem_badPrimesNF hQnd, not_not] at hv
      exact localDensityNF_good_four_ge v hv (hshape v hv) hT0)
  have hgp : ∏ v ∈ primesDividing T \ badPrimesNF Q, g v =
      ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
        ((N𝔭 v) - 1) / ((N𝔭 v) + 1) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hTv : T ∈ v.asIdeal := (mem_primesDividing hT0).1 (Finset.mem_sdiff.1 hv).1
    simp only [hg, hTv, and_true]
  rw [hgp] at h
  rw [aENF, aEWithNF]
  calc (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)
      = betaInfNF Q (T : F) * ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (betaInfNF_nonneg hQ hT)

/-- **Theorem 5.7(b) over a totally real field, global form** (Hanke 2004, p. 373; display on p. 375): for $Q$ totally
positive definite quaternary with the good-prime shape, under the hypotheses of `thm_5_7_b_NF`,
$$a_E(T'x^2) \;\ge\; \hat\Lambda_4(T')\,N\big((x)_{\mathrm{Iso}}\big)^2
  \prod_{\substack{\mathfrak p \mid T'\ \mathrm{good}\\ \chi(\mathfrak p) = -1}}\frac{N\mathfrak p - 1}{N\mathfrak p + 1}
  \prod_{\substack{\mathfrak p \in S\ \mathrm{good},\ \mathfrak p \nmid T'\\ \chi(\mathfrak p) = -1}}\Big(1 + \frac1{N\mathfrak p}\Big)^{-1},$$
$$\hat\Lambda_4(T') = (6/\pi^2)^d\,\beta_\infty(T')\prod_{\mathfrak p \in B}\beta_\mathfrak p(T')
  \prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T').$$
Since $(1 + 1/q)^{-1} \ge \frac{q-1}{q+1}$, this gives the printed $\prod_{\mathfrak p \mid m,\ \mathfrak p \nmid N,\ \chi = -1}\frac{q-1}{q+1}$
(here with $\mathfrak p \nmid 2\det H$ in place of $\mathfrak p \nmid N$, i.e. dyadic primes bad). The minimum over
$T' \in B_{\mathbb T}$ is not formalized. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, over F)"]
theorem thm_5_7_b_global_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
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
      aENF Q (T * x ^ 2) := by
  have hr := thm_5_7_b_NF Q hQ hQnd hshape hT0 hT hx hS hst hT2
  have hg := aENF_four_ge Q hQ hQnd hshape hT0 hT
  have hC : 0 ≤ ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
      NF.localConstC' v Q T := Finset.prod_nonneg fun v _ => localConstC'NF_nonneg v Q hQnd (by norm_num) hT0
  have hN : 0 ≤ (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 := by positivity
  have hI : 0 ≤ ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
      (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by positivity
  calc _ = ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by ring
    _ ≤ aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by
          gcongr
    _ ≤ _ := hr

/-- $1 - N\mathfrak p^{-2} \le C'_\mathfrak p(T')$ at good primes for $n \ge 5$ ($T' \notin \mathfrak p^2$): by Table 2,
$C'_\mathfrak p \in \{1, \frac{X}{X+1}\}$ ($n$ even, $X = N\mathfrak p^{(n-2)/2} \ge N\mathfrak p^2$) or
$\{1, \frac{1 - N\mathfrak p^{-(n-1)/2}}{1 - N\mathfrak p^{-(n-2)}}\}$ ($n$ odd). -/
theorem one_sub_le_localConstC'NF_good {Q : QuadForm (𝓞 F) n} (hn : 5 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) (hG : IsGoodPrimeNF Q v) (hsh : GoodPrimeShape Q v) {T : 𝓞 F}
    (hT2 : T ∉ v.asIdeal ^ 2) : 1 - (N𝔭 v) ^ (-(2 : ℝ)) ≤ NF.localConstC' v Q T := by
  have hN := two_le_normP_real v
  have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  have h0 : 0 ≤ 1 / (N𝔭 v) ^ 2 := by positivity
  have hle : ∀ k : ℕ, 2 ≤ k → 1 / (N𝔭 v) ^ k ≤ 1 / (N𝔭 v) ^ 2 := fun k hk =>
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) hk)
  rw [hr]
  rcases Nat.even_or_odd n with he | ho
  · rw [localConstC'NF_good_even v (by omega) he hG hsh hT2]
    split_ifs
    · set X := (N𝔭 v) ^ ((n - 2) / 2)
      have hX : 1 / X ≤ 1 / (N𝔭 v) ^ 2 := hle _ (by obtain ⟨j, rfl⟩ := he; omega)
      have hX0 : 0 < X := by positivity
      have : 1 - 1 / X ≤ X / (X + 1) := by
        rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
          le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · linarith
  · rw [localConstC'NF_good_odd v (by omega) ho hG hsh hT2]
    split_ifs
    · have ha : 1 / (N𝔭 v) ^ ((n - 1) / 2) ≤ 1 / (N𝔭 v) ^ 2 := hle _ (by obtain ⟨j, rfl⟩ := ho; omega)
      have hb0 : 0 < 1 / (N𝔭 v) ^ (n - 2) := by positivity
      have hb1 : 1 / (N𝔭 v) ^ (n - 2) < 1 := by
        rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by linarith) (by omega)
      have hnum : 0 ≤ 1 - 1 / (N𝔭 v) ^ ((n - 1) / 2) := by
        have : 1 / (N𝔭 v) ^ ((n - 1) / 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
        linarith
      have : 1 - 1 / (N𝔭 v) ^ ((n - 1) / 2) ≤
          (1 - 1 / (N𝔭 v) ^ ((n - 1) / 2)) / (1 - 1 / (N𝔭 v) ^ (n - 2)) :=
        le_div_self hnum (by linarith) (by linarith)
      linarith
    · linarith

/-- **Theorem 5.7(c) over a totally real field, global form, $n \ge 5$** (Hanke 2004, p. 373; proof pp. 374–376): for $Q$
totally positive definite with the good-prime shape, under the hypotheses of `thm_5_7_c_even_NF`,
$$a_E(T'x^2) \;\ge\; (6/\pi^2)^{2d}\,\beta_\infty(T')\prod_{\mathfrak p \in B \cup \mathrm{supp}(T')}\beta_\mathfrak p(T')
  \cdot N\big((x)_{\mathrm{Iso}}\big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T').$$
One factor $(6/\pi^2)^d$ bounds the generic part of $\prod_\mathfrak p\beta_\mathfrak p(T')$ (`aENF_ge`), the other the good factors of
the ratio ($C'_\mathfrak p \ge 1 - N\mathfrak p^{-2}$, `one_sub_le_localConstC'NF_good`); the paper's sharper
$\zeta_F(n-2)/(L_F\zeta_F(\cdot)^2)$ and $L_F((n-1)/2,\Phi_n)\zeta_F(n-2)/(\zeta_F(n-1)\zeta_F((n-1)/2))$ are bounded below by
these. With $\beta_\infty(T') = c_\infty N(T')^{(n-2)/2}$ (`betaInfNF_eq_norm`) the right side is
$c\,N(T')^{(n-2)/2}N((x)_{\mathrm{Iso}})^{n-2}$; for $n \ge 5$ every $\mathfrak p$ is isotropic (not formalized), so this is
$c\,N(m)^{(n-2)/2}$ as printed. The minimum over $T' \in B_{\mathbb T}$ is not formalized. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (global, n ≥ 5, over F)"]
theorem thm_5_7_c_global_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 5 ≤ n) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v)
    {T : 𝓞 F} (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T ≤
      aENF Q (T * x ^ 2) := by
  have hr := aEWithNF_mul_sq_ge Q hQ hQnd (by omega) hT0 hT hx hS hst (IsGoodPrimeNF Q)
    (fun v => 1 - (N𝔭 v) ^ (-(2 : ℝ)))
    (fun v hv hG => ⟨one_sub_normP_rpow_pos v,
      one_sub_le_localConstC'NF_good hn v hG (hshape v hG) (hT2 v hv hG)⟩)
    (isEulerProductValueNF_eulerProductNF hQnd (by omega) hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd (by omega) hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))
  have hg := aENF_ge Q hQ hQnd (by omega) hshape hT0 hT
  have hz := six_div_pi_sq_pow_le_prod (F := F) (S.filter (IsGoodPrimeNF Q))
  have hC : 0 ≤ ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
      NF.localConstC' v Q T :=
    Finset.prod_nonneg fun v _ => localConstC'NF_nonneg v Q hQnd (by omega) hT0
  have hN : 0 ≤ (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) := by positivity
  have hA : 0 ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
      ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T :=
    mul_nonneg (mul_nonneg (by positivity) (betaInfNF_nonneg hQ hT))
      (Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQnd hT0)
  have hz0 : (0 : ℝ) ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F := by positivity
  have hE : (0 : ℝ) ≤ aENF Q T := hA.trans hg
  calc _ = ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) *
        ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) * (6 / Real.pi ^ 2) ^ Module.finrank ℚ F := by
        rw [pow_mul']; ring
    _ ≤ aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (IsGoodPrimeNF Q), (1 - (N𝔭 v) ^ (-(2 : ℝ))) := by
          gcongr
    _ ≤ _ := hr

/-- **$\beta_\infty(T')$ in terms of the norm** ($F$ totally real, $T'$ nonnegative at every real place):
$\beta_\infty(T') = c_\infty(Q)\,N(T')^{(n-2)/2}$ with $c_\infty(Q) = \prod_w\frac{n\,\omega_n\,D_w^{-1/2}}{2}$ (Hanke 2004, (5.5),
p. 369, as used in the proof of Thm 5.7: $\prod_{v \mid \infty}\beta_v(T') = N(T')^{(n-2)/2}\prod_{v \mid \infty}\beta_v(1)$).
*Clarification (candidate):* the paper's $(\frac n2\omega_nD^{-1/2})^{[F:\mathbb{Q}]}$ is
$\prod_w\frac n2\omega_n\sigma_w(D)^{-1/2} = (\frac n2\omega_n)^{[F:\mathbb{Q}]}N_{F/\mathbb{Q}}(D)^{-1/2}$ over $F \ne \mathbb{Q}$. -/
theorem betaInfNF_eq_norm [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) {T : F}
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) :
    betaInfNF Q T = (∏ w : RealPlace F, n * unitBallVol n * gramDetNF Q w ^ (-(1 / 2 : ℝ)) / 2) *
      |Algebra.norm ℚ T| ^ (((n : ℝ) - 2) / 2) := by
  rw [betaInfNF, ← prod_realPlace_eq_abs_norm, ← Real.finsetProd_rpow _ _ (fun w _ => by
    rw [← abs_realEmb]; exact abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [betaInfAt, ← abs_realEmb, abs_of_nonneg (hT w)]

/-! ### Theorem 5.7(a), second part: $n = 3$ and $L_F(1, \psi_{T'})$ -/

/-- **The character $\psi_{T'}$ of Thm 5.7(a)** at good primes: $\psi_{T'}(\mathfrak p) = \chi_\mathfrak p((-1)^{(n-1)/2}\,2\det H\,T')$
($= \Phi_n(\mathfrak p)$, and for $n = 3$ the character of $F(\sqrt{-2\det H\,T'})/F$; $0$ at $\mathfrak p \mid T'$), and $0$ at the
bad primes. Hanke's $\psi_t$ ($t$ the squarefree part of $m$) differs from $\psi_{T'}$ at finitely many primes. -/
def psiNF (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsGoodPrimeNF Q v then (charNF v ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) : ℝ) else 0

/-- **The local factor at a good prime, $n = 3$** (Table 1): for $T' \notin \mathfrak p^2$,
$\beta_\mathfrak p(T') = (1 - N\mathfrak p^{-2})\,(1 - \psi_{T'}(\mathfrak p)N\mathfrak p^{-1})^{-1}$ (for $\mathfrak p \nmid T'$ this is
$1 + \psi_{T'}(\mathfrak p)/N\mathfrak p$; for $\mathfrak p \parallel T'$ it is $1 - N\mathfrak p^{-2}$ and $\psi_{T'}(\mathfrak p) = 0$). -/
theorem localDensityNF_good_three_eq {Q : QuadForm (𝓞 F) 3} (v : HeightOneSpectrum (𝓞 F))
    (hG : IsGoodPrimeNF Q v) (hsh : GoodPrimeShape Q v) {T : 𝓞 F} (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localDensity v Q T = (1 - (N𝔭 v) ^ (-(2 : ℝ))) * lFactor (psiNF Q T) 1 v := by
  obtain ⟨a, ha, hc, u, hu, hprod⟩ := hsh
  have h2 := not_π_dvd_two hG.1
  have hN := two_le_normP_real v
  have hr2 : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  have hr1 : ((normP v : ℕ) : ℝ) ^ (-(1 : ℝ)) = 1 / (N𝔭 v) := by
    rw [Real.rpow_neg (by simp only [normP]; linarith), Real.rpow_one, one_div]
  have hπT2 : ¬ NF.π v ^ 2 ∣ NF.ι v T := by rw [NF.π_pow_dvd_ι_iff]; exact hT2
  rw [localDensityNF_eq_diag v hc, lFactor, psiNF, ite_eq_left hG, hr2, hr1]
  by_cases hT : T ∈ v.asIdeal
  · have hπT : NF.π v ∣ NF.ι v T := (NF.π_dvd_ι_iff v T).2 hT
    rw [DVR.localDensity_diag_odd_ord_one a _ (NF.irreducible_π v) h2 ha (by decide) _ hπT hπT2,
      NF.q_completion]
    have h0 : charNF v ((-1) ^ ((3 - 1) / 2) * (2 * Q.hessian.det) * T) = 0 := by
      rw [charNF, quadraticChar_eq_zero_iff, (DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _)]
      rw [map_mul]; exact dvd_mul_of_dvd_right hπT _
    rw [h0]; norm_num
  · have hπT : ¬ NF.π v ∣ NF.ι v T := by rw [NF.π_dvd_ι_iff]; exact hT
    rw [DVR.localDensity_diag_odd_unit a _ (NF.irreducible_π v) h2 ha (by decide) _ hπT,
      NF.q_completion, charNF_shape_odd v (by decide) hG.1 hu hprod _ T]
    have hnot : (-1) ^ ((3 - 1) / 2) * (2 * Q.hessian.det) * T ∉ v.asIdeal := by
      intro h
      rcases v.isPrime.mem_or_mem h with h | h
      · rcases v.isPrime.mem_or_mem h with h | h
        · exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_neg_one.pow _))
        · rcases v.isPrime.mem_or_mem h with h | h
          · exact hG.1 h
          · exact hG.2 h
      · exact hT h
    have hχ := quadraticChar_res_eq v (z := NF.ι v ((-1) ^ ((3 - 1) / 2) * (2 * Q.hessian.det) * T))
      (by rw [NF.π_dvd_ι_iff]; exact hnot)
    simp only [charNF] at *
    have hN0 : (N𝔭 v) ≠ 0 := by linarith
    have hN1 : (N𝔭 v) - 1 ≠ 0 := by linarith
    have hN2 : (N𝔭 v) + 1 ≠ 0 := by linarith
    rcases hχ with h | h <;> rw [h] <;> push_cast
    · rw [show 1 - 1 * (1 / (N𝔭 v)) = ((N𝔭 v) - 1) / (N𝔭 v) by field_simp]
      field_simp; ring
    · rw [show 1 - -1 * (1 / (N𝔭 v)) = ((N𝔭 v) + 1) / (N𝔭 v) by field_simp; ring]
      field_simp; ring

/-- **The Euler product for $n = 3$ over $F$ in terms of $L_F(1, \psi_{T'})$** (the $n = 3$ case of (5.14), Hanke 2004,
pp. 374–375): for $Q$ ternary nondegenerate with the good-prime shape, $T' \ne 0$ with $T' \notin \mathfrak p^2$ at every good
$\mathfrak p$, and $L$ the natural-order value of $L_F(1, \psi_{T'}) = \prod_\mathfrak p(1 - \psi_{T'}(\mathfrak p)N\mathfrak p^{-1})^{-1}$,
$$\prod_\mathfrak p\beta_\mathfrak p(T') = \frac{L_F(1, \psi_{T'})}{\zeta_F(2)}\prod_{\mathfrak p \in B}\frac{\beta_\mathfrak p(T')}{1 - N\mathfrak p^{-2}}$$
in the natural order (in particular the left side converges in that order). -/
@[kb "hanke2004" "(5.14), p. 375 (n = 3, over F)"]
theorem isEulerProductValueNF_three {Q : QuadForm (𝓞 F) 3} (hQnd : Q.Nondegenerate)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT2 : ∀ v, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) {L : ℝ}
    (hL : IsEulerProductValueNF (lFactor (psiNF Q T) 1) L) :
    IsEulerProductValueNF (eulerFactorNF Q T)
      ((∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ)))) *
        (dedekindZetaR F 2)⁻¹ * L) := by
  set h : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if v ∈ badPrimesNF Q then NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ))) else 1 with hh
  have hH : IsEulerProductValueNF h
      (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ)))) := by
    have := isEulerProductValueNF_of_hasProd
      (hasProd_prod_of_ne_finset_one (s := badPrimesNF Q) (f := h) fun v hv => by simp [hh, hv])
    have e : ∏ v ∈ badPrimesNF Q, h v =
        ∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ))) :=
      Finset.prod_congr rfl fun v hv => by simp [hh, hv]
    rwa [e] at this
  have hZ := isEulerProductValueNF_of_hasProd (hasProd_one_sub_rpow (F := F) (s := 2) (by norm_num))
  refine ((hH.mul hZ).mul hL).congr fun X => ?_
  simp only [eulerPartialProdNF, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ badPrimesNF Q
  · have hng : ¬ IsGoodPrimeNF Q v := (mem_badPrimesNF hQnd).1 hv
    have hz := one_sub_normP_rpow_pos v
    simp only [hh, ite_eq_left hv, lFactor, psiNF, ite_eq_right hng, zero_mul, sub_zero, inv_one, mul_one,
      eulerFactorNF]
    rw [div_mul_cancel₀ _ hz.ne']
  · have hg : IsGoodPrimeNF Q v := by rw [mem_badPrimesNF hQnd, not_not] at hv; exact hv
    simp only [hh, ite_eq_right hv, one_mul, eulerFactorNF]
    rw [localDensityNF_good_three_eq v hg (hshape v hg) (hT2 v hg)]

/-- **Theorem 5.7(a), second part, over a totally real field** (Hanke 2004, p. 372), with the effective lower bound for
$L_F(1, \psi)$ kept as a hypothesis, as in the paper. Under the hypotheses of `thm_5_7_a_NF`, with moreover
$T' \notin \mathfrak p^2$ at every good $\mathfrak p$ (the paper's $\mathrm{ord}_\mathfrak p(T') \le 1$ for $\mathfrak p \nmid N$), let $L$ be
the natural-order value of $L_F(1, \psi_{T'})$ and $c \le L$ (the paper: $c = C_\varepsilon N(t)^{-\varepsilon}$). Then
$$\beta_\infty(T'x^2)P_m \;\ge\; \frac{c\,\beta_\infty(T')}{\zeta_F(2)}\prod_{\mathfrak p \in B}\frac{\beta_\mathfrak p(T')}{1 - N\mathfrak p^{-2}}
  \prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T')\cdot N\big((x)_{\mathrm{Iso}}\big),$$
and $\beta_\infty(T') = c_\infty N(T')^{1/2}$ (`betaInfNF_eq_norm`), so the right side is the paper's
$\hat\Lambda_3 N(t)^{1/2-\varepsilon}N((m')_{\mathrm{Iso}})$ for this $T'$ ($N(T')^{1/2} = N(t)^{1/2}N(T'/t)^{1/2}$).
*Clarification (candidate):* with $\psi_{T'}$ vanishing at the bad primes the
bad factor is exactly $\beta_\mathfrak p(T')/(1 - N\mathfrak p^{-2})$; the printed $\beta_\mathfrak p(T')/(1+q)$ is valid but weaker.
*Differences:* $\psi_{T'}$ in place of $\psi_t$ (they differ at finitely many primes, changing $L$ by an explicit finite
factor); the minimum over $T' \in B_{\mathbb T}$ is not formalized. -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (second part, over F)"]
theorem thm_5_7_a_second_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
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
      aEWithNF Q (T * x ^ 2) Pm := by
  have hP := isEulerProductValueNF_three hQnd hshape hT2 hL
  have h1 := thm_5_7_a_NF Q hQ hQnd hshape hT0 hT hx hS hst (fun v _ hG => hT2 v hG) hP hPm
  have hB : 0 ≤ ∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ))) :=
    Finset.prod_nonneg fun v _ =>
      div_nonneg (localDensityNF_nonneg v Q hQnd hT0) (one_sub_normP_rpow_pos v).le
  have hZ : 0 ≤ (dedekindZetaR F 2)⁻¹ :=
    inv_nonneg.2 (zero_le_one.trans (one_le_dedekindZetaR (by norm_num)))
  have hβ := betaInfNF_nonneg hQ hT
  have hC : 0 ≤ ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
      NF.localConstC' v Q T :=
    Finset.prod_nonneg fun v _ => localConstC'NF_nonneg v Q hQnd (by norm_num) hT0
  have hN : 0 ≤ ∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x :=
    Finset.prod_nonneg fun v _ => by positivity
  refine le_trans ?_ h1
  rw [aEWithNF]
  calc _ = betaInfNF Q (T : F) *
        ((∏ v ∈ badPrimesNF Q, NF.localDensity v Q T / (1 - (N𝔭 v) ^ (-(2 : ℝ)))) *
          (dedekindZetaR F 2)⁻¹ * c) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
          NF.localConstC' v Q T) *
        ∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x := by ring
    _ ≤ _ := by gcongr

end QuadFormsKB.Siegel

end
