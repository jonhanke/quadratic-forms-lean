/-
# Theorem 5.7(b), (c) over $F$: dyadic primes $\mathfrak p \nmid N$ are good

**Layer:** number field (continues `NFGlobalLowerBound.lean`, where dyadic $\mathfrak p$ are bad, as $p = 2$ is over $\mathbb{Q}$).

**The symbol.** `quadSymbolNF v x` $= \left(\frac{x}{\mathfrak p}\right)$: $0$ for $x \in \mathfrak p$, else $+1$ iff $x$ is a square in $F_\mathfrak p$.
At $\mathfrak p \nmid 2$ it equals the residue symbol `charNF` (`quadSymbolNF_eq_charNF`, Hensel), so it extends `charNF`
to dyadic primes. At dyadic $\mathfrak p \nmid N$ (even unimodular, $n = 2r$) the Arf sign of $Q \bmod \mathfrak p$ is
$\left(\frac{\Delta}{\mathfrak p}\right)$, $\Delta = (-1)^{n/2}\det H$ (`arfSignQ_eq_quadSymbolNF`, from `DyadicArf.lean`); $F(\sqrt\Delta)/F$ is
unramified at $\mathfrak p$, so this is the Frobenius: $\varepsilon = +1 \iff \mathfrak p$ splits.

**Results** (new names; the statements of `NFGlobalLowerBound.lean` are unchanged): $C'_\mathfrak p(T')$ at every $\mathfrak p \nmid N$
for $n \ge 4$ even (`localConstC'NF_level_even`), and Thm 5.7(b), (c) for even $n$ in ratio form with **bad set
$\{\mathfrak p \mid N\}$** (`thm_5_7_c_even_level_NF`, `thm_5_7_b_level_NF`). For odd $n$ every dyadic $\mathfrak p$ divides $N$
(`not_notDvdLevel_of_odd`), so the bad set $\{\mathfrak p \mid 2\det H\}$ of `thm_5_7_c_odd_NF` already equals $\{\mathfrak p \mid N\}$. The
hypothesis `hshape` is kept; composing with the hypothesis-free `goodPrimeShape_of_isGoodPrimeNF`
(`Siegel/NFGoodPrime.lean`) is left for later.

**Over $\mathbb{Q}$:** $2 \nmid N$ makes $Q \otimes \mathbb{Z}_2$ even unimodular (`isLocalLevel_two_of_odd_level`), and then the Arf sign
is $\chi_8(\Delta) = \left(\frac{\Delta}{2}\right)$ (`arfSignQ_two_eq_chi8`), the theta character at $2$
(`arfSignQ_two_eq_chiCharLevel`, via `chiCharLevel_two`).
-/
import QuadFormsKB.Siegel.NFGlobalLowerBound
import QuadFormsKB.LocalDensity.NFLocalGeneral
import QuadFormsKB.LocalDensity.DyadicArf
import QuadFormsKB.Siegel.ThetaCharacter

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-! ### The splitting symbol at every prime -/

/-- **The quadratic splitting symbol $\left(\frac{x}{\mathfrak p}\right)$ at every finite prime** ($x \in \mathcal O_F$): $0$ if
$x \in \mathfrak p$, $+1$ if $x$ is a square in $F_\mathfrak p$ (so $\mathfrak p$ splits in $F(\sqrt x)/F$), $-1$ otherwise. At
$\mathfrak p \nmid 2$ it is the residue symbol `charNF` (`quadSymbolNF_eq_charNF`); at dyadic $\mathfrak p$ with
$F(\sqrt x)/F$ unramified at $\mathfrak p$ ($x \equiv \square\,(1 - 4T)$, e.g. $x = (-1)^{n/2}\det H$ at $\mathfrak p \nmid N$) it is the Frobenius
$\pm 1$ of $\mathfrak p$; for ramified $x$ the value $-1$ carries no Frobenius meaning and is not used. -/
@[kb "hanke2004" "χ(𝔭) of F(√D)/F, p. 373 (at every prime)"]
def quadSymbolNF (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) : ℤ :=
  if x ∈ v.asIdeal then 0
  else if IsSquare (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (NF.ι v x)) then 1 else -1

section Local

variable (v : HeightOneSpectrum (𝓞 F))

/-- **At $\mathfrak p \nmid 2$ the splitting symbol is the residue symbol** (Hensel: a unit of $\mathfrak o_\mathfrak p$ is a square
iff its residue is). -/
theorem quadSymbolNF_eq_charNF (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (x : 𝓞 F) :
    quadSymbolNF v x = charNF v x := by
  unfold quadSymbolNF charNF
  by_cases hx : x ∈ v.asIdeal
  · rw [ite_eq_left hx]
    have : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v x) = 0 :=
      (DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).2 ((NF.π_dvd_ι_iff v x).2 hx)
    rw [this, quadraticChar_zero]
  · rw [ite_eq_right hx, DVR.isSquare_algebraMap_iff,
      DVR.isSquare_iff_quadraticChar_residue (NF.irreducible_π v) (not_π_dvd_two h2)
        (by rwa [NF.π_dvd_ι_iff])]
    have hne : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v x) ≠ 0 := fun h =>
      hx ((NF.π_dvd_ι_iff v x).1 ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).1 h))
    rcases quadraticChar_dichotomy hne with h | h <;> simp [h]

/-- At $\mathfrak p \nmid N$ the Hessian determinant is a $\mathfrak p$-unit (any $\mathfrak p$). -/
theorem det_not_mem_of_notDvdLevel {Q : QuadForm (𝓞 F) n} (hN : NF.NotDvdLevel v Q) :
    Q.hessian.det ∉ v.asIdeal := by
  intro h
  have hu := DVR.isUnit_det_of_isLocalLevel_zero hN
  rw [NF.det_hessian_Qp] at hu
  exact (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit ((NF.π_dvd_ι_iff v _).2 h) hu)

/-- **The dyadic Arf sign is the Frobenius of $\mathfrak p$ in $F(\sqrt\Delta)/F$** ($\mathfrak p \mid 2$, $\mathfrak p \nmid N$, $n = 2r \ge 2$,
$\Delta = (-1)^{n/2}\det H$): $\varepsilon(Q \bmod \mathfrak p) = \left(\frac{\Delta}{\mathfrak p}\right)$, i.e. $\varepsilon = +1 \iff \Delta$ is a square
in $F_\mathfrak p$ $\iff \mathfrak p$ splits. ($F(\sqrt\Delta)/F$ is unramified at $\mathfrak p$:
`DVR.exists_disc_eq_sq_mul_one_sub_four_of_level_zero`.) From `DVR.arfSignQ_eq_one_iff_isSquare_frac`. -/
@[kb "omeara1963" "§93D, 93:16, p. 259; 93:18, p. 260 (dyadic unimodular lattices)"]
theorem arfSignQ_eq_quadSymbolNF {Q : QuadForm (𝓞 F) n} (h2 : (2 : 𝓞 F) ∈ v.asIdeal)
    (hN : NF.NotDvdLevel v Q) (hn : 1 ≤ n) :
    DVR.arfSignQ (NF.Qp v Q) (NF.π v) = quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) := by
  have hdet := det_not_mem_of_notDvdLevel v hN
  have hx : (-1) ^ (n / 2) * Q.hessian.det ∉ v.asIdeal := by
    intro h
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h' | h'
    · exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_one.neg.pow _))
    · exact hdet h'
  have key := DVR.arfSignQ_eq_one_iff_isSquare_frac (v.adicCompletion F) (NF.Qp v Q) (NF.irreducible_π v)
    (NF.π_dvd_two v h2) (NF.two_ne_zero' v) hN hn
  rw [NF.det_hessian_Qp] at key
  have e : NF.ι v ((-1) ^ (n / 2) * Q.hessian.det) = (-1) ^ (n / 2) * NF.ι v Q.hessian.det := by
    simp [map_mul, map_pow, map_neg, map_one]
  unfold quadSymbolNF
  rw [ite_eq_right hx, e]
  by_cases hs : IsSquare (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)
      ((-1) ^ (n / 2) * NF.ι v Q.hessian.det))
  · rw [ite_eq_left hs]; exact key.2 hs
  · rw [ite_eq_right hs]
    have : DVR.arfSignQ (NF.Qp v Q) (NF.π v) ≠ 1 := fun h => hs (key.1 h)
    unfold DVR.arfSignQ at this ⊢; split_ifs at this ⊢ <;> simp_all

/-- Good primes (`IsGoodPrimeNF`: $\mathfrak p \nmid 2\det H$) are primes $\mathfrak p \nmid N$ (Lemma 2.2). -/
theorem notDvdLevel_of_isGoodPrimeNF {Q : QuadForm (𝓞 F) n} (hG : IsGoodPrimeNF Q v) : NF.NotDvdLevel v Q :=
  (NF.notDvdLevel_iff v Q hG.1).2 hG.2

/-- At $\mathfrak p \nmid 2$, $\mathfrak p \nmid N \iff \mathfrak p$ is good. -/
theorem notDvdLevel_iff_isGoodPrimeNF {Q : QuadForm (𝓞 F) n} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    NF.NotDvdLevel v Q ↔ IsGoodPrimeNF Q v :=
  ⟨fun hN => ⟨h2, (NF.notDvdLevel_iff v Q h2).1 hN⟩, notDvdLevel_of_isGoodPrimeNF v⟩

/-- **For odd $n$ every dyadic $\mathfrak p$ divides $N$**, so for odd $n$ the bad set $\{\mathfrak p \mid N\}$ already contains every
dyadic prime: it equals $\{\mathfrak p \mid 2\det H\}$, the bad set of `thm_5_7_c_odd_NF`. -/
theorem not_notDvdLevel_of_odd {Q : QuadForm (𝓞 F) n} (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (hodd : Odd n) :
    ¬ NF.NotDvdLevel v Q := fun hN =>
  (Nat.not_even_iff_odd.2 hodd) (DVR.even_of_isLocalLevel_zero_dyadic (NF.Qp v Q) (NF.irreducible_π v)
    (NF.π_dvd_two v h2) (NF.two_ne_zero' v) hN)

/-- **$C'_\mathfrak p(T')$ at every $\mathfrak p \nmid N$, $n \ge 4$ even, over $F$** (Table 2, p. 370; (5.12) corrected; dyadic
$\mathfrak p$ included): with $X = N\mathfrak p^{(n-2)/2}$ and $\left(\frac{\Delta}{\mathfrak p}\right)$ = `quadSymbolNF`,
$\Delta = (-1)^{n/2}\det H$, for $T' \notin \mathfrak p^2$: $C'_\mathfrak p(T') = X/(X+1)$ if $\left(\frac{\Delta}{\mathfrak p}\right) = -1$ and
$T' \notin \mathfrak p$, and $1$ otherwise. Non-dyadic: `localConstC'NF_good_even` (needs `GoodPrimeShape`); dyadic:
`NF.localConstC'_of_level_zero_dyadic` with $\varepsilon = \left(\frac{\Delta}{\mathfrak p}\right)$ (`arfSignQ_eq_quadSymbolNF`). -/
@[kb "hanke2004" "Table 2, p. 370; (5.12) corrected (every p ∤ N incl. dyadic, over F)"]
theorem localConstC'NF_level_even {Q : QuadForm (𝓞 F) n} (hn : 4 ≤ n) (heven : Even n)
    (hN : NF.NotDvdLevel v Q) (hsh : (2 : 𝓞 F) ∉ v.asIdeal → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT2 : T ∉ v.asIdeal ^ 2) :
    NF.localConstC' v Q T =
      if quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1 := by
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  · obtain ⟨hA, -, hC, -⟩ := NF.localConstC'_of_level_zero_dyadic v Q h2 hN (by omega) T hT2
    rw [← arfSignQ_eq_quadSymbolNF v h2 hN (by omega), show n / 2 - 1 = (n - 2) / 2 by omega] at *
    have hpm : DVR.arfSignQ (NF.Qp v Q) (NF.π v) = 1 ∨ DVR.arfSignQ (NF.Qp v Q) (NF.π v) = -1 := by
      unfold DVR.arfSignQ; split_ifs <;> simp
    by_cases hT : T ∈ v.asIdeal
    · rw [ite_eq_right (fun h => h.2 hT)]; exact hA hT
    · rcases hpm with h | h
      · rw [ite_eq_right (fun h' => by rw [h] at h'; exact absurd h'.1 (by decide))]
        exact (NF.localConstC'_of_level_zero_dyadic v Q h2 hN (by omega) T hT2).2.1 hT h
      · rw [ite_eq_left ⟨h, hT⟩]
        exact hC hT h
  · have hG : IsGoodPrimeNF Q v := (notDvdLevel_iff_isGoodPrimeNF v h2).1 hN
    rw [quadSymbolNF_eq_charNF v h2]
    exact localConstC'NF_good_even v hn heven hG (hsh h2) hT2

end Local

/-! ### Theorem 5.7(b), (c) over $F$ with bad set $\{\mathfrak p \mid N\}$ -/

/-- **Theorem 5.7(c), $n \ge 4$ even (and (b) for $n = 4$), ratio form, over $F$, with bad primes $\mathfrak p \mid N$ only**
(Hanke 2004, p. 373; proof pp. 374–375): `thm_5_7_c_even_NF` with the good set enlarged from $\mathfrak p \nmid 2\det H$ to every
$\mathfrak p \nmid N$ (`NF.NotDvdLevel`), dyadic primes included, and $\Phi_n(\mathfrak p) = \left(\frac{\Delta}{\mathfrak p}\right)$ (`quadSymbolNF`,
$\Delta = (-1)^{n/2}\det H$; the Arf sign at dyadic $\mathfrak p$). Under the hypotheses of `thm_5_7_c_even_NF`, with $T' \notin \mathfrak p^2$ at
the $\mathfrak p \in S$ with $\mathfrak p \nmid N$:
$$a_E(T'x^2) \;\ge\; a_E(T')\,N\big((x)_{\mathrm{Iso}}\big)^{n-2}\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p \mid N}C'_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \in S,\ \mathfrak p \nmid N,\ \mathfrak p \nmid T'\\ (\Delta/\mathfrak p) = -1}}\frac{X_\mathfrak p}{X_\mathfrak p + 1}.$$
The hypothesis `hshape` (the good-prime shape at $\mathfrak p \nmid 2\det H$) is kept as in `thm_5_7_c_even_NF`. -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even, over F, bad set p | N)"]
theorem thm_5_7_c_even_level_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 4 ≤ n) (heven : Even n)
    (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F} (hT0 : T ≠ 0)
    (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal),
          (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) ≤
      aENF Q (T * x ^ 2) := by
  have h := aEWithNF_mul_sq_ge Q hQ hQnd (by omega) hT0 hT hx hS hst (fun v => NF.NotDvdLevel v Q)
    (fun v => if quadSymbolNF v ((-1) ^ (n / 2) * Q.hessian.det) = -1 ∧ T ∉ v.asIdeal then
        (N𝔭 v) ^ ((n - 2) / 2) / ((N𝔭 v) ^ ((n - 2) / 2) + 1) else 1)
    (fun v hv hN => by
      rw [localConstC'NF_level_even v hn heven hN
        (fun h2 => hshape v ((notDvdLevel_iff_isGoodPrimeNF v h2).1 hN)) (hT2 v hv hN)]
      refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < (N𝔭 v) ^ ((n - 2) / 2) := pow_pos (by linarith [two_le_normP_real v]) _
      split_ifs <;> positivity)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape hT0)
    (isEulerProductValueNF_eulerProductNF hQnd hn hshape (mul_ne_zero hT0 (pow_ne_zero _ hx)))
  rwa [← Finset.prod_filter] at h

/-- **Theorem 5.7(b) over $F$, ratio form, with bad primes $\mathfrak p \mid N$ only** (Hanke 2004, p. 373; proof p. 375), $n = 4$:
`thm_5_7_b_NF` with every $\mathfrak p \nmid N$ (dyadic included) good and $\chi(\mathfrak p) = \left(\frac{\det H}{\mathfrak p}\right)$
(`quadSymbolNF`; the character of $F(\sqrt D)/F$, unramified at every $\mathfrak p \nmid N$):
$$a_E(T'x^2) \;\ge\; a_E(T')\,N\big((x)_{\mathrm{Iso}}\big)^2\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p \mid N}C'_\mathfrak p(T')
  \prod_{\substack{\mathfrak p \in S,\ \mathfrak p \nmid N,\ \mathfrak p \nmid T'\\ \chi(\mathfrak p) = -1}}\Big(1 + \frac1{N\mathfrak p}\Big)^{-1}.$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form, over F, bad set p | N)"]
theorem thm_5_7_b_level_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {T : 𝓞 F}
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, NF.NotDvdLevel v Q → T ∉ v.asIdeal ^ 2) :
    aENF Q T * (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ NF.NotDvdLevel v Q),
          NF.localConstC' v Q T) *
        ∏ v ∈ (S.filter (fun v => NF.NotDvdLevel v Q)).filter
            (fun v => quadSymbolNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) := by
  have h := thm_5_7_c_even_level_NF Q hQ hQnd le_rfl (by decide) hshape hT0 hT hx hS hst hT2
  simp only [show 4 / 2 = 2 from rfl, show (4 - 2) / 2 = 1 from rfl, show 4 - 2 = 2 from rfl,
    pow_one, neg_one_sq, one_mul] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (0 : ℝ) < N𝔭 v := by linarith [two_le_normP_real v]
  field_simp

/-! ### Over $\mathbb{Q}$: $p = 2 \nmid N$ and the Kronecker symbol $\left(\frac{\Delta}{2}\right) = \chi_8(\Delta)$ -/

section Rat

local notation "ι2" => Int.castRingHom ℤ_[2]

/-- Every element $z$ of the residue field $\mathbb{F}_2$ of $\mathbb{Z}_2$ has $z^2 + z = 0$. -/
theorem residue_two_sq_add_self (z : IsLocalRing.ResidueField ℤ_[2]) : z ^ 2 + z = 0 := by
  have h : ∀ w : ZMod 2, w ^ 2 + w = 0 := by decide
  apply PadicInt.residueField.injective
  rw [map_add, map_pow, map_zero]; exact h _

theorem irreducible_two_padicInt : Irreducible (2 : ℤ_[2]) := by
  simpa using PadicInt.irreducible_p (p := 2)

theorem two_dvd_intCast_iff (a : ℤ) : (2 : ℤ_[2]) ∣ ι2 a ↔ (2 : ℤ) ∣ a := by
  have := PadicInt.pow_p_dvd_int_iff (p := 2) 1 a
  simpa using this

/-- **$2 \nmid N$ makes $Q \otimes \mathbb{Z}_2$ even unimodular**: an odd level $L$ ($LH^{-1} = W$ even symmetric) is a unit of
$\mathbb{Z}_2$, so $2^0$ is a local level. -/
theorem isLocalLevel_two_of_odd_level {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hN : Odd (level Q)) :
    DVR.IsLocalLevel (Q.map ι2) 2 0 := by
  obtain ⟨W, hW, hE⟩ := isLevel_level hQ
  have hu : IsUnit (ι2 (level Q : ℤ)) := by
    refine LocalDensity.DVR.dvr_isUnit_of_not_dvd irreducible_two_padicInt ?_
    rw [two_dvd_intCast_iff]
    rintro ⟨c, hc⟩; rcases hN with ⟨m, hm⟩; omega
  refine ⟨((hu.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) • W.map ι2, ?_, ?_, fun i => ?_⟩
  · rw [hessian_map_NF, Matrix.mul_smul, ← Matrix.map_mul, hW, pow_zero, one_smul]
    ext i j : 1
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp only [mul_one]; exact hu.val_inv_mul
    · simp
  · rw [Matrix.transpose_smul, ← Matrix.transpose_map, hE.1]
  · obtain ⟨k, hk⟩ := hE.2 i
    refine ⟨((hu.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ι2 k, ?_⟩
    simp only [Matrix.smul_apply, Matrix.map_apply, hk, smul_eq_mul, map_add]
    ring

/-- **Over $\mathbb{Q}$, at $p = 2 \nmid N$ the Arf sign is the Kronecker symbol $\left(\frac{\Delta}{2}\right) = \chi_8(\Delta)$**
($\Delta = (-1)^{n/2}\det H$ = `disc Q`, $n \ge 1$; then $n$ is even and $\Delta \equiv 1 \pmod 4$): $\varepsilon(Q \bmod 2) = +1 \iff
\Delta \equiv 1 \pmod 8 \iff \Delta \in \mathbb{Z}_2^{\times 2}$. So $p = 2$ is a good prime of Thm 5.7 whenever $2 \nmid N$, with
$\Phi_n(2) = \chi_8(\Delta)$; with `chiCharLevel_two` this is $\chi_Q(2)$ (`arfSignQ_two_eq_chiCharLevel`). -/
@[kb "hanke2004" "Φ_n(2) = (Δ/2) at 2 ∤ N (dyadic, over ℚ)"]
theorem arfSignQ_two_eq_chi8 {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (hN : Odd (level Q)) :
    DVR.arfSignQ (Q.map ι2) 2 = ZMod.χ₈ (disc Q) := by
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[2]) :=
    Fintype.ofEquiv (ZMod 2) PadicInt.residueField.symm.toEquiv
  have hL := isLocalLevel_two_of_odd_level hQ hN
  have hπ := irreducible_two_padicInt
  have h20 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  have hkey := DVR.arfSignQ_eq_one_iff (Q.map ι2) hπ dvd_rfl h20 hL hn
  obtain ⟨B, T, hB, hΔ⟩ := DVR.exists_disc_eq_sq_mul_one_sub_four_of_level_zero (Q.map ι2) hπ dvd_rfl h20 hL
  have hD : (-1) ^ (n / 2) * (Q.map ι2).hessian.det = ι2 (disc Q) := by
    rw [hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det, disc]; simp
  rw [hD] at hkey hΔ
  -- `B² ≡ 1 mod 8`
  obtain ⟨k, hk⟩ : ∃ k, B ^ 2 = 1 + 8 * k := by
    have hB1 : IsLocalRing.residue ℤ_[2] B = 1 := by
      have hne : IsLocalRing.residue ℤ_[2] B ≠ 0 := fun h =>
        hπ.not_isUnit (isUnit_of_dvd_unit ((DVR.residue_eq_zero_iff_dvd hπ B).1 h) hB)
      have h01 : ∀ w : ZMod 2, w ≠ 0 → w = 1 := by decide
      apply PadicInt.residueField.injective
      rw [map_one]; exact h01 _ (by simpa using hne)
    obtain ⟨c, hc⟩ : (2 : ℤ_[2]) ∣ B - 1 := by
      rw [← DVR.residue_eq_zero_iff_dvd hπ, map_sub, hB1, map_one, sub_self]
    obtain ⟨d, hd⟩ : (2 : ℤ_[2]) ∣ c ^ 2 + c := by
      rw [← DVR.residue_eq_zero_iff_dvd hπ, map_add, map_pow]; exact residue_two_sq_add_self _
    exact ⟨d, by rw [show B = 1 + 2 * c by linear_combination hc]; linear_combination 4 * hd⟩
  have hsq : IsSquare (ι2 (disc Q)) ↔ (2 : ℤ_[2]) ∣ T := by
    rw [hΔ, DVR.isSquare_unit_sq_mul_iff hB, DVR.isSquare_one_sub_four_mul_iff hπ dvd_rfl h20,
      ← DVR.residue_eq_zero_iff_dvd hπ]
    exact ⟨fun ⟨z, hz⟩ => by rw [← hz, residue_two_sq_add_self], fun h => ⟨0, by rw [h]; ring⟩⟩
  have hm1 : ι2 (disc Q - 1) = 4 * (2 * k * (1 - 4 * T) - T) := by
    rw [map_sub, hΔ, hk, map_one]; ring
  have h4 : (4 : ℤ) ∣ disc Q - 1 := by
    have := (PadicInt.pow_p_dvd_int_iff (p := 2) 2 (disc Q - 1)).1
    norm_num at this
    exact this ⟨_, by rw [← map_ofNat ι2 4] at hm1 ⊢; simpa using hm1⟩
  have h8 : (8 : ℤ) ∣ disc Q - 1 ↔ (2 : ℤ_[2]) ∣ T := by
    have e := PadicInt.pow_p_dvd_int_iff (p := 2) 3 (disc Q - 1)
    norm_num at e
    rw [← e]
    have : ((disc Q : ℤ_[2]) - 1) = 4 * (2 * k * (1 - 4 * T) - T) := by simpa using hm1
    rw [this, show (8 : ℤ_[2]) = 4 * 2 by norm_num, mul_dvd_mul_iff_left (by norm_num)]
    constructor
    · intro h; have := dvd_sub ((dvd_mul_right 2 (k * (1 - 4 * T)))) h
      simpa [mul_assoc] using this
    · intro h; exact dvd_sub (by rw [mul_assoc]; exact dvd_mul_right _ _) h
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  have hmod : disc Q % 8 = 1 ∨ disc Q % 8 = 5 := by omega
  rcases hmod with h | h
  · rw [ite_eq_right (by omega), ite_eq_left (Or.inl h)]
    exact hkey.2 (hsq.2 (h8.1 (by omega)))
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hns : ¬ IsSquare (ι2 (disc Q)) := fun hs => by have := h8.2 (hsq.1 hs); omega
    have : DVR.arfSignQ (Q.map ι2) 2 ≠ 1 := fun h' => hns (hkey.1 h')
    unfold DVR.arfSignQ at this ⊢; split_ifs at this ⊢ <;> simp_all

/-- **$\Phi_n(2) = \chi_Q(2)$ at $2 \nmid N$** (positive definite $Q$, $n = 2k$): the dyadic Arf sign equals the value at $2$ of the
theta character `chiCharLevel` (`chiCharLevel_two`), i.e. the Kronecker symbol $\left(\frac{\Delta}{2}\right)$. -/
theorem arfSignQ_two_eq_chiCharLevel {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) (hk : 1 ≤ k)
    (hN : Odd (level Q)) :
    DVR.arfSignQ (Q.map ι2) 2 = chiCharLevel hQ hn (2 : ℤ) := by
  rw [chiCharLevel_two hQ hn hN, arfSignQ_two_eq_chi8 hQ.nondegenerate (by omega) hN]

end Rat

end QuadFormsKB.Siegel
