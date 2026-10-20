/-
# Local densities over a DVR: per-place lower bounds (the local core of Thms 5.7, 5.9)

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, finite residue field $\mathbb{F}$ of size $q$; e.g. the
completion $\mathfrak{o}_\mathfrak{p}$ of a number field at any prime). The list L1–L13 of local inequalities of §5 and
their status is in the module docstring of `LowerBounds.lean`; here are their DVR versions (the paper's Thm 5.7 is over
a totally real field $F$, so these are the per-place inputs at every $\mathfrak{p}$).

* **Every prime with $2 \ne 0$** (dyadic and ramified dyadic included): (5.8) `DVR.localDensity_pow_sq_div`,
  (5.11) `DVR.localDensity_pow_sq_ge`, `DVR.localDensity_pow_sq_div_ge`, Remark 5.4.1(a) `DVR.tendsto_localDensity_pow_sq`,
  `DVR.localDensity_pow_sq_mono`, `DVR.localDensityOf_nonZero_pow_sq`, (5.7) without isotropy
  `DVR.localDensity_pow_sq_of_stable`, $\beta > 0$ `DVR.localDensity_pos_of_isLocallyRepresentedAt`, square classes
  `DVR.localDensity_mul_sq_of_isUnit`, Thm 5.9 local inequality `DVR.thm_5_9_local`; for **complete** $R$ also
  $C_\mathfrak{p} > 0$ at isotropic $\mathfrak{p}$ `DVR.localConstC_pos` and $C_\mathfrak{p} = 0$, $\beta_\mathfrak{p}(T'\pi^{2\nu}) = q^{-(n-2)\nu}\beta_\mathfrak{p}(T')$
  at anisotropic $\mathfrak{p}$ (`DVR.localConstC_eq_zero_of_anisotropic`, `DVR.localDensity_pow_sq_of_anisotropic`; via the
  corrected Lemma 3.8).
* **Good non-dyadic $\pi \nmid 2N$** ($Q = \langle a_i\rangle$, $a_i$ units, $\chi$ the quadratic character of $\mathbb{F}$):
  stability `DVR.isPStable_diag`, explicit $\beta_\pi(T')$ (`DVR.localDensity_diag_odd_unit`, …), $C'_\pi$ and corrected
  (5.12) (`DVR.eq_5_12`, `DVR.localConstC'_diag_three`), per-place bounds `DVR.localDensity_ge_even`,
  `DVR.localDensity_ge_odd`, `DVR.localDensity_ge_three`.
* **Good dyadic $\pi \mid 2$, $\pi \nmid N$** (even unimodular `DVR.pairSumForm`, any ramification $e$, $n = 2r \ge 4$,
  $\Phi_n(\pi) :=$ Arf sign $\varepsilon$): nondegeneracy `DVR.nondegenerate_pairSumForm`, stability `DVR.isPStable_pairSum`,
  $C'_\pi$ and (5.12) `DVR.localConstC'_pairSum`, per-place bound `DVR.localDensity_ge_pairSum` (the factor
  $\frac{q-1}{q+1}$-type bound of Thm 5.7(b), (c) at dyadic $\mathfrak{p} \nmid N$: an update, since the paper's Table 2 route
  needs $\mathfrak{p} \nmid 2N$). For odd $n$ every dyadic $\mathfrak{p}$ divides $N$, so nothing more is needed there.

Products over the places of a number field are formal consequences (`Finset.prod_le_prod₀`) once the completions are
identified with DVRs; this identification is not formalized here, so products are stated over $\mathbb{Q}$ only
(`LowerBounds.lean`). **Depends on** `LowerBounds.lean` (the algebra of (5.7)–(5.11)), `DVRDyadicTable.lean`.
-/
import QuadFormsKB.LocalDensity.LowerBounds
import QuadFormsKB.LocalDensity.DVRDyadicTable

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Filter Topology

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-! ### General local facts over $R$ (every prime with $2 \ne 0$, including dyadic ones) -/

section General

/-- $q = \#R/\pi > 1$. -/
theorem one_lt_q [Finite 𝔽] : 1 < q R := Finite.one_lt_card

/-- $q^{n-2} > 1$ for $n \ge 3$. -/
theorem one_lt_q_pow_sub_two [Finite 𝔽] (hn : 3 ≤ n) : 1 < (q R : ℝ) ^ (n - 2) :=
  one_lt_pow₀ (by exact_mod_cast one_lt_q (R := R)) (by omega)

/-- $\beta_\pi(m) \ge 0$ for $Q$ nondegenerate, $m \ne 0$, $2 \ne 0$. -/
theorem localDensity_nonneg [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (m : R) (hm : m ≠ 0) : 0 ≤ localDensity Q π m := by
  obtain ⟨k, hk⟩ := (localDensity_eventually_eq Q hQ π hπ m hm h20).exists
  rw [← hk]; positivity

/-- **Locally represented ⟹ $\beta_\pi(m) > 0$** (Hanke 2004, Def. 5.2, p. 368). -/
@[kb "hanke2004" "Def. 5.2, p. 368"]
theorem localDensity_pos_of_isLocallyRepresentedAt [Finite 𝔽] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (m : R) (hm : m ≠ 0)
    (h : IsLocallyRepresentedAt Q π m) : 0 < localDensity Q π m := by
  obtain ⟨k, hk, hpos⟩ := ((localDensity_eventually_eq Q hQ π hπ m hm h20).and h).exists
  rw [← hk]
  have hq : (0 : ℝ) < q R := by exact_mod_cast (q_pos (R := R))
  exact div_pos (by exact_mod_cast hpos) (pow_pos hq _)

/-- $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2T) \ge 0$ (for $n \ge 3$, by (5.6)). -/
theorem localDensityOf_nonZero_sq_nonneg [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (T : R) (hT0 : T ≠ 0) :
    0 ≤ localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) := by
  rw [localDensityOf_nonZero_eq Q hQ π hπ h20 (by omega) T hT0, sub_nonneg]
  have h := localDensity_le_mul_sq Q hQ hn π hπ h20 T hT0
  have hp : (0 : ℝ) < (q R : ℝ) ^ (n - 2) := pow_pos (by exact_mod_cast (q_pos (R := R))) _
  rw [inv_mul_le_iff₀ hp]; exact h

/-- **(5.7) without the isotropy hypothesis** over $R$ (as `LocalDensity.localDensity_pow_sq_of_stable`). -/
theorem localDensity_pow_sq_of_stable [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (hn : n ≠ 1) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R)
    (hT0 : T ≠ 0) (hT : IsPStable Q S₀ π T) (e : ℕ) :
    localDensity Q π (π ^ (2 * e) * T) =
      localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) *
          ∑ i ∈ Finset.range e, ((q R : ℝ) ^ (n - 2))⁻¹ ^ i +
        localDensity Q π T / ((q R : ℝ) ^ (n - 2)) ^ e := by
  rw [localDensityOf_nonZero_eq Q hQ π hπ h20 hn T hT0]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [localDensity_pow_sq_step Q hQ π hπ h20 hn T hT0 hT.2 e, ih, Finset.sum_range_succ',
      Finset.sum_congr rfl (fun i _ => pow_succ ((q R : ℝ) ^ (n - 2))⁻¹ i), ← Finset.sum_mul,
      pow_succ (_ ^ _) e, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

theorem localConstC_eq_alg (Q : QuadForm R n) (π : R) (T : R) :
    localConstC Q π T = (q R : ℝ) ^ (n - 2) / ((q R : ℝ) ^ (n - 2) - 1) *
      (localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) / localDensity Q π T) :=
  rfl

/-- **The modified local constant** $C'_\pi(T') = \min\{1, C_\pi(T')\}$ over $R$ (Hanke 2004, (5.11), p. 371). -/
noncomputable def localConstC' (Q : QuadForm R n) (π : R) (T : R) : ℝ := min 1 (localConstC Q π T)

/-- $C_\pi(T') \ge 0$. -/
theorem localConstC_nonneg [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (T : R) (hT0 : T ≠ 0) :
    0 ≤ localConstC Q π T :=
  localConst_alg_nonneg _ _ _ (one_lt_q_pow_sub_two hn)
    (localDensityOf_nonZero_sq_nonneg Q hQ hn π hπ h20 T hT0)
    (localDensity_nonneg Q hQ π hπ h20 T hT0)

/-- **(5.8)** over $R$ (Hanke 2004, p. 369): for $T'$ $\pi$-stable,
$\beta_\pi(T'\pi^{2\nu})/\beta_\pi(T') = C_\pi(T') + (1 - C_\pi(T'))/q^{(n-2)\nu}$. Every prime with $2 \ne 0$, isotropic or not. -/
@[kb "hanke2004" "(5.8), p. 369"]
theorem localDensity_pow_sq_div [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ π T) (ν : ℕ) :
    localDensity Q π (π ^ (2 * ν) * T) / localDensity Q π T =
      localConstC Q π T + (1 - localConstC Q π T) / (q R : ℝ) ^ ((n - 2) * ν) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT0 hT.1
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) π hπ h20 S₀ T hT0 hT ν,
    pow_sq_closed_form _ _ _ (one_lt_q_pow_sub_two hn) hβ.ne', localConstC_eq_alg, pow_mul]
  field_simp

/-- **$C_\pi(T') > 0$ at isotropic primes** over complete $R$ (Hanke 2004, p. 370; via the corrected Lemma 3.8,
`DVR.anisotropic_iff_zeroType`). -/
@[kb "hanke2004" "Proof of Thm 5.4, p. 370 (C_p > 0)"]
theorem localConstC_pos [Finite 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n))
    (hiso : Q.IsotropicIn K) (T : R) (hT0 : T ≠ 0) (hT : IsPStable Q S₀ π T) :
    0 < localConstC Q π T := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT0 hT.1
  have hK0 := localDensityOf_nonZero_sq_nonneg Q hQ hn π hπ h20 T hT0
  have hY := one_lt_q_pow_sub_two (R := R) hn
  have hq0 : (0 : ℝ) < q R := by exact_mod_cast (q_pos (R := R))
  have hKpos : 0 < localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) := by
    refine lt_of_le_of_ne hK0 fun hK =>
      ((anisotropic_iff_zeroType K Q π hπ S₀ T hT).2 ?_) hiso
    have hpZ : π ^ 2 ≠ 0 := pow_ne_zero _ hπ.ne_zero
    have h1 := localDensity_eventually_eq Q hQ π hπ (π ^ 2 * T) (mul_ne_zero hpZ hT0) h20
    have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually
      (localDensity_eventually_eq Q hQ π hπ T hT0 h20)
    filter_upwards [h1, h2, Filter.eventually_ge_atTop 2] with k hk1 hk2 hk
    have hs := normalized_split Q π hπ (by omega) T k hk
    rw [hk1, hk2, ← sub_eq_iff_eq_add', ← localDensityOf_nonZero_eq Q hQ π hπ h20 (by omega) T hT0,
      ← hK, eq_comm, div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · rw [repCount_eq_zero_add_nonZero Q π hπ k]
      exact_mod_cast (show _ = 0 from by exact_mod_cast hs) ▸ (add_zero _)
    · exact absurd hs (pow_ne_zero _ hq0.ne')
  rw [localConstC_eq_alg]
  have : 0 < (q R : ℝ) ^ (n - 2) - 1 := by linarith
  positivity

/-- **$C_\pi(T') = 0$ at anisotropic primes** over complete $R$ ($K = 0$ by Lemma 3.8). -/
theorem localConstC_eq_zero_of_anisotropic [Finite 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn K) (T : R)
    (hT : IsPStable Q S₀ π T) :
    localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) = 0 ∧ localConstC Q π T = 0 := by
  have hK : localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) = 0 := by
    apply limUnder_eq_of_eventually
    filter_upwards [eventually_repCountOf_nonZero_eq_zero K Q π hπ haniso T hT.2] with k hk
    have := hk 1 le_rfl
    rw [mul_one] at this
    rw [this]; simp
  refine ⟨hK, ?_⟩
  rw [localConstC_eq_alg, hK]; simp

/-- **Remark 5.4.1(a), anisotropic case** over complete $R$: $\beta_\pi(T'\pi^{2\nu}) = \beta_\pi(T')/q^{(n-2)\nu}$. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (anisotropic)"]
theorem localDensity_pow_sq_of_anisotropic [Finite 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0)
    (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn K) (T : R) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ π T) (ν : ℕ) :
    localDensity Q π (π ^ (2 * ν) * T) = localDensity Q π T / (q R : ℝ) ^ ((n - 2) * ν) := by
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) π hπ h20 S₀ T hT0 hT ν,
    (localConstC_eq_zero_of_anisotropic K Q π hπ S₀ haniso T hT).1, pow_mul]
  simp

/-- **(5.11)** over $R$ (Hanke 2004, p. 371), multiplied out: $\beta_\pi(T'\pi^{2\nu}) \ge C'_\pi(T')\,\beta_\pi(T')$ for
$T'$ $\pi$-stable, all $\nu \ge 0$; every prime with $2 \ne 0$, isotropic or not. -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_ge [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ π T) (ν : ℕ) :
    localConstC' Q π T * localDensity Q π T ≤ localDensity Q π (π ^ (2 * ν) * T) := by
  rw [localDensity_pow_sq_of_stable Q hQ (by omega) π hπ h20 S₀ T hT0 hT ν, localConstC',
    localConstC_eq_alg]
  exact pow_sq_ge_min _ _ _ (one_lt_q_pow_sub_two hn)
    (localDensityOf_nonZero_sq_nonneg Q hQ hn π hπ h20 T hT0)
    (localDensity_nonneg Q hQ π hπ h20 T hT0) ν

/-- **(5.11)** over $R$, as printed: $\beta_\pi(T'\pi^{2\nu})/\beta_\pi(T') \ge C'_\pi(T')$. -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_div_ge [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R)
    (hT0 : T ≠ 0) (hT : IsPStable Q S₀ π T) (ν : ℕ) :
    localConstC' Q π T ≤ localDensity Q π (π ^ (2 * ν) * T) / localDensity Q π T := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT0 hT.1
  rw [le_div_iff₀ hβ]
  exact localDensity_pow_sq_ge Q hQ hn π hπ h20 S₀ T hT0 hT ν

/-- **Remark 5.4.1(a)** over $R$: $\beta_\pi(T'\pi^{2\nu}) \to C_\pi(T')\beta_\pi(T')$ (normalization $q^{(n-2)\nu}$ for
$a_E$, see `LocalDensity.tendsto_localDensity_pow_sq`). -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370"]
theorem tendsto_localDensity_pow_sq [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R)
    (hT0 : T ≠ 0) (hT : IsPStable Q S₀ π T) :
    Tendsto (fun ν : ℕ => localDensity Q π (π ^ (2 * ν) * T)) atTop
      (𝓝 (localConstC Q π T * localDensity Q π T)) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT0 hT.1
  simp_rw [localDensity_pow_sq_of_stable Q hQ (by omega) π hπ h20 S₀ T hT0 hT]
  exact pow_sq_tendsto _ _ _ (one_lt_q_pow_sub_two hn) hβ.ne'

/-- **Remark 5.4.1(a), monotonicity** over $R$. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (monotonically)"]
theorem localDensity_pow_sq_mono [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (T : R) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ π T) :
    (localConstC Q π T ≤ 1 → Antitone fun ν : ℕ => localDensity Q π (π ^ (2 * ν) * T)) ∧
    (1 ≤ localConstC Q π T → Monotone fun ν : ℕ => localDensity Q π (π ^ (2 * ν) * T)) := by
  have hβ := localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT0 hT.1
  simp_rw [localDensity_pow_sq_of_stable Q hQ (by omega) π hπ h20 S₀ T hT0 hT]
  exact ⟨pow_sq_antitone _ _ _ (one_lt_q_pow_sub_two hn) hβ,
    pow_sq_monotone _ _ _ (one_lt_q_pow_sub_two hn) hβ⟩

/-- **Remark 5.4.1(a), primitive densities** over $R$: $\beta^*_\pi(T'\pi^{2\nu}) = K$ for $\nu \ge 1$ ($T'$ stable).
See the erratum note at `LocalDensity.localDensityOf_nonZero_pow_sq`. -/
@[kb "hanke2004" "Remark 5.4.1(a), p. 370 (primitive)"]
theorem localDensityOf_nonZero_pow_sq (Q : QuadForm R n) (π : R) (S₀ : Finset (Fin n)) (T : R)
    (hT : IsPStable Q S₀ π T) (ν : ℕ) (hν : 1 ≤ ν) :
    localDensityOf Q π (π ^ (2 * ν) * T) (fun k x => ¬ IsZeroType π k x) =
      localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) := by
  unfold localDensityOf Filter.limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [hT.2] with k hk
  rw [hk ν hν]

/-- $Q(c\vec{x}) = c^2 Q(\vec{x})$ over any $R$-algebra. -/
theorem evalIn_smul (Q : QuadForm R n) {A : Type*} [CommRing A] [Algebra R A] (c : A)
    (x : Fin n → A) : Q.evalIn A (c • x) = c ^ 2 * Q.evalIn A x := by
  simp only [evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **$\beta_\pi$ depends only on the square class**: $r_{\pi^k}(u^2m) = r_{\pi^k}(m)$ and $\beta_\pi(u^2m) = \beta_\pi(m)$ for a
unit $u$. -/
theorem localDensity_mul_sq_of_isUnit (Q : QuadForm R n) (π : R) (u : R) (hu : IsUnit u) (m : R) :
    (∀ k, repCount Q π k (u ^ 2 * m) = repCount Q π k m) ∧
      localDensity Q π (u ^ 2 * m) = localDensity Q π m := by
  have hc : ∀ k, repCount Q π k (u ^ 2 * m) = repCount Q π k m := by
    intro k
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    set mk := Ideal.Quotient.mk (Ideal.span {π ^ k})
    have hb : mk v * mk u = 1 := by rw [← map_mul, hv, map_one]
    unfold repCount
    refine Nat.card_congr (Equiv.subtypeEquiv
      { toFun := fun x => mk v • x
        invFun := fun x => mk u • x
        left_inv := fun x => by simp only [smul_smul]; rw [mul_comm, hb, one_smul]
        right_inv := fun x => by simp only [smul_smul, hb, one_smul] } ?_)
    intro x
    simp only [Equiv.coe_fn_mk, evalIn_smul, map_mul, map_pow]
    constructor
    · intro h; rw [h, ← mul_assoc, ← mul_pow, hb]; ring
    · intro h
      calc Q.evalIn _ x = (mk u * mk v) ^ 2 * Q.evalIn _ x := by rw [mul_comm (mk u), hb]; ring
        _ = mk u ^ 2 * mk m := by rw [mul_pow, mul_assoc, h]
  refine ⟨hc, ?_⟩
  unfold localDensity
  simp_rw [hc]

end General

/-! ### Good non-dyadic primes $\pi \nmid 2N$: explicit local factors

$Q = \langle a_0, \dots, a_{n-1}\rangle$ with all $a_i$ units, $\pi \nmid 2$; $\chi$ is the quadratic character of $\mathbb{F} = R/\pi$
(the symbol $(\frac{\cdot}{\mathfrak p})$), $\Phi_n(\pi) = \chi((-1)^{n/2}D)$ ($n$ even), $\chi((-1)^{(n-1)/2}DT')$ ($n$ odd). These
are the $\mathbb{Q}$ results of `LowerBounds.lean` with $p \mapsto q$. -/

section Good

/-- A diagonal form with nonzero coefficients is nondegenerate when $2 \ne 0$. -/
theorem nondegenerate_diag (a : Fin n → R) (ha : ∀ i, a i ≠ 0) (h20 : (2 : R) ≠ 0) :
    (QuadForm.diag a).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [← two_mul]; exact mul_ne_zero h20 (ha i)

theorem two_ne_zero_of_not_dvd {π : R} (h2 : ¬ π ∣ 2) : (2 : R) ≠ 0 := by
  rintro h; exact h2 (h ▸ dvd_zero _)

theorem ne_zero_of_not_dvd' {π a : R} (ha : ¬ π ∣ a) : a ≠ 0 := by
  rintro rfl; exact ha (dvd_zero _)

/-- **Every $T$ is $\pi$-stable at a good non-dyadic prime** ($n \ge 3$). -/
theorem isPStable_diag [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (S₀ : Finset (Fin n)) (T : R) :
    IsPStable (QuadForm.diag a) S₀ π T := by
  refine ⟨isLocallyRepresentedAt_of_good a hn π hπ h2 ha T, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk ν hν
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  rw [repCountOf_nonZero_diag_succ a π hπ h2 ha, repCountOf_nonZero_diag_succ a π hπ h2 ha]
  congr 1
  apply repCountOf_congr
  exact ((mk_pow_one_eq_zero_iff π _).2 (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)).trans
    ((mk_pow_one_eq_zero_iff π _).2 (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)).symm

/-- **Writing $m = \pi^{2e}T'$ with $\pi^2 \nmid T'$** over $R$. -/
theorem exists_pow_sq_mul (π : R) (hπ : Irreducible π) (m : R) (hm : m ≠ 0) :
    ∃ e : ℕ, ∃ T : R, m = π ^ (2 * e) * T ∧ ¬ π ^ 2 ∣ T := by
  obtain ⟨v, u, rfl, hu⟩ := dvr_eq_pow_mul_unit hπ hm
  refine ⟨v / 2, π ^ (v % 2) * u, by rw [← mul_assoc, ← pow_add]; congr 2; omega, ?_⟩
  intro h
  rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
  · rw [h0] at h
    exact dvr_not_pow_succ_dvd hπ hu 0 (by simpa using dvd_trans (dvd_pow_self π two_ne_zero) h)
  · rw [h1] at h
    exact dvr_not_pow_succ_dvd hπ hu 1 h

theorem quadraticChar_res_sq_one [Fintype 𝔽] [DecidableEq 𝔽] {a : R} {π : R} (hπ : Irreducible π) (ha : ¬ π ∣ a) :
    ((quadraticChar 𝔽 (res a) : ℤ) : ℝ) = 1 ∨ ((quadraticChar 𝔽 (res a) : ℤ) : ℝ) = -1 := by
  rcases quadraticChar_dichotomy (fun h => ha ((residue_eq_zero_iff_dvd hπ a).1 h)) with h | h <;>
    simp [h]

theorem not_dvd_sign_prod (a : Fin n → R) {π : R} (hπ : Irreducible π) (ha : ∀ i, ¬ π ∣ a i)
    (s : ℕ) : ¬ π ∣ (-1) ^ s * ∏ i, a i := by
  rw [← residue_eq_zero_iff_dvd hπ]; exact residue_sign_prod_ne_zero a hπ ha s

theorem not_dvd_sign_prod_mul (a : Fin n → R) {π : R} (hπ : Irreducible π) (ha : ∀ i, ¬ π ∣ a i)
    (s : ℕ) (T : R) (hT : ¬ π ∣ T) : ¬ π ∣ (-1) ^ s * (∏ i, a i) * T := by
  intro h
  rcases hπ.prime.dvd_or_dvd h with h | h
  · exact not_dvd_sign_prod a hπ ha s h
  · exact hT h

/-- **$\beta_\pi(T')$, $n$ odd, $\pi \nmid T'$:** $1 + \Phi_n(\pi)\,q^{-(n-1)/2}$. -/
theorem localDensity_diag_odd_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (hodd : Odd n) (T : R) (hT : ¬ π ∣ T) :
    localDensity (QuadForm.diag a) π T =
      1 + ((quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) : ℤ) : ℝ) /
        (q R : ℝ) ^ ((n - 1) / 2) := by
  obtain ⟨j, rfl⟩ := hodd
  have hr := ((card_diag_mod_pi a π hπ h2 ha (by omega) T hT).2 ⟨j, rfl⟩).2
  rw [localDensity_unit a π hπ h2 ha T hT]
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  simp only [show 2 * j + 1 - 1 = 2 * j by omega, show 2 * j / 2 = j by omega] at hr ⊢
  have hr' : (repCount (QuadForm.diag a) π 1 T : ℝ) = (q R : ℝ) ^ (2 * j) +
      ((quadraticChar 𝔽 (res ((-1) ^ j * (∏ i, a i) * T)) : ℤ) : ℝ) * (q R : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr']
  field_simp
  ring

/-- **$\beta_\pi(T')$, $n$ odd, $\mathrm{ord}_\pi(T') = 1$:** $1 - q^{-(n-1)}$. -/
theorem localDensity_diag_odd_ord_one [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (hodd : Odd n) (T : R) (h1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localDensity (QuadForm.diag a) π T = 1 - 1 / (q R : ℝ) ^ (n - 1) := by
  have hr := ((card_diag_mod_pi a π hπ h2 ha (by obtain ⟨j, rfl⟩ := hodd; omega) 1
    (fun h => hπ.not_isUnit (isUnit_of_dvd_one h))).2 hodd).1
  rw [localDensity_diag_ord_one a π hπ h2 ha T h1 hT2, hr]
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  push_cast
  field_simp

/-- **$\beta_\pi(T')$, $n$ even, $\pi \nmid T'$:** $1 - \Phi_n(\pi)\,q^{-n/2}$. -/
theorem localDensity_diag_even_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (hn : 2 ≤ n) (heven : Even n) (T : R) (hT : ¬ π ∣ T) :
    localDensity (QuadForm.diag a) π T =
      1 - ((quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) : ℤ) : ℝ) / (q R : ℝ) ^ (n / 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 1, by omega⟩
  have hr := ((card_diag_mod_pi a π hπ h2 ha (by omega) T hT).1 heven).2
  rw [localDensity_unit a π hπ h2 ha T hT]
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  rw [show (2 * j + 2) / 2 - 1 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega] at hr
  have hr' : (repCount (QuadForm.diag a) π 1 T : ℝ) = (q R : ℝ) ^ (2 * j + 1) -
      ((quadraticChar 𝔽 (res ((-1) ^ ((2 * j + 2) / 2) * ∏ i, a i)) : ℤ) : ℝ) * (q R : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr', show 2 * j + 2 - 1 = 2 * j + 1 by omega, show (2 * j + 2) / 2 = j + 1 by omega]
  field_simp
  ring

/-- **$\beta_\pi(T')$, $n$ even, $\mathrm{ord}_\pi(T') = 1$:**
$(1 - \Phi_n(\pi)\,q^{-n/2})(1 + \Phi_n(\pi)\,q^{-(n-2)/2})$. -/
theorem localDensity_diag_even_ord_one [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 2 ≤ n) (heven : Even n) (T : R) (h1 : π ∣ T)
    (hT2 : ¬ π ^ 2 ∣ T) :
    localDensity (QuadForm.diag a) π T =
      (1 - ((quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) : ℤ) : ℝ) / (q R : ℝ) ^ (n / 2)) *
        (1 + ((quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) : ℤ) : ℝ) /
          (q R : ℝ) ^ ((n - 2) / 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 1, by omega⟩
  have hr := ((card_diag_mod_pi a π hπ h2 ha (by omega) 1
    (fun h => hπ.not_isUnit (isUnit_of_dvd_one h))).1 heven).1
  rw [localDensity_diag_ord_one a π hπ h2 ha T h1 hT2]
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  rw [show (2 * j + 2) / 2 - 1 = j by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega] at hr
  have hc := quadraticChar_res_sq_one hπ (not_dvd_sign_prod a hπ ha ((2 * j + 2) / 2))
  have hr' : (repCount (QuadForm.diag a) π 1 0 : ℝ) = (q R : ℝ) ^ (2 * j + 1) +
      ((quadraticChar 𝔽 (res ((-1) ^ ((2 * j + 2) / 2) * ∏ i, a i)) : ℤ) : ℝ) * ((q R : ℝ) - 1) *
        (q R : ℝ) ^ j := by
    exact_mod_cast hr
  rw [hr', show 2 * j + 2 - 1 = 2 * j + 1 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
    show (2 * j + 2 - 2) / 2 = j by omega]
  rw [show (2 * j + 2) / 2 = j + 1 by omega] at hc
  generalize ((quadraticChar 𝔽 (res ((-1) ^ (j + 1) * ∏ i, a i)) : ℤ) : ℝ) = c at hc ⊢
  field_simp
  rcases hc with rfl | rfl <;> ring

theorem three_le_q_real [Fintype 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    (3 : ℝ) ≤ q R := by exact_mod_cast three_le_q hπ h2

/-- **$C'_\pi(T') = 1$ for $\mathrm{ord}_\pi(T') = 1$** (Table 2). -/
theorem localConstC'_diag_ord_one [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (T : R) (h1 : π ∣ T)
    (hT2 : ¬ π ^ 2 ∣ T) : localConstC' (QuadForm.diag a) π T = 1 := by
  rw [localConstC', table2_ord_one a π hπ h2 ha hn T h1 hT2]
  have hY := one_lt_q_pow_sub_two (R := R) hn
  refine min_eq_left ?_
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **$C'_\pi(T')$, $n$ odd, $\pi \nmid T'$** (Table 2): $1$ if $\Phi_n(\pi) = -1$; $C_\pi(T') =
\frac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}}$ if $\Phi_n(\pi) = 1$. -/
theorem localConstC'_diag_odd_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : R)
    (hT : ¬ π ∣ T) :
    (quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) = -1 →
      localConstC' (QuadForm.diag a) π T = 1) ∧
    (quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) = 1 →
      localConstC' (QuadForm.diag a) π T = localConstC (QuadForm.diag a) π T ∧
      localConstC (QuadForm.diag a) π T =
        (1 - 1 / (q R : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (q R : ℝ) ^ (n - 2))) := by
  have hC := table2_odd_unit a π hπ h2 ha hn hodd T hT
  have hP := three_le_q_real hπ h2
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 3 := by obtain ⟨m, rfl⟩ := hodd; exact ⟨m - 1, by omega⟩
  simp only [show 2 * j + 3 - 2 = 2 * j + 1 by omega, show (2 * j + 3 - 3) / 2 = j by omega,
    show (2 * j + 3 - 1) / 2 = j + 1 by omega] at hC ⊢
  have hYj : (1 : ℝ) ≤ (q R : ℝ) ^ j := one_le_pow₀ (by linarith)
  have hY : (q R : ℝ) ^ j * 3 ≤ (q R : ℝ) ^ (2 * j + 1) := by
    rw [show 2 * j + 1 = j + j + 1 by ring, pow_succ, pow_add]; nlinarith
  refine ⟨fun hΦ => ?_, fun hΦ => ?_⟩
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · rw [hΦ] at hC; push_cast at hC
    refine ⟨min_eq_right ?_, ?_⟩
    · rw [hC, div_le_one (by linarith)]; linarith
    · rw [hC]
      have h0 : (q R : ℝ) ≠ 0 := by linarith
      have h1 : (q R : ℝ) ^ (2 * j + 1) - 1 ≠ 0 := by linarith
      have h2 : 1 - 1 / (q R : ℝ) ^ (2 * j + 1) ≠ 0 := by
        have : 1 / (q R : ℝ) ^ (2 * j + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      field_simp
      ring

/-- **$C'_\pi(T')$, $n$ even, $\pi \nmid T'$** (Table 2): $1$ if $\Phi_n(\pi) = 1$, $X/(X+1)$ if $\Phi_n(\pi) = -1$
($X = q^{(n-2)/2}$). -/
theorem localConstC'_diag_even_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 4 ≤ n) (heven : Even n)
    (T : R) (hT : ¬ π ∣ T) :
    (quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = 1 →
      localConstC' (QuadForm.diag a) π T = 1) ∧
    (quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = -1 →
      localConstC' (QuadForm.diag a) π T =
        (q R : ℝ) ^ ((n - 2) / 2) / ((q R : ℝ) ^ ((n - 2) / 2) + 1)) := by
  have hC := table2_even_unit a π hπ h2 ha (by omega) heven T hT
  have hP := three_le_q_real hπ h2
  have hX : (q R : ℝ) ≤ (q R : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  refine ⟨fun hΦ => ?_, fun hΦ => ?_⟩
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC]
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · rw [hΦ] at hC; push_cast at hC
    rw [localConstC', hC, sub_neg_eq_add]
    refine min_eq_right ?_
    rw [div_le_one (by linarith)]; linarith

/-- **$\Phi_n(\pi)$** over $R$ (Hanke 2004, p. 357), for $Q = \langle a_i \rangle$ at $\pi \nmid 2D$. -/
noncomputable def phiN [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (T : R) : ℤ :=
  if Even n then quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i))
  else quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T))

/-- **(5.12), corrected**, over $R$ at non-dyadic $\pi \nmid N$ (Hanke 2004, p. 371): for $\pi^2 \nmid T'$,
$C'_\pi(T') = 1 \iff n = 3$ or $\pi \mid T'$ or $\Phi_n(\pi) = (-1)^n$. See the erratum note at
`LocalDensity.eq_5_12`. -/
@[kb "hanke2004" "(5.12), p. 371 (corrected)"]
theorem eq_5_12 [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (T : R) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC' (QuadForm.diag a) π T = 1 ↔ n = 3 ∨ π ∣ T ∨ phiN a T = (-1) ^ n := by
  by_cases hpT : π ∣ T
  · exact ⟨fun _ => Or.inr (Or.inl hpT), fun _ => localConstC'_diag_ord_one a π hπ h2 ha hn T hpT hT2⟩
  have hP := three_le_q_real hπ h2
  rcases Nat.even_or_odd n with he | ho
  · have hn4 : 4 ≤ n := by obtain ⟨m, rfl⟩ := he; omega
    have hn3 : n ≠ 3 := by omega
    have hpow : ((-1 : ℤ)) ^ n = 1 := he.neg_one_pow
    simp only [phiN, he, ite_true, hpow, hn3, hpT, false_or]
    obtain ⟨h1, h2'⟩ := localConstC'_diag_even_unit a π hπ h2 ha hn4 he T hpT
    rcases quadraticChar_dichotomy (fun h => not_dvd_sign_prod a hπ ha (n / 2)
      ((residue_eq_zero_iff_dvd hπ _).1 h)) with hΦ | hΦ
    · exact ⟨fun _ => hΦ, fun _ => h1 hΦ⟩
    · rw [h2' hΦ, hΦ]
      have hX : (q R : ℝ) ≤ (q R : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
      constructor
      · intro h
        rw [div_eq_one_iff_eq (by linarith)] at h; linarith
      · intro h; exact absurd h (by decide)
  · have hpow : ((-1 : ℤ)) ^ n = -1 := ho.neg_one_pow
    have hne : ¬ Even n := Nat.not_even_iff_odd.2 ho
    simp only [phiN, hne, ite_false, hpow, hpT, false_or]
    obtain ⟨h1, h2'⟩ := localConstC'_diag_odd_unit a π hπ h2 ha hn ho T hpT
    rcases quadraticChar_dichotomy (fun h => not_dvd_sign_prod_mul a hπ ha ((n - 1) / 2) T hpT
      ((residue_eq_zero_iff_dvd hπ _).1 h)) with hΦ | hΦ
    · obtain ⟨h21, h22⟩ := h2' hΦ
      rw [h21, h22, hΦ]
      constructor
      · intro h
        left
        by_contra h3
        have hn5 : 5 ≤ n := by obtain ⟨m, rfl⟩ := ho; omega
        have hB : (q R : ℝ) ^ ((n - 1) / 2) < (q R : ℝ) ^ (n - 2) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
        have hB0 : (0 : ℝ) < (q R : ℝ) ^ ((n - 1) / 2) := by positivity
        rw [div_eq_one_iff_eq] at h
        · have : 1 / (q R : ℝ) ^ (n - 2) < 1 / (q R : ℝ) ^ ((n - 1) / 2) :=
            one_div_lt_one_div_of_lt hB0 hB
          linarith
        · have : 1 / (q R : ℝ) ^ (n - 2) < 1 := by
            rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by linarith) (by omega)
          linarith
      · rintro (h | h)
        · subst h; norm_num
          have : (q R : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
          linarith
        · exact absurd h (by decide)
    · exact ⟨fun _ => Or.inr hΦ, fun _ => h1 hΦ⟩

/-- **$C'_\pi(T') = 1$ for $n = 3$ at good non-dyadic primes** ((5.12); first part of Thm 5.7(a)). -/
@[kb "hanke2004" "(5.12), p. 371 (n = 3)"]
theorem localConstC'_diag_three [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin 3 → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (T : R) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC' (QuadForm.diag a) π T = 1 :=
  (eq_5_12 a π hπ h2 ha le_rfl T hT2).2 (Or.inl rfl)

open Classical in
/-- **Per-place lower bound, $n$ even, non-dyadic $\pi \nmid N$** (as `LocalDensity.localDensity_ge_even`): for $m \ne 0$,
$\beta_\pi(m) \ge (1 - \Phi_n(\pi)q^{-n/2}) \cdot \frac{X-1}{X+1}$ if $\Phi_n(\pi) = -1$ and $\pi \mid m$, and
$\ge 1 - \Phi_n(\pi)q^{-n/2}$ otherwise ($X = q^{(n-2)/2}$; for $n = 4$, $\frac{q-1}{q+1}$). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at p ∤ 2N, n even)"]
theorem localDensity_ge_even [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 4 ≤ n) (heven : Even n)
    (m : R) (hm : m ≠ 0) :
    (1 - ((quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) : ℤ) : ℝ) / (q R : ℝ) ^ (n / 2)) *
        (if quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = -1 ∧ π ∣ m then
          ((q R : ℝ) ^ ((n - 2) / 2) - 1) / ((q R : ℝ) ^ ((n - 2) / 2) + 1) else 1) ≤
      localDensity (QuadForm.diag a) π m := by
  obtain ⟨e, T, rfl, hT2⟩ := exists_pow_sq_mul π hπ m hm
  have hT0 : T ≠ 0 := by rintro rfl; simp at hm
  have h20 := two_ne_zero_of_not_dvd h2
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd' (ha i)) h20
  have hst := isPStable_diag a π hπ h2 ha (by omega) ∅ T
  have h511 := localDensity_pow_sq_ge (QuadForm.diag a) hQ (by omega) π hπ h20 ∅ T hT0 hst e
  have hP := three_le_q_real hπ h2
  have hX : (q R : ℝ) ≤ (q R : ℝ) ^ ((n - 2) / 2) := le_self_pow₀ (by linarith) (by omega)
  have hN : (q R : ℝ) ≤ (q R : ℝ) ^ (n / 2) := le_self_pow₀ (by linarith) (by omega)
  set X := (q R : ℝ) ^ ((n - 2) / 2) with hXdef
  set N2 := (q R : ℝ) ^ (n / 2)
  rcases quadraticChar_dichotomy (fun h => not_dvd_sign_prod a hπ ha (n / 2)
      ((residue_eq_zero_iff_dvd hπ _).1 h)) with hΦ | hΦ
  · have hif : ¬ (quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = -1 ∧ π ∣ π ^ (2 * e) * T) := by
      rw [hΦ]; simp
    rw [if_neg hif, mul_one, hΦ]
    push_cast
    by_cases hpT : π ∣ T
    · rw [localConstC'_diag_ord_one a π hπ h2 ha (by omega) T hpT hT2, one_mul,
        localDensity_diag_even_ord_one a π hπ h2 ha (by omega) heven T hpT hT2, hΦ] at h511
      push_cast at h511
      have h1 : 0 < 1 - 1 / N2 := by
        have : 1 / N2 < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      have h2' : 0 ≤ 1 / X := by positivity
      nlinarith
    · rw [(localConstC'_diag_even_unit a π hπ h2 ha hn heven T hpT).1 hΦ, one_mul,
        localDensity_diag_even_unit a π hπ h2 ha (by omega) heven T hpT, hΦ] at h511
      push_cast at h511
      exact h511
  · have hL : 0 < 1 - ((-1 : ℤ) : ℝ) / N2 := by
      have : 0 < 1 / N2 := by positivity
      push_cast; rw [neg_div]; linarith
    by_cases hpT : π ∣ T
    · have hif : (quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = -1 ∧ π ∣ π ^ (2 * e) * T) :=
        ⟨hΦ, Dvd.dvd.mul_left hpT _⟩
      rw [if_pos hif, hΦ]
      rw [localConstC'_diag_ord_one a π hπ h2 ha (by omega) T hpT hT2, one_mul,
        localDensity_diag_even_ord_one a π hπ h2 ha (by omega) heven T hpT hT2, hΦ] at h511
      refine le_trans ?_ h511
      apply mul_le_mul_of_nonneg_left _ hL.le
      have hX0 : 0 < X := by linarith
      have key : (X - 1) / (X + 1) ≤ 1 + (-1) / X := by
        have e1 : 1 + (-1) / X - (X - 1) / (X + 1) = (X - 1) / (X * (X + 1)) := by
          field_simp; ring
        have : 0 ≤ (X - 1) / (X * (X + 1)) := div_nonneg (by linarith) (by positivity)
        linarith
      rw [← hXdef]; push_cast; exact key
    · rw [(localConstC'_diag_even_unit a π hπ h2 ha hn heven T hpT).2 hΦ,
        localDensity_diag_even_unit a π hπ h2 ha (by omega) heven T hpT, hΦ] at h511
      split_ifs with hif
      · rw [hΦ]
        refine le_trans ?_ h511
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ hL.le
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      · have he : e = 0 := by
          by_contra he
          exact hif ⟨hΦ, Dvd.dvd.mul_right (dvd_pow (dvd_refl _) (by omega)) _⟩
        subst he
        rw [mul_one, hΦ, mul_zero, pow_zero, one_mul,
          localDensity_diag_even_unit a π hπ h2 ha (by omega) heven T hpT, hΦ]

open Classical in
/-- **Per-place lower bound, $n$ odd, non-dyadic $\pi \nmid N$** (as `LocalDensity.localDensity_ge_odd`). -/
@[kb "hanke2004" "Proof of Thm 5.7(a),(c), p. 375 (local factor at p ∤ 2N, n odd)"]
theorem localDensity_ge_odd [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : R)
    (hT0 : T ≠ 0) (hT2 : ¬ π ^ 2 ∣ T) (ν : ℕ) :
    (if π ∣ T then 1 - 1 / (q R : ℝ) ^ (n - 1) else
        1 + ((quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) : ℤ) : ℝ) /
          (q R : ℝ) ^ ((n - 1) / 2)) *
      (if ¬ π ∣ T ∧ quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) = 1 then
        (1 - 1 / (q R : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (q R : ℝ) ^ (n - 2)) else 1) ≤
      localDensity (QuadForm.diag a) π (π ^ (2 * ν) * T) := by
  have h20 := two_ne_zero_of_not_dvd h2
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd' (ha i)) h20
  have hst := isPStable_diag a π hπ h2 ha hn ∅ T
  have h511 := localDensity_pow_sq_ge (QuadForm.diag a) hQ hn π hπ h20 ∅ T hT0 hst ν
  refine le_trans (le_of_eq ?_) h511
  by_cases hpT : π ∣ T
  · simp only [hpT, ite_true, not_true_eq_false, false_and, ite_false, mul_one]
    rw [localConstC'_diag_ord_one a π hπ h2 ha hn T hpT hT2, one_mul,
      localDensity_diag_odd_ord_one a π hπ h2 ha hodd T hpT hT2]
  · simp only [hpT, ite_false, not_false_eq_true, true_and]
    rw [localDensity_diag_odd_unit a π hπ h2 ha hodd T hpT]
    obtain ⟨h1, h2'⟩ := localConstC'_diag_odd_unit a π hπ h2 ha hn hodd T hpT
    rcases quadraticChar_dichotomy (fun h => not_dvd_sign_prod_mul a hπ ha ((n - 1) / 2) T hpT
      ((residue_eq_zero_iff_dvd hπ _).1 h)) with hΦ | hΦ
    · rw [if_pos hΦ, (h2' hΦ).1, (h2' hΦ).2, mul_comm]
    · rw [if_neg (by rw [hΦ]; decide), h1 hΦ, one_mul, mul_one]

/-- **$n = 3$, non-dyadic $\pi \nmid N$:** $\beta_\pi(T'\pi^{2\nu}) \ge \beta_\pi(T')$ (first part of Thm 5.7(a)). -/
@[kb "hanke2004" "Thm 5.7(a), p. 374 (p ∤ 2N, n = 3)"]
theorem localDensity_ge_three [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin 3 → R) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (T : R) (hT0 : T ≠ 0)
    (hT2 : ¬ π ^ 2 ∣ T) (ν : ℕ) :
    localDensity (QuadForm.diag a) π T ≤ localDensity (QuadForm.diag a) π (π ^ (2 * ν) * T) := by
  have h20 := two_ne_zero_of_not_dvd h2
  have hQ := nondegenerate_diag a (fun i => ne_zero_of_not_dvd' (ha i)) h20
  have h := localDensity_pow_sq_ge (QuadForm.diag a) hQ le_rfl π hπ h20 ∅ T hT0
    (isPStable_diag a π hπ h2 ha le_rfl ∅ T) ν
  rwa [localConstC'_diag_three a π hπ h2 ha T hT2, one_mul] at h

end Good

/-! ### Good dyadic primes: even unimodular forms at $\pi \mid 2$, $\pi \nmid N$

$Q = \bigoplus_{i<r}(a_i x_{2i}^2 + b_i x_{2i}x_{2i+1} + c_i x_{2i+1}^2)$ (`pairSumForm`) with all $b_i$ units, $\pi \mid 2$ (any
ramification $e$), $n = 2r \ge 4$, and $\Phi_n(\pi) := \varepsilon$ the Arf sign (`pairArf`), as in `DVRDyadicTable.lean`. -/

section Dyadic

/-- `pairSumForm` with unit $b_i$ at $\pi \mid 2$ is nondegenerate: its Hessian is block diagonal with blocks
$\begin{pmatrix} 2a_i & b_i \\ b_i & 2c_i \end{pmatrix}$ of determinant $4a_ic_i - b_i^2 \equiv -b_i^2 \not\equiv 0 \pmod \pi$. -/
theorem nondegenerate_pairSumForm {r : ℕ} (A : Fin r → R × R × R) {π : R} (hπ : Irreducible π)
    (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) : (pairSumForm A).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  set e : Fin 2 × Fin r ≃ Fin (r * 2) := (Equiv.prodComm _ _).trans finProdFinEquiv
  rw [← Matrix.det_submatrix_equiv_self e]
  have hM : (pairSumForm A).hessian.submatrix e e = Matrix.blockDiagonal
      (fun i => !![2 * (A i).1, (A i).2.1; (A i).2.1, 2 * (A i).2.2]) := by
    ext ⟨j, i⟩ ⟨j', i'⟩
    simp only [Matrix.submatrix_apply, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.blockDiagonal_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
    rw [show finProdFinEquiv (i, j) = pidx i j from rfl, show finProdFinEquiv (i', j') = pidx i' j' from rfl,
      pairSumForm_coeff, pairSumForm_coeff]
    by_cases hii : i = i'
    · subst hii
      fin_cases j <;> fin_cases j' <;> simp <;> ring
    · simp [hii, Ne.symm hii]
  rw [hM, Matrix.det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [Matrix.det_fin_two_of]
  intro h
  apply hb i
  have : π ∣ (A i).2.1 * (A i).2.1 := by
    have e1 : (A i).2.1 * (A i).2.1 = 2 * (A i).1 * (2 * (A i).2.2) := by linear_combination -h
    rw [e1]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 _) _
  exact (hπ.prime.dvd_or_dvd this).elim id id

/-- **Every $T$ is $\pi$-stable** for an even unimodular `pairSumForm` at dyadic $\pi$, $r \ge 2$ (Remark 3.5.1, and
Lemma 3.2 from level 1). -/
theorem isPStable_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 2 ≤ r)
    (S₀ : Finset (Fin (r * 2))) (T : R) : IsPStable (pairSumForm A) S₀ π T := by
  refine ⟨isLocallyRepresentedAt_pairSum A π hπ h2 hb hr T, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk ν hν
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have hG := fun m => repCountGood_add_of_gradBound (pairSumForm A) π hπ (pairSumPairs r) 0
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) m 1 l le_rfl
  have hG' : ∀ m, repCountOf (pairSumForm A) π (1 + l) m (fun x => ¬ IsZeroType π (1 + l) x) =
      q R ^ ((r * 2 - 1) * l) * repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
    intro m
    have := hG m
    rwa [isGoodType_unimodularCoords_zero, isGoodType_unimodularCoords_zero] at this
  rw [hG', hG']
  congr 1
  apply repCountOf_congr
  exact ((mk_pow_one_eq_zero_iff π _).2 (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)).trans
    ((mk_pow_one_eq_zero_iff π _).2 (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)).symm

theorem pairArf_eq [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) :
    pairArf A = 1 ∨ pairArf A = -1 := by
  have := pairArf_sq A; rw [sq] at this; exact mul_self_eq_one_iff.1 this

/-- **Dyadic $C'_\pi(T')$** (Table 2 at dyadic $\pi \nmid N$, $\Phi_n := \varepsilon$): for $\pi^2 \nmid T'$,
$C'_\pi(T') = 1$ if $\pi \mid T'$ or $\varepsilon = 1$, and $C'_\pi(T') = X/(X+1)$, $X = q^{r-1}$, if $\pi \nmid T'$ and
$\varepsilon = -1$. This is **(5.12), corrected**, at dyadic $\pi \nmid N$: $C'_\pi(T') = 1 \iff \pi \mid T'$ or
$\Phi_n(\pi) = (-1)^n = 1$. -/
@[kb "hanke2004" "(5.12), p. 371 (corrected; dyadic, even unimodular)"]
theorem localConstC'_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 2 ≤ r) (T : R)
    (hT2 : ¬ π ^ 2 ∣ T) :
    (π ∣ T → localConstC' (pairSumForm A) π T = 1) ∧
    (¬ π ∣ T → pairArf A = 1 → localConstC' (pairSumForm A) π T = 1) ∧
    (¬ π ∣ T → pairArf A = -1 →
      localConstC' (pairSumForm A) π T = (q R : ℝ) ^ (r - 1) / ((q R : ℝ) ^ (r - 1) + 1)) ∧
    (localConstC' (pairSumForm A) π T = 1 ↔ π ∣ T ∨ pairArf A = 1) := by
  have hq : (2 : ℝ) ≤ q R := by exact_mod_cast two_le_q_of_fintype (R := R)
  have hX : (q R : ℝ) ≤ (q R : ℝ) ^ (r - 1) := le_self_pow₀ (by linarith) (by omega)
  have p1 : ∀ hT1 : π ∣ T, localConstC' (pairSumForm A) π T = 1 := by
    intro hT1
    rw [localConstC', table2_ord_one_pairSum A π hπ h2 hb hr T hT1 hT2]
    have hY : 1 < (q R : ℝ) ^ (r * 2 - 2) := one_lt_pow₀ (by linarith) (by omega)
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  have p2 : ∀ _ : ¬ π ∣ T, pairArf A = 1 → localConstC' (pairSumForm A) π T = 1 := by
    intro hT hε
    rw [localConstC', table2_even_unit_pairSum A π hπ h2 hb hr T hT, hε]
    push_cast
    refine min_eq_left ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  have p3 : ∀ _ : ¬ π ∣ T, pairArf A = -1 →
      localConstC' (pairSumForm A) π T = (q R : ℝ) ^ (r - 1) / ((q R : ℝ) ^ (r - 1) + 1) := by
    intro hT hε
    rw [localConstC', table2_even_unit_pairSum A π hπ h2 hb hr T hT, hε]
    push_cast
    rw [sub_neg_eq_add]
    refine min_eq_right ?_
    rw [div_le_one (by linarith)]; linarith
  refine ⟨p1, p2, p3, ?_⟩
  constructor
  · intro h
    by_cases hT : π ∣ T
    · exact Or.inl hT
    · rcases pairArf_eq A with hε | hε
      · exact Or.inr hε
      · rw [p3 hT hε, div_eq_one_iff_eq (by linarith)] at h; linarith
  · rintro (h | h)
    · exact p1 h
    · by_cases hT : π ∣ T
      · exact p1 hT
      · exact p2 hT h

open Classical in
/-- **Per-place lower bound at a dyadic $\pi \nmid N$** (even unimodular `pairSumForm`, $n = 2r \ge 4$, any $e$): the
even-$n$ bound of `LocalDensity.localDensity_ge_even` with $\Phi_n(\pi) := \varepsilon$ and $X = q^{r-1}$:
$$\beta_\pi(m) \;\ge\; \Big(1 - \frac{\varepsilon}{q^{r}}\Big)\cdot
  \begin{cases} \dfrac{X-1}{X+1} & \varepsilon = -1,\ \pi \mid m,\\ 1 & \text{otherwise.}\end{cases}$$
*Update (candidate generalization; pending author):* the local factors at $\mathfrak p \nmid N$ in the proof of
Thm 5.7(b), (c) (stated there via Table 2, i.e. for $\mathfrak p \nmid 2N$) hold at dyadic $\mathfrak p \nmid N$ too. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at dyadic p ∤ N)"]
theorem localDensity_ge_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R)
    (π : R) (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hb : ∀ i, ¬ π ∣ (A i).2.1)
    (hr : 2 ≤ r) (m : R) (hm : m ≠ 0) :
    (1 - (pairArf A : ℝ) / (q R : ℝ) ^ r) *
        (if pairArf A = -1 ∧ π ∣ m then ((q R : ℝ) ^ (r - 1) - 1) / ((q R : ℝ) ^ (r - 1) + 1) else 1) ≤
      localDensity (pairSumForm A) π m := by
  obtain ⟨e, T, rfl, hT2⟩ := exists_pow_sq_mul π hπ m hm
  have hT0 : T ≠ 0 := by rintro rfl; simp at hm
  have hQ := nondegenerate_pairSumForm A hπ h2 hb
  have hst := isPStable_pairSum A π hπ h2 hb hr ∅ T
  have h511 := localDensity_pow_sq_ge (pairSumForm A) hQ (by omega) π hπ h20 ∅ T hT0 hst e
  obtain ⟨c1, c2, c3, -⟩ := localConstC'_pairSum A π hπ h2 hb hr T hT2
  have hq : (2 : ℝ) ≤ q R := by exact_mod_cast two_le_q_of_fintype (R := R)
  have hX : (q R : ℝ) ≤ (q R : ℝ) ^ (r - 1) := le_self_pow₀ (by linarith) (by omega)
  have hN : (q R : ℝ) ≤ (q R : ℝ) ^ r := le_self_pow₀ (by linarith) (by omega)
  set X := (q R : ℝ) ^ (r - 1) with hXdef
  set N2 := (q R : ℝ) ^ r
  rcases pairArf_eq A with hε | hε
  · have hif : ¬ (pairArf A = -1 ∧ π ∣ π ^ (2 * e) * T) := by rw [hε]; simp
    rw [if_neg hif, mul_one, hε]
    push_cast
    by_cases hpT : π ∣ T
    · rw [c1 hpT, one_mul, localDensity_ord_one_pairSum A π hπ h2 hb (by omega) T hpT hT2, hε] at h511
      push_cast at h511
      have h1 : 0 < 1 - 1 / N2 := by
        have : 1 / N2 < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      have h2' : 0 ≤ 1 / X := by positivity
      nlinarith
    · rw [c2 hpT hε, one_mul, localDensity_unit_pairSum A π hπ h2 hb (by omega) T hpT, hε] at h511
      push_cast at h511
      exact h511
  · have hL : 0 < 1 - ((-1 : ℤ) : ℝ) / N2 := by
      have : 0 < 1 / N2 := by positivity
      push_cast; rw [neg_div]; linarith
    by_cases hpT : π ∣ T
    · rw [if_pos ⟨hε, Dvd.dvd.mul_left hpT _⟩, hε]
      rw [c1 hpT, one_mul, localDensity_ord_one_pairSum A π hπ h2 hb (by omega) T hpT hT2, hε] at h511
      refine le_trans ?_ h511
      apply mul_le_mul_of_nonneg_left _ hL.le
      have hX0 : 0 < X := by linarith
      have key : (X - 1) / (X + 1) ≤ 1 + (-1) / X := by
        have e1 : 1 + (-1) / X - (X - 1) / (X + 1) = (X - 1) / (X * (X + 1)) := by
          field_simp; ring
        have : 0 ≤ (X - 1) / (X * (X + 1)) := div_nonneg (by linarith) (by positivity)
        linarith
      rw [← hXdef]; push_cast; exact key
    · rw [c3 hpT hε, localDensity_unit_pairSum A π hπ h2 hb (by omega) T hpT, hε] at h511
      split_ifs with hif
      · rw [hε]
        refine le_trans ?_ h511
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ hL.le
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      · have he : e = 0 := by
          by_contra he
          exact hif ⟨hε, Dvd.dvd.mul_right (dvd_pow (dvd_refl _) (by omega)) _⟩
        subst he
        rw [mul_one, hε, pow_zero, one_mul,
          localDensity_unit_pairSum A π hπ h2 hb (by omega) T hpT, hε]

end Dyadic

/-! ### Theorem 5.9: the local inequality over $R$ -/

/-- **The local inequality in the proof of Thm 5.9(b)(ii)** over $R$ (as `LocalDensity.thm_5_9_local`; the paper
states Thm 5.9 over $\mathbb{Q}$): for $n = 3$, $T$ $\pi$-stable, $C = C_\pi(T) \ge 1$, $\nu \ge 1$:
$q^\nu\beta_\pi(T\pi^{2\nu})/\beta_\pi(T) = 1 + C(q^\nu - 1)$ and
$1 + C(q^\nu - 1) - q^\nu \ge \frac{(C-1)(q-1)}{q}q^\nu$. -/
@[kb "hanke2004" "Proof of Thm 5.9(b)(ii), p. 379 (local inequality)"]
theorem thm_5_9_local [Finite 𝔽] (Q : QuadForm R 3) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin 3)) (T : R) (hT0 : T ≠ 0)
    (hT : IsPStable Q S₀ π T) (hC : 1 ≤ localConstC Q π T) (ν : ℕ) (hν : 1 ≤ ν) :
    (q R : ℝ) ^ ν * (localDensity Q π (π ^ (2 * ν) * T) / localDensity Q π T) =
        1 + localConstC Q π T * ((q R : ℝ) ^ ν - 1) ∧
      (localConstC Q π T - 1) * ((q R : ℝ) - 1) / q R * (q R : ℝ) ^ ν ≤
        1 + localConstC Q π T * ((q R : ℝ) ^ ν - 1) - (q R : ℝ) ^ ν := by
  have h58 := localDensity_pow_sq_div Q hQ le_rfl π hπ h20 S₀ T hT0 hT ν
  simp only [show 3 - 2 = 1 by rfl, one_mul] at h58
  set C := localConstC Q π T
  have hP : (2 : ℝ) ≤ q R := by exact_mod_cast one_lt_q (R := R)
  have hpν : (q R : ℝ) ^ ν ≠ 0 := pow_ne_zero _ (by linarith)
  refine ⟨?_, ?_⟩
  · rw [h58]; field_simp; ring
  · obtain ⟨μ, rfl⟩ : ∃ μ, ν = μ + 1 := ⟨ν - 1, by omega⟩
    have hμ : (1 : ℝ) ≤ (q R : ℝ) ^ μ := one_le_pow₀ (by linarith)
    have : ((q R : ℝ) - 1) / q R * (q R : ℝ) ^ (μ + 1) = ((q R : ℝ) - 1) * (q R : ℝ) ^ μ := by
      rw [pow_succ]; field_simp
    rw [mul_div_assoc, mul_assoc, this, pow_succ]
    nlinarith

end QuadFormsKB.LocalDensity.DVR
