import QuadFormsKB.Binary.BinaryDensities
import QuadFormsKB.LocalDensity.Reduction

/-!
# Local densities of binary forms at ramified primes, every $m$

For $D$ fundamental, $f$ primitive of discriminant $D$, $p \mid D$ prime ($p = 2$ included) and **every** $m \ne 0$
(`localDensity_ram`):
$$\beta_p(f, m) = 1 + \chi_p(f)\,c_p(m) \in \{0, 2\}, \qquad c_p(m) = \psi_p\big(m_0\,e_p^{\,v}\big)\ (\texttt{ramChar}),$$
with $v = v_p(m)$, $m_0 = m/p^v$ (`pFree`), $\psi_p$ = `genusChar D p`, $\chi_p(f)$ = `formChar f p`, and
$e_p$ = `ramUnit p D`: $-D/p$ for odd $p$; $-D/8$ if $p = 2$, $8 \mid D$; $(1 - D/4)/2$ if $p = 2$, $4 \,\|\, D$. So
$\beta_p(f, m)$ depends on $f$ only through $\chi_p(f)$, and exactly one of the two local classes represents $m$.
`BinaryDensities.lean` did the case $p \nmid m$ ($c_p(m) = \psi_p(m)$).

**Method (local counting).**
* Reduction to a diagonal form by $(x, y) \mapsto (Ax + By, y)$ and a unit scaling (`repCount_transform`):
  $4af = (2ax + by)^2 - Dy^2$ for odd $p \nmid a$; $af = (ax + b'y)^2 - \frac D4y^2$ for $p = 2 \nmid a$, $b = 2b'$.
* For $\langle u, pw\rangle$ ($p \nmid uw$, `rd`): Hanke's type decomposition (Zero / Good / Bad, Def. 3.1) with the maps
  $\pi_Z$ (`repCountZero_eq`) and $\pi_{B'}$ (`repCountBadI_eq`) gives $\beta_p(\langle u, pw\rangle, n) = \beta_p(\langle w, pu\rangle, n/p)$
  for $p \,\|\, n$ and $= \beta_p(\langle u, pw\rangle, n/p^2)$ for $p^2 \mid n$ (`localDensity_rd`); at $p \nmid n$ the value is
  $1 + (\frac{un}{p})$ (odd $p$) or a check mod $8$ ($p = 2$).
* For $p = 2$, $4 \,\|\, D$: $\langle 1, -D/4\rangle$ is unimodular at $2$; a gradient bound of $1$ (`repCountOf_nonZero_add_diag_two`)
  lifts the counts at $n \equiv 2 \bmod 4$ from level $8$, and at $4 \mid n$ only Zero-type solutions exist
  (`localDensity_g0_four`).

Sources: Siegel (1935), §§1–2 [unverified locator]; Hanke (2004), Def. 3.1, maps $\pi_Z$, $\pi_{B'}$, pp. 358–360, and
Lemma 3.2; Yang (1998) for explicit binary densities [unverified locator].
-/

open QuadFormsKB.LocalDensity

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace QuadFormsKB.Binary

open BinQF QuadForm

/-- A diagonal binary form is `BinQF.mk a 0 c`. -/
theorem diag_two_eq_mk (a c : ℤ) : QuadForm.diag ![a, c] = BinQF.mk a 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinQF.mk, QuadForm.ofUpper, QuadForm.diag]

/-- **The ramified diagonal form** $\langle u, p w\rangle$. -/
def rd (p : ℕ) (u w : ℤ) : QuadForm ℤ 2 := QuadForm.diag ![u, p * w]

section Rd

variable {p : ℕ} [hp : Fact p.Prime] {u w : ℤ}

theorem padicValInt_rd_zero (hu : ¬ (p : ℤ) ∣ u) : padicValInt p u = 0 := padicValInt.eq_zero_of_not_dvd hu

theorem padicValInt_rd_one (hw : ¬ (p : ℤ) ∣ w) : padicValInt p ((p : ℤ) * w) = 1 := by
  rw [padicValInt.mul (by exact_mod_cast hp.out.ne_zero) (by rintro rfl; simp at hw),
    padicValInt.eq_zero_of_not_dvd hw]
  simp [padicValInt.self hp.out.one_lt]

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

theorem S₀_rd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) : S₀ ![u, (p : ℤ) * w] p = {0} := by
  have h0 : padicValInt p (![u, (p : ℤ) * w] 0) = 0 := padicValInt_rd_zero hu
  have h1 : padicValInt p (![u, (p : ℤ) * w] 1) = 1 := padicValInt_rd_one hw
  ext i
  rcases fin_two_cases i with rfl | rfl <;>
    simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h0, h1] <;>
    first | decide | skip

theorem S₁_rd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) : S₁ ![u, (p : ℤ) * w] p = {1} := by
  have h0 : padicValInt p (![u, (p : ℤ) * w] 0) = 0 := padicValInt_rd_zero hu
  have h1 : padicValInt p (![u, (p : ℤ) * w] 1) = 1 := padicValInt_rd_one hw
  ext i
  rcases fin_two_cases i with rfl | rfl <;>
    simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h0, h1] <;>
    first | decide | skip

theorem S₂_rd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) : S₂ ![u, (p : ℤ) * w] p = ∅ := by
  have h0 : padicValInt p (![u, (p : ℤ) * w] 0) = 0 := padicValInt_rd_zero hu
  have h1 : padicValInt p (![u, (p : ℤ) * w] 1) = 1 := padicValInt_rd_one hw
  ext i
  rcases fin_two_cases i with rfl | rfl <;>
    simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, h0, h1] <;>
    first | decide | skip

theorem badIForm_rd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) :
    badIForm ![u, (p : ℤ) * w] p = ![(p : ℤ) * u, w] := by
  have h0 : padicValInt p (![u, (p : ℤ) * w] 0) = 0 := padicValInt_rd_zero hu
  have h1 : padicValInt p (![u, (p : ℤ) * w] 1) = 1 := padicValInt_rd_one hw
  funext i
  rcases fin_two_cases i with rfl | rfl
  · simp only [badIForm, h0, ite_true]; rfl
  · simp only [badIForm, h1, one_ne_zero, ite_false]
    simp [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)]

theorem S₀_rd' (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) : S₀ ![(p : ℤ) * u, w] p = {1} := by
  have h0 : padicValInt p (![(p : ℤ) * u, w] 0) = 1 := padicValInt_rd_one hu
  have h1 : padicValInt p (![(p : ℤ) * u, w] 1) = 0 := padicValInt_rd_zero hw
  ext i
  rcases fin_two_cases i with rfl | rfl <;>
    simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h0, h1] <;>
    first | decide | skip

/-- In $\mathbb{Z}/p^k$ ($k \ge 1$): $p \mid y$ iff $y \equiv 0 \pmod p$. -/
theorem zmod_p_dvd_iff {k : ℕ} (hk : 1 ≤ k) (y : ZMod (p ^ k)) :
    (p : ZMod (p ^ k)) ∣ y ↔ ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p) y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩; rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  · intro h
    have hv : (p : ℕ) ∣ y.val := by
      have : ((y.val : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_val]; exact h
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    obtain ⟨c, hc⟩ := hv
    refine ⟨(c : ZMod (p ^ k)), ?_⟩
    rw [← ZMod.natCast_zmod_val y, hc]; push_cast; ring

theorem eval_diag_two {K : Type*} [CommRing K] (a c : ℤ) (x : Fin 2 → K) :
    (QuadForm.diag ![a, c]).evalIn K x = (a : K) * x 0 ^ 2 + (c : K) * x 1 ^ 2 := by
  rw [diag_two_eq_mk, evalIn_bin]; simp

/-- **The reduction for $\langle u, pw\rangle$ at $p \mid n$** ($p \nmid uw$, $k \ge 2$): Zero type gives
$p^2 r_{p^{k-2}}(n/p^2)$ (if $p^2 \mid n$), Good type is empty, and Bad type is Hanke's type I, giving
$p\, r^{\mathrm{Good}}_{p^{k-1}}(\langle pu, w\rangle, n/p)$ (map $\pi_{B'}$). -/
theorem repCount_rd_dvd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) (n : ℤ) (hn : (p : ℤ) ∣ n) (k : ℕ)
    (hk : 2 ≤ k) :
    repCount (rd p u w) p k n = (if (p : ℤ) ^ 2 ∣ n then p ^ 2 * repCount (rd p u w) p (k - 2) (n / p ^ 2) else 0) +
      p * repCountOf (QuadForm.diag ![(p : ℤ) * u, w]) p (k - 1) (n / p)
        (IsGoodType (S₀ ![(p : ℤ) * u, w] p) p (k - 1)) := by
  have hpp := hp.out
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have ha : ∀ i, ![u, (p : ℤ) * w] i ≠ 0 := by
    intro i; rcases fin_two_cases i with rfl | rfl
    · simpa using hu0
    · simpa using mul_ne_zero (show (p : ℤ) ≠ 0 by exact_mod_cast hpp.ne_zero) hw0
  unfold rd
  rw [repCount_eq_add_types _ (S₀ ![u, (p : ℤ) * w] p) p k n, repCountZero_eq _ p n k hk]
  have hgood : repCountOf (QuadForm.diag ![u, (p : ℤ) * w]) p k n (IsGoodType (S₀ ![u, (p : ℤ) * w] p) p k) = 0 := by
    unfold repCountOf
    rw [Nat.card_eq_zero]; left; constructor
    rintro ⟨x, hx, -, i, hi, hxi⟩
    rw [S₀_rd hu hw, Finset.mem_singleton] at hi
    subst hi
    apply hxi
    rw [zmod_p_dvd_iff (by omega)]
    have hcast := congrArg (ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)) hx
    rw [eval_diag_two] at hcast
    simp only [map_add, map_mul, map_pow, map_intCast] at hcast
    have hn' : ((n : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr hn
    have hp' : (((p : ℤ) * w : ℤ) : ZMod p) = 0 := by push_cast; simp
    rw [hn', hp', zero_mul, add_zero] at hcast
    have hu' : ((u : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hcast).resolve_left hu')
  have hbad : repCountOf (QuadForm.diag ![u, (p : ℤ) * w]) p k n (IsBadType (S₀ ![u, (p : ℤ) * w] p) p k) =
      repCountOf (QuadForm.diag ![u, (p : ℤ) * w]) p k n
        (fun x => IsBadType (S₀ ![u, (p : ℤ) * w] p) p k x ∧ ∃ i ∈ S₁ ![u, (p : ℤ) * w] p,
          ¬ (p : ZMod (p ^ k)) ∣ x i) := by
    unfold repCountOf
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    refine and_congr Iff.rfl ⟨fun hb => ⟨hb, ?_⟩, fun h => h.1⟩
    obtain ⟨hz, hng⟩ := hb
    rw [S₁_rd hu hw]
    simp only [IsZeroType, not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    rcases fin_two_cases i with rfl | rfl
    · exact absurd ⟨fun h => hi (h 0), 0, by rw [S₀_rd hu hw]; simp, hi⟩ hng
    · exact ⟨1, by simp, hi⟩
  rw [hgood, hbad, repCountBadI_eq _ ha p n k hk hn, S₁_rd hu hw, S₂_rd hu hw, badIForm_rd hu hw]
  simp

/-- Good-type counts of $\langle pu, w\rangle$: all solutions when $p \nmid n$. -/
theorem repCountGood_rd'_unit (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) (K : ℕ)
    (hK : 1 ≤ K) :
    repCountOf (QuadForm.diag ![(p : ℤ) * u, w]) p K n (IsGoodType (S₀ ![(p : ℤ) * u, w] p) p K) =
      repCount (QuadForm.diag ![(p : ℤ) * u, w]) p K n := by
  rw [repCount_eq_add_types _ (S₀ ![(p : ℤ) * u, w] p) p K n, repCountBad_eq_zero _ p n K hK hn]
  have hz : repCountOf (QuadForm.diag ![(p : ℤ) * u, w]) p K n (IsZeroType p K) = 0 := by
    unfold repCountOf
    rw [Nat.card_eq_zero]; left; constructor
    rintro ⟨x, hx, hz⟩
    apply hn
    have h0 := (zmod_p_dvd_iff hK (x 0)).mp (hz 0)
    have h1 := (zmod_p_dvd_iff hK (x 1)).mp (hz 1)
    have hcast := congrArg (ZMod.castHom (dvd_pow_self p (by omega : K ≠ 0)) (ZMod p)) hx
    rw [eval_diag_two] at hcast
    simp only [map_add, map_mul, map_pow, map_intCast, h0, h1] at hcast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [← hcast]; ring
  rw [hz]; ring

/-- Good-type counts of $\langle pu, w\rangle$ vanish when $p \mid n$. -/
theorem repCountGood_rd'_dvd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) (n : ℤ) (hn : (p : ℤ) ∣ n) (K : ℕ)
    (hK : 1 ≤ K) :
    repCountOf (QuadForm.diag ![(p : ℤ) * u, w]) p K n (IsGoodType (S₀ ![(p : ℤ) * u, w] p) p K) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left; constructor
  rintro ⟨x, hx, -, i, hi, hxi⟩
  rw [S₀_rd' hu hw, Finset.mem_singleton] at hi
  subst hi
  apply hxi
  rw [zmod_p_dvd_iff hK]
  have hcast := congrArg (ZMod.castHom (dvd_pow_self p (by omega : K ≠ 0)) (ZMod p)) hx
  rw [eval_diag_two] at hcast
  simp only [map_add, map_mul, map_pow, map_intCast] at hcast
  have hn' : ((n : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr hn
  have hp' : (((p : ℤ) * u : ℤ) : ZMod p) = 0 := by push_cast; simp
  rw [hn', hp', zero_mul, zero_add] at hcast
  have hw' : ((w : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hcast).resolve_left hw')

theorem rd_eq_mk : rd p u w = BinQF.mk u 0 ((p : ℤ) * w) := diag_two_eq_mk _ _

theorem repCount_diag_swap (k : ℕ) (n : ℤ) :
    repCount (QuadForm.diag ![(p : ℤ) * u, w]) p k n = repCount (rd p w u) p k n := by
  have : swapF (BinQF.mk w 0 ((p : ℤ) * u)) = BinQF.mk ((p : ℤ) * u) 0 w := by
    unfold swapF; rw [a_mk, b_mk, c_mk]
  rw [rd_eq_mk, diag_two_eq_mk, ← this, repCount_swapF]

theorem rd_nondegenerate (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) : (rd p u w).Nondegenerate := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  unfold QuadForm.Nondegenerate
  rw [rd_eq_mk, hessian_det_two]
  simp only [BinQF.mk, QuadForm.ofUpper, Matrix.of_apply]
  simp [hu0, hw0, hp.out.ne_zero]

/-- **$\beta_p(\langle u, pw\rangle, n) = \beta_p(\langle w, pu\rangle, n/p)$ when $p \,\|\, n$.** -/
theorem localDensity_rd_dvd_one (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) (n : ℤ) (hn0 : n ≠ 0)
    (hn : (p : ℤ) ∣ n) (hn2 : ¬ (p : ℤ) ^ 2 ∣ n) :
    localDensity (rd p u w) p n = localDensity (rd p w u) p (n / p) := by
  have hpp := hp.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hnp0 : n / p ≠ 0 := by
    obtain ⟨c, rfl⟩ := hn
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hpp.ne_zero)]; rintro rfl; simp at hn0
  have hnp : ¬ (p : ℤ) ∣ n / p := by
    rintro ⟨c, hc⟩; apply hn2
    obtain ⟨d, rfl⟩ := hn
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hpp.ne_zero)] at hc
    exact ⟨c, by rw [hc]; ring⟩
  have hev := localDensity_eventually_eq (rd p w u) (rd_nondegenerate hw hu) p (n / p) hnp0
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  apply limUnder_eq_of_eventually
  rw [Filter.eventually_atTop]
  refine ⟨J + 2, fun k hk => ?_⟩
  rw [repCount_rd_dvd hu hw n hn k (by omega), ite_eq_right hn2, zero_add,
    repCountGood_rd'_unit (n / p) hnp (k - 1) (by omega), repCount_diag_swap, ← hJ (k - 1) (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, show (j + 1) * (2 - 1) = j + 1 by omega, show j * (2 - 1) = j by omega]
  push_cast
  rw [pow_succ]
  field_simp

/-- **$\beta_p(\langle u, pw\rangle, n) = \beta_p(\langle u, pw\rangle, n/p^2)$ when $p^2 \mid n$.** -/
theorem localDensity_rd_dvd_two (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) (n : ℤ) (hn0 : n ≠ 0)
    (hn2 : (p : ℤ) ^ 2 ∣ n) :
    localDensity (rd p u w) p n = localDensity (rd p u w) p (n / p ^ 2) := by
  have hpp := hp.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hn : (p : ℤ) ∣ n := (dvd_pow_self _ two_ne_zero).trans hn2
  have hnp0 : n / p ^ 2 ≠ 0 := by
    obtain ⟨c, rfl⟩ := hn2
    rw [Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero))]; rintro rfl; simp at hn0
  have hnp : (p : ℤ) ∣ n / p := by
    obtain ⟨c, rfl⟩ := hn2
    rw [pow_two, mul_assoc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hpp.ne_zero)]
    exact dvd_mul_right _ _
  have hev := localDensity_eventually_eq (rd p u w) (rd_nondegenerate hu hw) p (n / p ^ 2) hnp0
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  apply limUnder_eq_of_eventually
  rw [Filter.eventually_atTop]
  refine ⟨J + 2, fun k hk => ?_⟩
  rw [repCount_rd_dvd hu hw n hn k (by omega), ite_eq_left hn2,
    repCountGood_rd'_dvd hu hw (n / p) hnp (k - 1) (by omega), mul_zero, add_zero, ← hJ (k - 2) (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 2 = j by omega, show (j + 2) * (2 - 1) = j + 2 by omega, show j * (2 - 1) = j by omega]
  push_cast
  rw [pow_add]
  field_simp

/-- The $p$-free part $n/p^{v_p(n)}$ of an integer. -/
def pFree (p : ℕ) (n : ℤ) : ℤ := n / (p : ℤ) ^ (n.natAbs.factorization p)

theorem pFree_not_dvd {n : ℤ} (hn : n ≠ 0) : ¬ (p : ℤ) ∣ pFree p n := by
  unfold pFree
  set v := n.natAbs.factorization p with hv
  have hpow : (p : ℤ) ^ v ∣ n := by
    have := Int.natCast_dvd.mpr (Nat.ordProj_dvd n.natAbs p)
    push_cast at this; exact this
  obtain ⟨c, hc⟩ := hpow
  have hdiv : n / (p : ℤ) ^ v = c := by
    rw [hc, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))]
  rw [hdiv]
  rintro ⟨d, rfl⟩
  have : ((p ^ (v + 1) : ℕ) : ℤ) ∣ n := ⟨d, by push_cast; rw [hc]; ring⟩
  exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hn) hp.out (Int.natCast_dvd.mp this)

theorem pFree_of_not_dvd {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : pFree p n = n := by
  unfold pFree
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hn (int_dvd_iff_natAbs.mpr h))]; simp

theorem factorization_div_p {n : ℤ} (hn0 : n ≠ 0) (hn : (p : ℤ) ∣ n) :
    n.natAbs.factorization p = (n / p).natAbs.factorization p + 1 := by
  obtain ⟨c, rfl⟩ := hn
  have hc : c ≠ 0 := by rintro rfl; simp at hn0
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.out.ne_zero), Int.natAbs_mul, Int.natAbs_natCast,
    Nat.factorization_mul hp.out.ne_zero (Int.natAbs_ne_zero.mpr hc), Finsupp.add_apply,
    hp.out.factorization_self]
  ring

theorem pFree_div_p {n : ℤ} (hn0 : n ≠ 0) (hn : (p : ℤ) ∣ n) : pFree p (n / p) = pFree p n := by
  unfold pFree
  rw [factorization_div_p hn0 hn, pow_succ', Int.ediv_ediv_of_nonneg (by positivity)]

/-- **$\beta_p$ of $\langle u, pw\rangle$ for every $n \ne 0$:** with $v = v_p(n)$ and $n_0 = n/p^v$,
$\beta_p(\langle u, pw\rangle, n) = \beta_p(\langle u, pw\rangle, n_0)$ for $v$ even and $\beta_p(\langle w, pu\rangle, n_0)$ for $v$ odd. -/
@[kb "hanke2004" "§3, maps π_Z, π_{B'}, pp. 359–360 (binary ⟨u, pw⟩)"]
theorem localDensity_rd (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w) :
    ∀ N : ℕ, ∀ n : ℤ, n.natAbs = N → n ≠ 0 →
      localDensity (rd p u w) p n = if Even (n.natAbs.factorization p) then
        localDensity (rd p u w) p (pFree p n) else localDensity (rd p w u) p (pFree p n) := by
  intro N
  induction N using Nat.strong_induction_on generalizing u w with
  | _ N ih =>
  intro n hN hn0
  have hpp := hp.out
  by_cases hn : (p : ℤ) ∣ n
  · by_cases hn2 : (p : ℤ) ^ 2 ∣ n
    · have hnp : (p : ℤ) ∣ n / p := by
        obtain ⟨c, rfl⟩ := hn2
        rw [pow_two, mul_assoc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hpp.ne_zero)]
        exact dvd_mul_right _ _
      have hn20 : n / p ^ 2 ≠ 0 := by
        obtain ⟨c, rfl⟩ := hn2
        rw [Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero))]; rintro rfl; simp at hn0
      have hdiv : n / p ^ 2 = n / p / p := by
        rw [pow_two, Int.ediv_ediv_of_nonneg (by positivity)]
      have hnp0 : n / p ≠ 0 := by rw [hdiv] at hn20; rintro h; rw [h] at hn20; simp at hn20
      have hlt : (n / p ^ 2).natAbs < N := by
        rw [← hN]
        obtain ⟨c, rfl⟩ := hn2
        rw [Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)), Int.natAbs_mul]
        have hc : c ≠ 0 := by rintro rfl; simp at hn0
        have : 1 < ((p : ℤ) ^ 2).natAbs := by
          rw [Int.natAbs_pow, Int.natAbs_natCast]; exact Nat.one_lt_pow (by norm_num) hpp.one_lt
        have : 0 < c.natAbs := Int.natAbs_pos.mpr hc
        nlinarith
      rw [localDensity_rd_dvd_two hu hw n hn0 hn2, ih _ hlt hu hw (n / p ^ 2) rfl hn20,
        hdiv, factorization_div_p hn0 hn, factorization_div_p hnp0 hnp,
        ← pFree_div_p hn0 hn, ← pFree_div_p hnp0 hnp]
      simp [Nat.even_add_one]
    · have hnp : ¬ (p : ℤ) ∣ n / p := by
        rintro ⟨c, hc⟩; apply hn2
        obtain ⟨d, rfl⟩ := hn
        rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hpp.ne_zero)] at hc
        exact ⟨c, by rw [hc]; ring⟩
      have hnp0 : n / p ≠ 0 := by rintro h; rw [h] at hnp; simp at hnp
      rw [localDensity_rd_dvd_one hu hw n hn0 hn hn2, factorization_div_p hn0 hn, ← pFree_div_p hn0 hn,
        pFree_of_not_dvd hnp, Nat.factorization_eq_zero_of_not_dvd (fun h => hnp (int_dvd_iff_natAbs.mpr h))]
      simp
  · rw [pFree_of_not_dvd hn, Nat.factorization_eq_zero_of_not_dvd (fun h => hn (int_dvd_iff_natAbs.mpr h))]
    simp

end Rd

/-- An integer prime to $p$ is a unit mod $p^k$. -/
theorem isUnit_intCast_zmod_pow {p : ℕ} [hp : Fact p.Prime] (k : ℕ) {a : ℤ} (h : ¬ (p : ℤ) ∣ a) :
    IsUnit (a : ZMod (p ^ k)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  push_cast
  exact (((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd).mpr h).pow_left

/-- **Counts are preserved by $(x, y) \mapsto (Ax + By, y)$ and scaling by a unit:** if
$g(Ax + By, y) = c\,f(x, y)$ over $\mathbb{Z}/N$ with $A, c$ units, then $r_N(f, m) = r_N(g, cm)$ ($N = p^k$). -/
@[kb "cox2013" "§2 (completing the square) [unverified locator]"]
theorem repCount_transform (f g : QuadForm ℤ 2) (p k : ℕ) (A B c : ℤ)
    (hA : IsUnit (A : ZMod (p ^ k))) (hc : IsUnit (c : ZMod (p ^ k)))
    (hid : ∀ x : Fin 2 → ZMod (p ^ k),
      g.evalIn _ ![(A : ZMod (p ^ k)) * x 0 + (B : ZMod (p ^ k)) * x 1, x 1] = (c : ZMod (p ^ k)) * f.evalIn _ x)
    (m : ℤ) : repCount f p k m = repCount g p k (c * m) := by
  set A' : ZMod (p ^ k) := (A : ZMod (p ^ k))
  set B' : ZMod (p ^ k) := (B : ZMod (p ^ k))
  let φ : (Fin 2 → ZMod (p ^ k)) ≃ (Fin 2 → ZMod (p ^ k)) :=
    { toFun := fun v => ![A' * v 0 + B' * v 1, v 1]
      invFun := fun w => ![(hA.unit⁻¹ : (ZMod (p ^ k))ˣ) * (w 0 - B' * w 1), w 1]
      left_inv := fun v => by
        funext i; rcases fin_two_cases i with rfl | rfl
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [add_sub_cancel_right, ← mul_assoc]
          have : ((hA.unit⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * A' = 1 := hA.val_inv_mul
          rw [this, one_mul]
        · simp
      right_inv := fun w => by
        funext i; rcases fin_two_cases i with rfl | rfl
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← mul_assoc]
          have : A' * ((hA.unit⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = 1 := hA.mul_val_inv
          rw [this, one_mul, sub_add_cancel]
        · simp }
  refine Nat.card_congr (φ.subtypeEquiv fun v => ?_)
  show _ ↔ g.evalIn _ ![A' * v 0 + B' * v 1, v 1] = _
  rw [hid v, Int.cast_mul]
  exact (hc.mul_right_inj).symm

/-- Equal counts give equal densities. -/
theorem localDensity_eq_of_repCount {Q Q' : QuadForm ℤ 2} {p : ℕ} {m m' : ℤ}
    (h : ∀ k, repCount Q p k m = repCount Q' p k m') : localDensity Q p m = localDensity Q' p m' := by
  unfold localDensity; simp_rw [h]

section Ram

variable {p : ℕ} [hp : Fact p.Prime]

theorem factorization_mul_unit {c m : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hm : m ≠ 0) :
    (c * m).natAbs.factorization p = m.natAbs.factorization p := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  rw [Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.mpr hc0) (Int.natAbs_ne_zero.mpr hm),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h => hc (int_dvd_iff_natAbs.mpr h)), zero_add]

theorem pFree_mul_unit {c m : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hm : m ≠ 0) : pFree p (c * m) = c * pFree p m := by
  unfold pFree
  rw [factorization_mul_unit hc hm]
  have hpow : (p : ℤ) ^ (m.natAbs.factorization p) ∣ m := by
    have := Int.natCast_dvd.mpr (Nat.ordProj_dvd m.natAbs p)
    push_cast at this; exact this
  exact Int.mul_ediv_assoc c hpow

theorem pFree_ne_zero {m : ℤ} (hm : m ≠ 0) : pFree p m ≠ 0 := by
  intro h; have := pFree_not_dvd (p := p) hm; rw [h] at this; simp at this

/-- $\beta_p(\langle u, pw\rangle, n) = 1 + \left(\frac{un}{p}\right)$ for odd $p \nmid unw$. -/
theorem localDensity_rd_unit_odd (hp2 : p ≠ 2) {u w : ℤ} (hu : ¬ (p : ℤ) ∣ u) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    localDensity (rd p u w) p n = 1 + legendreSym p (u * n) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : 2 * eTwo p + 1 = 1 := by simp [eTwo, hp2]
  have hlift : ∀ l, repCount (rd p u w) p (1 + l) n = p ^ l * repCount (rd p u w) p 1 n := by
    intro l
    have := repCount_unit_add (rd p u w) p n hn (2 * eTwo p + 1) l le_rfl
    rw [he, show (2 - 1) * l = l by omega] at this; exact this
  rw [localDensity_eq_of_lift _ p n 1 hlift, rd_eq_mk]
  have hc := repCount_one_ram (BinQF.mk u 0 ((p : ℤ) * w)) p hp2
    (by simp only [BinQF.disc, a_mk, b_mk, c_mk]; exact ⟨-(4 * u * w), by ring⟩) (by simpa using hu) n
  simp only [a_mk] at hc
  have hc' : (repCount (BinQF.mk u 0 ((p : ℤ) * w)) p 1 n : ℝ) = p * (1 + legendreSym p (u * n)) := by
    exact_mod_cast hc
  rw [hc', pow_one]; field_simp

/-- **The ramified character value at odd $p$:** $c_p(m) = \left(\frac{m_0}{p}\right)\left(\frac{-D/p}{p}\right)^{v}$, $v = v_p(m)$,
$m_0 = m/p^v$. -/
def ramCharOdd (p : ℕ) [Fact p.Prime] (D m : ℤ) : ℤ :=
  legendreSym p (pFree p m) * (if Even (m.natAbs.factorization p) then 1 else legendreSym p (-(D / p)))

/-- **$\beta_p(f, m)$ at an odd ramified prime, every $m \ne 0$** ($f$ primitive of fundamental discriminant $D$,
$p \mid D$ odd): with $v = v_p(m)$, $m_0 = m/p^v$,
$$\beta_p(m) = 1 + \chi_p(f)\,c_p(m), \qquad c_p(m) = \Big(\frac{m_0}{p}\Big)\Big(\frac{-D/p}{p}\Big)^{v},$$
so $\beta_p(m) \in \{0, 2\}$ and depends on $f$ only through $\chi_p(f)$. (Reduction $4af = (2ax + by)^2 - Dy^2$ to
$\langle 1, p\cdot(-D/p)\rangle$, then the recursion `localDensity_rd`.) -/
@[kb "siegel1935" "§§1–2 (odd p | D) [unverified locator]"]
theorem localDensity_ram_odd {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) {m : ℤ} (hm : m ≠ 0) :
    localDensity f p m = 1 + (formChar f p : ℝ) * (ramCharOdd p D m : ℝ) := by
  have hpp := hp.out
  set w : ℤ := -(D / p) with hwdef
  have hDw : D = (p : ℤ) * -w := by rw [hwdef, neg_neg]; exact (Int.mul_ediv_cancel' hpD).symm
  have hw : ¬ (p : ℤ) ∣ w := by
    rintro ⟨c, hc⟩
    apply odd_prime_sq_not_dvd (D := D) hpp hp2
    exact ⟨-c, by rw [hDw, hc]; ring⟩
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (by exact_mod_cast h))
  have h1 : ¬ (p : ℤ) ∣ 1 := by
    intro h; exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  -- the core, for forms with p ∤ a
  suffices H : ∀ g : BinQF, g.disc = D → ¬ (p : ℤ) ∣ g.a →
      localDensity g p m = 1 + (legendreSym p g.a : ℝ) * (ramCharOdd p D m : ℝ) by
    have hr := not_dvd_charCoeff hf hpp (by rw [hD]; exact hpD)
    have hfc : formChar f p = legendreSym p (charCoeff f p) := by
      rw [formChar, genusChar, ite_eq_right hp2, jacobiSym.legendreSym.to_jacobiSym]
    rw [hfc]
    by_cases ha : (p : ℤ) ∣ f.a
    · have hcf : charCoeff f p = f.c := by simp [charCoeff, ha]
      rw [hcf] at hr ⊢
      rw [show localDensity f p m = localDensity (swapF f) p m from
        localDensity_eq_of_repCount fun k => (repCount_swapF f p k m).symm]
      have := H (swapF f) (by rw [disc_swapF, hD]) (by simpa using hr)
      rwa [swapF_a] at this
    · have hcf : charCoeff f p = f.a := by simp [charCoeff, ha]
      rw [hcf]; exact H f hD ha
  intro g hgD ha
  have h4a : ¬ (p : ℤ) ∣ 4 * g.a := by
    intro h
    rcases int_prime_dvd_mul hpp h with h | h
    · rw [show (4 : ℤ) = 2 * 2 by norm_num] at h
      exact h2 ((int_prime_dvd_mul hpp h).elim id id)
    · exact ha h
  have hcount : ∀ k, repCount g p k m = repCount (rd p 1 w) p k (4 * g.a * m) := by
    intro k
    refine repCount_transform g (rd p 1 w) p k (2 * g.a) g.b (4 * g.a)
      (isUnit_intCast_zmod_pow k (fun h => (int_prime_dvd_mul hpp h).elim h2 ha))
      (isUnit_intCast_zmod_pow k h4a) (fun x => ?_) m
    rw [rd, eval_diag_two, evalIn_bin]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have : (p : ℤ) * w = -(g.b ^ 2 - 4 * g.a * g.c) := by
      have h' := hgD; rw [BinQF.disc, hDw] at h'; rw [h']; ring
    have hd : (((p : ℤ) * w : ℤ) : ZMod (p ^ k)) = -((g.b ^ 2 - 4 * g.a * g.c : ℤ) : ZMod (p ^ k)) := by
      rw [this]; push_cast; ring
    rw [hd]; push_cast; ring
  have hm4 : 4 * g.a * m ≠ 0 := mul_ne_zero (by rintro h; rw [h] at h4a; simp at h4a) hm
  rw [localDensity_eq_of_repCount hcount, localDensity_rd h1 hw _ _ rfl hm4,
    factorization_mul_unit h4a hm, pFree_mul_unit h4a hm]
  have hm0 := pFree_not_dvd (p := p) hm
  have hn0 : ¬ (p : ℤ) ∣ 4 * g.a * pFree p m := fun h => (int_prime_dvd_mul hpp h).elim h4a hm0
  have hL4 : legendreSym p 4 = 1 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact legendreSym.sq_one' p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])
  unfold ramCharOdd
  split_ifs with hv
  · rw [localDensity_rd_unit_odd hp2 h1 _ hn0, one_mul, legendreSym.mul, legendreSym.mul, hL4]
    push_cast; ring
  · rw [localDensity_rd_unit_odd hp2 hw _ hn0, legendreSym.mul, legendreSym.mul, legendreSym.mul, hL4]
    push_cast; ring

end Ram

/-! ### $p = 2$: the counts mod 8 -/

theorem card8_rd2 : ∀ u ∈ ({1, 3, 5, 7} : Finset (ZMod 8)), ∀ w ∈ ({1, 3, 5, 7} : Finset (ZMod 8)),
    ∀ n ∈ ({1, 3, 5, 7} : Finset (ZMod 8)),
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun v => u * v.1 ^ 2 + 2 * w * v.2 ^ 2 = n).card : ℤ) =
      8 * (1 + if u * w = 3 ∨ u * w = 7 then ZMod.χ₈ (u * n) else ZMod.χ₈' (u * n)) := by decide

theorem card8_unimod_two : ∀ d ∈ ({3, 7} : Finset (ZMod 8)), ∀ n ∈ ({1, 3, 5, 7} : Finset (ZMod 8)),
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun v => v.1 ^ 2 - d * v.2 ^ 2 = 2 * n).card : ℤ) =
      8 * (1 + ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) (n * (if d = 3 then 7 else 5)))) := by
  decide

theorem zmod4_unimod_two : ∀ d ∈ ({3} : Finset (ZMod 4)), ∀ X Y : ZMod 4, X ^ 2 - d * Y ^ 2 = 0 →
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) X = 0 ∧ ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) Y = 0 := by
  decide

theorem mem_odd8 {n : ℤ} (h : ¬ (2 : ℤ) ∣ n) : (n : ZMod 8) ∈ ({1, 3, 5, 7} : Finset (ZMod 8)) := by
  rcases odd_zmod8 h with h | h | h | h <;> rw [h] <;> decide

/-- **$\beta_2(\langle u, 2w\rangle, n)$ for odd $u, w, n$:** $1 + \psi(un)$ with $\psi = \chi_8$ if $uw \equiv 3 \pmod 4$
and $\psi = \chi_{-8}$ (`ZMod.χ₈'`) if $uw \equiv 1 \pmod 4$ (level $8$, a check over $(\mathbb{Z}/8)^2$). -/
theorem localDensity_rd_unit_two {u w : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hw : ¬ (2 : ℤ) ∣ w) (n : ℤ)
    (hn : ¬ (2 : ℤ) ∣ n) :
    localDensity (rd 2 u w) 2 n = 1 + ((if (u : ZMod 8) * (w : ZMod 8) = 3 ∨ (u : ZMod 8) * (w : ZMod 8) = 7
      then ZMod.χ₈ ((u : ZMod 8) * (n : ZMod 8)) else ZMod.χ₈' ((u : ZMod 8) * (n : ZMod 8)) : ℤ) : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlift : ∀ l, repCount (rd 2 u w) 2 (3 + l) n = 2 ^ l * repCount (rd 2 u w) 2 3 n := by
    intro l
    have := repCount_unit_add (rd 2 u w) 2 n (by exact_mod_cast hn) (2 * eTwo 2 + 1) l le_rfl
    rw [show 2 * eTwo 2 + 1 = 3 from rfl, show (2 - 1) * l = l by omega] at this; exact this
  rw [localDensity_eq_of_lift _ 2 n 3 hlift, rd_eq_mk, repCount_eq_card _ 2 3 8 (by norm_num) n]
  simp only [a_mk, b_mk, c_mk, Int.cast_zero, zero_mul, add_zero]
  rw [card8_aux (fun v => (u : ZMod 8) * v.1 ^ 2 + ((((2 : ℕ) : ℤ) * w : ℤ) : ZMod 8) * v.2 ^ 2 = (n : ZMod 8))]
  have key := card8_rd2 _ (mem_odd8 hu) _ (mem_odd8 hw) _ (mem_odd8 hn)
  have e : ((((2 : ℕ) : ℤ) * w : ℤ) : ZMod 8) = 2 * (w : ZMod 8) := by push_cast; ring
  simp only [e]
  have key' := congrArg (fun z : ℤ => (z : ℝ)) key
  push_cast at key'
  rw [key']
  split_ifs <;> push_cast <;> ring

/-! ### The ramified character $c_p(m)$ -/

/-- **The unit $e_p$ attached to a ramified prime $p \mid D$:** $-D/p$ for odd $p$; for $p = 2$, $-D/8$ if
$8 \mid D$ and $(1 - D/4)/2$ if $4 \,\|\, D$. -/
def ramUnit (p : ℕ) (D : ℤ) : ℤ :=
  if p = 2 then (if (8 : ℤ) ∣ D then -(D / 8) else (1 - D / 4) / 2) else -(D / p)

/-- **The ramified character value** $c_p(m) = \psi_p\big(m_0\,e_p^{\,v}\big)$, $v = v_p(m)$, $m_0 = m/p^v$ (only the parity
of $v$ matters). For $p \mid D$: $\beta_p(f, m) = 1 + \chi_p(f)\,c_p(m)$ (`localDensity_ram`). -/
def ramChar (p : ℕ) (D m : ℤ) : ℤ :=
  genusChar D p (pFree p m * (if Even (m.natAbs.factorization p) then 1 else ramUnit p D))

theorem ramChar_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (D m : ℤ) : ramChar p D m = ramCharOdd p D m := by
  unfold ramChar ramCharOdd ramUnit
  rw [genusChar, ite_eq_right hp2, ite_eq_right hp2, jacobiSym.mul_left,
    ← jacobiSym.legendreSym.to_jacobiSym]
  split_ifs
  · simp [jacobiSym.one_left]
  · congr 1; exact (jacobiSym.legendreSym.to_jacobiSym p _).symm

/-- $\psi_2$ for $8 \mid D$: $\chi_8$ if $-D/8 \equiv 3 \pmod 4$ ($D \equiv 8 \bmod 32$), $\chi_{-8}$ otherwise. -/
theorem genusChar_two_of_eight {D : ℤ} [IsQuadDisc D] (h8 : (8 : ℤ) ∣ D) (z : ℤ) :
    genusChar D 2 z = if ((-(D / 8) : ℤ) : ZMod 8) = 3 ∨ ((-(D / 8) : ℤ) : ZMod 8) = 7
      then ZMod.χ₈ (z : ZMod 8) else ZMod.χ₈' (z : ZMod 8) := by
  have hc := fund_cases (D := D)
  rw [genusChar_two_eq]
  rcases (show D % 32 = 8 ∨ D % 32 = 24 by omega) with h | h
  · rw [ite_eq_left h]
    rcases (show -(D / 8) % 8 = 3 ∨ -(D / 8) % 8 = 7 by omega) with h' | h'
    · rw [zmod8_cast_eq_of_emod (r := 3) h', ite_eq_left (by decide)]
    · rw [zmod8_cast_eq_of_emod (r := 7) h', ite_eq_left (by decide)]
  · rw [ite_eq_right (by omega), ite_eq_left h]
    rcases (show -(D / 8) % 8 = 1 ∨ -(D / 8) % 8 = 5 by omega) with h' | h'
    · rw [zmod8_cast_eq_of_emod (r := 1) h', ite_eq_right (by decide)]
    · rw [zmod8_cast_eq_of_emod (r := 5) h', ite_eq_right (by decide)]

/-- $\beta_2(\langle u, 2w'\rangle, n) = 1 + \psi_2(un)$ when $uw' = -D/8$ ($8 \mid D$; $u, w', n$ odd). -/
theorem localDensity_rd_unit_two' {D : ℤ} [IsQuadDisc D] (h8 : (8 : ℤ) ∣ D) {u w' : ℤ}
    (hu : ¬ (2 : ℤ) ∣ u) (hw : ¬ (2 : ℤ) ∣ w') (huw : u * w' = -(D / 8)) (n : ℤ) (hn : ¬ (2 : ℤ) ∣ n) :
    localDensity (rd 2 u w') 2 n = 1 + (genusChar D 2 (u * n) : ℝ) := by
  rw [localDensity_rd_unit_two hu hw n hn, genusChar_two_of_eight h8, ← huw]
  push_cast
  rfl

theorem two_dvd_b_of_two_dvd {D : ℤ} {g : BinQF} (hgD : g.disc = D) (h2D : (2 : ℤ) ∣ D) : (2 : ℤ) ∣ g.b := by
  have : g.b ^ 2 = D + 4 * g.a * g.c := by rw [← hgD, BinQF.disc]; ring
  have h2 : (2 : ℤ) ∣ g.b ^ 2 := by
    rw [this]; exact dvd_add h2D (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
  exact int_prime_dvd_of_dvd_sq (p := 2) Nat.prime_two (by exact_mod_cast h2)

/-- Reduction of the formChar statement to forms with $p \nmid a$ (by exchanging $x, y$). -/
theorem localDensity_reduce_a {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (p : ℕ) [Fact p.Prime] (hpD : (p : ℤ) ∣ D) (m : ℤ) (c : ℝ)
    (H : ∀ g : BinQF, g.disc = D → ¬ (p : ℤ) ∣ g.a → localDensity g p m = 1 + (genusChar D p g.a : ℝ) * c) :
    localDensity f p m = 1 + (formChar f p : ℝ) * c := by
  have hpp : p.Prime := Fact.out
  have hr := not_dvd_charCoeff hf hpp (by rw [hD]; exact hpD)
  rw [formChar, hD]
  by_cases ha : (p : ℤ) ∣ f.a
  · have hcf : charCoeff f p = f.c := by simp [charCoeff, ha]
    rw [hcf] at hr ⊢
    rw [show localDensity f p m = localDensity (swapF f) p m from
      localDensity_eq_of_repCount fun k => (repCount_swapF f p k m).symm]
    have := H (swapF f) (by rw [disc_swapF, hD]) (by simpa using hr)
    rwa [swapF_a] at this
  · have hcf : charCoeff f p = f.a := by simp [charCoeff, ha]
    rw [hcf]; exact H f hD ha

/-- **$\beta_2(f, m)$ for $8 \mid D$, every $m \ne 0$:** $\beta_2(m) = 1 + \chi_2(f)\,c_2(m)$ with
$c_2(m) = \psi_2(m_0 e^{v})$, $e = -D/8$. (Reduction $af = (ax + b'y)^2 + 2e\,y^2$ to $\langle 1, 2e\rangle$, then the
recursion `localDensity_rd` and the check mod $8$.) -/
@[kb "siegel1935" "§§1–2 (p = 2, 8 | D) [unverified locator]"]
theorem localDensity_ram_two_eight {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (h8 : (8 : ℤ) ∣ D) {m : ℤ} (hm : m ≠ 0) :
    localDensity f 2 m = 1 + (formChar f 2 : ℝ) * (ramChar 2 D m : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := fund_cases (D := D)
  set w : ℤ := -(D / 8) with hwdef
  have hw : ¬ (2 : ℤ) ∣ w := by omega
  have h1 : ¬ (2 : ℤ) ∣ 1 := by norm_num
  refine localDensity_reduce_a hf hD 2 (by exact_mod_cast (show (2 : ℤ) ∣ 8 by norm_num).trans h8) m _ ?_
  intro g hgD ha
  obtain ⟨b', hb'⟩ := two_dvd_b_of_two_dvd hgD ((show (2 : ℤ) ∣ 8 by norm_num).trans h8)
  have hD4 : 2 * w = -(b' ^ 2 - g.a * g.c) := by
    have : D = 4 * (b' ^ 2 - g.a * g.c) := by rw [← hgD, BinQF.disc, hb']; ring
    omega
  have hcount : ∀ k, repCount g 2 k m = repCount (rd 2 1 w) 2 k (g.a * m) := by
    intro k
    refine repCount_transform g (rd 2 1 w) 2 k g.a b' g.a (isUnit_intCast_zmod_pow k ha)
      (isUnit_intCast_zmod_pow k ha) (fun x => ?_) m
    rw [rd, eval_diag_two, evalIn_bin, hb']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hd : ((((2 : ℕ) : ℤ) * w : ℤ) : ZMod (2 ^ k)) = -((b' ^ 2 - g.a * g.c : ℤ) : ZMod (2 ^ k)) := by
      rw [show ((2 : ℕ) : ℤ) * w = -(b' ^ 2 - g.a * g.c) by push_cast; exact hD4]; push_cast; ring
    rw [hd]; push_cast; ring
  have ham : g.a * m ≠ 0 := mul_ne_zero (by rintro h; rw [h] at ha; simp at ha) hm
  rw [localDensity_eq_of_repCount hcount, localDensity_rd h1 hw _ _ rfl ham,
    factorization_mul_unit (p := 2) ha hm, pFree_mul_unit (p := 2) ha hm]
  have hm0 := pFree_not_dvd (p := 2) hm
  have hn0 : ¬ ((2 : ℕ) : ℤ) ∣ g.a * pFree 2 m := fun h => (int_prime_dvd_mul Nat.prime_two h).elim ha hm0
  unfold ramChar ramUnit
  rw [ite_eq_left rfl, ite_eq_left h8]
  split_ifs with hv
  · rw [localDensity_rd_unit_two' h8 h1 hw (by rw [one_mul]) _ (by exact_mod_cast hn0), one_mul, mul_one,
      genusChar_mul]
    push_cast; ring
  · rw [localDensity_rd_unit_two' h8 hw h1 (by rw [mul_one]) _ (by exact_mod_cast hn0), genusChar_mul,
      genusChar_mul, genusChar_mul]
    push_cast; ring

end QuadFormsKB.Binary

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **Non-Zero-type solutions lift from level $2t + 1$ under a gradient bound $t$** (every vector with a unit
coordinate has a gradient entry not divisible by $\pi^{t+1}$). -/
theorem repCountOf_nonZero_add_of_grad (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (t : ℕ)
    (hgrad : ∀ x, GoodR Finset.univ π x → ∃ j, ¬ π ^ (t + 1) ∣ (Q.hessian *ᵥ x) j) (m : R) (k l : ℕ)
    (hk : 2 * t + 1 ≤ k) :
    repCountOf Q π (k + l) m (fun x => ¬ IsZeroType π (k + l) x) =
      q R ^ ((n - 1) * l) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  have hT : ∀ K, (fun x => ¬ IsZeroType π K x) = IsGoodType (Finset.univ : Finset (Fin n)) π K := by
    intro K; funext x
    simp only [IsGoodType, IsZeroType, Finset.mem_univ, true_and, not_forall]
    exact propext ⟨fun h => ⟨h, h⟩, fun h => h.2⟩
  rw [hT, hT, repCountOf_good_eq Q _ π _ (by omega), repCountOf_good_eq Q _ π _ (by omega)]
  exact countG_add Q π hπ (GoodR Finset.univ π) (goodR_add_pi _ π) t hgrad m k l hk

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Binary

open BinQF QuadForm LocalDensity Matrix

/-- **Non-Zero-type solutions of $\langle A, C\rangle$ ($A, C$ odd) lift from level $3$ at $p = 2$** (gradient
$(2Ax_0, 2Cx_1)$ has valuation $1$ at a vector with an odd coordinate). -/
theorem repCountOf_nonZero_add_diag_two {A C : ℤ} (hA : ¬ (2 : ℤ) ∣ A) (hC : ¬ (2 : ℤ) ∣ C) (m : ℤ)
    (k l : ℕ) (hk : 3 ≤ k) :
    repCountOf (BinQF.mk A 0 C) 2 (k + l) m (fun x => ¬ IsZeroType 2 (k + l) x) =
      2 ^ l * repCountOf (BinQF.mk A 0 C) 2 k m (fun x => ¬ IsZeroType 2 k x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [repCountOf_nonZero_eq_padic, repCountOf_nonZero_eq_padic]
  have hprime : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.irreducible_p.prime
  have hgrad : ∀ x : Fin 2 → ℤ_[2], DVR.GoodR Finset.univ ((2 : ℕ) : ℤ_[2]) x →
      ∃ j, ¬ ((2 : ℕ) : ℤ_[2]) ^ (1 + 1) ∣ (((BinQF.mk A 0 C).map (Int.castRingHom ℤ_[2])).hessian *ᵥ x) j := by
    rintro x ⟨i, -, hi⟩
    refine ⟨i, fun hdvd => ?_⟩
    have hH : ∀ j, (((BinQF.mk A 0 C).map (Int.castRingHom ℤ_[2])).hessian *ᵥ x) j =
        ((2 : ℕ) : ℤ_[2]) * ((if j = 0 then A else C : ℤ) : ℤ_[2]) * x j := by
      intro j
      rcases fin_two_cases j with rfl | rfl <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, QuadForm.hessian, QuadForm.map, BinQF.mk,
          QuadForm.ofUpper] <;> left <;> ring
    rw [hH, pow_two, mul_assoc] at hdvd
    have h2 : ((2 : ℕ) : ℤ_[2]) ≠ 0 := hprime.ne_zero
    have h' := (mul_dvd_mul_iff_left h2).mp hdvd
    rcases hprime.dvd_or_dvd h' with h | h
    · have hu : ¬ (2 : ℤ) ∣ (if i = 0 then A else C) := by split_ifs <;> assumption
      exact hu (Binary.int_dvd_of_padic_dvd h)
    · exact hi h
  rw [DVR.repCountOf_nonZero_add_of_grad _ _ PadicInt.irreducible_p 1 hgrad _ k l (by omega), q_padicInt]
  simp


/-! ### $p = 2$, $4 \,\|\, D$: the unimodular form $\langle 1, -D/4\rangle$ -/

section TwoUnimod

variable {D : ℤ} [IsQuadDisc D]

theorem hessian_det_eq_neg_disc' (f : BinQF) : f.hessian.det = -f.disc := by
  rw [hessian_det_two, BinQF.disc]; simp only [BinQF.a, BinQF.b, BinQF.c]; ring

/-- $\langle 1, -D/4\rangle$, a primitive form of discriminant $D$ when $4 \mid D$. -/
def g0 (D : ℤ) : BinQF := BinQF.mk 1 0 (-(D / 4))

theorem g0_primitive : Primitive (g0 D) := by simp [g0, Primitive]

theorem g0_disc (h4 : (4 : ℤ) ∣ D) : (g0 D).disc = D := by
  simp only [g0, BinQF.disc, a_mk, b_mk, c_mk]; have := Int.mul_ediv_cancel' h4; linarith

theorem odd_of_four_not_eight (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) :
    D % 32 = 12 ∨ D % 32 = 28 := by
  have := (two_dvd_iff_of_fund (D := D)).mp h2D; omega

/-- $\beta_2(\langle 1, -d\rangle, n) = 1 + \psi_2(n)$ for odd $n$. -/
theorem localDensity_g0_odd (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) (n : ℤ) (hn : ¬ (2 : ℤ) ∣ n) :
    localDensity (g0 D) 2 n = 1 + (genusChar D 2 n : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (4 : ℤ) ∣ D := by have := odd_of_four_not_eight h2D h8; omega
  rw [localDensity_ram_unit g0_primitive (g0_disc h4) 2 (by exact_mod_cast h2D) n (by exact_mod_cast hn)]
  have : formChar (g0 D) 2 = 1 := by
    simp [formChar, charCoeff, g0, genusChar]
  rw [this]; simp

/-- $\beta_2(\langle 1, -d\rangle, 2n') = 1 + \psi_2(e\,n')$ for odd $n'$, $e = (1 - d)/2$ ($d = D/4$ odd). -/
theorem localDensity_g0_two (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) (n' : ℤ) (hn : ¬ (2 : ℤ) ∣ n') :
    localDensity (g0 D) 2 (2 * n') = 1 + (genusChar D 2 ((1 - D / 4) / 2 * n') : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := odd_of_four_not_eight h2D h8
  have hd : ¬ (2 : ℤ) ∣ -(D / 4) := by omega
  have hz : ∀ k, 2 ≤ k → repCountOf (g0 D) 2 k (2 * n') (IsZeroType 2 k) = 0 := by
    intro k hk
    rw [repCountZero_eq _ 2 _ k hk, ite_eq_right]
    intro h; apply hn
    have : (4 : ℤ) ∣ 2 * n' := by exact_mod_cast h
    omega
  have hlift : ∀ l, repCount (g0 D) 2 (3 + l) (2 * n') = 2 ^ l * repCount (g0 D) 2 3 (2 * n') := by
    intro l
    rw [repCount_eq_zero_add_nonZero, repCount_eq_zero_add_nonZero, hz _ (by omega), hz _ (by omega),
      zero_add, zero_add, g0, repCountOf_nonZero_add_diag_two (by norm_num) hd _ 3 l le_rfl]
  rw [localDensity_eq_of_lift _ 2 _ 3 hlift, repCount_eq_card _ 2 3 8 (by norm_num)]
  simp only [g0, a_mk, b_mk, c_mk, Int.cast_zero, zero_mul, add_zero, Int.cast_one, one_mul]
  have hd8 : ((D / 4 : ℤ) : ZMod 8) ∈ ({3, 7} : Finset (ZMod 8)) := by
    rcases hc with h | h
    · rw [zmod8_cast_eq_of_emod (r := 3) (by omega)]; decide
    · rw [zmod8_cast_eq_of_emod (r := 7) (by omega)]; decide
  have e1 : ∀ v : ZMod 8 × ZMod 8, (v.1 ^ 2 + ((-(D / 4) : ℤ) : ZMod 8) * v.2 ^ 2 = ((2 * n' : ℤ) : ZMod 8) ↔
      v.1 ^ 2 - ((D / 4 : ℤ) : ZMod 8) * v.2 ^ 2 = 2 * (n' : ZMod 8)) := by
    intro v; push_cast; constructor <;> intro h <;> linear_combination h
  rw [card8_aux (fun v => v.1 ^ 2 + ((-(D / 4) : ℤ) : ZMod 8) * v.2 ^ 2 = ((2 * n' : ℤ) : ZMod 8)),
    Finset.filter_congr (fun v _ => e1 v)]
  have key := card8_unimod_two _ hd8 _ (mem_odd8 hn)
  have key' := congrArg (fun z : ℤ => (z : ℝ)) key
  push_cast at key'
  rw [genusChar_two_eq, ite_eq_right (show ¬ D % 32 = 8 by omega), ite_eq_right (show ¬ D % 32 = 24 by omega),
    key']
  have hcast : ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4)
      ((n' : ZMod 8) * (if ((D / 4 : ℤ) : ZMod 8) = 3 then 7 else 5)) =
      ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) ((((1 - D / 4) / 2 * n' : ℤ)) : ZMod 8) := by
    rw [map_mul, map_intCast, map_intCast, Int.cast_mul]
    rcases hc with h | h
    · rw [zmod8_cast_eq_of_emod (r := 3) (show D / 4 % 8 = 3 by omega), ite_eq_left (by decide),
        zmod4_cast_eq_of_emod (r := 3) (show (1 - D / 4) / 2 % 4 = 3 by omega)]
      rw [mul_comm]; rfl
    · rw [zmod8_cast_eq_of_emod (r := 7) (show D / 4 % 8 = 7 by omega), ite_eq_right (by decide),
        zmod4_cast_eq_of_emod (r := 1) (show (1 - D / 4) / 2 % 4 = 1 by omega)]
      rw [mul_comm]; rfl
  rw [hcast]
  push_cast
  ring

/-- $\beta_2(\langle 1, -d\rangle, n) = \beta_2(\langle 1, -d\rangle, n/4)$ for $4 \mid n$ ($d$ odd, $d \equiv 3 \bmod 4$): no
solution with an odd coordinate has $x_0^2 - dx_1^2 \equiv 0 \pmod 4$. -/
theorem localDensity_g0_four (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) (n : ℤ) (hn0 : n ≠ 0)
    (h4 : (4 : ℤ) ∣ n) : localDensity (g0 D) 2 n = localDensity (g0 D) 2 (n / 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := odd_of_four_not_eight h2D h8
  have hD4 : (4 : ℤ) ∣ D := by omega
  have hp0 : (2 : ℝ) ≠ 0 := by norm_num
  have hnz : ∀ k, 2 ≤ k → repCountOf (g0 D) 2 k n (fun x => ¬ IsZeroType 2 k x) = 0 := by
    intro k hk
    unfold repCountOf
    rw [Nat.card_eq_zero]; left; constructor
    rintro ⟨x, hx, hnz⟩
    apply hnz
    have h4k : 4 ∣ 2 ^ k := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 hk
    set φ := ZMod.castHom h4k (ZMod 4)
    have hx4 := congrArg φ hx
    rw [evalIn_bin] at hx4
    simp only [map_add, map_mul, map_pow, map_intCast, g0, a_mk, b_mk, c_mk] at hx4
    have hn4 : ((n : ℤ) : ZMod 4) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n 4).mpr (by exact_mod_cast h4)
    have hd4 : ((D / 4 : ℤ) : ZMod 4) = 3 := zmod4_cast_eq_of_emod (r := 3) (by omega)
    rw [hn4] at hx4
    have hx4' : φ (x 0) ^ 2 - 3 * φ (x 1) ^ 2 = 0 := by
      rw [← hd4]; push_cast at hx4 ⊢; linear_combination hx4
    obtain ⟨h0, h1⟩ := zmod4_unimod_two 3 (by decide) _ _ hx4'
    have hcomp : ∀ y, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (φ y) =
        ZMod.castHom (dvd_pow_self 2 (by omega : k ≠ 0)) (ZMod 2) y := by
      intro y
      exact RingHom.congr_fun (Subsingleton.elim
        ((ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)).comp φ) _) y
    intro i
    rw [zmod_p_dvd_iff (p := 2) (by omega), ← hcomp]
    rcases fin_two_cases i with rfl | rfl
    · exact h0
    · exact h1
  have hn40 : n / 4 ≠ 0 := by
    obtain ⟨c, rfl⟩ := h4; rw [Int.mul_ediv_cancel_left _ (by norm_num)]; rintro rfl; simp at hn0
  have hev := localDensity_eventually_eq (g0 D) (by
    unfold QuadForm.Nondegenerate
    rw [hessian_det_eq_neg_disc', g0_disc hD4]; have := three_le_natAbs (D := D); omega) 2 (n / 4) hn40
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  apply limUnder_eq_of_eventually
  rw [Filter.eventually_atTop]
  refine ⟨J + 2, fun k hk => ?_⟩
  rw [repCount_eq_zero_add_nonZero, hnz k (by omega), add_zero, repCountZero_eq _ 2 n k (by omega),
    ite_eq_left (by exact_mod_cast (show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num) ▸ h4), ← hJ (k - 2) (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 2 = j by omega, show (j + 2) * (2 - 1) = j + 2 by omega, show j * (2 - 1) = j by omega]
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- **$\beta_2(\langle 1, -d\rangle, n)$ for every $n \ne 0$** ($4 \,\|\, D$): $1 + \psi_2(n_0 e^{v})$, $e = (1 - D/4)/2$. -/
theorem localDensity_g0 (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) :
    ∀ N : ℕ, ∀ n : ℤ, n.natAbs = N → n ≠ 0 →
      localDensity (g0 D) 2 n = 1 + (genusChar D 2 (pFree 2 n *
        (if Even (n.natAbs.factorization 2) then 1 else (1 - D / 4) / 2)) : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hN hn0
  by_cases hn : (2 : ℤ) ∣ n
  · by_cases h4 : (4 : ℤ) ∣ n
    · have hn' : ((2 : ℕ) : ℤ) ∣ n := by exact_mod_cast hn
      have hnp : ((2 : ℕ) : ℤ) ∣ n / (2 : ℕ) := by
        obtain ⟨c, rfl⟩ := h4
        rw [show (4 : ℤ) * c = (2 : ℕ) * (2 * c) by push_cast; ring,
          Int.mul_ediv_cancel_left _ (by norm_num)]
        exact ⟨c, by push_cast; ring⟩
      have hnp0 : n / ((2 : ℕ) : ℤ) ≠ 0 := by
        intro h; rw [h] at hnp; obtain ⟨c, rfl⟩ := h4; push_cast at h
        omega
      have hdiv : n / 4 = n / ((2 : ℕ) : ℤ) / ((2 : ℕ) : ℤ) := by
        push_cast; rw [Int.ediv_ediv_of_nonneg (by norm_num)]; norm_num
      have hn40 : n / 4 ≠ 0 := by
        obtain ⟨c, rfl⟩ := h4; rw [Int.mul_ediv_cancel_left _ (by norm_num)]; rintro rfl; simp at hn0
      have hlt : (n / 4).natAbs < N := by
        rw [← hN]; obtain ⟨c, rfl⟩ := h4
        rw [Int.mul_ediv_cancel_left _ (by norm_num), Int.natAbs_mul]
        have : 0 < c.natAbs := Int.natAbs_pos.mpr (by rintro rfl; simp at hn0)
        simp; omega
      rw [localDensity_g0_four h2D h8 n hn0 h4, ih _ hlt (n / 4) rfl hn40, hdiv,
        factorization_div_p (p := 2) hn0 hn', factorization_div_p (p := 2) hnp0 hnp,
        ← pFree_div_p (p := 2) hn0 hn', ← pFree_div_p (p := 2) hnp0 hnp]
      simp [Nat.even_add_one]
    · have hn' : ((2 : ℕ) : ℤ) ∣ n := by exact_mod_cast hn
      obtain ⟨n', rfl⟩ := hn
      have hn'o : ¬ (2 : ℤ) ∣ n' := by
        rintro ⟨c, rfl⟩; exact h4 ⟨c, by ring⟩
      have hn'0 : n' ≠ 0 := by rintro rfl; simp at hn0
      have hdiv : 2 * n' / ((2 : ℕ) : ℤ) = n' := by push_cast; omega
      rw [localDensity_g0_two h2D h8 n' hn'o, factorization_div_p (p := 2) hn0 hn', hdiv,
        ← pFree_div_p (p := 2) hn0 hn', hdiv, pFree_of_not_dvd (by exact_mod_cast hn'o),
        Nat.factorization_eq_zero_of_not_dvd (fun h => hn'o (by exact_mod_cast int_dvd_iff_natAbs.mpr h))]
      simp [mul_comm]
  · rw [localDensity_g0_odd h2D h8 n hn, pFree_of_not_dvd (by exact_mod_cast hn),
      Nat.factorization_eq_zero_of_not_dvd (fun h => hn (by exact_mod_cast int_dvd_iff_natAbs.mpr h))]
    simp

end TwoUnimod

/-- **$\beta_2(f, m)$ for $4 \,\|\, D$, every $m \ne 0$:** $\beta_2(m) = 1 + \chi_2(f)\,c_2(m)$ with
$c_2(m) = \psi_2(m_0 e^{v})$, $e = (1 - D/4)/2$. (Reduction $af = (ax + b'y)^2 - \frac D4y^2$ to $\langle 1, -D/4\rangle$.) -/
@[kb "siegel1935" "§§1–2 (p = 2, 4 ∥ D) [unverified locator]"]
theorem localDensity_ram_two_four {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (h2D : (2 : ℤ) ∣ D) (h8 : ¬ (8 : ℤ) ∣ D) {m : ℤ} (hm : m ≠ 0) :
    localDensity f 2 m = 1 + (formChar f 2 : ℝ) * (ramChar 2 D m : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := odd_of_four_not_eight h2D h8
  have hD4 : (4 : ℤ) ∣ D := by omega
  refine localDensity_reduce_a hf hD 2 (by exact_mod_cast h2D) m _ ?_
  intro g hgD ha
  obtain ⟨b', hb'⟩ := two_dvd_b_of_two_dvd hgD h2D
  have hd : D / 4 = b' ^ 2 - g.a * g.c := by
    have : D = 4 * (b' ^ 2 - g.a * g.c) := by rw [← hgD, BinQF.disc, hb']; ring
    omega
  have hcount : ∀ k, repCount g 2 k m = repCount (g0 D) 2 k (g.a * m) := by
    intro k
    refine repCount_transform g (g0 D) 2 k g.a b' g.a (isUnit_intCast_zmod_pow k ha)
      (isUnit_intCast_zmod_pow k ha) (fun x => ?_) m
    rw [g0, evalIn_bin, evalIn_bin, hb', a_mk, b_mk, c_mk, hd]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast; ring
  have ham : g.a * m ≠ 0 := mul_ne_zero (by rintro h; rw [h] at ha; simp at ha) hm
  have ha' : ¬ ((2 : ℕ) : ℤ) ∣ g.a := by exact_mod_cast ha
  rw [localDensity_eq_of_repCount hcount, localDensity_g0 h2D h8 _ _ rfl ham,
    factorization_mul_unit (p := 2) ha' hm, pFree_mul_unit (p := 2) ha' hm]
  unfold ramChar ramUnit
  rw [ite_eq_left rfl, ite_eq_right h8]
  split_ifs with hv
  · rw [mul_one, mul_one, genusChar_mul]; push_cast; ring
  · simp only [genusChar_mul]; push_cast; ring

/-! ### Every ramified prime -/

/-- **$\beta_p(f, m)$ at a ramified prime, every $m \ne 0$** ($D$ fundamental, $f$ primitive of discriminant $D$,
$p \mid D$ prime, $p = 2$ included):
$$\beta_p(m) = 1 + \chi_p(f)\,c_p(m) \in \{0, 2\}, \qquad c_p(m) = \psi_p\big(m_0\,e_p^{\,v}\big),$$
$v = v_p(m)$, $m_0 = m/p^v$, $e_p$ = `ramUnit p D` ($-D/p$ for odd $p$; $-D/8$ or $(1 - D/4)/2$ for $p = 2$). The
value depends on $f$ only through its genus character $\chi_p(f)$. -/
@[kb "siegel1935" "§§1–2, the densities α_p at p | D (binary case) [unverified locator]"]
theorem localDensity_ram {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (p : ℕ) [Fact p.Prime] (hpD : (p : ℤ) ∣ D) {m : ℤ} (hm : m ≠ 0) :
    localDensity f p m = 1 + (formChar f p : ℝ) * (ramChar p D m : ℝ) := by
  by_cases hp2 : p = 2
  · subst hp2
    by_cases h8 : (8 : ℤ) ∣ D
    · exact localDensity_ram_two_eight hf hD h8 hm
    · exact localDensity_ram_two_four hf hD (by exact_mod_cast hpD) h8 hm
  · rw [localDensity_ram_odd hf hD hp2 hpD hm, ramChar_odd hp2]

/-- $c_p(m) = \pm 1$ for $p \mid D$, $m \ne 0$. -/
theorem ramChar_sq {D : ℤ} [IsQuadDisc D] (p : ℕ) [hp : Fact p.Prime] (hpD : (p : ℤ) ∣ D) {m : ℤ}
    (hm : m ≠ 0) : ramChar p D m ^ 2 = 1 := by
  have hpp := hp.out
  unfold ramChar
  apply genusChar_sq D hpp
  have hm0 := pFree_not_dvd (p := p) hm
  have he : ¬ (p : ℤ) ∣ ramUnit p D := by
    unfold ramUnit
    by_cases hp2 : p = 2
    · subst hp2
      have hc := (two_dvd_iff_of_fund (D := D)).mp (by exact_mod_cast hpD)
      rw [ite_eq_left rfl]
      split_ifs with h8 <;> push_cast <;> omega
    · rw [ite_eq_right hp2]
      intro ⟨c, hc⟩
      apply odd_prime_sq_not_dvd (D := D) hpp hp2
      have : D = (p : ℤ) * (D / p) := (Int.mul_ediv_cancel' hpD).symm
      exact ⟨-c, by rw [this, show D / p = -(-(D / p)) by ring, hc]; ring⟩
  intro h
  rcases int_prime_dvd_mul hpp h with h | h
  · exact hm0 h
  · split_ifs at h
    · exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
    · exact he h

end QuadFormsKB.Binary
