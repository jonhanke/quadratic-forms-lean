import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Densities
import QuadFormsKB.Tamagawa.Classical.TernaryDensities

/-!
# Berkovich–Hanke–Jagy, S-genus identities: local densities of $x^2+y^2+z^2$

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary
quadratic forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §4, Lemmas 4.1 and 4.3, pp. 4–5.

* `localDensity_sumSq_three_odd` (Lemma 4.1): for an odd prime $p$ and an integer $m \ne 0$,
  $\beta_{x^2+y^2+z^2,\,p}(m) = $ `beta3 p m`.  Proof as in the paper: Table 1 gives
  $\beta(m) = 1 + \chi/p$ for $p \nmid m$ and $1 - p^{-2}$ for $p \,\|\, m$, and the Zero-type
  recursion $\beta(p^2 T) = (1 - p^{-2}) + \beta(T)/p$ ($T \neq 0$) gives the rest by induction.
* `localDensity_sumSq_three_two` (Lemma 4.3, formula (2)): the dyadic density
  $\beta_{x^2+y^2+z^2,\,2}(m)$ for $4 \nmid m$ (proved in
  `QuadFormsKB.Tamagawa.Classical`; restated here in the paper's form).
* `localDensity_diag_u_two` (Lemma 4.3, formula (3)): $\beta_{ux^2+2uy^2+2z^2,\,2}(m) = 1$ for
  $m \equiv 1, 2 \pmod 4$, and explicitly $0$ or $2$ for $m \equiv 3 \pmod 4$ depending on $u$.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Classical

section Odd

variable (p : ℕ)

theorem geomSum_succ_last (k : ℕ) : geomSum p (k + 1) = 1 + geomSum p k / p := by
  unfold geomSum
  rw [Finset.sum_range_succ', Finset.sum_div]
  have : ∀ j ∈ Finset.range k, (1 / (p : ℚ)) ^ (j + 1) = (1 / (p : ℚ)) ^ j / p := by
    intro j _; rw [pow_succ]; ring
  rw [Finset.sum_congr rfl this]; simp [add_comm]

variable [Fact p.Prime] in
theorem padicValInt_sq_mul (T : ℤ) (hT : T ≠ 0) :
    padicValInt p ((p : ℤ) ^ 2 * T) = padicValInt p T + 2 := by
  have hp : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [padicValInt.mul hp hT]
  have : padicValInt p ((p : ℤ) ^ 2) = 2 := by
    simp [padicValInt, Int.natAbs_pow]
  omega

variable [Fact p.Prime] in
theorem sqFree_sq_mul (T : ℤ) (hT : T ≠ 0) : sqFree p ((p : ℤ) ^ 2 * T) = sqFree p T := by
  unfold sqFree
  rw [padicValInt_sq_mul p T hT]
  have hp : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [show 2 * ((padicValInt p T + 2) / 2) = 2 + 2 * (padicValInt p T / 2) by omega, pow_add]
  have hpos : (0 : ℤ) < (p : ℤ) ^ 2 := by
    have := (Fact.out : p.Prime).pos
    positivity
  exact Int.mul_ediv_mul_of_pos _ _ hpos

variable [Fact p.Prime] in
/-- Recursion for the explicit formula: $\beta_3(p^2 T) = (1 - p^{-2}) + \beta_3(T)/p$. -/
theorem beta3_sq_mul (T : ℤ) (hT : T ≠ 0) :
    beta3 p ((p : ℤ) ^ 2 * T) = (1 - 1 / (p : ℚ) ^ 2) + beta3 p T / p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold beta3 chiOf
  rw [sqFree_sq_mul p T hT, padicValInt_sq_mul p T hT]
  simp only []
  rw [show (padicValInt p T + 2) / 2 = padicValInt p T / 2 + 1 by omega,
    show (padicValInt p T + 2) % 2 = padicValInt p T % 2 by omega]
  split_ifs
  · simp only [geomSum_succ_last]; field_simp; ring
  · simp only [geomSum_succ_last]; field_simp

end Odd

section Density

variable (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)

theorem units_one : ∀ i : Fin 3, ¬ (p : ℤ) ∣ (![1, 1, 1] : Fin 3 → ℤ) i := by
  intro i
  have hp1 : ¬ (p : ℤ) ∣ 1 := fun h => by
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this)
  fin_cases i <;> simpa using hp1

include hp in
theorem density_sq_mul (T : ℤ) (hT : T ≠ 0) :
    LocalDensity.localDensity (Siegel.sumSq 3) p ((p : ℤ) ^ 2 * T) =
      (1 - 1 / (p : ℝ) ^ 2) + LocalDensity.localDensity (Siegel.sumSq 3) p T / p := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  rw [sumSq_three_eq] at *
  have hnd : (QuadForm.diag ![(1 : ℤ), 1, 1]).Nondegenerate :=
    LocalDensity.nondegenerate_diag _ (by intro i; fin_cases i <;> simp)
  have h := localDensityOf_nonZero_eq _ hnd p (by norm_num) T hT
  rw [localDensityOf_nonZero_diag_sq _ p hp (units_one p),
    (table1_three 1 1 1 p hp (units_one p 0) (units_one p 1) (units_one p 2) 1
      (units_one p 0)).1] at h
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl, pow_one] at h
  push_cast at h
  field_simp at h ⊢
  linarith

include hp in
theorem density_unit (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    LocalDensity.localDensity (Siegel.sumSq 3) p m = 1 + (legendreSym p (-m) : ℝ) / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [sumSq_three_eq, localDensity_unit ![1, 1, 1] p hp (units_one p) m hm]
  have t := (table1_three 1 1 1 p hp (units_one p 0) (units_one p 1) (units_one p 2) m hm).2
  have t' : (LocalDensity.repCount (QuadForm.diag ![1, 1, 1]) p 1 m : ℝ) =
      (p : ℝ) ^ 2 + p * (legendreSym p (-m) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) t
    simpa using this
  rw [t']
  simp only [show (3 : ℕ) - 1 = 2 from rfl]
  field_simp

include hp in
theorem density_ord_one (m : ℤ) (hm : padicValInt p m = 1) :
    LocalDensity.localDensity (Siegel.sumSq 3) p m = 1 - 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [sumSq_three_eq, localDensity_diag_ord_one ![1, 1, 1] p hp (units_one p) m hm,
    (table1_three 1 1 1 p hp (units_one p 0) (units_one p 1) (units_one p 2) 1
      (units_one p 0)).1]
  simp only [show (3 : ℕ) - 1 = 2 from rfl]
  push_cast
  field_simp

include hp in
/-- **Lemma 4.1 (BHJ).** For an odd prime $p$ and $m \ne 0$,
$\beta_{x^2+y^2+z^2,\,p}(m)$ equals the explicit formula `beta3 p m`:
$(1 - p^{-2})(1 + p^{-1} + \dots + p^{1-k}) + p^{-k}(1 + \chi/p)$ if $\operatorname{ord}_p(m) = 2k$ and
$(1 - p^{-2})(1 + p^{-1} + \dots + p^{-k})$ if $\operatorname{ord}_p(m) = 2k+1$, where
$\chi = \left(\frac{-m/p^{2k}}{p}\right)$. -/
@[kb "berkovich2012" "§4, Lemma 4.1, p. 4"]
theorem localDensity_sumSq_three_odd (m : ℤ) (hm : m ≠ 0) :
    LocalDensity.localDensity (Siegel.sumSq 3) p m = ((beta3 p m : ℚ) : ℝ) := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  induction' hn : m.natAbs using Nat.strong_induction_on with n ih generalizing m
  by_cases h1 : (p : ℤ) ∣ m
  · by_cases h2 : (p : ℤ) ^ 2 ∣ m
    · obtain ⟨T, rfl⟩ := h2
      have hT : T ≠ 0 := by rintro rfl; simp at hm
      have hlt : T.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have := hpp.two_le
        simp only [Int.natAbs_pow, Int.natAbs_natCast]
        have : 0 < T.natAbs := Int.natAbs_pos.2 hT
        have : 2 ≤ p ^ 2 := by nlinarith
        nlinarith
      rw [density_sq_mul p hp T hT, ih _ hlt T hT rfl, beta3_sq_mul p T hT]
      push_cast
      ring
    · have hv : padicValInt p m = 1 := by
        have h2' : ¬ 2 ≤ padicValInt p m := fun h =>
          h2 ((padicValInt_dvd_iff 2 m).2 (Or.inr h))
        have h1' : 1 ≤ padicValInt p m := by
          have := (padicValInt_dvd_iff (p := p) 1 m).1 (by simpa using h1)
          rcases this with h | h
          · exact absurd h hm
          · exact h
        omega
      rw [density_ord_one p hp m hv]
      unfold beta3
      simp only [hv]
      norm_num [geomSum]
  · rw [density_unit p hp m h1]
    unfold beta3 chiOf sqFree
    rw [padicValInt.eq_zero_of_not_dvd (by exact_mod_cast h1)]
    simp [geomSum]
end Density

section Dyadic

/-- Number of pairs with $a x^2 + b y^2 = s$ in $(\mathbb{Z}/2^k)^2$. -/
def card2 {k : ℕ} (a b s : ZMod (2 ^ k)) : ℕ :=
  Fintype.card {p : ZMod (2 ^ k) × ZMod (2 ^ k) // a * p.1 ^ 2 + b * p.2 ^ 2 = s}

theorem card3Z_split (a b c : ℤ) (k : ℕ) (t : ZMod (2 ^ k)) :
    card3Z a b c k t = ∑ z : ZMod (2 ^ k), card2 (a : ZMod (2 ^ k)) b (t - c * z ^ 2) := by
  unfold card3Z card2
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun y => ⟨y.1.2.2, ⟨(y.1.1, y.1.2.1), by
        have := y.2; simp only at this ⊢; linear_combination this⟩⟩
      invFun := fun s => ⟨(s.2.1.1, s.2.1.2, s.1), by
        have := s.2.2; simp only at this ⊢; linear_combination this⟩
      left_inv := fun y => rfl
      right_inv := fun s => rfl }

theorem card2_scale {k : ℕ} (c a b v s : ZMod (2 ^ k)) (h : v * c = 1) :
    card2 (c * a) (c * b) s = card2 a b (v * s) := by
  unfold card2
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  constructor
  · intro hh
    linear_combination v * hh - (a * p.1 ^ 2 + b * p.2 ^ 2) * h
  · intro hh
    linear_combination c * hh + s * h

def pairTab : List ℕ :=
  [32, 64, 64, 64, 64, 0, 64, 0, 32, 64, 0, 64, 64, 0, 0, 0, 32, 64, 64, 64, 0, 0, 64, 0, 32, 64, 0, 64, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem enum_pair : ∀ s : ZMod (2 ^ 5), card2 (1 : ZMod (2 ^ 5)) 2 s = pairTab.getD s.val 0 := by
  unfold card2 pairTab; decide +kernel

set_option maxRecDepth 100000 in
theorem enum_inv : ∀ U : ZMod (2 ^ 5), U.val % 2 = 1 → U ^ 7 * U = 1 := by
  decide +kernel

/-- The expected count of solutions mod $32$, divided by $1024$ (see `card3Z_C`). -/
def gC (u t : ℕ) : ℕ :=
  if t % 4 ≠ 3 then 1
  else if (t % 8 = 3 ∧ (u % 8 = 1 ∨ u % 8 = 3)) ∨ (t % 8 = 7 ∧ (u % 8 = 5 ∨ u % 8 = 7)) then 2 else 0

set_option maxRecDepth 100000 in
theorem enum_sum : ∀ U : ZMod (2 ^ 5), U.val % 2 = 1 → ∀ t : ZMod (2 ^ 5), t.val % 4 ≠ 0 →
    ∑ z : ZMod (2 ^ 5), pairTab.getD ((U ^ 7 * (t - 2 * z ^ 2)).val) 0 = 1024 * gC U.val t.val := by
  unfold gC pairTab; decide +kernel


theorem card3Z_C (u : ℤ) (hu : Odd u) (m : ℤ) (hm : ¬ (4 : ℤ) ∣ m) :
    card3Z u (2 * u) 2 5 (m : ZMod (2 ^ 5)) = 1024 *
      (if m % 4 ≠ 3 then 1
       else if (m % 8 = 3 ∧ (u % 8 = 1 ∨ u % 8 = 3)) ∨ (m % 8 = 7 ∧ (u % 8 = 5 ∨ u % 8 = 7))
       then 2 else 0) := by
  have hU : ((ZMod.val (u : ZMod (2 ^ 5)) : ℕ) : ℤ) = u % 32 := by
    rw [ZMod.val_intCast]; norm_num
  have hT : ((ZMod.val (m : ZMod (2 ^ 5)) : ℕ) : ℤ) = m % 32 := by
    rw [ZMod.val_intCast]; norm_num
  set U : ZMod (2 ^ 5) := (u : ZMod (2 ^ 5))
  set t : ZMod (2 ^ 5) := (m : ZMod (2 ^ 5))
  obtain ⟨r, hr⟩ := hu
  have h1 : U.val % 2 = 1 := by omega
  have h2 : t.val % 4 ≠ 0 := by omega
  have h3 := enum_sum U h1 t h2
  have key : ∀ z : ZMod (2 ^ 5), card2 U (2 * U) (t - 2 * z ^ 2) =
      pairTab.getD ((U ^ 7 * (t - 2 * z ^ 2)).val) 0 := by
    intro z
    have e := card2_scale U 1 2 (U ^ 7) (t - 2 * z ^ 2) (enum_inv U h1)
    rw [mul_one, mul_comm U 2] at e
    rw [e, enum_pair]
  rw [card3Z_split]
  push_cast
  refine (Finset.sum_congr rfl (fun z _ => key z)).trans ?_
  rw [h3]
  unfold gC
  split_ifs <;> omega


theorem isJordanFormW_C {u : ℤ} (hu : Odd u) :
    DVR.IsJordanFormW (QuadForm.diag ![(u : ℤ_[2]), ((2 * u : ℤ) : ℤ_[2]), ((2 : ℤ) : ℤ_[2])])
      (2 : ℤ_[2]) ∅ ![0, 1, 1] := by
  have hπ := padic_two_irreducible
  have hun : IsUnit (u : ℤ_[2]) :=
    DVR.dvr_isUnit_of_not_dvd hπ (padic_two_not_dvd_odd (odd_not_dvd_two hu))
  refine ⟨fun h => absurd h Finset.not_nonempty_empty, fun e he => absurd he (Finset.notMem_empty e),
    fun e he => absurd he (Finset.notMem_empty e), fun i j hij _ => ?_,
    fun e he => absurd he (Finset.notMem_empty e), fun i _ => ?_⟩
  · simp [QuadForm.diag, hij.ne]
  · fin_cases i
    · exact ⟨u, by simp [QuadForm.diag], hun⟩
    · exact ⟨u, by simp [QuadForm.diag], hun⟩
    · exact ⟨1, by simp [QuadForm.diag], isUnit_one⟩

theorem localDensity_C_card {u : ℤ} (hu : Odd u) {m : ℤ} (hm : ¬ (4 : ℤ) ∣ m) :
    localDensity (QuadForm.diag ![u, 2 * u, 2]) 2 m =
      (card3Z u (2 * u) 2 5 (m : ZMod (2 ^ 5)) : ℝ) / 1024 := by
  have hπ := padic_two_irreducible
  have h2 : ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ (m : ℤ_[2]) := by
    have := padic_pow_dvd_int_iff 2 (1 + 1) m
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num; omega
  have h := DVR.localDensity_eq_level_J _ 2 hπ ∅ ![0, 1, 1] (isJordanFormW_C hu) 1 padic_two_ord 1
    (fun i => by fin_cases i <;> simp) h2 5 (by norm_num)
  rw [localDensity_eq_padic, diag3_map, Nat.cast_ofNat, h, repCount_padic_diag3, q_padicInt]
  norm_num


/-- **Lemma 4.3, formula (2) (BHJ).** The dyadic density of $x^2+y^2+z^2$:
$\beta_{x^2+y^2+z^2,\,2}(m) = 3/2$ if $m \equiv 1, 2 \pmod 4$, $1$ if $m \equiv 3 \pmod 8$ and
$0$ if $m \equiv 7 \pmod 8$ (here $m$ is any integer, `m % 4` etc. in `ℤ`). -/
@[kb "berkovich2012" "§4, Lemma 4.3, formula (2), p. 5"]
theorem localDensity_sumSq_three_two_paper (m : ℤ) :
    (m % 4 = 1 ∨ m % 4 = 2 → LocalDensity.localDensity (Siegel.sumSq 3) 2 m = 3 / 2) ∧
    (m % 8 = 3 → LocalDensity.localDensity (Siegel.sumSq 3) 2 m = 1) ∧
    (m % 8 = 7 → LocalDensity.localDensity (Siegel.sumSq 3) 2 m = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    rw [localDensity_sumSq_three_two (by omega)] <;> split_ifs <;> first | rfl | omega

/-- **Lemma 4.3, formula (3) (BHJ), for $m \equiv 1, 2 \pmod 4$ and $m \equiv 3 \pmod 4$.** For
$u$ odd, the form $G = u x^2 + 2u y^2 + 2 z^2$ has dyadic density
$\beta_{G,2}(m) = 1$ if $m \equiv 1, 2 \pmod 4$, and, for $m \equiv 3 \pmod 4$,
$\beta_{G,2}(m) = 2$ if ($m \equiv 3 \pmod 8$ and $u \equiv 1, 3 \pmod 8$) or
($m \equiv 7 \pmod 8$ and $u \equiv 5, 7 \pmod 8$), and $0$ otherwise.
Proof: $r_{2^5}(m)/2^{10}$ at level $a + L + 2e + 1 = 1 + 1 + 2 + 1 = 5$
(`DVR.localDensity_eq_level_J`), evaluated by a kernel enumeration of pair counts
(`enum_pair`, `enum_sum`). -/
@[kb "berkovich2012" "§4, Lemma 4.3, formula (3), p. 5"]
theorem localDensity_diag_u_two {u : ℤ} (hu : Odd u) (m : ℤ) :
    (m % 4 = 1 ∨ m % 4 = 2 →
      LocalDensity.localDensity (QuadForm.diag ![u, 2 * u, 2]) 2 m = 1) ∧
    (m % 4 = 3 →
      LocalDensity.localDensity (QuadForm.diag ![u, 2 * u, 2]) 2 m =
        if (m % 8 = 3 ∧ (u % 8 = 1 ∨ u % 8 = 3)) ∨ (m % 8 = 7 ∧ (u % 8 = 5 ∨ u % 8 = 7))
        then 2 else 0) := by
  have hc : ∀ m : ℤ, m % 4 ≠ 0 → ¬ (4 : ℤ) ∣ m := fun m h h' => h (by omega)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [localDensity_C_card hu (hc m (by omega)), card3Z_C u hu m (hc m (by omega))]
    split_ifs <;> first | omega | norm_num
  · rw [localDensity_C_card hu (hc m (by omega)), card3Z_C u hu m (hc m (by omega))]
    split_ifs <;> first | omega | norm_num

end Dyadic

end QuadFormsKB.Berkovich2012
