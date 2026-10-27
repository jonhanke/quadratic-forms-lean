/-
# Local densities of the classical ternary forms

**Layer:** $\mathbb Z$-local densities $\beta_p(m)$ (`LocalDensity.localDensity`) of $x_0^2+x_1^2+x_2^2$ (`Siegel.sumSq 3`)
and $x_0^2+x_1^2-x_2^2$ (`qInd`), used by the explicit evaluations of the Siegel headlines.

**Proves**
* `localDensity_sumSq_three_two`: $\beta_2(x_0^2+x_1^2+x_2^2; m) = 0, 1, 3/2$ for $4 \nmid m$ according to $m \bmod 8$;
* `localDensity_qInd_two`: $\beta_2(x_0^2+x_1^2-x_2^2; m) = 2, 1, 1/2$ for $4 \nmid m$;
* `localDensity_qInd_sq`: $\beta_p(x_0^2+x_1^2-x_2^2; k^2) = \beta_p(1) = 1 + 1/p$ ($p$ odd), $2$ ($p = 2$), for $k \ne 0$.

*Method.* $p = 2$: level $3$ (odd $m$) / level $4$ ($m \equiv 2 \bmod 4$) counts via `DVR.localDensity_unit_diag` and
`DVR.localDensity_eq_level_J`, and the Zero-type recursion `DVR.localDensity_eq_prim_add_zero_J`; the counts are kernel
enumerations (`decide +kernel`). Odd $p$: Table 1 / `localDensity_unit` and the recursion (5.7).
-/
import QuadFormsKB.Tamagawa.Classical.Basic
import QuadFormsKB.LocalDensity.BridgeDyadicBad

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB QuadFormsKB.LocalDensity QuadForm

/-! ### Dyadic counts for diagonal ternary forms -/

/-- Coordinates of $\mathbb{Z}/2^k$-vectors of length $3$ as triples. -/
def fin3Eq (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun x := (x 0, x 1, x 2)
  invFun y := ![y.1, y.2.1, y.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

/-- The number of triples $y \in (\mathbb{Z}/2^k)^3$ with $a y_0^2 + b y_1^2 + c y_2^2 = t$. -/
def card3Z (a b c : ℤ) (k : ℕ) (t : ZMod (2 ^ k)) : ℕ :=
  Fintype.card {y : ZMod (2 ^ k) × ZMod (2 ^ k) × ZMod (2 ^ k) //
    (a : ZMod (2 ^ k)) * y.1 ^ 2 + (b : ZMod (2 ^ k)) * y.2.1 ^ 2 + (c : ZMod (2 ^ k)) * y.2.2 ^ 2 = t}

/-- The number of such triples that are not all even (primitive), mod $8$. -/
def prim3 (a b c : ℤ) (t : ZMod (2 ^ 3)) : ℕ :=
  (Finset.univ.filter (fun y : ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) =>
    (a : ZMod (2 ^ 3)) * y.1 ^ 2 + (b : ZMod (2 ^ 3)) * y.2.1 ^ 2 + (c : ZMod (2 ^ 3)) * y.2.2 ^ 2 = t ∧
      ¬ (y.1.val % 2 = 0 ∧ y.2.1.val % 2 = 0 ∧ y.2.2.val % 2 = 0))).card

theorem repCount_diag3_eq_card (a b c : ℤ) (k : ℕ) (m : ℤ) :
    LocalDensity.repCount (QuadForm.diag ![a, b, c]) 2 k m = card3Z a b c k (m : ZMod (2 ^ k)) := by
  unfold LocalDensity.repCount card3Z
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr ((fin3Eq _).subtypeEquiv fun x => ?_)
  show _ ↔ (a : ZMod (2 ^ k)) * x 0 ^ 2 + (b : ZMod (2 ^ k)) * x 1 ^ 2 + (c : ZMod (2 ^ k)) * x 2 ^ 2 = m
  simp only [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three]
  simp
  constructor <;> intro h <;> linear_combination h


set_option maxRecDepth 100000 in
theorem enum_sumSq_odd : ∀ t : ZMod (2 ^ 3), t.val % 2 = 1 →
    card3Z 1 1 1 3 t = if t.val = 7 then 0 else if t.val = 3 then 64 else 96 := by
  unfold card3Z; decide +kernel

set_option maxRecDepth 100000 in
theorem enum_sumSq_two : ∀ t : ZMod (2 ^ 4), t.val % 4 = 2 → card3Z 1 1 1 4 t = 384 := by
  unfold card3Z; decide +kernel

set_option maxRecDepth 100000 in
theorem enum_qInd_odd : ∀ t : ZMod (2 ^ 3), t.val % 2 = 1 →
    card3Z 1 1 (-1) 3 t = if t.val = 1 then 128 else if t.val = 5 then 64 else 32 := by
  unfold card3Z; decide +kernel

set_option maxRecDepth 100000 in
theorem enum_qInd_two : ∀ t : ZMod (2 ^ 4), t.val % 4 = 2 → card3Z 1 1 (-1) 4 t = 128 := by
  unfold card3Z; decide +kernel

set_option maxRecDepth 100000 in
theorem enum_qInd_prim : ∀ t : ZMod (2 ^ 3), t.val % 4 = 0 → prim3 1 1 (-1) t = 64 := by
  unfold prim3; decide +kernel

theorem odd_not_dvd_two {a : ℤ} (h : Odd a) : ¬ (2 : ℤ) ∣ a := by
  obtain ⟨t, rfl⟩ := h; omega

theorem diag3_map (a b c : ℤ) :
    (QuadForm.diag ![a, b, c]).map (Int.castRingHom ℤ_[2]) = QuadForm.diag ![(a : ℤ_[2]), b, c] := by
  rw [diag_map_padic]; congr 1; funext i; fin_cases i <;> simp

theorem repCount_padic_diag3 (a b c : ℤ) (k : ℕ) (m : ℤ) :
    DVR.repCount (QuadForm.diag ![(a : ℤ_[2]), b, c]) 2 k (m : ℤ_[2]) = card3Z a b c k (m : ZMod (2 ^ k)) := by
  have := (repCount_eq_padic (QuadForm.diag ![a, b, c]) 2 ∅ k m).1
  rw [diag3_map] at this
  simp only [Nat.cast_ofNat] at this
  rw [← this, repCount_diag3_eq_card]

theorem units3 {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    ∀ i : Fin 3, ¬ (2 : ℤ_[2]) ∣ (![(a : ℤ_[2]), b, c]) i := by
  intro i; fin_cases i
  · exact padic_two_not_dvd_odd (odd_not_dvd_two ha)
  · exact padic_two_not_dvd_odd (odd_not_dvd_two hb)
  · exact padic_two_not_dvd_odd (odd_not_dvd_two hc)

/-- $\beta_2$ of a unit diagonal ternary form at odd $m$: $r_8(m)/8^2$. -/
theorem localDensity_diag3_two_odd {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) {m : ℤ}
    (hm : Odd m) :
    localDensity (QuadForm.diag ![a, b, c]) 2 m = (card3Z a b c 3 (m : ZMod (2 ^ 3)) : ℝ) / 8 ^ 2 := by
  have hπ := padic_two_irreducible
  rw [localDensity_eq_padic, diag3_map, Nat.cast_ofNat,
    DVR.localDensity_unit_diag _ 2 hπ (units3 ha hb hc) 1 padic_two_ord
      (padic_two_not_dvd_odd (odd_not_dvd_two hm)),
    repCount_padic_diag3, q_padicInt]
  norm_num

/-- $\beta_2$ of a unit diagonal ternary form at $m \equiv 2 \bmod 4$: $r_{16}(m)/16^2$. -/
theorem localDensity_diag3_two_two {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) {m : ℤ}
    (hm : m % 4 = 2) :
    localDensity (QuadForm.diag ![a, b, c]) 2 m = (card3Z a b c 4 (m : ZMod (2 ^ 4)) : ℝ) / 16 ^ 2 := by
  have hπ := padic_two_irreducible
  have h2 : ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ (m : ℤ_[2]) := by
    have := padic_pow_dvd_int_iff 2 (1 + 1) m
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num; omega
  have h := DVR.localDensity_eq_level_J _ 2 hπ ∅ 0
    (DVR.isJordanFormW_diag_unit _ hπ (units3 ha hb hc)) 1 padic_two_ord 0 (fun _ => le_rfl) h2 4
    (by norm_num)
  rw [localDensity_eq_padic, diag3_map, Nat.cast_ofNat, h, repCount_padic_diag3, q_padicInt]
  norm_num

/-- The primitive-count step for a unit diagonal ternary form over $\mathbb{Z}_2$:
$\beta_2(m) = r^*_8(m)/2^6 + [4 \mid m]\,\beta_2(m/4)/2$ for $m \ne 0$. -/
theorem localDensity_diag3_two_step {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) (m : ℤ)
    (hm : m ≠ 0) :
    localDensity (QuadForm.diag ![a, b, c]) 2 m = (prim3 a b c (m : ZMod (2 ^ 3)) : ℝ) / 2 ^ 6 +
      if (4 : ℤ) ∣ m then localDensity (QuadForm.diag ![a, b, c]) 2 (m / 4) / 2 else 0 := by
  have hπ := padic_two_irreducible
  have hJ := DVR.isJordanFormW_diag_unit _ hπ (units3 ha hb hc)
  have hm' : (m : ℤ_[2]) ≠ 0 := by exact_mod_cast hm
  have hprim : LocalDensity.repCountOf (QuadForm.diag ![a, b, c]) 2 3 m (fun x => ¬ IsZeroType 2 3 x) =
      prim3 a b c (m : ZMod (2 ^ 3)) := by
    classical
    unfold LocalDensity.repCountOf prim3
    have key : ∀ x : Fin 3 → ZMod (2 ^ 3),
        ((QuadForm.diag ![a, b, c]).evalIn (ZMod (2 ^ 3)) x = ((m : ℤ) : ZMod (2 ^ 3)) ∧
          ¬ IsZeroType 2 3 x) ↔
        ((a : ZMod (2 ^ 3)) * (fin3Eq _ x).1 ^ 2 + (b : ZMod (2 ^ 3)) * (fin3Eq _ x).2.1 ^ 2 +
            (c : ZMod (2 ^ 3)) * (fin3Eq _ x).2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) ∧
          ¬ ((fin3Eq _ x).1.val % 2 = 0 ∧ (fin3Eq _ x).2.1.val % 2 = 0 ∧ (fin3Eq _ x).2.2.val % 2 = 0)) := by
      intro x
      refine and_congr ?_ (not_congr ?_)
      · show _ ↔ (a : ZMod (2 ^ 3)) * x 0 ^ 2 + (b : ZMod (2 ^ 3)) * x 1 ^ 2 + (c : ZMod (2 ^ 3)) * x 2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3))
        simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three]
        constructor <;> intro h <;> linear_combination h

      · simp only [IsZeroType, fin3Eq, ← zmod8_two_dvd_iff']
        constructor
        · intro h; exact ⟨h 0, h 1, h 2⟩
        · rintro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption
    rw [Nat.card_congr ((Equiv.subtypeEquivRight key).trans ((fin3Eq _).subtypeEquiv
        (q := fun y : ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) =>
          (a : ZMod (2 ^ 3)) * y.1 ^ 2 + (b : ZMod (2 ^ 3)) * y.2.1 ^ 2 + (c : ZMod (2 ^ 3)) * y.2.2 ^ 2
            = ((m : ℤ) : ZMod (2 ^ 3)) ∧
            ¬ (y.1.val % 2 = 0 ∧ y.2.1.val % 2 = 0 ∧ y.2.2.val % 2 = 0))
        (fun _ => Iff.rfl))),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [localDensity_eq_padic, diag3_map, Nat.cast_ofNat]
  rw [DVR.localDensity_eq_prim_add_zero_J _ 2 hπ ∅ 0 hJ 1 padic_two_ord 0 (fun _ => le_rfl) hm' 3
    (by norm_num)]
  congr 1
  · unfold DVR.primDensityAt
    rw [← hprim, repCountOf_nonZero_eq_padic, diag3_map, q_padicInt]
    simp only [Nat.cast_ofNat]
  · have hd : (2 : ℤ_[2]) ^ 2 ∣ (m : ℤ_[2]) ↔ (4 : ℤ) ∣ m := by
      have := padic_pow_dvd_int_iff 2 2 m
      simp only [Nat.cast_ofNat] at this
      rw [this]; norm_num
    by_cases h4 : (4 : ℤ) ∣ m
    · rw [if_pos (hd.2 h4), if_pos h4]
      have hdiv : DVR.divPow (2 : ℤ_[2]) 2 (m : ℤ_[2]) = ((m / 4 : ℤ) : ℤ_[2]) := by
        refine DVR.divPow_eq_of_eq_mul hπ.ne_zero ?_
        have : m = 4 * (m / 4) := (Int.mul_ediv_cancel' h4).symm
        conv_lhs => rw [this]
        push_cast; ring
      rw [hdiv, DVR.zeroFactor, q_padicInt]
      norm_num
      ring
    · rw [if_neg (fun h => h4 (hd.1 h)), if_neg h4]

/-! ### Public statements -/

theorem sumSq_three_eq : Siegel.sumSq 3 = QuadForm.diag ![(1 : ℤ), 1, 1] := by
  unfold Siegel.sumSq; congr 1; funext i; fin_cases i <;> rfl

theorem val_mod8 (m : ℤ) : (((m : ZMod (2 ^ 3)).val : ℕ) : ℤ) = m % 8 := by
  have := ZMod.val_intCast (n := 2 ^ 3) m
  simpa using this

theorem val_mod16 (m : ℤ) : (((m : ZMod (2 ^ 4)).val : ℕ) : ℤ) = m % 16 := by
  have := ZMod.val_intCast (n := 2 ^ 4) m
  simpa using this

/-- **$\beta_2(x_0^2+x_1^2+x_2^2;\, m)$ for $4 \nmid m$:** $0$ if $m \equiv 7$, $1$ if $m \equiv 3$, and $3/2$ otherwise
(mod $8$). Odd $m$: $r_8(m)/8^2$; $m \equiv 2 \bmod 4$: $r_{16}(m)/16^2$ (kernel enumeration). -/
theorem localDensity_sumSq_three_two {m : ℤ} (hm : ¬ (4 : ℤ) ∣ m) :
    LocalDensity.localDensity (Siegel.sumSq 3) 2 m =
      if m % 8 = 7 then 0 else if m % 8 = 3 then 1 else 3 / 2 := by
  have h1 : Odd (1 : ℤ) := odd_one
  rw [sumSq_three_eq]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · have h4 : m % 4 = 2 := by omega
    rw [localDensity_diag3_two_two h1 h1 h1 h4, enum_sumSq_two]
    · have : ¬ m % 8 = 7 := by omega
      have : ¬ m % 8 = 3 := by omega
      simp [*]; norm_num
    · have := val_mod16 m
      omega
  · have hodd : Odd m := Int.odd_iff.2 h
    rw [localDensity_diag3_two_odd h1 h1 h1 hodd, enum_sumSq_odd]
    · have h8 := val_mod8 m
      generalize ((m : ZMod (2 ^ 3)).val) = v at h8 ⊢
      simp only [Nat.cast_ite]
      split_ifs <;> first | omega | norm_num
    · have := val_mod8 m
      omega

/-- **$\beta_2(x_0^2+x_1^2-x_2^2;\, m)$ for $4 \nmid m$:** $2$ if $m \equiv 1$, $1$ if $m \equiv 5$, and $1/2$ otherwise
(mod $8$; also for negative $m$). Odd $m$: $r_8(m)/8^2$; $m \equiv 2 \bmod 4$: $r_{16}(m)/16^2$. -/
theorem localDensity_qInd_two {m : ℤ} (hm : ¬ (4 : ℤ) ∣ m) :
    LocalDensity.localDensity qInd 2 m =
      if m % 8 = 1 then 2 else if m % 8 = 5 then 1 else 1 / 2 := by
  have h1 : Odd (1 : ℤ) := odd_one
  have h3 : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩
  unfold qInd
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · have h4 : m % 4 = 2 := by omega
    rw [localDensity_diag3_two_two h1 h1 h3 h4, enum_qInd_two]
    · have : ¬ m % 8 = 1 := by omega
      have : ¬ m % 8 = 5 := by omega
      simp [*]; norm_num
    · have := val_mod16 m
      omega
  · have hodd : Odd m := Int.odd_iff.2 h
    rw [localDensity_diag3_two_odd h1 h1 h3 hodd, enum_qInd_odd]
    · have h8 := val_mod8 m
      generalize ((m : ZMod (2 ^ 3)).val) = v at h8 ⊢
      simp only [Nat.cast_ite]
      split_ifs <;> first | omega | norm_num
    · have := val_mod8 m
      omega

/-- $\beta_2(x_0^2+x_1^2-x_2^2;\, k^2) = 2$ for $k \ne 0$. -/
theorem localDensity_qInd_two_sq (k : ℤ) (hk : k ≠ 0) :
    LocalDensity.localDensity qInd 2 (k ^ 2) = 2 := by
  have h1 : Odd (1 : ℤ) := odd_one
  have h3 : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩
  induction' hn : k.natAbs using Nat.strong_induction_on with n ih generalizing k
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
    have hk' : k' ≠ 0 := by rintro rfl; simp at hk
    have e : (2 * k') ^ 2 = 4 * k' ^ 2 := by ring
    have hne : k' ^ 2 ≠ 0 := pow_ne_zero _ hk'
    have hdiv : 4 * k' ^ 2 / 4 = k' ^ 2 := by omega
    unfold qInd at *
    rw [e, localDensity_diag3_two_step h1 h1 h3 _ (by omega), if_pos ⟨_, rfl⟩, hdiv,
      ih k'.natAbs (by omega) k' hk' rfl, enum_qInd_prim]
    · norm_num
    · have := val_mod8 (4 * k' ^ 2)
      generalize k' ^ 2 = s at *
      omega
  · have hk2 : k ^ 2 % 8 = 1 := by
      have : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
      rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
    rw [localDensity_qInd_two (by omega)]
    simp [hk2]



/-! ### Odd primes -/

theorem qInd_units (p : ℕ) [Fact p.Prime] : ∀ i : Fin 3, ¬ (p : ℤ) ∣ (![1, 1, -1] : Fin 3 → ℤ) i := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := fun h => by
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this)
  intro i; fin_cases i
  · simpa using hp1
  · simpa using hp1
  · simpa using hp1

/-- The recursion (5.7) for $x_0^2+x_1^2-x_2^2$ at odd $p$:
$\beta_p(p^2T) = (1 - p^{-2}) + \beta_p(T)/p$ for $T \ne 0$. -/
theorem localDensity_qInd_odd_sq_mul (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (T : ℤ) (hT : T ≠ 0) :
    LocalDensity.localDensity qInd p ((p : ℤ) ^ 2 * T) =
      (1 - 1 / (p : ℝ) ^ 2) + LocalDensity.localDensity qInd p T / p := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hnd : qInd.Nondegenerate := LocalDensity.nondegenerate_diag _ (by intro i; fin_cases i <;> simp)
  have h := localDensityOf_nonZero_eq qInd hnd p (by norm_num) T hT
  unfold qInd at h hnd
  rw [localDensityOf_nonZero_diag_sq _ p hp (qInd_units p), (table1_three 1 1 (-1) p hp
    (qInd_units p 0) (qInd_units p 1) (qInd_units p 2) 1 (qInd_units p 0)).1] at h
  unfold qInd
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl, pow_one] at h
  push_cast at h
  field_simp at h ⊢
  linarith

/-- $\beta_p(x_0^2+x_1^2-x_2^2;\, k^2) = 1 + 1/p$ for odd $p$ and $k \ne 0$. -/
theorem localDensity_qInd_odd_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℤ) (hk : k ≠ 0) :
    LocalDensity.localDensity qInd p (k ^ 2) = 1 + 1 / (p : ℝ) := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  induction' hn : k.natAbs using Nat.strong_induction_on with n ih generalizing k
  by_cases hd : (p : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    have hk' : k' ≠ 0 := by rintro rfl; simp at hk
    have hlt : k'.natAbs < n := by
      rw [← hn, Int.natAbs_mul]
      have := hpp.two_le
      simp only [Int.natAbs_natCast]
      have : 0 < k'.natAbs := Int.natAbs_pos.2 hk'
      nlinarith
    rw [show ((p : ℤ) * k') ^ 2 = (p : ℤ) ^ 2 * k' ^ 2 by ring,
      localDensity_qInd_odd_sq_mul p hp _ (pow_ne_zero _ hk'), ih _ hlt k' hk' rfl]
    field_simp
    ring
  · have hnd : ¬ (p : ℤ) ∣ k ^ 2 := fun h => hd (Prime.dvd_of_dvd_pow (Nat.prime_iff_prime_int.1 hpp) h)
    have h := localDensity_unit ![1, 1, -1] p hp (qInd_units p) (k ^ 2) hnd
    have t := (table1_three 1 1 (-1) p hp (qInd_units p 0) (qInd_units p 1) (qInd_units p 2) (k ^ 2) hnd).2
    have hk0 : (k : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hl : legendreSym p (-(1 * 1 * -1 * k ^ 2)) = 1 := by
      have e : (-(1 * 1 * -1 * k ^ 2) : ℤ) = k * k := by ring
      rw [e, legendreSym.mul]
      have := legendreSym.sq_one p hk0
      rw [pow_two] at this
      exact this
    rw [hl] at t
    unfold qInd
    rw [h]
    simp only [show (3 : ℕ) - 1 = 2 from rfl]
    have t' : (LocalDensity.repCount (QuadForm.diag ![1, 1, -1]) p 1 (k ^ 2) : ℝ) = (p : ℝ) ^ 2 + p := by
      have := congrArg (fun z : ℤ => (z : ℝ)) t
      simpa using this
    rw [t']
    field_simp

/-- **$\beta_p(x_0^2+x_1^2-x_2^2;\, k^2)$ for $k \ne 0$:** $2$ if $p = 2$ and $1 + 1/p$ otherwise (equal to
$\beta_p(1)$). -/
theorem localDensity_qInd_sq (p : ℕ) [Fact p.Prime] {k : ℤ} (hk : k ≠ 0) :
    LocalDensity.localDensity qInd p (k ^ 2) = if p = 2 then 2 else 1 + 1 / (p : ℝ) := by
  by_cases h : p = 2
  · subst h
    simp [localDensity_qInd_two_sq k hk]
  · simp [h, localDensity_qInd_odd_sq p h k hk]

end QuadFormsKB.Tamagawa.Classical
