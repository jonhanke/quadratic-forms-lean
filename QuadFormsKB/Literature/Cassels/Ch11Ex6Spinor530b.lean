/-
# Cassels, Chapter 11, Example 6 (i), (ii): local facts at $2$ for $x^2 + y^2 + 16z^2$

For a place $v \mid 2$ of $\mathbb Q$ and $\Lambda = \mathbb Z^3$ with $f = x_0^2 + x_1^2 + 16x_2^2$:
* `mem_theta6_iff`: $\theta(\Lambda_v) = \{a : a\mathbb Q_v^{\times2} \in H\}$, $H = \{1, 2, 5, 10\}$ (`H6`). The upper bound
  is `theta2_le_A6_gen` (`Ch11Ex6Spinor530.lean`); the lower bound: the symmetries in $e_0$ (value $1$), $e_0 + e_1$
  (value $2$; $B(y, z)/Q(y) = z_0 + z_1$ is integral) and $e_0 + 2e_1$ (value $5$, a unit) stabilize $\mathbb Z_v^3$.
* `three_add_four_not_mem_H6`, `one_add_four_mem_H6`: for $k \in \mathbb Z_2$, $1 + 4k \in H$ and $3 + 4k \notin H$
  (this includes $-1 \notin H$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex6Spinor530

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Ex11

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Theta6

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- Integrality: $f$ is integral on $\mathbb Z_v^3$. -/
theorem hint6 : ∀ x ∈ loc v (stdLat : Lat ℚ 3).1, Valued.v ((csQ A6).evalIn F2 x) ≤ 1 := by
  intro x hx
  have hL : loc v (stdLat : Lat ℚ 3).1 = std v := loc_intVec v
  rw [hL] at hx
  convert valued_evalIn_le_one_int v (Cassels.Ch8Ex2.gramForm A6) hx using 3
  exact Subsingleton.elim _ _

/-- The symmetries in $e_0$ and $e_0 + e_1$ give $2 \in \theta(\Lambda_v)$, $v \mid 2$. Argument `h2`: $v \mid 2$. -/
theorem two_mem_theta6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    Units.mk0 (2 : F2) two_ne_zero ∈ localSpinorNormGroup (csQ A6) A6_nondeg v stdLat := by
  have hL : loc v (stdLat : Lat ℚ 3).1 = std v := loc_intVec v
  have hxv : (csQ A6).evalIn F2 (Pi.single 0 1) = 1 := by
    rw [csQ_A6_eval]; simp
  have hyv : (csQ A6).evalIn F2 ![1, 1, 0] = 2 := by
    rw [csQ_A6_eval]; norm_num
  have hx0 : (csQ A6).evalIn F2 (Pi.single 0 1) ≠ 0 := by rw [hxv]; exact one_ne_zero
  have hy0 : (csQ A6).evalIn F2 ![1, 1, 0] ≠ 0 := by rw [hyv]; exact two_ne_zero
  have hxM : (Pi.single 0 1 : Fin 3 → F2) ∈ loc v (stdLat : Lat ℚ 3).1 := by
    rw [hL]; exact single_mem_std 0 (by simp)
  have hyM : (![1, 1, 0] : Fin 3 → F2) ∈ loc v (stdLat : Lat ℚ 3).1 := by
    rw [hL, mem_std_iff]
    intro i; fin_cases i <;> simp
  have hxs := symm_mem_locStabV_of_unit stdLat hint6 hxM (by rw [hxv, map_one])
  have hys : symm (csQ A6) F2 ![1, 1, 0] ∈ locStabV (csQ A6) v stdLat := by
    show locAct v (symm (csQ A6) F2 ![1, 1, 0] : GL (Fin 3) F2) (loc v (stdLat : Lat ℚ 3).1) =
      loc v (stdLat : Lat ℚ 3).1
    refine locAct_symm_eq hyM hy0 fun z hz => ?_
    rw [hL, mem_std_iff] at hz
    have hq : qbil (csQ A6) F2 ![1, 1, 0] z = 2 * (z 0 + z 1) := by
      rw [qbil_eq_polar, csQ_A6_eval, csQ_A6_eval, csQ_A6_eval]
      simp
      ring
    rw [hq, hyv, map_mul]
    have hle : Valued.v (z 0 + z 1) ≤ 1 := Valuation.map_add_le _ (hz 0) (hz 1)
    calc Valued.v (2 : F2) * Valued.v (z 0 + z 1) ≤ Valued.v (2 : F2) * 1 := mul_le_mul_right hle _
      _ = Valued.v (2 : F2) := mul_one _
  refine mem_localSpinorNormGroup_of_symm_pair A6_nondeg stdLat hx0 hy0 hxs hys (Units.mk0 2 two_ne_zero) ?_
  rw [hxv, hyv, one_mul, sqClassOf_of_ne_zero two_ne_zero]

/-- The symmetries in $e_0$ and $e_0 + 2e_1$ give $5 \in \theta(\Lambda_v)$, $v \mid 2$. Argument `h2`: $v \mid 2$. -/
theorem five_mem_theta6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    Units.mk0 (5 : F2) (by norm_num) ∈ localSpinorNormGroup (csQ A6) A6_nondeg v stdLat := by
  have hp2 := (two_mem_iff_natGenerator v).mp h2
  have hL : loc v (stdLat : Lat ℚ 3).1 = std v := loc_intVec v
  have h5 : Valued.v (5 : F2) = 1 := by
    have := valued_natCast_eq_one' (v := v) (m := 5) (by rw [hp2]; norm_num)
    simpa using this
  have hxv : (csQ A6).evalIn F2 (Pi.single 0 1) = 1 := by
    rw [csQ_A6_eval]; simp
  have hyv : (csQ A6).evalIn F2 ![1, 2, 0] = 5 := by
    rw [csQ_A6_eval]; simp; norm_num
  have hx0 : (csQ A6).evalIn F2 (Pi.single 0 1) ≠ 0 := by rw [hxv]; exact one_ne_zero
  have hy0 : (csQ A6).evalIn F2 ![1, 2, 0] ≠ 0 := by rw [hyv]; norm_num
  have hxM : (Pi.single 0 1 : Fin 3 → F2) ∈ loc v (stdLat : Lat ℚ 3).1 := by
    rw [hL]; exact single_mem_std 0 (by simp)
  have hyM : (![1, 2, 0] : Fin 3 → F2) ∈ loc v (stdLat : Lat ℚ 3).1 := by
    rw [hL, mem_std_iff]
    intro i; fin_cases i
    · simp
    · show Valued.v (2 : F2) ≤ 1
      rw [show (2 : F2) = 1 + 1 by norm_num]
      exact (Valuation.map_add _ _ _).trans (by simp)
    · simp
  have hxs := symm_mem_locStabV_of_unit stdLat hint6 hxM (by rw [hxv, map_one])
  have hys := symm_mem_locStabV_of_unit stdLat hint6 hyM (by rw [hyv, h5])
  refine mem_localSpinorNormGroup_of_symm_pair A6_nondeg stdLat hx0 hy0 hxs hys (Units.mk0 5 (by norm_num)) ?_
  rw [hxv, hyv, one_mul, sqClassOf_of_ne_zero (by norm_num)]

/-- **The local spinor norm group of $\mathbb Z_v^3$ for $f = x_0^2 + x_1^2 + 16x_2^2$, $v \mid 2$**:
$a \in \theta(\Lambda_v)$ iff the square class of $a$ lies in $H = \{1, 2, 5, 10\}$. Arguments: `h2` ($v \mid 2$),
`a` the unit of $\mathbb Q_v$. -/
theorem mem_theta6_iff (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a : F2ˣ) :
    a ∈ localSpinorNormGroup (csQ A6) A6_nondeg v stdLat ↔ SqClass.mk a ∈ H6 v := by
  constructor
  · exact theta2_le_A6_gen h2 a
  · intro ha
    have hle : H6 v ≤ (locStabV (csQ A6) v stdLat ⊓ Tamagawa.soSub (csQ A6) (v.adicCompletion ℚ)).map
        (spinorNormHom (csQ A6) (v.adicCompletion ℚ) A6_nondeg) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro c (rfl | rfl)
      · have := two_mem_theta6 h2
        rw [sqClassOf_of_ne_zero two_ne_zero]
        exact this
      · have := five_mem_theta6 h2
        rw [sqClassOf_of_ne_zero (by norm_num)]
        exact this
    exact hle ha

/-! ### $1 + 4k \in H$ and $3 + 4k \notin H$ -/

/-- $1 + 4k \in H$ for $k \in \mathbb Z_2$. -/
theorem one_add_four_mem_H6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : 𝔬) : sqClassOf (1 + 4 * (k : F2)) ∈ H6 v := by
  obtain ⟨d, s, hd, hs, e⟩ := onePlusFour h2 k
  exact mem_H6_of_eq (by rcases hd with rfl | rfl <;> simp) hs e

theorem coe_two6 : ((2 : 𝔬) : F2) = 2 := map_ofNat (𝔬).subtype 2

theorem coe_three6 : ((3 : 𝔬) : F2) = 3 := map_ofNat (𝔬).subtype 3

theorem coe_four6 : ((4 : 𝔬) : F2) = 4 := map_ofNat (𝔬).subtype 4

theorem coe_five6 : ((5 : 𝔬) : F2) = 5 := map_ofNat (𝔬).subtype 5

/-- $(3 + 4k)d$, $d \in \{1, 2, 5, 10\}$, is not a square in $\mathbb Z_2$. -/
theorem not_sq_three_add_four (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : 𝔬) :
    (∀ r : 𝔬, (3 + 4 * k) ≠ r * r) ∧ (∀ r : 𝔬, (3 + 4 * k) * 2 ≠ r * r) ∧
      (∀ r : 𝔬, (3 + 4 * k) * 5 ≠ r * r) ∧ (∀ r : 𝔬, (3 + 4 * k) * (2 * 5) ≠ r * r) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
      exact one_ne_two_mul h2 (2 * m - k) (mul_left_cancel₀ two_ne_zero_O (by linear_combination hr + hm))
    · exact one_ne_two_mul h2 (2 * (y ^ 2 - k) - 1) (by linear_combination hr)
  · rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
      exact one_ne_two_mul h2 (4 * (m - k) - 2) (by linear_combination hr + hm)
    · exact one_ne_two_mul h2 (y ^ 2 - 1 - 2 * k) (mul_left_cancel₀ two_ne_zero_O (by linear_combination hr))
  · rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
      exact one_ne_two_mul h2 (2 * m - 5 * k - 3) (mul_left_cancel₀ two_ne_zero_O (by linear_combination hr + hm))
    · exact one_ne_two_mul h2 (2 * y ^ 2 - 10 * k - 7) (by linear_combination hr)
  · rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
      exact one_ne_two_mul h2 (4 * m - 20 * k - 14) (by linear_combination hr + hm)
    · exact one_ne_two_mul h2 (y ^ 2 - 10 * k - 7) (mul_left_cancel₀ two_ne_zero_O (by linear_combination hr))

/-- $3 + 4k \notin H$ for $k \in \mathbb Z_2$ (for $k = -1$: $-1 \notin H$). -/
theorem three_add_four_not_mem_H6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : 𝔬) :
    sqClassOf (3 + 4 * (k : F2)) ∉ H6 v := by
  intro h
  obtain ⟨n1, n2, n5, n10⟩ := not_sq_three_add_four h2 k
  have hW : (((3 + 4 * k : 𝔬)) : F2) = 3 + 4 * (k : F2) := by
    push_cast
    rw [coe_three6, coe_four6]
  have hW0 : (3 + 4 * (k : F2)) ≠ 0 := by
    intro h0
    apply n1 0
    apply Subtype.ext
    rw [hW, h0]
    simp
  rw [H6, Subgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  have h20 : (2 : F2) ≠ 0 := two_ne_zero
  have h50 : (5 : F2) ≠ 0 := by norm_num
  rcases zpow_eq_one_or_self (sqClassOf_sq_eq_one h20) m with hm | hm <;>
    rcases zpow_eq_one_or_self (sqClassOf_sq_eq_one h50) n with hn | hn <;>
    rw [hm, hn] at hmn
  · rw [one_mul, eq_comm, sqClassOf_eq_one_iff hW0] at hmn
    refine not_isSquare_of_O (3 + 4 * k : 𝔬) n1 ?_
    rw [hW]; exact hmn
  · rw [one_mul] at hmn
    have := isSquare_of_sqClassOf_eq hW0 h50 hmn.symm
    refine not_isSquare_of_O ((3 + 4 * k) * 5 : 𝔬) n5 ?_
    rw [show ((((3 + 4 * k) * 5 : 𝔬)) : F2) = (3 + 4 * (k : F2)) * 5 by
      push_cast; rw [coe_three6, coe_four6, coe_five6]]
    exact this
  · rw [mul_one] at hmn
    have := isSquare_of_sqClassOf_eq hW0 h20 hmn.symm
    refine not_isSquare_of_O ((3 + 4 * k) * 2 : 𝔬) n2 ?_
    rw [show ((((3 + 4 * k) * 2 : 𝔬)) : F2) = (3 + 4 * (k : F2)) * 2 by
      push_cast; rw [coe_three6, coe_four6, coe_two6]]
    exact this
  · rw [← sqClassOf_mul h20 h50] at hmn
    have := isSquare_of_sqClassOf_eq hW0 (mul_ne_zero h20 h50) hmn.symm
    refine not_isSquare_of_O ((3 + 4 * k) * (2 * 5) : 𝔬) n10 ?_
    rw [show ((((3 + 4 * k) * (2 * 5) : 𝔬)) : F2) = (3 + 4 * (k : F2)) * (2 * 5) by
      push_cast; rw [coe_three6, coe_four6, coe_five6, coe_two6]]
    exact this

end Theta6

end QuadFormsKB.ConwaySloane
