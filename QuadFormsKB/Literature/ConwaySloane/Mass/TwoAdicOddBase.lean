/-
# The 2-adic density of a unary form

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §12, p. 281, and Table 2, p. 264 (bibliography key `conwaysloane1988`).

**Proves** `card_sq_eq_one`: modulo $2^r$, $r \ge 3$, the equation $x^2 = 1$ has exactly the four solutions
$\pm1$, $\pm1 + 2^{r-1}$; hence `countN_unary` ($N_r(\langle u\rangle) = 4$ for odd $u$) and `alphaP_unary`:
$\alpha_2(\langle u\rangle) = 4$, i.e. $m_2(\langle u\rangle) = \frac14 = \frac12\cdot\frac12\cdot M_2(0+)$, the value of (3)
for a single constituent $1_u^{\pm1}$ (bound $f_{1/2}$ and $f_2$, free $f_1$ of species $0+$). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRho

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix

variable {r : ℕ}

theorem pow_two_sub_one (hr : 1 ≤ r) : (2 : ℤ) ^ r = 2 * 2 ^ (r - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- An integer $c$ with $0 < |c| < 2^r$ is not divisible by $2^r$. -/
theorem not_dvd_of_small {c : ℤ} (h0 : c ≠ 0) (h1 : |c| < 2 ^ r) : ¬ (2 : ℤ) ^ r ∣ c := by
  intro h
  have := Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr h)
  linarith

/-- The four square roots of $1$ modulo $2^r$, $r \ge 3$, as integers. -/
theorem sq_eq_one_cases (hr : 3 ≤ r) {n : ℤ} (h : (2 : ℤ) ^ r ∣ n ^ 2 - 1) :
    (2 : ℤ) ^ r ∣ n - 1 ∨ (2 : ℤ) ^ r ∣ n + 1 ∨ (2 : ℤ) ^ r ∣ n - 1 - 2 ^ (r - 1) ∨
      (2 : ℤ) ^ r ∣ n + 1 - 2 ^ (r - 1) := by
  -- `n` is odd
  have hodd : ¬ 2 ∣ n := by
    rintro ⟨k, rfl⟩
    have h1 : (2 : ℤ) ∣ (2 * k) ^ 2 - 1 := (dvd_pow_self 2 (by omega : r ≠ 0)).trans h
    have h2 : (2 : ℤ) ∣ 2 * (2 * k ^ 2) := dvd_mul_right _ _
    have h3 := dvd_sub h2 h1
    ring_nf at h3
    norm_num at h3
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  -- `2^{r-2}` divides `m (m + 1)`, a product of coprime factors
  have hr2 : (2 : ℤ) ^ r = 4 * 2 ^ (r - 2) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h' : (2 : ℤ) ^ (r - 2) ∣ m * (m + 1) := by
    rw [hr2] at h
    have e : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
    rw [e] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h
  have hcase : (2 : ℤ) ^ (r - 2) ∣ m ∨ (2 : ℤ) ^ (r - 2) ∣ m + 1 := by
    rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- `m + 1` is odd
      left
      have hc : IsCoprime ((2 : ℤ) ^ (r - 2)) (m + 1) :=
        IsCoprime.pow_left ⟨k + 1, -1, by rw [hk]; ring⟩
      exact hc.dvd_of_dvd_mul_right h'
    · right
      have hc : IsCoprime ((2 : ℤ) ^ (r - 2)) m := IsCoprime.pow_left ⟨k + 1, -1, by rw [hk]; ring⟩
      exact hc.dvd_of_dvd_mul_left h'
  have hr1 : (2 : ℤ) ^ (r - 1) = 2 * 2 ^ (r - 2) := by rw [← pow_succ']; congr 1; omega
  have hr' : (2 : ℤ) ^ r = 2 * 2 ^ (r - 1) := pow_two_sub_one (by omega)
  rcases hcase with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n - 1 = 2 m = 2^{r-1} k`
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left; exact ⟨j, by rw [hr', hr1, hk, hj]; ring⟩
    · right; right; left; exact ⟨j, by rw [hr', hr1, hk, hj]; ring⟩
  · -- `n + 1 = 2 (m + 1) = 2^{r-1} k`
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · right; left; exact ⟨j, by rw [hr', hr1, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hk, hj]; ring⟩
    · right; right; right
      have e : 2 * m + 1 + 1 - 2 ^ (r - 1) = 2 * (m + 1) - 2 * 2 ^ (r - 2) := by rw [hr1]; ring
      exact ⟨j, by rw [e, hr', hr1, hk, hj]; ring⟩

theorem intCast_ne_of_small {c d : ℤ} (h0 : d - c ≠ 0) (h1 : |d - c| < 2 ^ r) :
    ((c : ℤ) : ZMod (2 ^ r)) ≠ ((d : ℤ) : ZMod (2 ^ r)) := by
  intro h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  exact not_dvd_of_small h0 h1 (by exact_mod_cast h)

/-- **The square roots of $1$ modulo $2^r$** ($r \ge 3$): there are exactly four. -/
theorem card_sq_eq_one (hr : 3 ≤ r) : Nat.card {x : ZMod (2 ^ r) // x * x = 1} = 4 := by
  classical
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  set h : ℤ := 2 ^ (r - 1)
  have hr' : (2 : ℤ) ^ r = 2 * h := pow_two_sub_one (by omega)
  have hh : (4 : ℤ) ≤ h := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  set S : Finset (ZMod (2 ^ r)) := {((1 : ℤ) : ZMod (2 ^ r)), ((-1 : ℤ) : ZMod (2 ^ r)),
    ((1 + h : ℤ) : ZMod (2 ^ r)), ((-1 + h : ℤ) : ZMod (2 ^ r))}
  have hmem : ∀ x : ZMod (2 ^ r), x * x = 1 ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      set n : ℤ := (x.val : ℤ)
      have hxn : x = ((n : ℤ) : ZMod (2 ^ r)) := by simp [n]
      have hd : (2 : ℤ) ^ r ∣ n ^ 2 - 1 := by
        have : ((n ^ 2 - 1 : ℤ) : ZMod (2 ^ r)) = 0 := by push_cast; rw [← hxn, sq, hx, sub_self]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this; exact_mod_cast this
      have e : ∀ c : ℤ, (2 : ℤ) ^ r ∣ n - c → x = ((c : ℤ) : ZMod (2 ^ r)) := fun c hc => by
        rw [hxn, ZMod.intCast_eq_intCast_iff_dvd_sub]; exact_mod_cast (dvd_sub_comm.mp hc)
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases sq_eq_one_cases hr hd with h1 | h1 | h1 | h1
      · exact Or.inl (e 1 h1)
      · exact Or.inr (Or.inl (e (-1) (by simpa using h1)))
      · exact Or.inr (Or.inr (Or.inl (e (1 + h) (by rw [show n - (1 + h) = n - 1 - h by ring]; exact h1))))
      · exact Or.inr (Or.inr (Or.inr (e (-1 + h) (by rw [show n - (-1 + h) = n + 1 - h by ring]; exact h1))))
    · intro hx
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      have sq1 : ∀ c : ℤ, (2 : ℤ) ^ r ∣ c * c - 1 → ((c : ℤ) : ZMod (2 ^ r)) * (c : ZMod (2 ^ r)) = 1 := by
        intro c hc
        have : ((c * c - 1 : ℤ) : ZMod (2 ^ r)) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hc
        push_cast at this
        exact sub_eq_zero.mp this
      have hhh : (2 : ℤ) ^ r ∣ h * h := by
        rw [hr']
        exact mul_dvd_mul (dvd_trans (by norm_num) (show (4 : ℤ) ∣ h from ⟨2 ^ (r - 3), by
          simp only [h]; rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩)) dvd_rfl
      rcases hx with rfl | rfl | rfl | rfl
      · exact sq1 1 (by simp)
      · exact sq1 (-1) (by simp)
      · exact sq1 (1 + h) (by
          rw [show (1 + h) * (1 + h) - 1 = 2 * h + h * h by ring, ← hr']; exact dvd_add dvd_rfl hhh)
      · exact sq1 (-1 + h) (by
          rw [show (-1 + h) * (-1 + h) - 1 = -(2 * h) + h * h by ring, ← hr']
          exact dvd_add (dvd_neg.mpr dvd_rfl) hhh)
  have hcard : S.card = 4 := by
    have hlt : ∀ c : ℤ, 0 < c → c < 2 * h → |c| < 2 ^ r := fun c h0 h1 => by
      rw [abs_of_pos h0, hr']; exact h1
    have hlt' : ∀ c : ℤ, 0 < c → c < 2 * h → |-c| < 2 ^ r := fun c h0 h1 => by
      rw [abs_neg]; exact hlt c h0 h1
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact intCast_ne_of_small (by linarith) (by rw [show -1 + h - (1 + h) = -2 by ring]; exact hlt' 2 (by norm_num) (by linarith))
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨intCast_ne_of_small (by linarith) ?_, intCast_ne_of_small (by linarith) ?_⟩
      · rw [show 1 + h - -1 = 2 + h by ring]; exact hlt _ (by linarith) (by linarith)
      · rw [show -1 + h - -1 = h by ring]; exact hlt _ (by linarith) (by linarith)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨intCast_ne_of_small (by norm_num) ?_, intCast_ne_of_small (by linarith) ?_,
        intCast_ne_of_small (by linarith) ?_⟩
      · rw [show (-1 : ℤ) - 1 = -2 by ring]; exact hlt' 2 (by norm_num) (by linarith)
      · rw [show 1 + h - 1 = h by ring]; exact hlt _ (by linarith) (by linarith)
      · rw [show -1 + h - 1 = h - 2 by ring]; exact hlt _ (by linarith) (by linarith)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hcard]
  congr 1
  ext x
  simp [hmem x]

/-- **$N_r(\langle u\rangle) = 4$** for odd $u$ and $r \ge 3$. -/
theorem countN_unary (hr : 3 ≤ r) {u : ℤ} (hu : ¬ 2 ∣ u) : countN 2 r !![u] = 4 := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  have huu : IsUnit (u : ZMod (2 ^ r)) := isUnit_odd hu
  unfold countN
  rw [← card_sq_eq_one hr]
  refine Nat.card_congr
    { toFun := fun X => ⟨X.1 0 0, ?_⟩
      invFun := fun x => ⟨!![x.1], ?_⟩
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun x => Subtype.ext rfl }
  · have h := congrFun (congrFun X.2 0) 0
    simp [Matrix.mul_apply] at h
    have h' : (X.1 0 0 * X.1 0 0) * (u : ZMod (2 ^ r)) = 1 * u := by rw [one_mul]; linear_combination h
    exact huu.mul_left_injective h'
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    rw [show x.1 * u * x.1 = (x.1 * x.1) * u by ring, x.2, one_mul]
  · ext i j
    fin_cases i; fin_cases j
    rfl

/-- **$\alpha_2(\langle u\rangle) = 4$** for odd $u$ (Conway–Sloane 1988, §12, p. 281). -/
@[kb "conwaysloane1988" "§12, p. 281 (the 2-adic density of a unary form)"]
theorem alphaP_unary {u : ℤ} (hu : ¬ 2 ∣ u) : alphaP 2 !![u] = 4 := by
  have hs : (!![u] : Matrix (Fin 1) (Fin 1) ℤ).IsSymm := by ext i j; fin_cases i; fin_cases j; rfl
  have hd : (!![u] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_one_of]; rintro rfl; exact hu (dvd_zero _)
  obtain ⟨r0, h0⟩ := alphaP_stabilizes Nat.prime_two hs hd
  rw [← h0 (max r0 3) (le_max_left _ _), countN_unary (le_max_right _ _) hu]
  simp

end QuadFormsKB.ConwaySloane.Mass.Two
