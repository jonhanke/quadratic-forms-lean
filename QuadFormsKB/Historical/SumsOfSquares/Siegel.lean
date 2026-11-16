/-
# Sums of $n$ squares through Siegel's formula: the common part ($4 \le n \le 8$)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).

For $I_n = x_0^2 + \dots + x_{n-1}^2$ with $4 \le n \le 8$ and every integer $m \ge 1$,
$$r_n(m) = \beta_\infty(m)\prod_p \beta_p(m)\qquad(\texttt{repNum\_sumSq\_eq\_siegel}),$$
from two results proved unconditionally in this library: Siegel's formula in every rank $\ge 4$
(`Tamagawa.siegelFormula_int_all_ranks_uncond`) and one class in the genus of $I_n$ for $n \le 8$
(`Siegel.genusRepAvg_sumSq_of_le_eight`). This file also evaluates $\beta_\infty$ for $n = 5, 6, 7$ and the local density
at $p = 2$ when $4 \nmid m$ by counting solutions modulo $8$:
$$\beta_2(m) = \frac{\#\{\vec x \in (\mathbb Z/8)^n : x_0^2 + \dots + x_{n-1}^2 \equiv m \bmod 8\}}{8^{\,n-1}}\qquad(4 \nmid m).$$
These are the inputs of the classical formulas of Jacobi (six squares), Eisenstein and Smith (five and seven squares) in
`SumsOfSquares/SixSquares.lean` and `SumsOfSquares/OddSquares.lean`.
-/
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus
import QuadFormsKB.LocalDensity.Table2
import QuadFormsKB.LocalDensity.LowerBounds

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-! ### Siegel's formula for $I_n$, $4 \le n \le 8$ -/

/-- **$r_n(m)$ is the Siegel product for $4 \le n \le 8$:** for every integer $m \ge 1$,
$r_n(m) = \#\{\vec x \in \mathbb Z^n : x_0^2 + \dots + x_{n-1}^2 = m\} = \beta_\infty(m)\prod_p\beta_p(m)$
(`betaInf`, `eulerProduct`). Unconditional: Siegel's formula (`Tamagawa.siegelFormula_int_all_ranks_uncond`) and one
class in the genus (`Siegel.genusRepAvg_sumSq_of_le_eight`). -/
theorem repNum_sumSq_eq_siegel {n : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) {m : ℤ} (hm : 1 ≤ m) :
    (repNum (sumSq n) m : ℝ) = betaInf (sumSq n) m * eulerProduct (sumSq n) m := by
  rw [← genusRepAvg_sumSq_of_le_eight h8,
    (Tamagawa.siegelFormula_int_all_ranks_uncond h4 (sumSq n) posDef_sumSq).genusRepAvg_eq m hm]
  rfl

/-- The Euler product of $I_n$ ($n \ge 4$, $m \ne 0$) converges to `eulerProduct`. -/
theorem hasProd_eulerFactor_sumSq {n : ℕ} (h4 : 4 ≤ n) {m : ℤ} (hm : m ≠ 0) :
    HasProd (eulerFactor (sumSq n) m) (eulerProduct (sumSq n) m) :=
  hasProd_eulerProduct (sumSq n) (posDef_sumSq.nondegenerate) h4 hm

/-! ### The archimedean factor -/

theorem betaInf_sumSq (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    betaInf (sumSq n) m =
      n * (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)) / 2 * m ^ (((n : ℝ) - 2) / 2) := by
  rw [betaInf, gramDet_sumSq, Real.one_rpow, unitBallVol_eq hn, mul_one]

/-- $\beta_\infty$ of $I_5$: $\tfrac43\pi^2 m^{3/2}$. -/
theorem betaInf_sumSq_five (m : ℝ) :
    betaInf (sumSq 5) m = 4 / 3 * Real.pi ^ 2 * m ^ ((3 : ℝ) / 2) := by
  rw [betaInf_sumSq 5 (by norm_num)]
  have hΓ : Real.Gamma ((5 : ℕ) / 2 + 1 : ℝ) = 15 / 8 * Real.sqrt Real.pi := by
    rw [show ((5 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1 + 1) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hs : Real.sqrt Real.pi ^ 5 = Real.pi ^ 2 * Real.sqrt Real.pi := by
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hΓ, hs, show (((5 : ℕ) : ℝ) - 2) / 2 = 3 / 2 by norm_num]
  field_simp
  push_cast
  ring

/-- $\beta_\infty$ of $I_6$: $\tfrac12\pi^3 m^2$. -/
theorem betaInf_sumSq_six (m : ℝ) :
    betaInf (sumSq 6) m = Real.pi ^ 3 / 2 * m ^ 2 := by
  rw [betaInf_sumSq 6 (by norm_num)]
  have hΓ : Real.Gamma ((6 : ℕ) / 2 + 1 : ℝ) = 6 := by
    rw [show ((6 : ℕ) : ℝ) / 2 + 1 = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hs : Real.sqrt Real.pi ^ 6 = Real.pi ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hΓ, hs, show (((6 : ℕ) : ℝ) - 2) / 2 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  push_cast
  ring

/-- $\beta_\infty$ of $I_7$: $\tfrac8{15}\pi^3 m^{5/2}$. -/
theorem betaInf_sumSq_seven (m : ℝ) :
    betaInf (sumSq 7) m = 8 / 15 * Real.pi ^ 3 * m ^ ((5 : ℝ) / 2) := by
  rw [betaInf_sumSq 7 (by norm_num)]
  have hΓ : Real.Gamma ((7 : ℕ) / 2 + 1 : ℝ) = 105 / 16 * Real.sqrt Real.pi := by
    rw [show ((7 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1 + 1 + 1) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hs : Real.sqrt Real.pi ^ 7 = Real.pi ^ 3 * Real.sqrt Real.pi := by
    rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hΓ, hs, show (((7 : ℕ) : ℝ) - 2) / 2 = 5 / 2 by norm_num]
  field_simp
  push_cast
  ring

/-! ### Counting solutions modulo $8$ -/

/-- The number of $\vec x \in (\mathbb Z/8)^n$ with $x_0^2 + \dots + x_{n-1}^2 = c$. -/
def sqCount8 (n : ℕ) (c : ZMod 8) : ℕ :=
  Fintype.card {x : Fin n → ZMod 8 // ∑ i, x i ^ 2 = c}

theorem sqCount8_zero (c : ZMod 8) : sqCount8 0 c = if c = 0 then 1 else 0 := by
  unfold sqCount8
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  split_ifs with h
  · subst h
    exact Fintype.card_eq_one_iff.mpr ⟨⟨finZeroElim, rfl⟩, fun x => Subtype.ext (funext finZeroElim)⟩
  · exact Fintype.card_eq_zero_iff.mpr ⟨fun x => h x.2.symm⟩

/-- Adding one variable: $N_{n+1}(c) = \sum_{y \in \mathbb Z/8} N_n(c - y^2)$. -/
theorem sqCount8_succ (n : ℕ) (c : ZMod 8) :
    sqCount8 (n + 1) c = ∑ y : ZMod 8, sqCount8 n (c - y ^ 2) := by
  classical
  unfold sqCount8
  rw [Fintype.card_congr ((Fin.consEquiv fun _ : Fin (n + 1) => ZMod 8).symm.subtypeEquiv
      (q := fun p : ZMod 8 × (Fin n → ZMod 8) => p.1 ^ 2 + ∑ i, p.2 i ^ 2 = c)
      (fun x => by simp [Fin.sum_univ_succ, Fin.consEquiv, Fin.tail]))]
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  exact propext ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩

/-- The table $N_n(c)$, $c = 0, \dots, 7$, for $n \le 7$. -/
def sqTable8 : ℕ → ZMod 8 → ℕ
  | 0 => ![1, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![2, 4, 0, 0, 2, 0, 0, 0]
  | 2 => ![8, 16, 16, 0, 8, 16, 0, 0]
  | 3 => ![32, 96, 96, 64, 32, 96, 96, 0]
  | 4 => ![128, 512, 768, 512, 384, 512, 768, 512]
  | 5 => ![3072, 2560, 5120, 5120, 3072, 3584, 5120, 5120]
  | 6 => ![32768, 24576, 30720, 40960, 32768, 24576, 34816, 40960]
  | _ => ![294912, 229376, 229376, 286720, 294912, 229376, 229376, 303104]

theorem sqTable8_step (n : ℕ) (hn : n < 7) (c : ZMod 8) :
    sqTable8 (n + 1) c = ∑ y : ZMod 8, sqTable8 n (c - y ^ 2) := by
  interval_cases n <;> revert c <;> decide

theorem sqCount8_eq (n : ℕ) (hn : n ≤ 7) (c : ZMod 8) : sqCount8 n c = sqTable8 n c := by
  induction n generalizing c with
  | zero => rw [sqCount8_zero]; revert c; decide
  | succ n ih =>
    rw [sqCount8_succ, sqTable8_step n (by omega)]
    exact Finset.sum_congr rfl fun y _ => ih (by omega) _

/-! ### The local density at $p = 2$ when $4 \nmid m$ -/

theorem sumSq_eq_diag (n : ℕ) : sumSq n = QuadForm.diag fun _ : Fin n => (1 : ℤ) := rfl

lemma not_dvd_one_sumSq {n : ℕ} (p : ℕ) [Fact p.Prime] : ∀ _ : Fin n, ¬ (p : ℤ) ∣ (1 : ℤ) := fun _ h =>
  (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)

theorem evalIn_sumSq {n : ℕ} {S : Type*} [CommRing S] (x : Fin n → S) :
    (sumSq n).evalIn S x = ∑ i, x i ^ 2 := by
  simp only [sumSq, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- **The non-Zero-type density at $p = 2$ is attained at level $3$** (Lemma 3.2 at $p = 2$):
$\beta^{\ne 0}_2(m) = r^{\ne 0}_8(m)/2^{3(n-1)}$. -/
theorem localDensityOf_nonZero_sumSq_two (n : ℕ) (m : ℤ) :
    localDensityOf (sumSq n) 2 m (fun k x => ¬ IsZeroType 2 k x) =
      (repCountOf (sumSq n) 2 3 m (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ (3 * (n - 1)) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = 3 + l := ⟨k - 3, by omega⟩
  have h := repCountGood_add_diag (fun _ : Fin n => (1 : ℤ)) 2 m 3 l (by norm_num)
  rw [isGoodType_diag_unimodular _ 2 (not_dvd_one_sumSq 2),
    isGoodType_diag_unimodular _ 2 (not_dvd_one_sumSq 2)] at h
  rw [sumSq_eq_diag, h]
  push_cast
  rw [show (3 + l) * (n - 1) = 3 * (n - 1) + (n - 1) * l by ring, pow_add]
  field_simp

/-- If $4 \nmid m$, $\beta_2(m) = N_n(m \bmod 8)/2^{3(n-1)}$, $N_n(c) = \#\{\vec x \in (\mathbb Z/8)^n : \sum x_i^2 = c\}$. -/
theorem localDensity_sumSq_two (n : ℕ) (m : ℤ) (hm : ¬ (4 : ℤ) ∣ m) :
    localDensity (sumSq n) 2 m = (sqCount8 n (m : ZMod 8) : ℝ) / 2 ^ (3 * (n - 1)) := by
  have h1 : localDensity (sumSq n) 2 m = localDensityOf (sumSq n) 2 m (fun k x => ¬ IsZeroType 2 k x) := by
    unfold localDensity localDensityOf Filter.limUnder
    refine congrArg Filter.lim (Filter.map_congr ?_)
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hm' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
    rw [repCount_eq_zero_add_nonZero, repCountZero_eq _ 2 m k hk]
    simp only [hm', ↓reduceIte, zero_add]
  rw [h1, localDensityOf_nonZero_sumSq_two]
  congr 2
  -- at level 3, with 4 ∤ m, every solution is of non-Zero type
  have hz : repCountOf (sumSq n) 2 3 m (IsZeroType 2 3) = 0 := by
    rw [repCountZero_eq _ 2 m 3 (by norm_num)]
    have hm' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
    split_ifs
    rfl
  have hsplit := repCount_eq_zero_add_nonZero (sumSq n) 2 3 m
  rw [hz, zero_add] at hsplit
  rw [← hsplit]
  unfold repCount sqCount8
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [evalIn_sumSq]

end QuadFormsKB.Historical.SumsOfSquares
