/-
# Conway–Sloane, Ch. 15, §9.7: ingredients of Corollary 22

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, Cor. 22, p. 395
(`conwaysloane1999`).

**Proves**
* The inequalities between the bounds of Thm. 20 and $d_0(n)$: `two_pow_mul_five_pow_le_twelve_pow`
  ($2^n5^{\binom n2} \le 12^{\binom n2}$, $n \ge 3$), `two_pow_mul_five_pow_le_eight_pow`
  ($2^n5^{\binom n2} \le 8^{\binom n2}$, $n \ge 4$).
* `isTractable_five_of_odd_order` (the step the book leaves out): if every prime of
  $P$ other than $5$ is tractable and $\theta(\Lambda_2)$ contains an element $c$ of order $1$ at $2$, then $5$ is
  tractable: $\Delta_2(c)$, in the kernel, has $5$-coordinate $2$, a non-residue mod $5$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Main

open NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

open scoped Classical

/-! ### Inequalities -/

theorem two_mul_five_pow_le_twelve_pow : ∀ m : ℕ, 1 ≤ m → 2 * 5 ^ m ≤ 12 ^ m
  | 0, h => by omega
  | 1, _ => by norm_num
  | m + 2, _ => by
    have := two_mul_five_pow_le_twelve_pow (m + 1) (by omega)
    rw [pow_succ 5 (m + 1), pow_succ 12 (m + 1)]
    calc 2 * (5 ^ (m + 1) * 5) = (2 * 5 ^ (m + 1)) * 5 := by ring
      _ ≤ 12 ^ (m + 1) * 12 := Nat.mul_le_mul this (by norm_num)

theorem two_mul_five_pow_le_eight_pow : ∀ m : ℕ, 2 ≤ m → 2 * 5 ^ m ≤ 8 ^ m
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by norm_num
  | m + 3, _ => by
    have := two_mul_five_pow_le_eight_pow (m + 2) (by omega)
    rw [pow_succ 5 (m + 2), pow_succ 8 (m + 2)]
    calc 2 * (5 ^ (m + 2) * 5) = (2 * 5 ^ (m + 2)) * 5 := by ring
      _ ≤ 8 ^ (m + 2) * 8 := Nat.mul_le_mul this (by norm_num)

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- $2^n5^{\binom n2} \le 12^{\binom n2}$ for $n \ge 3$. -/
theorem two_pow_mul_five_pow_le_twelve_pow : ∀ n : ℕ, 3 ≤ n → 2 ^ n * 5 ^ n.choose 2 ≤ 12 ^ n.choose 2
  | 0, h | 1, h | 2, h => by omega
  | 3, _ => by norm_num [Nat.choose]
  | n + 4, _ => by
    have ih := two_pow_mul_five_pow_le_twelve_pow (n + 3) (by omega)
    have h2 := two_mul_five_pow_le_twelve_pow (n + 3) (by omega)
    show 2 ^ (n + 3 + 1) * 5 ^ (n + 3 + 1).choose 2 ≤ 12 ^ (n + 3 + 1).choose 2
    rw [choose_two_succ (n + 3), pow_succ 2 (n + 3), pow_add 5, pow_add 12]
    calc 2 ^ (n + 3) * 2 * (5 ^ (n + 3).choose 2 * 5 ^ (n + 3))
        = (2 ^ (n + 3) * 5 ^ (n + 3).choose 2) * (2 * 5 ^ (n + 3)) := by ring
      _ ≤ 12 ^ (n + 3).choose 2 * 12 ^ (n + 3) := Nat.mul_le_mul ih h2

/-- $2^n5^{\binom n2} \le 8^{\binom n2}$ for $n \ge 4$. -/
theorem two_pow_mul_five_pow_le_eight_pow : ∀ n : ℕ, 4 ≤ n → 2 ^ n * 5 ^ n.choose 2 ≤ 8 ^ n.choose 2
  | 0, h | 1, h | 2, h | 3, h => by omega
  | 4, _ => by norm_num [Nat.choose]
  | n + 5, _ => by
    have ih := two_pow_mul_five_pow_le_eight_pow (n + 4) (by omega)
    have h2 := two_mul_five_pow_le_eight_pow (n + 4) (by omega)
    show 2 ^ (n + 4 + 1) * 5 ^ (n + 4 + 1).choose 2 ≤ 8 ^ (n + 4 + 1).choose 2
    rw [choose_two_succ (n + 4), pow_succ 2 (n + 4), pow_add 5, pow_add 8]
    calc 2 ^ (n + 4) * 2 * (5 ^ (n + 4).choose 2 * 5 ^ (n + 4))
        = (2 ^ (n + 4) * 5 ^ (n + 4).choose 2) * (2 * 5 ^ (n + 4)) := by ring
      _ ≤ 8 ^ (n + 4).choose 2 * 8 ^ (n + 4) := Nat.mul_le_mul ih h2

/-! ### $5$ is tractable when $\theta(\Lambda_2)$ has an element of odd order -/

section Five

variable {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- **$5$ is tractable** (Conway–Sloane, Cor. 22, the case $5$ intractable with $d$ odd; an argument not given in the
book): if every prime of $P$ other than $5$ is tractable and $\theta(\Lambda_2)$ contains an element $c$ with
$\lvert c\rvert_2 = \tfrac12$, then $5$ is tractable. *Proof:* $\Delta_2(c)$ is in the spinor kernel (Thm. 17); its
coordinates are $c/2$ at $2$ and $2$ at every odd $q \in P$; removing the tractable coordinates leaves $\Delta_5(2)$,
and every $5$-adic unit is a square or twice a square. -/
theorem isTractable_five_of_odd_order (hn : 3 ≤ n) (p5 p2 : P) (h5 : primeOf p5.1 = 5) (h2 : primeOf p2.1 = 2)
    (hoth : ∀ q : P, q ≠ p5 → IsTractable Q hQ L P q) {c : (p2.1.adicCompletion ℚ)ˣ}
    (hc : c ∈ localSpinorNormGroup Q hQ p2.1 L)
    (hcv : Valued.v (c : p2.1.adicCompletion ℚ) = exp (-1 : ℤ)) : IsTractable Q hQ L P p5 := by
  have hne : p5 ≠ p2 := fun e => by rw [e] at h5; omega
  have hord : ordP P p2 c = 1 := by rw [ordP, hcv]; simp
  -- the coordinates of `Δ₂(c)` away from `2`
  have hcoord : ∀ q : P, q ≠ p2 → deltaP P p2 c q = casselsDiag P (natGenUnit p2.1) q := by
    intro q hq
    rw [deltaP_apply_ne P hq, hord, zpow_one]
  have hX := deltaP_mem_casselsX P p2 c
  have hST := mem_casselsST_of_deltaP Q hQ L P hn p2 hc
  -- every coordinate other than the `5`-th is removable
  have key : (Pi.mulSingle p5 (deltaP P p2 c p5) : CasselsR P) ∈ casselsST Q hQ L P := by
    have e : (Pi.mulSingle p5 (deltaP P p2 c p5) : CasselsR P) =
        deltaP P p2 c * (∏ q ∈ Finset.univ.erase p5, Pi.mulSingle q (deltaP P p2 c q))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, Finset.mul_prod_erase Finset.univ
        (fun q => (Pi.mulSingle q (deltaP P p2 c q) : CasselsR P)) (Finset.mem_univ p5)]
      exact Finset.univ_prod_mulSingle _
    rw [e]
    exact (casselsST Q hQ L P).mul_mem hST ((casselsST Q hQ L P).inv_mem
      (Subgroup.prod_mem _ fun q hq => hoth q (Finset.ne_of_mem_erase hq) _ (hX q)))
  -- the `5`-coordinate is `2`
  have h5c : ((deltaP P p2 c p5 : (p5.1.adicCompletion ℚ)ˣ) : p5.1.adicCompletion ℚ) = 2 := by
    rw [hcoord p5 hne, casselsDiag_apply]
    simp only [natGenUnit, Units.val_mk0]
    rw [show Rat.HeightOneSpectrum.natGenerator p2.1 = 2 from h2]
    simp
  intro u hu
  rcases isSquare_or_isSquare_two_mul_of_five p5.1 h5 u hu with hsq | hsq
  · exact mulSingle_mem_of_isSquare Q hQ L P p5 hsq
  · -- `u = 2 · (2u) · 2⁻²`
    have e : u = deltaP P p2 c p5 * (deltaP P p2 c p5 * u) * (deltaP P p2 c p5)⁻¹ ^ 2 := by
      rw [inv_pow, ← mul_assoc, ← sq, mul_comm _ u, mul_inv_cancel_right]
    rw [e, Pi.mulSingle_mul, Pi.mulSingle_mul, Pi.mulSingle_pow]
    refine (casselsST Q hQ L P).mul_mem ((casselsST Q hQ L P).mul_mem key ?_)
      (Subgroup.mem_sup_left (sq_mem_casselsS Q hQ L P _))
    refine mulSingle_mem_of_isSquare Q hQ L P p5 ?_
    rw [Units.val_mul, h5c]; exact hsq

end Five

end QuadFormsKB.ConwaySloane
