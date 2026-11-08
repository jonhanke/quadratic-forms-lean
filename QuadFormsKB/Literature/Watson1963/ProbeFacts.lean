/-
# Watson (1963), §§6, 8: ranks of the perfect forms and $\Phi_9 \supseteq E_8$ locally

Facts about the perfect forms of Watson's §6 (`Probes.lean`) used in the bootstrap of Lemma 12 and in Theorem 3.

**Proved here.**
* `rank_five`, `rank_six`, `rank_formE7`, `rank_formE8`: for every prime $p$, one of $A_5$, $\Phi_5$ has rank $5$
  modulo $p$, one of $A_6$, $\Phi_6$ has rank $6$, and $E_7$, $E_8$ have full rank. (Watson, proof of Lemma 12, p. 562:
  "these forms have coprime discriminants".) The Hessian determinants are $6, 4, 7, 4, 2, 1$; the only prime needing
  an argument is $p = 2$ for $A_5$ and $E_7$, whose Hessians are $J - I$ modulo $2$ and whose values at
  $(1, \dots, 1)$ are odd.
* `phiD8_repOver_formE8`: $\Phi_9$ represents $E_8$ over every $\mathbb Z_p$ (Watson (6.6): $\Phi_9$ lies in the genus
  of $E + 2x^2$). Two explicit integral $9 \times 8$ matrices $M_2$, $M_3$ satisfy
  $\Phi_9(M_d\vec y) = d^2 E_8(\vec y)$ identically ($d = 2, 3$); use $d^{-1}M_d$ with $d$ a unit of $\mathbb Z_p$.
  ($M_2$: columns $-2e_i$ ($i < 7$) and $-(e_0 + \dots + e_6) + e_8$. $M_3$ was found as $3$ times an $E_8$-basis of the
  orthogonal complement of a norm-$4$ vector in a $3$-neighbour of $\Phi_9$.)
-/
import QuadFormsKB.Literature.Watson1963.Rank
import QuadFormsKB.Literature.Watson1963.Probes

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-! ### Ranks -/

/-- Helper: a form whose radical modulo $p$ is zero has full rank modulo $p$. -/
theorem rankModP_eq_of_radModP_eq_bot {n : ℕ} (p : ℕ) [Fact p.Prime] {f : QuadForm ℤ n}
    (h : radModP p f = ⊥) : rankModP p f = n := by
  unfold rankModP; rw [h, finrank_bot]; simp

/-- Helper: full rank modulo $p$ for $p \nmid \det H$, stated with a natural-number determinant. -/
theorem rankModP_eq_of_det {n : ℕ} (p : ℕ) [Fact p.Prime] {f : QuadForm ℤ n} {d : ℕ} (hd : f.hessian.det = d)
    (h : ¬ p ∣ d) : rankModP p f = n := by
  refine rankModP_eq_of_not_dvd_det p ?_
  rw [hd]; exact_mod_cast h

/-- Helper: a vector is in the radical modulo $p$ iff the form vanishes at it and it is orthogonal to the basis
vectors. -/
theorem mem_radModP_of_basis {n : ℕ} (p : ℕ) [Fact p.Prime] {f : QuadForm ℤ n} {x : Fin n → ZMod p}
    (hx : x ∈ radModP p f) : f.evalIn (ZMod p) x = 0 ∧
      ∀ j, x ⬝ᵥ (f.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ Pi.single j 1) = 0 :=
  ⟨hx.1, fun j => hx.2 _⟩

/-- The finite check behind `radModP_two_phiA5`. -/
theorem phiA5_check : ∀ x : Fin 5 → ZMod 2, (phiA 5).evalIn (ZMod 2) x = 0 →
    (∀ j, x ⬝ᵥ ((phiA 5).hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ Pi.single j 1) = 0) → x = 0 := by
  decide +kernel

/-- The finite check behind `radModP_two_formE7`. -/
theorem formE7_check : ∀ x : Fin 7 → ZMod 2, formE7.evalIn (ZMod 2) x = 0 →
    (∀ j, x ⬝ᵥ (formE7.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ Pi.single j 1) = 0) → x = 0 := by
  decide +kernel

/-- The radical of $A_5$ modulo $2$ is zero. -/
theorem radModP_two_phiA5 : radModP 2 (phiA 5) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨h1, h2⟩ := mem_radModP_of_basis 2 hx
  exact phiA5_check x h1 h2

/-- The radical of $E_7$ modulo $2$ is zero. -/
theorem radModP_two_formE7 : radModP 2 formE7 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨h1, h2⟩ := mem_radModP_of_basis 2 hx
  exact formE7_check x h1 h2

/-- **$A_5$ or $\Phi_5$ has rank $5$ modulo $p$** ($\det H = 6$, resp. $4$; at $p = 2$ the radical of $A_5$ is zero).
-/
theorem rank_five (p : ℕ) [hp : Fact p.Prime] : 5 ≤ rankModP p (phiA 5) ∨ 5 ≤ rankModP p (phiD 4) := by
  by_cases h2 : p = 2
  · subst h2; left; rw [rankModP_eq_of_radModP_eq_bot 2 radModP_two_phiA5]
  by_cases h3 : p = 3
  · subst h3; right
    rw [rankModP_eq_of_det 3 (d := 4) (by rw [phiD_hessian_det]; rfl) (by norm_num)]
  · left
    rw [rankModP_eq_of_det p (d := 6) (by rw [phiA_hessian_det]; norm_num) ?_]
    intro hd
    have h6 : p ∣ 2 * 3 := hd
    rcases (Nat.Prime.dvd_mul hp.out).mp h6 with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h)

/-- **$A_6$ or $\Phi_6$ has rank $6$ modulo $p$** ($\det H = 7$, resp. $4$). -/
theorem rank_six (p : ℕ) [hp : Fact p.Prime] : 6 ≤ rankModP p (phiA 6) ∨ 6 ≤ rankModP p (phiD 5) := by
  by_cases h7 : p = 7
  · subst h7; right
    rw [rankModP_eq_of_det 7 (d := 4) (by rw [phiD_hessian_det]; rfl) (by norm_num)]
  · left
    rw [rankModP_eq_of_det p (d := 7) (by rw [phiA_hessian_det]; norm_num) ?_]
    intro hd
    exact h7 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hd)

/-- **$E_7$ has rank $7$ modulo every prime** ($\det H = 2$; at $p = 2$ the radical is zero). -/
theorem rank_formE7 (p : ℕ) [hp : Fact p.Prime] : 7 ≤ rankModP p formE7 := by
  by_cases h2 : p = 2
  · subst h2; rw [rankModP_eq_of_radModP_eq_bot 2 radModP_two_formE7]
  · rw [rankModP_eq_of_det p (d := 2) (by rw [formE7_hessian_det]; rfl) ?_]
    intro hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)

/-- **$E_8$ has rank $8$ modulo every prime** ($\det H = 1$). -/
theorem rank_formE8 (p : ℕ) [hp : Fact p.Prime] : 8 ≤ rankModP p formE8 := by
  rw [rankModP_eq_of_det p (d := 1) (by rw [formE8_hessian_det]; rfl) hp.out.not_dvd_one]

/-! ### $\Phi_9$ represents $E_8$ locally -/

/-- The matrix $M_2$: $\Phi_9(M_2\vec y) = 4E_8(\vec y)$. -/
def matM2 : Matrix (Fin 9) (Fin 8) ℤ :=
  !![-2, 0, 0, 0, 0, 0, 0, -1; 0, -2, 0, 0, 0, 0, 0, -1; 0, 0, -2, 0, 0, 0, 0, -1; 0, 0, 0, -2, 0, 0, 0, -1;
     0, 0, 0, 0, -2, 0, 0, -1; 0, 0, 0, 0, 0, -2, 0, -1; 0, 0, 0, 0, 0, 0, -2, -1; 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

/-- The matrix $M_3$: $\Phi_9(M_3\vec y) = 9E_8(\vec y)$. -/
def matM3 : Matrix (Fin 9) (Fin 8) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 3, 1; 0, 0, 0, 0, 0, 3, 0, 1; 0, 0, 0, 0, 3, 0, 0, 1;
     0, 0, 0, 3, 0, 0, 0, 1; 0, 0, 3, 0, 0, 0, 0, 1; 0, 3, 0, 0, 0, 0, 0, 1; 3, 0, 0, 0, 0, 0, 0, 1;
     -3, -3, -3, -3, -3, -3, -3, -8]

/-- Helper: the value of $c\,Q$ over $S$. -/
theorem evalIn_smul_form {n : ℕ} {S : Type*} [CommRing S] (c : ℤ) (Q : QuadForm ℤ n) (y : Fin n → S) :
    (c • Q).evalIn S y = (c : S) * Q.evalIn S y := by
  simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
    algebraMap_int_eq, eq_intCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **$\Phi_9 \circ M_2 = 4E_8$** (coefficientwise; a finite computation). -/
theorem phiD8_compMat_matM2 : (phiD 8).compMat matM2 = (4 : ℤ) • formE8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- **$\Phi_9 \circ M_3 = 9E_8$** (coefficientwise; a finite computation). -/
theorem phiD8_compMat_matM3 : (phiD 8).compMat matM3 = (9 : ℤ) • formE8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Helper: if $\Phi_9 \circ M = d^2 E_8$ over $\mathbb Z$ and $d$ is a unit of $S$, then $\Phi_9$ represents
$E_8$ over $S$. -/
theorem repOver_of_scaled {S : Type*} [CommRing S] (M : Matrix (Fin 9) (Fin 8) ℤ) (d : ℤ) (hd : IsUnit (d : S))
    (h : (phiD 8).compMat M = (d ^ 2) • formE8) : RepOver S (phiD 8) formE8 := by
  have hr : Rep (phiD 8) ((d ^ 2) • formE8) := ⟨M, fun y => by rw [← QuadForm.eval_compMat, h]⟩
  obtain ⟨H, hH⟩ := hr.repOver S
  obtain ⟨u, hu⟩ := hd
  refine ⟨(↑u⁻¹ : S) • H, fun y => ?_⟩
  rw [smul_mulVec, evalIn_smul', hH, evalIn_smul_form, ← mul_assoc, Int.cast_pow, ← hu, ← mul_pow,
    Units.inv_mul, one_pow, one_mul]

/-- **$\Phi_9$ represents $E_8$ over every $\mathbb Z_p$** (Watson 1963, (6.6), p. 559: $\Phi_9$ is in the genus of
$E + 2x^2$). Use $\tfrac12 M_2$ for odd $p$ and $\tfrac13 M_3$ for $p = 2$. -/
@[kb "watson1963" "§6, Lemma 8, (6.6), p. 559 (Φ₉ in the genus of E + 2x²)"]
theorem phiD8_repOver_formE8 (p : ℕ) [hp : Fact p.Prime] : RepOver ℤ_[p] (phiD 8) formE8 := by
  by_cases h2 : p = 2
  · subst h2
    refine repOver_of_scaled matM3 3 ?_ (by rw [phiD8_compMat_matM3]; norm_num)
    exact_mod_cast isUnit_natCast_padic_of_prime_ne Nat.prime_three (by norm_num)
  · refine repOver_of_scaled matM2 2 ?_ (by rw [phiD8_compMat_matM2]; norm_num)
    exact_mod_cast isUnit_natCast_padic_of_prime_ne Nat.prime_two h2

end QuadFormsKB.Watson1963
