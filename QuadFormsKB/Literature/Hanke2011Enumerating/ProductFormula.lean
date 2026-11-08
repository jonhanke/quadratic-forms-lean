/-
# Hanke 2011, Lemma 5.2: the product formula for the Gan–Hanke–Yu invariants $w_p$ (corrected)

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (bib key `hanke2011enumerating`), Lemma 5.2, p. 9.

**Setting.** A positive definite rational quadratic space is a diagonal form $\langle a_0,\dots,a_{n-1}\rangle$ with
$a_i\in\mathbb Q_{>0}$. $(x,y)_p$ is the Hilbert symbol of $\mathbb Q_p$ (`hp p x y`, the library's `RatPlace.hilbert`),
$(x,y)_\infty$ the real one (`hinf`). The Gan–Hanke–Yu invariants at $p$ are those of Lemma 5.1 (`ghyOfStd`, applied to the
standard invariants $d = \prod_ia_i$, $c_p = \prod_{i<j}(a_i,a_j)_p$): $\delta = (-1)^{\lfloor n/2\rfloor}\prod_ia_i$ (`deltaQ`) and
$w_p = c_p\,\mu_p(n,\delta)$ (`wP`; `wP_eq_ghyOfStd` is the comparison with Lemma 5.1).

**Proves** the product formula (4) **corrected** (`lemma_5_2`): for $n\ge1$,
$$\prod_pw_p = (-1)^{\lfloor n/4\rfloor}\prod_p(-1,\delta)_p^{\lfloor(n-1)/2\rfloor},$$
and that the printed exponent $\lfloor(n+1)/2\rfloor$ is wrong (`lemma_5_2_printed_false`: $x^2+y^2+z^2$). The proof is the
paper's: $\prod_pc_p = c_\infty = 1$ by Hilbert reciprocity (`finprod_hp`), and the remaining factors are evaluated at
$\infty$. The local–global part of Lemma 5.2 (which collections of local spaces come from a global one) is not
formalized here.
-/
import QuadFormsKB.Literature.Hanke2011Enumerating.LocalInvariants
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Citation

open QuadFormsKB RatPlace

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

/-- The Hilbert symbol $(x,y)_p$ of $\mathbb Q_p$, for $x, y\in\mathbb Q$. -/
abbrev hp (p : Nat.Primes) (x y : ℚ) : ℤ := (RatPlace.finite p).hilbert x y

/-- The real Hilbert symbol $(x,y)_\infty$, for $x, y\in\mathbb Q$. -/
abbrev hinf (x y : ℚ) : ℤ := RatPlace.infinite.hilbert x y

theorem hp_pm (p : Nat.Primes) (x y : ℚ) : hp p x y = 1 ∨ hp p x y = -1 := by
  simp only [hp, RatPlace.hilbert, hilbertSymbol]; split_ifs <;> simp

theorem hinf_pm (x y : ℚ) : hinf x y = 1 ∨ hinf x y = -1 := by
  simp only [hinf, RatPlace.hilbert, hilbertSymbol]; split_ifs <;> simp

theorem hinf_eq {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) : hinf x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have key := hilbertSymbol_real (x : ℝ) y hx' hy'
  by_cases h : x < 0 ∧ y < 0
  · rw [if_pos h]
    exact key.2 ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [if_neg h]
    rcases hinf_pm x y with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨h1', h2'⟩ := key.1 h1
      exact h ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩

/-- **Hilbert reciprocity as a product over the primes**: $\prod_p(x,y)_p = (x,y)_\infty$ (finitely many factors
$\ne1$), from the library's product formula `hilbert_product_formula`. -/
theorem finprod_hp {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.HasFiniteMulSupport (fun p => hp p x y) ∧ ∏ᶠ p, hp p x y = hinf x y := by
  classical
  obtain ⟨hS, hE⟩ := hilbert_product_formula x y hx hy
  set S := {v : RatPlace | v.hilbert x y = -1} with hSdef
  set Sf := {p : Nat.Primes | hp p x y = -1} with hSfdef
  have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
  have hSf : Sf.Finite := hS.preimage hinj.injOn
  have hsupp : Function.mulSupport (fun p => hp p x y) = Sf := by
    ext p
    simp only [Function.mem_mulSupport, Set.mem_setOf_eq, Sf]
    rcases hp_pm p x y with h | h <;> simp [h]
  refine ⟨by rw [Function.HasFiniteMulSupport, hsupp]; exact hSf, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hSf.toFinset) (by rw [hsupp, Set.Finite.coe_toFinset])]
  have hprod : ∏ p ∈ hSf.toFinset, hp p x y = (-1) ^ Sf.ncard := by
    rw [Finset.prod_congr rfl (fun p hp' => (Set.Finite.mem_toFinset hSf).1 hp'), Finset.prod_const,
      Set.ncard_eq_toFinset_card _ hSf]
  rw [hprod]
  have hdecomp : S = RatPlace.finite '' Sf ∪ ({RatPlace.infinite} ∩ S) := by
    ext v
    cases v with
    | infinite => simp [S]
    | finite p => simp [S, Sf, hinj.eq_iff]
  have hdisj : Disjoint (RatPlace.finite '' Sf) ({RatPlace.infinite} ∩ S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, _, rfl⟩ ⟨h, _⟩
    cases h
  have hcard : S.ncard = Sf.ncard + ({RatPlace.infinite} ∩ S).ncard := by
    conv_lhs => rw [hdecomp]
    rw [Set.ncard_union_eq hdisj (hSf.image _) (Set.toFinite _), Set.ncard_image_of_injective _ hinj]
  rcases hinf_pm x y with h | h
  · have h0 : ({RatPlace.infinite} ∩ S) = ∅ := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, S, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl hv
      rw [hinf] at h
      rw [h] at hv
      norm_num at hv
    rw [h0, Set.ncard_empty, add_zero] at hcard
    rw [hcard] at hE
    rw [h]; exact hE.neg_one_pow
  · have h1 : ({RatPlace.infinite} ∩ S) = {RatPlace.infinite} := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, S, and_iff_left_iff_imp]
      rintro rfl
      exact h
    rw [h1, Set.ncard_singleton] at hcard
    rw [hcard] at hE
    have hodd : Odd Sf.ncard := Nat.odd_iff.2 (by
      rcases Nat.even_or_odd Sf.ncard with he | ho
      · exfalso; exact (Nat.not_even_iff_odd.2 (he.add_one)) hE
      · exact Nat.odd_iff.1 ho)
    rw [h]; exact hodd.neg_one_pow

/-! ### The Gan–Hanke–Yu invariants of a rational diagonal form -/

/-- $\delta = (-1)^{\lfloor n/2\rfloor}\prod_ia_i$ (Gan–Hanke–Yu's signed discriminant). -/
@[kb "hanke2011enumerating" "§5, p. 8–9 (δ = (-1)^{⌊n/2⌋} d)"]
def deltaQ {n : ℕ} (a : Fin n → ℚ) : ℚ := (-1) ^ (n / 2) * ∏ i, a i

/-- $c_p = \prod_{i<j}(a_i,a_j)_p$ (Serre's Hasse invariant over $\mathbb Q_p$). -/
def cP (p : Nat.Primes) {n : ℕ} (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then hp p (a i) (a j) else 1

/-- The factor $\mu_p(n,\delta)$ of Lemma 5.1 over $\mathbb Q_p$ (`ghyMu`). -/
def muP (p : Nat.Primes) (n : ℕ) (δ : ℚ) : ℤ :=
  if n % 2 = 0 then hp p (-1) (-1) ^ ((n / 2 - 1) / 2) * hp p ((-1) ^ (n / 2 - 1)) (-δ)
  else hp p (-1) (-1) ^ (n / 2 / 2) * hp p ((-1) ^ (n / 2)) δ

/-- **Gan–Hanke–Yu's local invariant $w_p$** of $\langle a_0,\dots,a_{n-1}\rangle$ (Hanke 2011, §5, via Lemma 5.1):
$w_p = c_p\,\mu_p(n,\delta)$. -/
@[kb "hanke2011enumerating" "§5, Lemma 5.1, pp. 8–9 (the Gan–Hanke–Yu invariant w_p)"]
def wP (p : Nat.Primes) {n : ℕ} (a : Fin n → ℚ) : ℤ := cP p a * muP p n (deltaQ a)

/-- `wP` is the $w$ of Lemma 5.1 (`ghyOfStd`) for the standard invariants of $\langle a\rangle$ over $\mathbb Q_p$. -/
theorem wP_eq_ghyOfStd (p : Nat.Primes) {n : ℕ} (a : Fin n → ℚ) :
    haveI : Fact p.1.Prime := ⟨p.2⟩
    wP p a = (ghyOfStd n (∏ i, (a i : ℚ_[p.1])) (PadicClass.hasseVec (fun i => (a i : ℚ_[p.1])))).2 := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  simp only [wP, ghyOfStd, cP, muP, ghyMu, deltaQ, hp, RatPlace.hilbert, PadicClass.hasseVec]
  push_cast
  rfl

/-! ### Lemma 5.2 -/

theorem hasFiniteMulSupport_hp {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.HasFiniteMulSupport (fun p => hp p x y) := (finprod_hp hx hy).1

theorem finprod_cP {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 < a i) :
    Function.HasFiniteMulSupport (fun p => cP p a) ∧ ∏ᶠ p, cP p a = 1 := by
  have hne : ∀ i, a i ≠ 0 := fun i => (ha i).ne'
  have hg : ∀ i j, Function.HasFiniteMulSupport (fun p => if i < j then hp p (a i) (a j) else 1) := by
    intro i j
    by_cases h : i < j
    · simpa [h] using hasFiniteMulSupport_hp (hne i) (hne j)
    · simp only [h, if_false, Function.HasFiniteMulSupport, Function.mulSupport_fun_one, Set.finite_empty]
  have hg' : ∀ i, Function.HasFiniteMulSupport (fun p => ∏ j, if i < j then hp p (a i) (a j) else 1) :=
    fun i => (Function.HasFiniteMulSupport.prod fun j => hg i j) Finset.univ
  refine ⟨(Function.HasFiniteMulSupport.prod fun i => hg' i) Finset.univ, ?_⟩
  unfold cP
  rw [finprod_prod_comm _ _ fun i _ => hg' i]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [finprod_prod_comm _ _ fun j _ => hg i j]
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases h : i < j
  · simp only [h, if_true]
    rw [(finprod_hp (hne i) (hne j)).2, hinf_eq (hne i) (hne j), if_neg]
    rintro ⟨h1, -⟩; exact absurd h1 (not_lt.2 (ha i).le)
  · simp [h]

theorem finprod_pow_hp {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (k : ℕ) {u v : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) :
    Function.HasFiniteMulSupport (fun p => hp p x y ^ k * hp p u v) ∧
      ∏ᶠ p, hp p x y ^ k * hp p u v = hinf x y ^ k * hinf u v := by
  have h1 := hasFiniteMulSupport_hp hx hy
  have h2 := hasFiniteMulSupport_hp hu hv
  have h1k : Function.HasFiniteMulSupport (fun p => hp p x y ^ k) := h1.pow k
  refine ⟨h1k.mul h2, ?_⟩
  rw [finprod_mul_distrib h1k h2, ← finprod_pow h1, (finprod_hp hx hy).2, (finprod_hp hu hv).2]

theorem neg_one_pow_lt_zero_iff (m : ℕ) : (-1 : ℚ) ^ m < 0 ↔ Odd m := by
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow]; simp [Nat.not_odd_iff_even.2 h]
  · rw [h.neg_one_pow]; simp [h]

/-- The parity identity of the even case of Lemma 5.2 ($n = 2r$). -/
theorem lemma_5_2_even_arith (r : ℕ) (hr : 1 ≤ r) :
    (-1 : ℤ) ^ ((r - 1) / 2) * (if Odd (r - 1) ∧ ¬ Odd r then -1 else 1) =
      (-1) ^ (2 * r / 4) * (if Odd r then -1 else 1) ^ ((2 * r - 1) / 2) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' r
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : (2 * (i + 1) - 1) / 2 = i := by omega
    have e2 : 2 * (2 * (i + 1)) / 4 = i + 1 := by omega
    have o1 : Odd (2 * (i + 1) - 1) := ⟨i, by omega⟩
    have o2 : ¬ Odd (2 * (i + 1)) := Nat.not_odd_iff_even.2 ⟨i + 1, by ring⟩
    rw [e1, e2, if_pos ⟨o1, o2⟩, if_neg o2, one_pow, pow_succ]; ring
  · have e1 : (2 * j + 1 - 1) / 2 = j := by omega
    have e2 : 2 * (2 * j + 1) / 4 = j := by omega
    have e3 : (2 * (2 * j + 1) - 1) / 2 = 2 * j := by omega
    have o1 : ¬ Odd (2 * j + 1 - 1) := Nat.not_odd_iff_even.2 ⟨j, by omega⟩
    have o2 : Odd (2 * j + 1) := ⟨j, rfl⟩
    rw [e1, e2, e3, if_neg (fun h => o1 h.1), if_pos o2, pow_mul]; norm_num

/-- The parity identity of the odd case of Lemma 5.2 ($n = 2r + 1$). -/
theorem lemma_5_2_odd_arith (r : ℕ) :
    (-1 : ℤ) ^ (r / 2) * (if Odd r ∧ Odd r then -1 else 1) =
      (-1) ^ ((2 * r + 1) / 4) * (if Odd r then -1 else 1) ^ ((2 * r + 1 - 1) / 2) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' r
  · have o : ¬ Odd (2 * j) := Nat.not_odd_iff_even.2 ⟨j, by ring⟩
    have e1 : 2 * j / 2 = j := by omega
    have e2 : (2 * (2 * j) + 1) / 4 = j := by omega
    rw [e1, e2, if_neg (fun h => o h.1), if_neg o]; simp
  · have o : Odd (2 * j + 1) := ⟨j, rfl⟩
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : (2 * (2 * j + 1) + 1) / 4 = j := by omega
    have e3 : (2 * (2 * j + 1) + 1 - 1) / 2 = 2 * j + 1 := by omega
    rw [e1, e2, e3, if_pos ⟨o, o⟩, if_pos o, pow_succ, pow_mul]; norm_num

/-- **Lemma 5.2, the product formula (4), corrected** (Hanke 2011, p. 9): for a positive definite rational space
$\langle a_0,\dots,a_{n-1}\rangle$ ($n\ge1$, $a_i > 0$),
$\prod_pw_p = (-1)^{\lfloor n/4\rfloor}\prod_p(-1,\delta)_p^{\lfloor(n-1)/2\rfloor}$ (both products have finitely many factors
$\ne1$). *Erratum:* the paper prints the exponent $\lfloor(n+1)/2\rfloor$ (`lemma_5_2_printed_false`). The proof is the
paper's: $\prod_pc_p = c_\infty = 1$ (positive definite), and the other factors are products of Hilbert symbols, whose
product over $p$ is the real symbol (Hilbert reciprocity), evaluated by the signs of $-1$ and
$\delta = (-1)^{\lfloor n/2\rfloor}\prod_ia_i$. -/
@[kb "hanke2011enumerating" "Lemma 5.2, (4), p. 9 (corrected exponent ⌊(n-1)/2⌋)"]
theorem lemma_5_2 {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℚ) (ha : ∀ i, 0 < a i) :
    Function.HasFiniteMulSupport (fun p => wP p a) ∧
      ∏ᶠ p, wP p a = (-1) ^ (n / 4) * (∏ᶠ p, hp p (-1) (deltaQ a)) ^ ((n - 1) / 2) := by
  have hP : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hδ0 : deltaQ a ≠ 0 := by
    unfold deltaQ; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hP.ne'
  have m1 : (-1 : ℚ) ≠ 0 := by norm_num
  have hδsign : deltaQ a < 0 ↔ Odd (n / 2) := by
    unfold deltaQ
    rw [← neg_one_pow_lt_zero_iff]
    constructor
    · intro h; by_contra h'; push Not at h'; exact absurd h (not_lt.2 (mul_nonneg h' hP.le))
    · intro h; exact mul_neg_of_neg_of_pos h hP
  obtain ⟨hc, hcp⟩ := finprod_cP ha
  have hRHS : ∏ᶠ p, hp p (-1) (deltaQ a) = if Odd (n / 2) then -1 else 1 := by
    rw [(finprod_hp m1 hδ0).2, hinf_eq m1 hδ0]
    simp only [show (-1 : ℚ) < 0 by norm_num, true_and, hδsign]
  rw [hRHS]
  by_cases h2 : n % 2 = 0
  · obtain ⟨hm, hmp⟩ := finprod_pow_hp m1 m1 ((n / 2 - 1) / 2) (pow_ne_zero (n / 2 - 1) m1) (neg_ne_zero.2 hδ0)
    have hmu : (fun p => muP p n (deltaQ a)) =
        fun p => hp p (-1) (-1) ^ ((n / 2 - 1) / 2) * hp p ((-1) ^ (n / 2 - 1)) (-deltaQ a) := by
      ext p; simp only [muP, h2, if_true]
    have hmS : Function.HasFiniteMulSupport (fun p => muP p n (deltaQ a)) := by rw [hmu]; exact hm
    refine ⟨hc.mul hmS, ?_⟩
    show ∏ᶠ p, cP p a * muP p n (deltaQ a) = _
    rw [finprod_mul_distrib hc hmS, hcp, one_mul, hmu, hmp, hinf_eq m1 m1,
      if_pos ⟨by norm_num, by norm_num⟩, hinf_eq (pow_ne_zero _ m1) (neg_ne_zero.2 hδ0)]
    have hr : 1 ≤ n / 2 := by omega
    have hn2 : n = 2 * (n / 2) := by omega
    have hcond : ((-1 : ℚ) ^ (n / 2 - 1) < 0 ∧ -deltaQ a < 0) ↔ (Odd (n / 2 - 1) ∧ ¬ Odd (n / 2)) := by
      have hpos' : 0 < deltaQ a ↔ ¬ Odd (n / 2) := by
        rw [← hδsign]
        constructor
        · intro h h'; linarith
        · intro h; rcases lt_or_gt_of_ne hδ0 with h' | h'
          · exact absurd h' h
          · exact h'
      rw [neg_one_pow_lt_zero_iff, neg_lt_zero, hpos']
    simp only [hcond]
    have := lemma_5_2_even_arith (n / 2) hr
    rw [← hn2] at this
    exact this
  · obtain ⟨hm, hmp⟩ := finprod_pow_hp m1 m1 (n / 2 / 2) (pow_ne_zero (n / 2) m1) hδ0
    have hmu : (fun p => muP p n (deltaQ a)) =
        fun p => hp p (-1) (-1) ^ (n / 2 / 2) * hp p ((-1) ^ (n / 2)) (deltaQ a) := by
      ext p; simp only [muP, h2, if_false]
    have hmS : Function.HasFiniteMulSupport (fun p => muP p n (deltaQ a)) := by rw [hmu]; exact hm
    refine ⟨hc.mul hmS, ?_⟩
    show ∏ᶠ p, cP p a * muP p n (deltaQ a) = _
    rw [finprod_mul_distrib hc hmS, hcp, one_mul, hmu, hmp, hinf_eq m1 m1,
      if_pos ⟨by norm_num, by norm_num⟩, hinf_eq (pow_ne_zero _ m1) hδ0]
    have hn2 : n = 2 * (n / 2) + 1 := by omega
    simp only [neg_one_pow_lt_zero_iff, hδsign]
    have := lemma_5_2_odd_arith (n / 2)
    rw [← hn2] at this
    exact this

/-- **The printed form of (4) is false** (Hanke 2011, Lemma 5.2, p. 9): for $x^2+y^2+z^2$ ($n = 3$, $\delta = -1$),
$\prod_pw_p = -1$ (`lemma_5_2`) while the printed right side
$(-1)^{\lfloor n/4\rfloor}\prod_p(-1,\delta)_p^{\lfloor(n+1)/2\rfloor} = (-1)^0\cdot((-1,-1)_\infty)^2 = 1$. -/
@[kb "hanke2011enumerating" "Lemma 5.2, (4), p. 9 (the printed exponent ⌊(n+1)/2⌋ fails)"]
theorem lemma_5_2_printed_false :
    ∏ᶠ p, wP p (![1, 1, 1] : Fin 3 → ℚ) ≠
      (-1) ^ (3 / 4) * (∏ᶠ p, hp p (-1) (deltaQ (![1, 1, 1] : Fin 3 → ℚ))) ^ ((3 + 1) / 2) := by
  have ha : ∀ i, 0 < (![1, 1, 1] : Fin 3 → ℚ) i := by intro i; fin_cases i <;> norm_num
  rw [(lemma_5_2 (by norm_num) _ ha).2]
  have hδ : deltaQ (![1, 1, 1] : Fin 3 → ℚ) = -1 := by simp [deltaQ, Fin.prod_univ_three]
  have m1 : (-1 : ℚ) ≠ 0 := by norm_num
  rw [hδ, (finprod_hp m1 m1).2, hinf_eq m1 m1, if_pos ⟨by norm_num, by norm_num⟩]
  norm_num

end QuadFormsKB.Hanke2011Enumerating
