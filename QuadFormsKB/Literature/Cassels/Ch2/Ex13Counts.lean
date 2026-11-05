/-
# Cassels, Chapter 2, Example 13 (iii)-(vi): counting zeros, representations of $1$ and proper automorphs over $\mathbb F_p$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Examples*, Ex. 13 (iii)-(vi), pp. 31-32.
Parts (i), (ii) are in `Ch2/ExercisesMore.lean` (`ex13_i`, `ex13_ii`, `ex13_ii_zmod`).

**Setting and conventions** (as in `Ch2/Exercises.lean`, `Ch2/ExercisesMore.lean`). $k = \mathbb F_p$ = `ZMod p`, $p$ an odd
prime (`[Fact p.Prime] [Invertible (2 : ZMod p)]`; the last instance says that $p$ is odd). A form $f$ in $n$ variables is
a Mathlib quadratic form `Q : QuadraticForm (ZMod p) (Fin n → ZMod p)` (indices $0$-based, variables $x_0, \dots, x_{n-1}$),
*regular* means that its bilinear form `associated Q` $= B$, $B(x, x) = Q(x)$, is nondegenerate, and the
**determinant** $d$ of $Q$ is `Q.discr'`, the determinant of the Gram matrix $(B(e_i, e_j))$ in the standard basis (so
$Q(x) = x^{T} F x$ with $d = \det F$, as in Cassels). It is defined up to the square of a unit under a change of
variables; only its class in $k^{\times}/(k^{\times})^{2}$ enters. The three quantities of the exercise are
* $N$ = `Nat.card {x // Q x = 0}`, the number of zeros including $x = 0$;
* $R$ = `Nat.card {x // Q x = 1}`, the number of representations of $1$;
* $A$ = `Nat.card (OMeara.orthPlus Q)`, the order of the group of proper automorphs
  (as in `ex13_i`; $O^{+}$ is the group of autometries of determinant $1$).

$\chi$ is Mathlib's quadratic character `quadraticChar (ZMod p)`: it is $1$ on nonzero squares and $-1$ on non-squares,
as in the book (`quadraticChar_eq_cassels_chi`); here its argument is always a nonzero determinant class
(a regular form has $d \ne 0$).

**Proves** (all unconditionally, no hypothesis beyond regularity; the formulas are for *every* regular form, not only
diagonal ones):
* (iii) `ex13_iii`: $N_{n}(d) = p^{n-2}(p - 1) + p\,N_{n-2}(-d)$ for $n \ge 3$.
* (iv) `ex13_iv_odd`, `ex13_iv_even`: $N_{2m+1}(d) = p^{2m}$ and
  $N_{2m}(d) = p^{2m-1} + \chi((-1)^{m} d)(p - 1)p^{m-1}$ ($m > 0$).
* (v) `ex13_v_even`, `ex13_v_odd`: $R_{2m}(d) = p^{2m-1} - \chi((-1)^{m} d)\,p^{m-1}$ ($m > 0$) and
  $R_{2m+1}(d) = p^{2m} + \chi((-1)^{m} d)\,p^{m}$ ($m \ge 0$).
* (vi) `ex13_vi_odd`, `ex13_vi_even`: $A_{2m+1}(d) = p^{m^{2}}(p^{2} - 1)(p^{4} - 1) \cdots (p^{2m} - 1)$ and
  $A_{2m}(d) = p^{m(m-1)}(p^{2} - 1)(p^{4} - 1) \cdots (p^{2m-2} - 1)(p^{m} - \varepsilon)$,
  $\varepsilon = \chi((-1)^{m} d)$ ($m > 0$).

**Source check.** The displayed formulas of (iii)-(vi) are garbled in the machine-read text (the exponent in (iii) shows
as "p^?"); they were first reconstructed from the case analysis and the hints, then checked against the page images
(pp. 31-32; they agree with the printed formulas), and were checked numerically by brute-force
enumeration (all diagonal forms over $\mathbb F_p$, $p \in \{3, 5, 7\}$, $n \le 5$ for $N$, $R$ and for the recursion (iii);
$p = 3$, $n \le 4$ and $p = 5$, $n \le 3$ for $A$) before being formalized. In (iii) the book writes $n \ge 3$ and
$N_{n-2}(-d)$; here the form is on `Fin (k + 2)` with $k = n - 2 \ge 1$, and $N_{n-2}(-d)$ is the number of zeros of any
regular form $Q'$ on `Fin k` whose determinant lies in the class of $-d$ (hypothesis `∃ c ≠ 0, Q'.discr' = -Q.discr' * c ^ 2`).
No erratum was found; the printed hint of (vi), $A_n(d) = R_n(d) A_{n-1}(d)$, holds as printed (the orthogonal
complement of a vector of value $1$ has the same determinant class; `discr_perp`), so $A_n$ depends only on $n$ and $d$.

**Method.** $N$ and $R$: by Witt-type diagonalization (Mathlib) the form is isometric to a diagonal form
$\sum_i w_i x_i^{2}$ with $w_i \ne 0$; for diagonal forms the number of solutions of $\sum_i w_i x_i^{2} = c$ is computed by
induction on the number of variables with the character sums $\sum_u \chi(u) = 0$ and
$\sum_u \chi(u)\chi(c - u)$ (`diagCount_formula`); this replaces the hint of (iii) (hyperbolic plane) and gives (iii)
as a consequence of (iv). $A$: orbit-stabilizer for $O(Q)$ acting on $\{Q = 1\}$, transitive by Witt's extension theorem
(`Witt/Extension.lean`), with stabilizer of $x_0$ equal to $O(Q|_{x_0^{\perp}})$ (`card_orth_eq`), together with
$|O| = 2|O^{+}|$ (`card_orth_eq_two_mul`), starting from $|O^{+}| = 1$ in dimension $1$, and an induction on the
dimension (`card_orthPlus_formula`).
-/
import QuadFormsKB.Literature.Cassels.Ch2.ExercisesMore
import QuadFormsKB.Witt.Extension

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch2Ex

namespace Ex13Counts

section CharSums

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Helper: the quadratic character takes the same value at $a^{-1}$ and at $a$ ($a \in F$). -/
lemma chi_inv (a : F) : quadraticChar F a⁻¹ = quadraticChar F a := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : a⁻¹ = a * (a⁻¹) ^ 2 := by field_simp
    conv_lhs => rw [h1]
    rw [map_mul, quadraticChar_sq_one' (inv_ne_zero ha), mul_one]

/-- Helper: $\chi(a^{2} b) = \chi(b)$ for $a \ne 0$ ($\chi$ the quadratic character of $F$). -/
lemma chi_sq_mul (a b : F) (ha : a ≠ 0) : quadraticChar F (a ^ 2 * b) = quadraticChar F b := by
  rw [map_mul, quadraticChar_sq_one' ha, one_mul]

/-- Helper: $\chi(a)\chi(a) = 1$ for $a \ne 0$. -/
lemma chi_mul_self {a : F} (ha : a ≠ 0) : quadraticChar F a * quadraticChar F a = 1 := by
  rw [← map_mul, ← _root_.sq, quadraticChar_sq_one' ha]

/-- Helper -/
lemma sum_chi_mul_chi_sub (hF : ringChar F ≠ 2) (c : F) :
    ∑ u : F, quadraticChar F u * quadraticChar F (c - u) =
      if c = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-1) else - quadraticChar F (-1) := by
  have h0 := quadraticChar_sum_zero hF (F := F)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  simp only [quadraticChar_zero, zero_mul, zero_add]
  split_ifs with hc
  · subst hc
    have : ∀ u ∈ (Finset.univ : Finset F).erase 0,
        quadraticChar F u * quadraticChar F (0 - u) = quadraticChar F (-1) := by
      intro u hu
      have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
      have : (0 : F) - u = (-1) * u := by ring
      rw [this, map_mul, mul_left_comm, chi_mul_self hu0, mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, nsmul_eq_mul]
    push_cast [Nat.cast_sub Fintype.card_pos]
    ring
  · have key : ∀ u ∈ (Finset.univ : Finset F).erase 0,
        quadraticChar F u * quadraticChar F (c - u) = quadraticChar F (c * u⁻¹ - 1) := by
      intro u hu
      have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
      have : c - u = u * (c * u⁻¹ - 1) := by field_simp
      rw [this, map_mul, ← mul_assoc, chi_mul_self hu0, one_mul]
    rw [Finset.sum_congr rfl key]
    have hfull : ∑ u : F, quadraticChar F (c * u⁻¹ - 1) = 0 := by
      have e1 : ∑ u : F, quadraticChar F (c * u⁻¹ - 1) = ∑ u : F, quadraticChar F (c * u - 1) :=
        Fintype.sum_equiv (Function.Involutive.toPerm (fun x : F => x⁻¹) inv_involutive) _ _
          (fun u => by simp)
      rw [e1]
      calc ∑ u : F, quadraticChar F (c * u - 1) = ∑ v : F, quadraticChar F v :=
            Fintype.sum_equiv ((Equiv.mulLeft₀ c hc).trans (Equiv.subRight 1)) _ _ (fun u => rfl)
        _ = 0 := h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))] at hfull
    simp only [inv_zero, mul_zero, zero_sub] at hfull
    linarith

end CharSums

section DiagCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Helper: the number of solutions $x \in F^{n}$ of $\sum_i w_i x_i^2 = c$. -/
def diagCount {n : ℕ} (w : Fin n → F) (c : F) : ℕ :=
  Fintype.card {x : Fin n → F // ∑ i, w i * x i ^ 2 = c}

/-- Helper: splitting off the first variable, the number of solutions of $a t^{2} + \sum_i w_i x_i^{2} = c$ is $\sum_{t \in F}$ of the number of solutions of $\sum_i w_i x_i^{2} = c - a t^{2}$ (`diagCount` is the number of solutions in $F^{n}$ of the diagonal equation with weights $w_i$ and right hand side $c$). -/
lemma diagCount_cons {n : ℕ} (a : F) (w : Fin n → F) (c : F) :
    diagCount (Fin.cons a w : Fin (n + 1) → F) c = ∑ t : F, diagCount w (c - a * t ^ 2) := by
  unfold diagCount
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.1 0, Fin.tail x.1, ?_⟩
      invFun := fun s => ⟨Fin.cons s.1 s.2.1, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun s => ?_ }
  · have h := x.2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
    simp only [Fin.tail]
    linear_combination h
  · have h := s.2.2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    linear_combination h
  · exact Subtype.ext (Fin.cons_self_tail _)
  · rcases s with ⟨t, y, hy⟩
    simp
    exact HEq.rfl

/-- Helper: for $a \ne 0$ the number of $t \in F$ with $a t^{2} = u$ is $\chi(a)\chi(u) + 1$ (odd characteristic `hF`). -/
lemma card_filter_sq (hF : ringChar F ≠ 2) (a u : F) (ha : a ≠ 0) :
    ((Finset.univ.filter fun t : F => a * t ^ 2 = u).card : ℤ) =
      quadraticChar F a * quadraticChar F u + 1 := by
  have h := quadraticChar_card_sqrts hF (a⁻¹ * u)
  have e : (Finset.univ.filter fun t : F => a * t ^ 2 = u) =
      {x : F | x ^ 2 = a⁻¹ * u}.toFinset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; rw [h]; field_simp
  rw [e, h, map_mul, chi_inv]

/-- Helper: the recursion of `diagCount_cons` in the form $\sum_{u} (1 + \chi(a)\chi(u))\,\mathrm{count}(c - u)$, for a first weight $a \ne 0$ (odd characteristic `hF`). -/
lemma diagCount_cons_int (hF : ringChar F ≠ 2) {n : ℕ} (a : F) (ha : a ≠ 0) (w : Fin n → F) (c : F) :
    (diagCount (Fin.cons a w : Fin (n + 1) → F) c : ℤ) =
      ∑ u : F, (1 + quadraticChar F a * quadraticChar F u) * (diagCount w (c - u) : ℤ) := by
  rw [diagCount_cons]
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun t : F => a * t ^ 2) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (diagCount w (c - u) : ℤ))
    (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const, nsmul_eq_mul,
    card_filter_sq hF a u ha]
  ring

end DiagCount

section DiagFormula

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Helper: $\sum_{u \in F} \chi(c - u) = 0$ (odd characteristic `hF`). -/
lemma sum_chi_sub (hF : ringChar F ≠ 2) (c : F) : ∑ u : F, quadraticChar F (c - u) = 0 := by
  rw [← quadraticChar_sum_zero hF (F := F)]
  exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun u => rfl)

/-- Helper: from even to odd dimension. -/
lemma step_even_odd (hF : ringChar F ≠ 2) {n : ℕ} (a : F) (ha : a ≠ 0) (w : Fin n → F) (c : F)
    (A B : ℤ) (IH : ∀ v : F, (Fintype.card F : ℤ) * diagCount w v =
      A + B * (if v = 0 then (Fintype.card F : ℤ) else 0)) :
    (Fintype.card F : ℤ) * diagCount (Fin.cons a w : Fin (n + 1) → F) c =
      (Fintype.card F : ℤ) * A + B * (Fintype.card F) * (1 + quadraticChar F a * quadraticChar F c) := by
  rw [diagCount_cons_int hF a ha, Finset.mul_sum]
  have h1 : ∀ u : F, (Fintype.card F : ℤ) * ((1 + quadraticChar F a * quadraticChar F u) *
      (diagCount w (c - u) : ℤ)) =
      A + A * quadraticChar F a * quadraticChar F u +
        (if u = c then B * (Fintype.card F) * (1 + quadraticChar F a * quadraticChar F c) else 0) := by
    intro u
    rw [mul_left_comm, IH (c - u)]
    by_cases h : u = c
    · subst h; simp; ring
    · have : c - u ≠ 0 := fun h' => h (sub_eq_zero.mp h').symm
      simp [h, this]; ring
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ c]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, quadraticChar_sum_zero hF]
  ring

/-- Helper: from odd to even dimension. -/
lemma step_odd_even (hF : ringChar F ≠ 2) {n : ℕ} (a : F) (ha : a ≠ 0) (w : Fin n → F) (c : F)
    (K f : ℤ) (IH : ∀ v : F, (diagCount w v : ℤ) = K + f * quadraticChar F v) :
    (diagCount (Fin.cons a w : Fin (n + 1) → F) c : ℤ) =
      (Fintype.card F : ℤ) * K + quadraticChar F a * f *
        (if c = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F (-1) else - quadraticChar F (-1)) := by
  rw [diagCount_cons_int hF a ha, ← sum_chi_mul_chi_sub hF c]
  have h1 : ∀ u : F, (1 + quadraticChar F a * quadraticChar F u) * (diagCount w (c - u) : ℤ) =
      K + f * quadraticChar F (c - u) + K * quadraticChar F a * quadraticChar F u +
        quadraticChar F a * f * (quadraticChar F u * quadraticChar F (c - u)) := by
    intro u; rw [IH (c - u)]; ring
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_chi_sub hF, ← Finset.mul_sum,
    quadraticChar_sum_zero hF]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Helper: $\chi((-1)^{m+1} a P) = \chi(-1)\chi(a)\chi((-1)^{m} P)$. -/
lemma chi_pow_mul (a P : F) (m : ℕ) :
    quadraticChar F ((-1) ^ (m + 1) * (a * P)) =
      quadraticChar F (-1) * quadraticChar F a * quadraticChar F ((-1) ^ m * P) := by
  rw [show ((-1 : F) ^ (m + 1) * (a * P)) = (-1) * a * ((-1) ^ m * P) by ring, map_mul, map_mul]

/-- Helper: $\chi((-1)^{m} a P) = \chi(a)\chi((-1)^{m} P)$. -/
lemma chi_pow_mul' (a P : F) (m : ℕ) :
    quadraticChar F ((-1) ^ m * (a * P)) =
      quadraticChar F a * quadraticChar F ((-1) ^ m * P) := by
  rw [show ((-1 : F) ^ m * (a * P)) = a * ((-1) ^ m * P) by ring, map_mul]

/-- Helper: for $n = 0$ there is exactly one solution (the empty tuple) if $c = 0$, and none otherwise. -/
lemma diagCount_zero (c : F) : diagCount (fun i : Fin 0 => (0 : F)) c = if c = 0 then 1 else 0 := by
  unfold diagCount
  by_cases hc : c = 0
  · subst hc
    simp
  · simp only [hc, ite_false]
    have : IsEmpty {x : Fin 0 → F // ∑ i, (fun _ : Fin 0 => (0 : F)) i * x i ^ 2 = c} :=
      ⟨fun x => hc (by simpa using x.2.symm)⟩
    exact Fintype.card_eq_zero

/-- Helper: the closed formula for diagonal forms, by induction on half the dimension. -/
theorem diagCount_formula (hF : ringChar F ≠ 2) (m : ℕ) :
    (∀ n, n = 2 * m → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (Fintype.card F : ℤ) * diagCount w c = (Fintype.card F : ℤ) ^ n +
        quadraticChar F ((-1) ^ m * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
          (if c = 0 then (Fintype.card F : ℤ) - 1 else -1)) ∧
    (∀ n, n = 2 * m + 1 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (diagCount w c : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
        quadraticChar F c * quadraticChar F ((-1) ^ m * ∏ i, w i) * (Fintype.card F : ℤ) ^ m) := by
  have hq : (Fintype.card F : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- even to odd
  have eo : ∀ m, (∀ n, n = 2 * m → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (Fintype.card F : ℤ) * diagCount w c = (Fintype.card F : ℤ) ^ n +
        quadraticChar F ((-1) ^ m * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
          (if c = 0 then (Fintype.card F : ℤ) - 1 else -1)) →
      (∀ n, n = 2 * m + 1 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (diagCount w c : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
        quadraticChar F c * quadraticChar F ((-1) ^ m * ∏ i, w i) * (Fintype.card F : ℤ) ^ m) := by
    intro m IH n hn w hw c
    subst hn
    obtain ⟨a, w', rfl⟩ : ∃ a w', w = Fin.cons a w' :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    have ha : a ≠ 0 := by simpa using hw 0
    have hw' : ∀ i, w' i ≠ 0 := fun i => by simpa using hw i.succ
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := step_even_odd hF a ha w' c
      ((Fintype.card F : ℤ) ^ (2 * m) - quadraticChar F ((-1) ^ m * ∏ i, w' i) * (Fintype.card F : ℤ) ^ m)
      (quadraticChar F ((-1) ^ m * ∏ i, w' i) * (Fintype.card F : ℤ) ^ m) (fun v => by
        rw [IH (2 * m) rfl w' hw' v]
        split_ifs <;> ring)
    rw [chi_pow_mul']
    apply mul_left_cancel₀ hq
    rw [this]
    ring
  have oe : ∀ m, (∀ n, n = 2 * m + 1 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (diagCount w c : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
        quadraticChar F c * quadraticChar F ((-1) ^ m * ∏ i, w i) * (Fintype.card F : ℤ) ^ m) →
      (∀ n, n = 2 * (m + 1) → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (Fintype.card F : ℤ) * diagCount w c = (Fintype.card F : ℤ) ^ n +
        quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) * (Fintype.card F : ℤ) ^ (m + 1) *
          (if c = 0 then (Fintype.card F : ℤ) - 1 else -1)) := by
    intro m IH n hn w hw c
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hn' : n' = 2 * m + 1 := by omega
    subst hn'
    obtain ⟨a, w', rfl⟩ : ∃ a w', w = Fin.cons a w' :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    have ha : a ≠ 0 := by simpa using hw 0
    have hw' : ∀ i, w' i ≠ 0 := fun i => by simpa using hw i.succ
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := step_odd_even hF a ha w' c
      ((Fintype.card F : ℤ) ^ (2 * m))
      (quadraticChar F ((-1) ^ m * ∏ i, w' i) * (Fintype.card F : ℤ) ^ m) (fun v => by
        rw [IH (2 * m + 1) rfl w' hw' v]
        ring)
    rw [chi_pow_mul, this]
    split_ifs
    · ring
    · ring
  induction m with
  | zero =>
    have e : ∀ n, n = 2 * 0 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (Fintype.card F : ℤ) * diagCount w c = (Fintype.card F : ℤ) ^ n +
        quadraticChar F ((-1) ^ 0 * ∏ i, w i) * (Fintype.card F : ℤ) ^ 0 *
          (if c = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
      intro n hn w hw c
      subst hn
      have : w = fun i => (0 : F) := funext fun i => i.elim0
      subst this
      rw [diagCount_zero]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, pow_zero, one_mul]
      split_ifs <;> simp
    exact ⟨e, eo 0 e⟩
  | succ m ih =>
    have e := oe m ih.2
    exact ⟨e, eo (m + 1) e⟩

end DiagFormula

section Abstract

open Module

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Helper: if $2$ is invertible in $F$ then the characteristic of $F$ is not $2$. -/
lemma ringChar_ne_two_of_invertible : ringChar F ≠ 2 := by
  intro h
  have h1 : ((2 : ℕ) : F) = 0 := by
    have := ringChar.spec F
    rw [h] at this
    exact (this 2).mpr dvd_rfl
  have h2 : (2 : F) = 0 := by exact_mod_cast h1
  exact Invertible.ne_zero (2 : F) h2

/-- Helper: the Gram determinant of an orthogonal basis is the product of the values $Q(v_i)$. -/
lemma discr_of_isOrtho (Q : QuadraticForm F V) {r : ℕ} (v : Basis (Fin r) F V)
    (hv : (associated (R := F) Q).IsOrthoᵢ v) : Q.discr v = ∏ i, Q (v i) := by
  have hM : Q.toMatrix v = Matrix.diagonal fun i => Q (v i) := by
    ext i j
    rw [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply]
    by_cases hij : i = j
    · subst hij
      simp [associated_eq_self_apply]
    · have h0 : associatedHom F Q (v i) (v j) = 0 := hv hij
      simp [Matrix.diagonal, hij, h0]
  rw [QuadraticForm.discr, hM, Matrix.det_diagonal]

/-- Helper: an orthogonal basis of a regular space, with its diagonal normal form and its Gram
determinant. -/
lemma exists_diag_data (Q : QuadraticForm F V) (hQ : (associated Q).Nondegenerate) :
    ∃ v : Basis (Fin (finrank F V)) F V, (∀ i, Q (v i) ≠ 0) ∧
      Nonempty (Q.IsometryEquiv (QuadraticMap.weightedSumSquares F fun i => Q (v i))) ∧
      Q.discr v = ∏ i, Q (v i) ∧ (associated (R := F) Q).IsOrthoᵢ v := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (_root_.QuadraticForm.associated_isSymm F Q)
  have hne : ∀ i, Q (v i) ≠ 0 := fun i => by
    have := hv.not_isOrtho_basis_self_of_separatingLeft hQ.1 i
    simpa [associated_eq_self_apply] using this
  exact ⟨v, hne, ⟨Q.isometryEquivWeightedSumSquares v hv⟩, discr_of_isOrtho Q v hv, hv⟩

/-- Helper: any two bases change the Gram determinant by a nonzero square. -/
lemma discr_eq_sq_mul (Q : QuadraticForm F V) {r : ℕ} (b v : Basis (Fin r) F V) :
    ∃ u : F, u ≠ 0 ∧ Q.discr b = u ^ 2 * Q.discr v := by
  have h := QuadraticForm.discr_comp (b := b) (Q := Q) (N := V) v (LinearMap.id)
  have hc : Q.comp (LinearMap.id : V →ₗ[F] V) = Q := by ext x; simp
  rw [hc] at h
  refine ⟨(LinearMap.toMatrix b v (LinearMap.id : V →ₗ[F] V)).det, ?_, by rw [h]; ring⟩
  intro h0
  have h1 : LinearMap.toMatrix b v LinearMap.id * LinearMap.toMatrix v b LinearMap.id = 1 := by
    rw [← LinearMap.toMatrix_comp v b v]; simp
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- Helper: the number of $x \in V$ with $Q(x) = c$ equals the diagonal count of an orthogonal
basis. -/
lemma card_level_eq_diagCount (Q : QuadraticForm F V) {r : ℕ} (w : Fin r → F)
    (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares F w)) (c : F) :
    Nat.card {x : V // Q x = c} = diagCount w c := by
  rw [Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv
    (p := fun x => Q x = c) (q := fun y => ∑ i, w i * y i ^ 2 = c) (fun x => by
      have h := e.map_app x
      simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at h
      rw [← h]
      simp only [_root_.sq]
      exact Iff.rfl)), Nat.card_eq_fintype_card]
  rfl

/-- Helper: the quadratic character of $(-1)^{m}\cdot$(Gram determinant) does not depend on the basis (for two bases $b$, $v$ indexed by `Fin r`). -/
lemma chi_discr_eq (Q : QuadraticForm F V) {r : ℕ} (b v : Basis (Fin r) F V) (m : ℕ) :
    quadraticChar F ((-1) ^ m * Q.discr b) = quadraticChar F ((-1) ^ m * Q.discr v) := by
  obtain ⟨u, hu, h⟩ := discr_eq_sq_mul Q b v
  rw [h, show ((-1 : F) ^ m * (u ^ 2 * Q.discr v)) = u ^ 2 * ((-1) ^ m * Q.discr v) by ring,
    chi_sq_mul _ _ hu]

/-- **Helper: counts of solutions of $Q = c$, even dimension.** -/
theorem card_level_even (Q : QuadraticForm F V) (hQ : (associated Q).Nondegenerate) (m : ℕ)
    {r : ℕ} (hr : finrank F V = r) (hn : r = 2 * m) (b : Basis (Fin r) F V) (c : F) :
    (Fintype.card F : ℤ) * Nat.card {x : V // Q x = c} = (Fintype.card F : ℤ) ^ (2 * m) +
      quadraticChar F ((-1) ^ m * Q.discr b) * (Fintype.card F : ℤ) ^ m *
        (if c = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
  subst hr
  obtain ⟨v, hne, ⟨e⟩, hd, -⟩ := exists_diag_data Q hQ
  rw [card_level_eq_diagCount Q _ e c,
    (diagCount_formula ringChar_ne_two_of_invertible m).1 (finrank F V) hn _ hne c,
    chi_discr_eq Q b v, hd, ← hn]

/-- **Helper: counts of solutions of $Q = c$, odd dimension.** -/
theorem card_level_odd (Q : QuadraticForm F V) (hQ : (associated Q).Nondegenerate) (m : ℕ)
    {r : ℕ} (hr : finrank F V = r) (hn : r = 2 * m + 1) (b : Basis (Fin r) F V) (c : F) :
    (Nat.card {x : V // Q x = c} : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
      quadraticChar F c * quadraticChar F ((-1) ^ m * Q.discr b) * (Fintype.card F : ℤ) ^ m := by
  subst hr
  obtain ⟨v, hne, ⟨e⟩, hd, -⟩ := exists_diag_data Q hQ
  rw [card_level_eq_diagCount Q _ e c,
    (diagCount_formula ringChar_ne_two_of_invertible m).2 (finrank F V) hn _ hne c,
    chi_discr_eq Q b v, hd]

end Abstract

section FinCoord

open Module

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]

/-- Helper: number of solutions of $Q = c$ on $F^{2m}$, for a regular form $Q$. -/
theorem card_level_even_fin (m : ℕ) (Q : QuadraticForm F (Fin (2 * m) → F))
    (hQ : (associated Q).Nondegenerate) (c : F) :
    (Fintype.card F : ℤ) * Nat.card {x : Fin (2 * m) → F // Q x = c} =
      (Fintype.card F : ℤ) ^ (2 * m) + quadraticChar F ((-1) ^ m * Q.discr') *
        (Fintype.card F : ℤ) ^ m * (if c = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
  have hr : finrank F (Fin (2 * m) → F) = 2 * m := Module.finrank_fin_fun F
  rw [← QuadraticForm.discr_eq_discr']
  exact card_level_even Q hQ m hr rfl (Pi.basisFun F (Fin (2 * m))) c

/-- Helper: number of solutions of $Q = c$ on $F^{2m+1}$, for a regular form $Q$. -/
theorem card_level_odd_fin (m : ℕ) (Q : QuadraticForm F (Fin (2 * m + 1) → F))
    (hQ : (associated Q).Nondegenerate) (c : F) :
    (Nat.card {x : Fin (2 * m + 1) → F // Q x = c} : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
      quadraticChar F c * quadraticChar F ((-1) ^ m * Q.discr') * (Fintype.card F : ℤ) ^ m := by
  have hr : finrank F (Fin (2 * m + 1) → F) = 2 * m + 1 := Module.finrank_fin_fun F
  rw [← QuadraticForm.discr_eq_discr']
  exact card_level_odd Q hQ m hr rfl (Pi.basisFun F (Fin (2 * m + 1))) c

end FinCoord

section Orbit

open QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Helper: the orthogonal complement $x_0^{\perp}$ of a vector $x_0$ (for the bilinear form
$B$ of $Q$). -/
def perp (x₀ : V) : Submodule F V where
  carrier := {y | bil Q x₀ y = 0}
  add_mem' := fun {a b} ha hb => by
    have ha' : bil Q x₀ a = 0 := ha
    have hb' : bil Q x₀ b = 0 := hb
    show bil Q x₀ (a + b) = 0
    rw [bil_add_right, ha', hb', add_zero]
  zero_mem' := by show bil Q x₀ 0 = 0; simp [bil]
  smul_mem' := fun c y hy => by
    have hy' : bil Q x₀ y = 0 := hy
    show bil Q x₀ (c • y) = 0
    rw [bil_smul_right, hy', mul_zero]

/-- Helper: membership in $x_0^{\perp}$ unfolded. -/
lemma mem_perp {x₀ y : V} : y ∈ perp Q x₀ ↔ bil Q x₀ y = 0 := Iff.rfl

/-- Helper: an autometry preserves the bilinear form. -/
lemma bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) (σ y) = bil Q x y := by
  have h1 := hσ (x + y)
  rw [map_add, Q_add, Q_add, hσ x, hσ y] at h1
  have h4 : (2 : F) * bil Q (σ x) (σ y) = 2 * bil Q x y := by linear_combination h1
  exact mul_left_cancel₀ (Invertible.ne_zero (2 : F)) h4

variable {Q}

/-- Helper: the linear functional $y \mapsto B(x_0, y)$. -/
def bilL (Q : QuadraticForm F V) (x₀ : V) : V →ₗ[F] F := QuadraticMap.associated (R := F) Q x₀

/-- Helper: `bilL` evaluated. -/
lemma bilL_apply (x₀ y : V) : bilL Q x₀ y = bil Q x₀ y := rfl

variable {x₀ : V} (hx : Q x₀ = 1)
include hx

/-- Helper: $v - B(x_0, v)\,x_0 \in x_0^{\perp}$ when $Q(x_0) = 1$. -/
lemma proj_mem (v : V) : v - bil Q x₀ v • x₀ ∈ perp Q x₀ := by
  rw [mem_perp, bil_sub_right, bil_smul_right, bil_self, hx]; ring

omit hx in
/-- Helper: the projection $V \to x_0^{\perp}$, $v \mapsto v - B(x_0, v)\, x_0$. -/
def proj (Q : QuadraticForm F V) (x₀ : V) (hx : Q x₀ = 1) : V →ₗ[F] perp Q x₀ :=
  LinearMap.codRestrict (perp Q x₀)
    (LinearMap.id - (bilL Q x₀).smulRight x₀) (fun v => proj_mem hx v)

/-- Helper: the projection onto $x_0^{\perp}$ evaluated. -/
lemma proj_apply (v : V) : (proj Q x₀ hx v : V) = v - bil Q x₀ v • x₀ := rfl

/-- Helper: the projection fixes the elements of $x_0^{\perp}$. -/
lemma proj_of_mem {w : V} (hw : w ∈ perp Q x₀) : proj Q x₀ hx w = ⟨w, hw⟩ := by
  apply Subtype.ext
  rw [proj_apply, (mem_perp Q).mp hw, zero_smul, sub_zero]

/-- Helper: extension of a linear endomorphism $\tau$ of $x_0^{\perp}$ to $V$, fixing $x_0$:
$v \mapsto B(x_0, v)\, x_0 + \tau(\text{proj } v)$. -/
def extL (τ : perp Q x₀ →ₗ[F] perp Q x₀) : V →ₗ[F] V :=
  (bilL Q x₀).smulRight x₀ + (perp Q x₀).subtype ∘ₗ τ ∘ₗ proj Q x₀ hx

/-- Helper: the extension `extL` evaluated. -/
lemma extL_apply (τ : perp Q x₀ →ₗ[F] perp Q x₀) (v : V) :
    extL hx τ v = bil Q x₀ v • x₀ + (τ (proj Q x₀ hx v) : V) := rfl

/-- Helper: the extension of $\tau$ fixes $x_0$. -/
lemma extL_x₀ (τ : perp Q x₀ →ₗ[F] perp Q x₀) : extL hx τ x₀ = x₀ := by
  have : proj Q x₀ hx x₀ = 0 := by
    apply Subtype.ext
    rw [proj_apply, bil_self, hx]; simp
  rw [extL_apply, this]; simp [bil_self, hx]

/-- Helper: the extension of $\tau$ restricts to $\tau$ on $x_0^{\perp}$. -/
lemma extL_of_mem (τ : perp Q x₀ →ₗ[F] perp Q x₀) {w : V} (hw : w ∈ perp Q x₀) :
    extL hx τ w = τ ⟨w, hw⟩ := by
  rw [extL_apply, (mem_perp Q).mp hw, zero_smul, zero_add, proj_of_mem hx hw]

/-- Helper: the extension of $\tau$ preserves $v \mapsto B(x_0, v)$. -/
lemma bil_extL (τ : perp Q x₀ →ₗ[F] perp Q x₀) (v : V) :
    bil Q x₀ (extL hx τ v) = bil Q x₀ v := by
  rw [extL_apply, bil_add_right, bil_smul_right, bil_self, hx,
    (mem_perp Q).mp (τ (proj Q x₀ hx v)).2]; ring

/-- Helper: projecting the extension of $\tau$ gives $\tau$ applied to the projection. -/
lemma proj_extL (τ : perp Q x₀ →ₗ[F] perp Q x₀) (v : V) :
    proj Q x₀ hx (extL hx τ v) = τ (proj Q x₀ hx v) := by
  apply Subtype.ext
  rw [proj_apply, bil_extL hx, extL_apply]
  abel

/-- Helper: extension is compatible with composition. -/
lemma extL_comp (τ τ' : perp Q x₀ →ₗ[F] perp Q x₀) (v : V) :
    extL hx τ (extL hx τ' v) = extL hx (τ ∘ₗ τ') v := by
  rw [extL_apply hx τ, bil_extL hx, proj_extL hx, extL_apply]
  rfl

/-- Helper: the extension of the identity is the identity. -/
lemma extL_id (v : V) : extL hx (LinearMap.id : perp Q x₀ →ₗ[F] perp Q x₀) v = v := by
  rw [extL_apply]
  simp only [LinearMap.id_apply, proj_apply]
  abel

/-- Helper: the extension of an autometry $\tau$ of $Q|_{x_0^{\perp}}$ is an autometry of $Q$. -/
lemma Q_ext (τ : perp Q x₀ →ₗ[F] perp Q x₀)
    (hτ : ∀ w : perp Q x₀, Q (τ w) = Q w) (v : V) : Q (extL hx τ v) = Q v := by
  have hv : v = bil Q x₀ v • x₀ + (proj Q x₀ hx v : V) := by rw [proj_apply]; abel
  have key : ∀ (c : F) (y : V), y ∈ perp Q x₀ → Q (c • x₀ + y) = c ^ 2 + Q y := by
    intro c y hy
    rw [Q_add, Q_smul, hx, bil_smul_left, (mem_perp Q).mp hy]; ring
  rw [extL_apply, key _ _ (τ (proj Q x₀ hx v)).2, hτ]
  conv_rhs => rw [hv, key _ _ (proj Q x₀ hx v).2]

end Orbit

section Stabilizer

open QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V} {x₀ : V} (hx : Q x₀ = 1)
include hx

/-- Helper: the extension, as a linear automorphism of $V$, of an automorphism $\tau$ of
$x_0^{\perp}$ (identity on $x_0$). -/
def extE (τ : perp Q x₀ ≃ₗ[F] perp Q x₀) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinear (extL hx (τ : perp Q x₀ →ₗ[F] perp Q x₀))
    (extL hx (τ.symm : perp Q x₀ →ₗ[F] perp Q x₀))
    (by
      ext v
      rw [LinearMap.comp_apply, extL_comp, show (τ : perp Q x₀ →ₗ[F] perp Q x₀) ∘ₗ
        (τ.symm : perp Q x₀ →ₗ[F] perp Q x₀) = LinearMap.id by ext; simp, extL_id]
      rfl)
    (by
      ext v
      rw [LinearMap.comp_apply, extL_comp, show (τ.symm : perp Q x₀ →ₗ[F] perp Q x₀) ∘ₗ
        (τ : perp Q x₀ →ₗ[F] perp Q x₀) = LinearMap.id by ext; simp, extL_id]
      rfl)

/-- Helper: the extended automorphism `extE` evaluated. -/
lemma extE_apply (τ : perp Q x₀ ≃ₗ[F] perp Q x₀) (v : V) :
    extE hx τ v = bil Q x₀ v • x₀ + (τ (proj Q x₀ hx v) : V) := rfl

/-- Helper: extension of automorphisms of $x_0^{\perp}$ is injective. -/
lemma extE_injective : Function.Injective (extE (Q := Q) (x₀ := x₀) hx) := by
  intro τ τ' h
  ext w
  have h1 := congrArg (fun σ : V ≃ₗ[F] V => σ (w : V)) h
  simp only [extE_apply, (mem_perp Q).mp w.2, zero_smul, zero_add, proj_of_mem hx w.2] at h1
  exact h1

/-- Helper: the stabilizer of $x_0$ in $O(Q)$ is in bijection with $O(Q|_{x_0^{\perp}})$. -/
theorem card_stabilizer :
    Nat.card (MulAction.stabilizer (orth Q) x₀) =
      Nat.card (orth (Q.comp (perp Q x₀).subtype)) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun τ => ⟨⟨extE hx τ.1, fun v => ?_⟩, ?_⟩) ⟨?_, ?_⟩)
  · exact Q_ext hx _ (fun w => τ.2 w) v
  · show extE hx τ.1 x₀ = x₀
    exact extL_x₀ hx _
  · intro τ τ' h
    apply Subtype.ext
    apply extE_injective hx
    exact congrArg (fun z => (z.1.1 : V ≃ₗ[F] V)) h
  · rintro ⟨⟨σ, hσ⟩, hfix⟩
    have hσx : σ x₀ = x₀ := hfix
    have hpres : ∀ w ∈ perp Q x₀, σ w ∈ perp Q x₀ := by
      intro w hw
      rw [mem_perp] at hw ⊢
      have h := bil_orth Q hσ x₀ w
      rw [hσx] at h
      rw [h]; exact hw
    let τ₀ : perp Q x₀ →ₗ[F] perp Q x₀ := (σ : V →ₗ[F] V).restrict hpres
    have hinj : Function.Injective τ₀ := fun a b h =>
      Subtype.ext (σ.injective (congrArg Subtype.val h))
    let τ : perp Q x₀ ≃ₗ[F] perp Q x₀ := LinearEquiv.ofInjectiveEndo τ₀ hinj
    have hτ : ∀ w, τ w = τ₀ w := fun w => by simp [τ]
    have hτo : τ ∈ orth (Q.comp (perp Q x₀).subtype) := by
      intro w
      show Q (τ w : V) = Q w
      rw [hτ]; exact hσ w
    refine ⟨⟨τ, hτo⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext v
    show extE hx τ v = σ v
    rw [extE_apply, hτ]
    conv_rhs => rw [show v = bil Q x₀ v • x₀ + (proj Q x₀ hx v : V) by rw [proj_apply]; abel]
    rw [map_add, map_smul, hσx]
    rfl

end Stabilizer

section OrbitStabilizer

open QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V}

/-- Helper: the orbit of a vector $x_0$ with $Q(x_0) = 1$ under $O(Q)$ is the set
$\{y : Q(y) = 1\}$ (Witt's theorem). -/
lemma orbit_eq_level (hQ : (associated Q).Nondegenerate) {x₀ : V} (hx : Q x₀ = 1) :
    MulAction.orbit (orth Q) x₀ = {y | Q y = 1} := by
  ext y
  constructor
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    show Q (σ x₀) = 1
    rw [hσ, hx]
  · intro hy
    obtain ⟨ρ, hρ⟩ := _root_.QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate Q
      ((QuadraticMap.nondegenerate_polar_iff).mpr ((QuadraticMap.nondegenerate_associated_iff).mp hQ))
      one_ne_zero hx hy
    exact ⟨⟨ρ.toLinearEquiv, fun x => ρ.map_app x⟩, hρ⟩

/-- Helper: **orbit-stabilizer count for the orthogonal group.** If $Q$ is regular and
$Q(x_0) = 1$ then $|O(Q)| = \#\{y : Q(y) = 1\} \cdot |O(Q|_{x_0^{\perp}})|$. -/
theorem card_orth_eq (hQ : (associated Q).Nondegenerate) {x₀ : V} (hx : Q x₀ = 1) :
    Nat.card (orth Q) = Nat.card {y : V // Q y = 1} *
      Nat.card (orth (Q.comp (perp Q x₀).subtype)) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (orth Q) x₀), Nat.card_prod,
    card_stabilizer hx]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => by
    rw [orbit_eq_level hQ hx]; rfl))

/-- Helper: on a regular space with an anisotropic vector, $|O(Q)| = 2\,|O^{+}(Q)|$. -/
theorem card_orth_eq_two_mul (hQ : (associated Q).Nondegenerate) {u : V} (hu : Q u ≠ 0) :
    Nat.card (orth Q) = 2 * Nat.card (orthPlus Q) := by
  have hle : orthPlus Q ≤ orth Q := inf_le_left
  set H : Subgroup (orth Q) := (orthPlus Q).subgroupOf (orth Q) with hH
  have hmem : ∀ b : orth Q, b ∈ H ↔ LinearEquiv.det (b : V ≃ₗ[F] V) = 1 := fun b => by
    rw [hH, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp h).2)
    · intro h; exact Subgroup.mem_inf.mpr ⟨b.2, MonoidHom.mem_ker.mpr h⟩
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨symmetry Q u hu, symmetry_mem_orth Q hu⟩, fun b => ?_⟩
    rw [hmem, hmem]
    have hb := det_orth_eq Q hQ b.2
    have hs := det_symmetry Q hu
    have hne : (-1 : Fˣ) ≠ 1 := by
      intro h
      have := congrArg (fun z : Fˣ => (z : F)) h
      simp only [Units.val_neg, Units.val_one] at this
      have h2 : (2 : F) = 0 := by linear_combination -this
      exact Invertible.ne_zero (2 : F) h2
    show Xor (LinearEquiv.det ((b : V ≃ₗ[F] V) * symmetry Q u hu) = 1) (LinearEquiv.det (b : V ≃ₗ[F] V) = 1)
    rw [map_mul, hs]
    rcases hb with h | h
    · rw [h]; simp [hne]
    · rw [h]; simp [hne]
  have := Subgroup.card_mul_index H
  rw [hidx] at this
  rw [← this, mul_comm]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

end OrbitStabilizer

section PerpFacts

open QuadFormsKB.OMeara Module

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V} {x₀ : V}

/-- Helper: the bilinear form of $Q$ restricted to $x_0^{\perp}$ is the restriction of the bilinear form of $Q$. -/
lemma bil_comp_subtype (w w' : perp Q x₀) :
    associated (R := F) (Q.comp (perp Q x₀).subtype) w w' = bil Q (w : V) (w' : V) := by
  simp [QuadraticMap.associated_comp]

/-- Helper: $x_0^{\perp}$ is regular when $Q$ is regular and $Q(x_0) = 1$. -/
theorem perp_nondegenerate (hQ : (associated Q).Nondegenerate) (hx : Q x₀ = 1) :
    (associated (R := F) (Q.comp (perp Q x₀).subtype)).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ?_).mpr ?_
  · intro a b h
    have := QuadraticMap.associated_isSymm F (Q.comp (perp Q x₀).subtype) a b
    rw [← this]; exact h
  · intro w hw
    have hw' : ∀ w' : perp Q x₀, bil Q (w : V) (w' : V) = 0 := fun w' => by
      rw [← bil_comp_subtype]; exact hw w'
    have hall : ∀ v : V, bil Q (w : V) v = 0 := by
      intro v
      have hv : v = bil Q x₀ v • x₀ + (proj Q x₀ hx v : V) := by rw [proj_apply]; abel
      rw [hv, bil_add_right, bil_smul_right, hw', bil_comm Q (w : V) x₀, (mem_perp Q).mp w.2]
      ring
    have : (w : V) = 0 := hQ.1 (w : V) hall
    exact Subtype.ext this

/-- Helper: $x_0^{\perp}$ has dimension one less than $V$. -/
theorem finrank_perp (hx : Q x₀ = 1) : finrank F (perp Q x₀) + 1 = finrank F V := by
  have hker : perp Q x₀ = LinearMap.ker (bilL Q x₀) := by
    ext y; exact Iff.rfl
  have hrange : LinearMap.range (bilL Q x₀) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • x₀, ?_⟩
    rw [bilL_apply, bil_smul_right, bil_self, hx]; ring
  have := LinearMap.finrank_range_add_finrank_ker (bilL Q x₀)
  rw [hrange, finrank_top, Module.finrank_self, ← hker] at this
  omega

/-- Helper: the Gram determinant of $V$ equals, up to a nonzero square, that of $x_0^{\perp}$
(when $Q(x_0) = 1$). -/
theorem discr_perp (hQ : (associated Q).Nondegenerate) (hx : Q x₀ = 1) {k : ℕ}
    (hk : finrank F (perp Q x₀) = k) (b : Basis (Fin (k + 1)) F V)
    (bW : Basis (Fin k) F (perp Q x₀)) :
    ∃ u : F, u ≠ 0 ∧ Q.discr b = u ^ 2 * QuadraticForm.discr bW (Q.comp (perp Q x₀).subtype) := by
  subst hk
  obtain ⟨vW, -, -, hdW, hoW⟩ := exists_diag_data (Q.comp (perp Q x₀).subtype)
    (perp_nondegenerate hQ hx)
  have hli : ∀ (c : F), ∀ x ∈ perp Q x₀, c • x₀ + x = 0 → c = 0 := by
    intro c x hxW h
    have := congrArg (bil Q x₀) h
    rw [bil_add_right, bil_smul_right, bil_self, hx, (mem_perp Q).mp hxW] at this
    simpa using this
  have hsp : ∀ z : V, ∃ c : F, z + c • x₀ ∈ perp Q x₀ := by
    intro z
    refine ⟨-bil Q x₀ z, ?_⟩
    rw [mem_perp, bil_add_right, bil_smul_right, bil_self, hx]; ring
  let b' := Basis.mkFinCons x₀ vW hli hsp
  have hb' : (associated (R := F) Q).IsOrthoᵢ b' := by
    intro i j hij
    show associatedHom F Q (b' i) (b' j) = 0
    rw [Basis.coe_mkFinCons]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ, Function.comp]
        exact (mem_perp Q).mp (vW j).2
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ, Function.comp]
        show bil Q _ x₀ = 0
        rw [bil_comm Q]; exact (mem_perp Q).mp (vW i).2
      | succ j =>
        simp only [Fin.cons_succ, Function.comp]
        have h0 := hoW (fun h => hij (by rw [h]) : i ≠ j)
        have h1 : associated (R := F) (Q.comp (perp Q x₀).subtype) (vW i) (vW j) = 0 := h0
        rw [bil_comp_subtype] at h1
        exact h1
  have hd' : Q.discr b' = QuadraticForm.discr vW (Q.comp (perp Q x₀).subtype) := by
    rw [discr_of_isOrtho Q b' hb', hdW, Fin.prod_univ_succ]
    simp [b', Basis.coe_mkFinCons, hx]
  obtain ⟨u1, hu1, h1⟩ := discr_eq_sq_mul Q b b'
  obtain ⟨u2, hu2, h2⟩ := discr_eq_sq_mul (Q.comp (perp Q x₀).subtype) vW bW
  refine ⟨u1 * u2, mul_ne_zero hu1 hu2, ?_⟩
  rw [h1, hd', h2]; ring

end PerpFacts

section DimOne

open QuadFormsKB.OMeara Module

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Helper: in dimension one the only proper autometry is the identity, so $|O^{+}(Q)| = 1$. -/
theorem card_orthPlus_dim_one (Q : QuadraticForm F V) (hdim : finrank F V = 1) :
    Nat.card (orthPlus Q) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, (orthPlus Q).one_mem⟩⟩⟩
  have key : ∀ σ : V ≃ₗ[F] V, σ ∈ orthPlus Q → σ = 1 := by
    intro σ hσ
    obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.mp hdim
    obtain ⟨c, hc⟩ := hspan (σ v)
    have hσc : (σ : V →ₗ[F] V) = c • LinearMap.id := by
      refine LinearMap.ext fun w => ?_
      obtain ⟨a, rfl⟩ := hspan w
      simp only [map_smul, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
      rw [← hc]
    have hdet : LinearEquiv.det σ = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hσ).2
    have h1 : c = 1 := by
      have := congrArg (fun z : Fˣ => (z : F)) hdet
      simp only [LinearEquiv.coe_det, Units.val_one] at this
      rw [hσc, LinearMap.det_smul, hdim] at this
      simpa using this
    ext w
    rw [show σ w = (σ : V →ₗ[F] V) w from rfl, hσc, h1]
    simp
  exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)

end DimOne

section ProperOrder

open QuadFormsKB.OMeara Module

universe u

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]

/-- Helper: a finite field in which $2$ is invertible has at least $3$ elements. -/
lemma three_le_card : 3 ≤ Fintype.card F := by
  have hk := FiniteField.odd_card_of_char_ne_two (ringChar_ne_two_of_invertible (F := F))
  have h1 := Fintype.one_lt_card (α := F)
  omega

/-- Helper: a regular space of positive dimension has an anisotropic vector. -/
lemma exists_anisotropic {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (associated Q).Nondegenerate) (hV : 0 < finrank F V) :
    ∃ u, Q u ≠ 0 := by
  by_contra h
  push Not at h
  have hb : ∀ x y, bil Q x y = 0 := by
    intro x y
    have h1 := Q_add Q x y
    rw [h, h, h] at h1
    have : (2 : F) * bil Q x y = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left (Invertible.ne_zero (2 : F))
  have : Subsingleton V := ⟨fun x y => by
    have hx : x = 0 := hQ.1 x (hb x)
    have hy : y = 0 := hQ.1 y (hb y)
    rw [hx, hy]⟩
  have := Module.finrank_zero_of_subsingleton (R := F) (M := V)
  omega

/-- Helper: the Gram determinant of a regular quadratic space in any basis `b` (indexed by `Fin r`, `r` the dimension) is nonzero. -/
lemma discr_ne_zero {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (associated Q).Nondegenerate) {r : ℕ} (hr : finrank F V = r)
    (b : Basis (Fin r) F V) : Q.discr b ≠ 0 := by
  subst hr
  obtain ⟨v, hne, -, hd, -⟩ := exists_diag_data Q hQ
  obtain ⟨u, hu, h⟩ := discr_eq_sq_mul Q b v
  rw [h, hd]
  exact mul_ne_zero (pow_ne_zero 2 hu) (Finset.prod_ne_zero_iff.mpr fun i _ => hne i)

/-- Helper: $\chi(a)\chi(a) = 1$ for $a \ne 0$. -/
lemma chi_sq_eq_one {a : F} (ha : a ≠ 0) : quadraticChar F a * quadraticChar F a = 1 := chi_mul_self ha

/-- Helper: the recursion $|O^{+}(Q)| = R \cdot |O^{+}(Q|_{x_0^{\perp}})|$ for $\dim V \ge 2$,
where $R = \#\{y : Q(y) = 1\}$. -/
theorem card_orthPlus_step {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (associated Q).Nondegenerate) {x₀ : V} (hx : Q x₀ = 1)
    (hdim : 0 < finrank F (perp Q x₀)) :
    Nat.card (orthPlus Q) = Nat.card {y : V // Q y = 1} *
      Nat.card (orthPlus (Q.comp (perp Q x₀).subtype)) := by
  have h1 := card_orth_eq hQ hx
  have h2 := card_orth_eq_two_mul hQ (u := x₀) (by rw [hx]; exact one_ne_zero)
  obtain ⟨u, hu⟩ := exists_anisotropic (perp_nondegenerate hQ hx) hdim
  have h3 := card_orth_eq_two_mul (perp_nondegenerate hQ hx) hu
  rw [h2, h3] at h1
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
  rw [h1]; ring

end ProperOrder

section ProperOrderFormula

open QuadFormsKB.OMeara Module

universe u w

/-- Helper: the closed formula for $|O^{+}|$ in odd dimension $2m + 1$. -/
def OddStmt (F : Type w) [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)] (m : ℕ) : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (associated Q).Nondegenerate → finrank F V = 2 * m + 1 →
    (Nat.card (orthPlus Q) : ℤ) = (Fintype.card F : ℤ) ^ (m * m) *
      ∏ i ∈ Finset.Ico 1 (m + 1), ((Fintype.card F : ℤ) ^ (2 * i) - 1)

/-- Helper: the closed formula for $|O^{+}|$ in even dimension $2m + 2$. -/
def EvenStmt (F : Type w) [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)] (m : ℕ) : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (associated Q).Nondegenerate → ∀ {r : ℕ}, finrank F V = r → r = 2 * m + 2 →
    ∀ b : Basis (Fin r) F V, (Nat.card (orthPlus Q) : ℤ) =
      (Fintype.card F : ℤ) ^ (m * (m + 1)) *
        (∏ i ∈ Finset.Ico 1 (m + 1), ((Fintype.card F : ℤ) ^ (2 * i) - 1)) *
        ((Fintype.card F : ℤ) ^ (m + 1) - quadraticChar F ((-1) ^ (m + 1) * Q.discr b))

variable {F : Type w} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]

/-- Helper: if $q \ge 3$ and $e^{2} = 1$ then $q - e > 0$ and $q + e > 0$. -/
lemma pos_of_sq_one {q e : ℤ} (hq : 3 ≤ q) (he : e * e = 1) : 0 < q - e ∧ 0 < q + e := by
  constructor <;> nlinarith

/-- Helper: the formula in dimension $2m + 2$ follows from the formula in dimension $2m + 1$ (orbit-stabilizer, `card_orthPlus_step`). -/
theorem even_of_odd (m : ℕ) (IH : OddStmt.{u} F m) : EvenStmt.{u} F m := by
  intro V _ _ _ Q hQ r hr hn b
  have hcard := three_le_card (F := F)
  have hqpos : (0 : ℤ) < Fintype.card F := by exact_mod_cast (by omega : 0 < Fintype.card F)
  subst hr
  have hdisc := discr_ne_zero hQ rfl b
  set ε := quadraticChar F ((-1) ^ (m + 1) * Q.discr b) with hε
  have hεε : ε * ε = 1 :=
    chi_sq_eq_one (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdisc)
  have hR := card_level_even Q hQ (m + 1) rfl (by omega) b 1
  rw [if_neg one_ne_zero, ← hε] at hR
  set R := Nat.card {y : V // Q y = 1} with hRdef
  have hq3 : (3 : ℤ) ≤ (Fintype.card F : ℤ) ^ (m + 1) :=
    le_trans (by exact_mod_cast hcard) (le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ Fintype.card F)) (by omega))
  have hRval : (R : ℤ) = (Fintype.card F : ℤ) ^ m * ((Fintype.card F : ℤ) ^ (m + 1) - ε) := by
    apply mul_left_cancel₀ hqpos.ne'
    rw [hR]; ring
  have hRpos : 0 < (R : ℤ) := by
    rw [hRval]
    exact mul_pos (pow_pos hqpos _) (pos_of_sq_one hq3 hεε).1
  have hne : Nonempty {y : V // Q y = 1} := by
    have : 0 < R := by exact_mod_cast hRpos
    exact (Nat.card_pos_iff.mp this).1
  obtain ⟨⟨x₀, hx⟩⟩ := hne
  have hdimW := finrank_perp (Q := Q) (x₀ := x₀) hx
  have hstep := card_orthPlus_step hQ hx (by omega)
  have hW := IH (Q.comp (perp Q x₀).subtype) (perp_nondegenerate hQ hx) (by omega)
  rw [← hRdef] at hstep
  have : (Nat.card (orthPlus Q) : ℤ) = R * Nat.card (orthPlus (Q.comp (perp Q x₀).subtype)) := by
    exact_mod_cast hstep
  rw [this, hW, hRval]
  ring

/-- Helper: the formula in dimension $2m + 3$ follows from the formula in dimension $2m + 2$ (orbit-stabilizer, `card_orthPlus_step`, and `discr_perp` for the determinant of the complement). -/
theorem odd_of_even (m : ℕ) (IH : EvenStmt.{u} F m) : OddStmt.{u} F (m + 1) := by
  intro V _ _ _ Q hQ hdim
  have hcard := three_le_card (F := F)
  have hqpos : (0 : ℤ) < Fintype.card F := by exact_mod_cast (by omega : 0 < Fintype.card F)
  -- a vector of value one, from the count
  have hexists : ∃ x₀ : V, Q x₀ = 1 := by
    have b₁ := Module.finBasis F V
    have hdisc := discr_ne_zero hQ rfl b₁
    have hR := card_level_odd Q hQ (m + 1) rfl hdim b₁ 1
    set ε := quadraticChar F ((-1) ^ (m + 1) * Q.discr b₁) with hε
    have hεε : ε * ε = 1 :=
      chi_sq_eq_one (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdisc)
    have hq3 : (3 : ℤ) ≤ (Fintype.card F : ℤ) ^ (m + 1) :=
      le_trans (by exact_mod_cast hcard)
        (le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ Fintype.card F)) (by omega))
    have hRpos : 0 < (Nat.card {y : V // Q y = 1} : ℤ) := by
      rw [hR, map_one, one_mul,
        show (Fintype.card F : ℤ) ^ (2 * (m + 1)) = (Fintype.card F : ℤ) ^ (m + 1) *
          (Fintype.card F : ℤ) ^ (m + 1) by rw [← pow_add]; ring_nf]
      have := (pos_of_sq_one hq3 hεε).2
      nlinarith [pow_pos hqpos (m + 1)]
    have : 0 < Nat.card {y : V // Q y = 1} := by exact_mod_cast hRpos
    obtain ⟨⟨x₀, hx⟩⟩ := (Nat.card_pos_iff.mp this).1
    exact ⟨x₀, hx⟩
  obtain ⟨x₀, hx⟩ := hexists
  have hdimW := finrank_perp (Q := Q) (x₀ := x₀) hx
  have hstep := card_orthPlus_step hQ hx (by omega)
  have hQW := perp_nondegenerate hQ hx
  set bW := Module.finBasis F (perp Q x₀)
  have hW := IH (Q.comp (perp Q x₀).subtype) hQW rfl (by omega) bW
  let b' : Basis (Fin (finrank F (perp Q x₀) + 1)) F V := Module.finBasisOfFinrankEq F V (by omega)
  obtain ⟨u, hu, hdu⟩ := discr_perp hQ hx rfl b' bW
  have hdisc := discr_ne_zero hQ (r := finrank F (perp Q x₀) + 1) (by omega) b'
  have hR := card_level_odd Q hQ (m + 1) (r := finrank F (perp Q x₀) + 1) (by omega) (by omega) b' 1
  have hchi : quadraticChar F ((-1) ^ (m + 1) * Q.discr b') =
      quadraticChar F ((-1) ^ (m + 1) * QuadraticForm.discr bW (Q.comp (perp Q x₀).subtype)) := by
    rw [hdu, show ((-1 : F) ^ (m + 1) * (u ^ 2 * QuadraticForm.discr bW (Q.comp (perp Q x₀).subtype))) =
      u ^ 2 * ((-1) ^ (m + 1) * QuadraticForm.discr bW (Q.comp (perp Q x₀).subtype)) by ring,
      chi_sq_mul _ _ hu]
  set ε := quadraticChar F ((-1) ^ (m + 1) * Q.discr b') with hε
  have hεε : ε * ε = 1 :=
    chi_sq_eq_one (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdisc)
  rw [map_one, one_mul] at hR
  rw [← hchi] at hW
  have : (Nat.card (orthPlus Q) : ℤ) = Nat.card {y : V // Q y = 1} *
      Nat.card (orthPlus (Q.comp (perp Q x₀).subtype)) := by exact_mod_cast hstep
  rw [this, hW, hR, Finset.prod_Ico_succ_top (show 1 ≤ m + 1 by omega)]
  linear_combination (-((Fintype.card F : ℤ) ^ ((m + 1) * (m + 1)) *
    ∏ i ∈ Finset.Ico 1 (m + 1), ((Fintype.card F : ℤ) ^ (2 * i) - 1))) * hεε

/-- Helper: **the closed formulas for $|O^{+}|$ over a finite field of odd characteristic**, for an abstract regular quadratic space of dimension $2m + 1$ (`OddStmt`) and $2m + 2$ (`EvenStmt`), by induction on $m$. -/
theorem card_orthPlus_formula (m : ℕ) : OddStmt.{u} F m ∧ EvenStmt.{u} F m := by
  have base : OddStmt.{u} F 0 := by
    intro V _ _ _ Q hQ hdim
    have := card_orthPlus_dim_one Q (show finrank F V = 1 by omega)
    simp [this]
  induction m with
  | zero => exact ⟨base, even_of_odd 0 base⟩
  | succ m ih =>
    have h : OddStmt.{u} F (m + 1) := odd_of_even m ih.2
    exact ⟨h, even_of_odd (m + 1) h⟩

end ProperOrderFormula

section FinCoord'

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Invertible (2 : F)]

/-- Helper: `card_level_even_fin` with the dimension given as `n` and a hypothesis `n = 2 * m`. -/
theorem card_level_even_fin' {n : ℕ} (m : ℕ) (hn : n = 2 * m) (Q : QuadraticForm F (Fin n → F))
    (hQ : (associated Q).Nondegenerate) (c : F) :
    (Fintype.card F : ℤ) * Nat.card {x : Fin n → F // Q x = c} =
      (Fintype.card F : ℤ) ^ (2 * m) + quadraticChar F ((-1) ^ m * Q.discr') *
        (Fintype.card F : ℤ) ^ m * (if c = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
  subst hn
  exact card_level_even_fin m Q hQ c

/-- Helper: `card_level_odd_fin` with the dimension given as `n` and a hypothesis `n = 2 * m + 1`. -/
theorem card_level_odd_fin' {n : ℕ} (m : ℕ) (hn : n = 2 * m + 1) (Q : QuadraticForm F (Fin n → F))
    (hQ : (associated Q).Nondegenerate) (c : F) :
    (Nat.card {x : Fin n → F // Q x = c} : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
      quadraticChar F c * quadraticChar F ((-1) ^ m * Q.discr') * (Fintype.card F : ℤ) ^ m := by
  subst hn
  exact card_level_odd_fin m Q hQ c

end FinCoord'

end Ex13Counts

open Ex13Counts


/-- Helper: for $a \ne 0$ in $\mathbb F_p$, Mathlib's `quadraticChar` is Cassels' $\chi$: $\chi(a) = 1$ if $a$ is a
nonzero square and $-1$ otherwise. -/
theorem quadraticChar_eq_cassels_chi (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    quadraticChar (ZMod p) a = if IsSquare a then 1 else -1 := by
  split_ifs with h
  · exact (quadraticChar_one_iff_isSquare ha).mpr h
  · exact quadraticChar_neg_one_iff_not_isSquare.mpr h

section Headlines

open QuadFormsKB.OMeara Module

variable (p : ℕ) [Fact p.Prime] [Invertible (2 : ZMod p)]

/-- **Cassels, Ch. 2, Ex. 13 (iv), p. 31 (odd dimension).** Let $p$ be an odd prime (`p`, with `Fact p.Prime`, `Invertible (2 : ZMod p)`), $m \ge 0$ and `Q` a regular quadratic form (`hQ`) in $n = 2m + 1$ variables over $\mathbb F_p$. Then the number of zeros of $Q$ in $\mathbb F_p^{n}$, including the trivial zero, is $N_{2m+1}(d) = p^{2m}$, independent of the determinant $d$. The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 5$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (iv), p. 31"]
theorem ex13_iv_odd (m : ℕ) (Q : QuadraticForm (ZMod p) (Fin (2 * m + 1) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    Nat.card {x : Fin (2 * m + 1) → ZMod p // Q x = 0} = p ^ (2 * m) := by
  have h := card_level_odd_fin' m rfl Q hQ 0
  rw [quadraticChar_zero, zero_mul, zero_mul, add_zero, ZMod.card] at h
  exact_mod_cast h

/-- **Cassels, Ch. 2, Ex. 13 (iv), p. 31 (even dimension).** Let $p$ be an odd prime, $m > 0$ (`hm`) and `Q` a regular quadratic form (`hQ`) in $n = 2m$ variables over $\mathbb F_p$ with determinant $d$ = `Q.discr'`. Then the number of zeros of $Q$ in $\mathbb F_p^{n}$, including the trivial zero, is $N_{2m}(d) = p^{2m-1} + \chi((-1)^{m} d)(p - 1)p^{m-1}$, where $\chi$ is the quadratic character (an equation of integers). The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 5$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (iv), p. 31"]
theorem ex13_iv_even (m : ℕ) (hm : 0 < m) (Q : QuadraticForm (ZMod p) (Fin (2 * m) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    (Nat.card {x : Fin (2 * m) → ZMod p // Q x = 0} : ℤ) = (p : ℤ) ^ (2 * m - 1) +
      quadraticChar (ZMod p) ((-1) ^ m * Q.discr') * ((p : ℤ) - 1) * (p : ℤ) ^ (m - 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := card_level_even_fin' (n := 2 * (m' + 1)) (m' + 1) rfl Q hQ 0
  simp only [ite_true, ZMod.card] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
  rw [e1, Nat.add_sub_cancel]
  apply mul_left_cancel₀ hp
  linear_combination h

/-- **Cassels, Ch. 2, Ex. 13 (v), p. 32 (odd dimension).** Let $p$ be an odd prime, $m \ge 0$ and `Q` a regular quadratic form (`hQ`) in $n = 2m + 1$ variables over $\mathbb F_p$ with determinant $d$ = `Q.discr'`. Then the number of representations of $1$ by $Q$ is $R_{2m+1}(d) = p^{2m} + \chi((-1)^{m} d)\,p^{m}$. The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 5$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (v), p. 32"]
theorem ex13_v_odd (m : ℕ) (Q : QuadraticForm (ZMod p) (Fin (2 * m + 1) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    (Nat.card {x : Fin (2 * m + 1) → ZMod p // Q x = 1} : ℤ) = (p : ℤ) ^ (2 * m) +
      quadraticChar (ZMod p) ((-1) ^ m * Q.discr') * (p : ℤ) ^ m := by
  have h := card_level_odd_fin' m rfl Q hQ 1
  rw [map_one, one_mul, ZMod.card] at h
  exact h

/-- **Cassels, Ch. 2, Ex. 13 (v), p. 32 (even dimension).** Let $p$ be an odd prime, $m > 0$ (`hm`) and `Q` a regular quadratic form (`hQ`) in $n = 2m$ variables over $\mathbb F_p$ with determinant $d$ = `Q.discr'`. Then the number of representations of $1$ by $Q$ is $R_{2m}(d) = p^{2m-1} - \chi((-1)^{m} d)\,p^{m-1}$. The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 5$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (v), p. 32"]
theorem ex13_v_even (m : ℕ) (hm : 0 < m) (Q : QuadraticForm (ZMod p) (Fin (2 * m) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    (Nat.card {x : Fin (2 * m) → ZMod p // Q x = 1} : ℤ) = (p : ℤ) ^ (2 * m - 1) -
      quadraticChar (ZMod p) ((-1) ^ m * Q.discr') * (p : ℤ) ^ (m - 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := card_level_even_fin' (n := 2 * (m' + 1)) (m' + 1) rfl Q hQ 1
  simp only [one_ne_zero, ite_false, ZMod.card] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
  rw [e1, Nat.add_sub_cancel]
  apply mul_left_cancel₀ hp
  linear_combination h

/-- **Cassels, Ch. 2, Ex. 13 (iii), p. 31.** Let $p$ be an odd prime, $k \ge 1$ (`hk`; so $n = k + 2 \ge 3$), `Q` a regular quadratic form (`hQ`) in $n = k + 2$ variables over $\mathbb F_p$ with determinant $d$ = `Q.discr'`, and `Q'` a regular quadratic form (`hQ'`) in $n - 2 = k$ variables whose determinant lies in the class of $-d$ modulo squares (`hd`: `Q'.discr' = -Q.discr' * c ^ 2` for some $c \ne 0$). Then $N_{n}(d) = p^{n-2}(p - 1) + p\,N_{n-2}(-d)$, i.e. the number of zeros of $Q$ is $p^{k}(p - 1)$ plus $p$ times the number of zeros of $Q'$. (Cassels' hint: $f = x_0 x_1 + g(x_2, \dots, x_{n-1})$; here instead the recursion is deduced from the closed formulas (iv).) The displayed formula is garbled in the machine-read text (the exponent shows as "p^?"); the exponent $n - 2$ was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $3 \le n \le 5$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (iii), p. 31"]
theorem ex13_iii (k : ℕ) (hk : 1 ≤ k) (Q : QuadraticForm (ZMod p) (Fin (k + 2) → ZMod p))
    (hQ : (associated Q).Nondegenerate) (Q' : QuadraticForm (ZMod p) (Fin k → ZMod p))
    (hQ' : (associated Q').Nondegenerate)
    (hd : ∃ c : ZMod p, c ≠ 0 ∧ Q'.discr' = -Q.discr' * c ^ 2) :
    Nat.card {x : Fin (k + 2) → ZMod p // Q x = 0} =
      p ^ k * (p - 1) + p * Nat.card {y : Fin k → ZMod p // Q' y = 0} := by
  obtain ⟨c, hc, hdc⟩ := hd
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · -- k = 2 m, m ≥ 1
    have h1 := card_level_even_fin' (n := k + 2) (m + 1) (by omega) Q hQ 0
    have h2 := card_level_even_fin' (n := k) m hm Q' hQ' 0
    rw [if_pos rfl, ZMod.card] at h1 h2
    have hchi : quadraticChar (ZMod p) ((-1) ^ m * Q'.discr') =
        quadraticChar (ZMod p) ((-1) ^ (m + 1) * Q.discr') := by
      rw [hdc, show ((-1 : ZMod p) ^ m * (-Q.discr' * c ^ 2)) = c ^ 2 * ((-1) ^ (m + 1) * Q.discr') by ring,
        chi_sq_mul _ _ hc]
    rw [hchi] at h2
    subst hm
    have : (Nat.card {x : Fin (2 * m + 2) → ZMod p // Q x = 0} : ℤ) =
        (p : ℤ) ^ (2 * m) * ((p : ℤ) - 1) + p * Nat.card {y : Fin (2 * m) → ZMod p // Q' y = 0} := by
      apply mul_left_cancel₀ hp
      linear_combination h1 - (p : ℤ) * h2
    zify [hp1]
    exact this
  · -- k = 2 m + 1
    have h1 := card_level_odd_fin' (n := k + 2) (m + 1) (by omega) Q hQ 0
    have h2 := card_level_odd_fin' (n := k) m hm Q' hQ' 0
    rw [quadraticChar_zero, zero_mul, zero_mul, add_zero, ZMod.card] at h1 h2
    subst hm
    have : (Nat.card {x : Fin (2 * m + 1 + 2) → ZMod p // Q x = 0} : ℤ) =
        (p : ℤ) ^ (2 * m + 1) * ((p : ℤ) - 1) + p * Nat.card {y : Fin (2 * m + 1) → ZMod p // Q' y = 0} := by
      rw [h1, h2]; ring
    zify [hp1]
    exact this

end Headlines

section HeadlinesVI

open QuadFormsKB.OMeara Module

variable (p : ℕ) [Fact p.Prime] [Invertible (2 : ZMod p)]

/-- **Cassels, Ch. 2, Ex. 13 (vi), p. 32 (odd dimension).** Let $p$ be an odd prime, $m \ge 0$ and `Q` a regular quadratic form (`hQ`) in $n = 2m + 1$ variables over $\mathbb F_p$. Then the order of the group of proper automorphs is $A_{2m+1}(d) = p^{m^{2}}(p^{2} - 1)(p^{4} - 1) \cdots (p^{2m} - 1)$, independent of $d$ (the product is $\prod_{i=1}^{m}(p^{2i} - 1)$, empty for $m = 0$). The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 4$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (vi), p. 32"]
theorem ex13_vi_odd (m : ℕ) (Q : QuadraticForm (ZMod p) (Fin (2 * m + 1) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    (Nat.card (orthPlus Q) : ℤ) =
      (p : ℤ) ^ (m * m) * ∏ i ∈ Finset.Ico 1 (m + 1), ((p : ℤ) ^ (2 * i) - 1) := by
  have h := (card_orthPlus_formula.{0, 0} (F := ZMod p) m).1 Q hQ (by simp)
  rw [ZMod.card] at h
  exact h

/-- **Cassels, Ch. 2, Ex. 13 (vi), p. 32 (even dimension).** Let $p$ be an odd prime, $m > 0$ (`hm`) and `Q` a regular quadratic form (`hQ`) in $n = 2m$ variables over $\mathbb F_p$ with determinant $d$ = `Q.discr'`. Then the order of the group of proper automorphs is $A_{2m}(d) = p^{m(m-1)}(p^{2} - 1)(p^{4} - 1) \cdots (p^{2m-2} - 1)(p^{m} - \varepsilon)$, $\varepsilon = \chi((-1)^{m} d)$ (the product is $\prod_{i=1}^{m-1}(p^{2i} - 1)$). (Cassels' hint $A_n(d) = R_n(d)A_{n-1}(d)$ is the orbit-stabilizer step `card_orthPlus_step`.) The displayed formula is garbled in the machine-read text; it was checked against the page image and numerically by brute-force enumeration for $p \in \{3, 5, 7\}$, $n \le 4$. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (vi), p. 32"]
theorem ex13_vi_even (m : ℕ) (hm : 0 < m) (Q : QuadraticForm (ZMod p) (Fin (2 * m) → ZMod p))
    (hQ : (associated Q).Nondegenerate) :
    (Nat.card (orthPlus Q) : ℤ) =
      (p : ℤ) ^ (m * (m - 1)) * (∏ i ∈ Finset.Ico 1 m, ((p : ℤ) ^ (2 * i) - 1)) *
        ((p : ℤ) ^ m - quadraticChar (ZMod p) ((-1) ^ m * Q.discr')) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := (card_orthPlus_formula.{0, 0} (F := ZMod p) m').2 Q hQ (r := 2 * (m' + 1))
    (by simp) (by omega) (Pi.basisFun (ZMod p) (Fin (2 * (m' + 1))))
  rw [ZMod.card, QuadraticForm.discr_eq_discr'] at h
  rw [h, Nat.add_sub_cancel, mul_comm (m' + 1) m']

end HeadlinesVI

end QuadFormsKB.Cassels.Ch2Ex
