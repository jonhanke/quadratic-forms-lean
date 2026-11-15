/-
# Chenevier–Lannes, §3.4.2: the arithmetic of the third proof of the holy constructions

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.2, Proposition 3.4.2.6, p. 67, Proposition 3.4.2.14,
p. 72, Proposition 3.4.2.18 and the discussion after it, pp. 74. Printed page numbers.

The book's third proof of Theorem 3.4.2.10 (c) ($\mathrm{vois}_h(L; \rho)$ has no roots) runs as follows. If
$L' = \mathrm{vois}_h(L; \rho)$ has roots, with Coxeter number $h'$, Proposition 3.4.2.6 (applied to $L'$ and $x = \rho$)
gives a root $\alpha'$ of $L'$ with $(\rho \cdot \alpha')^2 \le h(h + 1)/(h'(h' + 1))$, and Proposition 3.4.2.14 says
that $\nu = |\rho \cdot \alpha'|$ is divisible neither by $h$ nor by $h + 1$ but shares a factor with each
(Proposition 3.4.2.18). So the set $S(h, h')$ of such $\nu$ is nonempty. The rest is arithmetic, **proved here**:
- `sSet_mono`, `sSet_two_eq_empty`, `sSet_25`: $S(h, h'_1) \subset S(h, h'_2)$ for $h'_1 \ge h'_2$; $S(h, 2) = \emptyset$
  for the Coxeter numbers $h \ne 25$ of Table 1.1; $S(25, 2) = \{10\}$, $S(25, 3) = \emptyset$; hence
  `coxeter_of_sSet_nonempty`: $S(h, h') \ne \emptyset$ with $h' \ge 2$ forces $h = 25$, $h' = 2$;
- `no_admissible_24A1`: for $h = 25$, $h' = 2$ (so $R(L') = 24\mathbf{A}_1$, by the classification), there is no family
  of $24$ integers $\rho \cdot \beta$ ($\beta \in R'^+$) obeying the constraints of Proposition 3.4.2.14 with
  $\sum_\beta (\rho \cdot \beta)^2 = 2600$ (the value given by Scholium 2.3.4 and Proposition 3.4.2.5).

**States** `RootInfBound` (Proposition 3.4.2.6; the book's proof uses Bourbaki's positivity of the dual basis of a
basis of $R$) and `HolyRootConstraints` (Proposition 3.4.2.14; its proof uses Scholium 3.4.2.7, Proposition 3.4.2.15 and
Corollary 3.4.2.17, which rest on Proposition 3.4.2.6 and Scholium 3.4.1.3). Assembling the third proof would also need
the transport of these statements to $L'$ (a lattice of $\mathbb{Q}^{24}$ given by a basis) and the classification
($h' = 2 \Rightarrow R(L') = 24\mathbf{A}_1$); not done.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.Borcherds

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

/-! ### The named statements -/

/-- **Proposition 3.4.2.6** (Chenevier–Lannes, p. 67; named statement, the inequality): for a Niemeier lattice $L$ with
roots, Coxeter number $h$, and $x \in V$, some root $\alpha$ has $(\alpha \cdot x)^2 \le q(x)/(h(h + 1))$. (The equality
case, $x = \lambda\rho$, is not stated.) The book's proof uses the dual basis of a basis of $R$ and Bourbaki,
Chap. VI, §1, Théorème 2, Remarque 2; not formalized. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.6, p. 67"]
def RootInfBound : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ x : Fin 24 → ℚ,
    ∃ α ∈ rootSet Q, bQ Q (cv α) x ^ 2 * (coxeterNumber Q * (coxeterNumber Q + 1)) ≤ Q.evalIn ℚ x

/-- **Admissible values of $\rho \cdot \alpha'$** (the four conditions of Chenevier–Lannes, Proposition 3.4.2.14,
p. 72, on $t = |\rho \cdot \alpha'|$): $h \nmid t$, $(h + 1) \nmid t$, $\gcd(t, h) \ne 1$, $\gcd(t, h + 1) \ne 1$. -/
def AdmissibleDot (h t : ℕ) : Prop := ¬ h ∣ t ∧ ¬ (h + 1) ∣ t ∧ Nat.gcd t h ≠ 1 ∧ Nat.gcd t (h + 1) ≠ 1

instance (h t : ℕ) : Decidable (AdmissibleDot h t) := by unfold AdmissibleDot; infer_instance

/-- **Proposition 3.4.2.14** (Chenevier–Lannes, p. 72; named statement): for a Niemeier lattice $L$ with roots,
Coxeter number $h$, a Weyl vector $\rho \in L$, $v \in L$ with $\rho \cdot v \equiv 1 \bmod h$ and a root $\alpha'$ of
$\mathrm{vois}_h(L; \rho)$ (`voisLat Q h ρ v`; roots are the vectors with $q = 1$), the integer $t = |\rho \cdot
\alpha'|$ satisfies (a.1) $h \nmid t$, (a.2) $\gcd(t, h) \ne 1$, (b.1) $(h + 1) \nmid t$, (b.2) $\gcd(t, h + 1) \ne 1$.
($\rho \cdot \alpha'$ is an integer, as $\rho \in M_h(L; \rho) \subset \mathrm{vois}_h(L; \rho)$, an integral
lattice.) -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14, p. 72"]
def HolyRootConstraints : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ (h : ℕ), coxeterNumber Q = h →
    ∀ ρ : Fin 24 → ℤ, IsWeylVector Q (cv ρ) → ∀ v : Fin 24 → ℤ, (h : ℤ) ∣ bZ Q ρ v - 1 →
      ∀ α' ∈ voisLat Q h ρ v, Q.evalIn ℚ α' = 1 →
        ∃ t : ℕ, (bQ Q (cv ρ) α' = t ∨ bQ Q (cv ρ) α' = -t) ∧ AdmissibleDot h t

/-! ### The sets $S(h, h')$ -/

/-- **The set $S(h, h')$** (Chenevier–Lannes, p. 74): the integers $\nu$ with (1) $\nu > 0$,
(2) $\nu^2 \le h(h + 1)/(h'(h' + 1))$, (3) $\gcd(\nu, h) \ne 1$ and $\gcd(\nu, h + 1) \ne 1$; as a finite set
(`mem_sSet` shows that the bound $\nu \le h$ loses nothing when $h' \ge 1$). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.18, p. 74 (the set S(h, h'))"]
def sSet (h h' : ℕ) : Finset ℕ :=
  (Finset.range (h + 1)).filter fun ν => 0 < ν ∧ ν ^ 2 * (h' * (h' + 1)) ≤ h * (h + 1) ∧
    Nat.gcd ν h ≠ 1 ∧ Nat.gcd ν (h + 1) ≠ 1

theorem mem_sSet {h h' ν : ℕ} (hh' : 1 ≤ h') :
    ν ∈ sSet h h' ↔ 0 < ν ∧ ν ^ 2 * (h' * (h' + 1)) ≤ h * (h + 1) ∧ Nat.gcd ν h ≠ 1 ∧ Nat.gcd ν (h + 1) ≠ 1 := by
  unfold sSet
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun hc => ⟨?_, hc⟩⟩
  by_contra hν
  push Not at hν
  have h2 : 2 ≤ h' * (h' + 1) := by nlinarith
  have : (h + 1) ^ 2 * 2 ≤ ν ^ 2 * (h' * (h' + 1)) := by
    have := Nat.pow_le_pow_left hν 2
    nlinarith
  nlinarith [hc.2.1]

/-- $S(h, h'_1) \subset S(h, h'_2)$ for $h'_1 \ge h'_2$ (Chenevier–Lannes, p. 74). Unconditional. -/
theorem sSet_mono {h h₁ h₂ : ℕ} (h21 : h₂ ≤ h₁) : sSet h h₁ ⊆ sSet h h₂ := by
  intro ν hν
  unfold sSet at hν ⊢
  rw [Finset.mem_filter] at hν ⊢
  refine ⟨hν.1, hν.2.1, le_trans ?_ hν.2.2.1, hν.2.2.2⟩
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h21 (by omega))

/-- **$S(h, 2) = \emptyset$ for $h \ne 25$** (Chenevier–Lannes, p. 74), for the Coxeter numbers $h$ of Table 1.1.
Unconditional, by computation. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 74 (S(h, 2) = ∅ for h ≠ 25)"]
theorem sSet_two_eq_empty : ∀ e ∈ niemeierRootTable, e.2 ≠ 25 → sSet e.2 2 = ∅ := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  decide

/-- **$S(25, 2) = \{10\}$ and $S(25, 3) = \emptyset$** (Chenevier–Lannes, p. 74). Unconditional, by computation. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 74 (S(25, 2) = {10}, S(25, 3) = ∅)"]
theorem sSet_25 : sSet 25 2 = {10} ∧ sSet 25 3 = ∅ := by
  decide

/-- **The numerical core of the third proof of Theorem 3.4.2.10 (c)** (Chenevier–Lannes, p. 74): if $h$ is a Coxeter
number of Table 1.1, $h' \ge 2$ and $S(h, h') \ne \emptyset$, then $h = 25$ and $h' = 2$. Unconditional. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 74 (S(h, h') ≠ ∅ forces h = 25, h' = 2)"]
theorem coxeter_of_sSet_nonempty {e : Multiset ADEType × ℕ} (he : e ∈ niemeierRootTable) {h' : ℕ} (hh' : 2 ≤ h')
    (hS : (sSet e.2 h').Nonempty) : e.2 = 25 ∧ h' = 2 := by
  have h25 : e.2 = 25 := by
    by_contra hne
    have := sSet_mono (h := e.2) hh'
    rw [sSet_two_eq_empty e he hne] at this
    obtain ⟨ν, hν⟩ := hS
    exact absurd (this hν) (Finset.notMem_empty ν)
  refine ⟨h25, ?_⟩
  by_contra hne
  have h3 : 3 ≤ h' := by omega
  have := sSet_mono (h := 25) h3
  rw [sSet_25.2] at this
  obtain ⟨ν, hν⟩ := hS
  rw [h25] at hν
  exact absurd (this hν) (Finset.notMem_empty ν)

/-! ### The case $h = 25$, $R(L') = 24\mathbf{A}_1$ -/

/-- The admissible values for $h = 25$ up to $50$: $t^2 = 100$ or $t^2 \ge 400$. -/
theorem admissible25_sq : ∀ t : Fin 51, AdmissibleDot 25 t → (t : ℕ) ^ 2 = 100 ∨ 400 ≤ (t : ℕ) ^ 2 := by
  decide

/-- **The final contradiction for $h = 25$** (Chenevier–Lannes, p. 74): there is no family $(t_\beta)$ of $24$ natural
numbers, each admissible for $h = 25$ in the sense of Proposition 3.4.2.14 (`AdmissibleDot 25`), with
$\sum_\beta t_\beta^2 = 2600$. (The book: not all $t_\beta$ are $10$ since $24 \cdot 10^2 \ne 2600$; an admissible
$t \ne 10$ is $\ge 20$; then some other $t_\beta \le 9$, as $23 \cdot 10^2 > 2600 - 20^2$, which is not admissible.)
Unconditional. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 74 (the case h = 25)"]
theorem no_admissible_24A1 (t : Fin 24 → ℕ) (ht : ∀ i, AdmissibleDot 25 (t i)) :
    ∑ i, t i ^ 2 ≠ 2600 := by
  intro hsum
  have hbound : ∀ i, t i ≤ 50 := by
    intro i
    have := Finset.single_le_sum (f := fun i => t i ^ 2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    by_contra hlt
    push Not at hlt
    nlinarith
  have hcase : ∀ i, t i ^ 2 = 100 ∨ 400 ≤ t i ^ 2 := fun i =>
    admissible25_sq ⟨t i, by have := hbound i; omega⟩ (ht i)
  have hge : ∀ i, 100 ≤ t i ^ 2 := fun i => by rcases hcase i with h | h <;> omega
  by_cases hall : ∀ i, t i ^ 2 = 100
  · simp [hall] at hsum
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hj4 : 400 ≤ t j ^ 2 := (hcase j).resolve_left hj
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 24)) (fun i => t i ^ 2) (Finset.mem_univ j)
    have hrest : 23 * 100 ≤ ∑ i ∈ Finset.univ.erase j, t i ^ 2 := by
      have := Finset.card_nsmul_le_sum (Finset.univ.erase j) (fun i => t i ^ 2) 100 (fun i _ => hge i)
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)] at this
      simpa using this
    omega

end QuadFormsKB.ChenevierLannes
