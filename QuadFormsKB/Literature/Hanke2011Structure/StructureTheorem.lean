/-
# Hanke 2011, Theorem 4.8: the $A/B$ decomposition of the total non-archimedean mass

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §4.

Theorem 4.8 says that, for a fixed Hessian determinant squareclass $S$, the primitive total adelic non-archimedean
mass (Definition 3.5)
$$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \sum_{(G_{\mathfrak p}) \in \mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)}\
  \prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$$
equals
$$\tfrac12\,\beta_{n,f}^{-1}(\widetilde S)\prod_{\mathfrak p\in\mathbb S}\widetilde M^{*,(\vec c_{\mathbb S})_{\mathfrak p}}_{\mathfrak p;n}(S_{\mathfrak p})
  \Bigl[\prod_{\mathfrak p\in T\smallsetminus\mathbb S}A^*_{\mathfrak p;n}(S_{\mathfrak p})
   + C_{\varepsilon_\infty,\vec c_{\mathbb S}}\prod_{\mathfrak p\in T\smallsetminus\mathbb S}B^*_{\mathfrak p;n}(S_{\mathfrak p})\Bigr],
  \qquad C_{\varepsilon_\infty,\vec c_{\mathbb S}} = \varepsilon_\infty\prod_{\mathfrak p\in\mathbb S}(\vec c_{\mathbb S})_{\mathfrak p},$$
the coefficient of $S$ in the series identity of the theorem (eq. (12) of the proof). Here $T \supseteq \mathbb S$ is a finite
set of primes containing the dyadic primes, the support of $S$ and $\mathbb S$; outside $T$ the local genus is unique,
with Hasse invariant $1$ and $A^* = B^* = 1$ (Theorem 2.6, Lemma 4.7), so only the primes of $T$ contribute.

**What is formalized.** The derivation (6)–(12) is a finite computation once, for each $\mathfrak p \in T$, the finite set
of local genera $G_{\mathfrak p}$ with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$, their Hasse invariants
$c_{\mathfrak p}(G_{\mathfrak p}) \in \{\pm1\}$ and their local densities $\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p}) \ne 0$ are given.
This file proves it for **arbitrary** such finite data (`LocalGenusData`): `theorem_4_8_coeff` (with the normalized
weights $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$) and `theorem_4_8_mass` (with the
generic density product pulled out, eqs. (6)–(7)). The sets $\mathrm{Gen}^*_{\mathfrak p}(S_{\mathfrak p},\varepsilon;n)$ of local genera of
primitive $\mathcal O_{\mathfrak p}$-valued forms are not constructed here; the theorem applies to them as to any finite data.

*Update*: the proof of Theorem 4.8 applies Lemma 4.17 to
$T \smallsetminus \mathbb S$, which may be empty (e.g. $F = \mathbb{Q}$, $\mathbb S = \{2\}$, $S$ a unit squareclass), while Lemma 4.17
assumes a nonempty set. The conclusion (12) still holds in that case: both sides equal $1$ if
$C_{\varepsilon_\infty,\vec c_{\mathbb S}} = 1$ and $0$ otherwise (`sum_sign_prod_half`, which covers every finite set).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.SignSum

namespace QuadFormsKB.Hanke2011Structure

open Finset

variable {K : Type*} [Field K]

/-- **The sign sum of (12) over every finite set, including the empty one.** For a finite set $T$, $a, b : T \to K$
($K$ a field with $2 \ne 0$) and a sign $C \in \{\pm1\}$:
$$\sum_{\substack{\sigma \in \{\pm1\}^T\\ \prod_i\sigma_i = C}}\ \prod_{i\in T}\frac{a_i + \sigma_ib_i}{2} = \frac12\Bigl[\prod_i a_i + C\prod_i b_i\Bigr].$$
For $T = \emptyset$ both sides are $1$ if $C = 1$ and $0$ if $C = -1$. -/
@[kb "hanke2011structure" "Thm. 4.8, proof, eq. (12), p. 18"]
theorem sum_sign_prod_half (h2 : (2 : K) ≠ 0) {T : Type*} [Fintype T] [DecidableEq T] (a b : T → K)
    (C : ℤˣ) :
    ∑ σ ∈ (univ : Finset (T → ℤˣ)).filter (fun σ => ∏ i, σ i = C), ∏ i, (a i + ((σ i : ℤ) : K) * b i) / 2 =
      (∏ i, a i + ((C : ℤ) : K) * ∏ i, b i) / 2 := by
  rcases isEmpty_or_nonempty T with hT | hT
  · have huniv : (univ : Finset (T → ℤˣ)) = {isEmptyElim} := by
      ext σ; simp only [mem_univ, mem_singleton, true_iff]; funext i; exact isEmptyElim i
    rw [huniv]
    rcases Int.units_eq_one_or C with rfl | rfl
    · rw [Finset.filter_true_of_mem (fun σ _ => by simp)]
      simp
      field_simp
      norm_num
    · rw [Finset.filter_false_of_mem (fun σ _ => by simp)]
      simp
  · rw [sum_sign_prod_eq h2 a b C]
    have hc : Fintype.card T = (Fintype.card T - 1) + 1 :=
      (Nat.sub_add_cancel Fintype.card_pos).symm
    rw [hc, pow_succ, Nat.add_sub_cancel]
    field_simp

/-- **Finite local genus data at the primes of a finite set $T$.** For each $i \in T$ (a prime $\mathfrak p$; `ι` is the
type of these primes): a finite type `G i` (the local genera $G_{\mathfrak p}$ of primitive $\mathcal O_{\mathfrak p}$-valued forms in $n$
variables with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$), the Hasse invariant `hasse i g` $= c_{\mathfrak p}(G_{\mathfrak p}) \in \{\pm1\}$ of each, and its
normalized weight `weight i g` $= \beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$. -/
structure LocalGenusData (ι : Type*) (K : Type*) where
  /-- the local genera at the prime `i` -/
  G : ι → Type*
  /-- finiteness of the set of local genera at each prime -/
  fintype : ∀ i, Fintype (G i)
  /-- the Hasse invariant $c_{\mathfrak p}(G_{\mathfrak p}) \in \{\pm1\}$ -/
  hasse : ∀ i, G i → ℤˣ
  /-- the normalized weight $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ -/
  weight : ∀ i, G i → K

attribute [instance] LocalGenusData.fintype

namespace LocalGenusData

variable {ι : Type*} (D : LocalGenusData ι K)

/-- **The normalized local mass sum** $\widetilde M^{*,\varepsilon}_{\mathfrak p;n}(S_{\mathfrak p}) = \sum_{c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon}
\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$ (Definition 4.6). -/
def massSum (i : ι) (ε : ℤˣ) : K := ∑ g ∈ (univ : Finset (D.G i)).filter (fun g => D.hasse i g = ε), D.weight i g

/-- $A^*_{\mathfrak p;n}(S_{\mathfrak p}) = \widetilde M^{*,+} + \widetilde M^{*,-}$ (Definition 4.6). -/
def A (i : ι) : K := D.massSum i 1 + D.massSum i (-1)

/-- $B^*_{\mathfrak p;n}(S_{\mathfrak p}) = \widetilde M^{*,+} - \widetilde M^{*,-}$ (Definition 4.6). -/
def B (i : ι) : K := D.massSum i 1 - D.massSum i (-1)

theorem massSum_eq (h2 : (2 : K) ≠ 0) (i : ι) (s : ℤˣ) :
    D.massSum i s = (D.A i + ((s : ℤ) : K) * D.B i) / 2 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [A, B] <;> field_simp <;> ring

variable [Fintype ι] [DecidableEq ι]

/-- **Theorem 4.8, coefficientwise** (eqs. (8)–(12) of the proof), for arbitrary finite local genus data `D` at the
primes of a finite set $T$ (the type `ι`). Let $\mathbb S \subseteq T$ (`S`), a Hasse vector $\vec c_{\mathbb S}$ (`c`, read on
$\mathbb S$) and a sign $\varepsilon_\infty$ (`ε`). Then
$$\sum_{\substack{(G_{\mathfrak p})_{\mathfrak p\in T}\\ c_{\mathfrak p}(G_{\mathfrak p}) = c_{\mathfrak p}\ (\mathfrak p\in\mathbb S)\\ \prod_{\mathfrak p\in T}c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon_\infty}}
  \prod_{\mathfrak p\in T}\frac{\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})}{\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})}
  = \prod_{\mathfrak p\in\mathbb S}\widetilde M^{*,c_{\mathfrak p}}_{\mathfrak p;n}\cdot
    \frac12\Bigl[\prod_{\mathfrak p\in T\smallsetminus\mathbb S}A^*_{\mathfrak p;n} + C\prod_{\mathfrak p\in T\smallsetminus\mathbb S}B^*_{\mathfrak p;n}\Bigr],
  \qquad C = \varepsilon_\infty\prod_{\mathfrak p\in\mathbb S}c_{\mathfrak p}.$$ -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17 (coefficientwise, eqs. (8)-(12))"]
theorem theorem_4_8_coeff (h2 : (2 : K) ≠ 0) (S : Finset ι) (c : ι → ℤˣ) (ε : ℤˣ) :
    ∑ g : (∀ i, D.G i),
        (if (∀ i ∈ S, D.hasse i (g i) = c i) ∧ ∏ i, D.hasse i (g i) = ε then ∏ i, D.weight i (g i) else 0) =
      (∏ i ∈ S, D.massSum i (c i)) *
        ((∏ i ∈ Sᶜ, D.A i + ((ε * ∏ i ∈ S, c i : ℤˣ) : ℤ) * ∏ i ∈ Sᶜ, D.B i) / 2) := by
  classical
  -- the local factor with the sign `s` imposed: `e i s x`
  let e : ∀ i, ℤˣ → D.G i → K := fun i s x =>
    if D.hasse i x = s ∧ (i ∈ S → s = c i) then D.weight i x else 0
  -- (a) each term is a sum over sign vectors
  have hstep : ∀ g : (∀ i, D.G i),
      (if (∀ i ∈ S, D.hasse i (g i) = c i) ∧ ∏ i, D.hasse i (g i) = ε then ∏ i, D.weight i (g i) else 0) =
        ∑ σ : ι → ℤˣ, if ∏ i, σ i = ε then ∏ i, e i (σ i) (g i) else 0 := by
    intro g
    rw [Finset.sum_eq_single (fun i => D.hasse i (g i))]
    · by_cases hS : ∀ i ∈ S, D.hasse i (g i) = c i
      · by_cases hε : ∏ i, D.hasse i (g i) = ε
        · rw [if_pos ⟨hS, hε⟩, if_pos hε]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [e, true_and]
          rw [if_pos fun hi => (hS i hi).symm ▸ rfl]
        · rw [if_neg (fun h => hε h.2), if_neg hε]
      · push_neg at hS
        obtain ⟨i, hi, hne⟩ := hS
        rw [if_neg (fun h => hne (h.1 i hi))]
        split_ifs
        · refine (Finset.prod_eq_zero (mem_univ i) ?_).symm
          simp only [e]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (h hi)
        · rfl
    · intro σ _ hσ
      split_ifs
      · obtain ⟨i, hi⟩ : ∃ i, σ i ≠ D.hasse i (g i) := by
          by_contra h; push_neg at h; exact hσ (funext h)
        refine Finset.prod_eq_zero (mem_univ i) ?_
        simp only [e]
        rw [if_neg]
        rintro ⟨h, -⟩
        exact hi h.symm
      · rfl
    · intro h; exact absurd (mem_univ _) h
  rw [Finset.sum_congr rfl fun g _ => hstep g, Finset.sum_comm]
  -- (b) factor the inner sums
  have hfac : ∀ σ : ι → ℤˣ, (∑ g : (∀ i, D.G i), if ∏ i, σ i = ε then ∏ i, e i (σ i) (g i) else 0) =
      if ∏ i, σ i = ε then ∏ i, ∑ x : D.G i, e i (σ i) x else 0 := by
    intro σ
    split_ifs
    · exact (Fintype.prod_sum fun i x => e i (σ i) x).symm
    · simp
  rw [Finset.sum_congr rfl fun σ _ => hfac σ]
  -- (c) each local factor is `(A' + σ B') / 2`
  let A' : ι → K := fun i => if i ∈ S then D.massSum i (c i) else D.A i
  let B' : ι → K := fun i => if i ∈ S then ((c i : ℤ) : K) * D.massSum i (c i) else D.B i
  have hloc : ∀ i (s : ℤˣ), ∑ x : D.G i, e i s x = (A' i + ((s : ℤ) : K) * B' i) / 2 := by
    intro i s
    have hsum : ∑ x : D.G i, e i s x = if (i ∈ S → s = c i) then D.massSum i s else 0 := by
      simp only [e, massSum]
      split_ifs with h
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : D.hasse i x = s
        · rw [if_pos ⟨hx, h⟩, if_pos hx]
        · rw [if_neg (fun h' => hx h'.1), if_neg hx]
      · refine Finset.sum_eq_zero fun x _ => ?_
        rw [if_neg (fun h' => h h'.2)]
    rw [hsum]
    by_cases hi : i ∈ S
    · simp only [A', B', if_pos hi]
      have hc2 : ((c i : ℤ) : K) * ((c i : ℤ) : K) = 1 := by
        rcases Int.units_eq_one_or (c i) with h | h <;> rw [h] <;> simp
      by_cases hs : s = c i
      · subst hs
        rw [if_pos (fun _ => rfl), ← mul_assoc, hc2]
        field_simp
        ring
      · rw [if_neg (fun h => hs (h hi))]
        have : s = -c i := by
          rcases Int.units_eq_one_or s with h1 | h1 <;> rcases Int.units_eq_one_or (c i) with h2 | h2 <;>
            simp_all
        rw [this]
        push_cast
        rw [neg_mul, ← mul_assoc, hc2]
        ring
    · simp only [A', B', if_neg hi]
      rw [if_pos (fun h => absurd h hi), massSum_eq D h2]
  simp only [hloc]
  rw [← Finset.sum_filter, sum_sign_prod_half h2 A' B' ε]
  -- (d) split the products over `S` and its complement
  have hA : ∏ i, A' i = (∏ i ∈ S, D.massSum i (c i)) * ∏ i ∈ Sᶜ, D.A i := by
    rw [← Finset.prod_mul_prod_compl S]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [A', hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [A', Finset.mem_compl.mp hi]
  have hB : ∏ i, B' i =
      (∏ i ∈ S, ((c i : ℤ) : K)) * (∏ i ∈ S, D.massSum i (c i)) * ∏ i ∈ Sᶜ, D.B i := by
    rw [← Finset.prod_mul_prod_compl S, ← Finset.prod_mul_distrib]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [B', hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [B', Finset.mem_compl.mp hi]
  rw [hA, hB]
  push_cast
  ring

/-- **Theorem 4.8 for the masses themselves** (eqs. (6)–(12)): if $\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p}) \ne 0$
(`β i g`) and the generic local densities $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p}) \ne 0$ (`βgen i`) are given, and the weights
are $\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})/\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})$, then the restricted sum of
$\prod_{\mathfrak p\in T}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$ (Definition 3.5, over the primes of $T$) is
$$\prod_{\mathfrak p\in T}\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})^{-1}\cdot\prod_{\mathfrak p\in\mathbb S}\widetilde M^{*,c_{\mathfrak p}}_{\mathfrak p;n}
  \cdot\frac12\Bigl[\prod_{\mathfrak p\in T\smallsetminus\mathbb S}A^*_{\mathfrak p;n} + C\prod_{\mathfrak p\in T\smallsetminus\mathbb S}B^*_{\mathfrak p;n}\Bigr].$$ -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17 (coefficientwise, eqs. (6)-(12))"]
theorem theorem_4_8_mass (h2 : (2 : K) ≠ 0) (β : ∀ i, D.G i → K) (βgen : ι → K) (hgen : ∀ i, βgen i ≠ 0)
    (hw : ∀ i g, D.weight i g = βgen i / β i g) (S : Finset ι) (c : ι → ℤˣ) (ε : ℤˣ) :
    ∑ g : (∀ i, D.G i),
        (if (∀ i ∈ S, D.hasse i (g i) = c i) ∧ ∏ i, D.hasse i (g i) = ε then ∏ i, (β i (g i))⁻¹ else 0) =
      (∏ i, βgen i)⁻¹ * ((∏ i ∈ S, D.massSum i (c i)) *
        ((∏ i ∈ Sᶜ, D.A i + ((ε * ∏ i ∈ S, c i : ℤˣ) : ℤ) * ∏ i ∈ Sᶜ, D.B i) / 2)) := by
  rw [← theorem_4_8_coeff D h2 S c ε, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs
  · simp only [hw, div_eq_mul_inv, Finset.prod_mul_distrib, ← mul_assoc]
    rw [inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ => hgen i), one_mul]
  · rw [mul_zero]

/-- **Theorem 5.7, the counting step.** Suppose the local genera at the prime `i` for the squareclasses $S_{\mathfrak p}$
(data `D`) and $u_{\mathfrak p}S_{\mathfrak p}$ (data `D'`) correspond bijectively (`e`; in the paper: the unit scaling
$G_{\mathfrak p} \mapsto u_{\mathfrak p}G_{\mathfrak p}$, $n$ odd), preserving the normalized weights, and multiplying the Hasse invariant by a fixed sign
$\kappa$ (in the paper $\kappa = 1$ if $n \equiv 1 \pmod 4$ and $\kappa = (u_{\mathfrak p},u_{\mathfrak p})_{\mathfrak p}$ if $n \equiv 3 \pmod 4$,
`NFPlace.hasseSerre_smul_odd`). Then $A^*_{\mathfrak p;n}(u_{\mathfrak p}S_{\mathfrak p}) = A^*_{\mathfrak p;n}(S_{\mathfrak p})$ and
$B^*_{\mathfrak p;n}(u_{\mathfrak p}S_{\mathfrak p}) = \kappa\,B^*_{\mathfrak p;n}(S_{\mathfrak p})$. -/
@[kb "hanke2011structure" "Thm. 5.7, p. 24 (counting step)"]
theorem theorem_5_7_of_bijection (D' : LocalGenusData ι K) (i : ι) (e : D.G i ≃ D'.G i) (κ : ℤˣ)
    (hw : ∀ g, D'.weight i (e g) = D.weight i g) (hh : ∀ g, D'.hasse i (e g) = κ * D.hasse i g) :
    D'.A i = D.A i ∧ D'.B i = ((κ : ℤ) : K) * D.B i := by
  have hm : ∀ s : ℤˣ, D'.massSum i s = D.massSum i (κ * s) := by
    intro s
    simp only [massSum, Finset.sum_filter]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hh, hw]
    have : (κ * D.hasse i g = s) ↔ (D.hasse i g = κ * s) := by
      have hκ : κ * κ = 1 := by rcases Int.units_eq_one_or κ with h | h <;> rw [h] <;> decide
      constructor <;> intro h
      · rw [← h, ← mul_assoc, hκ, one_mul]
      · rw [h, ← mul_assoc, hκ, one_mul]
    by_cases h : D.hasse i g = κ * s
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
  rcases Int.units_eq_one_or κ with rfl | rfl
  · simp [A, B, hm]
  · simp only [A, B, hm, mul_neg, mul_one, neg_neg, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one]
    constructor <;> ring

end LocalGenusData

end QuadFormsKB.Hanke2011Structure
