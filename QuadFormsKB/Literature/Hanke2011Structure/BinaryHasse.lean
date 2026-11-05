/-
# Hanke 2011, Lemma 7.2 for $p$ odd: Hasse invariants of binary local genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §7.

Lemma 7.2 (p. 27) tabulates, for $\mathfrak p \nmid 2$, the Hasse invariants $c_{\mathfrak p}$ of the primitive binary local
genera with fixed Hessian determinant $u\pi^\nu$ ($u$ a unit), by Jordan block structure:

| Jordan block structure | $c_{\mathfrak p} = 1$ | $c_{\mathfrak p} = -1$ | condition |
|---|---|---|---|
| $(2)$ | 1 | 0 | – |
| $(1,1)$ | 1 | 1 | $\nu$ odd |
| $(1,1)$ | 2 | 0 | $\nu$ even |

The proof computes $c_{\mathfrak p}(u_1x^2 + \pi^\nu u_2y^2) = (u_1,\pi^\nu u_2)_{\mathfrak p} = \left(\frac{u_1}{\mathfrak p}\right)^\nu$, the two
genera of type $(1,1)$ being given by the two squareclasses of $u_1$ (with $u_1u_2$ fixed). This file formalizes these
Hasse invariant computations over $\mathbb Q_p$, $p$ odd (the repository has the explicit Hilbert symbol
`HilbertLocal.hilbertSymbol_odd_formula` there), with $c$ in Serre's convention
$\prod_{i<j}(a_i,a_j)$ (`hasseLocal`) as in the paper's proof of Lemma 5.10:

* `lemma_7_2_two`: type $(2)$: $c_p(u_1x^2 + u_2y^2) = 1$ for units $u_1, u_2$.
* `lemma_7_2_one_one`: type $(1,1)$: $c_p(u_1x^2 + p^\nu u_2y^2) = \left(\frac{u_1}{p}\right)^\nu$.
* `lemma_7_2_one_one_even`, `lemma_7_2_one_one_odd`: for $\nu$ even both genera have $c_p = 1$; for $\nu$ odd, replacing
  $(u_1, u_2)$ by $(\varepsilon u_1, \varepsilon^{-1}u_2)$ with $\varepsilon$ a nonresidue (same determinant) changes the sign of $c_p$,
  so the two genera have $c_p = 1$ and $c_p = -1$.

The genera themselves, counted with their Hasse invariants, are in `BinaryGeneraOdd.lean` (via Cassels' count of
$\mathbb Z_p$-classes); the dyadic table ($F_{\mathfrak p} = \mathbb Q_2$) is in `DyadicHasseTable.lean`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.Hanke2011Structure.HasseScaling

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.HilbertLocal

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Hasse invariant (Serre's convention) of a binary diagonal form $\langle a_0, a_1\rangle$ is $(a_0,a_1)_K$. -/
theorem hasseLocal_two (K : Type*) [Field K] (a b : K) : hasseLocal K ![a, b] = hilbertSymbol K a b := by
  simp [hasseLocal, Fin.prod_univ_two]

/-- **Lemma 7.2, Jordan type $(2)$, $p$ odd** (Hanke 2011, p. 27): for $p$-adic units $u_1, u_2$,
$c_p(u_1x_0^2 + u_2x_1^2) = (u_1,u_2)_p = 1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (2))"]
theorem lemma_7_2_two (hp2 : p ≠ 2) (u₁ u₂ : ℤ_[p]ˣ) :
    hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), ((u₂ : ℤ_[p]) : ℚ_[p])] = 1 := by
  rw [hasseLocal_two]
  exact hilbertSymbol_units hp2 u₁ u₂

/-- **Lemma 7.2, Jordan type $(1,1)$, $p$ odd** (Hanke 2011, p. 27–28): for $p$-adic units $u_1, u_2$ and $\nu \ge 0$,
$$c_p(u_1x_0^2 + p^\nu u_2x_1^2) = (u_1, p^\nu u_2)_p = \Bigl(\frac{u_1}{p}\Bigr)^{\nu},$$
with $\left(\frac{u_1}{p}\right)$ the quadratic residue character of $u_1$ (`unitChar`). -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27-28 (p ∤ 2, type (1,1))"]
theorem lemma_7_2_one_one (hp2 : p ≠ 2) (ν : ℕ) (u₁ u₂ : ℤ_[p]ˣ) :
    hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * ((u₂ : ℤ_[p]) : ℚ_[p])] = unitChar u₁ ^ ν := by
  rw [hasseLocal_two]
  have h := hilbertSymbol_odd_formula hp2 0 ν u₁ u₂
  simp only [pow_zero, one_mul, zero_mul, mul_one] at h
  exact h

/-- **Lemma 7.2, type $(1,1)$, $\nu$ even** (Hanke 2011, p. 27): both genera have $c_p = 1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (1,1), ν even)"]
theorem lemma_7_2_one_one_even (hp2 : p ≠ 2) {ν : ℕ} (hν : Even ν) (u₁ u₂ : ℤ_[p]ˣ) :
    hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * ((u₂ : ℤ_[p]) : ℚ_[p])] = 1 := by
  rw [lemma_7_2_one_one hp2]
  have h : unitChar u₁ = 1 ∨ unitChar u₁ = -1 := by
    unfold unitChar
    exact quadraticChar_dichotomy (by
      have := (u₁.isUnit.map (PadicInt.toZMod (p := p)))
      exact this.ne_zero)
  rcases h with h | h <;> rw [h]
  · exact one_pow ν
  · exact hν.neg_one_pow

/-- **Lemma 7.2, type $(1,1)$, $\nu$ odd** (Hanke 2011, p. 27): the two genera with determinant $u p^\nu$ have opposite
Hasse invariants. Precisely, there is a unit $\varepsilon$ (a quadratic nonresidue mod $p$) such that, for all units
$u_1, u_2$, the form $\varepsilon u_1x_0^2 + p^\nu\varepsilon^{-1}u_2x_1^2$ (same determinant as $u_1x_0^2 + p^\nu u_2x_1^2$) has
Hasse invariant $-c_p(u_1x_0^2 + p^\nu u_2x_1^2)$, and these are $\pm1$; so $c_p = 1$ and $c_p = -1$ occur once each. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (1,1), ν odd)"]
theorem lemma_7_2_one_one_odd (hp2 : p ≠ 2) {ν : ℕ} (hν : Odd ν) :
    ∃ ε : ℤ_[p]ˣ, ∀ u₁ u₂ : ℤ_[p]ˣ,
      hasseLocal ℚ_[p] ![(((ε * u₁ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * (((ε⁻¹ * u₂ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])] =
        -hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * ((u₂ : ℤ_[p]) : ℚ_[p])] ∧
      (hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * ((u₂ : ℤ_[p]) : ℚ_[p])] = 1 ∨
        hasseLocal ℚ_[p] ![((u₁ : ℤ_[p]) : ℚ_[p]), (p : ℚ_[p]) ^ ν * ((u₂ : ℤ_[p]) : ℚ_[p])] = -1) := by
  -- a nonresidue mod p, lifted to a unit of ℤ_p
  have hring : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨e, he⟩ := quadraticChar_exists_neg_one hring
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  let e' : ℤ_[p] := ((e.val : ℕ) : ℤ_[p])
  have he' : PadicInt.toZMod e' = e := by simp [e']
  have heU : IsUnit e' := by
    by_contra hne
    have hm : e' ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).mpr hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, he'] at hm
    exact he0 hm
  refine ⟨heU.unit, fun u₁ u₂ => ?_⟩
  have hε : unitChar heU.unit = -1 := by
    unfold unitChar; rw [IsUnit.unit_spec, he', he]
  have hmul : unitChar (heU.unit * u₁) = unitChar heU.unit * unitChar u₁ := by
    unfold unitChar; rw [Units.val_mul, map_mul, map_mul]
  have h1 := lemma_7_2_one_one hp2 ν u₁ u₂
  have h2 := lemma_7_2_one_one hp2 ν (heU.unit * u₁) (heU.unit⁻¹ * u₂)
  rw [h1, h2, hmul, hε, neg_one_mul, hν.neg_pow]
  refine ⟨rfl, ?_⟩
  have h : unitChar u₁ = 1 ∨ unitChar u₁ = -1 := by
    unfold unitChar
    exact quadraticChar_dichotomy (u₁.isUnit.map (PadicInt.toZMod (p := p))).ne_zero
  rcases h with h | h <;> rw [h]
  · left; exact one_pow ν
  · right; exact hν.neg_one_pow

end QuadFormsKB.Hanke2011Structure
