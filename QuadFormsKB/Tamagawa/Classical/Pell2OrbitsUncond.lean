/-
# Dirichlet's count for $x_0^2-2x_1^2$ for every $m\ge1$

**Layer:** $\mathbb Q$.

`dirichlet_pell2_orbits` (`BinaryJacobi.lean`) assumes that $m$ is represented by $x_0^2-2x_1^2$ over $\mathbb Q$. Here that
hypothesis is removed: if $m$ is not a value of $x_0^2-2x_1^2$ over $\mathbb Z$, there are no elements of norm $m$ in
$\mathbb Z[\sqrt2]$, and $\sum_{d\mid m}\chi_8(d) = 0$, since a nonzero divisor sum forces every prime $q\equiv3,5\pmod8$
to divide $m$ to an even power (`even_padicValNat_of_sum_chi8_ne_zero`), which makes $m$ a value (`pell2_value_iff`).
-/
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi
import QuadFormsKB.Tamagawa.Classical.BinaryUncond

open MulAction

namespace QuadFormsKB.Tamagawa.Classical

/-- **Dirichlet's count for $x_0^2 - 2x_1^2$, every $m\ge1$, from Siegel's formula:** for every $m\ge1$, the number of
elements of norm $m$ of $\mathbb Z[\sqrt2]$ (`normSet 2 m`) modulo the norm-one units $\pm(3+2\sqrt2)^k$
(`unitary (ℤ√2)`, `pell2_units`), i.e. of solutions of $x_0^2 - 2x_1^2 = m$ in $\mathbb Z^2$ modulo the automorphs
$\begin{psmallmatrix}a&2b\\b&a\end{psmallmatrix}$, $a^2-2b^2 = 1$, is
$$\sum_{d\mid m}\chi_8(d),\qquad\chi_8 = \left(\tfrac8\cdot\right) = \texttt{ZMod.χ₈}.$$
If $m$ is not a value of $x_0^2-2x_1^2$ both sides vanish (`pell2_value_iff`). This is `dirichlet_pell2_orbits` without
its hypothesis that $m$ is represented over $\mathbb Q$. Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93 (number of representations by a genus) [unverified locator]"]
theorem dirichlet_pell2_orbits_uncond (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card (orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m)) : ℝ) =
      ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  by_cases hval : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = m
  · obtain ⟨x, y, hxy⟩ := hval
    exact dirichlet_pell2_orbits m hm ⟨![x, y], by simp; exact_mod_cast hxy⟩
  · have hE : IsEmpty (normSet 2 m) :=
      ⟨fun z => hval ⟨(normSetEquivPell2 m z).1 0, (normSetEquivPell2 m z).1 1, (normSetEquivPell2 m z).2⟩⟩
    have hQ : IsEmpty (orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m)) :=
      ⟨fun q => Quotient.inductionOn' q fun z => hE.false z⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
    by_contra hs
    exact hval (pell2_value_iff.2 fun q hq h8 =>
      even_padicValNat_of_sum_chi8_ne_zero hm0 (Ne.symm hs) (Nat.prime_of_mem_primeFactors hq) h8)

end QuadFormsKB.Tamagawa.Classical
