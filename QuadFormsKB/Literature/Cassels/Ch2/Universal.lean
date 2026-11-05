/-
# Cassels, Chapter 2, §2: universal spaces

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, §2, *Isotropic spaces*, pp. 15–16.

**Setting.** Cassels' quadratic space $(U, \phi)$ with $\phi(u) = \phi(u, u)$ is a Mathlib quadratic form
`Q : QuadraticForm K V` with $Q(u) = \phi(u)$; it *represents* $b$ if $Q(u) = b$ for some $u$. A regular space is
*anisotropic* if it does not represent $0$ non-trivially (Mathlib's `QuadraticMap.Anisotropic`), and *isotropic*
otherwise.

**Proves.**
* The definition on p. 15: Cassels calls a regular space *universal* if it represents every non-zero element of $k$.
  The library's predicate is O'Meara's `QuadFormsKB.OMeara.IsUniversal` ($Q(V) = k$, O'Meara 41A); since $Q(0) = 0$
  the two agree (`isUniversal_iff_forall_ne_zero`).
* The Corollary to Lemma 2.2 (p. 16), `universal_and_anisotropic` and `exists_universal_anisotropic`: over a finite
  field of odd order (Cassels: $\mathbb F_p$, $p \ne 2$) the regular binary form $x_0^{2} + a x_1^{2}$ with $-a$ not a
  square is universal and anisotropic, so a space can be universal without being isotropic.
-/
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Literature.Cassels.Ch2.Basic

open QuadraticMap

namespace QuadFormsKB.Cassels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Cassels, Ch. 2, §2, p. 15 (definition: universal).** Cassels calls the regular space $(U, \phi)$ *universal*
if it represents every non-zero $b \in k$; the library's `OMeara.IsUniversal Q` asks that $Q$ take every value
$b \in k$ (O'Meara's $Q(V) = F$). The two agree, because $Q(0) = 0$. -/
@[kb "cassels1978" "Ch. 2, §2, p. 15 (definition: universal space)"]
theorem isUniversal_iff_forall_ne_zero (Q : QuadraticForm K V) :
    OMeara.IsUniversal Q ↔ ∀ b : K, b ≠ 0 → ∃ u : V, Q u = b := by
  refine ⟨fun h b _ => h b, fun h b => ?_⟩
  by_cases hb : b = 0
  · exact ⟨0, by rw [hb, QuadraticMap.map_zero]⟩
  · exact h b hb

/-- The binary diagonal form $x_0^{2} + a x_1^{2}$ on $k^{2}$. -/
def oneA (a : K) : QuadraticForm K (Fin 2 → K) := weightedSumSquares K ![1, a]

theorem oneA_apply (a : K) (x : Fin 2 → K) : oneA a x = x 0 ^ 2 + a * x 1 ^ 2 := by
  simp [oneA, weightedSumSquares_apply, Fin.sum_univ_two, _root_.sq]

private theorem ringChar_ne_two [Fintype K] (hK : Fintype.card K % 2 = 1) : ringChar K ≠ 2 := by
  intro h
  have := FiniteField.even_card_iff_char_two.mp h
  omega

/-- **Cassels, Ch. 2, Lemma 2.2, Corollary (p. 16).** Let $k$ be a finite field of odd order (Cassels:
$k = \mathbb F_p$, $p \ne 2$ prime) and let $a \in k$ with $-a$ not a square. Then the binary form
$x_0^{2} + a x_1^{2}$ (Cassels' normal basis with $\phi(u_1) = 1$, $\phi(u_2) = a$) is regular, universal and
anisotropic. -/
@[kb "cassels1978" "Ch. 2, Lemma 2.2, Cor., p. 16"]
theorem universal_and_anisotropic [Fintype K] (hK : Fintype.card K % 2 = 1) {a : K} (ha : ¬IsSquare (-a)) :
    (polarBilin (oneA a)).Nondegenerate ∧ OMeara.IsUniversal (oneA a) ∧ (oneA a).Anisotropic := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ x : Fin 2 → K, (∀ y, polarBilin (oneA a) x y = 0) → x = 0 := by
      intro x hx
      have h0 := hx (Pi.single 0 1)
      have h1 := hx (Pi.single 1 1)
      simp [polarBilin_apply_apply, polar, oneA_apply] at h0 h1
      have h2 : (2 : K) ≠ 0 := by
        intro h
        apply ringChar_ne_two hK
        exact ringChar.eq_iff.mpr ((CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h))
      have e0 : 2 * x 0 = 0 := by linear_combination h0
      have e1 : 2 * (a * x 1) = 0 := by linear_combination h1
      ext i
      fin_cases i
      · simpa [h2] using e0
      · simpa [h2, ha0] using e1
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    rw [polarBilin_apply_apply, polar_comm]
    simpa [polarBilin_apply_apply] using hy x
  · rw [isUniversal_iff_forall_ne_zero]
    intro b _
    obtain ⟨x, y, h⟩ := binary_universal_finiteField hK (a := 1) (b := a) one_ne_zero ha0 b
    exact ⟨![x, y], by rw [oneA_apply]; simpa using h⟩
  · intro x hx
    rw [oneA_apply] at hx
    by_cases h1 : x 1 = 0
    · have : x 0 = 0 := by rw [h1] at hx; simpa using hx
      ext i; fin_cases i <;> simp [this, h1]
    · exfalso
      apply ha
      refine ⟨x 0 / x 1, ?_⟩
      field_simp
      linear_combination -hx


/-- **Cassels, Ch. 2, Lemma 2.2, Corollary (p. 16), as stated:** over a finite field of odd order a regular
binary space can be universal without being isotropic. -/
@[kb "cassels1978" "Ch. 2, Lemma 2.2, Cor., p. 16 (existence)"]
theorem exists_universal_anisotropic [Fintype K] (hK : Fintype.card K % 2 = 1) :
    ∃ Q : QuadraticForm K (Fin 2 → K),
      (polarBilin Q).Nondegenerate ∧ OMeara.IsUniversal Q ∧ Q.Anisotropic := by
  have h2 : ringChar K ≠ 2 := ringChar_ne_two hK
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare h2
  exact ⟨oneA (-n), universal_and_anisotropic hK (by simpa using hn)⟩

end QuadFormsKB.Cassels
