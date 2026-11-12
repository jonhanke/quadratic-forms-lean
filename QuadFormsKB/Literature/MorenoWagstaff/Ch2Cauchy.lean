/-
# Moreno–Wagstaff 2005, §2.2: Cauchy's polygonal number theorem

**Source.** A.-L. Cauchy (1813); C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005),
Theorem 2.9 (p. 55–57); see also M. B. Nathanson, *Additive Number Theory: The Classical Bases*, Ch. 1.

**Proves**
* `theorem29` (**proved**, unconditional): for $m \ge 3$ and $n > 0$, $n$ is a sum of four $(m+2)$-gonal numbers
  plus a remainder $r \le m - 2$.

**Method.** The proof follows the book's interval argument from Cauchy's lemma (`lemma27`; Moreno–Wagstaff
p. 55–57, Nathanson), reorganized so that the finite check is independent of $m$ (it only involves $a \le 35$,
$s \le 17$). Write `Realized k s` for "$k = t^2+u^2+v^2+w^2$ and $s = t+u+v+w$ for some naturals $t,u,v,w$".
If `Realized (2a+s) s` then the four $(m+2)$-gonal numbers $p_t,p_u,p_v,p_w$ sum to exactly $m a + s$
(`poly_sum`). Cauchy's lemma gives `Realized (2a+s) s` whenever `Adm a s`
(an odd $s$ with $6a+s < s^2+4$ and $s^2 < 8a+4s$). The intervals $[ma+s,\, ma+s+m-1]$ for admissible
$(a,s)$ cover all $n \ge 1$ (`covering`, using Lemma A), and the last point of each interval is handled by
Lemma B (using a finite check with explicit four-square witnesses).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Proofs

namespace QuadFormsKB.MorenoWagstaff

namespace Cauchy

/-- `Realized k s`: $k = t^2+u^2+v^2+w^2$ and $s = t+u+v+w$ for some natural numbers $t,u,v,w$. -/
abbrev Realized (k s : ℕ) : Prop := ∃ t u v w : ℕ, k = t^2+u^2+v^2+w^2 ∧ s = t+u+v+w

/-- Admissible pairs: $s$ odd, and $k = 2a+s$ satisfies the hypotheses of Cauchy's lemma
($3k < s^2+2s+4$, i.e. $6a + s < s^2 + 4$; and $s^2 < 4k$, i.e. $s^2 < 8a + 4s$). -/
abbrev Adm (a s : ℕ) : Prop := Odd s ∧ 6 * a + s < s ^ 2 + 4 ∧ s ^ 2 < 8 * a + 4 * s

instance (a s : ℕ) : Decidable (Adm a s) := by unfold Adm; infer_instance

/-- Cauchy's lemma in the form needed here: admissible pairs are realized. -/
theorem adm_realized {a s : ℕ} (h : Adm a s) : Realized (2 * a + s) s := by
  obtain ⟨hs, h1, h2⟩ := h
  have hk : Odd (2 * a + s) := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨a + j, by omega⟩
  exact lemma27 (2 * a + s) s hk hs (by linarith) (by nlinarith)

/-- $2 \cdot \lfloor t(t-1)/2 \rfloor + t = t^2$. -/
theorem tri (t : ℕ) : 2 * (t * (t - 1) / 2) + t = t ^ 2 := by
  cases t with
  | zero => simp
  | succ j =>
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self j
    have h1 : (j + 1) * (j + 1 - 1) = c + c := by
      rw [Nat.add_sub_cancel, mul_comm]; exact hc
    rw [h1]
    have : (c + c) / 2 = c := by omega
    rw [this]
    nlinarith

theorem poly_unfold (m t : ℕ) : polygonal (m + 2) t = t + m * (t * (t - 1) / 2) := by
  simp [polygonal]

/-- If `Realized (2a+s) s`, four suitable $(m+2)$-gonal numbers sum to exactly $m a + s$. -/
theorem poly_sum (m a s : ℕ) (h : Realized (2 * a + s) s) :
    ∃ t u v w : ℕ, polygonal (m + 2) t + polygonal (m + 2) u + polygonal (m + 2) v
      + polygonal (m + 2) w = m * a + s := by
  obtain ⟨t, u, v, w, h1, h2⟩ := h
  refine ⟨t, u, v, w, ?_⟩
  have e1 := tri t
  have e2 := tri u
  have e3 := tri v
  have e4 := tri w
  have hsum : t * (t - 1) / 2 + u * (u - 1) / 2 + v * (v - 1) / 2 + w * (w - 1) / 2 = a := by
    omega
  have e : polygonal (m + 2) t + polygonal (m + 2) u + polygonal (m + 2) v + polygonal (m + 2) w
      = (t + u + v + w) + m * (t * (t - 1) / 2 + u * (u - 1) / 2 + v * (v - 1) / 2
        + w * (w - 1) / 2) := by
    simp only [poly_unfold]; ring
  rw [e, hsum]; omega

/-- The conclusion of Theorem 2.9 for given `m`, `n`. -/
def Good (m n : ℕ) : Prop :=
  ∃ t u v w r : ℕ, r ≤ m - 2 ∧ n = polygonal (m + 2) t + polygonal (m + 2) u
    + polygonal (m + 2) v + polygonal (m + 2) w + r

theorem good_of {m a s r n : ℕ} (h : Realized (2 * a + s) s) (hr : r ≤ m - 2)
    (hn : n = m * a + s + r) : Good m n := by
  obtain ⟨t, u, v, w, e⟩ := poly_sum m a s h
  exact ⟨t, u, v, w, r, hr, by omega⟩

/-- Lemma A: if `(a, s)` is admissible but `(a, s+2)` is not, then `(a+1, s)` is admissible. -/
theorem lemmaA {a s : ℕ} (h : Adm a s) (h2 : ¬ Adm a (s + 2)) : Adm (a + 1) s := by
  obtain ⟨hs, h1, h3⟩ := h
  have hup : s ^ 2 ≥ 8 * a + 4 := by
    by_contra hc
    apply h2
    refine ⟨hs.add_even even_two, by nlinarith, by nlinarith⟩
  refine ⟨hs, ?_, by nlinarith⟩
  obtain ⟨j, hj⟩ := hs
  by_cases hc : s ≤ 2 * a + 1
  · nlinarith
  · have hc' : 2 * a + 3 ≤ s := by omega
    nlinarith

/-- The finite check: all small exceptional pairs, with explicit witnesses. -/
theorem small (a s : ℕ) (hs : s ≤ 17) (ha : a ≤ 35) (h : Adm a s) (h2 : ¬ Adm a (s + 2))
    (h4 : ¬ (3 ≤ s ∧ Adm (a + 1) (s - 2))) :
    Realized (2 * a + s + 1) (s - 1) ∨ Realized (2 * a + s + 1) (s + 1) := by
  interval_cases s <;> interval_cases a <;>
  first
  | (exfalso; revert h h2 h4; decide)
  | exact Or.inl ⟨2, 0, 0, 0, rfl, rfl⟩
  | exact Or.inl ⟨2, 2, 0, 0, rfl, rfl⟩
  | exact Or.inl ⟨3, 1, 0, 0, rfl, rfl⟩
  | exact Or.inl ⟨3, 2, 1, 0, rfl, rfl⟩
  | exact Or.inl ⟨3, 3, 0, 0, rfl, rfl⟩
  | exact Or.inl ⟨4, 2, 2, 0, rfl, rfl⟩
  | exact Or.inl ⟨4, 3, 1, 0, rfl, rfl⟩
  | exact Or.inl ⟨5, 1, 1, 1, rfl, rfl⟩
  | exact Or.inl ⟨4, 4, 2, 0, rfl, rfl⟩
  | exact Or.inl ⟨5, 3, 2, 0, rfl, rfl⟩
  | exact Or.inl ⟨5, 4, 3, 0, rfl, rfl⟩
  | exact Or.inl ⟨5, 5, 1, 1, rfl, rfl⟩
  | exact Or.inl ⟨5, 5, 2, 0, rfl, rfl⟩
  | exact Or.inl ⟨6, 4, 4, 0, rfl, rfl⟩
  | exact Or.inl ⟨6, 5, 3, 0, rfl, rfl⟩
  | exact Or.inl ⟨6, 6, 4, 0, rfl, rfl⟩
  | exact Or.inr ⟨2, 2, 2, 2, rfl, rfl⟩
  | exact Or.inr ⟨4, 4, 2, 2, rfl, rfl⟩

/-- Lemma B: the four ways of continuing past the end of an admissible interval. -/
theorem lemmaB {a s : ℕ} (h : Adm a s) :
    Adm a (s + 2) ∨ (3 ≤ s ∧ Adm (a + 1) (s - 2)) ∨ Realized (2 * a + s + 1) (s - 1)
      ∨ Realized (2 * a + s + 1) (s + 1) := by
  by_cases h2 : Adm a (s + 2)
  · exact Or.inl h2
  right
  have hadm := h
  obtain ⟨hs, h1, h3⟩ := h
  have hup : s ^ 2 ≥ 8 * a + 4 := by
    by_contra hc
    apply h2
    refine ⟨hs.add_even even_two, by nlinarith, by nlinarith⟩
  by_cases hbig : 19 ≤ s
  · left
    obtain ⟨p, rfl⟩ : ∃ p, s = p + 2 := ⟨s - 2, by omega⟩
    obtain ⟨j, hj⟩ := hs
    have hp : p + 2 - 2 = p := by omega
    rw [hp]
    refine ⟨by omega, ⟨j - 1, by omega⟩, ?_, ?_⟩ <;> nlinarith
  · rw [not_le] at hbig
    have hs17 : s ≤ 17 := by
      obtain ⟨j, hj⟩ := hs
      omega
    have ha : a ≤ 35 := by nlinarith
    by_cases h4 : 3 ≤ s ∧ Adm (a + 1) (s - 2)
    · exact Or.inl h4
    rcases small a s hs17 ha hadm h2 h4 with h5 | h5
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h5)

/-- Covering: every `n ≥ 1` lies in an interval `[m a + s, m a + s + m - 1]` with `(a, s)` admissible. -/
theorem covering {m : ℕ} (hm : 3 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ a s : ℕ, Adm a s ∧ m * a + s ≤ n ∧ n ≤ m * a + s + (m - 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, 1, ⟨⟨0, rfl⟩, by decide, by decide⟩, by simp, by omega⟩
  | succ n hn ih =>
    obtain ⟨a, s, had, h1, h2⟩ := ih
    by_cases hlt : n < m * a + s + (m - 1)
    · exact ⟨a, s, had, by omega, by omega⟩
    · by_cases h3 : Adm a (s + 2)
      · exact ⟨a, s + 2, h3, by omega, by omega⟩
      · have hA := lemmaA had h3
        have : m * (a + 1) = m * a + m := by ring
        exact ⟨a + 1, s, hA, by omega, by omega⟩

end Cauchy

/-- **Moreno–Wagstaff, Theorem 2.9 (Cauchy's polygonal number theorem)** (p. 55–57): for $m \ge 3$ and every
positive integer $n$, $n = p^{(m+2)}_t + p^{(m+2)}_u + p^{(m+2)}_v + p^{(m+2)}_w + r$ with $0 \le r \le m-2$.
Unconditional: the only inputs are Cauchy's lemma (`lemma27`, proved) and elementary arithmetic. -/
theorem theorem29 : Theorem29 := by
  intro m n hm hn
  obtain ⟨a, s, had, h1, h2⟩ := Cauchy.covering hm n hn
  by_cases hle : n ≤ m * a + s + (m - 2)
  · exact Cauchy.good_of (Cauchy.adm_realized had) (r := n - (m * a + s)) (by omega) (by omega)
  · have hn' : n = m * a + s + (m - 1) := by omega
    have hs := had.1
    have hs1 : 1 ≤ s := by obtain ⟨j, hj⟩ := hs; omega
    rcases Cauchy.lemmaB had with h | ⟨h3, h⟩ | h | h
    · exact Cauchy.good_of (Cauchy.adm_realized h) (r := m - 3) (by omega) (by omega)
    · have e := Cauchy.adm_realized h
      have : m * (a + 1) = m * a + m := by ring
      exact Cauchy.good_of e (r := 1) (by omega) (by omega)
    · have e : Cauchy.Realized (2 * (a + 1) + (s - 1)) (s - 1) := by
        have : 2 * (a + 1) + (s - 1) = 2 * a + s + 1 := by omega
        rw [this]; exact h
      have : m * (a + 1) = m * a + m := by ring
      exact Cauchy.good_of e (r := 0) (by omega) (by omega)
    · have e : Cauchy.Realized (2 * a + (s + 1)) (s + 1) := by
        have : 2 * a + (s + 1) = 2 * a + s + 1 := by omega
        rw [this]; exact h
      exact Cauchy.good_of e (r := m - 2) (by omega) (by omega)

end QuadFormsKB.MorenoWagstaff
