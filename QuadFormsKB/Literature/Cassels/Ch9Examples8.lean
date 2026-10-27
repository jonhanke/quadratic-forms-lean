/-
# Cassels, Chapter 9, Example 2: the list of proper classes of discriminant −23 is complete

**Layer:** integral binary forms `BinQF` ($ax^2 + bxy + cy^2$, `BinQF.mk`, `BinQF.subst`), proper equivalence
`Binary.SLEquiv` (= `Siegel.ProperIntEquiv`, `properIntEquiv_iff_sLEquiv`), positive definiteness `BinQF.PosDef'`
($a > 0$, $b^2 - 4ac < 0$).

**Proves**
* Lagrange–Gauss reduction (`exists_reduced`): every positive definite binary form is properly equivalent to one with
  $\lvert b\rvert \le a \le c$ (same discriminant);
* the last part of Example 2 (p. 162, `ex2_complete`): *every positive-definite integer-valued form with the same
  determinant as $x^2 + xy + 6y^2$, $2x^2 + xy + 3y^2$, $2x^2 - xy + 3y^2$ is properly integrally equivalent to one of
  them.* (Same determinant: discriminant $b^2 - 4ac = -23$, i.e. Cassels' $d = 23/4$.)

*Proof.* Reduce; a reduced form has $3a^2 \le 4ac - b^2 = 23$, so $a \le 2$, $b$ odd, and $(a, b, c)$ is one of
$(1, \pm 1, 6)$, $(2, \pm 1, 3)$; and $(1, -1, 6) \sim (1, 1, 6)$ by $x \mapsto x + y$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples2
import QuadFormsKB.Binary.FormsIdeals

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel

open BinQF

/-- `subst` with determinant $1$ gives a properly equivalent form. -/
theorem sLEquiv_subst (f : BinQF) {p q r s : ℤ} (h : p * s - q * r = 1) : Binary.SLEquiv f (subst p q r s f) :=
  (Binary.sLEquiv_iff _ _).2 ⟨p, q, r, s, h, rfl⟩

/-- **Lagrange–Gauss reduction** (by strong induction on $a$): a positive definite binary form is properly
equivalent to a form $g$ with $\lvert b(g)\rvert \le a(g) \le c(g)$ and the same discriminant. -/
theorem exists_reduced : ∀ (N : ℕ) (f : BinQF), f.a.toNat = N → f.PosDef' →
    ∃ g : BinQF, Binary.SLEquiv f g ∧ |g.b| ≤ g.a ∧ g.a ≤ g.c ∧ g.disc = f.disc := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hN hf
    obtain ⟨ha, hd⟩ := hf
    -- translate: `b' = b + 2ak ∈ [-a, a)`
    set k : ℤ := -((f.b + f.a) / (2 * f.a)) with hk
    set f₁ := subst 1 k 0 1 f with hf₁
    have h₁ : Binary.SLEquiv f f₁ := sLEquiv_subst f (by ring)
    have hd₁ : f₁.disc = f.disc := disc_subst_of_det _ _ _ _ _ (by ring)
    have ha₁ : f₁.a = f.a := by simp [hf₁, subst]
    have hb₁ : f₁.b = f.b + 2 * f.a * k := by simp [hf₁, subst]; ring
    have h2a : (0 : ℤ) < 2 * f.a := by omega
    have hbnd : -f.a ≤ f₁.b ∧ f₁.b < f.a := by
      rw [hb₁, hk]
      have h1 := Int.emod_add_mul_ediv (f.b + f.a) (2 * f.a)
      have h2 := Int.emod_nonneg (f.b + f.a) h2a.ne'
      have h3 := Int.emod_lt_of_pos (f.b + f.a) h2a
      constructor <;> nlinarith
    have hc₁ : 0 < f₁.c := by
      have : f₁.disc < 0 := hd₁ ▸ hd
      simp only [BinQF.disc] at this
      nlinarith [sq_nonneg f₁.b]
    by_cases hac : f₁.a ≤ f₁.c
    · exact ⟨f₁, h₁, abs_le.2 ⟨by linarith [hbnd.1, ha₁], by linarith [hbnd.2, ha₁]⟩, hac, hd₁⟩
    · -- swap: `(x, y) ↦ (-y, x)`
      set f₂ := subst 0 (-1) 1 0 f₁ with hf₂
      have h₂ : Binary.SLEquiv f₁ f₂ := sLEquiv_subst f₁ (by ring)
      have hd₂ : f₂.disc = f₁.disc := disc_subst_of_det _ _ _ _ _ (by ring)
      have ha₂ : f₂.a = f₁.c := by simp [hf₂, subst]
      have hlt : f₂.a.toNat < N := by rw [← hN, ha₂]; rw [ha₁] at hac; omega
      obtain ⟨g, hg, hgb, hgc, hgd⟩ := ih _ hlt f₂ rfl ⟨by rw [ha₂]; exact hc₁, by rw [hd₂, hd₁]; exact hd⟩
      exact ⟨g, h₁.trans (h₂.trans hg), hgb, hgc, by rw [hgd, hd₂, hd₁]⟩

/-- A form is determined by $a, b, c$: $f = $ `mk f.a f.b f.c`. -/
theorem eq_mk_abc (f : BinQF) : f = mk f.a f.b f.c := BinQF.ext_abc (by simp) (by simp) (by simp)

/-- **Cassels, Ch. 9, Example 2** (p. 162), last part: *every positive-definite integer-valued form with the same
determinant as these forms is properly integrally equivalent to one of them*: a positive definite binary form of
discriminant $-23$ is properly equivalent to $x^2 + xy + 6y^2$, $2x^2 + xy + 3y^2$ or $2x^2 - xy + 3y^2$. -/
@[kb "cassels1978" "Ch. 9, Ex. 2, p. 162 (the list is complete)"]
theorem ex2_complete (f : BinQF) (hf : f.PosDef') (hD : f.disc = -23) :
    ProperIntEquiv f ex2f1 ∨ ProperIntEquiv f ex2f2 ∨ ProperIntEquiv f ex2f3 := by
  obtain ⟨g, hfg, hb, hac, hgd⟩ := exists_reduced _ f rfl hf
  rw [hD] at hgd
  simp only [BinQF.disc] at hgd
  have hb' := abs_le.1 hb
  have ha3 : g.a ≤ 2 := by nlinarith
  have ha0 : 0 < g.a := by nlinarith
  have hcases : (g.a = 1 ∧ g.b = 1 ∧ g.c = 6) ∨ (g.a = 1 ∧ g.b = -1 ∧ g.c = 6) ∨
      (g.a = 2 ∧ g.b = 1 ∧ g.c = 3) ∨ (g.a = 2 ∧ g.b = -1 ∧ g.c = 3) := by
    interval_cases h : g.a
    · have : g.b = -1 ∨ g.b = 0 ∨ g.b = 1 := by omega
      rcases this with h' | h' | h' <;> rw [h'] at hgd
      · right; left; exact ⟨rfl, h', by omega⟩
      · omega
      · left; exact ⟨rfl, h', by omega⟩
    · have : g.b = -2 ∨ g.b = -1 ∨ g.b = 0 ∨ g.b = 1 ∨ g.b = 2 := by omega
      rcases this with h' | h' | h' | h' | h' <;> rw [h'] at hgd
      · omega
      · right; right; right; exact ⟨rfl, h', by omega⟩
      · omega
      · right; right; left; exact ⟨rfl, h', by omega⟩
      · omega
  rw [eq_mk_abc g] at hfg
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] at hfg
  · exact Or.inl hfg
  · refine Or.inl (hfg.trans ?_)
    have := sLEquiv_subst (mk 1 (-1) 6) (p := 1) (q := 1) (r := 0) (s := 1) (by ring)
    convert this using 1
    simp [ex2f1, subst]
  · exact Or.inr (Or.inl hfg)
  · exact Or.inr (Or.inr hfg)

end QuadFormsKB.Siegel
