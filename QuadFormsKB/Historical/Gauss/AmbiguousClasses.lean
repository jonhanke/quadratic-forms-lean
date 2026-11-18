import QuadFormsKB.Historical.Gauss.RootForms

/-!
# A form properly equivalent to its opposite is properly equivalent to an ambiguous form (*Disq. Arith.* Arts. 163-165, 170)

the historical sources (Art. 170, last clause), via Gauss's Art. 165. Throughout, $(a, b, c)$ is `gaussForm a b c`.

* `art165_ambiguousClause` (proved, unconditional): `Art165AmbiguousClause`, i.e. if $(a, b, c)$ is properly
  equivalent to $(a, -b, c)$ then it is properly equivalent to some $(a', b', c')$ with $a' \mid 2 b'$. It is proved
  for **all** integers $a, b, c$, including degenerate determinants (square or zero determinant): no hypothesis on
  $b^2 - ac$ is needed.
* `art170_ambiguousClause` (proved, unconditional): `Art170AmbiguousClause`, by `art170_ambiguousClause_of_art165`.

Proof (a modern form of Arts. 163-165). Composing the proper equivalence with $(x, y) \mapsto (x, -y)$ gives an
improper automorph $S = (\alpha\ \beta;\ \gamma\ \delta)$, $\alpha\delta - \beta\gamma = -1$. If the form is not
identically zero, comparing with the Gram matrix gives $\alpha + \delta = 0$ (hence $\alpha^2 + \beta\gamma = 1$), so
$S$ has a primitive fixed vector $v = (p, r)$. Completing $v$ to a unimodular matrix with second column $w = (q, s)$,
one has $S w + w = k v$ for an integer $k$, and the bilinear form of the automorph gives $2B = k A$ for the new
form $(A, B, C)$, so $A \mid 2B$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- A nonzero fixed vector of an integer matrix can be made primitive and completed to a unimodular matrix. -/
private theorem ambig_fixed_primitive (α β γ δ w1 w2 : ℤ) (hne : ¬(w1 = 0 ∧ w2 = 0))
    (h1 : α * w1 + β * w2 = w1) (h2 : γ * w1 + δ * w2 = w2) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ α * p + β * r = p ∧ γ * p + δ * r = r := by
  have hpos : 0 < Int.gcd w1 w2 := by
    rcases not_and_or.mp hne with h | h
    · exact Int.gcd_pos_iff.mpr (Or.inl h)
    · exact Int.gcd_pos_iff.mpr (Or.inr h)
  obtain ⟨g, p, r, hg, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hpos
  have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have e1 : (α * p + β * r - p) * (g : ℤ) = 0 := by linear_combination h1
  have e2 : (γ * p + δ * r - r) * (g : ℤ) = 0 := by linear_combination h2
  have f1 := (mul_eq_zero.mp e1).resolve_right hg'
  have f2 := (mul_eq_zero.mp e2).resolve_right hg'
  have hb := Int.gcd_eq_gcd_ab p r
  rw [hcop] at hb
  refine ⟨p, -Int.gcdB p r, r, Int.gcdA p r, ?_, by linarith, by linarith⟩
  push_cast at hb
  linear_combination -hb

/-- The core of Art. 165: an improper automorph of a form that is not identically zero. -/
private theorem ambig_core (a b c α β γ δ : ℤ) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0))
    (E1 : a * α ^ 2 + 2 * b * α * γ + c * γ ^ 2 = a)
    (E2 : a * α * β + b * (α * δ + β * γ) + c * γ * δ = b)
    (E3 : a * β ^ 2 + 2 * b * β * δ + c * δ ^ 2 = c)
    (hdet : α * δ - β * γ = -1) :
    ∃ a' b' c' : ℤ, a' ∣ 2 * b' ∧ SLEquiv (gaussForm a b c) (gaussForm a' b' c') := by
  have ha : a * (α + δ) = 0 := by
    linear_combination (-δ) * E1 + γ * E2 + (a * α + b * γ) * hdet
  have hc : c * (α + δ) = 0 := by
    linear_combination (-α) * E3 + β * E2 + (b * β + c * δ) * hdet
  have hb2 : 2 * (b * (α + δ)) = 0 := by
    linear_combination (-δ) * E2 + γ * E3 + β * E1 - α * E2 + (a * β + b * δ + b * α + c * γ) * hdet
  have hb : b * (α + δ) = 0 := by linarith
  have hs : α + δ = 0 := by
    by_contra h
    exact hne ⟨(mul_eq_zero.mp ha).resolve_right h, (mul_eq_zero.mp hb).resolve_right h,
      (mul_eq_zero.mp hc).resolve_right h⟩
  have hδ : δ = -α := by linarith
  subst hδ
  have hq : α ^ 2 + β * γ = 1 := by linear_combination -hdet
  -- a nonzero fixed vector
  have hfix : ∃ w1 w2 : ℤ, ¬(w1 = 0 ∧ w2 = 0) ∧ α * w1 + β * w2 = w1 ∧ γ * w1 + (-α) * w2 = w2 := by
    by_cases h : β = 0 ∧ 1 - α = 0
    · refine ⟨α + 1, γ, ?_, by linear_combination hq, by ring⟩
      rintro ⟨h1, -⟩
      have : α = 1 := by linarith [h.2]
      omega
    · exact ⟨β, 1 - α, h, by ring, by linear_combination hq⟩
  obtain ⟨w1, w2, hw, hw1, hw2⟩ := hfix
  obtain ⟨p, q, r, s, hps, hf1, hf2⟩ := ambig_fixed_primitive α β γ (-α) w1 w2 hw hw1 hw2
  have hz : p * (γ * q + (-α) * s + s) - r * (α * q + β * s + q) = 0 := by
    linear_combination (-(γ * q + (-α) * s)) * hf1 + (α * q + β * s) * hf2 + (p * s - r * q) * hdet
  have hx : α * q + β * s + q = (s * (α * q + β * s + q) - q * (γ * q + (-α) * s + s)) * p := by
    linear_combination (-(α * q + β * s + q)) * hps + q * hz
  have hy : γ * q + (-α) * s + s = (s * (α * q + β * s + q) - q * (γ * q + (-α) * s + s)) * r := by
    linear_combination (-(γ * q + (-α) * s + s)) * hps + s * hz
  have hiso : a * (α * p + β * r) * (α * q + β * s) +
      b * ((α * p + β * r) * (γ * q + (-α) * s) + (γ * p + (-α) * r) * (α * q + β * s)) +
      c * (γ * p + (-α) * r) * (γ * q + (-α) * s) = a * p * q + b * (p * s + q * r) + c * r * s := by
    linear_combination (p * q) * E1 + (p * s + r * q) * E2 + (r * s) * E3
  have hdiff : a * p * (α * q + β * s) + b * (p * (γ * q + (-α) * s) + r * (α * q + β * s)) +
      c * r * (γ * q + (-α) * s) = a * p * q + b * (p * s + q * r) + c * r * s := by
    linear_combination hiso - (a * (α * q + β * s) + b * (γ * q + (-α) * s)) * hf1 -
      (b * (α * q + β * s) + c * (γ * q + (-α) * s)) * hf2
  have hfin : 2 * (a * p * q + b * (p * s + q * r) + c * r * s) =
      (s * (α * q + β * s + q) - q * (γ * q + (-α) * s + s)) *
        (a * p ^ 2 + 2 * b * p * r + c * r ^ 2) := by
    linear_combination (-1) * hdiff + (a * p + b * r) * hx + (b * p + c * r) * hy
  refine ⟨a * p ^ 2 + 2 * b * p * r + c * r ^ 2, a * p * q + b * (p * s + q * r) + c * r * s,
    a * q ^ 2 + 2 * b * q * s + c * s ^ 2, Dvd.intro_left
      (s * (α * q + β * s + q) - q * (γ * q + (-α) * s + s)) (by linear_combination -hfin), ?_⟩
  refine (sLEquiv_iff _ _).mpr ⟨p, q, r, s, hps, ?_⟩
  rw [subst_gaussForm]

/-- **Gauss's Art. 165** (*Disq. Arith.* Arts. 163-165): if $(a, b, c)$ is properly
equivalent to its opposite $(a, -b, c)$, then it is properly equivalent to an ambiguous form $(a', b', c')$, i.e.
one with $a' \mid 2 b'$. Proved for all integers $a, b, c$ (the zero form is handled separately; no hypothesis on
the determinant $b^2 - ac$ is needed, degenerate determinants included). Differences from Gauss: none in content;
Gauss argues with the ratio of the two automorphs of Arts. 162-163, here an improper automorph is used directly. -/
@[kb "gauss1801" "Art. 165"]
theorem art165_ambiguousClause : Art165AmbiguousClause := by
  intro a b c h
  by_cases hz : a = 0 ∧ b = 0 ∧ c = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hz
    exact ⟨0, 0, 0, dvd_refl _, SLEquiv.refl _⟩
  obtain ⟨p, q, r, s, hd, hsub⟩ := (sLEquiv_iff _ _).mp h
  rw [subst_gaussForm] at hsub
  have h1 : a * p ^ 2 + 2 * b * p * r + c * r ^ 2 = a := by
    have := congrArg BinQF.a hsub; simpa using this
  have h2 : a * p * q + b * (p * s + q * r) + c * r * s = -b := by
    have := congrArg BinQF.b hsub; simp at this; linarith
  have h3 : a * q ^ 2 + 2 * b * q * s + c * s ^ 2 = c := by
    have := congrArg BinQF.c hsub; simpa using this
  exact ambig_core a b c p (-q) r (-s) hz (by linear_combination h1) (by linear_combination -h2)
    (by linear_combination h3) (by linear_combination -hd)

/-- **Art. 170 (ii), last clause** (*Disq. Arith.* Art. 170): if $M \ne 0$ and
$(a, b, c)$ has primitive representations of $M$ with values $N$ and $-N$, then $(a, b, c)$ is properly equivalent
to an ambiguous form $(a', b', c')$ with $a' \mid 2 b'$. Proved unconditionally from `art170_converse` and
`art165_ambiguousClause` (`art170_ambiguousClause_of_art165`); no difference from the source. -/
@[kb "gauss1801" "Art. 170"]
theorem art170_ambiguousClause : Art170AmbiguousClause :=
  art170_ambiguousClause_of_art165 art165_ambiguousClause

end QuadFormsKB.Historical.Gauss
