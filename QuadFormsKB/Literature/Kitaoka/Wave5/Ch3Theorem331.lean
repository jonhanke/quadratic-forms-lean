/-
# Kitaoka 1993, Theorem 3.3.1 (2) and (4): $(a, 1 - a) = 1$ and continuity of the Hilbert symbol

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §3.3, Theorem 3.3.1, parts (2) and (4), p. 54
(printed page).

**Setting.** $F$ is a local field, $\mathbb Q_p$ or $\mathbb R$, and $(a, b)_F = 1$ if
$\langle a\rangle \perp \langle b\rangle \perp \langle -1\rangle$ is isotropic, $-1$ otherwise (`hilbertSymbol F a b`,
defined by "$z^2 = ax^2 + by^2$ has a nontrivial solution", the same condition).

**Proves** (unconditional).
* `theorem331_2`: $(a, -a)_F = (a, 1 - a)_F = 1$ for $a \ne 0, 1$ (the identity $(a, 1 - a) = 1$ holds over every
  field: $1^2 = a \cdot 1^2 + (1 - a) \cdot 1^2$).
* `theorem331_4_padic`, `theorem331_4_real` (part (4)): $(a, b) \mapsto (a, b)_F$ is continuous on
  $F^\times \times F^\times$, i.e. locally constant: for $a, b \in F^\times$, $(a', b')_F = (a, b)_F$ for all $(a', b')$
  in a neighbourhood of $(a, b)$ (`∀ᶠ x in 𝓝 (a, b), …`; the values $\pm 1$ are discrete).

**Proof.** (Kitaoka: "(4) follows from the fact that $(F^\times)^2$ is open".) Over $\mathbb Q_p$: if
$\|a' - a\| < \|4\|\,\|a\|$ then $a'/a = 1 + 4\alpha$ with $\alpha \in p\mathbb Z_p$, a square in $\mathbb Z_p$ by Hensel's
lemma (`OMeara.isSquare_one_add_four_mul`); the symbol does not see squares. Over $\mathbb R$ the symbol depends only on
the signs, which are locally constant.
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Theorem523
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch3Hasse342

open Filter Topology

noncomputable section

namespace QuadFormsKB.Kitaoka.Theorem331

/-- **Kitaoka 1993, Theorem 3.3.1 (2)** (p. 54): $(a, -a)_F = 1$ and $(a, 1 - a)_F = 1$ for $a \ne 0, 1$. Stated over
any field $F$ (Kitaoka: $F = \mathbb Q_p$ or $\mathbb R$). Unconditional. -/
@[kb "kitaoka1993" "§3.3, Thm. 3.3.1 (2), p. 54"]
theorem theorem331_2 (F : Type*) [Field F] (a : F) :
    hilbertSymbol F a (-a) = 1 ∧ hilbertSymbol F a (1 - a) = 1 := by
  refine ⟨hilbertSymbol_self_neg F a, ?_⟩
  unfold hilbertSymbol
  exact ite_eq_left ⟨1, 1, 1, by simp, by ring⟩

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Squares are open in $\mathbb Q_p^\times$: every $x$ near $a \ne 0$ is $c^2 a$ with $c \ne 0$. -/
theorem eventually_sq_mul {a : ℚ_[p]} (ha : a ≠ 0) : ∀ᶠ x in 𝓝 a, ∃ c : ℚ_[p], c ≠ 0 ∧ x = c ^ 2 * a := by
  have : HenselianLocalRing ℤ_[p] := henselianLocalRing_padicInt p
  have h4 : (4 : ℚ_[p]) ≠ 0 := by norm_num
  have hε : 0 < ‖(4 : ℚ_[p])‖ * ‖a‖ := mul_pos (norm_pos_iff.mpr h4) (norm_pos_iff.mpr ha)
  filter_upwards [Metric.ball_mem_nhds a hε] with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  set α : ℚ_[p] := (x - a) / (4 * a) with hα
  have hαn : ‖α‖ < 1 := by
    rw [hα, norm_div, norm_mul, div_lt_one (mul_pos (norm_pos_iff.mpr h4) (norm_pos_iff.mpr ha))]
    exact hx
  let α' : ℤ_[p] := ⟨α, hαn.le⟩
  have hmem : α' ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact hαn
  obtain ⟨r, hr⟩ := OMeara.isSquare_one_add_four_mul hmem
  have hr' : (1 : ℚ_[p]) + 4 * α = (r : ℚ_[p]) * r := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hr
    push_cast at this
    exact this
  have hx' : x = (r : ℚ_[p]) ^ 2 * a := by
    rw [sq, ← hr', hα]
    field_simp
    ring
  refine ⟨r, fun h0 => ?_, hx'⟩
  rw [h0] at hx'
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hx'
  rw [hx', zero_sub, norm_neg] at hx
  have : ‖(4 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) 4
  nlinarith [norm_pos_iff.mpr ha]

/-- **Kitaoka 1993, Theorem 3.3.1 (4)** (p. 54), $F = \mathbb Q_p$: the Hilbert symbol is continuous on
$\mathbb Q_p^\times \times \mathbb Q_p^\times$; equivalently (its values $\pm 1$ being discrete) it is locally constant:
for $a, b \ne 0$, $(a', b')_p = (a, b)_p$ for all $(a', b')$ near $(a, b)$. Unconditional. -/
@[kb "kitaoka1993" "§3.3, Thm. 3.3.1 (4), p. 54 (over ℚ_p)"]
theorem theorem331_4_padic {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ x in 𝓝 (a, b), hilbertSymbol ℚ_[p] x.1 x.2 = hilbertSymbol ℚ_[p] a b := by
  rw [nhds_prod_eq]
  filter_upwards [(eventually_sq_mul p ha).prod_mk (eventually_sq_mul p hb)]
  rintro ⟨x, y⟩ ⟨⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩⟩
  rw [PadicClass.hs_sq_left _ _ _ hc, PadicClass.hs_sq_right _ _ _ hd]

end Padic

section Real

/-- The real Hilbert symbol of nonzero arguments: $-1$ exactly when both are negative. -/
theorem hs_real_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  split_ifs with h
  · exact (hilbertSymbol_real x y hx hy).mpr h
  · rcases PadicClass.hs_pm (K := ℝ) x y with h1 | h1
    · exact h1
    · exact absurd ((hilbertSymbol_real x y hx hy).mp h1) h

/-- **Kitaoka 1993, Theorem 3.3.1 (4)** (p. 54), $F = \mathbb R$: the Hilbert symbol is locally constant on
$\mathbb R^\times \times \mathbb R^\times$. Unconditional. -/
@[kb "kitaoka1993" "§3.3, Thm. 3.3.1 (4), p. 54 (over ℝ)"]
theorem theorem331_4_real {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ x in 𝓝 (a, b), hilbertSymbol ℝ x.1 x.2 = hilbertSymbol ℝ a b := by
  have hsa : ∀ᶠ x in 𝓝 a, x ≠ 0 ∧ (x < 0 ↔ a < 0) := by
    rcases lt_or_gt_of_ne ha with h | h
    · filter_upwards [eventually_lt_nhds h] with x hx
      exact ⟨hx.ne, by simp [hx, h]⟩
    · filter_upwards [eventually_gt_nhds h] with x hx
      exact ⟨hx.ne', by simp [hx.not_gt, h.not_gt]⟩
  have hsb : ∀ᶠ y in 𝓝 b, y ≠ 0 ∧ (y < 0 ↔ b < 0) := by
    rcases lt_or_gt_of_ne hb with h | h
    · filter_upwards [eventually_lt_nhds h] with y hy
      exact ⟨hy.ne, by simp [hy, h]⟩
    · filter_upwards [eventually_gt_nhds h] with y hy
      exact ⟨hy.ne', by simp [hy.not_gt, h.not_gt]⟩
  rw [nhds_prod_eq]
  filter_upwards [hsa.prod_mk hsb]
  rintro ⟨x, y⟩ ⟨⟨hx0, hx⟩, ⟨hy0, hy⟩⟩
  rw [hs_real_eq hx0 hy0, hs_real_eq ha hb]
  simp only [hx, hy]

end Real

end QuadFormsKB.Kitaoka.Theorem331
