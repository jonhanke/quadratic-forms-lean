import QuadFormsKB.Literature.OMeara.Sec43C

/-!
# O'Meara §43E: the exceptional space (43:12 and 43:12a, the exceptional case)

**Setting** (as in `Sec43E.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic space,
$O(V)$ = `orth Q`. O'Meara's exceptional space (`IsExceptional43 Q`) is a regular isotropic binary space (a
hyperbolic plane, 42:9) over a field of three elements.

**Proves** (O'Meara 1973 printing, Chapter IV, §43E, p. 110):
* `orth_comm_of_exceptional` (**43:12**, exceptional case: $Z_n = O_n$; **43:12a**, exceptional case: $O_n$ is
  commutative): in the exceptional space every two isometries commute.

**Proof notes.** With a hyperbolic pair $x, y$, every anisotropic vector is $\pm(x + y)$ or $\pm(x - y)$ (the only
non-zero scalars are $\pm 1$), so every symmetry is $A = \tau_{x+y}$ or $B = \tau_{x-y}$; $A$ and $B$ commute (both
products are $-1_V$), and every isometry is a product of symmetries (43:3). O'Meara instead counts: $O_n$ has order 4.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Exc

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

theorem eq_one_or_neg_of_card_three (h3 : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  classical
  by_contra h
  push Not at h
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have h1 : (1 : F) ≠ -1 := fun h => iv_two_ne (by linear_combination h)
  have hcard : ({0, 1, -1, a} : Finset F).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
    · simp [h1, (Ne.symm h.1)]
    · simp [(neg_ne_zero.2 one_ne_zero).symm, ha.symm]
  have := Finset.card_le_univ ({0, 1, -1, a} : Finset F)
  rw [hcard, Fintype.card_eq_nat_card, h3] at this
  omega

/-- $\tau_{-u} = \tau_u$. -/
theorem iv_symmetry_neg {u : V} (hu : Q u ≠ 0) (hu' : Q (-u) ≠ 0) : symmetry Q (-u) hu' = symmetry Q u hu := by
  ext v
  rw [symmetry_apply, symmetry_apply, QuadraticMap.map_neg, show bil Q v (-u) = -bil Q v u by simp [bil]]
  rw [smul_neg, ← neg_smul]; congr 2; ring

theorem iv_symmetry_smul_pm {u : V} (hu : Q u ≠ 0) {s : F} (hs : s = 1 ∨ s = -1) (h' : Q (s • u) ≠ 0) :
    symmetry Q (s • u) h' = symmetry Q u hu := by
  rcases hs with rfl | rfl
  · simp only [one_smul]
  · simp only [neg_smul, one_smul] at h' ⊢
    exact iv_symmetry_neg Q hu h'

/-- **O'Meara 43:12 and 43:12a**, the exceptional case (p. 110). If $V$ is a hyperbolic plane over a field of three
elements, then $O(V)$ is commutative; equivalently its center $Z_n$ is all of $O_n$. -/
@[kb "omeara1963" "§43E, 43:12a, p. 110 (exceptional case: O_n commutative)"]
theorem orth_comm_of_exceptional (hQ : (QuadraticMap.associated Q).Nondegenerate) (hexc : IsExceptional43 Q) :
    ∀ σ ∈ orth Q, ∀ ρ ∈ orth Q, σ * ρ = ρ * σ := by
  obtain ⟨h2, ⟨x, hx0, hx⟩, h3⟩ := hexc
  obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
  have hli := linearIndependent_pair_of_hyp Q hx hy hxy
  set e := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have he : ⇑e = ![x, y] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hdec : ∀ v : V, ∃ s t : F, v = s • x + t • y := fun v => by
    refine ⟨e.repr v 0, e.repr v 1, ?_⟩
    conv_lhs => rw [← e.sum_repr v]
    simp [Fin.sum_univ_two, he]
  have hQu : Q (x + y) ≠ 0 := by
    have := Q_add_smul_of_pair Q hx hy hxy 1; rw [one_smul] at this; rw [this]; simpa using iv_two_ne
  have hQw : Q (x - y) ≠ 0 := by
    have := Q_add_smul_of_pair Q hx hy hxy (-1)
    rw [neg_one_smul, ← sub_eq_add_neg] at this; rw [this]
    exact mul_ne_zero iv_two_ne (neg_ne_zero.2 one_ne_zero)
  set A := symmetry Q (x + y) hQu
  set B := symmetry Q (x - y) hQw
  -- every symmetry is A or B
  have hsym : ∀ (v : V) (hv : Q v ≠ 0), symmetry Q v hv = A ∨ symmetry Q v hv = B := by
    intro v hv
    obtain ⟨s, t, rfl⟩ := hdec v
    have hQv : Q (s • x + t • y) = 2 * s * t := by
      rw [Q_add, Q_smul, Q_smul, hx, hy, bil_smul_left, bil_smul_right, hxy]; ring
    rw [hQv] at hv
    have hs0 : s ≠ 0 := fun h => hv (by simp [h])
    have ht0 : t ≠ 0 := fun h => hv (by simp [h])
    have hs := eq_one_or_neg_of_card_three h3 hs0
    have ht := eq_one_or_neg_of_card_three h3 ht0
    by_cases hst : t = s
    · left
      have hv' : s • x + t • y = s • (x + y) := by rw [hst, smul_add]
      have h' : Q (s • (x + y)) ≠ 0 := by rw [← hv', hQv]; exact hv
      rw [show symmetry Q (s • x + t • y) _ = symmetry Q (s • (x + y)) h' by congr 1]
      exact iv_symmetry_smul_pm Q hQu hs h'
    · right
      have hts : t = -s := by
        rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
      have hv' : s • x + t • y = s • (x - y) := by rw [hts, smul_sub, neg_smul, sub_eq_add_neg]
      have h' : Q (s • (x - y)) ≠ 0 := by rw [← hv', hQv]; exact hv
      rw [show symmetry Q (s • x + t • y) _ = symmetry Q (s • (x - y)) h' by congr 1]
      exact iv_symmetry_smul_pm Q hQw hs h'
  -- A and B commute
  have hAx : A x = -y := by
    rw [symmetry_apply, bil_add_right, bil_self, hx, hxy, Q_add, hx, hy, hxy]
    rw [show 2 * (0 + 1) / (0 + 2 * 1 + 0) = (1 : F) by field_simp; ring, one_smul]; abel
  have hAy : A y = -x := by
    rw [symmetry_apply, bil_add_right, bil_self, hy, bil_comm Q y x, hxy, Q_add, hx, hy, hxy]
    rw [show 2 * (1 + 0) / (0 + 2 * 1 + 0) = (1 : F) by field_simp; ring, one_smul]; abel
  have hBx : B x = y := by
    rw [symmetry_apply, bil_sub_right, bil_self, hx, hxy, sub_eq_add_neg x y, Q_add, hx,
      QuadraticMap.map_neg, hy, show bil Q x (-y) = -bil Q x y by simp [bil], hxy]
    rw [show 2 * (0 - 1) / (0 + 2 * -1 + 0) = (1 : F) by field_simp; ring, one_smul]; abel
  have hBy : B y = x := by
    rw [symmetry_apply, bil_sub_right, bil_self, hy, bil_comm Q y x, hxy, sub_eq_add_neg x y, Q_add, hx,
      QuadraticMap.map_neg, hy, show bil Q x (-y) = -bil Q x y by simp [bil], hxy]
    rw [show 2 * (1 - 0) / (0 + 2 * -1 + 0) = (-1 : F) by field_simp; ring, neg_one_smul]; abel
  have hAB : A * B = B * A := by
    ext v
    obtain ⟨s, t, rfl⟩ := hdec v
    simp only [LinearEquiv.mul_apply, map_add, map_smul, hAx, hAy, hBx, hBy, map_neg]
  -- every element of O(V) commutes with A and B
  have hfac : ∀ a : {u : V // Q u ≠ 0}, ∀ g : V ≃ₗ[F] V, g * A = A * g → g * B = B * g →
      g * symmetry Q a.1 a.2 = symmetry Q a.1 a.2 * g := fun a g hgA hgB => by
    rcases hsym a.1 a.2 with h | h <;> rw [h]
    · exact hgA
    · exact hgB
  have hP : ∀ l : List {u : V // Q u ≠ 0}, cd_prod Q l * A = A * cd_prod Q l ∧ cd_prod Q l * B = B * cd_prod Q l := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [cd_prod_cons]
      have hA := (hfac a A rfl hAB).symm
      have hB := (hfac a B hAB.symm rfl).symm
      constructor
      · rw [mul_assoc, ih.1, ← mul_assoc, hA, mul_assoc]
      · rw [mul_assoc, ih.2, ← mul_assoc, hB, mul_assoc]
  intro σ hσ ρ hρ
  obtain ⟨l, -, rfl⟩ := cd_list Q hQ hσ
  obtain ⟨m, -, rfl⟩ := cd_list Q hQ hρ
  clear hρ
  induction m with
  | nil => simp
  | cons a m ih =>
    rw [cd_prod_cons, ← mul_assoc, hfac a _ (hP l).1 (hP l).2, mul_assoc, ih, mul_assoc]

attribute [kb "omeara1963" "§43E, 43:12, p. 110 (exceptional case: Z_n = O_n)"] orth_comm_of_exceptional

end Sec43Exc

end QuadFormsKB.OMeara
