/-
# Cassels, Chapter 2, §4: proper autometries and products of two symmetries

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, §4, *Isometries and autometries*, pp. 18–21.

**Setting.** $k$ = `F` is a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`), $(U, \phi)$ is a
finite-dimensional quadratic space, given by a Mathlib quadratic form `Q : QuadraticForm F V` with $Q(u) = \phi(u)$;
*regular* means that the bilinear form $\phi(u, v)$ (`QuadraticMap.associated Q`) is nondegenerate. The library's
O'Meara groups are used: $O(U)$ is `OMeara.orth Q` and $O^{+}(U)$ is `OMeara.orthPlus Q` (determinant $1$); the
symmetry $\tau_v u = u - \frac{2\phi(u,v)}{\phi(v)}v$ of (4.3) is `OMeara.symmetry Q v hv`.

**Proves.**
* §4, p. 19 (2.r9): $O^{+}(U)$ has index exactly $2$ in $O(U)$ when $U$ is regular and $U \ne 0$
  (`index_orthPlus_eq_two`), so the improper autometries form a coset.
* Lemma 4.2, Corollary 2 (p. 20), `exists_two_symmetries`: if $U$ is regular of dimension $n > 1$ and
  $\phi(u) = \phi(v) \ne 0$, then $\tau_a\tau_b u = v$ for some anisotropic $a, b$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Units

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

open QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

private theorem Q_sub' (x y : V) : Q (x - y) = Q x - 2 * bil Q x y + Q y := by
  have h : bil Q x (-y) = - bil Q x y := by
    rw [← neg_one_smul F y, bil_smul_right]; ring
  rw [sub_eq_add_neg, Q_add, h, QuadraticMap.map_neg]; ring

private theorem exists_Q_ne_zero' (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V] :
    ∃ u : V, Q u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := exists_ne (0 : V)
  refine hm (hV.1 m fun n => ?_)
  change bil Q m n = 0
  have h := Q_add Q m n
  rw [hcon, hcon, hcon] at h
  have : (2 : F) * bil Q m n = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

private theorem symmetry_self' {u : V} (hu : Q u ≠ 0) : symmetry Q u hu u = -u := by
  rw [symmetry_apply, bil_self]
  have : 2 * Q u / Q u = 2 := by field_simp
  rw [this, two_smul]; abel

/-- **Cassels, Ch. 2, §4, p. 19 (proper and improper autometries).** For a regular quadratic space $U \ne 0$ over
a field of characteristic $\ne 2$, the proper orthogonal group $O^{+}(U)$ (autometries of determinant $+1$) has
index exactly $2$ in $O(U)$: improper autometries exist (a symmetry, determinant $-1$, (4.2)). -/
@[kb "cassels1978" "Ch. 2, §4, p. 19 (O⁺(U) has index 2 in O(U))"]
theorem index_orthPlus_eq_two (hQ : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V] :
    ((orthPlus Q).subgroupOf (orth Q)).index = 2 := by
  obtain ⟨u, hu⟩ := exists_Q_ne_zero' Q hQ
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    have h2 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h2
    have : (2 : F) = 0 := by linear_combination -h2
    exact two_ne_zero this
  have hτ : symmetry Q u hu ∈ orth Q := symmetry_mem_orth Q hu
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨_, hτ⟩, fun b => ?_⟩
  have hb := det_orth_eq Q hQ b.2
  have hmem : ∀ c : orth Q, c ∈ (orthPlus Q).subgroupOf (orth Q) ↔
      LinearEquiv.det (c : V ≃ₗ[F] V) = 1 := fun c => ⟨fun H => H.2, fun H => ⟨c.2, H⟩⟩
  rw [hmem, hmem]
  have hd : LinearEquiv.det ((b * ⟨_, hτ⟩ : orth Q) : V ≃ₗ[F] V) =
      LinearEquiv.det (b : V ≃ₗ[F] V) * -1 := by
    rw [← det_symmetry Q hu, ← map_mul]; rfl
  rw [hd]
  rcases hb with h | h
  · rw [h]; simp [hne]
  · rw [h]; simp [hne]

/-- **Cassels, Ch. 2, Lemma 4.2, Corollary 2 (p. 20).** Let $(U, \phi)$ be a regular quadratic space of dimension
$n > 1$ over a field of characteristic $\ne 2$, and let $u, v \in U$ with $\phi(u) = \phi(v) \ne 0$. Then some
product of exactly two symmetries maps $u$ to $v$: there are $a, b \in U$ with $\phi(a), \phi(b) \ne 0$ and
$\tau_a \tau_b u = v$. -/
@[kb "cassels1978" "Ch. 2, Lemma 4.2, Cor. 2, p. 20"]
theorem exists_two_symmetries (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 < finrank F V)
    {u v : V} (huv : Q u = Q v) (hu : Q u ≠ 0) :
    ∃ (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0), symmetry Q a ha (symmetry Q b hb u) = v := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  by_cases hd : Q (u - v) = 0
  · have hQ' : Q (u + v) ≠ 0 := by
      have e1 := Q_sub' Q u v
      have e2 := Q_add Q u v
      intro hz
      apply hu
      have : (4 : F) * Q u = 0 := by linear_combination hz + hd - e2 - e1 + 2 * huv
      have h4 : (4 : F) ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
      exact (mul_eq_zero.mp this).resolve_left h4
    have hv : Q v ≠ 0 := huv ▸ hu
    refine ⟨v, u + v, hv, hQ', ?_⟩
    have hbil : bil Q u v = Q u := by
      have e1 := Q_sub' Q u v
      have : (2 : F) * (bil Q u v - Q u) = 0 := by linear_combination -hd + e1 - huv
      have := (mul_eq_zero.mp this).resolve_left h2
      linear_combination this
    have hs : symmetry Q (u + v) hQ' u = -v := by
      rw [symmetry_apply, bil_add_right, bil_self, hbil, Q_add, ← huv, hbil]
      have h4 : (4 : F) * Q u ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) hu
      have hden : Q u + 2 * Q u + Q u ≠ 0 := by
        have e : Q u + 2 * Q u + Q u = 4 * Q u := by ring
        rw [e]; exact h4
      have : (2 * (Q u + Q u) / (Q u + 2 * Q u + Q u)) = 1 := by
        rw [div_eq_one_iff_eq hden]; ring
      rw [this, one_smul]; abel
    rw [hs]
    have := symmetry_self' Q hv
    have h' := symmetry_apply Q hv (-v)
    rw [bil_neg_left, bil_self] at h'
    rw [h']
    have : (2 * -Q v / Q v) = -2 := by field_simp
    rw [this]; module
  · have hneg : ∀ x y : V, Q (x - y) = Q x - 2 * bil Q x y + Q y := Q_sub' Q
    -- an anisotropic vector orthogonal to `u`
    obtain ⟨b, hb, hbu⟩ : ∃ b : V, Q b ≠ 0 ∧ bil Q b u = 0 := by
      obtain ⟨b', hb'⟩ : ∃ b' : V, ∀ t : F, t • u ≠ b' := by
        by_contra hcon
        push Not at hcon
        have : finrank F V ≤ 1 := finrank_le_one_iff.mpr ⟨u, fun w => hcon w⟩
        omega
      set w : V := b' - (bil Q b' u / Q u) • u with hw
      have hwu : bil Q w u = 0 := by
        rw [hw, bil_sub_left, bil_smul_left, bil_self]; field_simp; ring
      have hw0 : w ≠ 0 := by
        intro h0
        apply hb' (bil Q b' u / Q u)
        rw [hw, sub_eq_zero] at h0
        exact h0.symm
      obtain ⟨z, hz⟩ : ∃ z, bil Q w z ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hw0 (hQ.1 w hcon)
      set z' : V := z - (bil Q z u / Q u) • u with hz'
      have hz'u : bil Q z' u = 0 := by
        rw [hz', bil_sub_left, bil_smul_left, bil_self]; field_simp; ring
      have hwz : bil Q w z' = bil Q w z := by
        rw [hz', bil_sub_right, bil_smul_right, hwu]; ring
      by_cases h1 : Q w = 0
      · by_cases h3 : Q z' = 0
        · refine ⟨w + z', ?_, by rw [bil_add_left, hwu, hz'u, add_zero]⟩
          rw [Q_add, h1, h3, hwz]
          rw [zero_add, add_zero]; exact mul_ne_zero h2 hz
        · exact ⟨z', h3, hz'u⟩
      · exact ⟨w, h1, hwu⟩
    have hbu' : symmetry Q b hb u = u := by
      rw [symmetry_apply, bil_comm, hbu]; simp
    have hQa : Q (u - v) ≠ 0 := hd
    refine ⟨u - v, b, hQa, hb, ?_⟩
    rw [hbu', symmetry_apply, bil_sub_right, bil_self, hneg, ← huv]
    have : 2 * (Q u - bil Q u v) / (Q u - 2 * bil Q u v + Q u) = 1 := by
      have : Q u - 2 * bil Q u v + Q u ≠ 0 := by intro h; apply hd; rw [hneg, ← huv]; exact h
      field_simp; ring
    rw [this, one_smul]; abel

end QuadFormsKB.Cassels
