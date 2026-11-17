import QuadFormsKB.Historical.Gauss.GenusGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

/-!
# The presentation of the class group of a regular determinant (Disquisitiones Arithmeticae, Art. 307 VII)

(Art. 307 VII). This file proves the named proposition `Art307RegularPresentation`
(stated in `GenusGroup.lean`), which closes a recorded loose end. Gauss's worked tables for the determinants $-161$
and $-546$ remain unformalized.

The proof goes through a general lemma on finite commutative groups
(`exists_presentation_of_cyclic_sq`): if the subgroup $S = G^2$ of squares is cyclic and $G / S$ has order $2^{\mu}$,
then there are an element $E$ whose powers contain $S$ and elements $A_0, \dots, A_{\mu-2}$ of order dividing $2$ such
that every element of $G$ is $E^k \prod_{i \in I} A_i$. Gauss's indices $A', A'', \dots$ become $A_0, A_1, \dots$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition FormClass

/-- Covering lemma for an elementary abelian $2$-subgroup $T$ of a finite commutative group: if $B \le T$ and
$\#T \le 2^m \#B$, there are $m$ elements $A_i \in T$ such that every element of $T$ is $u \prod_{i \in I} A_i$ with
$u \in B$. -/
private theorem exp_two_cover {G : Type*} [CommGroup G] [Finite G] (T : Subgroup G) (hT : ∀ t ∈ T, t ^ 2 = 1) :
    ∀ (m : ℕ) (B : Subgroup G), B ≤ T → Nat.card T ≤ 2 ^ m * Nat.card B →
      ∃ A : Fin m → G, (∀ i, A i ∈ T) ∧
        ∀ C ∈ T, ∃ u ∈ B, ∃ I : Finset (Fin m), C = u * ∏ i ∈ I, A i := by
  intro m
  induction m with
  | zero =>
    intro B hB hcard
    have hBT : B = T := Subgroup.eq_of_le_of_card_ge hB (by simpa using hcard)
    subst hBT
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun C hC => ⟨C, hC, ∅, by simp⟩⟩
  | succ m ih =>
    intro B hB hcard
    by_cases hle : T ≤ B
    · exact ⟨fun _ => 1, fun _ => T.one_mem, fun C hC => ⟨C, hle hC, ∅, by simp⟩⟩
    obtain ⟨t, htT, htB⟩ := SetLike.not_le_iff_exists.mp hle
    set B' : Subgroup G := B ⊔ Subgroup.zpowers t with hB'
    have hB'T : B' ≤ T := sup_le hB ((Subgroup.zpowers_le).mpr htT)
    have hlt : B < B' := by
      refine lt_of_le_of_ne le_sup_left fun h => htB ?_
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hc1 := Subgroup.card_lt_of_lt hlt
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hlt.le
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hc2 : 2 ≤ c := by
      by_contra h
      have : c ≤ 1 := by omega
      have : Nat.card B' ≤ Nat.card B := by rw [hc]; nlinarith
      omega
    have hcard' : Nat.card T ≤ 2 ^ m * Nat.card B' := by
      calc Nat.card T ≤ 2 ^ (m + 1) * Nat.card B := hcard
        _ = 2 ^ m * (2 * Nat.card B) := by ring
        _ ≤ 2 ^ m * Nat.card B' := by
          apply Nat.mul_le_mul_left; rw [hc]; nlinarith
    obtain ⟨A', hA'T, hA'⟩ := ih B' hB'T hcard'
    refine ⟨Fin.cons t A', fun i => ?_, fun C hC => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using htT
      · simpa using hA'T j
    obtain ⟨u', hu', I', rfl⟩ := hA' C hC
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hn : t ^ n = 1 ∨ t ^ n = t := by
      rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
      · left; rw [zpow_mul]; simp [hT t htT]
      · right; rw [zpow_add, zpow_mul]; simp [hT t htT]
    have hmap : ∏ i ∈ I'.map (Fin.succEmb m), (Fin.cons t A' : Fin (m + 1) → G) i = ∏ i ∈ I', A' i := by
      rw [Finset.prod_map]; simp
    rcases hn with h | h
    · refine ⟨y, hy, I'.map (Fin.succEmb m), ?_⟩
      rw [hmap, h]; simp
    · refine ⟨y, hy, insert 0 (I'.map (Fin.succEmb m)), ?_⟩
      have h0 : (0 : Fin (m + 1)) ∉ I'.map (Fin.succEmb m) := by simp
      rw [Finset.prod_insert h0, hmap, h]
      simp [mul_assoc]

/-- **Structure of a finite commutative group whose squares form a cyclic group.** Let $G$ be a finite commutative
group whose subgroup $S = G^2$ of squares is cyclic, with $[G : S] = 2^{\mu}$. Then there are an element $E$ with
$S \subseteq \langle E \rangle$ and elements $A_0, \dots, A_{\mu - 2}$ with $A_i^2 = 1$ such that every $C \in G$ is
$E^k \prod_{i \in I} A_i$ for some natural number $k$ and finite set $I$ of indices. (Abstractly,
$G \cong \mathbb Z/n \times (\mathbb Z/2)^{\mu - 1}$ with $n$ even when $\mu \ge 1$, and $G = \langle E \rangle$
cyclic when $\mu = 0$.) -/
theorem exists_presentation_of_cyclic_sq {G : Type*} [CommGroup G] [Finite G]
    (hS : IsCyclic (powMonoidHom 2 : G →* G).range) (μ : ℕ)
    (hμ : Nat.card (G ⧸ (powMonoidHom 2 : G →* G).range) = 2 ^ μ) :
    ∃ (E : G) (A : Fin (μ - 1) → G),
      (∀ C ∈ (powMonoidHom 2 : G →* G).range, C ∈ Subgroup.zpowers E) ∧ (∀ i, A i ^ 2 = 1) ∧
      ∀ C : G, ∃ (k : ℕ) (I : Finset (Fin (μ - 1))), C = E ^ k * ∏ i ∈ I, A i := by
  set S := (powMonoidHom 2 : G →* G).range with hSdef
  set T : Subgroup G := (powMonoidHom 2 : G →* G).ker with hTdef
  have hTmem : ∀ t, t ∈ T ↔ t ^ 2 = 1 := fun t => by simp [hTdef]
  have hT : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => (hTmem t).mp ht
  have hcardT : Nat.card T = 2 ^ μ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    have h2 := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : G →* G)
    rw [hμ] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    have : Nat.card T * Nat.card S = 2 ^ μ * Nat.card S := by rw [h2, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨g, hg⟩ := hS.exists_generator
  obtain ⟨x, hx⟩ : ∃ x : G, x ^ 2 = g.1 := by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp g.2
    exact ⟨x, hx⟩
  have hE : ∃ E : G, E ^ 2 = g.1 ∧ (1 ≤ μ → ∃ t0 ∈ T, t0 ≠ 1 ∧ t0 ∈ Subgroup.zpowers E) := by
    by_cases heven : Even (orderOf x)
    · refine ⟨x, hx, fun h1 => ?_⟩
      obtain ⟨r, hr⟩ := heven
      have hpos : 0 < orderOf x := orderOf_pos x
      refine ⟨x ^ r, ?_, ?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _⟩
      · rw [hTmem, ← pow_mul, show r * 2 = orderOf x by omega]; exact pow_orderOf_eq_one x
      · exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    · obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
      by_cases hμ0 : μ = 0
      · exact ⟨x, hx, fun h => by omega⟩
      obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        have h1 : Nat.card T = 1 := Subgroup.card_eq_one.mpr ((Subgroup.eq_bot_iff_forall T).mpr hcon)
        have : 2 ≤ 2 ^ μ := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      refine ⟨x * t, by rw [mul_pow, hT t htT, mul_one, hx], fun _ => ⟨t, htT, ht1, ?_⟩⟩
      have : (x * t) ^ (orderOf x) = t := by
        rw [mul_pow, pow_orderOf_eq_one, one_mul, hr, pow_succ, pow_mul, hT t htT, one_pow, one_mul]
      have hmem := Subgroup.pow_mem _ (Subgroup.mem_zpowers (x * t)) (orderOf x)
      rwa [this] at hmem
  obtain ⟨E, hEg, hEt⟩ := hE
  set B : Subgroup G := Subgroup.zpowers E ⊓ T with hBdef
  have hcard : Nat.card T ≤ 2 ^ (μ - 1) * Nat.card B := by
    by_cases hμ0 : μ = 0
    · subst hμ0
      have : 0 < Nat.card B := Nat.card_pos
      rw [hcardT]; simp only [pow_zero, Nat.zero_sub, one_mul]; omega
    · obtain ⟨t0, ht0T, ht01, ht0E⟩ := hEt (by omega)
      have hpos : 0 < Nat.card B := Nat.card_pos
      have hne : Nat.card B ≠ 1 := by
        intro h1
        have := Subgroup.card_eq_one.mp h1
        have hm : t0 ∈ B := ⟨ht0E, ht0T⟩
        rw [this] at hm
        exact ht01 (by simpa using hm)
      have h2 : 2 ≤ Nat.card B := by omega
      rw [hcardT]
      obtain ⟨j, rfl⟩ : ∃ j, μ = j + 1 := ⟨μ - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) j]
  obtain ⟨A, hAT, hA⟩ := exp_two_cover T hT (μ - 1) B inf_le_right hcard
  have hsq : ∀ C ∈ S, ∃ n : ℤ, C = E ^ ((2 : ℤ) * n) := by
    intro C hC
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨C, hC⟩)
    have h' : g.1 ^ n = C := congrArg Subtype.val hn
    exact ⟨n, by rw [zpow_mul]; simp [hEg, h']⟩
  refine ⟨E, A, ?_, fun i => hT _ (hAT i), fun C => ?_⟩
  · intro C hC
    obtain ⟨n, hn⟩ := hsq C hC
    exact Subgroup.mem_zpowers_iff.mpr ⟨2 * n, hn.symm⟩
  · have hC2 : C ^ 2 ∈ S := ⟨C, by simp⟩
    obtain ⟨n, hn⟩ := hsq _ hC2
    have hsqE : (E ^ (-n)) ^ 2 = (E ^ ((2 : ℤ) * n))⁻¹ := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]; congr 1; push_cast; ring
    have htT : C * E ^ (-n) ∈ T := by
      rw [hTmem, mul_pow, hsqE, hn]; simp
    obtain ⟨u, hu, I, hI⟩ := hA _ htT
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu.1
    have hCeq : C = E ^ (n + m) * ∏ i ∈ I, A i := by
      have h1 : C * E ^ (-n) = E ^ m * ∏ i ∈ I, A i := by rw [hI, ← hm]
      calc C = (C * E ^ (-n)) * E ^ n := by simp [zpow_neg]
        _ = E ^ (n + m) * ∏ i ∈ I, A i := by rw [h1, zpow_add]; ac_rfl
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
      ((mem_powers_iff_mem_zpowers).mpr (Subgroup.mem_zpowers_iff.mpr ⟨n + m, rfl⟩ : E ^ (n + m) ∈ Subgroup.zpowers E))
    exact ⟨k, I, by rw [hk]; exact hCeq⟩

/-- **Gauss, *Disq. Arith.* Art. 307 VII: the class group of a regular determinant.** Let
$D$ be a nonzero discriminant whose principal genus (the subgroup $\mathcal G^2$ of squares of the class group) is
cyclic ("regular" in Gauss's sense), and suppose there are $2^{\mu}$ genera. Then there are a class $E$ whose powers
contain the whole principal genus and ambiguous classes $A_0, \dots, A_{\mu - 2}$ (that is, $A_i^2 = 1$, equivalently
$A_i$ is its own opposite) such that every class is $E^k \prod_{i \in I} A_i$ for some natural number $k$ and some set
$I$ of indices. Gauss's $A', A'', \dots$ are $A_0, A_1, \dots$ here (0-based). Proved, unconditionally, from the
general group-theoretic lemma `exists_presentation_of_cyclic_sq` (the class group is finite and commutative). This
closes a recorded loose end; Gauss's worked tables for $-161$ and $-546$ remain unformalized. -/
@[kb "gauss1801" "Art. 307 VII"]
theorem art307_regular_presentation (D : ℤ) [NonzeroDisc D] : Art307RegularPresentation D :=
  fun hS μ hμ => exists_presentation_of_cyclic_sq hS μ hμ

end QuadFormsKB.Historical.Gauss
