/-
# Chenevier–Lannes: neighbour graphs and Hecke operators in dimensions 8 and 16

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.2, p. 3 (Theorem A); §3.1, p. 52 (the graphs $K_n(p)$,
Theorem 3.1.12); §3.2, pp. 55–56 (Propositions 3.2.2–3.2.4); §3.3, pp. 57–59. Printed page numbers.

**Layer.** Earlier files (`Neighbors.lean`, `TheoremsAB.lean`): $N_p(x, y)$ = `nbNum`, `Siegel.Kneser.nbCount`, $T_p$ =
`heckeT`; $X_8 = \{E_8\}$ (`mordellRankEight`), $X_{16} = \{E_8 \oplus E_8, E_{16}\}$ (`wittRankSixteen`), the
orders $|O(E_8 \oplus E_8)| = 2|O(E_8)|^2$, $|O(E_{16})| = 2^{15}\,16!$ (`Witt.lean`).

**Proves** (all unconditional; $p$ an odd prime where stated):
- `nbrStep_of_nbCount_pos`: a positive neighbour count gives an edge of the neighbour graph;
- `neighborGraphConnected_eight` (Theorem 3.1.12 for $n = 8$, $p$ odd): $K_8(p)$ is connected, without the spinor-genus
  input (`kneser_connected_of_input`);
- `nbCount_e8_e8`, `heckeT_eight` ($n = 8$, $p$ odd): $N_p(E_8, E_8) = c_8(p)$, so $T_p = c_8(p)$ on $\mathbb{Z}[X_8]$;
- `nbCount_sixteen_add_uncond` (Proposition 3.2.2 for $n = 16$, $p$ odd), now without Witt's input;
- `nbCount_gamma16_twoE8_mul` (Scholium 3.1.7 for $n = 16$, $p$ odd): $405\,N_p(E_{16}, E_8 \oplus E_8) =
  286\,N_p(E_8 \oplus E_8, E_{16})$;
- `theoremA_odd_iff` ($p$ odd): the four equalities of Theorem A at $p$ are equivalent to the single equality
  $N_p(E_8 \oplus E_8, E_{16}) = 405\,c$, $c = (1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))/691$;
- `neighborGraphConnected_sixteen_of_pos` ($p$ odd): $K_{16}(p)$ is connected as soon as
  $N_p(E_8 \oplus E_8, E_{16}) \ne 0$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Witt
import QuadFormsKB.Literature.ChenevierLannes.TheoremsAB

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### Edges from neighbour counts -/

/-- **A positive neighbour count gives a neighbour step**: if some $p$-neighbour of $(\mathbb{Z}^n, Q)$ has class
$[Q']$ ($N(Q, [Q']) > 0$), then `NbrStep p Q Q'`. -/
theorem nbrStep_of_nbCount_pos {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q Q' : QuadForm ℤ n}
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (h : 0 < nbCount Q p (classOf Q')) : NbrStep p Q Q' := by
  classical
  unfold nbCount at h
  obtain ⟨L, hL⟩ := Finset.card_pos.mp h
  obtain ⟨hLn, hLc⟩ := Finset.mem_filter.mp hL
  obtain ⟨g, hgL, Q'', hcl, hQ''⟩ := ((nbClass_spec hp2 hdet hLn).2 (classOf Q')).mpr hLc
  refine ⟨Q'', ⟨(g : Matrix (Fin n) (Fin n) ℚ), ?_, ?_, hQ''⟩, classOf_eq_classOf_iff.mp hcl⟩
  · exact (g.isUnit.map Matrix.detMonoidHom).ne_zero
  · rw [hgL]; exact (mem_neighbors_iff hdet).mp hLn

/-- Neighbour steps between classes: `NbrStep p A B` gives `NbrStep p R S` for $R \simeq A$, $B \simeq S$. -/
theorem nbrStep_transport {p : ℕ} {R A B S : QuadForm ℤ n} (hRA : IntEquiv R A) (h : NbrStep p A B)
    (hBS : IntEquiv B S) : NbrStep p R S := by
  obtain ⟨Q', hn, he⟩ := h
  exact ⟨Q', hn.of_intEquiv hRA, IsometricGL.trans he hBS⟩

/-! ### Dimension 8 -/

/-- $c_n(p) > 0$. -/
theorem cn_pos (n p : ℕ) : 0 < cn n p := by
  unfold cn
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n / 2 - 1 = 0 := by omega
    rw [this, pow_zero]
    omega
  · have : 0 < ∑ m ∈ Finset.range (n - 1), p ^ m :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
    omega

/-- **$N_p(L, E_8) = c_8(p)$ for every even unimodular $L$ of dimension $8$** ($p$ odd): every $p$-neighbour of $L$ is
isomorphic to $E_8$ (`mordellRankEight`) and there are $c_8(p)$ of them (`card_neighbors_eq_cn`). Unconditional. -/
theorem nbCount_eight {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) :
    nbCount Q p (classOf e8) = cn 8 p := by
  have hT : ∀ c, c ∈ ({classOf e8} : Finset (QClass 8)) ↔ c ∈ genusClasses Q := by
    intro c
    rw [← classSet_eq_genusClasses hQ, mordellRankEight]
    simp
  have := sum_nbCount hp2 (not_dvd_det hQ p) _ hT
  rwa [Finset.sum_singleton, card_neighbors_eq_cn hQ (by norm_num) hp2] at this

/-- **$N_p(E_8, E_8) = c_8(p)$** (Chenevier–Lannes, Proposition 3.2.2 for $n = 8$, $p$ odd): $T_p$ acts on
$\mathbb{Z}[X_8] = \mathbb{Z}\,E_8$ by $c_8(p) = \sum_{m=0}^{6} p^m + p^3$. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.2.2, p. 56 (n = 8, odd p)"]
theorem nbCount_e8_e8 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : nbCount e8 p (classOf e8) = cn 8 p :=
  nbCount_eight hp2 isEvenUnimodular_e8

/-- **$T_p = c_8(p)$ on functions on $X_8$** (Chenevier–Lannes, §3.2, p. 55, for $n = 8$, $p$ odd): for every
$f : X_8 \to R$, $(T_pf)(E_8) = c_8(p)\,f(E_8)$. Unconditional. -/
@[kb "chenevierlannes2019" "§3.2, p. 55 (T_p on X_8, odd p)"]
theorem heckeT_eight {R : Type*} [AddCommMonoid R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : QClass 8 → R) :
    heckeT p f (classOf e8) = cn 8 p • f (classOf e8) := by
  have h8 : classSet 8 = {classOf e8} := mordellRankEight
  have hs : (classSet_finite 8).toFinset = {classOf e8} := by
    ext c; simp [h8]
  unfold heckeT
  rw [hs, Finset.sum_singleton]
  congr 1
  unfold nbNum
  have hx : classOf e8 ∈ classSet 8 := ⟨e8, isEvenUnimodular_e8, rfl⟩
  exact nbCount_eight hp2 (out_isEvenUnimodular hx)

/-- **Theorem 3.1.12 (Kneser) for $n = 8$** (Chenevier–Lannes, p. 52; $p$ odd): the neighbour graph $K_8(p)$ is
connected: any two even unimodular lattices of dimension $8$ are $p$-neighbours (as classes). Unconditional, without
the spinor-genus input `EvenUnimodularOneSpinorGenus` of `kneser_connected_of_input`. -/
@[kb "chenevierlannes2019" "Thm. 3.1.12, p. 52 (n = 8, odd p)"]
theorem neighborGraphConnected_eight {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : NeighborGraphConnected 8 p := by
  intro Q Q' hQ hQ'
  have e : classOf Q' = classOf e8 :=
    classOf_eq_classOf_iff.mpr (IsometricGL.symm (intEquiv_e8_of_isEvenUnimodular hQ'))
  refine Relation.ReflTransGen.single (nbrStep_of_nbCount_pos hp2 (not_dvd_det hQ p) ?_)
  rw [e, nbCount_eight hp2 hQ]
  exact cn_pos 8 p

/-! ### Dimension 16 -/

/-- **Proposition 3.2.2 for $n = 16$** (Chenevier–Lannes, p. 56; $p$ odd): the rows of $T_p$ on $\mathbb{Z}[X_{16}]$
sum to $c_{16}(p)$. Unconditional (the library's `nbCount_sixteen_add` with `wittTwoClassesSixteen`). -/
@[kb "chenevierlannes2019" "Prop. 3.2.2, p. 56 (n = 16, odd p)"]
theorem nbCount_sixteen_add_uncond {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    nbCount twoE8 p (classOf twoE8) + nbCount twoE8 p (classOf gamma16) = cn 16 p ∧
      nbCount gamma16 p (classOf twoE8) + nbCount gamma16 p (classOf gamma16) = cn 16 p :=
  nbCount_sixteen_add wittTwoClassesSixteen hp2

/-- **Scholium 3.1.7 for $n = 16$** (Chenevier–Lannes, p. 49, with $|O(E_8 \oplus E_8)|/|O(E_{16})| = 405/286$, §3.3.2,
p. 59; $p$ odd): $405\,N_p(E_{16}, E_8 \oplus E_8) = 286\,N_p(E_8 \oplus E_8, E_{16})$. Unconditional. -/
@[kb "chenevierlannes2019" "Scholium 3.1.7, p. 49; §3.3.2, p. 59 (n = 16, odd p)"]
theorem nbCount_gamma16_twoE8_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    405 * nbCount gamma16 p (classOf twoE8) = 286 * nbCount twoE8 p (classOf gamma16) := by
  have h := nbCount_mul_autCard hp2 twoE8_posDef gamma16_posDef (not_dvd_det isEvenUnimodular_twoE8 p)
    (not_dvd_det isEvenUnimodular_gamma16 p)
  rw [card_aut_twoE8, card_aut_gamma16, card_aut_e8_eq] at h
  have e1 : (2 : ℕ) ^ 15 * Nat.factorial 16 = 286 * 2397195730944000 := by decide
  have e2 : 2 * (696729600 : ℕ) ^ 2 = 405 * 2397195730944000 := by norm_num
  rw [e1, e2] at h
  have h' : (nbCount twoE8 p (classOf gamma16) * 286) * 2397195730944000 =
      (nbCount gamma16 p (classOf twoE8) * 405) * 2397195730944000 := by
    rw [mul_assoc, mul_assoc, h]
  have := Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  linarith

/-- **Theorem A at an odd prime reduces to one entry** (Chenevier–Lannes, §1.2, p. 3; $p$ odd): with
$c = (1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))/691$ (`thmAScalar p`), the four equalities of Theorem A at $p$ are
equivalent to $N_p(E_8 \oplus E_8, E_{16}) = 405\,c$. Unconditional: the diagonal entries follow from
Proposition 3.2.2 (`theoremA_iff_offDiag` with Witt's theorem) and $N_p(E_{16}, E_8 \oplus E_8)$ from Scholium 3.1.7
(`nbCount_gamma16_twoE8_mul`). -/
@[kb "chenevierlannes2019" "Thm. A, p. 3 (odd p: reduction to N_p(E_8 ⊕ E_8, E_16))"]
theorem theoremA_odd_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((nbCount twoE8 p (classOf twoE8) : ℂ) = cn 16 p - 405 * thmAScalar p ∧
      (nbCount twoE8 p (classOf gamma16) : ℂ) = 405 * thmAScalar p ∧
      (nbCount gamma16 p (classOf twoE8) : ℂ) = 286 * thmAScalar p ∧
      (nbCount gamma16 p (classOf gamma16) : ℂ) = cn 16 p - 286 * thmAScalar p) ↔
    (nbCount twoE8 p (classOf gamma16) : ℂ) = 405 * thmAScalar p := by
  rw [theoremA_iff_offDiag wittTwoClassesSixteen hp2]
  have hm : (405 : ℂ) * nbCount gamma16 p (classOf twoE8) = 286 * nbCount twoE8 p (classOf gamma16) := by
    exact_mod_cast nbCount_gamma16_twoE8_mul hp2
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [h] at hm
    have : (405 : ℂ) * (nbCount gamma16 p (classOf twoE8) - 286 * thmAScalar p) = 0 := by
      linear_combination hm
    have h405 : (405 : ℂ) ≠ 0 := by norm_num
    have := (mul_eq_zero.mp this).resolve_left h405
    linear_combination this

/-- **$K_{16}(p)$ is connected once $E_8 \oplus E_8$ and $E_{16}$ are $p$-neighbours** ($p$ odd): if
$N_p(E_8 \oplus E_8, E_{16}) \ne 0$, then any two even unimodular lattices of dimension $16$ are joined in the
neighbour graph (Chenevier–Lannes, Theorem 3.1.12 for $n = 16$; the book shows $N_2 = 18225$, $N_3 = 4147200$ in
§3.3). Unconditional apart from the displayed hypothesis. -/
@[kb "chenevierlannes2019" "Thm. 3.1.12, p. 52 (n = 16, odd p, given one edge)"]
theorem neighborGraphConnected_sixteen_of_pos {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : 0 < nbCount twoE8 p (classOf gamma16)) : NeighborGraphConnected 16 p := by
  have h' : 0 < nbCount gamma16 p (classOf twoE8) := by
    have := nbCount_gamma16_twoE8_mul hp2
    omega
  have s1 : NbrStep p twoE8 gamma16 := nbrStep_of_nbCount_pos hp2 (not_dvd_det isEvenUnimodular_twoE8 p) h
  have s2 : NbrStep p gamma16 twoE8 := nbrStep_of_nbCount_pos hp2 (not_dvd_det isEvenUnimodular_gamma16 p) h'
  intro R S hR hS
  rcases intEquiv_of_isEvenUnimodular_sixteen hR with hR8 | hR16 <;>
    rcases intEquiv_of_isEvenUnimodular_sixteen hS with hS8 | hS16
  · exact (Relation.ReflTransGen.single (nbrStep_transport (IsometricGL.symm hR8) s1 (IsometricGL.refl _))).tail
      (nbrStep_transport (IsometricGL.refl _) s2 hS8)
  · exact Relation.ReflTransGen.single (nbrStep_transport (IsometricGL.symm hR8) s1 hS16)
  · exact Relation.ReflTransGen.single (nbrStep_transport (IsometricGL.symm hR16) s2 hS8)
  · exact (Relation.ReflTransGen.single (nbrStep_transport (IsometricGL.symm hR16) s2 (IsometricGL.refl _))).tail
      (nbrStep_transport (IsometricGL.refl _) s1 hS16)

end QuadFormsKB.ChenevierLannes
