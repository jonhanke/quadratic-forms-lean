/-
# O'Meara Theorem 104:10: one proper class for modular or maximal lattices over $\mathbb Q$

**Layer:** $V = \mathbb Q^n$ with `Q : QuadForm ℚ n` nondegenerate, lattices `Lat ℚ n` ($S$ = all finite spots, so
the lattices are $\mathbb Z$-lattices), as in `OMeara104_10` (`Sec102To104.lean`).

**Proves** **`omeara104_10`** (Theorem 104:10, pp. 320–321): the named statement `OMeara104_10 Q hQ` holds,
unconditionally: if $n \ge 3$, $V_\infty$ is isotropic, and $L$, $K$ are lattices on $V$ with the same norm and the same
scale, both modular or both maximal, then $\operatorname{cls}^+L = \operatorname{cls}^+K$.

*Proof* (O'Meara's). $\operatorname{gen}L = \operatorname{gen}K$: in the modular case by 92:2 at the odd primes and 93:29 at
$2$ (`Sec104TenModular.lean`), in the maximal case by 91:2 applied to the common norm (`sameGenus_of_isMaximalLat`,
`Sec104TenMax.lean`). $J_\mathbb Q = P_DJ_\mathbb Q^S$ by Example 102:10 (i) (`idele_condition_rat`, `Sec102Ten.lean`).
Then Theorem 104:9 (`omeara104_9`) gives $\operatorname{cls}^+L = \operatorname{gen}L \ni K$.
-/
import QuadFormsKB.Literature.OMeara.Sec104NineMain
import QuadFormsKB.Literature.OMeara.Sec104TenMax
import QuadFormsKB.Literature.OMeara.Sec104TenModular
import QuadFormsKB.Literature.OMeara.Sec102Ten

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **Two modular lattices with the same scale and norm on a regular rational space are in the same genus**
(O'Meara 1973, proof of Theorem 104:10, p. 320: "In the modular case we have $\operatorname{gen}L = \operatorname{gen}K$
by Theorems 92:2 and 93:29"). -/
@[kb "omeara1963" "§104, proof of 104:10, p. 320 (modular case: gen L = gen K by 92:2 and 93:29)"]
theorem sameGenus_of_isModularLat_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) {L K : Lat ℚ n}
    (hL : IsModularLat Q L) (hK : IsModularLat Q K)
    (hs : OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1)
    (hnorm : OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1) :
    SameGenus Q L.1 K.1 := by
  intro v
  by_cases h2 : IsUnit (2 : v.adicCompletionIntegers ℚ)
  · obtain ⟨g, hg⟩ := exists_locAct_eq_of_mem_cls Q v (mem_cls_loc_of_isModular_nondyadic Q v h2 hL hK hs hnorm)
    exact ⟨g, g.2, hg⟩
  · obtain ⟨g, hg⟩ := exists_locAct_eq_of_mem_cls Q v
      (mem_cls_loc_of_isModular_twoAdic Q v hQ (isTwoAdic_rat v h2) hL hK hs hnorm)
    exact ⟨g, g.2, hg⟩

/-- **Theorem 104:10** (O'Meara 1973, §104, pp. 320–321): the named statement `OMeara104_10 Q hQ` holds for every
nondegenerate form $Q$ over $\mathbb Q$. Unconditional. -/
@[kb "omeara1963" "§104, 104:10, pp. 320–321"]
theorem omeara104_10 {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) : OMeara104_10 Q hQ := by
  refine ⟨fun hn hind L K hnorm hs hLK => ?_⟩
  have hgen : SameGenus Q L.1 K.1 := by
    rcases hLK with ⟨hL, hK⟩ | ⟨hL, hK⟩
    · exact sameGenus_of_isModularLat_rat Q hQ hL hK hs hnorm
    · exact sameGenus_of_isMaximalLat Q hQ (by omega) hL hK hnorm
  have hLmm : IsModularLat Q L ∨ IsMaximalLat Q L := by
    rcases hLK with ⟨hL, -⟩ | ⟨hL, -⟩
    · exact Or.inl hL
    · exact Or.inr hL
  exact (omeara104_9 Q hQ).holds hn hind (idele_condition_rat Q hQ hn hind) L K hLmm hgen

end QuadFormsKB.Lattices
