/-
# O'Meara Theorem 104:9: modular and maximal lattices in the indefinite case

**Layer:** $V = F^n$ over a number field $F$, `Q : QuadForm F n` nondegenerate, lattices `Lat F n`, $S$ = all finite
spots (as in `OMeara104_9`, `Sec102To104.lean`).

**Proves** (O'Meara 1973)
* `spinorNormsContainUnits_of_isModularLat` (102:10 (ii) with 92:5 and 93:20): a modular lattice on $V$, $n \ge 3$, has
  $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ at every finite spot;
* `spinorNormsContainUnits_of_isMaximalLat` (102:10 (ii) with 91:8): the same for a maximal lattice;
* **`omeara104_9`** (Theorem 104:9, p. 320): the named statement `OMeara104_9 Q hQ` holds, unconditionally:
  $n \ge 3$, $S$ indefinite for $V$, $J_F = P_DJ_F^S$, $L$ modular or maximal $\Rightarrow$
  $\operatorname{cls}^+L = \operatorname{gen}L$.

*Proof* (O'Meara's): $\operatorname{cls}^+L = \operatorname{spn}^+L$ by 104:5 and $\operatorname{spn}^+L = \operatorname{gen}L$
by 102:9 (`omeara104_9_of_local`, `Sec104Nine.lean`); the local hypothesis of 102:9 is Example 102:10 (ii): at a
non-dyadic spot 92:5 (`OMeara.exists_hasSpinorNorm_of_isModular`), at a dyadic spot 93:20 (`OMeara.D18.omeara93_20_nf`),
and for maximal lattices 91:8 (`OMeara.exists_hasSpinorNorm_of_isMaximal`), transported to the completions by
`isModular_loc_of_isModularLat`, `isMaximal_loc_of_isMaximalLat` (`Sec104LocalMod.lean`) and to the matrix groups by
`spinorNormsContainUnits_of_omeara` (`Sec104Bridge.lean`).
-/
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec104LocalMod
import QuadFormsKB.Literature.OMeara.Sec93DNF
import QuadFormsKB.Literature.OMeara.Sec91Local

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A modular lattice has $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$** (O'Meara 1973, Example 102:10 (ii),
p. 304, with Proposition 92:5 at the non-dyadic spots and Example 93:20 at the dyadic spots): for $Q$ nondegenerate on
$F^n$ with $n \ge 3$ and $L$ a modular lattice (`IsModularLat`), `SpinorNormsContainUnits Q v L` holds at every finite
spot $v$. -/
@[kb "omeara1963" "§102B, 102:10 (ii), p. 304 (modular lattices; 92:5, 93:20)"]
theorem spinorNormsContainUnits_of_isModularLat (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {L : Lat F n}
    (hL : IsModularLat Q L) : SpinorNormsContainUnits Q v L := by
  apply spinorNormsContainUnits_of_omeara Q v hQ L
  intro ε hε
  obtain ⟨a, -, hmod⟩ := isModular_loc_of_isModularLat (v := v) (Q := Q) hL
  rw [← qk_eq_toQuadraticForm_map] at hmod
  have hrk : Module.finrank 𝔬 (loc v L.1) = n := finrank_loc v L
  by_cases h2 : IsUnit (2 : 𝔬)
  · exact OMeara.exists_hasSpinorNorm_of_isModular (qk Q Fv) h2 (loc_fg v L) hmod (by omega) hε
  · exact OMeara.D18.omeara93_20_nf v (qk Q Fv) h2 (loc_fg v L) hmod (by omega) hε

/-- **A maximal lattice has $\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$** (O'Meara 1973, Example 102:10 (ii),
p. 304, with Proposition 91:8): for $Q$ nondegenerate on $F^n$ with $n \ge 3$ and $L$ a maximal lattice
(`IsMaximalLat`), `SpinorNormsContainUnits Q v L` holds at every finite spot $v$. -/
@[kb "omeara1963" "§102B, 102:10 (ii), p. 304 (maximal lattices; 91:8)"]
theorem spinorNormsContainUnits_of_isMaximalLat (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {L : Lat F n}
    (hL : IsMaximalLat Q L) : SpinorNormsContainUnits Q v L := by
  apply spinorNormsContainUnits_of_omeara Q v hQ L
  intro ε hε
  obtain ⟨a, hmax⟩ := isMaximal_loc_of_isMaximalLat Q v hQ hL
  rw [← qk_eq_toQuadraticForm_map] at hmax
  have hnd : (QuadraticMap.associated (qk Q Fv)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn Fv hQ))
  exact OMeara.exists_hasSpinorNorm_of_isMaximal v (qk Q Fv) hnd (by simpa using hn) hmax hε

end Local

/-- **Theorem 104:9** (O'Meara 1973, §104, p. 320): the named statement `OMeara104_9 Q hQ` holds for every
nondegenerate $Q$ on $F^n$ over a number field $F$: if $n \ge 3$, $S$ (all finite spots) is indefinite for $V$, the
idèle condition $J_F = P_DJ_F^S$ holds ($D = \theta(O^+(V))$) and $L$ is modular or maximal on $V$, then
$\operatorname{cls}^+L = \operatorname{gen}L$. Unconditional. -/
@[kb "omeara1963" "§104, 104:9, p. 320"]
theorem omeara104_9 (hQ : Q.Nondegenerate) : OMeara104_9 Q hQ := by
  refine ⟨fun hn hind hJ L K hL hK => ?_⟩
  have hloc : ∀ v, SpinorNormsContainUnits Q v L := fun v => by
    rcases hL with hL | hL
    · exact spinorNormsContainUnits_of_isModularLat Q v hQ hn hL
    · exact spinorNormsContainUnits_of_isMaximalLat Q v hQ hn hL
  exact omeara104_9_of_local Q hQ hn hind hJ L hloc hK

end QuadFormsKB.Lattices
