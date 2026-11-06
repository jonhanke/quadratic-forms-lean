/-
# O'Meara Chapter X: remaining citations

Items of Chapter X (introduction and §101) that had no citation tag yet and whose content is already a library
declaration: the O'Meara tag is added here with
`attribute [kb …]`, so the files where the declarations live are unchanged. One running-text claim (101.r57) had no
standalone declaration; it is stated and proved here (`eventually_locAct_loc_eq`).

Conventions as in `CitationsX.lean`: $F$ a number field, $S$ the set of all finite spots, lattices `Lattices.Lat F n`,
$J_V$ = `Lattices.OAf Q` (finite spots, full orthogonal groups).
-/
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion
import QuadFormsKB.Literature.OMeara.Sec101A
import QuadFormsKB.Literature.OMeara.Sec82Free
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Literature.OMeara.Sec64
import QuadFormsKB.Literature.OMeara.Sec106A
import QuadFormsKB.Literature.OMeara.Sec106Defs

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB

/-! ### Introduction to Chapter X (p. 284) -/

-- X.r2: the setting (lattices on V with respect to S; here S = all finite spots, 𝔬 = 𝓞_F)
attribute [kb "omeara1963" "Ch. X introduction, p. 284 (lattices on V with respect to the set S of spots; special case: S all finite spots)"]
  Lattices.Lat
-- X.r3, X.r5: localizations 𝔞_𝔭, V_𝔭, L_𝔭
attribute [kb "omeara1963" "Ch. X introduction, p. 284 (the localizations V_𝔭 and L_𝔭)"] Lattices.loc
-- X.r4: V is a regular quadratic space
attribute [kb "omeara1963" "Ch. X introduction, p. 284 (V a regular quadratic space)"] QuadForm.Nondegenerate
-- X.r6: the notation O(V), O⁺(V), … carried over from Chapters IV and V
attribute [kb "omeara1963" "Ch. X introduction, p. 284 (notation O(V), O⁺(V) carried over)"]
  Lattices.orthGroup Tamagawa.soSub

/-! ### §101B and §101D -/

-- 101.r26: the norms at every spot are taken with respect to one base of V
attribute [kb "omeara1963" "§101B, p. 289 (norms ‖ ‖_𝔭 at every spot with respect to a common base of V; finite spots)"]
  Lattices.vecNorm Lattices.matNorm
-- 101.r30, 101.r32: a rotation localizes to a rotation; O'(V)_𝔭 ⊆ O'(V_𝔭)
attribute [kb "omeara1963" "§101B, p. 289 (σ a rotation ⇒ σ_𝔭 a rotation)"] Lattices.orthMap_mem_soSub
attribute [kb "omeara1963" "§101B, p. 290 (O'(V)_𝔭 ⊆ O'(V_𝔭))"] Lattices.orthMap_mem_spinorKernel
-- 101.r35: recalled facts cls⁺L = cls L for odd n, and over local fields
attribute [kb "omeara1963" "§101B, 101:10, p. 292 (recalled: cls⁺L = cls L when n is odd, Example 82:4)"]
  OMeara.clsPlus_eq_cls_of_odd
attribute [kb "omeara1963" "§101B, 101:10, p. 292 (recalled: cls⁺L = cls L over local fields, Corollary 91:4a)"]
  OMeara.clsPlus_eq_cls
-- 101.r42: the idèle groups J_F^S recalled from §33I and §65A
attribute [kb "omeara1963" "§101D, p. 295 (recalled: the idèle groups J_F^S)"] OMeara.sIdeles
-- 101.r43: the direct product of the O(V_𝔭) with coordinatewise multiplication (restricted product)
attribute [kb "omeara1963" "§101D, p. 295 (the direct product of the groups O(V_𝔭), coordinatewise multiplication; variant: restricted product, finite spots, full orthogonal groups)"]
  Lattices.OAf
-- 101.r45: split rotations do not depend on the base (norms agree at almost all 𝔭)
attribute [kb "omeara1963" "§101D, p. 296 (the definition of a split rotation is independent of the base, by 101:1)"]
  Lattices.eventually_matNorm_conj_eq
-- 101.r49: σ ↦ (σ) is injective
attribute [kb "omeara1963" "§101D, p. 296 (σ ↦ (σ) is an injective homomorphism of O(V) into J_V)"]
  Lattices.diagF_injective

/-! ### §106 introduction -/

-- 106.r1: the setting of §106 (lattices over ℤ on a positive definite space carrying a unimodular lattice)
attribute [kb "omeara1963" "§106, p. 323 (setting: F = ℚ, S all discrete spots, unimodular lattices on a positive definite V)"]
  Lattices.IsUnimodularZ
-- 106.r5, 106.r6: dV = 1 and S_p V = 1 at every p, used to obtain V ≅ I_n
attribute [kb "omeara1963" "§106, p. 324 (a unimodular ℤ-lattice has discriminant ±1, so dV = 1; S_p V = 1 for all p by Hilbert reciprocity; the Hasse symbol route is replaced by diagonalization)"]
  Lattices.omeara106_r1

namespace Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **$\Sigma_\mathfrak p L_\mathfrak p = L_\mathfrak p$ for almost all $\mathfrak p$** (O'Meara 1973, §101D, p. 297):
for a split rotation $\Sigma \in J_V$ (here `OAf Q`: finite spots, full orthogonal groups) and a lattice $L$ on $V$,
the local lattices $\Sigma_\mathfrak p L_\mathfrak p$ and $L_\mathfrak p$ agree at all but finitely many finite spots.
(O'Meara: $\Sigma_\mathfrak p M_\mathfrak p = M_\mathfrak p$ for almost all $\mathfrak p$, $M = \mathfrak o x_1 + \dots +
\mathfrak o x_n$, and $M_\mathfrak p = L_\mathfrak p$ for almost all $\mathfrak p$.) -/
@[kb "omeara1963" "§101D, p. 297 (Σ_𝔭 L_𝔭 = L_𝔭 for almost all 𝔭)"]
theorem eventually_locAct_loc_eq (h : OAf Q) (L : Lat F n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v L.1 := by
  filter_upwards [h.2, loc_eventually_std L.2] with v hv hL
  rw [hL]; exact hv

end Lattices

end QuadFormsKB
