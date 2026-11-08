/-
# O'Meara Example 102:3: the genus of an $\mathfrak a$-maximal lattice

**Layer:** $V = F^n$ over a number field $F$, `Q : QuadForm F n` nondegenerate, lattices `Lat F n`, $S$ = all finite
spots; local forms `Qv` = `QuadForm.toQuadraticForm (Q.map (algebraMap F F_𝔭))`.

**Proves** (O'Meara 1973)
* `isMaximal_of_sameGenus`: a lattice in the genus of an $\mathfrak a$-maximal lattice is $\mathfrak a$-maximal;
* `sameGenus_of_isMaximal`: two $\mathfrak a$-maximal lattices on $V$ are in the same genus (91:2 at each completion);
* `scale_eq_of_sameGenus`, `normIdeal_eq_of_sameGenus`: lattices of one genus have the same scale and norm;
* `isModular_of_sameGenus` (§102A, p. 299): a lattice in the genus of an $\mathfrak a$-modular lattice is
  $\mathfrak a$-modular;
* **`omeara102_3_holds`** (Example 102:3, p. 299): the named statement `OMeara102_3 Q hQ 𝔞` holds, unconditionally.

*Proof* (O'Meara's): maximality is local (`isMaximal_loc_locFrac`, `isMaximal_of_forall_loc`, `Sec102Max.lean`) and is
preserved by isometries; two $\mathfrak a_\mathfrak p$-maximal lattices on $V_\mathfrak p$ are isometric (Theorem 91:2,
`OMeara.cls_eq_of_isMaximal`); scale, norm and volume of the lattices of a genus agree locally (§82K at the completion,
`scale_loc`, `normIdeal_loc`, `volume_loc`), hence globally.
-/
import QuadFormsKB.Literature.OMeara.Sec102Max
import QuadFormsKB.Literature.OMeara.Sec93Example
import QuadFormsKB.Literature.OMeara.Sec91Max

open NumberField IsDedekindDomain Matrix Submodule
open QuadFormsKB.OMeara.QIn (glEquiv map_orthGroup)
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- The O'Meara isometry `glEquiv g` of a local isometry $g$ of the genus, for the local form `Qv`. -/
theorem glEquiv_mem_orth_Qv (v : HeightOneSpectrum (𝓞 F)) {g : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ orthGroup Q (v.adicCompletion F)) :
    glEquiv (v.adicCompletion F) g ∈
      OMeara.orth (QuadForm.toQuadraticForm (Q.map (algebraMap F (v.adicCompletion F)))) := by
  rw [← qk_eq_toQuadraticForm_map, ← map_orthGroup Q (v.adicCompletion F)]
  exact ⟨g, hg, rfl⟩

/-- **The genus of an $\mathfrak a$-maximal lattice consists of $\mathfrak a$-maximal lattices** (O'Meara 1973,
§102A, p. 299, and Example 102:3): if $L$ is $\mathfrak a$-maximal ($\mathfrak a$ a non-zero finitely generated
$\mathcal O_F$-submodule of $F$) and $K \in \operatorname{gen}L$, then $K$ is $\mathfrak a$-maximal. -/
@[kb "omeara1963" "§102A, p. 299 (a genus containing an a-maximal lattice consists of a-maximal lattices)"]
theorem isMaximal_of_sameGenus {a : Submodule (𝓞 F) F} (ha : a.FG) (ha0 : a ≠ ⊥) {L K : Lat F n}
    (hL : OMeara.IsMaximal Q.toQuadraticForm a L.1) (hLK : SameGenus Q L.1 K.1) :
    OMeara.IsMaximal Q.toQuadraticForm a K.1 := by
  refine isMaximal_of_forall_loc Q ha ha0 fun w => ?_
  obtain ⟨g, hg, he⟩ := hLK w
  rw [← he, locAct_eq_latMap]
  exact (isMaximal_loc_locFrac Q w ha ha0 hL).latMap' _ (glEquiv_mem_orth_Qv Q w hg)

/-- **Two $\mathfrak a$-maximal lattices on $V$ are in the same genus** (O'Meara 1973, Example 102:3, p. 299, from
Theorem 91:2 at each completion), for $Q$ nondegenerate and $\mathfrak a$ a non-zero finitely generated
$\mathcal O_F$-submodule of $F$. -/
@[kb "omeara1963" "§102A, 102:3, p. 299 (two a-maximal lattices are in the same genus; 91:2)"]
theorem sameGenus_of_isMaximal (hQ : Q.Nondegenerate) {a : Submodule (𝓞 F) F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {L K : Lat F n} (hL : OMeara.IsMaximal Q.toQuadraticForm a L.1)
    (hK : OMeara.IsMaximal Q.toQuadraticForm a K.1) : SameGenus Q L.1 K.1 := by
  intro w
  have hLw := isMaximal_loc_locFrac Q w ha ha0 hL
  have hKw := isMaximal_loc_locFrac Q w ha ha0 hK
  rw [← qk_eq_toQuadraticForm_map] at hLw hKw
  have hnd : (QuadraticMap.associated (qk Q (w.adicCompletion F))).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp
        (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (w.adicCompletion F) hQ))
  have hcls := OMeara.cls_eq_of_isMaximal (qk Q (w.adicCompletion F)) hnd hLw hKw
  have hmem : loc w K.1 ∈ OMeara.cls (qk Q (w.adicCompletion F)) (loc w L.1) := by
    rw [← hcls]; exact OMeara.mem_cls_self _ _
  obtain ⟨g, hg⟩ := exists_locAct_eq_of_mem_cls Q w hmem
  exact ⟨g, g.2, hg⟩

/-- **Lattices of one genus have the same scale** (O'Meara 1973, §102A, p. 299): $\mathfrak sK = \mathfrak sL$ for
$K \in \operatorname{gen}L$. -/
@[kb "omeara1963" "§102A, p. 299 (lattices of one genus have the same scale)"]
theorem scale_eq_of_sameGenus {L K : Lat F n} (hLK : SameGenus Q L.1 K.1) :
    OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1 := by
  apply eq_of_forall_locFrac_eq (OMeara.scale_fg _ L.2.fg) (OMeara.scale_fg _ K.2.fg)
  intro w
  rw [← scale_loc, ← scale_loc]
  obtain ⟨g, hg, he⟩ := hLK w
  rw [← he, locAct_eq_latMap]
  exact (OMeara.IsometricLat.scale_eq _ _ (OMeara.isometricLat_latMap _ (glEquiv_mem_orth_Qv Q w hg) _)
    (loc_isLattice w L.2).fg).symm

/-- **Lattices of one genus have the same norm** (O'Meara 1973, §102A, p. 299): $\mathfrak nK = \mathfrak nL$ for
$K \in \operatorname{gen}L$. -/
@[kb "omeara1963" "§102A, p. 299 (lattices of one genus have the same norm)"]
theorem normIdeal_eq_of_sameGenus {L K : Lat F n} (hLK : SameGenus Q L.1 K.1) :
    OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1 := by
  apply eq_of_forall_locFrac_eq
    ((OMeara.scale_fg _ L.2.fg).of_le (OMeara.normIdeal_le_scale _ _))
    ((OMeara.scale_fg _ K.2.fg).of_le (OMeara.normIdeal_le_scale _ _))
  intro w
  rw [← normIdeal_loc, ← normIdeal_loc]
  obtain ⟨g, hg, he⟩ := hLK w
  rw [← he, locAct_eq_latMap]
  exact (OMeara.IsometricLat.normIdeal_eq _ _
    (OMeara.isometricLat_latMap _ (glEquiv_mem_orth_Qv Q w hg) _)).symm

/-- **The genus of an $\mathfrak a$-modular lattice consists of $\mathfrak a$-modular lattices** (O'Meara 1973, §102A,
p. 299): if $L$ is $\mathfrak a$-modular and $K \in \operatorname{gen}L$, then $K$ is $\mathfrak a$-modular, since the
lattices of a genus have the same scale and the same volume (102.r18) and the same rank $n$. -/
@[kb "omeara1963" "§102A, p. 299 (a genus containing an a-modular lattice consists of a-modular lattices)"]
theorem isModular_of_sameGenus {a : Submodule (𝓞 F) F} {L K : Lat F n}
    (hL : OMeara.IsModular Q.toQuadraticForm a L.1) (hLK : SameGenus Q L.1 K.1) :
    OMeara.IsModular Q.toQuadraticForm a K.1 := by
  refine ⟨hL.1, (scale_eq_of_sameGenus Q hLK).symm.trans hL.2.1, ?_⟩
  have hv : OMeara.volume Q.toQuadraticForm K.1 = OMeara.volume Q.toQuadraticForm L.1 :=
    ((omeara102_r18_holds Q).holds L K hLK).symm
  rw [hv, hL.2.2, finrank_lat, finrank_lat]

/-- **Example 102:3** (O'Meara 1973, §102A, p. 299): the named statement `OMeara102_3 Q hQ 𝔞` holds for every
nondegenerate $Q$ on $F^n$ over a number field and every non-zero fractional ideal $\mathfrak a$: the genus of an
$\mathfrak a$-maximal lattice $L$ is the set of all $\mathfrak a$-maximal lattices on $V$, and any two of them have the
same scale, norm and volume. Unconditional. -/
@[kb "omeara1963" "§102A, 102:3, p. 299"]
theorem omeara102_3_holds (hQ : Q.Nondegenerate) (a : FractionalIdeal (𝓞 F)⁰ F) : OMeara102_3 Q hQ a := by
  have hfg : (a : Submodule (𝓞 F) F).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl a
  have h0 : a ≠ 0 → (a : Submodule (𝓞 F) F) ≠ ⊥ := fun ha => by
    rwa [ne_eq, FractionalIdeal.coeToSubmodule_eq_bot]
  refine ⟨fun ha L K hL => ⟨fun hLK => isMaximal_of_sameGenus Q hfg (h0 ha) hL hLK,
    fun hK => sameGenus_of_isMaximal Q hQ hfg (h0 ha) hL hK⟩, fun ha L K hL hK => ?_⟩
  have hLK := sameGenus_of_isMaximal Q hQ hfg (h0 ha) hL hK
  exact ⟨scale_eq_of_sameGenus Q hLK, normIdeal_eq_of_sameGenus Q hLK, (omeara102_r18_holds Q).holds L K hLK⟩

end QuadFormsKB.Lattices
