/-
# O'Meara §81B and §81D: maximal independent sets of a lattice, and the finiteness of the index

**Setting.** $R$ is a Dedekind domain with fraction field $F$ (O'Meara's $\mathfrak o$ and $F$, Chapter VIII), $V$ a
vector space over $F$, and a lattice in $V$ is a finitely generated $R$-submodule $L \subseteq V$ (`Submodule.FG`,
81:6); it is a lattice *on* $V$ when moreover $FL = V$ (Mathlib's `Submodule.IsLattice F L`). The rank of $L$ is
`Module.finrank R L` (`finrank_eq_finrank_span`: it is $\dim FL$).

**Defines** `IsMaxIndep L s`: $s$ is a maximal subset of $L$ that is independent over $\mathfrak o$ (O'Meara 1963,
§81B, p. 212).

**Proves** (O'Meara 1963, §81B, p. 212, and §81D, p. 216):
* `linearIndepOn_iff_fractionRing`: a set of vectors is independent over $\mathfrak o$ if and only if it is
  independent over $F$ (Mathlib's `LinearIndependent.iff_fractionRing`);
* `isMaxIndep_iff`: a set of vectors of $L$ is maximal independent over $\mathfrak o$ if and only if it is a base for
  $FL$;
* `ncard_eq_finrank_of_isMaxIndep`, `ncard_eq_of_isMaxIndep`: such a set is finite with $\operatorname{rank} L$
  elements, so any two have the same number of elements;
* `finite_quotient_of_le`, `finite_setOf_between`: when every quotient $\mathfrak o/\mathfrak a$ by a non-zero ideal
  is finite ("the important situations", local and global fields), $(L : K) < \infty$ for lattices $K \subseteq L$
  on $V$, and only finitely many lattices lie between $K$ and $L$.
-/
import QuadFormsKB.Literature.OMeara.Sec81Adapted

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **Maximal independent set of a lattice** (O'Meara 1963, §81B, p. 212): $s$ is a subset of $L$, independent over
$\mathfrak o$ (`LinearIndepOn R id s`), and no strictly larger subset of $L$ is independent over $\mathfrak o$. -/
@[kb "omeara1963" "§81B, p. 212 (maximal independent set of vectors of L)"]
def IsMaxIndep (L : Submodule R V) (s : Set V) : Prop :=
  s ⊆ L ∧ LinearIndepOn R id s ∧ ∀ t : Set V, s ⊆ t → t ⊆ L → LinearIndepOn R id t → t = s

include F in
/-- **Independence over $\mathfrak o$ and over $F$ agree** (O'Meara 1963, §81B, p. 212): a set of vectors of $V$ is
independent over $\mathfrak o$ if and only if it is independent over $F$ ("immediately from the fact that $F$ is the
quotient field of $\mathfrak o$"). -/
@[kb "omeara1963" "§81B, p. 212 (independent over o iff independent over F)"]
theorem linearIndepOn_iff_fractionRing (s : Set V) : LinearIndepOn R id s ↔ LinearIndepOn F id s :=
  LinearIndependent.iff_fractionRing R F

/-- **Maximal independent sets are bases of $FL$** (O'Meara 1963, §81B, p. 212): a set $s$ of vectors of a lattice
$L$ is maximal independent over $\mathfrak o$ if and only if it is a base for $FL$ (independent over $F$ and spanning
$FL$). -/
@[kb "omeara1963" "§81B, p. 212 (maximal independent over o iff a base for FL)"]
theorem isMaxIndep_iff {L : Submodule R V} {s : Set V} (hs : s ⊆ L) :
    IsMaxIndep L s ↔ LinearIndepOn F id s ∧ span F s = span F (L : Set V) := by
  constructor
  · rintro ⟨-, hind, hmax⟩
    have hF := (linearIndepOn_iff_fractionRing (F := F) s).1 hind
    refine ⟨hF, le_antisymm (span_mono hs) (span_le.2 fun y hy => ?_)⟩
    by_contra hy'
    have hys : y ∉ s := fun h => hy' (subset_span h)
    have hins : LinearIndepOn F id (insert y s) :=
      (linearIndepOn_insert hys).2 ⟨hF, by simpa using hy'⟩
    have heq := hmax (insert y s) (Set.subset_insert _ _) (Set.insert_subset hy hs)
      ((linearIndepOn_iff_fractionRing (F := F) _).2 hins)
    exact hys (heq ▸ Set.mem_insert y s)
  · rintro ⟨hF, hspan⟩
    refine ⟨hs, (linearIndepOn_iff_fractionRing (F := F) s).2 hF, fun t hst htL htind => ?_⟩
    refine Set.Subset.antisymm (fun y hy => ?_) hst
    by_contra hys
    have htF := (linearIndepOn_iff_fractionRing (F := F) t).1 htind
    have hins : LinearIndepOn F id (insert y s) := htF.mono (Set.insert_subset hy hst)
    apply ((linearIndepOn_insert hys).1 hins).2
    simp only [id_eq, Set.image_id']
    rw [hspan]
    exact subset_span (htL hy)

/-- **A maximal independent set has $\operatorname{rank} L$ elements** (O'Meara 1963, §81B, p. 212): a maximal
independent subset $s$ of a lattice $L$ in a finite-dimensional space is finite and has
$\operatorname{rank} L = \dim FL$ elements. -/
@[kb "omeara1963" "§81B, p. 212 (rank L = number of elements of a maximal independent set)"]
theorem ncard_eq_finrank_of_isMaxIndep [FiniteDimensional F V] {L : Submodule R V} {s : Set V}
    (h : IsMaxIndep L s) : s.Finite ∧ s.ncard = finrank R L := by
  obtain ⟨hF, hspan⟩ := (isMaxIndep_iff (F := F) h.1).1 h
  have hfin : s.Finite := hF.finite
  refine ⟨hfin, ?_⟩
  have := hfin.fintype
  rw [finrank_eq_finrank_span (F := F) L, ← hspan, finrank_span_set_eq_card hF,
    Set.ncard_eq_toFinset_card']

/-- **Any two maximal independent sets have the same number of elements** (O'Meara 1963, §81B, p. 212). -/
@[kb "omeara1963" "§81B, p. 212 (any two maximal independent sets have the same number of elements)"]
theorem ncard_eq_of_isMaxIndep [FiniteDimensional F V] {L : Submodule R V} {s t : Set V}
    (hs : IsMaxIndep L s) (ht : IsMaxIndep L t) : s.ncard = t.ncard := by
  rw [(ncard_eq_finrank_of_isMaxIndep (F := F) hs).2, (ncard_eq_finrank_of_isMaxIndep (F := F) ht).2]

/-- A finitely generated `L` inside `F K` is moved into `K` by one non-zero scalar of `R`. -/
theorem exists_smul_le_of_fg {K L : Submodule R V} (hL : L.FG)
    (hLK : (L : Set V) ⊆ span F (K : Set V)) : ∃ c : R, c ≠ 0 ∧ ∀ x ∈ L, c • x ∈ K := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have hS : ∀ s ∈ S, ∃ d : R, d ≠ 0 ∧ d • s ∈ K := fun s hs =>
    exists_smul_mem_of_mem_span (hLK (subset_span hs))
  choose! d hd0 hdK using hS
  refine ⟨∏ s ∈ S, d s, Finset.prod_ne_zero_iff.2 hd0, fun x hx => ?_⟩
  have hle : span R (S : Set V) ≤ K.comap (LinearMap.lsmul R V (∏ s ∈ S, d s)) := by
    refine span_le.2 fun s hs => ?_
    show (∏ s ∈ S, d s) • s ∈ K
    rw [← Finset.prod_erase_mul S d hs, mul_smul]
    exact K.smul_mem _ (hdK s hs)
  exact hle hx

/-- **$(L : K) < \infty$** (O'Meara 1963, §81D, p. 216): if every quotient $R/\mathfrak a$ by a non-zero ideal is
finite (as for the integers of local and global fields; O'Meara: "the indices $(\mathfrak o : \mathfrak t_i)$ are
all finite"), then for lattices $K \subseteq L$ on $V$ the quotient $L/K$ is finite. (Stated for any two lattices $K$, $L$ on
$V$, with $L/(K \cap L)$ in place of $L/K$; O'Meara's case is $K \subseteq L$.) -/
@[kb "omeara1963" "§81D, p. 216 ((L : K) < ∞ when the indices (o : t_i) are finite)"]
theorem finite_quotient_of_le (hfin : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I)) {K L : Submodule R V}
    (hK : K.IsLattice F) (hL : L.IsLattice F) :
    Finite (L ⧸ K.comap L.subtype) := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_le_of_fg (F := F) hL.fg (by rw [hK.span_eq_top]; exact fun _ _ => trivial)
  set M := L ⧸ K.comap L.subtype
  have htors : IsTorsionBy R M c := by
    rw [isTorsionBy_quotient_iff]
    intro x
    exact hc x x.2
  have : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
  let _ := htors.module
  have : Finite (R ⧸ Ideal.span {c}) := hfin _ (by simpa using hc0)
  have : IsScalarTower R (R ⧸ Ideal.span {c}) M := IsTorsionBySet.isScalarTower _
  have : Module.Finite (R ⧸ Ideal.span {c}) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {c}) M
  exact Module.finite_of_finite (R ⧸ Ideal.span {c})

/-- **Finitely many lattices between $K$ and $L$** (O'Meara 1963, §81D, p. 216): under the hypothesis of
`finite_quotient_of_le`, only finitely many $R$-submodules $M$ of $V$ (all of them lattices on $V$) satisfy
$K \subseteq M \subseteq L$. (O'Meara assumes $K \subseteq L$; otherwise the set is empty.) -/
@[kb "omeara1963" "§81D, p. 216 (the number of lattices between K and L is finite)"]
theorem finite_setOf_between (hfin : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I)) {K L : Submodule R V}
    (hK : K.IsLattice F) (hL : L.IsLattice F) :
    {M : Submodule R V | K ≤ M ∧ M ≤ L}.Finite := by
  set K' := K.comap L.subtype
  have := finite_quotient_of_le (F := F) hfin hK hL
  have : Finite (Submodule R (L ⧸ K')) :=
    Finite.of_injective (fun N : Submodule R (L ⧸ K') => (N : Set (L ⧸ K'))) SetLike.coe_injective
  let f : Submodule R V → Submodule R (L ⧸ K') := fun M => (M.comap L.subtype).map K'.mkQ
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  rintro M ⟨hKM, hML⟩ N ⟨hKN, hNL⟩ hMN
  have hc : ∀ P : Submodule R V, K ≤ P → (f P).comap K'.mkQ = P.comap L.subtype := fun P hKP => by
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono hKP)]
  have h1 : M.comap L.subtype = N.comap L.subtype := by rw [← hc M hKM, ← hc N hKN, hMN]
  rw [← inf_eq_right.2 hML, ← inf_eq_right.2 hNL, ← Submodule.map_comap_subtype, h1,
    Submodule.map_comap_subtype]

end QuadFormsKB.OMeara
