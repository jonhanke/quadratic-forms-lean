/-
# O'Meara §93D: Examples 93:18 (iii), (iv) for lattices on subspaces

**Setting** as in `Sec93D18Q.lean`. O'Meara states 93:18 (iii) and (iv) for a lattice $L$ on the space $V$ ($FL = V$).
In the proofs of 93:18 (v) and 93:20 he applies them to quaternary and ternary *sublattices* of a larger lattice,
i.e. to lattices on the subspace $FL$ of $V$. This file transports a lattice $L \subseteq V$ to the quadratic space
$(FL, Q|_{FL})$, where it is a lattice on the whole space, and back.

**Proves**
* `subIso`: the isometry between $L$ viewed in $FL$ and $L$ in $V$; the invariants $\mathfrak sL$, $\mathfrak nL$,
  $\mathfrak gL$, $\mathfrak wL$, unimodularity, norm and weight generators, and bases with a given matrix are the same
  (`isUnimodular_subLat`, `isNormGenerator_subLat`, `isWeightGenerator_subLat`, `hasBlk_subLat`,
  `hasBlk1_subLat`);
* `finrank_spanF`: $\dim FL = \operatorname{rank} L$ for a regular lattice;
* `omeara93_18_iii_sub`, `omeara93_18_iv_sub`: 93:18 (iii) and (iv) for a lattice $L$ in $V$, without $FL = V$.
-/
import QuadFormsKB.Literature.OMeara.Sec93D18T
import QuadFormsKB.Literature.OMeara.Sec91Gap

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section Transport

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V) (L : Submodule R V)

section Defs

variable (F)

/-- The subspace $FL$ of $V$ spanned by a lattice $L$. -/
abbrev spanF : Submodule F V := span F (L : Set V)

/-- The lattice $L$ viewed as a lattice in $FL$. -/
def subLat : Submodule R (spanF F L) := L.comap ((spanF F L).subtype.restrictScalars R)

theorem map_subLat : (subLat F L).map ((spanF F L).subtype.restrictScalars R) = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, subset_span hx⟩, hx, rfl⟩

/-- The isometry from $L \subseteq FL$ to $L \subseteq V$. -/
def subIso : subLat F L ≃ₗ[R] L :=
  (Submodule.equivMapOfInjective _ (fun a b h => Subtype.ext h) (subLat F L)).trans
    (LinearEquiv.ofEq _ _ (map_subLat F L))

end Defs

/-- The restriction of $Q$ to $FL$. -/
def subQ : QuadraticForm F (spanF F L) := Q.comp (spanF F L).subtype

@[simp] theorem subIso_coe (x : subLat F L) : (subIso F L x : V) = ((x : spanF F L) : V) := rfl

theorem subIso_Q (x : subLat F L) : Q (subIso F L x : V) = subQ Q L (x : spanF F L) := rfl

theorem gram_subIso {ι : Type*} (e : ι → subLat F L) :
    gram Q (fun i => (subIso F L (e i) : V)) = gram (subQ Q L) (fun i => (e i : spanF F L)) := by
  ext i j
  simp only [gram, Matrix.of_apply]
  exact bil_eq_of_isometricLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) (e i) (e j)

theorem gram_subIso_symm {ι : Type*} (e : ι → L) :
    gram (subQ Q L) (fun i => ((subIso F L).symm (e i) : spanF F L)) = gram Q (fun i => (e i : V)) := by
  rw [← gram_subIso Q L]
  simp

theorem imgLat_subIso : imgLat (subIso F L) (subLat F L) = L := imgLat_top _

theorem scale_subLat : scale (subQ Q L) (subLat F L) = scale Q L := by
  rw [← scale_imgLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) le_rfl, imgLat_subIso]

theorem normIdeal_subLat : normIdeal (subQ Q L) (subLat F L) = normIdeal Q L := by
  rw [← normIdeal_imgLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) le_rfl, imgLat_subIso]

theorem normGroup_subLat : normGroup (subQ Q L) (subLat F L) = normGroup Q L := by
  rw [← normGroup_imgLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) le_rfl, imgLat_subIso]

theorem weight_subLat : weight (subQ Q L) (subLat F L) = weight Q L := by
  rw [← weight_imgLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) le_rfl, imgLat_subIso]

theorem finrank_subLat : finrank R (subLat F L) = finrank R L := (subIso F L).finrank_eq

theorem volume_subLat : volume (subQ Q L) (subLat F L) = volume Q L := by
  rw [← volume_imgLat (subQ Q L) Q (subIso F L) (subIso_Q Q L) le_rfl, imgLat_subIso]

theorem isUnimodular_subLat : IsUnimodular (subQ Q L) (subLat F L) ↔ IsUnimodular Q L := by
  unfold IsUnimodular IsModular
  rw [scale_subLat, volume_subLat, finrank_subLat]

theorem isNormGenerator_subLat {a : F} : IsNormGenerator (subQ Q L) (subLat F L) a ↔ IsNormGenerator Q L a := by
  unfold IsNormGenerator
  rw [normGroup_subLat, normIdeal_subLat]

theorem isWeightGenerator_subLat {b : F} :
    IsWeightGenerator (subQ Q L) (subLat F L) b ↔ IsWeightGenerator Q L b := by
  unfold IsWeightGenerator
  rw [weight_subLat]

theorem fg_subLat (hfg : L.FG) : (subLat F L).FG := by
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.iff_fg.mp (Module.Finite.equiv (subIso F L).symm)

theorem hasBlk_subLat {α β γ δ : F} : HasBlk (subQ Q L) (subLat F L) α β γ δ ↔ HasBlk Q L α β γ δ := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L), by rw [← he, ← gram_subIso Q L]; simp⟩
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L).symm, by rw [← he, ← gram_subIso_symm Q L]; simp⟩

theorem hasBlk1_subLat {β γ c : F} : HasBlk1 (subQ Q L) (subLat F L) β γ c ↔ HasBlk1 Q L β γ c := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L), by rw [← he, ← gram_subIso Q L]; simp⟩
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L).symm, by rw [← he, ← gram_subIso_symm Q L]; simp⟩

theorem exists_det_subLat {n : ℕ} {x : F} :
    (∃ e : Basis (Fin n) R (subLat F L), (gram (subQ Q L) fun i => (e i : spanF F L)).det = x) ↔
      ∃ e : Basis (Fin n) R L, (gram Q fun i => (e i : V)).det = x := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L), by rw [← he, ← gram_subIso Q L]; simp⟩
  · rintro ⟨e, he⟩
    exact ⟨e.map (subIso F L).symm, by rw [← he, ← gram_subIso_symm Q L]; simp⟩

/-- **$\dim FL = \operatorname{rank} L$** for a lattice with a base of non-zero discriminant (e.g. a regular lattice). -/
theorem finrank_spanF {n : ℕ} (e : Basis (Fin n) R L) (hdet : (gram Q fun i => (e i : V)).det ≠ 0) :
    finrank F (spanF F L) = n := by
  have hli : LinearIndependent F (fun i => (e i : V)) := linearIndependent_of_det_gram_ne_zero (R := F) Q hdet
  have hsp : spanF F L = span F (Set.range fun i => (e i : V)) := by
    have h1 := congrArg (fun M : Submodule R V => span F (M : Set V)) (span_basis_eq e).symm
    show span F (L : Set V) = _
    rw [h1, Submodule.span_span_of_tower]
  rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

end Transport

section Apply

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

theorem finrank_spanF_of_isUnimodular {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) {n : ℕ}
    (hrk : finrank R L = n) : finrank F (spanF F L) = n := by
  obtain ⟨b₀⟩ := exists_basis (R := R) (F := F) hfg
  let b : Basis (Fin n) R L := b₀.reindex (finCongr hrk)
  obtain ⟨u, hu, hdet⟩ := Eng93.isUnit_det_of_isUnimodular Q hU b
  refine finrank_spanF Q L b ?_
  rw [hdet]
  exact fun h => hu.ne_zero (IsFractionRing.injective R F (h.trans (map_zero _).symm))

/-- **93:18 (iii) for a quaternary unimodular lattice $L$ in $V$** (not necessarily on $V$), as applied by O'Meara to
sublattices in 93:18 (v) and 93:20 (pp. 261–262). The statement is `omeara93_18_iii` without the hypothesis
$\dim V = 4$: it is applied on the space $FL$. -/
@[kb "omeara1963" "§93D, 93:18 (iii), pp. 260–261 (L on a subspace)"]
theorem omeara93_18_iii_sub (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {α : R}
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1 + algebraMap R F α)
    (hdef : quadDefect R (1 + algebraMap R F α) = span R {algebraMap R F α})
    {ρ : R} (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    algebraMap R F α ∈ R ∙ (a * b) ∧
      Xor' (HasBlk Q L a (-(algebraMap R F α) / a) b 0)
        (HasBlk Q L a (-(algebraMap R F α - 4 * algebraMap R F ρ) / a) b (4 * algebraMap R F ρ / b)) := by
  have h := omeara93_18_iii (subQ Q L) hK h2p hπ (finrank_spanF_of_isUnimodular Q hfg hU hrk) (L := subLat F L)
    (fg_subLat L hfg) ((isUnimodular_subLat Q L).mpr hU) (by rw [finrank_subLat]; exact hrk)
    ((isNormGenerator_subLat Q L).mpr ha) ((isWeightGenerator_subLat Q L).mpr hb) hodd
    ((exists_det_subLat Q L).mpr hd) hdef hρ
  rwa [hasBlk_subLat, hasBlk_subLat] at h

/-- **93:18 (iv) for a ternary unimodular lattice $L$ in $V$** (not necessarily on $V$), as applied by O'Meara to
sublattices in 93:18 (v) and 93:20. The statement is `omeara93_18_iv` without the hypothesis $\dim V = 3$. -/
@[kb "omeara1963" "§93D, 93:18 (iv), p. 261 (L on a subspace)"]
theorem omeara93_18_iv_sub (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 3) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {d : R}
    (hd : ∃ e : Basis (Fin 3) R L, (gram Q fun i => (e i : V)).det = algebraMap R F d)
    {ρ : R} (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    Xor' (HasBlk1 Q L b 0 (-algebraMap R F d))
      (HasBlk1 Q L b (4 * algebraMap R F ρ / b) (-(algebraMap R F d * (1 - 4 * algebraMap R F ρ)))) := by
  have h := omeara93_18_iv (subQ Q L) hK h2p hπ (finrank_spanF_of_isUnimodular Q hfg hU hrk) (L := subLat F L)
    (fg_subLat L hfg) ((isUnimodular_subLat Q L).mpr hU) (by rw [finrank_subLat]; exact hrk)
    ((isNormGenerator_subLat Q L).mpr ha) ((isWeightGenerator_subLat Q L).mpr hb) hodd
    ((exists_det_subLat Q L).mpr hd) hρ
  rwa [hasBlk1_subLat, hasBlk1_subLat] at h

end Apply

end QuadFormsKB.OMeara.D18
