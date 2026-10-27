/-
# O'Meara §92: classification of lattices over non-dyadic local fields (92:1a, 92:2)

**Setting** (as in `Sec92.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, quadratic spaces $(V, Q)$, $(V', Q')$ over $F$, lattices = `Submodule R V`.

**Proves**
* `gram_smul`, `isUnimodular_smul_of_isModular`: scaling the form by $\alpha^{-1}$ turns an $\alpha$-modular lattice
  into a unimodular one (O'Meara 1963, §82J, p. 238);
* `isometricLat_iff_sameDisc_of_isUnimodular` (**92:1a**, p. 247): unimodular lattices of the same rank are isometric
  if and only if their discriminants agree in $\mathfrak u/\mathfrak u^2$;
* `exists_nonsquare_unit` (**92:1a**): $\mathfrak u/\mathfrak u^2$ has exactly two classes, so there are essentially two
  unimodular lattices of a given rank;
* `isometricLat_iff_sameDisc_of_isModular`: the same for $\mathfrak a$-modular lattices.
-/
import QuadFormsKB.Literature.OMeara.Sec92

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Scaling

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Scaling** (O'Meara 1963, §82J, p. 238): the bilinear form of $cQ$ is $cB$. -/
theorem bil_smul (c : F) (x y : V) : bil (c • Q) x y = c * bil Q x y := by
  simp [bil, QuadraticMap.associated_apply, smul_eq_mul]

theorem gram_smul (c : F) {ι : Type*} (x : ι → V) : gram (c • Q) x = c • gram Q x := by
  ext i j; simp [gram, bil_smul]

end Scaling

section ScalingDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Scaling a modular lattice to a unimodular one** (O'Meara 1963, §82J, p. 238: if $L$ is
$\mathfrak a$-modular in $V$ then $L$ is $c\mathfrak a$-modular in $V^c$): an $\alpha$-modular lattice is unimodular
for the form $\alpha^{-1}Q$. -/
theorem isUnimodular_smul_of_isModular {α : F} (hα : α ≠ 0) {L : Submodule R V} (hfg : L.FG)
    (hL : IsModular Q (R ∙ α) L) : IsUnimodular (α⁻¹ • Q) L := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  obtain ⟨hne, U, hU, hG⟩ := (isModular_iff_gram Q b hα).mp hL
  have h1 : (algebraMap R F 1) ≠ 0 := by simp
  have : IsModular (α⁻¹ • Q) (R ∙ algebraMap R F 1) L := by
    refine (isModular_iff_gram (α⁻¹ • Q) b h1).mpr ⟨hne, U, hU, ?_⟩
    rw [gram_smul, hG, smul_smul, inv_mul_cancel₀ hα, map_one]
  rwa [map_one, ← Submodule.one_eq_span] at this

end ScalingDomain

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- The discriminant of the normal form $\langle 1, \dots, 1, \varepsilon\rangle$ is $\varepsilon$. -/
theorem det_gram_of_diag {L : Submodule R V} {ε : R} (b : Basis (Fin (finrank R L)) R L)
    (hb : ∀ i j, bil Q (b i : V) (b j : V) =
      if i = j then (if i.val + 1 = finrank R L then algebraMap R F ε else 1) else 0)
    (hpos : 0 < finrank R L) : (gram Q fun i => (b i : V)).det = algebraMap R F ε := by
  classical
  have : (gram Q fun i => (b i : V)) =
      Matrix.diagonal fun i => if i.val + 1 = finrank R L then algebraMap R F ε else 1 := by
    ext i j
    rw [gram, Matrix.of_apply, hb, Matrix.diagonal_apply]
  rw [this, Matrix.det_diagonal]
  have hlast : ∃ i₀ : Fin (finrank R L), i₀.val + 1 = finrank R L := ⟨⟨finrank R L - 1, by omega⟩, by simp; omega⟩
  obtain ⟨i₀, hi₀⟩ := hlast
  rw [Finset.prod_eq_single i₀]
  · rw [if_pos hi₀]
  · intro j _ hj
    rw [if_neg]; intro h; exact hj (Fin.ext (by omega))
  · simp

/-- A unimodular lattice has positive rank. -/
theorem finrank_pos_of_isModular {a : Submodule R F} {L : Submodule R V} (hfg : L.FG) (hL : IsModular Q a L) :
    0 < finrank R L := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  rcases Nat.eq_zero_or_pos (finrank R L) with h0 | h0
  · exfalso
    have hsc : scale Q L = ⊥ := by
      rw [← span_basis_eq b, scale_span, span_eq_bot]
      rintro _ ⟨p, rfl⟩; exact Fin.elim0 (h0 ▸ p.1)
    exact hL.1 (hL.2.1.symm.trans hsc)
  · exact h0

/-- **Proposition 92:1a, first part** (O'Meara 1963, p. 247, from 92:1): two unimodular lattices of the same rank over
a non-dyadic local field are isometric if and only if their discriminants agree in $\mathfrak u/\mathfrak u^2$. -/
@[kb "omeara1963" "§92, 92:1a, p. 247 (unimodular lattices classified by dL)"]
theorem isometricLat_iff_sameDisc_of_isUnimodular (h2 : IsUnit (2 : R)) {L : Submodule R V}
    {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG) (hL : IsUnimodular Q L) (hK : IsUnimodular Q' K)
    (hrk : finrank R L = finrank R K) : IsometricLat Q Q' L K ↔ SameDisc Q Q' L K := by
  refine ⟨fun h => h.sameDisc Q Q' hLfg, fun hd => ?_⟩
  obtain ⟨ε, hε, b, hb⟩ := exists_basis_diag_of_isUnimodular Q h2 hLfg hL
  obtain ⟨ε', hε', b', hb'⟩ := exists_basis_diag_of_isUnimodular Q' h2 hKfg hK
  have hpos := finrank_pos_of_isModular Q hLfg hL
  obtain ⟨u, hu, hdet⟩ := SameDisc.forall Q Q' hd b b'
  rw [det_gram_of_diag Q b hb hpos, det_gram_of_diag Q' b' hb' (hrk ▸ hpos)] at hdet
  -- rescale the last vector of `b'` by `u`
  let w : Fin (finrank R K) → Rˣ := fun i => if i.val + 1 = finrank R K then hu.unit else 1
  let b'' := (b'.unitsSMul w).reindex (finCongr hrk.symm)
  refine isometricLat_of_gram_eq Q Q' b b'' ?_
  ext i j
  set i' := (finCongr hrk.symm).symm i
  set j' := (finCongr hrk.symm).symm j
  have hb''i : (b'' i : V') = (w i' : R) • (b' i' : V') := by
    simp [b'', Basis.reindex_apply, Basis.unitsSMul_apply, i', Units.smul_def]
  have hb''j : (b'' j : V') = (w j' : R) • (b' j' : V') := by
    simp [b'', Basis.reindex_apply, Basis.unitsSMul_apply, j', Units.smul_def]
  have hii : i'.val = i.val := by simp [i']
  have hjj : j'.val = j.val := by simp [j']
  have hij : i' = j' ↔ i = j := by simp [i', j']
  simp only [gram, Matrix.of_apply]
  rw [hb''i, hb''j, bil_rsmul_left, bil_rsmul_right, hb, hb']
  by_cases h : i = j
  · subst h
    have e : j' = i' := rfl
    rw [e]
    have hl : (i.val + 1 = finrank R L) ↔ (i'.val + 1 = finrank R K) := by omega
    simp only [if_true]
    by_cases hlast : i.val + 1 = finrank R L
    · have hlast' := hl.mp hlast
      simp only [w, if_pos hlast, if_pos hlast', IsUnit.unit_spec, hdet]
      ring
    · have hlast' : ¬ (i'.val + 1 = finrank R K) := fun h => hlast (hl.mpr h)
      simp [w, hlast, hlast']
  · have h' : ¬ i' = j' := fun h'' => h (hij.mp h'')
    simp [h, h']

/-- **Proposition 92:1a, second part** (O'Meara 1963, p. 247: "there are essentially two unimodular lattices of given
dimension"): over a non-dyadic local field there is a unit $\Delta$ which is not a square, and every unit is a square
or $\Delta$ times a square; so by the first part a unimodular lattice of given rank is isometric to
$\langle 1, \dots, 1, 1\rangle$ or to $\langle 1, \dots, 1, \Delta\rangle$. -/
@[kb "omeara1963" "§92, 92:1a, p. 247 (essentially two unimodular lattices)"]
theorem exists_nonsquare_unit (h2 : IsUnit (2 : R)) :
    ∃ Δ : R, IsUnit Δ ∧ ¬ IsSquare Δ ∧ ∀ ε : R, IsUnit ε → IsSquare ε ∨ IsSquare (ε * Δ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  have hchar := LocalDensity.DVR.ringChar_residueField_ne_two hπ h2'
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  obtain ⟨Δ, hΔ⟩ := IsLocalRing.residue_surjective a
  -- a unit with residue a square of a non-zero residue is a square (Hensel)
  have lift : ∀ c : R, IsSquare (residue R c) → residue R c ≠ 0 → IsSquare c := by
    intro c ⟨s, hs⟩ hc0
    have hs0 : s ≠ 0 := by rintro rfl; exact hc0 (by simp [hs])
    obtain ⟨z, hz⟩ := Lattices.Nbr.exists_sq_eq_of_residue hπ h2' c hs0 (by rw [hs, _root_.sq])
    exact ⟨z, by rw [← hz, _root_.sq]⟩
  have hunit : ∀ c : R, residue R c ≠ 0 → IsUnit c := by
    intro c hc
    by_contra h
    exact hc ((residue_eq_zero_iff c).mpr ((mem_maximalIdeal _).mpr h))
  refine ⟨Δ, hunit Δ (by rw [hΔ]; exact ha0), fun ⟨r, hr⟩ => ha ⟨residue R r, by rw [← hΔ, hr, map_mul]⟩,
    fun ε hε => ?_⟩
  have hε0 : residue R ε ≠ 0 := fun h => by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h; exact h hε
  by_cases hsq : IsSquare (residue R ε)
  · exact Or.inl (lift ε hsq hε0)
  · right
    refine lift _ ?_ (by rw [map_mul, hΔ]; exact mul_ne_zero hε0 ha0)
    rw [map_mul, hΔ, ← quadraticChar_one_iff_isSquare (mul_ne_zero hε0 ha0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr hsq, quadraticChar_neg_one_iff_not_isSquare.mpr ha]
    norm_num

/-- **Modular lattices of the same scale and rank** (92:1a after scaling, O'Meara 1963, §82J and §92, pp. 238, 247):
over a non-dyadic local field two $\mathfrak a$-modular lattices of the same rank are isometric if and only if their
discriminants agree in $F/\mathfrak u^2$. -/
@[kb "omeara1963" "§92, 92:1a, p. 247 (scaled to a-modular lattices, §82J)"]
theorem isometricLat_iff_sameDisc_of_isModular (h2 : IsUnit (2 : R)) {a : Submodule R F}
    {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG) (hL : IsModular Q a L)
    (hK : IsModular Q' a K) (hrk : finrank R L = finrank R K) :
    IsometricLat Q Q' L K ↔ SameDisc Q Q' L K := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton (R := R) (hL.2.1 ▸ scale_fg Q hLfg) hL.1
  have hα' : α⁻¹ ≠ 0 := inv_ne_zero hα
  have key := isometricLat_iff_sameDisc_of_isUnimodular (α⁻¹ • Q) (α⁻¹ • Q') h2 hLfg hKfg
    (isUnimodular_smul_of_isModular Q hα hLfg hL) (isUnimodular_smul_of_isModular Q' hα hKfg hK) hrk
  have hiso : IsometricLat Q Q' L K ↔ IsometricLat (α⁻¹ • Q) (α⁻¹ • Q') L K := by
    constructor
    · rintro ⟨f, hf⟩; exact ⟨f, fun x => by simp [hf x]⟩
    · rintro ⟨f, hf⟩
      refine ⟨f, fun x => ?_⟩
      have := hf x
      simp only [QuadraticMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hα' this
  have hdisc : SameDisc Q Q' L K ↔ SameDisc (α⁻¹ • Q) (α⁻¹ • Q') L K := by
    constructor
    · rintro ⟨b, b', ε, hε, hd⟩
      refine ⟨b, b', ε, hε, ?_⟩
      have hp : (α⁻¹) ^ finrank R L = (α⁻¹) ^ finrank R K := by rw [hrk]
      rw [gram_smul, gram_smul, Matrix.det_smul, Matrix.det_smul, hd, Fintype.card_fin, Fintype.card_fin,
        hp]
      ring
    · rintro ⟨b, b', ε, hε, hd⟩
      refine ⟨b, b', ε, hε, ?_⟩
      have hp' : (α⁻¹) ^ finrank R L = (α⁻¹) ^ finrank R K := by rw [hrk]
      rw [gram_smul, gram_smul, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, Fintype.card_fin,
        hp'] at hd
      have hp : (α⁻¹) ^ finrank R K ≠ 0 := pow_ne_zero _ hα'
      apply mul_left_cancel₀ hp
      linear_combination hd
  rw [hiso, hdisc, key]

end LocalNonDyadic

end QuadFormsKB.OMeara
