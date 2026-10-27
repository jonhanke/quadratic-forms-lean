/-
# O'Meara §92: values of unimodular lattices and symmetries of lattices (92:1b, 92:6)

**Setting** (as in `Sec92.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves**
* `exists_mem_Q_eq_unit` (**92:1b**, first part, p. 247): a unimodular lattice of rank $\ge 2$ represents every
  unit, $Q(L) \supseteq \mathfrak u$;
* `exists_mem_Q_eq` (**92:1b**, second part): a unimodular lattice of rank $\ge 3$ represents every element of
  $\mathfrak o$, so $Q(L) = \mathfrak o$;
* `symmetry_mem_orthLat_iff_splits` (**92:6**, p. 249): for a maximal anisotropic vector $y$ of $L$,
  $\tau_y \in O(L)$ if and only if $\mathfrak oy$ splits $L$.
-/
import QuadFormsKB.Literature.OMeara.Sec92

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section NonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Example 92:6** (O'Meara 1963, p. 249): over a non-dyadic field, for a maximal anisotropic vector $y$ of the
lattice $L$, the symmetry $\tau_y$ is a unit of $L$ if and only if $\mathfrak oy$ splits $L$ (the criterion of §91B
and 82:15, since $\mathfrak oy$ is $Q(y)$-modular). -/
@[kb "omeara1963" "§92, 92:6, p. 249"]
theorem symmetry_mem_orthLat_iff_splits (h2 : IsUnit (2 : R)) {L : Submodule R V} {y : V} (hy : Q y ≠ 0)
    (hmax : IsMaxVec F L y) :
    symmetry Q y hy ∈ orthLat Q L ↔ ∃ K, IsOrthSum Q L (R ∙ y) K := by
  let v : Fin 1 → V := fun _ => y
  have hG : gram Q v = Q y • (1 : Matrix (Fin 1) (Fin 1) R).map (algebraMap R F) := by
    ext i j; fin_cases i; fin_cases j; simp [v, gram]
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hy (by simp) hG
  have hJ : span R (Set.range v) = R ∙ y := by simp [v, Set.range_const]
  rw [hJ] at hmod
  have hJL : R ∙ y ≤ L := (span_singleton_le_iff_mem _ _).mpr hmax.1
  rw [symmetry_mem_orthLat_iff Q hy hmax, splits_iff_of_isModular Q hJL hmod (fg_span_singleton y)]
  obtain ⟨u, hu⟩ := h2
  have h2c : ∀ c : F, 2 * c ∈ R ∙ Q y → c ∈ R ∙ Q y := by
    intro c hc
    have : c = (↑u⁻¹ : R) • (2 * c) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap R F) 2, ← hu, ← map_mul, Units.inv_mul,
        map_one, one_mul]
    rw [this]; exact smul_mem _ _ hc
  have h2c' : ∀ c : F, c ∈ R ∙ Q y → 2 * c ∈ R ∙ Q y := by
    intro c hc
    have : 2 * c = (u : R) • c := by
      rw [Algebra.smul_def, hu, map_ofNat]
    rw [this]; exact smul_mem _ _ hc
  constructor
  · intro h x hx z hz
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hx
    rw [bil_rsmul_left]
    exact (R ∙ Q y).smul_mem r (h2c _ (h z hz)) |> fun h' => by simpa [Algebra.smul_def] using h'
  · intro h z hz
    exact h2c' _ (h y (mem_span_singleton_self y) z hz)

end NonDyadic

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Helper: orthogonal vectors of a unimodular lattice of rank at least $k$, with unit values. -/
theorem exists_orth_units (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L)
    {k : ℕ} (hk : k ≤ finrank R L) :
    ∃ (x : Fin k → V) (a : Fin k → R), (∀ i, x i ∈ L) ∧ (∀ i, IsUnit (a i)) ∧
      (∀ i, Q (x i) = algebraMap R F (a i)) ∧ ∀ i j, i ≠ j → bil Q (x i) (x j) = 0 := by
  obtain ⟨ε, hε, b, hb⟩ := exists_basis_diag_of_isUnimodular Q h2 hfg hL
  refine ⟨fun i => (b (Fin.castLE hk i) : V),
    fun i => if (Fin.castLE hk i).val + 1 = finrank R L then ε else 1, fun i => (b _).2,
    fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · dsimp only; split_ifs
    · exact hε
    · exact isUnit_one
  · rw [← bil_self, hb]; simp only [if_true]; split_ifs <;> simp
  · rw [hb]; simp only [if_neg (fun h => hij (Fin.castLE_injective hk h))]

/-- Helper: a binary orthogonal pair with unit values represents every unit. -/
theorem exists_binary_rep (h2 : IsUnit (2 : R)) {x₀ x₁ : V} {a₀ a₁ δ : R} (h0 : IsUnit a₀) (h1 : IsUnit a₁)
    (hδ : IsUnit δ) (hQ0 : Q x₀ = algebraMap R F a₀) (hQ1 : Q x₁ = algebraMap R F a₁)
    (horth : bil Q x₀ x₁ = 0) : ∃ s t : R, Q (s • x₀ + t • x₁) = algebraMap R F δ := by
  obtain ⟨s, t, hst⟩ := exists_binary_one (F := F) h2 (h0.mul (hδ.unit⁻¹).isUnit) (h1.mul (hδ.unit⁻¹).isUnit)
  refine ⟨s, t, ?_⟩
  rw [Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, horth, hQ0, hQ1]
  have h := congrArg (fun z => δ * z) hst
  simp only [mul_one] at h
  have h' : a₀ * s ^ 2 + a₁ * t ^ 2 = δ := by
    rw [← h]; simp only [mul_add]
    have : δ * (a₀ * ↑(hδ.unit⁻¹) * s ^ 2) = a₀ * s ^ 2 * (δ * ↑(hδ.unit⁻¹)) := by ring
    have h3 : δ * (a₁ * ↑(hδ.unit⁻¹) * t ^ 2) = a₁ * t ^ 2 * (δ * ↑(hδ.unit⁻¹)) := by ring
    have hh : δ * ↑(hδ.unit⁻¹) = 1 := by
      have := hδ.unit.mul_inv; simpa using this
    rw [this, h3, hh]; ring
  rw [← h']
  simp only [map_add, map_mul, map_pow, smul_eq_mul, Algebra.smul_def]
  ring

/-- **92:1b, first part** (O'Meara 1963, p. 247): a unimodular lattice $L$ of rank at least $2$ over a non-dyadic
local field represents every unit: $Q(L) \supseteq \mathfrak u$. -/
@[kb "omeara1963" "§92, 92:1b, p. 247 (Q(L) ⊇ u if dim L ≥ 2)"]
theorem exists_mem_Q_eq_unit (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L)
    (hrk : 2 ≤ finrank R L) {δ : R} (hδ : IsUnit δ) : ∃ x ∈ L, Q x = algebraMap R F δ := by
  obtain ⟨x, a, hxL, ha, hQ, ho⟩ := exists_orth_units Q h2 hfg hL hrk
  obtain ⟨s, t, hst⟩ := exists_binary_rep Q h2 (ha 0) (ha 1) hδ (hQ 0) (hQ 1) (ho 0 1 (by simp))
  exact ⟨_, add_mem (L.smul_mem s (hxL 0)) (L.smul_mem t (hxL 1)), hst⟩

/-- **92:1b, second part** (O'Meara 1963, p. 247): a unimodular lattice $L$ of rank at least $3$ over a non-dyadic
local field has $Q(L) = \mathfrak o$: every element of $\mathfrak o$ is a value, and every value lies in
$\mathfrak o$. -/
@[kb "omeara1963" "§92, 92:1b, p. 247 (Q(L) = o if dim L ≥ 3)"]
theorem exists_mem_Q_eq (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L)
    (hrk : 3 ≤ finrank R L) :
    (∀ c : R, ∃ x ∈ L, Q x = algebraMap R F c) ∧ ∀ x ∈ L, ∃ c : R, Q x = algebraMap R F c := by
  refine ⟨fun c => ?_, fun x hx => ?_⟩
  · by_cases hc : IsUnit c
    · exact exists_mem_Q_eq_unit Q h2 hfg hL (by omega) hc
    obtain ⟨x, a, hxL, ha, hQ, ho⟩ := exists_orth_units Q h2 hfg hL hrk
    have hca : IsUnit (c - a 2) := by
      by_contra hn
      have h1 : c ∈ nonunits R := hc
      have h2' : -(c - a 2) ∈ nonunits R := fun h => hn (by simpa using h.neg)
      have := IsLocalRing.nonunits_add h1 h2'
      exact this (by simpa using ha 2)
    obtain ⟨s, t, hst⟩ := exists_binary_rep Q h2 (ha 0) (ha 1) hca (hQ 0) (hQ 1) (ho 0 1 (by simp))
    refine ⟨s • x 0 + t • x 1 + x 2, add_mem (add_mem (L.smul_mem s (hxL 0)) (L.smul_mem t (hxL 1))) (hxL 2), ?_⟩
    have hb : bil Q (s • x 0 + t • x 1) (x 2) = 0 := by
      rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, ho 0 2 (by simp), ho 1 2 (by simp)]; simp
    rw [Q_add, hb, hst, hQ 2]
    simp only [map_sub]; ring
  · have h1 := (normIdeal_le_scale Q L) (Q_mem_normIdeal Q hx)
    rw [hL.2.1] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp h1
    exact ⟨c, hc.symm⟩

end LocalNonDyadic

end QuadFormsKB.OMeara
