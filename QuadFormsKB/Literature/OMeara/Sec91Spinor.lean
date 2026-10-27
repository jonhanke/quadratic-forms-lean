/-
# O'Meara §91B: spinor norms of maximal lattices (Proposition 91:8, isotropic case)

**Setting** (as in `Sec91MaxA.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
finite-dimensional regular quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`; spinor norms through a
factorization into symmetries (`HasSpinorNorm`, see `Sec92Spinor.lean`).

**Proves** `exists_hasSpinorNorm_of_isMaximal_isotropic` (**91:8**, p. 243, the case of an isotropic space): if $L$ is
an $\mathfrak a$-maximal lattice on an isotropic regular space, every unit $\varepsilon$ is the spinor norm of a rotation
in $O^+(L)$. O'Meara's proof: $L$ splits off $\mathfrak ox + \mathfrak oy$ with $Q(x) = Q(y) = 0$, $B(x, y) = \gamma$,
$\mathfrak a = 2\gamma\mathfrak o$ (82:20), and $\tau_{x + \varepsilon y}\tau_{x + y} \in O^+(L)$ has spinor norm
$4\varepsilon\gamma^2 \in \varepsilon F^{\times 2}$. The anisotropic case of 91:8 uses 91:6 (and 63:18) and is not
formalized.
-/
import QuadFormsKB.Literature.OMeara.Sec91MaxA
import QuadFormsKB.Literature.OMeara.Sec92Spinor

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Proposition 91:8, isotropic case** (O'Meara 1963, p. 243): if $L$ is an $\mathfrak a$-maximal lattice on a regular
isotropic quadratic space $V$, then $\theta(O^+(L)) \supseteq \mathfrak u$: every unit $\varepsilon$ is the spinor norm of
some $\sigma \in O^+(L)$. (O'Meara assumes $\dim V \ge 3$, which is needed only in the anisotropic case.) -/
@[kb "omeara1963" "§91B, 91:8, p. 243 (isotropic case)"]
theorem exists_hasSpinorNorm_of_isMaximal_isotropic [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} {L : Submodule R V}
    (hL : IsMaximal Q a L) {w : V} (hw0 : w ≠ 0) (hQw : Q w = 0) {ε : R} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  have hL' := (isMaxIn_top_iff Q).mpr hL
  have hreg : ∀ v ∈ (⊤ : Submodule F V), (∀ v' ∈ (⊤ : Submodule F V), bil Q v v' = 0) → v = 0 :=
    fun v _ h => hV.1 v fun v' => h v' trivial
  -- an isotropic vector of `L`
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have hwL : w ∈ span F (L : Set V) := by rw [hL.1.span_eq_top]; trivial
  obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (R := R) hwL
  obtain ⟨x, hx, y, hy, γ, hγ, haγ, hQx, hQy, hxy, -⟩ :=
    exists_hyperbolic_split_of_isMaxIn Q hreg hL' hdw (smul_ne_zero hd hw0) (by rw [Q_rsmul, hQw, mul_zero])
  -- `B(L, L) ⊆ γ o`
  have hsL : ∀ z ∈ L, ∀ z' ∈ L, bil Q z z' ∈ R ∙ γ := by
    intro z hz z' hz'
    have h2 := two_mul_mem_normIdeal Q (bil_mem_scale Q hz hz')
    have h3 : 2 * bil Q z z' ∈ R ∙ (2 * γ) := haγ ▸ hL.2.1 h2
    obtain ⟨c, hc⟩ := mem_span_singleton.mp h3
    refine mem_span_singleton.mpr ⟨c, ?_⟩
    have h2' : (2 : F) ≠ 0 := two_ne_zero
    rw [Algebra.smul_def] at hc ⊢
    apply mul_left_cancel₀ h2'
    linear_combination hc
  have hεF : algebraMap R F ε ≠ 0 := fun h => hε.ne_zero
    ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  -- the vectors `x + t y` with `t = ε, 1`
  have hQv : ∀ t : R, Q (x + t • y) = 2 * algebraMap R F t * γ := by
    intro t; rw [Q_add, Q_rsmul, hQx, hQy, bil_rsmul_right, hxy]; ring
  have hmem : ∀ t : R, IsUnit t → ∃ h : Q (x + t • y) ≠ 0, symmetry Q (x + t • y) h ∈ orthLat Q L := by
    intro t ht
    have htF : algebraMap R F t ≠ 0 := fun h => ht.ne_zero
      ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
    have h0 : Q (x + t • y) ≠ 0 := by
      rw [hQv]; exact mul_ne_zero (mul_ne_zero two_ne_zero htF) hγ
    refine ⟨h0, symmetry_mem_orthLat_of_le Q h0 fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (hsL _ (L.add_mem hx (L.smul_mem t hy)) z hz)
    obtain ⟨u, hu⟩ := ht
    rw [symmetry_apply]
    have : (2 * bil Q z (x + t • y) / Q (x + t • y)) • (x + t • y) = (c * ↑u⁻¹) • (x + t • y) := by
      rw [← algebraMap_smul F (c * ↑u⁻¹) (x + t • y)]
      congr 1
      have hu0 : algebraMap R F (u : R) ≠ 0 := by rw [hu]; exact htF
      rw [bil_comm, ← hc, hQv, Algebra.smul_def, ← hu, map_mul, map_units_inv (algebraMap R F)]
      field_simp
    rw [this]
    exact L.sub_mem hz (L.smul_mem _ (L.add_mem hx (L.smul_mem t hy)))
  obtain ⟨h1, hτ1⟩ := hmem ε hε
  obtain ⟨h2, hτ2⟩ := hmem 1 isUnit_one
  refine ⟨symmetry Q _ h1 * symmetry Q _ h2, ⟨(orthLat Q L).mul_mem hτ1 hτ2,
    symmetry_mul_mem_orthPlus Q h1 h2⟩, ?_⟩
  obtain ⟨l, hl, hσ, s, hs0, hprod⟩ := hasSpinorNorm_symmetry_mul Q h1 h2
  refine ⟨l, hl, hσ, 2 * γ * s, mul_ne_zero (mul_ne_zero two_ne_zero hγ) hs0, ?_⟩
  rw [hprod, hQv, hQv, map_one]; ring

end DVR

end QuadFormsKB.OMeara
