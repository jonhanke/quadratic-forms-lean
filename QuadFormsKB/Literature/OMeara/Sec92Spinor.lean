/-
# O'Meara §92: spinor norms of units of lattices over non-dyadic local fields (92:5, 92:9)

**Setting** (as in `Sec92.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), fraction field $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Spinor norms.** O'Meara's spinor norm $\theta : O^+(V) \to F^\times/F^{\times 2}$ (§55, p. 137) sends
$\tau_{x_1}\cdots\tau_{x_r}$ to $Q(x_1)\cdots Q(x_r)F^{\times 2}$; that this is independent of the factorization is
O'Meara's 55:1 (Chapter V), proved in this library only in coordinates over a number field
(`Lattices.isSquare_valProd_of_symmProd_eq_one`). Here `HasSpinorNorm Q σ c` says that $\sigma$ has *some*
factorization $\sigma = \tau_{x_1}\cdots\tau_{x_r}$ with $Q(x_1)\cdots Q(x_r) \in cF^{\times 2}$; by 55:1 this is
$\theta(\sigma) = cF^{\times 2}$. The statements below that assert $c \in \theta(O^+(L))$ are of this existential form and
do not use 55:1.

**Proves**
* `exists_hasSpinorNorm_of_isModular` (**92:5**, the inclusion $\theta(O^+(L)) \supseteq \mathfrak uF^{\times 2}$): for a
  modular lattice $L$ of rank $\ge 2$ over a non-dyadic local field, every unit is the spinor norm of a rotation in
  $O^+(L)$;
* `exists_hasSpinorNorm_of_volume` (**92:9**): if $\mathfrak sL \subseteq \mathfrak o$ and
  $\mathfrak vL \supsetneq \mathfrak p^{n(n-1)/2}$ for a lattice $L$ on an $n$-ary space, then
  $\theta(O^+(L)) \supseteq \mathfrak u$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Rep
import QuadFormsKB.Literature.OMeara.Sec92Class
import QuadFormsKB.Literature.OMeara.Sec91Units

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$\sigma$ has spinor norm $cF^{\times 2}$** (O'Meara 1963, §55A, p. 137, through a factorization):
$\sigma = \tau_{x_1}\cdots\tau_{x_r}$ with all $Q(x_i) \ne 0$ and $Q(x_1)\cdots Q(x_r) = c s^2$ for some
$s \in F^\times$. By O'Meara's 55:1 (not used here) this does not depend on the factorization. -/
@[kb "omeara1963" "§55A, p. 137 (spinor norm θ(τ_{x₁}⋯τ_{x_r}) = Q(x₁)⋯Q(x_r)F²)"]
def HasSpinorNorm (σ : V ≃ₗ[F] V) (c : F) : Prop :=
  ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
    σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧
      ∃ s : F, s ≠ 0 ∧ (l.map Q).prod = c * s ^ 2

/-- A product of two symmetries $\tau_x\tau_y$ has spinor norm $Q(x)Q(y)$. -/
theorem hasSpinorNorm_symmetry_mul {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
    HasSpinorNorm Q (symmetry Q x hx * symmetry Q y hy) (Q x * Q y) := by
  refine ⟨[x, y], fun u hu => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hx
    · exact hy, ?_, 1, one_ne_zero, by simp⟩
  simp [List.attach, List.attachWith]

end Defs

section Symm

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- A product of two symmetries is a rotation. -/
theorem symmetry_mul_mem_orthPlus {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
    symmetry Q x hx * symmetry Q y hy ∈ orthPlus Q := by
  refine ⟨(orth Q).mul_mem (symmetry_mem_orth Q hx) (symmetry_mem_orth Q hy), ?_⟩
  refine (MonoidHom.mem_ker).mpr ?_
  rw [map_mul, det_symmetry, det_symmetry]
  simp

end Symm

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- If $J \subseteq L$ is a component, $L = J \perp K$, $x \in J$ and $2B(x, J) \subseteq Q(x)\mathfrak o$, then
$\tau_x \in O(L)$. -/
theorem symmetry_mem_orthLat_of_component {L J K : Submodule R V} (hs : IsOrthSum Q L J K) {x : V}
    (hxJ : x ∈ J) (hx : Q x ≠ 0) (hJ : ∀ z ∈ J, 2 * bil Q z x ∈ R ∙ Q x) :
    symmetry Q x hx ∈ orthLat Q L := by
  refine symmetry_mem_orthLat_of_le Q hx fun z hz => ?_
  rw [← hs.sup_eq] at hz ⊢
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := mem_sup.mp hz
  have h0 : bil Q z₂ x = 0 := by rw [bil_comm]; exact hs.orth x hxJ z₂ hz₂
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (hJ z₁ hz₁)
  rw [symmetry_apply, bil_add_left, h0, add_zero]
  have : (2 * bil Q z₁ x / Q x) • x = r • x := by
    rw [← algebraMap_smul F r x]
    congr 1
    rw [← hr, Algebra.smul_def]; field_simp
  rw [this]
  exact sub_mem (add_mem (mem_sup_left hz₁) (mem_sup_right hz₂)) (mem_sup_left (J.smul_mem r hxJ))

/-- **The rotations needed for 92:5 and 92:9**: if $L = J \perp K$ with $J$ an $\alpha$-modular lattice of rank at
least $2$ over a non-dyadic local field, then for every unit $\varepsilon$ there is a rotation $\sigma \in O^+(L)$
with spinor norm $\varepsilon$, namely $\sigma = \tau_x\tau_y$ with $x, y \in J$, $Q(x) = \alpha\varepsilon$,
$Q(y) = \alpha$ (92:1b applied to the scaled form $\alpha^{-1}Q$). -/
theorem exists_hasSpinorNorm_of_component [FiniteDimensional F V] (h2 : IsUnit (2 : R))
    {L J K : Submodule R V} (hs : IsOrthSum Q L J K) {α : F} (hα : α ≠ 0) (hJfg : J.FG)
    (hJ : IsModular Q (R ∙ α) J) (hrk : 2 ≤ finrank R J) {ε : R} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  have hU := isUnimodular_smul_of_isModular Q hα hJfg hJ
  obtain ⟨x, hxJ, hQx⟩ := exists_mem_Q_eq_unit (α⁻¹ • Q) h2 hJfg hU hrk hε
  obtain ⟨y, hyJ, hQy⟩ := exists_mem_Q_eq_unit (α⁻¹ • Q) h2 hJfg hU hrk isUnit_one
  simp only [QuadraticMap.smul_apply, smul_eq_mul, map_one] at hQx hQy
  have hQx' : Q x = α * algebraMap R F ε := by
    rw [← hQx]; field_simp
  have hQy' : Q y = α := by
    rw [← mul_one α, ← hQy]; field_simp
  have hεF : algebraMap R F ε ≠ 0 := fun h => hε.ne_zero
    ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  have hx0 : Q x ≠ 0 := by rw [hQx']; exact mul_ne_zero hα hεF
  have hy0 : Q y ≠ 0 := by rw [hQy']; exact hα
  -- `2B(z, x) ∈ Q(x) o` for `z ∈ J`, since `B(J, J) ⊆ α o` and `Q x = α ε`
  have hcrit : ∀ v ∈ J, ∀ z ∈ J, (Q v = α * algebraMap R F ε ∨ Q v = α) → 2 * bil Q z v ∈ R ∙ Q v := by
    intro v hv z hz hQv
    have hB : bil Q z v ∈ R ∙ α := hJ.2.1 ▸ bil_mem_scale Q hz hv
    obtain ⟨c, hc⟩ := mem_span_singleton.mp hB
    obtain ⟨w, hw⟩ := hε
    rcases hQv with hQv | hQv
    · refine mem_span_singleton.mpr ⟨2 * c * ↑w⁻¹, ?_⟩
      rw [hQv, ← hc, ← hw, Algebra.smul_def, Algebra.smul_def]
      simp only [map_mul, map_ofNat]
      have : algebraMap R F (↑w⁻¹ : R) * algebraMap R F (w : R) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (2 * algebraMap R F c * α) * this
    · refine mem_span_singleton.mpr ⟨2 * c, ?_⟩
      rw [hQv, ← hc, Algebra.smul_def, Algebra.smul_def, map_mul, map_ofNat]; ring
  refine ⟨symmetry Q x hx0 * symmetry Q y hy0, ⟨(orthLat Q L).mul_mem ?_ ?_, ?_⟩, ?_⟩
  · exact symmetry_mem_orthLat_of_component Q hs hxJ hx0 fun z hz => hcrit x hxJ z hz (Or.inl hQx')
  · exact symmetry_mem_orthLat_of_component Q hs hyJ hy0 fun z hz => hcrit y hyJ z hz (Or.inr hQy')
  · exact symmetry_mul_mem_orthPlus Q hx0 hy0
  · have h := hasSpinorNorm_symmetry_mul Q hx0 hy0
    obtain ⟨l, hl, hσ, s, hs0, hprod⟩ := h
    refine ⟨l, hl, hσ, s * α, mul_ne_zero hs0 hα, ?_⟩
    rw [hprod, hQx', hQy']; ring

/-- **Proposition 92:5, the inclusion $\theta(O^+(L)) \supseteq \mathfrak uF^{\times 2}$** (O'Meara 1963, p. 249): for a
modular lattice $L$ of rank at least $2$ over a non-dyadic local field, every unit $\varepsilon$ is the spinor norm of a
rotation in $O^+(L)$. *Reconstruction:* the machine-read text has "$\dim L = 2$"; the hypothesis is $\dim L \ge 2$, as
the proof (via 92:1b) and the application in 92:9 ("$\dim L_i \ge 2$ for at least one $i$ and we can apply 92:5")
show. -/
@[kb "omeara1963" "§92, 92:5, p. 249 (θ(O⁺(L)) ⊇ u)"]
theorem exists_hasSpinorNorm_of_isModular [FiniteDimensional F V] (h2 : IsUnit (2 : R)) {a : Submodule R F}
    {L : Submodule R V} (hfg : L.FG) (hL : IsModular Q a L) (hrk : 2 ≤ finrank R L) {ε : R}
    (hε : IsUnit ε) : ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton (R := R) (hL.2.1 ▸ scale_fg Q hfg) hL.1
  exact exists_hasSpinorNorm_of_component Q h2 (K := ⊥)
    ⟨fun x _ y hy => by rw [mem_bot] at hy; simp [hy, bil], disjoint_bot_right, sup_bot_eq L⟩
    hα hfg hL hrk hε

end LocalNonDyadic

end QuadFormsKB.OMeara
