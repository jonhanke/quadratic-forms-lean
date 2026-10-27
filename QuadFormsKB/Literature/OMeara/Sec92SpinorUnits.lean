/-
# O'Meara §92: the spinor norms of $O^+(L)$ for a modular lattice are units (92:5, the inclusion $\subseteq$)

**Setting** (as in `Sec92Spinor.lean`): $R$ a discrete valuation ring with fraction field $F$, $2$ a unit of $R$
(non-dyadic), a finite-dimensional regular quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves**
* `exists_bil_unit_of_isMaxVec` (82:17, one direction, p. 233): if $L$ is $\alpha$-modular and $x$ is maximal in $L$,
  then $B(x, L) = \alpha\mathfrak o$;
* `exists_hasSpinorNorm_unit` (**92:5**, the inclusion $\theta(O^+(L)) \subseteq \mathfrak uF^{\times 2}$, p. 249): every
  $\sigma \in O^+(L)$, $L$ modular on $V$, is a product of symmetries $\tau_{x_1}\cdots\tau_{x_r}$ with
  $Q(x_1)\cdots Q(x_r) \in \mathfrak uF^{\times 2}$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Spinor
import QuadFormsKB.Literature.OMeara.Sec92Sym
import QuadFormsKB.Literature.OMeara.Sec91MaxA

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Proposition 82:17, one direction** (O'Meara 1963, p. 233): if $L$ is $\alpha$-modular and $x$ is a maximal vector
of $L$, then $B(x, z)\mathfrak o = \alpha\mathfrak o$ for some $z \in L$ (so $B(x, L) = \alpha\mathfrak o$). -/
@[kb "omeara1963" "§82G, 82:17, p. 233 (B(x, L) = a for maximal x in an a-modular L)"]
theorem exists_bil_unit_of_isMaxVec {α : F} {L : Submodule R V} (hfg : L.FG) (hL : IsModular Q (R ∙ α) L)
    {x : V} (hx : IsMaxVec F L x) : ∃ z ∈ L, R ∙ bil Q x z = R ∙ α := by
  have hα : α ≠ 0 := by
    rintro rfl; exact hL.1 (by simp)
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  obtain ⟨-, U, hU, hG⟩ := (isModular_iff_gram Q b hα).mp hL
  have hxL := hx.1
  obtain ⟨c, hxsum⟩ : ∃ c : Fin (finrank R L) → R, x = ∑ i, c i • (b i : V) := by
    refine ⟨fun i => b.repr ⟨x, hxL⟩ i, ?_⟩
    have := congrArg (fun y : L => (y : V)) (b.sum_repr ⟨x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hbb : ∀ i j, bil Q (b i : V) (b j : V) = α * algebraMap R F (U i j) := fun i j => by
    have := congrFun (congrFun hG i) j
    simpa only [gram, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using this
  set w : Fin (finrank R L) → R := Matrix.vecMul c U with hw
  have hbil : ∀ j, bil Q x (b j : V) = α * algebraMap R F (w j) := fun j => by
    conv_lhs => rw [hxsum]
    rw [bil_sum_left]
    simp only [bil_rsmul_left, hbb, hw, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hex : ∃ j, IsUnit (w j) := by
    by_contra hcon
    push Not at hcon
    have hwm : ∀ j, w j ∈ maximalIdeal R := fun j => (mem_maximalIdeal _).mpr (hcon j)
    have hc' : c = Matrix.vecMul w U⁻¹ := by
      rw [hw, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv U hU, Matrix.vecMul_one]
    have hcm : ∀ i, c i ∈ maximalIdeal R := fun i => by
      rw [hc']
      simp only [Matrix.vecMul, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hwm j)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    have hcs : ∀ i, ∃ d : R, d * ϖ = c i := fun i => by
      have := hcm i
      rw [hmax] at this
      exact Ideal.mem_span_singleton'.mp this
    choose c' hc' using hcs
    have hϖ0 : algebraMap R F ϖ ≠ 0 := fun h =>
      hϖ.ne_zero (IsFractionRing.injective R F (h.trans (map_zero _).symm))
    have hxy : x = ϖ • ∑ i, c' i • (b i : V) := by
      conv_lhs => rw [hxsum]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm, hc']
    have hyL : ∑ i, c' i • (b i : V) ∈ L := L.sum_mem fun i _ => L.smul_mem _ (b i).2
    have hmem : (algebraMap R F ϖ)⁻¹ • x ∈ L := by
      have : (algebraMap R F ϖ)⁻¹ • x = ∑ i, c' i • (b i : V) := by
        rw [hxy, ← algebraMap_smul F ϖ, smul_smul, inv_mul_cancel₀ hϖ0, one_smul]
      rw [this]; exact hyL
    obtain ⟨s, hs⟩ := hx.2 _ hmem
    have h1 : algebraMap R F (s * ϖ) = algebraMap R F 1 := by
      rw [map_mul, map_one, hs]; exact inv_mul_cancel₀ hϖ0
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one_right s (IsFractionRing.injective R F h1))
  obtain ⟨j, hj⟩ := hex
  refine ⟨b j, (b j).2, ?_⟩
  rw [hbil j]
  obtain ⟨v, hv⟩ := hj.exists_right_inv
  apply le_antisymm
  · rw [span_singleton_le_iff_mem]
    exact mem_span_singleton.mpr ⟨w j, by rw [Algebra.smul_def]; ring⟩
  · rw [span_singleton_le_iff_mem]
    refine mem_span_singleton.mpr ⟨v, ?_⟩
    have := congrArg (algebraMap R F) hv
    rw [map_mul, map_one] at this
    rw [Algebra.smul_def]
    linear_combination α * this

/-- The symmetry of a vector depends only on its line. -/
theorem symmetry_smul_eq' {y : V} {t : F} (ht : t ≠ 0) (hy : Q y ≠ 0) (hu : Q (t • y) ≠ 0) :
    symmetry Q (t • y) hu = symmetry Q y hy := by
  ext x
  rw [symmetry_apply, symmetry_apply, Q_smul, bil_smul_right, smul_smul]
  have : 2 * (t * bil Q x y) / (t ^ 2 * Q y) * t = 2 * bil Q x y / Q y := by
    field_simp
  rw [this]

/-- Helper for 92:5: a vector whose symmetry lies in $O(L)$, $L$ being $\alpha$-modular, has
$Q(u) = t^2 \alpha \varepsilon$ with $t \in F^\times$ and $\varepsilon \in \mathfrak u$. -/
theorem exists_Q_eq_of_symmetry_mem (h2 : IsUnit (2 : R)) {α : F} {L : Submodule R V}
    (hL : L.IsLattice F) (hmod : IsModular Q (R ∙ α) L) {u : V} (hu : Q u ≠ 0)
    (hτ : symmetry Q u hu ∈ orthLat Q L) :
    ∃ t : F, t ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧ Q u = t ^ 2 * α * algebraMap R F ε := by
  have hfg := hL.fg
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (map_zero Q)
  have huL : u ∈ span F (L : Set V) := by rw [hL.span_eq_top]; exact mem_top
  obtain ⟨y, hy, t, ht, rfl⟩ := exists_isMaxVec_smul hfg hu0 huL
  have hQy : Q y ≠ 0 := by
    intro h; apply hu; rw [Q_smul, h, mul_zero]
  rw [symmetry_smul_eq' Q ht hQy hu] at hτ
  have hcrit := (symmetry_mem_orthLat_iff Q hQy hy).mp hτ
  obtain ⟨z, hz, hzspan⟩ := exists_bil_unit_of_isMaxVec Q hfg hmod hy
  obtain ⟨s, hs⟩ := mem_span_singleton.mp (hcrit z hz)
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (hzspan ▸ mem_span_singleton_self α : α ∈ R ∙ bil Q y z)
  obtain ⟨w, hw⟩ := h2
  have hw2 : algebraMap R F ((w⁻¹ : Rˣ) : R) * 2 = 1 := by
    have := congrArg (algebraMap R F) (w.inv_mul)
    rw [map_mul, map_one, hw, map_ofNat] at this
    exact this
  have hαQ : ∃ q : R, α = algebraMap R F q * Q y := by
    refine ⟨r * ((w⁻¹ : Rˣ) : R) * s, ?_⟩
    rw [← hr, Algebra.smul_def]
    rw [Algebra.smul_def] at hs
    simp only [map_mul]
    linear_combination (-(algebraMap R F r * algebraMap R F ((w⁻¹ : Rˣ) : R))) * hs +
      (-(algebraMap R F r * bil Q y z)) * hw2
  obtain ⟨q, hq⟩ := hαQ
  have hQs : Q y ∈ R ∙ α := by
    have h1 := (normIdeal_le_scale Q L) (Q_mem_normIdeal Q hy.1)
    rwa [hmod.2.1] at h1
  obtain ⟨e, he⟩ := mem_span_singleton.mp hQs
  rw [Algebra.smul_def] at he
  refine ⟨t, ht, e, ?_, ?_⟩
  · have h1 : algebraMap R F (e * q) = algebraMap R F 1 := by
      rw [map_mul, map_one]
      apply mul_right_cancel₀ hQy
      linear_combination (-(algebraMap R F e)) * hq + he
    exact IsUnit.of_mul_eq_one _ (IsFractionRing.injective R F h1)
  · rw [Q_smul, ← he]; ring

/-- Helper for 92:5: the product of the values over a list. -/
theorem prod_Q_of_forall {α : F} (l : List V)
    (h : ∀ u ∈ l, ∃ t : F, t ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧ Q u = t ^ 2 * α * algebraMap R F ε) :
    ∃ t : F, t ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧
      (l.map Q).prod = t ^ 2 * α ^ l.length * algebraMap R F ε := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, 1, isUnit_one, by simp⟩
  | cons u l ih =>
    obtain ⟨t1, ht1, ε1, hε1, hu1⟩ := h u (by simp)
    obtain ⟨t2, ht2, ε2, hε2, h2⟩ := ih fun v hv => h v (by simp [hv])
    refine ⟨t1 * t2, mul_ne_zero ht1 ht2, ε1 * ε2, hε1.mul hε2, ?_⟩
    rw [List.map_cons, List.prod_cons, hu1, h2, List.length_cons, map_mul]
    ring

/-- Helper for 92:5: the determinant of a product of symmetries. -/
theorem det_symmetryOrOne_prod [FiniteDimensional F V] (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) :
    LinearEquiv.det (l.map (symmetryOrOne Q)).prod = (-1 : Fˣ) ^ l.length := by
  induction l with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih fun v hv => hl v (by simp [hv]),
      sym4_symmetryOrOne_of_ne Q (hl u (by simp)), det_symmetry, List.length_cons, pow_succ']

/-- **Proposition 92:5, the inclusion $\theta(O^+(L)) \subseteq \mathfrak uF^{\times 2}$** (O'Meara 1963, p. 249): for a
modular lattice $L$ on a regular quadratic space over a non-dyadic local field, every rotation $\sigma \in O^+(L)$ is a
product of symmetries $\tau_{x_1}\cdots\tau_{x_r}$ (each in $O(L)$) with $Q(x_1)\cdots Q(x_r) \in \mathfrak uF^{\times 2}$.
(O'Meara's proof: a symmetry in $O(L)$ is $\tau_y$ with $y$ maximal, and $B(y, L) \subseteq Q(y)\mathfrak o$ forces
$Q(y) \in \alpha\mathfrak u$; then use 92:4.) -/
@[kb "omeara1963" "§92, 92:5, p. 249 (θ(O⁺(L)) ⊆ uF²)"]
theorem exists_hasSpinorNorm_unit (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 ≤ finrank F V) {a : Submodule R F}
    {L : Submodule R V} (hL : L.IsLattice F) (hmod : IsModular Q a L) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orthLatPlus Q L) : ∃ ε : R, IsUnit ε ∧ HasSpinorNorm Q σ (algebraMap R F ε) := by
  have hfg := hL.fg
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton (R := R) (hmod.2.1 ▸ scale_fg Q hfg) hmod.1
  obtain ⟨l, -, hl, hσl⟩ := exists_symmetry_list Q h2 hV hn hL hσ.1
  have hQl : ∀ u ∈ l, Q u ≠ 0 := fun u hu => (hl u hu).1
  have hnorm : ∀ u ∈ l, ∃ t : F, t ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧
      Q u = t ^ 2 * α * algebraMap R F ε := fun u hu => by
    obtain ⟨hu', hτ⟩ := hl u hu
    exact exists_Q_eq_of_symmetry_mem Q h2 hL hmod hu' hτ
  obtain ⟨t, ht, ε, hε, hprod⟩ := prod_Q_of_forall Q l hnorm
  have hdet : LinearEquiv.det σ = 1 := MonoidHom.mem_ker.mp hσ.2.2
  rw [hσl, det_symmetryOrOne_prod Q l hQl] at hdet
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    have h' : (-1 : F) = 1 := congrArg Units.val h
    have h2F : (2 : F) = 0 := by linear_combination -h'
    exact (isUnit_of_invertible (2 : F)).ne_zero h2F
  obtain ⟨m, hm⟩ := (neg_one_pow_eq_one_iff_even hne).mp hdet
  refine ⟨ε, hε, l, hQl, ?_, t * α ^ m, mul_ne_zero ht (pow_ne_zero _ hα), ?_⟩
  · rw [hσl]
    congr 1
    have : (l.attach.map fun u => symmetry Q u.1 (hQl u.1 u.2)) =
        l.attach.map fun u => symmetryOrOne Q u.1 :=
      List.map_congr_left fun u _ => (sym4_symmetryOrOne_of_ne Q _).symm
    rw [this]
    simp
  · rw [hprod, hm]; ring

end DVR

end QuadFormsKB.OMeara
