import QuadFormsKB.Tamagawa.Measure.Weil.SL2Adele

/-!
# $\mathrm{SL}_n(\mathbb A_F)$ for every $n$: topology, the discrete subgroup $\mathrm{SL}_n(F)$, fundamental domains


$F$ a number field, $\iota$ a finite index set (in the applications $\iota = $ `Fin n`, the dimension $n$). This file
generalizes `SL2Adele.lean` from $\iota = $ `Fin 2` to every $\iota$, and adds two measure-theoretic lemmas used for
the Tamagawa measure of $\mathrm{SL}_n$ (`SLnMeasure.lean`).

* `SLnA F ι` $=\mathrm{SL}_\iota(\mathbb A_F)$ with the subspace topology from $M_\iota(\mathbb A_F)$: a locally compact,
  second countable topological group with its Borel σ-algebra.
* `slnEmb`: the diagonal embedding $\mathrm{SL}_\iota(F)\to\mathrm{SL}_\iota(\mathbb A_F)$, injective, with
  **discrete** image (`discreteTopology_slnSub`).
* Weil's quotient $G_{\mathbb A}/G_k$ (Weil 1982, §2.4, p. 23): $\mathrm{SL}_\iota(F)$ acts by right translation
  $\gamma\cdot g = g\gamma^{-1}$ (`slnRightAction`); **exact measurable fundamental domains** exist
  (`exists_measurableSet_forall_existsUnique_right'`).
* **`rightInvSub`** (generic): for a σ-finite left-invariant measure $\mu$ on a group with $0<\mu(U)<\infty$ for some
  measurable $U$, the elements $g$ with $(\cdot\,g)_*\mu = \mu$ form a **normal subgroup containing every commutator**
  (`rightInvSub_normal`, `commutator_le_rightInvSub`). (Right translation by $g$ multiplies $\mu$ by a positive
  constant $c(g)$, and $c$ is a homomorphism to a commutative group.)
* **`map_involution_eq`** (generic): an involutive automorphism of the group preserves such a $\mu$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

/-! ### Generic: right translates of a left-invariant measure -/

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The set of $g$ such that right translation by $g$ preserves $\mu$. -/
def rightInvSub (μ : Measure G) : Subgroup G where
  carrier := {g | μ.map (· * g) = μ}
  one_mem' := by
    show μ.map (· * 1) = μ
    simp only [mul_one]; exact Measure.map_id
  mul_mem' := by
    intro a b ha hb
    show μ.map (· * (a * b)) = μ
    have : (fun x : G => x * (a * b)) = (fun x => x * b) ∘ (fun x => x * a) := by
      funext x; simp [mul_assoc]
    rw [this, ← Measure.map_map (measurable_mul_const b) (measurable_mul_const a)]
    rw [show μ.map (· * a) = μ from ha, show μ.map (· * b) = μ from hb]
  inv_mem' := by
    intro a ha
    show μ.map (· * a⁻¹) = μ
    have ha' : μ.map (· * a) = μ := ha
    conv_lhs => rw [← ha']
    rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have : (fun x : G => x * a⁻¹) ∘ (fun x => x * a) = id := by funext x; simp
    rw [this, Measure.map_id]

theorem mem_rightInvSub {μ : Measure G} {g : G} : g ∈ rightInvSub μ ↔ μ.map (· * g) = μ := Iff.rfl

variable (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

/-- Right translates of a left-invariant measure are left invariant. -/
instance isMulLeftInvariant_map_mul_right (g : G) : (μ.map (· * g)).IsMulLeftInvariant := by
  refine ⟨fun a => ?_⟩
  rw [Measure.map_map (measurable_const_mul a) (measurable_mul_const g)]
  have : (fun x : G => a * x) ∘ (fun x => x * g) = (fun x => x * g) ∘ (fun x => a * x) := by
    funext x; simp [mul_assoc]
  rw [this, ← Measure.map_map (measurable_mul_const g) (measurable_const_mul a), map_mul_left_eq_self]

theorem sigmaFinite_map_mul_right (g : G) : SigmaFinite (μ.map (· * g)) :=
  (MeasurableEquiv.mulRight g).sigmaFinite_map

variable {μ}

/-- $(\cdot\,g)_*\mu = c(g)\,\mu$ with $c(g) = \mu(Ug^{-1})/\mu(U)$. -/
theorem map_mul_right_eq_smul {U : Set G} (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) (g : G) :
    μ.map (· * g) = (μ.map (· * g) U / μ U) • μ := by
  have := sigmaFinite_map_mul_right μ g
  exact measure_eq_div_smul (μ.map (· * g)) μ h0 htop

/-- The scalar $c(g)$ is finite and positive. -/
theorem rightScalar_pos_finite {U : Set G} (hU : MeasurableSet U) (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) (g : G) :
    μ.map (· * g) U / μ U ≠ 0 ∧ μ.map (· * g) U / μ U ≠ ∞ := by
  set c := fun g : G => μ.map (· * g) U / μ U
  have hc : ∀ g, μ.map (· * g) = c g • μ := fun g => map_mul_right_eq_smul h0 htop g
  -- `c g * c g⁻¹ = 1`
  have hmul : c g⁻¹ * c g = 1 := by
    have e : μ = (μ.map (· * g)).map (· * g⁻¹) := by
      rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
      have : (fun x : G => x * g⁻¹) ∘ (fun x => x * g) = id := by funext x; simp
      rw [this, Measure.map_id]
    have e2 : μ = (c g * c g⁻¹) • μ := by
      conv_lhs => rw [e]
      rw [hc g, Measure.map_smul, hc g⁻¹, smul_smul]
      all_goals exact (measurable_mul_const _).aemeasurable
    have := congrArg (fun ν : Measure G => ν U) e2
    simp only [Measure.smul_apply, smul_eq_mul] at this
    have h1 : (1 : ℝ≥0∞) * μ U = (c g * c g⁻¹) * μ U := by rw [one_mul]; exact this
    rw [mul_comm]
    exact ((ENNReal.mul_left_inj h0 htop).mp h1).symm
  constructor
  · intro h
    have h' : c g = 0 := h
    rw [h', mul_zero] at hmul; exact zero_ne_one hmul
  · intro h
    have h' : c g = ∞ := h
    rw [h'] at hmul
    rcases eq_or_ne (c g⁻¹) 0 with h' | h'
    · rw [h', zero_mul] at hmul; exact zero_ne_one hmul
    · rw [ENNReal.mul_top h'] at hmul; exact ENNReal.top_ne_one hmul

/-- **Right translation multiplies a left-invariant measure by a homomorphism to $\mathbb R_{>0}$**: the scalar
$c(g)$, as a monoid homomorphism to $\mathbb R_{\ge0}^\times$. -/
def rightChar {U : Set G} (hU : MeasurableSet U) (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) : G →* ℝ≥0 where
  toFun g := (μ.map (· * g) U / μ U).toNNReal
  map_one' := by
    simp only [mul_one, Measure.map_id', ENNReal.div_self h0 htop, ENNReal.toNNReal_one]
  map_mul' a b := by
    set c := fun g : G => μ.map (· * g) U / μ U
    have hc : ∀ g, μ.map (· * g) = c g • μ := fun g => map_mul_right_eq_smul h0 htop g
    have e : μ.map (· * (a * b)) = (c a * c b) • μ := by
      have : (fun x : G => x * (a * b)) = (fun x => x * b) ∘ (fun x => x * a) := by
        funext x; simp [mul_assoc]
      rw [this, ← Measure.map_map (measurable_mul_const b) (measurable_mul_const a), hc a, Measure.map_smul,
        hc b, smul_smul, mul_comm]
      all_goals exact (measurable_mul_const _).aemeasurable
    have hab : c (a * b) = c a * c b := by
      show μ.map (· * (a * b)) U / μ U = _
      rw [e, Measure.smul_apply, smul_eq_mul, mul_div_assoc, ENNReal.div_self h0 htop, mul_one]
    show (c (a * b)).toNNReal = (c a).toNNReal * (c b).toNNReal
    rw [hab, ENNReal.toNNReal_mul]

theorem rightChar_eq_one_iff {U : Set G} (hU : MeasurableSet U) (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) (g : G) :
    rightChar hU h0 htop g = 1 ↔ g ∈ rightInvSub μ := by
  have hfin := rightScalar_pos_finite hU h0 htop g
  have hc := map_mul_right_eq_smul h0 htop g
  constructor
  · intro h
    have h' : μ.map (· * g) U / μ U = 1 := by
      have : (μ.map (· * g) U / μ U).toNNReal = 1 := h
      rw [← ENNReal.coe_toNNReal hfin.2, this, ENNReal.coe_one]
    show μ.map (· * g) = μ
    rw [hc, h', one_smul]
  · intro h
    have h' : μ.map (· * g) = μ := h
    show (μ.map (· * g) U / μ U).toNNReal = 1
    rw [h', ENNReal.div_self h0 htop, ENNReal.toNNReal_one]

/-- **The right-invariance subgroup is normal.** -/
theorem rightInvSub_normal {U : Set G} (hU : MeasurableSet U) (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) :
    (rightInvSub μ).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← rightChar_eq_one_iff hU h0 htop] at hn ⊢
  set χ := rightChar hU h0 htop
  calc χ (g * n * g⁻¹) = χ n * (χ g * χ g⁻¹) := by rw [map_mul, map_mul]; ring
    _ = 1 := by rw [hn, ← map_mul, mul_inv_cancel, map_one, mul_one]

/-- **Every commutator lies in the right-invariance subgroup.** -/
theorem commutator_le_rightInvSub {U : Set G} (hU : MeasurableSet U) (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) :
    commutator G ≤ rightInvSub μ := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← rightChar_eq_one_iff hU h0 htop, commutatorElement_def]
  set χ := rightChar hU h0 htop
  calc χ (a * b * a⁻¹ * b⁻¹) = χ (a * a⁻¹) * χ (b * b⁻¹) := by simp only [map_mul]; ring
    _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, mul_one]

/-- **An involutive automorphism preserves a σ-finite left-invariant measure** (with $0<\mu(U)<\infty$ for some
measurable $U$): $\alpha_*\mu$ is left invariant, so $\alpha_*\mu = c\mu$, and $\alpha\circ\alpha = \mathrm{id}$ forces
$c^2 = 1$. -/
theorem map_involution_eq {U : Set G} (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) (α : G →* G) (hα : Measurable α)
    (hinv : ∀ g, α (α g) = g) : μ.map α = μ := by
  have hli : (μ.map α).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    rw [Measure.map_map (measurable_const_mul a) hα]
    have : (fun x : G => a * x) ∘ α = α ∘ (fun x => α a * x) := by
      funext x; simp [map_mul, hinv]
    rw [this, ← Measure.map_map hα (measurable_const_mul _), map_mul_left_eq_self]
  have hsf : SigmaFinite (μ.map α) := by
    let e : G ≃ᵐ G := ⟨⟨α, α, hinv, hinv⟩, hα, hα⟩
    exact e.sigmaFinite_map
  have hc := measure_eq_div_smul (μ.map α) μ h0 htop
  set c := μ.map α U / μ U
  have e2 : μ = (c * c) • μ := by
    have : μ = (μ.map α).map α := by
      rw [Measure.map_map hα hα]
      have : α ∘ α = id := funext hinv
      rw [this, Measure.map_id]
    conv_lhs => rw [this]
    rw [hc, Measure.map_smul, hc, smul_smul]
    all_goals exact hα.aemeasurable
  have hcc : c * c = 1 := by
    have := congrArg (fun ν : Measure G => ν U) e2
    simp only [Measure.smul_apply, smul_eq_mul] at this
    have h1 : (1 : ℝ≥0∞) * μ U = (c * c) * μ U := by rw [one_mul]; exact this
    exact ((ENNReal.mul_left_inj h0 htop).mp h1).symm
  have hc1 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exfalso
      have : c * c < 1 := by
        calc c * c ≤ c * 1 := by gcongr
          _ = c := mul_one c
          _ < 1 := h
      rw [hcc] at this; exact lt_irrefl _ this
    · exact h
    · exfalso
      have : 1 < c * c := by
        calc (1 : ℝ≥0∞) < c := h
          _ = c * 1 := (mul_one c).symm
          _ ≤ c * c := by gcongr
      rw [hcc] at this; exact lt_irrefl _ this
  rw [hc, hc1, one_smul]

end Generic

/-! ### The group $\mathrm{SL}_\iota(\mathbb A_F)$ -/

variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

variable (F ι) in
/-- $\mathrm{SL}_\iota(\mathbb A_F)$, with the subspace topology from $M_\iota(\mathbb A_F)$. -/
abbrev SLnA : Type := Matrix.SpecialLinearGroup ι (Adeles F)

instance : LocallyCompactSpace (Matrix ι ι (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (ι → ι → Adeles F))

instance : SecondCountableTopology (Matrix ι ι (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (ι → ι → Adeles F))

instance : LocallyCompactSpace (SLnA F ι) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance : SecondCountableTopology (SLnA F ι) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance measurableSpace_SLnA : MeasurableSpace (SLnA F ι) :=
  inferInstanceAs (MeasurableSpace {A : Matrix ι ι (Adeles F) // A.det = 1})

instance : BorelSpace (SLnA F ι) :=
  inferInstanceAs (BorelSpace {A : Matrix ι ι (Adeles F) // A.det = 1})

theorem measurableEmbedding_SLnA_val :
    MeasurableEmbedding (Subtype.val : SLnA F ι → Matrix ι ι (Adeles F)) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.measurableEmbedding

/-- A map into $\mathrm{SL}_\iota(\mathbb A_F)$ is measurable iff its entries are. -/
theorem measurable_SLnA_iff {X : Type*} [MeasurableSpace X] {f : X → SLnA F ι} :
    Measurable f ↔ ∀ i j, Measurable fun x => (f x : Matrix ι ι (Adeles F)) i j := by
  refine ⟨fun h i j => ?_, fun h => ?_⟩
  · exact (measurableEmbedding_SLnA_val.measurable.comp h).eval_matrix
  · exact measurableEmbedding_SLnA_val.measurable_comp_iff.mp (Measurable.of_eval_matrix _ h)

theorem measurable_SLnA_entry (i j : ι) :
    Measurable fun g : SLnA F ι => (g : Matrix ι ι (Adeles F)) i j :=
  measurable_SLnA_iff.mp measurable_id i j

instance : MeasurableMul₂ (SLnA F ι) := ContinuousMul.measurableMul₂
instance : MeasurableInv (SLnA F ι) := ContinuousInv.measurableInv
instance : MeasurableMul (SLnA F ι) := inferInstance

/-! ### The discrete subgroup $\mathrm{SL}_\iota(F)$ -/

instance : Countable (Matrix ι ι F) := inferInstanceAs (Countable (ι → ι → F))

instance : Countable (Matrix.SpecialLinearGroup ι F) :=
  Function.Injective.countable (f := fun g : Matrix.SpecialLinearGroup ι F => (g : Matrix ι ι F))
    Subtype.val_injective

variable (F ι) in
/-- The diagonal embedding $\mathrm{SL}_\iota(F)\to\mathrm{SL}_\iota(\mathbb A_F)$. -/
def slnEmb : Matrix.SpecialLinearGroup ι F →* SLnA F ι := Matrix.SpecialLinearGroup.map (diagRing F)

@[simp] theorem slnEmb_apply (γ : Matrix.SpecialLinearGroup ι F) (i j : ι) :
    (slnEmb F ι γ : Matrix ι ι (Adeles F)) i j = diag F ((γ : Matrix ι ι F) i j) := rfl

theorem slnEmb_injective : Function.Injective (slnEmb F ι) := by
  intro γ δ h
  ext i j
  have := congrArg (fun g : SLnA F ι => (g : Matrix ι ι (Adeles F)) i j) h
  simp only [slnEmb_apply] at this
  exact diag_injective this

variable (F ι) in
/-- $\mathrm{SL}_\iota(F)$ as a subgroup of $\mathrm{SL}_\iota(\mathbb A_F)$. -/
def slnSub : Subgroup (SLnA F ι) := (slnEmb F ι).range

/-- **$\mathrm{SL}_\iota(F)$ is discrete in $\mathrm{SL}_\iota(\mathbb A_F)$** (entrywise, from the discreteness of
$F$ in $\mathbb A_F$). -/
@[kb "weil1982" "§2.4, p. 23 (G_k discrete in G_𝔸) [unverified locator for the discreteness statement]"]
theorem discreteTopology_slnSub : DiscreteTopology (slnSub F ι) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  set V : Set (SLnA F ι) := {g | ∀ i j, (g : Matrix ι ι (Adeles F)) i j -
    (1 : Matrix ι ι (Adeles F)) i j ∈ U}
  have hV : IsOpen V := by
    simp only [V, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_
    exact ((continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)).sub
      continuous_const
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr ⟨V, hV, ?_⟩)
  ext ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff, V]
  constructor
  · intro h
    have hγ : γ = 1 := by
      ext i j
      have h' := h i j
      rw [slnEmb_apply] at h'
      have : diag F ((γ : Matrix ι ι F) i j - (1 : Matrix ι ι F) i j) ∈ U := by
        rw [← diagRing_apply, map_sub, diagRing_apply]
        convert h' using 2
        rcases eq_or_ne i j with rfl | hij
        · simp [Matrix.one_apply_eq, map_one]
        · simp [Matrix.one_apply_ne hij]
      exact sub_eq_zero.mp (hUdiag _ this)
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h i j
    have h1 : slnEmb F ι γ = 1 := congrArg Subtype.val h
    rw [h1, Matrix.SpecialLinearGroup.coe_one, sub_self]
    exact h0U

instance : DiscreteTopology (slnSub F ι) := discreteTopology_slnSub

/-! ### Weil's quotient $G_{\mathbb A}/G_k$ -/

/-- $\mathrm{SL}_\iota(F)$ acts on $\mathrm{SL}_\iota(\mathbb A_F)$ by right translation, $\gamma\cdot g = g\gamma^{-1}$. -/
instance slnRightAction : MulAction (Matrix.SpecialLinearGroup ι F) (SLnA F ι) where
  smul γ g := g * (slnEmb F ι γ)⁻¹
  one_smul g := by show g * (slnEmb F ι 1)⁻¹ = g; simp
  mul_smul γ δ g := by
    show g * (slnEmb F ι (γ * δ))⁻¹ = g * (slnEmb F ι δ)⁻¹ * (slnEmb F ι γ)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]

theorem slnRight_smul_def (γ : Matrix.SpecialLinearGroup ι F) (g : SLnA F ι) :
    γ • g = g * (slnEmb F ι γ)⁻¹ := rfl

instance : MeasurableConstSMul (Matrix.SpecialLinearGroup ι F) (SLnA F ι) :=
  ⟨fun γ => measurable_mul_const (slnEmb F ι γ)⁻¹⟩

/-- **Exact measurable fundamental domain for $G_{\mathbb A}/G_k$.** -/
theorem exists_measurableSet_forall_existsUnique_right' :
    ∃ D : Set (SLnA F ι), MeasurableSet D ∧ ∀ g : SLnA F ι, ∃! γ : Matrix.SpecialLinearGroup ι F, γ • g ∈ D := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_smul_mem (slnSub F ι)
  refine ⟨(fun g => g⁻¹) ⁻¹' D, measurable_inv hD, fun g => ?_⟩
  obtain ⟨⟨_, γ, rfl⟩, hγ, huniq⟩ := h g⁻¹
  refine ⟨γ, ?_, fun δ hδ => ?_⟩
  · show (g * (slnEmb F ι γ)⁻¹)⁻¹ ∈ D
    rw [mul_inv_rev, inv_inv]; exact hγ
  · have hδ' : (⟨slnEmb F ι δ, δ, rfl⟩ : slnSub F ι) • g⁻¹ ∈ D := by
      show slnEmb F ι δ * g⁻¹ ∈ D
      have : (g * (slnEmb F ι δ)⁻¹)⁻¹ ∈ D := hδ
      rwa [mul_inv_rev, inv_inv] at this
    have := huniq _ hδ'
    exact slnEmb_injective (congrArg Subtype.val this)

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
