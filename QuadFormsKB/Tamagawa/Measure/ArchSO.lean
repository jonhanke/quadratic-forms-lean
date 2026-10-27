import QuadFormsKB.Tamagawa.ArchVolume

/-!
# The compact group $SO(Q_\sigma)(\mathbb R)$ at a real place

For a positive definite real form $Q$ in $n$ variables, `soReal Q` is the subgroup
$SO(Q)(\mathbb R) = \{g \in \mathrm{GL}_n(\mathbb R) : g^{\mathsf T}Hg = H,\ \det g = 1\}$ of $\mathrm{GL}_n(\mathbb R)$
($H$ = `Q.hessian`; the same matrix condition as `orthGroup`). We prove it is compact (`isCompact_soReal`, closed and
bounded in $M_n(\mathbb R)$, together with the inverse $g^{-1} = H^{-1}g^{\mathsf T}H$), so `ArchSO Q` (the same group
as a type with its own Borel structure) is a compact, second countable, Hausdorff topological group.
-/

open MeasureTheory Matrix Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.ArchSOMeasure

open QuadFormsKB.Siegel

variable {n : ℕ}

/-- **The orthogonal group $O(Q)(\mathbb R)$** as a subgroup of $\mathrm{GL}_n(\mathbb R)$: $g^{\mathsf T}Hg = H$. -/
def orthReal (Q : QuadForm ℝ n) : Subgroup (GL (Fin n) ℝ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (g : Matrix (Fin n) (Fin n) ℝ) = Q.hessian}
  mul_mem' {a b} ha hb := by
    change (a : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * (a : Matrix (Fin n) (Fin n) ℝ) = _ at ha
    change (b : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * (b : Matrix (Fin n) (Fin n) ℝ) = _ at hb
    change ((a * b : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * ((a * b : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = _
    rw [Units.val_mul, transpose_mul]
    calc (b : Matrix (Fin n) (Fin n) ℝ)ᵀ * (a : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian *
          ((a : Matrix (Fin n) (Fin n) ℝ) * (b : Matrix (Fin n) (Fin n) ℝ))
        = (b : Matrix (Fin n) (Fin n) ℝ)ᵀ * ((a : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian *
            (a : Matrix (Fin n) (Fin n) ℝ)) * (b : Matrix (Fin n) (Fin n) ℝ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  one_mem' := by
    change ((1 : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * ((1 : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = _
    simp
  inv_mem' {a} ha := by
    change (a : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * (a : Matrix (Fin n) (Fin n) ℝ) = _ at ha
    change ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * _ * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = _
    have h1 : (a : Matrix (Fin n) (Fin n) ℝ) * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
        = ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * ((a : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian *
            (a : Matrix (Fin n) (Fin n) ℝ)) * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by rw [ha]
      _ = ((a : Matrix (Fin n) (Fin n) ℝ) * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ))ᵀ * Q.hessian *
            ((a : Matrix (Fin n) (Fin n) ℝ) * ((a⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp

/-- **$SO(Q)(\mathbb R)$** $= \{g \in \mathrm{GL}_n(\mathbb R) : g^{\mathsf T}Hg = H,\ \det g = 1\}$ with $H$ = `Q.hessian`. -/
def soReal (Q : QuadForm ℝ n) : Subgroup (GL (Fin n) ℝ) :=
  orthReal Q ⊓ (Matrix.GeneralLinearGroup.det (n := Fin n) (R := ℝ)).ker

theorem mem_soReal_iff (Q : QuadForm ℝ n) (g : GL (Fin n) ℝ) :
    g ∈ soReal Q ↔ (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (g : Matrix (Fin n) (Fin n) ℝ) = Q.hessian ∧
      (g : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  rw [soReal, Subgroup.mem_inf, MonoidHom.mem_ker]
  refine and_congr Iff.rfl ?_
  rw [Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.det]


/-! ### Compactness -/

/-- A positive definite real form is bounded below by a multiple of the squared sup norm. -/
theorem exists_lower_bound {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * ‖x‖ ^ 2 ≤ Q.eval x := by
  by_cases hS : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hS
      (continuous_eval_real Q).continuousOn
    have hx0n : x0 ≠ 0 := by
      rintro rfl; simp at hx0
    refine ⟨Q.eval x0, hQ x0 hx0n, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp [QuadForm.evalIn]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      have := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 by simpa using hu)
      have h2 : Q.eval x0 ≤ (‖x‖⁻¹) ^ 2 * Q.eval x := by
        have h3 : Q.eval x0 ≤ Q.eval ((‖x‖⁻¹ : ℝ) • x) := this
        rwa [eval_smul_real] at h3
      have : Q.eval x0 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 * ((‖x‖⁻¹) ^ 2 * Q.eval x) :=
        by nlinarith [sq_nonneg ‖x‖]
      calc Q.eval x0 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 * ((‖x‖⁻¹) ^ 2 * Q.eval x) := this
        _ = Q.eval x := by field_simp
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [QuadForm.evalIn]
    · exfalso
      apply hS
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_⟩
      simp [norm_smul, inv_mul_cancel₀ hxn.ne']


/-- For $M \in O(Q)$ the $j$-th column $x$ has $Q(x) = H_{jj}/2$. -/
theorem eval_col {Q : QuadForm ℝ n} {M : Matrix (Fin n) (Fin n) ℝ} (h : Mᵀ * Q.hessian * M = Q.hessian)
    (j : Fin n) : Q.eval (fun i => M i j) = Q.hessian j j / 2 := by
  have h1 : (fun i => M i j) ⬝ᵥ (Q.hessian *ᵥ fun i => M i j) = Q.hessian j j := by
    calc _ = (Mᵀ * Q.hessian * M) j j := by
          simp only [Matrix.mul_apply, dotProduct, mulVec, transpose_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := congrFun (congrFun h j) j
  rw [eval_real_eq_gramR, gramMatrixR, smul_mulVec, dotProduct_smul, smul_eq_mul, h1]
  ring

/-- Entries of $M \in O(Q)$ are uniformly bounded ($Q$ positive definite). -/
theorem exists_entry_bound {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) :
    ∃ R : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ * Q.hessian * M = Q.hessian → ∀ i j, |M i j| ≤ R := by
  obtain ⟨c, hc, hlow⟩ := exists_lower_bound hQ
  refine ⟨Real.sqrt (∑ j, Q.hessian j j / (2 * c)), fun M h i j => ?_⟩
  refine Real.abs_le_sqrt ?_
  have hx := hlow (fun i => M i j)
  rw [eval_col h j] at hx
  have h1 : |M i j| ≤ ‖fun i => M i j‖ := by
    simpa using norm_le_pi_norm (fun i => M i j) i
  have h2 : M i j ^ 2 ≤ ‖fun i => M i j‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : ‖fun i => M i j‖ ^ 2 ≤ Q.hessian j j / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h4 : Q.hessian j j / (2 * c) ≤ ∑ j, Q.hessian j j / (2 * c) := by
    refine Finset.single_le_sum (f := fun j => Q.hessian j j / (2 * c)) (fun k _ => ?_) (Finset.mem_univ j)
    have h5 := hlow (fun i => M i k)
    rw [eval_col h k] at h5
    have : 0 ≤ Q.hessian k k / 2 := le_trans (by positivity) h5
    exact div_nonneg (by linarith) (by positivity)
  linarith


theorem isUnit_hessian_det {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) : IsUnit Q.hessian.det := by
  have := gramDetR_pos hQ
  rw [gramDetR] at this
  exact isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at this)

/-- **$SO(Q)(\mathbb R)$ is compact** for $Q$ positive definite: it is the image of the compact set
$\{M : M^{\mathsf T}HM = H,\ \det M = 1\} \subset M_n(\mathbb R)$ under $M \mapsto (M, H^{-1}M^{\mathsf T}H)$, which
parametrizes $(g, g^{-1})$, the embedding of $\mathrm{GL}_n(\mathbb R)$ into $M_n \times M_n^{\mathrm{op}}$. -/
theorem isCompact_soReal {Q : QuadForm ℝ n} (hQ : IsPosDefR Q) :
    IsCompact ((soReal Q : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ)) := by
  obtain ⟨R, hR⟩ := exists_entry_bound hQ
  have hH : IsUnit Q.hessian := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_hessian_det hQ)
  set K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | Mᵀ * Q.hessian * M = Q.hessian ∧ M.det = 1} with hK
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Set.Icc (-R) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    have hcl : IsClosed K := by
      refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
      · exact (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id
      · exact continuous_id.matrix_det
    refine IsCompact.of_isClosed_subset hbox hcl fun M hM => ?_
    intro i _ j _
    have := hR M hM.1 i j
    exact abs_le.mp this
  let φ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op (Q.hessian⁻¹ * Mᵀ * Q.hessian))
  have hφ : Continuous φ := by
    refine continuous_id.prodMk (MulOpposite.continuous_op.comp ?_)
    exact (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) ℝ)).isCompact_iff]
  have : Units.embedProduct (Matrix (Fin n) (Fin n) ℝ) '' ((soReal Q : Subgroup (GL (Fin n) ℝ)) : Set (GL (Fin n) ℝ))
      = φ '' K := by
    have hXM : ∀ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ * Q.hessian * M = Q.hessian →
        (Q.hessian⁻¹ * Mᵀ * Q.hessian) * M = 1 := by
      intro M h1
      have e : Q.hessian⁻¹ * Mᵀ * Q.hessian * M = Q.hessian⁻¹ * (Mᵀ * Q.hessian * M) := by
        simp only [Matrix.mul_assoc]
      rw [e, h1, Matrix.nonsing_inv_mul _ (isUnit_hessian_det hQ)]
    ext ⟨A, B⟩
    constructor
    · rintro ⟨g, hg, hgAB⟩
      obtain ⟨h1, h2⟩ := (mem_soReal_iff Q g).mp hg
      have hA : A = (g : Matrix (Fin n) (Fin n) ℝ) := (congrArg Prod.fst hgAB).symm
      have hB : B = MulOpposite.op ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
        (congrArg Prod.snd hgAB).symm
      subst hA
      set A : Matrix (Fin n) (Fin n) ℝ := (g : Matrix (Fin n) (Fin n) ℝ) with hAdef
      refine ⟨A, ⟨h1, h2⟩, ?_⟩
      have hinv : (Q.hessian⁻¹ * (A)ᵀ * Q.hessian) = ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
        calc _ = (Q.hessian⁻¹ * (A)ᵀ * Q.hessian) * (A * ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
          _ = ((Q.hessian⁻¹ * (A)ᵀ * Q.hessian) * A) * ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hXM A h1, Matrix.one_mul]
      simp only [φ, hB, hinv]
    · rintro ⟨M, ⟨h1, h2⟩, hM⟩
      have hMX : M * (Q.hessian⁻¹ * Mᵀ * Q.hessian) = 1 := mul_eq_one_comm.mp (hXM M h1)
      refine ⟨⟨M, Q.hessian⁻¹ * Mᵀ * Q.hessian, hMX, hXM M h1⟩, ?_, ?_⟩
      · exact (mem_soReal_iff Q _).mpr ⟨h1, h2⟩
      · rw [← hM]; rfl
  rw [this]
  exact hKc.image hφ


/-! ### The group as a type, with its Borel structure -/

/-- **$SO(Q)(\mathbb R)$ as a type**: the subgroup `soReal Q` of $\mathrm{GL}_n(\mathbb R)$, wrapped so that it carries
its own Borel $\sigma$-algebra (Mathlib's `Units` instance is the comap of `val`, a different instance). -/
def ArchSO (Q : QuadForm ℝ n) : Type := soReal Q

namespace ArchSO

variable (Q : QuadForm ℝ n)

instance : Group (ArchSO Q) := inferInstanceAs (Group (soReal Q))
instance : TopologicalSpace (ArchSO Q) := inferInstanceAs (TopologicalSpace (soReal Q))
instance : IsTopologicalGroup (ArchSO Q) := inferInstanceAs (IsTopologicalGroup (soReal Q))
instance : T2Space (ArchSO Q) := inferInstanceAs (T2Space (soReal Q))

local instance secondCountable_matrix : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

local instance secondCountable_op : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℝ)).symm.isEmbedding.secondCountableTopology

local instance secondCountable_GL : SecondCountableTopology (GL (Fin n) ℝ) :=
  (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) ℝ)).secondCountableTopology

instance : SecondCountableTopology (ArchSO Q) :=
  (Topology.IsEmbedding.subtypeVal (p := fun g : GL (Fin n) ℝ => g ∈ soReal Q)).secondCountableTopology
instance : MeasurableSpace (ArchSO Q) := borel _
instance : BorelSpace (ArchSO Q) := ⟨rfl⟩

/-- The inclusion $SO(Q)(\mathbb R) \to \mathrm{GL}_n(\mathbb R)$ as a homomorphism. -/
def incl : ArchSO Q →* GL (Fin n) ℝ := (soReal Q).subtype

theorem continuous_incl : Continuous (incl Q) := continuous_subtype_val

/-- **$SO(Q)(\mathbb R)$ is compact** for positive definite $Q$. -/
instance [hQ : Fact (IsPosDefR Q)] : CompactSpace (ArchSO Q) :=
  show CompactSpace (soReal Q) from isCompact_iff_compactSpace.mp (isCompact_soReal hQ.out)

instance [Fact (IsPosDefR Q)] : LocallyCompactSpace (ArchSO Q) := inferInstance

end ArchSO


/-! ### The Haar probability measure and $\mu_\sigma$ -/

theorem archVolSO_pos (n : ℕ) {d : ℝ} (hd : 0 < d) : 0 < QuadFormsKB.Tamagawa.archVolSO n d := by
  unfold QuadFormsKB.Tamagawa.archVolSO
  refine mul_pos (mul_pos (mul_pos (by norm_num) (by positivity)) (Real.rpow_pos_of_pos hd _))
    (Finset.prod_pos fun j _ => div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.Gamma_pos_of_pos (by positivity)))

namespace ArchSO

variable (Q : QuadForm ℝ n) [hQ : Fact (IsPosDefR Q)]

/-- **The Haar probability measure on $SO(Q)(\mathbb R)$** (the Haar measure normalized on the whole compact group). -/
def haarProb : Measure (ArchSO Q) := Measure.haarMeasure ⊤

instance : (haarProb Q).IsHaarMeasure := by unfold haarProb; infer_instance

instance : IsProbabilityMeasure (haarProb Q) :=
  ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (ArchSO Q)))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h⟩

/-- **The measure $\mu_\sigma$** at a real place: `archVolSO` times the Haar probability measure on
$SO(Q_\sigma)(\mathbb R)$. It is a Haar measure (left and right invariant: the group is compact) whose total mass is
the Weil gauge-form volume of $SO(Q_\sigma)$. -/
def mu : Measure (ArchSO Q) :=
  ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO n (gramDetR Q)) • haarProb Q

theorem mu_univ :
    mu Q Set.univ = ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO n (gramDetR Q)) := by
  simp [mu]

instance : (mu Q).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _
    (by simpa using archVolSO_pos n (gramDetR_pos hQ.out)) ENNReal.ofReal_ne_top

instance : IsFiniteMeasure (mu Q) := Measure.smul_finite _ ENNReal.ofReal_ne_top

instance : (mu Q).IsMulLeftInvariant := by unfold mu; infer_instance

end ArchSO


/-! ### Total mass: the gauge-form volume -/

namespace ArchSO

variable (Q : QuadForm ℝ n) [hQ : Fact (IsPosDefR Q)]

/-- **Link to the gauge-form volume:** for $n \ge 1$ the total mass of $\mu_\sigma$ is the gauge-form volume of
$SO(Q)$ (Siegel's limit). -/
theorem mu_univ_eq_volume (hn : 1 ≤ n) :
    mu Q Set.univ = ENNReal.ofReal (ArchVol.archVolSOLim Q) := by
  rw [mu_univ, ArchVol.archVolSO_eq_volume hQ.out hn]

end ArchSO

open NumberField in
/-- **The total mass at a real embedding:** for $Q_0$ over $\mathcal O_F$ and a real embedding $\sigma = \rho$, the
measure $\mu_\sigma$ on $SO(Q_\sigma)(\mathbb R)$ has total mass `archVolSO n (detGram Q₀ σ)`, the factor
in `tamagawaK`. -/
theorem mu_univ_detGram {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) n)
    (σ : F →ₐ[ℚ] ℂ) (ρ : F →+* ℝ) (hσ : ∀ x, σ x = (ρ x : ℂ))
    [Fact (IsPosDefR (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))))] :
    ArchSO.mu (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))) Set.univ =
      ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO n (QuadFormsKB.Tamagawa.detGram Q₀ σ)) := by
  rw [ArchSO.mu_univ]
  congr 2
  have hpos := gramDetR_pos (Fact.out : IsPosDefR (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))))
  rw [QuadFormsKB.Tamagawa.detGram, hσ, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hpos]
  congr 1
  rw [gramDetR, hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp [map_ofNat]


/-! ### Transport along an isometry -/

section Isometry

variable {Q Q' : QuadForm ℝ n}

/-- Conjugation by $P$ maps $SO(Q')$ into $SO(Q)$ when $H' = P^{\mathsf T}HP$. -/
theorem conj_mem_soReal (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ))
    {g : GL (Fin n) ℝ} (hg : g ∈ soReal Q') : P * g * P⁻¹ ∈ soReal Q := by
  obtain ⟨h1, h2⟩ := (mem_soReal_iff Q' g).mp hg
  rw [mem_soReal_iff]
  set pm : Matrix (Fin n) (Fin n) ℝ := (P : Matrix (Fin n) (Fin n) ℝ) with hpm
  set qm : Matrix (Fin n) (Fin n) ℝ := ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) with hqm
  set gm : Matrix (Fin n) (Fin n) ℝ := (g : Matrix (Fin n) (Fin n) ℝ) with hgm
  have e1 : pm * qm = 1 := by rw [hpm, hqm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : qmᵀ * pmᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  simp only [Units.val_mul]
  constructor
  · calc (pm * gm * qm)ᵀ * Q.hessian * (pm * gm * qm)
        = qmᵀ * (gmᵀ * (pmᵀ * Q.hessian * pm) * gm) * qm := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = qmᵀ * (gmᵀ * Q'.hessian * gm) * qm := by rw [← hP]
      _ = qmᵀ * (pmᵀ * Q.hessian * pm) * qm := by rw [h1, hP]
      _ = (qmᵀ * pmᵀ) * Q.hessian * (pm * qm) := by simp only [Matrix.mul_assoc]
      _ = Q.hessian := by rw [e1, e2]; simp
  · rw [Matrix.det_mul, Matrix.det_mul, h2]
    have := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_one] at this
    linarith [mul_comm (pm.det) (qm.det)]

/-- The conjugation isomorphism $SO(Q') \to SO(Q)$, $g \mapsto PgP^{-1}$. -/
def conjEquiv (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ)) :
    ArchSO Q' ≃* ArchSO Q := by
  have hP' : Q.hessian = ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q'.hessian *
      ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    have e1 : (P : Matrix (Fin n) (Fin n) ℝ) * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * (P : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
      rw [← transpose_mul, e1, transpose_one]
    rw [hP]
    calc Q.hessian = (((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * (P : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
          Q.hessian * ((P : Matrix (Fin n) (Fin n) ℝ) * ((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [e1, e2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  refine
    { toFun := fun g => ⟨P * g.1 * P⁻¹, conj_mem_soReal P hP g.2⟩
      invFun := fun g => ⟨P⁻¹ * g.1 * P⁻¹⁻¹, conj_mem_soReal P⁻¹ hP' g.2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by
        show P * (a.1 * b.1) * P⁻¹ = (P * a.1 * P⁻¹) * (P * b.1 * P⁻¹)
        simp [mul_assoc]) }

theorem continuous_conjEquiv (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ)) :
    Continuous (conjEquiv P hP) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem eval_eq_dotProduct_hessian (Q : QuadForm ℝ n) (y : Fin n → ℝ) :
    Q.eval y = (y ⬝ᵥ (Q.hessian *ᵥ y)) / 2 := by
  rw [eval_real_eq_gramR, gramMatrixR, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

theorem eval_of_hessian_eq (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ))
    (x : Fin n → ℝ) : Q'.eval x = Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) := by
  rw [eval_eq_dotProduct_hessian, eval_eq_dotProduct_hessian, hP, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]

/-- Positive definiteness is transported along $H' = P^{\mathsf T}HP$. -/
theorem isPosDefR_of_hessian_eq (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ))
    (hQ : IsPosDefR Q) : IsPosDefR Q' := fun x hx => by
  rw [eval_of_hessian_eq P hP]
  refine hQ _ fun h0 => hx ?_
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit P)
  exact hinj (by rw [h0, mulVec_zero])

theorem gramDetR_of_hessian_eq (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ)) :
    gramDetR Q' = (P : Matrix (Fin n) (Fin n) ℝ).det ^ 2 * gramDetR Q := by
  rw [gramDetR, gramDetR, hP, Matrix.det_mul, Matrix.det_mul, det_transpose]
  ring

end Isometry

/-- Scaling of `archVolSO`: $\mathrm{vol}(SO_n, d/c^2) = c^{n+1}\mathrm{vol}(SO_n, d)$ (same proof as
`archVolSO_div_sq`, restated here to keep this file light). -/
theorem archVolSO_div_sq' (m : ℕ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    QuadFormsKB.Tamagawa.archVolSO m (d / c ^ 2) = QuadFormsKB.Tamagawa.archVolSO m d * c ^ (m + 1) := by
  unfold QuadFormsKB.Tamagawa.archVolSO
  rw [Real.div_rpow hd.le (by positivity), ← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le,
    show ((2 : ℕ) : ℝ) * (-((m : ℝ) + 1) / 2) = -(((m + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg hc.le,
    Real.rpow_natCast]
  have : c ^ (m + 1) ≠ 0 := by positivity
  field_simp

theorem archVolSO_mul_sq (m : ℕ) {d p : ℝ} (hd : 0 < d) (hp : p ≠ 0) :
    QuadFormsKB.Tamagawa.archVolSO m (p ^ 2 * d) =
      QuadFormsKB.Tamagawa.archVolSO m d * (|p|⁻¹) ^ (m + 1) := by
  have hc : 0 < |p|⁻¹ := by positivity
  rw [← archVolSO_div_sq' m hd hc]
  congr 1
  rw [inv_pow, sq_abs]
  field_simp

namespace ArchSO

variable {Q Q' : QuadForm ℝ n} [hQ : Fact (IsPosDefR Q)] [hQ' : Fact (IsPosDefR Q')]

/-- **Haar probability measures correspond under conjugation by an isometry.** -/
theorem map_conjEquiv_haarProb (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ)) :
    Measure.map (conjEquiv P hP) (haarProb Q') = haarProb Q := by
  have hc := continuous_conjEquiv P hP
  have : (Measure.map (conjEquiv P hP) (haarProb Q')).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (haarProb Q') (conjEquiv P hP) hc
      (by
        -- the inverse is conjugation by P⁻¹
        exact (continuous_const.mul continuous_subtype_val |>.mul continuous_const).subtype_mk _)
  have : IsProbabilityMeasure (Measure.map (conjEquiv P hP) (haarProb Q')) :=
    (Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable).mpr inferInstance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- **Behaviour of $\mu_\sigma$ under an isometry.** If $H' = P^{\mathsf T}HP$ ($P \in \mathrm{GL}_n(\mathbb R)$, i.e.
$Q'(x) = Q(Px)$), conjugation $g \mapsto PgP^{-1}$ carries $\mu_{Q'}$ to $|\det P|^{-(n+1)}\mu_Q$. -/
theorem map_conjEquiv_mu (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ)) :
    Measure.map (conjEquiv P hP) (mu Q') =
      ENNReal.ofReal ((|(P : Matrix (Fin n) (Fin n) ℝ).det|⁻¹) ^ (n + 1)) • mu Q := by
  have hdet : (P : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P)
    exact this.ne_zero
  have hd := gramDetR_pos hQ.out
  unfold mu
  rw [Measure.map_smul, map_conjEquiv_haarProb P hP, gramDetR_of_hessian_eq P hP, archVolSO_mul_sq n hd hdet,
    smul_smul, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  exact (continuous_conjEquiv P hP).measurable.aemeasurable

/-- Isometries of determinant $\pm1$ transport $\mu_{Q'}$ exactly to $\mu_Q$. -/
theorem map_conjEquiv_mu_of_abs_det (P : GL (Fin n) ℝ)
    (hP : Q'.hessian = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (P : Matrix (Fin n) (Fin n) ℝ))
    (h1 : |(P : Matrix (Fin n) (Fin n) ℝ).det| = 1) :
    Measure.map (conjEquiv P hP) (mu Q') = mu Q := by
  rw [map_conjEquiv_mu, h1]; simp

end ArchSO


/-! ### The product over the real places -/

section Product

variable {ι : Type*} [Fintype ι] (Q : ι → QuadForm ℝ n) [∀ i, Fact (IsPosDefR (Q i))]

/-- **The archimedean group** $G_\infty = \prod_\sigma SO(Q_\sigma)(\mathbb R)$ (finite product), compact. -/
abbrev ArchSOProd : Type _ := ∀ i, ArchSO (Q i)

/-- **The measure $\mu_\infty$** on $\prod_\sigma SO(Q_\sigma)(\mathbb R)$: the product measure of the $\mu_\sigma$. -/
def muInf : Measure (ArchSOProd Q) := Measure.pi fun i => ArchSO.mu (Q i)

instance : IsFiniteMeasure (muInf Q) := by unfold muInf; infer_instance

instance : (muInf Q).IsHaarMeasure := by unfold muInf; infer_instance

/-- $\mu_\infty$ has total mass $\prod_\sigma$ `archVolSO`. -/
theorem muInf_univ :
    muInf Q Set.univ = ∏ i, ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO n (gramDetR (Q i))) := by
  rw [muInf, Measure.pi_univ]
  exact Finset.prod_congr rfl fun i _ => ArchSO.mu_univ (Q i)

theorem muInf_univ_real :
    (muInf Q Set.univ).toReal = ∏ i, QuadFormsKB.Tamagawa.archVolSO n (gramDetR (Q i)) := by
  rw [muInf_univ, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ =>
    ENNReal.toReal_ofReal (archVolSO_pos n (gramDetR_pos (Fact.out : IsPosDefR (Q i)))).le

open NumberField in
/-- **The archimedean factor of `tamagawaK`:** over real embeddings $\sigma_i = \rho_i$ of $F$, $\mu_\infty$ has total mass
$\prod_i$ `archVolSO n (detGram Q₀ σᵢ)`. -/
theorem muInf_univ_detGram {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) n)
    (σ : ι → (F →ₐ[ℚ] ℂ)) (ρ : ι → (F →+* ℝ)) (hσ : ∀ i x, σ i x = (ρ i x : ℂ))
    (hQ : ∀ i, Q i = Q₀.map ((ρ i).comp (algebraMap (𝓞 F) F))) :
    muInf Q Set.univ =
      ∏ i, ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO n (QuadFormsKB.Tamagawa.detGram Q₀ (σ i))) := by
  rw [muInf_univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hp : IsPosDefR (Q₀.map ((ρ i).comp (algebraMap (𝓞 F) F))) := hQ i ▸ (Fact.out : IsPosDefR (Q i))
  have : Fact (IsPosDefR (Q₀.map ((ρ i).comp (algebraMap (𝓞 F) F)))) := ⟨hp⟩
  have h := mu_univ_detGram Q₀ (σ i) (ρ i) (hσ i)
  rw [ArchSO.mu_univ] at h
  rw [hQ i]
  exact h

end Product

end QuadFormsKB.Tamagawa.ArchSOMeasure
