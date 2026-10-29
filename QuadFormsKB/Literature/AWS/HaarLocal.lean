import QuadFormsKB.Literature.AWS.Adelic

open Matrix

namespace QuadFormsKB.AWS

variable {n : ℕ}

section
variable (p : ℕ) [Fact p.Prime]

private theorem isOpen_isIntP : IsOpen {M : Matrix (Fin n) (Fin n) ℚ_[p] | IsIntP p M} := by
  have : {M : Matrix (Fin n) (Fin n) ℚ_[p] | IsIntP p M} =
      ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) ℚ_[p] => M i j) ⁻¹' Metric.closedBall 0 1 := by
    ext M; simp [IsIntP]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero |>.preimage
    ((continuous_apply j).comp (continuous_apply i))

private theorem isCompact_isIntP : IsCompact {M : Matrix (Fin n) (Fin n) ℚ_[p] | IsIntP p M} := by
  have : {M : Matrix (Fin n) (Fin n) ℚ_[p] | IsIntP p M} =
      Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n => Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext M
    show (∀ i j, ‖M i j‖ ≤ 1) ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ Metric.closedBall 0 1
    simp
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

private theorem isClosed_isIntP : IsClosed {M : Matrix (Fin n) (Fin n) ℚ_[p] | IsIntP p M} :=
  (isCompact_isIntP p).isClosed

end

/-- The set $O(V)(\mathbb{Z}_p)$ is open in $O(V)(\mathbb{Q}_p)$ (for the $p$-adic topology). -/
theorem isOpen_intStab (H : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact p.Prime] :
    IsOpen (intStab H p : Set (orthGroup H ℚ_[p])) := by
  have h1 : Continuous fun g : orthGroup H ℚ_[p] => (g : GL (Fin n) ℚ_[p]).val :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun g : orthGroup H ℚ_[p] => ((g : GL (Fin n) ℚ_[p])⁻¹).val :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  exact (isOpen_isIntP p).preimage h1 |>.inter ((isOpen_isIntP p).preimage h2)

/-- The set $O(V)(\mathbb{Z}_p)$ is compact in $O(V)(\mathbb{Q}_p)$. -/
theorem isCompact_intStab (H : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact p.Prime] :
    IsCompact (intStab H p : Set (orthGroup H ℚ_[p])) := by
  let e : orthGroup H ℚ_[p] → Matrix (Fin n) (Fin n) ℚ_[p] × (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ :=
    fun g => Units.embedProduct _ (g : GL (Fin n) ℚ_[p])
  have he : Topology.IsEmbedding e :=
    Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  rw [he.isCompact_iff]
  let T : Set (Matrix (Fin n) (Fin n) ℚ_[p] × (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ) :=
    {x | IsIntP p x.1 ∧ IsIntP p x.2.unop ∧ x.1 * x.2.unop = 1 ∧ x.2.unop * x.1 = 1 ∧
      x.1ᵀ * H.map (algebraMap ℚ ℚ_[p]) * x.1 = H.map (algebraMap ℚ ℚ_[p])}
  have hu : Continuous fun x : Matrix (Fin n) (Fin n) ℚ_[p] × (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ =>
      x.2.unop := MulOpposite.continuous_unop.comp continuous_snd
  have hT : IsClosed T := by
    exact ((isClosed_isIntP p).preimage continuous_fst).inter (((isClosed_isIntP p).preimage hu).inter
      ((isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter
      ((isClosed_eq (hu.matrix_mul continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul
        continuous_fst) continuous_const))))
  have hTc : IsCompact T := by
    have : T ⊆ {M | IsIntP p M} ×ˢ (MulOpposite.op '' {M | IsIntP p M}) := by
      rintro ⟨a, b⟩ ⟨ha, hb, -⟩
      exact ⟨ha, MulOpposite.unop b, hb, rfl⟩
    refine IsCompact.of_isClosed_subset ((isCompact_isIntP p).prod ?_) hT this
    exact (isCompact_isIntP p).image MulOpposite.continuous_op
  have : e '' (intStab H p : Set (orthGroup H ℚ_[p])) = T := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨g, hg, hgx⟩
      have ha : a = (g : GL (Fin n) ℚ_[p]).val := by
        have := congrArg Prod.fst hgx; simpa [e] using this.symm
      have hb : b.unop = ((g : GL (Fin n) ℚ_[p])⁻¹).val := by
        have := congrArg Prod.snd hgx; simpa [e] using congrArg MulOpposite.unop this.symm
      subst ha
      refine ⟨hg.1, hb ▸ hg.2, ?_, ?_, mem_orthGroup.mp g.2⟩ <;> simp [hb]
    · rintro ⟨ha, hb, h1, h2, h3⟩
      let u : GL (Fin n) ℚ_[p] := ⟨a, b.unop, h1, h2⟩
      have hu' : u ∈ orthGroup H ℚ_[p] := mem_orthGroup.mpr h3
      refine ⟨⟨u, hu'⟩, ⟨ha, ?_⟩, ?_⟩
      · change IsIntP p (u⁻¹).val
        exact hb
      · rfl
  rw [this]; exact hTc

instance (H : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact p.Prime] : CompactSpace (intStab H p) :=
  isCompact_iff_compactSpace.mp (isCompact_intStab H p)

end QuadFormsKB.AWS
