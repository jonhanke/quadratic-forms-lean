/-
# Hasse norm theorem, step 4b: the local norm index at a non-split finite place

For $L = F(\sqrt a)$ and a prime $w$ of $L$ over $v$:

* `compMap`: the completion map $F_v \to L_w$ (from Mathlib's `uniformContinuous_algebraMap_liesOver`),
  making $L_w$ an $F_v$-algebra (`compAlgebra`);
* `tensorToCompletion_surjective`: $F_v \otimes_F L \to L_w$ is onto;
* `tensor_structure`: $F_v \otimes_F L = F_v \oplus F_v t$, $t^2 = a$, norm $x_0^2 - a x_1^2$;
* `ordTwo_liesOver`, `absNorm_pow_ordTwo_le`: $N(w)^{\operatorname{ord}_w 2} \le N(v)^{2\operatorname{ord}_v 2}$;
* `two_le_index_norm`: if $a$ is not a square in $F_v$, the local norms have index $\ge 2$ in $F_v^\times$.

The last is the local input "$[F_v^\times : N] \ge 2$ at non-split places" of the plan in `Herbrand.lean`, proved
at **all** finite places (including $v \mid 2$) by counting square classes (`index_sq_completion` for $F$ at $v$
and for $L$ at $w$), with no local class field theory.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.SquareClasses

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L]

/-- The map of completions $F_v \to L_w$ for $w \mid v$. -/
def compMap (w : HeightOneSpectrum (𝓞 L)) :
    (under (F := F) w).adicCompletion F →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((under (F := F) w).valuation F)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F L (under (F := F) w) w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv F (under (F := F) w)).toRingHom)


/-- `compMap` extends $F \to L$. -/
lemma compMap_algebraMap (w : HeightOneSpectrum (𝓞 L)) (c : F) :
    compMap w (algebraMap F ((under (F := F) w).adicCompletion F) c) =
      algebraMap L (w.adicCompletion L) (algebraMap F L c) := by
  simp only [compMap, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
  erw [UniformSpace.Completion.mapRingHom_coe]
  rfl

/-- `compMap` is continuous. -/
lemma continuous_compMap (w : HeightOneSpectrum (𝓞 L)) : Continuous (compMap (F := F) w) := by
  unfold compMap
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion F (under (F := F) w)))


/-- $\operatorname{ord}_w(2) = e(w \mid v)\,\operatorname{ord}_v(2)$. -/
lemma ordTwo_liesOver (w : HeightOneSpectrum (𝓞 L)) :
    ordTwo w = w.asIdeal.ramificationIdx (𝓞 F) * ordTwo (under (F := F) w) := by
  have h1 := valued_two (K := L) w
  have h2 := valued_two (K := F) (under (F := F) w)
  have : (2 : HeightOneSpectrum.adicCompletion L w) = algebraMap L _ (algebraMap F L 2) := by
    rw [map_ofNat, map_ofNat]
  rw [this, valued_algebraMap, valuation_algebraMap, ← valued_algebraMap, map_ofNat, h2,
    ← exp_nsmul, exp_inj] at h1
  simp only [smul_neg, nsmul_eq_mul] at h1
  have h3 : ((w.asIdeal.ramificationIdx (𝓞 F) : ℕ) : ℤ) * (ordTwo (under (F := F) w) : ℤ) =
      (ordTwo w : ℤ) := by linarith
  exact_mod_cast h3.symm

/-- $N(w)^{\operatorname{ord}_w 2} \le N(v)^{2\operatorname{ord}_v 2}$ (as $e f \le [L:F] = 2$). -/
lemma absNorm_pow_ordTwo_le (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm w.asIdeal ^ ordTwo w ≤
      Ideal.absNorm (under (F := F) w).asIdeal ^ (2 * ordTwo (under (F := F) w)) := by
  classical
  have hle : (under (F := F) w).asIdeal.ramificationIdx' w.asIdeal *
      (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal ≤ 2 := by
    rw [← sum_ef (L := L) (under (F := F) w)]
    exact Finset.single_le_sum (f := fun X => (under (F := F) w).asIdeal.ramificationIdx' X *
      (under (F := F) w).asIdeal.inertiaDeg' X) (fun _ _ => Nat.zero_le _)
      (mem_primesOverFinset (F := F) w)
  have := (under (F := F) w).isMaximal
  have := w.isMaximal
  have hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = w.asIdeal.inertiaDeg (𝓞 F) :=
    Ideal.inertiaDeg'_eq_inertiaDeg _ _
  have hN : Ideal.absNorm w.asIdeal =
      Ideal.absNorm (under (F := F) w).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) :=
    (Ideal.absNorm_pow_inertiaDeg (under (F := F) w).asIdeal w.asIdeal).symm
  rw [ramificationIdx'_eq (F := F), hf] at hle
  rw [hN, ordTwo_liesOver (F := F), ← pow_mul]
  have hpos : 1 ≤ Ideal.absNorm (under (F := F) w).asIdeal :=
    Nat.one_le_iff_ne_zero.mpr
      ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero (under (F := F) w).ne_bot))
  apply Nat.pow_le_pow_right hpos
  calc w.asIdeal.inertiaDeg (𝓞 F) * (w.asIdeal.ramificationIdx (𝓞 F) * ordTwo (under (F := F) w))
      = (w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F)) * ordTwo (under (F := F) w) := by ring
    _ ≤ 2 * ordTwo (under (F := F) w) := Nat.mul_le_mul_right _ hle

section Alg

variable (w : HeightOneSpectrum (𝓞 L))

local notation "Fv" => HeightOneSpectrum.adicCompletion F (under (F := F) w)
local notation "Lw" => HeightOneSpectrum.adicCompletion L w

/-- $L_w$ as an $F_v$-algebra via `compMap`. -/
@[implicit_reducible]
def compAlgebra : Algebra Fv Lw := (compMap (F := F) w).toAlgebra

attribute [local instance] compAlgebra

/-- $F \to F_v \to L_w$ is a scalar tower. -/
instance : IsScalarTower F Fv Lw := .of_algebraMap_eq fun c => by
  rw [RingHom.algebraMap_toAlgebra, compMap_algebraMap, HeightOneSpectrum.algebraMap_adicCompletion,
    HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

/-- $F_v$ acts continuously on $L_w$. -/
instance : ContinuousSMul Fv Lw where
  continuous_smul := ((continuous_compMap w).comp continuous_fst).mul continuous_snd

open scoped TensorProduct in
/-- The natural map $F_v \otimes_F L \to L_w$. -/
def tensorToCompletion : Fv ⊗[F] L →ₐ[Fv] Lw :=
  Algebra.TensorProduct.lift (Algebra.algHom Fv Fv Lw) (Algebra.algHom F L Lw)
    (fun _ _ ↦ mul_comm ..)

open scoped TensorProduct Valued in
/-- **$F_v \otimes_F L \to L_w$ is surjective** (its image is a finite-dimensional, hence closed, subspace
containing the dense image of $L$). -/
theorem tensorToCompletion_surjective : Function.Surjective (tensorToCompletion (F := F) w) := by
  let Φ := (tensorToCompletion (F := F) w).toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, tensorToCompletion, Algebra.algHom]⟩
  change Function.Surjective Φ
  have hc : IsClosed (Φ.range : Set Lw) := Submodule.closed_of_finiteDimensional Φ.range
  rw [← Set.range_eq_univ, ← Φ.coe_range, ← hc.closure_eq]
  exact h_dense.closure_range

end Alg


open scoped TensorProduct in
/-- **Structure of $M \otimes_F F(\sqrt a)$:** with $t = 1 \otimes s$, $t^2 = a$, every element is uniquely
$x_0 + x_1 t$, and the norm is $x_0^2 - a x_1^2$; the rank over $M$ is $2$. -/
theorem tensor_structure (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (M : Type*) [Field M] [Algebra F M] :
    ∃ t : M ⊗[F] L, t = (1 : M) ⊗ₜ s ∧ t * t = algebraMap M _ (algebraMap F M a) ∧
      (∀ y : M ⊗[F] L, ∃ x₀ x₁ : M, y = algebraMap M _ x₀ + algebraMap M _ x₁ * t) ∧
      (∀ x₀ x₁ : M, algebraMap M (M ⊗[F] L) x₀ + algebraMap M _ x₁ * t = 0 → x₀ = 0 ∧ x₁ = 0) ∧
      (∀ x₀ x₁ : M, Algebra.norm M (algebraMap M (M ⊗[F] L) x₀ + algebraMap M _ x₁ * t) =
        x₀ ^ 2 - algebraMap F M a * x₁ ^ 2) ∧
      Module.finrank M (M ⊗[F] L) = 2 := by
  classical
  have hinj := (algebraMap F L).injective
  have hli : LinearIndependent F ![(1:L), s] := by
    rw [LinearIndependent.pair_iff]
    intro c₀ c₁ h
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    by_cases h1 : c₁ = 0
    · subst h1; simp at h; exact ⟨h, rfl⟩
    · exfalso; apply hd
      refine ⟨-c₀ / c₁, ?_⟩
      apply hinj
      have h1' : algebraMap F L c₁ ≠ 0 := by simpa using h1
      have hs' : s = algebraMap F L (-c₀ / c₁) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [← hs, hs', map_mul, sq]
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1:L), s]) := by
    intro y _
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![b₀, b₁], ?_⟩
    simp [Fin.sum_univ_two, Algebra.smul_def]
  let bL := Module.Basis.mk hli hsp
  let bT := Algebra.TensorProduct.basis M bL
  set t : M ⊗[F] L := (1 : M) ⊗ₜ[F] s with ht
  set α := algebraMap F M a with hα
  have ht2 : t * t = algebraMap M _ α := by
    rw [ht, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← sq, hs, hα,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := L) a,
      Algebra.algebraMap_eq_smul_one (A := M) a, ← TensorProduct.smul_tmul]
    simp
  have hb0 : bT 0 = 1 := by simp [bT, bL, Algebra.TensorProduct.one_def]
  have hb1 : bT 1 = t := by simp [bT, bL, ht]
  have hrepr : ∀ c₀ c₁ : M, ∀ i, bT.repr (algebraMap M _ c₀ + algebraMap M _ c₁ * t) i = ![c₀, c₁] i := by
    intro c₀ c₁ i
    have : algebraMap M _ c₀ + algebraMap M _ c₁ * t = c₀ • bT 0 + c₁ • bT 1 := by
      rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [this]
    fin_cases i <;> simp
  refine ⟨t, ht, ht2, ?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨bT.repr y 0, bT.repr y 1, ?_⟩
    conv_lhs => rw [← bT.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  · intro x₀ x₁ h
    have h0 := hrepr x₀ x₁ 0
    have h1 := hrepr x₀ x₁ 1
    rw [h] at h0 h1
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at h0 h1
    exact ⟨by simpa using h0.symm, by simpa using h1.symm⟩
  · intro x₀ x₁
    rw [Algebra.norm_eq_matrix_det bT, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one]
    have : (algebraMap M _ x₀ + algebraMap M _ x₁ * t) * t = algebraMap M _ (α * x₁) + algebraMap M _ x₀ * t := by
      rw [map_mul]; linear_combination (algebraMap M _ x₁) * ht2
    rw [this, hrepr, hrepr, hrepr, hrepr]
    simp; ring
  · rw [Module.finrank_eq_card_basis bT]; simp


section D2

attribute [local instance] compAlgebra

open scoped TensorProduct

/-- **Local norms have index $\ge 2$ at a non-split finite place** ($a$ not a square in $F_v$): the norm
group $N((F_v \otimes_F L)^\times)$ is a proper subgroup of $F_v^\times$, indeed of index $\ge 2$.

*Proof.* $E = F_v \otimes_F L$ is a field, so $E \cong L_w$ (`tensorToCompletion_surjective`) and
$[E^\times : E^{\times 2}] = 4 N(w)^{\operatorname{ord}_w 2} \le 4 q^{2e}$ ($q^e = N(v)^{\operatorname{ord}_v 2}$,
`absNorm_pow_ordTwo_le`). The norm kills $F_v^\times E^{\times 2}$ modulo $F_v^{\times 2}$, and
$F_v^\times \cap E^{\times 2} = F_v^{\times 2} \cup a F_v^{\times 2}$, so
$[N E^\times : F_v^{\times 2}] \le [E^\times : F_v^\times E^{\times 2}] \le 4q^{2e}/(2q^e) = 2q^e$, while
$[F_v^\times : F_v^{\times 2}] = 4 q^e$ (`index_sq_completion`). -/
@[kb "milne2020cft" "Ch. III §2 (local norm index, n = 2) [unverified]"]
theorem two_le_index_norm (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (w : HeightOneSpectrum (𝓞 L))
    (hv : ¬ IsSquare (algebraMap F (HeightOneSpectrum.adicCompletion F (under (F := F) w)) a)) :
    2 ≤ (Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F (under (F := F) w)) :
      (HeightOneSpectrum.adicCompletion F (under (F := F) w)) ⊗[F] L →*
        HeightOneSpectrum.adicCompletion F (under (F := F) w))).range.index := by
  classical
  set Fv := HeightOneSpectrum.adicCompletion F (under (F := F) w)
  set E := Fv ⊗[F] L
  obtain ⟨t, -, ht2, hspanT, huniqT, hnormT, hrank⟩ := tensor_structure a hd s hs hspan Fv
  set α := algebraMap F Fv a with hα
  -- every nonzero element of E is a unit
  have hunit : ∀ y : E, y ≠ 0 → IsUnit y := by
    intro y hy
    obtain ⟨x₀, x₁, rfl⟩ := hspanT y
    have hN : x₀ ^ 2 - α * x₁ ^ 2 ≠ 0 := by
      intro h0
      by_cases hx1 : x₁ = 0
      · subst hx1
        have : x₀ = 0 := by simpa using h0
        subst this; simp at hy
      · apply hv
        refine ⟨x₀ / x₁, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx1 hx1)]
        linear_combination -h0
    have hmul : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
        (algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t)) = 1 := by
      have h1 : algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ * algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hN, map_one]
      have h2 : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t) = algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2) := by
        rw [map_sub, map_mul, map_pow, map_pow]
        linear_combination (-(algebraMap Fv E x₁) ^ 2) * ht2
      calc _ = algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ * ((algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t)) := by ring
        _ = 1 := by rw [h2, h1]
    exact IsUnit.of_mul_eq_one _ hmul
  set Lw := HeightOneSpectrum.adicCompletion L w
  have hΦinj : Function.Injective (tensorToCompletion (F := F) w) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨u, rfl⟩ := hunit y hy0
    have hu := (Units.map (tensorToCompletion (F := F) w : E →* Lw) u).ne_zero
    exact hu hy
  set eE : E ≃ₐ[Fv] Lw := AlgEquiv.ofBijective _ ⟨hΦinj, tensorToCompletion_surjective w⟩
  -- squares in E
  have hSqE : (powMonoidHom 2 : Eˣ →* Eˣ).range.index ≤
      4 * Ideal.absNorm (under (F := F) w).asIdeal ^ (2 * ordTwo (under (F := F) w)) := by
    have hmap : (powMonoidHom 2 : Eˣ →* Eˣ).range.map (Units.mapEquiv eE.toMulEquiv).toMonoidHom =
        (powMonoidHom 2 : Lwˣ →* Lwˣ).range := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨Units.mapEquiv eE.toMulEquiv y, by simp⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(Units.mapEquiv eE.toMulEquiv).symm y ^ 2, ⟨_, rfl⟩, ?_⟩
        simp only [powMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply]
    have := Subgroup.index_map_equiv (powMonoidHom 2 : Eˣ →* Eˣ).range (Units.mapEquiv eE.toMulEquiv)
    rw [← this]
    erw [hmap]
    rw [index_sq_completion (K := L) w]
    exact Nat.mul_le_mul_left 4 (absNorm_pow_ordTwo_le (F := F) w)
  have hSqE0 : (powMonoidHom 2 : Eˣ →* Eˣ).range.index ≠ 0 := by
    have hmap : (powMonoidHom 2 : Eˣ →* Eˣ).range.map (Units.mapEquiv eE.toMulEquiv).toMonoidHom =
        (powMonoidHom 2 : Lwˣ →* Lwˣ).range := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨Units.mapEquiv eE.toMulEquiv y, by simp⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(Units.mapEquiv eE.toMulEquiv).symm y ^ 2, ⟨_, rfl⟩, ?_⟩
        simp only [powMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply]
    have := Subgroup.index_map_equiv (powMonoidHom 2 : Eˣ →* Eˣ).range (Units.mapEquiv eE.toMulEquiv)
    rw [← this]
    erw [hmap]
    rw [index_sq_completion (K := L) w]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero w.ne_bot)))
  -- the counting
  set q := Ideal.absNorm (under (F := F) w).asIdeal ^ ordTwo (under (F := F) w) with hq
  have hq0 : 0 < q := pow_pos (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero (under (F := F) w).ne_bot))) _
  have hSqE' : (powMonoidHom 2 : Eˣ →* Eˣ).range.index ≤ 4 * q ^ 2 := by
    rw [hq, ← pow_mul, mul_comm (ordTwo _) 2]; exact hSqE
  have hSqF : (powMonoidHom 2 : Fvˣ →* Fvˣ).range.index = 4 * q := index_sq_completion _
  set Nm : Eˣ →* Fvˣ := Units.map (Algebra.norm Fv : E →* Fv)
  set incl : Fvˣ →* Eˣ := Units.map (algebraMap Fv E : Fv →* E)
  set SqF := (powMonoidHom 2 : Fvˣ →* Fvˣ).range
  set SqE := (powMonoidHom 2 : Eˣ →* Eˣ).range
  have hNincl : ∀ c : Fvˣ, Nm (incl c) = c ^ 2 := by
    intro c; ext
    simp only [Nm, incl, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
    rw [Algebra.norm_algebraMap, hrank]
  have hSqF_le : SqF ≤ Nm.range := by
    rintro _ ⟨c, rfl⟩; exact ⟨incl c, hNincl c⟩
  set M := incl.range ⊔ SqE
  have hM : M ≤ SqF.comap Nm := by
    rw [sup_le_iff]; constructor
    · rintro _ ⟨c, rfl⟩; exact ⟨c, (hNincl c).symm⟩
    · rintro _ ⟨y, rfl⟩; exact ⟨Nm y, by simp⟩
  -- C := preimage of the squares of E
  set C := SqE.comap incl
  have hSqFC : SqF ≤ C := by
    rintro _ ⟨c, rfl⟩; exact ⟨incl c, by simp⟩
  have hα0 : α ≠ 0 := by
    intro h; apply hv; rw [h]; exact ⟨0, by simp⟩
  set aU : Fvˣ := Units.mk0 α hα0
  have haC : aU ∈ C := by
    have ht0 : t ≠ 0 := by
      intro h; rw [h, zero_mul] at ht2
      exact hα0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Fv E)).mp ht2.symm)
    obtain ⟨tu, htu⟩ := hunit t ht0
    refine ⟨tu, ?_⟩
    ext; simp [incl, aU, htu, pow_two, ht2]
    rfl
  have haSq : aU ∉ SqF := by
    rintro ⟨c, hc⟩; apply hv
    refine ⟨(c : Fv), ?_⟩
    have := congrArg Units.val hc
    simpa [aU, pow_two, ← hα] using this.symm
  have hCidx : SqF.relIndex C = 2 := by
    rw [Subgroup.relIndex]
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨aU, haC⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    -- b ∈ C : b = y^2 in E
    obtain ⟨y, hy⟩ := b.2
    obtain ⟨x₀, x₁, hyx⟩ := hspanT (y : E)
    have hyb : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) ^ 2 = algebraMap Fv E ((b : Fvˣ) : Fv) := by
      have := congrArg Units.val hy
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, incl, Units.coe_map, MonoidHom.coe_coe] at this
      rw [← hyx, this]
    have hexp : algebraMap Fv E (x₀ ^ 2 + α * x₁ ^ 2 - ((b : Fvˣ) : Fv)) +
        algebraMap Fv E (2 * x₀ * x₁) * t = 0 := by
      rw [map_sub, ← hyb]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination (-(algebraMap Fv E x₁) ^ 2) * ht2
    obtain ⟨h1, h2⟩ := huniqT _ _ hexp
    have h2' : x₀ = 0 ∨ x₁ = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr h
    have hbval : ((b : Fvˣ) : Fv) = x₀ ^ 2 + α * x₁ ^ 2 := by linear_combination -h1
    have hsqiff : ∀ c : Fvˣ, c ∈ SqF ↔ IsSquare (c : Fv) := by
      intro c
      constructor
      · rintro ⟨d, rfl⟩; exact ⟨d, by simp [pow_two]⟩
      · rintro ⟨r, hr⟩
        have hr0 : r ≠ 0 := by rintro rfl; simp at hr
        exact ⟨Units.mk0 r hr0, by ext; simp [pow_two, hr]⟩
    have hmulval : (((b * ⟨aU, haC⟩ : C) : Fvˣ) : Fv) = ((b : Fvˣ) : Fv) * α := by
      simp [aU]
    rw [hsqiff, hsqiff, hmulval]
    have hb0 : ((b : Fvˣ) : Fv) ≠ 0 := Units.ne_zero _
    have hnot : ¬ (IsSquare (((b : Fvˣ) : Fv) * α) ∧ IsSquare ((b : Fvˣ) : Fv)) := by
      rintro ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩
      apply hv
      have hr2 : r₂ ≠ 0 := by rintro rfl; simp at h₂
      refine ⟨r₁ / r₂, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hr2 hr2), ← h₂, ← h₁]; ring
    rcases h2' with h0 | h0
    · -- b = α x₁^2
      subst h0
      have : IsSquare (((b : Fvˣ) : Fv) * α) := ⟨α * x₁, by rw [hbval]; ring⟩
      exact xor_iff_iff_not.mpr ⟨fun _ => fun h => hnot ⟨this, h⟩, fun _ => this⟩
    · subst h0
      have : IsSquare ((b : Fvˣ) : Fv) := ⟨x₀, by rw [hbval]; ring⟩
      rw [_root_.xor_comm]
      exact xor_iff_iff_not.mpr ⟨fun _ => fun h => hnot ⟨h, this⟩, fun _ => this⟩
  have hA := Subgroup.relIndex_mul_index hSqF_le
  have hB : SqF.relIndex Nm.range = (SqF.comap Nm).index := relIndex_range_eq_index_comap_mul Nm SqF
  have hC := Subgroup.index_dvd_of_le hM
  have hD := Subgroup.relIndex_mul_index (le_sup_right : SqE ≤ M)
  have hE : SqE.relIndex M = C.index := by
    rw [Subgroup.relIndex_sup_right, relIndex_range_eq_index_comap_mul]
  have hF := Subgroup.relIndex_mul_index hSqFC
  rw [hCidx, hSqF] at hF
  rw [hE] at hD
  rw [hB, hSqF] at hA
  have hCi : C.index = 2 * q := by omega
  rw [hCi] at hD
  have hM0 : M.index ≠ 0 := by
    intro h; rw [h, mul_zero] at hD; exact hSqE0 hD.symm
  have hMle : M.index ≤ 2 * q := by
    have h1 : 2 * q * M.index ≤ 4 * q ^ 2 := hD ▸ hSqE'
    have : 2 * q * M.index ≤ 2 * q * (2 * q) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hcle : (SqF.comap Nm).index ≤ 2 * q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hC).trans hMle
  by_contra hlt
  push Not at hlt
  have hpos : Nm.range.index ≠ 0 := by
    intro h; rw [h, mul_zero] at hA; omega
  have h1 : Nm.range.index = 1 := by omega
  rw [h1, mul_one] at hA
  omega

end D2

end QuadFormsKB.HN

end
