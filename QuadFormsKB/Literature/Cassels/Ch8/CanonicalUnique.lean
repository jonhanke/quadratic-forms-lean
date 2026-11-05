/-
# Cassels, Chapter 8, Theorem 3.1, uniqueness of the canonical form ($p \ne 2$)

Cassels proves uniqueness by splitting off $\langle 1\rangle$ or $\langle r\rangle$ and cancelling with Lemma 3.3. Here
the proof goes through O'Meara's lattice theory (the same content): for a canonical form the blocks of coordinates
give a Jordan splitting of $\mathbb Z_p^n$; by Theorem 91:9 (`OMeara.IsJordanSplitting.sameJordanType`) two Jordan
splittings of the same lattice have the same scales $p^{e(j)}\mathbb Z_p$ and ranks $m_j$, and by step 1 of the proof
of 92:2 (`OMeara.sameDisc_of_isJordanSplitting`) corresponding components have the same discriminant up to unit
squares, which determines $\varepsilon_j$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Canonical
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge

namespace QuadFormsKB.Cassels

open Matrix Submodule Module

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

private theorem bil_diag (d : Fin n → ℚ_[p]) (i k : Fin n) :
    OMeara.bil (qfForm (Matrix.diagonal d)) (Pi.single i (1 : ℚ_[p])) (Pi.single k (1 : ℚ_[p])) =
      if i = k then d i else 0 := by
  rw [bil_qfForm (by simp)]
  simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply]
  rcases eq_or_ne i k with rfl | h <;> simp [*, Ne.symm]

private theorem norm_p_zpow' (a : ℤ) : ‖(p : ℚ_[p]) ^ a‖ = (p : ℝ) ^ (-a) := by
  exact Padic.norm_p_zpow a

/-- `ℤ_p ∙ p^a ≤ ℤ_p ∙ p^b` iff `b ≤ a`. -/
private theorem span_pow_le_iff (a b : ℤ) :
    (ℤ_[p] ∙ (p : ℚ_[p]) ^ a) ≤ (ℤ_[p] ∙ (p : ℚ_[p]) ^ b) ↔ b ≤ a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : ‖(p : ℚ_[p]) ^ a‖ ≤ ‖(p : ℚ_[p]) ^ b‖ := by
      rw [← hc, Algebra.smul_def, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c)
    rw [norm_p_zpow', norm_p_zpow'] at h1
    have := (zpow_le_zpow_iff_right₀ hp1).1 h1
    omega
  · intro h
    have hn : ‖(p : ℚ_[p]) ^ (a - b)‖ ≤ 1 := by
      rw [norm_p_zpow']
      exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
    refine ⟨(p : ℤ_[p]) ^ (a - b).toNat, ?_⟩
    rw [Algebra.smul_def, PadicInt.algebraMap_apply]
    change ((p : ℤ_[p]) ^ (a - b).toNat : ℤ_[p]) * (p : ℚ_[p]) ^ b = _
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hp0]; congr 1; ring

private theorem span_pow_lt {a b : ℤ} (h : a < b) :
    (ℤ_[p] ∙ (p : ℚ_[p]) ^ b) < (ℤ_[p] ∙ (p : ℚ_[p]) ^ a) := by
  refine lt_of_le_of_ne ((span_pow_le_iff b a).2 h.le) fun he => ?_
  have := (span_pow_le_iff a b).1 he.ge
  omega

private theorem span_pow_inj {a b : ℤ} (h : (ℤ_[p] ∙ (p : ℚ_[p]) ^ a) = (ℤ_[p] ∙ (p : ℚ_[p]) ^ b)) : a = b :=
  le_antisymm ((span_pow_le_iff b a).1 h.ge) ((span_pow_le_iff a b).1 h.le)

/-- The lattice spanned by the standard basis vectors `e_i` with `z i = c`. -/
private noncomputable def blockLat (z : Fin n → ℤ) (c : ℤ) : Submodule ℤ_[p] (Fin n → ℚ_[p]) :=
  span ℤ_[p] (Set.range fun i : {i // z i = c} => (Pi.single (i : Fin n) (1 : ℚ_[p]) : Fin n → ℚ_[p]))

private theorem linIndep_single (z : Fin n → ℤ) (c : ℤ) :
    LinearIndependent ℤ_[p] (fun i : {i // z i = c} => (Pi.single (i : Fin n) (1 : ℚ_[p]) : Fin n → ℚ_[p])) := by
  have h := (Pi.basisFun ℚ_[p] (Fin n)).linearIndependent
  have h2 : LinearIndependent ℚ_[p] (fun i : {i // z i = c} => (Pi.basisFun ℚ_[p] (Fin n)) i.1) :=
    h.comp _ Subtype.val_injective
  simpa using h2.restrict_scalars' (R := ℤ_[p])

private noncomputable def blockBasis (z : Fin n → ℤ) (c : ℤ) : Basis {i // z i = c} ℤ_[p] (blockLat (p := p) z c) :=
  Basis.span (linIndep_single z c)

private theorem blockBasis_apply (z : Fin n → ℤ) (c : ℤ) (i : {i // z i = c}) :
    ((blockBasis (p := p) z c i : blockLat (p := p) z c) : Fin n → ℚ_[p]) = Pi.single (i : Fin n) 1 := by
  exact Basis.coe_span_apply (linIndep_single z c) i

private theorem gram_block (d : Fin n → ℚ_[p]) (z : Fin n → ℤ) (c : ℤ) :
    OMeara.gram (qfForm (Matrix.diagonal d)) (fun i => (blockBasis (p := p) z c i : Fin n → ℚ_[p])) =
      Matrix.diagonal (fun i : {i // z i = c} => d i) := by
  ext i k
  simp only [OMeara.gram, of_apply, blockBasis_apply, bil_diag, diagonal_apply]
  by_cases h : i = k
  · subst h; simp
  · have : (i : Fin n) ≠ k := fun h' => h (Subtype.ext h')
    simp [h, this]

private noncomputable def unitOf (u : ℚ_[p]) (h : ‖u‖ = 1) : ℤ_[p] :=
  ⟨u, (PadicInt.mem_subring_iff p).2 h.le⟩

private theorem coe_unitOf (u : ℚ_[p]) (h : ‖u‖ = 1) : ((unitOf u h : ℤ_[p]) : ℚ_[p]) = u := rfl

private theorem isModular_block (d u : Fin n → ℚ_[p]) (z : Fin n → ℤ) (hu : ∀ i, ‖u i‖ = 1)
    (hd : ∀ i, d i = (p : ℚ_[p]) ^ (z i) * u i) (c : ℤ) (hne : Nonempty {i // z i = c}) :
    OMeara.IsModular (qfForm (Matrix.diagonal d)) (ℤ_[p] ∙ (p : ℚ_[p]) ^ c) (blockLat z c) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine (OMeara.isModular_iff_gram _ (blockBasis z c) (zpow_ne_zero c hp0)).2 ⟨hne, ?_⟩
  let ut : {i // z i = c} → ℤ_[p] := fun i => unitOf (u i) (hu i)
  refine ⟨Matrix.diagonal ut, ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ?_
    exact PadicInt.isUnit_iff.2 (by
      show ‖unitOf (u i) (hu i)‖ = 1
      rw [PadicInt.norm_def, coe_unitOf]; exact hu i)
  · rw [gram_block]
    ext i k
    by_cases h : i = k
    · subst h
      have hz : z i = c := i.2
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.map_apply, ut, PadicInt.algebraMap_apply,
        smul_eq_mul]
      rw [hd, hz]
      rfl
    · simp [h]

private theorem blockLat_le (z : Fin n → ℤ) (c : ℤ) : blockLat (p := p) z c ≤ zpLat p n := by
  refine span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact subset_span ⟨i.1, by simp⟩

private theorem fg_blockLat (z : Fin n → ℤ) (c : ℤ) : (blockLat (p := p) z c).FG :=
  fg_span (Set.finite_range _)

private theorem bil_eq_zero_of_span (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) {S T : Set (Fin n → ℚ_[p])}
    (h : ∀ x ∈ S, ∀ y ∈ T, OMeara.bil Q x y = 0) :
    ∀ x ∈ span ℤ_[p] S, ∀ y ∈ span ℤ_[p] T, OMeara.bil Q x y = 0 := by
  intro x hx y hy
  refine span_induction (p := fun x _ => OMeara.bil Q x y = 0) ?_ (by simp [OMeara.bil]) ?_ ?_ hx
  · intro x hxS
    refine span_induction (p := fun y _ => OMeara.bil Q x y = 0) (fun y hyT => h x hxS y hyT)
      (by simp [OMeara.bil]) ?_ ?_ hy
    · intro a b _ _ ha hb
      rw [OMeara.bil_add_right, ha, hb, add_zero]
    · intro r a _ ha
      rw [OMeara.bil_rsmul_right, ha, mul_zero]
  · intro a b _ _ ha hb
    rw [OMeara.bil_add_left, ha, hb, add_zero]
  · intro r a _ ha
    rw [OMeara.bil_rsmul_left, ha, mul_zero]

private theorem isJordanSplitting_blocks (d u : Fin n → ℚ_[p]) (z : Fin n → ℤ) (hu : ∀ i, ‖u i‖ = 1)
    (hd : ∀ i, d i = (p : ℚ_[p]) ^ (z i) * u i) {t : ℕ} (Zs : Fin t → ℤ) (hZ : StrictMono Zs)
    (hcov : ∀ i, ∃ j, z i = Zs j) (hne : ∀ j, ∃ i, z i = Zs j) :
    OMeara.IsJordanSplitting (qfForm (Matrix.diagonal d)) (zpLat p n) (fun j => blockLat z (Zs j)) := by
  have hmod : ∀ j, OMeara.IsModular (qfForm (Matrix.diagonal d)) (ℤ_[p] ∙ (p : ℚ_[p]) ^ (Zs j))
      (blockLat z (Zs j)) := fun j => by
    obtain ⟨i, hi⟩ := hne j
    exact isModular_block d u z hu hd _ ⟨⟨i, hi⟩⟩
  have hsc : ∀ j, OMeara.scale (qfForm (Matrix.diagonal d)) (blockLat z (Zs j)) =
      ℤ_[p] ∙ (p : ℚ_[p]) ^ (Zs j) := fun j => (hmod j).2.1
  have horth : ∀ j k, j ≠ k → ∀ x ∈ blockLat z (Zs j), ∀ y ∈ blockLat z (Zs k),
      OMeara.bil (qfForm (Matrix.diagonal d)) x y = 0 := by
    intro j k hjk
    refine bil_eq_zero_of_span _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : (a : Fin n) ≠ b := fun h => hjk (hZ.injective (a.2.symm.trans ((congrArg z h).trans b.2)))
    rw [bil_diag]; simp [hab]
  refine ⟨⟨horth, OMeara.iSupIndep_of_orth _ horth fun j =>
      (hmod j).isRegular _ (fg_blockLat _ _), ?_⟩, fun j => by rw [hsc j]; exact hmod j, ?_⟩
  · refine le_antisymm (iSup_le fun j => blockLat_le _ _) ?_
    refine span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hcov i
    exact Submodule.mem_iSup_of_mem j (subset_span ⟨⟨i, hj⟩, by simp⟩)
  · intro j k hjk
    simp only [hsc]
    exact span_pow_lt (hZ hjk)

section transport

variable (Q Q' : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]))

private theorem bil_comp (hσ : ∀ x, Q (σ x) = Q' x) (x y : Fin n → ℚ_[p]) :
    OMeara.bil Q (σ x) (σ y) = OMeara.bil Q' x y := by
  rw [OMeara.bil_eq_half, OMeara.bil_eq_half, ← map_add, hσ, hσ, hσ]

private theorem isometricLat_map (hσ : ∀ x, Q (σ x) = Q' x) (J : Submodule ℤ_[p] (Fin n → ℚ_[p])) :
    OMeara.IsometricLat Q' Q J (OMeara.latMap σ J) :=
  ⟨Submodule.equivMapOfInjective ((σ : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])).restrictScalars ℤ_[p])
    σ.injective J, fun x => hσ x⟩

/-- Isometries between two forms carry Jordan splittings to Jordan splittings. -/
private theorem isJordanSplitting_transport (hσ : ∀ x, Q (σ x) = Q' x) {M : Submodule ℤ_[p] (Fin n → ℚ_[p])}
    (hfg : M.FG) {t : ℕ} {Ls : Fin t → Submodule ℤ_[p] (Fin n → ℚ_[p])}
    (hL : OMeara.IsJordanSplitting Q' M Ls) :
    OMeara.IsJordanSplitting Q (OMeara.latMap σ M) (fun i => OMeara.latMap σ (Ls i)) := by
  have hfgi : ∀ i, (Ls i).FG := fun i => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hsc : ∀ i, OMeara.scale Q (OMeara.latMap σ (Ls i)) = OMeara.scale Q' (Ls i) :=
    fun i => (isometricLat_map Q Q' σ hσ (Ls i)).scale_eq Q' Q (hfgi i)
  have hmod : ∀ i, OMeara.IsModular Q (OMeara.scale Q (OMeara.latMap σ (Ls i))) (OMeara.latMap σ (Ls i)) := by
    intro i; rw [hsc]
    exact (isometricLat_map Q Q' σ hσ (Ls i)).isModular Q' Q (hfgi i) (hL.modular i)
  have horth : ∀ i j, i ≠ j → ∀ x ∈ OMeara.latMap σ (Ls i), ∀ y ∈ OMeara.latMap σ (Ls j),
      OMeara.bil Q x y = 0 := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [bil_comp Q Q' σ hσ]; exact hL.split.orth i j hij x hx y hy
  refine ⟨⟨horth, OMeara.iSupIndep_of_orth Q horth fun i => (hmod i).isRegular Q ?_, ?_⟩, hmod, ?_⟩
  · exact (hfgi i).map _
  · rw [← hL.split.iSup_eq, OMeara.latMap, Submodule.map_iSup]
  · intro i j hij; simp only [hsc]; exact hL.scale_strictAnti hij

private theorem det_gram_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) {L : Submodule ℤ_[p] (Fin n → ℚ_[p])} (B : Basis ι ℤ_[p] L)
    (e : ι ≃ κ) :
    (OMeara.gram Q fun k => ((B.reindex e k : L) : Fin n → ℚ_[p])).det =
      (OMeara.gram Q fun i => ((B i : L) : Fin n → ℚ_[p])).det := by
  have : (OMeara.gram Q fun k => ((B.reindex e k : L) : Fin n → ℚ_[p])) =
      (OMeara.gram Q fun i => ((B i : L) : Fin n → ℚ_[p])).submatrix e.symm e.symm := by
    ext i j; simp [OMeara.gram]
  rw [this, Matrix.det_submatrix_equiv_self]

/-- Discriminants of corresponding blocks, from `SameDisc`. -/
private theorem exists_sq_of_sameDisc (d d' : Fin n → ℚ_[p]) (z z' : Fin n → ℤ) (c c' : ℤ)
    (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]))
    (hσ : ∀ x, qfForm (Matrix.diagonal d) (σ x) = qfForm (Matrix.diagonal d') x)
    (h : OMeara.SameDisc (qfForm (Matrix.diagonal d)) (qfForm (Matrix.diagonal d)) (blockLat z c)
      (OMeara.latMap σ (blockLat z' c'))) :
    ∃ ε : ℤ_[p], IsUnit ε ∧ ∏ i : {i // z i = c}, d i = (ε : ℚ_[p]) ^ 2 * ∏ i : {i // z' i = c'}, d' i := by
  set Q := qfForm (Matrix.diagonal d)
  set Q' := qfForm (Matrix.diagonal d')
  let f := Submodule.equivMapOfInjective ((σ : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])).restrictScalars ℤ_[p])
    σ.injective (blockLat (p := p) z' c')
  let b0 := blockBasis (p := p) z c
  let b0' := (blockBasis (p := p) z' c').map f
  have hr : Module.finrank ℤ_[p] (blockLat (p := p) z c) = Fintype.card {i // z i = c} :=
    Module.finrank_eq_card_basis b0
  have hr' : Module.finrank ℤ_[p] (OMeara.latMap σ (blockLat (p := p) z' c')) = Fintype.card {i // z' i = c'} :=
    Module.finrank_eq_card_basis b0'
  let b := b0.reindex (Fintype.equivFinOfCardEq hr.symm)
  let b' := b0'.reindex (Fintype.equivFinOfCardEq hr'.symm)
  obtain ⟨ε, hε, hd⟩ := OMeara.SameDisc.forall Q Q h b b'
  refine ⟨ε, hε, ?_⟩
  have h1 : (OMeara.gram Q fun i => ((b i : blockLat (p := p) z c) : Fin n → ℚ_[p])).det =
      ∏ i : {i // z i = c}, d i := by
    rw [det_gram_reindex, gram_block, Matrix.det_diagonal]
  have h2 : (OMeara.gram Q fun i => ((b' i : OMeara.latMap σ (blockLat (p := p) z' c')) : Fin n → ℚ_[p])).det =
      ∏ i : {i // z' i = c'}, d' i := by
    rw [det_gram_reindex]
    have : (OMeara.gram Q fun i => ((b0' i : OMeara.latMap σ (blockLat (p := p) z' c')) : Fin n → ℚ_[p])) =
        OMeara.gram Q' fun i => ((blockBasis (p := p) z' c' i : blockLat (p := p) z' c') : Fin n → ℚ_[p]) := by
      ext i j
      simp only [OMeara.gram, Matrix.of_apply, b0', Basis.map_apply, f]
      exact bil_comp Q Q' σ hσ _ _
    rw [this, gram_block, Matrix.det_diagonal]
  rw [h1, h2] at hd
  simpa using hd

end transport

private theorem finrank_blockLat (z : Fin n → ℤ) (c : ℤ) :
    Module.finrank ℤ_[p] (blockLat (p := p) z c) = Fintype.card {i // z i = c} :=
  Module.finrank_eq_card_basis (blockBasis z c)

private theorem finrank_latMap (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]))
    (L : Submodule ℤ_[p] (Fin n → ℚ_[p])) : Module.finrank ℤ_[p] (OMeara.latMap σ L) = Module.finrank ℤ_[p] L :=
  (Submodule.equivMapOfInjective ((σ : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])).restrictScalars ℤ_[p])
    σ.injective L).symm.finrank_eq

/-- Two diagonal block data related by an isometry mapping `ℤ_p^n` onto itself have the same block structure. -/
theorem generic_unique (hp2 : p ≠ 2) (d u d' u' : Fin n → ℚ_[p]) (z z' : Fin n → ℤ)
    (hu : ∀ i, ‖u i‖ = 1) (hd : ∀ i, d i = (p : ℚ_[p]) ^ (z i) * u i)
    (hu' : ∀ i, ‖u' i‖ = 1) (hd' : ∀ i, d' i = (p : ℚ_[p]) ^ (z' i) * u' i)
    {t t' : ℕ} (Zs : Fin t → ℤ) (hZ : StrictMono Zs) (hcov : ∀ i, ∃ j, z i = Zs j) (hne : ∀ j, ∃ i, z i = Zs j)
    (Zs' : Fin t' → ℤ) (hZ' : StrictMono Zs') (hcov' : ∀ i, ∃ j, z' i = Zs' j) (hne' : ∀ j, ∃ i, z' i = Zs' j)
    (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]))
    (hσ : ∀ x, qfForm (Matrix.diagonal d) (σ x) = qfForm (Matrix.diagonal d') x)
    (hσM : OMeara.latMap σ (zpLat p n) = zpLat p n) :
    ∃ h : t = t', ∀ j : Fin t, Zs j = Zs' (Fin.cast h j) ∧
      Fintype.card {i // z i = Zs j} = Fintype.card {i // z' i = Zs' (Fin.cast h j)} ∧
      ∃ ε : ℤ_[p], IsUnit ε ∧
        ∏ i : {i // z i = Zs j}, d i = (ε : ℚ_[p]) ^ 2 * ∏ i : {i // z' i = Zs' (Fin.cast h j)}, d' i := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofFinite _
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) := by norm_num
    rw [this, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
  have hfg : (zpLat p n).FG := fg_span (Set.finite_range _)
  have hL := isJordanSplitting_blocks d u z hu hd Zs hZ hcov hne
  have hL' := isJordanSplitting_blocks d' u' z' hu' hd' Zs' hZ' hcov' hne'
  have hK := isJordanSplitting_transport (qfForm (Matrix.diagonal d)) (qfForm (Matrix.diagonal d')) σ hσ hfg hL'
  rw [hσM] at hK
  obtain ⟨htt, hall⟩ := hL.sameJordanType _ hfg hK
  refine ⟨htt, fun j => ?_⟩
  obtain ⟨hsc, hrk, -⟩ := hall j
  have hfg' : ∀ k, (blockLat (p := p) z' (Zs' k)).FG := fun k => fg_blockLat _ _
  have hsc1 : OMeara.scale (qfForm (Matrix.diagonal d)) (blockLat z (Zs j)) = ℤ_[p] ∙ (p : ℚ_[p]) ^ (Zs j) := by
    obtain ⟨i, hi⟩ := hne j
    exact (isModular_block d u z hu hd _ ⟨⟨i, hi⟩⟩).2.1
  have hsc2 : OMeara.scale (qfForm (Matrix.diagonal d))
      (OMeara.latMap σ (blockLat z' (Zs' (Fin.cast htt j)))) = ℤ_[p] ∙ (p : ℚ_[p]) ^ (Zs' (Fin.cast htt j)) := by
    obtain ⟨i, hi⟩ := hne' (Fin.cast htt j)
    rw [(isometricLat_map _ _ σ hσ _).scale_eq _ _ (hfg' _)]
    exact (isModular_block d' u' z' hu' hd' _ ⟨⟨i, hi⟩⟩).2.1
  refine ⟨span_pow_inj (hsc1.symm.trans (hsc.trans hsc2)), ?_, ?_⟩
  · have := hrk
    simp only [finrank_blockLat, finrank_latMap] at this
    exact this
  · have hsd := OMeara.sameDisc_of_isJordanSplitting _ h2 hfg hL hK j (Fin.cast htt j) (by simp)
    exact exists_sq_of_sameDisc d d' z z' _ _ σ hσ hsd

/-! ### The tagged list of diagonal entries of a canonical form -/

/-- The diagonal entries of a canonical form, as pairs `(e, u)` standing for `p ^ e * u`. -/
private noncomputable def tag (r : ℚ_[p]) : List CanonBlock → List (ℤ × ℚ_[p])
  | [] => []
  | b :: D => (List.replicate (b.m - 1) (b.e, (1 : ℚ_[p])) ++ [(b.e, r ^ (b.ε : ℕ))]) ++ tag r D

private theorem tag_map (r : ℚ_[p]) (D : List CanonBlock) :
    (tag r D).map (fun x => (p : ℚ_[p]) ^ x.1 * x.2) = canonEntries p r D := by
  induction D with
  | nil => simp [tag, canonEntries]
  | cons b D ih =>
    simp only [canonEntries] at ih ⊢
    simp only [tag, List.flatMap_cons, List.map_append, List.map_replicate, List.map_cons, List.map_nil, mul_one, ih]

private theorem tag_norm {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (D : List CanonBlock) : ∀ x ∈ tag r D, ‖x.2‖ = 1 := by
  induction D with
  | nil => simp [tag]
  | cons b D ih =>
    intro x hx
    simp only [tag, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with (⟨-, rfl⟩ | rfl) | hx
    · simp
    · simp [hr1]
    · exact ih x hx

private theorem tag_exp (r : ℚ_[p]) (D : List CanonBlock) : ∀ x ∈ tag r D, ∃ b ∈ D, x.1 = b.e := by
  induction D with
  | nil => simp [tag]
  | cons b D ih =>
    intro x hx
    simp only [tag, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with (⟨-, rfl⟩ | rfl) | hx
    · exact ⟨b, List.mem_cons_self, rfl⟩
    · exact ⟨b, List.mem_cons_self, rfl⟩
    · obtain ⟨b', hb', h⟩ := ih x hx
      exact ⟨b', List.mem_cons_of_mem _ hb', h⟩

private theorem tag_exists (r : ℚ_[p]) (D : List CanonBlock) : ∀ b ∈ D, ∃ x ∈ tag r D, x.1 = b.e := by
  induction D with
  | nil => simp
  | cons b D ih =>
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact ⟨(b'.e, r ^ (b'.ε : ℕ)), by simp [tag], rfl⟩
    · obtain ⟨x, hx, h⟩ := ih b' hb'
      exact ⟨x, by simp [tag, hx], h⟩

private theorem tag_count (r : ℚ_[p]) (c : ℤ) (D : List CanonBlock) (hD : ∀ b ∈ D, 1 ≤ b.m) :
    ((tag r D).map fun x => if x.1 = c then 1 else 0).sum =
      (D.map fun b => if b.e = c then b.m else 0).sum := by
  induction D with
  | nil => simp [tag]
  | cons b D ih =>
    have hb := hD b List.mem_cons_self
    have := ih fun b' hb' => hD b' (List.mem_cons_of_mem _ hb')
    by_cases h : b.e = c
    · simp [tag, h, List.map_replicate, this]
      omega
    · simp [tag, h, List.map_replicate, this]

private theorem tag_prod (r : ℚ_[p]) (c : ℤ) (D : List CanonBlock) (hD : ∀ b ∈ D, 1 ≤ b.m) :
    ((tag r D).map fun x => if x.1 = c then (p : ℚ_[p]) ^ x.1 * x.2 else 1).prod =
      (D.map fun b => if b.e = c then ((p : ℚ_[p]) ^ b.e) ^ b.m * r ^ (b.ε : ℕ) else 1).prod := by
  induction D with
  | nil => simp [tag]
  | cons b D ih =>
    have hb := hD b List.mem_cons_self
    have := ih fun b' hb' => hD b' (List.mem_cons_of_mem _ hb')
    by_cases h : b.e = c
    · simp only [tag, List.map_append, List.map_replicate, List.map_cons, List.map_nil, List.prod_append,
        List.prod_replicate, List.prod_cons, List.prod_nil, if_pos h, this, mul_one]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hb
      rw [hm]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    · simp [tag, h, List.map_replicate, this]

private theorem canon_strictMono {D : List CanonBlock} (hD : IsCanon D) :
    StrictMono (fun j : Fin D.length => D[j].e) := by
  have hp : D.Pairwise (fun a b => a.e < b.e) := by
    have : IsTrans CanonBlock (fun a b => a.e < b.e) := ⟨fun a b c h1 h2 => h1.trans h2⟩
    exact List.isChain_iff_pairwise.1 hD.1
  intro j k hjk
  exact List.pairwise_iff_getElem.1 hp j k j.2 k.2 hjk

@[to_additive]
private theorem prod_single {D : List CanonBlock} (hZ : StrictMono (fun j : Fin D.length => D[j].e))
    (j : Fin D.length) {M : Type*} [CommMonoid M] (g : CanonBlock → M) :
    (D.map fun b => if b.e = D[j].e then g b else 1).prod = g D[j] := by
  rw [← Fin.prod_univ_fun_getElem D]
  rw [Finset.prod_eq_single j]
  · simp
  · intro k _ hk
    rw [if_neg]
    exact fun h => hk (hZ.injective h)
  · simp

theorem canon_data {r : ℚ_[p]} (hr1 : ‖r‖ = 1) {D : List CanonBlock} (hD : IsCanon D)
    (h : (canonEntries p r D).length = n) :
    ∃ (z : Fin n → ℤ) (u : Fin n → ℚ_[p]),
      canonMat r D h = Matrix.diagonal (fun i => (p : ℚ_[p]) ^ (z i) * u i) ∧ (∀ i, ‖u i‖ = 1) ∧
      (∀ i, ∃ j : Fin D.length, z i = D[j].e) ∧ (∀ j : Fin D.length, ∃ i, z i = D[j].e) ∧
      (∀ j : Fin D.length, Fintype.card {i // z i = D[j].e} = D[j].m ∧
        ∏ i : {i // z i = D[j].e}, ((p : ℚ_[p]) ^ (z i) * u i) =
          ((p : ℚ_[p]) ^ D[j].e) ^ D[j].m * r ^ (D[j].ε : ℕ)) := by
  classical
  have hlen : (tag r D).length = n := by
    rw [← h, ← tag_map r D, List.length_map]
  subst hlen
  have hm : ∀ b ∈ D, 1 ≤ b.m := hD.2
  have hZ := canon_strictMono hD
  set z : Fin (tag r D).length → ℤ := fun i => ((tag r D)[i]).1 with hz
  set u : Fin (tag r D).length → ℚ_[p] := fun i => ((tag r D)[i]).2 with hu
  refine ⟨z, u, ?_, ?_, ?_, ?_, ?_⟩
  · unfold canonMat
    congr 1
    funext i
    simp [← tag_map]
    rfl
  · intro i
    exact tag_norm hr1 D _ (List.getElem_mem _)
  · intro i
    obtain ⟨b, hb, hb'⟩ := tag_exp r D _ (List.getElem_mem i.2)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
    exact ⟨⟨j, hj⟩, hb'⟩
  · intro j
    obtain ⟨x, hx, hx'⟩ := tag_exists r D D[j] (List.getElem_mem _)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨⟨i, hi⟩, hx'⟩
  · intro j
    constructor
    · rw [Fintype.card_subtype, Finset.card_filter]
      have := tag_count r D[j].e D hm
      rw [← Fin.sum_univ_fun_getElem] at this
      exact this.trans (sum_single hZ j (fun b => b.m))
    · have := tag_prod r D[j].e D hm
      rw [← Fin.prod_univ_fun_getElem] at this
      rw [← Finset.prod_subtype (Finset.univ.filter fun i => z i = D[j].e) (fun i => by simp)
        (fun i => (p : ℚ_[p]) ^ (z i) * u i), Finset.prod_filter]
      exact this.trans (prod_single hZ j (fun b => ((p : ℚ_[p]) ^ b.e) ^ b.m * r ^ (b.ε : ℕ)))

private noncomputable def intOf (a : ℚ_[p]) (h : ‖a‖ ≤ 1) : ℤ_[p] := ⟨a, (PadicInt.mem_subring_iff p).2 h⟩

theorem isIntVec_mulVec (S : Matrix (Fin n) (Fin n) ℤ_[p]) {x : Fin n → ℚ_[p]} (hx : IsIntVec x) :
    IsIntVec ((S.map PadicInt.Coe.ringHom) *ᵥ x) := by
  intro i
  let x' : Fin n → ℤ_[p] := fun j => intOf (x j) (hx j)
  have hx' : x = PadicInt.Coe.ringHom ∘ x' := rfl
  have := RingHom.map_mulVec PadicInt.Coe.ringHom S x' i
  rw [hx']
  change ‖(S.map PadicInt.Coe.ringHom *ᵥ (PadicInt.Coe.ringHom ∘ x')) i‖ ≤ 1
  rw [← this]
  exact PadicInt.norm_le_one _

theorem qf_conj' (A W : Matrix (Fin n) (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) :
    qf (Wᵀ * A * W) x = qf A (W *ᵥ x) := by
  simp only [qf, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Cassels, Ch. 8, Theorem 3.1, uniqueness** ($p \ne 2$): *no two distinct forms (3.11) are
$\mathbb Z_p$-equivalent.* -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, p. 117 (uniqueness)"]
theorem canonical_unique (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r) {D D' : List CanonBlock}
    (hD : IsCanon D) (hD' : IsCanon D') (h : (canonEntries p r D).length = n)
    (h' : (canonEntries p r D').length = n) (heq : ZpEquiv (canonMat r D h) (canonMat r D' h')) : D = D' := by
  obtain ⟨z, u, hA, hu, hcov, hne, hblk⟩ := canon_data hr1 hD h
  obtain ⟨z', u', hA', hu', hcov', hne', hblk'⟩ := canon_data hr1 hD' h'
  obtain ⟨T, hT⟩ := heq
  rw [hA, hA'] at hT
  set W : Matrix (Fin n) (Fin n) ℚ_[p] := T.val.map PadicInt.Coe.ringHom with hW
  set W' : Matrix (Fin n) (Fin n) ℚ_[p] := (T⁻¹).val.map PadicInt.Coe.ringHom with hW'
  have hWW' : W * W' = 1 := by
    rw [hW, hW', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hW'W : W' * W = 1 := by
    rw [hW, hW', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  let σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin W) (Matrix.mulVecLin W')
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hWW'])
      (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hW'W])
  have hσx : ∀ x, σ x = W *ᵥ x := fun x => rfl
  have hσ : ∀ x, qfForm (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i) (σ x) =
      qfForm (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z' i) * u' i) x := by
    intro x
    rw [qfForm_apply, qfForm_apply, ← hT, qf_conj', hσx]
  have hσM : OMeara.latMap σ (zpLat p n) = zpLat p n := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_zpLat.2 (isIntVec_mulVec T.val (mem_zpLat.1 hx))
    · intro hy
      refine ⟨σ.symm y, mem_zpLat.2 (isIntVec_mulVec (T⁻¹).val (mem_zpLat.1 hy)), ?_⟩
      simp
  obtain ⟨htt, hall⟩ := generic_unique hp2 _ u _ u' z z' hu (fun i => rfl) hu' (fun i => rfl)
    (fun j : Fin D.length => D[j].e) (canon_strictMono hD) hcov hne
    (fun j : Fin D'.length => D'[j].e) (canon_strictMono hD') hcov' hne' σ hσ hσM
  refine List.ext_getElem htt fun k hk hk' => ?_
  obtain ⟨he, hcard, ε₀, hε₀, hprod⟩ := hall ⟨k, hk⟩
  have hm : D[k].m = D'[k].m := ((hblk ⟨k, hk⟩).1.symm.trans (hcard.trans (hblk' (Fin.cast htt ⟨k, hk⟩)).1) :)
  have he' : D[k].e = D'[k].e := he
  rw [(hblk ⟨k, hk⟩).2, (hblk' (Fin.cast htt ⟨k, hk⟩)).2] at hprod
  have hpow : ((p : ℚ_[p]) ^ D[k].e) ^ D[k].m ≠ 0 := by
    have : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    positivity
  change ((p : ℚ_[p]) ^ D[k].e) ^ D[k].m * r ^ (D[k].ε : ℕ) =
    (ε₀ : ℚ_[p]) ^ 2 * (((p : ℚ_[p]) ^ D'[k].e) ^ D'[k].m * r ^ (D'[k].ε : ℕ)) at hprod
  rw [← he', ← hm] at hprod
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hr1; exact zero_ne_one hr1
  have hε0 : (ε₀ : ℚ_[p]) ≠ 0 := by
    intro h0
    have := (PadicInt.isUnit_iff.1 hε₀)
    rw [PadicInt.norm_def, h0, norm_zero] at this
    exact zero_ne_one this
  have hkey : r ^ (D[k].ε : ℕ) = (ε₀ : ℚ_[p]) ^ 2 * r ^ (D'[k].ε : ℕ) := by
    apply mul_left_cancel₀ hpow
    linear_combination hprod
  have hε : D[k].ε = D'[k].ε := by
    by_contra hne
    have h1 := D[k].ε.isLt
    have h2 := D'[k].ε.isLt
    have hv : (D[k].ε : ℕ) ≠ D'[k].ε := fun h => hne (Fin.ext h)
    rcases (by omega : ((D[k].ε : ℕ) = 0 ∧ (D'[k].ε : ℕ) = 1) ∨ ((D[k].ε : ℕ) = 1 ∧ (D'[k].ε : ℕ) = 0)) with
      ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, b] at hkey
      apply hr
      refine ⟨(ε₀ : ℚ_[p])⁻¹, ?_⟩
      field_simp
      linear_combination -hkey
    · rw [a, b] at hkey
      exact hr ⟨ε₀, by linear_combination hkey⟩
  have key : ∀ a b : CanonBlock, a.e = b.e → a.ε = b.ε → a.m = b.m → a = b := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h1 h2 h3
    simp_all
  exact key _ _ he' hε hm

end QuadFormsKB.Cassels
