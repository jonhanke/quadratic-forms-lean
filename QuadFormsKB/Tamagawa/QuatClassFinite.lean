/-
# Finiteness of the left ideal class set of a maximal order

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$ a division algebra ($ab \ne 0$), $\mathcal O$ a maximal $\mathcal O_F$-order.

* `exists_ideal_basis`: a left ideal $J$ with $\operatorname{nrd}(J) \ne 0$ is a free $\mathcal O_F$-module of rank 4 (a lattice, `IsLattice.rank'`),
  with basis $f_j = \sum_iB_{ij}e_i$, $\det B \ne 0$.
* `exists_small_mem`: $J$ contains $x \ne 0$ with $|N(\operatorname{nrd}x)| \le C\,N(\operatorname{nrd}J)$, $C$ depending only on $(\mathcal O, e)$.
  *Proof:* the pigeonhole of O'Meara 103:2 (`ClassFin.exists_pigeon`) with $T^{4d} > |N\det B| = N(\operatorname{nrd}J)^2$ (the
  `span_det_eq_sq`) gives $\xi \ne 0$ with $B\xi$ of $\omega$-coordinates $< T$, and $|\varphi(\operatorname{nrd}x)| \le C_\varphi T^2$ at every
  embedding.
* **`finite_classes`**: the class set is finite. *Proof:* $J' = \nu^{-1}J\bar x$ is an integral ideal in the class of $J$
  (`mem_colon_iff`) with $N(\operatorname{nrd}J') = |N\operatorname{nrd}x|/N(\nu) \le C$; there are finitely many integral ideals of bounded
  reduced norm (`card_ideal_nrd_eq`).

Source: Voight, *Quaternion Algebras* (2021), Thm. 17.5.? / Lemma 17.7.? (finiteness of the class set via a Minkowski bound, there via
Minkowski's convex body theorem; here via O'Meara's pigeonhole, 103:2); locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatIdealInverse
import QuadFormsKB.Lattices.ClassFiniteAux

open NumberField IsDedekindDomain Quaternion IsLocalization

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

section IdealBasis

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **The $\mathcal O_F$-lattice of a left ideal** $J \subseteq D$. -/
def idealLat (J : Ideal O) : Submodule (𝓞 F) (QuatF F a b) where
  carrier := idealSet J
  add_mem' := add_mem_idealSet
  zero_mem' := zero_mem_idealSet J
  smul_mem' c x hx := by
    have h := mul_mem_idealSet (O.algebraMap_mem c) hx
    convert h using 1
    exact Algebra.smul_def c x

theorem mem_idealLat {J : Ideal O} {x : QuatF F a b} : x ∈ idealLat J ↔ x ∈ idealSet J := Iff.rfl

theorem idealLat_le (J : Ideal O) : idealLat J ≤ Subalgebra.toSubmodule O := fun _ hx => idealSet_subset J hx

/-- A left ideal with $\operatorname{nrd}(J) = (\nu) \ne 0$ is an $\mathcal O_F$-lattice in $D$ (it contains $\nu\mathcal O$). -/
theorem isLattice_idealLat (hO : IsOrder (𝓞 F) F O) {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0)
    (hν : leftNrdIdeal J = Ideal.span {ν}) : Submodule.IsLattice F (idealLat J) := by
  refine ⟨Submodule.FG.of_le hO.fg (idealLat_le J), ?_⟩
  have hνJ : algebraMap (𝓞 F) O ν ∈ J :=
    algebraMap_mem_of_mem_leftNrdIdeal hO J (by rw [hν]; exact Ideal.mem_span_singleton_self ν)
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
  refine eq_top_iff.2 (hO.span ▸ Submodule.span_le.2 fun o ho => ?_)
  have h1 : algebraMap (𝓞 F) F ν • o ∈ idealLat J := by
    have : (⟨o, ho⟩ : O) * algebraMap (𝓞 F) O ν ∈ J := J.mul_mem_left _ hνJ
    have e : algebraMap (𝓞 F) F ν • o = (((⟨o, ho⟩ : O) * algebraMap (𝓞 F) O ν : O) : QuatF F a b) := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← Algebra.commutes, Algebra.smul_def (R := F)]; rfl
    rw [mem_idealLat, e]
    exact coe_mem_idealSet.2 this
  have h2 : o = (algebraMap (𝓞 F) F ν)⁻¹ • (algebraMap (𝓞 F) F ν • o) := by
    rw [smul_smul, inv_mul_cancel₀ hνF, one_smul]
  rw [SetLike.mem_coe, h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem finrank_idealLat (hO : IsOrder (𝓞 F) F O) {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0)
    (hν : leftNrdIdeal J = Ideal.span {ν}) : Module.finrank (𝓞 F) (idealLat J) = 4 := by
  have := isLattice_idealLat hO hν0 hν
  have h := Submodule.IsLattice.rank' F (idealLat J)
  rw [QuaternionAlgebra.rank_eq_four] at h
  exact Module.finrank_eq_of_rank_eq h

/-- **A basis of a left ideal**, with its coordinate matrix in a basis $e$ of $\mathcal O$. -/
theorem exists_ideal_basis (hO : IsOrder (𝓞 F) F O) (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O))
    {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0) (hν : leftNrdIdeal J = Ideal.span {ν}) :
    ∃ (f : Fin 4 → QuatF F a b) (B : Matrix (Fin 4) (Fin 4) (𝓞 F)),
      (∀ j, f j ∈ idealSet J) ∧
      (∀ x ∈ idealSet J, ∃ c : Fin 4 → 𝓞 F, x = ∑ j, algebraMap (𝓞 F) F (c j) • f j) ∧
      (∀ c : Fin 4 → 𝓞 F, ∑ j, algebraMap (𝓞 F) F (c j) • f j = 0 → c = 0) ∧
      (∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • (e i : QuatF F a b)) ∧ B.det ≠ 0 ∧
      LinearIndependent F f := by
  classical
  have := isLattice_idealLat hO hν0 hν
  let g := Module.finBasisOfFinrankEq (𝓞 F) (idealLat J) (finrank_idealLat hO hν0 hν)
  set f : Fin 4 → QuatF F a b := fun j => (g j : QuatF F a b)
  have hfJ : ∀ j, f j ∈ idealSet J := fun j => (g j).2
  have hfO : ∀ j, f j ∈ O := fun j => idealSet_subset J (hfJ j)
  set B : Matrix (Fin 4) (Fin 4) (𝓞 F) := Matrix.of fun i j => e.repr ⟨f j, hfO j⟩ i
  have hB : ∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • (e i : QuatF F a b) := fun j => mem_O_eq_sum e (hfO j)
  have hsum : ∀ c : Fin 4 → 𝓞 F, ∑ j, algebraMap (𝓞 F) F (c j) • f j = ((∑ j, c j • g j : idealLat J) :
      QuatF F a b) := by
    intro c
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, algebraMap_smul]
  have hindep : ∀ c : Fin 4 → 𝓞 F, ∑ j, algebraMap (𝓞 F) F (c j) • f j = 0 → c = 0 := by
    intro c hc
    rw [hsum] at hc
    have h0 : (∑ j, c j • g j : idealLat J) = 0 := Subtype.ext hc
    exact funext fun j => (Fintype.linearIndependent_iff.1 g.linearIndependent) c h0 j
  have hli : LinearIndependent F f := by
    have h : ⇑(g.extendOfIsLattice F) = f := funext fun j => Module.Basis.extendOfIsLattice_apply F g j
    rw [← h]; exact (g.extendOfIsLattice F).linearIndependent
  refine ⟨f, B, hfJ, fun x hx => ⟨fun j => g.repr ⟨x, hx⟩ j, ?_⟩, hindep, hB, ?_, hli⟩
  · rw [hsum]
    have := congrArg Subtype.val (g.sum_repr ⟨x, hx⟩)
    exact this.symm
  · intro hdet
    obtain ⟨ξ, hξ0, hξ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hξ0
    apply hindep
    have : ∑ j, algebraMap (𝓞 F) F (ξ j) • f j = ∑ i, algebraMap (𝓞 F) F ((Matrix.mulVec B ξ) i) • (e i : QuatF F a b) := by
      simp only [hB, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    rw [this, hξ]
    simp

end IdealBasis

/-! ### A bound for the reduced norm in coordinates -/

section NrdBound

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

section QSum
variable {K : Type*} [Field K] {c₁ c₃ : K} {ι : Type*} (S : Finset ι) (f : ι → ℍ[K,c₁,c₃])
theorem re_finsetSum : (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := map_sum (QuaternionAlgebra.reₗ c₁ 0 c₃) f S
theorem imI_finsetSum : (∑ i ∈ S, f i).imI = ∑ i ∈ S, (f i).imI := map_sum (QuaternionAlgebra.imIₗ c₁ 0 c₃) f S
theorem imJ_finsetSum : (∑ i ∈ S, f i).imJ = ∑ i ∈ S, (f i).imJ := map_sum (QuaternionAlgebra.imJₗ c₁ 0 c₃) f S
theorem imK_finsetSum : (∑ i ∈ S, f i).imK = ∑ i ∈ S, (f i).imK := map_sum (QuaternionAlgebra.imKₗ c₁ 0 c₃) f S
end QSum

theorem norm_sum_mul_le (φ : F →+* ℂ) (y E : Fin 4 → F) (M : ℝ) (hy : ∀ i, ‖φ (y i)‖ ≤ M) :
    ‖φ (∑ i, y i * E i)‖ ≤ M * ∑ i, ‖φ (E i)‖ := by
  rw [map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hy i) (norm_nonneg _)

/-- **$|N(\operatorname{nrd}(\sum_iy_ie_i))| \le C\,M^{2d}$** if all conjugates of the $y_i$ are bounded by $M$ ($C$ depends only on $e$). -/
theorem exists_abs_norm_nrd_le (e : Fin 4 → QuatF F a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin 4 → F) (M : ℝ), 0 ≤ M → (∀ (φ : F →+* ℂ) i, ‖φ (y i)‖ ≤ M) →
      |(Algebra.norm ℚ (nrd (∑ i, y i • e i)) : ℝ)| ≤ C * M ^ (2 * Module.finrank ℚ F) := by
  classical
  set A := algebraMap (𝓞 F) F a
  set B := algebraMap (𝓞 F) F b
  let K : (F →+* ℂ) → (Fin 4 → F) → ℝ := fun φ E => ∑ i, ‖φ (E i)‖
  let Cφ : (F →+* ℂ) → ℝ := fun φ => K φ (fun i => (e i).re) ^ 2 + ‖φ A‖ * K φ (fun i => (e i).imI) ^ 2 +
    ‖φ B‖ * K φ (fun i => (e i).imJ) ^ 2 + ‖φ A‖ * ‖φ B‖ * K φ (fun i => (e i).imK) ^ 2
  have hCφ0 : ∀ φ, 0 ≤ Cφ φ := fun φ => by positivity
  set C1 : ℝ := 1 + ∑ φ, Cφ φ
  have hC1 : ∀ φ, Cφ φ ≤ C1 := fun φ => by
    have := Finset.single_le_sum (f := Cφ) (fun φ _ => hCφ0 φ) (Finset.mem_univ φ)
    simp only [C1]; linarith
  have hC1' : 0 ≤ C1 := by positivity
  refine ⟨C1 ^ Module.finrank ℚ F, pow_nonneg hC1' _, fun y M hM hy => ?_⟩
  set x := ∑ i, y i • e i
  have hx : nrd x = (∑ i, y i * (e i).re) ^ 2 - A * (∑ i, y i * (e i).imI) ^ 2 -
      B * (∑ i, y i * (e i).imJ) ^ 2 + A * B * (∑ i, y i * (e i).imK) ^ 2 := by
    simp only [nrd, x, re_finsetSum, imI_finsetSum, imJ_finsetSum, imK_finsetSum, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_smul, smul_eq_mul]
    rfl
  have hφ : ∀ φ : F →+* ℂ, ‖φ (nrd x)‖ ≤ C1 * M ^ 2 := by
    intro φ
    have h0 := norm_sum_mul_le φ y (fun i => (e i).re) M (hy φ)
    have h1 := norm_sum_mul_le φ y (fun i => (e i).imI) M (hy φ)
    have h2 := norm_sum_mul_le φ y (fun i => (e i).imJ) M (hy φ)
    have h3 := norm_sum_mul_le φ y (fun i => (e i).imK) M (hy φ)
    rw [hx]
    calc ‖φ ((∑ i, y i * (e i).re) ^ 2 - A * (∑ i, y i * (e i).imI) ^ 2 - B * (∑ i, y i * (e i).imJ) ^ 2 +
          A * B * (∑ i, y i * (e i).imK) ^ 2)‖
        ≤ ‖φ (∑ i, y i * (e i).re)‖ ^ 2 + ‖φ A‖ * ‖φ (∑ i, y i * (e i).imI)‖ ^ 2 +
          ‖φ B‖ * ‖φ (∑ i, y i * (e i).imJ)‖ ^ 2 + ‖φ A‖ * ‖φ B‖ * ‖φ (∑ i, y i * (e i).imK)‖ ^ 2 := by
          simp only [map_add, map_sub, map_mul, map_pow]
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            ((norm_sub_le _ _).trans (add_le_add (le_of_eq (norm_pow _ _)) ?_)) ?_)) ?_)
          · rw [norm_mul, norm_pow]
          · rw [norm_mul, norm_pow]
          · rw [norm_mul, norm_mul, norm_pow]
      _ ≤ (M * K φ (fun i => (e i).re)) ^ 2 + ‖φ A‖ * (M * K φ (fun i => (e i).imI)) ^ 2 +
          ‖φ B‖ * (M * K φ (fun i => (e i).imJ)) ^ 2 + ‖φ A‖ * ‖φ B‖ * (M * K φ (fun i => (e i).imK)) ^ 2 := by
          gcongr
      _ = Cφ φ * M ^ 2 := by simp only [Cφ]; ring
      _ ≤ C1 * M ^ 2 := mul_le_mul_of_nonneg_right (hC1 φ) (sq_nonneg _)
  have hw : ∀ w : InfinitePlace F, w (nrd x) ≤ C1 * M ^ 2 := fun w => by
    rw [← InfinitePlace.norm_embedding_eq]; exact hφ _
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  calc ∏ w : InfinitePlace F, w (nrd x) ^ w.mult ≤ ∏ w : InfinitePlace F, (C1 * M ^ 2) ^ w.mult :=
        Finset.prod_le_prod₀ (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _)
          (fun w _ => pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) (hw w) _)
    _ = (C1 * M ^ 2) ^ Module.finrank ℚ F := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    _ = C1 ^ Module.finrank ℚ F * M ^ (2 * Module.finrank ℚ F) := by rw [mul_pow, ← pow_mul]

end NrdBound

/-! ### Small elements and finiteness of the class set -/

section Finite

open QuadFormsKB.Lattices.ClassFin

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem card_oIdx : Fintype.card (QuadFormsKB.Lattices.OIdx F) = Module.finrank ℚ F := by
  rw [← RingOfIntegers.rank F, Module.finrank_eq_card_chooseBasisIndex]

theorem natAbs_norm_det_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0)
    (hν : leftNrdIdeal J = Ideal.span {ν}) (f : Fin 4 → QuatF F a b)
    (hspan : ∀ x ∈ idealSet J, ∃ c : Fin 4 → 𝓞 F, x = ∑ j, algebraMap (𝓞 F) F (c j) • f j)
    (hfJ : ∀ j, f j ∈ idealSet J)
    (B : Matrix (Fin 4) (Fin 4) (𝓞 F)) (hB : ∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • (e i : QuatF F a b))
    (hdet : B.det ≠ 0) :
    (Algebra.norm ℤ B.det).natAbs = (Algebra.norm ℤ ν).natAbs ^ 2 := by
  have hJ : leftNrdIdeal J ≠ ⊥ := by rw [hν, Ne, Ideal.span_singleton_eq_bot]; exact hν0
  have h := span_det_eq_sq ha hb hO e hJ f hspan hfJ B hB hdet
  rw [hν, Ideal.span_singleton_pow] at h
  have := congrArg Ideal.absNorm h
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, map_pow, Int.natAbs_pow] at this
  exact this

/-- **Small elements** (Minkowski-type bound): there is $C$ (depending on $\mathcal O$, $e$) such that every left ideal with
$\operatorname{nrd}(J) = (\nu) \ne 0$ contains $x \ne 0$ with $|N(\operatorname{nrd}x)| \le C\,|N(\nu)|$. -/
theorem exists_small_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : Ideal O} {ν : 𝓞 F}, ν ≠ 0 → leftNrdIdeal J = Ideal.span {ν} →
      ∃ x ∈ idealSet J, x ≠ 0 ∧
        |(Algebra.norm ℚ (nrd x) : ℝ)| ≤ C * ((Algebra.norm ℤ ν).natAbs : ℝ) := by
  classical
  obtain ⟨C0, hC0, hbound⟩ := exists_abs_norm_nrd_le (a := a) (b := b) (fun i => (e i : QuatF F a b))
  set d := Module.finrank ℚ F
  have hd : 0 < d := Module.finrank_pos
  set W := embW F
  have hW : 0 ≤ W := embW_nonneg
  refine ⟨C0 * W ^ (2 * d) * 4 ^ d, by positivity, fun {J ν} hν0 hν => ?_⟩
  obtain ⟨f, B, hfJ, hspan, hindep, hB, hdet, -⟩ := exists_ideal_basis hO.1 e hν0 hν
  set N := (Algebra.norm ℤ ν).natAbs
  have hN : N ≠ 0 := by
    simp only [N, Int.natAbs_ne_zero, ne_eq, Algebra.norm_eq_zero_iff]; exact hν0
  have hdetN := natAbs_norm_det_eq ha hb hO e hν0 hν f hspan hfJ B hB hdet
  have hex : ∃ T : ℕ, N < T ^ (2 * d) := ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N)
    (Nat.le_self_pow (by omega) _)⟩
  set T := Nat.find hex
  have hT : N < T ^ (2 * d) := Nat.find_spec hex
  have hT' : (Algebra.norm ℤ B.det).natAbs < T ^ (4 * Fintype.card (QuadFormsKB.Lattices.OIdx F)) := by
    rw [hdetN, card_oIdx, show 4 * d = 2 * (2 * d) by ring, pow_mul', ]
    exact Nat.pow_lt_pow_left hT two_ne_zero
  obtain ⟨ξ, hξ0, hξ⟩ := exists_pigeon B hdet T hT'
  set y : Fin 4 → F := fun i => algebraMap (𝓞 F) F ((Matrix.mulVec B ξ) i)
  set x := ∑ j, algebraMap (𝓞 F) F (ξ j) • f j
  have hxy : x = ∑ i, y i • (e i : QuatF F a b) := by
    simp only [x, y, hB, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have hxJ : x ∈ idealSet J := by
    have : x ∈ idealLat J := Submodule.sum_mem _ fun j _ => by
      rw [← algebraMap_smul (A := F)]
      exact Submodule.smul_mem _ _ (hfJ j)
    exact this
  refine ⟨x, hxJ, fun h0 => hξ0 (hindep ξ h0), ?_⟩
  have hy : ∀ (φ : F →+* ℂ) i, ‖φ (y i)‖ ≤ T * W := by
    intro φ i
    obtain ⟨q, hq, hqe⟩ := hξ i
    simp only [y]
    rw [hqe]
    exact norm_sum_omega_le φ q T fun k => by
      have := hq k
      exact_mod_cast this.le
  have h1 := hbound y (T * W) (by positivity) hy
  rw [← hxy] at h1
  refine h1.trans ?_
  -- T^(2d) ≤ 4^d N
  have hT4 : (T : ℝ) ^ (2 * d) ≤ 4 ^ d * N := by
    have hT0 : 1 ≤ T := by
      by_contra h
      rw [not_le] at h
      interval_cases T
      rw [zero_pow (by omega)] at hT; omega
    rcases Nat.eq_or_lt_of_le hT0 with h | h
    · rw [← h]; simp only [Nat.cast_one, one_pow]
      have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
      nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := d)]
    · have hmin : (T - 1) ^ (2 * d) ≤ N := by
        have := Nat.find_min hex (show T - 1 < T by omega)
        omega
      have h2 : T ≤ 2 * (T - 1) := by omega
      have h3 : T ^ (2 * d) ≤ 4 ^ d * N := by
        calc T ^ (2 * d) ≤ (2 * (T - 1)) ^ (2 * d) := Nat.pow_le_pow_left h2 _
          _ = 4 ^ d * (T - 1) ^ (2 * d) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ d * N := Nat.mul_le_mul_left _ hmin
      exact_mod_cast h3
  calc C0 * ((T : ℝ) * W) ^ (2 * d) = C0 * W ^ (2 * d) * (T : ℝ) ^ (2 * d) := by ring
    _ ≤ C0 * W ^ (2 * d) * (4 ^ d * N) := by gcongr
    _ = C0 * W ^ (2 * d) * 4 ^ d * N := by ring

theorem leftNrdIdeal_ne_bot (hO : IsOrder (𝓞 F) F O) (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) {J : Ideal O}
    (hJ : J ≠ ⊥) : leftNrdIdeal J ≠ ⊥ := by
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨n₀, hn₀⟩ := (isInteger_trd_nrd hO x₀.2).2
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn₀
    exact hx₀0 (Subtype.ext (hdiv _ hn₀.symm))
  intro h
  have hmem : n₀ ∈ leftNrdIdeal J := Ideal.subset_span ⟨x₀, hx₀, hn₀⟩
  rw [h] at hmem
  exact hn₀0 ((Submodule.mem_bot _).1 hmem)

theorem finite_setOf_leftNrdIdeal_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : 𝔫 ≠ ⊥) : {J : Ideal O | leftNrdIdeal J = 𝔫}.Finite := by
  obtain ⟨n, rfl⟩ := (IsPrincipalIdealRing.principal 𝔫).principal
  have hn : n ≠ 0 := by rintro rfl; exact h𝔫 (by simp)
  have hcard : Nat.card {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} = _ := card_ideal_nrd_eq ha hb hO hn
  have hpos : Nat.card {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} ≠ 0 := by
    rw [hcard, Finset.prod_ne_zero_iff]
    intro v _
    split_ifs
    · exact one_ne_zero
    · exact (Finset.sum_pos (fun i _ => pow_pos (Nat.pos_of_ne_zero (by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)) i) ⟨0, by simp⟩).ne'
  have : Finite {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} := Nat.finite_of_card_ne_zero hpos
  exact Set.finite_coe_iff.mp this

/-- **The left ideal class set of a maximal order of a division quaternion algebra is finite** ($\mathcal O_F$ a PID).

Source: Voight 2021, Thm. 17.7.? (finiteness of the class set; there via a Minkowski bound); here via O'Meara's pigeonhole
(`exists_small_mem`) and the inverse ideal $\nu^{-1}\bar J$ (`mem_colon_iff`). -/
@[kb "voight2021" "Thm. 17.8.3"]
theorem finite_classes (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) : Finite (Quotient (idealSetoid O)) := by
  classical
  obtain ⟨e⟩ := exists_basis_order hO.1
  obtain ⟨C, hC0, hsmall⟩ := exists_small_mem ha hb hO e
  set M0 := ⌊C⌋₊
  have hfinN : {𝔫 : Ideal (𝓞 F) | Ideal.absNorm 𝔫 ≤ M0}.Finite := Ideal.finite_setOfPred_absNorm_le M0
  set S : Set (Ideal O) := {J | J = ⊥ ∨ (Ideal.absNorm (leftNrdIdeal J) ≤ M0 ∧ leftNrdIdeal J ≠ ⊥)}
  have hS : S.Finite := by
    refine ((Set.finite_singleton ⊥).union (Set.Finite.biUnion (hfinN.subset (Set.inter_subset_left
      (t := {𝔫 : Ideal (𝓞 F) | 𝔫 ≠ ⊥}))) fun 𝔫 h𝔫 => finite_setOf_leftNrdIdeal_eq ha hb hO h𝔫.2)).subset ?_
    rintro J (rfl | ⟨h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Set.mem_biUnion (x := leftNrdIdeal J) ⟨h1, h2⟩ rfl)
  have hsurj : ∀ c : Quotient (idealSetoid O), ∃ J ∈ S, Quotient.mk _ J = c := by
    intro c
    set J := c.out
    by_cases hJ : J = ⊥
    · exact ⟨⊥, Or.inl rfl, by rw [← hJ, Quotient.out_eq]⟩
    have hJn := leftNrdIdeal_ne_bot hO.1 hdiv hJ
    obtain ⟨ν, hν⟩ := (IsPrincipalIdealRing.principal (leftNrdIdeal J)).principal
    have hν' : leftNrdIdeal J = Ideal.span {ν} := hν
    have hν0 : ν ≠ 0 := by rintro rfl; exact hJn (by rw [hν', Ideal.span_singleton_eq_bot.2 rfl])
    have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
    obtain ⟨x, hx, hx0, hxC⟩ := hsmall hν0 hν'
    set β : QuatF F a b := (algebraMap (𝓞 F) F ν)⁻¹ • star x
    have hβ : β ∈ colon J := (mem_colon_iff ha hb hO hν0 hν').2 ⟨x, hx, rfl⟩
    have hnrdx : nrd x ≠ 0 := fun h => hx0 (hdiv x h)
    have hnrdβ : nrd β = ((algebraMap (𝓞 F) F ν)⁻¹) ^ 2 * nrd x := by rw [nrd_smul, nrd_star]
    have hβu : IsUnit β := by
      rw [isUnit_iff_nrd_ne_zero, hnrdβ]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hνF)) hnrdx
    set J' := rmulIdeal J β
    have hrel : IdealRel J J' := ⟨hβu.unit, by rw [IsUnit.unit_spec]; exact idealSet_rmulIdeal hβ⟩
    have hnorm : (Ideal.absNorm (leftNrdIdeal J') : ℝ) =
        (Ideal.absNorm (leftNrdIdeal J) : ℝ) * |(Algebra.norm ℚ (nrd β) : ℝ)| :=
      absNorm_leftNrdIdeal_rmulIdeal hO.1 hβ
    set N := (Algebra.norm ℤ ν).natAbs
    have hNJ : Ideal.absNorm (leftNrdIdeal J) = N := by rw [hν', Ideal.absNorm_span_singleton]
    have hNν : |(Algebra.norm ℚ (algebraMap (𝓞 F) F ν) : ℝ)| = N := by
      rw [show (Algebra.norm ℚ (algebraMap (𝓞 F) F ν) : ℝ) = ((Algebra.norm ℤ ν : ℤ) : ℝ) by
        rw [← Algebra.coe_norm_int]; rfl]
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hN0 : (0 : ℝ) < N := by
      rw [← hNν]; exact abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hνF)
    have hxβ : nrd x = (algebraMap (𝓞 F) F ν) ^ 2 * nrd β := by
      rw [hnrdβ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hνF, one_pow, one_mul]
    have hβnorm : |(Algebra.norm ℚ (nrd β) : ℝ)| = |(Algebra.norm ℚ (nrd x) : ℝ)| / (N : ℝ) ^ 2 := by
      rw [hxβ, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, hNν]
      field_simp
    have hJ'N : (Ideal.absNorm (leftNrdIdeal J') : ℝ) = |(Algebra.norm ℚ (nrd x) : ℝ)| / N := by
      rw [hnorm, hNJ, hβnorm]; field_simp
    refine ⟨J', Or.inr ⟨?_, ?_⟩, ?_⟩
    · refine Nat.le_floor ?_
      rw [hJ'N, div_le_iff₀ hN0]; exact hxC
    · intro h
      have h0 : (Ideal.absNorm (leftNrdIdeal J') : ℝ) = 0 := by rw [h]; simp
      rw [hJ'N] at h0
      have : |(Algebra.norm ℚ (nrd x) : ℝ)| ≠ 0 :=
        abs_ne_zero.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hnrdx)
      exact this (by simpa [hN0.ne'] using h0)
    · rw [← Quotient.out_eq c]
      exact Quotient.sound (IdealRel.symm hrel)
  have : Finite S := hS.to_subtype
  exact Finite.of_surjective (fun J : S => (Quotient.mk _ J.1 : Quotient (idealSetoid O))) fun c => by
    obtain ⟨J, hJS, hJc⟩ := hsurj c
    exact ⟨⟨J, hJS⟩, hJc⟩

end Finite

end QuadFormsKB.QuatOrder
