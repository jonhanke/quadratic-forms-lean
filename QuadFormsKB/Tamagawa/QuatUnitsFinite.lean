/-
# Unit groups of left ideals of a totally definite order are finite modulo $\mathcal O_F^\times$

**Layer:** $F$ a totally real number field, $D = (a,b)_F$ totally definite ($\sigma(a), \sigma(b) < 0$ at every real embedding,
`IsTotDefinite`), $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ an order.

For a nonzero left ideal $J$ the group $\Gamma_J = \{\gamma \in D^\times : J\gamma = J\}$ contains $\mathcal O_F^\times$ with finite index
(`finiteIndex_centralUnitsIn`). *Proof.* (1) $\operatorname{nrd}\gamma \in \mathcal O_F^\times$ for $\gamma \in \Gamma_J$
(`exists_unit_nrd_eq`: $\operatorname{nrd}(J) = \operatorname{nrd}(J\gamma) = \operatorname{nrd}(J)(\operatorname{nrd}\gamma)$ as fractional ideals);
(2) every unit is $e w^2$ with $e$ in a finite set $E$ (`exists_finset_units_sq`, Dirichlet's unit theorem); replacing $\gamma$ by
$w^{-1}\gamma$ in the same coset gives $\operatorname{nrd}\gamma \in E$; (3) $(\mathcal O : J) \subseteq N^{-1}\mathcal O_F\langle1,i,j,k\rangle$ for some
$N \ne 0$ (`exists_smul_mem_stdOrder_of_colon`), and the quaternions with coordinates in $N^{-1}\mathcal O_F$ and
$\sigma(\operatorname{nrd}x) \le C$ at every real $\sigma$ are finitely many (`finite_bounded`: $\operatorname{nrd}$ is positive definite at every
real place, so the coordinates have bounded conjugates, `NumberField.Embeddings.finite_of_norm_le`).

Source: Voight, *Quaternion Algebras* (2021), Lemma 26.5.1 / Prop. 32.3.7 (finiteness of $\mathcal O^\times/R^\times$ for definite orders,
there via discreteness of $\mathcal O^1$ in the compact group $\mathbb H^1$); the argument here is the elementary bounded-coordinates version.
Locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatClassSum

open NumberField Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

/-! ### Units modulo squares -/

section UnitsSq

variable {F : Type} [Field F] [NumberField F]

/-- **$\mathcal O_F^\times/\mathcal O_F^{\times2}$ is finite**: there is a finite set $E$ of units with every unit of the form $ew^2$, $e \in E$
(from Dirichlet's unit theorem $u = \zeta\prod_i\varepsilon_i^{n_i}$, `NumberField.Units.exist_unique_eq_mul_prod`). -/
theorem exists_finset_units_sq : ∃ E : Finset (𝓞 F)ˣ, ∀ u : (𝓞 F)ˣ, ∃ e ∈ E, ∃ w : (𝓞 F)ˣ, u = e * w ^ 2 := by
  classical
  let g : (Units.torsion F) × (Fin (Units.rank F) → Fin 2) → (𝓞 F)ˣ := fun p =>
    (p.1 : (𝓞 F)ˣ) * ∏ i, Units.fundSystem F i ^ ((p.2 i : ℕ))
  refine ⟨(Set.finite_range g).toFinset, fun u => ?_⟩
  obtain ⟨⟨ζ, n⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod F u
  have h2 : ∀ i, (n i % 2).toNat < 2 := fun i => by omega
  refine ⟨g (ζ, fun i => ⟨(n i % 2).toNat, h2 i⟩), by simp, ∏ i, Units.fundSystem F i ^ (n i / 2), ?_⟩
  rw [hu]
  simp only [g, mul_assoc]
  congr 1
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hn : n i = ((n i % 2).toNat : ℤ) + 2 * (n i / 2) := by omega
  conv_lhs => rw [hn]
  rw [zpow_add, zpow_natCast, zpow_mul, ← zpow_natCast _ 2]
  congr 1
  rw [← zpow_mul, ← zpow_mul, mul_comm]
  norm_cast

end UnitsSq

/-! ### Total definiteness and bounded quaternions -/

section Definite

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- **$D = (a,b)_F$ is totally definite**: $\sigma(a) < 0$ and $\sigma(b) < 0$ for every real embedding $\sigma$ (equivalently, the norm form
$\langle 1,-a,-b,ab\rangle$ is positive definite at every real place). -/
def IsTotDefinite (a b : 𝓞 F) : Prop :=
  ∀ σ : F →+* ℝ, σ (algebraMap (𝓞 F) F a) < 0 ∧ σ (algebraMap (𝓞 F) F b) < 0

theorem sigma_nrd (σ : F →+* ℝ) (x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) :
    σ (nrd x) = σ x.re ^ 2 + (-σ (algebraMap (𝓞 F) F a)) * σ x.imI ^ 2 + (-σ (algebraMap (𝓞 F) F b)) * σ x.imJ ^ 2 +
      (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b)) * σ x.imK ^ 2 := by
  simp only [nrd, map_add, map_sub, map_mul, map_pow]; ring

/-- At a real place each of the four terms of $\sigma(\operatorname{nrd}x)$ is $\ge 0$. -/
theorem coord_sq_le (hdef : IsTotDefinite a b) (σ : F →+* ℝ) (x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) :
    σ x.re ^ 2 ≤ σ (nrd x) ∧ (-σ (algebraMap (𝓞 F) F a)) * σ x.imI ^ 2 ≤ σ (nrd x) ∧
      (-σ (algebraMap (𝓞 F) F b)) * σ x.imJ ^ 2 ≤ σ (nrd x) ∧
      (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b)) * σ x.imK ^ 2 ≤ σ (nrd x) := by
  obtain ⟨ha, hb⟩ := hdef σ
  have t0 := sq_nonneg (σ x.re)
  have t1 : 0 ≤ (-σ (algebraMap (𝓞 F) F a)) * σ x.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t2 : 0 ≤ (-σ (algebraMap (𝓞 F) F b)) * σ x.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t3 : 0 ≤ (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b)) * σ x.imK ^ 2 :=
    mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  rw [sigma_nrd]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A real embedding of $F$ (it exists for every number field with a real place; for $F$ totally real, any place). -/
def someRealEmb [IsTotallyReal F] : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (Classical.arbitrary (InfinitePlace F)))

/-- **The reduced norm is anisotropic** on a totally definite algebra. -/
theorem eq_zero_of_nrd_eq_zero [IsTotallyReal F] (hdef : IsTotDefinite a b)
    {x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]} (hx : nrd x = 0) : x = 0 := by
  set σ := someRealEmb (F := F)
  obtain ⟨ha, hb⟩ := hdef σ
  obtain ⟨h0, h1, h2, h3⟩ := coord_sq_le hdef σ x
  rw [hx, map_zero] at h0 h1 h2 h3
  have key : ∀ (A t : ℝ), 0 < A → A * t ^ 2 ≤ 0 → t = 0 := fun A t hA h =>
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (le_of_mul_le_mul_left (by rwa [mul_zero]) hA) (sq_nonneg _))
  have e0 : σ x.re = 0 := key 1 _ one_pos (by rwa [one_mul])
  have e1 : σ x.imI = 0 := key _ _ (by linarith) h1
  have e2 : σ x.imJ = 0 := key _ _ (by linarith) h2
  have e3 : σ x.imK = 0 := key _ _ (mul_pos_of_neg_of_neg ha hb) h3
  ext
  · exact (map_eq_zero_iff σ σ.injective).1 e0
  · exact (map_eq_zero_iff σ σ.injective).1 e1
  · exact (map_eq_zero_iff σ σ.injective).1 e2
  · exact (map_eq_zero_iff σ σ.injective).1 e3

/-- $|t| \le 1 + t^2$. -/
theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  rcases le_or_gt |t| 1 with h | h
  · nlinarith [sq_nonneg t]
  · have : |t| ≤ |t| ^ 2 := by nlinarith
    rw [sq_abs] at this; linarith

/-- If $\sigma(\operatorname{nrd}x) \le C$ then every coordinate $c$ of $x$ satisfies $|\sigma(Nc)| \le 1 + \sigma(N)^2\,C^+\,s_\sigma$,
$s_\sigma = 1 + (-\sigma a)^{-1} + (-\sigma b)^{-1} + (\sigma a\,\sigma b)^{-1}$. -/
theorem abs_sigma_coord_le (hdef : IsTotDefinite a b) (σ : F →+* ℝ) (N : F) (C : ℝ)
    (x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) (hx : σ (nrd x) ≤ C) (c : F)
    (hc : c = x.re ∨ c = x.imI ∨ c = x.imJ ∨ c = x.imK) :
    |σ (N * c)| ≤ 1 + σ N ^ 2 * max C 0 * (1 + (-σ (algebraMap (𝓞 F) F a))⁻¹ + (-σ (algebraMap (𝓞 F) F b))⁻¹ +
      (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b))⁻¹) := by
  obtain ⟨ha, hb⟩ := hdef σ
  set A := -σ (algebraMap (𝓞 F) F a) with hA
  set B := -σ (algebraMap (𝓞 F) F b) with hB
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hAB : σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b) = A * B := by rw [hA, hB]; ring
  rw [hAB]
  have hAB0 : 0 < A * B := mul_pos hA0 hB0
  obtain ⟨h0, h1, h2, h3⟩ := coord_sq_le hdef σ x
  rw [hAB] at h3
  set M := max C 0
  have hM : σ (nrd x) ≤ M := hx.trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  -- σ(c)² ≤ M · s
  have hs : σ c ^ 2 ≤ M * (1 + A⁻¹ + B⁻¹ + (A * B)⁻¹) := by
    have hpos : 0 ≤ M * A⁻¹ := mul_nonneg hM0 (inv_nonneg.2 hA0.le)
    have hpos' : 0 ≤ M * B⁻¹ := mul_nonneg hM0 (inv_nonneg.2 hB0.le)
    have hpos'' : 0 ≤ M * (A * B)⁻¹ := mul_nonneg hM0 (inv_nonneg.2 hAB0.le)
    have e : M * (1 + A⁻¹ + B⁻¹ + (A * B)⁻¹) = M + M * A⁻¹ + M * B⁻¹ + M * (A * B)⁻¹ := by ring
    rw [e]
    rcases hc with rfl | rfl | rfl | rfl
    · linarith
    · have : σ x.imI ^ 2 ≤ M * A⁻¹ := by
        rw [le_mul_inv_iff₀ hA0]; linarith
      linarith
    · have : σ x.imJ ^ 2 ≤ M * B⁻¹ := by
        rw [le_mul_inv_iff₀ hB0]; linarith
      linarith
    · have : σ x.imK ^ 2 ≤ M * (A * B)⁻¹ := by
        rw [le_mul_inv_iff₀ hAB0]; linarith
      linarith
  calc |σ (N * c)| ≤ 1 + σ (N * c) ^ 2 := abs_le_one_add_sq _
    _ = 1 + σ N ^ 2 * σ c ^ 2 := by rw [map_mul, mul_pow]
    _ ≤ 1 + σ N ^ 2 * (M * (1 + A⁻¹ + B⁻¹ + (A * B)⁻¹)) := by gcongr
    _ = _ := by ring

/-- **Bounded quaternions are finitely many**: for $N \ne 0$ and $C \in \mathbb R$, the quaternions $x$ with $Nx \in \mathcal O_F\langle1,i,j,k\rangle$
and $\sigma(\operatorname{nrd}x) \le C$ at every real embedding form a finite set ($F$ totally real, $D$ totally definite). -/
theorem finite_bounded [IsTotallyReal F] (hdef : IsTotDefinite a b) {N : 𝓞 F} (hN : N ≠ 0) (C : ℝ) :
    {x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] |
      (algebraMap (𝓞 F) F N) • x ∈ stdOrder F a b ∧ ∀ σ : F →+* ℝ, σ (nrd x) ≤ C}.Finite := by
  classical
  set N' := algebraMap (𝓞 F) F N with hN'def
  have hN' : N' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hN
  let bd : (F →+* ℝ) → ℝ := fun σ => 1 + σ N' ^ 2 * max C 0 * (1 + (-σ (algebraMap (𝓞 F) F a))⁻¹ +
    (-σ (algebraMap (𝓞 F) F b))⁻¹ + (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b))⁻¹)
  have hbd : ∀ σ, 0 ≤ bd σ := fun σ => by
    obtain ⟨ha, hb⟩ := hdef σ
    have h1 : 0 < (-σ (algebraMap (𝓞 F) F a))⁻¹ := inv_pos.2 (by linarith)
    have h2 : 0 < (-σ (algebraMap (𝓞 F) F b))⁻¹ := inv_pos.2 (by linarith)
    have h3 : 0 < (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b))⁻¹ := inv_pos.2 (mul_pos_of_neg_of_neg ha hb)
    have : 0 ≤ σ N' ^ 2 * max C 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
    have : 0 ≤ σ N' ^ 2 * max C 0 * (1 + (-σ (algebraMap (𝓞 F) F a))⁻¹ +
      (-σ (algebraMap (𝓞 F) F b))⁻¹ + (σ (algebraMap (𝓞 F) F a) * σ (algebraMap (𝓞 F) F b))⁻¹) :=
      mul_nonneg this (by linarith)
    simp only [bd]; linarith
  have hreal : ∀ φ : F →+* ℂ, ComplexEmbedding.IsReal φ := fun φ =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  let B : ℝ := ∑ φ : F →+* ℂ, bd (hreal φ).embedding
  set T := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B}
  have hT : T.Finite := Embeddings.finite_of_norm_le F ℂ B
  let c : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] → Fin 4 → F :=
    fun x => ![N' * x.re, N' * x.imI, N' * x.imJ, N' * x.imK]
  have hinj : Function.Injective c := by
    intro x y h
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2; have h3 := congrFun h 3
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_right_inj' hN'] at h0 h1 h2 h3
    ext <;> assumption
  refine ((Set.Finite.pi' (t := fun _ : Fin 4 => T) (fun _ => hT)).preimage hinj.injOn).subset ?_
  rintro x ⟨hstd, hC⟩
  rw [mem_stdOrder] at hstd
  obtain ⟨h0, h1, h2, h3⟩ := hstd
  simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul] at h0 h1 h2 h3
  have key : ∀ y : F, IsLocalization.IsInteger (𝓞 F) y → (y = N' * x.re ∨ y = N' * x.imI ∨ y = N' * x.imJ ∨ y = N' * x.imK) →
      y ∈ T := by
    intro y ⟨r, hr⟩ hy
    refine ⟨hr ▸ RingOfIntegers.isIntegral_coe r, fun φ => ?_⟩
    set σ := (hreal φ).embedding
    have hφ : ‖φ y‖ = |σ y| := by
      rw [← (hreal φ).coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [hφ]
    have hb : |σ y| ≤ bd σ := by
      obtain ⟨c', hc', rfl⟩ : ∃ c' : F, (c' = x.re ∨ c' = x.imI ∨ c' = x.imJ ∨ c' = x.imK) ∧ y = N' * c' := by
        rcases hy with h | h | h | h
        exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr (Or.inl rfl), h⟩, ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩,
          ⟨_, Or.inr (Or.inr (Or.inr rfl)), h⟩]
      exact abs_sigma_coord_le hdef σ N' C x (hC σ) c' hc'
    exact hb.trans (Finset.single_le_sum (f := fun φ => bd (hreal φ).embedding) (fun φ _ => hbd _)
      (Finset.mem_univ φ))
  intro i
  fin_cases i
  · exact key _ h0 (Or.inl rfl)
  · exact key _ h1 (Or.inr (Or.inl rfl))
  · exact key _ h2 (Or.inr (Or.inr (Or.inl rfl)))
  · exact key _ h3 (Or.inr (Or.inr (Or.inr rfl)))

end Definite

/-! ### $[\Gamma_J : \mathcal O_F^\times] < \infty$ -/

section UnitIndex

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

theorem algebraMap_int_quat (r : 𝓞 F) :
    algebraMap (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] r =
      ((algebraMap (𝓞 F) F r : F) : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) := rfl

/-- A nonzero left ideal of a totally definite order has nonzero reduced norm, and $(\mathcal O : J) \subseteq
N^{-1}\mathcal O_F\langle1,i,j,k\rangle$ for some $N \ne 0$ (if $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$). -/
theorem exists_smul_mem_stdOrder_of_colon [IsTotallyReal F] (hdef : IsTotDefinite a b) (hO : IsOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) {J : Ideal O} (hJ : J ≠ ⊥) :
    leftNrdIdeal J ≠ ⊥ ∧ ∃ N : 𝓞 F, N ≠ 0 ∧ ∀ α ∈ colon J, (algebraMap (𝓞 F) F N) • α ∈ stdOrder F a b := by
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hx₀' : (x₀ : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) ≠ 0 := fun h => hx₀0 (Subtype.ext h)
  obtain ⟨n₀, hn₀⟩ := (isInteger_trd_nrd hO x₀.2).2
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn₀
    exact hx₀' (eq_zero_of_nrd_eq_zero hdef hn₀.symm)
  have hmem : n₀ ∈ leftNrdIdeal J := Ideal.subset_span ⟨x₀, hx₀, hn₀⟩
  refine ⟨fun h => hn₀0 (by rw [h] at hmem; exact (Submodule.mem_bot _).1 hmem), 2 * a * b * n₀, ?_, ?_⟩
  · have h2 : (2 : 𝓞 F) ≠ 0 := by
      intro h; have := congrArg (algebraMap (𝓞 F) F) h; simp at this
    have ha : a ≠ 0 := by
      rintro rfl
      have := (hdef (someRealEmb (F := F))).1
      rw [map_zero, map_zero] at this; exact lt_irrefl 0 this
    have hb : b ≠ 0 := by
      rintro rfl
      have := (hdef (someRealEmb (F := F))).2
      rw [map_zero, map_zero] at this; exact lt_irrefl 0 this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) hb) hn₀0
  · intro α hα
    have halg : algebraMap (𝓞 F) O n₀ ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO J hmem
    have h1 := hα _ (coe_mem_idealSet.2 halg)
    have e : ((algebraMap (𝓞 F) O n₀ : O) : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) * α =
        (algebraMap (𝓞 F) F n₀) • α := by
      rw [Subalgebra.coe_algebraMap, algebraMap_int_quat]
      ext <;> simp [Algebra.smul_def]
    rw [e] at h1
    have h2 := smul_mem_stdOrder hO hstd h1
    rwa [smul_smul, ← map_mul] at h2

/-- **$\operatorname{nrd}\gamma$ is a unit for $\gamma \in \Gamma_J$** ($\operatorname{nrd}(J) \ne 0$): from
$\operatorname{nrd}(J) = \operatorname{nrd}(J\gamma) = \operatorname{nrd}(J)\cdot(\operatorname{nrd}\gamma)$. -/
theorem exists_unit_nrd_eq (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {γ : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ} (hγ : γ ∈ rStab J) :
    ∃ u : (𝓞 F)ˣ, algebraMap (𝓞 F) F u = nrd (γ : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) := by
  have hc : (γ : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) ∈ colon J := fun x hx =>
    idealSet_subset J (by rw [← mem_rStab.1 hγ]; exact ⟨x, hx, rfl⟩)
  have heq : rmulIdeal J γ = J := idealSet_injective (by rw [idealSet_rmulIdeal hc, mem_rStab.1 hγ])
  have h := coeIdeal_leftNrdIdeal_rmulIdeal hO hc
  rw [heq] at h
  have hne : ((leftNrdIdeal J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (nrd (γ : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) 1 := by
    rw [map_one]
    refine mul_left_cancel₀ hne ?_
    rw [mul_one]; exact h.symm
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h1
  refine ⟨z⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def] at hz
  have hz0 : algebraMap (𝓞 F) F (z : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 z.ne_zero
  have : algebraMap (𝓞 F) F ((z⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * algebraMap (𝓞 F) F (z : 𝓞 F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc algebraMap (𝓞 F) F ((z⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
      = algebraMap (𝓞 F) F ((z⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (algebraMap (𝓞 F) F (z : 𝓞 F) *
          nrd (γ : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])) := by rw [hz, mul_one]
    _ = _ := by rw [← mul_assoc, this, one_mul]

theorem nrd_algebraMap_int (r : 𝓞 F) :
    nrd (algebraMap (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] r) = (algebraMap (𝓞 F) F r) ^ 2 := by
  rw [algebraMap_int_quat]
  simp [nrd]

/-- **$[\Gamma_J : \mathcal O_F^\times] < \infty$** for every nonzero left ideal $J$ of an order $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ of a
totally definite quaternion algebra over a totally real field.

Source: Voight 2021, Lemma 26.5.1 (and Prop. 32.3.7); here by bounded coordinates (see the file header). -/
@[kb "voight2021" "Lemma 26.5.1"]
theorem finiteIndex_centralUnitsIn [IsTotallyReal F] (hdef : IsTotDefinite a b) (hO : IsOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) {J : Ideal O} (hJ : J ≠ ⊥) :
    (centralUnitsIn (R := 𝓞 F) J).FiniteIndex := by
  classical
  obtain ⟨hnJ, N, hN, hcol⟩ := exists_smul_mem_stdOrder_of_colon hdef hO hstd hJ
  obtain ⟨E, hE⟩ := exists_finset_units_sq (F := F)
  set C : ℝ := ∑ e ∈ E, ∑ φ : F →+* ℂ, ‖φ (algebraMap (𝓞 F) F (e : 𝓞 F))‖
  have hC : ∀ e ∈ E, ∀ σ : F →+* ℝ, σ (algebraMap (𝓞 F) F (e : 𝓞 F)) ≤ C := by
    intro e he σ
    set y := algebraMap (𝓞 F) F (e : 𝓞 F)
    have h1 : σ y ≤ ‖(Complex.ofRealHom.comp σ) y‖ := by
      rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    refine h1.trans ((Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)).trans ?_)
    exact Finset.single_le_sum (f := fun e : (𝓞 F)ˣ => ∑ φ : F →+* ℂ, ‖φ (algebraMap (𝓞 F) F (e : 𝓞 F))‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) he
  set S := {x : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] |
      (algebraMap (𝓞 F) F N) • x ∈ stdOrder F a b ∧ ∀ σ : F →+* ℝ, σ (nrd x) ≤ C}
  have hS : S.Finite := finite_bounded hdef hN C
  have : Finite S := hS.to_subtype
  set P : rStab J → Prop := fun γ => (((γ : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ) :
      ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) ∈ S) with hP
  have hfinT : Finite {γ : rStab J // P γ} := by
    refine Finite.of_injective (fun γ => (⟨_, γ.2⟩ : S)) fun γ δ h => ?_
    have : (((γ.1 : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ)) :
        ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) = ((δ.1 : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Units.ext this))
  have hfinQ : Finite (rStab J ⧸ centralUnitsIn (R := 𝓞 F) J) := by
    refine Finite.of_surjective (fun γ : {γ : rStab J // P γ} => (γ.1 : rStab J ⧸ centralUnitsIn (R := 𝓞 F) J)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ =>
      obtain ⟨u, hu⟩ := exists_unit_nrd_eq hO hnJ γ.2
      obtain ⟨e, he, w, huw⟩ := hE u
      set W : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ :=
        Units.map (algebraMap (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]).toMonoidHom w with hWdef
      have hWc : W ∈ centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) := ⟨w, rfl⟩
      have hWs : W ∈ rStab J := centralUnits_le_rStab J hWc
      set γ' : rStab J := γ * ⟨W, hWs⟩⁻¹
      have hγ'c : (((γ' : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ)) :
          ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) ∈ colon J := fun x hx =>
        idealSet_subset J (by rw [← mem_rStab.1 γ'.2]; exact ⟨x, hx, rfl⟩)
      have hnrd : nrd (((γ' : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ)) :
          ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) = algebraMap (𝓞 F) F (e : 𝓞 F) := by
        have hW1 : ((W⁻¹ : (ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b])ˣ) :
            ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]) =
            algebraMap (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b] ((w⁻¹ : (𝓞 F)ˣ) : 𝓞 F) := by
          rw [hWdef, ← map_inv]; rfl
        simp only [γ', Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
        rw [nrd_mul, hW1, nrd_algebraMap_int, ← hu, huw]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
        have : algebraMap (𝓞 F) F ((w⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * algebraMap (𝓞 F) F (w : 𝓞 F) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        linear_combination (algebraMap (𝓞 F) F (e : 𝓞 F)) *
          (algebraMap (𝓞 F) F ((w⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * algebraMap (𝓞 F) F (w : 𝓞 F) + 1) * this
      refine ⟨⟨γ', hcol _ hγ'c, fun σ => by rw [hnrd]; exact hC e he σ⟩, ?_⟩
      show ((γ * ⟨W, hWs⟩⁻¹ : rStab J) : rStab J ⧸ centralUnitsIn (R := 𝓞 F) J) = (γ : rStab J ⧸ _)
      rw [QuotientGroup.eq]
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      exact Subgroup.mem_subgroupOf.2 hWc
  exact Subgroup.finiteIndex_of_finite_quotient

end UnitIndex

end QuadFormsKB.QuatOrder
