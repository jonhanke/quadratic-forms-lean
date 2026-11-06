/-
# Hanke 2005, §6: local maximal lattices are similar (proof of Theorem 6.3)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $Q_0$ nondegenerate over $\mathcal O_F$, $V = (F^n, Q_0)$, $V_\mathfrak p = (F_\mathfrak p^n, Q_0)$ with the quadratic map
`qv v Q₀` ($x\mapsto Q_0(x)$ over $F_\mathfrak p$, O'Meara's convention), lattices `Submodule 𝔬 (Fin n → Fv)`.

**Proves** `exists_similitude_of_isMaximal` (Hanke thesis, proof of Theorem 6.3, p. 21): under Hanke's condition on
  $k = \mathrm{ord}_\mathfrak p\mathfrak a$, a $\mathfrak p^k$-maximal lattice is the image of an $\mathfrak o_\mathfrak p$-maximal lattice under a
  similitude of $V_\mathfrak p$ (a similitude with multiplier of valuation $k$, then O'Meara 91:2).
-/
import QuadFormsKB.Literature.Hanke2005.Sec6Defs
import QuadFormsKB.Literature.OMeara.Sec91Max
import QuadFormsKB.Literature.OMeara.Sec82Local
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import QuadFormsKB.Tamagawa.LocalRankFive

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Generic quadratic-form helpers -/

/-- $2Q(x) = x^{\mathsf T}Hx$ over any field. -/
theorem two_mul_eval_gen {K : Type} [Field K] {m : ℕ} (Q : QuadForm K m) (x : Fin m → K) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  unfold QuadForm.eval
  rw [QuadForm.evalIn_eq_dotProduct]
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
  rw [QuadForm.hessian, add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_comm x (vecMul x _),
    ← dotProduct_mulVec]
  ring

theorem single_dot_mulVec_single {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    (Pi.single i (1 : K) : Fin m → K) ⬝ᵥ (M *ᵥ (Pi.single j (1 : K) : Fin m → K)) = M i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

/-- A matrix scaling the values of $Q$ by $\xi$ satisfies $A^{\mathsf T}HA = \xi H$ (polarization). -/
theorem sim_of_eval {K : Type} [Field K] {m : ℕ} (Q : QuadForm K m) (A : Matrix (Fin m) (Fin m) K) (ξ : K)
    (h : ∀ z, Q.eval (A *ᵥ z) = ξ * Q.eval z) : Aᵀ * Q.hessian * A = ξ • Q.hessian := by
  ext i j
  have hp := QuadForm.polar_eq_hessian K Q (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1)
  have hp' := QuadForm.polar_eq_hessian K Q (Pi.single i 1) (Pi.single j 1)
  rw [← mulVec_add] at hp
  simp only [QuadForm.eval] at h
  rw [h, h, h] at hp
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hp hp'
  rw [Matrix.smul_apply, smul_eq_mul, ← single_dot_mulVec_single (Aᵀ * Q.hessian * A) i j,
    ← single_dot_mulVec_single Q.hessian i j, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]
  linear_combination (-1 : K) * hp + ξ * hp'

/-- Conversely, $A^{\mathsf T}HA = \xi H$ gives $Q(Az) = \xi Q(z)$. -/
theorem eval_of_sim {K : Type} [Field K] {m : ℕ} (h2 : (2 : K) ≠ 0) (Q : QuadForm K m) (A : Matrix (Fin m) (Fin m) K) (ξ : K)
    (h : Aᵀ * Q.hessian * A = ξ • Q.hessian) (z : Fin m → K) : Q.eval (A *ᵥ z) = ξ * Q.eval z := by

  apply mul_left_cancel₀ h2
  have e1 := two_mul_eval_gen Q (A *ᵥ z)
  have e2 := two_mul_eval_gen Q z
  have e3 : (A *ᵥ z) ⬝ᵥ (Q.hessian *ᵥ (A *ᵥ z)) = z ⬝ᵥ ((Aᵀ * Q.hessian * A) *ᵥ z) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z, vecMul_transpose]
  rw [e1, e3, h, smul_mulVec, dotProduct_smul, smul_eq_mul, ← e2]
  ring

theorem exists_zero_of_five_le {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (Qa : QuadraticForm K U) (h : 5 ≤ Module.finrank K U)
    (hF : ∀ Q : QuadForm K 5, ∃ x : Fin 5 → K, x ≠ 0 ∧ Q.eval x = 0) : ∃ u : U, u ≠ 0 ∧ Qa u = 0 := by
  let b := Module.finBasis K U
  let c : Fin 5 → Fin (Module.finrank K U) := Fin.castLE h
  let f : (Fin 5 → K) →ₗ[K] U := Fintype.linearCombination K (fun i : Fin 5 => b (c i))
  have hf : Function.Injective f := by
    have := b.linearIndependent.comp c (Fin.castLE_injective _)
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp this
  obtain ⟨x, hx, h0⟩ := hF (QuadForm.ofQuadraticForm (Qa.comp f))
  refine ⟨f x, fun h1 => hx (hf (by rw [h1, map_zero])), ?_⟩
  rw [QuadForm.eval_ofQuadraticForm] at h0
  exact h0

/-- **If every quinary form over $K$ has a nontrivial zero**, the anisotropic kernel of a nondegenerate form
has dimension at most $4$: $n - 2\,\mathrm{wittIndex}\le 4$. -/
theorem aniso_le_four_of_nondeg {K : Type} [Field K]
    (hF : ∀ Q : QuadForm K 5, ∃ x : Fin 5 → K, x ≠ 0 ∧ Q.eval x = 0)
    (Q : QuadForm K n) (hQ : Q.Nondegenerate) :
    n - 2 * QuadraticForm.wittIndex Q.toQuadraticForm ≤ 4 := by
  have hnd : (QuadraticMap.polarBilin Q.toQuadraticForm).Nondegenerate := by
    have h := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) (Q := Q) hQ
    have e : Q.toQuadraticFormIn K = Q.toQuadraticForm := by
      unfold QuadForm.toQuadraticFormIn
      congr 1
    rw [e] at h; exact h
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate _ hnd
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := QuadraticForm.wittIndex_spec _ hrad
  have := e.toLinearEquiv.finrank_eq
  simp [Module.finrank_prod, Module.finrank_pi_fintype] at this
  by_contra hgt
  have h5 : 5 ≤ Module.finrank K U := by omega
  obtain ⟨u, hu, hu0⟩ := exists_zero_of_five_le Qa h5 hF
  exact hu (ha u hu0)

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Every quinary form over $F_v$ has a nontrivial zero (`LocalRankFive.isotropic_five`, plus the degenerate case). -/
theorem exists_zero_five (Q : QuadForm Fv 5) : ∃ x : Fin 5 → Fv, x ≠ 0 ∧ Q.eval x = 0 := by
  by_cases hQ : Q.Nondegenerate
  · obtain ⟨x, hx, h⟩ := LocalRankFive.isotropic_five v Q hQ
    exact ⟨x, hx, h⟩
  · obtain ⟨x, hx, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (not_not.mp hQ)
    refine ⟨x, hx, ?_⟩
    have := two_mul_eval_gen Q x
    simp [h] at this
    exact this

/-- $Q_0$ over $F_\mathfrak p$ as a `QuadForm`. -/
abbrev Qf (Q₀ : QuadForm (𝓞 F) n) : QuadForm Fv n := (Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv)

theorem hessian_Qf (Q₀ : QuadForm (𝓞 F) n) : (Qf v Q₀).hessian = hessV v Q₀ := by
  ext i j
  simp [hessV, QuadForm.hessian, QuadForm.map]

theorem qv_apply (Q₀ : QuadForm (𝓞 F) n) (x : Fin n → Fv) : qv v Q₀ x = (Qf v Q₀).eval x :=
  QuadForm.toQuadraticForm_apply _ _

theorem nondegenerate_Qf (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : (Qf v Q₀).Nondegenerate :=
  nondegenerate_map_inj _ (algebraMap F (v.adicCompletion F)).injective _ (Tamagawa.nondegenerate_map Q₀ hQ)

theorem anisoDim_le_four (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : anisoDim v Q₀ ≤ 4 := by
  unfold anisoDim
  have e : Tamagawa.Measure.LerayPadic.QV v Q₀ = Qf v Q₀ := by
    apply QuadForm.ext
    ext i j
    simp [QuadForm.map, NF.Qp]
    rfl
  rw [e]
  exact aniso_le_four_of_nondeg (exists_zero_five v) _ (nondegenerate_Qf v Q₀ hQ)

theorem gramOf_eq (Q₀ : QuadForm (𝓞 F) n) :
    gramOf v (NF.Qp v Q₀) = (1 / 2 : Fv) • hessV v Q₀ := by
  have h1 := Tamagawa.Measure.LerayPadic.hessian_QV v Q₀
  have h2 : (Tamagawa.Measure.LerayPadic.QV v Q₀).hessian = (NF.Qp v Q₀).hessian.map (algebraMap 𝔬 Fv) := by
    ext i j
    simp [QuadForm.hessian, QuadForm.map]
  unfold gramOf hessV
  rw [← h2, h1]

/-- $z\in\mathfrak p^k\mathfrak o_\mathfrak p\iff v(z)\le e^{-k}$. -/
theorem mem_pPow_iff (k : ℕ) (z : Fv) : z ∈ pPow v k ↔ Valued.v z ≤ WithZero.exp (-(k : ℤ)) := by
  have hπ := NF.valued_π v
  have hpk : Valued.v (((NF.π v : 𝔬) : Fv) ^ k) = WithZero.exp (-(k : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hne : ((NF.π v : 𝔬) : Fv) ^ k ≠ 0 := by
    intro h; rw [h, map_zero] at hpk; exact absurd hpk.symm (WithZero.exp_ne_zero)
  unfold pPow
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    have hr : Valued.v (r : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp r.2
    change Valued.v ((r : Fv) * _) ≤ _
    rw [map_mul, hpk]
    calc Valued.v (r : Fv) * _ ≤ 1 * WithZero.exp (-(k : ℤ)) := mul_le_mul_left hr _
      _ = _ := one_mul _
  · intro h
    have hz : Valued.v (z / ((NF.π v : 𝔬) : Fv) ^ k) ≤ 1 := by
      rw [map_div₀, hpk]
      exact (div_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr h
    refine ⟨⟨z / ((NF.π v : 𝔬) : Fv) ^ k, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hz⟩, ?_⟩
    change (z / ((NF.π v : 𝔬) : Fv) ^ k) * _ = z
    field_simp

end Local

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A similitude with multiplier $\xi$ carries an $\mathfrak a'$-maximal lattice to an $\mathfrak a$-maximal one**, where
$z\in\mathfrak a\iff\xi^{-1}z\in\mathfrak a'$. -/
theorem isMaximal_locAct [Invertible (2 : Fv)] (Q₀ : QuadForm (𝓞 F) n) (g : GL (Fin n) Fv) (ξ : Fv) (hξ : ξ ≠ 0)
    (hs : g.valᵀ * hessV v Q₀ * g.val = ξ • hessV v Q₀) (a a' : Submodule 𝔬 Fv)
    (ha : ∀ z, z ∈ a ↔ ξ⁻¹ * z ∈ a') {M : Submodule 𝔬 (Fin n → Fv)}
    (hM : OMeara.IsMaximal (qv v Q₀) a' M) : OMeara.IsMaximal (qv v Q₀) a (locAct v g M) := by
  have hsim : ∀ z, qv v Q₀ (g.val *ᵥ z) = ξ * qv v Q₀ z := by
    intro z
    rw [qv_apply, qv_apply]
    exact eval_of_sim two_ne_zero _ _ ξ (by rw [hessian_Qf]; exact hs) z
  have hsimi : ∀ y, qv v Q₀ (g⁻¹.val *ᵥ y) = ξ⁻¹ * qv v Q₀ y := by
    intro y
    have := hsim (g⁻¹.val *ᵥ y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
    rw [this]
    field_simp
  obtain ⟨hlat, hnorm, hmax⟩ := hM
  refine ⟨locAct_isLattice g hlat, ?_, ?_⟩
  · unfold OMeara.normIdeal
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_locAct.mp hx
    show _ ∈ a
    rw [hsim, ha, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul]
    exact hnorm (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro K hK hle hKn
    have h1 : locAct v g⁻¹ K = M := by
      apply hmax _ (locAct_isLattice g⁻¹ hK)
      · intro x hx
        refine mem_locAct.mpr ⟨g.val *ᵥ x, hle (mem_locAct.mpr ⟨x, hx, rfl⟩), ?_⟩
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      · unfold OMeara.normIdeal
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, hx, rfl⟩
        obtain ⟨z, hz, rfl⟩ := mem_locAct.mp hx
        show _ ∈ a'
        rw [hsimi]
        exact (ha _).mp (hKn (Submodule.subset_span ⟨z, hz, rfl⟩))
    exact (locAct_eq_iff.mpr h1.symm).symm

/-- **Step 1 of the proof**: a similitude of $H$ whose multiplier has valuation exactly $e^{-k}$. -/
theorem exists_sim_val (I₃ : SimilitudeOddMultiplier F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (k : ℕ)
    (hk : (Odd n → Even k) ∧ (Even n → anisoDim v Q₀ = 2 → ¬ IsRamifiedAt v Q₀ → Even k)) :
    ∃ A : Matrix (Fin n) (Fin n) Fv, IsUnit A.det ∧ ∃ ξ : Fv, ξ ≠ 0 ∧
      Aᵀ * hessV v Q₀ * A = ξ • hessV v Q₀ ∧ Valued.v ξ = WithZero.exp (-(k : ℤ)) := by
  set c : Fv := ((NF.π v : 𝔬) : Fv) with hcdef
  have hvc : Valued.v c = WithZero.exp (-1 : ℤ) := NF.valued_π v
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hvc; exact WithZero.exp_ne_zero hvc.symm
  have hvcj : ∀ j : ℕ, Valued.v (c ^ j) = WithZero.exp (-(j : ℤ)) := by
    intro j; rw [map_pow, hvc, ← WithZero.exp_nsmul]; simp
  have scale : ∀ (A : Matrix (Fin n) (Fin n) Fv) (ξ : Fv) (m : ℕ), IsUnit A.det →
      Aᵀ * hessV v Q₀ * A = ξ • hessV v Q₀ →
      IsUnit ((c ^ m • A).det) ∧
        (c ^ m • A)ᵀ * hessV v Q₀ * (c ^ m • A) = (c ^ (2 * m) * ξ) • hessV v Q₀ := by
    intro A ξ m hA h
    refine ⟨?_, ?_⟩
    · rw [det_smul]; exact (IsUnit.mk0 _ (pow_ne_zero _ (pow_ne_zero _ hc0))).mul hA
    · simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul]
      congr 1
      ring
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨hu, he⟩ := scale 1 1 m (by simp) (by simp)
    refine ⟨_, hu, c ^ (2 * m) * 1, mul_ne_zero (pow_ne_zero _ hc0) one_ne_zero, he, ?_⟩
    rw [mul_one, hvcj]
    congr 1
    push_cast
    omega
  · have hnodd : ¬ Odd n := fun ho => (Nat.not_even_iff_odd.mpr ⟨m, hm⟩) (hk.1 ho)
    have hnE : Even n := Nat.not_odd_iff_even.mp hnodd
    have h4 := anisoDim_le_four v Q₀ hQ
    have hpar : anisoDim v Q₀ % 2 = n % 2 := by
      have hw := two_mul_wittIndex_le v Q₀ hQ
      unfold anisoDim; omega
    have hn2 : n % 2 = 0 := Nat.even_iff.mp hnE
    have hcase : anisoDim v Q₀ = 0 ∨ (anisoDim v Q₀ = 2 ∧ IsRamifiedAt v Q₀) ∨ anisoDim v Q₀ = 4 := by
      by_cases h2 : anisoDim v Q₀ = 2
      · right; left
        refine ⟨h2, ?_⟩
        by_contra hr
        exact (Nat.not_even_iff_odd.mpr ⟨m, hm⟩) (hk.2 hnE h2 hr)
      · have : anisoDim v Q₀ = 0 ∨ anisoDim v Q₀ = 4 := by omega
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    obtain ⟨ξ₁, ⟨hξ₁0, g, hg, hgξ⟩, hv₁⟩ := I₃.exists_mult hn hnE Q₀ hQ v hcase
    rw [gramOf_eq] at hgξ
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at hgξ
    have e2 : (2 : Fv) * (1 / 2) = 1 := by norm_num
    have hg' : gᵀ * hessV v Q₀ * g = ξ₁ • hessV v Q₀ := by
      calc gᵀ * hessV v Q₀ * g = ((2 : Fv) * (1 / 2)) • (gᵀ * hessV v Q₀ * g) := by rw [e2, one_smul]
        _ = (2 : Fv) • ((1 / 2 : Fv) • (gᵀ * hessV v Q₀ * g)) := by rw [smul_smul]
        _ = (2 : Fv) • ((ξ₁ * (1 / 2)) • hessV v Q₀) := by rw [hgξ]
        _ = ξ₁ • hessV v Q₀ := by rw [smul_smul]; congr 1; ring
    obtain ⟨hu, he⟩ := scale g ξ₁ m hg hg'
    refine ⟨_, hu, _, mul_ne_zero (pow_ne_zero _ hc0) hξ₁0, he, ?_⟩
    rw [map_mul, hvcj, hv₁, ← WithZero.exp_add]
    congr 1
    push_cast
    omega

theorem polar_nondeg_toQuadraticForm {K : Type} [Field K] {m : ℕ} (Q : QuadForm K m) (hQ : Q.Nondegenerate) :
    (QuadraticMap.polarBilin Q.toQuadraticForm).Nondegenerate := by
  have h := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) (Q := Q) hQ
  have e : Q.toQuadraticFormIn K = Q.toQuadraticForm := by
    unfold QuadForm.toQuadraticFormIn
    congr 1
  rw [e] at h; exact h

/-- **Hanke's local step in the proof of Theorem 6.3** (p. 21). -/
theorem exists_similitude_of_isMaximal (I₃ : SimilitudeOddMultiplier F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (k : ℕ)
    (hk : (Odd n → Even k) ∧ (Even n → anisoDim v Q₀ = 2 → ¬ IsRamifiedAt v Q₀ → Even k))
    (Λ Λ' : Submodule 𝔬 (Fin n → Fv))
    (hΛ : letI : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (qv v Q₀) (pPow v k) Λ)
    (hΛ' : letI : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (qv v Q₀) (pPow v 0) Λ') :
    ∃ g : GL (Fin n) Fv, ∃ ξ : Fv, ξ ≠ 0 ∧ g.valᵀ * hessV v Q₀ * g.val = ξ • hessV v Q₀ ∧
      Λ = locAct v g Λ' := by
  classical
  obtain ⟨A, hAdet, ξ, hξ0, hA, hvξ⟩ := exists_sim_val v I₃ hn Q₀ hQ k hk
  let g₀ : GL (Fin n) Fv := ⟨A, A⁻¹, Matrix.mul_nonsing_inv A hAdet, Matrix.nonsing_inv_mul A hAdet⟩
  have hg₀ : g₀.valᵀ * hessV v Q₀ * g₀.val = ξ • hessV v Q₀ := hA
  let : Invertible (2 : Fv) := invertibleOfNonzero two_ne_zero
  have ha : ∀ z, z ∈ pPow v k ↔ ξ⁻¹ * z ∈ pPow v 0 := by
    intro z
    rw [mem_pPow_iff, mem_pPow_iff, map_mul, map_inv₀, hvξ]
    simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), mul_one]
  have hmax'' : OMeara.IsMaximal (qv v Q₀) (pPow v k) (locAct v g₀ Λ') :=
    isMaximal_locAct v Q₀ g₀ ξ hξ0 hg₀ _ _ ha hΛ'
  have hV : (QuadraticMap.associated (qv v Q₀)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (polar_nondeg_toQuadraticForm _ (nondegenerate_Qf v Q₀ hQ)))
  have hcls := OMeara.cls_eq_of_isMaximal (qv v Q₀) hV hmax'' hΛ
  have hmem : Λ ∈ OMeara.cls (qv v Q₀) Λ := ⟨1, (OMeara.orth (qv v Q₀)).one_mem, by ext x; simp [OMeara.latMap]⟩
  rw [hcls] at hmem
  obtain ⟨σ, hσ, hσΛ⟩ := hmem
  let B : Matrix (Fin n) (Fin n) Fv := LinearMap.toMatrix' (σ : (Fin n → Fv) →ₗ[Fv] (Fin n → Fv))
  have hB : ∀ z, B *ᵥ z = σ z := fun z => by
    rw [← Matrix.toLin'_apply]
    simp [B]
  have hBorth : Bᵀ * hessV v Q₀ * B = hessV v Q₀ := by
    have := sim_of_eval (Qf v Q₀) B 1 (fun z => by
      rw [one_mul, ← qv_apply, ← qv_apply, hB]
      exact hσ z)
    rwa [hessian_Qf, one_smul] at this
  have hdetH : (hessV v Q₀).det ≠ 0 := by
    have := nondegenerate_Qf v Q₀ hQ
    rwa [QuadForm.Nondegenerate, hessian_Qf] at this
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hBorth
    rw [det_mul, det_mul, det_transpose, h0] at this
    simp at this
    exact hdetH this.symm
  let gB : GL (Fin n) Fv := ⟨B, B⁻¹, Matrix.mul_nonsing_inv B hBdet, Matrix.nonsing_inv_mul B hBdet⟩
  have hlat : ∀ M, OMeara.latMap σ M = locAct v gB M := fun M => by
    ext x
    simp only [OMeara.latMap, locAct, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [← h, hB]⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [← h]; exact (hB y).symm⟩⟩
  refine ⟨gB * g₀, ξ, hξ0, ?_, ?_⟩
  · have e : (gB * g₀).val = B * A := rfl
    rw [e, transpose_mul]
    calc Aᵀ * Bᵀ * hessV v Q₀ * (B * A) = Aᵀ * (Bᵀ * hessV v Q₀ * B) * A := by simp only [Matrix.mul_assoc]
      _ = ξ • hessV v Q₀ := by rw [hBorth]; exact hA
  · rw [locAct_mul, ← hlat, ← hσΛ]

end Local

end QuadFormsKB.Hanke2005
