import Mathlib
import QuadFormsKB.Tamagawa.Measure.LerayProps
import QuadFormsKB.Tamagawa.Measure.FibreLeray

/-!
# Transport of the Leray measures under a linear map scaling the form

Let $Q, Q'$ be quadratic forms on $V_v = F_v^n$, $A \in \mathrm{GL}_n(F_v)$ and $c \in F_v^\times$ with
$Q(Ax) = c\,Q'(x)$ for all $x$. Writing $\Delta = $ `distribHaarChar Fv`, the finite-place Leray measures satisfy
$$A_*\,\sigma_{Q',\rho'} \;=\; \frac{\Delta(c)}{\Delta(\det A)}\,\sigma_{Q,\,c\rho'}.$$

* `map_mulVec_lerayThick_scale` (thickened level, any $K$): $A_*\lambda_{Q',\,c^{-1}B} = \frac{\Delta(c)}{\Delta(\det A)}\lambda_{Q,B}$,
  using $A^{-1}Q^{-1}(B) = Q'^{-1}(c^{-1}B)$, $\mathrm{vol}(AX) = \Delta(\det A)\mathrm{vol}(X)$, $\nu(c^{-1}B) = \Delta(c)^{-1}\nu(B)$.
* `shell_inv_smul`: $c^{-1}(c\rho' + \mathfrak p^k) = \rho' + \mathfrak p^{k + v(c)}$ is again a shell, so the limit along $k$ is
  unaffected by the shift.
* `lerayMeasure_map_transport`: the statement for `lerayMeasure`, proved via `measure_ext_Cz`.
* `sig_map_transport`: the corollary for `FibreLeray.sig` (forms over $\mathcal O_F$, standard Haar measure).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix Set
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.LerayCone
open QuadFormsKB.Tamagawa.Measure.LerayFinite QuadFormsKB.Tamagawa.Measure.FibreLeray
open Matrix.GLmulVec

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayTransport

section Thick

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {m : ℕ}
  (ν : Measure K) [ν.IsAddHaarMeasure]

/-- **Transport of the thickened Leray measure.** If $Q(Ax) = c\,Q'(x)$ for all $x$ then
$A_*\lambda_{Q',\,c^{-1}B} = \frac{\Delta(c)}{\Delta(\det A)}\lambda_{Q,B}$. -/
theorem map_mulVec_lerayThick_scale (Q Q' : (Fin m → K) → K) (A : GL (Fin m) K) (c : Kˣ)
    (hA : ∀ x, Q ((A : Matrix (Fin m) (Fin m) K) *ᵥ x) = (c : K) * Q' x) (B : Set K) :
    Measure.map (fun x => (A : Matrix (Fin m) (Fin m) K) *ᵥ x)
        (lerayThick ν Q' (((c⁻¹ : Kˣ) : K) • B)) =
      ((distribHaarChar K c : ℝ≥0∞) / (distribHaarChar K (GeneralLinearGroup.det A) : ℝ≥0∞)) •
        lerayThick ν Q B := by
  have := pi_borelSpace (R := K) (Fin m)
  have hemb : MeasurableEmbedding (fun x : Fin m → K => (A : Matrix (Fin m) (Fin m) K) *ᵥ x) :=
    (glEquiv A).measurableEmbedding
  have hvol : Measure.map (fun x : Fin m → K => (A : Matrix (Fin m) (Fin m) K) *ᵥ x) (volV ν m) =
      ((distribHaarChar K (GeneralLinearGroup.det A))⁻¹ : ℝ≥0) • volV ν m := by
    have h := map_mulVec_eq_glHaarChar_inv (volV ν m) A
    rw [glHaarChar_eq_of_field] at h
    exact h
  have hpre : (fun x : Fin m → K => (A : Matrix (Fin m) (Fin m) K) *ᵥ x) ⁻¹' (Q ⁻¹' B) =
      Q' ⁻¹' (((c⁻¹ : Kˣ) : K) • B) := by
    ext x
    simp only [mem_preimage, hA]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by simp)]
    simp
  have hνB : ν (((c⁻¹ : Kˣ) : K) • B) = ((distribHaarChar K c : ℝ≥0∞))⁻¹ * ν B := by
    have h := distribHaarChar_mul ν (c⁻¹) B
    have h2 : ((c⁻¹ : Kˣ) : K) • B = (c⁻¹ : Kˣ) • B := by simp [Units.smul_def]
    rw [h2, ← h, map_inv]
    simp [ENNReal.coe_inv (distribHaarChar_pos (A := K) (g := c)).ne']
  have hΔ0 : (distribHaarChar K c : ℝ≥0∞) ≠ 0 := by
    simpa using (distribHaarChar_pos (A := K) (g := c)).ne'
  have hΔt : (distribHaarChar K c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : Measure.map (fun x : Fin m → K => (A : Matrix (Fin m) (Fin m) K) *ᵥ x)
      ((volV ν m).restrict (Q' ⁻¹' (((c⁻¹ : Kˣ) : K) • B))) =
      ((distribHaarChar K (GeneralLinearGroup.det A))⁻¹ : ℝ≥0) • (volV ν m).restrict (Q ⁻¹' B) := by
    have h1 := hemb.restrict_map (volV ν m) (Q ⁻¹' B)
    rw [hpre] at h1
    rw [← h1, hvol]
    simp [Measure.restrict_smul]
  rw [lerayThick, lerayThick, Measure.map_smul, hmap, hνB]
  ext S hS
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  have hpos := (distribHaarChar_pos (A := K) (g := GeneralLinearGroup.det A)).ne'
  rw [ENNReal.coe_inv hpos, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hΔt))
    (Or.inl (ENNReal.inv_ne_top.mpr hΔ0)), inv_inv, div_eq_mul_inv]
  generalize ((volV ν m).restrict (Q ⁻¹' B)) S = X
  generalize (ν B)⁻¹ = y
  generalize ((distribHaarChar K (GeneralLinearGroup.det A) : ℝ≥0) : ℝ≥0∞)⁻¹ = e
  generalize (distribHaarChar K c : ℝ≥0∞) = d
  ring
  exact hemb.measurable.aemeasurable

end Thick

section Finite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- **Shells are permuted by scaling**: if $v(c) = q^{-a}$-ish, i.e. `Valued.v c = exp a`, then for $k + a \ge 0$,
$c^{-1}(c\rho' + \mathfrak p^k) = \rho' + \mathfrak p^{k+a}$. -/
lemma shell_inv_smul (c : Fvˣ) (a : ℤ) (hc : Valued.v (c : Fv) = exp a) (ρ' : Fv) (k : ℕ)
    (hk : 0 ≤ (k : ℤ) + a) :
    (((c⁻¹ : Fvˣ) : Fv) • shell v ((c : Fv) * ρ') k) = shell v ρ' (((k : ℤ) + a).toNat) := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by simp)]
  simp only [shell, Set.mem_ofPred_eq, inv_inv, Units.val_inv_eq_inv_val, smul_eq_mul, inv_inv]
  have e1 : (c : Fv) * y - (c : Fv) * ρ' = (c : Fv) * (y - ρ') := by ring
  rw [e1, map_mul, hc, mul_comm, ← le_div_iff₀ (by simp), ← exp_sub]
  have : ((((k : ℤ) + a).toNat : ℕ) : ℤ) = (k : ℤ) + a := Int.toNat_of_nonneg hk
  rw [this]
  have e2 : (-(k : ℤ) - a) = -((k : ℤ) + a) := by ring
  rw [e2]

section Props

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]
  (Q Q' : QuadForm (v.adicCompletionIntegers F) n) (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)

/-- **Transport of the Leray measure under a linear map scaling the form.** If $A \in \mathrm{GL}_n(F_v)$,
$c \in F_v^\times$ and $Q(Ax) = c\,Q'(x)$ for all $x$, then
$A_*\sigma_{Q',\rho'} = \frac{\Delta(c)}{\Delta(\det A)}\,\sigma_{Q,\,c\rho'}$. -/
theorem lerayMeasure_map_transport (A : GL (Fin n) Fv) (c : Fvˣ)
    (hA : ∀ x, Qv v Q ((A : Matrix (Fin n) (Fin n) Fv) *ᵥ x) = (c : Fv) * Qv v Q' x) (ρ' : Fv) :
    Measure.map (fun x => (A : Matrix (Fin n) (Fin n) Fv) *ᵥ x) (lerayMeasure v ν Q' hQ' ρ') =
      ((distribHaarChar Fv c : ℝ≥0∞) / (distribHaarChar Fv (GeneralLinearGroup.det A) : ℝ≥0∞)) •
        lerayMeasure v ν Q hQ ((c : Fv) * ρ') := by
  have hmeas : Measurable fun x : Fin n → Fv => (A : Matrix (Fin n) (Fin n) Fv) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hpre0 : (fun x => (A : Matrix (Fin n) (Fin n) Fv) *ᵥ x) ⁻¹' {0} = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have := congrArg (fun y => ((A⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) h
      simpa [Matrix.mulVec_mulVec] using this
    · rintro rfl; simp
  -- the valuation of `c`
  have hc0 : Valued.v (c : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero c)
  set a : ℤ := WithZero.log (Valued.v (c : Fv)) with ha
  have hca : Valued.v (c : Fv) = exp a := (exp_log hc0).symm
  refine measure_ext_Cz v ?_ ?_ ?_ ?_
  · rw [Measure.map_apply hmeas (measurableSet_singleton _), hpre0]
    exact lerayMeasure_singleton_zero v ν Q' hQ' ρ'
  · simp [lerayMeasure_singleton_zero]
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet]
    exact (lerayMeasure_lt_top v ν Q' hQ' ρ' (preimage_mulVec_mem_Cz v A hU)).ne
  · intro U hU
    rw [Measure.map_apply hmeas hU.2.1.measurableSet, Measure.smul_apply, smul_eq_mul]
    have hU' := preimage_mulVec_mem_Cz v A hU
    have hev1 := (show Tendsto (fun k : ℕ => (((k : ℤ) + a).toNat)) atTop atTop from
      Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2
        ⟨b + a.natAbs, fun k hk => by omega⟩).eventually (lerayMeasure_eventually v ν Q' hQ' ρ' hU')
    have hev2 := lerayMeasure_eventually v ν Q hQ ((c : Fv) * ρ') hU
    obtain ⟨k, hk1, hk2, hk3⟩ := (hev1.and (hev2.and (Filter.eventually_ge_atTop a.natAbs))).exists
    have hk : 0 ≤ (k : ℤ) + a := by omega
    rw [← hk1, ← hk2, ← shell_inv_smul v c a hca ρ' k hk]
    have hmap := map_mulVec_lerayThick_scale ν (Qv v Q) (Qv v Q') A c hA (shell v ((c : Fv) * ρ') k)
    have := congrArg (fun m => m U) hmap
    simp only [Measure.map_apply hmeas hU.2.1.measurableSet, Measure.smul_apply, smul_eq_mul] at this
    exact this

end Props

end Finite

section Sig

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- Conversion: $Q_v(x)$ for the $\mathfrak o_v$-form `NF.Qp v Q` is the evaluation of $Q$ in $F_v$. -/
lemma qv_Qp (Q : QuadForm (𝓞 F) n) (x : Fin n → Fv) : Qv v (NF.Qp v Q) x = Q.evalIn Fv x := by
  simp [Qv, NF.evalIn_Qp]

/-- **Transport of the sphere measure `sig`**: for $Q_0, Q_1$ over $\mathcal O_F$ with
$Q_0(Ax) = c\,Q_1(x)$ in $F_v$,
$A_*\,\mathrm{sig}(Q_1,\rho') = \frac{\Delta(c)}{\Delta(\det A)}\,\mathrm{sig}(Q_0, c\rho')$. -/
theorem sig_map_transport (Q₀ Q₁ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (hQ₁ : Q₁.Nondegenerate)
    (A : GL (Fin n) Fv) (c : Fvˣ)
    (hA : ∀ x, Q₀.evalIn Fv ((A : Matrix (Fin n) (Fin n) Fv) *ᵥ x) = (c : Fv) * Q₁.evalIn Fv x) (ρ' : Fv) :
    Measure.map (fun x => (A : Matrix (Fin n) (Fin n) Fv) *ᵥ x) (sig v Q₁ hQ₁ ρ') =
      ((distribHaarChar Fv c : ℝ≥0∞) / (distribHaarChar Fv (GeneralLinearGroup.det A) : ℝ≥0∞)) •
        sig v Q₀ hQ₀ ((c : Fv) * ρ') :=
  lerayMeasure_map_transport v (haarV v) (NF.Qp v Q₀) (NF.Qp v Q₁) (NF.nondegenerate_Qp v hQ₀)
    (NF.nondegenerate_Qp v hQ₁) A c (fun x => by simpa only [qv_Qp] using hA x) ρ'

end Sig

end QuadFormsKB.Tamagawa.Measure.LerayTransport
