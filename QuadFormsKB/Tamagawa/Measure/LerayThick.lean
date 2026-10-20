import Mathlib
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# Thickened Leray measures on a local field: scaling and orthogonal invariance

Let $K$ be a locally compact field (e.g. $F_v$), $\nu$ a Haar measure on $K$, $V = K^m$ with $\mathrm{vol} = \nu^{\otimes m}$,
and $Q : V \to K$ a function (a quadratic form). For a set $B \subseteq K$ with $0 < \nu(B) < \infty$ the
**thickened Leray measure**
$$\lambda_B = \nu(B)^{-1}\,\mathrm{vol}|_{Q^{-1}(B)}$$
is the volume of the shell $Q \in B$ per unit of $\nu(B)$. For $B = \rho + \mathfrak p^k$ and $k \to \infty$ it tends to the Leray
measure $dx/dQ$ on $\{Q = \rho\}$ (the limit is constructed in `LerayFiniteNF.lean`). Nothing here uses $\mathrm{ord}$:

* `map_smul_lerayThick` (**scaling**): if $Q(tx) = t^2Q(x)$ then $(x\mapsto tx)_*\lambda_B = \Delta(t)^{2-m}\lambda_{t^2B}$,
  $\Delta = $ `distribHaarChar K`. So $\rho \mapsto t^2\rho$, $x \mapsto tx$ carries the Leray measure to $|t|^{m-2}$ times the
  Leray measure (homogeneity of degree $m - 2$ on the cone, $B = \{0\}$-neighbourhoods).
* `map_mulVec_lerayThick` (**orthogonal invariance**): for $g \in \mathrm{GL}_m(K)$ with $Q \circ g = Q$ and $\Delta_K(\det g) = 1$
  (every isometry of a nondegenerate form has $\det = \pm1$), $g_*\lambda_B = \lambda_B$.
-/

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal Pointwise
open Matrix.GLmulVec

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayThick

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {m : ℕ}

/-- The ambient measure on $V = K^m$. -/
abbrev volV (ν : Measure K) (m : ℕ) : Measure (Fin m → K) := Measure.pi fun _ => ν

/-- **The thickened Leray measure** $\lambda_B = \nu(B)^{-1}\,\mathrm{vol}|_{\{Q \in B\}}$. -/
def lerayThick (ν : Measure K) (Q : (Fin m → K) → K) (B : Set K) : Measure (Fin m → K) :=
  (ν B)⁻¹ • (volV ν m).restrict (Q ⁻¹' B)

theorem lerayThick_apply (ν : Measure K) (Q : (Fin m → K) → K) (B : Set K) {S : Set (Fin m → K)}
    (hS : MeasurableSet S) : lerayThick ν Q B S = (ν B)⁻¹ * volV ν m (S ∩ Q ⁻¹' B) := by
  rw [lerayThick, Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul]

/-- In real terms: for $0 < \nu(B) < \infty$ and a finite-volume shell piece. -/
theorem lerayThick_eq_ofReal (ν : Measure K) (Q : (Fin m → K) → K) (B : Set K) {S : Set (Fin m → K)}
    (hS : MeasurableSet S) (hB0 : ν B ≠ 0) (hBt : ν B ≠ ⊤) (hfin : volV ν m (S ∩ Q ⁻¹' B) ≠ ⊤) :
    lerayThick ν Q B S = ENNReal.ofReal ((volV ν m).real (S ∩ Q ⁻¹' B) / ν.real B) := by
  have hpos : 0 < ν.real B := ENNReal.toReal_pos hB0 hBt
  rw [lerayThick_apply ν Q B hS, ENNReal.ofReal_div_of_pos hpos, Measure.real, Measure.real,
    ENNReal.ofReal_toReal hfin, ENNReal.ofReal_toReal hBt, ENNReal.div_eq_inv_mul]

variable (ν : Measure K) [ν.IsAddHaarMeasure]

/-- $\mathrm{GL}_m$ scaling for the scalar matrix: $(x \mapsto tx)_*\mathrm{vol} = \Delta(t)^{-m}\mathrm{vol}$. -/
theorem map_smul_volV (t : Kˣ) :
    Measure.map (fun x : Fin m → K => (t : K) • x) (volV ν m) = ((distribHaarChar K t) ^ m)⁻¹ • volV ν m := by
  have := pi_borelSpace (R := K) (Fin m)
  have h := map_mulVec_eq_glHaarChar_inv (volV ν m) (diagGL fun _ : Fin m => t)
  rw [glHaarChar_diagGL] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  convert h using 2
  funext x i
  simp [coe_diagGL, mulVec_diagonal]

/-- The scaling map is a measurable equivalence. -/
def smulEquiv (t : Kˣ) : (Fin m → K) ≃ᵐ (Fin m → K) :=
  (MeasurableEquiv.smul t : (Fin m → K) ≃ᵐ (Fin m → K))

theorem coe_smulEquiv (t : Kˣ) : ⇑(smulEquiv (K := K) (m := m) t) = fun x => (t : K) • x := by
  funext x; simp [smulEquiv, Units.smul_def]

/-- **Scaling of the thickened Leray measure.** If $Q(tx) = t^2Q(x)$ for all $x$, then
$(x \mapsto tx)_*\lambda_B = \Delta(t)^2\Delta(t)^{-m}\lambda_{t^2B}$. -/
theorem map_smul_lerayThick (Q : (Fin m → K) → K) (t : Kˣ) (hQ : ∀ x, Q ((t : K) • x) = (t : K) ^ 2 * Q x)
    (B : Set K) :
    Measure.map (fun x : Fin m → K => (t : K) • x) (lerayThick ν Q B) =
      ((distribHaarChar K t : ℝ≥0∞) ^ 2 / (distribHaarChar K t : ℝ≥0∞) ^ m) •
        lerayThick ν Q (((t ^ 2 : Kˣ) : K) • B) := by
  have := pi_borelSpace (R := K) (Fin m)
  set e := smulEquiv (K := K) (m := m) t
  have he : (fun x : Fin m → K => (t : K) • x) = ⇑e := (coe_smulEquiv t).symm
  have hpre : (fun x : Fin m → K => (t : K) • x) ⁻¹' (Q ⁻¹' (((t ^ 2 : Kˣ) : K) • B)) = Q ⁻¹' B := by
    ext x
    simp only [mem_preimage, hQ]
    have : ((t ^ 2 : Kˣ) : K) • B = ((t : K) ^ 2) • B := by simp
    rw [this]
    show ((t : K) ^ 2) • Q x ∈ ((t : K) ^ 2) • B ↔ Q x ∈ B
    exact smul_mem_smul_set_iff₀ (pow_ne_zero 2 t.ne_zero) B (Q x)
  have hνB' : ν (((t ^ 2 : Kˣ) : K) • B) = (distribHaarChar K t : ℝ≥0∞) ^ 2 * ν B := by
    have h := distribHaarChar_mul ν (t ^ 2) B
    have h2 : ((t ^ 2 : Kˣ) : K) • B = (t ^ 2 : Kˣ) • B := by simp [Units.smul_def]
    rw [h2, ← h, map_pow]
    simp
  have hΔ0 : (distribHaarChar K t : ℝ≥0∞) ≠ 0 := by
    simpa using (distribHaarChar_pos (A := K) (g := t)).ne'
  have hΔt : (distribHaarChar K t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hemb : MeasurableEmbedding (fun x : Fin m → K => (t : K) • x) := by
    rw [he]; exact e.measurableEmbedding
  have hmap : Measure.map (fun x : Fin m → K => (t : K) • x) ((volV ν m).restrict (Q ⁻¹' B)) =
      (((distribHaarChar K t) ^ m)⁻¹ : ℝ≥0) • (volV ν m).restrict (Q ⁻¹' (((t ^ 2 : Kˣ) : K) • B)) := by
    have h1 := hemb.restrict_map (volV ν m) (Q ⁻¹' (((t ^ 2 : Kˣ) : K) • B))
    rw [hpre] at h1
    rw [← h1, map_smul_volV ν t]
    simp [Measure.restrict_smul]
  rw [lerayThick, lerayThick, Measure.map_smul, hmap, hνB']
  ext S hS
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  have hD2 : ((distribHaarChar K t : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero 2 hΔ0
  have hD2t : ((distribHaarChar K t : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top hΔt
  have hpos := (distribHaarChar_pos (A := K) (g := t)).ne'
  rw [ENNReal.coe_inv (pow_ne_zero m hpos), ENNReal.coe_pow, ENNReal.mul_inv (Or.inl hD2) (Or.inl hD2t),
    div_eq_mul_inv]
  have hc : (distribHaarChar K t : ℝ≥0∞) ^ 2 * ((distribHaarChar K t : ℝ≥0∞) ^ 2)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hD2 hD2t
  generalize ((volV ν m).restrict (Q ⁻¹' (((t ^ 2 : Kˣ) : K) • B))) S = X
  generalize ((distribHaarChar K t : ℝ≥0∞) ^ m)⁻¹ = a
  calc (ν B)⁻¹ * (a * X) = ((distribHaarChar K t : ℝ≥0∞) ^ 2 * ((distribHaarChar K t : ℝ≥0∞) ^ 2)⁻¹) *
        ((ν B)⁻¹ * (a * X)) := by rw [hc, one_mul]
    _ = _ := by ring
  exact hemb.measurable.aemeasurable

/-- The measurable equivalence $x \mapsto gx$ of $K^m$ for $g \in \mathrm{GL}_m(K)$. -/
def glEquiv (g : GL (Fin m) K) : (Fin m → K) ≃ᵐ (Fin m → K) where
  toFun x := (g : Matrix (Fin m) (Fin m) K) *ᵥ x
  invFun x := ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x
  left_inv x := by
    simp [Matrix.mulVec_mulVec]
  right_inv x := by
    simp [Matrix.mulVec_mulVec]
  measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
  measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable

theorem coe_glEquiv (g : GL (Fin m) K) :
    ⇑(glEquiv g) = fun x => (g : Matrix (Fin m) (Fin m) K) *ᵥ x := rfl

/-- **Orthogonal invariance of the thickened Leray measure.** If $g \in \mathrm{GL}_m(K)$ satisfies $Q \circ g = Q$ and
$\Delta_K(\det g) = 1$ (automatic for $\det g = \pm1$), then $g_*\lambda_B = \lambda_B$. -/
theorem map_mulVec_lerayThick (Q : (Fin m → K) → K) (g : GL (Fin m) K)
    (hg : ∀ x, Q ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = Q x)
    (hdet : distribHaarChar K (GeneralLinearGroup.det g) = 1) (B : Set K) :
    Measure.map (fun x => (g : Matrix (Fin m) (Fin m) K) *ᵥ x) (lerayThick ν Q B) = lerayThick ν Q B := by
  have := pi_borelSpace (R := K) (Fin m)
  have hemb : MeasurableEmbedding (fun x : Fin m → K => (g : Matrix (Fin m) (Fin m) K) *ᵥ x) :=
    (glEquiv g).measurableEmbedding
  have hvol : Measure.map (fun x : Fin m → K => (g : Matrix (Fin m) (Fin m) K) *ᵥ x) (volV ν m) = volV ν m := by
    have h := map_mulVec_eq_glHaarChar_inv (volV ν m) g
    rw [glHaarChar_eq_of_field, hdet] at h
    simpa using h
  have hpre : (fun x : Fin m → K => (g : Matrix (Fin m) (Fin m) K) *ᵥ x) ⁻¹' (Q ⁻¹' B) = Q ⁻¹' B := by
    ext x; simp [hg]
  rw [lerayThick, Measure.map_smul, ← hpre, ← hemb.restrict_map, hvol, hpre]
  exact hemb.measurable.aemeasurable

end QuadFormsKB.Tamagawa.Measure.LerayThick
