import QuadFormsKB.Tamagawa.Unitary.TraceForm
import QuadFormsKB.Tamagawa.Measure.ArchSO

/-!
# The unitary group at a real place and its archimedean Leray density

**Layer:** $F$ a number field, $\rho : F\to\mathbb R$ a real embedding, $H_0$ an integral hermitian matrix over $\mathcal O_F[\omega]$
(`TraceForm.lean`). At $\rho$ the trace form becomes the real quadratic form $q^\rho$ = `traceQR D H₀ ρ` in $2m$ variables, and
$U(V)(F_\rho)$ is the commutant of $\omega$ in $SO(q^\rho)(\mathbb R)$ (the library's `ArchSO`; unitary elements have
determinant $1$ as real matrices, `Realify.det_realify_unitary`).

**Defines**
* `traceQR D H₀ ρ`, `omegaRe D m ρ`; **`uReal D H₀ ρ`** $= U(V)(F_\rho)\le SO(q^\rho)(\mathbb R)$ (`UReal` its type);
* `hermR D ρ` : $\mathcal O_F[\omega]\to\mathbb R[\omega]$, $\omega^2 = -\rho(D)$; `hermMapR` : $X\mapsto X^*H^\rho X$ on
  $M_m(\mathbb R[\omega])$ in the coordinates $(\mathrm{re},\mathrm{im})$ of the basis $(1,\omega)$;
* **`archDensityU D H₀ ρ`** $=\lim_{\varepsilon\to0^+}\mathrm{vol}\{X : |(X^*H^\rho X - H^\rho)_{ij}|_{\mathrm{re},\mathrm{im}}<\varepsilon\ \forall i,j\}
  /(2\varepsilon)^{m^2}$, the Leray density of $X\mapsto X^*HX$ at $H$ for the Lebesgue measures in the $F$-rational coordinates
  $(1,\omega)$ (the archimedean analogue of `hermDensity`, and of Siegel's limit `ArchVol.archVolSOLim` for $SO$);
* **`muArchU D H₀ ρ`** (for $q^\rho$ positive definite, i.e. $H$ definite at $\rho$): `archDensityU` times the Haar probability
  measure of the compact group $U(V)(F_\rho)$ (the construction of `ArchSO.mu`).

**Proves** `isClosed_uReal`; $U(V)(F_\rho)$ is compact for positive definite $q^\rho$; `muArchU_univ`.

*Coordinates.* The box has $m^2$ independent real coordinates ($\mathrm{re}$ of the diagonal, $\mathrm{re}$ and $\mathrm{im}$ above the
diagonal; the entries below are conjugate and the diagonal $\mathrm{im}$ vanish identically), hence the normalization
$(2\varepsilon)^{m^2}$. The basis $(1,\omega)$ is $F$-rational, so the product of these local factors with
$|d_F|^{-m^2/2}$ is Weil's Tamagawa measure (product formula); the value of `archDensityU` (the volume of $U(m)$ for the
gauge form) is not computed here.
-/

open MeasureTheory Measure Topology Matrix Filter
open scoped ENNReal QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel NumberField

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))
variable (ρ : F →+* ℝ)

/-- The trace form at the real embedding $\rho$. -/
abbrev traceQR : QuadForm ℝ (m * 2) := (traceQF D H₀).map (ρ.comp (algebraMap (𝓞 F) F))

/-- Multiplication by $\omega$ at $\rho$, in the coordinates `Fin (m * 2)`. -/
def omegaRe (m : ℕ) : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ :=
  (reindex (eCoord m) (eCoord m) (omegaO D m)).map (ρ.comp (algebraMap (𝓞 F) F))

/-- **$U(V)(F_\rho)$**: the elements of $SO(q^\rho)(\mathbb R)$ commuting with $\omega$. -/
@[kb "ganhankeyu2001" "§1, p. 101 (G(k ⊗ ℝ)) [running text]"]
def uReal : Subgroup (ArchSO (traceQR D H₀ ρ)) where
  carrier := {g | (ArchSO.incl _ g).val * omegaRe D ρ m = omegaRe D ρ m * (ArchSO.incl _ g).val}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, Units.val_mul] at ha hb ⊢
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
    set g := ArchSO.incl (traceQR D H₀ ρ) a
    calc (g⁻¹).val * omegaRe D ρ m = (g⁻¹).val * (omegaRe D ρ m * g.val) * (g⁻¹).val := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (g⁻¹).val * (g.val * omegaRe D ρ m) * (g⁻¹).val := by rw [ha]
      _ = omegaRe D ρ m * (g⁻¹).val := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- $U(V)(F_\rho)$ as a type. -/
abbrev UReal : Type := uReal D H₀ ρ

theorem isClosed_uReal : IsClosed (uReal D H₀ ρ : Set (ArchSO (traceQR D H₀ ρ))) := by
  have hv : Continuous fun g : ArchSO (traceQR D H₀ ρ) => (ArchSO.incl _ g).val :=
    Units.continuous_val.comp (ArchSO.continuous_incl _)
  exact isClosed_eq (hv.matrix_mul continuous_const) (continuous_const.matrix_mul hv)

instance [Fact (IsPosDefR (traceQR D H₀ ρ))] : CompactSpace (UReal D H₀ ρ) :=
  isCompact_iff_compactSpace.mp (isClosed_uReal D H₀ ρ).isCompact

instance : SecondCountableTopology (UReal D H₀ ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance : BorelSpace (UReal D H₀ ρ) :=
  inferInstanceAs (BorelSpace (uReal D H₀ ρ : Set (ArchSO (traceQR D H₀ ρ))))

/-! ### The archimedean Leray density -/

/-- $\mathcal O_F[\omega]\to\mathbb R[\omega]$ at $\rho$ ($\omega^2 = \rho(-D)$). -/
def hermR : QuadO D →+* QuadraticAlgebra ℝ (ρ (algebraMap (𝓞 F) F (-D))) 0 where
  toFun z := ⟨ρ (algebraMap (𝓞 F) F z.re), ρ (algebraMap (𝓞 F) F z.im)⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

/-- The matrix $X\in M_m(\mathbb R[\omega])$ with coordinates $x_{ij0} + x_{ij1}\omega$. -/
def matOfCoords (x : Fin m → Fin m → Fin 2 → ℝ) :
    Matrix (Fin m) (Fin m) (QuadraticAlgebra ℝ (ρ (algebraMap (𝓞 F) F (-D))) 0) :=
  Matrix.of fun i j => ⟨x i j 0, x i j 1⟩

/-- **The $\varepsilon$-tube** $\{X : |\mathrm{re}|, |\mathrm{im}| < \varepsilon$ for every entry of $X^*H^\rho X - H^\rho\}$. -/
def tubeU (ε : ℝ) : Set (Fin m → Fin m → Fin 2 → ℝ) :=
  {x | ∀ i j,
    abs (((matOfCoords D ρ x)ᴴ * H₀.map (hermR D ρ) * matOfCoords D ρ x - H₀.map (hermR D ρ)) i j).re < ε ∧
    abs (((matOfCoords D ρ x)ᴴ * H₀.map (hermR D ρ) * matOfCoords D ρ x - H₀.map (hermR D ρ)) i j).im < ε}

/-- **The archimedean Leray density of $U(V)$ at $\rho$**: $\lim_{\varepsilon\to0^+}\mathrm{vol}(\text{tube}_\varepsilon)/(2\varepsilon)^{m^2}$
(Lean's `limUnder`; Lebesgue measure on the coordinates $(\mathrm{re},\mathrm{im})$ in the basis $(1,\omega)$). -/
@[kb "weil1982" "§2.2 (gauge forms and their measures at the real places) [unverified]"]
def archDensityU : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => (volume (tubeU D H₀ ρ ε)).toReal / (2 * ε) ^ (m ^ 2)

/-- **The local Tamagawa measure at $\rho$** ($q^\rho$ positive definite): `archDensityU` times the Haar probability measure
on the compact group $U(V)(F_\rho)$. -/
@[kb "weil1982" "§2.2 (local measures at the real places) [unverified]"]
def muArchU [Fact (IsPosDefR (traceQR D H₀ ρ))] : Measure (UReal D H₀ ρ) :=
  ENNReal.ofReal (archDensityU D H₀ ρ) • Measure.haarMeasure ⊤

instance [Fact (IsPosDefR (traceQR D H₀ ρ))] : (muArchU D H₀ ρ).IsMulLeftInvariant := by
  unfold muArchU; infer_instance

theorem muArchU_univ [Fact (IsPosDefR (traceQR D H₀ ρ))] :
    muArchU D H₀ ρ Set.univ = ENNReal.ofReal (archDensityU D H₀ ρ) := by
  have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (UReal D H₀ ρ)))
  rw [TopologicalSpace.PositiveCompacts.coe_top] at h
  simp [muArchU, h]

end QuadFormsKB.Tamagawa.Unitary
