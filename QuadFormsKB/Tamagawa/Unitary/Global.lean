import QuadFormsKB.Tamagawa.Unitary.Adelic
import QuadFormsKB.Tamagawa.Unitary.Arch
import QuadFormsKB.Tamagawa.Unitary.UnitaryOrth
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure

/-!
# $U(V)(\mathbb A)$, the diagonal $U(V)(F)$, Weil's Tamagawa measure and $\tau(U(V))$ (definite case)

**Layer:** Gan–Hanke–Yu's setting (Gan–Hanke–Yu 2001, §4): $F$ a totally real number field, $E = F(\omega)$, $\omega^2 = -D$, a quadratic
extension with character $\chi = \chi_{E/F}$ (`chiE F E`), $H_0$ an integral hermitian matrix over $\mathcal O_F[\omega]$,
nondegenerate, whose trace form is positive definite at every real embedding $\rho$ ($H$ totally definite, so
$G_\infty = \prod_\rho U(V)(F_\rho)$ is compact).

**Defines**
* `UInf D H₀` $= G_\infty = \prod_{\rho : F\to\mathbb R}U(V)(F_\rho)$ and **`UAdele D H₀`** $= G_\infty\times U(V)(\mathbb A_f)$;
* `archHomU`, `finHomU`, **`diagU`** : $U(V)(F)\to U(V)(\mathbb A)$ (diagonal) and **`GammaU`** its image;
* **`muTamU D H₀ E`** $= L(1,\chi)^{-1}\,|d_F|^{-m^2/2}\prod_\rho\mu_\rho\times\mu_f$, with $\mu_\rho$ = `muArchU` (Leray density at $\rho$)
  and $\mu_f$ = `muFinU` with convergence factors $\lambda_v = L_v(1,\chi)^{-1}$ (`lamL`), i.e. Weil's
  $\rho^{-1}|d_F|^{-\dim G/2}\prod_v L_v(1,\chi)\,|\omega|_v$ (Weil 1982, §2.3; Ono's convergence factors for groups whose
  maximal torus quotient is $U(1)$; the same factors as `muTamU1` for $m = 1$);
* **`tauU D H₀ E`** $=\tau(U(V)) = \mathrm{covol}(U(V)(F)\backslash U(V)(\mathbb A), \mu_{\mathrm{Tam}})$.

**Proves** `det_unitaryOrth_F` (rational unitary elements have determinant $1$ as $2m\times2m$ matrices) and the
well-definedness of the diagonal embedding.

*Status of the definition.* `muTamU` is a genuine left Haar measure. That it is Weil's Tamagawa measure needs (a) the
multipliability of $\prod_v\beta^h_v/\lambda_v$ (from the values at the good places), and (b) the
identification of `archDensityU` and `hermDensity` with gauge-form volumes (the Leray densities in $F$-rational
coordinates; Weil 1982, §2.2). Neither is used here; `tauU` is a defined quantity, not an input.
-/

open MeasureTheory Measure Topology Matrix Filter
open scoped ENNReal QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Lattices QuadFormsKB.Siegel NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

/-- **Rational unitary elements have determinant $1$** as $2m\times2m$ matrices ($D\ne0$, $H_0$ hermitian and
nondegenerate). -/
theorem det_unitaryOrth_F (hD : D ≠ 0) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)
    (γ : unitaryOrth D H₀ F) : ((γ : orthGroup (traceQFF D H₀) F) : GL (Fin (m * 2)) F).val.det = 1 := by
  obtain ⟨g, rfl⟩ := toUnitaryOrth_surjective D F hD hH γ
  rw [toUnitaryOrth_val, realifyR_apply, det_reindex_self]
  exact det_realify_unitary D F (HK_isHermitian D F hH) hdet g.2

/-- **The component at a real embedding** $U(V)(F)\to U(V)(F_\rho)$. -/
def archHomU (hD : D ≠ 0) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) (ρ : F →+* ℝ) :
    unitaryOrth D H₀ F →* UReal D H₀ ρ where
  toFun γ := ⟨⟨Matrix.GeneralLinearGroup.map ρ ((γ : orthGroup (traceQFF D H₀) F) : GL (Fin (m * 2)) F), by
      rw [mem_soReal_iff]
      have hγ := (mem_orthGroup _).1 (γ : orthGroup (traceQFF D H₀) F).2
      have hdet1 := det_unitaryOrth_F D H₀ hD hH hdet γ
      have hval : (Matrix.GeneralLinearGroup.map ρ ((γ : orthGroup (traceQFF D H₀) F) :
          GL (Fin (m * 2)) F) : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) =
          ((γ : orthGroup (traceQFF D H₀) F) : GL (Fin (m * 2)) F).val.map ρ := rfl
      have hhess : (traceQR D H₀ ρ).hessian = (traceQFF D H₀).hessian.map ρ := by
        ext i j
        simp [traceQR, traceQFF, QuadForm.hessian, QuadForm.map]
      rw [hval, hhess]
      have e : (traceQFF D H₀).hessian.map (algebraMap F F) = (traceQFF D H₀).hessian := by simp
      rw [e] at hγ
      refine ⟨?_, ?_⟩
      · rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
      · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet1, map_one]⟩, by
      show (Matrix.GeneralLinearGroup.map ρ _ : GL (Fin (m * 2)) ℝ).val * omegaRe D ρ m =
        omegaRe D ρ m * (Matrix.GeneralLinearGroup.map ρ _ : GL (Fin (m * 2)) ℝ).val
      have hc := (mem_unitaryOrth D).1 γ.2
      have hO : omegaRe D ρ m = (omegaR D m F).map ρ := by
        ext i j; simp [omegaRe, omegaR]
      have hval : (Matrix.GeneralLinearGroup.map ρ ((γ : orthGroup (traceQFF D H₀) F) :
          GL (Fin (m * 2)) F) : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) =
          ((γ : orthGroup (traceQFF D H₀) F) : GL (Fin (m * 2)) F).val.map ρ := rfl
      rw [hval, hO, ← Matrix.map_mul, ← Matrix.map_mul, hc]⟩
  map_one' := Subtype.ext (Subtype.ext (Units.ext (by simp; rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (Units.ext (by simp; rfl)))

/-- **The finite component** $U(V)(F)\to U(V)(\mathbb A_f)$ (the diagonal `diagF` of $O(V_F,q)$). -/
def finHomU : unitaryOrth D H₀ F →* UAf D H₀ where
  toFun γ := ⟨diagF (traceQFF D H₀) (γ : orthGroup (traceQFF D H₀) F), fun v => by
      show (orthMap (traceQFF D H₀) (v.adicCompletion F) (γ : orthGroup (traceQFF D H₀) F)) ∈ unitaryOrth D H₀ (v.adicCompletion F)
      rw [mem_unitaryOrth, orthMap_val]
      have hc := (mem_unitaryOrth D).1 γ.2
      have hO : omegaR D m (v.adicCompletion F) = (omegaR D m F).map (algebraMap F (v.adicCompletion F)) := by
        ext i j; simp [omegaR]
      rw [hO, ← Matrix.map_mul, ← Matrix.map_mul, hc]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp

/-- $G_\infty = \prod_{\rho : F\to\mathbb R}U(V)(F_\rho)$ (for totally real $F$ these are all the archimedean places). -/
abbrev UInf : Type := ∀ ρ : F →+* ℝ, UReal D H₀ ρ

/-- **$U(V)(\mathbb A) = G_\infty\times U(V)(\mathbb A_f)$.** -/
abbrev UAdele : Type := UInf D H₀ × UAf D H₀

/-- **The diagonal embedding** $U(V)(F)\to U(V)(\mathbb A)$. -/
def diagU (hD : D ≠ 0) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) : unitaryOrth D H₀ F →* UAdele D H₀ :=
  MonoidHom.prod (Pi.monoidHom fun ρ => archHomU D H₀ hD hH hdet ρ) (finHomU D H₀)

/-- **$U(V)(F)$ in $U(V)(\mathbb A)$.** -/
def GammaU (hD : D ≠ 0) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) : Subgroup (UAdele D H₀) :=
  (diagU D H₀ hD hH hdet).range

/-- **Weil's Tamagawa measure on $U(V)(\mathbb A)$** (definite case, $F$ totally real; `[Fact]`: the trace form is positive
definite at every real embedding): $L(1,\chi)^{-1}|d_F|^{-m^2/2}\prod_\rho\mu_\rho\times\mu_f$, $\mu_f$ with
$\lambda_v = L_v(1,\chi)^{-1}$, $\chi = \chi_{E/F}$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ρ^{-1}|d|^{-dim/2}∏ λ_v^{-1}ω_v) [unverified]; ganhankeyu2001 (4.3), p. 110"]
def muTamU [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Measure (UAdele D H₀) :=
  ENNReal.ofReal (QuadFormsKB.RegProd.LOne (chiE F E))⁻¹ •
    ENNReal.ofReal (|(discr F : ℝ)| ^ (-((m : ℝ) ^ 2 / 2))) •
      (Measure.pi fun ρ => muArchU D H₀ ρ).prod (muFinU D H₀ (lamL (chiE F E)))

/-- **The Tamagawa number** $\tau(U(V)) = \mathrm{vol}(U(V)(F)\backslash U(V)(\mathbb A))$ for `muTamU` (Gan–Hanke–Yu 2001, (4.3):
"$\tau(G) = 2$", Kottwitz, Ono). -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (τ(G)); weil1982 §2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)) [unverified]"]
def tauU [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hD : D ≠ 0) (hH : H₀.IsHermitian)
    (hdet : (HK D F H₀).det ≠ 0) (E : Type) [Field E] [NumberField E] [Algebra F E] : ℝ≥0∞ :=
  covolume (GammaU D H₀ hD hH hdet) (UAdele D H₀) (muTamU D H₀ E)

end QuadFormsKB.Tamagawa.Unitary
