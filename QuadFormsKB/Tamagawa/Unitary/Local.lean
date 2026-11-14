import QuadFormsKB.Tamagawa.Unitary.TraceForm
import QuadFormsKB.Tamagawa.Measure.LocalSO

/-!
# The local unitary groups $U(V)(F_v)$, the hermitian local density, and the local Tamagawa measure

**Layer:** $F$ a number field, $v$ a finite place, $F_v$ its completion; $H_0$ an integral hermitian matrix over
$\mathcal O_F[\omega]$ (`TraceForm.lean`), $\Lambda = \mathcal O_F[\omega]^m$, $V = E^m$.

**Defines**
* `Uv D H₀ v` $= U(V)(F_v)$ = `unitaryOrth D H₀ Fv`, a subgroup of the library's $O(V_F, q)(F_v)$ (`orthGroup`, with its topology
  from `Measure/LocalSO.lean`), with the subspace topology and its Borel $\sigma$-algebra;
* `uStab D H₀ v` $= U(\Lambda_v) = U(V)(F_v)\cap O(\mathcal O_v^{2m})$, the stabilizer of $\Lambda_v = \mathcal O_v[\omega]^m$;
* `resQ D v k` : $\mathcal O_F[\omega]\to(\mathcal O_F/\mathfrak p^k)[\omega]$ (reduction), and
  **`repCountHerm D v H₀ k`** $= \#\{X\in M_m((\mathcal O_F/\mathfrak p^k)[\omega]) : X^*H_0X = H_0\}$;
* **`hermDensity D v H₀`** $=\beta^h_v(\Lambda, \Lambda) = \lim_k\#\{X : X^*H_0X\equiv H_0\}/N\mathfrak p^{km^2}$, the hermitian local
  density ($m^2 = \dim U(V)$; the Leray density of $X\mapsto X^*H_0X$, $M_m(\mathcal O_v[\omega])\to\mathrm{Herm}_m(\mathcal O_v[\omega])$,
  in the coordinates $(1,\omega)$, the hermitian analogue of `LocalDensity.NF.localDensityForm`);
* **`muLocU D H₀ v λ`**: the **local Tamagawa measure** of $U(V)$ at $v$ with convergence factor $\lambda_v$: the Haar
  measure on $U(V)(F_v)$ normalized by $\mu_v(U(\Lambda_v)) = \beta^h_v(\Lambda,\Lambda)/\lambda_v$ (the normalization of
  `muLocSO`).

**Proves**
* `isClosed_Uv`: $U(V)(F_v)$ is closed in $O(V_F,q)(F_v)$; hence locally compact, second countable, Borel;
* `isCompact_uStab`, `isOpen_uStab`: $U(\Lambda_v)$ is a compact open subgroup;
* `muLocU_uStab`: $\mu_v(U(\Lambda_v)) = \beta^h_v/\lambda_v$; `muLocU` is left invariant and finite on compacts.

*Normalization.* For $m = 1$, $H_0 = (1)$: $U(\Lambda_v) = \{t\in\mathcal O_v[\omega] : t\bar t = 1\}$ and $\beta^h_v = \lim_k
\#\{x : x\bar x\equiv1\}/N\mathfrak p^k$, the measure of `UnitaryOne.lean` (Siegel's $\alpha_v$ of $x^2 + Dy^2$).
-/

open MeasureTheory Measure Topology Matrix Filter
open scoped QuadraticAlgebra
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Lattices NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))
variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "N𝔭" => (Ideal.absNorm v.asIdeal : ℝ)

/-! ### The local group and its lattice stabilizer -/

/-- **$U(V)(F_v)$**, the unitary group at the finite place $v$ (as a subgroup of $O(V_F, q)(F_v)$). -/
abbrev Uv : Type := unitaryOrth D H₀ Fv

/-- **$U(V)(F_v)$ is closed** in $O(V_F, q)(F_v)$ (cut out by $g\omega = \omega g$). -/
theorem isClosed_Uv : IsClosed (unitaryOrth D H₀ Fv : Set (orthGroup (traceQFF D H₀) Fv)) := by
  have hv : Continuous fun g : orthGroup (traceQFF D H₀) Fv => (g : GL (Fin (m * 2)) Fv).val :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hv.matrix_mul continuous_const) (continuous_const.matrix_mul hv)

instance : LocallyCompactSpace (Uv D H₀ v) := (isClosed_Uv D H₀ v).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (Uv D H₀ v) := Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- $U(V)(F_v)$ carries the subspace $\sigma$-algebra, which is its Borel $\sigma$-algebra. -/
instance : BorelSpace (Uv D H₀ v) :=
  inferInstanceAs (BorelSpace (unitaryOrth D H₀ Fv : Set (orthGroup (traceQFF D H₀) Fv)))

/-- **$U(\Lambda_v)$**: the stabilizer in $U(V)(F_v)$ of $\Lambda_v = \mathcal O_v[\omega]^m$ ($=\mathcal O_v^{2m}$ in the coordinates of
the trace form). -/
@[kb "ganhankeyu2001" "§1, p. 101 and (4.1), p. 109 (K_v the stabilizer of Λ_v)"]
def uStab : Subgroup (Uv D H₀ v) := (stdStab (traceQFF D H₀) v).subgroupOf (unitaryOrth D H₀ Fv)

theorem isCompact_uStab : IsCompact (uStab D H₀ v : Set (Uv D H₀ v)) :=
  (isClosed_Uv D H₀ v).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_stdStab v (traceQFF D H₀))

theorem isOpen_uStab : IsOpen (uStab D H₀ v : Set (Uv D H₀ v)) :=
  (isOpen_stdStab v (traceQFF D H₀)).preimage continuous_subtype_val

/-! ### The hermitian local density -/

/-- **Reduction mod $\mathfrak p^k$**: $\mathcal O_F[\omega]\to(\mathcal O_F/\mathfrak p^k)[\omega]$, $x + y\omega\mapsto\bar x + \bar y\omega$. -/
def resQ (k : ℕ) :
    QuadO D →+* QuadraticAlgebra (𝓞 F ⧸ v.asIdeal ^ k) (Ideal.Quotient.mk (v.asIdeal ^ k) (-D)) 0 where
  toFun z := ⟨Ideal.Quotient.mk _ z.re, Ideal.Quotient.mk _ z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

/-- **$A_{\mathfrak p^k}(H_0, H_0)$**: the number of $X\in M_m((\mathcal O_F/\mathfrak p^k)[\omega])$ with $X^*H_0X = H_0$ over
$(\mathcal O_F/\mathfrak p^k)[\omega]$ (the hermitian analogue of `LocalDensity.NF.repCountForm`; Shimura's and Kitaoka's local
densities of hermitian forms). -/
@[kb "ganhankeyu2001" "§1, p. 101 (Shimura's mass of hermitian lattices) [running text]"]
def repCountHerm (k : ℕ) : ℕ :=
  Nat.card {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra (𝓞 F ⧸ v.asIdeal ^ k)
      (Ideal.Quotient.mk (v.asIdeal ^ k) (-D)) 0) //
    Xᴴ * H₀.map (resQ D v k) * X = H₀.map (resQ D v k)}

/-- **The hermitian local density** $\beta^h_v(\Lambda,\Lambda) = \lim_k A_{\mathfrak p^k}(H_0, H_0)/N\mathfrak p^{k m^2}$ ($m^2 = \dim U(V)$
$= \dim_F M_m(E) - \dim_F\mathrm{Herm}_m(E)$; Lean's `limUnder`). -/
@[kb "ganhankeyu2001" "(2.6), p. 104 (∫_{K_v} |ω_G|, the local volume) [running text]"]
def hermDensity : ℝ :=
  limUnder atTop fun k : ℕ => (repCountHerm D H₀ v k : ℝ) / N𝔭 ^ (k * m ^ 2)

/-! ### The local Tamagawa measure -/

/-- **The local Tamagawa measure on $U(V)(F_v)$** with convergence factor $\lambda_v$ (default $1$): the Haar measure
normalized by $\mu_v(U(\Lambda_v)) = \beta^h_v(\Lambda,\Lambda)/\lambda_v$ (Weil 1982, §2.2–2.3; the normalization of
`muLocSO`). -/
@[kb "weil1982" "§2.2 (local measures), §2.3, p. 21 (convergence factors λ_v) [unverified]"]
def muLocU (lam : ℝ := 1) : Measure (Uv D H₀ v) :=
  haarNorm (uStab D H₀ v) (isCompact_uStab D H₀ v) (isOpen_uStab D H₀ v)
    (Real.toNNReal (hermDensity D H₀ v / lam))

instance (lam : ℝ) : IsMulLeftInvariant (muLocU D H₀ v lam) := by unfold muLocU; infer_instance

instance (lam : ℝ) : IsFiniteMeasureOnCompacts (muLocU D H₀ v lam) := by unfold muLocU; infer_instance

/-- **$\mu_v(U(\Lambda_v)) = \beta^h_v(\Lambda,\Lambda)/\lambda_v$.** -/
theorem muLocU_uStab (lam : ℝ) :
    muLocU D H₀ v lam (uStab D H₀ v : Set (Uv D H₀ v)) = ENNReal.ofReal (hermDensity D H₀ v / lam) :=
  haarNorm_self _ _ _

end QuadFormsKB.Tamagawa.Unitary
