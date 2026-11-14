import QuadFormsKB.Tamagawa.Unitary.Local
import QuadFormsKB.Tamagawa.Measure.AdelicSO

/-!
# The finite adelic unitary group $U(V)(\mathbb A_f)$ and its Tamagawa measure

**Layer:** $F$ a number field, $H_0$ an integral hermitian matrix over $\mathcal O_F[\omega]$, $\Lambda = \mathcal O_F[\omega]^m$
(`TraceForm.lean`); $O(V_F, q)(\mathbb A_f)$ = `OAf (traceQFF D H₀)` the restricted product of the library (`Lattices/ClassSet.lean`) for the
trace form $q$, with its topology and Borel $\sigma$-algebra (`Measure/AdelicSO.lean`).

**Defines**
* **`uAf D H₀`** $= U(V)(\mathbb A_f) = \{g\in O(V_F,q)(\mathbb A_f) : g_v\in U(V)(F_v)\ \forall v\}$ (closed subgroup; `UAf` its type);
* `KU D H₀` $= U(\hat\Lambda) = \prod_vU(\Lambda_v)$ (compact open); `GammaUf D H₀` $= U(V)(F)$ embedded diagonally;
* `finFactorU D H₀ λ` $= \prod'_v\mu_v(U(\Lambda_v)) = \prod'_v\beta^h_v(\Lambda,\Lambda)/\lambda_v$ for the local measures `muLocU`;
* **`muFinU D H₀ λ`**: the Haar measure on $U(V)(\mathbb A_f)$ normalized by $\mu_f(U(\hat\Lambda)) = \prod'_v\beta^h_v/\lambda_v$ (the
  finite part of Weil's Tamagawa measure $\prod_v\lambda_v^{-1}\omega_v$, Weil 1982, §2.3; same construction as `muFin` for
  $SO(V)$).

**Proves** `isClosed_uAf`, `isCompact_KU`, `isOpen_KU`, `sep_KU` ($U(\hat\Lambda)$ is profinite), `muFinU_KU`,
`finFactorU_eq`.

*What is not here*: the assembly of the good-place values (proved in
`GoodPlaces.lean`) $\beta^h_v = |U_m(\mathbb F_q)|q^{-m^2}$ (inert $v$),
$|GL_m(\mathbb F_q)|q^{-m^2}$ (split $v$) at the places $v\nmid2D\det H_0$, which make $\prod_v\beta^h_v/\lambda_v$ with
$\lambda_v = L_v(1,\chi_{E/F})^{-1}$ convergent. Until that assembly is done, `finFactorU` is a `tprod` whose multipliability is
open (Mathlib's `tprod` of a non-multipliable family is $1$), so `muFinU` is the Tamagawa measure only once that is
established.
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


/-- **The finite adelic unitary group** $U(V)(\mathbb A_f)$: the elements of $O(V_F, q)(\mathbb A_f)$ whose components are
$E\otimes F_v$-linear ($g_v\omega = \omega g_v$ at every $v$), i.e. the restricted product of the $U(V)(F_v)$ with respect to
the $U(\Lambda_v)$. -/
@[kb "ganhankeyu2001" "§1, p. 101 (G(𝔸), K = G(k ⊗ ℝ) × ∏_v K_v)"]
def uAf : Subgroup (OAf (traceQFF D H₀)) where
  carrier := {h | ∀ v : HeightOneSpectrum (𝓞 F), h v ∈ unitaryOrth D H₀ (v.adicCompletion F)}
  mul_mem' {a b} ha hb v := (unitaryOrth D H₀ _).mul_mem (ha v) (hb v)
  one_mem' v := (unitaryOrth D H₀ _).one_mem
  inv_mem' {a} ha v := (unitaryOrth D H₀ _).inv_mem (ha v)

/-- $U(V)(\mathbb A_f)$ as a type (subspace topology and $\sigma$-algebra). -/
abbrev UAf : Type := uAf D H₀

/-- **$U(V)(\mathbb A_f)$ is closed** in $O(V_F,q)(\mathbb A_f)$. -/
theorem isClosed_uAf : IsClosed (uAf D H₀ : Set (OAf (traceQFF D H₀))) := by
  have : (uAf D H₀ : Set (OAf (traceQFF D H₀))) =
      ⋂ v, (fun h : OAf (traceQFF D H₀) => h v) ⁻¹' (unitaryOrth D H₀ (v.adicCompletion F) : Set _) := by
    ext h; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun v => (isClosed_Uv D H₀ v).preimage (RestrictedProduct.continuous_eval v)

/-- **$U(\hat\Lambda) = \prod_vU(\Lambda_v)$**, $\Lambda = \mathcal O_F[\omega]^m$, as a subgroup of $U(V)(\mathbb A_f)$. -/
abbrev KU : Subgroup (UAf D H₀) := (locStab (traceQFF D H₀) (stdLat F (m * 2))).subgroupOf (uAf D H₀)

/-- **$U(V)(F)$** inside $U(V)(\mathbb A_f)$ (rational points, embedded diagonally). -/
abbrev GammaUf : Subgroup (UAf D H₀) := (ratPoints (traceQFF D H₀)).subgroupOf (uAf D H₀)

theorem isCompact_KU : IsCompact (KU D H₀ : Set (UAf D H₀)) :=
  (isClosed_uAf D H₀).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_locStab (traceQFF D H₀))

theorem isOpen_KU : IsOpen (KU D H₀ : Set (UAf D H₀)) :=
  (isOpen_locStab (traceQFF D H₀)).preimage continuous_subtype_val

/-- **$U(\hat\Lambda)$ is profinite**: open normal subgroups separate its points. -/
theorem sep_KU : ∀ s ∈ KU D H₀, s ≠ 1 → ∃ N : Subgroup (UAf D H₀), N ≤ KU D H₀ ∧
    (∀ x ∈ KU D H₀, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧ N.relIndex (KU D H₀) ≠ 0 ∧
    MeasurableSet (N : Set (UAf D H₀)) ∧ s ∉ N :=
  sep_of_isCompact_isOpen (KU D H₀) (isCompact_KU D H₀) (isOpen_KU D H₀)

/-- **The finite-adelic normalizing constant** $\prod'_v\mu_v(U(\Lambda_v))$ for the local measures `muLocU`. -/
def finFactorU (lam : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  ∏' v, (muLocU D H₀ v (lam v) (uStab D H₀ v : Set (Uv D H₀ v))).toReal

/-- $\prod'_v\mu_v(U(\Lambda_v)) = \prod'_v\beta^h_v/\lambda_v$ when every $\beta^h_v/\lambda_v\ge0$. -/
theorem finFactorU_eq {lam : HeightOneSpectrum (𝓞 F) → ℝ} (h : ∀ v, 0 ≤ hermDensity D H₀ v / lam v) :
    finFactorU D H₀ lam = ∏' v, hermDensity D H₀ v / lam v := by
  refine tprod_congr fun v => ?_
  rw [muLocU_uStab, ENNReal.toReal_ofReal (h v)]

/-- **The Tamagawa measure on $U(V)(\mathbb A_f)$** with convergence factors $(\lambda_v)$: the Haar measure normalized by
$\mu_f(U(\hat\Lambda)) = \prod'_v\mu_v(U(\Lambda_v)) = \prod'_v\beta^h_v(\Lambda,\Lambda)/\lambda_v$ (Weil 1982, §2.3; the
construction of `muFin` for $SO(V)$). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1} ω_v) [unverified]"]
def muFinU (lam : HeightOneSpectrum (𝓞 F) → ℝ) : Measure (UAf D H₀) :=
  haarNorm (KU D H₀) (isCompact_KU D H₀) (isOpen_KU D H₀) (Real.toNNReal (finFactorU D H₀ lam))

instance (lam : HeightOneSpectrum (𝓞 F) → ℝ) : (muFinU D H₀ lam).IsMulLeftInvariant := by
  unfold muFinU; infer_instance

/-- $\mu_f(U(\hat\Lambda)) = \prod'_v\mu_v(U(\Lambda_v))$. -/
theorem muFinU_KU (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    muFinU D H₀ lam (KU D H₀ : Set (UAf D H₀)) = ENNReal.ofReal (finFactorU D H₀ lam) :=
  haarNorm_self _ _ _

end QuadFormsKB.Tamagawa.Unitary
