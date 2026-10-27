/-
# The normalization of the sphere measures behind `AdelicSphereDensities`

**Layer:** number fields. This file checks, place by place, that the constants in the named input
`AdelicSphereDensities` (`SiegelIndefinite.lean`),
$$\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot
  \int\Phi\circ\tau_\infty\,d\sigma_\infty,$$
are the ones forced by Weil's Tamagawa measures `muTam` (finite local factors `muLocSO v Q₀ 1`, archimedean factor
$c_F(SO_N)\,\mu_\infty$). Setting: the split form $Q_0 = \langle m_0\rangle\perp Q_0'$ (`splitForm m₀ Q₀'`), $Q_0'$ in $n$
variables ($N = n + 1$), base point $\xi = e_0$, stabilizer $SO(Q_0')$, $L = \mathcal O_F e_0\perp\mathcal O_F^n$.

**Proves** (unconditional)
* **`finiteSphereGauge`** (every finite place, dyadic included): for the Leray measure $\sigma_v$ = `nuS` of the local
  sphere $\{Q = m_0\}\subseteq F_v^N$ (built from the Haar measure with $\mathrm{vol}(\mathfrak o_v) = 1$):
  $$\mu_{SO(V_v)} = |2m_0|_v^{-n}\,\mathrm{orb}_*(\sigma_v\otimes\mu_{SO(Q_0'\otimes F_v)}),\qquad
    \sigma_v(\{Q = m_0\}\cap\mathfrak o_v^N) = \beta_v(L, m_0),$$
  with the local measures $\mu$ = `muLocSO v · 1` (the finite factors of `muTam`, $\lambda_v = 1$). So the finite gauge
  normalization of `muLocSO` gives *exactly* $\beta_v$, with the Jacobian $|2m_0|_v^{-n}$ and no other constant.
* (already known, `FibreSO.prod_orbital_constants_eq_one`) the Jacobians $|2m_0|_v^{-n}$ of all places, archimedean
  ones included, multiply to $1$ (product formula), so they leave no global constant.
* **`cF_succ_eq`**: $c_F(SO_{n+1}) = |d_F|^{-n/2}\,c_F(SO_n)$ (`cF`), i.e. the archimedean normalizing constants of
  $SO(V)$ and of the stabilizer differ by exactly the factor $|d_F|^{-(N-1)/2}$ of `finDensityProduct`.

**What is still missing** for a proof of `AdelicSphereFibration` and `AdelicSphereDensities`: the adelic sphere
$T(m)_{\mathbb A}$ as a restricted product with a measurable adelic section (the local sections, integral at
almost all places), the restricted product $\sigma_{\mathbb A} = \sigma_\infty\otimes\prod'_v\sigma_v$ (Mathlib's
`Measure.infinitePi` on $\prod_v(\{Q = m_0\}\cap\mathfrak o_v^N)$, normalized by $\beta_v$), and the identification of
`muFin` with the product of the local fibrations on boxes (`muFin_boxSO_split`).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite
import QuadFormsKB.Tamagawa.Measure.FibreSO

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.LerayFinite QuadFormsKB.Tamagawa.Measure.FibreConst
  QuadFormsKB.Tamagawa.Measure.FibreSO QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-- **The finite gauge normalization of the sphere measure** (Weil 1982, Lemma 2.4.1 and §2.4): at every
finite place $v$, for $Q_0 = \langle m_0\rangle\perp Q_0'$ ($m_0\ne0$, `hm`; $Q_0'$ nondegenerate in $n\ge1$ variables,
`hQ'`, `hn`) and the local Leray measure $\sigma_v$ = `nuS` on $\{Q = m_0\}\subseteq F_v^{n+1}$:
* $\mu_{SO(V_v)} = |2m_0|_v^{-n}\cdot\mathrm{orb}_*(\sigma_v\otimes\mu_{SO(Q_0')})$ for the `muLocSO` ($\lambda_v = 1$);
* $\sigma_v(\{Q = m_0\}\cap\mathfrak o_v^{n+1}) = \beta_v(L, m_0)$ (`NF.localDensity`). -/
@[kb "weil1982" "Lemma 2.4.1, §2.4 (local fibration, gauge normalization) [unverified page]"]
theorem finiteSphereGauge (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (m₀ : 𝓞 F) (hm : m₀ ≠ 0)
    (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n) :
    muLocSO v (splitForm m₀ Q₀') 1 =
        ENNReal.ofReal ((absTwoM v m₀ ^ n)⁻¹) •
          ((nuS v m₀ hm Q₀' hQ').prod (muLocSO v Q₀' 1)).map (orbSO v m₀ hm Q₀' hQ' hn) ∧
      nuS v m₀ hm Q₀' hQ' (Pset v m₀ Q₀') = ENNReal.ofReal (NF.localDensity v (splitForm m₀ Q₀') m₀) := by
  refine ⟨lerayMeasure_orbital_finitePlace v m₀ hm Q₀' hQ' hn, ?_⟩
  have hQ : (splitForm m₀ Q₀').Nondegenerate := hQ0 m₀ Q₀' hm hQ'
  rw [nuS_Pset, lerayMeasure_latL v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v hQ)
    (n := n + 1) (by omega) (NF.ι v m₀) (NF.ι_ne_zero v hm), LocalZeta.haarV_real_O, one_pow, mul_one,
    ← NF.localDensity_eq_completion]

/-- **The archimedean normalizing constants**: $c_F(SO_{n+1}) = |d_F|^{-n/2}\,c_F(SO_n)$, $c_F(SO_n) = |d_F|^{-n(n-1)/4}$
(`cF`). The ratio $c_F(SO_N)/c_F(SO_{N-1}) = |d_F|^{-(N-1)/2}$ is the discriminant factor of `finDensityProduct`. -/
@[kb "weil1982" "§2.3, p. 21 (|d_F|^{-dim G/2}) [unverified page]"]
theorem cF_succ_eq (n : ℕ) :
    cF F (n + 1) = |(discr F : ℝ)| ^ (-((n : ℝ) / 2)) * cF F n := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  rw [cF, cF, ← Real.rpow_add hd]
  congr 1
  push_cast
  ring

end QuadFormsKB.Tamagawa.Indefinite
