/-
# The Euler product of the degree-$r$ local Whittaker integrals

**Layer:** global bookkeeping of local constants (product formulas) over a number field $F$; the comparison with Siegel's formula
for forms by forms over a totally real field.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ with $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$ (0-based indices), the degree $r \le n$, and
$T$ a nondegenerate quadratic form in $r$ variables over $\mathcal O_F$. At a finite place $v$ the local Whittaker integral of the
lattice section $f_v = f_{\mathbf 1_{L_v^r}}$ is (`whittakerR_eq_localDensityForm`, `SiegelWeil/Forms/LocalWhittaker.lean`)
$$W_{T,v} = \gamma_{V,v}^{\,r}\,c_{B,v}^{\,r}\operatorname{vol}(\mathcal O_v)^{nr - r(r+1)/2}\,\beta_v(Q, T).$$

**Results.**
* **`globalConstR_eq`** (the constants multiply to Siegel's power of the discriminant):
  $$(\gamma_{V,\infty}c_{B,\infty})^r\prod_{v<\infty}\gamma_{V,v}^{\,r}c_{B,v}^{\,r}\operatorname{vol}(\mathcal O_v)^{nr - r(r+1)/2}
    = \big(|d_F|^{-1/2}\big)^{nr - r(r+1)/2} = |d_F|^{-r(2n-r-1)/4}$$
  (`globalConstR_eq_rpow`), from Weil's $\prod_u\gamma_{V,u} = 1$, the product formula $\prod_u|2b_i|_u = 1$ and
  $\prod_v\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}$. This is the factor $|d_F|^{-r(2N-r-1)/4}$ of `Tamagawa.Frames.siegelProductT`.
* **`hasProd_whittakerR`**: if $\prod_v\beta_v(Q, T)$ converges to $P$, then $\prod_{v<\infty}W_{T,v}$ converges to $C_f^{(r)}P$, with
  $C_f^{(r)}$ = `constFinR` the finite part of the constant (a finite product).

For $r = 1$ these are the degree-one `globalConst_eq` and `hasProd_whittakerV` (`SiegelWeil/GlobalWhittaker.lean`).

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II–IV [unverified];
Weil, Acta Math. 111 (1964), §30, Prop. 5 [unverified]; Siegel, Ann. Math. 36 (1935), Hauptsatz [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.LocalWhittaker
import QuadFormsKB.SiegelWeil.GlobalWhittaker

open IsDedekindDomain NumberField MeasureTheory Filter
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (a : Fin (2 * m) → Fˣ) (r : ℕ)

/-- **The finite part of the degree-$r$ Whittaker constant**
$C_f^{(r)} = \prod_{v<\infty}\gamma_{V,v}^{\,r}c_{B,v}^{\,r}\operatorname{vol}(\mathcal O_v)^{nr - r(r+1)/2}$, $n = 2m$ (a finite product: all factors
are $1$ outside the places dividing $2\,\mathfrak d_F\prod_ia_i$). -/
def constFinR : ℂ := ∏ᶠ v : HeightOneSpectrum (𝓞 F),
  (localDataV v).gammaV (aV a v) ^ r * (localDataV v).cB (aV a v) ^ r *
    (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ)

/-- **The global Whittaker constant in degree $r$** (product formulas):
$$(\gamma_{V,\infty}c_{B,\infty})^r\cdot C_f^{(r)} = \big(|d_F|^{-1/2}\big)^{nr - r(r+1)/2},\qquad n = 2m.$$ -/
@[kb "weil1965" "Ch. II–IV (the constants of Siegel's formula for forms) [unverified]; Weil (1964), §30, Prop. 5 [unverified]"]
theorem globalConstR_eq :
    ((localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a)) ^ r * constFinR a r =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * m * r - r * (r + 1) / 2 := ⟨_, rfl⟩
  rw [← hK]
  have hG := hasFiniteMulSupport_gammaV a
  have hC := hasFiniteMulSupport_cB a
  have hGr : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).gammaV (aV a v) ^ r :=
    hG.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', one_pow])
  have hCr : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).cB (aV a v) ^ r :=
    hC.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', one_pow])
  have hvolR : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (selfDualV v).real (latticeV v 0) ^ K :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hvol' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) ^ K : ℝ) : ℂ) :=
    hvolR.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have e1 : constFinR a r = (∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gammaV (aV a v)) ^ r *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).cB (aV a v)) ^ r *
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ K : ℝ) : ℂ) := by
    have hGC : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (localDataV v).gammaV (aV a v) ^ r * (localDataV v).cB (aV a v) ^ r := hGr.mul hCr
    unfold constFinR
    rw [← hK, finprod_mul_distrib hGC hvol', finprod_mul_distrib hGr hCr, finprod_pow hG, finprod_pow hC]
    congr 1
    rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), (((selfDualV v).real (latticeV v 0) ^ K : ℝ) : ℂ)) =
        ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (selfDualV v).real (latticeV v 0) ^ K : ℝ) : ℂ) from
      (map_finprod Complex.ofRealHom hvolR).symm, ← finprod_pow (hasFiniteMulSupport_vol (F := F)), finprod_vol]
  rw [e1]
  have hγ := prod_gammaV_eq_one a
  have hc := cB_prod_eq_one a
  calc ((localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a)) ^ r *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gammaV (aV a v)) ^ r *
          (∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).cB (aV a v)) ^ r *
          (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ K : ℝ) : ℂ))
      = ((localDataInf (F := F)).gammaV (aInf a) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gammaV (aV a v)) ^ r *
        ((localDataInf (F := F)).cB (aInf a) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).cB (aV a v)) ^ r *
          (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ K : ℝ) : ℂ) := by ring
    _ = _ := by rw [hγ, hc]; simp

/-- $r(r+1)/2 \le 2mr$ for $r \le 2m$. -/
lemma tri_le (hrn : r ≤ 2 * m) : r * (r + 1) / 2 ≤ 2 * m * r := by
  have : r * (r + 1) ≤ 2 * (2 * m * r) := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; simp
    · calc r * (r + 1) ≤ r * (4 * m) := Nat.mul_le_mul_left r (by omega)
        _ = 2 * (2 * m * r) := by ring
  omega

/-- **Siegel's exponent:** $\big(|d_F|^{-1/2}\big)^{nr - r(r+1)/2} = |d_F|^{-r(2n-r-1)/4}$ for $n = 2m$, $r \le n$ (the factor of
`Tamagawa.Frames.siegelProductT`). -/
lemma sqrt_inv_pow_eq_rpow (hrn : r ≤ 2 * m) :
    (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m * r - r * (r + 1) / 2) =
      |(discr F : ℝ)| ^ (-((r : ℝ) * (2 * ((2 * m : ℕ) : ℝ) - r - 1)) / 4) := by
  set D := |(discr F : ℝ)|
  have hD : 0 ≤ D := abs_nonneg _
  have he : 2 * (r * (r + 1) / 2) = r * (r + 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)
  have hle := tri_le (m := m) r hrn
  have heR : (2 : ℝ) * ((r * (r + 1) / 2 : ℕ) : ℝ) = (r : ℝ) * (r + 1) := by exact_mod_cast he
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hD, ← Real.rpow_natCast, ← Real.rpow_mul hD]
  congr 1
  rw [Nat.cast_sub hle]
  push_cast
  linear_combination (1 / 4 : ℝ) * heR

/-- **The global constant as Siegel's factor:** $(\gamma_{V,\infty}c_{B,\infty})^r\,C_f^{(r)} = |d_F|^{-r(2n-r-1)/4}$, $n = 2m$, $r \le n$. -/
@[kb "weil1965" "Ch. II–IV [unverified]; siegel1935 Hauptsatz (the factor |d_F|^{-r(2N-r-1)/4}) [unverified]"]
theorem globalConstR_eq_rpow (hrn : r ≤ 2 * m) :
    ((localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a)) ^ r * constFinR a r =
      ((|(discr F : ℝ)| ^ (-((r : ℝ) * (2 * ((2 * m : ℕ) : ℝ) - r - 1)) / 4) : ℝ) : ℂ) := by
  rw [globalConstR_eq, sqrt_inv_pow_eq_rpow r hrn]

/-! ### The Euler product of the local Whittaker integrals -/

lemma hasFiniteMulSupport_constR :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gammaV (aV a v) ^ r * (localDataV v).cB (aV a v) ^ r *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ) := by
  have hGr : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).gammaV (aV a v) ^ r :=
    (hasFiniteMulSupport_gammaV a).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', one_pow])
  have hCr : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).cB (aV a v) ^ r :=
    (hasFiniteMulSupport_cB a).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', one_pow])
  have hvol' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  exact (hGr.mul hCr).mul hvol'

/-- **The finite part of the $T$-th Fourier coefficient as an Euler product** (every finite place, dyadic included): for
$Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$, $T$ a nondegenerate quadratic form in $r \le n$ variables over
$\mathcal O_F$, if Siegel's product of forms-by-forms local densities converges, $\prod_v\beta_v(Q, T) = P$, then
$$\prod_{v<\infty}W_{T,v}(\mathbf 1_{L_v^r}) = C_f^{(r)}\cdot P,\qquad (\gamma_{V,\infty}c_{B,\infty})^rC_f^{(r)} = |d_F|^{-r(2n-r-1)/4}\
  (\texttt{globalConstR\_eq\_rpow}).$$ -/
@[kb "weil1965" "Ch. II–IV [unverified]; siegel1935 (the product of the local densities of forms) [unverified]"]
theorem hasProd_whittakerR (hrn : r ≤ 2 * m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (T : QuadForm (𝓞 F) r) (hT : T.Nondegenerate) {P : ℝ}
    (hP : HasProd (fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.localDensityForm v (QuadForm.diag b) T) P) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerR v (aOfInt v b hb) ((LocalDensity.NF.Qp v T).map (algebraMap (v.adicCompletionIntegers F)
          (v.adicCompletion F))))
      (constFinR (unitsOfInt b hb) r * P) := by
  classical
  have hcfin := hasFiniteMulSupport_constR (unitsOfInt b hb) r
  have hcfin' := hcfin
  unfold Function.HasFiniteMulSupport at hcfin'
  have hC : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gammaV (aV (unitsOfInt b hb) v) ^ r * (localDataV v).cB (aV (unitsOfInt b hb) v) ^ r *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ))
      (constFinR (unitsOfInt b hb) r) := by
    unfold constFinR
    rw [finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hcfin'.mem_toFinset.mpr hv)]
    exact hasProd_prod_of_ne_finset_one fun v hv => by
      by_contra h; exact hv (hcfin'.mem_toFinset.mpr h)
  have hP' : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      ((LocalDensity.NF.localDensityForm v (QuadForm.diag b) T : ℝ) : ℂ)) (P : ℂ) :=
    hP.map Complex.ofRealHom Complex.continuous_ofReal
  refine (hC.mul hP').congr_fun ?_
  intro v
  rw [whittakerR_eq_NF_localDensityForm v hrn b hb T hT, aOfInt_eq_aV, ← selfDualV_real_Ov]

end QuadFormsKB.SiegelWeil.Forms
