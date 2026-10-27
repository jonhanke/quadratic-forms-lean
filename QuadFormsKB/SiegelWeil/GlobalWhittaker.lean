/-
# The Euler product of the local Whittaker integrals (the local–global constant)

**Layer:** global bookkeeping of local constants (product formulas only; no adelic integration).

**Setting.** $F$ a number field, $Q = \sum_{i<n}b_ix_i^2$ with $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m \ge 2$ (0-based),
$a_i = b_i \in F^\times$; at each finite place the local Whittaker integral of the lattice section is
$W_v(t) = \gamma_{V,v}\,c_{B,v}\,\operatorname{vol}(\mathcal O_v)^{n-1}\beta_v(t)$ (`whittakerV_eq_NF_localDensity`), and at $\infty$
the constants are $\gamma_{V,\infty}$, $c_{B,\infty}$ of the archimedean model `localDataInf` (the block $F_\infty$).

**Results.**
* **`globalConst_eq`** (the constants multiply to a power of the discriminant):
  $$\big(\gamma_{V,\infty}\,c_{B,\infty}\big)\cdot\prod_{v<\infty}\gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^{n-1} = |d_F|^{-(n-1)/2}.$$
  From Weil's $\prod_u\gamma_{V,u} = 1$ (`prod_gammaV_eq_one`), the product formula $\prod_u|2b_i|_u = 1$
  (`prod_modulus_eq_one`), and $\prod_v\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}$ (`finprod_selfDualV_real`).
* **`hasProd_whittakerV`** (the finite part of the Fourier coefficient as an Euler product): for $t \in \mathcal O_F\setminus\{0\}$,
  if $\prod_v\beta_v(t)$ converges to $P$ (e.g. `NFEulerProduct`), then $\prod_vW_v(t)$ converges to $C_f\cdot P$,
  $C_f = \prod_v\gamma_{V,v}c_{B,v}\operatorname{vol}(\mathcal O_v)^{n-1}$ (a finite product), and $\gamma_{V,\infty}c_{B,\infty}C_f = |d_F|^{-(n-1)/2}$.

So the Euler product of all local Whittaker integrals is $|d_F|^{-(n-1)/2}$ times Siegel's product of local densities
(`SiegelWeil/Eisenstein.lean` assembles it with the archimedean factor).

Sources: Weil, Acta Math. 113 (1965), Ch. II–IV [unverified]; Weil, Acta Math. 111 (1964), §30, Prop. 5 [unverified];
Tate's thesis (Cassels–Fröhlich Ch. XV), §4 (the self-dual measure and $|d_F|^{1/2}$) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.LocalWhittaker
import QuadFormsKB.Analysis.AdelicPoisson

open IsDedekindDomain NumberField MeasureTheory Filter
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (a : Fin (2 * m) → Fˣ)

/-! ### Finite supports -/

lemma hasFiniteMulSupport_gammaV :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).gammaV (aV a v) := by
  have hG : ∀ i, Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    fun i => hasFiniteMulSupport_gNV (a i)
  have hGp : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ∏ i, (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    Function.HasFiniteMulSupport.prod hG Finset.univ
  have hGi : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (∏ i, (localDataV v).gN ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ :=
    hGp.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', inv_one])
  exact ((hasFiniteMulSupport_chiV_neg_one a).mul hGi).subset fun v hv => by
    simpa [LocalData.gammaV] using hv

/-- The modulus $|2a_i|_v$ at a finite place. -/
lemma md_two_mul_aV (v : HeightOneSpectrum (𝓞 F)) (i : Fin (2 * m)) :
    (localDataV v).md (2 * ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (2 * (a i : F))) := by
  rw [aV_val, map_mul, map_ofNat]; rfl

lemma hasFiniteMulSupport_sqrt_md (i : Fin (2 * m)) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Real.sqrt ((localDataV v).md (2 * ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) := by
  have h2a : (2 * (a i : F)) ≠ 0 := mul_ne_zero two_ne_zero (a i).ne_zero
  refine (hasFiniteMulSupport_modK h2a).subset fun v hv h' => hv ?_
  simp only at h' ⊢
  rw [md_two_mul_aV, h', Real.sqrt_one]

lemma hasFiniteMulSupport_cB :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (localDataV v).cB (aV a v) := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin (2 * m))), Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Real.sqrt ((localDataV v).md (2 * ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) : ℝ) : ℂ) :=
    fun i _ => (hasFiniteMulSupport_sqrt_md a i).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  exact (Function.HasFiniteMulSupport.prod (fun i => h i (Finset.mem_univ i)) Finset.univ).subset
    fun v hv => by simpa [LocalData.cB] using hv

lemma hasFiniteMulSupport_vol :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (selfDualV v).real (latticeV v 0) := by
  refine (finite_support_diffExp (F := F)).subset fun v hv => ?_
  simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero]
  intro hd
  apply hv
  simp only
  rw [selfDualV_real_latticeV, hd]; simp

/-! ### The global constant -/

lemma real_sqrt_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ) (h0 : ∀ v, 0 ≤ f v) :
    ∏ v ∈ S, Real.sqrt (f v) = Real.sqrt (∏ v ∈ S, f v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert w S hw ih => rw [Finset.prod_insert hw, Finset.prod_insert hw, ih, Real.sqrt_mul (h0 w)]

lemma real_sqrt_finprod {f : HeightOneSpectrum (𝓞 F) → ℝ} (hf : Function.HasFiniteMulSupport f)
    (h0 : ∀ v, 0 ≤ f v) : ∏ᶠ v, Real.sqrt (f v) = Real.sqrt (∏ᶠ v, f v) := by
  classical
  have hf' : (Function.mulSupport f).Finite := hf
  have hsub : Function.mulSupport (fun v => Real.sqrt (f v)) ⊆ hf'.toFinset := fun v hv =>
    hf'.mem_toFinset.mpr fun h => hv (by simp only; rw [h, Real.sqrt_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
    finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hf'.mem_toFinset.mpr hv), real_sqrt_finset_prod _ _ h0]

/-- $c_{B,\infty}\prod_vc_{B,v} = 1$: the product formula $\prod_u|2a_i|_u = 1$, coordinate by coordinate. -/
theorem cB_prod_eq_one :
    (localDataInf (F := F)).cB (aInf a) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).cB (aV a v) = 1 := by
  have hfin : ∀ i ∈ (Finset.univ : Finset (Fin (2 * m))), Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Real.sqrt ((localDataV v).md (2 * ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) : ℝ) : ℂ) :=
    fun i _ => (hasFiniteMulSupport_sqrt_md a i).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  simp only [LocalData.cB]
  rw [finprod_prod_comm _ _ hfin, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have h2a : (2 * (a i : F)) ≠ 0 := mul_ne_zero two_ne_zero (a i).ne_zero
  have hpf := prod_modulus_eq_one h2a
  set g : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => Analysis.Weil.modK (v.adicCompletion F) (algebraMap F _ (2 * (a i : F))) with hgdef
  have hg : Function.HasFiniteMulSupport g := hasFiniteMulSupport_modK h2a
  have hgs : Function.HasFiniteMulSupport fun v => Real.sqrt (g v) :=
    hg.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h', Real.sqrt_one])
  have hg0 : ∀ v, 0 ≤ g v := fun v =>
    (Analysis.Weil.modK_pos ((map_ne_zero _).mpr h2a)).le
  simp only [md_two_mul_aV]
  rw [show (∏ᶠ v, ((Real.sqrt (g v) : ℝ) : ℂ)) = ((∏ᶠ v, Real.sqrt (g v) : ℝ) : ℂ) from
    (map_finprod Complex.ofRealHom hgs).symm, real_sqrt_finprod hg hg0, ← Complex.ofReal_mul,
    ← Real.sqrt_mul (by exact (mixedEmbedding.norm_nonneg _))]
  have : (localDataInf (F := F)).md (2 * ((aInf a i : (mixedEmbedding.mixedSpace F)ˣ) : mixedEmbedding.mixedSpace F)) =
      mixedEmbedding.norm (mixedEmbedding F (2 * (a i : F))) := by
    show mixedEmbedding.norm _ = _; congr 1; simp [aInf, map_mul, map_ofNat]
  rw [this, hpf, Real.sqrt_one, Complex.ofReal_one]

/-- **The finite part of the Whittaker constant** $C_f = \prod_{v<\infty}\gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^{n-1}$
(a finite product: all factors are $1$ outside the places dividing $2\,\mathfrak d_F\prod_ia_i$). -/
def constFin : ℂ := ∏ᶠ v : HeightOneSpectrum (𝓞 F),
  (localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
    (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ)

lemma finprod_vol : ∏ᶠ v : HeightOneSpectrum (𝓞 F), (selfDualV v).real (latticeV v 0) =
    (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
  have h := finprod_selfDualV_real (F := F) (k := fun _ => 0) (by simp)
  have h1 : idealOfExps (F := F) (fun _ => 0) = 1 := by simp [idealOfExps]
  simpa [h1] using h

/-- **The global Whittaker constant** (product formulas): $\big(\gamma_{V,\infty}c_{B,\infty}\big)\cdot C_f = |d_F|^{-(n-1)/2}$, i.e.
$$\gamma_{V,\infty}\,c_{B,\infty}\prod_{v<\infty}\gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^{n-1} = \big(|d_F|^{-1/2}\big)^{n-1}.$$ -/
@[kb "weil1965" "Ch. II–IV (the constants of Siegel's formula) [unverified]; Weil (1964), §30, Prop. 5 [unverified]"]
theorem globalConst_eq :
    (localDataInf (F := F)).gammaV (aInf a) * (localDataInf (F := F)).cB (aInf a) * constFin a =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m - 1) : ℝ) : ℂ) := by
  have hvol' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hvolR : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (selfDualV v).real (latticeV v 0) ^ (2 * m - 1) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hγc : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) :=
    (hasFiniteMulSupport_gammaV a).mul (hasFiniteMulSupport_cB a)
  unfold constFin
  rw [finprod_mul_distrib hγc hvol',
    finprod_mul_distrib (hasFiniteMulSupport_gammaV a) (hasFiniteMulSupport_cB a)]
  rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ)) =
      ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) from
    (map_finprod Complex.ofRealHom hvolR).symm, ← finprod_pow (hasFiniteMulSupport_vol (F := F)), finprod_vol]
  have hγ := prod_gammaV_eq_one a
  have hc := cB_prod_eq_one a
  linear_combination ((((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m - 1) : ℝ) : ℂ)) *
      ((localDataInf (F := F)).cB (aInf a) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).cB (aV a v)) * hγ +
    ((((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * m - 1) : ℝ) : ℂ)) * hc

/-! ### The Euler product of the local Whittaker integrals -/

/-- The global form $\sum_ib_ix_i^2$ as units $a_i = b_i \in F^\times$. -/
def unitsOfInt (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) : Fin (2 * m) → Fˣ :=
  fun i => Units.mk0 (b i : F) (by exact_mod_cast hb i)

lemma aOfInt_eq_aV (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    aOfInt v b hb = aV (unitsOfInt b hb) v := by
  funext i; ext; rfl

/-- **The finite part of the Fourier coefficient as an Euler product** (every finite place, dyadic included): for
$Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m \ge 2$, and $t \in \mathcal O_F\setminus\{0\}$, if Siegel's product of local
densities converges, $\prod_v\beta_v(Q, t) = P$, then
$$\prod_{v<\infty}W_v(f_{\mathbf 1_{L_v}}, t) = C_f\cdot P,\qquad \gamma_{V,\infty}c_{B,\infty}C_f = |d_F|^{-(n-1)/2}\ (\texttt{globalConst\_eq}).$$
(Unconditional convergence `HasProd`; the factor $C_f$ is a finite product.) -/
@[kb "weil1965" "Ch. II–IV [unverified]; Siegel (1935) (the singular series as a product of densities) [unverified]"]
theorem hasProd_whittakerV (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (t : 𝓞 F) (ht : t ≠ 0)
    {P : ℝ} (hP : HasProd (fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.localDensity v (QuadForm.diag b) t) P) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerV v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F))
      (constFin (unitsOfInt b hb) * P) := by
  classical
  set c : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    (localDataV v).gammaV (aV (unitsOfInt b hb) v) * (localDataV v).cB (aV (unitsOfInt b hb) v) *
      (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) with hc
  have hcfin : Function.HasFiniteMulSupport c := by
    have hvol' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (((selfDualV v).real (latticeV v 0) ^ (2 * m - 1) : ℝ) : ℂ) :=
      (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
    have hγc : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (localDataV v).gammaV (aV (unitsOfInt b hb) v) * (localDataV v).cB (aV (unitsOfInt b hb) v) :=
      (hasFiniteMulSupport_gammaV _).mul (hasFiniteMulSupport_cB _)
    exact hγc.mul hvol'
  have hcfin' : (Function.mulSupport c).Finite := hcfin
  have hC : HasProd c (constFin (unitsOfInt b hb)) := by
    unfold constFin
    rw [finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hcfin'.mem_toFinset.mpr hv)]
    exact hasProd_prod_of_ne_finset_one fun v hv => by
      by_contra h; exact hv (hcfin'.mem_toFinset.mpr h)
  have hP' : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      ((LocalDensity.NF.localDensity v (QuadForm.diag b) t : ℝ) : ℂ)) (P : ℂ) :=
    hP.map Complex.ofRealHom Complex.continuous_ofReal
  refine (hC.mul hP').congr_fun ?_
  intro v
  simp only [hc]
  rw [whittakerV_eq_NF_localDensity v hm b hb t ht, aOfInt_eq_aV, ← selfDualV_real_Ov]

end QuadFormsKB.SiegelWeil
