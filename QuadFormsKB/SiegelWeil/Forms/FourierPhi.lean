/-
# Siegel's $\Phi$ operator on Fourier expansions over a totally real field

**Layer:** global over a totally real number field $F$; analysis on $\mathbb H_{r+1}^d$ (no arithmetic input).

**Setting.** A function on $\mathbb H_{r+1}^d$ given by an absolutely convergent expansion $f(Z) = \sum_Tc(T)e_T(Z)$ over the forms $T$ in $r + 1$
variables over $F$ (`eT`, `ThetaR.lean`), with $c$ supported on **totally positive semidefinite** $T$: $\sigma_v(T_G) \ge 0$ at every real
place $v$ (`IsTotPSD`). The new variable is the first one (index $0$): `tailForm T` is the form in the variables $1, \dots, r$ (renumbered
$0, \dots, r-1$) and `extZero T'` the form $T'$ in the variables $1, \dots, r$, with the variable $0$ absent.

**Results.**
* `eT_blockZ_form`: $e_T(Z \oplus it) = e_{\mathrm{tail}\,T}(Z)\exp\big(-2\pi t\sum_v\sigma_v(T_{00})\big)$;
* `eq_extZero_of_psd`: a totally positive semidefinite $T$ with $T_{00} = 0$ is `extZero (tailForm T)`;
* **`tendsto_phi`** (Siegel's $\Phi$ operator on expansions): $f(Z \oplus it) \to \sum_{T'}c(\mathrm{extZero}\,T')e_{T'}(Z)$ as $t \to \infty$, for
  every $Z \in \mathbb H_r^d$: $\Phi f$ has the coefficients $c(\mathrm{extZero}\,T')$;
* **`coeff_extZero_eq_zero_of_phi`**: if moreover $\Phi f = 0$ on $\mathbb H_r^d$, then $c(\mathrm{extZero}\,T') = 0$ for every $T'$ (with
  `fourier_coeff_unique`);
* `actU`, `actU_mem`, `eT_compMat`: $(U\cdot Z)_v = \sigma_v(U)Z_v\sigma_v(U)^{\mathsf T}$ preserves $\mathbb H_r^d$ for invertible $U$, and
  $e_{T[U]}(Z) = e_T(U\cdot Z)$;
* **`coeff_compMat_eq`**: if $f(U\cdot Z) = f(Z)$ then $c(T[U]) = c(T)$ (with `eq_of_hasSum_eT`).
* `thetaR_actU`, `thetaGenR_actU`: $\theta_M$ and $\theta_{\mathrm{gen}(L)}$ are invariant under $U \in \mathrm{GL}_r(\mathcal O_F)$ ($U$, $U^{-1}$
  integral, `IsIntegralMat`); **`repMassT_compMat`** ($\mathrm{repMassT}(L, T[U]) = \mathrm{repMassT}(L, T)$), derived from these and
  `coeff_compMat_eq`, a check of the framework on the theta side.

In the Siegel–Weil comparison these are applied to $f = E^{(r+1)}(\cdot, s_0) - \theta^{(r+1)}_{\mathrm{gen}}$: if $\Phi f = 0$ (induction on the degree)
then the coefficients of $f$ vanish at every $T$ whose first row is zero; with the invariance of $f$ under $Z \mapsto U^{\mathsf T}ZU$,
$U \in \mathrm{GL}_{r+1}(\mathcal O_F)$, this reaches every singular $T$ whose radical contains a unimodular vector.

Source: Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939) (the operator $\Phi$) [unverified];
Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.ThetaPhi
import QuadFormsKB.SiegelWeil.Forms.FourierUnique
import QuadFormsKB.LocalDensity.FormDensitySelf

open Matrix NumberField Complex Filter Topology
open QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- **The form in the variables $1, \dots, r$** of a form $T$ in $r + 1$ variables (coefficients $T_{i+1,j+1}$). -/
def tailForm (T : QuadForm F (r + 1)) : QuadForm F r where
  coeff := Matrix.of fun i j => T.coeff i.succ j.succ
  upper := fun _ _ h => T.upper (Fin.succ_lt_succ_iff.mpr h)

/-- **The form $T'$ in the variables $1, \dots, r$** of $r + 1$ variables (the variable $0$ absent). -/
def extZero (T' : QuadForm F r) : QuadForm F (r + 1) where
  coeff := Matrix.of fun i j => Fin.cases 0 (fun i' => Fin.cases 0 (fun j' => T'.coeff i' j') j) i
  upper := by
    intro i j h
    induction i using Fin.cases with
    | zero => rfl
    | succ i' =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j' => exact T'.upper (Fin.succ_lt_succ_iff.mp h)

@[simp] lemma tailForm_extZero (T' : QuadForm F r) : tailForm (extZero T') = T' := by
  ext i j; rfl

lemma extZero_injective : Function.Injective (extZero : QuadForm F r → QuadForm F (r + 1)) := fun T T' h => by
  rw [← tailForm_extZero T, h, tailForm_extZero]

lemma gramT_tailForm (T : QuadForm F (r + 1)) (i j : Fin r) : gramT (tailForm T) i j = gramT T i.succ j.succ := by
  simp [gramT, QuadForm.hessian, tailForm]

/-- **Totally positive semidefinite:** $\sigma_v(T_G)$ is positive semidefinite at every real place $v$. -/
def IsTotPSD {n : ℕ} (T : QuadForm F n) : Prop := ∀ v : InfinitePlace F, ((gramT T).map (realEmb F v)).PosSemidef

/-- $e_T(Z \oplus it) = e_{\mathrm{tail}\,T}(Z)\exp\big(-2\pi t\sum_v\sigma_v(T_{00})\big)$. -/
lemma eT_blockZ_form (T : QuadForm F (r + 1)) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) :
    eT T (blockZ Z t) =
      eT (tailForm T) Z * ((Real.exp (-(2 * Real.pi * t) * ∑ v, realEmb F v (gramT T 0 0)) : ℝ) : ℂ) := by
  have htr : trPair T (blockZ Z t) =
      trPair (tailForm T) Z + I * t * ∑ v, (realEmb F v (gramT T 0 0) : ℂ) := by
    simp only [trPair, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_zero_succ, blockZ_succ_zero, blockZ_succ_succ,
      mul_zero, Finset.sum_const_zero, add_zero, gramT_tailForm, Finset.sum_add_distrib, Finset.mul_sum]
    rw [zero_add, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [eT, eT, htr, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A real positive semidefinite matrix with $A_{00} = 0$ has $A_{0j} = 0$ for every $j$. -/
lemma posSemidef_row_zero {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : A.PosSemidef) (h0 : A 0 0 = 0)
    (j : Fin (m + 1)) : A 0 j = 0 := by
  by_contra hj
  have hsym : A j 0 = A 0 j := by
    have := congrFun (congrFun hA.isHermitian.eq 0) j
    simpa using this
  have hq := (posSemidef_iff_dotProduct_mulVec.mp hA).2
  set a : ℝ := -(A j j + 1) / (2 * A 0 j) with ha
  have hx := hq (Pi.single 0 a + Pi.single j 1)
  have hj0 : j ≠ 0 := by rintro rfl; exact hj h0
  have e : star (Pi.single 0 a + Pi.single j 1 : Fin (m + 1) → ℝ) ⬝ᵥ (A *ᵥ (Pi.single 0 a + Pi.single j 1)) =
      2 * a * A 0 j + A j j := by
    simp only [star_trivial, mulVec_add, mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct]
    simp [Matrix.col_apply, h0, hsym]
    ring
  rw [e] at hx
  have : 2 * a * A 0 j = -(A j j + 1) := by rw [ha]; field_simp
  linarith

/-- A totally positive semidefinite $T$ with $T_{00} = 0$ is `extZero (tailForm T)`. -/
lemma eq_extZero_of_psd {T : QuadForm F (r + 1)} (hT : IsTotPSD T) (h0 : gramT T 0 0 = 0) :
    T = extZero (tailForm T) := by
  obtain ⟨v0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hA := hT v0
  have hrow : ∀ j, gramT T 0 j = 0 := by
    intro j
    have := posSemidef_row_zero hA (by simp [h0]) j
    simpa using this
  have hc00 : T.coeff 0 0 = 0 := by
    have := hrow 0
    simp only [gramT, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul] at this
    linear_combination this
  have hc0 : ∀ j' : Fin r, T.coeff 0 j'.succ = 0 := by
    intro j'
    have h1 := hrow j'.succ
    have h2 : T.coeff j'.succ 0 = 0 := T.upper (Fin.succ_pos j')
    simp only [gramT, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul, h2, add_zero] at h1
    linear_combination 2 * h1
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact hc00
    | succ j' => exact hc0 j'
  | succ i' =>
    induction j using Fin.cases with
    | zero => exact T.upper (Fin.succ_pos i')
    | succ j' => rfl

/-- **Siegel's $\Phi$ operator on an expansion:** $f(Z \oplus it) \to \sum_{T'}c(\mathrm{extZero}\,T')e_{T'}(Z)$ as $t \to \infty$. -/
@[kb "siegel1939" "the operator Phi on Fourier expansions [unverified]"]
theorem tendsto_phi {c : QuadForm F (r + 1) → ℂ}
    (hc : ∀ Z ∈ siegelHF F (r + 1), Summable fun T => ‖c T * eT T Z‖)
    (hpsd : ∀ T, c T ≠ 0 → IsTotPSD T)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Tendsto (fun t : ℝ => ∑' T, c T * eT T (blockZ Z t)) atTop
      (𝓝 (∑' T' : QuadForm F r, c (extZero T') * eT T' Z)) := by
  classical
  set S : QuadForm F (r + 1) → ℝ := fun T => ∑ v, realEmb F v (gramT T 0 0) with hSdef
  have hdiag : ∀ T, c T ≠ 0 → ∀ v, 0 ≤ realEmb F v (gramT T 0 0) := by
    intro T hT v
    have := (hpsd T hT v).diag_nonneg (i := 0)
    simpa using this
  have hS0 : ∀ T, c T ≠ 0 → 0 ≤ S T := fun T hT => Finset.sum_nonneg fun v _ => hdiag T hT v
  have hSpos : ∀ T, c T ≠ 0 → gramT T 0 0 ≠ 0 → 0 < S T := by
    intro T hT h0
    obtain ⟨v0⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine Finset.sum_pos (fun v _ => lt_of_le_of_ne (hdiag T hT v) ?_) ⟨v0, Finset.mem_univ _⟩
    exact fun h => h0 ((map_eq_zero _).mp h.symm)
  set g : QuadForm F (r + 1) → ℂ := fun T => if gramT T 0 0 = 0 then c T * eT (tailForm T) Z else 0 with hg
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (T : QuadForm F (r + 1)) => c T * eT T (blockZ Z t)) (g := g)
    (bound := fun T => ‖c T * eT T (blockZ Z 1)‖) (hc _ (blockZ_mem hZ one_pos))
    (fun T => by
      by_cases hcT : c T = 0
      · simp only [hg, hcT, zero_mul, ite_self]; exact tendsto_const_nhds
      simp only [eT_blockZ_form]
      by_cases h0 : gramT T 0 0 = 0
      · simp only [hg, h0, ite_true, map_zero, Finset.sum_const_zero, mul_zero, Real.exp_zero,
          Complex.ofReal_one, mul_one]
        exact tendsto_const_nhds
      · simp only [hg, h0, ite_false]
        have hSp := hSpos T hcT h0
        have h1 : Tendsto (fun t : ℝ => -(2 * Real.pi * t) * S T) atTop atBot := by
          have h2 : Tendsto (fun t : ℝ => (2 * Real.pi * S T) * t) atTop atTop :=
            tendsto_id.const_mul_atTop (by positivity)
          refine (tendsto_neg_atTop_atBot.comp h2).congr fun t => ?_
          simp only [Function.comp_apply]; ring
        have h3 := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h1)
        have h4 := h3.const_mul (c T * eT (tailForm T) Z)
        simp only [Complex.ofReal_zero, mul_zero] at h4
        refine h4.congr fun t => ?_
        simp only [Function.comp_apply, hSdef]
        ring)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht T
      by_cases hcT : c T = 0
      · simp [hcT]
      rw [eT_blockZ_form, eT_blockZ_form, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]
      gcongr
      have := hS0 T hcT
      simp only [hSdef] at this
      nlinarith [Real.pi_pos])
  have hsupp : Function.support g ⊆ Set.range extZero := by
    intro T hT
    have h0 : gramT T 0 0 = 0 := by by_contra h; exact hT (by simp [hg, h])
    have hcT : c T ≠ 0 := by intro h; exact hT (by simp [hg, h])
    exact ⟨tailForm T, (eq_extZero_of_psd (hpsd T hcT) h0).symm⟩
  have hgext : ∀ T', g (extZero T') = c (extZero T') * eT T' Z := by
    intro T'
    have h0 : gramT (extZero T') 0 0 = 0 := by simp [gramT, QuadForm.hessian, extZero]
    simp only [hg, h0, ite_true, tailForm_extZero]
  have hlim : ∑' T, g T = ∑' T' : QuadForm F r, c (extZero T') * eT T' Z := by
    rw [← extZero_injective.tsum_eq hsupp]
    simp only [hgext]
  rw [← hlim]
  exact hT

/-- **Vanishing of $\Phi f$ kills the coefficients with zero first row.** -/
theorem coeff_extZero_eq_zero_of_phi {c : QuadForm F (r + 1) → ℂ}
    (hc : ∀ Z ∈ siegelHF F (r + 1), Summable fun T => ‖c T * eT T Z‖)
    (hpsd : ∀ T, c T ≠ 0 → IsTotPSD T)
    (hphi : ∀ Z ∈ siegelHF F r, Tendsto (fun t : ℝ => ∑' T, c T * eT T (blockZ Z t)) atTop (𝓝 0))
    (T' : QuadForm F r) : c (extZero T') = 0 := by
  have hext : ∀ (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (T' : QuadForm F r),
      eT (extZero T') (blockZ Z 1) = eT T' Z := by
    intro Z T'
    have h0 : gramT (extZero T') 0 0 = 0 := by simp [gramT, QuadForm.hessian, extZero]
    rw [eT_blockZ_form, h0, tailForm_extZero]
    simp
  have hs : ∀ Z ∈ siegelHF F r, Summable fun T' : QuadForm F r => ‖c (extZero T') * eT T' Z‖ := by
    intro Z hZ
    have := (hc _ (blockZ_mem hZ one_pos)).comp_injective extZero_injective
    refine this.congr fun T' => ?_
    simp only [Function.comp_apply, hext]
  have hzero : (fun T' : QuadForm F r => c (extZero T')) = fun _ => 0 := by
    refine fourier_coeff_unique hs (fun Z _ => by simp) fun Z hZ => ?_
    have h1 := tendsto_phi hc hpsd hZ
    have h2 := hphi Z hZ
    rw [tendsto_nhds_unique h1 h2]
    simp
  exact congrFun hzero T'

/-! ### Invariance of the coefficients under $T \mapsto T[U]$ -/

/-- The complex image $\sigma_v(U)$ of a matrix over $F$ at the real place $v$. -/
abbrev embC (v : InfinitePlace F) (U : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) ℂ :=
  U.map fun x => (realEmb F v x : ℂ)

/-- **The action of $U$ on $\mathbb H_r^d$:** $(U\cdot Z)_v = \sigma_v(U)\,Z_v\,\sigma_v(U)^{\mathsf T}$. -/
def actU (U : Matrix (Fin r) (Fin r) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
  fun v => embC v U * Z v * (embC v U)ᵀ

lemma trPair_eq_trace (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    trPair T Z = ∑ v, (((gramT T).map fun x => (realEmb F v x : ℂ)) * Z v).trace := by
  simp only [trPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply]

/-- $e_{T[U]}(Z) = e_T(U\cdot Z)$. -/
lemma eT_compMat (T : QuadForm F r) (U : Matrix (Fin r) (Fin r) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    eT (T.compMat U) Z = eT T (actU U Z) := by
  rw [eT, eT, trPair_eq_trace, trPair_eq_trace, gramT_compMat]
  congr 2
  refine Finset.sum_congr rfl fun v _ => ?_
  set φ : F →+* ℂ := Complex.ofRealHom.comp (realEmb F v)
  have hm : ∀ A : Matrix (Fin r) (Fin r) F, A.map (fun x => (realEmb F v x : ℂ)) = φ.mapMatrix A := fun A => rfl
  simp only [actU, embC, hm, map_mul]
  rw [show φ.mapMatrix Uᵀ = (φ.mapMatrix U)ᵀ from rfl]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (φ.mapMatrix U)ᵀ]
  simp only [Matrix.mul_assoc]

/-- $U\cdot Z \in \mathbb H_r^d$ for $Z \in \mathbb H_r^d$ and $U$ invertible. -/
lemma actU_mem {U : Matrix (Fin r) (Fin r) F} (hU : U.det ≠ 0) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) : actU U Z ∈ siegelHF F r := by
  intro v
  obtain ⟨hsym, hY⟩ := hZ v
  set A : Matrix (Fin r) (Fin r) ℝ := U.map (realEmb F v)
  have hA : embC v U = A.map (fun x => (x : ℂ)) := rfl
  refine ⟨?_, ?_⟩
  · simp only [actU, Matrix.transpose_mul, Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
  · have him : (actU U Z v).map Complex.im = A * (Z v).map Complex.im * Aᵀ := by
      ext i j
      simp only [actU, hA, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Complex.im_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul, Complex.im_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [Complex.mul_im]
    rw [him]
    have hdet : A.det ≠ 0 := by
      rw [show A.det = realEmb F v U.det from (RingHom.map_det _ _).symm]
      exact (map_ne_zero _).mpr hU
    have hinj : Function.Injective A.vecMul :=
      Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
    have := hY.mul_mul_conjTranspose_same hinj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Invariance of the coefficients:** if $f(U\cdot Z) = f(Z)$ on $\mathbb H_r^d$ for an invertible $U$ over $F$ (in practice
$U \in \mathrm{GL}_r(\mathcal O_F)$) and $f = \sum_Tc(T)e_T$ absolutely, then $c(T[U]) = c(T)$ for every $T$. -/
@[kb "freitag1983" "Ch. I (the Fourier coefficients of a Siegel modular form are invariant under GL_r) [unverified]"]
theorem coeff_compMat_eq {c : QuadForm F r → ℂ} {f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (hc : ∀ Z ∈ siegelHF F r, Summable fun T => ‖c T * eT T Z‖)
    (hf : ∀ Z ∈ siegelHF F r, HasSum (fun T => c T * eT T Z) (f Z))
    {U : Matrix (Fin r) (Fin r) F} (hU : U.det ≠ 0) (hinv : ∀ Z ∈ siegelHF F r, f (actU U Z) = f Z)
    (T : QuadForm F r) : c (T.compMat U) = c T := by
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have hUU' : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  let e : QuadForm F r ≃ QuadForm F r :=
    { toFun := fun S => S.compMat U⁻¹
      invFun := fun S => S.compMat U
      left_inv := fun S => by
        simp only [QuadForm.compMat_mul, hUU', QuadForm.compMat_one]
      right_inv := fun S => by
        simp only [QuadForm.compMat_mul, hUU, QuadForm.compMat_one] }
  have hb : ∀ Z ∈ siegelHF F r, HasSum (fun S => c (e S) * eT S Z) (f Z) := by
    intro Z hZ
    have h := hf _ (actU_mem hU hZ)
    rw [hinv Z hZ] at h
    rw [← e.hasSum_iff] at h
    refine h.congr_fun fun S => ?_
    simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
    rw [← eT_compMat, QuadForm.compMat_mul, hUU', QuadForm.compMat_one]
  have hbs : ∀ Z ∈ siegelHF F r, Summable fun S => ‖c (e S) * eT S Z‖ := by
    intro Z hZ
    have h := hc _ (actU_mem hU hZ)
    rw [← e.summable_iff] at h
    refine h.congr fun S => ?_
    simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
    rw [← eT_compMat, QuadForm.compMat_mul, hUU', QuadForm.compMat_one]
  have heq := eq_of_hasSum_eT hbs hc hb hf
  have := congrFun heq (T.compMat U)
  simp only [e, Equiv.coe_fn_mk, QuadForm.compMat_mul, hUU, QuadForm.compMat_one] at this
  exact this.symm

/-! ### Invariance of the theta series under $\mathrm{GL}_r(\mathcal O_F)$ -/

section ThetaInv

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

variable {n : ℕ}

/-- An integral matrix: every entry lies in $\mathcal O_F$. -/
def IsIntegralMat (U : Matrix (Fin r) (Fin r) F) : Prop := ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = U i j

/-- Right multiplication by an integral $U$ maps $M^r$ to $M^r$. -/
lemma frames_mul_mem {M : Submodule (𝓞 F) (Fin n → F)} {U : Matrix (Fin r) (Fin r) F} (hU : IsIntegralMat U)
    (X : frames M r) (j : Fin r) : (fun i => (X.1 * U) i j) ∈ M := by
  have e : (fun i => (X.1 * U) i j) = ∑ k, (hU k j).choose • (fun i => X.1 i k) := by
    funext i
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, (hU k j).choose_spec, mul_comm]
  rw [e]
  exact M.sum_mem fun k _ => M.smul_mem _ (X.2 k)

/-- **$\theta_M(U\cdot Z) = \theta_M(Z)$** for $U \in \mathrm{GL}_r(\mathcal O_F)$ ($U$ and $U^{-1}$ integral): $X \mapsto XU$ permutes $M^r$. -/
theorem thetaR_actU (Q : QuadForm F n) (M : Submodule (𝓞 F) (Fin n → F)) {U : Matrix (Fin r) (Fin r) F}
    (hU : IsIntegralMat U) (hU' : IsIntegralMat U⁻¹) (hdet : U.det ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    thetaR Q M (actU U Z) = thetaR Q M Z := by
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  let e : frames M r ≃ frames M r :=
    { toFun := fun X => ⟨X.1 * U, frames_mul_mem hU X⟩
      invFun := fun X => ⟨X.1 * U⁻¹, frames_mul_mem hU' X⟩
      left_inv := fun X => Subtype.ext (by simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv U hu])
      right_inv := fun X => Subtype.ext (by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul U hu]) }
  unfold thetaR
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk, ← eT_compMat, QuadForm.compMat_mul]

/-- **$\theta_{\mathrm{gen}(L)}(U\cdot Z) = \theta_{\mathrm{gen}(L)}(Z)$** for $U \in \mathrm{GL}_r(\mathcal O_F)$. -/
theorem thetaGenR_actU (Q : QuadForm F n) (L : Lat F n) {U : Matrix (Fin r) (Fin r) F}
    (hU : IsIntegralMat U) (hU' : IsIntegralMat U⁻¹) (hdet : U.det ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    thetaGenR Q L (actU U Z) = thetaGenR Q L Z := by
  simp only [thetaGenR, thetaR_actU Q _ hU hU' hdet]

/-- **Check of the framework:** Siegel's averaged representation numbers satisfy $\mathrm{repMassT}(L, T[U]) = \mathrm{repMassT}(L, T)$ for
$U \in \mathrm{GL}_r(\mathcal O_F)$, derived from the invariance of $\theta_{\mathrm{gen}(L)}$ and the uniqueness of Fourier coefficients
(`coeff_compMat_eq`). -/
theorem repMassT_compMat {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {U : Matrix (Fin r) (Fin r) F} (hU : IsIntegralMat U) (hU' : IsIntegralMat U⁻¹) (hdet : U.det ≠ 0) (T : QuadForm F r) :
    repMassT Q L (T.compMat U) = repMassT Q L T := by
  have h := coeff_compMat_eq (c := fun T => ((repMassT Q L T / mass Q L : ℝ) : ℂ)) (f := thetaGenR Q L)
    (fun Z hZ => summable_norm_thetaGenR_coeff hQ L hLi hZ) (fun Z hZ => hasSum_thetaGenR hQ L hLi hZ) hdet
    (fun Z _ => thetaGenR_actU Q L hU hU' hdet Z) T
  have hm : (mass Q L : ℝ) ≠ 0 := (mass_pos hQ L hLi).ne'
  have h' : repMassT Q L (T.compMat U) / mass Q L = repMassT Q L T / mass Q L := by exact_mod_cast h
  field_simp at h'
  exact h'

end ThetaInv

end QuadFormsKB.SiegelWeil.Forms
