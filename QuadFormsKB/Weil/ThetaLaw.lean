/-
# The theta transformation law by local computations

**Layer:** global assembly of local results, over a totally real field $F$. The inputs are:
* the $\mathrm{SL}_2(F)$-invariance of the theta distribution (`thetaDist_omegaG`: Poisson summation, Hilbert
  reciprocity and Weil's product formula, all proved);
* **local** equivariance at every finite place (`weilRepV_K0`, `Weil/LocalK0.lean`, dyadic places included);
* **local** equivariance at the infinite places (`omegaG_inf_gOrb`, `Weil/ArchTheta.lean`);
* the bridge to the classical theta series (`thetaKernel_gz_eq_thetaQ`).
No Gauss sum is evaluated and no reciprocity law for Jacobi symbols is used ("Route 2"; compare the Hecke route,
`HilbertModular/ThetaCharF.lean`).

**Setting.** $Q = \langle b_0, \dots, b_{2m-1}\rangle$ with $b_i \in \mathcal O_F$ totally positive (`QuadForm.diag b`),
$m \ge 1$, $\mathfrak N$ a theta level of $Q$ (`IsThetaLevelF`). Locally $\mathfrak N \subseteq \bigcap_i4b_i\mathfrak d_v$ at every $v$
(`levelV_of_isThetaLevelF`), so $\gamma \in \Gamma_0(\mathfrak N)$ lies in $K_0(\mathfrak N_v)$ for the local level of `LocalK0`.

**Main results.**
* **`thetaQ_slash_route2`** (the Route 2 theorem): for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$,
  $$\theta_Q\,|_m\,\gamma = \Big(\prod_{v<\infty}\chi_v(d)\Big)\,\theta_Q,\qquad
    \chi_v(d) = (d, (-1)^m\det Q)_v\ (d \in \mathcal O_v^\times),\quad \chi_v(d) = 1\ (\text{otherwise})\quad(\texttt{chiLoc}),$$
  $\det Q = \prod_ib_i$. *Proof:* with $\Psi_\tau = G_\tau\otimes\bigotimes_v\mathbf 1_{\mathcal O_v^{2m}}$ we have
  $\Theta(\Psi_z) = \theta_Q(z)$ (the bridge); $\Theta(\omega(\gamma)\Psi_z) = \Theta(\Psi_z)$; and
  $\omega(\gamma)\Psi_z = \prod_w(c_wz_w + d_w)^{-m}\prod_v\chi_v(d)\cdot\Psi_{\gamma z}$ by the local results.
* **`thetaCharF_eq_finprod_chiLoc`** (identification with the local characters): for $d \in \mathcal O_F$ prime to $\mathfrak N$,
  $\chi_Q(d \bmod \mathfrak N) = \prod_v\chi_v(d)$, where $\chi_Q$ = `thetaCharF` is the character (both laws hold and
  $\theta_Q \ne 0$).
* **`thetaCharF_eq_hilbert`** (the Hilbert-symbol formula): $\chi_Q(d \bmod \mathfrak N) = \prod_{v \mid \mathfrak N}(d, (-1)^m\det Q)_v$;
  every dyadic $v$ divides $\mathfrak N$ (`dvd_of_not_good`), and at $v \nmid \mathfrak N$ the factor is $1$. Equivalently
  $(-1)^m\det Q$ may be replaced by the $D = (-1)^m\det H = 4^m(-1)^m\det Q$ (same square class).

Sources: Weil, Acta Math. 111 (1964), §§14, 29–30 [unverified]; Kudla, *Notes on the local theta correspondence*
(1996), §I.4 [unverified]; Bump, *Automorphic Forms and Representations* (1997), §4.8 [unverified]; Rallis (1984)
[unverified]; Shimura, Ann. of Math. 97 (1973), §2 (the character of $\theta_Q$) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.LocalK0
import QuadFormsKB.Weil.ArchTheta
import QuadFormsKB.HilbertModular.ThetaCharF

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open QuadFormsKB.Analysis WithZero
open scoped MatrixGroups Real Classical ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### The global level is local -/

/-- At each $v$ there is $\delta \in \mathfrak d^{-1}$ with $v(\delta) = \exp(d_v)$ exactly. -/
lemma exists_mem_dual_one_valued_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ δ ∈ FractionalIdeal.dual ℤ ℚ (1 : FI),
      Valued.v (algebraMap F (v.adicCompletion F) δ) = exp (diffExp v : ℤ) := by
  set k : HeightOneSpectrum (𝓞 F) → ℤ := fun w => -(diffExp w : ℤ) + if w = v then 1 else 0 with hk
  have hkfin : (Function.support k).Finite := by
    refine ((finite_support_neg_diffExp (F := F)).union (Set.finite_singleton v)).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not, Set.mem_singleton_iff] at h
    exact hw (by simp [hk, h.1, h.2])
  by_contra hne
  push_neg at hne
  -- every `δ ∈ 𝔡⁻¹` lies in `𝔭_v 𝔡⁻¹ = idealOfExps k`
  have hsub : FractionalIdeal.dual ℤ ℚ (1 : FI) = idealOfExps k := by
    refine le_antisymm (fun δ hδ => ?_) (fun δ hδ => ?_)
    · rw [mem_idealOfExps_iff hkfin]
      intro w
      have h1 := (mem_dual_one_iff δ).mp hδ w
      by_cases hw : w = v
      · subst hw
        have h2 := hne δ hδ
        have hlt : Valued.v (algebraMap F (w.adicCompletion F) δ) < exp (diffExp w : ℤ) := lt_of_le_of_ne h1 h2
        simp only [hk, if_true, neg_add, neg_neg]
        by_cases h0 : Valued.v (algebraMap F (w.adicCompletion F) δ) = 0
        · rw [h0]; exact zero_le
        · rw [← exp_log h0] at hlt ⊢
          rw [exp_lt_exp] at hlt
          rw [exp_le_exp]; omega
      · simpa [hk, hw] using h1
    · rw [mem_dual_one_iff]
      intro w
      have h1 := (mem_idealOfExps_iff hkfin δ).mp hδ w
      refine h1.trans ?_
      rw [exp_le_exp]
      simp only [hk]; split_ifs <;> omega
  have hc := count_idealOfExps hkfin v
  rw [← hsub, count_dual_one] at hc
  simp [hk] at hc

variable [IsTotallyReal F] {m : ℕ}

/-- The Gram matrix of a diagonal form: $\frac12H = \operatorname{diag}(b_i)$. -/
lemma gramF_diag (b : Fin (2 * m) → 𝓞 F) :
    HilbertModular.gramF (QuadForm.diag b) = Matrix.diagonal fun i => (b i : F) := by
  ext i j
  simp only [HilbertModular.gramF, QuadForm.hessian, QuadForm.diag, Matrix.smul_apply, Matrix.map_apply,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h, Ne.symm h]

/-- $Q^\#(\delta e_i) = \delta^2/(4b_i)$ for the diagonal form. -/
lemma qDual_diag_single (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (i : Fin (2 * m)) (δ : F) :
    HilbertModular.qDual (QuadForm.diag b) (Pi.single i δ) = δ ^ 2 / (4 * (b i : F)) := by
  have hbi : (b i : F) ≠ 0 := by exact_mod_cast hb i
  have hinv : (Matrix.diagonal fun j => (b j : F))⁻¹ = Matrix.diagonal fun j => (b j : F)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j
    exact inv_mul_cancel₀ (by exact_mod_cast hb j)
  rw [HilbertModular.qDual, gramF_diag, hinv]
  simp only [HilbertModular.qv]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
  field_simp

/-- **The global theta level is contained in the local levels:** if $\mathfrak N$ is a level of
$Q = \langle b_0, \dots, b_{2m-1}\rangle$ (`IsThetaLevelF`), then every $\nu \in \mathfrak N$ lies in $4b_i\mathfrak d_v$ at every finite
place $v$ and for every $i$ (`LevelV`). *Proof:* $\nu Q^\#(\delta e_i) = \nu\delta^2/(4b_i) \in \mathfrak d^{-1}$ for a
$\delta \in \mathfrak d^{-1}$ with $v(\delta) = \exp(d_v)$ (`exists_mem_dual_one_valued_eq`). -/
@[kb "shimura1973" "§2 (the level of $\\theta_Q$, localized) [unverified]"]
theorem levelV_of_isThetaLevelF (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) {ν : 𝓞 F} (hν : ν ∈ 𝔑)
    (v : HeightOneSpectrum (𝓞 F)) :
    LevelV v (aV (bF b hb) v) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ν)) := by
  intro i
  obtain ⟨δ, hδ, hδv⟩ := exists_mem_dual_one_valued_eq v
  have hy : ∀ j, (Pi.single i δ : Fin (2 * m) → F) j ∈ HilbertModular.invDifferent F := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same]; exact hδ
    · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem _
  have h := hlev ν hν _ hy
  rw [qDual_diag_single b hb i δ] at h
  have hv := (mem_dual_one_iff _).mp h v
  have hbi : (b i : F) ≠ 0 := by exact_mod_cast hb i
  set A := Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ν))
  set B := Valued.v (4 * ((aV (bF b hb) v i : (v.adicCompletion F)ˣ) : v.adicCompletion F))
  have hB : B = Valued.v (algebraMap F (v.adicCompletion F) 4) *
      Valued.v (algebraMap F (v.adicCompletion F) (b i : F)) := by
    simp only [B, aV_val, map_mul, map_ofNat, bF, Units.val_mk0]
  have hB0 : B ≠ 0 := by
    rw [hB]; simp [hbi]
  have hBpos : 0 < B := zero_lt_iff.mpr hB0
  have hv2 : A * exp (diffExp v : ℤ) ^ 2 / B ≤ exp (diffExp v : ℤ) := by
    have e : A * exp (diffExp v : ℤ) ^ 2 / B = Valued.v (algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F ν * (δ ^ 2 / (4 * (b i : F))))) := by
      rw [hB]; simp only [A, map_mul, map_div₀, map_pow, hδv]; rw [mul_div_assoc]
    rw [e]; exact hv
  have hv' : A * exp (diffExp v : ℤ) ^ 2 ≤ exp (diffExp v : ℤ) * B := (div_le_iff₀ hBpos).mp hv2
  have e1 : exp (diffExp v : ℤ) ^ 2 * exp (-(2 * (diffExp v : ℤ))) = 1 := by
    rw [← exp_nsmul, ← exp_add, ← exp_zero]; congr 1; simp
  have e2 : exp (diffExp v : ℤ) * exp (-(2 * (diffExp v : ℤ))) = exp (-(diffExp v : ℤ)) := by
    rw [← exp_add]; congr 1; ring
  calc A = A * (exp (diffExp v : ℤ) ^ 2 * exp (-(2 * (diffExp v : ℤ)))) := by rw [e1, mul_one]
    _ = (A * exp (diffExp v : ℤ) ^ 2) * exp (-(2 * (diffExp v : ℤ))) := (mul_assoc _ _ _).symm
    _ ≤ (exp (diffExp v : ℤ) * B) * exp (-(2 * (diffExp v : ℤ))) := by gcongr
    _ = B * exp (-(diffExp v : ℤ)) := by rw [mul_comm (exp _) B, mul_assoc, e2]

/-! ### Positivity and the standard Gaussian -/

local notation "RP" => {w : InfinitePlace F // IsReal w}

lemma ew_eq_realEmb (w : RP) (x : F) : ew w x = HilbertModular.realEmb F w.1 x := by
  rw [ew_apply, mixedEmbedding_apply_isReal]; rfl

/-- A diagonal form with totally positive coefficients is totally positive definite. -/
lemma isTotPosGram_diag (b : Fin (2 * m) → 𝓞 F) (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) :
    HilbertModular.IsTotPosGram (HilbertModular.gramF (QuadForm.diag b)) := by
  intro v
  rw [gramF_diag, Matrix.diagonal_map (map_zero _)]
  exact Matrix.posDef_diagonal_iff.mpr fun i => hpos i v

lemma bF_val (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (i : Fin (2 * m)) : ((bF b hb i : Fˣ) : F) = b i := rfl

lemma aInf_bF_fst (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (i : Fin (2 * m)) (w : RP) :
    ((aInf (bF b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w = ew w (b i : F) := rfl

/-- **The standard Gaussian is the orbit point $\tau = (i, \dots, i)$**: $\varphi_\infty = e^{-2\pi\sum_wQ_w} = G_i$. -/
lemma gaussQ_eq_gOrb (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) :
    gaussQ b = gOrb (aInf (bF b hb)) (fun _ => Complex.I) := by
  funext x
  simp only [gaussQ, gOrb, ptensor, gs, aInf_bF_fst]
  simp_rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (2 * m))))]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ew_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- $\omega_\infty(g_z)\varphi_\infty = \prod_wy_w^{m/2}\,G_z$, $g_z = n(x)m(y^{1/2})$. -/
lemma borelInf_phiStd_inf (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (z : InfinitePlace F → UpperHalfPlane) :
    (borelInf (bF b hb) (zRe z) (zSqrtIm z) (phiStd b)).inf =
      (∏ w : RP, ((Real.sqrt (z w.1).im : ℝ) : ℂ) ^ m) • gOrb (aInf (bF b hb)) (fun w => (z w.1 : ℂ)) := by
  have hpos' : ∀ i w, 0 < ((aInf (bF b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w := fun i w => by
    rw [aInf_bF_fst, ew_eq_realEmb]; exact hpos i w.1
  show (localDataInf (F := F)).opNf (aInf (bF b hb)) (zRe z)
    ((localDataInf (F := F)).opMf (aInf (bF b hb)) ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) (gaussQ b)) = _
  rw [gaussQ_eq_gOrb b hb, opMf_gOrb, opNf_smul, opNf_gOrb,
    chiV_mul_md_pow hpos' _ (fun w => (Real.sqrt_pos.mpr (z w.1).im_pos).ne')]
  refine congrArg₂ (· • ·) rfl (congrArg _ (funext fun w => ?_))
  simp only [zSqrtIm, zRe, Units.val_mk]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (z w.1).im_pos.le]
  conv_rhs => rw [← Complex.re_add_im (z w.1 : ℂ)]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- $\mathbf 1_{\mathcal O_v}$, the standard Gaussian at each coordinate, and $\varphi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L_v}$ is
fully factorizable. -/
lemma gs_I_mem_schwartzInf (β : RP → ℝ) (hβ : ∀ w, 0 < β w) :
    gs (fun w => (β w : ℂ) * Complex.I) ∈ schwartzInf (F := F) := by
  set t : (mixedSpace F)ˣ :=
    { val := (fun w => Real.sqrt (2 * β w), fun _ => 1)
      inv := (fun w => (Real.sqrt (2 * β w))⁻¹, fun _ => 1)
      val_inv := by
        ext w
        · exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (by linarith [hβ w])).ne'
        · exact isEmptyElim w
      inv_val := by
        ext w
        · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by linarith [hβ w])).ne'
        · exact isEmptyElim w }
  have h : gs (fun w => (β w : ℂ) * Complex.I) = dil (t : mixedSpace F) (gaussInfFun (F := F)) := by
    funext u
    simp only [gs, dil, gaussInfFun, gaussR, prod_complex_eq_one, mul_one, Prod.fst_mul, Pi.mul_apply, t]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 1
    have hs : ((Real.sqrt (2 * β w) : ℝ) : ℂ) ^ 2 = 2 * β w := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith [hβ w])]; push_cast; ring
    push_cast
    rw [mul_pow, hs]
    linear_combination (2 * (π : ℂ) * (β w : ℂ) * ((u.1 w : ℝ) : ℂ) ^ 2) * Complex.I_sq
  rw [h]
  exact dil_mem_schwartzInf t ⟨gaussInf, funext gaussInf_apply⟩

lemma phiStd_isPure (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) : (phiStd b).IsPure := by
  refine ⟨1, fun i => gs (fun w => (((aInf (bF b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w : ℂ) *
      Complex.I), fun _ => 1, fun v _ => ballIndV v 0 0, ∅, fun i => ?_, fun v i => ballIndV_zero_mem_SBK v,
    fun v _ => ⟨rfl, fun _ => rfl⟩, ?_⟩
  · exact gs_I_mem_schwartzInf _ fun w => by rw [aInf_bF_fst, ew_eq_realEmb]; exact hpos i w.1
  · show GDatum.mk _ _ = GDatum.mk _ _
    congr 1
    · rw [one_smul, gaussQ_eq_gOrb b hb]; rfl
    · funext v; rw [one_smul]; rfl

/-! ### Data and the theta distribution -/

lemma GDatum.ext' {n : ℕ} {Φ Ψ : GDatum F n} (h1 : Φ.inf = Ψ.inf) (h2 : ∀ v, Φ.fin v = Ψ.fin v) : Φ = Ψ := by
  cases Φ; cases Ψ; simp only at h1 h2; rw [h1, funext h2]

/-- $\Theta(c_\infty f\otimes\bigotimes_vc_vg_v) = c_\infty\prod_vc_v\cdot\Theta(f\otimes\bigotimes_vg_v)$. -/
lemma thetaDist_smul {n : ℕ} (c₀ : ℂ) (f : (Fin n → mixedSpace F) → ℂ) (c : HeightOneSpectrum (𝓞 F) → ℂ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → v.adicCompletion F) → ℂ)
    (hc : Function.HasFiniteMulSupport c) (hg : (GDatum.mk f g : GDatum F n).Adm) :
    thetaDist (GDatum.mk (c₀ • f) fun v => c v • g v) = (c₀ * ∏ᶠ v, c v) * thetaDist (GDatum.mk f g) := by
  rw [thetaDist, thetaDist, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  simp only [GDatum.eval, Pi.smul_apply, smul_eq_mul]
  rw [finprod_mul_distrib hc (hg.finite_mulSupport ξ)]
  ring

lemma adm_oneV {n : ℕ} (f : (Fin n → mixedSpace F) → ℂ) : (GDatum.mk f fun v => oneV v n : GDatum F n).Adm :=
  ⟨∅, fun _ _ => rfl⟩

/-- The datum $\Psi_\tau = G_\tau\otimes\bigotimes_v\mathbf 1_{\mathcal O_v^{2m}}$. -/
def psiD (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (τ : RP → ℂ) : GDatum F (2 * m) :=
  ⟨gOrb (aInf (bF b hb)) τ, fun v => oneV v (2 * m)⟩

lemma prod_sqrt_ne_zero (z : InfinitePlace F → UpperHalfPlane) :
    (∏ w : RP, ((Real.sqrt (z w.1).im : ℝ) : ℂ) ^ m) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (by exact_mod_cast (Real.sqrt_pos.mpr (z w.1).im_pos).ne')

lemma psiD_isPure (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (z : InfinitePlace F → UpperHalfPlane) :
    (psiD b hb fun w => (z w.1 : ℂ)).IsPure := by
  obtain ⟨c₀, f₀, c, f, T, h1, h2, h3, heq⟩ :=
    (phiStd_isPure b hb hpos).borelInf (bF b hb) (zRe z) (zSqrtIm z)
  set C := ∏ w : RP, ((Real.sqrt (z w.1).im : ℝ) : ℂ) ^ m
  refine ⟨C⁻¹ * c₀, f₀, c, f, T, h1, h2, h3, GDatum.ext' ?_ fun v => ?_⟩
  · have hi := congrArg GDatum.inf heq
    rw [borelInf_phiStd_inf b hb hpos] at hi
    show gOrb _ _ = (C⁻¹ * c₀) • ptensor f₀
    rw [mul_smul, ← show (pureD c₀ f₀ c f).inf = c₀ • ptensor f₀ from rfl, ← hi, smul_smul,
      inv_mul_cancel₀ (prod_sqrt_ne_zero z), one_smul]
  · have hf := congrFun (congrArg GDatum.fin heq) v
    exact hf

/-- **$\Theta(\Psi_z) = \theta_Q(z)$** (from the bridge `thetaKernel_gz_eq_thetaQ`). -/
lemma thetaDist_psiD (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (z : InfinitePlace F → UpperHalfPlane) :
    thetaDist (psiD b hb fun w => (z w.1 : ℂ)) = HilbertModular.thetaQ (QuadForm.diag b) z := by
  have hbr := thetaKernel_gz_eq_thetaQ b hb z
  have he : borelInf (bF b hb) (zRe z) (zSqrtIm z) (phiStd b) =
      GDatum.mk ((∏ w : RP, ((Real.sqrt (z w.1).im : ℝ) : ℂ) ^ m) • gOrb (aInf (bF b hb)) (fun w => (z w.1 : ℂ)))
        fun v => (1 : ℂ) • oneV v (2 * m) :=
    GDatum.ext' (borelInf_phiStd_inf b hb hpos z) fun v => (one_smul _ _).symm
  rw [he, thetaDist_smul _ _ (fun _ => 1) _ (by simp [Function.HasFiniteMulSupport]) (adm_oneV _),
    finprod_one, mul_one] at hbr
  have hC : (∏ w : RP, ((Real.sqrt (z w.1).im : ℝ) : ℂ) ^ m) =
      ((∏ v : InfinitePlace F, (z v).im ^ ((2 * m : ℝ) / 4) : ℝ) : ℂ) := by
    push_cast
    refine (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => ?_)
    simp only [Equiv.subtypeUnivEquiv_apply]
    rw [← Complex.ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (z w.1).im_pos.le]
    congr 1; ring
  rw [hC] at hbr
  have hC0 : ((∏ v : InfinitePlace F, (z v).im ^ ((2 * m : ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by
    rw [← hC]; exact prod_sqrt_ne_zero z
  exact mul_left_cancel₀ hC0 hbr

/-! ### The global character $\prod_v\chi_v$ -/

/-- **The Route 2 character** $\prod_{v<\infty}\chi_v(d)$, $\chi_v$ = `chiLoc` for $V = \langle b_0, \dots, b_{2m-1}\rangle$. -/
@[kb "kudla1996" "§I.4 (the character of $\\theta_Q$ as a product of local characters) [unverified]"]
def chiFin (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (d : 𝓞 F) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    chiLoc v (aV (bF b hb) v) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d))

lemma hasFiniteMulSupport_chiLoc (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (d : 𝓞 F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      chiLoc v (aV (bF b hb) v) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) := by
  by_cases hd : algebraMap (𝓞 F) F d = 0
  · refine Set.finite_empty.subset fun v hv => ?_
    simp only [Function.mem_mulSupport, chiLoc, hd, map_zero] at hv
    simp at hv
  refine (HN.finite_hilbert_finite_eq_neg_one (algebraMap (𝓞 F) F d) ((discV (bF b hb) : Fˣ) : F) hd
    (discV (bF b hb)).ne_zero).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, chiLoc] at hv
  split_ifs at hv with h1
  · simp only [LocalData.chiV, LocalData.hC, discV_aV] at hv
    rcases HN.hilbertSymbol_eq_one_or (v.adicCompletion F) (algebraMap F _ (algebraMap (𝓞 F) F d))
      (algebraMap F _ ((discV (bF b hb) : Fˣ) : F)) with h | h
    · exact absurd (by rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl, h]; simp) hv
    · exact h
  · exact absurd rfl hv

lemma chiFin_mul_self (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (d : 𝓞 F) :
    chiFin b hb d * chiFin b hb d = 1 := by
  rw [chiFin, ← finprod_mul_distrib (hasFiniteMulSupport_chiLoc b hb d) (hasFiniteMulSupport_chiLoc b hb d)]
  exact finprod_eq_one_of_forall_eq_one fun v => chiLoc_sq v _ _

/-! ### The Route 2 theorem -/

lemma valued_algebraMap_int_le_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) ≤ 1 := by
  rw [HN.valued_algebraMap]; exact v.valuation_le_one x

/-- **The finite components of $\omega(\gamma)\Psi_\tau$**, $\gamma \in \Gamma_0(\mathfrak N)$: $\chi_v(d)\mathbf 1_{L_v}$ at every $v$
(`weilRepV_K0`, with the local level from `levelV_of_isThetaLevelF`). -/
lemma omegaG_psiD_fin (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ HilbertModular.Gamma0R 𝔑) (τ : RP → ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    (omegaG (bF b hb) (HilbertModular.toF F γ) (psiD b hb τ)).fin v =
      chiLoc v (aV (bF b hb) v) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (γ 1 1))) •
        oneV v (2 * m) := by
  rw [omegaG_fin_eq_weilRepV (bF b hb) (HilbertModular.toF F γ) v (oneV_mem_Sn v)]
  have ha : ∀ i, Valued.v ((aV (bF b hb) v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := fun i => by
    rw [aV_val, bF_val]; exact valued_algebraMap_int_le_one v (b i)
  have hint : ∀ i j, Valued.v (((Matrix.SpecialLinearGroup.map (algebraMap F (v.adicCompletion F))
      (HilbertModular.toF F γ) : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1 :=
    fun i j => valued_algebraMap_int_le_one v (γ i j)
  have hK := weilRepV_K0 v (aV (bF b hb) v) hm ha
    (Matrix.SpecialLinearGroup.map (algebraMap F (v.adicCompletion F)) (HilbertModular.toF F γ)) hint
    (levelV_of_isThetaLevelF b hb hlev hγ v)
  have h1 : (⟨(psiD b hb τ).fin v, oneV_mem_Sn v⟩ : (localDataV v).Sn (2 * m)) = oneS v m := rfl
  rw [h1, hK]
  rfl

/-- **The theta transformation law by local computations (Route 2).** Let $F$ be totally real,
$Q = \langle b_0, \dots, b_{2m-1}\rangle$ with $b_i \in \mathcal O_F$ totally positive (`QuadForm.diag b`), $m \ge 1$, and
$\mathfrak N$ a theta level of $Q$ (`IsThetaLevelF`). For every $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$
($d = \gamma_{11}$, 0-based),
$$\theta_Q\,|_m\,\gamma = \Big(\prod_{v<\infty}\chi_v(d)\Big)\,\theta_Q,\qquad
  \chi_v(d) = \begin{cases}(d, (-1)^m\det Q)_v & d \in \mathcal O_v^\times\\ 1 & \text{otherwise}\end{cases}\quad
  (\texttt{chiFin},\ \texttt{chiLoc}).$$
*Proof* (all inputs proved): $\Theta(\omega(\gamma)\Psi_z) = \Theta(\Psi_z)$ (`thetaDist_omegaG`); at each finite place
$\omega_v(\gamma)\mathbf 1_{L_v} = \chi_v(d)\mathbf 1_{L_v}$ (`weilRepV_K0`, dyadic places included, no Weil-index correction); at
infinity $\omega_\infty(\gamma)G_z = \prod_w(c_wz_w + d_w)^{-m}G_{\gamma z}$ (`omegaG_inf_gOrb`); and $\Theta(\Psi_z) = \theta_Q(z)$
(`thetaDist_psiD`, the bridge). Hence $\theta_Q(z) = \prod_v\chi_v(d)\,(\theta_Q|_m\gamma)(z)$, and $\chi_v(d)^2 = 1$. -/
@[kb "weil1964" "§§14, 29–30; Kudla (1996), §I.4; Bump (1997), §4.8 (theta law from the Weil representation) [unverified]"]
theorem thetaQ_slash_route2 (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ HilbertModular.Gamma0R 𝔑) :
    HilbertModular.thetaQ (QuadForm.diag b) ∣[(m : ℤ)]
        HilbertModular.slHom (HilbertModular.realEmb F) (HilbertModular.toF F γ) =
      chiFin b hb (γ 1 1) • HilbertModular.thetaQ (QuadForm.diag b) := by
  set g : SL(2, F) := HilbertModular.toF F γ with hg
  have hposE : ∀ i w, 0 < ew w ((bF b hb i : Fˣ) : F) := fun i w => by
    rw [bF_val, ew_eq_realEmb]; exact hpos i w.1
  have hentry : ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j = algebraMap (𝓞 F) F (γ i j) := fun i j => rfl
  funext z
  set τ : RP → ℂ := fun w => (z w.1 : ℂ) with hτdef
  have hτ : ∀ w, 0 < (τ w).im := fun w => (z w.1).im_pos
  set gz := HilbertModular.slHom (HilbertModular.realEmb F) g • z with hgz
  have hinf := omegaG_inf_gOrb (bF b hb) hposE g hτ (Φ := psiD b hb τ) rfl
  have hω : omegaG (bF b hb) g (psiD b hb τ) = GDatum.mk _ fun v =>
      chiLoc v (aV (bF b hb) v) (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (γ 1 1))) •
        oneV v (2 * m) := GDatum.ext' hinf (omegaG_psiD_fin b hb hm hlev hγ τ)
  have h1 := thetaDist_omegaG (bF b hb) (psiD_isPure b hb hpos z) g
  rw [hω, thetaDist_smul _ _ _ _ (hasFiniteMulSupport_chiLoc b hb (γ 1 1)) (adm_oneV _),
    thetaDist_psiD b hb hpos z] at h1
  have hτ' : (fun w : RP => ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 0 0) : ℂ) * τ w + ew w (g 0 1)) /
      ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (g 1 1))) =
      fun w => ((gz w.1 : UpperHalfPlane) : ℂ) := by
    funext w
    rw [hgz, hg, HilbertModular.coe_slHom_toF_smul]
    simp only [ew_eq_realEmb, τ]
    rfl
  have h2 : thetaDist (GDatum.mk (gOrb (aInf (bF b hb)) fun w : RP =>
      ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 0 0) : ℂ) * τ w + ew w (g 0 1)) /
        ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (g 1 1)))
      fun v => oneV v (2 * m)) = HilbertModular.thetaQ (QuadForm.diag b) gz := by
    rw [hτ']; exact thetaDist_psiD b hb hpos gz
  rw [h2, show (∏ᶠ v : HeightOneSpectrum (𝓞 F), chiLoc v (aV (bF b hb) v)
    (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (γ 1 1)))) = chiFin b hb (γ 1 1) from rfl] at h1
  -- the automorphy factor
  have hJ : (∏ w : RP, ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (g 1 1)) ^ (-(m : ℤ))) =
      ∏ v : InfinitePlace F, (((HilbertModular.slHom (HilbertModular.realEmb F) g v : GL(2, ℝ)⁺) :
        GL (Fin 2) ℝ).det.val ^ ((m : ℤ) - 1) : ℝ) *
        UpperHalfPlane.denom ((HilbertModular.slHom (HilbertModular.realEmb F) g v : GL(2, ℝ)⁺) :
          GL (Fin 2) ℝ) (z v) ^ (-(m : ℤ)) := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => ?_
    simp only [Equiv.subtypeUnivEquiv_apply]
    rw [HilbertModular.slHom_det, one_zpow, Complex.ofReal_one, one_mul, hg, HilbertModular.denom_slHom_toF]
    simp only [ew_eq_realEmb, τ]
    rfl
  rw [HilbertModular.slash_apply, ← hJ, Pi.smul_apply, smul_eq_mul, ← h1, ← hgz]
  have hsq := chiFin_mul_self b hb (γ 1 1)
  linear_combination (-(HilbertModular.thetaQ (QuadForm.diag b) gz *
    ∏ w : RP, ((ew w ((g : Matrix (Fin 2) (Fin 2) F) 1 0) : ℂ) * τ w + ew w (g 1 1)) ^ (-(m : ℤ)))) * hsq

/-! ### Identification with the local characters and the Hilbert-symbol formula -/

/-- **Identification of the Route 2 character with the $\chi_Q$**: for $d \in \mathcal O_F$ prime to $\mathfrak N$,
$$\chi_Q(d \bmod \mathfrak N) = \prod_{v<\infty}\chi_v(d),$$
$\chi_Q$ = `HilbertModular.thetaCharF` (Hecke's global route) and $\chi_v$ = `chiLoc`. *Proof:* complete $d$ to
$\gamma = \begin{pmatrix}u&-1\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$; both transformation laws hold for $\gamma$
(`thetaQ_slash_gamma0_char`, `thetaQ_slash_route2`), and $\theta_Q(i, \dots, i) \ne 0$ (`thetaQ_ptI_ne_zero`). -/
@[kb "shimura1973" "§2 (the character of $\\theta_Q$) [unverified]"]
theorem thetaCharF_eq_chiFin (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {d : 𝓞 F}
    (hd : Ideal.span {d} ⊔ 𝔑 = ⊤) :
    HilbertModular.thetaCharF (isTotPosGram_diag b hpos) (rfl : 2 * m = 2 * m) hlev h𝔑
      (Ideal.Quotient.mk 𝔑 d) = chiFin b hb d := by
  have h1 : (1 : 𝓞 F) ∈ Ideal.span {d} ⊔ 𝔑 := by rw [hd]; trivial
  obtain ⟨x, hx, c, hc, hxc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  set γ : SL(2, 𝓞 F) := ⟨!![u, -1; c, d], by simp [Matrix.det_fin_two_of]; linear_combination hxc⟩
  have hγ : γ ∈ HilbertModular.Gamma0R 𝔑 := hc
  have hγd : γ 1 1 = d := rfl
  have hC3 := HilbertModular.thetaQ_slash_gamma0_char (isTotPosGram_diag b hpos) rfl hlev h𝔑 hγ
  rw [thetaQ_slash_route2 b hb hpos hm hlev hγ, hγd] at hC3
  have hz := congrFun hC3 HilbertModular.ptI
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  exact (mul_right_cancel₀ (HilbertModular.thetaQ_ptI_ne_zero (isTotPosGram_diag b hpos)) hz).symm

lemma valued_int_eq_one_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) = 1 := by
  rw [HN.valued_algebraMap]
  exact le_antisymm (v.valuation_le_one x) (not_lt.mp fun h => hx ((v.valuation_lt_one_iff_mem x).mp h))

/-- **At $v \nmid \mathfrak N$ the place is good** ($d_v = 0$, $v \nmid 2$, all $b_i$ units): every dyadic place, every
ramified place and every $v \mid \det Q$ divides the theta level. -/
lemma isGoodV_of_not_le (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔑 ≤ v.asIdeal) : IsGoodV v (aV (bF b hb) v) := by
  obtain ⟨ν, hν, hνv⟩ := Set.not_subset.mp hv
  refine isGoodV_of_level_of_unit v (aV (bF b hb) v) hm (fun i => ?_) (valued_int_eq_one_of_not_mem v hνv)
    (levelV_of_isThetaLevelF b hb hlev hν v)
  rw [aV_val, bF_val]; exact valued_algebraMap_int_le_one v (b i)

/-- **The Hilbert-symbol formula for the Route 2 character**: for $d$ prime to $\mathfrak N$,
$$\prod_{v<\infty}\chi_v(d) = \prod_{v \mid \mathfrak N}\big(d, (-1)^m\det Q\big)_v,\qquad \det Q = \prod_ib_i.$$ -/
@[kb "kudla1996" "§I.4 [unverified]"]
theorem chiFin_eq_hilbert (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) {d : 𝓞 F} (hd : Ideal.span {d} ⊔ 𝔑 = ⊤) :
    chiFin b hb d = ∏ᶠ v : HeightOneSpectrum (𝓞 F), if 𝔑 ≤ v.asIdeal then
      ((hilbertSymbol (v.adicCompletion F) (algebraMap F _ (algebraMap (𝓞 F) F d))
        (algebraMap F _ ((-1) ^ m * ∏ i, (b i : F))) : ℤ) : ℂ) else 1 := by
  refine finprod_congr fun v => ?_
  split_ifs with hv
  · have hdv : d ∉ v.asIdeal := fun h => v.isPrime.ne_top (top_le_iff.mp (hd ▸ sup_le
      ((Ideal.span_singleton_le_iff_mem _).mpr h) hv))
    rw [chiLoc, if_pos (valued_int_eq_one_of_not_mem v hdv)]
    simp only [LocalData.chiV, LocalData.hC, discV_aV]
    rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl]
    congr 3
    simp [discV, bF]
  · exact chiLoc_of_good v _ (isGoodV_of_not_le b hb hm hlev hv) _

/-- **The Hilbert-symbol formula for the character** (Route 2 corollary): for $d \in \mathcal O_F$ prime to $\mathfrak N$,
$$\chi_Q(d \bmod \mathfrak N) = \prod_{v \mid \mathfrak N}\big(d, (-1)^m\det Q\big)_v.$$
Every dyadic place divides $\mathfrak N$ (`isGoodV_of_not_le`), so the dyadic symbols are among the factors; no separate
Weil-index correction appears. -/
@[kb "shimura1973" "§2 (the character of $\\theta_Q$ as a product of Hilbert symbols) [unverified]"]
theorem thetaCharF_eq_hilbert (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hpos : ∀ i v, 0 < HilbertModular.realEmb F v (b i : F)) (hm : 0 < m) {𝔑 : Ideal (𝓞 F)}
    (hlev : HilbertModular.IsThetaLevelF (QuadForm.diag b) 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {d : 𝓞 F}
    (hd : Ideal.span {d} ⊔ 𝔑 = ⊤) :
    HilbertModular.thetaCharF (isTotPosGram_diag b hpos) (rfl : 2 * m = 2 * m) hlev h𝔑
      (Ideal.Quotient.mk 𝔑 d) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), if 𝔑 ≤ v.asIdeal then
      ((hilbertSymbol (v.adicCompletion F) (algebraMap F _ (algebraMap (𝓞 F) F d))
        (algebraMap F _ ((-1) ^ m * ∏ i, (b i : F))) : ℤ) : ℂ) else 1 := by
  rw [thetaCharF_eq_chiFin b hb hpos hm hlev h𝔑 hd, chiFin_eq_hilbert b hb hm hlev hd]

end QuadFormsKB.WeilRep
