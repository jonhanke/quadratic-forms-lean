import QuadFormsKB.Tamagawa.IdeleClass
import QuadFormsKB.HilbertModular.ThetaInversion

/-!
# Weil's additive calculation, anisotropic case: Tate's split and Poisson summation

**Setting.** $F$ totally real of degree $d$, real places $v$ with embeddings $\varphi_v$ (`realEmb F v`), a lattice
$L = \bigoplus_iI_ie_i \subset F^n$ (`I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ`, `latVec`) with a totally positive definite Gram
matrix $A$ (`IsTotPosGram A`; $Q(\xi) = \xi^{\mathsf T}A\xi$), and $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ with the Gaussian
$\Phi_\infty(y) = \exp(-\pi\sum_v\varphi_v(Q)(y_v))$. A totally positive definite form is anisotropic ("index 0" in Weil's §4.4,
p. 97), so $V(F)\setminus0$ contains no isotropic vectors and the only boundary terms come from $\xi = 0$.

**The additive zeta function** (Weil 1982, §4.4, (4), p. 97, for one lattice; the genus version is `AdditiveGenus.lean`): with the integral over the idele class group in the concrete cone model (`IdeleClass.ideleClassLIntegral`, unramified ideles
$z = (x,\mathfrak b)$, $|z| = N(x)/N(\mathfrak b)$),
$$Z^+_L(s) = \int_{I_F/F^\times}|z|^{n+2s}\sum_{\xi\in V(F)\setminus0}\Phi(\xi z)\,d^\times z
  = \int_{I_F/F^\times}|z|^{n+2s}\sum_{\xi\in\mathfrak b^{-1}L\setminus0}e^{-\pi\sum_v|x_v|^2\varphi_v(Q(\xi))}\,d^\times z
  \qquad(\texttt{additiveZeta}),$$
an element of $[0,\infty]$; $\Phi_f(\xi z_f) = \mathbf 1[\xi\in\mathfrak b^{-1}L]$ (`twist`).

**Main results** (all unconditional; axioms `propext`, `Classical.choice`, `Quot.sound`):
* `tsum_gaussTerm_inversion`: theta inversion at imaginary arguments (real form of `thetaLat_inversion`): Poisson
  summation on $L \subset (F\otimes\mathbb R)^n$ for the Gaussian, the substitute for the adelic Poisson formula on $V(\mathbb A)$
 for $\Phi_f = \mathbf 1_{\hat L}$;
* `thetaZero_decay`, `exists_cone_upper`, `cone_lower`: the theta series without its constant term decays like $e^{-\delta m}$,
  and the fundamental cone has bounded shape ($|x_v| \asymp N(x)^{1/d}$);
* `poisson_pointwise`: $|z|^{n+2s}(1+\Theta^0_L(z)) = c_L|z|^{2s}(1+\Theta^{\#0}_L(z^{-1}))$ with $c_L$ = `latConst` $=\hat\Phi(0)$;
* `inner_add_eq` and `additiveZeta_toReal_eq` (**Tate's split**, Weil's (5), p. 98, anisotropic case): for $s > 0$,
  $Z^+_L(s) = Z_+(s) + \frac{c_L\rho_F}{2s} + c_L B(s) - \frac{\rho_F}{n+2s}$, with $Z_+$ (the part $|z| > 1$) and the dual term $B$
  bounded near $s = 0$ (`exists_outer_le`, `exists_dualTerm_le`) and $Z^+_L(s) < \infty$ (`additiveZeta_lt_top`);
* **`tendsto_mul_additiveZeta`**: $\lim_{s\to0^+}s\,Z^+_L(s) = \frac{\rho_F}{2}\,c_L$ ($n \ge 1$), $\rho_F$ = `dedekindZeta_residue F`.

**Normalizations.** $d^\times z$ is Weil's Tamagawa measure on $I_F/F^\times$, so $\int_{|z|\le1}|z|^a\,d^\times z = \rho_F/a$
(`ideleClassLIntegral_le_one_rpow`). $c_L = (\prod_v\sqrt{\det\varphi_v(A)})^{-1}(\prod_i\Delta(I_i))^{-1}$, $\Delta(I) = N(I)\,d_F^{1/2}$
(`embDet_eq`), is $\int_{V(\mathbb A)}\Phi\,dx$ for the self-dual measure; for $L = \mathcal O_F^n$ it equals `phiIntegral` of the
Gaussian $e^{-\pi Q_w}$ (`phiIntegral_gaussian_pi`, `AdditiveGenus.lean`). Weil's exponent $|t|^{2s+m}$ is our $|z|^{n+2s}$.

**Not done.** The substitution $z \mapsto z^{-1}$ in the dual term (so $B(s)$ is not rewritten as $Z^\Psi_+(-s-\frac n2)$), complex $s$
and the meromorphic continuation, ramified $\Phi_f$, and the isotropic case. None is needed for the residue.
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Set Matrix Filter Topology
open scoped Real nonZeroDivisors ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.AdditiveZeta

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-! ### Lattice coordinates are injective -/

lemma sum_intCast_mul_basis_injective (b : Module.Basis (Fin dq) ℚ F) :
    Function.Injective fun k : Fin dq → ℤ => ∑ j, (k j : F) * b j := by
  intro k k' h
  have key : ∀ k : Fin dq → ℤ, ∑ j, (k j : F) * b j = b.equivFun.symm (fun j => (k j : ℚ)) := by
    intro k
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    simp
  simp only at h
  rw [key, key] at h
  have := b.equivFun.symm.injective h
  funext j
  exact_mod_cast congrFun this j

lemma latVec_injective (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Function.Injective (latVec I) := by
  intro k k' h
  funext i
  exact sum_intCast_mul_basis_injective (QuadFormsKB.Analysis.bq (I i)) (congrFun h i)

lemma dualLatVec_injective (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Function.Injective (dualLatVec I) := by
  intro k k' h
  funext i
  exact sum_intCast_mul_basis_injective (QuadFormsKB.Analysis.bq (I i)).traceDual (congrFun h i)

lemma latVec_zero (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : latVec I 0 = 0 := by
  funext i; simp [latVec, QuadFormsKB.Analysis.latElt]

lemma dualLatVec_zero (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : dualLatVec I 0 = 0 := by
  funext i; simp [dualLatVec, QuadFormsKB.Analysis.dualElt]

/-! ### Real Gaussian terms -/

/-- **The real Gaussian term** $\exp(-\pi\sum_v\varphi_v(\xi^{\mathsf T}B\xi)\,t_v)$. -/
def gaussTerm (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) (t : InfinitePlace F → ℝ) : ℝ :=
  Real.exp (-π * ∑ v, realEmb F v (qv B ξ) * t v)

lemma gaussTerm_pos (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) (t : InfinitePlace F → ℝ) :
    0 < gaussTerm B ξ t := Real.exp_pos _

lemma thetaTerm_I_mul (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) (t : InfinitePlace F → ℝ) :
    thetaTerm B ξ (fun v => Complex.I * ((t v / 2 : ℝ) : ℂ)) = (gaussTerm B ξ t : ℂ) := by
  rw [thetaTerm, gaussTerm, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_thetaTerm_I_mul (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) (t : InfinitePlace F → ℝ) :
    ‖thetaTerm B ξ (fun v => Complex.I * ((t v / 2 : ℝ) : ℂ))‖ = gaussTerm B ξ t := by
  rw [thetaTerm_I_mul, Complex.norm_real, Real.norm_of_nonneg (gaussTerm_pos B ξ t).le]

/-- Summability of the lattice Gaussian terms for $t_v > 0$. -/
lemma summable_gaussTerm_lat {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {t : InfinitePlace F → ℝ} (ht : ∀ v, 0 < t v) :
    Summable fun k : Fin n → Fin dq → ℤ => gaussTerm A (latVec I k) t := by
  have h := summable_norm_thetaTerm hA I (z := fun v => Complex.I * ((t v / 2 : ℝ) : ℂ))
    (fun v => by simp [ht v])
  simpa only [norm_thetaTerm_I_mul] using h

/-- Summability of the dual lattice Gaussian terms (form $\frac14A^{-1}$) for $t_v > 0$. -/
lemma summable_gaussTerm_dual {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {t : InfinitePlace F → ℝ} (ht : ∀ v, 0 < t v) :
    Summable fun m : Fin n → Fin dq → ℤ => gaussTerm ((1 / 4 : F) • A⁻¹) (dualLatVec I m) t := by
  set w : InfinitePlace F → ℂ := fun v => ((4 / t v : ℝ) : ℂ)
  have hdet : (dualMat A I).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (latMat_transpose_mul hA I)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hre : ∀ p : Fin n × Fin dq, 0 < ((fun p => (w (placeEquiv p.2))⁻¹) p).re := fun p => by
    have := ht (placeEquiv p.2)
    simp only [w, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have h := summable_norm_gaussAt (dualMat A I) hdet _ hre
  refine (Equiv.curry (Fin n) (Fin dq) ℤ).summable_iff.mp ?_
  refine h.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [gaussAt_dualMat hA I w m, Complex.norm_exp, gaussTerm]
  congr 1
  have hc : (-(Real.pi : ℂ) * ∑ v, (w v)⁻¹ *
      ((realEmb F v (qv A⁻¹ (dualLatVec I (Equiv.curry (Fin n) (Fin dq) ℤ m)))) : ℂ)) =
      ((-π * ∑ v, realEmb F v (qv ((1 / 4 : F) • A⁻¹) (dualLatVec I (Equiv.curry (Fin n) (Fin dq) ℤ m))) * t v :
        ℝ) : ℂ) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    have := (ht v).ne'
    simp only [w, qv_smul, map_mul]
    simp only [map_div₀, map_one, map_ofNat]
    push_cast
    field_simp
  rw [hc, Complex.ofReal_re]

lemma realEmb_qv_pos {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F)
    {ξ : Fin n → F} (hξ : ξ ≠ 0) : 0 < realEmb F v (qv A ξ) := by
  rw [realEmb_qv]
  have hne : (fun i => realEmb F v (ξ i)) ≠ 0 := by
    intro h
    apply hξ
    funext i
    exact (realEmb F v).injective (by simpa using congrFun h i)
  simpa using (hA v).dotProduct_mulVec_pos hne

lemma realEmb_qv_dual_pos {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F)
    {μ : Fin n → F} (hμ : μ ≠ 0) : 0 < realEmb F v (qv ((1 / 4 : F) • A⁻¹) μ) := by
  rw [qv_smul, map_mul, realEmb_qv, map_inv_realEmb hA]
  have hne : (fun i => realEmb F v (μ i)) ≠ 0 := by
    intro h
    apply hμ
    funext i
    exact (realEmb F v).injective (by simpa using congrFun h i)
  have := (hA v).inv.dotProduct_mulVec_pos hne
  simp only [map_div₀, map_one, map_ofNat]
  simp at this
  positivity

lemma realEmb_qv_dual_nonneg {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F)
    (μ : Fin n → F) : 0 ≤ realEmb F v (qv ((1 / 4 : F) • A⁻¹) μ) := by
  by_cases hμ : μ = 0
  · simp [hμ, qv]
  · exact (realEmb_qv_dual_pos hA v hμ).le

/-! ### Exponential decay of a theta series without its constant term -/

/-- **Decay of a lattice theta series minus its constant term.** Let $q_i \in [0,\infty)^{\{v\}}$ ($i \in \iota$) with
$\sum_vq_{i,v} > 0$ for $i \ne i_0$ and $\sum_i\exp(-\pi m_0\sum_vq_{i,v}) < \infty$ for some $m_0 > 0$. Then there are $C \ge 0$,
$\delta > 0$ with
$$\sum_{i\ne i_0}\exp\Big(-\pi\sum_vq_{i,v}t_v\Big) \le C\,e^{-\delta m}\qquad\text{whenever } m \ge m_0,\ t_v \ge m\ \forall v.$$ -/
theorem exists_decay {ι : Type*} [DecidableEq ι] (q : ι → InfinitePlace F → ℝ) (i₀ : ι) (hq0 : ∀ i v, 0 ≤ q i v)
    (hpos : ∀ i, i ≠ i₀ → 0 < ∑ v, q i v) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hsum : Summable fun i => Real.exp (-π * ∑ v, q i v * m₀)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (t : InfinitePlace F → ℝ) (m : ℝ), m₀ ≤ m → (∀ v, m ≤ t v) →
      ∑' i, (if i = i₀ then 0 else ENNReal.ofReal (Real.exp (-π * ∑ v, q i v * t v))) ≤
        ENNReal.ofReal (C * Real.exp (-δ * m)) := by
  set S : ι → ℝ := fun i => ∑ v, q i v
  have hS0 : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg fun v _ => hq0 i v
  have hsum' : Summable fun i => Real.exp (-π * m₀ * S i) := hsum.congr fun i => by
    simp only [S, Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun v _ => ?_; ring
  -- finitely many `i` with `S i ≤ 1`
  have hfin : {i | S i ≤ 1}.Finite := by
    have h := hsum'.tendsto_cofinite_zero
    have hε : (0 : ℝ) < Real.exp (-π * m₀) := Real.exp_pos _
    have := h.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq, not_lt] at hi ⊢
    refine Real.exp_le_exp.2 ?_
    have : m₀ * S i ≤ m₀ := by nlinarith
    nlinarith [Real.pi_pos]
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, i ≠ i₀ → δ₀ ≤ S i := by
    set T := hfin.toFinset.filter (· ≠ i₀)
    by_cases hT : T.Nonempty
    · obtain ⟨j, hj, hjmin⟩ := T.exists_min_image S hT
      refine ⟨min 1 (S j), lt_min one_pos (hpos j (Finset.mem_filter.1 hj).2), fun i hi => ?_⟩
      by_cases h1 : S i ≤ 1
      · exact (min_le_right _ _).trans (hjmin i (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 h1, hi⟩))
      · exact (min_le_left _ _).trans (le_of_not_ge h1)
    · refine ⟨1, one_pos, fun i hi => ?_⟩
      by_contra h1
      push Not at h1
      exact hT ⟨i, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 h1.le, hi⟩⟩
  set C := (∑' i, Real.exp (-π * m₀ * S i)) * Real.exp (π * m₀ * δ₀)
  refine ⟨C, π * δ₀, by positivity, by positivity, fun t m hm ht => ?_⟩
  have hterm : ∀ i, i ≠ i₀ → Real.exp (-π * ∑ v, q i v * t v) ≤
      Real.exp (-π * m₀ * S i) * (Real.exp (π * m₀ * δ₀) * Real.exp (-(π * δ₀) * m)) := by
    intro i hi
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : m * S i ≤ ∑ v, q i v * t v := by
      simp only [S, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => by nlinarith [hq0 i v, ht v]
    have h2 := hδ₀le i hi
    have h3 : (m - m₀) * δ₀ ≤ (m - m₀) * S i := mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith [Real.pi_pos]
  calc ∑' i, (if i = i₀ then 0 else ENNReal.ofReal (Real.exp (-π * ∑ v, q i v * t v)))
      ≤ ∑' i, ENNReal.ofReal (Real.exp (-π * m₀ * S i) * (Real.exp (π * m₀ * δ₀) * Real.exp (-(π * δ₀) * m))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        split_ifs with hi
        · exact zero_le
        · exact ENNReal.ofReal_le_ofReal (hterm i hi)
    _ = ENNReal.ofReal (∑' i, Real.exp (-π * m₀ * S i) * (Real.exp (π * m₀ * δ₀) * Real.exp (-(π * δ₀) * m))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hsum'.mul_right _)).symm
    _ = ENNReal.ofReal (C * Real.exp (-(π * δ₀) * m)) := by
        rw [tsum_mul_right]; simp only [C]; ring_nf

/-! ### The theta series without the constant term -/

/-- **The lattice theta series without its constant term**, in $[0,\infty]$:
$\Theta^0_{A,L}(t) = \sum_{\xi\in L\setminus0}\exp(-\pi\sum_v\varphi_v(\xi^{\mathsf T}A\xi)\,t_v)$, $L = \bigoplus_iI_ie_i$ (`latVec`). -/
def thetaZero (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : InfinitePlace F → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin n → Fin dq → ℤ, if k = 0 then 0 else ENNReal.ofReal (gaussTerm A (latVec I k) t)

/-- **The dual theta series without its constant term**: $\Theta^{\#0}_{A,L}(t) = \sum_{\mu\in L^\#\setminus0}
\exp(-\pi\sum_v\varphi_v(\tfrac14\mu^{\mathsf T}A^{-1}\mu)\,t_v)$ (`dualLatVec`). -/
def thetaDualZero (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : InfinitePlace F → ℝ) : ℝ≥0∞ :=
  ∑' m : Fin n → Fin dq → ℤ, if m = 0 then 0 else
    ENNReal.ofReal (gaussTerm ((1 / 4 : F) • A⁻¹) (dualLatVec I m) t)

lemma gaussTerm_zero (B : Matrix (Fin n) (Fin n) F) (t : InfinitePlace F → ℝ) : gaussTerm B 0 t = 1 := by
  simp [gaussTerm, qv]

lemma one_add_thetaZero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {t : InfinitePlace F → ℝ} (ht : ∀ v, 0 < t v) :
    1 + thetaZero A I t = ENNReal.ofReal (∑' k, gaussTerm A (latVec I k) t) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (gaussTerm_pos _ _ _).le) (summable_gaussTerm_lat hA I ht),
    ENNReal.tsum_eq_add_tsum_ite 0, latVec_zero, gaussTerm_zero, ENNReal.ofReal_one, thetaZero]
  congr!

lemma one_add_thetaDualZero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {t : InfinitePlace F → ℝ} (ht : ∀ v, 0 < t v) :
    1 + thetaDualZero A I t = ENNReal.ofReal (∑' m, gaussTerm ((1 / 4 : F) • A⁻¹) (dualLatVec I m) t) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (gaussTerm_pos _ _ _).le) (summable_gaussTerm_dual hA I ht),
    ENNReal.tsum_eq_add_tsum_ite 0, dualLatVec_zero, gaussTerm_zero, ENNReal.ofReal_one, thetaDualZero]
  congr!

/-- **Decay of $\Theta^0$**: for every $m_0 > 0$ there are $C \ge 0$, $\delta > 0$ with $\Theta^0_{A,L}(t) \le Ce^{-\delta m}$ whenever
$m \ge m_0$ and $t_v \ge m$ at every place. -/
theorem thetaZero_decay {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {m₀ : ℝ} (hm₀ : 0 < m₀) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (t : InfinitePlace F → ℝ) (m : ℝ), m₀ ≤ m → (∀ v, m ≤ t v) →
      thetaZero A I t ≤ ENNReal.ofReal (C * Real.exp (-δ * m)) := by
  have h := exists_decay (fun k v => realEmb F v (qv A (latVec I k))) 0
    (fun k v => qv_nonneg hA v _) (fun k hk => Finset.sum_pos (fun v _ => realEmb_qv_pos hA v
      (fun h0 => hk (latVec_injective I (h0.trans (latVec_zero I).symm)))) Finset.univ_nonempty)
    hm₀ (summable_gaussTerm_lat hA I (t := fun _ => m₀) fun _ => hm₀)
  exact h

/-- **Decay of $\Theta^{\#0}$** (the same for the dual lattice and the form $\frac14A^{-1}$). -/
theorem thetaDualZero_decay {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {m₀ : ℝ} (hm₀ : 0 < m₀) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (t : InfinitePlace F → ℝ) (m : ℝ), m₀ ≤ m → (∀ v, m ≤ t v) →
      thetaDualZero A I t ≤ ENNReal.ofReal (C * Real.exp (-δ * m)) := by
  have h := exists_decay (fun k v => realEmb F v (qv ((1 / 4 : F) • A⁻¹) (dualLatVec I k))) 0
    (fun k v => realEmb_qv_dual_nonneg hA v _) (fun k hk => Finset.sum_pos (fun v _ => realEmb_qv_dual_pos hA v
      (fun h0 => hk (dualLatVec_injective I (h0.trans (dualLatVec_zero I).symm)))) Finset.univ_nonempty)
    hm₀ (summable_gaussTerm_dual hA I (t := fun _ => m₀) fun _ => hm₀)
  exact h

/-! ### Theta inversion in real form -/

/-- **The covolume constant** $c_L = \big(\prod_v\sqrt{\det\varphi_v(A)}\big)^{-1}\big(\prod_i\Delta(I_i)\big)^{-1}$ of
$L = \bigoplus_iI_ie_i$ with Gram matrix $A$; $c_L = \int_{(F\otimes\mathbb R)^n}e^{-\pi\sum_v\varphi_v(Q)(y_v)}\,dy\,/\operatorname{covol}(L)$, the
Lebesgue measure being normalized so that $\mathcal O_F \subset \mathbb R^d$ has covolume $|d_F|^{1/2}$ (`embDet_one`). -/
def latConst (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : ℝ :=
  (∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (I i))⁻¹

/-- **Theta inversion at imaginary arguments** (real form of `thetaLat_inversion`): for $t_v > 0$,
$$\sum_{\xi\in L}e^{-\pi\sum_v\varphi_v(Q(\xi))t_v} = c_L\prod_vt_v^{-n/2}\sum_{\mu\in L^\#}e^{-\pi\sum_v\varphi_v(Q^\#(\mu))\,4/t_v}.$$
This is Poisson summation for $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ on $V(F) \subset V(\mathbb A)$ (Weil §4.4, p. 97) at the idele $z$ with
$|x_v|^2 = t_v$, $\hat\Phi(0) = c_L$. -/
@[kb "weil1982" "§4.4, p. 97 (Poisson summation Σ_ξΦ(Xξz) = |z̄z|^{-δm/2}Σ_ηΨ(X′ηz̄⁻¹)); cf. thetaLat_inversion"]
theorem tsum_gaussTerm_inversion {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {t : InfinitePlace F → ℝ} (ht : ∀ v, 0 < t v) :
    ∑' k, gaussTerm A (latVec I k) t = latConst A I * (∏ v, t v ^ (-(n : ℝ) / 2)) *
      ∑' m, gaussTerm ((1 / 4 : F) • A⁻¹) (dualLatVec I m) (fun v => 4 / t v) := by
  set z : InfinitePlace F → ℂ := fun v => Complex.I * (((4 / t v) / 2 : ℝ) : ℂ)
  have hz : ∀ v, 0 < (z v).im := fun v => by have := ht v; simp [z]; positivity
  have h := thetaLat_inversion hA I hz
  have hw : (fun v => -(z v)⁻¹) = fun v => Complex.I * ((t v / 2 : ℝ) : ℂ) := by
    funext v
    have := (ht v).ne'
    simp only [z]
    push_cast
    field_simp
    rw [Complex.I_sq]; ring
  have hc : ∀ v, (-Complex.I * z v / 2) = ((1 / t v : ℝ) : ℂ) := fun v => by
    have := (ht v).ne'
    simp only [z]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hw, thetaLat, thetaLatDual] at h
  simp_rw [thetaTerm_I_mul] at h
  have hz' : ∀ μ, thetaTerm ((1 / 4 : F) • A⁻¹) μ z = (gaussTerm ((1 / 4 : F) • A⁻¹) μ (fun v => 4 / t v) : ℂ) :=
    fun μ => thetaTerm_I_mul _ μ (fun v => 4 / t v)
  simp_rw [hz', hc] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, h]
  simp only [latConst, Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_inv]
  congr 2
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_cpow (by have := ht v; positivity)]
  congr 1
  rw [one_div, Real.inv_rpow (ht v).le, ← Real.rpow_neg (ht v).le, neg_div]

/-! ### Twisting the lattice by the finite part of an idele -/

open QuadFormsKB.IdeleClass in
/-- **The lattice $\mathfrak b^{-1}L$**: $\bigoplus_i\mathfrak b^{-1}I_ie_i$ for $L = \bigoplus_iI_ie_i$. For an unramified idele
$z = (x,\mathfrak b)$ ($\mathfrak b$ the ideal of its finite part) and $\Phi_f = \mathbf 1_{\hat L}$: $\Phi_f(\xi z_f) = 1 \iff \xi \in \mathfrak b^{-1}L$. -/
def twist (𝔟 : FracIdeal F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  fun i => 𝔟⁻¹ * I i

/-- $d_F > 0$ for $F$ totally real (from $\Delta(\mathcal O_F)^2 = d_F$, `embDet_sq_eq`). -/
lemma discr_pos : (0 : ℝ) < NumberField.discr F := by
  have h := embDet_sq_eq (F := F) 1
  have h0 : (NumberField.discr F : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
  simp only [Units.val_one, map_one, Rat.cast_one, one_pow, one_mul] at h
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · have : 0 ≤ embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) ^ 2 := sq_nonneg _
    linarith
  · exact hgt

/-- $\Delta(J) = N(J)\,d_F^{1/2}$. -/
lemma embDet_eq (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    embDet J = (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) : ℝ) * Real.sqrt (NumberField.discr F) := by
  have h := embDet_sq_eq J
  have h0 : 0 ≤ embDet J := abs_nonneg _
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg _
  rw [← Real.sqrt_sq h0, h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN]

open QuadFormsKB.IdeleClass in
lemma embDet_twist (𝔟 : FracIdeal F) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    embDet (𝔟⁻¹ * J) = (idealNorm F 𝔟)⁻¹ * embDet J := by
  rw [embDet_eq, embDet_eq, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, idealNorm]
  push_cast
  ring

open QuadFormsKB.IdeleClass in
lemma embDet_pos (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : 0 < embDet J := by
  rw [embDet_eq]
  have := idealNorm_pos F J
  unfold idealNorm at this
  exact mul_pos this (Real.sqrt_pos.2 discr_pos)

lemma latConst_pos {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : 0 < latConst A I := by
  unfold latConst
  have h1 : 0 < ∏ v, Real.sqrt (A.map (realEmb F v)).det :=
    Finset.prod_pos fun v _ => Real.sqrt_pos.2 (hA v).det_pos
  have h2 : 0 < ∏ i, embDet (I i) := Finset.prod_pos fun i _ => embDet_pos (I i)
  positivity

open QuadFormsKB.IdeleClass in
/-- $c_{\mathfrak b^{-1}L} = N(\mathfrak b)^n\,c_L$ (the covolume of $\mathfrak b^{-1}L$ is $N(\mathfrak b)^{-n}$ times that of $L$). -/
lemma latConst_twist (A : Matrix (Fin n) (Fin n) F) (𝔟 : FracIdeal F)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    latConst A (twist 𝔟 I) = idealNorm F 𝔟 ^ n * latConst A I := by
  unfold latConst twist
  simp_rw [embDet_twist]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, mul_inv, inv_inv]
  ring

/-! ### The shape of the fundamental cone -/

/-- For $F$ totally real, $N(x) = \prod_v|x_v|$ (all multiplicities are $1$). -/
lemma norm_eq_prod (x : mixedSpace F) : mixedEmbedding.norm x = ∏ v, normAtPlace v x := by
  rw [mixedEmbedding.norm_apply]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [InfinitePlace.mult, IsTotallyReal.isReal v]

/-- **The fundamental cone has bounded shape**: there is $R > 0$ with $|x_v| \le R\,N(x)^{1/d}$ for every $x$ in the cone
and every place $v$ (from `isBounded_normLeOne` and homogeneity). -/
theorem exists_cone_upper :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ fundamentalCone F, ∀ v,
      normAtPlace v x ≤ R * mixedEmbedding.norm x ^ ((dq : ℝ)⁻¹) := by
  classical
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 (fundamentalCone.isBounded_normLeOne F)
  refine ⟨max R₀ 1, lt_max_of_lt_right one_pos, fun x hx v => ?_⟩
  have hN := fundamentalCone.norm_pos_of_mem hx
  have hd : (0 : ℝ) < dq := by exact_mod_cast Module.finrank_pos
  set a := mixedEmbedding.norm x ^ ((dq : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have had : a ^ dq = mixedEmbedding.norm x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, inv_mul_cancel₀ hd.ne', Real.rpow_one]
  have hy : a⁻¹ • x ∈ fundamentalCone.normLeOne F := by
    refine (fundamentalCone.mem_normLeOne).2 ⟨fundamentalCone.smul_mem_of_mem hx (inv_ne_zero ha.ne'), ?_⟩
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos ha, inv_pow, had, inv_mul_cancel₀ hN.ne']
  have h1 := hR₀ _ hy
  have h2 : normAtPlace v (a⁻¹ • x) ≤ ‖a⁻¹ • x‖ := by
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => normAtPlace w (a⁻¹ • x)) (Finset.mem_univ v)
  rw [normAtPlace_smul, abs_inv, abs_of_pos ha] at h2
  have h3 : a⁻¹ * normAtPlace v x ≤ max R₀ 1 := (h2.trans h1).trans (le_max_left _ _)
  rw [inv_mul_le_iff₀ ha] at h3
  linarith [mul_comm a (max R₀ 1)]

/-- **Lower shape bound**: with $R$ as in `exists_cone_upper`, $|x_v| \ge R^{1-d}N(x)^{1/d}$ on the cone. -/
theorem cone_lower {R : ℝ} (hR : 0 < R)
    (hup : ∀ x ∈ fundamentalCone F, ∀ v, normAtPlace v x ≤ R * mixedEmbedding.norm x ^ ((dq : ℝ)⁻¹))
    {x : mixedSpace F} (hx : x ∈ fundamentalCone F) (v : InfinitePlace F) :
    mixedEmbedding.norm x ^ ((dq : ℝ)⁻¹) / R ^ (dq - 1) ≤ normAtPlace v x := by
  classical
  have hN := fundamentalCone.norm_pos_of_mem hx
  have hd : (0 : ℝ) < dq := by exact_mod_cast Module.finrank_pos
  set a := mixedEmbedding.norm x ^ ((dq : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have had : a ^ dq = mixedEmbedding.norm x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, inv_mul_cancel₀ hd.ne', Real.rpow_one]
  have hpos : ∀ w, 0 < normAtPlace w x := fun w => fundamentalCone.normAtPlace_pos_of_mem hx w
  have hprod : mixedEmbedding.norm x = normAtPlace v x * ∏ w ∈ Finset.univ.erase v, normAtPlace w x := by
    rw [norm_eq_prod]; exact (Finset.mul_prod_erase _ (fun w => normAtPlace w x) (Finset.mem_univ v)).symm
  have hle : ∏ w ∈ Finset.univ.erase v, normAtPlace w x ≤ (R * a) ^ (dq - 1) := by
    have := Finset.prod_le_prod₀ (s := Finset.univ.erase v) (fun w _ => (hpos w).le) (fun w _ => hup x hx w)
    rwa [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      card_infinitePlace] at this
  have hdq : 1 ≤ dq := Module.finrank_pos
  have key : a ^ dq ≤ normAtPlace v x * (R * a) ^ (dq - 1) := by
    rw [had, hprod]; exact mul_le_mul_of_nonneg_left hle (hpos v).le
  have ha' : a ^ dq = a * a ^ (dq - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hdq]
  rw [ha', mul_pow] at key
  rw [div_le_iff₀ (pow_pos hR _)]
  have hap : 0 < a ^ (dq - 1) := pow_pos ha _
  nlinarith [mul_comm (R ^ (dq - 1)) (a ^ (dq - 1))]

/-! ### Two elementary bounds -/

/-- $u^{n+2s}e^{-cu^{2/d}} \le M u^{-1}$ for $u \ge 1$, $0 \le s \le S$ ($c > 0$, $d \ge 1$, $S \in \mathbb N$). -/
lemma exists_rpow_mul_exp_le (c : ℝ) (hc : 0 < c) (d : ℕ) (hd : 1 ≤ d) (n S : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 1 ≤ u → ∀ s : ℝ, 0 ≤ s → s ≤ S →
      u ^ ((n : ℝ) + 2 * s) * Real.exp (-(c * u ^ ((2 : ℝ) / d))) ≤ M * u ^ (-1 : ℝ) := by
  set K := d * (n + 2 * S + 3)
  refine ⟨K.factorial / c ^ K, by positivity, fun u hu s hs0 hs1 => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  set y := c * u ^ ((2 : ℝ) / d)
  have hy : 0 < y := mul_pos hc (Real.rpow_pos_of_pos hu0 _)
  have hexp : Real.exp (-y) ≤ K.factorial / y ^ K := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have := Real.pow_div_factorial_le_exp y hy.le K
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hy _)]
    nlinarith [Real.exp_pos y]
  have hyK : y ^ K = c ^ K * u ^ (2 * ((n : ℝ) + 2 * S + 3)) := by
    simp only [y]
    rw [mul_pow, ← Real.rpow_natCast (u ^ _), ← Real.rpow_mul hu0.le]
    congr 2
    simp only [K]
    push_cast
    field_simp
  calc u ^ ((n : ℝ) + 2 * s) * Real.exp (-y) ≤ u ^ ((n : ℝ) + 2 * s) * (K.factorial / y ^ K) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = K.factorial / c ^ K * (u ^ ((n : ℝ) + 2 * s) / u ^ (2 * ((n : ℝ) + 2 * S + 3))) := by
        rw [hyK]; field_simp
    _ ≤ K.factorial / c ^ K * u ^ (-1 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.rpow_sub hu0]
        exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)

/-- $e^{-y} \le y^{-1}$ for $y > 0$. -/
lemma exp_neg_le_inv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hy (by linarith [Real.add_one_le_exp y])

/-! ### Integration over the idele class group: linearity and the power integrals -/

open QuadFormsKB.IdeleClass

section Integrals

variable (F)

lemma measurable_ideleNorm (𝔞 : FracIdeal F) : Measurable fun x : mixedSpace F => ideleNorm F x 𝔞 :=
  (mixedEmbedding.continuous_norm F).measurable.div_const _

lemma measurable_ofReal_inv_norm :
    Measurable fun x : mixedSpace F => ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ :=
  (mixedEmbedding.continuous_norm F).measurable.inv.ennreal_ofReal

lemma ideleClassLIntegral_add {f g : mixedSpace F → FracIdeal F → ℝ≥0∞} (hf : ∀ 𝔞, Measurable (f · 𝔞)) :
    ideleClassLIntegral F (fun x 𝔞 => f x 𝔞 + g x 𝔞) = ideleClassLIntegral F f + ideleClassLIntegral F g := by
  simp only [ideleClassLIntegral, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp_rw [add_mul]
  exact lintegral_add_left ((hf _).mul (measurable_ofReal_inv_norm F)) _

lemma ideleClassLIntegral_mono_cone {f g : mixedSpace F → FracIdeal F → ℝ≥0∞}
    (h : ∀ c, ∀ x ∈ fundamentalCone F, f x (classRep F c) ≤ g x (classRep F c)) :
    ideleClassLIntegral F f ≤ ideleClassLIntegral F g := by
  unfold ideleClassLIntegral
  refine mul_le_mul le_rfl (Finset.sum_le_sum fun c _ => ?_) zero_le zero_le
  exact setLIntegral_mono' (measurableSet_fundamentalCone F) fun x hx => mul_le_mul (h c x hx) le_rfl
    zero_le zero_le

lemma ideleClassLIntegral_congr_cone {f g : mixedSpace F → FracIdeal F → ℝ≥0∞}
    (h : ∀ c, ∀ x ∈ fundamentalCone F, f x (classRep F c) = g x (classRep F c)) :
    ideleClassLIntegral F f = ideleClassLIntegral F g :=
  le_antisymm (ideleClassLIntegral_mono_cone F fun c x hx => (h c x hx).le)
    (ideleClassLIntegral_mono_cone F fun c x hx => (h c x hx).ge)

lemma ideleClassLIntegral_const_mul (r : ℝ≥0∞) (hr : r ≠ ⊤) (f : mixedSpace F → FracIdeal F → ℝ≥0∞) :
    ideleClassLIntegral F (fun x 𝔞 => r * f x 𝔞) = r * ideleClassLIntegral F f := by
  simp only [ideleClassLIntegral, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lintegral_const_mul' r _ hr]
  ring

/-- $\int_0^1t^{a}\,dt/t = 1/a$, as a lower integral. -/
lemma lintegral_Ioi_indicator_Iic_rpow {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) t * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (1 / a) := by
  have h1 : ∫⁻ t in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) t * ENNReal.ofReal t⁻¹ =
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1)) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
    congr 1; funext t
    by_cases h0 : 0 < t
    · by_cases h1 : t ≤ 1
      · simp only [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from h0),
          Set.indicator_of_mem (show t ∈ Iic (1 : ℝ) from h1), Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨h0, h1⟩)]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0.le _), Real.rpow_sub_one h0.ne', div_eq_mul_inv]
      · simp [Set.indicator_of_notMem (show t ∉ Iic (1 : ℝ) from h1), Set.indicator_of_notMem
          (show t ∉ Ioc (0 : ℝ) 1 from fun h => h1 h.2), h0]
    · simp [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from h0),
        Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => h0 h.1)]
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _),
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
  rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow ha.ne', sub_zero]

/-- $\int_1^\infty t^{-a}\,dt/t = 1/a$, as a lower integral. -/
lemma lintegral_Ioi_indicator_Ioi_rpow_neg {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-a))) t * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (1 / a) := by
  have h1 : ∫⁻ t in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-a))) t * ENNReal.ofReal t⁻¹ =
      ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-a - 1)) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    congr 1; funext t
    by_cases h1 : 1 < t
    · have h0 : 0 < t := one_pos.trans h1
      simp only [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from h0),
        Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1)]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0.le _), Real.rpow_sub_one h0.ne', div_eq_mul_inv]
    · simp [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1)]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-a - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => Real.rpow_nonneg (zero_le_one.trans ht.le) _),
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  rw [show -a - 1 + 1 = -a by ring, Real.one_rpow, div_neg, neg_div, neg_neg]

/-- **The inner boundary integral**, $\int_{|z|\le1}|z|^a\,d^\times z = \rho_F/a$ ($a > 0$; lower-integral form of
`ideleClassIntegral_rpow_le_one`). -/
theorem ideleClassLIntegral_le_one_rpow {a : ℝ} (ha : 0 < a) :
    ideleClassLIntegral F (fun x 𝔞 => (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) (ideleNorm F x 𝔞)) =
      ENNReal.ofReal (dedekindZeta_residue F / a) := by
  rw [ideleClassLIntegral_comp_ideleNorm F (f := (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)))
      ((measurable_id.pow_const a).ennreal_ofReal.indicator measurableSet_Iic),
    lintegral_Ioi_indicator_Iic_rpow ha, ← ENNReal.ofReal_mul (dedekindZeta_residue_pos F).le]
  ring_nf

/-- **The outer boundary integral**, $\int_{|z|>1}|z|^{-a}\,d^\times z = \rho_F/a$ ($a > 0$). -/
theorem ideleClassLIntegral_gt_one_rpow_neg {a : ℝ} (ha : 0 < a) :
    ideleClassLIntegral F (fun x 𝔞 => (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-a))) (ideleNorm F x 𝔞)) =
      ENNReal.ofReal (dedekindZeta_residue F / a) := by
  rw [ideleClassLIntegral_comp_ideleNorm F (f := (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-a))))
      ((measurable_id.pow_const (-a)).ennreal_ofReal.indicator measurableSet_Ioi),
    lintegral_Ioi_indicator_Ioi_rpow_neg ha, ← ENNReal.ofReal_mul (dedekindZeta_residue_pos F).le]
  ring_nf

end Integrals

/-! ### The additive zeta function of a lattice -/

/-- $t_v = |x_v|^2$ for $x \in F_\infty$. -/
def sqPlaces (x : mixedSpace F) : InfinitePlace F → ℝ := fun v => normAtPlace v x ^ 2

lemma sqPlaces_pos {x : mixedSpace F} (hx : 0 < mixedEmbedding.norm x) (v : InfinitePlace F) :
    0 < sqPlaces x v := by
  have := (mixedEmbedding.norm_ne_zero_iff.mp hx.ne' v)
  exact pow_pos (lt_of_le_of_ne (normAtPlace_nonneg _ _) (Ne.symm this)) 2

lemma measurable_gaussTerm_sq (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) :
    Measurable fun x : mixedSpace F => gaussTerm B ξ (sqPlaces x) := by
  unfold gaussTerm sqPlaces
  exact Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun v _ =>
    measurable_const.mul ((continuous_normAtPlace v).measurable.pow_const 2)))

lemma measurable_gaussTerm_invSq (B : Matrix (Fin n) (Fin n) F) (ξ : Fin n → F) :
    Measurable fun x : mixedSpace F => gaussTerm B ξ (fun v => 4 / sqPlaces x v) := by
  unfold gaussTerm sqPlaces
  exact Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun v _ =>
    measurable_const.mul (measurable_const.div ((continuous_normAtPlace v).measurable.pow_const 2))))

lemma measurable_thetaZero_sq (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Measurable fun x : mixedSpace F => thetaZero A J (sqPlaces x) := by
  refine Measurable.tsum fun k => ?_
  split_ifs
  · exact measurable_const
  · exact (measurable_gaussTerm_sq A _).ennreal_ofReal

lemma measurable_thetaDualZero_invSq (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Measurable fun x : mixedSpace F => thetaDualZero A J (fun v => 4 / sqPlaces x v) := by
  refine Measurable.tsum fun k => ?_
  split_ifs
  · exact measurable_const
  · exact (measurable_gaussTerm_invSq _ _).ennreal_ofReal

/-- **The integrand of the additive zeta function** at the unramified idele $z = (x,\mathfrak b)$:
$$|z|^{n+2s}\sum_{\xi\in\mathfrak b^{-1}L\setminus0}\exp\Big(-\pi\sum_v|x_v|^2\varphi_v(Q(\xi))\Big)
  = |z|^{n+2s}\sum_{\xi\in V(F)\setminus0}\Phi(\xi z),$$
$\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$, $\Phi_\infty(y) = \exp(-\pi\sum_v\varphi_v(Q)(y_v))$ (the Gaussian of the totally positive form;
$\Phi_\infty(\xi x) = \exp(-\pi\sum_vx_v^2\varphi_v(Q(\xi)))$), and $\mathbf 1_{\hat L}(\xi z_f) = \mathbf 1[\xi\in\mathfrak b^{-1}L]$. -/
def zetaIntegrand (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ)
    (x : mixedSpace F) (𝔟 : FracIdeal F) : ℝ≥0∞ :=
  ENNReal.ofReal (ideleNorm F x 𝔟 ^ ((n : ℝ) + 2 * s)) * thetaZero A (twist 𝔟 I) (sqPlaces x)

/-- **Weil's additive zeta function of one lattice** (formula (4) of §4.4, p. 97, as used in §4.5, p. 109, for the
orbit of one lattice; anisotropic case):
$$Z^+_L(s) = \int_{I_F/F^\times}|z|^{n+2s}\sum_{\xi\in V(F)\setminus0}\Phi(\xi z)\,d^\times z \in [0,\infty],$$
$d^\times z$ Weil's Tamagawa measure on $I_F/F^\times$ (`ideleClassLIntegral`), $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ as in
`zetaIntegrand`, $L = \bigoplus_iI_ie_i$ with totally positive Gram matrix $A$ ($Q(\xi) = \xi^{\mathsf T}A\xi$). Weil's exponent
$|t|^{2s+m}$ with $m = n$ variables. The genus version (the $SO(V)(F)\backslash SO(V)(\mathbb A)$-integral) is the weighted sum
over classes, `genusAdditiveZeta`. -/
@[kb "weil1982" "§4.4, (4), p. 97; §4.5, p. 109 (Z(s) = ∫|t|^{2s+m}Σ_{F(ξ)≠0}Φ(Xξt))"]
def additiveZeta (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ideleClassLIntegral F (zetaIntegrand A I s)

lemma measurable_zetaIntegrand (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (s : ℝ) (𝔟 : FracIdeal F) : Measurable fun x => zetaIntegrand A I s x 𝔟 :=
  ((measurable_ideleNorm F 𝔟).pow_const _).ennreal_ofReal.mul (measurable_thetaZero_sq A _)

/-- **Poisson summation, pointwise** (theta inversion for $\mathfrak b^{-1}L$): for $N(x) > 0$,
$$|z|^{n+2s}\Big(1 + \sum_{\xi\ne0}\Phi(\xi z)\Big) = c_L\,|z|^{2s}\Big(1 + \sum_{\mu\in(\mathfrak b^{-1}L)^\#\setminus0}
  \exp\big(-\pi\textstyle\sum_v\varphi_v(Q^\#(\mu))\,4/|x_v|^2\big)\Big).$$ -/
@[kb "weil1982" "§4.4, p. 97 (Poisson summation applied in Z_−; Ψ(0) = Φ̂(0))"]
theorem poisson_pointwise {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) {x : mixedSpace F} (hx : 0 < mixedEmbedding.norm x)
    (𝔟 : FracIdeal F) :
    ENNReal.ofReal (ideleNorm F x 𝔟 ^ ((n : ℝ) + 2 * s)) * (1 + thetaZero A (twist 𝔟 I) (sqPlaces x)) =
      ENNReal.ofReal (latConst A I * ideleNorm F x 𝔟 ^ (2 * s)) *
        (1 + thetaDualZero A (twist 𝔟 I) (fun v => 4 / sqPlaces x v)) := by
  have ht := sqPlaces_pos hx
  have hz : 0 < ideleNorm F x 𝔟 := div_pos hx (idealNorm_pos F 𝔟)
  rw [one_add_thetaZero hA _ ht, one_add_thetaDualZero hA _ (fun v => div_pos four_pos (ht v)),
    tsum_gaussTerm_inversion hA _ ht, latConst_twist]
  have hS : 0 ≤ ∑' m, gaussTerm ((1 / 4 : F) • A⁻¹) (dualLatVec (twist 𝔟 I) m) (fun v => 4 / sqPlaces x v) :=
    tsum_nonneg fun m => (gaussTerm_pos _ _ _).le
  have hc := latConst_pos hA I
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hprod : ∏ v, sqPlaces x v ^ (-(n : ℝ) / 2) = mixedEmbedding.norm x ^ (-(n : ℝ)) := by
    have h1 : ∀ v, sqPlaces x v ^ (-(n : ℝ) / 2) = normAtPlace v x ^ (-(n : ℝ)) := fun v => by
      unfold sqPlaces
      rw [← Real.rpow_natCast (normAtPlace v x) 2, ← Real.rpow_mul (normAtPlace_nonneg _ _)]
      congr 1; push_cast; ring
    simp_rw [h1]
    rw [Real.finsetProd_rpow _ _ (fun v _ => normAtPlace_nonneg _ _), ← norm_eq_prod]
  rw [hprod]
  have hN𝔟 := idealNorm_pos F 𝔟
  have hzdef : ideleNorm F x 𝔟 = mixedEmbedding.norm x / idealNorm F 𝔟 := rfl
  rw [Real.rpow_add hz, Real.rpow_natCast, Real.rpow_neg hx.le, Real.rpow_natCast, hzdef, div_pow]
  field_simp

/-! ### The two halves of Tate's split -/

lemma rpow_inv_d_sq {u : ℝ} (hu : 0 ≤ u) : (u ^ ((dq : ℝ)⁻¹)) ^ 2 = u ^ ((2 : ℝ) / dq) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  congr 1; push_cast; ring

/-- **The outer half is bounded** (uniformly for $0 \le s \le S$): there is $M$ with
$|z|^{n+2s}\Theta^0(z) \le M|z|^{-1}$ for $z$ in the fundamental set with $|z| > 1$. -/
theorem exists_outer_bound {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (S : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ClassGroup (𝓞 F), ∀ x ∈ fundamentalCone F, ∀ s : ℝ, 0 ≤ s → s ≤ S →
      1 < ideleNorm F x (classRep F c) →
        zetaIntegrand A I s x (classRep F c) ≤ ENNReal.ofReal (M * ideleNorm F x (classRep F c) ^ (-1 : ℝ)) := by
  obtain ⟨R, hR, hup⟩ := exists_cone_upper (F := F)
  have hd1 : 1 ≤ dq := Module.finrank_pos
  have key : ∀ c : ClassGroup (𝓞 F), ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ fundamentalCone F, ∀ s : ℝ, 0 ≤ s → s ≤ S →
      1 < ideleNorm F x (classRep F c) →
        zetaIntegrand A I s x (classRep F c) ≤ ENNReal.ofReal (M * ideleNorm F x (classRep F c) ^ (-1 : ℝ)) := by
    intro c
    set 𝔟 := classRep F c
    have hN𝔟 := idealNorm_pos F 𝔟
    set β := idealNorm F 𝔟 ^ ((dq : ℝ)⁻¹) / R ^ (dq - 1)
    have hβ : 0 < β := div_pos (Real.rpow_pos_of_pos hN𝔟 _) (pow_pos hR _)
    obtain ⟨C, δ, hC, hδ, hdec⟩ := thetaZero_decay hA (twist 𝔟 I) (m₀ := β ^ 2) (by positivity)
    obtain ⟨M', hM', hbd⟩ := exists_rpow_mul_exp_le (δ * β ^ 2) (by positivity) dq hd1 n S
    refine ⟨C * M', by positivity, fun x hx s hs0 hsS hz1 => ?_⟩
    set z := ideleNorm F x 𝔟
    have hN := fundamentalCone.norm_pos_of_mem hx
    have hz0 : 0 < z := one_pos.trans hz1
    have hNz : mixedEmbedding.norm x = z * idealNorm F 𝔟 := by
      simp only [z, ideleNorm]; field_simp
    -- the lower shape bound, in terms of `z`
    have hlow : ∀ v, z ^ ((dq : ℝ)⁻¹) * β ≤ normAtPlace v x := fun v => by
      have := cone_lower hR hup hx v
      rwa [hNz, Real.mul_rpow hz0.le hN𝔟.le, mul_div_assoc] at this
    set m := z ^ ((2 : ℝ) / dq) * β ^ 2
    have hm : ∀ v, m ≤ sqPlaces x v := fun v => by
      have h1 := hlow v
      have h0 : 0 ≤ z ^ ((dq : ℝ)⁻¹) * β := by positivity
      calc m = (z ^ ((dq : ℝ)⁻¹) * β) ^ 2 := by rw [mul_pow, rpow_inv_d_sq hz0.le]
        _ ≤ sqPlaces x v := pow_le_pow_left₀ h0 h1 2
    have hm0 : β ^ 2 ≤ m := by
      have : 1 ≤ z ^ ((2 : ℝ) / dq) := Real.one_le_rpow hz1.le (by positivity)
      nlinarith [sq_nonneg β]
    have hθ := hdec (sqPlaces x) m hm0 hm
    calc zetaIntegrand A I s x 𝔟
        ≤ ENNReal.ofReal (z ^ ((n : ℝ) + 2 * s)) * ENNReal.ofReal (C * Real.exp (-δ * m)) := by
          unfold zetaIntegrand; gcongr
      _ = ENNReal.ofReal (C * (z ^ ((n : ℝ) + 2 * s) * Real.exp (-((δ * β ^ 2) * z ^ ((2 : ℝ) / dq))))) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _)]
          congr 1
          simp only [m]
          ring_nf
      _ ≤ ENNReal.ofReal (C * (M' * z ^ (-1 : ℝ))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbd z hz1.le s hs0 hsS) hC)
      _ = ENNReal.ofReal (C * M' * z ^ (-1 : ℝ)) := by ring_nf
  choose M hM0 hM using key
  refine ⟨∑ c, M c, Finset.sum_nonneg fun c _ => hM0 c, fun c x hx s hs0 hsS hz1 => ?_⟩
  refine (hM c x hx s hs0 hsS hz1).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun c _ => hM0 c) (Finset.mem_univ c))
    (Real.rpow_nonneg (one_pos.trans hz1).le _)

/-- **The dual half is small near $|z| = 0$**: there is $M$ with $|z|^{2s}\Theta^{\#0}(z^{-1}) \le M|z|^{2/d}$ for $z$ in the
fundamental set with $|z| \le 1$ and $s \ge 0$. -/
theorem exists_inner_bound {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ClassGroup (𝓞 F), ∀ x ∈ fundamentalCone F, ∀ s : ℝ, 0 ≤ s →
      ideleNorm F x (classRep F c) ≤ 1 →
        ENNReal.ofReal (ideleNorm F x (classRep F c) ^ (2 * s)) *
            thetaDualZero A (twist (classRep F c) I) (fun v => 4 / sqPlaces x v) ≤
          ENNReal.ofReal (M * ideleNorm F x (classRep F c) ^ ((2 : ℝ) / dq)) := by
  obtain ⟨R, hR, hup⟩ := exists_cone_upper (F := F)
  have key : ∀ c : ClassGroup (𝓞 F), ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ fundamentalCone F, ∀ s : ℝ, 0 ≤ s →
      ideleNorm F x (classRep F c) ≤ 1 →
        ENNReal.ofReal (ideleNorm F x (classRep F c) ^ (2 * s)) *
            thetaDualZero A (twist (classRep F c) I) (fun v => 4 / sqPlaces x v) ≤
          ENNReal.ofReal (M * ideleNorm F x (classRep F c) ^ ((2 : ℝ) / dq)) := by
    intro c
    set 𝔟 := classRep F c
    have hN𝔟 := idealNorm_pos F 𝔟
    set β := R * idealNorm F 𝔟 ^ ((dq : ℝ)⁻¹)
    have hβ : 0 < β := mul_pos hR (Real.rpow_pos_of_pos hN𝔟 _)
    obtain ⟨C, δ, hC, hδ, hdec⟩ := thetaDualZero_decay hA (twist 𝔟 I) (m₀ := 4 / β ^ 2) (by positivity)
    refine ⟨C * β ^ 2 / (4 * δ), by positivity, fun x hx s hs0 hz1 => ?_⟩
    set z := ideleNorm F x 𝔟
    have hN := fundamentalCone.norm_pos_of_mem hx
    have hz0 : 0 < z := div_pos hN hN𝔟
    have hNz : mixedEmbedding.norm x = z * idealNorm F 𝔟 := by
      simp only [z, ideleNorm]; field_simp
    have hupz : ∀ v, normAtPlace v x ≤ β * z ^ ((dq : ℝ)⁻¹) := fun v => by
      have := hup x hx v
      rwa [hNz, Real.mul_rpow hz0.le hN𝔟.le, mul_comm (z ^ _), ← mul_assoc] at this
    have hzd : 0 < z ^ ((2 : ℝ) / dq) := Real.rpow_pos_of_pos hz0 _
    set m := 4 / (β ^ 2 * z ^ ((2 : ℝ) / dq))
    have hmpos : 0 < m := by positivity
    have hm : ∀ v, m ≤ 4 / sqPlaces x v := fun v => by
      have hpos := sqPlaces_pos hN v
      refine div_le_div_of_nonneg_left (by norm_num) hpos ?_
      calc sqPlaces x v = normAtPlace v x ^ 2 := rfl
        _ ≤ (β * z ^ ((dq : ℝ)⁻¹)) ^ 2 := pow_le_pow_left₀ (normAtPlace_nonneg _ _) (hupz v) 2
        _ = β ^ 2 * z ^ ((2 : ℝ) / dq) := by rw [mul_pow, rpow_inv_d_sq hz0.le]
    have hm0 : 4 / β ^ 2 ≤ m := by
      have : z ^ ((2 : ℝ) / dq) ≤ 1 := Real.rpow_le_one hz0.le hz1 (by positivity)
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      nlinarith [sq_nonneg β, pow_pos hβ 2]
    have hθ := hdec (fun v => 4 / sqPlaces x v) m hm0 hm
    have hz2s : z ^ (2 * s) ≤ 1 := Real.rpow_le_one hz0.le hz1 (by positivity)
    calc ENNReal.ofReal (z ^ (2 * s)) * thetaDualZero A (twist 𝔟 I) (fun v => 4 / sqPlaces x v)
        ≤ ENNReal.ofReal 1 * ENNReal.ofReal (C * Real.exp (-δ * m)) := by
          gcongr
      _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal (C * (δ * m)⁻¹) := by
          gcongr
          rw [neg_mul]
          exact exp_neg_le_inv (by positivity)
      _ = ENNReal.ofReal (C * β ^ 2 / (4 * δ) * z ^ ((2 : ℝ) / dq)) := by
          rw [ENNReal.ofReal_one, one_mul]
          congr 1
          simp only [m]
          field_simp
  choose M hM0 hM using key
  refine ⟨∑ c, M c, Finset.sum_nonneg fun c _ => hM0 c, fun c x hx s hs0 hz1 => ?_⟩
  refine (hM c x hx s hs0 hz1).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun c _ => hM0 c) (Finset.mem_univ c))
    (Real.rpow_nonneg (div_pos (fundamentalCone.norm_pos_of_mem hx) (idealNorm_pos F _)).le _)

/-! ### Tate's split and the residue -/

/-- The part of the integrand with $|z| > 1$ (Weil's $Z_+$). -/
def outerIntegrand (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ)
    (x : mixedSpace F) (𝔟 : FracIdeal F) : ℝ≥0∞ :=
  if 1 < ideleNorm F x 𝔟 then zetaIntegrand A I s x 𝔟 else 0

/-- The part of the integrand with $|z| \le 1$ (Weil's $Z_-$). -/
def innerIntegrand (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ)
    (x : mixedSpace F) (𝔟 : FracIdeal F) : ℝ≥0∞ :=
  if ideleNorm F x 𝔟 ≤ 1 then zetaIntegrand A I s x 𝔟 else 0

/-- **The dual boundary term** $B(s) = \int_{|z|\le1}|z|^{2s}\sum_{\mu\in(\mathfrak b^{-1}L)^\#\setminus0}\Psi(\mu z^{-1})\,d^\times z$, with
$\Psi(\mu z^{-1}) = \exp(-\pi\sum_v\varphi_v(Q^\#(\mu))\,4/|x_v|^2)$: Weil's $Z^\Psi_+(-s-\frac m2)$ before the substitution
$z \mapsto z^{-1}$ (§4.4, p. 97). -/
def dualTerm (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ideleClassLIntegral F fun x 𝔟 => if ideleNorm F x 𝔟 ≤ 1 then
    ENNReal.ofReal (ideleNorm F x 𝔟 ^ (2 * s)) * thetaDualZero A (twist 𝔟 I) (fun v => 4 / sqPlaces x v) else 0

lemma additiveZeta_eq_add (A : Matrix (Fin n) (Fin n) F) (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℝ) :
    additiveZeta A I s = ideleClassLIntegral F (innerIntegrand A I s) +
      ideleClassLIntegral F (outerIntegrand A I s) := by
  rw [← ideleClassLIntegral_add F]
  · unfold additiveZeta
    congr 1; funext x 𝔟
    unfold innerIntegrand outerIntegrand
    by_cases h1 : ideleNorm F x 𝔟 ≤ 1
    · simp [h1, not_lt.2 h1]
    · simp [h1, lt_of_not_ge h1]
  · intro 𝔟
    exact Measurable.ite (measurableSet_le (measurable_ideleNorm F 𝔟) measurable_const)
      (measurable_zetaIntegrand A I s 𝔟) measurable_const

/-- **$Z_+$ is bounded near $s = 0$** (for $0 \le s \le S$): Weil's "$Z_+(s)$ is an entire function" (p. 97), in the form
needed for the residue. -/
theorem exists_outer_le {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (S : ℕ) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ S → ideleClassLIntegral F (outerIntegrand A I s) ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM0, hM⟩ := exists_outer_bound hA I S
  refine ⟨M * dedekindZeta_residue F, fun s hs0 hsS => ?_⟩
  calc ideleClassLIntegral F (outerIntegrand A I s)
      ≤ ideleClassLIntegral F (fun x 𝔟 => ENNReal.ofReal M *
          (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-(1 : ℝ)))) (ideleNorm F x 𝔟)) := by
        refine ideleClassLIntegral_mono_cone F fun c x hx => ?_
        unfold outerIntegrand
        split_ifs with h1
        · rw [Set.indicator_of_mem (show ideleNorm F x (classRep F c) ∈ Ioi (1 : ℝ) from h1),
            ← ENNReal.ofReal_mul hM0]
          exact hM c x hx s hs0 hsS h1
        · exact zero_le
    _ = ENNReal.ofReal (M * dedekindZeta_residue F) := by
        rw [ideleClassLIntegral_const_mul F _ ENNReal.ofReal_ne_top, ideleClassLIntegral_gt_one_rpow_neg F one_pos,
          ← ENNReal.ofReal_mul hM0, div_one]

/-- **The dual boundary term is bounded** for $s \ge 0$. -/
theorem exists_dualTerm_le {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → dualTerm A I s ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM0, hM⟩ := exists_inner_bound hA I
  have hd : (0 : ℝ) < (2 : ℝ) / dq := div_pos two_pos (by exact_mod_cast Module.finrank_pos)
  refine ⟨M * (dedekindZeta_residue F / ((2 : ℝ) / dq)), fun s hs0 => ?_⟩
  calc dualTerm A I s
      ≤ ideleClassLIntegral F (fun x 𝔟 => ENNReal.ofReal M *
          (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ ((2 : ℝ) / dq))) (ideleNorm F x 𝔟)) := by
        refine ideleClassLIntegral_mono_cone F fun c x hx => ?_
        split_ifs with h1
        · rw [Set.indicator_of_mem (show ideleNorm F x (classRep F c) ∈ Iic (1 : ℝ) from h1),
            ← ENNReal.ofReal_mul hM0]
          exact hM c x hx s hs0 h1
        · exact zero_le
    _ = ENNReal.ofReal (M * (dedekindZeta_residue F / ((2 : ℝ) / dq))) := by
        rw [ideleClassLIntegral_const_mul F _ ENNReal.ofReal_ne_top, ideleClassLIntegral_le_one_rpow F hd,
          ← ENNReal.ofReal_mul hM0]

/-- **Tate's split with Poisson summation on the inner half** (Weil §4.4, p. 97, and (5), p. 98, in the anisotropic case,
before the substitution $z \mapsto z^{-1}$ in the dual term): for $s > 0$,
$$Z^-_L(s) + \frac{\rho_F}{n+2s} = \frac{c_L\,\rho_F}{2s} + c_L\,B(s),$$
$Z^-_L(s) = \int_{|z|\le1}|z|^{n+2s}\sum_{\xi\ne0}\Phi(\xi z)\,d^\times z$, $B$ = `dualTerm`. The terms $\rho_F/(n+2s)$ and $c_L\rho_F/(2s)$ are the
boundary terms from $\xi = 0$ and $\mu = 0$ ($\Phi(0) = 1$, $\hat\Phi(0) = c_L$); in the anisotropic case there are no others. -/
@[kb "weil1982" "§4.4, pp. 97–98 (Tate's split, Poisson summation, index 0, Thm 3.1.1 (iii))"]
theorem inner_add_eq {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 0 < s) :
    ideleClassLIntegral F (innerIntegrand A I s) + ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) =
      ENNReal.ofReal (latConst A I * dedekindZeta_residue F / (2 * s)) + ENNReal.ofReal (latConst A I) * dualTerm A I s := by
  have hc := latConst_pos hA I
  have hmeasIn : ∀ 𝔟, Measurable fun x => innerIntegrand A I s x 𝔟 := fun 𝔟 =>
    Measurable.ite (measurableSet_le (measurable_ideleNorm F 𝔟) measurable_const)
      (measurable_zetaIntegrand A I s 𝔟) measurable_const
  have hmeasInd : ∀ (a : ℝ) 𝔟, Measurable fun x =>
      (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) (ideleNorm F x 𝔟) := fun a 𝔟 =>
    ((measurable_id.pow_const a).ennreal_ofReal.indicator measurableSet_Iic).comp (measurable_ideleNorm F 𝔟)
  rw [← ideleClassLIntegral_le_one_rpow F (by positivity : (0 : ℝ) < n + 2 * s), ← ideleClassLIntegral_add F hmeasIn]
  have hstep : ideleClassLIntegral F (fun x 𝔟 => innerIntegrand A I s x 𝔟 +
      (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ ((n : ℝ) + 2 * s))) (ideleNorm F x 𝔟)) =
      ideleClassLIntegral F (fun x 𝔟 => ENNReal.ofReal (latConst A I) *
        ((Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (2 * s))) (ideleNorm F x 𝔟) +
          if ideleNorm F x 𝔟 ≤ 1 then ENNReal.ofReal (ideleNorm F x 𝔟 ^ (2 * s)) *
            thetaDualZero A (twist 𝔟 I) (fun v => 4 / sqPlaces x v) else 0)) := by
    refine ideleClassLIntegral_congr_cone F fun c x hx => ?_
    have hN := fundamentalCone.norm_pos_of_mem hx
    unfold innerIntegrand zetaIntegrand
    by_cases h1 : ideleNorm F x (classRep F c) ≤ 1
    · simp only [h1, ↓reduceIte]
      rw [Set.indicator_of_mem (show _ ∈ Iic (1 : ℝ) from h1),
        Set.indicator_of_mem (show _ ∈ Iic (1 : ℝ) from h1)]
      have hP := poisson_pointwise hA I s hN (classRep F c)
      rw [mul_add, mul_one, add_comm] at hP
      rw [hP, ENNReal.ofReal_mul hc.le]
      ring
    · simp only [h1, ↓reduceIte]
      rw [Set.indicator_of_notMem (show _ ∉ Iic (1 : ℝ) from h1),
        Set.indicator_of_notMem (show _ ∉ Iic (1 : ℝ) from h1)]
      simp
  rw [hstep, ideleClassLIntegral_const_mul F _ ENNReal.ofReal_ne_top, ideleClassLIntegral_add F (hmeasInd _),
    ideleClassLIntegral_le_one_rpow F (by positivity : (0 : ℝ) < 2 * s), mul_add, ← ENNReal.ofReal_mul hc.le,
    mul_div_assoc]
  rfl

/-- **Finiteness**: $Z^+_L(s) < \infty$ for every real $s > 0$ (Weil, p. 97: the integral (4) "is absolutely convergent for
$\mathrm{Re}(s) > 0$"; proved here directly from Tate's split). -/
@[kb "weil1982" "§4.4, p. 97 (absolute convergence of (4) for Re(s) > 0)"]
theorem additiveZeta_lt_top {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 0 < s) : additiveZeta A I s < ⊤ := by
  obtain ⟨M₁, hM₁⟩ := exists_outer_le hA I ⌈s⌉₊
  obtain ⟨M₂, hM₂⟩ := exists_dualTerm_le hA I
  have hin := inner_add_eq hA I hs
  rw [additiveZeta_eq_add]
  refine ENNReal.add_lt_top.2 ⟨?_, (hM₁ s hs.le (Nat.le_ceil s)).trans_lt ENNReal.ofReal_lt_top⟩
  have : ideleClassLIntegral F (innerIntegrand A I s) ≤
      ENNReal.ofReal (latConst A I * dedekindZeta_residue F / (2 * s)) + ENNReal.ofReal (latConst A I) * dualTerm A I s := by
    rw [← hin]; exact le_self_add
  refine this.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hM₂ s hs.le).trans_lt ENNReal.ofReal_lt_top)⟩)

/-- **The functional-equation form of Tate's split** (Weil's (5), p. 98, anisotropic case, before $z \mapsto z^{-1}$): for
real $s > 0$, with all four terms finite,
$$Z^+_L(s) = Z_+(s) + \frac{c_L\rho_F}{2s} + c_L\,B(s) - \frac{\rho_F}{n+2s},$$
$Z_+(s) = \int_{|z|>1}|z|^{n+2s}\sum_{\xi\ne0}\Phi(\xi z)\,d^\times z$ (`outerIntegrand`), $B(s)$ = `dualTerm`, $c_L = \hat\Phi(0) = \int\Phi$
(`latConst`), $\Phi(0) = 1$. -/
@[kb "weil1982" "§4.4, (5), p. 98 (index 0: only the boundary terms Ψ(0)/s − Φ(0)/(s+m/2)); §4.5, p. 109"]
theorem additiveZeta_toReal_eq {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 0 < s) :
    (additiveZeta A I s).toReal = (ideleClassLIntegral F (outerIntegrand A I s)).toReal +
      latConst A I * dedekindZeta_residue F / (2 * s) + latConst A I * (dualTerm A I s).toReal -
        dedekindZeta_residue F / (n + 2 * s) := by
  obtain ⟨M₁, hM₁⟩ := exists_outer_le hA I ⌈s⌉₊
  obtain ⟨M₂, hM₂⟩ := exists_dualTerm_le hA I
  have hO := (hM₁ s hs.le (Nat.le_ceil s)).trans_lt ENNReal.ofReal_lt_top
  have hB := (hM₂ s hs.le).trans_lt ENNReal.ofReal_lt_top
  have hin := inner_add_eq hA I hs
  have hc := latConst_pos hA I
  have hρ := dedekindZeta_residue_pos F
  have hIn : ideleClassLIntegral F (innerIntegrand A I s) < ⊤ := by
    have : ideleClassLIntegral F (innerIntegrand A I s) ≤
        ENNReal.ofReal (latConst A I * dedekindZeta_residue F / (2 * s)) +
          ENNReal.ofReal (latConst A I) * dualTerm A I s := by rw [← hin]; exact le_self_add
    exact this.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB⟩)
  have h1 := congrArg ENNReal.toReal hin
  rw [ENNReal.toReal_add hIn.ne ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB).ne, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hc.le] at h1
  rw [additiveZeta_eq_add, ENNReal.toReal_add hIn.ne hO.ne]
  linarith

/-- **The residue of the additive zeta function of a lattice** (Weil §4.4, p. 98, index 0: the residue is
$\tau(G)\Psi(0)\rho_k$ there, $\frac12\rho_k\tau(G)$ in §4.5 after the substitution $|t|^2$; here for one lattice, without the
$[SO]$-integral): for $n \ge 1$,
$$\lim_{s\to0^+}s\,Z^+_L(s) = \frac{\rho_F}{2}\,c_L,\qquad c_L = \Big(\prod_v\sqrt{\det\varphi_v(A)}\Big)^{-1}\Big(\prod_i\Delta(I_i)\Big)^{-1}
  = \hat\Phi(0) = \int_{V(\mathbb A)}\Phi\,dx,$$
$\rho_F$ = `dedekindZeta_residue F`, $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$, $dx$ the self-dual (Tamagawa) measure. *Proof:* Tate's
split at $|z| = 1$; the outer half $Z_+(s)$ and the dual term $B(s)$ stay bounded as $s \to 0^+$ (theta decay on the
fundamental cone), so only the boundary term $c_L\rho_F/(2s)$ contributes (`additiveZeta_toReal_eq`). Unconditional. -/
@[kb "weil1982" "§4.4, pp. 97–98 (residue τ(G)Ψ(0)ρ_k at s = 0, index 0); §4.5, p. 109 (residue ρ_kτ(G)/2)"]
theorem tendsto_mul_additiveZeta {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (I : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) :
    Tendsto (fun s => s * (additiveZeta A I s).toReal) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * latConst A I)) := by
  obtain ⟨M₁, hM₁⟩ := exists_outer_le hA I 1
  obtain ⟨M₂, hM₂⟩ := exists_dualTerm_le hA I
  have hc := latConst_pos hA I
  have hρ := dedekindZeta_residue_pos F
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set K := max M₁ 0 + latConst A I * max M₂ 0 + dedekindZeta_residue F
  have hK : Tendsto (fun s : ℝ => K * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => K * s) (𝓝 0) (𝓝 (K * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hK)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  have hs0 := hs.1
  rw [additiveZeta_toReal_eq hA I hs0]
  have hO : (ideleClassLIntegral F (outerIntegrand A I s)).toReal ≤ max M₁ 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((hM₁ s hs0.le (by simpa using hs.2.le)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hB : (dualTerm A I s).toReal ≤ max M₂ 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((hM₂ s hs0.le).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hO0 : 0 ≤ (ideleClassLIntegral F (outerIntegrand A I s)).toReal := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ (dualTerm A I s).toReal := ENNReal.toReal_nonneg
  have hfrac : s * (dedekindZeta_residue F / (n + 2 * s)) ≤ s * dedekindZeta_residue F := by
    refine mul_le_mul_of_nonneg_left (div_le_self hρ.le (by linarith)) hs0.le
  have hfrac0 : 0 ≤ s * (dedekindZeta_residue F / (n + 2 * s)) := by positivity
  have hexp : s * ((ideleClassLIntegral F (outerIntegrand A I s)).toReal +
      latConst A I * dedekindZeta_residue F / (2 * s) + latConst A I * (dualTerm A I s).toReal -
        dedekindZeta_residue F / (n + 2 * s)) - dedekindZeta_residue F / 2 * latConst A I =
      s * (ideleClassLIntegral F (outerIntegrand A I s)).toReal + s * (latConst A I * (dualTerm A I s).toReal) -
        s * (dedekindZeta_residue F / (n + 2 * s)) := by
    field_simp
    ring
  rw [norm_norm, hexp, Real.norm_eq_abs, abs_le]
  have h1 : s * (latConst A I * (dualTerm A I s).toReal) ≤ s * (latConst A I * max M₂ 0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hc.le) hs0.le
  have h2 : s * (ideleClassLIntegral F (outerIntegrand A I s)).toReal ≤ s * max M₁ 0 :=
    mul_le_mul_of_nonneg_left hO hs0.le
  have h3 : 0 ≤ s * (latConst A I * (dualTerm A I s).toReal) := by positivity
  have h4 : 0 ≤ s * (ideleClassLIntegral F (outerIntegrand A I s)).toReal := by positivity
  constructor <;> nlinarith

end QuadFormsKB.AdditiveZeta
