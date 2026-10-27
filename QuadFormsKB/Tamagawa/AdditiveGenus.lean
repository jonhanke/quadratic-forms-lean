import QuadFormsKB.Tamagawa.AdditiveZeta
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.HilbertModular.GenusTheta
import QuadFormsKB.Tamagawa.ZetaResidue

/-!
# Weil's additive zeta function of a genus and its residue $\rho_F\tau(SO)\hat\Phi(0)/2$

**Setting.** $F$ totally real, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n \ge 1$ variables with $Q = Q_0\otimes F$ totally
positive definite on $V = F^n$, $L = \mathcal O_F^n$, $G = SO(V)$, and the genus of $L$ free (`GenusFree`; proved when
$\mathcal O_F$ is a PID). $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ with the Gaussian $\Phi_\infty(y) = \exp(-\pi\sum_v\varphi_v(Q)(y_v))$.

**The unfolded orbit integral.** Weil's additive zeta function (§4.4, (4), p. 97; §4.5, p. 109) is
$$Z^+(s) = \int_{G_F\backslash G_{\mathbb A}}\int_{I_F/F^\times}|t|^{2s+n}\sum_{\xi\in V(F)\setminus0}\Phi(g^{-1}\xi t)\,d^\times t\,dg.$$
For totally definite $V$, $G_F\backslash G_{\mathbb A} = \bigsqcup_\alpha\Gamma_\alpha\backslash(G_\infty\times\alpha K)$ ($K = SO(\hat L)$, $G_\infty$
compact), and $g \mapsto \sum_\xi\Phi(g^{-1}\xi t)$ is right $G_\infty K$-invariant ($\Phi_\infty$ is $SO(V_\infty)$-invariant), so the
$G$-integral is the finite sum $\mu_{\mathrm{Tam}}(K)\sum_\alpha|\Gamma_\alpha|^{-1}(\cdots)(\alpha)$ — the combinatorial measure (`tauSO`). The
summand at $\alpha$ is the additive zeta function of the lattice $M = \alpha L$ ($\Phi(\alpha^{-1}\xi t) = \Phi_\infty(\xi t_\infty)\mathbf 1[\xi \in
\mathfrak b^{-1}M]$, $\mathfrak b$ the ideal of $t_f$), which depends only on the class of $M$. With
$\mathrm{dcMass}(SO) = 2\,\mathrm{Mass}$ (`mass_SO_eq_two_mul_mass`):
$$Z^+(s) = 2\,\mu_{\mathrm{Tam}}(K)\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{Z^+_M(s)}{|O(M)|}\qquad(\texttt{genusAdditiveZeta}),$$
$Z^+_M$ = `additiveZeta` of the Gram form $Q_\gamma(\eta) = Q(\gamma\eta)$ of $M = \gamma\mathcal O_F^n$ (`classForm`).

**Main results.**
* `tendsto_mul_genusAdditiveZeta` (**the additive residue**, unconditional): $\lim_{s\to0^+}sZ^+(s) = \frac{\rho_F}2\,\hat\Phi(0)\,\tau(SO)$,
  $\hat\Phi(0) = c_L = \int_{V(\mathbb A)}\Phi\,dx$ (`latConst`), $\tau(SO)$ = `tauSO`. This is Weil's "the residue of $Z(s)$ at
  $s = 0$ turns out to be $\rho_k\tau(G)/2$" (p. 109) for $\Phi$ with $\hat\Phi(0) = 1$, in the anisotropic case (p. 97: $\Sigma_k = \{0\}$).
* `SphericalFibration` (**input**, Weil p. 109 via Lemma 2.4.2 and Witt's theorem) and `ComplementTauTwo` (**input**, the
  induction hypothesis $\tau(G') = 2$), and the interface theorem `tendsto_mul_sphericalSum`:
  $\lim_{s\to0^+}s\sum_\rho Z(s,\rho) = \frac{\rho_F}2\,\hat\Phi(0)\,\tau(SO)$.

*Erratum (Weil 1982, p. 109, first display):* printed "$Z(s,\rho) = \frac12\int_{T(\rho)_A}|y|^{2s+m}\Phi(x)|y|^{-m}d'x =
\frac12\int_{\Gamma_A/\Gamma_k}(\cdots)$"; by (1), p. 102, and Lemma 2.4.2 (p. 26, (2), with $\mu_g = \tau(\Gamma') = 2$) the first
$\frac12$ must be absent: $Z(s,\rho) = \int_{T(\rho)_A}\cdots = \frac12\int_{\Gamma_A/\Gamma_k}\sum_{(M,\tau)}\cdots$. Only then does the next
display, $Z(s) = \int_{\Gamma_A/\Gamma_k}|t|^{2s+m}\sum_{F(\xi)\ne0}\Phi(X\xi t)$, follow from $Z(s) = \sum_\rho Z(s,\rho)$ ((2), p. 102, which has
no $\frac12$: the "2" in a text extraction of (2) is the exponent of $k^{*2}$).
-/

open NumberField NumberField.InfinitePlace Filter Topology Set
open scoped Real ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.AdditiveZeta

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### The Gram form of a class -/

open Classical in
/-- **The Gram form of a class** $c$ of lattices in $(F^n, Q_0\otimes F)$: if the representative `c.out` is free and integral,
$c.\mathrm{out} = \gamma\mathcal O_F^n$, the form $Q_\gamma(\eta) = Q(\gamma\eta)$ over $\mathcal O_F$ (`Lattices.gramZ`) for a chosen $\gamma$; otherwise
$Q_0$ (junk; never used for classes in a free genus). Its theta series is that of $c.\mathrm{out}$ (`thetaLatt_latOf`). -/
def classForm (Q₀ : QuadForm (𝓞 F) n) (c : LatClass (formF Q₀)) : QuadForm (𝓞 F) n :=
  if h : ∃ (γ : GL (Fin n) F) (_ : IsIntegral (formF Q₀) (latOf γ)), c.out.1 = latOf γ then
    gramZ (formF Q₀) h.choose h.choose_spec.choose else Q₀

lemma classForm_spec (Q₀ : QuadForm (𝓞 F) n) (hfree : GenusFree (formF Q₀) stdLat) {c : LatClass (formF Q₀)}
    (hc : c ∈ genusClasses (formF Q₀) stdLat) :
    ∃ (γ : GL (Fin n) F) (hi : IsIntegral (formF Q₀) (latOf γ)),
      SameGenus (formF Q₀) intVec (latOf γ) ∧ classForm Q₀ c = gramZ (formF Q₀) γ hi := by
  classical
  have hg := sameGenus_out hc
  obtain ⟨γ, hγ⟩ := hfree c.out hg
  have hex : ∃ (γ : GL (Fin n) F) (_ : IsIntegral (formF Q₀) (latOf γ)), c.out.1 = latOf γ :=
    ⟨γ, hγ ▸ SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hg, hγ⟩
  refine ⟨hex.choose, hex.choose_spec.choose, ?_, ?_⟩
  · rw [← hex.choose_spec.choose_spec]; exact hg
  · unfold classForm; simp only [hex, ↓reduceDIte]

/-- The Gram form of a class in the genus is in the genus of $Q_0$ and totally positive definite. -/
lemma classForm_props (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) {c : LatClass (formF Q₀)} (hc : c ∈ genusClasses (formF Q₀) stdLat) :
    FormSameGenus Q₀ (classForm Q₀ c) ∧ IsTotPosGram (gramF (classForm Q₀ c)) := by
  obtain ⟨γ, hi, hg, he⟩ := classForm_spec Q₀ hfree hc
  rw [he]
  exact ⟨formSameGenus_gramZ Q₀ hg hi, isTotPosGram_gramZ hpd γ hi⟩

/-- **$\hat\Phi(0)$ is the same for every class in the genus**: $c_M = c_L$ (the covolumes agree; `prod_sqrt_det_gramF_eq`). -/
lemma latConst_classForm (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) {c : LatClass (formF Q₀)} (hc : c ∈ genusClasses (formF Q₀) stdLat) :
    latConst (gramF (classForm Q₀ c)) (fun _ => 1) = latConst (gramF Q₀) (fun _ => 1) := by
  obtain ⟨hfs, hQc⟩ := classForm_props Q₀ hpd hfree hc
  unfold latConst
  rw [prod_sqrt_det_gramF_eq (isTotPosGram_Q₀ hpd) hQc hfs]

/-! ### The genus additive zeta function and its residue -/

/-- **Weil's additive zeta function of the genus** (§4.4, (4), p. 97; §4.5, p. 109; anisotropic case), with the
$SO(V)(F)\backslash SO(V)(\mathbb A)$-integral unfolded into the combinatorial double cosets:
$$Z^+(s) = 2\,\mu_{\mathrm{Tam}}(K_{SO})\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{Z^+_M(s)}{|O(M)|},\qquad
  Z^+_M(s) = \int_{I_F/F^\times}|z|^{n+2s}\sum_{\xi\in\mathfrak b^{-1}M\setminus0}\Phi_\infty(\xi z_\infty)\,d^\times z,$$
$\mu_{\mathrm{Tam}}(K_{SO})$ = `Tamagawa.tamagawaK`, $|O(M)|$ = `LatClass.autCard` (improper automorphisms included), $Z^+_M$ =
`additiveZeta` of the Gram form of $M$ (`classForm`), as a real number (finite for $s > 0$, `additiveZeta_lt_top`). The factor
$2\,\mathrm{Mass}$ is $\mathrm{dcMass}(SO(V)(F), SO(\hat L))$ (`mass_SO_eq_two_mul_mass`), so $2\mu_{\mathrm{Tam}}(K)\sum_M|O(M)|^{-1}f(M)$ is
the integral over $SO(V)(F)\backslash SO(V)(\mathbb A)$ of the class function $f$. Parameters: `Q₀` (the form), `s`. -/
@[kb "weil1982" "§4.4, (4), p. 97; §4.5, p. 109 (∫_{Γ_A/Γ_k}|t|^{2s+m}Σ_{F(ξ)≠0}Φ(Xξt)dX(dt/t)')"]
def genusAdditiveZeta (Q₀ : QuadForm (𝓞 F) n) (s : ℝ) : ℝ :=
  2 * Tamagawa.tamagawaK Q₀ * ∑ᶠ c ∈ genusClasses (formF Q₀) stdLat,
    (additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s).toReal / (LatClass.autCard (formF Q₀) c : ℝ)

/-- **The additive residue** (Weil 1982, §4.4, pp. 97–98, and §4.5, p. 109; anisotropic case): for $Q_0$ nondegenerate over
$\mathcal O_F$, $n \ge 1$, $Q_0\otimes F$ totally positive definite, and the genus of $\mathcal O_F^n$ free,
$$\lim_{s\to0^+}s\,Z^+(s) = \frac{\rho_F}{2}\,\hat\Phi(0)\,\tau(SO),$$
$\rho_F$ = `dedekindZeta_residue F`, $\hat\Phi(0) = c_L = \int_{V(\mathbb A)}\Phi\,dx = \big(\prod_v\sqrt{\det\varphi_v(A)}\big)^{-1}|d_F|^{-n/2}$
(`latConst`, $A = H/2$), $\tau(SO) = \mu_{\mathrm{Tam}}(K_{SO})\,\mathrm{dcMass}(SO(V)(F), SO(\hat L))$ (`Tamagawa.tauSO`). Weil normalizes
$\hat\Phi(0) = \Psi(0)$ and states the residue as $\rho_k\tau(G)/2$ (p. 109). *Unconditional:* no cited input; `GenusFree` is a scope
restriction (proved for $\mathcal O_F$ a PID). The proof sums the per-class residues `tendsto_mul_additiveZeta` (Tate's split
and theta inversion) with the combinatorial weights. -/
@[kb "weil1982" "§4.5, p. 109 (residue ρ_kτ(G)/2); §4.4, pp. 97–98 (index 0)"]
theorem tendsto_mul_genusAdditiveZeta (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 1 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) :
    Tendsto (fun s => s * genusAdditiveZeta Q₀ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * latConst (gramF Q₀) (fun _ => 1) * Tamagawa.tauSO Q₀)) := by
  have hfin := genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)
  set C := hfin.toFinset
  set c₀ := latConst (gramF Q₀) (fun _ => 1)
  have hsum : ∀ s, s * genusAdditiveZeta Q₀ s = 2 * Tamagawa.tamagawaK Q₀ * ∑ c ∈ C,
      s * (additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s).toReal / (LatClass.autCard (formF Q₀) c : ℝ) := by
    intro s
    rw [genusAdditiveZeta, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [hsum]
  have hlim : Tendsto (fun s => 2 * Tamagawa.tamagawaK Q₀ * ∑ c ∈ C,
      s * (additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s).toReal / (LatClass.autCard (formF Q₀) c : ℝ))
      (𝓝[>] 0) (𝓝 (2 * Tamagawa.tamagawaK Q₀ * ∑ c ∈ C,
        dedekindZeta_residue F / 2 * c₀ / (LatClass.autCard (formF Q₀) c : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun c hc => ?_)
    have hcg : c ∈ genusClasses (formF Q₀) stdLat := hfin.mem_toFinset.1 hc
    have h := tendsto_mul_additiveZeta (classForm_props Q₀ hpd hfree hcg).2 (fun _ => 1) hn
    rw [latConst_classForm Q₀ hpd hfree hcg] at h
    exact h.div_const _
  convert hlim using 2
  -- the constant: $2\mu\sum_c\frac{\rho c_0/2}{|O(c)|} = \frac{\rho}{2}c_0\cdot\mu\cdot2\,\mathrm{Mass} = \frac\rho2c_0\tau(SO)$
  have hmass : Tamagawa.tauSO Q₀ = Tamagawa.tamagawaK Q₀ * (2 * mass (formF Q₀) stdLat) := by
    rw [Tamagawa.tauSO, Tamagawa.mass_SO_eq_two_mul_mass Q₀ hQ (by omega) hpd (isIntegral_stdLat Q₀)]
  have hm : mass (formF Q₀) stdLat = ∑ c ∈ C, ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ := by
    rw [mass, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [hmass, hm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### $\hat\Phi(0) = c_L$ in the normalization of `GlobalZeta` -/

open MeasureTheory Matrix in
open scoped MatrixOrder in
/-- **The Gaussian integral of a positive definite form**: $\int_{\mathbb R^n}e^{-\pi x^{\mathsf T}Ax}\,dx = (\det A)^{-1/2}$. -/
theorem integral_exp_neg_pi_dotProduct {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∫ x : Fin n → ℝ, Real.exp (-π * (x ⬝ᵥ A *ᵥ x)) = (Real.sqrt A.det)⁻¹ := by
  set B := CFC.sqrt A
  have h0 : 0 ≤ A := (nonneg_iff_posSemidef).2 hA.posSemidef
  have hBB : B * B = A := CFC.sqrt_mul_sqrt_self A h0
  have hBt : Bᵀ = B := by
    have hsa : IsSelfAdjoint B := (CFC.sqrt_nonneg _).isSelfAdjoint
    simpa [Matrix.star_eq_conjTranspose] using hsa.star_eq
  have hdetB : B.det = Real.sqrt A.det := by
    rw [← hBB, det_mul, Real.sqrt_mul_self ((nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).det_nonneg)]
  have hdet0 : B.det ≠ 0 := by rw [hdetB]; exact (Real.sqrt_pos.2 hA.det_pos).ne'
  set L := Matrix.toLin' B
  have hL : LinearMap.det L ≠ 0 := by rw [LinearMap.det_toLin']; exact hdet0
  set g : (Fin n → ℝ) → ℝ := fun y => Real.exp (-π * ∑ i, y i ^ 2)
  have hcomp : ∀ x : Fin n → ℝ, Real.exp (-π * (x ⬝ᵥ A *ᵥ x)) = g (L x) := fun x => by
    simp only [g, L, Matrix.toLin'_apply]
    rw [sum_sq_mulVec, hBt, hBB]
  simp_rw [hcomp]
  have hg : Continuous g := by fun_prop
  rw [← integral_map L.continuous_of_finiteDimensional.measurable.aemeasurable
    hg.aestronglyMeasurable, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hL, integral_smul_measure]
  have hint : ∫ y : Fin n → ℝ, g y = 1 := by
    have : ∀ y : Fin n → ℝ, g y = ∏ i, Real.exp (-π * y i ^ 2) := fun y => by
      simp only [g]; rw [← Real.exp_sum, Finset.mul_sum]
    have hg1 : ∫ t : ℝ, Real.exp (-π * t ^ 2) = 1 := by
      rw [integral_gaussian, div_self Real.pi_pos.ne', Real.sqrt_one]
    simp_rw [this]
    rw [volume_pi, integral_fintype_prod_eq_prod (fun _ t => Real.exp (-π * t ^ 2))]
    simp only [hg1, Finset.prod_const_one]
  rw [hint, LinearMap.det_toLin', hdetB, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_inv, abs_of_pos (Real.sqrt_pos.2 hA.det_pos)]

open Matrix in
/-- $Q_w(x) = x^{\mathsf T}\varphi_w(A)x$ at a real place, $A = H/2$ (`gramF`). -/
lemma realVal_eq_dotProduct (Q₀ : QuadForm (𝓞 F) n) (w : Siegel.RealPlace F) (x : Fin n → ℝ) :
    GlobalZeta.realVal Q₀ w x = x ⬝ᵥ ((gramF Q₀).map (realEmb F w.1)) *ᵥ x := by
  set f : 𝓞 F →+* ℝ := (realEmb F w.1).comp (algebraMap (𝓞 F) F)
  have hσ : Siegel.realEmb w = realEmb F w.1 := rfl
  unfold GlobalZeta.realVal Siegel.realForm
  rw [QuadForm.evalIn_eq_dotProduct, hσ]
  have hC : ((Q₀.map f).coeff.map (algebraMap ℝ ℝ)) = Q₀.coeff.map f := by
    ext i j; simp [QuadForm.map]
  have hG : (gramF Q₀).map (realEmb F w.1) = (1 / 2 : ℝ) • (Q₀.coeff.map f + (Q₀.coeff.map f)ᵀ) := by
    ext i j
    simp [gramF, QuadForm.hessian, f, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, map_ofNat]
  rw [hC, hG, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  have : x ⬝ᵥ (Q₀.coeff.map f)ᵀ *ᵥ x = x ⬝ᵥ (Q₀.coeff.map f) *ᵥ x := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [this, smul_eq_mul]
  ring

open Classical in
/-- **$\hat\Phi(0) = c_L$ is the $\int_{V(\mathbb A)}\Phi\,dx$ of `GlobalZeta`** for the Gaussian
$\Phi_w = e^{-\pi Q_w}$ (`GlobalZeta.gaussian Q₀ π`):
$$\int_{V(\mathbb A)}\Phi\,dx = |d_F|^{-n/2}\prod_w\int_{\mathbb R^n}e^{-\pi Q_w(x)}dx = |d_F|^{-n/2}\prod_w(\det\varphi_w(A))^{-1/2} = c_L.$$ -/
@[kb "weil1982" "§2.1.3, pp. 12–13 (self-dual measure, μ_k = |Δ_k|^{1/2}); the Gaussian integral"]
theorem phiIntegral_gaussian_pi (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotPosGram (gramF Q₀)) :
    GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π) = latConst (gramF Q₀) (fun _ => 1) := by
  rw [GlobalZeta.phiIntegral_eq, latConst]
  have hw : ∀ w : Siegel.RealPlace F, ∫ x, GlobalZeta.gaussian Q₀ π w x =
      (Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det)⁻¹ := fun w => by
    simp only [GlobalZeta.gaussian]
    simp_rw [realVal_eq_dotProduct]
    exact integral_exp_neg_pi_dotProduct (hpd w.1)
  simp_rw [hw]
  rw [← Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  have he : ∏ w : Siegel.RealPlace F, Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det =
      ∏ v : InfinitePlace F, Real.sqrt ((gramF Q₀).map (realEmb F v)).det :=
    Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => rfl
  rw [he]
  simp only [embDet_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hd := discr_pos (F := F)
  rw [abs_of_pos hd, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le, ← Real.rpow_neg hd.le,
    Finset.prod_inv_distrib]
  ring_nf

/-- **The additive residue in the normalization of `GlobalZeta`**: $\lim_{s\to0^+}sZ^+(s) = \frac{\rho_F}2\,\tau(SO)\int_{V(\mathbb A)}\Phi\,dx$ for the
Gaussian $\Phi_w = e^{-\pi Q_w}$, with $\int\Phi$ = `GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π)`, the quantity in
`tendsto_mul_globalZeta_zero_gaussian` ($\lim sZ_{\rm mult}(s) = \rho_F\int\Phi$). Unconditional (scope: `GenusFree`). -/
@[kb "weil1982" "§4.5, p. 109 (residue ρ_kτ(G)/2, Φ̂(0) = ∫Φ); cf. (8), p. 108"]
theorem tendsto_mul_genusAdditiveZeta_phiIntegral (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 1 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) :
    Tendsto (fun s => s * genusAdditiveZeta Q₀ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * Tamagawa.tauSO Q₀ *
        GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π))) := by
  rw [phiIntegral_gaussian_pi Q₀ (isTotPosGram_Q₀ hpd)]
  convert tendsto_mul_genusAdditiveZeta Q₀ hQ hn hpd hfree using 2
  ring

/-- **The additive residue for $h_F = 1$** (no scope hypothesis): if $\mathcal O_F$ is a principal ideal domain, then for $Q_0$
nondegenerate, $n \ge 1$, $Q_0\otimes F$ totally positive definite, $\lim_{s\to0^+}sZ^+(s) = \frac{\rho_F}2\,\tau(SO)\int_{V(\mathbb A)}\Phi\,dx$
(`genusFree_of_isPrincipalIdealRing`). -/
@[kb "weil1982" "§4.5, p. 109 (residue ρ_kτ(G)/2); §4.4, pp. 97–98 (index 0)"]
theorem tendsto_mul_genusAdditiveZeta_of_pid [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hn : 1 ≤ n) (hpd : IsTotallyPosDef (formF Q₀)) :
    Tendsto (fun s => s * genusAdditiveZeta Q₀ s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * Tamagawa.tauSO Q₀ *
        GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π))) :=
  tendsto_mul_genusAdditiveZeta_phiIntegral Q₀ hQ hn hpd (genusFree_of_isPrincipalIdealRing _ _)

/-! ### The interface: Weil's fibration over the spheres and the induction hypothesis -/

/-- **Input (Weil 1982, §4.5, p. 109: Lemma 2.4.2 for $\Gamma = G\times\mathbb G_m$ acting on $T(\rho)$, and Witt's theorem).** Let
$\iota$ index a full set of representatives $\rho_i$ of $F^\times/F^{\times2}$ with $T(\rho_i)(F) \ne \emptyset$, $Z_i(s) = Z(s,\rho_i) =
\int_{T(\rho_i)_{\mathbb A}}|y|^{2s}\Phi(x)\,d'x$ the spherical zeta functions ((1), p. 102), and $\tau'_i = \tau(G'_i)$ the Tamagawa
number of the stabilizer $G'_i = SO(\xi_i^\perp)$ of a vector $\xi_i$ with $Q(\xi_i) = \rho_i$. Weil's unfolding states, for $s > 0$,
$$\int_{\Gamma_{\mathbb A}/\Gamma_k}|t|^{2s+m}\sum_{F(\xi)\in\rho_ik^{*2}}\Phi(X\xi t) = \frac{\tau'_i}{2}\,Z(s,\rho_i)$$
($\Gamma_k$ acts transitively on $T(\rho_i)(k)$ with stabilizer $G'_i\times\{1\}$; $\xi = M\xi_i\tau$ runs **twice** through
$\{F(\xi)\in\rho_ik^{*2}\}$), and summing over $i$: $Z^+(s) = \sum_i\frac{\tau'_i}{2}Z(s,\rho_i)$ with $Z^+$ = `genusAdditiveZeta`.
Fields: `summable` (the series converges) and `unfold` (the identity). *Not formalized:* the Tamagawa measures on $T(\rho)_{\mathbb A}$,
$G'_{\mathbb A}$ and their matching (Weil, Theorem 2.4.3); this structure records the identity. It says nothing about $\tau(G)$. -/
@[kb "weil1982" "§4.5, p. 109 (Lemma 2.4.2 on T(ρ), Witt's theorem Lemma 4.1.3; ξ runs twice); Lemma 2.4.2, p. 26"]
structure SphericalFibration (Q₀ : QuadForm (𝓞 F) n) {ι : Type*} (Z : ι → ℝ → ℝ) (τ' : ι → ℝ) : Prop where
  /-- $\sum_i\frac{\tau'_i}2Z(s,\rho_i)$ converges for $s > 0$. -/
  summable : ∀ s, 0 < s → Summable fun i => τ' i / 2 * Z i s
  /-- Weil's unfolding: $Z^+(s) = \sum_i\frac{\tau'_i}2Z(s,\rho_i)$ for $s > 0$. -/
  unfold : ∀ s, 0 < s → genusAdditiveZeta Q₀ s = ∑' i, τ' i / 2 * Z i s

/-- **Input: the induction hypothesis** $\tau(G'_i) = 2$ for the stabilizers $G'_i = SO(\xi_i^\perp)$, orthogonal groups in $n - 1$
variables (Weil, §4.5, p. 108: "By Lemma 4.1.1 and the induction assumption … $\tau(G') = 2$"). For a free complement
$\xi_i^\perp \cap M = \gamma\mathcal O_F^{n-1}$ with form $Q'_i$ this is `TamagawaNumberTwo Q'_i` in rank $n - 1$; it is a statement about
groups of smaller dimension, not about $\tau(SO(V))$. Field: `eq_two`. -/
@[kb "weil1982" "§4.5, p. 108 (τ(G') = 2 by the induction assumption)"]
structure ComplementTauTwo {ι : Type*} (τ' : ι → ℝ) : Prop where
  /-- $\tau(G'_i) = 2$ for every $i$. -/
  eq_two : ∀ i, τ' i = 2

/-- **The additive calculation, interface form** (Weil, §4.5, p. 109: "the residue of $Z(s)$ at $s = 0$ turns out to be
$\rho_k\tau(G)/2$"): given Weil's fibration over the spheres (`SphericalFibration`) and the induction hypothesis
(`ComplementTauTwo`), the spherical sum $Z(s) = \sum_\rho Z(s,\rho)$ ((2), p. 102) satisfies
$$\lim_{s\to0^+}s\,\sum_iZ(s,\rho_i) = \frac{\rho_F}2\,\tau(SO)\int_{V(\mathbb A)}\Phi\,dx,$$
$\int_{V(\mathbb A)}\Phi\,dx = \hat\Phi(0) = c_L$ = `GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π)` (the normalization of `GlobalZeta`,
`phiIntegral_gaussian_pi`).
**Use:** combine with the multiplicative residue of the same spherical sum,
$\lim sZ(s) = \rho_F\int\Phi\,dx$ ((8), p. 108:
`tendsto_mul_globalZeta_zero` for $\int_{V_{\mathbb A}}$, transferred to $\sum_\rho Z(s,\rho)$ by `SphericalResidue.lean`), and $\rho_F > 0$, $c_L > 0$, to get
$\tau(SO) = 2$. -/
@[kb "weil1982" "§4.5, p. 109 (additive calculation; residue ρ_kτ(G)/2)"]
theorem tendsto_mul_sphericalSum (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 1 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) {ι : Type*} {Z : ι → ℝ → ℝ}
    {τ' : ι → ℝ} (hfib : SphericalFibration Q₀ Z τ') (htwo : ComplementTauTwo τ') :
    Tendsto (fun s => s * ∑' i, Z i s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F / 2 * Tamagawa.tauSO Q₀ * GlobalZeta.phiIntegral (GlobalZeta.gaussian Q₀ π))) := by
  refine (tendsto_mul_genusAdditiveZeta_phiIntegral Q₀ hQ hn hpd hfree).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hfib.unfold s hs]
  congr 1
  refine tsum_congr fun i => ?_
  rw [htwo.eq_two i]
  ring


end QuadFormsKB.AdditiveZeta
