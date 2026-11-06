/-
# Siegel's $\Phi$ operator on the Siegel Eisenstein series: $\Phi E^{(r+1)} = E^{(r)}$ (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$ (all finite places, dyadic included, and all real places).

**Setting.** As in `EisensteinBigCell.lean`: $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F$ totally positive, $n = 2m$ (0-based indices),
$\Phi_v = \mathbf 1_{L_v^r}$ at every finite place, $s_0 = m - \frac{r+1}2$. The **holomorphic Eisenstein series of degree $r$**
$$\mathcal E^{(r)}(Z) = \det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}j(\gamma, Z)^{-m}f_f(\gamma, s_0)$$
(`eisHolR`, terms `holQ`; $j(\gamma, Z) = \prod_w\det(\sigma_w(C)Z_w + \sigma_w(D))$). The new variable of $\Phi$ has index $0$:
$Z \oplus it = \operatorname{diag}(it, Z)$ (`blockZ`).

**Results.**
* `eisensteinR_eq_prodIm_mul`: $E^{(r)}(g_Z, s_0, \Phi) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\mathcal E^{(r)}(Z)$.
* `denR_embSp_blockZ`: $j(\iota(\delta), Z \oplus it) = j(\delta, Z)$; `finSecR_embSp`: $f_f^{(r+1)}(\iota(\delta), s_0) = f_f^{(r)}(\delta, s_0)$
  (place by place, `secRV_oneSG_embSp`).
* **`tendsto_eisHolR_blockZ`** ($\Phi\mathcal E^{(r+1)} = \mathcal E^{(r)}$): for $Z \in \mathbb H_r^d$ and $m > 4(r+1)^2$,
  $\mathcal E^{(r+1)}(Z \oplus it) \to \mathcal E^{(r)}(Z)$ as $t \to \infty$. *Proof* (Klingen): dominated convergence over
  $P(F)\backslash\mathrm{Sp}_{2r+2}(F)$; each $|j(\gamma, Z\oplus it)|$ is nondecreasing in $t$ (`PhiArch.monotoneOn_norm_det`), so the terms at $t = 1$
  dominate (absolutely summable, `summable_norm_eisTermR`); a term with nonzero column $0$ of $C$ tends to $0$
  (`PhiArch.tendsto_norm_det`), and the other cosets are the $P\iota(\delta)$ (`colZeroEquiv`), whose terms are constant, equal to
  the terms of $\mathcal E^{(r)}(Z)$.

Sources: Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 (the $\Phi$ operator on Eisenstein series)
[unverified]; Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinBigCell
import QuadFormsKB.SiegelWeil.Forms.ThetaPhi
import QuadFormsKB.SiegelWeil.Forms.PhiArch
import QuadFormsKB.SiegelWeil.Forms.PhiCoset
import QuadFormsKB.SiegelWeil.Forms.PhiLocal
import QuadFormsKB.SiegelWeil.Forms.EisensteinSLInv
import QuadFormsKB.SiegelWeil.Forms.SingularCoeff

open Matrix NumberField IsDedekindDomain Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The holomorphic Eisenstein series -/

variable (m) in
/-- $\prod_w\det(\operatorname{Im}Z_w)^{m/2}$. -/
def prodIm (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∏ w, ((((Z w).map Complex.im).det : ℝ) : ℂ) ^ ((m : ℂ) / 2)

lemma prodIm_ne_zero {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) : prodIm m Z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => (det_im_pos hZ w).ne' (by exact_mod_cast h.1)

/-- The term $j(\gamma, Z)^{-m}f_f(\gamma, s_0)$. -/
def holTermR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (γ : Sp r F) : ℂ :=
  denR γ Z ^ (-(m : ℤ)) * finSecR (unitsOfInt b hb) (fun v => oneSG v m r) γ (sZero m r)

lemma eisTermR_mk (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (γ : Sp r F) :
    eisTermR b hb hbpos Z (Quotient.mk _ γ) = prodIm m Z * holTermR b hb Z γ := by
  show globalSecR _ _ _ _ γ = _
  unfold globalSecR archSecR holTermR prodIm
  rw [sZero_add_rhoR, sub_self, Complex.cpow_zero, mul_one, mul_assoc]

/-- The term of $\mathcal E^{(r)}(Z)$ at a coset (well defined for $Z \in \mathbb H_r^d$, `holQ_mk`). -/
def holQ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (q : PQuot r F) : ℂ :=
  eisTermR b hb hbpos Z q / prodIm m Z

lemma holQ_mk (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (γ : Sp r F) :
    holQ b hb hbpos Z (Quotient.mk _ γ) = holTermR b hb Z γ := by
  rw [holQ, eisTermR_mk, mul_div_cancel_left₀ _ (prodIm_ne_zero hZ)]

/-- **The holomorphic Siegel Eisenstein series of degree $r$**, $\mathcal E^{(r)}(Z) = \sum_{\gamma}j(\gamma, Z)^{-m}f_f(\gamma, s_0)$. -/
def eisHolR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑' q, holQ b hb hbpos Z q

/-- $E^{(r)}(g_Z, s_0, \Phi) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\,\mathcal E^{(r)}(Z)$. -/
theorem eisensteinR_eq_prodIm_mul (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
        (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) = prodIm m Z * eisHolR b hb hbpos Z := by
  show ∑' q, eisTermR b hb hbpos Z q = _
  rw [eisHolR, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [holQ, mul_div_cancel₀ _ (prodIm_ne_zero hZ)]

lemma summable_norm_holQ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (hm : 4 * (r : ℝ) ^ 2 < m) :
    Summable fun q => ‖holQ b hb hbpos Z q‖ := by
  have h := (summable_norm_eisTermR b hb hbpos hr hZ hm).div_const ‖prodIm m Z‖
  refine h.congr fun q => ?_
  rw [holQ, norm_div]

/-! ### The embedded cosets -/

lemma extC_map {k k' : Type*} [Field k] [Field k'] (f : k → k') (hf : f 0 = 0) (c : k) (X : Matrix (Fin r) (Fin r) k) :
    (extC c X).map f = extC (f c) (X.map f) :=
  extC_ext (by simp) (by simp [hf]) (by simp [hf]) (by simp)

lemma blockZ_eq_extC (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (w : InfinitePlace F) :
    blockZ Z t w = extC (Complex.I * t) (Z w) := rfl

lemma denW_embSp_blockZ (δ : Sp r F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (w : InfinitePlace F) :
    denW (embSp δ) (blockZ Z t) w = extC 1 (denW δ Z w) := by
  rw [denW, denW, blockC_embSp, blockD_embSp, blockZ_eq_extC, extC_map _ (by simp), extC_map _ (by simp),
    extC_mul, extC_add]
  simp

/-- $j(\iota(\delta), Z \oplus it) = j(\delta, Z)$. -/
lemma denR_embSp_blockZ (δ : Sp r F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) :
    denR (embSp δ) (blockZ Z t) = denR δ Z := by
  unfold denR
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [denW_embSp_blockZ, det_extC, one_mul]

lemma locSp_embSp {k k' : Type*} [Field k] [Field k'] (ι : k →+* k') (g : Sp r k) :
    locSp ι (embSp g) = embSp (locSp ι g) := by
  apply Subtype.ext
  rw [locSp_coe, embSp_coe, embSp_coe, locSp_coe, embMat, embMat, fromBlocks_map]
  simp only [extC_map _ (map_zero ι), map_one, map_zero]
  rfl

/-- $f_f^{(r+1)}(\iota(\delta), s_0) = f_f^{(r)}(\delta, s_0)$ (the lattice function at every finite place). -/
lemma finSecR_embSp (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (δ : Sp r F) :
    finSecR (unitsOfInt b hb) (fun v => oneSG v m (r + 1)) (embSp δ) (sZero m (r + 1)) =
      finSecR (unitsOfInt b hb) (fun v => oneSG v m r) δ (sZero m r) := by
  rw [finSecR_sZero, finSecR_sZero]
  congr 1; funext v
  rw [locSp_embSp, secRV_oneSG_embSp]

lemma holTermR_embSp_blockZ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (δ : Sp r F)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) :
    holTermR b hb (blockZ Z t) (embSp δ) = holTermR b hb Z δ := by
  rw [holTermR, holTermR, denR_embSp_blockZ, finSecR_embSp]

/-! ### The real places -/

/-- $\sigma_w(C_\gamma)$. -/
abbrev realC (γ : Sp r F) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℝ := (blockC γ).map (realEmb F w)
/-- $\sigma_w(D_\gamma)$. -/
abbrev realD (γ : Sp r F) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℝ := (blockD γ).map (realEmb F w)

lemma realCD_sym (γ : Sp r F) (w : InfinitePlace F) : realC γ w * (realD γ w)ᵀ = realD γ w * (realC γ w)ᵀ := by
  have h := congrArg (RingHom.mapMatrix (realEmb F w)) (blockC_mul_blockD_transpose γ)
  simpa [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] using h

lemma realCD_rank (γ : Sp r F) (w : InfinitePlace F) (u : Fin r → ℝ) (hC : u ᵥ* realC γ w = 0)
    (hD : u ᵥ* realD γ w = 0) : u = 0 := by
  set G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℝ := (γ : Matrix _ _ F).map (realEmb F w)
  set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℝ := ((γ⁻¹ : Sp r F) : Matrix _ _ F).map (realEmb F w)
  have hGN : G * N = 1 := by
    have e : ((γ * γ⁻¹ : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 := by
      rw [mul_inv_cancel]; rfl
    rw [← Matrix.map_mul]
    rw [show (γ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) * ((γ⁻¹ : Sp r F) : Matrix _ _ F) = 1 from e,
      Matrix.map_one _ (map_zero _) (map_one _)]
  set x : Fin r ⊕ Fin r → ℝ := Sum.elim 0 u
  have hx : x ᵥ* G = 0 := by
    funext y
    cases y with
    | inl j =>
      have := congrFun hC j
      simpa [x, vecMul, dotProduct, Fintype.sum_sum_type, G, blockC, Matrix.toBlocks₂₁] using this
    | inr j =>
      have := congrFun hD j
      simpa [x, vecMul, dotProduct, Fintype.sum_sum_type, G, blockD, Matrix.toBlocks₂₂] using this
  have hx0 : x = 0 := by
    have := congrArg (fun y => y ᵥ* N) hx
    simpa [vecMul_vecMul, hGN] using this
  funext i
  have := congrFun hx0 (Sum.inr i)
  simpa [x] using this

lemma denW_eq_W (γ : Sp (r + 1) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (w : InfinitePlace F) :
    denW γ (blockZ Z t) w = PhiArch.W (realC γ w) (realD γ w) (PhiArch.zt (Z w) t) := rfl

lemma norm_det_pos (γ : Sp (r + 1) F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    {t : ℝ} (ht : 0 < t) (w : InfinitePlace F) : 0 < ‖(denW γ (blockZ Z t) w).det‖ := by
  rw [norm_pos_iff, denW_eq_W]
  exact PhiArch.det_ne_zero (realCD_sym γ w) (realCD_rank γ w) (blockZ_mem hZ ht w)

/-- **Monotonicity in $t$**: $\lVert j(\gamma, Z \oplus i)\rVert \le \lVert j(\gamma, Z \oplus it)\rVert$ for $t \ge 1$. -/
lemma norm_denR_mono (γ : Sp (r + 1) F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    {t : ℝ} (ht : 1 ≤ t) : ‖denR γ (blockZ Z 1)‖ ≤ ‖denR γ (blockZ Z t)‖ := by
  unfold denR
  rw [norm_prod, norm_prod]
  gcongr with w hw
  rw [denW_eq_W, denW_eq_W]
  exact PhiArch.monotoneOn_norm_det (realCD_sym γ w) (realCD_rank γ w) (hZ w) (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (by linarith)) (by exact_mod_cast ht)

/-- **Decay**: if column $0$ of $C_\gamma$ is nonzero, $\lVert j(\gamma, Z \oplus it)\rVert \to \infty$. -/
lemma tendsto_norm_denR (γ : Sp (r + 1) F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    (hγ : ¬IsColZero γ) : Tendsto (fun t : ℝ => ‖denR γ (blockZ Z t)‖) atTop atTop := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, blockC γ i 0 ≠ 0 := by
    by_contra h; push Not at h; exact hγ h
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hc : ∀ w, ∃ i, realC γ w i 0 ≠ 0 := fun w => ⟨i, by simpa using hi⟩
  have h0 : Tendsto (fun t : ℝ => ‖(denW γ (blockZ Z t) w0).det‖) atTop atTop := by
    simp only [denW_eq_W]
    exact PhiArch.tendsto_norm_det (realCD_sym γ w0) (realCD_rank γ w0) (hZ w0) (hc w0)
  set c : ℝ := ∏ w ∈ Finset.univ.erase w0, ‖(denW γ (blockZ Z 1) w).det‖
  have hcpos : 0 < c := Finset.prod_pos fun w _ => norm_det_pos γ hZ one_pos w
  refine tendsto_atTop_mono' atTop ?_ (h0.atTop_mul_const hcpos)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  unfold denR
  rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  show ∏ w ∈ Finset.univ.erase w0, ‖(denW γ (blockZ Z 1) w).det‖ ≤ _
  gcongr with w hw
  rw [denW_eq_W, denW_eq_W]
  exact PhiArch.monotoneOn_norm_det (realCD_sym γ w) (realCD_rank γ w) (hZ w) (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (by linarith)) (by exact_mod_cast ht)

lemma norm_denR_pos (γ : Sp (r + 1) F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    {t : ℝ} (ht : 0 < t) : 0 < ‖denR γ (blockZ Z t)‖ := by
  unfold denR
  rw [norm_prod]
  exact Finset.prod_pos fun w _ => norm_det_pos γ hZ ht w

/-! ### $\Phi\mathcal E^{(r+1)} = \mathcal E^{(r)}$ -/

/-- **Siegel's $\Phi$ operator on the Siegel Eisenstein series** (Klingen): for $Z \in \mathbb H_r^d$ and $m > 4(r+1)^2$,
$\mathcal E^{(r+1)}(Z \oplus it) \to \mathcal E^{(r)}(Z)$ as $t \to \infty$, i.e. $\Phi\mathcal E^{(r+1)} = \mathcal E^{(r)}$. -/
@[kb "klingen1990" "§5 (Φ of the Siegel Eisenstein series is the Eisenstein series of lower degree) [unverified]"]
theorem tendsto_eisHolR_blockZ (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    (hm : 4 * ((r : ℝ) + 1) ^ 2 < m) :
    Tendsto (fun t : ℝ => eisHolR (r := r + 1) b hb hbpos (blockZ Z t)) atTop (𝓝 (eisHolR b hb hbpos Z)) := by
  classical
  have hm1 : 1 ≤ m := by
    by_contra h; push Not at h
    have : (m : ℝ) < 1 := by exact_mod_cast h
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  set g : PQuot (r + 1) F → ℂ := fun q =>
    if h : IsColZeroQ q then holQ b hb hbpos Z (colZeroEquiv.symm ⟨q, h⟩) else 0 with hg
  have hZ1 := blockZ_mem hZ one_pos
  have hsum := summable_norm_holQ b hb hbpos (r := r + 1) (Nat.le_add_left 1 r) hZ1 (by push_cast; exact hm)
  have hlim : ∀ q, Tendsto (fun t : ℝ => holQ b hb hbpos (blockZ Z t) q) atTop (𝓝 (g q)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h γ =>
      by_cases hγ : IsColZero γ
      · obtain ⟨δ, hδ⟩ := exists_embSp_rel γ hγ
        have hq : (Quotient.mk _ γ : PQuot (r + 1) F) = Quotient.mk _ (embSp δ) := (Quotient.sound hδ).symm
        rw [hq]
        have hgq : g (Quotient.mk _ (embSp δ)) = holQ b hb hbpos Z (Quotient.mk _ δ) := by
          have hc : IsColZeroQ (Quotient.mk _ (embSp δ) : PQuot (r + 1) F) := isColZero_embSp δ
          simp only [hg, hc, ↓reduceDIte]
          congr 1
          rw [Equiv.symm_apply_eq]
          exact Subtype.ext (colZeroEquiv_apply δ).symm
        rw [hgq, holQ_mk b hb hbpos hZ]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        rw [holQ_mk b hb hbpos (blockZ_mem hZ ht), holTermR_embSp_blockZ]
      · have hgq : g (Quotient.mk _ γ) = 0 := by
          have hc : ¬IsColZeroQ (Quotient.mk _ γ : PQuot (r + 1) F) := hγ
          simp only [hg, hc, ↓reduceDIte]
        rw [hgq]
        have hinv : Tendsto (fun t : ℝ => ‖denR γ (blockZ Z t)‖⁻¹ ^ m) atTop (𝓝 0) := by
          have := (tendsto_inv_atTop_zero.comp (tendsto_norm_denR γ hZ hγ)).pow m
          rwa [zero_pow (by omega)] at this
        have hn : Tendsto (fun t : ℝ => holTermR b hb (blockZ Z t) γ) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have h2 := hinv.mul_const ‖finSecR (unitsOfInt b hb) (fun v => oneSG v m (r + 1)) γ (sZero m (r + 1))‖
          rw [zero_mul] at h2
          refine h2.congr fun t => ?_
          rw [holTermR, norm_mul, norm_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
        refine hn.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        rw [holQ_mk b hb hbpos (blockZ_mem hZ ht)]
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ q, ‖holQ b hb hbpos (blockZ Z t) q‖ ≤ ‖holQ b hb hbpos (blockZ Z 1) q‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht q
    induction q using Quotient.inductionOn with
    | h γ =>
      rw [holQ_mk b hb hbpos (blockZ_mem hZ (by linarith)), holQ_mk b hb hbpos hZ1, holTermR, holTermR, norm_mul,
        norm_mul, norm_zpow, norm_zpow, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
      gcongr
      · exact pow_pos (norm_denR_pos γ hZ one_pos) m
      · exact norm_denR_mono γ hZ ht
  have h := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  have hsupp : Function.support g ⊆ {q | IsColZeroQ q} := by
    intro q hq
    by_contra h'
    have hc : ¬IsColZeroQ q := h'
    exact hq (by simp only [hg, hc, ↓reduceDIte])
  have htsum : ∑' q, g q = eisHolR b hb hbpos Z := by
    rw [← tsum_subtype_eq_of_support_subset hsupp, eisHolR]
    rw [← colZeroEquiv.symm.tsum_eq]
    refine tsum_congr fun q => ?_
    have hc : IsColZeroQ (q : PQuot (r + 1) F) := q.2
    simp only [hg, hc, ↓reduceDIte]
    rfl
  rw [← htsum]
  exact h

/-! ### Invariance of $\mathcal E^{(r)}$ under $\mathrm{SL}_r(\mathcal O_F)$ -/

/-- **$\mathcal E^{(r)}(U\cdot Z) = \mathcal E^{(r)}(Z)$** for $U \in \mathrm{SL}_r(\mathcal O_F)$ and $Z \in \mathbb H_r^d$ (`eisensteinR_actU`;
$\det\operatorname{Im}(U\cdot Z)_w = \det\operatorname{Im}Z_w$). -/
theorem eisHolR_actU (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {U : Matrix (Fin r) (Fin r) F} (hU : IsSLIntMat U) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) : eisHolR b hb hbpos (actU U Z) = eisHolR b hb hbpos Z := by
  have hdet : U.det ≠ 0 := by rw [hU.2.2]; exact one_ne_zero
  set V : GL (Fin r) F := (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr hdet) |>.unit
  have hV : (V : Matrix (Fin r) (Fin r) F) = U := rfl
  have hVinv : ((V⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = U⁻¹ := by
    rw [Matrix.coe_units_inv, hV]
  have hVs : IsSLInt V := ⟨by rw [hV]; exact hU.1, by rw [hVinv]; exact hU.2.1, by rw [hV]; exact hU.2.2⟩
  have hZ' : actU U Z ∈ siegelHF F r := actU_mem hdet hZ
  have hE := eisensteinR_actU b hb hbpos hVs Z
  rw [hV, eisensteinR_eq_prodIm_mul b hb hbpos hZ', eisensteinR_eq_prodIm_mul b hb hbpos hZ] at hE
  have hP : prodIm m (actU U Z) = prodIm m Z := by
    unfold prodIm
    exact Finset.prod_congr rfl fun w _ => by rw [det_im_actU U hU.2.2 Z w]
  rw [hP] at hE
  exact mul_left_cancel₀ (prodIm_ne_zero hZ) hE

/-! ### Degree $0$ -/

instance : Subsingleton (Sp 0 F) :=
  ⟨fun g h => Subtype.ext (Matrix.ext fun i _ => by cases i <;> exact (Fin.elim0 ‹_›))⟩

/-- **$\mathcal E^{(0)} = 1$**: in degree $0$ there is one coset, $j = 1$ and $f_f = 1$. -/
theorem eisHolR_zero (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {Z : InfinitePlace F → Matrix (Fin 0) (Fin 0) ℂ} (hZ : Z ∈ siegelHF F 0) : eisHolR b hb hbpos Z = 1 := by
  have hsub : Subsingleton (PQuot 0 F) := ⟨fun q q' => by
    induction q using Quotient.inductionOn with
    | h g => induction q' using Quotient.inductionOn with
      | h g' => exact congrArg _ (Subsingleton.elim g g')⟩
  rw [eisHolR, tsum_eq_single (Quotient.mk _ (1 : Sp 0 F)) fun q hq => absurd (Subsingleton.elim q _) hq,
    holQ_mk b hb hbpos hZ, holTermR]
  have h1 : denR (1 : Sp 0 F) Z = 1 := by simp [denR]
  have h2 : finSecR (unitsOfInt b hb) (fun v => oneSG v m 0) (1 : Sp 0 F) (sZero m 0) = 1 := by
    rw [finSecR_sZero]
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [map_one, secRV_eq, map_one, Module.End.one_apply, coe_oneSG]
    simp [oneG, ptG]
  rw [h1, h2, _root_.one_zpow, one_mul]

end QuadFormsKB.SiegelWeil.Forms
