/-
# The unfolding of the Fourier coefficients of the big-cell part of $E(g_Z, s_0)$ (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ totally positive with $b_i \in \mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$, $\Phi_v = \mathbf 1_{L_v^r}$ at every
finite place; the degree $r \ge 1$ with $m > 4r^2$ (absolute convergence of $E(g_Z, s_0, \Phi)$, `summable_norm_globalSecR`); a height
$Y = (Y_w)_w$, $Y_w$ positive definite; $T$ a form in $r$ variables with coefficients in $\mathcal O_F$. Write $u \in F^{\{i\le i'\}}$ for the upper
coordinates of $B = \operatorname{symOf}(u) \in \mathrm{Sym}_r(F)$, $f_f(u) = f_f(w\,n(B), s_0)$ (`fFinR`), $g_\infty(Z) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}
(\prod_w\det(-Z_w))^{-m}$ (`gInfR`), so that the big-cell term is $g_\infty(Z + \sigma(B))f_f(u)$ (`bigCellTerm_eq`).

**Definitions.**
* `eisBigR` $= E_{\mathrm{big}}(Z) = \sum_{B\in\mathrm{Sym}_r(F)}f_\infty(w\,n(B)g_Z, s_0)f_f(w\,n(B), s_0)$, the big-cell part of
  `eisensteinR_eq_lower_add_bigCell`.
* `archIntR m T Y` $= \int_{\mathbb R^J}g_\infty(X(t) + iY)\,e_T(-X(t))\,dt$, the archimedean Whittaker integral in the coordinates of
  `EisensteinUnfoldCoord.lean`.
* `singR T` $= \sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B))$, **the singular series of degree $r$**
  (absolutely convergent, `summable_norm_fFinR_quot`).

**Main result.** **`coeffR_eisBigR`** (the unfolding):
$$c_T(E_{\mathrm{big}}, Y) = \int_{(0,1]^J}E_{\mathrm{big}}(X(t) + iY)\,e_T(-X(t))\,dt = \Big(\int_{\mathbb R^J}g_\infty(X(t) + iY)\,e_T(-X(t))\,dt\Big)\cdot
  \sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B)).$$
*Proof* (the classical unfolding, Siegel 1935 / Weil 1965): exchange $\int$ and $\sum_B$ (absolute convergence); split
$\mathrm{Sym}_r(F) = \bigsqcup_q(\tilde q + \Lambda)$, $\Lambda = \mathrm{Sym}_r(\mathcal O_F)$ (`tsum_eq_tsum_quot`); $f_f$ is $\Lambda$-periodic
(`finSecR_spW_spN_add`) and so is $e_T(-X(t))$ (`eT_realMat_int`); $\Lambda$ is $\mathbb Z^J$ in the coordinates $t$ (`tOf_symOEquiv`), so the
translates of the cube tile $\mathbb R^J$ (`hasSum_integral_unitCube_unfold`); finally translate by $t(\tilde q)$. The absolute convergence of
the singular series is deduced from that of $E$ itself (`summable_norm_fFinR_quot`): each coset has a representative with coordinates in
the closed unit cube, where $|g_\infty(X(t) + iY)|$ is bounded below.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§ 3–6 [unverified]; Weil, *Sur la formule
de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II [unverified]; Kudla, *Some extensions of the
Siegel–Weil formula* (2008), §1 (the unfolding of $E_T$) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldLattice
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldArch
import QuadFormsKB.SiegelWeil.Forms.UnitCubeUnfold

open Matrix NumberField IsDedekindDomain MeasureTheory Filter
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### Upper coordinates of symmetric matrices -/

/-- $u \mapsto \operatorname{symOf}(u)$: upper coordinates $\cong$ symmetric matrices. -/
def symMatEquiv : (SymIdx r → F) ≃ SymMat r F where
  toFun u := ⟨symOf u, symOf_transpose u⟩
  invFun B p := B.1 p.1.1 p.1.2
  left_inv u := by funext p; simp [symOf, p.2]
  right_inv B := by
    apply Subtype.ext
    ext i j
    simp only [symOf, of_apply]
    split_ifs with h
    · rfl
    · exact congrFun (congrFun B.2 i) j

/-! ### The big-cell term in terms of $g_\infty$ -/

/-- $f_f(w\,n(B), s_0)$ for $B = \operatorname{symOf}(u)$. -/
def fFinR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (u : SymIdx r → F) : ℂ :=
  finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (spW * spN (symOf u) (symOf_transpose u)) (sZero m r)

lemma fFinR_add_symO (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (u : SymIdx r → F) {l : SymIdx r → F}
    (hl : l ∈ symO F r) : fFinR b hb (u + l) = fFinR b hb u := by
  unfold fFinR
  rw [← finSecR_spW_spN_add b hb (symOf u) (symOf l) (symOf_transpose u) (symOf_transpose l) (isIntMat_symOf hl)]
  congr 2
  simp only [symOf_add]

lemma im_add_realMat (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin r) F) (w : InfinitePlace F) :
    (Z w + realMat B w).map Complex.im = (Z w).map Complex.im := by
  ext i j; simp [realMat]

/-- **The big-cell term** is $g_\infty(Z + \sigma(B))\,f_f(u)$. -/
lemma bigCellTerm_eq (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ)
    (u : SymIdx r → F) :
    bigCellTerm b hb Z (symMatEquiv u) = gInfR m (fun w => Z w + realMat (symOf u) w) * fFinR b hb u := by
  unfold bigCellTerm fFinR gInfR
  rw [archSecR_spW_spN]
  congr 1
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [im_add_realMat]

/-! ### Definitions -/

/-- **The big-cell part of $E(g_Z, s_0, \Phi)$**: $\sum_{B\in\mathrm{Sym}_r(F)}f_\infty(w\,n(B)g_Z, s_0)\,f_f(w\,n(B), s_0)$. -/
def eisBigR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑' B : SymMat r F, bigCellTerm b hb Z B

/-- The character $\chi_T(t) = e_T(-X(t))$ of the coefficient integral. -/
def chiT (T : QuadForm F r) (t : JR F r → ℝ) : ℂ := eT T (fun w => -(xMat t w).map (fun x => (x : ℂ)))

variable (m) in
/-- **The archimedean integral** $\int_{\mathbb R^J}g_\infty(X(t) + iY)\,e_T(-X(t))\,dt$. -/
def archIntR (T : QuadForm F r) (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) : ℂ :=
  ∫ t, gInfR m (zPt Y t) * chiT T t

/-- **The singular series of degree $r$**: $\sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B))$ (through the
representatives `q.out`). -/
@[kb "siegel1935" "§ 3 (the singular series as a sum over symmetric matrices modulo 1) [unverified]; kudla2008 §1 [unverified]"]
def singR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (T : QuadForm F r) : ℂ :=
  ∑' q : (SymIdx r → F) ⧸ symO F r, fFinR b hb q.out * eT T (realMat (symOf q.out))

/-! ### The character -/

lemma continuous_xCoord (p : SymIdx r) (w : InfinitePlace F) : Continuous fun t : JR F r → ℝ => xCoord t p w := by
  have hl : Continuous fun t : JR F r → ℝ => (oBasis F).equivFun.symm (fun j => t (p, j)) := by
    have : Continuous fun t : JR F r → ℝ => (fun j => t (p, j)) := continuous_pi fun j => continuous_apply _
    exact (LinearMap.continuous_of_finiteDimensional (oBasis F).equivFun.symm.toLinearMap).comp this
  exact (continuous_apply w).comp hl

lemma continuous_xMat_apply (w : InfinitePlace F) (i j : Fin r) : Continuous fun t : JR F r → ℝ => xMat t w i j := by
  simp only [xMat, symOf, of_apply]
  split_ifs
  · exact continuous_xCoord _ w
  · exact continuous_xCoord _ w

lemma continuous_chiT (T : QuadForm F r) : Continuous (chiT (F := F) T) := by
  unfold chiT eT trPair
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine continuous_const.mul ?_
  simp only [Matrix.neg_apply, Matrix.map_apply]
  exact (Complex.continuous_ofReal.comp (continuous_xMat_apply w j i)).neg

lemma norm_chiT (T : QuadForm F r) (t : JR F r → ℝ) : ‖chiT T t‖ = 1 := by
  rw [chiT, norm_eT]
  simp

lemma xMat_neg_tOf_add (t : JR F r → ℝ) (u : SymIdx r → F) (w : InfinitePlace F) :
    (xMat (t + tOf u) w).map (fun x => (x : ℂ)) = (xMat t w).map (fun x => (x : ℂ)) + realMat (symOf u) w := by
  rw [xMat_add, Matrix.map_add _ (by intros; push_cast; ring), xMat_tOf]

/-- $\chi_T(t + t(u)) = \chi_T(t)\,e_T(\sigma(u))^{-1}$. -/
lemma chiT_add_tOf (T : QuadForm F r) (t : JR F r → ℝ) (u : SymIdx r → F) :
    chiT T (t + tOf u) = chiT T t * (eT T (realMat (symOf u)))⁻¹ := by
  unfold chiT
  have e : (fun w => -(xMat (t + tOf u) w).map (fun x => (x : ℂ))) =
      (fun w => -(xMat t w).map (fun x => (x : ℂ))) + -(realMat (symOf u)) := by
    funext w; rw [xMat_neg_tOf_add]; simp only [Pi.add_apply, Pi.neg_apply]; abel
  rw [e, eT_add, eT_neg]

/-- $\chi_T$ is $\Lambda$-periodic for $T$ with coefficients in $\mathcal O_F$. -/
lemma chiT_add_int (T : QuadForm F r) (hT : IsIntMat T.coeff) (t : JR F r → ℝ) (n : JR F r → ℤ) :
    chiT T (t + fun q => (n q : ℝ)) = chiT T t := by
  have h := chiT_add_tOf T t (symOEquiv n : SymIdx r → F)
  rw [tOf_symOEquiv] at h
  rw [h, eT_realMat_int T hT (symOf_transpose _) (isIntMat_symOf (symOEquiv n).2), inv_one, mul_one]

lemma zPt_add_tOf (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (t : JR F r → ℝ) (u : SymIdx r → F) :
    zPt Y (t + tOf u) = fun w => zPt Y t w + realMat (symOf u) w := by
  funext w; rw [zPt_add, xMat_tOf]

/-! ### Absolute convergence of the singular series -/

lemma mk_out_add_symO (q : (SymIdx r → F) ⧸ symO F r) {l : SymIdx r → F} (hl : l ∈ symO F r) :
    (QuotientAddGroup.mk (q.out + l) : (SymIdx r → F) ⧸ symO F r) = q := by
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff l).mpr hl, add_zero, QuotientAddGroup.out_eq']

lemma unitCube_subset_Icc : unitCube (JR F r) ⊆ Set.Icc (0 : JR F r → ℝ) 1 :=
  fun t ht => ⟨fun j => (ht j).1.le, fun j => (ht j).2⟩

/-- $|g_\infty(X(t) + iY)|$ is bounded below on the closed unit cube. -/
lemma exists_lower_bound_gInfR (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef) (m : ℕ) :
    ∃ c > 0, ∀ t ∈ Set.Icc (0 : JR F r → ℝ) 1, c ≤ ‖gInfR m (zPt Y t)‖ := by
  have hK : IsCompact (Set.Icc (0 : JR F r → ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0 : JR F r → ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  obtain ⟨t0, -, ht0⟩ := hK.exists_isMinOn hne (continuous_gInfR_zPt Y hY m).norm.continuousOn
  exact ⟨‖gInfR m (zPt Y t0)‖, norm_pos_iff.mpr (gInfR_zPt_ne_zero Y hY m t0), fun t ht => ht0 ht⟩

section Main

variable (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (algebraMap (𝓞 F) F (b i)))

include hbpos in
lemma summable_norm_bigCell_u (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) :
    Summable fun u : SymIdx r → F => ‖gInfR m (fun w => Z w + realMat (symOf u) w) * fFinR b hb u‖ := by
  have := (summable_norm_bigCellTerm b hb hbpos hr hZ hm).comp_injective (symMatEquiv (F := F) (r := r)).injective
  refine this.congr fun u => ?_
  simp only [Function.comp, bigCellTerm_eq]

include hbpos in
/-- **The singular series of degree $r$ converges absolutely** ($m > 4r^2$):
$\sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}|f_f(w\,n(B), s_0)| < \infty$.
*Proof.* Each coset has a representative $u$ with coordinates $t(u)$ in the unit cube, where $|g_\infty(X(t) + iY)| \ge c > 0$; so
$|f_f(u)| \le c^{-1}|g_\infty(iY + \sigma(u))f_f(u)|$, a term of the absolutely convergent big-cell sum of $E(g_{iY}, s_0)$. -/
theorem summable_norm_fFinR_quot (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) :
    Summable fun q : (SymIdx r → F) ⧸ symO F r => ‖fFinR b hb q.out‖ := by
  set Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ := fun _ => 1
  have hY : ∀ w, (Y w).PosDef := fun _ => PosDef.one
  obtain ⟨c, hc, hcle⟩ := exists_lower_bound_gInfR Y hY m
  have hZ0 : zPt Y 0 ∈ siegelHF F r := zPt_mem_siegelHF Y hY 0
  have hS := summable_norm_bigCell_u b hb hbpos hr hm hZ0
  choose n hn using fun q : (SymIdx r → F) ⧸ symO F r => exists_int_add_mem_unitCube (tOf q.out)
  set rep : (SymIdx r → F) ⧸ symO F r → SymIdx r → F := fun q => q.out + (symOEquiv (n q) : SymIdx r → F)
  have hrep_inj : Function.Injective rep := by
    intro q q' h
    have := congrArg (fun u => (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r)) h
    simp only [rep] at this
    rwa [mk_out_add_symO q (symOEquiv (n q)).2, mk_out_add_symO q' (symOEquiv (n q')).2] at this
  refine ((hS.comp_injective hrep_inj).mul_left c⁻¹).of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_
  have hf : fFinR b hb (rep q) = fFinR b hb q.out := fFinR_add_symO b hb _ (symOEquiv (n q)).2
  have hz : (fun w => zPt Y 0 w + realMat (symOf (rep q)) w) = zPt Y (tOf (rep q)) := by
    rw [← zPt_add_tOf, zero_add]
  have ht : tOf (rep q) ∈ Set.Icc (0 : JR F r → ℝ) 1 := by
    apply unitCube_subset_Icc
    simp only [rep]
    rw [tOf_add, tOf_symOEquiv]
    exact hn q
  have hg := hcle _ ht
  simp only [Function.comp]
  rw [hz, norm_mul, hf, ← mul_assoc]
  calc ‖fFinR b hb q.out‖ = c⁻¹ * c * ‖fFinR b hb q.out‖ := by rw [inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * ‖gInfR m (zPt Y (tOf (rep q)))‖ * ‖fFinR b hb q.out‖ := by
      gcongr

/-! ### The unfolding -/

lemma integrable_gInfR_shift {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (hmr : r < m)
    (s : JR F r → ℝ) : Integrable fun t : JR F r → ℝ => gInfR m (zPt Y (t + s)) :=
  (integrable_gInfR_zPt Y hY hmr).comp_add_right s

lemma integrable_gInfR_shift_chi {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (hmr : r < m)
    (s : JR F r → ℝ) (T : QuadForm F r) : Integrable fun t : JR F r → ℝ => gInfR m (zPt Y (t + s)) * chiT T t :=
  (integrable_gInfR_shift hY hmr s).mul_bdd (continuous_chiT T).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (norm_chiT T t).le)

/-- $\sum_{n\in\mathbb Z^J}\int_{(0,1]^J}|g(t + n + s)|\,dt = \int_{\mathbb R^J}|g_\infty(X(t) + iY)|\,dt$. -/
lemma hasSum_integral_norm_shift {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (hmr : r < m)
    (s : JR F r → ℝ) :
    HasSum (fun n : JR F r → ℤ => ∫ t in unitCube (JR F r), ‖gInfR m (zPt Y (t + (fun q => (n q : ℝ)) + s))‖)
      (∫ t, ‖gInfR m (zPt Y t)‖) := by
  have hI : Integrable fun t : JR F r → ℝ => ((‖gInfR m (zPt Y (t + s))‖ : ℝ) : ℂ) :=
    (integrable_gInfR_shift hY hmr s).norm.ofReal
  have h := hasSum_integral_unitCube_unfold _ hI
  have e1 : ∫ t, ((‖gInfR m (zPt Y (t + s))‖ : ℝ) : ℂ) = ((∫ t, ‖gInfR m (zPt Y t)‖ : ℝ) : ℂ) := by
    rw [integral_complex_ofReal]
    have := integral_add_right_eq_self (μ := volume) (fun t => ‖gInfR m (zPt Y t)‖) s
    rw [this]
  rw [e1] at h
  have e2 : (fun n : JR F r → ℤ => ∫ t in unitCube (JR F r),
      ((‖gInfR m (zPt Y (t + (fun j => (n j : ℝ)) + s))‖ : ℝ) : ℂ)) =
      fun n => ((∫ t in unitCube (JR F r), ‖gInfR m (zPt Y (t + (fun q => (n q : ℝ)) + s))‖ : ℝ) : ℂ) := by
    funext n; exact integral_complex_ofReal
  rw [e2] at h
  exact Complex.hasSum_ofReal.mp h

variable (m) in
/-- $|f_f(u)|\int_{(0,1]^J}|g_\infty(X(t + t(u)) + iY)|\,dt$. -/
def kNormR (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (u : SymIdx r → F) : ℝ :=
  ‖fFinR b hb u‖ * ∫ t in unitCube (JR F r), ‖gInfR m (zPt Y (t + tOf u))‖

lemma kNormR_add_symO (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (u : SymIdx r → F) (n : JR F r → ℤ) :
    kNormR m b hb Y (u + (symOEquiv n : SymIdx r → F)) =
      ‖fFinR b hb u‖ * ∫ t in unitCube (JR F r), ‖gInfR m (zPt Y (t + (fun q => (n q : ℝ)) + tOf u))‖ := by
  unfold kNormR
  rw [fFinR_add_symO b hb _ (symOEquiv n).2, tOf_add, tOf_symOEquiv]
  simp only [add_assoc, add_comm (tOf u)]

variable {b hb} in
lemma summable_integral_norm_K {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (hmr : r < m)
    (hq : Summable fun q : (SymIdx r → F) ⧸ symO F r => ‖fFinR b hb q.out‖) :
    Summable fun u : SymIdx r → F => kNormR m b hb Y u := by
  have hH0 : ∀ u, 0 ≤ kNormR m b hb Y u := fun u => mul_nonneg (norm_nonneg _)
    (setIntegral_nonneg measurableSet_unitCube fun _ _ => norm_nonneg _)
  have key : ∀ (q : (SymIdx r → F) ⧸ symO F r),
      HasSum (fun l : symO F r => kNormR m b hb Y (q.out + l))
        (‖fFinR b hb q.out‖ * ∫ t, ‖gInfR m (zPt Y t)‖) := by
    intro q
    have h := (hasSum_integral_norm_shift hY hmr (tOf q.out)).mul_left ‖fFinR b hb q.out‖
    have e : (fun l : symO F r => kNormR m b hb Y (q.out + l)) ∘ symOEquiv = fun n : JR F r → ℤ =>
        ‖fFinR b hb q.out‖ * ∫ t in unitCube (JR F r), ‖gInfR m (zPt Y (t + (fun q => (n q : ℝ)) + tOf q.out))‖ :=
      funext fun n => kNormR_add_symO b hb Y q.out n
    rw [← e] at h
    exact symOEquiv.hasSum_iff.mp h
  have hP : Summable fun x : ((SymIdx r → F) ⧸ symO F r) × symO F r => kNormR m b hb Y (quotProdEquiv x) := by
    refine (summable_prod_of_nonneg fun x => hH0 _).mpr ⟨fun q => (key q).summable, ?_⟩
    refine (hq.mul_right (∫ t, ‖gInfR m (zPt Y t)‖)).congr fun q => ?_
    exact ((key q).tsum_eq).symm
  exact (quotProdEquiv.summable_iff).mp hP

include hbpos in
/-- **The unfolding of the $T$-th Fourier coefficient of the big-cell part** ($F$ totally real, $Q = \sum_ib_ix_i^2$ totally positive over
$\mathcal O_F$, $L = \mathcal O_F^n$, $n = 2m$, $r \ge 1$, $m > 4r^2$, $Y_w$ positive definite, $T$ with coefficients in $\mathcal O_F$):
$$\int_{(0,1]^J}E_{\mathrm{big}}(X(t) + iY)\,e_T(-X(t))\,dt = \Big(\int_{\mathbb R^J}g_\infty(X(t) + iY)\,e_T(-X(t))\,dt\Big)\cdot
  \sum_{B\in\mathrm{Sym}_r(F)/\mathrm{Sym}_r(\mathcal O_F)}f_f(w\,n(B), s_0)\,e_T(\sigma(B)),$$
the archimedean Whittaker integral times the singular series of degree $r$. -/
@[kb "weil1965" "Ch. II (the unfolding of the Fourier coefficients of the Siegel Eisenstein series) [unverified]; siegel1935 §§ 3–6 [unverified]; kudla2008 §1 [unverified]"]
theorem coeffR_eisBigR (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m) {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ}
    (hY : ∀ w, (Y w).PosDef) (T : QuadForm F r) (hT : IsIntMat T.coeff) :
    coeffR (eisBigR b hb) T Y = archIntR m T Y * singR b hb T := by
  have hmr : r < m := by
    have h1 : (r : ℝ) ≤ 4 * (r : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    exact_mod_cast h1.trans_lt hm
  set G : (JR F r → ℝ) → ℂ := fun t => gInfR m (zPt Y t)
  set K : (SymIdx r → F) → (JR F r → ℝ) → ℂ := fun u t => G (t + tOf u) * fFinR b hb u * chiT T t
  have hq := summable_norm_fFinR_quot b hb hbpos hr hm
  -- the integrand as a sum over `u`
  have h1 : ∀ t, eisBigR b hb (zPt Y t) * chiT T t = ∑' u, K u t := by
    intro t
    unfold eisBigR
    rw [← (symMatEquiv (F := F) (r := r)).tsum_eq, ← tsum_mul_right]
    congr 1; funext u
    rw [bigCellTerm_eq, ← zPt_add_tOf]
  have hKint : ∀ u, IntegrableOn (K u) (unitCube (JR F r)) := fun u => by
    have := ((integrable_gInfR_shift hY hmr (tOf u)).mul_const (fFinR b hb u)).mul_bdd
      (continuous_chiT T).aestronglyMeasurable (Filter.Eventually.of_forall fun t => (norm_chiT T t).le)
    exact this.integrableOn
  have hKnorm : ∀ u, ∫ t in unitCube (JR F r), ‖K u t‖ =
      ‖fFinR b hb u‖ * ∫ t in unitCube (JR F r), ‖G (t + tOf u)‖ := fun u => by
    rw [← integral_const_mul]
    congr 1; funext t
    simp only [K, norm_mul, norm_chiT, mul_one]; ring
  have hsumK : Summable fun u => ∫ t in unitCube (JR F r), ‖K u t‖ := by
    refine (summable_integral_norm_K hY hmr hq).congr fun u => ?_
    rw [hKnorm]; rfl
  -- exchange of sum and integral
  have h2 : ∫ t in unitCube (JR F r), ∑' u, K u t = ∑' u, ∫ t in unitCube (JR F r), K u t := by
    refine integral_tsum (fun u => (hKint u).aestronglyMeasurable) ?_
    have e : ∀ u, ∫⁻ t in unitCube (JR F r), ‖K u t‖ₑ = ENNReal.ofReal (∫ t in unitCube (JR F r), ‖K u t‖) :=
      fun u => (ofReal_integral_norm_eq_lintegral_enorm (hKint u)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => setIntegral_nonneg measurableSet_unitCube fun _ _ => norm_nonneg _)
      hsumK]
    exact ENNReal.ofReal_ne_top
  -- regroup by cosets
  have hsumI : Summable fun u => ‖∫ t in unitCube (JR F r), K u t‖ :=
    hsumK.of_nonneg_of_le (fun _ => norm_nonneg _) fun u => norm_integral_le_integral_norm _
  have h3 := tsum_eq_tsum_quot hsumI
  -- the inner sums
  have h4 : ∀ q : (SymIdx r → F) ⧸ symO F r, ∑' n : JR F r → ℤ,
      ∫ t in unitCube (JR F r), K (q.out + (symOEquiv n : SymIdx r → F)) t =
        fFinR b hb q.out * eT T (realMat (symOf q.out)) * archIntR m T Y := by
    intro q
    set s := tOf q.out
    set h : (JR F r → ℝ) → ℂ := fun t => G (t + s) * chiT T t
    have hh : Integrable h := integrable_gInfR_shift_chi hY hmr s T
    have hs := (hasSum_integral_unitCube_unfold h hh).mul_left (fFinR b hb q.out)
    have e1 : ∀ n : JR F r → ℤ, ∫ t in unitCube (JR F r), K (q.out + (symOEquiv n : SymIdx r → F)) t =
        fFinR b hb q.out * ∫ t in unitCube (JR F r), h (t + fun q => (n q : ℝ)) := by
      intro n
      rw [← integral_const_mul]
      congr 1; funext t
      simp only [K, h]
      rw [fFinR_add_symO b hb _ (symOEquiv n).2, tOf_add, tOf_symOEquiv, chiT_add_int T hT]
      rw [show t + (s + fun q => (n q : ℝ)) = t + (fun q => (n q : ℝ)) + s by abel]
      ring
    simp_rw [e1]
    rw [hs.tsum_eq]
    -- translate by `s`
    have e2 : ∫ t, h t = eT T (realMat (symOf q.out)) * archIntR m T Y := by
      unfold archIntR
      rw [← integral_const_mul]
      rw [← integral_add_right_eq_self (fun t => h t) (-s)]
      congr 1; funext t
      simp only [h]
      rw [neg_add_cancel_right]
      have hc := chiT_add_tOf T (t + -s) q.out
      rw [neg_add_cancel_right] at hc
      have hne : eT T (realMat (symOf q.out)) ≠ 0 := Complex.exp_ne_zero _
      rw [hc]
      field_simp
      exact mul_comm _ _
    rw [e2]; ring
  -- assemble
  show ∫ t in unitCube (JR F r), eisBigR b hb (zPt Y t) * chiT T t = _
  simp_rw [h1]
  rw [h2, h3]
  simp_rw [h4]
  unfold singR
  rw [← tsum_mul_left]
  congr 1; funext q; ring

end Main

end QuadFormsKB.SiegelWeil.Forms
