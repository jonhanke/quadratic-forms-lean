/-
# The archimedean factor of the unfolding at one real place
Rewrites the archimedean integral `archPlaceR` at one real place $w$ in terms of Siegel's Gaussian integral `gaussR`.

**Definitions.**
* `tW T w`: the upper-triangular coordinates of $\sigma_w(T_G)$, where $T_G$ is the Gram matrix of $T$;
* `iY Y w`: the matrix $iY_w$.

**Results.**
* `symU_tW`: $\mathrm{symU}(tW) = \sigma_w(T_G)$;
* `det_neg_pow_eq_gaussR`: for $Z \in \mathbb H_r$ and $S = \operatorname{diag}(s)$, $s_i > 0$, $N = 2m$,
  $$\det(-Z)^{-m} = (2i)^{rm}\Big(\prod_i s_i^{r/2}\Big)\,G_S(Z);$$
* **`archPlaceR_eq_gaussR`**:
  $$\mathtt{archPlaceR}_w = (2i)^{rm}\Big(\prod_{i<2m}\sqrt{s_i}^{\,r}\Big)\int_{\mathrm{Sym}_r(\mathbb R)}
  G_S(iY_w + x)\,e\big(-\operatorname{tr}(\sigma_w(T_G)x)\big)\,dx.$$

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldArchProd
import QuadFormsKB.SiegelWeil.Forms.ArchWhittakerR
open Matrix NumberField MeasureTheory Complex
open scoped Real
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.SiegelWeil.Forms.ArchR
set_option linter.unusedSectionVars false
noncomputable section
namespace QuadFormsKB.SiegelWeil.Forms
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- The upper-triangular coordinates of $\sigma_w(T_G)$ (the real image at the place $w$ of the Gram matrix of $T$). -/
def tW (T : QuadForm F r) (w : InfinitePlace F) : SymIdx r → ℝ :=
  fun p => realEmb F w (gramT T p.1.1 p.1.2)

/-- The complex matrix $iY_w$. -/
def iY (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (w : InfinitePlace F) : Matrix (Fin r) (Fin r) ℂ :=
  (Y w).map (fun y => (y : ℂ) * I)

/-- The symmetric matrix with coordinates `tW T w` is $\sigma_w(T_G)$. -/
lemma symU_tW (T : QuadForm F r) (w : InfinitePlace F) :
    symU (tW T w) = (gramT T).map (fun x => realEmb F w x) := by
  have h : ((gramT T).map (fun x => realEmb F w x))ᵀ = (gramT T).map (fun x => realEmb F w x) := by
    rw [← transpose_map, gramT_transpose]
  exact symU_upper h

/-- For $Z \in \mathbb H_r$: $\det(-Z)^{-m} = (2i)^{rm}\big(\prod_i\sqrt{s_i}^{\,r}\big)G_S(Z)$. -/
lemma det_neg_pow_eq_gaussR {m : ℕ} (s : Fin (2 * m) → ℝ) (hs : ∀ i, 0 < s i)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    (-Z).det ^ (-(m : ℤ)) =
      (2 * I) ^ (r * m) * ((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ) * gaussR s Z := by
  rw [gaussR_eq s hs hZ]
  have hd : Z.det ≠ 0 := det_ne_zero_of_mem_siegelH hZ
  have hP : (∏ i, (Real.sqrt (s i) ^ r) : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Real.sqrt_pos.2 (hs i)).ne'
  have hPc : ((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  have hinv : ((∏ i, (Real.sqrt (s i) ^ r)⁻¹ : ℝ) : ℂ) = (((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ))⁻¹ := by
    rw [Finset.prod_inv_distrib, Complex.ofReal_inv]
  rw [Matrix.det_neg, Matrix.det_smul, Fintype.card_fin, _root_.zpow_neg, zpow_natCast, hinv]
  have h2 : ((-2 * I) ^ r) = (-1) ^ r * (2 * I) ^ r := by
    rw [← mul_pow]; ring
  rw [h2, pow_mul]
  have hI : (2 * I) ^ r ≠ 0 := pow_ne_zero _ (by simp)
  have hm1 : ((-1 : ℂ) ^ r) ≠ 0 := pow_ne_zero _ (by simp)
  generalize ((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ) = P at *
  generalize ((-1 : ℂ) ^ r) = a at *
  generalize ((2 * I) ^ r) = b at *
  field_simp
  rw [one_div, inv_pow, ← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hm1 hd) hI))]

/-- **The archimedean factor at one place in terms of the Gaussian integral:**
$\mathtt{archPlaceR}_w = (2i)^{rm}\big(\prod_i\sqrt{s_i}^{\,r}\big)\int G_S(iY_w+x)\,e(-\operatorname{tr}(\sigma_w(T_G)x))\,dx$. -/
theorem archPlaceR_eq_gaussR {m : ℕ} (s : Fin (2 * m) → ℝ) (hs : ∀ i, 0 < s i) (T : QuadForm F r)
    (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef) (w : InfinitePlace F) :
    archPlaceR m T Y w = (2 * I) ^ (r * m) * ((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ) *
      ∫ B : SymIdx r → ℝ, gaussR s (iY Y w + cR (symU B)) *
        cexp (-2 * π * I * trU (tW T w) (cR (symU B))) := by
  have hmem : ∀ B : SymIdx r → ℝ, iY Y w + cR (symU B) ∈ siegelH r := by
    intro B
    have h0 : iY Y w ∈ siegelH r := by
      refine ⟨?_, ?_⟩
      · ext i j
        have := (hY w).isHermitian
        have h' := congrFun (congrFun this.eq j) i
        simp only [iY, transpose_apply, map_apply]
        have : Y w j i = Y w i j := by simpa using h'.symm
        rw [this]
      · have : (iY Y w).map Complex.im = Y w := by
          ext i j; simp [iY]
        rw [this]; exact hY w
    exact add_symU_mem h0 B
  unfold archPlaceR
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun B => ?_)
  have h1 := det_neg_pow_eq_gaussR s hs (hmem B)
  have h1' : (-((Y w).map (fun y => (y : ℂ) * Complex.I) + cR (symU B))).det ^ (-(m : ℤ)) =
      (2 * I) ^ (r * m) * ((∏ i, (Real.sqrt (s i) ^ r) : ℝ) : ℂ) * gaussR s (iY Y w + cR (symU B)) := h1
  simp only []
  rw [h1', mul_assoc]
  congr 2
  have e1 := symU_tW T w
  have : trU (tW T w) (cR (symU B)) =
      ∑ i, ∑ j, ((realEmb F w (gramT T i j) : ℝ) : ℂ) * ((symU B j i : ℝ) : ℂ) := by
    unfold trU
    rw [e1]
    rfl
  rw [this]
  ring_nf

end QuadFormsKB.SiegelWeil.Forms
