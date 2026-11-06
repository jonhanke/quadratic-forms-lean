/-
# The nonsingular Fourier coefficients of the holomorphic Siegel Eisenstein series are those of the genus theta series

**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $Q_0 = \sum_{i<n}b_ix_i^2$ totally positive definite with $b_i \in \mathcal O_F$, $n = 2m$, $L = \mathcal O_F^n$; $r \ge 1$, $m > 4r^2$;
$\mathcal E^{(r)}(Z) = \det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$ (`eisHolR`), $\Phi_v = \mathbf 1_{L_v^r}$.

**Result.** **`eisHolR_coeff_full`**: let $\mathcal E^{(r)}(Z) = \sum_Ta(T)e_T(Z)$ be *any* absolutely convergent expansion on $\mathbb H_r^d$ over forms
$T$ in $r$ variables over $F$, with $a(T) \ne 0$ only for totally positive semidefinite $T$. Then for every $T$ with $\det T_G \ne 0$,
$$a(T) = \frac{\mathrm{repMassT}(L, T)}{\mathrm{Mass}(L)} = \frac1{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|}.$$
This is exactly the hypothesis `hfull` of `eisHolR_eq_thetaGenR_of_expansion` (`SiegelWeilAssembly.lean`) for $Q = Q_0$, $L = \mathcal O_F^n$.
Also, for $E$ itself (not only its big-cell part): **`coeffR_eisR_eq_euler`** ($c_T(E, Y)$ = archimedean integral times the Euler product
$\prod_vW_{T,v}/\operatorname{vol}(\mathcal O_v)^{r(r+1)/2}$ of local Whittaker integrals) and **`coeffR_eisR_eq_thetaCoeff`** ($c_T(E, Y) =
\prod_w\det(Y_w)^{m/2}\,\frac{\mathrm{repMassT}(L,T)}{\mathrm{Mass}(L)}\,e_T(iY)$), for $T$ nondegenerate and totally positive definite over $\mathcal O_F$.

*Proof.* (i) $T$ not $\mathcal O_F$-integral: $a(T) = 0$, because $\mathcal E$ is periodic under $\mathrm{Sym}_r(\mathfrak d^{-1})$ (`eisHolR_addB_dual`,
`coeff_eq_zero_of_not_int`), and $\mathrm{repMassT}(L, T) = 0$ because $T = Q[X]$ with $X$ in an integral lattice is integral
(`isIntMat_of_repMassT_ne_zero`). (ii) $T$ integral but not totally positive definite: both sides vanish, since a nondegenerate totally
positive semidefinite form is totally positive definite (`isTotallyPosDef_of_isTotPSD`). (iii) $T$ integral and totally positive definite:
by orthogonality on the unit cube (`coeffR_of_hasSum`) $c_T(\mathcal E, Y) = a(T)e_T(iY)$; by the lower-cell vanishing
(`coeffR_eisR_eq_coeffR_eisBigR`) and the big-cell computation (`coeffR_eisBigR_eq_thetaCoeff`),
$c_T(E, Y) = \prod_w\det(Y_w)^{m/2}\,\frac{\mathrm{repMassT}(L,T)}{\mathrm{Mass}(L)}\,e_T(iY)$; and $E = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\,\mathcal E$.

Sources: Weil, Acta Math. 113 (1965), Ch. II–IV [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1
[unverified]; Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinDualPeriodic
import QuadFormsKB.SiegelWeil.Forms.FourierOrtho
import QuadFormsKB.SiegelWeil.Forms.EisensteinCoeffCompare
import QuadFormsKB.SiegelWeil.Forms.SingularCoeff
import QuadFormsKB.SiegelWeil.Forms.PhiEisenstein

open Matrix NumberField Complex MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus
  QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m n r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### Positivity and integrality of the coefficients -/

/-- A nondegenerate totally positive semidefinite form is totally positive definite. -/
lemma isTotallyPosDef_of_isTotPSD {T : QuadForm F r} (hT : IsTotPSD T) (hdet : (gramT T).det ≠ 0) :
    IsTotallyPosDef T := by
  intro x hx σ
  set w := placeOf σ
  have hPD : ((gramT T).map (realEmb F w)).PosDef := by
    refine (hT w).posDef_iff_det_ne_zero.mpr ?_
    show ((realEmb F w).mapMatrix (gramT T)).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero_iff _ (realEmb F w).injective).mpr hdet
  have hx' : (fun i => realEmb F w (x i)) ≠ 0 := by
    intro h; apply hx; funext i
    exact (realEmb F w).injective (by simpa using congrFun h i)
  have h1 := hPD.dotProduct_mulVec_pos hx'
  have e : realEmb F w (T.eval x) =
      (fun i => realEmb F w (x i)) ⬝ᵥ (gramT T).map (realEmb F w) *ᵥ (fun i => realEmb F w (x i)) := by
    rw [eval_eq_gramT]; simp only [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
  have h2 : 0 < realEmb F w (T.eval x) := by rw [e]; simpa using h1
  rw [← Tamagawa.Measure.realEmb_apply, ← realEmb_placeOf]
  exact_mod_cast h2

/-- $Q[X]$ has coefficients in $\mathcal O_F$ when the columns of $X$ lie in an integral lattice. -/
lemma isIntMat_compMat {Q : QuadForm F n} {M : Submodule (𝓞 F) (Fin n → F)} (hMi : IsIntegral Q M)
    (X : Matrix (Fin n) (Fin r) F) (hX : ∀ j, (fun i => X i j) ∈ M) : IsIntMat (Q.compMat X).coeff := by
  intro i j
  rw [QuadForm.compMat_coeff]
  split_ifs with h1 h2
  · obtain ⟨o, ho⟩ := hMi _ (hX i); exact ⟨o, ho⟩
  · obtain ⟨o, ho⟩ := bil_mem Q hMi (hX i) (hX j); exact ⟨o, ho⟩
  · exact ⟨0, by simp⟩

/-- **The genus theta series has coefficients only at integral forms**: $\mathrm{repMassT}(L, T) \ne 0 \Rightarrow T$ integral. -/
lemma isIntMat_of_repMassT_ne_zero {Q : QuadForm F n} (L : Lat F n) (hLi : IsIntegral Q L.1) {T : QuadForm F r}
    (h : repMassT Q L T ≠ 0) : IsIntMat T.coeff := by
  by_contra hT
  apply h
  unfold repMassT
  refine finsum_mem_eq_zero_of_forall_eq_zero fun c hc => ?_
  rw [latClass_repCountT_eq]
  obtain ⟨M, hMc, hgen⟩ := hc
  have hMi : IsIntegral Q M.1 := SameGenus.isIntegral Q hLi hgen
  have hiso : IsIsometric Q M.1 c.out.1 := by
    have : (Quotient.mk _ c.out : LatClass Q) = Quotient.mk _ M := by rw [Quotient.out_eq, hMc]
    exact (Quotient.exact this).symm
  obtain ⟨g, hg, hgM⟩ := hiso
  have hci : IsIntegral Q c.out.1 := by rw [← hgM]; exact (Nbr.isIntegral_glImage hg).mpr hMi
  have : repCountT Q c.out T = 0 := by
    unfold repCountT
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun X => hT (X.2.2 ▸ isIntMat_compMat hci X.1 X.2.1)⟩
  simp [this]

/-! ### Integral forms over $F$ as forms over $\mathcal O_F$ -/

/-- The form over $\mathcal O_F$ with the same coefficients as an integral form $T$ over $F$. -/
def toIntForm (T : QuadForm F r) (hT : IsIntMat T.coeff) : QuadForm (𝓞 F) r where
  coeff := fun i j => (hT i j).choose
  upper := by
    intro i j hij
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [(hT i j).choose_spec, map_zero]
    exact T.upper hij

lemma toIntForm_map (T : QuadForm F r) (hT : IsIntMat T.coeff) : (toIntForm T hT).map ιO = T := by
  ext i j
  exact (hT i j).choose_spec

lemma toIntForm_nondegenerate (T : QuadForm F r) (hT : IsIntMat T.coeff) (hdet : (gramT T).det ≠ 0) :
    (toIntForm T hT).Nondegenerate := by
  intro h0
  apply hdet
  have hH : T.hessian = (toIntForm T hT).hessian.map ιO := by
    conv_lhs => rw [← toIntForm_map T hT]
    rw [QuadForm.hessian_map]
  rw [gramT, det_smul, hH, show ((toIntForm T hT).hessian.map ιO).det = ((algebraMap (𝓞 F) F).mapMatrix (toIntForm T hT).hessian).det from rfl,
    ← RingHom.map_det, h0, map_zero, mul_zero]

/-! ### The comparison -/

lemma eT_iY_eq_prod (T : QuadForm F r) (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) :
    eT T (fun w => (Y w).map (fun y => (y : ℂ) * Complex.I)) =
      ∏ w, cexp (2 * Real.pi * I * ArchR.trU (tW T w) (iY Y w)) := by
  rw [eT, trPair, ← Complex.exp_sum, Finset.mul_sum]
  refine congrArg cexp (Finset.sum_congr rfl fun w _ => ?_)
  congr 1
  unfold ArchR.trU
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symU_tW]
  rfl

lemma prodIm_zPt {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (t : JR F r → ℝ) :
    prodIm m (zPt Y t) = ∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2) := by
  unfold prodIm
  simp only [zPt_im Y hY]

/-- $c_T(E, Y) = \prod_w\det(Y_w)^{m/2}\,c_T(\mathcal E, Y)$. -/
lemma coeffR_eisR_eq (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (T : QuadForm F r) :
    coeffR (eisR b hb hbpos) T Y =
      (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) * coeffR (eisHolR b hb hbpos) T Y := by
  unfold coeffR
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_unitCube fun t _ => ?_
  rw [eisR_eq_eisensteinR, eisensteinR_eq_prodIm_mul b hb hbpos (zPt_mem_siegelHF Y hY t), prodIm_zPt hY]
  ring

/-- **The nonsingular Fourier coefficients of $\mathcal E^{(r)}$ are those of the genus theta series** (see the module docstring): for
any absolutely convergent expansion $\mathcal E^{(r)} = \sum_Ta(T)e_T$ supported on totally positive semidefinite forms and every $T$ with
$\det T_G \ne 0$, $a(T) = \mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$, $L = \mathcal O_F^n$. -/
@[kb "weil1965" "Ch. II–IV (the nonsingular Fourier coefficients in the Siegel–Weil formula) [unverified]; kudla2008 §1 [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem eisHolR_coeff_full (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) {a : QuadForm F r → ℂ}
    (hsum : ∀ Z ∈ siegelHF F r, Summable fun T => ‖a T * eT T Z‖)
    (hexp : ∀ Z ∈ siegelHF F r, HasSum (fun T => a T * eT T Z) (eisHolR b hb hbpos Z))
    (hpsd : ∀ T, a T ≠ 0 → IsTotPSD T) (T : QuadForm F r) (hdet : (gramT T).det ≠ 0) :
    a T = ((repMassT ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) T /
      mass ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) := by
  set Q := (QuadForm.diag b).map ιO
  set L := Tamagawa.stdLat F (2 * m)
  have hLi : IsIntegral Q L.1 := Tamagawa.Frames.isIntegral_stdLat_map (QuadForm.diag b)
  have hint : ∀ T', a T' ≠ 0 → IsIntMat T'.coeff := fun T' h => by
    by_contra hn
    exact h (coeff_eq_zero_of_not_int hsum hexp
      (fun B hB hBi Z hZ => eisHolR_addB_dual b hb hbpos hB hBi hZ) T' hn)
  by_cases hTi : IsIntMat T.coeff
  swap
  · -- not integral: both sides vanish
    have ha : a T = 0 := by by_contra h; exact hTi (hint T h)
    rw [ha]
    by_contra hne
    exact hTi (isIntMat_of_repMassT_ne_zero L hLi fun h0 => hne (by simp [h0]))
  by_cases hpdT : IsTotallyPosDef T
  swap
  · -- integral, not totally positive definite: both sides vanish
    have ha : a T = 0 := by
      by_contra h; exact hpdT (isTotallyPosDef_of_isTotPSD (hpsd T h) hdet)
    rw [ha]
    by_contra hne
    exact hpdT (isTotallyPosDef_of_isTotPSD
      (isTotPSD_of_repMassT_ne_zero hpd L fun h0 => hne (by simp [h0])) hdet)
  -- integral and totally positive definite: compare the coefficients at height `Y = 1`
  have hT₀map : (toIntForm T hTi).map ιO = T := toIntForm_map T hTi
  set Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ := fun _ => 1 with hYdef
  have hY : ∀ w, (Y w).PosDef := fun _ => Matrix.PosDef.one
  have h1 := coeffR_of_hasSum hsum hexp hint hY T hTi
  have h2 := coeffR_eisR_eq (m := m) b hb hbpos hY T
  have h3 := coeffR_eisR_eq_coeffR_eisBigR b hb hbpos hr hm hY T hTi hdet
  have h4 := coeffR_eisBigR_eq_thetaCoeff b hb hbpos hr hm hpd (toIntForm T hTi)
    (toIntForm_nondegenerate T hTi hdet) (by rw [hT₀map]; exact hpdT) hY
  rw [hT₀map, ← eT_iY_eq_prod] at h4
  set P : ℂ := ∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2) with hPdef
  set E : ℂ := eT T (fun w => (Y w).map (fun y => (y : ℂ) * Complex.I)) with hEdef
  have hP : P = 1 := by simp [hPdef, hYdef]
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have key : a T * E = ((repMassT Q L T / mass Q L : ℝ) : ℂ) * E := by
    have := h2.symm.trans (h3.trans h4)
    rw [h1, hP] at this
    simpa [hP] using this
  exact mul_right_cancel₀ hE key

/-! ### The nonsingular coefficients of $E$ itself -/

lemma gramT_map_det_ne_zero {T₀ : QuadForm (𝓞 F) r} (hT₀ : T₀.Nondegenerate) : (gramT (T₀.map ιO)).det ≠ 0 := by
  rw [gramT, det_smul, QuadForm.hessian_map,
    show (T₀.hessian.map ιO).det = ((algebraMap (𝓞 F) F).mapMatrix T₀.hessian).det from rfl, ← RingHom.map_det]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hT₀

/-- **The $T$-th Fourier coefficient of $E(g_Z, s_0, \Phi)$ is an Euler product of local Whittaker integrals** ($m > 4r^2$, $T_0$ nondegenerate
and totally positive definite over $\mathcal O_F$): $c_T(E, Y) = \mathrm{archIntR}(T, Y)\cdot\mathrm{singR}(T)$ with
$\mathrm{singR}(T) = \prod_vW_{T,v}/\operatorname{vol}(\mathcal O_v)^{r(r+1)/2}$ (the product converging). The lower Bruhat cells contribute nothing
(`coeffR_eisR_eq_coeffR_eisBigR`); the big cell is `coeffR_eisBigR_eq_euler`. -/
@[kb "weil1965" "Ch. II (the nonsingular Fourier coefficients of the Siegel Eisenstein series as Euler products) [unverified]; kudla2008 §1 [unverified]"]
theorem coeffR_eisR_eq_euler (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) (T₀ : QuadForm (𝓞 F) r) (hT₀ : T₀.Nondegenerate)
    (hpdT : IsTotallyPosDef (T₀.map ιO)) {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) :
    HasProd (fun v => whittakerR v (aV (unitsOfInt b hb) v) (locT v T₀) / volR r v) (singR b hb (T₀.map ιO)) ∧
      coeffR (eisR b hb hbpos) (T₀.map ιO) Y = archIntR m (T₀.map ιO) Y * singR b hb (T₀.map ιO) := by
  obtain ⟨h1, h2⟩ := coeffR_eisBigR_eq_euler b hb hbpos hr hm hpd T₀ hT₀ hpdT hY
  refine ⟨h1, ?_⟩
  rw [coeffR_eisR_eq_coeffR_eisBigR b hb hbpos hr hm hY _ (fun i j => ⟨T₀.coeff i j, rfl⟩)
    (gramT_map_det_ne_zero hT₀), h2]

/-- **The nonsingular Fourier coefficients of $E(g_Z, s_0, \Phi)$ are those of the genus theta series** (the Siegel–Weil formula at the
level of nonsingular coefficients; $m > 4r^2$, $T_0$ nondegenerate and totally positive definite over $\mathcal O_F$):
$$c_T(E, Y) = \prod_w\det(Y_w)^{m/2}\cdot\frac{\mathrm{repMassT}(L, T_0)}{\mathrm{Mass}(L)}\cdot\prod_we^{2\pi i\operatorname{tr}(\sigma_w(T_G)\,iY_w)}.$$ -/
@[kb "weil1965" "Ch. II–IV (Siegel–Weil formula of degree r: the nonsingular Fourier coefficients) [unverified]; siegel1935 Hauptsatz [unverified]"]
theorem coeffR_eisR_eq_thetaCoeff (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map ιO)) (T₀ : QuadForm (𝓞 F) r) (hT₀ : T₀.Nondegenerate)
    (hpdT : IsTotallyPosDef (T₀.map ιO)) {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) :
    coeffR (eisR b hb hbpos) (T₀.map ιO) Y =
      (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) *
        ((repMassT ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) (T₀.map ιO) /
          mass ((QuadForm.diag b).map ιO) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) *
        ∏ w, cexp (2 * Real.pi * I * ArchR.trU (tW (T₀.map ιO) w) (iY Y w)) := by
  rw [coeffR_eisR_eq_coeffR_eisBigR b hb hbpos hr hm hY _ (fun i j => ⟨T₀.coeff i j, rfl⟩)
    (gramT_map_det_ne_zero hT₀)]
  exact coeffR_eisBigR_eq_thetaCoeff b hb hbpos hr hm hpd T₀ hT₀ hpdT hY

end QuadFormsKB.SiegelWeil.Forms
