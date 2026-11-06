/-
# Loewner monotonicity of $|\det(CZ+D)|$ and boundedness of the holomorphic Eisenstein series on $\{\operatorname{Im}Z \ge Y_0\}$
**Layer:** real and complex linear algebra, then global over a totally real number field $F$.

**Results.**
* **`norm_det_le_of_psd`**: for a real symmetric coprime pair $(C, D)$ (the bottom blocks of a real symplectic matrix), $Z \in \mathbb H_r$ and $P$
  real positive semidefinite, $|\det(CZ + D)| \le |\det(C(Z + iP) + D)|$. *Proof:* $P = B^{\mathsf T}B$ ($B = \sqrt P$, continuous functional
  calculus), so $P = \sum_kb_kb_k^{\mathsf T}$ over the rows $b_k$ of $B$; add the rank-one terms one at a time
  (`monotoneOn_norm_det_rankOne`, each intermediate point stays in $\mathbb H_r$).
* **`exists_bound_eisHolR`**: for $Y_0 = (Y_{0,w})_w$ positive definite, $\mathcal E^{(r)}$ (`eisHolR`, $m > 4r^2$) is bounded on
  $\{Z \in \mathbb H_r^d : \operatorname{Im}Z_w - Y_{0,w} \succeq 0\ \forall w\}$. *Proof:* translate $\operatorname{Re}Z$ into the unit cube by
  $\mathrm{Sym}_r(\mathcal O_F)$ (`eisHolR_addB`); each term at $Z$ is at most the term at $\operatorname{Re}Z + iY_0$ (`norm_det_le_of_psd` at every real
  place), which is dominated uniformly on the compact set $\{X(t) + iY_0 : t \in [0,1]^J\}$ (`exists_holQ_majorant`).

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (boundedness of Eisenstein series on Siegel domains) [unverified];
Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpBound
import QuadFormsKB.SiegelWeil.Forms.HolExpPeriodic
import QuadFormsKB.SiegelWeil.Forms.EisensteinLowerCell
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open Matrix NumberField
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus
open scoped MatrixOrder Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Loewner monotonicity -/

section Loewner

variable {r : ℕ} {C D : Matrix (Fin r) (Fin r) ℝ}

/-- Adding $i\sum_{k\in s}v_kv_k^{\mathsf T}$ keeps $Z$ in $\mathbb H_r$ and does not decrease $|\det(CZ + D)|$. -/
lemma norm_det_le_add_sum (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin r → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0) {ι : Type*} (v : ι → Fin r → ℝ)
    (s : Finset ι) {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    Z + Complex.I • (∑ k ∈ s, vecMulVec (v k) (v k)).map (fun x => (x : ℂ)) ∈ siegelH r ∧
      ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ ≤
        ‖(C.map (↑) * (Z + Complex.I • (∑ k ∈ s, vecMulVec (v k) (v k)).map (fun x => (x : ℂ))) + D.map (↑) :
          Matrix (Fin r) (Fin r) ℂ).det‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hZ]
  | insert a s ha ih =>
    obtain ⟨hZ', hle⟩ := ih
    set Z' := Z + Complex.I • (∑ k ∈ s, vecMulVec (v k) (v k)).map (fun x => (x : ℂ))
    have e : Z + Complex.I • (∑ k ∈ insert a s, vecMulVec (v k) (v k)).map (fun x => (x : ℂ)) =
        Z' + (((1 : ℝ) : ℂ) * Complex.I) • (vecMulVec (v a) (v a)).map (fun x => (x : ℂ)) := by
      rw [Finset.sum_insert ha, Matrix.map_add _ (by intros; push_cast; ring), smul_add]
      simp only [Z', Complex.ofReal_one, one_mul]
      abel
    have e0 : Z' = Z' + (((0 : ℝ) : ℂ) * Complex.I) • (vecMulVec (v a) (v a)).map (fun x => (x : ℂ)) := by
      simp
    rw [e]
    refine ⟨mem_siegelH_add_rankOne hZ' (v a) zero_le_one, hle.trans ?_⟩
    have hmono := monotoneOn_norm_det_rankOne hsym hrank hZ' (v a) (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr zero_le_one) zero_le_one
    simp only at hmono
    conv_lhs => rw [e0]
    exact hmono

/-- **Loewner monotonicity**: $|\det(CZ + D)| \le |\det(C(Z + iP) + D)|$ for $P \succeq 0$ real. -/
theorem norm_det_le_of_psd (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin r → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) {P : Matrix (Fin r) (Fin r) ℝ} (hP : P.PosSemidef) :
    Z + Complex.I • P.map (fun x => (x : ℂ)) ∈ siegelH r ∧
      ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ ≤
        ‖(C.map (↑) * (Z + Complex.I • P.map (fun x => (x : ℂ))) + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ := by
  set B := CFC.sqrt P
  have hB : star B * B = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hsum : P = ∑ k, vecMulVec (B k) (B k) := by
    rw [← hB]
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply, star_eq_conjTranspose]
  rw [hsum]
  exact norm_det_le_add_sum hsym hrank (fun k => B k) Finset.univ hZ

end Loewner

/-! ### Boundedness of $\mathcal E^{(r)}$ on $\{\operatorname{Im}Z \ge Y_0\}$ -/

section Bound

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma holQ_eq_out (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (q : PQuot r F) :
    holQ b hb hbpos Z q = holTermR b hb Z q.out := by
  conv_lhs => rw [← Quotient.out_eq q]
  exact holQ_mk b hb hbpos hZ q.out

/-- One term at $Z$ is at most the term at $\operatorname{Re}Z + iY_0$ when $\operatorname{Im}Z_w - Y_{0,w} \succeq 0$. -/
lemma norm_holTermR_le (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (γ : Sp r F)
    {Z0 : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ0 : Z0 ∈ siegelHF F r)
    (P : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hP : ∀ w, (P w).PosSemidef) :
    ‖holTermR b hb (fun w => Z0 w + Complex.I • (P w).map (fun x => (x : ℂ))) γ‖ ≤ ‖holTermR b hb Z0 γ‖ := by
  unfold holTermR
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hpos : 0 < ‖denR γ Z0‖ := norm_pos_iff.mpr (by
    unfold denR; exact Finset.prod_ne_zero_iff.mpr fun w _ => det_denW_ne_zero γ hZ0 w)
  have hle : ‖denR γ Z0‖ ≤ ‖denR γ (fun w => Z0 w + Complex.I • (P w).map (fun x => (x : ℂ)))‖ := by
    unfold denR
    rw [norm_prod, norm_prod]
    refine Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) fun w _ => ?_
    exact (norm_det_le_of_psd (blockCw_mul_transpose' γ w)
      (fun u hC hD => blocks_vecMul_eq_zero (realEmb F w) γ u hC hD) (hZ0 w) (hP w)).2
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hle _)

/-- **$\mathcal E^{(r)}$ is bounded on $\{\operatorname{Im}Z_w \succeq Y_{0,w}\}$** ($m > 4r^2$). -/
@[kb "freitag1983" "Ch. I (Eisenstein series are bounded on Siegel domains) [unverified]"]
theorem exists_bound_eisHolR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    {Y0 : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY0 : ∀ w, (Y0 w).PosDef) :
    ∃ M : ℝ, ∀ Z ∈ siegelHF F r, (∀ w, ((Z w).map Complex.im - Y0 w).PosSemidef) →
      ‖eisHolR b hb hbpos Z‖ ≤ M := by
  obtain ⟨M, G, hG, hG0, hbd⟩ := exists_holQ_majorant b hb hbpos hr hm
    (S := fun w => (fun t => zPt Y0 t w) '' Set.Icc (0 : JR F r → ℝ) 1)
    (fun w => isCompact_Icc.image (continuous_zPt_apply Y0 w))
    (fun w => by rintro _ ⟨t, -, rfl⟩; exact zPt_mem_siegelHF Y0 hY0 t w)
  refine ⟨M * ∑' q, G q, fun Z hZ hZY => ?_⟩
  -- translate the real part into the unit cube
  obtain ⟨s, hs⟩ := exists_xMat_eq (fun w => (Z w).map Complex.re) (fun w => by
    rw [← Matrix.transpose_map, (hZ w).1])
  obtain ⟨n, hn⟩ := exists_int_add_mem_unitCube s
  set u : SymIdx r → F := (symOEquiv n : SymIdx r → F)
  set L := symOf u
  have hL : Lᵀ = L := symOf_transpose _
  have hLi : IsIntMat L := isIntMat_symOf (symOEquiv n).2
  set t := s + fun j => (n j : ℝ)
  have ht : t ∈ Set.Icc (0 : JR F r → ℝ) 1 := ⟨fun j => (hn j).1.le, fun j => (hn j).2⟩
  have hZ' := addB_mem hL hZ
  rw [← eisHolR_addB b hb hbpos hL hLi hZ]
  set P : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ := fun w => (Z w).map Complex.im - Y0 w
  have hdecomp : addB L Z = fun w => zPt Y0 t w + Complex.I • (P w).map (fun x => (x : ℂ)) := by
    funext w
    ext i j
    have hx : xMat t w i j = (Z w i j).re + realEmb F w (L i j) := by
      have h1 := congrFun (congrFun (hs w) i) j
      have h2 : (xMat (tOf u) w).map (fun x => (x : ℂ)) = realMat L w := xMat_tOf u w
      have h3 := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply, realMat] at h1 h3
      rw [show t = s + tOf u by rw [tOf_symOEquiv]] at *
      rw [xMat_add, Matrix.add_apply, h1]
      congr 1
      exact_mod_cast h3
    simp only [addB, zPt, P, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hx]
    apply Complex.ext <;> simp
  have hZ0 : zPt Y0 t ∈ siegelHF F r := zPt_mem_siegelHF Y0 hY0 t
  have hterm : ∀ q, ‖holQ b hb hbpos (addB L Z) q‖ ≤ M * G q := by
    intro q
    rw [holQ_eq_out b hb hbpos hZ', hdecomp]
    refine (norm_holTermR_le b hb q.out hZ0 P hZY).trans ?_
    rw [← holQ_eq_out b hb hbpos hZ0]
    exact hbd _ (fun w => ⟨t, ht, rfl⟩) q
  have hsumm : Summable fun q => ‖holQ b hb hbpos (addB L Z) q‖ :=
    (hG.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖eisHolR b hb hbpos (addB L Z)‖ ≤ ∑' q, ‖holQ b hb hbpos (addB L Z) q‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' q, M * G q := hsumm.tsum_le_tsum hterm (hG.mul_left M)
    _ = M * ∑' q, G q := tsum_mul_left

end Bound

end QuadFormsKB.SiegelWeil.Forms
