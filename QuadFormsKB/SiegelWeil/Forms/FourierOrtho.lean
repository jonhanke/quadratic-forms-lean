/-
# Orthogonality of the characters $e_T$: coefficients of an absolutely convergent expansion

**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $f$ is a function on $\mathbb H_r^d$ with an absolutely convergent expansion
$f(Z) = \sum_Ta(T)\,e_T(Z)$ over the forms $T$ in $r$ variables over $F$ (`QuadForm F r`), the coefficients $a(T)$ vanishing unless $T$ has
coefficients in $\mathcal O_F$. $c_{T_0}(f, Y)$ = `coeffR f T₀ Y` is the $T_0$-th Fourier coefficient at height $Y$ over the unit cube of the
coordinates $t$ of $X(t) \in \mathrm{Sym}_r(\mathbb R)^d$.

**Idea.** Since $Z(t) = X(t) + iY$ and $|e_T(X(t))| = 1$, each term $a(T)e_T(Z(t))\chi_{T_0}(t)$ has the $t$-independent norm
$|a(T)e_T(iY)|$, summable by hypothesis; so sum and integral may be exchanged. For $T$ with coefficients in $\mathcal O_F$ the function
$t \mapsto e_T(X(t))\chi_{T_0}(t)$ is $\mathbb Z^J$-periodic, and for $T \ne T_0$ there is a real shift $s_0$ with
$\chi_T(s_0) = -\chi_{T_0}(s_0)$ (take $X(s_0)$ supported at one place, proportional to $\sigma(T_G - T_{0,G})$), so its integral over the cube
vanishes. The term $T = T_0$ is constant, equal to $a(T_0)e_{T_0}(iY)$.

**Results.**
* `exists_shift_ne`: for $T \ne T'$ there are coordinates $s_0$ with $\chi_T(s_0) = -\chi_{T'}(s_0)$;
* **`coeffR_of_hasSum`**: $c_{T_0}(f, Y) = a(T_0)\,e_{T_0}(iY)$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (Fourier expansions) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinLowerCell

open Matrix NumberField IsDedekindDomain Filter MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

open Classical in
/-- $\chi_T(s)$ for $X(s)$ supported at the single place $w_0$. -/
lemma chiT_of_supp (T : QuadForm F r) (w0 : InfinitePlace F) (X : Matrix (Fin r) (Fin r) ℝ) (s : JR F r → ℝ)
    (hs : ∀ w, xMat s w = if w = w0 then X else 0) :
    chiT T s = Complex.exp (2 * Real.pi * Complex.I *
      -((∑ i, ∑ j, realEmb F w0 (gramT T i j) * X j i : ℝ) : ℂ)) := by
  unfold chiT eT trPair
  congr 2
  rw [Finset.sum_eq_single w0]
  · beta_reduce
    rw [hs, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    push_cast
    simp only [Matrix.neg_apply, Matrix.map_apply, mul_neg, Finset.sum_neg_distrib]
  · intro w _ hw
    beta_reduce
    rw [hs, ite_eq_right_iff.mpr (fun h => absurd h hw)]
    simp
  · intro h; exact absurd (Finset.mem_univ w0) h

/-- **Two distinct forms are separated by a real shift**: $\chi_T(s_0) = -\chi_{T'}(s_0)$. -/
lemma exists_shift_ne (T T' : QuadForm F r) (hne : T ≠ T') :
    ∃ s0 : JR F r → ℝ, chiT T s0 = -chiT T' s0 := by
  classical
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  set A : Matrix (Fin r) (Fin r) ℝ := (gramT T - gramT T').map (realEmb F w0) with hA
  have hAs : Aᵀ = A := by
    rw [hA, ← transpose_map, transpose_sub, gramT_transpose, gramT_transpose]
  have hAne : ∃ i j, A i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply gramT_injective
    ext i j
    have := hcon i j
    simp only [hA, Matrix.map_apply, Matrix.sub_apply] at this
    have h0 : gramT T i j - gramT T' i j = 0 := (realEmb F w0).injective (by rw [this, map_zero])
    exact sub_eq_zero.mp h0
  obtain ⟨i0, j0, hij0⟩ := hAne
  set S : ℝ := ∑ i, ∑ j, A i j * A i j with hS
  have hSpos : 0 < S := by
    have h1 : 0 < A i0 j0 * A i0 j0 := mul_self_pos.mpr hij0
    have h2 : A i0 j0 * A i0 j0 ≤ ∑ j, A i0 j * A i0 j :=
      Finset.single_le_sum (f := fun j => A i0 j * A i0 j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ j0)
    have h3 : ∑ j, A i0 j * A i0 j ≤ S :=
      Finset.single_le_sum (f := fun i => ∑ j, A i j * A i j)
        (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _) (Finset.mem_univ i0)
    linarith
  set X : Matrix (Fin r) (Fin r) ℝ := (1 / (2 * S)) • A with hX
  have hXs : Xᵀ = X := by rw [hX, transpose_smul, hAs]
  obtain ⟨s0, hs0⟩ := exists_xMat_eq (fun w => if w = w0 then X else 0) (fun w => by
    split_ifs <;> simp [hXs])
  refine ⟨s0, ?_⟩
  rw [chiT_of_supp T w0 X s0 hs0, chiT_of_supp T' w0 X s0 hs0]
  have hp : (∑ i, ∑ j, realEmb F w0 (gramT T i j) * X j i) =
      (∑ i, ∑ j, realEmb F w0 (gramT T' i j) * X j i) + 1 / 2 := by
    have e1 : (∑ i, ∑ j, realEmb F w0 (gramT T i j) * X j i) -
        (∑ i, ∑ j, realEmb F w0 (gramT T' i j) * X j i) = ∑ i, ∑ j, A i j * X j i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hA, Matrix.map_apply, Matrix.sub_apply, map_sub]; ring
    have e2 : ∑ i, ∑ j, A i j * X j i = 1 / 2 := by
      have : ∀ i j, A i j * X j i = (1 / (2 * S)) * (A i j * A i j) := fun i j => by
        have := congrFun (congrFun hAs i) j
        simp only [hX, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this ⊢
        rw [this]; ring
      simp_rw [this, ← Finset.mul_sum]
      rw [← hS]; field_simp
    linarith
  have hk : ∀ P : ℂ, Complex.exp (2 * Real.pi * Complex.I * -(P + ((1 / 2 : ℝ) : ℂ))) =
      -Complex.exp (2 * Real.pi * Complex.I * -P) := fun P => by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * -(P + ((1 / 2 : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * -P + -(Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg (Real.pi * Complex.I), Complex.exp_pi_mul_I]
    norm_num
  rw [hp, Complex.ofReal_add]
  exact hk _

lemma eT_xMat (T : QuadForm F r) (t : JR F r → ℝ) :
    eT T (fun w => (xMat t w).map (fun x => (x : ℂ))) = (chiT T t)⁻¹ := by
  unfold chiT
  rw [← eT_neg]
  congr 1
  funext w
  simp

lemma norm_eT_xMat (T : QuadForm F r) (t : JR F r → ℝ) :
    ‖eT T (fun w => (xMat t w).map (fun x => (x : ℂ)))‖ = 1 := by
  rw [eT_xMat, norm_inv, norm_chiT, inv_one]

lemma eT_zPt (T : QuadForm F r) (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (t : JR F r → ℝ) :
    eT T (zPt Y t) =
      (chiT T t)⁻¹ * eT T (fun w => (Y w).map (fun y => (y : ℂ) * Complex.I)) := by
  rw [← eT_xMat, ← eT_add]
  rfl

/-- **Orthogonality**: if $f(Z) = \sum_Ta(T)e_T(Z)$ converges absolutely on $\mathbb H_r^d$ with $a$ supported on forms with coefficients in
$\mathcal O_F$, then for $T_0$ with coefficients in $\mathcal O_F$ the $T_0$-th coefficient at height $Y$ is $c_{T_0}(f, Y) = a(T_0)e_{T_0}(iY)$. -/
@[kb "freitag1983" "Ch. I (Fourier coefficients of Siegel modular forms) [unverified]"]
theorem coeffR_of_hasSum {a : QuadForm F r → ℂ} {f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (hsum : ∀ Z ∈ siegelHF F r, Summable fun T => ‖a T * eT T Z‖)
    (hexp : ∀ Z ∈ siegelHF F r, HasSum (fun T => a T * eT T Z) (f Z))
    (hint : ∀ T, a T ≠ 0 → IsIntMat T.coeff)
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef)
    (T₀ : QuadForm F r) (hT₀ : IsIntMat T₀.coeff) :
    coeffR f T₀ Y = a T₀ * eT T₀ (fun w => (Y w).map (fun y => (y : ℂ) * Complex.I)) := by
  classical
  set e0 : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ := fun w => (Y w).map (fun y => (y : ℂ) * Complex.I) with he0
  set g : QuadForm F r → (JR F r → ℝ) → ℂ := fun T t => a T * eT T (zPt Y t) * chiT T₀ t with hg
  have hgeq : ∀ T t, g T t = (a T * eT T e0) * ((chiT T t)⁻¹ * chiT T₀ t) := by
    intro T t; simp only [hg, eT_zPt]; ring
  have hgn : ∀ T t, ‖g T t‖ = ‖a T * eT T e0‖ := by
    intro T t
    rw [hgeq]; simp only [norm_mul, norm_inv, norm_chiT, inv_one, mul_one]
  have hG : Summable fun T => ‖a T * eT T e0‖ := by
    refine (hsum (zPt Y 0) (zPt_mem_siegelHF Y hY 0)).congr fun T => ?_
    rw [← hgn T 0]
    simp only [hg, norm_mul, norm_chiT, mul_one]
  have hcont : ∀ T, Continuous (g T) := fun T => by
    have : g T = fun t => (a T * eT T e0) * ((chiT T t)⁻¹ * chiT T₀ t) := funext (hgeq T)
    rw [this]
    exact continuous_const.mul (((continuous_chiT T).inv₀ fun t => by
      rw [← norm_pos_iff, norm_chiT]; norm_num).mul (continuous_chiT T₀))
  have hfun : ∀ t, f (zPt Y t) * chiT T₀ t = ∑' T, g T t := fun t => by
    rw [← (hexp _ (zPt_mem_siegelHF Y hY t)).tsum_eq, ← tsum_mul_right]
  have h1 : coeffR f T₀ Y = ∑' T, ∫ t in unitCube (JR F r), g T t := by
    rw [← integral_unitCube_tsum g (fun T => ‖a T * eT T e0‖) hG hcont
      (fun T t _ => (hgn T t).le)]
    unfold coeffR
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => hfun t)
  rw [h1]
  have hvol : ∀ C : ℂ, ∫ t in unitCube (JR F r), C = C := fun C => by
    rw [setIntegral_const, measureReal_def, volume_unitCube, ENNReal.toReal_one, one_smul]
  refine (tsum_eq_single T₀ fun T hT => ?_).trans ?_
  · by_cases ha : a T = 0
    · simp [hgeq, ha]
    · have hTi := hint T ha
      simp_rw [hgeq]
      rw [integral_const_mul]
      have h0 : ∫ t in unitCube (JR F r), ((chiT T t)⁻¹ * chiT T₀ t) = 0 := by
        obtain ⟨s0, hs0⟩ := exists_shift_ne T T₀ hT
        refine integral_unitCube_eq_zero_of_shift _ (fun n t => ?_) s0 (c := -1) (by norm_num) (fun t => ?_)
        · rw [chiT_add_int T hTi, chiT_add_int T₀ hT₀]
        · have n1 : chiT T t ≠ 0 := by rw [← norm_pos_iff, norm_chiT]; norm_num
          have n2 : chiT T₀ s0 ≠ 0 := by rw [← norm_pos_iff, norm_chiT]; norm_num
          rw [chiT_add, chiT_add, hs0]
          field_simp
      rw [h0, mul_zero]
  · have : ∀ t, g T₀ t = a T₀ * eT T₀ e0 := fun t => by
      rw [hgeq]
      have : chiT T₀ t ≠ 0 := by rw [← norm_pos_iff, norm_chiT]; norm_num
      field_simp
    simp_rw [this]
    exact hvol _

end QuadFormsKB.SiegelWeil.Forms
