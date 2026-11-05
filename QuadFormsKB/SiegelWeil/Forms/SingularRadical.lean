/-
# Moving a singular form to one with zero first row (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$ whose ring of integers $\mathcal O_F$ is a principal ideal domain; linear algebra
over $\mathcal O_F$ (no analysis).

**Setting.** $T$ is a quadratic form in $r + 1$ variables over $F$ with Gram matrix $G = T_G$ (`gramT T`), and $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$
is a matrix such that $U$ and $U^{-1}$ have entries in $\mathcal O_F$ (`IsIntegralMat`) and $\det U = 1$. The form $T[U]$ is `T.compMat U`, with
Gram matrix $U^{\mathsf T} G U$. The new variable is the first one (index $0$).

**Results.**
* `eq_extZero_of_gramT_row`: if the first row of $T_G$ is zero, then $T$ equals `extZero (tailForm T)`;
* **`exists_SL_int_gramT_row_zero`**: if $\det T_G = 0$, there is $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$ such that the first row of the Gram
  matrix of $T[U]$ vanishes. A nonzero vector of the radical $\ker T_G$ is scaled to a primitive vector of $\mathcal O_F^{r+1}$ (via the Smith
  normal form of the line it spans, over the principal ideal domain), completed to a basis of $\mathcal O_F^{r+1}$ as the first column of $U$,
  and the determinant is corrected to $1$ by rescaling the second column by a unit (the case $r = 0$ is trivial);
* **`exists_SL_int_compMat_eq_extZero`**: for singular $T$, some $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$ has $T[U] = \mathrm{extZero}(\mathrm{tail}(T[U]))$.

Together with `coeff_compMat_eq` and `coeff_extZero_eq_zero_of_phi` (`FourierPhi.lean`), this reaches every singular $T$ in the Siegel $\Phi$-operator argument.

Source: standard linear algebra over a principal ideal domain (completion of a unimodular vector); used for Siegel's $\Phi$-operator argument,
Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.FourierPhi

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- If the first row of the Gram matrix of $T$ vanishes, then $T = \mathrm{extZero}(\mathrm{tail}\,T)$. -/
lemma eq_extZero_of_gramT_row (T : QuadForm F (r + 1)) (h : ∀ j, gramT T 0 j = 0) :
    T = extZero (tailForm T) := by
  have hc00 : T.coeff 0 0 = 0 := by
    have := h 0
    simp only [gramT, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul] at this
    linear_combination this
  have hc0 : ∀ j' : Fin r, T.coeff 0 j'.succ = 0 := by
    intro j'
    have h1 := h j'.succ
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

/-- **Completion of a radical vector.** If $G w = 0$ for a nonzero integral vector $w$ (with $G$ over $F$), then there is a matrix $P$ over
$\mathcal O_F$ with unit determinant whose first column lies in $\ker G$. -/
lemma exists_unit_det_col_zero_mem_ker [IsPrincipalIdealRing (𝓞 F)] (G : Matrix (Fin (r + 1)) (Fin (r + 1)) F)
    (w : Fin (r + 1) → 𝓞 F) (hw : w ≠ 0) (hker : G *ᵥ (fun i => algebraMap (𝓞 F) F (w i)) = 0) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 F), IsUnit P.det ∧
      G *ᵥ (fun i => algebraMap (𝓞 F) F (P i 0)) = 0 := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun (𝓞 F) (Fin (r + 1)))
    (Submodule.span (𝓞 F) {w})
  have : Nontrivial (Submodule.span (𝓞 F) {w}) :=
    ⟨⟨⟨w, Submodule.mem_span_singleton_self w⟩, 0, fun h => hw (congrArg Subtype.val h)⟩⟩
  obtain ⟨i⟩ := S.bN.index_nonempty
  have hsnf := S.snf i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (S.bN i).2
  have ha : S.a i ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsnf
    exact S.bN.ne_zero i (Subtype.ext hsnf)
  set x : Fin (r + 1) → 𝓞 F := S.bM (S.f i) with hx
  have hax : S.a i • x = c • w := by
    rw [hc, hsnf]
  have hφ : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective (𝓞 F) F
  have hGx : G *ᵥ (fun k => algebraMap (𝓞 F) F (x k)) = 0 := by
    have h1 : (algebraMap (𝓞 F) F (S.a i)) • (G *ᵥ (fun k => algebraMap (𝓞 F) F (x k))) = 0 := by
      rw [← Matrix.mulVec_smul]
      have : (algebraMap (𝓞 F) F (S.a i)) • (fun k => algebraMap (𝓞 F) F (x k)) =
          (algebraMap (𝓞 F) F c) • (fun k => algebraMap (𝓞 F) F (w k)) := by
        funext k
        have := congrFun hax k
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [← map_mul, ← map_mul, this]
      rw [this, Matrix.mulVec_smul, hker, smul_zero]
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd (hφ (by simpa using h)) ha
    · exact h
  let b' := S.bM.reindex (Equiv.swap (0 : Fin (r + 1)) (S.f i))
  refine ⟨(Pi.basisFun (𝓞 F) (Fin (r + 1))).toMatrix b', ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact Module.Basis.isUnit_det _ _
  · have h0 : ∀ k, ((Pi.basisFun (𝓞 F) (Fin (r + 1))).toMatrix b') k 0 = x k := by
      intro k
      simp [Module.Basis.toMatrix_apply, b', hx]
    simpa only [h0] using hGx

/-- A matrix over $\mathcal O_F$ with unit determinant, in dimension at least two, can be changed in its second column only to have
determinant $1$. -/
lemma exists_det_one_same_col_zero {m : ℕ} (P : Matrix (Fin (m + 2)) (Fin (m + 2)) (𝓞 F)) (hP : IsUnit P.det) :
    ∃ P' : Matrix (Fin (m + 2)) (Fin (m + 2)) (𝓞 F), P'.det = 1 ∧ ∀ i, P' i 0 = P i 0 := by
  classical
  obtain ⟨u, hu⟩ := hP
  refine ⟨P * Matrix.diagonal (fun k => if k = 1 then ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) else 1), ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ (1 : Fin (m + 2))
      (fun _ => ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) ]
    simp [← hu]
  · intro i
    rw [Matrix.mul_diagonal]
    simp

/-- **Main lemma.** If $\det T_G = 0$, there is $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$ with the first row of the Gram matrix of $T[U]$ zero. -/
theorem exists_SL_int_gramT_row_zero [IsPrincipalIdealRing (𝓞 F)] (T : QuadForm F (r + 1))
    (hT : (gramT T).det = 0) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) F, IsIntegralMat U ∧ IsIntegralMat U⁻¹ ∧ U.det = 1 ∧
      ∀ j, gramT (T.compMat U) 0 j = 0 := by
  classical
  -- a nonzero integral radical vector
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) v
  choose w hw using hb
  have hb0 : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hwv : (fun i => algebraMap (𝓞 F) F (w i)) = (b : 𝓞 F) • v := by
    funext i; exact hw i
  have hφ : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective (𝓞 F) F
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hwv
    have : (b : 𝓞 F) • v = 0 := by rw [← hwv]; funext i; simp
    rcases smul_eq_zero.mp this with h | h
    · exact hb0 h
    · exact hv h
  have hker : gramT T *ᵥ (fun i => algebraMap (𝓞 F) F (w i)) = 0 := by
    rw [hwv, Matrix.mulVec_smul, hGv, smul_zero]
  obtain ⟨P, hPu, hPker⟩ := exists_unit_det_col_zero_mem_ker (gramT T) w hw0 hker
  -- the matrix with determinant one
  obtain ⟨P', hP'det, hP'ker⟩ : ∃ P' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 F), P'.det = 1 ∧
      gramT T *ᵥ (fun i => algebraMap (𝓞 F) F (P' i 0)) = 0 := by
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      have hG : gramT T = 0 := by
        ext i j
        have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst hi; subst hj
        simpa using hT
      rw [hG, Matrix.zero_mulVec]
    | succ m =>
      obtain ⟨P', h1, h2⟩ := exists_det_one_same_col_zero P hPu
      exact ⟨P', h1, by simpa only [h2] using hPker⟩
  set U : Matrix (Fin (r + 1)) (Fin (r + 1)) F := (algebraMap (𝓞 F) F).mapMatrix P' with hU
  have hUdet : U.det = 1 := by
    rw [hU, ← RingHom.map_det, hP'det, map_one]
  have hUinv : U⁻¹ = (algebraMap (𝓞 F) F).mapMatrix P'.adjugate := by
    rw [Matrix.inv_def, hUdet, Ring.inverse_one, one_smul, hU, RingHom.map_adjugate]
  refine ⟨U, fun i j => ⟨P' i j, rfl⟩, ?_, hUdet, ?_⟩
  · rw [hUinv]; exact fun i j => ⟨P'.adjugate i j, rfl⟩
  · intro j
    have hc : ∀ l, ∑ k, U k 0 * gramT T k l = 0 := by
      intro l
      have := congrFun hP'ker l
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs : gramT T k l = gramT T l k := by
        have := congrFun (congrFun (gramT_transpose T) k) l
        simpa using this.symm
      rw [hs, mul_comm]; rfl
    rw [gramT_compMat, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : (Uᵀ * gramT T) 0 l = 0 := by
      simpa [Matrix.mul_apply] using hc l
    rw [this, zero_mul]

/-- **Corollary.** For singular $T$ some $U \in \mathrm{SL}_{r+1}(\mathcal O_F)$ has $T[U] = \mathrm{extZero}(\mathrm{tail}(T[U]))$. -/
@[kb "freitag1983" "Ch. I (degenerate Fourier coefficients) [unverified]"]
theorem exists_SL_int_compMat_eq_extZero [IsPrincipalIdealRing (𝓞 F)] (T : QuadForm F (r + 1))
    (hT : (gramT T).det = 0) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) F, IsIntegralMat U ∧ IsIntegralMat U⁻¹ ∧ U.det = 1 ∧
      T.compMat U = extZero (tailForm (T.compMat U)) := by
  obtain ⟨U, h1, h2, h3, h4⟩ := exists_SL_int_gramT_row_zero T hT
  exact ⟨U, h1, h2, h3, eq_extZero_of_gramT_row _ h4⟩

end QuadFormsKB.SiegelWeil.Forms
