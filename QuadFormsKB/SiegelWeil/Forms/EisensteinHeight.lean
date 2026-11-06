/-
# The height on $\mathrm{Sp}_{2r}(F_v)$ (Siegel–Weil for forms by forms)

**Layer:** local, non-archimedean: every finite place $v$ of a number field $F$, dyadic places included.

**The height.** For $g = \begin{pmatrix}A&B\\C&D\end{pmatrix} \in \mathrm{Sp}_{2r}(F_v)$ let $(C\ D)$ be its bottom $r\times 2r$ block (`bottomRows`) and
$$\Lambda_g = \{U\,{}^t(C\ D) : U \in M_{2\times 2r}(\mathcal O_v)\} \subseteq M_{2\times r}(F_v)\quad(\texttt{latH}),\qquad
  \|g\|_v = \Big(\frac{\operatorname{vol}(\Lambda_g)}{\operatorname{vol}(M_{2\times r}(\mathcal O_v))}\Big)^{1/2}\quad(\texttt{htR}).$$
($\Lambda_g$ is two copies of the lattice spanned by the columns of $(C\ D)$, written in rows; two rows, rather than one, because the
change of variables of `Weil/Genus/HaarGL.lean` is stated on $M_{2m\times r}$.) This is the height for $r = 1$
($\|g\|_v = \max(|c|_v, |d|_v)$) in a form that needs neither minors nor an Iwasawa decomposition.

**Results.**
* `htR_mul_of_mem_siegelP` (**the parabolic law**): $\|pg\|_v = |\det D_p|_v\,\|g\|_v = |\det A_p|_v^{-1}\|g\|_v$ for $p \in P(F_v)$
  (`vol` of the image under $X \mapsto X\,{}^tD_p$ is $|\det D_p|_v^2\operatorname{vol}$, `cA_eq`).
* `htR_mul_of_int` (**right $\mathrm{Sp}_{2r}(\mathcal O_v)$-invariance**): $\|gk\|_v = \|g\|_v$ when $k$ has entries in $\mathcal O_v$
  ($U \mapsto U\,{}^tk$ permutes $M_{2\times 2r}(\mathcal O_v)$, since $k^{-1} = -J\,{}^tk\,J$ is integral too).
* `htR_eq_one_of_int`: $\|k\|_v = 1$ for $k \in \mathrm{Sp}_{2r}(\mathcal O_v)$ (the bottom block of $k$ has an integral right inverse,
  taken from $k^{-1}$).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (the standard section $\Phi(g, s) = \Phi(g)|a(g)|^{s-s_0}$)
[unverified]; Weil, Acta Math. 113 (1965), §§ 39–41 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.EisensteinParabolic
import QuadFormsKB.Weil.Genus.HaarGL
import QuadFormsKB.Weil.LocalK0

open MeasureTheory Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep WeilRep.LocalData WeilRep.Genus QuadFormsKB.Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r : ℕ}

local notation "Fv" => v.adicCompletion F

/-- The bottom $r\times 2r$ block $(C\ D)$ of $g \in \mathrm{Sp}_{2r}(F_v)$. -/
def bottomRows (g : Sp r Fv) : Matrix (Fin r) (Fin r ⊕ Fin r) Fv :=
  fun i x => (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) (Sum.inr i) x

/-- The integral $2\times 2r$ matrices $M_{2\times 2r}(\mathcal O_v)$. -/
def boxU (r : ℕ) : Set (Matrix (Fin (2 * 1)) (Fin r ⊕ Fin r) Fv) := {U | ∀ i x, ‖U i x‖ ≤ 1}

/-- The integral $2\times r$ matrices $M_{2\times r}(\mathcal O_v)$. -/
def boxX (r : ℕ) : Set (PtG 1 r Fv) := {X | ∀ i j, ‖X i j‖ ≤ 1}

/-- $\Lambda_g = \{U\,{}^t(C\ D) : U \in M_{2\times 2r}(\mathcal O_v)\}$. -/
def latH (g : Sp r Fv) : Set (PtG 1 r Fv) := (fun U => U * (bottomRows v g)ᵀ) '' boxU v r

/-- The measure on $M_{2\times r}(F_v)$: the product of the self-dual measures. -/
abbrev muH (r : ℕ) : Measure (PtG 1 r Fv) := muG (localDataV v) 1 r

/-- **The height** $\|g\|_v = \big(\operatorname{vol}(\Lambda_g)/\operatorname{vol}(M_{2\times r}(\mathcal O_v))\big)^{1/2}$ on $\mathrm{Sp}_{2r}(F_v)$. -/
@[kb "kudla2008" "§1 (the function $|a(g)|$ of the Iwasawa decomposition) [unverified]"]
def htR (g : Sp r Fv) : ℝ := Real.sqrt ((muH v r).real (latH v g) / (muH v r).real (boxX v r))

lemma htR_nonneg (g : Sp r Fv) : 0 ≤ htR v g := Real.sqrt_nonneg _

/-! ### Compactness -/

lemma isCompact_boxU : IsCompact (boxU v r) := by
  have : boxU v r = Set.univ.pi fun _ : Fin (2 * 1) => Set.univ.pi fun _ : Fin r ⊕ Fin r =>
      Metric.closedBall (0 : Fv) 1 := by
    ext U
    exact ⟨fun h i _ x _ => by simpa [Metric.mem_closedBall, dist_zero_right] using h i x,
      fun h i x => by simpa [Metric.mem_closedBall, dist_zero_right] using h i (Set.mem_univ _) x (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

lemma isCompact_boxX : IsCompact (boxX v r) := by
  have : boxX v r = Set.univ.pi fun _ : Fin (2 * 1) => Set.univ.pi fun _ : Fin r =>
      Metric.closedBall (0 : Fv) 1 := by
    ext U
    exact ⟨fun h i _ x _ => by simpa [Metric.mem_closedBall, dist_zero_right] using h i x,
      fun h i x => by simpa [Metric.mem_closedBall, dist_zero_right] using h i (Set.mem_univ _) x (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

lemma isCompact_latH (g : Sp r Fv) : IsCompact (latH v g) :=
  (isCompact_boxU v).image (by fun_prop)

lemma measurableSet_latH (g : Sp r Fv) : MeasurableSet (latH v g) := (isCompact_latH v g).isClosed.measurableSet

/-! ### The change of variables -/

instance : (localDataV v).μ.IsAddHaarMeasure := inferInstanceAs ((selfDualV v).IsAddHaarMeasure)

lemma md_eq_norm' {x : Fv} (hx : x ≠ 0) : (localDataV v).md x = ‖x‖ := modK_eq_norm v hx

/-- **The volume of $SA$:** $\operatorname{vol}(\{XA : X \in S\}) = |\det A|_v^2\operatorname{vol}(S)$ for a measurable $S \subseteq M_{2\times r}(F_v)$. -/
lemma muH_real_image_mulRight (A : GL (Fin r) Fv) {S : Set (PtG 1 r Fv)} (hS : MeasurableSet S) :
    (muH v r).real ((fun X => X * (A : Matrix (Fin r) (Fin r) Fv)) '' S) =
      ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ ^ 2 * (muH v r).real S := by
  set S' := (fun X : PtG 1 r Fv => X * (A : Matrix (Fin r) (Fin r) Fv)) '' S
  have hS' : S' = (fun X : PtG 1 r Fv => X * ((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv)) ⁻¹' S := by
    ext X
    simp only [S', Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]; exact hY
    · intro h
      exact ⟨_, h, by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]⟩
  have hmeas' : MeasurableSet S' := by
    rw [hS']
    exact hS.preimage (by fun_prop : Continuous fun X : PtG 1 r Fv =>
      X * ((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv)).measurable
  have key := integral_comp_mulRight (m := 1) (muH v r) A (S'.indicator fun _ => (1 : ℂ))
  have hind : ∀ X : PtG 1 r Fv, S'.indicator (fun _ => (1 : ℂ)) (X * (A : Matrix (Fin r) (Fin r) Fv)) =
      S.indicator (fun _ => (1 : ℂ)) X := by
    intro X
    have : X * (A : Matrix (Fin r) (Fin r) Fv) ∈ S' ↔ X ∈ S := by
      rw [hS', Set.mem_preimage, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    by_cases hX : X ∈ S
    · rw [Set.indicator_of_mem (this.mpr hX), Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem (fun h => hX (this.mp h)), Set.indicator_of_notMem hX]
  simp only [hind] at key
  have hc : ∀ T : Set (PtG 1 r Fv), MeasurableSet T →
      ∫ X, T.indicator (fun _ => (1 : ℂ)) X ∂muH v r = (((muH v r).real T : ℝ) : ℂ) := by
    intro T hT
    have e : (fun X => T.indicator (fun _ => (1 : ℂ)) X) = fun X => ((T.indicator (1 : PtG 1 r Fv → ℝ) X : ℝ) : ℂ) := by
      funext X; by_cases hX : X ∈ T <;> simp [hX]
    rw [e, integral_complex_ofReal, integral_indicator_one hT]
  rw [hc S hS, hc S' hmeas'] at key
  have hcA := cA_eq (D := localDataV v) (m := 1) (isModel_V v) (by
    show (Metric.closedBall (0 : Fv) 1).indicator (fun _ => (1 : ℂ)) ∈ SBK Fv
    exact indicator_closedBall_mem_SBK 0 one_pos) A
  have hdet : (A : Matrix (Fin r) (Fin r) Fv).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rw [md_eq_norm' v hdet] at hcA
  have hpos : (0 : ℝ) < cA 1 A := by exact_mod_cast cA_pos A
  rw [Complex.real_smul] at key
  have key' : (muH v r).real S = (cA 1 A : ℝ)⁻¹ * (muH v r).real S' := by exact_mod_cast key
  rw [key', ← mul_assoc, ← hcA, mul_inv_cancel₀ hpos.ne', one_mul]

/-! ### The parabolic law -/

lemma bottomRows_mul_of_mem_siegelP {p : Sp r Fv} (hp : p ∈ siegelP r Fv) (g : Sp r Fv) :
    bottomRows v (p * g) = blockD p * bottomRows v g := by
  obtain ⟨hC, hD⟩ := blockCD_mul_of_mem_siegelP hp g
  funext i x
  rcases x with j | j
  · have := congrFun (congrFun hC i) j
    simp only [blockC, toBlocks₂₁, of_apply] at this
    show ((p * g : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) (Sum.inr i) (Sum.inl j) = _
    rw [this]; simp [bottomRows, mul_apply]
  · have := congrFun (congrFun hD i) j
    simp only [blockD, toBlocks₂₂, of_apply] at this
    show ((p * g : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) (Sum.inr i) (Sum.inr j) = _
    rw [this]; simp [bottomRows, blockD, toBlocks₂₂, mul_apply]

/-- The block $D_p$ of $p \in P$ as an element of $\mathrm{GL}_r$ (transposed: ${}^tD_p = A_p^{-1}$). -/
def dT {p : Sp r Fv} (hp : p ∈ siegelP r Fv) : GL (Fin r) Fv := (levi hp)⁻¹

lemma dT_coe {p : Sp r Fv} (hp : p ∈ siegelP r Fv) :
    ((dT v hp : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) = (blockD p)ᵀ := rfl

lemma latH_mul_of_mem_siegelP {p : Sp r Fv} (hp : p ∈ siegelP r Fv) (g : Sp r Fv) :
    latH v (p * g) = (fun X => X * ((dT v hp : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv)) '' latH v g := by
  rw [latH, latH, Set.image_image, bottomRows_mul_of_mem_siegelP v hp, dT_coe, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **The parabolic law of the height**: $\|pg\|_v = |\det D_p|_v\,\|g\|_v$ for $p \in P(F_v)$ ($= |\det A_p|_v^{-1}\|g\|_v$). -/
@[kb "kudla2008" "§1 ($|a(pg)| = |a(p)|\\,|a(g)|$) [unverified]"]
theorem htR_mul_of_mem_siegelP {p : Sp r Fv} (hp : p ∈ siegelP r Fv) (g : Sp r Fv) :
    htR v (p * g) = ‖(blockD p).det‖ * htR v g := by
  rw [htR, htR, latH_mul_of_mem_siegelP v hp, muH_real_image_mulRight v _ (measurableSet_latH v g), dT_coe,
    det_transpose, mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- $\|pg\|_v = |\det A_p|_v^{-1}\|g\|_v$. -/
theorem htR_mul_of_mem_siegelP' {p : Sp r Fv} (hp : p ∈ siegelP r Fv) (g : Sp r Fv) :
    htR v (p * g) = ‖(blockA p).det‖⁻¹ * htR v g := by
  rw [htR_mul_of_mem_siegelP v hp]
  congr 1
  have h := det_blockD_of_mem_siegelP hp
  have hA : (blockA p).det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  exact eq_inv_of_mul_eq_one_left (by rw [← norm_mul, h, norm_one])

/-! ### Integral elements -/

/-- $g \in \mathrm{Sp}_{2r}(F_v)$ has all entries in $\mathcal O_v$. -/
def IsIntSp (g : Sp r Fv) : Prop := ∀ x y, ‖(g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) x y‖ ≤ 1

lemma norm_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → Fv) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one hf

lemma isIntSp_mul {g h : Sp r Fv} (hg : IsIntSp v g) (hh : IsIntSp v h) : IsIntSp v (g * h) := by
  intro x y
  show ‖((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * (h : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)) x y‖ ≤ 1
  rw [mul_apply]
  exact norm_sum_le_one v _ _ fun z _ => by rw [norm_mul]; exact mul_le_one₀ (hg x z) (norm_nonneg _) (hh z y)

lemma isIntSp_J : ∀ x y, ‖Matrix.J (Fin r) Fv x y‖ ≤ 1 := by
  intro x y
  rcases x with i | i <;> rcases y with j | j <;>
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]

/-- The inverse of an integral symplectic matrix is integral ($g^{-1} = -J\,{}^tg\,J$). -/
lemma isIntSp_inv {g : Sp r Fv} (hg : IsIntSp v g) : IsIntSp v g⁻¹ := by
  intro x y
  rw [SymplecticGroup.coe_inv, Matrix.neg_mul, Matrix.neg_mul, neg_apply, norm_neg, mul_apply]
  refine norm_sum_le_one v _ _ fun z _ => ?_
  rw [norm_mul, mul_apply]
  refine mul_le_one₀ (norm_sum_le_one v _ _ fun w _ => ?_) (norm_nonneg _) (isIntSp_J v z y)
  rw [norm_mul, transpose_apply]
  exact mul_le_one₀ (isIntSp_J v x w) (norm_nonneg _) (hg z w)

lemma bottomRows_mul (g k : Sp r Fv) :
    bottomRows v (g * k) = bottomRows v g * (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) := by
  ext i x; rfl

/-- $U \mapsto U\,{}^tk$ maps $M_{2\times 2r}(\mathcal O_v)$ into itself for integral $k$. -/
lemma mul_transpose_mem_boxU {k : Sp r Fv} (hk : IsIntSp v k) {U : Matrix (Fin (2 * 1)) (Fin r ⊕ Fin r) Fv}
    (hU : U ∈ boxU v r) : U * (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ ∈ boxU v r := by
  intro i x
  rw [mul_apply]
  exact norm_sum_le_one v _ _ fun z _ => by
    rw [norm_mul, transpose_apply]; exact mul_le_one₀ (hU i z) (norm_nonneg _) (hk x z)

/-- **Right invariance**: $\Lambda_{gk} = \Lambda_g$ for $k \in \mathrm{Sp}_{2r}(\mathcal O_v)$. -/
lemma latH_mul_of_int (g : Sp r Fv) {k : Sp r Fv} (hk : IsIntSp v k) : latH v (g * k) = latH v g := by
  have hki := isIntSp_inv v hk
  have hkk : (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ * ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ = 1 := by
    rw [← transpose_mul]
    have : ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
    rw [this, transpose_one]
  have hkk' : ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ * (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ = 1 := by
    rw [← transpose_mul]
    have : (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
    rw [this, transpose_one]
  ext X
  simp only [latH, Set.mem_image, bottomRows_mul, transpose_mul]
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U * (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ, mul_transpose_mem_boxU v hk hU, by rw [Matrix.mul_assoc]⟩
  · rintro ⟨U, hU, rfl⟩
    refine ⟨U * ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv)ᵀ, mul_transpose_mem_boxU v hki hU, ?_⟩
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U, hkk', Matrix.mul_one]

/-- **The height is right $\mathrm{Sp}_{2r}(\mathcal O_v)$-invariant**: $\|gk\|_v = \|g\|_v$ for $k$ with entries in $\mathcal O_v$. -/
@[kb "kudla2008" "§1 ($|a(gk)| = |a(g)|$ for $k \\in K$) [unverified]"]
theorem htR_mul_of_int (g : Sp r Fv) {k : Sp r Fv} (hk : IsIntSp v k) : htR v (g * k) = htR v g := by
  rw [htR, htR, latH_mul_of_int v g hk]

lemma muH_real_boxX_pos : 0 < (muH v r).real (boxX v r) := by
  have hopen : IsOpen (boxX v r) := by
    have : boxX v r = Set.univ.pi fun _ : Fin (2 * 1) => Set.univ.pi fun _ : Fin r =>
        Metric.closedBall (0 : Fv) 1 := by
      ext U
      exact ⟨fun h i _ x _ => by simpa [Metric.mem_closedBall, dist_zero_right] using h i x,
        fun h i x => by simpa [Metric.mem_closedBall, dist_zero_right] using h i (Set.mem_univ _) x (Set.mem_univ _)⟩
    rw [this]
    refine isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ?_
    exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hne : (boxX v r).Nonempty := ⟨0, fun i j => by simp⟩
  haveI : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  haveI : (Measure.pi fun _ : Fin r => (localDataV v).μ).IsOpenPosMeasure := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : Fin r => (localDataV v).μ) := inferInstance
  have : (muH v r).IsOpenPosMeasure :=
    (inferInstance : (Measure.pi fun _ : Fin (2 * 1) => Measure.pi fun _ : Fin r =>
      (localDataV v).μ : Measure (Fin (2 * 1) → Fin r → Fv)).IsOpenPosMeasure)
  exact ENNReal.toReal_pos (hopen.measure_pos _ hne).ne' (isCompact_boxX v).measure_lt_top.ne

/-- **$\|k\|_v = 1$ on $\mathrm{Sp}_{2r}(\mathcal O_v)$**: $\Lambda_k = M_{2\times r}(\mathcal O_v)$, since the bottom block of $k$ has the integral
right inverse given by the last $r$ columns of $k^{-1}$. -/
@[kb "kudla2008" "§1 ($|a(k)| = 1$ for $k \\in K$) [unverified]"]
theorem htR_eq_one_of_int {k : Sp r Fv} (hk : IsIntSp v k) : htR v k = 1 := by
  have hki := isIntSp_inv v hk
  set M : Matrix (Fin r ⊕ Fin r) (Fin r) Fv := fun x j => ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) x (Sum.inr j)
  have hBM : bottomRows v k * M = 1 := by
    have : (k : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) * ((k⁻¹ : Sp r Fv) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
    funext i j
    have h := congrFun (congrFun this (Sum.inr i)) (Sum.inr j)
    rw [mul_apply] at h
    rw [mul_apply]
    simpa [bottomRows, M, Matrix.one_apply] using h
  have hL : latH v k = boxX v r := by
    ext X
    constructor
    · rintro ⟨U, hU, rfl⟩ i j
      show ‖(U * (bottomRows v k)ᵀ) i j‖ ≤ 1
      rw [mul_apply]
      exact norm_sum_le_one v _ _ fun z _ => by
        rw [norm_mul, transpose_apply]; exact mul_le_one₀ (hU i z) (norm_nonneg _) (hk _ z)
    · intro hX
      refine ⟨X * Mᵀ, fun i x => ?_, ?_⟩
      · rw [mul_apply]
        exact norm_sum_le_one v _ _ fun z _ => by
          rw [norm_mul, transpose_apply]; exact mul_le_one₀ (hX i z) (norm_nonneg _) (hki x _)
      · show X * Mᵀ * (bottomRows v k)ᵀ = X
        rw [Matrix.mul_assoc, ← transpose_mul, hBM, transpose_one, Matrix.mul_one]
  rw [htR, hL, div_self (muH_real_boxX_pos v).ne', Real.sqrt_one]

end QuadFormsKB.SiegelWeil.Forms
