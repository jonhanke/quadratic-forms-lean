import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC
import QuadFormsKB.Tamagawa.SplitForm
import QuadFormsKB.Tamagawa.Measure.Weil.ReflectionSection

/-!
# The archimedean orbital identity at a complex place

Let $Q = \langle c\rangle \perp Q'$ (`splitForm c Q'`) be a nondegenerate complex quadratic form in $m+1$ variables,
$c \ne 0$. For a measurable section $s$ of $g \mapsto ge_0$, $SO(Q)(\mathbb C) \to S_c$ (`SphSectionC`), the
**complex archimedean orbital identity** (`lerayMeasureC_orbital`) is
$$\mu_Q = |2c|_{\mathbb C}^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_c \otimes \mu_{Q'}),\qquad
\mathrm{orb}_s(x, h) = s(x)\,\mathrm{diag}(1, h),\quad |z|_{\mathbb C} = |z|^2,$$
with $\mu_Q$, $\mu_{Q'}$ the complex Leray measures of `LerayComplex.lean` (`LerayComplex.lerayMeasureC`) and $\sigma_c$ the complex
sphere Leray measure (`SphereLerayC.sigC`).

**Proof.** As at the real places (`OrbitalReal.lean`), but every fibre count is avoided by working on small sets.
With slice data adapted to $e_0$ (`splitDiagC`), the slice group contains $\mathrm{bk}(\beta, r, b') =
\left(\begin{smallmatrix} \beta & r \\ 0 & b'\end{smallmatrix}\right)$ ($\beta \in \mathbb C^\times$, $b' \in B'$).
On $W = \mathrm{bk}(\{\operatorname{Re}\beta > 0\} \times \mathbb C^m \times V_0')$ ($V_0'$ the injectivity
neighbourhood for $Q'$) the orbit map $\beta$ and the chart $(g, b) \mapsto gb$ are injective, so the fibre-counting
measures are ordinary pull-backs there. For a box $K = \mathrm{bk}(K_1 \times K_2 \times K_3) \subseteq W$:
1. (`kappa0_box`) $\kappa_0(K) = |2c|^{2(m+1)}\lambda(K_1)\,\mathrm{Leb}(K_2)\,\kappa_0'(K_3)$, by the change of
   variables $s = c\beta^2$, $u = 2c\beta r$, $v = v' + c\,rr^{\mathsf T}$ in coefficient space and the density
   $\theta(b) = |\det b|^{-2}$ of $\kappa_0$ (from the complex `det_act`), written as a function of $\beta(b)$;
2. (`volume_chart_box`) $\mathrm{Leb}(\mathrm{chart}(A \times K)) = \lambda(K_1)\,\mathrm{Leb}(K_2)\,\kappa_0'(K_3)\cdot
   (\nu_c \otimes \mu_{Q'})(\mathrm{orb}^{-1}A)$, by complex polar coordinates on the first column
   (`SphereLerayC.lintegral_polC_half`), rotation by $s(x)$, splitting each remaining column, and the fibration for $Q'$
   on its injectivity slab;
3. The fibration for $Q$: $\mu_Q(A)\,\kappa_0(K) = \mathrm{Leb}(\mathrm{chart}(A \times K))$; cancel.
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.OrbitalComplex

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {m : ℕ}

/-! ### Block matrices over $\mathbb C$ -/

/-- **The block upper triangular matrix** $\left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right)$. -/
def rowMat (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (Fin.cases β r j) (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

@[simp] theorem rowMat_zero_zero (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : rowMat β r M 0 0 = β := rfl
@[simp] theorem rowMat_zero_succ (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    rowMat β r M 0 j.succ = r j := rfl
@[simp] theorem rowMat_succ_zero (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    rowMat β r M i.succ 0 = 0 := rfl
@[simp] theorem rowMat_succ_succ (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    rowMat β r M i.succ j.succ = M i j := rfl

theorem cornerMat_eq_rowMat (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) : cornerMat c A = rowMat c 0 A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem rowMat_mul (β β' : ℂ) (r r' : Fin m → ℂ) (M M' : Matrix (Fin m) (Fin m) ℂ) :
    rowMat β r M * rowMat β' r' M' = rowMat (β * β') (β • r' + r ᵥ* M') (M * M') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

theorem rowMat_one : rowMat (1 : ℂ) 0 (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  rw [← cornerMat_eq_rowMat, cornerMat_one]

theorem det_rowMat (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : (rowMat β r M).det = β * M.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, rowMat_zero_zero, rowMat_succ_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1

theorem transpose_rowMat_mul (β β' : ℂ) (r r' : Fin m → ℂ) (M M' : Matrix (Fin m) (Fin m) ℂ) :
    (rowMat β r M)ᵀ * rowMat β' r' M' = Matrix.of fun i j =>
      Fin.cases (Fin.cases (β * β') (fun j' => β * r' j') j)
        (fun i' => Fin.cases (r i' * β') (fun j' => r i' * r' j' + (Mᵀ * M') i' j') j) i := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem continuous_rowMat {X : Type*} [TopologicalSpace X] {β : X → ℂ} {r : X → Fin m → ℂ}
    {M : X → Matrix (Fin m) (Fin m) ℂ} (hβ : Continuous β) (hr : Continuous r) (hM : Continuous M) :
    Continuous fun x => rowMat (β x) (r x) (M x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [rowMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
  · exact hβ
  · exact (continuous_apply j).comp hr
  · exact continuous_const
  · exact hM.matrix_elem i j

/-! ### Upper coordinates over $\mathbb C$ -/

/-- **Assembling a complex upper vector of size $m+1$** from $s = t_{00}$, $u_j = t_{0,j+1}$, $v_{ij} = t_{i+1,j+1}$. -/
def asmC (s : ℂ) (u : Fin m → ℂ) (v : UIdx m → ℂ) : UIdx (m + 1) → ℂ :=
  fun p => Sum.elim (fun _ : Unit => s) (Sum.elim u v) ((eU m).symm p)

@[simp] theorem asmC_zero (s : ℂ) (u : Fin m → ℂ) (v : UIdx m → ℂ) : asmC s u v (eU m (.inl ())) = s := by
  simp [asmC]
@[simp] theorem asmC_u (s : ℂ) (u : Fin m → ℂ) (v : UIdx m → ℂ) (j : Fin m) :
    asmC s u v (eU m (.inr (.inl j))) = u j := by simp [asmC]
@[simp] theorem asmC_v (s : ℂ) (u : Fin m → ℂ) (v : UIdx m → ℂ) (p : UIdx m) :
    asmC s u v (eU m (.inr (.inr p))) = v p := by simp [asmC]

theorem asmC_inj {s s' : ℂ} {u u' : Fin m → ℂ} {v v' : UIdx m → ℂ} (h : asmC s u v = asmC s' u' v') :
    s = s' ∧ u = u' ∧ v = v' := by
  refine ⟨?_, funext fun j => ?_, funext fun p => ?_⟩
  · simpa using congrFun h (eU m (.inl ()))
  · simpa using congrFun h (eU m (.inr (.inl j)))
  · simpa using congrFun h (eU m (.inr (.inr p)))

theorem measurable_asmC : Measurable fun x : ℂ × (Fin m → ℂ) × (UIdx m → ℂ) => asmC x.1 x.2.1 x.2.2 := by
  refine measurable_pi_iff.mpr fun p => ?_
  unfold asmC
  rcases (eU m).symm p with _ | j | q
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  · exact (measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)

/-- **Fubini in complex upper coordinates.** -/
theorem lintegral_splitC {F : (UIdx (m + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t, F t = ∫⁻ s : ℂ, ∫⁻ u : Fin m → ℂ, ∫⁻ v : UIdx m → ℂ, F (asmC s u v) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : UIdx (m + 1) => ℂ) (eU m)
  rw [← h1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Unit ⊕ (Fin m ⊕ UIdx m) => ℂ)
  rw [← h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod _ (by fun_prop)]
  have h3 := (volume_preserving_funUnique Unit ℂ).symm
  rw [← h3.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine lintegral_congr fun s => ?_
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ UIdx m => ℂ)
  rw [← h4.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
    lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun u => lintegral_congr fun v => ?_
  congr 1
  funext p
  simp [asmC, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rcases (eU m).symm p with _ | j | q <;> rfl

/-- Splitting each of $N$ columns in $\mathbb C^{N+1}$ into its top entry and the rest. -/
theorem lintegral_cols_splitC {N : ℕ} {G : (Fin N → Fin (N + 1) → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ Y, G Y = ∫⁻ w : Fin N → ℂ, ∫⁻ Z : Fin N → Fin N → ℂ, G (fun j => Fin.cons (w j) (Z j)) := by
  let E : (Fin N → Fin (N + 1) → ℂ) ≃ᵐ (Fin N → ℂ) × (Fin N → Fin N → ℂ) :=
    (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℂ (Fin N → ℂ) (Fin N))
  have hE : MeasurePreserving E volume volume :=
    (measurePreserving_arrowProdEquivProdArrow ℂ (Fin N → ℂ) (Fin N) (fun _ => volume)
      (fun _ => volume)).comp
      (measurePreserving_pi _ _ (fun _ => volume_preserving_piFinSuccAbove (fun _ => ℂ) 0))
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun w => lintegral_congr fun Z => ?_
  congr 1
  funext j i
  simp [E, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.arrowProdEquivProdArrow]
  rfl

/-- **Splitting off the first column** in column coordinates over $\mathbb C$. -/
theorem lintegral_first_colC {N : ℕ} {G : (Fin (N + 1) → Fin (N + 1) → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ x₀ : Fin (N + 1) → ℂ, ∫⁻ X' : Fin N → Fin (N + 1) → ℂ, G (Fin.cons x₀ X') := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Fin (N + 1) → ℂ) 0
  have hE : MeasurePreserving E volume volume := volume_preserving_piFinSuccAbove _ 0
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun x₀ => lintegral_congr fun X' => ?_
  congr 1
  simp [E, MeasurableEquiv.piFinSuccAbove]
  rfl

/-- $x \mapsto Hx$ preserves Lebesgue measure on $\mathbb C^N$ when $|\det H| = 1$. -/
theorem measurePreserving_mulVecC {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : ‖H.det‖ = 1) :
    MeasurePreserving (fun x : Fin N → ℂ => H *ᵥ x) volume volume := by
  have h0 : LinearMap.det (Matrix.toLin' H) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h, norm_zero] at hH; exact zero_ne_one hH
  refine ⟨(Matrix.toLin' H).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [show (fun x : Fin N → ℂ => H *ᵥ x) = ⇑(Matrix.toLin' H) from rfl, map_clm_addHaar _ _ h0,
    LinearMap.det_toLin']
  have : ‖H.det‖₊ = 1 := by rw [← NNReal.coe_eq_one, coe_nnnorm, hH]
  simp [this]


/-! ### The split form over $\mathbb C$ -/

theorem cornerMat_smul (a c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) : a • cornerMat c A = cornerMat (a * c) (a • A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem gramC_splitForm (c : ℂ) (Q' : QuadForm ℂ m) : gramC (splitForm c Q') = cornerMat c (gramC Q') := by
  rw [gramC, hessian_splitForm, cornerMat_smul, gramC]
  congr 1; ring

theorem gramDetC_splitForm (c : ℂ) (Q' : QuadForm ℂ m) : gramDetC (splitForm c Q') = c * gramDetC Q' := by
  rw [gramDetC, gramDetC, gramC_splitForm, det_cornerMat]

theorem gramDetC_splitForm_ne_zero {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (hQ' : gramDetC Q' ≠ 0) :
    gramDetC (splitForm c Q') ≠ 0 := by
  rw [gramDetC_splitForm]; exact mul_ne_zero hc hQ'

/-- $u \mapsto (\mathrm{wt}_{ij}u_iu_j)_{i \le j}$ over $\mathbb C$. -/
def wtOuterC (r : Fin m → ℂ) : UIdx m → ℂ := fun p => (ArchVol.wt p : ℂ) * (r p.1.1 * r p.1.2)

theorem continuous_wtOuterC : Continuous (wtOuterC : (Fin m → ℂ) → UIdx m → ℂ) :=
  continuous_pi fun p => continuous_const.mul ((continuous_apply _).mul (continuous_apply _))

/-- **$\Phi_Q$ on block matrices** over $\mathbb C$: $\Phi_Q\left(\begin{smallmatrix} \beta & r \\ 0 & M
\end{smallmatrix}\right) = (c\beta^2,\ 2c\beta r,\ \Phi_{Q'}(M) + c\,(\mathrm{wt}_{ij}r_ir_j))$. -/
theorem phi_rowMat (c : ℂ) (Q' : QuadForm ℂ m) (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    phi (splitForm c Q') (rowMat β r M) = asmC (c * β ^ 2) ((2 * c * β) • r) (phi Q' M + c • wtOuterC r) := by
  have hAX : gramC (splitForm c Q') * rowMat β r M = rowMat (c * β) (c • r) (gramC Q' * M) := by
    rw [gramC_splitForm, cornerMat_eq_rowMat, rowMat_mul]
    congr 1
    · ext j; simp
  funext p
  obtain ⟨q, rfl⟩ := (eU m).surjective p
  rw [phi, wtU, Matrix.mul_assoc, hAX, transpose_rowMat_mul]
  rcases q with _ | j | q
  · rw [asmC_zero]; simp [eU, ArchVol.wt]; ring
  · rw [asmC_u]; simp [eU, ArchVol.wt, (Fin.succ_ne_zero j).symm]; ring
  · rw [asmC_v]
    simp only [eU, Equiv.coe_fn_mk, Matrix.of_apply, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      phi, wtU, wtOuterC, Matrix.mul_assoc]
    have : ArchVol.wt (⟨(q.1.1.succ, q.1.2.succ), Fin.succ_le_succ_iff.mpr q.2⟩ : UIdx (m + 1)) = ArchVol.wt q := by
      simp [ArchVol.wt, Fin.succ_inj]
    rw [this]
    ring

theorem cornerMat_diagonal (c : ℂ) (d : Fin m → ℂ) :
    cornerMat c (diagonal d) = diagonal (Fin.cons c d : Fin (m + 1) → ℂ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj]

/-- **Slice data for $\langle c\rangle \perp Q'$ adapted to $e_0$** over $\mathbb C$. -/
def splitDiagC {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (D' : DiagC Q') : DiagC (splitForm c Q') where
  P := blockGL D'.P
  d := Fin.cons c D'.d
  hd i := Fin.cases hc (fun i => D'.hd i) i
  hP := by
    rw [blockGL_val, gramC_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul, D'.hP,
      cornerMat_diagonal]
    simp

/-! ### The embedding $SO(Q') \to SO(Q)$ over $\mathbb C$ -/

theorem blockGL_mem_soC (c : ℂ) {Q' : QuadForm ℂ m} (g : GL (Fin m) ℂ) (hg : g ∈ soC Q') :
    blockGL g ∈ soC (splitForm c Q') := by
  rw [mem_soC_iff] at hg ⊢
  rw [blockGL_val, gramC_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul, hg.1, det_cornerMat, hg.2]
  simp

/-- **The embedding** $\iota : SO(Q')(\mathbb C) \to SO(Q)(\mathbb C)$, $h \mapsto \mathrm{diag}(1, h)$. -/
def iotaC (c : ℂ) (Q' : QuadForm ℂ m) : ArchSOC Q' →* ArchSOC (splitForm c Q') where
  toFun g := ArchSOC.mk _ (blockGL (ArchSOC.incl Q' g)) (blockGL_mem_soC c _ (ArchSOC.incl_mem Q' g))
  map_one' := by
    apply Subtype.ext; simp [ArchSOC.mk]; rfl
  map_mul' a b := by
    apply Subtype.ext; simp [ArchSOC.mk]; rfl

theorem mat_iotaC (c : ℂ) (Q' : QuadForm ℂ m) (g : ArchSOC Q') :
    ArchSOC.mat _ (iotaC c Q' g) = cornerMat 1 (ArchSOC.mat Q' g) := rfl

theorem continuous_iotaC (c : ℂ) (Q' : QuadForm ℂ m) : Continuous (iotaC c Q') := by
  have hval : Continuous fun g : ArchSOC Q' => cornerMat (1 : ℂ) (ArchSOC.mat Q' g) := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [cornerMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact ((ArchSOC.continuous_mat Q').matrix_elem i j)
  have hinv : Continuous fun g : ArchSOC Q' => cornerMat (1 : ℂ) (ArchSOC.mat Q' g⁻¹) := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [cornerMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact (((ArchSOC.continuous_mat Q').comp continuous_inv).matrix_elem i j)
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨hval, ?_⟩) _
  convert hinv using 1
  funext g
  rw [← map_inv, blockGL_val, ArchSOC.mat, map_inv]

/-! ### The adapted slice group over $\mathbb C$ -/

theorem isUT_rowMat_iff (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    IsUT (rowMat β r M) ↔ IsUT M := by
  constructor
  · intro h i j hij
    exact h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
  · intro h i j hij
    refine Fin.cases (fun hij => absurd hij (Fin.not_lt_zero _)) (fun i hij => ?_) i hij
    refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j hij
    exact h i j (Fin.succ_lt_succ_iff.mp hj)

theorem conj_rowMat (P : GL (Fin m) ℂ) (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    ((blockGL P)⁻¹ : GL (Fin (m + 1)) ℂ).val * rowMat β r M * (blockGL P).val =
      rowMat β (r ᵥ* P.val) ((P⁻¹ : GL (Fin m) ℂ).val * M * P.val) := by
  rw [← map_inv, blockGL_val, blockGL_val, cornerMat_eq_rowMat, cornerMat_eq_rowMat, rowMat_mul, rowMat_mul]
  congr 1
  · ring
  · ext j; simp [vecMul, dotProduct]

theorem rowMat_mem_slice_iff {P : GL (Fin m) ℂ} {β : ℂ} {r : Fin m → ℂ} {M : Matrix (Fin m) (Fin m) ℂ}
    (x : GL (Fin (m + 1)) ℂ) (hx : x.val = rowMat β r M) (y : GL (Fin m) ℂ) (hy : y.val = M) :
    x ∈ sliceGroup (blockGL P) ↔ y ∈ sliceGroup P := by
  rw [mem_sliceGroup, mem_sliceGroup]
  change IsUT ((blockGL P)⁻¹ * x * blockGL P).val ↔ IsUT (P⁻¹ * y * P).val
  rw [Units.val_mul, Units.val_mul, hx, conj_rowMat, isUT_rowMat_iff, Units.val_mul, Units.val_mul, hy]

section Slice

variable {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (D' : DiagC Q')

/-- The matrix $\left(\begin{smallmatrix} \beta & r \\ 0 & b'\end{smallmatrix}\right)$ as a unit. -/
def bkGL (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) : GL (Fin (m + 1)) ℂ where
  val := rowMat p.1 p.2.1 (SliceB.mat D'.P p.2.2)
  inv := rowMat (p.1⁻¹ : ℂˣ) (-((p.1⁻¹ : ℂˣ) : ℂ) • (p.2.1 ᵥ* SliceB.mat D'.P p.2.2⁻¹)) (SliceB.mat D'.P p.2.2⁻¹)
  val_inv := by
    rw [rowMat_mul, SliceB.mat_mul_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one, smul_smul, mul_neg,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, neg_one_smul, neg_add_cancel, rowMat_one]
  inv_val := by
    rw [rowMat_mul, SliceB.mat_inv_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, smul_vecMul,
      vecMul_vecMul, SliceB.mat_inv_mul, vecMul_one, neg_smul, add_neg_cancel, rowMat_one]

theorem bkGL_mem (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) : bkGL D' p ∈ sliceGroup (splitDiagC hc D').P :=
  (rowMat_mem_slice_iff (bkGL D' p) rfl (SliceB.incl D'.P p.2.2) rfl).mpr (SliceB.incl_mem D'.P p.2.2)

/-- **Coordinates on the adapted slice group**: $(\beta, r, b') \mapsto
\left(\begin{smallmatrix} \beta & r \\ 0 & b'\end{smallmatrix}\right)$ (injective, `bk_injective`). -/
def bk (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) : SliceB (splitDiagC hc D').P :=
  SliceB.mk _ (bkGL D' p) (bkGL_mem hc D' p)

theorem mat_bk (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) :
    SliceB.mat _ (bk hc D' p) = rowMat p.1 p.2.1 (SliceB.mat D'.P p.2.2) := rfl

theorem continuous_bk : Continuous (bk hc D') := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · exact continuous_rowMat (Units.continuous_val.comp continuous_fst) (continuous_fst.comp continuous_snd)
      ((SliceB.continuous_mat D'.P).comp (continuous_snd.comp continuous_snd))
  · exact continuous_rowMat (Units.continuous_val.comp (continuous_inv.comp continuous_fst))
      ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).neg.smul
        ((continuous_fst.comp continuous_snd).matrix_vecMul
          ((SliceB.continuous_mat D'.P).comp (continuous_inv.comp (continuous_snd.comp continuous_snd)))))
      ((SliceB.continuous_mat D'.P).comp (continuous_inv.comp (continuous_snd.comp continuous_snd)))

theorem measurable_bk : Measurable (bk hc D') := (continuous_bk hc D').measurable

theorem SliceB.mat_injective {n : ℕ} (P : GL (Fin n) ℂ) : Function.Injective (SliceB.mat P) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem bk_injective : Function.Injective (bk hc D') := by
  rintro ⟨t, r, b⟩ ⟨t', r', b'⟩ h
  have h1 := congrArg (SliceB.mat _) h
  rw [mat_bk, mat_bk] at h1
  have e0 := congrFun (congrFun h1 0) 0
  simp only [rowMat_zero_zero] at e0
  have ht : t = t' := Units.ext e0
  have hr : r = r' := funext fun j => by simpa using congrFun (congrFun h1 0) j.succ
  have hb : b = b' := SliceB.mat_injective D'.P (funext fun i => funext fun j => by
    simpa using congrFun (congrFun h1 i.succ) j.succ)
  rw [ht, hr, hb]

/-- **The orbit map on the adapted slice group**. -/
theorem beta_bk (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) :
    beta (splitDiagC hc D') (bk hc D' p) =
      asmC (c * (p.1 : ℂ) ^ 2) ((2 * c * p.1) • p.2.1) (beta D' p.2.2 + c • wtOuterC p.2.1) := by
  rw [beta, mat_bk, phi_rowMat, beta]

theorem det_mat_bk (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) :
    (SliceB.mat _ (bk hc D' p)).det = p.1 * (SliceB.mat D'.P p.2.2).det := by
  rw [mat_bk, det_rowMat]

end Slice


/-! ### The density of $\kappa_0$ as a function on coefficient space -/

/-- `symOf` as a linear map. -/
def symOfL (n : ℕ) : (UIdx n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := symOf
  map_add' := symOf_add
  map_smul' := symOf_smul

theorem continuous_symOf {n : ℕ} : Continuous (symOf : (UIdx n → ℂ) → Matrix (Fin n) (Fin n) ℂ) :=
  (symOfL n).continuous_of_finiteDimensional

/-- **The density of $\kappa_0$ in coefficient coordinates**: $H_Q(y) = |\det A|/|\det S(y)|$, $S(y)$ the symmetric
matrix with coefficient vector $y$ (`thetaB_eq_HQ`). -/
def HQ {n : ℕ} (Q : QuadForm ℂ n) (y : UIdx n → ℂ) : ℝ≥0∞ :=
  (‖(gramC Q).det‖₊ : ℝ≥0∞) * ((‖(symOf y).det‖₊ : ℝ≥0∞))⁻¹

theorem measurable_HQ {n : ℕ} (Q : QuadForm ℂ n) : Measurable (HQ Q) :=
  measurable_const.mul (continuous_nnnorm.comp (continuous_symOf.matrix_det)).measurable.coe_nnreal_ennreal.inv

theorem det_symOf_beta {n : ℕ} {Q : QuadForm ℂ n} (D : DiagC Q) (b : SliceB D.P) :
    (symOf (beta D b)).det = (SliceB.mat D.P b).det ^ 2 * (gramC Q).det := by
  rw [beta, phi, symOf_wtU (gram_sym_mul Q _), det_mul, det_mul, det_transpose]; ring

/-- **$\theta = H_Q \circ \beta$**: the density $\theta(b) = |\det b|^{-2}$ of $\kappa_0$ is a function of $\beta(b)$. -/
theorem thetaB_eq_HQ {n : ℕ} {Q : QuadForm ℂ n} (D : DiagC Q) (b : SliceB D.P) :
    (thetaB D b : ℝ≥0∞) = HQ Q (beta D b) := by
  have hA := D.det_gram_ne_zero
  have hb := SliceB.det_mat_ne_zero D.P b
  have hθ : thetaB D b = (‖(SliceB.mat D.P b).det‖₊ ^ 2)⁻¹ := by
    have hd : ‖(SliceB.mat D.P b).det‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hb
    simp only [thetaB, chiB, JB, MonoidHom.coe_mk, OneHom.coe_mk, det_act, nnnorm_pow]
    rw [← pow_mul, show (n + 1) * 2 = 2 * n + 2 by ring, pow_add, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hd), one_mul]
  rw [hθ, HQ, det_symOf_beta, nnnorm_mul, nnnorm_pow, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.mul_inv (Or.inl (by simp [hb])) (Or.inl (by simp)), ← mul_assoc, mul_comm (‖(gramC Q).det‖₊ : ℝ≥0∞),
    mul_assoc, ENNReal.mul_inv_cancel (by simp [hA]) ENNReal.coe_ne_top, mul_one,
    ENNReal.coe_inv (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hb)), ENNReal.coe_pow]

/-- **$\kappa_0$ on a set where $\beta$ is injective**: $\kappa_0(S) = \int_{\beta(S)}H_Q\,dy$. -/
theorem kappa0_eq_of_injOn {n : ℕ} {Q : QuadForm ℂ n} (D : DiagC Q) {S : Set (SliceB D.P)} (hS : MeasurableSet S)
    (hinj : InjOn (beta D) S) : kappa0 D S = ∫⁻ y in beta D '' S, HQ Q y := by
  have hmap := Leray.map_restrict_fibreCount (continuous_beta D) (isLocInj_beta D) volume hS hinj
  rw [kappa0, withDensity_apply _ hS]
  simp_rw [thetaB_eq_HQ]
  rw [← lintegral_map (measurable_HQ Q) (continuous_beta D).measurable, kappa1, hmap]

/-! ### Injectivity of $\beta$ on the adapted half-slab -/

section Half

variable {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (D' : DiagC Q')

include hc in
theorem eq_of_sq_eq_half {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) (h : c * β ^ 2 = c * β' ^ 2) : β = β' := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (mul_left_cancel₀ hc h) with h1 | h1
  · exact h1
  · exfalso; rw [h1, Complex.neg_re] at hβ; linarith

include hc in
/-- The map $(\beta, r, v) \mapsto (c\beta^2, 2c\beta r, v + c\,rr^{\mathsf T})$ is injective for $\operatorname{Re}\beta > 0$. -/
theorem asmC_param_inj {β β' : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re) {r r' : Fin m → ℂ} {v v' : UIdx m → ℂ}
    (h : asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r) =
      asmC (c * β' ^ 2) ((2 * c * β') • r') (v' + c • wtOuterC r')) : β = β' ∧ r = r' ∧ v = v' := by
  obtain ⟨h1, h2, h3⟩ := asmC_inj h
  have hb := eq_of_sq_eq_half hc hβ hβ' h1
  subst hb
  have h0 : 2 * c * β ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) (fun h => by rw [h] at hβ; simp at hβ)
  have hr := smul_right_injective _ h0 h2
  subst hr
  exact ⟨rfl, rfl, add_right_cancel h3⟩

/-- **The half-slab** $W = \mathrm{bk}(\{\operatorname{Re}\beta > 0\} \times \mathbb C^m \times V_0')$. -/
def halfSlab : Set (SliceB (splitDiagC hc D').P) := bk hc D' '' (halfU ×ˢ univ ×ˢ V0 D')

theorem injOn_beta_halfSlab : InjOn (beta (splitDiagC hc D')) (halfSlab hc D') := by
  rintro _ ⟨⟨β, r, b⟩, ⟨hβ, -, hb⟩, rfl⟩ _ ⟨⟨β', r', b'⟩, ⟨hβ', -, hb'⟩, rfl⟩ h
  rw [beta_bk, beta_bk] at h
  obtain ⟨e1, e2, e3⟩ := asmC_param_inj hc hβ hβ' h
  have e1' : β = β' := Units.ext e1
  have e3' : b = b' := injOn_beta_V0 D' hb hb' e3
  subst e1' e3'
  simp only at e2
  rw [e2]

end Half


/-! ### $\kappa_0$ in the adapted coordinates -/

/-- The generic form of `phi_rowMat`: $\mathrm{wt}\big(R^{\mathsf T}\,\mathrm{corner}(c, A')\,R\big)$ for
$R = \left(\begin{smallmatrix} \beta & r \\ 0 & M\end{smallmatrix}\right)$. -/
theorem wtU_rowMat (c : ℂ) (A' : Matrix (Fin m) (Fin m) ℂ) (β : ℂ) (r : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    wtU ((rowMat β r M)ᵀ * cornerMat c A' * rowMat β r M) =
      asmC (c * β ^ 2) ((2 * c * β) • r) (wtU (Mᵀ * A' * M) + c • wtOuterC r) := by
  have hAX : cornerMat c A' * rowMat β r M = rowMat (c * β) (c • r) (A' * M) := by
    rw [cornerMat_eq_rowMat, rowMat_mul]
    congr 1
    · ext j; simp
  funext p
  obtain ⟨q, rfl⟩ := (eU m).surjective p
  rw [wtU, Matrix.mul_assoc, hAX, transpose_rowMat_mul]
  rcases q with _ | j | q
  · rw [asmC_zero]; simp [eU, ArchVol.wt]; ring
  · rw [asmC_u]; simp [eU, ArchVol.wt, (Fin.succ_ne_zero j).symm]; ring
  · rw [asmC_v]
    simp only [eU, Equiv.coe_fn_mk, Matrix.of_apply, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      wtU, wtOuterC, Matrix.mul_assoc]
    have : ArchVol.wt (⟨(q.1.1.succ, q.1.2.succ), Fin.succ_le_succ_iff.mpr q.2⟩ : UIdx (m + 1)) = ArchVol.wt q := by
      simp [ArchVol.wt, Fin.succ_inj]
    rw [this]
    ring

theorem symOf_param (c β : ℂ) (r : Fin m → ℂ) (v : UIdx m → ℂ) :
    symOf (asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r)) =
      (rowMat β r 1)ᵀ * cornerMat c (symOf v) * rowMat β r 1 := by
  have h := wtU_rowMat c (symOf v) β r 1
  rw [transpose_one, Matrix.one_mul, Matrix.mul_one, wtU_symOf] at h
  rw [← h, symOf_wtU]
  rw [transpose_mul, transpose_mul, transpose_transpose, cornerMat_transpose, symOf_transpose, Matrix.mul_assoc]

theorem HQ_param {c : ℂ} (hc : c ≠ 0) (Q' : QuadForm ℂ m) {β : ℂ} (hβ : β ≠ 0) (r : Fin m → ℂ) (v : UIdx m → ℂ) :
    HQ (splitForm c Q') (asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r)) =
      ((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹ * HQ Q' v := by
  rw [HQ, HQ, symOf_param, det_mul, det_mul, det_transpose, det_rowMat, det_cornerMat, gramC_splitForm,
    det_cornerMat, det_one, mul_one]
  have hb : ((‖β‖₊ : ℝ≥0∞)) ≠ 0 := by simp [hβ]
  have hc' : ((‖c‖₊ : ℝ≥0∞)) ≠ 0 := by simp [hc]
  simp only [nnnorm_mul, ENNReal.coe_mul, ENNReal.coe_pow]
  rw [show (‖β‖₊ : ℝ≥0∞) * (‖c‖₊ * ‖(symOf v).det‖₊) * ‖β‖₊ = (‖β‖₊ ^ 2 * ‖c‖₊ : ℝ≥0∞) * ‖(symOf v).det‖₊ by ring,
    ENNReal.mul_inv (Or.inl (mul_ne_zero (pow_ne_zero _ hb) hc')) (Or.inl (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.coe_ne_top)),
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hb)) (Or.inl ENNReal.coe_ne_top)]
  have : (‖c‖₊ : ℝ≥0∞) * (‖c‖₊ : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top
  calc _ = ((‖c‖₊ : ℝ≥0∞) * (‖c‖₊ : ℝ≥0∞)⁻¹) * (((‖β‖₊ : ℝ≥0∞) ^ 2)⁻¹ * (‖(gramC Q').det‖₊ *
          (‖(symOf v).det‖₊ : ℝ≥0∞)⁻¹)) := by ring
    _ = _ := by rw [this, one_mul]

/-- **Scaling by a complex number** in $\mathbb C^N$: $\int K = |a|^{2N}\int K(a\,\cdot)$. -/
theorem lintegral_smul_vecC {N : ℕ} {K : (Fin N → ℂ) → ℝ≥0∞} (hK : Measurable K) {a : ℂ} (ha : a ≠ 0) :
    ∫⁻ u, K u = ((‖a‖₊ ^ (2 * N) : ℝ≥0) : ℝ≥0∞) * ∫⁻ r, K (a • r) := by
  have h := map_scV_volume (n := N) (Units.mk0 a ha)
  have e : ∫⁻ r, K (a • r) = ∫⁻ u, K u ∂(volume.map (scV N (Units.mk0 a ha))) := by
    rw [lintegral_map hK (scV N _).measurable]; rfl
  rw [e, h, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, SphereLerayC.wt, Units.val_mk0, ← ENNReal.coe_mul,
    _root_.zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr ha)), ENNReal.coe_one, one_mul]

/-- The half plane $\{\operatorname{Re}\beta > 0\} \subset \mathbb C$. -/
def halfC : Set ℂ := {β | 0 < β.re}

theorem measurableSet_halfC : MeasurableSet halfC :=
  measurableSet_lt measurable_const Complex.continuous_re.measurable

theorem ne_zero_of_mem_halfC {β : ℂ} (h : β ∈ halfC) : β ≠ 0 := fun h0 => by
  rw [halfC, mem_ofPred_eq, h0, Complex.zero_re] at h; exact lt_irrefl _ h

theorem det_toSpanSingleton (a : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq a := by
  have e : (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
      ((a • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ) := by
    ext z <;> simp [mul_comm]
  rw [ContinuousLinearMap.det, e, det_restrictScalars_complex, LinearMap.det_smul, LinearMap.det_id,
    Module.finrank_self, pow_one, mul_one]

section Coeff

variable {c : ℂ} (hc : c ≠ 0)

include hc in
/-- **The change of variables in coefficient space** for the adapted slice coordinates: for $G \ge 0$ measurable on
$\mathbb C^{(m+1)(m+2)/2}$ whose $(0,0)$ coordinate lies in $c\cdot\{\beta^2 : \operatorname{Re}\beta > 0\}$ on its support,
$\int G = \int_{\operatorname{Re}\beta > 0}|2c\beta|^{2(m+1)}\int\int G(c\beta^2, 2c\beta r, v + c\,rr^{\mathsf T})\,dv\,dr\,d^2\beta$. -/
theorem lintegral_coeff_half {G : (UIdx (m + 1) → ℂ) → ℝ≥0∞} (hG : Measurable G)
    (hG0 : ∀ s u v, (∀ β ∈ halfC, s ≠ c * β ^ 2) → G (asmC s u v) = 0) :
    ∫⁻ y, G y = ∫⁻ β in halfC, ((‖2 * c * β‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) *
      ∫⁻ r, ∫⁻ v, G (asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r)) := by
  rw [lintegral_splitC hG]
  set H : ℂ → ℝ≥0∞ := fun s => ∫⁻ u : Fin m → ℂ, ∫⁻ v : UIdx m → ℂ, G (asmC s u v) with hHdef
  set f : ℂ → ℂ := fun β => c * β ^ 2
  have hH0 : ∀ s, s ∉ f '' halfC → H s = 0 := by
    intro s hs
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun u => lintegral_eq_zero_of_ae_eq_zero
      (ae_of_all _ fun v => hG0 _ _ _ fun β hβ h => hs ⟨β, hβ, h.symm⟩))
  have hinj : InjOn f halfC := fun β hβ β' hβ' h => eq_of_sq_eq_half hc hβ hβ' h
  have hmS : MeasurableSet (f '' halfC) :=
    measurableSet_halfC.image_of_continuousOn_injOn (by fun_prop) hinj
  have hstep : ∫⁻ s, H s = ∫⁻ s in f '' halfC, H s := by
    rw [← lintegral_indicator hmS]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ f '' halfC
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs, hH0 s hs]
  rw [hstep, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_halfC
    (f' := fun β => (ContinuousLinearMap.toSpanSingleton ℂ (2 * c * β)).restrictScalars ℝ)
    (fun β _ => by
      have h : HasDerivAt f (2 * c * β) β := by
        have := ((hasDerivAt_pow 2 β).const_mul c)
        convert this using 1; simp; ring
      exact (h.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun measurableSet_halfC fun β hβ => ?_
  have hβ0 := ne_zero_of_mem_halfC hβ
  have ha : 2 * c * β ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hβ0
  simp only [hHdef, f]
  have hmK : Measurable fun u : Fin m → ℂ => ∫⁻ v : UIdx m → ℂ, G (asmC (c * β ^ 2) u v) :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin m → ℂ) × (UIdx m → ℂ) => G (asmC (c * β ^ 2) p.1 p.2))
      (hG.comp (measurable_asmC.comp (measurable_const.prodMk measurable_id)))
  rw [lintegral_smul_vecC hmK ha, det_toSpanSingleton, abs_of_nonneg (Complex.normSq_nonneg _), ← mul_assoc]
  congr 1
  · rw [Complex.normSq_eq_norm_sq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    rw [mul_add, mul_one, pow_add, mul_comm]
    simp only [← coe_nnnorm, ← NNReal.coe_pow, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul,
      ENNReal.coe_pow]
  · refine lintegral_congr fun r => ?_
    exact (lintegral_add_right_eq_self (fun v => G (asmC (c * β ^ 2) ((2 * c * β) • r) v)) (c • wtOuterC r)).symm

end Coeff


/-- The radial measure in Lebesgue terms: $\lambda(R) = \int_{R}|z|^{2m}\,d^2z$ (here $n = m+1$). -/
theorem lamU_succ_apply {R : Set ℂˣ} (hR : MeasurableSet R) :
    lamU (m + 1) R = ∫⁻ z in Units.val '' R, ((‖z‖₊ ^ (2 * m) : ℝ≥0) : ℝ≥0∞) := by
  have hR' := measurableEmbedding_val.measurableSet_image' hR
  set g : ℂ → ℝ≥0∞ := fun z => ((‖z‖₊ ^ (2 * m) : ℝ≥0) : ℝ≥0∞)
  have hg : Measurable g := (continuous_nnnorm.pow _).measurable.coe_nnreal_ennreal
  have hw : ∀ β : ℂˣ, SphereLerayC.wt (2 * ((m + 1 : ℕ) : ℤ) - 2) β = g β := fun β => by
    rw [SphereLerayC.wt, show (2 * ((m + 1 : ℕ) : ℤ) - 2) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [lamU, withDensity_apply _ hR]
  simp_rw [hw]
  rw [volU, ← lintegral_indicator hR, ← lintegral_indicator hR']
  have e : (R.indicator fun β : ℂˣ => g β) = ((Units.val '' R).indicator g) ∘ Units.val := by
    funext β
    by_cases hβ : β ∈ R
    · rw [indicator_of_mem hβ, Function.comp_apply, indicator_of_mem (mem_image_of_mem _ hβ)]
    · rw [indicator_of_notMem hβ, Function.comp_apply, indicator_of_notMem]
      rintro ⟨γ, hγ, h⟩; exact hβ (Units.ext h ▸ hγ)
  rw [e]
  show ∫⁻ a, (Units.val '' R).indicator g (Units.val a) ∂(Measure.comap Units.val volume) = _
  rw [← measurableEmbedding_val.lintegral_map, measurableEmbedding_val.map_comap,
    lintegral_indicator hR', lintegral_indicator hR', Measure.restrict_restrict hR']
  congr 2
  exact inter_eq_left.mpr fun z ⟨β, _, h⟩ => ⟨β, h⟩

section Box

variable {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (D' : DiagC Q')

theorem measurableSet_bk_image {S : Set (ℂˣ × (Fin m → ℂ) × SliceB D'.P)} (hS : MeasurableSet S) :
    MeasurableSet (bk hc D' '' S) :=
  hS.image_of_continuousOn_injOn (continuous_bk hc D').continuousOn (bk_injective hc D').injOn

include hc in
theorem mem_beta_box_iff {K₁ : Set ℂˣ} (hK₁h : K₁ ⊆ halfU) {K₂ : Set (Fin m → ℂ)} {K₃ : Set (SliceB D'.P)}
    {β : ℂ} (hβ : β ∈ halfC) (r : Fin m → ℂ) (v : UIdx m → ℂ) :
    asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r) ∈
        beta (splitDiagC hc D') '' (bk hc D' '' (K₁ ×ˢ K₂ ×ˢ K₃)) ↔
      β ∈ Units.val '' K₁ ∧ r ∈ K₂ ∧ v ∈ beta D' '' K₃ := by
  constructor
  · rintro ⟨_, ⟨⟨β₁, r₁, b'⟩, ⟨h1, h2, h3⟩, rfl⟩, hb⟩
    rw [beta_bk] at hb
    obtain ⟨e1, e2, e3⟩ := asmC_param_inj hc (hK₁h h1) hβ hb
    exact ⟨⟨β₁, h1, e1⟩, e2 ▸ h2, ⟨b', h3, e3⟩⟩
  · rintro ⟨⟨u, hu, rfl⟩, hr, ⟨b', hb', rfl⟩⟩
    exact ⟨bk hc D' (u, r, b'), ⟨(u, r, b'), ⟨hu, hr, hb'⟩, rfl⟩, beta_bk hc D' _⟩

/-- **$\kappa_0$ of a box in the half-slab**: for $K_1 \subseteq \{\operatorname{Re}\beta > 0\}$ and $K_3 \subseteq V_0'$,
$\kappa_0(\mathrm{bk}(K_1 \times K_2 \times K_3)) = |2c|^{2(m+1)}\,\lambda(K_1)\,\mathrm{Leb}(K_2)\,\kappa_0'(K_3)$. -/
theorem kappa0_box {K₁ : Set ℂˣ} (hK₁ : MeasurableSet K₁) (hK₁h : K₁ ⊆ halfU) {K₂ : Set (Fin m → ℂ)}
    (hK₂ : MeasurableSet K₂) {K₃ : Set (SliceB D'.P)} (hK₃ : MeasurableSet K₃) (hK₃V : K₃ ⊆ V0 D') :
    kappa0 (splitDiagC hc D') (bk hc D' '' (K₁ ×ˢ K₂ ×ˢ K₃)) =
      ((‖2 * c‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) * (lamU (m + 1) K₁ * (volume K₂ * kappa0 D' K₃)) := by
  set S := bk hc D' '' (K₁ ×ˢ K₂ ×ˢ K₃)
  have hS : MeasurableSet S := measurableSet_bk_image hc D' (hK₁.prod (hK₂.prod hK₃))
  have hSW : S ⊆ halfSlab hc D' := image_mono (prod_mono hK₁h (prod_mono (subset_univ _) hK₃V))
  have hinj := (injOn_beta_halfSlab hc D').mono hSW
  have hBS : MeasurableSet (beta (splitDiagC hc D') '' S) :=
    hS.image_of_continuousOn_injOn (continuous_beta _).continuousOn hinj
  have hB3 : MeasurableSet (beta D' '' K₃) :=
    hK₃.image_of_continuousOn_injOn (continuous_beta _).continuousOn ((injOn_beta_V0 D').mono hK₃V)
  rw [kappa0_eq_of_injOn _ hS hinj, ← lintegral_indicator hBS,
    lintegral_coeff_half hc ((measurable_HQ _).indicator hBS)]
  · have hK₁' := measurableEmbedding_val.measurableSet_image' hK₁
    have hsub : Units.val '' K₁ ⊆ halfC := fun z ⟨u, hu, h⟩ => h ▸ hK₁h hu
    set X := ∫⁻ v in beta D' '' K₃, HQ Q' v
    set g : ℂ → ℝ≥0∞ := fun z => ((‖z‖₊ ^ (2 * m) : ℝ≥0) : ℝ≥0∞)
    have hg : Measurable g := (continuous_nnnorm.pow _).measurable.coe_nnreal_ennreal
    have key : ∀ β ∈ halfC, ((‖2 * c * β‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ r, ∫⁻ v, (beta (splitDiagC hc D') '' S).indicator (HQ (splitForm c Q'))
          (asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r)) =
        ((‖2 * c‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) * ((Units.val '' K₁).indicator g β * (volume K₂ * X)) := by
      intro β hβ
      have hβ0 := ne_zero_of_mem_halfC hβ
      have hpt : ∀ r v, (beta (splitDiagC hc D') '' S).indicator (HQ (splitForm c Q'))
          (asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r)) =
          (Units.val '' K₁).indicator 1 β * (K₂.indicator 1 r *
            (((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹ * (beta D' '' K₃).indicator (HQ Q') v)) := by
        intro r v
        by_cases h : asmC (c * β ^ 2) ((2 * c * β) • r) (v + c • wtOuterC r) ∈ beta (splitDiagC hc D') '' S
        · obtain ⟨h1, h2, h3⟩ := (mem_beta_box_iff hc D' hK₁h hβ r v).mp h
          rw [indicator_of_mem h, indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem h3, HQ_param hc Q' hβ0]
          simp
        · rw [indicator_of_notMem h]
          by_cases h1 : β ∈ Units.val '' K₁
          · by_cases h2 : r ∈ K₂
            · have h3 : v ∉ beta D' '' K₃ := fun h3 => h ((mem_beta_box_iff hc D' hK₁h hβ r v).mpr ⟨h1, h2, h3⟩)
              rw [indicator_of_notMem h3]; simp
            · rw [indicator_of_notMem h2]; simp
          · rw [indicator_of_notMem h1]; simp
      simp_rw [hpt]
      have hf3 : Measurable ((beta D' '' K₃).indicator (HQ Q')) := (measurable_HQ _).indicator hB3
      have hin : ∀ r, ∫⁻ v, (Units.val '' K₁).indicator 1 β * (K₂.indicator 1 r *
            (((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹ * (beta D' '' K₃).indicator (HQ Q') v)) =
          (Units.val '' K₁).indicator 1 β * (K₂.indicator 1 r * (((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹ * X)) := by
        intro r
        rw [lintegral_const_mul _ ((hf3.const_mul _).const_mul _), lintegral_const_mul _ (hf3.const_mul _),
          lintegral_const_mul _ hf3, lintegral_indicator hB3]
      simp_rw [hin]
      rw [lintegral_const_mul _ ((measurable_one.indicator hK₂).mul_const _),
        lintegral_mul_const _ (measurable_one.indicator hK₂), lintegral_indicator_one hK₂]
      by_cases h1 : β ∈ Units.val '' K₁
      · rw [indicator_of_mem h1, indicator_of_mem h1, Pi.one_apply, one_mul]
        have hb : ‖β‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hβ0
        have hk : ((‖2 * c * β‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) * ((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹ =
            ((‖2 * c‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) * g β := by
          rw [← ENNReal.coe_inv (pow_ne_zero _ hb), ← ENNReal.coe_mul, ← ENNReal.coe_mul]
          congr 1
          rw [nnnorm_mul, mul_pow, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add (‖β‖₊)]
          field_simp
        calc _ = (((‖2 * c * β‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) * ((‖β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)⁻¹) *
              (volume K₂ * X) := by ring
          _ = _ := by rw [hk]; ring
      · rw [indicator_of_notMem h1, indicator_of_notMem h1]; simp
    rw [setLIntegral_congr_fun measurableSet_halfC key, lintegral_const_mul _ ((hg.indicator hK₁').mul_const _),
      lintegral_mul_const _ (hg.indicator hK₁'), setLIntegral_indicator hK₁',
      inter_eq_left.mpr hsub, lamU_succ_apply hK₁, kappa0_eq_of_injOn D' hK₃ ((injOn_beta_V0 D').mono hK₃V)]
  · intro s u v hs
    refine indicator_of_notMem ?_ _
    rintro ⟨_, ⟨⟨β₁, r₁, b'⟩, ⟨h1, -, -⟩, rfl⟩, hb⟩
    rw [beta_bk] at hb
    exact hs β₁ (hK₁h h1) (asmC_inj hb).1.symm

end Box


/-! ### Sections of the orbit map and the decomposition of $dX$ -/

/-- **A measurable section of the orbit map** $SO(Q)(\mathbb C) \to S_c$, $g \mapsto ge_0$, for
$Q = \langle c\rangle \perp Q'$ (data; one is built from reflections in `sphSectionC`). -/
structure SphSectionC (c : ℂ) (Q' : QuadForm ℂ m) where
  /-- the section -/
  toFun : SphC (splitForm c Q') c → ArchSOC (splitForm c Q')
  measurable : Measurable toFun
  spec : ∀ x, ArchSOC.mat _ (toFun x) *ᵥ (e₀ : Fin (m + 1) → ℂ) = (x : Fin (m + 1) → ℂ)

instance {n : ℕ} (Q : QuadForm ℂ n) : MeasurableMul₂ (ArchSOC Q) := ContinuousMul.measurableMul₂

/-- **The orbit map** $(x, h) \mapsto s(x)\,\mathrm{diag}(1, h)$, $S_c \times SO(Q') \to SO(Q)$. -/
def orbC {c : ℂ} {Q' : QuadForm ℂ m} (s : SphSectionC c Q') (p : SphC (splitForm c Q') c × ArchSOC Q') :
    ArchSOC (splitForm c Q') :=
  s.toFun p.1 * iotaC c Q' p.2

theorem measurable_orbC {c : ℂ} {Q' : QuadForm ℂ m} (s : SphSectionC c Q') : Measurable (orbC s) :=
  (s.measurable.comp measurable_fst).mul ((continuous_iotaC c Q').measurable.comp measurable_snd)

theorem cols_mul_rowMat (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (β : ℂ) (r : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    cols (S * rowMat β r M) = Fin.cons (S *ᵥ (Fin.cons β 0 : Fin (m + 1) → ℂ))
      (fun j => S *ᵥ (Fin.cons (r j) (cols M j) : Fin (m + 1) → ℂ)) := by
  funext j i
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [cols, Fin.cons_zero, Matrix.mul_apply, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  · simp only [cols, Fin.cons_succ, Matrix.mul_apply, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Fin.cases ?_ (fun k => ?_) k <;> simp [cols]

theorem cons_beta_zero (β : ℂ) : (Fin.cons β 0 : Fin (m + 1) → ℂ) = β • (e₀ : Fin (m + 1) → ℂ) := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem eval_mat_e₀ {c : ℂ} {Q' : QuadForm ℂ m} (g : ArchSOC (splitForm c Q')) :
    (splitForm c Q').eval (ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ)) = c := by
  rw [eval_mulVec_of_isometryC (ArchSOC.isometry _ g)]
  exact evalIn_splitForm_e₀ ℂ c Q'

section Chart

variable {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (hQ' : gramDetC Q' ≠ 0) (D' : DiagC Q') (s : SphSectionC c Q')

theorem chart_bk (g : ArchSOC (splitForm c Q')) (p : ℂˣ × (Fin m → ℂ) × SliceB D'.P) :
    chart (splitDiagC hc D') (g, bk hc D' p) =
      cols (ArchSOC.mat _ g * rowMat p.1 p.2.1 (SliceB.mat D'.P p.2.2)) := by
  rw [chart, mat_bk]

theorem chart_orb_bk (x : SphC (splitForm c Q') c) (h : ArchSOC Q') (β : ℂˣ) (r : Fin m → ℂ) (b' : SliceB D'.P) :
    chart (splitDiagC hc D') (orbC s (x, h), bk hc D' (β, r, b')) =
      Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ))
        (fun j => ArchSOC.mat _ (s.toFun x) *ᵥ (Fin.cons (r j) (chart D' (h, b') j) : Fin (m + 1) → ℂ)) := by
  have hR : ArchSOC.mat _ (orbC s (x, h)) * SliceB.mat _ (bk hc D' (β, r, b')) =
      ArchSOC.mat _ (s.toFun x) * rowMat β r (ArchSOC.mat Q' h * SliceB.mat D'.P b') := by
    rw [orbC, ArchSOC.mat_mul, mat_iotaC, mat_bk, Matrix.mul_assoc, cornerMat_eq_rowMat, rowMat_mul]
    congr 2
    · ring
    · simp
  rw [chart, hR, cols_mul_rowMat]
  congr 1
  rw [cons_beta_zero, mulVec_smul, s.spec]

/-- The first column of a point of the chart over the half-slab is $\beta x$ with $\operatorname{Re}\beta > 0$,
$x \in S_c$. -/
theorem chart_zero_mem_polC (g : ArchSOC (splitForm c Q')) {b : SliceB (splitDiagC hc D').P}
    (hb : b ∈ halfSlab hc D') :
    chart (splitDiagC hc D') (g, b) 0 ∈ polC (splitForm c Q') c '' (halfU ×ˢ univ) := by
  obtain ⟨⟨β, r, b'⟩, ⟨hβ, -, -⟩, rfl⟩ := hb
  refine ⟨(β, ⟨_, eval_mat_e₀ g⟩), ⟨hβ, mem_univ _⟩, ?_⟩
  rw [chart_bk, cols_mul_rowMat, Fin.cons_zero, cons_beta_zero, mulVec_smul]
  rfl

include hc in
/-- **The remaining columns, rotated back, lie over $V_0'$**: if $(\beta x, s(x)(r_j, Z_j)_j)$ is a point of the
chart over the half-slab with $\operatorname{Re}\beta > 0$, then $Z$ lies in the chart of $Q'$ over $V_0'$. -/
theorem mem_chart'_of_mem (x : SphC (splitForm c Q') c) {β : ℂˣ} (hβ : β ∈ halfU) (r : Fin m → ℂ)
    (Z : Fin m → Fin m → ℂ) (g : ArchSOC (splitForm c Q')) {b : SliceB (splitDiagC hc D').P}
    (hb : b ∈ halfSlab hc D')
    (hX : chart (splitDiagC hc D') (g, b) = Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ))
        (fun j => ArchSOC.mat _ (s.toFun x) *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℂ))) :
    Z ∈ chart D' '' (univ ×ˢ V0 D') := by
  obtain ⟨⟨β₁, r₁, b'₁⟩, ⟨hβ₁, -, hb'₁⟩, rfl⟩ := hb
  set S := ArchSOC.mat _ (s.toFun x)
  have hXeq : (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ))
        (fun j => S *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℂ)) : Fin (m + 1) → Fin (m + 1) → ℂ) =
      cols (S * rowMat β r (ofCols Z)) := by
    rw [cols_mul_rowMat, cols_ofCols, cons_beta_zero, mulVec_smul, s.spec]
  rw [hXeq, chart_bk] at hX
  have hM : ArchSOC.mat _ g * rowMat β₁ r₁ (SliceB.mat D'.P b'₁) = S * rowMat β r (ofCols Z) := by
    have := congrArg ofCols hX
    rwa [ofCols_cols, ofCols_cols] at this
  -- compare Φ_Q
  have hphi := congrArg (phi (splitForm c Q')) hM
  rw [phi_of_isometry _ (ArchSOC.isometry _ g), phi_of_isometry _ (ArchSOC.isometry _ _), phi_rowMat,
    phi_rowMat] at hphi
  obtain ⟨e1, e2, e3⟩ := asmC_param_inj hc hβ₁ hβ hphi
  -- compare determinants
  have hdet := congrArg Matrix.det hM
  rw [det_mul, det_mul, ArchSOC.det_mat, ArchSOC.det_mat, one_mul, one_mul, det_rowMat, det_rowMat, e1] at hdet
  have hdZ : (ofCols Z).det = (SliceB.mat D'.P b'₁).det := (mul_left_cancel₀ β.ne_zero hdet).symm
  have hreg : Z ∈ regionC Q' (U0 D') := ⟨by rw [hdZ]; exact hb'₁.2, by rw [← e3]; exact ⟨b'₁, hb'₁, rfl⟩⟩
  rw [← image_chart D' subset_rfl] at hreg
  obtain ⟨p, ⟨-, hp, -⟩, hpZ⟩ := hreg
  exact ⟨p, ⟨mem_univ _, hp⟩, hpZ⟩


theorem lintegral_eq_setLIntegral_of_vanish {α : Type*} [MeasurableSpace α] {μ : Measure α} {R : Set α}
    (hR : MeasurableSet R) {F : α → ℝ≥0∞} (hF0 : ∀ z, z ∉ R → F z = 0) :
    ∫⁻ z, F z ∂μ = ∫⁻ z in R, F z ∂μ := by
  rw [← lintegral_indicator hR]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ R
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, hF0 z hz]

/-- **The volume of the chart over a box**: for $A \subseteq SO(Q)$ measurable and a box
$K = \mathrm{bk}(K_1 \times K_2 \times K_3)$ in the half-slab,
$\mathrm{Leb}(\mathrm{chart}(A \times K)) = \lambda(K_1)\,\mathrm{Leb}(K_2)\,\kappa_0'(K_3)\cdot
(\nu_c \otimes \mu_{Q'})(\mathrm{orb}^{-1}A)$. -/
theorem volume_chart_box {A : Set (ArchSOC (splitForm c Q'))} (hA : MeasurableSet A) {K₁ : Set ℂˣ}
    (hK₁ : MeasurableSet K₁) (hK₁h : K₁ ⊆ halfU) {K₂ : Set (Fin m → ℂ)} (hK₂ : MeasurableSet K₂)
    {K₃ : Set (SliceB D'.P)} (hK₃ : MeasurableSet K₃) (hK₃V : K₃ ⊆ V0 D') :
    volume (chart (splitDiagC hc D') '' (A ×ˢ (bk hc D' '' (K₁ ×ˢ K₂ ×ˢ K₃)))) =
      lamU (m + 1) K₁ * (volume K₂ * kappa0 D' K₃) *
        ((nuC (splitForm c Q') c).prod (lerayMeasureC Q' hQ')) (orbC s ⁻¹' A) := by
  set D := splitDiagC hc D'
  set K := bk hc D' '' (K₁ ×ˢ K₂ ×ˢ K₃)
  set E := chart D '' (A ×ˢ K)
  set μ' := lerayMeasureC Q' hQ'
  have := isHaarMeasure_lerayMeasureC hQ'
  have hn1 : 1 ≤ m + 1 := by omega
  have := sigmaFinite_nuC (Q := splitForm c Q') hc hn1
  have hK : MeasurableSet K := measurableSet_bk_image hc D' (hK₁.prod (hK₂.prod hK₃))
  have hKW : K ⊆ halfSlab hc D' := image_mono (prod_mono hK₁h (prod_mono (subset_univ _) hK₃V))
  have hinjC : InjOn (chart D) (univ ×ˢ halfSlab hc D') := injOn_chart D (injOn_beta_halfSlab hc D')
  have hE : MeasurableSet E := (hA.prod hK).image_of_continuousOn_injOn (continuous_chart D).continuousOn
    (hinjC.mono (prod_mono (subset_univ _) hKW))
  have hind : ∀ g b, b ∈ halfSlab hc D' →
      E.indicator (1 : (Fin (m + 1) → Fin (m + 1) → ℂ) → ℝ≥0∞) (chart D (g, b)) =
        A.indicator 1 g * K.indicator 1 b := by
    intro g b hb
    by_cases hg : g ∈ A <;> by_cases hbK : b ∈ K
    · rw [indicator_of_mem (mem_image_of_mem (chart D) (show (g, b) ∈ A ×ˢ K from ⟨hg, hbK⟩)),
        indicator_of_mem hg, indicator_of_mem hbK]; simp
    all_goals
      rw [indicator_of_notMem]
      · simp [hg, hbK]
      · rintro ⟨⟨g', b'⟩, ⟨hg', hb'⟩, he⟩
        have := hinjC ⟨mem_univ _, hKW hb'⟩ ⟨mem_univ _, hb⟩ he
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        simp_all
  have hindK : ∀ β r b', K.indicator (1 : SliceB D.P → ℝ≥0∞) (bk hc D' (β, r, b')) =
      K₁.indicator 1 β * (K₂.indicator 1 r * K₃.indicator 1 b') := by
    intro β r b'
    have hmem : bk hc D' (β, r, b') ∈ K ↔ β ∈ K₁ ∧ r ∈ K₂ ∧ b' ∈ K₃ := by
      constructor
      · rintro ⟨p, hp, he⟩; rw [bk_injective hc D' he] at hp; exact hp
      · intro h; exact ⟨_, h, rfl⟩
    by_cases h1 : β ∈ K₁ <;> by_cases h2 : r ∈ K₂ <;> by_cases h3 : b' ∈ K₃ <;>
      simp [indicator, hmem, h1, h2, h3]
  set a : SphC (splitForm c Q') c → ℝ≥0∞ := fun x => ∫⁻ h, A.indicator 1 (orbC s (x, h)) ∂μ'
  have hmA : Measurable (A.indicator (1 : ArchSOC (splitForm c Q') → ℝ≥0∞)) := measurable_one.indicator hA
  have ham : Measurable a := Measurable.lintegral_prod_right'
    (f := fun q : SphC (splitForm c Q') c × ArchSOC Q' => A.indicator 1 (orbC s q)) (hmA.comp (measurable_orbC s))
  have hmE : Measurable (E.indicator (1 : (Fin (m + 1) → Fin (m + 1) → ℂ) → ℝ≥0∞)) := measurable_one.indicator hE
  -- the inner integral over the columns 1..m
  have hcols : ∀ β : ℂˣ, β ∈ halfU → ∀ x : SphC (splitForm c Q') c,
      ∫⁻ X' : Fin m → Fin (m + 1) → ℂ, E.indicator 1 (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ)) X') =
        K₁.indicator 1 β * (volume K₂ * (kappa0 D' K₃ * a x)) := by
    intro β hβ x
    set S := ArchSOC.mat _ (s.toFun x)
    have hS : MeasurePreserving (fun (Y : Fin m → Fin (m + 1) → ℂ) j => S *ᵥ Y j) volume volume :=
      measurePreserving_pi _ _ fun _ => measurePreserving_mulVecC _ (by rw [ArchSOC.det_mat, norm_one])
    rw [← hS.lintegral_comp (f := fun X' => E.indicator 1 (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ)) X'))
      (hmE.comp (by fun_prop))]
    rw [lintegral_cols_splitC (G := fun Y : Fin m → Fin (m + 1) → ℂ =>
      E.indicator 1 (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ)) fun j => S *ᵥ Y j)) (hmE.comp (by fun_prop))]
    have hr : ∀ r : Fin m → ℂ, ∫⁻ Z : Fin m → Fin m → ℂ, E.indicator 1 (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ))
          fun j => S *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℂ)) =
        K₁.indicator 1 β * (K₂.indicator 1 r * (kappa0 D' K₃ * a x)) := by
      intro r
      set KZ : (Fin m → Fin m → ℂ) → ℝ≥0∞ := fun Z => E.indicator 1 (Fin.cons ((β : ℂ) • (x : Fin (m + 1) → ℂ))
          fun j => S *ᵥ (Fin.cons (r j) (Z j) : Fin (m + 1) → ℂ)) with hKZ
      have hKZm : Measurable KZ := hmE.comp (by fun_prop)
      have hslab : MeasurableSet ((univ : Set (ArchSOC Q')) ×ˢ V0 D') :=
        MeasurableSet.univ.prod (isOpen_V0 D').measurableSet
      have hinj' : InjOn (chart D') (univ ×ˢ V0 D') := injOn_chart D' (injOn_beta_V0 D')
      have hT : MeasurableSet (chart D' '' (univ ×ˢ V0 D')) :=
        hslab.image_of_continuousOn_injOn (continuous_chart D').continuousOn hinj'
      have hKZ0 : ∀ Z, Z ∉ chart D' '' (univ ×ˢ V0 D') → KZ Z = 0 := by
        intro Z hZ
        refine indicator_of_notMem (fun hmem => hZ ?_) _
        obtain ⟨⟨g, b⟩, ⟨-, hb⟩, he⟩ := hmem
        exact mem_chart'_of_mem hc D' s x hβ r Z g (hKW hb) he
      have hmap := Leray.map_restrict_fibreCount (continuous_chart D') (isLocInj_chart D') volume hslab hinj'
      rw [lintegral_eq_setLIntegral_of_vanish hT hKZ0, ← hmap, lintegral_map hKZm (continuous_chart D').measurable,
        lerayMeasureC_fibration hQ' D', ← Measure.prod_restrict, Measure.restrict_univ,
        lintegral_prod (f := fun z => KZ (chart D' z)) (hKZm.comp (continuous_chart D').measurable).aemeasurable]
      have hin : ∀ h : ArchSOC Q', ∫⁻ b', KZ (chart D' (h, b')) ∂(kappa0 D').restrict (V0 D') =
          A.indicator 1 (orbC s (x, h)) * (K₁.indicator 1 β * (K₂.indicator 1 r * kappa0 D' K₃)) := by
        intro h
        rw [setLIntegral_congr_fun (isOpen_V0 D').measurableSet (g := fun b' => A.indicator 1 (orbC s (x, h)) *
          (K₁.indicator 1 β * (K₂.indicator 1 r * K₃.indicator 1 b'))) (fun b' hb' => by
            simp only [hKZ]
            rw [← chart_orb_bk hc D' s x h β r b', hind _ _ ⟨(β, r, b'), ⟨hβ, mem_univ _, hb'⟩, rfl⟩, hindK])]
        rw [lintegral_const_mul _ (((measurable_one.indicator hK₃).const_mul _).const_mul _),
          lintegral_const_mul _ ((measurable_one.indicator hK₃).const_mul _),
          lintegral_const_mul _ (measurable_one.indicator hK₃), lintegral_indicator_one hK₃,
          Measure.restrict_apply hK₃, inter_eq_left.mpr hK₃V]
      simp_rw [hin]
      rw [lintegral_mul_const (f := fun h => A.indicator 1 (orbC s (x, h))) _
        (hmA.comp ((measurable_orbC s).comp (measurable_const.prodMk measurable_id)))]
      ring
    simp_rw [hr]
    rw [lintegral_const_mul _ ((measurable_one.indicator hK₂).mul_const _),
      lintegral_mul_const _ (measurable_one.indicator hK₂), lintegral_indicator_one hK₂]
  -- the first column in polar coordinates
  rw [← lintegral_indicator_one hE, lintegral_first_colC hmE]
  set H : (Fin (m + 1) → ℂ) → ℝ≥0∞ := fun y₀ => ∫⁻ X' : Fin m → Fin (m + 1) → ℂ, E.indicator 1 (Fin.cons y₀ X')
    with hHdef
  have hHm : Measurable H := Measurable.lintegral_prod_right'
    (f := fun q : (Fin (m + 1) → ℂ) × (Fin m → Fin (m + 1) → ℂ) => E.indicator 1 (Fin.cons q.1 q.2))
    (hmE.comp (by fun_prop))
  have hpolm : MeasurableSet (polC (splitForm c Q') c '' (halfU ×ˢ univ)) :=
    (isOpen_halfU.measurableSet.prod MeasurableSet.univ).image_of_continuousOn_injOn
      (continuous_polC _ _).continuousOn (injOn_polC_halfU hc)
  have hH0 : ∀ y₀, y₀ ∉ polC (splitForm c Q') c '' (halfU ×ˢ univ) → H y₀ = 0 := by
    intro y₀ hy₀
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun X' => indicator_of_notMem (fun hmem => hy₀ ?_) _)
    obtain ⟨⟨g, b⟩, ⟨-, hb⟩, he⟩ := hmem
    have := chart_zero_mem_polC hc D' g (hKW hb)
    rwa [he, Fin.cons_zero] at this
  rw [lintegral_eq_setLIntegral_of_vanish hpolm hH0, lintegral_polC_half hc hn1 hHm]
  rw [setLIntegral_congr_fun isOpen_halfU.measurableSet (g := fun β => K₁.indicator 1 β *
    (volume K₂ * (kappa0 D' K₃ * ∫⁻ x, a x ∂nuC (splitForm c Q') c))) (fun β hβ => by
      simp only [hHdef]
      simp_rw [hcols β hβ]
      rw [lintegral_const_mul _ ((ham.const_mul _).const_mul _), lintegral_const_mul _ (ham.const_mul _),
        lintegral_const_mul _ ham])]
  rw [lintegral_mul_const _ (measurable_one.indicator hK₁), setLIntegral_indicator hK₁, inter_eq_left.mpr hK₁h,
    Measure.prod_apply ((measurable_orbC s) hA)]
  have hI : ∫⁻ x, a x ∂nuC (splitForm c Q') c = ∫⁻ x, μ' (Prod.mk x ⁻¹' (orbC s ⁻¹' A)) ∂nuC (splitForm c Q') c := by
    refine lintegral_congr fun x => ?_
    rw [← lintegral_indicator_one (((measurable_orbC s) hA).preimage measurable_prodMk_left)]
    rfl
  simp only [Pi.one_apply, setLIntegral_one]
  rw [hI]
  ring

end Chart


/-! ### The complex archimedean orbital identity -/

section Orbital

variable {c : ℂ} (hc : c ≠ 0) {Q' : QuadForm ℂ m} (hQ' : gramDetC Q' ≠ 0)

/-- A small sector around $1$ in $\mathbb C^\times$. -/
def K1 : Set ℂˣ := {β | ‖(β : ℂ) - 1‖ < 1 / 2}

theorem isOpen_K1 : IsOpen K1 := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const))
  continuous_const

theorem K1_subset_halfU : K1 ⊆ halfU := by
  intro β hβ
  have h1 : |((β : ℂ) - 1).re| ≤ ‖(β : ℂ) - 1‖ := Complex.abs_re_le_norm _
  have h2 : ‖(β : ℂ) - 1‖ < 1 / 2 := hβ
  show 0 < (β : ℂ).re
  rw [Complex.sub_re, Complex.one_re] at h1
  have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
  linarith

theorem lamU_K1_pos : 0 < lamU (m + 1) K1 :=
  withDensity_wt_pos isOpen_K1 ⟨1, by simp [K1]⟩ _

theorem lamU_K1_lt_top : lamU (m + 1) K1 < ⊤ := by
  rw [lamU_succ_apply isOpen_K1.measurableSet]
  have hsub : Units.val '' K1 ⊆ Metric.ball (1 : ℂ) (1 / 2) := by
    rintro _ ⟨β, hβ, rfl⟩; rw [Metric.mem_ball, dist_eq_norm]; exact hβ
  calc ∫⁻ z in Units.val '' K1, ((‖z‖₊ ^ (2 * m) : ℝ≥0) : ℝ≥0∞)
      ≤ ∫⁻ _ in Units.val '' K1, ((2 : ℝ≥0) ^ (2 * m) : ℝ≥0) := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        refine ENNReal.coe_le_coe.mpr (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := hsub hz
        rw [Metric.mem_ball, dist_eq_norm] at h
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        have : ‖z‖ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := by
          calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        rw [norm_one] at this
        push_cast; linarith
    _ = ((2 : ℝ≥0) ^ (2 * m) : ℝ≥0) * volume (Units.val '' K1) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top)

/-- **The archimedean orbital identity at a complex place** (Weil's $\omega_G = \omega_{G/H}\wedge\omega_H$ for
$G = SO(Q)(\mathbb C)$, $H = SO(Q')(\mathbb C) = \mathrm{Stab}(e_0)$, $G/H \cong S_c$): for $Q = \langle c\rangle \perp Q'$
nondegenerate over $\mathbb C$ ($c \ne 0$), every measurable section $s$ of $g \mapsto ge_0$, and the complex Leray
measures $\mu_Q$, $\mu_{Q'}$ and $\sigma_c$ (`SphereLerayC.sigC`),
$$\mu_Q = |2c|_{\mathbb C}^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_c \otimes \mu_{Q'}),\qquad |z|_{\mathbb C} = |z|^2.$$ -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (matching gauge forms on G, H, G/H); §4.5 [unverified]"]
theorem lerayMeasureC_orbital (s : SphSectionC c Q') :
    lerayMeasureC (splitForm c Q') (gramDetC_splitForm_ne_zero hc hQ') =
      (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) •
        ((sigC (splitForm c Q') c).prod (lerayMeasureC Q' hQ')).map (orbC s) := by
  set D' := DiagC.ofExists Q' hQ'
  set D := splitDiagC hc D'
  have hQ := gramDetC_splitForm_ne_zero hc hQ'
  have hn1 : 1 ≤ m + 1 := by omega
  have := sigmaFinite_sigC (Q := splitForm c Q') hc hn1
  have := sigmaFinite_nuC (Q := splitForm c Q') hc hn1
  have := isHaarMeasure_lerayMeasureC hQ'
  obtain ⟨K₃, hK₃c, h1K₃, hK₃V⟩ := exists_compact_subset (isOpen_V0 D') (one_mem_V0 D')
  have hK₃ : MeasurableSet K₃ := hK₃c.isClosed.measurableSet
  have hK₃pos : 0 < kappa0 D' K₃ := measure_pos_of_mem_nhds _ (mem_interior_iff_mem_nhds.mp h1K₃)
  have hK₃top : kappa0 D' K₃ < ⊤ := hK₃c.measure_lt_top
  set K₂ : Set (Fin m → ℂ) := Metric.ball 0 1
  have hK₂ : MeasurableSet K₂ := Metric.isOpen_ball.measurableSet
  have hK₂pos : 0 < volume K₂ := Metric.measure_ball_pos _ _ one_pos
  have hK₂top : volume K₂ < ⊤ := measure_ball_lt_top
  set K := bk hc D' '' (K1 ×ˢ K₂ ×ˢ K₃)
  have hK : MeasurableSet K := measurableSet_bk_image hc D' (isOpen_K1.measurableSet.prod (hK₂.prod hK₃))
  have hKW : K ⊆ halfSlab hc D' := image_mono (prod_mono K1_subset_halfU (prod_mono (subset_univ _) hK₃V))
  set J := lamU (m + 1) K1 * (volume K₂ * kappa0 D' K₃)
  have hJ0 : J ≠ 0 := mul_ne_zero lamU_K1_pos.ne' (mul_ne_zero hK₂pos.ne' hK₃pos.ne')
  have hJtop : J ≠ ⊤ := ENNReal.mul_ne_top lamU_K1_lt_top.ne (ENNReal.mul_ne_top hK₂top.ne hK₃top.ne)
  set C : ℝ≥0∞ := ((‖2 * c‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
  have h2c : ‖2 * c‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc)
  have hC0 : C ≠ 0 := by simp [C, hc]
  have hκ : kappa0 D K = C * J :=
    kappa0_box hc D' isOpen_K1.measurableSet K1_subset_halfU hK₂ hK₃ hK₃V
  ext A hA
  have hmain : lerayMeasureC (splitForm c Q') hQ A * kappa0 D K =
      J * ((nuC (splitForm c Q') c).prod (lerayMeasureC Q' hQ')) (orbC s ⁻¹' A) := by
    rw [← Measure.prod_prod, ← lerayMeasureC_fibration hQ D,
      Leray.fibreCount_apply_of_injOn (continuous_chart D) (isLocInj_chart D) volume (hA.prod hK)
        ((injOn_chart D (injOn_beta_halfSlab hc D')).mono (prod_mono (subset_univ _) hKW)),
      volume_chart_box hc hQ' D' s hA isOpen_K1.measurableSet K1_subset_halfU hK₂ hK₃ hK₃V]
  rw [hκ, mul_comm C, ← mul_assoc, mul_comm _ J, mul_assoc] at hmain
  have hcancel := (ENNReal.mul_right_inj hJ0 hJtop).mp hmain
  rw [Measure.smul_apply, Measure.map_apply (measurable_orbC s) hA, sigC, Measure.prod_smul_left,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, ← hcancel, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_mul]
  have : ((‖2 * c‖₊ ^ (2 * m))⁻¹ * (‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) * ‖2 * c‖₊ ^ (2 * (m + 1)) = 1 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
    field_simp
  rw [mul_comm, ← mul_assoc, show C = ((‖2 * c‖₊ ^ (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) from rfl, ← ENNReal.coe_mul,
    mul_comm _ ((‖2 * c‖₊ ^ (2 * m))⁻¹ * (‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0), this, ENNReal.coe_one, one_mul]

/-- **The orbital identity in integral form** at a complex place: $\int_{SO(Q)} f\,d\mu_Q =
|2c|_{\mathbb C}^{-m}\int_{S_c}\int_{SO(Q')} f(s(x)\,\mathrm{diag}(1, h))\,d\mu_{Q'}(h)\,d\sigma_c(x)$. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, p. 25 (integration over G as an iterated integral over G/H and H) [unverified]"]
theorem lintegral_lerayMeasureC_orbital (s : SphSectionC c Q') {f : ArchSOC (splitForm c Q') → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasureC (splitForm c Q') (gramDetC_splitForm_ne_zero hc hQ') =
      (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, ∫⁻ h, f (s.toFun x * iotaC c Q' h) ∂lerayMeasureC Q' hQ' ∂sigC (splitForm c Q') c := by
  have := sigmaFinite_sigC (Q := splitForm c Q') hc (by omega)
  have := isHaarMeasure_lerayMeasureC hQ'
  rw [lerayMeasureC_orbital hc hQ' s, lintegral_smul_measure, lintegral_map hf (measurable_orbC s),
    lintegral_prod (fun p => f (orbC s p)) (hf.comp (measurable_orbC s)).aemeasurable, smul_eq_mul]
  rfl

/-- **Total masses** at a complex place: $\mu_Q(SO(Q)) = |2c|_{\mathbb C}^{-m}\,\sigma_c(S_c)\,\mu_{Q'}(SO(Q'))$. -/
theorem lerayMeasureC_univ_orbital (s : SphSectionC c Q') :
    lerayMeasureC (splitForm c Q') (gramDetC_splitForm_ne_zero hc hQ') univ =
      (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (sigC (splitForm c Q') c univ * lerayMeasureC Q' hQ' univ) := by
  have := sigmaFinite_sigC (Q := splitForm c Q') hc (by omega)
  have := isHaarMeasure_lerayMeasureC hQ'
  rw [lerayMeasureC_orbital hc hQ' s, Measure.smul_apply, Measure.map_apply (measurable_orbC s) MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, smul_eq_mul]

end Orbital


/-! ### A measurable section from reflections (`sphereSec` over $\mathbb C$) -/

section Section

open QuadFormsKB.Tamagawa.Measure.Weil

variable {c : ℂ} {Q' : QuadForm ℂ m}

theorem qH_gramC {n : ℕ} (Q : QuadForm ℂ n) (x : Fin n → ℂ) : qH (gramC Q) x = Q.eval x :=
  (eval_eq_gramC Q x).symm

theorem continuous_refl_comp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {X : Type*} [TopologicalSpace X]
    {f : X → Fin n → ℂ} (hf : Continuous f) (hne : ∀ x, qH H (f x) ≠ 0) : Continuous fun x => Weil.refl H (f x) := by
  have hq : Continuous fun x => qH H (f x) := hf.dotProduct (continuous_const.matrix_mulVec hf)
  have hv : Continuous fun x => vecMulVec (f x) (H *ᵥ f x) := by
    refine continuous_matrix fun i j => ?_
    simp only [vecMulVec_apply]
    exact ((continuous_apply i).comp hf).mul ((continuous_apply j).comp (continuous_const.matrix_mulVec hf))
  unfold Weil.refl
  exact continuous_const.sub ((continuous_const.div hq hne).smul hv)

theorem qH_e₀ (hc : c ≠ 0) : qH (gramC (splitForm c Q')) (e₀ : Fin (m + 1) → ℂ) ≠ 0 := by
  rw [qH_gramC]
  show (splitForm c Q').evalIn ℂ e₀ ≠ 0
  rw [evalIn_splitForm_e₀]; simpa using hc

/-- **Sphere data** for $Q = \langle c\rangle \perp Q'$ over $\mathbb C$: base point $e_0$ and an anisotropic
$w \perp e_0$ ($m \ge 1$, `exists_orth_anisotropic`). -/
def sphDataC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) : SphereData (gramC (splitForm c Q')) :=
  have h := exists_orth_anisotropic (gramC_transpose (splitForm c Q')) two_ne_zero
    (gramDetC_splitForm_ne_zero hc hQ') (by omega) (qH_e₀ hc)
  ⟨e₀, h.choose, qH_e₀ hc, h.choose_spec.1, h.choose_spec.2⟩

theorem qH_sph (x : SphC (splitForm c Q') c) :
    qH (gramC (splitForm c Q')) (x : Fin (m + 1) → ℂ) = qH (gramC (splitForm c Q')) e₀ := by
  rw [qH_gramC, qH_gramC, x.2]
  show c = (splitForm c Q').evalIn ℂ e₀
  rw [evalIn_splitForm_e₀]; rfl

theorem sphereSec_det (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) (x : SphC (splitForm c Q') c) :
    (sphereSec (sphDataC hc hm hQ') (x : Fin (m + 1) → ℂ)).det = 1 :=
  (sphereSec_mem (gramC_transpose _) two_ne_zero (sphDataC hc hm hQ') (qH_sph x)).2

theorem toGL_sphereSec_mem (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) (x : SphC (splitForm c Q') c) :
    toGL (sphereSec (sphDataC hc hm hQ') (x : Fin (m + 1) → ℂ)) ∈ soC (splitForm c Q') := by
  have h := sphereSec_mem (gramC_transpose _) two_ne_zero (sphDataC hc hm hQ') (qH_sph x)
  rw [mem_soC_iff, toGL_val (by rw [h.2]; exact one_ne_zero)]
  exact h

/-- **The explicit section** $x \mapsto s(x)$, $s(x) = \tau_{x+e_0}\tau_{e_0}$ or $\tau_{x-e_0}\tau_w$. -/
def secFunC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) (x : SphC (splitForm c Q') c) : ArchSOC (splitForm c Q') :=
  ArchSOC.mk _ _ (toGL_sphereSec_mem hc hm hQ' x)

theorem mat_secFunC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) (x : SphC (splitForm c Q') c) :
    ArchSOC.mat _ (secFunC hc hm hQ' x) = sphereSec (sphDataC hc hm hQ') (x : Fin (m + 1) → ℂ) := by
  rw [secFunC, ArchSOC.mat_mk, toGL_val (by rw [sphereSec_det]; exact one_ne_zero)]

theorem measurable_secFunC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) : Measurable (secFunC hc hm hQ') := by
  classical
  have hcont : Continuous fun x : SphC (splitForm c Q') c => qH (gramC (splitForm c Q')) ((x : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) :=
    (continuous_subtype_val.add continuous_const).dotProduct
      (continuous_const.matrix_mulVec (continuous_subtype_val.add continuous_const))
  set U1 : Set (SphC (splitForm c Q') c) := {x | qH (gramC (splitForm c Q')) ((x : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) ≠ 0}
  have hU1 : MeasurableSet U1 := hcont.measurable (measurableSet_singleton 0).compl
  have hgl : ∀ {Y : Type} [TopologicalSpace Y] (M : Y → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      (hM : Continuous M) (hdet : ∀ y, (M y).det ≠ 0) (hmem : ∀ y, toGL (M y) ∈ soC (splitForm c Q')),
      Continuous fun y => (ArchSOC.mk _ (toGL (M y)) (hmem y) : ArchSOC (splitForm c Q')) := by
    intro Y _ M hM hdet hmem
    exact Continuous.subtype_mk (continuousOn_toGL.comp_continuous hM hdet) _
  refine measurable_of_restrict_of_restrict_compl hU1 ?_ ?_
  · have hv : Continuous fun y : U1 => ((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀ :=
      (continuous_subtype_val.comp continuous_subtype_val).add continuous_const
    have hM : Continuous fun y : U1 => Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) *
        Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').x₀ := (continuous_refl_comp (gramC (splitForm c Q')) hv fun y => y.2).matrix_mul continuous_const
    have e : ∀ y : U1, sphereSec (sphDataC hc hm hQ') ((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) =
        Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) * Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').x₀ := fun y => by
      rw [sphereSec, if_pos (show qH (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) ≠ 0 from y.2)]
    have hc' := hgl (fun y : U1 => Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) + (sphDataC hc hm hQ').x₀) *
        Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').x₀) hM (fun y : U1 => by rw [← e y, sphereSec_det hc hm hQ' y.1]; exact one_ne_zero)
      (fun y : U1 => by rw [← e y]; exact toGL_sphereSec_mem hc hm hQ' y.1)
    convert hc'.measurable using 1
    funext y
    exact Subtype.ext (congrArg toGL (e y))
  · have hv : Continuous fun y : ↥U1ᶜ => ((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) - (sphDataC hc hm hQ').x₀ :=
      (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const
    have hne : ∀ y : ↥U1ᶜ, qH (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) - (sphDataC hc hm hQ').x₀) ≠ 0 := fun y =>
      qH_sub_ne_zero (gramC_transpose _) two_ne_zero (sphDataC hc hm hQ') (qH_sph y.1) (not_not.mp y.2)
    have hM : Continuous fun y : ↥U1ᶜ => Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) - (sphDataC hc hm hQ').x₀) *
        Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').w := (continuous_refl_comp (gramC (splitForm c Q')) hv hne).matrix_mul continuous_const
    have e : ∀ y : ↥U1ᶜ, sphereSec (sphDataC hc hm hQ') ((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) =
        Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) - (sphDataC hc hm hQ').x₀) * Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').w := fun y => by
      rw [sphereSec, if_neg (show ¬ qH (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) +
        (sphDataC hc hm hQ').x₀) ≠ 0 from y.2)]
    have hc' := hgl (fun y : ↥U1ᶜ => Weil.refl (gramC (splitForm c Q')) (((y : SphC (splitForm c Q') c) : Fin (m + 1) → ℂ) - (sphDataC hc hm hQ').x₀) *
        Weil.refl (gramC (splitForm c Q')) (sphDataC hc hm hQ').w) hM
      (fun y : ↥U1ᶜ => by rw [← e y, sphereSec_det hc hm hQ' y.1]; exact one_ne_zero)
      (fun y : ↥U1ᶜ => by rw [← e y]; exact toGL_sphereSec_mem hc hm hQ' y.1)
    convert hc'.measurable using 1
    funext y
    exact Subtype.ext (congrArg toGL (e y))

/-- **A measurable section exists** at a complex place ($m \ge 1$, $Q'$ nondegenerate): $SO(Q)(\mathbb C)$ is
transitive on $S_c$, with an explicit measurable section from two reflections (`sphereSec`). -/
def sphSectionC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) : SphSectionC c Q' where
  toFun := secFunC hc hm hQ'
  measurable := measurable_secFunC hc hm hQ'
  spec x := by
    rw [mat_secFunC]
    exact sphereSec_mulVec (gramC_transpose _) two_ne_zero (sphDataC hc hm hQ') (qH_sph x)

/-- **Transitivity**: $SO(Q)(\mathbb C)$ acts transitively on $S_c$ ($m \ge 1$). -/
theorem exists_mulVec_e₀_eqC (hc : c ≠ 0) (hm : 1 ≤ m) (hQ' : gramDetC Q' ≠ 0) (x : SphC (splitForm c Q') c) :
    ∃ g : ArchSOC (splitForm c Q'), ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ) = x :=
  ⟨_, (sphSectionC hc hm hQ').spec x⟩

end Section

/-! ### Packaging: the local factor at a complex place of a number field -/

section NF

open NumberField NumberField.InfinitePlace

/-- **The archimedean orbital identity at a complex place of a number field** $F$: for $Q_0 = \langle c_0\rangle \perp
Q_0'$ over $F$ ($c_0 \ne 0$) and a complex place $w$ with embedding $\sigma_w$, the local form
$Q_0^{\sigma_w} = \langle\sigma_w(c_0)\rangle \perp Q_0'^{\sigma_w}$ satisfies
$$\mu_{Q_0^{\sigma_w}} = |2c_0|_w^{-m}\cdot(\mathrm{orb}_s)_*(\sigma_{\sigma_w(c_0)} \otimes \mu_{Q_0'^{\sigma_w}}),\qquad
|x|_w = w(x)^2$$
(the normalized absolute value at a complex place). Together with `OrbitalReal.lerayMeasure_orbital_realPlace`
($|x|_w = w(x)$ at real places) the archimedean constants are $\prod_{w \mid \infty}|2c_0|_w^{-m}$; with the finite-place
factors $|2c_0|_v^{-m}$ their product over all places is $1$ by the product formula. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3, p. 25; §4.5 (local factors at the infinite places) [unverified]"]
theorem lerayMeasureC_orbital_complexPlace {F : Type*} [Field F] [NumberField F]
    (w : {w : InfinitePlace F // w.IsComplex}) {c₀ : F} (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm F m)
    (hQ' : gramDetC (Q₀'.map w.1.embedding) ≠ 0) (s : SphSectionC (w.1.embedding c₀) (Q₀'.map w.1.embedding)) :
    lerayMeasureC (splitForm (w.1.embedding c₀) (Q₀'.map w.1.embedding))
        (gramDetC_splitForm_ne_zero ((map_ne_zero _).mpr hc₀) hQ') =
      ENNReal.ofReal (((w.1 (2 * c₀) ^ 2) ^ m)⁻¹) •
        ((sigC (splitForm (w.1.embedding c₀) (Q₀'.map w.1.embedding)) (w.1.embedding c₀)).prod
          (lerayMeasureC _ hQ')).map (orbC s) := by
  rw [lerayMeasureC_orbital ((map_ne_zero _).mpr hc₀) hQ' s, ← norm_embedding_eq, map_mul, map_ofNat,
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  push_cast
  rw [← pow_mul]

end NF

end QuadFormsKB.Tamagawa.Measure.OrbitalComplex
