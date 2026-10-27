/-
# The archimedean test set of the non-square model over every number field

**Layer:** $F$ any number field, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$; $Q_0 = \langle1,-ad,-bd,abd\rangle$ (`qNS`).

* Transport of the Leray and sphere measures along an equality of forms (`lerayMeasure_congr_mat`, `sig_congr_val`).
* **`URset v`** at a real place $v$ of $F$: the image $\varphi_v(Y_v)$ of the local test set ($Y_v = $ `posR`$^2$ if $d_v>0$,
  $Y_v = $ `posC` if $d_v<0$) under the local map (`phiSplit` resp. `phiNS`), as a subset of $SO(Q_0^{\sigma_v})(\mathbb R)$;
  measurable, with $\mathrm{Leray}(U_v) = \kappa_v\,\sigma(Y_v)$ (`leray_URset`).
* **`pos_of_nsR_mem_URset`**: if $\varphi_v(g)\in U_v$ then $g_{2,v}>0$.

Source: Weil 1982, §2.3, Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSBridgeR
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchTestSets
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSTestAny

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex SphereLeray SphereLerayC

/-! ### Transport along an equality of forms -/

section Transport

variable {n : ℕ}

theorem lerayMeasure_congr_mat {Q Q' : QuadForm ℝ n} (h : Q = Q') (hQ : gramDetR Q ≠ 0) (hQ' : gramDetR Q' ≠ 0)
    (T : Set (Matrix (Fin n) (Fin n) ℝ)) :
    lerayMeasure Q hQ {g | ArchSOInst.mat Q g ∈ T} = lerayMeasure Q' hQ' {g | ArchSOInst.mat Q' g ∈ T} := by
  subst h; rfl

theorem lerayMeasureC_congr_mat {Q Q' : QuadForm ℂ n} (h : Q = Q') (hQ : gramDetC Q ≠ 0) (hQ' : gramDetC Q' ≠ 0)
    (T : Set (Matrix (Fin n) (Fin n) ℂ)) :
    lerayMeasureC Q hQ {g | ArchSOC.mat Q g ∈ T} = lerayMeasureC Q' hQ' {g | ArchSOC.mat Q' g ∈ T} := by
  subst h; rfl

theorem sig_congr_val {Q Q' : QuadForm ℝ n} (h : Q = Q') (T : Set (Fin n → ℝ)) :
    sig Q 1 {x | (x : Fin n → ℝ) ∈ T} = sig Q' 1 {x | (x : Fin n → ℝ) ∈ T} := by
  subst h; rfl

theorem sigC_congr_val {Q Q' : QuadForm ℂ n} (h : Q = Q') (T : Set (Fin n → ℂ)) :
    sigC Q 1 {x | (x : Fin n → ℂ) ∈ T} = sigC Q' 1 {x | (x : Fin n → ℂ) ∈ T} := by
  subst h; rfl

theorem mat_injective (Q : QuadForm ℝ n) : Function.Injective (ArchSOInst.mat Q) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem matC_injective (Q : QuadForm ℂ n) : Function.Injective (ArchSOC.mat Q) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem setOf_mat_mem_image (Q : QuadForm ℝ n) (S : Set (ArchSO Q)) :
    {g | ArchSOInst.mat Q g ∈ ArchSOInst.mat Q '' S} = S :=
  (mat_injective Q).preimage_image S

theorem setOf_matC_mem_image (Q : QuadForm ℂ n) (S : Set (ArchSOC Q)) :
    {g | ArchSOC.mat Q g ∈ ArchSOC.mat Q '' S} = S :=
  (matC_injective Q).preimage_image S

theorem gramDetR_diag (c : Fin n → ℝ) : gramDetR (QuadForm.diag c) = ∏ i, c i := by
  have h : (QuadForm.diag c).hessian.det = 2 ^ n * ∏ i, c i := by
    unfold QuadForm.hessian QuadForm.diag
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
    rw [Finset.prod_congr rfl fun i _ => (two_mul (c i)).symm, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [gramDetR, h]; field_simp

end Transport

/-! ### Vector conditions -/

/-- $\{x : x_0>0,\ \|x\|<2\}\subseteq\mathbb R^4$. -/
def posVecR : Set (Fin 4 → ℝ) := {x | 0 < x 0 ∧ ‖x‖ < 2}

/-- $\{x : \operatorname{Re}x_0>0,\ \|x\|<2\}\subseteq\mathbb C^4$. -/
def posVecC : Set (Fin 4 → ℂ) := {x | 0 < (x 0).re ∧ ‖x‖ < 2}

theorem posR_eq (A B : ℝ) :
    NSArch.posR A B = ({x | (x : Fin 4 → ℝ) ∈ posVecR} : Set (Sph (NSArch.normForm A B) 1)) := rfl

theorem posC_eq (A B : ℂ) :
    NSArch.posC A B = ({x | (x : Fin 4 → ℂ) ∈ posVecC} : Set (SphC (NSArch.normForm A B) 1)) := rfl

/-! ### The local test sets at the real places of $F$ -/

section RealPlaces

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

local notation "Av" v => embedding_of_isReal (Subtype.prop v) ((a : 𝓞 F) : F)

include hb₀ hb₁ in
theorem exists_split_places (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    ∃ p : {w : InfinitePlace K // w.IsReal} × {w : InfinitePlace K // w.IsReal},
      p.1.1.comap (algebraMap F K) = v.1 ∧ p.2.1.comap (algebraMap F K) = v.1 ∧
      embedding_of_isReal p.2.2 (bK 1) = - embedding_of_isReal p.1.2 (bK 1) ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = p.1.1 ∨ w = p.2.1) := by
  obtain ⟨w₁, w₂, -, h₁, h₂, hall, -, h⟩ := exists_two_real_places bK hb₀ hb₁ v hv
  exact ⟨(w₁, w₂), h₁, h₂, h, hall⟩

/-- The two real places of $K$ over a real $v$ with $d_v>0$ (a choice). -/
def splitPlaces (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    {w : InfinitePlace K // w.IsReal} × {w : InfinitePlace K // w.IsReal} :=
  Classical.choose (exists_split_places hb₀ hb₁ v hv)

theorem splitPlaces_spec (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    (splitPlaces hb₀ hb₁ v hv).1.1.comap (algebraMap F K) = v.1 ∧
      (splitPlaces hb₀ hb₁ v hv).2.1.comap (algebraMap F K) = v.1 ∧
      embedding_of_isReal (splitPlaces hb₀ hb₁ v hv).2.2 (bK 1) =
        - embedding_of_isReal (splitPlaces hb₀ hb₁ v hv).1.2 (bK 1) ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 →
        w = (splitPlaces hb₀ hb₁ v hv).1.1 ∨ w = (splitPlaces hb₀ hb₁ v hv).2.1) :=
  Classical.choose_spec (exists_split_places hb₀ hb₁ v hv)

/-- $t_v = \delta_{w_1}$. -/
def tSplit (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) : ℝ :=
  embedding_of_isReal (splitPlaces hb₀ hb₁ v hv).1.2 (bK 1)

theorem tSplit_sq (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    tSplit hb₀ hb₁ v hv ^ 2 = embedding_of_isReal v.2 (d : F) :=
  embedding_of_isReal_delta_sq bK hb₁ v _ (splitPlaces_spec hb₀ hb₁ v hv).1

theorem tSplit_ne_zero (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    tSplit hb₀ hb₁ v hv ≠ 0 := by
  intro h
  have := tSplit_sq hb₀ hb₁ v hv
  rw [h, zero_pow two_ne_zero] at this
  exact hv.ne this

include hb₀ hb₁ in
theorem exists_ns_place (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) :
    ∃ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v.1 ∧
      (w.1.embedding (bK 1)).re = 0 ∧ w.1.embedding (bK 1) ^ 2 = ((embedding_of_isReal v.2 (d : F) : ℝ) : ℂ) ∧
      (∀ w' : InfinitePlace K, w'.comap (algebraMap F K) = v.1 → w' = w.1) := by
  obtain ⟨w, h₁, hall, -, h₂, h₃⟩ := exists_unique_complex_place bK hb₀ hb₁ v hv
  exact ⟨w, h₁, h₂, h₃, hall⟩

/-- The complex place of $K$ over a real $v$ with $d_v<0$ (a choice). -/
def nsPlace (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) :
    {w : InfinitePlace K // w.IsComplex} :=
  Classical.choose (exists_ns_place hb₀ hb₁ v hv)

theorem nsPlace_spec (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) :
    (nsPlace hb₀ hb₁ v hv).1.comap (algebraMap F K) = v.1 ∧ ((nsPlace hb₀ hb₁ v hv).1.embedding (bK 1)).re = 0 ∧
      (nsPlace hb₀ hb₁ v hv).1.embedding (bK 1) ^ 2 = ((embedding_of_isReal v.2 (d : F) : ℝ) : ℂ) ∧
      (∀ w' : InfinitePlace K, w'.comap (algebraMap F K) = v.1 → w' = (nsPlace hb₀ hb₁ v hv).1) :=
  Classical.choose_spec (exists_ns_place hb₀ hb₁ v hv)

/-- $s_v = \delta_{w'}$ ($s_v^2 = d_v<0$, $\operatorname{Re}s_v = 0$). -/
def sNs (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) : ℂ :=
  (nsPlace hb₀ hb₁ v hv).1.embedding (bK 1)

theorem sNs_ne_zero (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) :
    (nsPlace hb₀ hb₁ v hv).1.embedding (bK 1) ≠ 0 := by
  intro h
  have := (nsPlace_spec hb₀ hb₁ v hv).2.2.1
  rw [h, zero_pow two_ne_zero] at this
  have h0 : embedding_of_isReal v.2 (d : F) = 0 := Complex.ofReal_eq_zero.1 this.symm
  exact hv.ne h0

open Classical in
/-- **The matrix set $\varphi_v(Y_v)$** at a real place $v$ of $F$. -/
def TRset (v : {v : InfinitePlace F // v.IsReal}) : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  if hv : 0 < embedding_of_isReal v.2 (d : F) then
    (fun p => ArchSOInst.mat _ (NSArch.phiSplit (A := embedding_of_isReal v.2 (a : F))
      (B := embedding_of_isReal v.2 (b : F)) (tSplit_ne_zero hb₀ hb₁ v hv) (tSplit_sq hb₀ hb₁ v hv) p)) ''
      (NSArch.posR _ _ ×ˢ NSArch.posR _ _)
  else if hv' : embedding_of_isReal v.2 (d : F) < 0 then
    (fun x => ArchSOInst.mat _ (NSArch.phiNS (A := embedding_of_isReal v.2 (a : F))
      (B := embedding_of_isReal v.2 (b : F)) (nsPlace_spec hb₀ hb₁ v hv').2.2.1 (nsPlace_spec hb₀ hb₁ v hv').2.1
        (sNs_ne_zero hb₀ hb₁ v hv') x)) '' NSArch.posC _ _
  else ∅

/-- **The local test set $U_v\subseteq SO(Q_0^{\sigma_v})(\mathbb R)$.** -/
def URset (v : {v : InfinitePlace F // v.IsReal}) : Set (ArchSO (QRe (qNS a b d) v)) :=
  {g | ArchSOInst.mat _ g ∈ TRset (a := a) (b := b) hb₀ hb₁ v}

theorem TRset_split (v : {v : InfinitePlace F // v.IsReal}) (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    TRset (a := a) (b := b) hb₀ hb₁ v = ArchSOInst.mat _ '' (NSArch.phiSplit (A := embedding_of_isReal v.2 (a : F))
      (B := embedding_of_isReal v.2 (b : F)) (tSplit_ne_zero hb₀ hb₁ v hv) (tSplit_sq hb₀ hb₁ v hv) ''
        (NSArch.posR _ _ ×ˢ NSArch.posR _ _)) := by
  rw [TRset, dif_pos hv, Set.image_image]

theorem TRset_ns (v : {v : InfinitePlace F // v.IsReal}) (hv : embedding_of_isReal v.2 (d : F) < 0) :
    TRset (a := a) (b := b) hb₀ hb₁ v = ArchSOInst.mat _ '' (NSArch.phiNS (A := embedding_of_isReal v.2 (a : F))
      (B := embedding_of_isReal v.2 (b : F)) (nsPlace_spec hb₀ hb₁ v hv).2.2.1 (nsPlace_spec hb₀ hb₁ v hv).2.1
        (sNs_ne_zero hb₀ hb₁ v hv) '' NSArch.posC _ _) := by
  rw [TRset, dif_neg (not_lt.2 hv.le), dif_pos hv, Set.image_image]

theorem ne_zero_of_algebraMap_ne {x : F} (hx : x ≠ 0) (v : {v : InfinitePlace F // v.IsReal}) :
    embedding_of_isReal v.2 x ≠ 0 := (map_ne_zero _).2 hx

theorem measurableSet_TRset (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : {v : InfinitePlace F // v.IsReal}) :
    MeasurableSet (TRset (a := a) (b := b) hb₀ hb₁ v) := by
  have hA := ne_zero_of_algebraMap_ne ha0 v
  rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne hd0 v) with hv | hv
  · rw [TRset_ns hb₀ hb₁ v hv, Set.image_image]
    exact NSArch.measurableSet_posC.image_of_continuousOn_injOn
      ((ArchSOInst.continuous_mat _).comp (NSArch.continuous_phiNS _ _ _)).continuousOn
      ((mat_injective _).comp_injOn (NSArch.injOn_phiNS_posC _ _ _ hA))
  · rw [TRset_split hb₀ hb₁ v hv, Set.image_image]
    exact (NSArch.measurableSet_posR.prod NSArch.measurableSet_posR).image_of_continuousOn_injOn
      ((ArchSOInst.continuous_mat _).comp (NSArch.continuous_phiSplit _ _)).continuousOn
      ((mat_injective _).comp_injOn (NSArch.injOn_phiSplit_posR _ _ hA))

theorem measurableSet_URset (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : {v : InfinitePlace F // v.IsReal}) :
    MeasurableSet (URset (a := a) (b := b) hb₀ hb₁ v) :=
  (measurableSet_TRset hb₀ hb₁ ha0 hd0 v).preimage (ArchSOInst.continuous_mat _).measurable

theorem gramDetR_pureForm_ne {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) : gramDetR (pureForm A B) ≠ 0 := by
  rw [pureForm, gramDetR_diag, Fin.prod_univ_three]
  simp [hA, hB]

theorem gramDetR_pureFormD_ne {A B d : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    gramDetR (NSArch.pureFormD A B d) ≠ 0 := by
  rw [NSArch.pureFormD, gramDetR_diag, Fin.prod_univ_three]
  simp [hA, hB, hd]

theorem gramDetR_nsFormR_ne {A B d : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    gramDetR (NSArch.nsFormR A B d) ≠ 0 := by
  rw [NSArch.nsFormR_eq_diag, gramDetR_diag, Fin.prod_univ_four]
  simp [hA, hB, hd]

theorem abs_pow_three_mul_six {t d : ℝ} (ht : t ^ 2 = d) :
    |t| ^ 3 * |d| ^ 6 = |d| ^ ((15 : ℝ) / 2) := by
  have h1 : |t| = |d| ^ ((1 : ℝ) / 2) := by
    rw [← ht, abs_pow, sq_abs, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add' (abs_nonneg _)]
  · norm_num
  · norm_num

theorem norm_pow_three_mul_six {s : ℂ} {d : ℝ} (ht : s ^ 2 = (d : ℂ)) :
    |d| ^ 6 * ‖s‖ ^ 3 = |d| ^ ((15 : ℝ) / 2) := by
  have h1 : ‖s‖ = |d| ^ ((1 : ℝ) / 2) := by
    have h2 : ‖s‖ ^ 2 = |d| := by rw [← norm_pow, ht, Complex.norm_real, Real.norm_eq_abs]
    rw [← Real.sqrt_eq_rpow, ← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add' (abs_nonneg _)]
  · norm_num
  · norm_num

/-- **The Leray measure of $U_v$, $d_v>0$**: $\mathrm{Leray}(U_v) = (32|a_v|^3|b_v|^3|d_v|^{15/2})^{-1}\sigma(Y)^2$. -/
theorem leray_URset_split (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (v : {v : InfinitePlace F // v.IsReal})
    (hv : 0 < embedding_of_isReal v.2 (d : F)) :
    lerayMeasure (QRe (qNS a b d) v) (gramDetR_QRe_ne_zero _ hQ v) (URset (a := a) (b := b) hb₀ hb₁ v) =
      ENNReal.ofReal (1 / (32 * |embedding_of_isReal v.2 (a : F)| ^ 3 * |embedding_of_isReal v.2 (b : F)| ^ 3 *
        |embedding_of_isReal v.2 (d : F)| ^ ((15 : ℝ) / 2))) *
        (sig (NSArch.normForm (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))) 1
          (NSArch.posR _ _)) ^ 2 := by
  have hA := ne_zero_of_algebraMap_ne ha0 v
  have hB := ne_zero_of_algebraMap_ne hb0 v
  have hD := ne_zero_of_algebraMap_ne hd0 v
  rw [URset, TRset_split hb₀ hb₁ v hv,
    lerayMeasure_congr_mat (QRe_qNS a b d v) _ (gramDetR_nsFormR_ne hA hB hD), setOf_mat_mem_image,
    NSArch.leray_phiSplit_image _ _ hA hB hD (gramDetR_pureForm_ne hA hB) (gramDetR_pureFormD_ne hA hB hD) _
      (NSArch.measurableSet_posR.prod NSArch.measurableSet_posR) (NSArch.injOn_phiSplit_posR _ _ hA),
    Measure.prod_prod, sq, mul_assoc (32 : ℝ), mul_assoc (32 * _), mul_assoc,
    abs_pow_three_mul_six (tSplit_sq hb₀ hb₁ v hv)]
  ring_nf

/-- **The Leray measure of $U_v$, $d_v<0$**: $\mathrm{Leray}(U_v) = (4|a_v|^3|b_v|^3|d_v|^{15/2})^{-1}\sigma_{\mathbb C}(Y)$. -/
theorem leray_URset_ns (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (v : {v : InfinitePlace F // v.IsReal})
    (hv : embedding_of_isReal v.2 (d : F) < 0) :
    lerayMeasure (QRe (qNS a b d) v) (gramDetR_QRe_ne_zero _ hQ v) (URset (a := a) (b := b) hb₀ hb₁ v) =
      ENNReal.ofReal (1 / (4 * |embedding_of_isReal v.2 (a : F)| ^ 3 * |embedding_of_isReal v.2 (b : F)| ^ 3 *
        |embedding_of_isReal v.2 (d : F)| ^ ((15 : ℝ) / 2))) *
        sigC (NSArch.normForm ((embedding_of_isReal v.2 (a : F) : ℝ) : ℂ) ((embedding_of_isReal v.2 (b : F) : ℝ) : ℂ)) 1
          (NSArch.posC _ _) := by
  have hA := ne_zero_of_algebraMap_ne ha0 v
  have hB := ne_zero_of_algebraMap_ne hb0 v
  have hD := ne_zero_of_algebraMap_ne hd0 v
  rw [URset, TRset_ns hb₀ hb₁ v hv,
    lerayMeasure_congr_mat (QRe_qNS a b d v) _ (gramDetR_nsFormR_ne hA hB hD), setOf_mat_mem_image,
    NSArch.leray_phiNS_image _ _ _ hA hB hD (gramDetR_pureForm_ne hA hB) (gramDetR_pureFormD_ne hA hB hD) _
      NSArch.measurableSet_posC (NSArch.injOn_phiNS_posC _ _ _ hA)]
  congr 3
  rw [mul_assoc (4 * _ * _), norm_pow_three_mul_six (nsPlace_spec hb₀ hb₁ v hv).2.2.1]

end RealPlaces

/-! ### The global map at the real places -/

section GlobalReal

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F))
  (hA0 : A' ≠ 0) (hB0 : B' ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

local notation "MM" => (QuatAdele (F := K) A' B')ˣ

theorem fAtR_unit_ne_zero (v : {v : InfinitePlace F // v.IsReal}) (t : (Adeles F)ˣ) :
    fAtR v (t : Adeles F) ≠ 0 :=
  (t.isUnit.map (fAtR v)).ne_zero

theorem nrd_psiR_nsXR (v : {v : InfinitePlace F // v.IsReal}) {t : ℝ} (ht : t ^ 2 = embedding_of_isReal v.2 (d : F))
    (g : (gnatBC bK 0 hb₀ hA0 hB0).G) : nrd (psiR t ht (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)) = fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) := by
  have := nrd_psi (RingHom.id ℝ) t ht rfl rfl (nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g) _
    (nrdE_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v g)
  rw [nrdK_nsXR] at this
  exact this

include hd0 in
/-- **If $\varphi_v(g)\in U_v$ then $g_{2,v}>0$** (the reduced norm is a square on the image of $\mathrm{SL}_1$). -/
theorem pos_of_nsR_mem_URset (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg : nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g ∈ URset (a := a) (b := b) hb₀ hb₁ v) :
    0 < fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) := by
  have hu : fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) ≠ 0 := fAtR_unit_ne_zero v _
  have hA := ne_zero_of_algebraMap_ne ha0 v
  rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne hd0 v) with hv | hv
  · rw [URset, mem_ofPred_eq, TRset_ns hb₀ hb₁ v hv] at hg
    obtain ⟨_, ⟨y, -, rfl⟩, hy⟩ := hg
    obtain ⟨hw, htre, ht, -⟩ := nsPlace_spec hb₀ hb₁ v hv
    have e := mat_nsR_cx hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v (nsPlace hb₀ hb₁ v hv) hw rfl htre ht g
    rw [← hy, NSArch.mat_phiNS] at e
    have h := congrArg (fun M => fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) • M) e
    simp only [smul_smul, mul_inv_cancel₀ hu, one_smul] at h
    exact NSArch.pos_of_MR_eq_smul hA htre (sNs_ne_zero hb₀ hb₁ v hv) hu (NSArch.nrd_sphC y) h.symm
  · rw [URset, mem_ofPred_eq, TRset_split hb₀ hb₁ v hv] at hg
    obtain ⟨_, ⟨p, -, rfl⟩, hp⟩ := hg
    obtain ⟨h₁, h₂, h₁₂, -⟩ := splitPlaces_spec hb₀ hb₁ v hv
    have ht := tSplit_sq hb₀ hb₁ v hv
    have ht0 := tSplit_ne_zero hb₀ hb₁ v hv
    have e := mat_nsR_real hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v hv _ _ h₁ h₂ rfl h₁₂ g
    rw [← hp, NSArch.mat_phiSplit] at e
    have hconj : ∀ M N : Matrix (Fin 4) (Fin 4) ℝ,
        NSArch.tInv (tSplit hb₀ hb₁ v hv) * M * NSArch.tMat (tSplit hb₀ hb₁ v hv) =
          NSArch.tInv (tSplit hb₀ hb₁ v hv) * N * NSArch.tMat (tSplit hb₀ hb₁ v hv) → M = N := fun M N h => by
      have := congrArg (fun P => NSArch.tMat (tSplit hb₀ hb₁ v hv) * P * NSArch.tInv (tSplit hb₀ hb₁ v hv)) h
      simp only [← Matrix.mul_assoc, NSArch.tMat_mul_tInv ht0, Matrix.one_mul] at this
      simpa only [Matrix.mul_assoc, NSArch.tMat_mul_tInv ht0, Matrix.mul_one] using this
    have e' := e
    rw [eq_inv_smul_iff₀ hu, ← Matrix.smul_mul, ← Matrix.mul_smul] at e'
    have h := (hconj _ _ e').symm
    have hX : nrd (vecQ (qVec (mUnitR (splitPlaces hb₀ hb₁ v hv).1 (g : MM × (Adeles F)ˣ).1)) :
        ℍ[ℝ, embedding_of_isReal v.2 (a : F), embedding_of_isReal v.2 (b : F)]) =
          fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) := by
      rw [← qVec_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v _ h₁ rfl ht g, vecQ_qVec]
      exact nrd_psiR_nsXR hb₀ hb₁ hA' hB' hA0 hB0 v ht g
    exact NSArch.pos_of_sqMat_eq_smul hA hu hX (NSArch.nrd_sph p.1) (NSArch.nrd_sph p.2) h

theorem fAtR_of_snd_eq_one (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1) : fAtR v ((g : MM × (Adeles F)ˣ).2 : Adeles F) = 1 := by
  rw [hg1, Units.val_one, map_one]

theorem real_place_eq_of_comap_split (v : {v : InfinitePlace F // v.IsReal})
    (hv : 0 < embedding_of_isReal v.2 (d : F)) (w : {w : InfinitePlace K // w.IsReal})
    (hw : w.1.comap (algebraMap F K) = v.1) :
    w = (splitPlaces hb₀ hb₁ v hv).1 ∨ w = (splitPlaces hb₀ hb₁ v hv).2 := by
  rcases (splitPlaces_spec hb₀ hb₁ v hv).2.2.2 w.1 hw with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

include hb₀ hb₁ in
theorem not_complex_over_split (v : {v : InfinitePlace F // v.IsReal})
    (hv : 0 < embedding_of_isReal v.2 (d : F)) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) : False := by
  rcases (splitPlaces_spec hb₀ hb₁ v hv).2.2.2 w.1 hw with h | h
  · exact (not_isReal_iff_isComplex.2 w.2) (h ▸ (splitPlaces hb₀ hb₁ v hv).1.2)
  · exact (not_isReal_iff_isComplex.2 w.2) (h ▸ (splitPlaces hb₀ hb₁ v hv).2.2)

include hb₀ hb₁ in
theorem not_real_over_ns (v : {v : InfinitePlace F // v.IsReal})
    (hv : embedding_of_isReal v.2 (d : F) < 0) (w : {w : InfinitePlace K // w.IsReal})
    (hw : w.1.comap (algebraMap F K) = v.1) : False := by
  have h := (nsPlace_spec hb₀ hb₁ v hv).2.2.2 w.1 hw
  exact (not_isReal_iff_isComplex.2 (nsPlace hb₀ hb₁ v hv).2) (h ▸ w.2)

theorem complex_place_eq_of_comap_ns (v : {v : InfinitePlace F // v.IsReal})
    (hv : embedding_of_isReal v.2 (d : F) < 0) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) : w = nsPlace hb₀ hb₁ v hv :=
  Subtype.ext ((nsPlace_spec hb₀ hb₁ v hv).2.2.2 w.1 hw)

include hd0 in
/-- **Sufficient condition for $\varphi_v(g)\in U_v$** ($g_2 = 1$): the coordinates of $g_1$ at the places of $K$ over $v$
lie in the test sets. -/
theorem nsR_mem_URset_of_coords (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1)
    (hR : ∀ w : {w : InfinitePlace K // w.IsReal}, w.1.comap (algebraMap F K) = v.1 →
      qVec (mUnitR w (g : MM × (Adeles F)ˣ).1) ∈ posVecR)
    (hC : ∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v.1 →
      qVec (mUnitC w (g : MM × (Adeles F)ˣ).1) ∈ posVecC) :
    nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g ∈ URset (a := a) (b := b) hb₀ hb₁ v := by
  have hu := fAtR_of_snd_eq_one hb₀ hA0 hB0 v g hg1
  rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne hd0 v) with hv | hv
  · obtain ⟨hw, htre, ht, -⟩ := nsPlace_spec hb₀ hb₁ v hv
    obtain ⟨x, hx, hmat⟩ := mat_nsR_eq_phiNS hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v (nsPlace hb₀ hb₁ v hv) hw rfl htre
      ht (sNs_ne_zero hb₀ hb₁ v hv) g (by rw [hu]; exact one_pos)
    rw [hu, Real.sqrt_one, inv_one, Complex.ofReal_one, one_smul] at hx
    rw [URset, mem_ofPred_eq, TRset_ns hb₀ hb₁ v hv]
    refine ⟨_, ⟨x, ?_, rfl⟩, hmat.symm⟩
    show (x : Fin 4 → ℂ) ∈ posVecC
    rw [hx]; exact hC _ hw
  · obtain ⟨h₁, h₂, h₁₂, -⟩ := splitPlaces_spec hb₀ hb₁ v hv
    obtain ⟨x₁, x₂, hx₁, hx₂, hmat⟩ := mat_nsR_eq_phiSplit hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v _ _ h₁ h₂ rfl h₁₂
      (tSplit_ne_zero hb₀ hb₁ v hv) (tSplit_sq hb₀ hb₁ v hv) g (by rw [hu]; exact one_pos)
    rw [hu, Real.sqrt_one, inv_one, one_smul] at hx₁ hx₂
    rw [URset, mem_ofPred_eq, TRset_split hb₀ hb₁ v hv]
    refine ⟨_, ⟨(x₁, x₂), ⟨?_, ?_⟩, rfl⟩, hmat.symm⟩
    · show (x₁ : Fin 4 → ℝ) ∈ posVecR
      rw [hx₁]; exact hR _ h₁
    · show (x₂ : Fin 4 → ℝ) ∈ posVecR
      rw [hx₂]; exact hR _ h₂

include hd0 in
/-- **Necessary condition for $\varphi_v(g)\in U_v$** ($g_2 = 1$): up to one sign $r = \pm1$, the coordinates of $g_1$ at the
places of $K$ over $v$ lie in the test sets. -/
theorem exists_sign_of_nsR_mem_URset (v : {v : InfinitePlace F // v.IsReal}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1)
    (h : nsR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g ∈ URset (a := a) (b := b) hb₀ hb₁ v) :
    ∃ r : ℝ, r ^ 2 = 1 ∧
      (∀ w : {w : InfinitePlace K // w.IsReal}, w.1.comap (algebraMap F K) = v.1 →
        r • qVec (mUnitR w (g : MM × (Adeles F)ˣ).1) ∈ posVecR) ∧
      (∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v.1 →
        (r : ℂ) • qVec (mUnitC w (g : MM × (Adeles F)ˣ).1) ∈ posVecC) := by
  have hu := fAtR_of_snd_eq_one hb₀ hA0 hB0 v g hg1
  have hA := ne_zero_of_algebraMap_ne ha0 v
  rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne hd0 v) with hv | hv
  · obtain ⟨hw, htre, ht, -⟩ := nsPlace_spec hb₀ hb₁ v hv
    obtain ⟨x, hx, hmat⟩ := mat_nsR_eq_phiNS hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v (nsPlace hb₀ hb₁ v hv) hw rfl htre
      ht (sNs_ne_zero hb₀ hb₁ v hv) g (by rw [hu]; exact one_pos)
    rw [hu, Real.sqrt_one, inv_one, Complex.ofReal_one, one_smul] at hx
    rw [URset, mem_ofPred_eq, TRset_ns hb₀ hb₁ v hv] at h
    obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ := h
    have hxy := mat_injective _ (hmat.symm.trans hy'.symm)
    obtain ⟨r, hr, hry⟩ := NSArch.eq_smul_of_phiNS_eq _ _ _ hA hxy
    rcases NSArch.eq_one_or_neg_one_of_sq hr with h1 | h1
    · refine ⟨1, one_pow 2, fun w hw' => (not_real_over_ns hb₀ hb₁ v hv w hw').elim, fun w hw' => ?_⟩
      rw [complex_place_eq_of_comap_ns hb₀ hb₁ v hv w hw', ← hx, Complex.ofReal_one, one_smul]
      have : (y : Fin 4 → ℂ) = (x : Fin 4 → ℂ) := by rw [hry, h1, one_smul]
      rw [← this]; exact hy
    · refine ⟨-1, by norm_num, fun w hw' => (not_real_over_ns hb₀ hb₁ v hv w hw').elim, fun w hw' => ?_⟩
      rw [complex_place_eq_of_comap_ns hb₀ hb₁ v hv w hw', ← hx, Complex.ofReal_neg, Complex.ofReal_one, ← h1, ← hry]
      exact hy
  · obtain ⟨h₁, h₂, h₁₂, -⟩ := splitPlaces_spec hb₀ hb₁ v hv
    obtain ⟨x₁, x₂, hx₁, hx₂, hmat⟩ := mat_nsR_eq_phiSplit hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v _ _ h₁ h₂ rfl h₁₂
      (tSplit_ne_zero hb₀ hb₁ v hv) (tSplit_sq hb₀ hb₁ v hv) g (by rw [hu]; exact one_pos)
    rw [hu, Real.sqrt_one, inv_one, one_smul] at hx₁ hx₂
    rw [URset, mem_ofPred_eq, TRset_split hb₀ hb₁ v hv] at h
    obtain ⟨_, ⟨p, hp, rfl⟩, hp'⟩ := h
    have hxy := mat_injective _ (hmat.symm.trans hp'.symm)
    obtain ⟨r, hr, hr1, hr2⟩ := NSArch.eq_smul_of_phiSplit_eq _ _ hA hxy
    refine ⟨r, hr, fun w hw' => ?_, fun w hw' => (not_complex_over_split hb₀ hb₁ v hv w hw').elim⟩
    rcases real_place_eq_of_comap_split hb₀ hb₁ v hv w hw' with rfl | rfl
    · rw [← hx₁, ← hr1]; exact hp.1
    · rw [← hx₂, ← hr2]; exact hp.2

end GlobalReal

end QuadFormsKB.Tamagawa.Measure.Weil

end
