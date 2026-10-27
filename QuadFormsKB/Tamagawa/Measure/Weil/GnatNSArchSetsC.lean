/-
# The archimedean test set at the complex places of $F$

**Layer:** $F$ any number field, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$; $Q_0 = \langle1,-ad,-bd,abd\rangle$ (`qNS`);
$v$ a complex place of $F$, $w_1\neq w_2$ the two places of $K$ over $v$.

* **`UCset v`**: the image $\varphi_v(Y_v)$, $Y_v = $ `posC`$^2$, under `phiSplitC` (with $t = $ `twt` $w_1$), as a subset of
  $SO(Q_0^{\tau_v})(\mathbb C)$; measurable, with $\mathrm{Leray}(U_v) = (1024\|a_v\|^6\|b_v\|^6\|d_v\|^{15})^{-1}\sigma(Y)^2$.
* Membership of $\varphi_v(g)$ ($g_2=1$) in terms of the coordinates of $g_1$ at $w_1, w_2$ (up to one sign).

Source: Weil 1982, §2.3, Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSArchSets
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSBridgeC

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex SphereLeray SphereLerayC

theorem conjV_mem_posVecC_iff (x : Fin 4 → ℂ) : conjV x ∈ posVecC ↔ x ∈ posVecC := by
  simp only [posVecC, mem_setOf_eq, norm_conjV]
  simp [conjV]

open Classical in
theorem twC_mem_posVecC_iff {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Fin 4 → ℂ) : twC F w x ∈ posVecC ↔ x ∈ posVecC := by
  unfold twC
  split_ifs
  · rfl
  · exact conjV_mem_posVecC_iff x

open Classical in
theorem twC_smul_real {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (w : {w : InfinitePlace K // w.IsComplex}) (r : ℝ) (x : Fin 4 → ℂ) : twC F w ((r : ℂ) • x) = (r : ℂ) • twC F w x := by
  unfold twC
  split_ifs
  · rfl
  · rw [conjV_smul, Complex.conj_ofReal]

section ComplexPlaces

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

include hb₀ hb₁ in
theorem exists_cx_places (v : {v : InfinitePlace F // v.IsComplex}) :
    ∃ p : {w : InfinitePlace K // w.IsComplex} × {w : InfinitePlace K // w.IsComplex}, p.1 ≠ p.2 ∧
      p.1.1.comap (algebraMap F K) = v.1 ∧ p.2.1.comap (algebraMap F K) = v.1 ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = p.1.1 ∨ w = p.2.1) := by
  obtain ⟨w₁, w₂, hne, h₁, h₂, hall⟩ := exists_two_complex_places bK hb₀ hb₁ v
  exact ⟨(w₁, w₂), hne, h₁, h₂, hall⟩

/-- The two places of $K$ over a complex place $v$ of $F$ (a choice). -/
def cxPlaces (v : {v : InfinitePlace F // v.IsComplex}) :
    {w : InfinitePlace K // w.IsComplex} × {w : InfinitePlace K // w.IsComplex} :=
  Classical.choose (exists_cx_places hb₀ hb₁ v)

theorem cxPlaces_spec (v : {v : InfinitePlace F // v.IsComplex}) :
    (cxPlaces hb₀ hb₁ v).1 ≠ (cxPlaces hb₀ hb₁ v).2 ∧
      (cxPlaces hb₀ hb₁ v).1.1.comap (algebraMap F K) = v.1 ∧ (cxPlaces hb₀ hb₁ v).2.1.comap (algebraMap F K) = v.1 ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 →
        w = (cxPlaces hb₀ hb₁ v).1.1 ∨ w = (cxPlaces hb₀ hb₁ v).2.1) :=
  Classical.choose_spec (exists_cx_places hb₀ hb₁ v)

theorem cxPlaces_sq (v : {v : InfinitePlace F // v.IsComplex}) :
    twt bK (cxPlaces hb₀ hb₁ v).1 ^ 2 = v.1.embedding (d : F) :=
  twt_sq hb₁ v _ (cxPlaces_spec hb₀ hb₁ v).2.1

theorem cxPlaces_ne_zero (hd0 : (d : F) ≠ 0) (v : {v : InfinitePlace F // v.IsComplex}) :
    twt bK (cxPlaces hb₀ hb₁ v).1 ≠ 0 :=
  twt_ne_zero hb₁ hd0 v _ (cxPlaces_spec hb₀ hb₁ v).2.1

open Classical in
/-- **The matrix set $\varphi_v(Y_v)$** at a complex place $v$ of $F$. -/
def TCset (v : {v : InfinitePlace F // v.IsComplex}) : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  if hd0 : (d : F) ≠ 0 then
    ArchSOC.mat _ '' (NSArch.phiSplitC (A := v.1.embedding (a : F)) (B := v.1.embedding (b : F))
      (cxPlaces_ne_zero hb₀ hb₁ hd0 v) (cxPlaces_sq hb₀ hb₁ v) '' (NSArch.posC _ _ ×ˢ NSArch.posC _ _))
  else ∅

/-- **The local test set $U_v\subseteq SO(Q_0^{\tau_v})(\mathbb C)$.** -/
def UCset (v : {v : InfinitePlace F // v.IsComplex}) : Set (ArchSOC (QCx (qNS a b d) v)) :=
  {g | ArchSOC.mat _ g ∈ TCset (a := a) (b := b) hb₀ hb₁ v}

theorem TCset_eq (hd0 : (d : F) ≠ 0) (v : {v : InfinitePlace F // v.IsComplex}) :
    TCset (a := a) (b := b) hb₀ hb₁ v = ArchSOC.mat _ '' (NSArch.phiSplitC (A := v.1.embedding (a : F))
      (B := v.1.embedding (b : F)) (cxPlaces_ne_zero hb₀ hb₁ hd0 v) (cxPlaces_sq hb₀ hb₁ v) ''
        (NSArch.posC _ _ ×ˢ NSArch.posC _ _)) := by
  rw [TCset, dif_pos hd0]

theorem measurableSet_UCset (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : {v : InfinitePlace F // v.IsComplex}) :
    MeasurableSet (UCset (a := a) (b := b) hb₀ hb₁ v) := by
  have hA : v.1.embedding (a : F) ≠ 0 := (map_ne_zero _).2 ha0
  refine MeasurableSet.preimage ?_ (ArchSOC.continuous_mat _).measurable
  rw [TCset_eq hb₀ hb₁ hd0 v, Set.image_image]
  exact (NSArch.measurableSet_posC.prod NSArch.measurableSet_posC).image_of_continuousOn_injOn
    ((ArchSOC.continuous_mat _).comp (NSArch.continuous_phiSplitC _ _)).continuousOn
    ((matC_injective _).comp_injOn (NSArch.injOn_phiSplitC_posC _ _ hA))

theorem gramDetC_diag {n : ℕ} (c : Fin n → ℂ) : gramDetC (QuadForm.diag c) = ∏ i, c i := by
  have h : gramC (QuadForm.diag c) = Matrix.diagonal c := by
    unfold gramC QuadForm.hessian QuadForm.diag
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal]; ring
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  rw [gramDetC, h, Matrix.det_diagonal]

theorem gramDetC_pureForm_ne {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) : gramDetC (pureForm A B) ≠ 0 := by
  rw [pureForm, gramDetC_diag, Fin.prod_univ_three]
  simp [hA, hB]

theorem gramDetC_pureFormDC_ne {A B d : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    gramDetC (NSArch.pureFormDC A B d) ≠ 0 := by
  rw [NSArch.pureFormDC, gramDetC_diag, Fin.prod_univ_three]
  simp [hA, hB, hd]

theorem gramDetC_nsFormC_ne {A B d : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    gramDetC (NSArch.nsFormC A B d) ≠ 0 := by
  rw [NSArch.nsFormC_eq_diag, gramDetC_diag, Fin.prod_univ_four]
  simp [hA, hB, hd]

theorem norm_pow_six_mul_twelve {t d : ℂ} (ht : t ^ 2 = d) : ‖t‖ ^ 6 * ‖d‖ ^ 12 = ‖d‖ ^ (15 : ℝ) := by
  have h2 : ‖t‖ ^ 2 = ‖d‖ := by rw [← norm_pow, ht]
  rw [show ‖t‖ ^ 6 = (‖t‖ ^ 2) ^ 3 by ring, h2, ← pow_add, show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- **The Leray measure of $U_v$ at a complex place**: $(1024\|a_v\|^6\|b_v\|^6\|d_v\|^{15})^{-1}\sigma(Y)^2$. -/
theorem leray_UCset (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (v : {v : InfinitePlace F // v.IsComplex}) :
    lerayMeasureC (QCx (qNS a b d) v) (gramDetC_QCx_ne_zero _ hQ v) (UCset (a := a) (b := b) hb₀ hb₁ v) =
      ENNReal.ofReal (1 / (1024 * ‖v.1.embedding (a : F)‖ ^ 6 * ‖v.1.embedding (b : F)‖ ^ 6 *
        ‖v.1.embedding (d : F)‖ ^ (15 : ℝ))) *
        (sigC (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))) 1 (NSArch.posC _ _)) ^ 2 := by
  have hA : v.1.embedding (a : F) ≠ 0 := (map_ne_zero _).2 ha0
  have hB : v.1.embedding (b : F) ≠ 0 := (map_ne_zero _).2 hb0
  have hD : v.1.embedding (d : F) ≠ 0 := (map_ne_zero _).2 hd0
  rw [UCset, TCset_eq hb₀ hb₁ hd0 v,
    lerayMeasureC_congr_mat (QCx_qNS a b d v) _ (gramDetC_nsFormC_ne hA hB hD), setOf_matC_mem_image,
    NSArch.lerayC_phiSplitC_image _ _ hA hB hD (gramDetC_pureForm_ne hA hB) (gramDetC_pureFormDC_ne hA hB hD) _
      (NSArch.measurableSet_posC.prod NSArch.measurableSet_posC) (NSArch.injOn_phiSplitC_posC _ _ hA),
    Measure.prod_prod, sq]
  congr 3
  rw [mul_assoc (1024 * _ * _), norm_pow_six_mul_twelve (cxPlaces_sq hb₀ hb₁ v)]

end ComplexPlaces

section GlobalComplex

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F))
  (hA0 : A' ≠ 0) (hB0 : B' ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

local notation "MM" => (QuatAdele (F := K) A' B')ˣ

theorem fAtC_of_snd_eq_one (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1) : fAtC v ((g : MM × (Adeles F)ˣ).2 : Adeles F) = 1 := by
  rw [hg1, Units.val_one, map_one]

theorem not_real_over_complex (v : {v : InfinitePlace F // v.IsComplex}) (w : {w : InfinitePlace K // w.IsReal})
    (hw : w.1.comap (algebraMap F K) = v.1) : False :=
  (not_isReal_iff_isComplex.2 v.2) (hw ▸ w.2.comap _)

theorem complex_place_eq_of_comap_cx (v : {v : InfinitePlace F // v.IsComplex})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    w = (cxPlaces hb₀ hb₁ v).1 ∨ w = (cxPlaces hb₀ hb₁ v).2 := by
  rcases (cxPlaces_spec hb₀ hb₁ v).2.2.2 w.1 hw with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

include hd0 in
/-- **Sufficient condition for $\varphi_v(g)\in U_v$** at a complex place ($g_2 = 1$). -/
theorem nsC_mem_UCset_of_coords (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1)
    (hC : ∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v.1 →
      qVec (mUnitC w (g : MM × (Adeles F)ˣ).1) ∈ posVecC) :
    nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g ∈ UCset (a := a) (b := b) hb₀ hb₁ v := by
  have hu := fAtC_of_snd_eq_one hb₀ hA0 hB0 v g hg1
  obtain ⟨hne, h₁, h₂, -⟩ := cxPlaces_spec hb₀ hb₁ v
  obtain ⟨x₁, x₂, hx₁, hx₂, hmat⟩ := mat_nsC_eq_phiSplitC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v _ _ h₁ h₂ hne rfl
    (cxPlaces_ne_zero hb₀ hb₁ hd0 v) (cxPlaces_sq hb₀ hb₁ v) g (c := 1) (by rw [hu, one_pow]) one_ne_zero
  rw [inv_one, one_smul] at hx₁ hx₂
  rw [UCset, mem_ofPred_eq, TCset_eq hb₀ hb₁ hd0 v]
  refine ⟨_, ⟨(x₁, x₂), ⟨?_, ?_⟩, rfl⟩, hmat.symm⟩
  · show (x₁ : Fin 4 → ℂ) ∈ posVecC
    rw [hx₁, twC_mem_posVecC_iff]; exact hC _ h₁
  · show (x₂ : Fin 4 → ℂ) ∈ posVecC
    rw [hx₂, twC_mem_posVecC_iff]; exact hC _ h₂

include hd0 in
/-- **Necessary condition for $\varphi_v(g)\in U_v$** at a complex place ($g_2 = 1$): up to one sign. -/
theorem exists_sign_of_nsC_mem_UCset (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (hg1 : (g : MM × (Adeles F)ˣ).2 = 1)
    (h : nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g ∈ UCset (a := a) (b := b) hb₀ hb₁ v) :
    ∃ r : ℝ, r ^ 2 = 1 ∧ ∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v.1 →
      (r : ℂ) • qVec (mUnitC w (g : MM × (Adeles F)ˣ).1) ∈ posVecC := by
  have hu := fAtC_of_snd_eq_one hb₀ hA0 hB0 v g hg1
  have hA : v.1.embedding (a : F) ≠ 0 := (map_ne_zero _).2 ha0
  obtain ⟨hne, h₁, h₂, -⟩ := cxPlaces_spec hb₀ hb₁ v
  obtain ⟨x₁, x₂, hx₁, hx₂, hmat⟩ := mat_nsC_eq_phiSplitC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v _ _ h₁ h₂ hne rfl
    (cxPlaces_ne_zero hb₀ hb₁ hd0 v) (cxPlaces_sq hb₀ hb₁ v) g (c := 1) (by rw [hu, one_pow]) one_ne_zero
  rw [inv_one, one_smul] at hx₁ hx₂
  rw [UCset, mem_ofPred_eq, TCset_eq hb₀ hb₁ hd0 v] at h
  obtain ⟨_, ⟨p, hp, rfl⟩, hp'⟩ := h
  have hxy := matC_injective _ (hmat.symm.trans hp'.symm)
  obtain ⟨r, hr, hr1, hr2⟩ := NSArch.eq_smul_of_phiSplitC_eq _ _ hA hxy
  have key : ∃ r' : ℝ, r' ^ 2 = 1 ∧ (r' : ℂ) = r := by
    rcases NSArch.eq_one_or_neg_one_of_sq hr with h1 | h1
    · exact ⟨1, one_pow 2, by rw [h1, Complex.ofReal_one]⟩
    · exact ⟨-1, by norm_num, by rw [h1, Complex.ofReal_neg, Complex.ofReal_one]⟩
  obtain ⟨r', hr', hrr⟩ := key
  refine ⟨r', hr', fun w hw' => ?_⟩
  rcases complex_place_eq_of_comap_cx hb₀ hb₁ v w hw' with rfl | rfl
  · rw [← twC_mem_posVecC_iff (F := F) (cxPlaces hb₀ hb₁ v).1, twC_smul_real, ← hx₁, hrr, ← hr1]; exact hp.1
  · rw [← twC_mem_posVecC_iff (F := F) (cxPlaces hb₀ hb₁ v).2, twC_smul_real, ← hx₂, hrr, ← hr2]; exact hp.2

end GlobalComplex

end QuadFormsKB.Tamagawa.Measure.Weil

end
