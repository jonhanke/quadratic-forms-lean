import QuadFormsKB.Tamagawa.Measure.Weil.BinaryNonCompact

/-!
# The measure comparison for the norm-one torus: reduction to fibre integrals
**Layer:** as in `BinaryNonCompact.lean`. $G = (E\otimes\mathbb A_F)^\times$, $\pi : G\to T(\mathbb A)$, $\Phi$ = `torAdeleEquiv`.

**Proves**
* `tamQuad_eq_lintegral_fibre`: for measurable $B\subseteq G$,
  $\mathrm{tamQuad}(B) = \int_{T(\mathbb A)}\mathrm{tamIdeles}_F\{c : g_qc\in B\}\,d\mu_T(q)$ (the fibration `fibMeas_muTor`);
* `fibreFn_box`: for a box $B = \{g : \Theta(g)_\infty\in A_\infty,\ \Theta(g)_f\in A_f\}$ ($\Theta$ = `quadUnitsBC`), the fibre
  function is the product $k_\infty(\Theta(g)_\infty)\,k_f(\Theta(g)_f)$ of an archimedean and a finite fibre function,
  and `tamQuad_box`: $\mathrm{tamQuad}(B) = \omega_{\infty,E}(A_\infty)\,\mu_{f,E}(A_f)$.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {d : F}
  {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E d)

/-- The fibre function $g\mapsto\mathrm{tamIdeles}_F\{c : g\,c\in B\}$. -/
def fibreFn (B : Set (QuadAdele F d)ˣ) (g : (QuadAdele F d)ˣ) : ℝ≥0∞ :=
  tamIdeles F {c | g * quadScalar d c ∈ B}

theorem kern_quadMk (B : Set (QuadAdele F d)ˣ) (hB : MeasurableSet B) (g : (QuadAdele F d)ˣ) :
    NormalFib.kern (quadMk d) (quadMk_surjective d) (muZQuad d) (quadMk d g) B = fibreFn B g := by
  rw [NormalFib.kern_apply_N, NormalFib.fibK_apply _ _ _ hB, muZQuad,
    Measure.map_apply (map_continuous (quadKerEquiv d)).measurable
      (hB.preimage (NormalFib.measurable_mul_val _ _))]
  rfl

/-- **The fibration identity on test sets.** -/
theorem tamQuad_eq_lintegral_fibre (B : Set (QuadAdele F d)ˣ) (hB : MeasurableSet B) :
    tamQuad hb0 hb1 B = ∫⁻ q, NormalFib.kern (quadMk d) (quadMk_surjective d) (muZQuad d) q B ∂(muTor hb0 hb1) := by
  rw [← fibMeas_muTor hb0 hb1, NormalFib.fibMeas_apply _ _ (measurable_quadMk d) _ _ hB]

/-- The box $\{g : \Theta(g)_\infty\in A_\infty,\ \Theta(g)_f\in A_f\}$. -/
def quadBox (A : Set (mixedSpace E)ˣ) (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) : Set (QuadAdele F d)ˣ :=
  quadUnitsBC hb0 hb1 ⁻¹' (idelesEquiv E ⁻¹' (A ×ˢ Af))

theorem measurableSet_quadBox {A : Set (mixedSpace E)ˣ} {Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ}
    (hA : MeasurableSet A) (hAf : MeasurableSet Af) : MeasurableSet (quadBox hb0 hb1 A Af) :=
  ((hA.prod hAf).preimage (idelesEquiv E).continuous.measurable).preimage (quadUnitsBC hb0 hb1).continuous.measurable

/-- **`tamQuad` of a box**: $\omega_{\infty,E}(A_\infty)\,\mu_{f,E}(A_f)$. -/
theorem tamQuad_box (A : Set (mixedSpace E)ˣ) (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) :
    tamQuad hb0 hb1 (quadBox hb0 hb1 A Af) = omegaInf E A * muFinUnits E Af := by
  have he : ((quadUnitsBC hb0 hb1).symm : (Adeles E)ˣ → (QuadAdele F d)ˣ) =
      (quadUnitsBC hb0 hb1).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [tamQuad, he, MeasurableEquiv.map_apply, ← he, quadBox, ← preimage_comp]
  have : (quadUnitsBC hb0 hb1 ∘ (quadUnitsBC hb0 hb1).symm) = id :=
    funext fun y => (quadUnitsBC hb0 hb1).apply_symm_apply y
  rw [this, preimage_id, tamIdeles_prod]

variable (F) in
/-- The archimedean fibre function $k_\infty(y) = \omega_{\infty,F}\{c : y\,\iota(c)\in A\}$. -/
def fibreInf (A : Set (mixedSpace E)ˣ) (y : (mixedSpace E)ˣ) : ℝ≥0∞ :=
  omegaInf F {c : (mixedSpace F)ˣ | y * Units.map (infRingHom F E).toMonoidHom c ∈ A}

variable (F) in
/-- The finite fibre function $k_f(y) = \mu_{f,F}\{c : y\,\iota(c)\in A_f\}$. -/
def fibreFin (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (y : (FiniteAdeleRing (𝓞 E) E)ˣ) : ℝ≥0∞ :=
  muFinUnits F {c : (FiniteAdeleRing (𝓞 F) F)ˣ | y * Units.map (finMap F E).toMonoidHom c ∈ Af}

theorem idelesEquiv_quadUnitsBC_mul_quadScalar (g : (QuadAdele F d)ˣ) (c : (Adeles F)ˣ) :
    idelesEquiv E (quadUnitsBC hb0 hb1 (g * quadScalar d c)) =
      ((idelesEquiv E (quadUnitsBC hb0 hb1 g)).1 * Units.map (infRingHom F E).toMonoidHom (idelesEquiv F c).1,
       (idelesEquiv E (quadUnitsBC hb0 hb1 g)).2 * Units.map (finMap F E).toMonoidHom (idelesEquiv F c).2) := by
  rw [map_mul, map_mul]
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · change ((quadUnitsBC hb0 hb1 g : (Adeles E)ˣ) : Adeles E).1 *
        ((quadUnitsBC hb0 hb1 (quadScalar d c) : (Adeles E)ˣ) : Adeles E).1 = _
    rw [quadUnitsBC_quadScalar, adeleMap_fst]; rfl
  · change ((quadUnitsBC hb0 hb1 g : (Adeles E)ˣ) : Adeles E).2 *
        ((quadUnitsBC hb0 hb1 (quadScalar d c) : (Adeles E)ˣ) : Adeles E).2 = _
    rw [quadUnitsBC_quadScalar, adeleMap_snd]; rfl

/-- **The fibre function of a box is a product.** -/
theorem fibreFn_box (A : Set (mixedSpace E)ˣ) (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (g : (QuadAdele F d)ˣ) :
    fibreFn (quadBox hb0 hb1 A Af) g =
      fibreInf F A (idelesEquiv E (quadUnitsBC hb0 hb1 g)).1 * fibreFin F Af (idelesEquiv E (quadUnitsBC hb0 hb1 g)).2 := by
  rw [fibreFn, fibreInf, fibreFin, ← tamIdeles_prod]
  congr 1
  ext c
  simp only [quadBox, mem_setOf_eq, mem_preimage, mem_prod, idelesEquiv_quadUnitsBC_mul_quadScalar]

/-! ### The archimedean and finite parts of the base change -/

/-- $E\otimes F_\infty\to E_\infty$, $x + y\omega\mapsto\iota(x) + \delta\,\iota(y)$. -/
def quadInfBC : QuadInf F d →+* mixedSpace E where
  toFun z := infRingHom F E z.re + mixedEmbedding E (b 1) * infRingHom F E z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' z w := by
    have hδ : mixedEmbedding E (b 1) * mixedEmbedding E (b 1) = infRingHom F E (mixedEmbedding F d) := by
      rw [← map_mul, hb1, ← infMap_mixedEmbedding]; rfl
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (-(infRingHom F E z.im * infRingHom F E w.im)) * hδ

/-- $E\otimes\mathbb A_{F,f}\to\mathbb A_{E,f}$, $x + y\omega\mapsto\iota(x) + \delta\,\iota(y)$. -/
def quadFinBC : QuadFin F d →+* FiniteAdeleRing (𝓞 E) E where
  toFun z := finMap F E z.re + algebraMap E (FiniteAdeleRing (𝓞 E) E) (b 1) * finMap F E z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' z w := by
    have hδ : algebraMap E (FiniteAdeleRing (𝓞 E) E) (b 1) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (b 1) =
        finMap F E (algebraMap F (FiniteAdeleRing (𝓞 F) F) d) := by
      rw [← map_mul, hb1, finMap_algebraMap]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (-(finMap F E z.im * finMap F E w.im)) * hδ

theorem idelesEquiv_quadUnitsBC (g : (QuadAdele F d)ˣ) :
    idelesEquiv E (quadUnitsBC hb0 hb1 g) =
      (Units.map (quadInfBC hb1).toMonoidHom (quadUnitsSplit d g).1,
       Units.map (quadFinBC hb1).toMonoidHom (quadUnitsSplit d g).2) := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · change (quadBaseChange hb0 hb1 (g : QuadAdele F d)).1 = _
    rw [quadBaseChange_apply]; rfl
  · change (quadBaseChange hb0 hb1 (g : QuadAdele F d)).2 = _
    rw [quadBaseChange_apply]; rfl

/-! ### The fibre function on $SO(V)(\mathbb A)$ -/

section SO

variable {D : 𝓞 F} {E : Type} [Field E] [NumberField E] [Algebra F E] {b : Module.Basis (Fin 2) F E}
  (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D))

theorem fibreInf_mul (A : Set (mixedSpace E)ˣ) (y : (mixedSpace E)ˣ) (c : (mixedSpace F)ˣ) :
    fibreInf F A (y * Units.map (infRingHom F E).toMonoidHom c) = fibreInf F A y := by
  unfold fibreInf
  have : {c' : (mixedSpace F)ˣ | y * Units.map (infRingHom F E).toMonoidHom c *
      Units.map (infRingHom F E).toMonoidHom c' ∈ A} =
      (fun c' => c * c') ⁻¹' {c' | y * Units.map (infRingHom F E).toMonoidHom c' ∈ A} := by
    ext c'; simp [mul_assoc]
  rw [this, measure_preimage_mul]

theorem fibreFin_mul (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (y : (FiniteAdeleRing (𝓞 E) E)ˣ)
    (c : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    fibreFin F Af (y * Units.map (finMap F E).toMonoidHom c) = fibreFin F Af y := by
  unfold fibreFin
  have : {c' : (FiniteAdeleRing (𝓞 F) F)ˣ | y * Units.map (finMap F E).toMonoidHom c *
      Units.map (finMap F E).toMonoidHom c' ∈ Af} =
      (fun c' => c * c') ⁻¹' {c' | y * Units.map (finMap F E).toMonoidHom c' ∈ Af} := by
    ext c'; simp [mul_assoc]
  rw [this, measure_preimage_mul]

theorem quadInfBC_infScalarQ (c : (mixedSpace F)ˣ) :
    Units.map (quadInfBC hb1).toMonoidHom (infScalarQ (dD D) c) = Units.map (infRingHom F E).toMonoidHom c := by
  apply Units.ext
  change infRingHom F E (c : mixedSpace F) + mixedEmbedding E (b 1) * infRingHom F E 0 = _
  simp

theorem quadFinBC_finScalarQ (c : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Units.map (quadFinBC hb1).toMonoidHom (finScalarQ (dD D) c) = Units.map (finMap F E).toMonoidHom c := by
  apply Units.ext
  change finMap F E (c : FiniteAdeleRing (𝓞 F) F) + algebraMap E (FiniteAdeleRing (𝓞 E) E) (b 1) * finMap F E 0 = _
  simp

theorem fibreInf_eq_of_torInf_eq (A : Set (mixedSpace E)ˣ) {g g' : (QuadInf F (dD D))ˣ}
    (h : torInf D g = torInf D g') :
    fibreInf F A (Units.map (quadInfBC hb1).toMonoidHom g) =
      fibreInf F A (Units.map (quadInfBC hb1).toMonoidHom g') := by
  have hk : g⁻¹ * g' ∈ (torInf D).ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [ker_torInf] at hk
  obtain ⟨c, hc⟩ := hk
  have : g' = g * infScalarQ (dD D) c := by rw [hc, mul_inv_cancel_left]
  rw [this, map_mul, quadInfBC_infScalarQ, fibreInf_mul]

theorem fibreFin_eq_of_torFin_eq (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) {g g' : (QuadFin F (dD D))ˣ}
    (h : torFin D g = torFin D g') :
    fibreFin F Af (Units.map (quadFinBC hb1).toMonoidHom g) =
      fibreFin F Af (Units.map (quadFinBC hb1).toMonoidHom g') := by
  have hk : g⁻¹ * g' ∈ (torFin D).ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [ker_torFin] at hk
  obtain ⟨c, hc⟩ := hk
  have : g' = g * finScalarQ (dD D) c := by rw [hc, mul_inv_cancel_left]
  rw [this, map_mul, quadFinBC_finScalarQ, fibreFin_mul]

variable (E) in
/-- **The archimedean fibre function on $G_\infty$**: $K_\infty(x) = k_\infty(\Theta(z))$ for any $z$ with $\mathrm{tor}(z) = x$. -/
def fibInfSO (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) (A : Set (mixedSpace E)ˣ)
    (x : GInfSO (diagForm1 D)) : ℝ≥0∞ :=
  fibreInf F A (Units.map (quadInfBC hb1).toMonoidHom (Function.surjInv (torInf_surjective D hD) x))

variable (E) in
/-- **The finite fibre function on $SO(V)(\mathbb A_f)$.** -/
def fibFinSO (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ)
    (x : SOAf (diagForm1 D)) : ℝ≥0∞ :=
  fibreFin F Af (Units.map (quadFinBC hb1).toMonoidHom (Function.surjInv (torFin_surjective D hD) x))

theorem fibInfSO_torInf (hD : D ≠ 0) (A : Set (mixedSpace E)ˣ) (g : (QuadInf F (dD D))ˣ) :
    fibInfSO E hb1 hD A (torInf D g) = fibreInf F A (Units.map (quadInfBC hb1).toMonoidHom g) :=
  fibreInf_eq_of_torInf_eq hb1 A (Function.surjInv_eq _ _)

theorem fibFinSO_torFin (hD : D ≠ 0) (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (g : (QuadFin F (dD D))ˣ) :
    fibFinSO E hb1 hD Af (torFin D g) = fibreFin F Af (Units.map (quadFinBC hb1).toMonoidHom g) :=
  fibreFin_eq_of_torFin_eq hb1 Af (Function.surjInv_eq _ _)

/-- **The fibration identity for a box, on $SO(V)(\mathbb A)$**:
$\omega_{\infty,E}(A_\infty)\,\mu_{f,E}(A_f) = \int K_\infty(x_\infty)\,K_f(x_f)\,d(\Phi_*\mu_T)(x)$. -/
theorem tamQuad_box_eq_lintegral (hD : D ≠ 0) {A : Set (mixedSpace E)ˣ} {Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ}
    (hA : MeasurableSet A) (hAf : MeasurableSet Af) :
    omegaInf E A * muFinUnits E Af =
      ∫⁻ x, fibInfSO E hb1 hD A x.1 * fibFinSO E hb1 hD Af x.2 ∂(muTorSO hb0 hb1 hD) := by
  have he : (torAdeleEquiv D hD : TorA D → SOAdele (diagForm1 D)) =
      (torAdeleEquiv D hD).toHomeomorph.toMeasurableEquiv := rfl
  rw [← tamQuad_box hb0 hb1, tamQuad_eq_lintegral_fibre hb0 hb1 _ (measurableSet_quadBox hb0 hb1 hA hAf), muTorSO,
    he, lintegral_map_equiv, ← he]
  refine lintegral_congr fun q => ?_
  obtain ⟨g, rfl⟩ := quadMk_surjective (dD D) q
  rw [kern_quadMk _ (measurableSet_quadBox hb0 hb1 hA hAf), fibreFn_box, idelesEquiv_quadUnitsBC]
  change _ = fibInfSO E hb1 hD A (torAdeleEquiv D hD (torMk D g)).1 *
    fibFinSO E hb1 hD Af (torAdeleEquiv D hD (torMk D g)).2
  rw [torAdeleEquiv_mk, torAdele_apply, fibInfSO_torInf, fibFinSO_torFin]

end SO

end QuadFormsKB.Tamagawa.Measure.Weil

