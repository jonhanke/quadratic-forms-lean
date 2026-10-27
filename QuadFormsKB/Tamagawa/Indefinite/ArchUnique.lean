/-
# The measures on the stabilizers are canonical (Siegel's formula for indefinite forms)

**Layer:** abstract measure theory, plus the right invariance of the concrete stabilizer measures.

An archimedean fibration (`ArchFibration`) fixes, for each point `y` of the quadric, a measure $\mu_{H_y}$ on the
stabilizer $H_y$ with $\mu_A = c\cdot\mathrm{coord}_*(\sigma\otimes\mu_{H_y})$. The coordinates are a choice (a section of
the orbit map); the measure is not: **if the $\mu_{H_y}$ are right invariant ($H_y$ unimodular), they are determined by
$\mu_A$, $\sigma$ and $c$** (`ArchFibration.μH_eq`). Hence Siegel's measure of representations
$\rho = \sum\operatorname{vol}(\Gamma_y\backslash H_y, \mu_{H_y})$ (`repMeasureOf`) does not depend on the coordinates
(`repMeasureOf_eq`). This is Weil's statement that the measure on $H$ is the quotient of the measures on $G$ and $G/H$
(Weil 1982, Lemma 2.4.1 / Thm 2.4.3).

**Proves** (unconditional, standard axioms only)
* `map_prod_skew`: $(x, h)\mapsto(x, hu(x))$ preserves $\sigma\otimes\nu$ for right-invariant $\nu$;
* `orbitCoord_exists_skew`: two orbit coordinates differ by such a skew right translation;
* `ArchFibration.μH_eq`, `repMeasureOf_eq`: uniqueness of the stabilizer measures, and of $\rho$;
* `isMulRightInvariant_map_of_surjective`, `SplitFrame.isMulRightInvariant_stabMeasure`,
  `isMulRightInvariant_realStabMeasure`: the real-place stabilizer measures are right invariant;
  `ArchFibration.isMulRightInvariant_pi`, `ArchFibration.isMulRightInvariant_prod`: and so are those of products.
-/
import QuadFormsKB.Tamagawa.Indefinite.ArchConj
import QuadFormsKB.Tamagawa.Indefinite.ArchProduct

open MeasureTheory Measure MulAction Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Skew right translations -/

section Skew

variable {T : Type*} [MeasurableSpace T] {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]

/-- **Skew right translations preserve $\sigma\otimes\nu$** when $\nu$ is right invariant:
$(x, h)\mapsto(x, h\,u(x))$. -/
theorem map_prod_skew (σ : Measure T) [SFinite σ] (ν : Measure H) [SFinite ν] [ν.IsMulRightInvariant]
    {u : T → H} (hu : Measurable u) :
    (σ.prod ν).map (fun p => (p.1, p.2 * u p.1)) = σ.prod ν := by
  have hm : Measurable fun p : T × H => (p.1, p.2 * u p.1) :=
    measurable_fst.prodMk (measurable_snd.mul (hu.comp measurable_fst))
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm, lintegral_prod (fun a : T × H => f (a.1, a.2 * u a.1)) (hf.comp hm).aemeasurable,
    lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun x => ?_
  exact lintegral_mul_right_eq_self (fun h => f (x, h)) (u x)

end Skew

/-! ### Uniqueness of the stabilizer measures -/

section Unique

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul₂ A] [MeasurableInv A]
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T]

/-- **Two orbit coordinates differ by a skew right translation**: $\mathrm{coord}(x, h) =
\mathrm{coord}'(x, h\,u(x))$ with $u(x) = \mathrm{coord}(x, 1)\,\mathrm{coord}'(x, 1)^{-1}\in H_y$. -/
theorem orbitCoord_exists_skew {τ : T → Y} {y : Y} (C C' : OrbitCoord (stabilizer A y).subtype τ y) :
    ∃ u : T → stabilizer A y, Measurable u ∧ ∀ x h, C.coord (x, h) = C'.coord (x, h * u x) := by
  have hmem : ∀ x, C.coord (x, 1) * (C'.coord (x, 1))⁻¹ ∈ stabilizer A y := fun x => by
    rw [mem_stabilizer_iff, mul_smul, C'.orbit, ← C.orbit x 1, smul_inv_smul]
  refine ⟨fun x => ⟨_, hmem x⟩, ?_, fun x h => ?_⟩
  · have h1 : Measurable fun x : T => C.coord (x, 1) := C.coord.measurable.comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable fun x : T => C'.coord (x, 1) :=
      C'.coord.measurable.comp (measurable_id.prodMk measurable_const)
    exact (h1.mul h2.inv).subtype_mk
  · rw [C'.coord_eq, C.coord_eq]
    simp [mul_assoc]

variable [MeasurableMul A] {μA : Measure A} {P : Set Y} {σ : Measure T} {τ : T → Y} {c : ℝ≥0∞}

/-- **The stabilizer measures of an archimedean fibration are canonical**: if two fibrations of the same $\mu_A$
over the same $(P, \sigma, \tau, c)$ are given, $0 < c < \infty$, $\sigma\ne0$ is σ-finite, and the stabilizer measure
of the first at $y\in P$ is right invariant, then the two stabilizer measures at $y$ agree (so the second is right
invariant too). -/
theorem ArchFibration.μH_eq [SigmaFinite σ] (𝔉 𝔉' : ArchFibration μA P σ τ c) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hσ : σ ≠ 0) {y : Y} (hy : y ∈ P) (h𝔉 : (𝔉.μH y).IsMulRightInvariant) : 𝔉.μH y = 𝔉'.μH y := by
  haveI := 𝔉.sigmaFinite y
  haveI := 𝔉'.sigmaFinite y
  haveI := measurableMul_subgroup (stabilizer A y)
  haveI : MeasurableMul₂ (stabilizer A y) :=
    ⟨(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd) |>.subtype_mk⟩
  set C := 𝔉.coord y hy
  set C' := 𝔉'.coord y hy
  obtain ⟨u, hu, hCu⟩ := orbitCoord_exists_skew C C'
  have hskew : (C.coord : T × stabilizer A y → A) = C'.coord ∘ fun p : T × stabilizer A y => (p.1, p.2 * u p.1) :=
    funext fun p => hCu p.1 p.2
  have hm : Measurable fun p : T × stabilizer A y => (p.1, p.2 * u p.1) :=
    measurable_fst.prodMk (measurable_snd.mul (hu.comp measurable_fst))
  have hmap : (σ.prod (𝔉.μH y)).map C.coord = (σ.prod (𝔉.μH y)).map C'.coord := by
    rw [hskew, ← Measure.map_map C'.coord.measurable hm, map_prod_skew σ (𝔉.μH y) hu]
  have h1 : c • (σ.prod (𝔉.μH y)).map C'.coord = c • (σ.prod (𝔉'.μH y)).map C'.coord := by
    rw [← hmap, ← 𝔉.fib y hy, ← 𝔉'.fib y hy]
  have h2 : (σ.prod (𝔉.μH y)).map C'.coord = (σ.prod (𝔉'.μH y)).map C'.coord := by
    ext s hs
    have := congrArg (fun ν : Measure A => ν s) h1
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj hc0 hct).mp this
  have h3 : σ.prod (𝔉.μH y) = σ.prod (𝔉'.μH y) := by
    have := congrArg (fun ν => ν.map C'.coord.symm) h2
    simpa only [MeasurableEquiv.map_symm_map] using this
  -- a set of finite positive σ-measure
  obtain ⟨k, hk⟩ : ∃ k, σ (spanningSets σ k) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hσ
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets σ]
    exact measure_iUnion_null hall
  have hkt := measure_spanningSets_lt_top σ k
  ext E hE
  have := congrArg (fun ν : Measure (T × stabilizer A y) => ν (spanningSets σ k ×ˢ E)) h3
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hk hkt.ne).mp this

/-- **Siegel's measure of representations does not depend on the coordinates** of the fibration (given right
invariance of the stabilizer measures of one of them). -/
theorem repMeasureOf_eq [SigmaFinite σ] (𝔉 𝔉' : ArchFibration μA P σ τ c) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hσ : σ ≠ 0) (Γ' : Subgroup A) (S : SubMulAction Γ' Y) (hSP : ∀ y ∈ S, y ∈ P)
    (h𝔉 : ∀ y ∈ P, (𝔉.μH y).IsMulRightInvariant) :
    repMeasureOf Γ' S 𝔉.μH = repMeasureOf Γ' S 𝔉'.μH := by
  unfold repMeasureOf
  refine tsum_congr fun q => ?_
  have hy := hSP _ (q.out : S).2
  rw [𝔉.μH_eq 𝔉' hc0 hct hσ hy (h𝔉 _ hy)]

end Unique

/-! ### Right invariance at a real place -/

section Real

open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure

/-- The image of a right-invariant measure under a surjective measurable homomorphism is right invariant. -/
theorem isMulRightInvariant_map_of_surjective {G H : Type*} [Group G] [Group H] [MeasurableSpace G]
    [MeasurableSpace H] [MeasurableMul G] [MeasurableMul H] (μ : Measure G) [μ.IsMulRightInvariant]
    (f : G →* H) (hf : Measurable f) (hsurj : Function.Surjective f) : (μ.map f).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj h
  rw [Measure.map_map (measurable_mul_const _) hf]
  conv_rhs => rw [← map_mul_right_eq_self μ g]
  rw [Measure.map_map hf (measurable_mul_const _)]
  congr 1
  funext x
  simp

variable {m : ℕ} {Q : QuadForm ℝ (m + 1)} {c : ℝ} {y : Fin (m + 1) → ℝ}

theorem SplitFrame.isMulRightInvariant_stabMeasure (F : SplitFrame Q c y) (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) :
    (F.stabMeasure hc hQ).IsMulRightInvariant := by
  haveI := isMulRightInvariant_lerayMeasure (F.gramDetR_Q' hQ)
  haveI := measurableMul_subgroup (stabilizer (ArchSO Q) y)
  haveI := isMulRightInvariant_map_of_surjective (lerayMeasure F.Q' (F.gramDetR_Q' hQ)) F.stabHom
    F.measurable_stabHom (F.stabHom_surjective hc)
  unfold SplitFrame.stabMeasure
  infer_instance

/-- **The real-place stabilizer measures are right invariant** ($H_y\cong SO(Q'_y)(\mathbb R)$ is unimodular). -/
theorem isMulRightInvariant_realStabMeasure (Q : QuadForm ℝ (m + 1)) (hQ : gramDetR Q ≠ 0) (hc : c ≠ 0)
    (y : Fin (m + 1) → ℝ) : (realStabMeasure Q hQ hc y).IsMulRightInvariant := by
  unfold realStabMeasure
  split_ifs with hy
  · exact (frameAt Q hc hy).isMulRightInvariant_stabMeasure hc hQ
  · exact ⟨fun g => by simp⟩

end Real

/-! ### Right invariance for products -/

section Products

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Group (A i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, MeasurableMul (A i)] {Y : ι → Type*} [∀ i, MulAction (A i) (Y i)] {T : ι → Type*}
  [∀ i, MeasurableSpace (T i)] {μA : ∀ i, Measure (A i)} {P : ∀ i, Set (Y i)} {σ : ∀ i, Measure (T i)}
  {τ : ∀ i, T i → Y i} {c : ι → ℝ≥0∞}

theorem ArchFibration.isMulRightInvariant_pi [∀ i, SigmaFinite (σ i)] (hc : ∀ i, c i ≠ ⊤)
    (𝔉 : ∀ i, ArchFibration (μA i) (P i) (σ i) (τ i) (c i)) (y : ∀ i, Y i)
    (h : ∀ i, ((𝔉 i).μH (y i)).IsMulRightInvariant) : ((ArchFibration.pi hc 𝔉).μH y).IsMulRightInvariant := by
  haveI := fun i => (𝔉 i).sigmaFinite (y i)
  haveI : ∀ i, MeasurableMul (stabilizer (A i) (y i)) := fun i => measurableMul_subgroup _
  haveI := measurableMul_subgroup (stabilizer (∀ i, A i) y)
  haveI := h
  have hm : Measurable (stabPi (A := A) y).symm.toMonoidHom := (stabPiME y).symm.measurable
  exact isMulRightInvariant_map_of_surjective (Measure.pi fun i => (𝔉 i).μH (y i)) (stabPi (A := A) y).symm.toMonoidHom hm
    (stabPi (A := A) y).symm.surjective

variable {A₁ A₂ : Type*} [Group A₁] [Group A₂] [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableMul A₁]
  [MeasurableMul A₂] {Y₁ Y₂ : Type*} [MulAction A₁ Y₁] [MulAction A₂ Y₂] {T₁ T₂ : Type*} [MeasurableSpace T₁]
  [MeasurableSpace T₂] {μ₁ : Measure A₁} {μ₂ : Measure A₂} {P₁ : Set Y₁} {P₂ : Set Y₂} {σ₁ : Measure T₁}
  {σ₂ : Measure T₂} {τ₁ : T₁ → Y₁} {τ₂ : T₂ → Y₂} {c₁ c₂ : ℝ≥0∞}

theorem ArchFibration.isMulRightInvariant_prod [SigmaFinite σ₁] [SigmaFinite σ₂]
    (𝔉₁ : ArchFibration μ₁ P₁ σ₁ τ₁ c₁) (𝔉₂ : ArchFibration μ₂ P₂ σ₂ τ₂ c₂) (y : Y₁ × Y₂)
    (h₁ : (𝔉₁.μH y.1).IsMulRightInvariant) (h₂ : (𝔉₂.μH y.2).IsMulRightInvariant) :
    ((ArchFibration.prod 𝔉₁ 𝔉₂).μH y).IsMulRightInvariant := by
  haveI := 𝔉₁.sigmaFinite y.1
  haveI := 𝔉₂.sigmaFinite y.2
  haveI := measurableMul_subgroup (stabilizer A₁ y.1)
  haveI := measurableMul_subgroup (stabilizer A₂ y.2)
  haveI := measurableMul_subgroup (stabilizer (A₁ × A₂) y)
  have hm : Measurable (stabProd (A₁ := A₁) (A₂ := A₂) y).symm.toMonoidHom := (stabProdME y).symm.measurable
  exact isMulRightInvariant_map_of_surjective ((𝔉₁.μH y.1).prod (𝔉₂.μH y.2)) (stabProd (A₁ := A₁) (A₂ := A₂) y).symm.toMonoidHom hm
    (stabProd (A₁ := A₁) (A₂ := A₂) y).symm.surjective

end Products

end QuadFormsKB.Tamagawa.Indefinite
