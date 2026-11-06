/-
# Hanke 2005, (5.4)–(5.7): Hanke's mass as a sum of volumes of $\Gamma_a\backslash Z$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n\ge1$ variables, $\Lambda = \mathcal O_F^n$,
$G_a = SO(V)(F\otimes\mathbb R)$ = `GInfSO Q₀` with Hanke's measure $\tau_a$ = `muArchHanke`, the classes $a$ = `DC Q₀`
with unit groups $\Gamma_a$ = `unitGroup Q₀ a`. At each real place $w$ the form $Q^{\sigma_w}$ is brought to Hanke's normal
form (2.9) (`DR`, `transR`), at each complex place to the sum of squares (`DCx`, `transC`).

**Defines** $Z = \prod_{v\in a}Z_v$ (`ZQ`) with Shimura's measure (`muZQ`), $F : G_a\to Z$ (`FQ`) and the action of $G_a$ on $Z$.

**Proves**
* `map_FQ`: $F_*\tau_a = \mathrm{vol}_C(C_a)\,\mu_Z$ with $\mathrm{vol}_C(C_a) = \prod_v$`volCAt Q₀ v` (the volumes of §4 for the
  matrix $\psi$), unconditional at the real places, with the named statement `ArchFibrationComplex n` at the complex
  places;
* `hankeMass_eq_tsum` (**(5.6)–(5.7)**): for every family of measurable $D_a\subseteq Z$ such that $D_a$ meets almost every
  $\Gamma_a$-orbit $s_a$ times ($0 < s_a < \infty$),
  $$\texttt{hankeMass} = \sum_{a\in\mathrm{Cl}}\frac{\tau_a(\Gamma_a\backslash G_a)}{\mathrm{vol}_C(C_a)}
  = \sum_{a\in\mathrm{Cl}}s_a^{-1}\,\mu_Z(D_a),$$
  which is Hanke's (5.4)–(5.5) $\mathrm{Mass}(\Lambda,\varphi) = \sum_a[\Gamma_a\cap\{\pm1\}:1]^{-1}\mathrm{vol}(\Gamma_a\backslash Z)$ when
  $D_a$ is a fundamental domain of $\Gamma_a/(\Gamma_a\cap S)$ and $s_a = [\Gamma_a\cap S:1]$;
* `theorem51_volZ`: Theorem 5.1 for this mass.
-/
import QuadFormsKB.Literature.Hanke2005.MuArchHankeFactor
import QuadFormsKB.Literature.Hanke2005.ArchTransportReal
import QuadFormsKB.Literature.Hanke2005.ArchTransportComplex
import QuadFormsKB.Literature.Hanke2005.Eq56
import QuadFormsKB.Literature.Hanke2005.Unconditional
import QuadFormsKB.Tamagawa.Measure.Weil.FundamentalDomain

open MeasureTheory Measure NumberField NumberField.InfinitePlace
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.Eq57

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.LerayArch QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.ArchReal
  QuadFormsKB.Hanke2005.ArchCx QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

open scoped Classical

/-- The normal form data (2.9) at a real place. -/
def DR (w : {w : InfinitePlace F // w.IsReal}) : NFData (QRe Q₀ w) :=
  NFData.ofExists _ (gramDetR_QRe_ne_zero Q₀ hQ w)

/-- The normal form data at a complex place. -/
def DCx (w : {w : InfinitePlace F // w.IsComplex}) : NFDataC (QCx Q₀ w) :=
  NFDataC.ofExists _ (gramDetC_QCx_ne_zero Q₀ hQ w)

/-- **$Z = \prod_{v\in a}Z_v$** for $Q_0$ (Hanke thesis, (5.2), p. 16). -/
abbrev ZQ : Type :=
  (∀ w : {w : InfinitePlace F // w.IsReal}, Fin ((DR Q₀ hQ w).r + (DR Q₀ hQ w).t) → Fin (DR Q₀ hQ w).r → ℝ) ×
    ({w : InfinitePlace F // w.IsComplex} → LIdx n → ℝ)

/-- **Shimura's measure on $Z$** for $Q_0$. -/
@[kb "hanke2005crelle" "(5.2), p. 16; (4.2.8), (4.3.9)"]
def muZQ : Measure (ZQ Q₀ hQ) :=
  (Measure.pi fun w => muZR (DR Q₀ hQ w).r (DR Q₀ hQ w).t).prod (Measure.pi fun _ => muZC n)

/-- **$F : G_a\to Z$** for $Q_0$ (Hanke thesis, (5.1), (5.3), p. 16). -/
@[kb "hanke2005crelle" "(5.1), (5.3), p. 16"]
def FQ (g : GInfSO Q₀) : ZQ Q₀ hQ := (fun w => FRQ (DR Q₀ hQ w) (g.1 w), fun w => FCQ (DCx Q₀ hQ w) (g.2 w))

theorem measurable_FQ : Measurable (FQ Q₀ hQ) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun w => (measurable_FRQ _).comp ((measurable_pi_apply w).comp measurable_fst)
  · exact measurable_pi_iff.mpr fun w => (measurable_FCQ _).comp ((measurable_pi_apply w).comp measurable_snd)

theorem DR_r_eq (w : {w : InfinitePlace F // w.IsReal}) : (DR Q₀ hQ w).r = rAt Q₀ w.1 := by
  rw [rAt_eq_wittIndex]; exact (DR Q₀ hQ w).hw

theorem volCAt_real (w : {w : InfinitePlace F // w.IsReal}) :
    volCAt Q₀ w.1 = |gramDetR (QRe Q₀ w)| ^ (-((n : ℝ) + 1) / 2) *
      volCReal ((DR Q₀ hQ w).r + (DR Q₀ hQ w).t) (DR Q₀ hQ w).r := by
  have h1 : n - rAt Q₀ w.1 = (DR Q₀ hQ w).r + (DR Q₀ hQ w).t := by
    rw [← DR_r_eq Q₀ hQ w]; have := (DR Q₀ hQ w).hn; omega
  rw [volCAt, volFactor_real, if_pos w.2, h1, DR_r_eq Q₀ hQ w]

theorem volCAt_complex (w : {w : InfinitePlace F // w.IsComplex}) :
    volCAt Q₀ w.1 = (‖gramDetC (QCx Q₀ w)‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * volCComplex n := by
  rw [volCAt, volFactor_complex, if_neg (not_isReal_iff_isComplex.mpr w.2)]

theorem prod_volCAt :
    ∏ w, volCAt Q₀ w = (∏ w : {w : InfinitePlace F // w.IsReal}, volCAt Q₀ w.1) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, volCAt Q₀ w.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _ fun w => rfl

/-- **The fibration $F : G_a\to Z$ for $Q_0$** (Hanke thesis, (5.1)–(5.3) and §4 with (2.9)):
$F_*\tau_a = \mathrm{vol}_C(C_a)\,\mu_Z$, $\mathrm{vol}_C(C_a) = \prod_v$`volCAt Q₀ v`. -/
@[kb "hanke2005crelle" "(5.1)–(5.3), p. 16; §4; (2.9)"]
theorem map_FQ (hn : 1 ≤ n) (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n) :
    (muArchHanke Q₀ hQ).map (FQ Q₀ hQ) = ENNReal.ofReal (∏ w, volCAt Q₀ w) • muZQ Q₀ hQ := by
  rw [muArchHanke_eq]
  haveI : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite (ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) •
      lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)) := fun w => by
    haveI := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q₀ hQ w)
    exact ArchCx.sigmaFinite_ofReal_smul _ _
  haveI : ∀ w : {w : InfinitePlace F // w.IsComplex}, SigmaFinite (ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) •
      lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)) := fun w => by
    haveI := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q₀ hQ w)
    exact ArchCx.sigmaFinite_ofReal_smul _ _
  have e₁ := map_pi_eq_smul_pi
    (μ := fun w : {w : InfinitePlace F // w.IsReal} => ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) •
      lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w))
    (ν := fun w => muZR (DR Q₀ hQ w).r (DR Q₀ hQ w).t) (F := fun w => FRQ (DR Q₀ hQ w))
    (fun w => measurable_FRQ _) (c := fun w => ENNReal.ofReal (volCAt Q₀ w.1)) (fun _ => ENNReal.ofReal_ne_top)
    (fun w => by rw [volCAt_real Q₀ hQ w]; exact map_FRQ _ _ hn)
  have e₂ := map_pi_eq_smul_pi
    (μ := fun w : {w : InfinitePlace F // w.IsComplex} => ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) •
      lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w))
    (ν := fun _ => muZC n) (F := fun w => FCQ (DCx Q₀ hQ w))
    (fun w => measurable_FCQ _) (c := fun w => ENNReal.ofReal (volCAt Q₀ w.1)) (fun _ => ENNReal.ofReal_ne_top)
    (fun w => by rw [volCAt_complex Q₀ w]; exact map_FCQ _ (hC ⟨w⟩) _)
  have hc₁ : (∏ w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal (volCAt Q₀ w.1)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hc₂ : (∏ w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal (volCAt Q₀ w.1)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hm₁ : Measurable fun (g : ∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe Q₀ w)) w =>
      FRQ (DR Q₀ hQ w) (g w) :=
    measurable_pi_iff.mpr fun w => (measurable_FRQ _).comp (measurable_pi_apply w)
  have hm₂ : Measurable fun (g : ∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx Q₀ w)) w =>
      FCQ (DCx Q₀ hQ w) (g w) :=
    measurable_pi_iff.mpr fun w => (measurable_FCQ _).comp (measurable_pi_apply w)
  have h := map_prod_eq_smul_prod hm₁ hm₂ hc₁ hc₂ e₁ e₂
  rw [show FQ Q₀ hQ = Prod.map (fun g w => FRQ (DR Q₀ hQ w) (g w)) (fun g w => FCQ (DCx Q₀ hQ w) (g w)) from rfl]
  rw [h, muZQ, prod_volCAt, ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (volCAt_pos Q₀ hQ _).le),
    ENNReal.ofReal_prod_of_nonneg (fun w _ => (volCAt_pos Q₀ hQ _).le),
    ENNReal.ofReal_prod_of_nonneg (fun w _ => (volCAt_pos Q₀ hQ _).le)]

/-! ### The action of $G_a$ on $Z$ -/

instance : SMul (GInfSO Q₀) (ZQ Q₀ hQ) :=
  ⟨fun g z => (fun w => transR (DR Q₀ hQ w) (g.1 w) • z.1 w, fun w => transC (DCx Q₀ hQ w) (g.2 w) • z.2 w)⟩

theorem smul_ZQ (g : GInfSO Q₀) (z : ZQ Q₀ hQ) :
    g • z = (fun w => transR (DR Q₀ hQ w) (g.1 w) • z.1 w, fun w => transC (DCx Q₀ hQ w) (g.2 w) • z.2 w) := rfl

instance : MulAction (GInfSO Q₀) (ZQ Q₀ hQ) where
  one_smul z := by
    rw [smul_ZQ]; ext w <;> simp
  mul_smul g h z := by
    rw [smul_ZQ, smul_ZQ, smul_ZQ]; ext w <;> simp [mul_smul]

instance : MeasurableConstSMul (GInfSO Q₀) (ZQ Q₀ hQ) where
  measurable_const_smul g := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun w =>
        (measurable_const_smul (transR (DR Q₀ hQ w) (g.1 w))).comp ((measurable_pi_apply w).comp measurable_fst)
    · exact measurable_pi_iff.mpr fun w =>
        (measurable_const_smul (transC (DCx Q₀ hQ w) (g.2 w))).comp ((measurable_pi_apply w).comp measurable_snd)

theorem FQ_mul (g h : GInfSO Q₀) : FQ Q₀ hQ (g * h) = g • FQ Q₀ hQ h := by
  rw [FQ, FQ, smul_ZQ]
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · show FRG (transR _ (g.1 w * h.1 w)) = _
    rw [map_mul, FRG_mul]; rfl
  · exact FCQ_mul _ (g.2 w) (h.2 w)

/-! ### (5.6)–(5.7) -/

/-- **(5.6) for the unit group of a class** (Hanke thesis, p. 17): $s_a\,\tau_a(\Gamma_a\backslash G_a) =
\mathrm{vol}_C(C_a)\,\mu_Z(D_a)$ for $D_a$ meeting almost every $\Gamma_a$-orbit $s_a$ times. -/
@[kb "hanke2005crelle" "(5.6), p. 17"]
theorem eq56_class (hn : 1 ≤ n) (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n)
    (i : DC Q₀) {D : Set (ZQ Q₀ hQ)} (hD : MeasurableSet D) {s : ℝ≥0∞}
    (hDs : ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, D.indicator 1 (γ • z) = s) :
    s * covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (∏ w, volCAt Q₀ w) * muZQ Q₀ hQ D := by
  have := countable_GammaSOAdele Q₀
  have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  haveI := discreteTopology_levelGroup Q₀ (dcRep Q₀ i)
  obtain ⟨E, hE⟩ := exists_isFundamentalDomain (unitGroup Q₀ i) (muArchHanke Q₀ hQ)
  rw [hE.covolume_eq_volume]
  exact lemmaA7 (Γ := unitGroup Q₀ i) (measurable_FQ Q₀ hQ) (fun γ x => FQ_mul Q₀ hQ (γ : GInfSO Q₀) x)
    (map_FQ Q₀ hQ hn hC) hE hD hDs

/-- **(5.6)–(5.7): Hanke's mass is the sum of the volumes of $\Gamma_a\backslash Z$** (Hanke thesis, (5.4)–(5.7),
pp. 16–17): for every family $D_a\subseteq Z$ ($a\in\mathrm{Cl}$) of measurable sets meeting almost every
$\Gamma_a$-orbit $s_a$ times, $0 < s_a < \infty$,
$$\texttt{hankeMass}(Q_0) = \sum_a\frac{\tau_a(\Gamma_a\backslash G_a)}{\mathrm{vol}_C(C_a)} = \sum_a s_a^{-1}\,\mathrm{vol}_Z(D_a).$$
With $s_a = [\Gamma_a\cap\{\pm1\}:1]$ and $D_a$ a fundamental domain of $\Gamma_a/(\Gamma_a\cap\{\pm1\})$ on $Z$ this is
$\mathrm{Mass}(\Lambda,\varphi) = \sum_a\nu(\Gamma_a)$ of (5.4)–(5.5). Unconditional at the real places; the complex places
enter through `ArchFibrationComplex n`. -/
@[kb "hanke2005crelle" "(5.4)–(5.7), pp. 16–17"]
theorem hankeMass_eq_tsum (hn : 1 ≤ n) (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) :
    hankeMass Q₀ hQ = ∑' i, muZQ Q₀ hQ (D i) / s i := by
  set C := ENNReal.ofReal (∏ w, volCAt Q₀ w)
  have hC0 : C ≠ 0 := by
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun w _ => volCAt_pos Q₀ hQ w
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcov : ∀ i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) = C * (muZQ Q₀ hQ (D i) / s i) := by
    intro i
    have h := eq56_class Q₀ hQ hn hC i (hD i) (hDs i)
    rw [← ENNReal.eq_div_iff (hs0 i) (hsT i)] at h
    rw [h, mul_div_assoc]
  rw [hankeMass, tsum_congr hcov, ENNReal.tsum_mul_left, mul_comm, ENNReal.mul_div_cancel_right hC0 hCT]

/-- **Theorem 5.1 for Hanke's mass (5.4)–(5.5)** (Hanke thesis, pp. 16–19): for $n\ge3$, $\mathcal O_F^n$ maximal and Shimura's
hypothesis, and any family $D_a$ as in `hankeMass_eq_tsum` (in particular $s_a = [\Gamma_a\cap\{\pm1\}:1]$ and $D_a$ a fundamental
domain of the effective action of $\Gamma_a$ on $Z$),
$$\sum_{a\in\mathrm{Cl}}s_a^{-1}\,\mathrm{vol}_Z(D_a) = \text{the right side of Theorem 5.1}.$$
The archimedean volumes $\mathrm{vol}_C(C_v)$ are no longer stated values: at the real places they are proved to be the fibre
volumes (`ArchReal.map_FR_hankeHaar`); at the complex places they enter through the named statement
`ArchFibrationComplex n`. The finite places enter through `ShimuraMaximalDensityRest F` (`theorem51_of_rest`). -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19; (5.4)–(5.7)"]
theorem theorem51_volZ (I : ShimuraMaximalDensityRest F) (hn : 3 ≤ n) (hmax : StdIsMaximal Q₀)
    (hdet : ShimuraDetHyp Q₀) (hC : Nonempty {w : InfinitePlace F // w.IsComplex} → ArchFibrationComplex n)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) :
    ∑' i, muZQ Q₀ hQ (D i) / s i = ENNReal.ofReal (theorem51RHS Q₀) := by
  rw [← hankeMass_eq_tsum Q₀ hQ (by omega) hC D hD s hs0 hsT hDs, theorem51_of_rest I hn Q₀ hQ hmax hdet]

/-- **Theorem 5.1 for Hanke's mass over a totally real field**: as `theorem51_volZ`, with no archimedean input. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19; (5.4)–(5.7) (totally real field)"]
theorem theorem51_volZ_totallyReal [IsTotallyReal F] (I : ShimuraMaximalDensityRest F) (hn : 3 ≤ n)
    (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) :
    ∑' i, muZQ Q₀ hQ (D i) / s i = ENNReal.ofReal (theorem51RHS Q₀) := by
  refine theorem51_volZ Q₀ hQ I hn hmax hdet (fun h => ?_) D hD s hs0 hsT hDs
  exfalso
  obtain ⟨⟨w, hw⟩⟩ := h
  exact (not_isReal_iff_isComplex.mpr hw) (IsTotallyReal.isReal w)

end QuadFormsKB.Hanke2005.Eq57
