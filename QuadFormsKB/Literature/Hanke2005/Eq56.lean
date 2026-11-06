/-
# Hanke 2005, (5.1)–(5.3) and (5.6): the archimedean fibration $F : G_a\to Z$ and the volume of $\Gamma\backslash Z$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting** (§5, p. 16). The archimedean places are given in Hanke's normal forms (2.9): a family of real places
$i\in\iota_R$ with $\varphi_i = \mathrm{diag}[1_{q_i}, -1_{r_i}]$, $q_i = r_i + t_i$ (`phiQ (r i) (t i)`; $r_i = 0$ for a definite
place, where $Z_i$ is a point), and a family of complex places $j\in\iota_C$ with $G_j = SO_n(\mathbb C)$. Then
* `GA` $= G_a = \prod_iSO(\varphi_i)\times\prod_jSO_n(\mathbb C)$ with Hanke's measure `tauA` $=\tau_a = \prod_v\widetilde\omega_{G_v}$;
* `ZA` $= Z = \prod_vZ_v$ (5.2), with `muZA` $=\prod_v\omega_{Z_v}$ (Shimura's measures (4.2.8), (4.3.9));
* `FA` $= F : G_a\to Z$ (5.1), (5.3), componentwise $F_{\mathbb R}$, $F_{\mathbb C}$; the action of $G_a$ on $Z$ (`ArchActionReal`,
  `ArchActionComplex`); `volCA` $=\mathrm{vol}_C(C_a) = \prod_v\mathrm{vol}_C(C_v)$.

**Proves**
* `map_FA` (the fibration of $G_a$ over $Z$): $F_*\tau_a = \mathrm{vol}_C(C_a)\,\mu_Z$; at the real places this is proved
  (`ArchReal.map_FR_hankeHaar`), at the complex places it is the named statement `ArchFibrationComplex n`
  (so `map_FA` is unconditional when $\iota_C$ is empty, `map_FA_real`);
* `eq56` (**(5.6)**, via Lemma A7): for a countable subgroup $\Gamma\le G_a$ with a fundamental domain $E$ and a set
  $D\subseteq Z$ meeting almost every $\Gamma$-orbit $s$ times,
  $s\cdot\tau_a(E) = \mathrm{vol}_C(C_a)\,\mu_Z(D)$, i.e.
  $\tau_a(\Gamma_a\backslash G_a)\,\mathrm{vol}_C(C_a)^{-1} = s^{-1}\mathrm{vol}_Z(\Gamma_a\backslash Z)$, with
  $s = [\Gamma\cap S:1]$, $S$ the kernel of the action. (By Lemma A1, `lemmaA1_real` and `lemmaA1_complex`, $S$ consists of
  the elements that are $\pm1$ at every indefinite real place and every complex place; for $\Gamma_a = G(k)\cap aDa^{-1}$
  and $a$ not totally definite this gives Hanke's $[\Gamma_a\cap\{\pm1\}:1]$.)
-/
import QuadFormsKB.Literature.Hanke2005.ArchActionReal
import QuadFormsKB.Literature.Hanke2005.ArchActionComplex
import QuadFormsKB.Literature.Hanke2005.ArchProductFibration
import QuadFormsKB.Literature.Hanke2005.LemmaA7

open MeasureTheory Measure
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.Arch56

open QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Hanke2005.ArchReal QuadFormsKB.Hanke2005.ArchCx

variable {ιR ιC : Type*} [Fintype ιR] [Fintype ιC] [DecidableEq ιR] [DecidableEq ιC]
  (r t : ιR → ℕ) (n : ℕ)

/-- **$G_a$ in normal form** (Hanke thesis, §1 and (2.9)): $\prod_iSO(\varphi_i)\times\prod_jSO_n(\mathbb C)$. -/
abbrev GA (ιC : Type*) : Type _ := (∀ i, ArchSO (phiQ (r i) (t i))) × (ιC → ArchSOC (sumSqC n))

/-- **$Z = \prod_{v\in a}Z_v$** (Hanke thesis, (5.2), p. 16). -/
abbrev ZA (ιC : Type*) : Type _ := (∀ i, Fin (r i + t i) → Fin (r i) → ℝ) × (ιC → LIdx n → ℝ)

/-- **Hanke's measure $\tau_a$ on $G_a$**: the product of the $\widetilde\omega_{G_v}$. -/
@[kb "hanke2005crelle" "§2, p. 5 (τ_a = ∏_{v∈a} ω̃_G)"]
def tauA : Measure (GA r t n ιC) :=
  (Measure.pi fun i => hankeHaarR (r i) (t i)).prod (Measure.pi fun _ : ιC => hankeHaarC n)

/-- **The measure on $Z$**: the product of Shimura's measures $\omega_{Z_v}$. -/
@[kb "hanke2005crelle" "(5.2), p. 16; (4.2.8), p. 12; (4.3.9), p. 14"]
def muZA : Measure (ZA r t n ιC) :=
  (Measure.pi fun i => muZR (r i) (t i)).prod (Measure.pi fun _ : ιC => muZC n)

/-- **$F : G_a\to Z$** (Hanke thesis, (5.1), (5.3), p. 16), $F(\alpha) = (\alpha_vp_v)_v$. -/
@[kb "hanke2005crelle" "(5.1), (5.3), p. 16"]
def FA (g : GA r t n ιC) : ZA r t n ιC := (fun i => FRG (g.1 i), fun j => FCG (g.2 j))

/-- **$\mathrm{vol}_C(C_a) = \prod_{v\in a}\mathrm{vol}_C(C_v)$** (Hanke thesis, (5.6)–(5.7), p. 17). -/
def volCA (ιC : Type*) [Fintype ιC] : ℝ := (∏ i, volCReal (r i + t i) (r i)) * volCComplex n ^ Fintype.card ιC

theorem volCReal_pos (q r : ℕ) : 0 < volCReal q r := by
  unfold volCReal; have := tauR_pos q; have := tauR_pos r; positivity

theorem volCComplex_pos (n : ℕ) : 0 < volCComplex n := by
  unfold volCComplex; have := tauR_pos n; positivity

theorem measurable_FCG' : Measurable (FCG (n := n)) := by
  have hm : Continuous (ArchSOC.mat (sumSqC n)) := ArchSOC.continuous_mat _
  have hre : Continuous fun g : ArchSOC (sumSqC n) => reM (ArchSOC.mat _ g) := by
    unfold reM; exact hm.matrix_map Complex.continuous_re
  have him : Continuous fun g : ArchSOC (sumSqC n) => imM (ArchSOC.mat _ g) := by
    unfold imM; exact hm.matrix_map Complex.continuous_im
  have hlow : Continuous (lowerOf : Matrix (Fin n) (Fin n) ℝ → LIdx n → ℝ) := by
    refine continuous_pi fun p => ?_
    unfold lowerOf; fun_prop
  have : (FCG (n := n)) = fun g => lowerOf (-imM (ArchSOC.mat _ g) * (reM (ArchSOC.mat _ g))⁻¹) := by
    funext g; rw [FCG, actC_zero]
  rw [this]
  exact hlow.measurable.comp (ArchCx.measurable_matMul him.measurable.neg (ArchCx.measurable_matInv hre.measurable))

theorem measurable_FA : Measurable (FA r t n (ιC := ιC)) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun i => measurable_FRG.comp ((measurable_pi_apply i).comp measurable_fst)
  · exact measurable_pi_iff.mpr fun j => (measurable_FCG' n).comp ((measurable_pi_apply j).comp measurable_snd)

set_option maxHeartbeats 1000000 in
/-- **The fibration $F : G_a\to Z$** (Hanke thesis, (5.1)–(5.3) with §4): $F_*\tau_a = \mathrm{vol}_C(C_a)\,\mu_Z$, the real places
by `map_FR_hankeHaar` (proved), the complex places by the named statement `ArchFibrationComplex n`. -/
@[kb "hanke2005crelle" "(5.1)–(5.3), p. 16; §4.2–§4.3"]
theorem map_FA (ht : ∀ i, 1 ≤ r i + t i) (hC : Nonempty ιC → ArchFibrationComplex n) :
    (tauA r t n (ιC := ιC)).map (FA r t n) = ENNReal.ofReal (volCA r t n ιC) • muZA r t n := by
  haveI : ∀ i, SigmaFinite (hankeHaarR (r i) (t i)) := fun i => inferInstance
  haveI : ∀ i, SigmaFinite (muZR (r i) (t i)) := fun i => inferInstance
  have e₁ := map_pi_eq_smul_pi (μ := fun i => hankeHaarR (r i) (t i)) (ν := fun i => muZR (r i) (t i))
    (F := fun i => (FRG : ArchSO (phiQ (r i) (t i)) → _)) (fun i => measurable_FRG)
    (c := fun i => ENNReal.ofReal (volCReal (r i + t i) (r i))) (fun i => ENNReal.ofReal_ne_top)
    (fun i => map_FR_hankeHaar (ht i))
  have e₂ := map_pi_eq_smul_pi (ι := ιC) (μ := fun _ => hankeHaarC n) (ν := fun _ => muZC n)
    (F := fun _ => (FCG : ArchSOC (sumSqC n) → _)) (fun _ => measurable_FCG' n)
    (c := fun _ => ENNReal.ofReal (volCComplex n)) (fun _ => ENNReal.ofReal_ne_top) (fun j => (hC ⟨j⟩).map_eq)
  have hc₁ : (∏ i, ENNReal.ofReal (volCReal (r i + t i) (r i))) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hc₂ : (∏ _j : ιC, ENNReal.ofReal (volCComplex n)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hm₁ : Measurable fun (g : ∀ i, ArchSO (phiQ (r i) (t i))) i => FRG (g i) :=
    measurable_pi_iff.mpr fun i => measurable_FRG.comp (measurable_pi_apply i)
  have hm₂ : Measurable fun (g : ιC → ArchSOC (sumSqC n)) j => FCG (g j) :=
    measurable_pi_iff.mpr fun j => (measurable_FCG' n).comp (measurable_pi_apply j)
  have h := map_prod_eq_smul_prod hm₁ hm₂ hc₁ hc₂ e₁ e₂
  rw [tauA, muZA, show FA r t n (ιC := ιC) = Prod.map (fun g i => FRG (g i)) (fun g j => FCG (g j)) from rfl, h]
  congr 1
  rw [volCA, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (volCReal_pos _ _).le), ENNReal.ofReal_prod_of_nonneg
    (fun i _ => (volCReal_pos _ _).le), ENNReal.ofReal_pow (volCComplex_pos n).le, Finset.prod_const, Finset.card_univ]

/-! ### The action of $G_a$ on $Z$ and (5.6) -/

/-- The componentwise action of $G_a$ on $Z$ (Hanke thesis, (4.2.2), (4.3.2); §5, p. 16). -/
instance : SMul (GA r t n ιC) (ZA r t n ιC) := ⟨fun g z => (fun i => g.1 i • z.1 i, fun j => g.2 j • z.2 j)⟩

theorem smul_ZA (g : GA r t n ιC) (z : ZA r t n ιC) :
    g • z = (fun i => g.1 i • z.1 i, fun j => g.2 j • z.2 j) := rfl

instance : MulAction (GA r t n ιC) (ZA r t n ιC) where
  one_smul z := by
    rw [smul_ZA]; ext i <;> simp
  mul_smul g h z := by
    rw [smul_ZA, smul_ZA, smul_ZA]; ext i <;> simp [mul_smul]

instance : MeasurableConstSMul (GA r t n ιC) (ZA r t n ιC) where
  measurable_const_smul g := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun i =>
        (measurable_const_smul (g.1 i)).comp ((measurable_pi_apply i).comp measurable_fst)
    · exact measurable_pi_iff.mpr fun j =>
        (measurable_const_smul (g.2 j)).comp ((measurable_pi_apply j).comp measurable_snd)

/-- **$F$ is $G_a$-equivariant** (Hanke thesis, (5.1)): $F(gh) = g\cdot F(h)$. -/
theorem FA_mul (g h : GA r t n ιC) : FA r t n (g * h) = g • FA r t n h := by
  rw [FA, FA, smul_ZA]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · exact FRG_mul (g.1 i) (h.1 i)
  · exact FCG_mul (g.2 j) (h.2 j)

instance (r t : ℕ) : (hankeHaarR r t).IsMulLeftInvariant := by
  have := isHaarMeasure_lerayMeasure (gramDetR_phiQ_ne_zero (r := r) (t := t))
  unfold hankeHaarR; infer_instance

instance (n : ℕ) : (hankeHaarC n).IsMulLeftInvariant := by
  have := isHaarMeasure_lerayMeasureC (gramDetC_sumSqC_ne_zero (n := n))
  unfold hankeHaarC; infer_instance

instance : (tauA r t n (ιC := ιC)).IsMulLeftInvariant := by
  unfold tauA; infer_instance

/-- **(5.6)** (Hanke thesis, p. 17), via Lemma A7 and the fibration `map_FA`: for a countable subgroup
$\Gamma\le G_a$ with a fundamental domain $E$ (so $\tau_a(E) = \tau_a(\Gamma\backslash G_a)$) and a measurable $D\subseteq Z$
meeting almost every $\Gamma$-orbit $s$ times (so $\mu_Z(D) = \mathrm{vol}_Z(\Gamma\backslash Z)$ when $s = [\Gamma\cap S:1]$, $S$ the
kernel of the action), $s\cdot\tau_a(\Gamma\backslash G_a) = \mathrm{vol}_C(C_a)\cdot\mathrm{vol}_Z(\Gamma\backslash Z)$. Unconditional at the
real places; the complex places enter through the named statement `ArchFibrationComplex n`. -/
@[kb "hanke2005crelle" "(5.6), p. 17"]
theorem eq56 (ht : ∀ i, 1 ≤ r i + t i) (hC : Nonempty ιC → ArchFibrationComplex n) (Γ : Subgroup (GA r t n ιC)) [Countable Γ]
    {E : Set (GA r t n ιC)} (hE : IsFundamentalDomain Γ E (tauA r t n)) {D : Set (ZA r t n ιC)}
    (hD : MeasurableSet D) {s : ℝ≥0∞}
    (hDs : ∀ᵐ z ∂(muZA r t n (ιC := ιC)), ∑' γ : Γ, D.indicator 1 (γ • z) = s) :
    s * tauA r t n E = ENNReal.ofReal (volCA r t n ιC) * muZA r t n D :=
  lemmaA7 (Γ := Γ) (measurable_FA r t n) (fun γ x => FA_mul r t n (γ : GA r t n ιC) x) (map_FA r t n ht hC) hE hD hDs

/-- **(5.6) at the real places only** (e.g. a totally real field): no named input. -/
@[kb "hanke2005crelle" "(5.6), p. 17 (no complex places)"]
theorem eq56_real [IsEmpty ιC] (ht : ∀ i, 1 ≤ r i + t i) (Γ : Subgroup (GA r t n ιC)) [Countable Γ]
    {E : Set (GA r t n ιC)} (hE : IsFundamentalDomain Γ E (tauA r t n)) {D : Set (ZA r t n ιC)}
    (hD : MeasurableSet D) {s : ℝ≥0∞}
    (hDs : ∀ᵐ z ∂(muZA r t n (ιC := ιC)), ∑' γ : Γ, D.indicator 1 (γ • z) = s) :
    s * tauA r t n E = ENNReal.ofReal (volCA r t n ιC) * muZA r t n D :=
  eq56 r t n ht (fun h => isEmptyElim h.some) Γ hE hD hDs

end QuadFormsKB.Hanke2005.Arch56
