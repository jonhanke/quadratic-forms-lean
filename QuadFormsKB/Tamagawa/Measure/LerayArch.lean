import QuadFormsKB.Tamagawa.Measure.LerayComplex

/-!
# The archimedean Leray measure for Weil's Tamagawa measure

For a nondegenerate quadratic form over a number field $F$, Weil's Tamagawa measure has at the archimedean places
the product of the gauge-form (Leray) measures: at a real place $\sigma$ the measure `LerayReal.lerayMeasure` on
$SO(Q_\sigma)(\mathbb R)$ (any signature), at a complex place $\tau$ the measure `LerayComplex.lerayMeasureC` on
$SO(Q_\tau)(\mathbb C)$. This file packages the product
$$\mu_\infty^{\mathrm{Leray}} = \prod_{\sigma\ \text{real}}\mu_{Q_\sigma} \times \prod_{\tau\ \text{complex}}\mu_{Q_\tau}$$
on $G_\infty = \prod_\sigma SO(Q_\sigma)(\mathbb R) \times \prod_\tau SO(Q_\tau)(\mathbb C)$ (`muArchLeray`, a Haar
measure), its number-field form indexed by the infinite places (`muArchNF`), and the specialization to `ArchSO.lean`: when every
real form is positive definite, the real factor is `muInf` (`pi_lerayMeasure_eq_muInf`), and when moreover there
are no complex places (totally real $F$, totally definite $Q$) the whole measure is `muInf` (`map_fst_muArchLeray`).
-/

open MeasureTheory Measure Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayArch

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {n : ℕ} {ιR ιC : Type*} [Fintype ιR] [Fintype ιC]

/-- **The archimedean group** $G_\infty = \prod_{i \in \iota_R} SO(Q_i)(\mathbb R) \times
\prod_{j \in \iota_C} SO(Q_j)(\mathbb C)$. -/
abbrev ArchGroup (QR : ιR → QuadForm ℝ n) (QC : ιC → QuadForm ℂ n) : Type _ :=
  (∀ i, ArchSO (QR i)) × (∀ j, ArchSOC (QC j))

instance (QR : ιR → QuadForm ℝ n) (i : ιR) (hR : ∀ i, gramDetR (QR i) ≠ 0) :
    SigmaFinite (lerayMeasure (QR i) (hR i)) := by
  have := isHaarMeasure_lerayMeasure (hR i); infer_instance

instance (QC : ιC → QuadForm ℂ n) (j : ιC) (hC : ∀ j, gramDetC (QC j) ≠ 0) :
    SigmaFinite (lerayMeasureC (QC j) (hC j)) := by
  have := isHaarMeasure_lerayMeasureC (hC j); infer_instance

/-- **The archimedean Leray measure** $\prod_i \mu_{Q_i} \times \prod_j \mu_{Q_j}$ on $G_\infty$ (real forms of any
signature, complex forms), the archimedean factor of Weil's Tamagawa measure (before the global constant). -/
@[kb "weil1982" "§2.2 (gauge forms at the archimedean places), §2.3 [unverified]"]
def muArchLeray (QR : ιR → QuadForm ℝ n) (QC : ιC → QuadForm ℂ n) (hR : ∀ i, gramDetR (QR i) ≠ 0)
    (hC : ∀ j, gramDetC (QC j) ≠ 0) : Measure (ArchGroup QR QC) :=
  (Measure.pi fun i => lerayMeasure (QR i) (hR i)).prod (Measure.pi fun j => lerayMeasureC (QC j) (hC j))

variable (QR : ιR → QuadForm ℝ n) (QC : ιC → QuadForm ℂ n) (hR : ∀ i, gramDetR (QR i) ≠ 0)
  (hC : ∀ j, gramDetC (QC j) ≠ 0)

instance isHaarMeasure_pi_lerayMeasure : (Measure.pi fun i => lerayMeasure (QR i) (hR i)).IsHaarMeasure := by
  have := fun i => isHaarMeasure_lerayMeasure (Q := QR i) (hR i); infer_instance

instance isHaarMeasure_pi_lerayMeasureC : (Measure.pi fun j => lerayMeasureC (QC j) (hC j)).IsHaarMeasure := by
  have := fun j => isHaarMeasure_lerayMeasureC (Q := QC j) (hC j); infer_instance

/-- **$\mu_\infty^{\mathrm{Leray}}$ is a Haar measure** on $G_\infty$. -/
@[kb "weil1982" "§2.2 (gauge forms) [unverified]"]
theorem isHaarMeasure_muArchLeray : (muArchLeray QR QC hR hC).IsHaarMeasure := by
  unfold muArchLeray; infer_instance

/-- **The definite real factor is `muInf`**: if every real form is positive definite ($n \ge 1$), then
$\prod_i \mu_{Q_i}$ = `muInf QR`. -/
@[kb "weil1982" "§2.2 (gauge forms); cf. muInf [unverified]"]
theorem pi_lerayMeasure_eq_muInf [∀ i, Fact (IsPosDefR (QR i))] (hn : 1 ≤ n) :
    (Measure.pi fun i => lerayMeasure (QR i) (hR i)) = muInf QR := by
  unfold muInf
  congr 1
  funext i
  exact lerayMeasure_eq_mu (hR i) hn

/-- **Totally real, totally definite case** (no complex places, every real form positive definite, $n \ge 1$): the
archimedean Leray measure is `muInf` (the $\mathbb C$-factor is a point of mass $1$). -/
@[kb "weil1982" "§2.2 (gauge forms); cf. muInf [unverified]"]
theorem map_fst_muArchLeray [IsEmpty ιC] [∀ i, Fact (IsPosDefR (QR i))] (hn : 1 ≤ n) :
    (muArchLeray QR QC hR hC).map Prod.fst = muInf QR := by
  rw [muArchLeray, Measure.map_fst_prod, Measure.pi_of_empty, dirac_apply_of_mem (mem_univ _), one_smul,
    pi_lerayMeasure_eq_muInf QR hR hn]

/-! ### Number-field form -/

open NumberField NumberField.InfinitePlace

open Classical in
/-- **The archimedean Leray measure of a form over a number field** $F$: the product over the real places $w$ of
$\mu_{Q^{\sigma_w}}$ ($\sigma_w$ the real embedding) and over the complex places $w$ of $\mu_{Q^{\tau_w}}$ ($\tau_w$ the
chosen complex embedding of $w$; another choice is the complex conjugate, giving an isomorphic form). -/
@[kb "weil1982" "§2.2, §2.3 (archimedean factors of the Tamagawa measure) [unverified]"]
def muArchNF {F : Type*} [Field F] [NumberField F] (Q₀ : QuadForm F n)
    (hR : ∀ w : {w : InfinitePlace F // w.IsReal}, gramDetR (Q₀.map (embedding_of_isReal w.2)) ≠ 0)
    (hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, gramDetC (Q₀.map w.1.embedding) ≠ 0) :
    Measure (ArchGroup (fun w : {w : InfinitePlace F // w.IsReal} => Q₀.map (embedding_of_isReal w.2))
      (fun w : {w : InfinitePlace F // w.IsComplex} => Q₀.map w.1.embedding)) :=
  muArchLeray _ _ hR hC

end QuadFormsKB.Tamagawa.Measure.LerayArch
