/-
# Shimura 2004, Lemma 4.4: the big cell $\mathfrak M = P_1^+\lambda P_1^+$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §4.2, Lemma 4.4
(printed pp. 30–31). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave6/Prop43.lean`: a weak Witt decomposition $V = U + Fe + Ff$ of a
nondegenerate $\varphi$, $\Psi : A(V) \cong M_2(A(U))$ (`psi`), $c_a$ the lower-left entry of $\Psi(a)$,
$P_1^+ = G^+(V) \cap P'_1$ (`parabolicGPlus Q (F ∙ e)`), $P_1^1 = G^1(V) \cap P'_1$ (`parabolicG1 Q (F ∙ e)`).
Shimura puts $\kappa = e + f$, $\iota = e - f$, and lets $\lambda$ denote $\kappa\varepsilon$ or $\iota\varepsilon$
with $\varepsilon \in U$, $\varepsilon^2 \ne 0$; here $\lambda = w\varepsilon$ with `hw : w = e + f ∨ w = e - f`
(the unit `lam`). $\mathfrak M = \{a \in G^+(V) \mid c_a \in A(U)^\times\}$ and $\mathfrak M^1 = \mathfrak M \cap
G^1(V)$ are written out as conditions.

**Proves** (all unconditional; standard axioms only): **Lemma 4.4**,
* $\mathfrak M = P_1^+\lambda P_1^+$ (`lemma_4_4`);
* $\mathfrak M^1 = P_1^1\lambda P_1^1$ provided $\nu(\lambda) = 1$ (`lemma_4_4_one`).

The proof is Shimura's identity (*): for $a \in \mathfrak M$, $\Psi(a) = \begin{pmatrix} 1 & ac^{-1} \\ 0 & 1
\end{pmatrix}\Psi(\lambda)\Psi(q)$ with $ac^{-1} \in U$ (Lemma 3.15 (i), (ii)), the first factor is $\Psi(1 + ye)$
(`Prop43.psi_one_add_ye`), and $q = \lambda^{-1}(1+ye)^{-1}a$ has $c_q = 0$, hence lies in $P_1^+$ by the first
assertion of Proposition 4.3 (`Prop43.mem_P1_iff`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave6.Prop43
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Lemma44

open MatrixModel Prop43

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

local notation "A" => CliffordAlgebra Q

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
  (hQ : (QuadraticMap.associated Q).Nondegenerate)
include he hf hef

theorem Q_w_ne_zero {w : V} (hw : w = e + f ∨ w = e - f) : Q w ≠ 0 := by
  rcases hw with rfl | rfl
  · rw [QuadraticMap.map_add (⇑Q), he, hf, hef]; norm_num
  · rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), he, QuadraticMap.map_neg, hf,
      QuadraticMap.polar_neg_right, hef]; norm_num

omit he hf hef in
/-- Shimura's $\lambda = w\varepsilon$ ($w = \kappa$ or $\iota$, $\varepsilon \in U$ anisotropic) as a unit. -/
def lam {w : V} (hw0 : Q w ≠ 0) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) : Aˣ :=
  vecUnit w hw0 * vecUnit (ε : V) hε

omit he hf hef in
theorem coe_lam {w : V} (hw0 : Q w ≠ 0) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) :
    ((lam hw0 ε hε : Aˣ) : A) = ι Q w * ι Q (ε : V) := rfl

omit he hf hef in
/-- $\lambda \in G^+(V)$ (Shimura, proof of Lemma 4.4: "$\lambda \in G^+(V)$"). -/
theorem lam_mem_M0 {w : V} (hw0 : Q w ≠ 0) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) :
    lam hw0 ε hε ∈ M0 Q :=
  ⟨by rw [coe_lam]; exact ι_mul_ι_mem_evenOdd_zero Q w ε,
    (cliffordGroup Q).mul_mem (vecUnit_mem w hw0) (vecUnit_mem (ε : V) hε)⟩

/-- $\Psi(\lambda) = \begin{pmatrix} 0 & -\varepsilon \\ \pm\varepsilon & 0\end{pmatrix}$. -/
theorem psi_lam {w : V} (hw : w = e + f ∨ w = e - f) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) :
    ∃ σ : F, σ ≠ 0 ∧ psi he hf hef ((lam (Q_w_ne_zero he hf hef hw) ε hε : Aˣ) : A) =
      !![0, -ι (QU Q e f) ε; σ • ι (QU Q e f) ε, 0] := by
  have hpw : ∃ σ : F, σ ≠ 0 ∧ psi he hf hef (ι Q w) = !![0, 1; algebraMap F _ σ, 0] := by
    rcases hw with rfl | rfl
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [map_add, map_add, psi_e, psi_f]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · refine ⟨-1, by norm_num, ?_⟩
      rw [map_sub, map_sub, psi_e, psi_f]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨σ, hσ, hpsi⟩ := hpw
  refine ⟨σ, hσ, ?_⟩
  rw [coe_lam, map_mul, hpsi, psi_ι_of_mem]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

omit he hf hef in
/-- $\varepsilon$ is a unit of $A(U)$ ($\varepsilon^2 = \varphi[\varepsilon] \ne 0$). -/
theorem isUnit_ι_eps (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) : IsUnit (ι (QU Q e f) ε) :=
  (vecUnit (Q := QU Q e f) ε hε).isUnit

include hQ in
/-- The entry $a$ of $\Psi(q)$ for $q \in P'_1$ is invertible ($a = rd$ by (4.10)). -/
theorem isUnit_a (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (F ∙ e)) :
    IsUnit (psi he hf hef ((α : Aˣ) : A) 0 0) := by
  obtain ⟨r, hd, y, hr, -, hshape⟩ := prop_4_3_shape he hf hef hQ α hα
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 0 0) hshape
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h00
  rw [h00, Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.2 hr).map (algebraMap F (AU Q e f))).mul hd

omit he hf hef in
/-- An element of $P_1^+$ as an element of $G'(V)$. -/
theorem homog_of_mem_P {p : Aˣ} (hp : p ∈ parabolicGPlus Q (F ∙ e)) : p ∈ homogeneousCliffordGroup Q :=
  M0_le_homogeneous hp.1

include hQ in
/-- $P_1^+\lambda P_1^+ \subseteq \mathfrak M$. -/
theorem mem_M_of_mul {w : V} (hw : w = e + f ∨ w = e - f) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0)
    {p q : Aˣ} (hp : p ∈ parabolicGPlus Q (F ∙ e)) (hq : q ∈ parabolicGPlus Q (F ∙ e)) :
    p * lam (Q_w_ne_zero he hf hef hw) ε hε * q ∈ M0 Q ∧
      IsUnit (psi he hf hef ((p * lam (Q_w_ne_zero he hf hef hw) ε hε * q : Aˣ) : A) 1 0) := by
  refine ⟨(M0 Q).mul_mem ((M0 Q).mul_mem hp.1 (lam_mem_M0 _ ε hε)) hq.1, ?_⟩
  obtain ⟨σ, hσ, hl⟩ := psi_lam he hf hef hw ε hε
  set P : homogeneousCliffordGroup Q := ⟨p, homog_of_mem_P hp⟩
  set Qh : homogeneousCliffordGroup Q := ⟨q, homog_of_mem_P hq⟩
  have hpc := (mem_P1_iff he hf hef hQ P).1 hp.2
  have hpd := isUnit_d he hf hef hQ P hpc
  have hqa := isUnit_a he hf hef hQ Qh hq.2
  -- $c_{p\lambda q} = d_p\,(\sigma\varepsilon)\,a_q$
  have key : psi he hf hef ((p * lam (Q_w_ne_zero he hf hef hw) ε hε * q : Aˣ) : A) 1 0 =
      psi he hf hef (p : A) 1 1 * (σ • ι (QU Q e f) ε) * psi he hf hef (q : A) 0 0 := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_zero, zero_mul, add_zero, zero_add]
    rw [show psi he hf hef (p : A) 1 0 = 0 from hpc, zero_mul, zero_mul, add_zero]
  rw [key]
  refine (hpd.mul ?_).mul hqa
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.2 hσ).map (algebraMap F (AU Q e f))).mul (isUnit_ι_eps ε hε)

include hQ in
/-- The decomposition (*) in the proof of Lemma 4.4: every $a \in \mathfrak M$ is $(1 + ye)\lambda q$ with
$1 + ye \in P_1^+$, $(1 + ye)(1 + ye)^* = 1$ and $q \in G^+(V)$, $c_q = 0$. -/
theorem decomp_M {w : V} (hw : w = e + f ∨ w = e - f) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0)
    {a : Aˣ} (ha : a ∈ M0 Q) (hc : IsUnit (psi he hf hef (a : A) 1 0)) :
    ∃ g : Aˣ, g ∈ parabolicGPlus Q (F ∙ e) ∧ (g : A) * reverse (g : A) = 1 ∧
      (lam (Q_w_ne_zero he hf hef hw) ε hε)⁻¹ * g⁻¹ * a ∈ parabolicGPlus Q (F ∙ e) := by
  set ξ := psi he hf hef (a : A) with hξ
  set Ah : homogeneousCliffordGroup Q := ⟨a, M0_le_homogeneous ha⟩
  -- $y = ac^{-1} \in U$
  obtain ⟨-, ⟨-, hac, -, -⟩, -, -⟩ := lemma_3_15_i he hf hef hQ Ah
  obtain ⟨hcc, ⟨t, ht⟩, -⟩ := lemma_3_15_ii he hf hef hQ Ah 1 0
  change ξ 1 0 * reverse (ξ 1 0) = reverse (ξ 1 0) * ξ 1 0 at hcc
  change ξ 1 0 * reverse (ξ 1 0) = algebraMap F _ t at ht
  change IsVecU Q e f (ξ 0 0 * reverse (ξ 1 0)) at hac
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    have h0 : reverse (ξ 1 0) = 0 := hc.mul_right_eq_zero.1 ht
    have h1 : ξ 1 0 = 0 := by simpa using congrArg reverse h0
    exact hc.ne_zero h1
  obtain ⟨u, hu⟩ := hac
  set y : uSpace Q e f := t⁻¹ • u
  have hy : ι (QU Q e f) y * ξ 1 0 = ξ 0 0 := by
    rw [map_smul, smul_mul_assoc, ← hu, mul_assoc, ← hcc, ht, ← Algebra.commutes, ← Algebra.smul_def,
      smul_smul, inv_mul_cancel₀ ht0, one_smul]
  obtain ⟨g, hg, hgM⟩ := exists_one_add_ye he hf hef y
  have hpg : psi he hf hef (g : A) = !![1, ι (QU Q e f) y; 0, 1] := by rw [hg, psi_one_add_ye]
  have hgP : g ∈ parabolicGPlus Q (F ∙ e) :=
    ⟨hgM, (mem_P1_iff he hf hef hQ ⟨g, M0_le_homogeneous hgM⟩).2 (by
      change psi he hf hef (g : A) 1 0 = 0
      rw [hpg]; simp)⟩
  have hgr : (g : A) * reverse (g : A) = 1 := by
    rw [hg, mul_reverse_rxy, (mem_uSpace.1 y.2).1, he]; simp
  refine ⟨g, hgP, hgr, ?_⟩
  set l := lam (Q_w_ne_zero he hf hef hw) ε hε
  have hqM : l⁻¹ * g⁻¹ * a ∈ M0 Q :=
    (M0 Q).mul_mem ((M0 Q).mul_mem ((M0 Q).inv_mem (lam_mem_M0 _ ε hε)) ((M0 Q).inv_mem hgM)) ha
  refine ⟨hqM, (mem_P1_iff he hf hef hQ ⟨_, M0_le_homogeneous hqM⟩).2 ?_⟩
  change psi he hf hef ((l⁻¹ * g⁻¹ * a : Aˣ) : A) 1 0 = 0
  -- $a = g b$ and $b = \lambda q$
  have hgb : (a : A) = (g : A) * ((g⁻¹ * a : Aˣ) : A) := by
    rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have hlq : ((g⁻¹ * a : Aˣ) : A) = (l : A) * ((l⁻¹ * g⁻¹ * a : Aˣ) : A) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  set B := psi he hf hef ((g⁻¹ * a : Aˣ) : A)
  set C := psi he hf hef ((l⁻¹ * g⁻¹ * a : Aˣ) : A)
  have E1 := congrArg (psi he hf hef) hgb
  rw [map_mul, hpg] at E1
  have E00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 0 0) E1
  have E10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 1 0) E1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    one_mul, zero_mul, zero_add] at E00 E10
  have hB00 : B 0 0 = 0 := by
    have h1 : ξ 0 0 = B 0 0 + ι (QU Q e f) y * ξ 1 0 := by rw [hξ, E10]; exact E00
    rw [hy] at h1
    exact (add_eq_right.1 h1.symm)
  obtain ⟨σ, -, hl⟩ := psi_lam he hf hef hw ε hε
  have E2 := congrArg (psi he hf hef) hlq
  rw [map_mul, hl] at E2
  have F00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 0 0) E2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    zero_mul, zero_add, neg_mul] at F00
  change B 0 0 = -(ι (QU Q e f) ε * C 1 0) at F00
  rw [hB00, eq_comm, neg_eq_zero] at F00
  exact (isUnit_ι_eps ε hε).mul_right_eq_zero.1 F00

include hQ in
/-- **Lemma 4.4** (Shimura 2004, p. 30): $\mathfrak M = P_1^+\lambda P_1^+$, where $\mathfrak M = \{a \in G^+(V)
\mid c_a \in A(U)^\times\}$ and $\lambda = \kappa\varepsilon$ or $\iota\varepsilon$ ($\kappa = e + f$,
$\iota = e - f$, $\varepsilon \in U$, $\varepsilon^2 \ne 0$). -/
@[kb "shimura2004" "Lemma 4.4, p. 30 (𝔐 = P_1^+ λ P_1^+)"]
theorem lemma_4_4 {w : V} (hw : w = e + f ∨ w = e - f) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0) (a : Aˣ) :
    (a ∈ M0 Q ∧ IsUnit (psi he hf hef (a : A) 1 0)) ↔
      ∃ p ∈ parabolicGPlus Q (F ∙ e), ∃ q ∈ parabolicGPlus Q (F ∙ e),
        a = p * lam (Q_w_ne_zero he hf hef hw) ε hε * q := by
  constructor
  · rintro ⟨ha, hc⟩
    obtain ⟨g, hg, -, hq⟩ := decomp_M he hf hef hQ hw ε hε ha hc
    exact ⟨g, hg, _, hq, by group⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact mem_M_of_mul he hf hef hQ hw ε hε hp hq

include hQ in
/-- **Lemma 4.4** (Shimura 2004, p. 30), second assertion: $\mathfrak M^1 = P_1^1\lambda P_1^1$ provided
$\nu(\lambda) = 1$, where $\mathfrak M^1 = \mathfrak M \cap G^1(V)$. -/
@[kb "shimura2004" "Lemma 4.4, p. 30 (𝔐¹ = P_1^1 λ P_1^1 provided ν(λ) = 1)"]
theorem lemma_4_4_one {w : V} (hw : w = e + f ∨ w = e - f) (ε : uSpace Q e f) (hε : Q (ε : V) ≠ 0)
    (hν : ((lam (Q_w_ne_zero he hf hef hw) ε hε : Aˣ) : A) *
      reverse ((lam (Q_w_ne_zero he hf hef hw) ε hε : Aˣ) : A) = 1) (a : Aˣ) :
    (a ∈ spinGroupG1 Q ∧ IsUnit (psi he hf hef (a : A) 1 0)) ↔
      ∃ p ∈ parabolicG1 Q (F ∙ e), ∃ q ∈ parabolicG1 Q (F ∙ e),
        a = p * lam (Q_w_ne_zero he hf hef hw) ε hε * q := by
  have hl1 : lam (Q_w_ne_zero he hf hef hw) ε hε ∈ spinGroupG1 Q := ⟨lam_mem_M0 _ ε hε, hν⟩
  constructor
  · rintro ⟨ha, hc⟩
    obtain ⟨g, hg, hgr, hq⟩ := decomp_M he hf hef hQ hw ε hε ha.1 hc
    have hg1 : g ∈ spinGroupG1 Q := ⟨hg.1, hgr⟩
    refine ⟨g, ⟨hg1, hg.2⟩, _, ⟨?_, hq.2⟩, by group⟩
    exact (spinGroupG1 Q).mul_mem ((spinGroupG1 Q).mul_mem ((spinGroupG1 Q).inv_mem hl1)
      ((spinGroupG1 Q).inv_mem hg1)) ha
  · rintro ⟨p, hp, q, hq, rfl⟩
    refine ⟨(spinGroupG1 Q).mul_mem ((spinGroupG1 Q).mul_mem hp.1 hl1) hq.1, ?_⟩
    exact (mem_M_of_mul he hf hef hQ hw ε hε ⟨spinGroupG1_le_M0 hp.1, hp.2⟩
      ⟨spinGroupG1_le_M0 hq.1, hq.2⟩).2

end Hyp

end Lemma44

end QuadFormsKB.Shimura2004
