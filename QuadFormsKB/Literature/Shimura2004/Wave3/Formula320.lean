/-
# Shimura 2004, (3.20a,b): the stabilizer of the line $Fh$ in $G^+(V)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, Lemma 3.16,
formulas (3.20a), (3.20b) (printed p. 27). Page numbers are printed pages.

**Setting and dictionary.** As in `Wave2/Hyperplane.lean` and `Wave3/SubspaceGroup.lean`: $\varphi$ nondegenerate,
$h \in V$ with $h^2 = \varphi[h] \ne 0$, $W = (Fh)^\perp$, $G^\pm(W)$ = `subspaceCliffordGroup Q h 0`,
`subspaceCliffordGroup Q h 1`, $G^+(V)$ = `Cassels.M0 Q`, $\nu$ = `multiplier`, $a \mapsto a^*$ = `reverse`.

**Proves** (unconditional; standard axioms only):
* (3.20a): $\{a \in G^+(V) : a^*ha \in Fh\} = G^+(W) \cup hG^-(W)$ (`formula_3_20a`);
* (3.20b): $\{a \in G^+(V) : a^*ha = \nu(a)h\} = G^+(W)$ (`formula_3_20b`); equivalently $G^+(W)$ is the
  centralizer of $h$ in $G^+(V)$ (`formula_3_20b_conj`).

The inclusions "$\supseteq$" are Lemma 3.16 (`lemma_3_16_even`, `lemma_3_16_h_odd`). For "$\subseteq$":
if $a^*ha = \mu h$ then $a^{-1}ha = \lambda h$ with $\lambda = \mu/\nu(a)$, and squaring gives $\lambda = \pm 1$; for
$\lambda = 1$, $a$ commutes with $h$, so $a \in A(W)$ by the converse of (3.14) (`mem_cliffordSubalgebra_iff`); for
$\lambda = -1$, $b = h^{-1}a$ anticommutes with $h$, so $b \in G^-(W)$ and $a = hb$. (Shimura obtains these from
Lemma 3.13; the direct argument avoids it.)
-/
import QuadFormsKB.Literature.Shimura2004.Wave3.Lemma313
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-- For $a \in G^+(V)$, $a^* = \nu(a)a^{-1}$, so $a^*ha = \mu h$ turns into $\nu(a)\,a^{-1}ha = \mu h$. -/
theorem reverse_eq_smul_inv (hQ : (QuadraticMap.associated Q).Nondegenerate) {a : (CliffordAlgebra Q)ˣ}
    (ha : a ∈ homogeneousCliffordGroup Q) :
    reverse (a : A) = (multiplier hQ ⟨a, ha⟩ : F) • ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) := by
  have h := algebraMap_multiplier hQ ⟨a, ha⟩
  calc reverse (a : A) = ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ((a : A) * reverse (a : A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by
        change _ * ((((⟨a, ha⟩ : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : A) *
          reverse ((((⟨a, ha⟩ : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : A))) = _
        rw [← h, ← Algebra.commutes, ← Algebra.smul_def]

/-- $a^{-1}ha = \lambda h$ with $h^2 \ne 0$ forces $\lambda = \pm 1$. -/
theorem eq_one_or_neg_one_of_conj {h : V} (hh : Q h ≠ 0) (a : (CliffordAlgebra Q)ˣ) {l : F}
    (hl : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a = l • ι Q h) : l = 1 ∨ l = -1 := by
  have hsq : (((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a) * (((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a) =
      algebraMap F A (Q h) := by
    have : (((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a) * (((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a) =
        ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * ((a : A) * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A)) * ι Q h * a := by
      simp only [mul_assoc]
    rw [this, Units.mul_inv, mul_one, mul_assoc _ (ι Q h) (ι Q h), ι_sq_scalar, ← Algebra.commutes,
      mul_assoc, Units.inv_mul, mul_one]
  have e : (l • ι Q h) * (l • ι Q h) = algebraMap F A (Q h) := hl ▸ hsq
  rw [smul_mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul] at e
  have h1 : l * l * Q h = Q h := (algebraMap F A).injective e
  have h2 : l * l = 1 := mul_right_cancel₀ hh (h1.trans (one_mul _).symm)
  exact mul_self_eq_one_iff.1 h2

/-- **(3.20a)** (Shimura 2004, Lemma 3.16, p. 27): for nondegenerate $\varphi$, $h^2 \ne 0$ and $W = (Fh)^\perp$,
an element $a \in G^+(V)$ satisfies $a^*ha \in Fh$ if and only if $a \in G^+(W)$ or $a = hb$ with $b \in G^-(W)$. -/
@[kb "shimura2004" "(3.20a), p. 27 ({a ∈ G⁺(V) : a*ha ∈ Fh} = G⁺(W) ∪ hG⁻(W))"]
theorem formula_3_20a (hQ : (QuadraticMap.associated Q).Nondegenerate) {h : V} (hh : Q h ≠ 0)
    (a : (CliffordAlgebra Q)ˣ) (ha : a ∈ M0 Q) :
    (∃ μ : F, reverse (a : A) * ι Q h * a = μ • ι Q h) ↔
      (a ∈ subspaceCliffordGroup Q h 0 ∨
        ∃ b ∈ subspaceCliffordGroup Q h 1, (a : A) = ι Q h * (b : A)) := by
  have hah : a ∈ homogeneousCliffordGroup Q := M0_le_homogeneous ha
  set ν : F := (multiplier hQ ⟨a, hah⟩ : F)
  have hν : ν ≠ 0 := (multiplier hQ ⟨a, hah⟩).ne_zero
  constructor
  · rintro ⟨μ, hμ⟩
    rw [reverse_eq_smul_inv hQ hah, smul_mul_assoc, smul_mul_assoc] at hμ
    have hconj : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a = (ν⁻¹ * μ) • ι Q h := by
      rw [mul_smul, ← hμ, smul_smul, inv_mul_cancel₀ hν, one_smul, mul_assoc]
    -- `h a = λ a h`
    have hcomm : ∀ l : F, ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a = l • ι Q h →
        (a : A) * (l • ι Q h) = ι Q h * a := by
      intro l hl
      rw [← hl, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    rcases eq_one_or_neg_one_of_conj hh a hconj with hl | hl
    · left
      have hc := hcomm _ hconj
      rw [hl, one_smul] at hc
      have hW : (a : A) ∈ cliffordSubalgebra Q h := by
        rw [mem_cliffordSubalgebra_iff hh, involute_eq_of_mem_even ha.1, hc]
      exact (mem_subspaceCliffordGroup_zero_iff hQ hh a).2 ⟨ha, hW⟩
    · right
      have hc := hcomm _ hconj
      rw [hl, neg_one_smul, mul_neg] at hc
      set H := vecUnit h hh
      set b : (CliffordAlgebra Q)ˣ := H⁻¹ * a
      have hHb : (H : A) * b = a := by
        change (H : A) * ((H⁻¹ * a : (CliffordAlgebra Q)ˣ) : A) = a
        rw [← Units.val_mul, mul_inv_cancel_left]
      have hbo : (b : A) ∈ evenOdd Q 1 := by
        have hHi : ((H⁻¹ : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1 :=
          mem_evenOdd_of_mul_eq_one Q (ι_mem_evenOdd_one Q h) H.mul_inv
        change ((H⁻¹ * a : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 1
        rw [Units.val_mul]
        simpa using mul_mem_evenOdd hHi ha.1
      have hbG : b ∈ cliffordGroup Q :=
        (cliffordGroup Q).mul_mem ((cliffordGroup Q).inv_mem (vecUnit_mem h hh)) ha.2
      have hbκ : (b : A) * ι Q h = ι Q h * involute (b : A) := by
        rw [involute_eq_of_mem_odd hbo]
        apply (Units.mul_right_inj H).1
        change (H : A) * ((b : A) * ι Q h) = (H : A) * (ι Q h * -(b : A))
        have hHb' : ι Q h * (b : A) = a := hHb
        have L : (H : A) * ((b : A) * ι Q h) = (a : A) * ι Q h := by rw [← mul_assoc, hHb]
        have R : (H : A) * (ι Q h * -(b : A)) = -(ι Q h * a) := by
          rw [mul_neg, mul_neg]
          change -(ι Q h * (ι Q h * (b : A))) = _
          rw [hHb']
        rw [L, R]
        exact neg_eq_iff_eq_neg.1 hc
      have hbW : (b : A) ∈ cliffordSubalgebra Q h := (mem_cliffordSubalgebra_iff hh _).2 hbκ
      exact ⟨b, (mem_subspaceCliffordGroup_one_iff hQ hh b).2 ⟨⟨hbG, hbo⟩, hbW⟩, hHb.symm⟩
  · rintro (h0 | ⟨b, hb, hab⟩)
    · obtain ⟨-, haW⟩ := (mem_subspaceCliffordGroup_zero_iff hQ hh a).1 h0
      refine ⟨ν, ?_⟩
      rw [lemma_3_16_even hQ h ⟨a, hah⟩ haW ha.1, Algebra.smul_def]
    · obtain ⟨hbo, hbW⟩ := (mem_subspaceCliffordGroup_one_iff hQ hh b).1 hb
      refine ⟨-ν, ?_⟩
      rw [lemma_3_16_h_odd hQ h ⟨a, hah⟩ ⟨b, cliffordGroupOdd_subset_homogeneous hbo⟩ hab hbW hbo.2,
        neg_smul, Algebra.smul_def]

/-- **(3.20b)** (Shimura 2004, Lemma 3.16, p. 27): for nondegenerate $\varphi$, $h^2 \ne 0$ and $W = (Fh)^\perp$,
an element $a \in G^+(V)$ satisfies $a^*ha = \nu(a)h$ if and only if $a \in G^+(W)$. -/
@[kb "shimura2004" "(3.20b), p. 27 ({a ∈ G⁺(V) : a*ha = ν(a)h} = G⁺(W))"]
theorem formula_3_20b (hQ : (QuadraticMap.associated Q).Nondegenerate) {h : V} (hh : Q h ≠ 0)
    (a : (CliffordAlgebra Q)ˣ) (ha : a ∈ M0 Q) :
    reverse (a : A) * ι Q h * a = (multiplier hQ ⟨a, M0_le_homogeneous ha⟩ : F) • ι Q h ↔
      a ∈ subspaceCliffordGroup Q h 0 := by
  have hah : a ∈ homogeneousCliffordGroup Q := M0_le_homogeneous ha
  set ν : F := (multiplier hQ ⟨a, hah⟩ : F)
  have hν : ν ≠ 0 := (multiplier hQ ⟨a, hah⟩).ne_zero
  constructor
  · intro hμ
    rw [reverse_eq_smul_inv hQ hah, smul_mul_assoc, smul_mul_assoc] at hμ
    have hconj : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a = ι Q h :=
      smul_right_injective A hν hμ
    have hc : (a : A) * ι Q h = ι Q h * a := by
      conv_lhs => rw [← hconj]
      simp only [← mul_assoc, Units.mul_inv, one_mul]
    have hW : (a : A) ∈ cliffordSubalgebra Q h := by
      rw [mem_cliffordSubalgebra_iff hh, involute_eq_of_mem_even ha.1, hc]
    exact (mem_subspaceCliffordGroup_zero_iff hQ hh a).2 ⟨ha, hW⟩
  · intro h0
    obtain ⟨-, haW⟩ := (mem_subspaceCliffordGroup_zero_iff hQ hh a).1 h0
    rw [lemma_3_16_even hQ h ⟨a, hah⟩ haW ha.1, Algebra.smul_def]

/-- (3.20b) in centralizer form: $G^+(W) = \{a \in G^+(V) : a^{-1}ha = h\}$. -/
theorem formula_3_20b_conj (hQ : (QuadraticMap.associated Q).Nondegenerate) {h : V} (hh : Q h ≠ 0)
    (a : (CliffordAlgebra Q)ˣ) (ha : a ∈ M0 Q) :
    ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q h * a = ι Q h ↔ a ∈ subspaceCliffordGroup Q h 0 := by
  constructor
  · intro hconj
    have hc : (a : A) * ι Q h = ι Q h * a := by
      conv_lhs => rw [← hconj]
      simp only [← mul_assoc, Units.mul_inv, one_mul]
    have hW : (a : A) ∈ cliffordSubalgebra Q h := by
      rw [mem_cliffordSubalgebra_iff hh, involute_eq_of_mem_even ha.1, hc]
    exact (mem_subspaceCliffordGroup_zero_iff hQ hh a).2 ⟨ha, hW⟩
  · intro h0
    obtain ⟨-, haW⟩ := (mem_subspaceCliffordGroup_zero_iff hQ hh a).1 h0
    exact lemma_3_16_conj_eq h a haW ha.1

end QuadFormsKB.Shimura2004
