/-
# Cassels, Chapter 9, Examples 11-13: indefinite unimodular forms and lattices of index $p$ in binary lattices

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 11-13, pp. 164-165.

**Status.** Example 12 (i)-(iii) is proved unconditionally in this file (with the reconstructions and the erratum noted
below). Example 12 (iv) and Example 13 (i), (ii) are proved in `Ch9Examples11.lean`, which builds on the definitions
of this file (`ImpMat`, `ProMat`, `theta`, `psi`, `Emap`, `transport`, ...). Example 11 (Serre's classification of
indefinite unimodular forms) is not formalized here; see "Not formalized".

**Conventions.** Indices are $0$-based (`Fin 2`; variables $x_0, x_1$; Cassels' $x_1, x_2$). A binary form is
given by its Gram matrix $F = (f_{ij})$ (Cassels' *classical* convention, $f(x) = \sum f_{ij} x_i x_j$, "integral"
means $f_{ij} \in \mathbb Z$, "primitive" means $\gcd(f_{ij}) = 1$, the determinant is $\det F$). In the library's terms
(`Ch9Sec1.lean`, `Ch9Sec6Weight.lean`) these are the `QuadForm ℤ 2` with `IsPrimitiveCI` and Gram matrix `casselsMat`;
proper equivalence is `ProperIntEquiv` ($\mathrm{SL}_2(\mathbb Z)$).

**Lattices (Example 12 (i), (ii)).** A $2$-dimensional regular quadratic space over $\mathbb Q$ is modelled as
$V = \mathbb Q^{2}$ with $\varphi(x, y) = x^{\mathsf T} S y$, $S$ symmetric and invertible (`S`); a lattice is a
$\mathbb Z$-submodule `Λ : Submodule ℤ (Fin 2 → ℚ)` with a basis (`HasDet`); `IsIntegralOn`, `IsPrimitiveOn` and
`HasDet` express "$\varphi$ induces an integral / primitive form of determinant $d$"; `IsPrimIntLat` is their
conjunction.

**Proves**
* `ex12_i` (**Ex. 12 (i)**): a primitive integral lattice of determinant $d p^{2}$ has exactly one overlattice carrying a
  primitive integral form of determinant $d$ (any prime $p$);
* `ex12_ii` (**Ex. 12 (ii)**): a primitive integral lattice of determinant $d$ ($p$ odd) has exactly $p - (-d/p)$
  sublattices carrying a primitive integral form of determinant $d p^{2}$;
* `ex12_iii` (**Ex. 12 (iii)**): $h(d p^{2}) = (p - (-d/p))\, h(d)$ for $d \ge 2$, $d \ne 3$, where $h$ counts proper
  classes (`hClasses`); the general recursion under the hypothesis "proper automorphs are $\pm I$" is `hcl_mul`;
* `aut_pm_one` (the hint of Ex. 12 (iii)): a primitive binary form of determinant $d \ge 2$, $d \ne 3$ has only the
  proper automorphs $\pm I$.

**Method.** The $p + 1$ sublattices of index $p$ of $\mathbb Z^{2}$ are the kernels of the $p + 1$ functionals
`evf ρ`, `ρ ∈ ℙ¹(𝔽_p)` (`Cρ` is a basis, `exists_ρ_of_det`); a sublattice is primitive iff the form does not vanish
on the line `ρ` modulo $p$ (`Fl_char`), and the count follows from the number of roots of a binary quadratic form over
$\mathbb F_p$ (`card_nonvan`, via Mathlib's `legendreSym.card_sqrts`). The overlattice of (i) is $p^{-1} B C_\rho$ for
the unique line with the integrality condition `PCond` (`pcond_exists`, `pcond_unique`, `Gl_char_mpr`, `Gl_char_mp`).
For (iii) the map (class of $H$, line $\rho$) $\mapsto$ class of $C_\rho^{\mathsf T} H C_\rho$ is a bijection
(`Emap_injective`, `Emap_surjective`): surjectivity writes a form of determinant $d p^{2}$ as $\operatorname{adj}(C_\rho)^{\mathsf T}H'\operatorname{adj}(C_\rho)$
(`exists_sub`), injectivity uses the uniqueness of the overlattice (`transport`) and that the proper automorphs act
trivially on the sublattices (they are $\pm I$). The class numbers are finite or not, the count is by cardinalities.
The bridge between Gram matrices and the library's forms is `libEquiv`, `libRel_iff`, `hClasses_eq`.

**Reconstructed from garbled text.** The printed formula for $N$ in (ii) is illegible; $N = p - (-d/p)$ is derived
and checked numerically (`ex12_ii`). The factor in (iii) is $N$ (the printed text has "$h(dp^{2}) = N h(d)$").

**Errata and updates.**
* *Erratum* (hint of (iii)): "a primitive integral form of determinant $d > 3$ has only the automorphs $\pm I$" is false
  for improper automorphs (e.g. $x^{2} + 5y^{2}$ has $\operatorname{diag}(1, -1)$, Cassels p. 128); it is true for *proper*
  automorphs, which is what the argument uses (`aut_pm_one`).
* *Update:* the hypothesis "$d > 3$" can be weakened to "$d \ge 2$, $d \ne 3$" ($d = 2$ is covered; $d = 3$ and $d = 1$
  have proper automorphs of order $6$ and $4$); (i) holds for every prime $p$, not only odd $p$.

**Not formalized.**
* Example 11 (i)-(vi) (Serre 1964): indefinite unimodular classically integral forms are $\pm y_1^{2} \mp y_2^{2} + g$ or
  $2y_1y_2 + g$ and are classified by rank, signature and parity. Needs: isotropy of an indefinite unimodular form over
  $\mathbb Q$ (Hasse-Minkowski with the oddity/reciprocity argument at $2$), Example 9, the $\mathbb Z_p$-classification
  of unimodular forms, and "one class per genus" for indefinite unimodular lattices (spinor norm of unimodular
  lattices, Ch. 11 Thm. 1.4 in `Literature/Cassels/Ch11Sec1Indef.lean` for lattices over number fields).
  (Example 12 (iv) and Example 13 are formalized in `Ch9Examples11.lean`.)
-/

import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Literature.Cassels.Ch9Sec1

open Matrix

namespace QuadFormsKB.Siegel.Ch9Ex12

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: the functional $\mathbb Z^{2} \to \mathbb F_p$ cutting out the line `ρ` of $\mathbb P^{1}(\mathbb F_p)$ (`ρ = some t`: $z_1 - t z_0$; `ρ = none`: $z_0$). `z` is an integer vector of length $2$. -/
def evf (ρ : Option (ZMod p)) (z : Fin 2 → ℤ) : ZMod p :=
  match ρ with
  | some t => (z 1 : ZMod p) - t * (z 0 : ZMod p)
  | none => (z 0 : ZMod p)

/-- Helper: a basis matrix (columns) of the index-$p$ sublattice $\ker(\mathrm{evf}\ \rho)$ of $\mathbb Z^{2}$: `some t` gives columns $(1, \tilde t), (0, p)$ and `none` gives columns $(p, 0), (0, 1)$ ($\tilde t$ the least non-negative integer lift of `t`). The determinant is $p$ in all cases (`det_Cρ'`). -/
def Cρ (p : ℕ) (ρ : Option (ZMod p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  match ρ with
  | some t => !![1, 0; (t.val : ℤ), p]
  | none => !![p, 0; 0, 1]

/-- Helper: $\det C_\rho = p$ for every line `ρ`. -/
theorem det_Cρ' (ρ : Option (ZMod p)) : (Cρ p ρ).det = p := by
  cases ρ with
  | none => simp [Cρ, Matrix.det_fin_two_of]
  | some t => simp [Cρ, Matrix.det_fin_two_of]

/-- Helper: $\det C_\rho = \pm p$ (the form used for the general factorization lemmas). -/
theorem det_Cρ (ρ : Option (ZMod p)) : (Cρ p ρ).det = p ∨ (Cρ p ρ).det = -p := Or.inl (det_Cρ' ρ)

/-- Helper: a vector `z` lies in the column span of $C_\rho$ iff `evf ρ z = 0`. -/
theorem mem_range_Cρ_iff (ρ : Option (ZMod p)) (z : Fin 2 → ℤ) :
    (∃ w, z = Cρ p ρ *ᵥ w) ↔ evf ρ z = 0 := by
  cases ρ with
  | none =>
    simp only [evf, Cρ]
    constructor
    · rintro ⟨w, rfl⟩
      simp [mulVec, dotProduct, Fin.sum_univ_two]
    · intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨![k, z 1], ?_⟩
      ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, hk]
  | some t =>
    simp only [evf, Cρ]
    constructor
    · rintro ⟨w, rfl⟩
      simp [mulVec, dotProduct, Fin.sum_univ_two]
    · intro h
      have h' : ((z 1 - (t.val : ℤ) * z 0 : ℤ) : ZMod p) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val]; exact h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
      obtain ⟨k, hk⟩ := h'
      refine ⟨![z 0, k], ?_⟩
      ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, -ZMod.natCast_val, -ZMod.intCast_cast]
      linarith

/-- Helper: two lines with the same kernel are equal. -/
theorem ρ_inj {ρ ρ' : Option (ZMod p)} (h : ∀ z, evf ρ z = 0 ↔ evf ρ' z = 0) : ρ = ρ' := by
  have hp2 : (1 : ZMod p) ≠ 0 := one_ne_zero
  cases ρ with
  | none =>
    cases ρ' with
    | none => rfl
    | some t' =>
      have := (h ![0, 1]).1 (by simp [evf])
      simp [evf] at this
  | some t =>
    cases ρ' with
    | none =>
      have := (h ![0, 1]).2 (by simp [evf])
      simp [evf] at this
    | some t' =>
      have := (h ![1, (t.val : ℤ)]).1 (by simp [evf])
      simp [evf] at this
      rw [sub_eq_zero.mp this]

/-- Helper: the same functional on a pair of residues. -/
def ev2 (ρ : Option (ZMod p)) (x y : ZMod p) : ZMod p :=
  match ρ with
  | some t => y - t * x
  | none => x

/-- Helper: `evf` in terms of the residues of the coordinates. -/
theorem evf_eq_ev2 (ρ : Option (ZMod p)) (z : Fin 2 → ℤ) : evf ρ z = ev2 ρ (z 0 : ZMod p) (z 1 : ZMod p) := by
  cases ρ <;> rfl

/-- Helper (linear algebra over $\mathbb F_p$): if the two functionals $(\alpha, \beta)$ and $(\alpha', \beta')$ are parallel and not both zero, their common kernel is the kernel of `ev2 ρ` for some line `ρ`. -/
theorem exists_ρ_core (α β α' β' : ZMod p) (hpar : α * β' = β * α')
    (hne : α ≠ 0 ∨ β ≠ 0 ∨ α' ≠ 0 ∨ β' ≠ 0) :
    ∃ ρ : Option (ZMod p), ∀ x y : ZMod p, (α * x + β * y = 0 ∧ α' * x + β' * y = 0) ↔ ev2 ρ x y = 0 := by
  by_cases hβ : β ≠ 0
  · refine ⟨some (-α / β), fun x y => ?_⟩
    simp only [ev2]
    constructor
    · rintro ⟨h1, -⟩
      field_simp
      linear_combination h1
    · intro h
      have hy : y = -α / β * x := sub_eq_zero.mp h
      have hα' : α' = α * β' / β := by field_simp; linear_combination -hpar
      constructor
      · rw [hy]; field_simp; ring
      · rw [hy, hα']; field_simp; ring
  · push_neg at hβ
    by_cases hα : α ≠ 0
    · refine ⟨none, fun x y => ?_⟩
      simp only [ev2]
      have hβ' : β' = 0 := by
        have : α * β' = 0 := by rw [hpar, hβ, zero_mul]
        exact (mul_eq_zero.mp this).resolve_left hα
      constructor
      · rintro ⟨h1, -⟩
        rw [hβ, zero_mul, add_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_left hα
      · intro h
        rw [h]
        simp [hβ, hβ']
    · push_neg at hα
      by_cases hβ' : β' ≠ 0
      · refine ⟨some (-α' / β'), fun x y => ?_⟩
        simp only [ev2]
        constructor
        · rintro ⟨-, h2⟩
          field_simp
          linear_combination h2
        · intro h
          have hy : y = -α' / β' * x := sub_eq_zero.mp h
          rw [hα, hβ]
          refine ⟨by simp, ?_⟩
          rw [hy]; field_simp; ring
      · push_neg at hβ'
        have hα' : α' ≠ 0 := by
          rcases hne with h | h | h | h
          · exact absurd hα h
          · exact absurd hβ h
          · exact h
          · exact absurd hβ' h
        refine ⟨none, fun x y => ?_⟩
        simp only [ev2]
        constructor
        · rintro ⟨-, h2⟩
          rw [hβ', zero_mul, add_zero] at h2
          exact (mul_eq_zero.mp h2).resolve_left hα'
        · intro h
          rw [h]
          simp [hα, hβ, hβ']

/-- Helper: for an integer matrix `C` of determinant $\pm p$, `z` is in the column span of `C` iff $p$ divides $\operatorname{adj}(C) z$. -/
theorem mem_range_iff_adj (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det = p ∨ C.det = -p) (z : Fin 2 → ℤ) :
    (∃ w, z = C *ᵥ w) ↔ ∀ i, (p : ℤ) ∣ (C.adjugate *ᵥ z) i := by
  constructor
  · rintro ⟨w, rfl⟩ i
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul]
    rcases hC with h | h <;> rw [h]
    · exact dvd_mul_right _ _
    · exact (dvd_neg.mpr (dvd_refl _)).mul_right _
  · intro h
    choose k hk using h
    have hz : C.adjugate *ᵥ z = (p : ℤ) • k := by ext i; simp [hk i]
    have h1 : C *ᵥ (C.adjugate *ᵥ z) = C.det • z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hz, Matrix.mulVec_smul] at h1
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rcases hC with h | h
    · refine ⟨k, ?_⟩
      rw [h] at h1
      ext i
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact (mul_left_cancel₀ hp0 this).symm
    · refine ⟨-k, ?_⟩
      rw [h] at h1
      ext i
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mulVec_neg]
      simp only [Pi.neg_apply]
      have h2 : (p : ℤ) * (C *ᵥ k) i = (p : ℤ) * (-z i) := by rw [this]; ring
      exact (mul_left_cancel₀ hp0 h2).symm ▸ by ring

/-- Helper: **every index-$p$ sublattice of $\mathbb Z^{2}$ is one of the $p+1$ lattices $\ker(\mathrm{evf}\ \rho)$**: if an integer matrix `C` has determinant $\pm p$, its column span is the kernel of `evf ρ` for some line `ρ`. -/
theorem exists_ρ_of_det (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det = p ∨ C.det = -p) :
    ∃ ρ : Option (ZMod p), ∀ z, (∃ w, z = C *ᵥ w) ↔ evf ρ z = 0 := by
  have hz : ((C 0 0 : ℤ) : ZMod p) * (C 1 1 : ZMod p) - (C 0 1 : ZMod p) * (C 1 0 : ZMod p) = 0 := by
    have : ((C.det : ℤ) : ZMod p) = 0 := by
      rcases hC with h | h <;> simp [h]
    rw [Matrix.det_fin_two] at this; push_cast at this; exact this
  have hne : ((C 1 1 : ℤ) : ZMod p) ≠ 0 ∨ (-(C 0 1 : ℤ) : ZMod p) ≠ 0 ∨ (-(C 1 0 : ℤ) : ZMod p) ≠ 0 ∨
      ((C 0 0 : ℤ) : ZMod p) ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not, neg_eq_zero] at hcon
    obtain ⟨h11, h01, h10, h00⟩ := hcon
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h11 h01 h10 h00
    have h2 : (p : ℤ) * p ∣ C.det := by
      rw [Matrix.det_fin_two]
      exact dvd_sub (mul_dvd_mul h00 h11) (mul_dvd_mul h01 h10)
    have hpp : (p : ℤ) * p ∣ p := by
      rcases hC with h | h
      · rwa [h] at h2
      · rw [h] at h2; exact (dvd_neg.mp h2)
    have : (p : ℤ) ∣ 1 := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      obtain ⟨k, hk⟩ := hpp
      exact ⟨k, by nlinarith [mul_left_cancel₀ hp0 (show (p:ℤ) * 1 = p * (p * k) by linarith)]⟩
    have h1 : p ∣ 1 := by exact_mod_cast this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨ρ, hρ⟩ := exists_ρ_core (p := p) (C 1 1) (-(C 0 1)) (-(C 1 0)) (C 0 0) (by linear_combination hz) hne
  refine ⟨ρ, fun z => ?_⟩
  rw [mem_range_iff_adj C hC z, evf_eq_ev2, ← hρ]
  simp only [Fin.forall_fin_two, Matrix.adjugate_fin_two, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Counting the non-vanishing lines -/

open Classical in
/-- Helper: the line `ρ` is not a zero of the form `a x² + 2 b x y + c y²` modulo `p`. -/
def NonVan (a b c : ℤ) (ρ : Option (ZMod p)) : Prop :=
  match ρ with
  | some t => (a : ZMod p) + 2 * b * t + c * t ^ 2 ≠ 0
  | none => (c : ZMod p) ≠ 0

/-- Helper: for $c \not\equiv 0 \pmod p$ the number of roots $t \in \mathbb F_p$ of $a + 2bt + ct^{2}$ is $\left(\frac{b^{2} - ac}{p}\right) + 1$ (`a b c` integers, `p` odd). -/
theorem card_roots_of_ne (hp2 : p ≠ 2) (a b c : ℤ) (hc : (c : ZMod p) ≠ 0) :
    ((Finset.univ.filter fun t : ZMod p => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0).card : ℤ) =
      legendreSym p (b ^ 2 - a * c) + 1 := by
  rw [← legendreSym.card_sqrts p hp2 (b ^ 2 - a * c)]
  congr 1
  rw [Set.toFinset_ofPred]
  refine Finset.card_nbij' (fun t => c * t + b) (fun s => (s - b) / c) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    push_cast
    linear_combination (c : ZMod p) * ht
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    push_cast at hs
    field_simp
    linear_combination hs
  · intro t ht
    simp only
    field_simp
    ring
  · intro s hs
    simp only
    field_simp
    ring

open Classical in
/-- Helper: **the count of Exercise 12 (ii)**. If $p$ is odd and $a, b, c$ are integers not all divisible by $p$, the number of lines `ρ` on which $a x^{2} + 2bxy + cy^{2}$ does not vanish modulo $p$ equals $p - \left(\frac{b^{2} - ac}{p}\right)$. -/
theorem card_nonvan (hp2 : p ≠ 2) (a b c : ℤ)
    (hprim : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)) :
    ((Finset.univ.filter fun ρ : Option (ZMod p) => NonVan a b c ρ).card : ℤ) =
      p - legendreSym p (b ^ 2 - a * c) := by
  classical
  have hsplit : ∀ P : Option (ZMod p) → Prop, [DecidablePred P] →
      (Finset.univ.filter P).card =
        (if P none then 1 else 0) + (Finset.univ.filter fun t : ZMod p => P (some t)).card := by
    intro P _
    rw [Finset.card_filter, Fintype.sum_option, Finset.card_filter]
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  have hneg : ∀ Q : ZMod p → Prop, [DecidablePred Q] →
      (Finset.univ.filter fun t => ¬ Q t).card + (Finset.univ.filter Q).card = p := by
    intro Q _
    rw [add_comm, Finset.card_filter_add_card_filter_not (s := Finset.univ), hcard]
  rw [hsplit]
  have e : (Finset.univ.filter fun t : ZMod p => NonVan a b c (some t)) =
      Finset.univ.filter fun t : ZMod p => ¬ ((a : ZMod p) + 2 * b * t + c * t ^ 2 = 0) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [e]
  by_cases hc : (c : ZMod p) ≠ 0
  · have h1 := hneg (fun t => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0)
    have h2 := card_roots_of_ne hp2 a b c hc
    have hnv : NonVan a b c none := hc
    rw [if_pos hnv]
    have h1' : ((Finset.univ.filter fun t : ZMod p => ¬ ((a : ZMod p) + 2 * b * t + c * t ^ 2 = 0)).card : ℤ)
        + (Finset.univ.filter fun t : ZMod p => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0).card = p := by
      exact_mod_cast h1
    push_cast
    linarith
  · push Not at hc
    have hnv : ¬ NonVan a b c none := not_not.mpr hc
    rw [if_neg hnv]
    have hD : ((b ^ 2 - a * c : ℤ) : ZMod p) = (b : ZMod p) ^ 2 := by push_cast; rw [hc]; ring
    have h1 := hneg (fun t => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0)
    have h1' : ((Finset.univ.filter fun t : ZMod p => ¬ ((a : ZMod p) + 2 * b * t + c * t ^ 2 = 0)).card : ℤ)
        + (Finset.univ.filter fun t : ZMod p => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0).card = p := by
      exact_mod_cast h1
    by_cases hb : (b : ZMod p) = 0
    · have ha : (a : ZMod p) ≠ 0 := by
        intro ha
        apply hprim
        refine ⟨?_, ?_, ?_⟩ <;> rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] <;> assumption
      have hz : (Finset.univ.filter fun t : ZMod p => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0) = ∅ := by
        ext t
        simp [hb, hc, ha]
      have hl : legendreSym p (b ^ 2 - a * c) = 0 := by
        rw [legendreSym.eq_zero_iff, hD, hb]; ring
      rw [hz] at h1'
      simp only [ne_eq, Finset.card_empty] at h1' ⊢
      rw [hl]
      push_cast at h1' ⊢
      linarith
    · have hl : legendreSym p (b ^ 2 - a * c) = 1 := by
        rw [legendreSym.eq_one_iff p (by rw [hD]; exact pow_ne_zero 2 hb), hD]
        exact ⟨b, sq _⟩
      have h2 : ((2 : ZMod p)) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
        exact hp2 this
      have hone : (Finset.univ.filter fun t : ZMod p => (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0) =
          {-(a : ZMod p) / (2 * b)} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hc]
        constructor
        · intro h
          field_simp
          linear_combination h
        · intro h
          rw [h]; field_simp; ring
      rw [hone] at h1'
      rw [hl]
      simp only [ne_eq, Finset.card_singleton] at h1' ⊢
      push_cast at h1' ⊢
      linarith

/-! ### Lattices in the plane `ℚ²` -/

/-- Helper: the symmetric bilinear form of the space with Gram matrix `S`. -/
def phi (S : Matrix (Fin 2) (Fin 2) ℚ) (x y : Fin 2 → ℚ) : ℚ := x ⬝ᵥ (S *ᵥ y)

/-- Helper: lattice with basis the columns of `B`. -/
def latOf (B : Matrix (Fin 2) (Fin 2) ℚ) : Submodule ℤ (Fin 2 → ℚ) :=
  Submodule.span ℤ (Set.range fun j : Fin 2 => fun i => B i j)

/-- Helper: integer vector as a rational vector. -/
def zc (z : Fin 2 → ℤ) : Fin 2 → ℚ := fun i => (z i : ℚ)

/-- Helper: integer matrix as a rational matrix. -/
def cm (C : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℚ := C.map (fun x : ℤ => (x : ℚ))

/-- Helper: `cm` is multiplicative. -/
theorem cm_mul (C D : Matrix (Fin 2) (Fin 2) ℤ) : cm (C * D) = cm C * cm D := by
  ext i j; simp [cm, Matrix.mul_apply]

/-- Helper: `cm` commutes with transposition. -/
theorem cm_transpose (C : Matrix (Fin 2) (Fin 2) ℤ) : cm Cᵀ = (cm C)ᵀ := by
  ext i j; simp [cm]

/-- Helper: `cm` commutes with the determinant. -/
theorem cm_det (C : Matrix (Fin 2) (Fin 2) ℤ) : (cm C).det = (C.det : ℚ) := by
  simp [Matrix.det_fin_two, cm]

/-- Helper: `cm` is compatible with matrix-vector products. -/
theorem cm_mulVec (C : Matrix (Fin 2) (Fin 2) ℤ) (w : Fin 2 → ℤ) : cm C *ᵥ zc w = zc (C *ᵥ w) := by
  ext i; simp [cm, zc, mulVec, dotProduct]

/-- Helper: `cm` is injective. -/
theorem cm_injective : Function.Injective cm := by
  intro C D h
  ext i j
  have := congrFun (congrFun h i) j
  simpa [cm] using this

/-- Helper: membership in the lattice with basis the columns of `B`. -/
theorem mem_latOf {B : Matrix (Fin 2) (Fin 2) ℚ} {x : Fin 2 → ℚ} :
    x ∈ latOf B ↔ ∃ z : Fin 2 → ℤ, x = B *ᵥ zc z := by
  unfold latOf
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [zc, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    ext i
    simp [zc, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- Helper: the bilinear form on coordinate vectors has Gram matrix $B^{\mathsf T} S B$. -/
theorem phi_mulVec (S B : Matrix (Fin 2) (Fin 2) ℚ) (z w : Fin 2 → ℚ) :
    phi S (B *ᵥ z) (B *ᵥ w) = z ⬝ᵥ ((Bᵀ * S * B) *ᵥ w) := by
  unfold phi
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply]
  ring

/-- **Integral:** `φ(x, y) ∈ ℤ` for all `x, y` in the lattice. -/
def IsIntegralOn (S : Matrix (Fin 2) (Fin 2) ℚ) (Λ : Submodule ℤ (Fin 2 → ℚ)) : Prop :=
  ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, phi S x y = m

/-- **Primitive:** the only integers dividing all values `φ(x, y)` are units. -/
def IsPrimitiveOn (S : Matrix (Fin 2) (Fin 2) ℚ) (Λ : Submodule ℤ (Fin 2 → ℚ)) : Prop :=
  ∀ c : ℤ, (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, phi S x y = c * m) → IsUnit c

/-- **Determinant `d`:** some basis `B` of the lattice has Gram determinant `d`. -/
def HasDet (S : Matrix (Fin 2) (Fin 2) ℚ) (Λ : Submodule ℤ (Fin 2 → ℚ)) (d : ℤ) : Prop :=
  ∃ B : Matrix (Fin 2) (Fin 2) ℚ, B.det ≠ 0 ∧ Λ = latOf B ∧ (Bᵀ * S * B).det = (d : ℚ)

/-- **Primitive integral lattice of determinant `d`.** -/
def IsPrimIntLat (S : Matrix (Fin 2) (Fin 2) ℚ) (Λ : Submodule ℤ (Fin 2 → ℚ)) (d : ℤ) : Prop :=
  IsIntegralOn S Λ ∧ IsPrimitiveOn S Λ ∧ HasDet S Λ d

/-- Helper: the basis vectors lie in the lattice. -/
theorem col_mem_latOf (B : Matrix (Fin 2) (Fin 2) ℚ) (i : Fin 2) :
    B *ᵥ zc (Pi.single i 1) ∈ latOf B := mem_latOf.mpr ⟨_, rfl⟩

/-- Helper: the values of the form on the basis vectors are the entries of the Gram matrix. -/
theorem gram_entry (S B : Matrix (Fin 2) (Fin 2) ℚ) (i j : Fin 2) :
    phi S (B *ᵥ zc (Pi.single i 1)) (B *ᵥ zc (Pi.single j 1)) = (Bᵀ * S * B) i j := by
  rw [phi_mulVec]
  simp [zc, mulVec, dotProduct, Pi.single_apply]

/-- Helper: the form is integral on the lattice with basis `B` iff the Gram matrix $B^{\mathsf T} S B$ is an integer matrix `H`. -/
theorem integral_iff (S B : Matrix (Fin 2) (Fin 2) ℚ) :
    IsIntegralOn S (latOf B) ↔ ∃ H : Matrix (Fin 2) (Fin 2) ℤ, Bᵀ * S * B = cm H := by
  constructor
  · intro h
    have : ∀ i j, ∃ m : ℤ, (Bᵀ * S * B) i j = m := fun i j => by
      rw [← gram_entry]; exact h _ (col_mem_latOf B i) _ (col_mem_latOf B j)
    choose H hH using this
    exact ⟨H, by ext i j; rw [hH i j]; rfl⟩
  · rintro ⟨H, hH⟩ x hx y hy
    obtain ⟨z, rfl⟩ := mem_latOf.mp hx
    obtain ⟨w, rfl⟩ := mem_latOf.mp hy
    refine ⟨z ⬝ᵥ (H *ᵥ w), ?_⟩
    rw [phi_mulVec, hH, cm_mulVec]
    simp [zc, dotProduct]

/-- Helper: for the lattice with basis `B` and integral Gram matrix `H`, primitivity of the form is the statement that the entries of `H` have no common non-unit divisor. -/
theorem primitive_iff (S B : Matrix (Fin 2) (Fin 2) ℚ) (H : Matrix (Fin 2) (Fin 2) ℤ)
    (hH : Bᵀ * S * B = cm H) :
    IsPrimitiveOn S (latOf B) ↔ ∀ c : ℤ, (∀ i j, c ∣ H i j) → IsUnit c := by
  constructor
  · intro h c hc
    apply h c
    rintro x hx y hy
    obtain ⟨z, rfl⟩ := mem_latOf.mp hx
    obtain ⟨w, rfl⟩ := mem_latOf.mp hy
    have : ∀ i j, ∃ k : ℤ, H i j = c * k := hc
    choose k hk using this
    refine ⟨z ⬝ᵥ (Matrix.of k *ᵥ w), ?_⟩
    rw [phi_mulVec, hH]
    have : cm H = (c : ℚ) • cm (Matrix.of k) := by
      ext i j; simp [cm, hk i j]
    rw [this]
    simp [cm, zc, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · intro h c hc
    apply h c
    intro i j
    obtain ⟨m, hm⟩ := hc _ (col_mem_latOf B i) _ (col_mem_latOf B j)
    rw [gram_entry, hH] at hm
    have h2 : (H i j : ℚ) = ((c * m : ℤ) : ℚ) := by simpa [cm] using hm
    exact ⟨m, by exact_mod_cast h2⟩

/-! ### Sublattices of index `p` -/

/-- Helper: membership in the sublattice $B C \mathbb Z^{2}$ of the lattice with basis `B` (`C` an integer matrix). -/
theorem mem_latOf_mul (B : Matrix (Fin 2) (Fin 2) ℚ) (C : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → ℚ) :
    x ∈ latOf (B * cm C) ↔ ∃ w : Fin 2 → ℤ, x = B *ᵥ zc (C *ᵥ w) := by
  rw [mem_latOf]
  simp only [← Matrix.mulVec_mulVec, cm_mulVec]

/-- Helper: sublattices with the same column spans have the same image under `B`. -/
theorem latOf_eq_of_range (B : Matrix (Fin 2) (Fin 2) ℚ) (C₁ C₂ : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ z, (∃ w, z = C₁ *ᵥ w) ↔ (∃ w, z = C₂ *ᵥ w)) : latOf (B * cm C₁) = latOf (B * cm C₂) := by
  ext x
  rw [mem_latOf_mul, mem_latOf_mul]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := (h (C₁ *ᵥ w)).1 ⟨w, rfl⟩
    exact ⟨w', by rw [← hw']⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := (h (C₂ *ᵥ w)).2 ⟨w, rfl⟩
    exact ⟨w', by rw [← hw']⟩

/-- Helper: `zc` is injective. -/
theorem zc_injective : Function.Injective zc := by
  intro z w h
  ext i
  have := congrFun h i
  simpa [zc] using this

/-- Helper: an invertible matrix acts injectively on vectors. -/
theorem mulVec_inj_of_det {B : Matrix (Fin 2) (Fin 2) ℚ} (hB : B.det ≠ 0) {v w : Fin 2 → ℚ}
    (h : B *ᵥ v = B *ᵥ w) : v = w := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have := congrArg (fun u => B⁻¹ *ᵥ u) h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec,
    Matrix.one_mulVec] at this
  exact this

/-- Helper: converse of `latOf_eq_of_range` for invertible `B`. -/
theorem range_eq_of_latOf_eq {B : Matrix (Fin 2) (Fin 2) ℚ} (hB : B.det ≠ 0)
    (C₁ C₂ : Matrix (Fin 2) (Fin 2) ℤ) (h : latOf (B * cm C₁) = latOf (B * cm C₂)) :
    ∀ z, (∃ w, z = C₁ *ᵥ w) ↔ (∃ w, z = C₂ *ᵥ w) := by
  have key : ∀ C₁ C₂ : Matrix (Fin 2) (Fin 2) ℤ, latOf (B * cm C₁) = latOf (B * cm C₂) →
      ∀ z, (∃ w, z = C₁ *ᵥ w) → (∃ w, z = C₂ *ᵥ w) := by
    intro C₁ C₂ h z ⟨w, hw⟩
    have hm : B *ᵥ zc (C₁ *ᵥ w) ∈ latOf (B * cm C₁) := (mem_latOf_mul _ _ _).2 ⟨w, rfl⟩
    rw [h, mem_latOf_mul] at hm
    obtain ⟨w', hw'⟩ := hm
    exact ⟨w', by rw [hw]; exact zc_injective (mulVec_inj_of_det hB hw')⟩
  exact fun z => ⟨key C₁ C₂ h z, key C₂ C₁ h.symm z⟩

/-- Helper: a sublattice `latOf B''` of `latOf B` has `B'' = B * cm C` for an integer matrix `C`. -/
theorem exists_int_of_le {B B'' : Matrix (Fin 2) (Fin 2) ℚ} (h : latOf B'' ≤ latOf B) :
    ∃ C : Matrix (Fin 2) (Fin 2) ℤ, B'' = B * cm C := by
  have hcol : ∀ j, ∃ z : Fin 2 → ℤ, B'' *ᵥ zc (Pi.single j 1) = B *ᵥ zc z := fun j =>
    mem_latOf.mp (h (col_mem_latOf B'' j))
  choose z hz using hcol
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have := congrFun (hz j) i
  simp only [zc, mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] at this
  simp only [cm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply]
  fin_cases j <;> simp at this ⊢ <;> linarith

/-- Helper: Gram matrix of a sublattice. -/
theorem gram_mul (S B : Matrix (Fin 2) (Fin 2) ℚ) (C : Matrix (Fin 2) (Fin 2) ℤ) (H : Matrix (Fin 2) (Fin 2) ℤ)
    (hH : Bᵀ * S * B = cm H) : (B * cm C)ᵀ * S * (B * cm C) = cm (Cᵀ * H * C) := by
  rw [cm_mul, cm_mul, cm_transpose, ← hH, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Helper: the Gram determinant of $B C$ is $\det(C)^{2}\det(H)$ for $B^{\mathsf T} S B = H$. -/
theorem det_gram_mul (S B : Matrix (Fin 2) (Fin 2) ℚ) (C : Matrix (Fin 2) (Fin 2) ℤ) (H : Matrix (Fin 2) (Fin 2) ℤ)
    (hH : Bᵀ * S * B = cm H) : ((B * cm C)ᵀ * S * (B * cm C)).det = (C.det : ℚ) ^ 2 * (H.det : ℚ) := by
  rw [gram_mul S B C H hH, cm_det, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  push_cast; ring

/-! ### Gram matrices of the index-`p` sublattices -/

/-- Helper: the Gram matrix of the sublattice $C_{\mathrm{some}\,t}$ for the form $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$. -/
theorem gram_some (a b c : ℤ) (t : ZMod p) :
    (Cρ p (some t))ᵀ * !![a, b; b, c] * Cρ p (some t) =
      !![a + 2 * b * (t.val : ℤ) + c * (t.val : ℤ) ^ 2, p * (b + c * (t.val : ℤ));
         p * (b + c * (t.val : ℤ)), p ^ 2 * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cρ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Helper: the Gram matrix of the sublattice $C_{\mathrm{none}}$ for the form $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$. -/
theorem gram_none (a b c : ℤ) :
    (Cρ p (none : Option (ZMod p)))ᵀ * !![a, b; b, c] * Cρ p none =
      !![p ^ 2 * a, p * b; p * b, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cρ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Helper: if `m` divides all entries of `G` it divides all entries of $A G B$. -/
theorem dvd_mul3 (m : ℤ) (A G B : Matrix (Fin 2) (Fin 2) ℤ) (h : ∀ i j, m ∣ G i j) (i j : Fin 2) :
    m ∣ (A * G * B) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.dvd_sum fun l _ => ?_
  exact ((h l k).mul_left _).mul_right _

/-- Helper: if `m` divides the four entries then it divides all entries of the $2 \times 2$ matrix. -/
theorem dvd_of_four (m a b c d : ℤ) (h0 : m ∣ a) (h1 : m ∣ b) (h2 : m ∣ c) (h3 : m ∣ d) :
    ∀ i j, m ∣ (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

/-- Helper: if the form vanishes on the line `ρ` modulo $p$, then $p$ divides every entry of the Gram matrix $C_\rho^{\mathsf T} H C_\rho$ of the sublattice. -/
theorem p_dvd_gram_of_not_nonvan (ρ : Option (ZMod p)) (a b c : ℤ) (h : ¬ NonVan a b c ρ) :
    ∀ i j, (p : ℤ) ∣ ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j := by
  cases ρ with
  | none =>
    have hc : (c : ZMod p) = 0 := by simpa [NonVan] using h
    rw [gram_none]
    exact dvd_of_four _ _ _ _ _ (Dvd.intro (p * a) (by ring)) (dvd_mul_right _ _)
      (dvd_mul_right _ _) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc)
  | some t =>
    have hc : (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0 := by simpa [NonVan] using h
    rw [gram_some]
    have h0 : (p : ℤ) ∣ a + 2 * b * (t.val : ℤ) + c * (t.val : ℤ) ^ 2 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]; exact hc
    exact dvd_of_four _ _ _ _ _ h0 (dvd_mul_right _ _) (dvd_mul_right _ _) (Dvd.intro (p * c) (by ring))

/-- Helper: if the primitive form with Gram matrix $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$ does not vanish on `ρ` modulo $p$, then the Gram matrix of the sublattice $C_\rho$ is primitive. -/
theorem gram_primitive_of_nonvan (ρ : Option (ZMod p)) (a b c : ℤ)
    (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) (hnv : NonVan a b c ρ) :
    ∀ m : ℤ, (∀ i j, m ∣ ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j) → IsUnit m := by
  intro m hm
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpm : ¬ (p : ℤ) ∣ m := by
    intro h
    cases ρ with
    | none =>
      have h11 : (p : ℤ) ∣ c := by simpa [gram_none] using h.trans (hm 1 1)
      exact hnv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h11)
    | some t =>
      have h00 : (p : ℤ) ∣ a + 2 * b * (t.val : ℤ) + c * (t.val : ℤ) ^ 2 := by
        simpa [gram_some] using h.trans (hm 0 0)
      apply hnv
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h00
      push_cast at h00
      rw [ZMod.natCast_zmod_val] at h00
      exact h00
  have hcop : IsCoprime m ((p : ℤ) ^ 2) :=
    (hpz.irreducible.coprime_iff_not_dvd.mpr hpm).symm.pow_right
  have hC : (Cρ p ρ).det = p ∨ (Cρ p ρ).det = -p := det_Cρ ρ
  have hid : ((Cρ p ρ).adjugateᵀ * ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) * (Cρ p ρ).adjugate) =
      ((p : ℤ) ^ 2) • !![a, b; b, c] := by
    have : (Cρ p ρ).adjugateᵀ * ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) * (Cρ p ρ).adjugate =
        (Cρ p ρ * (Cρ p ρ).adjugate)ᵀ * !![a, b; b, c] * (Cρ p ρ * (Cρ p ρ).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hd2 : (Cρ p ρ).det ^ 2 = (p : ℤ) ^ 2 := by rcases hC with h | h <;> rw [h] <;> ring
    rw [this, Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← sq, hd2]
  have hdiv : ∀ i j, m ∣ ((p : ℤ) ^ 2) * (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    have := dvd_mul3 m (Cρ p ρ).adjugateᵀ _ (Cρ p ρ).adjugate hm i j
    rw [hid] at this
    simpa using this
  have h00 := hcop.dvd_of_dvd_mul_left (hdiv 0 0)
  have h01 := hcop.dvd_of_dvd_mul_left (hdiv 0 1)
  have h11 := hcop.dvd_of_dvd_mul_left (hdiv 1 1)
  simp at h00 h01 h11
  exact hprim m h00 h01 h11

/-! ### Coordinates of a primitive integral lattice -/

/-- Helper: a primitive integral lattice of determinant `d` has a basis `B` whose Gram matrix is $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$ with $ac - b^{2} = d$ and no common non-unit divisor of $a, b, c$ (`S` symmetric). -/
theorem gamma_data {S : Matrix (Fin 2) (Fin 2) ℚ} (hS : Sᵀ = S) {Γ : Submodule ℤ (Fin 2 → ℚ)} {d : ℤ}
    (h : IsPrimIntLat S Γ d) :
    ∃ (B : Matrix (Fin 2) (Fin 2) ℚ) (a b c : ℤ), B.det ≠ 0 ∧ Γ = latOf B ∧
      Bᵀ * S * B = cm !![a, b; b, c] ∧ a * c - b ^ 2 = d ∧
      (∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) := by
  obtain ⟨hint, hprim, B, hB, rfl, hdet⟩ := h
  obtain ⟨H, hH⟩ := (integral_iff S B).1 hint
  have hsym : (Bᵀ * S * B)ᵀ = Bᵀ * S * B := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hS, Matrix.transpose_transpose, Matrix.mul_assoc]
  have h10 : H 1 0 = H 0 1 := by
    have := congrFun (congrFun hsym 0) 1
    rw [hH] at this
    simp only [Matrix.transpose_apply, cm, Matrix.map_apply] at this
    exact_mod_cast this
  obtain ⟨a, b, c, hHe⟩ : ∃ a b c : ℤ, H = !![a, b; b, c] :=
    ⟨H 0 0, H 0 1, H 1 1, by have := Matrix.eta_fin_two H; rw [h10] at this; exact this⟩
  subst hHe
  refine ⟨B, a, b, c, hB, rfl, hH, ?_, ?_⟩
  · rw [hH, cm_det] at hdet
    simp only [Matrix.det_fin_two_of] at hdet
    have := (Int.cast_inj (α := ℚ)).mp hdet
    rw [← this]; ring
  · intro m ha hb hc
    refine (primitive_iff S B _ hH).1 hprim m ?_
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact hb
    · exact hc

/-! ### Exercise 12 (ii): the sublattices of index `p` -/

/-- Helper: the sublattice of `latOf B` attached to the line `ρ`. -/
def Fl (B : Matrix (Fin 2) (Fin 2) ℚ) (ρ : Option (ZMod p)) : Submodule ℤ (Fin 2 → ℚ) :=
  latOf (B * cm (Cρ p ρ))

/-- Helper: $\det(C_\rho)^{2} = p^{2}$ in $\mathbb Q$. -/
theorem det_Cρ_sq (ρ : Option (ZMod p)) : (((Cρ p ρ).det : ℤ) : ℚ) ^ 2 = (p : ℚ) ^ 2 := by
  rcases det_Cρ ρ with h | h <;> rw [h] <;> push_cast <;> ring

/-- Helper: the sublattice `Fl B ρ` lies in `latOf B`. -/
theorem Fl_le (B : Matrix (Fin 2) (Fin 2) ℚ) (ρ : Option (ZMod p)) : Fl B ρ ≤ latOf B := by
  intro x hx
  obtain ⟨w, rfl⟩ := (mem_latOf_mul B _ x).1 hx
  exact mem_latOf.2 ⟨_, rfl⟩

/-- Helper: **the sublattices of index $p$ of a primitive lattice** $\Gamma = \mathrm{latOf}\ B$ of determinant `d` (Gram matrix $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$) that are primitive and integral of determinant $d p^{2}$ are exactly the lattices `Fl B ρ` with `ρ` a line on which the form does not vanish modulo $p$. -/
theorem Fl_char {S : Matrix (Fin 2) (Fin 2) ℚ} {B : Matrix (Fin 2) (Fin 2) ℚ} {a b c d : ℤ}
    (hB : B.det ≠ 0) (hH : Bᵀ * S * B = cm !![a, b; b, c]) (hd : a * c - b ^ 2 = d) (hd0 : d ≠ 0)
    (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) (Λ : Submodule ℤ (Fin 2 → ℚ)) :
    (Λ ≤ latOf B ∧ IsPrimIntLat S Λ (d * (p : ℤ) ^ 2)) ↔ ∃ ρ : Option (ZMod p), NonVan a b c ρ ∧ Λ = Fl B ρ := by
  have hdetH : ((!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℤ).det : ℚ) = (d : ℚ) := by
    rw [Matrix.det_fin_two_of, ← hd]; push_cast; ring
  constructor
  · rintro ⟨hle, hint, hpr, B'', hB'', rfl, hdet''⟩
    obtain ⟨C, hC⟩ := exists_int_of_le hle
    subst hC
    rw [det_gram_mul S B C _ hH, hdetH] at hdet''
    have hsq : ((C.det : ℤ) : ℚ) ^ 2 = (p : ℚ) ^ 2 := by
      have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      rw [show (((d * (p : ℤ) ^ 2 : ℤ)) : ℚ) = (d : ℚ) * (p : ℚ) ^ 2 by push_cast; ring] at hdet''
      apply mul_right_cancel₀ hd0'
      linear_combination hdet''
    have hsq' : C.det ^ 2 = (p : ℤ) ^ 2 := by exact_mod_cast hsq
    have hC : C.det = p ∨ C.det = -p := sq_eq_sq_iff_eq_or_eq_neg.mp hsq'
    obtain ⟨ρ, hρ⟩ := exists_ρ_of_det C hC
    have hrange : ∀ z, (∃ w, z = C *ᵥ w) ↔ (∃ w, z = Cρ p ρ *ᵥ w) := fun z => by
      rw [hρ, mem_range_Cρ_iff]
    have heq : latOf (B * cm C) = Fl B ρ := latOf_eq_of_range B C _ hrange
    refine ⟨ρ, ?_, heq⟩
    by_contra hn
    have hdv := p_dvd_gram_of_not_nonvan ρ a b c hn
    rw [heq] at hpr
    have hu := (primitive_iff S (B * cm (Cρ p ρ)) _ (gram_mul S B _ _ hH)).1 hpr p hdv
    rcases Int.isUnit_iff.mp hu with h | h
    · have := hp.out.one_lt; omega
    · have := hp.out.one_lt; omega
  · rintro ⟨ρ, hnv, rfl⟩
    refine ⟨Fl_le B ρ, ?_, ?_, B * cm (Cρ p ρ), ?_, rfl, ?_⟩
    · exact (integral_iff S _).2 ⟨_, gram_mul S B _ _ hH⟩
    · exact (primitive_iff S _ _ (gram_mul S B _ _ hH)).2 (gram_primitive_of_nonvan ρ a b c hprim hnv)
    · rw [Matrix.det_mul, cm_det]
      refine mul_ne_zero hB ?_
      intro h0
      have : (((Cρ p ρ).det : ℤ) : ℚ) ^ 2 = 0 := by rw [h0]; ring
      rw [det_Cρ_sq] at this
      have : (p : ℚ) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      exact hp.out.ne_zero (by exact_mod_cast this)
    · rw [det_gram_mul S B _ _ hH, hdetH, det_Cρ_sq]
      push_cast; ring

/-- Helper: the prime $p$ is not a unit of $\mathbb Z$. -/
theorem not_isUnit_p : ¬ IsUnit (p : ℤ) := by
  intro hu
  rcases Int.isUnit_iff.mp hu with h | h
  · have := hp.out.one_lt; omega
  · have := hp.out.one_lt; omega

/-- Helper: distinct lines give distinct sublattices. -/
theorem Fl_injective {B : Matrix (Fin 2) (Fin 2) ℚ} (hB : B.det ≠ 0) :
    Function.Injective (Fl (p := p) B) := by
  intro ρ ρ' h
  have := range_eq_of_latOf_eq hB _ _ h
  exact ρ_inj fun z => by rw [← mem_range_Cρ_iff, ← mem_range_Cρ_iff]; exact this z

open Classical in
/-- Helper: the number of primitive integral sublattices of determinant $d p^{2}$ of $\Gamma$ is $p - \left(\frac{-d}{p}\right)$ (in the coordinates of `gamma_data`). -/
theorem ncard_sub (hp2 : p ≠ 2) {S : Matrix (Fin 2) (Fin 2) ℚ} {B : Matrix (Fin 2) (Fin 2) ℚ} {a b c d : ℤ}
    (hB : B.det ≠ 0) (hH : Bᵀ * S * B = cm !![a, b; b, c]) (hd : a * c - b ^ 2 = d) (hd0 : d ≠ 0)
    (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) :
    (((({Λ | Λ ≤ latOf B ∧ IsPrimIntLat S Λ (d * (p : ℤ) ^ 2)} : Set (Submodule ℤ (Fin 2 → ℚ)))).ncard : ℕ) : ℤ) =
      p - legendreSym p (-d) := by
  have hset : {Λ | Λ ≤ latOf B ∧ IsPrimIntLat S Λ (d * (p : ℤ) ^ 2)} =
      Fl (p := p) B '' (setOf fun ρ : Option (ZMod p) => NonVan a b c ρ) := by
    ext Λ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    rw [Fl_char hB hH hd hd0 hprim Λ]
    constructor
    · rintro ⟨ρ, h1, rfl⟩; exact ⟨ρ, h1, rfl⟩
    · rintro ⟨ρ, h1, rfl⟩; exact ⟨ρ, h1, rfl⟩
  have hfin : (setOf fun ρ : Option (ZMod p) => NonVan a b c ρ) = ↑(Finset.univ.filter fun ρ : Option (ZMod p) => NonVan a b c ρ) := by
    ext ρ; simp only [Finset.coe_filter, Finset.mem_univ, true_and]; rfl
  rw [hset, Set.ncard_image_of_injective _ (Fl_injective hB), hfin, Set.ncard_coe_finset]
  have hprim' : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) := fun ⟨h1, h2, h3⟩ =>
    not_isUnit_p (hprim _ h1 h2 h3)
  rw [card_nonvan hp2 a b c hprim']
  congr 2
  rw [← hd]; ring

/-! ### Exercise 12 (i): the overlattice of determinant `d` -/

/-- Helper: the integrality condition on the overlattice attached to the line `ρ`: all entries of the
Gram matrix of `Cρ` are divisible by `p²`. -/
def PCond (a b c : ℤ) (ρ : Option (ZMod p)) : Prop :=
  ∀ i j, ((p : ℤ) ^ 2) ∣ ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j

/-- Helper: explicit form of `PCond` for the line `some t`. -/
theorem pcond_some_iff (a b c : ℤ) (t : ZMod p) :
    PCond a b c (some t) ↔ ((p : ℤ) ^ 2 ∣ a + 2 * b * (t.val : ℤ) + c * (t.val : ℤ) ^ 2) ∧
      (p : ℤ) ∣ b + c * (t.val : ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold PCond
  rw [gram_some]
  constructor
  · intro h
    refine ⟨by simpa using h 0 0, ?_⟩
    have := h 0 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at this
    rw [sq] at this
    exact (mul_dvd_mul_iff_left hp0).mp this
  · rintro ⟨h0, h1⟩
    refine dvd_of_four _ _ _ _ _ h0 ?_ ?_ (dvd_mul_right _ _)
    · rw [sq]; exact mul_dvd_mul_left _ h1
    · rw [sq]; exact mul_dvd_mul_left _ h1

/-- Helper: explicit form of `PCond` for the line `none`. -/
theorem pcond_none_iff (a b c : ℤ) :
    PCond a b c (none : Option (ZMod p)) ↔ (p : ℤ) ∣ b ∧ (p : ℤ) ^ 2 ∣ c := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold PCond
  rw [gram_none]
  constructor
  · intro h
    refine ⟨?_, by simpa using h 1 1⟩
    have := h 0 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at this
    rw [sq] at this
    exact (mul_dvd_mul_iff_left hp0).mp this
  · rintro ⟨h1, h0⟩
    refine dvd_of_four _ _ _ _ _ (dvd_mul_right _ _) ?_ ?_ h0
    · rw [sq]; exact mul_dvd_mul_left _ h1
    · rw [sq]; exact mul_dvd_mul_left _ h1

/-- Helper: the residue-level kernel condition. -/
def KerEq (a b c : ℤ) (ρ : Option (ZMod p)) : Prop :=
  match ρ with
  | some t => (a : ZMod p) + b * t = 0 ∧ (b : ZMod p) + c * t = 0
  | none => (b : ZMod p) = 0 ∧ (c : ZMod p) = 0

/-- Helper: `PCond` implies the residue-level kernel condition. -/
theorem pcond_kerEq (a b c : ℤ) (ρ : Option (ZMod p)) (h : PCond a b c ρ) : KerEq a b c ρ := by
  cases ρ with
  | none =>
    obtain ⟨h1, h2⟩ := (pcond_none_iff a b c).1 h
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_⟩
    exact (dvd_pow_self (p : ℤ) two_ne_zero).trans h2
  | some t =>
    obtain ⟨h0, h1⟩ := (pcond_some_iff a b c t).1 h
    have h1' : (b : ZMod p) + c * t = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    have h0' : (a : ZMod p) + 2 * b * t + c * t ^ 2 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((dvd_pow_self (p : ℤ) two_ne_zero).trans h0)
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    refine ⟨?_, h1'⟩
    linear_combination h0' - t * h1'

/-- Helper: two lines satisfying the kernel condition for a form that is not identically zero modulo $p$ coincide. -/
theorem kerEq_unique (a b c : ℤ) (hz : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0))
    {ρ ρ' : Option (ZMod p)} (h : KerEq a b c ρ) (h' : KerEq a b c ρ') : ρ = ρ' := by
  cases ρ with
  | none =>
    cases ρ' with
    | none => rfl
    | some t' =>
      obtain ⟨hb, hc⟩ := h
      obtain ⟨h1, h2⟩ := h'
      exfalso; apply hz
      refine ⟨?_, hb, hc⟩
      rw [hb] at h1; simpa using h1
  | some t =>
    cases ρ' with
    | none =>
      obtain ⟨hb, hc⟩ := h'
      obtain ⟨h1, h2⟩ := h
      exfalso; apply hz
      refine ⟨?_, hb, hc⟩
      rw [hb] at h1; simpa using h1
    | some t' =>
      by_contra hne
      have hne' : t ≠ t' := fun e => hne (by rw [e])
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h1', h2'⟩ := h'
      have hc : (c : ZMod p) = 0 := by
        have : (c : ZMod p) * (t - t') = 0 := by linear_combination h2 - h2'
        exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne')
      have hb : (b : ZMod p) = 0 := by rw [hc] at h2; simpa using h2
      have ha : (a : ZMod p) = 0 := by rw [hb] at h1; simpa using h1
      exact hz ⟨ha, hb, hc⟩

/-- Helper: a primitive triple $(a, b, c)$ is not identically zero modulo $p$. -/
theorem not_all_zero (a b c : ℤ) (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) :
    ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0) := by
  rintro ⟨h1, h2, h3⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2 h3
  exact not_isUnit_p (hprim _ h1 h2 h3)

/-- Helper: **uniqueness of the overlattice**: at most one line `ρ` satisfies `PCond`. -/
theorem pcond_unique (a b c : ℤ) (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m)
    {ρ ρ' : Option (ZMod p)} (h : PCond a b c ρ) (h' : PCond a b c ρ') : ρ = ρ' :=
  kerEq_unique a b c (not_all_zero a b c hprim) (pcond_kerEq a b c ρ h) (pcond_kerEq a b c ρ' h')

/-- Helper: **existence of the overlattice**: if $p^{2}$ divides $ac - b^{2}$ and $(a, b, c)$ is primitive, some line satisfies `PCond`. -/
theorem pcond_exists (a b c : ℤ) (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m)
    (hD : (p : ℤ) ^ 2 ∣ a * c - b ^ 2) : ∃ ρ : Option (ZMod p), PCond a b c ρ := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hc : (p : ℤ) ∣ c
  · -- the point at infinity
    refine ⟨none, (pcond_none_iff a b c).2 ?_⟩
    have hpD : (p : ℤ) ∣ a * c - b ^ 2 := (dvd_pow_self (p : ℤ) two_ne_zero).trans hD
    have hb2 : (p : ℤ) ∣ b ^ 2 := by
      have : (p : ℤ) ∣ a * c := hc.mul_left a
      have h2 := dvd_sub this hpD
      simpa using h2
    have hb : (p : ℤ) ∣ b := hpz.dvd_of_dvd_pow hb2
    have ha : ¬ (p : ℤ) ∣ a := fun ha => not_isUnit_p (hprim _ ha hb hc)
    refine ⟨hb, ?_⟩
    obtain ⟨k, hk⟩ := hb
    have h2 : (p : ℤ) ^ 2 ∣ a * c := by
      have : (p : ℤ) ^ 2 ∣ b ^ 2 := by rw [hk]; exact ⟨k ^ 2, by ring⟩
      have h3 := dvd_add hD this
      simpa using h3
    exact hpz.pow_dvd_of_dvd_mul_left 2 ha h2
  · -- an affine point
    set t : ZMod p := -(b : ZMod p) / c with ht
    have hcz : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    refine ⟨some t, (pcond_some_iff a b c t).2 ?_⟩
    set τ : ℤ := (t.val : ℤ) with hτ
    have hy : (p : ℤ) ∣ b + c * τ := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hτ]; push_cast; rw [ZMod.natCast_zmod_val, ht]
      field_simp; ring
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨D', hD'⟩ := hD
    have hid : c * (a + b * τ) = (p : ℤ) ^ 2 * D' + b * ((p : ℤ) * y') := by
      rw [← hy']
      have : (p : ℤ) ^ 2 * D' = a * c - b ^ 2 := hD'.symm
      rw [this]; ring
    have hx : (p : ℤ) ∣ a + b * τ := by
      have h1 : (p : ℤ) ∣ c * (a + b * τ) := by
        rw [hid]
        exact dvd_add ⟨(p : ℤ) * D', by ring⟩ ⟨b * y', by ring⟩
      exact (hpz.dvd_or_dvd h1).resolve_left hc
    obtain ⟨x', hx'⟩ := hx
    have hcx : c * x' = (p : ℤ) * D' + b * y' := by
      apply mul_left_cancel₀ hp0
      rw [hx'] at hid
      linear_combination hid
    have hk : (p : ℤ) ∣ c * (x' + τ * y') := ⟨D' + y' ^ 2, by
      have : c * (x' + τ * y') = (p : ℤ) * D' + y' * (b + c * τ) := by linear_combination hcx
      rw [this, hy']; ring⟩
    obtain ⟨k, hk'⟩ := (hpz.dvd_or_dvd hk).resolve_left hc
    refine ⟨⟨k, ?_⟩, ⟨y', hy'⟩⟩
    have : a + 2 * b * τ + c * τ ^ 2 = (a + b * τ) + τ * (b + c * τ) := by ring
    rw [this, hx', hy', show (p : ℤ) * x' + τ * ((p : ℤ) * y') = (p : ℤ) * (x' + τ * y') by ring, hk']
    ring

/-- Helper: the overlattice `p⁻¹ · (B Cρ)` attached to the line `ρ`. -/
def Gl (B : Matrix (Fin 2) (Fin 2) ℚ) (ρ : Option (ZMod p)) : Submodule ℤ (Fin 2 → ℚ) :=
  latOf (((p : ℚ)⁻¹ • B) * cm (Cρ p ρ))

/-- Helper: the Gram matrix of the overlattice $p^{-1} B C$. -/
theorem gram_Gl (S B : Matrix (Fin 2) (Fin 2) ℚ) (C H : Matrix (Fin 2) (Fin 2) ℤ)
    (hH : Bᵀ * S * B = cm H) :
    (((p : ℚ)⁻¹ • B) * cm C)ᵀ * S * (((p : ℚ)⁻¹ • B) * cm C) = ((p : ℚ)⁻¹) ^ 2 • cm (Cᵀ * H * C) := by
  have e : ((p : ℚ)⁻¹ • B) * cm C = (p : ℚ)⁻¹ • (B * cm C) := Matrix.smul_mul _ _ _
  rw [e, Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [gram_mul S B C H hH, sq]

/-- Helper: primitivity passes to overlattices. -/
theorem prim_mono {S : Matrix (Fin 2) (Fin 2) ℚ} {Λ Γ : Submodule ℤ (Fin 2 → ℚ)} (hle : Λ ≤ Γ)
    (h : IsPrimitiveOn S Λ) : IsPrimitiveOn S Γ := by
  intro m hm
  exact h m fun x hx y hy => hm x (hle hx) y (hle hy)

/-- Helper: the lattice lies in each of the overlattices `Gl B ρ`. -/
theorem le_Gl (B : Matrix (Fin 2) (Fin 2) ℚ) (ρ : Option (ZMod p)) : latOf B ≤ Gl B ρ := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_latOf.1 hx
  obtain ⟨w, hw⟩ := (mem_range_Cρ_iff ρ ((p : ℤ) • z)).2 (by
    cases ρ <;> simp [evf])
  unfold Gl
  refine mem_latOf.2 ⟨w, ?_⟩
  rw [Matrix.smul_mul, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, cm_mulVec, ← hw]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  ext i
  fin_cases i <;> simp [zc, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Helper: if `PCond` holds for `ρ`, the lattice `Gl B ρ` is a primitive integral overlattice of determinant `d`. -/
theorem Gl_char_mpr {S : Matrix (Fin 2) (Fin 2) ℚ} {B : Matrix (Fin 2) (Fin 2) ℚ} {a b c d : ℤ}
    (hB : B.det ≠ 0) (hH : Bᵀ * S * B = cm !![a, b; b, c]) (hD : a * c - b ^ 2 = d * (p : ℤ) ^ 2)
    (hprim : ∀ m : ℤ, m ∣ a → m ∣ b → m ∣ c → IsUnit m) (ρ : Option (ZMod p)) (hP : PCond a b c ρ) :
    latOf B ≤ Gl B ρ ∧ IsPrimIntLat S (Gl B ρ) d := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hΛ : IsPrimitiveOn S (latOf B) :=
    (primitive_iff S B _ hH).2 fun m hm => hprim m (hm 0 0) (hm 0 1) (hm 1 1)
  have hG : ∀ i j, ∃ k : ℤ, ((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j = (p : ℤ) ^ 2 * k := hP
  choose G' hG' using hG
  have hgram : (((p : ℚ)⁻¹ • B) * cm (Cρ p ρ))ᵀ * S * (((p : ℚ)⁻¹ • B) * cm (Cρ p ρ)) =
      cm (Matrix.of G') := by
    rw [gram_Gl S B _ _ hH]
    ext i j
    simp only [Matrix.smul_apply, cm, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
    have := hG' i j
    have h2 : (((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j : ℚ) = (p : ℚ) ^ 2 * G' i j := by
      exact_mod_cast this
    rw [h2]; field_simp
  refine ⟨le_Gl B ρ, (integral_iff S _).2 ⟨Matrix.of G', hgram⟩, prim_mono (le_Gl B ρ) hΛ,
    ((p : ℚ)⁻¹ • B) * cm (Cρ p ρ), ?_, rfl, ?_⟩
  · have hC : ((Cρ p ρ).det : ℚ) ≠ 0 := by
      intro h0
      have : (((Cρ p ρ).det : ℤ) : ℚ) ^ 2 = 0 := by rw [h0]; ring
      rw [det_Cρ_sq] at this
      exact hp0 (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [Matrix.det_mul, Matrix.det_smul, cm_det]
    simp [hp0, hB, hC]
  · rw [gram_Gl S B _ _ hH, Matrix.det_smul, cm_det, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_fin_two_of]
    have hD' : (a : ℚ) * c - (b : ℚ) * b = (d : ℚ) * (p : ℚ) ^ 2 := by exact_mod_cast (by linear_combination hD : a * c - b * b = d * (p : ℤ) ^ 2)
    have := det_Cρ_sq (p := p) ρ
    push_cast
    simp only [Fintype.card_fin]
    field_simp
    have h3 : ((Cρ p ρ).map fun x : ℤ => (x : ℚ)).det = ((Cρ p ρ).det : ℚ) := cm_det _
    rw [h3, this]
    linear_combination (p : ℚ) ^ 2 * hD'

/-- Helper: membership in `Gl B ρ`. -/
theorem mem_Gl (B : Matrix (Fin 2) (Fin 2) ℚ) (ρ : Option (ZMod p)) (x : Fin 2 → ℚ) :
    x ∈ Gl B ρ ↔ ∃ w : Fin 2 → ℤ, x = (p : ℚ)⁻¹ • (B *ᵥ zc (Cρ p ρ *ᵥ w)) := by
  unfold Gl
  rw [mem_latOf]
  simp only [Matrix.smul_mul, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, cm_mulVec]

/-- Helper: `zc` commutes with negation. -/
theorem zc_neg (v : Fin 2 → ℤ) : zc (-v) = -zc v := by
  ext i; simp [zc]

/-- Helper: $\det(\operatorname{adj} C) = \det C$ for $2 \times 2$ matrices. -/
theorem det_adj (C : Matrix (Fin 2) (Fin 2) ℤ) : C.adjugate.det = C.det := by
  simp [Matrix.adjugate_fin_two, Matrix.det_fin_two]; ring

/-- Helper: `cm` of a scalar matrix. -/
theorem cm_det_smul_one (C : Matrix (Fin 2) (Fin 2) ℤ) : cm (C.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) =
    (C.det : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  simp only [cm, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Helper: every primitive integral overlattice of determinant `d` of the lattice with basis `B` is `Gl B ρ` for a line `ρ` with `PCond`. -/
theorem Gl_char_mp {S : Matrix (Fin 2) (Fin 2) ℚ} {B : Matrix (Fin 2) (Fin 2) ℚ} {a b c d : ℤ}
    (hH : Bᵀ * S * B = cm !![a, b; b, c]) (hD : a * c - b ^ 2 = d * (p : ℤ) ^ 2) (hd0 : d ≠ 0)
    (Γ : Submodule ℤ (Fin 2 → ℚ)) (hle : latOf B ≤ Γ) (hΓ : IsPrimIntLat S Γ d) :
    ∃ ρ : Option (ZMod p), PCond a b c ρ ∧ Γ = Gl B ρ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hintΓ := hΓ.1
  obtain ⟨-, -, B'', hB'', rfl, hdet''⟩ := hΓ
  obtain ⟨C, hC⟩ := exists_int_of_le hle
  obtain ⟨H'', hH''⟩ := (integral_iff S B'').1 hintΓ
  have hdetH'' : (H''.det : ℚ) = d := by rw [← cm_det, ← hH'']; exact hdet''
  have hdet1 : (Bᵀ * S * B).det = (C.det : ℚ) ^ 2 * (H''.det : ℚ) := by
    rw [hC]; exact det_gram_mul S B'' C H'' hH''
  have hdet2 : (Bᵀ * S * B).det = (d : ℚ) * (p : ℚ) ^ 2 := by
    rw [hH, cm_det, Matrix.det_fin_two_of]
    have : ((a * c - b * b : ℤ) : ℚ) = ((d * (p : ℤ) ^ 2 : ℤ) : ℚ) := by
      congr 1; linear_combination hD
    rw [this]; push_cast; ring
  have hsq : ((C.det : ℤ) : ℚ) ^ 2 = (p : ℚ) ^ 2 := by
    have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    apply mul_right_cancel₀ hd0'
    rw [hdetH''] at hdet1
    linear_combination hdet1.symm.trans hdet2
  have hsq' : C.det ^ 2 = (p : ℤ) ^ 2 := by exact_mod_cast hsq
  have hCd : C.det = p ∨ C.det = -p := sq_eq_sq_iff_eq_or_eq_neg.mp hsq'
  have hσ : (C.det : ℚ) = p ∨ (C.det : ℚ) = -p := by
    rcases hCd with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hσ0 : (C.det : ℚ) ≠ 0 := by
    rcases hσ with h | h <;> rw [h]
    · exact hp0
    · exact neg_ne_zero.mpr hp0
  have hBadj : B * cm C.adjugate = (C.det : ℚ) • B'' := by
    rw [hC, Matrix.mul_assoc, ← cm_mul, Matrix.mul_adjugate, cm_det_smul_one, Matrix.mul_smul, Matrix.mul_one]
  have hkey : ∀ z : Fin 2 → ℤ, B'' *ᵥ zc z = (C.det : ℚ)⁻¹ • (B *ᵥ zc (C.adjugate *ᵥ z)) := by
    intro z
    rw [← cm_mulVec, Matrix.mulVec_mulVec, hBadj, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hσ0,
      one_smul]
  obtain ⟨ρ, hρ⟩ := exists_ρ_of_det C.adjugate (by rw [det_adj]; exact hCd)
  have hΓeq : latOf B'' = Gl B ρ := by
    ext x
    rw [mem_latOf, mem_Gl]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := (mem_range_Cρ_iff ρ (C.adjugate *ᵥ z)).2 ((hρ _).1 ⟨z, rfl⟩)
      rw [hkey]
      rcases hσ with h | h
      · exact ⟨w, by rw [h, ← hw]⟩
      · refine ⟨-w, ?_⟩
        rw [h, Matrix.mulVec_neg, ← hw, zc_neg, Matrix.mulVec_neg]
        simp only [inv_neg, neg_smul, smul_neg, neg_neg]
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hρ (Cρ p ρ *ᵥ w)).2 ((mem_range_Cρ_iff ρ _).1 ⟨w, rfl⟩)
      rcases hσ with h | h
      · exact ⟨z, by rw [hkey, h, ← hz]⟩
      · refine ⟨-z, ?_⟩
        rw [hkey, h, Matrix.mulVec_neg, ← hz, zc_neg, Matrix.mulVec_neg]
        simp only [inv_neg, neg_smul, smul_neg, neg_neg]
  refine ⟨ρ, ?_, hΓeq⟩
  rw [hΓeq] at hintΓ
  obtain ⟨H₂, hH₂⟩ := (integral_iff S _).1 hintΓ
  rw [gram_Gl S B _ _ hH] at hH₂
  intro i j
  have := congrFun (congrFun hH₂ i) j
  simp only [Matrix.smul_apply, cm, Matrix.map_apply, smul_eq_mul] at this
  refine ⟨H₂ i j, ?_⟩
  have h2 : (((Cρ p ρ)ᵀ * !![a, b; b, c] * Cρ p ρ) i j : ℚ) = ((p : ℚ) ^ 2 * H₂ i j : ℚ) := by
    field_simp at this
    linear_combination this
  exact_mod_cast h2

/-- Helper: the integer `d` of a regular primitive lattice of determinant $d p^{2}$ is non-zero. -/
theorem d_ne_zero {S B : Matrix (Fin 2) (Fin 2) ℚ} {a b c d : ℤ} (hSd : S.det ≠ 0) (hB : B.det ≠ 0)
    (hH : Bᵀ * S * B = cm !![a, b; b, c]) (hD : a * c - b ^ 2 = d * (p : ℤ) ^ 2) : d ≠ 0 := by
  intro h0
  have h1 : (Bᵀ * S * B).det = 0 := by
    rw [hH, cm_det, Matrix.det_fin_two_of]
    have : a * c - b * b = 0 := by rw [h0] at hD; linear_combination hD
    simp [this]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  exact mul_ne_zero (mul_ne_zero hB hSd) hB h1

/-- **Cassels, Ch. 9, Example 12 (i)** (p. 164): *the unique overlattice of determinant $d$.* The plane is
$V = \mathbb Q^{2}$ with the regular symmetric form $\varphi(x, y) = x^{\mathsf T} S y$ (`S`, `hS : Sᵀ = S`,
`hSd : S.det ≠ 0`; every regular $2$-dimensional quadratic space over $\mathbb Q$ is of this form). A lattice is a
$\mathbb Z$-submodule of $V$ with a basis; `IsPrimIntLat S Λ m` says that $\varphi$ induces on `Λ` a primitive
integral form of determinant `m` (Cassels' conventions: integral means $\varphi(\Lambda, \Lambda) \subseteq \mathbb Z$,
primitive means that the values $\varphi(x, y)$ have no common non-unit divisor, the determinant is that of the Gram
matrix in a basis). If $\varphi$ induces a primitive integral form of determinant $d p^{2}$ on `Λ` ($p$ a prime,
$d$ an integer), then there is exactly one lattice $\Gamma \supseteq \Lambda$ on which $\varphi$ induces a primitive
integral form of determinant $d$. (*Update:* the proof does not use that $p$ is odd, as the book assumes.) -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (i), p. 164"]
theorem ex12_i {S : Matrix (Fin 2) (Fin 2) ℚ} (hS : Sᵀ = S) (hSd : S.det ≠ 0) {d : ℤ}
    {Λ : Submodule ℤ (Fin 2 → ℚ)} (hΛ : IsPrimIntLat S Λ (d * (p : ℤ) ^ 2)) :
    ∃! Γ : Submodule ℤ (Fin 2 → ℚ), Λ ≤ Γ ∧ IsPrimIntLat S Γ d := by
  obtain ⟨B, a, b, c, hB, rfl, hH, hD, hprim⟩ := gamma_data hS hΛ
  have hd0 : d ≠ 0 := d_ne_zero hSd hB hH hD
  obtain ⟨ρ, hρ⟩ := pcond_exists a b c hprim (by rw [hD]; exact dvd_mul_left _ _)
  refine ⟨Gl B ρ, Gl_char_mpr hB hH hD hprim ρ hρ, ?_⟩
  rintro Γ' ⟨hle, hΓ'⟩
  obtain ⟨ρ', hP', rfl⟩ := Gl_char_mp hH hD hd0 Γ' hle hΓ'
  rw [pcond_unique a b c hprim hP' hρ]

/-- **Cassels, Ch. 9, Example 12 (ii)** (p. 164): *the number of sublattices of index $p$.* In the setting of
`ex12_i` ($S$ symmetric and regular, $p$ an odd prime), let `Γ` be a lattice on which $\varphi$ induces a primitive
integral form of determinant $d$. The number $N$ of lattices $\Lambda \subseteq \Gamma$ on which $\varphi$ induces a
primitive integral form of determinant $d p^{2}$ is $N = p - \left(\frac{-d}{p}\right)$, where
$\left(\frac{-d}{p}\right)$ is the Legendre symbol (`legendreSym p (-d)`; $0$ if $p \mid d$, $+1$ if $-d$ is a non-zero
square modulo $p$, $-1$ otherwise). The set is finite (its cardinality `Set.ncard` is positive).
*Reconstruction:* the displayed formula is garbled in the machine-read text; $N = p - (-d/p)$ is reconstructed from the
proof ($p + 1$ sublattices of index $p$, of which exactly $1 + (-d/p)$ give a form that is divisible by $p$) and was
checked by brute-force enumeration for $p \in \{3, 5, 7\}$ and all primitive forms with entries in $[-6, 6]$. -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (ii), p. 164"]
theorem ex12_ii (hp2 : p ≠ 2) {S : Matrix (Fin 2) (Fin 2) ℚ} (hS : Sᵀ = S) (hSd : S.det ≠ 0) {d : ℤ}
    {Γ : Submodule ℤ (Fin 2 → ℚ)} (hΓ : IsPrimIntLat S Γ d) :
    ((({Λ | Λ ≤ Γ ∧ IsPrimIntLat S Λ (d * (p : ℤ) ^ 2)} : Set (Submodule ℤ (Fin 2 → ℚ))).ncard : ℕ) : ℤ) =
      p - legendreSym p (-d) := by
  obtain ⟨B, a, b, c, hB, rfl, hH, hD, hprim⟩ := gamma_data hS hΓ
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * S * B).det = 0 := by
      rw [hH, cm_det, Matrix.det_fin_two_of]
      have : a * c - b * b = 0 := by rw [h0] at hD; linear_combination hD
      simp [this]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    exact mul_ne_zero (mul_ne_zero hB hSd) hB h1
  exact ncard_sub hp2 hB hH hD hd0 hprim

/-! ### Exercise 12 (iii): proper classes of binary forms -/

/-- Helper: for $\det V = 1$ the adjugate is the inverse. -/
theorem adj_mul_self (V : Matrix (Fin 2) (Fin 2) ℤ) (hV : V.det = 1) :
    V * V.adjugate = 1 ∧ V.adjugate * V = 1 := by
  rw [Matrix.mul_adjugate, Matrix.adjugate_mul, hV]; simp

/-- Helper: an integral matrix of determinant `p` factors as `Cρ * V` with `V` of determinant `1`. -/
theorem exists_ρ_mul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = p) :
    ∃ (ρ : Option (ZMod p)) (V : Matrix (Fin 2) (Fin 2) ℤ), V.det = 1 ∧ M = Cρ p ρ * V := by
  obtain ⟨ρ, hρ⟩ := exists_ρ_of_det M (Or.inl hM)
  have hcol : ∀ j : Fin 2, ∃ w : Fin 2 → ℤ, M *ᵥ Pi.single j 1 = Cρ p ρ *ᵥ w := fun j =>
    (mem_range_Cρ_iff ρ _).2 ((hρ _).1 ⟨Pi.single j 1, rfl⟩)
  choose w hw using hcol
  refine ⟨ρ, Matrix.of fun i j => w j i, ?_, ?_⟩
  · have hMV : M = Cρ p ρ * Matrix.of fun i j => w j i := by
      ext i j
      have := congrFun (hw j) i
      fin_cases j <;> simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] using this
    have h2 := congrArg Matrix.det hMV
    rw [hM, Matrix.det_mul, det_Cρ'] at h2
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact (mul_left_cancel₀ hp0 (by linarith : (p : ℤ) * 1 = p * (Matrix.of fun i j => w j i).det)).symm
  · ext i j
    have := congrFun (hw j) i
    fin_cases j <;> simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] using this

/-- **Primitive binary forms of determinant `m`** as symmetric Gram matrices (Cassels' `(f_{ij})`). -/
def PrimMat (m : ℤ) : Type :=
  {H : Matrix (Fin 2) (Fin 2) ℤ // Hᵀ = H ∧ H.det = m ∧ ∀ k : ℤ, (∀ i j, k ∣ H i j) → IsUnit k}

/-- **Proper equivalence** of Gram matrices: `Uᵀ H U = H'` with `U` of determinant `1`. -/
def SLRel (H H' : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ Uᵀ * H * U = H'

/-- Helper: reflexivity of proper equivalence of Gram matrices. -/
theorem SLRel.refl (H : Matrix (Fin 2) (Fin 2) ℤ) : SLRel H H := ⟨1, by simp, by simp⟩

/-- Helper: symmetry of proper equivalence of Gram matrices. -/
theorem SLRel.symm {H H' : Matrix (Fin 2) (Fin 2) ℤ} (h : SLRel H H') : SLRel H' H := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨h1, h2⟩ := adj_mul_self U hU
  refine ⟨U.adjugate, ?_, ?_⟩
  · rw [det_adj]; exact hU
  · calc U.adjugateᵀ * (Uᵀ * H * U) * U.adjugate = (U * U.adjugate)ᵀ * H * (U * U.adjugate) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = H := by rw [h1]; simp

/-- Helper: transitivity of proper equivalence of Gram matrices. -/
theorem SLRel.trans {H H' H'' : Matrix (Fin 2) (Fin 2) ℤ} (h : SLRel H H') (h' : SLRel H' H'') :
    SLRel H H'' := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨U', hU', rfl⟩ := h'
  refine ⟨U * U', by rw [Matrix.det_mul, hU, hU', one_mul], ?_⟩
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The setoid of proper equivalence on `PrimMat m`. -/
def slSetoid (m : ℤ) : Setoid (PrimMat m) where
  r H H' := SLRel H.1 H'.1
  iseqv := ⟨fun H => SLRel.refl _, SLRel.symm, SLRel.trans⟩

/-- **The number of proper classes** of primitive forms of determinant `m`: Cassels' `h(m)`. -/
noncomputable def hcl (m : ℤ) : ℕ := Nat.card (Quotient (slSetoid m))

/-- Helper: the line `ρ` is not a zero of the form with Gram matrix `H`. -/
def NV (H : Matrix (Fin 2) (Fin 2) ℤ) (ρ : Option (ZMod p)) : Prop := NonVan (H 0 0) (H 0 1) (H 1 1) ρ

/-- Helper: a symmetric $2 \times 2$ matrix is $\begin{pmatrix} H_{00} & H_{01} \\ H_{01} & H_{11}\end{pmatrix}$. -/
theorem sym_eta {H : Matrix (Fin 2) (Fin 2) ℤ} (h : Hᵀ = H) : H = !![H 0 0, H 0 1; H 0 1, H 1 1] := by
  have h10 : H 1 0 = H 0 1 := by have := congrFun (congrFun h 0) 1; simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10]

/-- Helper: `cm` commutes with integer scalar multiplication. -/
theorem cm_smul (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) : cm (k • M) = (k : ℚ) • cm M := by
  ext i j; simp only [cm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; rfl

/-- Helper: `cm` of the identity. -/
theorem cm_one : cm (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j; simp [cm, Matrix.one_apply]

/-- Helper: the Gram matrix $C_\rho^{\mathsf T} H C_\rho$ of a non-vanishing line is a primitive symmetric matrix of determinant $d p^{2}$. -/
theorem phi_primMat {d : ℤ} (H : PrimMat d) {ρ : Option (ZMod p)} (hρ : NV H.1 ρ) :
    ((Cρ p ρ)ᵀ * H.1 * Cρ p ρ)ᵀ = (Cρ p ρ)ᵀ * H.1 * Cρ p ρ ∧
      ((Cρ p ρ)ᵀ * H.1 * Cρ p ρ).det = d * (p : ℤ) ^ 2 ∧
      ∀ k : ℤ, (∀ i j, k ∣ ((Cρ p ρ)ᵀ * H.1 * Cρ p ρ) i j) → IsUnit k := by
  obtain ⟨hs, hd, hpr⟩ := H.2
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Cρ', hd]; ring
  · have h10 : H.1 1 0 = H.1 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
    have hpr' : ∀ m : ℤ, m ∣ H.1 0 0 → m ∣ H.1 0 1 → m ∣ H.1 1 1 → IsUnit m := by
      intro m h1 h2 h3
      refine hpr m fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact h1
      · exact h2
      · simpa [h10] using h2
      · exact h3
    have := gram_primitive_of_nonvan ρ (H.1 0 0) (H.1 0 1) (H.1 1 1) hpr' hρ
    rwa [← sym_eta hs] at this

/-- Helper: Gram matrix of a scalar multiple of an integer basis. -/
theorem gram_smul_cm (q : ℚ) (X H : Matrix (Fin 2) (Fin 2) ℤ) :
    (q • cm X)ᵀ * cm H * (q • cm X) = (q * q) • cm (Xᵀ * H * X) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, cm_mul, cm_transpose,
    Matrix.mul_assoc]

/-- Helper: `latOf 1` with the Gram matrix `cm H` of a primitive form is a primitive integral lattice. -/
theorem isPrimIntLat_one {d : ℤ} (H : PrimMat d) :
    IsPrimIntLat (cm H.1) (latOf 1) d := by
  obtain ⟨hs, hd, hpr⟩ := H.2
  have hG : (1 : Matrix (Fin 2) (Fin 2) ℚ)ᵀ * cm H.1 * 1 = cm H.1 := by simp
  refine ⟨(integral_iff _ _).2 ⟨H.1, hG⟩, (primitive_iff _ _ H.1 hG).2 hpr, 1, by simp, rfl, ?_⟩
  rw [hG, cm_det, hd]

/-- Helper: **transport of the overlattice**. If $V^{\mathsf T}(C_\rho^{\mathsf T} H C_\rho)V = C_{\rho_2}^{\mathsf T} H_2 C_{\rho_2}$ with $\det V = 1$ (primitive `H`, `H2` of the same non-zero determinant `d`, `ρ` a non-vanishing line of `H`), there is an integer matrix `U` of determinant $1$ with $U^{\mathsf T} H U = H_2$ and $U C_{\rho_2} = C_\rho V$. (Uniqueness of the overlattice, `ex12_i`, applied to the lattice $\mathrm{latOf}(C_\rho)$ in the space $(\mathbb Q^{2}, H)$.) -/
theorem transport {d : ℤ} (hd0 : d ≠ 0) (H H2 : PrimMat d) {ρ ρ2 : Option (ZMod p)} (hρ : NV H.1 ρ)
    (V : Matrix (Fin 2) (Fin 2) ℤ) (hV : V.det = 1)
    (hVeq : Vᵀ * ((Cρ p ρ)ᵀ * H.1 * Cρ p ρ) * V = (Cρ p ρ2)ᵀ * H2.1 * Cρ p ρ2) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ Uᵀ * H.1 * U = H2.1 ∧ U * Cρ p ρ2 = Cρ p ρ * V := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨hs, hd, hpr⟩ := H.2
  obtain ⟨hs2, hd2, hpr2⟩ := H2.2
  set S : Matrix (Fin 2) (Fin 2) ℚ := cm H.1 with hSdef
  have hS : Sᵀ = S := by rw [hSdef, ← cm_transpose, hs]
  have hSd : S.det ≠ 0 := by
    rw [hSdef, cm_det, hd]; exact_mod_cast hd0
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℚ)ᵀ * S * 1 = cm !![H.1 0 0, H.1 0 1; H.1 0 1, H.1 1 1] := by
    rw [← sym_eta hs]; simp [hSdef]
  have hpr' : ∀ m : ℤ, m ∣ H.1 0 0 → m ∣ H.1 0 1 → m ∣ H.1 1 1 → IsUnit m := by
    have h10 : H.1 1 0 = H.1 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
    intro m h1 h2 h3
    refine hpr m fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact h1
    · exact h2
    · simpa [h10] using h2
    · exact h3
  have hdd : H.1 0 0 * H.1 1 1 - H.1 0 1 ^ 2 = d := by
    have h10 : H.1 1 0 = H.1 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
    have hd' := hd
    rw [Matrix.det_fin_two, h10] at hd'
    linear_combination hd'
  -- the sublattice
  have hΛ := (Fl_char (S := S) (B := 1) (a := H.1 0 0) (b := H.1 0 1) (c := H.1 1 1) (d := d)
    (by simp) hone hdd hd0 hpr' (Fl (1 : Matrix (Fin 2) (Fin 2) ℚ) ρ)).2 ⟨ρ, hρ, rfl⟩
  -- the second overlattice
  set A : Matrix (Fin 2) (Fin 2) ℤ := Cρ p ρ * V * (Cρ p ρ2).adjugate with hA
  set W : Matrix (Fin 2) (Fin 2) ℚ := (p : ℚ)⁻¹ • cm A with hW
  have hC2 : (Cρ p ρ2).adjugate * Cρ p ρ2 = (p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.adjugate_mul, det_Cρ']
  have hC2' : Cρ p ρ2 * (Cρ p ρ2).adjugate = (p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.mul_adjugate, det_Cρ']
  have hW1 : W * cm (Cρ p ρ2) = cm (Cρ p ρ * V) := by
    rw [hW, Matrix.smul_mul, ← cm_mul, hA, Matrix.mul_assoc, hC2, Matrix.mul_smul, Matrix.mul_one, cm_smul,
      smul_smul, Int.cast_natCast, inv_mul_cancel₀ hp0, one_smul]
  have hAH : Aᵀ * H.1 * A = (p : ℤ) ^ 2 • H2.1 := by
    have : Aᵀ * H.1 * A = (Cρ p ρ2).adjugateᵀ * (Vᵀ * ((Cρ p ρ)ᵀ * H.1 * Cρ p ρ) * V) * (Cρ p ρ2).adjugate := by
      simp only [hA, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hVeq]
    calc (Cρ p ρ2).adjugateᵀ * ((Cρ p ρ2)ᵀ * H2.1 * Cρ p ρ2) * (Cρ p ρ2).adjugate
        = (Cρ p ρ2 * (Cρ p ρ2).adjugate)ᵀ * H2.1 * (Cρ p ρ2 * (Cρ p ρ2).adjugate) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (p : ℤ) ^ 2 • H2.1 := by
          rw [hC2', Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
            Matrix.mul_smul, Matrix.mul_one, smul_smul, sq]
  have hW2 : Wᵀ * S * W = cm H2.1 := by
    rw [hW, hSdef, gram_smul_cm, hAH, cm_smul]
    push_cast
    rw [smul_smul]
    have : (p : ℚ)⁻¹ * (p : ℚ)⁻¹ * (p : ℚ) ^ 2 = 1 := by field_simp
    rw [this, one_smul]
  have hdetA : A.det = (p : ℤ) * p := by
    rw [hA, Matrix.det_mul, Matrix.det_mul, det_Cρ', hV, det_adj, det_Cρ']; ring
  have hWdet : W.det = 1 := by
    rw [hW, Matrix.det_smul, cm_det, hdetA]
    push_cast
    simp only [Fintype.card_fin]
    field_simp
  have hWΛ : Fl (1 : Matrix (Fin 2) (Fin 2) ℚ) ρ ≤ latOf W := by
    intro x hx
    obtain ⟨w, rfl⟩ := (mem_latOf_mul 1 _ x).1 hx
    obtain ⟨hV1, hV2⟩ := adj_mul_self V hV
    refine mem_latOf.2 ⟨Cρ p ρ2 *ᵥ (V.adjugate *ᵥ w), ?_⟩
    have h3 : W *ᵥ zc (Cρ p ρ2 *ᵥ (V.adjugate *ᵥ w)) = zc (Cρ p ρ *ᵥ w) := by
      rw [← cm_mulVec, Matrix.mulVec_mulVec, hW1, cm_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc, hV1, Matrix.mul_one]
    rw [h3, Matrix.one_mulVec]
  have hWprim : IsPrimIntLat S (latOf W) d := by
    refine ⟨(integral_iff S W).2 ⟨H2.1, hW2⟩, (primitive_iff S W H2.1 hW2).2 hpr2, W, ?_, rfl, ?_⟩
    · rw [hWdet]; exact one_ne_zero
    · rw [hW2, cm_det, hd2]
  have huniq := (ex12_i hS hSd hΛ.2).unique ⟨hΛ.1, isPrimIntLat_one H⟩ ⟨hWΛ, hWprim⟩
  have hcol : ∀ j, ∃ z : Fin 2 → ℤ, W *ᵥ zc (Pi.single j 1) = zc z := by
    intro j
    have : W *ᵥ zc (Pi.single j 1) ∈ latOf (1 : Matrix (Fin 2) (Fin 2) ℚ) := huniq ▸ col_mem_latOf W j
    obtain ⟨z, hz⟩ := mem_latOf.1 this
    exact ⟨z, by rw [hz, Matrix.one_mulVec]⟩
  choose z hz using hcol
  set U : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => z j i with hU
  have hWU : W = cm U := by
    ext i j
    have := congrFun (hz j) i
    fin_cases j <;> simpa [zc, Matrix.mulVec, dotProduct, Fin.sum_univ_two, cm, hU] using this
  refine ⟨U, ?_, ?_, ?_⟩
  · have : (U.det : ℚ) = 1 := by rw [← cm_det, ← hWU, hWdet]
    exact_mod_cast this
  · apply cm_injective
    rw [cm_mul, cm_mul, cm_transpose, ← hWU]
    exact hW2
  · apply cm_injective
    rw [cm_mul, ← hWU, hW1]

/-- Helper: if $U C_{\rho_2} = C_{\rho_1} V$ with $U = \pm 1$ and $\det V = 1$ then $\rho_1 = \rho_2$. -/
theorem rho_eq_of_mul {ρ₁ ρ₂ : Option (ZMod p)} {V U : Matrix (Fin 2) (Fin 2) ℤ} (hV : V.det = 1)
    (hU : U = 1 ∨ U = -1) (h : U * Cρ p ρ₂ = Cρ p ρ₁ * V) : ρ₁ = ρ₂ := by
  obtain ⟨hV1, hV2⟩ := adj_mul_self V hV
  apply ρ_inj
  intro z
  rw [← mem_range_Cρ_iff, ← mem_range_Cρ_iff]
  rcases hU with rfl | rfl
  · rw [Matrix.one_mul] at h
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨V.adjugate *ᵥ w, ?_⟩
      rw [Matrix.mulVec_mulVec, h, Matrix.mul_assoc, hV1, Matrix.mul_one]
    · rintro ⟨w, rfl⟩
      exact ⟨V *ᵥ w, by rw [Matrix.mulVec_mulVec, ← h]⟩
  · rw [Matrix.neg_mul, Matrix.one_mul] at h
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨-(V.adjugate *ᵥ w), ?_⟩
      have h' : Cρ p ρ₂ = -(Cρ p ρ₁ * V) := by rw [← h]; simp
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, h', Matrix.neg_mul, Matrix.neg_mulVec, neg_neg,
        Matrix.mul_assoc, hV1, Matrix.mul_one]
    · rintro ⟨w, rfl⟩
      refine ⟨-(V *ᵥ w), ?_⟩
      have h' : Cρ p ρ₂ = -(Cρ p ρ₁ * V) := by rw [← h]; simp
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, h', Matrix.neg_mulVec]

/-- Helper: cancellation of a non-zero integer scalar in a matrix equation. -/
theorem smul_cancel {k : ℤ} (hk : k ≠ 0) {M N : Matrix (Fin 2) (Fin 2) ℤ} (h : k • M = k • N) : M = N := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hk this

/-- Helper: every primitive form of determinant $d p^{2}$ is $\operatorname{adj}(C_\rho)^{\mathsf T} H' \operatorname{adj}(C_\rho)$ for a primitive form `H'` of determinant `d` with $C_\rho^{\mathsf T} G C_\rho = p^{2} H'$. -/
theorem exists_sub {d : ℤ} (G : PrimMat (d * (p : ℤ) ^ 2)) :
    ∃ (ρ : Option (ZMod p)) (H' : PrimMat d), (Cρ p ρ)ᵀ * G.1 * Cρ p ρ = (p : ℤ) ^ 2 • H'.1 ∧
      G.1 = (Cρ p ρ).adjugateᵀ * H'.1 * (Cρ p ρ).adjugate := by
  obtain ⟨hs, hd, hpr⟩ := G.2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp20 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  have hGe := sym_eta hs
  have h10 : G.1 1 0 = G.1 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  have hD : G.1 0 0 * G.1 1 1 - G.1 0 1 ^ 2 = d * (p : ℤ) ^ 2 := by
    have hd' := hd
    rw [Matrix.det_fin_two, h10] at hd'
    linear_combination hd'
  have hpr' : ∀ m : ℤ, m ∣ G.1 0 0 → m ∣ G.1 0 1 → m ∣ G.1 1 1 → IsUnit m := by
    intro m h1 h2 h3
    refine hpr m fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact h1
    · exact h2
    · simpa [h10] using h2
    · exact h3
  obtain ⟨ρ, hP⟩ := pcond_exists (G.1 0 0) (G.1 0 1) (G.1 1 1) hpr' (by rw [hD]; exact dvd_mul_left _ _)
  have hP' : ∀ i j, (p : ℤ) ^ 2 ∣ ((Cρ p ρ)ᵀ * G.1 * Cρ p ρ) i j := by
    have := hP
    unfold PCond at this
    rw [← hGe] at this
    exact this
  choose Hk hHk using hP'
  set M : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of Hk with hM
  have hCGC : (Cρ p ρ)ᵀ * G.1 * Cρ p ρ = (p : ℤ) ^ 2 • M := by
    ext i j; simp [hHk i j, hM]
  have hC2' : Cρ p ρ * (Cρ p ρ).adjugate = (p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.mul_adjugate, det_Cρ']
  have hGM : (p : ℤ) ^ 2 • G.1 = (p : ℤ) ^ 2 • ((Cρ p ρ).adjugateᵀ * M * (Cρ p ρ).adjugate) := by
    have e1 : (Cρ p ρ).adjugateᵀ * ((Cρ p ρ)ᵀ * G.1 * Cρ p ρ) * (Cρ p ρ).adjugate =
        (Cρ p ρ * (Cρ p ρ).adjugate)ᵀ * G.1 * (Cρ p ρ * (Cρ p ρ).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have eR : ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))ᵀ * G.1 * ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) =
        (p : ℤ) ^ 2 • G.1 := by
      rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one, smul_smul, ← sq]
    calc (p : ℤ) ^ 2 • G.1 = ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))ᵀ * G.1 *
          ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) := eR.symm
      _ = (Cρ p ρ * (Cρ p ρ).adjugate)ᵀ * G.1 * (Cρ p ρ * (Cρ p ρ).adjugate) := by rw [hC2']
      _ = (Cρ p ρ).adjugateᵀ * ((Cρ p ρ)ᵀ * G.1 * Cρ p ρ) * (Cρ p ρ).adjugate := e1.symm
      _ = (Cρ p ρ).adjugateᵀ * ((p : ℤ) ^ 2 • M) * (Cρ p ρ).adjugate := by rw [hCGC]
      _ = (p : ℤ) ^ 2 • ((Cρ p ρ).adjugateᵀ * M * (Cρ p ρ).adjugate) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
  have hGM' : G.1 = (Cρ p ρ).adjugateᵀ * M * (Cρ p ρ).adjugate := smul_cancel hp20 hGM
  have hMs : Mᵀ = M := by
    have : ((p : ℤ) ^ 2 • M)ᵀ = (p : ℤ) ^ 2 • M := by
      rw [← hCGC, Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    rw [Matrix.transpose_smul] at this
    exact smul_cancel hp20 this
  have hMd : M.det = d := by
    have h1 : ((Cρ p ρ)ᵀ * G.1 * Cρ p ρ).det = ((p : ℤ) ^ 2) ^ 2 * M.det := by
      rw [hCGC, Matrix.det_smul]; simp
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Cρ', hd] at h1
    have hp40 : ((p : ℤ) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hp20
    apply mul_left_cancel₀ hp40
    linear_combination -h1
  have hMp : ∀ k : ℤ, (∀ i j, k ∣ M i j) → IsUnit k := by
    intro k hk
    apply hpr k
    intro i j
    rw [hGM']
    exact dvd_mul3 k _ _ _ hk i j
  exact ⟨ρ, ⟨M, hMs, hMd, hMp⟩, hCGC, hGM'⟩

/-- Helper: the lines of non-vanishing for the chosen representative of the class `c`. -/
def Fib (p : ℕ) [Fact p.Prime] (d : ℤ) (c : Quotient (slSetoid d)) : Type :=
  {ρ : Option (ZMod p) // NV (Quotient.out c).1 ρ}

/-- Helper: the set of non-vanishing lines is finite. -/
instance Fib.finite (p : ℕ) [Fact p.Prime] (d : ℤ) (c : Quotient (slSetoid d)) : Finite (Fib p d c) :=
  Subtype.finite

/-- Helper: the form attached to a class and a line. -/
noncomputable def Eobj {d : ℤ} (c : Quotient (slSetoid d)) (ρ : Fib p d c) : PrimMat (d * (p : ℤ) ^ 2) :=
  ⟨(Cρ p ρ.1)ᵀ * (Quotient.out c).1 * Cρ p ρ.1, by
    obtain ⟨h1, h2, h3⟩ := phi_primMat (Quotient.out c) ρ.2
    exact ⟨h1, h2, h3⟩⟩

/-- Helper: the map from pairs (class, line) to proper classes of determinant `d p²`. -/
noncomputable def Emap (p : ℕ) [Fact p.Prime] (d : ℤ) : (Σ c : Quotient (slSetoid d), Fib p d c) →
    Quotient (slSetoid (d * (p : ℤ) ^ 2)) :=
  fun x => Quotient.mk _ (Eobj x.1 x.2)

/-- Helper: the map $(\text{class of } H, \rho) \mapsto [C_\rho^{\mathsf T} H C_\rho]$ is injective, if the proper automorphs of every primitive form of determinant `d` are $\pm 1$. -/
theorem Emap_injective {d : ℤ} (hd0 : d ≠ 0)
    (haut : ∀ H : PrimMat d, ∀ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 → Uᵀ * H.1 * U = H.1 →
      U = 1 ∨ U = -1) : Function.Injective (Emap p d) := by
  rintro ⟨c₁, ρ₁⟩ ⟨c₂, ρ₂⟩ h
  have h' : SLRel (Eobj c₁ ρ₁).1 (Eobj c₂ ρ₂).1 := Quotient.exact h
  obtain ⟨V, hV, hVeq⟩ := h'
  obtain ⟨U, hU, hUH, hUC⟩ := transport hd0 (Quotient.out c₁) (Quotient.out c₂) ρ₁.2 V hV hVeq
  have hc : c₁ = c₂ := by
    have : (Quotient.mk _ (Quotient.out c₁) : Quotient (slSetoid d)) = Quotient.mk _ (Quotient.out c₂) :=
      Quotient.sound ⟨U, hU, hUH⟩
    simpa using this
  subst hc
  have hUpm := haut _ U hU hUH
  have := rho_eq_of_mul hV hUpm hUC
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext this))

/-- Helper: the map $(\text{class of } H, \rho) \mapsto [C_\rho^{\mathsf T} H C_\rho]$ is surjective. -/
theorem Emap_surjective {d : ℤ} : Function.Surjective (Emap p d) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ G =>
  obtain ⟨ρ, H', hCG, hGadj⟩ := exists_sub (p := p) G
  obtain ⟨U, hU, hUH⟩ : SLRel (Quotient.out (Quotient.mk (slSetoid d) H')).1 H'.1 :=
    Quotient.mk_out (s := slSetoid d) H'
  set H₀ := Quotient.out (Quotient.mk (slSetoid d) H') with hH₀
  have hdetM : (U * (Cρ p ρ).adjugate).det = p := by
    rw [Matrix.det_mul, hU, det_adj, det_Cρ', one_mul]
  obtain ⟨ρ₃, V, hV, hMV⟩ := exists_ρ_mul _ hdetM
  have hGV : G.1 = Vᵀ * ((Cρ p ρ₃)ᵀ * H₀.1 * Cρ p ρ₃) * V := by
    rw [hGadj, ← hUH]
    have : (Cρ p ρ).adjugateᵀ * (Uᵀ * H₀.1 * U) * (Cρ p ρ).adjugate =
        (U * (Cρ p ρ).adjugate)ᵀ * H₀.1 * (U * (Cρ p ρ).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hMV]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hNV : NV H₀.1 ρ₃ := by
    by_contra hn
    have hn' := p_dvd_gram_of_not_nonvan ρ₃ (H₀.1 0 0) (H₀.1 0 1) (H₀.1 1 1) hn
    rw [← sym_eta H₀.2.1] at hn'
    apply not_isUnit_p (p := p)
    apply G.2.2.2
    intro i j
    rw [hGV]
    exact dvd_mul3 _ _ _ _ hn' i j
  refine ⟨⟨Quotient.mk _ H', ⟨ρ₃, hNV⟩⟩, ?_⟩
  exact Quotient.sound ⟨V, hV, hGV.symm⟩

/-- Helper: the Legendre symbol is at most $1$. -/
theorem legendreSym_le_one (a : ℤ) : legendreSym p a ≤ 1 := by
  by_cases h : (a : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p a).2 h]; norm_num
  · rcases legendreSym.eq_one_or_neg_one p h with h | h <;> rw [h] <;> norm_num

open Classical in
/-- Helper: the number of non-vanishing lines of a primitive form of determinant `d` is $p - \left(\frac{-d}{p}\right)$. -/
theorem card_fib (hp2 : p ≠ 2) {d : ℤ} (c : Quotient (slSetoid d)) :
    ((Nat.card (Fib p d c) : ℕ) : ℤ) = (p : ℤ) - legendreSym p (-d) := by
  obtain ⟨hs, hd, hpr⟩ := (Quotient.out c).2
  set H := (Quotient.out c).1 with hH
  have h10 : H 1 0 = H 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  have hpr' : ¬ ((p : ℤ) ∣ H 0 0 ∧ (p : ℤ) ∣ H 0 1 ∧ (p : ℤ) ∣ H 1 1) := fun ⟨h1, h2, h3⟩ =>
    not_isUnit_p (hpr _ fun i j => by
      fin_cases i <;> fin_cases j
      · exact h1
      · exact h2
      · simpa [h10] using h2
      · exact h3)
  have hcard : Nat.card (Fib p d c) =
      (Finset.univ.filter fun ρ : Option (ZMod p) => NonVan (H 0 0) (H 0 1) (H 1 1) ρ).card := by
    unfold Fib
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [hcard, card_nonvan hp2 _ _ _ hpr']
  have hd' := hd
  rw [Matrix.det_fin_two, h10] at hd'
  have : H 0 1 ^ 2 - H 0 0 * H 1 1 = -d := by linear_combination -hd'
  rw [this]

/-- **The recursion $h(d p^{2}) = \left(p - \left(\frac{-d}{p}\right)\right) h(d)$ for Gram matrices** (the general form of Cassels' Example 12 (iii)). If the proper automorphs of every primitive form of determinant `d` are $\pm I$, then the number of proper classes of primitive forms of determinant $d p^{2}$ is $\left(p - \left(\frac{-d}{p}\right)\right)$ times that of determinant `d`. Here `p` is an odd prime, `d` a non-zero integer, `haut` the hypothesis on the automorphs. -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iii), pp. 164–165 (general form, proper automorphs ±I)"]
theorem hcl_mul (hp2 : p ≠ 2) {d : ℤ} (hd0 : d ≠ 0)
    (haut : ∀ H : PrimMat d, ∀ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 → Uᵀ * H.1 * U = H.1 →
      U = 1 ∨ U = -1) :
    (hcl (d * (p : ℤ) ^ 2) : ℤ) = ((p : ℤ) - legendreSym p (-d)) * (hcl d : ℤ) := by
  have hbij : Function.Bijective (Emap p d) := ⟨Emap_injective hd0 haut, Emap_surjective⟩
  have hnn : 0 ≤ (p : ℤ) - legendreSym p (-d) := by
    have := legendreSym_le_one (p := p) (-d)
    have := hp.out.one_lt
    omega
  set N : ℕ := ((p : ℤ) - legendreSym p (-d)).toNat with hN
  have hNc : (N : ℤ) = (p : ℤ) - legendreSym p (-d) := Int.toNat_of_nonneg hnn
  have hfib : ∀ c : Quotient (slSetoid d), Nat.card (Fib p d c) = N := fun c => by
    have := card_fib hp2 c
    omega
  have e : (Σ c : Quotient (slSetoid d), Fib p d c) ≃ Quotient (slSetoid (d * (p : ℤ) ^ 2)) :=
    Equiv.ofBijective _ hbij
  have e2 : (Σ c : Quotient (slSetoid d), Fib p d c) ≃ Quotient (slSetoid d) × Fin N :=
    (Equiv.sigmaCongrRight fun c => (Finite.equivFin (Fib p d c)).trans (finCongr (hfib c))).trans
      (Equiv.sigmaEquivProd _ _)
  have h1 : hcl (d * (p : ℤ) ^ 2) = hcl d * N := by
    unfold hcl
    rw [Nat.card_congr e.symm, Nat.card_congr e2, Nat.card_prod, Nat.card_fin]
  rw [h1]
  push_cast
  rw [hNc]; ring

/-! ### The proper automorphs of a primitive binary form are `±I` -/

/-- Helper: three integers without common non-unit divisor have a Bezout relation. -/
theorem bezout3 (a b c : ℤ) (hpr : ∀ k : ℤ, k ∣ a → k ∣ b → k ∣ c → IsUnit k) :
    ∃ x y z : ℤ, a * x + b * y + c * z = 1 := by
  have h1 : IsCoprime (Int.gcd a b : ℤ) c := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hu := hpr (Int.gcd (Int.gcd a b : ℤ) c : ℤ)
      ((Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left a b))
      ((Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right a b)) (Int.gcd_dvd_right _ _)
    rcases Int.isUnit_iff.mp hu with h | h
    · exact_mod_cast h
    · have := Int.natCast_nonneg (Int.gcd (Int.gcd a b : ℤ) c)
      omega
  obtain ⟨r, s, hrs⟩ := h1
  refine ⟨r * Int.gcdA a b, r * Int.gcdB a b, s, ?_⟩
  have := Int.gcd_eq_gcd_ab a b
  linear_combination r * this.symm + hrs

/-- **Cassels, Ch. 9, Example 12 (iii), hint** (p. 165): a primitive classically integral binary form of determinant `d` with $d \ge 2$, $d \ne 3$ has no proper integral automorphs other than $\pm I$. (*Erratum:* the hint says "only the automorphs $\pm I$"; improper automorphs exist, e.g. $\operatorname{diag}(1,-1)$ for $x^{2} + 5y^{2}$, Cassels p. 128. *Update:* the proof gives $d \ge 2$, $d \neq 3$; the printed $d > 3$ misses $d = 2$.) Here `H` is the Gram matrix, `U` the automorph, $\det U = 1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iii), p. 165 (hint: proper automorphs of a primitive form)"]
theorem aut_pm_one {d : ℤ} (hd2 : 2 ≤ d) (hd3 : d ≠ 3) (H : PrimMat d)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hU : U.det = 1) (hUH : Uᵀ * H.1 * U = H.1) :
    U = 1 ∨ U = -1 := by
  obtain ⟨hs, hd, hpr⟩ := H.2
  have h1 : Uᵀ * H.1 = H.1 * U.adjugate := by
    obtain ⟨hm, -⟩ := adj_mul_self U hU
    calc Uᵀ * H.1 = Uᵀ * H.1 * (U * U.adjugate) := by rw [hm, Matrix.mul_one]
      _ = (Uᵀ * H.1 * U) * U.adjugate := by simp only [Matrix.mul_assoc]
      _ = H.1 * U.adjugate := by rw [hUH]
  obtain ⟨a, b, c, hHe⟩ : ∃ a b c : ℤ, H.1 = !![a, b; b, c] := ⟨_, _, _, sym_eta hs⟩
  rw [hHe] at h1 hd hpr
  have hpr' : ∀ k : ℤ, k ∣ a → k ∣ b → k ∣ c → IsUnit k := fun k h1 h2 h3 => hpr k (by
    intro i j
    fin_cases i <;> fin_cases j <;> simpa)
  obtain ⟨u, v, w, z, hUe⟩ : ∃ u v w z : ℤ, U = !![u, v; w, z] := ⟨_, _, _, _, Matrix.eta_fin_two U⟩
  subst hUe
  rw [Matrix.det_fin_two_of] at hU
  rw [Matrix.det_fin_two_of] at hd
  rw [Matrix.adjugate_fin_two_of] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e11 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have E1 : a * (u - z) + 2 * b * w = 0 := by linarith
  have E2 : a * v + c * w = 0 := by linarith
  have E3 : c * (u - z) - 2 * b * v = 0 := by linarith
  obtain ⟨x, y, z', hxyz⟩ := bezout3 a b c hpr'
  set μ : ℤ := -2 * w * x + (u - z) * y + 2 * v * z' with hμ
  have hs' : u - z = μ * b := by
    rw [hμ]; linear_combination (-(u - z)) * hxyz + x * E1 + z' * E3
  have hv' : 2 * v = μ * c := by
    rw [hμ]; linear_combination (-2 * v) * hxyz + 2 * x * E2 - y * E3
  have hw' : -2 * w = μ * a := by
    rw [hμ]; linear_combination (2 * w) * hxyz - y * E1 - 2 * z' * E2
  have key : (u + z) ^ 2 + d * μ ^ 2 = 4 := by
    linear_combination 4 * hU + (u - z + μ * b) * hs' + (2 * w) * hv' - (μ * c) * hw' - μ ^ 2 * hd
  by_cases hμ0 : μ = 0
  · rw [hμ0] at hs' hv' hw'
    have hv0 : v = 0 := by linarith
    have hw0 : w = 0 := by linarith
    have huz : u = z := by linarith
    have hu : u * u = 1 := by rw [hv0, hw0, ← huz] at hU; linarith
    have hU' : (!![u, v; w, z] : Matrix (Fin 2) (Fin 2) ℤ) = !![u, 0; 0, u] := by rw [hv0, hw0, ← huz]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · left; rw [hU', h]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · right; rw [hU', h]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · exfalso
    have hμpos : 0 < μ ^ 2 := by positivity
    have hle : (u + z) ^ 2 ≤ 2 := by nlinarith
    have ht : -1 ≤ u + z ∧ u + z ≤ 1 := by constructor <;> nlinarith
    have hμ1 : μ ^ 2 ≤ 2 := by nlinarith
    have hμ_abs : μ = 1 ∨ μ = -1 := by
      have h1 : -1 ≤ μ ∧ μ ≤ 1 := by constructor <;> nlinarith
      omega
    have hμsq : μ ^ 2 = 1 := by rcases hμ_abs with h | h <;> rw [h] <;> norm_num
    have hbound : d = 4 - (u + z) ^ 2 := by rw [hμsq] at key; linarith
    have : u + z = -1 ∨ u + z = 0 ∨ u + z = 1 := by omega
    rcases this with h | h | h
    · apply hd3; rw [h] at hbound; linarith
    · have h2 : (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b ∧ (2 : ℤ) ∣ c := by
        rcases hμ_abs with h' | h'
        · rw [h'] at hs' hv' hw'
          exact ⟨⟨-w, by linarith⟩, ⟨u, by linarith⟩, ⟨v, by linarith⟩⟩
        · rw [h'] at hs' hv' hw'
          exact ⟨⟨w, by linarith⟩, ⟨-u, by linarith⟩, ⟨-v, by linarith⟩⟩
      have hu2 := hpr' 2 h2.1 h2.2.1 h2.2.2
      rcases Int.isUnit_iff.mp hu2 with h3 | h3 <;> omega
    · apply hd3; rw [h] at hbound; linarith

/-! ### Comparison with the library's proper classes of integral forms -/

/-- Helper: primitive classically integral binary forms of determinant `m` in the library's terms. -/
def LibForms (m : ℤ) : Type :=
  {f : QuadForm ℤ 2 // IsPrimitiveCI f ∧ (casselsMat f).det = m}

/-- Helper: proper equivalence (`ProperIntEquiv`) on `LibForms m`. -/
def libSetoid (m : ℤ) : Setoid (LibForms m) := Setoid.comap Subtype.val (properSetoid 2)

/-- **The number of proper classes of primitive integral binary forms of determinant `m`**
(Cassels' `h(m)`), in the library's terms. -/
noncomputable def hClasses (m : ℤ) : ℕ := Nat.card (Quotient (libSetoid m))

/-- Helper: the Gram-matrix model `PrimMat m` of `LibForms m`. -/
noncomputable def libEquiv (m : ℤ) : LibForms m ≃ PrimMat m where
  toFun f := ⟨casselsMat f.1, casselsMat_isSymm f.1, f.2.2, fun k hk => f.2.1.2 k (fun i j => hk i j)⟩
  invFun M := ⟨ofGram M.1, ⟨⟨M.1, M.2.1, fun x => eval_ofGram M.2.1 x⟩, fun c hc => M.2.2.2 c (fun i j => by
      have := hc i j
      have h2 := congrFun (congrFun (casselsMat_ofGram M.2.1) i) j
      simp only [casselsMat, Matrix.of_apply] at h2
      rwa [h2] at this)⟩, by rw [casselsMat_ofGram M.2.1]; exact M.2.2.1⟩
  left_inv f := Subtype.ext (ofGram_casselsMat f.2.1.1)
  right_inv M := Subtype.ext (casselsMat_ofGram M.2.1)

/-- Helper: proper equivalence of the library's forms is proper equivalence of the Cassels matrices. -/
theorem libRel_iff {m : ℤ} (f g : LibForms m) :
    ProperIntEquiv f.1 g.1 ↔ SLRel (casselsMat f.1) (casselsMat g.1) := by
  constructor
  · rintro ⟨T, hT, h⟩
    exact ⟨T.val, hT, (eval_mulVec_iff_casselsMat f.2.1.1 g.2.1.1 T.val).1 h⟩
  · rintro ⟨U, hU, h⟩
    have h2 : (U 0 0 * U 1 1 - U 0 1 * U 1 0) ^ 2 = 1 := by
      rw [Matrix.det_fin_two] at hU; rw [hU]; norm_num
    refine ⟨QuadFormsKB.Binary.glOf (U 0 0) (U 0 1) (U 1 0) (U 1 1) h2, ?_, ?_⟩
    · simp [Matrix.det_fin_two_of, ← Matrix.det_fin_two U, hU]
    · rw [eval_mulVec_iff_casselsMat f.2.1.1 g.2.1.1, QuadFormsKB.Binary.glOf_val, ← Matrix.eta_fin_two U]
      exact h

/-- Helper: the library's class number `hClasses` equals the Gram-matrix class number `hcl`. -/
theorem hClasses_eq (m : ℤ) : hClasses m = hcl m := by
  unfold hClasses hcl
  exact Nat.card_congr (Quotient.congr (libEquiv m) (fun f g => libRel_iff f g))

/-! ### Exercise 13: properly and improperly primitive classes (the prime `2`) -/

/-- **Improperly primitive** forms of determinant `m` (Gram matrices): primitive with both diagonal entries even. -/
def ImpMat (m : ℤ) : Type := {H : PrimMat m // (2 : ℤ) ∣ H.1 0 0 ∧ (2 : ℤ) ∣ H.1 1 1}

/-- **Properly primitive** forms of determinant `m` (Gram matrices): primitive with an odd diagonal entry. -/
def ProMat (m : ℤ) : Type := {H : PrimMat m // ¬ ((2 : ℤ) ∣ H.1 0 0 ∧ (2 : ℤ) ∣ H.1 1 1)}

/-- Proper equivalence on `ImpMat m`. -/
def impSetoid (m : ℤ) : Setoid (ImpMat m) := Setoid.comap (fun H => H.1) (slSetoid m)

/-- Proper equivalence on `ProMat m`. -/
def proSetoid (m : ℤ) : Setoid (ProMat m) := Setoid.comap (fun H => H.1) (slSetoid m)

/-- Cassels' $h'(m)$: the number of proper classes of improperly primitive forms of determinant `m`. -/
noncomputable def hImp (m : ℤ) : ℕ := Nat.card (Quotient (impSetoid m))

/-- Cassels' $h(m)$ of Example 13: the number of proper classes of properly primitive forms of determinant `m`. -/
noncomputable def hPro (m : ℤ) : ℕ := Nat.card (Quotient (proSetoid m))

/-- Helper: entrywise integer half. -/
def halfM (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => M i j / 2

/-- Helper: if every entry of the integer matrix `M` is even then $2 \cdot \mathrm{halfM}(M) = M$ (`h` says $2 \mid M_{ij}$). -/
theorem two_smul_halfM {M : Matrix (Fin 2) (Fin 2) ℤ} (h : ∀ i j, (2 : ℤ) ∣ M i j) :
    (2 : ℤ) • halfM M = M := by
  ext i j
  simp only [halfM, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel' (h i j)

/-- Helper: the off-diagonal entry of an improperly primitive form is odd. -/
theorem imp_b_odd {m : ℤ} (H : ImpMat m) : ¬ (2 : ℤ) ∣ H.1.1 0 1 := by
  intro h
  have h10 : H.1.1 1 0 = H.1.1 0 1 := by
    have := congrFun (congrFun H.1.2.1 0) 1; simpa using this
  have hu := H.1.2.2.2 2 (by
    intro i j
    fin_cases i <;> fin_cases j
    · exact H.2.1
    · exact h
    · simpa [h10] using h
    · exact H.2.2)
  rcases Int.isUnit_iff.mp hu with h2 | h2 <;> omega

/-- Helper: the sublattice form `θ(H, ρ) = C_ρ^T H C_ρ / 2` of index `2` (`p = 2`). -/
def theta (H : Matrix (Fin 2) (Fin 2) ℤ) (ρ : Option (ZMod 2)) : Matrix (Fin 2) (Fin 2) ℤ :=
  halfM ((Cρ 2 ρ)ᵀ * H * Cρ 2 ρ)

/-- Helper: for an improperly primitive Gram matrix `H` and every line `ρ` modulo $2$, all entries of $C_\rho^{\mathsf T} H C_\rho$ are even. -/
theorem theta_even {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) :
    ∀ i j, (2 : ℤ) ∣ ((Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ) i j := by
  have he := sym_eta H.1.2.1
  have h0 := H.2.1
  have h1 := H.2.2
  rw [he]
  cases ρ with
  | none =>
    rw [gram_none]
    refine dvd_of_four _ _ _ _ _ ?_ ?_ ?_ ?_
    · exact ⟨2 * H.1.1 0 0, by push_cast; ring⟩
    · exact ⟨H.1.1 0 1, by push_cast; ring⟩
    · exact ⟨H.1.1 0 1, by push_cast; ring⟩
    · exact h1
  | some t =>
    rw [gram_some]
    refine dvd_of_four _ _ _ _ _ ?_ ?_ ?_ ?_
    · obtain ⟨u, hu⟩ := h0
      obtain ⟨w, hw⟩ := h1
      exact ⟨u + H.1.1 0 1 * (t.val : ℤ) + w * (t.val : ℤ) ^ 2, by rw [hu, hw]; ring⟩
    · exact ⟨H.1.1 0 1 + H.1.1 1 1 * (t.val : ℤ), by push_cast; ring⟩
    · exact ⟨H.1.1 0 1 + H.1.1 1 1 * (t.val : ℤ), by push_cast; ring⟩
    · exact ⟨2 * H.1.1 1 1, by push_cast; ring⟩

/-- Helper: $2\,\theta(H, \rho) = C_\rho^{\mathsf T} H C_\rho$ for an improperly primitive `H` and a line `ρ`. -/
theorem two_smul_theta {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) :
    (2 : ℤ) • theta H.1.1 ρ = (Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ := two_smul_halfM (theta_even H ρ)

/-- Helper: the sublattice form $\theta(H, \rho)$ of an improperly primitive `H` is symmetric. -/
theorem theta_sym {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) : (theta H.1.1 ρ)ᵀ = theta H.1.1 ρ := by
  have hs : ((Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ)ᵀ = (Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, H.1.2.1, Matrix.transpose_transpose, Matrix.mul_assoc]
  ext i j
  have := congrFun (congrFun hs i) j
  simp only [Matrix.transpose_apply] at this
  simp only [theta, halfM, Matrix.transpose_apply, Matrix.of_apply]
  rw [this]

/-- Helper: $\theta(H, \rho)$ has the same determinant `m` as the improperly primitive form `H`. -/
theorem theta_det {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) : (theta H.1.1 ρ).det = m := by
  have h1 := congrArg Matrix.det (two_smul_theta H ρ)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Cρ', H.1.2.2.1] at h1
  simp only [Fintype.card_fin] at h1
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  push_cast at h1
  linear_combination h1

/-- Helper: $2x / 2 = x$ for an integer `x` (integer division). -/
theorem two_mul_div (x : ℤ) : 2 * x / 2 = x := by omega

/-- Helper: explicit entries of $\theta(H, \mathrm{none})$ for a symmetric Gram matrix `H`. -/
theorem theta_none {H : Matrix (Fin 2) (Fin 2) ℤ} (hs : Hᵀ = H) :
    theta H none = !![2 * H 0 0, H 0 1; H 0 1, H 1 1 / 2] := by
  have h10 : H 1 0 = H 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [theta, halfM, Cρ, Matrix.mul_apply, Fin.sum_univ_two, h10] <;> omega

/-- Helper: explicit entries of $\theta(H, \mathrm{some}\ t)$ for a symmetric Gram matrix `H` and a residue `t` modulo $2$. -/
theorem theta_some {H : Matrix (Fin 2) (Fin 2) ℤ} (hs : Hᵀ = H) (t : ZMod 2) :
    theta H (some t) = !![(H 0 0 + 2 * H 0 1 * (t.val : ℤ) + H 1 1 * (t.val : ℤ) ^ 2) / 2,
        H 0 1 + H 1 1 * (t.val : ℤ); H 0 1 + H 1 1 * (t.val : ℤ), 2 * H 1 1] := by
  have h10 : H 1 0 = H 0 1 := by have := congrFun (congrFun hs 0) 1; simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta, halfM, Cρ, Matrix.mul_apply, Fin.sum_univ_two, h10, -ZMod.natCast_val, -ZMod.intCast_cast]
  all_goals first
    | (congr 1; ring1)
    | ring1
    | (rw [show (2 : ℤ) * H 0 1 + 2 * H 1 1 * (t.val : ℤ) = 2 * (H 0 1 + H 1 1 * (t.val : ℤ)) by ring]
       exact two_mul_div _)

/-- Helper: the off-diagonal entry of $\theta(H, \rho)$ is odd for an improperly primitive `H`. -/
theorem theta_01_odd {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) : ¬ (2 : ℤ) ∣ (theta H.1.1 ρ) 0 1 := by
  have hb := imp_b_odd H
  cases ρ with
  | none => rw [theta_none H.1.2.1]; simpa using hb
  | some t =>
    rw [theta_some H.1.2.1 t]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.head_cons]
    intro h
    exact hb ((dvd_add_left (H.2.2.mul_right _)).mp h)

/-- Helper: a Bezout relation for the entries of a primitive form. -/
theorem primMat_bezout {m : ℤ} (H : PrimMat m) :
    ∃ x y z : ℤ, H.1 0 0 * x + H.1 0 1 * y + H.1 1 1 * z = 1 := by
  apply bezout3
  intro k h1 h2 h3
  have h10 : H.1 1 0 = H.1 0 1 := by have := congrFun (congrFun H.2.1 0) 1; simpa using this
  refine H.2.2.2 k fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · simpa [h10] using h2
  · exact h3

/-- Helper: an odd integer `k` dividing $4$ is a unit. -/
theorem isUnit_of_dvd_four_odd {k : ℤ} (h4 : k ∣ 4) (hk : ¬ (2 : ℤ) ∣ k) : IsUnit k := by
  have h2 : IsCoprime (2 : ℤ) k := Int.prime_two.irreducible.coprime_iff_not_dvd.mpr hk
  have h22 : IsCoprime (4 : ℤ) k := by
    have := h2.pow_left (m := 2)
    simpa using this
  exact h22.isUnit_of_dvd' h4 dvd_rfl

/-- Helper: the sublattice form $\theta(H, \rho)$ of an improperly primitive `H` is primitive (no common non-unit divisor `k` of its entries). -/
theorem theta_prim {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) :
    ∀ k : ℤ, (∀ i j, k ∣ (theta H.1.1 ρ) i j) → IsUnit k := by
  intro k hk
  have hM : ∀ i j, k ∣ ((Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ) i j := by
    intro i j
    rw [← two_smul_theta H ρ]
    simpa using (hk i j).mul_left 2
  have hC : Cρ 2 ρ * (Cρ 2 ρ).adjugate = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.mul_adjugate, det_Cρ']; norm_num
  have hid : (Cρ 2 ρ).adjugateᵀ * ((Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ) * (Cρ 2 ρ).adjugate = (4 : ℤ) • H.1.1 := by
    have : (Cρ 2 ρ).adjugateᵀ * ((Cρ 2 ρ)ᵀ * H.1.1 * Cρ 2 ρ) * (Cρ 2 ρ).adjugate =
        (Cρ 2 ρ * (Cρ 2 ρ).adjugate)ᵀ * H.1.1 * (Cρ 2 ρ * (Cρ 2 ρ).adjugate) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hC, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  have h4H : ∀ i j, k ∣ 4 * H.1.1 i j := by
    intro i j
    have := dvd_mul3 k (Cρ 2 ρ).adjugateᵀ _ (Cρ 2 ρ).adjugate hM i j
    rw [hid] at this
    simpa using this
  obtain ⟨x, y, z, hxyz⟩ := primMat_bezout H.1
  have hk4 : k ∣ 4 := by
    have : (4 : ℤ) = 4 * H.1.1 0 0 * x + 4 * H.1.1 0 1 * y + 4 * H.1.1 1 1 * z := by linear_combination -4 * hxyz
    rw [this]
    exact dvd_add (dvd_add ((h4H 0 0).mul_right x) ((h4H 0 1).mul_right y)) ((h4H 1 1).mul_right z)
  have hodd : ¬ (2 : ℤ) ∣ k := fun h2 => theta_01_odd H ρ (h2.trans (hk 0 1))
  exact isUnit_of_dvd_four_odd hk4 hodd

/-- Helper: `θ(H, ρ)` has an odd diagonal entry (so is properly primitive). -/
def Valid {m : ℤ} (H : ImpMat m) (ρ : Option (ZMod 2)) : Prop :=
  ¬ ((2 : ℤ) ∣ (theta H.1.1 ρ) 0 0 ∧ (2 : ℤ) ∣ (theta H.1.1 ρ) 1 1)

/-- Helper: an improperly primitive Gram matrix `H` has the shape $\begin{pmatrix} 2\alpha & 2\beta + 1 \\ 2\beta + 1 & 2\gamma\end{pmatrix}$ for integers $\alpha, \beta, \gamma$. -/
theorem imp_decomp {m : ℤ} (H : ImpMat m) : ∃ α β γ : ℤ, H.1.1 0 0 = 2 * α ∧ H.1.1 1 1 = 2 * γ ∧
    H.1.1 0 1 = 2 * β + 1 := by
  obtain ⟨α, hα⟩ := H.2.1
  obtain ⟨γ, hγ⟩ := H.2.2
  have hb := imp_b_odd H
  exact ⟨α, (H.1.1 0 1 - 1) / 2, γ, hα, hγ, by omega⟩

/-- Helper: for `H` of the shape of `imp_decomp` (entries `hα hγ hβ`) the line `none` is valid iff $\gamma$ is odd. -/
theorem valid_none_iff {m : ℤ} (H : ImpMat m) {α β γ : ℤ} (hα : H.1.1 0 0 = 2 * α) (hγ : H.1.1 1 1 = 2 * γ)
    (hβ : H.1.1 0 1 = 2 * β + 1) : Valid H none ↔ ¬ (2 : ℤ) ∣ γ := by
  unfold Valid
  rw [theta_none H.1.2.1]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [hα, hγ]
  omega

/-- Helper: for `H` of the shape of `imp_decomp` (entries `hα hγ hβ`) the line `some 0` is valid iff $\alpha$ is odd. -/
theorem valid_zero_iff {m : ℤ} (H : ImpMat m) {α β γ : ℤ} (hα : H.1.1 0 0 = 2 * α) (hγ : H.1.1 1 1 = 2 * γ)
    (hβ : H.1.1 0 1 = 2 * β + 1) : Valid H (some 0) ↔ ¬ (2 : ℤ) ∣ α := by
  unfold Valid
  rw [theta_some H.1.2.1]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons]
  have h0v : (0 : ZMod 2).val = 0 := rfl
  have h0 : ((0 : ZMod 2).val : ℤ) = 0 := by rw [h0v]; rfl
  rw [h0, hα, hγ]
  omega

/-- Helper: for `H` of the shape of `imp_decomp` (entries `hα hγ hβ`) the line `some 1` is valid iff $\alpha + \gamma$ is even. -/
theorem valid_one_iff {m : ℤ} (H : ImpMat m) {α β γ : ℤ} (hα : H.1.1 0 0 = 2 * α) (hγ : H.1.1 1 1 = 2 * γ)
    (hβ : H.1.1 0 1 = 2 * β + 1) : Valid H (some 1) ↔ (2 : ℤ) ∣ α + γ := by
  unfold Valid
  rw [theta_some H.1.2.1]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons]
  have h1v : (1 : ZMod 2).val = 1 := rfl
  have h1 : ((1 : ZMod 2).val : ℤ) = 1 := by rw [h1v]; rfl
  rw [h1, hα, hγ, hβ]
  omega

/-- Helper: the lines modulo $2$ are exactly `none`, `some 0` and `some 1`. -/
theorem option_cases (ρ : Option (ZMod 2)) : ρ = none ∨ ρ = some 0 ∨ ρ = some 1 := by
  rcases ρ with _ | t
  · exact Or.inl rfl
  · right
    have : t = 0 ∨ t = 1 := by
      fin_cases t
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Helper: for an improperly primitive form of determinant `d`, `d ≡ 4 α γ - 1 (mod 8)` in the notation of `imp_decomp`. -/
theorem imp_det_eq {m : ℤ} (H : ImpMat m) {α β γ : ℤ} (hα : H.1.1 0 0 = 2 * α) (hγ : H.1.1 1 1 = 2 * γ)
    (hβ : H.1.1 0 1 = 2 * β + 1) : ∃ e : ℤ, m = 4 * (α * γ) - 8 * e - 1 := by
  have h10 : H.1.1 1 0 = H.1.1 0 1 := by have := congrFun (congrFun H.1.2.1 0) 1; simpa using this
  have hd := H.1.2.2.1
  rw [Matrix.det_fin_two, h10, hα, hγ, hβ] at hd
  obtain ⟨e, he⟩ := Int.even_mul_succ_self β
  refine ⟨e / 1, ?_⟩
  have : β * (β + 1) = e + e := he
  rw [Int.ediv_one]
  nlinarith [hd, this]

/-- Helper: for $d \equiv 3 \pmod 8$ every line modulo $2$ is valid for every improperly primitive form of determinant `d`. -/
theorem valid_three {d : ℤ} (hd : d % 8 = 3) (H : ImpMat d) (ρ : Option (ZMod 2)) : Valid H ρ := by
  obtain ⟨α, β, γ, hα, hγ, hβ⟩ := imp_decomp H
  obtain ⟨e, he⟩ := imp_det_eq H hα hγ hβ
  have hodd : Odd (α * γ) := by
    rw [Int.odd_iff]
    generalize α * γ = n at he
    omega
  obtain ⟨hαo, hγo⟩ := Int.odd_mul.mp hodd
  rw [Int.odd_iff] at hαo hγo
  rcases option_cases ρ with rfl | rfl | rfl
  · rw [valid_none_iff H hα hγ hβ]; omega
  · rw [valid_zero_iff H hα hγ hβ]; omega
  · rw [valid_one_iff H hα hγ hβ]; omega

/-- Helper: for $d \equiv 7 \pmod 8$ every improperly primitive form of determinant `d` has exactly one valid line modulo $2$. -/
theorem valid_seven {d : ℤ} (hd : d % 8 = 7) (H : ImpMat d) : ∃! ρ : Option (ZMod 2), Valid H ρ := by
  obtain ⟨α, β, γ, hα, hγ, hβ⟩ := imp_decomp H
  obtain ⟨e, he⟩ := imp_det_eq H hα hγ hβ
  have hev : Even (α * γ) := by
    rw [Int.even_iff]
    generalize α * γ = n at he
    omega
  rcases Int.even_mul.mp hev with hαe | hγe
  · rw [even_iff_two_dvd] at hαe
    by_cases hγp : (2 : ℤ) ∣ γ
    · refine ⟨some 1, (valid_one_iff H hα hγ hβ).2 (dvd_add hαe hγp), fun ρ hρ => ?_⟩
      rcases option_cases ρ with rfl | rfl | rfl
      · rw [valid_none_iff H hα hγ hβ] at hρ; exact absurd hγp hρ
      · rw [valid_zero_iff H hα hγ hβ] at hρ; exact absurd hαe hρ
      · rfl
    · refine ⟨none, (valid_none_iff H hα hγ hβ).2 hγp, fun ρ hρ => ?_⟩
      rcases option_cases ρ with rfl | rfl | rfl
      · rfl
      · rw [valid_zero_iff H hα hγ hβ] at hρ; exact absurd hαe hρ
      · rw [valid_one_iff H hα hγ hβ] at hρ; omega
  · rw [even_iff_two_dvd] at hγe
    by_cases hαp : (2 : ℤ) ∣ α
    · refine ⟨some 1, (valid_one_iff H hα hγ hβ).2 (dvd_add hαp hγe), fun ρ hρ => ?_⟩
      rcases option_cases ρ with rfl | rfl | rfl
      · rw [valid_none_iff H hα hγ hβ] at hρ; exact absurd hγe hρ
      · rw [valid_zero_iff H hα hγ hβ] at hρ; exact absurd hαp hρ
      · rfl
    · refine ⟨some 0, (valid_zero_iff H hα hγ hβ).2 hαp, fun ρ hρ => ?_⟩
      rcases option_cases ρ with rfl | rfl | rfl
      · rw [valid_none_iff H hα hγ hβ] at hρ; exact absurd hγe hρ
      · rfl
      · rw [valid_one_iff H hα hγ hβ] at hρ; omega

/-! #### The sublattice of a properly primitive form that gives an improperly primitive form -/

/-- Helper: `ρ` is a line for which `C_ρ^T G C_ρ` has all entries even. -/
def Ev (G : Matrix (Fin 2) (Fin 2) ℤ) (ρ : Option (ZMod 2)) : Prop :=
  ∀ i j, (2 : ℤ) ∣ ((Cρ 2 ρ)ᵀ * G * Cρ 2 ρ) i j

/-- Helper: `m` divides all entries of the matrix $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ iff it divides each of $a, b, c, d$. -/
theorem forall_dvd_four_iff (m a b c d : ℤ) :
    (∀ i j, m ∣ (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ) i j) ↔ m ∣ a ∧ m ∣ b ∧ m ∣ c ∧ m ∣ d := by
  constructor
  · intro h
    exact ⟨h 0 0, h 0 1, h 1 0, h 1 1⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact dvd_of_four m a b c d h0 h1 h2 h3

/-- Helper: the Gram matrix $C_{\mathrm{some}\,t}^{\mathsf T} G\, C_{\mathrm{some}\,t}$ of a symmetric `G` modulo the line `some t` ($p = 2$). -/
theorem gramG_some {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (t : ZMod 2) :
    (Cρ 2 (some t))ᵀ * G * Cρ 2 (some t) =
      !![G 0 0 + 2 * G 0 1 * (t.val : ℤ) + G 1 1 * (t.val : ℤ) ^ 2, 2 * (G 0 1 + G 1 1 * (t.val : ℤ));
         2 * (G 0 1 + G 1 1 * (t.val : ℤ)), 4 * G 1 1] := by
  have := gram_some (p := 2) (G 0 0) (G 0 1) (G 1 1) t
  rw [← sym_eta hs] at this
  rw [this]
  norm_num

/-- Helper: the Gram matrix $C_{\mathrm{none}}^{\mathsf T} G\, C_{\mathrm{none}}$ of a symmetric `G` ($p = 2$). -/
theorem gramG_none {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) :
    (Cρ 2 (none : Option (ZMod 2)))ᵀ * G * Cρ 2 none = !![4 * G 0 0, 2 * G 0 1; 2 * G 0 1, G 1 1] := by
  have := gram_none (p := 2) (G 0 0) (G 0 1) (G 1 1)
  rw [← sym_eta hs] at this
  rw [this]
  norm_num

/-- Helper: the sublattice of the line `none` has an even Gram matrix iff $G_{11}$ is even. -/
theorem ev_none_iff {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) : Ev G none ↔ (2 : ℤ) ∣ G 1 1 := by
  unfold Ev
  rw [gramG_none hs, forall_dvd_four_iff]
  constructor
  · rintro ⟨-, -, -, h⟩; exact h
  · intro h
    exact ⟨⟨2 * G 0 0, by ring⟩, ⟨G 0 1, rfl⟩, ⟨G 0 1, rfl⟩, h⟩

/-- Helper: the sublattice of the line `some 0` has an even Gram matrix iff $G_{00}$ is even. -/
theorem ev_zero_iff {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) : Ev G (some 0) ↔ (2 : ℤ) ∣ G 0 0 := by
  unfold Ev
  rw [gramG_some hs, forall_dvd_four_iff]
  have h0v : (0 : ZMod 2).val = 0 := rfl
  rw [h0v]
  constructor
  · rintro ⟨h, -, -, -⟩; simpa using h
  · intro h
    refine ⟨by simpa using h, ⟨G 0 1 + G 1 1 * ((0 : ℕ) : ℤ), rfl⟩, ⟨G 0 1 + G 1 1 * ((0 : ℕ) : ℤ), rfl⟩,
      ⟨2 * G 1 1, by ring⟩⟩

/-- Helper: the sublattice of the line `some 1` has an even Gram matrix iff $G_{00} + G_{11}$ is even. -/
theorem ev_one_iff {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) :
    Ev G (some 1) ↔ (2 : ℤ) ∣ G 0 0 + G 1 1 := by
  unfold Ev
  rw [gramG_some hs, forall_dvd_four_iff]
  have h1v : (1 : ZMod 2).val = 1 := rfl
  rw [h1v]
  constructor
  · rintro ⟨h, -, -, -⟩
    have : (2 : ℤ) ∣ G 0 0 + 2 * G 0 1 * ((1 : ℕ) : ℤ) + G 1 1 * ((1 : ℕ) : ℤ) ^ 2 := h
    simp only [Nat.cast_one, mul_one, one_pow] at this
    omega
  · intro h
    refine ⟨?_, ⟨G 0 1 + G 1 1 * ((1 : ℕ) : ℤ), rfl⟩, ⟨G 0 1 + G 1 1 * ((1 : ℕ) : ℤ), rfl⟩, ⟨2 * G 1 1, by ring⟩⟩
    simp only [Nat.cast_one, mul_one, one_pow]
    omega

/-- Helper: the unique line with `Ev` for a properly primitive form. -/
def rhoOf (G : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod 2) :=
  if (2 : ℤ) ∣ G 0 0 then some 0 else if (2 : ℤ) ∣ G 1 1 then none else some 1

/-- Helper: for a symmetric `G` with an odd diagonal entry (`hpro`) a line `ρ` has an even sublattice Gram matrix iff `ρ = rhoOf G`. -/
theorem ev_iff_rhoOf {G : Matrix (Fin 2) (Fin 2) ℤ} (hs : Gᵀ = G) (hpro : ¬ ((2 : ℤ) ∣ G 0 0 ∧ (2 : ℤ) ∣ G 1 1))
    (ρ : Option (ZMod 2)) : Ev G ρ ↔ ρ = rhoOf G := by
  unfold rhoOf
  rcases option_cases ρ with rfl | rfl | rfl
  · rw [ev_none_iff hs]
    by_cases h0 : (2 : ℤ) ∣ G 0 0
    · have : ¬ (2 : ℤ) ∣ G 1 1 := fun h => hpro ⟨h0, h⟩
      simp [h0, this]
    · by_cases h1 : (2 : ℤ) ∣ G 1 1 <;> simp [h0, h1]
  · rw [ev_zero_iff hs]
    by_cases h0 : (2 : ℤ) ∣ G 0 0
    · simp [h0]
    · simp only [h0, if_false]
      by_cases h1 : (2 : ℤ) ∣ G 1 1 <;> simp [h0, h1]
  · rw [ev_one_iff hs]
    by_cases h0 : (2 : ℤ) ∣ G 0 0
    · have : ¬ (2 : ℤ) ∣ G 1 1 := fun h => hpro ⟨h0, h⟩
      simp [h0]
      omega
    · by_cases h1 : (2 : ℤ) ∣ G 1 1 <;> simp [h0, h1] <;> omega

/-- Helper: $(ac - b^{2}) \bmod 4$ depends only on the residues of $a, b, c$ modulo $4$. -/
theorem det_mod4 (a b c : ℤ) : (a * c - b * b) % 4 = ((a % 4) * (c % 4) - (b % 4) * (b % 4)) % 4 :=
  (Int.ModEq.sub ((Int.mod_modEq a 4).mul (Int.mod_modEq c 4))
    ((Int.mod_modEq b 4).mul (Int.mod_modEq b 4))).symm

/-- Helper: the parity pattern of $(a, b, c)$ when $ac - b^{2} \equiv 3 \pmod 4$: exactly one of $a, c$ even gives $b$ odd and the even one divisible by $4$; both odd gives $b$ even and $4 \mid a + 2b + c$. -/
theorem parity_cases (a b c : ℤ) (h : (a * c - b * b) % 4 = 3) :
    ((2 : ℤ) ∣ a → ¬ (2 : ℤ) ∣ c → ¬ (2 : ℤ) ∣ b ∧ (4 : ℤ) ∣ a) ∧
    (¬ (2 : ℤ) ∣ a → (2 : ℤ) ∣ c → ¬ (2 : ℤ) ∣ b ∧ (4 : ℤ) ∣ c) ∧
    (¬ (2 : ℤ) ∣ a → ¬ (2 : ℤ) ∣ c → (2 : ℤ) ∣ b ∧ (4 : ℤ) ∣ a + 2 * b + c) := by
  rw [det_mod4] at h
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have hc : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rcases hc with hc | hc | hc | hc <;>
    simp only [ha, hb, hc] at h <;> omega

/-- Helper: `ψ(G) = C_{ρ'}^T G C_{ρ'} / 2` with `ρ' = rhoOf G`: the improperly primitive form attached to a
properly primitive form. -/
def psi (G : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  halfM ((Cρ 2 (rhoOf G))ᵀ * G * Cρ 2 (rhoOf G))

/-- Helper: the determinant of a properly primitive Gram matrix in coordinates: $G_{00} G_{11} - G_{01}^{2} = d$. -/
theorem det_ProMat {d : ℤ} (G : ProMat d) : G.1.1 0 0 * G.1.1 1 1 - G.1.1 0 1 * G.1.1 0 1 = d := by
  have h10 : G.1.1 1 0 = G.1.1 0 1 := by have := congrFun (congrFun G.1.2.1 0) 1; simpa using this
  have hd := G.1.2.2.1
  rw [Matrix.det_fin_two, h10] at hd
  exact hd

/-- Helper: the sublattice of the line `rhoOf G` of a properly primitive `G` has an even Gram matrix. -/
theorem ev_rhoOf {d : ℤ} (G : ProMat d) : Ev G.1.1 (rhoOf G.1.1) :=
  (ev_iff_rhoOf G.1.2.1 G.2 _).2 rfl

/-- Helper: $2\,\psi(G) = C_\rho^{\mathsf T} G\, C_\rho$ for $\rho$ = `rhoOf G.1`. -/
theorem two_smul_psi {d : ℤ} (G : ProMat d) :
    (2 : ℤ) • psi G.1.1 = (Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1) :=
  two_smul_halfM (ev_rhoOf G)

/-- Helper: $\psi(G)$ is symmetric. -/
theorem psi_sym {d : ℤ} (G : ProMat d) : (psi G.1.1)ᵀ = psi G.1.1 := by
  have hs : ((Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1))ᵀ =
      (Cρ 2 (rhoOf G.1.1))ᵀ * G.1.1 * Cρ 2 (rhoOf G.1.1) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, G.1.2.1, Matrix.transpose_transpose, Matrix.mul_assoc]
  ext i j
  have := congrFun (congrFun hs i) j
  simp only [Matrix.transpose_apply] at this
  simp only [psi, halfM, Matrix.transpose_apply, Matrix.of_apply]
  rw [this]

/-- Helper: $\psi(G)$ has the same determinant `d` as the properly primitive form `G`. -/
theorem psi_det {d : ℤ} (G : ProMat d) : (psi G.1.1).det = d := by
  have h1 := congrArg Matrix.det (two_smul_psi G)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Cρ', G.1.2.2.1] at h1
  simp only [Fintype.card_fin] at h1
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  push_cast at h1
  linear_combination h1


/-- **Cassels, Ch. 9, Example 12 (iii)** (pp. 164–165): *class numbers of binary forms of determinants $d$ and
$d p^{2}$.* Let $p$ be an odd prime and $d \ge 2$, $d \ne 3$ an integer. Let $h(m)$ (`hClasses m`) be the number
of proper equivalence classes (`ProperIntEquiv`, $\mathrm{SL}_2(\mathbb Z)$-classes) of primitive classically integral
binary forms $f = \sum f_{ij} x_i x_j$ of determinant $\det(f_{ij}) = m$ (`IsPrimitiveCI`, `casselsMat`; these
include both properly and improperly primitive forms and both signs of definiteness). Then
$$h(d p^{2}) = \left(p - \left(\frac{-d}{p}\right)\right) h(d),$$
the factor being the number $N$ of Example 12 (ii) (`ex12_ii`). (*Update:* the hint's hypothesis "$d > 3$" is replaced by
$d \ge 2$, $d \ne 3$, which is what the proof gives; see `aut_pm_one` for the *erratum* "automorphs" versus
"proper automorphs". The cases $d \le 1$ and $d = 3$, asked for in part (iv), are in `Ch9Examples11.lean`
(`ex12_iv_orbits`, `ex12_iv_one`, `ex12_iv_three`, `ex12_iv_square`): the proper automorphs are then not just $\pm I$.) -/
@[kb "cassels1978" "Ch. 9, Ex. 12 (iii), pp. 164–165"]
theorem ex12_iii (hp2 : p ≠ 2) {d : ℤ} (hd2 : 2 ≤ d) (hd3 : d ≠ 3) :
    (hClasses (d * (p : ℤ) ^ 2) : ℤ) = ((p : ℤ) - legendreSym p (-d)) * (hClasses d : ℤ) := by
  rw [hClasses_eq, hClasses_eq]
  exact hcl_mul hp2 (by omega) fun H U hU h => aut_pm_one hd2 hd3 H U hU h

end QuadFormsKB.Siegel.Ch9Ex12
