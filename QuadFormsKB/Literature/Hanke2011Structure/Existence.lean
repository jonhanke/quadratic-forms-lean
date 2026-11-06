/-
# Hanke 2011, Remark 2.11 and Remark 5.8: existence of local forms; unit scaling at $\mathfrak p \nmid 2$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

**Remark 2.11 (p. 12).** "From the proof of Theorem 2.6 we see that a local genus $G_{\mathfrak p}$ with
$\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$ exists for any normalized squareclass $S_{\mathfrak p}$ when
$I(S_{\mathfrak p}) \subseteq h_n\mathcal O_{\mathfrak p}$ both when $n$ is odd, and when $n$ is even and $\mathfrak p \nmid 2$."
Formalized for every Hessian determinant $s$ with $s \in h_n$ (so for normalized and non-normalized squareclasses):

* `remark_2_11_odd`: $n = 2m+1$ odd, any commutative ring $R$, any $s \in 2R$: the form
  $x_0x_{n-1} + x_1x_{n-2} + \cdots + x_{m-1}x_{m+1} + c\,x_m^2$ (`antidiagFormC`) with a suitable $c$ has
  $\det_H = s$; it is primitive when $n \ge 3$ (it has a coefficient $1$). For $n = 1$ a primitive form $cx_0^2$ has $c$
  a unit, so $\det_H = 2c$ is normalized: for $n = 1$ only normalized squareclasses occur
  (`remark_2_11_one`), which is the case the remark covers.
* `remark_2_11_even_nondyadic`: $n \ge 1$, $2 \in R^\times$, any $s \in R$: $\langle 1,\dots,1,s/2^n\rangle$ is primitive with
  $\det_H = s$.

The dyadic even case ($F_{\mathfrak p} = \mathbb Q_2$: existence iff $S \equiv (-1)^{n/2}$ with $I(S) \subseteq \mathcal O$, or
$I(S) \subseteq 4\mathcal O$) is not formalized.

**Remark 5.8 (p. 25), Hasse invariant part.** For $\mathfrak p \nmid 2$ and $n$ odd, unit scaling does not change the
Hasse invariant: $c_{\mathfrak p}(uV) = c_{\mathfrak p}(V)$ for every unit $u \in \mathcal O_{\mathfrak p}^\times$, since
$(u,u)_{\mathfrak p} = 1$ (`remark_5_8_hasse`). With the counting step `LocalGenusData.theorem_5_7_of_bijection`
($\kappa = 1$) this gives $A^*_{\mathfrak p;n}(uS_{\mathfrak p}) = A^*_{\mathfrak p;n}(S_{\mathfrak p})$ and
$B^*_{\mathfrak p;n}(uS_{\mathfrak p}) = B^*_{\mathfrak p;n}(S_{\mathfrak p})$, i.e. the Euler factors depend only on
$\operatorname{ord}_{\mathfrak p}(S_{\mathfrak p})$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.HessianParity
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera

namespace QuadFormsKB.Hanke2011Structure

open Matrix

section Odd

variable {R : Type*} [CommRing R]

/-- The coefficients of $x_0x_{n-1} + x_1x_{n-2} + \cdots$, with $c\,x_m^2$ added when $n = 2m+1$ (0-based indices):
$c_{ij} = 1$ if $j = n-1-i > i$, $c_{mm} = c$, and $0$ otherwise. -/
def antidiagCoeffC (n : ℕ) (c : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i ≤ j ∧ j = Fin.rev i then (if Fin.rev i = i then c else 1) else 0

/-- The form $x_0x_{n-1} + x_1x_{n-2} + \cdots\ (+\,c\,x_m^2$ if $n = 2m+1)$. For $c = 1$ it is `antidiagForm n`. -/
def antidiagFormC (n : ℕ) (c : R) : QuadForm R n where
  coeff := antidiagCoeffC n c
  upper := by
    intro i j hij
    simp only [antidiagCoeffC, of_apply]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h => absurd h.1 (not_le.mpr hij))

theorem antidiagFormC_hessian (n : ℕ) (c : R) :
    (antidiagFormC n c).hessian =
      (Fin.revPerm.permMatrix R) * Matrix.diagonal fun j : Fin n => if Fin.rev j = j then 2 * c else 1 := by
  ext i j
  simp only [QuadForm.hessian, antidiagFormC, antidiagCoeffC, Matrix.add_apply, transpose_apply, of_apply,
    mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
  have hrev : ∀ a b : Fin n, a = Fin.rev b ↔ b = Fin.rev a := fun a b => by
    constructor <;> intro h <;> simp [h]
  by_cases hj : j = Fin.rev i
  · have hi : i = Fin.rev j := (hrev j i).mp hj
    subst hj
    by_cases hii : Fin.rev i = i
    · simp [hii]
      ring
    · have hne : i ≠ Fin.rev i := fun h => hii h.symm
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simp [hlt.le, not_le.mpr hlt, hne, Fin.rev_rev, hii]
      · simp [hlt.le, not_le.mpr hlt, hne, Fin.rev_rev]
  · have hi : ¬ i = Fin.rev j := fun h => hj ((hrev i j).mp h)
    simp [hj, hi, Ne.symm hj]

/-- For $n$ odd, $\det H(\text{antidiagFormC}\ n\ c) = \operatorname{sgn}(\sigma)\cdot 2c$, $\sigma(i) = n-1-i$. -/
theorem antidiagFormC_hessian_det {n : ℕ} (hn : Odd n) (c : R) :
    (antidiagFormC n c).hessian.det = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : R) * (2 * c) := by
  rw [antidiagFormC_hessian, det_mul, det_permutation, det_diagonal]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hcard : (Finset.univ.filter fun j : Fin n => Fin.rev j = j).card = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [Finset.card_eq_one]
    refine ⟨⟨m, by omega⟩, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_rev]
    omega
  rw [hcard, pow_one]

/-- **Remark 2.11, $n$ odd** (Hanke 2011, p. 12). Over any commutative ring $R$ (in the paper
$R = \mathcal O_{\mathfrak p}$, any $\mathfrak p$, dyadic included), for $n$ odd and every $s \in 2R$ (i.e. $s \in h_n$, Lemma 2.5)
there is a form $Q$ in $n$ variables with $\det H(Q) = s$, namely
$x_0x_{n-1} + \cdots + x_{m-1}x_{m+1} + c\,x_m^2$ (`antidiagFormC`); for $n \ge 3$ its coefficient $c_{0,n-1}$ is $1$, so
$Q$ is primitive. -/
@[kb "hanke2011structure" "Rem. 2.11, p. 12 (n odd)"]
theorem remark_2_11_odd {n : ℕ} (hn : Odd n) {s : R} (hs : s ∈ Ideal.span {(2 : R)}) :
    ∃ c : R, (antidiagFormC n c).hessian.det = s := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  set σ : R := (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : R)
  have hσ : σ * σ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
      simp [σ, h]
  refine ⟨σ * t, ?_⟩
  rw [antidiagFormC_hessian_det hn]
  linear_combination (2 * t) * hσ

end Odd

section DVR

variable {R : Type*} [CommRing R]

/-- The form `antidiagFormC n c` is primitive for $n \ge 2$: its coefficient $c_{0,n-1}$ is $1$. -/
theorem isPrimitiveForm_antidiagFormC {n : ℕ} (hn : 2 ≤ n) (c : R) : IsPrimitiveForm (antidiagFormC n c) := by
  rw [IsPrimitiveForm, Ideal.eq_top_iff_one]
  refine Ideal.subset_span ⟨(⟨0, by omega⟩, ⟨n - 1, by omega⟩), ?_⟩
  have h1 : (⟨n - 1, by omega⟩ : Fin n) = Fin.rev ⟨0, by omega⟩ := by ext; simp
  have h2 : Fin.rev (⟨0, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by
    rw [← h1]; intro h; have := congrArg Fin.val h; simp at this; omega
  simp only [antidiagFormC, antidiagCoeffC, of_apply]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Fin.mk_le_mk.mpr (by omega), h1⟩), ite_eq_right_of_eq_false _ _ (eq_false h2)]

/-- **Remark 2.11, $n$ odd, primitive form** (Hanke 2011, p. 12): for $n \ge 3$ odd and every $s \in 2R$ there is a
primitive $R$-valued form in $n$ variables with $\det H = s$. -/
@[kb "hanke2011structure" "Rem. 2.11, p. 12 (n odd)"]
theorem remark_2_11_odd_primitive {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {s : R} (hs : s ∈ Ideal.span {(2 : R)}) :
    ∃ Q : QuadForm R n, IsPrimitiveForm Q ∧ Q.hessian.det = s := by
  obtain ⟨c, hc⟩ := remark_2_11_odd hn hs
  exact ⟨_, isPrimitiveForm_antidiagFormC (by omega) c, hc⟩

/-- **Remark 2.11, $n = 1$** (*clarification*, proposed by the formalization): a primitive form $c\,x_0^2$ in one
variable over a DVR has $c$ a unit, so its Hessian determinant $2c$ has $\operatorname{ord}(\det_H) = \operatorname{ord}(2)$,
i.e. it is normalized. So for $n = 1$ the existence in Remark 2.11 holds exactly for normalized squareclasses (as the
remark says), not for every $S$ with $I(S) \subseteq h_1$. -/
@[kb "hanke2011structure" "Rem. 2.11, p. 12 (n = 1)"]
theorem remark_2_11_one (Q : QuadForm R 1) (hQ : IsPrimitiveForm Q) :
    IsUnit (Q.coeff 0 0) ∧ Q.hessian.det = 2 * Q.coeff 0 0 := by
  refine ⟨?_, ?_⟩
  · have hspan : Set.range (fun p : Fin 1 × Fin 1 => Q.coeff p.1 p.2) = {Q.coeff 0 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff, Prod.exists]
      constructor
      · rintro ⟨i, j, rfl⟩; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      · rintro rfl; exact ⟨0, 0, rfl⟩
    rw [IsPrimitiveForm, hspan, Ideal.span_singleton_eq_top] at hQ
    exact hQ
  · simp [QuadForm.hessian, two_mul]

/-- **Remark 2.11, $n$ even, $\mathfrak p \nmid 2$** (Hanke 2011, p. 12; the formula holds for every $n \ge 1$). If $2$ is a
unit in $R$, then for every $s \in R$ the form $\langle 1,\dots,1,s/2^{k+1}\rangle$ in $k+1$ variables is primitive (for
$k \ge 1$, or $s$ a unit) with Hessian determinant $s$. -/
@[kb "hanke2011structure" "Rem. 2.11, p. 12 (p ∤ 2)"]
theorem remark_2_11_even_nondyadic [IsDomain R] [IsDiscreteValuationRing R] (h2 : IsUnit (2 : R)) {k : ℕ} (hk : 1 ≤ k) (s : R) :
    ∃ Q : QuadForm R (k + 1), IsPrimitiveForm Q ∧ Q.hessian.det = s := by
  obtain ⟨w, hw⟩ := h2.pow (k + 1)
  let d : R := s * ↑w⁻¹
  refine ⟨QuadForm.diag (Function.update (1 : Fin (k + 1) → R) (Fin.last k) d), ?_, ?_⟩
  · rw [IsPrimitiveForm, Ideal.eq_top_iff_one]
    refine Ideal.subset_span ⟨(0, 0), ?_⟩
    have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [QuadForm.diag, Function.update_of_ne h0]
  · rw [LocalDensity.DVR.det_hessian_diag, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one, d]
    rw [← hw, mul_comm s, ← mul_assoc, Units.mul_inv, one_mul]

end DVR

section Remark58

open IsDedekindDomain NumberField

/-- **Remark 5.8, Hasse invariant part** (Hanke 2011, p. 25). Let $F$ be a number field, $\mathfrak p \nmid 2$ a finite prime
(`v`), $K_{\mathfrak p}$ the completion, $n$ odd, $u \in \mathcal O_{\mathfrak p}^\times$ and $a_0,\dots,a_{n-1} \in K_{\mathfrak p}^\times$. Then
$c_{\mathfrak p}(u\langle a_0,\dots,a_{n-1}\rangle) = c_{\mathfrak p}(\langle a_0,\dots,a_{n-1}\rangle)$ (Serre's convention, `hasseLocal`).
*Proof:* Lemma 5.10 (`lemma_5_10_finite`) with $(u,u)_{\mathfrak p} = 1$ (`hilbertSymbol_units_dvr`) and $n - 1$ even. -/
@[kb "hanke2011structure" "Rem. 5.8, p. 25 (Hasse invariant)"]
theorem remark_5_8_hasse {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (hn : Odd n) {u : v.adicCompletionIntegers F} (hu : IsUnit u)
    (a : Fin n → v.adicCompletion F) (ha : ∀ i, a i ≠ 0) :
    hasseLocal _ (fun i => (u : v.adicCompletion F) * a i) = hasseLocal _ a := by
  have hu0 : (u : v.adicCompletion F) ≠ 0 := by
    intro h
    exact hu.ne_zero (Subtype.ext h)
  have hnd : ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
    rwa [pow_one, map_ofNat] at this
  have huu : hilbertSymbol (v.adicCompletion F) (u : v.adicCompletion F) (u : v.adicCompletion F) = 1 :=
    hilbertSymbol_units_dvr (LocalDensity.NF.irreducible_π v) hnd (v.adicCompletion F) hu hu
  rw [lemma_5_10_finite v hu0 a ha, huu, one_pow, one_mul]
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = 2 * m := ⟨(n - 1) / 2, by obtain ⟨k, rfl⟩ := hn; omega⟩
  have hsq : hilbertSymbol (v.adicCompletion F) (u : v.adicCompletion F) (∏ i, a i) ^ 2 = 1 := by
    unfold hilbertSymbol; split_ifs <;> norm_num
  rw [hm, pow_mul, hsq, one_pow, one_mul]

end Remark58

end QuadFormsKB.Hanke2011Structure
