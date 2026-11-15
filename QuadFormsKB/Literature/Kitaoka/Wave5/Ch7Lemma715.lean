/-
# Kitaoka 1993, Lemma 7.1.5 and Theorem 7.1.3: the trace form of an abelian number field

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Theorem 7.1.3, Lemma 7.1.5, p. 195, and
Lemma 7.1.7, p. 196 (printed pages).

**Setting.** Let $F$ be a finite abelian extension of $\mathbb Q$ and $R_F$ its ring of integers. Kitaoka (Theorem 7.1.3)
puts $B_F(x, y) = \operatorname{tr}_{F/\mathbb Q}(x\bar y)$, where $\bar y$ is the complex conjugate of $y$. Kitaoka
regards $F$ as a subfield of $\mathbb C$; an abelian field is stable under complex conjugation, and conjugation
restricts to an automorphism $c$ of $F$ with $\varphi(c(x)) = \overline{\varphi(x)}$ for **every** complex embedding
$\varphi$ of $F$ (the identity when $F$ is totally real, the complex conjugation of the CM field $F$ otherwise). Here
$F$ is an abstract number field, and $c$ is an automorphism with that property (`IsComplexConj c`, Mathlib's
`NumberField.ComplexEmbedding.IsConj φ c` for every $\varphi$); `exists_isComplexConj` proves that it exists for every
abelian $F$, and it is unique. The form is `traceForm c x y` $= \operatorname{tr}_{F/\mathbb Q}(x\,c(y))$, and
$Q(x) = B_F(x, x) = \sum_\varphi |\varphi(x)|^2$ (`traceForm_self_eq`).

**Proves** (unconditional)
* `lemma715`: Kitaoka's Lemma 7.1.5: $\min R_F = [F : \mathbb Q]$, and the minimal vectors $\mathcal M(R_F)$ are exactly
  the roots of unity in $F$ (Kitaoka states "are roots of unity"; the converse inclusion is immediate). The proof
  (Kitaoka's) is the arithmetic–geometric mean inequality
  $\sum_\varphi |\varphi(x)|^2 \ge n\,|N_{F/\mathbb Q}(x)|^{2/n} \ge n$ for $0 \ne x \in R_F$ ($n = [F:\mathbb Q]$),
  with equality only if every $|\varphi(x)| = 1$, and then $x$ is a root of unity (Kronecker; Mathlib's
  `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`). *Update:* the lemma holds for every number field with such a $c$
  (`traceForm_ge`, `traceForm_eq_iff`); `lemma715` is the abelian case.
* `exists_isComplexConj`: the conjugation $c$ exists on an abelian number field.

**States** (named propositions, not proved)
* `Lemma717`: Kitaoka's Lemma 7.1.7: for $F = \mathbb Q(\zeta)$, $\zeta$ a primitive $p^n$-th root of unity, $(R_F, B_F)$ is
  a positive lattice of E-type. Kitaoka's proof computes $\operatorname{tr}_{F/\mathbb Q}\zeta^m$ and identifies $R_F$
  with $L \otimes M$ ($L$ the lattice of Lemma 7.1.6, `EType.isEType_gram716`, and $M = \langle p^{n-1}\rangle^{\perp
  p^{n-1}}$); the traces of roots of unity are not in Mathlib.
* `Theorem713`: Kitaoka's Theorem 7.1.3: for every finite abelian $F/\mathbb Q$, $(R_F, B_F)$ is a positive lattice of
  E-type. Kitaoka's proof needs the Kronecker–Weber theorem and $R_{\mathbb Q(\zeta_m)} = \bigotimes_i
  R_{\mathbb Q(\zeta_{p_i^{a_i}})}$; neither is in Mathlib.

In the statements, the lattice $(R_F, B_F)$ enters through its Gram matrix in Mathlib's integral basis
`NumberField.RingOfIntegers.basis F` (`gramTrace c`), matching the Gram-matrix model of `Ch7EType.lean`; E-type does not
depend on the basis.
-/
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.Basic
import QuadFormsKB.Literature.Kitaoka.Ch7EType

open NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace Module

noncomputable section

namespace QuadFormsKB.Kitaoka.EType.TraceForm

/-! ### An arithmetic–geometric mean consequence -/

/-- Nonnegative reals with product at least $1$ have sum at least their number, with equality only if all are $1$
(the arithmetic–geometric mean inequality). -/
theorem card_le_sum_of_one_le_prod {ι : Type*} (s : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hp : 1 ≤ ∏ i ∈ s, z i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, z i ∧ (∑ i ∈ s, z i = s.card → ∀ i ∈ s, z i = 1) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  set w : ι → ℝ := fun _ => (s.card : ℝ)⁻¹ with hw
  have hw0 : ∀ i ∈ s, 0 < w i := fun _ _ => inv_pos.2 hn
  have hw1 : ∑ i ∈ s, w i = 1 := by
    simp only [hw, Finset.sum_const, nsmul_eq_mul]; field_simp
  have hG : 1 ≤ ∏ i ∈ s, z i ^ w i := by
    rw [Real.finsetProd_rpow s z hz]
    exact Real.one_le_rpow hp (inv_pos.2 hn).le
  have hamgm := Real.geom_mean_le_arith_mean_weighted s w z (fun i hi => (hw0 i hi).le) hw1 hz
  have hA : ∑ i ∈ s, w i * z i = (s.card : ℝ)⁻¹ * ∑ i ∈ s, z i := by
    simp only [hw, Finset.mul_sum]
  refine ⟨?_, fun heq => ?_⟩
  · have : 1 ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, z i := hA ▸ hG.trans hamgm
    have := mul_le_mul_of_nonneg_left this hn.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at this
  · have hA1 : ∑ i ∈ s, w i * z i = 1 := by rw [hA, heq, inv_mul_cancel₀ hn.ne']
    have hGA : ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i := le_antisymm hamgm (hA1 ▸ hG)
    intro i hi
    rw [← hA1]
    exact (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw0 hw1 hz).1 hGA i hi

variable {F : Type*} [Field F] [NumberField F]

/-! ### The trace form -/

/-- **Complex conjugation on $F$**: an automorphism $c$ of $F$ with $\varphi(c(x)) = \overline{\varphi(x)}$ for every
complex embedding $\varphi$ of $F$ (Mathlib's `ComplexEmbedding.IsConj φ c` for all $\varphi$). -/
def IsComplexConj (c : F ≃ₐ[ℚ] F) : Prop := ∀ φ : F →+* ℂ, IsConj φ c

/-- **Kitaoka's form $B_F$** (Theorem 7.1.3, p. 195): $B_F(x, y) = \operatorname{tr}_{F/\mathbb Q}(x\,\bar y)$, with
$\bar y = c(y)$ for the complex conjugation $c$ of $F$. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.3, p. 195 (the form B_F(x, y) = tr xȳ)"]
def traceForm (c : F ≃ₐ[ℚ] F) (x y : F) : ℚ := Algebra.trace ℚ F (x * c y)

/-- $Q(x) = B_F(x, x) = \sum_\varphi |\varphi(x)|^2$, the sum over the $\mathbb Q$-embeddings $\varphi : F \to \mathbb C$
(p. 195). -/
theorem traceForm_self_eq {c : F ≃ₐ[ℚ] F} (hc : IsComplexConj c) (x : F) :
    (traceForm c x x : ℝ) = ∑ σ : F →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x * c x)
  have h2 : ∀ σ : F →ₐ[ℚ] ℂ, σ (x * c x) = (Complex.normSq (σ x) : ℂ) := by
    intro σ
    rw [map_mul, ← Complex.mul_conj]
    congr 1
    have := (hc (σ : F →+* ℂ)).eq x
    simpa using this
  simp only [h2] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, ← h]
  simp [traceForm]

/-- The product of the $|\varphi(x)|^2$ is $N_{F/\mathbb Q}(x)^2$. -/
theorem prod_normSq_eq (x : F) :
    ∏ σ : F →ₐ[ℚ] ℂ, Complex.normSq (σ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← map_prod Complex.normSq, ← h]
  simp [sq]

/-- $|\varphi(x)| = 1$ for every embedding when $x$ is a root of unity. -/
theorem normSq_eq_one_of_pow {x : F} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) (σ : F →ₐ[ℚ] ℂ) :
    Complex.normSq (σ x) = 1 := by
  have h1 : (σ x) ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : ‖σ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hm.ne'
  rw [Complex.normSq_eq_norm_sq, h2, one_pow]

/-- **Lemma 7.1.5, the bound** (for every number field with a complex conjugation $c$): $Q(x) \ge [F : \mathbb Q]$ for
$0 \ne x \in R_F$, with equality iff $x$ is a root of unity. -/
theorem traceForm_ge {c : F ≃ₐ[ℚ] F} (hc : IsComplexConj c) {x : 𝓞 F} (hx : x ≠ 0) :
    (finrank ℚ F : ℚ) ≤ traceForm c x x ∧
      (traceForm c x x = finrank ℚ F ↔ ∃ m : ℕ, 0 < m ∧ (x : F) ^ m = 1) := by
  classical
  set z : (F →ₐ[ℚ] ℂ) → ℝ := fun σ => Complex.normSq (σ x) with hzdef
  have hz : ∀ σ ∈ (Finset.univ : Finset (F →ₐ[ℚ] ℂ)), 0 ≤ z σ := fun σ _ => Complex.normSq_nonneg _
  have hcard : ((Finset.univ : Finset (F →ₐ[ℚ] ℂ)).card : ℝ) = finrank ℚ F := by
    rw [Finset.card_univ, AlgHom.card]
  -- the norm is a nonzero integer
  have hN : 1 ≤ ((Algebra.norm ℚ (x : F) : ℚ) : ℝ) ^ 2 := by
    have hNz : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
    have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hNz
      exact_mod_cast this
    have h2 : ((Algebra.norm ℚ (x : F) : ℚ) : ℝ) = ((Algebra.norm ℤ x : ℤ) : ℝ) := by
      rw [← Algebra.coe_norm_int]; push_cast; rfl
    rw [h2, ← sq_abs]
    nlinarith [abs_nonneg ((Algebra.norm ℤ x : ℤ) : ℝ)]
  have hp : 1 ≤ ∏ σ ∈ (Finset.univ : Finset (F →ₐ[ℚ] ℂ)), z σ := by
    rw [hzdef]; simp only; rw [prod_normSq_eq]; exact hN
  obtain ⟨hge, heq⟩ := card_le_sum_of_one_le_prod _ z hz hp
  rw [hcard] at hge heq
  have hQ : (traceForm c x x : ℝ) = ∑ σ, z σ := traceForm_self_eq hc x
  refine ⟨?_, ⟨fun h => ?_, fun ⟨m, hm, hxm⟩ => ?_⟩⟩
  · have : ((finrank ℚ F : ℚ) : ℝ) ≤ (traceForm c x x : ℝ) := by rw [hQ]; push_cast; exact hge
    exact_mod_cast this
  · have hs : ∑ σ, z σ = finrank ℚ F := by
      rw [← hQ, h]; push_cast; rfl
    have h1 := heq hs
    obtain ⟨m, hm, hxm⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ
      (x := (x : F)) (RingOfIntegers.isIntegral_coe x) (fun φ => by
        have := h1 φ.toRatAlgHom (Finset.mem_univ _)
        simp only [hzdef, RingHom.toRatAlgHom_apply] at this
        rw [Complex.normSq_eq_norm_sq] at this
        nlinarith [norm_nonneg (φ x), sq_nonneg (‖φ x‖ - 1)])
    exact ⟨m, hm, hxm⟩
  · have : (traceForm c x x : ℝ) = ((finrank ℚ F : ℚ) : ℝ) := by
      rw [hQ]
      simp only [hzdef, normSq_eq_one_of_pow hm hxm, Finset.sum_const, Finset.card_univ, AlgHom.card,
        nsmul_eq_mul, mul_one]
      push_cast; rfl
    exact_mod_cast this

/-- $Q(1) = [F : \mathbb Q]$. -/
theorem traceForm_one {c : F ≃ₐ[ℚ] F} : traceForm c 1 1 = finrank ℚ F := by
  have := Algebra.trace_algebraMap (R := ℚ) (S := F) 1
  simpa [traceForm] using this

open scoped IsMulCommutative in
/-- On an abelian number field, complex conjugation restricts to an automorphism $c$ with
$\varphi \circ c = \overline{\varphi}$ for every complex embedding $\varphi$ (the identity if $F$ is totally real).
The argument follows Mathlib's `NumberField.IsCMField.of_isAbelianGalois`. -/
theorem exists_isComplexConj [IsAbelianGalois ℚ F] : ∃ c : F ≃ₐ[ℚ] F, IsComplexConj c := by
  classical
  let φ : F →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨σ, hσ₁⟩ : ∃ σ : Gal(F/ℚ), IsConj φ σ := by
    by_cases hr : IsReal φ
    · exact ⟨1, isConj_one_iff.2 hr⟩
    · refine exists_isConj_of_isRamified (k := ℚ) ?_
      refine isRamified_iff.mpr ⟨?_, IsTotallyReal.isReal _⟩
      rw [isComplex_mk_iff]; exact hr
  refine ⟨σ, fun ψ => ?_⟩
  obtain ⟨ν, rfl⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ (by ext; simp)
  have hcomm : σ = ν.symm⁻¹ * σ * ν.symm := by
    rw [mul_assoc, mul_comm σ ν.symm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcomm]
  exact hσ₁.comp _

/-- **Kitaoka 1993, Lemma 7.1.5** (p. 195). Let $F$ be a finite abelian extension of $\mathbb Q$, $R_F$ its ring of
integers and $B_F(x, y) = \operatorname{tr}_{F/\mathbb Q}(x\bar y)$. Then $\min R_F = [F:\mathbb Q]$: every nonzero
$x \in R_F$ has $Q(x) \ge [F : \mathbb Q]$, and $Q(1) = [F : \mathbb Q]$; and the minimal vectors $\mathcal M(R_F)$ are
the roots of unity in $F$ (a nonzero $x$ has $Q(x) = [F:\mathbb Q]$ iff $x^m = 1$ for some $m \ge 1$). -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.5, p. 195"]
theorem lemma715 [IsAbelianGalois ℚ F] (c : F ≃ₐ[ℚ] F) (hc : IsComplexConj c) :
    (∀ x : 𝓞 F, x ≠ 0 → (finrank ℚ F : ℚ) ≤ traceForm c x x) ∧ traceForm c 1 1 = finrank ℚ F ∧
      ∀ x : 𝓞 F, x ≠ 0 → (traceForm c x x = finrank ℚ F ↔ ∃ m : ℕ, 0 < m ∧ (x : F) ^ m = 1) :=
  ⟨fun _ hx => (traceForm_ge hc hx).1, traceForm_one, fun _ hx => (traceForm_ge hc hx).2⟩

/-! ### Theorem 7.1.3 and Lemma 7.1.7 (stated) -/

/-- **The Gram matrix of $(R_F, B_F)$** in Mathlib's integral basis `NumberField.RingOfIntegers.basis F`
$(b_i)$: $(B_F(b_i, b_j))_{i,j}$. -/
def gramTrace (c : F ≃ₐ[ℚ] F) :
    Matrix (Free.ChooseBasisIndex ℤ (𝓞 F)) (Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ :=
  Matrix.of fun i j => traceForm c (RingOfIntegers.basis F i) (RingOfIntegers.basis F j)

/-- **Kitaoka 1993, Lemma 7.1.7** (p. 196), *stated*: let $p$ be a prime, $n \ge 1$, and $F = \mathbb Q(\zeta)$ with
$\zeta$ a primitive $p^n$-th root of unity (`IsCyclotomicExtension {p ^ n} ℚ F`). Then $(R_F, B_F)$ is a positive
lattice of E-type. (The lower bound on $n$ is hard to read in our copy of the book; Kitaoka's proof works for every
$n \ge 1$, and $n = 1$ is the lattice of Lemma 7.1.6.) -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.7, p. 196"]
def Lemma717 : Prop :=
  ∀ (p n : ℕ), p.Prime → 1 ≤ n → ∀ (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {p ^ n} ℚ F]
    (c : F ≃ₐ[ℚ] F), IsComplexConj c → IsPosGram (gramTrace c) ∧ IsEType (gramTrace c)

/-- **Kitaoka 1993, Theorem 7.1.3** (p. 195), *stated*: let $F$ be a finite abelian extension of $\mathbb Q$, $R_F$
its ring of integers and $B_F(x, y) = \operatorname{tr}_{F/\mathbb Q}(x\bar y)$. Then $(R_F, B_F)$ is a positive lattice
of E-type. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.3, p. 195"]
def Theorem713 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F] (c : F ≃ₐ[ℚ] F), IsComplexConj c →
    IsPosGram (gramTrace c) ∧ IsEType (gramTrace c)

end QuadFormsKB.Kitaoka.EType.TraceForm
