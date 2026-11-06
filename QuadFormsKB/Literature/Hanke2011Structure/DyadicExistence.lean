/-
# Hanke 2011, Remark 2.11: the dyadic even case over $\mathbb Q_2$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Remark 2.11, p. 12: "When $n$ is even and $F_{\mathfrak p} = \mathbb Q_2$,
we have existence [of a local genus $G_{\mathfrak p}$ with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$] iff either
$\mathfrak I(S_{\mathfrak p}) \subseteq \mathcal O_{\mathfrak p}$ and $S \equiv (-1)^{n/2}$ or
$\mathfrak I(S_{\mathfrak p}) \subseteq 4\mathcal O_{\mathfrak p}$."

Here $\mathcal O_{\mathfrak p} = \mathbb Z_2$, $n = 2k$, and the local genera are the $\mathrm{GL}_n(\mathbb Z_2)$-classes of
primitive $\mathbb Z_2$-valued forms (`IsPrimitiveForm`). The statement is made for a representative $s \in \mathbb Z_2$ of
the squareclass; both sides are unchanged by $s \mapsto sw^2$, $w \in \mathbb Z_2^\times$ (the left side by scaling one
variable, the right side since $w^2 \equiv 1 \bmod 8$), and a squareclass with $\mathfrak I(S) \not\subseteq \mathbb Z_2$ has
no integral representative, so it is never a Hessian determinant of a $\mathbb Z_2$-valued form. The congruence
"$S \equiv (-1)^{n/2}$" is read modulo $4$ (the paper's $\equiv_{(4)}$); it forces $S$ to be a unit.

**Proves** (unconditional)
* `hessian_det_mod_four`: the Hessian matrix $H = C + C^{\mathsf T}$ (`Dyadic.IsHess`) of any form over $\mathbb Z_2$ in
  $2k$ variables has $\det H \equiv 0$ or $(-1)^k \bmod 4$ (splitting off binary blocks of unit determinant,
  `Dyadic.split_at`; a binary block has determinant $4ac - b^2 \equiv -1 \bmod 4$ with $b$ odd);
* `hessian_orthSum_det`: $\det H(Q_1 \perp Q_2) = \det H(Q_1)\det H(Q_2)$;
* `remark_2_11_even_dyadic`: **Remark 2.11 for $n = 2k \ge 2$, $F_{\mathfrak p} = \mathbb Q_2$**: a primitive form over
  $\mathbb Z_2$ in $2k$ variables with $\det_H = s$ exists iff $s \equiv (-1)^k \bmod 4$ or $s \equiv 0 \bmod 4$. The
  forms are $x_0x_1 + \cdots + x_{2k-4}x_{2k-3} + (x_{2k-2}^2 + x_{2k-2}x_{2k-1} + t x_{2k-1}^2)$ and
  $x_0x_1 + \cdots + x_{2k-4}x_{2k-3} + (x_{2k-2}^2 + t x_{2k-1}^2)$ for a suitable $t$; the "only if" direction holds
  for every form, primitive or not.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicSplit
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesTwo
import QuadFormsKB.Witt.Bridge

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Hanke2011Structure.Dyadic

/-! ### Two facts about $\mathbb Z_2$ -/

/-- A non-unit of $\mathbb Z_2$ is divisible by $2$. -/
theorem two_dvd_of_not_isUnit_padic {x : ℤ_[2]} (hx : ¬ IsUnit x) : (2 : ℤ_[2]) ∣ x := by
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).mpr hx
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  simpa using hm

/-- $2$ does not divide $1$ in $\mathbb Z_2$. -/
theorem two_not_dvd_one_padic : ¬ (2 : ℤ_[2]) ∣ 1 := by
  intro h
  have hp : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.prime_p
  exact hp.not_isUnit (isUnit_of_dvd_one (by simpa using h))

/-! ### Hessian determinants modulo $4$ -/

/-- **Hessian determinants over $\mathbb Z_2$ modulo $4$.** If $H = G + G^{\mathsf T}$ is a Hessian matrix over
$\mathbb Z_2$ on an index type with $2k$ elements, then $4 \mid \det H$ or $4 \mid \det H - (-1)^k$. -/
theorem hessian_det_mod_four : ∀ (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ_[2]),
    IsHess H → Fintype.card ι = 2 * k → (4 : ℤ_[2]) ∣ H.det ∨ (4 : ℤ_[2]) ∣ H.det - (-1) ^ k := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ H _ hcard
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by simpa using hcard)
    right
    simp [Matrix.det_isEmpty]
  | succ k ih =>
    intro ι _ _ H hH hcard
    obtain ⟨G, hG⟩ := hH
    have hsym : ∀ a b, H b a = H a b := fun a b => by rw [hG]; simp [add_comm]
    have hdiag : ∀ a, H a a = 2 * G a a := fun a => by rw [hG]; simp [two_mul]
    by_cases hu : ∃ a b, a ≠ b ∧ IsUnit (H a b)
    · obtain ⟨a, b, hab, hunit⟩ := hu
      obtain ⟨m, hm⟩ := Composition.two_dvd_sub_one_of_isUnit hunit
      set t : ℤ_[2] := G a a * G b b - m - m ^ 2 with ht
      have hblock : (H.submatrix ![a, b] ![a, b]).det = -1 + 4 * t := by
        rw [Matrix.det_fin_two]
        simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hdiag a, hdiag b, hsym a b, ht]
        have : H a b = 1 + 2 * m := by linear_combination hm
        rw [this]; ring
      have hA : IsUnit (H.submatrix ![a, b] ![a, b]).det := by
        by_contra hne
        obtain ⟨c, hc⟩ := two_dvd_of_not_isUnit_padic hne
        rw [hblock] at hc
        exact two_not_dvd_one_padic ⟨2 * t - c, by linear_combination (-1 : ℤ_[2]) * hc⟩
      obtain ⟨S, hS, -, hdet⟩ := split_at H ⟨G, hG⟩ hab hA
      have hcardS : Fintype.card {x : ι // ¬ (x = a ∨ x = b)} = 2 * k := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype]
        have : (Finset.univ.filter fun x : ι => x = a ∨ x = b) = {a, b} := by
          ext x; simp
        rw [this, Finset.card_pair hab]
        omega
      rcases ih S hS hcardS with ⟨c, hc⟩ | ⟨c, hc⟩
      · left
        exact ⟨(-1 + 4 * t) * c, by rw [hdet, hblock, hc]; ring⟩
      · right
        refine ⟨t * (-1) ^ k - c + 4 * t * c, ?_⟩
        have hc' : S.det = (-1) ^ k + 4 * c := by linear_combination hc
        rw [hdet, hblock, hc']
        ring
    · push Not at hu
      have hdvd : ∀ i j, (2 : ℤ_[2]) ∣ H i j := by
        intro i j
        by_cases hij : i = j
        · subst hij; exact ⟨G i i, hdiag i⟩
        · exact two_dvd_of_not_isUnit_padic (hu i j hij)
      choose H' hH' using hdvd
      have hH2 : H = (2 : ℤ_[2]) • Matrix.of H' := by
        ext i j; simp [hH' i j]
      left
      refine ⟨2 ^ (2 * k) * (Matrix.of H').det, ?_⟩
      rw [hH2, Matrix.det_smul, hcard]
      ring

/-! ### Orthogonal sums -/

section OrthSum

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The Hessian matrix of $Q_1 \perp Q_2$ is the block sum of the Hessian matrices (reindexed by
$\mathrm{Fin}\,m \oplus \mathrm{Fin}\,n \simeq \mathrm{Fin}(m+n)$). -/
theorem hessian_orthSum (Q₁ : QuadForm R m) (Q₂ : QuadForm R n) :
    (QuadForm.orthSum Q₁ Q₂).hessian =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q₁.hessian 0 0 Q₂.hessian) := by
  have u₁ := Q₁.upper
  have u₂ := Q₂.upper
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b =>
      simp only [QuadForm.hessian, QuadForm.orthSum, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.of_apply, Fin.addCases_left, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        fromBlocks_apply₁₁]
      have e1 : (Fin.castAdd n a ≤ Fin.castAdd n b) ↔ a ≤ b := Iff.rfl
      have e2 : (Fin.castAdd n b ≤ Fin.castAdd n a) ↔ b ≤ a := Iff.rfl
      simp only [e1, e2]
      by_cases hab : a ≤ b
      · rcases hab.lt_or_eq with h | rfl
        · simp [hab, not_le.mpr h, u₁ h]
        · simp
      · simp [hab, le_of_lt (not_le.mp hab), u₁ (not_le.mp hab)]
    | right b =>
      have h1 : Fin.castAdd n a ≤ Fin.natAdd m b := Fin.le_iff_val_le_val.mpr (by simp; omega)
      have h2 : ¬ Fin.natAdd m b ≤ Fin.castAdd n a := by
        rw [Fin.le_iff_val_le_val]; simp; omega
      simp [QuadForm.hessian, QuadForm.orthSum, QuadForm.ofUpper, h1, h2]
  | right a =>
    induction j using Fin.addCases with
    | left b =>
      have h1 : Fin.castAdd n b ≤ Fin.natAdd m a := Fin.le_iff_val_le_val.mpr (by simp; omega)
      have h2 : ¬ Fin.natAdd m a ≤ Fin.castAdd n b := by
        rw [Fin.le_iff_val_le_val]; simp; omega
      simp [QuadForm.hessian, QuadForm.orthSum, QuadForm.ofUpper, h1, h2]
    | right b =>
      simp only [QuadForm.hessian, QuadForm.orthSum, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.of_apply, Fin.addCases_right, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₂₂, Fin.natAdd_le_natAdd_iff]
      by_cases hab : a ≤ b
      · rcases hab.lt_or_eq with h | rfl
        · simp [hab, not_le.mpr h, u₂ h]
        · simp
      · simp [hab, le_of_lt (not_le.mp hab), u₂ (not_le.mp hab)]

/-- $\det H(Q_1 \perp Q_2) = \det H(Q_1)\cdot\det H(Q_2)$. -/
theorem hessian_orthSum_det (Q₁ : QuadForm R m) (Q₂ : QuadForm R n) :
    (QuadForm.orthSum Q₁ Q₂).hessian.det = Q₁.hessian.det * Q₂.hessian.det := by
  rw [hessian_orthSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- The hyperbolic plane $x_0x_1$. -/
def hypPlane : QuadForm R 2 := Composition.bq 0 1 0

/-- The sum $x_0x_1 + x_2x_3 + \cdots + x_{2j-2}x_{2j-1}$ of $j$ hyperbolic planes. -/
def hypSum : (j : ℕ) → QuadForm R (2 * j)
  | 0 => QuadForm.ofUpper fun _ _ => 0
  | j + 1 => QuadForm.orthSum (hypSum j) hypPlane

theorem hypSum_hessian_det (j : ℕ) : (hypSum (R := R) j).hessian.det = (-1) ^ j := by
  induction j with
  | zero => simp [Matrix.det_isEmpty]
  | succ j ih =>
    show (QuadForm.orthSum (hypSum j) hypPlane).hessian.det = _
    rw [hessian_orthSum_det, ih, pow_succ]
    congr 1
    have := Composition.neg_det_bq (0 : R) 1 0
    simp only [hypPlane] at this ⊢
    linear_combination -this

end OrthSum

/-! ### Remark 2.11 over $\mathbb Q_2$, $n$ even -/

/-- **Remark 2.11, $n$ even, $F_{\mathfrak p} = \mathbb Q_2$** (Hanke 2011, p. 12). For $n = 2k \ge 2$ and $s \in \mathbb Z_2$
(a representative of the squareclass $S_{\mathfrak p}$), a primitive $\mathbb Z_2$-valued form in $n$ variables with
Hessian determinant $s$ exists if and only if $s \equiv (-1)^{n/2} \bmod 4$ (then $s$ is a unit, $\mathfrak I(S) = \mathcal O$)
or $s \equiv 0 \bmod 4$ ($\mathfrak I(S) \subseteq 4\mathcal O$). -/
@[kb "hanke2011structure" "Rem. 2.11, p. 12 (n even, F_p = Q_2)"]
theorem remark_2_11_even_dyadic {k : ℕ} (hk : 1 ≤ k) (s : ℤ_[2]) :
    (∃ Q : QuadForm ℤ_[2] (2 * k), IsPrimitiveForm Q ∧ Q.hessian.det = s) ↔
      ((4 : ℤ_[2]) ∣ s - (-1) ^ k ∨ (4 : ℤ_[2]) ∣ s) := by
  constructor
  · rintro ⟨Q, -, rfl⟩
    rcases hessian_det_mod_four k Q.hessian ⟨Q.coeff, rfl⟩ (by simp) with h | h
    · exact Or.inr h
    · exact Or.inl h
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    -- the form `hypSum j ⊥ B` with `B` binary and `B.coeff 0 0 = 1`
    have prim : ∀ B : QuadForm ℤ_[2] 2, B.coeff 0 0 = 1 →
        IsPrimitiveForm (QuadForm.orthSum (hypSum j) B) := by
      intro B hB
      rw [IsPrimitiveForm, Ideal.eq_top_iff_one]
      refine Ideal.subset_span ⟨(Fin.natAdd (2 * j) 0, Fin.natAdd (2 * j) 0), ?_⟩
      simp [QuadForm.orthSum, QuadForm.ofUpper, hB]
    have hsq : ((-1 : ℤ_[2]) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
    rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · -- unit case: `B = x² + xy + t y²`, `det H(B) = 4t - 1`
      refine ⟨QuadForm.orthSum (hypSum j) (Composition.bq 1 1 ((-1) ^ j * c)),
        prim _ (Composition.bq_coeff00 _ _ _), ?_⟩
      rw [hessian_orthSum_det, hypSum_hessian_det]
      have hb := Composition.neg_det_bq (1 : ℤ_[2]) 1 ((-1) ^ j * c)
      linear_combination (-(-1 : ℤ_[2]) ^ j) * hb - hc + 4 * c * hsq
    · -- `4 ∣ s`: `B = x² + t y²`, `det H(B) = 4t`
      refine ⟨QuadForm.orthSum (hypSum j) (Composition.bq 1 0 ((-1) ^ j * c)),
        prim _ (Composition.bq_coeff00 _ _ _), ?_⟩
      rw [hessian_orthSum_det, hypSum_hessian_det]
      have hb := Composition.neg_det_bq (1 : ℤ_[2]) 0 ((-1) ^ j * c)
      linear_combination (-(-1 : ℤ_[2]) ^ j) * hb - hc + 4 * c * hsq

end QuadFormsKB.Hanke2011Structure
