/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for $L_2 = 2^k(E \perp \langle 2u\rangle)$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$, for the $2$-adic Jordan shape
$L_2 = 2^k(E \perp \langle 2u\rangle)$ with $E$ even unimodular and $u$ a $2$-adic unit.

**Layer.** As in `Section9Theorem18DyadicEven.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ of $B(x, y) = Q(x + y) - Q(x) - Q(y)$ (`locGram`, so
$G_{kk} = 2Q(b_k)$). The glue lemma of `Section9DyadicGlue.lean` (stated there for an integer Gram matrix on
$\mathbb Z^{n}$ with the special index last) is generalized here to an arbitrary matrix $A$ over $\mathbb Q_2$ and an
arbitrary special index $l$, exactly as `exists_sq_valued_wallDet'` generalizes the core lemma.

**Setting of the glue lemma** (`GlueData`-free hypotheses, all named in each statement): $A$ symmetric over
$\mathbb Q_2$ with integral entries and $A_{ii}/2$ integral; an index $l$ with $A_{il} = 0$ for $i \ne l$ and
$A_{ll} = 2u$, $u$ a unit; $\lvert\det A\rvert = \lvert 2\rvert$ (so the complement $E$ of $l$ is even unimodular).

**Proves**
* `congr_col`: for $S$ integral with $S^{\mathsf T}AS = A$ and $\det S = 1$, $Se_l \equiv e_l \pmod 2$;
* `exists_sq_valued_wallDet_glue'` (**the glue lemma over $\mathbb Q_2$**): every Wall frame $(P, R)$ of such an
  $S$ has $\lvert\det(P^{\mathsf T}AR)\rvert$ a square (glue $L$ to $\langle -2u\rangle$ to an even unimodular
  lattice and apply `exists_sq_valued_wallDet'`);
* `even_log_of_scaledEvenUnimodularPerpTwoUnit`: every element of $\theta(O^+(L_2))$ has even order;
* `exists_rootVector_of_unit_entry`: an off-diagonal unit entry of $A = cG$ (with $A_{kk}/2$ integral) gives
  $2$-adic root vectors of norm $c^{-1}w$ for every unit $w$;
* `theorem18OnlyIf_of_scaledEvenUnimodularPerpTwoUnit` (**Theorem 18, "only if", at $p = 2$ for
  $L_2 = 2^k(E \perp \langle 2u\rangle)$**): $\theta(O^+(L_2)) \subseteq \mathbb Z_2^\times\mathbb Q_2^{\times 2}
  \subseteq$ root group;
* `theorem18OnlyIf_of_covered2`, `theorem18DyadicResidual_of_residual2`, `theorem18Dyadic_of_residual2`,
  `theorem18Statement_of_residual2`.

**Defines**
* `IsScaledEvenUnimodularPerpTwoUnit` (the shape);
* `Theorem18DyadicCovered2` (`Theorem18DyadicCovered` or the new shape);
* `Theorem18DyadicResidual2` (a **named statement**, smaller than `Theorem18DyadicResidual`): the "only if" direction
  at the prime over $2$ for every lattice not covered by `Theorem18DyadicCovered2`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

namespace Glue2

/-! ### The congruence $Se_l \equiv e_l \pmod 2$ -/

section Congr

variable {N : ℕ}

/-- $A$ with column $l$ replaced by $e_l$: it has determinant $\det A / A_{ll}$. -/
def colOne (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) : Matrix (Fin N) (Fin N) Fv := A.updateCol l (Pi.single l 1)

theorem det_eq_mul_colOne (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (hl : ∀ i, i ≠ l → A i l = 0) : A.det = A l l * (colOne A l).det := by
  have hcol : (fun i => A i l) = A l l • (Pi.single l 1 : Fin N → Fv) := by
    ext i
    by_cases hi : i = l
    · subst hi; simp
    · simp [hl i hi, hi]
  have hA : A = A.updateCol l (A l l • (Pi.single l 1 : Fin N → Fv)) := by
    rw [← hcol]; ext i j
    by_cases hj : j = l
    · subst hj; simp
    · simp [updateCol_ne hj]
  conv_lhs => rw [hA]
  rw [det_updateCol_smul]
  rfl

theorem colOne_integral (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (hint : ∀ i j, Valued.v (A i j) ≤ 1) : ∀ i j, Valued.v (colOne A l i j) ≤ 1 := by
  intro i j
  simp only [colOne, updateCol_apply]
  split_ifs
  · simp only [Pi.single_apply]; split_ifs <;> simp
  · exact hint i j

theorem valued_det_colOne (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) (hu : Valued.v u = 1)
    (hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ)) (hdetA : Valued.v A.det = Valued.v (2 : Fv)) :
    Valued.v (colOne A l).det = 1 := by
  have h := hdetA
  rw [det_eq_mul_colOne A l hl, hll, map_mul, map_mul, hu, mul_one] at h
  have h2 : Valued.v (2 : Fv) ≠ 0 := by rw [hv2]; exact exp_ne_zero
  exact (mul_eq_left₀ h2).mp h

/-- **$Se_l \equiv e_l \pmod 2$** for an integral $S$ with $S^{\mathsf T}AS = A$ and $\det S = 1$, where $A$ is
symmetric, integral, $A_{ii}/2$ integral, $A_{il} = 0$ ($i \ne l$), $A_{ll} = 2u$ with $u$ a unit and
$\lvert\det A\rvert = \lvert 2\rvert$. -/
theorem congr_col (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) (hA : Aᵀ = A) (hint : ∀ i j, Valued.v (A i j) ≤ 1) (heven : ∀ i, Valued.v (A i i / 2) ≤ 1)
    (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) (hu : Valued.v u = 1)
    (hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ)) (hdetA : Valued.v A.det = Valued.v (2 : Fv))
    (S : Matrix (Fin N) (Fin N) Fv) (hS : ∀ i j, Valued.v (S i j) ≤ 1) (hSA : Sᵀ * A * S = A)
    (hdet : S.det = 1) :
    ∀ i, Valued.v ((S i l - if i = l then 1 else 0) / 2) ≤ 1 := by
  classical
  have hsymA : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  have hAl : ∀ k, A l k = if k = l then 2 * u else 0 := by
    intro k
    split_ifs with h
    · rw [h, hll]
    · rw [hsymA]; exact hl k h
  set s : Fin N → Fv := fun k => S k l
  set Sinv := S.adjugate
  have hSinv : ∀ i j, Valued.v (Sinv i j) ≤ 1 := Glue.adjugate_integral S hS
  have hSSinv : S * Sinv = 1 := by rw [mul_adjugate, hdet, one_smul]
  -- Step 1: `(A s)_j = 2u (S⁻¹)_{l j}`
  have hstep1 : ∀ j, (A *ᵥ s) j = 2 * u * Sinv l j := by
    intro j
    have h1 : Sᵀ * A = A * Sinv := by
      calc Sᵀ * A = Sᵀ * A * (S * Sinv) := by rw [hSSinv, Matrix.mul_one]
        _ = A * Sinv := by rw [← Matrix.mul_assoc, hSA]
    have h2 := congrFun (congrFun h1 l) j
    simp only [Matrix.mul_apply, transpose_apply] at h2
    have h3 : ∑ k, A l k * Sinv k j = 2 * u * Sinv l j := by
      rw [Finset.sum_eq_single l]
      · rw [hll]
      · intro k _ hk; rw [hAl k, if_neg hk, zero_mul]
      · simp
    rw [← h3, ← h2]
    simp only [mulVec, dotProduct, s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsymA]; ring
  -- Step 2: the vector `st = s - s_l e_l`
  set st : Fin N → Fv := fun k => if k = l then 0 else s k with hst
  have hAcol : ∀ j, A j l = if j = l then 2 * u else 0 := fun j => by rw [hsymA]; exact hAl j
  have hAst : ∀ j, (A *ᵥ st) j = 2 * (u * Sinv l j - if j = l then u * s l else 0) := by
    intro j
    have e : (A *ᵥ st) j = (A *ᵥ s) j - A j l * s l := by
      simp only [mulVec, dotProduct, st]
      rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ l),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ l)]
      simp only [if_true, mul_zero, add_zero]
      have : ∑ x ∈ Finset.univ.erase l, A j x * (if x = l then 0 else s x) =
          ∑ x ∈ Finset.univ.erase l, A j x * s x :=
        Finset.sum_congr rfl fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)]
      rw [this]
    rw [e, hstep1, hAcol]
    split_ifs <;> ring
  have hAst_l : (A *ᵥ st) l = 0 := by
    simp only [mulVec, dotProduct, st]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = l
    · simp [hk]
    · rw [hAl k, if_neg hk, zero_mul]
  -- Step 3: `st = 2t` with `t` integral
  set A' := colOne A l
  have hA'int := colOne_integral A l hint
  have hA'det := valued_det_colOne A l u hl hll hu hv2 hdetA
  have hA'inv := Glue.inv_integral A' hA'int hA'det
  have hA'unit : IsUnit A'.det := isUnit_iff_ne_zero.mpr (by
    intro h0; rw [h0, map_zero] at hA'det; exact zero_ne_one hA'det)
  have hA'st : A' *ᵥ st = A *ᵥ st := by
    funext i
    simp only [A', colOne, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = l
    · simp [hk, st]
    · rw [updateCol_ne hk]
  set w : Fin N → Fv := fun j => u * Sinv l j - if j = l then u * s l else 0
  have hw : ∀ j, Valued.v (w j) ≤ 1 := by
    intro j
    simp only [w]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul, hu, one_mul]; exact hSinv _ _
    · split_ifs
      · rw [map_mul, hu, one_mul]; exact hS _ _
      · simp
  set t : Fin N → Fv := A'⁻¹ *ᵥ w
  have ht : ∀ k, Valued.v (t k) ≤ 1 := mulVec_integral _ _ hA'inv hw
  have hst2 : st = (2 : Fv) • t := by
    have e1 : A' *ᵥ st = (2 : Fv) • w := by
      rw [hA'st]; ext j; rw [hAst]; rfl
    have e2 : st = A'⁻¹ *ᵥ (A' *ᵥ st) := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'unit, one_mulVec]
    rw [e2, e1, mulVec_smul]
  -- Step 4: `Q(s) = Q(e_l)` gives `v(s_l² - 1) ≤ exp(-2)`
  have hQs : s ⬝ᵥ (A *ᵥ s) = 2 * u := by
    have := congrFun (congrFun hSA l) l
    simp only [Matrix.mul_apply, transpose_apply] at this
    rw [← hll, ← this]
    simp only [dotProduct, mulVec, s, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hs_dec : s = st + Pi.single l (s l) := by
    ext k
    by_cases hk : k = l
    · subst hk; simp [st]
    · simp [st, hk]
  have hsplit : s ⬝ᵥ (A *ᵥ s) = st ⬝ᵥ (A *ᵥ st) + s l * (2 * u * s l) := by
    have hAsingle : A *ᵥ Pi.single l (s l) = (s l) • fun j => A j l := by
      funext j; simp [mulVec_single, mul_comm]
    have hsym_dot : Pi.single l (s l) ⬝ᵥ (A *ᵥ st) = 0 := by
      rw [single_dotProduct, hAst_l, mul_zero]
    have hst_l : st l = 0 := by simp [st]
    have e3 : st ⬝ᵥ (fun j => A j l) = 0 := by
      simp only [dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = l
      · rw [hk, hst_l, zero_mul]
      · rw [hl k hk, mul_zero]
    conv_lhs => rw [hs_dec]
    rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym_dot, hAsingle]
    simp only [dotProduct_smul, single_dotProduct, smul_eq_mul, Pi.smul_apply, e3, mul_zero, zero_add,
      add_zero, hll]
    ring
  have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have hhalf := valued_half_quad_le_one' A hA hint heven t ht
  set h := (t ⬝ᵥ (A *ᵥ t)) / 2
  have hsl2 : s l ^ 2 - 1 = -(4 * h) / u := by
    have e := hQs
    rw [hsplit, hst2, mulVec_smul, smul_dotProduct, dotProduct_smul] at e
    simp only [smul_eq_mul] at e
    field_simp
    simp only [h]
    linear_combination e / 2
  have hv4 : Valued.v (s l ^ 2 - 1) ≤ exp (-2 : ℤ) := by
    rw [hsl2, map_div₀, hu, div_one, Valuation.map_neg, map_mul]
    have : Valued.v (4 : Fv) = exp (-2 : ℤ) := by
      rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, hv2, ← exp_add]; norm_num
    rw [this]
    exact mul_le_of_le_one_right' hhalf
  -- Step 5: `s_l ≡ 1 (mod 2)`
  have hsl1 : Valued.v (s l - 1) ≤ exp (-1 : ℤ) := by
    by_contra hgt
    have hle : Valued.v (s l - 1) ≤ 1 :=
      le_trans (Valuation.map_sub _ _ _) (max_le (hS l l) (by simp))
    have h1 : Valued.v (s l - 1) = 1 := by
      by_contra hne; exact hgt (Glue.le_exp_neg_one_of_lt_one' (lt_of_le_of_ne hle hne))
    have h2 : Valued.v (s l + 1) = 1 := by
      have e : s l + 1 = (s l - 1) + 2 := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [h1, hv2, ← exp_zero, exp_lt_exp]; norm_num), h1]
    have h3 : Valued.v (s l ^ 2 - 1) = 1 := by
      rw [show s l ^ 2 - 1 = (s l - 1) * (s l + 1) by ring, map_mul, h1, h2, one_mul]
    rw [h3, ← exp_zero, exp_le_exp] at hv4
    norm_num at hv4
  -- conclusion
  intro i
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hv2inv : Valued.v ((2 : Fv)⁻¹) = exp (1 : ℤ) := by rw [map_inv₀, hv2, ← WithZero.exp_neg]; norm_num
  by_cases hi : i = l
  · subst hi
    rw [if_pos rfl, div_eq_mul_inv, map_mul, hv2inv]
    calc Valued.v (S i i - 1) * exp (1 : ℤ) ≤ exp (-1 : ℤ) * exp (1 : ℤ) := mul_le_mul' hsl1 le_rfl
      _ = 1 := by rw [← exp_add]; norm_num
  · rw [if_neg hi, sub_zero]
    have : S i l = 2 * t i := by
      have := congrFun hst2 i
      simpa [st, hi] using this
    rw [this, mul_div_cancel_left₀ _ h2ne]
    exact ht i

end Congr

/-! ### The glued lattice -/

section GlueLattice

variable {N : ℕ}

/-- The column with entry $c$ in row $l$. -/
def lcol (l : Fin N) (c : Fv) : Matrix (Fin N) (Fin 1) Fv :=
  Matrix.of fun i _ => if i = l then c else 0

/-- The Gram matrix of the glued lattice $K$ (basis $e_0, \dots, e_{N-1}, (e_l + f)/2$ of
$L \perp \langle -2u\rangle$, where $f$ spans $\langle -2u\rangle$). -/
def glueA (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) :
    Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks A (lcol l u) (lcol l u)ᵀ 0

/-- The change of basis from $K$ to $L \perp \langle -2u\rangle$. -/
def gam (l : Fin N) : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks 1 (lcol l (1 / 2 : Fv)) 0 (Matrix.of fun _ _ => (1 / 2 : Fv))

/-- Its inverse. -/
def gamInv (l : Fin N) : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks 1 (lcol l (-1 : Fv)) 0 (Matrix.of fun _ _ => (2 : Fv))

/-- The Gram matrix of $L \perp \langle -2u\rangle$. -/
def tildeA (A : Matrix (Fin N) (Fin N) Fv) (u : Fv) : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks A 0 0 (Matrix.of fun _ _ => -(2 * u))

/-- $S \oplus 1$. -/
def tildeS (S : Matrix (Fin N) (Fin N) Fv) : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks S 0 0 1

/-- The matrix of $S \oplus 1$ in the basis of $K$. -/
def glueS (S : Matrix (Fin N) (Fin N) Fv) (l : Fin N) : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) Fv :=
  fromBlocks S (Matrix.of fun i _ => (S i l - if i = l then 1 else 0) / 2) 0 1

theorem gam_mul_gamInv (l : Fin N) : (gam (v := v) l) * gamInv l = 1 := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp only [gam, gamInv] <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, lcol, Matrix.of_apply, Matrix.one_apply, Matrix.zero_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, Fin.fin_one_eq_zero, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
  all_goals (try split_ifs)
  all_goals (first | rfl | ring | norm_num)

theorem glueS_eq (S : Matrix (Fin N) (Fin N) Fv) (l : Fin N) : gamInv l * tildeS S * gam l = glueS S l := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp only [gam, gamInv, tildeS, glueS] <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, lcol, Matrix.of_apply, Matrix.one_apply, Matrix.zero_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, Fin.fin_one_eq_zero, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
  all_goals (try split_ifs)
  all_goals (first | rfl | ring | norm_num)

theorem glueA_eq (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) (hA : Aᵀ = A)
    (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) :
    (gam l)ᵀ * tildeA A u * gam l = glueA A l u := by
  have hsymA : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  have hl' : ∀ j, j ≠ l → A l j = 0 := fun j hj => by rw [hsymA]; exact hl j hj
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp only [gam, tildeA, glueA] <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, lcol, Matrix.of_apply, Matrix.one_apply, Matrix.zero_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add, Finset.univ_unique,
      Finset.sum_singleton, Fin.fin_one_eq_zero, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false,
      transpose_apply, fromBlocks_transpose]
  all_goals (try split_ifs)
  all_goals (try subst_vars)
  all_goals (try rw [hll])
  all_goals (try rw [hl _ (by assumption)])
  all_goals (try rw [hl' _ (by assumption)])
  all_goals (first | rfl | ring | norm_num | simp)

theorem glueS_orth (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) (hA : Aᵀ = A)
    (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) (S : Matrix (Fin N) (Fin N) Fv)
    (hSA : Sᵀ * A * S = A) : (glueS S l)ᵀ * glueA A l u * glueS S l = glueA A l u := by
  rw [← glueS_eq, ← glueA_eq A l u hA hl hll]
  have h1 : (gamInv (v := v) l)ᵀ * (gam l)ᵀ = 1 := by
    rw [← transpose_mul, gam_mul_gamInv, transpose_one]
  have h2 : (gam (v := v) l) * gamInv l = 1 := gam_mul_gamInv l
  have h3 : (tildeS S)ᵀ * tildeA A u * tildeS S = tildeA A u := by
    rw [tildeS, tildeA, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_zero, transpose_one,
      Matrix.one_mul, Matrix.mul_one, hSA]
  calc (gamInv l * tildeS S * gam l)ᵀ * ((gam l)ᵀ * tildeA A u * gam l) * (gamInv l * tildeS S * gam l)
      = (gam l)ᵀ * (tildeS S)ᵀ * ((gamInv l)ᵀ * (gam l)ᵀ) * tildeA A u * (gam l * gamInv l) * tildeS S *
          gam l := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = (gam l)ᵀ * ((tildeS S)ᵀ * tildeA A u * tildeS S) * gam l := by
        rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (gam l)ᵀ * tildeA A u * gam l := by rw [h3]

end GlueLattice

section GlueFinal

variable {N : ℕ}

theorem valued_det_glueA (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) (hA : Aᵀ = A)
    (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) (hu : Valued.v u = 1)
    (hdetA : Valued.v A.det = Valued.v (2 : Fv)) :
    Valued.v (glueA A l u).det = 1 := by
  have hgam : (gam (v := v) l).det = 1 / 2 := by
    rw [gam, det_fromBlocks_zero₂₁, det_one, one_mul, det_unique]; rfl
  have hd1 : (Matrix.of fun _ _ => -(2 * u) : Matrix (Fin 1) (Fin 1) Fv).det = -(2 * u) := by
    rw [det_unique]; rfl
  have htil : (tildeA A u).det = A.det * (-(2 * u)) := by
    rw [tildeA, det_fromBlocks_zero₂₁, hd1]
  rw [← glueA_eq A l u hA hl hll, det_mul, det_mul, det_transpose, hgam, htil]
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have e : (1 / 2 : Fv) * (A.det * -(2 * u)) * (1 / 2) = -(A.det * u / 2) := by field_simp
  have hv2' : Valued.v (2 : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr h2ne
  rw [e, Valuation.map_neg, map_div₀, map_mul, hdetA, hu, mul_one, div_self hv2']

/-- The padded frame matrix. -/
def padM {m : ℕ} (P : Matrix (Fin N) (Fin m) Fv) : Matrix (Fin N ⊕ Fin 1) (Fin m) Fv :=
  Matrix.of fun a j => Sum.elim (fun i => P i j) (fun _ => 0) a

/-- The reindexing $\mathrm{Fin}\,N \oplus \mathrm{Fin}\,1 \simeq \mathrm{Fin}(N+1)$. -/
abbrev eGlue : Fin N ⊕ Fin 1 ≃ Fin (N + 1) := finSumFinEquiv

theorem glue_frame (S : Matrix (Fin N) (Fin N) Fv) (l : Fin N) {m : ℕ} {P R : Matrix (Fin N) (Fin m) Fv}
    (hf : IsWallFrame Fv S P R) :
    IsWallFrame Fv ((glueS S l).submatrix eGlue.symm eGlue.symm) ((padM P).submatrix eGlue.symm id)
      ((padM R).submatrix eGlue.symm id) := by
  obtain ⟨hTR, hinj, hspan⟩ := hf
  have hone : (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Fv) - (glueS S l).submatrix eGlue.symm eGlue.symm =
      (1 - glueS S l).submatrix eGlue.symm eGlue.symm := by
    ext a b
    simp [Matrix.one_apply, Matrix.sub_apply, submatrix_apply, eGlue.symm.injective.eq_iff]
  have hpad : (1 - glueS S l) * padM R = padM P := by
    ext a j
    rcases a with i | i
    · rw [← hTR]
      simp only [Matrix.mul_apply, Fintype.sum_sum_type, padM, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
        mul_zero, Finset.sum_const_zero, add_zero, Matrix.sub_apply, glueS, fromBlocks_apply₁₁,
        Matrix.one_apply, Sum.inl.injEq]
    · simp only [Matrix.mul_apply, Fintype.sum_sum_type, padM, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
        mul_zero, Finset.sum_const_zero, add_zero, Matrix.sub_apply, glueS, fromBlocks_apply₂₁,
        Matrix.one_apply, Matrix.zero_apply, reduceCtorEq, if_false, sub_zero, zero_mul, sub_self]
  have hPv : ∀ (c : Fin m → Fv) k, ((padM P).submatrix eGlue.symm id *ᵥ c) k = (padM P *ᵥ c) (eGlue.symm k) :=
    fun c k => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hone, submatrix_mul_equiv, hpad]
  · intro c hc
    apply hinj c
    funext i
    have := congrFun hc (eGlue (Sum.inl i))
    rw [hPv, Equiv.symm_apply_apply] at this
    simpa [padM, mulVec, dotProduct] using this
  · intro z
    set x : Fin N → Fv := fun i => z (eGlue (Sum.inl i))
    set t : Fv := z (eGlue (Sum.inr 0))
    obtain ⟨c, hc⟩ := hspan (x + (t / 2) • Pi.single l 1)
    refine ⟨c, ?_⟩
    rw [hone, submatrix_mulVec_equiv]
    funext k
    rw [hPv]
    obtain ⟨a, rfl⟩ := eGlue.surjective k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases a with i | i
    · have h1 := congrFun hc i
      simp only [padM, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl] at h1 ⊢
      rw [← h1]
      simp only [Fintype.sum_sum_type, Matrix.sub_apply, glueS, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        Matrix.one_apply, Sum.inl.injEq, reduceCtorEq, if_false, Function.comp_apply, Equiv.symm_symm,
        Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, Fin.fin_one_eq_zero, zero_sub]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.sub_apply,
        Matrix.one_apply, x, t]
      split_ifs <;> ring
    · simp only [padM, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
        Fintype.sum_sum_type, Matrix.sub_apply, glueS, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply,
        reduceCtorEq, if_false, Matrix.zero_apply, sub_zero, Finset.univ_unique, Finset.sum_singleton,
        Fin.fin_one_eq_zero, Sum.inr.injEq, if_true, sub_self, add_zero]

theorem glue_gram (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv) {m : ℕ}
    (P R : Matrix (Fin N) (Fin m) Fv) :
    ((padM P).submatrix eGlue.symm id)ᵀ * (glueA A l u).submatrix eGlue.symm eGlue.symm *
      (padM R).submatrix eGlue.symm id = Pᵀ * A * R := by
  rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, transpose_apply, padM, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, glueA, fromBlocks_apply₁₁]

end GlueFinal

end Glue2

open Glue2 in
/-- **The glue lemma over $\mathbb Q_2$** (`Glue.exists_sq_valued_wallDet_glue` for an arbitrary matrix and an
arbitrary special index): let $A$ be a symmetric $N \times N$ matrix over $\mathbb Q_2$ with integral entries and
$A_{ii}/2$ integral, $l$ an index with $A_{il} = 0$ for $i \ne l$ and $A_{ll} = 2u$, $u$ a unit, and
$\lvert\det A\rvert = \lvert 2\rvert$ (so $A = E \perp \langle 2u\rangle$, $E$ even unimodular). If $S$ is integral
with $S^{\mathsf T}AS = A$ and $\det S = 1$, every Wall frame $(P, R)$ of $S$ has $\lvert\det(P^{\mathsf T}AR)\rvert$
a square. *Proof.* $Se_l \equiv e_l \pmod 2$ (`congr_col`), so $S \oplus 1$ preserves the even unimodular lattice $K$
with basis $e_0, \dots, e_{N-1}, (e_l + f)/2$ in $L \perp \langle -2u\rangle$; the padded frame is a Wall frame of
$S \oplus 1$ on $K$ with the same Gram matrix, and the core lemma `exists_sq_valued_wallDet'` applies. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers of E ⊥ ⟨2u⟩, any basis)"]
theorem exists_sq_valued_wallDet_glue' {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) (l : Fin N) (u : Fv)
    (hA : Aᵀ = A) (hint : ∀ i j, Valued.v (A i j) ≤ 1) (heven : ∀ i, Valued.v (A i i / 2) ≤ 1)
    (hl : ∀ i, i ≠ l → A i l = 0) (hll : A l l = 2 * u) (hu : Valued.v u = 1)
    (hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ)) (hdetA : Valued.v A.det = Valued.v (2 : Fv))
    (S : Matrix (Fin N) (Fin N) Fv) (hS : ∀ i j, Valued.v (S i j) ≤ 1) (hSA : Sᵀ * A * S = A)
    (hdet : S.det = 1) {m : ℕ} {P R : Matrix (Fin N) (Fin m) Fv} (hf : IsWallFrame Fv S P R) :
    ∃ γ : ℤᵐ⁰, Valued.v (Pᵀ * A * R).det = γ ^ 2 := by
  set A2 := (glueA A l u).submatrix eGlue.symm eGlue.symm
  set S2 := (glueS S l).submatrix eGlue.symm eGlue.symm
  have hA2 : A2ᵀ = A2 := by
    simp only [A2, transpose_submatrix, glueA, fromBlocks_transpose, hA, transpose_transpose, transpose_zero]
  have hint2 : ∀ i j, Valued.v (A2 i j) ≤ 1 := by
    intro i j
    obtain ⟨a, rfl⟩ := eGlue.surjective i
    obtain ⟨b, rfl⟩ := eGlue.surjective j
    rcases a with i | i <;> rcases b with j | j <;> simp only [A2, glueA, submatrix_apply,
      Equiv.symm_apply_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      lcol, Matrix.of_apply, Matrix.zero_apply, transpose_apply]
    · exact hint i j
    · split_ifs
      · rw [hu]
      · simp
    · split_ifs
      · rw [hu]
      · simp
    · simp
  have hdet2 : Valued.v A2.det = 1 := by
    rw [det_submatrix_equiv_self]; exact valued_det_glueA A l u hA hl hll hu hdetA
  have heven2 : ∀ k, Valued.v (A2 k k / 2) ≤ 1 := by
    intro k
    obtain ⟨a, rfl⟩ := eGlue.surjective k
    rcases a with i | i
    · simpa [A2, glueA] using heven i
    · simp [A2, glueA]
  have hcong := congr_col A l u hA hint heven hl hll hu hv2 hdetA S hS hSA hdet
  have hS2 : ∀ i j, Valued.v (S2 i j) ≤ 1 := by
    intro i j
    obtain ⟨a, rfl⟩ := eGlue.surjective i
    obtain ⟨b, rfl⟩ := eGlue.surjective j
    rcases a with i | i <;> rcases b with j | j <;> simp only [S2, glueS, submatrix_apply,
      Equiv.symm_apply_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.of_apply, Matrix.zero_apply, Matrix.one_apply]
    · exact hS i j
    · exact hcong i
    · simp
    · split_ifs <;> simp
  have hSA2 : S2ᵀ * A2 * S2 = A2 := by
    simp only [S2, A2, transpose_submatrix, submatrix_mul_equiv, glueS_orth A l u hA hl hll S hSA]
  obtain ⟨γ, hγ⟩ := exists_sq_valued_wallDet' A2 hA2 hint2 hdet2 heven2 S2 hS2 hSA2 (glue_frame S l hf)
  exact ⟨γ, by rw [← glue_gram A l u P R]; exact hγ⟩


/-! ### The shape and the upper bound -/

section Shape

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n}

/-- **The shape $L_2 = 2^k(E \perp \langle 2u\rangle)$**, $E$ even unimodular, $u$ a unit: for some basis
$b_k = \gamma e_k$ of $L_2$ (`loc v L.1 = locAct v γ (std v)`), some $c \in \mathbb Q_2^\times$ and some index $l$,
the matrix $A = cG$, $G$ = `locGram Q v γ` the Gram matrix of $B$, has (i) integral entries, (ii) $A_{kk}/2$
integral for every $k$, (iii) $A_{il} = 0$ for $i \ne l$ ($b_l$ spans an orthogonal summand), (iv) $A_{ll}/2$ a unit
(the summand is $\langle 2u\rangle$, $u = A_{ll}/2$), and (v) $\lvert\det A\rvert = \lvert 2\rvert$ (so the
complement $E$ of $b_l$, with the form $cB$, is even unimodular). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic Jordan shape: an even unimodular constituent and ⟨2u⟩, scaled)"]
def IsScaledEvenUnimodularPerpTwoUnit (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (c : v.adicCompletion ℚ) (l : Fin n),
    loc v L.1 = locAct v γ (std v) ∧ c ≠ 0 ∧
    (∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1) ∧ (∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) ∧
    (∀ i, i ≠ l → locGram Q v γ i l = 0) ∧ Valued.v (c * locGram Q v γ l l / 2) = 1 ∧
    Valued.v (c • locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ)

/-- **The upper bound for $L_2 = 2^k(E \perp \langle 2u\rangle)$**: every element of $\theta(O^+(L_2))$ has even
order (Wall's formula and the glue lemma `exists_sq_valued_wallDet_glue'` for $A = cG$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers of a scaled E ⊥ ⟨2u⟩ have even order)"]
theorem even_log_of_scaledEvenUnimodularPerpTwoUnit (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {c : Fv} (hc : c ≠ 0) (l : Fin n)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ≠ l → locGram Q v γ i l = 0) (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (c • locGram Q v γ).det = Valued.v (2 : Fv)) (B : Fvˣ)
    (hB : B ∈ localSpinorNormGroup Q hQ v L) : ∃ k : ℤ, Valued.v (B : Fv) = exp (2 * k) := by
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hB
  set G := locGram Q v γ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val
  obtain ⟨hS', hS'G⟩ := conj_integral_orth γ hγ hσL
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S'
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  set A := c • G
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hSA : S'ᵀ * A * S' = A := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul]
    rw [show S'ᵀ * G * S' = G from hS'G]
  have h1 : (mat Q Fv σ).det = 1 := hσS
  have hS'det : S'.det = 1 := by
    have hgig : (γ⁻¹ : GL (Fin n) Fv).val * γ.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg Matrix.det hgig
    rw [det_mul, det_one] at this
    simp only [S', det_mul, h1, mul_one]
    exact this
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet_glue' A l (c * G l l / 2) hA
    (fun i j => by simpa [A] using hint i j) (fun i => by simpa [A, mul_div_assoc] using heven i)
    (fun i hi => by simp [A, G, hl i hi]) (by simp only [A, Matrix.smul_apply, smul_eq_mul]; ring) hu
    (valued_two_dyadic v h2) hdet S' hS' hSA hS'det hf
  have hm : Even m := by
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  set d := (Pᵀ * G * R).det
  have hAd : (Pᵀ * A * R).det = c ^ (m' + m') * d := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin, d]
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have hvd : Valued.v d = (δ * (Valued.v c ^ m')⁻¹) ^ 2 := by
    have h := hδ
    rw [hAd, map_mul, map_pow] at h
    have hcm : Valued.v c ^ (m' + m') ≠ 0 := pow_ne_zero _ hvc
    rw [mul_pow, inv_pow, ← h, ← pow_mul, show m' * 2 = m' + m' by ring]
    field_simp
  set δ' := δ * (Valued.v c ^ m')⁻¹
  have hδ'0 : δ' ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero, Valuation.zero_iff] at hvd; exact hne hvd
  rw [hθ, sqClassOf_of_ne_zero hne] at hσB
  set D : Fvˣ := Units.mk0 d hne
  have h1' : SqClass.mk (B⁻¹ * D) = 1 := by
    rw [SqClass.mk_mul, hσB, ← SqClass.mk_mul, inv_mul_cancel]
    rfl
  obtain ⟨y, hy⟩ := (SqClass.mk_eq_one_iff (B⁻¹ * D)).mp h1'
  have hBe : (B : Fv) = d * ((y : Fv) ^ 2)⁻¹ := by
    have : B = D * (y ^ 2)⁻¹ := by rw [hy]; group
    rw [this]; simp [D]
  have hsv : Valued.v (y : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  refine ⟨log δ' - log (Valued.v (y : Fv)), ?_⟩
  rw [hBe, map_mul, map_inv₀, map_pow, hvd, ← exp_log hδ'0, ← exp_log hsv, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.log_exp, WithZero.log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ### Root vectors -/

/-- **Root vectors from an off-diagonal unit entry**: if $A = cG$ has integral entries, $A_{kk}/2$ integral for every
$k$, and $A_{i_0j}$ is a unit, then for every unit $w$ of $\mathbb Z_2$ there is a $2$-adic root vector of norm
$c^{-1}w$. *Proof* as in `exists_rootVector_of_scaledEvenUnimodular` ($j \ne i_0$ as $A_{i_0i_0}$ is even; the
binary sublattice spanned by $b_{i_0}, b_j$ is $c^{-1}(\alpha s^2 + \beta st + \delta t^2)$ with $\beta$ a unit). -/
theorem exists_rootVector_of_unit_entry (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (i0 j : Fin n)
    (hj : Valued.v (c * locGram Q v γ i0 j) = 1) {w : Fv} (hw : Valued.v w = 1) :
    ∃ x, IsRootVector Q L v x ∧ Q.evalIn Fv x = c⁻¹ * w := by
  set G := locGram Q v γ
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  have hji0 : j ≠ i0 := by
    rintro rfl
    have h := heven j
    have e : c * G j j = 2 * (c * G j j / 2) := by field_simp
    rw [e, map_mul, hv2] at hj
    have : exp (-1 : ℤ) * Valued.v (c * G j j / 2) ≤ exp (-1 : ℤ) :=
      (mul_le_mul' le_rfl h).trans_eq (mul_one _)
    rw [hj] at this
    exact absurd this (by rw [← exp_zero, exp_le_exp]; omega)
  set β := c * G i0 j with hβ
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hj; exact zero_ne_one hj
  have hα1 : Valued.v (c * G i0 i0 / 2) ≤ 1 := heven i0
  have hδ1 : Valued.v (c * G j j / 2 / β ^ 2) ≤ 1 := by
    rw [map_div₀, map_pow, hj, one_pow, div_one]; exact heven j
  have hw0 : IsUnit (toO v w hw.le) := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hw
  obtain ⟨s, t', hst⟩ := exists_binary_value h2 (toO v _ hα1) (toO v _ hδ1) _ hw0
  have hst' : c * G i0 i0 / 2 * (s : Fv) ^ 2 + (s : Fv) * (t' : Fv) + c * G j j / 2 / β ^ 2 * (t' : Fv) ^ 2 = w := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hst
    push_cast at this
    exact this
  set t : Fv := (t' : Fv) / β
  have ht1 : Valued.v t ≤ 1 := by rw [map_div₀, hj, div_one]; exact vle_one t'
  set d : Fin n → Fv := Pi.single i0 (s : Fv) + Pi.single j t with hd
  have hGd : ∀ m, (G *ᵥ d) m = G m i0 * s + G m j * t := by
    intro m
    simp [hd, Matrix.mulVec_add, Matrix.mulVec_single]
    ring
  have hdot : ∀ e : Fin n → Fv, d ⬝ᵥ e = s * e i0 + t * e j := fun e => by
    rw [hd, add_dotProduct, single_dotProduct, single_dotProduct]
  have hji : G j i0 = G i0 j := locGram_symm' γ j i0
  have hdstd : d ∈ std v := (std v).add_mem (single_mem_std i0 (vle_one s)) (single_mem_std j ht1)
  have hQx : Q.evalIn Fv (γ.val *ᵥ d) = c⁻¹ * w := by
    have h2Q := two_mul_evalIn_locGram (Q := Q) (v := v) γ d
    rw [hdot, hGd, hGd, hji] at h2Q
    have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
    have hQd : Q.evalIn Fv (γ.val *ᵥ d) =
        ((s : Fv) * (G i0 i0 * s + G i0 j * t) + t * (G i0 j * s + G j j * t)) / 2 := by
      rw [← h2Q]; field_simp
    have hdt : t * β = t' := by simp only [t]; field_simp
    have hG0 : G i0 j ≠ 0 := fun h => hβ0 (by rw [hβ, h, mul_zero])
    rw [hQd, ← hst', ← hdt, hβ]
    field_simp
    ring
  have hcw : c⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hc) (fun h => by rw [h, map_zero] at hw; exact zero_ne_one hw)
  have hx0 : Q.evalIn Fv (γ.val *ᵥ d) ≠ 0 := by rw [hQx]; exact hcw
  refine ⟨γ.val *ᵥ d, ⟨hx0, symm_mem_of_gram L γ hγ hdstd hx0 fun m => ?_⟩, hQx⟩
  rw [hQx, map_mul, hw, mul_one, hGd]
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have key : Valued.v (c * (G m i0 * s + G m j * t)) ≤ 1 := by
    rw [show c * (G m i0 * s + G m j * t) = (c * G m i0) * s + (c * G m j) * t by ring]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul]; exact mul_le_one' (hint m i0) (vle_one s)
    · rw [map_mul]; exact mul_le_one' (hint m j) ht1
  rw [map_mul] at key
  rw [map_inv₀]
  calc Valued.v (G m i0 * ↑s + G m j * t)
      = (Valued.v c)⁻¹ * (Valued.v c * Valued.v (G m i0 * ↑s + G m j * t)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hvc, one_mul]
    _ ≤ (Valued.v c)⁻¹ * 1 := mul_le_mul' le_rfl key
    _ = (Valued.v c)⁻¹ := mul_one _

/-- **Every unit class is in the root group when $A = cG$ has an off-diagonal unit entry** (root vectors of norms
$c^{-1}u$ and $c^{-1}$, `exists_rootVector_of_unit_entry`). -/
theorem units_le_rootGroup_of_unit_entry (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (i0 j : Fin n)
    (hj : Valued.v (c * locGram Q v γ i0 j) = 1) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  intro u hu
  obtain ⟨x, hxr, hx⟩ := exists_rootVector_of_unit_entry h2 γ hγ hc hint heven i0 j hj hu
  obtain ⟨y, hyr, hy⟩ := exists_rootVector_of_unit_entry h2 γ hγ hc hint heven i0 j hj (map_one Valued.v)
  have hmem := sqClassOf_mul_mem_rootGroup hxr hyr
  have e : Q.evalIn Fv x * Q.evalIn Fv y = c⁻¹ ^ 2 * u := by rw [hx, hy]; ring
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu; exact zero_ne_one hu
  rwa [e, sqClassOf_sq_mul (inv_ne_zero hc) hu0] at hmem

/-- **Theorem 18, "only if", at $p = 2$ for $L_2 = 2^k(E \perp \langle 2u\rangle)$, $E$ even unimodular, $u$ a
unit** (Conway–Sloane §9.5, p. 391): every $A \in \theta(O^+(L_2))$ is, up to squares, the product of the norms of
two $2$-adic root vectors. Indeed $\theta(O^+(L_2)) \subseteq \mathbb Z_2^\times\mathbb Q_2^{\times 2}$
(`even_log_of_scaledEvenUnimodularPerpTwoUnit`), and for $n \ge 2$ a row $i_0 \ne l$ of the unimodular matrix $E$
has a unit entry, so every unit class lies in the root group (`units_le_rootGroup_of_unit_entry`); in dimension
$\le 1$ the group is trivial. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': L₂ a scaled E ⊥ ⟨2u⟩, E even unimodular)"]
theorem theorem18OnlyIf_of_scaledEvenUnimodularPerpTwoUnit (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hshape : IsScaledEvenUnimodularPerpTwoUnit Q L v) : Theorem18OnlyIf Q L v hQ := by
  obtain ⟨γ, c, l, hγ, hc, hint, heven, hl, hu, hdet⟩ := hshape
  by_cases hn : n ≤ 1
  · exact theorem18OnlyIf_of_le_one hQ hn
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i0, hi0⟩ := exists_ne l
  set G := locGram Q v γ
  set A := c • G
  have hAint : ∀ i j, Valued.v (A i j) ≤ 1 := fun i j => by simpa [A] using hint i j
  have hAl : ∀ i, i ≠ l → A i l = 0 := fun i hi => by simp [A, G, hl i hi]
  have hAll : A l l = 2 * (c * G l l / 2) := by simp only [A, Matrix.smul_apply, smul_eq_mul]; ring
  have hA'det := Glue2.valued_det_colOne A l _ hAl hAll hu (valued_two_dyadic v h2) hdet
  obtain ⟨j, hj⟩ := exists_unit_entry (Glue2.colOne A l) (Glue2.colOne_integral A l hAint) hA'det i0
  have hjl : j ≠ l := by
    rintro rfl
    simp [Glue2.colOne, updateCol_apply, hi0] at hj
  have hj' : Valued.v (c * G i0 j) = 1 := by
    simpa [Glue2.colOne, updateCol_ne hjl, A] using hj
  have hunits := units_le_rootGroup_of_unit_entry h2 γ hγ hc hint heven i0 j hj'
  intro B hB
  obtain ⟨k, hk⟩ := even_log_of_scaledEvenUnimodularPerpTwoUnit hQ h2 γ hγ hc l hint heven hl hu hdet B hB
  have hmem := sqClassOf_mem_of_even h2 hunits B.ne_zero k hk
  rw [sqClassOf_of_ne_zero B.ne_zero, Units.mk0_val] at hmem
  exact hmem

/-! ### The enlarged shape predicate and the smaller residual statement -/

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, second version**: the shapes of
`Theorem18DyadicCovered` ($n \le 1$, generated by root reflections, scaled even unimodular, or root group full), or
$L_2 = 2^k(E \perp \langle 2u\rangle)$ with $E$ even unimodular and $u$ a unit
(`IsScaledEvenUnimodularPerpTwoUnit`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, second version)"]
def Theorem18DyadicCovered2 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered Q L v ∨ IsScaledEvenUnimodularPerpTwoUnit Q L v

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, second version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, second version)"]
theorem theorem18OnlyIf_of_covered2 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered2 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | hc
  · exact theorem18OnlyIf_of_covered hQ h2 hc
  · exact theorem18OnlyIf_of_scaledEvenUnimodularPerpTwoUnit hQ h2 hc

end Shape

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, second version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape
covered by `Theorem18DyadicCovered2`, every $2$-adically automorphous number $A \in \theta(O^+(L_2))$ is, up to
squares, the product of the norms of an even number of $2$-adic root vectors (`Theorem18OnlyIf`).

It implies `Theorem18DyadicResidual` (`theorem18DyadicResidual_of_residual2`), hence `Theorem18Dyadic`. The remaining
lattices are those with $n \ge 2$ outside the shapes of `Theorem18DyadicCovered` which are also not of the form
$2^k(E \perp \langle 2u\rangle)$ with $E$ even unimodular; for them the computation of $\theta(O^+(L_2))$ from a
Jordan splitting (Earnest–Hsia 1975) is needed. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, second version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual2 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered2 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The first residual statement from the second**: on the new shape the condition is proved
(`theorem18OnlyIf_of_scaledEvenUnimodularPerpTwoUnit`), elsewhere it is `Theorem18DyadicResidual2`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the second residual statement)"]
theorem theorem18DyadicResidual_of_residual2 (h : Theorem18DyadicResidual2) : Theorem18DyadicResidual where
  exists_rootVectors n Q hQ L v h2 hnc := by
    by_cases hs : IsScaledEvenUnimodularPerpTwoUnit Q L v
    · exact theorem18OnlyIf_of_scaledEvenUnimodularPerpTwoUnit hQ h2 hs
    · refine h.exists_rootVectors n Q hQ L v h2 ?_
      rintro (hc | hc)
      exacts [hnc hc, hs hc]

/-- **`Theorem18Dyadic` from the second residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, second version)"]
theorem theorem18Dyadic_of_residual2 (h : Theorem18DyadicResidual2) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual (theorem18DyadicResidual_of_residual2 h)

/-- **Conway–Sloane's Theorem 18 from the second residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual2`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, second version)"]
theorem theorem18Statement_of_residual2 (h : Theorem18DyadicResidual2) : Theorem18Statement :=
  theorem18Statement_of_residual (theorem18DyadicResidual_of_residual2 h)

end QuadFormsKB.ConwaySloane
