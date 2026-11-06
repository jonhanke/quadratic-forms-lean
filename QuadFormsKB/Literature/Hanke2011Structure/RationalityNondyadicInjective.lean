/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicDensity

/-!
# Paper 6, Theorem 5.4 at $\mathfrak p \nmid 2$ of a number field: the symbol of a diagonal genus is an invariant

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24 (O'Meara 92:2).

**Main result** (`symC_eq_of_isometricGL`).  Let $R$ be a discrete valuation ring with finite residue field and
uniformizer $\pi \nmid 2$, $c \in R^\times$ with $\chi(\bar c) = -1$.  If two diagonal forms
$D(z,x) = \operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$ and $D(z',x')$ are $\mathrm{GL}_n(R)$-equivalent
(`Siegel.IsometricGL`), then their symbols agree: $\#\{i : z_i = k\} = \#\{i : z'_i = k\}$ and
$\prod_{z_i=k}x_i = \prod_{z'_i=k}x'_i$ for every $k$ (`RatOdd`'s `symC z x = symC z' x'`).  This is the "easy half" of
O'Meara 92:2 for a non-dyadic local field (the invariance of the Jordan type and of the unit discriminant classes of
the Jordan components), proved here by elementary linear algebra and not by the lattice-theoretic route.

*Proof.* Let $A = \operatorname{diag}(d)$, $A' = \operatorname{diag}(d') = U^{\mathsf T}AU$ with $U \in \mathrm{GL}_n(R)$
(Hessians, with the common factor $2$ cancelled).  Fix a scale $k$ and put $m_i = \max(k-z_i, 0)$,
$D = \operatorname{diag}(\pi^{m_i})$, $D'$ likewise.  The entries of $UD'$ are divisible by the appropriate powers of
$\pi$, so $UD' = Dh$ with $h$ integral (`exists_h`); the same argument for $U^{-1}$ gives $h'$ with $hh' = 1$, so $h
\in \mathrm{GL}_n(R)$.  Then $M_k' = h^{\mathsf T}M_kh$ for $M_k = \operatorname{diag}(\pi^{|z_i-k|}u_i)$
(`Mk_congr`): the "$k$-th graded Gram matrix".  Reducing modulo $\pi$ gives congruent diagonal matrices over the residue
field whose nonzero entries are exactly those with $z_i = k$, namely the residues $\overline{\operatorname{rep}(x_i)}$.
Over a field, congruent diagonal matrices have the same number of nonzero entries (rank) and the products of the nonzero
entries differ by a nonzero square (`field_diag_congr`: compare the principal minors on the supports).  Applying the
quadratic character gives the equality of $\prod_{z_i=k}x_i$.

Indices are 0-based.
-/

open Finset Matrix

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure.RatOdd
  QuadFormsKB.ConwaySloane QuadFormsKB.Odd7

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

/-! ### Congruent diagonal matrices over a field -/

section Field

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

/-- Sum over the support of a vector vanishing off the support. -/
theorem sum_support (a : Fin n → K) (g : Fin n → K) (hg : ∀ l, a l = 0 → g l = 0) :
    ∑ l, g l = ∑ l : {l // a l ≠ 0}, g l := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => a l ≠ 0) (fun x => by simp) g]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => hg l ?_
  simpa using hl

theorem gram_entry {ι κ : Type*} [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] (a : ι → S)
    (h : Matrix ι κ S) (j l : κ) :
    (hᵀ * Matrix.diagonal a * h) j l = ∑ i, h i j * a i * h i l := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal]
  simp

/-- **Congruent diagonal matrices over a field** have the same number of nonzero entries, and the products of the
nonzero entries differ by a nonzero square. -/
theorem field_diag_congr (a a' : Fin n → K) (h : Matrix (Fin n) (Fin n) K) (hh : h.det ≠ 0)
    (heq : Matrix.diagonal a' = hᵀ * Matrix.diagonal a * h) :
    Fintype.card {i // a i ≠ 0} = Fintype.card {j // a' j ≠ 0} ∧
      ∃ t : K, t ≠ 0 ∧ ∏ j : {j // a' j ≠ 0}, a' j = t ^ 2 * ∏ i : {i // a i ≠ 0}, a i := by
  have hU : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hUt : IsUnit hᵀ.det := by rwa [Matrix.det_transpose]
  have hrank : (Matrix.diagonal a').rank = (Matrix.diagonal a).rank := by
    rw [heq, Matrix.rank_mul_eq_left_of_isUnit_det h _ hU, Matrix.rank_mul_eq_right_of_isUnit_det hᵀ _ hUt]
  rw [Matrix.rank_diagonal, Matrix.rank_diagonal] at hrank
  have hcard := hrank.symm
  refine ⟨hcard, ?_⟩
  let e := Fintype.equivOfCardEq hcard
  let B : Matrix {i // a i ≠ 0} {i // a i ≠ 0} K := fun i i' => h i (e i')
  have key : (Matrix.diagonal fun i' : {i // a i ≠ 0} => a' (e i')) =
      Bᵀ * Matrix.diagonal (fun i : {i // a i ≠ 0} => a i) * B := by
    ext i' i''
    have h0 := congrFun (congrFun heq (e i')) (e i'')
    rw [gram_entry] at h0
    rw [gram_entry]
    rw [sum_support a (fun l => h l (e i') * a l * h l (e i'')) (fun l hl => by simp [hl])] at h0
    rw [← h0]
    simp only [Matrix.diagonal_apply, Subtype.ext_iff.symm, e.injective.eq_iff]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hdet
  have hprod : ∏ j : {j // a' j ≠ 0}, a' j = ∏ i' : {i // a i ≠ 0}, a' (e i') :=
    (Equiv.prod_comp e (fun j : {j // a' j ≠ 0} => a' j)).symm
  refine ⟨B.det, ?_, ?_⟩
  · intro h0
    have hne : ∏ j : {j // a' j ≠ 0}, a' j ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => j.2
    apply hne
    rw [hprod, hdet, h0]; ring
  · rw [hprod, hdet]; ring

/-- Filter form of `field_diag_congr`. -/
theorem field_diag_congr' (a a' : Fin n → K) (h : Matrix (Fin n) (Fin n) K) (hh : h.det ≠ 0)
    (heq : Matrix.diagonal a' = hᵀ * Matrix.diagonal a * h) :
    (Finset.univ.filter fun i => a i ≠ 0).card = (Finset.univ.filter fun j => a' j ≠ 0).card ∧
      ∃ t : K, t ≠ 0 ∧ ∏ j ∈ Finset.univ.filter (fun j => a' j ≠ 0), a' j =
        t ^ 2 * ∏ i ∈ Finset.univ.filter (fun i => a i ≠ 0), a i := by
  obtain ⟨h1, t, ht, h2⟩ := field_diag_congr a a' h hh heq
  refine ⟨?_, t, ht, ?_⟩
  · rw [Fintype.card_subtype, Fintype.card_subtype] at h1
    exact h1
  · rw [Finset.prod_subtype (p := fun j => a' j ≠ 0) (Finset.univ.filter fun j => a' j ≠ 0)
        (fun x => by simp) a',
      Finset.prod_subtype (p := fun i => a i ≠ 0) (Finset.univ.filter fun i => a i ≠ 0)
        (fun x => by simp) a]
    exact h2

end Field

/-! ### The graded Gram matrices -/

section Mat

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
  {n : ℕ}

/-- $|z - k|$ as a natural number. -/
def absd (z k : ℕ) : ℕ := (z - k) + (k - z)

include hπ in
/-- **Divisibility** (the heart of the comparison of two diagonalizations): if
$A' = \operatorname{diag}(\pi^{z'_j}u'_j) = U^{\mathsf T}AU$, $A = \operatorname{diag}(\pi^{z_i}u_i)$ with $u_i$ units
and $UV = 1$, then for every $k$ there is an integral $h$ with $\pi^{(k-z_i)_+}h_{ij} = U_{ij}\pi^{(k-z'_j)_+}$ (i.e.
$Dh = UD'$). -/
theorem exists_h {z z' : Fin n → ℕ} {u u' : Fin n → R} (hu : ∀ i, IsUnit (u i)) (k : ℕ)
    (U V : Matrix (Fin n) (Fin n) R) (hUV : U * V = 1)
    (hA : Matrix.diagonal (fun j => π ^ z' j * u' j) =
      Uᵀ * Matrix.diagonal (fun i => π ^ z i * u i) * U) :
    ∃ h : Matrix (Fin n) (Fin n) R, ∀ i j, π ^ (k - z i) * h i j = U i j * π ^ (k - z' j) := by
  have h1 : Vᵀ * Matrix.diagonal (fun j => π ^ z' j * u' j) =
      Matrix.diagonal (fun i => π ^ z i * u i) * U := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hUV, Matrix.transpose_one,
      Matrix.one_mul]
  have hdiv : ∀ i j, π ^ (k - z i) ∣ U i j * π ^ (k - z' j) := by
    intro i j
    have hij := congrFun (congrFun h1 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    simp only [Matrix.transpose_apply] at hij
    -- hij : V j i * (π^z' j * u' j) = (π^z i * u i) * U i j
    by_cases hzk : z i ≤ k
    · have hX : π ^ k ∣ π ^ z i * (u i * (U i j * π ^ (k - z' j))) := by
        have e : π ^ z i * (u i * (U i j * π ^ (k - z' j))) =
            π ^ (k - z' j + z' j) * (V j i * u' j) := by
          rw [pow_add]
          calc π ^ z i * (u i * (U i j * π ^ (k - z' j))) = π ^ (k - z' j) * (π ^ z i * u i * U i j) := by ring
            _ = π ^ (k - z' j) * (V j i * (π ^ z' j * u' j)) := by rw [hij]
            _ = _ := by ring
        rw [e]
        exact (pow_dvd_pow π (by omega)).trans (dvd_mul_right _ _)
      have e2 : π ^ k = π ^ z i * π ^ (k - z i) := by rw [← pow_add]; congr 1; omega
      rw [e2] at hX
      have hX2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hX
      exact (IsUnit.dvd_mul_left (hu i)).1 hX2
    · have : k - z i = 0 := by omega
      rw [this, pow_zero]; exact one_dvd _
  choose h hh using fun i j => hdiv i j
  exact ⟨h, fun i j => by rw [hh i j]⟩

include hπ in
/-- **The graded Gram matrices are congruent**: with $Dh = UD'$ and $A' = U^{\mathsf T}AU$,
$\operatorname{diag}(\pi^{|z'_j-k|}u'_j) = h^{\mathsf T}\operatorname{diag}(\pi^{|z_i-k|}u_i)\,h$. -/
theorem Mk_congr {z z' : Fin n → ℕ} {u u' : Fin n → R} (k : ℕ)
    (U h : Matrix (Fin n) (Fin n) R)
    (hh : ∀ i j, π ^ (k - z i) * h i j = U i j * π ^ (k - z' j))
    (hA : Matrix.diagonal (fun j => π ^ z' j * u' j) =
      Uᵀ * Matrix.diagonal (fun i => π ^ z i * u i) * U) :
    Matrix.diagonal (fun j => π ^ absd (z' j) k * u' j) =
      hᵀ * Matrix.diagonal (fun i => π ^ absd (z i) k * u i) * h := by
  have hk : π ^ k ≠ 0 := pow_ne_zero _ hπ.ne_zero
  ext j l
  apply mul_left_cancel₀ hk
  rw [gram_entry]
  have hexp : ∀ w : ℕ, π ^ k * π ^ absd w k = π ^ (k - w) * π ^ w * π ^ (k - w) := by
    intro w
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    unfold absd
    omega
  have step : ∀ i, π ^ k * (h i j * (π ^ absd (z i) k * u i) * h i l) =
      (U i j * π ^ (k - z' j)) * (π ^ z i * u i) * (U i l * π ^ (k - z' l)) := by
    intro i
    rw [← hh i j, ← hh i l]
    calc π ^ k * (h i j * (π ^ absd (z i) k * u i) * h i l)
        = (π ^ k * π ^ absd (z i) k) * (h i j * u i * h i l) := by ring
      _ = _ := by rw [hexp]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => step i]
  have hjl := congrFun (congrFun hA j) l
  rw [gram_entry] at hjl
  have e1 : ∑ i, U i j * π ^ (k - z' j) * (π ^ z i * u i) * (U i l * π ^ (k - z' l)) =
      π ^ (k - z' j) * π ^ (k - z' l) * ∑ i, U i j * (π ^ z i * u i) * U i l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, ← hjl, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hjl' : j = l
  · subst hjl'
    simp only [if_true]
    rw [← mul_assoc, hexp, show π ^ (k - z' j) * π ^ (k - z' j) * (π ^ z' j * u' j) =
      π ^ (k - z' j) * π ^ z' j * π ^ (k - z' j) * u' j by ring]
  · simp [hjl']

include hπ in
/-- If both $Dh = UD'$ and $D'h' = VD$ with $UV = 1$, then $hh' = 1$. -/
theorem h_mul_h' {z z' : Fin n → ℕ} (k : ℕ) (U V h h' : Matrix (Fin n) (Fin n) R) (hUV : U * V = 1)
    (hh : ∀ i j, π ^ (k - z i) * h i j = U i j * π ^ (k - z' j))
    (hh' : ∀ i j, π ^ (k - z' i) * h' i j = V i j * π ^ (k - z j)) : h * h' = 1 := by
  ext i j
  apply mul_left_cancel₀ (pow_ne_zero (k - z i) hπ.ne_zero)
  rw [Matrix.mul_apply, Finset.mul_sum]
  have : ∀ l, π ^ (k - z i) * (h i l * h' l j) = U i l * (V l j * π ^ (k - z j)) := by
    intro l
    rw [← mul_assoc, hh i l, mul_assoc, ← hh' l j]
  rw [Finset.sum_congr rfl fun l _ => this l]
  have e : ∑ l, U i l * (V l j * π ^ (k - z j)) = (U * V) i j * π ^ (k - z j) := by
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, hUV, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end Mat

/-! ### The symbol is an invariant of the genus -/

section Final

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {c : R} (hcU : IsUnit c) (hc : chiR c = -1)
  {n : ℕ}

/-- The residue of the $k$-th graded Gram entry $\pi^{|z_i-k|}\operatorname{rep}(x_i)$. -/
def gradedRes (π c : R) (z : Fin n → ℕ) (x : Fin n → ℤˣ) (k : ℕ) (i : Fin n) : IsLocalRing.ResidueField R :=
  IsLocalRing.residue R (π ^ absd (z i) k * repR c (x i))

include hπ hcU in
theorem gradedRes_ne_zero_iff (z : Fin n → ℕ) (x : Fin n → ℤˣ) (k : ℕ) (i : Fin n) :
    gradedRes π c z x k i ≠ 0 ↔ z i = k := by
  unfold gradedRes
  have hu : IsUnit (IsLocalRing.residue R (repR c (x i))) := (isUnit_repR hcU _).map _
  rw [map_mul, map_pow]
  have hπ0 : IsLocalRing.residue R π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  by_cases hzk : z i = k
  · have : absd (z i) k = 0 := by unfold absd; omega
    rw [this, pow_zero, one_mul]
    exact ⟨fun _ => hzk, fun _ => hu.ne_zero⟩
  · have : absd (z i) k ≠ 0 := by unfold absd; omega
    simp [hπ0, zero_pow this, hzk]

include hπ hcU in
theorem prod_gradedRes (z : Fin n → ℕ) (x : Fin n → ℤˣ) (k : ℕ) :
    ∏ i ∈ Finset.univ.filter (fun i => gradedRes π c z x k i ≠ 0), gradedRes π c z x k i =
      IsLocalRing.residue R (∏ i ∈ Finset.univ.filter (fun i => z i = k), repR c (x i)) := by
  rw [Finset.filter_congr (fun i _ => gradedRes_ne_zero_iff hπ hcU z x k i), map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hzk : z i = k := (Finset.mem_filter.1 hi).2
  have : absd (z i) k = 0 := by unfold absd; omega
  simp [gradedRes, this]

include hπ h2 hcU hc in
/-- **The symbol of a diagonal genus is an invariant** (O'Meara 92:2, Jordan type and discriminants of the Jordan
components, $\mathfrak p \nmid 2$): $\mathrm{GL}_n(R)$-equivalent diagonal forms $D(z,x)$, $D(z',x')$ have the same
symbol `symC`. -/
@[kb "omeara1963" "§92, 92:2, p. 247 (invariance of the Jordan type and discriminants, p ∤ 2; proved elementarily)"]
theorem symC_eq_of_isometricGL {z z' : Fin n → ℕ} {x x' : Fin n → ℤˣ}
    (h : Siegel.IsometricGL (QuadForm.diag (diagVec π c z x)) (QuadForm.diag (diagVec π c z' x'))) :
    symC z x = symC z' x' := by
  classical
  obtain ⟨g, hg⟩ := h
  have h2u : IsUnit (2 : R) := dvr_isUnit_of_not_dvd hπ h2
  have hdet : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set U := g.val with hU
  set V := U⁻¹ with hV
  have hUV : U * V = 1 := Matrix.mul_nonsing_inv U hdet
  have hVU : V * U = 1 := Matrix.nonsing_inv_mul U hdet
  have hVdet : IsUnit V.det := Matrix.isUnit_nonsing_inv_det U hdet
  have hu : ∀ i, IsUnit (repR c (x i)) := fun i => isUnit_repR hcU _
  have hu' : ∀ i, IsUnit (repR c (x' i)) := fun i => isUnit_repR hcU _
  -- the Hessian relation, with the factor 2 cancelled
  have hH := hessian_eq_of_eval (Q := QuadForm.diag (diagVec π c z x))
    (Q' := QuadForm.diag (diagVec π c z' x')) (U := U) (fun y => (hg y).symm)
  rw [Hanke2005.hessian_diag_gen, Hanke2005.hessian_diag_gen] at hH
  have hA : Matrix.diagonal (fun j => π ^ z' j * repR c (x' j)) =
      Uᵀ * Matrix.diagonal (fun i => π ^ z i * repR c (x i)) * U := by
    ext j l
    apply mul_left_cancel₀ h2u.ne_zero
    have := congrFun (congrFun hH j) l
    rw [gram_entry] at this
    rw [gram_entry, Finset.mul_sum]
    simp only [diagVec] at this
    calc (2 : R) * (Matrix.diagonal fun j => π ^ z' j * repR c (x' j)) j l
        = (Matrix.diagonal fun j => 2 * (π ^ z' j * repR c (x' j))) j l := by
          simp only [Matrix.diagonal_apply]; split_ifs <;> simp
      _ = ∑ i, U i j * (2 * (π ^ z i * repR c (x i))) * U i l := this
      _ = _ := Finset.sum_congr rfl fun i _ => by ring
  have hA' : Matrix.diagonal (fun j => π ^ z j * repR c (x j)) =
      Vᵀ * Matrix.diagonal (fun i => π ^ z' i * repR c (x' i)) * V := by
    rw [hA]
    have e : Vᵀ * (Uᵀ * Matrix.diagonal (fun i => π ^ z i * repR c (x i)) * U) * V =
        (Vᵀ * Uᵀ) * Matrix.diagonal (fun i => π ^ z i * repR c (x i)) * (U * V) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.transpose_mul, hUV, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  funext k
  obtain ⟨h, hh⟩ := exists_h hπ hu k U V hUV hA
  obtain ⟨h', hh'⟩ := exists_h hπ hu' k V U hVU hA'
  have hhh : h * h' = 1 := h_mul_h' hπ k U V h h' hUV hh hh'
  have hhdet : IsUnit h.det := Matrix.isUnit_det_of_right_inverse hhh
  have hM := Mk_congr hπ k U h hh hA
  have hM' := congrArg (fun M => M.map (IsLocalRing.residue R)) hM
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.diagonal_map (map_zero (IsLocalRing.residue R))] at hM'
  have hdetne : (h.map (IsLocalRing.residue R)).det ≠ 0 := by
    have e : (h.map (IsLocalRing.residue R)).det = IsLocalRing.residue R h.det :=
      (RingHom.map_det (IsLocalRing.residue R) h).symm
    rw [e]
    exact (hhdet.map _).ne_zero
  obtain ⟨hcard, t, ht, hprod⟩ := field_diag_congr' (gradedRes π c z x k) (gradedRes π c z' x' k)
    (h.map (IsLocalRing.residue R)) hdetne hM'
  rw [prod_gradedRes hπ hcU, prod_gradedRes hπ hcU] at hprod
  rw [Finset.filter_congr (fun i _ => gradedRes_ne_zero_iff hπ hcU z x k i),
    Finset.filter_congr (fun i _ => gradedRes_ne_zero_iff hπ hcU z' x' k i)] at hcard
  have hchi : chiR (∏ i ∈ Finset.univ.filter (fun i => z' i = k), repR c (x' i)) =
      chiR (∏ i ∈ Finset.univ.filter (fun i => z i = k), repR c (x i)) := by
    unfold chiR
    rw [hprod, map_mul, map_pow]
    have : (quadraticChar (IsLocalRing.ResidueField R)) (t ^ 2) = 1 := quadraticChar_sq_one' ht
    rw [map_pow] at this
    rw [this, one_mul]
  rw [chiR_prod, chiR_prod] at hchi
  simp only [chiR_repR hc] at hchi
  simp only [symC]
  rw [Finset.card_filter, Finset.card_filter] at hcard
  have hp : ∏ i, (if z i = k then x i else 1) = ∏ i ∈ Finset.univ.filter (fun i => z i = k), x i :=
    (Finset.prod_filter _ _).symm
  have hp' : ∏ i, (if z' i = k then x' i else 1) = ∏ i ∈ Finset.univ.filter (fun i => z' i = k), x' i :=
    (Finset.prod_filter _ _).symm
  have hunits : ∏ i ∈ Finset.univ.filter (fun i => z i = k), x i =
      ∏ i ∈ Finset.univ.filter (fun i => z' i = k), x' i := by
    apply Units.ext
    push_cast
    exact hchi.symm
  rw [hp, hp', hunits]
  congr 1

end Final

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.symC_eq_of_isometricGL
