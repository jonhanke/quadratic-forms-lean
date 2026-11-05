/-
# Hanke 2011, §2: the odd case of Thm. 2.6 (dyadic), Sublemmas 2.8 and 2.9

Setting: $R$ a Henselian discrete valuation ring with finite residue field, $2 \ne 0$, $2 \in \mathfrak p$.
For $n$ odd and $\det H = 2\cdot$(unit) ("normalized": $\operatorname{ord}\det H = \operatorname{ord} 2$) the Hessian matrix is
congruent to $(2c) \oplus H''$ with $c$ a unit and $H''$ even unimodular of size $n - 1$ (`odd_split`, from Hanke 2004's
corrected normal form: an odd number of coordinates cannot all lie in binary blocks, and an unpaired coordinate splits
off), and then to $\begin{pmatrix}0&1\\1&0\end{pmatrix} \oplus S$ with $S$ again of this kind (`odd_hyp_split`).

**Proves** (unconditional): `odd_split`, `odd_hyp_split`, `odd_cong` (the odd case of Sublemmas 2.8 and 2.9 for
Hessian matrices: two normalized odd Hessian matrices of the same size whose determinants differ by a unit square are
congruent), and the transfer to forms (`uniqueNormalizedLocalGenus_odd`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicClassify
import QuadFormsKB.Literature.Hanke2011Structure.DyadicUnique
import QuadFormsKB.LocalDensity.DVRLevel

open Matrix IsLocalRing QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section OddSplit

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Every Hessian matrix is the Hessian matrix of a form. -/
theorem exists_quadForm_hessian {n : ℕ} {H : Matrix (Fin n) (Fin n) R} (hH : IsHess H) :
    ∃ Q : QuadForm R n, Q.hessian = H := by
  obtain ⟨G, hG⟩ := hH
  refine ⟨QuadForm.ofUpper fun i j => if i = j then G i i else H i j, ?_⟩
  have hs : Hᵀ = H := by rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  ext i j
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.of_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.le, not_le.2 h, h.ne]
  · simp [hG, two_mul]
  · have hH' : H i j = H j i := by
      have := congrFun (congrFun hs j) i
      simpa [Matrix.transpose_apply] using this
    simp [h, h.le, not_le.2 h, h.ne', h.ne, hH']

/-- **Splitting off an odd unit** (Hanke 2011, proof of Sublemma 2.9): an even-size-plus-one Hessian matrix with
$\det H = 2 w$, $w$ a unit, is congruent to $(2c) \oplus H''$ with $c$ a unit and $H''$ a Hessian matrix of unit
determinant on `Fin m`. *Proof:* take Hanke 2004's corrected normal form of a form with Hessian matrix $H$; the number of
coordinates is odd, so some coordinate lies in no binary block, and its row and column of the Hessian matrix are
concentrated on the diagonal. -/
theorem odd_split (h20 : (2 : R) ≠ 0) (m : ℕ) (hm : Even m) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hH : IsHess H) (hd : ∃ w : R, IsUnit w ∧ H.det = 2 * w) :
    ∃ (c : R) (H'' : Matrix (Fin m) (Fin m) R), IsUnit c ∧ IsHess H'' ∧ IsUnit H''.det ∧
      Cong H (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => 2 * c) 0 0 H'') := by
  obtain ⟨w, hw, hdet⟩ := hd
  obtain ⟨Q, hQ⟩ := exists_quadForm_hessian hH
  have hQnd : Q.Nondegenerate := by
    show Q.hessian.det ≠ 0
    rw [hQ, hdet]; exact mul_ne_zero h20 hw.ne_zero
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨Q', P, w', hJ, hP, U, hU, heval⟩ := exists_jordanFormW_isGLEquiv Q hQnd π hπ h20
  have hcong1 : Cong H Q'.hessian := by
    rw [hessian_eq_of_eval heval, hQ]
    exact cong_of_isUnit_det H U hU
  -- an unpaired coordinate
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsPaired P i := by
    by_contra hall
    push Not at hall
    obtain ⟨σ, -, -⟩ := exists_pairEquiv hJ.2.1 hJ.2.2.1 hall
    have := Fintype.card_congr σ
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    obtain ⟨k, hk⟩ := hm
    omega
  have hrow : ∀ j, j ≠ i → Q'.hessian i j = 0 := by
    intro j hj
    refine hJ.hessian_eq_zero (Ne.symm hj) (fun h => hi ⟨_, h, Or.inl rfl⟩) (fun h => hi ⟨_, h, Or.inr rfl⟩)
  obtain ⟨hsc, hsd⟩ := split_single Q'.hessian i hrow (isHess_hessian Q').symm_eq
  set D1 := Q'.hessian.submatrix (fun x : {x : Fin (m + 1) // x = i} => x.1)
    (fun x : {x : Fin (m + 1) // x = i} => x.1) with hD1def
  set Hr := Q'.hessian.submatrix (fun x : {x : Fin (m + 1) // ¬ x = i} => x.1)
    (fun x : {x : Fin (m + 1) // ¬ x = i} => x.1) with hHrdef
  have hcong2 := hcong1.trans hsc
  have hcardκ : Fintype.card (Fin m) = Fintype.card {x : Fin (m + 1) // ¬ x = i} := by
    have := hcong2.card_eq
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_eq] at this ⊢
    omega
  let e2 := Fintype.equivOfCardEq hcardκ
  let e1 : Unit ≃ {x : Fin (m + 1) // x = i} :=
    ⟨fun _ => ⟨i, rfl⟩, fun _ => (), fun _ => rfl, fun x => Subtype.ext x.2.symm⟩
  have hdiag : Q'.hessian i i = 2 * Q'.coeff i i := by simp [QuadForm.hessian, two_mul]
  have hD1 : D1.submatrix e1 e1 = Matrix.of fun _ _ : Unit => 2 * Q'.coeff i i := by
    ext a b; simp [hD1def, e1, hdiag]
  have hdetD1 : D1.det = 2 * Q'.coeff i i := by
    rw [Matrix.det_unique]; exact hdiag
  obtain ⟨w1, hw1, e⟩ := hcong1.det
  have hcr : Q'.coeff i i * Hr.det = w1 ^ 2 * w := by
    apply mul_left_cancel₀ h20
    rw [hdetD1] at hsd
    rw [hdet] at e
    linear_combination e - hsd
  have hu : IsUnit (Q'.coeff i i * Hr.det) := by rw [hcr]; exact (hw1.pow 2).mul hw
  have hHr : IsHess (Hr.submatrix e2 e2) := ((isHess_hessian Q').submatrix _).submatrix e2
  refine ⟨Q'.coeff i i, Hr.submatrix e2 e2, isUnit_of_mul_isUnit_left hu, hHr, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]; exact isUnit_of_mul_isUnit_right hu
  · have := hcong2.trans (Cong.fromBlocks (cong_submatrix D1 e1) (cong_submatrix Hr e2))
    rwa [hD1] at this

end OddSplit

section OddHyp

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]

/-- If $a x^2 + b x y + c y^2$ is a unit then $x$ or $y$ is a unit. -/
theorem isUnit_or_isUnit_of_rep {a b c T x y : R} (hT : IsUnit T) (h : a * x ^ 2 + b * x * y + c * y ^ 2 = T) :
    IsUnit x ∨ IsUnit y := by
  by_contra hcon
  push Not at hcon
  have hxm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hcon.1
  have hym : y ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal y).2 hcon.2
  have h1 : T ∈ maximalIdeal R := by
    rw [← h]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hxm 2 (by norm_num))
    · exact Ideal.mul_mem_left _ _ hym
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hym 2 (by norm_num))
  exact ((IsLocalRing.mem_maximalIdeal _).1 h1) hT

/-- **A hyperbolic plane splits off an odd normalized Hessian matrix of size $\ge 3$** (Hanke 2011, Sublemma 2.9):
$H \cong \begin{pmatrix}0&1\\1&0\end{pmatrix} \oplus S$ with $S$ a Hessian matrix on `Fin (m + 1)`. After `odd_split` and
`peel`, the binary block represents $-c$ (`exists_represents_unit`), which gives an isotropic vector. -/
theorem odd_hyp_split (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) (m : ℕ) (hm : Even m)
    (H : Matrix (Fin (m + 3)) (Fin (m + 3)) R) (hH : IsHess H) (hd : ∃ w : R, IsUnit w ∧ H.det = 2 * w) :
    ∃ S : Matrix (Fin (m + 1)) (Fin (m + 1)) R, IsHess S ∧ Cong H (Matrix.fromBlocks (hyp R) 0 0 S) := by
  obtain ⟨c, H'', hc, hH'', hH''d, hcong⟩ := odd_split h20 (m + 2) (by simpa using hm.add even_two) H hH hd
  obtain ⟨B, S2, hB, hBd, hS2, hS2d, hcp⟩ := peel h2 m H'' hH'' hH''d
  obtain ⟨a, b, c', rfl⟩ := isHess_fin_two hB
  have hb := isUnit_cross h2 hBd
  obtain ⟨x, y, hxy⟩ := exists_represents_unit h2 (a := a) (b := b) (c := c') hb hc.neg
  have hcM := hcong.trans (Cong.fromBlocks (Cong.refl _) hcp)
  have hM : IsHess (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => 2 * c) 0 0
      (Matrix.fromBlocks (!![2 * a, b; b, 2 * c'] : Matrix (Fin 2) (Fin 2) R) 0 0 S2)) :=
    (IsHess.fromBlocks ⟨Matrix.of fun _ _ : Unit => c, by ext i j; simp [two_mul]⟩ (hB.fromBlocks hS2))
  set M := Matrix.fromBlocks (Matrix.of fun _ _ : Unit => 2 * c) 0 0
    (Matrix.fromBlocks (!![2 * a, b; b, 2 * c'] : Matrix (Fin 2) (Fin 2) R) 0 0 S2) with hMdef
  set v : Unit ⊕ (Fin 2 ⊕ Fin m) → R := Sum.elim (fun _ => 1) (Sum.elim ![x, y] 0) with hv
  have hMv : M *ᵥ v = Sum.elim (fun _ => 2 * c) (Sum.elim ![2 * a * x + b * y, b * x + 2 * c' * y] 0) := by
    simp only [hMdef, hv, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    ext i
    rcases i with i | i | i
    · simp [Matrix.mulVec, dotProduct]
    · fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    · simp
  have hv0 : v ⬝ᵥ (M *ᵥ v) = 0 := by
    rw [hMv]
    simp [hv, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
    linear_combination 2 * hxy
  have hcard : Fintype.card (Unit ⊕ (Fin 2 ⊕ Fin m)) = (m + 1) + 2 := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega
  have hm2 : ∀ z : R, 2 * z ∈ maximalIdeal R := fun z => Ideal.mul_mem_right _ _ h2
  rcases isUnit_or_isUnit_of_rep hc.neg hxy with hx | hy
  · obtain ⟨S, hS, hC⟩ := hyp_of_pair h2 h20 hcard M hM
      (k := Sum.inl ()) (l := Sum.inr (Sum.inl 1)) (by simp) v (by simp [hv]) hv0 (by
        have hu := isUnit_add_of_mem (hb.mul hx) (hm2 (c' * y))
        have : (M *ᵥ v) (Sum.inr (Sum.inl 1)) = b * x + 2 * (c' * y) := by rw [hMv]; simp; ring
        rw [this]; exact hu)
    exact ⟨S, hS, hcM.trans hC⟩
  · obtain ⟨S, hS, hC⟩ := hyp_of_pair h2 h20 hcard M hM
      (k := Sum.inl ()) (l := Sum.inr (Sum.inl 0)) (by simp) v (by simp [hv]) hv0 (by
        have hu := isUnit_add_of_mem (hb.mul hy) (hm2 (a * x))
        have : (M *ᵥ v) (Sum.inr (Sum.inl 0)) = b * y + 2 * (a * x) := by rw [hMv]; simp; ring
        rw [this]; exact hu)
    exact ⟨S, hS, hcM.trans hC⟩

/-- **Sublemmas 2.8 and 2.9 for Hessian matrices (Hanke 2011, p. 10; $n$ odd, dyadic):** two Hessian matrices of the same odd
size with determinants $2\cdot$unit whose determinants differ by the square of a unit are congruent. (Induction on the size:
the base case is $1 \times 1$, the step splits a hyperbolic plane off both, `odd_hyp_split`.) -/
@[kb "hanke2011structure" "Sublemmas 2.8, 2.9, p. 10 (n odd, dyadic; Hessian matrices up to congruence)"]
theorem odd_cong (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) :
    ∀ r : ℕ, ∀ n : ℕ, n = 2 * r + 1 → ∀ H H' : Matrix (Fin n) (Fin n) R, IsHess H → IsHess H' →
      (∃ w : R, IsUnit w ∧ H.det = 2 * w) → (∃ w : R, IsUnit w ∧ H'.det = 2 * w) →
      ∀ u : R, IsUnit u → H'.det = u ^ 2 * H.det → Cong H H' := by
  intro r
  induction r with
  | zero =>
    intro n hn H H' hH hH' hd hd' u hu h
    obtain rfl : n = 1 := by omega
    have hU : IsUnit (!![u] : Matrix (Fin 1) (Fin 1) R).det := by simpa using hu
    have := cong_of_isUnit_det H (!![u] : Matrix (Fin 1) (Fin 1) R) hU
    convert this using 1
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    have h1 : H'.det = H' 0 0 := Matrix.det_unique H'
    have h2' : H.det = H 0 0 := Matrix.det_unique H
    simp [Matrix.mul_apply]
    rw [← h1, h, h2']; ring
  | succ r ih =>
    intro n hn H H' hH hH' hd hd' u hu h
    obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    subst hm
    have hmev : Even (2 * r) := even_two_mul r
    have hm' : (m = 2 * r) := by omega
    subst hm'
    obtain ⟨S, hS, hc⟩ := odd_hyp_split h2 h20 (2 * r) hmev H hH hd
    obtain ⟨S', hS', hc'⟩ := odd_hyp_split h2 h20 (2 * r) hmev H' hH' hd'
    obtain ⟨w, hw, e1⟩ := det_of_cong_hyp hc
    obtain ⟨w', hw', e2⟩ := det_of_cong_hyp hc'
    obtain ⟨d0, hd0, hdd⟩ := hd
    obtain ⟨d0', hd0', hdd'⟩ := hd'
    obtain ⟨winv, hwinv⟩ := hw.exists_right_inv
    have hwi : IsUnit winv := isUnit_iff_exists_inv'.2 ⟨w, hwinv⟩
    have hrel : S'.det = (w' * u * winv) ^ 2 * S.det := by
      rw [e1, e2, h]
      linear_combination (H.det * w' ^ 2 * u ^ 2 * (w * winv + 1)) * hwinv
    have hSd : ∃ z : R, IsUnit z ∧ S.det = 2 * z :=
      ⟨-(w ^ 2 * d0), ((hw.pow 2).mul hd0).neg, by rw [e1, hdd]; ring⟩
    have hSd' : ∃ z : R, IsUnit z ∧ S'.det = 2 * z :=
      ⟨-(w' ^ 2 * d0'), ((hw'.pow 2).mul hd0').neg, by rw [e2, hdd']; ring⟩
    have hSS := ih (2 * r + 1) rfl S S' hS hS' hSd hSd' (w' * u * winv) ((hw'.mul hu).mul hwi) hrel
    exact hc.trans ((Cong.fromBlocks (Cong.refl _) hSS).trans hc'.symm)

end OddHyp

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {n : ℕ}

/-- **Thm. 2.6, dyadic case, $n$ odd** (= Sublemmas 2.8 and 2.9: Hanke 2011, pp. 8--10), proved without Theorem 93:28.
Let $R$ be a Henselian discrete valuation ring with finite residue field and $2 \ne 0$ a non-unit (e.g. the integers of a
completion of a number field at a prime over $2$). If $Q, Q'$ are forms in an odd number $n$ of variables with
$\operatorname{ord}\det H(Q) = \operatorname{ord} 2$ and $\det H(Q') = u^2\det H(Q)$ for a unit $u$, then $Q$ and $Q'$ are
$\mathrm{GL}_n(R)$-isometric. (Hanke's Sublemma 2.8 is the statement for the quadratic spaces over the fraction field, and
Sublemma 2.9 the statement for the lattices; this gives the lattice statement directly, which implies the space statement.
Primitivity is not used.) -/
@[kb "hanke2011structure" "Sublemmas 2.8, 2.9 and Thm. 2.6, pp. 8-10 (dyadic, n odd)"]
theorem uniqueNormalizedLocalGenus_odd (h2 : ¬ IsUnit (2 : R)) (h20 : (2 : R) ≠ 0) (hn : Odd n)
    (Q Q' : QuadForm R n) (hN : IsNormalizedHessian R Q) (u : R) (hu : IsUnit u)
    (hdet : Q'.hessian.det = u ^ 2 * Q.hessian.det) : QuadFormsKB.Siegel.IsometricGL Q Q' := by
  have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h2
  obtain ⟨r, hr⟩ := hn
  have hnev : ¬ Even n := Nat.not_even_iff_odd.2 ⟨r, hr⟩
  have hd : ∃ w : R, IsUnit w ∧ Q.hessian.det = 2 * w := by
    simp only [IsNormalizedHessian, hnev, ite_false] at hN
    obtain ⟨v, hv⟩ := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).1 hN
    refine ⟨((v⁻¹ : Rˣ) : R), (v⁻¹).isUnit, ?_⟩
    calc Q.hessian.det = Q.hessian.det * (v * ((v⁻¹ : Rˣ) : R)) := by simp
      _ = (Q.hessian.det * v) * ((v⁻¹ : Rˣ) : R) := by ring
      _ = 2 * ((v⁻¹ : Rˣ) : R) := by rw [hv]
  have hd' : ∃ w : R, IsUnit w ∧ Q'.hessian.det = 2 * w := by
    obtain ⟨w, hw, e⟩ := hd
    exact ⟨u ^ 2 * w, (hu.pow 2).mul hw, by rw [hdet, e]; ring⟩
  exact isometricGL_of_cong h20 (odd_cong h2m h20 r n hr Q.hessian Q'.hessian (isHess_hessian Q)
    (isHess_hessian Q') hd hd' u hu hdet)

/-- **Thm. 2.6, dyadic case** (Hanke 2011, p. 8): for a Henselian discrete valuation ring $R$ with finite residue field
in which $2$ is a non-unit and nonzero, `UniqueNormalizedLocalGenus R n` holds for every $n$. Unconditional: no named
statement is assumed (Hanke's proof uses O'Meara 93:11, 93:15, 93:16, 93:18, 93:28; this proof uses Hensel's lemma
and the Hessian-matrix normal forms of Hanke 2004 instead). -/
@[kb "hanke2011structure" "Thm. 2.6, p. 8 (dyadic case)"]
theorem uniqueNormalizedLocalGenus_of_dyadic (h2 : ¬ IsUnit (2 : R)) (h20 : (2 : R) ≠ 0) :
    UniqueNormalizedLocalGenus R n := by
  refine ⟨fun Q Q' hQ _ hN u hu hdet => ?_⟩
  rcases Nat.even_or_odd n with hn | hn
  · exact uniqueNormalizedLocalGenus_even h2 h20 hn Q Q' hQ hN u hu hdet
  · exact uniqueNormalizedLocalGenus_odd h2 h20 hn Q Q' hN u hu hdet

end Main

section Completion

open IsDedekindDomain NumberField

/-- **Thm. 2.6 for the completion of a number field at a prime over $2$** (Hanke 2011, p. 8): for a number field $F$ and a
finite prime $\mathfrak p$ (`v`) with $2 \in \mathfrak p$, `UniqueNormalizedLocalGenus` holds for
$R = \mathcal O_\mathfrak p$ = `v.adicCompletionIntegers F`, in every dimension $n$, unconditionally. Together with
`uniqueNormalizedLocalGenus_completion` ($\mathfrak p \nmid 2$) this proves Thm. 2.6 at every finite prime. -/
@[kb "hanke2011structure" "Thm. 2.6, p. 8 (dyadic p, number field completion)"]
theorem uniqueNormalizedLocalGenus_completion_dyadic {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (n : ℕ) :
    UniqueNormalizedLocalGenus (v.adicCompletionIntegers F) n := by
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) :=
    ⟨fun f hf a₀ h₁ h₂ => HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers F)) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))⟩
  have hdvd : QuadFormsKB.LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    have := (QuadFormsKB.LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).2 (by simpa using h2)
    rwa [pow_one, map_ofNat] at this
  refine uniqueNormalizedLocalGenus_of_dyadic (fun hu => ?_) (QuadFormsKB.LocalDensity.NF.two_ne_zero' v)
  exact (QuadFormsKB.LocalDensity.NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit hdvd hu)

end Completion

end QuadFormsKB.Hanke2011Structure.Dyadic
