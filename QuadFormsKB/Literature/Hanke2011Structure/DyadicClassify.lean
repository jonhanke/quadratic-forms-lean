/-
# Hanke 2011, §2: classification of even unimodular and "odd" Hessian matrices over a dyadic local ring

Setting: $R$ a discrete valuation ring that is Henselian with finite residue field, in which $2 \in \mathfrak p$
(`(2 : R) ∈ maximalIdeal R`) and $2 \ne 0$. Matrices are Hessian matrices (`IsHess`), $H = C + C^{\mathsf T}$.

**Proves** (unconditional)
* `peel`: a Hessian matrix of unit determinant on `Fin (m + 2)` is congruent to $A \oplus S$, $A$ binary, $S$ on `Fin m`,
  both Hessian matrices of unit determinant;
* `hyp_split`: on `Fin (m + 4)` it is congruent to $\begin{pmatrix}0&1\\1&0\end{pmatrix} \oplus S$ (a hyperbolic plane splits off);
* `even_cong` (Hanke 2011, Sublemma 2.7): even unimodular Hessian matrices of the same size whose determinants differ
  by a unit square are congruent.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicBinary
import QuadFormsKB.Literature.Hanke2011Structure.DyadicSplit

open Matrix IsLocalRing

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section Peel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The diagonal of a Hessian matrix lies in $2R \subseteq \mathfrak p$. -/
theorem isHess_diag_mem (h2 : (2 : R) ∈ maximalIdeal R) {H : Matrix ι ι R} (hH : IsHess H) (k : ι) :
    H k k ∈ maximalIdeal R := by
  obtain ⟨G, hG⟩ := hH
  have : H k k = 2 * G k k := by
    rw [hG]; simp [two_mul]
  rw [this]; exact Ideal.mul_mem_right _ _ h2

/-- A Hessian matrix of unit determinant (on a nonempty index type, residue characteristic $2$) has a unit entry off
the diagonal. -/
theorem exists_unit_offdiag (h2 : (2 : R) ∈ maximalIdeal R) [Nonempty ι] {H : Matrix ι ι R} (hH : IsHess H)
    (hdet : IsUnit H.det) : ∃ k l, k ≠ l ∧ IsUnit (H k l) := by
  by_contra hcon
  have hcon : ∀ k l, k ≠ l → ¬ IsUnit (H k l) := fun k l hk hu => hcon ⟨k, l, hk, hu⟩
  have hall : ∀ k l, H k l ∈ maximalIdeal R := fun k l => by
    by_cases hkl : k = l
    · subst hkl; exact isHess_diag_mem h2 hH k
    · exact (IsLocalRing.mem_maximalIdeal _).2 (hcon k l hkl)
  have h0 : (residue R) H.det = 0 := by
    rw [RingHom.map_det]
    have : (residue R).mapMatrix H = 0 := by
      ext i j; simp [(IsLocalRing.residue_eq_zero_iff _).2 (hall i j)]
    rw [this]; exact Matrix.det_zero
  exact ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h0)) hdet

/-- The $2 \times 2$ principal block at $k \ne l$ with a unit off-diagonal entry has unit determinant. -/
theorem isUnit_block_det (h2 : (2 : R) ∈ maximalIdeal R) {H : Matrix ι ι R} (hH : IsHess H) {k l : ι}
    (hkl : IsUnit (H k l)) : IsUnit (H.submatrix ![k, l] ![k, l]).det := by
  have hs := hH.symm_eq
  have hlk : H l k = H k l := by
    have := congrFun (congrFun hs k) l
    simpa [Matrix.transpose_apply] using this
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hlk]
  have hm : H k k * H l l ∈ maximalIdeal R := Ideal.mul_mem_right _ _ (isHess_diag_mem h2 hH k)
  have := isUnit_add_of_mem (hkl.pow 2).neg hm
  convert this using 1; ring

/-- **Peeling a binary block:** a Hessian matrix of unit determinant on `Fin (m + 2)` is congruent to a block sum of a
binary Hessian matrix and a Hessian matrix on `Fin m`, both of unit determinant. -/
theorem peel (h2 : (2 : R) ∈ maximalIdeal R) (m : ℕ) (H : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (hH : IsHess H)
    (hdet : IsUnit H.det) :
    ∃ (A : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin m) (Fin m) R), IsHess A ∧ IsUnit A.det ∧ IsHess S ∧
      IsUnit S.det ∧ Cong H (Matrix.fromBlocks A 0 0 S) := by
  obtain ⟨k, l, hkl, hu⟩ := exists_unit_offdiag h2 hH hdet
  have hA := isUnit_block_det h2 hH hu
  obtain ⟨S₀, hS₀, hc, hd⟩ := split_at H hH hkl hA
  have hcard : Fintype.card (Fin m) = Fintype.card {x : Fin (m + 2) // ¬ (x = k ∨ x = l)} := by
    have := hc.card_eq
    simp only [Fintype.card_fin, Fintype.card_sum] at this ⊢
    omega
  let e := Fintype.equivOfCardEq hcard
  refine ⟨H.submatrix ![k, l] ![k, l], S₀.submatrix e e, hH.submatrix _, hA, hS₀.submatrix e, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]
    rw [hd] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  · exact hc.trans (cong_fromBlocks_reindex _ _ e)

end Peel

section Hyperbolic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]

/-- The Hessian matrix of $xy$, the hyperbolic plane. -/
def hyp (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- **A hyperbolic pair splits off:** if a Hessian matrix $M$ of unit determinant on an index type of size $n + 2$ has
a vector $v$ with a unit coordinate $v_k$, $v^{\mathsf T}Mv = 0$ and $(Mv)_l$ a unit ($l \ne k$), then $M$ is
congruent to $\begin{pmatrix}0&1\\1&0\end{pmatrix} \oplus S$ with $S$ a Hessian matrix of unit determinant on `Fin n`. -/
theorem hyp_of_pair (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hcard : Fintype.card ι = n + 2) (M : Matrix ι ι R) (hM : IsHess M)
    {k l : ι} (hkl : k ≠ l) (v : ι → R) (hvk : IsUnit (v k)) (hv0 : v ⬝ᵥ (M *ᵥ v) = 0)
    (hvl : IsUnit ((M *ᵥ v) l)) :
    ∃ S : Matrix (Fin n) (Fin n) R, IsHess S ∧ Cong M (Matrix.fromBlocks (hyp R) 0 0 S) := by
  obtain ⟨S₃, hS₃, hc, hd⟩ := pair_split M hM hkl v hvk hv0 hvl
  set β := (M *ᵥ v) l with hβ
  obtain ⟨β', hβ'⟩ := hvl.exists_right_inv
  obtain ⟨g, hg⟩ : ∃ g, M l l = 2 * g := by
    obtain ⟨G, hG⟩ := hM
    exact ⟨G l l, by rw [hG]; simp [two_mul]⟩
  have hA'h : IsHess (!![0, β; β, M l l] : Matrix (Fin 2) (Fin 2) R) :=
    ⟨!![0, β; 0, g], by ext i j; fin_cases i <;> fin_cases j <;> simp [hg, two_mul]⟩
  have hA'd : (!![0, β; β, M l l] : Matrix (Fin 2) (Fin 2) R).det = -β ^ 2 := by
    rw [Matrix.det_fin_two_of]; ring
  have hhypd : (hyp R).det = -1 := by
    rw [hyp, Matrix.det_fin_two_of]; ring
  have hcong : Cong (!![0, β; β, M l l] : Matrix (Fin 2) (Fin 2) R) (hyp R) := by
    refine cong_binary h2 h20 hA'h ⟨!![0, 1; 0, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [hyp]⟩
      (by rw [hA'd]; exact (hvl.pow 2).neg) (by rw [hhypd]; exact isUnit_one.neg) (u := β') ?_ ?_
    · exact isUnit_iff_exists_inv'.2 ⟨β, hβ'⟩
    · rw [hA'd, hhypd]; linear_combination (β * β' + 1) * hβ'
  have hc2 : Cong M (Matrix.fromBlocks (hyp R) 0 0 S₃) := hc.trans (Cong.fromBlocks hcong (Cong.refl S₃))
  have hcard' : Fintype.card (Fin n) = Fintype.card {x : ι // ¬ (x = k ∨ x = l)} := by
    have := hc.card_eq
    simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
    omega
  let e := Fintype.equivOfCardEq hcard'
  exact ⟨S₃.submatrix e e, hS₃.submatrix e, hc2.trans (cong_fromBlocks_reindex _ _ e)⟩

/-- The determinant of the hyperbolic plane is $-1$. -/
theorem det_hyp : (hyp R).det = -1 := by
  rw [hyp, Matrix.det_fin_two_of]; ring

/-- If $H \cong \mathrm{hyp} \oplus S$ then $\det S = -w^2 \det H$ for a unit $w$. -/
theorem det_of_cong_hyp {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {H : Matrix ι ι R}
    {S : Matrix (Fin n) (Fin n) R} (h : Cong H (Matrix.fromBlocks (hyp R) 0 0 S)) :
    ∃ w : R, IsUnit w ∧ S.det = -(w ^ 2 * H.det) := by
  obtain ⟨w, hw, e⟩ := h.det
  rw [Matrix.det_fromBlocks_zero₂₁, det_hyp] at e
  exact ⟨w, hw, by linear_combination -e⟩

/-- A binary Hessian matrix of unit determinant has a unit cross coefficient. -/
theorem isUnit_cross (h2 : (2 : R) ∈ maximalIdeal R) {a b c : R}
    (hd : IsUnit (!![2 * a, b; b, 2 * c] : Matrix (Fin 2) (Fin 2) R).det) : IsUnit b := by
  refine isUnit_of_isUnit_four_sub_sq h2 (c := a * c) ?_
  rw [Matrix.det_fin_two_of] at hd
  convert hd using 1; ring

/-- **A hyperbolic plane splits off** an even unimodular Hessian matrix of size $\ge 4$ (Hanke 2011, proof of
Sublemma 2.7): congruent to $\begin{pmatrix}0&1\\1&0\end{pmatrix} \oplus S$, $S$ again even unimodular. After
`peel` twice, the binary blocks represent $1$ and $-1$ (`exists_represents_unit`), which gives an isotropic vector. -/
theorem hyp_split (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) (m : ℕ)
    (H : Matrix (Fin (m + 4)) (Fin (m + 4)) R) (hH : IsHess H) (hdet : IsUnit H.det) :
    ∃ S : Matrix (Fin (m + 2)) (Fin (m + 2)) R, IsHess S ∧ IsUnit S.det ∧
      Cong H (Matrix.fromBlocks (hyp R) 0 0 S) := by
  obtain ⟨A, S1, hA, hAu, hS1, hS1u, c1⟩ := peel h2 (m + 2) H hH hdet
  obtain ⟨A2, S2, hA2, hA2u, hS2, hS2u, c2⟩ := peel h2 m S1 hS1 hS1u
  obtain ⟨a, b, c, rfl⟩ := isHess_fin_two hA
  obtain ⟨a2, b2, c2', rfl⟩ := isHess_fin_two hA2
  have hb := isUnit_cross h2 hAu
  have hb2 := isUnit_cross h2 hA2u
  obtain ⟨x, y, hxy⟩ := exists_represents_unit h2 (a := a) (b := b) (c := c) hb isUnit_one
  obtain ⟨x2, y2, hxy2⟩ := exists_represents_unit h2 (a := a2) (b := b2) (c := c2') hb2 isUnit_one.neg
  have hcM := c1.trans (Cong.fromBlocks (Cong.refl _) c2)
  have hM := hA.fromBlocks (hA2.fromBlocks hS2)
  set M := Matrix.fromBlocks (!![2 * a, b; b, 2 * c] : Matrix (Fin 2) (Fin 2) R) 0 0
    (Matrix.fromBlocks (!![2 * a2, b2; b2, 2 * c2'] : Matrix (Fin 2) (Fin 2) R) 0 0 S2) with hMdef
  set v : Fin 2 ⊕ (Fin 2 ⊕ Fin m) → R := Sum.elim ![x, y] (Sum.elim ![x2, y2] 0) with hv
  have hMv : M *ᵥ v = Sum.elim ![2 * a * x + b * y, b * x + 2 * c * y]
      (Sum.elim ![2 * a2 * x2 + b2 * y2, b2 * x2 + 2 * c2' * y2] 0) := by
    simp only [hMdef, hv, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    ext i
    rcases i with i | i | i
    · fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    · fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    · simp
  have hv0 : v ⬝ᵥ (M *ᵥ v) = 0 := by
    rw [hMv]
    simp [hv, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
    linear_combination 2 * hxy + 2 * hxy2
  have hcard : Fintype.card (Fin 2 ⊕ (Fin 2 ⊕ Fin m)) = m + 2 + 2 := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  have hm2 : ∀ z : R, 2 * z ∈ maximalIdeal R := fun z => Ideal.mul_mem_right _ _ h2
  by_cases hx : IsUnit x
  · obtain ⟨S, hS, hC⟩ := hyp_of_pair h2 h20 hcard M hM
      (k := Sum.inl 0) (l := Sum.inl 1) (by simp) v (by simpa [hv] using hx) hv0 (by
        have hu := isUnit_add_of_mem (hb.mul hx) (hm2 (c * y))
        have : (M *ᵥ v) (Sum.inl 1) = b * x + 2 * (c * y) := by rw [hMv]; simp; ring
        rw [this]; exact hu)
    obtain ⟨w, hw, e⟩ := det_of_cong_hyp (hcM.trans hC)
    exact ⟨S, hS, by rw [e]; exact ((hw.pow 2).mul hdet).neg, hcM.trans hC⟩
  · have hy : IsUnit y := by
      by_contra hy
      have hxm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hx
      have hym : y ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal y).2 hy
      have h1 : (1 : R) ∈ maximalIdeal R := by
        rw [← hxy]
        refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
        · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hxm 2 (by norm_num))
        · exact Ideal.mul_mem_left _ _ hym
        · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hym 2 (by norm_num))
      exact ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
    obtain ⟨S, hS, hC⟩ := hyp_of_pair h2 h20 hcard M hM
      (k := Sum.inl 1) (l := Sum.inl 0) (by simp) v (by simpa [hv] using hy) hv0 (by
        have hu := isUnit_add_of_mem (hb.mul hy) (hm2 (a * x))
        have : (M *ᵥ v) (Sum.inl 0) = b * y + 2 * (a * x) := by rw [hMv]; simp; ring
        rw [this]; exact hu)
    obtain ⟨w, hw, e⟩ := det_of_cong_hyp (hcM.trans hC)
    exact ⟨S, hS, by rw [e]; exact ((hw.pow 2).mul hdet).neg, hcM.trans hC⟩

/-- **Sublemma 2.7 for Hessian matrices (Hanke 2011, p. 9; $n$ even, dyadic):** two even unimodular Hessian matrices of the
same even size whose determinants differ by the square of a unit are congruent. *Proof:* induction on the size; the base
case is `cong_binary`, the step splits a hyperbolic plane off both (`hyp_split`) and compares the determinants of the
remaining parts. -/
@[kb "hanke2011structure" "Sublemma 2.7, p. 9 (n even, dyadic; Hessian matrices up to congruence)"]
theorem even_cong (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) :
    ∀ r : ℕ, 1 ≤ r → ∀ n : ℕ, n = 2 * r → ∀ H H' : Matrix (Fin n) (Fin n) R, IsHess H → IsHess H' →
      IsUnit H.det → IsUnit H'.det → ∀ u : R, IsUnit u → H'.det = u ^ 2 * H.det → Cong H H' := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro n hn H H' hH hH' hd hd' u hu h
    subst hn
    exact cong_binary h2 h20 hH hH' hd hd' hu h
  | succ r hr ih =>
    intro n hn H H' hH hH' hd hd' u hu h
    obtain ⟨m, hm⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    subst hm
    obtain ⟨S, hS, hSu, hc⟩ := hyp_split h2 h20 m H hH hd
    obtain ⟨S', hS', hSu', hc'⟩ := hyp_split h2 h20 m H' hH' hd'
    obtain ⟨w, hw, e1⟩ := hc.det
    obtain ⟨w', hw', e2⟩ := hc'.det
    rw [Matrix.det_fromBlocks_zero₂₁, det_hyp] at e1 e2
    obtain ⟨winv, hwinv⟩ := hw.exists_right_inv
    have hwi : IsUnit winv := isUnit_iff_exists_inv'.2 ⟨w, hwinv⟩
    have hrel : S'.det = (w' * u * winv) ^ 2 * S.det := by
      linear_combination (-1 : R) * e2 + (-(w' ^ 2)) * h + ((w' * u * winv) ^ 2) * e1 +
        (H.det * w' ^ 2 * u ^ 2 * (w * winv + 1)) * hwinv
    have hSS := ih (m + 2) (by omega) S S' hS hS' hSu hSu' (w' * u * winv) ((hw'.mul hu).mul hwi) hrel
    exact hc.trans ((Cong.fromBlocks (Cong.refl _) hSS).trans hc'.symm)

end Hyperbolic

end QuadFormsKB.Hanke2011Structure.Dyadic
