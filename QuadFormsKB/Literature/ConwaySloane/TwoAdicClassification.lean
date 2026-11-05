/-
# Conway–Sloane, Ch. 15, Theorem 10 for forms: the 2-adic classification

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.5, Thm. 10, p. 381, and
§7.5–7.6, pp. 381–382 (`conwaysloane1999`).

Theorem 10: two integral forms $f$, $f'$ over $\mathbb Z_2$ with 2-adic symbols $\sigma$, $\sigma'$ (from Jordan
decompositions) are $\mathbb Z_2$-equivalent iff (i) $n_q = n'_q$, $S_q = S'_q$ for all $q$ and (ii) the congruences of
`Theorem10Cond` hold. Conway–Sloane give no proof (p. 378, "No proofs will be offered"); the rules were checked against
Jones' canonical form and Pall's invariants.

**Route.** A block decomposition $D$ (Cassels' Lemma 4.1 normalization of a Jordan
decomposition) gives a basis of $\mathbb Z_2^n$ in which the Gram matrix is block diagonal; the blocks of exponent $k$
span a Jordan splitting (`TwoAdicClassificationLattice.lean`). For two such forms on one quadratic space (they are
equivalent over $\mathbb Q_2$ iff the determinant units and the oddities of the whole forms agree, `ratIso_iff`), O'Meara's
93:29 (`OMeara.G29.twoAdicClassificationLe_twoAdic`, proved unconditionally in the library) says the lattices are
isometric iff O'Meara's conditions (i), (ii) hold, which `cls_eq_iff_omPair` rewrites as `OMPair`; and
`theorem10Cond_iff_omCond` shows that `OMPair` together with the equality over $\mathbb Q_2$ is exactly the printed
Theorem 10. Everything is local: no reciprocity, no global input.

**Proves**
* `zpEquiv_iff_theorem10Cond`: **Theorem 10** for forms with 2-adic symbols $\sigma$, $\tau$;
* `zpEquiv_iff_moveEquiv`, `zpEquiv_iff_canonical_eq`: equivalently, the symbols are related by sign walking and
  oddity fusion, or have the same canonical symbol (§7.5–7.6);
* `moveEquiv_of_isTwoSymbolOf`: any two 2-adic symbols of one form are related by the moves (§7.5, p. 381: "a form may
  have several Jordan decompositions", whose symbols differ by sign walking and oddity fusion);
* `exists_isTwoSymbolOf`: every nonsingular integral form has a 2-adic symbol.
-/
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassificationLattice
import QuadFormsKB.Literature.Cassels.Ch8.DyadicCancelAux
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

noncomputable section

namespace QuadFormsKB.ConwaySloane.TwoAdic

open OMeara Matrix Finset Module
open Cassels (DyBlock dyMat dyDim ZpEquiv qfForm zpLat)

variable {n : ℕ}

/-! ### The matrix of a block decomposition -/

theorem mat_transpose (b : DyBlock) : b.matᵀ = b.mat := by
  cases b with
  | sq e u =>
    show (!![(2 : ℚ_[2]) ^ e * u] : Matrix (Fin 1) (Fin 1) ℚ_[2])ᵀ = !![(2 : ℚ_[2]) ^ e * u]
    ext i j; fin_cases i; fin_cases j; rfl
  | hyp e =>
    show ((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]))ᵀ =
      (2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  | ell e =>
    show ((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]))ᵀ =
      (2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])
    ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem bmat_transpose (D : List DyBlock) : (bmat D)ᵀ = bmat D := by
  unfold bmat; rw [blockDiagonal'_transpose]; congr 1; funext j; exact mat_transpose _

/-- The variables of $\mathbb Q_2^n$ as variables of the blocks. -/
def bE (D : List DyBlock) (h : dyDim D = n) : Fin n ≃ BIdx D := (finCongr h.symm).trans (bEquiv D)

/-- `dyMat D` as an $n \times n$ matrix. -/
def castMat (D : List DyBlock) (h : dyDim D = n) : Matrix (Fin n) (Fin n) ℚ_[2] :=
  (dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)

theorem castMat_apply (D : List DyBlock) (h : dyDim D = n) (i j : Fin n) :
    castMat D h i j = bmat D (bE D h i) (bE D h j) := dyMat_apply D _ _

theorem castMat_transpose (D : List DyBlock) (h : dyDim D = n) : (castMat D h)ᵀ = castMat D h := by
  ext i j
  rw [transpose_apply, castMat_apply, castMat_apply, ← transpose_apply (bmat D), bmat_transpose]

theorem castMat_det_ne (D : List DyBlock) (h : dyDim D = n) (hD : ∀ b ∈ D, b.Valid)
    (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : (castMat D h).det ≠ 0 := by
  have : castMat D h = (bmat D).submatrix (bE D h) (bE D h) := by ext i j; rw [castMat_apply]; rfl
  rw [this, det_submatrix_equiv_self, bmat, det_blockDiagonal']
  refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
  rw [det_mat _ (hD0 _ (List.get_mem _ _))]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  have h1 : bUnit (D.get j) ≠ 0 := fun h0 => by
    have := bUnit_odd (D.get j) (hD _ (List.get_mem _ _)); rw [h0] at this; exact absurd this (by decide)
  exact_mod_cast h1

theorem nondegenerate_qfForm {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    (QuadraticMap.associated (qfForm F)).Nondegenerate := by
  have hright : ∀ y : Fin n → ℚ_[2], (∀ x, OMeara.bil (qfForm F) x y = 0) → y = 0 := by
    intro y hy
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [Cassels.bil_qfForm hF, single_dotProduct, one_mul] at this
    simpa using this
  exact ⟨fun x hx => hright x fun z => (OMeara.bil_comm (qfForm F) z x).trans (hx z), hright⟩

/-! ### The lattice $\mathbb Z_2^n$ with the basis of a block decomposition -/

/-- The standard basis of $\mathbb Z_2^n$. -/
def zpBasis (n : ℕ) : Basis (Fin n) ℤ_[2] (zpLat 2 n) :=
  Basis.span ((Pi.basisFun ℚ_[2] (Fin n)).linearIndependent.restrict_scalars' (R := ℤ_[2]))

theorem zpBasis_apply (i : Fin n) : (zpBasis n i : Fin n → ℚ_[2]) = Pi.single i 1 := by
  rw [zpBasis]
  exact congrArg Subtype.val (Basis.span_apply _ i) |>.trans (by simp)

/-- The basis of $\mathbb Z_2^n$ indexed by the variables of the blocks. -/
def bLat (D : List DyBlock) (h : dyDim D = n) : Basis (BIdx D) ℤ_[2] (zpLat 2 n) := (zpBasis n).reindex (bE D h)

theorem bLat_apply (D : List DyBlock) (h : dyDim D = n) (x : BIdx D) :
    (bLat D h x : Fin n → ℚ_[2]) = Pi.single ((bE D h).symm x) 1 := by
  rw [bLat, Basis.reindex_apply, zpBasis_apply]

theorem gram_bLat (D : List DyBlock) (h : dyDim D = n) (x y : BIdx D) :
    bil (qfForm (castMat D h)) (bLat D h x : Fin n → ℚ_[2]) (bLat D h y : Fin n → ℚ_[2]) = bmat D x y := by
  rw [bLat_apply, bLat_apply, Cassels.bil_qfForm (castMat_transpose D h), mulVec_single_one, single_dotProduct,
    one_mul, col_apply, castMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The image of a basis under a linear automorphism of $V$. -/
def mapBasis {ι : Type*} (φ : (Fin n → ℚ_[2]) ≃ₗ[ℚ_[2]] (Fin n → ℚ_[2])) {M : Submodule ℤ_[2] (Fin n → ℚ_[2])}
    (b : Basis ι ℤ_[2] M) : Basis ι ℤ_[2] (latMap φ M) :=
  b.map (Submodule.equivMapOfInjective (((φ : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))).restrictScalars ℤ_[2])
    φ.injective M)

theorem mapBasis_apply {ι : Type*} (φ : (Fin n → ℚ_[2]) ≃ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    {M : Submodule ℤ_[2] (Fin n → ℚ_[2])} (b : Basis ι ℤ_[2] M) (x : ι) :
    (mapBasis φ b x : Fin n → ℚ_[2]) = φ (b x) := rfl

theorem bil_map {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (φ : (Fin n → ℚ_[2]) ≃ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    (hφ : ∀ x, qfForm F (φ x) = qfForm G x) (x y : Fin n → ℚ_[2]) :
    bil (qfForm F) (φ x) (φ y) = bil (qfForm G) x y := by
  rw [bil_eq_half, bil_eq_half, ← map_add, hφ, hφ, hφ]

/-- The linear automorphism $x \mapsto Px$ of an invertible matrix. -/
def matEquiv (P : Matrix (Fin n) (Fin n) ℚ_[2]) (hP : IsUnit P.det) :
    (Fin n → ℚ_[2]) ≃ₗ[ℚ_[2]] (Fin n → ℚ_[2]) :=
  haveI := P.invertibleOfIsUnitDet hP
  Matrix.toLinearEquiv' P this

theorem matEquiv_apply (P : Matrix (Fin n) (Fin n) ℚ_[2]) (hP : IsUnit P.det) (x : Fin n → ℚ_[2]) :
    matEquiv P hP x = P *ᵥ x := rfl

theorem qfForm_matEquiv {F G P : Matrix (Fin n) (Fin n) ℚ_[2]} (hP : IsUnit P.det) (h : Pᵀ * F * P = G)
    (x : Fin n → ℚ_[2]) : qfForm F (matEquiv P hP x) = qfForm G x := by
  rw [matEquiv_apply, Cassels.qfForm_apply, Cassels.qfForm_apply, ← h, Cassels.qf_conj']

/-! ### Equivalence over $\mathbb Q_2$ -/

/-- The weights of a diagonalization over $\mathbb Q_2$ of the whole form. -/
def wFull (D : List DyBlock) (h : dyDim D = n) (i : Fin n) : ℤ := bW (D.get (bE D h i).1) (bE D h i).2

theorem rep_full (D : List DyBlock) (h : dyDim D = n) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    D18.Rep (qfForm (castMat D h)) (diagonal fun i => ((wFull D h i : ℤ) : ℚ_[2])) := by
  have h0 : D18.Rep (qfForm (castMat D h)) (castMat D h) := by
    refine ⟨Pi.basisFun ℚ_[2] (Fin n), ?_⟩
    ext i j
    simp only [OMeara.gram, of_apply, Pi.basisFun_apply]
    rw [Cassels.bil_qfForm (castMat_transpose D h), mulVec_single_one, single_dotProduct, one_mul, col_apply]
  set B := blockDiagonal' fun j : Fin D.length => bP (D.get j)
  have hPm : IsUnit (B.submatrix (bE D h) (bE D h)).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal', isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => bP_det_ne _
  have h1 := D18.rep_congr _ h0 hPm
  have hc : castMat D h = (bmat D).submatrix (bE D h) (bE D h) := by ext i j; rw [castMat_apply]; rfl
  have hmat : B.submatrix (bE D h) (bE D h) * castMat D h * (B.submatrix (bE D h) (bE D h))ᵀ =
      diagonal fun i => ((wFull D h i : ℤ) : ℚ_[2]) := by
    rw [hc, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    simp only [B, bmat]
    rw [blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_mul,
      show (fun j : Fin D.length => bP (D.get j) * (D.get j).mat * (bP (D.get j))ᵀ) =
        fun j => diagonal fun r => ((bW (D.get j) r : ℤ) : ℚ_[2]) from
        funext fun j => bP_mul _ (hD0 _ (List.get_mem _ _)),
      blockDiagonal'_diagonal, submatrix_diagonal_equiv]
    rfl
  rwa [hmat] at h1

theorem oddity_wFull (D : List DyBlock) (h : dyDim D = n) :
    oddity (wFull D h) = ∑ j, bOdd (D.get j) := by
  unfold oddity wFull
  rw [Equiv.sum_comp (bE D h) (fun y => oddityEntry (bW (D.get y.1) y.2)), Fintype.sum_sigma]
  rfl

theorem prod_wFull (D : List DyBlock) (h : dyDim D = n) :
    ∏ i, wFull D h i = 2 ^ (∑ j, bWexp (D.get j)) * ∏ j, bUnit (D.get j) := by
  unfold wFull
  rw [Equiv.prod_comp (bE D h) (fun y => bW (D.get y.1) y.2), Fintype.prod_sigma,
    Finset.prod_congr rfl fun j _ => prod_bW (D.get j), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem wFull_ne_zero (D : List DyBlock) (h : dyDim D = n) (hD : ∀ b ∈ D, b.Valid) (i : Fin n) :
    wFull D h i ≠ 0 := bW_ne_zero _ (hD _ (List.get_mem _ _)) _

/-- **Square classes of $2^a U$**: for odd $U$, $U'$ and $a \equiv b \pmod 2$, $2^bU' = t^2\,2^aU$ for some
$t \in \mathbb Q_2^\times$ iff $U \equiv U' \pmod 8$. -/
theorem sq_class_iff {a b : ℕ} (hab : a % 2 = b % 2) {U U' : ℤ} (hU : Odd U) (hU' : Odd U') :
    (∃ t : ℚ_[2], t ≠ 0 ∧ (2 : ℚ_[2]) ^ b * (U' : ℚ_[2]) = t ^ 2 * ((2 : ℚ_[2]) ^ a * (U : ℚ_[2]))) ↔
      (8 : ℤ) ∣ U' - U := by
  have hUu : IsUnit (U : ℤ_[2]) := Cassels.dyadic_isUnit_int_cast_of_odd hU
  have hU'u : IsUnit (U' : ℤ_[2]) := Cassels.dyadic_isUnit_int_cast_of_odd hU'
  have hU0 : (U : ℚ_[2]) ≠ 0 := by
    have : (U : ℤ) ≠ 0 := fun h => by rw [h] at hU; exact absurd hU (by decide)
    exact_mod_cast this
  have h1 : ((↑hUu.unit⁻¹ : ℤ_[2]) : ℚ_[2]) * U = 1 := by
    rw [← PadicInt.coe_intCast, ← PadicInt.coe_mul, hUu.val_inv_mul, PadicInt.coe_one]
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  constructor
  · rintro ⟨t, ht, hteq⟩
    set w : ℤ_[2]ˣ := hU'u.unit * hUu.unit⁻¹
    have hinv : ((↑hUu.unit⁻¹ : ℤ_[2]) : ℚ_[2]) = (U : ℚ_[2])⁻¹ := eq_inv_of_mul_eq_one_left h1
    have key : t * t = (2 : ℚ_[2]) ^ b * U' / ((2 : ℚ_[2]) ^ a * U) := by
      rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ h2) hU0)]
      linear_combination -hteq
    have hsq : IsSquare ((2 : ℚ_[2]) ^ ((b : ℤ) - a) * ((w : ℤ_[2]) : ℚ_[2])) := by
      refine ⟨t, ?_⟩
      have hw : ((w : ℤ_[2]) : ℚ_[2]) = (U' : ℚ_[2]) * ((↑hUu.unit⁻¹ : ℤ_[2]) : ℚ_[2]) := by
        simp [w, PadicInt.coe_mul]
      rw [hw, hinv, zpow_sub₀ h2, zpow_natCast, zpow_natCast, key]
      field_simp
    obtain ⟨-, hres⟩ := (HilbertLocal.isSquare_two_zpow_mul_unit_iff _ w).1 hsq
    have e : PadicInt.toZModPow 3 (U' : ℤ_[2]) = PadicInt.toZModPow 3 (U : ℤ_[2]) := by
      have := congrArg (· * PadicInt.toZModPow 3 (U : ℤ_[2])) hres
      simp only [one_mul] at this
      rw [← this, Units.val_mul, map_mul, mul_assoc, ← map_mul, hUu.val_inv_mul, map_one, mul_one,
        IsUnit.unit_spec]
    rw [map_intCast, map_intCast] at e
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub U U' (2 ^ 3)).1 e.symm
    norm_num at this
    exact this
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz, hzu⟩ := Composition.exists_sq_one_add_eight (w * ↑hUu.unit⁻¹)
    have hz' : (z : ℚ_[2]) ^ 2 = 1 + 8 * ((w : ℚ_[2]) * ((↑hUu.unit⁻¹ : ℤ_[2]) : ℚ_[2])) := by
      have := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
      simp only [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_one,
        PadicInt.coe_intCast] at this
      exact this
    obtain ⟨c, hc⟩ : ∃ c : ℤ, (b : ℤ) - a = 2 * c := ⟨((b : ℤ) - a) / 2, by omega⟩
    refine ⟨(2 : ℚ_[2]) ^ c * z, mul_ne_zero (zpow_ne_zero _ h2) (PadicInt.coe_ne_zero.2 hzu.ne_zero), ?_⟩
    have hU'e : (U' : ℚ_[2]) = U + 8 * w := by
      have := congrArg (fun z : ℤ => (z : ℚ_[2])) hw
      push_cast at this; linear_combination this
    have h2b : (2 : ℚ_[2]) ^ b = (2 : ℚ_[2]) ^ c * (2 : ℚ_[2]) ^ c * (2 : ℚ_[2]) ^ a := by
      rw [← zpow_add₀ h2, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h2]; congr 1; omega
    rw [mul_pow, hz', h2b, hU'e]
    linear_combination -((2 : ℚ_[2]) ^ c * (2 : ℚ_[2]) ^ c * (2 : ℚ_[2]) ^ a * (8 * w)) * h1

section Global

variable {D D' : List DyBlock} (h : dyDim D = n) (h' : dyDim D' = n)
  (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (hD' : ∀ b ∈ D', b.Valid)
  (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b)
  (hshape : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧ (blockSymbol D' k).type = (blockSymbol D k).type)
  {N : ℕ} (hN : ∀ j, bexp D j < N) (hN' : ∀ j, bexp D' j < N)

include hD hD0 hN in
theorem unitPre_full : unitPre (blockSymbol D) N = ((∏ j, bUnit (D.get j) : ℤ) : ZMod 8) := by
  rw [unitPre_blockSymbol D hD hD0, Int.cast_prod]
  exact Finset.prod_congr (by ext j; simp [hN j]) fun _ _ => rfl

include hD hD0 hD' hD'0 hshape hN hN' in
/-- **Equivalence over $\mathbb Q_2$**: the forms of two block decompositions with the same dimensions at each scale
are equivalent over $\mathbb Q_2$ iff the determinant units modulo 8 and the oddities of the whole forms agree. -/
theorem ratIso_iff :
    (∃ P : Matrix (Fin n) (Fin n) ℚ_[2], IsUnit P.det ∧ Pᵀ * castMat D h * P = castMat D' h') ↔
      unitPre (blockSymbol D) N = unitPre (blockSymbol D') N ∧ oddPre (blockSymbol D) N = oddPre (blockSymbol D') N := by
  set wF := wFull D h
  set wG := wFull D' h'
  set EF := ∑ j, bWexp (D.get j)
  set EG := ∑ j, bWexp (D'.get j)
  set UF : ℤ := ∏ j, bUnit (D.get j)
  set UG : ℤ := ∏ j, bUnit (D'.get j)
  have hpF : ∏ i, wF i = 2 ^ EF * UF := prod_wFull D h
  have hpG : ∏ i, wG i = 2 ^ EG * UG := prod_wFull D' h'
  have hUF : Odd UF := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD _ (List.get_mem _ _))
  have hUG : Odd UG := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD' _ (List.get_mem _ _))
  have hall : ∀ j, j ∈ univ.filter (fun j => bexp D j ≤ N) := fun j => by simp [(hN j).le]
  have hall' : ∀ j, j ∈ univ.filter (fun j => bexp D' j ≤ N) := fun j => by simp [(hN' j).le]
  have hE : ∑ j, bexp D j * (D.get j).dim = ∑ j, bexp D' j * (D'.get j).dim := by
    rw [← Finset.filter_true_of_mem (s := univ) (p := fun j => bexp D j ≤ N) (fun j _ => (hN j).le),
      ← Finset.filter_true_of_mem (s := univ) (p := fun j => bexp D' j ≤ N) (fun j _ => (hN' j).le),
      chainExp_eq hD0, chainExp_eq hD'0]
    exact Finset.sum_congr rfl fun k _ => by rw [(hshape k).1]
  have hpar : EF % 2 = EG % 2 := by
    have e1 : EF % 2 = (∑ j, bexp D j * (D.get j).dim) % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl fun j _ => bWexp_mod_two (D.get j), ← Finset.sum_nat_mod]; rfl
    have e2 : EG % 2 = (∑ j, bexp D' j * (D'.get j).dim) % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl fun j _ => bWexp_mod_two (D'.get j), ← Finset.sum_nat_mod]; rfl
    rw [e1, e2, hE]
  have hoF : oddity wF = oddPre (blockSymbol D) N := by
    rw [oddity_wFull, oddPre_blockSymbol D hD hD0]
    exact (Finset.sum_congr (by ext j; simp [hN j]) fun _ _ => rfl)
  have hoG : oddity wG = oddPre (blockSymbol D') N := by
    rw [oddity_wFull, oddPre_blockSymbol D' hD' hD'0]
    exact (Finset.sum_congr (by ext j; simp [hN' j]) fun _ _ => rfl)
  have huF : unitPre (blockSymbol D) N = (UF : ZMod 8) := unitPre_full hD hD0 hN
  have huG : unitPre (blockSymbol D') N = (UG : ZMod 8) := unitPre_full hD' hD'0 hN'
  have hwF : ∀ i, ((wF i : ℤ) : ℚ_[2]) ≠ 0 := fun i => by exact_mod_cast wFull_ne_zero D h hD i
  have hwG : ∀ i, ((wG i : ℤ) : ℚ_[2]) ≠ 0 := fun i => by exact_mod_cast wFull_ne_zero D' h' hD' i
  have hsqc : (∃ t : ℚ_[2], t ≠ 0 ∧ ∏ i, ((wF i : ℤ) : ℚ_[2]) = t ^ 2 * ∏ i, ((wG i : ℤ) : ℚ_[2])) ↔
      (8 : ℤ) ∣ UF - UG := by
    rw [← sq_class_iff (a := EG) (b := EF) hpar.symm hUG hUF]
    have e1 : ∏ i, ((wF i : ℤ) : ℚ_[2]) = (2 : ℚ_[2]) ^ EF * (UF : ℚ_[2]) := by
      rw [← Int.cast_prod, hpF]; push_cast; ring
    have e2 : ∏ i, ((wG i : ℤ) : ℚ_[2]) = (2 : ℚ_[2]) ^ EG * (UG : ℚ_[2]) := by
      rw [← Int.cast_prod, hpG]; push_cast; ring
    rw [e1, e2]
  have hcong : (UF : ZMod 8) = UG ↔ (8 : ℤ) ∣ UF - UG := by
    have := ZMod.intCast_eq_intCast_iff_dvd_sub UG UF 8
    push_cast at this; rw [eq_comm, this]
  have hhasse : (UF : ZMod 8) = UG →
      (PadicClass.hasseVec (fun i => ((wG i : ℤ) : ℚ_[2])) = PadicClass.hasseVec (fun i => ((wF i : ℤ) : ℚ_[2])) ↔
        oddity wF = oddity wG) := by
    intro hc
    have hoF' := oddity_eq_hasse wF (wFull_ne_zero D h hD)
    have hoG' := oddity_eq_hasse wG (wFull_ne_zero D' h' hD')
    have hent : oddityEntry (∏ i, wF i) = oddityEntry (∏ i, wG i) := by
      rw [hpF, hpG, oddityEntry_eq_oddE _ hUF, oddityEntry_eq_oddE _ hUG, hc]
      exact oddE_congr (four_mul_natCast_of_parity hpar) _
    rw [hasseVec_intCast, hasseVec_intCast, eq_comm,
      ← Rational.sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]
    constructor
    · intro h1; rw [hoF', hoG', hent, h1]
    · intro h1; rw [hoF', hoG', hent] at h1; exact add_left_cancel h1
  have hRF := rep_full D h hD0
  have hRG := rep_full D' h' hD'0
  have hHil := PadicClass.localHilbertField_padic 2
  constructor
  · rintro ⟨P, hPu, hP⟩
    let ψ : (qfForm (castMat D' h')).IsometryEquiv (qfForm (castMat D h)) :=
      { matEquiv P hPu with map_app' := qfForm_matEquiv hPu hP }
    have hR := rep_of_isometryEquiv ψ.symm hRF
    obtain ⟨hsq, hhv⟩ := (D18.rep_diag_iff _ hHil hwG hwF hRG).1 hR
    have hc := hcong.2 (hsqc.1 hsq)
    refine ⟨by rw [huF, huG, hc], ?_⟩
    rw [← hoF, ← hoG]
    exact (hhasse hc).1 hhv
  · rintro ⟨hu, ho⟩
    have hc : (UF : ZMod 8) = UG := by rw [← huF, ← huG, hu]
    have hR : D18.Rep (qfForm (castMat D' h')) (diagonal fun i => ((wF i : ℤ) : ℚ_[2])) :=
      (D18.rep_diag_iff _ hHil hwG hwF hRG).2
        ⟨hsqc.2 (hcong.1 hc), (hhasse hc).2 (by rw [hoF, hoG, ho])⟩
    obtain ⟨ψ⟩ := isometryEquiv_of_rep hRF hR
    set P := LinearMap.toMatrix' (ψ.symm.toLinearEquiv : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    set P' := LinearMap.toMatrix' (ψ.toLinearEquiv : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    have hPP : P * P' = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have : ((ψ.symm.toLinearEquiv : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2])) ∘ₗ
          (ψ.toLinearEquiv : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))) = LinearMap.id := by
        ext x; simp
      rw [this, LinearMap.toMatrix'_id]
    have hPu : IsUnit P.det := by
      have h1 : P.det * P'.det = 1 := by rw [← det_mul, hPP, det_one]
      exact ⟨⟨P.det, P'.det, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
    refine ⟨P, hPu, ?_⟩
    have hmv : ∀ x, P *ᵥ x = ψ.symm x := fun x => LinearMap.toMatrix'_mulVec _ x
    refine D18.mat_ext_of_quad _ _ ?_ (castMat_transpose D' h') fun x => ?_
    · simp [transpose_mul, castMat_transpose, Matrix.mul_assoc]
    · have e := ψ.symm.map_app x
      rw [← Cassels.qf, ← Cassels.qf, Cassels.qf_conj', hmv, ← Cassels.qfForm_apply, e, Cassels.qfForm_apply]

end Global

/-! ### Lattices with two block bases -/

theorem type_eq_of_isTypeI_iff {σ τ : TwoSymbol} {k : ℕ} (h : IsTypeI σ k ↔ IsTypeI τ k) :
    (τ k).type = (σ k).type := by
  unfold IsTypeI at h
  cases h1 : (σ k).type <;> cases h2 : (τ k).type <;> simp_all

section Shape

variable {V : Type*} [AddCommGroup V] [Module ℚ_[2] V] [Module ℤ_[2] V] [IsScalarTower ℤ_[2] ℚ_[2] V]
variable (Q : QuadraticForm ℚ_[2] V)

/-- **Two block bases of one lattice have the same dimensions and types at each scale** (O'Meara 1963, §91C, 91:9:
the Jordan type is an invariant of the lattice). -/
theorem shape_of_two_bases {D D' : List DyBlock} {M : Submodule ℤ_[2] V} (bL : Basis (BIdx D) ℤ_[2] M)
    (bK : Basis (BIdx D') ℤ_[2] M) (hGL : ∀ x y, bil Q (bL x : V) (bL y : V) = bmat D x y)
    (hGK : ∀ x y, bil Q (bK x : V) (bK y : V) = bmat D' x y)
    (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (hD' : ∀ b ∈ D', b.Valid)
    (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) (hfg : M.FG) :
    ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧ (blockSymbol D' k).type = (blockSymbol D k).type := by
  set ks := scaleEnum D
  set ks' := scaleEnum D'
  have hJL := isJordanSplitting_comp Q bL hGL hD hD0 ks ks.strictMono (scaleEnum_range D)
  have hJK := isJordanSplitting_comp Q bK hGK hD' hD'0 ks' ks'.strictMono (scaleEnum_range D')
  obtain ⟨ht, hi⟩ := hJL.sameJordanType Q hfg hJK
  have hneL : ∀ i, ∃ j, bexp D j = ks i := fun i => (scaleEnum_range D _).1 ⟨i, rfl⟩
  have hneK : ∀ i, ∃ j, bexp D' j = ks' i := fun i => (scaleEnum_range D' _).1 ⟨i, rfl⟩
  have hks : ∀ i, ks' (Fin.cast ht i) = ks i := fun i => by
    have := (hi i).1
    simp only [compLat] at this
    rw [scale_comp Q bL hGL hD hD0 (hneL i), scale_comp Q bK hGK hD' hD'0 (hneK _)] at this
    exact (span_two_pow_inj this).symm
  have main : ∀ k, (blockSymbol D k).dim ≠ 0 →
      (blockSymbol D' k).dim = (blockSymbol D k).dim ∧ (blockSymbol D' k).type = (blockSymbol D k).type := by
    intro k hk
    obtain ⟨i, rfl⟩ := (scaleEnum_range D k).2 ((exists_bexp_iff D hD0 k).2 hk)
    obtain ⟨h1, h2, h3⟩ := hi i
    simp only [compLat] at h3
    have h2' : (blockSymbol D (ks i)).dim = (blockSymbol D' (ks' (Fin.cast ht i))).dim := by
      rw [← finrank_comp bL hD0, ← finrank_comp bK hD'0]; exact h2
    rw [hks] at h2'
    refine ⟨h2'.symm, type_eq_of_isTypeI_iff ?_⟩
    rw [normIdeal_comp Q bL hGL hD hD0 (hneL i), scale_comp Q bL hGL hD hD0 (hneL i),
      normIdeal_comp Q bK hGK hD' hD'0 (hneK _), scale_comp Q bK hGK hD' hD'0 (hneK _), hks] at h3
    have e1 : ∀ (ρ : TwoSymbol) (k : ℕ), (ℤ_[2] ∙ (2 : ℚ_[2]) ^ (k + dlt ρ k) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ k) ↔
        IsTypeI ρ k := by
      intro ρ k
      constructor
      · intro h; have := span_two_pow_inj h; by_contra hI; simp [dlt, hI] at this
      · intro hI; simp [dlt, hI]
    rw [e1, e1] at h3
    exact h3
  intro k
  by_cases hk : (blockSymbol D k).dim ≠ 0
  · exact main k hk
  by_cases hk' : (blockSymbol D' k).dim ≠ 0
  · exfalso
    obtain ⟨i', hi'⟩ := (scaleEnum_range D' k).2 ((exists_bexp_iff D' hD'0 k).2 hk')
    apply hk
    rw [← exists_bexp_iff D hD0, ← scaleEnum_range]
    exact ⟨Fin.cast ht.symm i', by rw [← hks]; simpa using hi'⟩
  push Not at hk hk'
  refine ⟨by rw [hk, hk'], ?_⟩
  rw [((blockSymbol_exists D hD k).1 hk).1, ((blockSymbol_exists D' hD' k).1 hk').1]

end Shape

/-! ### Theorem 10 -/

theorem latMap_gl (T : GL (Fin n) ℤ_[2]) (hTu : IsUnit (T.val.map PadicInt.Coe.ringHom).det) :
    latMap (matEquiv (T.val.map PadicInt.Coe.ringHom) hTu) (zpLat 2 n) = zpLat 2 n := by
  ext x
  simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, matEquiv_apply,
    Cassels.mem_zpLat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Cassels.isIntVec_mulVec T.val hy
  · intro hx
    refine ⟨((T⁻¹ : GL (Fin n) ℤ_[2]).val.map PadicInt.Coe.ringHom) *ᵥ x, Cassels.isIntVec_mulVec _ hx, ?_⟩
    rw [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]

/-- A linear automorphism of $\mathbb Q_2^n$ preserving $\mathbb Z_2^n$ has an integral unimodular matrix. -/
theorem um_of_latMap (τ : (Fin n → ℚ_[2]) ≃ₗ[ℚ_[2]] (Fin n → ℚ_[2])) (h : latMap τ (zpLat 2 n) = zpLat 2 n) :
    Cassels.Lemma42.UM (LinearMap.toMatrix' (τ : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))) := by
  have hmem : ∀ x, Cassels.IsIntVec x → Cassels.IsIntVec (τ x) := fun x hx => by
    have : τ x ∈ latMap τ (zpLat 2 n) := ⟨x, Cassels.mem_zpLat.2 hx, rfl⟩
    rw [h] at this; exact Cassels.mem_zpLat.1 this
  have hmem' : ∀ x, Cassels.IsIntVec x → Cassels.IsIntVec (τ.symm x) := fun x hx => by
    have : x ∈ latMap τ (zpLat 2 n) := by rw [h]; exact Cassels.mem_zpLat.2 hx
    obtain ⟨y, hy, rfl⟩ := this
    simpa using Cassels.mem_zpLat.1 hy
  have hsingle : ∀ j : Fin n, Cassels.IsIntVec (Pi.single j (1 : ℚ_[2])) := fun j i => by
    rw [Pi.single_apply]; split_ifs <;> simp
  set A := LinearMap.toMatrix' (τ : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
  set B := LinearMap.toMatrix' (τ.symm : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
  have hA : ∀ i j, ‖A i j‖ ≤ 1 := fun i j => by
    simp only [A, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    exact hmem _ (hsingle j) i
  have hB : ∀ i j, ‖B i j‖ ≤ 1 := fun i j => by
    simp only [B, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    exact hmem' _ (hsingle j) i
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : ((τ : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2])) ∘ₗ
        (τ.symm : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))) = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  refine ⟨hA, ?_⟩
  have h1 := Cassels.dyadic_norm_det_le_one hA
  have h2 := Cassels.dyadic_norm_det_le_one hB
  have h3 : ‖A.det‖ * ‖B.det‖ = 1 := by rw [← norm_mul, ← det_mul, hAB, det_one, norm_one]
  nlinarith [norm_nonneg A.det, norm_nonneg B.det]

theorem bexp_lt_of_supported {D : List DyBlock} (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) {N : ℕ}
    (hN : (blockSymbol D).SupportedBelow N) (j : Fin D.length) : bexp D j < N := by
  by_contra hj
  have h1 := (exists_bexp_iff D hD0 (bexp D j)).1 ⟨j, rfl⟩
  rw [hN _ (by omega)] at h1
  exact h1 rfl

theorem blockSymbol_supported (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    ∃ N, (blockSymbol D).SupportedBelow N := by
  refine ⟨univ.sup (bexp D) + 1, fun k hk => ?_⟩
  have hnil : (D.filter fun b => decide (blockExp b = (k : ℤ))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb hbk
    obtain ⟨j, rfl⟩ := List.get_of_mem hb
    have h1 : bexp D j ≤ univ.sup (bexp D) := Finset.le_sup (Finset.mem_univ j)
    have h2 : blockExp (D.get j) = k := of_decide_eq_true hbk
    simp only [bexp, h2, Int.toNat_natCast] at h1
    omega
  simp only [blockSymbol, hnil, List.map_nil, List.sum_nil, Sign.prodList, List.any_nil]
  rfl

/-- The hypotheses of the symbol-level Theorem 10 for two block decompositions with the same dimensions and types. -/
theorem setting_of_shape {D D' : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (hD' : ∀ b ∈ D', b.Valid)
    (hshape : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧ (blockSymbol D' k).type = (blockSymbol D k).type)
    {N : ℕ} (hN : (blockSymbol D).SupportedBelow N) (hN' : (blockSymbol D').SupportedBelow N) :
    Theorem10Setting (blockSymbol D) (blockSymbol D') N where
  dim_eq k := (hshape k).1
  type_eq k := (hshape k).2
  oddity_typeII k hk := by
    have hkτ : ¬ IsTypeI (blockSymbol D') k := by unfold IsTypeI at hk ⊢; rw [(hshape k).2]; exact hk
    rw [(blockSymbol_exists D hD k).2.2.2.2 (type_eq_II_of_not hk),
      (blockSymbol_exists D' hD' k).2.2.2.2 (type_eq_II_of_not hkτ)]
  eq_of_le k hk := by rw [hN k hk, hN' k hk]
  typeII_of_le k hk := by unfold IsTypeI; rw [hN k hk]; simp [TwoFactor.trivial]

/-- **Theorem 10 for block decompositions.** -/
theorem zpEquiv_castMat_iff {D D' : List DyBlock} (h : dyDim D = n) (h' : dyDim D' = n)
    (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (hD' : ∀ b ∈ D', b.Valid)
    (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) {N : ℕ} (hN : (blockSymbol D).SupportedBelow N)
    (hN' : (blockSymbol D').SupportedBelow N) :
    ZpEquiv (castMat D h) (castMat D' h') ↔ Theorem10Cond (blockSymbol D) (blockSymbol D') N := by
  have hF0s := castMat_transpose D h
  have hQ := nondegenerate_qfForm hF0s (castMat_det_ne D h hD hD0)
  haveI hLat : (zpLat 2 n).IsLattice ℚ_[2] := Cassels.zpLat_isLattice
  have hbN := bexp_lt_of_supported hD0 hN
  have hbN' := bexp_lt_of_supported hD'0 hN'
  have hdimN : ∀ k, N ≤ k → (blockSymbol D k).dim = 0 := fun k hk => by rw [hN k hk]; rfl
  constructor
  · intro hZ
    obtain ⟨T, hT⟩ := hZ
    have hTu : IsUnit (T.val.map PadicInt.Coe.ringHom).det := by
      rw [Cassels.dyadic_det_map_coe]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 T.isUnit).map PadicInt.Coe.ringHom
    set φ := matEquiv (T.val.map PadicInt.Coe.ringHom) hTu
    have hφ : ∀ x, qfForm (castMat D h) (φ x) = qfForm (castMat D' h') x := qfForm_matEquiv hTu hT
    have hLK := latMap_gl T hTu
    set bK : Basis (BIdx D') ℤ_[2] (zpLat 2 n) := (mapBasis φ (bLat D' h')).map (LinearEquiv.ofEq _ _ hLK)
    have hGK : ∀ x y, bil (qfForm (castMat D h)) (bK x : Fin n → ℚ_[2]) (bK y : Fin n → ℚ_[2]) = bmat D' x y := by
      intro x y
      show bil _ (φ (bLat D' h' x)) (φ (bLat D' h' y)) = _
      rw [bil_map φ hφ, gram_bLat]
    have hshape := shape_of_two_bases (qfForm (castMat D h)) (bLat D h) bK (gram_bLat D h) hGK hD hD0 hD' hD'0
      hLat.fg
    have hT10 := setting_of_shape hD hD' hshape hN hN'
    rw [theorem10Cond_iff_omCond hT10 (blockSymbol_exists D hD) (blockSymbol_exists D' hD') hdimN]
    refine ⟨?_, (ratIso_iff h h' hD hD0 hD' hD'0 hshape hbN hbN').1 ⟨_, hTu, hT⟩⟩
    exact (cls_eq_iff_omPair (qfForm (castMat D h)) (bLat D h) bK (gram_bLat D h) hGK hD hD0 hD' hD'0 hshape
      hQ).1 rfl
  · intro hC
    have hshape : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧
        (blockSymbol D' k).type = (blockSymbol D k).type := fun k => ⟨(hC.1 k).1.symm, (hC.1 k).2.symm⟩
    have hT10 := setting_of_shape hD hD' hshape hN hN'
    obtain ⟨hpairs, hU, hO⟩ :=
      (theorem10Cond_iff_omCond hT10 (blockSymbol_exists D hD) (blockSymbol_exists D' hD') hdimN).1 hC
    obtain ⟨P, hPu, hP⟩ := (ratIso_iff h h' hD hD0 hD' hD'0 hshape hbN hbN').2 ⟨hU, hO⟩
    set φ := matEquiv P hPu
    have hφ : ∀ x, qfForm (castMat D h) (φ x) = qfForm (castMat D' h') x := qfForm_matEquiv hPu hP
    haveI : (latMap φ (zpLat 2 n)).IsLattice ℚ_[2] := SuffSub.isLattice_latMap
    set bK := mapBasis φ (bLat D' h')
    have hGK : ∀ x y, bil (qfForm (castMat D h)) (bK x : Fin n → ℚ_[2]) (bK y : Fin n → ℚ_[2]) = bmat D' x y := by
      intro x y
      rw [mapBasis_apply, mapBasis_apply, bil_map φ hφ, gram_bLat]
    have hcls := (cls_eq_iff_omPair (qfForm (castMat D h)) (bLat D h) bK (gram_bLat D h) hGK hD hD0 hD' hD'0
      hshape hQ).2 hpairs
    have hKmem : latMap φ (zpLat 2 n) ∈ cls (qfForm (castMat D h)) (zpLat 2 n) := by
      rw [hcls]; exact ⟨1, Subgroup.one_mem _, by ext x; simp [latMap]⟩
    obtain ⟨σ', hσ', hKσ⟩ := hKmem
    set τ := σ'.trans φ.symm
    have hτ : latMap τ (zpLat 2 n) = zpLat 2 n := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : σ' y ∈ latMap φ (zpLat 2 n) := by rw [hKσ]; exact ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := this
        have : τ y = z := by
          simp only [τ, LinearEquiv.trans_apply]
          rw [← hzy]; simp
        simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
        rw [this]; exact hz
      · intro hx
        have : φ x ∈ latMap σ' (zpLat 2 n) := by rw [← hKσ]; exact ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := this
        refine ⟨y, hy, ?_⟩
        simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, τ, LinearEquiv.trans_apply] at hyx ⊢
        rw [hyx]; simp
    have hUM := um_of_latMap τ hτ
    set Tm := LinearMap.toMatrix' (τ : (Fin n → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    have hTm : Tmᵀ * castMat D' h' * Tm = castMat D h := by
      refine D18.mat_ext_of_quad _ _ ?_ hF0s fun x => ?_
      · simp [transpose_mul, castMat_transpose, Matrix.mul_assoc]
      · have hmv : Tm *ᵥ x = τ x := LinearMap.toMatrix'_mulVec _ x
        have e1 : qfForm (castMat D' h') (φ.symm (σ' x)) = qfForm (castMat D h) (σ' x) := by
          rw [← hφ]; simp
        rw [← Cassels.qf, ← Cassels.qf, Cassels.qf_conj', hmv, ← Cassels.qfForm_apply, ← Cassels.qfForm_apply]
        simp only [τ, LinearEquiv.trans_apply]
        rw [e1]
        exact hσ' x
    exact (Cassels.Lemma42.zpEquiv_of_UM hUM hTm).symm

/-- **Theorem 10** (Conway–Sloane, §7.5, Thm. 10, p. 381): two integral forms $f$, $f'$ over $\mathbb Z_2$ (symmetric
matrices $F$, $G$ over $\mathbb Q_2$) with 2-adic symbols $\sigma$, $\tau$ (`IsTwoSymbolOf`), both vanishing from the scale
$2^N$ on, are $\mathbb Z_2$-equivalent iff (i) $n_q = n'_q$, $S_q = S'_q$ for all $q$ and (ii)
$\sum_{q<2^m}(t_q - t'_q) \equiv 4\sum_{\varepsilon_{2^a} \ne \varepsilon'_{2^a}}\min(a, m) \pmod 8$ for every integer
$m$ (including negative $m$) such that $f_{2^m}$ has type II (`Theorem10Cond`).

*Proof:* via O'Meara's 93:29 (see the file header). -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381"]
theorem zpEquiv_iff_theorem10Cond {F G : Matrix (Fin n) (Fin n) ℚ_[2]} {σ τ : TwoSymbol}
    (hF : IsTwoSymbolOf F σ) (hG : IsTwoSymbolOf G τ) {N : ℕ} (hσ : σ.SupportedBelow N)
    (hτ : τ.SupportedBelow N) : ZpEquiv F G ↔ Theorem10Cond σ τ N := by
  obtain ⟨D, hD, hD0, h, hFD, rfl⟩ := hF
  obtain ⟨D', hD', hD'0, h', hGD, rfl⟩ := hG
  rw [← zpEquiv_castMat_iff h h' hD hD0 hD' hD'0 hσ hτ]
  exact ⟨fun hFG => hFD.symm.trans (hFG.trans hGD), fun h0 => hFD.trans (h0.trans hGD.symm)⟩

theorem supported_of_isTwoSymbolOf {F : Matrix (Fin n) (Fin n) ℚ_[2]} {σ : TwoSymbol} (hF : IsTwoSymbolOf F σ) :
    ∃ N, σ.SupportedBelow N := by
  obtain ⟨D, -, hD0, -, -, rfl⟩ := hF
  exact blockSymbol_supported D hD0

theorem exists_of_isTwoSymbolOf {F : Matrix (Fin n) (Fin n) ℚ_[2]} {σ : TwoSymbol} (hF : IsTwoSymbolOf F σ) :
    ∀ k, (σ k).Exists := by
  obtain ⟨D, hD, -, -, -, rfl⟩ := hF
  exact blockSymbol_exists D hD

/-- **Theorem 10 with the moves** (Conway–Sloane, §7.5, pp. 381–382): two integral forms with 2-adic symbols $\sigma$,
$\tau$ are $\mathbb Z_2$-equivalent iff $\sigma$ and $\tau$ are related by sign walking and oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10 and rules (i), (ii), pp. 381–382"]
theorem zpEquiv_iff_moveEquiv {F G : Matrix (Fin n) (Fin n) ℚ_[2]} {σ τ : TwoSymbol}
    (hF : IsTwoSymbolOf F σ) (hG : IsTwoSymbolOf G τ) : ZpEquiv F G ↔ MoveEquiv σ τ := by
  obtain ⟨N₁, h₁⟩ := supported_of_isTwoSymbolOf hF
  obtain ⟨N₂, h₂⟩ := supported_of_isTwoSymbolOf hG
  have hσ : σ.SupportedBelow (max N₁ N₂) := fun k hk => h₁ k (le_trans (le_max_left _ _) hk)
  have hτ : τ.SupportedBelow (max N₁ N₂) := fun k hk => h₂ k (le_trans (le_max_right _ _) hk)
  have hset : (∀ k, (τ k).dim = (σ k).dim ∧ (τ k).type = (σ k).type) → Theorem10Setting σ τ (max N₁ N₂) :=
    fun hs => {
      dim_eq := fun k => (hs k).1
      type_eq := fun k => (hs k).2
      oddity_typeII := fun k hk => by
        have hkτ : ¬ IsTypeI τ k := by unfold IsTypeI at hk ⊢; rw [(hs k).2]; exact hk
        rw [(exists_of_isTwoSymbolOf hF k).2.2.2.2 (type_eq_II_of_not hk),
          (exists_of_isTwoSymbolOf hG k).2.2.2.2 (type_eq_II_of_not hkτ)]
      eq_of_le := fun k hk => by rw [hσ k hk, hτ k hk]
      typeII_of_le := fun k hk => by unfold IsTypeI; rw [hσ k hk]; simp [TwoFactor.trivial] }
  rw [zpEquiv_iff_theorem10Cond hF hG hσ hτ]
  constructor
  · intro hC
    exact (theorem10Cond_iff_moveEquiv (hset fun k => ⟨(hC.1 k).1.symm, (hC.1 k).2.symm⟩)).1 hC
  · intro hM
    have hS := hM.sameInvariants
    exact (theorem10Cond_iff_moveEquiv (hset fun k => ⟨hS.dim_eq k, hS.type_eq k⟩)).2 hM

/-- **The canonical 2-adic symbol classifies** (Conway–Sloane, §7.6, p. 382): two integral forms are
$\mathbb Z_2$-equivalent iff their 2-adic symbols have the same canonical symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
theorem zpEquiv_iff_canonical_eq {F G : Matrix (Fin n) (Fin n) ℚ_[2]} {σ τ : TwoSymbol}
    (hF : IsTwoSymbolOf F σ) (hG : IsTwoSymbolOf G τ) (hσ : EventuallyTypeII σ) (hτ : EventuallyTypeII τ) :
    ZpEquiv F G ↔ canonical hσ = canonical hτ := by
  rw [zpEquiv_iff_moveEquiv hF hG, moveEquiv_iff_canonical_eq]

/-- **The 2-adic symbol is an invariant up to the moves** (Conway–Sloane, §7.5, p. 381): any two 2-adic symbols of one
form (from two Jordan decompositions) are related by sign walking and oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381"]
theorem moveEquiv_of_isTwoSymbolOf {F : Matrix (Fin n) (Fin n) ℚ_[2]} {σ τ : TwoSymbol}
    (hσ : IsTwoSymbolOf F σ) (hτ : IsTwoSymbolOf F τ) : MoveEquiv σ τ :=
  (zpEquiv_iff_moveEquiv hσ hτ).1 (Cassels.ZpEquiv.refl F)

/-! ### Every integral form has a 2-adic symbol -/

theorem norm_intCast_odd {u : ℤ} (hu : Odd u) : ‖(u : ℚ_[2])‖ = 1 := by
  have h := PadicInt.isUnit_iff.1 (Cassels.dyadic_isUnit_int_cast_of_odd hu)
  rwa [PadicInt.norm_def, PadicInt.coe_intCast] at h

theorem zero_le_of_norm_two_zpow {e : ℤ} (h : ‖(2 : ℚ_[2]) ^ e‖ ≤ 1) : 0 ≤ e := by
  rw [norm_two_zpow] at h
  exact (zpow_le_one_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).1 h

/-- A block with integral entries has exponent $\ge 0$. -/
theorem exp_nonneg_of_int (b : DyBlock) (hv : b.Valid) (h : ∀ r s, ‖b.mat r s‖ ≤ 1) : 0 ≤ blockExp b := by
  cases b with
  | sq e u =>
    have hu : Odd u := by
      simp only [DyBlock.Valid] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    have h1 := h ⟨0, by simp [DyBlock.dim]⟩ ⟨0, by simp [DyBlock.dim]⟩
    change ‖(!![(2 : ℚ_[2]) ^ e * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]) 0 0‖ ≤ 1 at h1
    simp only [of_apply, cons_val', cons_val_fin_one, empty_val'] at h1
    rw [norm_mul, norm_intCast_odd hu, mul_one] at h1
    exact zero_le_of_norm_two_zpow h1
  | hyp e =>
    have h1 := h ⟨0, by simp [DyBlock.dim]⟩ ⟨1, by simp [DyBlock.dim]⟩
    change ‖((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) 0 1‖ ≤ 1 at h1
    simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, smul_eq_mul, mul_one] at h1
    exact zero_le_of_norm_two_zpow h1
  | ell e =>
    have h1 := h ⟨0, by simp [DyBlock.dim]⟩ ⟨1, by simp [DyBlock.dim]⟩
    change ‖((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])) 0 1‖ ≤ 1 at h1
    simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, smul_eq_mul, mul_one] at h1
    exact zero_le_of_norm_two_zpow h1

/-- **Every nonsingular integral form has a 2-adic symbol** (Conway–Sloane, §7.4, p. 380, with the Jordan decomposition
of Theorem 2, §4.4, in Cassels' normalization, Ch. 8, Lemma 4.1): a symmetric matrix $F$ over $\mathbb Q_2$ with entries
in $\mathbb Z_2$ and $\det F \ne 0$ has a 2-adic symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.4, p. 380"]
theorem exists_isTwoSymbolOf (F : Matrix (Fin n) (Fin n) ℚ_[2]) (hF : Fᵀ = F) (hdet : F.det ≠ 0)
    (hint : ∀ i j, ‖F i j‖ ≤ 1) : ∃ σ, IsTwoSymbolOf F σ := by
  obtain ⟨D, hD, h, hFD⟩ := Cassels.exists_dyadic_decomp F hF hdet
  have hGint : ∀ i j, ‖castMat D h i j‖ ≤ 1 := by
    obtain ⟨T, hT⟩ := hFD
    obtain ⟨Fz, rfl⟩ := Cassels.dyadic_lift_mat hint
    have e : (T.val.map PadicInt.Coe.ringHom)ᵀ * Fz.map PadicInt.Coe.ringHom * T.val.map PadicInt.Coe.ringHom =
        (T.valᵀ * Fz * T.val).map PadicInt.Coe.ringHom := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
    intro i j
    change ‖((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) i j‖ ≤ 1
    rw [← hT, e, map_apply]
    exact PadicInt.norm_le_one _
  have hD0 : ∀ b ∈ D, 0 ≤ blockExp b := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.get_of_mem hb
    refine exp_nonneg_of_int _ (hD _ hb) fun r s => ?_
    have := hGint ((bE D h).symm ⟨j, r⟩) ((bE D h).symm ⟨j, s⟩)
    rwa [castMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, bmat, blockDiagonal'_apply_eq] at this
  exact ⟨blockSymbol D, D, hD, hD0, h, hFD, rfl⟩

end QuadFormsKB.ConwaySloane.TwoAdic

end
