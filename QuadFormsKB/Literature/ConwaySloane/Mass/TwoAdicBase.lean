/-
# Formula (3) at $p = 2$: the even unimodular base case

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263; Table 1 and Table 2, p. 264; §12, p. 281 (bibliography key `conwaysloane1988`).

**Proves** `pMassDensity_intMat_typeII_unimodular` (unconditional): for a list $D$ of Cassels' blocks $2xy$
(`hyp 0`, Gram matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$) and $2x^2 + 2xy + 2y^2$ (`ell 0`, Gram matrix
$\begin{pmatrix}2&1\\1&2\end{pmatrix}$), with orthogonal sum $A$ = `intMat D` (even unimodular, rank $n = 2m$,
$m$ the number of blocks), the counting 2-mass of §12 is
$$m_2(A) = M_2(f_1)\,2^{-n},$$
$M_2(f_1)$ the diagonal factor (`mFac`) of the species of the free type II constituent $f_1$ of Table 1: $2m+$ if the
number $e$ of blocks `ell 0` is even (octane value $0$), $2m-$ if it is odd (octane value $4$); for $D = []$ both sides are
$1$. Equivalently $\alpha_2(A) = 2^n\cdot 2\prod_{i=1}^{m-1}(1 - 2^{-2i})\,(1 \mp 2^{-m})$.

**Route.** $\alpha_2(A) = 2^n\beta_2(Q', Q')$ for the quadratic form $Q'(x) = x^{\mathsf T}Ax/2$ with Hessian $A$
over $\mathbb Z_2$ (`Base.alphaP_eq_localDensityForm_half`: Hanke's $\beta_2 = \tfrac12\alpha_2$ for the form
$x^{\mathsf T}Ax = 2Q'(x)$, the comparison `hankeBeta_gramV`, and the scaling law `Tamagawa.localDensityForm_smul`).
The self-density of the unimodular $Q'$ is $2(1 - \varepsilon 2^{-m})\prod_{i=1}^{m-1}(1 - 2^{-2i})$ from the order of
$O^\varepsilon_{2m}(\mathbb F_2)$ (`Hanke2005.card_orthMod_even`, `Hanke2005.localDensityForm_self_even_of_card`), with
$\varepsilon = +1$ iff the reduction has Witt index $m$, iff $(-1)^m\det A$ is a square in $\mathbb Z_2$
(`Hanke2005.arfSignQ_eq_one_iff_wittIndex`, `DVR.arfSignQ_eq_one_iff`). Here $(-1)^m\det A = (-3)^e$, a square iff $e$
is even ($-3 = 1 - 4$, and $z^2 + z = 1$ has no solution in $\mathbb F_2$; `Base.isSquare_neg_three_pow_iff`).
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicStep
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm
import QuadFormsKB.Literature.Hanke2005.DensityDyadicWitt
import QuadFormsKB.Tamagawa.AlphaLawMoves

set_option linter.unusedSectionVars false

open QuadFormsKB IsDedekindDomain NumberField Matrix

noncomputable section

namespace QuadFormsKB.ConwaySloane.Mass.Two.Base

open Hanke2011Structure Tamagawa.RatBridge

variable {n : ℕ}

/-- The form $x \mapsto x^{\mathsf T}Ax/2$ (Hessian $A$) of a symmetric $A$ with even diagonal. -/
def halfForm (A : Matrix (Fin n) (Fin n) ℤ) : QuadForm ℤ n :=
  ⟨halfUp A, fun i j h => by
    simp only [id] at h
    simp [halfUp, not_lt.mpr h.le, h.ne']⟩

theorem hessian_halfForm {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (he : EvenDiag A) :
    (halfForm A).hessian = A :=
  halfUp_add_transpose hA.eq he

theorem ofMatrixZ_eq {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (he : EvenDiag A) :
    LocalDensity.ofMatrixZ A = (2 : ℤ) • halfForm A := by
  ext i j
  simp only [LocalDensity.ofMatrixZ, halfForm, halfUp, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h, ite_true]
    rw [show A j i = A i j from hA.apply i j]; ring
  · simp only [lt_irrefl, ite_false, ite_true]
    exact (Int.mul_ediv_cancel' (he i)).symm
  · simp [not_lt.mpr h.le, h.ne']

theorem map_smul' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : QuadForm R n) :
    (c • Q).map f = f c • Q.map f := by
  ext i j
  simp [QuadForm.map]

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem two_assoc (hv : pv v = 2) : Associated (2 : 𝔬) (LocalDensity.NF.π v) := by
  have h := eInt_assoc v
  rw [map_natCast] at h
  rwa [hv] at h

theorem pi_dvd_two (hv : pv v = 2) : LocalDensity.NF.π v ∣ (2 : 𝔬) := (two_assoc v hv).symm.dvd

theorem not_pi_sq_dvd_two (hv : pv v = 2) : ¬ LocalDensity.NF.π v ^ 2 ∣ (2 : 𝔬) := by
  intro hd
  have h1 : LocalDensity.NF.π v * LocalDensity.NF.π v ∣ LocalDensity.NF.π v * 1 := by
    rw [mul_one, ← sq]; exact hd.trans (two_assoc v hv).dvd
  have h2 := (mul_dvd_mul_iff_left (LocalDensity.NF.irreducible_π v).ne_zero).mp h1
  exact (LocalDensity.NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h2)

theorem norm_two (hv : pv v = 2) : ‖(2 : v.adicCompletion ℚ)‖ = 1 / 2 := by
  have h := norm_prime_completion v
  rw [hv] at h
  simpa using h

theorem q_two (hv : pv v = 2) : (LocalDensity.DVR.q 𝔬 : ℝ) = 2 := by
  rw [q_eq, hv]; norm_num

theorem tri_split (n : ℕ) : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | n
  · simp
  · have : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1 - 1) + 2 * (n + 1) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ two_pos]

/-- **The bridge at $p = 2$**: $\alpha_2(A) = 2^n\beta_2(Q', Q')$ for the form $Q'$ with Hessian $A$. -/
theorem alphaP_eq_localDensityForm_half (hv : pv v = 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (he : EvenDiag A) (hdet : A.det ≠ 0) :
    alphaP 2 A = (2 : ℝ) ^ n * LocalDensity.DVR.localDensityForm (LocalDensity.NF.Qp v (up (halfForm A)))
      (LocalDensity.NF.Qp v (up (halfForm A))) (LocalDensity.NF.π v) := by
  have h1 := Hanke2005.hankeBeta_gramV v (up (LocalDensity.ofMatrixZ A)) (nondegenerate_up hA hdet)
  have h2 := localBeta_ofMatrixZ v hA hdet
  unfold localBeta at h2
  rw [h1, LocalDensity.NF.siegelDensity, if_pos rfl, LocalDensity.NF.localDensityForm_eq_completion] at h2
  have hQ : LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A)) =
      (2 : 𝔬) • LocalDensity.NF.Qp v (up (halfForm A)) := by
    rw [ofMatrixZ_eq hA he]
    show QuadForm.map _ (QuadForm.map _ _) = _
    rw [map_smul', map_smul', map_ofNat, map_ofNat]
  have hnd : (LocalDensity.NF.Qp v (up (halfForm A))).Nondegenerate := by
    refine LocalDensity.NF.nondegenerate_Qp v ?_
    unfold QuadForm.Nondegenerate
    rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hessian_halfForm hA he]
    exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 ℚ)).injective_int).mpr hdet
  rw [hQ, Tamagawa.localDensityForm_smul _ hnd (LocalDensity.NF.irreducible_π v) (o := 1)
    (by rw [pow_one]; exact pi_dvd_two v hv) (not_pi_sq_dvd_two v hv), norm_two v hv, q_two v hv, hv] at h2
  rw [tri_split, one_mul, pow_add] at h2
  have h3 : (1 / 2 : ℝ) ^ (n * (n - 1) / 2) * 2 ^ (n * (n - 1) / 2) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-2 : ℝ) * h2 + (2 : ℝ) ^ n *
    LocalDensity.DVR.localDensityForm (LocalDensity.NF.Qp v (up (halfForm A)))
      (LocalDensity.NF.Qp v (up (halfForm A))) (LocalDensity.NF.π v) * h3

theorem hessian_det_Qp_half {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (he : EvenDiag A) :
    (LocalDensity.NF.Qp v (up (halfForm A))).hessian.det = ((A.det : ℤ) : 𝔬) := by
  rw [LocalDensity.NF.det_hessian_Qp, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    hessian_halfForm hA he]
  simp

theorem isUnit_hessian_det_Qp_half (hv : pv v = 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (he : EvenDiag A) (hodd : ¬ 2 ∣ A.det) :
    IsUnit (LocalDensity.NF.Qp v (up (halfForm A))).hessian.det := by
  refine LocalDensity.DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) ?_
  apply LocalDensity.NF.π_not_dvd_det
  rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hessian_halfForm hA he]
  have : (Rat.HeightOneSpectrum.natGenerator v : ℕ) = 2 := hv
  rw [show (Int.castRingHom (𝓞 ℚ)) A.det = ((A.det : ℤ) : 𝓞 ℚ) by simp, Tamagawa.RatHeadline3.intCast_mem_iff,
    this]
  exact_mod_cast hodd

open Classical in
/-- **The self-density of the even unimodular form with Hessian $A$** at $p = 2$, $n = 2(j+1)$. -/
theorem localDensityForm_half (hv : pv v = 2) {j : ℕ} {A : Matrix (Fin (2 * (j + 1))) (Fin (2 * (j + 1))) ℤ}
    (hA : A.IsSymm) (he : EvenDiag A) (hodd : ¬ 2 ∣ A.det) :
    LocalDensity.DVR.localDensityForm (LocalDensity.NF.Qp v (up (halfForm A)))
      (LocalDensity.NF.Qp v (up (halfForm A))) (LocalDensity.NF.π v) =
      2 * (1 - ((if IsSquare ((((-1) ^ (j + 1) * A.det : ℤ)) : 𝔬) then 1 else -1 : ℤ) : ℝ) *
        ((2 : ℝ) ^ (j + 1))⁻¹) * ∏ i ∈ Finset.range j, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  classical
  have : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := pi_dvd_two v hv
  have hdet := isUnit_hessian_det_Qp_half v hv hA he hodd
  have hc := Hanke2005.card_orthMod_even hπ h2 (m := j + 1) (by omega) _ hdet
  rw [Hanke2005.localDensityForm_self_even_of_card (j + 1) (by omega) _ _ hπ hdet _ hc, q_two v hv,
    Nat.add_sub_cancel]
  have hw := (Hanke2005.arfSignQ_eq_one_iff_wittIndex hπ h2 _ hdet).symm.trans
    (LocalDensity.DVR.arfSignQ_eq_one_iff _ hπ h2 (LocalDensity.NF.two_ne_zero' v)
      (Hanke2005.isLocalLevel_zero_of_isUnit_det _ _ hdet) (by omega))
  have e : ((-1 : 𝔬) ^ (j + 1) * ((A.det : ℤ) : 𝔬)) = (((-1) ^ (j + 1) * A.det : ℤ) : 𝔬) := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hessian_det_Qp_half v hA he, show 2 * (j + 1) / 2 = j + 1 by omega, e] at hw
  simp only [hw]

theorem isUnit_three (hv : pv v = 2) : IsUnit (3 : 𝔬) := by
  have hπ := LocalDensity.NF.irreducible_π v
  refine LocalDensity.DVR.dvr_isUnit_of_not_dvd hπ fun h3 => hπ.not_isUnit (isUnit_of_dvd_one ?_)
  have := dvd_sub h3 (pi_dvd_two v hv)
  norm_num at this
  exact this

/-- $(-3)^k$ is a square in $\mathbb Z_2$ iff $k$ is even ($-3 = 1 - 4$ and $z^2 + z \ne 1$ in $\mathbb F_2$). -/
theorem isSquare_neg_three_pow_iff (hv : pv v = 2) (k : ℕ) :
    IsSquare ((((-3) ^ k : ℤ)) : 𝔬) ↔ Even k := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := pi_dvd_two v hv
  constructor
  · intro hs
    by_contra hk
    obtain ⟨l, rfl⟩ := Nat.not_even_iff_odd.mp hk
    have hu : IsUnit ((-3 : 𝔬) ^ l) := ((isUnit_three v hv).neg).pow l
    have e : ((((-3) ^ (2 * l + 1) : ℤ)) : 𝔬) = ((-3 : 𝔬) ^ l) ^ 2 * (1 - 4 * 1) := by
      push_cast; ring
    rw [e, LocalDensity.DVR.isSquare_unit_sq_mul_iff hu,
      LocalDensity.DVR.isSquare_one_sub_four_mul_iff hπ h2 (LocalDensity.NF.two_ne_zero' v)] at hs
    obtain ⟨z, hz⟩ := hs
    classical
    have : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
    have hcard : Fintype.card (IsLocalRing.ResidueField 𝔬) = 2 := by
      have := q_eq v
      rw [hv, LocalDensity.DVR.q, Nat.card_eq_fintype_card] at this
      exact this
    have hc := LocalDensity.DVR.charP_residueField_two hπ h2
    have hzz : z ^ 2 = z := by rw [← hcard]; exact FiniteField.pow_card z
    rw [hzz, map_one, ← two_mul, CharTwo.two_eq_zero, zero_mul] at hz
    exact zero_ne_one hz
  · rintro ⟨l, rfl⟩
    exact ⟨(((-3) ^ l : ℤ) : 𝔬), by push_cast; ring⟩

end QuadFormsKB.ConwaySloane.Mass.Two.Base

namespace QuadFormsKB.ConwaySloane.Mass.Two.Base

/-- **$\alpha_2$ of an even unimodular form** of rank $n = 2(j+1)$ with $(-1)^{j+1}\det A = (-3)^k$. -/
theorem alphaP_evenUnimodular {n j k : ℕ} (hn : n = 2 * (j + 1)) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (he : EvenDiag A) (hd : (-1) ^ (j + 1) * A.det = (-3) ^ k) :
    alphaP 2 A = (2 : ℝ) ^ n * (2 * (1 - (-1 : ℝ) ^ k * ((2 : ℝ) ^ (j + 1))⁻¹) *
      ∏ i ∈ Finset.range j, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹)) := by
  subst hn
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), pv v = 2 :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩, congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (⟨2, Nat.prime_two⟩ : Nat.Primes))⟩
  have hodd : ¬ 2 ∣ A.det := by
    intro h2
    have h3 : (2 : ℤ) ∣ (-3) ^ k := hd ▸ h2.mul_left _
    have := Int.prime_two.dvd_of_dvd_pow h3
    omega
  have hdet : A.det ≠ 0 := fun h0 => hodd (h0 ▸ dvd_zero 2)
  rw [alphaP_eq_localDensityForm_half v hv hA he hdet, localDensityForm_half v hv hA he hodd, hd,
    isSquare_neg_three_pow_iff v hv k]
  rcases Nat.even_or_odd k with hk | hk
  · simp [hk, hk.neg_one_pow]
  · simp [Nat.not_even_iff_odd.mpr hk, hk.neg_one_pow]

open Cassels

/-- The block is $2x^2 + 2xy + 2y^2$ (any exponent). -/
def isEll : DyBlock → Bool
  | .ell _ => true
  | _ => false

/-- The blocks of an even unimodular decomposition. -/
def IsBase (D : List DyBlock) : Prop := ∀ b ∈ D, b = .hyp 0 ∨ b = .ell 0

theorem IsBase.tail {b : DyBlock} {D : List DyBlock} (h : IsBase (b :: D)) : IsBase D :=
  fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem isSymm_bInt' (b : DyBlock) : (bInt b).IsSymm := by
  cases b with
  | sq e u => ext i j; fin_cases i; fin_cases j; rfl
  | hyp e =>
    show ((2 ^ e.toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ))ᵀ = (2 ^ e.toNat : ℤ) • !![0, 1; 1, 0]
    rw [transpose_smul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> rfl
  | ell e =>
    show ((2 ^ e.toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ))ᵀ = (2 ^ e.toNat : ℤ) • !![2, 1; 1, 2]
    rw [transpose_smul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem isSymm_orthSumMat' {a b : ℕ} {F : Matrix (Fin a) (Fin a) ℤ} {G : Matrix (Fin b) (Fin b) ℤ}
    (hF : F.IsSymm) (hG : G.IsSymm) : (orthSumMat F G).IsSymm := by
  unfold Matrix.IsSymm
  rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix, fromBlocks_transpose, hF.eq, hG.eq]
  simp

theorem isSymm_intMat' : ∀ D : List DyBlock, (intMat D).IsSymm
  | [] => by unfold intMat; exact Matrix.isSymm_zero
  | b :: D => isSymm_orthSumMat' (isSymm_bInt' b) (isSymm_intMat' D)

theorem dyDim_base : ∀ D : List DyBlock, IsBase D → dyDim D = 2 * D.length
  | [], _ => rfl
  | b :: D, h => by
    rcases h b List.mem_cons_self with rfl | rfl <;>
      simp [dyDim, DyBlock.dim, dyDim_base D h.tail] <;> ring

theorem det_base : ∀ D : List DyBlock, IsBase D →
    (-1) ^ D.length * (intMat D).det = (-3) ^ D.countP isEll
  | [], _ => by
    show (-1) ^ 0 * Matrix.det (0 : Matrix (Fin 0) (Fin 0) ℤ) = (-3) ^ 0
    simp
  | b :: D, h => by
    have ih := det_base D h.tail
    show (-1) ^ (b :: D).length * (orthSumMat (bInt b) (intMat D)).det = _
    rw [det_orthSumMat]
    rcases h b List.mem_cons_self with rfl | rfl
    · have hb : (bInt (.hyp 0)).det = -1 := by
        show ((2 ^ (0 : ℤ).toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)).det = -1
        simp [det_fin_two_of]
      rw [hb, List.countP_cons, List.length_cons]
      simp only [isEll, Bool.false_eq_true, ite_false, add_zero, pow_succ, ← ih]
      ring
    · have hb : (bInt (.ell 0)).det = 3 := by
        show ((2 ^ (0 : ℤ).toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ)).det = 3
        simp [det_fin_two_of]
      rw [hb, List.countP_cons, List.length_cons]
      simp only [isEll, ite_true, pow_succ, ← ih]
      ring

theorem prodList_base : ∀ D : List DyBlock, IsBase D →
    (Sign.prodList (D.map blockSign)).toInt = (-1) ^ D.countP isEll
  | [], _ => rfl
  | b :: D, h => by
    have ih := prodList_base D h.tail
    rw [List.map_cons, Sign.prodList, Sign.toInt_mul, ih, List.countP_cons]
    rcases h b List.mem_cons_self with rfl | rfl <;> simp [blockSign, isEll, Sign.toInt, pow_succ]

theorem oddity_base : ∀ D : List DyBlock, IsBase D → (D.map blockOddity).sum = 0
  | [], _ => rfl
  | b :: D, h => by
    rw [List.map_cons, List.sum_cons, oddity_base D h.tail]
    rcases h b List.mem_cons_self with rfl | rfl <;> rfl

theorem any_sq_base (D : List DyBlock) (h : IsBase D) : D.any (fun b => decide (IsSqBlock b)) = false := by
  rw [List.any_eq_false]
  intro b hb
  rcases h b hb with rfl | rfl <;> simp [IsSqBlock]

theorem blockSymbol_base_zero (D : List DyBlock) (h : IsBase D) :
    blockSymbol D 0 = ⟨2 * D.length, Sign.prodList (D.map blockSign), .II, 0⟩ := by
  have hf : D.filter (fun b => decide (blockExp b = ((0 : ℕ) : ℤ))) = D :=
    List.filter_eq_self.2 fun b hb => by rcases h b hb with rfl | rfl <;> rfl
  unfold blockSymbol
  simp only
  rw [hf, any_sq_base D h, oddity_base D h, ← dyDim_eq_sum, dyDim_base D h]
  rfl

theorem blockSymbol_base_one (D : List DyBlock) (h : IsBase D) : (blockSymbol D 1).type = .II := by
  have hf : D.filter (fun b => decide (blockExp b = ((1 : ℕ) : ℤ))) = [] :=
    List.filter_eq_nil_iff.2 fun b hb => by rcases h b hb with rfl | rfl <;> decide
  unfold blockSymbol
  simp only
  rw [hf]
  rfl

theorem mFac_base (D : List DyBlock) (h : IsBase D) :
    mFac (blockSymbol D) 0 = (Species.mk (2 * D.length) (Sign.prodList (D.map blockSign))).diagFactor 2 := by
  have hb : ¬ IsBound (blockSymbol D) 0 := by
    rintro (⟨h0, -⟩ | h1)
    · exact h0 rfl
    · rw [blockSymbol_base_one D h] at h1; exact absurd h1 (by decide)
  unfold mFac
  congr 1
  rw [blockSymbol_base_zero D h]
  unfold twoSpecies
  simp only [hb, false_or, octane, ite_true]
  rw [show 2 * D.length / 2 = D.length by omega]
  generalize Sign.prodList (D.map blockSign) = s
  cases s <;> simp (config := { decide := true })

end QuadFormsKB.ConwaySloane.Mass.Two.Base

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Cassels

/-- **The 2-mass of an even unimodular form** (Conway–Sloane 1988, (3) at $p = 2$ for a single free type II
constituent $f_1$, with Table 1): for a list $D$ of blocks `hyp 0` ($2xy$) and `ell 0` ($2x^2 + 2xy + 2y^2$),
$$m_2(\texttt{intMat }D) = M_2(f_1)\cdot 2^{-n},\qquad n = \dim f_1 = 2m,$$
where $M_2(f_1)$ (`mFac (blockSymbol D) 0`) is the diagonal factor of the species $2m+$ (an even number of blocks `ell 0`)
or $2m-$ (an odd number), i.e. $M_2(2m\pm) = \bigl(2\prod_{i=1}^{m-1}(1 - 2^{-2i})(1 \mp 2^{-m})\bigr)^{-1}$, and
$2^{-n} = 2^{-n(\mathrm{II})}$ is the type factor of (3). The hypothesis `hv` (valid blocks) is not needed. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264 (even unimodular constituent, p = 2)"]
theorem pMassDensity_intMat_typeII_unimodular (D : List DyBlock) (_hv : ∀ b ∈ D, b.Valid)
    (h0 : ∀ b ∈ D, blockExp b = 0) (hII : ∀ b ∈ D, ¬ IsSqBlock b) :
    pMassDensity 2 (intMat D) = (mFac (blockSymbol D) 0 : ℝ) * (2 : ℝ) ^ (-(dyDim D : ℤ)) := by
  have hB : Base.IsBase D := by
    intro b hb
    have e := h0 b hb
    have s := hII b hb
    cases b with
    | sq e u => exact absurd trivial s
    | hyp e => left; simp only [blockExp] at e; rw [e]
    | ell e => right; simp only [blockExp] at e; rw [e]
  rw [Base.mFac_base D hB]
  rcases hL : D.length with _ | j
  · obtain rfl : D = [] := List.length_eq_zero_iff.mp hL
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show pMassDensity 2 (intMat []) = 1 from pMassDensity_fin_zero _]
    simp [Species.diagFactor, dyDim]
  · have hd := Base.det_base D hB
    rw [hL] at hd
    have hodd : ¬ 2 ∣ (intMat D).det := by
      intro h2
      have h3 : (2 : ℤ) ∣ (-3) ^ D.countP Base.isEll := hd ▸ h2.mul_left _
      have := Int.prime_two.dvd_of_dvd_pow h3
      omega
    have hn : dyDim D = 2 * (j + 1) := by rw [Base.dyDim_base D hB, hL]
    have hα := Base.alphaP_evenUnimodular hn (Base.isSymm_intMat' D)
      (evenDiag_intMat D (fun b hb => by rw [h0 b hb]) fun b hb hs => hII b hb hs.1) hd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hval : padicValInt 2 (intMat D).det = 0 := padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hodd)
    have hs := Base.prodList_base D hB
    unfold pMassDensity
    rw [hval, hα, hn, _root_.zpow_neg, zpow_natCast]
    simp only [Species.diagFactor, show 2 * (j + 1) ≠ 0 by omega, ite_false,
      show ¬ Odd (2 * (j + 1)) by simp, show 2 * (j + 1) / 2 = j + 1 by omega, Nat.add_sub_cancel, lowerProd]
    rw [show ((Sign.prodList (D.map blockSign)).toInt : ℚ) = (-1) ^ D.countP Base.isEll by rw [hs]; push_cast; rfl]
    push_cast
    simp only [zero_mul, zero_div, Real.rpow_zero]
    have h1 : (0 : ℝ) < 1 - (-1) ^ D.countP Base.isEll * ((2 : ℝ) ^ (j + 1))⁻¹ := by
      have : ((2 : ℝ) ^ (j + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))
      have : (0 : ℝ) < ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
      rcases neg_one_pow_eq_or ℝ (D.countP Base.isEll) with h | h <;> rw [h] <;> linarith
    have h2 : (0 : ℝ) < ∏ i ∈ Finset.range j, (1 - ((2 : ℝ) ^ (2 * (i + 1)))⁻¹) := by
      have := (Rat.cast_pos (K := ℝ)).mpr (lowerProd_pos j)
      unfold lowerProd at this
      push_cast at this
      exact this
    field_simp

end QuadFormsKB.ConwaySloane.Mass.Two
