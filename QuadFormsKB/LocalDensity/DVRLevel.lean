/-
# Local densities over a DVR: the local level, Lemma 2.2, and dyadic $\pi \nmid N$

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$; at the end, finite residue field).
**Defines** the local level (Hanke 2004, p. 355: $N$ is the largest integral ideal with $N(2Q)^{-1}$ integral with
diagonal in $2\mathfrak o$; $2Q$ is the Hessian $H$): `DVR.IsLocalLevel Q π k` says $\pi^k H^{-1}$ is an integral symmetric
matrix with even diagonal, and `DVR.levelExp Q π` $= \mathrm{ord}_\pi N$ is the least such $k$; $\mathrm{ord}_\pi D_{2Q}$ is
$\mathrm{ord}_\pi \det H$. The binary form $ax^2 + bxy + cy^2$ is `DVR.binForm a b c`.

**Proves** $\mathrm{GL}_n(R)$-invariance of the level; Lemma 2.2 at non-dyadic $\pi$ (`DVR.lemma_2_2_nondyadic`:
$\pi \mid N \iff \pi \mid \det H \iff$ some $\nu_j \ge 1$); (2.4) and (2.5) for 1-dimensional blocks at every $\pi$
(`DVR.isLocalLevel_diag_iff_exp`, `DVR.det_hessian_diag_exp`: $\lambda'' = \nu + 2\,\mathrm{ord}_\pi 2$, $\lambda' = \nu + \mathrm{ord}_\pi 2$,
as printed) and for 2-dimensional blocks (`DVR.isLocalLevel_binForm_iff`, `DVR.binForm_normal`): in Hanke's normal form
$\lambda'' = \nu$ as printed, but $\mathrm{ord}_\pi \det = 2\nu$, so the printed $\lambda'_j = \nu_j$ in (2.4) is an erratum
(`DVR.det_hessian_binForm_erratum`); at ramified dyadic primes $x^2 + \pi xy + y^2$ is a norm-indexed block with $w = 0$
and $\pi^2 \mid N$, so (2.5) and Lemma 2.2 fail as printed with $\nu = w$ (`DVR.lemma_2_2_ramified_counterexample`).
At dyadic $\pi \nmid N$ (`DVR.isLocalLevel_zero_jordanW`): no 1-dimensional blocks, and every block has $b$ a unit (so
$w = \mu = 0$). Hence $Q \cong$ `pairSumForm A` with all $b_i$ units (`DVR.exists_pairSum_of_isLocalLevel_zero`), and
conversely; so "$\pi \nmid N \iff$ unimodular" at every prime (`DVR.isLocalLevel_zero_iff_unimodular`). The dyadic results of
`DVRDyadicTable.lean` and `DVRLowerBounds.lean` then hold for every $Q$ with $\pi \nmid N$, with the intrinsic Arf sign
`DVR.arfSignQ`. Remark 3.8.1: $\pi \nmid N$, $n \ge 3$ ⇒ isotropic (`DVR.isotropicIn_of_isLocalLevel_zero`).
**Depends on** `DVRUnimodular.lean`.
-/
import QuadFormsKB.LocalDensity.DVRUnimodular

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix Filter

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-! ### The local level -/

section Level

/-- **$\pi^k$ is a local level of $Q$** (Hanke 2004, p. 355, the level $N_Q$ locally at $\mathfrak p$): there is a symmetric
matrix $W$ over $R$ with even diagonal ($2 \mid W_{ii}$) and $HW = \pi^k I$, i.e. $\pi^k H^{-1}$ is integral with diagonal in
$2R$ (Hanke writes $N(2Q)^{-1}$ with $Q$ his Gram matrix, so $2Q = H$). "$\pi \nmid N$" is `IsLocalLevel Q π 0`. -/
@[kb "hanke2004" "p. 355 (level N_Q, local)"]
def IsLocalLevel (Q : QuadForm R n) (π : R) (k : ℕ) : Prop :=
  ∃ W : Matrix (Fin n) (Fin n) R, Q.hessian * W = π ^ k • (1 : Matrix (Fin n) (Fin n) R) ∧ Wᵀ = W ∧
    ∀ i, 2 ∣ W i i

theorem IsLocalLevel.mono {Q : QuadForm R n} {π : R} {k k' : ℕ} (h : IsLocalLevel Q π k) (hk : k ≤ k') :
    IsLocalLevel Q π k' := by
  obtain ⟨W, hW, hs, hd⟩ := h
  refine ⟨π ^ (k' - k) • W, ?_, by rw [transpose_smul, hs], fun i => ?_⟩
  · rw [Matrix.mul_smul, hW, smul_smul, ← pow_add, Nat.sub_add_cancel hk]
  · rw [Matrix.smul_apply, smul_eq_mul]; exact (hd i).mul_left _

/-- **A level exists** for $Q$ nondegenerate ($2 \ne 0$): $\pi^{v}$ with $\pi^v u = 2\det H$ ($W = 2u^{-1}\operatorname{adj} H$). -/
theorem exists_isLocalLevel {Q : QuadForm R n} (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) : ∃ k, IsLocalLevel Q π k := by
  obtain ⟨v, u, hv, hu⟩ := dvr_eq_pow_mul_unit hπ (mul_ne_zero h20 hQ)
  refine ⟨v, (hu.unit⁻¹ : Rˣ).val • (2 : R) • Q.hessian.adjugate, ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, hv, mul_left_comm, IsUnit.val_inv_mul, mul_one]
  · rw [transpose_smul, transpose_smul, adjugate_transpose, hessian_transpose]
  · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]; exact (dvd_mul_right 2 _).mul_left _

open Classical in
/-- **The local level exponent** $\mathrm{ord}_\pi N$ (Hanke 2004, p. 355): the least $k$ with `IsLocalLevel Q π k`
($0$ if there is none, a junk value for degenerate $Q$). -/
@[kb "hanke2004" "p. 355 (ord_p N_Q)"]
noncomputable def levelExp (Q : QuadForm R n) (π : R) : ℕ :=
  if h : ∃ k, IsLocalLevel Q π k then Nat.find h else 0

/-- The levels are the $\pi^k$ with $k \ge \mathrm{ord}_\pi N$. -/
theorem isLocalLevel_iff_levelExp_le {Q : QuadForm R n} {π : R} (hex : ∃ k, IsLocalLevel Q π k) (k : ℕ) :
    IsLocalLevel Q π k ↔ levelExp Q π ≤ k := by
  classical
  simp only [levelExp, hex, ↓reduceDIte]
  exact ⟨fun h => Nat.find_min' hex h, fun h => (Nat.find_spec hex).mono h⟩

/-- $\pi \nmid N \iff \mathrm{ord}_\pi N = 0$. -/
theorem levelExp_eq_zero_iff {Q : QuadForm R n} {π : R} (hex : ∃ k, IsLocalLevel Q π k) :
    levelExp Q π = 0 ↔ IsLocalLevel Q π 0 := by
  rw [isLocalLevel_iff_levelExp_le hex]; omega

/-- $\vec r^{\mathsf T} W \vec r$ is even for $W$ symmetric with even diagonal. -/
theorem two_dvd_dotProduct_mulVec_self {W : Matrix (Fin n) (Fin n) R} (hW : Wᵀ = W) (hd : ∀ i, 2 ∣ W i i)
    (r : Fin n → R) : 2 ∣ r ⬝ᵥ (W *ᵥ r) := by
  rw [← dvr_eval_ofMatrix W r]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs with hij
  · refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    simp only [dvr_ofMatrix, Algebra.algebraMap_self, RingHom.id_apply, Matrix.of_apply]
    split_ifs with h1 h2
    · rw [show W j i = W i j by simpa using congrFun (congrFun hW i) j, ← two_mul]
      exact dvd_mul_right _ _
    · subst h2; exact hd i
    · exact dvd_zero _
  · exact dvd_zero _

/-- **The level is a $\mathrm{GL}_n(R)$-invariant:** if $Q'(\vec x) = Q(U\vec x)$ with $\det U$ a unit and $\pi^k$ is a level of
$Q$, it is one of $Q'$ ($W' = U^{-1} W U^{-\mathsf T}$). -/
theorem IsLocalLevel.of_isGLEquiv {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') {π : R} {k : ℕ}
    (hL : IsLocalLevel Q π k) : IsLocalLevel Q' π k := by
  obtain ⟨U, hU, hQ⟩ := h
  obtain ⟨W, hW, hs, hd⟩ := hL
  have hH := hessian_eq_of_eval hQ
  refine ⟨U⁻¹ * W * U⁻¹ᵀ, ?_, ?_, fun i => ?_⟩
  · rw [hH]
    calc Uᵀ * Q.hessian * U * (U⁻¹ * W * U⁻¹ᵀ) = Uᵀ * (Q.hessian * W) * U⁻¹ᵀ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hU]
      _ = π ^ k • (Uᵀ * U⁻¹ᵀ) := by rw [hW, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = π ^ k • 1 := by
          rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.transpose_one]
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  · have : (U⁻¹ * W * U⁻¹ᵀ) i i = (fun j => U⁻¹ i j) ⬝ᵥ (W *ᵥ fun j => U⁻¹ i j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    rw [this]; exact two_dvd_dotProduct_mulVec_self hs hd _

theorem IsGLEquiv.isLocalLevel_iff {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) (k : ℕ) :
    IsLocalLevel Q π k ↔ IsLocalLevel Q' π k :=
  ⟨fun hL => hL.of_isGLEquiv h, fun hL => hL.of_isGLEquiv h.symm⟩

/-- $\pi \nmid N$ forces $\det H$ to be a unit. -/
theorem isUnit_det_of_isLocalLevel_zero {Q : QuadForm R n} {π : R} (h : IsLocalLevel Q π 0) :
    IsUnit Q.hessian.det := by
  obtain ⟨W, hW, -⟩ := h
  rw [pow_zero, one_smul] at hW
  exact IsUnit.of_mul_eq_one W.det (by rw [← Matrix.det_mul, hW, Matrix.det_one])

/-- **At $\pi \nmid 2$: $\pi \nmid N \iff \pi \nmid \det H$** (half of Lemma 2.2, non-dyadic). -/
theorem isLocalLevel_zero_iff {Q : QuadForm R n} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    IsLocalLevel Q π 0 ↔ ¬ π ∣ Q.hessian.det := by
  refine ⟨fun h => dvr_not_dvd_of_isUnit hπ (isUnit_det_of_isLocalLevel_zero h), fun h => ?_⟩
  have hu := dvr_isUnit_of_not_dvd hπ h
  have h2u := dvr_isUnit_of_not_dvd hπ h2
  refine ⟨(hu.unit⁻¹ : Rˣ).val • Q.hessian.adjugate, ?_, ?_, fun i => h2u.dvd⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_zero]
    rw [IsUnit.val_inv_mul]
  · rw [transpose_smul, adjugate_transpose, hessian_transpose]

end Level

/-! ### (2.4), (2.5) and Lemma 2.2 -/

section Blocks

theorem levelExp_eq_of_isGLEquiv {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) :
    levelExp Q π = levelExp Q' π := by
  classical
  have hiff := h.isLocalLevel_iff π
  have hex : (∃ k, IsLocalLevel Q π k) ↔ ∃ k, IsLocalLevel Q' π k := exists_congr hiff
  unfold levelExp
  by_cases h1 : ∃ k, IsLocalLevel Q π k
  · rw [dif_pos h1, dif_pos (hex.1 h1)]
    exact le_antisymm (Nat.find_min' h1 ((hiff _).2 (Nat.find_spec (hex.1 h1))))
      (Nat.find_min' (hex.1 h1) ((hiff _).1 (Nat.find_spec h1)))
  · rw [dif_neg h1, dif_neg (fun h' => h1 (hex.2 h'))]

/-- A normal form without 2-dimensional blocks is diagonal. -/
theorem eq_diag_of_isJordanForm_empty {Q : QuadForm R n} {π : R} {ν : Fin n → ℕ}
    (hJ : IsJordanForm Q π ∅ ν) : Q = QuadForm.diag fun i => Q.coeff i i := by
  ext i j
  simp only [QuadForm.diag, Matrix.diagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg h.ne]; exact hJ.2.2.2.1 i j h (by simp)
  · simp
  · rw [if_neg h.ne']; exact Q.upper (show id j < id i from h)

theorem hessian_diag (a : Fin n → R) : (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  unfold QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, two_mul]

/-- **The level of a diagonal form** (1-dimensional blocks, every $\pi$): $\pi^k$ is a level of $\langle a_i\rangle$ iff
$4a_i \mid \pi^k$ for all $i$ ($W = \mathrm{diag}(\pi^k/2a_i)$ must have even diagonal). -/
theorem isLocalLevel_diag_iff (a : Fin n → R) (π : R) (k : ℕ) :
    IsLocalLevel (QuadForm.diag a) π k ↔ ∀ i, 4 * a i ∣ π ^ k := by
  constructor
  · rintro ⟨W, hW, -, hd⟩ i
    have h := congrFun (congrFun hW i) i
    rw [hessian_diag, Matrix.diagonal_mul] at h
    obtain ⟨t, ht⟩ := hd i
    refine ⟨t, ?_⟩
    rw [ht] at h
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; ring
  · intro h
    choose t ht using h
    refine ⟨Matrix.diagonal fun i => 2 * t i, ?_, Matrix.diagonal_transpose _, fun i => ?_⟩
    · rw [hessian_diag, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
      congr 1; funext i; rw [ht i]; ring
    · rw [Matrix.diagonal_apply_eq]; exact dvd_mul_right _ _

/-- **(2.5) for 1-dimensional blocks** (Hanke 2004, p. 356, as printed): if $2 = \pi^e v$ ($v$ a unit) and
$a_i = \pi^{\nu_i} u_i$ ($u_i$ units), then $\pi^k$ is a level of $\langle a_i \rangle$ iff $\nu_i + 2e \le k$ for all $i$,
i.e. $\lambda''_i = \nu_i + 2\,\mathrm{ord}_\pi 2$. -/
@[kb "hanke2004" "(2.5), p. 356 (dim 1)"]
theorem isLocalLevel_diag_iff_exp {π : R} (hπ : Irreducible π) {e : ℕ} {v : R} (hv : IsUnit v)
    (he : 2 = π ^ e * v) (a : Fin n → R) (ν : Fin n → ℕ) (hν : ∀ i, ∃ u, a i = π ^ ν i * u ∧ IsUnit u)
    (k : ℕ) : IsLocalLevel (QuadForm.diag a) π k ↔ ∀ i, ν i + 2 * e ≤ k := by
  rw [isLocalLevel_diag_iff]
  refine forall_congr' fun i => ?_
  obtain ⟨u, hu, hu1⟩ := hν i
  rw [show 4 * a i = π ^ (ν i + 2 * e) * (v ^ 2 * u) by rw [hu, show (4 : R) = 2 * 2 by norm_num, he]; ring,
    (hv.pow 2 |>.mul hu1).mul_right_dvd, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]

/-- **(2.4) for 1-dimensional blocks** (Hanke 2004, p. 356, as printed): with $2 = \pi^e v$ and $a_i = \pi^{\nu_i}u_i$,
$\det H = \pi^{\sum_i (\nu_i + e)} \cdot$ unit, i.e. $\lambda'_i = \nu_i + \mathrm{ord}_\pi 2$. -/
@[kb "hanke2004" "(2.4), p. 356 (dim 1)"]
theorem det_hessian_diag_exp {π : R} {e : ℕ} {v : R} (hv : IsUnit v) (he : 2 = π ^ e * v)
    (a : Fin n → R) (ν : Fin n → ℕ) (hν : ∀ i, ∃ u, a i = π ^ ν i * u ∧ IsUnit u) :
    ∃ w : R, IsUnit w ∧ (QuadForm.diag a).hessian.det = π ^ (∑ i, (ν i + e)) * w := by
  choose u hu hu1 using hν
  refine ⟨∏ i, (v * u i), IsUnit.prod_univ_iff.2 fun i => hv.mul (hu1 i), ?_⟩
  rw [hessian_diag, Matrix.det_diagonal, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hu i, he, pow_add]; ring

/-- **(2.5) for diagonal forms:** $\mathrm{ord}_\pi N = \max_i (\nu_i + 2\,\mathrm{ord}_\pi 2)$. -/
@[kb "hanke2004" "(2.5), p. 356 (dim 1)"]
theorem levelExp_diag {π : R} (hπ : Irreducible π) {e : ℕ} {v : R} (hv : IsUnit v) (he : 2 = π ^ e * v)
    (a : Fin n → R) (ν : Fin n → ℕ) (hν : ∀ i, ∃ u, a i = π ^ ν i * u ∧ IsUnit u) :
    levelExp (QuadForm.diag a) π = Finset.univ.sup fun i => ν i + 2 * e := by
  have hiff := isLocalLevel_diag_iff_exp hπ hv he a ν hν
  have hex : ∃ k, IsLocalLevel (QuadForm.diag a) π k :=
    ⟨_, (hiff _).2 fun i => Finset.le_sup (f := fun i => ν i + 2 * e) (Finset.mem_univ i)⟩
  refine le_antisymm ((isLocalLevel_iff_levelExp_le hex _).1 ((hiff _).2 fun i =>
    Finset.le_sup (f := fun i => ν i + 2 * e) (Finset.mem_univ i))) ?_
  exact Finset.sup_le fun i _ => (hiff _).1 ((isLocalLevel_iff_levelExp_le hex _).2 le_rfl) i

/-- $\pi \mid \pi^\nu u \iff \nu \ge 1$ for a unit $u$. -/
theorem dvd_pow_mul_unit_iff {π u : R} (hπ : Irreducible π) (hu : IsUnit u) (ν : ℕ) :
    π ∣ π ^ ν * u ↔ 1 ≤ ν := by
  rw [hu.dvd_mul_right]
  constructor
  · intro h
    by_contra h0
    obtain rfl : ν = 0 := by omega
    exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using h))
  · intro h; exact dvd_pow_self π (by omega)

/-- **Lemma 2.2 at a non-dyadic prime** (Hanke 2004, Lemma 2.2, p. 356, $\mathfrak p \nmid 2$): for $Q$ $\mathrm{GL}_n(R)$-equivalent to
a normal form $Q' = \langle \pi^{\nu_i} u_i \rangle$, $\pi \mid N \iff \pi \mid D_{2Q} = \det H \iff \nu_i \ge 1$ for some $i$. -/
@[kb "hanke2004" "Lemma 2.2, p. 356 (p ∤ 2)"]
theorem lemma_2_2_nondyadic (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    {Q' : QuadForm R n} {ν : Fin n → ℕ} (hJ : IsJordanForm Q' π ∅ ν) (hE : IsGLEquiv Q Q') :
    (¬ IsLocalLevel Q π 0 ↔ π ∣ Q.hessian.det) ∧ (π ∣ Q.hessian.det ↔ ∃ i, 1 ≤ ν i) := by
  refine ⟨by rw [isLocalLevel_zero_iff hπ h2, not_not], ?_⟩
  obtain ⟨u, hu, hdu⟩ := hE.det_hessian
  have hdiag := eq_diag_of_isJordanForm_empty hJ
  rw [hdiag, det_hessian_diag] at hdu
  have hp := hπ.prime
  have h1 : π ∣ Q.hessian.det ↔ π ∣ ∏ i, Q'.coeff i i := by
    constructor
    · intro h
      have : π ∣ 2 ^ n * ∏ i, Q'.coeff i i := hdu ▸ h.mul_left _
      rcases hp.dvd_or_dvd this with h' | h'
      · exact absurd (hp.dvd_of_dvd_pow h') h2
      · exact h'
    · intro h
      have : π ∣ u ^ 2 * Q.hessian.det := hdu ▸ h.mul_left _
      rcases hp.dvd_or_dvd this with h' | h'
      · exact absurd (hp.dvd_of_dvd_pow h') (dvr_not_dvd_of_isUnit hπ hu)
      · exact h'
  rw [h1, hp.dvd_finset_prod_iff]
  refine ⟨fun ⟨i, _, hi⟩ => ⟨i, ?_⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ _, ?_⟩⟩
  · obtain ⟨w, hw, hw1⟩ := hJ.2.2.2.2.2 i (by simp [IsPaired])
    rwa [hw, dvd_pow_mul_unit_iff hπ hw1] at hi
  · obtain ⟨w, hw, hw1⟩ := hJ.2.2.2.2.2 i (by simp [IsPaired])
    rwa [hw, dvd_pow_mul_unit_iff hπ hw1]

/-- **(2.4) and (2.5) at a non-dyadic prime** (Hanke 2004, p. 356, as printed with $\mathrm{ord}_\pi 2 = 0$): for $Q$
equivalent to $\langle \pi^{\nu_i}u_i \rangle$, $\det H = \pi^{\sum_i \nu_i}\cdot$ unit and $\mathrm{ord}_\pi N = \max_i \nu_i$. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (p ∤ 2)"]
theorem eq_2_4_2_5_nondyadic (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    {Q' : QuadForm R n} {ν : Fin n → ℕ} (hJ : IsJordanForm Q' π ∅ ν) (hE : IsGLEquiv Q Q') :
    (∃ w : R, IsUnit w ∧ Q.hessian.det = π ^ (∑ i, ν i) * w) ∧
      levelExp Q π = Finset.univ.sup ν := by
  have h2u := dvr_isUnit_of_not_dvd hπ h2
  have he : (2 : R) = π ^ 0 * 2 := by ring
  have hν : ∀ i, ∃ u, Q'.coeff i i = π ^ ν i * u ∧ IsUnit u := fun i =>
    hJ.2.2.2.2.2 i (by simp [IsPaired])
  have hdiag := eq_diag_of_isJordanForm_empty hJ
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw, hdw⟩ := det_hessian_diag_exp h2u he _ ν hν
    obtain ⟨u, hu, hdu⟩ := hE.det_hessian
    rw [hdiag, hdw] at hdu
    refine ⟨w * ((hu.unit⁻¹ : Rˣ) : R) ^ 2, hw.mul ((Units.isUnit _).pow 2), ?_⟩
    have : Q.hessian.det = ((hu.unit⁻¹ : Rˣ) : R) ^ 2 * (u ^ 2 * Q.hessian.det) := by
      rw [← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
    rw [this, ← hdu]; simp only [add_zero]; ring
  · rw [levelExp_eq_of_isGLEquiv hE, hdiag, levelExp_diag hπ h2u he _ ν hν]
    simp

/-- **The binary form** $ax^2 + bxy + cy^2$ over $R$ (coefficient matrix $\begin{pmatrix} a & b \\ 0 & c\end{pmatrix}$). -/
def binForm (a b c : R) : QuadForm R 2 :=
  ⟨!![a, b; 0, c], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

theorem hessian_binForm (a b c : R) : (binForm a b c).hessian = !![2 * a, b; b, 2 * c] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, binForm] <;> ring

theorem det_hessian_binForm (a b c : R) : (binForm a b c).hessian.det = 4 * a * c - b ^ 2 := by
  rw [hessian_binForm, Matrix.det_fin_two_of]; ring

/-- **The level of a binary block** (Hanke 2004, (2.5), p. 356, dimension 2, at every $\pi$): with
$d = 4ac - b^2 = \det H \ne 0$ and $2 \ne 0$, $\pi^k$ is a level of $ax^2 + bxy + cy^2$ iff $d \mid \pi^k a$, $d \mid \pi^k b$ and
$d \mid \pi^k c$ (from $\pi^k H^{-1} = \frac{\pi^k}{d}\begin{pmatrix} 2c & -b \\ -b & 2a\end{pmatrix}$, whose diagonal must be even). -/
@[kb "hanke2004" "(2.5), p. 356 (dim 2)"]
theorem isLocalLevel_binForm_iff (a b c : R) (h20 : (2 : R) ≠ 0) (hd : 4 * a * c - b ^ 2 ≠ 0) (π : R)
    (k : ℕ) :
    IsLocalLevel (binForm a b c) π k ↔
      (4 * a * c - b ^ 2 ∣ π ^ k * a ∧ 4 * a * c - b ^ 2 ∣ π ^ k * b ∧ 4 * a * c - b ^ 2 ∣ π ^ k * c) := by
  constructor
  · rintro ⟨W, hW, hs, hd2⟩
    have e : ∀ i j, (!![2 * a, b; b, 2 * c] * W) i j = (π ^ k • (1 : Matrix (Fin 2) (Fin 2) R)) i j := by
      intro i j; rw [← hessian_binForm, hW]
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have hsym : W 1 0 = W 0 1 := by simpa using congrFun (congrFun hs 0) 1
    obtain ⟨s, hs0⟩ := hd2 0
    obtain ⟨t, ht1⟩ := hd2 1
    rw [hsym] at e00 e10
    refine ⟨⟨t, ?_⟩, ⟨-W 0 1, ?_⟩, ⟨s, ?_⟩⟩
    · refine mul_left_cancel₀ h20 ?_
      linear_combination (-(2 * a)) * e11 + b * e01 + (4 * a * c - b ^ 2) * ht1
    · linear_combination (2 * c) * e01 - b * e11
    · refine mul_left_cancel₀ h20 ?_
      linear_combination (-(2 * c)) * e00 + b * e10 + (4 * a * c - b ^ 2) * hs0
  · rintro ⟨⟨t, ht⟩, ⟨v, hv⟩, ⟨s, hs⟩⟩
    refine ⟨!![2 * s, -v; -v, 2 * t], ?_, ?_, fun i => ?_⟩
    · rw [hessian_binForm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        refine mul_left_cancel₀ hd ?_
      · linear_combination -(4 * a) * hs + b * hv
      · linear_combination -(2 * b) * ht + 2 * a * hv
      · linear_combination -(2 * b) * hs + 2 * c * hv
      · linear_combination -(4 * c) * ht + b * hv
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> simp

/-- **(2.4) and (2.5) for a binary block in Hanke's normal form** (Hanke 2004, Lemma 2.1 and p. 356, at $\pi \mid 2$): for
$Q_j = \pi^\nu(\alpha x^2 + \beta xy + \gamma y^2)$ with $\beta$ a unit, $\det H = \pi^{2\nu}\delta$ with $\delta$ a unit, and $\pi^k$ is a
level iff $\nu \le k$. So $\lambda''_j = \nu_j$ as printed in (2.5), but the contribution to $\mathrm{ord}_\pi D_{2Q}$ is
$\lambda'_j = 2\nu_j$, not $\nu_j$.

*Erratum candidate:* (2.4) prints $\lambda'_j = \nu_j$ for $\dim Q_j = 2$; it should be
$2\nu_j$ (e.g. $2xy$ over $\mathbb Z_2$: $\nu = 1$, $\det H = -4$; `det_hessian_binForm_erratum`). Lemma 2.2 is unaffected. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (dim 2, corrected)"]
theorem binForm_normal {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (ν : ℕ)
    (α β γ : R) (hβ : IsUnit β) :
    (∃ δ : R, IsUnit δ ∧ (binForm (π ^ ν * α) (π ^ ν * β) (π ^ ν * γ)).hessian.det = π ^ (2 * ν) * δ) ∧
      ∀ k, IsLocalLevel (binForm (π ^ ν * α) (π ^ ν * β) (π ^ ν * γ)) π k ↔ ν ≤ k := by
  set δ := 4 * α * γ - β ^ 2
  have hδ : IsUnit δ := by
    refine dvr_isUnit_of_not_dvd hπ fun h => dvr_not_dvd_of_isUnit hπ (hβ.pow 2) ?_
    have h4 : π ∣ 4 * α * γ := by
      rw [show (4 : R) * α * γ = 2 * (2 * α * γ) by ring]; exact h2.mul_right _
    have := dvd_sub h4 h
    rwa [show 4 * α * γ - δ = β ^ 2 by ring] at this
  have hdet : (binForm (π ^ ν * α) (π ^ ν * β) (π ^ ν * γ)).hessian.det = π ^ (2 * ν) * δ := by
    rw [det_hessian_binForm]; ring
  refine ⟨⟨δ, hδ, hdet⟩, fun k => ?_⟩
  have hd0 : 4 * (π ^ ν * α) * (π ^ ν * γ) - (π ^ ν * β) ^ 2 ≠ 0 := by
    rw [← det_hessian_binForm, hdet]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hδ.ne_zero
  rw [isLocalLevel_binForm_iff _ _ _ h20 hd0]
  rw [← det_hessian_binForm, hdet, hδ.mul_right_dvd, hδ.mul_right_dvd, hδ.mul_right_dvd]
  constructor
  · rintro ⟨-, hb, -⟩
    rw [← mul_assoc, ← pow_add, hβ.dvd_mul_right, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at hb
    omega
  · intro hk
    have : π ^ (2 * ν) ∣ π ^ k * π ^ ν := by
      rw [← pow_add]; exact pow_dvd_pow π (by omega)
    exact ⟨this.trans (by rw [← mul_assoc]; exact dvd_mul_right _ _),
      this.trans (by rw [← mul_assoc]; exact dvd_mul_right _ _),
      this.trans (by rw [← mul_assoc]; exact dvd_mul_right _ _)⟩

/-- **The (2.4) erratum, explicitly:** $\pi^\nu x_0x_1$ (Hanke's normal form at $\pi \mid 2$, one 2-dimensional block with
$\nu_j = \nu$) has $\det H = -\pi^{2\nu}$, so $\mathrm{ord}_\pi D_{2Q} = 2\nu$, while (2.4) as printed gives $\nu$. For
$R = \mathbb Z_2$, $\nu = 1$: $Q = 2x_0x_1$, $\det H = -4$. -/
theorem det_hessian_binForm_erratum (π : R) (h2 : π ∣ 2) (ν : ℕ) :
    IsJordanForm (binForm 0 (π ^ ν) 0) π {((0 : Fin 2), (1 : Fin 2))} (fun _ => ν) ∧
      (binForm 0 (π ^ ν) 0).hessian.det = -π ^ (2 * ν) := by
  refine ⟨⟨fun _ => h2, by simp, by simp, ?_, ?_, ?_⟩, by rw [det_hessian_binForm]; ring⟩
  · intro i j hij hP
    fin_cases i <;> fin_cases j <;> simp_all
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨rfl, ⟨1, by simp [binForm], isUnit_one⟩, by simp [binForm], by simp [binForm]⟩
  · intro i hi
    exact absurd (show IsPaired _ i from ⟨(0, 1), by simp, by fin_cases i <;> simp⟩) hi

/-- **Lemma 2.2 and (2.5) fail as printed at ramified dyadic primes** (erratum candidate;
companion of the Lemma 2.1 erratum): if $\pi^2 \mid 2$ (e.g. $\mathbb Z_2[\sqrt 2]$, $\pi = \sqrt 2$), $Q = x^2 + \pi xy + y^2$ is
in the corrected normal form `IsJordanFormW` with one 2-dimensional block of norm exponent $w = 0$ (no
1-dimensional blocks, all $\nu_j = 0$), yet $\mathrm{ord}_\pi N = 2$: $\pi^k$ is a level iff $k \ge 2$. So
"$\mathfrak p \mid N \iff$ some $\nu_j \ge 1$ or ($\mathfrak p \mid 2$ and some $\dim Q_j = 1$)" and $\lambda''_j = \nu_j$ fail with
$\nu = w$; the correct statements use the scale exponent $\mu$ of the block ($\mu = 1$ here): for a block
$\pi^\mu$-modular Hessian $\begin{pmatrix} 2a & b \\ b & 2c\end{pmatrix}$, $b = \pi^\mu\beta$, the level is governed by $\mu$
and $v(a), v(c)$ (`isLocalLevel_binForm_iff`); dyadic $\pi \nmid N$ iff all blocks binary with $\mu = 0$
(`isLocalLevel_zero_iff_unimodular`). -/
@[kb "hanke2004" "Lemma 2.2, (2.5), p. 356 (ramified dyadic counterexample)"]
theorem lemma_2_2_ramified_counterexample {π : R} (hπ : Irreducible π) (h2 : π ^ 2 ∣ 2)
    (h20 : (2 : R) ≠ 0) :
    IsJordanFormW (binForm 1 π 1) π {((0 : Fin 2), (1 : Fin 2))} 0 ∧
      ∀ k, IsLocalLevel (binForm 1 π 1) π k ↔ 2 ≤ k := by
  obtain ⟨t, ht⟩ := h2
  have hπ2 : π ∣ 2 := ⟨π * t, by rw [ht]; ring⟩
  refine ⟨⟨fun _ => hπ2, by simp, by simp, ?_, ?_, ?_⟩, fun k => ?_⟩
  · intro i j hij hP
    fin_cases i <;> fin_cases j <;> simp_all
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    refine ⟨rfl, by simp [binForm], by simp [binForm], ?_, 1, 1, by simp [binForm], isUnit_one, by simp,
      ?_, ?_, ?_⟩
    · rintro ⟨h, -⟩
      exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa [binForm] using h))
    · simp [binForm, ht]
    · simp [binForm, ht]
    · simp [hπ2]
  · intro i hi
    exact absurd (show IsPaired _ i from ⟨(0, 1), by simp, by fin_cases i <;> simp⟩) hi
  · have hd : 4 * 1 * 1 - π ^ 2 = π ^ 2 * (π ^ 2 * t ^ 2 - 1) := by
      rw [show (4 : R) * 1 * 1 = 2 * 2 by norm_num, ht]; ring
    have hu : IsUnit (π ^ 2 * t ^ 2 - 1) := by
      refine dvr_isUnit_of_not_dvd hπ fun h => hπ.not_isUnit (isUnit_of_dvd_one ?_)
      have : π ∣ π ^ 2 * t ^ 2 := ⟨π * t ^ 2, by ring⟩
      have := dvd_sub this h
      rwa [show π ^ 2 * t ^ 2 - (π ^ 2 * t ^ 2 - 1) = 1 by ring] at this
    have hd0 : 4 * 1 * 1 - π ^ 2 ≠ 0 := by
      rw [hd]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hu.ne_zero
    rw [isLocalLevel_binForm_iff _ _ _ h20 hd0, hd, hu.mul_right_dvd, mul_one, ← pow_succ, hu.mul_right_dvd,
      pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega, h⟩⟩

end Blocks

/-! ### Dyadic $\pi \nmid N$: no 1-dimensional blocks, unit cross terms, and `pairSumForm` -/

section Dyadic

/-- **Lemma 2.1, corrected, with the change of variables kept:** as `exists_jordanFormW`, with $Q'$
$\mathrm{GL}_n(R)$-equivalent to $Q$. -/
theorem exists_jordanFormW_isGLEquiv (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      IsJordanFormW Q' π P w ∧ (¬ π ∣ 2 → P = ∅) ∧ IsGLEquiv Q Q' := by
  classical
  have hJ0 : DvrJInvGen π (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P, ν, hV, hJ⟩ := dvr_jinvGen_complete_aux hπ _ Q.coeff ∅ ∅ (fun _ => 0) rfl hQ hJ0
  set Q' := dvr_ofMatrix (Vᵀ * Q.coeff * V) with hQ'
  have hH : Q'.hessian = Vᵀ * (Q.coeff + Q.coeffᵀ) * V := by
    rw [hQ', dvr_hessian_ofMatrix]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have heval : ∀ x, Q'.eval x = Q.eval (V *ᵥ x) := by
    intro x
    rw [hQ', dvr_eval_ofMatrix]
    show _ = Q.evalIn R (V *ᵥ x)
    rw [QuadForm.evalIn_eq_dotProduct]
    simp only [Algebra.algebraMap_self, Matrix.map_id]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    rfl
  have hJG := dvr_isJordanFormGen_of_jinvGen h20 Q' P ν (hH ▸ hJ)
  obtain ⟨w, hw, -⟩ := hJG.toW hπ
  refine ⟨Q', P, w, hw, fun h => ?_, V, hV, heval⟩
  by_contra hP
  exact h (hJ.1 (Finset.nonempty_iff_ne_empty.2 hP))

/-- Off the blocks the Hessian of a normal form vanishes. -/
theorem IsJordanFormW.hessian_eq_zero {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)}
    {w : Fin n → ℕ} (hJ : IsJordanFormW Q π P w) {i j : Fin n} (hij : i ≠ j) (h1 : (i, j) ∉ P)
    (h2 : (j, i) ∉ P) : Q.hessian i j = 0 := by
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [hJ.2.2.2.1 i j h h1, Q.upper (show id i < id j from h), add_zero]
  · rw [hJ.2.2.2.1 j i h h2, Q.upper (show id j < id i from h), zero_add]

/-- **Dyadic $\pi \nmid N$ in normal form** (Hanke 2004, Lemma 2.2, corrected, at $\pi \mid 2$): if
$Q$ is in the corrected normal form `IsJordanFormW Q π P w` at $\pi \mid 2$ and $\pi^0$ is a level ($\pi \nmid N$), then every
coordinate lies in a 2-dimensional block, every block's cross coefficient $b$ is a unit (scale exponent $\mu = 0$), and
all norm exponents $w$ vanish. *Proof:* $(HW)_{ii} = 1$; for an unpaired $i$ this reads $2c_{ii}W_{ii} = 1$, and for a pair
$(i, j)$ it reads $2c_{ii}W_{ii} + c_{ij}W_{ji} = 1$; $\pi \mid 2$. -/
@[kb "hanke2004" "Lemma 2.2, p. 356 (dyadic p ∤ N, corrected)"]
theorem isLocalLevel_zero_jordanW {Q : QuadForm R n} {π : R} (hπ : Irreducible π) (h2 : π ∣ 2)
    {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ} (hJ : IsJordanFormW Q π P w) (hL : IsLocalLevel Q π 0) :
    (∀ i, IsPaired P i) ∧ (∀ e ∈ P, IsUnit (Q.coeff e.1 e.2)) ∧ ∀ i, w i = 0 := by
  classical
  obtain ⟨W, hW, -, -⟩ := hL
  rw [pow_zero, one_smul] at hW
  have hrow : ∀ i, ∑ l, Q.hessian i l * W l i = 1 := by
    intro i; have := congrFun (congrFun hW i) i; simpa [Matrix.mul_apply] using this
  have hdiag : ∀ i, Q.hessian i i = 2 * Q.coeff i i := by
    intro i; simp [QuadForm.hessian]; ring
  have hnot1 : ¬ π ∣ 1 := fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
  have hpaired : ∀ i, IsPaired P i := by
    intro i
    by_contra hi
    have h := hrow i
    rw [Fintype.sum_eq_single i fun l hl => by
      rw [hJ.hessian_eq_zero (Ne.symm hl) (fun h => hi ⟨_, h, Or.inl rfl⟩)
        (fun h => hi ⟨_, h, Or.inr rfl⟩), zero_mul], hdiag] at h
    exact hnot1 (h ▸ (h2.mul_right _).mul_right _)
  have hunit : ∀ e ∈ P, IsUnit (Q.coeff e.1 e.2) := by
    intro e he
    have hlt := hJ.2.1 e he
    have h := hrow e.1
    rw [Fintype.sum_eq_add e.1 e.2 hlt.ne fun l ⟨hl1, hl2⟩ => ?_, hdiag] at h
    · refine dvr_isUnit_of_not_dvd hπ fun hb => hnot1 ?_
      have : Q.hessian e.1 e.2 = Q.coeff e.1 e.2 := by
        simp [QuadForm.hessian, Q.upper (show id e.1 < id e.2 from hlt)]
      rw [this] at h
      rw [← h]
      exact dvd_add ((h2.mul_right _).mul_right _) (hb.mul_right _)
    · have hd := hJ.2.2.1
      rw [hJ.hessian_eq_zero (Ne.symm hl1) (fun h' => ?_) (fun h' => ?_), zero_mul]
      · have hne : (e.1, l) ≠ e := fun h'' => hl2 (by rw [← h'']) 
        exact (hd e he _ h' (Ne.symm hne)).1 rfl
      · have hne : (l, e.1) ≠ e := fun h'' => hl1 (by rw [← h''])
        exact (hd e he _ h' (Ne.symm hne)).2.1 rfl
  refine ⟨hpaired, hunit, fun i => ?_⟩
  obtain ⟨e, he, hi⟩ := hpaired i
  obtain ⟨hw, -, -, -, μ, β, hb, hβ, hle, -⟩ := hJ.2.2.2.2.1 e he
  have hμ : μ = 0 := by
    by_contra hμ
    refine dvr_not_dvd_of_isUnit hπ (hunit e he) ?_
    rw [hb]; exact (dvd_pow_self π hμ).mul_right _
  rcases hi with rfl | rfl
  · omega
  · rw [← hw]; omega

/-- **Enumerating the blocks:** if the disjoint pairs $P$ (with $e_1 < e_2$) cover every coordinate, then
$(i, j) \mapsto$ ($j$-th entry of the $i$-th pair) is a bijection $\mathrm{Fin}\,|P| \times \mathrm{Fin}\,2 \to \mathrm{Fin}\,n$. -/
theorem exists_pairEquiv {P : Finset (Fin n × Fin n)} (h1 : ∀ e ∈ P, e.1 < e.2)
    (h3 : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hp : ∀ i, IsPaired P i) :
    ∃ σ : Fin P.card × Fin 2 ≃ Fin n, ∃ p : Fin P.card ≃ P,
      ∀ i, σ (i, 0) = (p i).1.1 ∧ σ (i, 1) = (p i).1.2 := by
  classical
  set p : Fin P.card ≃ P := P.equivFin.symm
  let g : Fin P.card × Fin 2 → Fin n := fun ij => if ij.2 = 0 then (p ij.1).1.1 else (p ij.1).1.2
  have hg0 : ∀ i, g (i, 0) = (p i).1.1 := fun i => by simp [g]
  have hg1 : ∀ i, g (i, 1) = (p i).1.2 := fun i => by simp [g]
  have hinj : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have key : ∀ (i i' : Fin P.card), (p i).1 ≠ (p i').1 → ∀ j j' : Fin 2, g (i, j) ≠ g (i', j') := by
      intro i i' hne j j'
      have hd := h3 _ (p i).2 _ (p i').2 hne
      fin_cases j <;> fin_cases j' <;> simp [hg0, hg1] at * <;> tauto
    by_cases hii : i = i'
    · subst hii
      have hlt := h1 _ (p i).2
      fin_cases j <;> fin_cases j' <;> simp [g] at h ⊢ <;> [exact absurd h hlt.ne; exact absurd h hlt.ne']
    · exact absurd h (key i i' (fun h' => hii (p.injective (Subtype.ext h'))) j j')
  have hsurj : Function.Surjective g := by
    intro s
    obtain ⟨e, he, hs⟩ := hp s
    obtain ⟨i, hi⟩ := p.surjective ⟨e, he⟩
    rcases hs with hs | hs
    · exact ⟨(i, 0), by rw [hg0, hi, ← hs]⟩
    · exact ⟨(i, 1), by rw [hg1, hi, ← hs]⟩
  exact ⟨Equiv.ofBijective g ⟨hinj, hsurj⟩, p, fun i => ⟨hg0 i, hg1 i⟩⟩

/-- **A form all of whose coordinates lie in 2-dimensional blocks is a `pairSumForm` after renumbering:** for
`IsJordanFormW Q π P w` with every coordinate paired, there are $r$, $A : \mathrm{Fin}\,r \to R^3$ (the blocks) and a
bijection $\varepsilon : \mathrm{Fin}(2r) \to \mathrm{Fin}\,n$ with $Q(\vec x) = \texttt{pairSumForm}\,A\,(\vec x \circ \varepsilon)$, each
$b_i$ the cross coefficient of a pair of $P$. -/
theorem exists_eval_eq_pairSumForm {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}
    (hJ : IsJordanFormW Q π P w) (hp : ∀ i, IsPaired P i) :
    ∃ (r : ℕ) (A : Fin r → R × R × R) (ε : Fin (r * 2) ≃ Fin n),
      (∀ i, ∃ e ∈ P, (A i).2.1 = Q.coeff e.1 e.2) ∧ ∀ x : Fin n → R, Q.eval x = (pairSumForm A).eval (x ∘ ε) := by
  classical
  obtain ⟨σ, p, hσ⟩ := exists_pairEquiv hJ.2.1 hJ.2.2.1 hp
  let A : Fin P.card → R × R × R := fun i =>
    (Q.coeff (p i).1.1 (p i).1.1, Q.coeff (p i).1.1 (p i).1.2, Q.coeff (p i).1.2 (p i).1.2)
  let ε : Fin (P.card * 2) ≃ Fin n := finProdFinEquiv.symm.trans σ
  have hε : ∀ i j, ε (pidx i j) = σ (i, j) := fun i j => by simp [ε, pidx]
  refine ⟨P.card, A, ε, fun i => ⟨(p i).1, (p i).2, rfl⟩, fun x => ?_⟩
  -- the left side: diagonal terms plus the cross terms on the pairs
  have hL : Q.eval x = ∑ s, Q.coeff s s * x s ^ 2 + ∑ e ∈ P, Q.coeff e.1 e.2 * x e.1 * x e.2 := by
    show Q.evalIn R x = _
    simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
    have hsplit : ∀ s t : Fin n, (if s ≤ t then Q.coeff s t * x s * x t else 0) =
        (if s = t then Q.coeff s t * x s * x t else 0) + (if s < t then Q.coeff s t * x s * x t else 0) := by
      intro s t
      rcases lt_trichotomy s t with h | rfl | h
      · simp [h, h.le, h.ne]
      · simp
      · simp [h.ne', not_le.2 h, not_lt.2 h.le]
    simp only [hsplit, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_ite_eq]; simp; ring
    · rw [← Finset.sum_product' (f := fun s t => if s < t then Q.coeff s t * x s * x t else 0)]
      rw [← Finset.sum_filter]
      symm
      refine Finset.sum_subset (fun e he => by simp [hJ.2.1 e he]) fun e he heP => ?_
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at he
      rw [hJ.2.2.2.1 e.1 e.2 he heP]; ring
  rw [hL]
  show _ = (pairSumForm A).evalIn R (x ∘ ε)
  rw [evalIn_pairSumForm]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Function.comp, hε]
  rw [← σ.sum_comp, Fintype.sum_prod_type, ← Finset.sum_coe_sort P, ← p.sum_comp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, (hσ i).1, (hσ i).2]
  simp only [A]; ring

/-- **Permuting coordinates is a $\mathrm{GL}_n(R)$-equivalence:** $Q'(\vec x) = Q(\vec x \circ \varepsilon)$ for a permutation
$\varepsilon$. -/
theorem isGLEquiv_of_perm {Q Q' : QuadForm R n} (ε : Equiv.Perm (Fin n))
    (h : ∀ x : Fin n → R, Q'.eval x = Q.eval (x ∘ ε)) : IsGLEquiv Q Q' := by
  refine ⟨(1 : Matrix (Fin n) (Fin n) R).submatrix ε id, ?_, fun x => ?_⟩
  · rw [Matrix.det_permute, Matrix.det_one, mul_one]
    exact (Units.isUnit _).map (Int.castRingHom R) |>.map (RingHom.id R)
  · rw [h]; congr 1; funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- **Dyadic $\pi \nmid N$ ⇒ `pairSumForm`** (O'Meara §93 is not needed): if $\pi \mid 2$, $2 \ne 0$ and
$\pi \nmid N$, then $n = 2r$ and $Q$ is $\mathrm{GL}_n(R)$-equivalent to $\bigoplus_{i<r}(a_ix^2 + b_ixy + c_iy^2)$ with every $b_i$
a unit. *Proof:* the corrected normal form (`exists_jordanFormW_isGLEquiv`) has no 1-dimensional blocks and unit cross
terms (`isLocalLevel_zero_jordanW`, the level being invariant), and renumbering the coordinates is a permutation. -/
@[kb "hanke2004" "Lemma 2.1, Lemma 2.2, p. 355–356 (dyadic p ∤ N)"]
theorem exists_pairSum_of_isLocalLevel_zero (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2)
    (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) :
    ∃ (r : ℕ) (A : Fin r → R × R × R) (h : r * 2 = n), (∀ i, ¬ π ∣ (A i).2.1) ∧
      IsGLEquiv Q (h ▸ pairSumForm A) := by
  have hQ : Q.Nondegenerate := (isUnit_det_of_isLocalLevel_zero hL).ne_zero
  obtain ⟨Q', P, w, hJ, -, hE⟩ := exists_jordanFormW_isGLEquiv Q hQ π hπ h20
  obtain ⟨hp, hu, -⟩ := isLocalLevel_zero_jordanW hπ h2 hJ ((hE.isLocalLevel_iff π 0).1 hL)
  obtain ⟨r, A, ε, hA, hev⟩ := exists_eval_eq_pairSumForm hJ hp
  have hn : r * 2 = n := by simpa using Fintype.card_congr ε
  subst hn
  refine ⟨r, A, rfl, fun i => ?_, hE.trans (isGLEquiv_of_perm ε hev).symm⟩
  obtain ⟨e, he, hb⟩ := hA i
  rw [hb]; exact dvr_not_dvd_of_isUnit hπ (hu e he)

/-- **An even unimodular `pairSumForm` has $\pi \nmid N$** ($\pi \mid 2$, all $b_i$ units): $H$ is block diagonal with blocks
$B_i = \begin{pmatrix} 2a_i & b_i \\ b_i & 2c_i\end{pmatrix}$ of unit determinant $\delta_i = 4a_ic_i - b_i^2$, and
$B_i^{-1} = \delta_i^{-1}\begin{pmatrix} 2c_i & -b_i \\ -b_i & 2a_i\end{pmatrix}$ has even diagonal. -/
theorem isLocalLevel_zero_pairSumForm {r : ℕ} (A : Fin r → R × R × R) {π : R} (hπ : Irreducible π)
    (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) : IsLocalLevel (pairSumForm A) π 0 := by
  classical
  set e : Fin 2 × Fin r ≃ Fin (r * 2) := (Equiv.prodComm _ _).trans finProdFinEquiv
  set B : Fin r → Matrix (Fin 2) (Fin 2) R := fun i => !![2 * (A i).1, (A i).2.1; (A i).2.1, 2 * (A i).2.2]
  have hM : (pairSumForm A).hessian.submatrix e e = Matrix.blockDiagonal B := by
    ext ⟨j, i⟩ ⟨j', i'⟩
    simp only [Matrix.submatrix_apply, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.blockDiagonal_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, B]
    rw [show finProdFinEquiv (i, j) = pidx i j from rfl, show finProdFinEquiv (i', j') = pidx i' j' from rfl,
      pairSumForm_coeff, pairSumForm_coeff]
    by_cases hii : i = i'
    · subst hii
      fin_cases j <;> fin_cases j' <;> simp <;> ring
    · simp [hii, Ne.symm hii]
  have hδ : ∀ i, IsUnit (4 * (A i).1 * (A i).2.2 - (A i).2.1 ^ 2) := by
    intro i
    refine dvr_isUnit_of_not_dvd hπ fun h => hb i (hπ.prime.dvd_of_dvd_pow (n := 2) ?_)
    have h4 : π ∣ 4 * (A i).1 * (A i).2.2 := by
      rw [show (4 : R) * (A i).1 * (A i).2.2 = 2 * (2 * (A i).1 * (A i).2.2) by ring]; exact h2.mul_right _
    have := dvd_sub h4 h
    rwa [show 4 * (A i).1 * (A i).2.2 - (4 * (A i).1 * (A i).2.2 - (A i).2.1 ^ 2) = (A i).2.1 ^ 2 by ring]
      at this
  set C : Fin r → Matrix (Fin 2) (Fin 2) R := fun i =>
    ((hδ i).unit⁻¹ : Rˣ).val • !![2 * (A i).2.2, -(A i).2.1; -(A i).2.1, 2 * (A i).1]
  have hBC : ∀ i, B i * C i = 1 := by
    intro i
    have hBM : B i * !![2 * (A i).2.2, -(A i).2.1; -(A i).2.1, 2 * (A i).1] =
        (4 * (A i).1 * (A i).2.2 - (A i).2.1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
      ext j j'; fin_cases j <;> fin_cases j' <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    simp only [C, Matrix.mul_smul, hBM, smul_smul, IsUnit.val_inv_mul, one_smul]
  set W := (Matrix.blockDiagonal C).submatrix e.symm e.symm
  have hWe : W.submatrix e e = Matrix.blockDiagonal C := by
    simp [W, Matrix.submatrix_submatrix]
  refine ⟨W, ?_, ?_, fun s => ?_⟩
  · have h1 : ((pairSumForm A).hessian * W).submatrix e e = 1 := by
      rw [← Matrix.submatrix_mul_equiv _ _ e e e, hM, hWe, ← Matrix.blockDiagonal_mul,
        show (fun i => B i * C i) = 1 from funext hBC, Matrix.blockDiagonal_one]
    rw [pow_zero, one_smul]
    have : (pairSumForm A).hessian * W = (((pairSumForm A).hessian * W).submatrix e e).submatrix e.symm e.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [this, h1, Matrix.submatrix_one_equiv]
  · simp only [W, Matrix.transpose_submatrix, Matrix.blockDiagonal_transpose]
    congr 2; funext i
    simp only [C, Matrix.transpose_smul]
    congr 1; ext j j'; fin_cases j <;> fin_cases j' <;> simp
  · simp only [W, Matrix.submatrix_apply, Matrix.blockDiagonal_apply_eq, C, Matrix.smul_apply, smul_eq_mul]
    obtain ⟨j, i⟩ := e.symm s
    fin_cases j <;> simp

/-- **$\pi \nmid N \iff$ unimodular, at every prime** (Hanke 2004, Lemma 2.2, p. 356, corrected): for $Q$
$\mathrm{GL}_n(R)$-equivalent to a corrected normal form $Q'$ (`IsJordanFormW Q' π P w`, no 2-dimensional blocks at
$\pi \nmid 2$), $\pi^0$ is a level of $Q$ iff all norm exponents vanish and, at $\pi \mid 2$, every coordinate lies in a
2-dimensional block whose cross coefficient is a unit (all blocks binary with unit Hessian). -/
@[kb "hanke2004" "Lemma 2.2, p. 356 (p ∤ N iff unimodular, corrected)"]
theorem isLocalLevel_zero_iff_unimodular (Q : QuadForm R n) {π : R} (hπ : Irreducible π)
    {Q' : QuadForm R n} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ} (hJ : IsJordanFormW Q' π P w)
    (hP : ¬ π ∣ 2 → P = ∅) (hE : IsGLEquiv Q Q') :
    IsLocalLevel Q π 0 ↔
      (∀ i, w i = 0) ∧ (π ∣ 2 → (∀ i, IsPaired P i) ∧ ∀ e ∈ P, IsUnit (Q'.coeff e.1 e.2)) := by
  classical
  rw [hE.isLocalLevel_iff]
  by_cases h2 : π ∣ 2
  · refine ⟨fun hL => ?_, fun ⟨_, h⟩ => ?_⟩
    · obtain ⟨hp, hu, hw⟩ := isLocalLevel_zero_jordanW hπ h2 hJ hL
      exact ⟨hw, fun _ => ⟨hp, hu⟩⟩
    · obtain ⟨hp, hu⟩ := h h2
      obtain ⟨r, A, ε, hA, hev⟩ := exists_eval_eq_pairSumForm hJ hp
      have hn : r * 2 = n := by simpa using Fintype.card_congr ε
      subst hn
      refine (isLocalLevel_zero_pairSumForm A hπ h2 fun i => ?_).of_isGLEquiv (isGLEquiv_of_perm ε hev)
      obtain ⟨e, he, hb⟩ := hA i
      rw [hb]; exact dvr_not_dvd_of_isUnit hπ (hu e he)
  · have hP0 := hP h2
    subst hP0
    have hdiag : Q' = QuadForm.diag fun i => Q'.coeff i i := by
      ext i j
      simp only [QuadForm.diag, Matrix.diagonal_apply]
      rcases lt_trichotomy i j with h | rfl | h
      · rw [if_neg h.ne]; exact hJ.2.2.2.1 i j h (by simp)
      · simp
      · rw [if_neg h.ne']; exact Q'.upper (show id j < id i from h)
    have hu : ∀ i, ∃ u, Q'.coeff i i = π ^ w i * u ∧ IsUnit u := fun i => hJ.2.2.2.2.2 i (by simp [IsPaired])
    rw [isLocalLevel_zero_iff hπ h2, hdiag, det_hessian_diag]
    simp only [h2, false_imp_iff, and_true]
    have hp := hπ.prime
    rw [show (π ∣ 2 ^ n * ∏ i, Q'.coeff i i) ↔ π ∣ ∏ i, Q'.coeff i i from
      ⟨fun h => (hp.dvd_or_dvd h).resolve_left fun h' => h2 (hp.dvd_of_dvd_pow h'), fun h => h.mul_left _⟩,
      hp.dvd_finset_prod_iff]
    simp only [Finset.mem_univ, true_and, not_exists]
    refine forall_congr' fun i => ?_
    obtain ⟨u, hu1, hu2⟩ := hu i
    rw [hu1, dvd_pow_mul_unit_iff hπ hu2]; omega

/-! ### The dyadic results for a general form at $\pi \nmid N$ -/

open Classical in
/-- **The Arf sign of $Q$ at $\pi$** (the dyadic $\Phi_n(\mathfrak p)$, `DVR.pairArf` for a `pairSumForm`): $+1$ if $Q \bmod \pi$ has
more than $q^{n-1}$ zeros in $(R/\pi)^n$ (then $Q \bmod \pi$ is hyperbolic), $-1$ otherwise. For an even unimodular form at
$\pi \mid 2$ this is the Arf invariant sign $\varepsilon$ (`arfSign_pairSumForm`). -/
@[kb "hanke2004" "Φ_n(𝔭), p. 357 (dyadic analogue)"]
noncomputable def arfSignQ (Q : QuadForm R n) (π : R) : ℤ :=
  if q R ^ (n - 1) < repCount Q π 1 0 then 1 else -1

theorem SameCounts.arfSign_eq {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) :
    arfSignQ Q π = arfSignQ Q' π := by
  simp only [arfSignQ, (h 1 0).1]

/-- For an even unimodular `pairSumForm`, `arfSignQ` is the Arf sign `pairArf` (from Table 1, dyadic). -/
theorem arfSign_pairSumForm [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) {π : R}
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 1 ≤ r) :
    arfSignQ (pairSumForm A) π = pairArf A := by
  have hc := (card_pairSum_mod_pi A π hπ h2 hb hr 0).1 (dvd_zero π)
  have hq := two_le_q_of_fintype (R := R)
  have hpos : (0 : ℤ) < (q R : ℤ) ^ r - (q R : ℤ) ^ (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    have : (0 : ℤ) < (q R : ℤ) ^ s := by positivity
    have : (2 : ℤ) ≤ q R := by exact_mod_cast hq
    nlinarith
  unfold arfSignQ
  rcases pairArf_eq A with h | h
  · rw [h] at hc ⊢
    rw [if_pos]
    rw [pairSum_exp]
    have : ((q R ^ (2 * r - 1) : ℕ) : ℤ) < (repCount (pairSumForm A) π 1 0 : ℤ) := by
      rw [hc]; push_cast; linarith
    exact_mod_cast this
  · rw [h] at hc ⊢
    rw [if_neg]
    rw [pairSum_exp, not_lt]
    have : (repCount (pairSumForm A) π 1 0 : ℤ) ≤ ((q R ^ (2 * r - 1) : ℕ) : ℤ) := by
      rw [hc]; push_cast; linarith
    exact_mod_cast this

/-- **Count form:** at dyadic $\pi \nmid N$, $Q$ has the counts (all levels, all types) of an even unimodular
`pairSumForm`. -/
theorem exists_pairSum_sameCounts (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2)
    (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) :
    ∃ (r : ℕ) (A : Fin r → R × R × R) (h : r * 2 = n), (∀ i, ¬ π ∣ (A i).2.1) ∧
      SameCounts Q (h ▸ pairSumForm A) π := by
  obtain ⟨r, A, h, hb, hE⟩ := exists_pairSum_of_isLocalLevel_zero Q hπ h2 h20 hL
  exact ⟨r, A, h, hb, hE.sameCounts π⟩

/-- **At dyadic $\pi \nmid N$ the dimension is even** (so for odd $n$ every dyadic $\mathfrak p$ divides $N$). -/
theorem even_of_isLocalLevel_zero_dyadic (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2)
    (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) : Even n := by
  obtain ⟨r, -, h, -⟩ := exists_pairSum_of_isLocalLevel_zero Q hπ h2 h20 hL
  exact ⟨r, by omega⟩

section DyadicGeneral

variable {π : R}

/-- **Table 1 at dyadic $\pi \nmid N$ for a general form** (Hanke 2004, Table 1, p. 363; the paper leaves $\mathfrak p \mid 2$ to
"case-by-case" computation): $n = 2r \ge 2$, $\varepsilon$ = `arfSignQ Q π`, $q = \#R/\pi$:
$r_\pi(s) = q^{n-1} + \varepsilon(q^{n/2} - q^{n/2-1})$ for $\pi \mid s$ and $r_\pi(s) = q^{n-1} - \varepsilon q^{n/2-1}$ for $\pi \nmid s$.
From `card_pairSum_mod_pi` and `DVR.exists_pairSum_of_isLocalLevel_zero`. -/
@[kb "hanke2004" "Table 1, p. 363 (dyadic p ∤ N, general Q)"]
theorem card_mod_pi_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) (s : R) :
    (π ∣ s → (repCount Q π 1 s : ℤ) =
      (q R : ℤ) ^ (n - 1) + arfSignQ Q π * ((q R : ℤ) ^ (n / 2) - (q R : ℤ) ^ (n / 2 - 1))) ∧
    (¬ π ∣ s → (repCount Q π 1 s : ℤ) = (q R : ℤ) ^ (n - 1) - arfSignQ Q π * (q R : ℤ) ^ (n / 2 - 1)) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  have hr : 1 ≤ r := by omega
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb hr, (hS 1 s).1, show r * 2 / 2 = r by omega,
    pairSum_exp]
  exact card_pairSum_mod_pi A π hπ h2 hb hr s

/-- **$\beta_\pi(m)$, $\pi \nmid m$, at dyadic $\pi \nmid N$** (Remark 3.4.1(a)): $1 - \varepsilon q^{-n/2}$. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (dyadic p ∤ N, general Q)"]
theorem localDensity_unit_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n)
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) (m : R)
    (hm : ¬ π ∣ m) : localDensity Q π m = 1 - (arfSignQ Q π : ℝ) / (q R : ℝ) ^ (n / 2) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  have hr : 1 ≤ r := by omega
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb hr, hS.localDensity_eq, show r * 2 / 2 = r by omega]
  exact localDensity_unit_pairSum A π hπ h2 hb hr m hm

/-- **$\beta_\pi(m)$, $\mathrm{ord}_\pi m = 1$, at dyadic $\pi \nmid N$** (Remark 5.4.1(b)):
$(1 - \varepsilon q^{-n/2})(1 + \varepsilon q^{1-n/2})$. -/
@[kb "hanke2004" "Remark 5.4.1(b), p. 370 (dyadic p ∤ N, general Q)"]
theorem localDensity_ord_one_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n)
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) (m : R)
    (hm1 : π ∣ m) (hm2 : ¬ π ^ 2 ∣ m) :
    localDensity Q π m =
      (1 - (arfSignQ Q π : ℝ) / (q R : ℝ) ^ (n / 2)) * (1 + (arfSignQ Q π : ℝ) / (q R : ℝ) ^ (n / 2 - 1)) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  have hr : 1 ≤ r := by omega
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb hr, hS.localDensity_eq, show r * 2 / 2 = r by omega]
  exact localDensity_ord_one_pairSum A π hπ h2 hb hr m hm1 hm2

/-- **Remark 3.5.1 at dyadic $\pi \nmid N$ for a general form** (Hanke 2004, p. 362: "when $n \ge 3$ and $\mathfrak p \nmid N$,
every number $m$ is locally represented at $\mathfrak p$"; $n$ is even here, so $n \ge 4$). From `isLocallyRepresentedAt_pairSum`. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (dyadic p ∤ N, general Q)"]
theorem isLocallyRepresentedAt_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n)
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (m : R) :
    IsLocallyRepresentedAt Q π m := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  rw [hS.isLocallyRepresentedAt_iff]
  exact isLocallyRepresentedAt_pairSum A π hπ h2 hb (by omega) m

/-- **Every $T$ is $\pi$-stable at dyadic $\pi \nmid N$** ($n \ge 3$). From `isPStable_pairSum`. -/
theorem isPStable_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (S₀ : Finset (Fin n)) (T : R) :
    IsPStable Q S₀ π T := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  rw [hS.isPStable_iff S₀ ∅]
  exact isPStable_pairSum A π hπ h2 hb (by omega) ∅ T

/-- **Table 2 at dyadic $\pi \nmid N$, $\pi \nmid T'$, for a general form** (Hanke 2004, Table 2, p. 370, with
$\Phi_n(\mathfrak p) := \varepsilon$): $C_\pi(T') = \dfrac{q^{n/2-1}}{q^{n/2-1} - \varepsilon}$. From `table2_even_unit_pairSum`. -/
@[kb "hanke2004" "Table 2, p. 370 (dyadic p ∤ N, general Q)"]
theorem table2_unit_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (T : R) (hT : ¬ π ∣ T) :
    localConstC Q π T = (q R : ℝ) ^ (n / 2 - 1) / ((q R : ℝ) ^ (n / 2 - 1) - arfSignQ Q π) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  have hr : 2 ≤ r := by omega
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb (by omega), hS.localConstC_eq,
    show r * 2 / 2 = r by omega]
  exact table2_even_unit_pairSum A π hπ h2 hb hr T hT

/-- **Table 2 at dyadic $\pi \nmid N$, $\mathrm{ord}_\pi T' = 1$, for a general form** (Hanke 2004, Table 2, p. 370; (5.9)):
$C_\pi(T') = \dfrac{q^{n-2}}{q^{n-2} - 1}$. From `table2_ord_one_pairSum`. -/
@[kb "hanke2004" "Table 2, p. 370; (5.9) (dyadic p ∤ N, general Q)"]
theorem table2_ord_one_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (T : R) (hT1 : π ∣ T)
    (hT2 : ¬ π ^ 2 ∣ T) : localConstC Q π T = (q R : ℝ) ^ (n - 2) / ((q R : ℝ) ^ (n - 2) - 1) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  rw [hS.localConstC_eq]
  exact table2_ord_one_pairSum A π hπ h2 hb (by omega) T hT1 hT2

/-- **(5.12), corrected, at dyadic $\pi \nmid N$ for a general form** (Hanke 2004, p. 371, with $\Phi_n := \varepsilon$): for
$\pi^2 \nmid T'$, $C'_\pi(T') = 1$ if $\pi \mid T'$ or $\varepsilon = 1$, and $C'_\pi(T') = \frac{X}{X+1}$, $X = q^{n/2-1}$, if
$\pi \nmid T'$ and $\varepsilon = -1$; so $C'_\pi(T') = 1 \iff \pi \mid T'$ or $\varepsilon = (-1)^n = 1$. From `localConstC'_pairSum`. -/
@[kb "hanke2004" "(5.12), p. 371 (corrected; dyadic p ∤ N, general Q)"]
theorem localConstC'_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (T : R) (hT2 : ¬ π ^ 2 ∣ T) :
    (π ∣ T → localConstC' Q π T = 1) ∧
    (¬ π ∣ T → arfSignQ Q π = 1 → localConstC' Q π T = 1) ∧
    (¬ π ∣ T → arfSignQ Q π = -1 →
      localConstC' Q π T = (q R : ℝ) ^ (n / 2 - 1) / ((q R : ℝ) ^ (n / 2 - 1) + 1)) ∧
    (localConstC' Q π T = 1 ↔ π ∣ T ∨ arfSignQ Q π = 1) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb (by omega), hS.localConstC'_eq,
    show r * 2 / 2 = r by omega]
  exact localConstC'_pairSum A π hπ h2 hb (by omega) T hT2

open Classical in
/-- **Per-place lower bound L10 at dyadic $\pi \nmid N$, general form** (proof of Thm 5.7(b),(c), p. 374): for $m \ne 0$,
$\beta_\pi(m) \ge (1 - \varepsilon q^{-n/2})\cdot\frac{X-1}{X+1}$ if $\varepsilon = -1$ and $\pi \mid m$, and $\ge 1 - \varepsilon q^{-n/2}$
otherwise ($X = q^{n/2-1}$). From `localDensity_ge_pairSum`. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at dyadic p ∤ N, general Q)"]
theorem localDensity_ge_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n)
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n) (m : R)
    (hm : m ≠ 0) :
    (1 - (arfSignQ Q π : ℝ) / (q R : ℝ) ^ (n / 2)) *
        (if arfSignQ Q π = -1 ∧ π ∣ m then
          ((q R : ℝ) ^ (n / 2 - 1) - 1) / ((q R : ℝ) ^ (n / 2 - 1) + 1) else 1) ≤
      localDensity Q π m := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  rw [hS.arfSign_eq, arfSign_pairSumForm A hπ h2 hb (by omega), hS.localDensity_eq,
    show r * 2 / 2 = r by omega]
  convert localDensity_ge_pairSum A π hπ h2 h20 hb (by omega) m hm using 2

end DyadicGeneral

end Dyadic

/-! ### Remark 3.8.1: $\pi \nmid N$ and $n \ge 3$ imply isotropy -/

section Isotropy

/-- **Primitive zeros mod every $\pi^k$ at a non-dyadic good prime:** for $\pi \nmid 2\det H$ and $n \ge 3$, every $k \ge 1$
has a non-Zero-type solution of $Q \equiv 0 \pmod{\pi^k}$. -/
theorem repCountOf_nonZero_zero_pos_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) {π : R}
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    0 < repCountOf Q π k 0 (fun x => ¬ IsZeroType π k x) := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [(hS k 0).2]
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  rw [repCountOf_nonZero_diag_succ a π hπ h2 ha 0 l]
  refine Nat.mul_pos (pow_pos (q_pos (R := R)) _) ?_
  have h1 := repCount_one_eq_nonZero_add (QuadForm.diag a) π hπ 0
  simp only [dvd_zero, ↓reduceIte] at h1
  have hq : (3 : ℤ) ≤ q R := by exact_mod_cast three_le_q hπ h2
  have hc := card_diag_mod_pi a π hπ h2 ha (by omega) 1 (fun h => hπ.not_isUnit (isUnit_of_dvd_one h))
  suffices h : (2 : ℤ) ≤ repCount (QuadForm.diag a) π 1 0 by omega
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := by obtain ⟨m, rfl⟩ := he; exact ⟨m - 2, by omega⟩
    rw [(hc.1 he).1, show 2 * j + 4 - 1 = (j + 1) + (j + 1) + 1 by omega,
      show (2 * j + 4) / 2 - 1 = j + 1 by omega]
    have hχ := quadraticChar_dichotomy (F := 𝔽) (a := res ((-1) ^ ((2 * j + 4) / 2) * ∏ i, a i))
      (residue_sign_prod_ne_zero a hπ ha _)
    have hY : (3 : ℤ) ≤ (q R : ℤ) ^ (j + 1) := le_trans hq (le_self_pow₀ (by linarith) (by omega))
    rw [pow_succ, pow_add]
    generalize (q R : ℤ) ^ (j + 1) = Y at hY ⊢
    have h6 : 6 ≤ (q R : ℤ) * (Y - 1) := by nlinarith
    have h7 : 0 ≤ (Y - 3) * ((q R : ℤ) * (Y - 1) + 1) := mul_nonneg (by linarith) (by linarith)
    rcases hχ with h | h <;> rw [h] <;> nlinarith
  · rw [(hc.2 ho).1]
    have : (q R : ℤ) ^ 2 ≤ (q R : ℤ) ^ (n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
    push_cast; nlinarith

/-- **Primitive zeros mod every $\pi^k$ at dyadic $\pi \nmid N$** ($n \ge 3$). -/
theorem repCountOf_nonZero_zero_pos_of_level_zero_dyadic [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n)
    {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) (hn : 3 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) : 0 < repCountOf Q π k 0 (fun x => ¬ IsZeroType π k x) := by
  obtain ⟨r, A, h, hb, hS⟩ := exists_pairSum_sameCounts Q hπ h2 h20 hL
  subst h
  have hr : 2 ≤ r := by
    have := even_of_isLocalLevel_zero_dyadic Q hπ h2 h20 hL; omega
  rw [(hS k 0).2]
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have hG := repCountGood_add_of_gradBound (pairSumForm A) π hπ (pairSumPairs r) 0
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) 0 1 l le_rfl
  rw [isGoodType_unimodularCoords_zero, isGoodType_unimodularCoords_zero] at hG
  rw [hG]
  refine Nat.mul_pos (pow_pos (q_pos (R := R)) _) ?_
  have hc := (repCountOf_nonZero_pairSum A π hπ h2 hb (by omega) 0).1 (dvd_zero π)
  have hq : (2 : ℤ) ≤ q R := by exact_mod_cast two_le_q_of_fintype (R := R)
  have hY : (2 : ℤ) ≤ (q R : ℤ) ^ (r - 1) := le_trans hq (le_self_pow₀ (by linarith) (by omega))
  have hpos := (pairSum_pos_aux (q R) ((q R : ℤ) ^ (r - 1)) (pairArf A) hq hY (pairArf_eq A)).1
  have e1 : (q R : ℤ) ^ (2 * r - 1) = (q R : ℤ) ^ (r - 1) * ((q R : ℤ) ^ (r - 1) * q R) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have e2 : (q R : ℤ) ^ r = (q R : ℤ) ^ (r - 1) * q R := by rw [← pow_succ]; congr 1; omega
  have : (0 : ℤ) < repCountOf (pairSumForm A) π 1 0 (fun x => ¬ IsZeroType π 1 x) := by
    rw [hc, e1, e2]; exact hpos
  exact_mod_cast this

/-- **Remark 3.8.1 over a DVR** (Hanke 2004, p. 364: "if $\mathfrak p \nmid N$ and $n \ge 3$, then $\mathfrak p$ is isotropic"): for $R$ complete with finite residue field, $2 \ne 0$, $\pi \nmid N$ and $n \ge 3$, $Q$ is isotropic over the
fraction field $K$, at non-dyadic and dyadic $\pi$ alike. *Proof:* $Q$ has primitive zeros mod every $\pi^k$ (a unit
diagonal form, resp. an even unimodular `pairSumForm`, has $r_\pi(0) \ge 2$ and Good solutions lift from level 1), and
$R^n$ is compact (`isotropicIn_of_primitive_pow_dvd`). -/
@[kb "hanke2004" "Remark 3.8.1, p. 364"]
theorem isotropicIn_of_isLocalLevel_zero [Fintype 𝔽] [DecidableEq 𝔽]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0)
    (hn : 3 ≤ n) : Q.IsotropicIn K := by
  have hpos : ∀ k, 1 ≤ k → 0 < repCountOf Q π k 0 (fun x => ¬ IsZeroType π k x) := by
    by_cases h2 : π ∣ 2
    · exact repCountOf_nonZero_zero_pos_of_level_zero_dyadic Q hπ h2 h20 hL hn
    · exact repCountOf_nonZero_zero_pos_of_unimodular Q hπ h2 ((isLocalLevel_zero_iff hπ h2).1 hL) hn
  refine isotropicIn_of_primitive_pow_dvd K Q π hπ fun C => ?_
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · refine ⟨Pi.single ⟨0, by omega⟩ 1, ⟨⟨0, by omega⟩, ?_⟩, by simp⟩
    simpa using fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
  · have := hpos C hC
    rw [repCountOf, Nat.card_pos_iff] at this
    obtain ⟨⟨x, hx, hxz⟩⟩ := this.1
    refine ⟨liftV π C x, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := not_forall.1 hxz
      refine ⟨i, fun h => hi ?_⟩
      rw [← redV_liftV π C x]
      exact (mk_pi_dvd_iff π C hC _).2 h
    · have h := evalIn_redV Q π C (liftV π C x)
      rw [redV_liftV, hx, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      simpa using h

end Isotropy

end QuadFormsKB.LocalDensity.DVR
