/-
# Local densities over a DVR: (2.4) and (2.5) for a general multi-block normal form

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, $2 = \pi^e v$ with $v$ a unit, $e = \mathrm{ord}_\pi 2$).
**Proves** Hanke 2004, (2.4) and (2.5), p. 356, for $Q$ in the general (corrected) local normal form
`IsJordanFormW Q π P w` of `DyadicJordan.lean`, at every prime (dyadic, ramified or not, and non-dyadic), with the
**corrected** per-block values. Write $\mu_j$ for the scale exponent of a 2-dimensional block
$\pi^{w_j}$-normed block $ax^2 + bxy + cy^2$ ($b = \pi^{\mu_j}\beta$, $\beta$ a unit; $w_j \le \mu_j \le w_j + e$). Then
$$\mathrm{ord}_\pi D_{2Q} = \mathrm{ord}_\pi \det H = \sum_j \lambda'_j, \qquad \mathrm{ord}_\pi N = \max_j \lambda''_j,$$
$$\lambda'_j = \begin{cases} w_j + e & \dim Q_j = 1 \\ 2\mu_j & \dim Q_j = 2\end{cases}, \qquad
\lambda''_j = \begin{cases} w_j + 2e & \dim Q_j = 1 \\ 2\mu_j - w_j & \dim Q_j = 2.\end{cases}$$
In Lean the exponents are indexed by **coordinates** (`detBlockExp`, `levelBlockExp`): a coordinate of a 2-dimensional
block contributes $\mu_j$ to the sum (so the block contributes $2\mu_j$) and $2\mu_j - w_j$ to the max.

* `DVR.isLocalLevel_jordanW_iff`, `DVR.levelExp_jordanW` ((2.5)), `DVR.det_hessian_jordanW` ((2.4)).
* Mechanism: the Hessian is block diagonal; $\pi^k H^{-1}$ is integral with even diagonal column by column
  (`DVR.isLocalLevel_iff_cols`), and a column only sees its block (`DVR.col_unpaired_iff`, `DVR.cols_pair_iff`); for a
  binary block $\det = 4ac - b^2 = \pi^{2\mu}\cdot$unit and the level is $\pi^{2\mu - w}$ (`DVR.pairBlock_exp`); the
  determinant is a product over blocks (`Matrix.BlockTriangular.det_fintype`).
* **Where the printed formulas hold.** If $\pi^2 \nmid 2$ (all primes of $\mathbb Q$, unramified dyadic primes and all
  non-dyadic primes), every binary block has $\mu_j = w_j$ (`DVR.scale_eq_norm_of_not_sq_dvd_two`), so
  $\lambda''_j = w_j$ as printed and $\lambda'_j = 2w_j$ (the (2.4) erratum, `docs/updates-and-errata.md`)
  (`DVR.eq_2_4_2_5_of_not_sq_dvd_two`); the same holds for Hanke's printed normal form `IsJordanForm` at every
  prime where it exists (`DVR.eq_2_4_2_5_hankeNormal`). At non-dyadic $\pi$ there are no binary blocks and
  (2.4)/(2.5) hold verbatim: $\lambda'_j = \lambda''_j = w_j$ (`DVR.eq_2_4_2_5_nondyadic_W`).
* For a general nondegenerate $Q$ (through a normal form, Lemma 2.1 corrected): `DVR.eq_2_4_2_5_general`.

**Depends on** `DVRLevel.lean`.
-/
import QuadFormsKB.LocalDensity.DVRLevel

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Block structure of the Hessian of a normal form -/

section Structure

variable {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}

theorem hessian_symm' (Q : QuadForm R n) (i j : Fin n) : Q.hessian i j = Q.hessian j i := by
  simp [QuadForm.hessian, add_comm]

/-- Two pairs of a normal form sharing a coordinate are equal. -/
theorem IsJordanFormW.pair_unique (hJ : IsJordanFormW Q π P w) {e e' : Fin n × Fin n} (he : e ∈ P)
    (he' : e' ∈ P) {i : Fin n} (hi : e.1 = i ∨ e.2 = i) (hi' : e'.1 = i ∨ e'.2 = i) : e = e' := by
  by_contra hne
  obtain ⟨a, b, c, d⟩ := hJ.2.2.1 e he e' he' hne
  rcases hi with rfl | rfl <;> rcases hi' with h | h
  · exact a h.symm
  · exact b h.symm
  · exact c h.symm
  · exact d h.symm

/-- **Column of an unpaired coordinate:** $H_{l i} = 2c_{ii}$ if $l = i$ and $0$ otherwise. -/
theorem IsJordanFormW.hessian_unpaired (hJ : IsJordanFormW Q π P w) {i : Fin n} (hi : ¬ IsPaired P i)
    (l : Fin n) : Q.hessian l i = if l = i then 2 * Q.coeff i i else 0 := by
  split_ifs with h
  · subst h; simp [QuadForm.hessian]; ring
  · exact hJ.hessian_eq_zero h (fun h' => hi ⟨_, h', Or.inr rfl⟩) (fun h' => hi ⟨_, h', Or.inl rfl⟩)

/-- Outside its pair, the columns of a paired coordinate vanish. -/
theorem IsJordanFormW.hessian_pair_zero (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P)
    {i l : Fin n} (hi : e.1 = i ∨ e.2 = i) (hl1 : l ≠ e.1) (hl2 : l ≠ e.2) : Q.hessian l i = 0 := by
  have hli : l ≠ i := by rintro rfl; rcases hi with h | h <;> [exact hl1 h.symm; exact hl2 h.symm]
  refine hJ.hessian_eq_zero hli (fun h => ?_) (fun h => ?_)
  · have := hJ.pair_unique he h hi (Or.inr rfl)
    subst this; exact hl1 rfl
  · have := hJ.pair_unique he h hi (Or.inl rfl)
    subst this; exact hl2 rfl

theorem hessian_diag_apply (Q : QuadForm R n) (i : Fin n) : Q.hessian i i = 2 * Q.coeff i i := by
  simp [QuadForm.hessian]; ring

theorem IsJordanFormW.hessian_fst_snd (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) :
    Q.hessian e.1 e.2 = Q.coeff e.1 e.2 := by
  simp [QuadForm.hessian, Q.upper (show id e.1 < id e.2 from hJ.2.1 e he)]

theorem IsJordanFormW.hessian_snd_fst (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) :
    Q.hessian e.2 e.1 = Q.coeff e.1 e.2 := by
  rw [hessian_symm']; exact hJ.hessian_fst_snd he

end Structure

/-! ### Levels column by column -/

section Columns

/-- **Levels, column by column:** $\pi^k$ is a level of $Q$ iff for every $m$ the equation $H\vec x = \pi^k \vec e_m$ has a
solution $\vec x \in R^n$ with $x_m$ even (the $m$-th column of $W = \pi^k H^{-1}$). Symmetry of $W$ is automatic
($W^{\mathsf T}H = \pi^k I$ too, and $\pi^k \ne 0$). -/
theorem isLocalLevel_iff_cols (Q : QuadForm R n) {π : R} (hπ : π ≠ 0) (k : ℕ) :
    IsLocalLevel Q π k ↔
      ∀ m, ∃ x : Fin n → R, Q.hessian *ᵥ x = π ^ k • Pi.single m 1 ∧ 2 ∣ x m := by
  classical
  constructor
  · rintro ⟨W, hW, -, hd⟩ m
    refine ⟨fun l => W l m, ?_, hd m⟩
    funext l
    have := congrFun (congrFun hW l) m
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, this]
  · intro h
    choose x hx hd using h
    set W : Matrix (Fin n) (Fin n) R := Matrix.of fun l m => x m l
    have hHW : Q.hessian * W = π ^ k • (1 : Matrix (Fin n) (Fin n) R) := by
      ext l m
      have := congrFun (hx m) l
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at this
      simp only [Matrix.mul_apply, W, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, this]
    have hWH : Wᵀ * Q.hessian = π ^ k • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [← hessian_transpose, ← Matrix.transpose_mul, hHW, transpose_smul, transpose_one]
    have hsym : π ^ k • Wᵀ = π ^ k • W := by
      calc π ^ k • Wᵀ = Wᵀ * (Q.hessian * W) := by rw [hHW, Matrix.mul_smul, Matrix.mul_one]
        _ = (Wᵀ * Q.hessian) * W := by rw [Matrix.mul_assoc]
        _ = π ^ k • W := by rw [hWH, Matrix.smul_mul, Matrix.one_mul]
    refine ⟨W, hHW, ?_, fun i => hd i⟩
    ext i j
    have := congrFun (congrFun hsym i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (pow_ne_zero k hπ) this

variable {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}

/-- **The column of an unpaired coordinate** (a 1-dimensional block $c_{ii}x_i^2$): solvable with even $x_i$ iff
$4c_{ii} \mid \pi^k$. -/
theorem col_unpaired_iff (hJ : IsJordanFormW Q π P w) {i : Fin n} (hi : ¬ IsPaired P i) (k : ℕ) :
    (∃ x : Fin n → R, Q.hessian *ᵥ x = π ^ k • Pi.single i 1 ∧ 2 ∣ x i) ↔ 4 * Q.coeff i i ∣ π ^ k := by
  classical
  have hcol := hJ.hessian_unpaired hi
  constructor
  · rintro ⟨x, hx, ⟨t, ht⟩⟩
    have h := congrFun hx i
    have hrow : ∀ r, Q.hessian i r = if r = i then 2 * Q.coeff i i else 0 := fun r => by
      rw [hessian_symm']; exact hcol r
    simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
    exact ⟨t, by rw [← h, ht]; ring⟩
  · rintro ⟨t, ht⟩
    refine ⟨Pi.single i (2 * t), ?_, by simp⟩
    funext l
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hcol, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [ht]; ring
    · ring

/-- **The two columns of a binary block** $ax^2 + bxy + cy^2$ on the pair $e$ (with $d = 4ac - b^2 \ne 0$, $2 \ne 0$):
both are solvable with even diagonal entries iff $d \mid \pi^k a$, $d \mid \pi^k b$ and $d \mid \pi^k c$. -/
theorem cols_pair_iff (hJ : IsJordanFormW Q π P w) (h20 : (2 : R) ≠ 0) {e : Fin n × Fin n} (he : e ∈ P)
    (hd : 4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ≠ 0) (k : ℕ) :
    ((∃ x : Fin n → R, Q.hessian *ᵥ x = π ^ k • Pi.single e.1 1 ∧ 2 ∣ x e.1) ∧
      (∃ y : Fin n → R, Q.hessian *ᵥ y = π ^ k • Pi.single e.2 1 ∧ 2 ∣ y e.2)) ↔
      (4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.1 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.2 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.2 e.2) := by
  classical
  have hne : e.1 ≠ e.2 := (hJ.2.1 e he).ne
  set a := Q.coeff e.1 e.1
  set b := Q.coeff e.1 e.2
  set c := Q.coeff e.2 e.2
  have h11 : Q.hessian e.1 e.1 = 2 * a := hessian_diag_apply Q _
  have h22 : Q.hessian e.2 e.2 = 2 * c := hessian_diag_apply Q _
  have h12 : Q.hessian e.1 e.2 = b := hJ.hessian_fst_snd he
  have h21 : Q.hessian e.2 e.1 = b := hJ.hessian_snd_fst he
  -- the two rows of the block
  have hrow : ∀ i, (i = e.1 ∨ i = e.2) → ∀ x : Fin n → R,
      (Q.hessian *ᵥ x) i = Q.hessian i e.1 * x e.1 + Q.hessian i e.2 * x e.2 := by
    intro i hi x
    simp only [Matrix.mulVec, dotProduct]
    refine Fintype.sum_eq_add e.1 e.2 hne fun l ⟨hl1, hl2⟩ => ?_
    rw [hessian_symm', hJ.hessian_pair_zero he (by rcases hi with rfl | rfl <;> simp) hl1 hl2, zero_mul]
  constructor
  · rintro ⟨⟨x, hx, ⟨s, hs⟩⟩, ⟨y, hy, ⟨t, ht⟩⟩⟩
    have x1 := congrFun hx e.1
    have x2 := congrFun hx e.2
    have y1 := congrFun hy e.1
    have y2 := congrFun hy e.2
    rw [hrow _ (Or.inl rfl)] at x1 y1
    rw [hrow _ (Or.inr rfl)] at x2 y2
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_apply, hne, hne.symm, ite_false, smul_eq_mul,
      mul_one, mul_zero, h11, h22, h12, h21] at x1 x2 y1 y2
    refine ⟨⟨t, ?_⟩, ⟨-x e.2, ?_⟩, ⟨s, ?_⟩⟩
    · refine mul_left_cancel₀ h20 ?_
      linear_combination (-(2 * a)) * y2 + b * y1 + (4 * a * c - b ^ 2) * ht
    · linear_combination 2 * a * x2 - b * x1
    · refine mul_left_cancel₀ h20 ?_
      linear_combination (-(2 * c)) * x1 + b * x2 + (4 * a * c - b ^ 2) * hs
  · rintro ⟨⟨t, ht⟩, ⟨v, hv⟩, ⟨s, hs⟩⟩
    -- columns supported on the pair
    have hsupp : ∀ (x : Fin n → R), (∀ l, l ≠ e.1 → l ≠ e.2 → x l = 0) → ∀ l, l ≠ e.1 → l ≠ e.2 →
        (Q.hessian *ᵥ x) l = 0 := by
      intro x hx l hl1 hl2
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = e.1 ∨ r = e.2
      · rw [hJ.hessian_pair_zero he (by rcases hr with rfl | rfl <;> simp) hl1 hl2, zero_mul]
      · push Not at hr; rw [hx r hr.1 hr.2, mul_zero]
    refine ⟨⟨fun l => if l = e.1 then 2 * s else if l = e.2 then -v else 0, ?_, by simp⟩,
      ⟨fun l => if l = e.1 then -v else if l = e.2 then 2 * t else 0, ?_, by simp [hne.symm]⟩⟩
    · funext l
      by_cases hl1 : l = e.1
      · subst hl1
        rw [hrow _ (Or.inl rfl)]
        simp only [h11, h12, ite_true, hne.symm, ite_false, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one]
        refine mul_left_cancel₀ hd ?_
        linear_combination (-(4 * a)) * hs + b * hv
      by_cases hl2 : l = e.2
      · subst hl2
        rw [hrow _ (Or.inr rfl)]
        simp only [h21, h22, ite_true, hne.symm, hne, ite_false, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
          mul_zero]
        refine mul_left_cancel₀ hd ?_
        linear_combination (-(2 * b)) * hs + (2 * c) * hv
      · rw [hsupp _ (fun l h1 h2 => by simp [h1, h2]) l hl1 hl2]
        simp [Pi.single_apply, hl1]
    · funext l
      by_cases hl1 : l = e.1
      · subst hl1
        rw [hrow _ (Or.inl rfl)]
        simp only [h11, h12, ite_true, hne.symm, hne, ite_false, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
          mul_zero]
        refine mul_left_cancel₀ hd ?_
        linear_combination (2 * a) * hv - (2 * b) * ht
      by_cases hl2 : l = e.2
      · subst hl2
        rw [hrow _ (Or.inr rfl)]
        simp only [h21, h22, ite_true, hne.symm, ite_false, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one]
        refine mul_left_cancel₀ hd ?_
        linear_combination b * hv - (4 * c) * ht
      · rw [hsupp _ (fun l h1 h2 => by simp [h1, h2]) l hl1 hl2]
        simp [Pi.single_apply, hl2]

/-- **The level of a normal form, block by block** (every $\pi$, $2 \ne 0$, every binary block nondegenerate):
$\pi^k$ is a level iff $4c_{ii} \mid \pi^k$ for every unpaired $i$ and $d \mid \pi^k a, \pi^k b, \pi^k c$ for every binary
block $ax^2 + bxy + cy^2$, $d = 4ac - b^2$. -/
theorem isLocalLevel_jordanW_iff_dvd (hJ : IsJordanFormW Q π P w) (hπ : π ≠ 0) (h20 : (2 : R) ≠ 0)
    (hd : ∀ e ∈ P, 4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ≠ 0) (k : ℕ) :
    IsLocalLevel Q π k ↔ (∀ i, ¬ IsPaired P i → 4 * Q.coeff i i ∣ π ^ k) ∧
      ∀ e ∈ P, (4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.1 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.2 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.2 e.2) := by
  rw [isLocalLevel_iff_cols Q hπ]
  constructor
  · intro h
    exact ⟨fun i hi => (col_unpaired_iff hJ hi k).1 (h i),
      fun e he => (cols_pair_iff hJ h20 he (hd e he) k).1 ⟨h e.1, h e.2⟩⟩
  · rintro ⟨h1, h2⟩ m
    by_cases hm : IsPaired P m
    · obtain ⟨e, he, hm⟩ := hm
      have := (cols_pair_iff hJ h20 he (hd e he) k).2 (h2 e he)
      rcases hm with rfl | rfl
      · exact this.1
      · exact this.2
    · exact (col_unpaired_iff hJ hm k).2 (h1 m hm)

end Columns

/-! ### Exponents: the corrected $\lambda'_j$, $\lambda''_j$ -/

section Exponents

/-- **The corrected (2.5) exponent, per coordinate** (Hanke 2004, (2.5), p. 356, $\lambda''_j$): for a coordinate in a
1-dimensional block, $w_i + 2t$ ($t = \mathrm{ord}_\pi 2$); for a coordinate in a 2-dimensional block with norm exponent
$w_i$ and scale exponent $\mu_i$, $2\mu_i - w_i$. ($\mu$ is only read on paired coordinates.) -/
@[kb "hanke2004" "(2.5), p. 356 (λ'', corrected)"]
noncomputable def levelBlockExp (P : Finset (Fin n × Fin n)) (w μ : Fin n → ℕ) (t : ℕ) (i : Fin n) : ℕ :=
  open Classical in if IsPaired P i then 2 * μ i - w i else w i + 2 * t

/-- **The corrected (2.4) exponent, per coordinate** (Hanke 2004, (2.4), p. 356, $\lambda'_j$): $w_i + t$ for a
1-dimensional block ($t = \mathrm{ord}_\pi 2$); $\mu_i$ for each of the two coordinates of a 2-dimensional block, so the
block contributes $2\mu_j$ (printed: $\nu_j$; see `docs/updates-and-errata.md`). -/
@[kb "hanke2004" "(2.4), p. 356 (λ', corrected)"]
noncomputable def detBlockExp (P : Finset (Fin n × Fin n)) (w μ : Fin n → ℕ) (t : ℕ) (i : Fin n) : ℕ :=
  open Classical in if IsPaired P i then μ i else w i + t

/-- **Scale exponents of the binary blocks:** $\mu$ is constant on each pair $e \in P$ and $c_{e_1e_2} = \pi^{\mu_{e_1}}\beta$
with $\beta$ a unit (the off-diagonal Hessian entry has valuation $\mu$). They always exist (`exists_isScaleExp`) and
are unique on the pairs. -/
def IsScaleExp (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n)) (μ : Fin n → ℕ) : Prop :=
  ∀ e ∈ P, μ e.1 = μ e.2 ∧ ∃ β, Q.coeff e.1 e.2 = π ^ μ e.1 * β ∧ IsUnit β

theorem pow_mul_unit_inj {π : R} (hπ : Irreducible π) {m m' : ℕ} {β β' : R} (hβ : IsUnit β)
    (hβ' : IsUnit β') (h : π ^ m * β = π ^ m' * β') : m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact dvr_not_pow_succ_dvd hπ hβ m (h ▸ (pow_dvd_pow π hl).mul_right β')
  · exact dvr_not_pow_succ_dvd hπ hβ' m' (h.symm ▸ (pow_dvd_pow π hl).mul_right β)

variable {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}

theorem exists_isScaleExp (hJ : IsJordanFormW Q π P w) : ∃ μ, IsScaleExp Q π P μ := by
  classical
  have h : ∀ e : Fin n × Fin n, ∃ m : ℕ, e ∈ P → ∃ β, Q.coeff e.1 e.2 = π ^ m * β ∧ IsUnit β := by
    intro e
    by_cases he : e ∈ P
    · obtain ⟨-, -, -, -, m, β, hb, hβ, -⟩ := hJ.2.2.2.2.1 e he
      exact ⟨m, fun _ => ⟨β, hb, hβ⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose μP hμP using h
  refine ⟨fun i => if hp : IsPaired P i then μP (Classical.choose hp) else 0, fun e he => ?_⟩
  have key : ∀ i, (e.1 = i ∨ e.2 = i) → (if hp : IsPaired P i then μP (Classical.choose hp) else 0) = μP e := by
    intro i hi
    have hp : IsPaired P i := ⟨e, he, hi⟩
    rw [dif_pos hp]
    obtain ⟨hm, hs⟩ := Classical.choose_spec hp
    rw [hJ.pair_unique hm he hs hi]
  simp only
  rw [key _ (Or.inl rfl), key _ (Or.inr rfl)]
  exact ⟨rfl, hμP e he⟩

/-- **A binary block, exponents** (pure algebra; every $\pi$): if $ax^2 + bxy + cy^2$ has exact norm exponent $w$
($\pi^w \mid a, c$; not all of $a, b, c$ divisible by $\pi^{w+1}$) and scale exponent $\mu \ge w$ ($b = \pi^\mu\beta$,
$\pi^{\mu+1} \mid 2a, 2c$), then $d = 4ac - b^2 = \pi^{2\mu}\delta$ with $\delta$ a unit, and
$d \mid \pi^k a, \pi^k b, \pi^k c \iff k \ge 2\mu - w$. -/
theorem pairBlock_exp {π : R} (hπ : Irreducible π) {w μ : ℕ} {a b c β : R} (ha : π ^ w ∣ a) (hc : π ^ w ∣ c)
    (hex : ¬ (π ^ (w + 1) ∣ a ∧ π ^ (w + 1) ∣ b ∧ π ^ (w + 1) ∣ c)) (hb : b = π ^ μ * β) (hβ : IsUnit β)
    (hwμ : w ≤ μ) (h2a : π ^ (μ + 1) ∣ 2 * a) (h2c : π ^ (μ + 1) ∣ 2 * c) :
    (∃ δ, IsUnit δ ∧ 4 * a * c - b ^ 2 = π ^ (2 * μ) * δ) ∧
      ∀ k, (4 * a * c - b ^ 2 ∣ π ^ k * a ∧ 4 * a * c - b ^ 2 ∣ π ^ k * b ∧ 4 * a * c - b ^ 2 ∣ π ^ k * c) ↔
        2 * μ - w ≤ k := by
  obtain ⟨a', ha'⟩ := h2a
  obtain ⟨c', hc'⟩ := h2c
  set δ := π ^ 2 * a' * c' - β ^ 2
  have hdet : 4 * a * c - b ^ 2 = π ^ (2 * μ) * δ := by
    rw [show 4 * a * c = (2 * a) * (2 * c) by ring, ha', hc', hb]; ring
  have hδ : IsUnit δ := by
    refine dvr_isUnit_of_not_dvd hπ fun h => dvr_not_dvd_of_isUnit hπ (hβ.pow 2) ?_
    have h1 : π ∣ π ^ 2 * a' * c' := ⟨π * a' * c', by ring⟩
    have := dvd_sub h1 h
    rwa [show π ^ 2 * a' * c' - δ = β ^ 2 by ring] at this
  refine ⟨⟨δ, hδ, hdet⟩, fun k => ?_⟩
  rw [hdet, hδ.mul_right_dvd, hδ.mul_right_dvd, hδ.mul_right_dvd]
  have hbk : π ^ (2 * μ) ∣ π ^ k * b ↔ μ ≤ k := by
    rw [hb, ← mul_assoc, ← pow_add, hβ.dvd_mul_right, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]; omega
  rw [hbk]
  constructor
  · rintro ⟨h1, hk, h3⟩
    by_cases hμw : μ = w
    · omega
    · have hb1 : π ^ (w + 1) ∣ b := by rw [hb]; exact (pow_dvd_pow π (by omega)).mul_right _
      have key : ∀ x : R, π ^ w ∣ x → ¬ π ^ (w + 1) ∣ x → π ^ (2 * μ) ∣ π ^ k * x → 2 * μ - w ≤ k := by
        intro x hx hx' hd
        obtain ⟨u, hu, hu1⟩ := dvr_exact hπ hx hx'
        rw [hu, ← mul_assoc, ← pow_add, hu1.dvd_mul_right, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at hd
        omega
      by_cases hA : π ^ (w + 1) ∣ a
      · exact key c hc (fun hC => hex ⟨hA, hb1, hC⟩) h3
      · exact key a ha hA h1
  · intro hk
    have hd : ∀ x : R, π ^ w ∣ x → π ^ (2 * μ) ∣ π ^ k * x := fun x hx =>
      (pow_dvd_pow π (by omega : 2 * μ ≤ k + w)).trans (by rw [pow_add]; exact mul_dvd_mul_left _ hx)
    exact ⟨hd a ha, by omega, hd c hc⟩

/-- The binary block of a pair $e$ of a normal form, with its scale exponent: the hypotheses of `pairBlock_exp`. -/
theorem IsJordanFormW.pairBlock (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) {μ : Fin n → ℕ}
    (hμ : IsScaleExp Q π P μ) {e : Fin n × Fin n} (he : e ∈ P) :
    (∃ δ, IsUnit δ ∧ 4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 = π ^ (2 * μ e.1) * δ) ∧
      ∀ k, (4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.1 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.1 e.2 ∧
        4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ∣ π ^ k * Q.coeff e.2 e.2) ↔
        2 * μ e.1 - w e.1 ≤ k := by
  obtain ⟨-, ha, hc, hex, μ0, β0, hb0, hβ0, hwμ, h2a, h2c, -⟩ := hJ.2.2.2.2.1 e he
  obtain ⟨-, β, hb, hβ⟩ := hμ e he
  have : μ0 = μ e.1 := pow_mul_unit_inj hπ hβ0 hβ (hb0.symm.trans hb)
  subst this
  exact pairBlock_exp hπ ha hc hex hb hβ hwμ h2a h2c

/-- $4c \mid \pi^k$ for $c = \pi^{w}u$ and $2 = \pi^t v$ ($u, v$ units) iff $w + 2t \le k$. -/
theorem four_mul_dvd_iff {π : R} (hπ : Irreducible π) {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v)
    {c u : R} {m : ℕ} (hc : c = π ^ m * u) (hu : IsUnit u) (k : ℕ) : 4 * c ∣ π ^ k ↔ m + 2 * t ≤ k := by
  rw [show 4 * c = π ^ (m + 2 * t) * (v ^ 2 * u) by rw [hc, show (4 : R) = 2 * 2 by norm_num, ht]; ring,
    (hv.pow 2 |>.mul hu).mul_right_dvd, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]

/-- **(2.5), corrected, for a general normal form, as a level criterion** (Hanke 2004, (2.5), p. 356, every prime):
for $Q$ in the normal form `IsJordanFormW Q π P w` with scale exponents $\mu$, $2 = \pi^t v$ ($v$ a unit, $2 \ne 0$),
$\pi^k$ is a local level iff $k \ge \lambda''_i$ for every coordinate $i$ (`levelBlockExp`): $k \ge w_i + 2t$ on
1-dimensional blocks and $k \ge 2\mu_j - w_j$ on 2-dimensional blocks. -/
@[kb "hanke2004" "(2.5), p. 356 (general normal form, corrected)"]
theorem isLocalLevel_jordanW_iff (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0)
    {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v) {μ : Fin n → ℕ} (hμ : IsScaleExp Q π P μ) (k : ℕ) :
    IsLocalLevel Q π k ↔ ∀ i, levelBlockExp P w μ t i ≤ k := by
  classical
  have hd : ∀ e ∈ P, 4 * Q.coeff e.1 e.1 * Q.coeff e.2 e.2 - Q.coeff e.1 e.2 ^ 2 ≠ 0 := by
    intro e he
    obtain ⟨δ, hδ, h⟩ := (hJ.pairBlock hπ hμ he).1
    rw [h]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hδ.ne_zero
  rw [isLocalLevel_jordanW_iff_dvd hJ hπ.ne_zero h20 hd]
  -- the exponent on a pair is the same at both coordinates
  have hpair : ∀ e ∈ P, ∀ i, (e.1 = i ∨ e.2 = i) → levelBlockExp P w μ t i = 2 * μ e.1 - w e.1 := by
    intro e he i hi
    rw [levelBlockExp, if_pos ⟨e, he, hi⟩]
    rcases hi with rfl | rfl
    · rfl
    · rw [← (hJ.2.2.2.2.1 e he).1, ← (hμ e he).1]
  have hunp : ∀ i, ¬ IsPaired P i → levelBlockExp P w μ t i = w i + 2 * t := fun i hi => by
    rw [levelBlockExp, if_neg hi]
  constructor
  · rintro ⟨h1, h2⟩ i
    by_cases hi : IsPaired P i
    · obtain ⟨e, he, hi⟩ := hi
      rw [hpair e he i hi]; exact ((hJ.pairBlock hπ hμ he).2 k).1 (h2 e he)
    · obtain ⟨u, hu, hu1⟩ := hJ.2.2.2.2.2 i hi
      rw [hunp i hi]; exact (four_mul_dvd_iff hπ hv ht hu hu1 k).1 (h1 i hi)
  · intro h
    refine ⟨fun i hi => ?_, fun e he => ((hJ.pairBlock hπ hμ he).2 k).2 ?_⟩
    · obtain ⟨u, hu, hu1⟩ := hJ.2.2.2.2.2 i hi
      exact (four_mul_dvd_iff hπ hv ht hu hu1 k).2 (hunp i hi ▸ h i)
    · exact hpair e he e.1 (Or.inl rfl) ▸ h e.1

/-- **(2.5), corrected, for a general normal form** (Hanke 2004, (2.5), p. 356, every prime):
$\mathrm{ord}_\pi N = \max_i \lambda''_i$, with $\lambda''_i = w_i + 2\,\mathrm{ord}_\pi 2$ on 1-dimensional blocks and
$\lambda''_i = 2\mu_j - w_j$ on 2-dimensional blocks (`levelBlockExp`). -/
@[kb "hanke2004" "(2.5), p. 356 (general normal form, corrected)"]
theorem levelExp_jordanW (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0)
    {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v) {μ : Fin n → ℕ} (hμ : IsScaleExp Q π P μ) :
    levelExp Q π = Finset.univ.sup (levelBlockExp P w μ t) := by
  have hiff := isLocalLevel_jordanW_iff hJ hπ h20 hv ht hμ
  have hex : ∃ k, IsLocalLevel Q π k :=
    ⟨_, (hiff _).2 fun i => Finset.le_sup (f := levelBlockExp P w μ t) (Finset.mem_univ i)⟩
  refine le_antisymm ((isLocalLevel_iff_levelExp_le hex _).1 ((hiff _).2 fun i =>
    Finset.le_sup (f := levelBlockExp P w μ t) (Finset.mem_univ i))) ?_
  exact Finset.sup_le fun i _ => (hiff _).1 ((isLocalLevel_iff_levelExp_le hex _).2 le_rfl) i

end Exponents

/-! ### The determinant: a product over the blocks -/

section Det

variable {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}

open Classical in
/-- **The block label** of a coordinate: the first coordinate of its pair, or itself if it is unpaired (or a first
coordinate). The Hessian of a normal form is block triangular (indeed block diagonal) for it. -/
noncomputable def blockLabel (P : Finset (Fin n × Fin n)) (i : Fin n) : Fin n :=
  if h : ∃ e ∈ P, e.2 = i then (Classical.choose h).1 else i

theorem blockLabel_snd (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) :
    blockLabel P e.2 = e.1 := by
  have h : ∃ e' ∈ P, e'.2 = e.2 := ⟨e, he, rfl⟩
  rw [blockLabel, dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  rw [hJ.pair_unique h1 he (Or.inr h2) (Or.inr rfl)]

theorem blockLabel_of_not {i : Fin n} (h : ¬ ∃ e ∈ P, e.2 = i) : blockLabel P i = i := by
  rw [blockLabel, dif_neg h]

theorem IsJordanFormW.not_snd_of_fst (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) :
    ¬ ∃ e' ∈ P, e'.2 = e.1 := by
  rintro ⟨e', he', h⟩
  have := hJ.pair_unique he' he (Or.inr h) (Or.inl rfl)
  rw [this] at h
  exact (hJ.2.1 e he).ne' h

theorem blockLabel_unpaired {i : Fin n} (hi : ¬ IsPaired P i) : blockLabel P i = i :=
  blockLabel_of_not fun ⟨e, he, h⟩ => hi ⟨e, he, Or.inr h⟩

theorem blockLabel_eq_unpaired (hJ : IsJordanFormW Q π P w) {a : Fin n} (ha : ¬ IsPaired P a) (i : Fin n) :
    blockLabel P i = a ↔ i = a := by
  by_cases h : ∃ e ∈ P, e.2 = i
  · obtain ⟨e, he, rfl⟩ := h
    rw [blockLabel_snd hJ he]
    exact ⟨fun h => absurd ⟨e, he, Or.inl h⟩ ha, fun h => absurd ⟨e, he, Or.inr h⟩ ha⟩
  · rw [blockLabel_of_not h]

theorem blockLabel_eq_fst (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) (i : Fin n) :
    blockLabel P i = e.1 ↔ i = e.1 ∨ i = e.2 := by
  by_cases h : ∃ e' ∈ P, e'.2 = i
  · obtain ⟨e', he', rfl⟩ := h
    rw [blockLabel_snd hJ he']
    constructor
    · intro h
      right; rw [hJ.pair_unique he' he (Or.inl h) (Or.inl rfl)]
    · rintro (h | h)
      · exact absurd ⟨e', he', h⟩ (hJ.not_snd_of_fst he)
      · rw [hJ.pair_unique he' he (Or.inr h) (Or.inr rfl)]
  · rw [blockLabel_of_not h]
    exact ⟨Or.inl, fun h' => h'.elim id fun h' => absurd ⟨e, he, h'.symm⟩ h⟩

theorem blockLabel_ne_snd (hJ : IsJordanFormW Q π P w) {e : Fin n × Fin n} (he : e ∈ P) (i : Fin n) :
    blockLabel P i ≠ e.2 := by
  by_cases h : ∃ e' ∈ P, e'.2 = i
  · obtain ⟨e', he', rfl⟩ := h
    rw [blockLabel_snd hJ he']
    intro h'
    have := hJ.pair_unique he' he (Or.inl h') (Or.inr rfl)
    rw [this] at h'
    exact (hJ.2.1 e he).ne h'
  · rw [blockLabel_of_not h]
    rintro rfl; exact h ⟨e, he, rfl⟩

/-- **The Hessian of a normal form is block diagonal** for `blockLabel` (in particular block triangular). -/
theorem IsJordanFormW.blockTriangular (hJ : IsJordanFormW Q π P w) :
    Q.hessian.BlockTriangular (blockLabel P) := by
  intro i j hij
  by_contra hne
  have hij' : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
  by_cases h1 : (i, j) ∈ P
  · have a1 : blockLabel P j = i := blockLabel_snd hJ h1
    have a2 : blockLabel P i = i := blockLabel_of_not (hJ.not_snd_of_fst h1)
    rw [a1, a2] at hij; exact lt_irrefl _ hij
  by_cases h2 : (j, i) ∈ P
  · have a1 : blockLabel P i = j := blockLabel_snd hJ h2
    have a2 : blockLabel P j = j := blockLabel_of_not (hJ.not_snd_of_fst h2)
    rw [a1, a2] at hij; exact lt_irrefl _ hij
  exact hne (hJ.hessian_eq_zero hij' h1 h2)

/-- **The determinant of one block**, as a product over the coordinates of the block: $2c_{aa}$ for an unpaired $a$,
$4ac - b^2$ for a pair with first coordinate $a$, and $1$ (empty block) for a second coordinate. -/
theorem det_toSquareBlock (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) {t : ℕ} {v : R} (hv : IsUnit v)
    (ht : 2 = π ^ t * v) {μ : Fin n → ℕ} (hμ : IsScaleExp Q π P μ) (a : Fin n) :
    ∃ u, IsUnit u ∧ (Q.hessian.toSquareBlock (blockLabel P) a).det =
      (∏ i : {i // blockLabel P i = a}, π ^ detBlockExp P w μ t i.1) * u := by
  classical
  by_cases ha : IsPaired P a
  · obtain ⟨e, he, ha | ha⟩ := ha
    · subst ha
      have hne : e.1 ≠ e.2 := (hJ.2.1 e he).ne
      let f : Fin 2 → {i // blockLabel P i = e.1} :=
        ![⟨e.1, (blockLabel_eq_fst hJ he _).2 (Or.inl rfl)⟩, ⟨e.2, (blockLabel_eq_fst hJ he _).2 (Or.inr rfl)⟩]
      have hf : Function.Bijective f := by
        refine ⟨fun j j' h => ?_, fun s => ?_⟩
        · fin_cases j <;> fin_cases j' <;> simp_all [f, Subtype.ext_iff, hne.symm]
        · rcases (blockLabel_eq_fst hJ he s.1).1 s.2 with h | h
          · exact ⟨0, Subtype.ext h.symm⟩
          · exact ⟨1, Subtype.ext h.symm⟩
      set E := Equiv.ofBijective f hf
      obtain ⟨δ, hδ, hdet⟩ := (hJ.pairBlock hπ hμ he).1
      refine ⟨δ, hδ, ?_⟩
      rw [← Matrix.det_reindex_self E.symm, Matrix.det_fin_two,
        ← Fintype.prod_equiv E (fun j => π ^ detBlockExp P w μ t (E j).1) _ (fun _ => rfl), Fin.prod_univ_two]
      simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
        E, Equiv.ofBijective_apply, f, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hessian_diag_apply, hessian_diag_apply, hJ.hessian_fst_snd he, hJ.hessian_snd_fst he,
        detBlockExp, detBlockExp, if_pos ⟨e, he, Or.inl rfl⟩, if_pos ⟨e, he, Or.inr rfl⟩, ← (hμ e he).1,
        ← pow_add, ← two_mul, ← hdet]
      ring
    · subst ha
      have : IsEmpty {i // blockLabel P i = e.2} := ⟨fun s => blockLabel_ne_snd hJ he s.1 s.2⟩
      exact ⟨1, isUnit_one, by rw [Matrix.det_isEmpty, Finset.univ_eq_empty, Finset.prod_empty, one_mul]⟩
  · let f : Fin 1 → {i // blockLabel P i = a} := fun _ => ⟨a, blockLabel_unpaired ha⟩
    have hf : Function.Bijective f :=
      ⟨fun j j' _ => Subsingleton.elim j j',
        fun s => ⟨0, Subtype.ext ((blockLabel_eq_unpaired hJ ha s.1).1 s.2).symm⟩⟩
    set E := Equiv.ofBijective f hf
    obtain ⟨u, hu, hu1⟩ := hJ.2.2.2.2.2 a ha
    refine ⟨v * u, hv.mul hu1, ?_⟩
    rw [← Matrix.det_reindex_self E.symm, Matrix.det_fin_one,
      ← Fintype.prod_equiv E (fun j => π ^ detBlockExp P w μ t (E j).1) _ (fun _ => rfl),
      Fin.prod_univ_one]
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
      E, Equiv.ofBijective_apply, f, Matrix.of_apply]
    rw [hessian_diag_apply, detBlockExp, if_neg ha, hu, ht, pow_add]
    ring

/-- **(2.4), corrected, for a general normal form** (Hanke 2004, (2.4), p. 356, every prime): for $Q$ in the normal form
`IsJordanFormW Q π P w` with scale exponents $\mu$ and $2 = \pi^t v$ ($v$ a unit),
$\det H = \pi^{\sum_i \lambda'_i}\cdot$ unit, i.e. $\mathrm{ord}_\pi D_{2Q} = \sum_i \lambda'_i$ with $\lambda'_i = w_i + t$ on
1-dimensional blocks and $\lambda'_i = \mu_j$ on each coordinate of a 2-dimensional block (`detBlockExp`), so the block
contributes $2\mu_j$. -/
@[kb "hanke2004" "(2.4), p. 356 (general normal form, corrected)"]
theorem det_hessian_jordanW (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) {t : ℕ} {v : R} (hv : IsUnit v)
    (ht : 2 = π ^ t * v) {μ : Fin n → ℕ} (hμ : IsScaleExp Q π P μ) :
    ∃ u, IsUnit u ∧ Q.hessian.det = π ^ (∑ i, detBlockExp P w μ t i) * u := by
  classical
  choose u hu hdet using det_toSquareBlock hJ hπ hv ht hμ
  refine ⟨∏ a, u a, IsUnit.prod_univ_iff.2 hu, ?_⟩
  rw [hJ.blockTriangular.det_fintype, Finset.prod_congr rfl fun a _ => hdet a, Finset.prod_mul_distrib,
    Fintype.prod_fiberwise (blockLabel P) (fun i => π ^ detBlockExp P w μ t i), Finset.prod_pow_eq_pow_sum]

end Det

/-! ### Domain of validity of the printed (2.4)/(2.5), and general $Q$ -/

section Corollaries

variable {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {w : Fin n → ℕ}

/-- **If $\pi^2 \nmid 2$, every binary block has $\mu = w$** (scale exponent = norm exponent): $w \le \mu \le w + \mathrm{ord}_\pi 2
\le w + 1$, and $\mu = w + 1$ would make $\pi^{w+1}$ divide $a$, $b$ and $c$ ($\pi^{w+2} \mid 2a$ with $2 \mid \pi\cdot$unit),
contradicting exactness. This covers all primes of $\mathbb Q$, all unramified dyadic primes and all non-dyadic primes. -/
theorem scale_eq_norm_of_not_sq_dvd_two (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) (h2 : ¬ π ^ 2 ∣ 2)
    {μ : Fin n → ℕ} (hμ : IsScaleExp Q π P μ) {e : Fin n × Fin n} (he : e ∈ P) : μ e.1 = w e.1 := by
  obtain ⟨-, ha, hc, hex, μ0, β0, hb0, hβ0, hwμ, h2a, h2c, h2w⟩ := hJ.2.2.2.2.1 e he
  obtain ⟨-, β, hb, hβ⟩ := hμ e he
  have h0 : μ0 = μ e.1 := pow_mul_unit_inj hπ hβ0 hβ (hb0.symm.trans hb)
  rw [← h0]
  by_contra hne
  have hlt : w e.1 < μ0 := lt_of_le_of_ne hwμ (Ne.symm hne)
  -- $\pi^{\mu_0} \mid 2\pi^w$ forces $\mu_0 = w + 1$ and $2 = \pi\cdot$unit
  have hπ2 : π ∣ 2 := by
    have : π ^ (w e.1 + 1) ∣ 2 * π ^ w e.1 := (pow_dvd_pow π hlt).trans h2w
    rw [pow_succ, mul_comm 2] at this
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 this
  obtain ⟨s, hs⟩ := hπ2
  have hsu : IsUnit s := dvr_isUnit_of_not_dvd hπ fun hd => h2 (by
    obtain ⟨r, hr⟩ := hd; exact ⟨r, by rw [hs, hr]; ring⟩)
  have hμ0 : μ0 = w e.1 + 1 := by
    have h' : π ^ μ0 ∣ π ^ (w e.1 + 1) * s := by rw [pow_succ, mul_assoc, ← hs, mul_comm]; exact h2w
    rw [hsu.dvd_mul_right, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h'
    omega
  subst hμ0
  have key : ∀ x : R, π ^ (w e.1 + 1 + 1) ∣ 2 * x → π ^ (w e.1 + 1) ∣ x := by
    intro x hx
    rw [hs, pow_succ, mul_assoc, mul_comm (π ^ (w e.1 + 1)) π] at hx
    exact hsu.dvd_mul_left.1 ((mul_dvd_mul_iff_left hπ.ne_zero).1 hx)
  exact hex ⟨key _ h2a, by rw [hb0]; exact dvd_mul_right _ _, key _ h2c⟩

/-- The scale exponents may be taken equal to the norm exponents when $\pi^2 \nmid 2$. -/
theorem isScaleExp_self_of_not_sq_dvd_two (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π)
    (h2 : ¬ π ^ 2 ∣ 2) : IsScaleExp Q π P w := by
  obtain ⟨μ, hμ⟩ := exists_isScaleExp hJ
  intro e he
  obtain ⟨-, β, hb, hβ⟩ := hμ e he
  refine ⟨(hJ.2.2.2.2.1 e he).1, β, ?_, hβ⟩
  rw [hb, scale_eq_norm_of_not_sq_dvd_two hJ hπ h2 hμ he]

theorem levelBlockExp_self (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (t : ℕ) (i : Fin n) :
    levelBlockExp P w w t i = (open Classical in if IsPaired P i then w i else w i + 2 * t) := by
  unfold levelBlockExp; split_ifs <;> omega

/-- **(2.4) and (2.5) where the printed values hold** (Hanke 2004, p. 356; $\pi^2 \nmid 2$: every prime of $\mathbb Q$, every
unramified dyadic and every non-dyadic prime): for $Q$ in the normal form `IsJordanFormW Q π P w` and
$2 = \pi^t v$, $\mathrm{ord}_\pi N = \max_i \lambda''_i$ with $\lambda''_i = w_i$ on 2-dimensional blocks and $w_i + 2t$ on
1-dimensional blocks (**as printed**), and $\mathrm{ord}_\pi \det H = \sum_i \lambda'_i$ with $\lambda'_i = w_i + t$ on
1-dimensional blocks (as printed) and $\lambda'_i = w_i$ on each coordinate of a 2-dimensional block, i.e. $2w_j$ per
block (*erratum:* printed $\nu_j$; `docs/updates-and-errata.md`). -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (p² ∤ 2, corrected (2.4))"]
theorem eq_2_4_2_5_of_not_sq_dvd_two (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) (h2 : ¬ π ^ 2 ∣ 2)
    (h20 : (2 : R) ≠ 0) {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v) :
    (∃ u, IsUnit u ∧ Q.hessian.det = π ^ (∑ i, detBlockExp P w w t i) * u) ∧
      levelExp Q π = Finset.univ.sup fun i => (open Classical in if IsPaired P i then w i else w i + 2 * t) := by
  have hμ := isScaleExp_self_of_not_sq_dvd_two hJ hπ h2
  refine ⟨det_hessian_jordanW hJ hπ hv ht hμ, ?_⟩
  rw [levelExp_jordanW hJ hπ h20 hv ht hμ]
  congr 1; funext i; exact levelBlockExp_self P w t i

/-- **(2.4) and (2.5) for Hanke's printed normal form** `IsJordanForm` (2-dimensional blocks $\pi^\nu(\alpha x^2 + \beta xy +
\gamma y^2)$ with $\beta$ a unit; it exists whenever $\pi^2 \nmid 2$, `exists_jordanForm`), at every prime: $\mu = w = \nu$, so
$\lambda''_j = \nu_j$ (as printed) and $\lambda'_j = 2\nu_j$ (corrected) on 2-dimensional blocks, $\lambda''_j = \nu_j + 2t$,
$\lambda'_j = \nu_j + t$ on 1-dimensional ones. Multi-block form of `binForm_normal`, `levelExp_diag`, `det_hessian_diag_exp`. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (Hanke's normal form, corrected (2.4))"]
theorem eq_2_4_2_5_hankeNormal {ν : Fin n → ℕ} (hJ : IsJordanForm Q π P ν) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v) :
    (∃ u, IsUnit u ∧ Q.hessian.det = π ^ (∑ i, detBlockExp P ν ν t i) * u) ∧
      levelExp Q π = Finset.univ.sup fun i => (open Classical in if IsPaired P i then ν i else ν i + 2 * t) := by
  have hW := hJ.toW hπ
  have hμ : IsScaleExp Q π P ν := fun e he => by
    obtain ⟨h1, ⟨b, hb, hbu⟩, -⟩ := hJ.2.2.2.2.1 e he
    exact ⟨h1, b, hb, hbu⟩
  refine ⟨det_hessian_jordanW hW hπ hv ht hμ, ?_⟩
  rw [levelExp_jordanW hW hπ h20 hv ht hμ]
  congr 1; funext i; exact levelBlockExp_self P ν t i

/-- **(2.4) and (2.5) verbatim at a non-dyadic prime**, for the general normal form (no 2-dimensional blocks):
$\det H = \pi^{\sum_i w_i}\cdot$unit and $\mathrm{ord}_\pi N = \max_i w_i$ (`eq_2_4_2_5_nondyadic` for `IsJordanForm`). -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (p ∤ 2)"]
theorem eq_2_4_2_5_nondyadic_W (hJ : IsJordanFormW Q π P w) (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    (∃ u, IsUnit u ∧ Q.hessian.det = π ^ (∑ i, w i) * u) ∧ levelExp Q π = Finset.univ.sup w := by
  classical
  have hP : P = ∅ := by
    by_contra h; exact h2 (hJ.1 (Finset.nonempty_iff_ne_empty.2 h))
  have hunp : ∀ i, ¬ IsPaired P i := fun i ⟨e, he, _⟩ => by rw [hP] at he; simp at he
  have h2u := dvr_isUnit_of_not_dvd hπ h2
  have ht : (2 : R) = π ^ 0 * 2 := by ring
  have h20 : (2 : R) ≠ 0 := h2u.ne_zero
  have hμ : IsScaleExp Q π P w := fun e he => by rw [hP] at he; simp at he
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu, h⟩ := det_hessian_jordanW hJ hπ h2u ht hμ
    refine ⟨u, hu, ?_⟩
    rw [h]; congr 2; exact Finset.sum_congr rfl fun i _ => by simp [detBlockExp, hunp i]
  · rw [levelExp_jordanW hJ hπ h20 h2u ht hμ]
    congr 1; funext i; rw [levelBlockExp, if_neg (hunp i)]; simp

/-- **(2.4) and (2.5), corrected, for every nondegenerate $Q$** (Hanke 2004, Lemma 2.1 corrected + (2.4), (2.5), p. 356,
every prime, $2 \ne 0$, $2 = \pi^t v$): $Q$ is $\mathrm{GL}_n(R)$-equivalent to a normal form `IsJordanFormW Q' π P w` with
scale exponents $\mu$, and $\mathrm{ord}_\pi \det H_Q = \sum_i \lambda'_i$, $\mathrm{ord}_\pi N_Q = \max_i \lambda''_i$. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (general Q, corrected)"]
theorem eq_2_4_2_5_general (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0)
    {t : ℕ} {v : R} (hv : IsUnit v) (ht : 2 = π ^ t * v) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (w μ : Fin n → ℕ),
      IsJordanFormW Q' π P w ∧ IsScaleExp Q' π P μ ∧ IsGLEquiv Q Q' ∧
      (∃ u, IsUnit u ∧ Q.hessian.det = π ^ (∑ i, detBlockExp P w μ t i) * u) ∧
      levelExp Q π = Finset.univ.sup (levelBlockExp P w μ t) := by
  obtain ⟨Q', P, w, hJ, -, hE⟩ := exists_jordanFormW_isGLEquiv Q hQ π hπ h20
  obtain ⟨μ, hμ⟩ := exists_isScaleExp hJ
  refine ⟨Q', P, w, μ, hJ, hμ, hE, ?_, by rw [levelExp_eq_of_isGLEquiv hE, levelExp_jordanW hJ hπ h20 hv ht hμ]⟩
  obtain ⟨u, hu, hdet⟩ := det_hessian_jordanW hJ hπ hv ht hμ
  obtain ⟨s, hs, hds⟩ := hE.det_hessian
  refine ⟨u * ((hs.unit⁻¹ : Rˣ) : R) ^ 2, hu.mul ((Units.isUnit _).pow 2), ?_⟩
  have : Q.hessian.det = ((hs.unit⁻¹ : Rˣ) : R) ^ 2 * (s ^ 2 * Q.hessian.det) := by
    rw [← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
  rw [this, ← hds, hdet]; ring

/-- **The ramified dyadic counterexample, recovered** (`lemma_2_2_ramified_counterexample`): for $\pi^2 \mid 2$,
$x^2 + \pi xy + y^2$ has one binary block with $w = 0$, $\mu = 1$, so $\mathrm{ord}_\pi N = 2\mu - w = 2$ and
$\mathrm{ord}_\pi \det H = 2\mu = 2$. -/
theorem ramified_example_exps (hπ : Irreducible π) (h2 : π ^ 2 ∣ 2) (h20 : (2 : R) ≠ 0) {t : ℕ} {v : R}
    (hv : IsUnit v) (ht : 2 = π ^ t * v) :
    levelExp (binForm 1 π 1) π = 2 ∧
      ∃ u, IsUnit u ∧ (binForm 1 π 1).hessian.det = π ^ 2 * u := by
  classical
  have hJ := (lemma_2_2_ramified_counterexample hπ h2 h20).1
  have hμ : IsScaleExp (binForm 1 π 1) π {((0 : Fin 2), (1 : Fin 2))} (fun _ => 1) := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨rfl, 1, by simp [binForm], isUnit_one⟩
  have hp : ∀ i : Fin 2, IsPaired {((0 : Fin 2), (1 : Fin 2))} i := fun i =>
    ⟨(0, 1), by simp, by fin_cases i <;> simp⟩
  refine ⟨?_, ?_⟩
  · have : levelBlockExp {((0 : Fin 2), (1 : Fin 2))} 0 (fun _ => 1) t = fun _ => 2 := by
      funext i; rw [levelBlockExp, if_pos (hp i)]; rfl
    rw [levelExp_jordanW hJ hπ h20 hv ht hμ, this, Finset.sup_const Finset.univ_nonempty]
  · obtain ⟨u, hu, h⟩ := det_hessian_jordanW hJ hπ hv ht hμ
    have : detBlockExp {((0 : Fin 2), (1 : Fin 2))} 0 (fun _ => 1) t = fun _ => 1 := by
      funext i; rw [detBlockExp, if_pos (hp i)]
    refine ⟨u, hu, ?_⟩
    rw [h, this]; simp

end Corollaries

end QuadFormsKB.LocalDensity.DVR
