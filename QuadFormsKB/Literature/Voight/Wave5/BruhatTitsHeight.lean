/-
# The Bruhat–Tits tree is a tree; distances (Voight, Proposition 23.5.8, Lemma 23.5.15)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 23.5.8 (p. 387),
23.5.14 and Lemma 23.5.15 (p. 389).

**Setting.** As in `Wave5/BruhatTits.lean`: $R$ a discrete valuation ring with fraction field $F$ (`K`) and uniformizer
$\pi$; vertices are homothety classes of $R$-lattices in $F^2$.

**Method** (not the book's: the book proves acyclicity by the Dasgupta–Teitelbaum argument). Every vertex is
$[A R^2]$ for an integral matrix $A$ that is *primitive* (some entry is a unit) with $\det A \ne 0$; the *height*
$h([AR^2]) = v(\det A)$ is well defined (`height`). Every neighbour of $[AR^2]$ is $[AWD_1R^2]$ with $W \in \mathrm{GL}_2(R)$,
$D_1 = \operatorname{diag}(1, \pi)$ (`exists_nbr_eq`), and writing $A = U\operatorname{diag}(1,\pi^d)V$ one finds that
all neighbours have height $d + 1$ except exactly one, $[U\operatorname{diag}(1, \pi^{d-1})R^2]$ when $d \ge 1$
(`height_nbr`). The height criterion `isAcyclic_of_height` then gives acyclicity, and `le_dist_of_height` gives the
distance.

**Contents.**
* `bruhatTits_isTree` (Proposition 23.5.8, tree part): $\mathcal T$ is a tree.
* `dist_base_eq_height`: $d([R^2], x) = h(x)$.
* `dist_diag` (Lemma 23.5.15, distance): $d([PR^2], [P\operatorname{diag}(1,\pi^e)R^2]) = e$, i.e. for $L$ with basis
  $x_0, x_1$ and $L'$ with basis $\pi^f x_0, \pi^{e+f}x_1$, $d([L],[L']) = e$.
-/
import QuadFormsKB.Literature.Voight.Wave5.BruhatTits
import QuadFormsKB.Literature.Voight.Wave5.GraphHeight

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

open Matrix Pointwise

noncomputable section

namespace QuadFormsKB.Voight.Wave8

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  IsLocalization IsDiscreteValuationRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-! ### Integral matrices: primitivity and the valuation of the determinant -/

/-- An integral matrix is **primitive** if some entry is a unit. -/
def IsPrim (A : Matrix (Fin 2) (Fin 2) R) : Prop := ∃ i j, IsUnit (A i j)

/-- The valuation of the determinant, $v(\det A) \in \mathbb N$ (zero if $\det A = 0$). -/
def vdet (A : Matrix (Fin 2) (Fin 2) R) : ℕ := (addVal R A.det).toNat

theorem vdet_of_isUnit {A : Matrix (Fin 2) (Fin 2) R} (h : IsUnit A.det) : vdet A = 0 := by
  obtain ⟨u, hu⟩ := h
  rw [vdet, ← hu, addVal_eq_zero_of_unit]; rfl

theorem vdet_mul {A B : Matrix (Fin 2) (Fin 2) R} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    vdet (A * B) = vdet A + vdet B := by
  rw [vdet, vdet, vdet, Matrix.det_mul, addVal_mul]
  have h1 : addVal R A.det ≠ ⊤ := fun h => hA (addVal_eq_top_iff.1 h)
  have h2 : addVal R B.det ≠ ⊤ := fun h => hB (addVal_eq_top_iff.1 h)
  exact ENat.toNat_add h1 h2

theorem det_diagR (π : R) (e : ℕ) : (diagR π e).det = π ^ e := by
  simp [Matrix.det_fin_two_of]

theorem vdet_diagR {π : R} (hπ : Irreducible π) (e : ℕ) : vdet (diagR π e) = e := by
  rw [vdet, det_diagR, addVal_pow, addVal_uniformizer hπ]; simp

theorem det_ne_zero_of_isUnit {A : Matrix (Fin 2) (Fin 2) R} (h : IsUnit A.det) : A.det ≠ 0 := h.ne_zero

theorem diagR_det_ne_zero {π : R} (hπ : Irreducible π) (e : ℕ) : (diagR π e).det ≠ 0 := by
  rw [det_diagR]; exact pow_ne_zero _ hπ.ne_zero

/-- $\operatorname{vdet}(U\operatorname{diag}(1,\pi^d)V) = d$ for $U, V \in \mathrm{GL}_2(R)$. -/
theorem vdet_cartan {π : R} (hπ : Irreducible π) {U V : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hV : IsUnit V.det) (d : ℕ) : vdet (U * diagR π d * V) = d := by
  have h1 : (U * diagR π d).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hU.ne_zero (diagR_det_ne_zero hπ d)
  rw [vdet_mul h1 hV.ne_zero, vdet_mul hU.ne_zero (diagR_det_ne_zero hπ d), vdet_of_isUnit hU,
    vdet_of_isUnit hV, vdet_diagR hπ]
  ring

theorem isUnit_det_of_mul_eq_one {U U' : Matrix (Fin 2) (Fin 2) R} (h : U * U' = 1) : IsUnit U.det :=
  IsUnit.of_mul_eq_one U'.det (by rw [← Matrix.det_mul, h, Matrix.det_one])

/-- Left multiplication by $U \in \mathrm{GL}_2(R)$ preserves primitivity. -/
theorem IsPrim.mul_left {A U : Matrix (Fin 2) (Fin 2) R} (hA : IsPrim A) (hU : IsUnit U.det) : IsPrim (U * A) := by
  by_contra hn
  obtain ⟨i, j, hij⟩ := hA
  have hall : ∀ k l, (U * A) k l ∈ IsLocalRing.maximalIdeal R := fun k l =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu => hn ⟨k, l, hu⟩
  have hA' : A = U⁻¹ * (U * A) := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hU, one_mul]
  have : A i j ∈ IsLocalRing.maximalIdeal R := by
    rw [hA', Matrix.mul_apply, Fin.sum_univ_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hall 0 j)) (Ideal.mul_mem_left _ _ (hall 1 j))
  exact (IsLocalRing.mem_maximalIdeal _).1 this hij

/-- Right multiplication by $V \in \mathrm{GL}_2(R)$ preserves primitivity. -/
theorem IsPrim.mul_right {A V : Matrix (Fin 2) (Fin 2) R} (hA : IsPrim A) (hV : IsUnit V.det) : IsPrim (A * V) := by
  by_contra hn
  obtain ⟨i, j, hij⟩ := hA
  have hall : ∀ k l, (A * V) k l ∈ IsLocalRing.maximalIdeal R := fun k l =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu => hn ⟨k, l, hu⟩
  have hA' : A = (A * V) * V⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hV, mul_one]
  have : A i j ∈ IsLocalRing.maximalIdeal R := by
    rw [hA', Matrix.mul_apply, Fin.sum_univ_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hall i 0)) (Ideal.mul_mem_right _ _ (hall i 1))
  exact (IsLocalRing.mem_maximalIdeal _).1 this hij

/-- A matrix of $\mathrm{GL}_2(R)$ is primitive. -/
theorem isPrim_of_isUnit {T : Matrix (Fin 2) (Fin 2) R} (hT : IsUnit T.det) : IsPrim T := by
  have h1 : IsPrim (1 : Matrix (Fin 2) (Fin 2) R) := ⟨0, 0, by simp⟩
  simpa using h1.mul_left hT

/-- $\operatorname{diag}(1,\pi^e)$ is primitive. -/
theorem isPrim_diagR (π : R) (e : ℕ) : IsPrim (diagR π e) := ⟨0, 0, by simp⟩

/-! ### Column lattices of integral matrices -/

theorem mapR_injective : Function.Injective (mapR (R := R) (K := K)) := by
  intro A B h
  ext i j
  exact IsFractionRing.injective R K (congrFun (congrFun h i) j)

theorem det_mapR (A : Matrix (Fin 2) (Fin 2) R) : (mapR (K := K) A).det = algebraMap R K A.det := by
  rw [mapR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem det_mapR_ne_zero {A : Matrix (Fin 2) (Fin 2) R} (h : A.det ≠ 0) : (mapR (K := K) A).det ≠ 0 := by
  rw [det_mapR]; exact algebraMap_ne_zero h

theorem exists_eq_mapR {M : Matrix (Fin 2) (Fin 2) K} (h : M ∈ matOrder R K) :
    ∃ A : Matrix (Fin 2) (Fin 2) R, M = mapR A := by
  rw [mem_matOrder] at h
  choose B hB using h
  exact ⟨Matrix.of B, by ext i j; simp [mapR, hB i j]⟩

/-- The lattice $AR^2$ of an integral matrix with $\det A \ne 0$. -/
def latR {A : Matrix (Fin 2) (Fin 2) R} (h : A.det ≠ 0) : Lat R K :=
  latOf (R := R) (Matrix.mul_nonsing_inv (mapR (K := K) A) (isUnit_iff_ne_zero.2 (det_mapR_ne_zero h)))

theorem latR_val {A : Matrix (Fin 2) (Fin 2) R} (h : A.det ≠ 0) : (latR (K := K) h).1 = colLat R (mapR A) := rfl

/-- Two integral matrices with the same column lattice differ by $\mathrm{GL}_2(R)$ on the right. -/
theorem exists_eq_mul_of_colLat_eq {A A' : Matrix (Fin 2) (Fin 2) R} (hA : A.det ≠ 0) (hA' : A'.det ≠ 0)
    (h : colLat R (mapR (K := K) A') = colLat R (mapR A)) : ∃ W, IsUnit W.det ∧ A' = A * W := by
  set X := mapR (K := K) A
  set X' := mapR (K := K) A'
  have hX := isUnit_iff_ne_zero.2 (det_mapR_ne_zero (K := K) hA)
  have hX' := isUnit_iff_ne_zero.2 (det_mapR_ne_zero (K := K) hA')
  have h1 := (colLat_le_colLat_iff (R := R) (Matrix.mul_nonsing_inv X hX) (Matrix.nonsing_inv_mul X hX)).1 h.le
  have h2 := (colLat_le_colLat_iff (R := R) (Matrix.mul_nonsing_inv X' hX') (Matrix.nonsing_inv_mul X' hX')).1 h.ge
  obtain ⟨W, hW⟩ := exists_eq_mapR h1
  obtain ⟨W', hW'⟩ := exists_eq_mapR h2
  have hWW : W * W' = 1 := by
    apply mapR_injective (K := K)
    rw [mapR_mul, ← hW, ← hW', mapR_one, mul_assoc, ← mul_assoc X', Matrix.mul_nonsing_inv X' hX', one_mul,
      Matrix.nonsing_inv_mul X hX]
  refine ⟨W, isUnit_det_of_mul_eq_one hWW, mapR_injective (K := K) ?_⟩
  rw [mapR_mul, ← hW, ← mul_assoc, Matrix.mul_nonsing_inv X hX, one_mul]

/-- **Uniqueness of primitive representatives**: if $A, A'$ are primitive with nonzero determinant and
$A'R^2 = c\,AR^2$, then $v(\det A') = v(\det A)$. -/
theorem vdet_eq_of_colLat_eq {π : R} (hπ : Irreducible π) {A A' : Matrix (Fin 2) (Fin 2) R} (hA : IsPrim A)
    (hA' : IsPrim A') (hdA : A.det ≠ 0) (hdA' : A'.det ≠ 0) {c : K} (hc : c ≠ 0)
    (h : colLat R (mapR (K := K) A') = c • colLat R (mapR A)) : vdet A' = vdet A := by
  -- one-sided version: `c = u π^k` with `k ≥ 0`
  have key : ∀ (A A' : Matrix (Fin 2) (Fin 2) R), IsPrim A' → A.det ≠ 0 → A'.det ≠ 0 → ∀ (u : Rˣ) (k : ℕ),
      colLat R (mapR (K := K) A') = (algebraMap R K u * algebraMap R K π ^ k) • colLat R (mapR A) →
      vdet A' = vdet A := by
    intro A A' hA' hdA hdA' u k h
    have hdA2 : (((u : R) * π ^ k) • A).det ≠ 0 := by
      rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hπ.ne_zero))) hdA
    have h' : colLat R (mapR (K := K) A') = colLat R (mapR (((u : R) * π ^ k) • A)) := by
      rw [h, smul_colLat]
      congr 1; ext i j; simp [mapR, Matrix.smul_apply]
    obtain ⟨W, hW, hAW⟩ := exists_eq_mul_of_colLat_eq hdA2 hdA' h'
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have e1 : A' = A * ((u : R) • W) := by rw [hAW, pow_zero, mul_one, Matrix.smul_mul, Matrix.mul_smul]
      have hu2 : IsUnit ((u : R) • W).det := by
        rw [Matrix.det_smul]; exact (u.isUnit.pow _).mul hW
      rw [e1, vdet_mul hdA hu2.ne_zero, vdet_of_isUnit hu2, add_zero]
    · exfalso
      obtain ⟨i, j, hij⟩ := hA'
      rw [hAW, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at hij
      have : π ∣ (u : R) * π ^ k * (A * W) i j :=
        Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self π hk.ne') _) _
      exact hπ.not_isUnit (isUnit_of_dvd_unit this hij)
  obtain ⟨u, k, rfl⟩ := exists_unit_zpow hπ hc
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    exact key A A' hA' hdA hdA' u k (by simpa using h)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -n := ⟨(-k).toNat, by omega⟩
    have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
    have huK : algebraMap R K (u : R) ≠ 0 := algebraMap_ne_zero u.ne_zero
    refine (key A' A hA hdA' hdA u⁻¹ n ?_).symm
    rw [h, smul_smul]
    have : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K π ^ n *
        (algebraMap R K (u : R) * algebraMap R K π ^ (-(n : ℤ))) = 1 := by
      have hu : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [_root_.zpow_neg, zpow_natCast]
      field_simp
      linear_combination hu
    rw [this, one_smul]

/-! ### The height of a vertex -/

/-- Every lattice is $c\,AR^2$ with $A$ integral, primitive, $\det A \ne 0$. -/
theorem exists_primRep {π : R} (hπ : Irreducible π) (L : Lat R K) :
    ∃ (c : K) (A : Matrix (Fin 2) (Fin 2) R), c ≠ 0 ∧ IsPrim A ∧ A.det ≠ 0 ∧ L.1 = c • colLat R (mapR A) := by
  obtain ⟨P, Q, hPQ, -, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
  have hdetP : P.det ≠ 0 := by
    intro h0; have := congrArg Matrix.det hPQ; rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨c, A0, hc, rfl⟩ := exists_eq_smul_mapR (R := R) P
  have hA0 : A0 ≠ 0 := by rintro rfl; apply hdetP; simp [mapR]
  obtain ⟨n, A, rfl, hunit⟩ := exists_eq_pow_smul_isUnit hπ A0 hA0
  have hmap : mapR (K := K) (π ^ n • A) = algebraMap R K (π ^ n) • mapR A := by
    ext i j; simp [mapR, Matrix.smul_apply]
  refine ⟨c * algebraMap R K (π ^ n), A, mul_ne_zero hc (algebraMap_ne_zero (pow_ne_zero _ hπ.ne_zero)), hunit,
    ?_, ?_⟩
  · intro h0; apply hdetP
    rw [hmap, smul_smul, Matrix.det_smul, det_mapR, h0, map_zero, mul_zero]
  · rw [hP, hmap, smul_smul, smul_colLat]

variable (R K) in
/-- The height of a lattice: $v(\det A)$ for a primitive representative $c\,AR^2$. -/
def latHeight (π : R) (hπ : Irreducible π) (L : Lat R K) : ℕ := vdet (exists_primRep hπ L).choose_spec.choose

theorem latHeight_eq {π : R} (hπ : Irreducible π) (L : Lat R K) {c : K} {A : Matrix (Fin 2) (Fin 2) R}
    (hc : c ≠ 0) (hA : IsPrim A) (hdA : A.det ≠ 0) (h : L.1 = c • colLat R (mapR A)) :
    latHeight R K π hπ L = vdet A := by
  obtain ⟨hc', hA', hdA', h'⟩ := (exists_primRep hπ L).choose_spec.choose_spec
  rw [latHeight]
  apply vdet_eq_of_colLat_eq hπ hA hA' hdA hdA' (c := (exists_primRep hπ L).choose⁻¹ * c) (mul_ne_zero
    (inv_ne_zero hc') hc)
  calc _ = (exists_primRep hπ L).choose⁻¹ • ((exists_primRep hπ L).choose •
        colLat R (mapR (exists_primRep hπ L).choose_spec.choose)) := by
          rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
    _ = (exists_primRep hπ L).choose⁻¹ • L.1 := by rw [← h']
    _ = (exists_primRep hπ L).choose⁻¹ • (c • colLat R (mapR A)) := congrArg _ h
    _ = _ := by rw [smul_smul]

variable (R K) in
/-- **The height** $h([L])$ of a vertex: $v(\det A)$ for a primitive integral $A$ with $[L] = [AR^2]$. -/
def height (π : R) (hπ : Irreducible π) : Vert R K → ℕ :=
  Quotient.lift (latHeight R K π hπ) (by
    rintro L L' ⟨a, ha, h⟩
    obtain ⟨c, A, hc, hA, hdA, hL⟩ := exists_primRep hπ L
    rw [latHeight_eq hπ L hc hA hdA hL, latHeight_eq hπ L' (mul_ne_zero ha hc) hA hdA (by rw [h, hL, smul_smul])])

theorem height_latR {π : R} (hπ : Irreducible π) {A : Matrix (Fin 2) (Fin 2) R} (hA : IsPrim A) (hdA : A.det ≠ 0) :
    height R K π hπ (latR (K := K) hdA).cls = vdet A :=
  latHeight_eq hπ _ one_ne_zero hA hdA (by rw [one_smul]; rfl)

/-! ### Neighbours -/

/-- Diagonal column lattices with powers of $\pi$: $Y\operatorname{diag}(\pi^{a_0},\pi^{a_1})R^2 \subseteq
Y\operatorname{diag}(\pi^{b_0},\pi^{b_1})R^2$ iff $b_i \le a_i$. -/
theorem colLat_zpow_le_iff {π : R} (hπ : Irreducible π) {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : Y * Y' = 1)
    (hY' : Y' * Y = 1) (a b : Fin 2 → ℤ) :
    colLat R (Y * Matrix.diagonal (fun i => algebraMap R K π ^ a i)) ≤
        colLat R (Y * Matrix.diagonal (fun i => algebraMap R K π ^ b i)) ↔ ∀ i, b i ≤ a i := by
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  rw [colLat_mul_diagonal_le_iff hY hY' (fun i => zpow_ne_zero _ hπK)]
  refine forall_congr' fun i => ?_
  rw [← zpow_sub₀ hπK, isInteger_zpow_iff hπ]
  omega

theorem diagonal_zpow_zero (π : R) :
    Matrix.diagonal (fun _ : Fin 2 => algebraMap R K π ^ (0 : ℤ)) = 1 := by
  simp

/-- Strict inclusion is preserved by scaling with $a \ne 0$. -/
theorem smul_lt_smul_of_lt {a : K} (ha : a ≠ 0) {L M : Submodule R (Fin 2 → K)} (h : L < M) : a • L < a • M := by
  refine lt_of_le_not_ge (smul_submodule_mono a h.le) fun h' => h.not_ge ?_
  have := smul_submodule_mono a⁻¹ h'
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul, one_smul] at this

/-- A scaled lattice, as an element of `Lat R K`. -/
def Lat.scale {a : K} (ha : a ≠ 0) (L : Lat R K) : Lat R K :=
  ⟨a • L.1, by
    obtain ⟨P, Q, hPQ, -, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
    rw [hP, smul_colLat]
    exact isLattice_colLat (Q := a⁻¹ • Q) (by rw [Matrix.smul_mul, Matrix.mul_smul, hPQ, smul_smul,
      mul_inv_cancel₀ ha, one_smul])⟩

theorem Lat.scale_cls {a : K} (ha : a ≠ 0) (L : Lat R K) : (L.scale ha).cls = L.cls :=
  (Quotient.sound (s := homothety R K) (show Homothetic L.1 (a • L.1) from ⟨a, ha, rfl⟩)).symm

/-- **The sandwich lemma**: if $\pi XR^2 \subsetneq M \subsetneq XR^2$ ($X$ invertible), then
$M = XW\operatorname{diag}(1,\pi)R^2$ for some $W \in \mathrm{GL}_2(R)$. -/
theorem exists_sandwich {π : R} (hπ : Irreducible π) {X : Matrix (Fin 2) (Fin 2) K} (hX : IsUnit X.det)
    (M : Lat R K) (h1 : algebraMap R K π • colLat R X < M.1) (h2 : M.1 < colLat R X) :
    ∃ W : Matrix (Fin 2) (Fin 2) R, IsUnit W.det ∧ M.1 = colLat R (X * mapR W * diagP π 1) := by
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat M.1).1 M.2
  have hZ : (X⁻¹ * P) * (Q * X) = 1 := by
    rw [mul_assoc, ← mul_assoc P, hPQ, one_mul, Matrix.nonsing_inv_mul _ hX]
  obtain ⟨c, f, U, U', V, V', hc, hU, -, hV, -, hg⟩ := exists_eq_smul_mul_diag_mul (K := K) hπ hZ
  obtain ⟨u, k, rfl⟩ := exists_unit_zpow hπ hc
  -- `Y = X (uU)` is invertible and `XR² = YR²`
  set U₁ : Matrix (Fin 2) (Fin 2) R := (u : R) • U with hU₁
  have hU₁u : IsUnit U₁.det := by
    rw [hU₁, Matrix.det_smul]; exact (u.isUnit.pow _).mul (isUnit_det_of_mul_eq_one hU)
  set Y : Matrix (Fin 2) (Fin 2) K := X * mapR U₁ with hYdef
  set Y' : Matrix (Fin 2) (Fin 2) K := mapR U₁⁻¹ * X⁻¹ with hY'def
  have hY : Y * Y' = 1 := by
    rw [hYdef, hY'def, mul_assoc, ← mul_assoc (mapR U₁), ← mapR_mul, Matrix.mul_nonsing_inv _ hU₁u, mapR_one,
      one_mul, Matrix.mul_nonsing_inv _ hX]
  have hY' : Y' * Y = 1 := by
    rw [hYdef, hY'def, mul_assoc, ← mul_assoc X⁻¹, Matrix.nonsing_inv_mul _ hX, one_mul, ← mapR_mul,
      Matrix.nonsing_inv_mul _ hU₁u, mapR_one]
  have hXY : colLat R X = colLat R (Y * Matrix.diagonal (fun _ => algebraMap R K π ^ (0 : ℤ))) := by
    rw [diagonal_zpow_zero, mul_one, hYdef, colLat_mul_mapR (Matrix.mul_nonsing_inv _ hU₁u)]
  have hπXY : algebraMap R K π • colLat R X =
      colLat R (Y * Matrix.diagonal (fun _ => algebraMap R K π ^ (1 : ℤ))) := by
    rw [hXY, smul_colLat_mul_diagonal]; congr 3; funext i; simp
  -- `M = Y diag(π^k, π^(k+f)) R²`
  have hM : M.1 = colLat R (Y * Matrix.diagonal (fun i => algebraMap R K π ^ (![k, k + f] i))) := by
    have hP' : P = X * (X⁻¹ * P) := by rw [← mul_assoc, Matrix.mul_nonsing_inv _ hX, one_mul]
    rw [hP, hP', hg, mapR_mul, mapR_mul, mapR_diagR, Matrix.mul_smul, ← mul_assoc, ← mul_assoc,
      ← Matrix.smul_mul, colLat_mul_mapR hV]
    congr 1
    rw [hYdef, hU₁]
    ext i j
    have hm : ∀ (B : Matrix (Fin 2) (Fin 2) R), mapR (K := K) ((u : R) • B) = algebraMap R K (u : R) • mapR B := by
      intro B; ext i j; simp [mapR, Matrix.smul_apply]
    rw [hm]
    have hs : ∀ x : K, (u : R) • x = algebraMap R K (u : R) * x := fun x => Algebra.smul_def _ _
    fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, diagP, Matrix.smul_apply, zpow_add₀ hπK,
        zpow_natCast, hs] <;> ring
  rw [hM, hXY] at h2
  rw [hM, hπXY] at h1
  have c1 := (colLat_zpow_le_iff hπ hY hY' _ _).1 h2.le
  have c2 := (colLat_zpow_le_iff hπ hY hY' _ _).not.1 h2.not_ge
  have c3 := (colLat_zpow_le_iff hπ hY hY' _ _).1 h1.le
  have c4 := (colLat_zpow_le_iff hπ hY hY' _ _).not.1 h1.not_ge
  have c10 := c1 0; have c11 := c1 1; have c30 := c3 0; have c31 := c3 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at c10 c11 c30 c31
  have hk : k = 0 := by
    by_contra hk
    apply c4; intro i; fin_cases i <;> simp <;> omega
  have hf : f = 1 := by
    by_contra hf
    apply c2; intro i; fin_cases i <;> simp <;> omega
  refine ⟨U₁, hU₁u, ?_⟩
  rw [hM, hk, hf, hYdef, diagP]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_nbr_ne_zero {π : R} (hπ : Irreducible π) {A W : Matrix (Fin 2) (Fin 2) R} (hdA : A.det ≠ 0)
    (hW : IsUnit W.det) : (A * W * diagR π 1).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hdA hW.ne_zero) (diagR_det_ne_zero hπ 1)

/-- **The neighbours of $[AR^2]$** are the vertices $[AW\operatorname{diag}(1,\pi)R^2]$, $W \in \mathrm{GL}_2(R)$. -/
theorem exists_nbr_eq {π : R} (hπ : Irreducible π) {A : Matrix (Fin 2) (Fin 2) R} (hdA : A.det ≠ 0)
    {y : Vert R K} (hadj : (bruhatTits R K π).Adj (latR (K := K) hdA).cls y) :
    ∃ (W : Matrix (Fin 2) (Fin 2) R) (hW : IsUnit W.det), y = (latR (K := K) (det_nbr_ne_zero hπ hdA hW)).cls := by
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  have hX : IsUnit (mapR (K := K) A).det := isUnit_iff_ne_zero.2 (det_mapR_ne_zero hdA)
  -- core: `L ∈ x`, `M ∈ y`, `πL < M < L`
  have core : ∀ L M : Lat R K, L.cls = (latR (K := K) hdA).cls → M.cls = y →
      algebraMap R K π • L.1 < M.1 → M.1 < L.1 →
      ∃ (W : Matrix (Fin 2) (Fin 2) R) (hW : IsUnit W.det), y = (latR (K := K) (det_nbr_ne_zero hπ hdA hW)).cls := by
    intro L M hL hM h1 h2
    obtain ⟨a, ha, hLa⟩ := cls_eq_cls_iff.1 hL.symm
    -- `L = a • A R²`; rescale `M` by `a⁻¹`
    have ha' : a⁻¹ ≠ 0 := inv_ne_zero ha
    have h1' : algebraMap R K π • colLat R (mapR (K := K) A) < (M.scale ha').1 := by
      have := smul_lt_smul_of_lt ha' h1
      rwa [hLa, smul_comm, smul_smul a⁻¹ a, inv_mul_cancel₀ ha, one_smul] at this
    have h2' : (M.scale ha').1 < colLat R (mapR (K := K) A) := by
      have := smul_lt_smul_of_lt ha' h2
      rwa [hLa, smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    obtain ⟨W, hW, hMW⟩ := exists_sandwich hπ hX (M.scale ha') h1' h2'
    refine ⟨W, hW, ?_⟩
    rw [← hM, ← Lat.scale_cls ha' M]
    apply congrArg (Quotient.mk _); apply Subtype.ext
    rw [hMW, latR_val, mapR_mul, mapR_mul, mapR_diagR]
  rw [bruhatTits_adj_iff hπ] at hadj
  rcases hadj with ⟨L, M, hL, hM, h1, h2⟩ | ⟨M, L, hM, hL, h1, h2⟩
  · exact core L M hL hM h1 h2
  · -- `πM < L < M`: use `πM` in the class of `y`
    refine core L (M.scale hπK) hL (by rw [Lat.scale_cls, hM]) (smul_lt_smul_of_lt hπK h2) h1

/-! ### Heights of neighbours -/

theorem latR_cls_congr {A B : Matrix (Fin 2) (Fin 2) R} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (h : A = B) :
    (latR (K := K) hA).cls = (latR (K := K) hB).cls := by
  subst h; rfl

theorem latR_cls_eq_of_colLat_eq {A B : Matrix (Fin 2) (Fin 2) R} (hA : A.det ≠ 0) (hB : B.det ≠ 0) {c : K}
    (hc : c ≠ 0) (h : colLat R (mapR (K := K) B) = c • colLat R (mapR A)) :
    (latR (K := K) hA).cls = (latR (K := K) hB).cls :=
  Quotient.sound (s := homothety R K) (show Homothetic (latR (K := K) hA).1 (latR (K := K) hB).1 from ⟨c, hc, h⟩)

theorem diagR_mul_mul_diagR (π : R) (d : ℕ) (T : Matrix (Fin 2) (Fin 2) R) :
    diagR π d * T * diagR π 1 = !![T 0 0, π * T 0 1; π ^ d * T 1 0, π ^ d * T 1 1 * π] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp; ring

theorem det_nbr {π : R} (hπ : Irreducible π) {U T : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hT : IsUnit T.det) (d : ℕ) : (U * diagR π d * T * diagR π 1).det ≠ 0 := by
  simp only [Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hU.ne_zero (diagR_det_ne_zero hπ d)) hT.ne_zero)
    (diagR_det_ne_zero hπ 1)

theorem vdet_nbr {π : R} (hπ : Irreducible π) {U T : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hT : IsUnit T.det) (d : ℕ) : vdet (U * diagR π d * T * diagR π 1) = d + 1 := by
  have h1 : (U * diagR π d).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hU.ne_zero (diagR_det_ne_zero hπ d)
  have h2 : (U * diagR π d * T).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h1 hT.ne_zero
  rw [vdet_mul h2 (diagR_det_ne_zero hπ 1), vdet_mul h1 hT.ne_zero, vdet_mul hU.ne_zero (diagR_det_ne_zero hπ d),
    vdet_of_isUnit hU, vdet_of_isUnit hT, vdet_diagR hπ, vdet_diagR hπ]
  ring

/-- If $T \in \mathrm{GL}_2(R)$ and $T_{00}$ is not a unit, then $T_{10}$ is a unit. -/
theorem isUnit_one_zero {T : Matrix (Fin 2) (Fin 2) R} (hT : IsUnit T.det) (h0 : ¬ IsUnit (T 0 0)) :
    IsUnit (T 1 0) := by
  by_contra h1
  rw [Matrix.det_fin_two] at hT
  have hm0 : T 0 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h0
  have hm1 : T 1 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h1
  have : T 0 0 * T 1 1 - T 0 1 * T 1 0 ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hm0) (Ideal.mul_mem_left _ _ hm1)
  exact (IsLocalRing.mem_maximalIdeal _).1 this hT

/-- **Upper neighbours**: if $T_{00}$ is a unit, or $d = 0$, then $UD_dTD_1$ is primitive. -/
theorem isPrim_nbr_up {π : R} {U T : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hT : IsUnit T.det) (d : ℕ) (h : IsUnit (T 0 0) ∨ d = 0) : IsPrim (U * diagR π d * T * diagR π 1) := by
  rw [mul_assoc, mul_assoc]
  apply IsPrim.mul_left _ hU
  rw [← mul_assoc, diagR_mul_mul_diagR]
  rcases h with h | rfl
  · exact ⟨0, 0, by simpa using h⟩
  · by_cases h0 : IsUnit (T 0 0)
    · exact ⟨0, 0, by simpa using h0⟩
    · exact ⟨1, 0, by simpa using isUnit_one_zero hT h0⟩

/-- **The lower neighbour**: if $T_{00}$ is not a unit and $d = e + 1$, then $[UD_dTD_1R^2] = [UD_eR^2]$. -/
theorem latR_nbr_down {π : R} (hπ : Irreducible π) {U T : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det)
    (hT : IsUnit T.det) (e : ℕ) (h0 : ¬ IsUnit (T 0 0)) :
    (latR (K := K) (det_nbr hπ hU hT (e + 1))).cls =
      (latR (K := K) (show (U * diagR π e).det ≠ 0 by
        rw [Matrix.det_mul]; exact mul_ne_zero hU.ne_zero (diagR_det_ne_zero hπ e))).cls := by
  have hm0 : T 0 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h0
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm0
  obtain ⟨a, ha⟩ := hm0
  set T₂ : Matrix (Fin 2) (Fin 2) R := !![a, T 0 1; T 1 0, π * T 1 1] with hT₂
  have hdT₂ : T₂.det = T.det := by
    rw [hT₂, Matrix.det_fin_two_of, Matrix.det_fin_two, ha]; ring
  have hT₂u : IsUnit T₂.det := hdT₂ ▸ hT
  have hB : U * diagR π (e + 1) * T * diagR π 1 = π • (U * diagR π e * T₂) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (diagR π (e + 1)), diagR_mul_mul_diagR, mul_assoc U (diagR π e) T₂,
      ← Matrix.mul_smul]
    congr 1
    ext i j
    rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [hT₂, ha] <;> ring
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  symm
  apply latR_cls_eq_of_colLat_eq _ _ hπK
  rw [hB, smul_colLat]
  have hm : mapR (K := K) (π • (U * diagR π e * T₂)) = algebraMap R K π • (mapR (U * diagR π e) * mapR T₂) := by
    rw [← mapR_mul]; ext i j; simp only [mapR, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [hm, ← Matrix.smul_mul, colLat_mul_mapR (Matrix.mul_nonsing_inv _ hT₂u)]

/-! ### The tree -/

/-- Every vertex is $[AR^2]$ with $A$ integral and primitive. -/
theorem exists_latR_eq {π : R} (hπ : Irreducible π) (x : Vert R K) :
    ∃ (A : Matrix (Fin 2) (Fin 2) R) (hdA : A.det ≠ 0), IsPrim A ∧ x = (latR (K := K) hdA).cls := by
  induction x using Quotient.inductionOn with | h L => ?_
  obtain ⟨c, A, hc, hA, hdA, hL⟩ := exists_primRep hπ L
  exact ⟨A, hdA, hA, (Quotient.sound (s := homothety R K)
    (show Homothetic (latR (K := K) hdA).1 L.1 from ⟨c, hc, hL⟩)).symm⟩

theorem det_UD_ne_zero {π : R} (hπ : Irreducible π) {U : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det) (e : ℕ) :
    (U * diagR π e).det ≠ 0 := by
  rw [Matrix.det_mul]; exact mul_ne_zero hU.ne_zero (diagR_det_ne_zero hπ e)

/-- **Neighbour analysis** at $x = [AR^2]$ with $A = UD_dV$ ($U, V \in \mathrm{GL}_2(R)$): every neighbour $y$ of $x$
has height $d + 1$, or $d = e + 1$ and $y = [UD_eR^2]$. -/
theorem nbr_cases {π : R} (hπ : Irreducible π) {A : Matrix (Fin 2) (Fin 2) R} (hdA : A.det ≠ 0)
    {U V : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det) (hV : IsUnit V.det) {d : ℕ}
    (hAUV : A = U * diagR π d * V) {y : Vert R K} (hy : (bruhatTits R K π).Adj (latR (K := K) hdA).cls y) :
    height R K π hπ y = d + 1 ∨ ∃ e, d = e + 1 ∧ y = (latR (K := K) (det_UD_ne_zero hπ hU e)).cls := by
  obtain ⟨W, hW, rfl⟩ := exists_nbr_eq hπ hdA hy
  have hT : IsUnit (V * W).det := by rw [Matrix.det_mul]; exact hV.mul hW
  have hAW : A * W * diagR π 1 = U * diagR π d * (V * W) * diagR π 1 := by
    rw [hAUV]; simp only [mul_assoc]
  rw [latR_cls_congr _ (det_nbr hπ hU hT d) hAW]
  by_cases hcase : IsUnit ((V * W) 0 0) ∨ d = 0
  · left
    rw [height_latR hπ (isPrim_nbr_up hU hT d hcase), vdet_nbr hπ hU hT]
  · right
    rw [not_or] at hcase
    obtain ⟨h0, hd⟩ := hcase
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    exact ⟨e, rfl, latR_nbr_down hπ hU hT e h0⟩

theorem height_UD {π : R} (hπ : Irreducible π) {U : Matrix (Fin 2) (Fin 2) R} (hU : IsUnit U.det) (e : ℕ) :
    height R K π hπ (latR (K := K) (det_UD_ne_zero hπ hU e)).cls = e := by
  rw [height_latR hπ ((isPrim_diagR π e).mul_left hU), vdet_mul hU.ne_zero (diagR_det_ne_zero hπ e),
    vdet_of_isUnit hU, vdet_diagR hπ, zero_add]

/-- Adjacent vertices have heights differing by exactly one. -/
theorem height_adj {π : R} (hπ : Irreducible π) {x y : Vert R K} (hxy : (bruhatTits R K π).Adj x y) :
    height R K π hπ x + 1 = height R K π hπ y ∨ height R K π hπ y + 1 = height R K π hπ x := by
  obtain ⟨A, hdA, hA, rfl⟩ := exists_latR_eq (K := K) hπ x
  obtain ⟨d, U, U', V, V', hU, -, hV, -, hAUV⟩ := exists_factor hπ A hA hdA
  have hUu := isUnit_det_of_mul_eq_one hU
  have hVu := isUnit_det_of_mul_eq_one hV
  have hx : height R K π hπ (latR (K := K) hdA).cls = d := by
    rw [height_latR hπ hA hdA, hAUV, vdet_cartan hπ hUu hVu]
  rcases nbr_cases hπ hdA hUu hVu hAUV hxy with h | ⟨e, rfl, rfl⟩
  · left; omega
  · right; rw [hx, height_UD hπ hUu]

/-- Every vertex has at most one neighbour of smaller height. -/
theorem height_lower_unique {π : R} (hπ : Irreducible π) {x y y' : Vert R K} (hy : (bruhatTits R K π).Adj x y)
    (hy' : (bruhatTits R K π).Adj x y') (h : height R K π hπ y + 1 = height R K π hπ x)
    (h' : height R K π hπ y' + 1 = height R K π hπ x) : y = y' := by
  obtain ⟨A, hdA, hA, rfl⟩ := exists_latR_eq (K := K) hπ x
  obtain ⟨d, U, U', V, V', hU, -, hV, -, hAUV⟩ := exists_factor hπ A hA hdA
  have hUu := isUnit_det_of_mul_eq_one hU
  have hVu := isUnit_det_of_mul_eq_one hV
  have hx : height R K π hπ (latR (K := K) hdA).cls = d := by
    rw [height_latR hπ hA hdA, hAUV, vdet_cartan hπ hUu hVu]
  rcases nbr_cases hπ hdA hUu hVu hAUV hy with h1 | ⟨e, he, rfl⟩
  · omega
  rcases nbr_cases hπ hdA hUu hVu hAUV hy' with h1 | ⟨e', he', rfl⟩
  · omega
  obtain rfl : e = e' := by omega
  rfl

/-- **Proposition 23.5.8** (Voight 2021), tree part: the Bruhat–Tits graph $\mathcal T$ is a tree (connected, without
cycles). -/
@[kb "voight2021" "Proposition 23.5.8, p. 387"]
theorem bruhatTits_isTree {π : R} (hπ : Irreducible π) : (bruhatTits R K π).IsTree :=
  ⟨bruhatTits_connected hπ, isAcyclic_of_height _ (height R K π hπ) (fun _ _ h => height_adj hπ h)
    (fun _ _ _ hu hu' h h' => height_lower_unique hπ hu hu' h h')⟩

/-! ### Distances (23.5.14, Lemma 23.5.15) -/

variable (R K) in
/-- The base vertex $[R^2]$. -/
def baseVert : Vert R K := (latR (K := K) (A := (1 : Matrix (Fin 2) (Fin 2) R)) (by simp)).cls

theorem height_baseVert {π : R} (hπ : Irreducible π) : height R K π hπ (baseVert R K) = 0 := by
  rw [baseVert, height_latR hπ (isPrim_of_isUnit (by simp)), vdet_of_isUnit (by simp)]

/-- **Distance from the base vertex** (23.5.14): $d([R^2], x) = h(x)$. -/
@[kb "voight2021" "23.5.14, p. 389; Lemma 23.5.15, p. 389"]
theorem dist_baseVert {π : R} (hπ : Irreducible π) (x : Vert R K) :
    (bruhatTits R K π).dist (baseVert R K) x = height R K π hπ x := by
  apply le_antisymm
  · obtain ⟨A, hdA, hA, rfl⟩ := exists_latR_eq (K := K) hπ x
    obtain ⟨d, U, U', V, V', hU, hU', hV, -, hAUV⟩ := exists_factor hπ A hA hdA
    have hUu := isUnit_det_of_mul_eq_one hU
    have hVu := isUnit_det_of_mul_eq_one hV
    rw [height_latR hπ hA hdA, show vdet A = d by rw [hAUV, vdet_cartan hπ hUu hVu]]
    have hPQ : mapR (K := K) U * mapR U' = 1 := by rw [← mapR_mul, hU, mapR_one]
    have hQP : mapR (K := K) U' * mapR U = 1 := by rw [← mapR_mul, hU', mapR_one]
    have key : ∀ a b a' b' : Vert R K, a = a' → b = b' → (bruhatTits R K π).dist a b ≤ d →
        (bruhatTits R K π).dist a' b' ≤ d := by
      rintro _ _ _ _ rfl rfl h; exact h
    refine key _ _ _ _ ?_ ?_ (dist_le_diag hπ hPQ hQP d)
    · apply congrArg (Quotient.mk _); apply Subtype.ext
      change colLat R (mapR U) = colLat R (mapR (1 : Matrix (Fin 2) (Fin 2) R))
      rw [mapR_one, ← one_mul (mapR (K := K) U), colLat_mul_mapR hU]
    · apply congrArg (Quotient.mk _); apply Subtype.ext
      change colLat R (mapR U * diagP π d) = colLat R (mapR A)
      rw [hAUV, mapR_mul, mapR_mul, mapR_diagR, colLat_mul_mapR hV]
  · have h := le_dist_of_height (bruhatTits R K π) (height R K π hπ)
      (fun u v huv => by rcases height_adj hπ huv with h | h <;> omega)
      ((bruhatTits_connected (K := K) hπ).preconnected (baseVert R K) x)
    rwa [height_baseVert hπ, zero_add] at h

theorem smulVert_inv_smulVert (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (z : Vert R K) :
    smulVert g⁻¹ (smulVert g z) = z := by
  induction z using Quotient.inductionOn with | h L => ?_
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  change latMap g⁻¹ (latMap g L.1) = L.1
  ext v
  simp only [mem_latMap]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro hv
    exact ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ v, ⟨v, hv, rfl⟩, by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]⟩

theorem dist_smulVert_le {π : R} (hπ : Irreducible π) (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (a b : Vert R K) :
    (bruhatTits R K π).dist (smulVert g a) (smulVert g b) ≤ (bruhatTits R K π).dist a b := by
  obtain ⟨w, hw⟩ := ((bruhatTits_connected (K := K) hπ).preconnected a b).exists_walk_length_eq_dist
  let f : bruhatTits R K π →g bruhatTits R K π := ⟨smulVert g, fun h => bruhatTits_adj_smulVert g h⟩
  calc _ ≤ (w.map f).length := SimpleGraph.dist_le _
    _ = _ := by rw [SimpleGraph.Walk.length_map, hw]

/-- $\mathrm{GL}_2(F)$ acts on $\mathcal T$ by isometries (23.5.11, 23.5.14). -/
@[kb "voight2021" "23.5.11, p. 388; 23.5.14, p. 389"]
theorem dist_smulVert {π : R} (hπ : Irreducible π) (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (a b : Vert R K) :
    (bruhatTits R K π).dist (smulVert g a) (smulVert g b) = (bruhatTits R K π).dist a b := by
  apply le_antisymm (dist_smulVert_le hπ g a b)
  have := dist_smulVert_le hπ g⁻¹ (smulVert g a) (smulVert g b)
  rwa [smulVert_inv_smulVert, smulVert_inv_smulVert] at this

/-- **Lemma 23.5.15** (Voight 2021), distance: if $L = PR^2$ has basis $x_0, x_1$ (the columns of $P$) and $L'$ has
basis $x_0, \pi^e x_1$ (the columns of $P\operatorname{diag}(1,\pi^e)$), then $d([L],[L']) = e$. (A further factor
$\pi^f$ on both basis vectors of $L'$, as in the book, does not change $[L']$.) -/
@[kb "voight2021" "Lemma 23.5.15, p. 389; 23.5.14, p. 389"]
theorem dist_diag {π : R} (hπ : Irreducible π) {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (e : ℕ) :
    (bruhatTits R K π).dist (latOf (R := R) hPQ).cls
      (latOf (R := R) (Q := diagQ π e * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π e), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π e * (diagQ π e * Q) = 1)).cls = e := by
  let g : (Matrix (Fin 2) (Fin 2) K)ˣ := ⟨Q, P, hQP, hPQ⟩
  rw [← dist_smulVert hπ g]
  have h1 : smulVert g (latOf (R := R) hPQ).cls = baseVert R K := by
    apply congrArg (Quotient.mk _); apply Subtype.ext
    change latMap g (colLat R P) = colLat R (mapR (1 : Matrix (Fin 2) (Fin 2) R))
    rw [latMap_colLat, mapR_one]
    change colLat R (Q * P) = _
    rw [hQP]
  have h2 : smulVert g (latOf (R := R) (Q := diagQ π e * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π e), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π e * (diagQ π e * Q) = 1)).cls = (latR (K := K) (diagR_det_ne_zero hπ e)).cls := by
    apply congrArg (Quotient.mk _); apply Subtype.ext
    change latMap g (colLat R (P * diagP π e)) = colLat R (mapR (diagR π e))
    rw [latMap_colLat, mapR_diagR]
    change colLat R (Q * (P * diagP π e)) = _
    rw [← mul_assoc, hQP, one_mul]
  rw [h1, h2, dist_baseVert hπ, height_latR hπ (isPrim_diagR π e), vdet_diagR hπ]

end QuadFormsKB.Voight.Wave8
