/-
# Lattices in $F^2$ over a discrete valuation ring (Voight, Lemma 23.5.1)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): section 23.5 (p. 386),
Lemma 23.5.1.

**Setting.** $R$ is a discrete valuation ring with fraction field $F$ (written `K` in the code) and uniformizer $\pi$;
$V = F^2$ (`Fin 2 → K`, column vectors, entries indexed $0, 1$). An $R$-lattice in $V$ is a finitely generated
$R$-submodule $L \subseteq V$ with $FL = V$ (Mathlib's `Submodule.IsLattice K L`).

**Contents.**
* `colLat R P`: the $R$-span of the columns of $P \in \mathrm M_2(F)$; `mem_colLat`: $v \in \operatorname{colLat} P$ iff
  $v = P r$ with $r \in R^2$.
* `colLat_le_colLat_iff`: for invertible $P, P'$, $\operatorname{colLat} P \subseteq \operatorname{colLat} P'$ iff
  $P'^{-1}P \in \mathrm M_2(R)$.
* `isLattice_iff_exists_colLat`: the $R$-lattices in $V$ are exactly the $\operatorname{colLat} P$ with $P \in \mathrm{GL}_2(F)$.
* `IsRBasis x L`: the vectors $x_0, x_1$ form an $R$-basis of $L$.
* `exists_adapted_basis` (Lemma 23.5.1): for $R$-lattices $L, M \subseteq V$ there is an $R$-basis $x_0, x_1$ of $L$ and
  integers $f_0 \le f_1$ such that $\pi^{f_0}x_0, \pi^{f_1}x_1$ is an $R$-basis of $M$.

All proved; no inputs. The book's indices $x_1, x_2$, $f_1, f_2$ are $x_0, x_1$, $f_0, f_1$ here.
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerNormalizer

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave8

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Column lattices -/

/-- The vector $(r_0, r_1) \in F^2$ for $r \in R^2$. -/
abbrev vecR (r : Fin 2 → R) : Fin 2 → K := fun i => algebraMap R K (r i)

/-- The $j$-th column of a matrix, as a vector of $V = F^2$. -/
abbrev colVec (P : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) : Fin 2 → K := fun i => P i j

variable (R) in
/-- **The column lattice** of $P \in \mathrm M_2(F)$: the $R$-span of the columns of $P$, i.e. $P R^2 \subseteq F^2$. -/
def colLat (P : Matrix (Fin 2) (Fin 2) K) : Submodule R (Fin 2 → K) :=
  Submodule.span R (Set.range (colVec P))

theorem sum_smul_colVec (P : Matrix (Fin 2) (Fin 2) K) (r : Fin 2 → R) :
    ∑ j, r j • colVec P j = P *ᵥ vecR r := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Algebra.smul_def, mul_comm]

theorem mem_colLat {P : Matrix (Fin 2) (Fin 2) K} {v : Fin 2 → K} :
    v ∈ colLat R P ↔ ∃ r : Fin 2 → R, v = P *ᵥ vecR r := by
  rw [colLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, sum_smul_colVec P r⟩
  · rintro ⟨r, rfl⟩; exact ⟨r, sum_smul_colVec P r⟩

theorem colVec_mem_colLat (P : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) : colVec P j ∈ colLat R P :=
  Submodule.subset_span ⟨j, rfl⟩

theorem mapR_mulVec (U : Matrix (Fin 2) (Fin 2) R) (r : Fin 2 → R) :
    mapR (K := K) U *ᵥ vecR r = vecR (U *ᵥ r) := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mapR, vecR]

/-- A vector is integral iff it is `vecR r`. -/
theorem exists_vecR_iff {v : Fin 2 → K} : (∃ r : Fin 2 → R, v = vecR r) ↔ ∀ i, IsInteger R (v i) := by
  constructor
  · rintro ⟨r, rfl⟩ i; exact ⟨r i, rfl⟩
  · intro h
    choose r hr using h
    exact ⟨r, funext fun i => (hr i).symm⟩

/-- An integral matrix times an integral vector is integral. -/
theorem mulVec_vecR_of_mem_matOrder {A : Matrix (Fin 2) (Fin 2) K} (hA : A ∈ matOrder R K) (r : Fin 2 → R) :
    ∃ s : Fin 2 → R, A *ᵥ vecR r = vecR s := by
  rw [mem_matOrder] at hA
  choose B hB using hA
  refine ⟨(Matrix.of B) *ᵥ r, ?_⟩
  have : A = mapR (Matrix.of B) := by ext i j; simp [mapR, hB i j]
  rw [this, mapR_mulVec]

/-- **Inclusion of column lattices**: for $P$ (any) and $P'$ invertible with inverse $Q'$,
$\operatorname{colLat} P \subseteq \operatorname{colLat} P'$ iff $Q'P$ is integral. -/
theorem colLat_le_colLat_iff {P P' Q' : Matrix (Fin 2) (Fin 2) K} (hPQ' : P' * Q' = 1) (hQP' : Q' * P' = 1) :
    colLat R P ≤ colLat R P' ↔ Q' * P ∈ matOrder R K := by
  constructor
  · intro h
    rw [mem_matOrder]
    intro i j
    have hj : colVec P j ∈ colLat R P' := h (colVec_mem_colLat P j)
    obtain ⟨r, hr⟩ := mem_colLat.1 hj
    have : (fun i => (Q' * P) i j) = vecR r := by
      have h2 : Q' *ᵥ colVec P j = vecR r := by rw [hr, Matrix.mulVec_mulVec, hQP', Matrix.one_mulVec]
      rw [← h2]; ext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, colVec]
    rw [congrFun this i]; exact ⟨r i, rfl⟩
  · intro h v hv
    obtain ⟨r, rfl⟩ := mem_colLat.1 hv
    obtain ⟨s, hs⟩ := mulVec_vecR_of_mem_matOrder h r
    refine mem_colLat.2 ⟨s, ?_⟩
    rw [← hs, Matrix.mulVec_mulVec, ← mul_assoc, hPQ', one_mul]

/-- Right multiplication by $U \in \mathrm{GL}_2(R)$ does not change the column lattice. -/
theorem colLat_mul_mapR {P : Matrix (Fin 2) (Fin 2) K} {U U' : Matrix (Fin 2) (Fin 2) R} (hU : U * U' = 1) :
    colLat R (P * mapR U) = colLat R P := by
  apply le_antisymm
  · intro v hv
    obtain ⟨r, rfl⟩ := mem_colLat.1 hv
    exact mem_colLat.2 ⟨U *ᵥ r, by rw [← Matrix.mulVec_mulVec, mapR_mulVec]⟩
  · intro v hv
    obtain ⟨r, rfl⟩ := mem_colLat.1 hv
    refine mem_colLat.2 ⟨U' *ᵥ r, ?_⟩
    rw [← Matrix.mulVec_mulVec, mapR_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- The columns of an invertible matrix are $R$-linearly independent. -/
theorem linearIndependent_colVec {P Q : Matrix (Fin 2) (Fin 2) K} (hQP : Q * P = 1) :
    LinearIndependent R (colVec P) := by
  rw [Fintype.linearIndependent_iff]
  intro r hr
  rw [sum_smul_colVec] at hr
  have h1 : vecR (K := K) r = 0 := by
    have := congrArg (Q *ᵥ ·) hr
    change Q *ᵥ (P *ᵥ vecR r) = Q *ᵥ 0 at this
    rwa [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  intro i
  have := congrFun h1 i
  simpa [vecR, (IsFractionRing.injective R K).eq_iff] using this

/-! ### $R$-bases and lattices -/

variable (R) in
/-- **$R$-basis** of an $R$-submodule $L \subseteq V$: the vectors $x_0, x_1$ are $R$-linearly independent and span $L$. -/
def IsRBasis (x : Fin 2 → Fin 2 → K) (L : Submodule R (Fin 2 → K)) : Prop :=
  LinearIndependent R x ∧ Submodule.span R (Set.range x) = L

theorem isRBasis_colVec {P Q : Matrix (Fin 2) (Fin 2) K} (hQP : Q * P = 1) : IsRBasis R (colVec P) (colLat R P) :=
  ⟨linearIndependent_colVec hQP, rfl⟩

/-- The matrix whose columns are $x_0, x_1$. -/
abbrev ofCols (x : Fin 2 → Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x j i

theorem colVec_ofCols (x : Fin 2 → Fin 2 → K) : colVec (ofCols x) = x := rfl

/-- A column lattice of an invertible matrix is an $R$-lattice. -/
theorem isLattice_colLat {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) :
    Submodule.IsLattice K (colLat R P) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    have hv : v = P *ᵥ (Q *ᵥ v) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    rw [hv]
    have : P *ᵥ (Q *ᵥ v) = ∑ j, (Q *ᵥ v) j • colVec P j := by
      ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩)

section PID

variable [IsPrincipalIdealRing R]

/-- **Every $R$-lattice in $F^2$ is a column lattice** ($R$ a principal ideal domain): $L = P R^2$ for some
$P \in \mathrm{GL}_2(F)$ (inverse $Q$), and conversely. -/
theorem isLattice_iff_exists_colLat (L : Submodule R (Fin 2 → K)) :
    Submodule.IsLattice K L ↔
      ∃ P Q : Matrix (Fin 2) (Fin 2) K, P * Q = 1 ∧ Q * P = 1 ∧ L = colLat R P := by
  constructor
  · intro hL
    have hrank : Module.finrank R L = 2 := by
      simpa using Submodule.IsLattice.finrank_of_pi K L
    let b : Module.Basis (Fin 2) R L := Module.finBasisOfFinrankEq R L hrank
    let e : Module.Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
    let P : Matrix (Fin 2) (Fin 2) K := ofCols fun j => (b j : Fin 2 → K)
    have hP : (Pi.basisFun K (Fin 2)).toMatrix e = P := by
      ext i j
      simp [Module.Basis.toMatrix_apply, P, e]
    refine ⟨P, e.toMatrix (Pi.basisFun K (Fin 2)), ?_, ?_, ?_⟩
    · rw [← hP, Module.Basis.toMatrix_mul_toMatrix_flip]
    · rw [← hP, Module.Basis.toMatrix_mul_toMatrix_flip]
    · rw [colLat, colVec_ofCols]
      symm
      have : Set.range (fun j => (b j : Fin 2 → K)) = L.subtype '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rintro ⟨P, Q, hPQ, -, rfl⟩
    exact isLattice_colLat hPQ

end PID

/-! ### Lemma 23.5.1 -/

variable [IsDiscreteValuationRing R]

/-- Every $c \in F^\times$ is $u\pi^k$ with $u \in R^\times$ and $k \in \mathbb Z$. -/
theorem exists_unit_zpow {π : R} (hπ : Irreducible π) {c : K} (hc : c ≠ 0) :
    ∃ (u : Rˣ) (k : ℤ), c = algebraMap R K u * algebraMap R K π ^ k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have ha : a ≠ 0 := by rintro rfl; simp at hc
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  have hwK : algebraMap R K (w : R) ≠ 0 := algebraMap_ne_zero w.ne_zero
  refine ⟨u * w⁻¹, (m : ℤ) - n, ?_⟩
  rw [zpow_sub₀ hπK, zpow_natCast, zpow_natCast]
  simp only [map_mul, map_pow, Units.val_mul]
  have hww : algebraMap R K (w : R) * algebraMap R K ((w⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  field_simp
  linear_combination (-1 : K) * hww

/-- **Lemma 23.5.1** (Voight 2021): for $R$-lattices $L, M \subseteq V = F^2$ ($R$ a discrete valuation ring with
uniformizer $\pi$) there exist an $R$-basis $x_0, x_1$ of $L$ and integers $f_0 \le f_1$ such that
$\pi^{f_0}x_0, \pi^{f_1}x_1$ is an $R$-basis of $M$. (The book's $x_1, x_2, f_1, f_2$ are $x_0, x_1, f_0, f_1$.)

Proof: write $L = PR^2$, $M = P'R^2$ (`isLattice_iff_exists_colLat`) and apply the Cartan decomposition
$P^{-1}P' = cU\operatorname{diag}(1,\pi^e)V$ (`Wave4.exists_eq_smul_mul_diag_mul`); with $c = u\pi^k$ take the columns of
$P\,uU$ as $x$ and $f = (k, k+e)$. -/
@[kb "voight2021" "Lemma 23.5.1, p. 386"]
theorem exists_adapted_basis {π : R} (hπ : Irreducible π) (L M : Submodule R (Fin 2 → K))
    [hL : Submodule.IsLattice K L] [hM : Submodule.IsLattice K M] :
    ∃ (x : Fin 2 → Fin 2 → K) (f₀ f₁ : ℤ), f₀ ≤ f₁ ∧ IsRBasis R x L ∧
      IsRBasis R ![algebraMap R K π ^ f₀ • x 0, algebraMap R K π ^ f₁ • x 1] M := by
  obtain ⟨P, Q, hPQ, hQP, rfl⟩ := (isLattice_iff_exists_colLat L).1 hL
  obtain ⟨P', Q', hPQ', hQP', rfl⟩ := (isLattice_iff_exists_colLat M).1 hM
  have hgh : (Q * P') * (Q' * P) = 1 := by
    rw [mul_assoc, ← mul_assoc P', hPQ', one_mul, hQP]
  obtain ⟨c, e, U, U', V, V', hc, hU, hU', hV, hV', hg⟩ := exists_eq_smul_mul_diag_mul (K := K) hπ hgh
  obtain ⟨u, k, rfl⟩ := exists_unit_zpow hπ hc
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  -- the new basis matrix of `L`
  set W : Matrix (Fin 2) (Fin 2) R := (u : R) • U with hW
  set W' : Matrix (Fin 2) (Fin 2) R := ((u⁻¹ : Rˣ) : R) • U' with hW'
  have hWW : W * W' = 1 := by
    rw [hW, hW', Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, Units.mul_inv, one_smul]
  have hWW' : W' * W = 1 := by
    rw [hW, hW', Matrix.smul_mul, Matrix.mul_smul, hU', smul_smul, Units.inv_mul, one_smul]
  set X : Matrix (Fin 2) (Fin 2) K := P * mapR W with hX
  set Y : Matrix (Fin 2) (Fin 2) K := mapR W' * Q with hY
  have hXY : X * Y = 1 := by
    rw [hX, hY, mul_assoc, ← mul_assoc (mapR W), ← mapR_mul, hWW, mapR_one, one_mul, hPQ]
  have hYX : Y * X = 1 := by
    rw [hX, hY, mul_assoc, ← mul_assoc Q, hQP, one_mul, ← mapR_mul, hWW', mapR_one]
  -- `P' = π^k X diag(1, π^e) V`
  have hP' : P' = algebraMap R K π ^ k • (X * diagP π e * mapR V) := by
    have h1 : P' = P * (Q * P') := by rw [← mul_assoc, hPQ, one_mul]
    rw [h1, hg, mapR_mul, mapR_mul, mapR_diagR, hX, hW]
    have : mapR (K := K) ((u : R) • U) = algebraMap R K (u : R) • mapR U := by
      ext i j; simp [mapR, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [this]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_assoc]
    rw [mul_comm (algebraMap R K (u : R))]
  refine ⟨colVec X, k, k + e, by omega, ?_, ?_⟩
  · rw [show colLat R P = colLat R X by rw [hX, colLat_mul_mapR hWW]]
    exact isRBasis_colVec hYX
  · -- `M = colLat (π^k X diag(1,π^e))`
    set Z : Matrix (Fin 2) (Fin 2) K := algebraMap R K π ^ k • (X * diagP π e) with hZ
    set Z' : Matrix (Fin 2) (Fin 2) K := (algebraMap R K π ^ k)⁻¹ • (diagQ π e * Y) with hZ'
    have hπk : algebraMap R K π ^ k ≠ 0 := zpow_ne_zero _ hπK
    have hZZ : Z' * Z = 1 := by
      rw [hZ, hZ', Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hπk, one_smul, mul_assoc,
        ← mul_assoc Y, hYX, one_mul, diagQ_mul_diagP hπ.ne_zero]
    have hM : colLat R P' = colLat R Z := by
      rw [hP', hZ, ← Matrix.smul_mul, colLat_mul_mapR hV]
    have hcol : colVec Z = ![algebraMap R K π ^ k • colVec X 0, algebraMap R K π ^ (k + (e : ℤ)) • colVec X 1] := by
      funext j i
      fin_cases j
      · simp [colVec, hZ, diagP, Matrix.mul_diagonal]
      · simp [colVec, hZ, diagP, Matrix.mul_diagonal, zpow_add₀ hπK]
        ring
    rw [hM, ← hcol]
    exact isRBasis_colVec hZZ

end QuadFormsKB.Voight.Wave8
