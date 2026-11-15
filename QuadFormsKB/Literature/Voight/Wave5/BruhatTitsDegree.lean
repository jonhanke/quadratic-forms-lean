/-
# The degree of the Bruhat–Tits tree (Voight, Proposition 23.5.8)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 23.5.8 (p. 387).

**Setting.** As in `Wave5/BruhatTits.lean`: $R$ a discrete valuation ring with fraction field $F$ (`K`), uniformizer
$\pi$ and residue field $k$; $\mathcal T$ the Bruhat–Tits graph on homothety classes of $R$-lattices in $F^2$.

**Contents.**
* `nbrBase`: the neighbours of $[R^2]$ are, without repetition, the classes of
  $N_a = \begin{pmatrix}1 & 0\\ \hat a & \pi\end{pmatrix}R^2$ ($a \in k$, $\hat a \in R$ a lift) and of
  $N_\infty = \begin{pmatrix}\pi & 0\\ 0 & 1\end{pmatrix}R^2$, i.e. they correspond to the lines of $k^2$.
* `bruhatTitsDegree` (Proposition 23.5.8, degree): every vertex has $\#k + 1$ neighbours (`ENat.card`), proving
  `BruhatTitsDegree`. With `bruhatTits_isTree` this completes Proposition 23.5.8.
-/
import QuadFormsKB.Literature.Voight.Wave5.BruhatTitsHeight

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

open Matrix Pointwise

noncomputable section

namespace QuadFormsKB.Voight.Wave8

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  IsLocalization IsDiscreteValuationRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-! ### Transport of neighbourhoods along the action -/

theorem smulVert_smulVert_inv (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (z : Vert R K) :
    smulVert g (smulVert g⁻¹ z) = z := by
  simpa using smulVert_inv_smulVert g⁻¹ z

theorem adj_smulVert_iff {π : R} (g : (Matrix (Fin 2) (Fin 2) K)ˣ) {x y : Vert R K} :
    (bruhatTits R K π).Adj (smulVert g x) (smulVert g y) ↔ (bruhatTits R K π).Adj x y := by
  refine ⟨fun h => ?_, bruhatTits_adj_smulVert g⟩
  have := bruhatTits_adj_smulVert (π := π) g⁻¹ h
  rwa [smulVert_inv_smulVert, smulVert_inv_smulVert] at this

/-- $g$ maps the neighbours of $x$ bijectively onto the neighbours of $gx$. -/
def nbrEquiv {π : R} (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (x : Vert R K) :
    (bruhatTits R K π).neighborSet x ≃ (bruhatTits R K π).neighborSet (smulVert g x) where
  toFun y := ⟨smulVert g y, (adj_smulVert_iff g).2 y.2⟩
  invFun y := ⟨smulVert g⁻¹ y, by
    have h : (bruhatTits R K π).Adj (smulVert g x) (smulVert g (smulVert g⁻¹ y.1)) := by
      rw [smulVert_smulVert_inv]; exact y.2
    exact (adj_smulVert_iff g).1 h⟩
  left_inv y := Subtype.ext (smulVert_inv_smulVert g y.1)
  right_inv y := Subtype.ext (smulVert_smulVert_inv g y.1)

/-! ### Lattices strictly between $\pi R^2$ and $R^2$ -/

/-- The lattice $R^2$. -/
abbrev latOne : Submodule R (Fin 2 → K) := colLat R (1 : Matrix (Fin 2) (Fin 2) K)

/-- Two lattices strictly between $\pi R^2$ and $R^2$ that are homothetic are equal. -/
theorem eq_of_between {π : R} (hπ : Irreducible π) {M M' : Submodule R (Fin 2 → K)}
    (h1 : algebraMap R K π • latOne < M) (h2 : M < latOne) (h1' : algebraMap R K π • latOne < M')
    (h2' : M' < latOne) {c : K} (hc : c ≠ 0) (h : M' = c • M) : M' = M := by
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  have h11 : (1 : Matrix (Fin 2) (Fin 2) K) * 1 = 1 := one_mul 1
  obtain ⟨u, k, rfl⟩ := exists_unit_zpow hπ hc
  rw [mul_smul, unit_smul_submodule] at h
  -- `π^j R² ≤ π R²` for `j ≥ 1`
  have hle : ∀ j : ℤ, 1 ≤ j → algebraMap R K π ^ j • (latOne : Submodule R (Fin 2 → K)) ≤
      algebraMap R K π • latOne := by
    intro j hj
    have := smul_submodule_mono (algebraMap R K π)
      ((zpow_smul_colLat_le_iff (R := R) hπ h11 h11 (j - 1)).2 (by omega))
    rwa [smul_smul, ← zpow_one_add₀ hπK, add_sub_cancel] at this
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · -- `M = π^(-k) M' ≤ π^(-k) R² ≤ π R²`, contradiction
    exfalso
    have hM : M = algebraMap R K π ^ (-k) • M' := by
      rw [h, smul_smul, ← zpow_add₀ hπK, neg_add_cancel, zpow_zero, one_smul]
    apply h1.not_ge
    rw [hM]
    exact (smul_submodule_mono _ h2'.le).trans (hle _ (by omega))
  · rwa [zpow_zero, one_smul] at h
  · exfalso
    apply h1'.not_ge
    rw [h]
    exact (smul_submodule_mono _ h2.le).trans (hle _ (by omega))

/-- The lattice $W\operatorname{diag}(1,\pi)R^2$ ($W \in \mathrm{GL}_2(R)$) lies strictly between $\pi R^2$ and $R^2$, and
its class is a neighbour of $[R^2]$. -/
theorem between_nbr {π : R} (hπ : Irreducible π) {W : Matrix (Fin 2) (Fin 2) R} (hW : IsUnit W.det) :
    algebraMap R K π • latOne < colLat R (mapR (K := K) (W * diagR π 1)) ∧
      colLat R (mapR (K := K) (W * diagR π 1)) < latOne := by
  have hPQ : mapR (K := K) W * mapR W⁻¹ = 1 := by rw [← mapR_mul, Matrix.mul_nonsing_inv _ hW, mapR_one]
  have hQP : mapR (K := K) W⁻¹ * mapR W = 1 := by rw [← mapR_mul, Matrix.nonsing_inv_mul _ hW, mapR_one]
  have h0 : colLat R (mapR (K := K) W * diagP π 0) = latOne := by
    rw [show diagP (K := K) π 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [diagP], mul_one,
      ← one_mul (mapR (K := K) W), colLat_mul_mapR (Matrix.mul_nonsing_inv _ hW)]
  have := diagP_succ_lt (R := R) hπ hPQ hQP 0
  rw [h0, zero_add, ← mapR_diagR, ← mapR_mul] at this
  exact this

theorem adj_base_nbr {π : R} (hπ : Irreducible π) {W : Matrix (Fin 2) (Fin 2) R} (hW : IsUnit W.det) :
    (bruhatTits R K π).Adj (baseVert R K)
      (latR (K := K) (show (W * diagR π 1).det ≠ 0 by
        rw [Matrix.det_mul]; exact mul_ne_zero hW.ne_zero (diagR_det_ne_zero hπ 1))).cls := by
  rw [bruhatTits_adj_iff hπ]
  left
  obtain ⟨h1, h2⟩ := between_nbr (K := K) hπ hW
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  · change algebraMap R K π • colLat R (mapR (1 : Matrix (Fin 2) (Fin 2) R)) < _
    rw [mapR_one]; exact h1
  · change _ < colLat R (mapR (1 : Matrix (Fin 2) (Fin 2) R))
    rw [mapR_one]; exact h2

/-! ### The neighbours of the base vertex -/

/-- $N_r = \begin{pmatrix}1 & 0\\ r & \pi\end{pmatrix} = \begin{pmatrix}1 & 0\\ r & 1\end{pmatrix}\operatorname{diag}(1,\pi)$. -/
abbrev wFin (r : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; r, 1]

/-- $\begin{pmatrix}0 & 1\\ 1 & 0\end{pmatrix}$; $N_\infty = \operatorname{diag}(\pi, 1)$ has the same column lattice as
$\begin{pmatrix}0&1\\1&0\end{pmatrix}\operatorname{diag}(1,\pi)$. -/
abbrev wInf : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

theorem isUnit_det_wFin (r : R) : IsUnit (wFin r).det := by simp [Matrix.det_fin_two_of]

theorem isUnit_det_wInf : IsUnit (wInf : Matrix (Fin 2) (Fin 2) R).det := by
  simp [Matrix.det_fin_two_of]

theorem det_wd_ne_zero {π : R} (hπ : Irreducible π) {W : Matrix (Fin 2) (Fin 2) R} (hW : IsUnit W.det) :
    (W * diagR π 1).det ≠ 0 := by
  rw [Matrix.det_mul]; exact mul_ne_zero hW.ne_zero (diagR_det_ne_zero hπ 1)

/-- The candidate neighbours of $[R^2]$: $W\operatorname{diag}(1,\pi)R^2$ for $W = W_{\hat a}$ ($a \in k$) or $W_\infty$. -/
def nbrMat : Option (IsLocalRing.ResidueField R) → Matrix (Fin 2) (Fin 2) R
  | some a => wFin (Function.surjInv (IsLocalRing.residue_surjective (R := R)) a)
  | none => wInf

theorem isUnit_det_nbrMat (o : Option (IsLocalRing.ResidueField R)) : IsUnit (nbrMat o).det := by
  cases o with
  | none => exact isUnit_det_wInf
  | some a => exact isUnit_det_wFin _

/-- The candidate neighbour of $[R^2]$ indexed by a point of $\mathbb P^1(k) = k \sqcup \{\infty\}$. -/
def nbrVert {π : R} (hπ : Irreducible π) (o : Option (IsLocalRing.ResidueField R)) : Vert R K :=
  (latR (K := K) (det_wd_ne_zero hπ (isUnit_det_nbrMat o))).cls

/-- Equal candidate classes have equal column lattices. -/
theorem colLat_eq_of_nbrVert_eq {π : R} (hπ : Irreducible π) {o o' : Option (IsLocalRing.ResidueField R)}
    (h : nbrVert (K := K) hπ o = nbrVert hπ o') :
    colLat R (mapR (K := K) (nbrMat o' * diagR π 1)) = colLat R (mapR (K := K) (nbrMat o * diagR π 1)) := by
  unfold nbrVert at h
  obtain ⟨c, hc, hcM⟩ := cls_eq_cls_iff.1 h
  obtain ⟨h1, h2⟩ := between_nbr (K := K) hπ (isUnit_det_nbrMat o)
  obtain ⟨h1', h2'⟩ := between_nbr (K := K) hπ (isUnit_det_nbrMat o')
  exact eq_of_between hπ h1 h2 h1' h2' hc hcM

theorem nbrMat_some (a : IsLocalRing.ResidueField R) :
    nbrMat (some a) = wFin (Function.surjInv (IsLocalRing.residue_surjective (R := R)) a) := rfl

theorem nbrMat_none : nbrMat (none : Option (IsLocalRing.ResidueField R)) = wInf := rfl

theorem wFin_mul_diagR (π r : R) : wFin r * diagR π 1 = !![1, 0; r, π] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wInf_mul_diagR (π : R) : (wInf : Matrix (Fin 2) (Fin 2) R) * diagR π 1 = !![0, π; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The candidate neighbours are pairwise distinct. -/
theorem nbrVert_injective {π : R} (hπ : Irreducible π) : Function.Injective (nbrVert (K := K) hπ) := by
  intro o o' h
  have hcol := colLat_eq_of_nbrVert_eq (K := K) hπ h
  obtain ⟨W, hW, hNW⟩ := exists_eq_mul_of_colLat_eq (det_wd_ne_zero hπ (isUnit_det_nbrMat o))
    (det_wd_ne_zero hπ (isUnit_det_nbrMat o')) hcol
  have e := fun i j => congrFun (congrFun hNW i) j
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some b =>
      exfalso
      rw [nbrMat_some, nbrMat_none, wFin_mul_diagR, wInf_mul_diagR] at e
      have := e 0 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this
      -- `1 = π * W 1 0`
      exact hπ.not_isUnit (IsUnit.of_mul_eq_one _ this.symm)
  | some a =>
    cases o' with
    | none =>
      exfalso
      rw [nbrMat_some, nbrMat_none, wFin_mul_diagR, wInf_mul_diagR] at e
      have e00 := e 0 0
      have e01 := e 0 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      -- first row of `W` is `(0, π)`, so `π ∣ det W`
      have : π ∣ W.det := by
        rw [Matrix.det_fin_two, ← e00, ← e01]; exact ⟨-(W 1 0), by ring⟩
      exact hπ.not_isUnit (isUnit_of_dvd_unit this hW)
    | some b =>
      rw [nbrMat_some, nbrMat_some, wFin_mul_diagR, wFin_mul_diagR] at e
      have e00 := e 0 0
      have e10 := e 1 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      -- `b̂ = â + π W 1 0`
      congr 1
      set f := Function.surjInv (IsLocalRing.residue_surjective (R := R))
      have hb : IsLocalRing.residue R (f b) = b := Function.surjInv_eq _ b
      have ha : IsLocalRing.residue R (f a) = a := Function.surjInv_eq _ a
      rw [← ha, ← hb, e10, ← e00, mul_one, map_add, map_mul]
      have : IsLocalRing.residue R π = 0 :=
        (IsLocalRing.residue_eq_zero_iff π).2 hπ.not_isUnit
      rw [this, zero_mul, add_zero]

/-- Every neighbour of $[R^2]$ is a candidate neighbour. -/
theorem nbrVert_surjective {π : R} (hπ : Irreducible π) {y : Vert R K}
    (hy : (bruhatTits R K π).Adj (baseVert R K) y) : ∃ o, nbrVert (K := K) hπ o = y := by
  obtain ⟨W, hW, rfl⟩ := exists_nbr_eq (K := K) hπ (A := 1) (by simp) hy
  have hWD : (1 : Matrix (Fin 2) (Fin 2) R) * W * diagR π 1 = !![W 0 0, π * W 0 1; W 1 0, π * W 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  -- it suffices to write `W diag(1,π) = N T` with `T ∈ GL₂(R)`
  have key : ∀ (o : Option (IsLocalRing.ResidueField R)) (T : Matrix (Fin 2) (Fin 2) R), IsUnit T.det →
      (1 : Matrix (Fin 2) (Fin 2) R) * W * diagR π 1 = nbrMat o * diagR π 1 * T →
      nbrVert (K := K) hπ o = (latR (K := K) (det_nbr_ne_zero hπ (A := (1 : Matrix (Fin 2) (Fin 2) R)) (by simp) hW)).cls := by
    intro o T hT hNT
    apply congrArg (Quotient.mk _); apply Subtype.ext
    change colLat R (mapR (nbrMat o * diagR π 1)) = colLat R (mapR (1 * W * diagR π 1))
    rw [hNT, mapR_mul (nbrMat o * diagR π 1), colLat_mul_mapR (Matrix.mul_nonsing_inv _ hT)]
  by_cases h0 : IsUnit (W 0 0)
  · obtain ⟨u, hu⟩ := h0
    set f := Function.surjInv (IsLocalRing.residue_surjective (R := R))
    set a := IsLocalRing.residue R (W 1 0 * ((u⁻¹ : Rˣ) : R))
    have hfa : IsLocalRing.residue R (f a) = a := Function.surjInv_eq _ a
    have hdiv : π ∣ W 1 0 - f a * W 0 0 := by
      have h1 : W 1 0 * ((u⁻¹ : Rˣ) : R) - f a ∈ IsLocalRing.maximalIdeal R := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hfa, sub_self]
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
      have : W 1 0 - f a * W 0 0 = (W 1 0 * ((u⁻¹ : Rˣ) : R) - f a) * W 0 0 := by
        rw [← hu, sub_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [this]; exact h1.mul_right _
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨some a, key (some a) !![W 0 0, π * W 0 1; t, W 1 1 - f a * W 0 1] ?_ ?_⟩
    · have : (!![W 0 0, π * W 0 1; t, W 1 1 - f a * W 0 1] : Matrix (Fin 2) (Fin 2) R).det = W.det := by
        rw [Matrix.det_fin_two_of, Matrix.det_fin_two]
        linear_combination (W 0 1) * ht
      rw [this]; exact hW
    · rw [hWD, nbrMat_some, wFin_mul_diagR]
      simp only [f] at ht
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination ht
  · have hm0 : W 0 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h0
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm0
    obtain ⟨s, hs⟩ := hm0
    refine ⟨none, key none !![W 1 0, π * W 1 1; s, W 0 1] ?_ ?_⟩
    · have : (!![W 1 0, π * W 1 1; s, W 0 1] : Matrix (Fin 2) (Fin 2) R).det = -W.det := by
        rw [Matrix.det_fin_two_of, Matrix.det_fin_two, hs]; ring
      rw [this]; exact hW.neg
    · rw [hWD, nbrMat_none, wInf_mul_diagR]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]

/-- The neighbours of $[R^2]$ correspond to $\mathbb P^1(k) = k \sqcup \{\infty\}$. -/
def nbrBase {π : R} (hπ : Irreducible π) :
    Option (IsLocalRing.ResidueField R) ≃ (bruhatTits R K π).neighborSet (baseVert R K) :=
  Equiv.ofBijective (fun o => ⟨nbrVert hπ o, adj_base_nbr hπ (isUnit_det_nbrMat o)⟩)
    ⟨fun o o' h => nbrVert_injective hπ (congrArg Subtype.val h), fun y => by
      obtain ⟨o, ho⟩ := nbrVert_surjective hπ y.2
      exact ⟨o, Subtype.ext ho⟩⟩

/-- **Proposition 23.5.8** (Voight 2021), degree: every vertex of the Bruhat–Tits tree has exactly $\#k + 1$
neighbours ($k$ the residue field; as cardinals in $\mathbb N \cup \{\infty\}$, so $q + 1$ when $\#k = q$). With
`bruhatTits_isTree` this is all of Proposition 23.5.8. -/
@[kb "voight2021" "Proposition 23.5.8, p. 387"]
theorem bruhatTitsDegree {π : R} (hπ : Irreducible π) : BruhatTitsDegree R K π := by
  intro x
  obtain ⟨g, rfl⟩ := smulVert_transitive (baseVert R K) x
  rw [← ENat.card_congr (nbrEquiv (π := π) g (baseVert R K)), ← ENat.card_congr (nbrBase (K := K) hπ),
    ENat.card_congr (Equiv.optionEquivSumPUnit (IsLocalRing.ResidueField R) :
      Option (IsLocalRing.ResidueField R) ≃ IsLocalRing.ResidueField R ⊕ PUnit.{1}), ENat.card_sum]
  simp

end QuadFormsKB.Voight.Wave8
