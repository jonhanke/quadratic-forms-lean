/-
# Conway–Sloane, Ch. 15, §9.5: the Wall core lemma for a lattice that is not unimodular

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicEven.lean`: matrices over $F_2$ = `v.adicCompletion ℚ` ($v$ the prime over
$2$), "integral" meaning entries of valuation $\le 1$. A symmetric matrix $A$ with integral entries and integral
$A_{ii}/2$ is the Gram matrix of an even lattice $M = \mathfrak o^N$ for the bilinear form $x^{\mathsf T}Ay$; its dual
lattice is $M^\# = A^{-1}\mathfrak o^N$. A matrix $S$ with $S^{\mathsf T}AS = A$ is an isometry, and
$(1 - S)A^{-1}$ integral means $(1 - \sigma)M^\# \subseteq M$: $\sigma$ acts trivially on the discriminant group
$M^\#/M$.

**Proves**
* `exists_sq_valued_wallDet_of_dual` (**the core lemma without unimodularity**): if $A$ is symmetric, integral, with
  $A_{ii}/2$ integral and $\det A \ne 0$, and $S^{\mathsf T}AS = A$ with $(1 - S)A^{-1}$ integral, then every Wall
  frame $(P, R)$ of $S$ has $\lvert\det(P^{\mathsf T}AR)\rvert$ a square. For $\lvert\det A\rvert = 1$ and $S$ integral
  this is `exists_sq_valued_wallDet'`.

*Proof.* Put $K = (1 - S)A^{-1}$ (integral) and take the Smith normal form frame of $K$ (`exists_snf_frame` applied
to $1 - K$): a basis $W$ of $\mathfrak o^N$, nonzero integral $a_j$ and integral $Z$ with
$K\mathfrak o^N = \bigoplus_j a_j\mathfrak o\,W_{f(j)}$ and $KZ_j = a_jW_{f(j)}$. Then $P_j = W_{f(j)}$,
$R_j = A^{-1}Z_j/a_j$ is a Wall frame of $S$ (every $(1 - S)z = K(Az)$), with Gram matrix
$P^{\mathsf T}AR = U\,\mathrm{diag}(a)^{-1}$, $U = P^{\mathsf T}Z$ integral. $U$ has an integral right inverse: for the
dual basis vector $w = W'^{\mathsf T}e_{f(i)}$ choose integral $r$ with $Kw = KZr$; then $A^{-1}(w - Zr)$ is fixed by
$S$, hence orthogonal to $V_\sigma$, which gives $Ur = e_i$. So $\lvert\det U\rvert = 1$. The symmetric part of the
Gram matrix is $\tfrac12 P^{\mathsf T}AP$ (integral off the diagonal, and on the diagonal because $A$ is even), so the
level lemma (`Levels.exists_sq_prod_valued`) makes $\prod_j\lvert a_j\rvert$ a square.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicEven

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The core lemma without unimodularity** (see the module docstring): for $A$ symmetric, integral, with
$A_{ii}/2$ integral and $\det A \ne 0$, and $S$ with $S^{\mathsf T}AS = A$ and $(1 - S)A^{-1}$ integral (the isometry
acts trivially on the discriminant group of the even lattice with Gram matrix $A$), every Wall frame $(P, R)$ of $S$
has $\lvert\det(P^{\mathsf T}AR)\rvert$ a square. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (Wall determinants of an isometry acting trivially on the discriminant group of an even lattice)"]
theorem exists_sq_valued_wallDet_of_dual {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) (hA : Aᵀ = A)
    (hint : ∀ i j, Valued.v (A i j) ≤ 1) (hdet0 : A.det ≠ 0) (heven : ∀ i, Valued.v (A i i / 2) ≤ 1)
    (S : Matrix (Fin N) (Fin N) Fv) (hSA : Sᵀ * A * S = A)
    (hK : ∀ i j, Valued.v (((1 - S) * A⁻¹) i j) ≤ 1) {m : ℕ}
    {P R : Matrix (Fin N) (Fin m) Fv} (hf : IsWallFrame Fv S P R) :
    ∃ γ : ℤᵐ⁰, Valued.v (Pᵀ * A * R).det = γ ^ 2 := by
  classical
  set K := (1 - S) * A⁻¹ with hKdef
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0)
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet0)
  have hSt : ∀ i j, Valued.v ((1 - K) i j) ≤ 1 := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ (hK i j))
    split_ifs <;> simp
  obtain ⟨m', W, W', f, Z, a, hW, hW', hWW', hW'W, hZ, ha, hframeK, hspan⟩ := exists_snf_frame (1 - K) hSt
  have hKK : (1 : Matrix (Fin N) (Fin N) Fv) - (1 - K) = K := sub_sub_cancel _ _
  rw [hKK] at hspan
  set P0 : Matrix (Fin N) (Fin m') Fv := Matrix.of fun i j => W i (f j)
  set R0 : Matrix (Fin N) (Fin m') Fv := A⁻¹ * Z * Matrix.diagonal fun j => (a j)⁻¹
  have hP0 : ∀ i j, Valued.v (P0 i j) ≤ 1 := fun i j => hW _ _
  have hframe : IsWallFrame Fv S P0 R0 := by
    obtain ⟨h1, h2, h3⟩ := hframeK
    rw [hKK] at h1 h3
    refine ⟨?_, h2, fun z => ?_⟩
    · rw [← h1]
      simp only [R0, hKdef, Matrix.mul_assoc]
    · obtain ⟨c, hc⟩ := h3 (A *ᵥ z)
      refine ⟨c, ?_⟩
      rw [← hc, hKdef, ← mulVec_mulVec, Matrix.mulVec_mulVec z A⁻¹ A, hAinvA, one_mulVec]
  set U := P0ᵀ * Z
  have hU : ∀ k j, Valued.v (U k j) ≤ 1 := mul_integral _ _ (fun i j => hP0 j i) hZ
  have hC : P0ᵀ * A * R0 = U * Matrix.diagonal fun j => (a j)⁻¹ := by
    simp only [R0, U, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A, hAAinv, Matrix.one_mul]
  have hcolP0 : ∀ k, (fun i => P0 i k) = (1 - S) *ᵥ (fun i => R0 i k) := fun k => by
    ext i; rw [← mul_apply_col, hframe.1]
  have hright : ∀ i, ∃ r : Fin m' → Fv, (∀ j, Valued.v (r j) ≤ 1) ∧
      ∀ k, (U *ᵥ r) k = if k = i then 1 else 0 := by
    intro i
    set e : Fin N → Fv := Pi.single (f i) 1
    set w : Fin N → Fv := W'ᵀ *ᵥ e
    have hw : ∀ l, Valued.v (w l) ≤ 1 := by
      refine mulVec_integral _ _ (fun i j => hW' j i) fun l => ?_
      simp only [e, Pi.single_apply]; split_ifs <;> simp
    obtain ⟨r, hr, hTr⟩ := hspan w hw
    refine ⟨r, hr, fun k => ?_⟩
    set y := A⁻¹ *ᵥ (w - Z *ᵥ r) with hy
    have hfix : S *ᵥ y = y := by
      have h0 : (1 - S) *ᵥ y = 0 := by
        rw [hy, mulVec_mulVec, ← hKdef, mulVec_sub, hTr, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
      exact h0.symm
    have horth := orth_ker_mat hSA (fun i => R0 i k) _ hfix
    rw [← hcolP0, hy, mulVec_mulVec, hAAinv, one_mulVec, dotProduct_sub, sub_eq_zero] at horth
    have h1 : (fun l => P0 l k) ⬝ᵥ w = if k = i then 1 else 0 := by
      have e2 : (fun l => P0 l k) = W *ᵥ Pi.single (f k) 1 := by
        ext l; simp [P0, mulVec, dotProduct, Pi.single_apply]
      rw [e2, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← transpose_mul,
        hW'W, transpose_one, one_mulVec, dotProduct_single, mul_one]
      simp only [e, Pi.single_apply, f.injective.eq_iff]
    have h2 : (fun l => P0 l k) ⬝ᵥ (Z *ᵥ r) = (U *ᵥ r) k := by
      rw [show U *ᵥ r = P0ᵀ *ᵥ (Z *ᵥ r) by rw [mulVec_mulVec]]
      simp only [mulVec, dotProduct, transpose_apply]
    rw [← h2, ← horth, h1]
  choose r hr hUr using hright
  set V : Matrix (Fin m') (Fin m') Fv := Matrix.of fun j i => r i j
  have hUV : U * V = 1 := by
    ext k i
    rw [mul_apply_col]
    have : (fun j => V j i) = r i := rfl
    rw [this, hUr, Matrix.one_apply]
  have hdetU : Valued.v U.det = 1 := by
    have h1 := congrArg (fun M => Valued.v (Matrix.det M)) hUV
    simp only [det_mul, map_mul, det_one, map_one] at h1
    have hu := valued_det_le_one U hU
    have hv := valued_det_le_one V fun j i => hr i j
    by_contra hne
    have hlt : Valued.v U.det < 1 := lt_of_le_of_ne hu hne
    have := Levels.lt_one_of_lt_le hlt hv
    rw [h1] at this
    exact lt_irrefl _ this
  have hsymm := wall_symm_id hA hSA hframe.1
  rw [hC] at hsymm
  have hCe : ∀ k j, (U * Matrix.diagonal fun j => (a j)⁻¹) k j = U k j / a j := fun k j => by
    simp [mul_diagonal, div_eq_mul_inv]
  have hPP : ∀ k j, Valued.v ((P0ᵀ * A * P0) k j) ≤ 1 :=
    mul_integral _ _ (mul_integral _ _ (fun i j => hP0 j i) hint) hP0
  have hsym' : ∀ k j, Valued.v (U k j / a j + U j k / a k) ≤ 1 := by
    intro k j
    have := congrFun (congrFun hsymm k) j
    rw [Matrix.add_apply, transpose_apply, hCe, hCe] at this
    rw [this]; exact hPP k j
  have hdiag' : ∀ k, Valued.v (U k k / a k) ≤ 1 := by
    intro k
    have := congrFun (congrFun hsymm k) k
    rw [Matrix.add_apply, transpose_apply, hCe, gram_apply'] at this
    have e : U k k / a k = ((fun l => P0 l k) ⬝ᵥ (A *ᵥ fun l => P0 l k)) / 2 := by
      rw [← this]; ring
    rw [e]
    exact valued_half_quad_le_one' A hA hint heven _ fun l => hP0 l k
  obtain ⟨γ0, hγ0⟩ := Levels.exists_sq_prod_valued U a hU hdetU (fun j => (ha j).1) (fun j => (ha j).2)
    hsym' hdiag'
  obtain rfl := wallFrame_size_eq hf hframe
  obtain ⟨u, hu0, hu⟩ := wallDet_eq_mat hSA hframe hf
  refine ⟨Valued.v u * γ0⁻¹, ?_⟩
  rw [hu, hC, map_mul, det_mul, map_mul, map_pow, det_diagonal, hdetU, one_mul, map_prod]
  simp only [map_inv₀]
  rw [Finset.prod_inv_distrib, hγ0, mul_pow, inv_pow]

end QuadFormsKB.ConwaySloane
