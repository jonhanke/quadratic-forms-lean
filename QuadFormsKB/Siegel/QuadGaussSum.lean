/-
# Quadratic Gauss sums over a finite field

For a finite field $K$ of odd characteristic, a primitive additive character $\psi : K \to \mathbb{C}$, the quadratic
character $\chi$ of $K$, and a nondegenerate symmetric $n \times n$ matrix $M$ over $K$ with $n = 2k$ even:

* `sum_addChar_mul_sq`: $\sum_{t \in K} \psi(u t^2) = \chi(u)\, g$ for $u \ne 0$, $g = \sum_t \chi(t)\psi(t)$ the Gauss sum;
* `sum_addChar_quadForm`: for $b \ne 0$,
  $$\sum_{\vec{x} \in K^n} \psi\big(b\, \vec{x}^{\mathsf T} M \vec{x}\big) = \chi\big((-1)^k \det M\big)\, |K|^k.$$

*Proof:* an orthogonal basis (Mathlib's `LinearMap.BilinForm.exists_orthogonal_basis`) splits the sum into a
product of one-dimensional sums; $g^2 = \chi(-1)|K|$ (Mathlib's `gaussSum_sq`), and $\prod_i M[\vec{v}_i] = \det(P)^2\det M$
for the matrix $P$ of the basis. Sources: Lidl–Niederreiter, *Finite Fields*, Thm. 5.33 and §6.2 [unverified];
Iwaniec, *Topics in Classical Automorphic Forms*, §10.4 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation

open Finset Matrix

namespace QuadFormsKB.Siegel

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The quadratic character of $K$ with values in $\mathbb{C}$. -/
abbrev quadCharC (K : Type*) [Field K] [Fintype K] [DecidableEq K] : MulChar K ℂ :=
  (quadraticChar K).ringHomComp (Int.castRingHom ℂ)

/-- **One-dimensional quadratic Gauss sums:** for $u \ne 0$,
$\sum_{t \in K}\psi(u t^2) = \chi(u)\, g(\chi, \psi)$, $g(\chi,\psi) = \sum_t \chi(t)\psi(t)$ (Mathlib's `gaussSum`). -/
@[kb "lidl1997" "Thm. 5.33 [unverified]"]
theorem sum_addChar_mul_sq (hK : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) {u : K}
    (hu : u ≠ 0) :
    ∑ t : K, ψ (u * t ^ 2) = quadCharC K u * gaussSum (quadCharC K) ψ := by
  -- count square roots
  have h1 : ∑ t : K, ψ (u * t ^ 2) = ∑ s : K, ((quadraticChar K s : ℂ) + 1) * ψ (u * s) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun t : K => t ^ 2) (fun t => ψ (u * t ^ 2))]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ∀ t ∈ (Finset.univ.filter fun t : K => t ^ 2 = s), ψ (u * t ^ 2) = ψ (u * s) := by
      intro t ht; rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := quadraticChar_card_sqrts hK s
    have : (Finset.univ.filter fun t : K => t ^ 2 = s) = {x : K | x ^ 2 = s}.toFinset := by
      ext; simp
    rw [this]
    exact_mod_cast hc
  rw [h1]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : K, ψ (u * s) = 0 := by
    have := AddChar.sum_mulShift (ψ := ψ) u hψ
    rw [if_neg hu] at this
    simpa [mul_comm] using this
  rw [h2, add_zero]
  have h3 : ∑ s : K, (quadraticChar K s : ℂ) * ψ (u * s) =
      gaussSum (quadCharC K) (ψ.mulShift u) := by
    simp [gaussSum, AddChar.mulShift_apply]
  rw [h3]
  have := gaussSum_mulShift_eq (quadCharC K) ψ (Units.mk0 u hu)
  rw [Units.val_mk0] at this
  rw [this, ((quadraticChar_isQuadratic K).comp (Int.castRingHom ℂ)).inv]

/-- An additive character maps finite sums to products. -/
lemma addChar_sum {ι : Type*} (ψ : AddChar K ℂ) (s : Finset ι) (f : ι → K) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]

/-- **Quadratic Gauss sums of a nondegenerate even-dimensional form over a finite field.** Let $K$ be a finite field
of odd characteristic, $\psi$ a primitive additive character, $\chi$ the quadratic character, and $M$ a symmetric
$n \times n$ matrix over $K$ with $\det M \ne 0$ and $n = 2k$. For $b \ne 0$,
$$\sum_{\vec{x} \in K^n} \psi\big(b\,\vec{x}^{\mathsf T}M\vec{x}\big) = \chi\big((-1)^k\det M\big)\,|K|^k.$$ -/
@[kb "lidl1997" "§6.2, Thm. 6.26-type evaluation [unverified]"]
theorem sum_addChar_quadForm (hK : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {n k : ℕ} (hn : n = 2 * k) (M : Matrix (Fin n) (Fin n) K) (hM : Mᵀ = M) (hdet : M.det ≠ 0)
    {b : K} (hb : b ≠ 0) :
    ∑ x : Fin n → K, ψ (b * (x ⬝ᵥ M *ᵥ x)) =
      quadCharC K ((-1) ^ k * M.det) * (Fintype.card K : ℂ) ^ k := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  set B : LinearMap.BilinForm K (Fin n → K) := Matrix.toBilin' M with hBdef
  have hBapp : ∀ x y, B x y = x ⬝ᵥ M *ᵥ y := fun x y => Matrix.toBilin'_apply' M x y
  have hB : LinearMap.IsSymm B := by
    refine ⟨fun x y => ?_⟩
    rw [RingHom.id_apply, hBapp, hBapp, dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  set v' := v.reindex (finCongr (Module.finrank_fin_fun K)) with hv'def
  have hv' : ∀ i j, i ≠ j → B (v' i) (v' j) = 0 := by
    intro i j hij
    simp only [hv'def, Module.Basis.reindex_apply]
    exact hv (by simpa using hij)
  set w : Fin n → K := fun i => B (v' i) (v' i) with hw
  -- the form in the orthogonal basis
  have hdiag : ∀ y : Fin n → K, B (∑ i, y i • v' i) (∑ i, y i • v' i) = ∑ i, w i * y i ^ 2 := by
    intro y
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hv' j i hji]; ring)
      (by simp)]
    simp only [hw]; ring
  -- the basis matrix `P`
  set P : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => v' j i with hP
  have hPmul : ∀ y : Fin n → K, P *ᵥ y = ∑ j, y j • v' j := by
    intro y; funext i
    simp [hP, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPmul] at hy
    have := (Fintype.linearIndependent_iff.mp v'.linearIndependent) y hy
    exact hy0 (funext this)
  have hPMP : Pᵀ * M * P = Matrix.diagonal w := by
    ext i j
    have : (Pᵀ * M * P) i j = B (v' i) (v' j) := by
      rw [hBapp]
      simp [hP, Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; rfl
    · exact hv' i j hij
  have hprodw : ∏ i, w i = P.det ^ 2 * M.det := by
    have := congrArg Matrix.det hPMP
    rw [det_diagonal, det_mul, det_mul, det_transpose] at this
    rw [← this]; ring
  have hw0 : ∀ i, w i ≠ 0 := by
    have : ∏ i, w i ≠ 0 := by rw [hprodw]; exact mul_ne_zero (pow_ne_zero _ hPdet) hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp this) i (Finset.mem_univ _)
  -- change variables and split
  have hsum : ∑ x : Fin n → K, ψ (b * (x ⬝ᵥ M *ᵥ x)) = ∏ i, ∑ t : K, ψ ((b * w i) * t ^ 2) := by
    rw [← Fintype.sum_equiv v'.equivFun.symm.toEquiv (fun y => ψ (b * (B (∑ i, y i • v' i)
      (∑ i, y i • v' i)))) _ (fun y => by
        simp only [LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply, hBapp])]
    simp_rw [hdiag, Finset.mul_sum, addChar_sum]
    rw [Fintype.prod_sum]
    refine Fintype.sum_congr _ _ fun y => Finset.prod_congr rfl fun i _ => by ring_nf
  rw [hsum]
  simp_rw [fun i => sum_addChar_mul_sq hK hψ (mul_ne_zero hb (hw0 i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_prod]
  have hg := gaussSum_sq (quadraticChar_ne_one hK |> fun h => by
      rwa [Ne, MulChar.ringHomComp_eq_one_iff (RingHom.injective_int (Int.castRingHom ℂ))])
    ((quadraticChar_isQuadratic K).comp (Int.castRingHom ℂ)) hψ
  rw [show gaussSum (quadCharC K) ψ ^ n = (gaussSum (quadCharC K) ψ ^ 2) ^ k by
      rw [← pow_mul, hn], hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hprodw]
  have hb2 : quadCharC K (b ^ n) = 1 := by
    rw [hn, pow_mul, map_pow]
    simp only [quadCharC, MulChar.ringHomComp_apply, quadraticChar_sq_one' hb]; simp
  have hP2 : quadCharC K (P.det ^ 2) = 1 := by
    simp only [quadCharC, MulChar.ringHomComp_apply, quadraticChar_sq_one' hPdet]; simp
  rw [map_mul, hb2, map_mul, hP2, mul_pow, map_mul, map_pow]
  ring

end

end QuadFormsKB.Siegel