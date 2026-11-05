/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for (scaled) even unimodular $L_2$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$, for the $2$-adic Jordan shape "one even
(type II) constituent": $L_2 = 2^kE$ with $E$ even unimodular.

**Layer.** As in `Section9Theorem18DyadicRootGroup.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G = \gamma^{\mathsf T}H\gamma$ of $B(x, y) = Q(x + y) - Q(x) - Q(y)$
(`locGram`, so $G_{kk} = 2Q(b_k)$). The shape is `IsScaledEvenUnimodular`: for some $c \in \mathbb Q_2^\times$ the
matrix $A = cG$ is integral, $\lvert\det A\rvert = 1$, and every $A_{kk}$ is even (the lattice $L_2$ with the
bilinear form $cB$ is even unimodular). The earlier files (`Section9EvenUnimodular.lean`, `Section9DyadicEven.lean`)
treat the standard lattice $\mathbb Z^n$ of an integer Gram matrix; here the lattice and its basis are arbitrary.

**Proves**
* `exists_sq_valued_wallDet'` (the core lemma of `Section9EvenUnimodular.lean` for an arbitrary matrix $A$ over
  $\mathbb Q_2$ with integral entries, $\lvert\det A\rvert = 1$ and $A_{kk}/2$ integral): the Wall determinants
  $\det(P^{\mathsf T}AR)$ of an integral $S$ with $S^{\mathsf T}AS = A$ have square valuation;
* `spinorNorm_eq_wallDet_conj`: for $\sigma \in O(L_2)$, $S' = \gamma^{-1}\sigma\gamma$ is integral with
  $S'^{\mathsf T}GS' = G$, and $\theta(\sigma) = \det(P'^{\mathsf T}GR')$ for a Wall frame $(P', R')$ of $S'$;
* `even_log_of_scaledEvenUnimodular`: every element of $\theta(O^+(L_2))$ has even order;
* `exists_rootVector_of_scaledEvenUnimodular`: for every unit $w$ there is a $2$-adic root vector of norm $c^{-1}w$
  (two basis vectors $b_{i_0}, b_j$ with $A_{i_0j}$ a unit span a binary sublattice
  $c^{-1}(\alpha s^2 + \beta st + \delta t^2)$, $\beta$ a unit, which represents every unit);
* `theorem18OnlyIf_of_scaledEvenUnimodular` (**Theorem 18, "only if", at $p = 2$ for $L_2 = 2^kE$, $E$ even
  unimodular**): $\theta(O^+(L_2)) = \mathbb Z_2^\times\mathbb Q_2^{\times 2}$ is the root group.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicRootGroup
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicGlue

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-! ### The core lemma for a matrix over $\mathbb Q_2$ -/

/-- For an integral vector $x$ and a symmetric integral matrix $A$ over $\mathbb Q_2$ with $A_{ii}/2$ integral,
$\tfrac12 x^{\mathsf T}Ax$ is integral. -/
theorem valued_half_quad_le_one' {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) (hA : Aᵀ = A)
    (hint : ∀ i j, Valued.v (A i j) ≤ 1) (heven : ∀ i, Valued.v (A i i / 2) ≤ 1) (x : Fin N → Fv)
    (hx : ∀ i, Valued.v (x i) ≤ 1) : Valued.v ((x ⬝ᵥ (A *ᵥ x)) / 2) ≤ 1 := by
  classical
  set Lm : Matrix (Fin N) (Fin N) Fv :=
    Matrix.of fun i j => if j < i then A i j else if i = j then A i i / 2 else 0
  have hsymA : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  have hdec : A = Lm + Lmᵀ := by
    ext i j
    simp only [Lm, Matrix.add_apply, transpose_apply, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [not_lt_of_gt h, ne_of_lt h, h, ite_false, ite_true, zero_add, hsymA]
    · simp only [lt_irrefl, ite_false, ite_true]
      ring_nf
    · simp only [not_lt_of_gt h, ne_of_gt h, ne_of_lt h, h, ite_false, ite_true, add_zero]
  have hLt : x ⬝ᵥ (Lmᵀ *ᵥ x) = x ⬝ᵥ (Lm *ᵥ x) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  have e : (x ⬝ᵥ (A *ᵥ x)) / 2 = x ⬝ᵥ (Lm *ᵥ x) := by
    conv_lhs => rw [hdec]
    rw [add_mulVec, dotProduct_add, hLt]
    ring
  rw [e]
  refine valued_sum_le_one _ _ fun i _ => valued_mul_le_one (hx i) ?_
  refine valued_sum_le_one _ _ fun j _ => valued_mul_le_one ?_ (hx j)
  simp only [Lm, of_apply]
  split_ifs with h1 h2
  · exact hint _ _
  · subst h2; exact heven _
  · simp

/-- **The core lemma over $\mathbb Q_2$** (`EvenUnimodular.exists_sq_valued_wallDet` for an arbitrary matrix): if
$A$ is symmetric with integral entries, $\lvert\det A\rvert = 1$ and every $A_{ii}/2$ integral, and $S$ is integral
with $S^{\mathsf T}AS = A$, then every Wall frame $(P, R)$ of $S$ has $\lvert\det(P^{\mathsf T}AR)\rvert$ a square. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers of an even unimodular lattice)"]
theorem exists_sq_valued_wallDet' {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) (hA : Aᵀ = A)
    (hint : ∀ i j, Valued.v (A i j) ≤ 1) (hdetA : Valued.v A.det = 1) (heven : ∀ i, Valued.v (A i i / 2) ≤ 1)
    (S : Matrix (Fin N) (Fin N) Fv) (hS : ∀ i j, Valued.v (S i j) ≤ 1) (hSA : Sᵀ * A * S = A) {m : ℕ}
    {P R : Matrix (Fin N) (Fin m) Fv} (hf : IsWallFrame Fv S P R) :
    ∃ γ : ℤᵐ⁰, Valued.v (Pᵀ * A * R).det = γ ^ 2 := by
  classical
  obtain ⟨m', W, W', f, Z, a, hW, hW', hWW', hW'W, hZ, ha, hframe, hspan⟩ := exists_snf_frame S hS
  set P0 : Matrix (Fin N) (Fin m') Fv := Matrix.of fun i j => W i (f j)
  set R0 : Matrix (Fin N) (Fin m') Fv := Z * Matrix.diagonal fun j => (a j)⁻¹
  have hP0 : ∀ i j, Valued.v (P0 i j) ≤ 1 := fun i j => hW _ _
  set U := P0ᵀ * A * Z
  have hU : ∀ k j, Valued.v (U k j) ≤ 1 :=
    mul_integral _ _ (mul_integral _ _ (fun i j => hP0 j i) hint) hZ
  have hC : P0ᵀ * A * R0 = U * Matrix.diagonal fun j => (a j)⁻¹ := by
    simp only [R0, U, Matrix.mul_assoc]
  have hdet0 : A.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdetA; exact zero_ne_one hdetA
  have hAinv : ∀ i j, Valued.v (A⁻¹ i j) ≤ 1 := Glue.inv_integral A hint hdetA
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0)
  have hcolP0 : ∀ k, (fun i => P0 i k) = (1 - S) *ᵥ (fun i => R0 i k) := fun k => by
    ext i; rw [← mul_apply_col, hframe.1]
  have hright : ∀ i, ∃ r : Fin m' → Fv, (∀ j, Valued.v (r j) ≤ 1) ∧
      ∀ k, (U *ᵥ r) k = if k = i then 1 else 0 := by
    intro i
    set e : Fin N → Fv := Pi.single (f i) 1
    set w : Fin N → Fv := A⁻¹ *ᵥ (W'ᵀ *ᵥ e)
    have hw : ∀ l, Valued.v (w l) ≤ 1 := by
      refine mulVec_integral _ _ hAinv (mulVec_integral _ _ (fun i j => hW' j i) fun l => ?_)
      simp only [e, Pi.single_apply]; split_ifs <;> simp
    obtain ⟨r, hr, hTr⟩ := hspan w hw
    refine ⟨r, hr, fun k => ?_⟩
    have hfix : S *ᵥ (w - Z *ᵥ r) = w - Z *ᵥ r := by
      have h0 : (1 - S) *ᵥ (w - Z *ᵥ r) = 0 := by rw [mulVec_sub, hTr, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
      exact h0.symm
    have horth := orth_ker_mat hSA (fun i => R0 i k) _ hfix
    rw [← hcolP0, mulVec_sub, dotProduct_sub, sub_eq_zero] at horth
    have h1 : (fun l => P0 l k) ⬝ᵥ (A *ᵥ w) = if k = i then 1 else 0 := by
      have e1 : A *ᵥ w = W'ᵀ *ᵥ e := by
        rw [mulVec_mulVec, hAAinv, one_mulVec]
      have e2 : (fun l => P0 l k) = W *ᵥ Pi.single (f k) 1 := by
        ext l; simp [P0, mulVec, dotProduct, Pi.single_apply]
      rw [e1, e2, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← transpose_mul,
        hW'W, transpose_one, one_mulVec, dotProduct_single, mul_one]
      simp only [e, Pi.single_apply, f.injective.eq_iff]
    have h2 : (fun l => P0 l k) ⬝ᵥ (A *ᵥ (Z *ᵥ r)) = (U *ᵥ r) k := by
      rw [show U *ᵥ r = (P0ᵀ * A) *ᵥ (Z *ᵥ r) by rw [mulVec_mulVec]]
      rw [← mulVec_mulVec]
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

/-! ### Transport to a basis of $L_2$ -/

section Transport

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n}

theorem mulVec_single_one_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) Fv) (i j : Fin N) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

/-- **An integral automorphism in a basis of $L_2$**: for $\sigma \in O(L_2)$ and $L_2 = \gamma\mathfrak o^n$, the
matrix $S' = \gamma^{-1}S\gamma$ is integral and $S'^{\mathsf T}GS' = G$ ($G$ = `locGram Q v γ`). -/
theorem conj_integral_orth (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {σ : orthGroup Q Fv}
    (hσ : σ ∈ locStabV Q v L) :
    (∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1) ∧
      ((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val)ᵀ * locGram Q v γ *
        ((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) = locGram Q v γ := by
  set g := γ.val
  set gi := (γ⁻¹ : GL (Fin n) Fv).val
  have hggi : g * gi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨fun i j => ?_, ?_⟩
  · have hbj : g *ᵥ Pi.single j 1 ∈ loc v L.1 := by
      rw [hγ]; exact ⟨Pi.single j 1, single_mem_std j (by simp), rfl⟩
    have hσb : mat Q Fv σ *ᵥ (g *ᵥ Pi.single j 1) ∈ loc v L.1 := by
      have : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
      rw [← this]; exact ⟨_, hbj, rfl⟩
    rw [hγ, mem_locAct_std_iff] at hσb
    have := hσb i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one_apply] at this
  · have hH := mat_orth σ
    unfold locGram
    change (gi * mat Q Fv σ * g)ᵀ * (gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g) * (gi * mat Q Fv σ * g) =
      gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g
    have hT : giᵀ * gᵀ = 1 := by rw [← transpose_mul, hggi, transpose_one]
    calc (gi * mat Q Fv σ * g)ᵀ * (gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g) * (gi * mat Q Fv σ * g)
        = gᵀ * ((mat Q Fv σ)ᵀ * (giᵀ * gᵀ) * Q.hessian.map (algebraMap ℚ Fv) * (g * gi) * mat Q Fv σ) * g := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g := by
          rw [hT, hggi, Matrix.mul_one, Matrix.mul_one, hH, Matrix.mul_assoc]

/-- **Wall frames in a basis of $L_2$**: a Wall frame $(P', R')$ of $S' = \gamma^{-1}S\gamma$ gives the Wall frame
$(\gamma P', \gamma R')$ of $S$, whose Gram matrix is $P'^{\mathsf T}GR'$. So $\theta(\sigma) = \det(P'^{\mathsf
T}GR')F_2^{\times 2}$, the determinant is nonzero, and $\det\sigma = (-1)^m$. -/
theorem spinorNorm_eq_wallDet_conj (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) (σ : orthGroup Q Fv) {m : ℕ}
    {P R : Matrix (Fin n) (Fin m) Fv}
    (hf : IsWallFrame Fv ((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) P R) :
    spinorNorm Q Fv σ = sqClassOf (Pᵀ * locGram Q v γ * R).det ∧ (Pᵀ * locGram Q v γ * R).det ≠ 0 ∧
      (mat Q Fv σ).det = (-1) ^ m := by
  set g := γ.val
  set gi := (γ⁻¹ : GL (Fin n) Fv).val
  set S := mat Q Fv σ
  have hggi : g * gi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgig : gi * g = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hT : (1 - S) = g * (1 - gi * S * g) * gi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hggi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hggi,
      Matrix.one_mul, Matrix.mul_assoc, hggi, Matrix.mul_one]
  obtain ⟨h1, h2, h3⟩ := hf
  have hf' : IsWallFrame Fv S (g * P) (g * R) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hT, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gi, hgig, Matrix.one_mul, h1]
    · intro c hc
      apply h2
      have := congrArg (fun z => gi *ᵥ z) hc
      simp only [mulVec_mulVec, ← Matrix.mul_assoc, hgig, Matrix.one_mul, mulVec_zero] at this
      exact this
    · intro z
      obtain ⟨c, hc⟩ := h3 (gi *ᵥ z)
      refine ⟨c, ?_⟩
      rw [hT, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_mulVec]
  obtain ⟨hθ, hne, hdet⟩ := wall_formula hQ σ hf'
  have hG : wallGram Q Fv (g * P) (g * R) = Pᵀ * locGram Q v γ * R := by
    simp only [wallGram, locGram, transpose_mul, Matrix.mul_assoc]
    rfl
  rw [hG] at hθ hne
  exact ⟨hθ, hne, hdet⟩

end Transport

/-! ### The shape and the upper bound -/

section Shape

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n}

/-- **The shape "one even Jordan constituent"**: $L_2 = 2^kE$ with $E$ even unimodular, i.e. for some basis
$b_k = \gamma e_k$ of $L_2$ (`loc v L.1 = locAct v γ (std v)`) and some $c \in \mathbb Q_2^\times$ the matrix
$A = cG$, $G$ = `locGram Q v γ` the Gram matrix of $B$, has (i) integral entries, (ii) $\lvert\det A\rvert = 1$ and
(iii) $A_{kk}/2$ integral for every $k$ (the lattice $L_2$ with the bilinear form $cB$ is even unimodular). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic Jordan shape: a single even unimodular constituent, scaled)"]
def IsScaledEvenUnimodular (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (c : v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ c ≠ 0 ∧
    (∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1) ∧ Valued.v (c • locGram Q v γ).det = 1 ∧
    ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1

/-- **The upper bound for $L_2 = 2^kE$**: every element of $\theta(O^+(L_2))$ has even order (Wall's formula and the
core lemma `exists_sq_valued_wallDet'` for $A = cG$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers of a scaled even unimodular lattice have even order)"]
theorem even_log_of_scaledEvenUnimodular (hQ : Q.Nondegenerate)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1) (hdet : Valued.v (c • locGram Q v γ).det = 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (B : Fvˣ)
    (hB : B ∈ localSpinorNormGroup Q hQ v L) : ∃ k : ℤ, Valued.v (B : Fv) = exp (2 * k) := by
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hB
  set G := locGram Q v γ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val
  obtain ⟨hS', hS'G⟩ := conj_integral_orth γ hγ hσL
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S'
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  set A := c • G
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hSA : S'ᵀ * A * S' = A := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul]
    rw [show S'ᵀ * G * S' = G from hS'G]
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet' A hA (fun i j => by simpa [A] using hint i j) hdet
    (fun i => by simpa [A, mul_div_assoc] using heven i) S' hS' hSA hf
  have hm : Even m := by
    have h1 : (mat Q Fv σ).det = 1 := hσS
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  set d := (Pᵀ * G * R).det
  have hAd : (Pᵀ * A * R).det = c ^ (m' + m') * d := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin, d]
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have hvd : Valued.v d = (δ * (Valued.v c ^ m')⁻¹) ^ 2 := by
    have h := hδ
    rw [hAd, map_mul, map_pow] at h
    have hcm : Valued.v c ^ (m' + m') ≠ 0 := pow_ne_zero _ hvc
    rw [mul_pow, inv_pow, ← h, ← pow_mul, show m' * 2 = m' + m' by ring]
    field_simp
  set δ' := δ * (Valued.v c ^ m')⁻¹
  have hδ'0 : δ' ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero, Valuation.zero_iff] at hvd; exact hne hvd
  rw [hθ, sqClassOf_of_ne_zero hne] at hσB
  set D : Fvˣ := Units.mk0 d hne
  have h1 : SqClass.mk (B⁻¹ * D) = 1 := by
    rw [SqClass.mk_mul, hσB, ← SqClass.mk_mul, inv_mul_cancel]
    rfl
  obtain ⟨y, hy⟩ := (SqClass.mk_eq_one_iff (B⁻¹ * D)).mp h1
  have hBe : (B : Fv) = d * ((y : Fv) ^ 2)⁻¹ := by
    have : B = D * (y ^ 2)⁻¹ := by rw [hy]; group
    rw [this]; simp [D]
  have hsv : Valued.v (y : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  refine ⟨log δ' - log (Valued.v (y : Fv)), ?_⟩
  rw [hBe, map_mul, map_inv₀, map_pow, hvd, ← exp_log hδ'0, ← exp_log hsv, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.log_exp, WithZero.log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ### Root vectors -/

/-- A row of an integral matrix with $\lvert\det\rvert = 1$ has a unit entry. -/
theorem exists_unit_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) (hint : ∀ i j, Valued.v (A i j) ≤ 1)
    (hdet : Valued.v A.det = 1) (i : Fin N) : ∃ j, Valued.v (A i j) = 1 := by
  by_contra hno
  push Not at hno
  have hlt : ∀ j, Valued.v (A i j) < 1 := fun j => lt_of_le_of_ne (hint i j) (hno j)
  have hadj := Glue.adjugate_integral A hint
  have e : A.det = ∑ j, A i j * A.adjugate j i := by
    have := congrFun (congrFun (Matrix.mul_adjugate A) i) i
    rw [Matrix.mul_apply] at this
    rw [this]; simp
  have : Valued.v A.det < 1 := by
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact Levels.lt_one_of_lt_le (hlt j) (hadj j i)
  rw [hdet] at this
  exact lt_irrefl _ this

/-- **Root vectors of a scaled even unimodular $L_2$**: in the setting of `IsScaledEvenUnimodular` with $n \ge 1$,
for every unit $w$ of $\mathbb Z_2$ there is a $2$-adic root vector of norm $c^{-1}w$. *Proof.* Pick $i_0$ and $j$ with
$A_{i_0j}$ a unit (`exists_unit_entry`; $j \ne i_0$ as $A_{i_0i_0}$ is even). On $x = \gamma(se_{i_0} + te_j)$,
$cQ(x) = \alpha s^2 + \beta st + \delta t^2$ with $\alpha = A_{i_0i_0}/2$, $\beta = A_{i_0j}$, $\delta = A_{jj}/2$,
which represents $w$ (Cassels' `exists_binary_value` after $t = t'/\beta$). The reflection is integral since
$\lvert(Gd)_k\rvert = \lvert c\rvert^{-1}\lvert(Ad)_k\rvert \le \lvert c\rvert^{-1} = \lvert Q(x)\rvert$. -/
theorem exists_rootVector_of_scaledEvenUnimodular (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1) (hdet : Valued.v (c • locGram Q v γ).det = 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (i0 : Fin n) {w : Fv} (hw : Valued.v w = 1) :
    ∃ x, IsRootVector Q L v x ∧ Q.evalIn Fv x = c⁻¹ * w := by
  set G := locGram Q v γ
  have hint' : ∀ i j, Valued.v ((c • G) i j) ≤ 1 := fun i j => by simpa using hint i j
  obtain ⟨j, hj⟩ := exists_unit_entry (c • G) hint' hdet i0
  simp only [Matrix.smul_apply, smul_eq_mul] at hj
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  have hji0 : j ≠ i0 := by
    rintro rfl
    have h := heven j
    have e : c * G j j = 2 * (c * G j j / 2) := by field_simp
    rw [e, map_mul, hv2] at hj
    have : exp (-1 : ℤ) * Valued.v (c * G j j / 2) ≤ exp (-1 : ℤ) :=
      (mul_le_mul' le_rfl h).trans_eq (mul_one _)
    rw [hj] at this
    exact absurd this (by rw [← exp_zero, exp_le_exp]; omega)
  set β := c * G i0 j with hβ
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hj; exact zero_ne_one hj
  have hα1 : Valued.v (c * G i0 i0 / 2) ≤ 1 := heven i0
  have hδ1 : Valued.v (c * G j j / 2 / β ^ 2) ≤ 1 := by
    rw [map_div₀, map_pow, hj, one_pow, div_one]; exact heven j
  have hw0 : IsUnit (toO v w hw.le) := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hw
  obtain ⟨s, t', hst⟩ := exists_binary_value h2 (toO v _ hα1) (toO v _ hδ1) _ hw0
  have hst' : c * G i0 i0 / 2 * (s : Fv) ^ 2 + (s : Fv) * (t' : Fv) + c * G j j / 2 / β ^ 2 * (t' : Fv) ^ 2 = w := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hst
    push_cast at this
    exact this
  set t : Fv := (t' : Fv) / β
  have ht1 : Valued.v t ≤ 1 := by rw [map_div₀, hj, div_one]; exact vle_one t'
  set d : Fin n → Fv := Pi.single i0 (s : Fv) + Pi.single j t with hd
  have hGd : ∀ m, (G *ᵥ d) m = G m i0 * s + G m j * t := by
    intro m
    simp [hd, Matrix.mulVec_add, Matrix.mulVec_single]
    ring
  have hdot : ∀ e : Fin n → Fv, d ⬝ᵥ e = s * e i0 + t * e j := fun e => by
    rw [hd, add_dotProduct, single_dotProduct, single_dotProduct]
  have hji : G j i0 = G i0 j := locGram_symm' γ j i0
  have hdstd : d ∈ std v := (std v).add_mem (single_mem_std i0 (vle_one s)) (single_mem_std j ht1)
  have hQx : Q.evalIn Fv (γ.val *ᵥ d) = c⁻¹ * w := by
    have h2Q := two_mul_evalIn_locGram (Q := Q) (v := v) γ d
    rw [hdot, hGd, hGd, hji] at h2Q
    have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
    have hQd : Q.evalIn Fv (γ.val *ᵥ d) =
        ((s : Fv) * (G i0 i0 * s + G i0 j * t) + t * (G i0 j * s + G j j * t)) / 2 := by
      rw [← h2Q]; field_simp
    have hdt : t * β = t' := by simp only [t]; field_simp
    have hG0 : G i0 j ≠ 0 := fun h => hβ0 (by rw [hβ, h, mul_zero])
    rw [hQd, ← hst', ← hdt, hβ]
    field_simp
    ring
  have hcw : c⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hc) (fun h => by rw [h, map_zero] at hw; exact zero_ne_one hw)
  have hx0 : Q.evalIn Fv (γ.val *ᵥ d) ≠ 0 := by rw [hQx]; exact hcw
  refine ⟨γ.val *ᵥ d, ⟨hx0, symm_mem_of_gram L γ hγ hdstd hx0 fun m => ?_⟩, hQx⟩
  rw [hQx, map_mul, hw, mul_one, hGd]
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have key : Valued.v (c * (G m i0 * s + G m j * t)) ≤ 1 := by
    rw [show c * (G m i0 * s + G m j * t) = (c * G m i0) * s + (c * G m j) * t by ring]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul]; exact mul_le_one' (hint m i0) (vle_one s)
    · rw [map_mul]; exact mul_le_one' (hint m j) ht1
  rw [map_mul] at key
  rw [map_inv₀]
  calc Valued.v (G m i0 * ↑s + G m j * t)
      = (Valued.v c)⁻¹ * (Valued.v c * Valued.v (G m i0 * ↑s + G m j * t)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hvc, one_mul]
    _ ≤ (Valued.v c)⁻¹ * 1 := mul_le_mul' le_rfl key
    _ = (Valued.v c)⁻¹ := mul_one _

/-- **Theorem 18, "only if", at $p = 2$ for $L_2 = 2^kE$, $E$ even unimodular** (Conway–Sloane §9.5, p. 391): every
$A \in \theta(O^+(L_2))$ is, up to squares, the product of the norms of two $2$-adic root vectors. Indeed
$\theta(O^+(L_2)) \subseteq \mathbb Z_2^\times\mathbb Q_2^{\times 2}$ (`even_log_of_scaledEvenUnimodular`), and every
unit $u$ is $Q(x)Q(y)$ up to squares for root vectors of norms $c^{-1}u$ and $c^{-1}$
(`exists_rootVector_of_scaledEvenUnimodular`); in dimension $\le 1$ the group is trivial. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': L₂ a scaled even unimodular lattice)"]
theorem theorem18OnlyIf_of_scaledEvenUnimodular (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hshape : IsScaledEvenUnimodular Q L v) : Theorem18OnlyIf Q L v hQ := by
  obtain ⟨γ, c, hγ, hc, hint, hdet, heven⟩ := hshape
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact theorem18OnlyIf_of_le_one hQ (by norm_num)
  set i0 : Fin n := ⟨0, hn⟩
  have hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
    intro u hu
    obtain ⟨x, hxr, hx⟩ := exists_rootVector_of_scaledEvenUnimodular h2 γ hγ hc hint hdet heven i0 hu
    obtain ⟨y, hyr, hy⟩ :=
      exists_rootVector_of_scaledEvenUnimodular h2 γ hγ hc hint hdet heven i0 (map_one Valued.v)
    have hmem := sqClassOf_mul_mem_rootGroup hxr hyr
    have e : Q.evalIn Fv x * Q.evalIn Fv y = c⁻¹ ^ 2 * u := by rw [hx, hy]; ring
    have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu; exact zero_ne_one hu
    rwa [e, sqClassOf_sq_mul (inv_ne_zero hc) hu0] at hmem
  intro A hA
  obtain ⟨k, hk⟩ := even_log_of_scaledEvenUnimodular hQ γ hγ hc hint hdet heven A hA
  have hmem := sqClassOf_mem_of_even h2 hunits A.ne_zero k hk
  rw [sqClassOf_of_ne_zero A.ne_zero, Units.mk0_val] at hmem
  exact hmem

end Shape

end QuadFormsKB.ConwaySloane
