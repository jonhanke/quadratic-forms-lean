/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ through a preserved overlattice

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$. For the remaining $2$-adic shapes the upper bound
$\theta(O^+(L_2)) \subseteq$ root group cannot come from generation by integral reflections. This file gives a second
route: if every proper integral automorphism of $L_2$ also preserves a lattice $L^+$ whose (scaled) form is even
unimodular, or of the shape $E \perp \langle 2u\rangle$, then Wall's formula computed in a basis of $L^+$ shows that
every element of $\theta(O^+(L_2))$ has even order.

**Layer.** As in `Section9Theorem18DyadicEven.lean`: over $\mathbb Q$ at the prime $v$ over $2$, the form $Q$ on
$\mathbb Q_2^n$ with bilinear form $B(x, y) = Q(x + y) - Q(x) - Q(y)$ (`qbil`), a lattice $L$ with localization $L_2$
(`loc v L.1`), $O(L_2)$ = `locStabV Q v L`, $O^+(V)$ = `Tamagawa.soSub Q Fv`, the matrix $S$ = `mat Q Fv σ` of
$\sigma$, and for a matrix $\gamma' \in GL_n(\mathbb Q_2)$ the lattice $\gamma'\mathbb Z_2^n$ (`locAct v γ' (std v)`)
with Gram matrix $G' = \gamma'^{\mathsf T}H\gamma'$ (`locGram Q v γ'`).

**Defines**
* `EvenSpinor σ`: the spinor norm of $\sigma$ is the class of an element of even order;
* `CanonPred Q L v s t x` (a **condition** on a vector $x$, with parameters $s, t \in \mathbb Q_2$): $sx \in L_2$,
  $\lvert t\,B(x, y)\rvert \le 1$ for all $y \in L_2$, and $\lvert t\,Q(x)\rvert \le 1$. It is defined from $L_2$, $B$
  and $Q$ only, so every $\sigma \in O(L_2)$ preserves it (`canonPred_mulVec`).

**Proves**
* `conj_orth_any`, `conj_integral_of_maps`: for any $\gamma'$, $S' = \gamma'^{-1}S\gamma'$ satisfies
  $S'^{\mathsf T}G'S' = G'$, and it is integral when $\sigma$ maps $\gamma'\mathbb Z_2^n$ into itself;
* `evenSpinor_of_conj_scaledEvenUnimodular`, `evenSpinor_of_conj_glue` (**the upper bound through a preserved
  lattice**): if $S'$ is integral, $\det\sigma = 1$, and $cG'$ is even unimodular (resp. of the shape
  $E \perp \langle 2u\rangle$ of `exists_sq_valued_wallDet_glue'`), then `EvenSpinor σ`;
* `conj_integral_of_canonPred`: if the basis vectors $\gamma' e_k$ satisfy `CanonPred` and every vector satisfying
  `CanonPred` lies in $\gamma'\mathbb Z_2^n$ (the lattice $L^+ = \gamma'\mathbb Z_2^n$ is *characterized* by the
  predicate), then every $\sigma \in O(L_2)$ has $\gamma'^{-1}S\gamma'$ integral;
* `theorem18OnlyIf_of_evenSpinor`: `Theorem18OnlyIf` holds if every proper $\sigma \in O(L_2)$ has `EvenSpinor σ`
  and every unit class lies in the root group.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPeelBinary

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Overlattice

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- For any $\gamma'$, $S' = \gamma'^{-1}S\gamma'$ preserves the Gram matrix $G' = \gamma'^{\mathsf T}H\gamma'$. -/
theorem conj_orth_any (γ : GL (Fin n) Fv) (σ : orthGroup Q Fv) :
    ((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val)ᵀ * locGram Q v γ *
      ((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) = locGram Q v γ := by
  set g := γ.val
  set gi := (γ⁻¹ : GL (Fin n) Fv).val
  have hggi : g * gi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hH := mat_orth σ
  unfold locGram
  change (gi * mat Q Fv σ * g)ᵀ * (gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g) * (gi * mat Q Fv σ * g) =
    gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g
  have hT : giᵀ * gᵀ = 1 := by rw [← transpose_mul, hggi, transpose_one]
  calc (gi * mat Q Fv σ * g)ᵀ * (gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g) * (gi * mat Q Fv σ * g)
      = gᵀ * ((mat Q Fv σ)ᵀ * (giᵀ * gᵀ) * Q.hessian.map (algebraMap ℚ Fv) * (g * gi) * mat Q Fv σ) * g := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = gᵀ * Q.hessian.map (algebraMap ℚ Fv) * g := by
        rw [hT, hggi, Matrix.mul_one, Matrix.mul_one, hH, Matrix.mul_assoc]

/-- $S' = \gamma'^{-1}S\gamma'$ is integral when $\sigma$ maps every basis vector $\gamma' e_j$ into
$\gamma'\mathbb Z_2^n$. -/
theorem conj_integral_of_maps (γ : GL (Fin n) Fv) (σ : orthGroup Q Fv)
    (h : ∀ j, mat Q Fv σ *ᵥ (γ.val *ᵥ Pi.single j 1) ∈ locAct v γ (std v)) :
    ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1 := by
  intro i j
  have := (mem_locAct_std_iff γ _).mp (h j) i
  rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one_apply] at this

variable (Q) in
/-- **$\sigma$ has a spinor norm of even order**: $\theta(\sigma) = xF_2^{\times 2}$ with $\lvert x\rvert = e^{2k}$
for some $k \in \mathbb Z$. -/
def EvenSpinor (σ : orthGroup Q Fv) : Prop :=
  ∃ x : Fv, x ≠ 0 ∧ (∃ k : ℤ, Valued.v x = exp (2 * k)) ∧ spinorNorm Q Fv σ = sqClassOf x

/-- A Wall determinant $d = \det(P^{\mathsf T}GR)$ with $\lvert c^{2m'}d\rvert$ a square has square absolute value. -/
theorem exists_even_of_scaled_sq {c d : Fv} (hc : c ≠ 0) (hd : d ≠ 0) (m' : ℕ) {δ : ℤᵐ⁰}
    (hδ : Valued.v (c ^ (m' + m') * d) = δ ^ 2) : ∃ k : ℤ, Valued.v d = exp (2 * k) := by
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have hvd : Valued.v d = (δ * (Valued.v c ^ m')⁻¹) ^ 2 := by
    rw [map_mul, map_pow] at hδ
    have hcm : Valued.v c ^ (m' + m') ≠ 0 := pow_ne_zero _ hvc
    rw [mul_pow, inv_pow, ← hδ, ← pow_mul, show m' * 2 = m' + m' by ring]
    field_simp
  set δ' := δ * (Valued.v c ^ m')⁻¹
  have hδ'0 : δ' ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero, Valuation.zero_iff] at hvd; exact hd hvd
  refine ⟨log δ', ?_⟩
  rw [hvd, ← exp_log hδ'0, ← WithZero.exp_nsmul, WithZero.log_exp]
  congr 1

/-- **The upper bound through a preserved scaled even unimodular lattice**: let $\gamma' \in GL_n(\mathbb Q_2)$ and
$c \ne 0$ with $A = cG'$ ($G'$ = `locGram Q v γ'`) integral, $\lvert\det A\rvert = 1$ and $A_{kk}/2$ integral. If
$\det\sigma = 1$ and $\gamma'^{-1}S\gamma'$ is integral, then $\theta(\sigma)$ has even order. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (spinor norms of rotations preserving a scaled even unimodular lattice have even order)"]
theorem evenSpinor_of_conj_scaledEvenUnimodular (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {c : Fv}
    (hc : c ≠ 0) (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (hdet : Valued.v (c • locGram Q v γ).det = 1) (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (σ : orthGroup Q Fv) (hσ1 : σ ∈ Tamagawa.soSub Q Fv)
    (hS : ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1) :
    EvenSpinor Q σ := by
  set G := locGram Q v γ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val
  have hS'G : S'ᵀ * G * S' = G := conj_orth_any γ σ
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S'
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  set A := c • G
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hSA : S'ᵀ * A * S' = A := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul]
    rw [hS'G]
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet' A hA (fun i j => by simpa [A] using hint i j) hdet
    (fun i => by simpa [A, mul_div_assoc] using heven i) S' hS hSA hf
  have hm : Even m := by
    have h1 : (mat Q Fv σ).det = 1 := hσ1
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  have hAd : (Pᵀ * A * R).det = c ^ (m' + m') * (Pᵀ * G * R).det := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin]
  rw [hAd] at hδ
  exact ⟨_, hne, exists_even_of_scaled_sq hc hne m' hδ, hθ⟩

/-- **The upper bound through a preserved lattice of the shape $E \perp \langle 2u\rangle$** (scaled): as
`evenSpinor_of_conj_scaledEvenUnimodular`, with $A = cG'$ integral, $A_{kk}/2$ integral, an index $l$ with
$A_{il} = 0$ for $i \ne l$, $A_{ll}/2$ a unit and $\lvert\det A\rvert = \lvert 2\rvert$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (spinor norms of rotations preserving a scaled E ⊥ ⟨2u⟩ have even order)"]
theorem evenSpinor_of_conj_glue (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    {c : Fv} (hc : c ≠ 0) (l : Fin n) (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ≠ l → locGram Q v γ i l = 0) (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (c • locGram Q v γ).det = Valued.v (2 : Fv))
    (σ : orthGroup Q Fv) (hσ1 : σ ∈ Tamagawa.soSub Q Fv)
    (hS : ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1) :
    EvenSpinor Q σ := by
  set G := locGram Q v γ
  set S' := (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val
  have hS'G : S'ᵀ * G * S' = G := conj_orth_any γ σ
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame S'
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  set A := c • G
  have hA : Aᵀ = A := by simp only [A, transpose_smul, G, locGram_transpose]
  have hSA : S'ᵀ * A * S' = A := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul]
    rw [hS'G]
  have h1 : (mat Q Fv σ).det = 1 := hσ1
  have hS'det : S'.det = 1 := by
    have hgig : (γ⁻¹ : GL (Fin n) Fv).val * γ.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg Matrix.det hgig
    rw [det_mul, det_one] at this
    simp only [S', det_mul, h1, mul_one]
    exact this
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet_glue' A l (c * G l l / 2) hA
    (fun i j => by simpa [A] using hint i j) (fun i => by simpa [A, mul_div_assoc] using heven i)
    (fun i hi => by simp [A, G, hl i hi]) (by simp only [A, Matrix.smul_apply, smul_eq_mul]; ring) hu
    (valued_two_dyadic v h2) hdet S' hS hSA hS'det hf
  have hm : Even m := by
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  have hAd : (Pᵀ * A * R).det = c ^ (m' + m') * (Pᵀ * G * R).det := by
    simp only [A, Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin]
  rw [hAd] at hδ
  exact ⟨_, hne, exists_even_of_scaled_sq hc hne m' hδ, hθ⟩

variable (Q L v) in
/-- **The canonical predicate** (a **condition** on a vector $x \in \mathbb Q_2^n$, parameters $s, t$):
$sx \in L_2$, $\lvert t\,B(x, y)\rvert \le 1$ for every $y \in L_2$, and $\lvert t\,Q(x)\rvert \le 1$. -/
def CanonPred (s t : Fv) (x : Fin n → Fv) : Prop :=
  s • x ∈ loc v L.1 ∧ (∀ y ∈ loc v L.1, Valued.v (t * qbil Q Fv x y) ≤ 1) ∧ Valued.v (t * Q.evalIn Fv x) ≤ 1

/-- $Q(Sx) = Q(x)$ for $\sigma \in O(V)$. -/
theorem evalIn_mat_mulVec (σ : orthGroup Q Fv) (x : Fin n → Fv) :
    Q.evalIn Fv (mat Q Fv σ *ᵥ x) = Q.evalIn Fv x := by
  have h := qbil_orth Q Fv σ x x
  have e1 := two_mul_evalIn_eq Q Fv (mat Q Fv σ *ᵥ x)
  have e2 := two_mul_evalIn_eq Q Fv x
  apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
  rw [e1, e2]
  exact h

/-- **Every $\sigma \in O(L_2)$ preserves the canonical predicate.** -/
theorem canonPred_mulVec {σ : orthGroup Q Fv} (hσ : σ ∈ locStabV Q v L) {s t : Fv} {x : Fin n → Fv}
    (hx : CanonPred Q L v s t x) : CanonPred Q L v s t (mat Q Fv σ *ᵥ x) := by
  have hσM : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, fun y hy => ?_, ?_⟩
  · rw [← mulVec_smul]
    rw [← hσM]
    exact ⟨_, h1, rfl⟩
  · rw [← hσM] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := qbil_orth Q Fv σ x z
    change Valued.v (t * qbil Q Fv (mat Q Fv σ *ᵥ x) (mat Q Fv σ *ᵥ z)) ≤ 1
    rw [this]
    exact h2 z hz
  · rw [evalIn_mat_mulVec]; exact h3

/-- **A lattice characterized by the canonical predicate is preserved by $O(L_2)$**: if every basis vector
$\gamma' e_k$ satisfies `CanonPred Q L v s t` and every vector satisfying it lies in $\gamma'\mathbb Z_2^n$, then for
every $\sigma \in O(L_2)$ the matrix $\gamma'^{-1}S\gamma'$ is integral. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (a canonically defined overlattice is preserved by the integral automorphisms)"]
theorem conj_integral_of_canonPred (γ : GL (Fin n) Fv) {s t : Fv}
    (hbasis : ∀ k, CanonPred Q L v s t (γ.val *ᵥ Pi.single k 1))
    (hchar : ∀ x, CanonPred Q L v s t x → x ∈ locAct v γ (std v)) {σ : orthGroup Q Fv}
    (hσ : σ ∈ locStabV Q v L) :
    ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1 :=
  conj_integral_of_maps γ σ fun j => hchar _ (canonPred_mulVec hσ (hbasis j))

/-! ### The canonical predicate for an arbitrary local lattice, and chains of overlattices -/

variable (Q) in
/-- **The canonical predicate relative to a local lattice $M$** (a **condition** on $x \in \mathbb Q_2^n$, parameters
$s, t, r$): $sx \in M$, $\lvert t\,B(x, y)\rvert \le 1$ for every $y \in M$, and $\lvert r\,Q(x)\rvert \le 1$. For
$M = L_2$ and $r = t$ this is `CanonPred`. -/
def CanonPredM (M : Submodule (v.adicCompletionIntegers ℚ) (Fin n → Fv)) (s t r : Fv) (x : Fin n → Fv) : Prop :=
  s • x ∈ M ∧ (∀ y ∈ M, Valued.v (t * qbil Q Fv x y) ≤ 1) ∧ Valued.v (r * Q.evalIn Fv x) ≤ 1

/-- Every $\sigma \in O(V)$ with $\sigma M = M$ preserves `CanonPredM Q M s t r`. -/
theorem canonPredM_mulVec {M : Submodule (v.adicCompletionIntegers ℚ) (Fin n → Fv)} {σ : orthGroup Q Fv}
    (hσ : locAct v (σ : GL (Fin n) Fv) M = M) {s t r : Fv} {x : Fin n → Fv}
    (hx : CanonPredM Q M s t r x) : CanonPredM Q M s t r (mat Q Fv σ *ᵥ x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, fun y hy => ?_, ?_⟩
  · rw [← mulVec_smul, ← hσ]
    exact ⟨_, h1, rfl⟩
  · rw [← hσ] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := qbil_orth Q Fv σ x z
    change Valued.v (t * qbil Q Fv (mat Q Fv σ *ᵥ x) (mat Q Fv σ *ᵥ z)) ≤ 1
    rw [this]
    exact h2 z hz
  · rw [evalIn_mat_mulVec]; exact h3

/-- If $\gamma'^{-1}S\gamma'$ is integral, $\sigma$ maps $\gamma'\mathbb Z_2^n$ into itself. -/
theorem locAct_le_of_conj_integral (γ : GL (Fin n) Fv) (g : GL (Fin n) Fv)
    (h : ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * g.val * γ.val) i j) ≤ 1) :
    locAct v g (locAct v γ (std v)) ≤ locAct v γ (std v) := by
  rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  have hd1 := mem_std_iff.mp hd
  refine ⟨((γ⁻¹ : GL (Fin n) Fv).val * g.val * γ.val) *ᵥ d, mem_std_iff.mpr fun i => ?_, ?_⟩
  · simp only [mulVec, dotProduct]
    exact valued_sum_le_one _ _ fun j _ => valued_mul_le_one (h i j) (hd1 j)
  · change γ.val *ᵥ (((γ⁻¹ : GL (Fin n) Fv).val * g.val * γ.val) *ᵥ d) = g.val *ᵥ (γ.val *ᵥ d)
    rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, mulVec_mulVec]

/-- **Stability is inherited by a lattice characterized by the canonical predicate**: if $\sigma$ preserves
$M = \gamma\mathbb Z_2^n$, the basis vectors $\gamma' e_k$ satisfy `CanonPredM Q M s t r`, and every vector satisfying
it lies in $M' = \gamma'\mathbb Z_2^n$, then $\sigma M' = M'$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (a canonically defined overlattice of a local lattice is preserved by its automorphisms)"]
theorem stab_of_canonPredM (γ γ' : GL (Fin n) Fv) {s t r : Fv}
    (hbasis : ∀ k, CanonPredM Q (locAct v γ (std v)) s t r (γ'.val *ᵥ Pi.single k 1))
    (hchar : ∀ x, CanonPredM Q (locAct v γ (std v)) s t r x → x ∈ locAct v γ' (std v)) {σ : orthGroup Q Fv}
    (hσ : locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v)) :
    locAct v (σ : GL (Fin n) Fv) (locAct v γ' (std v)) = locAct v γ' (std v) := by
  have hσi : locAct v ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) := by
    have := (locAct_eq_iff.mp hσ).symm
    simpa using this
  have hle : ∀ τ : orthGroup Q Fv,
      locAct v (τ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) →
      locAct v (τ : GL (Fin n) Fv) (locAct v γ' (std v)) ≤ locAct v γ' (std v) := fun τ hτ =>
    locAct_le_of_conj_integral γ' _ (conj_integral_of_maps γ' τ fun j => hchar _ (canonPredM_mulVec hτ (hbasis j)))
  refine le_antisymm (hle σ hσ) ?_
  have h2 := hle σ⁻¹ hσi
  intro x hx
  have hx' : (((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv)).val *ᵥ x ∈ locAct v γ' (std v) := h2 ⟨x, hx, rfl⟩
  refine ⟨_, hx', ?_⟩
  change (σ : GL (Fin n) Fv).val *ᵥ (((σ : GL (Fin n) Fv)⁻¹).val *ᵥ x) = x
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

variable (Q) in
/-- **Even spinor norms on the stabilizer of $\gamma\mathbb Z_2^n$** (a **condition** on $\gamma$): every rotation
$\sigma \in O^+(V)$ with $\sigma\gamma\mathbb Z_2^n = \gamma\mathbb Z_2^n$ has a spinor norm of even order. -/
def EvenStable (γ : GL (Fin n) Fv) : Prop :=
  ∀ σ : orthGroup Q Fv, σ ∈ Tamagawa.soSub Q Fv →
    locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) → EvenSpinor Q σ

theorem conj_integral_of_stab (γ : GL (Fin n) Fv) {σ : orthGroup Q Fv}
    (hσ : locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v)) :
    ∀ i j, Valued.v (((γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val) i j) ≤ 1 :=
  conj_integral_of_maps γ σ fun j => by
    rw [← hσ]; exact ⟨_, ⟨_, single_mem_std j (by simp), rfl⟩, rfl⟩

/-- `EvenStable` for a scaled even unimodular $\gamma\mathbb Z_2^n$. -/
theorem evenStable_of_scaledEvenUnimodular (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {c : Fv}
    (hc : c ≠ 0) (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (hdet : Valued.v (c • locGram Q v γ).det = 1) (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) :
    EvenStable Q γ := fun σ hσ1 hσ =>
  evenSpinor_of_conj_scaledEvenUnimodular hQ γ hc hint hdet heven σ hσ1 (conj_integral_of_stab γ hσ)

/-- `EvenStable` for a scaled $E \perp \langle 2u\rangle$. -/
theorem evenStable_of_glue (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    {c : Fv} (hc : c ≠ 0) (l : Fin n) (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ≠ l → locGram Q v γ i l = 0) (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (c • locGram Q v γ).det = Valued.v (2 : Fv)) : EvenStable Q γ := fun σ hσ1 hσ =>
  evenSpinor_of_conj_glue hQ h2 γ hc l hint heven hl hu hdet σ hσ1 (conj_integral_of_stab γ hσ)

/-- **One step of a chain of canonical overlattices**: `EvenStable` passes from $\gamma'$ to $\gamma$ when
$\gamma'\mathbb Z_2^n$ is characterized by a canonical predicate relative to $\gamma\mathbb Z_2^n$. -/
theorem evenStable_of_step (γ γ' : GL (Fin n) Fv) {s t r : Fv}
    (hbasis : ∀ k, CanonPredM Q (locAct v γ (std v)) s t r (γ'.val *ᵥ Pi.single k 1))
    (hchar : ∀ x, CanonPredM Q (locAct v γ (std v)) s t r x → x ∈ locAct v γ' (std v))
    (h : EvenStable Q γ') : EvenStable Q γ := fun σ hσ1 hσ =>
  h σ hσ1 (stab_of_canonPredM γ γ' hbasis hchar hσ)

/-- **Theorem 18, "only if", from an even-order upper bound**: if every proper $\sigma \in O(L_2)$ has a spinor norm
of even order and every unit class lies in the root group, then `Theorem18OnlyIf` holds. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if' from an even-order upper bound and the unit classes)"]
theorem theorem18OnlyIf_of_evenSpinor (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (heven : ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L → σ ∈ Tamagawa.soSub Q Fv → EvenSpinor Q σ)
    (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) : Theorem18OnlyIf Q L v hQ := by
  rw [theorem18OnlyIf_iff]
  intro A hA
  obtain ⟨σ, ⟨hσL, hσ1⟩, hσθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hA
  obtain ⟨x, hx0, ⟨k, hk⟩, hθ⟩ := heven σ hσL hσ1
  have hmem := sqClassOf_mem_of_even h2 hunits hx0 k hk
  rw [← hθ, hσθ] at hmem
  exact hmem

/-- **Theorem 18, "only if", from `EvenStable` of a basis of $L_2$** and the unit classes in the root group. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if' from even spinor norms on the stabilizer of L₂)"]
theorem theorem18OnlyIf_of_evenStable (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (hs : EvenStable Q γ)
    (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_evenSpinor hQ h2 (fun σ hσ hσ1 => hs σ hσ1 (by
    have : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
    rwa [hγ] at this)) hunits

end Overlattice

end QuadFormsKB.ConwaySloane
