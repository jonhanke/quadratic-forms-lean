/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, relative chains of canonical overlattices

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicOverlattice.lean` and `Section9Theorem18DyadicPeelTheta.lean`: over
$\mathbb Q$ at the prime $v$ over $2$, a basis $b_k = \gamma e_k$ of a local lattice $M = \gamma\mathbb Z_2^n$ with
Gram matrix $G$ = `locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$), and a set $T$ of basis indices (the *fixed* ones).
Indices are $0$-based.

**Idea.** `EvenStable` (every rotation preserving $M$ has a spinor norm of even order) is proved in
`Section9Theorem18DyadicOverChain.lean` along chains of canonical overlattices. After peeling orthogonal basis vectors
$b_t$, $t \in T$ (`Section9Theorem18DyadicPeelTheta.lean`), only the rotations that **fix** the $b_t$ matter. For
those the chain may use, in addition:
* **rescaling** the fixed vectors: if $\sigma$ preserves $M$ and fixes the $b_t$ (which are orthogonal to the other
  basis vectors), then $\sigma$ preserves the lattice with basis $\lambda_t b_t$ ($t \in T$), $b_i$ ($i \notin T$) for
  any scalars $\lambda_t \ne 0$ (`stab_rescale`);
* **block base cases**: the complement of $T$ is a scaled even unimodular block or a scaled $E \perp \langle 2u\rangle$
  block (the Wall-determinant lemmas `wallSq_of_block_even`, `wallSq_of_block_glue`).
The halving and pair-glue-and-halving steps keep the fixed vectors fixed (up to a scalar).

**Defines**
* `RelEven Q γ T` (a **condition**): every rotation $\sigma$ preserving $\gamma\mathbb Z_2^n$ and fixing the $b_t$,
  $t \in T$, has a spinor norm of even order;
* `diagGL lam hlam` (the diagonal matrix of nonzero scalars, as an element of $GL_n$);
* `RelChain Q v T γ` (a **condition**, an inductive predicate): a block base case, or a rescaling, halving or
  pair-glue-and-halving step leading to a basis with `RelChain`;
* `PeelChainRel Q v γ T ks` (a **condition**): a chain of peeling steps (as in `PeelChainTheta`) ending in a set $T$
  with `RelChain Q v T γ` and an orthogonal basis vector outside $T$.

**Proves**
* `relEven_of_stab`, `relEven_of_half`, `relEven_of_pairHalf`, `relEven_of_rescale`, `relEven_of_block_even`,
  `relEven_of_block_glue`, `relEven_of_relChain`;
* `fixTheta_of_relEven` (`RelEven` plus the unit classes in the root group and one root vector orthogonal to the
  $b_t$ give `FixTheta`), `fixTheta_of_peelChainRel`;
* `theorem18OnlyIf_of_peelChainRel` (**Theorem 18, "only if", at $p = 2$ for a peeling chain followed by a relative
  chain of canonical overlattices**, unconditional).

*Example* (`Section9Theorem18DyadicShapeA.lean`, `theorem18OnlyIf_of_shapeA`): $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$
with $b + c \equiv 0 \pmod 4$ (Conway–Sloane's notation, $Q(x) = x^{\mathsf T}Mx$): peel $b_0$, rescale it by $4$,
then glue $\tfrac12(b_1 + b_2)$ and halve $b_0, b_3$; the complement of $T = \{0\}$ becomes $E \perp \langle 2d\rangle$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual8

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section RelEven

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q) in
/-- **Even spinor norms on the rotations fixing $b_t$, $t \in T$** (a **condition** on a basis $\gamma$ and a set
$T$ of indices): every $\sigma \in O^+(V)$ with $\sigma\gamma\mathbb Z_2^n = \gamma\mathbb Z_2^n$ and
$\sigma b_t = b_t$ ($t \in T$) has a spinor norm of even order. For $T = \emptyset$ this is `EvenStable`. -/
def RelEven (γ : GL (Fin n) Fv) (T : Finset (Fin n)) : Prop :=
  ∀ σ : orthGroup Q Fv, σ ∈ Tamagawa.soSub Q Fv →
    locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) →
    (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) → EvenSpinor Q σ

theorem evenStable_of_relEven_empty {γ : GL (Fin n) Fv} (h : RelEven Q γ ∅) : EvenStable Q γ :=
  fun σ hσ1 hσ => h σ hσ1 hσ (by simp)

/-- **The generic step**: `RelEven` passes from $\gamma'$ to $\gamma$ if every $\sigma$ preserving
$\gamma\mathbb Z_2^n$ and fixing the $b_t$ preserves $\gamma'\mathbb Z_2^n$, and the fixed basis vectors of $\gamma'$
are scalar multiples of those of $\gamma$. -/
theorem relEven_of_stab {γ γ' : GL (Fin n) Fv} {T : Finset (Fin n)}
    (hstab : ∀ σ : orthGroup Q Fv,
      locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      locAct v (σ : GL (Fin n) Fv) (locAct v γ' (std v)) = locAct v γ' (std v))
    (hscal : ∀ t ∈ T, ∃ s : Fv, basisVec γ' t = s • basisVec γ t)
    (h : RelEven Q γ' T) : RelEven Q γ T := by
  intro σ hσ1 hσ hfix
  refine h σ hσ1 (hstab σ hσ hfix) fun t ht => ?_
  obtain ⟨s, hs⟩ := hscal t ht
  rw [hs, mulVec_smul, hfix t ht]

/-- **The halving step, relative version.** -/
theorem relEven_of_half (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {γ : GL (Fin n) Fv} {c : Fv} {C D : Finset (Fin n)}
    (hD : HalfStep.Data Q v γ c C D) {T : Finset (Fin n)} (h : RelEven Q (HalfStep.gamH γ C) T) :
    RelEven Q γ T :=
  relEven_of_stab (fun _ hσ _ => stab_of_canonPredM γ _ (HalfStep.half_canonPred_basis h2 hD)
      (HalfStep.half_mem_of_canonPred hD) hσ)
    (fun t _ => ⟨if t ∈ C then 1 / 2 else 1, by
      simp only [basisVec]
      rw [HalfStep.gamH_val, ← mulVec_mulVec, HalfStep.W_mulVec_single, mulVec_smul]⟩) h

/-- **The pair-glue-and-halving step, relative version** (the glued index $l_1$ is not fixed). -/
theorem relEven_of_pairHalf (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {γ : GL (Fin n) Fv} {c : Fv} {C : Finset (Fin n)}
    {l₁ l₂ : Fin n} (hD : PairHalf.Data Q v γ c C l₁ l₂) {T : Finset (Fin n)} (hl₁T : l₁ ∉ T)
    (h : RelEven Q (PairHalf.gamP γ C hD.hl) T) : RelEven Q γ T :=
  relEven_of_stab (fun _ hσ _ => stab_of_canonPredM γ _ (PairHalf.pairHalf_canonPred_basis h2 hD)
      (PairHalf.pairHalf_mem_of_canonPred h2 hD) hσ)
    (fun t ht => ⟨if t ∈ C then 1 / 2 else 1, by
      have htl : t ≠ l₁ := fun h => hl₁T (h ▸ ht)
      simp only [basisVec]
      rw [PairHalf.gamP_val_mulVec, PairGlue.W_mulVec_single, if_neg htl, HalfStep.W_mulVec_single,
        mulVec_smul]⟩) h

/-- The diagonal matrix of nonzero scalars $\lambda_i$, as an element of $GL_n(F_v)$. -/
def diagGL (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0) : GL (Fin n) Fv :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal lam)
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hlam i)

theorem diagGL_val (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0) :
    ((diagGL lam hlam : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = diagonal lam := rfl

theorem diagGL_inv_val (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0) :
    (((diagGL lam hlam)⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = diagonal fun i => (lam i)⁻¹ := by
  have h1 : (diagGL lam hlam).val * diagonal (fun i => (lam i)⁻¹) = 1 := by
    rw [diagGL_val, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hlam i)
  calc (((diagGL lam hlam)⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)
      = ((diagGL lam hlam)⁻¹ : GL (Fin n) Fv).val * ((diagGL lam hlam).val * diagonal fun i => (lam i)⁻¹) := by
        rw [h1, Matrix.mul_one]
    _ = diagonal fun i => (lam i)⁻¹ := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- The conjugate $(\gamma\Lambda)^{-1}S(\gamma\Lambda) = \Lambda^{-1}(\gamma^{-1}S\gamma)\Lambda$ entrywise. -/
theorem conj_diagGL_apply (γ : GL (Fin n) Fv) (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0)
    (S : Matrix (Fin n) (Fin n) Fv) (i j : Fin n) :
    (((γ * diagGL lam hlam)⁻¹ : GL (Fin n) Fv).val * S * (γ * diagGL lam hlam).val) i j =
      (lam i)⁻¹ * (((γ⁻¹ : GL (Fin n) Fv).val * S * γ.val) i j) * lam j := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, diagGL_inv_val, diagGL_val]
  have : diagonal (fun i => (lam i)⁻¹) * (γ⁻¹ : GL (Fin n) Fv).val * S * (γ.val * diagonal lam) =
      diagonal (fun i => (lam i)⁻¹) * ((γ⁻¹ : GL (Fin n) Fv).val * S * γ.val) * diagonal lam := by
    simp only [Matrix.mul_assoc]
  rw [this, mul_diagonal, diagonal_mul]

/-- If $\sigma$ maps $M'$ into itself and $\sigma^{-1}$ does too, then $\sigma M' = M'$. -/
theorem stab_of_le_le {γ' : GL (Fin n) Fv} {σ : orthGroup Q Fv}
    (h1 : locAct v (σ : GL (Fin n) Fv) (locAct v γ' (std v)) ≤ locAct v γ' (std v))
    (h2 : locAct v ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv) (locAct v γ' (std v)) ≤ locAct v γ' (std v)) :
    locAct v (σ : GL (Fin n) Fv) (locAct v γ' (std v)) = locAct v γ' (std v) := by
  refine le_antisymm h1 ?_
  intro x hx
  have hx' : (((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv)).val *ᵥ x ∈ locAct v γ' (std v) := h2 ⟨x, hx, rfl⟩
  refine ⟨_, hx', ?_⟩
  change (σ : GL (Fin n) Fv).val *ᵥ (((σ : GL (Fin n) Fv)⁻¹).val *ᵥ x) = x
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- One inclusion of `stab_rescale`. -/
theorem le_rescale (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0)
    (h1 : ∀ i, i ∉ T → lam i = 1) {σ : orthGroup Q Fv}
    (hσ : locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v))
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) :
    locAct v (σ : GL (Fin n) Fv) (locAct v (γ * diagGL lam hlam) (std v)) ≤
      locAct v (γ * diagGL lam hlam) (std v) := by
  obtain ⟨L', hL'⟩ := exists_lat_loc_eq v γ
  have hσL : σ ∈ locStabV Q v L' := by
    change locAct v _ (loc v L'.1) = loc v L'.1
    rw [hL']; exact hσ
  obtain ⟨hS', -, F1, F2⟩ := conj_block_data hQ γ hL' hT hσL hfix
  refine locAct_le_of_conj_integral _ _ fun i j => ?_
  rw [conj_diagGL_apply]
  change Valued.v ((lam i)⁻¹ * conjMat γ σ i j * lam j) ≤ 1
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ T
    · rw [F1 j hj i]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, mul_one, inv_mul_cancel₀ (hlam i), map_one]
      · rw [if_neg hij, mul_zero, zero_mul, map_zero]; exact zero_le
    · rw [F2 i hi j hj, mul_zero, zero_mul, map_zero]; exact zero_le
  · by_cases hj : j ∈ T
    · rw [F1 j hj i, if_neg (fun h : i = j => hi (h ▸ hj)), mul_zero, zero_mul, map_zero]; exact zero_le
    · rw [h1 i hi, h1 j hj, inv_one, one_mul, mul_one]; exact hS' i j

/-- **Rescaling the fixed vectors**: if $\sigma$ preserves $\gamma\mathbb Z_2^n$ and fixes the $b_t$ ($t \in T$,
orthogonal to the other basis vectors), then $\sigma$ preserves $\gamma\Lambda\mathbb Z_2^n$ for every diagonal
$\Lambda$ with nonzero entries that are $1$ off $T$. -/
theorem stab_rescale (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0)
    (h1 : ∀ i, i ∉ T → lam i = 1) {σ : orthGroup Q Fv}
    (hσ : locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v))
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) :
    locAct v (σ : GL (Fin n) Fv) (locAct v (γ * diagGL lam hlam) (std v)) =
      locAct v (γ * diagGL lam hlam) (std v) := by
  have hσi : locAct v ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) := by
    have := (locAct_eq_iff.mp hσ).symm
    simpa using this
  have hfixi : ∀ t ∈ T, ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t := by
    intro t ht
    conv_lhs => rw [← hfix t ht]
    change ((σ : GL (Fin n) Fv)⁻¹).val *ᵥ ((σ : GL (Fin n) Fv).val *ᵥ basisVec γ t) = _
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  exact stab_of_le_le (le_rescale hQ γ hT lam hlam h1 hσ hfix) (le_rescale hQ γ hT lam hlam h1 hσi hfixi)

/-- **The rescaling step**: `RelEven` passes from $\gamma\Lambda$ to $\gamma$. -/
theorem relEven_of_rescale (hQ : Q.Nondegenerate) {γ : GL (Fin n) Fv} {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (lam : Fin n → Fv) (hlam : ∀ i, lam i ≠ 0)
    (h1 : ∀ i, i ∉ T → lam i = 1) (h : RelEven Q (γ * diagGL lam hlam) T) : RelEven Q γ T :=
  relEven_of_stab (fun _ hσ hfix => stab_rescale hQ γ hT lam hlam h1 hσ hfix)
    (fun t _ => ⟨lam t, by
      simp only [basisVec]
      rw [Units.val_mul, diagGL_val, ← mulVec_mulVec, mulVec_single_one, ← mulVec_smul]
      congr 1; funext i
      by_cases hit : i = t
      · subst hit; simp
      · simp [hit]⟩) h

/-- **Even spinor norm from Wall squares**: if for every Wall frame $(P, R)$ of $\gamma^{-1}\sigma\gamma$ the
valuation of $\det(P^{\mathsf T}(cG)R)$ is a square, a rotation $\sigma$ has a spinor norm of even order. -/
theorem evenSpinor_of_wallSq (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {c : Fv} (hc : c ≠ 0)
    (σ : orthGroup Q Fv) (hσ1 : σ ∈ Tamagawa.soSub Q Fv)
    (hsq : ∀ {m' : ℕ} {P R : Matrix (Fin n) (Fin m') Fv}, IsWallFrame Fv (conjMat γ σ) P R →
      ∃ δ : ℤᵐ⁰, Valued.v (Pᵀ * (c • locGram Q v γ) * R).det = δ ^ 2) : EvenSpinor Q σ := by
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame (conjMat γ σ)
  obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
  obtain ⟨δ, hδ⟩ := hsq hf
  have hm : Even m := by
    have h1 : (mat Q Fv σ).det = 1 := hσ1
    rw [h1] at hdetm
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
  obtain ⟨m', rfl⟩ := hm
  have hAd : (Pᵀ * (c • locGram Q v γ) * R).det = c ^ (m' + m') * (Pᵀ * locGram Q v γ * R).det := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin]
  rw [hAd] at hδ
  exact ⟨_, hne, exists_even_of_scaled_sq hc hne m' hδ, hθ⟩

/-- **Block base case (relative): a scaled even unimodular block** on the complement of $T$. -/
theorem relEven_of_block_even (hQ : Q.Nondegenerate) {γ : GL (Fin n) Fv} {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = 1) : RelEven Q γ T := by
  intro σ hσ1 hσ hfix
  obtain ⟨L', hL'⟩ := exists_lat_loc_eq v γ
  have hσL : σ ∈ locStabV Q v L' := by
    change locAct v _ (loc v L'.1) = loc v L'.1
    rw [hL']; exact hσ
  exact evenSpinor_of_wallSq hQ γ hc σ hσ1 fun hf =>
    wallSq_of_block_even hQ γ hL' hT hint heven hdet σ hσL hfix hσ1 hf

/-- **Block base case (relative): a scaled $E \perp \langle 2u\rangle$ block** on the complement of $T$. -/
theorem relEven_of_block_glue (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {γ : GL (Fin n) Fv}
    {T : Finset (Fin n)} (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0) (l : Fin n)
    (hlT : l ∉ T) (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ∉ T → i ≠ l → locGram Q v γ i l = 0)
    (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = Valued.v (2 : Fv)) : RelEven Q γ T := by
  intro σ hσ1 hσ hfix
  obtain ⟨L', hL'⟩ := exists_lat_loc_eq v γ
  have hσL : σ ∈ locStabV Q v L' := by
    change locAct v _ (loc v L'.1) = loc v L'.1
    rw [hL']; exact hσ
  exact evenSpinor_of_wallSq hQ γ hc σ hσ1 fun hf =>
    wallSq_of_block_glue hQ h2 γ hL' hT l hlT hint heven hl hu hdet σ hσL hfix hσ1 hf

end RelEven

section RelChain

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q v) in
/-- **Relative chains of canonical overlattices** (a **condition** on a basis $\gamma$, for a set $T$ of fixed
indices; an inductive predicate): the complement of $T$ is a scaled even unimodular block or a scaled
$E \perp \langle 2u\rangle$ block (with the $b_t$, $t \in T$, orthogonal to the other basis vectors); or a rescaling of
the fixed vectors, a halving step (`HalfStep.Data`) or a pair-glue-and-halving step (`PairHalf.Data`, glued index not
in $T$) leads to a basis with `RelChain`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic shapes reached by a chain of canonical overlattices relative to fixed orthogonal vectors)"]
inductive RelChain (T : Finset (Fin n)) : GL (Fin n) (v.adicCompletion ℚ) → Prop
  /-- The complement of $T$ is a scaled even unimodular block. -/
  | blockEven {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ}
      (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (hc : c ≠ 0)
      (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
      (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
      (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = 1) : RelChain T γ
  /-- The complement of $T$ is a scaled $E \perp \langle 2u\rangle$ block. -/
  | blockGlue {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} (l : Fin n)
      (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (hc : c ≠ 0) (hlT : l ∉ T)
      (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
      (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
      (hl : ∀ i, i ∉ T → i ≠ l → locGram Q v γ i l = 0)
      (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
      (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = Valued.v (2 : v.adicCompletion ℚ)) :
      RelChain T γ
  /-- Rescaling the fixed vectors. -/
  | rescale {γ : GL (Fin n) (v.adicCompletion ℚ)} (lam : Fin n → v.adicCompletion ℚ) (hlam : ∀ i, lam i ≠ 0)
      (h1 : ∀ i, i ∉ T → lam i = 1) (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
      (h : RelChain T (γ * diagGL lam hlam)) : RelChain T γ
  /-- A halving step. -/
  | half {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C D : Finset (Fin n)}
      (hD : HalfStep.Data Q v γ c C D) (h : RelChain T (HalfStep.gamH γ C)) : RelChain T γ
  /-- A pair-glue-and-halving step. -/
  | pairHalf {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C : Finset (Fin n)} {l₁ l₂ : Fin n}
      (hD : PairHalf.Data Q v γ c C l₁ l₂) (hl₁T : l₁ ∉ T) (h : RelChain T (PairHalf.gamP γ C hD.hl)) :
      RelChain T γ

/-- **Even spinor norms along a relative chain of canonical overlattices.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (rotations fixing orthogonal vectors and preserving a lattice with a relative chain of canonical overlattices have spinor norms of even order)"]
theorem relEven_of_relChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {T : Finset (Fin n)}
    {γ : GL (Fin n) Fv} (h : RelChain Q v T γ) : RelEven Q γ T := by
  induction h with
  | blockEven hT hc hint heven hdet => exact relEven_of_block_even hQ hT hc hint heven hdet
  | blockGlue l hT hc hlT hint heven hl hu hdet =>
      exact relEven_of_block_glue hQ h2 hT hc l hlT hint heven hl hu hdet
  | rescale lam hlam h1 hT _ ih => exact relEven_of_rescale hQ hT lam hlam h1 ih
  | half hD _ ih => exact relEven_of_half h2 hD ih
  | pairHalf hD hl₁T _ ih => exact relEven_of_pairHalf h2 hD hl₁T ih

/-- **`FixTheta` from `RelEven`**: if every rotation fixing the $b_t$ has a spinor norm of even order, every unit
class lies in the root group, and some root vector $x_0$ is orthogonal to all $b_t$, then `FixTheta Q L v γ T`. -/
theorem fixTheta_of_relEven (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)} (h : RelEven Q γ T)
    (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) {x0 : Fin n → Fv}
    (hx0r : IsRootVector Q L v x0) (hx0t : ∀ t ∈ T, qbil Q Fv x0 (basisVec γ t) = 0) : FixTheta Q L v γ T := by
  have hproper : ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      ((σ : GL (Fin n) Fv).val).det = 1 →
      ∃ xs : List (Fin n → Fv), (∀ x ∈ xs, IsRootVector Q L v x) ∧ Even xs.length ∧
        spinorNorm Q Fv σ = sqClassOf (valProd Q Fv xs) := by
    intro σ hσ hfix hdet
    have hσ' : locAct v (σ : GL (Fin n) Fv) (locAct v γ (std v)) = locAct v γ (std v) := by
      have : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
      rwa [hγ] at this
    obtain ⟨x, hx0, ⟨k, hk⟩, hθ⟩ := h σ hdet hσ' hfix
    obtain ⟨xs, hev, hxr, hcl⟩ := (mem_rootGroup).mp (sqClassOf_mem_of_even h2 hunits hx0 k hk)
    exact ⟨xs, hxr, hev, hθ.trans hcl⟩
  intro σ hσ hfix
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with hd | hd
  · obtain ⟨xs, hxr, hev, hθ⟩ := hproper σ hσ hfix hd
    exact ⟨xs, hxr, by rw [hd, hev.neg_one_pow], hθ⟩
  · have hσ1M : symm Q Fv x0 * σ ∈ locStabV Q v L := mul_mem hx0r.2 hσ
    have hfix1 : ∀ t ∈ T, ((symm Q Fv x0 * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t =
        basisVec γ t := fun t ht => by
      rw [orthGroup_mul_mulVec, hfix t ht]; exact symm_fix Q Fv (hx0t t ht)
    have hdet1 : ((symm Q Fv x0 * σ : orthGroup Q Fv) : GL (Fin n) Fv).val.det = 1 := by
      rw [orthGroup_det_mul, symm_det Q Fv hx0r.1, hd]; norm_num
    obtain ⟨xs, hxr, hev, hθ⟩ := hproper _ hσ1M hfix1 hdet1
    have hσeq : σ = symm Q Fv x0 * (symm Q Fv x0 * σ) := by rw [← mul_assoc, symm_mul_self, one_mul]
    have hxs0 : ∀ z ∈ xs, Q.evalIn Fv z ≠ 0 := fun z hz => (hxr z hz).1
    refine ⟨x0 :: xs, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx0r
      · exact hxr z hz
    · rw [hd, List.length_cons, pow_succ, hev.neg_one_pow, one_mul]
    · have h1 : spinorNorm Q Fv σ =
          spinorNorm Q Fv (symm Q Fv x0) * spinorNorm Q Fv (symm Q Fv x0 * σ) :=
        calc spinorNorm Q Fv σ = spinorNorm Q Fv (symm Q Fv x0 * (symm Q Fv x0 * σ)) := by rw [← hσeq]
          _ = _ := (spinorNormHom Q Fv hQ).map_mul _ _
      have hv : valProd Q Fv (x0 :: xs) = Q.evalIn Fv x0 * valProd Q Fv xs := by simp [valProd]
      rw [h1, hθ, spinorNorm_symm Q Fv hQ hx0r.1, hv, sqClassOf_mul hx0r.1 (valProd_ne_zero Q Fv hxs0)]

variable (Q v) in
/-- **A peeling chain followed by a relative chain of canonical overlattices** (a **condition** on a basis $\gamma$
of $L_2$): given the set $T$ of indices already peeled and a list $ks$ of further indices,
* if $ks$ is empty: `RelChain Q v T γ`, and some basis vector $b_l$, $l \notin T$, is orthogonal to all other basis
  vectors;
* if $ks = k :: ks'$: $k \notin T$, $b_k$ is orthogonal to the other basis vectors,
  $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{k\}$ (the peeling condition of
  `PeelChainTheta`), and `PeelChainRel Q v γ (insert k T) ks'`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling orthogonal basis vectors, then a relative chain of canonical overlattices, p = 2)"]
def PeelChainRel (γ : GL (Fin n) (v.adicCompletion ℚ)) : Finset (Fin n) → List (Fin n) → Prop
  | T, [] => RelChain Q v T γ ∧ ∃ l, l ∉ T ∧ ∀ m, m ≠ l → locGram Q v γ m l = 0
  | T, k :: ks => k ∉ T ∧ (∀ m, m ≠ k → locGram Q v γ m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T →
        Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k)) ∧
      PeelChainRel γ (insert k T) ks

/-- **`FixTheta` along a peeling chain followed by a relative chain.** -/
theorem fixTheta_of_peelChainRel (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v))
    (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) :
    ∀ (ks : List (Fin n)) (T : Finset (Fin n)), (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) →
      PeelChainRel Q v γ T ks → FixTheta Q L v γ T
  | [], T, hT, ⟨hc, l, hlT, hl⟩ => by
    refine fixTheta_of_relEven hQ h2 γ hγ (relEven_of_relChain hQ h2 hc) hunits
      (isRootVector_basis_of_orth γ hγ l hl (locGram_diag_ne_zero hQ γ hl)) fun t ht => ?_
    have hlt : l ≠ t := fun h => hlT (h ▸ ht)
    change qbil Q Fv (basisVec γ l) (basisVec γ t) = 0
    rw [qbil_basisVec]
    exact hT t ht l hlt
  | k :: ks, T, hT, ⟨hkT, hk, hd, hrest⟩ => by
    refine fixTheta_peel hQ h2 γ hγ T k hkT hT hk hd
      (fixTheta_of_peelChainRel hQ h2 γ hγ hunits ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm

/-- **Theorem 18, "only if", for a peeling chain followed by a relative chain of canonical overlattices**
(Conway–Sloane §9.5, p. 391; $p = 2$; unconditional): if $L_2$ has a basis $b = \gamma e$ and a list $ks$ with
`PeelChainRel Q v γ ∅ ks`, and every unit class lies in the root group, then every element of
$\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a peeling chain followed by a relative chain of canonical overlattices)"]
theorem theorem18OnlyIf_of_peelChainRel (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChainRel Q v γ ∅ ks) (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) :
    Theorem18OnlyIf Q L v hQ := by
  intro A hA
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hA
  obtain ⟨xs, hxs, hdet, hθ⟩ :=
    fixTheta_of_peelChainRel hQ h2 γ hγ hunits ks ∅ (by simp) hc σ hσL (by simp)
  have h1 : ((σ : GL (Fin n) Fv).val).det = 1 := hσS
  refine ⟨xs, ?_, hxs, hσB.symm.trans hθ⟩
  rw [h1] at hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdet.symm

end RelChain

end QuadFormsKB.ConwaySloane
