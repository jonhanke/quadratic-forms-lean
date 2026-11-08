/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, peeling with an orthogonal partner

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it, at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicPeel.lean` and `Section9Theorem18DyadicPeelTheta.lean`: over $\mathbb Q$ at
the prime $v$ over $2$, a basis $b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ` of $B$
($G_{kk} = 2Q(b_k)$), the reflections $\tau_x$ (`symm`), the $2$-adic root vectors (`IsRootVector`). Indices are
$0$-based.

**The peeling step with a partner.** The peeling step of `exists_peel_reflections` moves $y = \sigma b_k$ back to
$\pm b_k$ by root reflections, assuming $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for **all** remaining indices.
Here one remaining index $j$ may violate this: $b_j$ is orthogonal to all other basis vectors and
$\lvert G_{jj}\rvert = \lvert G_{kk}\rvert$ (in Conway–Sloane's notation $b_k, b_j$ span $2^e\langle a, b\rangle$ with
$a, b$ units, the other remaining vectors lie deeper). *Proof.* Write $y = s b_k + d_j b_j + z'$. From
$Q(y) = Q(b_k)$: $G_{kk}(1 - s^2) = G_{jj}d_j^2 + z'^{\mathsf T}Gz'$ with $\lvert z'^{\mathsf T}Gz'\rvert \le
\lvert 2G_{kk}\rvert$.
* If $1 - s$ is a unit, $w = y - b_k$ has $Q(w) = G_{kk}(1 - s)$ of the same absolute value as $G_{kk}$, and
  $\lvert B(w, x)\rvert \le \lvert G_{kk}\rvert$ on $L_2$, so $\tau_w \in O(L_2)$.
* Otherwise $\lvert 1 - s^2\rvert \le \lvert 1 - s\rvert \le \lvert 2\rvert$, so $\lvert 1 - \varepsilon s\rvert =
  \lvert 2\rvert$ for a sign $\varepsilon$ (`exists_sign_of_sq`), and $\lvert G_{jj}d_j^2\rvert \le \lvert 2G_{kk}\rvert$
  forces $\lvert d_j\rvert \le \lvert 2\rvert$; then $w = y - \varepsilon b_k$ has $\lvert Q(w)\rvert = \lvert 2G_{kk}\rvert$
  and $\lvert B(w, x)\rvert \le \lvert 2G_{kk}\rvert$ on $L_2$.
In both cases $\tau_w y = \varepsilon b_k$, and (if $\varepsilon = -1$) $\tau_{b_k}$ finishes.

**Defines** `PeelChainPair Q v γ T ks` (a **condition**): a chain of peeling steps, each either of the
`PeelChainTheta` kind or with a partner, ending in a remainder of rank $\le 2$, a scaled even unimodular or
$E \perp \langle 2u\rangle$ block, or a relative chain of canonical overlattices (`RelChain`) together with an
orthogonal basis vector outside $T$ and `UnitRoots Q v γ` or `UnitRootsBlock Q v γ` (root vectors of every unit
norm inside a block).

**Proves** `exists_peel_reflections_pair`, `fixTheta_peel_pair`, `fixTheta_of_peelChainPair`,
`theorem18OnlyIf_of_peelChainPair` (**Theorem 18, "only if", at $p = 2$ for peeling chains with partners**,
unconditional).

*Examples* (checked by computer; Conway–Sloane's notation, $Q(x) = x^{\mathsf T}Mx$):
$\langle a, b\rangle \perp 16\langle c, d\rangle$ (peel $b_0$ with partner $b_1$, then $b_1$; remainder of rank $2$),
$\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$ (peel $b_0$ with partner $b_1$, then $b_1$,
$b_2$), $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicRelChain

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section PeelPair

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- $(Gc)_k = G_{kk}c_k$ when $b_k$ is orthogonal to the other basis vectors. -/
theorem gram_mulVec_orth (γ : GL (Fin n) Fv) {k : Fin n} (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (c : Fin n → Fv) : (locGram Q v γ *ᵥ c) k = locGram Q v γ k k * c k := by
  have hk' : ∀ m, m ≠ k → locGram Q v γ k m = 0 := fun m hm => by rw [locGram_symm']; exact hk m hm
  unfold mulVec dotProduct
  rw [Finset.sum_eq_single k]
  · intro i _ hi; show locGram Q v γ k i * c i = 0; rw [hk' i hi, zero_mul]
  · simp

/-- **The peeling step with an orthogonal partner, with the reflections made explicit.** Let $b_t$ ($t \in T$),
$b_k$ and $b_j$ ($k \ne j$, both outside $T$) be orthogonal to all other basis vectors, with
$\lvert G_{jj}\rvert = \lvert G_{kk}\rvert$ and $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for
$i, i' \notin T \cup \{j, k\}$. Then every $\sigma \in O(L_2)$ fixing the $b_t$ factors as
$\sigma = \tau_{x_1}\cdots\tau_{x_r}\sigma'$ with $r \le 2$, the $x_i$ $2$-adic root vectors orthogonal to all $b_t$, and
$\sigma' \in O(L_2)$ fixing the $b_t$ for $t \in T \cup \{k\}$. (See the module docstring.) -/
theorem exists_peel_reflections_pair (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n)) (k j : Fin n) (hkT : k ∉ T) (hjT : j ∉ T)
    (hjk : j ≠ k)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hj : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    (hjj : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ k k))
    (hd : ∀ i i', i ∉ insert k (insert j T) → i' ∉ insert k (insert j T) →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    (σ : orthGroup Q Fv) (hσ : σ ∈ locStabV Q v L)
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) :
    ∃ (l : List (Fin n → Fv)) (σ' : orthGroup Q Fv),
      (∀ u ∈ l, IsRootVector Q L v u ∧ ∀ t ∈ T, qbil Q Fv u (basisVec γ t) = 0) ∧
      σ = symmProd Q Fv l * σ' ∧ σ' ∈ locStabV Q v L ∧
      ∀ t ∈ insert k T, (σ' : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t := by
  have hGkk : locGram Q v γ k k ≠ 0 := locGram_diag_ne_zero hQ γ hk
  have hGtt : ∀ t ∈ T, locGram Q v γ t t ≠ 0 := fun t ht => locGram_diag_ne_zero hQ γ (hT t ht)
  have hbkM : basisVec γ k ∈ loc v L.1 := by
    rw [hγ]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  have hσM : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
  have hyM : (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k ∈ loc v L.1 := by
    have : (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k ∈ locAct v (σ : GL (Fin n) Fv) (loc v L.1) :=
      ⟨_, hbkM, rfl⟩
    rwa [hσM] at this
  set y := (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k with hy
  obtain ⟨d, hdstd, hyd⟩ : ∃ d ∈ std v, γ.val *ᵥ d = y := by rw [hγ] at hyM; exact hyM
  have hdle := mem_std_iff.mp hdstd
  have hbt : ∀ t ∈ T, qbil Q Fv y (basisVec γ t) = 0 := by
    intro t ht
    have h := qbil_orth Q Fv σ (basisVec γ k) (basisVec γ t)
    change qbil Q Fv y ((σ : GL (Fin n) Fv).val *ᵥ basisVec γ t) = _ at h
    rw [hfix t ht, qbil_basisVec] at h
    rw [h]; exact hT t ht k (fun h => hkT (h ▸ ht))
  have hdt : ∀ t ∈ T, d t = 0 := by
    intro t ht
    have := hbt t ht
    rw [← hyd, qbil_vec_basisVec γ (hT t ht)] at this
    exact (mul_eq_zero.mp this).resolve_right (hGtt t ht)
  set s := d k with hs
  set dj := d j with hdj
  set zr : Fin n → Fv := Function.update (Function.update d k 0) j 0 with hzr
  have hzr_j : zr j = 0 := by simp [hzr]
  have hzr_k : zr k = 0 := by simp [hzr, hjk.symm]
  have hzr_i : ∀ i, i ≠ k → i ≠ j → zr i = d i := fun i hik hij => by
    simp [hzr, hik, hij]
  set z : Fin n → Fv := zr + Pi.single j dj with hz
  have hzk : z k = 0 := by simp [hz, hzr_k, hjk.symm]
  have hdz : d = z + Pi.single k s := by
    ext i
    by_cases hik : i = k
    · subst hik; simp [hz, hzr_k, hjk.symm, hs]
    · by_cases hij : i = j
      · subst hij; simp [hz, hzr_j, hik, hdj]
      · simp [hz, hzr_i i hik hij, hik, hij]
  have hTj : ∀ t ∈ insert j T, ∀ m, m ≠ t → locGram Q v γ m t = 0 := by
    intro t ht m hm
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hj m hm
    · exact hT t ht m hm
  have hzrsupp : ∀ i ∈ insert k (insert j T), zr i = 0 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hzr_k
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hzr_j
      · have hik : i ≠ k := fun h => hkT (h ▸ hi)
        have hij : i ≠ j := fun h => hjT (h ▸ hi)
        rw [hzr_i i hik hij]; exact hdt i hi
  have hzr1 : ∀ i, Valued.v (zr i) ≤ 1 := fun i => by
    by_cases hik : i = k
    · subst hik; rw [hzr_k, map_zero]; exact zero_le
    · by_cases hij : i = j
      · subst hij; rw [hzr_j, map_zero]; exact zero_le
      · rw [hzr_i i hik hij]; exact hdle i
  have hs1 : Valued.v s ≤ 1 := hdle k
  have hdj1 : Valued.v dj ≤ 1 := hdle j
  have hRb : Valued.v (zr ⬝ᵥ (locGram Q v γ *ᵥ zr)) ≤ Valued.v (2 * locGram Q v γ k k) :=
    valued_dot_gram_le γ hTj hk hd hzrsupp hzr1 hzr1
  have hyy : qbil Q Fv y y = locGram Q v γ k k := by
    have h := qbil_orth Q Fv σ (basisVec γ k) (basisVec γ k)
    rw [qbil_basisVec] at h
    exact h
  have hyk : qbil Q Fv y (basisVec γ k) = s * locGram Q v γ k k := by
    rw [← hyd, qbil_vec_basisVec γ hk]
  have hquad : locGram Q v γ k k = zr ⬝ᵥ (locGram Q v γ *ᵥ zr) + locGram Q v γ j j * dj ^ 2 +
      locGram Q v γ k k * s ^ 2 := by
    rw [← dot_gram_split γ hj zr hzr_j dj, ← hz, ← dot_gram_split γ hk z hzk s, ← hdz,
      ← qbil_mulVec_locGram, hyd]
    exact hyy.symm
  have hrel : locGram Q v γ k k * (1 - s ^ 2) =
      zr ⬝ᵥ (locGram Q v γ *ᵥ zr) + locGram Q v γ j j * dj ^ 2 := by
    linear_combination hquad
  set bk := basisVec γ k with hbk
  have hbky : qbil Q Fv bk y = s * locGram Q v γ k k := by rw [qbil_comm]; exact hyk
  have hbkbk : qbil Q Fv bk bk = locGram Q v γ k k := qbil_basisVec γ k k
  -- the norm of `y - ε b_k`
  have hQw : ∀ ε : Fv, ε * ε = 1 → Q.evalIn Fv (y - ε • bk) = locGram Q v γ k k * (1 - ε * s) := by
    intro ε hεε
    have hqww : qbil Q Fv (y - ε • bk) (y - ε • bk) = 2 * locGram Q v γ k k * (1 - ε * s) := by
      simp only [qbil_sub_left, qbil_sub_right, qbil_smul_left, qbil_smul_right']
      rw [hyy, hyk, hbky, hbkbk]
      linear_combination (locGram Q v γ k k) * hεε
    have h := two_mul_evalIn_eq Q Fv (y - ε • bk)
    rw [hqww] at h
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    linear_combination h
  -- the inner products of `y - ε b_k` with the lattice
  have hBw : ∀ (ε : Fv) (c : Fin n → Fv), qbil Q Fv (y - ε • bk) (γ.val *ᵥ c) =
      zr ⬝ᵥ (locGram Q v γ *ᵥ c) + dj * (locGram Q v γ j j * c j) +
        (s - ε) * (locGram Q v γ k k * c k) := by
    intro ε c
    have hq1 : qbil Q Fv y (γ.val *ᵥ c) = zr ⬝ᵥ (locGram Q v γ *ᵥ c) + dj * (locGram Q v γ j j * c j) +
        s * (locGram Q v γ k k * c k) := by
      rw [← hyd, qbil_mulVec_locGram, hdz, hz, add_dotProduct, add_dotProduct, single_dotProduct,
        single_dotProduct, gram_mulVec_orth γ hj, gram_mulVec_orth γ hk]
    have hq2 : qbil Q Fv bk (γ.val *ᵥ c) = locGram Q v γ k k * c k := by
      rw [hbk]
      show qbil Q Fv (γ.val *ᵥ Pi.single k 1) (γ.val *ᵥ c) = _
      rw [qbil_mulVec_locGram, single_dotProduct, one_mul, gram_mulVec_orth γ hk]
    rw [qbil_sub_left, qbil_smul_left, hq1, hq2]
    ring
  have hwM : ∀ ε : Fv, (ε = 1 ∨ ε = -1) → y - ε • bk ∈ loc v L.1 := by
    intro ε hε
    have hεbk : ε • bk ∈ loc v L.1 := by
      rcases hε with rfl | rfl
      · simpa using hbkM
      · simpa using (loc v L.1).neg_mem hbkM
    exact (loc v L.1).sub_mem hyM hεbk
  have hv2le : Valued.v (2 : Fv) ≤ 1 := (valued_two_lt_one h2).le
  have hGkk0 : Valued.v (locGram Q v γ k k) ≠ 0 := (Valuation.ne_zero_iff _).mpr hGkk
  -- choose the sign and prove that `y - ε b_k` is a root vector
  obtain ⟨ε, hε, hroot⟩ : ∃ ε : Fv, (ε = 1 ∨ ε = -1) ∧ IsRootVector Q L v (y - ε • bk) := by
    have h1s : Valued.v (1 - s) ≤ 1 := Valuation.map_sub_le _ (map_one _).le hs1
    by_cases hu : Valued.v (1 - s) = 1
    · -- `1 - s` a unit: reflect in `y - b_k`
      have hQw1 := hQw 1 (by ring)
      have hvw : Valued.v (Q.evalIn Fv (y - (1 : Fv) • bk)) = Valued.v (locGram Q v γ k k) := by
        rw [hQw1, one_mul, map_mul, hu, mul_one]
      have hw0 : Q.evalIn Fv (y - (1 : Fv) • bk) ≠ 0 := by
        intro h0; rw [h0, map_zero] at hvw; exact hGkk0 hvw.symm
      refine ⟨1, Or.inl rfl, hw0, ?_⟩
      show locAct v (symm Q Fv (y - (1 : Fv) • bk) : GL (Fin n) Fv) (loc v L.1) = loc v L.1
      refine locAct_symm_eq (hwM 1 (Or.inl rfl)) hw0 fun x hx => ?_
      rw [hγ, mem_locAct] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have hc1 := mem_std_iff.mp hc
      rw [hBw, hvw]
      refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
      · calc _ ≤ Valued.v (2 * locGram Q v γ k k) := valued_dot_gram_le γ hTj hk hd hzrsupp hzr1 hc1
          _ ≤ 1 * Valued.v (locGram Q v γ k k) := by rw [map_mul]; exact mul_le_mul' hv2le le_rfl
          _ = _ := one_mul _
      · rw [map_mul, map_mul, hjj]
        calc Valued.v dj * (Valued.v (locGram Q v γ k k) * Valued.v (c j))
            ≤ 1 * (Valued.v (locGram Q v γ k k) * 1) := mul_le_mul' hdj1 (mul_le_mul' le_rfl (hc1 j))
          _ = _ := by rw [one_mul, mul_one]
      · rw [map_mul, map_mul, show s - 1 = -(1 - s) by ring, Valuation.map_neg, hu, one_mul]
        calc Valued.v (locGram Q v γ k k) * Valued.v (c k) ≤ Valued.v (locGram Q v γ k k) * 1 :=
              mul_le_mul' le_rfl (hc1 k)
          _ = _ := mul_one _
    · -- `1 - s` not a unit: the sign of `exists_sign_of_sq`
      have hlt : Valued.v (1 - s) < 1 := lt_of_le_of_ne h1s hu
      have h1p : Valued.v (1 + s) ≤ 1 := Valuation.map_add_le _ (map_one _).le hs1
      have hbnd : Valued.v (1 - s ^ 2) ≤ Valued.v (2 : Fv) := by
        refine valued_le_two_of_lt_one h2 (lt_of_le_of_lt ?_ hlt)
        rw [show 1 - s ^ 2 = (1 - s) * (1 + s) by ring, map_mul]
        calc _ ≤ Valued.v (1 - s) * 1 := mul_le_mul' le_rfl h1p
          _ = _ := mul_one _
      obtain ⟨ε, hε, hεv⟩ := exists_sign_of_sq h2 hs1 hbnd
      have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
      have hεv1 : Valued.v ε = 1 := by rcases hε with rfl | rfl <;> simp
      -- the partner coordinate is even
      have hdj2 : Valued.v dj ≤ Valued.v (2 : Fv) := by
        have hA : Valued.v (locGram Q v γ j j * dj ^ 2) ≤ Valued.v (2 * locGram Q v γ k k) := by
          have e : locGram Q v γ j j * dj ^ 2 =
              locGram Q v γ k k * (1 - s ^ 2) - zr ⬝ᵥ (locGram Q v γ *ᵥ zr) := by
            linear_combination -hrel
          rw [e]
          refine Valuation.map_sub_le _ ?_ hRb
          rw [map_mul, map_mul, mul_comm (Valued.v (2 : Fv))]
          exact mul_le_mul' le_rfl hbnd
        rw [map_mul, map_mul, hjj, map_pow, mul_comm (Valued.v (2 : Fv))] at hA
        have hsq : Valued.v dj ^ 2 ≤ Valued.v (2 : Fv) := le_of_mul_le_mul_left hA (zero_lt_iff.mpr hGkk0)
        refine valued_le_two_of_lt_one h2 ?_
        by_contra hcon
        push Not at hcon
        have hd1 : Valued.v dj = 1 := le_antisymm hdj1 hcon
        rw [hd1, one_pow] at hsq
        exact absurd (lt_of_le_of_lt hsq (valued_two_lt_one h2)) (lt_irrefl _)
      have hQwε := hQw ε hεε
      have hvw : Valued.v (Q.evalIn Fv (y - ε • bk)) = Valued.v (2 * locGram Q v γ k k) := by
        rw [hQwε, map_mul, hεv, map_mul, mul_comm]
      have hw0 : Q.evalIn Fv (y - ε • bk) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hvw
        have : Valued.v (2 * locGram Q v γ k k) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr (mul_ne_zero two_ne_zero hGkk)
        exact this hvw.symm
      refine ⟨ε, hε, hw0, ?_⟩
      show locAct v (symm Q Fv (y - ε • bk) : GL (Fin n) Fv) (loc v L.1) = loc v L.1
      refine locAct_symm_eq (hwM ε hε) hw0 fun x hx => ?_
      rw [hγ, mem_locAct] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have hc1 := mem_std_iff.mp hc
      rw [hBw, hvw]
      refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
      · exact valued_dot_gram_le γ hTj hk hd hzrsupp hzr1 hc1
      · rw [map_mul, map_mul, hjj, map_mul]
        calc Valued.v dj * (Valued.v (locGram Q v γ k k) * Valued.v (c j))
            ≤ Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * 1) :=
              mul_le_mul' hdj2 (mul_le_mul' le_rfl (hc1 j))
          _ = _ := by rw [mul_one]
      · have hse : s - ε = -(ε * (1 - ε * s)) := by linear_combination (-s) * hεε
        rw [map_mul, map_mul, hse, Valuation.map_neg, map_mul, hεv1, hεv, one_mul, map_mul]
        calc Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * Valued.v (c k))
            ≤ Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * 1) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl (hc1 k))
          _ = _ := by rw [mul_one]
  -- the common tail (as in `exists_peel_reflections`)
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  set w := y - ε • bk with hw
  have hw0 : Q.evalIn Fv w ≠ 0 := hroot.1
  have hwt : ∀ t ∈ T, qbil Q Fv w (basisVec γ t) = 0 := by
    intro t ht
    rw [hw, qbil_sub_left, qbil_smul_left, hbt t ht, qbil_basisVec γ k t, hT t ht k (fun h => hkT (h ▸ ht))]
    ring
  have hτy : (symm Q Fv w : GL (Fin n) Fv).val *ᵥ y = ε • bk := by
    have hwy : qbil Q Fv w y = Q.evalIn Fv w := by
      rw [hQw ε hεε, hw, qbil_sub_left, qbil_smul_left, hyy, hbky]
      ring
    rw [symm_mulVec_bil Q Fv hw0, hwy, div_self hw0, one_smul, hw]
    abel
  have hτt : ∀ t ∈ T, (symm Q Fv w : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t :=
    fun t ht => symm_fix Q Fv (hwt t ht)
  have hσ1M : symm Q Fv w * σ ∈ locStabV Q v L := mul_mem hroot.2 hσ
  have hσ1t : ∀ t ∈ T, ((symm Q Fv w * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t =
      basisVec γ t := fun t ht => by
    rw [orthGroup_mul_mulVec, hfix t ht]; exact hτt t ht
  have hσ1k : ((symm Q Fv w * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ bk = ε • bk := by
    rw [orthGroup_mul_mulVec]; exact hτy
  have hσeq : σ = symm Q Fv w * (symm Q Fv w * σ) := by rw [← mul_assoc, symm_mul_self, one_mul]
  have hbkroot : IsRootVector Q L v bk := isRootVector_basis_of_orth γ hγ k hk hGkk
  have hbkt : ∀ t ∈ T, qbil Q Fv bk (basisVec γ t) = 0 := fun t ht => by
    rw [hbk, qbil_basisVec]; exact hT t ht k (fun h => hkT (h ▸ ht))
  rcases hε with rfl | rfl
  · refine ⟨[w], symm Q Fv w * σ, ?_, ?_, hσ1M, ?_⟩
    · intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ⟨hroot, hwt⟩
    · have : symmProd Q Fv [w] = symm Q Fv w := by simp [symmProd]
      rw [this]; exact hσeq
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h]; exact (by rw [← hbk, hσ1k, one_smul])
      · exact hσ1t t ht
  · have hQbk : Q.evalIn Fv bk ≠ 0 := hbkroot.1
    have hσ2M : symm Q Fv bk * (symm Q Fv w * σ) ∈ locStabV Q v L := mul_mem hbkroot.2 hσ1M
    refine ⟨[w, bk], symm Q Fv bk * (symm Q Fv w * σ), ?_, ?_, hσ2M, ?_⟩
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨hroot, hwt⟩
      · exact ⟨hbkroot, hbkt⟩
    · have : symm Q Fv w * σ = symm Q Fv bk * (symm Q Fv bk * (symm Q Fv w * σ)) := by
        rw [← mul_assoc, symm_mul_self, one_mul]
      have e2 : symmProd Q Fv [w, bk] = symm Q Fv w * symm Q Fv bk := by simp [symmProd]
      rw [e2, mul_assoc, ← this]
      exact hσeq
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h, ← hbk, orthGroup_mul_mulVec, hσ1k, neg_smul, one_smul]
        exact symm_neg_self Q Fv hQbk
      · rw [orthGroup_mul_mulVec, hσ1t t ht]; exact symm_fix Q Fv (hbkt t ht)

/-- **The peeling step with a partner, for `FixTheta`**: under the hypotheses of `exists_peel_reflections_pair`,
`FixTheta` for $T \cup \{k\}$ implies it for $T$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling an orthogonal basis vector off past an orthogonal partner of the same norm order, spinor-norm version, p = 2)"]
theorem fixTheta_peel_pair (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n)) (k j : Fin n) (hkT : k ∉ T) (hjT : j ∉ T)
    (hjk : j ≠ k)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hj : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    (hjj : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ k k))
    (hd : ∀ i i', i ∉ insert k (insert j T) → i' ∉ insert k (insert j T) →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    (hgen : FixTheta Q L v γ (insert k T)) : FixTheta Q L v γ T := by
  intro σ hσ hfix
  obtain ⟨l, σ', hl, rfl, hσ', hfix'⟩ :=
    exists_peel_reflections_pair hQ h2 γ hγ T k j hkT hjT hjk hT hk hj hjj hd σ hσ hfix
  obtain ⟨xs, hxs, hdet, hθ⟩ := hgen σ' hσ' hfix'
  have hl0 : ∀ x ∈ l, Q.evalIn Fv x ≠ 0 := fun x hx => (hl x hx).1.1
  have hxs0 : ∀ x ∈ xs, Q.evalIn Fv x ≠ 0 := fun x hx => (hxs x hx).1
  refine ⟨l ++ xs, ?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact (hl u h).1
    · exact hxs u h
  · rw [orthGroup_det_mul, det_symmProd_pow l hl0, hdet, List.length_append, pow_add]
  · have h1 : spinorNorm Q Fv (symmProd Q Fv l * σ') = spinorNorm Q Fv (symmProd Q Fv l) * spinorNorm Q Fv σ' :=
      (spinorNormHom Q Fv hQ).map_mul _ _
    rw [h1, hθ, spinorNorm_symmProd Q Fv hQ l hl0, valProd_append',
      sqClassOf_mul (valProd_ne_zero Q Fv hl0) (valProd_ne_zero Q Fv hxs0)]

end PeelPair

section ChainPair

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q v) in
/-- **Root vectors for every unit class inside a block** (a **condition** on a basis $\gamma$): for some set $T$ of
indices with $b_t$ orthogonal to all other basis vectors and some $c \ne 0$, the entries $cG_{ij}$ and $cG_{ii}/2$
($i, j \notin T$) are integral and some $cG_{i_0j}$ ($i_0, j \notin T$) is a unit. (For $T = \emptyset$ this is the
first alternative of `UnitRoots`; the other basis vectors may lie at any scale.) -/
def UnitRootsBlock (γ : GL (Fin n) (v.adicCompletion ℚ)) : Prop :=
  ∃ (T : Finset (Fin n)) (c : v.adicCompletion ℚ) (i0 j : Fin n),
    (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) ∧ c ≠ 0 ∧
    (∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1) ∧
    (∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1) ∧ i0 ∉ T ∧ j ∉ T ∧
    Valued.v (c * locGram Q v γ i0 j) = 1

/-- Under `UnitRootsBlock`, every unit class is the class of $Q(x)Q(y)$ for two root vectors in the block
(`exists_rootVector_block`), hence lies in the root group. -/
theorem units_of_unitRootsBlock (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (h : UnitRootsBlock Q v γ) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  obtain ⟨T, c, i0, j, hT, hc, hint, heven, hi0, hjT, hj⟩ := h
  intro u hu
  obtain ⟨x, hxr, hx, -⟩ := exists_rootVector_block h2 γ hγ hT hc hint heven i0 j hi0 hjT hj hu
  obtain ⟨y, hyr, hy, -⟩ := exists_rootVector_block h2 γ hγ hT hc hint heven i0 j hi0 hjT hj (map_one Valued.v)
  have hmem := sqClassOf_mul_mem_rootGroup hxr hyr
  have e : Q.evalIn Fv x * Q.evalIn Fv y = c⁻¹ ^ 2 * u := by rw [hx, hy]; ring
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu; exact zero_ne_one hu
  rwa [e, sqClassOf_sq_mul (inv_ne_zero hc) hu0] at hmem

variable (Q v) in
/-- **Peeling chains with partners** (a **condition** on a basis $\gamma$ of $L_2$): given the set $T$ of indices
already peeled and a list of steps $(k, j?)$,
* if the list is empty, the complement of $T$ has at most $2$ elements, or is a scaled even unimodular block
  (`IsBlockEvenUnimodular`), or a scaled $E \perp \langle 2u\rangle$ block (`IsBlockGlue2`), or carries a relative
  chain of canonical overlattices (`RelChain Q v T γ`) with some basis vector $b_l$, $l \notin T$, orthogonal to all
  other basis vectors, and `UnitRoots Q v γ` or `UnitRootsBlock Q v γ` holds;
* a step $(k, \mathrm{none})$ is a peeling step of `PeelChainTheta`: $k \notin T$, $b_k$ orthogonal to the other
  basis vectors, $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{k\}$;
* a step $(k, \mathrm{some}\ j)$ is a peeling step with partner $j$: $k, j \notin T$, $j \ne k$, $b_k$ and $b_j$
  orthogonal to the other basis vectors, $\lvert G_{jj}\rvert = \lvert G_{kk}\rvert$, and
  $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{j, k\}$;
and after a step the chain continues with $T \cup \{k\}$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling chains with orthogonal partners, p = 2)"]
def PeelChainPair (γ : GL (Fin n) (v.adicCompletion ℚ)) :
    Finset (Fin n) → List (Fin n × Option (Fin n)) → Prop
  | T, [] => (Finset.univ \ T).card ≤ 2 ∨ (∃ c, IsBlockEvenUnimodular (locGram Q v γ) T c) ∨
      (∃ c l, IsBlockGlue2 (locGram Q v γ) T c l) ∨
      (RelChain Q v T γ ∧ (∃ l, l ∉ T ∧ ∀ m, m ≠ l → locGram Q v γ m l = 0) ∧
        (UnitRoots Q v γ ∨ UnitRootsBlock Q v γ))
  | T, (k, none) :: ks => k ∉ T ∧ (∀ m, m ≠ k → locGram Q v γ m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T →
        Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k)) ∧
      PeelChainPair γ (insert k T) ks
  | T, (k, some j) :: ks => k ∉ T ∧ j ∉ T ∧ j ≠ k ∧ (∀ m, m ≠ k → locGram Q v γ m k = 0) ∧
      (∀ m, m ≠ j → locGram Q v γ m j = 0) ∧
      Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ k k) ∧
      (∀ i i', i ∉ insert k (insert j T) → i' ∉ insert k (insert j T) →
        Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k)) ∧
      PeelChainPair γ (insert k T) ks

/-- **`FixTheta` along a peeling chain with partners.** -/
theorem fixTheta_of_peelChainPair (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) :
    ∀ (ks : List (Fin n × Option (Fin n))) (T : Finset (Fin n)),
      (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) → PeelChainPair Q v γ T ks → FixTheta Q L v γ T
  | [], T, hT, hc => by
    rcases hc with hc' | ⟨c, hc'⟩ | ⟨c, l, hc'⟩ | ⟨hrc, ⟨l, hlT, hl⟩, hu⟩
    · exact fixTheta_of_fixGenerated hQ (fixGenerated_of_peelChain2 hQ h2 γ hγ [] T hT hc')
    · obtain ⟨hc0, hm, hint, heven, hdet⟩ := hc'
      exact fixTheta_of_block_scaledEvenUnimodular hQ h2 γ hγ T hT hc0 hm hint hdet heven
    · obtain ⟨hc0, hm, hlT, hint, heven, hl, hu, hdet⟩ := hc'
      exact fixTheta_of_block_glue hQ h2 γ hγ T hT hc0 hm l hlT hint heven hl hu hdet
    · have hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
        rcases hu with hu | hu
        exacts [units_of_unitRoots h2 γ hγ hu, units_of_unitRootsBlock h2 γ hγ hu]
      refine fixTheta_of_relEven hQ h2 γ hγ (relEven_of_relChain hQ h2 hrc) hunits
        (isRootVector_basis_of_orth γ hγ l hl (locGram_diag_ne_zero hQ γ hl)) fun t ht => ?_
      have hlt : l ≠ t := fun h => hlT (h ▸ ht)
      change qbil Q Fv (basisVec γ l) (basisVec γ t) = 0
      rw [qbil_basisVec]
      exact hT t ht l hlt
  | (k, none) :: ks, T, hT, ⟨hkT, hk, hd, hrest⟩ => by
    refine fixTheta_peel hQ h2 γ hγ T k hkT hT hk hd
      (fixTheta_of_peelChainPair hQ h2 γ hγ ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm
  | (k, some j) :: ks, T, hT, ⟨hkT, hjT, hjk, hk, hj, hjj, hd, hrest⟩ => by
    refine fixTheta_peel_pair hQ h2 γ hγ T k j hkT hjT hjk hT hk hj hjj hd
      (fixTheta_of_peelChainPair hQ h2 γ hγ ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm

/-- **Theorem 18, "only if", for a peeling chain with partners** (Conway–Sloane §9.5, p. 391; $p = 2$;
unconditional): if $L_2$ has a basis $b = \gamma e$ and a list of steps with `PeelChainPair Q v γ ∅ ks`, every
element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': peeling chains with orthogonal partners)"]
theorem theorem18OnlyIf_of_peelChainPair (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n × Option (Fin n)))
    (hc : PeelChainPair Q v γ ∅ ks) : Theorem18OnlyIf Q L v hQ := by
  intro A hA
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hA
  obtain ⟨xs, hxs, hdet, hθ⟩ :=
    fixTheta_of_peelChainPair hQ h2 γ hγ ks ∅ (by simp) hc σ hσL (by simp)
  have h1 : ((σ : GL (Fin n) Fv).val).det = 1 := hσS
  refine ⟨xs, ?_, hxs, hσB.symm.trans hθ⟩
  rw [h1] at hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdet.symm

end ChainPair

end QuadFormsKB.ConwaySloane
