/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ by peeling off orthogonal basis vectors

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it: *the integral automorphisms of a lattice are usually, but
not always, products of integral reflections.* This file proves that they are, for the $2$-adic lattices $L_2$ that
have a basis $b_{k_1}, \dots, b_{k_m}$ of mutually orthogonal vectors spanning $1$-dimensional orthogonal summands
with norms $\lvert Q(b_{k_1})\rvert > \lvert Q(b_{k_2})\rvert > \cdots$ spread out by at least a factor $\lvert 4\rvert$,
followed by a remainder of at most one further basis vector.

**Layer.** As in `Section9Theorem18DyadicBinary.lean`, over $\mathbb Q$ at the prime $v$ over $2$ (so that
$\lvert 2\rvert = e^{-1}$): the form $Q$ on $\mathbb Q_2^n$ with bilinear form $B(x, y) = Q(x + y) - Q(x) - Q(y)$, a
lattice $L$ with localization $L_2$ (`loc v L.1`), a basis $b_k = \gamma e_k$ of $L_2$
(`loc v L.1 = locAct v γ (std v)`) with Gram matrix $G = \gamma^{\mathsf T}H\gamma$ (`locGram`, $G_{ij} = B(b_i, b_j)$,
$G_{kk} = 2Q(b_k)$), the reflections $\tau_x$ (`symm`), $O(L_2)$ (`locStabV`) and the $2$-adic root vectors
(`IsRootVector`). Indices are $0$-based.

**Defines**
* `FixGenerated Q L v γ T` (the **fixing condition** for a set $T$ of basis indices): every $\sigma \in O(L_2)$ with
  $\sigma b_t = b_t$ for all $t \in T$ is a product of reflections in $2$-adic root vectors that are orthogonal to
  all $b_t$, $t \in T$. For $T = \emptyset$ this is `GeneratedByRootReflections`.
* `PeelChain G T ks` (the **shape predicate on a list** $ks = [k_1, \dots, k_m]$ of distinct indices, given the set
  $T$ of indices already fixed): at each step $k = k_j$ the index $k \notin T$, the basis vector $b_k$ is orthogonal
  to all the other basis vectors ($G_{mk} = 0$ for $m \ne k$), and for all $i, i' \notin T \cup \{k\}$ (the later
  indices of the list and the remainder) $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert = \lvert 4Q(b_k)\rvert$; at
  the end the complement of $T$ has at most one element. For $T = \emptyset$ this says: $b_{k_j}$ spans an orthogonal
  summand, $\lvert G_{ii'}\rvert \le \lvert 2G_{k_jk_j}\rvert$ for all $i, i' \notin \{k_1, \dots, k_j\}$ (so
  $\operatorname{ord}_2 Q(b_{k_1}) + 2 \le \operatorname{ord}_2 Q(b_{k_2}) + 0$, and so on), and at most one basis
  vector is not in the list.
* `Theorem18DyadicCovered4`, `Theorem18DyadicResidual4`: the shape predicate and the named statement for the
  remaining lattices, as in `Section9Theorem18DyadicBinary.lean`.

**Proves**
* `fixGenerated_peel` (**the peeling step**): if $b_k$ spans an orthogonal summand and
  $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{k\}$, then
  `FixGenerated` for $T \cup \{k\}$ implies it for $T$. *Proof.* For $\sigma$ fixing $T$ write $y = \sigma b_k =
  s\,b_k + z$ with $z$ in the span of $b_i$, $i \notin T \cup \{k\}$ (since $y \perp b_t$); $Q(y) = Q(b_k)$ and
  $\lvert Q(z)\rvert \le \lvert 2Q(b_k)\rvert$ force $\lvert 1 - s^2\rvert \le \lvert 2\rvert$, so $s$ is a unit and
  (as $\lvert 2\rvert = e^{-1}$) $\lvert 1 - \varepsilon s\rvert = \lvert 2\rvert$ for some $\varepsilon = \pm1$.
  Then $w = y - \varepsilon b_k$ has $Q(w) = G_{kk}(1 - \varepsilon s)$, $\lvert Q(w)\rvert = \lvert 2G_{kk}\rvert$,
  $\lvert B(w, x)\rvert \le \lvert Q(w)\rvert$ on $L_2$, so $w$ is a root vector orthogonal to $T$ with
  $\tau_w y = \varepsilon b_k$; for $\varepsilon = -1$ also apply the root vector $\tau_{b_k}$.
* `fixGenerated_of_peelChain`, `generatedByRootReflections_of_peelChain` (**peeling**): the shape `PeelChain`
  implies `GeneratedByRootReflections`;
* `theorem18OnlyIf_of_peelChain`, `theorem18OnlyIf_of_covered4`, `theorem18DyadicResidual3_of_residual4`,
  `theorem18Dyadic_of_residual4`, `theorem18Statement_of_residual4`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicBinary

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Valuation lemmas at the prime over $2$ -/

section Valuation

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- A valuation below $1$ is at most $\lvert 2\rvert = e^{-1}$. -/
theorem valued_le_two_of_lt_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fv} (hx : Valued.v x < 1) :
    Valued.v x ≤ Valued.v (2 : Fv) := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]; exact zero_le
  · obtain ⟨k, hk⟩ := exists_valued_eq_exp v hx0
    rw [hk, ← exp_zero, exp_lt_exp] at hx
    rw [hk, valued_two_dyadic v h2, exp_le_exp]
    omega

theorem valued_two_lt_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (2 : Fv) < 1 := by
  rw [valued_two_dyadic v h2, ← exp_zero, exp_lt_exp]; norm_num

theorem valued_sub_lt_one {x y : Fv} (hx : Valued.v x < 1) (hy : Valued.v y < 1) : Valued.v (x - y) < 1 :=
  lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)

/-- **The sign $\varepsilon$ for peeling**: if $\lvert s\rvert \le 1$ and $\lvert 1 - s^2\rvert \le \lvert 2\rvert$ then
$\lvert 1 - \varepsilon s\rvert = \lvert 2\rvert$ for $\varepsilon = 1$ or $\varepsilon = -1$. (The numbers $1 - s$
and $1 + s$ add up to $2$ and have product $1 - s^2$; both have absolute value below $1$, hence at most $\lvert
2\rvert$ since $\lvert 2\rvert = e^{-1}$; they cannot both be smaller than $\lvert 2\rvert$.) -/
theorem exists_sign_of_sq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {s : Fv} (hs : Valued.v s ≤ 1)
    (h : Valued.v (1 - s ^ 2) ≤ Valued.v (2 : Fv)) :
    ∃ ε : Fv, (ε = 1 ∨ ε = -1) ∧ Valued.v (1 - ε * s) = Valued.v (2 : Fv) := by
  have hlt := valued_two_lt_one (v := v) h2
  have ha1 : Valued.v (1 - s) ≤ 1 := Valuation.map_sub_le _ (map_one _).le hs
  have hprod : Valued.v ((1 - s) * (1 + s)) < 1 := by
    rw [show (1 - s) * (1 + s) = 1 - s ^ 2 by ring]; exact lt_of_le_of_lt h hlt
  rw [map_mul] at hprod
  have e1 : (1 + s) = 2 - (1 - s) := by ring
  have e2 : (1 - s) = 2 - (1 + s) := by ring
  -- both factors have absolute value below one
  have hboth : Valued.v (1 - s) < 1 ∧ Valued.v (1 + s) < 1 := by
    by_cases ha : Valued.v (1 - s) < 1
    · exact ⟨ha, by rw [e1]; exact valued_sub_lt_one hlt ha⟩
    · have ha' : Valued.v (1 - s) = 1 := le_antisymm ha1 (not_lt.mp ha)
      rw [ha', one_mul] at hprod
      exact absurd (by rw [e2]; exact valued_sub_lt_one hlt hprod) ha
  have ha2 := valued_le_two_of_lt_one h2 hboth.1
  have hb2 := valued_le_two_of_lt_one h2 hboth.2
  by_cases hA : Valued.v (1 - s) = Valued.v (2 : Fv)
  · exact ⟨1, Or.inl rfl, by rw [one_mul]; exact hA⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hAlt : Valued.v (1 - s) < Valued.v (2 : Fv) := lt_of_le_of_ne ha2 hA
    rw [neg_mul, one_mul, sub_neg_eq_add]
    refine le_antisymm hb2 ?_
    by_contra hcon
    push Not at hcon
    have h22 : Valued.v (2 : Fv) < Valued.v (2 : Fv) :=
      calc Valued.v (2 : Fv) = Valued.v ((1 - s) + (1 + s)) := by congr 1; ring
        _ ≤ max (Valued.v (1 - s)) (Valued.v (1 + s)) := Valuation.map_add _ _ _
        _ < Valued.v (2 : Fv) := max_lt hAlt hcon
    exact lt_irrefl _ h22

end Valuation

/-! ### Coordinates in a basis -/

section Peel

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- The basis vector $b_k = \gamma e_k$ of $L_2$. -/
abbrev basisVec (γ : GL (Fin n) Fv) (k : Fin n) : Fin n → Fv := γ.val *ᵥ Pi.single k 1

theorem qbil_basisVec (γ : GL (Fin n) Fv) (k l : Fin n) :
    qbil Q Fv (basisVec γ k) (basisVec γ l) = locGram Q v γ k l := locGram_apply_eq γ k l

/-- $B(\gamma d, b_k) = d_k G_{kk}$ when $b_k$ is orthogonal to the other basis vectors. -/
theorem qbil_vec_basisVec (γ : GL (Fin n) Fv) {k : Fin n} (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (d : Fin n → Fv) : qbil Q Fv (γ.val *ᵥ d) (basisVec γ k) = d k * locGram Q v γ k k := by
  rw [qbil_mulVec_locGram, dotProduct, Finset.sum_eq_single k]
  · simp [mulVec_single]
  · intro i _ hi; simp [mulVec_single, hk i hi]
  · simp

/-- A basis vector orthogonal to all the others has $G_{kk} \ne 0$ (the Gram matrix is nonsingular). -/
theorem locGram_diag_ne_zero (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {k : Fin n}
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0) : locGram Q v γ k k ≠ 0 := by
  intro h0
  refine locGram_det_ne_zero hQ γ (Matrix.det_eq_zero_of_column_eq_zero k fun i => ?_)
  by_cases hi : i = k
  · subst hi; exact h0
  · exact hk i hi

theorem qbil_smul_right' (c : Fv) (x z : Fin n → Fv) : qbil Q Fv z (c • x) = c * qbil Q Fv z x := by
  rw [qbil_comm, qbil_smul_left, qbil_comm]

/-- **Bound for a form restricted to the later indices**: if $p$ vanishes on $T \cup \{k\}$, $b_k$ and the $b_t$ are
orthogonal to the other basis vectors, and $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ off $T \cup \{k\}$, then
$\lvert p^{\mathsf T}Gc\rvert \le \lvert 2G_{kk}\rvert$ for $p, c$ with entries of absolute value $\le 1$. -/
theorem valued_dot_gram_le (γ : GL (Fin n) Fv) {T : Finset (Fin n)} {k : Fin n}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hd : ∀ i i', i ∉ insert k T → i' ∉ insert k T →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    {p c : Fin n → Fv} (hp : ∀ i ∈ insert k T, p i = 0) (hp1 : ∀ i, Valued.v (p i) ≤ 1)
    (hc : ∀ i, Valued.v (c i) ≤ 1) :
    Valued.v (p ⬝ᵥ (locGram Q v γ *ᵥ c)) ≤ Valued.v (2 * locGram Q v γ k k) := by
  unfold dotProduct
  refine Valuation.map_sum_le _ fun i _ => ?_
  by_cases hi : i ∈ insert k T
  · rw [hp i hi, zero_mul, map_zero]; exact zero_le
  · rw [map_mul]
    have hin : Valued.v ((locGram Q v γ *ᵥ c) i) ≤ Valued.v (2 * locGram Q v γ k k) := by
      unfold mulVec dotProduct
      refine Valuation.map_sum_le _ fun i' _ => ?_
      show Valued.v (locGram Q v γ i i' * c i') ≤ _
      by_cases hi' : i' ∈ insert k T
      · have : locGram Q v γ i i' = 0 := by
          rcases Finset.mem_insert.mp hi' with rfl | ht
          · exact hk i (fun h => hi (Finset.mem_insert.mpr (Or.inl h)))
          · exact hT i' ht i (fun h => hi (h ▸ hi'))
        rw [this, zero_mul, map_zero]; exact zero_le
      · rw [map_mul]
        calc _ ≤ Valued.v (2 * locGram Q v γ k k) * 1 := mul_le_mul' (hd i i' hi hi') (hc i')
          _ = _ := mul_one _
    calc _ ≤ 1 * Valued.v (2 * locGram Q v γ k k) := mul_le_mul' (hp1 i) hin
      _ = _ := one_mul _

/-- $z^{\mathsf T}Gz + G_{kk}s^2$ for $d = z + s e_k$, $z_k = 0$, $b_k \perp$ the other basis vectors. -/
theorem dot_gram_split (γ : GL (Fin n) Fv) {k : Fin n} (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (z : Fin n → Fv) (hzk : z k = 0) (s : Fv) :
    (z + Pi.single k s) ⬝ᵥ (locGram Q v γ *ᵥ (z + Pi.single k s)) =
      z ⬝ᵥ (locGram Q v γ *ᵥ z) + locGram Q v γ k k * s ^ 2 := by
  have hk' : ∀ m, m ≠ k → locGram Q v γ k m = 0 := fun m hm => by rw [locGram_symm']; exact hk m hm
  have e1 : z ⬝ᵥ (locGram Q v γ *ᵥ Pi.single k s) = 0 := by
    unfold dotProduct
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = k
    · subst hi; rw [hzk, zero_mul]
    · simp [mulVec_single, hk i hi]
  have e2 : (Pi.single k s : Fin n → Fv) ⬝ᵥ (locGram Q v γ *ᵥ z) = 0 := by
    rw [single_dotProduct]
    have : (locGram Q v γ *ᵥ z) k = 0 := by
      unfold mulVec dotProduct
      refine Finset.sum_eq_zero fun i _ => ?_
      show locGram Q v γ k i * z i = 0
      by_cases hi : i = k
      · subst hi; rw [hzk, mul_zero]
      · rw [hk' i hi, zero_mul]
    rw [this, mul_zero]
  have e3 : (Pi.single k s : Fin n → Fv) ⬝ᵥ (locGram Q v γ *ᵥ Pi.single k s) =
      locGram Q v γ k k * s ^ 2 := by
    rw [single_dotProduct]; simp [mulVec_single]; ring
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, e1, e2, e3]
  ring

/-! ### The peeling step -/

variable (Q L v) in
/-- **The fixing condition** for a set $T$ of basis indices of $L_2 = \gamma\,\mathrm{std}$: every $\sigma \in
O(L_2)$ with $\sigma b_t = b_t$ for all $t \in T$ ($b_t = \gamma e_t$) is a product $\tau_{x_1}\cdots\tau_{x_r}$ of
reflections in $2$-adic root vectors $x_j$ of $L$ that are orthogonal to all $b_t$, $t \in T$ ($B(x_j, b_t) = 0$).
For $T = \emptyset$ this is `GeneratedByRootReflections`. -/
def FixGenerated (γ : GL (Fin n) Fv) (T : Finset (Fin n)) : Prop :=
  ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
    (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
    ∃ l : List (Fin n → Fv), (∀ u ∈ l, IsRootVector Q L v u ∧ ∀ t ∈ T, qbil Q Fv u (basisVec γ t) = 0) ∧
      σ = symmProd Q Fv l

theorem orthGroup_mul_mulVec (a b : orthGroup Q Fv) (x : Fin n → Fv) :
    ((a * b : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ x =
      (a : GL (Fin n) Fv).val *ᵥ ((b : GL (Fin n) Fv).val *ᵥ x) := by
  rw [mulVec_mulVec]; rfl

/-- **The peeling step.** Let $T$ be a set of basis indices all of whose vectors $b_t$ are orthogonal to the other
basis vectors, and $k \notin T$ with $b_k$ orthogonal to the other basis vectors and
$\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert = \lvert 4Q(b_k)\rvert$ for all $i, i' \notin T \cup \{k\}$. If
every $\sigma \in O(L_2)$ fixing $b_t$ ($t \in T \cup \{k\}$) is a product of reflections in root vectors orthogonal to
these, then so is every $\sigma \in O(L_2)$ fixing $b_t$ ($t \in T$) (Conway–Sloane §9.5, p. 391; $v \mid 2$ over
$\mathbb Q$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling an orthogonal basis vector off, p = 2)"]
theorem fixGenerated_peel (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n)) (k : Fin n) (hkT : k ∉ T)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hd : ∀ i i', i ∉ insert k T → i' ∉ insert k T →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    (hgen : FixGenerated Q L v γ (insert k T)) : FixGenerated Q L v γ T := by
  intro σ hσ hfix
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
  set z : Fin n → Fv := Function.update d k 0 with hz
  have hzk : z k = 0 := by simp [hz]
  have hzi : ∀ i, i ≠ k → z i = d i := fun i hi => by simp [hz, hi]
  have hdz : d = z + Pi.single k s := by
    ext i
    by_cases hi : i = k
    · subst hi; simp [hz, hs]
    · simp [hzi i hi, hi]
  have hzsupp : ∀ i ∈ insert k T, z i = 0 := by
    intro i hi
    by_cases hik : i = k
    · subst hik; exact hzk
    · rw [hzi i hik]
      exact hdt i ((Finset.mem_insert.mp hi).resolve_left hik)
  have hz1 : ∀ i, Valued.v (z i) ≤ 1 := fun i => by
    by_cases hi : i = k
    · subst hi; rw [hzk, map_zero]; exact zero_le
    · rw [hzi i hi]; exact hdle i
  have hs1 : Valued.v s ≤ 1 := hdle k
  have hzz : Valued.v (z ⬝ᵥ (locGram Q v γ *ᵥ z)) ≤ Valued.v (2 * locGram Q v γ k k) :=
    valued_dot_gram_le γ hT hk hd hzsupp hz1 hz1
  have hyy : qbil Q Fv y y = locGram Q v γ k k := by
    have h := qbil_orth Q Fv σ (basisVec γ k) (basisVec γ k)
    rw [qbil_basisVec] at h
    exact h
  have hyk : qbil Q Fv y (basisVec γ k) = s * locGram Q v γ k k := by
    rw [← hyd, qbil_vec_basisVec γ hk]
  have hquad : locGram Q v γ k k = z ⬝ᵥ (locGram Q v γ *ᵥ z) + locGram Q v γ k k * s ^ 2 := by
    rw [← dot_gram_split γ hk z hzk s, ← hdz, ← qbil_mulVec_locGram, hyd]
    exact hyy.symm
  have hrel : locGram Q v γ k k * (1 - s ^ 2) = z ⬝ᵥ (locGram Q v γ *ᵥ z) := by
    linear_combination hquad
  have hGv0 : 0 < Valued.v (locGram Q v γ k k) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hGkk)
  have hbnd : Valued.v (1 - s ^ 2) ≤ Valued.v (2 : Fv) := by
    have h1 : Valued.v (locGram Q v γ k k) * Valued.v (1 - s ^ 2) ≤
        Valued.v (locGram Q v γ k k) * Valued.v (2 : Fv) := by
      rw [← map_mul, hrel, mul_comm (Valued.v (locGram Q v γ k k)), ← map_mul]; exact hzz
    exact le_of_mul_le_mul_left h1 hGv0
  obtain ⟨ε, hε, hεv⟩ := exists_sign_of_sq h2 hs1 hbnd
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hεv1 : Valued.v ε = 1 := by rcases hε with rfl | rfl <;> simp
  set bk := basisVec γ k with hbk
  set w := y - ε • bk with hw
  have hbky : qbil Q Fv bk y = s * locGram Q v γ k k := by rw [qbil_comm]; exact hyk
  have hbkbk : qbil Q Fv bk bk = locGram Q v γ k k := qbil_basisVec γ k k
  have hqww : qbil Q Fv w w = 2 * locGram Q v γ k k * (1 - ε * s) := by
    rw [hw]
    simp only [qbil_sub_left, qbil_sub_right, qbil_smul_left, qbil_smul_right']
    rw [hyy, hyk, hbky, hbkbk]
    linear_combination (locGram Q v γ k k) * hεε
  have hQw : Q.evalIn Fv w = locGram Q v γ k k * (1 - ε * s) := by
    have h := two_mul_evalIn_eq Q Fv w
    rw [hqww] at h
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    linear_combination h
  have hvw : Valued.v (Q.evalIn Fv w) = Valued.v (2 * locGram Q v γ k k) := by
    rw [hQw, map_mul, hεv, map_mul, mul_comm]
  have hw0 : Q.evalIn Fv w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvw
    have : Valued.v (2 * locGram Q v γ k k) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (mul_ne_zero two_ne_zero hGkk)
    exact this hvw.symm
  have hεbk : ε • bk ∈ loc v L.1 := by
    rcases hε with rfl | rfl
    · simpa using hbkM
    · simpa using (loc v L.1).neg_mem hbkM
  have hwM : w ∈ loc v L.1 := (loc v L.1).sub_mem hyM hεbk
  have hwt : ∀ t ∈ T, qbil Q Fv w (basisVec γ t) = 0 := by
    intro t ht
    rw [hw, qbil_sub_left, qbil_smul_left, hbt t ht, qbil_basisVec γ k t, hT t ht k (fun h => hkT (h ▸ ht))]
    ring
  have hroot : IsRootVector Q L v w := by
    refine ⟨hw0, ?_⟩
    show locAct v (symm Q Fv w : GL (Fin n) Fv) (loc v L.1) = loc v L.1
    refine locAct_symm_eq hwM hw0 fun x hx => ?_
    rw [hγ, mem_locAct] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hc1 := mem_std_iff.mp hc
    have hGc : (locGram Q v γ *ᵥ c) k = locGram Q v γ k k * c k := by
      have hk' : ∀ m, m ≠ k → locGram Q v γ k m = 0 := fun m hm => by
        rw [locGram_symm']; exact hk m hm
      unfold mulVec dotProduct
      rw [Finset.sum_eq_single k]
      · intro i _ hi; show locGram Q v γ k i * c i = 0; rw [hk' i hi, zero_mul]
      · simp
    have hq1 : qbil Q Fv y (γ.val *ᵥ c) =
        z ⬝ᵥ (locGram Q v γ *ᵥ c) + s * (locGram Q v γ k k * c k) := by
      rw [← hyd, qbil_mulVec_locGram, hdz, add_dotProduct, single_dotProduct, hGc]
    have hq2 : qbil Q Fv bk (γ.val *ᵥ c) = locGram Q v γ k k * c k := by
      rw [hbk]
      show qbil Q Fv (γ.val *ᵥ Pi.single k 1) (γ.val *ᵥ c) = _
      rw [qbil_mulVec_locGram, single_dotProduct, one_mul, hGc]
    rw [hw, qbil_sub_left, qbil_smul_left, hq1, hq2, ← hw, hvw,
      show z ⬝ᵥ (locGram Q v γ *ᵥ c) + s * (locGram Q v γ k k * c k) - ε * (locGram Q v γ k k * c k) =
        z ⬝ᵥ (locGram Q v γ *ᵥ c) + (s - ε) * (locGram Q v γ k k * c k) by ring]
    refine Valuation.map_add_le _ (valued_dot_gram_le γ hT hk hd hzsupp hz1 hc1) ?_
    have hse : s - ε = -(ε * (1 - ε * s)) := by linear_combination (-s) * hεε
    rw [map_mul, map_mul, hse, Valuation.map_neg, map_mul, hεv1, hεv, one_mul]
    calc Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * Valued.v (c k))
        ≤ Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (hc1 k))
      _ = Valued.v (2 * locGram Q v γ k k) := by rw [map_mul, mul_one]
  have hτy : (symm Q Fv w : GL (Fin n) Fv).val *ᵥ y = ε • bk := by
    have hwy : qbil Q Fv w y = Q.evalIn Fv w := by
      rw [hQw, hw, qbil_sub_left, qbil_smul_left, hyy, hbky]
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
  · obtain ⟨l, hl, hσl⟩ := hgen (symm Q Fv w * σ) hσ1M (by
      intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h]; exact (by rw [← hbk, hσ1k, one_smul])
      · exact hσ1t t ht)
    refine ⟨w :: l, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hroot, hwt⟩
      · obtain ⟨hr, ho⟩ := hl u hu
        exact ⟨hr, fun t ht => ho t (Finset.mem_insert_of_mem ht)⟩
    · rw [hσeq, hσl]; simp [symmProd]
  · have hQbk : Q.evalIn Fv bk ≠ 0 := hbkroot.1
    have hσ2M : symm Q Fv bk * (symm Q Fv w * σ) ∈ locStabV Q v L := mul_mem hbkroot.2 hσ1M
    obtain ⟨l, hl, hσl⟩ := hgen (symm Q Fv bk * (symm Q Fv w * σ)) hσ2M (by
      intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h, ← hbk, orthGroup_mul_mulVec, hσ1k, neg_smul, one_smul]
        exact symm_neg_self Q Fv hQbk
      · rw [orthGroup_mul_mulVec, hσ1t t ht]; exact symm_fix Q Fv (hbkt t ht))
    refine ⟨w :: bk :: l, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hroot, hwt⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hbkroot, hbkt⟩
      · obtain ⟨hr, ho⟩ := hl u hu
        exact ⟨hr, fun t ht => ho t (Finset.mem_insert_of_mem ht)⟩
    · have : symm Q Fv w * σ = symm Q Fv bk * (symm Q Fv bk * (symm Q Fv w * σ)) := by
        rw [← mul_assoc, symm_mul_self, one_mul]
      rw [hσeq, this, hσl]; simp [symmProd]

/-- Every $\sigma$ fixing all basis vectors is the identity, the empty product. -/
theorem fixGenerated_univ (γ : GL (Fin n) Fv) : FixGenerated Q L v γ Finset.univ := by
  intro σ _ hfix
  refine ⟨[], by simp, ?_⟩
  have h : (σ : GL (Fin n) Fv).val * γ.val = γ.val := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hfix j (Finset.mem_univ j)) i
    rw [mulVec_mulVec] at this
    simpa [mulVec_single] using this
  have h1 : (σ : GL (Fin n) Fv).val = 1 :=
    calc (σ : GL (Fin n) Fv).val
        = (σ : GL (Fin n) Fv).val * (γ.val * ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = ((σ : GL (Fin n) Fv).val * γ.val) * ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) := by
          rw [Matrix.mul_assoc]
      _ = γ.val * ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) := by rw [h]
      _ = 1 := Units.mul_inv γ
  have : σ = 1 := Subtype.ext (Units.ext h1)
  rw [this]; simp [symmProd]

end Peel

/-! ### Peeling an orthogonal chain -/

section Chain

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The peeling shape on a list of indices** (a **condition** on the Gram matrix $G$ of a basis $b = \gamma e$ of
$L_2$): given the set $T$ of indices already peeled and a list $ks = [k_1, k_2, \dots, k_m]$ of further indices,
* if $ks$ is empty, at most one index is not in $T$ (the remainder has at most one basis vector);
* if $ks = k :: ks'$, then $k \notin T$, $b_k$ is orthogonal to all other basis vectors ($G_{mk} = 0$ for $m \ne k$),
  $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert = \lvert 4Q(b_k)\rvert$ for all indices $i, i' \notin T \cup \{k\}$,
  and `PeelChain G (insert k T) ks'` holds.
With $T = \emptyset$: the basis vectors $b_{k_1}, b_{k_2}, \dots$ span $1$-dimensional orthogonal summands whose
norms decrease by at least a factor $\lvert 4\rvert$ at each step, and at most one basis vector is left over. -/
def PeelChain (G : Matrix (Fin n) (Fin n) Fv) : Finset (Fin n) → List (Fin n) → Prop
  | T, [] => (Finset.univ \ T).card ≤ 1
  | T, k :: ks => k ∉ T ∧ (∀ m, m ≠ k → G m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T → Valued.v (G i i') ≤ Valued.v (2 * G k k)) ∧
      PeelChain G (insert k T) ks

/-- **Peeling an orthogonal chain** gives the fixing condition for the set $T$ already peeled. -/
theorem fixGenerated_of_peelChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) :
    ∀ (ks : List (Fin n)) (T : Finset (Fin n)), (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) →
      PeelChain (locGram Q v γ) T ks → FixGenerated Q L v γ T
  | [], T, hT, hc => by
    have hcard : (Finset.univ \ T).card ≤ 1 := hc
    have hmemT : ∀ i, i ∉ T → i ∈ Finset.univ \ T := fun i hi => by simp [hi]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · have hTu : T = Finset.univ := by
        refine Finset.eq_univ_of_forall fun i => ?_
        by_contra hi
        have := hmemT i hi
        rw [Finset.card_eq_zero.mp h0] at this
        simp at this
      rw [hTu]; exact fixGenerated_univ γ
    · obtain ⟨m, hm⟩ := Finset.card_eq_one.mp h1
      have hmT : m ∉ T := by
        have : m ∈ Finset.univ \ T := by rw [hm]; simp
        simpa using this
      have hTm : ∀ i, i ≠ m → i ∈ T := fun i hi => by
        by_contra hiT
        have := hmemT i hiT
        rw [hm] at this
        exact hi (by simpa using this)
      have hins : insert m T = Finset.univ := by
        refine Finset.eq_univ_of_forall fun i => ?_
        by_cases him : i = m
        · rw [him]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hTm i him)
      refine fixGenerated_peel hQ h2 γ hγ T m hmT hT (fun m' hm' => ?_) (fun i i' hi _ => ?_) ?_
      · rw [locGram_symm']; exact hT m' (hTm m' hm') m (fun h => hm' h.symm)
      · exact absurd (by rw [hins]; exact Finset.mem_univ i) hi
      · rw [hins]; exact fixGenerated_univ γ
  | k :: ks, T, hT, ⟨hkT, hk, hd, hrest⟩ => by
    refine fixGenerated_peel hQ h2 γ hγ T k hkT hT hk hd
      (fixGenerated_of_peelChain hQ h2 γ hγ ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm

/-- **Binary-and-larger lattices with a peeling chain** (Conway–Sloane §9.5, p. 391, the remark after Theorem 18,
$p = 2$): if $L_2$ has a basis $b = \gamma e$ and a list $ks = [k_1, \dots, k_m]$ of indices with the shape
`PeelChain` (the $b_{k_j}$ span $1$-dimensional orthogonal summands, $\lvert G_{ii'}\rvert \le \lvert 2G_{k_jk_j}\rvert$
for the later indices $i, i'$ and for the at most one index outside the list), then every integral automorphism of
$L_2$ is a product of integral reflections. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: p = 2, integral automorphisms are products of integral reflections for a peeling chain of orthogonal basis vectors)"]
theorem generatedByRootReflections_of_peelChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChain (locGram Q v γ) ∅ ks) : GeneratedByRootReflections Q v L := by
  intro σ hσ
  obtain ⟨l, hl, h⟩ := fixGenerated_of_peelChain hQ h2 γ hγ ks ∅ (by simp) hc σ hσ (by simp)
  exact ⟨l, fun u hu => (hl u hu).1, h⟩

/-- **Theorem 18, "only if", for a peeling chain** (Conway–Sloane §9.5, p. 391; $p = 2$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a peeling chain of orthogonal basis vectors)"]
theorem theorem18OnlyIf_of_peelChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChain (locGram Q v γ) ∅ ks) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_generated hQ (generatedByRootReflections_of_peelChain hQ h2 γ hγ ks hc)

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, fourth version**: the shapes of
`Theorem18DyadicCovered3` ($n = 2$ or the shapes of `Theorem18DyadicCovered2`), or $L_2$ has a basis $b = \gamma e$
and a list $ks$ of indices with the shape `PeelChain (locGram Q v γ) ∅ ks`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, fourth version)"]
def Theorem18DyadicCovered4 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered3 Q L v ∨ ∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)),
    loc v L.1 = locAct v γ (std v) ∧ PeelChain (locGram Q v γ) ∅ ks

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, fourth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, fourth version)"]
theorem theorem18OnlyIf_of_covered4 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered4 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, ks, hγ, hks⟩
  · exact theorem18OnlyIf_of_covered3 hQ h2 hc
  · exact theorem18OnlyIf_of_peelChain hQ h2 γ hγ ks hks

end Chain

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, fourth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape
covered by `Theorem18DyadicCovered4`, every $2$-adically automorphous number $A \in \theta(O^+(L_2))$ is, up to
squares, the product of the norms of an even number of $2$-adic root vectors (`Theorem18OnlyIf`).

It implies `Theorem18DyadicResidual3` (`theorem18DyadicResidual3_of_residual4`), hence `Theorem18Dyadic`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, fourth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual4 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered4 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The third residual statement from the fourth**: lattices with a peeling chain are proved
(`theorem18OnlyIf_of_peelChain`), elsewhere it is `Theorem18DyadicResidual4`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the fourth residual statement)"]
theorem theorem18DyadicResidual3_of_residual4 (h : Theorem18DyadicResidual4) : Theorem18DyadicResidual3 where
  exists_rootVectors n Q hQ L v h2 hnc := by
    by_cases hs : ∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)),
        loc v L.1 = locAct v γ (std v) ∧ PeelChain (locGram Q v γ) ∅ ks
    · obtain ⟨γ, ks, hγ, hks⟩ := hs
      exact theorem18OnlyIf_of_peelChain hQ h2 γ hγ ks hks
    · exact h.exists_rootVectors n Q hQ L v h2 (fun hc => hc.elim hnc hs)

/-- **`Theorem18Dyadic` from the fourth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, fourth version)"]
theorem theorem18Dyadic_of_residual4 (h : Theorem18DyadicResidual4) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual3 (theorem18DyadicResidual3_of_residual4 h)

/-- **Conway–Sloane's Theorem 18 from the fourth residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual4`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, fourth version)"]
theorem theorem18Statement_of_residual4 (h : Theorem18DyadicResidual4) : Theorem18Statement :=
  theorem18Statement_of_residual3 (theorem18DyadicResidual3_of_residual4 h)

end QuadFormsKB.ConwaySloane
