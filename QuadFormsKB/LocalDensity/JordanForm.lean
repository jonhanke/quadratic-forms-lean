/-
# Local densities over $\mathbb{Q}$: the printed local normal form, Lemma 2.1

**Layer:** $\mathbb{Q}$. **Defines** `IsJordanForm Q p P ν`, the normal form of Hanke 2004, (2.3) and Lemma 2.1,
p. 355, *as printed*: $Q = \bigoplus_j p^{\nu_j} Q_j$ with $Q_j = u x^2$ ($u$ a unit) or $Q_j = a x^2 + bxy + cy^2$
($b$ a unit; only for $p = 2$), and $S_0 = $ `unimodularCoords ν` $= \{i : \nu_i = 0\}$. **Proves** Lemma 2.1:
every nondegenerate $Q$ has, at each prime $p$, an integral form in normal form with the same counts
$r_{p^k}(m)$ (`exists_jordanForm`; `exists_diag_same_counts` for odd $p$), and count invariance under
$\mathrm{GL}_n(\mathbb{Z}_p)$ (`repCount_eq_of_unimodular`). **Depends on** `Basic.lean`. Over $\mathbb{Z}_p$ this is
`DVR.IsJordanFormW` (`Bridge.lean`: `isJordanForm_iff_isJordanFormW_padic`).
-/
import QuadFormsKB.LocalDensity.Basic

namespace QuadFormsKB.LocalDensity

open QuadForm Matrix

variable {n : ℕ}

/-- **Coordinate $i$ lies in a 2-dimensional block** of `P` (a set of coordinate pairs). -/
def IsPaired (P : Finset (Fin n × Fin n)) (i : Fin n) : Prop := ∃ e ∈ P, e.1 = i ∨ e.2 = i

/-- **Local normal form** (Hanke 2004, (2.3) and Lemma 2.1, p. 355): $Q = \sum_j p^{\nu_j} Q_j$ is block
diagonal at $p$, with
1. the 2-dimensional blocks on the pairs $(i, j) \in P$, $i < j$, pairwise disjoint, and **only when
   $p = 2$** (Lemma 2.1: for $p \nmid 2$ all blocks are 1-dimensional; at $p = 2$, $b$ a unit makes the block
   discriminant $b^2 - 4ac$ a unit);
2. no cross terms $x_i x_j$ outside $P$ (coefficient $c_{ij} = 0$ for $i < j$, $(i,j) \notin P$);
3. for $(i,j) \in P$: $\nu_i = \nu_j$, $c_{ij} = p^{\nu_i} b$ with $p \nmid b$, and $p^{\nu_i} \mid c_{ii}, c_{jj}$
   (the block is $p^{\nu_i}(a x_i^2 + b x_i x_j + c x_j^2)$ with $b$ a unit);
4. for unpaired $i$: $c_{ii} = p^{\nu_i} u$ with $p \nmid u$.

(Lemma 2.1 also gives $\mathrm{ord}_p(a) = \mathrm{ord}_p(c)$ in 2-dimensional blocks; not needed here.)

*Correction:* an earlier version was stated without "only when $p = 2$", which is false for Lemma 3.2:
$p = 3$, $Q = (x+y)^2$ as a "block" $x^2 + 2xy + y^2$ ($b = 2$ a unit, but the block is degenerate mod 3)
has 18 Good solutions mod 9 vs. the predicted $3 \cdot 2 = 6$ (checked in Lean by `decide`). -/
def IsJordanForm (Q : QuadForm ℤ n) (p : ℕ) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) : Prop :=
  (P.Nonempty → p = 2) ∧
  (∀ e ∈ P, e.1 < e.2) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i < j → (i, j) ∉ P → Q.coeff i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, Q.coeff e.1 e.2 = (p : ℤ) ^ ν e.1 * b ∧ ¬ (p : ℤ) ∣ b) ∧
    (p : ℤ) ^ ν e.1 ∣ Q.coeff e.1 e.1 ∧ (p : ℤ) ^ ν e.1 ∣ Q.coeff e.2 e.2) ∧
  (∀ i, ¬ IsPaired P i → ∃ u, Q.coeff i i = (p : ℤ) ^ ν i * u ∧ ¬ (p : ℤ) ∣ u)

/-- **The unimodular coordinates** $S_0 = \{i : \nu_i = 0\}$ of a local normal form. -/
def unimodularCoords (ν : Fin n → ℕ) : Finset (Fin n) := Finset.univ.filter fun i => ν i = 0

/-- **Counts are invariant under changes of variables invertible mod $p$** (Hanke 2004, used in
Lemma 2.1, p. 355): if $Q'(\vec{x}) = Q(U\vec{x})$ for an integer matrix $U$ with $p \nmid \det U$, then
$r_{p^k}(Q', m) = r_{p^k}(Q, m)$ for all $k, m$. *Proof:* $\vec{x} \mapsto U\vec{x}$ is a bijection of
$(\mathbb{Z}/p^k)^n$ since $\det U$ is a unit mod $p^k$. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem repCount_eq_of_unimodular (Q Q' : QuadForm ℤ n) (U : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    [Fact p.Prime] (hU : ¬ (p : ℤ) ∣ U.det) (hQ' : ∀ x : Fin n → ℤ, Q'.eval x = Q.eval (U *ᵥ x))
    (k : ℕ) (m : ℤ) : repCount Q' p k m = repCount Q p k m := by
  have hp := (Fact.out : p.Prime)
  set K := ZMod (p ^ k)
  let f : ℤ →+* K := Int.castRingHom K
  have hcast : ∀ (R : QuadForm ℤ n) (z : Fin n → ℤ), R.evalIn K (fun i => f (z i)) = f (R.eval z) := by
    intro R z
    simp [QuadForm.evalIn, map_sum, apply_ite f]
  set U' := U.map f
  have hmv : ∀ z : Fin n → ℤ, U' *ᵥ (fun i => f (z i)) = fun i => f ((U *ᵥ z) i) := by
    intro z
    funext i
    simp [U', Matrix.mulVec, dotProduct, map_sum]
  have key : ∀ x : Fin n → K, Q'.evalIn K x = Q.evalIn K (U' *ᵥ x) := by
    intro x
    obtain ⟨z, rfl⟩ : ∃ z : Fin n → ℤ, (fun i => f (z i)) = x :=
      ⟨fun i => (ZMod.intCast_surjective (x i)).choose,
        by funext i; exact (ZMod.intCast_surjective (x i)).choose_spec⟩
    rw [hmv, hcast, hcast, hQ']
  have hdet : IsUnit U'.det := by
    rw [show U'.det = f U.det from (RingHom.map_det f U).symm]
    have hcop : IsCoprime U.det ((p ^ k : ℕ) : ℤ) := by
      push_cast
      apply IsCoprime.pow_right
      exact ((Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hU).symm
    exact (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr hcop.symm
  let e : (Fin n → K) ≃ (Fin n → K) :=
    { toFun := fun x => U' *ᵥ x
      invFun := fun x => U'⁻¹ *ᵥ x
      left_inv := fun x => by
        simp only
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
      right_inv := fun x => by
        simp only
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] }
  unfold repCount
  exact Nat.card_congr (Equiv.subtypeEquiv e (fun x => by rw [key]; rfl))

/-- Entries of a congruence $M^{\mathsf T} H M$. -/
theorem conj_apply_eq_sum (M H : Matrix (Fin n) (Fin n) ℤ) (k l : Fin n) :
    (Mᵀ * H * M) k l = ∑ a, ∑ b, M a k * H a b * M b l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The column operation of Lemma 2.1**: $\mathrm{diag}(d)\,(1 + e_i r^{\mathsf T})$, i.e. column $l$ is
$d_l e_l + r_l e_i$ (when $d_i = 1$). With $d = (u,\dots,1,\dots,u)$, $r_l = -c_l$ it clears row/column $i$;
with $d = 1$, $r = e_j$ (pivot index swapped) it is $x_j \mapsto x_j + x_i$. -/
def colOp (d r : Fin n → ℤ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal d * (1 + vecMulVec (Pi.single i (1:ℤ)) r)

/-- Entries of `colOp`. -/
theorem colOp_apply (d r : Fin n → ℤ) (i : Fin n) (hd : d i = 1) (a b : Fin n) :
    colOp d r i a b = (if a = b then d a else 0) + (if a = i then r b else 0) := by
  simp only [colOp, diagonal_mul, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- $\det(\mathrm{colOp}) = \prod_k d_k$ when $r_i = 0$. -/
theorem colOp_det (d r : Fin n → ℤ) (i : Fin n) (hr : r i = 0) :
    (colOp d r i).det = ∏ k, d k := by
  rw [colOp, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, det_diagonal]
  simp [hr]

/-- Entries of the congruence of $H$ by `colOp`. -/
theorem colOp_conj (H : Matrix (Fin n) (Fin n) ℤ) (d r : Fin n → ℤ) (i : Fin n) (hd : d i = 1)
    (k l : Fin n) :
    ((colOp d r i)ᵀ * H * colOp d r i) k l =
      d k * d l * H k l + d k * r l * H k i + r k * d l * H i l + r k * r l * H i i := by
  rw [conj_apply_eq_sum]
  simp only [colOp_apply d r i hd, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- $H$ has no off-diagonal entries outside the block $S \times S$. -/
def DiagOutside (H : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ k l, k ≠ l → (k ∉ S ∨ l ∉ S) → H k l = 0

/-- Congruence preserves symmetry. -/
theorem isSymm_conj {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsSymm) (E : Matrix (Fin n) (Fin n) ℤ) :
    (Eᵀ * H * E).IsSymm := by
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hH.eq, Matrix.mul_assoc]

/-- **Pivot step of Hanke 2004, Lemma 2.1** (p. 355): if $H_{ii} = \pi u$ with $p \nmid u$ and $\pi$ divides
row $i$, a column operation with determinant prime to $p$ clears row and column $i$ (no division). -/
theorem pivot_step {p : ℤ} (hp : Prime p) (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.IsSymm)
    (S : Finset (Fin n)) (hS : DiagOutside H S) (i : Fin n) (hi : i ∈ S) (π u : ℤ)
    (c : Fin n → ℤ) (hc : ∀ l, H i l = π * c l) (hii : H i i = π * u) (hu : ¬ p ∣ u) :
    ∃ E : Matrix (Fin n) (Fin n) ℤ, ¬ p ∣ E.det ∧ DiagOutside (Eᵀ * H * E) (S.erase i) := by
  set d : Fin n → ℤ := fun k => if k = i then 1 else u with hd
  set r : Fin n → ℤ := fun l => if l = i then 0 else -c l with hr
  have hdi : d i = 1 := by simp [hd]
  refine ⟨colOp d r i, ?_, ?_⟩
  · rw [colOp_det d r i (by simp [hr]), Prime.dvd_finsetProd_iff hp]
    rintro ⟨k, -, hk⟩
    by_cases hki : k = i
    · simp [hd, hki] at hk; exact hp.not_dvd_one hk
    · simp [hd, hki] at hk; exact hu hk
  · intro k l hkl hkS
    rw [colOp_conj H d r i hdi]
    by_cases hki : k = i
    · subst hki
      have hli : l ≠ k := Ne.symm hkl
      simp only [hd, hr, hli, ite_true, ite_false, one_mul, zero_mul, add_zero, hc l, hii]
      ring
    by_cases hli : l = i
    · subst hli
      simp only [hd, hr, hki, ite_true, ite_false, mul_one, mul_zero, zero_mul, add_zero, hii,
        hH.apply l k, hc k]
      ring
    have hk' : k ∉ S ∨ l ∉ S := by
      rcases hkS with h | h
      · left; intro hm; exact h (Finset.mem_erase.2 ⟨hki, hm⟩)
      · right; intro hm; exact h (Finset.mem_erase.2 ⟨hli, hm⟩)
    simp only [hd, hr, hki, hli, ite_false, hS k l hkl hk', hH.apply i k, hc k, hc l, hii]
    rcases hk' with h | h
    · have h0 : π * c k = 0 := by rw [← hc k]; exact hS i k (Ne.symm hki) (Or.inr h)
      linear_combination (-u * c l) * h0
    · have h0 : π * c l = 0 := by rw [← hc l]; exact hS i l (Ne.symm hli) (Or.inr h)
      linear_combination (-u * c k) * h0

/-- Composing congruences with determinants prime to $p$. -/
theorem conj_compose {p : ℤ} (hp : Prime p) (H E : Matrix (Fin n) (Fin n) ℤ) (hE : ¬ p ∣ E.det)
    (h : ∃ U : Matrix (Fin n) (Fin n) ℤ, ¬ p ∣ U.det ∧ ∃ D, Uᵀ * (Eᵀ * H * E) * U = diagonal D) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, ¬ p ∣ U.det ∧ ∃ D, Uᵀ * H * U = diagonal D := by
  obtain ⟨U, hU, D, hD⟩ := h
  refine ⟨E * U, ?_, D, ?_⟩
  · rw [det_mul]; intro h; rcases hp.dvd_or_dvd h with h | h <;> contradiction
  · rw [← hD, transpose_mul]; simp only [Matrix.mul_assoc]

/-- **Hanke 2004, Lemma 2.1 (p. 355), odd $p$, matrix form**: a symmetric integer matrix that is already
diagonal outside $S \times S$ is congruent, $U^{\mathsf T} H U = \mathrm{diag}(D)$, by an integer $U$ with
$p \nmid \det U$. Induction on $|S|$: take an entry of least $p$-valuation in $S \times S$; if neither of the
corresponding diagonal entries has that valuation, $x_i \mapsto x_i + x_j$ creates one ($p \nmid 2$); pivot. -/
theorem exists_conj_diagonal_aux {p : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2) (hpv : ∀ a : ℤ, a ≠ 0 →
      ∃ v : ℕ, ∃ w, a = p ^ v * w ∧ ¬ p ∣ w) :
    ∀ (m : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n)), S.card = m → H.IsSymm →
      DiagOutside H S → ∃ U : Matrix (Fin n) (Fin n) ℤ, ¬ p ∣ U.det ∧ ∃ D, Uᵀ * H * U = diagonal D := by
  intro m
  induction m with
  | zero =>
    intro H S hcard _ hS
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    refine ⟨1, by simpa using hp.not_dvd_one, fun k => H k k, ?_⟩
    ext k l
    simp only [transpose_one, Matrix.one_mul, Matrix.mul_one, diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hS k l h (Or.inl (Finset.notMem_empty k))
  | succ m ih =>
    intro H S hcard hH hS
    -- pivot at `i` and recurse on `S.erase i`
    have finish : ∀ H' : Matrix (Fin n) (Fin n) ℤ, H'.IsSymm → DiagOutside H' S → ∀ i ∈ S,
        ∀ π u : ℤ, (∀ l, π ∣ H' i l) → H' i i = π * u → ¬ p ∣ u →
        ∃ U : Matrix (Fin n) (Fin n) ℤ, ¬ p ∣ U.det ∧ ∃ D, Uᵀ * H' * U = diagonal D := by
      intro H' hH' hS' i hi π u hdvd hii hu
      choose c hc using hdvd
      obtain ⟨E, hE, hES⟩ := pivot_step hp H' hH' S hS' i hi π u c hc hii hu
      exact conj_compose hp H' E hE
        (ih _ (S.erase i) (by rw [Finset.card_erase_of_mem hi, hcard]; rfl) (isSymm_conj hH' E) hES)
    by_cases hz : ∃ k ∈ S, ∃ l ∈ S, H k l ≠ 0
    swap
    · push Not at hz
      refine ⟨1, by simpa using hp.not_dvd_one, fun k => H k k, ?_⟩
      ext k l
      simp only [transpose_one, Matrix.one_mul, Matrix.mul_one, diagonal_apply]
      split_ifs with h
      · rw [h]
      · by_cases hk : k ∈ S
        · by_cases hl : l ∈ S
          · exact hz k hk l hl
          · exact hS k l h (Or.inr hl)
        · exact hS k l h (Or.inl hk)
    obtain ⟨k0, hk0, l0, hl0, hkl0⟩ := hz
    -- an entry of least valuation
    classical
    set T := (S ×ˢ S).filter (fun e => H e.1 e.2 ≠ 0)
    have hTne : T.Nonempty := ⟨(k0, l0), by simp [T, hk0, hl0, hkl0]⟩
    choose val w hval hw using hpv
    obtain ⟨⟨i, j⟩, hijT, hmin⟩ :=
      Finset.exists_min_image T (fun e => if h : H e.1 e.2 = 0 then 0 else val _ h) hTne
    simp only [T, Finset.mem_filter, Finset.mem_product] at hijT
    obtain ⟨⟨hi, hj⟩, hij0⟩ := hijT
    set v := val (H i j) hij0
    have hdiv : ∀ k ∈ S, ∀ l ∈ S, p ^ v ∣ H k l := by
      intro k hk l hl
      by_cases h0 : H k l = 0
      · rw [h0]; exact dvd_zero _
      have := hmin (k, l) (by simp [T, hk, hl, h0])
      simp only [h0, hij0, dite_false] at this
      rw [hval (H k l) h0]
      exact Dvd.dvd.mul_right (pow_dvd_pow p this) _
    have hvij : H i j = p ^ v * w (H i j) hij0 := hval (H i j) hij0
    have hwij := hw (H i j) hij0
    set w0 := w (H i j) hij0
    have hpow0 : p ^ v ≠ 0 := pow_ne_zero _ hp.ne_zero
    -- row divisibility
    have hrow : ∀ i ∈ S, ∀ l, p ^ v ∣ H i l := by
      intro i hi l
      by_cases hl : l ∈ S
      · exact hdiv i hi l hl
      · rw [hS i l (by rintro rfl; exact hl hi) (Or.inr hl)]; exact dvd_zero _
    obtain ⟨s, hs⟩ := hdiv i hi i hi
    obtain ⟨t, ht⟩ := hdiv j hj j hj
    by_cases hps : p ∣ s
    swap
    · exact finish H hH hS i hi _ s (hrow i hi) hs hps
    by_cases hpt : p ∣ t
    swap
    · exact finish H hH hS j hj _ t (hrow j hj) ht hpt
    have hne : i ≠ j := by
      rintro rfl
      rw [hvij] at hs
      have := mul_left_cancel₀ hpow0 hs
      exact hwij (this ▸ hps)
    -- replace x_i by x_i + x_j
    set ei : Fin n → ℤ := Pi.single i 1 with hei
    set F := colOp (fun _ => 1) ei j
    have hF : ∀ k l, (Fᵀ * H * F) k l = H k l + ei l * H k j +
        ei k * H j l + ei k * ei l * H j j := by
      intro k l
      rw [colOp_conj H _ _ j rfl]
      ring
    have hFdet : ¬ p ∣ F.det := by
      rw [colOp_det _ _ j (by simp [hei, Ne.symm hne])]
      simpa using hp.not_dvd_one
    have hF2 : DiagOutside (Fᵀ * H * F) S := by
      intro k l hkl hkS
      rw [hF]
      rcases hkS with h | h
      · have hki : k ≠ i := by rintro rfl; exact h hi
        have hkj : k ≠ j := by rintro rfl; exact h hj
        simp [hei, Pi.single_apply, hki, hS k l hkl (Or.inl h), hS k j hkj (Or.inl h)]
      · have hli : l ≠ i := by rintro rfl; exact h hi
        have hlj : l ≠ j := by rintro rfl; exact h hj
        simp [hei, Pi.single_apply, hli, hS k l hkl (Or.inr h), hS j l (Ne.symm hlj) (Or.inr h)]
    refine conj_compose hp H F hFdet (finish _ (isSymm_conj hH F) hF2 i hi (p ^ v) (s + 2 * w0 + t)
      (fun l => ?_) ?_ ?_)
    · rw [hF]
      by_cases hl : l ∈ S
      · refine dvd_add (dvd_add (dvd_add (hdiv i hi l hl) (dvd_mul_of_dvd_right (hdiv i hi j hj) _))
          (dvd_mul_of_dvd_right (hdiv j hj l hl) _)) (dvd_mul_of_dvd_right (hdiv j hj j hj) _)
      · have hli : l ≠ i := by rintro rfl; exact hl hi
        have hlj : l ≠ j := by rintro rfl; exact hl hj
        simp [hei, hli, hS i l (Ne.symm hli) (Or.inr hl), hS j l (Ne.symm hlj) (Or.inr hl)]
    · rw [hF]
      simp only [hei, Pi.single_eq_same, hH.apply i j]
      linear_combination hs + ht + 2 * hvij
    · intro h
      have h2 : p ∣ 2 * w0 := by
        have := dvd_sub (dvd_sub h hps) hpt
        rwa [show s + 2 * w0 + t - s - t = 2 * w0 by ring] at this
      rcases hp.dvd_or_dvd h2 with h2 | h2
      · exact hp2 h2
      · exact hwij h2

/-- $2Q(\vec{x}) = \vec{x}^{\mathsf T} H \vec{x}$ for the Hessian $H = C + C^{\mathsf T}$. -/
theorem two_mul_eval_eq_hessian (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  have h := Q.evalIn_eq_dotProduct ℤ x
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, eval] at h ⊢
  have h2 : x ⬝ᵥ (x ᵥ* Q.coeff) = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [dotProduct_comm, ← dotProduct_mulVec]
  rw [hessian, add_mulVec, dotProduct_add, mulVec_transpose, h2, ← h]
  ring

/-- The Hessian is symmetric. -/
theorem hessian_isSymm (Q : QuadForm ℤ n) : Q.hessian.IsSymm := by
  simp [Matrix.IsSymm, hessian, add_comm]

/-- **Odd $p$: a diagonal form with the same counts** (Hanke 2004, Lemma 2.1, p. 355, case $p \nmid 2$):
for $Q$ nondegenerate and $p$ odd there are $a_i \ne 0$ with $r_{p^k}(Q, m) = r_{p^k}(\langle a_0, \dots, a_{n-1}\rangle, m)$
for all $k, m$.

*Proof.* Run the reduction of Lemma 2.1 over $\mathbb{Z}_{(p)}$ (rationals with denominator prime to $p$): take a
coefficient of least $p$-valuation; if it is off the diagonal, replace $x_i$ by $x_i + x_j$ (valid as $p \ne 2$)
to move it to the diagonal; clear its row and column, dividing only by $p$-units; induct. This gives
$U \in \mathrm{GL}_n(\mathbb{Z}_{(p)})$ with $Q(U\vec{x}) = \sum b_i x_i^2$. Choose $d \in \mathbb{Z}$, $p \nmid d$, with $dU$ integral;
then $Q(dU\vec{x}) = \sum d^2 b_i x_i^2$ has integer coefficients $a_i = d^2 b_i$, and
`repCount_eq_of_unimodular` (with $\det(dU)$ a $p$-unit) gives equal counts. Nondegeneracy gives $a_i \ne 0$. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem exists_diag_same_counts (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    ∃ a : Fin n → ℤ, (∀ i, a i ≠ 0) ∧ ∀ k m, repCount Q p k m = repCount (QuadForm.diag a) p k m := by
  have hpp : (p : ℕ).Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hpv : ∀ a : ℤ, a ≠ 0 → ∃ v : ℕ, ∃ w, a = (p : ℤ) ^ v * w ∧ ¬ (p : ℤ) ∣ w := by
    intro a ha
    obtain ⟨w, hw⟩ := padicValInt_dvd (p := p) a
    refine ⟨padicValInt p a, w, hw, ?_⟩
    rintro ⟨w', rfl⟩
    have h1 : (p : ℤ) ^ (padicValInt p a + 1) ∣ a := ⟨w', hw.trans (by ring)⟩
    rcases (padicValInt_dvd_iff (p := p) (padicValInt p a + 1) a).1 h1 with h | h
    · exact ha h
    · omega
  obtain ⟨U, hU, D, hD⟩ := exists_conj_diagonal_aux hpZ hp2 hpv _ Q.hessian Finset.univ rfl
    (hessian_isSymm Q) (fun k l _ h => by simp at h)
  -- 2 Q(Ux) = ∑ D_i x_i²
  have hval : ∀ x : Fin n → ℤ, 2 * Q.eval (U *ᵥ x) = ∑ i, D i * x i * x i := by
    intro x
    have hc : (U *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ * Q.hessian * U) *ᵥ x) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Uᵀ, vecMul_transpose]
    rw [two_mul_eval_eq_hessian, hc, hD]
    simp [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  set a : Fin n → ℤ := fun i => Q.eval (U *ᵥ Pi.single i 1) with ha
  have hDa : ∀ i, D i = 2 * a i := by
    intro i
    rw [ha]; dsimp only
    rw [hval]
    simp [Pi.single_apply]
  have hdiag : ∀ x : Fin n → ℤ, (QuadForm.diag a).eval x = ∑ i, a i * x i * x i := by
    intro x
    simp only [QuadForm.diag, evalIn, diagonal_apply, Algebra.algebraMap_self, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  have hQ' : ∀ x : Fin n → ℤ, (QuadForm.diag a).eval x = Q.eval (U *ᵥ x) := by
    intro x
    have h2 := hval x
    rw [hdiag]
    have : (2 : ℤ) * ∑ i, a i * x i * x i = 2 * Q.eval (U *ᵥ x) := by
      rw [h2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hDa]; ring
    exact (mul_left_cancel₀ two_ne_zero this)
  refine ⟨a, fun i hai => ?_, fun k m => (repCount_eq_of_unimodular Q _ U p hU hQ' k m).symm⟩
  have hdetU : U.det ≠ 0 := fun h => hU (h ▸ dvd_zero _)
  have hdet : (Uᵀ * Q.hessian * U).det ≠ 0 := by
    rw [det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetU hQ) hdetU
  rw [hD, det_diagonal] at hdet
  exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hDa, hai, mul_zero]))

/-- **Diagonal forms are in local normal form** with no 2-dimensional blocks and
$\nu_i = \mathrm{ord}_p(a_i)$ (for $a_i \ne 0$), linking `Reduction.lean`/`Stabilization.lean` to this file. -/
@[kb "hanke2004" "(2.3), p. 355"]
theorem isJordanForm_diag (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (p : ℕ) [Fact p.Prime] :
    IsJordanForm (QuadForm.diag a) p ∅ fun i => padicValInt p (a i) := by
  refine ⟨by simp, by simp, by simp, ?_, by simp, ?_⟩
  · intro i j hij _
    simp [QuadForm.diag, Matrix.diagonal, ne_of_lt hij]
  · intro i _
    obtain ⟨u, hu⟩ := padicValInt_dvd (p := p) (a i)
    refine ⟨u, by simpa [QuadForm.diag] using hu, ?_⟩
    rintro ⟨w, rfl⟩
    have h1 : (p:ℤ) ^ (padicValInt p (a i) + 1) ∣ a i :=
      ⟨w, hu.trans (by ring)⟩
    have := (padicValInt_dvd_iff (p := p) (padicValInt p (a i) + 1) (a i)).1 h1
    rcases this with h | h
    · exact ha i h
    · omega

/-! ### Helpers for `exists_jordanForm` (the case $p = 2$, Lemma 2.1 via Conway–Sloane pp. 369–370) -/

/-- **The integral form $\vec{x}^{\mathsf T} M \vec{x}$** of an arbitrary (not necessarily symmetric or upper
triangular) integer matrix $M$: coefficients $c_{ii} = M_{ii}$ and $c_{ij} = M_{ij} + M_{ji}$ for $i < j$. -/
def ofMatrixZ (M : Matrix (Fin n) (Fin n) ℤ) : QuadForm ℤ n where
  coeff := Matrix.of fun i j => if i < j then M i j + M j i else if i = j then M i i else 0
  upper := by
    intro i j h
    simp only [id] at h
    simp [Matrix.of_apply, not_lt.mpr h.le, (ne_of_lt h).symm]

/-- `ofMatrixZ M` evaluates to $\vec{x}^{\mathsf T} M \vec{x}$. -/
theorem eval_ofMatrixZ (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (ofMatrixZ M).eval x = x ⬝ᵥ (M *ᵥ x) := by
  have hL : (ofMatrixZ M).eval x = ∑ i, ∑ j, ((if i < j then M i j * x i * x j else 0)
      + (if i < j then M j i * x j * x i else 0) + (if i = j then M i j * x i * x j else 0)) := by
    simp only [QuadForm.evalIn, ofMatrixZ, Matrix.of_apply, algebraMap_int_eq, eq_intCast,
      Int.cast_id]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.le, h.ne]; ring
    · simp
    · simp [h, not_le.mpr h, not_lt.mpr h.le, h.ne']
  have hR : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, ((if i < j then M i j * x i * x j else 0)
      + (if j < i then M i j * x i * x j else 0) + (if i = j then M i j * x i * x j else 0)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le, h.ne]; ring
    · simp; ring
    · simp [h, not_lt.mpr h.le, h.ne']; ring
  rw [hL, hR]
  simp only [Finset.sum_add_distrib]
  congr 2
  rw [Finset.sum_comm]

/-- The Hessian of `ofMatrixZ M` is $M + M^{\mathsf T}$. -/
theorem hessian_ofMatrixZ (M : Matrix (Fin n) (Fin n) ℤ) : (ofMatrixZ M).hessian = M + Mᵀ := by
  ext i j
  simp only [QuadForm.hessian, ofMatrixZ, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp
  · simp [h, not_lt.mpr h.le, h.ne']; ring

/-- **Partial local normal form at 2** of a symmetric integer matrix $G$ (a Hessian), used as the
induction invariant in Lemma 2.1 for $p = 2$: the coordinates in `D` are already split off, as
2-dimensional blocks on the pairs in `P` (off-diagonal Hessian entry $2^{\nu}\cdot$odd, diagonal entries
divisible by $2^{\nu+1}$) and 1-dimensional blocks (diagonal entry $2^{\nu+1}\cdot$odd), and they are
orthogonal to all other coordinates. -/
def JInv (G : Matrix (Fin n) (Fin n) ℤ) (D : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) : Prop :=
  (∀ e ∈ P, e.1 < e.2 ∧ e.1 ∈ D ∧ e.2 ∈ D) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i ≠ j → (i ∈ D ∨ j ∈ D) → (i, j) ∉ P → (j, i) ∉ P → G i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, G e.1 e.2 = 2 ^ ν e.1 * b ∧ ¬ (2:ℤ) ∣ b) ∧
    (2:ℤ) ^ (ν e.1 + 1) ∣ G e.1 e.1 ∧ (2:ℤ) ^ (ν e.1 + 1) ∣ G e.2 e.2) ∧
  (∀ i ∈ D, ¬ IsPaired P i → ∃ u, G i i = 2 ^ (ν i + 1) * u ∧ ¬ (2:ℤ) ∣ u)

/-- **Clearing step with odd determinant** (the row/column operations of Lemma 2.1 done over $\mathbb{Z}$):
for symmetric $G$, a pivot set `S` and the remaining coordinates `R`, if columns $k \in R$ can be replaced
by $\delta e_k + \sum_{b \in S} w_{bk} e_b$ ($\delta$ odd) orthogonal to `S`, the resulting $V$ has odd
determinant, $V^{\mathsf T} G V$ agrees with $G$ off `R`, and is orthogonal between `R` and its complement. -/
theorem clear_step (G : Matrix (Fin n) (Fin n) ℤ) (hG : Gᵀ = G) (D S R : Finset (Fin n))
    (hR : ∀ l, l ∈ R ↔ l ∉ D ∧ l ∉ S) (hSD : ∀ s ∈ S, s ∉ D)
    (hD : ∀ l ∈ D, ∀ m, m ∉ D → G l m = 0)
    (δ : ℤ) (hδ : ¬ (2:ℤ) ∣ δ) (w : Fin n → Fin n → ℤ) (hw : ∀ b k, b ∉ S → w b k = 0)
    (hclear : ∀ s ∈ S, ∀ k ∈ R, δ * G s k + ∑ b, G s b * w b k = 0) :
    ∃ V : Matrix (Fin n) (Fin n) ℤ, ¬ (2:ℤ) ∣ V.det ∧
      (∀ l m, l ∉ R → m ∉ R → (Vᵀ * G * V) l m = G l m) ∧
      (∀ l k, l ∉ R → k ∈ R → (Vᵀ * G * V) l k = 0 ∧ (Vᵀ * G * V) k l = 0) := by
  classical
  set V : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun b k =>
    if k ∈ R then (if b = k then δ else 0) + w b k else (if b = k then 1 else 0) with hV
  have hGV : ∀ l k, (G * V) l k = if k ∈ R then δ * G l k + ∑ b, G l b * w b k else G l k := by
    intro l k
    simp only [Matrix.mul_apply, hV, Matrix.of_apply]
    split_ifs with hk
    · simp [mul_add, Finset.sum_add_distrib, mul_comm]
    · simp
  have hVl : ∀ l m, l ∉ R → (Vᵀ * G * V) l m = (G * V) l m := by
    intro l m hl
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp [hV, Matrix.transpose_apply, hl]
  have hsym : (Vᵀ * G * V)ᵀ = Vᵀ * G * V := by
    simp [Matrix.transpose_mul, hG, Matrix.mul_assoc]
  have hB1 : ∀ l k, l ∉ R → k ∈ R → (Vᵀ * G * V) l k = 0 := by
    intro l k hl hk
    rw [hVl l k hl, hGV, if_pos hk]
    by_cases hlS : l ∈ S
    · exact hclear l hlS k hk
    · have hlD : l ∈ D := by
        by_contra h
        exact hl ((hR l).2 ⟨h, hlS⟩)
      have hkD : k ∉ D := ((hR k).1 hk).1
      rw [hD l hlD k hkD, mul_zero, zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : b ∈ S
      · rw [hD l hlD b (hSD b hb), zero_mul]
      · rw [hw b k hb, mul_zero]
  have hdet : ¬ (2:ℤ) ∣ V.det := by
    set Dg : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal fun b => if b ∈ R then δ else 1 with hDg
    set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun b k => if k ∈ R then w b k else 0 with hN
    have hwR : ∀ b k, b ∈ R → w b k = 0 := fun b k hb => hw b k ((hR b).1 hb).2
    have hfac : V = Dg * (1 + N) := by
      ext b k
      simp only [hV, hDg, hN, Matrix.diagonal_mul, Matrix.of_apply, Matrix.add_apply,
        Matrix.one_apply]
      by_cases hk : k ∈ R <;> by_cases hbk : b = k
      · subst hbk; simp [hk, hwR b b hk]
      · by_cases hb : b ∈ R
        · simp [hk, hbk, hb, hwR b k hb]
        · simp [hk, hbk, hb]
      · subst hbk; simp [hk]
      · simp [hk, hbk]
    have hNN : N * N = 0 := by
      ext b k
      simp only [Matrix.mul_apply, hN, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c ∈ R
      · simp [hc, hwR c k hc]
      · simp [hc]
    have hinv : (1 + N) * (1 - N) = 1 := by
      rw [mul_sub, mul_one, add_mul, one_mul, hNN]; abel
    have h1 : (1 + N).det = 1 ∨ (1 + N).det = -1 := by
      have := congrArg Matrix.det hinv
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact Int.eq_one_or_neg_one_of_mul_eq_one this
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
    intro h2
    have h2' : (2:ℤ) ∣ ∏ b, (if b ∈ R then δ else 1) := by
      rcases h1 with h | h <;> rw [h] at h2
      · simpa using h2
      · simpa using h2
    obtain ⟨b, _, hb⟩ := (Prime.dvd_finsetProd_iff Int.prime_two _).1 h2'
    split_ifs at hb
    · exact hδ hb
    · norm_num at hb
  refine ⟨V, hdet, ?_, ?_⟩
  · intro l m hl hm
    rw [hVl l m hl, hGV, if_neg hm]
  · intro l k hl hk
    refine ⟨hB1 l k hl hk, ?_⟩
    rw [← hsym, Matrix.transpose_apply]
    exact hB1 l k hl hk

/-- **Combining a split-off pivot block with the invariant** (bookkeeping for Lemma 2.1). -/
theorem jinv_step_finish (G G' : Matrix (Fin n) (Fin n) ℤ) (D S R : Finset (Fin n))
    (P PS : Finset (Fin n × Fin n)) (ν νS : Fin n → ℕ)
    (hR : ∀ l, l ∈ R ↔ l ∉ D ∧ l ∉ S) (hSD : ∀ s ∈ S, s ∉ D)
    (hA : ∀ l m, l ∉ R → m ∉ R → G' l m = G l m)
    (hB : ∀ l k, l ∉ R → k ∈ R → G' l k = 0 ∧ G' k l = 0)
    (hJ : JInv G D P ν)
    (hS1 : ∀ e ∈ PS, e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S)
    (hS2 : ∀ e ∈ PS, ∀ e' ∈ PS, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hS3 : ∀ i j, i ∈ S → j ∈ S → i ≠ j → (i, j) ∉ PS → (j, i) ∉ PS → G i j = 0)
    (hS4 : ∀ e ∈ PS, νS e.1 = νS e.2 ∧ (∃ b, G e.1 e.2 = 2 ^ νS e.1 * b ∧ ¬ (2:ℤ) ∣ b) ∧
      (2:ℤ) ^ (νS e.1 + 1) ∣ G e.1 e.1 ∧ (2:ℤ) ^ (νS e.1 + 1) ∣ G e.2 e.2)
    (hS5 : ∀ i ∈ S, ¬ IsPaired PS i → ∃ u, G i i = 2 ^ (νS i + 1) * u ∧ ¬ (2:ℤ) ∣ u) :
    JInv G' (D ∪ S) (P ∪ PS) (fun l => if l ∈ D then ν l else νS l) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  have nR : ∀ l, l ∈ D ∨ l ∈ S → l ∉ R := fun l hl hlR => by
    rcases hl with hl | hl
    · exact ((hR l).1 hlR).1 hl
    · exact ((hR l).1 hlR).2 hl
  have hne : ∀ x y, x ∈ D → y ∈ S → x ≠ y := fun x y hx hy h => hSD y hy (h ▸ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨a, b, c⟩ := h1 e he
      exact ⟨a, Finset.mem_union_left _ b, Finset.mem_union_left _ c⟩
    · obtain ⟨a, b, c⟩ := hS1 e he
      exact ⟨a, Finset.mem_union_right _ b, Finset.mem_union_right _ c⟩
  · intro e he e' he' hee
    rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
    · exact h2 e he e' he' hee
    · obtain ⟨-, a, b⟩ := h1 e he
      obtain ⟨-, c, d⟩ := hS1 e' he'
      exact ⟨hne _ _ a c, hne _ _ a d, hne _ _ b c, hne _ _ b d⟩
    · obtain ⟨-, a, b⟩ := hS1 e he
      obtain ⟨-, c, d⟩ := h1 e' he'
      exact ⟨(hne _ _ c a).symm, (hne _ _ d a).symm, (hne _ _ c b).symm, (hne _ _ d b).symm⟩
    · exact hS2 e he e' he' hee
  · intro i j hij hor hP1 hP2
    have hP1' : (i, j) ∉ P := fun h => hP1 (Finset.mem_union_left _ h)
    have hP2' : (j, i) ∉ P := fun h => hP2 (Finset.mem_union_left _ h)
    have hQ1 : (i, j) ∉ PS := fun h => hP1 (Finset.mem_union_right _ h)
    have hQ2 : (j, i) ∉ PS := fun h => hP2 (Finset.mem_union_right _ h)
    by_cases hiR : i ∈ R
    · have hj : j ∉ R := by
        rcases hor with h | h
        · exact absurd hiR (nR i (Finset.mem_union.1 h))
        · exact nR j (Finset.mem_union.1 h)
      exact (hB j i hj hiR).2
    by_cases hjR : j ∈ R
    · exact (hB i j hiR hjR).1
    rw [hA i j hiR hjR]
    have hi' : i ∈ D ∨ i ∈ S := by
      by_contra h; push_neg at h; exact hiR ((hR i).2 h)
    have hj' : j ∈ D ∨ j ∈ S := by
      by_contra h; push_neg at h; exact hjR ((hR j).2 h)
    by_cases hiD : i ∈ D
    · exact h3 i j hij (Or.inl hiD) hP1' hP2'
    by_cases hjD : j ∈ D
    · exact h3 i j hij (Or.inr hjD) hP1' hP2'
    exact hS3 i j (hi'.resolve_left hiD) (hj'.resolve_left hjD) hij hQ1 hQ2
  · intro e he
    dsimp only
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨-, d2, d3⟩ := h1 e he
      obtain ⟨a, ⟨b, hb, hb2⟩, c, d⟩ := h4 e he
      have r1 := nR e.1 (Or.inl d2)
      have r2 := nR e.2 (Or.inl d3)
      rw [if_pos d2, if_pos d3, hA _ _ r1 r2, hA _ _ r1 r1, hA _ _ r2 r2]
      exact ⟨a, ⟨b, hb, hb2⟩, c, d⟩
    · obtain ⟨-, d2, d3⟩ := hS1 e he
      obtain ⟨a, ⟨b, hb, hb2⟩, c, d⟩ := hS4 e he
      have r1 := nR e.1 (Or.inr d2)
      have r2 := nR e.2 (Or.inr d3)
      rw [if_neg (hSD _ d2), if_neg (hSD _ d3), hA _ _ r1 r2, hA _ _ r1 r1, hA _ _ r2 r2]
      exact ⟨a, ⟨b, hb, hb2⟩, c, d⟩
  · intro i hi hnp
    dsimp only
    have hnp1 : ¬ IsPaired P i := fun ⟨e, he, h⟩ => hnp ⟨e, Finset.mem_union_left _ he, h⟩
    have hnp2 : ¬ IsPaired PS i := fun ⟨e, he, h⟩ => hnp ⟨e, Finset.mem_union_right _ he, h⟩
    rcases Finset.mem_union.1 hi with hi | hi
    · rw [if_pos hi, hA i i (nR i (Or.inl hi)) (nR i (Or.inl hi))]
      exact h5 i hi hnp1
    · rw [if_neg (hSD i hi), hA i i (nR i (Or.inr hi)) (nR i (Or.inr hi))]
      exact hS5 i hi hnp2

/-- **One step of Lemma 2.1 at $p = 2$** (Conway–Sloane pp. 369–370): if $G = c + c^{\mathsf T}$ is nondegenerate
and satisfies the invariant on `D ≠ univ`, take an entry of least 2-adic valuation $\mu$ among the
remaining coordinates; if one lies on the diagonal split off a 1-dimensional block, otherwise split off
the 2-dimensional block on an off-diagonal entry $2^\mu\beta$ ($\beta$ odd). The change of variables has
odd determinant. -/
theorem jinv_step (c : Matrix (Fin n) (Fin n) ℤ) (D : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hdet : (c + cᵀ).det ≠ 0) (hJ : JInv (c + cᵀ) D P ν) (hD : D ≠ Finset.univ) :
    ∃ (V : Matrix (Fin n) (Fin n) ℤ) (D' : Finset (Fin n)) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), ¬ (2:ℤ) ∣ V.det ∧ D ⊂ D' ∧ JInv (Vᵀ * (c + cᵀ) * V) D' P' ν' := by
  classical
  set G := c + cᵀ with hGdef
  have hGs : Gᵀ = G := by simp [hGdef, add_comm]
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    rw [← Matrix.transpose_apply G i j, hGs]
  have heven : ∀ i, (2:ℤ) ∣ G i i := fun i => ⟨c i i, by simp [hGdef]; ring⟩
  have hJ0 := hJ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  have hcross : ∀ l ∈ D, ∀ m, m ∉ D → G l m = 0 := by
    intro l hl m hm
    refine h3 l m (fun h => hm (h ▸ hl)) (Or.inl hl) (fun h => hm (h1 _ h).2.2)
      (fun h => hm (h1 _ h).2.1)
  have hnz : ∃ k l, k ∉ D ∧ l ∉ D ∧ G k l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ : ∃ k, k ∉ D := by
      by_contra h
      push_neg at h
      exact hD (Finset.eq_univ_iff_forall.2 h)
    apply hdet
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro l
    by_cases hl : l ∈ D
    · exact hcross l hl k hk
    · exact hcon l k hl hk
  obtain ⟨μ, hμdiv, hμnd⟩ : ∃ μ : ℕ, (∀ k l, k ∉ D → l ∉ D → (2:ℤ) ^ μ ∣ G k l) ∧
      ∃ k l, k ∉ D ∧ l ∉ D ∧ ¬ (2:ℤ) ^ (μ + 1) ∣ G k l := by
    have hex : ∃ μ : ℕ, ∃ k l, k ∉ D ∧ l ∉ D ∧ ¬ (2:ℤ) ^ (μ + 1) ∣ G k l := by
      obtain ⟨k, l, hk, hl, hne⟩ := hnz
      refine ⟨(G k l).natAbs, k, l, hk, hl, fun hdvd => ?_⟩
      have h6 := Int.natAbs_dvd_natAbs.2 hdvd
      have hle := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h6
      rw [Int.natAbs_pow] at hle
      have h7 := (G k l).natAbs.lt_two_pow_self
      have h8 : 2 ^ (G k l).natAbs ≤ 2 ^ ((G k l).natAbs + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
      simp at hle
      omega
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    intro k l hk hl
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push_neg at this
      have h := this k l hk hl
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [e] at h
  by_cases hdiag : ∃ i, i ∉ D ∧ ¬ (2:ℤ) ^ (μ + 1) ∣ G i i
  · -- 1-dimensional block
    obtain ⟨i, hiD, hi⟩ := hdiag
    have hμ1 : 1 ≤ μ := by
      rcases Nat.eq_zero_or_pos μ with h0 | h0
      · exfalso; apply hi; rw [h0]; simpa using heven i
      · exact h0
    obtain ⟨u, hu⟩ := hμdiv i i hiD hiD
    have hu2 : ¬ (2:ℤ) ∣ u := by
      rintro ⟨v, hv⟩; apply hi; exact ⟨v, by rw [hu, hv]; ring⟩
    set S : Finset (Fin n) := {i} with hS
    set R : Finset (Fin n) := Finset.univ.filter fun l => l ∉ D ∧ l ∉ S with hRdef
    have hR : ∀ l, l ∈ R ↔ l ∉ D ∧ l ∉ S := by intro l; simp [hRdef]
    have hSD : ∀ s ∈ S, s ∉ D := by
      intro s hs; rw [Finset.mem_singleton.1 hs]; exact hiD
    obtain ⟨V, hV, hA, hB⟩ := clear_step G hGs D S R hR hSD hcross u hu2
      (fun b k => if b = i then -(G i k / 2 ^ μ) else 0)
      (by intro b k hb; simp [hS] at hb; simp [hb])
      (by
        intro s hs k hk
        rw [Finset.mem_singleton.1 hs]
        have hk' := ((hR k).1 hk).1
        have ht := (Int.mul_ediv_cancel' (hμdiv i k hiD hk')).symm
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination u * ht - (G i k / 2 ^ μ) * hu)
    refine ⟨V, D ∪ S, P ∪ ∅, fun l => if l ∈ D then ν l else (fun _ => μ - 1) l, hV, ?_, ?_⟩
    · rw [Finset.ssubset_iff]
      exact ⟨i, hiD, by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h, hS]⟩
    · refine jinv_step_finish G _ D S R P ∅ ν (fun _ => μ - 1) hR hSD hA hB hJ0
        (by simp) (by simp) ?_ (by simp) ?_
      · intro a b ha hb hab
        rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb] at hab
        exact absurd rfl hab
      · intro a ha _
        rw [Finset.mem_singleton.1 ha, Nat.sub_add_cancel hμ1]
        exact ⟨u, hu, hu2⟩
  · -- 2-dimensional block
    push_neg at hdiag
    obtain ⟨k, l, hk, hl, hkl⟩ := hμnd
    have hne : k ≠ l := by rintro rfl; exact hkl (hdiag k hk)
    obtain ⟨i, j, hi, hj, hij, hb⟩ : ∃ i j, i ∉ D ∧ j ∉ D ∧ i < j ∧ ¬ (2:ℤ) ^ (μ + 1) ∣ G i j := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨k, l, hk, hl, h, hkl⟩
      · exact ⟨l, k, hl, hk, h, by rwa [hsym]⟩
    obtain ⟨a', ha⟩ := hdiag i hi
    obtain ⟨c', hc⟩ := hdiag j hj
    obtain ⟨β, hβ⟩ := hμdiv i j hi hj
    have hβ2 : ¬ (2:ℤ) ∣ β := by
      rintro ⟨v, hv⟩; apply hb; exact ⟨v, by rw [hβ, hv]; ring⟩
    have hji : G j i = 2 ^ μ * β := by rw [hsym]; exact hβ
    have hδ : ¬ (2:ℤ) ∣ 4 * a' * c' - β ^ 2 := by
      intro h
      have : (2:ℤ) ∣ β ^ 2 := by
        have h' : (2:ℤ) ∣ 4 * a' * c' := ⟨2 * a' * c', by ring⟩
        have := dvd_sub h' h
        simpa using this
      exact hβ2 (Int.prime_two.dvd_of_dvd_pow this)
    have hij' : i ≠ j := hij.ne
    set S : Finset (Fin n) := {i, j} with hS
    set R : Finset (Fin n) := Finset.univ.filter fun l => l ∉ D ∧ l ∉ S with hRdef
    have hR : ∀ l, l ∈ R ↔ l ∉ D ∧ l ∉ S := by intro l; simp [hRdef]
    have hSD : ∀ s ∈ S, s ∉ D := by
      intro s hs
      rcases Finset.mem_insert.1 hs with h | h
      · rw [h]; exact hi
      · rw [Finset.mem_singleton.1 h]; exact hj
    obtain ⟨V, hV, hA, hB⟩ := clear_step G hGs D S R hR hSD hcross (4 * a' * c' - β ^ 2) hδ
      (fun b k => (if b = i then β * (G j k / 2 ^ μ) - 2 * c' * (G i k / 2 ^ μ) else 0) +
        (if b = j then β * (G i k / 2 ^ μ) - 2 * a' * (G j k / 2 ^ μ) else 0))
      (by
        intro b k hb
        have hbi : b ≠ i := fun h => hb (by simp [hS, h])
        have hbj : b ≠ j := fun h => hb (by simp [hS, h])
        simp [hbi, hbj])
      (by
        intro s hs k hk
        have hk' := ((hR k).1 hk).1
        have hx := (Int.mul_ediv_cancel' (hμdiv i k hi hk')).symm
        have hy := (Int.mul_ediv_cancel' (hμdiv j k hj hk')).symm
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rcases Finset.mem_insert.1 hs with h | h
        · rw [h]
          linear_combination (4 * a' * c' - β ^ 2) * hx +
            (β * (G j k / 2 ^ μ) - 2 * c' * (G i k / 2 ^ μ)) * ha +
            (β * (G i k / 2 ^ μ) - 2 * a' * (G j k / 2 ^ μ)) * hβ
        · rw [Finset.mem_singleton.1 h]
          linear_combination (4 * a' * c' - β ^ 2) * hy +
            (β * (G j k / 2 ^ μ) - 2 * c' * (G i k / 2 ^ μ)) * hji +
            (β * (G i k / 2 ^ μ) - 2 * a' * (G j k / 2 ^ μ)) * hc)
    refine ⟨V, D ∪ S, P ∪ {(i, j)}, fun l => if l ∈ D then ν l else (fun _ => μ) l, hV, ?_, ?_⟩
    · rw [Finset.ssubset_iff]
      exact ⟨i, hi, by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h, hS]⟩
    · refine jinv_step_finish G _ D S R P {(i, j)} ν (fun _ => μ) hR hSD hA hB hJ0
        ?_ ?_ ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_singleton.1 he]
        exact ⟨hij, by simp [hS], by simp [hS]⟩
      · intro e he e' he' hee
        rw [Finset.mem_singleton.1 he, Finset.mem_singleton.1 he'] at hee
        exact absurd rfl hee
      · intro a b ha hb hab hP1 hP2
        exfalso
        rcases Finset.mem_insert.1 ha with ha | ha <;>
          rcases Finset.mem_insert.1 hb with hb | hb
        · exact hab (ha.trans hb.symm)
        · rw [Finset.mem_singleton.1 hb] at hP1; rw [ha] at hP1; exact hP1 (by simp)
        · rw [Finset.mem_singleton.1 ha] at hP2; rw [hb] at hP2; exact hP2 (by simp)
        · exact hab ((Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm)
      · intro e he
        rw [Finset.mem_singleton.1 he]
        exact ⟨rfl, ⟨β, hβ, hβ2⟩, ⟨a', ha⟩, ⟨c', hc⟩⟩
      · intro a ha hnp
        exfalso
        apply hnp
        rcases Finset.mem_insert.1 ha with h | h
        · exact ⟨(i, j), by simp, Or.inl h.symm⟩
        · exact ⟨(i, j), by simp, Or.inr (Finset.mem_singleton.1 h).symm⟩

/-- **Lemma 2.1 at $p = 2$, matrix form** (induction on the number of coordinates not yet split off):
every nondegenerate $G = c + c^{\mathsf T}$ satisfying the invariant on `D` can be brought, by an integer change
of variables $V$ with odd determinant, to $V^{\mathsf T} G V$ satisfying the invariant on all coordinates. -/
theorem jinv_complete_aux : ∀ (k : ℕ) (c : Matrix (Fin n) (Fin n) ℤ) (D : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ), Dᶜ.card = k → (c + cᵀ).det ≠ 0 →
    JInv (c + cᵀ) D P ν → ∃ (V : Matrix (Fin n) (Fin n) ℤ) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), ¬ (2:ℤ) ∣ V.det ∧ JInv (Vᵀ * (c + cᵀ) * V) Finset.univ P' ν' := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c D P ν hk hdet hJ
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨1, P, ν, by simp, by simpa using hJ⟩
  obtain ⟨V, D', P', ν', hV, hDD, hJ'⟩ := jinv_step c D P ν hdet hJ hD
  have hc' : Vᵀ * (c + cᵀ) * V = (Vᵀ * c * V) + (Vᵀ * c * V)ᵀ := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hV0 : V.det ≠ 0 := fun h => hV (h ▸ dvd_zero 2)
  have hdet' : ((Vᵀ * c * V) + (Vᵀ * c * V)ᵀ).det ≠ 0 := by
    rw [← hc', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hV0 hdet) hV0
  have hlt : D'ᶜ.card < k := by
    rw [← hk, Finset.card_compl, Finset.card_compl]
    have h1 := Finset.card_lt_card hDD
    have h2 := Finset.card_le_univ D'
    omega
  obtain ⟨W, P'', ν'', hW, hJ''⟩ :=
    ih _ hlt (Vᵀ * c * V) D' P' ν' rfl hdet' (by rw [← hc']; exact hJ')
  refine ⟨V * W, P'', ν'', ?_, ?_⟩
  · rw [Matrix.det_mul]
    intro h2
    rcases Int.prime_two.dvd_or_dvd h2 with h | h
    · exact hV h
    · exact hW h
  · have : (V * W)ᵀ * (c + cᵀ) * (V * W) = Wᵀ * (Vᵀ * c * V + (Vᵀ * c * V)ᵀ) * W := by
      rw [← hc']; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this]; exact hJ''

/-- The invariant on all coordinates for the Hessian of `Q` is exactly the local normal form at 2. -/
theorem isJordanForm_two_of_jinv (Q : QuadForm ℤ n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ)
    (hJ : JInv Q.hessian Finset.univ P ν) : IsJordanForm Q 2 P ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  have hoff : ∀ i j, i < j → Q.hessian i j = Q.coeff i j := by
    intro i j hij
    simp [QuadForm.hessian, Q.upper (show id i < id j from hij)]
  have hdi : ∀ i, Q.hessian i i = 2 * Q.coeff i i := by
    intro i; simp [QuadForm.hessian]; ring
  refine ⟨fun _ => rfl, fun e he => (h1 e he).1, h2, ?_, ?_, ?_⟩
  · intro i j hij hP
    rw [← hoff i j hij]
    exact h3 i j hij.ne (Or.inl (Finset.mem_univ _)) hP
      (fun h => absurd (h1 _ h).1 (not_lt.2 hij.le))
  · intro e he
    obtain ⟨a, ⟨b, hb, hb2⟩, c, d⟩ := h4 e he
    have hc : ∀ i, (2:ℤ) ^ (ν e.1 + 1) ∣ Q.hessian i i → (2:ℤ) ^ ν e.1 ∣ Q.coeff i i := by
      intro i h
      rw [hdi, pow_succ, mul_comm 2] at h
      exact (mul_dvd_mul_iff_right two_ne_zero).1 h
    refine ⟨a, ⟨b, ?_, by exact_mod_cast hb2⟩, ?_, ?_⟩
    · rw [← hoff _ _ (h1 e he).1]; exact_mod_cast hb
    · exact_mod_cast hc _ c
    · exact_mod_cast hc _ d
  · intro i hi
    obtain ⟨u, hu, hu2⟩ := h5 i (Finset.mem_univ _) hi
    refine ⟨u, ?_, by exact_mod_cast hu2⟩
    rw [hdi, pow_succ] at hu
    have : (2:ℤ) * Q.coeff i i = 2 * (2 ^ ν i * u) := by rw [hu]; ring
    exact_mod_cast mul_left_cancel₀ two_ne_zero this

/-- **Existence of a local normal form with the same counts** (Hanke 2004, Lemma 2.1, p. 355): for a
nondegenerate integral form $Q$ and a prime $p$ there is an integral form $Q'$ in local normal form at
$p$ (with 2-dimensional blocks only if $p = 2$) such that $r_{p^k}(Q, m) = r_{p^k}(Q', m)$ for all $k, m$.

*Proof.* For odd $p$: `exists_diag_same_counts` and `isJordanForm_diag`. For $p = 2$: the same
reduction over $\mathbb{Z}_{(2)}$ (Lemma 2.1, following Conway–Sloane, *SPLAG* 3rd ed., pp. 369–370, cited as [CS] in the paper), splitting off a 2-dimensional
block $\begin{pmatrix} 2^\nu\alpha & 2^\nu\beta \\ 2^\nu\beta & 2^\nu\gamma\end{pmatrix}$ when the least valuation is off the
diagonal, then clear denominators by an odd $d$ and apply `repCount_eq_of_unimodular`. (The remarks
below about $\mathbb{Z}_p$-approximation are an alternative route.) The counts mod
$p^k$ are invariant under $\vec{x} \mapsto U\vec{x}$ for $U \in \mathrm{GL}_n(\mathbb{Z}_p)$. Finally replace the
$\mathbb{Z}_p$-coefficients of the normal form by integers agreeing with them modulo a high power $p^K$
(keeping the block shape, units and valuations): a nondegenerate form and a form sufficiently close to
it $p$-adically are $\mathbb{Z}_p$-equivalent (Cassels, *Rational Quadratic Forms*, Ch. 8 [unverified locator];
precision $K > \mathrm{ord}_p(\det) + 2\,\mathrm{ord}_p(2) + 1$ suffices), so the integral form has
the same counts for **all** $k$. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem exists_jordanForm (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime] :
    ∃ (Q' : QuadForm ℤ n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q' p P ν ∧ Q'.Nondegenerate ∧ (p ≠ 2 → P = ∅) ∧
        ∀ k m, repCount Q p k m = repCount Q' p k m := by
  classical
  by_cases hp : p = 2
  · subst hp
    have hJ0 : JInv (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
      refine ⟨by simp, by simp, ?_, by simp, by simp⟩
      intro i j _ h
      simp at h
    obtain ⟨V, P, ν, hV, hJ⟩ := jinv_complete_aux _ Q.coeff ∅ ∅ (fun _ => 0) rfl hQ hJ0
    set Q' := ofMatrixZ (Vᵀ * Q.coeff * V) with hQ'
    have hH : Q'.hessian = Vᵀ * (Q.coeff + Q.coeffᵀ) * V := by
      rw [hQ', hessian_ofMatrixZ]
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    have heval : ∀ x, Q'.eval x = Q.eval (V *ᵥ x) := by
      intro x
      rw [hQ', eval_ofMatrixZ]
      show _ = Q.evalIn ℤ (V *ᵥ x)
      rw [QuadForm.evalIn_eq_dotProduct]
      simp only [algebraMap_int_eq, eq_intCast, Int.cast_id]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
      congr 2
    refine ⟨Q', P, ν, isJordanForm_two_of_jinv Q' P ν (hH ▸ hJ), ?_, fun h => absurd rfl h,
      fun k m => (repCount_eq_of_unimodular Q Q' V 2 (by exact_mod_cast hV) heval k m).symm⟩
    show Q'.hessian.det ≠ 0
    have hV0 : V.det ≠ 0 := fun h => hV (h ▸ dvd_zero 2)
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hV0 hQ) hV0
  · obtain ⟨a, ha, hc⟩ := exists_diag_same_counts Q hQ p hp
    refine ⟨QuadForm.diag a, ∅, fun i => padicValInt p (a i), isJordanForm_diag a ha p, ?_,
      fun _ => rfl, hc⟩
    show (QuadForm.diag a).hessian.det ≠ 0
    simp only [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add,
      Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by have := ha i; omega

end QuadFormsKB.LocalDensity
