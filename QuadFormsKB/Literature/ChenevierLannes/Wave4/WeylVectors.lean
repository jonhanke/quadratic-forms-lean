/-
# Chenevier–Lannes, §3.4.2: Weyl vectors of Niemeier lattices

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition-Definition 2.3.3 (c), p. 35, and Scholium 2.3.4,
p. 36; §3.4.2, Proposition 3.4.2.1 (Borcherds), p. 65, Proposition 3.4.2.2, Corollary 3.4.2.3 and Proposition 3.4.2.4,
p. 66. Printed page numbers.

**Layer.** Even unimodular lattices as integral forms $Q = q_L$ on $L = \mathbb{Z}^n$ (`EvenUnimodular.lean`); the
book's inner product is $x \cdot y$ = `bQ Q x y` on $V = \mathbb{Q}^n$ (`bZ` on $L$), with $x \cdot x = 2q(x)$
(`bQ_self_eq`); roots $R = R(L)$ are the $\alpha \in L$ with $q(\alpha) = 1$ (`rootSet`, as the finite set `rootFin`).
The book works in $V = \mathbb{R} \otimes L$; every statement below is linear or polynomial with rational coefficients,
so the rational points carry it. A Weyl vector (`IsWeylVector`) is $\rho$ with $2\rho = \sum_{\alpha \in R^+}
\alpha$, $R^+ = \{\alpha \in R : \alpha \cdot \xi > 0\}$ (`posRoots Q ξ`) for a vector $\xi$ orthogonal to no root.
The Coxeter number is $h = h(L) = |R(L)|/24$ (`coxeterNumber`, the book's Proposition-Definition 2.3.3 (c)).

**Input.** Venkov's identity `VenkovRootSum 24` (Proposition 2.3.2, wave 2; the book proves it with theta series with
harmonic coefficients, not formalized here). Every result below is **conditional** on it, and on nothing else.

**Proves** (conditional on `VenkovRootSum 24`):
- `venkov_polar` (Scholium 2.3.4, polarized): $\sum_{\alpha \in R}(\alpha \cdot x)(\alpha \cdot y) = 2h\,x \cdot y$;
- `coxeterNumber_eq_nat` (Proposition-Definition 2.3.3 (c), integrality): if $R(L) \ne \emptyset$, $h(L)$ is a natural
  number (from Venkov's identity at a root and a parity count of the roots $\beta$ with $\alpha \cdot \beta = 1$);
- `venkov_half`, `prop_3_4_2_2_a` (Proposition 3.4.2.2 (a)): $h\,x \cdot y = \sum_{\alpha \in R^+}(\alpha\cdot x)
  (\alpha \cdot y)$, for $R^+$ any half of $R$ (one of $\pm\alpha$ for each root), in particular for a chamber;
- `prop_3_4_2_2_b` (Proposition 3.4.2.2 (b), Borcherds): $h\,q(x) - \rho \cdot x = \sum_{\alpha \in R^+}
  \frac{(\alpha \cdot x)^2 - \alpha \cdot x}{2}$;
- `coxeter_smul_eq_sum` ($h\,x = \sum_{\alpha \in R^+} (\alpha \cdot x)\,\alpha$, the vector form of (a)) and
  `coxeter_smul_mem_rootSpan` (Corollary 3.4.2.3): $h$ annihilates $Q(R)^\sharp/Q(R)$;
- `prop_3_4_2_4` (Proposition 3.4.2.4): $h\,q(\xi) - \rho \cdot \xi \in \mathbb{Z}$ for $\xi \in Q(R)^\sharp$;
- `weylVector_mem_lattice`, `weylVectorIntegral_of_venkov` (Proposition 3.4.2.1, Borcherds): a Weyl vector of a
  Niemeier lattice with roots lies in $L$.

Unconditional helpers: `eq_cv_of_bQ_int` (a unimodular lattice is its own dual: $\rho \in V$ with $\rho \cdot L
\subset \mathbb{Z}$ lies in $L$), `eq_of_bQ_eq` (nondegeneracy), `lexPos_iff_not_neg` (a half of $R$ exists).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave3.Statements

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### The inner product on $V = \mathbb{Q}^n$ -/

/-- $x \cdot x = 2\,q(x)$. -/
theorem bQ_self_eq (Q : QuadForm ℤ n) (x : Fin n → ℚ) : bQ Q x x = 2 * Q.evalIn ℚ x := by
  have h := evalIn_add_smulQ Q x x 1
  rw [one_smul, ← two_smul ℚ x, evalIn_smulQ] at h
  linarith

/-- The inner product is symmetric. -/
theorem bQ_symm (Q : QuadForm ℤ n) (x y : Fin n → ℚ) : bQ Q x y = bQ Q y x := by
  unfold bQ
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, (hessian_isSymm Q).eq]

theorem bQ_neg_left (Q : QuadForm ℤ n) (x y : Fin n → ℚ) : bQ Q (-x) y = -bQ Q x y := by
  simp [bQ]

theorem bQ_zero_left (Q : QuadForm ℤ n) (y : Fin n → ℚ) : bQ Q 0 y = 0 := by
  simp [bQ]

theorem bQ_sum_left (Q : QuadForm ℤ n) {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) (y : Fin n → ℚ) :
    bQ Q (∑ i ∈ s, f i) y = ∑ i ∈ s, bQ Q (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bQ_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bQ_add_left, ih]

theorem cv_neg' (y : Fin n → ℤ) : cv (-y) = -cv y := by
  ext i
  simp [cv]

theorem bZ_neg_left (Q : QuadForm ℤ n) (x v : Fin n → ℤ) : bZ Q (-x) v = -bZ Q x v := by
  rw [← neg_one_smul ℤ x, bZ_smul_left]
  ring

/-- $\rho = (\rho\,H)\,\operatorname{adj}(H)$ for $\det H = 1$ (rows times the Gram matrix, then the adjugate). -/
theorem vecMul_hessian_adjugate {Q : QuadForm ℤ n} (hdet : Q.hessian.det = 1) (ρ : Fin n → ℚ) :
    ρ = (ρ ᵥ* Q.hessian.map (algebraMap ℤ ℚ)) ᵥ* (Q.hessian.adjugate.map (algebraMap ℤ ℚ)) := by
  have hadj : Q.hessian.adjugate.map (algebraMap ℤ ℚ) = (Q.hessian.map (algebraMap ℤ ℚ)).adjugate := by
    have := RingHom.map_adjugate (algebraMap ℤ ℚ) Q.hessian
    simpa [RingHom.mapMatrix_apply] using this
  have hd : (Q.hessian.map (algebraMap ℤ ℚ)).det = 1 := by
    have := RingHom.map_det (algebraMap ℤ ℚ) Q.hessian
    rw [hdet] at this
    simpa [RingHom.mapMatrix_apply] using this.symm
  rw [vecMul_vecMul, hadj, mul_adjugate, hd, one_smul, vecMul_one]

/-- **Nondegeneracy**: for $\det H = 1$, a vector $v \in V$ with $v \cdot y = 0$ for every $y \in V$ is $0$; hence two
vectors with the same inner products are equal. -/
theorem eq_of_bQ_eq {Q : QuadForm ℤ n} (hdet : Q.hessian.det = 1) {v w : Fin n → ℚ}
    (h : ∀ y, bQ Q v y = bQ Q w y) : v = w := by
  classical
  have hv : (v - w) ᵥ* Q.hessian.map (algebraMap ℤ ℚ) = 0 := by
    ext i
    have := h (Pi.single i 1)
    simp only [bQ, dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [sub_vecMul, Pi.sub_apply, Pi.zero_apply, this, sub_self]
  have := vecMul_hessian_adjugate hdet (v - w)
  rw [hv, zero_vecMul] at this
  exact sub_eq_zero.mp this

/-- **A unimodular lattice is its own dual** (Chenevier–Lannes, §2.1; used in the proof of Proposition 3.4.2.1,
p. 66): if $\det H = 1$ and $\rho \in V$ has $\rho \cdot y \in \mathbb{Z}$ for every $y \in L = \mathbb{Z}^n$, then
$\rho \in L$. Unconditional. -/
theorem eq_cv_of_bQ_int {Q : QuadForm ℤ n} (hdet : Q.hessian.det = 1) {ρ : Fin n → ℚ}
    (h : ∀ y : Fin n → ℤ, ∃ k : ℤ, bQ Q ρ (cv y) = k) : ∃ r : Fin n → ℤ, ρ = cv r := by
  classical
  choose k hk using fun i => h (Pi.single i 1)
  have hcv : ∀ i : Fin n, cv (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℚ) := fun i => by
    ext j
    by_cases hj : j = i
    · subst hj; simp [cv]
    · simp [cv, Pi.single_apply, hj]
  have hc : ρ ᵥ* Q.hessian.map (algebraMap ℤ ℚ) = cv k := by
    ext i
    have := hk i
    rw [hcv] at this
    simp only [bQ, dotProduct_mulVec, dotProduct_single, mul_one] at this
    simpa [cv] using this
  refine ⟨k ᵥ* Q.hessian.adjugate, ?_⟩
  rw [vecMul_hessian_adjugate (Q := Q) hdet ρ, hc]
  ext j
  simp [cv, vecMul, dotProduct, Matrix.map_apply]

/-! ### The finite set of roots and its halves -/

/-- **The roots of $L$ as a finite set** (`rootSet Q` is finite for $Q$ positive definite, `rootSet_finite`). -/
noncomputable def rootFin (Q : QuadForm ℤ n) : Finset (Fin n → ℤ) := by
  classical
  exact if h : (rootSet Q).Finite then h.toFinset else ∅

theorem rootFin_eq {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : rootFin Q = (rootSet_finite hQ).toFinset := by
  unfold rootFin
  split_ifs with h
  · rfl
  · exact absurd (rootSet_finite hQ) h

theorem mem_rootFin {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {α : Fin n → ℤ} :
    α ∈ rootFin Q ↔ α ∈ rootSet Q := by
  rw [rootFin_eq hQ, Set.Finite.mem_toFinset]

theorem root_ne_zero {Q : QuadForm ℤ n} {α : Fin n → ℤ} (hα : α ∈ rootSet Q) : α ≠ 0 := by
  intro h
  exact root_ne_neg hα (by rw [h, neg_zero])

/-- **The positive roots of the chamber of $\xi$** (Chenevier–Lannes, §3.4.2, p. 65): $R^+ = \{\alpha \in R :
\alpha \cdot \xi > 0\}$. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 65 (positive roots R+ of a chamber)"]
noncomputable def posRoots (Q : QuadForm ℤ n) (ξ : Fin n → ℚ) : Finset (Fin n → ℤ) :=
  (rootFin Q).filter fun α => 0 < bQ Q (cv α) ξ

/-- Summing an even function over the roots is twice the sum over a half $S$ of them (a set containing exactly one of
$\alpha, -\alpha$ for each root). -/
theorem sum_eq_two_mul_sum_filter {R : Finset (Fin n → ℤ)} (hneg : ∀ α ∈ R, -α ∈ R)
    (P : (Fin n → ℤ) → Prop) [DecidablePred P] (hP : ∀ α ∈ R, (P α ↔ ¬ P (-α)))
    (F : (Fin n → ℤ) → ℚ) (hF : ∀ α, F (-α) = F α) :
    ∑ α ∈ R, F α = 2 * ∑ α ∈ R.filter P, F α := by
  rw [← Finset.sum_filter_add_sum_filter_not R P, two_mul]
  congr 1
  refine Finset.sum_nbij' (fun α => -α) (fun α => -α) ?_ ?_ ?_ ?_ ?_
  · intro α hα
    simp only [Finset.mem_filter] at hα ⊢
    refine ⟨hneg α hα.1, ?_⟩
    have := hP (-α) (hneg α hα.1)
    rw [neg_neg] at this
    exact this.mpr hα.2
  · intro α hα
    simp only [Finset.mem_filter] at hα ⊢
    exact ⟨hneg α hα.1, (hP α hα.1).mp hα.2⟩
  · intro α _; simp
  · intro α _; simp
  · intro α _; rw [hF]

/-- For $\xi$ orthogonal to no root, $R^+$ is a half of $R$: exactly one of $\alpha, -\alpha$ is positive. -/
theorem pos_iff_not_neg {Q : QuadForm ℤ n} {ξ : Fin n → ℚ} (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0)
    {α : Fin n → ℤ} (hα : α ∈ rootSet Q) : 0 < bQ Q (cv α) ξ ↔ ¬ 0 < bQ Q (cv (-α)) ξ := by
  rw [cv_neg', bQ_neg_left]
  have := hξ α hα
  constructor
  · intro h; linarith
  · intro h; push Not at h; exact lt_of_le_of_ne (by linarith) (Ne.symm this)

/-- **A lexicographic half**: $\alpha$ is lexicographically positive if its first nonzero coordinate is positive. -/
def lexPos (α : Fin n → ℤ) : Prop := ∃ i, 0 < α i ∧ ∀ j < i, α j = 0

/-- For $\alpha \ne 0$, exactly one of $\alpha, -\alpha$ is lexicographically positive. -/
theorem lexPos_iff_not_neg {α : Fin n → ℤ} (hα : α ≠ 0) : lexPos α ↔ ¬ lexPos (-α) := by
  classical
  have hne : (Finset.univ.filter fun j => α j ≠ 0).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hα
    exact ⟨k, by simpa using hk⟩
  set i := (Finset.univ.filter fun j => α j ≠ 0).min' hne
  have hi : α i ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hlt : ∀ j < i, α j = 0 := fun j hj => by
    by_contra h
    have := Finset.min'_le (Finset.univ.filter fun j => α j ≠ 0) j (by simp [h])
    exact absurd hj (not_lt.mpr this)
  have key : ∀ β : Fin n → ℤ, (∀ j < i, β j = 0) → β i ≠ 0 → (lexPos β ↔ 0 < β i) := by
    intro β hβ hβi
    constructor
    · rintro ⟨i', hpos, hz⟩
      rcases lt_trichotomy i' i with h | h | h
      · exact absurd (hβ i' h) hpos.ne'
      · exact h ▸ hpos
      · exact absurd (hz i h) hβi
    · intro h
      exact ⟨i, h, hβ⟩
  rw [key α hlt hi, key (-α) (fun j hj => by simp [hlt j hj]) (by simpa using hi)]
  simp only [Pi.neg_apply, neg_pos, not_lt]
  exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hi)⟩

/-! ### Venkov's identity over $\mathbb{Q}$ and its polarization -/

theorem latDot_ratCast (Q : QuadForm ℤ n) (α : Fin n → ℤ) (x : Fin n → ℚ) :
    latDot Q α (fun i => (x i : ℝ)) = ((bQ Q (cv α) x : ℚ) : ℝ) := by
  simp [latDot, bQ, dotProduct, mulVec, Matrix.map_apply, cv]

theorem evalIn_ratCast (Q : QuadForm ℤ n) (x : Fin n → ℚ) :
    Q.evalIn ℝ (fun i => (x i : ℝ)) = ((Q.evalIn ℚ x : ℚ) : ℝ) := by
  simpa [Function.comp_def] using (AWS.evalIn_map Q (Rat.castHom ℝ) x).symm

/-- **Scholium 2.3.4 over $\mathbb{Q}$**: **conditional** on `VenkovRootSum 24`, $\sum_{\alpha \in R}(\alpha\cdot x)^2
= 2h\,x\cdot x$ for a Niemeier lattice and $x \in \mathbb{Q}^{24}$. -/
theorem venkovQ (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) (x : Fin 24 → ℚ) :
    ∑ α ∈ rootFin Q, bQ Q (cv α) x ^ 2 = 2 * coxeterNumber Q * bQ Q x x := by
  have h := scholium_2_3_4 hV hQ (fun i => (x i : ℝ))
  rw [finsum_mem_eq_finite_toFinset_sum _ (rootSet_finite hQ.posDef), ← rootFin_eq hQ.posDef] at h
  simp only [latDot_ratCast, evalIn_ratCast] at h
  rw [bQ_self_eq]
  exact_mod_cast h

/-- **Scholium 2.3.4, polarized** (Chenevier–Lannes, p. 36, and Proposition 3.4.2.2 (a), p. 66): **conditional** on
`VenkovRootSum 24`. For a Niemeier lattice $L$ and $x, y \in V$,
$$\sum_{\alpha \in R(L)} (\alpha \cdot x)(\alpha \cdot y) = 2h\; x \cdot y.$$ -/
@[kb "chenevierlannes2019" "Scholium 2.3.4, p. 36 (polarized; conditional)"]
theorem venkov_polar (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) (x y : Fin 24 → ℚ) :
    ∑ α ∈ rootFin Q, bQ Q (cv α) x * bQ Q (cv α) y = 2 * coxeterNumber Q * bQ Q x y := by
  have h1 := venkovQ hV hQ (x + y)
  have h2 := venkovQ hV hQ x
  have h3 := venkovQ hV hQ y
  have e : ∀ α, bQ Q (cv α) (x + y) ^ 2 =
      bQ Q (cv α) x ^ 2 + 2 * (bQ Q (cv α) x * bQ Q (cv α) y) + bQ Q (cv α) y ^ 2 := fun α => by
    rw [bQ_add_right]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  rw [bQ_add_left, bQ_add_right, bQ_add_right, bQ_symm Q y x] at h1
  linear_combination (h1 - h2 - h3) / 2

/-! ### The Coxeter number is an integer -/

/-- **The Coxeter number $h(L)$ is an integer** (Chenevier–Lannes, Proposition-Definition 2.3.3 (c), p. 35):
**conditional** on `VenkovRootSum 24`. If a Niemeier lattice $L$ has roots, $h(L) = |R(L)|/24 \in \mathbb{N}$.
*Proof.* For a root $\alpha$ the roots $\beta$ with $\beta \cdot \alpha = \pm 1$ number $4h - 8$
(`card_root_dot_pm_one_twentyFour`); $\beta \mapsto -\beta$ exchanges the signs, and $\beta \mapsto \alpha - \beta$ is
a fixed-point-free involution of $\{\beta : \beta \cdot \alpha = 1\}$, so $4 \mid 4h - 8$. (The book reads this off the
classification of root systems: $h$ is the Coxeter number of the components.) -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3 (c), p. 35 (h(L) is an integer; conditional)"]
theorem coxeterNumber_eq_nat (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    (hR : (rootSet Q).Nonempty) : ∃ m : ℕ, coxeterNumber Q = m := by
  classical
  obtain ⟨α, hα⟩ := hR
  have hc := card_root_dot_pm_one_twentyFour hV hQ hα
  set T := (rootSet_finite hQ.posDef).toFinset with hT
  have hα1 : Q.eval α = 1 := hα
  have hmemT : ∀ β, β ∈ T ↔ Q.eval β = 1 := fun β => by rw [hT, Set.Finite.mem_toFinset]; rfl
  have hsplit : T.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1) =
      T.filter (fun β => bZ Q β α = 1) ∪ T.filter (fun β => bZ Q β α = -1) := Finset.filter_or _ _ _
  have hdisj : Disjoint (T.filter (fun β => bZ Q β α = 1)) (T.filter (fun β => bZ Q β α = -1)) := by
    rw [Finset.disjoint_filter]
    intro β _ h1 h2
    omega
  have hneg : (T.filter (fun β => bZ Q β α = -1)).card = (T.filter (fun β => bZ Q β α = 1)).card := by
    refine Finset.card_nbij' (fun β => -β) (fun β => -β) ?_ ?_ ?_ ?_
    · intro β hβ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmemT] at hβ ⊢
      refine ⟨?_, by rw [bZ_neg_left, hβ.2]; norm_num⟩
      have := neg_mem_rootSet (Q := Q) (α := β) hβ.1
      exact this
    · intro β hβ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmemT] at hβ ⊢
      refine ⟨?_, by rw [bZ_neg_left, hβ.2]⟩
      exact neg_mem_rootSet (Q := Q) (α := β) hβ.1
    · intro β _; simp
    · intro β _; simp
  have heven : 2 ∣ (T.filter (fun β => bZ Q β α = 1)).card := by
    have hmem : ∀ β ∈ T.filter (fun β => bZ Q β α = 1), α - β ∈ T.filter (fun β => bZ Q β α = 1) := by
      intro β hβ
      simp only [Finset.mem_filter, hmemT] at hβ ⊢
      have hab : bZ Q α β = 1 := by rw [bZ_comm]; exact hβ.2
      have e := eval_add_smulZ Q α β (-1)
      rw [neg_one_smul, ← sub_eq_add_neg, hα1, hab, hβ.1] at e
      refine ⟨by rw [e]; norm_num, ?_⟩
      rw [sub_eq_add_neg, ← neg_one_smul ℤ β, bZ_add_left, bZ_smul_left, bZ_self, hα1, hβ.2]
      norm_num
    have := Finset.sum_involution (s := T.filter (fun β => bZ Q β α = 1)) (f := fun _ => (1 : ZMod 2))
      (fun β _ => α - β) (fun _ _ => by decide) (fun β hβ _ h => by
        simp only [Finset.mem_filter, hmemT] at hβ
        have h2 : α = β + (1 : ℤ) • β := by rw [one_smul]; rw [sub_eq_iff_eq_add] at h; exact h
        have e := eval_add_smulZ Q β β 1
        rw [← h2, hα1, bZ_self, hβ.1] at e
        norm_num at e)
      hmem (fun β _ => by simp)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact (ZMod.natCast_eq_zero_iff _ 2).mp this
  obtain ⟨j, hj⟩ := heven
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hneg, hj] at hc
  have hq : ((2 * j + 2 * j : ℕ) : ℚ) = 4 * coxeterNumber Q - 8 := by exact_mod_cast hc
  push_cast at hq
  have h3 : coxeterNumber Q = (j : ℚ) + 2 := by linarith
  exact ⟨j + 2, by rw [h3]; push_cast; ring⟩

/-! ### Proposition 3.4.2.2 -/

/-- **Proposition 3.4.2.2 (a) for any half of $R$** (Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`.
If $S \subset R$ contains exactly one of $\alpha, -\alpha$ for each root (`P` its indicator), then
$h\,x \cdot y = \sum_{\alpha \in S} (\alpha \cdot x)(\alpha \cdot y)$. -/
theorem venkov_half (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    {P : (Fin 24 → ℤ) → Prop} [DecidablePred P] (hP : ∀ α ∈ rootSet Q, (P α ↔ ¬ P (-α))) (x y : Fin 24 → ℚ) :
    coxeterNumber Q * bQ Q x y = ∑ α ∈ (rootFin Q).filter P, bQ Q (cv α) x * bQ Q (cv α) y := by
  have h := venkov_polar hV hQ x y
  rw [sum_eq_two_mul_sum_filter (fun α hα => (mem_rootFin hQ.posDef).mpr
      (neg_mem_rootSet ((mem_rootFin hQ.posDef).mp hα))) P
      (fun α hα => hP α ((mem_rootFin hQ.posDef).mp hα))
      (fun α => bQ Q (cv α) x * bQ Q (cv α) y) (fun α => by simp only [cv_neg', bQ_neg_left]; ring)] at h
  linarith

/-- **Proposition 3.4.2.2 (a)** (Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`. For a Niemeier lattice
$L$, a vector $\xi$ orthogonal to no root (a chamber) and $x, y \in V$,
$$h\; x \cdot y = \sum_{\alpha \in R^+} (\alpha \cdot x)(\alpha \cdot y).$$ -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.2 (a), p. 66 (conditional)"]
theorem prop_3_4_2_2_a (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (x y : Fin 24 → ℚ) :
    coxeterNumber Q * bQ Q x y = ∑ α ∈ posRoots Q ξ, bQ Q (cv α) x * bQ Q (cv α) y :=
  venkov_half hV hQ (P := fun α => 0 < bQ Q (cv α) ξ) (fun α hα => pos_iff_not_neg hξ hα) x y

/-- A Weyl vector in the sense of `IsWeylVector` has $2\rho = \sum_{\alpha \in R^+}\alpha$ as a finite sum. -/
theorem IsWeylVector.exists_posRoots {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {ρ : Fin n → ℚ}
    (hρ : IsWeylVector Q ρ) :
    ∃ ξ : Fin n → ℚ, (∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) ∧ (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α := by
  obtain ⟨ξ, hξ, h2⟩ := hρ
  refine ⟨ξ, hξ, ?_⟩
  rw [h2]
  apply finsum_cond_eq_sum_of_cond_iff
  intro α _
  simp [posRoots, Finset.mem_filter, mem_rootFin hQ]

/-- **Proposition 3.4.2.2 (b) (Borcherds)** (Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`. For a
Niemeier lattice $L$, $\xi$ orthogonal to no root, $\rho$ the Weyl vector of the chamber of $\xi$
($2\rho = \sum_{\alpha \in R^+} \alpha$) and $x \in V$,
$$h\,q(x) - \rho \cdot x = \sum_{\alpha \in R^+} \frac{(\alpha \cdot x)^2 - \alpha \cdot x}{2}.$$ -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.2 (b), p. 66 (conditional)"]
theorem prop_3_4_2_2_b (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α) (x : Fin 24 → ℚ) :
    coxeterNumber Q * Q.evalIn ℚ x - bQ Q ρ x =
      ∑ α ∈ posRoots Q ξ, (bQ Q (cv α) x ^ 2 - bQ Q (cv α) x) / 2 := by
  have ha := prop_3_4_2_2_a hV hQ hξ x x
  have hb : 2 * bQ Q ρ x = ∑ α ∈ posRoots Q ξ, bQ Q (cv α) x := by
    rw [← bQ_smul_left, hρ, bQ_sum_left]
  rw [bQ_self_eq] at ha
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [sq]
  rw [← hb, ← ha]
  ring

/-! ### Corollary 3.4.2.3 and Proposition 3.4.2.4 -/

/-- **$h\,x = \sum_{\alpha \in S} (\alpha \cdot x)\,\alpha$** for any half $S$ of $R$ (the vector form of
Proposition 3.4.2.2 (a), Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`. -/
theorem coxeter_smul_eq_sum (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    {P : (Fin 24 → ℤ) → Prop} [DecidablePred P] (hP : ∀ α ∈ rootSet Q, (P α ↔ ¬ P (-α))) (x : Fin 24 → ℚ) :
    coxeterNumber Q • x = ∑ α ∈ (rootFin Q).filter P, bQ Q (cv α) x • cv α := by
  apply eq_of_bQ_eq hQ.det_one
  intro y
  rw [bQ_smul_left, bQ_sum_left, venkov_half hV hQ hP x y]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [bQ_smul_left]

/-- **Corollary 3.4.2.3** (Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`. For a Niemeier lattice $L$
with root lattice $Q(R) = \mathbb{Z}R$, the quotient $Q(R)^\sharp / Q(R)$ is annihilated by $h$: if $\xi \in V$ has
$\alpha \cdot \xi \in \mathbb{Z}$ for every root $\alpha$ (i.e. $\xi \in Q(R)^\sharp$), then $h\,\xi \in Q(R)$, the
$\mathbb{Z}$-span of the roots in $V$. -/
@[kb "chenevierlannes2019" "Cor. 3.4.2.3, p. 66 (conditional)"]
theorem coxeter_smul_mem_rootSpan (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    {ξ : Fin 24 → ℚ} (hξ : ∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) ξ = k) :
    coxeterNumber Q • ξ ∈ Submodule.span ℤ (cv '' rootSet Q) := by
  classical
  rw [coxeter_smul_eq_sum hV hQ (P := lexPos) (fun α hα => lexPos_iff_not_neg (root_ne_zero hα)) ξ]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hαR : α ∈ rootSet Q := (mem_rootFin hQ.posDef).mp (Finset.mem_filter.mp hα).1
  obtain ⟨k, hk⟩ := hξ α hαR
  rw [hk, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ k (Submodule.subset_span ⟨α, hαR, rfl⟩)

/-- $\frac{k^2 - k}{2} \in \mathbb{Z}$ for $k \in \mathbb{Z}$. -/
theorem half_sq_sub_int (k : ℤ) : ∃ r : ℤ, (((k : ℚ) ^ 2 - k) / 2) = r := by
  obtain ⟨r, hr⟩ := Int.even_mul_pred_self k
  refine ⟨r, ?_⟩
  have : ((k * (k - 1) : ℤ) : ℚ) = r + r := by exact_mod_cast hr
  push_cast at this
  linear_combination this / 2

/-- A finite sum of rationals that are integers is an integer. -/
theorem exists_int_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, ∃ k : ℤ, f i = k) :
    ∃ k : ℤ, ∑ i ∈ s, f i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k1, hk1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨k2, hk2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨k1 + k2, by rw [Finset.sum_insert ha, hk1, hk2]; push_cast; ring⟩

/-- **Proposition 3.4.2.4** (Chenevier–Lannes, p. 66): **conditional** on `VenkovRootSum 24`. For a Niemeier lattice $L$
with Weyl vector $\rho$ (of the chamber of $\xi$) and $\eta \in Q(R)^\sharp$ ($\alpha \cdot \eta \in \mathbb{Z}$ for
every root), $h\,q(\eta) - \rho \cdot \eta \in \mathbb{Z}$; that is, the class of $\rho$ in $Q(R)^\sharp/Q(R)$ is
characterized by $h\,q(\eta) \equiv \rho \cdot \eta \pmod{\mathbb{Z}}$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.4, p. 66 (conditional)"]
theorem prop_3_4_2_4 (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) {ξ ρ : Fin 24 → ℚ}
    (hξ : ∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) (hρ : (2 : ℚ) • ρ = ∑ α ∈ posRoots Q ξ, cv α) {η : Fin 24 → ℚ}
    (hη : ∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) η = k) :
    ∃ m : ℤ, coxeterNumber Q * Q.evalIn ℚ η - bQ Q ρ η = m := by
  rw [prop_3_4_2_2_b hV hQ hξ hρ η]
  refine exists_int_sum _ _ fun α hα => ?_
  have hαR : α ∈ rootSet Q := (mem_rootFin hQ.posDef).mp (Finset.mem_filter.mp hα).1
  obtain ⟨k, hk⟩ := hη α hαR
  rw [hk]
  exact half_sq_sub_int k

/-! ### Proposition 3.4.2.1 (Borcherds) -/

/-- **Proposition 3.4.2.1 (Borcherds)** (Chenevier–Lannes, p. 65): **conditional** on `VenkovRootSum 24`. A Weyl vector
$\rho$ of a Niemeier lattice $L$ with roots lies in $L$. *Proof* (the book's, p. 66): for $y \in L$,
$\rho \cdot y \equiv h\,q(y) \pmod{\mathbb{Z}}$ (Proposition 3.4.2.4, $L \subset Q(R)^\sharp$), and $h\,q(y) \in
\mathbb{Z}$ ($h$ is an integer, `coxeterNumber_eq_nat`); so $\rho \in L^\sharp = L$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.1, p. 65 (conditional)"]
theorem weylVector_mem_lattice (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) : ∃ r : Fin 24 → ℤ, ρ = cv r := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨m, hm⟩ := coxeterNumber_eq_nat hV hQ' hR
  obtain ⟨ξ, hξ, h2⟩ := hρ.exists_posRoots hQ'.posDef
  apply eq_cv_of_bQ_int hQ'.det_one
  intro y
  obtain ⟨k, hk⟩ := prop_3_4_2_4 hV hQ' hξ h2 (η := cv y) fun α _ => ⟨bZ Q α y, bQ_cv Q α y⟩
  refine ⟨m * Q.eval y - k, ?_⟩
  rw [hm, evalIn_cv] at hk
  push_cast
  linarith

/-- **Proposition 3.4.2.1 in the named form** `WeylVectorIntegral`: **conditional** on `VenkovRootSum 24`. -/
theorem weylVectorIntegral_of_venkov (hV : VenkovRootSum 24) : WeylVectorIntegral :=
  fun _ hQ hR _ hρ => weylVector_mem_lattice hV hQ hR hρ

end QuadFormsKB.ChenevierLannes
