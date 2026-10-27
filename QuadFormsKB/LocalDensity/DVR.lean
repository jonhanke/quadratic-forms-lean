/-
# Local densities over a DVR: counts, types, density, and the printed normal form

**Layer:** DVR (the number-field lift: $R$ a discrete valuation ring with uniformizer $\pi$ and residue field of
size $q$, e.g. the completion $\mathfrak{o}_\mathfrak{p}$ of a number field, or $\mathbb{Z}_p$). **Defines** the DVR
analogues of `Basic.lean`: `DVR.repCount` ($r_{\pi^k}(m)$ in $(R/\pi^k)^n$, pp. 356–357), the types of Def. 3.1
(p. 358), `DVR.localDensity` ((5.2), p. 368, corrected), and the *printed* normal form `DVR.IsJordanForm`
((2.3), Lemma 2.1, p. 355). **Proves** Lemma 2.1 as printed under $\pi^2 \nmid 2$ (`DVR.exists_jordanForm`; it
fails at ramified dyadic primes) and $\mathrm{GL}_n(R)$-invariance of counts.
**Depends on** `JordanReduction.lean` (shared notation: `IsPaired`, `unimodularCoords`, `nuI`, `nuII`).
-/
import QuadFormsKB.LocalDensity.JordanReduction

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **$q$, the size of the residue field** $R/\pi$ (finite in all cases of interest). -/
noncomputable def q (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : ℕ :=
  Nat.card (IsLocalRing.ResidueField R)

/-- **$r_{\pi^k}(m)$:** the number of $\vec{x} \in (R/\pi^k)^n$ with $Q(\vec{x}) \equiv m \pmod{\pi^k}$ (Hanke 2004,
pp. 356–357, $r_{\mathfrak{p}^k,Q}(m)$). -/
noncomputable def repCount (Q : QuadForm R n) (π : R) (k : ℕ) (m : R) : ℕ :=
  Nat.card {x : Fin n → R ⧸ Ideal.span {π ^ k} //
    Q.evalIn (R ⧸ Ideal.span {π ^ k}) x = Ideal.Quotient.mk _ m}

/-- **Zero type** (Hanke 2004, Def. 3.1): $\vec{x} \equiv \vec{0} \pmod \pi$. -/
def IsZeroType (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) : Prop :=
  ∀ i, Ideal.Quotient.mk _ π ∣ x i

/-- **Good type** (Hanke 2004, Def. 3.1), relative to the unimodular coordinates $S_0$ of a local
Jordan splitting: not Zero type, and $x_i \not\equiv 0 \pmod \pi$ for some $i \in S_0$. -/
def IsGoodType (S₀ : Finset (Fin n)) (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) : Prop :=
  ¬ IsZeroType π k x ∧ ∃ i ∈ S₀, ¬ Ideal.Quotient.mk _ π ∣ x i

/-- **Bad type** (Hanke 2004, Def. 3.1): neither Zero nor Good type. -/
def IsBadType (S₀ : Finset (Fin n)) (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) : Prop :=
  ¬ IsZeroType π k x ∧ ¬ IsGoodType S₀ π k x

/-- **Solutions of a given type** mod $\pi^k$. -/
noncomputable def repCountOf (Q : QuadForm R n) (π : R) (k : ℕ) (m : R)
    (T : (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop) : ℕ :=
  Nat.card {x : Fin n → R ⧸ Ideal.span {π ^ k} //
    Q.evalIn (R ⧸ Ideal.span {π ^ k}) x = Ideal.Quotient.mk _ m ∧ T x}

/-- **The local density** $\beta_\pi(m) = \lim_k r_{\pi^k}(m)/q^{k(n-1)}$ (Hanke 2004, (5.1)–(5.2), p. 368, with
the corrected exponent). -/
noncomputable def localDensity (Q : QuadForm R n) (π : R) (m : R) : ℝ :=
  Filter.limUnder Filter.atTop fun k : ℕ => (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1))

/-- **Local normal form over $R$** (Hanke 2004, (2.3) and Lemma 2.1): block diagonal, with 2-dimensional
blocks on the pairs in $P$ ($c_{ij} = \pi^{\nu_i} b$, $b$ a unit, $\pi^{\nu_i} \mid c_{ii}, c_{jj}$), unpaired
coordinates $c_{ii} = \pi^{\nu_i} u$ with $u$ a unit, and no other cross terms; 2-dimensional blocks only
when $\pi \mid 2$ (see the correction in `LocalDensity.IsJordanForm`). This is the normal form **as printed**;
it exists when $\pi^2 \nmid 2$ (`exists_jordanForm`) and is then equivalent to the general normal form
`IsJordanFormW`, on which the DVR theory runs (`isJordanForm_iff_isJordanFormW`). -/
def IsJordanForm (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) : Prop :=
  (P.Nonempty → π ∣ 2) ∧
  (∀ e ∈ P, e.1 < e.2) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i < j → (i, j) ∉ P → Q.coeff i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, Q.coeff e.1 e.2 = π ^ ν e.1 * b ∧ IsUnit b) ∧
    π ^ ν e.1 ∣ Q.coeff e.1 e.1 ∧ π ^ ν e.1 ∣ Q.coeff e.2 e.2) ∧
  (∀ i, ¬ IsPaired P i → ∃ u, Q.coeff i i = π ^ ν i * u ∧ IsUnit u)

/-! ### The reduction procedure of §3 over $R$ -/

/-- In a DVR, an element not divisible by an irreducible `π` is a unit. -/
theorem dvr_isUnit_of_not_dvd {π u : R} (hπ : Irreducible π) (h : ¬ π ∣ u) : IsUnit u := by
  by_contra hu
  apply h
  have : u ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal u).2 hu
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at this
  exact this

/-- A unit is not divisible by an irreducible element. -/
theorem dvr_not_dvd_of_isUnit {π u : R} (hπ : Irreducible π) (h : IsUnit u) : ¬ π ∣ u :=
  fun hd => hπ.not_isUnit (isUnit_of_dvd_unit hd h)

/-- In a DVR every nonzero element is $\pi^v u$ with $u$ a unit. -/
theorem dvr_eq_pow_mul_unit {π a : R} (hπ : Irreducible π) (ha : a ≠ 0) :
    ∃ v : ℕ, ∃ u, a = π ^ v * u ∧ IsUnit u := by
  obtain ⟨v, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  exact ⟨v, u, by rw [h, mul_comm], u.isUnit⟩

/-- If $\pi^\mu \mid a$ and $\pi^{\mu+1} \nmid a$ then $a = \pi^\mu u$ with $u$ a unit. -/
theorem dvr_exact {π a : R} (hπ : Irreducible π) {μ : ℕ} (h1 : π ^ μ ∣ a) (h2 : ¬ π ^ (μ + 1) ∣ a) :
    ∃ u, a = π ^ μ * u ∧ IsUnit u := by
  obtain ⟨u, rfl⟩ := h1
  exact ⟨u, rfl, dvr_isUnit_of_not_dvd hπ fun ⟨w, hw⟩ => h2 ⟨w, by rw [hw, pow_succ]; ring⟩⟩

/-- $\pi^{v+1} \nmid \pi^v u$ for a unit $u$. -/
theorem dvr_not_pow_succ_dvd {π u : R} (hπ : Irreducible π) (hu : IsUnit u) (v : ℕ) :
    ¬ π ^ (v + 1) ∣ π ^ v * u := by
  rintro ⟨w, hw⟩
  rw [pow_succ, mul_assoc] at hw
  exact dvr_not_dvd_of_isUnit hπ hu ⟨w, mul_left_cancel₀ (pow_ne_zero v hπ.ne_zero) hw⟩

/-- **Counts are invariant under $\mathrm{GL}_n(R)$** (DVR analogue of `repCount_eq_of_unimodular`): if
$Q'(\vec{x}) = Q(U\vec{x})$ with $\det U$ a unit, then $r_{\pi^k}(Q', m) = r_{\pi^k}(Q, m)$. -/
theorem dvr_repCount_eq_of_unimodular (Q Q' : QuadForm R n) (U : Matrix (Fin n) (Fin n) R) (π : R)
    (hU : IsUnit U.det) (hQ' : ∀ x : Fin n → R, Q'.eval x = Q.eval (U *ᵥ x))
    (k : ℕ) (m : R) : repCount Q' π k m = repCount Q π k m := by
  set K := R ⧸ Ideal.span {π ^ k}
  let f : R →+* K := Ideal.Quotient.mk _
  have hcast : ∀ (Q₁ : QuadForm R n) (z : Fin n → R),
      Q₁.evalIn K (fun i => f (z i)) = f (Q₁.eval z) := by
    intro Q₁ z
    simp [QuadForm.evalIn, map_sum, apply_ite f, f]
    rfl
  set U' := U.map f
  have hmv : ∀ z : Fin n → R, U' *ᵥ (fun i => f (z i)) = fun i => f ((U *ᵥ z) i) := by
    intro z
    funext i
    simp [U', Matrix.mulVec, dotProduct, map_sum]
  have key : ∀ x : Fin n → K, Q'.evalIn K x = Q.evalIn K (U' *ᵥ x) := by
    intro x
    obtain ⟨z, rfl⟩ : ∃ z : Fin n → R, (fun i => f (z i)) = x :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
        by funext i; exact (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
    rw [hmv, hcast, hcast, hQ']
  have hdet : IsUnit U'.det := by
    rw [show U'.det = f U.det from (RingHom.map_det f U).symm]
    exact hU.map f
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

/-- **The form $\vec{x}^{\mathsf T} M \vec{x}$** of an arbitrary matrix $M$ over $R$. -/
def dvr_ofMatrix (M : Matrix (Fin n) (Fin n) R) : QuadForm R n where
  coeff := Matrix.of fun i j => if i < j then M i j + M j i else if i = j then M i i else 0
  upper := by
    intro i j h
    simp only [id] at h
    simp [Matrix.of_apply, not_lt.mpr h.le, (ne_of_lt h).symm]

/-- `dvr_ofMatrix M` evaluates to $\vec{x}^{\mathsf T} M \vec{x}$. -/
theorem dvr_eval_ofMatrix (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (dvr_ofMatrix M).eval x = x ⬝ᵥ (M *ᵥ x) := by
  have hL : (dvr_ofMatrix M).eval x = ∑ i, ∑ j, ((if i < j then M i j * x i * x j else 0)
      + (if i < j then M j i * x j * x i else 0) + (if i = j then M i j * x i * x j else 0)) := by
    simp only [QuadForm.evalIn, dvr_ofMatrix, Matrix.of_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
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

/-- The Hessian of `dvr_ofMatrix M` is $M + M^{\mathsf T}$. -/
theorem dvr_hessian_ofMatrix (M : Matrix (Fin n) (Fin n) R) :
    (dvr_ofMatrix M).hessian = M + Mᵀ := by
  ext i j
  simp only [QuadForm.hessian, dvr_ofMatrix, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp
  · simp [h, not_lt.mpr h.le, h.ne']; ring


/-- **A column operation over $R$** (Hanke 2004, Lemma 2.1): columns $k \in T$ are replaced by
$\delta e_k + \sum_{b \in S} w_{bk} e_b$ ($\delta$ a unit, $S \cap T = \emptyset$). The matrix $V$ has unit determinant,
and the entries of $V^{\mathsf T} G V$ are given explicitly. -/
theorem dvr_clear (G : Matrix (Fin n) (Fin n) R) (hG : Gᵀ = G) (T S : Finset (Fin n))
    (hST : ∀ s ∈ S, s ∉ T) (δ : R) (hδ : IsUnit δ) (w : Fin n → Fin n → R)
    (hw : ∀ b k, b ∉ S → w b k = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, IsUnit V.det ∧
      (Vᵀ * G * V)ᵀ = Vᵀ * G * V ∧
      (∀ l m, l ∉ T → m ∉ T → (Vᵀ * G * V) l m = G l m) ∧
      (∀ l k, l ∉ T → k ∈ T → (Vᵀ * G * V) l k = δ * G l k + ∑ b, G l b * w b k) ∧
      (∀ k l, k ∈ T → l ∈ T → (Vᵀ * G * V) k l = δ * δ * G k l + δ * ∑ b, G k b * w b l +
        δ * ∑ a, w a k * G a l + ∑ a, ∑ b, w a k * G a b * w b l) := by
  classical
  set V : Matrix (Fin n) (Fin n) R := Matrix.of fun b k =>
    if k ∈ T then (if b = k then δ else 0) + w b k else (if b = k then 1 else 0) with hV
  have hGV : ∀ l k, (G * V) l k = if k ∈ T then δ * G l k + ∑ b, G l b * w b k else G l k := by
    intro l k
    simp only [Matrix.mul_apply, hV, Matrix.of_apply]
    split_ifs with hk
    · simp [mul_add, Finset.sum_add_distrib, mul_comm]
    · simp
  have hVl : ∀ l m, l ∉ T → (Vᵀ * G * V) l m = (G * V) l m := by
    intro l m hl
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp [hV, Matrix.transpose_apply, hl]
  have hsym : (Vᵀ * G * V)ᵀ = Vᵀ * G * V := by
    simp [Matrix.transpose_mul, hG, Matrix.mul_assoc]
  have hwT : ∀ b k, b ∈ T → w b k = 0 := fun b k hb => hw b k (fun hs => hST b hs hb)
  have hdet : IsUnit V.det := by
    set Dg : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun b => if b ∈ T then δ else 1 with hDg
    set N : Matrix (Fin n) (Fin n) R := Matrix.of fun b k => if k ∈ T then w b k else 0 with hN
    have hfac : V = Dg * (1 + N) := by
      ext b k
      simp only [hV, hDg, hN, Matrix.diagonal_mul, Matrix.of_apply, Matrix.add_apply,
        Matrix.one_apply]
      by_cases hk : k ∈ T <;> by_cases hbk : b = k
      · subst hbk; simp [hk, hwT b b hk]
      · by_cases hb : b ∈ T
        · simp [hk, hbk, hb, hwT b k hb]
        · simp [hk, hbk, hb]
      · subst hbk; simp [hk]
      · simp [hk, hbk]
    have hNN : N * N = 0 := by
      ext b k
      simp only [Matrix.mul_apply, hN, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c ∈ T
      · simp [hc, hwT c k hc]
      · simp [hc]
    have hinv : (1 + N) * (1 - N) = 1 := by
      rw [mul_sub, mul_one, add_mul, one_mul, hNN]; abel
    have h1 : IsUnit (1 + N).det := by
      have := congrArg Matrix.det hinv
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact isUnit_iff_exists_inv.2 ⟨_, this⟩
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul ?_ h1
    rw [IsUnit.prod_univ_iff]
    intro b
    split_ifs
    · exact hδ
    · exact isUnit_one
  refine ⟨V, hdet, hsym, ?_, ?_, ?_⟩
  · intro l m hl hm; rw [hVl l m hl, hGV, if_neg hm]
  · intro l k hl hk; rw [hVl l k hl, hGV, if_pos hk]
  · intro k l hk hl
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hGV, if_pos hl]
    have e : ∀ X : Fin n → R, ∑ a, ((if a = k then δ else 0) + w a k) * X a =
        δ * X k + ∑ a, w a k * X a := by
      intro X; simp [add_mul, Finset.sum_add_distrib]
    simp only [hV, Matrix.transpose_apply, Matrix.of_apply, if_pos hk]
    rw [e]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring_nf


/-- **Clearing step over $R$** (DVR analogue of `clear_step`): if the columns $k \in T$ (the coordinates
outside `D ∪ S`) can be made orthogonal to `S`, the resulting $V$ has unit determinant, $V^{\mathsf T} G V$
agrees with $G$ off $T$, and is orthogonal between $T$ and its complement. -/
theorem dvr_clear_step (G : Matrix (Fin n) (Fin n) R) (hG : Gᵀ = G) (D S T : Finset (Fin n))
    (hT : ∀ l, l ∈ T ↔ l ∉ D ∧ l ∉ S) (hSD : ∀ s ∈ S, s ∉ D)
    (hD : ∀ l ∈ D, ∀ m, m ∉ D → G l m = 0)
    (δ : R) (hδ : IsUnit δ) (w : Fin n → Fin n → R) (hw : ∀ b k, b ∉ S → w b k = 0)
    (hclear : ∀ s ∈ S, ∀ k ∈ T, δ * G s k + ∑ b, G s b * w b k = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, IsUnit V.det ∧
      (∀ l m, l ∉ T → m ∉ T → (Vᵀ * G * V) l m = G l m) ∧
      (∀ l k, l ∉ T → k ∈ T → (Vᵀ * G * V) l k = 0 ∧ (Vᵀ * G * V) k l = 0) := by
  obtain ⟨V, hV, hsym, hA, hB, -⟩ := dvr_clear G hG T S (fun s hs hsT => ((hT s).1 hsT).2 hs)
    δ hδ w hw
  have hB1 : ∀ l k, l ∉ T → k ∈ T → (Vᵀ * G * V) l k = 0 := by
    intro l k hl hk
    rw [hB l k hl hk]
    by_cases hlS : l ∈ S
    · exact hclear l hlS k hk
    · have hlD : l ∈ D := by
        by_contra h
        exact hl ((hT l).2 ⟨h, hlS⟩)
      have hkD : k ∉ D := ((hT k).1 hk).1
      rw [hD l hlD k hkD, mul_zero, zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : b ∈ S
      · rw [hD l hlD b (hSD b hb), zero_mul]
      · rw [hw b k hb, mul_zero]
  refine ⟨V, hV, hA, fun l k hl hk => ⟨hB1 l k hl hk, ?_⟩⟩
  rw [← hsym, Matrix.transpose_apply]
  exact hB1 l k hl hk

/-- **Partial local normal form over $R$** (induction invariant for Lemma 2.1; DVR analogue of `JInv`),
for a symmetric matrix $G$ (a Hessian): the coordinates in `D` are split off as 2-dimensional blocks on the
pairs in `P` (off-diagonal entry $\pi^\nu b$, $b$ a unit, diagonal entries divisible by $2\pi^\nu$; only when
$\pi \mid 2$) and 1-dimensional blocks (diagonal entry $2\pi^\nu u$, $u$ a unit), orthogonal to everything else. -/
def DvrJInv (π : R) (G : Matrix (Fin n) (Fin n) R) (D : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) : Prop :=
  (P.Nonempty → π ∣ 2) ∧
  (∀ e ∈ P, e.1 < e.2 ∧ e.1 ∈ D ∧ e.2 ∈ D) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i ≠ j → (i ∈ D ∨ j ∈ D) → (i, j) ∉ P → (j, i) ∉ P → G i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, G e.1 e.2 = π ^ ν e.1 * b ∧ IsUnit b) ∧
    2 * π ^ ν e.1 ∣ G e.1 e.1 ∧ 2 * π ^ ν e.1 ∣ G e.2 e.2) ∧
  (∀ i ∈ D, ¬ IsPaired P i → ∃ u, G i i = 2 * π ^ ν i * u ∧ IsUnit u)

/-- **Combining a split-off pivot block with the invariant** (DVR analogue of `jinv_step_finish`). -/
theorem dvr_jinv_finish (π : R) (G G' : Matrix (Fin n) (Fin n) R) (D S T : Finset (Fin n))
    (P PS : Finset (Fin n × Fin n)) (ν νS : Fin n → ℕ)
    (hT : ∀ l, l ∈ T ↔ l ∉ D ∧ l ∉ S) (hSD : ∀ s ∈ S, s ∉ D)
    (hA : ∀ l m, l ∉ T → m ∉ T → G' l m = G l m)
    (hB : ∀ l k, l ∉ T → k ∈ T → G' l k = 0 ∧ G' k l = 0)
    (hJ : DvrJInv π G D P ν)
    (hS0 : PS.Nonempty → π ∣ 2)
    (hS1 : ∀ e ∈ PS, e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S)
    (hS2 : ∀ e ∈ PS, ∀ e' ∈ PS, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hS3 : ∀ i j, i ∈ S → j ∈ S → i ≠ j → (i, j) ∉ PS → (j, i) ∉ PS → G i j = 0)
    (hS4 : ∀ e ∈ PS, νS e.1 = νS e.2 ∧ (∃ b, G e.1 e.2 = π ^ νS e.1 * b ∧ IsUnit b) ∧
      2 * π ^ νS e.1 ∣ G e.1 e.1 ∧ 2 * π ^ νS e.1 ∣ G e.2 e.2)
    (hS5 : ∀ i ∈ S, ¬ IsPaired PS i → ∃ u, G i i = 2 * π ^ νS i * u ∧ IsUnit u) :
    DvrJInv π G' (D ∪ S) (P ∪ PS) (fun l => if l ∈ D then ν l else νS l) := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hJ
  have nR : ∀ l, l ∈ D ∨ l ∈ S → l ∉ T := fun l hl hlR => by
    rcases hl with hl | hl
    · exact ((hT l).1 hlR).1 hl
    · exact ((hT l).1 hlR).2 hl
  have hne : ∀ x y, x ∈ D → y ∈ S → x ≠ y := fun x y hx hy h => hSD y hy (h ▸ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hP
    rcases Finset.union_nonempty.1 hP with h | h
    · exact h0 h
    · exact hS0 h
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
    by_cases hiR : i ∈ T
    · have hj : j ∉ T := by
        rcases hor with h | h
        · exact absurd hiR (nR i (Finset.mem_union.1 h))
        · exact nR j (Finset.mem_union.1 h)
      exact (hB j i hj hiR).2
    by_cases hjR : j ∈ T
    · exact (hB i j hiR hjR).1
    rw [hA i j hiR hjR]
    have hi' : i ∈ D ∨ i ∈ S := by
      by_contra h; push Not at h; exact hiR ((hT i).2 h)
    have hj' : j ∈ D ∨ j ∈ S := by
      by_contra h; push Not at h; exact hjR ((hT j).2 h)
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

/-- Rows in `D` are orthogonal to coordinates outside `D`. -/
theorem dvr_jinv_cross {π : R} {G : Matrix (Fin n) (Fin n) R} {D P ν} (hJ : DvrJInv π G D P ν) :
    ∀ l ∈ D, ∀ m, m ∉ D → G l m = 0 := by
  obtain ⟨-, h1, -, h3, -, -⟩ := hJ
  intro l hl m hm
  exact h3 l m (fun h => hm (h ▸ hl)) (Or.inl hl) (fun h => hm (h1 _ h).2.2)
    (fun h => hm (h1 _ h).2.1)

/-- **1-dimensional pivot** (Hanke 2004, Lemma 2.1): if $G_{ii} = 2c_0 \ne 0$ divides every $G_{ik}$
($k \notin D$), the coordinate $i$ is split off as a 1-dimensional block by a unimodular change of variables. -/
theorem dvr_pivot {π : R} (hπ : Irreducible π) (G : Matrix (Fin n) (Fin n) R) (hGs : Gᵀ = G)
    (D : Finset (Fin n)) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : DvrJInv π G D P ν)
    (i : Fin n) (hiD : i ∉ D) (c0 : R) (hc0 : G i i = 2 * c0) (hii : G i i ≠ 0)
    (hdiv : ∀ k, k ∉ D → G i i ∣ G i k) :
    ∃ (V : Matrix (Fin n) (Fin n) R) (ν' : Fin n → ℕ), IsUnit V.det ∧
      DvrJInv π (Vᵀ * G * V) (D ∪ {i}) P ν' := by
  classical
  have hcross := dvr_jinv_cross hJ
  have ht : ∀ k, ∃ t, k ∉ D → G i k = G i i * t := by
    intro k
    by_cases hk : k ∈ D
    · exact ⟨0, fun h => absurd hk h⟩
    · obtain ⟨t, ht⟩ := hdiv k hk; exact ⟨t, fun _ => ht⟩
  choose t ht using ht
  have hc00 : c0 ≠ 0 := by rintro rfl; exact hii (by rw [hc0, mul_zero])
  obtain ⟨v, u, hu, hu1⟩ := dvr_eq_pow_mul_unit hπ hc00
  set S : Finset (Fin n) := {i} with hS
  set T : Finset (Fin n) := Finset.univ.filter fun l => l ∉ D ∧ l ∉ S with hTdef
  have hT : ∀ l, l ∈ T ↔ l ∉ D ∧ l ∉ S := by intro l; simp [hTdef]
  have hSD : ∀ s ∈ S, s ∉ D := by intro s hs; rw [Finset.mem_singleton.1 hs]; exact hiD
  obtain ⟨V, hV, hA, hB⟩ := dvr_clear_step G hGs D S T hT hSD hcross 1 isUnit_one
    (fun b k => if b = i then -t k else 0) (by intro b k hb; simp [hS] at hb; simp [hb])
    (by
      intro s hs k hk
      rw [Finset.mem_singleton.1 hs]
      have hk' := ((hT k).1 hk).1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [ht k hk']; ring)
  refine ⟨V, fun l => if l ∈ D then ν l else (fun _ => v) l, hV, ?_⟩
  have := dvr_jinv_finish π G _ D S T P ∅ ν (fun _ => v) hT hSD hA hB hJ
    (by simp) (by simp) (by simp) ?_ (by simp) ?_
  · rwa [Finset.union_empty] at this
  · intro a b ha hb hab
    rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb] at hab
    exact absurd rfl hab
  · intro a ha _
    rw [Finset.mem_singleton.1 ha]
    exact ⟨u, by rw [hc0, hu]; ring, hu1⟩


/-- **One step of Lemma 2.1 over $R$** (Hanke 2004, p. 355; Conway–Sloane pp. 369–370), assuming
$\pi^2 \nmid 2$: take the least $\pi$-adic valuation $\mu$ of the Hessian entries among the remaining
coordinates. If attained on the diagonal, split off a 1-dimensional block. Otherwise, at an off-diagonal
entry $\pi^\mu\beta$: if $\pi \mid 2$ split off the 2-dimensional block ($\delta = \pi^2 a'c' - \beta^2$ a unit); if
$\pi \nmid 2$, first replace $x_i$ by $x_i + x_j$ to move the valuation to the diagonal. -/
theorem dvr_step {π : R} (hπ : Irreducible π) (h2 : ¬ π ^ 2 ∣ 2) (c : Matrix (Fin n) (Fin n) R)
    (D : Finset (Fin n)) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hdet : (c + cᵀ).det ≠ 0)
    (hJ : DvrJInv π (c + cᵀ) D P ν) (hD : D ≠ Finset.univ) :
    ∃ (V : Matrix (Fin n) (Fin n) R) (D' : Finset (Fin n)) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), IsUnit V.det ∧ D ⊂ D' ∧ DvrJInv π (Vᵀ * (c + cᵀ) * V) D' P' ν' := by
  classical
  set G := c + cᵀ with hGdef
  have hGs : Gᵀ = G := by simp [hGdef, add_comm]
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    rw [← Matrix.transpose_apply G i j, hGs]
  have hdiag2 : ∀ i, G i i = 2 * c i i := fun i => by simp [hGdef]; ring
  have hcross := dvr_jinv_cross hJ
  have hJ0 := hJ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hnz : ∃ k l, k ∉ D ∧ l ∉ D ∧ G k l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ : ∃ k, k ∉ D := by
      by_contra h
      push Not at h
      exact hD (Finset.eq_univ_iff_forall.2 h)
    apply hdet
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro l
    by_cases hl : l ∈ D
    · exact hcross l hl k hk
    · exact hcon l k hl hk
  obtain ⟨μ, hμdiv, hμnd⟩ : ∃ μ : ℕ, (∀ k l, k ∉ D → l ∉ D → π ^ μ ∣ G k l) ∧
      ∃ k l, k ∉ D ∧ l ∉ D ∧ ¬ π ^ (μ + 1) ∣ G k l := by
    have hex : ∃ μ : ℕ, ∃ k l, k ∉ D ∧ l ∉ D ∧ ¬ π ^ (μ + 1) ∣ G k l := by
      obtain ⟨k, l, hk, hl, hne⟩ := hnz
      obtain ⟨v, u, hu, hu1⟩ := dvr_eq_pow_mul_unit hπ hne
      exact ⟨v, k, l, hk, hl, by rw [hu]; exact dvr_not_pow_succ_dvd hπ hu1 v⟩
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    intro k l hk hl
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push Not at this
      have h := this k l hk hl
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [e] at h
  have hssub : ∀ i, i ∉ D → D ⊂ D ∪ {i} := fun i hi => by
    rw [Finset.ssubset_iff]
    exact ⟨i, hi, by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h]⟩
  by_cases hdiag : ∃ i, i ∉ D ∧ ¬ π ^ (μ + 1) ∣ G i i
  · -- 1-dimensional block
    obtain ⟨i, hiD, hi⟩ := hdiag
    obtain ⟨u, hu, hu1⟩ := dvr_exact hπ (hμdiv i i hiD hiD) hi
    obtain ⟨u', hu'⟩ := hu1.exists_right_inv
    obtain ⟨V, ν', hV, hJ'⟩ := dvr_pivot hπ G hGs D P ν hJ0 i hiD (c i i) (hdiag2 i)
      (by rw [hu]; exact mul_ne_zero (pow_ne_zero _ hπ0) hu1.ne_zero)
      (fun k hk => by
        obtain ⟨t, ht⟩ := hμdiv i k hiD hk
        exact ⟨u' * t, by rw [ht, hu]; linear_combination (-(π ^ μ * t)) * hu'⟩)
    exact ⟨V, D ∪ {i}, P, ν', hV, hssub i hiD, hJ'⟩
  push Not at hdiag
  obtain ⟨k, l, hk, hl, hkl⟩ := hμnd
  have hne : k ≠ l := by rintro rfl; exact hkl (hdiag k hk)
  obtain ⟨i, j, hi, hj, hij, hb⟩ : ∃ i j, i ∉ D ∧ j ∉ D ∧ i < j ∧ ¬ π ^ (μ + 1) ∣ G i j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨k, l, hk, hl, h, hkl⟩
    · exact ⟨l, k, hl, hk, h, by rwa [hsym]⟩
  obtain ⟨a', ha⟩ := hdiag i hi
  obtain ⟨c', hc⟩ := hdiag j hj
  obtain ⟨β, hβ, hβ1⟩ := dvr_exact hπ (hμdiv i j hi hj) hb
  have hβπ : ¬ π ∣ β := dvr_not_dvd_of_isUnit hπ hβ1
  have hji : G j i = π ^ μ * β := by rw [hsym]; exact hβ
  have hij' : i ≠ j := hij.ne
  by_cases hπ2 : π ∣ 2
  · -- 2-dimensional block (π ∣ 2, so v(2) = 1)
    obtain ⟨ε, hε⟩ := hπ2
    have hε1 : IsUnit ε := dvr_isUnit_of_not_dvd hπ fun ⟨w, hw⟩ => h2 ⟨w, by rw [hε, hw]; ring⟩
    obtain ⟨ε', hε'⟩ := hε1.exists_right_inv
    have hδ : IsUnit (π ^ 2 * a' * c' - β ^ 2) := by
      refine dvr_isUnit_of_not_dvd hπ fun h => hβπ ?_
      have h' : π ∣ π ^ 2 * a' * c' := ⟨π * a' * c', by ring⟩
      have : π ∣ β ^ 2 := by
        have := dvd_sub h' h
        rwa [show π ^ 2 * a' * c' - (π ^ 2 * a' * c' - β ^ 2) = β ^ 2 by ring] at this
      exact hπ.prime.dvd_of_dvd_pow this
    have hx : ∀ k, ∃ t, k ∉ D → G i k = π ^ μ * t := by
      intro k
      by_cases hk : k ∈ D
      · exact ⟨0, fun h => absurd hk h⟩
      · obtain ⟨t, ht⟩ := hμdiv i k hi hk; exact ⟨t, fun _ => ht⟩
    have hy : ∀ k, ∃ t, k ∉ D → G j k = π ^ μ * t := by
      intro k
      by_cases hk : k ∈ D
      · exact ⟨0, fun h => absurd hk h⟩
      · obtain ⟨t, ht⟩ := hμdiv j k hj hk; exact ⟨t, fun _ => ht⟩
    choose x hx using hx
    choose y hy using hy
    set S : Finset (Fin n) := {i, j} with hS
    set T : Finset (Fin n) := Finset.univ.filter fun l => l ∉ D ∧ l ∉ S with hTdef
    have hT : ∀ l, l ∈ T ↔ l ∉ D ∧ l ∉ S := by intro l; simp [hTdef]
    have hSD : ∀ s ∈ S, s ∉ D := by
      intro s hs
      rcases Finset.mem_insert.1 hs with h | h
      · rw [h]; exact hi
      · rw [Finset.mem_singleton.1 h]; exact hj
    obtain ⟨V, hV, hA, hB⟩ := dvr_clear_step G hGs D S T hT hSD hcross _ hδ
      (fun b k => (if b = i then β * y k - π * c' * x k else 0) +
        (if b = j then β * x k - π * a' * y k else 0))
      (by
        intro b k hb
        have hbi : b ≠ i := fun h => hb (by simp [hS, h])
        have hbj : b ≠ j := fun h => hb (by simp [hS, h])
        simp [hbi, hbj])
      (by
        intro s hs k hk
        have hk' := ((hT k).1 hk).1
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rcases Finset.mem_insert.1 hs with h | h
        · rw [h, hx k hk', ha, hβ]
          ring
        · rw [Finset.mem_singleton.1 h, hy k hk', hji, hc]
          ring)
    have h2dvd : ∀ z, 2 * π ^ μ ∣ π ^ (μ + 1) * z := fun z =>
      ⟨ε' * z, by rw [hε]; linear_combination (-(π ^ (μ + 1) * z)) * hε'⟩
    refine ⟨V, D ∪ S, P ∪ {(i, j)}, fun l => if l ∈ D then ν l else (fun _ => μ) l, hV, ?_, ?_⟩
    · rw [Finset.ssubset_iff]
      exact ⟨i, hi, by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h, hS]⟩
    · refine dvr_jinv_finish π G _ D S T P {(i, j)} ν (fun _ => μ) hT hSD hA hB hJ0
        (fun _ => ⟨ε, hε⟩) ?_ ?_ ?_ ?_ ?_
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
        exact ⟨rfl, ⟨β, hβ, hβ1⟩, by rw [ha]; exact h2dvd a', by rw [hc]; exact h2dvd c'⟩
      · intro a ha hnp
        exfalso
        apply hnp
        rcases Finset.mem_insert.1 ha with h | h
        · exact ⟨(i, j), by simp, Or.inl h.symm⟩
        · exact ⟨(i, j), by simp, Or.inr (Finset.mem_singleton.1 h).symm⟩
  · -- π ∤ 2: replace x_i by x_i + x_j, then pivot at i
    obtain ⟨F, hF, hFs, hFA, hFB, hFC⟩ := dvr_clear G hGs {i} {j} (by simp [Ne.symm hij']) 1
      isUnit_one (fun b _ => if b = j then 1 else 0) (by intro b k hb; simp at hb; simp [hb])
    set G' := Fᵀ * G * F with hG'def
    have hG'c : G' = (Fᵀ * c * F) + (Fᵀ * c * F)ᵀ := by
      simp [hG'def, hGdef, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    have hG's : G'ᵀ = G' := hFs
    have hG'sym : ∀ a b, G' b a = G' a b := fun a b => by
      rw [← Matrix.transpose_apply G' a b, hG's]
    have hFB' : ∀ l, l ≠ i → G' l i = G l i + G l j := by
      intro l hl
      rw [hFB l i (by simpa using hl) (by simp)]
      simp
    -- the invariant still holds on `D`
    set T' : Finset (Fin n) := Finset.univ.filter fun l => l ∉ D ∧ l ∉ (∅ : Finset (Fin n))
      with hT'def
    have hT' : ∀ l, l ∈ T' ↔ l ∉ D ∧ l ∉ (∅ : Finset (Fin n)) := by intro l; simp [hT'def]
    have hJ' : DvrJInv π G' D P (fun l => if l ∈ D then ν l else (fun _ => 0) l) := by
      have hDi : ∀ l, l ∈ D → l ≠ i := fun l hl h => hi (h ▸ hl)
      have := dvr_jinv_finish π G G' D ∅ T' P ∅ ν (fun _ => 0) hT' (by simp)
        (by
          intro l m hl hm
          have hl' : l ∈ D := by by_contra h; exact hl ((hT' l).2 ⟨h, by simp⟩)
          have hm' : m ∈ D := by by_contra h; exact hm ((hT' m).2 ⟨h, by simp⟩)
          exact hFA l m (by simpa using hDi l hl') (by simpa using hDi m hm'))
        (by
          intro l k hl hk
          have hl' : l ∈ D := by by_contra h; exact hl ((hT' l).2 ⟨h, by simp⟩)
          have hk' : k ∉ D := ((hT' k).1 hk).1
          have h1 : G' l k = 0 := by
            by_cases hki : k = i
            · rw [hki, hFB' l (hDi l hl'), hcross l hl' i hi, hcross l hl' j hj, add_zero]
            · rw [hFA l k (by simpa using hDi l hl') (by simpa using hki), hcross l hl' k hk']
          exact ⟨h1, by rw [hG'sym]; exact h1⟩)
        hJ0 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      rwa [Finset.union_empty, Finset.union_empty] at this
    -- the new diagonal entry has valuation μ
    have hG'ii : G' i i = π ^ μ * (π * a' + 2 * β + π * c') := by
      rw [hFC i i (by simp) (by simp)]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul, one_mul]
      rw [ha, hc, hβ, hji]
      ring
    have hu0 : IsUnit (π * a' + 2 * β + π * c') := by
      refine dvr_isUnit_of_not_dvd hπ fun h => ?_
      have h' : π ∣ 2 * β := by
        have := dvd_sub (dvd_sub h (dvd_mul_right π a')) (dvd_mul_right π c')
        rwa [show π * a' + 2 * β + π * c' - π * a' - π * c' = 2 * β by ring] at this
      rcases hπ.prime.dvd_or_dvd h' with h'' | h''
      · exact hπ2 h''
      · exact hβπ h''
    obtain ⟨u', hu'⟩ := hu0.exists_right_inv
    obtain ⟨W, ν', hW, hJW⟩ := dvr_pivot hπ G' hG's D P _ hJ' i hi ((Fᵀ * c * F) i i)
      (by rw [hG'c, Matrix.add_apply, Matrix.transpose_apply]; ring)
      (by rw [hG'ii]; exact mul_ne_zero (pow_ne_zero _ hπ0) hu0.ne_zero)
      (fun k hk => by
        by_cases hki : k = i
        · rw [hki]
        · obtain ⟨t1, ht1⟩ := hμdiv k i hk hi
          obtain ⟨t2, ht2⟩ := hμdiv k j hk hj
          refine ⟨u' * (t1 + t2), ?_⟩
          rw [hG'sym, hFB' k hki, ht1, ht2, hG'ii]
          linear_combination (-(π ^ μ * (t1 + t2))) * hu')
    refine ⟨F * W, D ∪ {i}, P, ν', ?_, hssub i hi, ?_⟩
    · rw [Matrix.det_mul]; exact hF.mul hW
    · have : (F * W)ᵀ * G * (F * W) = Wᵀ * G' * W := by
        simp [hG'def, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this]; exact hJW


/-- **Lemma 2.1 over $R$, matrix form** (induction on the number of coordinates not yet split off). -/
theorem dvr_jinv_complete_aux {π : R} (hπ : Irreducible π) (h2 : ¬ π ^ 2 ∣ 2) :
    ∀ (k : ℕ) (c : Matrix (Fin n) (Fin n) R) (D : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ), Dᶜ.card = k → (c + cᵀ).det ≠ 0 →
    DvrJInv π (c + cᵀ) D P ν → ∃ (V : Matrix (Fin n) (Fin n) R) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), IsUnit V.det ∧ DvrJInv π (Vᵀ * (c + cᵀ) * V) Finset.univ P' ν' := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c D P ν hk hdet hJ
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨1, P, ν, by simp, by simpa using hJ⟩
  obtain ⟨V, D', P', ν', hV, hDD, hJ'⟩ := dvr_step hπ h2 c D P ν hdet hJ hD
  have hc' : Vᵀ * (c + cᵀ) * V = (Vᵀ * c * V) + (Vᵀ * c * V)ᵀ := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hV0 : V.det ≠ 0 := hV.ne_zero
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
  · rw [Matrix.det_mul]; exact hV.mul hW
  · have : (V * W)ᵀ * (c + cᵀ) * (V * W) = Wᵀ * (Vᵀ * c * V + (Vᵀ * c * V)ᵀ) * W := by
      rw [← hc']; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this]; exact hJ''

/-- The invariant on all coordinates for the Hessian of `Q` is the local normal form over $R$
(needs $2 \ne 0$). -/
theorem dvr_isJordanForm_of_jinv {π : R} (h20 : (2 : R) ≠ 0) (Q : QuadForm R n)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : DvrJInv π Q.hessian Finset.univ P ν) :
    IsJordanForm Q π P ν := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hJ
  have hoff : ∀ i j, i < j → Q.hessian i j = Q.coeff i j := by
    intro i j hij
    simp [QuadForm.hessian, Q.upper (show id i < id j from hij)]
  have hdi : ∀ i, Q.hessian i i = 2 * Q.coeff i i := by
    intro i; simp [QuadForm.hessian]; ring
  refine ⟨h0, fun e he => (h1 e he).1, h2, ?_, ?_, ?_⟩
  · intro i j hij hP
    rw [← hoff i j hij]
    exact h3 i j hij.ne (Or.inl (Finset.mem_univ _)) hP
      (fun h => absurd (h1 _ h).1 (not_lt.2 hij.le))
  · intro e he
    obtain ⟨a, ⟨b, hb, hb2⟩, c, d⟩ := h4 e he
    have hc : ∀ i, 2 * π ^ ν e.1 ∣ Q.hessian i i → π ^ ν e.1 ∣ Q.coeff i i := by
      intro i h
      rw [hdi] at h
      exact (mul_dvd_mul_iff_left h20).1 h
    refine ⟨a, ⟨b, ?_, hb2⟩, hc _ c, hc _ d⟩
    rw [← hoff _ _ (h1 e he).1]; exact hb
  · intro i hi
    obtain ⟨u, hu, hu2⟩ := h5 i (Finset.mem_univ _) hi
    refine ⟨u, ?_, hu2⟩
    rw [hdi, mul_assoc] at hu
    exact mul_left_cancel₀ h20 hu

/-- **Existence of a local normal form** (Hanke 2004, Lemma 2.1, p. 355): a nondegenerate $Q$ over $R$
is $\mathrm{GL}_n(R)$-equivalent to a form in local normal form (2-dimensional blocks needed only when
$\pi \mid 2$), and equivalent forms have the same counts, **provided $\pi^2 \nmid 2$** (non-dyadic, or dyadic
with $v_\pi(2) = 1$; this covers every prime of $\mathbb{Q}$).

*Erratum candidate:* at ramified dyadic primes the paper's normal form need
not exist: $Q = x^2 + \pi xy + y^2$ over $\mathbb{Z}_2[\sqrt2]$, $\pi = \sqrt2$, is a counterexample. The corrected statement valid at every prime is `exists_jordanFormW`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem exists_jordanForm (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ^ 2 ∣ 2) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q' π P ν ∧ (¬ π ∣ 2 → P = ∅) ∧ ∀ k m, repCount Q π k m = repCount Q' π k m := by
  classical
  have h20 : (2 : R) ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hJ0 : DvrJInv π (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P, ν, hV, hJ⟩ := dvr_jinv_complete_aux hπ h2 _ Q.coeff ∅ ∅ (fun _ => 0) rfl hQ hJ0
  set Q' := dvr_ofMatrix (Vᵀ * Q.coeff * V) with hQ'
  have hH : Q'.hessian = Vᵀ * (Q.coeff + Q.coeffᵀ) * V := by
    rw [hQ', dvr_hessian_ofMatrix]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have heval : ∀ x, Q'.eval x = Q.eval (V *ᵥ x) := by
    intro x
    rw [hQ', dvr_eval_ofMatrix]
    show _ = Q.evalIn R (V *ᵥ x)
    rw [QuadForm.evalIn_eq_dotProduct]
    simp only [Algebra.algebraMap_self, Matrix.map_id]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    rfl
  refine ⟨Q', P, ν, dvr_isJordanForm_of_jinv h20 Q' P ν (hH ▸ hJ), fun h => ?_,
    fun k m => (dvr_repCount_eq_of_unimodular Q Q' V π hV heval k m).symm⟩
  by_contra hP
  exact h (hJ.1 (Finset.nonempty_iff_ne_empty.2 hP))

end QuadFormsKB.LocalDensity.DVR
