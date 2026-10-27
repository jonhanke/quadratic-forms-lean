/-
# Local densities over a DVR: the normal form at every prime (Lemma 2.1, corrected)

**Layer:** DVR. **Defines** `DVR.IsJordanFormW Q π P w`: block diagonal, each block $\pi^{w}Q_j$ with $w$ the
**exact** norm exponent (Hanke's $\nu_j$ in (2.3)), and each 2-dimensional block also carrying its scale exponent
$\mu = v(c_{ij})$, $w \le \mu \le w + v(2)$ (`PairBlockW`). **Proves** Hanke 2004, Lemma 2.1 (p. 355) corrected:
the normal form exists whenever $2 \ne 0$ in $R$, including ramified dyadic primes (`exists_jordanFormW`, via the
Jordan splitting `IsJordanFormGen`, `exists_jordanFormGen`), and that for $\pi^2 \nmid 2$ it is exactly the
printed one (`isJordanForm_iff_isJordanFormW`: same blocks, $\nu = w$, $\mu = w$). Also `IsJordanFormW.coeff_block`
and `PairBlockW.mul`/`cancel` used by the reductions. **Depends on** `DVR.lean`.
-/
import QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **General local normal form over $R$ (Jordan splitting), valid at every prime.** Block diagonal, with
2-dimensional blocks on the pairs in $P$ and 1-dimensional blocks on the unpaired coordinates:
- 2-dimensional block on $(i, j) \in P$, $i < j$: $\nu_i = \nu_j$, $c_{ij} = \pi^{\nu_i} b$ with $b$ a unit, and
  $\pi^{\nu_i + 1} \mid 2 c_{ii}$, $\pi^{\nu_i + 1} \mid 2 c_{jj}$ (the Hessian block
  $\begin{pmatrix} 2c_{ii} & c_{ij} \\ c_{ij} & 2c_{jj} \end{pmatrix}$ is $\pi^{\nu_i}$ times a unimodular matrix whose
  diagonal lies in $\pi$);
- unpaired $i$: $c_{ii} = \pi^{\nu_i} u$ with $u$ a unit;
- no other cross terms; and 2-dimensional blocks only when $\pi \mid 2$.
When $v_\pi(2) \le 1$ this is equivalent in strength to `IsJordanForm` up to the diagonal condition (which
there reads $\pi^{\nu} \mid c_{ii}$); at ramified dyadic primes it is strictly weaker, as it must be. -/
def IsJordanFormGen (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) : Prop :=
  (P.Nonempty → π ∣ 2) ∧
  (∀ e ∈ P, e.1 < e.2) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i < j → (i, j) ∉ P → Q.coeff i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, Q.coeff e.1 e.2 = π ^ ν e.1 * b ∧ IsUnit b) ∧
    π ^ (ν e.1 + 1) ∣ 2 * Q.coeff e.1 e.1 ∧ π ^ (ν e.1 + 1) ∣ 2 * Q.coeff e.2 e.2) ∧
  (∀ i, ¬ IsPaired P i → ∃ u, Q.coeff i i = π ^ ν i * u ∧ IsUnit u)

/-- **The old normal form is a special case:** `IsJordanForm → IsJordanFormGen` (2-dimensional blocks occur
only when $\pi \mid 2$, so $\pi^\nu \mid c_{ii}$ gives $\pi^{\nu+1} \mid 2c_{ii}$). -/
theorem IsJordanForm.toGen {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ}
    (h : IsJordanForm Q π P ν) : IsJordanFormGen Q π P ν := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, h1, h2, h3, fun e he => ?_, h5⟩
  obtain ⟨a, b, c, d⟩ := h4 e he
  have h2' : π ∣ 2 := h0 ⟨e, he⟩
  refine ⟨a, b, ?_, ?_⟩
  · rw [pow_succ, mul_comm 2]; exact mul_dvd_mul c h2'
  · rw [pow_succ, mul_comm 2]; exact mul_dvd_mul d h2'

/-- **Partial general local normal form over $R$** (induction invariant for `exists_jordanFormGen`; the
general-prime version of `DvrJInv`), for a symmetric matrix $G$ (a Hessian): the coordinates in `D` are split
off as 2-dimensional blocks on the pairs in `P` (off-diagonal entry $\pi^\nu b$, $b$ a unit, diagonal entries
divisible by $\pi^{\nu+1}$; only when $\pi \mid 2$) and 1-dimensional blocks (diagonal entry $2\pi^\nu u$, $u$ a unit), orthogonal to everything else. -/
def DvrJInvGen (π : R) (G : Matrix (Fin n) (Fin n) R) (D : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) : Prop :=
  (P.Nonempty → π ∣ 2) ∧
  (∀ e ∈ P, e.1 < e.2 ∧ e.1 ∈ D ∧ e.2 ∈ D) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i ≠ j → (i ∈ D ∨ j ∈ D) → (i, j) ∉ P → (j, i) ∉ P → G i j = 0) ∧
  (∀ e ∈ P, ν e.1 = ν e.2 ∧ (∃ b, G e.1 e.2 = π ^ ν e.1 * b ∧ IsUnit b) ∧
    π ^ (ν e.1 + 1) ∣ G e.1 e.1 ∧ π ^ (ν e.1 + 1) ∣ G e.2 e.2) ∧
  (∀ i ∈ D, ¬ IsPaired P i → ∃ u, G i i = 2 * π ^ ν i * u ∧ IsUnit u)

/-- **Combining a split-off pivot block with the invariant** (DVR analogue of `jinv_step_finish`). -/
theorem dvr_jinvGen_finish (π : R) (G G' : Matrix (Fin n) (Fin n) R) (D S T : Finset (Fin n))
    (P PS : Finset (Fin n × Fin n)) (ν νS : Fin n → ℕ)
    (hT : ∀ l, l ∈ T ↔ l ∉ D ∧ l ∉ S) (hSD : ∀ s ∈ S, s ∉ D)
    (hA : ∀ l m, l ∉ T → m ∉ T → G' l m = G l m)
    (hB : ∀ l k, l ∉ T → k ∈ T → G' l k = 0 ∧ G' k l = 0)
    (hJ : DvrJInvGen π G D P ν)
    (hS0 : PS.Nonempty → π ∣ 2)
    (hS1 : ∀ e ∈ PS, e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S)
    (hS2 : ∀ e ∈ PS, ∀ e' ∈ PS, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)
    (hS3 : ∀ i j, i ∈ S → j ∈ S → i ≠ j → (i, j) ∉ PS → (j, i) ∉ PS → G i j = 0)
    (hS4 : ∀ e ∈ PS, νS e.1 = νS e.2 ∧ (∃ b, G e.1 e.2 = π ^ νS e.1 * b ∧ IsUnit b) ∧
      π ^ (νS e.1 + 1) ∣ G e.1 e.1 ∧ π ^ (νS e.1 + 1) ∣ G e.2 e.2)
    (hS5 : ∀ i ∈ S, ¬ IsPaired PS i → ∃ u, G i i = 2 * π ^ νS i * u ∧ IsUnit u) :
    DvrJInvGen π G' (D ∪ S) (P ∪ PS) (fun l => if l ∈ D then ν l else νS l) := by
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
theorem dvr_jinvGen_cross {π : R} {G : Matrix (Fin n) (Fin n) R} {D P ν} (hJ : DvrJInvGen π G D P ν) :
    ∀ l ∈ D, ∀ m, m ∉ D → G l m = 0 := by
  obtain ⟨-, h1, -, h3, -, -⟩ := hJ
  intro l hl m hm
  exact h3 l m (fun h => hm (h ▸ hl)) (Or.inl hl) (fun h => hm (h1 _ h).2.2)
    (fun h => hm (h1 _ h).2.1)

/-- **1-dimensional pivot** (Hanke 2004, Lemma 2.1): if $G_{ii} = 2c_0 \ne 0$ divides every $G_{ik}$
($k \notin D$), the coordinate $i$ is split off as a 1-dimensional block by a unimodular change of variables. -/
theorem dvr_pivotGen {π : R} (hπ : Irreducible π) (G : Matrix (Fin n) (Fin n) R) (hGs : Gᵀ = G)
    (D : Finset (Fin n)) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : DvrJInvGen π G D P ν)
    (i : Fin n) (hiD : i ∉ D) (c0 : R) (hc0 : G i i = 2 * c0) (hii : G i i ≠ 0)
    (hdiv : ∀ k, k ∉ D → G i i ∣ G i k) :
    ∃ (V : Matrix (Fin n) (Fin n) R) (ν' : Fin n → ℕ), IsUnit V.det ∧
      DvrJInvGen π (Vᵀ * G * V) (D ∪ {i}) P ν' := by
  classical
  have hcross := dvr_jinvGen_cross hJ
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
  have := dvr_jinvGen_finish π G _ D S T P ∅ ν (fun _ => v) hT hSD hA hB hJ
    (by simp) (by simp) (by simp) ?_ (by simp) ?_
  · rwa [Finset.union_empty] at this
  · intro a b ha hb hab
    rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb] at hab
    exact absurd rfl hab
  · intro a ha _
    rw [Finset.mem_singleton.1 ha]
    exact ⟨u, by rw [hc0, hu]; ring, hu1⟩


/-- **One step of the general Jordan splitting over $R$** (Hanke 2004, p. 355; Conway–Sloane pp. 369–370;
O'Meara §91), valid at every prime: take the least $\pi$-adic valuation $\mu$ of the Hessian entries among the remaining
coordinates. If attained on the diagonal, split off a 1-dimensional block. Otherwise, at an off-diagonal
entry $\pi^\mu\beta$: if $\pi \mid 2$ split off the 2-dimensional block ($G_{ii} = \pi^{\mu+1}a'$, $G_{jj} = \pi^{\mu+1}c'$ by
minimality, so $\delta = \pi^2 a'c' - \beta^2$ is a unit; no condition on $v_\pi(2)$ is needed); if
$\pi \nmid 2$, first replace $x_i$ by $x_i + x_j$ to move the valuation to the diagonal. -/
theorem dvr_stepGen {π : R} (hπ : Irreducible π) (c : Matrix (Fin n) (Fin n) R)
    (D : Finset (Fin n)) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hdet : (c + cᵀ).det ≠ 0)
    (hJ : DvrJInvGen π (c + cᵀ) D P ν) (hD : D ≠ Finset.univ) :
    ∃ (V : Matrix (Fin n) (Fin n) R) (D' : Finset (Fin n)) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), IsUnit V.det ∧ D ⊂ D' ∧ DvrJInvGen π (Vᵀ * (c + cᵀ) * V) D' P' ν' := by
  classical
  set G := c + cᵀ with hGdef
  have hGs : Gᵀ = G := by simp [hGdef, add_comm]
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    rw [← Matrix.transpose_apply G i j, hGs]
  have hdiag2 : ∀ i, G i i = 2 * c i i := fun i => by simp [hGdef]; ring
  have hcross := dvr_jinvGen_cross hJ
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
    obtain ⟨V, ν', hV, hJ'⟩ := dvr_pivotGen hπ G hGs D P ν hJ0 i hiD (c i i) (hdiag2 i)
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
    refine ⟨V, D ∪ S, P ∪ {(i, j)}, fun l => if l ∈ D then ν l else (fun _ => μ) l, hV, ?_, ?_⟩
    · rw [Finset.ssubset_iff]
      exact ⟨i, hi, by intro x hx; simp at hx ⊢; rcases hx with h | h <;> simp [h, hS]⟩
    · refine dvr_jinvGen_finish π G _ D S T P {(i, j)} ν (fun _ => μ) hT hSD hA hB hJ0
        (fun _ => hπ2) ?_ ?_ ?_ ?_ ?_
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
        exact ⟨rfl, ⟨β, hβ, hβ1⟩, ⟨a', ha⟩, ⟨c', hc⟩⟩
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
    have hJ' : DvrJInvGen π G' D P (fun l => if l ∈ D then ν l else (fun _ => 0) l) := by
      have hDi : ∀ l, l ∈ D → l ≠ i := fun l hl h => hi (h ▸ hl)
      have := dvr_jinvGen_finish π G G' D ∅ T' P ∅ ν (fun _ => 0) hT' (by simp)
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
    obtain ⟨W, ν', hW, hJW⟩ := dvr_pivotGen hπ G' hG's D P _ hJ' i hi ((Fᵀ * c * F) i i)
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
theorem dvr_jinvGen_complete_aux {π : R} (hπ : Irreducible π) :
    ∀ (k : ℕ) (c : Matrix (Fin n) (Fin n) R) (D : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ), Dᶜ.card = k → (c + cᵀ).det ≠ 0 →
    DvrJInvGen π (c + cᵀ) D P ν → ∃ (V : Matrix (Fin n) (Fin n) R) (P' : Finset (Fin n × Fin n))
      (ν' : Fin n → ℕ), IsUnit V.det ∧ DvrJInvGen π (Vᵀ * (c + cᵀ) * V) Finset.univ P' ν' := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c D P ν hk hdet hJ
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨1, P, ν, by simp, by simpa using hJ⟩
  obtain ⟨V, D', P', ν', hV, hDD, hJ'⟩ := dvr_stepGen hπ c D P ν hdet hJ hD
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

/-- The invariant on all coordinates for the Hessian of `Q` is the general local normal form over $R$
(needs $2 \ne 0$). -/
theorem dvr_isJordanFormGen_of_jinvGen {π : R} (h20 : (2 : R) ≠ 0) (Q : QuadForm R n)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : DvrJInvGen π Q.hessian Finset.univ P ν) :
    IsJordanFormGen Q π P ν := by
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
    have hc : ∀ i, π ^ (ν e.1 + 1) ∣ Q.hessian i i → π ^ (ν e.1 + 1) ∣ 2 * Q.coeff i i := by
      intro i h
      rwa [hdi] at h
    refine ⟨a, ⟨b, ?_, hb2⟩, hc _ c, hc _ d⟩
    rw [← hoff _ _ (h1 e he).1]; exact hb
  · intro i hi
    obtain ⟨u, hu, hu2⟩ := h5 i (Finset.mem_univ _) hi
    refine ⟨u, ?_, hu2⟩
    rw [hdi, mul_assoc] at hu
    exact mul_left_cancel₀ h20 hu

/-- **Existence of a general local normal form (Jordan splitting) at every prime** (corrects Hanke 2004,
Lemma 2.1, p. 355; cf. O'Meara §91–93, Conway–Sloane Ch. 15 §7): a nondegenerate $Q$ over a DVR $R$ with
$2 \ne 0$ is $\mathrm{GL}_n(R)$-equivalent to a form satisfying `IsJordanFormGen` (2-dimensional blocks only when
$\pi \mid 2$), and equivalent forms have the same counts $r_{\pi^k}(m)$ for all $k, m$. No hypothesis on
$v_\pi(2)$: at ramified dyadic primes the 2-dimensional blocks may have diagonal coefficients $c_{ii}$ with
$v(c_{ii}) < \nu$ (e.g. $x^2 + \pi xy + y^2$ over $\mathbb{Z}_2[\sqrt2]$, $\nu = 1$), as long as
$v(2c_{ii}) > \nu$. -/
theorem exists_jordanFormGen (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanFormGen Q' π P ν ∧ (¬ π ∣ 2 → P = ∅) ∧ ∀ k m, repCount Q π k m = repCount Q' π k m := by
  classical
  have hJ0 : DvrJInvGen π (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P, ν, hV, hJ⟩ := dvr_jinvGen_complete_aux hπ _ Q.coeff ∅ ∅ (fun _ => 0) rfl hQ hJ0
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
  refine ⟨Q', P, ν, dvr_isJordanFormGen_of_jinvGen h20 Q' P ν (hH ▸ hJ), fun h => ?_,
    fun k m => (dvr_repCount_eq_of_unimodular Q Q' V π hV heval k m).symm⟩
  by_contra hP
  exact h (hJ.1 (Finset.nonempty_iff_ne_empty.2 hP))

/-! ### Part B support: the norm-indexed general normal form

The index $w$ of a block is its **norm exponent** (all its coefficients $c_{ab}$ are divisible by $\pi^w$),
not the exponent $\mu$ of the Hessian's off-diagonal entry. Good type is then `IsGoodType (unimodularCoords w)`,
exactly as in Hanke's Def. 3.1, and the reductions of p. 360 apply verbatim. -/

/-- **A 2-dimensional block $a x^2 + b xy + c y^2$ with exact norm exponent $w$.** The fields, in order:
1. $\pi^w \mid a$ and $\pi^w \mid c$;
2. *exactness:* $\pi^{w+1}$ does not divide all three of $a, b, c$ (so $w = \min(v(a), v(b), v(c))$, the
   norm exponent of the block, Hanke's $\nu_j$ in $Q = \bigoplus_j \pi^{\nu_j} Q_j$);
3. the **scale exponent** $\mu$: $b = \pi^\mu \beta$ with $\beta$ a unit, $w \le \mu$, $\pi^{\mu+1} \mid 2a$ and
   $\pi^{\mu+1} \mid 2c$ (the Hessian block $\begin{pmatrix} 2a & b \\ b & 2c \end{pmatrix}$ is $\pi^\mu$ times a unimodular
   matrix), and $\pi^\mu \mid 2\pi^w$ (i.e. $\mu \le w + \mathrm{ord}_\pi 2$). -/
def PairBlockW (π : R) (w : ℕ) (a b c : R) : Prop :=
  π ^ w ∣ a ∧ π ^ w ∣ c ∧ ¬ (π ^ (w + 1) ∣ a ∧ π ^ (w + 1) ∣ b ∧ π ^ (w + 1) ∣ c) ∧ ∃ μ β, b = π ^ μ * β ∧ IsUnit β ∧ w ≤ μ ∧
    π ^ (μ + 1) ∣ 2 * a ∧ π ^ (μ + 1) ∣ 2 * c ∧ π ^ μ ∣ 2 * π ^ w

/-- **Local normal form at every prime, indexed by exact norm exponents** (Hanke 2004, (2.3) and Lemma 2.1,
p. 355, corrected for ramified dyadic primes). $Q$ over the DVR $R$ is block diagonal: the fields say, in order,
1. 2-dimensional blocks occur only when $\pi \mid 2$;
2. each pair $(i, j) \in P$ has $i < j$;
3. distinct pairs are disjoint;
4. no cross terms outside the pairs: $c_{ij} = 0$ for $i < j$, $(i, j) \notin P$;
5. on a pair $(i, j) \in P$: $w_i = w_j$ and `PairBlockW π (w i) c_ii c_ij c_jj` (the block is
   $\pi^{w_i}$ times an integral form, $w_i$ is the **exact** minimum valuation of $c_{ii}, c_{ij}, c_{jj}$, and the
   scale exponent $\mu = v(c_{ij})$ satisfies $w_i \le \mu \le w_i + v(2)$);
6. unpaired $i$: $c_{ii} = \pi^{w_i} u$ with $u$ a unit.
So $w$ is Hanke's $\nu$ ($Q = \bigoplus_j \pi^{\nu_j} Q_j$, $Q_j$ primitive), and Good type (Def. 3.1) is
`IsGoodType (unimodularCoords w)`. When $\pi^2 \nmid 2$ this is exactly `IsJordanForm`
(`isJordanForm_iff_isJordanFormW`). -/
def IsJordanFormW (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) : Prop :=
  (P.Nonempty → π ∣ 2) ∧
  (∀ e ∈ P, e.1 < e.2) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  (∀ i j, i < j → (i, j) ∉ P → Q.coeff i j = 0) ∧
  (∀ e ∈ P, w e.1 = w e.2 ∧
    PairBlockW π (w e.1) (Q.coeff e.1 e.1) (Q.coeff e.1 e.2) (Q.coeff e.2 e.2)) ∧
  (∀ i, ¬ IsPaired P i → ∃ u, Q.coeff i i = π ^ w i * u ∧ IsUnit u)

/-- Hanke's normal form is a norm-indexed one with $w = \nu$ (and $\mu = \nu$ on every pair). -/
theorem IsJordanForm.toW {Q : QuadForm R n} {π : R} (hπ : Irreducible π) {P : Finset (Fin n × Fin n)}
    {ν : Fin n → ℕ} (h : IsJordanForm Q π P ν) : IsJordanFormW Q π P ν := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, h1, h2, h3, fun e he => ?_, h5⟩
  obtain ⟨a, ⟨b, hb, hbu⟩, c, d⟩ := h4 e he
  have h2' : π ∣ 2 := h0 ⟨e, he⟩
  refine ⟨a, c, d, fun ⟨_, h, _⟩ => dvr_not_pow_succ_dvd hπ hbu _ (hb ▸ h), ν e.1, b, hb, hbu,
    le_rfl, ?_, ?_, dvd_mul_left _ _⟩
  · rw [pow_succ, mul_comm 2]; exact mul_dvd_mul c h2'
  · rw [pow_succ, mul_comm 2]; exact mul_dvd_mul d h2'

/-- The norm exponent of a pair block, capped at $\mu$. -/
theorem exists_pairNormExp (π a c : R) (μ : ℕ) : ∃ w, w ≤ μ ∧ π ^ w ∣ a ∧ π ^ w ∣ c ∧
    (¬ π ^ (w + 1) ∣ a ∨ ¬ π ^ (w + 1) ∣ c ∨ w = μ) := by
  classical
  have hex : ∃ k, ¬ π ^ (k + 1) ∣ a ∨ ¬ π ^ (k + 1) ∣ c ∨ k = μ := ⟨μ, Or.inr (Or.inr rfl)⟩
  have hd : π ^ Nat.find hex ∣ a ∧ π ^ Nat.find hex ∣ c := by
    by_cases h0 : Nat.find hex = 0
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      simp only [not_or, not_not] at this
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)] at this
      exact ⟨this.1, this.2.1⟩
  exact ⟨Nat.find hex, Nat.find_min' hex (Or.inr (Or.inr rfl)), hd.1, hd.2, Nat.find_spec hex⟩

/-- **`IsJordanFormGen` yields a norm-indexed normal form** (same $Q$, same pairs; $w = \nu$ off the pairs,
$w = \min(\mu, v(c_{ii}), v(c_{jj}))$ on a pair). -/
theorem IsJordanFormGen.toW {Q : QuadForm R n} {π : R} (hπ : Irreducible π)
    {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} (h : IsJordanFormGen Q π P ν) :
    ∃ w : Fin n → ℕ, IsJordanFormW Q π P w ∧ ∀ i, ¬ IsPaired P i → w i = ν i := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hwp : ∀ e : Fin n × Fin n, ∃ w, w ≤ ν e.1 ∧ π ^ w ∣ Q.coeff e.1 e.1 ∧
      π ^ w ∣ Q.coeff e.2 e.2 ∧ (¬ π ^ (w + 1) ∣ Q.coeff e.1 e.1 ∨
        ¬ π ^ (w + 1) ∣ Q.coeff e.2 e.2 ∨ w = ν e.1) :=
    fun e => exists_pairNormExp π _ _ _
  choose wp hwp using hwp
  have huniq : ∀ e ∈ P, ∀ e' ∈ P, ∀ i, (i = e.1 ∨ i = e.2) → (e'.1 = i ∨ e'.2 = i) → e' = e := by
    intro e he e' he' i hi hi'
    by_contra hne
    obtain ⟨a, b, c, d⟩ := h2 e he e' he' (Ne.symm hne)
    rcases hi with rfl | rfl <;> rcases hi' with h | h
    · exact a h.symm
    · exact b h.symm
    · exact c h.symm
    · exact d h.symm
  let w : Fin n → ℕ := fun i => if hp : IsPaired P i then wp (Classical.choose hp) else ν i
  have hwe : ∀ e ∈ P, ∀ i, (i = e.1 ∨ i = e.2) → w i = wp e := by
    intro e he i hi
    have hp : IsPaired P i := ⟨e, he, by rcases hi with rfl | rfl <;> simp⟩
    simp only [w, dif_pos hp]
    obtain ⟨hm, hs⟩ := Classical.choose_spec hp
    rw [huniq e he _ hm i hi hs]
  refine ⟨w, ⟨h0, h1, h2, h3, fun e he => ?_, fun i hi => ?_⟩, fun i hi => by simp [w, hi]⟩
  · rw [hwe e he _ (Or.inl rfl), hwe e he _ (Or.inr rfl)]
    obtain ⟨-, ⟨b, hb, hbu⟩, d1, d2⟩ := h4 e he
    obtain ⟨hle, ha, hc, hor⟩ := hwp e
    refine ⟨rfl, ha, hc, ?_, ν e.1, b, hb, hbu, hle, d1, d2, ?_⟩
    · rintro ⟨x1, x2, x3⟩
      rcases hor with h | h | h
      · exact h x1
      · exact h x3
      · rw [h, hb] at x2; exact dvr_not_pow_succ_dvd hπ hbu _ x2
    have key : ∀ x : R, π ^ wp e ∣ x → ¬ π ^ (wp e + 1) ∣ x → π ^ (ν e.1 + 1) ∣ 2 * x →
        π ^ ν e.1 ∣ 2 * π ^ wp e := by
      intro x hx hx' hd
      obtain ⟨u, hu, hu1⟩ := dvr_exact hπ hx hx'
      rw [hu, ← mul_assoc] at hd
      exact (hu1.dvd_mul_right).1 ((pow_dvd_pow π (Nat.le_succ _)).trans hd)
    rcases hor with h | h | h
    · exact key _ ha h d1
    · exact key _ hc h d2
    · rw [h]; exact dvd_mul_left _ _
  · simp only [w, dif_neg hi]; exact h5 i hi

/-- **Lemma 2.1 at every prime** (Hanke 2004, Lemma 2.1, p. 355, corrected): a nondegenerate $Q$ over a DVR $R$
with $2 \ne 0$ has a $\mathrm{GL}_n(R)$-equivalent form $Q'$ in normal form `IsJordanFormW Q' π P w` (exact norm
exponents $w$; 2-dimensional blocks only when $\pi \mid 2$) with the same counts $r_{\pi^k}(m)$ for all $k, m$.
No hypothesis on $v_\pi(2)$.

*Update* (`docs/updates-and-errata.md`, Lemma 2.1 entry): the printed normal form (`IsJordanForm`) need not
exist at ramified dyadic primes ($x^2 + \pi xy + y^2$ over $\mathbb{Z}_2[\sqrt2]$); recording the scale exponent
$\mu$ of each 2-dimensional block besides $w$ repairs it, and for $\pi^2 \nmid 2$ nothing changes
(`isJordanForm_iff_isJordanFormW`). -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (corrected)"]
theorem exists_jordanFormW (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      IsJordanFormW Q' π P w ∧ (¬ π ∣ 2 → P = ∅) ∧ ∀ k m, repCount Q π k m = repCount Q' π k m := by
  obtain ⟨Q', P, ν, hJ, hP, hc⟩ := exists_jordanFormGen Q hQ π hπ h20
  obtain ⟨w, hw, -⟩ := hJ.toW hπ
  exact ⟨Q', P, w, hw, hP, hc⟩

/-- **At $\pi^2 \nmid 2$ the scale exponent of a pair block equals its norm exponent** ($\mu = w$): if
$\pi \mid 2$, $\pi^2 \nmid 2$ and `PairBlockW π w a b c`, then $b = \pi^w \beta$ with $\beta$ a unit.
*Proof:* $\mu \le w + v(2) = w + 1$; if $\mu = w + 1$ then $\pi^{w+2} \mid 2a, 2c$ gives $\pi^{w+1} \mid a, c$ and
$\pi^{w+1} \mid b$, contradicting exactness of $w$. -/
theorem PairBlockW.mu_eq {π : R} (hπ : Irreducible π) (h2 : ¬ π ^ 2 ∣ 2) (hπ2 : π ∣ 2) {w : ℕ}
    {a b c : R} (h : PairBlockW π w a b c) : ∃ β, b = π ^ w * β ∧ IsUnit β := by
  obtain ⟨-, -, hex, μ, β, hb, hβ, hle, h1, h1', h3⟩ := h
  obtain ⟨u, hu⟩ := hπ2
  have huu : IsUnit u :=
    dvr_isUnit_of_not_dvd hπ fun ⟨t, ht⟩ => h2 ⟨t, by rw [hu, ht]; ring⟩
  have hμ : μ ≤ w + 1 := by
    by_contra hcon
    have h' : π ^ w * π ^ 2 ∣ π ^ w * 2 := by
      rw [← pow_add, mul_comm (π ^ w)]; exact (pow_dvd_pow π (by omega)).trans h3
    exact h2 ((mul_dvd_mul_iff_left (pow_ne_zero w hπ.ne_zero)).1 h')
  rcases (show μ = w ∨ μ = w + 1 by omega) with rfl | rfl
  · exact ⟨β, hb, hβ⟩
  · exfalso
    have can : ∀ x : R, π ^ (w + 1 + 1) ∣ 2 * x → π ^ (w + 1) ∣ x := by
      intro x hx
      have h' : π ^ (w + 1) * π ∣ (u * x) * π := by
        rw [← pow_succ]; convert hx using 1; rw [hu]; ring
      exact huu.dvd_mul_left.1 ((mul_dvd_mul_iff_right hπ.ne_zero).1 h')
    exact hex ⟨can _ h1, hb ▸ dvd_mul_right _ _, can _ h1'⟩

/-- Multiplying a pair block by $\pi^d$ raises its norm exponent by $d$. -/
theorem PairBlockW.mul {π : R} (hπ : π ≠ 0) {w : ℕ} {a b c : R} (h : PairBlockW π w a b c) (d : ℕ) :
    PairBlockW π (w + d) (π ^ d * a) (π ^ d * b) (π ^ d * c) := by
  obtain ⟨ha, hc, hex, μ, β, hb, hβ, hle, h1, h2, h3⟩ := h
  have can : ∀ x : R, π ^ (w + d + 1) ∣ π ^ d * x → π ^ (w + 1) ∣ x := fun x h => by
    rw [show w + d + 1 = d + (w + 1) by omega, pow_add] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero d hπ)).1 h
  refine ⟨?_, ?_, fun ⟨x1, x2, x3⟩ => hex ⟨can _ x1, can _ x2, can _ x3⟩, μ + d, β, by rw [hb, pow_add]; ring, hβ, by omega, ?_, ?_, ?_⟩
  · rw [pow_add, mul_comm (π ^ w)]; exact mul_dvd_mul_left _ ha
  · rw [pow_add, mul_comm (π ^ w)]; exact mul_dvd_mul_left _ hc
  · rw [show 2 * (π ^ d * a) = π ^ d * (2 * a) by ring, show μ + d + 1 = d + (μ + 1) by omega,
      pow_add]
    exact mul_dvd_mul_left _ h1
  · rw [show 2 * (π ^ d * c) = π ^ d * (2 * c) by ring, show μ + d + 1 = d + (μ + 1) by omega,
      pow_add]
    exact mul_dvd_mul_left _ h2
  · rw [show 2 * π ^ (w + d) = π ^ d * (2 * π ^ w) by rw [pow_add]; ring,
      show μ + d = d + μ by omega, pow_add]
    exact mul_dvd_mul_left _ h3

/-- Dividing a pair block by $\pi^d$ lowers its norm exponent by $d$. -/
theorem PairBlockW.cancel {π : R} (hπ : π ≠ 0) {w : ℕ} {a b c : R} (d : ℕ)
    (h : PairBlockW π (w + d) (π ^ d * a) (π ^ d * b) (π ^ d * c)) : PairBlockW π w a b c := by
  obtain ⟨ha, hc, hex, μ, β, hb, hβ, hle, h1, h2, h3⟩ := h
  have hd0 : π ^ d ≠ 0 := pow_ne_zero d hπ
  have up : ∀ x : R, π ^ (w + 1) ∣ x → π ^ (w + d + 1) ∣ π ^ d * x := fun x h => by
    rw [show w + d + 1 = d + (w + 1) by omega, pow_add]; exact mul_dvd_mul_left _ h
  have can : ∀ k (x : R), π ^ (d + k) ∣ π ^ d * x → π ^ k ∣ x := fun k x h => by
    rw [pow_add] at h; exact (mul_dvd_mul_iff_left hd0).1 h
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = d + μ' := ⟨μ - d, by omega⟩
  refine ⟨can w a (by rwa [add_comm d w]), can w c (by rwa [add_comm d w]),
    fun ⟨x1, x2, x3⟩ => hex ⟨up _ x1, up _ x2, up _ x3⟩, μ', β, ?_, hβ,
    by omega, can _ _ ?_, can _ _ ?_, can _ _ ?_⟩
  · exact mul_left_cancel₀ hd0 (by rw [hb, pow_add, mul_assoc])
  · rwa [show 2 * (π ^ d * a) = π ^ d * (2 * a) by ring, show d + μ' + 1 = d + (μ' + 1) by omega]
      at h1
  · rwa [show 2 * (π ^ d * c) = π ^ d * (2 * c) by ring, show d + μ' + 1 = d + (μ' + 1) by omega]
      at h2
  · rwa [show 2 * π ^ (w + (d)) = π ^ d * (2 * π ^ w) by rw [pow_add]; ring] at h3

/-- **The printed normal form and the general one agree when $\pi^2 \nmid 2$** (all primes of $\mathbb{Q}$;
unramified dyadic primes of a number field): `IsJordanForm Q π P ν ↔ IsJordanFormW Q π P ν`, with the same
blocks $P$, $\nu = w$, and scale exponent $\mu = w$ in every 2-dimensional block (`PairBlockW.mu_eq`). Since Good,
Bad and Zero type depend only on $S_0 = $ `unimodularCoords ν`, the solution types of Def. 3.1 coincide too.
($\Rightarrow$ is `IsJordanForm.toW` and needs no hypothesis on $v_\pi(2)$.) -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem isJordanForm_iff_isJordanFormW {Q : QuadForm R n} {π : R} (hπ : Irreducible π)
    (h2 : ¬ π ^ 2 ∣ 2) {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} :
    IsJordanForm Q π P ν ↔ IsJordanFormW Q π P ν := by
  refine ⟨IsJordanForm.toW hπ, fun h => ?_⟩
  obtain ⟨h0, h1, h2', h3, h4, h5⟩ := h
  refine ⟨h0, h1, h2', h3, fun e he => ?_, h5⟩
  obtain ⟨hw, hpb⟩ := h4 e he
  obtain ⟨β, hb, hβ⟩ := hpb.mu_eq hπ h2 (h0 ⟨e, he⟩)
  exact ⟨hw, ⟨β, hb, hβ⟩, hpb.1, hpb.2.1⟩

/-- **Coefficients of a norm-indexed normal form lie inside blocks** (analogue of `IsJordanForm.coeff_block`,
which is all that `pow_dvd_evalIn_J`, `nu_eq_of_coeff_ne_zero`, `badIForm_rel`, `badIIForm_rel` and
`evalIn_badI/II` use): a nonzero $c_{ij}$, $i \le j$, has $w_i = w_j$ and $\pi^{w_i} \mid c_{ij}$. -/
theorem IsJordanFormW.coeff_block {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)}
    {w : Fin n → ℕ} (hJ : IsJordanFormW Q π P w) (i j : Fin n) (hij : i ≤ j) (h0 : Q.coeff i j ≠ 0) :
    w i = w j ∧ π ^ (w i) ∣ Q.coeff i j := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
  rcases hij.lt_or_eq with hlt | rfl
  · by_cases hP : (i, j) ∈ P
    · obtain ⟨hw, -, -, -, μ, β, hb, -, hle, -⟩ := h5 _ hP
      exact ⟨hw, by rw [hb]; exact dvd_mul_of_dvd_left (pow_dvd_pow π hle) _⟩
    · exact absurd (h4 i j hlt hP) h0
  · refine ⟨rfl, ?_⟩
    by_cases hp : IsPaired P i
    · obtain ⟨e, he, h | h⟩ := hp
      · obtain ⟨-, hd, -⟩ := h5 e he
        subst h; exact hd
      · obtain ⟨hw, -, hd, -⟩ := h5 e he
        subst h; rw [← hw]; exact hd
    · obtain ⟨u, hu, _⟩ := h6 i hp
      exact ⟨u, hu⟩

end QuadFormsKB.LocalDensity.DVR

