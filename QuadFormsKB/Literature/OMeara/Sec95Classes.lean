/-
# O'Meara §95: square classes of a non-dyadic local field, and the normalized base

**Setting.** $R$ is a complete discrete valuation ring (O'Meara's $\mathfrak o$; `IsAdicComplete`) with finite
residue field and fraction field $F$, non-dyadic ($2 \in R^\times$), $\pi$ a prime element of $R$ and $\Delta$ a unit
of $R$ which is not a square (O'Meara's fixed non-square unit, §63A; any such unit works).

**Defines** `S95.cls π Δ = (1, Δ, π, πΔ)`, the four representatives of $\dot F/\dot F^2$ (0-based).

**Proves** (used in steps 3 and 4 of the proof of O'Meara's 95:1, 1973 printing, pp. 281–282)
* `S95.isSquare_or_isSquare_mul`: every unit $\varepsilon$ is a square or $\Delta$ times a square;
* `S95.not_isSquare_algebraMap`: $\Delta$ is not a square in $F$;
* `S95.exists_cls`: every $x \in \dot F$ is $s^2$ times one of $1, \Delta, \pi, \pi\Delta$;
* `S95.isSquare_pow_iff`: $\Delta^m\pi^n \in \dot F^2$ if and only if $m$ and $n$ are even;
* `S95.exists_normalBasis`: an anisotropic quaternary space has a normalized orthogonal base
  (`S95.NormalBasis`: values $a_0, a_1, \pi a_2, \pi a_3$ with units $a_i$), as in step 4 of the proof
  ("By Proposition 63:17 we can take a lattice $L_1 \perp L_2$ on $V$ with $L_1 \cong \langle 1\rangle \perp
  \langle -\Delta\rangle$ and $L_2 \cong \langle\pi\rangle \perp \langle -\pi\Delta\rangle$"; only the units are left
  unnormalized here).
-/
import QuadFormsKB.Literature.OMeara.Sec95Basis
import QuadFormsKB.Literature.OMeara.Sec63A
import QuadFormsKB.Literature.OMeara.Sec92Class

open QuadraticMap Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace S95

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The four representatives $1, \Delta, \pi, \pi\Delta$ of the square classes of a non-dyadic local field
(0-based: `cls π Δ 0 = 1`, `cls π Δ 1 = Δ`, `cls π Δ 2 = π`, `cls π Δ 3 = πΔ`). -/
def cls (π Δ : R) : Fin 4 → F :=
  ![1, algebraMap R F Δ, algebraMap R F π, algebraMap R F π * algebraMap R F Δ]

/-- Every unit is a square or $\Delta$ times a square, for any non-square unit $\Delta$ (non-dyadic). -/
theorem isSquare_or_isSquare_mul (h2 : IsUnit (2 : R)) {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) {ε : R}
    (hε : IsUnit ε) : IsSquare ε ∨ IsSquare (ε * Δ) := by
  obtain ⟨Δ0, hΔ0, -, hall⟩ := exists_nonsquare_unit (R := R) h2
  obtain ⟨p, hp⟩ : IsSquare (Δ * Δ0) := (hall Δ hΔ).resolve_left hΔs
  rcases hall ε hε with h | ⟨q, hq⟩
  · exact Or.inl h
  · right
    obtain ⟨w, hw⟩ := hΔ0.exists_right_inv
    exact ⟨q * p * w, by
      linear_combination (-(ε * Δ) * (1 + Δ0 * w)) * hw + (Δ * Δ0 * w ^ 2) * hq + (q ^ 2 * w ^ 2) * hp⟩

/-- A unit of $R$ which is not a square in $R$ is not a square in $F$ ($R$ is integrally closed). -/
theorem not_isSquare_algebraMap {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) :
    ¬ IsSquare (algebraMap R F Δ) := by
  rintro ⟨f, hf⟩
  obtain ⟨g, hg⟩ := exists_alg_of_sq (R := R) (η := f) (c := Δ) (by rw [hf]; ring)
  exact hΔs ⟨g, alg_inj (R := R) (F := F) (by rw [map_mul, hg, ← hf])⟩

/-- Every $x \in \dot F$ is $s^2$ times one of $1, \Delta, \pi, \pi\Delta$. -/
theorem exists_cls (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔs : ¬ IsSquare Δ) {x : F} (hx : x ≠ 0) : ∃ i : Fin 4, ∃ s : F, s ≠ 0 ∧ x = s ^ 2 * cls π Δ i := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨k, u, hu, hxu⟩ := exists_rep hπ hx
  obtain ⟨w, hw⟩ := hΔ.exists_right_inv
  set P : F := algebraMap R F π with hP
  have hdecomp : P ^ k = (P ^ (k / 2)) ^ 2 * P ^ (k % 2) := by
    rw [pow_two, ← zpow_add₀ hne, ← zpow_add₀ hne]
    congr 1
    omega
  have hs0 : P ^ (k / 2) ≠ 0 := zpow_ne_zero _ hne
  have hw' : algebraMap R F Δ ≠ 0 := (map_ne_zero_iff _ (alg_inj (R := R) (F := F))).2 hΔ.ne_zero
  rw [hdecomp] at hxu
  have hu0 : algebraMap R F u ≠ 0 := (map_ne_zero_iff _ (alg_inj (R := R) (F := F))).2 hu.ne_zero
  have hΔe : algebraMap R F Δ * algebraMap R F w = 1 := by rw [← map_mul, hw, map_one]
  rcases isSquare_or_isSquare_mul h2 hΔ hΔs hu with ⟨v, hv⟩ | ⟨v, hv⟩
  · have hv0 : algebraMap R F v ≠ 0 := by
      intro h0
      apply hu0
      rw [hv, map_mul, h0, zero_mul]
    have hs : algebraMap R F v * P ^ (k / 2) ≠ 0 := mul_ne_zero hv0 hs0
    rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> rw [hk] at hxu
    · refine ⟨0, _, hs, ?_⟩
      rw [hxu, hv, map_mul]
      simp [cls]
      ring
    · refine ⟨2, _, hs, ?_⟩
      rw [hxu, hv, map_mul]
      simp [cls, hP]
      ring
  · have hu' : u = Δ * (v * w) ^ 2 := by
      linear_combination (-(u) * (1 + Δ * w)) * hw + (Δ * w ^ 2) * hv
    have hv0 : algebraMap R F v ≠ 0 := by
      intro h0
      apply hu0
      rw [hu', map_mul, map_pow, map_mul, h0, zero_mul]
      simp
    have hw0 : algebraMap R F w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hΔe
      exact zero_ne_one hΔe
    have hs : algebraMap R F v * algebraMap R F w * P ^ (k / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hv0 hw0) hs0
    rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> rw [hk] at hxu
    · refine ⟨1, _, hs, ?_⟩
      rw [hxu, hu']
      simp [cls]
      ring
    · refine ⟨3, _, hs, ?_⟩
      rw [hxu, hu']
      simp [cls, hP]
      ring

/-- $\Delta^m\pi^n$ is a square in $F$ if and only if $m$ and $n$ are even. -/
theorem isSquare_pow_iff {π : R} (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) (m n : ℕ) :
    IsSquare (algebraMap R F Δ ^ m * algebraMap R F π ^ n) ↔ Even m ∧ Even n := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  constructor
  · rintro ⟨s, hs⟩
    have hne0 : algebraMap R F Δ ^ m * algebraMap R F π ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ (alg_inj (R := R) (F := F))).2 hΔ.ne_zero))
        (pow_ne_zero _ hne)
    have hs0 : s ≠ 0 := by
      intro h0
      apply hne0
      rw [hs, h0, mul_zero]
    obtain ⟨k, v, hv, hsv⟩ := exists_rep hπ hs0
    have key : algebraMap R F (Δ ^ m) * algebraMap R F π ^ (n : ℤ) =
        algebraMap R F (v * v) * algebraMap R F π ^ (2 * k) := by
      rw [map_pow, zpow_natCast, hs, hsv, map_mul, two_mul, zpow_add₀ hne]
      ring
    have hle1 := rep_le hπ (hΔ.pow m) (hv.mul hv) key
    have hle2 := rep_le hπ (hv.mul hv) (hΔ.pow m) key.symm
    have hnk : (n : ℤ) = 2 * k := le_antisymm hle1 hle2
    rw [hnk] at key
    have hm := alg_inj (R := R) (F := F) (mul_right_cancel₀ (zpow_ne_zero _ hne) key)
    refine ⟨?_, ⟨k.toNat, by omega⟩⟩
    by_contra hodd
    obtain ⟨l, hl⟩ := Nat.not_even_iff_odd.1 hodd
    obtain ⟨w, hw⟩ := hΔ.exists_right_inv
    have e : Δ ^ (2 * l + 1) * w ^ (2 * l) = Δ * (Δ * w) ^ (2 * l) := by ring
    rw [hw, one_pow, mul_one, ← hl, hm] at e
    exact hΔs ⟨v * w ^ l, by rw [← e]; ring⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨algebraMap R F Δ ^ a * algebraMap R F π ^ b, by rw [ha, hb]; ring⟩

variable [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Three pairwise orthogonal vectors with values $\lambda\cdot$(units) in an anisotropic space cannot exist
(a binary unimodular form represents every unit). -/
theorem no_three_orth (h2 : IsUnit (2 : R)) (Q : QuadraticForm F V) (hQ : Q.Anisotropic) {v1 v2 v3 : V}
    (h12 : bil Q v1 v2 = 0) (h13 : bil Q v1 v3 = 0) (h23 : bil Q v2 v3 = 0) {l : F} (hl : l ≠ 0)
    {a1 a2 a3 : R} (h1 : IsUnit a1) (h2' : IsUnit a2) (h3 : IsUnit a3)
    (q1 : Q v1 = l * algebraMap R F a1) (q2 : Q v2 = l * algebraMap R F a2)
    (q3 : Q v3 = l * algebraMap R F a3) : False := by
  obtain ⟨w, hw⟩ := h3.exists_right_inv
  have hwu : IsUnit w := IsUnit.of_mul_eq_one a3 (by rw [mul_comm]; exact hw)
  obtain ⟨s, t, hst⟩ := exists_binary_one (F := F) h2 (h1.mul hwu).neg (h2'.mul hwu).neg
  have hrel : a1 * s ^ 2 + a2 * t ^ 2 + a3 = 0 := by
    linear_combination (-a3) * hst - (a1 * s ^ 2 + a2 * t ^ 2) * hw
  have hrel' := congrArg (algebraMap R F) hrel
  simp only [map_add, map_mul, map_pow, map_zero] at hrel'
  have hz : Q (algebraMap R F s • v1 + algebraMap R F t • v2 + v3) = 0 := by
    simp only [Q_add, Q_smul, bil_add_left, bil_smul_left, bil_smul_right, h12, h13, h23, q1, q2, q3]
    linear_combination l * hrel'
  have hz0 := hQ _ hz
  have hb : bil Q (algebraMap R F s • v1 + algebraMap R F t • v2 + v3) v3 = Q v3 := by
    simp only [bil_add_left, bil_smul_left, h13, h23, bil_self]
    ring
  rw [hz0, q3] at hb
  have ha3 : algebraMap R F a3 ≠ 0 := (map_ne_zero_iff _ (alg_inj (R := R) (F := F))).2 h3.ne_zero
  rw [show bil Q 0 v3 = 0 by simp [bil]] at hb
  exact mul_ne_zero hl ha3 hb.symm

/-- Rescaling a vector of nonzero norm by a power of $\pi$ makes its norm a unit or $\pi$ times a unit. -/
theorem exists_scale {π : R} (hπ : Irreducible π) (Q : QuadraticForm F V) {v : V} (hv : Q v ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ∃ a : R, IsUnit a ∧
      (Q (c • v) = algebraMap R F a ∨ Q (c • v) = algebraMap R F (π * a)) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨k, u, hu, hQv⟩ := exists_rep hπ hv
  refine ⟨algebraMap R F π ^ (-(k / 2)), zpow_ne_zero _ hne, u, hu, ?_⟩
  have e : (algebraMap R F π ^ (-(k / 2))) ^ 2 * Q v = algebraMap R F u * algebraMap R F π ^ (k % 2) := by
    rw [hQv, pow_two]
    calc _ = algebraMap R F u * (algebraMap R F π ^ (-(k / 2)) * algebraMap R F π ^ (-(k / 2)) *
          algebraMap R F π ^ k) := by ring
      _ = _ := by
        rw [← zpow_add₀ hne, ← zpow_add₀ hne, show -(k / 2) + -(k / 2) + k = k % 2 by omega]
  rw [Q_smul, e]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> rw [hk]
  · left; simp
  · right; simp [map_mul]; ring

/-- A combinatorial fact: a predicate on `Fin 4` with no three true and no three false values is true on exactly
two points, which a permutation moves to `0, 1`. -/
theorem exists_perm_of_no_three (p : Fin 4 → Prop)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ (p i ∧ p j ∧ p k))
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ (¬ p i ∧ ¬ p j ∧ ¬ p k)) :
    ∃ σ : Equiv.Perm (Fin 4), p (σ 0) ∧ p (σ 1) ∧ ¬ p (σ 2) ∧ ¬ p (σ 3) := by
  by_cases a0 : p 0 <;> by_cases a1 : p 1 <;> by_cases a2 : p 2 <;> by_cases a3 : p 3
  all_goals first
    | (exfalso; exact h1 0 1 2 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h1 0 1 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h1 0 2 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h1 1 2 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h2 0 1 2 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h2 0 1 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h2 0 2 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (exfalso; exact h2 1 2 3 (by decide) (by decide) (by decide) ⟨by assumption, by assumption, by assumption⟩)
    | (refine ⟨1, ?_⟩; simp [a0, a1, a2, a3]; done)
    | (refine ⟨Equiv.swap 1 2, ?_⟩; simp [Equiv.swap_apply_def, a0, a1, a2, a3]; done)
    | (refine ⟨Equiv.swap 1 3, ?_⟩; simp [Equiv.swap_apply_def, a0, a1, a2, a3]; done)
    | (refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩; simp [Equiv.swap_apply_def, a0, a1, a2, a3]; done)
    | (refine ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩; simp [Equiv.swap_apply_def, a0, a1, a2, a3]; done)
    | (refine ⟨Equiv.swap 0 2 * Equiv.swap 1 3, ?_⟩; simp [Equiv.swap_apply_def, a0, a1, a2, a3]; done)

/-- **A normalized orthogonal base** (O'Meara 1973, proof of 95:1, step 4, p. 282, from Proposition 63:17): a
regular anisotropic quaternary space over a non-dyadic local field has an orthogonal base $e_0, \dots, e_3$ with
$Q(e_0), Q(e_1)$ units and $Q(e_2), Q(e_3)$ equal to $\pi$ times units. (Three unit values, or three values of order
$1$, would give an isotropic ternary subspace, since a binary unimodular form represents every unit, 92:1b.) -/
theorem exists_normalBasis (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) (Q : QuadraticForm F V)
    (hQ : Q.Anisotropic) (hn : finrank F V = 4) : Nonempty (NormalBasis Q π) := by
  classical
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := (QuadraticMap.associated Q : LinearMap.BilinForm F V)) ⟨fun x y => by simpa using bil_comm Q x y⟩
  let e : Basis (Fin 4) F V := b.reindex (finCongr hn)
  have horth : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0 := by
    intro i j hij
    have h0 : (QuadraticMap.associated Q : LinearMap.BilinForm F V) (b ((finCongr hn).symm i))
        (b ((finCongr hn).symm j)) = 0 := hb ((finCongr hn).symm.injective.ne hij)
    simp only [e, Basis.reindex_apply]
    exact h0
  have hQe : ∀ i, Q (e i) ≠ 0 := by
    intro i h
    exact e.ne_zero i (hQ (e i) h)
  choose c hc a ha hQc using fun i => exists_scale hπ Q (hQe i)
  let w : Fin 4 → V := fun i => c i • e i
  have worth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0 := by
    intro i j hij
    simp only [w, bil_smul_left, bil_smul_right, horth i j hij]
    ring
  let t : Fin 4 → Prop := fun i => Q (w i) = algebraMap R F (a i)
  have hnot : ∀ i, ¬ t i → Q (w i) = algebraMap R F (π * a i) := fun i hi => (hQc i).resolve_left hi
  have h3t : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ (t i ∧ t j ∧ t k) := by
    rintro i j k hij hik hjk ⟨ti, tj, tk⟩
    exact no_three_orth h2 Q hQ (worth i j hij) (worth i k hik) (worth j k hjk) (l := 1) one_ne_zero
      (ha i) (ha j) (ha k) (by rw [ti, one_mul]) (by rw [tj, one_mul]) (by rw [tk, one_mul])
  have h3f : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ (¬ t i ∧ ¬ t j ∧ ¬ t k) := by
    rintro i j k hij hik hjk ⟨ti, tj, tk⟩
    exact no_three_orth h2 Q hQ (worth i j hij) (worth i k hik) (worth j k hjk) hne
      (ha i) (ha j) (ha k) (by rw [hnot i ti, map_mul]) (by rw [hnot j tj, map_mul])
      (by rw [hnot k tk, map_mul])
  obtain ⟨σ, s0, s1, s2, s3⟩ := exists_perm_of_no_three t h3t h3f
  let e' : Basis (Fin 4) F V :=
    (e.reindex σ.symm).unitsSMul fun i => Units.mk0 (c (σ i)) (hc _)
  have he' : ∀ i, e' i = w (σ i) := by
    intro i
    simp [e', w, Basis.unitsSMul_apply, Basis.reindex_apply, Units.smul_def]
  exact ⟨{ e := e'
           a := fun i => a (σ i)
           unit := fun i => ha _
           orth := fun i j hij => by
             rw [he', he']; exact worth _ _ (σ.injective.ne hij)
           Q0 := by rw [he']; exact s0
           Q1 := by rw [he']; exact s1
           Q2 := by rw [he']; exact hnot _ s2
           Q3 := by rw [he']; exact hnot _ s3 }⟩

end S95

end QuadFormsKB.OMeara
