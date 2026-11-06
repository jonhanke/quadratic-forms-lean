/-
# The ramified binary kernel at a dyadic place: the counts mod $\pi^k$

Continuation of `DyadicR2RamCount.lean`. Over $R_k = R/\pi^k$ ($R$ a discrete valuation ring with finite residue field,
$\pi\mid t$, $\pi\,\|\,n$, $\pi^d\,\|\,4n - t^2$):

* `card_stab_level`: $\#\{y \bmod \pi^k : N\circ[e_0\,|\,y] \equiv N\} = 2q^d$ for $k > d \ge 1$;
* `card_normOne_level`: $\#\{\xi \bmod \pi^k : N(\xi) \equiv 1\} = 2q^k$ when the unit norms have index $2$ in the units of $R$
  (`IndexTwo`) and $1 + \pi^kR$ consists of squares;
* `localDensityForm_eisForm`: $\beta(N, N) = 4q^d = 4|\det H_N|^{-1}$.

Sources: GHY 2001, §6, (6.5) (the kernel of the ramified case is the norm form of $\mathcal O_{E}$); Kitaoka 1993, §5.6
[unverified] (densities). Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.DyadicR2RamCount

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.R2Ram

open QuadForm LocalDensity LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

/-! ### Lifts from $R/\pi^k$ -/

section Lift

variable (π) (k : ℕ)

/-- A chosen lift of a class mod $\pi^k$. -/
def lft (x : R ⧸ Ideal.span {π ^ k}) : R := (Ideal.Quotient.mk_surjective x).choose

theorem mk_lft (x : R ⧸ Ideal.span {π ^ k}) : Ideal.Quotient.mk _ (lft π k x) = x :=
  (Ideal.Quotient.mk_surjective x).choose_spec

variable {π k}

theorem mk_eq_mk_iff {r s : R} :
    (Ideal.Quotient.mk (Ideal.span {π ^ k}) r = Ideal.Quotient.mk _ s) ↔ π ^ k ∣ r - s := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem lft_mk_sub (r : R) : π ^ k ∣ lft π k (Ideal.Quotient.mk _ r) - r :=
  mk_eq_mk_iff.1 (mk_lft π k _)

theorem pow_dvd_lft_sub_iff {a : ℕ} (hak : a ≤ k) (r c : R) :
    π ^ a ∣ lft π k (Ideal.Quotient.mk _ r) - c ↔ π ^ a ∣ r - c := by
  have h := (pow_dvd_pow π hak).trans (lft_mk_sub (π := π) (k := k) r)
  constructor
  · intro h1; have := dvd_sub h1 h; rwa [sub_sub_sub_cancel_left] at this
  · intro h1; have := dvd_add h1 h; rwa [sub_add_sub_cancel'] at this

theorem isUnit_mk_iff (hπ : Irreducible π) (hk : 1 ≤ k) (r : R) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {π ^ k}) r) ↔ ¬ π ∣ r := by
  constructor
  · rintro ⟨u, hu⟩ hr
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ Ideal.span {π ^ k})
    have h1 : Ideal.Quotient.mk (Ideal.span {π ^ k}) (r * s) = Ideal.Quotient.mk _ 1 := by
      rw [map_mul, hs, ← hu, Units.mul_inv, map_one]
    have h2 := (dvd_pow_self π (by omega)).trans (mk_eq_mk_iff.1 h1)
    have h3 := dvd_sub (dvd_mul_of_dvd_left hr s) h2
    rw [sub_sub_cancel] at h3
    exact hπ.not_isUnit (isUnit_of_dvd_one h3)
  · intro h
    exact (dvr_isUnit_of_not_dvd hπ h).map _

end Lift

/-! ### One-dimensional boxes -/

section Box

variable [Finite (IsLocalRing.ResidueField R)]

/-- **A residue class mod $\pi^a$ inside $R/\pi^k$** has $q^{k-a}$ elements ($a \le k$). -/
theorem card_box1 (hπ : Irreducible π) {a k : ℕ} (hak : a ≤ k) (c : R) :
    Nat.card {x : R ⧸ Ideal.span {π ^ k} // π ^ a ∣ lft π k x - c} = q R ^ (k - a) := by
  have hπ0 := hπ.ne_zero
  have hk' : π ^ k = π ^ a * π ^ (k - a) := by rw [← pow_add]; congr 1; omega
  rw [← card_quot_pow π hπ (k - a)]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨Ideal.Quotient.mk _ (c + π ^ a * lft π (k - a) w), by
      rw [pow_dvd_lft_sub_iff hak, add_sub_cancel_left]; exact dvd_mul_right _ _⟩) ⟨?_, ?_⟩)
  · intro w₁ w₂ h
    have h' := mk_eq_mk_iff.1 (congrArg Subtype.val h)
    rw [add_sub_add_left_eq_sub, ← mul_sub, hk', mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)] at h'
    rw [← mk_lft π (k - a) w₁, ← mk_lft π (k - a) w₂]
    exact mk_eq_mk_iff.2 h'
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hx
    refine ⟨Ideal.Quotient.mk _ s, Subtype.ext ?_⟩
    simp only
    rw [← mk_lft π k x, mk_eq_mk_iff]
    have h1 := lft_mk_sub (π := π) (k := k - a) s
    have h2 : π ^ k ∣ π ^ a * (lft π (k - a) (Ideal.Quotient.mk _ s) - s) := by
      rw [hk']; exact mul_dvd_mul_left _ h1
    have e : c + π ^ a * lft π (k - a) (Ideal.Quotient.mk _ s) - lft π k x =
        π ^ a * (lft π (k - a) (Ideal.Quotient.mk _ s) - s) := by
      rw [show lft π k x = c + π ^ a * s by rw [← hs]; ring]; ring
    rw [e]; exact h2

/-- **A box mod $\pi^k$** ($a, b \le k$): $q^{k-a}q^{k-b}$ classes. -/
theorem card_box2 (hπ : Irreducible π) {a b k : ℕ} (hak : a ≤ k) (hbk : b ≤ k) (c₀ c₁ : R) :
    Nat.card {y : Fin 2 → R ⧸ Ideal.span {π ^ k} //
      π ^ a ∣ lft π k (y 0) - c₀ ∧ π ^ b ∣ lft π k (y 1) - c₁} = q R ^ (k - a) * q R ^ (k - b) := by
  rw [← card_box1 hπ hak c₀, ← card_box1 hπ hbk c₁, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun y => (⟨y.1 0, y.2.1⟩, ⟨y.1 1, y.2.2⟩)
      invFun := fun p => ⟨![p.1.1, p.2.1], p.1.2, p.2.2⟩
      left_inv := fun y => Subtype.ext (funext fun i => by fin_cases i <;> rfl)
      right_inv := fun p => rfl }

end Box

/-! ### The stabilizer count -/

section Stab

variable [Finite (IsLocalRing.ResidueField R)]
variable (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w) {d : ℕ}
  (hd : π ^ d ∣ 4 * n - t ^ 2) (hd' : ¬ π ^ (d + 1) ∣ 4 * n - t ^ 2)

include hπ ht hn hw hd hd'

/-- **The stabilizer of $e_0$ mod $\pi^k$** ($k > d$, $d \ge 1$): $2q^d$ elements. -/
theorem card_stab_level {k : ℕ} (hdk : d < k) (hd1 : 1 ≤ d) :
    Nat.card {y : Fin 2 → R ⧸ Ideal.span {π ^ k} //
      (eisForm (Ideal.Quotient.mk _ t) (Ideal.Quotient.mk _ n)).compMat (stabM y) =
        eisForm (Ideal.Quotient.mk _ t) (Ideal.Quotient.mk _ n)} = 2 * q R ^ d := by
  classical
  haveI : Finite (R ⧸ Ideal.span {π ^ k}) := finite_quot_pow π hπ k
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  set m := 2 * k - d with hm
  have hA : (m + 1) / 2 ≤ k := by omega
  have hB : m / 2 ≤ k := by omega
  -- the condition, in terms of lifts
  let Bp : (Fin 2 → R ⧸ Ideal.span {π ^ k}) → Prop := fun y =>
    π ^ ((m + 1) / 2) ∣ lft π k (y 0) - 0 ∧ π ^ (m / 2) ∣ lft π k (y 1) - 1
  let Bm : (Fin 2 → R ⧸ Ideal.span {π ^ k}) → Prop := fun y =>
    π ^ ((m + 1) / 2) ∣ lft π k (y 0) - t ∧ π ^ (m / 2) ∣ lft π k (y 1) - (-1)
  have hiff : ∀ y : Fin 2 → R ⧸ Ideal.span {π ^ k},
      (eisForm (mk t) (mk n)).compMat (stabM y) = eisForm (mk t) (mk n) ↔ Bp y ∨ Bm y := by
    intro y
    rw [compMat_stabM_iff]
    set y0 := lft π k (y 0)
    set y1 := lft π k (y 1)
    have e0 : y 0 = mk y0 := (mk_lft π k _).symm
    have e1 : y 1 = mk y1 := (mk_lft π k _).symm
    have hl : (2 * y 0 + mk t * y 1 = mk t ∧ nrm (mk t) (mk n) (y 0) (y 1) = mk n) ↔
        (π ^ k ∣ 2 * y0 + t * y1 - t ∧ π ^ k ∣ nrm t n y0 y1 - n) := by
      rw [e0, e1, ← mk_eq_mk_iff, ← mk_eq_mk_iff]
      simp only [nrm, map_add, map_mul, map_ofNat]
      exact Iff.rfl
    rw [hl, stab_iff_box hπ ht hn hw hd hd' hdk, ← hm, pow_dvd_nrm_iff hπ ht hn hw,
      pow_dvd_nrm_iff hπ ht hn hw]
    simp only [Bp, Bm, sub_zero, sub_neg_eq_add]
    exact Iff.rfl
  have hdisj : ∀ y, ¬ (Bp y ∧ Bm y) := by
    intro y ⟨h1, h2⟩
    apply box_disjoint hπ ht hn hw hd hd' hdk (lft π k (y 0)) (lft π k (y 1))
    rw [pow_dvd_nrm_iff hπ ht hn hw, pow_dvd_nrm_iff hπ ht hn hw, ← hm]
    simp only [Bp, Bm, sub_zero, sub_neg_eq_add] at h1 h2
    exact ⟨h1, h2⟩
  have hcard := Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans
    (subtypeOrEquiv Bp Bm (Pi.disjoint_iff.mpr fun y => by
      rw [Prop.disjoint_iff]; exact hdisj y)))
  rw [hcard, Nat.card_sum, card_box2 hπ hA hB, card_box2 hπ hA hB]
  rw [← pow_add, show k - (m + 1) / 2 + (k - m / 2) = d by omega]
  ring

end Stab

/-! ### The norm-one count -/

section NormOne

/-- **The unit norms have index $2$ in the units of $R$** (for the norm form $N(a,b) = a^2 + tab + nb^2$): some unit is not a
norm, and the product of two non-norm units is a norm. At a dyadic place this is the Hilbert-symbol statement
$[\mathfrak o^\times : N\mathcal O_E^\times] = 2$ for ramified $E$ (`DyadicR2RamNorm.lean`). -/
structure IndexTwo (t n : R) : Prop where
  /-- Some unit is not a norm. -/
  exists_non : ∃ u : R, IsUnit u ∧ ¬ ∃ a b, nrm t n a b = u
  /-- Two non-norm units multiply to a norm. -/
  mul_non : ∀ u u' : R, IsUnit u → IsUnit u' → (¬ ∃ a b, nrm t n a b = u) → (¬ ∃ a b, nrm t n a b = u') →
    ∃ a b, nrm t n a b = u * u'

variable {t n : R}

theorem isNorm_mul {u u' : R} (h : ∃ a b, nrm t n a b = u) (h' : ∃ a b, nrm t n a b = u') :
    ∃ a b, nrm t n a b = u * u' := by
  obtain ⟨a, b, rfl⟩ := h
  obtain ⟨c, d, rfl⟩ := h'
  exact ⟨_, _, nrm_mul t n a b c d⟩

theorem isNorm_sq_mul (c : R) {u : R} (h : ∃ a b, nrm t n a b = u) : ∃ a b, nrm t n a b = c ^ 2 * u := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨_, _, nrm_smul t n c a b⟩

theorem isNorm_inv {u : R} (hu : IsUnit u) (h : ∃ a b, nrm t n a b = u) :
    ∃ a b, nrm t n a b = (↑hu.unit⁻¹ : R) := by
  have := isNorm_sq_mul (↑hu.unit⁻¹ : R) h
  rwa [pow_two, mul_assoc, show (↑hu.unit⁻¹ : R) * u = 1 from hu.val_inv_mul, mul_one] at this

/-- **$N\xi \equiv u$ is solvable mod $\pi^k$ iff $u$ is a norm** ($u$ a unit, $1 + \pi^kR$ consisting of squares). -/
theorem exists_level_iff (hπ : Irreducible π) {k : ℕ} (hk : 1 ≤ k) (hsq : ∀ x : R, π ^ k ∣ x - 1 → IsSquare x)
    {u : R} (hu : IsUnit u) :
    (∃ ξ : Fin 2 → R ⧸ Ideal.span {π ^ k},
        nrm (Ideal.Quotient.mk _ t) (Ideal.Quotient.mk _ n) (ξ 0) (ξ 1) = Ideal.Quotient.mk _ u) ↔
      ∃ a b, nrm t n a b = u := by
  constructor
  · rintro ⟨ξ, hξ⟩
    set a := lft π k (ξ 0)
    set b := lft π k (ξ 1)
    have h : π ^ k ∣ nrm t n a b - u := by
      rw [← mk_eq_mk_iff, ← hξ, ← mk_lft π k (ξ 0), ← mk_lft π k (ξ 1)]
      simp only [nrm, map_add, map_mul]
      rfl
    have hN : IsUnit (nrm t n a b) := by
      refine dvr_isUnit_of_not_dvd hπ fun hN => ?_
      have := dvd_sub hN ((dvd_pow_self π (by omega)).trans h)
      rw [sub_sub_cancel] at this
      exact hπ.not_isUnit (isUnit_of_dvd_unit this hu)
    obtain ⟨s, hs⟩ := hsq (u * ↑hN.unit⁻¹) (by
      have e : u * ↑hN.unit⁻¹ - 1 = -(nrm t n a b - u) * ↑hN.unit⁻¹ := by
        rw [neg_sub, sub_mul, hN.mul_val_inv]
      rw [e]; exact (dvd_neg.2 h).mul_right _)
    refine ⟨s * a, s * b, ?_⟩
    rw [nrm_smul, pow_two, ← hs, mul_assoc, hN.val_inv_mul, mul_one]
  · rintro ⟨a, b, rfl⟩
    exact ⟨![Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b], by simp [nrm]⟩

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The norm-one count** $\#\{\xi \bmod \pi^k : N(\xi) \equiv 1\} = 2q^k$ ($\pi\mid t$, $\pi\,\|\,n$, index two, $1+\pi^kR$ squares). -/
theorem card_normOne_level (hπ : Irreducible π) {w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w)
    (hI : IndexTwo t n) {k : ℕ} (hk : 1 ≤ k) (hsq : ∀ x : R, π ^ k ∣ x - 1 → IsSquare x) :
    Nat.card {ξ : Fin 2 → R ⧸ Ideal.span {π ^ k} //
      (eisForm (Ideal.Quotient.mk _ t) (Ideal.Quotient.mk _ n)).eval ξ = 1} = 2 * q R ^ k := by
  classical
  set Rk := R ⧸ Ideal.span {π ^ k}
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  set tk := mk t
  set nk := mk n
  have hfin : Finite Rk := finite_quot_pow π hπ k
  haveI : Fintype Rk := Fintype.ofFinite Rk
  -- the image of the norm on units
  let Im : Rk → Prop := fun x => IsUnit x ∧ ∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x
  let Co : Rk → Prop := fun x => IsUnit x ∧ ¬ ∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x
  -- units of `Rk` with a unit in the first coordinate
  have hunit : ∀ ξ : Fin 2 → Rk, IsUnit (nrm tk nk (ξ 0) (ξ 1)) ↔ IsUnit (ξ 0) := by
    intro ξ
    rw [← mk_lft π k (ξ 0), ← mk_lft π k (ξ 1)]
    have : nrm tk nk (mk (lft π k (ξ 0))) (mk (lft π k (ξ 1))) = mk (nrm t n (lft π k (ξ 0)) (lft π k (ξ 1))) := by
      simp [nrm, tk, nk]
    rw [this, isUnit_mk_iff hπ hk, isUnit_mk_iff hπ hk]
    have h1 := pow_dvd_nrm_iff hπ ht hn hw 1 (lft π k (ξ 0)) (lft π k (ξ 1))
    simp only [pow_one, Nat.reduceAdd, Nat.reduceDiv, pow_zero, one_dvd, and_true] at h1
    rw [h1]
  -- (1) `#U = #Rkˣ · q^k`
  have hU1 : Nat.card {ξ : Fin 2 → Rk // IsUnit (nrm tk nk (ξ 0) (ξ 1))} =
      Nat.card {x : Rk // IsUnit x} * q R ^ k := by
    rw [← card_quot_pow π hπ k, ← Nat.card_prod]
    exact Nat.card_congr ((Equiv.subtypeEquivRight hunit).trans
      ((Equiv.subtypeEquiv (finTwoArrowEquiv _) fun y => Iff.rfl).trans Equiv.prodSubtypeFstEquivSubtypeProd))
  -- (2) `#U = #Im · #(norm one)`
  let ρ : Rk → Fin 2 → Rk := fun x =>
    if h : ∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x then h.choose else 0
  have hρ : ∀ x, (∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x) → nrm tk nk (ρ x 0) (ρ x 1) = x := by
    intro x hx; simp only [ρ, dif_pos hx]; exact hx.choose_spec
  have hmul : ∀ ξ η : Fin 2 → Rk, nrm tk nk ((mulM tk nk ξ *ᵥ η) 0) ((mulM tk nk ξ *ᵥ η) 1) =
      nrm tk nk (ξ 0) (ξ 1) * nrm tk nk (η 0) (η 1) := by
    intro ξ η; have := eval_mulM tk nk ξ η; rwa [eval_eisForm, eval_eisForm, eval_eisForm] at this
  have hsmul : ∀ (c : Rk) (η : Fin 2 → Rk),
      nrm tk nk ((c • η) 0) ((c • η) 1) = c ^ 2 * nrm tk nk (η 0) (η 1) := by
    intro c η; simp only [Pi.smul_apply, smul_eq_mul]; exact nrm_smul _ _ _ _ _
  have hconj : ∀ ξ : Fin 2 → Rk, nrm tk nk (conjV tk ξ 0) (conjV tk ξ 1) = nrm tk nk (ξ 0) (ξ 1) := by
    intro ξ; have := eval_conjV tk nk ξ; rwa [eval_eisForm, eval_eisForm] at this
  have hMc : ∀ ξ : Fin 2 → Rk, mulM tk nk ξ * mulM tk nk (conjV tk ξ) = nrm tk nk (ξ 0) (ξ 1) • 1 := by
    intro ξ; rw [mulM_mul_conj, eval_eisForm]
  have hcM : ∀ ξ : Fin 2 → Rk, mulM tk nk (conjV tk ξ) * mulM tk nk ξ = nrm tk nk (ξ 0) (ξ 1) • 1 := by
    intro ξ; rw [mulM_conj_mul, eval_eisForm]
  have hU2 : Nat.card {ξ : Fin 2 → Rk // IsUnit (nrm tk nk (ξ 0) (ξ 1))} =
      Nat.card {x : Rk // Im x} * Nat.card {η : Fin 2 → Rk // nrm tk nk (η 0) (η 1) = 1} := by
    rw [← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun ξ => (⟨nrm tk nk (ξ.1 0) (ξ.1 1), ξ.2, ξ.1, rfl⟩,
          ⟨Ring.inverse (nrm tk nk (ξ.1 0) (ξ.1 1)) •
            (mulM tk nk (conjV tk (ρ (nrm tk nk (ξ.1 0) (ξ.1 1)))) *ᵥ ξ.1), by
            have hi := Ring.inverse_mul_cancel _ ξ.2
            rw [hsmul, hmul, hconj, hρ _ ⟨ξ.1, rfl⟩]
            linear_combination (Ring.inverse (nrm tk nk (ξ.1 0) (ξ.1 1)) * nrm tk nk (ξ.1 0) (ξ.1 1) + 1) * hi⟩)
        invFun := fun p => ⟨mulM tk nk (ρ p.1.1) *ᵥ p.2.1, by
          rw [hmul, hρ _ p.1.2.2, p.2.2, mul_one]; exact p.1.2.1⟩
        left_inv := fun ξ => ?_
        right_inv := fun p => ?_ }
    · apply Subtype.ext
      simp only
      rw [mulVec_smul, mulVec_mulVec, hMc, hρ _ ⟨ξ.1, rfl⟩, smul_mulVec, one_mulVec, smul_smul,
        Ring.inverse_mul_cancel _ ξ.2, one_smul]
    · obtain ⟨⟨u, hu, hu'⟩, ⟨η, hη⟩⟩ := p
      have h : nrm tk nk ((mulM tk nk (ρ u) *ᵥ η) 0) ((mulM tk nk (ρ u) *ᵥ η) 1) = u := by
        rw [hmul, hρ _ hu', hη, mul_one]
      refine Prod.ext (Subtype.ext h) (Subtype.ext ?_)
      simp only
      rw [h, mulVec_mulVec, hcM, hρ _ hu', smul_mulVec, one_mulVec, smul_smul,
        Ring.inverse_mul_cancel _ hu, one_smul]
  -- (3) `#Im = #Co`, so `2 #Im = #Rkˣ`
  obtain ⟨u0, hu0, hu0n⟩ := hI.exists_non
  set u0' : R := ↑hu0.unit⁻¹
  have hu0' : IsUnit u0' := Units.isUnit _
  have h00 : u0' * u0 = 1 := hu0.val_inv_mul
  have hlev : ∀ {u : R}, IsUnit u → ((∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = mk u) ↔
      ∃ a b, nrm t n a b = u) := fun hu => exists_level_iff (t := t) (n := n) hπ hk hsq hu
  have hlft : ∀ x : Rk, IsUnit x → IsUnit (lft π k x) := fun x hx => by
    rw [← mk_lft π k x, isUnit_mk_iff hπ hk] at hx; exact dvr_isUnit_of_not_dvd hπ hx
  have hImP : ∀ x : Rk, IsUnit x → ((∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x) ↔
      ∃ a b, nrm t n a b = lft π k x) := fun x hx => by
    have := hlev (hlft x hx)
    rwa [mk_lft] at this
  have hIC : Nat.card {x : Rk // Im x} = Nat.card {x : Rk // Co x} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨mk u0 * x.1, (hu0.map mk).mul x.2.1, fun hP => ?_⟩
        invFun := fun y => ⟨mk u0' * y.1, (hu0'.map mk).mul y.2.1, ?_⟩
        left_inv := fun x => Subtype.ext (by
          simp only; rw [← mul_assoc, ← map_mul, h00, map_one, one_mul])
        right_inv := fun y => Subtype.ext (by
          simp only; rw [← mul_assoc, ← map_mul, mul_comm u0 u0', h00, map_one, one_mul]) }
    · obtain ⟨hx, hxP⟩ := x.2
      have hr := hlft _ hx
      have e : mk u0 * x.1 = mk (u0 * lft π k x.1) := by rw [map_mul, mk_lft]
      rw [e] at hP
      have hP' := (hlev (hu0.mul hr)).1 hP
      have hPr := (hImP _ hx).1 hxP
      apply hu0n
      have := isNorm_mul hP' (isNorm_inv hr hPr)
      rwa [mul_assoc, hr.mul_val_inv, mul_one] at this
    · obtain ⟨hy, hyP⟩ := y.2
      have hs := hlft _ hy
      have hns : ¬ ∃ a b, nrm t n a b = lft π k y.1 := fun h => hyP ((hImP _ hy).2 h)
      have h1 := hI.mul_non u0 _ hu0 hs hu0n hns
      have h2 := isNorm_sq_mul u0' h1
      have e : u0' ^ 2 * (u0 * lft π k y.1) = u0' * lft π k y.1 := by
        rw [pow_two, mul_assoc, ← mul_assoc u0' u0, h00, one_mul]
      rw [e] at h2
      have e' : mk u0' * y.1 = mk (u0' * lft π k y.1) := by rw [map_mul, mk_lft]
      rw [e']
      exact (hlev (hu0'.mul hs)).2 h2
  have hsplit : Nat.card {x : Rk // IsUnit x} = Nat.card {x : Rk // Im x} + Nat.card {x : Rk // Co x} := by
    rw [← Nat.card_sum]
    refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans
      (subtypeOrEquiv Im Co (Pi.disjoint_iff.mpr fun x => by
        rw [Prop.disjoint_iff]; exact fun h => h.2.2 h.1.2)))
    constructor
    · intro hx
      by_cases h : ∃ ξ : Fin 2 → Rk, nrm tk nk (ξ 0) (ξ 1) = x
      exacts [Or.inl ⟨hx, h⟩, Or.inr ⟨hx, h⟩]
    · rintro (h | h)
      exacts [h.1, h.1]
  -- conclusion
  have hpos : 0 < Nat.card {x : Rk // IsUnit x} := by
    haveI : Nonempty {x : Rk // IsUnit x} := ⟨⟨1, isUnit_one⟩⟩
    exact Nat.card_pos
  have hR : Nat.card {ξ : Fin 2 → Rk // (eisForm tk nk).eval ξ = 1} =
      Nat.card {η : Fin 2 → Rk // nrm tk nk (η 0) (η 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun ξ => by rw [eval_eisForm])
  rw [hR]
  have e1 := hU1.symm.trans hU2
  rw [hsplit, ← hIC] at e1
  have hIpos : 0 < Nat.card {x : Rk // Im x} := by
    rw [hsplit, ← hIC] at hpos; omega
  apply Nat.eq_of_mul_eq_mul_left hIpos
  rw [← e1]; ring

end NormOne

/-! ### The self-density -/

section Density

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The self-density of the ramified norm form** $\beta(N, N) = 4q^d$, $\pi^d\,\|\,\det H_N = 4n - t^2$ ($\pi \mid t$,
$\pi\,\|\,n$, $d \ge 1$, unit norms of index $2$, and $1 + \pi^{k_0}R$ consisting of squares for some $k_0$). Here $d$ is the
exponent of the different of $E = F(\varpi)$ (GHY Lemma A.1: $\mathfrak D = (\pi_E^d)$; $4n - t^2 = -(\varpi - \bar\varpi)^2$), and the
stabilizer count mirrors the integral models of GHY Lemma B.1. -/
@[kb "ganhankeyu2001" "§6, (6.5) (A_{E_δ} with αN, E_δ ramified); Appendix A, Lemma A.1; Appendix B, Lemma B.1, pp. 123–124"]
theorem localDensityForm_eisForm (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w)
    {d : ℕ} (hd : π ^ d ∣ 4 * n - t ^ 2) (hd' : ¬ π ^ (d + 1) ∣ 4 * n - t ^ 2) (hd1 : 1 ≤ d)
    (hI : IndexTwo t n) {k₀ : ℕ} (hsq : ∀ x : R, π ^ k₀ ∣ x - 1 → IsSquare x) :
    localDensityForm (eisForm t n) (eisForm t n) π = 4 * (q R : ℝ) ^ d := by
  set k := 2 * d + 1 + k₀ with hk
  have hdet : (eisForm t n).hessian.det = 4 * n - t ^ 2 := det_hessian_eisForm t n
  rw [localDensityForm_self_eq (eisForm t n) π hπ d (hdet ▸ hd) (hdet ▸ hd') k (by omega)]
  have hcount : repCountForm (eisForm t n) (eisForm t n) π k = 2 * q R ^ k * (2 * q R ^ d) := by
    unfold repCountForm
    rw [map_eisForm, card_aut_eq_mul,
      card_normOne_level hπ ht hn hw hI (by omega) (fun x hx => hsq x ((pow_dvd_pow π (by omega)).trans hx)),
      card_stab_level hπ ht hn hw hd hd' (by omega) hd1]
  rw [hcount]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  push_cast
  rw [show k * (2 * (2 - 1) / 2) = k by norm_num]
  field_simp
  ring

end Density

end QuadFormsKB.Hanke2005.R2Ram
