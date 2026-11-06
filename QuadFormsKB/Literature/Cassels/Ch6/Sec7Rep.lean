/-
# Cassels, Chapter 6, §7: a value represented at every place, for Theorem 1.3

The choice of $t \in \mathbb Q^\times$ represented by every local form $f_v = \langle\alpha_v\rangle$ in the proof of
Theorem 1.3 (`exists_form_of_local`, `Ch6/Sec7.lean`; see the module docstring there): `exists_rep_two` ($n = 2$, by
prescribed Hilbert symbols) and `exists_rep_three_le` ($n \ge 3$, by approximation in finitely many square classes).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols

namespace QuadFormsKB.Cassels.Ch6

open QuadForm

variable {m n : ℕ}

/-- The Hilbert symbol at `v` depends only on the square class of its first argument. -/
theorem hilbert_congr_left (v : RatPlace) (d₁ d₂ y : ℚ)
    (h : v.atPlace fun K _ _ => SameSquareClass K d₁ d₂) : v.hilbert d₁ y = v.hilbert d₂ y := by
  cases v with
  | infinite =>
    obtain ⟨t, ht, e⟩ := h
    simp only [RatPlace.hilbert]
    rw [show ((d₁ : ℚ) : ℝ) = t ^ 2 * (d₂ : ℝ) by simpa using e]
    exact PadicClass.hs_sq_left _ _ _ ht
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    obtain ⟨t, ht, e⟩ := h
    simp only [RatPlace.hilbert]
    rw [show ((d₁ : ℚ) : ℚ_[p.1]) = t ^ 2 * (d₂ : ℚ_[p.1]) by simpa using e]
    exact PadicClass.hs_sq_left _ _ _ ht

/-- Square classes are preserved by negation. -/
theorem atPlace_sameSquareClass_neg (v : RatPlace) (d₁ d₂ : ℚ)
    (h : v.atPlace fun K _ _ => SameSquareClass K d₁ d₂) :
    v.atPlace fun K _ _ => SameSquareClass K (-d₁) (-d₂) := by
  cases v with
  | infinite =>
    obtain ⟨t, ht, e⟩ := h
    exact ⟨t, ht, by rw [map_neg, map_neg, e]; ring⟩
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    obtain ⟨t, ht, e⟩ := h
    exact ⟨t, ht, by rw [map_neg, map_neg, e]; ring⟩

/-- A diagonal form represents `c` if `c = a i * y ^ 2` for some coefficient `a i`. -/
theorem representsIn_diag_of_single (K : Type) [Field K] [CharZero K] (a : Fin n → ℚ) (i : Fin n)
    (y : K) (c : ℚ) (h : algebraMap ℚ K c = algebraMap ℚ K (a i) * y ^ 2) :
    (diag a).RepresentsIn K c := by
  refine ⟨Pi.single i y, ?_⟩
  rw [evalIn_diag, Finset.sum_eq_single i]
  · simp [h]
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

/-- Over `ℝ`, `diag a` represents `c` if `c * a i > 0` for some `i`. -/
theorem representsIn_real_of_pos (a : Fin n → ℚ) (i : Fin n) (c : ℚ) (h : 0 < c * a i) :
    (diag a).RepresentsIn ℝ c := by
  have h' : (0 : ℝ) < c * a i := by exact_mod_cast h
  have hai : (a i : ℝ) ≠ 0 := by
    intro h0; rw [h0] at h'; simp at h'
  refine representsIn_diag_of_single ℝ a i (Real.sqrt (c / a i)) c ?_
  have : (0 : ℝ) ≤ c / a i := by
    have : (c : ℝ) / a i = (c * a i) / (a i) ^ 2 := by field_simp
    rw [this]; positivity
  simp only [eq_ratCast]
  rw [Real.sq_sqrt this]; field_simp

/-- Binary real representation criterion in terms of the Hilbert symbol at `∞`. -/
theorem exists_pos_of_hilbert_infinite (a b t : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (h : RatPlace.infinite.hilbert t (-(a * b)) = RatPlace.infinite.hilbert a b) :
    0 < t * a ∨ 0 < t * b := by
  rw [hilbert_infinite_eq _ _ ht (neg_ne_zero.mpr (mul_ne_zero ha hb)),
    hilbert_infinite_eq _ _ ha hb] at h
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  split_ifs at h with h1 h2 h2 <;> try (norm_num at h; done)
  · obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    nlinarith
  · rcases lt_or_gt_of_ne ht with ht' | ht' <;> rcases lt_or_gt_of_ne ha with ha' | ha' <;>
      rcases lt_or_gt_of_ne hb with hb' | hb' <;>
      first
      | nlinarith
      | (exfalso; apply h1; constructor <;> nlinarith)
      | (exfalso; apply h2; constructor <;> nlinarith)

/-- Key identity: `(-d₀, α₀)_v = (α₀, α₁)_v` when `α₀ α₁` has the square class of `d₀`. -/
theorem hilbert_neg_det_eq (v : RatPlace) (d₀ a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdet : v.atPlace fun K _ _ => SameSquareClass K (a * b) d₀) :
    v.hilbert (-d₀) a = v.hilbert a b := by
  have h1 := hilbert_congr_left v (-(a * b)) (-d₀) a (atPlace_sameSquareClass_neg v _ _ hdet)
  rw [← h1, RatPlace.hilbert_comm, show -(a * b) = (-a) * b by ring,
    RatPlace.hilbert_mul_right v a (-a) b ha (neg_ne_zero.mpr ha) hb, RatPlace.hilbert_self_neg,
    one_mul]

/-- At an odd `p`, a unit `d₀` and trivial Hasse invariant make a form of rank at least `3` universal. -/
theorem represents_unit_case (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (d₀ : ℚ) (hd₀ : d₀ ≠ 0)
    (hv : padicValRat p d₀ = 0) (α : Fin (m + 3) → ℚ) (hα : ∀ i, α i ≠ 0)
    (hd : SameSquareClass ℚ_[p] (∏ i, α i) d₀) (hh : hasseInvariant ℚ_[p] α = 1) (x : ℚ) :
    (diag α).RepresentsIn ℚ_[p] x := by
  let β : Fin (m + 3) → ℚ := Fin.cons d₀ (fun _ => 1)
  have hβ : ∀ i, β i ≠ 0 := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [β] using hd₀
    · simp [β]
  have hβprod : ∏ i, β i = d₀ := by simp [β, Fin.prod_univ_succ]
  have hβh : hasseInvariant ℚ_[p] β = 1 := by
    unfold hasseInvariant
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have hj : β j = 1 := by
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.ne_zero_of_lt hij)
        simp [β]
      rw [hj]; simp [hilbertSymbol_one_right]
    · rfl
  have hiso : (diag α).IsometricIn ℚ_[p] (diag β) := by
    rw [isometric_padic_iff_invariants p α β hα hβ, hβprod, hh, hβh]
    exact ⟨hd, rfl⟩
  refine representsIn_of_isometricIn _ hiso ?_
  have hne : -1 / d₀ ≠ 0 := div_ne_zero (by norm_num) hd₀
  have h3 : (diag ![d₀, 1, 1]).IsotropicIn ℚ_[p] := by
    rw [HM3.isotropic_diag_three_iff _ _ _ _ hd₀ one_ne_zero one_ne_zero]
    have hu : padicValRat p (-1 / d₀) = 0 := by
      rw [padicValRat.div (by norm_num) hd₀, hv]; simp
    have := HilbertLocal.hilbert_eq_one_of_padicValRat hp2 (-1 / d₀) (-1 / d₀) hne hne hu hu
    simpa [RatPlace.hilbert] using this
  obtain ⟨z, hz0, hz⟩ := h3
  rw [evalIn_diag, Fin.sum_univ_three] at hz
  have hiso' : (diag (fun i => algebraMap ℚ ℚ_[p] (β i))).IsotropicIn ℚ_[p] := by
    rw [PadicClass.isotropicIn_diag_iff]
    refine ⟨Fin.cons (z 0) (Fin.cons (z 1) (Fin.cons (z 2) (fun _ => 0))), ?_, ?_⟩
    · intro h
      apply hz0
      have h0 := congrFun h 0
      have h1 := congrFun h (Fin.succ 0)
      have h2 := congrFun h (Fin.succ (Fin.succ 0))
      simp only [Fin.cons_zero, Fin.cons_succ] at h0 h1 h2
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    · simp [β, Fin.sum_univ_succ]
      simp at hz
      linear_combination hz
  rw [PadicClass.representsIn_rat_iff]
  exact PadicClass.representsIn_of_isotropic (PadicClass.cast_ne_zero p hβ) hiso' _

/-- **Cassels, Ch. 6, §7, p. 85** (the case $n = 2$ of the proof of Theorem 1.3): there is $t \in \mathbb Q^\times$
represented by every binary $f_v = \langle\alpha_{v,0}, \alpha_{v,1}\rangle$. -/
@[kb "cassels1978" "Ch. 6, §7, pp. 85–86 (proof of Thm. 1.3, n = 2)"]
theorem exists_rep_two (d₀ : ℚ) (hd₀ : d₀ ≠ 0) (α : RatPlace → Fin 2 → ℚ) (hα : ∀ v i, α v i ≠ 0)
    (hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) d₀)
    (hfin : {v : RatPlace | v.hasseCassels (α v) = -1}.Finite)
    (heven : Even {v : RatPlace | v.hasseCassels (α v) = -1}.ncard) :
    ∃ t : ℚ, t ≠ 0 ∧ ∀ v : RatPlace, v.atPlace fun K _ _ => (diag (α v)).RepresentsIn K t := by
  have hc2 : ∀ v : RatPlace, v.hasseCassels (α v) = v.hilbert (α v 0) (α v 1) := by
    intro v; simp [RatPlace.hasseCassels, Fin.prod_univ_two]
  have hdet2 : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (α v 0 * α v 1) d₀ := by
    intro v; simpa [Fin.prod_univ_two] using hdet v
  have key : ∀ v : RatPlace, v.hilbert (-d₀) (α v 0) = v.hasseCassels (α v) := fun v => by
    rw [hc2]; exact hilbert_neg_det_eq v d₀ _ _ (hα v 0) (hα v 1) (hdet2 v)
  obtain ⟨t, ht, hH⟩ := Prescribed.exists_rat_prescribed_hilbert (ι := Unit) (fun _ => -d₀)
    (fun _ => neg_ne_zero.mpr hd₀) (fun _ v => v.hasseCassels (α v))
    (fun _ v => by rw [hc2]; exact RatPlace.hilbert_pm v _ _)
    (by simpa using hfin) (fun _ => by simpa using heven) (by
    intro v
    cases v with
    | infinite =>
      refine ⟨((α .infinite 0 : ℚ) : ℝ), by simpa using hα _ 0, fun _ => ?_⟩
      have := key .infinite
      simpa [RatPlace.hilbert] using this
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      refine ⟨((α (.finite p) 0 : ℚ) : ℚ_[p.1]), by simpa using hα _ 0, fun _ => ?_⟩
      have := key (.finite p)
      simpa [RatPlace.hilbert] using this)
  refine ⟨t, ht, fun v => ?_⟩
  have hv : v.hilbert t (-∏ i, α v i) = v.hasseCassels (α v) := by
    rw [RatPlace.hilbert_comm, hilbert_congr_left v _ (-d₀) t
      (atPlace_sameSquareClass_neg v _ _ (hdet v))]
    exact hH () v
  cases v with
  | infinite =>
    have h2 : RatPlace.infinite.hilbert t (-(α .infinite 0 * α .infinite 1)) =
        RatPlace.infinite.hilbert (α .infinite 0) (α .infinite 1) := by
      rw [← hc2, ← hv]; simp [Fin.prod_univ_two]
    rcases exists_pos_of_hilbert_infinite _ _ t (hα _ 0) (hα _ 1) ht h2 with h | h
    · exact representsIn_real_of_pos _ 0 t h
    · exact representsIn_real_of_pos _ 1 t h
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    show (diag (α (.finite p))).RepresentsIn ℚ_[p.1] t
    rw [represents_padic_two_iff p.1 _ (hα _) t ht]
    rw [← RatPlace.hasseSerre_finite, ← RatPlace.hasseCassels_eq_hasseSerre]
    simpa [RatPlace.hilbert] using hv

/-- **Cassels, Ch. 6, §7, p. 86** (the choice of $t$ in the proof of Theorem 1.3 for $n \ge 3$): there is
$t \in \mathbb Q^\times$ represented by every $f_v = \langle\alpha_v\rangle$. -/
@[kb "cassels1978" "Ch. 6, §7, p. 86 (proof of Thm. 1.3, n ≥ 3: the choice of t)"]
theorem exists_rep_three_le (d₀ : ℚ) (hd₀ : d₀ ≠ 0) (α : RatPlace → Fin (m + 3) → ℚ) (hα : ∀ v i, α v i ≠ 0)
    (hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) d₀)
    (hfin : {v : RatPlace | v.hasseCassels (α v) = -1}.Finite) :
    ∃ t : ℚ, t ≠ 0 ∧ ∀ v : RatPlace, v.atPlace fun K _ _ => (diag (α v)).RepresentsIn K t := by
  classical
  set N : ℕ := d₀.num.natAbs * d₀.den with hN
  have hN0 : N ≠ 0 := mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hd₀)) d₀.den_nz
  let S : Set Nat.Primes := {p | (p : ℕ) = 2 ∨ (p : ℕ) ∣ N ∨
    (RatPlace.finite p).hasseCassels (α (.finite p)) = -1}
  have hS : S.Finite := by
    have h1 : {p : Nat.Primes | (p : ℕ) ∣ N}.Finite :=
      ((Nat.divisors N).finite_toSet.preimage Subtype.val_injective.injOn).subset
        (fun p hp => by
          simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
          exact ⟨hp, hN0⟩)
    have h2 : {p : Nat.Primes | (p : ℕ) = 2}.Finite :=
      (Set.finite_singleton (⟨2, Nat.prime_two⟩ : Nat.Primes)).subset (fun p hp => Subtype.ext hp)
    have h3 : {p : Nat.Primes | (RatPlace.finite p).hasseCassels (α (.finite p)) = -1}.Finite :=
      hfin.preimage (fun a _ b _ h => RatPlace.finite.inj h)
    exact (h2.union (h1.union h3)).subset (fun p hp => by
      rcases hp with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  obtain ⟨x, hx0, hxs, hxT⟩ := Prescribed.exists_rat_approx_sq_classes hS.toFinset
    (fun p => α (.finite p) 0) (fun p _ => hα _ 0)
    (if 0 < α .infinite 0 then 1 else -1) (by split_ifs <;> simp)
  refine ⟨x, hx0, fun v => ?_⟩
  cases v with
  | infinite =>
    refine representsIn_real_of_pos _ 0 x ?_
    have ha := hα .infinite 0
    split_ifs at hxs with hpos
    · have : 0 < x := hxs.mpr rfl
      exact mul_pos this hpos
    · have hneg : α .infinite 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) ha
      have : ¬ 0 < x := fun h => by simpa using hxs.mp h
      exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.mp this) hx0) hneg
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    by_cases hpT : p ∈ hS.toFinset
    · obtain ⟨r, hr⟩ := hxT p hpT
      have hq : ((α (.finite p) 0 : ℚ) : ℚ_[p.1]) ≠ 0 := by simpa using hα (.finite p) 0
      refine representsIn_diag_of_single ℚ_[p.1] (α (.finite p)) 0 r x ?_
      rw [div_eq_iff hq] at hr
      simp only [eq_ratCast]
      rw [hr]; ring
    · have hpS : p ∉ S := by simpa using hpT
      simp only [S, Set.mem_ofPred_eq, not_or] at hpS
      obtain ⟨hp2, hpN, hc⟩ := hpS
      have hv : padicValRat p.1 d₀ = 0 := by
        have h1 : ¬ p.1 ∣ d₀.num.natAbs := fun h => hpN (h.mul_right _)
        have h2 : ¬ p.1 ∣ d₀.den := fun h => hpN (h.mul_left _)
        simp [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd h1,
          padicValNat.eq_zero_of_not_dvd h2]
      have hh : hasseInvariant ℚ_[p.1] (α (.finite p)) = 1 := by
        have e : hasseInvariant ℚ_[p.1] (α (.finite p)) =
            (RatPlace.finite p).hasseCassels (α (.finite p)) := by
          rw [RatPlace.hasseCassels_eq_hasseSerre, RatPlace.hasseSerre_finite]
        have hpm := PadicClass.hasseVec_pm (fun i => algebraMap ℚ ℚ_[p.1] (α (.finite p) i))
        rw [← PadicClass.hasseInvariant_eq_hasseVec] at hpm
        rcases hpm with h | h
        · exact h
        · exact absurd (e ▸ h) hc
      exact represents_unit_case p.1 hp2 d₀ hd₀ hv _ (hα _)
        (hdet (.finite p)) hh x

end QuadFormsKB.Cassels.Ch6
