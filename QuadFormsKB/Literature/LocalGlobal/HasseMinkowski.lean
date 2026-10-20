/-
# Hasse–Minkowski over ℚ and its local ingredients (Serre, *A Course in Arithmetic*, III–IV)

Everything is stated for `RatQF` (Gram-matrix model) and the places `RatPlace` of ℚ.
The number-field version should keep these names and this shape, with ℚ replaced
by a number field and `RatPlace` by its places.
-/
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiFour
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree
import QuadFormsKB.Literature.LocalGlobal.RankFive
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

namespace QuadFormsKB

open RatPlace

variable {n : ℕ}

/-! ### Local results -/

/-- A rational number is a square iff it is a square in `ℝ` and in every `ℚ_p`. -/
@[kb "serre1973" "Ch. IV, §3.2"]
theorem isSquare_iff_everywhere (a : ℚ) :
    IsSquare a ↔ Everywhere fun K _ _ => IsSquare (algebraMap ℚ K a) := by
  constructor
  · rintro h (_ | p) <;> exact h.map _
  · intro h
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    have hpos : 0 ≤ a := by
      obtain ⟨r, hr⟩ := h .infinite
      have : (a : ℝ) = r * r := by simpa using hr
      have : (0:ℝ) ≤ a := by rw [this]; exact mul_self_nonneg r
      exact_mod_cast this
    have hev : ∀ p : ℕ, p.Prime → Even (padicValRat p a) := by
      intro p hp
      have := Fact.mk hp
      obtain ⟨x, hx⟩ := h (.finite ⟨p, hp⟩)
      have hx' : (a : ℚ_[p]) = x * x := by simpa using hx
      have hx0 : x ≠ 0 := by
        rintro rfl; simp at hx'; exact ha hx'
      have := congrArg Padic.valuation hx'
      rw [Padic.valuation_ratCast, Padic.valuation_mul hx0 hx0] at this
      exact ⟨_, this⟩
    rw [Rat.isSquare_iff]
    have hnum0 : 0 ≤ a.num := Rat.num_nonneg.mpr hpos
    have key : ∀ p : ℕ, p.Prime → Even (padicValNat p a.num.natAbs) ∧ Even (padicValNat p a.den) := by
      intro p hp
      have := Fact.mk hp
      have e := hev p hp
      rw [padicValRat, padicValInt] at e
      by_cases hd : p ∣ a.den
      · have hn : ¬ p ∣ a.num.natAbs := by
          intro hn
          exact hp.ne_one (Nat.eq_one_of_dvd_coprimes a.reduced hn hd)
        rw [padicValNat.eq_zero_of_not_dvd hn] at e ⊢
        refine ⟨⟨0, rfl⟩, ?_⟩
        simpa using e
      · rw [padicValNat.eq_zero_of_not_dvd hd] at e ⊢
        refine ⟨?_, ⟨0, rfl⟩⟩
        simpa using e
    constructor
    · rw [← Int.natAbs_of_nonneg hnum0]
      have : IsSquare a.num.natAbs := by
        rw [Nat.isSquare_iff_even_factorization]
        intro p hp
        rw [Nat.factorization_def _ hp]
        exact (key p hp).1
      obtain ⟨r, hr⟩ := this
      exact ⟨r, by rw [hr]; push_cast; try ring⟩
    · have : IsSquare a.den := by
        rw [Nat.isSquare_iff_even_factorization]
        intro p hp
        rw [Nat.factorization_def _ hp]
        exact (key p hp).2
      obtain ⟨r, hr⟩ := this
      exact ⟨r, by rw [hr]⟩

/-- Over `ℚ_p`, every nondegenerate form in at least 5 variables is isotropic. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6"]
theorem isotropic_padic_of_five_le (p : ℕ) [Fact p.Prime] (Q : RatQF n) (hn : 5 ≤ n)
    (hQ : Q.Nondegenerate) : Q.IsotropicIn ℚ_[p] := by
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  rw [HM3.isotropicIn_iff_of_isometricIn ℚ_[p] (HM3.isometricIn_of_rat ℚ_[p] hiso)]
  by_cases hp2 : p = 2
  · subst hp2; exact RankFive.isotropic_two_adic_diag a ha hn
  · exact RankFive.isotropic_padic_diag_odd p hp2 a ha hn

/-- Local classification: nondegenerate diagonal forms of the same rank over `ℚ_p` are
isometric iff they have the same discriminant square class and Hasse invariant.

*Proof* (`isometric_padic_iff_invariants`, `Literature/LocalGlobal/PadicClassification.lean`).
"⇒": the discriminant changes by $\det(P)^2$, and `hasseInvariant_isometric`. "⇐": induction on
$n$; by the representation criterion (Serre IV §2.2, Thm. 6) the second form represents $a_0$,
so it is $\cong \langle a_0 \rangle \perp \beta$; the invariants of $\langle a_1, \dots \rangle$ and
$\beta$ agree, and induction applies. -/
@[kb "serre1973" "Ch. IV, §2.3, Thm. 7"]
theorem isometric_padic_iff (p : ℕ) [Fact p.Prime] (a b : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn ℚ_[p] (QuadForm.diag b) ↔
      SameSquareClass ℚ_[p] (∏ i, a i) (∏ i, b i) ∧
        hasseInvariant ℚ_[p] a = hasseInvariant ℚ_[p] b :=
  isometric_padic_iff_invariants p a b ha hb

/-! ### Hasse–Minkowski -/

/-- **Hasse–Minkowski**: a nondegenerate rational quadratic form is isotropic over ℚ iff it is
isotropic over `ℝ` and over every `ℚ_p`. -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8"]
theorem hasseMinkowski (Q : RatQF n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K := by
  by_cases hn : 5 ≤ n
  · have evdiag : ∀ (K : Type) [Field K] [CharZero K] {m : ℕ} (a : Fin m → ℚ) (x : Fin m → K), QuadForm.evalIn K (QuadForm.diag a) x = ∑ i, (a i : K) * x i ^ 2 := by
      intro K _ _ m a x
      simp only [QuadForm.evalIn, QuadForm.diag]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
      · simp
    have crt : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) → ∀ (m : ℕ → ℤ) (K : ℕ → ℕ), ∃ x : ℤ, ∀ p ∈ T, (p:ℤ)^(K p) ∣ x - m p := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _ m K; exact ⟨0, by simp⟩
      | insert q T hq ih =>
        intro hT m K
        obtain ⟨x, hx⟩ := ih (fun p hp => hT p (Finset.mem_insert_of_mem hp)) m K
        set M : ℤ := ∏ p ∈ T, (p:ℤ)^(K p) with hM
        have hcop : IsCoprime M ((q:ℤ)^(K q)) := by
          apply IsCoprime.prod_left
          intro p hp
          apply IsCoprime.pow
          rw [Int.isCoprime_iff_gcd_eq_one]
          have hp' := hT p (Finset.mem_insert_of_mem hp)
          have hq' := hT q (Finset.mem_insert_self q T)
          have hne : p ≠ q := fun h => hq (h ▸ hp)
          have := (Nat.coprime_primes hp' hq').mpr hne
          simpa [Int.gcd] using this
        obtain ⟨α, β, hαβ⟩ := hcop
        refine ⟨x + α * M * (m q - x), ?_⟩
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨β * (x - m p), by linear_combination -(x - m p) * hαβ⟩
        · have h1 := hx p hp
          have h2 : (p:ℤ)^(K p) ∣ M := Finset.dvd_prod_of_mem _ hp
          have : x + α * M * (m q - x) - m p = (x - m p) + M * (α * (m q - x)) := by ring
          rw [this]
          exact dvd_add h1 (dvd_mul_of_dvd_left h2 _)
    have wapprox : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) → ∀ (r : ℕ → ℚ) (N : ℕ), ∃ s : ℚ, ∀ p ∈ T, padicNorm p (s - r p) ≤ (p:ℚ)^(-(N:ℤ)) := by
      intro T hT r N
      set D : ℕ := ∏ p ∈ T, (r p).den with hD
      have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => (r p).den_nz
      have hdvd : ∀ p ∈ T, (r p).den ∣ D := fun p hp => Finset.dvd_prod_of_mem _ hp
      set m : ℕ → ℤ := fun p => (r p).num * ((D / (r p).den : ℕ) : ℤ) with hmdef
      have hm : ∀ p ∈ T, (m p : ℚ) = r p * D := by
        intro p hp
        obtain ⟨k, hk⟩ := hdvd p hp
        have hk' : D / (r p).den = k := by rw [hk]; exact Nat.mul_div_cancel_left k (r p).den_pos
        simp only [hmdef, hk']
        push_cast
        rw [hk]; push_cast
        rw [← Rat.mul_den_eq_num]; ring
      obtain ⟨x, hx⟩ := crt T hT m (fun p => N + padicValNat p D)
      refine ⟨(x : ℚ) / D, fun p hp => ?_⟩
      have := Fact.mk (hT p hp)
      have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
      have e : (x : ℚ) / D - r p = ((x - m p : ℤ) : ℚ) / D := by
        push_cast; rw [hm p hp]; field_simp
      rw [e, padicNorm.div]
      have h1 := (padicNorm.dvd_iff_norm_le (p := p) (n := N + padicValNat p D) (z := x - m p)).mp (by exact_mod_cast hx p hp)
      have h2 : padicNorm p (D : ℚ) = (p:ℚ)^(-(padicValNat p D : ℤ)) := by
        rw [padicNorm.eq_zpow_of_nonzero hDq, padicValRat.of_nat]
      have hp0 : (0:ℚ) < p := by exact_mod_cast (hT p hp).pos
      rw [h2, div_le_iff₀ (zpow_pos hp0 _), ← zpow_add₀ hp0.ne']
      convert h1 using 2
      push_cast; ring
    have sqnear : ∀ (p : ℕ) [Fact p.Prime] (z : ℚ_[p]), ‖z - 1‖ < ‖(2:ℚ_[p])‖^2 → IsSquare z := by
      intro p _ z hz
      have h2 : ‖(2:ℚ_[p])‖ ≤ 1 := by
        have := Padic.norm_int_le_one (p := p) 2
        simpa using this
      have hz1 : ‖z‖ ≤ 1 := by
        have : z = (z - 1) + 1 := by ring
        rw [this]
        refine (Padic.nonarchimedean _ _).trans (max_le ?_ (by simp))
        nlinarith [norm_nonneg (2:ℚ_[p])]
      set z' : ℤ_[p] := ⟨z, hz1⟩
      have hz' : (z' : ℚ_[p]) = z := rfl
      obtain ⟨w, hw, -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C z' : Polynomial ℤ_[p])) (a := 1) (by
        simp
        rw [PadicInt.norm_def, PadicInt.norm_def]
        have : ((1 - z' : ℤ_[p]) : ℚ_[p]) = -(z - 1) := by push_cast; rw [hz']; ring
        rw [this, norm_neg]
        have h11 : ((1 + 1 : ℤ_[p]) : ℚ_[p]) = 2 := by push_cast; norm_num
        rw [h11]; exact hz)
      refine ⟨(w : ℚ_[p]), ?_⟩
      simp at hw
      have : (w : ℚ_[p]) ^ 2 = z := by
        have := congrArg (fun u : ℤ_[p] => (u : ℚ_[p])) hw
        simp only [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_zero, hz'] at this
        linear_combination this
      rw [← this]; ring
    have perprime : ∀ (p : ℕ) [Fact p.Prime] (b3 b4 : ℚ) (sp tp : ℚ_[p]), (b3:ℚ_[p]) * sp^2 + b4 * tp^2 ≠ 0 → ∃ r1 r2 : ℚ, ∃ N : ℕ, ∀ s t : ℚ, padicNorm p (s - r1) ≤ (p:ℚ)^(-(N:ℤ)) → padicNorm p (t - r2) ≤ (p:ℚ)^(-(N:ℤ)) → ((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) ≠ 0 ∧ IsSquare (((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) / ((b3:ℚ_[p]) * sp^2 + b4 * tp^2)) := by
      intro p _ b3 b4 sp tp hyp
      set yp := (b3:ℚ_[p]) * sp^2 + b4 * tp^2 with hypdef
      have hF : Continuous (fun x : ℚ_[p] × ℚ_[p] => (b3:ℚ_[p]) * x.1^2 + b4 * x.2^2) := by fun_prop
      have h2pos : 0 < ‖(2:ℚ_[p])‖ := norm_pos_iff.mpr two_ne_zero
      have h2le : ‖(2:ℚ_[p])‖ ≤ 1 := by
        have := Padic.norm_int_le_one (p := p) 2
        simpa using this
      have h2sq : ‖(2:ℚ_[p])‖^2 ≤ 1 := by nlinarith
      have hε : 0 < ‖yp‖ * ‖(2:ℚ_[p])‖^2 := by
        have := norm_pos_iff.mpr hyp
        positivity
      obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hF (sp, tp) _ hε
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hδ) (show (1:ℝ)/p < 1 by rw [div_lt_one (by linarith)]; exact hp1)
      obtain ⟨r1, hr1⟩ := Padic.rat_dense p sp (half_pos hδ)
      obtain ⟨r2, hr2⟩ := Padic.rat_dense p tp (half_pos hδ)
      refine ⟨r1, r2, N, fun s t hs ht => ?_⟩
      have close : ∀ (u r : ℚ) (x : ℚ_[p]), padicNorm p (u - r) ≤ (p:ℚ)^(-(N:ℤ)) → ‖x - r‖ < δ/2 → ‖(u:ℚ_[p]) - x‖ < δ := by
        intro u r x hu hx
        have e1 : ‖(u:ℚ_[p]) - r‖ ≤ (1/p:ℝ)^N := by
          have : ((u:ℚ_[p]) - r) = ((u - r : ℚ) : ℚ_[p]) := by push_cast; ring
          rw [this, Padic.eq_padicNorm]
          have := (Rat.cast_le (K := ℝ)).mpr hu
          convert this using 1
          push_cast
          rw [one_div, inv_pow, zpow_neg, zpow_natCast]
        have : (u:ℚ_[p]) - x = ((u:ℚ_[p]) - r) + (r - x) := by ring
        rw [this]
        calc _ ≤ ‖(u:ℚ_[p]) - r‖ + ‖(r:ℚ_[p]) - x‖ := norm_add_le _ _
          _ < δ/2 + δ/2 := by
            rw [norm_sub_rev (r:ℚ_[p]) x]; linarith
          _ = δ := by ring
      have hd : dist ((s:ℚ_[p]), (t:ℚ_[p])) (sp, tp) < δ := by
        rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
        exact ⟨close s r1 sp hs hr1, close t r2 tp ht hr2⟩
      have hb := hball _ hd
      rw [dist_eq_norm] at hb
      have ey : ((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) = (b3:ℚ_[p]) * (s:ℚ_[p])^2 + b4 * (t:ℚ_[p])^2 := by push_cast; ring
      rw [ey]
      set y := (b3:ℚ_[p]) * (s:ℚ_[p])^2 + b4 * (t:ℚ_[p])^2
      change ‖y - yp‖ < _ at hb
      have hyp' : 0 < ‖yp‖ := norm_pos_iff.mpr hyp
      constructor
      · intro hy0
        rw [hy0, zero_sub, norm_neg] at hb
        nlinarith
      · apply sqnear
        have : y / yp - 1 = (y - yp) / yp := by field_simp
        rw [this, norm_div, div_lt_iff₀ hyp']
        linarith
    have loctarget : ∀ (K : Type) [Field K] [CharZero K] (b : Fin 5 → ℚ), (∀ i, b i ≠ 0) → QuadForm.IsotropicIn K (QuadForm.diag b) → ∃ sp tp : K, (b 3 : K) * sp^2 + b 4 * tp^2 ≠ 0 ∧ ∃ z0 z1 z2 w : K, ¬(z0 = 0 ∧ z1 = 0 ∧ z2 = 0 ∧ w = 0) ∧ (b 0 : K) * z0^2 + b 1 * z1^2 + b 2 * z2^2 + ((b 3 : K) * sp^2 + b 4 * tp^2) * w^2 = 0 := by
      intro K _ _ b hb ⟨z, hz0, hz⟩
      rw [evdiag, Fin.sum_univ_five] at hz
      have hb' : ∀ i, (b i : K) ≠ 0 := fun i => by exact_mod_cast hb i
      by_cases h1 : (b 3 : K) * z 3^2 + b 4 * z 4^2 = 0
      · by_cases h2 : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0
        · obtain ⟨e0, e1, e2⟩ := h2
          have h3 : z 3 ≠ 0 := by
            intro h3
            apply hz0
            have : (b 4 : K) * z 4 ^ 2 = 0 := by rw [h3] at h1; simpa using h1
            have h4 : z 4 = 0 := by simpa [hb' 4] using this
            funext i; fin_cases i <;> simp [e0, e1, e2, h3, h4]
          set r : K := -(b 0 : K) / ((b 3 : K) * z 3 ^ 2)
          have hr : (b 3 : K) * z 3 ^ 2 * r = -(b 0) := by
            simp only [r]; field_simp [hb' 3, h3]
          have hy : (b 3 : K) * (z 3 * ((r+1)/2))^2 + b 4 * (z 4 * ((r-1)/2))^2 = -(b 0) := by
            linear_combination ((r-1)^2/4) * h1 + hr
          refine ⟨z 3 * ((r+1)/2), z 4 * ((r-1)/2), ?_, 1, 0, 0, 1, by simp, ?_⟩
          · rw [hy]; exact neg_ne_zero.mpr (hb' 0)
          · rw [hy]; ring
        · refine ⟨1, 0, by simpa using hb' 3, z 0, z 1, z 2, 0, by tauto, ?_⟩
          linear_combination hz - h1
      · refine ⟨z 3, z 4, h1, z 0, z 1, z 2, 1, by simp, ?_⟩
        linear_combination hz
    have core5 : ∀ b : Fin 5 → ℚ, (∀ i, b i ≠ 0) → 0 < b 0 → b 1 < 0 → QuadForm.IsotropicIn ℚ (QuadForm.diag b) := by
      intro b hb hb0 hb1
      set L : ℕ := 2 * ((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den) with hLdef
      have hL : L ≠ 0 := by simp [hLdef, hb]
      set T := L.primeFactors
      have hT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
      have h2T : 2 ∈ T := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ⟨((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩, hL⟩
      have hf0 : (b 0).num.natAbs * (b 0).den ∣ L := ⟨2 * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩
      have hf1 : (b 1).num.natAbs * (b 1).den ∣ L := ⟨2 * ((b 0).num.natAbs * (b 0).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩
      have hf2 : (b 2).num.natAbs * (b 2).den ∣ L := ⟨2 * ((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den), by simp only [hLdef]; ring⟩
      have hv : ∀ p, p.Prime → p ∉ T → ∀ q : ℚ, q.num.natAbs * q.den ∣ L → padicValRat p q = 0 := by
        intro p hp hpT q hq
        have hnd : ¬ p ∣ L := fun h => hpT (Nat.mem_primeFactors.mpr ⟨hp, h, hL⟩)
        have key : ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
          constructor <;> intro h <;> apply hnd
          · exact (h.trans (dvd_mul_right _ _)).trans hq
          · exact (h.trans (dvd_mul_left _ _)).trans hq
        have := Fact.mk hp
        rw [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd key.1, padicValNat.eq_zero_of_not_dvd key.2]
        simp
      have hloc : ∀ p : ℕ, ∃ r1 r2 : ℚ, ∃ N : ℕ, ∀ (hp : p ∈ T) (s t : ℚ), padicNorm p (s - r1) ≤ (p:ℚ)^(-(N:ℤ)) → padicNorm p (t - r2) ≤ (p:ℚ)^(-(N:ℤ)) → b 3 * s^2 + b 4 * t^2 ≠ 0 ∧ RatPlace.atPlace (fun K _ _ => QuadForm.IsotropicIn K (QuadForm.diag ![b 0, b 1, b 2, b 3 * s^2 + b 4 * t^2])) (RatPlace.finite ⟨p, hT p hp⟩) := by
        intro p
        by_cases hp : p ∈ T
        · have := Fact.mk (hT p hp)
          have hiso : QuadForm.IsotropicIn ℚ_[p] (QuadForm.diag b) := by
            by_cases h2 : p = 2
            · subst h2; exact RankFive.isotropic_two_adic_diag b hb le_rfl
            · exact RankFive.isotropic_padic_diag_odd p h2 b hb le_rfl
          obtain ⟨sp, tp, hyp, z0, z1, z2, w, hz0, hz⟩ := loctarget ℚ_[p] b hb hiso
          obtain ⟨r1, r2, N, hgood⟩ := perprime p (b 3) (b 4) sp tp hyp
          refine ⟨r1, r2, N, fun _ s t hs ht => ?_⟩
          obtain ⟨hy0, c, hc⟩ := hgood s t hs ht
          refine ⟨fun h => hy0 (by rw [h]; simp), ?_⟩
          show QuadForm.IsotropicIn ℚ_[p] _
          have hc0 : c ≠ 0 := by
            rintro rfl; rw [mul_zero] at hc; exact div_ne_zero hy0 hyp hc
          have hyeq : ((b 3 * s^2 + b 4 * t^2 : ℚ) : ℚ_[p]) = ((b 3 : ℚ_[p]) * sp^2 + b 4 * tp^2) * (c * c) := by
            rw [← hc]; field_simp
          refine ⟨![z0, z1, z2, w / c], ?_, ?_⟩
          · intro h; apply hz0
            have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2; have e3 := congrFun h 3
            simp at e0 e1 e2 e3
            exact ⟨e0, e1, e2, by simpa [hc0] using e3⟩
          · rw [evdiag, Fin.sum_univ_four]
            show (b 0 : ℚ_[p]) * z0^2 + (b 1 : ℚ_[p]) * z1^2 + (b 2:ℚ_[p]) * z2^2 + ((b 3 * s^2 + b 4 * t^2 : ℚ) : ℚ_[p]) * (w/c)^2 = 0
            rw [hyeq]
            have hw : (c*c)*(w/c)^2 = w^2 := by field_simp
            linear_combination hz + ((b 3 : ℚ_[p]) * sp^2 + b 4 * tp^2) * hw
        · exact ⟨0, 0, 0, fun h => absurd h hp⟩
      choose r1 r2 N hgood using hloc
      obtain ⟨s, hs⟩ := wapprox T hT r1 (T.sup N)
      obtain ⟨t, ht⟩ := wapprox T hT r2 (T.sup N)
      have hmono : ∀ p ∈ T, (p:ℚ)^(-((T.sup N : ℕ):ℤ)) ≤ (p:ℚ)^(-(N p:ℤ)) := fun p hp =>
        zpow_le_zpow_right₀ (by exact_mod_cast (hT p hp).one_lt.le) (neg_le_neg (by exact_mod_cast Finset.le_sup hp))
      have hG : ∀ (p : ℕ) (hp : p ∈ T), _ := fun p hp => hgood p hp s t ((hs p hp).trans (hmono p hp)) ((ht p hp).trans (hmono p hp))
      set y := b 3 * s^2 + b 4 * t^2 with hydef
      have hy0 : y ≠ 0 := (hG 2 h2T).1
      have H := HM4.hasseMinkowski_diag_four (b 0) (b 1) (-b 2) (-y) (hb 0) (hb 1) (neg_ne_zero.mpr (hb 2)) (neg_ne_zero.mpr hy0)
      simp only [neg_neg] at H
      have hev : RatPlace.Everywhere fun K _ _ => QuadForm.IsotropicIn K (QuadForm.diag ![b 0, b 1, b 2, y]) := by
        intro v
        cases v with
        | infinite =>
          show QuadForm.IsotropicIn ℝ _
          refine ⟨![Real.sqrt (-b 1), Real.sqrt (b 0), 0, 0], ?_, ?_⟩
          · intro h; have := congrFun h 1; simp at this
            have := Real.sqrt_eq_zero'.mp this
            have : (0:ℝ) < b 0 := by exact_mod_cast hb0
            linarith
          · rw [evdiag, Fin.sum_univ_four]
            show (b 0 : ℝ) * Real.sqrt (-b 1)^2 + (b 1 : ℝ) * Real.sqrt (b 0)^2 + (b 2:ℝ) * 0^2 + (y : ℝ) * 0^2 = 0
            have h0 : (0:ℝ) ≤ b 0 := by exact_mod_cast hb0.le
            have h1 : (0:ℝ) ≤ -b 1 := by have h := (show (b 1 : ℝ) < 0 by exact_mod_cast hb1); linarith
            rw [Real.sq_sqrt h0, Real.sq_sqrt h1]; ring
        | finite p =>
          by_cases hp : (p:ℕ) ∈ T
          · exact (hG p hp).2
          · have := Fact.mk p.2
            show QuadForm.IsotropicIn ℚ_[p] _
            have hp2 : (p:ℕ) ≠ 2 := fun h => hp (h ▸ h2T)
            obtain ⟨z, hz0, hz⟩ := RankFive.isotropic_padic_unit_ternary p hp2 (b 0) (b 1) (b 2) (hb 0) (hb 1) (hb 2)
              (hv p p.2 hp _ hf0) (hv p p.2 hp _ hf1) (hv p p.2 hp _ hf2)
            refine ⟨![z 0, z 1, z 2, 0], ?_, ?_⟩
            · intro h; apply hz0
              have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
              simp at e0 e1 e2
              funext i; fin_cases i <;> simp [e0, e1, e2]
            · rw [evdiag, Fin.sum_univ_four]
              rw [evdiag, Fin.sum_univ_three] at hz
              show (b 0 : ℚ_[p]) * z 0^2 + (b 1 : ℚ_[p]) * z 1^2 + (b 2:ℚ_[p]) * z 2^2 + (y : ℚ_[p]) * 0^2 = 0
              simpa using hz
      obtain ⟨x, hx0, hx⟩ := H.mpr hev
      refine ⟨![x 0, x 1, x 2, x 3 * s, x 3 * t], ?_, ?_⟩
      · intro h; apply hx0
        have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
        have e3 := congrFun h 3; have e4 := congrFun h 4
        simp at e0 e1 e2 e3 e4
        have h3 : x 3 = 0 := by
          by_contra h3
          apply hy0
          have : y * x 3 ^ 2 = 0 := by
            rw [hydef, e3.resolve_left h3, e4.resolve_left h3]; ring
          simpa [h3] using this
        funext i; fin_cases i <;> simp [e0, e1, e2, h3]
      · rw [evdiag, Fin.sum_univ_five]
        rw [evdiag, Fin.sum_univ_four] at hx
        have hx' : b 0 * x 0^2 + b 1 * x 1^2 + b 2 * x 2^2 + y * x 3^2 = 0 := by simpa using hx
        show ((b 0 : ℚ) : ℚ) * x 0^2 + ((b 1 : ℚ) : ℚ) * x 1^2 + ((b 2 : ℚ) : ℚ) * x 2^2 + ((b 3 : ℚ) : ℚ) * (x 3 * s)^2 + ((b 4 : ℚ) : ℚ) * (x 3 * t)^2 = 0
        rw [hydef] at hx'
        try simp only [Rat.cast_id]
        linear_combination hx'
    constructor
    · intro h
      have key : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K Q := by
        intro K _ _
        obtain ⟨x, hx, hQx⟩ := h
        refine ⟨fun i => algebraMap ℚ K (x i), ?_, ?_⟩
        · intro h0
          apply hx
          funext i
          have := congrFun h0 i
          simpa using this
        · have : QuadForm.evalIn K Q (fun i => algebraMap ℚ K (x i)) = algebraMap ℚ K (QuadForm.evalIn ℚ Q x) := by
            simp only [QuadForm.evalIn, map_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
          rw [this, hQx, map_zero]
      intro v
      cases v with
      | infinite => exact key ℝ
      | finite p =>
        haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
        exact key ℚ_[p]
    · intro h
      obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
      have hiK : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K :=
        fun K _ _ => HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso)
      rw [hiK ℚ]
      have hR : (QuadForm.diag a).IsotropicIn ℝ := (hiK ℝ).mp (h .infinite)
      have hsign : ∀ (c : ℝ), (c = 1 ∨ c = -1) → ∃ i, 0 < c * a i := by
        intro c hc
        by_contra hcon
        push_neg at hcon
        obtain ⟨x, hx0, hx⟩ := hR
        rw [evdiag] at hx
        have hx' : ∑ i, c * ((a i : ℝ) * x i ^ 2) = 0 := by rw [← Finset.mul_sum, hx, mul_zero]
        have hle : ∀ i ∈ Finset.univ, c * ((a i : ℝ) * x i ^ 2) ≤ 0 := by
          intro i _
          have := hcon i
          rw [← mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _)
        have hall := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hx'
        apply hx0
        funext i
        have := hall i (Finset.mem_univ _)
        have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
        have ha0 : (a i : ℝ) ≠ 0 := by exact_mod_cast ha i
        simpa [hc0, ha0] using this
      obtain ⟨i, hi⟩ := hsign 1 (Or.inl rfl)
      obtain ⟨j, hj⟩ := hsign (-1) (Or.inr rfl)
      have hi' : 0 < a i := by
        have : (0:ℝ) < a i := by simpa using hi
        exact_mod_cast this
      have hj' : a j < 0 := by
        have : (a j : ℝ) < 0 := by simpa using hj
        exact_mod_cast this
      have hij : i ≠ j := by rintro rfl; linarith
      set i0 : Fin n := ⟨0, by omega⟩
      set i1 : Fin n := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
      set σ1 := Equiv.swap i0 i
      set j' := σ1 j
      have hj'0 : j' ≠ i0 := by
        intro e
        apply hij
        have : σ1 (σ1 j) = σ1 i0 := by rw [show σ1 j = j' from rfl, e]
        rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
        exact this.symm
      set σ2 := Equiv.swap i1 j'
      set a2 := (a ∘ σ1) ∘ σ2
      have e0 : a2 i0 = a i := by
        simp only [a2, Function.comp_apply, σ2, σ1]
        rw [Equiv.swap_apply_of_ne_of_ne h01 hj'0.symm, Equiv.swap_apply_left]
      have e1 : a2 i1 = a j := by
        simp only [a2, Function.comp_apply, σ2, Equiv.swap_apply_left, j', σ1, Equiv.swap_apply_self]
      rw [← RankFive.isotropicIn_diag_perm_iff ℚ a σ1, ← RankFive.isotropicIn_diag_perm_iff ℚ _ σ2]
      apply RankFive.isotropicIn_diag_of_prefix ℚ 5 hn a2
      apply core5
      · intro k; exact ha _
      · exact e0 ▸ hi'
      · exact e1 ▸ hj'
  · push_neg at hn
    interval_cases n
    · constructor
      · rintro ⟨x, hx, -⟩; exact absurd (Subsingleton.elim x 0) hx
      · intro h
        obtain ⟨x, hx, -⟩ : Q.IsotropicIn ℝ := h .infinite
        exact absurd (Subsingleton.elim x 0) hx
    · have hc : Q.coeff 0 0 ≠ 0 := by
        intro h; apply hQ
        simp [QuadForm.hessian, Matrix.det_unique, h]
      have gen : ∀ (K : Type) [Field K] [CharZero K], ¬ Q.IsotropicIn K := by
        intro K _ _ ⟨x, hx, hQx⟩
        have hx0 : x 0 ≠ 0 := by
          intro h0; apply hx; funext i; fin_cases i; simpa using h0
        simp [QuadForm.evalIn] at hQx
        tauto
      constructor
      · intro h; exact absurd h (gen ℚ)
      · intro h
        exact absurd (h .infinite) (gen ℝ)
    · have gen : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
          IsSquare (algebraMap ℚ K (Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1)) := by
        intro K _ _
        have hdet : Q.hessian.det = 4 * Q.coeff 0 0 * Q.coeff 1 1 - Q.coeff 0 1 ^ 2 := by
          have := Q.upper
          have h10 : Q.coeff 1 0 = 0 := this (by decide)
          simp [QuadForm.hessian, Matrix.det_fin_two, h10]
          ring
        have hD : (algebraMap ℚ K (Q.coeff 0 1)) ^ 2 - 4 * (algebraMap ℚ K (Q.coeff 0 0)) * (algebraMap ℚ K (Q.coeff 1 1)) ≠ 0 := by
          have h1 : Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1 ≠ 0 := by
            intro h; apply hQ; unfold QuadForm.Nondegenerate at *; rw [hdet]; linear_combination -h
          intro h; apply h1
          have : algebraMap ℚ K (Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1) = 0 := by
            simp only [map_sub, map_mul, map_pow, map_ofNat]; exact h
          exact (map_eq_zero_iff _ (algebraMap ℚ K).injective).mp this
        have hev : ∀ x : Fin 2 → K, QuadForm.evalIn K Q x = algebraMap ℚ K (Q.coeff 0 0) * x 0 * x 0 + algebraMap ℚ K (Q.coeff 0 1) * x 0 * x 1 + algebraMap ℚ K (Q.coeff 1 1) * x 1 * x 1 := by
          intro x
          simp [QuadForm.evalIn, Fin.sum_univ_two]
        have key : ∀ (a b c : K), b^2 - 4*a*c ≠ 0 → ((∃ x : Fin 2 → K, x ≠ 0 ∧ a * x 0 * x 0 + b * x 0 * x 1 + c * x 1 * x 1 = 0) ↔ IsSquare (b^2 - 4*a*c)) := by
          intro a b c hD
          constructor
          · rintro ⟨x, hx0, hx⟩
            by_cases ha : a = 0
            · subst ha; exact ⟨b, by ring⟩
            · have hy : x 1 ≠ 0 := by
                intro hy
                apply hx0
                have : a * (x 0 * x 0) = 0 := by rw [hy] at hx; linear_combination hx
                have h0 : x 0 = 0 := by simpa [ha] using this
                ext i; fin_cases i <;> simp [h0, hy]
              refine ⟨(2 * a * x 0 + b * x 1) / x 1, ?_⟩
              field_simp
              linear_combination (-4 * a) * hx
          · rintro ⟨s, hs⟩
            by_cases ha : a = 0
            · refine ⟨![1, 0], ?_, ?_⟩
              · intro h; have := congrFun h 0; simp at this
              · simp [ha]
            · refine ⟨![s - b, 2 * a], ?_, ?_⟩
              · intro h; have := congrFun h 1; simp at this; exact ha this
              · simp
                linear_combination (-a) * hs
        unfold QuadForm.IsotropicIn
        simp only [hev]
        rw [key _ _ _ hD]
        simp only [map_sub, map_mul, map_pow, map_ofNat]
      set D := Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1 with hDdef
      have hD0 : D ≠ 0 := by
        have hdet : Q.hessian.det = 4 * Q.coeff 0 0 * Q.coeff 1 1 - Q.coeff 0 1 ^ 2 := by
          have := Q.upper
          have h10 : Q.coeff 1 0 = 0 := this (by decide)
          simp [QuadForm.hessian, Matrix.det_fin_two, h10]
          ring
        intro h; apply hQ; unfold QuadForm.Nondegenerate at *; rw [hdet]; linear_combination -h
      have sqlem : ∀ (q : ℚ), 0 < q → (∀ p : ℕ, p.Prime → Even (padicValRat p q)) → IsSquare q := by
        intro q hq h
        have hnum : 0 < q.num := Rat.num_pos.mpr hq
        have hn0 : q.num.natAbs ≠ 0 := by omega
        have hd0 : q.den ≠ 0 := q.den_nz
        have hN : IsSquare (q.num.natAbs * q.den) := by
          apply Nat.isSquare_iff_even_factorization.mpr
          intro p hp
          have hev := h p hp
          have : Fact p.Prime := ⟨hp⟩
          rw [Nat.factorization_def _ hp, padicValNat.mul hn0 hd0]
          unfold padicValRat padicValInt at hev
          have h2 := Int.even_sub.mp hev
          have : Even ((padicValNat p q.num.natAbs : ℤ) + (padicValNat p q.den : ℤ)) := Int.even_add.mpr h2
          exact_mod_cast this
        obtain ⟨r, hr⟩ := hN
        refine ⟨(r : ℚ) / q.den, ?_⟩
        have key : (q.num : ℚ) * q.den = r * r := by
          have : ((q.num.natAbs : ℕ) : ℚ) = q.num := by
            rw [Nat.cast_natAbs]; simp [abs_of_pos hnum]
          rw [← this]; exact_mod_cast hr
        have hdq : (q.den : ℚ) ≠ 0 := by exact_mod_cast hd0
        calc q = (q.num : ℚ) * q.den / ((q.den : ℚ) * q.den) := by
                rw [mul_div_mul_right _ _ hdq]; exact (Rat.num_div_den q).symm
          _ = _ := by rw [key]; ring
      have padlem : ∀ (p : ℕ) [Fact p.Prime], IsSquare (algebraMap ℚ ℚ_[p] D) → Even (padicValRat p D) := by
        intro p _ h
        obtain ⟨y, hy⟩ := h
        simp only [eq_ratCast] at hy
        have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hD0 hy
        have := congrArg Padic.valuation hy
        rw [Padic.valuation_ratCast, Padic.valuation_mul hy0 hy0] at this
        exact ⟨_, this⟩
      constructor
      · intro h v
        have hs := (gen ℚ).mp h
        cases v with
        | infinite =>
          show Q.IsotropicIn ℝ
          rw [gen ℝ]; exact hs.map _
        | finite p =>
          have : Fact (p : ℕ).Prime := ⟨p.prop⟩
          show Q.IsotropicIn ℚ_[p]
          rw [gen ℚ_[p]]; exact hs.map _
      · intro h
        rw [gen ℚ]
        have hR : Q.IsotropicIn ℝ := h RatPlace.infinite
        rw [gen ℝ] at hR
        have hpos : 0 < D := by
          obtain ⟨y, hy⟩ := hR
          have : (0:ℝ) ≤ algebraMap ℚ ℝ D := by rw [hy]; exact mul_self_nonneg y
          have h0 : (0:ℝ) ≤ (D : ℝ) := by simpa using this
          have : (0:ℚ) ≤ D := by exact_mod_cast h0
          exact lt_of_le_of_ne this (Ne.symm hD0)
        have := sqlem D hpos (fun p hp => by
          have : Fact p.Prime := ⟨hp⟩
          have hP : Q.IsotropicIn ℚ_[p] := h (RatPlace.finite ⟨p, hp⟩)
          rw [gen ℚ_[p]] at hP
          exact padlem p hP)
        simpa using this
    · obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
      have hae : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
      have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
          hilbertSymbol K (algebraMap ℚ K (-a 1 / a 0)) (algebraMap ℚ K (-a 2 / a 0)) = 1 := by
        intro K _ _
        rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), hae,
          HM3.isotropic_diag_three_iff K _ _ _ (ha 0) (ha 1) (ha 2)]
        simp
      have hx : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 1)) (ha 0)
      have hy : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 2)) (ha 0)
      constructor
      · intro h
        have key2 : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K Q := by
          intro K _ _
          obtain ⟨x, hx, hQx⟩ := h
          refine ⟨fun i => algebraMap ℚ K (x i), ?_, ?_⟩
          · intro h0
            apply hx
            funext i
            have := congrFun h0 i
            simpa using this
          · have : QuadForm.evalIn K Q (fun i => algebraMap ℚ K (x i)) = algebraMap ℚ K (QuadForm.evalIn ℚ Q x) := by
              simp only [QuadForm.evalIn, map_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              split_ifs <;> simp
            rw [this, hQx, map_zero]
        intro v
        cases v with
        | infinite => exact key2 ℝ
        | finite p =>
          haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
          exact key2 ℚ_[p]
      · intro h
        rw [key ℚ]
        have := HM3.hilbert_rat_eq_one_of_everywhere _ _ hx hy (fun v => by
          have hv := h v
          cases v with
          | infinite =>
            have hv' : Q.IsotropicIn ℝ := hv
            rw [key ℝ] at hv'
            simpa [RatPlace.hilbert] using hv'
          | finite p =>
            haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
            have hv' : Q.IsotropicIn ℚ_[p] := hv
            rw [key ℚ_[p]] at hv'
            simpa [RatPlace.hilbert] using hv')
        simpa using this
    · obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
      have hae : a = ![a 0, a 1, -(-a 2), -(-a 3)] := by funext i; fin_cases i <;> simp
      have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
          (QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)]).IsotropicIn K := by
        intro K _ _
        rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), ← hae]
      have H := HM4.hasseMinkowski_diag_four (a 0) (a 1) (-a 2) (-a 3) (ha 0) (ha 1)
        (neg_ne_zero.mpr (ha 2)) (neg_ne_zero.mpr (ha 3))
      rw [key ℚ, H]
      constructor
      · intro h v
        have hv := h v
        cases v with
        | infinite => exact (key ℝ).mpr hv
        | finite p =>
          haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
          exact (key ℚ_[p]).mpr hv
      · intro h v
        have hv := h v
        cases v with
        | infinite => exact (key ℝ).mp hv
        | finite p =>
          haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
          exact (key ℚ_[p]).mp hv

/-- Hasse–Minkowski, `n = 2`: reduces to `-det` being a square, via `isSquare_iff_everywhere`. -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8 (n = 2)"]
theorem hasseMinkowski_two (Q : RatQF 2) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K := by
  have gen : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      IsSquare (algebraMap ℚ K (Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1)) := by
    intro K _ _
    have hdet : Q.hessian.det = 4 * Q.coeff 0 0 * Q.coeff 1 1 - Q.coeff 0 1 ^ 2 := by
      have := Q.upper
      have h10 : Q.coeff 1 0 = 0 := this (by decide)
      simp [QuadForm.hessian, Matrix.det_fin_two, h10]
      ring
    have hD : (algebraMap ℚ K (Q.coeff 0 1)) ^ 2 - 4 * (algebraMap ℚ K (Q.coeff 0 0)) * (algebraMap ℚ K (Q.coeff 1 1)) ≠ 0 := by
      have h1 : Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1 ≠ 0 := by
        intro h; apply hQ; unfold QuadForm.Nondegenerate at *; rw [hdet]; linear_combination -h
      intro h; apply h1
      have : algebraMap ℚ K (Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1) = 0 := by
        simp only [map_sub, map_mul, map_pow, map_ofNat]; exact h
      exact (map_eq_zero_iff _ (algebraMap ℚ K).injective).mp this
    have hev : ∀ x : Fin 2 → K, QuadForm.evalIn K Q x = algebraMap ℚ K (Q.coeff 0 0) * x 0 * x 0 + algebraMap ℚ K (Q.coeff 0 1) * x 0 * x 1 + algebraMap ℚ K (Q.coeff 1 1) * x 1 * x 1 := by
      intro x
      simp [QuadForm.evalIn, Fin.sum_univ_two]
    have key : ∀ (a b c : K), b^2 - 4*a*c ≠ 0 → ((∃ x : Fin 2 → K, x ≠ 0 ∧ a * x 0 * x 0 + b * x 0 * x 1 + c * x 1 * x 1 = 0) ↔ IsSquare (b^2 - 4*a*c)) := by
      intro a b c hD
      constructor
      · rintro ⟨x, hx0, hx⟩
        by_cases ha : a = 0
        · subst ha; exact ⟨b, by ring⟩
        · have hy : x 1 ≠ 0 := by
            intro hy
            apply hx0
            have : a * (x 0 * x 0) = 0 := by rw [hy] at hx; linear_combination hx
            have h0 : x 0 = 0 := by simpa [ha] using this
            ext i; fin_cases i <;> simp [h0, hy]
          refine ⟨(2 * a * x 0 + b * x 1) / x 1, ?_⟩
          field_simp
          linear_combination (-4 * a) * hx
      · rintro ⟨s, hs⟩
        by_cases ha : a = 0
        · refine ⟨![1, 0], ?_, ?_⟩
          · intro h; have := congrFun h 0; simp at this
          · simp [ha]
        · refine ⟨![s - b, 2 * a], ?_, ?_⟩
          · intro h; have := congrFun h 1; simp at this; exact ha this
          · simp
            linear_combination (-a) * hs
    unfold QuadForm.IsotropicIn
    simp only [hev]
    rw [key _ _ _ hD]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  set D := Q.coeff 0 1 ^ 2 - 4 * Q.coeff 0 0 * Q.coeff 1 1 with hDdef
  have hD0 : D ≠ 0 := by
    have hdet : Q.hessian.det = 4 * Q.coeff 0 0 * Q.coeff 1 1 - Q.coeff 0 1 ^ 2 := by
      have := Q.upper
      have h10 : Q.coeff 1 0 = 0 := this (by decide)
      simp [QuadForm.hessian, Matrix.det_fin_two, h10]
      ring
    intro h; apply hQ; unfold QuadForm.Nondegenerate at *; rw [hdet]; linear_combination -h
  have sqlem : ∀ (q : ℚ), 0 < q → (∀ p : ℕ, p.Prime → Even (padicValRat p q)) → IsSquare q := by
    intro q hq h
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have hn0 : q.num.natAbs ≠ 0 := by omega
    have hd0 : q.den ≠ 0 := q.den_nz
    have hN : IsSquare (q.num.natAbs * q.den) := by
      apply Nat.isSquare_iff_even_factorization.mpr
      intro p hp
      have hev := h p hp
      have : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, padicValNat.mul hn0 hd0]
      unfold padicValRat padicValInt at hev
      have h2 := Int.even_sub.mp hev
      have : Even ((padicValNat p q.num.natAbs : ℤ) + (padicValNat p q.den : ℤ)) := Int.even_add.mpr h2
      exact_mod_cast this
    obtain ⟨r, hr⟩ := hN
    refine ⟨(r : ℚ) / q.den, ?_⟩
    have key : (q.num : ℚ) * q.den = r * r := by
      have : ((q.num.natAbs : ℕ) : ℚ) = q.num := by
        rw [Nat.cast_natAbs]; simp [abs_of_pos hnum]
      rw [← this]; exact_mod_cast hr
    have hdq : (q.den : ℚ) ≠ 0 := by exact_mod_cast hd0
    calc q = (q.num : ℚ) * q.den / ((q.den : ℚ) * q.den) := by
            rw [mul_div_mul_right _ _ hdq]; exact (Rat.num_div_den q).symm
      _ = _ := by rw [key]; ring
  have padlem : ∀ (p : ℕ) [Fact p.Prime], IsSquare (algebraMap ℚ ℚ_[p] D) → Even (padicValRat p D) := by
    intro p _ h
    obtain ⟨y, hy⟩ := h
    simp only [eq_ratCast] at hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hD0 hy
    have := congrArg Padic.valuation hy
    rw [Padic.valuation_ratCast, Padic.valuation_mul hy0 hy0] at this
    exact ⟨_, this⟩
  constructor
  · intro h v
    have hs := (gen ℚ).mp h
    cases v with
    | infinite =>
      show Q.IsotropicIn ℝ
      rw [gen ℝ]; exact hs.map _
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.prop⟩
      show Q.IsotropicIn ℚ_[p]
      rw [gen ℚ_[p]]; exact hs.map _
  · intro h
    rw [gen ℚ]
    have hR : Q.IsotropicIn ℝ := h RatPlace.infinite
    rw [gen ℝ] at hR
    have hpos : 0 < D := by
      obtain ⟨y, hy⟩ := hR
      have : (0:ℝ) ≤ algebraMap ℚ ℝ D := by rw [hy]; exact mul_self_nonneg y
      have h0 : (0:ℝ) ≤ (D : ℝ) := by simpa using this
      have : (0:ℚ) ≤ D := by exact_mod_cast h0
      exact lt_of_le_of_ne this (Ne.symm hD0)
    have := sqlem D hpos (fun p hp => by
      have : Fact p.Prime := ⟨hp⟩
      have hP : Q.IsotropicIn ℚ_[p] := h (RatPlace.finite ⟨p, hp⟩)
      rw [gen ℚ_[p]] at hP
      exact padlem p hP)
    simpa using this

/-- Hasse–Minkowski, `n = 3` (Legendre; uses Dirichlet's theorem on primes in progressions). -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8 (n = 3)"]
theorem hasseMinkowski_three (Q : RatQF 3) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  have hae : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      hilbertSymbol K (algebraMap ℚ K (-a 1 / a 0)) (algebraMap ℚ K (-a 2 / a 0)) = 1 := by
    intro K _ _
    rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), hae,
      HM3.isotropic_diag_three_iff K _ _ _ (ha 0) (ha 1) (ha 2)]
    simp
  have hx : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 1)) (ha 0)
  have hy : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ha 2)) (ha 0)
  constructor
  · intro h
    have key2 : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K Q := by
      intro K _ _
      obtain ⟨x, hx, hQx⟩ := h
      refine ⟨fun i => algebraMap ℚ K (x i), ?_, ?_⟩
      · intro h0
        apply hx
        funext i
        have := congrFun h0 i
        simpa using this
      · have : QuadForm.evalIn K Q (fun i => algebraMap ℚ K (x i)) = algebraMap ℚ K (QuadForm.evalIn ℚ Q x) := by
          simp only [QuadForm.evalIn, map_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        rw [this, hQx, map_zero]
    intro v
    cases v with
    | infinite => exact key2 ℝ
    | finite p =>
      haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
      exact key2 ℚ_[p]
  · intro h
    rw [key ℚ]
    have := HM3.hilbert_rat_eq_one_of_everywhere _ _ hx hy (fun v => by
      have hv := h v
      cases v with
      | infinite =>
        have hv' : Q.IsotropicIn ℝ := hv
        rw [key ℝ] at hv'
        simpa [RatPlace.hilbert] using hv'
      | finite p =>
        haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
        have hv' : Q.IsotropicIn ℚ_[p] := hv
        rw [key ℚ_[p]] at hv'
        simpa [RatPlace.hilbert] using hv')
    simpa using this

/-- Hasse–Minkowski, `n = 4`. -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8 (n = 4)"]
theorem hasseMinkowski_four (Q : RatQF 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
  have hae : a = ![a 0, a 1, -(-a 2), -(-a 3)] := by funext i; fin_cases i <;> simp
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔
      (QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)]).IsotropicIn K := by
    intro K _ _
    rw [HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso), ← hae]
  have H := HM4.hasseMinkowski_diag_four (a 0) (a 1) (-a 2) (-a 3) (ha 0) (ha 1)
    (neg_ne_zero.mpr (ha 2)) (neg_ne_zero.mpr (ha 3))
  rw [key ℚ, H]
  constructor
  · intro h v
    have hv := h v
    cases v with
    | infinite => exact (key ℝ).mpr hv
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact (key ℚ_[p]).mpr hv
  · intro h v
    have hv := h v
    cases v with
    | infinite => exact (key ℝ).mp hv
    | finite p =>
      haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      exact (key ℚ_[p]).mp hv

/-- Hasse–Minkowski, `n ≥ 5` (by induction from `n = 4`). -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8 (n ≥ 5)"]
theorem hasseMinkowski_five_le (Q : RatQF n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ Everywhere fun K _ _ => Q.IsotropicIn K := by
  have evdiag : ∀ (K : Type) [Field K] [CharZero K] {m : ℕ} (a : Fin m → ℚ) (x : Fin m → K), QuadForm.evalIn K (QuadForm.diag a) x = ∑ i, (a i : K) * x i ^ 2 := by
    intro K _ _ m a x
    simp only [QuadForm.evalIn, QuadForm.diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  have crt : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) → ∀ (m : ℕ → ℤ) (K : ℕ → ℕ), ∃ x : ℤ, ∀ p ∈ T, (p:ℤ)^(K p) ∣ x - m p := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ m K; exact ⟨0, by simp⟩
    | insert q T hq ih =>
      intro hT m K
      obtain ⟨x, hx⟩ := ih (fun p hp => hT p (Finset.mem_insert_of_mem hp)) m K
      set M : ℤ := ∏ p ∈ T, (p:ℤ)^(K p) with hM
      have hcop : IsCoprime M ((q:ℤ)^(K q)) := by
        apply IsCoprime.prod_left
        intro p hp
        apply IsCoprime.pow
        rw [Int.isCoprime_iff_gcd_eq_one]
        have hp' := hT p (Finset.mem_insert_of_mem hp)
        have hq' := hT q (Finset.mem_insert_self q T)
        have hne : p ≠ q := fun h => hq (h ▸ hp)
        have := (Nat.coprime_primes hp' hq').mpr hne
        simpa [Int.gcd] using this
      obtain ⟨α, β, hαβ⟩ := hcop
      refine ⟨x + α * M * (m q - x), ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨β * (x - m p), by linear_combination -(x - m p) * hαβ⟩
      · have h1 := hx p hp
        have h2 : (p:ℤ)^(K p) ∣ M := Finset.dvd_prod_of_mem _ hp
        have : x + α * M * (m q - x) - m p = (x - m p) + M * (α * (m q - x)) := by ring
        rw [this]
        exact dvd_add h1 (dvd_mul_of_dvd_left h2 _)
  have wapprox : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) → ∀ (r : ℕ → ℚ) (N : ℕ), ∃ s : ℚ, ∀ p ∈ T, padicNorm p (s - r p) ≤ (p:ℚ)^(-(N:ℤ)) := by
    intro T hT r N
    set D : ℕ := ∏ p ∈ T, (r p).den with hD
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => (r p).den_nz
    have hdvd : ∀ p ∈ T, (r p).den ∣ D := fun p hp => Finset.dvd_prod_of_mem _ hp
    set m : ℕ → ℤ := fun p => (r p).num * ((D / (r p).den : ℕ) : ℤ) with hmdef
    have hm : ∀ p ∈ T, (m p : ℚ) = r p * D := by
      intro p hp
      obtain ⟨k, hk⟩ := hdvd p hp
      have hk' : D / (r p).den = k := by rw [hk]; exact Nat.mul_div_cancel_left k (r p).den_pos
      simp only [hmdef, hk']
      push_cast
      rw [hk]; push_cast
      rw [← Rat.mul_den_eq_num]; ring
    obtain ⟨x, hx⟩ := crt T hT m (fun p => N + padicValNat p D)
    refine ⟨(x : ℚ) / D, fun p hp => ?_⟩
    have := Fact.mk (hT p hp)
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    have e : (x : ℚ) / D - r p = ((x - m p : ℤ) : ℚ) / D := by
      push_cast; rw [hm p hp]; field_simp
    rw [e, padicNorm.div]
    have h1 := (padicNorm.dvd_iff_norm_le (p := p) (n := N + padicValNat p D) (z := x - m p)).mp (by exact_mod_cast hx p hp)
    have h2 : padicNorm p (D : ℚ) = (p:ℚ)^(-(padicValNat p D : ℤ)) := by
      rw [padicNorm.eq_zpow_of_nonzero hDq, padicValRat.of_nat]
    have hp0 : (0:ℚ) < p := by exact_mod_cast (hT p hp).pos
    rw [h2, div_le_iff₀ (zpow_pos hp0 _), ← zpow_add₀ hp0.ne']
    convert h1 using 2
    push_cast; ring
  have sqnear : ∀ (p : ℕ) [Fact p.Prime] (z : ℚ_[p]), ‖z - 1‖ < ‖(2:ℚ_[p])‖^2 → IsSquare z := by
    intro p _ z hz
    have h2 : ‖(2:ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) 2
      simpa using this
    have hz1 : ‖z‖ ≤ 1 := by
      have : z = (z - 1) + 1 := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (by simp))
      nlinarith [norm_nonneg (2:ℚ_[p])]
    set z' : ℤ_[p] := ⟨z, hz1⟩
    have hz' : (z' : ℚ_[p]) = z := rfl
    obtain ⟨w, hw, -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C z' : Polynomial ℤ_[p])) (a := 1) (by
      simp
      rw [PadicInt.norm_def, PadicInt.norm_def]
      have : ((1 - z' : ℤ_[p]) : ℚ_[p]) = -(z - 1) := by push_cast; rw [hz']; ring
      rw [this, norm_neg]
      have h11 : ((1 + 1 : ℤ_[p]) : ℚ_[p]) = 2 := by push_cast; norm_num
      rw [h11]; exact hz)
    refine ⟨(w : ℚ_[p]), ?_⟩
    simp at hw
    have : (w : ℚ_[p]) ^ 2 = z := by
      have := congrArg (fun u : ℤ_[p] => (u : ℚ_[p])) hw
      simp only [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_zero, hz'] at this
      linear_combination this
    rw [← this]; ring
  have perprime : ∀ (p : ℕ) [Fact p.Prime] (b3 b4 : ℚ) (sp tp : ℚ_[p]), (b3:ℚ_[p]) * sp^2 + b4 * tp^2 ≠ 0 → ∃ r1 r2 : ℚ, ∃ N : ℕ, ∀ s t : ℚ, padicNorm p (s - r1) ≤ (p:ℚ)^(-(N:ℤ)) → padicNorm p (t - r2) ≤ (p:ℚ)^(-(N:ℤ)) → ((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) ≠ 0 ∧ IsSquare (((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) / ((b3:ℚ_[p]) * sp^2 + b4 * tp^2)) := by
    intro p _ b3 b4 sp tp hyp
    set yp := (b3:ℚ_[p]) * sp^2 + b4 * tp^2 with hypdef
    have hF : Continuous (fun x : ℚ_[p] × ℚ_[p] => (b3:ℚ_[p]) * x.1^2 + b4 * x.2^2) := by fun_prop
    have h2pos : 0 < ‖(2:ℚ_[p])‖ := norm_pos_iff.mpr two_ne_zero
    have h2le : ‖(2:ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) 2
      simpa using this
    have h2sq : ‖(2:ℚ_[p])‖^2 ≤ 1 := by nlinarith
    have hε : 0 < ‖yp‖ * ‖(2:ℚ_[p])‖^2 := by
      have := norm_pos_iff.mpr hyp
      positivity
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hF (sp, tp) _ hε
    have hp1 : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hδ) (show (1:ℝ)/p < 1 by rw [div_lt_one (by linarith)]; exact hp1)
    obtain ⟨r1, hr1⟩ := Padic.rat_dense p sp (half_pos hδ)
    obtain ⟨r2, hr2⟩ := Padic.rat_dense p tp (half_pos hδ)
    refine ⟨r1, r2, N, fun s t hs ht => ?_⟩
    have close : ∀ (u r : ℚ) (x : ℚ_[p]), padicNorm p (u - r) ≤ (p:ℚ)^(-(N:ℤ)) → ‖x - r‖ < δ/2 → ‖(u:ℚ_[p]) - x‖ < δ := by
      intro u r x hu hx
      have e1 : ‖(u:ℚ_[p]) - r‖ ≤ (1/p:ℝ)^N := by
        have : ((u:ℚ_[p]) - r) = ((u - r : ℚ) : ℚ_[p]) := by push_cast; ring
        rw [this, Padic.eq_padicNorm]
        have := (Rat.cast_le (K := ℝ)).mpr hu
        convert this using 1
        push_cast
        rw [one_div, inv_pow, zpow_neg, zpow_natCast]
      have : (u:ℚ_[p]) - x = ((u:ℚ_[p]) - r) + (r - x) := by ring
      rw [this]
      calc _ ≤ ‖(u:ℚ_[p]) - r‖ + ‖(r:ℚ_[p]) - x‖ := norm_add_le _ _
        _ < δ/2 + δ/2 := by
          rw [norm_sub_rev (r:ℚ_[p]) x]; linarith
        _ = δ := by ring
    have hd : dist ((s:ℚ_[p]), (t:ℚ_[p])) (sp, tp) < δ := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨close s r1 sp hs hr1, close t r2 tp ht hr2⟩
    have hb := hball _ hd
    rw [dist_eq_norm] at hb
    have ey : ((b3 * s^2 + b4 * t^2 : ℚ) : ℚ_[p]) = (b3:ℚ_[p]) * (s:ℚ_[p])^2 + b4 * (t:ℚ_[p])^2 := by push_cast; ring
    rw [ey]
    set y := (b3:ℚ_[p]) * (s:ℚ_[p])^2 + b4 * (t:ℚ_[p])^2
    change ‖y - yp‖ < _ at hb
    have hyp' : 0 < ‖yp‖ := norm_pos_iff.mpr hyp
    constructor
    · intro hy0
      rw [hy0, zero_sub, norm_neg] at hb
      nlinarith
    · apply sqnear
      have : y / yp - 1 = (y - yp) / yp := by field_simp
      rw [this, norm_div, div_lt_iff₀ hyp']
      linarith
  have loctarget : ∀ (K : Type) [Field K] [CharZero K] (b : Fin 5 → ℚ), (∀ i, b i ≠ 0) → QuadForm.IsotropicIn K (QuadForm.diag b) → ∃ sp tp : K, (b 3 : K) * sp^2 + b 4 * tp^2 ≠ 0 ∧ ∃ z0 z1 z2 w : K, ¬(z0 = 0 ∧ z1 = 0 ∧ z2 = 0 ∧ w = 0) ∧ (b 0 : K) * z0^2 + b 1 * z1^2 + b 2 * z2^2 + ((b 3 : K) * sp^2 + b 4 * tp^2) * w^2 = 0 := by
    intro K _ _ b hb ⟨z, hz0, hz⟩
    rw [evdiag, Fin.sum_univ_five] at hz
    have hb' : ∀ i, (b i : K) ≠ 0 := fun i => by exact_mod_cast hb i
    by_cases h1 : (b 3 : K) * z 3^2 + b 4 * z 4^2 = 0
    · by_cases h2 : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0
      · obtain ⟨e0, e1, e2⟩ := h2
        have h3 : z 3 ≠ 0 := by
          intro h3
          apply hz0
          have : (b 4 : K) * z 4 ^ 2 = 0 := by rw [h3] at h1; simpa using h1
          have h4 : z 4 = 0 := by simpa [hb' 4] using this
          funext i; fin_cases i <;> simp [e0, e1, e2, h3, h4]
        set r : K := -(b 0 : K) / ((b 3 : K) * z 3 ^ 2)
        have hr : (b 3 : K) * z 3 ^ 2 * r = -(b 0) := by
          simp only [r]; field_simp [hb' 3, h3]
        have hy : (b 3 : K) * (z 3 * ((r+1)/2))^2 + b 4 * (z 4 * ((r-1)/2))^2 = -(b 0) := by
          linear_combination ((r-1)^2/4) * h1 + hr
        refine ⟨z 3 * ((r+1)/2), z 4 * ((r-1)/2), ?_, 1, 0, 0, 1, by simp, ?_⟩
        · rw [hy]; exact neg_ne_zero.mpr (hb' 0)
        · rw [hy]; ring
      · refine ⟨1, 0, by simpa using hb' 3, z 0, z 1, z 2, 0, by tauto, ?_⟩
        linear_combination hz - h1
    · refine ⟨z 3, z 4, h1, z 0, z 1, z 2, 1, by simp, ?_⟩
      linear_combination hz
  have core5 : ∀ b : Fin 5 → ℚ, (∀ i, b i ≠ 0) → 0 < b 0 → b 1 < 0 → QuadForm.IsotropicIn ℚ (QuadForm.diag b) := by
    intro b hb hb0 hb1
    set L : ℕ := 2 * ((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den) with hLdef
    have hL : L ≠ 0 := by simp [hLdef, hb]
    set T := L.primeFactors
    have hT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have h2T : 2 ∈ T := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ⟨((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩, hL⟩
    have hf0 : (b 0).num.natAbs * (b 0).den ∣ L := ⟨2 * ((b 1).num.natAbs * (b 1).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩
    have hf1 : (b 1).num.natAbs * (b 1).den ∣ L := ⟨2 * ((b 0).num.natAbs * (b 0).den) * ((b 2).num.natAbs * (b 2).den), by simp only [hLdef]; ring⟩
    have hf2 : (b 2).num.natAbs * (b 2).den ∣ L := ⟨2 * ((b 0).num.natAbs * (b 0).den) * ((b 1).num.natAbs * (b 1).den), by simp only [hLdef]; ring⟩
    have hv : ∀ p, p.Prime → p ∉ T → ∀ q : ℚ, q.num.natAbs * q.den ∣ L → padicValRat p q = 0 := by
      intro p hp hpT q hq
      have hnd : ¬ p ∣ L := fun h => hpT (Nat.mem_primeFactors.mpr ⟨hp, h, hL⟩)
      have key : ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
        constructor <;> intro h <;> apply hnd
        · exact (h.trans (dvd_mul_right _ _)).trans hq
        · exact (h.trans (dvd_mul_left _ _)).trans hq
      have := Fact.mk hp
      rw [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd key.1, padicValNat.eq_zero_of_not_dvd key.2]
      simp
    have hloc : ∀ p : ℕ, ∃ r1 r2 : ℚ, ∃ N : ℕ, ∀ (hp : p ∈ T) (s t : ℚ), padicNorm p (s - r1) ≤ (p:ℚ)^(-(N:ℤ)) → padicNorm p (t - r2) ≤ (p:ℚ)^(-(N:ℤ)) → b 3 * s^2 + b 4 * t^2 ≠ 0 ∧ RatPlace.atPlace (fun K _ _ => QuadForm.IsotropicIn K (QuadForm.diag ![b 0, b 1, b 2, b 3 * s^2 + b 4 * t^2])) (RatPlace.finite ⟨p, hT p hp⟩) := by
      intro p
      by_cases hp : p ∈ T
      · have := Fact.mk (hT p hp)
        have hiso : QuadForm.IsotropicIn ℚ_[p] (QuadForm.diag b) := by
          by_cases h2 : p = 2
          · subst h2; exact RankFive.isotropic_two_adic_diag b hb le_rfl
          · exact RankFive.isotropic_padic_diag_odd p h2 b hb le_rfl
        obtain ⟨sp, tp, hyp, z0, z1, z2, w, hz0, hz⟩ := loctarget ℚ_[p] b hb hiso
        obtain ⟨r1, r2, N, hgood⟩ := perprime p (b 3) (b 4) sp tp hyp
        refine ⟨r1, r2, N, fun _ s t hs ht => ?_⟩
        obtain ⟨hy0, c, hc⟩ := hgood s t hs ht
        refine ⟨fun h => hy0 (by rw [h]; simp), ?_⟩
        show QuadForm.IsotropicIn ℚ_[p] _
        have hc0 : c ≠ 0 := by
          rintro rfl; rw [mul_zero] at hc; exact div_ne_zero hy0 hyp hc
        have hyeq : ((b 3 * s^2 + b 4 * t^2 : ℚ) : ℚ_[p]) = ((b 3 : ℚ_[p]) * sp^2 + b 4 * tp^2) * (c * c) := by
          rw [← hc]; field_simp
        refine ⟨![z0, z1, z2, w / c], ?_, ?_⟩
        · intro h; apply hz0
          have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2; have e3 := congrFun h 3
          simp at e0 e1 e2 e3
          exact ⟨e0, e1, e2, by simpa [hc0] using e3⟩
        · rw [evdiag, Fin.sum_univ_four]
          show (b 0 : ℚ_[p]) * z0^2 + (b 1 : ℚ_[p]) * z1^2 + (b 2:ℚ_[p]) * z2^2 + ((b 3 * s^2 + b 4 * t^2 : ℚ) : ℚ_[p]) * (w/c)^2 = 0
          rw [hyeq]
          have hw : (c*c)*(w/c)^2 = w^2 := by field_simp
          linear_combination hz + ((b 3 : ℚ_[p]) * sp^2 + b 4 * tp^2) * hw
      · exact ⟨0, 0, 0, fun h => absurd h hp⟩
    choose r1 r2 N hgood using hloc
    obtain ⟨s, hs⟩ := wapprox T hT r1 (T.sup N)
    obtain ⟨t, ht⟩ := wapprox T hT r2 (T.sup N)
    have hmono : ∀ p ∈ T, (p:ℚ)^(-((T.sup N : ℕ):ℤ)) ≤ (p:ℚ)^(-(N p:ℤ)) := fun p hp =>
      zpow_le_zpow_right₀ (by exact_mod_cast (hT p hp).one_lt.le) (neg_le_neg (by exact_mod_cast Finset.le_sup hp))
    have hG : ∀ (p : ℕ) (hp : p ∈ T), _ := fun p hp => hgood p hp s t ((hs p hp).trans (hmono p hp)) ((ht p hp).trans (hmono p hp))
    set y := b 3 * s^2 + b 4 * t^2 with hydef
    have hy0 : y ≠ 0 := (hG 2 h2T).1
    have H := HM4.hasseMinkowski_diag_four (b 0) (b 1) (-b 2) (-y) (hb 0) (hb 1) (neg_ne_zero.mpr (hb 2)) (neg_ne_zero.mpr hy0)
    simp only [neg_neg] at H
    have hev : RatPlace.Everywhere fun K _ _ => QuadForm.IsotropicIn K (QuadForm.diag ![b 0, b 1, b 2, y]) := by
      intro v
      cases v with
      | infinite =>
        show QuadForm.IsotropicIn ℝ _
        refine ⟨![Real.sqrt (-b 1), Real.sqrt (b 0), 0, 0], ?_, ?_⟩
        · intro h; have := congrFun h 1; simp at this
          have := Real.sqrt_eq_zero'.mp this
          have : (0:ℝ) < b 0 := by exact_mod_cast hb0
          linarith
        · rw [evdiag, Fin.sum_univ_four]
          show (b 0 : ℝ) * Real.sqrt (-b 1)^2 + (b 1 : ℝ) * Real.sqrt (b 0)^2 + (b 2:ℝ) * 0^2 + (y : ℝ) * 0^2 = 0
          have h0 : (0:ℝ) ≤ b 0 := by exact_mod_cast hb0.le
          have h1 : (0:ℝ) ≤ -b 1 := by have h := (show (b 1 : ℝ) < 0 by exact_mod_cast hb1); linarith
          rw [Real.sq_sqrt h0, Real.sq_sqrt h1]; ring
      | finite p =>
        by_cases hp : (p:ℕ) ∈ T
        · exact (hG p hp).2
        · have := Fact.mk p.2
          show QuadForm.IsotropicIn ℚ_[p] _
          have hp2 : (p:ℕ) ≠ 2 := fun h => hp (h ▸ h2T)
          obtain ⟨z, hz0, hz⟩ := RankFive.isotropic_padic_unit_ternary p hp2 (b 0) (b 1) (b 2) (hb 0) (hb 1) (hb 2)
            (hv p p.2 hp _ hf0) (hv p p.2 hp _ hf1) (hv p p.2 hp _ hf2)
          refine ⟨![z 0, z 1, z 2, 0], ?_, ?_⟩
          · intro h; apply hz0
            have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
            simp at e0 e1 e2
            funext i; fin_cases i <;> simp [e0, e1, e2]
          · rw [evdiag, Fin.sum_univ_four]
            rw [evdiag, Fin.sum_univ_three] at hz
            show (b 0 : ℚ_[p]) * z 0^2 + (b 1 : ℚ_[p]) * z 1^2 + (b 2:ℚ_[p]) * z 2^2 + (y : ℚ_[p]) * 0^2 = 0
            simpa using hz
    obtain ⟨x, hx0, hx⟩ := H.mpr hev
    refine ⟨![x 0, x 1, x 2, x 3 * s, x 3 * t], ?_, ?_⟩
    · intro h; apply hx0
      have e0 := congrFun h 0; have e1 := congrFun h 1; have e2 := congrFun h 2
      have e3 := congrFun h 3; have e4 := congrFun h 4
      simp at e0 e1 e2 e3 e4
      have h3 : x 3 = 0 := by
        by_contra h3
        apply hy0
        have : y * x 3 ^ 2 = 0 := by
          rw [hydef, e3.resolve_left h3, e4.resolve_left h3]; ring
        simpa [h3] using this
      funext i; fin_cases i <;> simp [e0, e1, e2, h3]
    · rw [evdiag, Fin.sum_univ_five]
      rw [evdiag, Fin.sum_univ_four] at hx
      have hx' : b 0 * x 0^2 + b 1 * x 1^2 + b 2 * x 2^2 + y * x 3^2 = 0 := by simpa using hx
      show ((b 0 : ℚ) : ℚ) * x 0^2 + ((b 1 : ℚ) : ℚ) * x 1^2 + ((b 2 : ℚ) : ℚ) * x 2^2 + ((b 3 : ℚ) : ℚ) * (x 3 * s)^2 + ((b 4 : ℚ) : ℚ) * (x 3 * t)^2 = 0
      rw [hydef] at hx'
      try simp only [Rat.cast_id]
      linear_combination hx'
  constructor
  · intro h
    have key : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K Q := by
      intro K _ _
      obtain ⟨x, hx, hQx⟩ := h
      refine ⟨fun i => algebraMap ℚ K (x i), ?_, ?_⟩
      · intro h0
        apply hx
        funext i
        have := congrFun h0 i
        simpa using this
      · have : QuadForm.evalIn K Q (fun i => algebraMap ℚ K (x i)) = algebraMap ℚ K (QuadForm.evalIn ℚ Q x) := by
          simp only [QuadForm.evalIn, map_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        rw [this, hQx, map_zero]
    intro v
    cases v with
    | infinite => exact key ℝ
    | finite p =>
      haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
      exact key ℚ_[p]
  · intro h
    obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag Q hQ
    have hiK : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K :=
      fun K _ _ => HM3.isotropicIn_iff_of_isometricIn K (HM3.isometricIn_of_rat K hiso)
    rw [hiK ℚ]
    have hR : (QuadForm.diag a).IsotropicIn ℝ := (hiK ℝ).mp (h .infinite)
    have hsign : ∀ (c : ℝ), (c = 1 ∨ c = -1) → ∃ i, 0 < c * a i := by
      intro c hc
      by_contra hcon
      push_neg at hcon
      obtain ⟨x, hx0, hx⟩ := hR
      rw [evdiag] at hx
      have hx' : ∑ i, c * ((a i : ℝ) * x i ^ 2) = 0 := by rw [← Finset.mul_sum, hx, mul_zero]
      have hle : ∀ i ∈ Finset.univ, c * ((a i : ℝ) * x i ^ 2) ≤ 0 := by
        intro i _
        have := hcon i
        rw [← mul_assoc]
        exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _)
      have hall := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hx'
      apply hx0
      funext i
      have := hall i (Finset.mem_univ _)
      have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
      have ha0 : (a i : ℝ) ≠ 0 := by exact_mod_cast ha i
      simpa [hc0, ha0] using this
    obtain ⟨i, hi⟩ := hsign 1 (Or.inl rfl)
    obtain ⟨j, hj⟩ := hsign (-1) (Or.inr rfl)
    have hi' : 0 < a i := by
      have : (0:ℝ) < a i := by simpa using hi
      exact_mod_cast this
    have hj' : a j < 0 := by
      have : (a j : ℝ) < 0 := by simpa using hj
      exact_mod_cast this
    have hij : i ≠ j := by rintro rfl; linarith
    set i0 : Fin n := ⟨0, by omega⟩
    set i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    set σ1 := Equiv.swap i0 i
    set j' := σ1 j
    have hj'0 : j' ≠ i0 := by
      intro e
      apply hij
      have : σ1 (σ1 j) = σ1 i0 := by rw [show σ1 j = j' from rfl, e]
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact this.symm
    set σ2 := Equiv.swap i1 j'
    set a2 := (a ∘ σ1) ∘ σ2
    have e0 : a2 i0 = a i := by
      simp only [a2, Function.comp_apply, σ2, σ1]
      rw [Equiv.swap_apply_of_ne_of_ne h01 hj'0.symm, Equiv.swap_apply_left]
    have e1 : a2 i1 = a j := by
      simp only [a2, Function.comp_apply, σ2, Equiv.swap_apply_left, j', σ1, Equiv.swap_apply_self]
    rw [← RankFive.isotropicIn_diag_perm_iff ℚ a σ1, ← RankFive.isotropicIn_diag_perm_iff ℚ _ σ2]
    apply RankFive.isotropicIn_diag_of_prefix ℚ 5 hn a2
    apply core5
    · intro k; exact ha _
    · exact e0 ▸ hi'
    · exact e1 ▸ hj'

/-- The trivial direction: isotropic over ℚ implies isotropic everywhere locally. -/
@[kb "serre1973" "Ch. IV, §3.2, Thm. 8"]
theorem isotropic_everywhere_of_isotropic (Q : RatQF n) (h : Q.IsotropicIn ℚ) :
    Everywhere fun K _ _ => Q.IsotropicIn K := by
  have key : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K Q := by
    intro K _ _
    obtain ⟨x, hx, hQx⟩ := h
    refine ⟨fun i => algebraMap ℚ K (x i), ?_, ?_⟩
    · intro h0
      apply hx
      funext i
      have := congrFun h0 i
      simpa using this
    · have : QuadForm.evalIn K Q (fun i => algebraMap ℚ K (x i)) = algebraMap ℚ K (QuadForm.evalIn ℚ Q x) := by
        simp only [QuadForm.evalIn, map_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [this, hQx, map_zero]
  intro v
  cases v with
  | infinite => exact key ℝ
  | finite p =>
    haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
    exact key ℚ_[p]

/-- **Everywhere-local properties are monotone:** if $P(K) \Rightarrow P'(K)$ for every field $K$ of
characteristic $0$, then $P$ everywhere locally implies $P'$ everywhere locally. -/
theorem RatPlace.Everywhere.mono {P P' : (K : Type) → [Field K] → [CharZero K] → Prop}
    (H : ∀ (K : Type) [Field K] [CharZero K], P K → P' K) (h : Everywhere P) : Everywhere P' := by
  intro v
  cases v with
  | infinite => exact H ℝ (h .infinite)
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    exact H ℚ_[p.1] (h (.finite p))

/-- Corollary: local-global principle for representing a nonzero rational.

*Proof* (Serre IV §3.2, Cor. 1). For $c \ne 0$, $Q$ represents $c$ over a field $K$ iff
$Q \perp \langle -c \rangle$ is isotropic over $K$ (`QuadForm.representsIn_iff_isotropicIn_orthSum`);
apply `hasseMinkowski` to $Q \perp \langle -c \rangle$. -/
@[kb "serre1973" "Ch. IV, §3.2, Cor. 1"]
theorem represents_iff_everywhere (Q : RatQF n) (hQ : Q.Nondegenerate) (c : ℚ) (hc : c ≠ 0) :
    Q.RepresentsIn ℚ c ↔ Everywhere fun K _ _ => Q.RepresentsIn K c := by
  have hc' : ∀ i, (![-c] : Fin 1 → ℚ) i ≠ 0 := fun i => by
    simpa [Subsingleton.elim i 0] using hc
  rw [QuadForm.representsIn_iff_isotropicIn_orthSum ℚ hQ c,
    hasseMinkowski _ (QuadForm.nondegenerate_orthSum hQ (QuadForm.nondegenerate_diag hc'))]
  exact ⟨Everywhere.mono fun K _ _ =>
      (QuadForm.representsIn_iff_isotropicIn_orthSum K hQ c).mpr,
    Everywhere.mono fun K _ _ => (QuadForm.representsIn_iff_isotropicIn_orthSum K hQ c).mp⟩

/-- **The local–global step for isometry** (Serre IV §3.3, proof of Thm. 9): induction on $n$. Write
$R \cong \langle b, \beta' \rangle$ over $\mathbb{Q}$. Locally $Q \cong R$ represents $b$, so $Q$ represents $b$
over $\mathbb{Q}$ (`represents_iff_everywhere`) and $Q \cong \langle b, \alpha \rangle$
(`QuadForm.exists_isometric_diag_cons`). Witt cancellation at each place
(`QuadForm.isometricIn_of_diag_cons`) gives $\langle \alpha \rangle \cong \langle \beta' \rangle$
everywhere locally, hence over $\mathbb{Q}$ by induction. -/
theorem isometric_of_everywhere : ∀ {n : ℕ} (Q R : RatQF n), Q.Nondegenerate → R.Nondegenerate →
    (Everywhere fun K _ _ => Q.IsometricIn K R) → Q.IsometricIn ℚ R
  | 0, Q, R, _, _, _ => ⟨1, by simp, fun x => by simp [QuadForm.evalIn]⟩
  | m + 1, Q, R, hQ, hR, h => by
    obtain ⟨β, hβ, hRβ⟩ := FieldGen.exists_isometric_diag R hR
    have hrep : ∀ (K : Type) [Field K] [CharZero K], (QuadForm.diag β).RepresentsIn K (β 0) := by
      intro K _ _
      refine ⟨Pi.single 0 1, ?_⟩
      rw [QuadForm.evalIn_diag, Finset.sum_eq_single 0]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    have hQb : Q.RepresentsIn ℚ (β 0) := by
      rw [represents_iff_everywhere Q hQ _ (hβ 0)]
      exact Everywhere.mono (fun K _ _ hK => QuadForm.representsIn_of_isometricIn K
        (QuadForm.isometricIn_trans K hK (FieldGen.isometricIn_of_base K hRβ)) (hrep K)) h
    obtain ⟨α, hα, hQα⟩ := QuadForm.exists_isometric_diag_cons hQ (hβ 0) hQb
    have hβc : Fin.cons (β 0) (Fin.tail β) = β := Fin.cons_self_tail β
    have hloc : Everywhere fun K _ _ =>
        (QuadForm.diag α).IsometricIn K (QuadForm.diag (Fin.tail β)) :=
      Everywhere.mono (fun K _ _ hK => by
        refine QuadForm.isometricIn_of_diag_cons K (hβ 0) hα ?_
        rw [hβc]
        exact QuadForm.isometricIn_trans K
          (QuadForm.isometricIn_symm K (FieldGen.isometricIn_of_base K hQα))
          (QuadForm.isometricIn_trans K hK (FieldGen.isometricIn_of_base K hRβ))) h
    have ih := isometric_of_everywhere _ _ (QuadForm.nondegenerate_diag hα)
      (QuadForm.nondegenerate_diag (a := Fin.tail β) fun i => hβ i.succ) hloc
    have := QuadForm.isometricIn_diag_cons_of ℚ (β 0) ih
    rw [hβc] at this
    exact QuadForm.isometricIn_trans ℚ hQα
      (QuadForm.isometricIn_trans ℚ this (QuadForm.isometricIn_symm ℚ hRβ))

/-- Corollary: two nondegenerate rational forms are isometric over ℚ iff they are isometric
over every completion.

*Proof* (Serre IV §3.3, Thm. 9). Isometry over $\mathbb{Q}$ base-changes to every completion
(`FieldGen.isometricIn_of_base`); the converse is `isometric_of_everywhere`, from
`represents_iff_everywhere` and Witt cancellation over $\mathbb{R}$ and $\mathbb{Q}_p$. -/
@[kb "serre1973" "Ch. IV, §3.3, Thm. 9"]
theorem isometric_iff_everywhere (Q R : RatQF n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn ℚ R ↔ Everywhere fun K _ _ => Q.IsometricIn K R := by
  refine ⟨fun h => ?_, isometric_of_everywhere Q R hQ hR⟩
  have key : ∀ (K : Type) [Field K] [CharZero K], Q.IsometricIn K R :=
    fun K _ _ => FieldGen.isometricIn_of_base K h
  intro v
  cases v with
  | infinite => exact key ℝ
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    exact key ℚ_[p.1]

end QuadFormsKB
