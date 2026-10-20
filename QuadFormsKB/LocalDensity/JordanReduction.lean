/-
# Local densities over $\mathbb{Q}$: the Bad-type reduction maps for forms in normal form

**Layer:** $\mathbb{Q}$. For $Q$ with `IsJordanForm Q p P ν` (block diagonal, 1- and 2-dimensional blocks),
**defines** the reduced forms $Q'$ (`badIFormJ`, exponents `nuI ν`) and $Q''$ (`badIIFormJ`, exponents `nuII ν`) of
Hanke 2004, §3, p. 360, **proves** they are again in normal form (`isJordanForm_badI_badII`), and the counting
identities for $\pi_{B'}$ (`repCountBadI_eq_J`) and $\pi_{B''}$ (`repCountBadII_eq_J`), p. 360.
**Depends on** `JordanForm.lean`. The diagonal case is `Reduction.lean`; the DVR version is
`DVRReductions.lean` and `DVRGeneral.lean`.
-/
import QuadFormsKB.LocalDensity.JordanForm

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **The form $Q'$ of Bad type I for a block-diagonal form** (Hanke 2004, p. 360): coefficient
$p\,c_{ij}$ when $\nu_i = 0$ and $c_{ij}/p$ otherwise (cross-block coefficients are $0$ either way). -/
def badIFormJ (Q : QuadForm ℤ n) (p : ℕ) (ν : Fin n → ℕ) : QuadForm ℤ n :=
  QuadForm.ofUpper fun i j => if ν i = 0 then (p : ℤ) * Q.coeff i j else Q.coeff i j / p

/-- **The form $Q''$ of Bad type II for a block-diagonal form** (Hanke 2004, p. 360): coefficient
$c_{ij}/p^2$ when $\nu_i \ge 2$ and $c_{ij}$ otherwise. -/
def badIIFormJ (Q : QuadForm ℤ n) (p : ℕ) (ν : Fin n → ℕ) : QuadForm ℤ n :=
  QuadForm.ofUpper fun i j => if 2 ≤ ν i then Q.coeff i j / (p : ℤ) ^ 2 else Q.coeff i j

/-- **The new Jordan exponents** (Hanke 2004, p. 360): $\nu'_j = \nu_j + 1$ on $S_0$, $\nu_j - 1$ elsewhere;
$\nu''_j = \nu_j$ on $S_0 \cup S_1$, $\nu_j - 2$ on $S_2$. -/
def nuI (ν : Fin n → ℕ) : Fin n → ℕ := fun i => if ν i = 0 then 1 else ν i - 1

/-- See `nuI`. -/
def nuII (ν : Fin n → ℕ) : Fin n → ℕ := fun i => if 2 ≤ ν i then ν i - 2 else ν i

/-- **$Q'$ and $Q''$ are again in local normal form**, with the same blocks and exponents `nuI ν`,
`nuII ν` (Hanke 2004, p. 360: "$Q_j = Q'_j = Q''_j$ for all $j$"). -/
@[kb "hanke2004" "§3, p. 360"]
theorem isJordanForm_badI_badII (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) :
    IsJordanForm (badIFormJ Q p ν) p P (nuI ν) ∧ IsJordanForm (badIIFormJ Q p ν) p P (nuII ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
  have hp : (p:ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have d1 : ∀ d, 1 ≤ d → ∀ b : ℤ, (p:ℤ)^d * b / p = p^(d-1) * b := by
    intro d hd b
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [show (p:ℤ)^(1+e)*b = p * (p^e*b) by ring, Int.mul_ediv_cancel_left _ hp]
    simp
  have d2 : ∀ d, 2 ≤ d → ∀ b : ℤ, (p:ℤ)^d * b / p^2 = p^(d-2) * b := by
    intro d hd b
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [show (p:ℤ)^(2+e)*b = p^2 * (p^e*b) by ring, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp)]
    simp
  have cI : ∀ i j, (badIFormJ Q p ν).coeff i j = if i ≤ j then (if ν i = 0 then (p:ℤ) * Q.coeff i j else Q.coeff i j / p) else 0 := fun i j => rfl
  have cII : ∀ i j, (badIIFormJ Q p ν).coeff i j = if i ≤ j then (if 2 ≤ ν i then Q.coeff i j / (p:ℤ)^2 else Q.coeff i j) else 0 := fun i j => rfl
  refine ⟨⟨h1, h2, h3, ?_, ?_, ?_⟩, ⟨h1, h2, h3, ?_, ?_, ?_⟩⟩
  · intro i j hij hP; rw [cI, h4 i j hij hP]; simp
  · intro e he
    obtain ⟨hν, ⟨b, hb, hbp⟩, hd1, hd2⟩ := h5 e he
    have hle : e.1 ≤ e.2 := (h2 e he).le
    simp only [cI, hle, le_refl, if_true, nuI, ← hν]
    by_cases h0 : ν e.1 = 0
    · simp only [h0, if_true, pow_zero, one_mul] at hb ⊢
      exact ⟨trivial, ⟨b, by rw [hb]; ring, hbp⟩, by rw [pow_one]; exact dvd_mul_right _ _, by rw [pow_one]; exact dvd_mul_right _ _⟩
    · simp only [h0, if_false]
      obtain ⟨c1, hc1⟩ := hd1; obtain ⟨c2, hc2⟩ := hd2
      have hd : 1 ≤ ν e.1 := Nat.one_le_iff_ne_zero.mpr h0
      exact ⟨trivial, ⟨b, by rw [hb, d1 _ hd], hbp⟩, ⟨c1, by rw [hc1, d1 _ hd]⟩, ⟨c2, by rw [hc2, d1 _ hd]⟩⟩
  · intro i hi
    obtain ⟨u, hu, hup⟩ := h6 i hi
    simp only [cI, le_refl, if_true, nuI]
    by_cases h0 : ν i = 0
    · simp only [h0, if_true, pow_zero, one_mul] at hu ⊢
      exact ⟨u, by rw [hu]; ring, hup⟩
    · simp only [h0, if_false]
      exact ⟨u, by rw [hu, d1 _ (Nat.one_le_iff_ne_zero.mpr h0)], hup⟩
  · intro i j hij hP; rw [cII, h4 i j hij hP]; simp
  · intro e he
    obtain ⟨hν, ⟨b, hb, hbp⟩, hd1, hd2⟩ := h5 e he
    have hle : e.1 ≤ e.2 := (h2 e he).le
    simp only [cII, hle, le_refl, if_true, nuII, ← hν]
    by_cases h0 : 2 ≤ ν e.1
    · simp only [h0, if_true]
      obtain ⟨c1, hc1⟩ := hd1; obtain ⟨c2, hc2⟩ := hd2
      exact ⟨trivial, ⟨b, by rw [hb, d2 _ h0], hbp⟩, ⟨c1, by rw [hc1, d2 _ h0]⟩, ⟨c2, by rw [hc2, d2 _ h0]⟩⟩
    · simp only [h0, if_false]
      exact ⟨trivial, ⟨b, hb, hbp⟩, hd1, hd2⟩
  · intro i hi
    obtain ⟨u, hu, hup⟩ := h6 i hi
    simp only [cII, le_refl, if_true, nuII]
    by_cases h0 : 2 ≤ ν i
    · simp only [h0, if_true]
      exact ⟨u, by rw [hu, d2 _ h0], hup⟩
    · simp only [h0, if_false]
      exact ⟨u, hu, hup⟩

/-- **Bad type I reduction for block-diagonal forms** (Hanke 2004, §3, map $\pi_{B'}$, p. 360): for
$p \mid m$ and $k \ge 2$, the Bad-type solutions with $\vec{x}_{S_1} \not\equiv \vec{0}$ number
$p^{s_1 + s_2}$ times the Good-type solutions of $Q'(\vec{x}') \equiv m/p \pmod{p^{k-1}}$ (Good relative to
the unimodular coordinates of $Q'$, which are $S_1$). Same proof as `repCountBadI_eq`, blockwise. -/
@[kb "hanke2004" "§3, map π_{B'}, p. 360"]
theorem repCountBadI_eq_J (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (m : ℤ) (k : ℕ) (hk : 2 ≤ k) (hm : (p : ℤ) ∣ m) :
    repCountOf Q p k m
        (fun x => IsBadType (unimodularCoords ν) p k x ∧
          ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p ^ k)) ∣ x i) =
      p ^ ((Finset.univ.filter fun i => 1 ≤ ν i).card) *
        repCountOf (badIFormJ Q p ν) p (k - 1) (m / p)
          (IsGoodType (unimodularCoords (nuI ν)) p (k - 1)) := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have hpZ : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hblk : ∀ i j, i ≤ j → Q.coeff i j ≠ 0 → ν i = ν j ∧ (p:ℤ)^(ν i) ∣ Q.coeff i j := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
    intro i j hij hne
    rcases hij.eq_or_lt with rfl | hlt
    · refine ⟨rfl, ?_⟩
      by_cases hp : IsPaired P i
      · obtain ⟨e, he, h⟩ := hp
        obtain ⟨hν, _, hd1, hd2⟩ := h5 e he
        rcases h with rfl | rfl
        · exact hd1
        · rw [← hν]; exact hd2
      · obtain ⟨u, hu, _⟩ := h6 i hp
        exact ⟨u, hu⟩
    · by_cases hP : (i, j) ∈ P
      · obtain ⟨hν, ⟨b, hb, _⟩, _, _⟩ := h5 _ hP
        exact ⟨hν, ⟨b, hb⟩⟩
      · exact absurd (h4 i j hlt hP) hne
  have hev : ∀ X Y : Fin n → ℤ, (∀ j, X j = (if ν j = 0 then (p:ℤ) else 1) * Y j) →
      QuadForm.evalIn ℤ Q X = p * QuadForm.evalIn ℤ (badIFormJ Q p ν) Y := by
    intro X Y hXY
    simp only [QuadForm.evalIn, Finset.mul_sum, algebraMap_int_eq, eq_intCast, Int.cast_id]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≤ j
    · have hc : (badIFormJ Q p ν).coeff i j = if ν i = 0 then (p:ℤ) * Q.coeff i j else Q.coeff i j / p := by
        simp [badIFormJ, QuadForm.ofUpper, hij]
      simp only [hij, if_true, hc, hXY]
      by_cases h0 : Q.coeff i j = 0
      · simp [h0]
      obtain ⟨hν, hd⟩ := hblk i j hij h0
      by_cases hνi : ν i = 0
      · have hνj : ν j = 0 := hν ▸ hνi
        simp only [hνi, hνj, if_true]; ring
      · have hνj : ¬ ν j = 0 := hν ▸ hνi
        have : (p:ℤ) ∣ Q.coeff i j := (dvd_pow_self _ hνi).trans hd
        obtain ⟨c, hc⟩ := this
        simp only [hνi, hνj, if_false, hc, Int.mul_ediv_cancel_left _ hpZ]; ring
    · simp [hij]
  have hcast : ∀ (M : ℕ) (Q : QuadForm ℤ n) (v : Fin n → ℤ),
      QuadForm.evalIn (ZMod M) Q (fun j => (v j : ZMod M)) = ((QuadForm.evalIn ℤ Q v : ℤ) : ZMod M) := by
    intro M Q v; simp [QuadForm.evalIn]
  have hdvd : ∀ M, 1 ≤ M → ∀ a : ℕ, (p : ZMod (p^M)) ∣ (a : ZMod (p^M)) ↔ p ∣ a := by
    intro M hM a
    constructor
    · rintro ⟨c, hc⟩
      have : ((a : ℤ) : ZMod (p^M)) = ((p * c.val : ℕ) : ℤ) := by push_cast; simp [hc]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      have h2 : (p:ℤ) ∣ (p^M : ℕ) := by push_cast; exact dvd_pow_self _ (by omega)
      have h3 := h2.trans this
      have h4 : (p:ℤ) ∣ ((p * c.val : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
      have := (dvd_sub h4 h3)
      simp at this
      exact_mod_cast this
    · rintro ⟨t, rfl⟩
      push_cast; exact dvd_mul_right _ _
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [show N + 1 - 1 = N by omega]
  have F0 : ∀ y : ZMod (p^N), (Finset.univ.filter fun a : ZMod (p^(N+1)) => p ∣ a.val ∧ ((a.val / p : ℕ) : ZMod (p^N)) = y).card = 1 := by
    intro y
    have hpN : 0 < p^N := pow_pos hp N
    have : NeZero (p^N) := ⟨hpN.ne'⟩
    have hyv : y.val < p^N := ZMod.val_lt y
    have hlt : p * y.val < p^(N+1) := by
      calc p * y.val < p * p^N := Nat.mul_lt_mul_of_pos_left hyv hp
        _ = p^(N+1) := by ring
    rw [Finset.card_eq_one]
    refine ⟨((p * y.val : ℕ) : ZMod (p^(N+1))), ?_⟩
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨t, ht⟩, hty⟩
      rw [ht, Nat.mul_div_cancel_left _ hp] at hty
      have htlt : t < p^N := by
        have h := ZMod.val_lt b
        rw [ht] at h
        have h' : p * t < p * p^N := by
          calc p * t < p^(N+1) := h
            _ = p * p^N := by ring
        exact Nat.lt_of_mul_lt_mul_left h'
      have : t = y.val := by rw [← hty, ZMod.val_natCast_of_lt htlt]
      rw [← this, ← ht, ZMod.natCast_zmod_val]
    · rintro rfl
      rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel_left _ hp]
      simp
  have F1 : ∀ y : ZMod (p^N), (Finset.univ.filter fun a : ZMod (p^(N+1)) => ((a.val : ℕ) : ZMod (p^N)) = y).card = p := by
    intro y
    have hpN : 0 < p^N := pow_pos hp N
    have : NeZero (p^N) := ⟨hpN.ne'⟩
    have hyv : y.val < p^N := ZMod.val_lt y
    conv_rhs => rw [← Finset.card_range p]
    symm
    refine Finset.card_nbij' (fun t => ((y.val + p^N * t : ℕ) : ZMod (p^(N+1)))) (fun a => a.val / p^N) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio] at ht
      have hlt : y.val + p^N * t < p^(N+1) := by
        rw [pow_succ]; nlinarith
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [ZMod.val_natCast_of_lt hlt]; simp
    · intro a ha
      simp only [Finset.coe_range, Set.mem_Iio]
      have h : a.val < p^N * p := by
        calc a.val < p^(N+1) := ZMod.val_lt a
          _ = p^N * p := by ring
      rw [Nat.div_lt_iff_lt_mul hpN]; linarith
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio] at ht
      have hlt : y.val + p^N * t < p^(N+1) := by
        rw [pow_succ]; nlinarith
      simp only
      rw [ZMod.val_natCast_of_lt hlt]
      rw [Nat.add_mul_div_left _ _ hpN, Nat.div_eq_of_lt hyv]; simp
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
      have hmod : a.val % p^N = y.val := by
        rw [← ha, ZMod.val_natCast]
      simp only
      rw [← hmod, Nat.mod_add_div]
      simp
  obtain ⟨m', rfl⟩ := hm
  rw [Int.mul_ediv_cancel_left _ hpZ]
  obtain ⟨π, hπ⟩ : ∃ π : (Fin n → ZMod (p^(N+1))) → (Fin n → ZMod (p^N)),
      ∀ x j, π x j = (((if ν j = 0 then (x j).val / p else (x j).val) : ℕ) : ZMod (p^N)) :=
    ⟨_, fun _ _ => rfl⟩
  have hkey : ∀ x : Fin n → ZMod (p^(N+1)),
      (QuadForm.evalIn (ZMod (p^(N+1))) Q x = ((p * m' : ℤ) : ZMod (p^(N+1))) ∧
        (IsBadType (unimodularCoords ν) p (N+1) x ∧ ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p^(N+1))) ∣ x i)) ↔
      ((∀ j, ν j = 0 → p ∣ (x j).val) ∧
        (QuadForm.evalIn (ZMod (p^N)) (badIFormJ Q p ν) (π x) = (m' : ZMod (p^N)) ∧
          IsGoodType (unimodularCoords (nuI ν)) p N (π x))) := by
    intro x
    have hdx : ∀ j, (p : ZMod (p^(N+1))) ∣ x j ↔ p ∣ (x j).val := by
      intro j
      conv_lhs => rw [← ZMod.natCast_zmod_val (x j)]
      exact hdvd _ (by omega) _
    have hdπ : ∀ j, ν j = 1 → ((p : ZMod (p^N)) ∣ π x j ↔ p ∣ (x j).val) := by
      intro j hj
      rw [hπ x j]
      simp only [hj, one_ne_zero, if_false]
      exact hdvd N hN _
    have hT : (IsBadType (unimodularCoords ν) p (N+1) x ∧ ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p^(N+1))) ∣ x i) ↔
        ((∀ j, ν j = 0 → p ∣ (x j).val) ∧ IsGoodType (unimodularCoords (nuI ν)) p N (π x)) := by
      constructor
      · rintro ⟨⟨hnz, hng⟩, i, hi1, hi⟩
        refine ⟨fun j hj => ?_, ?_, i, ?_, ?_⟩
        · by_contra h
          exact hng ⟨hnz, j, by simp [unimodularCoords, hj], by rwa [hdx]⟩
        · intro hz
          exact hi ((hdx i).2 ((hdπ i hi1).1 (hz i)))
        · rw [unimodularCoords, Finset.mem_filter]
          simp [nuI, hi1]
        · rwa [hdπ i hi1, ← hdx]
      · rintro ⟨hA, ⟨hnz, i, hi, hpi⟩⟩
        have hi1 : ν i = 1 := by
          have h : nuI ν i = 0 := by simpa [unimodularCoords] using hi
          unfold nuI at h
          split_ifs at h with h'
          omega
        have hxi : ¬ (p : ZMod (p^(N+1))) ∣ x i := by rwa [hdx, ← hdπ i hi1]
        refine ⟨⟨fun hz => hxi (hz i), fun ⟨_, j, hj, hpj⟩ => hpj ?_⟩, i, hi1, hxi⟩
        rw [hdx]
        exact hA j (by simpa [unimodularCoords] using hj)
    have hEq : (∀ j, ν j = 0 → p ∣ (x j).val) →
        (QuadForm.evalIn (ZMod (p^(N+1))) Q x = ((p * m' : ℤ) : ZMod (p^(N+1))) ↔
          QuadForm.evalIn (ZMod (p^N)) (badIFormJ Q p ν) (π x) = (m' : ZMod (p^N))) := by
      intro hA
      set X : Fin n → ℤ := fun j => ((x j).val : ℤ) with hX
      set Y : Fin n → ℤ := fun j => (((if ν j = 0 then (x j).val / p else (x j).val) : ℕ) : ℤ) with hY
      have hXY : ∀ j, X j = (if ν j = 0 then (p:ℤ) else 1) * Y j := by
        intro j
        simp only [hX, hY]
        by_cases h0 : ν j = 0
        · simp only [h0, if_true]
          rw [← Nat.cast_mul, Nat.mul_div_cancel' (hA j h0)]
        · simp [h0]
      have hx : QuadForm.evalIn (ZMod (p^(N+1))) Q x = ((QuadForm.evalIn ℤ Q X : ℤ) : ZMod _) := by
        rw [← hcast]; congr 1; funext j; simp [hX]
      have hπx : QuadForm.evalIn (ZMod (p^N)) (badIFormJ Q p ν) (π x) =
          ((QuadForm.evalIn ℤ (badIFormJ Q p ν) Y : ℤ) : ZMod _) := by
        rw [← hcast]; congr 1; funext j; rw [hπ x j]; exact (Int.cast_natCast _).symm
      rw [hx, hπx, hev X Y hXY, ZMod.intCast_eq_intCast_iff_dvd_sub,
        ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      rw [← mul_sub, pow_succ', Int.mul_dvd_mul_iff_left hpZ]
    constructor
    · rintro ⟨hE, hT'⟩
      obtain ⟨hA, hG⟩ := hT.1 hT'
      exact ⟨hA, (hEq hA).1 hE, hG⟩
    · rintro ⟨hA, hE', hG⟩
      exact ⟨(hEq hA).2 hE', hT.2 ⟨hA, hG⟩⟩
  unfold repCountOf
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  rw [Finset.filter_congr (fun x _ => hkey x)]
  rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ.filter fun y =>
      QuadForm.evalIn (ZMod (p^N)) (badIFormJ Q p ν) y = (m' : ZMod (p^N)) ∧
          IsGoodType (unimodularCoords (nuI ν)) p N y)
    (by intro x hx; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢; exact hx.2)]
  rw [Finset.sum_congr rfl (g := fun _ => p ^ ((Finset.univ.filter fun i => 1 ≤ ν i).card)) ?_,
    Finset.sum_const, smul_eq_mul, mul_comm]
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  let F : Fin n → ZMod (p^N) → Finset (ZMod (p^(N+1))) := fun j b =>
    Finset.univ.filter (fun a : ZMod (p^(N+1)) => (ν j = 0 → p ∣ a.val) ∧
      (((if ν j = 0 then a.val / p else a.val) : ℕ) : ZMod (p^N)) = b)
  have hF : ∀ j b, (F j b).card = if 1 ≤ ν j then p else 1 := by
    intro j b
    by_cases h0 : ν j = 0
    · have : ¬ 1 ≤ ν j := by omega
      simp only [F, h0, if_true, this, if_false, forall_const]
      exact F0 b
    · have : 1 ≤ ν j := by omega
      simp only [F, h0, if_false, this, if_true, IsEmpty.forall_iff, true_and]
      exact F1 b
  have hset : (Finset.univ.filter fun x : Fin n → ZMod (p^(N+1)) => (∀ j, ν j = 0 → p ∣ (x j).val) ∧
        (QuadForm.evalIn (ZMod (p^N)) (badIFormJ Q p ν) (π x) = (m' : ZMod (p^N)) ∧
          IsGoodType (unimodularCoords (nuI ν)) p N (π x))).filter (fun a => π a = y) =
      Fintype.piFinset (fun j => F j (y j)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, F]
    constructor
    · rintro ⟨⟨hA, _⟩, hxy⟩ j
      exact ⟨hA j, by rw [← hπ x j, hxy]⟩
    · intro h
      have hxy : π x = y := funext fun j => by rw [hπ x j]; exact (h j).2
      exact ⟨⟨fun j => (h j).1, hxy ▸ hy⟩, hxy⟩
  rw [hset, Fintype.card_piFinset]
  simp_rw [hF]
  rw [← Finset.prod_filter, Finset.prod_const]

/-- **Bad type II reduction for block-diagonal forms** (Hanke 2004, §3, map $\pi_{B''}$, p. 360): for
$p^2 \mid m$ and $k \ge 3$, the Bad-type solutions with $\vec{x}_{S_1} \equiv \vec{0}$ number
$p^{2n - s_0 - s_1}$ times the solutions of $Q''(\vec{x}'') \equiv m/p^2 \pmod{p^{k-2}}$ with
$\vec{x}''_{S_2} \not\equiv \vec{0}$. Same proof as `repCountBadII_eq`, blockwise. -/
@[kb "hanke2004" "§3, map π_{B''}, p. 360"]
theorem repCountBadII_eq_J (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (m : ℤ) (k : ℕ) (hk : 3 ≤ k)
    (hm : (p : ℤ) ^ 2 ∣ m) :
    repCountOf Q p k m
        (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p ^ k)) ∣ x i) =
      p ^ (2 * n - (Finset.univ.filter fun i => ν i ≤ 1).card) *
        repCountOf (badIIFormJ Q p ν) p (k - 2) (m / p ^ 2)
          (fun y => ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p ^ (k - 2))) ∣ y i) := by
  classical
  have hp : p.Prime := Fact.out
  have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have E : ∀ (K : Type) [CommRing K] (Q : QuadForm ℤ n) (v : Fin n → ℤ),
      QuadForm.evalIn K Q (fun i => (v i : K)) = ((Q.eval v : ℤ) : K) := by
    intro K _ Q v
    simp only [QuadForm.eval, QuadForm.evalIn, Int.cast_sum, algebraMap_int_eq, eq_intCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> push_cast <;> rfl
  have X : ∀ k, 1 ≤ k → ∀ a : ZMod (p^k), (p : ZMod (p^k)) ∣ a ↔ p ∣ a.val := by
    intro k hk a
    have : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    constructor
    · rintro ⟨c, rfl⟩
      have : (p : ZMod (p^k)) * c = ((p * c.val : ℕ) : ZMod (p^k)) := by push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, ZMod.val_natCast, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]
      exact dvd_mul_right _ _
    · rintro ⟨t, ht⟩
      refine ⟨(t : ZMod (p^k)), ?_⟩
      rw [← ZMod.natCast_zmod_val a, ht]; push_cast; rfl
  have C : ∀ (i j : Fin n), i ≤ j → Q.coeff i j ≠ 0 → ν i = ν j ∧ (p:ℤ)^(ν i) ∣ Q.coeff i j := by
    intro i j hij h0
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
    rcases hij.lt_or_eq with hlt | rfl
    · by_cases hP : (i, j) ∈ P
      · obtain ⟨hν, ⟨b, hb, _⟩, _, _⟩ := h5 _ hP
        exact ⟨hν, ⟨b, hb⟩⟩
      · exact absurd (h4 i j hlt hP) h0
    · refine ⟨rfl, ?_⟩
      by_cases hp : IsPaired P i
      · obtain ⟨e, he, h | h⟩ := hp
        · obtain ⟨_, _, hd, _⟩ := h5 e he
          subst h; exact hd
        · obtain ⟨hν, _, _, hd⟩ := h5 e he
          subst h; rw [← hν]; exact hd
      · obtain ⟨u, hu, _⟩ := h6 i hp
        exact ⟨u, hu⟩
  have I : ∀ Y : Fin n → ℤ,
      Q.eval (fun i => ((if ν i ≤ 1 then p else 1 : ℕ) : ℤ) * Y i) = (p:ℤ)^2 * (badIIFormJ Q p ν).eval Y := by
    intro Y
    simp only [QuadForm.eval, QuadForm.evalIn, Finset.mul_sum, algebraMap_int_eq, eq_intCast, Int.cast_id]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≤ j
    · simp only [hij, if_true, badIIFormJ, QuadForm.ofUpper, Matrix.of_apply]
      by_cases h0 : Q.coeff i j = 0
      · simp [h0]
      obtain ⟨hν, hd⟩ := C i j hij h0
      by_cases h2 : 2 ≤ ν i
      · have h2' : ¬ ν i ≤ 1 := by omega
        have h2'' : ¬ ν j ≤ 1 := by omega
        have hd2 : (p:ℤ)^2 ∣ Q.coeff i j := (pow_dvd_pow _ h2).trans hd
        simp only [h2, h2', h2'', if_true, if_false, Nat.cast_one, one_mul]
        rw [← mul_assoc, ← mul_assoc, Int.mul_ediv_cancel' hd2]
      · have h2' : ν i ≤ 1 := by omega
        have h2'' : ν j ≤ 1 := by omega
        simp only [h2, h2', h2'', if_true, if_false]
        ring
    · simp [hij]
  have L : ∀ (M s N c : ℕ) (hs : 0 < s) (hN : 0 < N) (hM : M = s * N * c) [NeZero M] (b : ZMod N),
      (Finset.univ.filter (fun a : ZMod M => s ∣ a.val ∧ ((a.val / s : ℕ) : ZMod N) = b)).card = c := by
    intro M s N c hs hN hM _ b
    have : NeZero N := ⟨hN.ne'⟩
    have h1 : (Finset.univ.filter (fun a : ZMod M => s ∣ a.val ∧ ((a.val / s : ℕ) : ZMod N) = b)).card
        = ((Finset.range M).filter (fun v => s ∣ v ∧ (v / s) % N = b.val)).card := by
      apply Finset.card_nbij' (fun a : ZMod M => a.val) (fun v : ℕ => (v : ZMod M))
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_range] at ha ⊢
        refine ⟨ZMod.val_lt a, ha.1, ?_⟩
        rw [← ha.2, ZMod.val_natCast]
      · intro v hv
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_range] at hv ⊢
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv.1]
        refine ⟨hv.2.1, ?_⟩
        rw [← ZMod.natCast_zmod_val b, ZMod.natCast_eq_natCast_iff', hv.2.2, Nat.mod_eq_of_lt (ZMod.val_lt b)]
      · intro a _; simp
      · intro v hv
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hv
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt hv.1]
    rw [h1]
    have h2 : (Finset.range M).filter (fun v => s ∣ v ∧ (v / s) % N = b.val)
        = (Finset.range c).image (fun t => s * (b.val + N * t)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hv, ⟨w, rfl⟩, hw⟩
        rw [Nat.mul_div_cancel_left _ hs] at hw
        refine ⟨w / N, ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hN]
          rw [hM, mul_assoc] at hv
          have := Nat.lt_of_mul_lt_mul_left hv
          linarith [mul_comm N c]
        · rw [← hw, Nat.mod_add_div]
      · rintro ⟨t, ht, rfl⟩
        have hb := ZMod.val_lt b
        refine ⟨?_, dvd_mul_right _ _, ?_⟩
        · rw [hM, mul_assoc]
          apply Nat.mul_lt_mul_of_pos_left _ hs
          nlinarith
        · rw [Nat.mul_div_cancel_left _ hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    rw [h2, Finset.card_image_of_injective, Finset.card_range]
    intro t t' h
    simp only at h
    have := Nat.eq_of_mul_eq_mul_left hs h
    have := Nat.eq_of_mul_eq_mul_left hN (by omega : N * t = N * t')
    exact this
  -- main
  obtain ⟨m', rfl⟩ := hm
  rw [Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hpz)]
  have : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p^(k-2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set s : Fin n → ℕ := fun i => if ν i ≤ 1 then p else 1 with hs
  set φ : (Fin n → ZMod (p^k)) → (Fin n → ZMod (p^(k-2))) :=
    fun x i => (((x i).val / s i : ℕ) : ZMod (p^(k-2))) with hφ
  set R : (Fin n → ZMod (p^(k-2))) → Prop := fun y =>
    QuadForm.evalIn (ZMod (p^(k-2))) (badIIFormJ Q p ν) y = ((m' : ℤ) : ZMod (p^(k-2))) ∧
      ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p ^ (k - 2))) ∣ y i with hR
  have hA : ∀ x : Fin n → ZMod (p^k),
      (QuadForm.evalIn (ZMod (p^k)) Q x = (((p:ℤ)^2 * m' : ℤ) : ZMod (p^k)) ∧
        (IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p ^ k)) ∣ x i)) ↔
      (∀ i, s i ∣ (x i).val) ∧ R (φ x) := by
    intro x
    have hsD : ∀ i, s i ∣ (x i).val ↔ (ν i ≤ 1 → (p : ZMod (p^k)) ∣ x i) := by
      intro i; rw [X k (by omega)]; simp only [hs]; split_ifs with h <;> simp [h]
    have hφ2 : ∀ i, 2 ≤ ν i → ((p : ZMod (p^(k-2))) ∣ φ x i ↔ (p : ZMod (p^k)) ∣ x i) := by
      intro i hi
      have : s i = 1 := by simp only [hs]; rw [if_neg (by omega)]
      rw [X k (by omega), X (k-2) (by omega)]
      simp only [hφ, this, Nat.div_one, ZMod.val_natCast]
      exact Nat.dvd_mod_iff (dvd_pow_self p (by omega))
    have hT : (IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p ^ k)) ∣ x i) ↔
        (∀ i, ν i ≤ 1 → (p : ZMod (p^k)) ∣ x i) ∧ ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p^k)) ∣ x i := by
      simp only [IsBadType, IsGoodType, IsZeroType, unimodularCoords, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hnz, hng⟩, h1⟩
        have h0 : ∀ i, ν i = 0 → (p : ZMod (p^k)) ∣ x i := by
          intro i hi; by_contra hc; exact hng ⟨hnz, i, hi, hc⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
          exacts [h0 i h, h1 i h]
        · push_neg at hnz; obtain ⟨i, hi⟩ := hnz
          refine ⟨i, ?_, hi⟩
          by_contra hc
          rcases (by omega : ν i = 0 ∨ ν i = 1) with h | h
          exacts [hi (h0 i h), hi (h1 i h)]
      · rintro ⟨h1, i, hi, hc⟩
        refine ⟨⟨fun h => hc (h i), fun ⟨_, j, hj, hc'⟩ => hc' (h1 j (by omega))⟩, fun j hj => h1 j (by omega)⟩
    have hEv : (∀ i, s i ∣ (x i).val) → (QuadForm.evalIn (ZMod (p^k)) Q x = (((p:ℤ)^2 * m' : ℤ) : ZMod (p^k)) ↔
        QuadForm.evalIn (ZMod (p^(k-2))) (badIIFormJ Q p ν) (φ x) = ((m' : ℤ) : ZMod (p^(k-2)))) := by
      intro hD
      set Y : Fin n → ℤ := fun i => (((x i).val / s i : ℕ) : ℤ) with hY
      have hx : x = fun i => ((((s i : ℕ) : ℤ) * Y i : ℤ) : ZMod (p^k)) := by
        funext i
        simp only [hY]
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (hD i), Int.cast_natCast, ZMod.natCast_zmod_val]
      have hy : φ x = fun i => ((Y i : ℤ) : ZMod (p^(k-2))) := by
        funext i; simp only [hφ, hY, Int.cast_natCast]
      rw [hy, E (ZMod (p^(k-2))) _ Y, hx, E (ZMod (p^k)) Q, I Y]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub, ← mul_sub]
      have hpk : ((p^k : ℕ) : ℤ) = (p:ℤ)^2 * ((p^(k-2) : ℕ) : ℤ) := by
        push_cast; rw [← pow_add]; congr 1; omega
      rw [hpk, mul_dvd_mul_iff_left (pow_ne_zero 2 hpz)]
    rw [hT]
    constructor
    · rintro ⟨hE, h1, i, hi, hc⟩
      have hD : ∀ i, s i ∣ (x i).val := fun i => (hsD i).2 (h1 i)
      exact ⟨hD, (hEv hD).1 hE, i, hi, (hφ2 i hi).not.2 hc⟩
    · rintro ⟨hD, hE, i, hi, hc⟩
      exact ⟨(hEv hD).2 hE, fun j => (hsD j).1 (hD j), i, hi, (hφ2 i hi).not.1 hc⟩
  have hRHS : repCountOf (badIIFormJ Q p ν) p (k - 2) m'
      (fun y => ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p ^ (k - 2))) ∣ y i) = (Finset.univ.filter R).card := by
    unfold repCountOf
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hLHS : repCountOf Q p k ((p:ℤ)^2 * m')
        (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p ^ k)) ∣ x i) =
      (Finset.univ.filter (fun x => (∀ i, s i ∣ (x i).val) ∧ R (φ x))).card := by
    unfold repCountOf
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hA x
  rw [hRHS, hLHS]
  rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ.filter R) (by
    intro x hx; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢; exact hx.2)]
  rw [Finset.sum_const_nat (m := p ^ (2 * n - (Finset.univ.filter fun i => ν i ≤ 1).card)), mul_comm]
  intro y hy
  have hfib : (Finset.univ.filter (fun x => (∀ i, s i ∣ (x i).val) ∧ R (φ x))).filter (fun x => φ x = y)
      = Fintype.piFinset (fun i => Finset.univ.filter (fun a : ZMod (p^k) => s i ∣ a.val ∧ ((a.val / s i : ℕ) : ZMod (p^(k-2))) = y i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    constructor
    · rintro ⟨⟨hD, _⟩, rfl⟩ i; exact ⟨hD i, rfl⟩
    · intro h
      have hxy : φ x = y := funext fun i => (h i).2
      exact ⟨⟨fun i => (h i).1, hxy ▸ hy⟩, hxy⟩
  have hpk2 : p^k = p^2 * p^(k-2) := by rw [← pow_add]; congr 1; omega
  rw [hfib, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun i _ => L (p^k) (s i) (p^(k-2)) (if ν i ≤ 1 then p else p^2)
    (by simp only [hs]; split_ifs <;> simp [hp.pos]) (pow_pos hp.pos _)
    (by simp only [hs]; split_ifs <;> rw [hpk2] <;> ring) (y i))]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, ← pow_mul, ← pow_add]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => ν i ≤ 1)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

end QuadFormsKB.LocalDensity
