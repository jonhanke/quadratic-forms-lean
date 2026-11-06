/-
# The 2-adic density of an odd unimodular form: first pieces

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264, §12, p. 281 (bibliography key `conwaysloane1988`).

Toward the input `PMassUnimodularTwoTypeI` (formula (3) for one odd unimodular constituent), via the splitting
$O \perp M$ of `TwoAdicOddSplit.lean`.

**Proves**
* `intMat_sq_mod_two`: a list of blocks $u x^2$ of exponent $0$ is the identity modulo $2$ (the hypothesis of
  `alphaP_blk_odd`);
* `exists_sq_of_mod8`: an integer $c \equiv 1 \pmod 8$ is a square modulo every $2^k$, $k \ge 3$;
* `card_sq_eq`: modulo $2^r$, $r \ge 3$, $x^2 = c$ has $4$ solutions if $c \equiv 1 \pmod 8$ and none if $c$ is odd
  and $c \not\equiv 1 \pmod 8$.
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicOddSplit
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicOddBase
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRhoEven

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Blocks $u x^2$ are the identity modulo $2$ -/

theorem intMat_sq_mod_two : ∀ L : List DyBlock, (∀ c ∈ L, c.Valid) → (∀ c ∈ L, blockExp c = 0) →
    (∀ c ∈ L, IsSqBlock c) → (intMat L).map (Int.castRingHom (ZMod 2)) = 1
  | [], _, _, _ => by ext i; exact i.elim0
  | c :: L, hv, he, hs => by
    have ih := intMat_sq_mod_two L (fun x hx => hv x (by simp [hx])) (fun x hx => he x (by simp [hx]))
      (fun x hx => hs x (by simp [hx]))
    cases c with
    | hyp e => exact absurd (hs (.hyp e) (by simp)) id
    | ell e => exact absurd (hs (.ell e) (by simp)) id
    | sq e u =>
      obtain rfl : e = 0 := he (.sq e u) (by simp)
      have hu := valid_odd (hv (.sq 0 u) (by simp))
      show (orthSumMat (bInt (.sq 0 u)) (intMat L)).map (Int.castRingHom (ZMod 2)) = 1
      rw [orthSumMat_map _ (map_zero _), ih]
      have hb : (bInt (.sq 0 u)).map (Int.castRingHom (ZMod 2)) = 1 := by
        ext i j
        fin_cases i; fin_cases j
        show ((2 ^ (0 : ℤ).toNat * u : ℤ) : ZMod 2) = 1
        simp only [Int.toNat_zero, pow_zero, one_mul]
        obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k + 1 := ⟨u / 2, by omega⟩
        push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring
      rw [hb]
      ext i j
      induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j => rw [orthSumG_cc]; simp [Matrix.one_apply, Fin.castAdd_inj]
        | right j => rw [orthSumG_cn]; simp [Matrix.one_apply, Fin.ext_iff]; omega
      | right i =>
        induction j using Fin.addCases with
        | left j => rw [orthSumG_nc]; simp [Matrix.one_apply, Fin.ext_iff]; omega
        | right j => rw [orthSumG_nn]; simp [Matrix.one_apply, Fin.natAdd_inj]

/-! ### Square roots modulo $2^r$ -/

theorem exists_sq_of_mod8 {c : ℤ} (hc : (8 : ℤ) ∣ c - 1) :
    ∀ k : ℕ, 3 ≤ k → ∃ s : ℤ, ¬ 2 ∣ s ∧ (2 : ℤ) ^ k ∣ s ^ 2 - c := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨1, by decide, ?_⟩
    have : (1 : ℤ) ^ 2 - c = -(c - 1) := by ring
    rw [this]; exact (dvd_neg).mpr (by simpa using hc)
  | succ k hk ih =>
    obtain ⟨s, hs, m, hm⟩ := ih
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · obtain ⟨m', rfl⟩ := Int.dvd_of_emod_eq_zero h
      exact ⟨s, hs, m', by rw [hm, pow_succ]; ring⟩
    · refine ⟨s + 2 ^ (k - 1), ?_, ?_⟩
      · rintro ⟨t, ht⟩
        apply hs
        refine ⟨t - 2 ^ (k - 2), ?_⟩
        have : (2 : ℤ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
        linarith
      · have hsodd : ∃ s', s = 2 * s' + 1 := ⟨s / 2, by omega⟩
        obtain ⟨s', rfl⟩ := hsodd
        have hm' : ∃ m', m = 2 * m' + 1 := ⟨m / 2, by omega⟩
        obtain ⟨m', rfl⟩ := hm'
        have e1 : (2 : ℤ) ^ (k - 1) * 2 = 2 ^ k := by rw [← pow_succ]; congr 1; omega
        have e2 : (2 : ℤ) ^ (k - 1) * 2 ^ (k - 1) = 2 ^ (k + 1) * 2 ^ (k - 3) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        refine ⟨(m' + s' + 1) + 2 ^ (k - 3), ?_⟩
        have : (2 * s' + 1 + 2 ^ (k - 1)) ^ 2 - c = ((2 * s' + 1) ^ 2 - c) + 2 ^ (k - 1) * 2 * (2 * s' + 1) +
            2 ^ (k - 1) * 2 ^ (k - 1) := by ring
        rw [this, hm, e1, e2, pow_succ]
        ring

section Sq

variable {r : ℕ}

/-- $x^2 = \sigma^2$ has $4$ solutions modulo $2^r$ for a unit $\sigma$, $r \ge 3$. -/
theorem card_sq_eq_sq (hr : 3 ≤ r) {σ : ZMod (2 ^ r)} (hσ : IsUnit σ) :
    Nat.card {x : ZMod (2 ^ r) // x * x = σ * σ} = 4 := by
  rw [← card_sq_eq_one hr]
  obtain ⟨w, rfl⟩ := hσ
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1 * ↑w⁻¹, by rw [show x.1 * ↑w⁻¹ * (x.1 * ↑w⁻¹) = (x.1 * x.1) * (↑w⁻¹ * ↑w⁻¹) by ring,
        x.2, show (w : ZMod (2 ^ r)) * w * (↑w⁻¹ * ↑w⁻¹) = (w * ↑w⁻¹) * (w * ↑w⁻¹) by ring, Units.mul_inv,
        one_mul]⟩
      invFun := fun y => ⟨y.1 * w, by rw [show y.1 * w * (y.1 * w) = (y.1 * y.1) * (w * w) by ring, y.2, one_mul]⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }

/-- $x^2 = c$ has $4$ solutions modulo $2^r$ if $c \equiv 1 \pmod 8$. -/
theorem card_sq_eq_of_mod8 (hr : 3 ≤ r) {c : ℤ} (hc : (8 : ℤ) ∣ c - 1) :
    Nat.card {x : ZMod (2 ^ r) // x * x = (c : ZMod (2 ^ r))} = 4 := by
  obtain ⟨s, hs, hsc⟩ := exists_sq_of_mod8 hc r hr
  have e : (c : ZMod (2 ^ r)) = (s : ZMod (2 ^ r)) * s := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub c (s ^ 2) (2 ^ r)).mpr (by simpa using hsc)
    rw [this]; push_cast; ring
  rw [e]
  exact card_sq_eq_sq hr (isUnit_odd hs)

/-- No solutions if $c$ is odd and $c \not\equiv 1 \pmod 8$. -/
theorem card_sq_eq_of_not_mod8 (hr : 3 ≤ r) {c : ℤ} (hc : ¬ 2 ∣ c) (hc8 : ¬ (8 : ℤ) ∣ c - 1) :
    Nat.card {x : ZMod (2 ^ r) // x * x = (c : ZMod (2 ^ r))} = 0 := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx⟩ => hc8 ?_⟩
  have hx' : ((x.val * x.val : ℤ) : ZMod (2 ^ r)) = (c : ZMod (2 ^ r)) := by push_cast; simpa using hx
  have h := (ZMod.intCast_eq_intCast_iff_dvd_sub c _ (2 ^ r)).mp hx'.symm
  have h8 : (8 : ℤ) ∣ (x.val : ℤ) * x.val - c := (by
    have : (8 : ℤ) ∣ (2 ^ r : ℕ) := by push_cast; exact (show (8 : ℤ) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 hr
    exact this.trans (by simpa using h))
  have hodd : ¬ 2 ∣ (x.val : ℤ) := fun h2 => hc (by
    obtain ⟨k, hk⟩ := h2
    obtain ⟨m, hm⟩ := h8
    exact ⟨2 * k * k - 4 * m, by rw [hk] at hm; linarith⟩)
  obtain ⟨k, hk⟩ : ∃ k, (x.val : ℤ) = 2 * k + 1 := ⟨(x.val : ℤ) / 2, by omega⟩
  rw [hk] at h8
  obtain ⟨m, hm⟩ := h8
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
  exact ⟨j - m, by linear_combination (-1 : ℤ) * hm + 4 * hj⟩

end Sq

/-! ### $\alpha_2(\mathrm{diag}(u, v))$: the orbit count -/

section Diag2

variable {r : ℕ} {u v : ZMod (2 ^ r)}

/-- The second columns that complete a first column $(a, c)$ with $ua^2 + vc^2 = u$: they are $t(-vc, ua)$ with
$(ut)^2 = 1$, so there are $4$ of them. -/
theorem card_second_col (hr : 3 ≤ r) (hu : IsUnit u) (hv : IsUnit v) {a c : ZMod (2 ^ r)}
    (hQ : u * a * a + v * c * c = u) :
    Nat.card {q : ZMod (2 ^ r) × ZMod (2 ^ r) //
      u * a * q.1 + v * c * q.2 = 0 ∧ u * q.1 * q.1 + v * q.2 * q.2 = v} = 4 := by
  obtain ⟨iu, hiu⟩ := hu.exists_right_inv
  obtain ⟨iv, hiv⟩ := hv.exists_right_inv
  rw [← card_sq_eq_one hr]
  refine Nat.card_congr
    { toFun := fun q => ⟨iu * (a * q.1.2 - c * q.1.1) * u, ?_⟩
      invFun := fun s => ⟨(-(v * c * (iu * s.1)), u * a * (iu * s.1)), ?_⟩
      left_inv := fun q => Subtype.ext ?_
      right_inv := fun s => Subtype.ext ?_ }
  · obtain ⟨⟨y0, y1⟩, h1, h2⟩ := q
    simp only at h1 h2 ⊢
    have e0 : y0 = -(v * c * (iu * (a * y1 - c * y0))) := by
      linear_combination (iu * a) * h1 + (-(iu * y0)) * hQ + (-y0) * hiu
    have e1 : y1 = u * a * (iu * (a * y1 - c * y0)) := by
      linear_combination (iu * c) * h1 + (-(iu * y1)) * hQ + (-y1) * hiu
    set t := iu * (a * y1 - c * y0)
    rw [e0, e1] at h2
    have h3 : (u * t * (u * t) - 1) * (v * u) = 0 := by
      linear_combination u * h2 - (v * u * t * t * u) * hQ
    have h4 := (hv.mul hu).mul_left_eq_zero.mp h3
    linear_combination h4
  · have hs := s.2
    constructor
    · ring
    · linear_combination (v * u * (iu * s.1) * (iu * s.1)) * hQ + (v * (u * iu) ^ 2) * hs +
        (v * (u * iu + 1)) * hiu
  · obtain ⟨⟨y0, y1⟩, h1, h2⟩ := q
    simp only at h1 h2 ⊢
    ext
    · simp only
      linear_combination -((iu * a) * h1 + (-(iu * y0)) * hQ + (-y0) * hiu) -
        (v * c * iu * (a * y1 - c * y0)) * hiu
    · simp only
      linear_combination -((iu * c) * h1 + (-(iu * y1)) * hQ + (-y1) * hiu) +
        (u * a * iu * (a * y1 - c * y0)) * hiu
  · simp only
    linear_combination (iu * iu * s.1 * u) * hQ + (s.1 * (u * iu + 1)) * hiu

theorem quad_diag2_apply (u v : ZMod (2 ^ r)) (X : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ r))) (i j : Fin 2) :
    (Xᵀ * !![u, 0; 0, v] * X) i j = u * X 0 i * X 0 j + v * X 1 i * X 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- **The orbit count**: $N_r(\mathrm{diag}(u, v)) = 4\,\#\{x : ux_0^2 + vx_1^2 = u\}$, $r \ge 3$. -/
theorem countN_diag2 (hr : 3 ≤ r) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    countN 2 r !![u, 0; 0, v] = 4 * Nat.card {p : ZMod (2 ^ r) × ZMod (2 ^ r) //
      (u : ZMod (2 ^ r)) * p.1 * p.1 + (v : ZMod (2 ^ r)) * p.2 * p.2 = u} := by
  have hD : (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod (2 ^ r))) =
      !![(u : ZMod (2 ^ r)), 0; 0, (v : ZMod (2 ^ r))] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  unfold countN
  rw [hD]
  set P := {p : ZMod (2 ^ r) × ZMod (2 ^ r) //
      (u : ZMod (2 ^ r)) * p.1 * p.1 + (v : ZMod (2 ^ r)) * p.2 * p.2 = u}
  set F : P → Type := fun p => {q : ZMod (2 ^ r) × ZMod (2 ^ r) //
      (u : ZMod (2 ^ r)) * p.1.1 * q.1 + (v : ZMod (2 ^ r)) * p.1.2 * q.2 = 0 ∧
        (u : ZMod (2 ^ r)) * q.1 * q.1 + (v : ZMod (2 ^ r)) * q.2 * q.2 = v}
  have hF : ∀ p : P, Nat.card (F p) = 4 := fun p =>
    card_second_col hr (isUnit_odd hu) (isUnit_odd hv) p.2
  have e : {X : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ r)) //
      Xᵀ * !![(u : ZMod (2 ^ r)), 0; 0, (v : ZMod (2 ^ r))] * X = !![(u : ZMod (2 ^ r)), 0; 0, (v : ZMod (2 ^ r))]} ≃
      Σ p : P, F p :=
    { toFun := fun X => ⟨⟨(X.1 0 0, X.1 1 0), by
          have := congrFun (congrFun X.2 0) 0; rw [quad_diag2_apply] at this; simpa using this⟩,
        ⟨(X.1 0 1, X.1 1 1), by
          have h01 := congrFun (congrFun X.2 0) 1; rw [quad_diag2_apply] at h01
          have h11 := congrFun (congrFun X.2 1) 1; rw [quad_diag2_apply] at h11
          exact ⟨by simpa using h01, by simpa using h11⟩⟩⟩
      invFun := fun pq => ⟨!![pq.1.1.1, pq.2.1.1; pq.1.1.2, pq.2.1.2], by
          ext i j
          rw [quad_diag2_apply]
          have h0 := pq.1.2
          have h1 := pq.2.2.1
          have h2 := pq.2.2.2
          fin_cases i <;> fin_cases j <;> simp <;>
            first | linear_combination h0 | linear_combination h1 | linear_combination h2⟩
      left_inv := fun X => Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
      right_inv := fun pq => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl fun p _ => hF p, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]

end Diag2

/-! ### Counting the vectors of norm $u$ -/

section Count2

variable {r : ℕ}

theorem eight_dvd_pow (hr : 3 ≤ r) : 8 ∣ 2 ^ r := (show 8 = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 hr

/-- Reduction modulo $8$. -/
def red8 (hr : 3 ≤ r) : ZMod (2 ^ r) →+* ZMod 8 := ZMod.castHom (eight_dvd_pow hr) (ZMod 8)

theorem red8_surj (hr : 3 ≤ r) : Function.Surjective (red8 hr) := ZMod.ringHom_surjective _

theorem red8_val (hr : 3 ≤ r) (e : ZMod (2 ^ r)) : red8 hr e = ((e.val : ℕ) : ZMod 8) := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  unfold red8; rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem zmod8_unit_sq_val : ∀ z : ZMod 8, (∃ w, z * w = 1) → z * z = 1 := by decide

/-- The units $a$ with $a^2 = e$: $4$ if $e \equiv 1 \pmod 8$, none otherwise. -/
theorem card_unit_sq (hr : 3 ≤ r) (e : ZMod (2 ^ r)) :
    Nat.card {a : ZMod (2 ^ r) // IsUnit a ∧ a * a = e} = if red8 hr e = 1 then 4 else 0 := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  split_ifs with h
  · have hv : (8 : ℤ) ∣ ((e.val : ℕ) : ℤ) - 1 := by
      rw [red8_val] at h
      have h' : ((e.val : ℕ) : ZMod 8) = ((1 : ℕ) : ZMod 8) := by simpa using h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      have : e.val % 8 = 1 := by simpa using h'
      omega
    have he : e = (((e.val : ℕ) : ℤ) : ZMod (2 ^ r)) := by simp
    rw [← card_sq_eq_of_mod8 hr hv, ← he]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.2.2⟩
        invFun := fun a => ⟨a.1, ?_, a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
    have hodd : ¬ 2 ∣ (((e.val : ℕ) : ℤ)) := by omega
    have hu : IsUnit e := by rw [he]; exact isUnit_odd hodd
    rw [← a.2] at hu
    exact isUnit_of_mul_isUnit_left hu
  · rw [Nat.card_eq_zero]; left
    refine ⟨fun ⟨a, ha, hae⟩ => h ?_⟩
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    rw [← hae, map_mul]
    exact zmod8_unit_sq_val _ ⟨red8 hr b, by rw [← map_mul, hb, map_one]⟩

/-- Proportions of residues modulo $8$. -/
theorem card_red8 (hr : 3 ≤ r) (P : ZMod 8 → Prop) [DecidablePred P] :
    ((Finset.univ.filter fun c : ZMod (2 ^ r) => P (red8 hr c)).card : ℝ) =
      2 ^ r * ((Finset.univ.filter P).card : ℝ) / 8 := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  have h := card_comp_div (red8 hr).toAddMonoidHom (red8_surj hr) P
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.card] at h
  have h2 : ((2 ^ r : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff h2 (by norm_num)] at h
  push_cast at h
  rw [eq_div_iff (by norm_num)]
  linarith

theorem zmod8_unit_odd : ∀ z : ZMod 8, (∃ t, z * t = 1) → z.val % 2 = 1 := by decide

theorem isUnit_iff_red8 (hr : 3 ≤ r) (a : ZMod (2 ^ r)) : IsUnit a ↔ ∃ t, red8 hr a * t = 1 := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    exact ⟨red8 hr b, by rw [← map_mul, hb, map_one]⟩
  · intro h
    have h1 := zmod8_unit_odd _ h
    rw [red8_val, ZMod.val_natCast] at h1
    have h2 : ¬ 2 ∣ ((a.val : ℕ) : ℤ) := by omega
    have := isUnit_odd (r := r) h2
    simpa using this

theorem zmod8_parity : ∀ x y k : ZMod 8, (∃ t, k * t = 1) → x * x + k * (y * y) = 1 →
    ((∃ t, x * t = 1) ↔ ¬ ∃ t, y * t = 1) := by decide

theorem unit_iff_not_unit (hr : 3 ≤ r) {w a c : ZMod (2 ^ r)} (hw : IsUnit w) (h : a * a + w * c * c = 1) :
    IsUnit a ↔ ¬ IsUnit c := by
  rw [isUnit_iff_red8 hr, isUnit_iff_red8 hr]
  refine zmod8_parity _ _ _ ((isUnit_iff_red8 hr w).mp hw) ?_
  have := congrArg (red8 hr) h
  simp only [map_add, map_mul, map_one] at this
  linear_combination this

theorem card_vec_A (hr : 3 ≤ r) (w : ZMod (2 ^ r)) :
    Nat.card {p : ZMod (2 ^ r) × ZMod (2 ^ r) // IsUnit p.1 ∧ p.1 * p.1 + w * p.2 * p.2 = 1} =
      4 * (Finset.univ.filter fun c : ZMod (2 ^ r) => red8 hr (1 - w * c * c) = 1).card := by
  classical
  have e : {p : ZMod (2 ^ r) × ZMod (2 ^ r) // IsUnit p.1 ∧ p.1 * p.1 + w * p.2 * p.2 = 1} ≃
      Σ c : ZMod (2 ^ r), {a : ZMod (2 ^ r) // IsUnit a ∧ a * a = 1 - w * c * c} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2.1, by linear_combination p.2.2⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2.1, by linear_combination q.2.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_unit_sq hr]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_vec_B (hr : 3 ≤ r) {w iw : ZMod (2 ^ r)} (hw : w * iw = 1) :
    Nat.card {p : ZMod (2 ^ r) × ZMod (2 ^ r) // IsUnit p.2 ∧ p.1 * p.1 + w * p.2 * p.2 = 1} =
      4 * (Finset.univ.filter fun a : ZMod (2 ^ r) => red8 hr (iw * (1 - a * a)) = 1).card := by
  classical
  have e : {p : ZMod (2 ^ r) × ZMod (2 ^ r) // IsUnit p.2 ∧ p.1 * p.1 + w * p.2 * p.2 = 1} ≃
      Σ a : ZMod (2 ^ r), {c : ZMod (2 ^ r) // IsUnit c ∧ c * c = iw * (1 - a * a)} :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2.1, by linear_combination iw * p.2.2 - (p.1.2 * p.1.2) * hw⟩
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2.1, by linear_combination w * q.2.2.2 + (1 - q.1 * q.1) * hw⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_unit_sq hr]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

/-- $\#\{(a, c) : a^2 + wc^2 = 1\} = |A| + |B|$, $a$ a unit in $A$, $c$ a unit in $B$. -/
theorem card_vec (hr : 3 ≤ r) {w iw : ZMod (2 ^ r)} (hw : w * iw = 1) :
    Nat.card {p : ZMod (2 ^ r) × ZMod (2 ^ r) // p.1 * p.1 + w * p.2 * p.2 = 1} =
      4 * (Finset.univ.filter fun c : ZMod (2 ^ r) => red8 hr (1 - w * c * c) = 1).card +
      4 * (Finset.univ.filter fun a : ZMod (2 ^ r) => red8 hr (iw * (1 - a * a)) = 1).card := by
  classical
  have hwu : IsUnit w := ⟨⟨w, iw, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  rw [← card_vec_A hr w, ← card_vec_B hr hw]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    fun p : ZMod (2 ^ r) × ZMod (2 ^ r) => p.1 * p.1 + w * p.2 * p.2 = 1) (fun p => IsUnit p.1)]
  congr 1
  · congr 1; ext p; simp [and_comm]
  · congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hn⟩; exact ⟨by_contra fun hc => hn ((unit_iff_not_unit hr hwu h).mpr hc), h⟩
    · rintro ⟨hc, h⟩; exact ⟨h, fun ha => (unit_iff_not_unit hr hwu h).mp ha hc⟩

end Count2

/-! ### The value of $\alpha_2(\mathrm{diag}(u, v))$ -/

section Value

variable {r : ℕ}

theorem zmod8_counts : ∀ w iw : ZMod 8, w * iw = 1 →
    (Finset.univ.filter fun c : ZMod 8 => 1 - w * c * c = 1).card +
      (Finset.univ.filter fun a : ZMod 8 => iw * (1 - a * a) = 1).card =
      if w = 1 ∨ w = 5 then 4 else 2 := by decide

theorem zmod8_w_iff : ∀ u v iu : ZMod 8, u * iu = 1 →
    ((v * iu = 1 ∨ v * iu = 5) ↔ (u - v = 0 ∨ u - v = 4)) := by decide

theorem four_dvd_iff_zmod8 (x : ℤ) : (4 : ℤ) ∣ x ↔ ((x : ZMod 8) = 0 ∨ (x : ZMod 8) = 4) := by
  have hm : (((x % 8 : ℤ)) : ZMod 8) = (x : ZMod 8) := by exact_mod_cast ZMod.intCast_mod x 8
  rw [← hm]
  have h0 : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
  have h1 : x % 8 < 8 := Int.emod_lt_of_pos x (by norm_num)
  have key : ∀ t : ℤ, 0 ≤ t → t < 8 → ((((t : ℤ) : ZMod 8) = 0 ∨ ((t : ℤ) : ZMod 8) = 4) ↔ t = 0 ∨ t = 4) := by
    intro t ht0 ht1
    interval_cases t <;> decide
  rw [key _ h0 h1]
  omega

/-- $\#\{(x_0, x_1) : ux_0^2 + vx_1^2 = u\} = 2^r$ or $2^{r+1}$ modulo $2^r$, $r \ge 3$, the latter iff
$u \equiv v \pmod 4$. -/
theorem card_norm_eq (hr : 3 ≤ r) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    (Nat.card {p : ZMod (2 ^ r) × ZMod (2 ^ r) //
      (u : ZMod (2 ^ r)) * p.1 * p.1 + (v : ZMod (2 ^ r)) * p.2 * p.2 = u} : ℝ) =
      2 ^ r * (if (4 : ℤ) ∣ u - v then 2 else 1) := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  obtain ⟨iu, hiu⟩ := (isUnit_odd (r := r) hu).exists_right_inv
  obtain ⟨iv, hiv⟩ := (isUnit_odd (r := r) hv).exists_right_inv
  set w := (v : ZMod (2 ^ r)) * iu with hwdef
  have hw : w * ((u : ZMod (2 ^ r)) * iv) = 1 := by
    rw [hwdef]; linear_combination ((v : ZMod (2 ^ r)) * iv) * hiu + hiv
  have e : {p : ZMod (2 ^ r) × ZMod (2 ^ r) //
      (u : ZMod (2 ^ r)) * p.1 * p.1 + (v : ZMod (2 ^ r)) * p.2 * p.2 = u} ≃
      {p : ZMod (2 ^ r) × ZMod (2 ^ r) // p.1 * p.1 + w * p.2 * p.2 = 1} :=
    Equiv.subtypeEquivRight fun p => by
      constructor
      · intro h; rw [hwdef]; linear_combination iu * h + (1 - p.1 * p.1) * hiu
      · intro h; rw [hwdef] at h; linear_combination (u : ZMod (2 ^ r)) * h - ((v : ZMod (2 ^ r)) * p.2 * p.2) * hiu
  rw [Nat.card_congr e, card_vec hr hw]
  have f1 : ((Finset.univ.filter fun c : ZMod (2 ^ r) => red8 hr (1 - w * c * c) = 1).card : ℝ) =
      2 ^ r * ((Finset.univ.filter fun z : ZMod 8 => 1 - red8 hr w * z * z = 1).card : ℝ) / 8 := by
    rw [← card_red8 hr (fun z => 1 - red8 hr w * z * z = 1)]
    congr 2; ext c; simp [map_sub, map_mul]
  have f2 : ((Finset.univ.filter fun a : ZMod (2 ^ r) => red8 hr ((u * iv) * (1 - a * a)) = 1).card : ℝ) =
      2 ^ r * ((Finset.univ.filter fun z : ZMod 8 => red8 hr (u * iv) * (1 - z * z) = 1).card : ℝ) / 8 := by
    rw [← card_red8 hr (fun z => red8 hr (u * iv) * (1 - z * z) = 1)]
    congr 2; ext c; simp [map_sub, map_mul]
  have hsum := zmod8_counts (red8 hr w) (red8 hr (u * iv)) (by rw [← map_mul, hw, map_one])
  have hw8 : (red8 hr w = 1 ∨ red8 hr w = 5) ↔ (4 : ℤ) ∣ u - v := by
    rw [four_dvd_iff_zmod8]
    push_cast
    have h8 := zmod8_w_iff (u : ZMod 8) (v : ZMod 8) (red8 hr iu) (by
      rw [← map_intCast (red8 hr) u, ← map_mul, hiu, map_one])
    rw [hwdef, map_mul, map_intCast]
    exact h8
  push_cast
  rw [f1, f2]
  by_cases h : (4 : ℤ) ∣ u - v
  · rw [if_pos (hw8.mpr h)] at hsum
    have hsumR : ((Finset.univ.filter fun c : ZMod 8 => 1 - red8 hr w * c * c = 1).card : ℝ) +
        ((Finset.univ.filter fun a : ZMod 8 => red8 hr (u * iv) * (1 - a * a) = 1).card : ℝ) = 4 := by
      exact_mod_cast hsum
    rw [if_pos h]
    linear_combination ((2 : ℝ) ^ r / 2) * hsumR
  · rw [if_neg (fun h' => h (hw8.mp h'))] at hsum
    have hsumR : ((Finset.univ.filter fun c : ZMod 8 => 1 - red8 hr w * c * c = 1).card : ℝ) +
        ((Finset.univ.filter fun a : ZMod 8 => red8 hr (u * iv) * (1 - a * a) = 1).card : ℝ) = 2 := by
      exact_mod_cast hsum
    rw [if_neg h]
    linear_combination ((2 : ℝ) ^ r / 2) * hsumR

theorem countN_diag2_val (hr : 3 ≤ r) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    (countN 2 r !![u, 0; 0, v] : ℝ) = 2 ^ r * (if (4 : ℤ) ∣ u - v then 8 else 4) := by
  rw [countN_diag2 hr hu hv]
  push_cast
  rw [card_norm_eq hr hu hv]
  split_ifs <;> ring

/-- **$\alpha_2(\mathrm{diag}(u, v)) = 8$ if $u \equiv v \pmod 4$ and $4$ otherwise**, for odd $u$, $v$
(Conway–Sloane 1988, §12, p. 281). -/
@[kb "conwaysloane1988" "§12, p. 281 (the 2-adic density of an odd binary form)"]
theorem alphaP_diag2 {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    alphaP 2 !![u, 0; 0, v] = if (4 : ℤ) ∣ u - v then 8 else 4 := by
  have hs : (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hd : (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h
    have : u * v = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hu (h' ▸ dvd_zero _)
    · exact hv (h' ▸ dvd_zero _)
  obtain ⟨r0, h0⟩ := alphaP_stabilizes Nat.prime_two hs hd
  rw [← h0 (max r0 3) (le_max_left _ _), countN_diag2_val (le_max_right _ _) hu hv]
  have : (max r0 3) * (2 * (2 - 1) / 2) = max r0 3 := by norm_num
  rw [this]
  push_cast
  field_simp

end Value

end QuadFormsKB.ConwaySloane.Mass.Two
