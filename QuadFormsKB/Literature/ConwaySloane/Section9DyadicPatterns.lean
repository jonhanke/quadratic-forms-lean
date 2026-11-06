/-
# Conway–Sloane, Ch. 15, §9.7: Theorem 19 and Theorem 20 (c), (d) at the prime $2$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–394
(`conwaysloane1999`).

**Layer.** As in `Section9Dyadic.lean` and Cassels' Lemma 3.8: $L_2 = \gamma\mathbb Z_2^n$ over $\mathbb Q_2$, Gram
matrix `locGram Q v γ` of $B = 2Q$ (so $G_{kk} = 2Q(b_k)$), $\theta(O^+(L_2))$ = `localSpinorNormGroup`.

**Proves**
* Pattern lemmas (`pair_002` … `pair_033`, `five_bin_0/2/4`): for diagonal coefficients $(1, 2^bq', 2^cr')$,
  $0 \le b \le c \le 3$ (the six patterns not covered by Cassels' Lemma 3.8), resp. $(1, 2^dq')$,
  $d \in \{0,2,4\}$, there are admissible root vectors whose norm products are $\equiv 5$, resp. $\equiv 3, 7 \pmod 8$.
* `units_of_sorted`: three orthogonal basis vectors with exponents $\nu_i \le \nu_j \le \nu_k \le \nu_i + 3$ make every
  $2$-adic unit a spinor norm. `five_of_diff`: two orthogonal basis vectors whose exponents differ by $0, 2, 4$ put
  $5$ in $\theta$.
* `valued_det_le_of_not_units_mem_two_cs` (Thm. 20 (c), (41)), `exists_diag_basis_two_of_five_not_mem` (Thm. 19),
  `valued_det_le_of_five_not_mem_two` (Thm. 20 (d), (42)).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Dyadic

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Alg

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}
  (hQ : Q.Nondegenerate) (L : Lat ℚ n)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The root-vector property of the coefficients $(p, q, r)$: products of norms of admissible vectors lie in
$\theta$. -/
def RootPair (p q r : 𝔬) : Prop :=
  ∀ s t z s' t' z' : 𝔬, Adm p q r s t z → Adm p q r s' t' z' →
    InT hQ L ((Bf p q r s t z * Bf p q r s' t' z' : 𝔬) : Fv)

theorem two_ne_zero_o : (2 : 𝔬) ≠ 0 := by
  intro h
  have := congrArg (fun x : 𝔬 => (x : Fv)) h
  exact two_ne_zero (by simp at this)

theorem vle_of_eq {x B y a : 𝔬} (m : ℕ) (hy : IsUnit y) (hB : B = 2 ^ m * y) (hx : x = 2 ^ m * a) :
    Valued.v ((x : 𝔬) : Fv) ≤ Valued.v ((B : 𝔬) : Fv) := by
  have hy1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hy
  rw [hB, hx]
  push_cast
  rw [map_mul, map_mul, hy1, mul_one]
  exact (mul_le_mul' le_rfl (vle_one a)).trans_eq (mul_one _)

theorem adm_mk {p q r s t z y a1 a2 a3 : 𝔬} (m : ℕ) (hy : IsUnit y) (hB : Bf p q r s t z = 2 ^ m * y)
    (e1 : 2 * p * s = 2 ^ m * a1) (e2 : 2 * q * t = 2 ^ m * a2) (e3 : 2 * r * z = 2 ^ m * a3) :
    Adm p q r s t z := by
  refine ⟨?_, vle_of_eq m hy hB e1, vle_of_eq m hy hB e2, vle_of_eq m hy hB e3⟩
  rw [hB]
  exact mul_ne_zero (pow_ne_zero _ (two_ne_zero_o (v := v))) hy.ne_zero

theorem adm_unit {p q r s t z : 𝔬} (hy : IsUnit (Bf p q r s t z)) : Adm p q r s t z := by
  have h1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hy
  refine ⟨hy.ne_zero, ?_, ?_, ?_⟩ <;> rw [h1] <;> exact vle_one _

theorem rp_prod {p q r : 𝔬} (hR : RootPair hQ L p q r) {s t z s' t' z' : 𝔬} (hA : Adm p q r s t z)
    (hA' : Adm p q r s' t' z') (k : ℕ) {y y' : 𝔬}
    (hprod : Bf p q r s t z * Bf p q r s' t' z' = (2 ^ k) ^ 2 * (y * y')) :
    InT hQ L ((y * y' : 𝔬) : Fv) := by
  have := hR s t z s' t' z' hA hA'
  rw [hprod] at this
  have h2k : (((2 : 𝔬) ^ k : 𝔬) : Fv) ≠ 0 := fun h =>
    pow_ne_zero k (two_ne_zero_o (v := v)) (by exact_mod_cast h)
  have e : (((2 ^ k) ^ 2 * (y * y') : 𝔬) : Fv) = ((y * y' : 𝔬) : Fv) * (((2 ^ k : 𝔬)) : Fv) ^ 2 := by
    push_cast; ring
  rw [e] at this
  exact (InT.sq_mul_iff hQ L h2k).mp this

variable (v) in
/-- A pair of admissible vectors with residues multiplying to $5$. -/
def PairOK : Prop :=
  (∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5) ∧ (∃ β : 𝔬, InT hQ L (β : Fv) ∧ (Rl β 3 ∨ Rl β 7))

theorem units_of_pairOK (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (h : PairOK v hQ L) (u : Fvˣ)
    (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  obtain ⟨⟨α, h1, h2'⟩, ⟨β, h3, h4⟩⟩ := h
  exact units_of_pair hQ L h2 h1 h2' h3 h4 u hu

theorem r1 : Rl (1 : 𝔬) 1 := by simpa using Rl.natCast (v := v) 1
theorem r4 : Rl (4 : 𝔬) 4 := by simpa using Rl.natCast (v := v) 4
theorem r8 : Rl (8 : 𝔬) 8 := by simpa using Rl.natCast (v := v) 8

macro "bfr" : tactic => `(tactic| (unfold Bf; ring))

theorem adm0 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p q r y : 𝔬} (s t z : 𝔬) {ay : ZMod 8} (hy : Rl y ay)
    (hod : Od ay) (hB : Bf p q r s t z = y) : Adm p q r s t z :=
  adm_unit (by rw [hB]; exact hy.od_unit h2 hod)

theorem admm (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p q r y : 𝔬} (s t z : 𝔬) {ay : ZMod 8} (m : ℕ) (hy : Rl y ay)
    (hod : Od ay) (hB : Bf p q r s t z = 2 ^ m * y) (e1 : ∃ a, 2 * p * s = 2 ^ m * a)
    (e2 : ∃ a, 2 * q * t = 2 ^ m * a) (e3 : ∃ a, 2 * r * z = 2 ^ m * a) : Adm p q r s t z := by
  obtain ⟨a1, e1⟩ := e1
  obtain ⟨a2, e2⟩ := e2
  obtain ⟨a3, e3⟩ := e3
  exact adm_mk m (hy.od_unit h2 hod) hB e1 e2 e3

theorem rp_five {p q r : 𝔬} (hR : RootPair hQ L p q r) {s t z s' t' z' : 𝔬} (hA : Adm p q r s t z)
    (hA' : Adm p q r s' t' z') (k : ℕ) {y y' : 𝔬} {ay ay' : ZMod 8} (hy : Rl y ay) (hy' : Rl y' ay')
    (hprod : Bf p q r s t z * Bf p q r s' t' z' = (2 ^ k) ^ 2 * (y * y')) (h5 : ay * ay' = 5) :
    ∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5 :=
  ⟨y * y', rp_prod hQ L hR hA hA' k hprod, h5 ▸ hy.mul hy'⟩

theorem rp_37 {p q r : 𝔬} (hR : RootPair hQ L p q r) {s t z s' t' z' : 𝔬} (hA : Adm p q r s t z)
    (hA' : Adm p q r s' t' z') (k : ℕ) {y y' : 𝔬} {ay ay' : ZMod 8} (hy : Rl y ay) (hy' : Rl y' ay')
    (hprod : Bf p q r s t z * Bf p q r s' t' z' = (2 ^ k) ^ 2 * (y * y'))
    (h37 : ay * ay' = 3 ∨ ay * ay' = 7) :
    ∃ β : 𝔬, InT hQ L (β : Fv) ∧ (Rl β 3 ∨ Rl β 7) := by
  refine ⟨y * y', rp_prod hQ L hR hA hA' k hprod, ?_⟩
  rcases h37 with h | h
  · exact Or.inl (h ▸ hy.mul hy')
  · exact Or.inr (h ▸ hy.mul hy')

theorem dA5 : ∀ aq : ZMod 8, Od aq → Od (1 + 4 * aq) ∧ (1 : ZMod 8) * (1 + 4 * aq) = 5 := by decide
theorem dB5 : ∀ aq ar : ZMod 8, Od aq → Od ar → Od (aq + 4 * ar) ∧ aq * (aq + 4 * ar) = 5 := by decide
theorem d37 : ∀ ar : ZMod 8, Od ar → Od (1 + 2 * ar) ∧ ((1 : ZMod 8) * (1 + 2 * ar) = 3 ∨
    (1 : ZMod 8) * (1 + 2 * ar) = 7) := by decide
theorem d002 : ∀ aq ar : ZMod 8, Od aq → Od ar → ((1 : ZMod 8) * aq = 3 ∨ (1 : ZMod 8) * aq = 7) ∨
    (Od (1 + aq + ar) ∧ ((1 + aq + ar) * ar = 3 ∨ (1 + aq + ar) * ar = 7)) := by decide
theorem d022 : ∀ aq ar : ZMod 8, Od aq → Od ar → ((1 : ZMod 8) * aq = 3 ∨ (1 : ZMod 8) * aq = 7) ∨
    ((1 : ZMod 8) * ar = 3 ∨ (1 : ZMod 8) * ar = 7) ∨
    (Od (1 + aq + ar) ∧ ((1 : ZMod 8) * (1 + aq + ar) = 3 ∨ (1 : ZMod 8) * (1 + aq + ar) = 7)) := by decide

/-- Pattern $(0,0,2)$: coefficients $(1, q, 4r')$. -/
theorem pair_002 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 q (2 ^ 2 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dA5 ar hr2
    have hy' : Rl (1 + 4 * r') (1 + 4 * ar) := r1.add (r4.mul hr1)
    exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 0 1 hy' k1 (by bfr)) 0
      r1 hy' (by bfr) k2
  · rcases d002 aq ar hq2 hr2 with h | ⟨hod, h⟩
    · exact rp_37 hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 0 1 0 hq1 hq2 (by bfr)) 0
        r1 hq1 (by bfr) h
    · have hy : Rl (1 + q + r') (1 + aq + ar) := (r1.add hq1).add hr1
      exact rp_37 hQ L hR
        (admm h2 2 2 1 2 hy hod (by bfr) ⟨1, by ring⟩ ⟨q, by ring⟩ ⟨2 * r', by ring⟩)
        (admm h2 0 0 1 2 hr1 hr2 (by bfr) ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨2 * r', by ring⟩) 2 hy hr1
        (by bfr) h

/-- Pattern $(0,0,3)$: coefficients $(1, q, 8r')$. -/
theorem pair_003 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 q (2 ^ 3 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dA5 aq hq2
    have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
    exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 2 0 hy' k1 (by bfr)) 0
      r1 hy' (by bfr) k2
  · obtain ⟨k1, k2⟩ := d37 ar hr2
    have hy' : Rl (1 + 2 * r') (1 + 2 * ar) := r1.add (Rl.two.mul hr1)
    exact rp_37 hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr))
      (admm h2 2 0 1 2 hy' k1 (by bfr) ⟨1, by ring⟩ ⟨0, by ring⟩ ⟨4 * r', by ring⟩) 1 r1 hy'
      (by bfr) k2

/-- Pattern $(0,1,3)$: coefficients $(1, 2q', 8r')$. -/
theorem pair_013 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 (2 ^ 1 * q) (2 ^ 3 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dB5 aq ar hq2 hr2
    have hy' : Rl (q + 4 * r') (aq + 4 * ar) := hq1.add (r4.mul hr1)
    exact rp_five hQ L hR
      (admm h2 0 1 0 1 hq1 hq2 (by bfr) ⟨0, by ring⟩ ⟨2 * q, by ring⟩ ⟨0, by ring⟩)
      (admm h2 0 1 1 1 hy' k1 (by bfr) ⟨0, by ring⟩ ⟨2 * q, by ring⟩ ⟨8 * r', by ring⟩) 1 hq1 hy'
      (by bfr) k2
  · obtain ⟨k1, k2⟩ := d37 ar hr2
    have hy' : Rl (1 + 2 * r') (1 + 2 * ar) := r1.add (Rl.two.mul hr1)
    exact rp_37 hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr))
      (admm h2 2 0 1 2 hy' k1 (by bfr) ⟨1, by ring⟩ ⟨0, by ring⟩ ⟨4 * r', by ring⟩) 1 r1 hy'
      (by bfr) k2

/-- Pattern $(0,2,2)$: coefficients $(1, 4q', 4r')$. -/
theorem pair_022 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 (2 ^ 2 * q) (2 ^ 2 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dA5 aq hq2
    have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
    exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 1 0 hy' k1 (by bfr)) 0
      r1 hy' (by bfr) k2
  · have A0 : Adm 1 (2 ^ 2 * q) (2 ^ 2 * r') 2 0 0 :=
      admm h2 2 0 0 2 r1 (Or.inl rfl) (by bfr) ⟨1, by ring⟩ ⟨0, by ring⟩ ⟨0, by ring⟩
    rcases d022 aq ar hq2 hr2 with h | h | ⟨hod, h⟩
    · exact rp_37 hQ L hR A0
        (admm h2 0 1 0 2 hq1 hq2 (by bfr) ⟨0, by ring⟩ ⟨2 * q, by ring⟩ ⟨0, by ring⟩) 2 r1 hq1
        (by bfr) h
    · exact rp_37 hQ L hR A0
        (admm h2 0 0 1 2 hr1 hr2 (by bfr) ⟨0, by ring⟩ ⟨0, by ring⟩ ⟨2 * r', by ring⟩) 2 r1 hr1
        (by bfr) h
    · have hy : Rl (1 + q + r') (1 + aq + ar) := (r1.add hq1).add hr1
      exact rp_37 hQ L hR A0
        (admm h2 2 1 1 2 hy hod (by bfr) ⟨1, by ring⟩ ⟨2 * q, by ring⟩ ⟨2 * r', by ring⟩) 2 r1 hy
        (by bfr) h

/-- Pattern $(0,2,3)$: coefficients $(1, 4q', 8r')$. -/
theorem pair_023 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 (2 ^ 2 * q) (2 ^ 3 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dA5 aq hq2
    have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
    exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 1 0 hy' k1 (by bfr)) 0
      r1 hy' (by bfr) k2
  · obtain ⟨k1, k2⟩ := d37 ar hr2
    have hy' : Rl (1 + 2 * r') (1 + 2 * ar) := r1.add (Rl.two.mul hr1)
    exact rp_37 hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr))
      (admm h2 2 0 1 2 hy' k1 (by bfr) ⟨1, by ring⟩ ⟨0, by ring⟩ ⟨4 * r', by ring⟩) 1 r1 hy'
      (by bfr) k2

/-- Pattern $(0,3,3)$: coefficients $(1, 8q', 8r')$. -/
theorem pair_033 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q r' : 𝔬} (hq : IsUnit q) (hr : IsUnit r')
    (hR : RootPair hQ L 1 (2 ^ 3 * q) (2 ^ 3 * r')) : PairOK v hQ L := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
  refine ⟨?_, ?_⟩
  · obtain ⟨k1, k2⟩ := dB5 aq ar hq2 hr2
    have hy' : Rl (q + 4 * r') (aq + 4 * ar) := hq1.add (r4.mul hr1)
    exact rp_five hQ L hR
      (admm h2 0 1 0 3 hq1 hq2 (by bfr) ⟨0, by ring⟩ ⟨2 * q, by ring⟩ ⟨0, by ring⟩)
      (admm h2 0 1 2 3 hy' k1 (by bfr) ⟨0, by ring⟩ ⟨2 * q, by ring⟩ ⟨4 * r', by ring⟩) 3 hq1 hy'
      (by bfr) k2
  · obtain ⟨k1, k2⟩ := d37 aq hq2
    have hy' : Rl (1 + 2 * q) (1 + 2 * aq) := r1.add (Rl.two.mul hq1)
    exact rp_37 hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr))
      (admm h2 2 1 0 2 hy' k1 (by bfr) ⟨1, by ring⟩ ⟨4 * q, by ring⟩ ⟨0, by ring⟩) 1 r1 hy'
      (by bfr) k2

/-- Binary patterns: coefficients $(1, 2^dq')$, $d \in \{0, 2, 4\}$, third coefficient $0$. -/
theorem five_bin_0 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q : 𝔬} (hq : IsUnit q)
    (hR : RootPair hQ L 1 (2 ^ 0 * q) 0) : ∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5 := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨k1, k2⟩ := dA5 aq hq2
  have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
  exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 2 0 hy' k1 (by bfr)) 0
    r1 hy' (by bfr) k2

theorem five_bin_2 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q : 𝔬} (hq : IsUnit q)
    (hR : RootPair hQ L 1 (2 ^ 2 * q) 0) : ∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5 := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨k1, k2⟩ := dA5 aq hq2
  have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
  exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr)) (adm0 h2 1 1 0 hy' k1 (by bfr)) 0
    r1 hy' (by bfr) k2

theorem five_bin_4 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {q : 𝔬} (hq : IsUnit q)
    (hR : RootPair hQ L 1 (2 ^ 4 * q) 0) : ∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5 := by
  obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
  obtain ⟨k1, k2⟩ := dA5 aq hq2
  have hy' : Rl (1 + 4 * q) (1 + 4 * aq) := r1.add (r4.mul hq1)
  exact rp_five hQ L hR (adm0 h2 1 0 0 r1 (Or.inl rfl) (by bfr))
    (admm h2 2 1 0 2 hy' k1 (by bfr) ⟨1, by ring⟩ ⟨8 * q, by ring⟩ ⟨0, by ring⟩) 1 r1 hy'
    (by bfr) k2

end Alg

section Bin

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}
  (hQ : Q.Nondegenerate) (L : Lat F n)

local notation "Fw" => v.adicCompletion F
local notation "𝔬w" => v.adicCompletionIntegers F

/-- **Root vectors in the span of two orthogonal basis vectors** (the case $z = 0$ of `ternary_adm_gen`, needing no
third basis vector): $G_{ii} = wp$, $G_{jj} = wq$, $x = sb_i + tb_j$ has $Q(x) = \frac w2(ps^2 + qt^2)$ and is a
root vector when $\lvert 2ps\rvert, \lvert 2qt\rvert \le \lvert ps^2 + qt^2\rvert$. -/
theorem binary_adm_gen (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n}
    (hij : i ≠ j)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q)
    (s t : 𝔬w) (hB0 : (Bf p q 0 s t 0 : 𝔬w) ≠ 0)
    (hps : Valued.v ((2 * p * s : 𝔬w) : Fw) ≤ Valued.v ((Bf p q 0 s t 0 : 𝔬w) : Fw))
    (hqt : Valued.v ((2 * q * t : 𝔬w) : Fw) ≤ Valued.v ((Bf p q 0 s t 0 : 𝔬w) : Fw)) :
    ∃ x, Q.evalIn Fw x = w / 2 * ((Bf p q 0 s t 0 : 𝔬w) : Fw) ∧ symm Q Fw x ∈ locStabV Q v L := by
  set c : Fin n → Fw := Pi.single i (s : Fw) + Pi.single j (t : Fw) with hc
  have hci : c i = s := by simp [hc, hij]
  have hcj : c j = t := by simp [hc, hij.symm]
  have hcm : ∀ m, m ≠ i → m ≠ j → c m = 0 := by
    intro m h1 h2; simp [hc, h1, h2]
  have hcstd : c ∈ std v :=
    (std v).add_mem (single_mem_std i (vle_one s)) (single_mem_std j (vle_one t))
  have hdiag : ∀ m, (locGram Q v γ *ᵥ c) m = locGram Q v γ m m * c m := fun m =>
    gram_mulVec_diag_of γ fun l hl hcl => by
      have : l = i ∨ l = j := by
        by_contra h
        push Not at h
        exact hcl (hcm l h.1 h.2)
      rw [locGram_symm']
      exact horth l m hl this
  have hdot : ∀ d : Fin n → Fw, c ⬝ᵥ d = s * d i + t * d j := fun d => by
    rw [hc, add_dotProduct, single_dotProduct, single_dotProduct]
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hQ2 : 2 * Q.evalIn Fw (γ.val *ᵥ c) = w * ((Bf p q 0 s t 0 : 𝔬w) : Fw) := by
    rw [two_mul_evalIn_locGram, hdot, hdiag i, hdiag j, hci, hcj, hgi, hgj]
    simp only [Bf]
    push_cast
    ring
  have hQx : Q.evalIn Fw (γ.val *ᵥ c) = w / 2 * ((Bf p q 0 s t 0 : 𝔬w) : Fw) := by
    rw [div_mul_eq_mul_div, eq_div_iff h2ne]
    linear_combination hQ2
  have hBne : ((Bf p q 0 s t 0 : 𝔬w) : Fw) ≠ 0 := fun h => hB0 (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw (γ.val *ᵥ c) ≠ 0 := by
    rw [hQx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  refine ⟨γ.val *ᵥ c, hQx, symm_mem_of_gram L γ hγ hcstd hx0 fun m => ?_⟩
  have h2pos : 0 < Valued.v (2 : Fw) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne)
  have key : ∀ (a y : 𝔬w), Valued.v ((2 * a * y : 𝔬w) : Fw) ≤ Valued.v ((Bf p q 0 s t 0 : 𝔬w) : Fw) →
      Valued.v (w * (a : Fw) * (y : Fw)) ≤ Valued.v (Q.evalIn Fw (γ.val *ᵥ c)) := by
    intro a y h
    rw [hQx]
    have e : ((2 * a * y : 𝔬w) : Fw) = 2 * (a : Fw) * (y : Fw) := by push_cast; rfl
    rw [e] at h
    have e1 : w * (a : Fw) * (y : Fw) * 2 = w * (2 * (a : Fw) * (y : Fw)) := by ring
    have e2 : w / 2 * ((Bf p q 0 s t 0 : 𝔬w) : Fw) * 2 = w * ((Bf p q 0 s t 0 : 𝔬w) : Fw) := by
      field_simp
    refine le_of_mul_le_mul_right ?_ h2pos
    rw [← map_mul, ← map_mul, e1, e2, map_mul (Valued.v) w, map_mul (Valued.v) w]
    exact mul_le_mul' le_rfl h
  rw [hdiag m]
  by_cases hmi : m = i
  · subst hmi; rw [hci, hgi]; exact key p s hps
  by_cases hmj : m = j
  · subst hmj; rw [hcj, hgj]; exact key q t hqt
  rw [hcm m hmi hmj, mul_zero, map_zero]
  exact zero_le

/-- The binary analogue of `ternary_InT_gen`. -/
theorem binary_InT_gen (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n}
    (hij : i ≠ j)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q)
    {s t s' t' : 𝔬w} (hB : Adm p q 0 s t 0) (hB' : Adm p q 0 s' t' 0) :
    InT hQ L (((Bf p q 0 s t 0 * Bf p q 0 s' t' 0 : 𝔬w)) : Fw) := by
  obtain ⟨x, hx, hxs⟩ := binary_adm_gen L γ hγ hij horth hw hgi hgj s t hB.1 hB.2.1 hB.2.2.1
  obtain ⟨y, hy, hys⟩ := binary_adm_gen L γ hγ hij horth hw hgi hgj s' t' hB'.1 hB'.2.1 hB'.2.2.1
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hBne : ((Bf p q 0 s t 0 : 𝔬w) : Fw) ≠ 0 := fun h => hB.1 (by exact_mod_cast h)
  have hBne' : ((Bf p q 0 s' t' 0 : 𝔬w) : Fw) ≠ 0 := fun h => hB'.1 (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw x ≠ 0 := by rw [hx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  have hy0 : Q.evalIn Fw y ≠ 0 := by rw [hy]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne'
  have := InT.of_symm_pair hQ L hx0 hy0 hxs hys
  rw [hx, hy] at this
  have e : w / 2 * ((Bf p q 0 s t 0 : 𝔬w) : Fw) * (w / 2 * ((Bf p q 0 s' t' 0 : 𝔬w) : Fw)) =
      ((Bf p q 0 s t 0 * Bf p q 0 s' t' 0 : 𝔬w) : Fw) * (w / 2) ^ 2 := by push_cast; ring
  rw [e] at this
  exact (InT.sq_mul_iff hQ L (div_ne_zero hw h2ne)).mp this

end Bin

section Geo

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}
  (hQ : Q.Nondegenerate) (L : Lat ℚ n)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem rootPair_ternary (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fv} (hw : w ≠ 0) {p q r : 𝔬}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r) :
    RootPair hQ L p q r :=
  fun _ _ _ _ _ _ hB hB' => ternary_InT_gen hQ L γ hγ hij hik hjk horth hw hgi hgj hgk hB hB'

theorem adm_bin {p q s t z : 𝔬} (h : Adm p q 0 s t z) : Adm p q 0 s t 0 := by
  obtain ⟨h0, h1, h2, -⟩ := h
  have e : Bf p q 0 s t z = Bf p q 0 s t 0 := by simp [Bf]
  rw [e] at h0 h1 h2
  exact ⟨h0, h1, h2, by simp⟩

theorem rootPair_binary (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n}
    (hij : i ≠ j)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j) → locGram Q v γ l m = 0)
    {w : Fv} (hw : w ≠ 0) {p q : 𝔬}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) :
    RootPair hQ L p q 0 := by
  intro s t z s' t' z' hB hB'
  have e : ∀ s t z : 𝔬, Bf p q 0 s t z = Bf p q 0 s t 0 := fun s t z => by simp [Bf]
  rw [e s t z, e s' t' z']
  exact binary_InT_gen hQ L γ hγ hij horth hw hgi hgj (adm_bin hB) (adm_bin hB')

/-- Diagonal entries of valuation $e^{-1-\nu}$: $G_{bb} = G_{aa}\cdot 2^d u$ with $u$ a unit when
$\nu_b = \nu_a + d$. -/
theorem diag_ratio (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv) {ν : Fin n → ℕ}
    (hval : ∀ l, Valued.v (locGram Q v γ l l) = exp (-1 - (ν l : ℤ))) {a b : Fin n} (d : ℕ)
    (hd : ν b = ν a + d) :
    ∃ u : 𝔬, IsUnit u ∧ locGram Q v γ b b = locGram Q v γ a a * (((2 ^ d * u : 𝔬)) : Fv) := by
  have h2v := valued_two_dyadic v h2
  have hne : locGram Q v γ a a ≠ 0 := fun h => by
    have := hval a
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hne' : (2 : Fv) ^ d * locGram Q v γ a a ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hne
  have hv : Valued.v (locGram Q v γ b b) = Valued.v ((2 : Fv) ^ d * locGram Q v γ a a) := by
    rw [map_mul, map_pow, h2v, hval a, hval b, ← WithZero.exp_nsmul, ← exp_add]
    congr 1
    rw [hd]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨u, hu, hu'⟩ := exists_unit_ratio hne' hv
  refine ⟨u, hu, ?_⟩
  rw [hu']
  push_cast
  rw [coe_two_eq]
  ring

theorem diag_ne_zero (γ : GL (Fin n) Fv) {ν : Fin n → ℕ}
    (hval : ∀ l, Valued.v (locGram Q v γ l l) = exp (-1 - (ν l : ℤ))) (a : Fin n) :
    locGram Q v γ a a ≠ 0 := fun h => by
  have := hval a
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- **Sorted triple within a window of width $3$ gives all units** (Cassels' Lemma 3.8 (ii), (iii) and the six
further patterns of Conway–Sloane §9.7). -/
theorem units_of_sorted (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {ν : Fin n → ℕ} (hval : ∀ l, Valued.v (locGram Q v γ l l) = exp (-1 - (ν l : ℤ)))
    (h1 : ν i ≤ ν j) (h2' : ν j ≤ ν k) (h3 : ν k ≤ ν i + 3) (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) :
    u ∈ localSpinorNormGroup Q hQ v L := by
  have hne := diag_ne_zero γ hval i
  obtain ⟨d1, hd1⟩ : ∃ d, ν j = ν i + d := ⟨ν j - ν i, by omega⟩
  obtain ⟨d2, hd2⟩ : ∃ d, ν k = ν i + d := ⟨ν k - ν i, by omega⟩
  have hb : d1 ≤ d2 := by omega
  have hc : d2 ≤ 3 := by omega
  obtain ⟨q', hq', hgj⟩ := diag_ratio h2 γ hval d1 hd1
  obtain ⟨r', hr', hgk⟩ := diag_ratio h2 γ hval d2 hd2
  have hgi : locGram Q v γ i i = locGram Q v γ i i * ((1 : 𝔬) : Fv) := by simp
  have RP : ∀ {p q r : 𝔬}, locGram Q v γ j j = locGram Q v γ i i * (q : Fv) →
      locGram Q v γ k k = locGram Q v γ i i * (r : Fv) → locGram Q v γ i i = locGram Q v γ i i * (p : Fv) →
      RootPair hQ L p q r := fun hj hk hi =>
    rootPair_ternary hQ L γ hγ hij hik hjk horth hne hi hj hk
  clear hd1 hd2 h1 h2' h3
  interval_cases d2 <;> interval_cases d1
  · exact ternary_units hQ L h2 γ hγ hij hik hjk horth hne (p := 1) (q := 2 ^ 0 * q') (r := 2 ^ 0 * r')
      (Or.inl ⟨isUnit_one, by simpa using hq', by simpa using hr'⟩) hgi hgj hgk u hu
  · exact ternary_units hQ L h2 γ hγ hij hik hjk horth hne (p := 1) (q := 2 ^ 0 * q') (r := 2 ^ 1 * r')
      (Or.inr (Or.inl ⟨isUnit_one, by simpa using hq', r', hr', by ring⟩)) hgi hgj hgk u hu
  · exact ternary_units hQ L h2 γ hγ hij hik hjk horth hne (p := 1) (q := 2 ^ 1 * q') (r := 2 ^ 1 * r')
      (Or.inr (Or.inr (Or.inl ⟨isUnit_one, q', r', hq', hr', by ring, by ring⟩))) hgi hgj hgk u hu
  · exact units_of_pairOK hQ L h2 (pair_002 hQ L h2 (q := 2 ^ 0 * q') (r' := r')
      (by simpa using hq') hr' (RP hgj hgk hgi)) u hu
  · exact ternary_units hQ L h2 γ hγ hij hik hjk horth hne (p := 1) (q := 2 ^ 1 * q') (r := 2 ^ 2 * r')
      (Or.inr (Or.inr (Or.inr ⟨isUnit_one, q', r', hq', hr', by ring, by ring⟩))) hgi hgj hgk u hu
  · exact units_of_pairOK hQ L h2 (pair_022 hQ L h2 (q := q') (r' := r') hq' hr'
      (by simpa using RP hgj hgk hgi)) u hu
  · exact units_of_pairOK hQ L h2 (pair_003 hQ L h2 (q := 2 ^ 0 * q') (r' := r')
      (by simpa using hq') hr' (RP hgj hgk hgi)) u hu
  · exact units_of_pairOK hQ L h2 (pair_013 hQ L h2 (q := q') (r' := r') hq' hr'
      (RP hgj hgk hgi)) u hu
  · exact units_of_pairOK hQ L h2 (pair_023 hQ L h2 (q := q') (r' := r') hq' hr'
      (RP hgj hgk hgi)) u hu
  · exact units_of_pairOK hQ L h2 (pair_033 hQ L h2 (q := q') (r' := r') hq' hr'
      (RP hgj hgk hgi)) u hu

theorem InT_five (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {α : 𝔬} (hα : InT hQ L (α : Fv)) (h5 : Rl α 5) :
    InT hQ L (5 : Fv) := by
  obtain ⟨ma, hma⟩ := Rl.of_cast (n := 5) (by simpa using h5)
  push_cast at hma
  have u5 : IsUnit (5 : 𝔬) := by
    have := isUnit_one_add_two_mul h2 (2 : 𝔬)
    convert this using 1; norm_num
  obtain ⟨s, hs, hαs⟩ := cong_sq h2 u5 ma hma
  have hs0 : (s : Fv) ≠ 0 := fun h => hs.ne_zero (by exact_mod_cast h)
  rw [hαs] at hα
  have hc5 : ((5 : 𝔬) : Fv) = 5 := map_ofNat (algebraMap 𝔬 Fv) 5
  have e : (((5 : 𝔬) * s ^ 2 : 𝔬) : Fv) = 5 * (s : Fv) ^ 2 := by push_cast; rw [hc5]
  rw [e] at hα
  exact (InT.sq_mul_iff hQ L hs0).mp hα

/-- **Two orthogonal basis vectors with exponents differing by $0$, $2$ or $4$ put $5$ in $\theta$.** -/
theorem five_of_diff (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j) → locGram Q v γ l m = 0)
    {ν : Fin n → ℕ} (hval : ∀ l, Valued.v (locGram Q v γ l l) = exp (-1 - (ν l : ℤ)))
    (d : ℕ) (hd : d = 0 ∨ d = 2 ∨ d = 4) (hν : ν j = ν i + d) : InT hQ L (5 : Fv) := by
  obtain ⟨u, hu, hgj⟩ := diag_ratio h2 γ hval d hν
  have hne := diag_ne_zero γ hval i
  have hgi : locGram Q v γ i i = locGram Q v γ i i * ((1 : 𝔬) : Fv) := by simp
  have hR := rootPair_binary hQ L γ hγ hij horth hne hgi hgj
  obtain ⟨α, hα, h5⟩ : ∃ α : 𝔬, InT hQ L (α : Fv) ∧ Rl α 5 := by
    rcases hd with rfl | rfl | rfl
    · exact five_bin_0 hQ L h2 hu hR
    · exact five_bin_2 hQ L h2 hu hR
    · exact five_bin_4 hQ L h2 hu hR
  exact InT_five hQ L h2 hα h5

theorem not_all_units_of_five (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (h5 : Units.mk0 (5 : Fv) (by norm_num) ∉ localSpinorNormGroup Q hQ v L) :
    ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L := by
  intro h
  apply h5
  apply h
  have u5 : IsUnit (5 : 𝔬) := by
    have := isUnit_one_add_two_mul h2 (2 : 𝔬)
    convert this using 1; norm_num
  have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u5
  rw [Units.val_mk0]
  convert this using 2

end Geo

section Comb

variable {m : ℕ}

theorem sum_ge_of_top (f : Fin m → ℕ) (g : ℕ → ℕ)
    (hg : ∀ (s : Finset (Fin m)) (c M : ℕ), s.card = c + 1 → (∀ k ∈ s, f k ≤ M) → g c ≤ M) :
    ∀ (c : ℕ) (s : Finset (Fin m)), s.card = c → ∑ i ∈ Finset.range c, g i ≤ ∑ k ∈ s, f k := by
  intro c
  induction c with
  | zero => intro s hs; simp
  | succ c ih =>
    intro s hs
    have hne : s.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image s f hne
    have hcard : (s.erase k0).card = c := by rw [Finset.card_erase_of_mem hk0]; omega
    have h1 := ih (s.erase k0) hcard
    rw [← Finset.add_sum_erase s f hk0, Finset.sum_range_succ]
    have := hg s c (f k0) hs hmax
    omega

theorem window_le (f : Fin m → ℕ) (W : ℕ)
    (htr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ f i → a ≤ f j → a ≤ f k → f i < a + W →
      f j < a + W → f k < a + W → False)
    (s : Finset (Fin m)) (a : ℕ) : (s.filter (fun k => a ≤ f k ∧ f k < a + W)).card ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp h
  simp only [Finset.mem_filter] at hi hj hk
  exact htr i j k hij hik hjk a hi.2.1 hj.2.1 hk.2.1 hi.2.2 hj.2.2 hk.2.2

theorem count_lt (f : Fin m → ℕ) (W : ℕ)
    (htr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ f i → a ≤ f j → a ≤ f k → f i < a + W →
      f j < a + W → f k < a + W → False)
    (s : Finset (Fin m)) (q : ℕ) : (s.filter (fun k => f k < W * q)).card ≤ 2 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : W * (q + 1) = W * q + W := by ring
    have hsub : s.filter (fun k => f k < W * (q + 1)) ⊆
        s.filter (fun k => f k < W * q) ∪ s.filter (fun k => W * q ≤ f k ∧ f k < W * q + W) := by
      intro k hk
      simp only [Finset.mem_union, Finset.mem_filter] at hk ⊢
      obtain ⟨hks, hk⟩ := hk
      rw [e] at hk
      by_cases h : f k < W * q
      · exact Or.inl ⟨hks, h⟩
      · exact Or.inr ⟨hks, by omega, hk⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 * q + 2 := add_le_add ih (window_le f W htr s _)
      _ = _ := by ring

theorem top4 (f : Fin m → ℕ)
    (htr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ f i → a ≤ f j → a ≤ f k → f i < a + 4 →
      f j < a + 4 → f k < a + 4 → False) :
    ∀ (s : Finset (Fin m)) (c M : ℕ), s.card = c + 1 → (∀ k ∈ s, f k ≤ M) → (fun i => 4 * (i / 2)) c ≤ M := by
  intro s c M hs hM
  have h := count_lt f 4 htr s (M / 4 + 1)
  rw [Finset.filter_true_of_mem (fun k hk => by have := hM k hk; omega)] at h
  show 4 * (c / 2) ≤ M
  omega

theorem top6 (f : Fin m → ℕ)
    (htr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ f i → a ≤ f j → a ≤ f k → f i < a + 6 →
      f j < a + 6 → f k < a + 6 → False)
    (hinj : ∀ i j, i ≠ j → f i ≠ f j) :
    ∀ (s : Finset (Fin m)) (c M : ℕ), s.card = c + 1 → (∀ k ∈ s, f k ≤ M) →
      (fun i => 6 * (i / 2) + i % 2) c ≤ M := by
  intro s c M hs hM
  show 6 * (c / 2) + c % 2 ≤ M
  have hlt := count_lt f 6 htr s (M / 6)
  have hT := window_le f 6 htr s (6 * (M / 6))
  have hsub : s ⊆ s.filter (fun k => f k < 6 * (M / 6)) ∪
      s.filter (fun k => 6 * (M / 6) ≤ f k ∧ f k < 6 * (M / 6) + 6) := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_filter]
    have := hM k hk
    by_cases h : f k < 6 * (M / 6)
    · exact Or.inl ⟨hk, h⟩
    · exact Or.inr ⟨hk, by omega, by omega⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  by_cases hM0 : M = 6 * (M / 6)
  · have hT1 : (s.filter (fun k => 6 * (M / 6) ≤ f k ∧ f k < 6 * (M / 6) + 6)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      simp only [Finset.mem_filter] at hi hj
      by_contra hij
      exact hinj i j hij (by have := hM i hi.1; have := hM j hj.1; omega)
    omega
  · omega

theorem sum4 : ∀ n : ℕ, ∑ i ∈ Finset.range n, 4 * (i / 2) + 2 * (n / 2) = 2 * n.choose 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    rw [Finset.sum_range_succ, h, Nat.choose_one_right]
    omega

theorem sum6 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (6 * (i / 2) + i % 2) + 2 * (n / 2) = 3 * n.choose 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    rw [Finset.sum_range_succ, h, Nat.choose_one_right]
    omega

end Comb

section Main

variable {n : ℕ} {Q : QuadForm ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}
  (hQ : Q.Nondegenerate) (L : Lat ℚ n)

local notation "Fv" => v.adicCompletion ℚ

theorem det_le_of_diag (γ' : GL (Fin n) Fv) {ν : Fin n → ℕ}
    (horth : ∀ k l, k ≠ l → locGram Q v γ' k l = 0)
    (hval : ∀ k, Valued.v (locGram Q v γ' k k) = exp (-1 - (ν k : ℤ))) (B : ℕ) (hB : B ≤ ∑ k, ν k) :
    Valued.v (locGram Q v γ').det ≤ exp (-((B + n : ℕ) : ℤ)) := by
  have hG : locGram Q v γ' = Matrix.diagonal (fun k => locGram Q v γ' k k) := by
    ext k l
    by_cases h : k = l
    · subst h; simp
    · rw [horth k l h, Matrix.diagonal_apply_ne _ h]
  rw [hG, Matrix.det_diagonal, map_prod]
  simp only [hval]
  rw [prod_exp, exp_le_exp]
  have h3 : (∑ k, (-1 - (ν k : ℤ))) = -(n : ℤ) - ((∑ k, ν k : ℕ) : ℤ) := by
    simp [Finset.sum_sub_distrib]
  rw [h3]
  have : (B : ℤ) ≤ ((∑ k, ν k : ℕ) : ℤ) := by exact_mod_cast hB
  omega

/-- Three distinct indices with exponents in a window of width $3$ are impossible when not all units lie in
$\theta$ (all orderings of the triple). -/
theorem no_triple (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) {ν : Fin n → ℕ}
    (hval : ∀ l, Valued.v (locGram Q v γ l l) = exp (-1 - (ν l : ℤ))) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ ν i → a ≤ ν j → a ≤ ν k → ν i < a + 4 → ν j < a + 4 →
      ν k < a + 4 → False := by
  have hsorted : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ν i ≤ ν j → ν j ≤ ν k → ν k ≤ ν i + 3 → False := by
    intro i j k hij hik hjk a b c
    apply hnot
    intro u hu
    exact units_of_sorted hQ L h2 γ hγ hij hik hjk (fun l m hlm _ => horth l m hlm) hval a b c u hu
  intro i j k hij hik hjk a h1 h2 h3 h4 h5 h6
  rcases le_total (ν i) (ν j) with o1 | o1 <;> rcases le_total (ν j) (ν k) with o2 | o2 <;>
    rcases le_total (ν i) (ν k) with o3 | o3 <;>
  first
    | (refine hsorted i j k hij hik hjk ?_ ?_ ?_ <;> omega)
    | (refine hsorted i k j hik hij hjk.symm ?_ ?_ ?_ <;> omega)
    | (refine hsorted j i k hij.symm hjk hik ?_ ?_ ?_ <;> omega)
    | (refine hsorted j k i hjk hij.symm hik.symm ?_ ?_ ?_ <;> omega)
    | (refine hsorted k i j hik.symm hjk.symm hij ?_ ?_ ?_ <;> omega)
    | (refine hsorted k j i hjk.symm hik.symm hij.symm ?_ ?_ ?_ <;> omega)

/-- **Conway–Sloane, Ch. 15, §9.7, Theorem 20 (c)** (the divisibility (41)): if the form is $2$-adically integral on
$L_2$ ($\lvert Q(x)\rvert \le 1$ for all $x \in L_2$, `hint`) and not every $2$-adic unit is a spinor norm of $L_2$
(`hnot`: $U_2 \not\subseteq \theta(O^+(L_2))$), then for every basis $\gamma$ of $L_2$ (`hγ`) the Gram determinant of
$B = 2Q$ satisfies $\lvert\det G\rvert \le 2^{-(2\binom n2 - 2\lfloor n/2\rfloor + n)}$, i.e.
$\det G$ is divisible by $2^{\,n + 2\binom n2 - 2\lfloor n/2\rfloor}$ (equivalently, the determinant $d = 2^{-n}\det G$
of the classical Gram matrix is divisible by $2^{\,2\binom n2 - 2\lfloor n/2\rfloor}$).
Hypotheses: `hQ` nondegeneracy of $Q$; `h2` the prime $v$ lies over $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (c), (41), p. 394 (local form at 2)"]
theorem valued_det_le_of_not_units_mem_two_cs (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    Valued.v (locGram Q v γ).det ≤ exp (-((2 * n.choose 2 - 2 * (n / 2) + n : ℕ) : ℤ)) := by
  obtain ⟨γ', ν, hγ', hdet, horth, hval⟩ := exists_diag_basis_two Q hQ h2 L hint hnot γ hγ
  rw [← hdet]
  have htr := no_triple hQ L h2 hnot γ' hγ' horth hval
  have h1 := sum_ge_of_top ν (fun i => 4 * (i / 2)) (top4 ν htr) n Finset.univ (by simp)
  refine (det_le_of_diag γ' horth hval _ h1).trans ?_
  rw [exp_le_exp]
  have := sum4 n
  omega

/-- **Conway–Sloane, Ch. 15, §9.7, Theorem 19** (local form at $2$): if $5$ is not a spinor norm of $L_2$ (`h5`)
and the form is $2$-adically integral on $L_2$ (`hint`), then $L_2$ has an orthogonal basis $\gamma'$ with
$\lvert G_{kk}\rvert = 2^{-1-\nu_k}$, the exponents $\nu_k$ are pairwise distinct, and no two differ by $2$ or $4$;
also $\lvert\det G'\rvert = \lvert\det G\rvert$ for the given basis $\gamma$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 19, p. 393 (local form at 2)"]
theorem exists_diag_basis_two_of_five_not_mem (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (h5 : Units.mk0 (5 : Fv) (by norm_num) ∉ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    ∃ (γ' : GL (Fin n) Fv) (ν : Fin n → ℕ), loc v L.1 = locAct v γ' (std v) ∧
      Valued.v (locGram Q v γ').det = Valued.v (locGram Q v γ).det ∧
      (∀ k l, k ≠ l → locGram Q v γ' k l = 0) ∧
      (∀ k, Valued.v (locGram Q v γ' k k) = exp (-1 - (ν k : ℤ))) ∧ Function.Injective ν ∧
      (∀ i j, i ≠ j → ν i ≠ ν j + 2 ∧ ν i ≠ ν j + 4) := by
  have hnot := not_all_units_of_five hQ L h2 h5
  obtain ⟨γ', ν, hγ', hdet, horth, hval⟩ := exists_diag_basis_two Q hQ h2 L hint hnot γ hγ
  have hd : ∀ i j (d : ℕ), i ≠ j → (d = 0 ∨ d = 2 ∨ d = 4) → ν j = ν i + d → False := by
    intro i j d hij hd hν
    exact h5 (by
      obtain ⟨h0, hm⟩ := five_of_diff hQ L h2 γ' hγ' hij (fun l m hlm _ => horth l m hlm) hval d hd hν
      exact hm)
  refine ⟨γ', ν, hγ', hdet, horth, hval, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    exact hd i j 0 hne (Or.inl rfl) (by omega)
  · intro i j hij
    exact ⟨fun h => hd j i 2 hij.symm (Or.inr (Or.inl rfl)) h,
      fun h => hd j i 4 hij.symm (Or.inr (Or.inr rfl)) h⟩

/-- **Conway–Sloane, Ch. 15, §9.7, Theorem 20 (d)** (the divisibility (42)): if the form is $2$-adically integral on
$L_2$ (`hint`) and $5$ is not a spinor norm of $L_2$ (`h5`: $5 \notin \theta(O^+(L_2))$), then for every basis $\gamma$
of $L_2$ (`hγ`): $\lvert\det G\rvert \le 2^{-(3\binom n2 - 2\lfloor n/2\rfloor + n)}$. (The printed hypothesis
$n \ge 3$ is not needed in this proof.) Hypotheses `hQ`, `h2` as in Theorem 20 (c). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (d), (42), p. 394 (local form at 2)"]
theorem valued_det_le_of_five_not_mem_two (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (h5 : Units.mk0 (5 : Fv) (by norm_num) ∉ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    Valued.v (locGram Q v γ).det ≤ exp (-((3 * n.choose 2 - 2 * (n / 2) + n : ℕ) : ℤ)) := by
  obtain ⟨γ', ν, hγ', hdet, horth, hval, hinj, hp⟩ :=
    exists_diag_basis_two_of_five_not_mem hQ h2 L hint h5 γ hγ
  rw [← hdet]
  have P : ∀ i j, i ≠ j → ν j ≠ ν i ∧ ν j ≠ ν i + 2 ∧ ν j ≠ ν i + 4 := fun i j hij =>
    ⟨fun h => hij (hinj h.symm), (hp j i hij.symm).1, (hp j i hij.symm).2⟩
  have htr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ a, a ≤ ν i → a ≤ ν j → a ≤ ν k → ν i < a + 6 →
      ν j < a + 6 → ν k < a + 6 → False := by
    intro i j k hij hik hjk a h1 h2 h3 h4 h5 h6
    have := P i j hij
    have := P j i hij.symm
    have := P i k hik
    have := P k i hik.symm
    have := P j k hjk
    have := P k j hjk.symm
    omega
  have h1 := sum_ge_of_top ν (fun i => 6 * (i / 2) + i % 2) (top6 ν htr fun i j hij h => hij (hinj h)) n
    Finset.univ (by simp)
  refine (det_le_of_diag γ' horth hval _ h1).trans ?_
  rw [exp_le_exp]
  have := sum6 n
  omega

end Main

end QuadFormsKB.ConwaySloane
