/-
# Local densities over a DVR: explicit values at non-dyadic primes (Tables 1–2, (5.8)–(5.10))

**Layer:** DVR, at a **non-dyadic** prime: $R$ a DVR with uniformizer $\pi$, $\pi \nmid 2$, finite residue field
$\mathbb{F} = R/\pi$ of size $q$ (odd), and $Q = \langle a_0, \dots, a_{n-1}\rangle$ diagonal with all $a_i$ units ($\mathfrak{p} \nmid 2N$);
$\chi$ is the quadratic character of $\mathbb{F}$ (the symbol $(\frac{\cdot}{\mathfrak{p}})$ of the paper).
**Proves** Table 1 for all $n$ (p. 363; `DVR.card_diag_mod_pi`, over any finite field of odd characteristic:
`DVR.diagCountF_odd`, `DVR.diagCountF_even`), Remark 3.5.1 (p. 362; `DVR.isLocallyRepresentedAt_of_good`),
Remark 3.4.1(a) (p. 361; `DVR.localDensity_unit`), Table 2 (p. 370, with (5.9); `DVR.table2_odd_unit`,
`DVR.table2_even_unit`, `DVR.table2_ord_one`) and (5.10) (p. 371; `DVR.eq_5_10`); the local constant is
`DVR.localConstC` ((5.8), p. 370). These are the $\mathbb{Q}$ results of `Table2.lean` and `Explicit.lean` with
$p$ replaced by $q$ and the Legendre symbol by $\chi$; the proofs are the same character-sum computations over
$\mathbb{F}$ instead of $\mathbb{F}_p$. The paper states Table 1 only for $\mathfrak{p} \nmid 2N$ (at $\mathfrak{p} \mid 2$ it says the
counts "must be computed on a case-by-case basis"); the dyadic versions (for $\mathfrak{p} \nmid N$, i.e. even
unimodular forms with unit Hessian) are in `DVRDyadicTable.lean`.
**Depends on** `DVRExplicit.lean`.
-/
import QuadFormsKB.LocalDensity.DVRExplicit
import QuadFormsKB.LocalDensity.Table2

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

/-! ### Table 1 over a finite field of odd characteristic -/

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number (as an integer) of $\vec{x} \in \mathbb{F}^m$ with $\sum_i a_i x_i^2 = c$. -/
noncomputable def diagCountF {m : ℕ} (a : Fin m → F) (c : F) : ℤ :=
  ∑ x : Fin m → F, if ∑ i, a i * x i ^ 2 = c then 1 else 0

/-- Splitting off the first variable: $r_{a_0 \oplus a}(c) = \sum_y r_a(c - a_0 y^2)$. -/
theorem diagCountF_cons {m : ℕ} (a0 : F) (a : Fin m → F) (c : F) :
    diagCountF (Fin.cons a0 a : Fin (m + 1) → F) c = ∑ y : F, diagCountF a (c - a0 * y ^ 2) := by
  unfold diagCountF
  rw [← (Fin.consEquiv fun _ => F).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

/-- The counts sum to the number of vectors: $\sum_c r_a(c) = q^m$. -/
theorem sum_diagCountF {m : ℕ} (a : Fin m → F) :
    ∑ c : F, diagCountF a c = (Fintype.card F : ℤ) ^ m := by
  unfold diagCountF
  rw [Finset.sum_comm]
  simp

/-- Fibre sum over squares: $\sum_y f(y^2) = \sum_t (1 + \chi(t)) f(t)$. -/
theorem sum_sq_eq_sum_quadraticCharF (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ y : F, f (y ^ 2) = ∑ t : F, (1 + quadraticChar F t) * f t := by
  have h1 : ∀ y : F, f (y^2) = ∑ t : F, if y^2 = t then f t else 0 := by
    intro y; rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have := quadraticChar_card_sqrts hF t
  rw [Set.toFinset_ofPred] at this
  rw [this]; ring

/-- $\sum_y \chi(A + B y^2) = (q-1)\chi(B)$ if $A = 0$, and $-\chi(B)$ otherwise ($B \ne 0$). -/
theorem sum_quadraticChar_add_mul_sqF (hF : ringChar F ≠ 2) (A B : F) (hB : B ≠ 0) :
    ∑ y : F, quadraticChar F (A + B * y^2) =
      if A = 0 then ((Fintype.card F : ℤ) - 1) * quadraticChar F B else - quadraticChar F B := by
  have hlin : ∀ A B : F, B ≠ 0 → ∑ t : F, quadraticChar F (A + B * t) = 0 := by
    intro A B hB
    have hbij : Function.Bijective (fun t : F => A + B * t) := by
      rw [← Finite.injective_iff_bijective]
      intro x y h; simpa [hB] using h
    rw [Fintype.sum_bijective _ hbij _ (fun s => quadraticChar F s) (fun _ => rfl)]
    exact quadraticChar_sum_zero hF
  have hJ : jacobiSum (quadraticChar F) (quadraticChar F) = - quadraticChar F (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv] at this
  rw [sum_sq_eq_sum_quadraticCharF hF (fun s => (quadraticChar F) (A + B * s))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, hlin A B hB, zero_add]
  have hm1 : (quadraticChar F) (-1) * (quadraticChar F) (-1) = 1 := by
    rw [← map_mul]; norm_num
  split_ifs with hA
  · subst hA
    have : ∀ t : F, (quadraticChar F) t * (quadraticChar F) (0 + B * t) =
        (quadraticChar F) B * (1 - if t = 0 then 1 else 0) := by
      intro t
      by_cases ht : t = 0
      · simp [ht, MulChar.map_zero]
      · simp only [ht, ite_false, sub_zero, mul_one, zero_add]
        rw [← map_mul, show t * (B * t) = B * t^2 by ring, map_mul, quadraticChar_sq_one' ht, mul_one]
    simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp; ring
  · have hbij : Function.Bijective (fun s : F => -A / B * s) := by
      rw [← Finite.injective_iff_bijective]
      intro x y h; simpa [hB, hA] using h
    rw [← Fintype.sum_bijective _ hbij (fun s => (quadraticChar F) (-A / B * s) *
      (quadraticChar F) (A + B * (-A / B * s))) _ (fun _ => rfl)]
    have : ∀ s : F, (quadraticChar F) (-A / B * s) * (quadraticChar F) (A + B * (-A / B * s)) =
        (quadraticChar F) (-B) * ((quadraticChar F) s * (quadraticChar F) (1 - s)) := by
      intro s
      rw [← map_mul, ← map_mul, ← map_mul]
      have : -A / B * s * (A + B * (-A / B * s)) = (A / B)^2 * (-B * (s * (1 - s))) := by
        field_simp; ring
      rw [this, map_mul, quadraticChar_sq_one' (div_ne_zero hA hB), one_mul]
    simp_rw [this, ← Finset.mul_sum]
    rw [← jacobiSum, hJ, show -B = -1 * B by ring, map_mul]
    linear_combination (- (quadraticChar F) B) * hm1

/-- One-variable count: $\#\{x : a x^2 = t\} = 1 + \chi(a t)$ for $a \ne 0$. -/
theorem sum_ite_mul_sq_eqF (hF : ringChar F ≠ 2) (a t : F) (ha : a ≠ 0) :
    ∑ x : F, (if a * x^2 = t then 1 else 0 : ℤ) = 1 + quadraticChar F (a * t) := by
  rw [sum_sq_eq_sum_quadraticCharF hF (fun s => if a * s = t then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  have : ∀ s : F, (a * s = t) ↔ s = t / a := by
    intro s; constructor
    · rintro rfl; field_simp
    · rintro rfl; field_simp
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [show a * t = a^2 * (t / a) by field_simp, map_mul, quadraticChar_sq_one' ha, one_mul]

/-- The binary counts of Table 1 over $\mathbb{F}$:
$\#\{b y^2 + c z^2 = r\} = q - \eta + q\,\eta\,[r = 0]$ with $\eta = \chi(-bc)$. -/
theorem binary_countF (hF : ringChar F ≠ 2) (b c : F) (hb : b ≠ 0) (hc : c ≠ 0) (r : F) :
    ∑ y : F, ∑ z : F, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) =
      (Fintype.card F : ℤ) - quadraticChar F (-(b*c)) +
        (Fintype.card F : ℤ) * quadraticChar F (-(b*c)) * (if r = 0 then 1 else 0) := by
  have hA := fun a t ha => sum_ite_mul_sq_eqF (F := F) hF a t ha
  have : ∀ y : F, ∑ z : F, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) =
      1 + (quadraticChar F) (c * r + (-(c * b)) * y^2) := by
    intro y
    have h2 : ∀ z : F, (b * y^2 + c * z^2 = r) ↔ c * z^2 = r - b * y^2 := by
      intro z; constructor <;> intro h <;> linear_combination h
    simp_rw [h2]
    rw [hA c _ hc]; ring_nf
  simp_rw [this, Finset.sum_add_distrib,
    sum_quadraticChar_add_mul_sqF hF _ _ (neg_ne_zero.mpr (mul_ne_zero hc hb))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_eq_zero, hc, false_or]
  rw [show -(c*b) = -(b*c) by ring]
  split_ifs <;> ring

/-- **Two-variable recursion:** $r_{a_0 \oplus a_1 \oplus a}(c) = (q - \eta) q^m + \eta\, q\, r_a(c)$,
$\eta = \chi(-a_0 a_1)$. -/
theorem diagCountF_cons_cons {m : ℕ} (hF : ringChar F ≠ 2) (a0 a1 : F) (h0 : a0 ≠ 0) (h1 : a1 ≠ 0)
    (a : Fin m → F) (c : F) :
    diagCountF (Fin.cons a0 (Fin.cons a1 a : Fin (m + 1) → F) : Fin (m + 2) → F) c =
      ((Fintype.card F : ℤ) - quadraticChar F (-(a0 * a1))) * (Fintype.card F : ℤ) ^ m +
        quadraticChar F (-(a0 * a1)) * (Fintype.card F : ℤ) * diagCountF a c := by
  simp_rw [diagCountF_cons]
  have hconv : ∀ y z : F, diagCountF a (c - a0 * y ^ 2 - a1 * z ^ 2) =
      ∑ t : F, (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ) * diagCountF a (c - t) := by
    intro y z
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    congr 1; ring
  simp_rw [hconv]
  rw [show (∑ y : F, ∑ z : F, ∑ t : F,
      (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ) * diagCountF a (c - t)) =
      ∑ t : F, (∑ y : F, ∑ z : F, (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ)) *
        diagCountF a (c - t) by
    simp_rw [Finset.sum_mul]
    exact (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans Finset.sum_comm]
  simp_rw [binary_countF hF a0 a1 h0 h1]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  have htot : ∑ t : F, diagCountF a (c - t) = (Fintype.card F : ℤ) ^ m := by
    rw [← sum_diagCountF a]
    exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun _ => rfl)
  rw [htot, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, sub_zero]
  ring

/-- No variables: $r_{\emptyset}(c) = [c = 0]$. -/
theorem diagCountF_zero (a : Fin 0 → F) (c : F) :
    diagCountF a c = if c = 0 then 1 else 0 := by
  simp [diagCountF, eq_comm]

/-- **Table 1 over $\mathbb{F}$, $n = 2k+1$ odd:** $r(c) = q^{2k} + \chi((-1)^k D)\, q^k \chi(c)$. -/
theorem diagCountF_odd (hF : ringChar F ≠ 2) (k : ℕ) :
    ∀ (m : ℕ), m = 2 * k + 1 → ∀ (a : Fin m → F), (∀ i, a i ≠ 0) → ∀ c : F,
      diagCountF a c = (Fintype.card F : ℤ) ^ (2 * k) +
        quadraticChar F ((-1) ^ k * ∏ i, a i) * (Fintype.card F : ℤ) ^ k * quadraticChar F c := by
  induction k with
  | zero =>
    intro m hm a ha c
    obtain rfl : m = 1 := by simpa using hm
    conv_lhs => rw [← Fin.cons_self_tail a]
    rw [diagCountF_cons]
    simp_rw [diagCountF_zero]
    have h2 : ∀ y : F, (c - a 0 * y ^ 2 = 0) ↔ a 0 * y ^ 2 = c := fun y => by
      constructor <;> intro h <;> linear_combination -h
    simp_rw [h2]
    rw [sum_ite_mul_sq_eqF hF _ _ (ha 0), map_mul]
    simp
  | succ k ih =>
    intro m hm a ha c
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨2 * k + 1, by omega⟩
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountF_cons_cons hF _ _ (ha 0) (ha 1),
      ih m' (by omega) (Fin.tail (Fin.tail a)) (fun i => ha _) c]
    obtain rfl : m' = 2 * k + 1 := by omega
    have hprod : ∏ i, a i = a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i) := by
      conv_lhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rfl
    rw [hprod]
    have hχ : quadraticChar F ((-1) ^ (k + 1) * (a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i))) =
        quadraticChar F (-(a 0 * a 1)) *
          quadraticChar F ((-1) ^ k * ∏ i, Fin.tail (Fin.tail a) i) := by
      rw [← map_mul]; congr 1; ring
    rw [hχ]
    ring

/-- **Table 1 over $\mathbb{F}$, $n = 2k+2$ even:**
$r(c) = q^{2k+1} + \chi((-1)^{k+1} D)\, q^k (q[c = 0] - 1)$. -/
theorem diagCountF_even (hF : ringChar F ≠ 2) (k : ℕ) :
    ∀ (m : ℕ), m = 2 * k + 2 → ∀ (a : Fin m → F), (∀ i, a i ≠ 0) → ∀ c : F,
      diagCountF a c = (Fintype.card F : ℤ) ^ (2 * k + 1) +
        quadraticChar F ((-1) ^ (k + 1) * ∏ i, a i) * (Fintype.card F : ℤ) ^ k *
          ((Fintype.card F : ℤ) * (if c = 0 then 1 else 0) - 1) := by
  induction k with
  | zero =>
    intro m hm a ha c
    obtain rfl : m = 2 := by simpa using hm
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountF_cons_cons hF _ _ (ha 0) (ha 1), diagCountF_zero, Fin.prod_univ_two]
    have : (-1) ^ (0 + 1) * (a 0 * a 1) = -(a 0 * a 1) := by ring
    rw [this]
    ring
  | succ k ih =>
    intro m hm a ha c
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨2 * k + 2, by omega⟩
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountF_cons_cons hF _ _ (ha 0) (ha 1),
      ih m' (by omega) (Fin.tail (Fin.tail a)) (fun i => ha _) c]
    obtain rfl : m' = 2 * k + 2 := by omega
    have hprod : ∏ i, a i = a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i) := by
      conv_lhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rfl
    rw [hprod]
    have hχ : quadraticChar F ((-1) ^ (k + 1 + 1) * (a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i))) =
        quadraticChar F (-(a 0 * a 1)) *
          quadraticChar F ((-1) ^ (k + 1) * ∏ i, Fin.tail (Fin.tail a) i) := by
      rw [← map_mul]; congr 1; ring
    rw [hχ]
    ring

end FiniteField

/-! ### From $R$ to the residue field -/

section NonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-- $\pi \mid a$ iff $a \equiv 0$ in the residue field. -/
theorem residue_eq_zero_iff_dvd {π : R} (hπ : Irreducible π) (a : R) : res a = 0 ↔ π ∣ a := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

/-- **Non-dyadic residue field:** if $\pi \nmid 2$ then $\mathrm{char}(R/\pi) \ne 2$. -/
theorem ringChar_residueField_ne_two {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    ringChar 𝔽 ≠ 2 := by
  intro h
  apply h2
  rw [← residue_eq_zero_iff_dvd hπ, map_ofNat]
  have := ringChar.Nat.cast_ringChar (R := 𝔽)
  rw [h] at this
  exact_mod_cast this

/-- At a non-dyadic prime, $q = \#R/\pi \ge 3$ (it is odd and $\ge 2$). -/
theorem three_le_q [Fintype 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) : 3 ≤ q R := by
  have h1 := FiniteField.odd_card_of_char_ne_two (ringChar_residueField_ne_two hπ h2)
  have h3 : 1 < Fintype.card 𝔽 := Fintype.one_lt_card
  rw [q, Nat.card_eq_fintype_card]
  omega

/-- $R/\pi^1 \cong R/\pi$, the residue field. -/
noncomputable def quotPiEquivResidue {π : R} (hπ : Irreducible π) :
    R ⧸ Ideal.span {π ^ 1} ≃+* 𝔽 :=
  Ideal.quotEquivOfEq (by rw [pow_one, hπ.maximalIdeal_eq])

theorem quotPiEquivResidue_mk {π : R} (hπ : Irreducible π) (r : R) :
    quotPiEquivResidue hπ (Ideal.Quotient.mk _ r) = res r := rfl

/-- The value of a diagonal form: $\langle a \rangle(\vec{x}) = \sum_i a_i x_i^2$. -/
theorem evalIn_diag {S : Type*} [CommRing S] [Algebra R S] (a : Fin n → R) (x : Fin n → S) :
    (QuadForm.diag a).evalIn S x = ∑ i, algebraMap R S (a i) * x i ^ 2 := by
  simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- `repCount` of a diagonal form mod $\pi$ is the residue-field count `diagCountF`. -/
theorem repCount_diag_one_eq [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) {π : R}
    (hπ : Irreducible π) (c : R) :
    (repCount (QuadForm.diag a) π 1 c : ℤ) = diagCountF (fun i => res (a i)) (res c) := by
  set e := quotPiEquivResidue hπ
  let E : (Fin n → R ⧸ Ideal.span {π ^ 1}) ≃ (Fin n → 𝔽) := Equiv.piCongrRight fun _ => e.toEquiv
  have hval : ∀ x, (QuadForm.diag a).evalIn _ x = Ideal.Quotient.mk _ c ↔
      ∑ i, res (a i) * E x i ^ 2 = res c := by
    intro x
    rw [← e.injective.eq_iff, evalIn_diag, map_sum]
    simp only [map_mul, map_pow, Ideal.Quotient.algebraMap_eq]
    rfl
  unfold repCount
  rw [Nat.card_congr (E.subtypeEquiv (q := fun y => ∑ i, res (a i) * y i ^ 2 = res c) hval), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum]
  unfold diagCountF
  push_cast
  rfl

/-- **Table 1 for all $n$ over a DVR** (Hanke 2004, Table 1, p. 363, for $\mathfrak{p} \nmid 2N$, extended to all $n$;
Kitaoka Lemmas 1.3.1–1.3.2): for $\pi \nmid 2$, a diagonal form with all $a_i$ units, $n \ge 1$, $u$ a unit,
$q = \#R/\pi$, $D = \prod a_i$ and $\chi$ the quadratic character of $R/\pi$:
- $n$ even, $\chi_D = \chi((-1)^{n/2}D)$: $r_\pi(0) = q^{n-1} + \chi_D (q-1) q^{n/2-1}$ and $r_\pi(u) = q^{n-1} - \chi_D q^{n/2-1}$;
- $n$ odd: $r_\pi(0) = q^{n-1}$ and $r_\pi(u) = q^{n-1} + \chi((-1)^{(n-1)/2}Du)\, q^{(n-1)/2}$.
The $\mathbb{Q}$ version is `LocalDensity.card_diag_mod_p` ($q = p$, $\chi$ = Legendre symbol); $n \le 4$ is the
printed table. *Proof:* as over $\mathbb{F}_p$ (`diagCountF_odd`, `diagCountF_even`). -/
@[kb "hanke2004" "Table 1, p. 363 (all n)"]
theorem card_diag_mod_pi [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 1 ≤ n) (u : R) (hu : ¬ π ∣ u) :
    (Even n →
      (repCount (QuadForm.diag a) π 1 0 : ℤ) =
          (q R : ℤ) ^ (n - 1) + quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) *
            ((q R : ℤ) - 1) * (q R : ℤ) ^ (n / 2 - 1) ∧
      (repCount (QuadForm.diag a) π 1 u : ℤ) =
          (q R : ℤ) ^ (n - 1) - quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) *
            (q R : ℤ) ^ (n / 2 - 1)) ∧
    (Odd n →
      repCount (QuadForm.diag a) π 1 0 = q R ^ (n - 1) ∧
      (repCount (QuadForm.diag a) π 1 u : ℤ) =
          (q R : ℤ) ^ (n - 1) + quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * u)) *
            (q R : ℤ) ^ ((n - 1) / 2)) := by
  have hF := ringChar_residueField_ne_two hπ h2
  have hq : (q R : ℤ) = Fintype.card 𝔽 := by rw [q, Nat.card_eq_fintype_card]
  have hne : ∀ t : R, ¬ π ∣ t → res t ≠ 0 := fun t ht h => ht ((residue_eq_zero_iff_dvd hπ t).1 h)
  have ha' : ∀ i, ((fun i => res (a i)) i) ≠ 0 := fun i => hne _ (ha i)
  have hu' := hne u hu
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by obtain ⟨j, hj⟩ := he; omega⟩
    have e1 : (2 * k + 2) / 2 = k + 1 := by omega
    have e2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [e1, e2, Nat.add_sub_cancel, repCount_diag_one_eq a hπ, repCount_diag_one_eq a hπ,
      diagCountF_even hF k _ rfl _ ha', diagCountF_even hF k _ rfl _ ha', hq]
    simp only [map_mul, map_pow, map_neg, map_one, map_prod, map_zero, ↓reduceIte, hu']
    constructor <;> ring
  · obtain ⟨k, rfl⟩ := ho
    have e1 : (2 * k + 1 - 1) / 2 = k := by omega
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [e1, e2]
    have h0 := diagCountF_odd hF k _ rfl _ ha' (res 0)
    have h1 := diagCountF_odd hF k _ rfl _ ha' (res u)
    rw [← repCount_diag_one_eq a hπ, ← hq] at h0 h1
    refine ⟨?_, ?_⟩
    · simp only [map_zero, MulChar.map_zero, mul_zero, add_zero] at h0
      exact_mod_cast h0
    · rw [h1]
      simp only [map_mul, map_pow, map_neg, map_one, map_prod]
      ring

/-- A diagonal form with unit coefficients is in normal form with no pairs and $w = 0$. -/
theorem isJordanFormW_diag_unit (a : Fin n → R) {π : R} (hπ : Irreducible π) (ha : ∀ i, ¬ π ∣ a i) :
    IsJordanFormW (QuadForm.diag a) π ∅ 0 := by
  refine ⟨fun h => absurd h Finset.not_nonempty_empty, fun e he => absurd he (Finset.notMem_empty e),
    fun e he => absurd he (Finset.notMem_empty e), fun i j hij _ => ?_,
    fun e he => absurd he (Finset.notMem_empty e), fun i _ => ⟨a i, ?_, dvr_isUnit_of_not_dvd hπ (ha i)⟩⟩
  · simp [QuadForm.diag, hij.ne]
  · simp [QuadForm.diag]

/-- With all coordinates unimodular, Good type = not Zero type. -/
theorem isGoodType_unimodularCoords_zero (π : R) (k : ℕ) :
    IsGoodType (unimodularCoords (0 : Fin n → ℕ)) π k = fun x => ¬ IsZeroType π k x := by
  funext x
  apply propext
  simp only [IsGoodType, IsZeroType, unimodularCoords, Pi.zero_apply, Finset.mem_filter,
    Finset.mem_univ, true_and, not_forall]
  tauto

/-- **Lemma 3.2 for unimodular diagonal forms at non-dyadic $\pi$**: $r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^{1+l}}(m) =
q^{(n-1)l}\, r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi}(m)$ (no Bad type; Remark 3.4.1(b)). -/
theorem repCountOf_nonZero_diag_succ (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (m : R) (l : ℕ) :
    repCountOf (QuadForm.diag a) π (1 + l) m (fun x => ¬ IsZeroType π (1 + l) x) =
      q R ^ ((n - 1) * l) * repCountOf (QuadForm.diag a) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
  have h := repCountGood_add (QuadForm.diag a) π hπ ∅ 0 (isJordanFormW_diag_unit a hπ ha) 0
    ⟨by simp, by simpa using h2⟩ m 1 l (by omega)
  rwa [isGoodType_unimodularCoords_zero, isGoodType_unimodularCoords_zero] at h

open Classical in
/-- Mod $\pi$, the only Zero-type vector is $\vec 0$: $r_\pi(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(m) + [\pi \mid m]$. -/
theorem repCount_one_eq_nonZero_add [Finite 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (m : R) :
    repCount Q π 1 m = repCountOf Q π 1 m (fun x => ¬ IsZeroType π 1 x) +
      if π ∣ m then 1 else 0 := by
  rw [repCount_eq_zero_add_nonZero Q π hπ, add_comm]
  congr 1
  have hp0 : (Ideal.Quotient.mk (Ideal.span {π ^ 1}) π) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (by rw [pow_one]))
  have hz : ∀ x : Fin n → R ⧸ Ideal.span {π ^ 1}, IsZeroType π 1 x ↔ x = 0 := by
    intro x
    simp only [IsZeroType, hp0, zero_dvd_iff, funext_iff, Pi.zero_apply]
  have h0 : Q.evalIn (R ⧸ Ideal.span {π ^ 1}) 0 = 0 := by simp [QuadForm.evalIn]
  have hm : (Ideal.Quotient.mk (Ideal.span {π ^ 1}) m = 0) ↔ π ∣ m := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
  unfold repCountOf
  split_ifs with h
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun u v => Subtype.ext (((hz _).1 u.2.2).trans ((hz _).1 v.2.2).symm)⟩,
      ⟨⟨0, by rw [h0, hm.2 h], (hz 0).2 rfl⟩⟩⟩
  · rw [Nat.card_eq_zero]; left
    exact ⟨fun u => h (hm.1 (by rw [← u.2.1, (hz _).1 u.2.2, h0]))⟩

/-- Normalized non-Zero-type counts of a unimodular diagonal form at non-dyadic $\pi$ are constant from
$k = 1$. -/
theorem normalized_nonZero_diag [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (m : R) (k : ℕ) (hk : 1 ≤ k) :
    (repCountOf (QuadForm.diag a) π k m (fun x => ¬ IsZeroType π k x) : ℝ) / (q R : ℝ) ^ (k * (n - 1)) =
      (repCountOf (QuadForm.diag a) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℝ) / (q R : ℝ) ^ (n - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  rw [repCountOf_nonZero_diag_succ a π hπ h2 ha m l,
    show (1 + l) * (n - 1) = (n - 1) + (n - 1) * l by ring, pow_add]
  push_cast
  field_simp

/-- $\beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(m)/q^{n-1}$ for a unimodular diagonal
form at non-dyadic $\pi$. -/
theorem localDensityOf_nonZero_diag [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (m : R) :
    localDensityOf (QuadForm.diag a) π m (fun k x => ¬ IsZeroType π k x) =
      (repCountOf (QuadForm.diag a) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℝ) / (q R : ℝ) ^ (n - 1) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  exact normalized_nonZero_diag a π hπ h2 ha m k hk

/-- If $\pi^2 \nmid m$ there are no Zero-type solutions for $k \ge 2$, so for a unimodular diagonal form at
non-dyadic $\pi$, $\beta_\pi(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(m)/q^{n-1}$. -/
theorem localDensity_diag_of_not_sq_dvd [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (m : R) (hm : ¬ π ^ 2 ∣ m) :
    localDensity (QuadForm.diag a) π m =
      (repCountOf (QuadForm.diag a) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℝ) / (q R : ℝ) ^ (n - 1) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  rw [repCount_eq_zero_add_nonZero _ π hπ,
    repCountOf_eq_zero_of_not_dvd _ π ∅ 0 (isJordanFormW_diag_unit a hπ ha) m k 2 le_rfl hk hm
      (IsZeroType π k) (fun x hx i _ => hx i), zero_add]
  exact normalized_nonZero_diag a π hπ h2 ha m k (by omega)

/-- Counts of a given type depend on $m$ only mod $\pi^k$. -/
theorem repCountOf_congr (Q : QuadForm R n) (π : R) (k : ℕ) {m m' : R}
    (h : Ideal.Quotient.mk (Ideal.span {π ^ k}) m = Ideal.Quotient.mk _ m')
    (T : (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop) :
    repCountOf Q π k m T = repCountOf Q π k m' T := by
  unfold repCountOf; rw [h]

theorem mk_pow_one_eq_zero_iff (π m : R) :
    Ideal.Quotient.mk (Ideal.span {π ^ 1}) m = Ideal.Quotient.mk _ 0 ↔ π ∣ m := by
  rw [map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]

/-- $K_0 = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2T) = (r_\pi(0) - 1)/q^{n-1}$ for a unimodular diagonal form at
non-dyadic $\pi$ (the nonzero solutions of $Q \equiv 0 \pmod \pi$, all of Good type). -/
theorem localDensityOf_nonZero_diag_sq [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (T : R) :
    localDensityOf (QuadForm.diag a) π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) =
      ((repCount (QuadForm.diag a) π 1 0 : ℝ) - 1) / (q R : ℝ) ^ (n - 1) := by
  have hc : Ideal.Quotient.mk (Ideal.span {π ^ 1}) (π ^ 2 * T) = Ideal.Quotient.mk _ 0 :=
    (mk_pow_one_eq_zero_iff π _).2 (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)
  rw [localDensityOf_nonZero_diag a π hπ h2 ha, repCountOf_congr _ π 1 hc,
    repCount_one_eq_nonZero_add _ π hπ 0]
  simp

/-- $\beta_\pi(T)$ for $\mathrm{ord}_\pi(T) = 1$: equal to $K_0 = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2T)$
(Remark 5.4.1(b)). -/
theorem localDensity_diag_ord_one [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (T : R) (hT1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localDensity (QuadForm.diag a) π T =
      ((repCount (QuadForm.diag a) π 1 0 : ℝ) - 1) / (q R : ℝ) ^ (n - 1) := by
  rw [localDensity_diag_of_not_sq_dvd a π hπ h2 ha T hT2,
    repCountOf_congr _ π 1 (m' := 0) ((mk_pow_one_eq_zero_iff π T).2 hT1),
    repCount_one_eq_nonZero_add _ π hπ 0]
  simp

/-- **Local densities at units, non-dyadic $\pi$** (Hanke 2004, Remark 3.4.1(a), p. 361, with Lemma 3.2): for a
unimodular diagonal form at $\pi \nmid 2$ and $\pi \nmid m$, $\beta_\pi(m) = r_\pi(m)/q^{n-1}$. The $\mathbb{Q}$ version is
`LocalDensity.localDensity_unit`. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; Lemma 3.2"]
theorem localDensity_unit [Finite 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (ha : ∀ i, ¬ π ∣ a i) (m : R) (hm : ¬ π ∣ m) :
    localDensity (QuadForm.diag a) π m = (repCount (QuadForm.diag a) π 1 m : ℝ) / (q R : ℝ) ^ (n - 1) := by
  rw [localDensity_diag_of_not_sq_dvd a π hπ h2 ha m
      (fun h => hm (dvd_trans (dvd_pow_self _ two_ne_zero) h)),
    repCount_one_eq_nonZero_add _ π hπ m]
  simp [hm]

/-- **Remark 3.5.1 over a DVR** (Hanke 2004, p. 362): for $n \ge 3$ and $\mathfrak{p} \nmid 2N$ (here: a diagonal form
with all $a_i$ units at $\pi \nmid 2$), every $m$ is locally represented at $\pi$. *Proof:* every residue mod
$\pi$ has a Good-type solution (Chevalley–Warning style: two quadratics over $\mathbb{F}$ of odd order,
`FiniteField.exists_root_sum_quadratic`), and Good-type solutions lift (Lemma 3.2). -/
@[kb "hanke2004" "Remark 3.5.1, p. 362"]
theorem isLocallyRepresentedAt_of_good [Fintype 𝔽] (a : Fin n → R) (hn : 3 ≤ n) (π : R)
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (m : R) :
    IsLocallyRepresentedAt (QuadForm.diag a) π m := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  have hF := ringChar_residueField_ne_two hπ h2
  have hcard := FiniteField.odd_card_of_char_ne_two hF
  have hne : ∀ i, res (a i) ≠ 0 := fun i h => ha i ((residue_eq_zero_iff_dvd hπ _).1 h)
  obtain ⟨y0, y1, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C (res (a 0)) * Polynomial.X ^ 2 + Polynomial.C (res (a 2 - m)))
    (g := Polynomial.C (res (a 1)) * Polynomial.X ^ 2)
    (by compute_degree!; exact dvr_isUnit_of_not_dvd hπ (ha 0))
    (by compute_degree!; exact dvr_isUnit_of_not_dvd hπ (ha 1)) hcard
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective y0
  obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y1
  have huv : π ∣ a 0 * u ^ 2 + a 1 * v ^ 2 + a 2 - m := by
    rw [← residue_eq_zero_iff_dvd hπ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, map_sub] at h
    simp only [map_sub, map_add, map_mul, map_pow]
    linear_combination h
  set w : Fin (n' + 3) → R := Fin.cons u (Fin.cons v (Fin.cons 1 0)) with hw
  have hsum : (QuadForm.diag a).eval w = a 0 * u ^ 2 + a 1 * v ^ 2 + a 2 := by
    change (QuadForm.diag a).evalIn R w = _
    rw [evalIn_diag]
    simp [hw, Fin.sum_univ_succ]
    ring
  have hpos : 0 < repCountOf (QuadForm.diag a) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
    have := finite_quot_pow π hπ 1
    rw [repCountOf, Nat.card_pos_iff]
    refine ⟨⟨⟨redV π 1 w, ?_, ?_⟩⟩, inferInstance⟩
    · rw [evalIn_redV, mk_eq_mk_iff, pow_one, hsum]; exact huv
    · intro h
      have h1 := (mk_pi_dvd_iff π 1 le_rfl (w 2)).1 (h 2)
      have hw2 : w 2 = 1 := by simp [hw]; rfl
      rw [hw2] at h1
      exact hπ.not_isUnit (isUnit_of_dvd_one h1)
  rw [IsLocallyRepresentedAt, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have := repCountOf_nonZero_diag_succ a π hπ h2 ha m l
  have hle := repCountOf_le_repCount (QuadForm.diag a) π hπ (1 + l) m
    (fun x => ¬ IsZeroType π (1 + l) x)
  refine lt_of_lt_of_le ?_ hle
  rw [this]
  exact Nat.mul_pos (pow_pos q_pos _) hpos

/-! ### Table 2 and (5.10) -/

/-- **The local constant $C_\pi(T')$ over $R$** (Hanke 2004, after (5.8), p. 370):
$C_\pi(T') = \frac{q^{n-2}}{q^{n-2} - 1} \cdot \frac{K_0}{\beta_\pi(T')}$ with $K_0 = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2 T')$, the
non-Zero-type density at $\pi^2T'$ (as `LocalDensity.localConstC`). -/
noncomputable def localConstC (Q : QuadForm R n) (π : R) (T : R) : ℝ :=
  ((q R : ℝ) ^ (n - 2) / ((q R : ℝ) ^ (n - 2) - 1)) *
    (localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) / localDensity Q π T)

theorem residue_sign_prod_ne_zero (a : Fin n → R) {π : R} (hπ : Irreducible π)
    (ha : ∀ i, ¬ π ∣ a i) (s : ℕ) : res ((-1) ^ s * ∏ i, a i) ≠ 0 := by
  simp only [map_mul, map_pow, map_neg, map_one, map_prod]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (Finset.prod_ne_zero_iff.2 fun i _ h => ha i ((residue_eq_zero_iff_dvd hπ _).1 h))

/-- **Table 2, $n$ odd, $\pi \nmid T'$** (Hanke 2004, Table 2, p. 370) over a DVR at $\pi \nmid 2$:
$C_\pi(T') = \dfrac{q^{n-2} - q^{(n-3)/2}\Phi_n(\pi)}{q^{n-2} - 1}$, $\Phi_n(\pi) = \chi((-1)^{(n-1)/2} D T')$.
*Proof:* (5.9) with the Good-type densities from `card_diag_mod_pi` and Lemma 3.2.
*Clarification (candidate; pending author):* Table 2 is headed $\mathfrak{p} \nmid N$, but $\Phi_n(\mathfrak{p})$ is defined
(p. 357) only for $\mathfrak{p} \nmid 2N$; this is the $\mathfrak{p} \nmid 2N$ case. -/
@[kb "hanke2004" "Table 2, p. 370"]
theorem table2_odd_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : R) (hT : ¬ π ∣ T) :
    localConstC (QuadForm.diag a) π T =
      ((q R : ℝ) ^ (n - 2) - (q R : ℝ) ^ ((n - 3) / 2) *
          quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T))) /
        ((q R : ℝ) ^ (n - 2) - 1) := by
  obtain ⟨r0, rT⟩ := (card_diag_mod_pi a π hπ h2 ha (by omega) T hT).2 hodd
  have hc : ((quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) : ℤ) : ℝ) ^ 2 = 1 := by
    have : res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (residue_sign_prod_ne_zero a hπ ha _)
        (fun h => hT ((residue_eq_zero_iff_dvd hπ _).1 h))
    exact_mod_cast quadraticChar_sq_one this
  generalize quadraticChar 𝔽 (res ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) = c at rT hc ⊢
  have r0' : (repCount (QuadForm.diag a) π 1 0 : ℝ) = (q R : ℝ) ^ (n - 1) := by exact_mod_cast r0
  have rT' : (repCount (QuadForm.diag a) π 1 T : ℝ) =
      (q R : ℝ) ^ (n - 1) + c * (q R : ℝ) ^ ((n - 1) / 2) := by
    exact_mod_cast rT
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a π hπ h2 ha, localDensity_unit a π hπ h2 ha T hT, r0', rT']
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 3 := by obtain ⟨m, rfl⟩ := hodd; exact ⟨m - 1, by omega⟩
  have hP : (3 : ℝ) ≤ q R := by exact_mod_cast three_le_q hπ h2
  have e1 : 2 * j + 3 - 2 = 2 * j + 1 := by omega
  have e2 : 2 * j + 3 - 1 = 2 * j + 2 := by omega
  have e3 : (2 * j + 3 - 3) / 2 = j := by omega
  have e4 : (2 * j + 3 - 1) / 2 = j + 1 := by omega
  rw [e3, e4, e1, e2]
  have := table2_odd_alg (q R : ℝ) ((q R : ℝ) ^ j) c hP (one_le_pow₀ (by linarith)) hc
  rw [show (q R : ℝ) ^ (2 * j + 1) = ((q R : ℝ) ^ j) ^ 2 * q R by ring,
    show (q R : ℝ) ^ (2 * j + 2) = ((q R : ℝ) ^ j) ^ 2 * (q R) ^ 2 by ring,
    show (q R : ℝ) ^ (j + 1) = (q R : ℝ) ^ j * q R by ring]
  rw [← this]

/-- **Table 2, $n$ even, $\pi \nmid T'$** (Hanke 2004, Table 2, p. 370) over a DVR at $\pi \nmid 2$:
$C_\pi(T') = \dfrac{q^{(n-2)/2}}{q^{(n-2)/2} - \Phi_n(\pi)}$, $\Phi_n(\pi) = \chi((-1)^{n/2} D)$. -/
@[kb "hanke2004" "Table 2, p. 370"]
theorem table2_even_unit [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (heven : Even n) (T : R) (hT : ¬ π ∣ T) :
    localConstC (QuadForm.diag a) π T =
      (q R : ℝ) ^ ((n - 2) / 2) /
        ((q R : ℝ) ^ ((n - 2) / 2) - quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i))) := by
  obtain ⟨r0, rT⟩ := (card_diag_mod_pi a π hπ h2 ha (by omega) T hT).1 heven
  have hc : ((quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (residue_sign_prod_ne_zero a hπ ha _)
  generalize quadraticChar 𝔽 (res ((-1) ^ (n / 2) * ∏ i, a i)) = c at r0 rT hc ⊢
  have r0' : (repCount (QuadForm.diag a) π 1 0 : ℝ) =
      (q R : ℝ) ^ (n - 1) + c * ((q R : ℝ) - 1) * (q R : ℝ) ^ (n / 2 - 1) := by exact_mod_cast r0
  have rT' : (repCount (QuadForm.diag a) π 1 T : ℝ) =
      (q R : ℝ) ^ (n - 1) - c * (q R : ℝ) ^ (n / 2 - 1) := by
    exact_mod_cast rT
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a π hπ h2 ha, localDensity_unit a π hπ h2 ha T hT, r0', rT']
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 2, by omega⟩
  have hP : (3 : ℝ) ≤ q R := by exact_mod_cast three_le_q hπ h2
  have e1 : 2 * j + 4 - 2 = 2 * (j + 1) := by omega
  have e2 : 2 * j + 4 - 1 = 2 * (j + 1) + 1 := by omega
  have e3 : (2 * j + 4 - 2) / 2 = j + 1 := by omega
  have e4 : (2 * j + 4) / 2 - 1 = j + 1 := by omega
  rw [e3, e4, e1, e2]
  have hY : (3 : ℝ) ≤ (q R : ℝ) ^ (j + 1) := le_trans hP (le_self_pow₀ (by linarith) (by omega))
  have := table2_even_alg (q R : ℝ) ((q R : ℝ) ^ (j + 1)) c hP hY hc
  rw [pow_mul, pow_succ (_ ^ 2), ← pow_mul, ← this]
  ring

/-- **Table 2, $\mathrm{ord}_\pi(T') = 1$** (Hanke 2004, Table 2, p. 370; (5.9)) over a DVR at $\pi \nmid 2$:
$C_\pi(T') = \dfrac{q^{n-2}}{q^{n-2} - 1}$ for both parities (no Zero-type or Bad-type solutions, Remark 5.4.1(b)). -/
@[kb "hanke2004" "Table 2, p. 370; (5.9)"]
theorem table2_ord_one [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin n → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (hn : 3 ≤ n) (T : R) (hT1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC (QuadForm.diag a) π T = (q R : ℝ) ^ (n - 2) / ((q R : ℝ) ^ (n - 2) - 1) := by
  have hq3 := three_le_q hπ h2
  have h2' : (2 : ℤ) ≤ repCount (QuadForm.diag a) π 1 0 := by
    have hcd := card_diag_mod_pi a π hπ h2 ha (by omega) 1 (fun h => hπ.not_isUnit (isUnit_of_dvd_one h))
    rcases Nat.even_or_odd n with he | ho
    · rw [(hcd.1 he).1]
      obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := by obtain ⟨m, rfl⟩ := he; exact ⟨m - 2, by omega⟩
      have e2 : 2 * j + 4 - 1 = 2 * (j + 1) + 1 := by omega
      have e4 : (2 * j + 4) / 2 - 1 = j + 1 := by omega
      rw [e2, e4]
      have hc := quadraticChar_dichotomy (residue_sign_prod_ne_zero a hπ ha ((2 * j + 4) / 2))
      have hP : (3 : ℤ) ≤ q R := by exact_mod_cast hq3
      have hY : (3 : ℤ) ≤ (q R : ℤ) ^ (j + 1) := le_trans hP (le_self_pow₀ (by linarith) (by omega))
      rw [show (q R : ℤ) ^ (2 * (j + 1) + 1) = ((q R : ℤ) ^ (j + 1)) ^ 2 * q R by ring]
      have hnn : (0 : ℤ) ≤ (q R : ℤ) * (q R : ℤ) ^ (j + 1) * ((q R : ℤ) ^ (j + 1) - 1) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      rcases hc with hc | hc <;> rw [hc] <;> nlinarith
    · rw [(hcd.2 ho).1]
      have : q R ≤ q R ^ (n - 1) := le_self_pow₀ (by omega) (by omega)
      push_cast; exact_mod_cast (show 2 ≤ q R ^ (n - 1) by omega)
  have hne : ((repCount (QuadForm.diag a) π 1 0 : ℝ) - 1) / (q R : ℝ) ^ (n - 1) ≠ 0 := by
    have hq0 : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
    have : (2 : ℝ) ≤ repCount (QuadForm.diag a) π 1 0 := by exact_mod_cast h2'
    exact div_ne_zero (by linarith) (pow_ne_zero _ hq0.ne')
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a π hπ h2 ha, localDensity_diag_ord_one a π hπ h2 ha T hT1 hT2,
    div_self hne, mul_one]

/-- **(5.10), $n = 3$, over a DVR** (Hanke 2004, p. 371, stated there over $\mathbb{Q}$): for a unimodular ternary
diagonal form at $\pi \nmid 2$, $\psi = \Phi_3(\pi, T') = \chi(-DT')$ and $\nu \ge 0$, with $q = \#R/\pi$,
$C_\pi(T') + \dfrac{1 - C_\pi(T')}{q^\nu} = \dfrac{1}{q^\nu}\cdot\begin{cases} q^\nu & \pi \nmid T',\ \psi = 1,\\
q^\nu + 2\sum_{\mu=0}^{\nu-1} q^\mu & \pi \nmid T',\ \psi = -1,\\ \sum_{\mu=0}^{\nu} q^\mu & \mathrm{ord}_\pi(T') = 1.\end{cases}$
*Proof:* substitute Table 2 with $n = 3$. -/
@[kb "hanke2004" "(5.10), p. 371"]
theorem eq_5_10 [Fintype 𝔽] [DecidableEq 𝔽] (a : Fin 3 → R) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) (T : R) (ν : ℕ) :
    let C := localConstC (QuadForm.diag a) π T
    let ψ := quadraticChar 𝔽 (res (-(∏ i, a i) * T))
    (¬ π ∣ T → ψ = 1 → C + (1 - C) / (q R : ℝ) ^ ν = 1) ∧
    (¬ π ∣ T → ψ = -1 →
      C + (1 - C) / (q R : ℝ) ^ ν =
        ((q R : ℝ) ^ ν + 2 * ∑ μ ∈ Finset.range ν, (q R : ℝ) ^ μ) / (q R : ℝ) ^ ν) ∧
    (π ∣ T → ¬ π ^ 2 ∣ T →
      C + (1 - C) / (q R : ℝ) ^ ν = (∑ μ ∈ Finset.range (ν + 1), (q R : ℝ) ^ μ) / (q R : ℝ) ^ ν) := by
  intro C ψ
  have hP : (3 : ℝ) ≤ q R := by exact_mod_cast three_le_q hπ h2
  have hp1 : (q R : ℝ) - 1 ≠ 0 := by linarith
  have hpν : (q R : ℝ) ^ ν ≠ 0 := pow_ne_zero _ (by linarith)
  have hodd : ∀ hT : ¬ π ∣ T, C = ((q R : ℝ) - ψ) / ((q R : ℝ) - 1) := by
    intro hT
    have h := table2_odd_unit a π hπ h2 ha le_rfl (by decide) T hT
    simp only [show 3 - 2 = 1 by rfl, show (3 - 3) / 2 = 0 by rfl, show (3 - 1) / 2 = 1 by rfl,
      pow_one, pow_zero, one_mul, neg_one_mul] at h
    exact h
  refine ⟨fun hT hψ => ?_, fun hT hψ => ?_, fun hT1 hT2 => ?_⟩
  · rw [hodd hT, hψ]; push_cast; field_simp; ring
  · rw [hodd hT, hψ, geom_sum_eq (by linarith)]; push_cast; field_simp; ring
  · have h := table2_ord_one a π hπ h2 ha le_rfl T hT1 hT2
    simp only [show 3 - 2 = 1 by rfl, pow_one] at h
    change C = _ at h
    rw [h, geom_sum_eq (by linarith)]; field_simp; ring

end NonDyadic

end QuadFormsKB.LocalDensity.DVR
