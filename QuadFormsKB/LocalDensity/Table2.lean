/-
# Local densities over $\mathbb{Q}$: local constants at good primes, Table 2 and (5.8)–(5.10)

**Layer:** $\mathbb{Q}$, at odd $p \nmid N$ (diagonal unimodular forms $\langle a_0, \dots, a_{n-1}\rangle$,
$D = \prod a_i$, character $\Phi_n$ of p. 357). **Proves** Table 1 for all $n$ (p. 363; `card_diag_mod_p`),
$\beta_p$ at units (Remark 3.4.1(a), p. 361; `localDensity_unit`), Table 2 (p. 370; `table2_odd_unit`,
`table2_even_unit`, `table2_ord_one`, with (5.9)) and (5.10) (p. 371; `eq_5_10`); the local constant is
`localConstC` ((5.8), p. 370). **Depends on** `Explicit.lean`. No errata found in Table 2.
-/
import QuadFormsKB.LocalDensity.Explicit

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **The local constant $C_p(T')$** (Hanke 2004, after (5.8), p. 370):
$C_p(T') = \frac{q^{n-2}}{q^{n-2} - 1} \cdot \frac{K}{\beta_p(T')}$ with $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2 T')$, the
non-Zero-type density at $p^2T'$. -/
noncomputable def localConstC (Q : QuadForm ℤ n) (p : ℕ) (T : ℤ) : ℝ :=
  ((p : ℝ) ^ (n - 2) / ((p : ℝ) ^ (n - 2) - 1)) *
    (localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) / localDensity Q p T)

/-- The number (as an integer) of $\vec{x} \in \mathbb{F}_p^m$ with $\sum_i a_i x_i^2 = c$. -/
noncomputable def diagCountModP {p m : ℕ} [NeZero p] (a : Fin m → ZMod p) (c : ZMod p) : ℤ :=
  ∑ x : Fin m → ZMod p, if ∑ i, a i * x i ^ 2 = c then 1 else 0

/-- Splitting off the first variable: $r_{a_0 \oplus a}(c) = \sum_y r_a(c - a_0 y^2)$. -/
theorem diagCountModP_cons {p m : ℕ} [NeZero p] (a0 : ZMod p) (a : Fin m → ZMod p) (c : ZMod p) :
    diagCountModP (Fin.cons a0 a : Fin (m + 1) → ZMod p) c =
      ∑ y : ZMod p, diagCountModP a (c - a0 * y ^ 2) := by
  unfold diagCountModP
  rw [← (Fin.consEquiv fun _ => ZMod p).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

/-- The counts sum to the number of vectors: $\sum_c r_a(c) = p^m$. -/
theorem sum_diagCountModP {p m : ℕ} [NeZero p] (a : Fin m → ZMod p) :
    ∑ c : ZMod p, diagCountModP a c = (p : ℤ) ^ m := by
  unfold diagCountModP
  rw [Finset.sum_comm]
  simp

/-- Fibre sum over squares: $\sum_y f(y^2) = \sum_t (1 + \chi(t)) f(t)$. -/
theorem sum_sq_eq_sum_quadraticChar {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (f : ZMod p → ℤ) :
    ∑ y : ZMod p, f (y ^ 2) = ∑ t : ZMod p, (1 + quadraticChar (ZMod p) t) * f t := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have h1 : ∀ y : ZMod p, f (y^2) = ∑ t : ZMod p, if y^2 = t then f t else 0 := by
    intro y; rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have := quadraticChar_card_sqrts hF t
  rw [Set.toFinset_ofPred] at this
  rw [this]; ring

/-- $\sum_y \chi(A + B y^2) = (p-1)\chi(B)$ if $A = 0$, and $-\chi(B)$ otherwise ($B \ne 0$). -/
theorem sum_quadraticChar_add_mul_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (A B : ZMod p)
    (hB : B ≠ 0) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (A + B * y^2) =
      if A = 0 then (p - 1) * quadraticChar (ZMod p) B else - quadraticChar (ZMod p) B := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hlin : ∀ A B : ZMod p, B ≠ 0 → ∑ t : ZMod p, quadraticChar (ZMod p) (A + B * t) = 0 := by
    intro A B hB
    have hbij : Function.Bijective (fun t : ZMod p => A + B * t) := by
      rw [← Finite.injective_iff_bijective]
      intro x y h; simpa [hB] using h
    rw [Fintype.sum_bijective _ hbij _ (fun s => quadraticChar (ZMod p) s) (fun _ => rfl)]
    exact quadraticChar_sum_zero hF
  have hJ : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = - quadraticChar (ZMod p) (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic (ZMod p)).inv] at this
  rw [sum_sq_eq_sum_quadraticChar hp (fun s => (quadraticChar (ZMod p)) (A + B * s))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, hlin A B hB, zero_add]
  have hm1 : (quadraticChar (ZMod p)) (-1) * (quadraticChar (ZMod p)) (-1) = 1 := by
    rw [← map_mul]; norm_num
  split_ifs with hA
  · subst hA
    have : ∀ t : ZMod p, (quadraticChar (ZMod p)) t * (quadraticChar (ZMod p)) (0 + B * t) = (quadraticChar (ZMod p)) B * (1 - if t = 0 then 1 else 0) := by
      intro t
      by_cases ht : t = 0
      · simp [ht, MulChar.map_zero]
      · simp only [ht, ite_false, sub_zero, mul_one, zero_add]
        rw [← map_mul, show t * (B * t) = B * t^2 by ring, map_mul, quadraticChar_sq_one' ht, mul_one]
    simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp; ring
  · have hbij : Function.Bijective (fun s : ZMod p => -A / B * s) := by
      rw [← Finite.injective_iff_bijective]
      intro x y h; simpa [hB, hA] using h
    rw [← Fintype.sum_bijective _ hbij (fun s => (quadraticChar (ZMod p)) (-A / B * s) * (quadraticChar (ZMod p)) (A + B * (-A / B * s))) _ (fun _ => rfl)]
    have : ∀ s : ZMod p, (quadraticChar (ZMod p)) (-A / B * s) * (quadraticChar (ZMod p)) (A + B * (-A / B * s)) = (quadraticChar (ZMod p)) (-B) * ((quadraticChar (ZMod p)) s * (quadraticChar (ZMod p)) (1 - s)) := by
      intro s
      rw [← map_mul, ← map_mul, ← map_mul]
      have : -A / B * s * (A + B * (-A / B * s)) = (A / B)^2 * (-B * (s * (1 - s))) := by
        field_simp; ring
      rw [this, map_mul, quadraticChar_sq_one' (div_ne_zero hA hB), one_mul]
    simp_rw [this, ← Finset.mul_sum]
    rw [← jacobiSum, hJ, show -B = -1 * B by ring, map_mul]
    linear_combination (- (quadraticChar (ZMod p)) B) * hm1

/-- One-variable count: $\#\{x : a x^2 = t\} = 1 + \chi(a t)$ for $a \ne 0$. -/
theorem sum_ite_mul_sq_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (a t : ZMod p) (ha : a ≠ 0) :
    ∑ x : ZMod p, (if a * x^2 = t then 1 else 0 : ℤ) = 1 + quadraticChar (ZMod p) (a * t) := by
  rw [sum_sq_eq_sum_quadraticChar hp (fun s => if a * s = t then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  have : ∀ s : ZMod p, (a * s = t) ↔ s = t / a := by
    intro s; constructor
    · rintro rfl; field_simp
    · rintro rfl; field_simp
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [show a * t = a^2 * (t / a) by field_simp, map_mul, quadraticChar_sq_one' ha, one_mul]

/-- The binary counts of Table 1 over $\mathbb{F}_p$:
$\#\{a y^2 + b z^2 = r\} = p - \eta + p\,\eta\,[r = 0]$ with $\eta = \chi(-ab)$. -/
theorem binary_count_modP {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (b c : ZMod p) (hb : b ≠ 0)
    (hc : c ≠ 0) (r : ZMod p) :
    ∑ y : ZMod p, ∑ z : ZMod p, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) =
      p - quadraticChar (ZMod p) (-(b*c)) + p * quadraticChar (ZMod p) (-(b*c)) * (if r = 0 then 1 else 0) := by
  have hA := fun a t ha => sum_ite_mul_sq_eq (p := p) hp a t ha
  have : ∀ y : ZMod p, ∑ z : ZMod p, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) = 1 + (quadraticChar (ZMod p)) (c * r + (-(c * b)) * y^2) := by
    intro y
    have h2 : ∀ z : ZMod p, (b * y^2 + c * z^2 = r) ↔ c * z^2 = r - b * y^2 := by
      intro z; constructor <;> intro h <;> linear_combination h
    simp_rw [h2]
    rw [hA c _ hc]; ring_nf
  simp_rw [this, Finset.sum_add_distrib, sum_quadraticChar_add_mul_sq hp _ _ (neg_ne_zero.mpr (mul_ne_zero hc hb))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_eq_zero, hc, false_or, ZMod.card]
  rw [show -(c*b) = -(b*c) by ring]
  split_ifs <;> ring

/-- **Two-variable recursion:** $r_{a_0 \oplus a_1 \oplus a}(c) = (p - \eta) p^m + \eta\, p\, r_a(c)$,
$\eta = \chi(-a_0 a_1)$. -/
theorem diagCountModP_cons_cons {p m : ℕ} [Fact p.Prime] (hp : p ≠ 2) (a0 a1 : ZMod p)
    (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (a : Fin m → ZMod p) (c : ZMod p) :
    diagCountModP (Fin.cons a0 (Fin.cons a1 a : Fin (m + 1) → ZMod p) : Fin (m + 2) → ZMod p) c =
      (p - quadraticChar (ZMod p) (-(a0 * a1))) * p ^ m +
        quadraticChar (ZMod p) (-(a0 * a1)) * p * diagCountModP a c := by
  simp_rw [diagCountModP_cons]
  have hconv : ∀ y z : ZMod p, diagCountModP a (c - a0 * y ^ 2 - a1 * z ^ 2) =
      ∑ t : ZMod p, (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ) * diagCountModP a (c - t) := by
    intro y z
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    congr 1; ring
  simp_rw [hconv]
  rw [show (∑ y : ZMod p, ∑ z : ZMod p, ∑ t : ZMod p,
      (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ) * diagCountModP a (c - t)) =
      ∑ t : ZMod p, (∑ y : ZMod p, ∑ z : ZMod p, (if a0 * y^2 + a1 * z^2 = t then 1 else 0 : ℤ)) *
        diagCountModP a (c - t) by
    simp_rw [Finset.sum_mul]
    exact (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans Finset.sum_comm]
  simp_rw [binary_count_modP hp a0 a1 h0 h1]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  have htot : ∑ t : ZMod p, diagCountModP a (c - t) = (p : ℤ) ^ m := by
    rw [← sum_diagCountModP a]
    exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun _ => rfl)
  rw [htot, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, sub_zero]
  ring

/-- No variables: $r_{\emptyset}(c) = [c = 0]$. -/
theorem diagCountModP_zero {p : ℕ} [NeZero p] (a : Fin 0 → ZMod p) (c : ZMod p) :
    diagCountModP a c = if c = 0 then 1 else 0 := by
  simp [diagCountModP, eq_comm]

/-- Split a tuple of length $m+2$ into its first two entries and the rest. -/
theorem fin_cons_cons_self_tail {α : Type*} {m : ℕ} (a : Fin (m + 2) → α) :
    a = Fin.cons (a 0) (Fin.cons (a 1) (Fin.tail (Fin.tail a)) : Fin (m + 1) → α) := by
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> rfl

/-- **Table 1 over $\mathbb{F}_p$, $n = 2k+1$ odd:** $r(c) = p^{2k} + \chi((-1)^k D)\, p^k \chi(c)$. -/
theorem diagCountModP_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) :
    ∀ (m : ℕ), m = 2 * k + 1 → ∀ (a : Fin m → ZMod p), (∀ i, a i ≠ 0) → ∀ c : ZMod p,
      diagCountModP a c = (p : ℤ) ^ (2 * k) +
        quadraticChar (ZMod p) ((-1) ^ k * ∏ i, a i) * p ^ k * quadraticChar (ZMod p) c := by
  induction k with
  | zero =>
    intro m hm a ha c
    obtain rfl : m = 1 := by simpa using hm
    conv_lhs => rw [← Fin.cons_self_tail a]
    rw [diagCountModP_cons]
    simp_rw [diagCountModP_zero]
    have h2 : ∀ y : ZMod p, (c - a 0 * y ^ 2 = 0) ↔ a 0 * y ^ 2 = c := fun y => by
      constructor <;> intro h <;> linear_combination -h
    simp_rw [h2]
    rw [sum_ite_mul_sq_eq hp _ _ (ha 0), map_mul]
    simp
  | succ k ih =>
    intro m hm a ha c
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨2 * k + 1, by omega⟩
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountModP_cons_cons hp _ _ (ha 0) (ha 1),
      ih m' (by omega) (Fin.tail (Fin.tail a)) (fun i => ha _) c]
    obtain rfl : m' = 2 * k + 1 := by omega
    have hprod : ∏ i, a i = a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i) := by
      conv_lhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rfl
    rw [hprod]
    have hχ : quadraticChar (ZMod p) ((-1) ^ (k + 1) * (a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i))) =
        quadraticChar (ZMod p) (-(a 0 * a 1)) *
          quadraticChar (ZMod p) ((-1) ^ k * ∏ i, Fin.tail (Fin.tail a) i) := by
      rw [← map_mul]; congr 1; ring
    rw [hχ]
    ring

/-- **Table 1 over $\mathbb{F}_p$, $n = 2k+2$ even:**
$r(c) = p^{2k+1} + \chi((-1)^{k+1} D)\, p^k (p[c = 0] - 1)$. -/
theorem diagCountModP_even {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) :
    ∀ (m : ℕ), m = 2 * k + 2 → ∀ (a : Fin m → ZMod p), (∀ i, a i ≠ 0) → ∀ c : ZMod p,
      diagCountModP a c = (p : ℤ) ^ (2 * k + 1) +
        quadraticChar (ZMod p) ((-1) ^ (k + 1) * ∏ i, a i) * p ^ k *
          ((p : ℤ) * (if c = 0 then 1 else 0) - 1) := by
  induction k with
  | zero =>
    intro m hm a ha c
    obtain rfl : m = 2 := by simpa using hm
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountModP_cons_cons hp _ _ (ha 0) (ha 1), diagCountModP_zero, Fin.prod_univ_two]
    have : (-1) ^ (0 + 1) * (a 0 * a 1) = -(a 0 * a 1) := by ring
    rw [this]
    ring
  | succ k ih =>
    intro m hm a ha c
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨2 * k + 2, by omega⟩
    conv_lhs => rw [fin_cons_cons_self_tail a]
    rw [diagCountModP_cons_cons hp _ _ (ha 0) (ha 1),
      ih m' (by omega) (Fin.tail (Fin.tail a)) (fun i => ha _) c]
    obtain rfl : m' = 2 * k + 2 := by omega
    have hprod : ∏ i, a i = a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i) := by
      conv_lhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rfl
    rw [hprod]
    have hχ : quadraticChar (ZMod p) ((-1) ^ (k + 1 + 1) * (a 0 * (a 1 * ∏ i, Fin.tail (Fin.tail a) i))) =
        quadraticChar (ZMod p) (-(a 0 * a 1)) *
          quadraticChar (ZMod p) ((-1) ^ (k + 1) * ∏ i, Fin.tail (Fin.tail a) i) := by
      rw [← map_mul]; congr 1; ring
    rw [hχ]
    ring

/-- `repCount` of a diagonal form mod $p$ is the $\mathbb{F}_p$-count `diagCountModP`. -/
theorem repCount_diag_one_eq (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (c : ℤ) :
    (repCount (QuadForm.diag a) p 1 c : ℤ) = diagCountModP (fun i => (a i : ZMod p)) (c : ZMod p) := by
  unfold repCount
  rw [pow_one, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  unfold diagCountModP
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdiag : (QuadForm.diag a).evalIn (ZMod p) x = ∑ i, (a i : ZMod p) * x i ^ 2 := by
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  rw [hdiag]
  push_cast
  rfl

/-- **Table 1 for all $n$** (Hanke 2004, Table 1, p. 363, extended; Kitaoka Lemmas 1.3.1–1.3.2): for a
diagonal form with $p$ odd, all $a_i$ units mod $p$, $n \ge 1$ and $u$ a unit mod $p$:
- $n$ even, $\chi = \left(\frac{(-1)^{n/2}D}{p}\right)$: $r_p(0) = p^{n-1} + \chi (p-1) p^{n/2-1}$ and
  $r_p(u) = p^{n-1} - \chi p^{n/2-1}$;
- $n$ odd: $r_p(0) = p^{n-1}$ and $r_p(u) = p^{n-1} + \left(\frac{(-1)^{(n-1)/2}Du}{p}\right) p^{(n-1)/2}$.
*Proof:* Gauss sums (Mathlib `gaussSum`, `quadraticChar`), or induction on $n$ by splitting off two
variables (the binary counts of Table 1) and the recursion $r_n(c) = \sum_{t} r_{n-2}(c - t)\, r_2(t)$. -/
@[kb "hanke2004" "Table 1, p. 363 (all n)"]
theorem card_diag_mod_p (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 1 ≤ n) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    (Even n →
      (repCount (QuadForm.diag a) p 1 0 : ℤ) =
          p ^ (n - 1) + legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) * (p - 1) * p ^ (n / 2 - 1) ∧
      (repCount (QuadForm.diag a) p 1 u : ℤ) =
          p ^ (n - 1) - legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) * p ^ (n / 2 - 1)) ∧
    (Odd n →
      repCount (QuadForm.diag a) p 1 0 = p ^ (n - 1) ∧
      (repCount (QuadForm.diag a) p 1 u : ℤ) =
          p ^ (n - 1) + legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * u) * p ^ ((n - 1) / 2)) := by
  have hne : ∀ t : ℤ, ¬ (p : ℤ) ∣ t → (t : ZMod p) ≠ 0 := fun t ht h =>
    ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
  have ha' : ∀ i, ((fun i => (a i : ZMod p)) i) ≠ 0 := fun i => hne _ (ha i)
  have hu' := hne u hu
  have hleg : ∀ t : ℤ, legendreSym p t = quadraticChar (ZMod p) (t : ZMod p) := fun _ => rfl
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by obtain ⟨j, hj⟩ := he; omega⟩
    have e1 : (2 * k + 2) / 2 = k + 1 := by omega
    have e2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [e1, e2, Nat.add_sub_cancel, repCount_diag_one_eq, repCount_diag_one_eq,
      diagCountModP_even hp k _ rfl _ ha', diagCountModP_even hp k _ rfl _ ha', hleg]
    push_cast
    simp only [↓reduceIte, hu']
    constructor <;> ring
  · obtain ⟨k, rfl⟩ := ho
    have e1 : (2 * k + 1 - 1) / 2 = k := by omega
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [e1, e2]
    have h0 := diagCountModP_odd hp k _ rfl _ ha' ((0 : ℤ) : ZMod p)
    have h1 := diagCountModP_odd hp k _ rfl _ ha' (u : ZMod p)
    rw [← repCount_diag_one_eq] at h0 h1
    refine ⟨?_, ?_⟩
    · push_cast at h0
      simp only [MulChar.map_zero, mul_zero, add_zero] at h0
      exact_mod_cast h0
    · rw [h1, hleg]
      push_cast
      rw [map_mul (quadraticChar (ZMod p)) ((-1) ^ k * ∏ i, (a i : ZMod p)) (u : ZMod p)]
      ring

/-- For a diagonal form unimodular at $p$, Good type = not Zero type (all coordinates are unimodular). -/
theorem isGoodType_diag_unimodular (a : Fin n → ℤ) (p : ℕ) (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (k : ℕ) :
    IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i) p k = fun x => ¬ IsZeroType p k x := by
  funext x
  apply propext
  simp only [IsGoodType, IsZeroType, Finset.mem_filter, Finset.mem_univ, true_and, ha,
    not_false_eq_true, not_forall]
  tauto

/-- **Lemma 3.2 for unimodular diagonal forms at odd $p$**: $r^{\mathrm{Good}\cup\mathrm{Bad}}_{p^{1+l}}(m) =
p^{(n-1)l}\, r^{\mathrm{Good}\cup\mathrm{Bad}}_{p}(m)$ (no Bad type, Remark 3.4.1(b)). -/
theorem repCountOf_nonZero_diag_succ (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) (l : ℕ) :
    repCountOf (QuadForm.diag a) p (1 + l) m (fun x => ¬ IsZeroType p (1 + l) x) =
      p ^ ((n - 1) * l) * repCountOf (QuadForm.diag a) p 1 m (fun x => ¬ IsZeroType p 1 x) := by
  have h := repCountGood_add_diag a p m 1 l (by simp [hp])
  rwa [isGoodType_diag_unimodular a p ha, isGoodType_diag_unimodular a p ha] at h

/-- Mod $p$, the only Zero-type vector is $\vec 0$: $r_p(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_p(m) + [p \mid m]$. -/
theorem repCount_one_eq_nonZero_add (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    repCount Q p 1 m = repCountOf Q p 1 m (fun x => ¬ IsZeroType p 1 x) +
      if (m : ZMod (p ^ 1)) = 0 then 1 else 0 := by
  rw [repCount_eq_zero_add_nonZero, add_comm]
  congr 1
  have hp0 : (p : ZMod (p ^ 1)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff p (p ^ 1)).2 (by simp)
  have hz : ∀ x : Fin n → ZMod (p ^ 1), IsZeroType p 1 x ↔ x = 0 := by
    intro x
    simp only [IsZeroType, hp0, zero_dvd_iff, funext_iff, Pi.zero_apply]
  have h0 : Q.evalIn (ZMod (p ^ 1)) 0 = 0 := by simp [QuadForm.evalIn]
  unfold repCountOf
  split_ifs with h
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun u v => Subtype.ext (((hz _).1 u.2.2).trans ((hz _).1 v.2.2).symm)⟩,
      ⟨⟨0, by rw [h0, h], (hz 0).2 rfl⟩⟩⟩
  · rw [Nat.card_eq_zero]; left
    exact ⟨fun u => h (by rw [← u.2.1, (hz _).1 u.2.2, h0])⟩

theorem limUnder_eq_of_eventually {f : ℕ → ℝ} {c : ℝ} (h : ∀ᶠ k in Filter.atTop, f k = c) :
    Filter.limUnder Filter.atTop f = c :=
  (tendsto_const_nhds.congr' (h.mono fun _ hk => hk.symm)).limUnder_eq

/-- Normalized non-Zero-type counts of a unimodular diagonal form are constant from $k = 1$. -/
theorem normalized_nonZero_diag (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (repCountOf (QuadForm.diag a) p k m (fun x => ¬ IsZeroType p k x) : ℝ) / (p : ℝ) ^ (k * (n - 1)) =
      (repCountOf (QuadForm.diag a) p 1 m (fun x => ¬ IsZeroType p 1 x) : ℝ) / (p : ℝ) ^ (n - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [repCountOf_nonZero_diag_succ a p hp ha m l, show (1 + l) * (n - 1) = (n - 1) + (n - 1) * l by ring,
    pow_add]
  push_cast
  field_simp

/-- $\beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_p(m)/p^{n-1}$ for a unimodular
diagonal form at odd $p$. -/
theorem localDensityOf_nonZero_diag (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) :
    localDensityOf (QuadForm.diag a) p m (fun k x => ¬ IsZeroType p k x) =
      (repCountOf (QuadForm.diag a) p 1 m (fun x => ¬ IsZeroType p 1 x) : ℝ) / (p : ℝ) ^ (n - 1) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  exact normalized_nonZero_diag a p hp ha m k hk

/-- If $p^2 \nmid m$ there are no Zero-type solutions for $k \ge 2$, so for a unimodular diagonal form at
odd $p$, $\beta_p(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_p(m)/p^{n-1}$. -/
theorem localDensity_diag_of_not_sq_dvd (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) (hm : ¬ (p : ℤ) ^ 2 ∣ m) :
    localDensity (QuadForm.diag a) p m =
      (repCountOf (QuadForm.diag a) p 1 m (fun x => ¬ IsZeroType p 1 x) : ℝ) / (p : ℝ) ^ (n - 1) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  rw [repCount_eq_zero_add_nonZero, repCountZero_eq _ p m k hk]
  simp only [hm, ↓reduceIte, zero_add]
  exact normalized_nonZero_diag a p hp ha m k (by omega)

/-- Counts of a given type depend on $m$ only mod $p^k$. -/
theorem repCountOf_congr (Q : QuadForm ℤ n) (p k : ℕ) {m m' : ℤ}
    (h : (m : ZMod (p ^ k)) = (m' : ZMod (p ^ k))) (T : (Fin n → ZMod (p ^ k)) → Prop) :
    repCountOf Q p k m T = repCountOf Q p k m' T := by
  unfold repCountOf; rw [h]

theorem intCast_zmod_pow_one_eq_zero {p : ℕ} {m : ℤ} : (m : ZMod (p ^ 1)) = 0 ↔ (p : ℤ) ∣ m := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simp

/-- $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T) = (r_p(0) - 1)/p^{n-1}$ for a unimodular diagonal form at
odd $p$ (the non-zero solutions of $Q \equiv 0 \pmod p$, all Good type). -/
theorem localDensityOf_nonZero_diag_sq (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (T : ℤ) :
    localDensityOf (QuadForm.diag a) p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
      ((repCount (QuadForm.diag a) p 1 0 : ℝ) - 1) / (p : ℝ) ^ (n - 1) := by
  have hc : (((p : ℤ) ^ 2 * T : ℤ) : ZMod (p ^ 1)) = ((0 : ℤ) : ZMod (p ^ 1)) := by
    rw [Int.cast_zero, intCast_zmod_pow_one_eq_zero]
    exact Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
  rw [localDensityOf_nonZero_diag a p hp ha, repCountOf_congr _ p 1 hc,
    repCount_one_eq_nonZero_add _ p 0]
  simp

/-- $\beta_p(T)$ for $\mathrm{ord}_p(T) = 1$: equal to $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2T)$ (Remark 5.4.1(b)). -/
theorem localDensity_diag_ord_one (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (T : ℤ) (hT : padicValInt p T = 1) :
    localDensity (QuadForm.diag a) p T =
      ((repCount (QuadForm.diag a) p 1 0 : ℝ) - 1) / (p : ℝ) ^ (n - 1) := by
  have hT0 : T ≠ 0 := by rintro rfl; simp at hT
  have h2 : ¬ (p : ℤ) ^ 2 ∣ T := by
    rw [padicValInt_dvd_iff]; omega
  have h1 : (p : ℤ) ∣ T := by
    have := (padicValInt_dvd_iff (p := p) 1 T).2 (Or.inr hT.ge); simpa using this
  rw [localDensity_diag_of_not_sq_dvd a p hp ha T h2,
    repCountOf_congr _ p 1 (m' := 0) (by rw [Int.cast_zero, intCast_zmod_pow_one_eq_zero]; exact h1),
    repCount_one_eq_nonZero_add _ p 0]
  simp

/-- **Local densities at good primes, $p \nmid m$** (Hanke 2004, §3: at $p \nmid N$ and $p \nmid m$ every solution
is of Good type, Remark 3.4.1(a); Lemma 3.2 then gives stabilization from $k = 1$): for a unimodular
diagonal form at odd $p$ and $p \nmid m$, $\beta_p(m) = r_p(m)/p^{n-1}$. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; Lemma 3.2"]
theorem localDensity_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    localDensity (QuadForm.diag a) p m = (repCount (QuadForm.diag a) p 1 m : ℝ) / (p : ℝ) ^ (n - 1) := by
  rw [localDensity_diag_of_not_sq_dvd a p hp ha m
      (fun h => hm (dvd_trans (dvd_pow_self _ two_ne_zero) h)),
    repCount_one_eq_nonZero_add _ p m]
  simp [intCast_zmod_pow_one_eq_zero, hm]

/-- Algebra for Table 2, $n = 2j + 3$ odd, with $q = p^j$, $P = p$ and $c = \Phi_n(p) = \pm 1$. -/
theorem table2_odd_alg (P q c : ℝ) (hP : 3 ≤ P) (hq : 1 ≤ q) (hc : c ^ 2 = 1) :
    q^2*P / (q^2*P - 1) * ((q^2*P^2 - 1) / (q^2*P^2) / ((q^2*P^2 + c*(q*P)) / (q^2*P^2))) =
      (q^2*P - q * c) / (q^2*P - 1) := by
  have hqP : 3 ≤ q * P := by nlinarith
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith
  have h1 : q^2*P - 1 ≠ 0 := by nlinarith
  have h2 : q^2*P^2 ≠ 0 := by positivity
  have h3 : q^2*P^2 + c*(q*P) ≠ 0 := by nlinarith
  rw [div_div_div_cancel_right₀ h2, div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h3) h1]
  linear_combination ((-(q^3*P^2) + q^3*P) * (q^2*P - 1) -
    (q^2*P - q^3*P + q^3*P^2 - q^4*P^2 + q^5*P^2 - q^5*P^3)) * hc

/-- Algebra for Table 2, $n = 2j + 4$ even, with $Y = p^{j+1}$, $P = p$ and $c = \Phi_n(p) = \pm 1$. -/
theorem table2_even_alg (P Y c : ℝ) (hP : 3 ≤ P) (hY : 3 ≤ Y) (hc : c ^ 2 = 1) :
    Y^2 / (Y^2 - 1) * ((Y^2*P + c*(P-1)*Y - 1) / (Y^2*P) / ((Y^2*P - c*Y) / (Y^2*P))) =
      Y / (Y - c) := by
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith
  have h1 : Y^2 - 1 ≠ 0 := by nlinarith
  have h2 : Y^2*P ≠ 0 := by positivity
  have h3 : Y^2*P - c*Y ≠ 0 := by nlinarith
  have h4 : Y - c ≠ 0 := by nlinarith
  rw [div_div_div_cancel_right₀ h2, div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h3) h4]
  linear_combination (-(Y^3*(P-1))) * hc

/-- $\prod a_i$ is a unit mod $p$. -/
theorem prod_ne_zero_zmod (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (ha : ∀ i, ¬ (p : ℤ) ∣ a i) :
    ((∏ i, a i : ℤ) : ZMod p) ≠ 0 := by
  push_cast
  exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha i

theorem neg_one_pow_ne_zero_zmod (p : ℕ) [Fact p.Prime] (s : ℕ) : (((-1) ^ s : ℤ) : ZMod p) ≠ 0 := by
  push_cast; exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/-- **Table 2, $n$ odd, $p \nmid T'$** (Hanke 2004, Table 2, p. 370):
$C_p(T') = \dfrac{q^{n-2} - q^{(n-3)/2}\Phi_n(p)}{q^{n-2} - 1}$, $\Phi_n(p) = \left(\frac{(-1)^{(n-1)/2} D T'}{p}\right)$.
*Proof:* (5.9) with the Good-type densities from `card_diag_mod_p` and Lemma 3.2. -/
@[kb "hanke2004" "Table 2, p. 370"]
theorem table2_odd_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (hodd : Odd n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    localConstC (QuadForm.diag a) p T =
      ((p : ℝ) ^ (n - 2) - (p : ℝ) ^ ((n - 3) / 2) *
          legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T)) / ((p : ℝ) ^ (n - 2) - 1) := by
  obtain ⟨r0, rT⟩ := (card_diag_mod_p a p hp ha (by omega) T hT).2 hodd
  have hc : ((legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) : ℤ) : ℝ) ^ 2 = 1 := by
    have : (((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact_mod_cast neg_one_pow_ne_zero_zmod p _
      · exact_mod_cast prod_ne_zero_zmod a p ha
      · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hT
    exact_mod_cast legendreSym.sq_one p this
  generalize legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * T) = c at rT hc ⊢
  have r0' : (repCount (QuadForm.diag a) p 1 0 : ℝ) = (p : ℝ) ^ (n - 1) := by exact_mod_cast r0
  have rT' : (repCount (QuadForm.diag a) p 1 T : ℝ) = (p : ℝ) ^ (n - 1) + c * (p : ℝ) ^ ((n - 1) / 2) := by
    exact_mod_cast rT
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a p hp ha, localDensity_unit a p hp ha T hT, r0', rT']
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 3 := by obtain ⟨m, rfl⟩ := hodd; exact ⟨m - 1, by omega⟩
  have hP : (3 : ℝ) ≤ p := by
    have := (Fact.out : p.Prime).two_le; exact_mod_cast (show 3 ≤ p by omega)
  have e1 : 2 * j + 3 - 2 = 2 * j + 1 := by omega
  have e2 : 2 * j + 3 - 1 = 2 * j + 2 := by omega
  have e3 : (2 * j + 3 - 3) / 2 = j := by omega
  have e4 : (2 * j + 3 - 1) / 2 = j + 1 := by omega
  rw [e3, e4, e1, e2]
  have := table2_odd_alg (p : ℝ) ((p : ℝ) ^ j) c hP (one_le_pow₀ (by linarith)) hc
  rw [show (p : ℝ) ^ (2 * j + 1) = ((p : ℝ) ^ j) ^ 2 * p by ring,
    show (p : ℝ) ^ (2 * j + 2) = ((p : ℝ) ^ j) ^ 2 * p ^ 2 by ring,
    show (p : ℝ) ^ (j + 1) = (p : ℝ) ^ j * p by ring]
  rw [← this]

/-- **Table 2, $n$ even, $p \nmid T'$** (Hanke 2004, Table 2, p. 370):
$C_p(T') = \dfrac{q^{(n-2)/2}}{q^{(n-2)/2} - \Phi_n(p)}$, $\Phi_n(p) = \left(\frac{(-1)^{n/2} D}{p}\right)$. -/
@[kb "hanke2004" "Table 2, p. 370"]
theorem table2_even_unit (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (heven : Even n) (T : ℤ) (hT : ¬ (p : ℤ) ∣ T) :
    localConstC (QuadForm.diag a) p T =
      (p : ℝ) ^ ((n - 2) / 2) /
        ((p : ℝ) ^ ((n - 2) / 2) - legendreSym p ((-1) ^ (n / 2) * ∏ i, a i)) := by
  obtain ⟨r0, rT⟩ := (card_diag_mod_p a p hp ha (by omega) T hT).1 heven
  have hc : ((legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) : ℤ) : ℝ) ^ 2 = 1 := by
    have : (((-1) ^ (n / 2) * ∏ i, a i : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast neg_one_pow_ne_zero_zmod p _
      · exact_mod_cast prod_ne_zero_zmod a p ha
    exact_mod_cast legendreSym.sq_one p this
  generalize legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = c at r0 rT hc ⊢
  have r0' : (repCount (QuadForm.diag a) p 1 0 : ℝ) =
      (p : ℝ) ^ (n - 1) + c * ((p : ℝ) - 1) * (p : ℝ) ^ (n / 2 - 1) := by exact_mod_cast r0
  have rT' : (repCount (QuadForm.diag a) p 1 T : ℝ) = (p : ℝ) ^ (n - 1) - c * (p : ℝ) ^ (n / 2 - 1) := by
    exact_mod_cast rT
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a p hp ha, localDensity_unit a p hp ha T hT, r0', rT']
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := by obtain ⟨m, rfl⟩ := heven; exact ⟨m - 2, by omega⟩
  have hP : (3 : ℝ) ≤ p := by
    have := (Fact.out : p.Prime).two_le; exact_mod_cast (show 3 ≤ p by omega)
  have e1 : 2 * j + 4 - 2 = 2 * (j + 1) := by omega
  have e2 : 2 * j + 4 - 1 = 2 * (j + 1) + 1 := by omega
  have e3 : (2 * j + 4 - 2) / 2 = j + 1 := by omega
  have e4 : (2 * j + 4) / 2 - 1 = j + 1 := by omega
  rw [e3, e4, e1, e2]
  have hY : (3 : ℝ) ≤ (p : ℝ) ^ (j + 1) := le_trans hP (le_self_pow₀ (by linarith) (by omega))
  have := table2_even_alg (p : ℝ) ((p : ℝ) ^ (j + 1)) c hP hY hc
  rw [pow_mul, pow_succ (_ ^ 2), ← pow_mul, ← this]
  ring

/-- **Table 2, $\mathrm{ord}_p(T') = 1$** (Hanke 2004, Table 2, p. 370; (5.9)): $C_p(T') = \dfrac{q^{n-2}}{q^{n-2} - 1}$
for both parities (no Zero-type or Bad-type solutions, Remark 5.4.1(b)). -/
@[kb "hanke2004" "Table 2, p. 370; (5.9)"]
theorem table2_ord_one (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (hn : 3 ≤ n) (T : ℤ) (hT : padicValInt p T = 1) :
    localConstC (QuadForm.diag a) p T = (p : ℝ) ^ (n - 2) / ((p : ℝ) ^ (n - 2) - 1) := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have h2 : (2 : ℤ) ≤ repCount (QuadForm.diag a) p 1 0 := by
    have hcd := card_diag_mod_p a p hp ha (by omega) 1 (by
      exact_mod_cast (Fact.out : p.Prime).not_dvd_one)
    rcases Nat.even_or_odd n with he | ho
    · rw [(hcd.1 he).1]
      obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := by obtain ⟨m, rfl⟩ := he; exact ⟨m - 2, by omega⟩
      have e2 : 2 * j + 4 - 1 = 2 * (j + 1) + 1 := by omega
      have e4 : (2 * j + 4) / 2 - 1 = j + 1 := by omega
      rw [e2, e4]
      have hc := legendreSym.eq_one_or_neg_one p (a := (-1) ^ ((2 * j + 4) / 2) * ∏ i, a i) (by
        push_cast
        refine mul_ne_zero ?_ ?_
        · exact_mod_cast neg_one_pow_ne_zero_zmod p _
        · exact_mod_cast prod_ne_zero_zmod a p ha)
      have hP : (3 : ℤ) ≤ p := by exact_mod_cast hp3
      have hY : (3 : ℤ) ≤ (p : ℤ) ^ (j + 1) := le_trans hP (le_self_pow₀ (by linarith) (by omega))
      rw [show (p : ℤ) ^ (2 * (j + 1) + 1) = ((p : ℤ) ^ (j + 1)) ^ 2 * p by ring]
      have hnn : (0 : ℤ) ≤ (p : ℤ) * (p : ℤ) ^ (j + 1) * ((p : ℤ) ^ (j + 1) - 1) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      rcases hc with hc | hc <;> rw [hc] <;> nlinarith
    · rw [(hcd.2 ho).1]
      have : p ≤ p ^ (n - 1) := le_self_pow₀ (by omega) (by omega)
      push_cast; exact_mod_cast (show 2 ≤ p ^ (n - 1) by omega)
  have hne : ((repCount (QuadForm.diag a) p 1 0 : ℝ) - 1) / (p : ℝ) ^ (n - 1) ≠ 0 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have : (2 : ℝ) ≤ repCount (QuadForm.diag a) p 1 0 := by exact_mod_cast h2
    exact div_ne_zero (by linarith) (pow_ne_zero _ hp0.ne')
  unfold localConstC
  rw [localDensityOf_nonZero_diag_sq a p hp ha, localDensity_diag_ord_one a p hp ha T hT,
    div_self hne, mul_one]

/-- **(5.10), $n = 3$** (Hanke 2004, p. 371): for a unimodular ternary diagonal form at odd $p$,
$\psi = \Phi_3(p, T')$ and $\nu \ge 0$,
$C_p(T') + \dfrac{1 - C_p(T')}{p^\nu} = \dfrac{1}{p^\nu}\cdot\begin{cases} p^\nu & p \nmid T',\ \psi = 1,\\
p^\nu + 2\sum_{\mu=0}^{\nu-1} p^\mu & p \nmid T',\ \psi = -1,\\ \sum_{\mu=0}^{\nu} p^\mu & \mathrm{ord}_p(T') = 1.\end{cases}$
*Proof:* substitute Table 2 with $n = 3$. -/
@[kb "hanke2004" "(5.10), p. 371"]
theorem eq_5_10 (a : Fin 3 → ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ∀ i, ¬ (p : ℤ) ∣ a i)
    (T : ℤ) (ν : ℕ) :
    let C := localConstC (QuadForm.diag a) p T
    let ψ := legendreSym p (-(∏ i, a i) * T)
    (¬ (p : ℤ) ∣ T → ψ = 1 → C + (1 - C) / (p : ℝ) ^ ν = 1) ∧
    (¬ (p : ℤ) ∣ T → ψ = -1 →
      C + (1 - C) / (p : ℝ) ^ ν = ((p : ℝ) ^ ν + 2 * ∑ μ ∈ Finset.range ν, (p : ℝ) ^ μ) / (p : ℝ) ^ ν) ∧
    (padicValInt p T = 1 →
      C + (1 - C) / (p : ℝ) ^ ν = (∑ μ ∈ Finset.range (ν + 1), (p : ℝ) ^ μ) / (p : ℝ) ^ ν) := by
  intro C ψ
  have hP : (3 : ℝ) ≤ p := by
    have := (Fact.out : p.Prime).two_le; exact_mod_cast (show 3 ≤ p by omega)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpν : (p : ℝ) ^ ν ≠ 0 := pow_ne_zero _ (by linarith)
  have hodd : ∀ hT : ¬ (p : ℤ) ∣ T, C = ((p : ℝ) - ψ) / ((p : ℝ) - 1) := by
    intro hT
    have h := table2_odd_unit a p hp ha le_rfl (by decide) T hT
    simp only [show 3 - 2 = 1 by rfl, show (3 - 3) / 2 = 0 by rfl, show (3 - 1) / 2 = 1 by rfl,
      pow_one, pow_zero, one_mul, neg_one_mul] at h
    exact h
  refine ⟨fun hT hψ => ?_, fun hT hψ => ?_, fun hT => ?_⟩
  · rw [hodd hT, hψ]; push_cast; field_simp; ring
  · rw [hodd hT, hψ, geom_sum_eq (by linarith)]; push_cast; field_simp; ring
  · have h := table2_ord_one a p hp ha le_rfl T hT
    simp only [show 3 - 2 = 1 by rfl, pow_one] at h
    change C = _ at h
    rw [h, geom_sum_eq (by linarith)]; field_simp; ring

end QuadFormsKB.LocalDensity
