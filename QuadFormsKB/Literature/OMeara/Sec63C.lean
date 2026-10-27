/-
# O'Meara §63B–§63C: the Hasse symbol of a local space, and spaces with prescribed invariants

**Setting.** $F$ is a number field, $\mathfrak p$ (`v`) a finite place, and $K = F_\mathfrak p$
(`v.adicCompletion F`) is O'Meara's local field (§63, p. 158; every local field of characteristic $0$ is such a
completion). A regular quadratic space over $K$ is given by an orthogonal splitting
$V \cong \langle a_0\rangle \perp \cdots \perp \langle a_{n-1}\rangle$ with $a_i \in \dot K$, i.e. by the diagonal form
`QuadForm.diag a` (indices are $0$-based; O'Meara's $\alpha_1, \dots, \alpha_n$ are `a 0, …, a (n-1)`); its discriminant is
$\prod_i a_i$ modulo squares, and isometry is `QuadForm.IsometricIn K`. The Hilbert symbol is `hilbertSymbol K`.

**Defines** O'Meara's Hasse symbol of a diagonal form with coefficients in a field $K$ (§63B, p. 167, in the form of
Remark 58:3),
$$S(\langle a_0, \dots, a_{n-1}\rangle) = \prod_{0 \le i \le j < n} (a_i, a_j)_K$$
(`hasseS K a`). For coefficients from the number field it is the library's `NFPlace.hasseOMeara`
(`hasseOMeara_finite_eq_hasseS`), and it is Serre's $\varepsilon$ (`PadicClass.hasseVec`) times $(-1, dV)$
(`hasseS_eq_hasseVec_mul`). Its independence of the splitting is `hasseS_eq_of_isometric`.

**Proves** over $K = F_\mathfrak p$
* `hasseS_eq_prod_partial` (§63B, p. 167, O'Meara's definition): $S_\mathfrak pV = \prod_i (a_i, d_i)_\mathfrak p$,
  $d_i = a_0 \cdots a_i$;
* `hasseS_append` (p. 167): $S_\mathfrak p(U \perp W) = S_\mathfrak pU \cdot (dU, dW)_\mathfrak p \cdot S_\mathfrak pW$;
* `hasseS_smul` (p. 167): $S_\mathfrak p(V^{\alpha}) = (\alpha, (-1)^{n(n+1)/2}(dV)^{n+1})_\mathfrak p\,S_\mathfrak pV$;
* Theorem 63:22 (p. 171): `exists_hasseS_neg_iff`;
* Theorem 63:23 (p. 171): `exists_invariants_iff`;
* Example 63:24 (p. 172): `represents_units_of_ternary`.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Tamagawa.SquareClassDuality

open NumberField IsDedekindDomain QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open QuadForm

/-! ### The Hasse symbol over a field -/

section General

variable (K : Type*) [Field K] {n : ℕ}

/-- **O'Meara's Hasse symbol** of the diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ over the field $K$
(O'Meara 1963, §63B, p. 167; the formula $S_\mathfrak pV = \prod_{1 \le i \le j \le n}(\alpha_i, \alpha_j)_\mathfrak p$
of Remark 58:3, here with $0$-based indices): $\prod_{0 \le i \le j < n} (a_i, a_j)_K$. O'Meara's defining formula
$\prod_i (a_i, a_0\cdots a_i)$ is `hasseS_eq_prod_partial`. -/
@[kb "omeara1963" "§63B, p. 167 (the Hasse symbol S_pV = ∏_{i ≤ j} (α_i, α_j)_p)"]
def hasseS (a : Fin n → K) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then hilbertSymbol K (a i) (a j) else 1

end General


/-! ### Algebra of Hilbert symbols over an abstract local Hilbert field -/

section Aux

open PadicClass

variable {L : Type*} [Field L] [CharZero L] {m k n : ℕ}

theorem hasseS_eq_vec (a : Fin n → L) :
    hasseS L a = hasseVec a * ∏ i, hilbertSymbol L (a i) (a i) := by
  unfold hasseS hasseVec
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ∀ j, (if i ≤ j then hilbertSymbol L (a i) (a j) else 1) =
      (if i < j then hilbertSymbol L (a i) (a j) else 1) *
        (if i = j then hilbertSymbol L (a i) (a j) else 1) := by
    intro j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.le, h.ne]
    · subst h; simp
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq]
  simp

variable (hK : LocalHilbertField L)
include hK

theorem hs_pow_right' {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    hilbertSymbol L a (b ^ k) = hilbertSymbol L a b ^ k := by
  induction k with
  | zero => simp [hilbertSymbol_one_right]
  | succ k ih => rw [pow_succ, hK.mul_right ha (pow_ne_zero _ hb) hb, ih, pow_succ]

theorem hs_prod_left' {x : L} (hx : x ≠ 0) {v : Fin n → L} (hv : ∀ i, v i ≠ 0) :
    ∏ j, hilbertSymbol L (v j) x = hilbertSymbol L (∏ j, v j) x := by
  simp_rw [hilbertSymbol_comm L _ x]
  exact hs_prod_right hK hx hv

theorem hasseS_eq_vec_mul (a : Fin n → L) (ha : ∀ i, a i ≠ 0) :
    hasseS L a = hasseVec a * hilbertSymbol L (-1) (∏ i, a i) := by
  rw [hasseS_eq_vec]
  congr 1
  have : ∀ i, hilbertSymbol L (a i) (a i) = hilbertSymbol L (-1) (a i) := fun i => by
    rw [hK.self (ha i), hilbertSymbol_comm]
  simp_rw [this]
  exact hs_prod_right hK (by norm_num) ha

theorem hasseS_eq_of_isometric_gen {a b : Fin n → L} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (diag a).IsometricIn L (diag b)) : hasseS L a = hasseS L b := by
  rw [hasseS_eq_vec_mul hK a ha, hasseS_eq_vec_mul hK b hb, hasseVec_eq_of_isometric hK n a b ha hb h]
  obtain ⟨t, ht, hd⟩ := disc_of_isometric h
  rw [hd, hs_sq_right _ _ _ ht]

theorem hasseS_eq_prod_partial_gen (a : Fin n → L) (ha : ∀ i, a i ≠ 0) :
    hasseS L a = ∏ i : Fin n, hilbertSymbol L (a i) (∏ j : Fin n, if j ≤ i then a j else 1) := by
  have h1 : ∀ i : Fin n, hilbertSymbol L (a i) (∏ j : Fin n, if j ≤ i then a j else 1) =
      ∏ j : Fin n, if j ≤ i then hilbertSymbol L (a i) (a j) else 1 := by
    intro i
    rw [← hs_prod_right hK (ha i) (fun j => by by_cases h : j ≤ i <;> simp [h, ha j])]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases h : j ≤ i <;> simp [h, hilbertSymbol_one_right]
  simp_rw [h1]
  unfold hasseS
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  by_cases h : j ≤ i <;> simp [h, hilbertSymbol_comm L (a j) (a i)]

theorem hasseS_append_gen (a : Fin m → L) (b : Fin n → L) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    hasseS L (Fin.append a b) = hasseS L a * hilbertSymbol L (∏ i, a i) (∏ i, b i) * hasseS L b := by
  unfold hasseS
  rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add (f := fun j => if _ ≤ j then _ else _)]
  simp only [Fin.append_left, Fin.append_right, Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]
  have e1 : ∀ i : Fin m, ∀ j : Fin n, (i : ℕ) ≤ m + j := fun i j => by omega
  have e2 : ∀ i : Fin n, ∀ j : Fin m, ¬ (m + (i : ℕ) ≤ j) := fun i j => by omega
  simp only [e1, e2, ite_true, ite_false, Finset.prod_const_one, Finset.prod_mul_distrib, one_mul, Nat.add_le_add_iff_left]
  have : ∏ i : Fin m, ∏ j : Fin n, hilbertSymbol L (a i) (b j) = hilbertSymbol L (∏ i, a i) (∏ i, b i) := by
    rw [← hs_prod_left' hK (Finset.prod_ne_zero_iff.mpr fun i _ => hb i) ha]
    refine Finset.prod_congr rfl fun i _ => hs_prod_right hK (ha i) hb
  rw [this]

theorem hasseS_cons_gen (x : L) (hx : x ≠ 0) (v : Fin n → L) (hv : ∀ i, v i ≠ 0) :
    hasseS L (Fin.cons x v : Fin (n + 1) → L) =
      hilbertSymbol L x x * hilbertSymbol L x (∏ i, v i) * hasseS L v := by
  have hc : ∀ i, (Fin.cons x v : Fin (n + 1) → L) i ≠ 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hx, hv]
  have hpv : ∏ j, v j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
  rw [hasseS_eq_vec_mul hK _ hc, hasseS_eq_vec_mul hK _ hv, hasseVec_cons hK hx hv, Fin.prod_cons,
    hK.mul_right (by norm_num) hx hpv, hK.self hx, hilbertSymbol_comm L x (-1)]
  ring

theorem hasseS_smul_gen (α : L) (hα : α ≠ 0) : ∀ (n : ℕ) (a : Fin n → L), (∀ i, a i ≠ 0) →
    hasseS L (fun i => α * a i) =
      hilbertSymbol L α ((-1) ^ (n * (n + 1) / 2) * (∏ i, a i) ^ (n + 1)) * hasseS L a
  | 0, a, _ => by simp [hasseS, hilbertSymbol_one_right]
  | n + 1, a, ha => by
    obtain ⟨x, v, rfl⟩ : ∃ (x : L) (v : Fin n → L), a = Fin.cons x v :=
      ⟨a 0, Fin.tail a, (Fin.cons_self_tail a).symm⟩
    have hx : x ≠ 0 := by simpa using ha 0
    have hv : ∀ i, v i ≠ 0 := fun i => by simpa using ha i.succ
    have hαv : ∀ i, α * v i ≠ 0 := fun i => mul_ne_zero hα (hv i)
    have hD : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    have hfun : (fun i => α * (Fin.cons x v : Fin (n + 1) → L) i) =
        (Fin.cons (α * x) (fun i => α * v i) : Fin (n + 1) → L) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have IH := hasseS_smul_gen α hα n v hv
    rw [hfun, hasseS_cons_gen hK _ (mul_ne_zero hα hx) _ hαv, hasseS_cons_gen hK x hx v hv, IH]
    have hm1 : (-1 : L) ≠ 0 := by norm_num
    have hpα : ∏ i, α * v i = α ^ n * ∏ i, v i := by
      simp [Finset.prod_mul_distrib, Finset.prod_const]
    have hT : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
    rw [Fin.prod_cons, hpα, hT]
    set T := n * (n + 1) / 2
    have hαn : α ^ n ≠ 0 := pow_ne_zero _ hα
    have h1 : hilbertSymbol L (α * x) (α * x) = hilbertSymbol L α (-1) * hilbertSymbol L x (-1) := by
      rw [hK.self (mul_ne_zero hα hx), hK.mul_left _ _ _ hα hx hm1]
    have h2 : hilbertSymbol L (α * x) (α ^ n * ∏ i, v i) =
        (hilbertSymbol L α (-1) ^ n * hilbertSymbol L α (∏ i, v i)) *
          (hilbertSymbol L α x ^ n * hilbertSymbol L x (∏ i, v i)) := by
      rw [hK.mul_left _ _ _ hα hx (mul_ne_zero hαn hD), hK.mul_right hα hαn hD,
        hK.mul_right hx hαn hD, hs_pow_right' hK hα hα, hs_pow_right' hK hx hα, hK.self hα,
        hilbertSymbol_comm L x α]
    have h3 : hilbertSymbol L α ((-1) ^ T * (∏ i, v i) ^ (n + 1)) =
        hilbertSymbol L α (-1) ^ T * hilbertSymbol L α (∏ i, v i) ^ (n + 1) := by
      rw [hK.mul_right hα (pow_ne_zero _ hm1) (pow_ne_zero _ hD), hs_pow_right' hK hα hm1,
        hs_pow_right' hK hα hD]
    have h4 : hilbertSymbol L α ((-1) ^ (T + (n + 1)) * (x * ∏ i, v i) ^ (n + 1 + 1)) =
        hilbertSymbol L α (-1) ^ (T + (n + 1)) *
          ((hilbertSymbol L α x * hilbertSymbol L α (∏ i, v i)) ^ (n + 1 + 1)) := by
      rw [hK.mul_right hα (pow_ne_zero _ hm1) (pow_ne_zero _ (mul_ne_zero hx hD)),
        hs_pow_right' hK hα hm1, hs_pow_right' hK hα (mul_ne_zero hx hD),
        hK.mul_right hα hx hD]
    rw [h1, h2, h3, h4, hK.self hx]
    have hA2 := hs_pm (K := L) α x
    have hsq : hilbertSymbol L α x ^ 2 = 1 := by rcases hA2 with h | h <;> rw [h] <;> norm_num
    generalize hilbertSymbol L α x = A2 at *
    generalize hilbertSymbol L α (-1) = A1 at *
    generalize hilbertSymbol L α (∏ i, v i) = A3 at *
    generalize hilbertSymbol L x (-1) = B1 at *
    generalize hilbertSymbol L x (∏ i, v i) = C at *
    generalize hasseS L v = S at *
    linear_combination (-(A1 ^ (T + (n + 1)) * B1 * A3 ^ (n + 1 + 1) * A2 ^ n * C * S)) * hsq

theorem hasseS_exc {a : Fin n → L} (ha : ∀ i, a i ≠ 0) {d₀ t : L} (ht : t ≠ 0)
    (hdt : ∏ i, a i = t ^ 2 * d₀) (h : n = 1 ∨ (n = 2 ∧ IsSquare (-d₀))) :
    hasseS L a = hilbertSymbol L (-1) d₀ := by
  rw [hasseS_eq_vec_mul hK a ha, hdt, hs_sq_right _ _ _ ht]
  rcases h with rfl | ⟨rfl, ⟨s, hs⟩⟩
  · have : hasseVec a = 1 := by simp [hasseVec]
    rw [this, one_mul]
  · have e := hasseVec_two (a 0) (a 1)
    rw [← eq_vec_two a] at e
    rw [e, hs_eq_one_of_isSquare_neg_mul hK (ha 0) (ha 1), one_mul]
    refine ⟨t * s, ?_⟩
    simp only [Fin.prod_univ_two] at hdt
    linear_combination (-1 : L) * hdt + t ^ 2 * hs

theorem exists_tri (hns : ∃ x : L, ¬ IsSquare x) {d : L} (hd : d ≠ 0) {e : ℤ}
    (he : e = 1 ∨ e = -1) :
    ∃ x y : L, x ≠ 0 ∧ y ≠ 0 ∧
      hilbertSymbol L x y * hilbertSymbol L x d * hilbertSymbol L y d = e := by
  by_cases hsq : IsSquare d
  · rcases he with rfl | rfl
    · exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp [hs_one_left, hilbertSymbol_one_right]⟩
    · obtain ⟨x0, hx0⟩ := hns
      have hx00 : x0 ≠ 0 := by rintro rfl; exact hx0 ⟨0, by simp⟩
      obtain ⟨y, hy0, hy⟩ := hK.exists_neg_one x0 hx00 hx0
      refine ⟨x0, y, hx00, hy0, ?_⟩
      rw [hs_of_isSquare _ d hd hsq, hs_of_isSquare _ d hd hsq, hy]; norm_num
  · rcases he with rfl | rfl
    · exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp [hs_one_left, hilbertSymbol_one_right]⟩
    · obtain ⟨y, hy0, hy⟩ := hK.exists_neg_one d hd hsq
      refine ⟨1, y, one_ne_zero, hy0, ?_⟩
      simp only [hs_one_left]
      rw [hilbertSymbol_comm L y d, hy]; norm_num

theorem hasseVec_cons3 {p q r : L} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) {v : Fin m → L}
    (hv : ∀ i, v i ≠ 0) :
    hasseVec (Fin.cons p (Fin.cons q (Fin.cons r v)) : Fin (m + 3) → L) =
      hilbertSymbol L p q * hilbertSymbol L p r * hilbertSymbol L q r *
        hilbertSymbol L (p * q * r) (∏ i, v i) * hasseVec v := by
  have hD : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
  have h1 := PadicClass.cons_ne_zero hr hv
  have h2 := PadicClass.cons_ne_zero hq h1
  rw [hasseVec_cons hK hp h2, hasseVec_cons hK hq h1, hasseVec_cons hK hr hv]
  simp only [Fin.prod_cons]
  rw [hK.mul_right hp hq (mul_ne_zero hr hD), hK.mul_right hp hr hD, hK.mul_right hq hr hD,
    hK.mul_left _ _ _ (mul_ne_zero hp hq) hr hD, hK.mul_left _ _ _ hp hq hD]
  ring

theorem eps_tri {x y d : L} (hx : x ≠ 0) (hy : y ≠ 0) (hd : d ≠ 0) :
    hilbertSymbol L x y * hilbertSymbol L x (d * x * y) * hilbertSymbol L y (d * x * y) =
      hilbertSymbol L x y * hilbertSymbol L x (-d) * hilbertSymbol L y (-d) := by
  have hm1 : (-1 : L) ≠ 0 := by norm_num
  rw [hK.mul_right hx (mul_ne_zero hd hx) hy, hK.mul_right hx hd hx,
    hK.mul_right hy (mul_ne_zero hd hx) hy, hK.mul_right hy hd hx,
    show -d = -1 * d by ring, hK.mul_right hx hm1 hd, hK.mul_right hy hm1 hd,
    hK.self hx, hK.self hy, hilbertSymbol_comm L y x]
  have h := hs_pm (K := L) x y
  have hsq : hilbertSymbol L x y ^ 2 = 1 := by rcases h with h | h <;> rw [h] <;> norm_num
  generalize hilbertSymbol L x y = A at *
  generalize hilbertSymbol L x (-1) = B at *
  generalize hilbertSymbol L y (-1) = C at *
  generalize hilbertSymbol L x d = D at *
  generalize hilbertSymbol L y d = E at *
  linear_combination (B * D * C * E * A) * hsq

theorem exists_hasseS_neg_gen (hns : ∃ x : L, ¬ IsSquare x) (hn : 2 ≤ n) (a : Fin n → L)
    (ha : ∀ i, a i ≠ 0) (hexc : n = 2 → ¬ IsSquare (-∏ i, a i)) :
    ∃ b : Fin n → L, (∀ i, b i ≠ 0) ∧ (∃ t : L, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧
      hasseS L b = -hasseS L a := by
  have hm1 : (-1 : L) ≠ 0 := by norm_num
  obtain h2 | h3 : n = 2 ∨ 3 ≤ n := by omega
  · subst h2
    obtain ⟨a0, a1, rfl⟩ : ∃ a0 a1 : L, a = ![a0, a1] := ⟨a 0, a 1, eq_vec_two a⟩
    have h0 : a0 ≠ 0 := by simpa using ha 0
    have h1 : a1 ≠ 0 := by simpa using ha 1
    have hnsq := hexc rfl
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hnsq
    have hd : -(a0 * a1) ≠ 0 := by simp [h0, h1]
    obtain ⟨y, hy0, hy⟩ := hK.exists_neg_one _ hd hnsq
    have hx : a0 * y ≠ 0 := mul_ne_zero h0 hy0
    have hb : ∀ i, (![a0 * y, a0 * y * (a0 * a1)] : Fin 2 → L) i ≠ 0 := fun i => by
      fin_cases i <;> simp [h0, h1, hy0]
    refine ⟨![a0 * y, a0 * y * (a0 * a1)], hb, ⟨a0 * y, hx, ?_⟩, ?_⟩
    · simp [Fin.prod_univ_two]; ring
    · have ha' : ∀ i, (![a0, a1] : Fin 2 → L) i ≠ 0 := fun i => by fin_cases i <;> simpa
      rw [hasseS_eq_vec_mul hK _ hb, hasseS_eq_vec_mul hK _ ha', hasseVec_two, hasseVec_two]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hxn : -(a0 * y) ≠ 0 := neg_ne_zero.mpr hx
      have e1 : hilbertSymbol L (a0 * y) (a0 * y * (a0 * a1)) =
          hilbertSymbol L (a0 * y) (-(a0 * a1)) := by
        rw [show a0 * y * (a0 * a1) = (-(a0 * y)) * (-(a0 * a1)) by ring,
          hK.mul_right hx hxn hd, hilbertSymbol_self_neg, one_mul]
      have e2 : hilbertSymbol L a0 a1 = hilbertSymbol L a0 (-(a0 * a1)) := by
        rw [← hs_sq_right a0 a1 a0 h0, show a0 ^ 2 * a1 = (-a0) * (-(a0 * a1)) by ring,
          hK.mul_right h0 (neg_ne_zero.mpr h0) hd, hilbertSymbol_self_neg, one_mul]
      have e3 : hilbertSymbol L (a0 * y) (-(a0 * a1)) =
          hilbertSymbol L a0 (-(a0 * a1)) * hilbertSymbol L y (-(a0 * a1)) :=
        hK.mul_left _ _ _ h0 hy0 hd
      have e4 : hilbertSymbol L y (-(a0 * a1)) = -1 := by
        rw [hilbertSymbol_comm]; exact hy
      have e5 : hilbertSymbol L (-1) (a0 * y * (a0 * y * (a0 * a1))) =
          hilbertSymbol L (-1) (a0 * a1) := by
        rw [show a0 * y * (a0 * y * (a0 * a1)) = (a0 * y) ^ 2 * (a0 * a1) by ring,
          hs_sq_right _ _ _ hx]
      rw [e1, e2, e3, e4, e5]
      ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    obtain ⟨p, q, r, v, rfl⟩ : ∃ (p q r : L) (v : Fin m → L),
        a = Fin.cons p (Fin.cons q (Fin.cons r v)) :=
      ⟨a 0, a 1, a 2, fun i => a i.succ.succ.succ, by
        funext i
        refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i) i⟩
    have hp : p ≠ 0 := by simpa using ha 0
    have hq : q ≠ 0 := by simpa using ha (Fin.succ 0)
    have hr : r ≠ 0 := by simpa only [Fin.cons_succ, Fin.cons_zero] using ha (Fin.succ (Fin.succ 0))
    have hv : ∀ i, v i ≠ 0 := fun i => by simpa using ha i.succ.succ.succ
    have hD : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    have hd3 : -(p * q * r) ≠ 0 := by simp [hp, hq, hr]
    have hpm : ∀ u v w : ℤ, (u = 1 ∨ u = -1) → (v = 1 ∨ v = -1) → (w = 1 ∨ w = -1) →
        (-(u * v * w) = 1 ∨ -(u * v * w) = -1) := by
      rintro u v w (rfl | rfl) (rfl | rfl) (rfl | rfl) <;> simp
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_tri hK hns hd3
      (e := -(hilbertSymbol L p q * hilbertSymbol L p r * hilbertSymbol L q r))
      (hpm _ _ _ (hs_pm _ _) (hs_pm _ _) (hs_pm _ _))
    have hz : p * q * r * x * y ≠ 0 := by simp [hp, hq, hr, hx, hy]
    have hbn : ∀ i, (Fin.cons x (Fin.cons y (Fin.cons (p * q * r * x * y) v)) :
        Fin (m + 3) → L) i ≠ 0 :=
      PadicClass.cons_ne_zero hx (PadicClass.cons_ne_zero hy (PadicClass.cons_ne_zero hz hv))
    have han := ha
    have hprodb : ∏ i, (Fin.cons x (Fin.cons y (Fin.cons (p * q * r * x * y) v)) :
        Fin (m + 3) → L) i = (x * y) ^ 2 * ∏ i, (Fin.cons p (Fin.cons q (Fin.cons r v)) :
        Fin (m + 3) → L) i := by
      simp only [Fin.prod_cons]; ring
    refine ⟨_, hbn, ⟨x * y, mul_ne_zero hx hy, hprodb⟩, ?_⟩
    rw [hasseS_eq_vec_mul hK _ hbn, hasseS_eq_vec_mul hK _ ha, hasseVec_cons3 hK hx hy hz hv,
      hasseVec_cons3 hK hp hq hr hv, hprodb, hs_sq_right _ _ _ (mul_ne_zero hx hy),
      show x * y * (p * q * r * x * y) = (x * y) ^ 2 * (p * q * r) by ring,
      hs_sq_left _ _ _ (mul_ne_zero hx hy)]
    have ε : hilbertSymbol L x y * hilbertSymbol L x (p * q * r * x * y) *
        hilbertSymbol L y (p * q * r * x * y) =
        -(hilbertSymbol L p q * hilbertSymbol L p r * hilbertSymbol L q r) := by
      rw [eps_tri hK hx hy (mul_ne_zero (mul_ne_zero hp hq) hr)]; exact hxy
    rw [mul_assoc (hilbertSymbol L x y * hilbertSymbol L x _ * hilbertSymbol L y _), ε]
    ring

end Aux

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- The local field $F_\mathfrak p$ has a non-square (a uniformizer has odd valuation). -/
theorem exists_nonsquare_adic : ∃ x : v.adicCompletion F, ¬ IsSquare x := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨algebraMap F (v.adicCompletion F) π, ?_⟩
  rintro ⟨r, hr⟩
  have h := congrArg Valued.v hr
  have hv : Valued.v (algebraMap F (v.adicCompletion F) π) = v.valuation F π :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  rw [hv, hπ, map_mul] at h
  have hr0 : Valued.v r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact WithZero.exp_ne_zero h
  rw [← WithZero.exp_log hr0, ← WithZero.exp_add, WithZero.exp_inj] at h
  omega

local notation "K" => v.adicCompletion F

variable {n : ℕ}

/-- For coefficients from the number field, `hasseS` at the completion is the library's `NFPlace.hasseOMeara`. -/
theorem hasseOMeara_finite_eq_hasseS (a : Fin n → F) :
    (NFPlace.finite v).hasseOMeara a = hasseS K (fun i => algebraMap F K (a i)) := by
  simp only [NFPlace.hasseOMeara, hasseS, NFPlace.hilbert]

/-- $S = \varepsilon \cdot (-1, dV)$: O'Meara's Hasse symbol is Serre's Hasse invariant $\varepsilon =
\prod_{i<j}(a_i,a_j)$ (`PadicClass.hasseVec`) times $(-1, a_0 \cdots a_{n-1})$. -/
theorem hasseS_eq_hasseVec_mul (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    hasseS K a = PadicClass.hasseVec a * hilbertSymbol K (-1) (∏ i, a i) :=
  hasseS_eq_vec_mul (HasseIsoNF.localHilbertField_adicCompletion v) a ha

/-- **The Hasse symbol is independent of the orthogonal splitting** (O'Meara 1963, §63B, p. 167). -/
@[kb "omeara1963" "§63B, p. 167 (S_pV is independent of the splitting)"]
theorem hasseS_eq_of_isometric {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (diag a).IsometricIn K (diag b)) : hasseS K a = hasseS K b :=
  hasseS_eq_of_isometric_gen (HasseIsoNF.localHilbertField_adicCompletion v) ha hb h

/-- **O'Meara's definition of the Hasse symbol** (O'Meara 1963, §63B, p. 167):
$S_\mathfrak pV = \prod_i (a_i, d_i)_\mathfrak p$ with $d_i = a_0 \cdots a_i$ ($0$-based; O'Meara's
$d_i = \alpha_1 \cdots \alpha_i$). -/
@[kb "omeara1963" "§63B, p. 167 (S_pV = ∏ (α_i, d_i)_p, d_i = α_1 ⋯ α_i)"]
theorem hasseS_eq_prod_partial (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    hasseS K a = ∏ i : Fin n, hilbertSymbol K (a i) (∏ j : Fin n, if j ≤ i then a j else 1) :=
  hasseS_eq_prod_partial_gen (HasseIsoNF.localHilbertField_adicCompletion v) a ha

/-- **The Hasse symbol of an orthogonal sum** (O'Meara 1963, §63B, p. 167):
$S_\mathfrak p(U \perp W) = S_\mathfrak pU \cdot (dU, dW)_\mathfrak p \cdot S_\mathfrak pW$, for
$U = \langle a\rangle$, $W = \langle b\rangle$ and $U \perp W = \langle a, b\rangle$ (`Fin.append`). -/
@[kb "omeara1963" "§63B, p. 167 (S_p(U ⊥ W) = S_pU · (dU, dW)_p · S_pW)"]
theorem hasseS_append {m : ℕ} (a : Fin m → K) (b : Fin n → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    hasseS K (Fin.append a b) = hasseS K a * hilbertSymbol K (∏ i, a i) (∏ i, b i) * hasseS K b :=
  hasseS_append_gen (HasseIsoNF.localHilbertField_adicCompletion v) a b ha hb

/-- **The Hasse symbol of a scaled space** (O'Meara 1963, §63B, p. 167):
$S_\mathfrak p(V^{\alpha}) = (\alpha, (-1)^{n(n+1)/2}(dV)^{n+1})_\mathfrak p\,S_\mathfrak pV$, where $V^{\alpha}$ is $V$
with the form scaled by $\alpha$, i.e. $\langle \alpha a_0, \dots, \alpha a_{n-1}\rangle$. -/
@[kb "omeara1963" "§63B, p. 167 (S_p(V^α) = (α, (−1)^{n(n+1)/2} (dV)^{n+1})_p S_pV)"]
theorem hasseS_smul (α : K) (hα : α ≠ 0) (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    hasseS K (fun i => α * a i) =
      hilbertSymbol K α ((-1) ^ (n * (n + 1) / 2) * (∏ i, a i) ^ (n + 1)) * hasseS K a := by
  exact hasseS_smul_gen (HasseIsoNF.localHilbertField_adicCompletion v) α hα n a ha

/-! ### Theorems 63:22 and 63:23 -/

/-- **Theorem 63:22** (O'Meara 1963, p. 171): for a regular space $V = \langle a_0, \dots, a_{n-1}\rangle$ over the local
field $F_\mathfrak p$ with $n \ge 1$, there is a regular space $V'$ with $\dim V' = \dim V$, $dV' = dV$ and
$S_\mathfrak pV' = -S_\mathfrak pV$ if and only if $V$ is neither a line ($n = 1$) nor a hyperbolic plane ($n = 2$ and
$-dV$ a square).

*Update:* the hypothesis $n \ge 1$ is needed and is not stated in the book: the zero space is neither a line nor a
hyperbolic plane, but every space of dimension $0$ has Hasse symbol $1$. -/
@[kb "omeara1963" "§63C, 63:22, p. 171 (V' with the same n, dV and S_pV' = −S_pV iff V is not a line or H)"]
theorem exists_hasseS_neg_iff (hn : 1 ≤ n) (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    (∃ b : Fin n → K, (∀ i, b i ≠ 0) ∧ (∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧
        hasseS K b = -hasseS K a) ↔
      ¬ (n = 1 ∨ (n = 2 ∧ IsSquare (-∏ i, a i))) := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  constructor
  · rintro ⟨b, hb, ⟨t, ht, hdt⟩, hS⟩ h
    have h1 := hasseS_exc hK ha (one_ne_zero (α := K)) (d₀ := ∏ i, a i) (by ring) h
    have h2 := hasseS_exc hK hb ht hdt h
    rw [h1, h2] at hS
    rcases PadicClass.hs_pm (-1 : K) (∏ i, a i) with h3 | h3 <;> rw [h3] at hS <;> omega
  · intro h
    exact exists_hasseS_neg_gen hK (exists_nonsquare_adic v)
      (by rcases Nat.lt_or_ge n 2 with h' | h'
          · exact absurd (Or.inl (by omega)) h
          · exact h') a ha (fun h2 hsq => h (Or.inr ⟨h2, hsq⟩))

/-- **Theorem 63:23** (O'Meara 1963, p. 171): given $n_0 \ge 1$, $d_0 \in \dot F_\mathfrak p$ and $s_0 = \pm 1$, there is
a regular space $V$ over $F_\mathfrak p$ with $\dim V = n_0$, $dV = d_0$ and $S_\mathfrak pV = s_0$ if and only if
$s_0 = (-1, d_0)_\mathfrak p$ whenever $n_0 = 1$, or $n_0 = 2$ and $d_0 \in -F_\mathfrak p^{2}$.

*Reconstruction:* the formula for $s_0$ is lost in the machine-read text; it is reconstructed from the proof ("the
spaces $\langle d_0\rangle$ and $\langle 1\rangle \perp \langle -1\rangle$ will work in the exceptional cases"):
$S\langle d_0\rangle = (d_0, d_0) = (-1, d_0)$ and $S(\langle 1\rangle \perp \langle -1\rangle) = (-1, -1) =
(-1, d_0)$ when $d_0 \in -F^{2}$. O'Meara's $n_0 \in \mathbb N$ is a positive integer (for $n_0 = 0$ only
$d_0 = 1$, $s_0 = 1$ occur). -/
@[kb "omeara1963" "§63C, 63:23, p. 171 (the invariants (n₀, d₀, s₀) that occur)"]
theorem exists_invariants_iff {n₀ : ℕ} (hn : 1 ≤ n₀) {d₀ : K} (hd : d₀ ≠ 0) {s₀ : ℤ} (hs : s₀ = 1 ∨ s₀ = -1) :
    (∃ a : Fin n₀ → K, (∀ i, a i ≠ 0) ∧ (∃ t : K, t ≠ 0 ∧ ∏ i, a i = t ^ 2 * d₀) ∧ hasseS K a = s₀) ↔
      ((n₀ = 1 ∨ (n₀ = 2 ∧ IsSquare (-d₀))) → s₀ = hilbertSymbol K (-1) d₀) := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  constructor
  · rintro ⟨a, ha, ⟨t, ht, hdt⟩, hS⟩ h
    rw [← hS]; exact hasseS_exc hK ha ht hdt h
  · intro H
    obtain ⟨m, rfl⟩ : ∃ m, n₀ = m + 1 := ⟨n₀ - 1, by omega⟩
    set a0 : Fin (m + 1) → K := Fin.cons d₀ (fun _ : Fin m => (1 : K)) with ha0def
    have ha0 : ∀ i, a0 i ≠ 0 := PadicClass.cons_ne_zero hd (fun _ => one_ne_zero)
    have hprod : ∏ i, a0 i = d₀ := by simp [a0, Fin.prod_cons]
    have h1 : PadicClass.hasseVec (fun _ : Fin m => (1 : K)) = 1 := by
      simp [PadicClass.hasseVec, hilbertSymbol_one_right]
    have hS0 : hasseS K a0 = hilbertSymbol K (-1) d₀ := by
      rw [hasseS_eq_vec_mul hK a0 ha0, hprod, ha0def,
        PadicClass.hasseVec_cons hK hd (fun _ => one_ne_zero), h1]
      simp [hilbertSymbol_one_right]
    by_cases hs0 : s₀ = hilbertSymbol K (-1) d₀
    · exact ⟨a0, ha0, ⟨1, one_ne_zero, by rw [hprod]; ring⟩, by rw [hS0, hs0]⟩
    · have hexc : ¬ (m + 1 = 1 ∨ (m + 1 = 2 ∧ IsSquare (-d₀))) := fun h => hs0 (H h)
      obtain ⟨b, hb, ⟨t, ht, hdt⟩, hSb⟩ := exists_hasseS_neg_gen hK (exists_nonsquare_adic v)
        (by rcases Nat.lt_or_ge (m + 1) 2 with h' | h'
            · exact absurd (Or.inl (by omega)) hexc
            · exact h') a0 ha0 (fun h2 hsq => hexc (Or.inr ⟨h2, by rwa [hprod] at hsq⟩))
      refine ⟨b, hb, ⟨t, ht, by rw [hdt, hprod]⟩, ?_⟩
      rw [hSb, hS0]
      rcases hs with h1 | h1 <;> rcases PadicClass.hs_pm (-1 : K) d₀ with h2 | h2 <;>
        rw [h2] at hs0 ⊢ <;> omega

/-! ### Example 63:24 -/


theorem split_ternary {L : Type*} [Field L] [CharZero L] (a : Fin 4 → L) (_ha : ∀ i, a i ≠ 0)
    (U : Submodule L (Fin 4 → L)) (hU : ((weightedSumSquares L a).restrict U).radical = ⊥)
    (hU3 : Module.finrank L U = 3) :
    ∃ (c : Fin 3 → L) (E : L), (∀ i, c i ≠ 0) ∧
      (diag a).IsometricIn L (diag ![c 0, c 1, c 2, E]) ∧
      ∀ r : L, (∃ y : Fin 3 → L, ∑ i, c i * y i ^ 2 = r) →
        ∃ x ∈ U, weightedSumSquares L a x = r := by
  have : Invertible (2 : L) := invertibleOfNonzero two_ne_zero
  set Q := weightedSumSquares L a with hQdef
  set Q' := Q.restrict U with hQ'def
  have hsep : (QuadraticMap.associated (R := L) Q').SeparatingLeft := by
    intro x hx
    have : x ∈ Q'.radical := by
      rw [QuadraticMap.radical_eq_ker_associated]
      exact LinearMap.mem_ker.mpr (LinearMap.ext hx)
    rw [hU] at this
    simpa using this
  obtain ⟨k, rfl, w, ⟨e⟩⟩ : ∃ k, k = 3 ∧ ∃ w : Fin k → Lˣ,
      Q'.Equivalent (weightedSumSquares L w) := by
    obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q' hsep
    exact ⟨_, hU3, w, hw⟩
  have hQsum : ∀ z, Q z = ∑ i, a i * z i ^ 2 := fun z => by
    simp [hQdef, weightedSumSquares_apply, pow_two]
  have hadd : ∀ z₁ z₂, Q (z₁ + z₂) = Q z₁ + Q z₂ + 2 * ∑ i, a i * z₁ i * z₂ i := fun z₁ z₂ => by
    simp only [hQsum, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set g : (Fin 3 → L) →ₗ[L] (Fin 4 → L) := U.subtype ∘ₗ e.toLinearEquiv.symm.toLinearMap with hg
  have hgU : ∀ y, g y ∈ U := fun y => (e.toLinearEquiv.symm y).2
  have hgQ : ∀ y, Q (g y) = ∑ i, (w i : L) * y i ^ 2 := fun y => by
    have h1 := e.map_app (e.toLinearEquiv.symm y)
    have h2 : Q (g y) = Q' (e.toLinearEquiv.symm y) := rfl
    rw [h2, ← h1]
    have : e (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    rw [this]
    simp [weightedSumSquares_apply, pow_two, Units.smul_def]
  have hginj : Function.Injective g := fun y y' h => by
    have : (e.toLinearEquiv.symm y : Fin 4 → L) = e.toLinearEquiv.symm y' := h
    exact e.toLinearEquiv.symm.injective (Subtype.ext this)
  set wk : Fin 3 → (Fin 4 → L) := fun j => g (Pi.single j 1) with hwk
  set M : Matrix (Fin 3) (Fin 4) L := fun j i => a i * wk j i with hM
  obtain ⟨ev, hevker, hev0⟩ : ∃ ev ∈ LinearMap.ker (Matrix.toLin' M), ev ≠ 0 := by
    have := LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.toLin' M)
      (by simp)
    exact (Submodule.ne_bot_iff _).mp this
  have hevj : ∀ j, ∑ i, a i * wk j i * ev i = 0 := fun j => by
    have := congrFun (LinearMap.mem_ker.mp hevker) j
    rw [Matrix.toLin'_apply] at this
    simpa [Matrix.mulVec, dotProduct, hM] using this
  let lam : (Fin 4 → L) →ₗ[L] L :=
    { toFun := fun z => ∑ i, a i * z i * ev i
      map_add' := fun z z' => by
        simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r z => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  have hlam : ∀ y, ∑ i, a i * g y i * ev i = 0 := fun y => by
    have : lam ∘ₗ g = 0 := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simpa [lam, hwk] using hevj j
    exact LinearMap.congr_fun this y
  set Pl : (Fin 4 → L) →ₗ[L] (Fin 4 → L) :=
    g ∘ₗ LinearMap.funLeft L L (Fin.castSucc : Fin 3 → Fin 4) +
      (LinearMap.proj (Fin.last 3) : (Fin 4 → L) →ₗ[L] L).smulRight ev with hPl
  have hPlx : ∀ x, Pl x = g (fun j => x (Fin.castSucc j)) + x (Fin.last 3) • ev := fun x => rfl
  have hQP : ∀ x, Q (Pl x) =
      ∑ j : Fin 3, (w j : L) * x (Fin.castSucc j) ^ 2 + Q ev * x (Fin.last 3) ^ 2 := by
    intro x
    rw [hPlx, hadd, hgQ]
    have h1 : Q (x (Fin.last 3) • ev) = x (Fin.last 3) ^ 2 * Q ev := by
      rw [QuadraticMap.map_smul]; simp [smul_eq_mul, pow_two]
    have h2 : ∑ i, a i * g (fun j => x (Fin.castSucc j)) i * (x (Fin.last 3) • ev) i = 0 := by
      have := hlam (fun j => x (Fin.castSucc j))
      calc ∑ i, a i * g (fun j => x (Fin.castSucc j)) i * (x (Fin.last 3) • ev) i
          = x (Fin.last 3) * ∑ i, a i * g (fun j => x (Fin.castSucc j)) i * ev i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Pi.smul_apply, smul_eq_mul]; ring
        _ = 0 := by rw [this, mul_zero]
    rw [h1, h2]; ring
  have hperp : ∀ n ∈ U, ∑ i, a i * ev i * n i = 0 := fun n hn => by
    have hn' : n = g (e.toLinearEquiv ⟨n, hn⟩) := by simp [hg]
    have := hlam (e.toLinearEquiv ⟨n, hn⟩)
    rw [← hn'] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hinj : Function.Injective Pl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hPlx] at hx
    by_cases hx3 : x (Fin.last 3) = 0
    · rw [hx3, zero_smul, add_zero] at hx
      have hy : (fun j => x (Fin.castSucc j)) = 0 := hginj (by rw [hx, map_zero])
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hx3
      · simpa using congrFun hy j
    · exfalso
      have hevU : ev ∈ U := by
        have : ev = g (-(x (Fin.last 3))⁻¹ • (fun j => x (Fin.castSucc j))) := by
          rw [map_smul]
          have : g (fun j => x (Fin.castSucc j)) = -(x (Fin.last 3) • ev) := eq_neg_of_add_eq_zero_left hx
          rw [this, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hx3, neg_smul, one_smul, neg_neg]
        rw [this]; exact hgU _
      have hQev : Q ev = 0 := by
        rw [hQsum]
        have := hperp ev hevU
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hrad : (⟨ev, hevU⟩ : U) ∈ Q'.radical := by
        rw [mem_radical_iff']
        refine ⟨hQev, fun n => ?_⟩
        show Q (ev + n) = Q n
        rw [hadd, hQev, hperp n n.2]; ring
      rw [hU] at hrad
      exact hev0 (by simpa using congrArg Subtype.val (Submodule.mem_bot L |>.mp hrad))
  have hdet : IsUnit (LinearMap.toMatrix' Pl).det := by
    rw [LinearMap.det_toMatrix']
    exact (((LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot.mpr hinj))).map LinearMap.det
  refine ⟨fun j => (w j : L), Q ev, fun i => (w i).ne_zero, ⟨LinearMap.toMatrix' Pl, hdet, fun x => ?_⟩, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, PadicClass.evalIn_diag_self, PadicClass.evalIn_diag_self]
    rw [← hQsum, hQP]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    congr 1
  · rintro r ⟨y, hy⟩
    exact ⟨g y, hgU y, by rw [hgQ]; exact hy⟩



theorem hs_units (h2 : Valued.v (2 : v.adicCompletion F) = 1) {u u' : v.adicCompletion F}
    (hu : Valued.v u = 1) (hu' : Valued.v u' = 1) :
    hilbertSymbol (v.adicCompletion F) u u' = 1 := by
  have hv : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hn2 : (2 : 𝓞 F) ∉ v.asIdeal := by
    have : (2 : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F 2) := by
      rw [map_ofNat, map_ofNat]
    rw [this, hv, HeightOneSpectrum.valuation_of_algebraMap] at h2
    exact HeightOneSpectrum.intValuation_eq_one_iff.mp h2
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have approx : ∀ x : v.adicCompletion F, Valued.v x = 1 → ∃ c : F, v.valuation F c = 1 ∧
      ∃ z : v.adicCompletion F, z ≠ 0 ∧ x = algebraMap F _ c * z ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp (HeightOneSpectrum.denseRange_algebraMap F v) x 1
      one_pos
    rw [dist_eq_norm, Valued.toNormedField.norm_lt_one_iff] at hc
    set c' := algebraMap F (v.adicCompletion F) c with hc'
    have hxc : Valued.v c' = 1 := by
      have := Valuation.map_add_eq_of_lt_left (Valued.v : Valuation (v.adicCompletion F) _)
        (x := x) (y := -(x - c')) (by rw [hx, Valuation.map_neg]; exact hc)
      rw [show x + -(x - c') = c' by ring, hx] at this
      exact this
    have hc0 : c' ≠ 0 := by rintro h; rw [h, map_zero] at hxc; exact zero_ne_one hxc
    have hw : Valued.v (x / c' - 1) < Valued.v (4 : v.adicCompletion F) := by
      rw [h4, show x / c' - 1 = (x - c') / c' by field_simp, map_div₀, hxc, div_one]
      exact hc
    obtain ⟨z, hz⟩ := HN.isSquare_of_valued_sub_one_lt v (x / c') hw
    have hx0 : x ≠ 0 := by rintro h; rw [h, map_zero] at hx; exact zero_ne_one hx
    refine ⟨c, ?_, z, ?_, ?_⟩
    · rw [← hv c]; exact hxc
    · rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hz
      rcases hz with h | h
      · exact hx0 h
      · exact hc0 h
    · rw [pow_two, ← hz]; field_simp; exact hc'
  obtain ⟨c, hc, z, hz0, rfl⟩ := approx u hu
  obtain ⟨c', hc', z', hz0', rfl⟩ := approx u' hu'
  rw [mul_comm (algebraMap F _ c), mul_comm (algebraMap F _ c'), PadicClass.hs_sq_left _ _ _ hz0,
    PadicClass.hs_sq_right _ _ _ hz0']
  exact SqDual.hilbert_units_nondyadic v hn2 c c' hc hc'



theorem hs_unitSq (h2 : Valued.v (2 : K) = 1) {x y r r' u u' : K} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (hu : Valued.v u = 1) (hu' : Valued.v u' = 1) (hx : x = r ^ 2 * u) (hy : y = r' ^ 2 * u') :
    hilbertSymbol K x y = 1 := by
  rw [hx, hy, PadicClass.hs_sq_left _ _ _ hr, PadicClass.hs_sq_right _ _ _ hr']
  exact hs_units v h2 hu hu'

/-- **Example 63:24** (O'Meara 1963, p. 172): let $F_\mathfrak p$ be non-dyadic ($\lvert 2\rvert_\mathfrak p = 1$), let
$V = \langle a_0, a_1, a_2, a_3\rangle$ be a regular quaternary space with $dV$ a unit and $S_\mathfrak pV = 1$, and let
$U$ be a regular ternary subspace of $V$. Then $Q(U)$ contains every unit $\varepsilon$ of $F_\mathfrak p$. The space
is Mathlib's `weightedSumSquares K a` on $K^4$ and $U$ is a submodule with regular restriction. -/
@[kb "omeara1963" "§63C, 63:24, p. 172 (non-dyadic quaternary V, dV a unit, S_pV = 1: Q(U) ⊇ 𝔲 for ternary U)"]
theorem represents_units_of_ternary (h2 : Valued.v (2 : K) = 1) (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (hd : Valued.v (∏ i, a i) = 1) (hS : hasseS K a = 1) (U : Submodule K (Fin 4 → K))
    (hU : ((weightedSumSquares K a).restrict U).radical = ⊥) (hU3 : Module.finrank K U = 3)
    {ε : K} (hε : Valued.v ε = 1) : ∃ x ∈ U, weightedSumSquares K a x = ε := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  obtain ⟨c, E, hc, hiso, hrep⟩ := split_ternary a ha U hU hU3
  obtain ⟨t, ht, hdt⟩ := PadicClass.disc_of_isometric hiso
  set P : K := ∏ i, a i with hPdef
  have hA0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hdt' : c 0 * c 1 * c 2 * E = t ^ 2 * P := by
    have := hdt
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_three] at this
    linear_combination this
  have hE : E ≠ 0 := fun h => by
    rw [h, mul_zero] at hdt'; exact (mul_ne_zero (pow_ne_zero 2 ht) hA0) hdt'.symm
  have hb : ∀ i, (![c 0, c 1, c 2, E] : Fin 4 → K) i ≠ 0 := fun i => by
    fin_cases i <;> simp [hc, hE]
  have hSb : hasseS K ![c 0, c 1, c 2, E] = 1 := by
    rw [← hasseS_eq_of_isometric v ha hb hiso]; exact hS
  rw [hasseS_eq_vec_mul hK _ hb] at hSb
  have hvec : PadicClass.hasseVec (![c 0, c 1, c 2, E] : Fin 4 → K) =
      hilbertSymbol K (c 0) (c 1) * hilbertSymbol K (c 0) (c 2) * hilbertSymbol K (c 1) (c 2) *
        hilbertSymbol K (c 0 * c 1 * c 2) E := by
    have h := hasseVec_cons3 hK (hc 0) (hc 1) (hc 2) (v := ![E])
      (fun i => by fin_cases i; simpa using hE)
    have e : (![c 0, c 1, c 2, E] : Fin 4 → K) =
        Fin.cons (c 0) (Fin.cons (c 1) (Fin.cons (c 2) ![E])) := rfl
    have h1 : PadicClass.hasseVec (![E] : Fin 1 → K) = 1 := by simp [PadicClass.hasseVec]
    rw [e, h, h1]
    simp
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hmε : Valued.v (-ε) = 1 := by rw [Valuation.map_neg]; exact hε
  have hm1 : Valued.v (-1 : K) = 1 := by rw [Valuation.map_neg, map_one]
  have hR : (diag ![c 0, c 1, c 2]).RepresentsIn K ε := by
    rw [PadicClass.represents_three_iff hK (hc 0) (hc 1) (hc 2) hε0]
    rintro ⟨s, hs0, hs⟩
    have hD0 : c 0 * c 1 * c 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) (hc 2)
    have hD : c 0 * c 1 * c 2 = s⁻¹ ^ 2 * (-ε) := by
      rw [hs]; field_simp
    have hEe : E = (t * s) ^ 2 * (P / (-ε)) := by
      have h1 : E = t ^ 2 * P / (c 0 * c 1 * c 2) :=
        eq_div_of_mul_eq hD0 (by linear_combination hdt')
      rw [h1, hs]
      field_simp
    have hvP : Valued.v (P / (-ε)) = 1 := by rw [map_div₀, hd, hmε, div_one]
    have f1 : hilbertSymbol K (-1) (∏ i, ![c 0, c 1, c 2, E] i) = 1 :=
      hs_unitSq v h2 one_ne_zero ht hm1 hd (by ring) (by rw [hdt])
    have f2 : hilbertSymbol K (c 0 * c 1 * c 2) E = 1 :=
      hs_unitSq v h2 (inv_ne_zero hs0) (mul_ne_zero ht hs0) hmε hvP hD hEe
    have f3 : hilbertSymbol K (-1) (-(c 0 * c 1 * c 2)) = 1 :=
      hs_unitSq v h2 one_ne_zero (inv_ne_zero hs0) hm1 hε (by ring)
        (by rw [hs]; field_simp)
    have e3 : hilbertSymbol K (c 0) (c 1) * hilbertSymbol K (c 0) (c 2) *
        hilbertSymbol K (c 1) (c 2) = 1 := by
      rw [hvec, f2, f1] at hSb
      simpa using hSb
    rw [f3, e3]
  obtain ⟨y, hy⟩ := (PadicClass.representsIn_diag_iff _ _).mp hR
  rw [← PadicClass.eq_vec_three c] at hy
  exact hrep ε ⟨y, hy⟩

end QuadFormsKB.OMeara
