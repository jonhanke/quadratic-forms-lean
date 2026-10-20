/-
# Local densities over a DVR: explicit values at dyadic primes for even unimodular forms

**Layer:** DVR, at a **dyadic** prime: $R$ a DVR with uniformizer $\pi \mid 2$, $e = \mathrm{ord}_\pi 2 \ge 1$ arbitrary
(ramified or not), residue field $\mathbb{F} = R/\pi$ of size $q = 2^f$.

**Characteristic-2 counting** (any finite field $\mathbb{F}$ of characteristic 2, $q = \#\mathbb{F}$; Lidl–Niederreiter,
*Finite Fields*, Thms. 6.30–6.32 [unverified]): the Arf sign $\varepsilon(a, b, c) = \pm 1$ of $ax^2 + bxy + cy^2$
(`DVR.arfSign`: $+1$ iff $ac/b^2 \in \{z^2 + z\}$); the binary count `DVR.binCountF_eq`
($q + \varepsilon(q-1)$ at $0$, $q - \varepsilon$ elsewhere); and for an orthogonal sum of $r$ nonsingular binary blocks,
with $\varepsilon = \prod_i \varepsilon_i$, `DVR.pairCountF_mul_q`:
$q\,N(s) = q^{2r} + \varepsilon q^r (q[s = 0] - 1)$, i.e. $N(0) = q^{2r-1} + \varepsilon(q^r - q^{r-1})$ and
$N(s) = q^{2r-1} - \varepsilon q^{r-1}$ for $s \ne 0$ — the odd-characteristic formula of Table 1 with $\chi((-1)^{n/2}D)$
replaced by $\varepsilon$.

**Forms:** `DVR.pairSumForm A` $= \bigoplus_{i<r}(a_i x_{2i}^2 + b_i x_{2i}x_{2i+1} + c_i x_{2i+1}^2)$ over any commutative
ring; for $\pi \mid 2$ and all $b_i$ units it is in normal form `IsJordanFormW` with all $w = 0$, $\mu = 0`
(`DVR.isJordanFormW_pairSumForm`) and gradient bound $0$ (`DVR.gradBound_pairSumForm`), so Lemma 3.2 holds from
level $1$ (`DVRDyadic.lean`).

**Paper results at dyadic $\mathfrak p$** (Hanke 2004 says Table 1 at $\mathfrak p \mid 2$ "must be computed on a
case-by-case basis", p. 362): dyadic Table 1 for $n = 2r$ (`DVR.card_pairSum_mod_pi`), Remark 3.4.1(a)
(`DVR.localDensity_unit_pairSum`: $\beta_\pi(m) = 1 - \varepsilon q^{-r}$), $\mathrm{ord}_\pi m = 1$
(`DVR.localDensity_ord_one_pairSum`), Remark 3.5.1 (`DVR.isLocallyRepresentedAt_pairSum`, $r \ge 2$), Table 2
(`DVR.table2_even_unit_pairSum`, `DVR.table2_ord_one_pairSum`), with $\Phi_n(\mathfrak p) := \varepsilon$. For these
forms nothing depends on $e$; $f$ enters only through $q = 2^f$. Forms with a 1-dimensional unimodular block
need level $2e + 1$ (`DVR.localDensity_unit_unimodular` with $t = e$); ℤ₂ checks are in `BridgeDyadic.lean`.

**Depends on** `DVRDyadic.lean`.
-/
import QuadFormsKB.LocalDensity.DVRDyadic

set_option linter.unusedSectionVars false

namespace QuadFormsKB.LocalDensity.DVR

section CharTwo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The number (as an integer) of $z \in \mathbb{F}$ with $z^2 + z = d$ (Artin–Schreier). -/
noncomputable def asCountF (d : F) : ℤ := ∑ z : F, if z ^ 2 + z = d then 1 else 0

/-- The number (as an integer) of $(x, y) \in \mathbb{F}^2$ with $a x^2 + b x y + c y^2 = s$. -/
noncomputable def binCountF (a b c s : F) : ℤ :=
  ∑ x : F × F, if a * x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2 = s then 1 else 0

/-- **The Arf sign** $\varepsilon(a, b, c) \in \{\pm 1\}$ of the binary form $a x^2 + bxy + cy^2$ over $\mathbb{F}$ of
characteristic $2$ ($b \ne 0$): $+1$ if its Arf invariant $ac/b^2$ lies in $\wp(\mathbb{F}) = \{z^2 + z\}$
(the form is hyperbolic), $-1$ otherwise (anisotropic). -/
@[kb "lidl1997" "Ch. 6, §2 (Arf invariant) [unverified]"]
noncomputable def arfSign (a b c : F) : ℤ := if ∃ z : F, z ^ 2 + z = a * c / b ^ 2 then 1 else -1

theorem asCountF_eq (d : F) : asCountF d = 1 + (if ∃ z : F, z ^ 2 + z = d then 1 else -1) := by
  unfold asCountF
  split_ifs with h
  · obtain ⟨z0, hz0⟩ := h
    have hne : z0 ≠ z0 + 1 := fun h => one_ne_zero (by linear_combination -h)
    have key : ∀ z : F, (z ^ 2 + z = d) ↔ (z = z0 ∨ z = z0 + 1) := by
      intro z
      have hfac : z ^ 2 + z - d = (z - z0) * (z - (z0 + 1)) := by
        rw [← hz0]
        have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
        linear_combination (z - z0 ^ 2 + z * z0 - z0) * h2
      rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    have : ∀ z : F, (if z ^ 2 + z = d then (1 : ℤ) else 0) =
        (if z = z0 then 1 else 0) + (if z = z0 + 1 then 1 else 0) := by
      intro z
      by_cases h1 : z = z0
      · subst h1; simp [hz0, hne]
      · by_cases h2 : z = z0 + 1
        · subst h2; simp [Ne.symm hne, (key _).2 (Or.inr rfl)]
        · simp [h1, h2, (not_congr (key z)).2 (by tauto)]
    rw [Finset.sum_congr rfl fun z _ => this z, Finset.sum_add_distrib]
    simp
  · push Not at h
    simp [h]


theorem two_eq_zero_F : (2 : F) = 0 := CharTwo.two_eq_zero

theorem add_eq_zero_iff_eq_F (u v : F) : u + v = 0 ↔ u = v := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- In characteristic $2$ every element of a finite field is a square (Frobenius is bijective). -/
theorem sq_surjective_F : Function.Surjective (fun x : F => x ^ 2) := by
  have hinj : Function.Injective (fun x : F => x ^ 2) := by
    intro x y h
    have h' : x ^ 2 = y ^ 2 := h
    have : (x - y) ^ 2 = 0 := by
      linear_combination h' + (y ^ 2 - x * y) * (two_eq_zero_F (F := F))
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  exact Finite.injective_iff_surjective.mp hinj

/-- Scaling: $N(\lambda^2 s) = N(s)$ for $\lambda \ne 0$ (substitute $(x, y) \mapsto (\lambda x, \lambda y)$). -/
theorem binCountF_sq_mul (a b c s l : F) (hl : l ≠ 0) :
    binCountF a b c (l ^ 2 * s) = binCountF a b c s := by
  unfold binCountF
  rw [← (Equiv.prodCongr (Equiv.mulLeft₀ l hl) (Equiv.mulLeft₀ l hl)).sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.mulLeft₀_apply]
  congr 1
  apply propext
  rw [show a * (l * x.1) ^ 2 + b * (l * x.1) * (l * x.2) + c * (l * x.2) ^ 2 =
    l ^ 2 * (a * x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2) by ring]
  exact mul_right_inj' (pow_ne_zero 2 hl)

theorem sum_binCountF (a b c : F) : ∑ s : F, binCountF a b c s = (Fintype.card F : ℤ) ^ 2 := by
  unfold binCountF
  rw [Finset.sum_comm]
  simp [Fintype.card_prod, sq]

theorem binCountF_eq_sum (a b c s : F) :
    binCountF a b c s = ∑ y : F, ∑ x : F, if a * x ^ 2 + b * x * y + c * y ^ 2 = s then 1 else 0 := by
  unfold binCountF
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **Binary count at $0$ in characteristic $2$**: for $b \ne 0$,
$\#\{a x^2 + bxy + cy^2 = 0\} = q + \varepsilon(q - 1)$, $\varepsilon$ the Arf sign. -/
theorem binCountF_zero (a b c : F) (hb : b ≠ 0) :
    binCountF a b c 0 = Fintype.card F + arfSign a b c * (Fintype.card F - 1) := by
  rw [binCountF_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  have hcard : ((Finset.univ : Finset F).erase 0).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hq1 : (1 : ℕ) ≤ Fintype.card F := Fintype.card_pos
  by_cases ha : a = 0
  · subst ha
    have h0 : arfSign (0 : F) b c = 1 := by
      unfold arfSign; exact ite_eq_left_iff.2 fun h => absurd ⟨0, by simp⟩ h
    have hin : ∀ y ∈ (Finset.univ : Finset F).erase 0,
        (∑ x : F, if 0 * x ^ 2 + b * x * y + c * y ^ 2 = 0 then (1 : ℤ) else 0) = 1 := by
      intro y hy
      have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
      have : ∀ x : F, (0 * x ^ 2 + b * x * y + c * y ^ 2 = 0) ↔ x = -(c * y) / b := by
        intro x
        rw [eq_div_iff hb]
        constructor
        · intro h
          have : y * (x * b + c * y) = 0 := by linear_combination h
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hy0
          · linear_combination h
        · intro h; linear_combination y * h
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_congr rfl hin, h0]
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    push_cast [hq1]
    ring
  · have hin : ∀ y ∈ (Finset.univ : Finset F).erase 0,
        (∑ x : F, if a * x ^ 2 + b * x * y + c * y ^ 2 = 0 then (1 : ℤ) else 0) =
          asCountF (a * c / b ^ 2) := by
      intro y hy
      have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
      have hl : b * y / a ≠ 0 := div_ne_zero (mul_ne_zero hb hy0) ha
      unfold asCountF
      rw [← Equiv.sum_comp (Equiv.mulLeft₀ (b * y / a) hl)]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Equiv.mulLeft₀_apply]
      congr 1
      apply propext
      have hk : (b * y) ^ 2 / a ≠ 0 := div_ne_zero (pow_ne_zero 2 (mul_ne_zero hb hy0)) ha
      rw [show a * (b * y / a * z) ^ 2 + b * (b * y / a * z) * y + c * y ^ 2 =
          (b * y) ^ 2 / a * (z ^ 2 + z + a * c / b ^ 2) by field_simp,
        mul_eq_zero, or_iff_right hk, add_eq_zero_iff_eq_F]
    rw [Finset.sum_congr rfl hin, asCountF_eq]
    have h0 : (∑ x : F, if a * x ^ 2 + b * x * 0 + c * 0 ^ 2 = 0 then (1 : ℤ) else 0) = 1 := by
      simp [ha]
    rw [h0]
    unfold arfSign
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast [hq1]
    ring

/-- **Binary count in characteristic $2$** (the char-2 analogue of Table 1, $n = 2$): for $b \ne 0$, $q = \#\mathbb{F}$,
and $\varepsilon$ the Arf sign of $a x^2 + bxy + cy^2$:
$$\#\{(x, y) : ax^2 + bxy + cy^2 = s\} = \begin{cases} q + \varepsilon (q - 1) & s = 0,\\ q - \varepsilon & s \ne 0.\end{cases}$$ -/
@[kb "lidl1997" "Ch. 6, §2 [unverified]"]
theorem binCountF_eq (a b c : F) (hb : b ≠ 0) (s : F) :
    binCountF a b c s = Fintype.card F - arfSign a b c +
      if s = 0 then arfSign a b c * Fintype.card F else 0 := by
  have hq : (1 : ℤ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have h0 := binCountF_zero a b c hb
  -- every nonzero count equals the count at 1
  have h1 : ∀ s : F, s ≠ 0 → binCountF a b c s = binCountF a b c 1 := by
    intro s hs
    obtain ⟨l, hl⟩ := sq_surjective_F s
    have hl0 : l ≠ 0 := by rintro rfl; exact hs (by simpa using hl.symm)
    rw [← binCountF_sq_mul a b c 1 l hl0, mul_one]
    exact congrArg _ hl.symm
  have hsum := sum_binCountF a b c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
    Finset.sum_congr rfl fun s hs => h1 s (Finset.ne_of_mem_erase hs), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul, h0] at hsum
  have hq1 : (1 : ℕ) ≤ Fintype.card F := Fintype.card_pos
  push_cast [hq1] at hsum
  have hN1 : binCountF a b c 1 = Fintype.card F - arfSign a b c := by
    have : ((Fintype.card F : ℤ) - 1) * (binCountF a b c 1 - (Fintype.card F - arfSign a b c)) = 0 := by
      linear_combination hsum
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  split_ifs with hs
  · subst hs; rw [h0]; ring
  · rw [h1 s hs, hN1]; ring

/-! ### Orthogonal sums of binary blocks over $\mathbb{F}$ -/

/-- The value $a x^2 + bxy + cy^2$ of the binary block $A = (a, b, c)$ at $(x, y)$. -/
def binF (A : F × F × F) (x : F × F) : F := A.1 * x.1 ^ 2 + A.2.1 * x.1 * x.2 + A.2.2 * x.2 ^ 2

/-- The number (as an integer) of $(\vec{x}_0, \dots, \vec{x}_{r-1}) \in (\mathbb{F}^2)^r$ with
$\sum_i a_i x_i^2 + b_i x_i y_i + c_i y_i^2 = s$, for blocks $A_i = (a_i, b_i, c_i)$. -/
noncomputable def pairCountF {r : ℕ} (A : Fin r → F × F × F) (s : F) : ℤ :=
  ∑ x : Fin r → F × F, if ∑ i, binF (A i) (x i) = s then 1 else 0

omit [CharP F 2] in
theorem pairCountF_cons {r : ℕ} (A0 : F × F × F) (A : Fin r → F × F × F) (s : F) :
    pairCountF (Fin.cons A0 A : Fin (r + 1) → F × F × F) s =
      ∑ y : F × F, pairCountF A (s - binF A0 y) := by
  unfold pairCountF
  rw [← (Fin.consEquiv fun _ => F × F).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

omit [CharP F 2] in
theorem sum_comp_fibre {α : Type*} [Fintype α] (f : α → F) (g : F → ℤ) :
    ∑ y, g (f y) = ∑ t, (∑ y, if f y = t then (1 : ℤ) else 0) * g t := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

/-- **Count for an orthogonal sum of $r$ nonsingular binary blocks in characteristic $2$** (the char-2
analogue of Table 1 for even $n = 2r$; cf. Lidl–Niederreiter, Thm. 6.32 [unverified]): if every $b_i \ne 0$
and $\varepsilon = \prod_i \varepsilon(a_i, b_i, c_i)$ (the Arf sign of the whole form), then for $q = \#\mathbb{F}$
$$q \cdot \#\{\textstyle\sum_i a_ix_i^2 + b_ix_iy_i + c_iy_i^2 = s\} = q^{2r} + \varepsilon q^r\,(q\,[s = 0] - 1),$$
i.e. the count is $q^{2r-1} + \varepsilon(q^r - q^{r-1})$ at $s = 0$ and $q^{2r-1} - \varepsilon q^{r-1}$ at $s \ne 0$
(for $r \ge 1$; `pairCountF_zero`, `pairCountF_ne_zero`). -/
@[kb "lidl1997" "Ch. 6, §2 [unverified]"]
theorem pairCountF_mul_q {r : ℕ} (A : Fin r → F × F × F) (hb : ∀ i, (A i).2.1 ≠ 0) (s : F) :
    (Fintype.card F : ℤ) * pairCountF A s =
      (Fintype.card F : ℤ) ^ (2 * r) + (∏ i, arfSign (A i).1 (A i).2.1 (A i).2.2) *
        (Fintype.card F : ℤ) ^ r * ((if s = 0 then (Fintype.card F : ℤ) else 0) - 1) := by
  induction r generalizing s with
  | zero =>
    unfold pairCountF
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty,
      Finset.prod_empty, pow_zero, mul_zero, one_mul]
    by_cases hs : s = 0
    · subst hs; simp
    · simp [hs, Ne.symm hs]
  | succ r ih =>
    set qq : ℤ := (Fintype.card F : ℤ) with hqq
    rw [← Fin.cons_self_tail A, pairCountF_cons, Finset.mul_sum, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have ih' := fun u => ih (Fin.tail A) (fun i => hb i.succ) u
    simp_rw [ih']
    set ε := ∏ i : Fin r, arfSign (Fin.tail A i).1 (Fin.tail A i).2.1 (Fin.tail A i).2.2
    set A0 := A 0
    have hfib := sum_comp_fibre (binF A0)
      (fun u => qq ^ (2 * r) + ε * qq ^ r * ((if s - u = 0 then qq else 0) - 1))
    rw [hfib]
    have hbc : ∀ t, (∑ y : F × F, if binF A0 y = t then (1 : ℤ) else 0) =
        qq - arfSign A0.1 A0.2.1 A0.2.2 + if t = 0 then arfSign A0.1 A0.2.1 A0.2.2 * qq else 0 :=
      fun t => binCountF_eq A0.1 A0.2.1 A0.2.2 (hb 0) t
    simp_rw [hbc]
    set ε0 := arfSign A0.1 A0.2.1 A0.2.2
    have hpt : ∀ t : F, (qq - ε0 + if t = 0 then ε0 * qq else 0) *
        (qq ^ (2 * r) + ε * qq ^ r * ((if s - t = 0 then qq else 0) - 1)) =
        (qq - ε0) * (qq ^ (2 * r) - ε * qq ^ r) + (if t = s then (qq - ε0) * (ε * qq ^ (r + 1)) else 0) +
          (if t = 0 then ε0 * qq * (qq ^ (2 * r) - ε * qq ^ r) else 0) +
          (if t = 0 then (if t = s then ε0 * qq * (ε * qq ^ (r + 1)) else 0) else 0) := by
      intro t
      have : (s - t = 0) ↔ (t = s) := by rw [sub_eq_zero, eq_comm]
      simp only [this]
      split_ifs <;> ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    by_cases hs : s = 0
    · subst hs; simp only [↓reduceIte]; ring
    · simp only [hs, ↓reduceIte, Ne.symm hs]; ring

omit [CharP F 2] in
theorem arfSign_sq (a b c : F) : arfSign a b c ^ 2 = 1 := by
  unfold arfSign; split_ifs <;> norm_num

omit [CharP F 2] in
theorem prod_arfSign_sq {r : ℕ} (A : Fin r → F × F × F) :
    (∏ i, arfSign (A i).1 (A i).2.1 (A i).2.2) ^ 2 = 1 := by
  rw [← Finset.prod_pow]; simp [arfSign_sq]

/-- **Even-dimensional char-2 Table 1, $s = 0$**: for $r \ge 1$ nonsingular binary blocks,
$\#\{Q = 0\} = q^{2r-1} + \varepsilon\,(q^r - q^{r-1})$. -/
theorem pairCountF_zero {r : ℕ} (hr : 1 ≤ r) (A : Fin r → F × F × F) (hb : ∀ i, (A i).2.1 ≠ 0) :
    pairCountF A 0 = (Fintype.card F : ℤ) ^ (2 * r - 1) + (∏ i, arfSign (A i).1 (A i).2.1 (A i).2.2) *
      ((Fintype.card F : ℤ) ^ r - (Fintype.card F : ℤ) ^ (r - 1)) := by
  have h := pairCountF_mul_q A hb 0
  have hq : (Fintype.card F : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine mul_left_cancel₀ hq ?_
  rw [h, show 2 * (r + 1) - 1 = 2 * r + 1 by omega, Nat.add_sub_cancel]
  simp only [↓reduceIte]
  ring

/-- **Even-dimensional char-2 Table 1, $s \ne 0$**: for $r \ge 1$ nonsingular binary blocks,
$\#\{Q = s\} = q^{2r-1} - \varepsilon\, q^{r-1}$. -/
theorem pairCountF_ne_zero {r : ℕ} (hr : 1 ≤ r) (A : Fin r → F × F × F) (hb : ∀ i, (A i).2.1 ≠ 0)
    (s : F) (hs : s ≠ 0) :
    pairCountF A s = (Fintype.card F : ℤ) ^ (2 * r - 1) - (∏ i, arfSign (A i).1 (A i).2.1 (A i).2.2) *
      (Fintype.card F : ℤ) ^ (r - 1) := by
  have h := pairCountF_mul_q A hb s
  have hq : (Fintype.card F : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine mul_left_cancel₀ hq ?_
  rw [h, show 2 * (r + 1) - 1 = 2 * r + 1 by omega, Nat.add_sub_cancel]
  simp only [hs, ↓reduceIte]
  ring

end CharTwo

/-! ### Orthogonal sums of binary blocks over a ring -/

section PairSum



open QuadForm

/-- The coordinate $(i, j) \mapsto 2i + j$ of the block form. -/
abbrev pidx {r : ℕ} (i : Fin r) (j : Fin 2) : Fin (r * 2) := finProdFinEquiv (i, j)

theorem pidx_val {r : ℕ} (i : Fin r) (j : Fin 2) : (pidx i j : ℕ) = j + 2 * i := by
  simp [pidx, finProdFinEquiv_apply_val]

/-- **The orthogonal sum of binary blocks** $\bigoplus_{i<r} (a_i x_{2i}^2 + b_i x_{2i}x_{2i+1} + c_i x_{2i+1}^2)$ over a
commutative ring $S$, for $A_i = (a_i, b_i, c_i)$; coordinates $2i, 2i+1$ (`pidx i 0`, `pidx i 1`). -/
@[kb "omeara1963" "§93 (dyadic unimodular splitting) [unverified]"]
def pairSumForm {S : Type*} [CommRing S] {r : ℕ} (A : Fin r → S × S × S) : QuadForm S (r * 2) :=
  QuadForm.ofUpper fun k l =>
    if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1 then
      (if (finProdFinEquiv.symm k).2 = 0 ∧ (finProdFinEquiv.symm l).2 = 0 then (A (finProdFinEquiv.symm k).1).1
      else if (finProdFinEquiv.symm k).2 = 0 ∧ (finProdFinEquiv.symm l).2 = 1 then
        (A (finProdFinEquiv.symm k).1).2.1
      else if (finProdFinEquiv.symm k).2 = 1 ∧ (finProdFinEquiv.symm l).2 = 1 then
        (A (finProdFinEquiv.symm k).1).2.2
      else 0)
    else 0

theorem pairSumForm_coeff {S : Type*} [CommRing S] {r : ℕ} (A : Fin r → S × S × S) (i i' : Fin r)
    (j j' : Fin 2) :
    (pairSumForm A).coeff (pidx i j) (pidx i' j') =
      if i = i' then
        (if j = 0 ∧ j' = 0 then (A i).1 else if j = 0 ∧ j' = 1 then (A i).2.1
          else if j = 1 ∧ j' = 1 then (A i).2.2 else 0)
      else 0 := by
  simp only [pairSumForm, QuadForm.ofUpper, Matrix.of_apply, pidx, Equiv.symm_apply_apply]
  by_cases hii : i = i'
  · subst hii
    simp only [↓reduceIte]
    have hle : (finProdFinEquiv (i, j) ≤ finProdFinEquiv (i, j')) ↔ j ≤ j' := by
      rw [Fin.le_iff_val_le_val, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val,
        Fin.le_iff_val_le_val]
      simp only; omega
    simp only [hle]
    fin_cases j <;> fin_cases j' <;> simp
  · simp [hii]

theorem pidx_le_iff {r : ℕ} (i : Fin r) (j j' : Fin 2) : pidx i j ≤ pidx i j' ↔ j ≤ j' := by
  rw [Fin.le_iff_val_le_val, pidx_val, pidx_val, Fin.le_iff_val_le_val]; omega

theorem evalIn_pairSumForm {S : Type*} [CommRing S] (K : Type*) [CommRing K] [Algebra S K] {r : ℕ}
    (A : Fin r → S × S × S) (x : Fin (r * 2) → K) :
    (pairSumForm A).evalIn K x = ∑ i, (algebraMap S K (A i).1 * x (pidx i 0) ^ 2 +
      algebraMap S K (A i).2.1 * x (pidx i 0) * x (pidx i 1) + algebraMap S K (A i).2.2 * x (pidx i 1) ^ 2) := by
  unfold QuadForm.evalIn
  rw [← finProdFinEquiv.sum_comp]
  simp_rw [← finProdFinEquiv.sum_comp (fun l => if _ ≤ l then _ else _)]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : ∀ j : Fin 2, (∑ i' : Fin r, ∑ j' : Fin 2,
      if pidx i j ≤ pidx i' j' then
        algebraMap S K ((pairSumForm A).coeff (pidx i j) (pidx i' j')) * x (pidx i j) * x (pidx i' j')
      else 0) = ∑ j' : Fin 2, if pidx i j ≤ pidx i j' then
        algebraMap S K ((pairSumForm A).coeff (pidx i j) (pidx i j')) * x (pidx i j) * x (pidx i j')
      else 0 := by
    intro j
    rw [Finset.sum_eq_single i]
    · intro i' _ hi'
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [pairSumForm_coeff, ite_eq_right_iff.2 (fun h => absurd h (Ne.symm hi'))]; simp
    · simp
  rw [Fin.sum_univ_two, hz 0, hz 1]
  simp only [Fin.sum_univ_two, pidx_le_iff, pairSumForm_coeff]
  simp
  ring

end PairSum

section Dyadic


variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

theorem pidx_inj {r : ℕ} {i i' : Fin r} {j j' : Fin 2} (h : pidx i j = pidx i' j') : i = i' ∧ j = j' := by
  have := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at this
  exact this

/-- The pairs $\{(2i, 2i+1)\}$ of `pairSumForm`. -/
def pairSumPairs (r : ℕ) : Finset (Fin (r * 2) × Fin (r * 2)) :=
  Finset.univ.image fun i : Fin r => (pidx i 0, pidx i 1)

theorem isPaired_pairSumPairs {r : ℕ} (k : Fin (r * 2)) : IsPaired (pairSumPairs r) k := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  refine ⟨(pidx i 0, pidx i 1), Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **`pairSumForm` is in dyadic normal form**: if $\pi \mid 2$ and every $b_i$ is a unit, then
$\bigoplus_i (a_i, b_i, c_i)$ is in normal form `IsJordanFormW` with the pairs $(2i, 2i+1)$, all $w = 0$ and all
scale exponents $\mu = 0$. -/
theorem isJordanFormW_pairSumForm {r : ℕ} (A : Fin r → R × R × R) {π : R} (hπ : Irreducible π)
    (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) :
    IsJordanFormW (pairSumForm A) π (pairSumPairs r) 0 := by
  refine ⟨fun _ => h2, ?_, ?_, ?_, ?_, fun k hk => absurd (isPaired_pairSumPairs k) hk⟩
  · intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    rw [Fin.lt_def, pidx_val, pidx_val]; simp
  · intro e he e' he' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 he'
    have hii : i ≠ i' := fun h => hne (by rw [h])
    refine ⟨fun h => hii (pidx_inj h).1, fun h => hii (pidx_inj h).1, fun h => hii (pidx_inj h).1,
      fun h => hii (pidx_inj h).1⟩
  · intro k l hkl hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective l
    change (pairSumForm A).coeff (pidx i j) (pidx i' j') = 0
    by_cases hii : i = i'
    · subst hii
      have hjj : j < j' := by
        have : pidx i j < pidx i j' := hkl
        rw [Fin.lt_def, pidx_val, pidx_val] at this
        rw [Fin.lt_def]; omega
      have : j = 0 ∧ j' = 1 := by fin_cases j <;> fin_cases j' <;> simp_all
      obtain ⟨rfl, rfl⟩ := this
      exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) hP
    · rw [pairSumForm_coeff, ite_eq_right_iff.2 (fun h => absurd h hii)]
  · intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    refine ⟨rfl, ?_⟩
    have ha : (pairSumForm A).coeff (pidx i 0) (pidx i 0) = (A i).1 := by rw [pairSumForm_coeff]; simp
    have hb' : (pairSumForm A).coeff (pidx i 0) (pidx i 1) = (A i).2.1 := by
      rw [pairSumForm_coeff]; simp
    have hc : (pairSumForm A).coeff (pidx i 1) (pidx i 1) = (A i).2.2 := by
      rw [pairSumForm_coeff]; simp
    show PairBlockW π 0 ((pairSumForm A).coeff (pidx i 0) (pidx i 0))
      ((pairSumForm A).coeff (pidx i 0) (pidx i 1)) ((pairSumForm A).coeff (pidx i 1) (pidx i 1))
    rw [ha, hb', hc]
    refine ⟨by simp, by simp, fun h => hb i (by simpa using h.2.1), 0, (A i).2.1, by simp,
      dvr_isUnit_of_not_dvd hπ (hb i), le_rfl, ?_, ?_, by simp⟩
    · rw [zero_add, pow_one]; exact dvd_mul_of_dvd_left h2 _
    · rw [zero_add, pow_one]; exact dvd_mul_of_dvd_left h2 _

/-- **Gradient bound $0$ for `pairSumForm`** (unit middle coefficients): Lemma 3.2 holds from level 1. -/
theorem gradBound_pairSumForm {r : ℕ} (A : Fin r → R × R × R) (π : R) (hb : ∀ i, ¬ π ∣ (A i).2.1) :
    GradBound (pairSumForm A) π (pairSumPairs r) 0 0 := by
  refine ⟨fun k _ hk => absurd (isPaired_pairSumPairs k) hk, fun e he _ => ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
  have hb' : (pairSumForm A).coeff (pidx i 0) (pidx i 1) = (A i).2.1 := by
    rw [pairSumForm_coeff]; simp
  show ¬ π ^ (0 + 1) ∣ (pairSumForm A).coeff (pidx i 0) (pidx i 1)
  rw [hb', zero_add, pow_one]
  exact hb i



/-- `repCount` of `pairSumForm` mod $\pi$ is the residue-field count `pairCountF`. -/
theorem repCount_pairSumForm_one_eq [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) {π : R}
    (hπ : Irreducible π) (s : R) :
    (repCount (pairSumForm A) π 1 s : ℤ) =
      pairCountF (fun i => (res (A i).1, res (A i).2.1, res (A i).2.2)) (res s) := by
  set φ := quotPiEquivResidue hπ
  let E : (Fin (r * 2) → R ⧸ Ideal.span {π ^ 1}) ≃ (Fin r → 𝔽 × 𝔽) :=
    { toFun := fun x i => (φ (x (pidx i 0)), φ (x (pidx i 1)))
      invFun := fun y k => φ.symm (if (finProdFinEquiv.symm k).2 = 0 then (y (finProdFinEquiv.symm k).1).1
        else (y (finProdFinEquiv.symm k).1).2)
      left_inv := fun x => by
        funext k
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        fin_cases j <;> simp [pidx]
      right_inv := fun y => by
        funext i
        simp [pidx] }
  have hE : ∀ x i, E x i = (φ (x (pidx i 0)), φ (x (pidx i 1))) := fun x i => rfl
  clear_value E
  have hval : ∀ x, (pairSumForm A).evalIn _ x = Ideal.Quotient.mk _ s ↔
      ∑ i, binF (res (A i).1, res (A i).2.1, res (A i).2.2) (E x i) = res s := by
    intro x
    rw [← φ.injective.eq_iff, evalIn_pairSumForm, map_sum]
    simp only [hE, binF, map_add, map_mul, map_pow, Ideal.Quotient.algebraMap_eq]
    rfl
  unfold repCount
  have hc : Nat.card {x : Fin (r * 2) → R ⧸ Ideal.span {π ^ 1} //
      (pairSumForm A).evalIn (R ⧸ Ideal.span {π ^ 1}) x = Ideal.Quotient.mk _ s} =
      Nat.card {y : Fin r → 𝔽 × 𝔽 // ∑ i, binF (res (A i).1, res (A i).2.1, res (A i).2.2) (y i) = res s} :=
    Nat.card_congr
      { toFun := fun x => ⟨E x.1, (hval x.1).1 x.2⟩
        invFun := fun y => ⟨E.symm y.1, (hval _).2 (by rw [Equiv.apply_symm_apply]; exact y.2)⟩
        left_inv := fun x => Subtype.ext (E.symm_apply_apply _)
        right_inv := fun y => Subtype.ext (E.apply_symm_apply _) }
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  unfold pairCountF
  push_cast
  rfl

/-! ### Dyadic Table 1, Remark 3.4.1(a), Remark 3.5.1 and Table 2 for even unimodular forms -/

/-- **The Arf sign of `pairSumForm A` mod $\pi$**: $\varepsilon(A) = \prod_i \varepsilon(\bar a_i, \bar b_i, \bar c_i) \in \{\pm1\}$,
$+1$ iff the reduction of the form mod $\pi$ is hyperbolic (Arf invariant $\sum_i \bar a_i\bar c_i/\bar b_i^2 \in \wp(\mathbb{F})$).
It plays the role of $\Phi_n(\mathfrak p) = \chi((-1)^{n/2}D)$ of the non-dyadic case. -/
@[kb "hanke2004" "Φ_n(𝔭), p. 357 (dyadic analogue)"]
noncomputable def pairArf [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) : ℤ :=
  ∏ i, arfSign (res (A i).1) (res (A i).2.1) (res (A i).2.2)

theorem pairArf_sq [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) : pairArf A ^ 2 = 1 :=
  prod_arfSign_sq (F := 𝔽) fun i => (res (A i).1, res (A i).2.1, res (A i).2.2)

/-- At a dyadic prime the residue field has characteristic $2$. -/
theorem charP_residueField_two {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) : CharP 𝔽 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    rw [show (2 : 𝔽) = res 2 from (map_ofNat res 2).symm]
    exact (residue_eq_zero_iff_dvd hπ 2).2 h2)

theorem q_eq_fintype_card [Fintype 𝔽] : (q R : ℤ) = Fintype.card 𝔽 := by
  rw [q, Nat.card_eq_fintype_card]

/-- **Dyadic Table 1 for even unimodular forms** (Hanke 2004, Table 1, p. 363, which is stated for $\mathfrak p \nmid 2N$;
at $\mathfrak p \mid 2$ the paper defers to "a case-by-case basis", p. 362). Let $\pi \mid 2$ (any $e \ge 1$),
$q = \#R/\pi = 2^f$, $r \ge 1$, $Q = \bigoplus_{i<r}(a_i, b_i, c_i)$ with all $b_i$ units, and $\varepsilon = $ `pairArf A`. Then
$$r_\pi(s) = \begin{cases} q^{2r-1} + \varepsilon\,(q^r - q^{r-1}) & \pi \mid s,\\ q^{2r-1} - \varepsilon\, q^{r-1} & \pi \nmid s,\end{cases}$$
which is the $n = 2r$ row of the non-dyadic Table 1 (`DVR.card_diag_mod_pi`) with $\chi((-1)^{n/2}D)$ replaced by
$\varepsilon$. *Proof:* reduce mod $\pi$ (`repCount_pairSumForm_one_eq`) and count over $\mathbb{F}$ (`pairCountF_zero`,
`pairCountF_ne_zero`). -/
@[kb "hanke2004" "Table 1, p. 363 (dyadic, even unimodular)"]
theorem card_pairSum_mod_pi [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 1 ≤ r) (s : R) :
    (π ∣ s → (repCount (pairSumForm A) π 1 s : ℤ) =
      (q R : ℤ) ^ (2 * r - 1) + pairArf A * ((q R : ℤ) ^ r - (q R : ℤ) ^ (r - 1))) ∧
    (¬ π ∣ s → (repCount (pairSumForm A) π 1 s : ℤ) =
      (q R : ℤ) ^ (2 * r - 1) - pairArf A * (q R : ℤ) ^ (r - 1)) := by
  have := charP_residueField_two hπ h2
  have hb' : ∀ i, ((fun i => (res (A i).1, res (A i).2.1, res (A i).2.2)) i).2.1 ≠ 0 :=
    fun i h => hb i ((residue_eq_zero_iff_dvd hπ _).1 h)
  rw [repCount_pairSumForm_one_eq A hπ, q_eq_fintype_card]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [(residue_eq_zero_iff_dvd hπ s).2 hs, pairCountF_zero hr _ hb']; rfl
  · rw [pairCountF_ne_zero hr _ hb' _ (fun h => hs ((residue_eq_zero_iff_dvd hπ s).1 h))]; rfl

theorem pairSum_exp (r : ℕ) : r * 2 - 1 = 2 * r - 1 := by omega

/-- **Dyadic Remark 3.4.1(a) for even unimodular forms** (Hanke 2004, Remark 3.4.1(a), p. 361, with Lemma 3.2 from
level $1$): for $\pi \mid 2$ (any $e$), $Q = \bigoplus_{i<r}(a_i, b_i, c_i)$ with all $b_i$ units, $r \ge 1$ and $\pi \nmid m$,
$$\beta_\pi(m) = \frac{r_\pi(m)}{q^{2r-1}} = 1 - \frac{\varepsilon}{q^r},\qquad \varepsilon = \texttt{pairArf}\,A.$$
Independent of $e$. For $R = \mathbb{Z}_2$: $\beta_2(1) = 1/2$ for $xy$ and $3/2$ for $x^2 + xy + y^2$
(`localDensity_hyperbolic_two`, `localDensity_anisoPlane_two`). -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (dyadic, even unimodular)"]
theorem localDensity_unit_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 1 ≤ r) (m : R) (hm : ¬ π ∣ m) :
    localDensity (pairSumForm A) π m = 1 - (pairArf A : ℝ) / (q R : ℝ) ^ r := by
  rw [localDensity_unit_unimodular (pairSumForm A) π hπ (pairSumPairs r)
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) m hm 1 le_rfl, one_mul,
    pairSum_exp]
  have h := (card_pairSum_mod_pi A π hπ h2 hb hr m).2 hm
  have h' : (repCount (pairSumForm A) π 1 m : ℝ) =
      (q R : ℝ) ^ (2 * r - 1) - (pairArf A : ℝ) * (q R : ℝ) ^ (r - 1) := by exact_mod_cast h
  rw [h']
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (r + 1) - 1 = r + (r + 1) by omega, Nat.add_sub_cancel, pow_add]
  field_simp

/-- **Densities at $\mathrm{ord}_\pi(m) = 1$ for even unimodular forms at dyadic $\pi$**: under the hypotheses of
`localDensity_unit_pairSum`, if $\pi \mid m$ and $\pi^2 \nmid m$ then
$$\beta_\pi(m) = \frac{r_\pi(0) - 1}{q^{2r-1}} = \Bigl(1 - \frac{\varepsilon}{q^r}\Bigr)\Bigl(1 + \frac{\varepsilon}{q^{r-1}}\Bigr).$$ -/
@[kb "hanke2004" "Remark 5.4.1(b), p. 370 (dyadic, even unimodular)"]
theorem localDensity_ord_one_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R)
    (π : R) (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 1 ≤ r) (m : R)
    (hm1 : π ∣ m) (hm2 : ¬ π ^ 2 ∣ m) :
    localDensity (pairSumForm A) π m =
      (1 - (pairArf A : ℝ) / (q R : ℝ) ^ r) * (1 + (pairArf A : ℝ) / (q R : ℝ) ^ (r - 1)) := by
  rw [localDensity_ord_one_unimodular (pairSumForm A) π hπ (pairSumPairs r)
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) m hm2 1 le_rfl, one_mul,
    pairSum_exp]
  have h1 := repCount_one_eq_nonZero_add (pairSumForm A) π hπ m
  simp only [hm1, ↓reduceIte] at h1
  have h := (card_pairSum_mod_pi A π hπ h2 hb hr m).1 hm1
  have h' : (repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℝ) =
      (q R : ℝ) ^ (2 * r - 1) + (pairArf A : ℝ) * ((q R : ℝ) ^ r - (q R : ℝ) ^ (r - 1)) - 1 := by
    have : (repCount (pairSumForm A) π 1 m : ℤ) =
        repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) + 1 := by exact_mod_cast h1
    have h'' : (repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℤ) =
        (q R : ℤ) ^ (2 * r - 1) + pairArf A * ((q R : ℤ) ^ r - (q R : ℤ) ^ (r - 1)) - 1 := by
      linarith
    exact_mod_cast h''
  rw [h']
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  have hε : (pairArf A : ℝ) * (pairArf A : ℝ) = 1 := by
    have := pairArf_sq A; rw [sq] at this; exact_mod_cast this
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (r + 1) - 1 = r + (r + 1) by omega, Nat.add_sub_cancel, pow_add, pow_succ]
  rcases mul_self_eq_one_iff.1 hε with h1 | h1 <;> rw [h1] <;> field_simp <;> ring

theorem pairSum_pos_aux (q Y ε : ℤ) (hq : 2 ≤ q) (hY : 2 ≤ Y) (hε : ε = 1 ∨ ε = -1) :
    0 < Y * (Y * q) + ε * (Y * q - Y) - 1 ∧ 0 < Y * (Y * q) - ε * Y := by
  have h1 : 0 ≤ Y * (q - 1) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ Y * q * (Y - 1) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h3 : 4 ≤ Y * q := by nlinarith
  have h4 : 0 ≤ Y * (Y * q - 1) := mul_nonneg (by linarith) (by linarith)
  rcases hε with rfl | rfl <;> constructor <;> nlinarith

theorem two_le_q_of_fintype [Fintype 𝔽] : 2 ≤ q R := by
  have : 1 < Fintype.card 𝔽 := Fintype.one_lt_card
  rw [q, Nat.card_eq_fintype_card]; omega

/-- The non-Zero-type count mod $\pi$ of an even unimodular `pairSumForm` (in $\mathbb{Z}$). -/
theorem repCountOf_nonZero_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 1 ≤ r) (m : R) :
    (π ∣ m → (repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℤ) =
      (q R : ℤ) ^ (2 * r - 1) + pairArf A * ((q R : ℤ) ^ r - (q R : ℤ) ^ (r - 1)) - 1) ∧
    (¬ π ∣ m → (repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) : ℤ) =
      (q R : ℤ) ^ (2 * r - 1) - pairArf A * (q R : ℤ) ^ (r - 1)) := by
  have h1 := repCount_one_eq_nonZero_add (pairSumForm A) π hπ m
  have hc := card_pairSum_mod_pi A π hπ h2 hb hr m
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · simp only [hm, ↓reduceIte] at h1
    have := hc.1 hm
    rw [h1] at this; push_cast at this; linarith
  · simp only [hm, ↓reduceIte, add_zero] at h1
    rw [← hc.2 hm, h1]

/-- **Dyadic Remark 3.5.1 for even unimodular forms** (Hanke 2004, Remark 3.5.1, p. 362: "when $n \ge 3$ and
$\mathfrak p \nmid N$, every number $m$ is locally represented at $\mathfrak p$"): for $\pi \mid 2$ (any $e$) and
$Q = \bigoplus_{i<r}(a_i, b_i, c_i)$ with all $b_i$ units and $n = 2r \ge 4$, every $m \in R$ is locally represented
at $\pi$. *Proof:* there are $r^{\mathrm{Good}}_\pi(m) \ge (q^r - 1)(q^{r-1} - 1) > 0$ Good solutions mod $\pi$
(`repCountOf_nonZero_pairSum`), and they lift from level 1 (`repCountGood_add_of_gradBound`, $t = 0$).
For $r = 1$ this fails: $x^2 + xy + y^2$ does not represent $2$ over $\mathbb{Z}_2$. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (dyadic, even unimodular)"]
theorem isLocallyRepresentedAt_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R)
    (π : R) (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 2 ≤ r) (m : R) :
    IsLocallyRepresentedAt (pairSumForm A) π m := by
  have hq := two_le_q_of_fintype (R := R)
  have hε := pairArf_sq A
  have hε' : pairArf A = 1 ∨ pairArf A = -1 := by
    rw [sq] at hε; exact mul_self_eq_one_iff.1 hε
  have hpos : 0 < repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
    have hc := repCountOf_nonZero_pairSum A π hπ h2 hb (by omega) m
    have hQ : (2 : ℤ) ≤ q R := by exact_mod_cast hq
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    have e1 : 2 * (r + 2) - 1 = (r + 1) + (r + 2) := by omega
    have e2 : r + 2 - 1 = r + 1 := by omega
    have hY : (2 : ℤ) ≤ (q R : ℤ) ^ (r + 1) := le_trans hQ (le_self_pow₀ (by linarith) (by omega))
    have hY2 : (q R : ℤ) ^ (r + 2) = (q R : ℤ) ^ (r + 1) * q R := pow_succ _ _
    have haux := pairSum_pos_aux (q R) ((q R : ℤ) ^ (r + 1)) (pairArf A) hQ hY hε'
    by_cases hm : π ∣ m
    · have := hc.1 hm
      rw [e1, e2, pow_add, hY2] at this
      have : (0 : ℤ) < repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
        rw [this]; exact haux.1
      exact_mod_cast this
    · have := hc.2 hm
      rw [e1, e2, pow_add, hY2] at this
      have : (0 : ℤ) < repCountOf (pairSumForm A) π 1 m (fun x => ¬ IsZeroType π 1 x) := by
        rw [this]; linarith [haux.2]
      exact_mod_cast this
  rw [IsLocallyRepresentedAt, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have hG := repCountGood_add_of_gradBound (pairSumForm A) π hπ (pairSumPairs r) 0
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) m 1 l le_rfl
  rw [isGoodType_unimodularCoords_zero, isGoodType_unimodularCoords_zero] at hG
  refine lt_of_lt_of_le ?_ (repCountOf_le_repCount (pairSumForm A) π hπ (1 + l) m
    (fun x => ¬ IsZeroType π (1 + l) x))
  rw [hG]
  exact Nat.mul_pos (pow_pos q_pos _) hpos

/-- **Dyadic Table 2, $n = 2r$ even, $\pi \nmid T'$** (Hanke 2004, Table 2, p. 370, stated for $\mathfrak p \nmid N$ with
$\Phi_n$ defined only for $\mathfrak p \nmid 2N$): for $\pi \mid 2$ (any $e$), $Q = \bigoplus_{i<r}(a_i, b_i, c_i)$ with all $b_i$
units, $r \ge 2$ and $\pi \nmid T'$,
$$C_\pi(T') = \frac{q^{(n-2)/2}}{q^{(n-2)/2} - \varepsilon},\qquad \varepsilon = \texttt{pairArf}\,A,$$
the printed even-$n$ entry with $\Phi_n(\mathfrak p) := \varepsilon$ (`DVR.table2_even_unit` for $\pi \nmid 2$).
*Update (candidate generalization; pending author; `docs/updates-and-errata.md`):* Table 2 thus holds at dyadic
$\mathfrak p \nmid N$, with $\Phi_n(\mathfrak p)$ the Arf sign. -/
@[kb "hanke2004" "Table 2, p. 370 (dyadic, even unimodular)"]
theorem table2_even_unit_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 2 ≤ r) (T : R) (hT : ¬ π ∣ T) :
    localConstC (pairSumForm A) π T =
      (q R : ℝ) ^ (r - 1) / ((q R : ℝ) ^ (r - 1) - pairArf A) := by
  have hK := localDensityOf_nonZero_unimodular (pairSumForm A) π hπ (pairSumPairs r)
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) (π ^ 2 * T) 1 le_rfl
  have hc := (repCountOf_nonZero_pairSum A π hπ h2 hb (by omega) (π ^ 2 * T)).1
    (dvd_mul_of_dvd_left (dvd_pow_self π two_ne_zero) T)
  have hc' : (repCountOf (pairSumForm A) π 1 (π ^ 2 * T) (fun x => ¬ IsZeroType π 1 x) : ℝ) =
      (q R : ℝ) ^ (2 * r - 1) + (pairArf A : ℝ) * ((q R : ℝ) ^ r - (q R : ℝ) ^ (r - 1)) - 1 := by
    exact_mod_cast hc
  have hβ := localDensity_unit_pairSum A π hπ h2 hb (by omega) T hT
  have hQ : (2 : ℝ) ≤ q R := by exact_mod_cast two_le_q_of_fintype (R := R)
  have hε : (pairArf A : ℝ) * (pairArf A : ℝ) = 1 := by
    have := pairArf_sq A; rw [sq] at this; exact_mod_cast this
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  set Y := (q R : ℝ) ^ (r + 1) with hYdef
  have p1 : (q R : ℝ) ^ (1 * ((r + 2) * 2 - 1)) = Y * (Y * q R) := by
    rw [hYdef, ← pow_succ, ← pow_add]; congr 1; omega
  have p2 : (q R : ℝ) ^ (2 * (r + 2) - 1) = Y * (Y * q R) := by
    rw [hYdef, ← pow_succ, ← pow_add]; congr 1; omega
  have p3 : (q R : ℝ) ^ (r + 2) = Y * q R := by rw [hYdef, ← pow_succ]
  have p4 : (q R : ℝ) ^ (r + 2 - 1) = Y := by rw [hYdef]; congr 1
  have p5 : (q R : ℝ) ^ ((r + 2) * 2 - 2) = Y * Y := by rw [hYdef, ← pow_add]; congr 1; omega
  rw [hc', p2, p3, p4, p1] at hK
  rw [p3] at hβ
  unfold localConstC
  rw [hK, hβ, p5, p4]
  have hY : 2 ≤ Y := le_trans hQ (le_self_pow₀ (by linarith) (by omega))
  have h1 : Y - 1 ≠ 0 := by linarith
  have h2' : Y + 1 ≠ 0 := by linarith
  have h3 : Y * Y - 1 ≠ 0 := by nlinarith
  have h4 : Y * (q R : ℝ) - 1 ≠ 0 := by nlinarith
  have h5 : Y * (q R : ℝ) + 1 ≠ 0 := by nlinarith
  have hq0 : (q R : ℝ) ≠ 0 := by linarith
  have hY0 : Y ≠ 0 := by linarith
  have hYq : Y * q R ≠ 0 := mul_ne_zero hY0 hq0
  rcases mul_self_eq_one_iff.1 hε with h | h <;> rw [h]
  · rw [show Y * (Y * q R) + 1 * (Y * q R - Y) - 1 = (Y * q R - 1) * (Y + 1) by ring,
      show Y * Y - 1 = (Y - 1) * (Y + 1) by ring]
    field_simp
  · have h5' : 1 + Y * q R ≠ 0 := by rw [add_comm]; exact h5
    rw [show Y * (Y * q R) + -1 * (Y * q R - Y) - 1 = (Y * q R + 1) * (Y - 1) by ring,
      show Y * Y - 1 = (Y - 1) * (Y + 1) by ring, sub_neg_eq_add]
    field_simp
    rw [sub_neg_eq_add, div_self h5]

/-- **Dyadic Table 2, $\mathrm{ord}_\pi(T') = 1$** (Hanke 2004, Table 2, p. 370; (5.9)): under the hypotheses of
`table2_even_unit_pairSum` with $\pi \mid T'$, $\pi^2 \nmid T'$: $C_\pi(T') = \dfrac{q^{n-2}}{q^{n-2} - 1}$, as printed. -/
@[kb "hanke2004" "Table 2, p. 370; (5.9) (dyadic, even unimodular)"]
theorem table2_ord_one_pairSum [Fintype 𝔽] [DecidableEq 𝔽] {r : ℕ} (A : Fin r → R × R × R) (π : R)
    (hπ : Irreducible π) (h2 : π ∣ 2) (hb : ∀ i, ¬ π ∣ (A i).2.1) (hr : 2 ≤ r) (T : R) (hT1 : π ∣ T)
    (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC (pairSumForm A) π T = (q R : ℝ) ^ (r * 2 - 2) / ((q R : ℝ) ^ (r * 2 - 2) - 1) := by
  have hK := localDensityOf_nonZero_unimodular (pairSumForm A) π hπ (pairSumPairs r)
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) (π ^ 2 * T) 1 le_rfl
  have hB := localDensity_ord_one_unimodular (pairSumForm A) π hπ (pairSumPairs r)
    (isJordanFormW_pairSumForm A hπ h2 hb) 0 (gradBound_pairSumForm A π hb) T hT2 1 le_rfl
  have hcong : Ideal.Quotient.mk (Ideal.span {π ^ 1}) (π ^ 2 * T) = Ideal.Quotient.mk _ T := by
    rw [(mk_pow_one_eq_zero_iff π _).2 (dvd_mul_of_dvd_left (dvd_pow_self π two_ne_zero) T),
      ((mk_pow_one_eq_zero_iff π T).2 hT1)]
  rw [repCountOf_congr _ π 1 hcong] at hK
  have hpos : 0 < repCountOf (pairSumForm A) π 1 T (fun x => ¬ IsZeroType π 1 x) := by
    have hc := (repCountOf_nonZero_pairSum A π hπ h2 hb (by omega) T).1 hT1
    have hQ : (2 : ℤ) ≤ q R := by exact_mod_cast two_le_q_of_fintype (R := R)
    have hε' : pairArf A = 1 ∨ pairArf A = -1 := by
      have hε := pairArf_sq A; rw [sq] at hε; exact mul_self_eq_one_iff.1 hε
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    rw [show 2 * (r + 2) - 1 = (r + 1) + (r + 2) by omega, show r + 2 - 1 = r + 1 by omega, pow_add,
      pow_succ _ (r + 1)] at hc
    have hY : (2 : ℤ) ≤ (q R : ℤ) ^ (r + 1) := le_trans hQ (le_self_pow₀ (by linarith) (by omega))
    have haux := pairSum_pos_aux (q R) ((q R : ℤ) ^ (r + 1)) (pairArf A) hQ hY hε'
    have : (0 : ℤ) < repCountOf (pairSumForm A) π 1 T (fun x => ¬ IsZeroType π 1 x) := by
      rw [hc]; exact haux.1
    exact_mod_cast this
  have hne : (repCountOf (pairSumForm A) π 1 T (fun x => ¬ IsZeroType π 1 x) : ℝ) /
      (q R : ℝ) ^ (1 * (r * 2 - 1)) ≠ 0 :=
    div_ne_zero (by exact_mod_cast hpos.ne') (pow_ne_zero _ (by exact_mod_cast (q_pos (R := R)).ne'))
  unfold localConstC
  rw [hK, hB, div_self hne, mul_one]

end Dyadic

end QuadFormsKB.LocalDensity.DVR
