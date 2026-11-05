import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Primitive
import QuadFormsKB.Binary.FormsIdeals

/-!
# Saha–Hanke: the first three strongly primitive values of a reduced form

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §3–§4: the
successive minima of a reduced form on strongly primitive vectors.

Let $f = a x^2 + b x y + c y^2$ be reduced ($0 \le b \le a \le c$, $a > 0$) and put
$d = a + c - b$. The strongly primitive vectors $(1, 0)$, $(0, 1)$, $(-1, 1)$, $(1, 1)$ have values
$a \le c \le d \le a + b + c$, and every other strongly primitive vector has value $> d$
(`value_gt_of_not_special`). Consequently, for $m < d$,
$r^{\tilde *}_f(m) = [a = m] + [c = m]$ (`spRepNum_lt`), and $r^{\tilde *}_f(m) \ge [a = m] +
[c = m] + [d = m]$ for all $m$ (`spRepNum_ge`). The partial sums
$N_f(t) = \sum_{m \le t} r^{\tilde *}_f(m)$ therefore determine $a$, $c$ and $d$, hence $f$
(`eq_of_spRepNum_eq`); and $r^{\tilde *}_f(m) \ge 4$ forces $m > d$ (`lt_of_four_le`; this is the
content of the zero-cone computations in the proof of Lemma 6.4, Cases 2a–2c).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

variable {f : BinQF}

/-- The third value $d = a + c - b$ of a form, the value at $(-1, 1)$. -/
def dval (f : BinQF) : ℤ := f.a + f.c - f.b

lemma eval_10 (f : BinQF) : f.eval 1 0 = f.a := by simp [BinQF.eval_eq]
lemma eval_01 (f : BinQF) : f.eval 0 1 = f.c := by simp [BinQF.eval_eq]
lemma eval_m11 (f : BinQF) : f.eval (-1) 1 = dval f := by simp [BinQF.eval_eq, dval]; ring
lemma eval_11 (f : BinQF) : f.eval 1 1 = f.a + f.b + f.c := by simp [BinQF.eval_eq]

/-- A reduced form is positive definite. -/
lemma IsReduced.posDef (hf : IsReduced f) : IntQF.PosDef f := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have e : QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 := by
    have := BinQF.eval_eq f (x 0) (x 1)
    have hx2 : (![x 0, x 1] : Fin 2 → ℤ) = x := by funext i; fin_cases i <;> rfl
    rw [BinQF.eval, hx2] at this; exact this
  rw [e]
  have key : 4 * f.a * (f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2) =
      (2 * f.a * x 0 + f.b * x 1) ^ 2 + (4 * f.a * f.c - f.b ^ 2) * x 1 ^ 2 := by ring
  have hdisc : 0 < 4 * f.a * f.c - f.b ^ 2 := by nlinarith
  rcases hx' with h | h
  · by_cases h1' : x 1 = 0
    · rw [h1']; simp; positivity
    · have : 0 < (4 * f.a * f.c - f.b ^ 2) * x 1 ^ 2 := by positivity
      have : 0 < 4 * f.a * (f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2) := by
        rw [key]; positivity
      nlinarith
  · have : 0 < (4 * f.a * f.c - f.b ^ 2) * x 1 ^ 2 := by positivity
    have : 0 < 4 * f.a * (f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2) := by
      rw [key]; positivity
    nlinarith

/-- The four special strongly primitive vectors. -/
lemma sp_10 : StronglyPrimitive (1, 0) := by simp [StronglyPrimitive]
lemma sp_01 : StronglyPrimitive (0, 1) := by simp [StronglyPrimitive]
lemma sp_m11 : StronglyPrimitive (-1, 1) := by simp [StronglyPrimitive]

/-- **Reduced forms: non-special strongly primitive vectors have value $> d = a + c - b$.**
If $f$ is reduced and $v$ is strongly primitive with $v \notin \{(1,0), (0,1), (-1,1), (1,1)\}$,
then $f(v) > a + c - b$. -/
theorem value_gt_of_not_special (hf : IsReduced f) {v : ℤ × ℤ} (hv : StronglyPrimitive v)
    (h10 : v ≠ (1, 0)) (h01 : v ≠ (0, 1)) (hm11 : v ≠ (-1, 1)) (h11 : v ≠ (1, 1)) :
    dval f < f.eval v.1 v.2 := by
  obtain ⟨hb0, hba, hac, ha⟩ := hf
  obtain ⟨x, y⟩ := v
  obtain ⟨hg, hpos⟩ := hv
  simp only at hg hpos
  rw [BinQF.eval_eq, dval]
  rcases hpos with hy | ⟨hy, hx⟩
  · rcases eq_or_lt_of_le (show 1 ≤ y by omega) with hy1 | hy2
    · subst hy1
      have hx : x ≠ 0 ∧ x ≠ -1 ∧ x ≠ 1 := ⟨fun h => h01 (by rw [h]), fun h => hm11 (by rw [h]),
        fun h => h11 (by rw [h])⟩
      have hx2 : 2 ≤ |x| := by
        rcases le_or_gt 0 x with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      simp only
      have hxx : 2 * |x| ≤ x ^ 2 := by nlinarith [sq_abs x]
      have hbx : -(f.b * |x|) ≤ f.b * x := by nlinarith [neg_abs_le x]
      have h1 : f.a * (2 * |x|) ≤ f.a * x ^ 2 := by nlinarith
      nlinarith
    · have hy2' : 2 ≤ y := hy2
      have key : 4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) =
          (2 * f.a * x + f.b * y) ^ 2 + (4 * f.a * f.c - f.b ^ 2) * y ^ 2 := by ring
      have hdisc : 3 * f.a * f.c ≤ 4 * f.a * f.c - f.b ^ 2 := by nlinarith
      have hy4 : 4 ≤ y ^ 2 := by nlinarith
      have h1 : 4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) ≥ 12 * f.a * f.c := by
        rw [key]; nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]
      have h2 : 12 * f.a * f.c > 4 * f.a * (f.a + f.c - f.b) := by nlinarith
      nlinarith
  · subst hy
    have : x = 1 := by
      simp at hg; omega
    subst this; exact absurd rfl h10

/-- For $m < d$: $r^{\tilde *}_f(m) = [a = m] + [c = m]$. -/
theorem spRepNum_lt (hf : IsReduced f) {m : ℤ} (hm : m < dval f) :
    spRepNum f m = (if f.a = m then 1 else 0) + (if f.c = m then 1 else 0) := by
  classical
  have hT : ∀ v : ℤ × ℤ, (StronglyPrimitive v ∧ f.eval v.1 v.2 = m) ↔
      (v ∈ ({(1, 0), (0, 1)} : Finset (ℤ × ℤ)) ∧ f.eval v.1 v.2 = m) := by
    intro v
    constructor
    · rintro ⟨hv, hvm⟩
      refine ⟨?_, hvm⟩
      by_contra hmem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
      have hm11 : v ≠ (-1, 1) := by
        rintro rfl; rw [eval_m11] at hvm; omega
      have h11 : v ≠ (1, 1) := by
        rintro rfl; rw [eval_11] at hvm
        obtain ⟨hb0, _, _, _⟩ := hf; simp only [dval] at hm; omega
      have := value_gt_of_not_special hf hv hmem.1 hmem.2 hm11 h11
      omega
    · rintro ⟨hv, hvm⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨sp_10, hvm⟩
      · exact ⟨sp_01, hvm⟩
  rw [spRepNum, Nat.card_congr (Equiv.subtypeEquivRight hT)]
  rw [show (Nat.card {v : ℤ × ℤ // v ∈ ({(1, 0), (0, 1)} : Finset (ℤ × ℤ)) ∧
      f.eval v.1 v.2 = m}) = (({(1, 0), (0, 1)} : Finset (ℤ × ℤ)).filter
        (fun v => f.eval v.1 v.2 = m)).card by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp [Finset.mem_filter])]
  rw [Finset.filter_insert, Finset.filter_singleton, eval_10, eval_01]
  split_ifs <;> simp_all

/-- For all $m$: $r^{\tilde *}_f(m) \ge [a = m] + [c = m] + [d = m]$ (the vectors $(1,0)$, $(0,1)$,
$(-1,1)$ are distinct and strongly primitive). -/
theorem spRepNum_ge (hf : IsReduced f) (m : ℤ) :
    (if f.a = m then 1 else 0) + (if f.c = m then 1 else 0) + (if dval f = m then 1 else 0) ≤
      spRepNum f m := by
  classical
  have hfin := finite_sp f hf.posDef m
  let T : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 1)}
  have hinj : Function.Injective (fun v : (T.filter (fun v => f.eval v.1 v.2 = m)) =>
      (⟨v.1, by
        have h := v.2
        simp only [T, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
        obtain ⟨h1, h2⟩ := h
        refine ⟨?_, h2⟩
        rcases h1 with h | h | h <;> rw [h]
        exacts [sp_10, sp_01, sp_m11]⟩ :
        {v : ℤ × ℤ // StronglyPrimitive v ∧ f.eval v.1 v.2 = m})) := by
    intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at this
  refine le_trans (le_of_eq ?_) this
  simp only [T, Finset.filter_insert, Finset.filter_singleton, eval_10, eval_01, eval_m11]
  split_ifs <;> simp_all


/-- The partial sums $N_f(t) = \sum_{0 \le m \le t} r^{\tilde *}_f(m)$. -/
noncomputable def spCount (f : BinQF) (t : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (t + 1), spRepNum f m

lemma sum_ind (z : ℤ) (hz : 0 ≤ z) (t : ℕ) :
    ∑ m ∈ Finset.range (t + 1), (if z = (m : ℤ) then 1 else 0 : ℕ) = if z ≤ t then 1 else 0 := by
  lift z to ℕ using hz
  simp only [Nat.cast_inj, Nat.cast_le]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma dval_ge (hf : IsReduced f) : f.c ≤ dval f := by
  obtain ⟨_, h, _, _⟩ := hf; simp only [dval]; omega

lemma spCount_ge (hf : IsReduced f) (t : ℕ) :
    (if f.a ≤ t then 1 else 0) + (if f.c ≤ t then 1 else 0) + (if dval f ≤ t then 1 else 0) ≤
      spCount f t := by
  obtain ⟨h0, h1, h2, h3⟩ := hf
  have hd := dval_ge ⟨h0, h1, h2, h3⟩
  rw [← sum_ind f.a h3.le, ← sum_ind f.c (by omega), ← sum_ind (dval f) (by omega),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, spCount]
  exact Finset.sum_le_sum fun m _ => spRepNum_ge ⟨h0, h1, h2, h3⟩ m

lemma spCount_lt (hf : IsReduced f) {t : ℕ} (ht : (t : ℤ) < dval f) :
    spCount f t = (if f.a ≤ t then 1 else 0) + (if f.c ≤ t then 1 else 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := hf
  rw [← sum_ind f.a h3.le, ← sum_ind f.c (by omega), ← Finset.sum_add_distrib, spCount]
  refine Finset.sum_congr rfl fun m hm => ?_
  apply spRepNum_lt ⟨h0, h1, h2, h3⟩
  have : m ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have : (m : ℤ) ≤ t := by exact_mod_cast this
  omega

/-- If $N_f(t) \le N_g(t)$ for all $t < M$ and $d_f < M$, then $a_g \le a_f$, $c_g \le c_f$ and
$d_g \le d_f$. -/
lemma le_of_spCount_le {g : BinQF} (hf : IsReduced f) (hg : IsReduced g) {M : ℕ}
    (hfM : dval f < M) (h : ∀ t : ℕ, t < M → spCount f t ≤ spCount g t) :
    g.a ≤ f.a ∧ g.c ≤ f.c ∧ dval g ≤ dval f := by
  have hdf := dval_ge hf
  have hdg := dval_ge hg
  obtain ⟨f0, f1, f2, f3⟩ := hf
  obtain ⟨g0, g1, g2, g3⟩ := hg
  have key : ∀ t : ℕ, (t : ℤ) ≤ dval f →
      (if f.a ≤ t then 1 else 0) + (if f.c ≤ t then 1 else 0) + (if dval f ≤ t then 1 else 0) ≤
        spCount g t := fun t ht =>
    (spCount_ge ⟨f0, f1, f2, f3⟩ t).trans (h t (by omega))
  refine ⟨?_, ?_, ?_⟩
  · by_contra hlt; push Not at hlt
    lift f.a to ℕ using f3.le with A hA
    have := key A (by omega)
    rw [spCount_lt ⟨g0, g1, g2, g3⟩ (by omega)] at this
    split_ifs at this <;> omega
  · by_contra hlt; push Not at hlt
    have hc : 0 ≤ f.c := by omega
    lift f.c to ℕ using hc with C hC
    have := key C (by omega)
    rw [spCount_lt ⟨g0, g1, g2, g3⟩ (by omega)] at this
    split_ifs at this <;> omega
  · by_contra hlt; push Not at hlt
    have hd : 0 ≤ dval f := by omega
    lift dval f to ℕ using hd with D hD
    have := key D le_rfl
    rw [spCount_lt ⟨g0, g1, g2, g3⟩ (by omega)] at this
    split_ifs at this <;> omega

/-- **Determination by the first strongly primitive values.** If $f, g$ are reduced,
$d_f, d_g < M$, and $r^{\tilde *}_f(m) = r^{\tilde *}_g(m)$ for all $0 \le m < M$, then $f = g$. -/
theorem eq_of_spRepNum_eq {g : BinQF} (hf : IsReduced f) (hg : IsReduced g) {M : ℕ}
    (hfM : dval f < M) (hgM : dval g < M)
    (h : ∀ m : ℕ, m < M → spRepNum f m = spRepNum g m) : f = g := by
  have hc : ∀ t : ℕ, t < M → spCount f t = spCount g t := by
    intro t ht
    refine Finset.sum_congr rfl fun m hm => h m ?_
    have := Finset.mem_range.1 hm; omega
  obtain ⟨a1, c1, d1⟩ := le_of_spCount_le hf hg hfM fun t ht => (hc t ht).le
  obtain ⟨a2, c2, d2⟩ := le_of_spCount_le hg hf hgM fun t ht => (hc t ht).ge
  simp only [dval] at d1 d2
  exact BinQF.ext_abc (by omega) (by omega) (by omega)

/-- **Four strongly primitive representations force $m > d$.** If $f$ is reduced and
$r^{\tilde *}_f(m) \ge 4$, then $m > a + c - b$. (For $m \le d$ the strongly primitive
representations lie among $(1,0), (0,1), (-1,1), (1,1)$, whose values cannot all be equal.) -/
theorem lt_of_four_le (hf : IsReduced f) {m : ℤ} (h4 : 4 ≤ spRepNum f m) : dval f < m := by
  classical
  by_contra hle; push Not at hle
  let S : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 1), (1, 1)}
  have hS : S.card = 4 := by decide
  have hsub : ∀ v : ℤ × ℤ, StronglyPrimitive v → f.eval v.1 v.2 = m → v ∈ S := by
    intro v hv hvm
    by_contra hmem
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    have := value_gt_of_not_special hf hv hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
    omega
  have hfin : Finite (S.filter fun v => f.eval v.1 v.2 = m) := inferInstance
  have hinj : Function.Injective (fun v : {v : ℤ × ℤ // StronglyPrimitive v ∧ f.eval v.1 v.2 = m} =>
      (⟨v.1, Finset.mem_filter.2 ⟨hsub v.1 v.2.1 v.2.2, v.2.2⟩⟩ :
        (S.filter fun v => f.eval v.1 v.2 = m))) := by
    intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have hle' := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at hle'
  have hcard : (S.filter fun v => f.eval v.1 v.2 = m).card = S.card := by
    have := Finset.card_filter_le S (fun v => f.eval v.1 v.2 = m)
    rw [spRepNum] at h4; omega
  have hall := Finset.filter_card_eq hcard
  have e1 := hall (1, 0) (by simp [S])
  have e2 := hall (0, 1) (by simp [S])
  have e3 := hall (-1, 1) (by simp [S])
  have e4 := hall (1, 1) (by simp [S])
  simp only [eval_10, eval_01, eval_m11, eval_11, dval] at e1 e2 e3 e4
  obtain ⟨_, _, _, ha⟩ := hf
  omega

end QuadFormsKB.Hanke2023ThreeTerm
