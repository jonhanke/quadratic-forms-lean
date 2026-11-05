/-
# Conway–Sloane, Ch. 15, §3 and §10.1: further items on binary forms and Minkowski reduction

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15
(`conwaysloane1999`; printed page = PDF page of the chapter file + 351). Built on `Binary.lean` (`BinForm`, `stepPair`,
`sequenceOf`, `cycleSet`, `IsReducedIndef`), `Table152.lean` (`variants`) and `Examples.lean`.

**Proved.**
* (9), (10), p. 357: `definite_cycle`: the sequence of a positive definite form is ultimately periodic, with a cycle
  that is a single form $a^{b}a$ ($b = 0$ or $2b = \lvert a\rvert$) or a pair $\{a^{b}c,\ c^{-b}a\}$.
* §3.3, p. 359: extended reduced forms `IsExtReduced`, the modified rule `nextFormLe` (≤ in (7)), the finite chain
  `sqChain`; the square rows $d = -B^2$ ($B \le 10$) of Table 15.2 (`table152sq_a_correct`, `table152sq_b_correct`).
* §3.4, pp. 365–366: determinant $-7$: the cycles, the ideal square in $\mathbb{Z}[\sqrt 7]$ (`det7_ideal_square`),
  principal class, non-equivalence of the classes (`det7_cycles`, `det7_square_cycle`, `det7_principal`,
  `det7_not_equiv`).
* §10.1, (ii), p. 396: `minkowski_ineq` (one-sided; the printed absolute value is too strong for $\lvert S\rvert \ge 2$).

**Stated here, proved in `Section3Det7.lean`.** `Det7ClassesStatement` (every form of determinant $-7$ is in one of the
two classes; `det7_classes`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Binary
import QuadFormsKB.Literature.ConwaySloane.Examples
import QuadFormsKB.Literature.ConwaySloane.Table152

namespace QuadFormsKB

namespace ConwaySloane

namespace Binary

open scoped Pointwise

/-! ### (9), (10): cycles of definite forms -/

theorem not_isSquare_neg_of_pos {d : ℤ} (hd : 0 < d) : ¬ IsSquare (-d) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

theorem stepB_pos_eq {d b m : ℤ} (hd : 0 < d) (hm : 0 < m) : stepB b m d = smallSol b m := by
  simp [stepB, not_lt.2 hd.le, Int.natAbs_of_nonneg hm.le]

theorem smallSol_range {n : ℤ} (b : ℤ) (hn : 0 < n) :
    -n < 2 * smallSol b n ∧ 2 * smallSol b n ≤ n := by
  have h1 := Int.emod_nonneg (-b) hn.ne'
  have h2 := Int.emod_lt_of_pos (-b) hn
  unfold smallSol
  split_ifs <;> omega

theorem step_pos_facts {d : ℤ} (hd : 0 < d) {p : ℤ × ℤ} (hp : 0 < p.1) (hI : StepInv d p) :
    0 < (stepPair d p).1 ∧ -(stepPair d p).1 < 2 * (stepPair d p).2 ∧
      2 * (stepPair d p).2 ≤ (stepPair d p).1 := by
  have h1 := stepPair_fst_mul hI.2
  have hc : 0 < (stepPair d p).1 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg p.2]
  refine ⟨hc, ?_⟩
  rw [stepPair_snd, stepB_pos_eq hd hc]
  exact smallSol_range _ hc

theorem stable_step {d : ℤ} (hd : 0 < d) {p : ℤ × ℤ} (hI : StepInv d p) (ha : 0 < p.1)
    (h1 : -p.1 < 2 * p.2) (h2 : 2 * p.2 ≤ p.1) (hac : p.1 ≤ (stepPair d p).1) :
    (stepPair d p).2 = (if 2 * p.2 = p.1 ∧ p.1 = (stepPair d p).1 then p.2 else -p.2) ∧
      stepPair d (stepPair d p) = p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, b', hq⟩ : ∃ c b', stepPair d (a, b) = (c, b') := ⟨_, _, rfl⟩
  have hfst := stepPair_fst_mul hI.2
  have hsnd := stepPair_snd d (a, b)
  have hpos := step_pos_facts hd ha hI
  have hqI := hI.step (not_isSquare_neg_of_pos hd)
  rw [hq] at hfst hsnd hpos hqI hac
  rw [hq]
  simp only at hfst hsnd hpos hqI hac h1 h2 ha ⊢
  obtain ⟨hc, hb1, hb2⟩ := hpos
  have hB := isStepB_stepB (d := d) (b := b) (m := c) hc.ne'
  rw [← hsnd] at hB
  obtain ⟨hdvd, -, hmin⟩ := hB
  have hno : ¬ ∃ y, c ∣ b + y ∧ y ^ 2 + d < 0 := by
    rintro ⟨y, -, hy⟩
    nlinarith [sq_nonneg y]
  replace hmin := hmin hno
  clear hno
  obtain ⟨k, hk⟩ := hdvd
  have hm1 := hmin (-b) ⟨0, by ring⟩
  simp only [Int.natAbs_neg] at hm1
  have hkb : -c ≤ c * k ∧ c * k ≤ c := by omega
  have hk1 : k ≤ 1 := by
    by_contra h; push_neg at h; nlinarith
  have hk2 : -1 ≤ k := by
    by_contra h; push_neg at h; nlinarith
  have key : b' = (if 2 * b = a ∧ a = c then b else -b) := by
    by_cases hex : 2 * b = a ∧ a = c
    · rw [if_pos hex]
      have hm2 := hmin b ⟨1, by omega⟩
      obtain rfl | rfl | rfl : k = -1 ∨ k = 0 ∨ k = 1 := by omega
      · omega
      · omega
      · omega
    · rw [if_neg hex]
      have hex := not_and_or.1 hex
      obtain rfl | rfl | rfl : k = -1 ∨ k = 0 ∨ k = 1 := by omega
      · omega
      · omega
      · omega
  refine ⟨key, ?_⟩
  have hb2 : b' ^ 2 = b ^ 2 := by
    rw [key]; split_ifs <;> ring
  have hdiv : (b' ^ 2 + d) / c = a := by
    apply Int.ediv_eq_of_eq_mul_left hc.ne'
    rw [hb2]; linarith
  have hst : stepPair d (c, b') = (a, stepB b' a d) := by
    simp only [stepPair, hdiv]
  rw [hst]
  have hB2 := isStepB_stepB (d := d) (b := b') (m := a) ha.ne'
  obtain ⟨hdvd2, -, hmin2⟩ := hB2
  have hno2 : ¬ ∃ y, a ∣ b' + y ∧ y ^ 2 + d < 0 := by
    rintro ⟨y, -, hy⟩
    nlinarith [sq_nonneg y]
  replace hmin2 := hmin2 hno2
  clear hno2
  obtain ⟨m, hm⟩ := hdvd2
  generalize stepB b' a d = b'' at hm hmin2 ⊢
  have : b'' = b := by
    by_cases hex : 2 * b = a ∧ a = c
    · rw [if_pos hex] at key
      subst key
      have hm1 := hmin2 (-b') ⟨0, by ring⟩
      have hm2 := hmin2 b' ⟨1, by omega⟩
      simp only [Int.natAbs_neg] at hm1
      clear hmin2
      have hm0 : 0 ≤ a * m ∧ a * m ≤ a := by omega
      have hmu : m ≤ 1 := by by_contra h; push_neg at h; nlinarith
      have hml : 0 ≤ m := by by_contra h; push_neg at h; nlinarith
      obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · omega
      · omega
    · rw [if_neg hex] at key
      have hex := not_and_or.1 hex
      subst key
      have hm1 := hmin2 b ⟨0, by ring⟩
      clear hmin2
      have hm0 : -a ≤ a * m ∧ a * m ≤ a := by omega
      have hmu : m ≤ 1 := by by_contra h; push_neg at h; nlinarith
      have hml : -1 ≤ m := by by_contra h; push_neg at h; nlinarith
      obtain rfl | rfl | rfl : m = -1 ∨ m = 0 ∨ m = 1 := by omega
      · omega
      · omega
      · omega
  rw [this]

/-- **Cycles of definite forms** ((9), (10), Ch. 15, §3.2, p. 357), for a positive definite form
$f = a^{b}c$ (`0 < f.a`, `0 < f.det`; then $-d$ is not a square, so Theorem 1's rules (5)–(7) apply): the sequence
(5) of `f` (`sequenceOf`) is ultimately periodic (`UltimatelyPeriodic`), and its cycle (`cycleSet`: the forms
occurring infinitely often) is either a single form $a^{b}a$ with $b = 0$ or $2b = |a|$ (the book's (9): the left
disjunct; the fields `a`, `b` are the entries of the form), or else a pair of two distinct forms
$\{a^{b}c,\ c^{-b}a\}$ (the book's (10): the right disjunct, with entries `a`, `b`, `c`). Proved from the
step rules; the book states this as an immediate consequence of Theorem 1. -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (9), (10), p. 357"]
theorem definite_cycle (f : BinForm) (ha : 0 < f.a) (hd : 0 < f.det) :
    UltimatelyPeriodic (sequenceOf f) ∧
    ((∃ a b : ℤ, cycleSet f = {⟨a, b, a⟩} ∧ (b = 0 ∨ 2 * b = |a|)) ∨
     (∃ a b c : ℤ, (⟨a, b, c⟩ : BinForm) ≠ ⟨c, -b, a⟩ ∧ cycleSet f = {⟨a, b, c⟩, ⟨c, -b, a⟩})) := by
  have hI0 : StepInv f.det (f.a, f.b) := BinForm.stepInv (not_isSquare_neg_of_pos hd)
  have hpos : ∀ n, 0 < (pairSeq f.det (f.a, f.b) n).1 ∧ StepInv f.det (pairSeq f.det (f.a, f.b) n) := by
    intro n
    induction n with
    | zero => exact ⟨ha, hI0⟩
    | succ n ih =>
      rw [pairSeq_succ]
      exact ⟨(step_pos_facts hd ih.1 ih.2).1, ih.2.step (not_isSquare_neg_of_pos hd)⟩
  have hrange : ∀ n, -(pairSeq f.det (f.a, f.b) (n + 1)).1 < 2 * (pairSeq f.det (f.a, f.b) (n + 1)).2 ∧
      2 * (pairSeq f.det (f.a, f.b) (n + 1)).2 ≤ (pairSeq f.det (f.a, f.b) (n + 1)).1 := by
    intro n
    rw [pairSeq_succ]
    exact (step_pos_facts hd (hpos n).1 (hpos n).2).2
  have hex : ∃ j : ℕ, (pairSeq f.det (f.a, f.b) (j + 1)).1 ≤ (pairSeq f.det (f.a, f.b) (j + 1 + 1)).1 := by
    by_contra h
    push_neg at h
    have hk : ∀ k : ℕ, (pairSeq f.det (f.a, f.b) (1 + k)).1 + k ≤ (pairSeq f.det (f.a, f.b) 1).1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := h k
        have e : 1 + (k + 1) = k + 1 + 1 := by ring
        rw [e]
        push_cast
        have e2 : 1 + k = k + 1 := by ring
        rw [e2] at ih
        omega
    have h1 := hk (pairSeq f.det (f.a, f.b) 1).1.toNat
    have h2 := (hpos (1 + (pairSeq f.det (f.a, f.b) 1).1.toNat)).1
    have h3 := (hpos 1).1
    omega
  obtain ⟨j, hj⟩ := hex
  obtain ⟨hr1, hr2⟩ := hrange j
  have hI := (hpos (j + 1)).2
  have hsucc : pairSeq f.det (f.a, f.b) (j + 1 + 1) = stepPair f.det (pairSeq f.det (f.a, f.b) (j + 1)) :=
    pairSeq_succ _ _ _
  rw [hsucc] at hj
  obtain ⟨hb', hss⟩ := stable_step hd hI (hpos (j + 1)).1 hr1 hr2 hj
  have hss' : pairSeq f.det (f.a, f.b) (j + 1 + 2) = pairSeq f.det (f.a, f.b) (j + 1) := by
    rw [show j + 1 + 2 = (j + 1 + 1) + 1 from rfl, pairSeq_succ, hsucc, pairSeq_succ] at *
    rw [pairSeq_succ, hss]
  refine ⟨⟨j + 1, 2, by norm_num, periodic_of_pairSeq hss'⟩, ?_⟩
  have hcyc : cycleSet f = {x | x ∈ [sequenceOf f (j + 1), sequenceOf f (j + 1 + 1)]} :=
    cycleSet_eq_of_list (N := j + 1) (P := 2) (by norm_num) hss' (by simp [List.range_succ])
  have hf1 : sequenceOf f (j + 1) = ⟨(pairSeq f.det (f.a, f.b) (j + 1)).1, (pairSeq f.det (f.a, f.b) (j + 1)).2,
      (stepPair f.det (pairSeq f.det (f.a, f.b) (j + 1))).1⟩ := rfl
  have hf2 : sequenceOf f (j + 1 + 1) = ⟨(stepPair f.det (pairSeq f.det (f.a, f.b) (j + 1))).1,
      (stepPair f.det (pairSeq f.det (f.a, f.b) (j + 1))).2, (pairSeq f.det (f.a, f.b) (j + 1)).1⟩ := by
    show formAt f.det (pairSeq f.det (f.a, f.b) (j + 1 + 1)) = _
    rw [hsucc]
    simp only [formAt, hss]
  have hapos := (hpos (j + 1)).1
  rw [hf1, hf2] at hcyc
  generalize pairSeq f.det (f.a, f.b) (j + 1) = P at hb' hss hcyc hapos
  obtain ⟨a, b⟩ := P
  obtain ⟨c, b', hq⟩ : ∃ c b', stepPair f.det (a, b) = (c, b') := ⟨_, _, rfl⟩
  rw [hq] at hb' hcyc
  simp only at hb' hcyc hapos
  by_cases hex : 2 * b = a ∧ a = c
  · rw [if_pos hex] at hb'
    rw [hb'] at hcyc
    obtain ⟨h1, h2⟩ := hex
    subst h2
    left
    refine ⟨a, b, ?_, Or.inr (by rw [abs_of_pos hapos]; exact h1)⟩
    rw [hcyc]
    ext x
    simp
  · rw [if_neg hex] at hb'
    rw [hb'] at hcyc
    by_cases heq : (⟨a, b, c⟩ : BinForm) = ⟨c, -b, a⟩
    · injection heq with e1 e2 e3
      obtain rfl : b = 0 := by omega
      subst e1
      left
      refine ⟨a, 0, ?_, Or.inl rfl⟩
      rw [hcyc]
      ext x
      simp
    · right
      refine ⟨a, b, c, heq, ?_⟩
      rw [hcyc]
      ext x
      simp

/-! ### §3.3: square determinants, extended reduced forms (p. 359), Table 15.2 for $d = -B^2$ -/

/-- **Extended reduced forms** (Ch. 15, §3.3, p. 359), for $-d$ a square: the book extends the notion of reduced form
(12) (`IsReducedIndef`) by "all forms of the shape $0^{b}a$ or $a^{b}0$ ($-b < a \le b$)". The form $a^{b}c$ with
entries `a b c` is extended reduced iff it satisfies (12), or $a = 0$, $b > 0$, $-b < c \le b$ (the shape
$0^{b}c$), or $c = 0$, $b > 0$, $-b < a \le b$ (the shape $a^{b}0$). -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
def IsExtReduced (a b c : ℤ) : Prop :=
  IsReducedIndef a b c ∨ (a = 0 ∧ 0 < b ∧ -b < c ∧ c ≤ b) ∨ (c = 0 ∧ 0 < b ∧ -b < a ∧ a ≤ b)

instance (a b c : ℤ) : Decidable (IsExtReduced a b c) := by unfold IsExtReduced; infer_instance

/-- **The next form of the modified sequence for $-d$ a square** (Ch. 15, §3.3, p. 359: "Theorem 1 must be modified
slightly, and in particular the inequality in (7) must be replaced by $\le$"). From $f = a^{b}c$ with $c \ne 0$ the
next form is $c^{b'}c'$ with $b'$ the largest solution of $b + x \equiv 0 \pmod c$ with $x^2 + d \le 0$ (if there is
one; otherwise the solution of least absolute value, positive in a tie) and $c' = (b'^2 + d)/c$. Since $x^2 + d \le 0$
is $x^2 + (d - 1) < 0$ over $\mathbb{Z}$, $b'$ is `stepB b c (d - 1)`, the rule (6)–(7) for the determinant
$d - 1$ (`nextFormLe_isStepB`). The fields: `f.b`, `f.c` are $b$, $c$; the determinant is `d`. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
def nextFormLe (d : ℤ) (f : BinForm) : BinForm :=
  ⟨f.c, stepB f.b f.c (d - 1), (stepB f.b f.c (d - 1) ^ 2 + d) / f.c⟩

/-- **`nextFormLe` implements rules (6) and (7) with $\le$ in (7)**: $b'$ solves $b + b' \equiv 0 \pmod c$ and is
the largest such solution with $b'^2 + d - 1 < 0$ (i.e. $b'^2 + d \le 0$) when one exists, and otherwise the solution
of least absolute value (positive in a tie). -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
theorem nextFormLe_isStepB (d : ℤ) (f : BinForm) (hc : f.c ≠ 0) :
    IsStepB (d - 1) f.b f.c (nextFormLe d f).b := isStepB_stepB hc

/-- **The finite chain** $0^{b_0}a_1^{b_1}a_2\ldots a_k^{b_0}0$ of §3.3 (p. 359: "the 'cycle' of reduced forms
becomes a finite sequence"): the forms $f_0, f_1, \ldots$ from the start form $f_0$ by `nextFormLe`, up to and
including the first form with $c = 0$ (of shape $a^{b}0$); `fuel` bounds the length (the list is truncated if the
chain is longer; the table checks use `fuel = 64`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
def sqChain (d : ℤ) : ℕ → BinForm → List BinForm
  | 0, _ => []
  | n + 1, f => if f.c = 0 then [f] else f :: sqChain d n (nextFormLe d f)

/-- **The digits of a chain** in the book's notation: $|a_0|, b_0, |a_1|, b_1, \ldots, |a_k|, b_k, |c_k|$ (the signs of
the $a_i$ alternate and are omitted in the printed tables; the last digit is the last form's third entry). -/
def chainDigits (L : List BinForm) : List ℤ :=
  L.flatMap (fun f => [|f.a|, f.b]) ++ [|(L.getLastD ⟨0, 0, 0⟩).c|]

/-- **The digits of a printed entry**: with a curly bracket (`refl = true`) the entry $E$ is read as $E$ followed by
its mirror image about the last digit (reflection about the outermost digits, p. 360); otherwise the printed digits
are taken as they are. -/
def sqDecode (refl : Bool) (E : List ℤ) : List ℤ := if refl then E ++ E.dropLast.reverse else E

/-- **The chain of a printed entry for $d = -B^2$**: the chain started at $0^{B}a_1$, where $a_1$ is the third printed
digit ($0$ if the entry is just $0^{B}$). -/
def entryChain (B : ℤ) (e : Bool × List ℤ) : List BinForm := sqChain (-B ^ 2) 64 ⟨0, B, e.2.getD 2 0⟩

/-- **One entry of the square rows is correct:** it starts $0, B$, and its digits (reflected if printed with a curly
bracket) are exactly the digits of the chain of the modified sequence started at $0^{B}a_1$. -/
def SqEntryOK (B : ℤ) (e : Bool × List ℤ) : Prop :=
  e.2.take 2 = [0, B] ∧ chainDigits (entryChain B e) = sqDecode e.1 e.2

instance (B : ℤ) (e : Bool × List ℤ) : Decidable (SqEntryOK B e) := by unfold SqEntryOK; infer_instance

/-- **All forms represented by the entries of the row $d = -B^2$**: each chain, its sign change of the $a_i$, its
reversal and both (`variants`, as for the nonsquare rows). -/
def sqForms (B : ℤ) (entries : List (Bool × List ℤ)) : List BinForm :=
  (entries.flatMap fun e => (variants (entryChain B e)).flatten)

/-- **The row $d = -B^2$ of Table 15.2 is correct:** every printed entry is the chain of the modified sequence; the
forms of these chains are extended reduced of determinant $-B^2$; and every extended reduced form of determinant
$-B^2$ occurs in the chain of an entry, or in its sign change or reversal (the "four related cycles"). The check of the
last part: the forms $0^{B}c$, $c^{B}0$ ($-B < c \le B$), and the forms satisfying (12) (found by the bounded search
of `reducedIndef_complete`). -/
def SqTableOK (B : ℤ) (entries : List (Bool × List ℤ)) : Prop :=
  (∀ e ∈ entries, SqEntryOK B e) ∧
  (∀ e ∈ entries, ∀ f ∈ entryChain B e, IsExtReduced f.a f.b f.c ∧ f.det = -B ^ 2) ∧
  (∀ c ∈ Finset.Icc (-B + 1) B, (⟨0, B, c⟩ : BinForm) ∈ sqForms B entries ∧
      (⟨c, B, 0⟩ : BinForm) ∈ sqForms B entries) ∧
  (∀ a ∈ Finset.Icc (-B ^ 2) (-(-B ^ 2)), ∀ b ∈ Finset.Icc 1 B, a ∣ -B ^ 2 + b ^ 2 →
      IsReducedIndef a b ((-B ^ 2 + b ^ 2) / a) →
        (⟨a, b, (-B ^ 2 + b ^ 2) / a⟩ : BinForm) ∈ sqForms B entries)

instance (B : ℤ) (entries : List (Bool × List ℤ)) : Decidable (SqTableOK B entries) := by
  unfold SqTableOK SqEntryOK; infer_instance

/-- **If a row is correct, its entries (with their four variants) represent every extended reduced form** of
determinant $-B^2$ ($B > 0$). -/
theorem SqTableOK.complete {B : ℤ} {entries : List (Bool × List ℤ)} (h : SqTableOK B entries) (hB : 0 < B)
    (x : BinForm) (hx : IsExtReduced x.a x.b x.c) (hd : x.det = -B ^ 2) : x ∈ sqForms B entries := by
  obtain ⟨-, -, h3, h4⟩ := h
  rcases hx with h | ⟨ha, hb, hc1, hc2⟩ | ⟨hc, hb, ha1, ha2⟩
  · exact reducedIndef_complete (d := -B ^ 2) (B := B) hB.le (by nlinarith) h4 x h hd
  · have hbB : x.b = B := by
      simp only [BinForm.det, ha] at hd
      nlinarith
    have := (h3 x.c (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).1
    obtain ⟨a, b, c⟩ := x
    simp only at ha hbB
    subst ha hbB
    exact this
  · have hbB : x.b = B := by
      simp only [BinForm.det, hc] at hd
      nlinarith
    have := (h3 x.a (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2
    obtain ⟨a, b, c⟩ := x
    simp only at hc hbB
    subst hc hbB
    exact this

/-- **Table 15.2, the square rows $d = -B^2$ ($B = 1, \ldots, 10$), printed entries**: for each $B$ the entries of the
row $d = -B^2$ as (curly bracket, printed digits): $0^{B}$, $0^{B}1$, … with the digits $b_0 = B, a_1, b_1, a_2, \ldots$.
A curly bracket marks reflection about the last digit; an entry without it (`false`) is printed in full.
*Transcription note:* the page scan is of low resolution; the entry $0^{10}6^{8}$ (for $d = -100$) was read as the
only reading consistent with the chain computed by the modified rule (`SqEntryOK`), which the check confirms. -/
def t152sq : List (ℤ × List (Bool × List ℤ)) := [
  (1, [(true, [0, 1]), (true, [0, 1, 1])]),
  (2, [(true, [0, 2]), (true, [0, 2, 1]), (true, [0, 2, 2])]),
  (3, [(true, [0, 3]), (true, [0, 3, 1]), (true, [0, 3, 2]), (true, [0, 3, 3])]),
  (4, [(true, [0, 4]), (true, [0, 4, 1]), (true, [0, 4, 2]), (true, [0, 4, 3, 2, 4]), (true, [0, 4, 4])]),
  (5, [(true, [0, 5]), (true, [0, 5, 1]), (true, [0, 5, 2]), (true, [0, 5, 3, 4]), (true, [0, 5, 4, 3]),
    (true, [0, 5, 5])]),
  (6, [(true, [0, 6]), (true, [0, 6, 1]), (true, [0, 6, 2]), (true, [0, 6, 3]), (true, [0, 6, 4]),
    (true, [0, 6, 5, 4, 4]), (true, [0, 6, 6])]),
  (7, [(true, [0, 7]), (true, [0, 7, 1]), (true, [0, 7, 2]), (false, [0, 7, 3, 5, 8, 3, 5, 7, 0]),
    (false, [0, 7, 4, 5, 6, 7, 0]), (true, [0, 7, 7])]),
  (8, [(true, [0, 8]), (true, [0, 8, 1]), (true, [0, 8, 2]), (false, [0, 8, 3, 7, 5, 8, 0]), (true, [0, 8, 4]),
    (true, [0, 8, 6, 4, 8]), (true, [0, 8, 7, 6, 4]), (true, [0, 8, 8])]),
  (9, [(true, [0, 9]), (true, [0, 9, 1]), (true, [0, 9, 2]), (true, [0, 9, 3]),
    (false, [0, 9, 4, 7, 8, 9, 0]), (false, [0, 9, 5, 6, 9, 3, 8, 5, 7, 9, 0]), (true, [0, 9, 6]),
    (true, [0, 9, 9])]),
  (10, [(true, [0, 10]), (true, [0, 10, 1]), (true, [0, 10, 2]), (false, [0, 10, 3, 8, 12, 4, 7, 10, 0]),
    (true, [0, 10, 4]), (true, [0, 10, 5]), (true, [0, 10, 6, 8]),(true, [0, 10, 8, 6]),
    (true, [0, 10, 9, 8, 4]), (true, [0, 10, 10])])]

/-- **Table 15.2a, the square rows $d = -1, -4, -9, -16, -25, -36, -49$ checked** (Ch. 15, §3.3, p. 362): every
printed entry is a chain of the modified sequence (extended reduced forms from $0^{B}a_1$ to $a_k^{B}0$), and every
extended reduced form of determinant $-B^2$ occurs in an entry or in one of its sign changes and reversals. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, Table 15.2a, p. 362"]
theorem table152sq_a_correct : ∀ e ∈ t152sq.take 7, SqTableOK e.1 e.2 := by
  decide +kernel

/-- **Table 15.2b, the square rows $d = -64, -81, -100$ checked** (Ch. 15, §3.3, p. 363), as for
`table152sq_a_correct`. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, Table 15.2b, p. 363"]
theorem table152sq_b_correct : ∀ e ∈ t152sq.drop 7, SqTableOK e.1 e.2 := by
  decide +kernel

/-! ### §3.4: the determinant $-7$ example (pp. 365–366) -/

theorem not_isSquare_neg_det7 : ¬ IsSquare (-(BinForm.det ⟨3, 2, -1⟩)) := by
  have : -(BinForm.det ⟨3, 2, -1⟩) = 7 := by decide
  rw [this]
  exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)

/-- **The two cycles of determinant $-7$** (Ch. 15, §3.4, p. 365): the form $\begin{pmatrix}3&2\\2&-1\end{pmatrix}$
lies in the reduced cycle printed in the book ($a_i$: $3, -1, 3, -2$; $b_i$: $2, 2, 1, 1$), namely
$3^{2}(-1),\ (-1)^{2}3,\ 3^{1}(-2),\ (-2)^{1}3$ (four forms), and $\begin{pmatrix}2&1\\1&-3\end{pmatrix}$ lies in the
other cycle $2^{1}(-3),\ (-3)^{2}1,\ 1^{2}(-3),\ (-3)^{1}2$. The two cycles are the two cycles of Table 15.2a
at $d=-7$ (`table152_correct`), exchanged by changing the signs of the $a_i$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
theorem det7_cycles :
    CycleData ⟨3, 2, -1⟩ 4 [⟨3, 2, -1⟩, ⟨-1, 2, 3⟩, ⟨3, 1, -2⟩, ⟨-2, 1, 3⟩] ∧
    CycleData ⟨2, 1, -3⟩ 4 [⟨2, 1, -3⟩, ⟨-3, 2, 1⟩, ⟨1, 2, -3⟩, ⟨-3, 1, 2⟩] := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- **The reduction sequence of $\begin{pmatrix}9&5\\5&2\end{pmatrix}$** (p. 365: "which gives the reduction
sequence $9^{5}2,\ 2^{1}(-3),\ (-3)^{2}1,\ 1^{2}(-3), \dots$"): the form $9^{5}2$ has determinant $-7$, its
successor in the sequence (5) is $2^{1}(-3)$, and its cycle is that of $2^{1}(-3)$, the cycle of the principal form
(`det7_principal`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
theorem det7_square_cycle :
    BinForm.det ⟨9, 5, 2⟩ = -7 ∧ sequenceOf ⟨9, 5, 2⟩ 1 = ⟨2, 1, -3⟩ ∧
      cycleSet ⟨9, 5, 2⟩ = {x | x ∈ [(⟨2, 1, -3⟩ : BinForm), ⟨-3, 2, 1⟩, ⟨1, 2, -3⟩, ⟨-3, 1, 2⟩]} := by
  refine ⟨by decide, by decide +kernel, ?_⟩
  have hper : pairSeq (BinForm.det ⟨9, 5, 2⟩) (9, 5) (1 + 4) = pairSeq (BinForm.det ⟨9, 5, 2⟩) (9, 5) 1 := by
    decide +kernel
  have hL : (List.range 4).map (fun i => sequenceOf ⟨9, 5, 2⟩ (1 + i)) =
      [(⟨2, 1, -3⟩ : BinForm), ⟨-3, 2, 1⟩, ⟨1, 2, -3⟩, ⟨-3, 1, 2⟩] := by
    decide +kernel
  exact cycleSet_eq_of_list (f := ⟨9, 5, 2⟩) (by norm_num) hper hL

/-- **The class of $2^{1}(-3)$ is the principal class**: $\begin{pmatrix}2&1\\1&-3\end{pmatrix}$ and
$\begin{pmatrix}9&5\\5&2\end{pmatrix}$ are properly equivalent to $x^2 - 7y^2$ = `⟨1, 0, -7⟩`. (The cycle of
$2^{1}(-3)$ contains $1^{2}(-3)$, which is $x^2-7y^2$ after the translation $x \mapsto x + 2y$.) -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, pp. 365–366"]
theorem det7_principal : ProperEquiv ⟨2, 1, -3⟩ ⟨1, 0, -7⟩ ∧ ProperEquiv ⟨9, 5, 2⟩ ⟨1, 0, -7⟩ := by
  have h1 : ¬ IsSquare (-(BinForm.det ⟨2, 1, -3⟩)) := by
    have : -(BinForm.det ⟨2, 1, -3⟩) = 7 := by decide
    rw [this]
    exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : ¬ IsSquare (-(BinForm.det ⟨9, 5, 2⟩)) := by
    have : -(BinForm.det ⟨9, 5, 2⟩) = 7 := by decide
    rw [this]
    exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ProperEquiv ⟨2, 1, -3⟩ ⟨1, 2, -3⟩ := by
    have := (properEquiv_sequenceOf h1 2).1
    have e : sequenceOf ⟨2, 1, -3⟩ 2 = ⟨1, 2, -3⟩ := by decide +kernel
    rwa [e] at this
  have e2 : ProperEquiv ⟨1, 2, -3⟩ ⟨1, 0, -7⟩ := by
    have := (translate_equiv 1 0 (-7) 2).symm
    exact this
  have e3 : ProperEquiv ⟨9, 5, 2⟩ ⟨2, 1, -3⟩ := by
    have := (properEquiv_sequenceOf h2 1).1
    have e : sequenceOf ⟨9, 5, 2⟩ 1 = ⟨2, 1, -3⟩ := by decide +kernel
    rwa [e] at this
  exact ⟨e1.trans e2, e3.trans (e1.trans e2)⟩

/-- **The class of $3^{2}(-1)$ is not principal, and it is not that of $2^{1}(-3)$** (p. 366: the group of classes
is "cyclic of order 2" with the class of $\begin{pmatrix}3&2\\2&-1\end{pmatrix}$ of order $2$): the form
$3x^2 + 4xy - y^2$ represents $-1$, whereas a form equivalent to $\begin{pmatrix}2&1\\1&-3\end{pmatrix}$ cannot:
$2x^2 + 2xy - 3y^2 = -1$ gives $(2x+y)^2 \equiv -2 \pmod 7$, impossible. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, pp. 365–366"]
theorem det7_not_equiv : ¬ ProperEquiv ⟨3, 2, -1⟩ ⟨2, 1, -3⟩ ∧ ¬ ProperEquiv ⟨3, 2, -1⟩ ⟨1, 0, -7⟩ := by
  have key : ∀ g : BinForm, (∀ r s : ℤ, g.a * r ^ 2 + 2 * g.b * r * s + g.c * s ^ 2 ≠ -1) →
      ¬ ProperEquiv ⟨3, 2, -1⟩ g := by
    intro g hg h
    obtain ⟨p, q, r, s, -, -, hc, -⟩ := equiv_entries h.symm
    exact hg r s (by simpa using hc.symm)
  constructor
  · apply key
    intro r s h
    dsimp only at h
    have hmod := congrArg (Int.cast : ℤ → ZMod 7) (show (2 * r + s) ^ 2 = -2 + 7 * s ^ 2 by
      linear_combination 2 * h)
    push_cast at hmod
    have hno : ∀ x : ZMod 7, x ^ 2 ≠ -2 := by decide
    apply hno (2 * (r : ZMod 7) + s)
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hmod
  · apply key
    intro r s h
    dsimp only at h
    have hmod := congrArg (Int.cast : ℤ → ZMod 7) (show r ^ 2 = -1 + 7 * s ^ 2 by
      linear_combination h)
    push_cast at hmod
    have hno : ∀ x : ZMod 7, x ^ 2 ≠ -1 := by decide
    apply hno (r : ZMod 7)
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hmod

/-- **The ideal computation of p. 365**, in the ring $\mathbb{Z}[\sqrt 7]$ (`Zsqrtd 7`, elements `⟨re, im⟩` meaning
$\mathrm{re} + \mathrm{im}\sqrt 7$): the square of the ideal $\langle 3,\ -2+\sqrt 7\rangle$ attached to
$\begin{pmatrix}3&2\\2&-1\end{pmatrix}$ equals $\langle 9,\ -5+\sqrt 7\rangle$, the ideal attached to
$\begin{pmatrix}9&5\\5&2\end{pmatrix}$ (the book: "this is easily seen to be the same as the ideal
$\langle 9, -5+\sqrt 7\rangle_9$", using the generators $9$, $-6+3\sqrt 7$, $11-4\sqrt 7$ of the square). The *normed*
ideals $\langle\cdot\rangle_N$ and the correspondence with forms (p. 365) are in `NormedIdeals.lean` and
`NormedIdealsForms.lean` (`det7_normed_square` is this identity for normed ideals, norm part included). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
theorem det7_ideal_square :
    (Ideal.span {(⟨3, 0⟩ : Zsqrtd 7), ⟨-2, 1⟩}) ^ 2 = Ideal.span {(⟨9, 0⟩ : Zsqrtd 7), ⟨-5, 1⟩} := by
  rw [pow_two, Ideal.span_mul_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨y, hy, z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
    · exact Ideal.mem_span_pair.2 ⟨1, 0, by ext <;> simp⟩
    · exact Ideal.mem_span_pair.2 ⟨1, 3, by ext <;> simp⟩
    · exact Ideal.mem_span_pair.2 ⟨1, 3, by ext <;> simp⟩
    · exact Ideal.mem_span_pair.2 ⟨-1, -4, by ext <;> simp⟩
  · rw [Ideal.span_le]
    set S : Set (Zsqrtd 7) := {⟨3, 0⟩, ⟨-2, 1⟩} with hS
    have g1 : (⟨9, 0⟩ : Zsqrtd 7) ∈ Ideal.span (S * S) :=
      Ideal.subset_span ⟨⟨3, 0⟩, by simp [hS], ⟨3, 0⟩, by simp [hS], by ext <;> simp⟩
    have g2 : (⟨-6, 3⟩ : Zsqrtd 7) ∈ Ideal.span (S * S) :=
      Ideal.subset_span ⟨⟨3, 0⟩, by simp [hS], ⟨-2, 1⟩, by simp [hS], by ext <;> simp⟩
    have g3 : (⟨11, -4⟩ : Zsqrtd 7) ∈ Ideal.span (S * S) :=
      Ideal.subset_span ⟨⟨-2, 1⟩, by simp [hS], ⟨-2, 1⟩, by simp [hS], by ext <;> simp⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact g1
    · have : (⟨-5, 1⟩ : Zsqrtd 7) = 3 * ⟨-6, 3⟩ + 2 * ⟨11, -4⟩ - ⟨9, 0⟩ := by ext <;> simp
      rw [SetLike.mem_coe, this]
      exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ g2) (Ideal.mul_mem_left _ _ g3)) g1

/-- **Stated, not proved: the classes of determinant $-7$** (p. 366: "in fact every form of determinant $-7$ is in one
of these two classes, and so the group is cyclic of order 2"). Every integral binary form of determinant $-7$ is
properly equivalent to the principal form $x^2-7y^2$ (the class of $2^{1}(-3)$, `det7_principal`) or to
$3^{2}(-1)$. Together with `det7_not_equiv` (these are different) and the ideal square `det7_ideal_square`, this says
the group of classes is cyclic of order $2$. It needs the reduction theory of Theorem 1 for arbitrary forms
(that every form reaches a cycle), which is not formalized; for the forms of the cycles it is Table 15.2a at
$d = -7$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 366"]
def Det7ClassesStatement : Prop :=
  ∀ f : BinForm, f.det = -7 → ProperEquiv f ⟨1, 0, -7⟩ ∨ ProperEquiv f ⟨3, 2, -1⟩

/-! ### §10.1: the inequalities of Minkowski reduction -/

theorem sum_sum_eq_diag_add_two_lt {n : ℕ} (S : Finset (Fin n)) (g : Fin n → Fin n → ℝ)
    (hg : ∀ r s, g r s = g s r) :
    ∑ r ∈ S, ∑ s ∈ S, g r s =
      ∑ s ∈ S, g s s + 2 * ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s), g r s := by
  have h1 : ∀ r s, g r s = (if r < s then g r s else 0) + (if s < r then g s r else 0) +
      (if r = s then g r r else 0) := by
    intro r s
    rcases lt_trichotomy r s with h | h | h
    · simp [h, not_lt.2 h.le, h.ne]
    · subst h; simp
    · simp [h, not_lt.2 h.le, h.ne', hg r s]
  have h2 : ∑ r ∈ S, ∑ s ∈ S, (if s < r then g s r else 0) =
      ∑ r ∈ S, ∑ s ∈ S, (if r < s then g r s else 0) := Finset.sum_comm
  have h3 : ∑ r ∈ S, ∑ s ∈ S, (if r = s then g r r else 0) = ∑ s ∈ S, g s s := by
    refine Finset.sum_congr rfl fun r hr => ?_
    simp [hr]
  calc ∑ r ∈ S, ∑ s ∈ S, g r s
      = ∑ r ∈ S, ∑ s ∈ S, ((if r < s then g r s else 0) + (if s < r then g s r else 0) +
          (if r = s then g r r else 0)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => h1 r s
    _ = ∑ s ∈ S, g s s + 2 * ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s), g r s := by
        simp only [Finset.sum_add_distrib, h2, h3, Finset.sum_filter]
        ring

/-- **The one-sided Minkowski inequality** (Conway–Sloane, Ch. 15, §10.1, (ii), p. 396), for a Minkowski reduced real
(in particular integral or rational) symmetric matrix $F = (a_{ij})$ (`Reduction.IsMinkowskiReduced`, condition (45)):
for $t$, a set $S$ of indices $s < t$ and signs $\epsilon_s = \pm 1$ ($s \in S$),
$$2\Bigl(\sum_{s\in S}\epsilon_s a_{st} - \sum_{r<s,\ r,s\in S}\epsilon_r\epsilon_s a_{rs}\Bigr) \le \sum_{s\in S} a_{ss},$$
which is $f(e_t) \le f(v)$ for $v = e_t - \sum_{s\in S}\epsilon_se_s$ (this $v$ extends $e_0, \dots, e_{t-1}$ to a
basis, as $v_t = 1$). Indices are $0$-based. *Erratum (printed form):* the book writes the left side with an absolute
value; the derivation gives only this one-sided inequality for each choice of signs (and, replacing $\epsilon$ by
$-\epsilon$, the second one `minkowski_ineq_neg`). The absolute value is justified for $\lvert S\rvert \le 1$
(`minkowski_ineq_abs_of_card_le_one`) but not in general: see `Examples.counterexample_printed48`. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (ii), p. 396"]
theorem minkowski_ineq {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : Reduction.IsMinkowskiReduced F)
    (t : Fin n) (S : Finset (Fin n)) (hS : ∀ s ∈ S, s < t) (ε : Fin n → ℤ)
    (hε : ∀ s ∈ S, ε s = 1 ∨ ε s = -1) :
    2 * (∑ s ∈ S, (ε s : ℝ) * F s t -
        ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s), (ε r : ℝ) * ε s * F r s) ≤ ∑ s ∈ S, F s s := by
  have hs : F.IsSymm := ((Reduction.posDef_iff F).1 hF.1).1
  have hsym : ∀ r s, F r s = F s r := fun r s => by
    have : Matrix.transpose F = F := hs
    simpa using (congrFun (congrFun this r) s).symm
  have htS : t ∉ S := fun h => lt_irrefl _ (hS t h)
  let vz : Fin n → ℤ := fun i => (Pi.single t 1 : Fin n → ℤ) i - (if i ∈ S then ε i else 0)
  let w : Fin n → ℝ := fun i => if i ∈ S then (ε i : ℝ) else 0
  have hcast : Reduction.cast vz = (Pi.single t 1 : Fin n → ℝ) + (-1 : ℝ) • w := by
    funext i
    by_cases h : i = t <;> by_cases h2 : i ∈ S <;> simp [Reduction.cast, vz, w, Pi.single_apply, h, h2] <;>
      ring
  have hvt : vz t = 1 := by simp [vz, htS]
  have hext : Reduction.ExtendsBasis t vz := by
    rw [Reduction.extendsBasis_iff_gcd]
    have h1 : Reduction.tailGcd t vz ∣ vz t :=
      Finset.gcd_dvd (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)
    rw [hvt] at h1
    exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) h1
  have hmain := hF.2 t vz hext
  rw [hcast, Reduction.val_add hs, Reduction.val_single, Reduction.val_smul] at hmain
  have e1 : (Pi.single t 1 : Fin n → ℝ) ⬝ᵥ (F.mulVec ((-1 : ℝ) • w)) = -∑ s ∈ S, (ε s : ℝ) * F t s := by
    simp [dotProduct, Matrix.mulVec, w, Finset.sum_ite_mem, mul_ite, Finset.sum_neg_distrib,
      Pi.single_apply, mul_comm]
  have e2 : Reduction.val F w = ∑ r ∈ S, ∑ s ∈ S, (ε r : ℝ) * ε s * F r s := by
    simp [Reduction.val, dotProduct, Matrix.mulVec, w, Finset.sum_ite_mem, mul_ite, ite_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  rw [e1, e2] at hmain
  have e3 := sum_sum_eq_diag_add_two_lt S (fun r s => (ε r : ℝ) * ε s * F r s)
    (fun r s => by rw [hsym r s]; ring)
  have e4 : ∑ s ∈ S, (ε s : ℝ) * ε s * F s s = ∑ s ∈ S, F s s := by
    refine Finset.sum_congr rfl fun s hs' => ?_
    rcases hε s hs' with h | h <;> simp [h]
  have e5 : ∑ s ∈ S, (ε s : ℝ) * F t s = ∑ s ∈ S, (ε s : ℝ) * F s t := by
    refine Finset.sum_congr rfl fun s _ => by rw [hsym t s]
  rw [e3, e4, e5] at hmain
  nlinarith [hmain]

/-- **The second one-sided inequality** (replace $\epsilon$ by $-\epsilon$ in `minkowski_ineq`):
$2(-\sum_s\epsilon_sa_{st} - \sum_{r<s}\epsilon_r\epsilon_sa_{rs}) \le \sum_s a_{ss}$. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (ii), p. 396"]
theorem minkowski_ineq_neg {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : Reduction.IsMinkowskiReduced F)
    (t : Fin n) (S : Finset (Fin n)) (hS : ∀ s ∈ S, s < t) (ε : Fin n → ℤ)
    (hε : ∀ s ∈ S, ε s = 1 ∨ ε s = -1) :
    2 * (-∑ s ∈ S, (ε s : ℝ) * F s t -
        ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s), (ε r : ℝ) * ε s * F r s) ≤ ∑ s ∈ S, F s s := by
  have := minkowski_ineq hF t S hS (fun s => -ε s) (fun s hs => by
    rcases hε s hs with h | h <;> simp [h])
  simpa [Finset.sum_neg_distrib] using this

/-- **The absolute-value form for $\lvert S\rvert \le 1$** (the inequality (47)): for a single index $s < t$,
$2\lvert a_{st}\rvert \le a_{ss}$. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (ii), (47), p. 396"]
theorem minkowski_ineq_abs_of_card_le_one {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : Reduction.IsMinkowskiReduced F) (s t : Fin n) (hst : s < t) :
    2 * |F s t| ≤ F s s := by
  have h1 := minkowski_ineq hF t {s} (by simpa using hst) (fun _ => 1) (by simp)
  have h2 := minkowski_ineq_neg hF t {s} (by simpa using hst) (fun _ => 1) (by simp)
  simp [Finset.filter_singleton] at h1 h2
  rcases abs_cases (F s t) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

end Binary

end ConwaySloane

end QuadFormsKB
