/-
# Conway–Sloane, Ch. 15, §3: the classification of binary quadratic forms

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3
(printed pp. 356–364; bibliography key `conwaysloane1999`; printed page = PDF page of the chapter file + 351).
The chapter quotes Theorem 1 from Edwards, *Fermat's Last Theorem*, p. 325, and (11), (12) and the square case from
Dickson/Jones and Gauss, *Disquisitiones*, §§183, 206–210, without proof; everything proved here is new to the book.

**Conventions (the book's).** The binary form $a^{b}c$ is $ax^2 + 2bxy + cy^2$ with the (classically integral) Gram
matrix $\begin{pmatrix} a & b\\ b & c\end{pmatrix}$ and determinant $d = ac - b^2$ ($d > 0$ definite, $d < 0$
indefinite). Forms are *properly* equivalent if $B = MAM^{\mathrm t}$ with $M$ integral of determinant $1$ ((4), p. 356).
Indices of the sequence $a_0, b_0, a_1, b_1, \dots$ are the book's own (already $0$-based).

**Formalization.** `BinForm` (fields `a b c`), `ProperEquiv` ((4)); Theorem 1's rules (5)–(7) as `stepPair` with the
computable choice `stepB` of $b_{i+1}$ and the specification `IsStepB` of the book's wording; `sequenceOf` (the
sequence (5)), `cycleSet` (the forms that occur infinitely often = the forms in the period), `Theorem1Statement`
(the full statement of Theorem 1, not weakened); (11) `IsReducedPos`; (12) `IsReducedIndef`; Table 15.1 as data
`table151`; Gauss' criterion for the square case `GaussSquareCriterion`.

**Proved (no `sorry`, no `native_decide`)**
* `isStepB_stepB`, `IsStepB.unique`: `stepB` implements rules (6)–(7), which determine $b_{i+1}$ uniquely.
* For $-d$ not a square: $a_i \ne 0$ and $a_i \mid b_i^2 + d$ are preserved (`StepInv.step`); the next form has
  determinant $d$ (`formAt_det`) and is properly equivalent to the previous one via
  $\begin{pmatrix} 0 & 1\\ -1 & k\end{pmatrix}$, $k = (b_i + b_{i+1})/a_{i+1}$ (`formAt_equiv`, `properEquiv_sequenceOf`);
  later forms of the sequence have the same cycle (`cycleSet_sequenceOf`).
* The easy half of Theorem 1: same nonempty cycle $\Rightarrow$ properly equivalent (`properEquiv_of_cycleSet_eq`,
  `properEquiv_of_periodic`).
* Example (8): the ten reduced forms of the cycle of $x^2 - 67y^2$, ultimate periodicity, and the disjoint cycle of
  $-x^2 + 67y^2$ (`example8_cycle`, `example8_neg_cycle`, `example8_disjoint`), all by `decide +kernel`.
  Inequivalence of the two forms is `example8_not_equiv` (proved directly, modulo $67$).
* (11): $3b^2 \le d$ for reduced forms (`IsReducedPos.three_sq_le`), existence of a properly equivalent reduced form
  for every positive definite form (`exists_reduced_pos`), uniqueness (`reduced_pos_unique`), together
  `exists_unique_reduced_pos`.
* Table 15.1 for $1 \le d \le 50$: the listed forms are exactly the reduced forms, each once
  (`table151_correct`, `tableTriples_nodup`). No discrepancy with the printed table.
* (12) and the cycles of $d = -13$, $-14$, $-37$ described on p. 361: `indef_d13`, `indef_d14`, `indef_d37`
  (the cycles, and that they exhaust the forms satisfying (12)).
* Gauss' criterion for the square case, both directions (`gauss_square_criterion`).

**Theorem 1 in full** (`Theorem1Statement`) is proved in `BinaryTheorem1.lean` (`theorem1`): ultimate periodicity of
the sequence in general and "properly equivalent $\Rightarrow$ same cycle". The book's improper-equivalence criterion
for the square case is not formalized (the printed formula $aa' \equiv \gcd(a,b)^2 \pmod{2b\gcd(a,b)}$ seems to need extra hypotheses: a numerical
check found it false for $a = a' = -20$, $b = 1$, where $a^{b}0$ is improperly equivalent to itself; not yet
confirmed against Gauss).

*Choice of `stepB`.* Written with `Nat.findGreatest` (not `Nat.sqrt`) so that all examples are kernel-evaluable.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB

namespace ConwaySloane

namespace Binary

/-! ### Forms, determinant, proper equivalence -/

/-- **An integral binary quadratic form $a^{b}c$** in Conway–Sloane's notation (Ch. 15, §1, p. 355): the form
$f(x,y) = ax^2 + 2bxy + cy^2$ with Gram matrix $\begin{pmatrix} a & b\\ b & c\end{pmatrix}$ (classically integral:
the off-diagonal entry is $b$, the cross term is $2b$). The fields `a`, `b`, `c` are the entries $a$, $b$, $c$. -/
structure BinForm where
  /-- The entry $a$ (the coefficient of $x^2$). -/
  a : ℤ
  /-- The off-diagonal entry $b$ (the coefficient of $xy$ is $2b$). -/
  b : ℤ
  /-- The entry $c$ (the coefficient of $y^2$). -/
  c : ℤ
  deriving DecidableEq, Repr

/-- **The Gram matrix** $\begin{pmatrix} a & b\\ b & c\end{pmatrix}$ of $a^{b}c$. -/
def BinForm.gram (f : BinForm) : Matrix (Fin 2) (Fin 2) ℤ := !![f.a, f.b; f.b, f.c]

/-- **The determinant** $d = ac - b^2$ of $a^{b}c$ (Conway–Sloane's $d$, Ch. 15, §2, p. 356; positive for definite
forms, negative for indefinite forms). -/
def BinForm.det (f : BinForm) : ℤ := f.a * f.c - f.b ^ 2

/-- **Proper integral equivalence** (Conway–Sloane, Ch. 15, §2, (4), p. 356): $B = MAM^{\mathrm t}$ for an integral
matrix $M$ of determinant $+1$ (`Matrix.det M = 1`), where $A$, $B$ are the Gram matrices of `f`, `g`. -/
@[kb "conwaysloane1999" "Ch. 15, §2, (4), p. 356"]
def ProperEquiv (f g : BinForm) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ g.gram = M * f.gram * M.transpose

/-- **Improper integral equivalence** (same, with $\det M = -1$; Ch. 15, §2, (4), p. 356). -/
@[kb "conwaysloane1999" "Ch. 15, §2, (4), p. 356"]
def ImproperEquiv (f g : BinForm) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = -1 ∧ g.gram = M * f.gram * M.transpose

theorem ProperEquiv.refl (f : BinForm) : ProperEquiv f f :=
  ⟨1, by simp, by simp⟩

theorem ProperEquiv.trans {f g h : BinForm} (h1 : ProperEquiv f g) (h2 : ProperEquiv g h) :
    ProperEquiv f h := by
  obtain ⟨M, hM, hMg⟩ := h1
  obtain ⟨N, hN, hNh⟩ := h2
  refine ⟨N * M, by rw [Matrix.det_mul, hM, hN]; norm_num, ?_⟩
  rw [hNh, hMg]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem ProperEquiv.symm {f g : BinForm} (h : ProperEquiv f g) : ProperEquiv g f := by
  obtain ⟨M, hM, hMg⟩ := h
  have h1 : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hM, one_smul]
  refine ⟨M.adjugate, by simp [Matrix.det_adjugate, hM], ?_⟩
  rw [hMg]
  calc f.gram = (M.adjugate * M) * f.gram * (M.transpose * M.adjugate.transpose) := by
        rw [h1, ← Matrix.transpose_mul, h1]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem ProperEquiv.det_eq {f g : BinForm} (h : ProperEquiv f g) : f.det = g.det := by
  obtain ⟨M, hM, hMg⟩ := h
  have := congrArg Matrix.det hMg
  simp only [Matrix.det_mul, Matrix.det_transpose, hM] at this
  simp [BinForm.gram, Matrix.det_fin_two] at this
  unfold BinForm.det
  nlinarith [this]

/-! ### Theorem 1: the step rules (5)–(7) -/

/-- **The solution of least absolute value** of $b + x \equiv 0 \pmod n$ ($n > 0$), with $x > 0$ in case of a tie
$|x| = n/2$: the representative of $-b$ in $(-n/2, n/2]$. -/
def smallSol (b n : ℤ) : ℤ := if 2 * ((-b) % n) ≤ n then (-b) % n else (-b) % n - n

/-- **The integer square-root bound** $T$ for $d < 0$: the largest natural number $t$ with $t^2 + d < 0$, i.e.
$t < \sqrt{-d}$ (found by `Nat.findGreatest` below the bound $|d|$, so that it is kernel-evaluable;
`sqrtBound_iff` says it has the stated property). -/
def sqrtBound (d : ℤ) : ℕ := Nat.findGreatest (fun t : ℕ => (t : ℤ) ^ 2 + d < 0) d.natAbs

/-- **Computable choice of $b_{i+1}$** in Conway–Sloane's Theorem 1, rules (6)–(7) (Ch. 15, §3.1, p. 357), given
$b = b_i$, $m = a_{i+1} \ne 0$ and the determinant $d$: if $d < 0$ let $T = $ `sqrtBound d` and let $c$ be the
largest integer $\le T$ with $b + c \equiv 0 \pmod m$; when $c^2 + d < 0$ this is the largest solution of (6) with (7),
and it is $b_{i+1}$; otherwise (no solution satisfies (7), in particular always for $d > 0$) $b_{i+1}$ is the solution of
(6) of least absolute value, positive in case of a tie (`smallSol`). That this implements the book's rule is
`isStepB_stepB`; that the rule determines $b_{i+1}$ uniquely is `IsStepB.unique`. -/
def stepB (b m d : ℤ) : ℤ :=
  if d < 0 then
    let T : ℤ := (sqrtBound d : ℤ)
    let c := T - (T + b) % (m.natAbs : ℤ)
    if c ^ 2 + d < 0 then c else smallSol b (m.natAbs : ℤ)
  else smallSol b (m.natAbs : ℤ)

/-- **The book's rules (6)–(7) as a specification** (Ch. 15, §3.1, p. 357): $x$ is "the largest solution of
$b + x \equiv 0 \pmod m$ for which $x^2 + d < 0$ if such solutions exist, and otherwise the solution of smallest
absolute value, taking $x$ positive in case of a tie". Here $b = b_i$, $m = a_{i+1}$, $x = b_{i+1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (6)–(7), p. 357"]
def IsStepB (d b m x : ℤ) : Prop :=
  m ∣ b + x ∧
  ((∃ y, m ∣ b + y ∧ y ^ 2 + d < 0) →
      x ^ 2 + d < 0 ∧ ∀ y, m ∣ b + y → y ^ 2 + d < 0 → y ≤ x) ∧
  ((¬ ∃ y, m ∣ b + y ∧ y ^ 2 + d < 0) →
      ∀ y, m ∣ b + y → x.natAbs ≤ y.natAbs ∧ (y.natAbs = x.natAbs → y ≤ x))

/-- **The rules (6)–(7) determine $b_{i+1}$ uniquely.** -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (6)–(7), p. 357"]
theorem IsStepB.unique {d b m x x' : ℤ} (h : IsStepB d b m x) (h' : IsStepB d b m x') : x = x' := by
  obtain ⟨hd, h1, h2⟩ := h
  obtain ⟨hd', h1', h2'⟩ := h'
  by_cases hex : ∃ y, m ∣ b + y ∧ y ^ 2 + d < 0
  · obtain ⟨-, hx⟩ := h1 hex
    obtain ⟨hx'0, hx'⟩ := h1' hex
    exact le_antisymm (hx' x hd (h1 hex).1) (hx x' hd' hx'0)
  · have e1 := h2 hex x' hd'
    have e2 := h2' hex x hd
    omega

theorem abs_step_aux {n s y : ℤ} (hn : 0 < n) (h1 : -n < 2 * s) (h2 : 2 * s ≤ n) (k : ℤ)
    (hy : y = s + n * k) : s.natAbs ≤ y.natAbs ∧ (y.natAbs = s.natAbs → y ≤ s) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have : n * k ≤ -n := by nlinarith
    omega
  · subst hk; simp at hy; subst hy; simp
  · have : n * k ≥ n := by nlinarith
    omega

theorem smallSol_spec {n : ℤ} (b : ℤ) (hn : 0 < n) :
    n ∣ b + smallSol b n ∧ ∀ y, n ∣ b + y →
      (smallSol b n).natAbs ≤ y.natAbs ∧ (y.natAbs = (smallSol b n).natAbs → y ≤ smallSol b n) := by
  have hqr := Int.mul_ediv_add_emod (-b) n
  have hr0 := Int.emod_nonneg (-b) hn.ne'
  have hr1 := Int.emod_lt_of_pos (-b) hn
  unfold smallSol
  split_ifs with hs
  · refine ⟨⟨-((-b) / n), by linarith⟩, ?_⟩
    rintro y ⟨j, hj⟩
    exact abs_step_aux hn (by omega) hs (j + (-b) / n) (by linarith)
  · refine ⟨⟨-((-b) / n) - 1, by linarith⟩, ?_⟩
    rintro y ⟨j, hj⟩
    exact abs_step_aux hn (by omega) (by omega) (j + (-b) / n + 1) (by linarith)

theorem sqrtBound_iff {d : ℤ} (hd : d < 0) (t : ℕ) : (t : ℤ) ^ 2 + d < 0 ↔ t ≤ sqrtBound d := by
  have hdn : (d.natAbs : ℤ) = -d := by omega
  constructor
  · intro h
    have : t ≤ d.natAbs := by
      by_contra hc
      push_neg at hc
      have : (t : ℤ) ≥ d.natAbs + 1 := by exact_mod_cast hc
      nlinarith
    exact Nat.le_findGreatest this h
  · intro h
    have h0 : (((0 : ℕ) : ℤ)) ^ 2 + d < 0 := by simpa using hd
    have hT := Nat.findGreatest_spec (P := fun t : ℕ => (t : ℤ) ^ 2 + d < 0) (m := 0)
      (Nat.zero_le d.natAbs) h0
    have : (t : ℤ) ≤ (sqrtBound d : ℤ) := by exact_mod_cast h
    have ht0 : (0 : ℤ) ≤ t := by positivity
    have hT' : ((sqrtBound d : ℕ) : ℤ) ^ 2 + d < 0 := hT
    nlinarith

theorem sq_neg_iff {d : ℤ} (hd : d < 0) (y : ℤ) : y ^ 2 + d < 0 ↔ y.natAbs ≤ sqrtBound d := by
  rw [← sqrtBound_iff hd, Int.natAbs_sq]

/-- **`stepB` implements the rules (6)–(7)** for $m = a_{i+1} \ne 0$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (6)–(7), p. 357"]
theorem isStepB_stepB {d b m : ℤ} (hm : m ≠ 0) : IsStepB d b m (stepB b m d) := by
  obtain ⟨n, hn_def⟩ : ∃ n : ℤ, n = (m.natAbs : ℤ) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (sqrtBound d : ℤ) := ⟨_, rfl⟩
  have hn : (0 : ℤ) < n := by rw [hn_def]; positivity
  have key : ∀ z, m ∣ z ↔ n ∣ z := fun z => by rw [hn_def]; exact Int.natAbs_dvd.symm
  simp only [IsStepB, key]
  obtain ⟨hs1, hs2⟩ := smallSol_spec b hn
  have hqr := Int.mul_ediv_add_emod (T + b) n
  have hr0 := Int.emod_nonneg (T + b) hn.ne'
  have hr1 := Int.emod_lt_of_pos (T + b) hn
  have hc : n ∣ b + (T - (T + b) % n) := ⟨(T + b) / n, by linarith⟩
  by_cases hex : ∃ y, n ∣ b + y ∧ y ^ 2 + d < 0
  · obtain ⟨x0, hx0, hx0'⟩ := hex
    have hd : d < 0 := by nlinarith [sq_nonneg x0]
    have hbig : ∀ y, n ∣ b + y → y ≤ T → y ≤ T - (T + b) % n := by
      intro y hy hyT
      obtain ⟨j, hj⟩ := hy
      by_contra hlt
      push_neg at hlt
      have h1 : n * (j - (T + b) / n) = y - (T - (T + b) % n) := by linarith
      have h2 : 1 ≤ j - (T + b) / n := by
        by_contra hh
        push_neg at hh
        have : j - (T + b) / n ≤ 0 := by omega
        nlinarith
      nlinarith
    have hx0T := (sq_neg_iff hd x0).1 hx0'
    have hx0T' : (x0.natAbs : ℤ) ≤ T := by rw [hT]; exact_mod_cast hx0T
    have hcsq : (T - (T + b) % n) ^ 2 + d < 0 := by
      have := hbig x0 hx0 (by omega)
      rw [sq_neg_iff hd]
      omega
    have hst : stepB b m d = T - (T + b) % n := by
      simp only [stepB, if_pos hd, ← hn_def, ← hT]
      rw [if_pos hcsq]
    rw [hst]
    refine ⟨hc, fun _ => ⟨hcsq, fun y hy hy2 => hbig y hy ?_⟩, fun hno => absurd ⟨x0, hx0, hx0'⟩ hno⟩
    have := (sq_neg_iff hd y).1 hy2
    have : (y.natAbs : ℤ) ≤ T := by rw [hT]; exact_mod_cast this
    omega
  · have hst : stepB b m d = smallSol b n := by
      by_cases hd : d < 0
      · simp only [stepB, if_pos hd, ← hn_def, ← hT]
        rw [if_neg]
        intro hcl
        exact hex ⟨_, hc, hcl⟩
      · simp only [stepB, if_neg hd, ← hn_def]
    rw [hst]
    exact ⟨hs1, fun h => absurd h hex, fun _ => hs2⟩

/-! ### Theorem 1: the sequence of forms (5) -/

/-- **One step of Theorem 1's sequence (5)–(7)** (Ch. 15, §3.1, p. 357), on pairs $(a_i, b_i)$ for a fixed
determinant $d$: $(a_i, b_i) \mapsto (a_{i+1}, b_{i+1})$ with $a_{i+1} = (b_i^2 + d)/a_i$ (rule (5), exact integer
division when $a_i \mid b_i^2 + d$) and $b_{i+1} = $ `stepB b_i a_{i+1} d` (rules (6)–(7)). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (5)–(7), p. 357"]
def stepPair (d : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.2 ^ 2 + d) / p.1, stepB p.2 ((p.2 ^ 2 + d) / p.1) d)

/-- **The pair $(a_n, b_n)$**: the $n$-th iterate of `stepPair d` on the starting pair $(a_0, b_0)$. -/
def pairSeq (d : ℤ) (p : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := (stepPair d)^[n] p

/-- **The form $a_i^{b_i}a_{i+1}$ attached to a pair $(a_i, b_i)$**: its third entry is the next $a_{i+1}$. -/
def formAt (d : ℤ) (p : ℤ × ℤ) : BinForm := ⟨p.1, p.2, (stepPair d p).1⟩

/-- **The $n$-th form $a_n^{b_n}a_{n+1}$ of the sequence (5)** generated from the starting pair $(a_0, b_0)$. -/
def formSeq (d : ℤ) (p : ℤ × ℤ) (n : ℕ) : BinForm := formAt d (pairSeq d p n)

/-- **Theorem 1's sequence (5) of forms of a given form $f = a_0^{b_0}a_1$**: $f_0 = f$ (`sequenceOf_zero`),
$f_n = a_n^{b_n}a_{n+1}$, with $d = \det f$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, (5)–(7), p. 357"]
def sequenceOf (f : BinForm) (n : ℕ) : BinForm := formSeq f.det (f.a, f.b) n

/-- **The invariant of the iteration:** $a_i \ne 0$ and $a_i \mid b_i^2 + d$ (so that rule (5) is an exact division
and gives the next entry). -/
def StepInv (d : ℤ) (p : ℤ × ℤ) : Prop := p.1 ≠ 0 ∧ p.1 ∣ p.2 ^ 2 + d

theorem stepPair_fst_mul {d : ℤ} {p : ℤ × ℤ} (h : p.1 ∣ p.2 ^ 2 + d) :
    (stepPair d p).1 * p.1 = p.2 ^ 2 + d :=
  Int.ediv_mul_cancel h

theorem stepPair_snd (d : ℤ) (p : ℤ × ℤ) :
    (stepPair d p).2 = stepB p.2 (stepPair d p).1 d := rfl

theorem StepInv.fst_ne {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) :
    (stepPair d p).1 ≠ 0 := by
  intro h0
  have := stepPair_fst_mul h.2
  rw [h0, zero_mul] at this
  exact hd ⟨p.2, by nlinarith⟩

theorem StepInv.dvd_sum {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) :
    (stepPair d p).1 ∣ p.2 + (stepPair d p).2 := by
  rw [stepPair_snd]
  exact (isStepB_stepB (d := d) (b := p.2) (h.fst_ne hd)).1

/-- **The rules preserve $a_i \mid b_i^2 + d$ and $a_{i+1} \ne 0$** (Ch. 15, §3.1, p. 357: "the condition that $-d$
be not a square implies that the $a_i$ are nonzero, and so $a_{i+1}$ and $b_{i+1}$ are well-defined"). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem StepInv.step {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) :
    StepInv d (stepPair d p) := by
  refine ⟨h.fst_ne hd, ?_⟩
  have h1 := stepPair_fst_mul h.2
  have h2 := h.dvd_sum hd
  have : (stepPair d p).2 ^ 2 + d =
      (p.2 + (stepPair d p).2) * ((stepPair d p).2 - p.2) + (stepPair d p).1 * p.1 := by
    linear_combination (-1 : ℤ) * h1
  rw [this]
  exact dvd_add (h2.mul_right _) (dvd_mul_right _ _)

/-- **The next form has the same determinant** (Ch. 15, §3.1, p. 357: "a sequence of binary forms of determinant
$d$"): $\det a_i^{b_i}a_{i+1} = a_ia_{i+1} - b_i^2 = d$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem formAt_det {d : ℤ} {p : ℤ × ℤ} (h : StepInv d p) : (formAt d p).det = d := by
  have h1 := stepPair_fst_mul h.2
  simp only [formAt, BinForm.det]
  linarith

theorem properEquiv_step {a b a' b' a'' : ℤ} (ha' : a' ≠ 0) (hk : a' ∣ b + b')
    (h : a' * a'' = b' ^ 2 + (a * a' - b ^ 2)) : ProperEquiv ⟨a, b, a'⟩ ⟨a', b', a''⟩ := by
  obtain ⟨k, hk⟩ := hk
  refine ⟨!![0, 1; -1, k], by simp [Matrix.det_fin_two], ?_⟩
  have h2 : a'' = a - 2 * k * b + k ^ 2 * a' := by
    apply mul_left_cancel₀ ha'
    have hb' : b' = a' * k - b := by linarith
    rw [h, hb']; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two, h2] <;> nlinarith [hk]

/-- **Each form of the sequence is properly equivalent to the next**, via
$M = \begin{pmatrix} 0 & 1\\ -1 & k\end{pmatrix}$, $k = (b_i + b_{i+1})/a_{i+1}$ (Ch. 15, §3.1, Theorem 1, p. 357:
"two binary forms are properly equivalent if and only if they lead to the same cycle"; this is the easy half of
the proof). Here $B = MAM^{\mathrm t}$ holds with $\det M = 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem formAt_equiv {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) :
    ProperEquiv (formAt d p) (formAt d (stepPair d p)) := by
  have hq := h.step hd
  have h1 := stepPair_fst_mul h.2
  have h2 := stepPair_fst_mul hq.2
  exact properEquiv_step (a := p.1) (b := p.2) (a' := (stepPair d p).1) (b' := (stepPair d p).2)
    (a'' := (stepPair d (stepPair d p)).1) (h.fst_ne hd) (h.dvd_sum hd) (by linarith)

theorem pairSeq_succ (d : ℤ) (p : ℤ × ℤ) (n : ℕ) :
    pairSeq d p (n + 1) = stepPair d (pairSeq d p n) :=
  Function.iterate_succ_apply' _ _ _

theorem pairSeq_zero (d : ℤ) (p : ℤ × ℤ) : pairSeq d p 0 = p := rfl

theorem StepInv.pairSeq {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) (n : ℕ) :
    StepInv d (pairSeq d p n) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [pairSeq_succ]; exact ih.step hd

theorem formSeq_equiv_succ {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) (n : ℕ) :
    ProperEquiv (formSeq d p n) (formSeq d p (n + 1)) := by
  unfold formSeq
  rw [pairSeq_succ]
  exact formAt_equiv hd (h.pairSeq hd n)

theorem formSeq_equiv {d : ℤ} {p : ℤ × ℤ} (hd : ¬ IsSquare (-d)) (h : StepInv d p) (n : ℕ) :
    ProperEquiv (formSeq d p 0) (formSeq d p n) := by
  induction n with
  | zero => exact ProperEquiv.refl _
  | succ n ih => exact ih.trans (formSeq_equiv_succ hd h n)

theorem BinForm.stepInv {f : BinForm} (hf : ¬ IsSquare (-f.det)) : StepInv f.det (f.a, f.b) := by
  have ha : f.a ≠ 0 := by
    intro h0
    exact hf ⟨f.b, by simp [BinForm.det, h0]; ring⟩
  refine ⟨ha, ⟨f.c, ?_⟩⟩
  simp only [BinForm.det]
  ring

/-- **The sequence (5) starts at the given form** (needs only $a_0 \ne 0$, which holds as $-d$ is not a square). -/
theorem sequenceOf_zero {f : BinForm} (hf : ¬ IsSquare (-f.det)) : sequenceOf f 0 = f := by
  have h := BinForm.stepInv hf
  have h1 := stepPair_fst_mul h.2
  have : (stepPair f.det (f.a, f.b)).1 = f.c := by
    apply mul_right_cancel₀ h.1
    simp only at h1 ⊢
    rw [h1]; simp only [BinForm.det]; ring
  simp only [sequenceOf, formSeq, pairSeq_zero, formAt, this]

/-- **Every form of the sequence has determinant $d$ and is properly equivalent to $f$** (Ch. 15, §3.1, Theorem 1,
p. 357: the sequence consists of forms of determinant $d$, each properly equivalent to the given one). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem properEquiv_sequenceOf {f : BinForm} (hf : ¬ IsSquare (-f.det)) (n : ℕ) :
    ProperEquiv f (sequenceOf f n) ∧ (sequenceOf f n).det = f.det := by
  have h := BinForm.stepInv hf
  have e : ProperEquiv (sequenceOf f 0) (sequenceOf f n) := formSeq_equiv hf h n
  rw [sequenceOf_zero hf] at e
  have e2 : ProperEquiv f (sequenceOf f n) := e
  exact ⟨e2, (e2.det_eq).symm⟩

/-! ### Cycles -/

/-- **The set of values taken infinitely often by a sequence** $s : \mathbb{N} \to \alpha$: $x$ with
$\forall N\, \exists n \ge N,\ s_n = x$. For an ultimately periodic sequence this is exactly the set of values in
the period. -/
def recurrentSet {α : Type*} (s : ℕ → α) : Set α := {x | ∀ N, ∃ n ≥ N, s n = x}

/-- **A sequence is ultimately periodic**: $s_{n+p} = s_n$ for all $n \ge N$, for some $p > 0$. -/
def UltimatelyPeriodic {α : Type*} (s : ℕ → α) : Prop := ∃ N p : ℕ, 0 < p ∧ ∀ n ≥ N, s (n + p) = s n

/-- **The cycle of reduced forms of $f$** (Ch. 15, §3.1, Theorem 1, p. 357: "the forms in the period are called a
cycle of reduced forms"): the set of forms of the sequence (5) that occur infinitely often, which for an ultimately
periodic sequence is the set of the forms in the period. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
def cycleSet (f : BinForm) : Set BinForm := recurrentSet (sequenceOf f)

theorem periodic_mul {α : Type*} {s : ℕ → α} {N p : ℕ} (h : ∀ n ≥ N, s (n + p) = s n) :
    ∀ k n, n ≥ N → s (n + p * k) = s n := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hn
    have : n + p * (k + 1) = (n + p * k) + p := by ring
    rw [this, h _ (by nlinarith [Nat.zero_le (p * k)]), ih n hn]

theorem periodic_mod {α : Type*} {s : ℕ → α} {N p : ℕ} (hp : 0 < p) (h : ∀ n ≥ N, s (n + p) = s n)
    (j : ℕ) : s (N + j) = s (N + j % p) := by
  have h1 := periodic_mul h (j / p) (N + j % p) (by omega)
  have : N + j % p + p * (j / p) = N + j := by
    have := Nat.mod_add_div j p
    omega
  rw [this] at h1
  exact h1

/-- **The recurrent set of an ultimately periodic sequence is the set of values of one period**,
$\{s_{N+i} : 0 \le i < p\}$. -/
theorem mem_recurrentSet_iff {α : Type*} {s : ℕ → α} {N p : ℕ} (hp : 0 < p)
    (h : ∀ n ≥ N, s (n + p) = s n) (x : α) :
    x ∈ recurrentSet s ↔ ∃ i < p, s (N + i) = x := by
  constructor
  · intro hx
    obtain ⟨n, hn, hsn⟩ := hx N
    refine ⟨(n - N) % p, Nat.mod_lt _ hp, ?_⟩
    rw [← hsn, ← periodic_mod hp h (n - N)]
    congr 1
    omega
  · rintro ⟨i, hi, rfl⟩ M
    refine ⟨N + i + p * M, ?_, ?_⟩
    · nlinarith
    · exact periodic_mul h M (N + i) (by omega)

theorem recurrentSet_nonempty {α : Type*} {s : ℕ → α} (hs : UltimatelyPeriodic s) :
    (recurrentSet s).Nonempty := by
  obtain ⟨N, p, hp, h⟩ := hs
  exact ⟨s N, (mem_recurrentSet_iff hp h _).2 ⟨0, hp, rfl⟩⟩

theorem sequenceOf_shift {f : BinForm} (hf : ¬ IsSquare (-f.det)) (k n : ℕ) :
    sequenceOf (sequenceOf f k) n = sequenceOf f (n + k) := by
  have hI := (BinForm.stepInv hf).pairSeq hf k
  have hdet := (properEquiv_sequenceOf hf k).2
  simp only [sequenceOf, formSeq, pairSeq] at hdet ⊢
  have hd' : (formAt f.det ((stepPair f.det)^[k] (f.a, f.b))).det = f.det := hdet
  rw [hd']
  simp only [formAt]
  rw [← Function.iterate_add_apply]

/-- **Passing to a later form of the sequence does not change the cycle.** -/
theorem cycleSet_sequenceOf {f : BinForm} (hf : ¬ IsSquare (-f.det)) (k : ℕ) :
    cycleSet (sequenceOf f k) = cycleSet f := by
  ext g
  simp only [cycleSet, recurrentSet, Set.mem_setOf_eq, sequenceOf_shift hf]
  constructor
  · intro h N
    obtain ⟨n, hn, e⟩ := h N
    exact ⟨n + k, by omega, e⟩
  · intro h N
    obtain ⟨m, hm, e⟩ := h (N + k)
    exact ⟨m - k, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

/-- **Theorem 1, the half that is proved: forms with the same (nonempty) cycle are properly equivalent.**
If the cycles of $f$ and $g$ coincide and are nonempty (as they are once the sequences are ultimately periodic, the
first claim of Theorem 1), then $f \sim f_n = h = g_m \sim g$ for a common form $h$ of the cycle. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem properEquiv_of_cycleSet_eq {f g : BinForm} (hf : ¬ IsSquare (-f.det)) (hg : ¬ IsSquare (-g.det))
    (hne : (cycleSet f).Nonempty) (h : cycleSet f = cycleSet g) : ProperEquiv f g := by
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ cycleSet g := h ▸ hx
  obtain ⟨n, -, hn⟩ := hx 0
  obtain ⟨m, -, hm⟩ := hx' 0
  have e1 := (properEquiv_sequenceOf hf n).1
  have e2 := (properEquiv_sequenceOf hg m).1
  rw [hn] at e1
  rw [hm] at e2
  exact e1.trans e2.symm

/-- **Theorem 1** of Conway–Sloane, Ch. 15, §3.1, p. 357 (quoted there from Edwards, *Fermat's Last Theorem*, p. 325),
stated in full: for forms $f = a_0^{b_0}a_1$ and $g$ whose determinants have $-d$ not a square, the sequence (5)
built by the rules (5)–(7) (`sequenceOf`) is ultimately periodic, and $f$, $g$ are properly equivalent if and only if
they lead to the same cycle of reduced forms (`cycleSet`, the forms occurring infinitely often).

*Proved here* (not part of this statement as a whole; see the named theorems): the sequence is well defined, with all
$a_i \ne 0$ and every form of determinant $d$ (`StepInv.step`, `formAt_det`); each form is properly equivalent to its
successor and so to $f$ (`formAt_equiv`, `properEquiv_sequenceOf`); passing to a later form does not change the cycle
(`cycleSet_sequenceOf`); same nonempty cycle $\Rightarrow$ properly equivalent (`properEquiv_of_cycleSet_eq`), hence the
"if" half given ultimate periodicity (`properEquiv_of_periodic`); and for given forms the periodicity and the cycle
can be checked by computation (Example (8), (12) below). The whole statement, including ultimate periodicity and
"properly equivalent $\Rightarrow$ same cycle", is **proved** in `BinaryTheorem1.lean` (`Binary.theorem1`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
structure Theorem1Statement : Prop where
  /-- The sequence is ultimately periodic, and proper equivalence is equality of cycles. -/
  holds : ∀ f g : BinForm, ¬ IsSquare (-f.det) → ¬ IsSquare (-g.det) →
    UltimatelyPeriodic (sequenceOf f) ∧ (ProperEquiv f g ↔ cycleSet f = cycleSet g)

/-- **Theorem 1, "same cycle $\Rightarrow$ properly equivalent"** when the sequence of $f$ is ultimately periodic. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, Theorem 1, p. 357"]
theorem properEquiv_of_periodic {f g : BinForm} (hf : ¬ IsSquare (-f.det)) (hg : ¬ IsSquare (-g.det))
    (hper : UltimatelyPeriodic (sequenceOf f)) (h : cycleSet f = cycleSet g) : ProperEquiv f g :=
  properEquiv_of_cycleSet_eq hf hg (recurrentSet_nonempty hper) h

theorem pairSeq_add (d : ℤ) (p : ℤ × ℤ) (j n : ℕ) :
    pairSeq d p (j + n) = (stepPair d)^[j] (pairSeq d p n) :=
  Function.iterate_add_apply _ _ _ _

/-- **A computed period:** if $(a_{N+P}, b_{N+P}) = (a_N, b_N)$ then the sequence of forms is periodic from $N$ on. -/
theorem periodic_of_pairSeq {d : ℤ} {p : ℤ × ℤ} {N P : ℕ}
    (h : pairSeq d p (N + P) = pairSeq d p N) : ∀ n ≥ N, formSeq d p (n + P) = formSeq d p n := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e1 : N + j + P = j + (N + P) := by ring
  have e2 : N + j = j + N := by ring
  have : pairSeq d p (N + j + P) = pairSeq d p (N + j) := by
    rw [e1, pairSeq_add, h, ← pairSeq_add, e2]
  simp only [formSeq, this]

/-- **The cycle of a form with a computed period is the listed set of forms**: if the pairs satisfy
$(a_{N+P}, b_{N+P}) = (a_N, b_N)$ and the forms $f_N, \dots, f_{N+P-1}$ are the list `L`, then `cycleSet f` is
the set of entries of `L`. -/
theorem cycleSet_eq_of_list {f : BinForm} {N P : ℕ} {L : List BinForm} (hP : 0 < P)
    (hper : pairSeq f.det (f.a, f.b) (N + P) = pairSeq f.det (f.a, f.b) N)
    (hL : (List.range P).map (fun i => sequenceOf f (N + i)) = L) :
    cycleSet f = {x | x ∈ L} := by
  ext x
  rw [← hL]
  simp only [cycleSet, Set.mem_setOf_eq, List.mem_map, List.mem_range]
  exact mem_recurrentSet_iff (s := sequenceOf f) hP (fun n hn => periodic_of_pairSeq hper n hn) x

theorem not_isSquare_of_between {n k : ℤ} (hk : 0 ≤ k) (h1 : k * k < n) (h2 : n < (k + 1) * (k + 1)) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr : |r| * |r| = r * r := abs_mul_abs_self r
  have h0 : 0 ≤ |r| := abs_nonneg r
  rw [← hr] at h1 h2
  rcases le_or_gt |r| k with h | h
  · nlinarith
  · nlinarith

/-- **Example (8)** (Ch. 15, §3.1, p. 357): the ten reduced forms $a_i^{b_i}a_{i+1}$ of the cycle of
$x^2 - 67y^2$, in order (period of the sequence $\ldots 1^8(-3)\,7\,6\,5\,(-7)\,2\,9\,7\,(-2)\,7\,9\,2\,(-7)\,5\,6\,7\,(-3)\,8\,1\ldots$):
$1^8(-3)$, $(-3)^7 6$, $6^5(-7)$, $(-7)^2 9$, $9^7(-2)$, $(-2)^7 9$, $9^2(-7)$, $(-7)^5 6$, $6^7(-3)$, $(-3)^8 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (8), p. 357"]
def cycle67 : List BinForm :=
  [⟨1, 8, -3⟩, ⟨-3, 7, 6⟩, ⟨6, 5, -7⟩, ⟨-7, 2, 9⟩, ⟨9, 7, -2⟩, ⟨-2, 7, 9⟩, ⟨9, 2, -7⟩, ⟨-7, 5, 6⟩,
    ⟨6, 7, -3⟩, ⟨-3, 8, 1⟩]

/-- **The cycle of $-x^2 + 67y^2$**: that of `cycle67` with the signs of the $a_i$ changed (book: "obtained by
changing the signs of the lower terms in (8) (the $a_i$'s)"). -/
def cycle67neg : List BinForm := cycle67.map fun f => ⟨-f.a, f.b, -f.c⟩

/-- **Example (8), the sequence for $x^2 - 67y^2$:** the forms $f_2, \dots, f_{11}$ of the sequence (5) started at
$1^0(-67)$ are the listed ones (after the pre-period $1^0(-67)$, $(-67)^0 1$), and $(a_{12}, b_{12}) = (a_2, b_2)$,
so the sequence is ultimately periodic with period $10$: the cycle has ten reduced forms. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (8), p. 357"]
theorem example8_cycle :
    UltimatelyPeriodic (sequenceOf ⟨1, 0, -67⟩) ∧ cycleSet ⟨1, 0, -67⟩ = {x | x ∈ cycle67} ∧
      cycle67.length = 10 := by
  have hper : pairSeq (BinForm.det ⟨1, 0, -67⟩) (1, 0) (2 + 10) = pairSeq (BinForm.det ⟨1, 0, -67⟩) (1, 0) 2 := by
    decide +kernel
  have hL : (List.range 10).map (fun i => sequenceOf ⟨1, 0, -67⟩ (2 + i)) = cycle67 := by
    decide +kernel
  exact ⟨⟨2, 10, by norm_num, periodic_of_pairSeq hper⟩,
    cycleSet_eq_of_list (f := ⟨1, 0, -67⟩) (by norm_num) hper hL, by decide⟩

/-- **Example (8), the sequence for $-x^2 + 67y^2$:** its cycle consists of the sign-changed forms. -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (8), p. 357"]
theorem example8_neg_cycle :
    UltimatelyPeriodic (sequenceOf ⟨-1, 0, 67⟩) ∧ cycleSet ⟨-1, 0, 67⟩ = {x | x ∈ cycle67neg} := by
  have hper : pairSeq (BinForm.det ⟨-1, 0, 67⟩) (-1, 0) (2 + 10) = pairSeq (BinForm.det ⟨-1, 0, 67⟩) (-1, 0) 2 := by
    decide +kernel
  have hL : (List.range 10).map (fun i => sequenceOf ⟨-1, 0, 67⟩ (2 + i)) = cycle67neg := by
    decide +kernel
  exact ⟨⟨2, 10, by norm_num, periodic_of_pairSeq hper⟩,
    cycleSet_eq_of_list (f := ⟨-1, 0, 67⟩) (by norm_num) hper hL⟩

/-- **Example (8): the two cycles are disjoint** (as the book says, "the disjoint sequence"). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (8), p. 357"]
theorem example8_disjoint : Disjoint (cycleSet ⟨1, 0, -67⟩) (cycleSet ⟨-1, 0, 67⟩) := by
  rw [example8_cycle.2.1, example8_neg_cycle.2]
  rw [Set.disjoint_left]
  intro x hx hx'
  have : ∀ y ∈ cycle67, y ∉ cycle67neg := by decide
  exact this x hx hx'

/-- **Example (8): $x^2 - 67y^2$ and $-x^2 + 67y^2$ are not properly equivalent** (Ch. 15, §3.1, p. 357). The book
reads this off the disjoint cycles, using the full Theorem 1; here it is proved directly: an equivalence would give
$x^2 - 67y^2 = -1$, impossible modulo $67$ ($-1$ is not a square modulo $67 \equiv 3 \pmod 4$). -/
@[kb "conwaysloane1999" "Ch. 15, §3.1, (8), p. 357"]
theorem example8_not_equiv : ¬ ProperEquiv ⟨1, 0, -67⟩ ⟨-1, 0, 67⟩ := by
  rintro ⟨M, -, hM⟩
  have h00 := congrFun (congrFun hM 0) 0
  simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h00
  have hmod := congrArg (Int.cast : ℤ → ZMod 67) h00
  push_cast at hmod
  have key : ∀ x : ZMod 67, x * x ≠ -1 := by decide
  apply key (M 0 0)
  linear_combination (norm := (ring_nf; try reduce_mod_char)) -hmod

/-! ### Definite forms: the reduction condition (11) -/

/-- **Reduced positive definite binary forms**, Conway–Sloane (11) (Ch. 15, §3.2, p. 358): the form $a^{b}c$ is
reduced iff
$$-a < 2b \le a \le c, \qquad b \ge 0 \text{ if } a = c$$
(the conditions already force $a > 0$; with $d = ac - b^2 > 0$ the form is positive definite). -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (11), p. 358"]
def IsReducedPos (a b c : ℤ) : Prop := -a < 2 * b ∧ 2 * b ≤ a ∧ a ≤ c ∧ (a = c → 0 ≤ b)

instance (a b c : ℤ) : Decidable (IsReducedPos a b c) := by unfold IsReducedPos; infer_instance

/-- **A reduced form has $3b^2 \le d$** (Ch. 15, §3.2, p. 358: "(11) implies $b^2 \le d/3$"), where
$d = ac - b^2$. This bounds $b$ and makes the enumeration of Table 15.1 finite. -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (11), p. 358"]
theorem IsReducedPos.three_sq_le {a b c : ℤ} (h : IsReducedPos a b c) : 3 * b ^ 2 ≤ a * c - b ^ 2 := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have ha : 0 < a := by omega
  have : 4 * b ^ 2 ≤ a ^ 2 := by nlinarith
  nlinarith

/-- **Translation** $M = \begin{pmatrix} 1 & 0\\ k & 1\end{pmatrix}$: $a^{b}c \sim a^{b+ka}(c + 2kb + k^2a)$. -/
theorem translate_equiv (a b c k : ℤ) :
    ProperEquiv ⟨a, b, c⟩ ⟨a, b + k * a, c + 2 * k * b + k ^ 2 * a⟩ := by
  refine ⟨!![1, 0; k, 1], by simp [Matrix.det_fin_two], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Swap** $M = \begin{pmatrix} 0 & 1\\ -1 & 0\end{pmatrix}$: $a^{b}c \sim c^{-b}a$. -/
theorem swap_equiv (a b c : ℤ) : ProperEquiv ⟨a, b, c⟩ ⟨c, -b, a⟩ := by
  refine ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_reduced_aux : ∀ n : ℕ, ∀ a b c : ℤ, 0 < a → a ≤ n → 0 < a * c - b ^ 2 →
    ∃ a' b' c' : ℤ, ProperEquiv ⟨a, b, c⟩ ⟨a', b', c'⟩ ∧ IsReducedPos a' b' c' := by
  intro n
  induction n with
  | zero => intro a b c ha han; omega
  | succ n ih =>
    intro a b c ha han hdet
    have hq := Int.mul_ediv_add_emod (2 * b + a - 1) (2 * a)
    have hr0 := Int.emod_nonneg (2 * b + a - 1) (by omega : (2 * a) ≠ 0)
    have hr1 := Int.emod_lt_of_pos (2 * b + a - 1) (by omega : 0 < 2 * a)
    obtain ⟨q, hqdef⟩ : ∃ q, q = (2 * b + a - 1) / (2 * a) := ⟨_, rfl⟩
    obtain ⟨r, hrdef⟩ : ∃ r, r = (2 * b + a - 1) % (2 * a) := ⟨_, rfl⟩
    rw [← hqdef, ← hrdef] at hq
    rw [← hrdef] at hr0 hr1
    obtain ⟨b', hb'⟩ : ∃ b', b' = b + (-q) * a := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c', c' = c + 2 * (-q) * b + (-q) ^ 2 * a := ⟨_, rfl⟩
    have hb1 : -a < 2 * b' := by rw [hb']; linarith
    have hb2 : 2 * b' ≤ a := by rw [hb']; linarith
    have hdet' : a * c' - b' ^ 2 = a * c - b ^ 2 := by rw [hb', hc']; ring
    have hc0 : 0 < c' := by
      by_contra hh
      push_neg at hh
      nlinarith [sq_nonneg b']
    have e1 : ProperEquiv ⟨a, b, c⟩ ⟨a, b', c'⟩ := by
      rw [hb', hc']; exact translate_equiv a b c (-q)
    by_cases hlt : c' < a
    · obtain ⟨a'', b'', c'', e, hr⟩ := ih c' (-b') a hc0 (by omega) (by nlinarith)
      exact ⟨a'', b'', c'', e1.trans ((swap_equiv a b' c').trans e), hr⟩
    · by_cases h3 : a = c' ∧ b' < 0
      · refine ⟨c', -b', a, e1.trans (swap_equiv a b' c'), ?_⟩
        unfold IsReducedPos
        omega
      · refine ⟨a, b', c', e1, ?_⟩
        unfold IsReducedPos
        omega

/-- **Every positive definite binary form is properly equivalent to a reduced one** (Ch. 15, §3.2, (11), p. 358,
first half of "every positive definite form is properly equivalent to a unique such reduced form"): descent by
translations $b \mapsto b + ka$ and swaps $a^bc \mapsto c^{-b}a$, which strictly decrease $a$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (11), p. 358"]
theorem exists_reduced_pos (f : BinForm) (ha : 0 < f.a) (hd : 0 < f.det) :
    ∃ g : BinForm, ProperEquiv f g ∧ IsReducedPos g.a g.b g.c := by
  obtain ⟨a', b', c', e, hr⟩ := exists_reduced_aux f.a.toNat f.a f.b f.c ha (by omega) hd
  exact ⟨⟨a', b', c'⟩, e, hr⟩

/-- **Minima of a reduced form:** for $a^{b}c$ satisfying (11), $f(x,y) = ax^2 + 2bxy + cy^2 \ge a$ at every nonzero
integral vector and $f(x,y) \ge c$ whenever $y \ne 0$ (the book: "$a$ is the absolutely smallest value taken by the
form, and $c$ the smallest value taken at a vector independent of $e_1$", Ch. 15, §3.2, p. 358). -/
theorem reduced_ge {a b c x y : ℤ} (h : IsReducedPos a b c) (hxy : x ≠ 0 ∨ y ≠ 0) :
    a ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ∧
      (y ≠ 0 → c ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have ha : 0 < a := by omega
  have hxy2 : 1 ≤ x ^ 2 + y ^ 2 := by
    rcases hxy with hx | hy
    · have : 0 < x ^ 2 := by positivity
      nlinarith [sq_nonneg y]
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
  have hy2 : y ≠ 0 → 1 ≤ y ^ 2 := fun hy => by
    have : 0 < y ^ 2 := by positivity
    linarith
  have hca : 0 ≤ c - a := by omega
  rcases le_or_gt 0 (x * y) with hp | hn
  · have t1 : -a * (x * y) ≤ 2 * b * (x * y) := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * b + a by omega) hp]
    have hE : 1 ≤ x ^ 2 - x * y + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
    have t2 := mul_nonneg hca (sq_nonneg y)
    have t3 := mul_nonneg ha.le (sub_nonneg.2 hE)
    refine ⟨by nlinarith, fun hy => ?_⟩
    have t4 := mul_nonneg hca (sub_nonneg.2 (hy2 hy))
    nlinarith
  · have t1 : a * (x * y) ≤ 2 * b * (x * y) := by
      nlinarith [mul_nonneg (show 0 ≤ a - 2 * b by omega) (neg_nonneg.2 hn.le)]
    have hE : 1 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith [sq_nonneg (x + y)]
    have t2 := mul_nonneg hca (sq_nonneg y)
    have t3 := mul_nonneg ha.le (sub_nonneg.2 hE)
    refine ⟨by nlinarith, fun hy => ?_⟩
    have t4 := mul_nonneg hca (sub_nonneg.2 (hy2 hy))
    nlinarith

theorem equiv_entries {f g : BinForm} (h : ProperEquiv f g) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧
      g.a = f.a * p ^ 2 + 2 * f.b * p * q + f.c * q ^ 2 ∧
      g.c = f.a * r ^ 2 + 2 * f.b * r * s + f.c * s ^ 2 ∧
      g.b = f.a * p * r + f.b * (p * s + q * r) + f.c * q * s := by
  obtain ⟨M, hM, hMg⟩ := h
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, M = !![p, q; r, s] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  simp [Matrix.det_fin_two] at hM
  have h00 := congrFun (congrFun hMg 0) 0
  have h01 := congrFun (congrFun hMg 0) 1
  have h11 := congrFun (congrFun hMg 1) 1
  simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  refine ⟨p, q, r, s, hM, by linear_combination h00, by linear_combination h11,
    by linear_combination h01⟩

theorem reduced_ge_of_equiv {f g : BinForm} (hf : IsReducedPos f.a f.b f.c) (hg : IsReducedPos g.a g.b g.c)
    (h : ProperEquiv f g) : f.a ≤ g.a ∧ f.c ≤ g.c := by
  obtain ⟨p, q, r, s, hdet, ha, hc, -⟩ := equiv_entries h
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hh
    push_neg at hh
    rw [hh.1, hh.2] at hdet
    simp at hdet
  refine ⟨ha ▸ (reduced_ge hf hpq).1, ?_⟩
  by_cases hs : s = 0
  · have hq : q ≠ 0 := by
      rintro rfl
      rw [hs] at hdet
      simp at hdet
    have h1 := (reduced_ge hf hpq).2 hq
    have h2 := hg.2.2.1
    rw [← ha] at h1
    omega
  · have := (reduced_ge hf (Or.inr hs : r ≠ 0 ∨ s ≠ 0)).2 hs
    rw [← hc] at this
    exact this

/-- **Uniqueness of the reduced form** (Ch. 15, §3.2, (11), p. 358, second half of "every positive definite form is
properly equivalent to a unique such reduced form"): two properly equivalent reduced forms are equal. Proof: the
minima $a$ and $c$ (`reduced_ge`) are invariants, so $b' = \pm b$; the sign is fixed by the tie conditions of (11),
or, when $a < c$ and $|2b| < a$, because a proper equivalence preserving $a < c$ is a translation. -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (11), p. 358"]
theorem reduced_pos_unique {f g : BinForm} (hf : IsReducedPos f.a f.b f.c) (hg : IsReducedPos g.a g.b g.c)
    (h : ProperEquiv f g) : f = g := by
  have h1 := reduced_ge_of_equiv hf hg h
  have h2 := reduced_ge_of_equiv hg hf h.symm
  have hdet := h.det_eq
  have haa : g.a = f.a := by omega
  have hcc : g.c = f.c := by omega
  simp only [BinForm.det] at hdet
  have hb2 : g.b ^ 2 = f.b ^ 2 := by rw [haa, hcc] at hdet; linarith
  have hb : g.b = f.b ∨ g.b = -f.b := by
    have : (g.b - f.b) * (g.b + f.b) = 0 := by linear_combination hb2
    rcases mul_eq_zero.1 this with h0 | h0
    · left; linarith
    · right; linarith
  have hbb : g.b = f.b := by
    rcases hb with hb | hb
    · exact hb
    · obtain ⟨hf1, hf2, hf3, hf4⟩ := id hf
      obtain ⟨hg1, hg2, hg3, hg4⟩ := id hg
      by_cases hac : f.a = f.c
      · have h5 := hf4 hac
        have h6 := hg4 (by omega)
        omega
      · have hlt : f.a < f.c := lt_of_le_of_ne hf3 hac
        by_cases hb0 : f.b = 0
        · omega
        · -- |2b| < a, since 2b = ±a is excluded by the strict inequalities for b and -b
          have hbl : -f.a < 2 * f.b ∧ 2 * f.b < f.a := by omega
          obtain ⟨p, q, r, s, hdet', ha, -, hbe⟩ := equiv_entries h
          have hq : q = 0 := by
            by_contra hq0
            have := (reduced_ge hf (Or.inr hq0 : p ≠ 0 ∨ q ≠ 0)).2 hq0
            rw [← ha, haa] at this
            omega
          subst hq
          have hp2 : p ^ 2 = 1 := by
            have : f.a * p ^ 2 = f.a * 1 := by rw [mul_one]; linarith
            exact mul_left_cancel₀ (by omega) this
          have hps : p * s = 1 := by linarith
          have hp : p = 1 ∨ p = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hps
          have hr : r = 0 := by
            rcases hp with rfl | rfl
            · have hs : s = 1 := by linarith
              subst hs
              have : f.a * r = -(2 * f.b) := by nlinarith
              by_contra hr0
              rcases lt_or_gt_of_ne hr0 with hrn | hrp
              · nlinarith
              · nlinarith
            · have hs : s = -1 := by linarith
              subst hs
              have : f.a * r = 2 * f.b := by nlinarith
              by_contra hr0
              rcases lt_or_gt_of_ne hr0 with hrn | hrp
              · nlinarith
              · nlinarith
          subst hr
          have : g.b = f.b * (p * s) := by rw [hbe]; ring
          rw [this, hps, mul_one]
  obtain ⟨a, b, c⟩ := f
  obtain ⟨a', b', c'⟩ := g
  simp only at haa hcc hbb
  subst haa hcc hbb
  rfl

/-- **Existence and uniqueness of the reduced form** (11) as one statement: every positive definite form is properly
equivalent to exactly one reduced form (`exists_reduced_pos`, `reduced_pos_unique`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.2, (11), p. 358"]
theorem exists_unique_reduced_pos (f : BinForm) (ha : 0 < f.a) (hd : 0 < f.det) :
    ∃! g : BinForm, ProperEquiv f g ∧ IsReducedPos g.a g.b g.c := by
  obtain ⟨g, e, hg⟩ := exists_reduced_pos f ha hd
  refine ⟨g, ⟨e, hg⟩, ?_⟩
  rintro g' ⟨e', hg'⟩
  exact (reduced_pos_unique hg hg' (e.symm.trans e')).symm

/-! ### Table 15.1 -/

/-- A table entry $a^{b}c$ (one form). -/
def tr (a b c : ℤ) : ℤ × ℤ × ℤ × Bool := (a, b, c, false)

/-- A table entry $a^{\pm b}c$ (both $a^{b}c$ and $a^{-b}c$). -/
def tp (a b c : ℤ) : ℤ × ℤ × ℤ × Bool := (a, b, c, true)

/-- **Table 15.1, "Reduced positive definite binary forms"** (Ch. 15, §3.3, p. 360), encoded as data: the $i$-th
row (starting at $i = 0$) lists the forms for $d = i + 1$, $1 \le d \le 50$, in the book's order; `tr a b c` is the
entry $a^{b}c$ and `tp a b c` is $a^{\pm b}c$ (both signs of $b$). Transcribed from the printed page 360. -/
@[kb "conwaysloane1999" "Ch. 15, Table 15.1, p. 360"]
def table151 : List (List (ℤ × ℤ × ℤ × Bool)) :=
  [ [tr 1 0 1], [tr 1 0 2], [tr 1 0 3, tr 2 1 2], [tr 1 0 4, tr 2 0 2], [tr 1 0 5, tr 2 1 3],
    [tr 1 0 6, tr 2 0 3], [tr 1 0 7, tr 2 1 4], [tr 1 0 8, tr 2 0 4, tr 3 1 3],
    [tr 1 0 9, tr 3 0 3, tr 2 1 5], [tr 1 0 10, tr 2 0 5], [tr 1 0 11, tr 2 1 6, tp 3 1 4],
    [tr 1 0 12, tr 2 0 6, tr 3 0 4, tr 4 2 4], [tr 1 0 13, tr 2 1 7], [tr 1 0 14, tr 2 0 7, tp 3 1 5],
    [tr 1 0 15, tr 3 0 5, tr 2 1 8, tr 4 1 4], [tr 1 0 16, tr 2 0 8, tr 4 0 4, tr 4 2 5],
    [tr 1 0 17, tr 2 1 9, tp 3 1 6], [tr 1 0 18, tr 2 0 9, tr 3 0 6], [tr 1 0 19, tr 2 1 10, tp 4 1 5],
    [tr 1 0 20, tr 2 0 10, tr 4 0 5, tp 3 1 7, tr 4 2 6], [tr 1 0 21, tr 3 0 7, tr 2 1 11, tr 5 2 5],
    [tr 1 0 22, tr 2 0 11], [tr 1 0 23, tr 2 1 12, tp 3 1 8, tp 4 1 6],
    [tr 1 0 24, tr 2 0 12, tr 3 0 8, tr 4 0 6, tr 5 1 5, tr 4 2 7], [tr 1 0 25, tr 5 0 5, tr 2 1 13],
    [tr 1 0 26, tr 2 0 13, tp 3 1 9, tp 5 2 6], [tr 1 0 27, tr 3 0 9, tr 2 1 14, tp 4 1 7, tr 6 3 6],
    [tr 1 0 28, tr 2 0 14, tr 4 0 7, tr 4 2 8], [tr 1 0 29, tr 2 1 15, tp 3 1 10, tp 5 1 6],
    [tr 1 0 30, tr 2 0 15, tr 3 0 10, tr 5 0 6], [tr 1 0 31, tr 2 1 16, tp 4 1 8, tp 5 2 7],
    [tr 1 0 32, tr 2 0 16, tr 4 0 8, tp 3 1 11, tr 4 2 9, tr 6 2 6],
    [tr 1 0 33, tr 3 0 11, tr 2 1 17, tr 6 3 7], [tr 1 0 34, tr 2 0 17, tp 5 1 7],
    [tr 1 0 35, tr 5 0 7, tr 2 1 18, tp 3 1 12, tp 4 1 9, tr 6 1 6],
    [tr 1 0 36, tr 2 0 18, tr 3 0 12, tr 4 0 9, tr 6 0 6, tr 4 2 10, tp 5 2 8],
    [tr 1 0 37, tr 2 1 19], [tr 1 0 38, tr 2 0 19, tp 3 1 13, tp 6 2 7],
    [tr 1 0 39, tr 3 0 13, tr 2 1 20, tp 4 1 10, tp 5 1 8, tr 6 3 8],
    [tr 1 0 40, tr 2 0 20, tr 4 0 10, tr 5 0 8, tr 4 2 11, tr 7 3 7],
    [tr 1 0 41, tr 2 1 21, tp 3 1 14, tp 6 1 7, tp 5 2 9], [tr 1 0 42, tr 2 0 21, tr 3 0 14, tr 6 0 7],
    [tr 1 0 43, tr 2 1 22, tp 4 1 11],
    [tr 1 0 44, tr 2 0 22, tr 4 0 11, tp 3 1 15, tp 5 1 9, tr 4 2 12, tp 6 2 8],
    [tr 1 0 45, tr 3 0 15, tr 5 0 9, tr 2 1 23, tr 7 2 7, tr 6 3 9],
    [tr 1 0 46, tr 2 0 23, tp 5 2 10],
    [tr 1 0 47, tr 2 1 24, tp 3 1 16, tp 4 1 12, tp 6 1 8, tp 7 3 8],
    [tr 1 0 48, tr 2 0 24, tr 3 0 16, tr 4 0 12, tr 6 0 8, tr 7 1 7, tr 4 2 13, tr 8 4 8],
    [tr 1 0 49, tr 7 0 7, tr 2 1 25, tp 5 1 10],
    [tr 1 0 50, tr 2 0 25, tr 5 0 10, tp 3 1 17, tp 6 2 9] ]

/-- **The forms $(a, b, c)$ listed for the determinant $d$ in Table 15.1**, with each "$\pm$" entry expanded to
both signs of $b$ (empty outside $1 \le d \le 50$). -/
def tableTriples (d : ℤ) : List (ℤ × ℤ × ℤ) :=
  ((table151.getD (d - 1).toNat []).flatMap fun e =>
    if e.2.2.2 then [(e.1, e.2.1, e.2.2.1), (e.1, -e.2.1, e.2.2.1)] else [(e.1, e.2.1, e.2.2.1)])

theorem tableTriples_sound :
    ∀ d ∈ Finset.Icc (1 : ℤ) 50, ∀ t ∈ tableTriples d,
      IsReducedPos t.1 t.2.1 t.2.2 ∧ t.1 * t.2.2 - t.2.1 ^ 2 = d := by
  decide +kernel

theorem tableTriples_nodup : ∀ d ∈ Finset.Icc (1 : ℤ) 50, (tableTriples d).Nodup := by
  decide +kernel

theorem tableTriples_complete :
    ∀ d ∈ Finset.Icc (1 : ℤ) 50, ∀ a ∈ Finset.Icc (1 : ℤ) 8, ∀ b ∈ Finset.Icc (-4 : ℤ) 4,
      a ∣ d + b ^ 2 → IsReducedPos a b ((d + b ^ 2) / a) → (a, b, (d + b ^ 2) / a) ∈ tableTriples d := by
  decide +kernel

/-- **Table 15.1 is correct and complete:** for every $1 \le d \le 50$, the forms listed in the row for $d$ (with
"$\pm$" read as both signs) are *exactly* the reduced forms $a^{b}c$ of (11) with $ac - b^2 = d$, each once
(Ch. 15, §3.3, p. 360). Checked by exhaustive enumeration: (11) gives $3b^2 \le d$, so $|b| \le 4$, and $a^2 \le ac
= d + b^2 \le 66$, so $a \le 8$, and $c = (d + b^2)/a$. No discrepancy with the printed table was found. -/
@[kb "conwaysloane1999" "Ch. 15, Table 15.1, p. 360"]
theorem table151_correct {d : ℤ} (hd1 : 1 ≤ d) (hd2 : d ≤ 50) (a b c : ℤ) :
    (IsReducedPos a b c ∧ a * c - b ^ 2 = d) ↔ (a, b, c) ∈ tableTriples d := by
  have hd : d ∈ Finset.Icc (1 : ℤ) 50 := Finset.mem_Icc.2 ⟨hd1, hd2⟩
  constructor
  · rintro ⟨hr, hdet⟩
    have h3 := hr.three_sq_le
    obtain ⟨h1, h2, h4, h5⟩ := hr
    have ha : 0 < a := by omega
    have hb : -4 ≤ b ∧ b ≤ 4 := by constructor <;> nlinarith
    have ha8 : a ≤ 8 := by nlinarith
    have hc : c = (d + b ^ 2) / a := by
      rw [← hdet]; simp only [sub_add_cancel]; exact (Int.mul_ediv_cancel_left c ha.ne').symm
    have hdv : a ∣ d + b ^ 2 := ⟨c, by rw [← hdet]; ring⟩
    subst hc
    exact tableTriples_complete d hd a (Finset.mem_Icc.2 ⟨by omega, ha8⟩) b (Finset.mem_Icc.2 hb) hdv
      ⟨h1, h2, h4, h5⟩
  · intro h
    exact tableTriples_sound d hd _ h

/-! ### Indefinite forms: the reduction condition (12) and Table 15.2 -/

/-- **Reduced indefinite binary forms**, Conway–Sloane (12) (Ch. 15, §3.3, p. 359; Gauss, *Disquisitiones*, §183):
for $-d$ not a square, the forms of the cycles of Theorem 1 are precisely those with
$$0 < b < \sqrt{-d} < \min\{b + |a|,\ b + |c|\},$$
where $-d = b^2 - ac$. With integer inequalities (all quantities positive, so squaring is monotone):
$0 < b$, $b^2 < -d$, $-d < (b + |a|)^2$ and $-d < (b + |c|)^2$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, (12), p. 359"]
def IsReducedIndef (a b c : ℤ) : Prop :=
  0 < b ∧ b ^ 2 < b ^ 2 - a * c ∧ b ^ 2 - a * c < (b + |a|) ^ 2 ∧ b ^ 2 - a * c < (b + |c|) ^ 2

instance (a b c : ℤ) : Decidable (IsReducedIndef a b c) := by unfold IsReducedIndef; infer_instance

/-- **The forms $f_N, \dots, f_{N+P-1}$ of the sequence (5) of $f$**, in order. -/
def cycleForms (f : BinForm) (N P : ℕ) : List BinForm := (List.range P).map fun i => sequenceOf f (N + i)

/-- **Data of a computed cycle:** $P > 0$, $(a_P, b_P) = (a_0, b_0)$ (so the sequence is periodic from the start), and
the forms $f_0, \dots, f_{P-1}$ are the list `L`. Decidable, so verified by `decide`. -/
def CycleData (f : BinForm) (P : ℕ) (L : List BinForm) : Prop :=
  0 < P ∧ pairSeq f.det (f.a, f.b) P = (f.a, f.b) ∧ cycleForms f 0 P = L

instance (f : BinForm) (P : ℕ) (L : List BinForm) : Decidable (CycleData f P L) := by
  unfold CycleData; infer_instance

theorem CycleData.cycleSet_eq {f : BinForm} {P : ℕ} {L : List BinForm} (h : CycleData f P L) :
    UltimatelyPeriodic (sequenceOf f) ∧ cycleSet f = {x | x ∈ L} := by
  obtain ⟨hP, hper, hL⟩ := h
  have hper' : pairSeq f.det (f.a, f.b) (0 + P) = pairSeq f.det (f.a, f.b) 0 := by
    rw [Nat.zero_add, hper]; rfl
  exact ⟨⟨0, P, hP, periodic_of_pairSeq hper'⟩, cycleSet_eq_of_list hP hper' hL⟩

theorem reducedIndef_complete {d B : ℤ} {L : List BinForm} (hB0 : 0 ≤ B) (hB : -d ≤ (B + 1) ^ 2)
    (hcheck : ∀ a ∈ Finset.Icc d (-d), ∀ b ∈ Finset.Icc 1 B, a ∣ d + b ^ 2 →
      IsReducedIndef a b ((d + b ^ 2) / a) → (⟨a, b, (d + b ^ 2) / a⟩ : BinForm) ∈ L)
    (x : BinForm) (h : IsReducedIndef x.a x.b x.c) (hx : x.det = d) : x ∈ L := by
  obtain ⟨a, b, c⟩ := x
  simp only [BinForm.det] at hx h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hac : a * c < 0 := by linarith
  have hbd : b ^ 2 < -d := by linarith
  have hbB : b ≤ B := by
    by_contra hh
    push_neg at hh
    nlinarith
  have ha : a ≠ 0 := by rintro rfl; simp at hac
  have haI : d ≤ a ∧ a ≤ -d := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have hc : 0 < c := by nlinarith
      constructor <;> nlinarith
    · have hc : c < 0 := by nlinarith
      constructor <;> nlinarith
  have hdv : a ∣ d + b ^ 2 := ⟨c, by rw [← hx]; ring⟩
  have hc : c = (d + b ^ 2) / a := by
    rw [← hx]; simp only [sub_add_cancel]; exact (Int.mul_ediv_cancel_left c ha).symm
  have := hcheck a (Finset.mem_Icc.2 haI) b (Finset.mem_Icc.2 ⟨h1, hbB⟩) hdv (by rw [← hc]; exact ⟨h1, h2, h3, h4⟩)
  rwa [← hc] at this

/-- **$d = -13$** (Ch. 15, §3.3, p. 361): the printed entry $\{1^3 4^1 3^2\}$ of Table 15.2 represents the single cycle
$\ldots 1^3(-4)\,1\,3\,2\,(-3)\,1\,4\,3\,(-1)\,3\,4\,1\,(-3)\,2\,3\,1\,(-4)\,3\,1\,3\ldots$ of ten forms, and the entry $\{2^3\}$
the cycle $2^3(-2)\,3\,2\ldots$ of two forms. Checked: both are cycles of Theorem 1's sequence (period lengths
$10$ and $2$), they are disjoint, and together they are *all* the forms satisfying (12) with $d = -13$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 361; Table 15.2a, p. 362"]
theorem indef_d13 :
    CycleData ⟨1, 3, -4⟩ 10 [⟨1, 3, -4⟩, ⟨-4, 1, 3⟩, ⟨3, 2, -3⟩, ⟨-3, 1, 4⟩, ⟨4, 3, -1⟩, ⟨-1, 3, 4⟩,
        ⟨4, 1, -3⟩, ⟨-3, 2, 3⟩, ⟨3, 1, -4⟩, ⟨-4, 3, 1⟩] ∧
    CycleData ⟨2, 3, -2⟩ 2 [⟨2, 3, -2⟩, ⟨-2, 3, 2⟩] ∧
    (∀ x : BinForm, (IsReducedIndef x.a x.b x.c ∧ x.det = -13) ↔
      x ∈ [⟨1, 3, -4⟩, ⟨-4, 1, 3⟩, ⟨3, 2, -3⟩, ⟨-3, 1, 4⟩, ⟨4, 3, -1⟩, ⟨-1, 3, 4⟩,
        ⟨4, 1, -3⟩, ⟨-3, 2, 3⟩, ⟨3, 1, -4⟩, ⟨-4, 3, 1⟩, ⟨2, 3, -2⟩, ⟨-2, 3, 2⟩]) ∧
    [(⟨1, 3, -4⟩ : BinForm), ⟨-4, 1, 3⟩, ⟨3, 2, -3⟩, ⟨-3, 1, 4⟩, ⟨4, 3, -1⟩, ⟨-1, 3, 4⟩,
        ⟨4, 1, -3⟩, ⟨-3, 2, 3⟩, ⟨3, 1, -4⟩, ⟨-4, 3, 1⟩, ⟨2, 3, -2⟩, ⟨-2, 3, 2⟩].Nodup := by
  refine ⟨by decide +kernel, by decide +kernel, fun x => ⟨fun ⟨h, hx⟩ => ?_, fun hx => ?_⟩, by decide +kernel⟩
  · exact reducedIndef_complete (d := -13) (B := 3) (by norm_num) (by norm_num) (by decide +kernel) x h hx
  · have : ∀ y ∈ [(⟨1, 3, -4⟩ : BinForm), ⟨-4, 1, 3⟩, ⟨3, 2, -3⟩, ⟨-3, 1, 4⟩, ⟨4, 3, -1⟩, ⟨-1, 3, 4⟩,
        ⟨4, 1, -3⟩, ⟨-3, 2, 3⟩, ⟨3, 1, -4⟩, ⟨-4, 3, 1⟩, ⟨2, 3, -2⟩, ⟨-2, 3, 2⟩],
        IsReducedIndef y.a y.b y.c ∧ y.det = -13 := by decide +kernel
    exact this x hx

/-- **$d = -14$** (p. 361): the entry $\{1^3 5^2 2\}$ represents the two cycles
$\ldots 1^3(-5)\,2\,2\,(-5)\,3\ldots$ and $\ldots(-1)\,3\,5\,2\,(-2)\,2\,5\,3\ldots$ (four forms each); together they are
all the forms satisfying (12) with $d = -14$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 361; Table 15.2a, p. 362"]
theorem indef_d14 :
    CycleData ⟨1, 3, -5⟩ 4 [⟨1, 3, -5⟩, ⟨-5, 2, 2⟩, ⟨2, 2, -5⟩, ⟨-5, 3, 1⟩] ∧
    CycleData ⟨-1, 3, 5⟩ 4 [⟨-1, 3, 5⟩, ⟨5, 2, -2⟩, ⟨-2, 2, 5⟩, ⟨5, 3, -1⟩] ∧
    (∀ x : BinForm, (IsReducedIndef x.a x.b x.c ∧ x.det = -14) ↔
      x ∈ [⟨1, 3, -5⟩, ⟨-5, 2, 2⟩, ⟨2, 2, -5⟩, ⟨-5, 3, 1⟩,
        ⟨-1, 3, 5⟩, ⟨5, 2, -2⟩, ⟨-2, 2, 5⟩, ⟨5, 3, -1⟩]) ∧
    [(⟨1, 3, -5⟩ : BinForm), ⟨-5, 2, 2⟩, ⟨2, 2, -5⟩, ⟨-5, 3, 1⟩,
        ⟨-1, 3, 5⟩, ⟨5, 2, -2⟩, ⟨-2, 2, 5⟩, ⟨5, 3, -1⟩].Nodup := by
  refine ⟨by decide +kernel, by decide +kernel, fun x => ⟨fun ⟨h, hx⟩ => ?_, fun hx => ?_⟩, by decide +kernel⟩
  · exact reducedIndef_complete (d := -14) (B := 3) (by norm_num) (by norm_num) (by decide +kernel) x h hx
  · have : ∀ y ∈ [(⟨1, 3, -5⟩ : BinForm), ⟨-5, 2, 2⟩, ⟨2, 2, -5⟩, ⟨-5, 3, 1⟩,
        ⟨-1, 3, 5⟩, ⟨5, 2, -2⟩, ⟨-2, 2, 5⟩, ⟨5, 3, -1⟩],
        IsReducedIndef y.a y.b y.c ∧ y.det = -14 := by decide +kernel
    exact this x hx

/-- **$d = -37$** (p. 361): the entry $(3^5 4^3 7^4)$ is the cycle
$\ldots 3^5(-4)\,3\,7\,4\,(-3)\,5\,4\,3\,(-7)\,4\,3\ldots$ of six forms, and its reversal (the forms read backwards)
is another one, as the book says ("only two inequivalent cycles"). The entries $\{1^6 1\}$ and $\{2^5 6^1\}$ give a
cycle of two forms and one of six; together the four cycles are all $20$ forms satisfying (12) with $d = -37$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 361; Table 15.2a, p. 362"]
theorem indef_d37 :
    CycleData ⟨3, 5, -4⟩ 6 [⟨3, 5, -4⟩, ⟨-4, 3, 7⟩, ⟨7, 4, -3⟩, ⟨-3, 5, 4⟩, ⟨4, 3, -7⟩, ⟨-7, 4, 3⟩] ∧
    CycleData ⟨3, 4, -7⟩ 6 [⟨3, 4, -7⟩, ⟨-7, 3, 4⟩, ⟨4, 5, -3⟩, ⟨-3, 4, 7⟩, ⟨7, 3, -4⟩, ⟨-4, 5, 3⟩] ∧
    CycleData ⟨6, 1, -6⟩ 6 [⟨6, 1, -6⟩, ⟨-6, 5, 2⟩, ⟨2, 5, -6⟩, ⟨-6, 1, 6⟩, ⟨6, 5, -2⟩, ⟨-2, 5, 6⟩] ∧
    CycleData ⟨1, 6, -1⟩ 2 [⟨1, 6, -1⟩, ⟨-1, 6, 1⟩] ∧
    (∀ x : BinForm, (IsReducedIndef x.a x.b x.c ∧ x.det = -37) ↔
      x ∈ [⟨3, 5, -4⟩, ⟨-4, 3, 7⟩, ⟨7, 4, -3⟩, ⟨-3, 5, 4⟩, ⟨4, 3, -7⟩, ⟨-7, 4, 3⟩,
        ⟨3, 4, -7⟩, ⟨-7, 3, 4⟩, ⟨4, 5, -3⟩, ⟨-3, 4, 7⟩, ⟨7, 3, -4⟩, ⟨-4, 5, 3⟩,
        ⟨6, 1, -6⟩, ⟨-6, 5, 2⟩, ⟨2, 5, -6⟩, ⟨-6, 1, 6⟩, ⟨6, 5, -2⟩, ⟨-2, 5, 6⟩,
        ⟨1, 6, -1⟩, ⟨-1, 6, 1⟩]) ∧
    [(⟨3, 5, -4⟩ : BinForm), ⟨-4, 3, 7⟩, ⟨7, 4, -3⟩, ⟨-3, 5, 4⟩, ⟨4, 3, -7⟩, ⟨-7, 4, 3⟩,
        ⟨3, 4, -7⟩, ⟨-7, 3, 4⟩, ⟨4, 5, -3⟩, ⟨-3, 4, 7⟩, ⟨7, 3, -4⟩, ⟨-4, 5, 3⟩,
        ⟨6, 1, -6⟩, ⟨-6, 5, 2⟩, ⟨2, 5, -6⟩, ⟨-6, 1, 6⟩, ⟨6, 5, -2⟩, ⟨-2, 5, 6⟩,
        ⟨1, 6, -1⟩, ⟨-1, 6, 1⟩].Nodup := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun x => ⟨fun ⟨h, hx⟩ => ?_, fun hx => ?_⟩, by decide +kernel⟩
  · exact reducedIndef_complete (d := -37) (B := 6) (by norm_num) (by norm_num) (by decide +kernel) x h hx
  · have : ∀ y ∈ [(⟨3, 5, -4⟩ : BinForm), ⟨-4, 3, 7⟩, ⟨7, 4, -3⟩, ⟨-3, 5, 4⟩, ⟨4, 3, -7⟩, ⟨-7, 4, 3⟩,
        ⟨3, 4, -7⟩, ⟨-7, 3, 4⟩, ⟨4, 5, -3⟩, ⟨-3, 4, 7⟩, ⟨7, 3, -4⟩, ⟨-4, 5, 3⟩,
        ⟨6, 1, -6⟩, ⟨-6, 5, 2⟩, ⟨2, 5, -6⟩, ⟨-6, 1, 6⟩, ⟨6, 5, -2⟩, ⟨-2, 5, 6⟩,
        ⟨1, 6, -1⟩, ⟨-1, 6, 1⟩],
        IsReducedIndef y.a y.b y.c ∧ y.det = -37 := by decide +kernel
    exact this x hx

/-! ### The square case $-d = b^2$ (§3.3): Gauss' criterion -/

/-- **Gauss' criterion for the square case** (Ch. 15, §3.3, p. 359; Gauss, *Disquisitiones*, §§206–210): for
$b > 0$, the forms $a^{b}0$ and $a'^{b}0$ (determinant $-b^2$) are properly equivalent iff $a \equiv a' \pmod{2b}$.
This proposition is *proved* below (`gauss_square_criterion`); the book's companion statement about improper
equivalence ($aa' \equiv \gcd(a,b)^2 \pmod{2b\gcd(a,b)}$) is not formalized. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
def GaussSquareCriterion : Prop :=
  ∀ a a' b : ℤ, 0 < b → (ProperEquiv ⟨a, b, 0⟩ ⟨a', b, 0⟩ ↔ a ≡ a' [ZMOD 2 * b])

/-- **Gauss' criterion, "if":** $a \equiv a' \pmod{2b}$ gives $a^{b}0 \sim a'^{b}0$ via
$M = \begin{pmatrix} 1 & k\\ 0 & 1\end{pmatrix}$, $a' = a + 2bk$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
theorem gauss_square_if {a a' b : ℤ} (h : a ≡ a' [ZMOD 2 * b]) :
    ProperEquiv ⟨a, b, 0⟩ ⟨a', b, 0⟩ := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h
  refine ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two], ?_⟩
  have : a' = a + 2 * b * k := by linarith
  subst this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Gauss' criterion, "only if":** a proper equivalence $a^{b}0 \sim a'^{b}0$ ($b > 0$) has the lower-left entry
$r$ of $M$ equal to $0$ (the $(2,2)$ entry gives $r(ar + 2bs) = 0$, and $ar + 2bs = 0$ would force $\det M = -1$),
hence $p = s = \pm 1$ and $a' = a + 2bpq$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
theorem gauss_square_only_if {a a' b : ℤ} (hb : 0 < b) (h : ProperEquiv ⟨a, b, 0⟩ ⟨a', b, 0⟩) :
    a ≡ a' [ZMOD 2 * b] := by
  obtain ⟨M, hM, hMg⟩ := h
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, M = !![p, q; r, s] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  simp [Matrix.det_fin_two] at hM
  have h00 := congrFun (congrFun hMg 0) 0
  have h01 := congrFun (congrFun hMg 0) 1
  have h11 := congrFun (congrFun hMg 1) 1
  simp [BinForm.gram, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  have hr : r * (a * r + 2 * b * s) = 0 := by linear_combination -h11
  rcases mul_eq_zero.1 hr with hr0 | hr1
  · subst hr0
    have hps : p * s = 1 := by linarith
    have hp : p = 1 ∨ p = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hps
    have hp2 : p ^ 2 = 1 := by rcases hp with rfl | rfl <;> norm_num
    apply Int.modEq_iff_dvd.2
    exact ⟨p * q, by linear_combination h00 + a * hp2⟩
  · exfalso
    have : b * (q * r - p * s) = b := by linear_combination -h01 - p * hr1
    have h2 : q * r - p * s = 1 := by
      have := mul_left_cancel₀ hb.ne' (this.trans (mul_one b).symm)
      exact this
    linarith

/-- **Gauss' criterion for the square case, proved.** -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, p. 359"]
theorem gauss_square_criterion : GaussSquareCriterion :=
  fun _ _ _ hb => ⟨gauss_square_only_if hb, gauss_square_if⟩

end Binary

end ConwaySloane

end QuadFormsKB
