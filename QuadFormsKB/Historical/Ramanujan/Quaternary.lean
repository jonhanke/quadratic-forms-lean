/-
# Ramanujan's universal diagonal quaternary forms (1917, § 2), with Dickson's correction, and Liouville's forms

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Ramanujan 1917, § 2, (2.1)–(2.471), *Collected Papers* pp. 169–170, occurrence
  `ramanujan1927-papers:p20.s2.necessary`): the escalation conditions. If $ax^2 + by^2 + cz^2 + du^2$ with
  $1 \le a \le b \le c \le d$ represents every positive integer, then $a = 1$, $b \le 2$, $c \le 3$ if $b = 1$, $c \le 5$
  if $b = 2$, and $d \le 7, 14, 6, 7, 10, 14, 10$ for $(a, b, c) = (1,1,1), (1,1,2), (1,1,3), (1,2,2), (1,2,3), (1,2,4),
  (1,2,5)$ (`ramanujan_escalation`). **Proved.**
* (same, § 2, table, p. 170): the positive diagonal forms
  representing every positive integer are exactly the 54 forms of `RamanujanList` (Ramanujan lists 55; his
  $(1, 2, 5, 5)$ misses $15$, as Dickson observed in 1927: `not_rep_1255_15`, an *erratum*).
  * *Necessity* (`ramanujan_necessary`): **proved** (escalation and $(1,2,5,5)$).
  * *Sufficiency*: **proved for 39 of the 54 forms** (`universal_of_ramanujanList`): 38 through a ternary sub-form
    whose exceptions follow from Legendre's three-squares theorem (`Ternary.lean`), choosing the fourth variable
    $t \in \{0, 1, 2\}$ by the residue of $n$; and $(1, 2, 3, 6)$ through Lagrange's four squares
    (`universal_1236`). The remaining 15 forms (`RemainingForm`: $(1,1,3,d)$, $d = 3, \dots, 6$; $(1,2,3,d)$,
    $d = 3, 5, 7, 8, 9, 10$; $(1,2,5,d)$, $d = 6, \dots, 10$) are `RamanujanRemaining`, **stated**; the full
    classification `RamanujanClassification` is **proved equivalent** to it (`ramanujanClassification_iff`).
* (Dickson, *History* III): every positive integer is
  $x^2 + 2y^2 + 3z^2 + 6t^2$ (`universal_1236`). **Proved.**
* : every four-square representation gives one by
  $x^2 + 2y^2 + 3z^2 + 6t^2$ (`rep_1236_of_four_squares`). **Proved.**
* (Smith, *Collected Mathematical Papers* II) and 
  (Dickson, *History* III): every positive integer is represented by
  $x^2 + y^2 + 3u^2 + 3v^2$ and by $x^2 + 2y^2 + 3u^2 + 6v^2$. **Partial:** the second form is `universal_1236`; the first
  is `Universal1133`, **stated** (it is one of the 15 remaining forms).

**Proof of `universal_1236`.** Given $n = a^2 + b^2 + c^2 + d^2$, reorder and change signs so that $3 \mid a + b + c$
(possible unless exactly one of $a, b, c, d$ is prime to $3$, and then the other three are divisible by $3$). With
$a + b + c = 3w$, $p = a - b$, $q = b - c$ ($p \equiv q \bmod 3$, $q = p + 3r$), $a^2 + b^2 + c^2 = 3w^2 + 2N$ with
$N = s^2 + st + t^2$, $s = p + r$, $t = r$. Rotating $(s, t) \mapsto (-t, s + t)$ makes $t$ even, $t = 2k$, and then
$N = (s + k)^2 + 3k^2$, so $n = d^2 + 2(s + k)^2 + 3w^2 + 6k^2$.

**Conventions.** $x, y, z, t \in \mathbb Z$; `Rep4 a b c d n` means $ax^2 + by^2 + cz^2 + dt^2 = n$; "universal" means
every $n \in \mathbb N$ is represented ($n = 0$ trivially).
-/
import QuadFormsKB.Historical.Ramanujan.Ternary

namespace QuadFormsKB.Historical.Ramanujan

/-- **$n$ is represented by $ax^2 + by^2 + cz^2 + dt^2$** ($x, y, z, t \in \mathbb Z$). -/
def Rep4 (a b c d n : ℕ) : Prop := ∃ x y z t : ℤ, (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * t ^ 2 = n

/-- **$ax^2 + by^2 + cz^2 + dt^2$ represents every natural number.** -/
def Universal4 (a b c d : ℕ) : Prop := ∀ n : ℕ, Rep4 a b c d n

/-- **Ramanujan's list, corrected** (54 forms, $a \le b \le c \le d$): $(1,1,1,d)$, $1 \le d \le 7$; $(1,1,2,d)$,
$2 \le d \le 14$; $(1,1,3,d)$, $3 \le d \le 6$; $(1,2,2,d)$, $2 \le d \le 7$; $(1,2,3,d)$, $3 \le d \le 10$;
$(1,2,4,d)$, $4 \le d \le 14$; $(1,2,5,d)$, $6 \le d \le 10$. -/
def RamanujanList (a b c d : ℕ) : Prop :=
  a = 1 ∧ ((b = 1 ∧ c = 1 ∧ 1 ≤ d ∧ d ≤ 7) ∨ (b = 1 ∧ c = 2 ∧ 2 ≤ d ∧ d ≤ 14) ∨
    (b = 1 ∧ c = 3 ∧ 3 ≤ d ∧ d ≤ 6) ∨ (b = 2 ∧ c = 2 ∧ 2 ≤ d ∧ d ≤ 7) ∨ (b = 2 ∧ c = 3 ∧ 3 ≤ d ∧ d ≤ 10) ∨
    (b = 2 ∧ c = 4 ∧ 4 ≤ d ∧ d ≤ 14) ∨ (b = 2 ∧ c = 5 ∧ 6 ≤ d ∧ d ≤ 10))

/-- **The 15 forms of the list not proved universal here:** $(1,1,3,d)$, $3 \le d \le 6$; $(1,2,3,d)$,
$d \in \{3, 5, 7, 8, 9, 10\}$; $(1,2,5,d)$, $6 \le d \le 10$. -/
def RemainingForm (a b c d : ℕ) : Prop :=
  a = 1 ∧ ((b = 1 ∧ c = 3 ∧ 3 ≤ d ∧ d ≤ 6) ∨
    (b = 2 ∧ c = 3 ∧ (d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10)) ∨ (b = 2 ∧ c = 5 ∧ 6 ≤ d ∧ d ≤ 10))

/-- A term $e x^2 \le k < e$ forces $x = 0$. -/
private theorem sq_zero_of_lt (e k : ℕ) (hk : k < e) (x : ℤ) (h : (e : ℤ) * x ^ 2 ≤ k) : x = 0 := by
  by_contra hx
  have hpos : 0 < x ^ 2 := by positivity
  have he : (k : ℤ) + 1 ≤ e := by exact_mod_cast hk
  nlinarith [mul_nonneg (Nat.cast_nonneg e : (0:ℤ) ≤ e) (show (0:ℤ) ≤ x ^ 2 - 1 by omega)]

/-- If every coefficient exceeds $k \ne 0$, then $ax^2+by^2+cz^2+dt^2 = k$ is impossible. -/
private theorem miss0 (k a b c d : ℕ) (hk : k ≠ 0) (ha : k < a) (hb : k < b) (hc : k < c) (hd : k < d)
    (h : Rep4 a b c d k) : False := by
  obtain ⟨x, y, z, t, h⟩ := h
  have h0 : (0:ℤ) ≤ (a:ℤ) * x ^ 2 := by positivity
  have h1 : (0:ℤ) ≤ (b:ℤ) * y ^ 2 := by positivity
  have h2 : (0:ℤ) ≤ (c:ℤ) * z ^ 2 := by positivity
  have h3 : (0:ℤ) ≤ (d:ℤ) * t ^ 2 := by positivity
  have hx := sq_zero_of_lt a k ha x (by linarith)
  have hy := sq_zero_of_lt b k hb y (by linarith)
  have hz := sq_zero_of_lt c k hc z (by linarith)
  have ht := sq_zero_of_lt d k hd t (by linarith)
  subst hx hy hz ht
  simp at h
  omega

/-- If $b,c,d > k$ then $ax^2+by^2+cz^2+dt^2=k$ reduces to $ax^2=k$. -/
private theorem miss1 (a k b c d : ℕ) (hno : ∀ x : ℤ, (a : ℤ) * x ^ 2 ≠ k) (hb : k < b) (hc : k < c)
    (hd : k < d) (h : Rep4 a b c d k) : False := by
  obtain ⟨x, y, z, t, h⟩ := h
  have h0 : (0:ℤ) ≤ (a:ℤ) * x ^ 2 := by positivity
  have h1 : (0:ℤ) ≤ (b:ℤ) * y ^ 2 := by positivity
  have h2 : (0:ℤ) ≤ (c:ℤ) * z ^ 2 := by positivity
  have h3 : (0:ℤ) ≤ (d:ℤ) * t ^ 2 := by positivity
  have hy := sq_zero_of_lt b k hb y (by linarith)
  have hz := sq_zero_of_lt c k hc z (by linarith)
  have ht := sq_zero_of_lt d k hd t (by linarith)
  subst hy hz ht
  exact hno x (by simpa using h)

/-- If $c,d > k$ then $ax^2+by^2+cz^2+dt^2=k$ reduces to $ax^2+by^2=k$. -/
private theorem miss2 (a b k c d : ℕ) (hno : ∀ x y : ℤ, (a : ℤ) * x ^ 2 + (b : ℤ) * y ^ 2 ≠ k)
    (hc : k < c) (hd : k < d) (h : Rep4 a b c d k) : False := by
  obtain ⟨x, y, z, t, h⟩ := h
  have h0 : (0:ℤ) ≤ (a:ℤ) * x ^ 2 := by positivity
  have h1 : (0:ℤ) ≤ (b:ℤ) * y ^ 2 := by positivity
  have h2 : (0:ℤ) ≤ (c:ℤ) * z ^ 2 := by positivity
  have h3 : (0:ℤ) ≤ (d:ℤ) * t ^ 2 := by positivity
  have hz := sq_zero_of_lt c k hc z (by linarith)
  have ht := sq_zero_of_lt d k hd t (by linarith)
  subst hz ht
  exact hno x y (by simpa using h)

/-- If $d > k$ then $ax^2+by^2+cz^2+dt^2=k$ reduces to $ax^2+by^2+cz^2=k$. -/
private theorem miss3 (a b c k d : ℕ)
    (hno : ∀ x y z : ℤ, (a : ℤ) * x ^ 2 + (b : ℤ) * y ^ 2 + (c : ℤ) * z ^ 2 ≠ k) (hd : k < d)
    (h : Rep4 a b c d k) : False := by
  obtain ⟨x, y, z, t, h⟩ := h
  have h0 : (0:ℤ) ≤ (a:ℤ) * x ^ 2 := by positivity
  have h1 : (0:ℤ) ≤ (b:ℤ) * y ^ 2 := by positivity
  have h2 : (0:ℤ) ≤ (c:ℤ) * z ^ 2 := by positivity
  have h3 : (0:ℤ) ≤ (d:ℤ) * t ^ 2 := by positivity
  have ht := sq_zero_of_lt d k hd t (by linarith)
  subst ht
  exact hno x y z (by simpa using h)

set_option maxHeartbeats 1600000 in
/-- $x^2 + 2y^2 + 5z^2 + 5t^2 \ne 15$ over $\mathbb Z$ (bounded search). -/
private theorem no1255_15 (x y z t : ℤ)
    (h : ((1:ℕ):ℤ) * x ^ 2 + ((2:ℕ):ℤ) * y ^ 2 + ((5:ℕ):ℤ) * z ^ 2 + ((5:ℕ):ℤ) * t ^ 2 = ((15:ℕ):ℤ)) :
    False := by
  push_cast at h
  have hx : -3 ≤ x ∧ x ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]
  have ht : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg t]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨ht1, ht2⟩ := ht
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases t <;> omega


/-- No integers satisfy $1x^2 = 2$. -/
private theorem no_1_2 : ∀ x : ℤ, (((1:ℕ)):ℤ) * x ^ 2 ≠ ((2:ℕ):ℤ) := by
  intro x h
  push_cast at h
  have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
  obtain ⟨hx1, hx2⟩ := hx
  interval_cases x <;> omega

/-- No integers satisfy $1x^2 + 1y^2 = 3$. -/
private theorem no_1_1_3 : ∀ x y : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((1:ℕ)):ℤ) * y ^ 2 ≠ ((3:ℕ):ℤ) := by
  intro x y h
  push_cast at h
  have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> omega

/-- No integers satisfy $1x^2 + 2y^2 = 5$. -/
private theorem no_1_2_5 : ∀ x y : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((2:ℕ)):ℤ) * y ^ 2 ≠ ((5:ℕ):ℤ) := by
  intro x y h
  push_cast at h
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> omega

/-- No integers satisfy $1x^2 + 1y^2 + 1z^2 = 7$. -/
private theorem no_1_1_1_7 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((1:ℕ)):ℤ) * y ^ 2 + (((1:ℕ)):ℤ) * z ^ 2 ≠ ((7:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -2 ≤ z ∧ z ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 1y^2 + 2z^2 = 14$. -/
private theorem no_1_1_2_14 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((1:ℕ)):ℤ) * y ^ 2 + (((2:ℕ)):ℤ) * z ^ 2 ≠ ((14:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -3 ≤ x ∧ x ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -3 ≤ y ∧ y ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -2 ≤ z ∧ z ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 1y^2 + 3z^2 = 6$. -/
private theorem no_1_1_3_6 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((1:ℕ)):ℤ) * y ^ 2 + (((3:ℕ)):ℤ) * z ^ 2 ≠ ((6:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 2y^2 + 2z^2 = 7$. -/
private theorem no_1_2_2_7 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((2:ℕ)):ℤ) * y ^ 2 + (((2:ℕ)):ℤ) * z ^ 2 ≠ ((7:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 2y^2 + 3z^2 = 10$. -/
private theorem no_1_2_3_10 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((2:ℕ)):ℤ) * y ^ 2 + (((3:ℕ)):ℤ) * z ^ 2 ≠ ((10:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -3 ≤ x ∧ x ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 2y^2 + 4z^2 = 14$. -/
private theorem no_1_2_4_14 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((2:ℕ)):ℤ) * y ^ 2 + (((4:ℕ)):ℤ) * z ^ 2 ≠ ((14:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -3 ≤ x ∧ x ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- No integers satisfy $1x^2 + 2y^2 + 5z^2 = 10$. -/
private theorem no_1_2_5_10 : ∀ x y z : ℤ, (((1:ℕ)):ℤ) * x ^ 2 + (((2:ℕ)):ℤ) * y ^ 2 + (((5:ℕ)):ℤ) * z ^ 2 ≠ ((10:ℕ):ℤ) := by
  intro x y z h
  push_cast at h
  have hx : -3 ≤ x ∧ x ≤ 3 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- **Escalation** (Ramanujan 1917, § 2): if $ax^2 + by^2 + cz^2 + dt^2$,
$1 \le a \le b \le c \le d$, represents every natural number, then $a = 1$, $b \le 2$, $c \le 3$ if $b = 1$,
$c \le 5$ if $b = 2$, and $d$ is at most $7, 14, 6, 7, 10, 14, 10$ for
$(b, c) = (1,1), (1,2), (1,3), (2,2), (2,3), (2,4), (2,5)$ (the first integer missed otherwise). -/
@[kb "ramanujan1917" "§ 2, (2.1)–(2.471), Collected Papers pp. 169–170 (occurrence ramanujan1927-papers:p20.s2.necessary)"]
theorem ramanujan_escalation {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hU : Universal4 a b c d) :
    a = 1 ∧ b ≤ 2 ∧ (b = 1 → c ≤ 3) ∧ (b = 2 → c ≤ 5) ∧
      (b = 1 → c = 1 → d ≤ 7) ∧ (b = 1 → c = 2 → d ≤ 14) ∧ (b = 1 → c = 3 → d ≤ 6) ∧
      (b = 2 → c = 2 → d ≤ 7) ∧ (b = 2 → c = 3 → d ≤ 10) ∧ (b = 2 → c = 4 → d ≤ 14) ∧
      (b = 2 → c = 5 → d ≤ 10) := by
  have ha1 : a = 1 := by
    by_contra hne
    exact miss0 1 a b c d (by norm_num) (by omega) (by omega) (by omega) (by omega) (hU 1)
  subst ha1
  have hb2 : b ≤ 2 := by
    by_contra hne
    exact miss1 1 2 b c d no_1_2 (by omega) (by omega) (by omega) (hU 2)
  refine ⟨rfl, hb2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb; subst hb
    by_contra hne
    exact miss2 1 1 3 c d no_1_1_3 (by omega) (by omega) (hU 3)
  · intro hb; subst hb
    by_contra hne
    exact miss2 1 2 5 c d no_1_2_5 (by omega) (by omega) (hU 5)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 1 1 7 d no_1_1_1_7 (by omega) (hU 7)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 1 2 14 d no_1_1_2_14 (by omega) (hU 14)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 1 3 6 d no_1_1_3_6 (by omega) (hU 6)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 2 2 7 d no_1_2_2_7 (by omega) (hU 7)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 2 3 10 d no_1_2_3_10 (by omega) (hU 10)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 2 4 14 d no_1_2_4_14 (by omega) (hU 14)
  · intro hb hc; subst hb; subst hc
    by_contra hne
    exact miss3 1 2 5 10 d no_1_2_5_10 (by omega) (hU 10)

/-- **Dickson's correction to Ramanujan's list** (*erratum*): $x^2 + 2y^2 + 5z^2 + 5t^2$,
the 55th form of Ramanujan's table, does not represent $15$. -/
@[kb "ramanujan1917" "§ 2, table, Collected Papers p. 170 (occurrence ramanujan1927-papers:p20.s2.verify)"]
theorem not_rep_1255_15 : ¬ Rep4 1 2 5 5 15 := by
  rintro ⟨x, y, z, t, h⟩
  exact no1255_15 x y z t h

/-- **Ramanujan's classification, necessity**: a universal diagonal form
$ax^2 + by^2 + cz^2 + dt^2$, $1 \le a \le b \le c \le d$, is one of the 54 forms of `RamanujanList`. -/
@[kb "ramanujan1917" "§ 2, Collected Papers pp. 169–170"]
theorem ramanujan_necessary {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hU : Universal4 a b c d) : RamanujanList a b c d := by
  obtain ⟨rfl, hb2, hc1, hc2, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ :=
    ramanujan_escalation ha hab hbc hcd hU
  have h55 : b = 2 → c = 5 → d ≠ 5 := by
    intro hb hc hd
    subst hb; subst hc; subst hd
    exact not_rep_1255_15 (hU 15)
  refine ⟨rfl, ?_⟩
  have hb : b = 1 ∨ b = 2 := by omega
  rcases hb with rfl | rfl
  · have hc : c = 1 ∨ c = 2 ∨ c = 3 := by have := hc1 rfl; omega
    rcases hc with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl, by omega, hd1 rfl rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, by omega, hd2 rfl rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, hd3 rfl rfl⟩))
  · have hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by have := hc2 rfl; omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, hd4 rfl rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, hd5 rfl rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, hd6 rfl rfl⟩)))))
    · have := h55 rfl rfl
      have := hd7 rfl rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by omega, by omega⟩)))))

/-- If $p+q+r=0$ and $q$ is even, then $(p+w)^2+(q+w)^2+(r+w)^2+d^2 = x^2+2y^2+3z^2+6t^2$ is solvable. -/
private theorem rep1236_core2 (p q r w d : ℤ) (n : ℕ) (hs : p + q + r = 0) (hq : q % 2 = 0)
    (h : (p + w) ^ 2 + (q + w) ^ 2 + (r + w) ^ 2 + d ^ 2 = n) : Rep4 1 2 3 6 n := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k := ⟨q / 2, by omega⟩
  have hr : r = -p - 2 * k := by omega
  subst hk hr
  exact ⟨d, p + k, w, k, by push_cast; linarith⟩

/-- If $3 \mid a+b+c$ then $a^2+b^2+c^2+d^2 = x^2+2y^2+3z^2+6t^2$ is solvable. -/
private theorem rep1236_core (a b c d : ℤ) (n : ℕ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n)
    (h3 : (a + b + c) % 3 = 0) : Rep4 1 2 3 6 n := by
  obtain ⟨w, hw⟩ : ∃ w, a + b + c = 3 * w := ⟨(a + b + c) / 3, by omega⟩
  have hs : (a - w) + (b - w) + (c - w) = 0 := by linarith
  have : (b - w) % 2 = 0 ∨ (a - w) % 2 = 0 ∨ (c - w) % 2 = 0 := by omega
  rcases this with h1 | h1 | h1
  · exact rep1236_core2 (a - w) (b - w) (c - w) w d n hs h1 (by linarith)
  · exact rep1236_core2 (b - w) (a - w) (c - w) w d n (by linarith) h1 (by linarith)
  · exact rep1236_core2 (a - w) (c - w) (b - w) w d n (by linarith) h1 (by linarith)

/-- Among four integers, after sign changes and reordering, three have sum divisible by $3$ and the
sum of squares is unchanged. -/
private theorem pick_triple (a b c d : ℤ) :
    ∃ a' b' c' d' : ℤ, a' ^ 2 + b' ^ 2 + c' ^ 2 + d' ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ∧
      (a' + b' + c') % 3 = 0 := by
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hc : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  have hd : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rcases hc with hc | hc | hc <;>
    rcases hd with hd | hd | hd <;>
    first
    | exact ⟨a, b, c, d, rfl, by omega⟩
    | exact ⟨a, b, -c, d, by ring, by omega⟩
    | exact ⟨a, -b, c, d, by ring, by omega⟩
    | exact ⟨a, -b, -c, d, by ring, by omega⟩
    | exact ⟨a, b, d, c, by ring, by omega⟩
    | exact ⟨a, b, -d, c, by ring, by omega⟩
    | exact ⟨a, -b, d, c, by ring, by omega⟩
    | exact ⟨a, -b, -d, c, by ring, by omega⟩
    | exact ⟨a, c, d, b, by ring, by omega⟩
    | exact ⟨a, c, -d, b, by ring, by omega⟩
    | exact ⟨a, -c, d, b, by ring, by omega⟩
    | exact ⟨a, -c, -d, b, by ring, by omega⟩
    | exact ⟨b, c, d, a, by ring, by omega⟩
    | exact ⟨b, c, -d, a, by ring, by omega⟩
    | exact ⟨b, -c, d, a, by ring, by omega⟩
    | exact ⟨b, -c, -d, a, by ring, by omega⟩

/-- Every sum of four integer squares is $x^2+2y^2+3z^2+6t^2$ (Dickson). -/
private theorem rep1236_aux (n : ℕ) (h : ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) :
    Rep4 1 2 3 6 n := by
  obtain ⟨a, b, c, d, h⟩ := h
  obtain ⟨a', b', c', d', h1, h2⟩ := pick_triple a b c d
  exact rep1236_core a' b' c' d' n (by rw [h1]; exact h) h2


/-- **Liouville's form $x^2 + 2y^2 + 3z^2 + 6t^2$ is universal** (,
), from Lagrange's four-squares theorem (module docstring). -/
@[kb "dickson1923" "[unverified locator]"]
theorem universal_1236 : Universal4 1 2 3 6 := by
  intro n
  exact rep1236_aux n (by
    obtain ⟨a, b, c, d, h⟩ := Grosswald.lagrange_four_squares n
    exact ⟨a, b, c, d, by exact_mod_cast h⟩)

/-- **From four squares to $x^2 + 2y^2 + 3z^2 + 6t^2$**: if $n$ is a sum of four integer
squares then $n = x^2 + 2y^2 + 3z^2 + 6t^2$ for some integers $x, y, z, t$. -/
@[kb "dickson1923" "[unverified locator]"]
theorem rep_1236_of_four_squares (n : ℕ) (h : ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) :
    Rep4 1 2 3 6 n := by
  exact rep1236_aux n h

/-- Doubling all variables: $\mathrm{Rep4}(m) \Rightarrow \mathrm{Rep4}(4m)$. -/
private theorem rep4_four {a b c d m : ℕ} (h : Rep4 a b c d m) : Rep4 a b c d (4 * m) := by
  obtain ⟨x, y, z, t, h⟩ := h
  exact ⟨2 * x, 2 * y, 2 * z, 2 * t, by push_cast; linarith⟩

/-- Universality follows from representing every $n$ with $4 \nmid n$ (descent $n = 4m$). -/
private theorem univ_of_nonmult4 (a b c d : ℕ) (h : ∀ n, n % 4 ≠ 0 → Rep4 a b c d n) :
    Universal4 a b c d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n % 4 = 0
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact ⟨0, 0, 0, 0, by simp⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
        exact rep4_four (ih m (by omega))
    · exact h n h4

/-- If $4 \nmid m$ and $m \not\equiv 7 \pmod 8$ then $m \ne 4^\lambda(8\mu+7)$. -/
private theorem nexc8 (m : ℕ) (h4 : m % 4 ≠ 0) (h8 : m % 8 ≠ 7) : ¬ IsExc 4 8 7 m := by
  rintro ⟨l, k, h⟩
  cases l with
  | zero => simp at h; omega
  | succ l =>
    obtain ⟨q, hq⟩ : ∃ q, m = 4 * q := ⟨4 ^ l * (8 * k + 7), by rw [h]; ring⟩
    omega

/-- If $4 \nmid m$ and $m \not\equiv 14 \pmod{16}$ then $m \ne 4^\lambda(16\mu+14)$. -/
private theorem nexc16 (m : ℕ) (h4 : m % 4 ≠ 0) (h8 : m % 16 ≠ 14) : ¬ IsExc 4 16 14 m := by
  rintro ⟨l, k, h⟩
  cases l with
  | zero => simp at h; omega
  | succ l =>
    obtain ⟨q, hq⟩ : ∃ q, m = 4 * q := ⟨4 ^ l * (16 * k + 14), by rw [h]; ring⟩
    omega

/-- Adding $e t^2$ in slot 1 to a ternary representation of $n - et^2$. -/
private theorem drop1 (a b c e n t : ℕ) (h : e * t ^ 2 ≤ n) (hr : Rep3 a b c (n - e * t ^ 2)) :
    Rep4 e a b c n := by
  obtain ⟨x, y, z, hxyz⟩ := hr
  have hc : ((n - e * t ^ 2 : ℕ) : ℤ) = n - e * t ^ 2 := by rw [Nat.cast_sub h]; push_cast; ring
  rw [hc] at hxyz
  exact ⟨t, x, y, z, by linarith⟩

/-- Adding $e t^2$ in slot 2 to a ternary representation of $n - et^2$. -/
private theorem drop2 (a b c e n t : ℕ) (h : e * t ^ 2 ≤ n) (hr : Rep3 a b c (n - e * t ^ 2)) :
    Rep4 a e b c n := by
  obtain ⟨x, y, z, hxyz⟩ := hr
  have hc : ((n - e * t ^ 2 : ℕ) : ℤ) = n - e * t ^ 2 := by rw [Nat.cast_sub h]; push_cast; ring
  rw [hc] at hxyz
  exact ⟨x, t, y, z, by linarith⟩

/-- Adding $e t^2$ in slot 3 to a ternary representation of $n - et^2$. -/
private theorem drop3 (a b c e n t : ℕ) (h : e * t ^ 2 ≤ n) (hr : Rep3 a b c (n - e * t ^ 2)) :
    Rep4 a b e c n := by
  obtain ⟨x, y, z, hxyz⟩ := hr
  have hc : ((n - e * t ^ 2 : ℕ) : ℤ) = n - e * t ^ 2 := by rw [Nat.cast_sub h]; push_cast; ring
  rw [hc] at hxyz
  exact ⟨x, y, t, z, by linarith⟩

/-- Adding $e t^2$ in slot 4 to a ternary representation of $n - et^2$. -/
private theorem drop4 (a b c e n t : ℕ) (h : e * t ^ 2 ≤ n) (hr : Rep3 a b c (n - e * t ^ 2)) :
    Rep4 a b c e n := by
  obtain ⟨x, y, z, hxyz⟩ := hr
  have hc : ((n - e * t ^ 2 : ℕ) : ℤ) = n - e * t ^ 2 := by rw [Nat.cast_sub h]; push_cast; ring
  rw [hc] at hxyz
  exact ⟨x, y, z, t, by linarith⟩


/-- For $4 \nmid n$ some $t \le 1$ makes $n - 1t^2 \ge 0$ non-exceptional (mod 8). -/
private theorem arith8_1_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 1 * t ^ 2 ≤ n ∧ (n - 1 * t ^ 2) % 4 ≠ 0 ∧ (n - 1 * t ^ 2) % 8 ≠ 7 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (1 ≤ n ∧ (n - 1) % 4 ≠ 0 ∧ (n - 1) % 8 ≠ 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 1t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_1_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 1 * t ^ 2 ≤ n ∧ (n - 1 * t ^ 2) % 4 ≠ 0 ∧ (n - 1 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (1 ≤ n ∧ (n - 1) % 4 ≠ 0 ∧ (n - 1) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 3t^2 \ge 0$ non-exceptional (mod 8), except $n \in \{7\}$. -/
private theorem arith8_3_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    (∃ t : ℕ, 3 * t ^ 2 ≤ n ∧ (n - 3 * t ^ 2) % 4 ≠ 0 ∧ (n - 3 * t ^ 2) % 8 ≠ 7) ∨ (n = 7) := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (3 ≤ n ∧ (n - 3) % 4 ≠ 0 ∧ (n - 3) % 8 ≠ 7) ∨ (12 ≤ n ∧ (n - 12) % 4 ≠ 0 ∧ (n - 12) % 8 ≠ 7) ∨ (n = 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · left; refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · right; exact h

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 4t^2 \ge 0$ non-exceptional (mod 8). -/
private theorem arith8_4_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 4 * t ^ 2 ≤ n ∧ (n - 4 * t ^ 2) % 4 ≠ 0 ∧ (n - 4 * t ^ 2) % 8 ≠ 7 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (4 ≤ n ∧ (n - 4) % 4 ≠ 0 ∧ (n - 4) % 8 ≠ 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 5t^2 \ge 0$ non-exceptional (mod 8). -/
private theorem arith8_5_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 5 * t ^ 2 ≤ n ∧ (n - 5 * t ^ 2) % 4 ≠ 0 ∧ (n - 5 * t ^ 2) % 8 ≠ 7 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (5 ≤ n ∧ (n - 5) % 4 ≠ 0 ∧ (n - 5) % 8 ≠ 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 6t^2 \ge 0$ non-exceptional (mod 8). -/
private theorem arith8_6_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 6 * t ^ 2 ≤ n ∧ (n - 6 * t ^ 2) % 4 ≠ 0 ∧ (n - 6 * t ^ 2) % 8 ≠ 7 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (6 ≤ n ∧ (n - 6) % 4 ≠ 0 ∧ (n - 6) % 8 ≠ 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 7t^2 \ge 0$ non-exceptional (mod 8), except $n \in \{7, 15, 23\}$. -/
private theorem arith8_7_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    (∃ t : ℕ, 7 * t ^ 2 ≤ n ∧ (n - 7 * t ^ 2) % 4 ≠ 0 ∧ (n - 7 * t ^ 2) % 8 ≠ 7) ∨ (n = 7 ∨ n = 15 ∨ n = 23) := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (7 ≤ n ∧ (n - 7) % 4 ≠ 0 ∧ (n - 7) % 8 ≠ 7) ∨ (28 ≤ n ∧ (n - 28) % 4 ≠ 0 ∧ (n - 28) % 8 ≠ 7) ∨ (n = 7 ∨ n = 15 ∨ n = 23) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · left; refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · right; exact h

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 3t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_3_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 3 * t ^ 2 ≤ n ∧ (n - 3 * t ^ 2) % 4 ≠ 0 ∧ (n - 3 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (3 ≤ n ∧ (n - 3) % 4 ≠ 0 ∧ (n - 3) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 5t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_5_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 5 * t ^ 2 ≤ n ∧ (n - 5 * t ^ 2) % 4 ≠ 0 ∧ (n - 5 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (5 ≤ n ∧ (n - 5) % 4 ≠ 0 ∧ (n - 5) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 6t^2 \ge 0$ non-exceptional (mod 16), except $n \in \{14\}$. -/
private theorem arith16_6_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    (∃ t : ℕ, 6 * t ^ 2 ≤ n ∧ (n - 6 * t ^ 2) % 4 ≠ 0 ∧ (n - 6 * t ^ 2) % 16 ≠ 14) ∨ (n = 14) := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (6 ≤ n ∧ (n - 6) % 4 ≠ 0 ∧ (n - 6) % 16 ≠ 14) ∨ (24 ≤ n ∧ (n - 24) % 4 ≠ 0 ∧ (n - 24) % 16 ≠ 14) ∨ (n = 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · left; refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · right; exact h

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 7t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_7_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 7 * t ^ 2 ≤ n ∧ (n - 7 * t ^ 2) % 4 ≠ 0 ∧ (n - 7 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (7 ≤ n ∧ (n - 7) % 4 ≠ 0 ∧ (n - 7) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 8t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_8_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 8 * t ^ 2 ≤ n ∧ (n - 8 * t ^ 2) % 4 ≠ 0 ∧ (n - 8 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (8 ≤ n ∧ (n - 8) % 4 ≠ 0 ∧ (n - 8) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 9t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_9_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 9 * t ^ 2 ≤ n ∧ (n - 9 * t ^ 2) % 4 ≠ 0 ∧ (n - 9 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (9 ≤ n ∧ (n - 9) % 4 ≠ 0 ∧ (n - 9) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 10t^2 \ge 0$ non-exceptional (mod 16), except $n \in \{14, 30\}$. -/
private theorem arith16_10_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    (∃ t : ℕ, 10 * t ^ 2 ≤ n ∧ (n - 10 * t ^ 2) % 4 ≠ 0 ∧ (n - 10 * t ^ 2) % 16 ≠ 14) ∨ (n = 14 ∨ n = 30) := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (10 ≤ n ∧ (n - 10) % 4 ≠ 0 ∧ (n - 10) % 16 ≠ 14) ∨ (40 ≤ n ∧ (n - 40) % 4 ≠ 0 ∧ (n - 40) % 16 ≠ 14) ∨ (n = 14 ∨ n = 30) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · left; refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · right; exact h

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 11t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_11_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 11 * t ^ 2 ≤ n ∧ (n - 11 * t ^ 2) % 4 ≠ 0 ∧ (n - 11 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (11 ≤ n ∧ (n - 11) % 4 ≠ 0 ∧ (n - 11) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 12t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_12_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 12 * t ^ 2 ≤ n ∧ (n - 12 * t ^ 2) % 4 ≠ 0 ∧ (n - 12 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (12 ≤ n ∧ (n - 12) % 4 ≠ 0 ∧ (n - 12) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 13t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_13_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 13 * t ^ 2 ≤ n ∧ (n - 13 * t ^ 2) % 4 ≠ 0 ∧ (n - 13 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (13 ≤ n ∧ (n - 13) % 4 ≠ 0 ∧ (n - 13) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 14t^2 \ge 0$ non-exceptional (mod 16), except $n \in \{14, 30, 46\}$. -/
private theorem arith16_14_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    (∃ t : ℕ, 14 * t ^ 2 ≤ n ∧ (n - 14 * t ^ 2) % 4 ≠ 0 ∧ (n - 14 * t ^ 2) % 16 ≠ 14) ∨ (n = 14 ∨ n = 30 ∨ n = 46) := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (14 ≤ n ∧ (n - 14) % 4 ≠ 0 ∧ (n - 14) % 16 ≠ 14) ∨ (56 ≤ n ∧ (n - 56) % 4 ≠ 0 ∧ (n - 56) % 16 ≠ 14) ∨ (n = 14 ∨ n = 30 ∨ n = 46) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · left; refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · left; refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · right; exact h

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 2t^2 \ge 0$ non-exceptional (mod 8). -/
private theorem arith8_2_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 2 * t ^ 2 ≤ n ∧ (n - 2 * t ^ 2) % 4 ≠ 0 ∧ (n - 2 * t ^ 2) % 8 ≠ 7 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 8 ≠ 7) ∨ (2 ≤ n ∧ (n - 2) % 4 ≠ 0 ∧ (n - 2) % 8 ≠ 7) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 2$ makes $n - 2t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_2_2 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 2 * t ^ 2 ≤ n ∧ (n - 2 * t ^ 2) % 4 ≠ 0 ∧ (n - 2 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (2 ≤ n ∧ (n - 2) % 4 ≠ 0 ∧ (n - 2) % 16 ≠ 14) ∨ (8 ≤ n ∧ (n - 8) % 4 ≠ 0 ∧ (n - 8) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨2, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- For $4 \nmid n$ some $t \le 1$ makes $n - 4t^2 \ge 0$ non-exceptional (mod 16). -/
private theorem arith16_4_1 (n : ℕ) (hn : n % 4 ≠ 0) :
    ∃ t : ℕ, 4 * t ^ 2 ≤ n ∧ (n - 4 * t ^ 2) % 4 ≠ 0 ∧ (n - 4 * t ^ 2) % 16 ≠ 14 := by
  have h : (0 ≤ n ∧ (n - 0) % 4 ≠ 0 ∧ (n - 0) % 16 ≠ 14) ∨ (4 ≤ n ∧ (n - 4) % 4 ≠ 0 ∧ (n - 4) % 16 ≠ 14) := by omega
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> norm_num <;> omega
  · refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num <;> omega

/-- The form $(1,1,1,1)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_1 : Universal4 1 1 1 1 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_1_1 n hn
    exact drop1 1 1 1 1 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,1,1,2)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_1_2 : Universal4 1 1 1 2 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_1_1 n hn
    exact drop1 1 1 2 1 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,1,3)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_3 : Universal4 1 1 1 3 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith8_3_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 1 1 3 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3))
    · rcases h with rfl
      · exact ⟨0, 0, 2, 1, by norm_num⟩)

/-- The form $(1,1,1,4)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_4 : Universal4 1 1 1 4 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_4_1 n hn
    exact drop4 1 1 1 4 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,1,1,5)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_5 : Universal4 1 1 1 5 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_5_1 n hn
    exact drop4 1 1 1 5 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,1,1,6)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_6 : Universal4 1 1 1 6 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_6_1 n hn
    exact drop4 1 1 1 6 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,1,1,7)$ represents every natural number (ternary sub-form $(1,1,1)$). -/
private theorem u_1_1_1_7 : Universal4 1 1 1 7 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith8_7_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 1 1 7 n t h1 ((ternary_111 _).2 (nexc8 _ h2 h3))
    · rcases h with rfl | rfl | rfl
      · exact ⟨0, 0, 0, 1, by norm_num⟩
      · exact ⟨0, 2, 2, 1, by norm_num⟩
      · exact ⟨0, 0, 4, 1, by norm_num⟩)

/-- The form $(1,1,2,2)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_1_2_2 : Universal4 1 1 2 2 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_1_1 n hn
    exact drop1 1 2 2 1 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,1,2,3)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_3 : Universal4 1 1 2 3 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_3_1 n hn
    exact drop4 1 1 2 3 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,4)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_1_2_4 : Universal4 1 1 2 4 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_1_1 n hn
    exact drop1 1 2 4 1 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,5)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_5 : Universal4 1 1 2 5 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_5_1 n hn
    exact drop4 1 1 2 5 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,6)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_6 : Universal4 1 1 2 6 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_6_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 1 2 6 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl
      · exact ⟨0, 0, 2, 1, by norm_num⟩)

/-- The form $(1,1,2,7)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_7 : Universal4 1 1 2 7 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_7_1 n hn
    exact drop4 1 1 2 7 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,8)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_8 : Universal4 1 1 2 8 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_8_1 n hn
    exact drop4 1 1 2 8 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,9)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_9 : Universal4 1 1 2 9 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_9_1 n hn
    exact drop4 1 1 2 9 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,10)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_10 : Universal4 1 1 2 10 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_10_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 1 2 10 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl | rfl
      · exact ⟨0, 2, 0, 1, by norm_num⟩
      · exact ⟨1, 1, 3, 1, by norm_num⟩)

/-- The form $(1,1,2,11)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_11 : Universal4 1 1 2 11 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_11_1 n hn
    exact drop4 1 1 2 11 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,12)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_12 : Universal4 1 1 2 12 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_12_1 n hn
    exact drop4 1 1 2 12 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,13)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_13 : Universal4 1 1 2 13 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_13_1 n hn
    exact drop4 1 1 2 13 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,1,2,14)$ represents every natural number (ternary sub-form $(1,1,2)$). -/
private theorem u_1_1_2_14 : Universal4 1 1 2 14 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_14_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 1 2 14 n t h1 ((ternary_112 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl | rfl | rfl
      · exact ⟨0, 0, 0, 1, by norm_num⟩
      · exact ⟨0, 4, 0, 1, by norm_num⟩
      · exact ⟨0, 0, 4, 1, by norm_num⟩)

/-- The form $(1,2,2,2)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_2_2_2 : Universal4 1 2 2 2 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_2_1 n hn
    exact drop2 1 2 2 2 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,2,2,3)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_2_2_3 : Universal4 1 2 2 3 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith8_3_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 2 2 3 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3))
    · rcases h with rfl
      · exact ⟨0, 1, 1, 1, by norm_num⟩)

/-- The form $(1,2,2,4)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_2_4 : Universal4 1 2 2 4 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_2_2 n hn
    exact drop2 1 2 4 2 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,2,5)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_2_2_5 : Universal4 1 2 2 5 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_5_1 n hn
    exact drop4 1 2 2 5 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,2,2,6)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_2_2_6 : Universal4 1 2 2 6 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith8_6_1 n hn
    exact drop4 1 2 2 6 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3)))

/-- The form $(1,2,2,7)$ represents every natural number (ternary sub-form $(1,2,2)$). -/
private theorem u_1_2_2_7 : Universal4 1 2 2 7 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith8_7_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 2 2 7 n t h1 ((ternary_122 _).2 (nexc8 _ h2 h3))
    · rcases h with rfl | rfl | rfl
      · exact ⟨0, 0, 0, 1, by norm_num⟩
      · exact ⟨0, 0, 2, 1, by norm_num⟩
      · exact ⟨0, 2, 2, 1, by norm_num⟩)

/-- The form $(1,2,3,4)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_3_4 : Universal4 1 2 3 4 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_3_1 n hn
    exact drop3 1 2 4 3 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,4)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_4 : Universal4 1 2 4 4 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_4_1 n hn
    exact drop3 1 2 4 4 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,5)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_5 : Universal4 1 2 4 5 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_5_1 n hn
    exact drop4 1 2 4 5 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,6)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_6 : Universal4 1 2 4 6 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_6_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 2 4 6 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl
      · exact ⟨0, 2, 0, 1, by norm_num⟩)

/-- The form $(1,2,4,7)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_7 : Universal4 1 2 4 7 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_7_1 n hn
    exact drop4 1 2 4 7 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,8)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_8 : Universal4 1 2 4 8 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_8_1 n hn
    exact drop4 1 2 4 8 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,9)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_9 : Universal4 1 2 4 9 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_9_1 n hn
    exact drop4 1 2 4 9 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,10)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_10 : Universal4 1 2 4 10 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_10_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 2 4 10 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl | rfl
      · exact ⟨0, 0, 1, 1, by norm_num⟩
      · exact ⟨2, 0, 2, 1, by norm_num⟩)

/-- The form $(1,2,4,11)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_11 : Universal4 1 2 4 11 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_11_1 n hn
    exact drop4 1 2 4 11 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,12)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_12 : Universal4 1 2 4 12 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_12_1 n hn
    exact drop4 1 2 4 12 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,13)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_13 : Universal4 1 2 4 13 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    obtain ⟨t, h1, h2, h3⟩ := arith16_13_1 n hn
    exact drop4 1 2 4 13 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3)))

/-- The form $(1,2,4,14)$ represents every natural number (ternary sub-form $(1,2,4)$). -/
private theorem u_1_2_4_14 : Universal4 1 2 4 14 :=
  univ_of_nonmult4 _ _ _ _ (fun n hn => by
    rcases arith16_14_2 n hn with ⟨t, h1, h2, h3⟩ | h
    · exact drop4 1 2 4 14 n t h1 ((ternary_124 _).2 (nexc16 _ h2 h3))
    · rcases h with rfl | rfl | rfl
      · exact ⟨0, 0, 0, 1, by norm_num⟩
      · exact ⟨0, 0, 2, 1, by norm_num⟩
      · exact ⟨0, 4, 0, 1, by norm_num⟩)

/-- **Ramanujan's classification, sufficiency for 39 of the 54 forms**: every form of
`RamanujanList` other than the 15 `RemainingForm`s is universal. -/
@[kb "ramanujan1917" "§ 2, table, Collected Papers p. 170"]
theorem universal_of_ramanujanList {a b c d : ℕ} (h : RamanujanList a b c d) (hr : ¬ RemainingForm a b c d) :
    Universal4 a b c d := by
  obtain ⟨rfl, hl⟩ := h
  rcases hl with ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ |
    ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ <;> interval_cases d <;>
    first | exact universal_1236 | with_reducible exact u_1_1_1_1 | with_reducible exact u_1_1_1_2 | with_reducible exact u_1_1_1_3 | with_reducible exact u_1_1_1_4 | with_reducible exact u_1_1_1_5 | with_reducible exact u_1_1_1_6 | with_reducible exact u_1_1_1_7 | with_reducible exact u_1_1_2_2 | with_reducible exact u_1_1_2_3 | with_reducible exact u_1_1_2_4 | with_reducible exact u_1_1_2_5 | with_reducible exact u_1_1_2_6 | with_reducible exact u_1_1_2_7 | with_reducible exact u_1_1_2_8 | with_reducible exact u_1_1_2_9 | with_reducible exact u_1_1_2_10 | with_reducible exact u_1_1_2_11 | with_reducible exact u_1_1_2_12 | with_reducible exact u_1_1_2_13 | with_reducible exact u_1_1_2_14 | with_reducible exact u_1_2_2_2 | with_reducible exact u_1_2_2_3 | with_reducible exact u_1_2_2_4 | with_reducible exact u_1_2_2_5 | with_reducible exact u_1_2_2_6 | with_reducible exact u_1_2_2_7 | with_reducible exact u_1_2_3_4 | with_reducible exact u_1_2_4_4 | with_reducible exact u_1_2_4_5 | with_reducible exact u_1_2_4_6 | with_reducible exact u_1_2_4_7 | with_reducible exact u_1_2_4_8 | with_reducible exact u_1_2_4_9 | with_reducible exact u_1_2_4_10 | with_reducible exact u_1_2_4_11 | with_reducible exact u_1_2_4_12 | with_reducible exact u_1_2_4_13 | with_reducible exact u_1_2_4_14 |
      (exfalso; exact hr (by unfold RemainingForm; omega))

/-- **The 15 remaining forms are universal** (the part not proved here). **Stated.**
*Why out of reach here:* each of them contains no ternary sub-form whose exceptions follow from the three-squares
theorem; the classical proofs use the ternary laws `Ternary113`, `Ternary123`, `Ternary125` (Dickson, *Studies* (1930);
Bhargava–Hanke's 15 theorem would also give them, and is itself only stated in this library). Checked numerically for
every $n \le 10000$ (the historical sources). -/
@[kb "ramanujan1917" "§ 2, table, Collected Papers p. 170"]
def RamanujanRemaining : Prop := ∀ a b c d : ℕ, RemainingForm a b c d → Universal4 a b c d

/-- **Ramanujan's classification** (corrected count 54): for $1 \le a \le b \le c \le d$,
$ax^2 + by^2 + cz^2 + dt^2$ represents every natural number iff $(a, b, c, d)$ is in `RamanujanList`. -/
@[kb "ramanujan1917" "§ 2, Collected Papers pp. 169–170"]
def RamanujanClassification : Prop :=
  ∀ a b c d : ℕ, 1 ≤ a → a ≤ b → b ≤ c → c ≤ d → (Universal4 a b c d ↔ RamanujanList a b c d)

/-- **The classification is reduced to the 15 remaining forms:** `RamanujanClassification ↔ RamanujanRemaining`. -/
theorem ramanujanClassification_iff : RamanujanClassification ↔ RamanujanRemaining := by
  constructor
  · intro h a b c d hr
    rcases hr with ⟨ha, ⟨hb, hc, h1, h2⟩ | ⟨hb, hc, hd⟩ | ⟨hb, hc, h1, h2⟩⟩
    · exact (h a b c d (by omega) (by omega) (by omega) (by omega)).2
        ⟨ha, Or.inr (Or.inr (Or.inl ⟨hb, hc, h1, h2⟩))⟩
    · exact (h a b c d (by omega) (by omega) (by omega) (by omega)).2
        ⟨ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hc, by omega, by omega⟩))))⟩
    · exact (h a b c d (by omega) (by omega) (by omega) (by omega)).2
        ⟨ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, hc, h1, h2⟩)))))⟩
  · intro hR a b c d h1 h2 h3 h4
    constructor
    · exact fun hU => ramanujan_necessary h1 h2 h3 h4 hU
    · intro hl
      by_cases hr : RemainingForm a b c d
      · exact hR a b c d hr
      · exact universal_of_ramanujanList hl hr

/-- **$x^2 + y^2 + 3z^2 + 3t^2$ is universal** (first form). **Stated**
(one of the 15 `RemainingForm`s; the classical proof goes through Dirichlet's law `Ternary113`). -/
@[kb "smith1894b" "[unverified locator]"]
def Universal1133 : Prop := Universal4 1 1 3 3

end QuadFormsKB.Historical.Ramanujan
