/-
# Conway–Sloane, Ch. 15, §3.3: Table 15.2, cycles of reduced indefinite binary forms

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.3,
Table 15.2 (pp. 362–363) (`conwaysloane1999`); the notation is explained on pp. 359–361.

**The printed notation (pp. 359–361).** An entry $a^{b}c^{d}e\ldots$ stands for the digits $a_0, b_0, a_1, b_1, \ldots$ of
the cycle of Theorem 1 (rules (5)–(7), `stepPair`): $a_i$ are the (absolute values of the) entries $a$ and $b_i$ the entries
$b$ of the forms $a_i^{b_i}a_{i+1}$; the signs of the $a_i$ alternate; one entry stands for up to four cycles
(the signs of the $a_i$ changed, and the cycle read backwards); a curly bracket $\{\ \}$ indicates reflection about the
outermost digits; an ordinary bracket $(\ )$ bounds a whole (or half) period.

**Formalization.** `decodeDigits` turns the printed digits into the periodic digit string
($d_0 \ldots d_m d_{m-1} \ldots d_1$ for a reflected entry, the digits themselves for a parenthesized one);
`cycleOfPairs` into the forms with alternating signs (a full cycle has twice as many forms as the digit period when
that period has an odd number of forms); `variants` into the four related cycles. `TableOK d entries` says that every
such cycle is a cycle of Theorem 1's sequence (consecutive forms are related by `stepPair`, all have determinant $d$)
and that the forms of all these cycles are *exactly* the forms satisfying the reduction condition (12) (`IsReducedIndef`)
of determinant $d$. `table152_correct` checks `TableOK` for the entries transcribed below by `decide +kernel`.

**Covered determinants:** every nonsquare $-99 \le d \le -2$ (`table152_correct` for Table 15.2a, `table152b_correct`
for Table 15.2b). The square determinants ($d = -1, -4, -9, \ldots, -100$), whose cycles are the finite chains
$0^b\ldots$ of §3.3, are not covered.

**Transcription.** The entries were read from a low-resolution scan. In Table 15.2b six entries were not legible
with certainty and were read as the only reading consistent with the visible digits that `TableOK` accepts:
$d = -52$: $\{1^7 3^5 9^4 4\}$; $d = -65$: $(4^5 10^5 4^7)$ (read at first as two entries $\{4^5 10\}, \{4^7\}$);
$d = -84$: $\{2^8 10^2 8^6 6\}$ and $\{4^8 5^7 7\}$; $d = -85$: $(6^5 10^5 6^7)$; $d = -90$: $\{6^6 9^3\}$. For $d = -88$ the scan seems to show a
fourth entry $\{4^8 6\}$, which is not a cycle (the forms $4^8 6$ and $6^8 4$ lie on the cycle $\{2^8 12^4 6^8 4\}$);
it is omitted here and should be checked against a clean copy before it is recorded as an erratum. These readings are
therefore confirmed by the computation, not independently transcribed.
-/
import QuadFormsKB.Literature.ConwaySloane.Binary

namespace QuadFormsKB
namespace ConwaySloane
namespace Binary

/-- The digits of an entry as a periodic digit string: reflected about the outermost digits (curly brackets) or taken
as printed (ordinary brackets). An entry whose printed first digit is a *superscript* $b_i$ (the centre of the reflection
is then a $b$-digit; e.g. $\{5^3 4^6 2^5 3\}$ for $d = -34$) is transcribed with a leading `0`, which rotates the digit
string so that it starts at the preceding $a$-digit. -/
def decodeDigits (refl : Bool) (D : List ℤ) : List ℤ :=
  let reflect : List ℤ → List ℤ := fun E => if refl then E ++ (E.dropLast.reverse.dropLast) else E
  match D with
  | 0 :: E => let C := reflect E; C.getLastD 0 :: C.dropLast
  | _ => reflect D

/-- Consecutive digits as pairs $(a_i, b_i)$. -/
def pairsOf : List ℤ → List (ℤ × ℤ)
  | a :: b :: rest => (a, b) :: pairsOf rest
  | _ => []

/-- The forms of the cycle with the signs of the $a_i$ alternating, starting with $+$: $\langle (-1)^i a_i, b_i,
(-1)^{i+1} a_{i+1}\rangle$, over a full period (twice the digit period if it has an odd number of pairs). -/
def cycleOfPairs (P : List (ℤ × ℤ)) : List BinForm :=
  let P2 := if P.length % 2 = 0 then P else P ++ P
  (List.range P2.length).map fun i =>
    ⟨(-1) ^ i * (P2.getD i (0, 0)).1, (P2.getD i (0, 0)).2,
      (-1) ^ (i + 1) * (P2.getD ((i + 1) % P2.length) (0, 0)).1⟩

/-- Change the signs of the $a_i$. -/
def negForm (f : BinForm) : BinForm := ⟨-f.a, f.b, -f.c⟩
/-- Read the form backwards. -/
def flipForm (f : BinForm) : BinForm := ⟨f.c, f.b, f.a⟩

/-- The four related cycles represented by one printed entry. -/
def variants (L : List BinForm) : List (List BinForm) :=
  [L, L.map negForm, (L.map flipForm).reverse, ((L.map negForm).map flipForm).reverse]

/-- `L` is a cycle of Theorem 1's sequence for determinant $d$: nonempty, every form has determinant $d$, and
consecutive forms (cyclically) are related by the step of rules (5)–(7). -/
def CycOK (d : ℤ) (L : List BinForm) : Prop :=
  L ≠ [] ∧ ∀ i ∈ List.range L.length,
    (L.getD i ⟨0, 0, 0⟩).det = d ∧ (L.getD i ⟨0, 0, 0⟩).c = (L.getD ((i + 1) % L.length) ⟨0, 0, 0⟩).a ∧
      stepPair d ((L.getD i ⟨0, 0, 0⟩).a, (L.getD i ⟨0, 0, 0⟩).b) =
        ((L.getD ((i + 1) % L.length) ⟨0, 0, 0⟩).a, (L.getD ((i + 1) % L.length) ⟨0, 0, 0⟩).b)

instance (d : ℤ) (L : List BinForm) : Decidable (CycOK d L) := by unfold CycOK; infer_instance

/-- All forms represented by the entries. -/
def entryCycles (entries : List (Bool × List ℤ)) : List (List BinForm) :=
  entries.flatMap fun e => variants (cycleOfPairs (pairsOf (decodeDigits e.1 e.2)))

/-- **The table entries for $d$ are correct:** every represented cycle is a cycle of the sequence (5), and the forms of all
of them are exactly the forms satisfying (12) with determinant $d$. -/
def TableOK (d : ℤ) (entries : List (Bool × List ℤ)) : Prop :=
  (∀ L ∈ entryCycles entries, CycOK d L) ∧
  (∀ y ∈ (entryCycles entries).flatten, IsReducedIndef y.a y.b y.c ∧ y.det = d) ∧
  (∀ a ∈ Finset.Icc d (-d), ∀ b ∈ Finset.Icc 1 (-d), a ∣ d + b ^ 2 →
      IsReducedIndef a b ((d + b ^ 2) / a) → (⟨a, b, (d + b ^ 2) / a⟩ : BinForm) ∈ (entryCycles entries).flatten)

instance (d : ℤ) (entries : List (Bool × List ℤ)) : Decidable (TableOK d entries) := by
  unfold TableOK; infer_instance

/-- If `TableOK`, then the printed entries represent exactly the reduced indefinite forms of determinant $d$. -/
theorem TableOK.iff {d : ℤ} {entries : List (Bool × List ℤ)} (h : TableOK d entries) (hd : d < 0) (x : BinForm) :
    (IsReducedIndef x.a x.b x.c ∧ x.det = d) ↔ x ∈ (entryCycles entries).flatten := by
  obtain ⟨-, hs, hc⟩ := h
  constructor
  · rintro ⟨hx, hdx⟩
    exact reducedIndef_complete (d := d) (B := -d) (by omega) (by nlinarith) hc x hx hdx
  · intro hx
    exact hs x hx

/-- Printed entries of Table 15.2: for each determinant a list of entries (curly bracket = `true`). -/
def t152 : List (ℤ × List (Bool × List ℤ)) := [
  (-2, [(true, [1, 1])]),
  (-3, [(true, [1, 1, 2])]),
  (-5, [(true, [1, 2]), (true, [2, 1])]),
  (-6, [(true, [1, 2, 2])]),
  (-7, [(true, [1, 2, 3, 1, 2])]),
  (-8, [(true, [1, 2, 4]), (true, [2, 2])]),
  (-10, [(true, [1, 3]), (true, [2, 2, 3, 1])]),
  (-11, [(true, [1, 3, 2])]),
  (-12, [(true, [1, 3, 3]), (true, [2, 2, 4])]),
  (-13, [(true, [1, 3, 4, 1, 3, 2]), (true, [2, 3])]),
  (-14, [(true, [1, 3, 5, 2, 2])]),
  (-15, [(true, [1, 3, 6]), (true, [2, 3, 3])]),
  (-17, [(true, [1, 4]), (true, [2, 3, 4, 1])]),
  (-18, [(true, [1, 4, 2]), (true, [3, 3])]),
  (-19, [(true, [1, 4, 3, 2, 5, 3, 2])]),
  (-20, [(true, [1, 4, 4]), (true, [2, 4]), (true, [4, 2])]),
  (-21, [(true, [1, 4, 5, 1, 4, 3, 3]), (true, [2, 3, 6])]),
  (-22, [(true, [1, 4, 6, 2, 3, 4, 2])]),
  (-23, [(true, [1, 4, 7, 3, 2])]),
  (-24, [(true, [1, 4, 8]), (true, [2, 4, 4]), (true, [3, 3, 5, 2, 4])]),
  (-26, [(true, [1, 5]), (true, [2, 4, 5, 1])]),
  (-27, [(true, [1, 5, 2]), (true, [3, 3, 6])]),
  (-28, [(true, [1, 5, 3, 4, 4]), (true, [2, 4, 6, 2, 4])]),
  (-29, [(true, [1, 5, 4, 3, 5, 2]), (true, [2, 5])]),
  (-30, [(true, [1, 5, 5]), (true, [2, 4, 7, 3, 3])]),
  (-31, [(true, [1, 5, 6, 1, 5, 4, 3, 5, 2])]),
  (-32, [(true, [1, 5, 7, 2, 4]), (true, [2, 4, 8]), (true, [4, 4])]),
  (-33, [(true, [1, 5, 8, 3, 3]), (true, [2, 5, 4, 3, 6])]),
  (-34, [(true, [1, 5, 9, 4, 2]), (true, [0, 5, 3, 4, 6, 2, 5, 3])]),
  (-35, [(true, [1, 5, 10]), (true, [2, 5, 5])]),
  (-37, [(true, [1, 6, 1]), (true, [2, 5, 6, 1]), (false, [3, 5, 4, 3, 7, 4])]),
  (-38, [(true, [1, 6, 2])]),
  (-39, [(true, [1, 6, 3]), (true, [2, 5, 7, 2, 5, 3, 6])]),
  (-40, [(true, [1, 6, 4]), (true, [2, 6]), (true, [5, 5, 3, 4, 8]), (true, [4, 4, 6, 2])]),
  (-41, [(true, [1, 6, 5, 4]), (true, [2, 5, 8, 3, 4, 5])]),
  (-42, [(true, [1, 6, 6]), (true, [2, 6, 3])]),
  (-43, [(true, [1, 6, 7, 1, 6, 5, 3, 4, 9, 5, 2])]),
  (-44, [(true, [1, 6, 8, 2, 5, 3, 7, 4, 4]), (true, [2, 6, 4])]),
  (-45, [(true, [1, 6, 9, 3, 4, 5, 5]), (true, [2, 5, 10]), (true, [3, 6]), (true, [6, 3])]),
  (-46, [(true, [1, 6, 10, 4, 3, 5, 7, 2, 6, 4, 5, 6, 2])]),
  (-47, [(true, [1, 6, 11, 5, 2])]),
  (-48, [(true, [1, 6, 12]), (true, [2, 6, 6]), (true, [3, 6, 4]), (true, [4, 4, 8])]),
  (-50, [(true, [1, 7]), (true, [2, 6, 7, 1]), (true, [5, 5])])]

/-- Printed entries of Table 15.2b, $-99 \le d \le -51$ (square $d$ omitted), transcribed as for `t152`. -/
def t152b : List (ℤ × List (Bool × List ℤ)) := [
  (-51, [(true, [1, 7, 2]), (true, [3, 6, 5, 4, 7, 3, 6])]),
  (-52, [(true, [1, 7, 3, 5, 9, 4, 4]), (true, [2, 6, 8, 2, 6, 4]), (true, [4, 6])]),
  (-53, [(true, [1, 7, 4, 5, 7, 2]), (true, [2, 7])]),
  (-54, [(true, [1, 7, 5, 3, 9, 6, 2]), (true, [3, 6, 6])]),
  (-55, [(true, [1, 7, 6, 5, 5]), (true, [2, 7, 3, 5, 10])]),
  (-56, [(true, [1, 7, 7]), (true, [2, 6, 10, 4, 4]), (true, [4, 6, 5, 4, 8])]),
  (-57, [(true, [1, 7, 8, 1, 7, 6, 3]), (true, [2, 7, 4, 5, 8, 3, 6])]),
  (-58, [(true, [1, 7, 9, 2, 6, 4, 7, 3]), (true, [2, 6, 11, 5, 3, 7])]),
  (-59, [(true, [1, 7, 10, 3, 5, 7, 2])]),
  (-60, [(true, [1, 7, 11, 4, 4]), (true, [2, 6, 12]), (true, [3, 6, 8, 2, 7, 5, 5]), (true, [4, 6, 6])]),
  (-61, [(true, [1, 7, 12, 5, 3, 7, 4, 5, 9, 4, 5, 6]), (true, [2, 7, 6, 5])]),
  (-62, [(true, [1, 7, 13, 6, 2])]),
  (-63, [(true, [1, 7, 14]), (true, [2, 7, 7]), (true, [3, 6, 9, 3, 6])]),
  (-65, [(true, [1, 8]), (true, [2, 7, 8, 1]), (false, [4, 5, 10, 5, 4, 7]), (true, [5, 5, 8, 3, 7, 4])]),
  (-66, [(true, [1, 8, 2]), (true, [3, 6, 10, 4, 5, 6, 6])]),
  (-67, [(true, [1, 8, 3, 7, 6, 5, 7, 2, 9, 7, 2])]),
  (-68, [(true, [1, 8, 4]), (true, [2, 8]), (true, [4, 6, 8, 2])]),
  (-69, [(true, [1, 8, 5, 7, 4, 5, 11, 6, 3]), (true, [2, 7, 10, 3, 6])]),
  (-70, [(true, [1, 8, 6, 4, 9, 5, 5]), (true, [2, 8, 3, 7, 7])]),
  (-71, [(true, [1, 8, 7, 6, 5, 4, 11, 7, 2])]),
  (-72, [(true, [1, 8, 8]), (true, [2, 8, 4]), (true, [3, 6, 12]), (true, [4, 6, 9, 3, 7, 4, 8]), (true, [6, 6])]),
  (-73, [(true, [1, 8, 9, 1, 8, 7, 3, 8]), (true, [2, 7, 12, 5, 4, 7, 6, 5, 8, 3])]),
  (-74, [(true, [1, 8, 10, 2, 7, 5]), (true, [2, 8, 5, 7])]),
  (-75, [(true, [1, 8, 11, 3, 6]), (true, [2, 7, 13, 6, 3]), (true, [5, 5, 10])]),
  (-76, [(true, [1, 8, 12, 4, 5, 6, 8, 2, 9, 7, 3, 8, 4]), (true, [2, 8, 6, 4, 10, 6, 4])]),
  (-77, [(true, [1, 8, 13, 5, 4, 7, 7]), (true, [2, 7, 14])]),
  (-78, [(true, [1, 8, 14, 6, 3]), (true, [2, 8, 7, 6, 6])]),
  (-79, [(true, [1, 8, 15, 7, 2]), (false, [3, 8, 5, 7, 6, 5, 9, 4, 7, 3, 10, 7])]),
  (-80, [(true, [1, 8, 16]), (true, [2, 8, 8]), (true, [4, 6, 11, 5, 5]), (true, [4, 8]), (true, [8, 4])]),
  (-82, [(true, [1, 9]), (true, [2, 8, 9, 1]), (false, [3, 7, 11, 4, 6, 8])]),
  (-83, [(true, [1, 9, 2])]),
  (-84, [(true, [1, 9, 3]), (true, [2, 8, 10, 2, 8, 6, 6]), (true, [4, 6, 12]), (true, [4, 8, 5, 7, 7])]),
  (-85, [(true, [1, 9, 4, 7, 9, 2]), (true, [2, 9]), (true, [5, 5, 12, 7, 3, 8, 7, 6]), (false, [6, 5, 10, 5, 6, 7])]),
  (-86, [(true, [1, 9, 5, 6, 10, 4, 7, 3, 11, 8, 2])]),
  (-87, [(true, [1, 9, 6]), (true, [2, 9, 3])]),
  (-88, [(true, [1, 9, 7, 5, 9, 4, 8]), (true, [2, 8, 12, 4, 6, 8, 4]), (true, [4, 6, 13, 7, 3, 8, 8])]),
  (-89, [(true, [1, 9, 8, 7, 5, 8]), (true, [2, 9, 4, 7, 10, 3, 8, 5])]),
  (-90, [(true, [1, 9, 9]), (true, [3, 9]), (true, [2, 8, 13, 5, 5]), (true, [6, 6, 9, 3])]),
  (-91, [(true, [1, 9, 10, 1, 9, 8, 3, 7, 14]), (true, [2, 9, 5, 6, 11, 5, 6, 7, 7])]),
  (-92, [(true, [1, 9, 11, 2, 8, 6, 7, 8, 4]), (true, [2, 8, 14, 6, 4])]),
  (-93, [(true, [1, 9, 12, 3, 7, 4, 11, 7, 4, 9, 3]), (true, [2, 9, 6])]),
  (-94, [(true, [1, 9, 13, 4, 6, 8, 5, 7, 9, 2, 10, 8, 3, 7, 15, 8, 2])]),
  (-95, [(true, [1, 9, 14, 5, 5]), (true, [2, 9, 7, 5, 10])]),
  (-96, [(true, [1, 9, 15, 6, 4]), (true, [3, 9, 5, 6, 12]), (true, [2, 8, 16]), (true, [4, 8, 8]), (true, [6, 6, 10, 4, 8])]),
  (-97, [(true, [1, 9, 16, 7, 3, 8, 11, 3, 8, 5, 9, 4]), (true, [2, 9, 8, 7, 6, 5, 12, 7, 4, 9])]),
  (-98, [(true, [1, 9, 17, 8, 2]), (true, [7, 7])]),
  (-99, [(true, [1, 9, 18]), (true, [2, 9, 9]), (true, [3, 9, 6]), (false, [5, 8, 7, 6, 9, 3, 10, 7])])]

/-- **Table 15.2a checked** for the transcribed determinants: every nonsquare $-50 \le d \le -2$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, Table 15.2a, p. 362"]
theorem table152_correct : ∀ e ∈ t152, TableOK e.1 e.2 := by
  decide +kernel

set_option maxHeartbeats 10000000 in
/-- **Table 15.2b checked** for the transcribed determinants: every nonsquare $-99 \le d \le -51$ (see the file
header for the entries fixed by the computation). One kernel check per determinant. -/
@[kb "conwaysloane1999" "Ch. 15, §3.3, Table 15.2b, p. 363"]
theorem table152b_correct : ∀ e ∈ t152b, TableOK e.1 e.2 := by
  intro e he
  simp only [t152b, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    decide +kernel

end Binary
end ConwaySloane
end QuadFormsKB
