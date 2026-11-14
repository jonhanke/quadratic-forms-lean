/-
# Chenevier–Lannes, Table 1.1: the 23 equi-Coxeter root systems of type ADE and rank 24

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 2 (Table 1.1), and §2.3, Proposition-Definition 2.3.3
(b), p. 35, and p. 36 (Venkov's list $R_1, \dots, R_{23}$). Printed page numbers.

**Layer.** Pure combinatorics of root-system *types*. An irreducible root system of type ADE is recorded by its type
(`ADEType`): $A_m$ ($m \ge 1$), $D_m$ ($m \ge 4$), $E_6$, $E_7$, $E_8$ (`ADEType.Valid`). A root system of type ADE is,
up to isomorphism, the multiset of the types of its irreducible components (a `Multiset ADEType`); this is the
classification of reduced root systems with all roots of the same length (Bourbaki, Chap. VI, §4), which the book
uses and which is not formalized here: only types are manipulated. For each type the file records
- the rank (`ADEType.rank`): $m$, $m$, $6$, $7$, $8$;
- the Coxeter number (`ADEType.coxeter`): $h(A_m) = m + 1$, $h(D_m) = 2m - 2$, $h(E_6) = 12$, $h(E_7) = 18$,
  $h(E_8) = 30$;
- the number of roots (`ADEType.numRoots`): $m(m+1)$, $2m(m-1)$, $72$, $126$, $240$.

**Defines** `niemeierRootTable`, Table 1.1 as a list of $23$ pairs (root system, Coxeter number).

**Proves** (all unconditional):
- `numRoots_eq_rank_mul_coxeter`: $|R| = \operatorname{rank}(R)\cdot h(R)$ for each irreducible type (the relation
  quoted in the Remarks after Proposition-Definition 2.3.3, p. 35);
- `niemeierRootTable_spec`: each of the $23$ entries is a nonempty root system of type ADE, of rank $24$, all of whose
  components have the displayed Coxeter number;
- `niemeierRootTable_nodup`: the $23$ entries are pairwise distinct;
- `mem_niemeierRootTable_of_equiCoxeter` (**completeness**, Venkov's list, p. 36): every nonempty equi-Coxeter root
  system of type ADE and rank $24$ is one of the $23$ entries;
- `niemeierRootTable_numRoots`: an entry with Coxeter number $h$ has $24h$ roots (Proposition-Definition 2.3.3 (c));
- `niemeierCoxeterTable_eq`: the Coxeter numbers of Table 1.1, together with $0$ for the Leech lattice, are the
  multiset `niemeierCoxeterTable` of `Classification.lean`.
-/
import QuadFormsKB.Literature.ChenevierLannes.Classification

namespace QuadFormsKB.ChenevierLannes

/-- **The type of an irreducible root system of type ADE** (Chenevier–Lannes, §1.1, p. 1: "its irreducible components
are of type $A_n$, $D_n$, $E_6$, $E_7$ or $E_8$"). Constructors: `A m` is $A_m$, `D m` is $D_m$ (only $m \ge 1$,
resp. $m \ge 4$, are root systems; see `ADEType.Valid`), and `E6`, `E7`, `E8`. -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (type ADE)"]
inductive ADEType
  /-- $A_m$, rank $m$. -/
  | A (m : ℕ)
  /-- $D_m$, rank $m$. -/
  | D (m : ℕ)
  /-- $E_6$. -/
  | E6
  /-- $E_7$. -/
  | E7
  /-- $E_8$. -/
  | E8
  deriving DecidableEq, Repr

namespace ADEType

/-- The rank of an irreducible root system of the given type. -/
def rank : ADEType → ℕ
  | A m => m
  | D m => m
  | E6 => 6
  | E7 => 7
  | E8 => 8

/-- **The Coxeter number** $h$ of an irreducible root system of the given type (Bourbaki, Chap. VI, Planches I–VII):
$h(A_m) = m + 1$, $h(D_m) = 2m - 2$, $h(E_6) = 12$, $h(E_7) = 18$, $h(E_8) = 30$. -/
def coxeter : ADEType → ℕ
  | A m => m + 1
  | D m => 2 * m - 2
  | E6 => 12
  | E7 => 18
  | E8 => 30

/-- The number of roots of an irreducible root system of the given type: $m(m+1)$ for $A_m$, $2m(m-1)$ for $D_m$,
and $72$, $126$, $240$ for $E_6$, $E_7$, $E_8$. -/
def numRoots : ADEType → ℕ
  | A m => m * (m + 1)
  | D m => 2 * m * (m - 1)
  | E6 => 72
  | E7 => 126
  | E8 => 240

/-- **The types that are root systems**: $A_m$ with $m \ge 1$, $D_m$ with $m \ge 4$ (the conventions $D_2 = A_1 A_1$,
$D_3 = A_3$ are excluded, so that a root system has exactly one type), and $E_6, E_7, E_8$. -/
def Valid : ADEType → Prop
  | A m => 1 ≤ m
  | D m => 4 ≤ m
  | _ => True

instance (t : ADEType) : Decidable t.Valid := by
  cases t <;> unfold Valid <;> infer_instance

/-- **$|R| = \operatorname{rank}(R)\cdot h(R)$ for an irreducible root system of type ADE** (Chenevier–Lannes, Remarks
after Proposition-Definition 2.3.3, p. 35; Bourbaki, Chap. VI, §1, Exercise 20). Unconditional (case check). -/
@[kb "chenevierlannes2019" "Remarks after Prop.-Def. 2.3.3, p. 35 (|R| = n h, irreducible types)"]
theorem numRoots_eq_rank_mul_coxeter (t : ADEType) (ht : t.Valid) : t.numRoots = t.rank * t.coxeter := by
  cases t with
  | A m => simp [numRoots, rank, coxeter]
  | D m =>
    simp only [Valid] at ht
    have : 2 * m - 2 = 2 * (m - 1) := by omega
    simp only [numRoots, rank, coxeter, this]
    ring
  | E6 => simp [numRoots, rank, coxeter]
  | E7 => simp [numRoots, rank, coxeter]
  | E8 => simp [numRoots, rank, coxeter]

end ADEType

open ADEType

/-- **A root system of type ADE** (up to isomorphism): a multiset of valid irreducible types. -/
def IsADE (R : Multiset ADEType) : Prop := ∀ t ∈ R, t.Valid

/-- The rank of a root system of type ADE: the sum of the ranks of its components. -/
def adeRank (R : Multiset ADEType) : ℕ := (R.map ADEType.rank).sum

/-- The number of roots of a root system of type ADE. -/
def adeNumRoots (R : Multiset ADEType) : ℕ := (R.map ADEType.numRoots).sum

/-- **Equi-Coxeter with Coxeter number $h$** (Chenevier–Lannes, Proposition-Definition 2.3.3 (b), p. 35): every
irreducible component has Coxeter number $h$. -/
def IsEquiCoxeter (R : Multiset ADEType) (h : ℕ) : Prop := ∀ t ∈ R, t.coxeter = h

/-- **Table 1.1** (Chenevier–Lannes, §1.1, p. 2): the $23$ root systems of type ADE and rank $24$ whose components all
have the same Coxeter number $h(R)$, as pairs $(R, h(R))$, in the book's order
$D_{24}$ ($46$), $D_{16}E_8$ ($30$), $3E_8$ ($30$), $A_{24}$ ($25$), $2D_{12}$ ($22$), $A_{17}E_7$ ($18$),
$D_{10}2E_7$ ($18$), $A_{15}D_9$ ($16$), $3D_8$ ($14$), $2A_{12}$ ($13$), $A_{11}D_7E_6$ ($12$), $4E_6$ ($12$),
$2A_9D_6$ ($10$), $4D_6$ ($10$), $3A_8$ ($9$), $2A_72D_5$ ($8$), $4A_6$ ($7$), $4A_5D_4$ ($6$), $6D_4$ ($6$),
$6A_4$ ($5$), $8A_3$ ($4$), $12A_2$ ($3$), $24A_1$ ($2$). (Index $i$ of the list is the book's $R_{i+1}$, p. 36.) -/
@[kb "chenevierlannes2019" "Table 1.1, p. 2"]
def niemeierRootTable : List (Multiset ADEType × ℕ) :=
  [({D 24}, 46), ({D 16, E8}, 30), (Multiset.replicate 3 E8, 30), ({A 24}, 25),
   (Multiset.replicate 2 (D 12), 22), ({A 17, E7}, 18), ({D 10, E7, E7}, 18), ({A 15, D 9}, 16),
   (Multiset.replicate 3 (D 8), 14), (Multiset.replicate 2 (A 12), 13), ({A 11, D 7, E6}, 12),
   (Multiset.replicate 4 E6, 12), ({A 9, A 9, D 6}, 10), (Multiset.replicate 4 (D 6), 10),
   (Multiset.replicate 3 (A 8), 9), ({A 7, A 7, D 5, D 5}, 8), (Multiset.replicate 4 (A 6), 7),
   (Multiset.replicate 4 (A 5) + {D 4}, 6), (Multiset.replicate 6 (D 4), 6), (Multiset.replicate 6 (A 4), 5),
   (Multiset.replicate 8 (A 3), 4), (Multiset.replicate 12 (A 2), 3), (Multiset.replicate 24 (A 1), 2)]

theorem niemeierRootTable_length : niemeierRootTable.length = 23 := rfl

/-- **The entries of Table 1.1 are as described** (Chenevier–Lannes, Table 1.1, p. 2): each entry $(R, h)$ is a
nonempty root system of type ADE, of rank $24$, equi-Coxeter with Coxeter number $h$. Unconditional. -/
@[kb "chenevierlannes2019" "Table 1.1, p. 2 (the entries)"]
theorem niemeierRootTable_spec : ∀ e ∈ niemeierRootTable,
    e.1 ≠ 0 ∧ IsADE e.1 ∧ adeRank e.1 = 24 ∧ IsEquiCoxeter e.1 e.2 := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> simp only [IsADE, adeRank, IsEquiCoxeter] <;> decide

/-- **The $23$ root systems of Table 1.1 are pairwise non-isomorphic**: the list of multisets has no repetition. -/
theorem niemeierRootTable_nodup : (niemeierRootTable.map Prod.fst).Nodup := by
  decide

private lemma decomp {R : Multiset ADEType} {h : ℕ} (hR : IsADE R) (hh : IsEquiCoxeter R h) :
    R = Multiset.replicate (R.count (A (h - 1))) (A (h - 1)) +
      Multiset.replicate (R.count (D (h / 2 + 1))) (D (h / 2 + 1)) +
      Multiset.replicate (R.count E6) E6 + Multiset.replicate (R.count E7) E7 +
      Multiset.replicate (R.count E8) E8 := by
  ext x
  by_cases hx : x ∈ R
  · have h1 := hh x hx
    have h2 := hR x hx
    cases x with
    | A m =>
      simp only [coxeter, Valid] at h1 h2
      have : m = h - 1 := by omega
      subst this
      simp [Multiset.count_replicate]
    | D m =>
      simp only [coxeter, Valid] at h1 h2
      have : m = h / 2 + 1 := by omega
      subst this
      simp [Multiset.count_replicate]
    | E6 => simp [Multiset.count_replicate]
    | E7 => simp [Multiset.count_replicate]
    | E8 => simp [Multiset.count_replicate]
  · have h0 : R.count x = 0 := Multiset.count_eq_zero.2 hx
    simp only [Multiset.count_add, Multiset.count_replicate, h0]
    split_ifs <;> simp_all

/-- The $23$ solutions $(h, a, d, x, y, z)$ of the rank equation in `completeness_arith`. -/
private def goodList : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(46, 0, 1, 0, 0, 0), (30, 0, 1, 0, 0, 1), (30, 0, 0, 0, 0, 3), (25, 1, 0, 0, 0, 0), (22, 0, 2, 0, 0, 0),
   (18, 1, 0, 0, 1, 0), (18, 0, 1, 0, 2, 0), (16, 1, 1, 0, 0, 0), (14, 0, 3, 0, 0, 0), (13, 2, 0, 0, 0, 0),
   (12, 1, 1, 1, 0, 0), (12, 0, 0, 4, 0, 0), (10, 2, 1, 0, 0, 0), (10, 0, 4, 0, 0, 0), (9, 3, 0, 0, 0, 0),
   (8, 2, 2, 0, 0, 0), (7, 4, 0, 0, 0, 0), (6, 4, 1, 0, 0, 0), (6, 0, 6, 0, 0, 0), (5, 6, 0, 0, 0, 0),
   (4, 8, 0, 0, 0, 0), (3, 12, 0, 0, 0, 0), (2, 24, 0, 0, 0, 0)]

/-- The equi-Coxeter root system with Coxeter number $h$ and $a, d, x, y, z$ components of types $A_{h-1}$,
$D_{h/2+1}$, $E_6$, $E_7$, $E_8$. -/
private def mkR (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Multiset ADEType :=
  Multiset.replicate t.2.1 (A (t.1 - 1)) + Multiset.replicate t.2.2.1 (D (t.1 / 2 + 1)) +
    Multiset.replicate t.2.2.2.1 E6 + Multiset.replicate t.2.2.2.2.1 E7 + Multiset.replicate t.2.2.2.2.2 E8

private lemma goodList_table : ∀ t ∈ goodList, (mkR t, t.1) ∈ niemeierRootTable := by
  decide +kernel

/-- The arithmetic core of the completeness of Table 1.1: the solutions of
$a(h-1) + d(h/2+1) + 6x + 7y + 8z = 24$ under the constraints that make each component a valid type with Coxeter
number $h$. -/
private lemma completeness_arith {h a d x y z : ℕ}
    (hrank : a * (h - 1) + d * (h / 2 + 1) + 6 * x + 7 * y + 8 * z = 24)
    (cA : a = 0 ∨ 2 ≤ h) (cD : d = 0 ∨ (6 ≤ h ∧ h % 2 = 0)) (c6 : x = 0 ∨ h = 12) (c7 : y = 0 ∨ h = 18)
    (c8 : z = 0 ∨ h = 30) (hpos : 0 < a + d + x + y + z) : (h, a, d, x, y, z) ∈ goodList := by
  have ha : a ≤ 24 / (h - 1) := by
    rcases cA with rfl | h2
    · exact Nat.zero_le _
    · refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
      generalize a * (h - 1) = P at hrank ⊢
      omega
  have hd : d ≤ 24 / (h / 2 + 1) := by
    refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
    generalize d * (h / 2 + 1) = P at hrank ⊢
    omega
  have hx : x ≤ 4 := by omega
  have hy : y ≤ 3 := by omega
  have hz : z ≤ 3 := by omega
  rcases c6 with rfl | rfl
  · rcases c7 with rfl | rfl
    · rcases c8 with rfl | rfl
      · have hle : h ≤ 46 := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · rcases Nat.eq_zero_or_pos d with h1 | h1
            · omega
            · have := Nat.le_mul_of_pos_left (h / 2 + 1) h1
              omega
          · have := Nat.le_mul_of_pos_left (h - 1) h0
            rcases cA with rfl | h2 <;> omega
        interval_cases h <;> simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at ha hd <;>
          interval_cases a <;> interval_cases d <;> first | omega | decide
      · simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at ha hd
        interval_cases a <;> interval_cases d <;> interval_cases z <;> first | omega | decide
    · obtain rfl : z = 0 := by omega
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at ha hd
      interval_cases a <;> interval_cases d <;> interval_cases y <;> first | omega | decide
  · obtain rfl : y = 0 := by omega
    obtain rfl : z = 0 := by omega
    simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at ha hd
    interval_cases a <;> interval_cases d <;> interval_cases x <;> first | omega | decide

/-- **Completeness of Table 1.1** (Chenevier–Lannes, p. 36, after Corollary 2.3.6: "Venkov begins by listing the
isomorphism classes of such root systems explicitly. This list has 23 elements"): every nonempty root system $R$ of
type ADE and rank $24$ that is equi-Coxeter with Coxeter number $h$ is an entry of Table 1.1, with that $h$.
Unconditional (an enumeration over $h \le 46$ and the multiplicities of $A_{h-1}$, $D_{h/2+1}$ and $E_6, E_7, E_8$). -/
@[kb "chenevierlannes2019" "p. 36 (Venkov's list of 23 root systems); Table 1.1, p. 2"]
theorem mem_niemeierRootTable_of_equiCoxeter {R : Multiset ADEType} {h : ℕ} (hR0 : R ≠ 0) (hR : IsADE R)
    (hrank : adeRank R = 24) (hh : IsEquiCoxeter R h) : (R, h) ∈ niemeierRootTable := by
  have hdec := decomp hR hh
  have hrk : adeRank R = R.count (A (h - 1)) * (h - 1) + R.count (D (h / 2 + 1)) * (h / 2 + 1) +
      6 * R.count E6 + 7 * R.count E7 + 8 * R.count E8 := by
    conv_lhs => rw [hdec]
    simp [adeRank, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
      rank]
    ring
  have cA : 0 < R.count (A (h - 1)) → 2 ≤ h := fun hp => by
    have m := Multiset.count_pos.1 hp
    have h1 := hh _ m
    have h2 := hR _ m
    simp only [coxeter, Valid] at h1 h2
    omega
  have cD : 0 < R.count (D (h / 2 + 1)) → 6 ≤ h ∧ h % 2 = 0 := fun hp => by
    have m := Multiset.count_pos.1 hp
    have h1 := hh _ m
    have h2 := hR _ m
    simp only [coxeter, Valid] at h1 h2
    omega
  have c6 : 0 < R.count E6 → h = 12 := fun hp => by
    have := hh _ (Multiset.count_pos.1 hp)
    simpa [coxeter] using this.symm
  have c7 : 0 < R.count E7 → h = 18 := fun hp => by
    have := hh _ (Multiset.count_pos.1 hp)
    simpa [coxeter] using this.symm
  have c8 : 0 < R.count E8 → h = 30 := fun hp => by
    have := hh _ (Multiset.count_pos.1 hp)
    simpa [coxeter] using this.symm
  have hpos : 0 < R.count (A (h - 1)) + R.count (D (h / 2 + 1)) + R.count E6 + R.count E7 +
      R.count E8 := by
    have hc : 0 < Multiset.card R := Multiset.card_pos.2 hR0
    have := congrArg Multiset.card hdec
    simp only [Multiset.card_add, Multiset.card_replicate] at this
    omega
  rw [hrk] at hrank
  rw [hdec]
  generalize R.count (A (h - 1)) = a at *
  generalize R.count (D (h / 2 + 1)) = d at *
  generalize R.count E6 = x at *
  generalize R.count E7 = y at *
  generalize R.count E8 = z at *
  have cA' : a = 0 ∨ 2 ≤ h := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    exacts [Or.inl h0, Or.inr (cA h0)]
  have cD' : d = 0 ∨ (6 ≤ h ∧ h % 2 = 0) := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    exacts [Or.inl h0, Or.inr (cD h0)]
  have c6' : x = 0 ∨ h = 12 := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    exacts [Or.inl h0, Or.inr (c6 h0)]
  have c7' : y = 0 ∨ h = 18 := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    exacts [Or.inl h0, Or.inr (c7 h0)]
  have c8' : z = 0 ∨ h = 30 := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    exacts [Or.inl h0, Or.inr (c8 h0)]
  exact goodList_table _ (completeness_arith hrank cA' cD' c6' c7' c8' hpos)

/-- **$|R| = 24\,h(R)$ for the entries of Table 1.1** (Chenevier–Lannes, Proposition-Definition 2.3.3 (c), p. 35, on the
root-system side). Unconditional. -/
theorem niemeierRootTable_numRoots : ∀ e ∈ niemeierRootTable, adeNumRoots e.1 = 24 * e.2 := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp only [adeNumRoots] <;> decide

/-- **The Coxeter numbers of Table 1.1 and the Leech lattice** form the multiset `niemeierCoxeterTable` used in the
numerical form of Niemeier's theorem (`NiemeierCoxeterNumbers`). Unconditional. -/
theorem niemeierCoxeterTable_eq :
    (0 : ℚ) ::ₘ ((niemeierRootTable.map fun e => (e.2 : ℚ)) : Multiset ℚ) = niemeierCoxeterTable := by
  simp [niemeierRootTable, niemeierCoxeterTable]
  rfl

end QuadFormsKB.ChenevierLannes
