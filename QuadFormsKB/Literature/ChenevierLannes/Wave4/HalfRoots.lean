/-
# Chenevier–Lannes, §3.4.4–§3.4.5: the root systems $R/2$ and the map $\psi$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.4, "Comments", pp. 85–87: the root system $R/2$ of roots
of even height, the number $h'(R) = h(R)/2 - \iota(R)/8 + 2$, Proposition-Definition 3.4.5 (the map
$\psi : \mathrm{YR}_{24} \to \mathrm{Y}_{24}$), the Remark after it, Proposition 3.4.5.1, Proposition 3.4.5.2,
Scholium 3.4.5.3 and Figure 3.1. Printed page numbers.

**Layer.** Root systems of type ADE up to isomorphism are multisets of irreducible types (`ADEType`);
$\mathrm{YR}_{24}$ is Table 1.1 (`niemeierRootTable`, the $23$ equi-Coxeter root systems of rank $24$, with their
Coxeter numbers) and $\mathrm{Y}_{24} = \mathrm{YR}_{24} \sqcup \{\emptyset\}$ is indexed here by `Fin 24`, index
$23$ being $\emptyset$ (the Leech lattice) with Coxeter number $0$ (`yEntry`).

**Inclusions of root systems.** The book's condition "$R/2 \subset \psi(R)$" is an inclusion of root systems. Two
standard necessary conditions for an inclusion $S \subset S'$ of root systems of type ADE are encoded by `HalfFits`:
(1) $|S| \le |S'|$, with equality only if $S = S'$ (then the two root sets coincide); (2) every irreducible component of
$S$ has rank at most the largest rank of an irreducible component of $S'$ (an irreducible subsystem lies in one irreducible
component of $S'$, since distinct components are orthogonal). These two facts about root systems are not formalized;
the theorems below are about `HalfFits`, which is all that the book's uniqueness argument (p. 86) uses.

**Proves** (unconditional, by computation over Table 1.1):
- `half_numRoots_table`: $|R/2| = 12h(R) - \iota(R)$ for the $23$ root systems (the root-system side of
  Proposition 3.4.4.3);
- `psi_spec`, `psi_unique` (Proposition-Definition 3.4.5, with `HalfFits` for the inclusion): $\psi$ (`psiIdx`, read
  off Figure 3.1) satisfies $h(\psi(R)) = h'(R)$ and `HalfFits (R/2) ψ(R)`, and it is the only map into
  $\mathrm{Y}_{24}$ that does;
- `psi_eq_half_iff` (the Remark after Proposition-Definition 3.4.5);
- `coxeter_psi_le` ($h(\psi(R)) - 1 \le (h(R) - 1)/2$) and `psi_iterate_eq_leech` (Proposition 3.4.5.1:
  $\psi^k(R) = \emptyset$ for $h(R) < 2^k + 1$).

**States** `TwoNeighborRootType` (Proposition 3.4.5.2: the root system of $\mathrm{vois}_2(L; \rho)$ is $\psi(R(L))$),
and proves Scholium 3.4.5.3 for $k = 1$ from it (`twoNeighbor_rootless`).

*Erratum* (p. 86): the book prints $(\mathbf{A}_{11}\mathbf{D}_7\mathbf{E}_6)/2 = \mathbf{A}_1\mathbf{A}_3\mathbf{A}_4
3\mathbf{A}_5$; by the book's own rule $\mathbf{D}_{2m+1}/2 = \mathbf{D}_{m+1}\mathbf{D}_m$ (p. 85),
$\mathbf{D}_7/2 = \mathbf{D}_4\mathbf{D}_3 = \mathbf{D}_4\mathbf{A}_3$, so the correct value is
$\mathbf{A}_1\mathbf{A}_3\mathbf{D}_4 3\mathbf{A}_5$, with $128 = 12 \cdot 12 - 16$ roots as Proposition 3.4.4.3
requires ($\mathbf{A}_4$ would give $124$). The conclusion $\not\subset 6\mathbf{D}_4$ is unaffected ($\mathbf{A}_5$ has
rank $5$). Checked on the scan; `half_A11D7E6`.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.Statements

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser ADEType

/-! ### The root system $R/2$ -/

/-- $\mathbf{A}_k$ with the convention $\mathbf{A}_0 = \emptyset$. -/
def aTypeConv (k : ℕ) : Multiset ADEType := if k = 0 then 0 else {A k}

/-- $\mathbf{D}_k$ with the conventions $\mathbf{D}_2 = \mathbf{A}_1\mathbf{A}_1$, $\mathbf{D}_3 = \mathbf{A}_3$ (and
$\mathbf{D}_1 = \mathbf{D}_0 = \emptyset$, which do not occur below for valid types). -/
def dTypeConv (k : ℕ) : Multiset ADEType :=
  if k ≤ 1 then 0 else if k = 2 then {A 1, A 1} else if k = 3 then {A 3} else {D k}

/-- **$R/2$ for an irreducible type** (Chenevier–Lannes, §3.4.4, p. 85): the sub-root system of roots of even height
(for the height function of a chamber):
$\mathbf{A}_{2m}/2 = \mathbf{A}_m\mathbf{A}_{m-1}$, $\mathbf{A}_{2m+1}/2 = \mathbf{A}_m\mathbf{A}_m$,
$\mathbf{D}_{2m}/2 = \mathbf{D}_m\mathbf{D}_m$, $\mathbf{D}_{2m+1}/2 = \mathbf{D}_{m+1}\mathbf{D}_m$,
$\mathbf{E}_6/2 = \mathbf{A}_5\mathbf{A}_1$, $\mathbf{E}_7/2 = \mathbf{A}_7$, $\mathbf{E}_8/2 = \mathbf{D}_8$
(with $\mathbf{A}_0 = \emptyset$, $\mathbf{D}_2 = \mathbf{A}_1\mathbf{A}_1$, $\mathbf{D}_3 = \mathbf{A}_3$). The book
states this list without proof; it is taken here as the definition. -/
@[kb "chenevierlannes2019" "§3.4.4, p. 85 (R/2, irreducible types)"]
def ADEType.half : ADEType → Multiset ADEType
  | A l => aTypeConv (l / 2) + aTypeConv (if l % 2 = 0 then l / 2 - 1 else l / 2)
  | D l => dTypeConv ((l + 1) / 2) + dTypeConv (l / 2)
  | E6 => {A 5, A 1}
  | E7 => {A 7}
  | E8 => {D 8}

/-- **$R/2$** (Chenevier–Lannes, §3.4.4, p. 85): additive, $(R_1 R_2)/2 = (R_1/2)(R_2/2)$. -/
@[kb "chenevierlannes2019" "§3.4.4, p. 85 (R/2)"]
def adeHalf (R : Multiset ADEType) : Multiset ADEType := R.bind ADEType.half

/-- The erratum of p. 86: $(\mathbf{A}_{11}\mathbf{D}_7\mathbf{E}_6)/2 = \mathbf{A}_1\mathbf{A}_3\mathbf{D}_4
3\mathbf{A}_5$ (the book prints $\mathbf{A}_4$ for $\mathbf{D}_4$). -/
@[kb "chenevierlannes2019" "§3.4.4, p. 86 ((A11 D7 E6)/2; erratum)"]
theorem half_A11D7E6 : adeHalf {A 11, D 7, E6} = {A 1, A 3, D 4, A 5, A 5, A 5} := by decide

/-- **$|R/2| = 12h(R) - \iota(R)$ on Table 1.1** (the root-system side of Chenevier–Lannes, Proposition 3.4.4.3, p. 82:
the roots of even height are those $\alpha$ with $\rho \cdot \alpha$ even). Unconditional, by computation. -/
@[kb "chenevierlannes2019" "Prop. 3.4.4.3, p. 82 (on R/2, Table 1.1)"]
theorem half_numRoots_table : ∀ e ∈ niemeierRootTable, adeNumRoots (adeHalf e.1) + adeIota e.1 = 12 * e.2 := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  decide

/-! ### $\mathrm{Y}_{24}$, $h'$ and $\psi$ -/

/-- **$\mathrm{Y}_{24}$** (Chenevier–Lannes, p. 85): the $23$ root systems of Table 1.1 with their Coxeter numbers,
followed by $(\emptyset, 0)$ (the Leech lattice), indexed by `Fin 24`. -/
@[kb "chenevierlannes2019" "§3.4.4, p. 85 (Y_24)"]
def yEntry (i : Fin 24) : Multiset ADEType × ℕ := (niemeierRootTable ++ [(0, 0)]).getD i (0, 0)

/-- **$h'(R) = h(R)/2 - \iota(R)/8 + 2$** (Chenevier–Lannes, p. 85), computed as $(4h + 16 - \iota)/8$ (exact on
Table 1.1, `iota_table`). -/
@[kb "chenevierlannes2019" "§3.4.4, p. 85 (h'(R))"]
def hPrime (R : Multiset ADEType) (h : ℕ) : ℕ := (4 * h + 16 - adeIota R) / 8

/-- **Necessary conditions for an inclusion of root systems $S \subset S'$** (see the header): $|S| \le |S'|$, with
equality only for $S = S'$, and each irreducible component of $S$ has rank at most the largest rank of a component of $S'$. -/
def HalfFits (S S' : Multiset ADEType) : Prop :=
  adeNumRoots S ≤ adeNumRoots S' ∧ (adeNumRoots S = adeNumRoots S' → S = S') ∧
    ∀ t ∈ S, t.rank ≤ (S'.map ADEType.rank).sup

instance (S S' : Multiset ADEType) : Decidable (HalfFits S S') := by
  unfold HalfFits
  exact instDecidableAnd

/-- **The map $\psi$ of Figure 3.1** (Chenevier–Lannes, p. 87), on indices of $\mathrm{Y}_{24}$:
$\mathbf{D}_{24} \mapsto 2\mathbf{D}_{12}$, $\mathbf{D}_{16}\mathbf{E}_8, 3\mathbf{E}_8 \mapsto 3\mathbf{D}_8$,
$\mathbf{A}_{24} \mapsto 2\mathbf{A}_{12}$, $2\mathbf{D}_{12} \mapsto 4\mathbf{D}_6$,
$\mathbf{A}_{17}\mathbf{E}_7 \mapsto 3\mathbf{A}_8$, $\mathbf{D}_{10}2\mathbf{E}_7, \mathbf{A}_{15}\mathbf{D}_9 \mapsto
2\mathbf{A}_72\mathbf{D}_5$, $3\mathbf{D}_8 \mapsto 6\mathbf{D}_4$, $2\mathbf{A}_{12} \mapsto 4\mathbf{A}_6$,
$\mathbf{A}_{11}\mathbf{D}_7\mathbf{E}_6, 4\mathbf{E}_6 \mapsto 4\mathbf{A}_5\mathbf{D}_4$,
$2\mathbf{A}_9\mathbf{D}_6, 3\mathbf{A}_8 \mapsto 6\mathbf{A}_4$,
$4\mathbf{D}_6, 2\mathbf{A}_72\mathbf{D}_5, 4\mathbf{A}_6 \mapsto 8\mathbf{A}_3$,
$4\mathbf{A}_5\mathbf{D}_4, 6\mathbf{A}_4 \mapsto 12\mathbf{A}_2$, $6\mathbf{D}_4, 8\mathbf{A}_3, 12\mathbf{A}_2 \mapsto
24\mathbf{A}_1$, $24\mathbf{A}_1 \mapsto \emptyset$, and $\psi(\emptyset) = \emptyset$. -/
@[kb "chenevierlannes2019" "Fig. 3.1, p. 87 (the map ψ)"]
def psiIdx : Fin 24 → Fin 24 :=
  ![4, 8, 8, 9, 13, 14, 15, 15, 18, 16, 17, 17, 19, 20, 19, 20, 20, 21, 22, 21, 22, 22, 23, 23]

/-- **Proposition-Definition 3.4.5, existence** (Chenevier–Lannes, p. 86), with `HalfFits` for the inclusion: for each
$R \in \mathrm{YR}_{24}$, $h(\psi(R)) = h'(R)$ and `HalfFits (R/2) ψ(R)`. Unconditional, by computation. -/
@[kb "chenevierlannes2019" "Prop.-Def. 3.4.5, p. 86 (existence; inclusion via HalfFits)"]
theorem psi_spec : ∀ i : Fin 24, i ≠ 23 →
    (yEntry (psiIdx i)).2 = hPrime (yEntry i).1 (yEntry i).2 ∧ HalfFits (adeHalf (yEntry i).1) (yEntry (psiIdx i)).1 := by
  decide

/-- **Proposition-Definition 3.4.5, uniqueness** (Chenevier–Lannes, p. 86), with `HalfFits` for the inclusion: if
$S \in \mathrm{Y}_{24}$ has $h(S) = h'(R)$ and `HalfFits (R/2) S`, then $S = \psi(R)$. The fibres of $h$ with more than
one element are $h^{-1}(12)$, $h^{-1}(10)$, $h^{-1}(6)$ (p. 85); in the two that are hit, the rejected candidate fails
`HalfFits`: $4\mathbf{D}_6 \ne 2\mathbf{A}_9\mathbf{D}_6$ with $240$ roots each, $6\mathbf{D}_4 \ne
4\mathbf{A}_5\mathbf{D}_4$ with $144$ roots each, and $\mathbf{A}_5$ (rank $5$) is in no $\mathbf{D}_4$. Unconditional,
by computation. -/
@[kb "chenevierlannes2019" "Prop.-Def. 3.4.5, p. 86 (uniqueness; inclusion via HalfFits)"]
theorem psi_unique : ∀ i j : Fin 24, i ≠ 23 → (yEntry j).2 = hPrime (yEntry i).1 (yEntry i).2 →
    HalfFits (adeHalf (yEntry i).1) (yEntry j).1 → j = psiIdx i := by
  decide

/-- **The Remark after Proposition-Definition 3.4.5** (Chenevier–Lannes, p. 86): for $R \in \mathrm{YR}_{24}$, the
following are equivalent: $\psi(R) = R/2$; $\iota(R) = 24$; every irreducible component of $R$ is of type
$\mathbf{A}_1$, $\mathbf{D}_l$ with $l$ even, $\mathbf{E}_7$ or $\mathbf{E}_8$. Unconditional, by computation. -/
@[kb "chenevierlannes2019" "Remark after Prop.-Def. 3.4.5, p. 86"]
theorem psi_eq_half_iff : ∀ i : Fin 24, i ≠ 23 →
    ((yEntry (psiIdx i)).1 = adeHalf (yEntry i).1 ↔ adeIota (yEntry i).1 = 24) ∧
    (adeIota (yEntry i).1 = 24 ↔
      ∀ t ∈ (yEntry i).1, t = A 1 ∨ (∃ l, t = D l ∧ l % 2 = 0) ∨ t = E7 ∨ t = E8) := by
  intro i hi
  fin_cases i <;> simp_all [yEntry, psiIdx, niemeierRootTable, adeIota, adeHalf] <;> decide

/-- **$h(\psi(R)) - 1 \le (h(R) - 1)/2$** (Chenevier–Lannes, p. 86, the note after Proposition 3.4.5.1), in the form
$2h(\psi(R)) \le h(R) + 1$ on $\mathrm{Y}_{24}$ (with $h(\emptyset) = 0$). Unconditional, by computation. -/
@[kb "chenevierlannes2019" "§3.4.5, p. 86 (h(ψ(R)) − 1 ≤ (h(R) − 1)/2)"]
theorem coxeter_psi_le : ∀ i : Fin 24, 2 * (yEntry (psiIdx i)).2 ≤ (yEntry i).2 + 1 := by
  decide

/-- $\psi(R) = \emptyset$ when $h(R) \le 2$, and $h(R) = 0$ only for $R = \emptyset$. -/
theorem psi_leech_of_le_two : ∀ i : Fin 24, (yEntry i).2 ≤ 2 → psiIdx i = 23 := by
  decide

/-- **Proposition 3.4.5.1** (Chenevier–Lannes, p. 86): for $R \in \mathrm{Y}_{24}$ and $k \ge 1$, $\psi^k(R) = \emptyset$
when $h(R) < 2^k + 1$. Unconditional: induction on $k$ from `coxeter_psi_le` and `psi_leech_of_le_two`. -/
@[kb "chenevierlannes2019" "Prop. 3.4.5.1, p. 86"]
theorem psi_iterate_eq_leech (k : ℕ) (hk : 1 ≤ k) (i : Fin 24) (hi : (yEntry i).2 < 2 ^ k + 1) :
    psiIdx^[k] i = 23 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact psi_leech_of_le_two i (by simpa using Nat.lt_succ_iff.mp hi)
    · apply ih hk1
      have h1 := coxeter_psi_le i
      have : (yEntry i).2 ≤ 2 ^ (k + 1) := by omega
      rw [pow_succ] at this
      omega

/-! ### Proposition 3.4.5.2 and Scholium 3.4.5.3 -/

/-- **Proposition 3.4.5.2** (Chenevier–Lannes, p. 86; named statement): $R(\varphi([L])) = \psi(R([L]))$, where
$\varphi([L]) = [\mathrm{vois}_2(L; \rho)]$ for a Weyl vector $\rho$. Stated as: for a Niemeier lattice $L$ whose root
system is the entry $i$ of Table 1.1 (`HasRootType`), a Weyl vector $\rho \in L$ and $v \in L$ with
$\rho \cdot v$ odd, the lattice $\mathrm{vois}_2(L; \rho)$ (`voisLat Q 2 ρ v`) has a basis $g$ in which its form $P$
is a Niemeier lattice whose root system is $\psi(R)$ (no roots when $\psi(R) = \emptyset$). The book derives it from
Proposition 3.4.4.2 (`CoxeterOfTwoNeighbor`, stated in wave 4), the inclusion $R/2 \subset R(\varphi([L]))$ and
Proposition-Definition 3.4.5; the first is not proved, and the inclusion of root systems is not formalized. -/
@[kb "chenevierlannes2019" "Prop. 3.4.5.2, p. 86"]
def TwoNeighborRootType : Prop :=
  ∀ (i : Fin 24), i ≠ 23 → ∀ Q : QuadForm ℤ 24, IsNiemeier Q → HasRootType Q (yEntry i).1 →
    ∀ ρ : Fin 24 → ℤ, IsWeylVector Q (cv ρ) → ∀ v : Fin 24 → ℤ, ¬ (2 : ℤ) ∣ bZ Q ρ v →
      ∃ (g : Matrix (Fin 24) (Fin 24) ℚ) (P : QuadForm ℤ 24), g.det ≠ 0 ∧ imgLat g = voisLat Q 2 ρ v ∧
        (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsNiemeier P ∧
        (if psiIdx i = 23 then rootSet P = ∅ else HasRootType P (yEntry (psiIdx i)).1)

/-- **Scholium 3.4.5.3 for $k = 1$** (Chenevier–Lannes, p. 86): **conditional** on `TwoNeighborRootType`. If $L$ has
root system $R$ with $h(R) < 3$ (that is, $R = 24\mathbf{A}_1$), then $\varphi([L]) = [\mathrm{vois}_2(L; \rho)]$ has no
roots. (For general $k$ the book iterates $\varphi$, which needs a Weyl vector of each iterate; not stated.) -/
@[kb "chenevierlannes2019" "Scholium 3.4.5.3, p. 86 (k = 1; conditional)"]
theorem twoNeighbor_rootless (hT : TwoNeighborRootType) {i : Fin 24} (hi : i ≠ 23) (hh : (yEntry i).2 < 2 ^ 1 + 1)
    {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : HasRootType Q (yEntry i).1) {ρ : Fin 24 → ℤ}
    (hρ : IsWeylVector Q (cv ρ)) {v : Fin 24 → ℤ} (hv : ¬ (2 : ℤ) ∣ bZ Q ρ v) :
    ∃ (g : Matrix (Fin 24) (Fin 24) ℚ) (P : QuadForm ℤ 24), g.det ≠ 0 ∧ imgLat g = voisLat Q 2 ρ v ∧
      (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsLeechType P := by
  obtain ⟨g, P, hg, himg, hP, hN, hroot⟩ := hT i hi Q hQ hR ρ hρ v hv
  have h23 : psiIdx i = 23 := psi_iterate_eq_leech 1 le_rfl i hh
  rw [if_pos h23] at hroot
  exact ⟨g, P, hg, himg, hP, hN, hroot⟩

end QuadFormsKB.ChenevierLannes
