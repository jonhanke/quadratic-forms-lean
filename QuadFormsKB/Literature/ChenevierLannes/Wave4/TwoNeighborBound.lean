/-
# Chenevier–Lannes, §3.4.4: the Coxeter number of $\mathrm{vois}_2(L; \rho)$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.4, Proposition 3.4.4.1 and the discussion after
Proposition 3.4.4.2, pp. 81–82. Printed page numbers.

For a Niemeier lattice $L$ with roots, Coxeter number $h$, root system $R$ and a Weyl vector $\rho$, Proposition 3.4.4.2
(`CoxeterOfTwoNeighbor`, stated in wave 4) gives $h(\mathrm{vois}_2(L; \rho)) = h/2 - \iota(R)/8 + 2$. The book
deduces from it:
- Proposition 3.4.4.1: $h(\mathrm{vois}_2(L; \rho)) \le (h + 1)/2$ (`prop_3_4_4_1`);
- the equivalence of (i) $h$ odd, (ii) $R \cong (24/d)\mathbf{A}_d$ for an even divisor $d$ of $24$, (iii) equality in
  Proposition 3.4.4.1 (`twoNeighbor_equality_iff`, `odd_coxeter_iff_table`).

**Proves**: `odd_coxeter_iff_table` (unconditional, by computation on Table 1.1); `prop_3_4_4_1` and
`twoNeighbor_equality_iff`, **conditional** on `CoxeterOfTwoNeighbor` (Proposition 3.4.4.2) and
`EquiCoxeterRootSystem 24` (Proposition-Definition 2.3.3: $R(L)$ is an equi-Coxeter root system of type ADE of rank
$24$, so that it is an entry of Table 1.1). The book's first proof of Proposition 3.4.4.1 (through Proposition 3.1.13
and the holy constructions) is not formalized: Proposition 3.1.13 needs neighbours of a lattice other than
$\mathbb{Z}^{24}$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.Statements

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

/-- **Odd Coxeter numbers in Table 1.1** (Chenevier–Lannes, p. 82): for an entry $(R, h)$ of Table 1.1, $h$ is odd if
and only if $R = (24/d)\mathbf{A}_d$ for an even divisor $d$ of $24$. Unconditional (by computation). -/
@[kb "chenevierlannes2019" "§3.4.4, p. 82 (h odd iff R = (24/d) A_d, d even)"]
theorem odd_coxeter_iff_table : ∀ e ∈ niemeierRootTable,
    e.2 % 2 = 1 ↔ ∃ d ∈ ({2, 4, 6, 8, 12, 24} : Finset ℕ), e.1 = Multiset.replicate (24 / d) (ADEType.A d) := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  decide

/-- The value of Proposition 3.4.4.2 on an entry of Table 1.1. -/
theorem twoNeighbor_value {Q : QuadForm ℤ 24} (hC : CoxeterOfTwoNeighbor) (hE : EquiCoxeterRootSystem 24)
    (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {r v : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv r))
    (hv : (2 : ℤ) ∣ bZ Q r v - 1) :
    ∃ e ∈ niemeierRootTable, coxeterNumber Q = e.2 ∧
      (latRepNum Q (voisLat Q 2 r v) 2 : ℚ) / 24 = (e.2 : ℚ) / 2 - (adeIota e.1 : ℚ) / 8 + 2 := by
  obtain ⟨e, he, htype, hcox⟩ := rootType_mem_table hE hQ hR
  refine ⟨e, he, hcox, ?_⟩
  rw [hC Q hQ hR e.1 htype r v hρ hv, hcox]

/-- **Proposition 3.4.4.1** (Chenevier–Lannes, p. 81): **conditional** on `CoxeterOfTwoNeighbor` (Proposition
3.4.4.2) and `EquiCoxeterRootSystem 24`. For a Niemeier lattice $L$ with roots, a Weyl vector $\rho \in L$ and $v$
with $\rho \cdot v$ odd,
$$h(\mathrm{vois}_2(L; \rho)) \le \frac{h(L) + 1}{2},$$
where $h(\mathrm{vois}_2(L; \rho)) = r_2/24$ (`latRepNum`; $0$ for the Leech lattice, the book's convention). *Proof*
(the book's, p. 82): Proposition 3.4.4.2 and $24 \le 2\iota(R)$ (`iota_table`). -/
@[kb "chenevierlannes2019" "Prop. 3.4.4.1, p. 81 (conditional)"]
theorem prop_3_4_4_1 (hC : CoxeterOfTwoNeighbor) (hE : EquiCoxeterRootSystem 24) {Q : QuadForm ℤ 24}
    (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {r v : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv r))
    (hv : (2 : ℤ) ∣ bZ Q r v - 1) :
    (latRepNum Q (voisLat Q 2 r v) 2 : ℚ) / 24 ≤ (coxeterNumber Q + 1) / 2 := by
  obtain ⟨e, he, hcox, hval⟩ := twoNeighbor_value hC hE hQ hR hρ hv
  obtain ⟨h24, -⟩ := iota_table e he
  have : (24 : ℚ) ≤ 2 * adeIota e.1 := by exact_mod_cast h24
  rw [hval, hcox]
  linarith

/-- **Equality in Proposition 3.4.4.1** (Chenevier–Lannes, p. 82): **conditional** on `CoxeterOfTwoNeighbor` and
`EquiCoxeterRootSystem 24`. $h(\mathrm{vois}_2(L; \rho)) = (h(L) + 1)/2$ if and only if $h(L)$ is odd (equivalently,
by `odd_coxeter_iff_table`, $R(L) \cong (24/d)\mathbf{A}_d$ with $d$ an even divisor of $24$). -/
@[kb "chenevierlannes2019" "§3.4.4, p. 82 (equality in Prop. 3.4.4.1 iff h odd; conditional)"]
theorem twoNeighbor_equality_iff (hC : CoxeterOfTwoNeighbor) (hE : EquiCoxeterRootSystem 24) {Q : QuadForm ℤ 24}
    (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {r v : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv r))
    (hv : (2 : ℤ) ∣ bZ Q r v - 1) :
    ∃ h : ℕ, coxeterNumber Q = h ∧
      ((latRepNum Q (voisLat Q 2 r v) 2 : ℚ) / 24 = (coxeterNumber Q + 1) / 2 ↔ h % 2 = 1) := by
  obtain ⟨e, he, hcox, hval⟩ := twoNeighbor_value hC hE hQ hR hρ hv
  obtain ⟨-, hodd, -⟩ := iota_table e he
  refine ⟨e.2, hcox, ?_⟩
  rw [hval, hcox, ← hodd]
  constructor
  · intro h
    have : (2 * adeIota e.1 : ℚ) = 24 := by linarith
    exact_mod_cast this
  · intro h
    have : (2 * adeIota e.1 : ℚ) = 24 := by exact_mod_cast h
    linarith

end QuadFormsKB.ChenevierLannes
