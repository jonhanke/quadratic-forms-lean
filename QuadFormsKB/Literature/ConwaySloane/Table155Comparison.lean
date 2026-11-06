import QuadFormsKB.Literature.ConwaySloane.SmallDetTables7
import QuadFormsKB.Literature.ConwaySloane.Tables8TwoElementary

/-!
# Table 15.5 of Conway–Sloane, Chapter 15, proved twice: comparison

Two machines proved the existence half of Table 15.5 (§8.2), with different statements:

* `SmallDetTables7` (`table155_I_2I`, `table155_I_2II`, `table155_II_2I`, `table155_II_2II_plus`,
  `table155_II_2II_minus`): existence of a system of symbols of determinant $\pm 2^k$ with the stated shape, the
  conditions written with `ZMod 8` representatives;
* `Tables8TwoElementary` (`table155_I_I`, …, `table155_II_II_minus`): existence of a *2-elementary genus*
  (`TwoElemGenus`, which also fixes trivial odd-prime symbols and the dimension of the scale-1 constituent), the
  conditions written with integer residues; and in addition the uniqueness theorem `table155_unique`.

Both are kept. This file proves that the two existence statements are equivalent, row by row, so the stronger
(`TwoElemGenus`, with uniqueness) version is the reference and the older one is a corollary of it, and conversely.
-/

namespace QuadFormsKB.ConwaySloane

/-- Row $\mathrm I(2_{\mathrm I}^k)$: the two versions of Table 15.5 agree. -/
theorem table155_I_2I_iff (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .I ∧ (G.two 1).dim = k ∧ (G.two 1).type = .I ∧ True)) ↔
      (∃ G : GenusSymbolData, TwoElemGenus G r s k .I .I) := by
  rw [table155_I_2I r s k hk, table155_I_I r s k hk]
  have hp := val_sub_mod_two r s
  constructor <;> intro h <;> omega

/-- Row $\mathrm I(2_{\mathrm{II}}^k)$: the two versions of Table 15.5 agree. -/
theorem table155_I_2II_iff (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .I ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ True)) ↔
      (∃ G : GenusSymbolData, TwoElemGenus G r s k .I .II) := by
  rw [table155_I_2II r s k hk, table155_I_II r s k hk]
  have hp := val_sub_mod_two r s
  have hd := twoElem_dmod r s
  simp only [Nat.even_iff]
  constructor <;> intro h <;> omega

/-- Row $\mathrm{II}(2_{\mathrm I}^k)$: the two versions of Table 15.5 agree. -/
theorem table155_II_2I_iff (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .I ∧ True)) ↔
      (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .I) := by
  rw [table155_II_2I r s k hk, table155_II_I r s k hk]
  have hp := val_sub_mod_two r s
  have hd := twoElem_dmod r s
  constructor <;> intro h <;> omega

/-- Row $\mathrm{II}(2_{\mathrm{II}}^{k,+})$: the two versions of Table 15.5 agree. -/
theorem table155_II_2II_plus_iff (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ (G.two 1).sign = .plus)) ↔
      (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .II ∧ (G.two 1).sign = .plus) := by
  rw [table155_II_2II_plus r s k hk, table155_II_II_plus r s k hk]
  have hd := twoElem_dmod r s
  simp only [Nat.even_iff]
  constructor <;> intro h <;> omega

/-- Row $\mathrm{II}(2_{\mathrm{II}}^{k,-})$: the two versions of Table 15.5 agree. -/
theorem table155_II_2II_minus_iff (r s k : ℕ) (hk : 1 ≤ k) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 2 ^ k ∧
        (∀ j, 2 ≤ j → (G.two j).dim = 0) ∧
        ((G.two 0).type = .II ∧ (G.two 1).dim = k ∧ (G.two 1).type = .II ∧ (G.two 1).sign = .minus)) ↔
      (∃ G : GenusSymbolData, TwoElemGenus G r s k .II .II ∧ (G.two 1).sign = .minus) := by
  rw [table155_II_2II_minus r s k hk, table155_II_II_minus r s k hk]
  have hd := twoElem_dmod r s
  simp only [Nat.even_iff]
  constructor <;> intro h <;> omega

end QuadFormsKB.ConwaySloane
