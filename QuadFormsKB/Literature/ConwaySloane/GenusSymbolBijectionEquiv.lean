/-
# Conway–Sloane, Ch. 15, §7.7–7.8 made explicit: genera ≃ genus symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7–7.8, pp. 382–384
(`conwaysloane1999`).

**The bijection.** The genus symbol is a bijection
$$\{\text{genera of nondegenerate integral forms in } n \text{ variables}\} \xrightarrow{\ \sim\ }
\{\text{systems of symbols of dimension } n \text{ satisfying (29)–(35)}\}/\text{(same genus symbol)}.$$
It is well defined and injective by `sameGenus_iff_sameSymbol`, lands in the systems satisfying (29)–(35) by
`IsGenusSymbolOf.conditions` (with the oddity formula (30) for every form, `IsGenusSymbolOf.oddity_formula`), and is
surjective by Theorem 11 (`theorem11`). The book uses this correspondence in §7.8 (p. 384), naming genera by their
symbols, without stating it.

**Conventions.** A nondegenerate classically integral form in $n$ variables is a symmetric $A \in M_n(\mathbb Z)$ with
$\det A \ne 0$ (`NondegSymm n`), its form $x^{\mathsf T}Ax$ (`LocalDensity.ofMatrixZ`); genera are the classes of
`Siegel.SameGenus` (`Genera n`). A system of symbols of dimension $n$ is a `GenusSymbolData` with `G.n = n` satisfying
`Conditions` (`SymbolSystem n`), up to `SameSymbol` (`GenusSymbols n`); the support bound is not part of the symbol.
-/
import QuadFormsKB.Literature.ConwaySloane.GenusSymbolBijectionOddity

namespace QuadFormsKB.ConwaySloane

open Matrix Siegel GenusSymbolData

variable {n : ℕ}

/-- The nondegenerate symmetric integral matrices $A \in M_n(\mathbb Z)$ (Gram matrices of nondegenerate classically
integral forms in $n$ variables). -/
def NondegSymm (n : ℕ) : Type := {A : Matrix (Fin n) (Fin n) ℤ // Aᵀ = A ∧ A.det ≠ 0}

/-- Same genus (`Siegel.SameGenus` of the forms $x^{\mathsf T}Ax$) as a setoid. -/
def genusSetoid (n : ℕ) : Setoid (NondegSymm n) where
  r A B := SameGenus (LocalDensity.ofMatrixZ A.1) (LocalDensity.ofMatrixZ B.1)
  iseqv := ⟨fun A => SameGenus.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The genera** of nondegenerate classically integral forms in $n$ variables. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128"]
def Genera (n : ℕ) : Type := Quotient (genusSetoid n)

/-- The systems of symbols of dimension $n$ satisfying the conditions (29)–(35) of §7.7. -/
def SymbolSystem (n : ℕ) : Type := {G : GenusSymbolData // G.n = n ∧ G.Conditions}

/-- `SameSymbol` on the systems of dimension $n$. -/
def symbolSetoid (n : ℕ) : Setoid (SymbolSystem n) where
  r G H := G.1.SameSymbol H.1
  iseqv := ⟨fun G => SameSymbol.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The genus symbols** of dimension $n$ (Conway–Sloane, §7.8, p. 384): systems of symbols satisfying (29)–(35), up
to the same genus symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7–7.8, pp. 382–384"]
def GenusSymbols (n : ℕ) : Type := Quotient (symbolSetoid n)

/-- Every nondegenerate form has a system of symbols satisfying (29)–(35). -/
theorem exists_isGenusSymbolOf_conditions (A : NondegSymm n) :
    ∃ G : GenusSymbolData, G.IsGenusSymbolOf A.1 ∧ G.Conditions := by
  obtain ⟨G, hG, hodd, htwo⟩ := exists_isGenusSymbolOf_supported A.1 A.2.1 A.2.2
  exact ⟨G, hG, hG.conditions hodd htwo⟩

/-- A chosen system of symbols of $A$ (any two are the same genus symbol, `sameGenus_iff_sameSymbol`). -/
noncomputable def symbolOf (A : NondegSymm n) : SymbolSystem n :=
  ⟨(exists_isGenusSymbolOf_conditions A).choose,
    (exists_isGenusSymbolOf_conditions A).choose_spec.1.fst,
    (exists_isGenusSymbolOf_conditions A).choose_spec.2⟩

theorem symbolOf_spec (A : NondegSymm n) : (symbolOf A).1.IsGenusSymbolOf A.1 :=
  (exists_isGenusSymbolOf_conditions A).choose_spec.1

/-- **Genera ≃ genus symbols** (Conway–Sloane, Ch. 15, §7.7–7.8, pp. 382–384, made explicit): the genus symbol is a
bijection from the genera of nondegenerate classically integral forms in $n$ variables onto the systems of symbols of
dimension $n$ satisfying (29)–(35), up to the same genus symbol. Injective by Theorems 9, 10 and §7.6
(`sameGenus_iff_sameSymbol`), onto the systems satisfying (29)–(35) by the necessity of the conditions
(`IsGenusSymbolOf.conditions`, including the oddity formula (30)) and Theorem 11 (`theorem11`). Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7–7.8, Thms. 9–11, pp. 379–384, made explicit"]
noncomputable def genusSymbolEquiv (n : ℕ) : Genera n ≃ GenusSymbols n :=
  Equiv.ofBijective
    (Quotient.map (sa := genusSetoid n) (sb := symbolSetoid n) symbolOf fun A B h =>
      (sameGenus_iff_sameSymbol (symbolOf_spec A) (symbolOf_spec B)).1 h)
    ⟨by
      rintro ⟨A⟩ ⟨B⟩ h
      exact Quotient.sound ((sameGenus_iff_sameSymbol (symbolOf_spec A) (symbolOf_spec B)).2 (Quotient.exact h)),
    by
      rintro ⟨G, hGn, hG⟩
      obtain ⟨A', hA'⟩ := theorem11 G hG
      set A : Matrix (Fin n) (Fin n) ℤ := A'.submatrix (Fin.cast hGn.symm) (Fin.cast hGn.symm) with hAdef
      have hGA : G.IsGenusSymbolOf A := by
        refine ⟨hGn, ?_, hG.real_dim⟩
        convert hA' using 1
        ext i j; simp [hAdef]
      obtain ⟨-, -, hAs, hAd, -, -, -⟩ := (G.isGenusSymbolOf_iff A).1 hGA
      refine ⟨Quotient.mk _ ⟨A, hAs, hAd ▸ hG.ne_zero⟩, Quotient.sound ?_⟩
      exact (sameGenus_iff_sameSymbol (symbolOf_spec ⟨A, hAs, hAd ▸ hG.ne_zero⟩) hGA).1 (SameGenus.refl _)⟩

/-- The bijection sends the genus of $A$ to the class of any system of symbols of $A$. -/
theorem genusSymbolEquiv_mk (A : NondegSymm n) (G : SymbolSystem n) (hG : G.1.IsGenusSymbolOf A.1) :
    genusSymbolEquiv n (Quotient.mk _ A) = Quotient.mk _ G :=
  Quotient.sound ((sameGenus_iff_sameSymbol (symbolOf_spec A) hG).1 (SameGenus.refl _))

end QuadFormsKB.ConwaySloane
