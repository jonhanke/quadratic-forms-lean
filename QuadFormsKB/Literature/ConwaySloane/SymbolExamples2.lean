/-
# Conway–Sloane, Ch. 15, §7.5: one form, two different 2-adic symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.5, p. 381
(`conwaysloane1999`): "a form may have several essentially different Jordan decompositions, and so can have several
different 2-adic symbols".

**Example.** $f = x^2 + 2y^2$: the vectors $(1,1)$ and $(-2,1)$ have norms $3$ and $6$, are orthogonal, and span
$\mathbb Z_2^2$ (the change of basis has determinant $3$, a 2-adic unit). So $\langle 1\rangle \perp 2\langle 1\rangle
\cong \langle 3\rangle \perp 2\langle 3\rangle$ over $\mathbb Z_2$, and $f$ has the two 2-adic symbols $1_1^{+1}2_1^{+1}$
and $1_3^{-1}2_3^{-1}$ (they differ by one walk step, which changes the compartment total by $4$).

**Proves** `twoSymbols_differ` (`IsTwoSymbolOf` for both symbols, and they are different).
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Literature.ConwaySloane.SymbolExamples

namespace QuadFormsKB.ConwaySloane

open Cassels Matrix

/-- The blocks $\langle u\rangle \perp 2\langle u\rangle$. -/
def blocksU (u : ℤ) : List DyBlock := [.sq 0 u, .sq 1 u]

theorem dyMatInt_blocksU (u : ℤ) : dyMatInt (blocksU u) = !![u, 0; 0, 2 * u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blocksU, dyMatInt, blockMatInt, orthSumMat, Matrix.reindex_apply, Matrix.fromBlocks,
      finSumFinEquiv, Fin.addCases, Fin.castLT, Fin.subNat] <;> rfl

/-- $\langle u\rangle \perp 2\langle u\rangle$ has the 2-adic symbol of its block decomposition. -/
theorem isTwoSymbolOf_blocksU {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    IsTwoSymbolOf ((!![u, 0; 0, 2 * u] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ_[2])) (blockSymbol (blocksU u)) := by
  refine ⟨blocksU u, ?_, ?_, rfl, ?_, rfl⟩
  · intro b hb
    simp only [blocksU, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact hu
  · intro b hb
    simp only [blocksU, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [blockExp]
  · rw [← map_dyMatInt _ (fun b hb => by
      simp only [blocksU, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [blockExp]), dyMatInt_blocksU]
    convert ZpEquiv.refl _ using 2
    ext i j; rfl

/-- **One form, two 2-adic symbols** (Conway–Sloane, §7.5, p. 381): $x^2 + 2y^2$ is $\mathbb Z_2$-equivalent to
$3x^2 + 6y^2$, so it has the two different 2-adic symbols $1_1^{+1}2_1^{+1}$ and $1_3^{-1}2_3^{-1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381 (several 2-adic symbols)"]
theorem twoSymbols_differ :
    IsTwoSymbolOf ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ_[2])) (blockSymbol (blocksU 1)) ∧
    IsTwoSymbolOf ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ_[2])) (blockSymbol (blocksU 3)) ∧
    blockSymbol (blocksU 1) ≠ blockSymbol (blocksU 3) := by
  refine ⟨by simpa using isTwoSymbolOf_blocksU (u := 1) (Or.inl rfl), ?_, ?_⟩
  · -- the change of basis $(1,1), (-2,1)$, determinant $3$
    obtain ⟨D, hDv, hDe, hdim, hZ, hσ⟩ := isTwoSymbolOf_blocksU (u := 3) (Or.inr (Or.inl rfl))
    refine ⟨D, hDv, hDe, hdim, ZpEquiv.trans ?_ hZ, hσ⟩
    set P : Matrix (Fin 2) (Fin 2) ℤ := !![1, -2; 1, 1] with hP
    have key : Pᵀ * !![1, 0; 0, 2] * P = !![3, 0; 0, 2 * 3] := by rw [hP]; decide
    have hdet : IsUnit (P.map (Int.castRingHom ℤ_[2])).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have : P.det = 3 := by rw [hP]; decide
      rw [this]
      exact Binary.isUnit_intCast_padic (p := 2) (by decide)
    refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩
    have e : (P.map (Int.castRingHom ℤ_[2])).map PadicInt.Coe.ringHom = P.map (Int.castRingHom ℚ_[2]) := by
      rw [Matrix.map_map]; congr 1
    show ((P.map (Int.castRingHom ℤ_[2])).map PadicInt.Coe.ringHom)ᵀ * _ *
      (P.map (Int.castRingHom ℤ_[2])).map PadicInt.Coe.ringHom = _
    rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, key]
  · intro h
    have := congrArg (fun σ => (σ 0).sign) h
    revert this
    decide

/-! ### §7.7: the compartment remark holds only up to sign walking -/

/-- **The compartment remark of §7.7 needs sign walking** (Conway–Sloane, §7.7, p. 384, "the only existence condition on
a compartment of two or more constituents is that its total oddity has the parity of its total dimension"): the
compartment $[1^{+1}2^{+1}]_4$ satisfies the parity condition, but no oddities allowed by (33) for two
one-dimensional constituents of sign $+$ add up to $4$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 384 (Clarification: only up to sign walking)"]
theorem compartment_remark_counterexample :
    ∀ t₁ t₂ : ZMod 8, (TwoFactor.mk 1 .plus .I t₁).Exists → (TwoFactor.mk 1 .plus .I t₂).Exists → t₁ + t₂ ≠ 4 := by
  decide

/-- The compartment $[1^{+1}2^{+1}]_4$ (oddity on the first form). -/
def compartment11 : TwoSymbol
  | 0 => ⟨1, .plus, .I, 4⟩
  | 1 => ⟨1, .plus, .I, 0⟩
  | _ => TwoFactor.trivial

/-- After one walk step it becomes $[1^{-1}2^{-1}]_0$, realized by $\langle 3\rangle \perp 2\langle 5\rangle$. -/
def compartment11' : TwoSymbol
  | 0 => ⟨1, .minus, .I, 3⟩
  | 1 => ⟨1, .minus, .I, 5⟩
  | _ => TwoFactor.trivial

@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 384 (Clarification: only up to sign walking)"]
theorem compartment11_walk : MoveEquiv compartment11 compartment11' ∧ (∀ k, (compartment11' k).Exists) := by
  refine ⟨?_, fun k => ?_⟩
  · have s1 := Step.walk compartment11 0 0 (Or.inl rfl) (by decide)
    have s2 := Step.fuse (walkStep compartment11 0 0) 0 3 (by decide) (by decide)
    have e : fuseStep (walkStep compartment11 0 0) 0 3 = compartment11' := by
      refine twoSymbol_ext_lt 3 (by decide) fun k hk => ?_
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      simp [fuseStep, walkStep, compartment11, compartment11', TwoFactor.trivial, Sign.flip]
    rw [← e]
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s1) (Relation.EqvGen.rel _ _ s2)
  · rcases k with _ | _ | k
    · decide
    · decide
    · simp only [compartment11']; decide

end QuadFormsKB.ConwaySloane
