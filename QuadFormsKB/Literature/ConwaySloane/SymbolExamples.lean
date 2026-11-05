/-
# Conway–Sloane, Ch. 15, §7.5–7.6: the examples (25)–(28) and the canonical symbol of (25)

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.5–7.6, pp. 381–382
(`conwaysloane1999`). The symbols are written with every scale $2^k$ (zero-dimensional constituents included); a
compartment written with only its total oddity (oddity fusion, $[\cdots]_t$) is represented by putting the total on its
first form and $0$ on the others.

**Proves**
* (25): `example25` as printed is not a valid symbol: its constituent $256_7^{-1}$ violates (33) (`not_exists_example25`);
  *Erratum:* read $256_3^{-1}$ (`example25c`); then the canonical symbol printed on p. 382 (`canonical25`) is correct
  (`moveEquiv_example25c_canonical25`), while it is not equivalent to (25) as printed
  (`not_moveEquiv_example25_canonical25`: the compartment invariant of $[256]$ differs);
* (26)–(28): the three-step walk (26) → (27) and the one-step walk (26) → (28) (`moveEquiv_26_27`, `moveEquiv_26_28`).
-/
import QuadFormsKB.Literature.ConwaySloane.Existence

namespace QuadFormsKB.ConwaySloane

/-- **(25) as printed** (p. 381): $1^{+2}[2_6^{-2}4_5^{+3}]8^{+0}[16_1^{+1}]32^{+2}: 64^{-2}: 128^{-4}[256_7^{-1}]512^{+0}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (25), p. 381"]
def example25 : TwoSymbol
  | 0 => ⟨2, .plus, .II, 0⟩
  | 1 => ⟨2, .minus, .I, 6⟩
  | 2 => ⟨3, .plus, .I, 5⟩
  | 3 => ⟨0, .plus, .II, 0⟩
  | 4 => ⟨1, .plus, .I, 1⟩
  | 5 => ⟨2, .plus, .II, 0⟩
  | 6 => ⟨2, .minus, .II, 0⟩
  | 7 => ⟨4, .minus, .II, 0⟩
  | 8 => ⟨1, .minus, .I, 7⟩
  | _ => TwoFactor.trivial

/-- **(25) corrected**: as `example25` with $256_3^{-1}$ in place of $256_7^{-1}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (25), p. 381 (Erratum: 256_3^{-1})"]
def example25c : TwoSymbol := fun k => if k = 8 then ⟨1, .minus, .I, 3⟩ else example25 k

/-- **The canonical symbol of (25)** as printed (p. 382):
$1^{-2}[2^{+2}4^{+3}]_7 8^{+0}[16^{+1}]_1 32^{+2}: 64^{-2}: 128^{+4}[256^{+1}]_7 512^{+0}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
def canonical25 : TwoSymbol
  | 0 => ⟨2, .minus, .II, 0⟩
  | 1 => ⟨2, .plus, .I, 7⟩
  | 2 => ⟨3, .plus, .I, 0⟩
  | 3 => ⟨0, .plus, .II, 0⟩
  | 4 => ⟨1, .plus, .I, 1⟩
  | 5 => ⟨2, .plus, .II, 0⟩
  | 6 => ⟨2, .minus, .II, 0⟩
  | 7 => ⟨4, .plus, .II, 0⟩
  | 8 => ⟨1, .plus, .I, 7⟩
  | _ => TwoFactor.trivial

/-- (25) as printed contains an impossible constituent: $256_7^{-1}$ violates (33) ($\varepsilon = -$ needs
$t \equiv \pm 3$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (25), p. 381 (Erratum)"]
theorem not_exists_example25 : ¬ (example25 8).Exists := by decide

/-- Every constituent of the corrected (25) satisfies (32)–(35). -/
theorem exists_example25c : ∀ k < 10, (example25c k).Exists := by decide

/-- (25) as printed is not move-equivalent to the printed canonical symbol: the compartment $[256]$ has invariant
$7 + 4\cdot 1$ in (25) and $7$ in the canonical symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382 (Erratum)"]
theorem not_moveEquiv_example25_canonical25 : ¬ MoveEquiv example25 canonical25 := by
  intro h
  have hc : IsCompartment example25 8 8 := by
    refine ⟨le_rfl, fun x h1 h2 => ?_, Or.inr ?_, ?_⟩
    · obtain rfl : x = 8 := le_antisymm h2 h1
      decide
    · decide
    · decide
  have := h.sameInvariants.compartment 8 8 hc
  revert this
  decide

theorem twoSymbol_ext_lt {σ τ : TwoSymbol} (B : ℕ) (h : ∀ k < B, σ k = τ k) (h' : ∀ k, B ≤ k → σ k = τ k) : σ = τ :=
  funext fun k => if hk : k < B then h k hk else h' k (by omega)

/-- **The canonical symbol of the corrected (25)** is the one printed on p. 382: one walk step between $1$ and $2$ (the
compartment $[2, 4]$ changes its oddity by $4$), an oddity fusion in that compartment, and one walk step between $128$ and
$256$ (the compartment $[256]$ changes its oddity by $4$: $3 + 4 = 7$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
theorem moveEquiv_example25c_canonical25 : MoveEquiv example25c canonical25 := by
  have s1 := Step.walk example25c 0 1 (Or.inr rfl) (by decide)
  have s2 := Step.walk (walkStep example25c 0 1) 7 8 (Or.inr rfl) (by decide)
  have s3 := Step.fuse (walkStep (walkStep example25c 0 1) 7 8) 1 5 (by decide) (by decide)
  have e : fuseStep (walkStep (walkStep example25c 0 1) 7 8) 1 5 = canonical25 := by
    refine twoSymbol_ext_lt 10 (by decide) fun k hk => ?_
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 10 := ⟨k - 10, by omega⟩
    simp [fuseStep, walkStep, example25c, example25, canonical25, TwoFactor.trivial, Sign.flip]
  rw [← e]
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s1)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s2) (Relation.EqvGen.rel _ _ s3))

/-- **(26)** (p. 382): $1^2[2^{-2}4^3]_3 8^0[16^1]_1 32^2$ (the compartment total on its first form). -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (26), p. 382"]
def example26 : TwoSymbol
  | 0 => ⟨2, .plus, .II, 0⟩
  | 1 => ⟨2, .minus, .I, 3⟩
  | 2 => ⟨3, .plus, .I, 0⟩
  | 3 => ⟨0, .plus, .II, 0⟩
  | 4 => ⟨1, .plus, .I, 1⟩
  | 5 => ⟨2, .plus, .II, 0⟩
  | _ => TwoFactor.trivial

/-- **(27)** (p. 382): $1^2[2^2 4^3]_3 8^0[16^{-1}]_5 32^2$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (27), p. 382"]
def example27 : TwoSymbol
  | 0 => ⟨2, .plus, .II, 0⟩
  | 1 => ⟨2, .plus, .I, 3⟩
  | 2 => ⟨3, .plus, .I, 0⟩
  | 3 => ⟨0, .plus, .II, 0⟩
  | 4 => ⟨1, .minus, .I, 5⟩
  | 5 => ⟨2, .plus, .II, 0⟩
  | _ => TwoFactor.trivial

/-- **(28)** (p. 382): $1^2[2^2 4^{-3}]_7 8^0[16^1]_1 32^2$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (28), p. 382"]
def example28 : TwoSymbol
  | 0 => ⟨2, .plus, .II, 0⟩
  | 1 => ⟨2, .plus, .I, 7⟩
  | 2 => ⟨3, .minus, .I, 0⟩
  | 3 => ⟨0, .plus, .II, 0⟩
  | 4 => ⟨1, .plus, .I, 1⟩
  | 5 => ⟨2, .plus, .II, 0⟩
  | _ => TwoFactor.trivial

/-- **The three-step walk (26) → (27)** (p. 382): steps $2 \to 4$, $4 \to 8$ (both in the compartment $[2,4]$, total
oddity unchanged) and $8 \to 16$ (the compartment $[16]$, oddity $1 + 4 = 5$), and an oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (26)–(27), p. 382"]
theorem moveEquiv_26_27 : MoveEquiv example26 example27 := by
  have s1 := Step.walk example26 1 1 (Or.inl rfl) (by decide)
  have s2 := Step.walk (walkStep example26 1 1) 2 2 (Or.inl rfl) (by decide)
  have s3 := Step.walk (walkStep (walkStep example26 1 1) 2 2) 3 4 (Or.inr rfl) (by decide)
  have s4 := Step.fuse (walkStep (walkStep (walkStep example26 1 1) 2 2) 3 4) 1 4 (by decide) (by decide)
  have e : fuseStep (walkStep (walkStep (walkStep example26 1 1) 2 2) 3 4) 1 4 = example27 := by
    refine twoSymbol_ext_lt 10 (by decide) fun k hk => ?_
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 10 := ⟨k - 10, by omega⟩
    simp [fuseStep, walkStep, example26, example27, TwoFactor.trivial, Sign.flip]
  rw [← e]
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s1)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s2)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s3) (Relation.EqvGen.rel _ _ s4)))

/-- **The one-step walk (26) → (28)** (p. 382): the step $2 \to 4$ changes the total oddity of $[2,4]$ by $4$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, (26), (28), p. 382"]
theorem moveEquiv_26_28 : MoveEquiv example26 example28 := by
  have s1 := Step.walk example26 1 1 (Or.inl rfl) (by decide)
  have e : walkStep example26 1 1 = example28 := by
    refine twoSymbol_ext_lt 10 (by decide) fun k hk => ?_
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 10 := ⟨k - 10, by omega⟩
    simp [walkStep, example26, example28, TwoFactor.trivial, Sign.flip]
  rw [← e]
  exact Relation.EqvGen.rel _ _ s1

end QuadFormsKB.ConwaySloane
