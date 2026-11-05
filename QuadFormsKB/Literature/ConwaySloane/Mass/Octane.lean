/-
# Conway–Sloane 1988, §5 and §13: the octane value of a diagonal constituent

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §5, p. 265 and §13, p. 284 (bibliography key `conwaysloane1988`).

The paper defines the octane value of a type I constituent through a diagonalization $\mathrm{diag}(a_1, a_2, \ldots)$
with odd 2-adic integers $a_i$: "the number of $a_i$ that are congruent to $1 \pmod 4$ minus the number of $a_i$ that
are congruent to $-1 \pmod 4$", and remarks that this is the oddity if the sign is $+$, the oddity $+4$ if the sign is
$-$ (p. 265). `octane` (`PMass.lean`) is defined by the remark; `octane_diag` proves the definition: for a constituent
$\langle u_1\rangle \perp \cdots \perp \langle u_m\rangle$ of scale $2^k$ in a Cassels block decomposition
($u_i \in \{1,3,5,7\}$, the shape of *Sphere Packings, Lattices and Groups* Ch. 15, Thm. 2), the octane value of its symbol is
$\#\{u_i \equiv 1\} - \#\{u_i \equiv 3 \pmod 4\}$. `octane_typeII` is the type II case (§5, p. 265; §13, p. 284: "for a
type II summand the octane value is already determined by $\epsilon_q$").
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass
import QuadFormsKB.Literature.ConwaySloane.TwoAdicForm

namespace QuadFormsKB.ConwaySloane.Mass

open Cassels

/-- The octane value read from a diagonalization: $\#\{u \equiv 1 \pmod 4\} - \#\{u \equiv -1 \pmod 4\}$. -/
def diagOctane (L : List ℤ) : ZMod 8 := (L.map fun u => if u % 4 = 1 then (1 : ZMod 8) else -1).sum

/-- **Octane value of a type II constituent** (Conway–Sloane 1988, §5, p. 265; §13, p. 284): $0$ or $4$ according as
the sign is $+$ ($\det \equiv \pm1 \pmod 8$) or $-$ ($\det \equiv \pm3$). -/
@[kb "conwaysloane1988" "§5, p. 265 (type II); §13, p. 284"]
theorem octane_typeII (f : TwoFactor) (h : f.oddity = 0) :
    octane f = if f.sign = .minus then 4 else 0 := by
  simp [octane, h]

theorem ind_mul (s t : Sign) :
    (if s.mul t = .minus then (4 : ZMod 8) else 0) =
      (if s = .minus then 4 else 0) + (if t = .minus then 4 else 0) := by
  cases s <;> cases t <;> decide

theorem blockSymbol_of_exp {k : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, blockExp b = k) :
    octane (blockSymbol D k) = (D.map blockOddity).sum +
      (if Sign.prodList (D.map blockSign) = .minus then 4 else 0) := by
  have hf : D.filter (fun b => decide (blockExp b = (k : ℤ))) = D := List.filter_eq_self.mpr (by simpa using hD)
  unfold blockSymbol octane
  simp only [hf]

theorem octane_contrib (k : ℤ) (u : ℤ) (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    blockOddity (DyBlock.sq k u) + (if blockSign (DyBlock.sq k u) = .minus then (4 : ZMod 8) else 0) =
      if u % 4 = 1 then 1 else -1 := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [blockOddity, blockSign, jacobiTwo] <;> norm_num <;> rfl

/-- **The octane value of a diagonal constituent** (Conway–Sloane 1988, §5, p. 265): for the constituent
$2^k(\langle u_1\rangle \perp \cdots \perp \langle u_m\rangle)$, $u_i \in \{1, 3, 5, 7\}$, of a block decomposition, the
octane value of its symbol (oddity $+4$ if the sign is $-$) is $\#\{u_i \equiv 1\} - \#\{u_i \equiv -1 \pmod 4\}$. -/
@[kb "conwaysloane1988" "§5, p. 265 (octane value of a diagonal constituent)"]
theorem octane_diag (k : ℕ) (L : List ℤ) (hL : ∀ u ∈ L, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    octane (blockSymbol (L.map fun u => DyBlock.sq k u) k) = diagOctane L := by
  rw [blockSymbol_of_exp (by intro b hb; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hb; rfl)]
  induction L with
  | nil => simp [diagOctane, Sign.prodList]
  | cons u L ih =>
    have hu := hL u (List.mem_cons_self ..)
    have ih := ih (fun v hv => hL v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, Sign.prodList, ind_mul, diagOctane] at ih ⊢
    rw [← ih]
    rw [← octane_contrib k u hu]
    ring

end QuadFormsKB.ConwaySloane.Mass
