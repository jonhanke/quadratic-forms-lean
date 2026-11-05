/-
# Conway–Sloane, Ch. 15, §7.3–7.4: the 2-adic symbol of a form

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.3–7.4, p. 380
(`conwaysloane1999`).

A 2-adic Jordan decomposition is taken in the shape of Theorem 2 (§4.4, pp. 369–370), as normalized by Cassels
(Ch. 8, Lemma 4.1): an orthogonal sum of blocks $2^e u x^2$ ($u \in \{1, 3, 5, 7\}$), $2^e\cdot 2xy$ and
$2^e(2x^2 + 2xy + 2y^2)$ (`Cassels.DyBlock`). The Jordan constituent $qf_q$, $q = 2^k$, is the sum of the blocks with
$e = k$; its invariants (§7.3) are read off the blocks:
* $n_q$: the number of variables;
* type I iff there is a block $2^k u x^2$ (an odd diagonal entry of $f_q$); otherwise type II;
* $\varepsilon_q = \left(\frac{\det f_q}{2}\right)$: the product of $\left(\frac{u}{2}\right)$ over the blocks
  $2^k u x^2$, of $\left(\frac{-1}{2}\right) = +1$ over the blocks $2^k\cdot 2xy$, and of $\left(\frac{3}{2}\right) = -1$ over
  the blocks $2^k(2x^2+2xy+2y^2)$;
* $t_q$: the sum of the $u$ (the trace of the diagonalized $f_q$), modulo 8; $0$ for type II.

**Defines** `blockSymbol` (the 2-adic symbol of a block decomposition), `IsTwoSymbolOf` (a 2-adic symbol of a form,
from some block decomposition of an integral form).
-/
import QuadFormsKB.Literature.ConwaySloane.Existence
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic

namespace QuadFormsKB.ConwaySloane

open Cassels

/-- The exponent $e$ of a block $2^e(\cdots)$. -/
def blockExp : DyBlock → ℤ
  | .sq e _ => e
  | .hyp e => e
  | .ell e => e

/-- The sign $\left(\frac{\det}{2}\right)$ of a block: $\left(\frac{u}{2}\right)$ for $u x^2$, $+$ for $2xy$
($\det = -1$), $-$ for $2x^2 + 2xy + 2y^2$ ($\det = 3$). -/
def blockSign : DyBlock → Sign
  | .sq _ u => jacobiTwo u
  | .hyp _ => .plus
  | .ell _ => .minus

/-- The oddity contribution of a block: $u$ for $u x^2$, $0$ for the binary blocks. -/
def blockOddity : DyBlock → ZMod 8
  | .sq _ u => (u : ZMod 8)
  | _ => 0

/-- The block is of the shape $2^e u x^2$. -/
def IsSqBlock : DyBlock → Prop
  | .sq .. => True
  | _ => False

instance (b : DyBlock) : Decidable (IsSqBlock b) := by cases b <;> unfold IsSqBlock <;> infer_instance

/-- The product of a list of signs. -/
def Sign.prodList : List Sign → Sign
  | [] => .plus
  | s :: l => s.mul (Sign.prodList l)

/-- **The 2-adic symbol of a block decomposition** (Conway–Sloane, §7.3–7.4, p. 380): the constituent of scale $2^k$
collects the blocks with exponent $k$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.3–7.4, p. 380"]
def blockSymbol (D : List DyBlock) : TwoSymbol := fun k =>
  let B := D.filter fun b => blockExp b = k
  { dim := (B.map DyBlock.dim).sum
    sign := Sign.prodList (B.map blockSign)
    type := if B.any fun b => decide (IsSqBlock b) then .I else .II
    oddity := (B.map blockOddity).sum }

/-- **A 2-adic symbol of an integral form** (Conway–Sloane, §7.4, p. 380: "the 2-adic symbol representing a given
Jordan decomposition"): the form with symmetric matrix $F$ over $\mathbb Q_2$ is $\mathbb Z_2$-equivalent to an
orthogonal sum of blocks of nonnegative exponents (a Jordan decomposition in the shape of Theorem 2), and $\sigma$ is the
symbol of that decomposition. A form has in general several 2-adic symbols (§7.5). -/
@[kb "conwaysloane1999" "Ch. 15, §7.4, p. 380"]
def IsTwoSymbolOf {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ_[2]) (σ : TwoSymbol) : Prop :=
  ∃ D : List DyBlock, (∀ b ∈ D, b.Valid) ∧ (∀ b ∈ D, 0 ≤ blockExp b) ∧ ∃ h : dyDim D = n,
    ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) ∧ σ = blockSymbol D

end QuadFormsKB.ConwaySloane
