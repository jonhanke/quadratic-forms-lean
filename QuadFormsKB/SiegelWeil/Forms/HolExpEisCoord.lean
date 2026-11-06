/-
# Complex coordinates for the holomorphic Eisenstein series

**Layer:** archimedean, over a totally real number field $F$ of degree $d$.

**Setting.** (The coordinates `zC`, `zC_cplx`, `zC_add_int` are defined in `HolExpCoord.lean`.) $b = (b_j)_{j<d}$ = `oBasis F` (the real embeddings of a $\mathbb Z$-basis of $\mathcal O_F$), $J = \{(p, j)\}$ (`JR F r`) with $p = (i \le i')$.
A complex vector $t \in \mathbb C^J$ gives the point $Z(t) = (Z_w(t))_w$, $(Z_w(t))_{ii'} = \sum_jt_{p,j}(b_j)_w$ (`zC`); for $t = x + iy$ this is
$X(x) + iX(y)$ (`zC_cplx`), so the tube $\{x + iy : y \in K\}$ over the open convex cone $K = \{y : X_w(y) \succ 0\ \forall w\}$ (`coneK`) is
$\mathbb H_r^d$ in these coordinates. `fC` is $\mathcal E^{(r)}\circ Z$ on the tube (and $0$ off it); it is $\mathbb Z^J$-periodic (`fC_add_int`),
because $Z(t + n) = Z(t) + \sigma(\lambda_n)$ with $\lambda_n \in \mathrm{Sym}_r(\mathcal O_F)$ (`zC_add_int`).

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinHolBound
import QuadFormsKB.SiegelWeil.Forms.HolExpTorus
import QuadFormsKB.SiegelWeil.Forms.HolExpCoord

open Matrix NumberField
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.SiegelWeil.Forms.HolExp

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

variable (F r) in
/-- **The cone of imaginary parts**: $K = \{y \in \mathbb R^J : X_w(y) \text{ positive definite at every real place } w\}$. -/
def coneK : Set (JR F r → ℝ) := {y | ∀ w, (xMat y w).PosDef}

open Classical in
/-- $\mathcal E^{(r)}(Z(t))$ on the tube $Z(t) \in \mathbb H_r^d$, and $0$ off it. -/
def fC (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (t : JR F r → ℂ) : ℂ :=
  if zC t ∈ siegelHF F r then eisHolR b hb hbpos (zC t) else 0

lemma xCoord_eq_sum (t : JR F r → ℝ) (p : SymIdx r) (w : InfinitePlace F) :
    xCoord t p w = ∑ j, t (p, j) * (oBasis F) j w := by
  unfold xCoord
  rw [Module.Basis.equivFun_symm_apply]
  simp [Finset.sum_apply]

lemma zC_mem (x : JR F r → ℝ) {y : JR F r → ℝ} (hy : y ∈ coneK F r) : zC (cplx x y) ∈ siegelHF F r := by
  rw [zC_cplx]; exact zPt_mem_siegelHF _ hy x

lemma fC_cplx (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (x : JR F r → ℝ) {y : JR F r → ℝ} (hy : y ∈ coneK F r) :
    fC b hb hbpos (cplx x y) = eisHolR b hb hbpos (zPt (fun w => xMat y w) x) := by
  unfold fC
  rw [if_pos (zC_mem x hy), zC_cplx]

lemma xMat_zero' (w : InfinitePlace F) : xMat (0 : JR F r → ℝ) w = 0 := by
  ext i k
  simp only [xMat, symOf, of_apply, xCoord_eq_sum, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Matrix.zero_apply]
  split_ifs <;> rfl

lemma addB_mem_iff {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    addB B Z ∈ siegelHF F r ↔ Z ∈ siegelHF F r := by
  refine ⟨fun h => ?_, fun h => addB_mem hB h⟩
  have hB' : (-B)ᵀ = -B := by rw [transpose_neg, hB]
  have := addB_mem hB' h
  have e : addB (-B) (addB B Z) = Z := by
    funext w; simp only [addB]; ext i j; simp
  rwa [e] at this

/-- **$\mathbb Z^J$-periodicity** of `fC`. -/
lemma fC_add_int (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (t : JR F r → ℂ) (n : JR F r → ℤ) : fC b hb hbpos (t + fun q => (n q : ℂ)) = fC b hb hbpos t := by
  have hL : (symOf (symOEquiv n : SymIdx r → F))ᵀ = symOf (symOEquiv n : SymIdx r → F) := symOf_transpose _
  have hLi := isIntMat_symOf (symOEquiv n).2
  unfold fC
  rw [zC_add_int, addB_mem_iff hL]
  split_ifs with h
  · exact eisHolR_addB b hb hbpos hL hLi h
  · rfl

end QuadFormsKB.SiegelWeil.Forms
