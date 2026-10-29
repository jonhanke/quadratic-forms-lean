/-
# The presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$, for every infinite field

**Layer:** pure algebra over a field $k$.

**Result** (`siegelPresentation`). For every genus $g$ and every **infinite** field $k$ (for instance a number field or
one of its completions), the named input `SiegelPresentation g k` holds: if maps $N$ (on symmetric matrices), $A$ (on
$\mathrm{GL}_g(k)$) and an element $W$ of a monoid $M$ satisfy the relations `SiegelRelations`
(the parabolic relations, $W A(a) = A({}^ta^{-1})W$, $W^2 = A(-1)$ and
$W N(B) W = N(-B^{-1})A(-B^{-1})WN(-B^{-1})$ for invertible symmetric $B$), then there is a monoid homomorphism
$\rho : \mathrm{Sp}_{2g}(k) \to M$ with $\rho(n(B)) = N(B)$, $\rho(m(a)) = A(a)$, $\rho(w) = W$.

**Method** (no Bruhat decomposition). All generators are units of $M$ (`unitsN`, `unitsA`, `unitsW`). On the big cell
$\Omega = \{\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} : \det c \ne 0\}$ put
$\rho_\Omega(\gamma) = N(ac^{-1})A(-{}^tc^{-1})WN(c^{-1}d)$ (`rhoCell`); it is multiplicative whenever $x, y, xy \in \Omega$
(`rhoCell_mul`, where the relation for $WN(B)W$ is used exactly once). Over an infinite field $\Omega$ is generic: for
finitely many $h_i$ there is $z = n(T)w \in \Omega$ with all $h_iz \in \Omega$ (`exists_spN_spW_generic`). Hence $\rho_\Omega$
extends to a homomorphism (`exists_monoidHom_of_generic`), and its values on the generators follow from
$n(B) = (n(B)w)w^{-1}$, $m(a) = (m(a)w)w^{-1}$.

Sources: Weil, Acta Math. 111 (1964), §§1–2 [unverified]; Kudla, *Notes on the local theta correspondence* (1996),
§I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.ExtendHom
import QuadFormsKB.Weil.Genus.SiegelCell
import QuadFormsKB.Weil.Genus.SiegelGeneric

open Matrix

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u v

variable {g : ℕ} {k : Type v} [Field k]

section Units

variable {M : Type u} [Monoid M] {N : Matrix (Fin g) (Fin g) k → M} {A : GL (Fin g) k → M} {W : M}

open Classical in
/-- $N(B)$ as a unit of $M$ (inverse $N(-B)$) for symmetric $B$; $1$ otherwise (a junk value). -/
def unitsN (hR : SiegelRelations N A W) (B : Matrix (Fin g) (Fin g) k) : Mˣ :=
  if hB : Bᵀ = B then
    { val := N B, inv := N (-B)
      val_inv := by rw [← hR.N_add _ _ hB (by rw [transpose_neg, hB]), add_neg_cancel, hR.N_zero]
      inv_val := by rw [← hR.N_add _ _ (by rw [transpose_neg, hB]) hB, neg_add_cancel, hR.N_zero] }
  else 1

lemma unitsN_val (hR : SiegelRelations N A W) {B : Matrix (Fin g) (Fin g) k} (hB : Bᵀ = B) :
    ((unitsN hR B : Mˣ) : M) = N B := by
  simp [unitsN, hB]

/-- $A(a)$ as a unit of $M$ (inverse $A(a^{-1})$). -/
def unitsA (hR : SiegelRelations N A W) (a : GL (Fin g) k) : Mˣ where
  val := A a
  inv := A a⁻¹
  val_inv := by rw [← hR.A_mul, mul_inv_cancel, hR.A_one]
  inv_val := by rw [← hR.A_mul, inv_mul_cancel, hR.A_one]

lemma A_neg_one_comm (hR : SiegelRelations N A W) : W * A (-1) = A (-1) * W := by
  rw [hR.W_A]
  congr 2
  ext i j
  simp [invT_coe, Matrix.one_apply, eq_comm]

lemma A_neg_one_sq (hR : SiegelRelations N A W) : A (-1) * A (-1) = 1 := by
  rw [← hR.A_mul, neg_one_mul, neg_neg, hR.A_one]

/-- $W$ as a unit of $M$ (inverse $WA(-1)$, from $W^2 = A(-1)$ and $A(-1)^2 = 1$). -/
def unitsW (hR : SiegelRelations N A W) : Mˣ where
  val := W
  inv := W * A (-1)
  val_inv := by rw [← mul_assoc, hR.W_W, A_neg_one_sq hR]
  inv_val := by rw [mul_assoc, ← A_neg_one_comm hR, ← mul_assoc, hR.W_W, A_neg_one_sq hR]

/-- The relations hold for the units. -/
lemma siegelRelations_units (hR : SiegelRelations N A W) :
    SiegelRelations (unitsN hR) (unitsA hR) (unitsW hR) where
  N_zero := Units.ext (by rw [unitsN_val hR (by simp), hR.N_zero]; rfl)
  N_add B B' hB hB' := Units.ext (by
    rw [Units.val_mul, unitsN_val hR hB, unitsN_val hR hB', unitsN_val hR (by rw [transpose_add, hB, hB'])]
    exact hR.N_add B B' hB hB')
  A_one := Units.ext hR.A_one
  A_mul a a' := Units.ext (hR.A_mul a a')
  A_N a B hB := Units.ext (by
    rw [Units.val_mul, Units.val_mul, unitsN_val hR hB,
      unitsN_val hR (by simp [transpose_mul, hB, Matrix.mul_assoc])]
    exact hR.A_N a B hB)
  W_A a := Units.ext (hR.W_A a)
  W_W := Units.ext hR.W_W
  W_N_W B hB := Units.ext (by
    simp only [Units.val_mul]
    rw [unitsN_val hR hB, unitsN_val hR (symm_neg_inv hB)]
    exact hR.W_N_W B hB)

end Units

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$, for every infinite field $k$**
(every genus $g$): the named input `SiegelPresentation g k` holds. See the module docstring for the method. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation [Infinite k] : SiegelPresentation.{u} g k := by
  refine ⟨fun M _ N A W hR => ?_⟩
  have hU := siegelRelations_units hR
  obtain ⟨φ, hφ⟩ := exists_monoidHom_of_generic (bigCell (g := g) (k := k))
    (rhoCell (unitsN hR) (unitsA hR) (unitsW hR)) (fun x y hx hy hxy => rhoCell_mul hU hx hy hxy)
    (fun L => by
      obtain ⟨T, hT, hL⟩ := exists_spN_spW_generic L
      exact ⟨spN T hT * spW, spN_spW_mem_bigCell T hT, hL⟩)
  have hW : φ spW = unitsW hR := by rw [hφ _ spW_mem_bigCell, rhoCell_spW hU]
  refine ⟨(Units.coeHom M).comp φ, fun B hB => ?_, fun a => ?_, ?_⟩
  · have h := hφ _ (spN_spW_mem_bigCell B hB)
    rw [rhoCell_spN_spW hU, map_mul, hW] at h
    have h' := mul_right_cancel h
    simp [h', unitsN_val hR hB]
  · have h := hφ _ (spM_spW_mem_bigCell a)
    rw [rhoCell_spM_spW hU, map_mul, hW] at h
    have h' := mul_right_cancel h
    simp [h', unitsA]
  · simp [hW, unitsW]

end QuadFormsKB.WeilRep.Genus
