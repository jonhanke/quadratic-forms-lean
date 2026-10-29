/-
# The symplectic group $\mathrm{Sp}_{2g}$: the Siegel parabolic, $w$, and the relations

**Layer:** pure algebra over a field $k$.

**The group.** $\mathrm{Sp}_{2g}(k)$ is Mathlib's `Matrix.symplecticGroup (Fin g) k`: the $2g\times2g$ matrices $M$ (block
index `Fin g ⊕ Fin g`) with $MJM^{\mathsf T} = J$, $J = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$ (`Sp`). The genus $g$ is any
natural number (0-based indices $0, \dots, g-1$).

**The generators** (Kudla, *Notes on the local theta correspondence*, §I.1; Weil 1964, §1):
$$m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}\ (A \in \mathrm{GL}_g(k)),\qquad
  n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix}\ (B = {}^tB),\qquad
  w = \begin{pmatrix}0&1\\-1&0\end{pmatrix} = J^{-1}$$
(`spM`, `spN`, `spW`). The Siegel parabolic is $P = MN$, $M = \{m(A)\}$, $N = \{n(B)\}$.

**Relations** (`siegelRelations_sp`, all matrix identities): for $A, A' \in \mathrm{GL}_g(k)$, symmetric $B, B'$,
* $n(0) = 1$, $n(B + B') = n(B)n(B')$; $m(1) = 1$, $m(AA') = m(A)m(A')$;
* $m(A)\,n(B) = n(AB\,{}^tA)\,m(A)$;
* $w\,m(A) = m({}^tA^{-1})\,w$;  $w^2 = m(-1)$;
* $w\,n(B)\,w = n(-B^{-1})\,m(-B^{-1})\,w\,n(-B^{-1})$ for $B$ invertible.
For $g = 1$ these are the relations (R1)–(R6) of `Weil/SL2Cells.lean` (`sp1ToSL2`: $\mathrm{Sp}_2(k) \cong \mathrm{SL}_2(k)$,
sending $n(B), m(A), w$ to `nMat`, `mMat`, `wMat`).

**The presentation** (`SiegelPresentation g k`, a named input): any maps $N, A, W$ into a monoid satisfying these
relations (`SiegelRelations`) extend to a monoid homomorphism $\mathrm{Sp}_{2g}(k) \to M$ with the given values on
$n(B)$, $m(A)$, $w$. For $g = 1$ it is **proved** (`siegelPresentation_one`, from the Bruhat-cell presentation `cellHom`).
For $g \ge 2$ it is the presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$ (Bruhat decomposition
$\mathrm{Sp}_{2g} = \bigsqcup_{j\le g}Pw_jP$); it is assumed, not proved.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Weil, *Sur certains groupes
d'opérateurs unitaires*, Acta Math. 111 (1964), §§1–2 [unverified]; Rao, Pacific J. Math. 157 (1993), §2 (Bruhat
decomposition relative to the Siegel parabolic) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.SL2Cells

open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u v

/-- **The symplectic group** $\mathrm{Sp}_{2g}(k) = \{M : MJM^{\mathsf T} = J\}$ (Mathlib's convention,
$J = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$, blocks indexed by `Fin g ⊕ Fin g`). -/
abbrev Sp (g : ℕ) (k : Type*) [Field k] := Matrix.symplecticGroup (Fin g) k

variable {g : ℕ} {k : Type*} [Field k]

/-- ${}^tA^{-1}$ as an element of $\mathrm{GL}_g(k)$. -/
def invT {R : Type*} [CommRing R] (A : GL (Fin g) R) : GL (Fin g) R where
  val := ((A⁻¹ : GL (Fin g) R) : Matrix (Fin g) (Fin g) R)ᵀ
  inv := (A : Matrix (Fin g) (Fin g) R)ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]

@[simp] lemma invT_coe {R : Type*} [CommRing R] (A : GL (Fin g) R) :
    ((invT A : GL (Fin g) R) : Matrix (Fin g) (Fin g) R) = ((A⁻¹ : GL (Fin g) R) : Matrix (Fin g) (Fin g) R)ᵀ :=
  rfl

/-- For symmetric invertible $B$, $B^{-1}$ is symmetric. -/
lemma symm_inv {B : GL (Fin g) k} (hB : (B : Matrix (Fin g) (Fin g) k)ᵀ = B) :
    ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ = ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
  have h : ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (B : Matrix (Fin g) (Fin g) k) = 1 := by
    conv_lhs => rw [← hB]
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ
      = ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * ((B : Matrix _ _ k) * ((B⁻¹ : GL (Fin g) k) : Matrix _ _ k)) := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = ((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]

lemma symm_neg_inv {B : GL (Fin g) k} (hB : (B : Matrix (Fin g) (Fin g) k)ᵀ = B) :
    (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k))ᵀ = -((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
  rw [transpose_neg, symm_inv hB]

/-- **The Levi element** $m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}$, $A \in \mathrm{GL}_g(k)$. -/
@[kb "kudla1996" "§I.1 (the Siegel parabolic $P = MN$, $m(a)$) [unverified]"]
def spM (A : GL (Fin g) k) : Sp g k :=
  ⟨fromBlocks (A : Matrix (Fin g) (Fin g) k) 0 0 (invT A : Matrix (Fin g) (Fin g) k), by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    simp only [invT_coe, transpose_zero, zero_mul, sub_zero]
    rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

/-- **The unipotent element** $n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix}$, $B$ symmetric. -/
@[kb "kudla1996" "§I.1 (the Siegel parabolic $P = MN$, $n(b)$) [unverified]"]
def spN (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) : Sp g k :=
  ⟨fromBlocks 1 B 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp [hB], by simp⟩⟩

/-- **The Weyl element** $w = \begin{pmatrix}0&1\\-1&0\end{pmatrix} = J^{-1}$. -/
@[kb "kudla1996" "§I.1 (the element $w$) [unverified]"]
def spW : Sp g k :=
  ⟨fromBlocks 0 1 (-1) 0, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, by simp⟩⟩

@[simp] lemma spM_coe (A : GL (Fin g) k) : ((spM A : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
    fromBlocks (A : Matrix (Fin g) (Fin g) k) 0 0 (((A⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) := rfl

@[simp] lemma spN_coe (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) :
    ((spN B hB : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) = fromBlocks 1 B 0 1 := rfl

@[simp] lemma spW_coe : ((spW : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) = fromBlocks 0 1 (-1) 0 := rfl

/-! ### Relations in $\mathrm{Sp}_{2g}(k)$ -/

lemma spN_zero : spN (0 : Matrix (Fin g) (Fin g) k) (by simp) = 1 := by
  apply Subtype.ext
  show fromBlocks (1 : Matrix (Fin g) (Fin g) k) 0 0 1 = 1
  exact fromBlocks_one

lemma spN_add (B B' : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) (hB' : B'ᵀ = B') :
    spN (B + B') (by rw [transpose_add, hB, hB']) = spN B hB * spN B' hB' := by
  ext1; simp [fromBlocks_multiply, add_comm]

lemma spM_one : spM (1 : GL (Fin g) k) = 1 := by
  apply Subtype.ext
  simp [fromBlocks_one]

lemma spM_mul (A A' : GL (Fin g) k) : spM (A * A') = spM A * spM A' := by
  apply Subtype.ext
  simp only [spM_coe, Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul,
    zero_add, _root_.mul_inv_rev, Units.val_mul]
  rw [transpose_mul]

lemma spM_spN (A : GL (Fin g) k) (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) :
    spM A * spN B hB = spN ((A : Matrix (Fin g) (Fin g) k) * B * (A : Matrix (Fin g) (Fin g) k)ᵀ)
      (by simp [transpose_mul, hB, Matrix.mul_assoc]) * spM A := by
  apply Subtype.ext
  simp only [spM_coe, spN_coe, Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero,
    add_zero, Matrix.zero_mul, zero_add, Matrix.one_mul]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one]

lemma spW_spM (A : GL (Fin g) k) : spW * spM A = spM (invT A) * spW := by
  apply Subtype.ext
  simp only [spW_coe, spM_coe, Submonoid.coe_mul, fromBlocks_multiply, invT_coe]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.mul_one, Matrix.mul_neg, neg_zero]
  congr 2

lemma spW_sq : spW * spW = spM (-1 : GL (Fin g) k) := by
  apply Subtype.ext
  simp [fromBlocks_multiply]

lemma spW_spN_spW (B : GL (Fin g) k) (hB : (B : Matrix (Fin g) (Fin g) k)ᵀ = B) :
    spW * spN (B : Matrix (Fin g) (Fin g) k) hB * spW =
      spN (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) (symm_neg_inv hB) *
        spM (-B⁻¹) * spW *
        spN (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) (symm_neg_inv hB) := by
  have hBi := symm_inv hB
  apply Subtype.ext
  simp only [spW_coe, spN_coe, spM_coe, Submonoid.coe_mul, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.mul_one, Matrix.mul_neg, neg_zero, inv_neg, Units.val_neg, inv_inv, transpose_neg, neg_neg]
  rw [hB, Units.inv_mul, Units.mul_inv, Matrix.one_mul]
  simp

/-! ### The relations and the presentation -/

/-- **The relations of $\mathrm{Sp}_{2g}(k)$ relative to the Siegel parabolic** for maps $N$ (on symmetric matrices),
$A$ (on $\mathrm{GL}_g(k)$) and an element $W$ of a monoid $M$:
* `N_zero`, `N_add`: $N(0) = 1$, $N(B + B') = N(B)N(B')$ for symmetric $B, B'$;
* `A_one`, `A_mul`: $A(1) = 1$, $A(aa') = A(a)A(a')$;
* `A_N`: $A(a)N(B) = N(aB\,{}^ta)A(a)$ for symmetric $B$;
* `W_A`: $WA(a) = A({}^ta^{-1})W$;
* `W_W`: $W^2 = A(-1)$;
* `W_N_W`: $WN(B)W = N(-B^{-1})\,A(-B^{-1})\,W\,N(-B^{-1})$ for symmetric invertible $B$.
For $g = 1$ these are (R1)–(R6) of `SL2Relations`. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
structure SiegelRelations {M : Type*} [Monoid M] (N : Matrix (Fin g) (Fin g) k → M) (A : GL (Fin g) k → M)
    (W : M) : Prop where
  N_zero : N 0 = 1
  N_add : ∀ B B' : Matrix (Fin g) (Fin g) k, Bᵀ = B → B'ᵀ = B' → N (B + B') = N B * N B'
  A_one : A 1 = 1
  A_mul : ∀ a a' : GL (Fin g) k, A (a * a') = A a * A a'
  A_N : ∀ (a : GL (Fin g) k) (B : Matrix (Fin g) (Fin g) k), Bᵀ = B →
    A a * N B = N ((a : Matrix (Fin g) (Fin g) k) * B * (a : Matrix (Fin g) (Fin g) k)ᵀ) * A a
  W_A : ∀ a : GL (Fin g) k, W * A a = A (invT a) * W
  W_W : W * W = A (-1)
  W_N_W : ∀ B : GL (Fin g) k, (B : Matrix (Fin g) (Fin g) k)ᵀ = B →
    W * N B * W = N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) * A (-B⁻¹) * W *
      N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k))

open Classical in
/-- $n(B)$ extended by $1$ to non-symmetric $B$ (so that it is a function on all matrices). -/
def spNext (B : Matrix (Fin g) (Fin g) k) : Sp g k := if hB : Bᵀ = B then spN B hB else 1

lemma spNext_of_symm {B : Matrix (Fin g) (Fin g) k} (hB : Bᵀ = B) : spNext B = spN B hB := by
  classical
  unfold spNext; rw [dif_pos hB]

/-- **The relations hold in $\mathrm{Sp}_{2g}(k)$** for $N = n$, $A = m$, $W = w$ (they are necessary). -/
@[kb "kudla1996" "§I.1 (the relations among $m(a)$, $n(b)$, $w$) [unverified]"]
theorem siegelRelations_sp : SiegelRelations (spNext (g := g) (k := k)) spM spW where
  N_zero := by rw [spNext_of_symm (by simp)]; exact spN_zero
  N_add B B' hB hB' := by
    rw [spNext_of_symm hB, spNext_of_symm hB', spNext_of_symm (by rw [transpose_add, hB, hB'])]
    exact spN_add B B' hB hB'
  A_one := spM_one
  A_mul := spM_mul
  A_N a B hB := by
    rw [spNext_of_symm hB, spNext_of_symm (by simp [transpose_mul, hB, Matrix.mul_assoc])]
    exact spM_spN a B hB
  W_A := spW_spM
  W_W := spW_sq
  W_N_W B hB := by
    rw [spNext_of_symm hB, spNext_of_symm (symm_neg_inv hB)]
    exact spW_spN_spW B hB

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$** (named input, universe level `u` of
the target monoids): for every monoid $M$ and maps $N, A, W$ satisfying `SiegelRelations`, there is a monoid
homomorphism $\rho : \mathrm{Sp}_{2g}(k) \to M$ with $\rho(n(B)) = N(B)$, $\rho(m(a)) = A(a)$ and $\rho(w) = W$.
For $g = 1$ this is proved (`siegelPresentation_one`); for $g \ge 2$ it is assumed. -/
@[kb "rao1993" "§2 (Bruhat decomposition of $\\mathrm{Sp}$ relative to the Siegel parabolic; generators and relations) [unverified]"]
structure SiegelPresentation (g : ℕ) (k : Type v) [Field k] : Prop where
  extend : ∀ (M : Type u) [Monoid M] (N : Matrix (Fin g) (Fin g) k → M) (A : GL (Fin g) k → M) (W : M),
    SiegelRelations N A W → ∃ ρ : Sp g k →* M,
      (∀ (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B), ρ (spN B hB) = N B) ∧
      (∀ a : GL (Fin g) k, ρ (spM a) = A a) ∧ ρ spW = W

/-! ### Genus one: $\mathrm{Sp}_2 = \mathrm{SL}_2$ -/

/-- The reindexing `Fin 1 ⊕ Fin 1 ≃ Fin 2` (block $0$ is row/column $0$, block $1$ is row/column $1$). -/
def e12 : Fin 1 ⊕ Fin 1 ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun i := if i = 0 then Sum.inl 0 else Sum.inr 0
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] lemma e12_symm_zero : e12.symm 0 = Sum.inl 0 := rfl
@[simp] lemma e12_symm_one : e12.symm 1 = Sum.inr 0 := rfl

/-- **$\mathrm{Sp}_2(k) \to \mathrm{SL}_2(k)$** (injective, `sp1ToSL2_injective`; in fact an isomorphism): reindex
the blocks `Fin 1 ⊕ Fin 1` as `Fin 2`. -/
@[kb "kudla1996" "§I.1 ($\\mathrm{Sp}_2 = \\mathrm{SL}_2$) [unverified]"]
def sp1ToSL2 : Sp 1 k →* SL(2, k) where
  toFun M := ⟨reindex e12 e12 (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k), by
    rw [det_reindex_self]; exact SymplecticGroup.det_eq_one M.2⟩
  map_one' := by
    apply Subtype.ext
    show reindex e12 e12 (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k) = 1
    rw [reindex_apply, submatrix_one_equiv]
  map_mul' M M' := by
    apply Subtype.ext
    show reindex e12 e12 ((M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k) *
        (M' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k)) =
      reindex e12 e12 (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k) *
        reindex e12 e12 (M' : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) k)
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

lemma sp1ToSL2_coe (M : Sp 1 k) :
    ((sp1ToSL2 M : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = reindex e12 e12 (M : Matrix _ _ k) := rfl

lemma sp1ToSL2_injective : Function.Injective (sp1ToSL2 (k := k)) := by
  intro M M' h
  have := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k)) h
  simp only [sp1ToSL2_coe] at this
  exact Subtype.ext ((reindex e12 e12).injective this)

lemma sp1ToSL2_spN (B : Matrix (Fin 1) (Fin 1) k) (hB : Bᵀ = B) : sp1ToSL2 (spN B hB) = nMat (B 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp1ToSL2_coe, fromBlocks]

/-- The scalar $t$ as an element of $\mathrm{GL}_1(k)$. -/
def gl1 (t : kˣ) : GL (Fin 1) k := Units.map (Matrix.scalar (Fin 1) : k →+* Matrix (Fin 1) (Fin 1) k).toMonoidHom t

@[simp] lemma gl1_coe (t : kˣ) : ((gl1 t : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) = Matrix.scalar (Fin 1) (t : k) :=
  rfl

lemma gl1_apply (A : GL (Fin 1) k) : A = gl1 (Units.mk0 ((A : Matrix (Fin 1) (Fin 1) k) 0 0) (by
    intro h
    have := A.isUnit.map (detMonoidHom (n := Fin 1) (R := k))
    simp [det_unique, h] at this)) := by
  ext i j
  fin_cases i; fin_cases j; simp

lemma sp1ToSL2_spM (t : kˣ) : sp1ToSL2 (spM (gl1 t)) = mMat t := by
  ext i j
  have hinv : ((gl1 t)⁻¹ : GL (Fin 1) k) = gl1 t⁻¹ := by rw [gl1, gl1, map_inv]
  fin_cases i <;> fin_cases j <;> simp [sp1ToSL2_coe, fromBlocks, hinv]

lemma sp1ToSL2_spW : sp1ToSL2 (spW : Sp 1 k) = wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp1ToSL2_coe, fromBlocks]

/-- **The presentation holds for $g = 1$** (from the Bruhat-cell presentation `cellHom` of $\mathrm{SL}_2(k)$). -/
@[kb "kudla1996" "§I.1 (the presentation of $\\mathrm{SL}_2$ by $n(b)$, $m(a)$, $w$) [unverified]"]
theorem siegelPresentation_one : SiegelPresentation.{u} 1 k := by
  refine ⟨fun M _ N A W hR => ?_⟩
  -- the one-variable maps
  let N1 : k → M := fun b => N (Matrix.scalar (Fin 1) b)
  let A1 : kˣ → M := fun t => A (gl1 t)
  have hsc : ∀ b : k, (Matrix.scalar (Fin 1) b)ᵀ = Matrix.scalar (Fin 1) b := fun b => by
    ext i j; fin_cases i; fin_cases j; simp
  have hS : SL2Relations N1 A1 W := {
    N_zero := by simpa [N1] using hR.N_zero
    N_add := fun b b' => by simpa [N1] using hR.N_add _ _ (hsc b) (hsc b')
    A_one := by simpa [A1, gl1] using hR.A_one
    A_mul := fun t t' => by simpa [A1, gl1] using hR.A_mul (gl1 t) (gl1 t')
    A_N := fun t b => by
      have h := hR.A_N (gl1 t) _ (hsc b)
      have e : (gl1 t : Matrix (Fin 1) (Fin 1) k) * Matrix.scalar (Fin 1) b * (gl1 t : Matrix (Fin 1) (Fin 1) k)ᵀ =
          Matrix.scalar (Fin 1) ((t : k) ^ 2 * b) := by
        ext i j; fin_cases i; fin_cases j; simp; ring
      rw [e] at h
      exact h
    W_A := fun t => by
      have h := hR.W_A (gl1 t)
      have e : invT (gl1 t) = gl1 t⁻¹ := by
        ext i j; fin_cases i; fin_cases j; simp [invT, gl1, map_inv]
      rw [e] at h
      exact h
    W_W := by
      have h := hR.W_W
      have e : (-1 : GL (Fin 1) k) = gl1 (-1) := by
        ext i j; fin_cases i; fin_cases j; simp [gl1]
      rw [e] at h
      exact h
    W_N_W := fun b hb => by
      have h := hR.W_N_W (gl1 (Units.mk0 b hb)) (hsc b)
      have e1 : -(((gl1 (Units.mk0 b hb))⁻¹ : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) =
          Matrix.scalar (Fin 1) (-b⁻¹) := by
        rw [gl1, ← map_inv]
        ext i j; fin_cases i; fin_cases j; simp
      have e2 : -(gl1 (Units.mk0 b hb))⁻¹ = gl1 (Units.mk0 (-b⁻¹) (unit_ne_zero_aux hb)) := by
        ext i j; fin_cases i; fin_cases j; simp [gl1]
      rw [e1, e2] at h
      exact h }
  refine ⟨(cellHom hS).comp sp1ToSL2, fun B hB => ?_, fun a => ?_, ?_⟩
  · have hB1 : B = Matrix.scalar (Fin 1) (B 0 0) := by ext i j; fin_cases i; fin_cases j; simp
    simp only [MonoidHom.comp_apply, sp1ToSL2_spN, cellHom_nMat, N1]
    rw [← hB1]
  · rw [gl1_apply a]
    simp only [MonoidHom.comp_apply, sp1ToSL2_spM, cellHom_mMat, A1]
  · simp only [MonoidHom.comp_apply, sp1ToSL2_spW, cellHom_wMat]

end QuadFormsKB.WeilRep.Genus
