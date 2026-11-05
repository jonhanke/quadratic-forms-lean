/-
# Cassels, Appendix B, §3, pp. 377–378: representations of forms by forms

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §3, pp. 377–378. Let $f$ be a form in $n$
variables and $g$ a form in $l$ variables, both classically integral (Cassels' "integral": the symmetric matrices
$F = (f_{ij})$, $G = (g_{ij})$ are integral; here `casselsMat`). An integral matrix $X$ is an *integral representation of
$g$ by $f$* if $X^{\mathsf T}FX = G$ (3.10).

*Erratum (candidate).* Cassels calls $X$ an "$l \times n$" matrix; for $X^{\mathsf T}FX$ to make sense with $F$ of size
$n \times n$ and to equal $G$ of size $l \times l$, $X$ must be $n \times l$ (`Matrix (Fin n) (Fin l) ℤ` here): its $l$
columns are the vectors representing the diagonal entries $g_{jj}$ and the cross terms. (Indices are 0-based; Cassels'
variables $x_1, \dots, x_n$ are $x_0, \dots, x_{n-1}$ here.)

**Defines**
* `repMatSet f g`, `repMatNum f g` (3.10): the set of integral representations of $g$ by $f$, and its cardinality
  $A(f, g)$ (finite when $f$ is positive definite, `repMatSet_finite`);
* `repSumGenus f g` (3.11): $S(\mathcal F, g) = \sum_{f'} A(f', g)/o^{+}(f')$ over representatives $f'$ of the proper classes
  of the genus $\mathcal F$ of $f$ (`pgenusClasses`, as `pweight`);
* `repRatioGenus f g` (3.12): $\mathcal A(\mathcal F, g) = S(\mathcal F, g)/W(\mathcal F)$, $W = $ `pweight`.

**Proves**
* `repMatSet_finite`: finiteness of $A(f, g)$ for positive definite $f$;
* `repMatNum_eq_of_intEquiv_left`, `repMatNum_eq_of_intEquiv_right`: $A(f, g)$ is a class invariant in each argument
  ($X \mapsto U^{-1}X$ and $X \mapsto XV$);
* `repSumGenus_eq_of_sameGenus_left`: $S(\mathcal F, g)$ depends on $f$ only through its genus;
* `repMatNum_unary`: for $l = 1$, $A(f, \langle a\rangle)$ is the library's representation number `repNum f a`;
* `repMatNum_eq_repCountT`: $A(f, g)$ is the library's lattice representation number `Tamagawa.Frames.repCountT` of
  $g\otimes\mathbb Q$ by $\mathbb Z^n \subset (\mathbb Q^n, f\otimes\mathbb Q)$ (frames with integral columns and Gram form $g$).

**Not formalized here: (3.13)–(3.17).** Siegel's formula $\mathcal A(\mathcal F, \mathcal G) = \varepsilon\prod_{p\le\infty}\alpha_p$
and the resulting statement that $S(\mathcal F, g)$ depends only on the genus of $g$ are *proved in the library* in the
lattice formulation by `Tamagawa.Frames.siegelForms_all_ranks` (`Tamagawa/FrameSiegelAll.lean`), whose left side is
`repMassT` (a sum over classes of lattices in the genus of $\mathbb Z^n$ of $r_M(T)/\lvert O(M)\rvert$) and whose right
side is `siegelProductAll`. No hypothesis is assumed here (in particular there is no named input for (3.13)). Not yet
proved, so that `repSumGenus f g` is not yet expressed through `siegelForms_all_ranks`: (a) a bridge between the sum over
classes of lattices in the genus of $\mathbb Z^n$ (`repMassT`) and the sum over proper classes of integral forms in the
genus of $f$ (`repSumGenus`; the factor $2$ is that of `pweight_eq_two_mul_mass`, and the per-class terms agree by
`repMatNum_eq_repCountT`); (b) invariance of `siegelProductAll` (equivalently of the local densities
`NF.siegelDensity`, and of the archimedean factor through $\det g$) under local equivalence of $T$, to conclude that
$S(\mathcal F, g)$ depends only on the genus of $g$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.MassFormula

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n l : ℕ}

/-! ### Helpers on matrices -/

/-- Helper: the diagonal entry $(X^{\mathsf T}AX)_{jj}$ is the quadratic value of the $j$-th column of $X$. -/
theorem conj_diag_eq (A : Matrix (Fin n) (Fin n) ℤ) (X : Matrix (Fin n) (Fin l) ℤ) (j : Fin l) :
    (Xᵀ * A * X) j j = (fun i => X i j) ⬝ᵥ (A *ᵥ fun i => X i j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Helper: $(U^{-1}X)^{\mathsf T}(U^{\mathsf T}AU)(U^{-1}X) = X^{\mathsf T}AX$ for invertible $U$ over a commutative
ring. -/
theorem conj_inv_cancel {R : Type*} [CommRing R] (U : GL (Fin n) R) (A : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) (Fin l) R) :
    ((U⁻¹).val * X)ᵀ * (U.valᵀ * A * U.val) * ((U⁻¹).val * X) = Xᵀ * A * X := by
  have h1 : U.val * (U⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((U⁻¹).val)ᵀ * U.valᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  calc ((U⁻¹).val * X)ᵀ * (U.valᵀ * A * U.val) * ((U⁻¹).val * X)
      = Xᵀ * (((U⁻¹).val)ᵀ * U.valᵀ) * A * (U.val * (U⁻¹).val) * X := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Xᵀ * A * X := by rw [h1, h2]; simp [Matrix.mul_assoc]

/-- Helper: $(UX)^{\mathsf T}A'(UX) = X^{\mathsf T}(U^{\mathsf T}A'U)X$. -/
theorem conj_mul_eq_mat {R : Type*} [CommRing R] (U : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) (Fin l) R) : (U * X)ᵀ * A * (U * X) = Xᵀ * (Uᵀ * A * U) * X := by
  simp only [transpose_mul, Matrix.mul_assoc]

/-- Helper: left change of variables. If $U^{\mathsf T}AU = A'$ with $U$ invertible then $X \mapsto U^{-1}X$ is a
bijection from the solutions of $X^{\mathsf T}AX = G$ to those of $Y^{\mathsf T}A'Y = G$ (any commutative ring). -/
def leftEquiv {R : Type*} [CommRing R] (A A' : Matrix (Fin n) (Fin n) R) (G : Matrix (Fin l) (Fin l) R)
    (U : GL (Fin n) R) (hU : U.valᵀ * A * U.val = A') :
    {X : Matrix (Fin n) (Fin l) R // Xᵀ * A * X = G} ≃ {X : Matrix (Fin n) (Fin l) R // Xᵀ * A' * X = G} where
  toFun X := ⟨(U⁻¹).val * X.1, by rw [← hU, conj_inv_cancel]; exact X.2⟩
  invFun Y := ⟨U.val * Y.1, by rw [conj_mul_eq_mat, hU]; exact Y.2⟩
  left_inv X := Subtype.ext (by
    show U.val * ((U⁻¹).val * X.1) = X.1
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul])
  right_inv Y := Subtype.ext (by
    show (U⁻¹).val * (U.val * Y.1) = Y.1
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])

/-- Helper: right change of variables. If $V^{\mathsf T}GV = G'$ with $V$ invertible then $X \mapsto XV$ is a bijection
from the solutions of $X^{\mathsf T}AX = G$ to those of $Y^{\mathsf T}AY = G'$ (any commutative ring). -/
def rightEquiv {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (G G' : Matrix (Fin l) (Fin l) R)
    (V : GL (Fin l) R) (hV : V.valᵀ * G * V.val = G') :
    {X : Matrix (Fin n) (Fin l) R // Xᵀ * A * X = G} ≃ {X : Matrix (Fin n) (Fin l) R // Xᵀ * A * X = G'} where
  toFun X := ⟨X.1 * V.val, by
    have h := X.2
    have e : (X.1 * V.val)ᵀ * A * (X.1 * V.val) = V.valᵀ * (X.1ᵀ * A * X.1) * V.val := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e, h, hV]⟩
  invFun Y := ⟨Y.1 * (V⁻¹).val, by
    have h := conj_inv_cancel V G Y.1ᵀ
    have e : (Y.1 * (V⁻¹).val)ᵀ * A * (Y.1 * (V⁻¹).val) =
        ((V⁻¹).val)ᵀ * (Y.1ᵀ * A * Y.1) * (V⁻¹).val := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e, Y.2, ← hV]
    have h1 : V.val * (V⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((V⁻¹).val)ᵀ * V.valᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
    calc ((V⁻¹).val)ᵀ * (V.valᵀ * G * V.val) * (V⁻¹).val
        = (((V⁻¹).val)ᵀ * V.valᵀ) * G * (V.val * (V⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]; simp⟩
  left_inv X := Subtype.ext (by
    show X.1 * V.val * (V⁻¹).val = X.1
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  right_inv Y := Subtype.ext (by
    show Y.1 * (V⁻¹).val * V.val = Y.1
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one])

/-! ### (3.10): integral representations of $g$ by $f$ -/

/-- **The integral representations of $g$ by $f$** (Cassels, App. B, §3, (3.10), p. 377): the integral $n \times l$
matrices $X$ with $X^{\mathsf T}FX = G$, where $F = $ `casselsMat f` and $G = $ `casselsMat g` are the matrices of the
classically integral forms $f$ (in $n$ variables) and $g$ (in $l$ variables). (Cassels prints $X$ as $l \times n$; see the
erratum in the module docstring.) Arguments: `f` the representing form, `g` the represented form. -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377"]
def repMatSet (f : QuadForm ℤ n) (g : QuadForm ℤ l) : Set (Matrix (Fin n) (Fin l) ℤ) :=
  {X | Xᵀ * casselsMat f * X = casselsMat g}

/-- **The number $A(f, g)$ of integral representations of $g$ by $f$** (Cassels, App. B, §3, p. 377): the cardinality of
`repMatSet f g` (`Nat.card`, so $0$ if the set were infinite, which does not happen for positive definite $f$,
`repMatSet_finite`). For $l = 1$ it is the number of representations of an integer (`repMatNum_unary`). -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (the number A(f, g))"]
def repMatNum (f : QuadForm ℤ n) (g : QuadForm ℤ l) : ℕ := Nat.card (repMatSet f g)

/-- **Finiteness of $A(f, g)$ for positive definite $f$** (Cassels, App. B, §3, p. 377: *when $f$ is positive definite the
number of integral representations is finite*). *Proof:* each column of $X$ represents a diagonal entry $g_{jj}$ by $f$,
and a positive definite form represents a given integer finitely often. Arguments: `hf` positive definiteness of $f$,
`hfc` classical integrality of $f$ (which makes $f(\mathbf x) = \mathbf x^{\mathsf T}F\mathbf x$). -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (A(f, g) is finite for positive definite f)"]
theorem repMatSet_finite {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hfc : IsClassicallyIntegral f)
    (g : QuadForm ℤ l) : (repMatSet f g).Finite := by
  have hT : (Set.pi Set.univ fun j : Fin l => repSet f ((casselsMat g) j j)).Finite :=
    Set.Finite.pi fun j => IntQF.PosDef.repSet_finite hf _
  refine (hT.preimage (Matrix.transpose_injective (m := Fin n) (n := Fin l) (α := ℤ)).injOn).subset ?_
  intro X hX j _
  have h1 : f.eval (fun i => X i j) = (Xᵀ * casselsMat f * X) j j := by
    rw [conj_diag_eq, eval_eq_casselsMat hfc]
  show f.eval (fun i => X i j) = _
  rw [h1, show Xᵀ * casselsMat f * X = casselsMat g from hX]

/-- **Left class invariance of $A(f, g)$:** $A(f \circ U, g) = A(f, g)$ for $U \in \mathrm{GL}_n(\mathbb Z)$, i.e. $A$
depends on $f$ only through its $\mathrm{GL}_n(\mathbb Z)$-class (bijection $X \mapsto U^{-1}X$). Arguments: `hf`, `hf'`
classical integrality of $f$, $f'$; `h` integral equivalence of $f$ and $f'$. -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (A(f, g) depends only on the class of f)"]
theorem repMatNum_eq_of_intEquiv_left {f f' : QuadForm ℤ n} (hf : IsClassicallyIntegral f)
    (hf' : IsClassicallyIntegral f') (h : IntEquiv f f') (g : QuadForm ℤ l) :
    repMatNum f g = repMatNum f' g := by
  obtain ⟨U, hU⟩ := h
  have hU' := (eval_mulVec_iff_casselsMat hf hf' U.val).mp hU
  exact Nat.card_congr (leftEquiv (casselsMat f) (casselsMat f') (casselsMat g) U hU')

/-- **Right class invariance of $A(f, g)$:** $A(f, g \circ V) = A(f, g)$ for $V \in \mathrm{GL}_l(\mathbb Z)$, i.e. $A$
depends on $g$ only through its $\mathrm{GL}_l(\mathbb Z)$-class (bijection $X \mapsto XV$). Arguments: `hg`, `hg'`
classical integrality of $g$, $g'$; `h` integral equivalence of $g$ and $g'$. -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (A(f, g) depends only on the class of g)"]
theorem repMatNum_eq_of_intEquiv_right (f : QuadForm ℤ n) {g g' : QuadForm ℤ l}
    (hg : IsClassicallyIntegral g) (hg' : IsClassicallyIntegral g') (h : IntEquiv g g') :
    repMatNum f g = repMatNum f g' := by
  obtain ⟨V, hV⟩ := h
  have hV' := (eval_mulVec_iff_casselsMat hg hg' V.val).mp hV
  exact Nat.card_congr (rightEquiv (casselsMat f) (casselsMat g) (casselsMat g') V hV')

/-- Helper: the matrix of the unary form $a x_0^2$ is $(a)$. -/
theorem casselsMat_diag_one (a : ℤ) :
    casselsMat (QuadForm.diag fun _ : Fin 1 => a) = Matrix.of fun _ _ => a := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [casselsMat, QuadForm.hessian, QuadForm.diag]
  omega

/-- **For $l = 1$, $A(f, \langle a\rangle)$ is the representation number of the integer $a$** (Cassels, App. B, §3,
p. 377: *if $l = 1$ this is the representation of an integer*): $A(f, a x_0^2) = r_f(a)$ (`repNum`), for classically
integral $f$. Arguments: `hf` classical integrality of $f$, `a` the represented integer. -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (for l = 1 this is the representation of an integer)"]
theorem repMatNum_unary {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (a : ℤ) :
    repMatNum f (QuadForm.diag fun _ : Fin 1 => a) = repNum f a := by
  have key : ∀ X : Matrix (Fin n) (Fin 1) ℤ, (Xᵀ * casselsMat f * X) 0 0 = f.eval (fun i => X i 0) := by
    intro X; rw [conj_diag_eq, eval_eq_casselsMat hf]
  refine Nat.card_congr
    { toFun := fun X => ⟨fun i => X.1 i 0, by
        have h : X.1ᵀ * casselsMat f * X.1 = casselsMat (QuadForm.diag fun _ : Fin 1 => a) := X.2
        have := congrFun (congrFun h 0) 0
        rw [key, casselsMat_diag_one] at this
        exact (by simpa using this : f.eval (fun i => X.1 i 0) = a)⟩
      invFun := fun x => ⟨Matrix.of fun i _ => x.1 i, by
        show _ᵀ * casselsMat f * _ = casselsMat (QuadForm.diag fun _ : Fin 1 => a)
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst hi hj
        rw [key, casselsMat_diag_one]
        have : f.eval x.1 = a := x.2
        simpa using this⟩
      left_inv := fun X => by
        apply Subtype.ext; ext i j
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj; rfl
      right_inv := fun x => rfl }

/-! ### (3.11), (3.12): the sum over the genus and its ratio to the weight -/

/-- **The sum $S(\mathcal F, g)$** (Cassels, App. B, §3, (3.11), p. 377): $\sum_{f'} A(f', g)/o^{+}(f')$ over
representatives $f'$ of the proper classes of the genus $\mathcal F$ of `f` (as `pweight`: a `finsum` over
`pgenusClasses f`, using the representative `C.out` of each class; each term is independent of the representative by
`repMatNum_eq_of_intEquiv_left` and `card_autPlus_eq_of_intEquiv` when the forms are classically integral). Arguments:
`f` any representative of the genus $\mathcal F$, `g` the represented form. -/
@[kb "cassels1978" "App. B, §3, (3.11), p. 377 (the sum S(𝓕, g))"]
def repSumGenus (f : QuadForm ℤ n) (g : QuadForm ℤ l) : ℝ :=
  ∑ᶠ C ∈ pgenusClasses f, (repMatNum C.out g : ℝ) / Nat.card (AutPlus C.out)

/-- **The ratio $\mathcal A(\mathcal F, g) = S(\mathcal F, g)/W(\mathcal F)$** (Cassels, App. B, §3, (3.12), p. 377), with
$W(\mathcal F) = $ `pweight f` $= \sum 1/o^{+}(f')$. Arguments as in `repSumGenus`. -/
@[kb "cassels1978" "App. B, §3, (3.12), p. 377 (the ratio 𝒜 = S / W)"]
def repRatioGenus (f : QuadForm ℤ n) (g : QuadForm ℤ l) : ℝ := repSumGenus f g / pweight f

/-- Helper: forms in the same genus have the same proper classes. -/
theorem pgenusClasses_eq_of_sameGenus {f f' : QuadForm ℤ n} (h : SameGenus f f') :
    pgenusClasses f = pgenusClasses f' := by
  ext C
  rw [mem_pgenusClasses_iff_out, mem_pgenusClasses_iff_out]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- **$S(\mathcal F, g)$ depends on $f$ only through its genus** (the genus $\mathcal F$ is what the notation
$S(\mathcal F, g)$ records, Cassels p. 377): `repSumGenus f g = repSumGenus f' g` for $f$, $f'$ in the same genus. -/
@[kb "cassels1978" "App. B, §3, (3.11), p. 377 (S(𝓕, g) depends only on the genus 𝓕)"]
theorem repSumGenus_eq_of_sameGenus_left {f f' : QuadForm ℤ n} (h : SameGenus f f') (g : QuadForm ℤ l) :
    repSumGenus f g = repSumGenus f' g := by
  unfold repSumGenus
  rw [pgenusClasses_eq_of_sameGenus h]

/-- **$\mathcal A(\mathcal F, g)$ depends on $f$ only through its genus.** -/
theorem repRatioGenus_eq_of_sameGenus_left {f f' : QuadForm ℤ n} (h : SameGenus f f') (g : QuadForm ℤ l)
    (hw : pweight f = pweight f') : repRatioGenus f g = repRatioGenus f' g := by
  unfold repRatioGenus
  rw [repSumGenus_eq_of_sameGenus_left h, hw]

/-! ### Comparison with the lattice formulation `Tamagawa.Frames.repCountT` -/

/-- Helper: a vector over $\mathbb Q$ lies in $\mathcal O_{\mathbb Q}^n$ iff its entries are integers. -/
theorem mem_intVec_rat (x : Fin n → ℚ) :
    x ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ z : ℤ, x i = z := by
  rw [Lattices.mem_intVec]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Rat.ringOfIntegersEquiv a, by rw [← ha]; simp [Rat.ringOfIntegersEquiv_apply_coe]⟩
  · rintro ⟨z, hz⟩
    exact ⟨(z : 𝓞 ℚ), by rw [hz]; simp⟩

/-- Helper: over $\mathbb Q$, a symmetric matrix is determined by its quadratic values. -/
theorem eq_of_forall_dotProduct_rat {A B : Matrix (Fin l) (Fin l) ℚ} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  set N := A - B with hN
  have hs : N.IsSymm := hA.sub hB
  have h0 : ∀ x, x ⬝ᵥ (N *ᵥ x) = 0 := fun x => by
    rw [hN, sub_mulVec, dotProduct_sub, h, sub_self]
  have hd : ∀ i, N i i = 0 := fun i => by simpa using h0 (Pi.single i 1)
  ext i j
  have : N i j = 0 := by
    by_cases hij : i = j
    · subst hij; exact hd i
    · have h1 := h0 (Pi.single i 1 + Pi.single j 1)
      simp [mulVec_add, hd] at h1
      have h2 := hs.apply i j
      linarith
  have h3 : A i j - B i j = 0 := this
  linarith

/-- Helper: for classically integral $f$ and $\mathbf x \in \mathbb Q^n$, $f(\mathbf x) = \mathbf x^{\mathsf T}F\mathbf x$
with $F = $ `casselsMat f` (base-changed to $\mathbb Q$). -/
theorem eval_map_rat {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (x : Fin n → ℚ) :
    (f.map (Int.castRingHom ℚ)).eval x = x ⬝ᵥ ((casselsMat f).map (Int.castRingHom ℚ) *ᵥ x) := by
  have h1 := eval_map_eq_dotProduct (Int.castRingHom ℚ) f x
  have hH : (f.hessian).map (Int.castRingHom ℚ) =
      f.coeff.map (Int.castRingHom ℚ) + (f.coeff.map (Int.castRingHom ℚ))ᵀ := by
    simp [QuadForm.hessian, Matrix.map_add, Matrix.transpose_map]
  have hC : (f.hessian).map (Int.castRingHom ℚ) = (2 : ℚ) • (casselsMat f).map (Int.castRingHom ℚ) := by
    rw [hessian_eq_two_smul_casselsMat hf]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_ofNat]
  have h2 : x ⬝ᵥ (((2 : ℚ) • (casselsMat f).map (Int.castRingHom ℚ)) *ᵥ x) =
      2 * (x ⬝ᵥ (f.coeff.map (Int.castRingHom ℚ) *ᵥ x)) := by
    rw [← hC, hH, add_mulVec, dotProduct_add, dotProduct_mulVec_transpose_self]; ring
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul] at h2
  rw [h1]
  linarith

/-- Helper: for classically integral $f$ and $X \in \mathbb Q^{n \times l}$, the Gram form of the frame $X$ in
$(\mathbb Q^n, f)$ is $g$ iff $X^{\mathsf T}FX = G$ over $\mathbb Q$ ($g$ classically integral). -/
theorem compMat_eq_iff {f : QuadForm ℤ n} {g : QuadForm ℤ l} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) (X : Matrix (Fin n) (Fin l) ℚ) :
    (f.map (Int.castRingHom ℚ)).compMat X = g.map (Int.castRingHom ℚ) ↔
      Xᵀ * (casselsMat f).map (Int.castRingHom ℚ) * X = (casselsMat g).map (Int.castRingHom ℚ) := by
  have key : ∀ y : Fin l → ℚ, ((f.map (Int.castRingHom ℚ)).compMat X).eval y =
      y ⬝ᵥ ((Xᵀ * (casselsMat f).map (Int.castRingHom ℚ) * X) *ᵥ y) := fun y => by
    rw [QuadForm.eval_compMat, eval_map_rat hf, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Xᵀ,
      vecMul_transpose]
  constructor
  · intro h
    have hs : (Xᵀ * (casselsMat f).map (Int.castRingHom ℚ) * X).IsSymm := by
      unfold Matrix.IsSymm
      rw [transpose_mul, transpose_mul, transpose_transpose, ((casselsMat_isSymm f).map (Int.castRingHom ℚ)).eq, Matrix.mul_assoc]
    refine eq_of_forall_dotProduct_rat hs ((casselsMat_isSymm g).map _) fun y => ?_
    rw [← key, h, eval_map_rat hg]
  · intro h
    refine QuadForm.eq_of_eval_eq fun y => ?_
    rw [key, h, eval_map_rat hg]

/-- **Comparison with the lattice formulation:** for classically integral $f$, $g$, $A(f, g)$ is the library's
representation number `Tamagawa.Frames.repCountT` of the form $g \otimes \mathbb Q$ by the standard lattice $\mathbb Z^n$ in
$(\mathbb Q^n, f \otimes \mathbb Q)$ (frames: rational $n \times l$ matrices with columns in $\mathbb Z^n$ and Gram form $g$). -/
@[kb "cassels1978" "App. B, §3, (3.10), p. 377 (A(f, g) as the lattice representation number)"]
theorem repMatNum_eq_repCountT {f : QuadForm ℤ n} {g : QuadForm ℤ l} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) :
    repMatNum f g = Tamagawa.Frames.repCountT (f.map (Int.castRingHom ℚ)) (Tamagawa.stdLat ℚ n)
      (g.map (Int.castRingHom ℚ)) := by
  have hcast : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  unfold repMatNum Tamagawa.Frames.repCountT
  refine Nat.card_congr (Equiv.ofBijective
    (fun X : repMatSet f g => (⟨X.1.map (Int.castRingHom ℚ), fun j => ?_, ?_⟩ :
      {Y : Matrix (Fin n) (Fin l) ℚ // (∀ j, (fun i => Y i j) ∈ (Tamagawa.stdLat ℚ n).1) ∧
        (f.map (Int.castRingHom ℚ)).compMat Y = g.map (Int.castRingHom ℚ)})) ⟨?_, ?_⟩)
  · exact (mem_intVec_rat _).mpr fun i => ⟨X.1 i j, rfl⟩
  · refine (compMat_eq_iff hf hg _).mpr ?_
    have h : X.1ᵀ * casselsMat f * X.1 = casselsMat g := X.2
    have := congrArg (fun M => M.map (Int.castRingHom ℚ)) h
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  · intro X Y h
    exact Subtype.ext (Matrix.map_injective hcast (congrArg Subtype.val h))
  · rintro ⟨Y, hcol, hcomp⟩
    choose z hz using fun i j => (mem_intVec_rat _).mp (hcol j) i
    have hY : Y = (Matrix.of z).map (Int.castRingHom ℚ) := by
      ext i j; simp [hz i j]
    have hm := (compMat_eq_iff hf hg Y).mp hcomp
    rw [hY] at hm
    have hX : (Matrix.of z)ᵀ * casselsMat f * Matrix.of z = casselsMat g := by
      refine Matrix.map_injective hcast ?_
      show ((Matrix.of z)ᵀ * casselsMat f * Matrix.of z).map (Int.castRingHom ℚ) = _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      exact hm
    exact ⟨⟨Matrix.of z, hX⟩, Subtype.ext hY.symm⟩

end QuadFormsKB.Siegel
