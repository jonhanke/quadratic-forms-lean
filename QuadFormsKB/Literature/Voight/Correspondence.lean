/-
# Quaternion orders and ternary quadratic forms: the statements (Voight, Ch. 22)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Chapter 22 (key `voight2021`).

**The correspondence.** Over a principal ideal domain $R$ with fraction field $F$, the even Clifford
algebra $Q \mapsto \operatorname{Clf}^0(Q)$ (built explicitly in `Voight/EvenClifford.lean`) induces a
discriminant-preserving bijection
$$\{\text{nondegenerate ternary quadratic forms over } R\}/\text{similarity}
\;\longleftrightarrow\; \{\text{quaternion orders over } R\}/\text{isomorphism}$$
(Main Theorems 22.1.1 = 22.4.1, Gross–Lucianovic), with inverse $O \mapsto N \operatorname{nrd}^\sharp(O)$;
over a Dedekind domain the same holds with similarity replaced by twisted similarity
(Main Theorem 22.5.7).

**Definitions used** (all in Voight's terms):
* `IsQuaternionAlgebra F B`: $B \cong (K, b \mid F) = K \oplus Kj$ with $K = F[i]$ a separable
  quadratic $F$-algebra, $j^2 = b \ne 0$ and $j\alpha = \bar\alpha j$ (Voight 6.1.5, which agrees with
  Definition 2.2.1 when $\operatorname{char} F \ne 2$). Mathlib's `ℍ[F,c₁,c₂,c₃]` is exactly
  $(F[i], c_3 \mid F)$ with $i^2 = c_1 + c_2 i$; separability of $F[i]$ is $c_2^2 + 4c_1 \ne 0$.
* `IsQuaternionOrder R F O`: an $R$-algebra $O$, finitely generated and torsion-free as an
  $R$-module, such that $B = O \otimes_R F$ is a quaternion algebra (Voight 10.2.1–10.2.2: such an
  algebra is an $R$-order in $B$).
* `Similar Q Q'`: $Q'(\vec x) = c\, Q(P\vec x)$ for some $P \in \mathrm{GL}_3(R)$ and $c \in R^\times$
  (Voight 22.1: the change of variable by $\mathrm{GL}_3(R)$ and rescaling by $R^\times$).
* Nondegenerate: the half-discriminant $N = 4abc + uvw - au^2 - bv^2 - cw^2$ (`ternaryDisc`) is nonzero.

**Status.**
* `EvenCliffordCorrespondence R F` is the statement of Main Theorem 22.4.1 (a named `Prop`
  structure; not proved here).
* Proved in other files: the clause `isQuaternionOrder` when $\operatorname{char} F \ne 2$
  (`isQuaternionOrder_clf0`, Corollary 22.3.22, `Voight/QuaternionOrder.lean`), and the "if" direction of
  `nonempty_equiv_iff_similar` over every commutative ring (`nonempty_clf0_equiv_of_similar`,
  Theorem 22.2.11, `Voight/Functoriality.lean`). Open: `exists_clf0` (Proposition 22.4.4, good bases) and
  the "only if" direction (Proposition 22.4.12, second half).
* Proved here: the discriminant clause (`span_det_trd_gram_clf0`: $\operatorname{disc}(\operatorname{Clf}^0(Q))
  = (N^2)$, so $\operatorname{discrd} = (N)$); rescaling invariance (`clf0SmulEquiv`:
  $\operatorname{Clf}^0(cQ) \cong \operatorname{Clf}^0(Q)$ for $c \in R^\times$), the rescaling half of
  "similar forms give isomorphic orders"; and the counterexample to a claim on p. 354
  (`not_exists_minor_ne_zero_example`).

Indices are 0-based (Voight's $x, y, z$ are $x_0, x_1, x_2$).
-/
import QuadFormsKB.Literature.Voight.EvenClifford

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open scoped TensorProduct Quaternion

universe u

namespace QuadFormsKB.Voight

/-! ## Quaternion algebras and orders -/

/-- **Quaternion algebra over a field** (Voight 2021, 6.1.5; Definition 2.2.1 when
$\operatorname{char} F \ne 2$): an $F$-algebra $B$ is a quaternion algebra if
$B \cong (K, b \mid F) = K \oplus K j$, where $K = F[i]$, $i^2 = c_1 + c_2 i$, is a separable quadratic
$F$-algebra ($c_2^2 + 4 c_1 \ne 0$), $j^2 = c_3 = b \in F^\times$ and $j \alpha = \bar\alpha j$ for
$\alpha \in K$. This is Mathlib's `ℍ[F,c₁,c₂,c₃]` (`QuaternionAlgebra F c₁ c₂ c₃`, where $ji = c_2 j - ij$,
i.e. $ji = \bar i j$). In characteristic $\ne 2$, completing the square gives Voight's
$(a, b \mid F)$ with $a = c_2^2/4 + c_1$ (Voight 6.1.3). -/
@[kb "voight2021" "6.1.5, p. 86; Definition 2.2.1, p. 22"]
def IsQuaternionAlgebra (F B : Type*) [Field F] [Ring B] [Algebra F B] : Prop :=
  ∃ c₁ c₂ c₃ : F, c₂ ^ 2 + 4 * c₁ ≠ 0 ∧ c₃ ≠ 0 ∧ Nonempty (B ≃ₐ[F] ℍ[F,c₁,c₂,c₃])

/-- **Quaternion order over a domain** (Voight 2021, Definition 10.2.1 and 10.2.2): for a domain
$R$ with fraction field $F$, an $R$-algebra $O$ is a quaternion $R$-order if it is finitely generated
and torsion-free as an $R$-module (so $O$ is an $R$-lattice in $B = F \otimes_R O$ and a subring of it)
and $B$ is a quaternion algebra over $F$. -/
@[kb "voight2021" "Definition 10.2.1, 10.2.2, p. 156"]
structure IsQuaternionOrder (R F O : Type*) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Ring O] [Algebra R O] : Prop where
  /-- $O$ is a finitely generated $R$-module. -/
  finite : Module.Finite R O
  /-- $O$ is a torsion-free $R$-module (so $O \hookrightarrow F \otimes_R O$). -/
  torsionFree : Module.IsTorsionFree R O
  /-- $B = F \otimes_R O$ is a quaternion algebra over $F$. -/
  quaternion : IsQuaternionAlgebra F (F ⊗[R] O)

/-- **Similar quadratic forms** (Voight 2021, 22.1, p. 353):
$Q$ and $Q'$ in $n$ variables over $R$ are similar if $Q'(\vec x) = c\,Q(P\vec x)$ for all $\vec x \in R^n$,
for some $P \in \mathrm{GL}_n(R)$ and $c \in R^\times$ (change of variables on the domain and rescaling by
a unit on the codomain). -/
@[kb "voight2021" "22.1, p. 353"]
def Similar {R : Type*} [CommRing R] {n : ℕ} (Q Q' : QuadForm R n) : Prop :=
  ∃ c : Rˣ, ((c : R) • Q).IsometricIn R Q'

/-! ## Main Theorem 22.4.1 (statement) -/

/-- **Main Theorem 22.1.1 = Main Theorem 22.4.1 (Gross–Lucianovic)**, stated as a named
proposition. For a domain $R$ with fraction field $F$:

1. (`isQuaternionOrder`) for every nondegenerate ternary form $Q$ over $R$ (half-discriminant
   $N \ne 0$), $\operatorname{Clf}^0(Q)$ is a quaternion $R$-order (Voight Corollary 22.3.22);
2. (`exists_clf0`) every quaternion $R$-order $O$ (in the universe of $R$) is isomorphic to
   $\operatorname{Clf}^0(Q)$ for a nondegenerate ternary form $Q$ (Voight Proposition 22.4.4);
3. (`nonempty_equiv_iff_similar`) for nondegenerate $Q, Q'$:
   $\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ as $R$-algebras iff $Q$ and $Q'$ are similar
   (Voight Proposition 22.4.12 and the functoriality of $\operatorname{Clf}^0$, Theorem 22.2.11).

Together: $Q \mapsto \operatorname{Clf}^0(Q)$ is a bijection from similarity classes of nondegenerate
ternary forms to isomorphism classes of quaternion $R$-orders. The discriminant clause
($\operatorname{discrd}\operatorname{Clf}^0(Q) = N R$) is proved unconditionally
(`span_det_trd_gram_clf0`). Voight proves the theorem for $R$ a principal ideal domain (`mainTheorem_22_4_1` is the
hypothesis-free form of the claim for principal ideal domains; it is a statement, not proved here). -/
@[kb "voight2021" "Main Theorem 22.1.1, p. 353; Main Theorem 22.4.1, p. 364"]
structure EvenCliffordCorrespondence (R : Type u) (F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] : Prop where
  /-- $\operatorname{Clf}^0(Q)$ is a quaternion order for nondegenerate $Q$. -/
  isQuaternionOrder : ∀ Q : QuadForm R 3, ternaryDisc Q ≠ 0 → IsQuaternionOrder R F (Clf0 Q)
  /-- Every quaternion order is an even Clifford algebra. -/
  exists_clf0 : ∀ (O : Type u) [Ring O] [Algebra R O], IsQuaternionOrder R F O →
    ∃ Q : QuadForm R 3, ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Clf0 Q)
  /-- Isomorphic even Clifford algebras exactly for similar forms. -/
  nonempty_equiv_iff_similar : ∀ Q Q' : QuadForm R 3, ternaryDisc Q ≠ 0 → ternaryDisc Q' ≠ 0 →
    (Nonempty (Clf0 Q ≃ₐ[R] Clf0 Q') ↔ Similar Q Q')

/-- **Main Theorem 22.4.1 for principal ideal domains** (Voight 2021, p. 364), as a proposition:
for every principal ideal domain $R$ with fraction field $F$, `EvenCliffordCorrespondence R F` holds.
Stated, not proved: Proposition 22.4.4 (every quaternion order has a good basis) is not formalized. -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364"]
def MainTheorem22_4_1 : Prop :=
  ∀ (R F : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F]
    [IsFractionRing R F], EvenCliffordCorrespondence R F

/-! ## Proved parts -/

section Proved

variable {R : Type*} [CommRing R]

/-- **The discriminant clause of Main Theorem 22.4.1** (Voight Lemma 22.3.19, (22.3.21)): the
discriminant $\operatorname{disc}(\operatorname{Clf}^0(Q))$, the ideal generated by
$\det(\operatorname{trd}(e_p e_q))$ for the basis $e = (1, i, j, k)$, is $(N^2)$; hence the reduced
discriminant (its square root, Lemma 15.4.7) is $N R$. -/
@[kb "voight2021" "Lemma 22.3.19, p. 362"]
theorem span_det_trd_gram_clf0 (Q : QuadForm R 3) :
    Ideal.span {(Matrix.of fun p q : Fin 4 =>
      EvenClf.trd ((![1, EvenClf.ei, EvenClf.ej, EvenClf.ek] : Fin 4 → Clf0 Q) p *
        (![1, EvenClf.ei, EvenClf.ej, EvenClf.ek] : Fin 4 → Clf0 Q) q)).det} =
      Ideal.span {ternaryDisc Q ^ 2} := by
  rw [EvenClf.det_trd_gram, ← ternaryDisc, Ideal.span_singleton_neg]

/-- **Rescaling** (Voight 22.1: similarity includes rescaling by $R^\times$): for $c \in R$, the map
$i \mapsto c\,i$, $j \mapsto c\,j$, $k \mapsto c\,k$ is an $R$-algebra homomorphism
$\operatorname{Clf}^0(cQ) \to \operatorname{Clf}^0(Q)$; for a unit $c$ it is an isomorphism
(`clf0SmulEquiv`). -/
def EvenClf.scaleHom (r a b c u v w : R) :
    EvenClf R (r * a) (r * b) (r * c) (r * u) (r * v) (r * w) →ₐ[R] EvenClf R a b c u v w where
  toFun x := ⟨x.re, r * x.i, r * x.j, r * x.k⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> ring
  commutes' s := by ext <;> simp

/-- The identity map between even Clifford algebras with equal coefficients. -/
def EvenClf.congrEquiv {a b c u v w a' b' c' u' v' w' : R} (ha : a = a') (hb : b = b')
    (hc : c = c') (hu : u = u') (hv : v = v') (hw : w = w') :
    EvenClf R a b c u v w ≃ₐ[R] EvenClf R a' b' c' u' v' w' where
  toFun x := ⟨x.re, x.i, x.j, x.k⟩
  invFun x := ⟨x.re, x.i, x.j, x.k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by subst ha hb hc hu hv hw; rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **Rescaling by a unit gives isomorphic even Clifford algebras**:
$\operatorname{Clf}^0(cQ) \cong \operatorname{Clf}^0(Q)$ for $c \in R^\times$ (the rescaling half of
"similar forms have isomorphic even Clifford algebras", Voight Theorem 22.2.11). -/
@[kb "voight2021" "Theorem 22.2.11, p. 357"]
def clf0SmulEquiv (c : Rˣ) (Q : QuadForm R 3) : Clf0 ((c : R) • Q) ≃ₐ[R] Clf0 Q :=
  AlgEquiv.ofAlgHom
    (EvenClf.scaleHom (c : R) (Q.coeff 0 0) (Q.coeff 1 1) (Q.coeff 2 2) (Q.coeff 1 2)
      (Q.coeff 0 2) (Q.coeff 0 1))
    ((EvenClf.scaleHom ((c⁻¹ : Rˣ) : R) ((c : R) * Q.coeff 0 0) ((c : R) * Q.coeff 1 1)
      ((c : R) * Q.coeff 2 2) ((c : R) * Q.coeff 1 2) ((c : R) * Q.coeff 0 2)
      ((c : R) * Q.coeff 0 1)).comp
      (EvenClf.congrEquiv (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).toAlgHom)
    (by ext x <;> simp [EvenClf.scaleHom, EvenClf.congrEquiv])
    (by ext x <;> simp [EvenClf.scaleHom, EvenClf.congrEquiv])

/-- **A claim on p. 354 is false** (Voight 22.1, after (22.1.2): "At least one of the minors
$u^2 - 4bc$, $v^2 - 4ac$, $w^2 - 4ab$ of the Gram matrix of $Q$ in the standard basis is nonzero since
$Q$ is nondegenerate"). Counterexample: $Q = x_0^2 + x_1^2 + x_2^2 - 2x_1x_2 - 2x_0x_2 - 2x_0x_1$, i.e.
$(a,b,c,u,v,w) = (1,1,1,-2,-2,-2)$, has $N = -16 \ne 0$ but all three minors vanish (its Gram matrix
$\begin{pmatrix} 2&-2&-2\\-2&2&-2\\-2&-2&2\end{pmatrix}$ has all principal $2 \times 2$ minors $0$ and
determinant $-32$). The splitting $B \cong (w^2 - 4ab, -aN \mid F)$ there therefore needs a change of
basis first. -/
@[kb "voight2021" "22.1, p. 354 (erratum)"]
theorem not_exists_minor_ne_zero_example :
    EvenClf.halfDisc (1 : ℤ) 1 1 (-2) (-2) (-2) = -16 ∧
      (-2 : ℤ) ^ 2 - 4 * 1 * 1 = 0 ∧ (-2 : ℤ) ^ 2 - 4 * 1 * 1 = 0 ∧ (-2 : ℤ) ^ 2 - 4 * 1 * 1 = 0 := by
  norm_num [EvenClf.halfDisc]

end Proved

end QuadFormsKB.Voight
