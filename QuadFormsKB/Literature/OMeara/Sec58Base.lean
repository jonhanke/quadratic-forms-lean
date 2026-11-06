/-
# O'Meara §53 (algebras) and 58:3: extension of scalars of algebras and of the Hasse algebra

**Setting.** Fields $F \subseteq E$ (an `Algebra F E`). O'Meara's $E$-ification $EA$ of an $F$-algebra $A$ (§53,
pp. 130-131) is the $E$-algebra `E ⊗[F] A`, with $A$ embedded by $a \mapsto 1 \otimes a$. For 58:3 the setting of
`Sec58Hasse.lean`: $\operatorname{char} F \ne 2$, the Hasse algebra `Hasse58.hasseAlg a` of a list of values
$a = (a_0, \dots, a_{n-1})$ (units of $F$), $S V = \bigotimes_i (a_i, a_0 \cdots a_i)$.

**Proves**
* **53.r10** (p. 130): `includeRight_injective` ($A \subseteq EA$, same identity) and `mul_unique` (the multiplication of
  $EA$ is the only $E$-bilinear one extending that of $A$);
* **53.r11** (pp. 130-131): `existsUnique_algHom` (an $F$-algebra homomorphism of $A$ into an $E$-algebra $C$ extends
  uniquely to an $E$-algebra homomorphism $EA \to C$); `nonempty_algEquiv_of_algEquiv` (two $E$-ifications of $A$, as
  $E$-algebras with this universal property, are isomorphic by the extension of the identity);
* **53.r12** (p. 131): `algEquiv_baseChange_congr` (isomorphic algebras have isomorphic $E$-ifications);
* **53.r13** (p. 131): `algEquiv_baseChange_tensor`, $E(A_1 \otimes_F A_2) \cong EA_1 \otimes_E EA_2$, and for $r$
  factors `nonempty_algEquiv_baseChange_tprodList`;
* **58:3, extension of scalars** (p. 152): `nonempty_algEquiv_baseChange_hasseAlg` (algebraic form: the Hasse algebra
  of the images of the values) and `nonempty_algEquiv_hasseAlg_baseChange` ($S(EV) \cong E\,S(V)$ for a regular space,
  with $S(EV)$ computed from any orthogonal base of $EV$);
* **58:3, ternary and quaternary rules in the printed form** (p. 152, read from the page image):
  `isBrauerEquivalent_hasseAlg_ternary_printed`, `isBrauerEquivalent_hasseAlg_quaternary_printed`.
-/
import QuadFormsKB.Literature.OMeara.Sec57Base
import QuadFormsKB.Literature.OMeara.Sec51
import QuadFormsKB.Literature.OMeara.Sec58Class

open scoped TensorProduct
open Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Base53

/-! ### §53: the $E$-ification of an algebra -/

section Alg

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable {A : Type*} [Ring A] [Algebra F A]

/-- **53.r10, the embedding** (O'Meara 1963, §53, p. 130): $A \to EA$, $a \mapsto 1 \otimes a$, is an injective
homomorphism of $F$-algebras (so $A$ is a subalgebra of $EA$ with the same identity $1 \otimes 1$). -/
@[kb "omeara1963" "§53, p. 130 (A ⊆ EA, same identity)"]
theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[F] E ⊗[F] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective

/-- **53.r10, uniqueness of the multiplication** (O'Meara 1963, §53, p. 130): an $E$-bilinear multiplication $m$ on
the $E$-ification $EA = E \otimes_F A$ that extends the multiplication of $A$ ($m(1\otimes a, 1\otimes b) =
1 \otimes ab$) is the multiplication of the $E$-algebra `E ⊗[F] A`. -/
@[kb "omeara1963" "§53, p. 130 (the multiplication of EA is unique)"]
theorem mul_unique (m : E ⊗[F] A →ₗ[E] E ⊗[F] A →ₗ[E] E ⊗[F] A)
    (h : ∀ a b : A, m (1 ⊗ₜ a) (1 ⊗ₜ b) = 1 ⊗ₜ (a * b)) : m = LinearMap.mul E (E ⊗[F] A) := by
  have key : ∀ (e : E) (a : A), e ⊗ₜ[F] a = e • ((1 : E) ⊗ₜ[F] a) := fun e a => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul e a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul e' b =>
      rw [key e a, key e' b]
      simp only [map_smul, LinearMap.smul_apply, h, LinearMap.mul_apply',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, smul_smul, mul_comm e' e]

/-- **53.r11** (O'Meara 1963, §53, pp. 130-131): if $C$ is an algebra over $E$ and $f : A \to C$ is a homomorphism of
$F$-algebras (O'Meara: $C \supseteq A$ with the same identity, $f$ the inclusion), there is exactly one homomorphism of
$E$-algebras $g : EA \to C$ extending $f$ ($g(1 \otimes a) = f(a)$). -/
@[kb "omeara1963" "§53, pp. 130-131 (EA → C extending A ⊆ C, unique)"]
theorem existsUnique_algHom {C : Type*} [Ring C] [Algebra E C] [Algebra F C] [IsScalarTower F E C]
    (f : A →ₐ[F] C) : ∃! g : E ⊗[F] A →ₐ[E] C, ∀ a, g (1 ⊗ₜ a) = f a := by
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId E C) f
    (fun x y => show Commute (Algebra.ofId E C x) (f y) from Algebra.commute_algebraMap_left x (f y)),
    fun a => by rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul], fun g hg => ?_⟩
  apply Algebra.TensorProduct.ext'
  intro e a
  have he : e ⊗ₜ[F] a = e • ((1 : E) ⊗ₜ[F] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- **53.r11, consequence** (O'Meara 1963, §53, p. 131): the unique $E$-linear map between two $E$-ifications of an
algebra is an algebra isomorphism. Here: an $E$-algebra $C$ with an injective $F$-algebra map $j : A \to C$ such that
an $F$-base of $A$ is mapped to an $E$-base of $C$ (an $E$-ification of $A$ in O'Meara's sense) is isomorphic to
`E ⊗[F] A` by the extension of $j$. -/
@[kb "omeara1963" "§53, p. 131 (two E-ifications of A are isomorphic algebras)"]
theorem nonempty_algEquiv_of_basis {C : Type*} [Ring C] [Algebra E C] [Algebra F C] [IsScalarTower F E C]
    (j : A →ₐ[F] C) {ι : Type*} (b : Module.Basis ι F A) (hb : LinearIndependent E (j ∘ b))
    (hs : Submodule.span E (Set.range (j ∘ b)) = ⊤) :
    ∃ e : E ⊗[F] A ≃ₐ[E] C, ∀ a, e (1 ⊗ₜ a) = j a := by
  let g : E ⊗[F] A →ₐ[E] C :=
    Algebra.TensorProduct.lift (Algebra.ofId E C) j
      (fun x y => show Commute (Algebra.ofId E C x) (j y) from Algebra.commute_algebraMap_left x (j y))
  have hg : ∀ i, g ((b.baseChange E) i) = j (b i) := fun i => by
    simp [g, Module.Basis.baseChange_apply]
  let cb : Module.Basis ι E C := Module.Basis.mk hb (by rw [hs])
  have hbij : Function.Bijective g := by
    have : g.toLinearMap = ((b.baseChange E).equiv cb (Equiv.refl ι)).toLinearMap :=
      (b.baseChange E).ext fun i => by
        simp only [AlgHom.toLinearMap_apply, hg, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
          Equiv.refl_apply, cb, Module.Basis.mk_apply, Function.comp_apply]
    have h2 : (g : E ⊗[F] A → C) = (b.baseChange E).equiv cb (Equiv.refl ι) := by
      funext x
      exact LinearMap.congr_fun this x
    rw [h2]
    exact LinearEquiv.bijective _
  exact ⟨AlgEquiv.ofBijective g hbij, fun a => by simp [g]⟩

/-- **53.r12** (O'Meara 1963, §53, p. 131): isomorphic $F$-algebras have isomorphic $E$-ifications:
$A \cong A'$ implies $EA \cong EA'$ (as $E$-algebras). -/
@[kb "omeara1963" "§53, p. 131 (A ≅ A' implies EA ≅ EA')"]
def algEquiv_baseChange_congr {A' : Type*} [Ring A'] [Algebra F A'] (e : A ≃ₐ[F] A') :
    E ⊗[F] A ≃ₐ[E] E ⊗[F] A' :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

variable {B : Type*} [Ring B] [Algebra F B]

/-- The $E$-algebra homomorphism $EA \otimes_E EB \to E(A \otimes_F B)$, $(e \otimes a) \otimes (e' \otimes b) \mapsto
ee' \otimes (a \otimes b)$. -/
def tensorBaseChangeHom : (E ⊗[F] A) ⊗[E] (E ⊗[F] B) →ₐ[E] E ⊗[F] (A ⊗[F] B) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.map (AlgHom.id E E) Algebra.TensorProduct.includeLeft)
    (Algebra.TensorProduct.map (AlgHom.id E E) Algebra.TensorProduct.includeRight)
    (fun x y => by
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => rw [map_add]; exact hx.add_left hx'
      | tmul e a =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => rw [map_add]; exact hy.add_right hy'
        | tmul e' b =>
          simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply]
          show _ * _ = _ * _
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm e e'])

theorem tensorBaseChangeHom_eq (z : (E ⊗[F] A) ⊗[E] (E ⊗[F] B)) :
    tensorBaseChangeHom z = (TensorProduct.AlgebraTensorModule.distribBaseChange F E A B).symm z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']
    | tmul e a =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
      | tmul e' b =>
        rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
        simp [tensorBaseChangeHom, Algebra.TensorProduct.tmul_mul_tmul]

/-- **53.r13** (O'Meara 1963, §53, p. 131): $E(A_1 \otimes_F A_2) \cong (EA_1) \otimes_E (EA_2)$ as $E$-algebras
(for $F$-algebras $A_1, A_2$), by $e \otimes (a_1 \otimes a_2) \mapsto (e \otimes a_1) \otimes (1 \otimes a_2)$. The
$r$-fold statement follows by induction; it is used in this form for the Hasse algebra
(`nonempty_algEquiv_baseChange_hasseAlg`). -/
@[kb "omeara1963" "§53, p. 131 (E(A₁ ⊗ A₂) ≅ EA₁ ⊗_E EA₂)"]
def algEquiv_baseChange_tensor : E ⊗[F] (A ⊗[F] B) ≃ₐ[E] (E ⊗[F] A) ⊗[E] (E ⊗[F] B) :=
  (AlgEquiv.ofBijective (tensorBaseChangeHom (F := F) (E := E) (A := A) (B := B)) (by
    have h : (tensorBaseChangeHom (F := F) (E := E) (A := A) (B := B) : _ → _) =
        (TensorProduct.AlgebraTensorModule.distribBaseChange F E A B).symm := funext tensorBaseChangeHom_eq
    rw [h]
    exact LinearEquiv.bijective _)).symm

end Alg

section Iterated

open Tensor51

universe w

variable {F : Type w} [Field F] {E : Type w} [Field E] [Algebra F E]

theorem tprodList_concat (l : List (AlgCat.{w} F)) (A : AlgCat.{w} F) :
    tprodList (l ++ [A]) = AlgCat.of F (↥(tprodList l) ⊗[F] ↥A) := by
  unfold tprodList
  rw [List.foldl_append]
  rfl

/-- **53.r13, $r$ factors** (O'Meara 1963, §53, p. 131): $E(A_1 \otimes_F \cdots \otimes_F A_r) \cong
EA_1 \otimes_E \cdots \otimes_E EA_r$, with the iterated tensor products `Tensor51.tprodList` of §51 (over $F$ on
the left, over $E$ on the right). -/
@[kb "omeara1963" "§53, p. 131 (E(⊗ A_i) ≅ ⊗ EA_i)"]
theorem nonempty_algEquiv_baseChange_tprodList (l : List (AlgCat.{w} F)) :
    Nonempty (E ⊗[F] ↥(tprodList l) ≃ₐ[E]
      ↥(tprodList (l.map fun A : AlgCat.{w} F => AlgCat.of E (E ⊗[F] ↥A)))) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨Algebra.TensorProduct.rid F E E⟩
  | append_singleton l A ih =>
    obtain ⟨e⟩ := ih
    rw [List.map_append, List.map_singleton, tprodList_concat, tprodList_concat]
    exact ⟨(algEquiv_baseChange_tensor (A := ↥(tprodList l)) (B := ↥A)).trans
      (Algebra.TensorProduct.congr e AlgEquiv.refl)⟩

end Iterated

end QuadFormsKB.OMeara.Base53

namespace QuadFormsKB.OMeara.Hasse58

open CSA52 Base53

universe u

/-! ### 58:3: $S(EV) \cong E\,S(V)$ -/

section BaseChange

variable {F : Type u} [Field F] [Invertible (2 : F)] {E : Type u} [Field E] [Algebra F E] [Invertible (2 : E)]

/-- The image of a unit of $F$ in $E$. -/
abbrev uE (E : Type u) [Field E] [Algebra F E] : Fˣ →* Eˣ := Units.map (algebraMap F E : F →* E)

/-- $(\alpha,\beta)$ over $E$ depends only on the values of $\alpha, \beta$. -/
def quatCongr {a b a' b' : E} (ha : a = a') (hb : b = b') : ℍ[E,a,b] ≃ₐ[E] ℍ[E,a',b'] := by
  subst ha hb; exact AlgEquiv.refl

theorem nonempty_algEquiv_baseChange_qs (a b : Fˣ) :
    Nonempty (E ⊗[F] (qs a b) ≃ₐ[E] qs (uE E a) (uE E b)) :=
  ⟨(QuatBase57.algEquiv_baseChange (E := E) (a : F) (b : F)).trans (quatCongr rfl rfl)⟩

theorem nonempty_algEquiv_baseChange_rev (l : List Fˣ) :
    Nonempty (E ⊗[F] (Rev.hasseAlg l) ≃ₐ[E] Rev.hasseAlg (l.map (uE E))) := by
  induction l with
  | nil => exact ⟨Algebra.TensorProduct.rid F E E⟩
  | cons x l ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨q⟩ := nonempty_algEquiv_baseChange_qs (E := E) x (x :: l).prod
    have hp : uE E (x :: l).prod = ((x :: l).map (uE E)).prod := by rw [List.prod_hom]
    have e1 : E ⊗[F] (Rev.hasseAlg (x :: l)) ≃ₐ[E] (E ⊗[F] (qs x (x :: l).prod)) ⊗[E]
        (E ⊗[F] (Rev.hasseAlg l)) :=
      algEquiv_baseChange_tensor (A := qs x (x :: l).prod) (B := Rev.hasseAlg l)
    have e2 : (E ⊗[F] (qs x (x :: l).prod)) ⊗[E] (E ⊗[F] (Rev.hasseAlg l)) ≃ₐ[E]
        (qs (uE E x) ((x :: l).map (uE E)).prod) ⊗[E] (Rev.hasseAlg (l.map (uE E))) :=
      Algebra.TensorProduct.congr (q.trans (quatCongr rfl (by rw [hp]))) e
    exact ⟨e1.trans e2⟩

/-- **O'Meara 58:3, extension of scalars, algebraic form** (§58, p. 152): for a field extension $E/F$ and values
$a_0, \dots, a_{n-1} \in F^\times$, $E\bigl(\bigotimes_i (a_i, d_i)_F\bigr) \cong \bigotimes_i (a_i, d_i)_E$, i.e. the
$E$-ification of the Hasse algebra of the values is the Hasse algebra over $E$ of the same values. (By 53.r13 and
57.r3: `algEquiv_baseChange_tensor`, `QuatBase57.algEquiv_baseChange`.) `Invertible (2 : E)` is automatic and
only needed to form the Hasse algebra over $E$. -/
@[kb "omeara1963" "§58, 58:3, p. 152 (S(EV) ≅ E S(V), algebraic form)"]
theorem nonempty_algEquiv_baseChange_hasseAlg (a : List Fˣ) :
    Nonempty (E ⊗[F] (hasseAlg a) ≃ₐ[E] hasseAlg (a.map (uE E))) := by
  obtain ⟨e⟩ := nonempty_algEquiv_baseChange_rev (E := E) a.reverse
  refine ⟨e.trans ?_⟩
  rw [List.map_reverse]
  exact AlgEquiv.refl

open Sp58 Class58 in
/-- **O'Meara 58:3, extension of scalars** (§58, p. 152): *the behaviour under $E$-ification is described by
$S(EV) \cong E\,S(V)$.* For a regular quadratic space $V$ over $F$ with an orthogonal base $X$ and any orthogonal base
$Y$ of the $E$-ification $EV = E \otimes_F V$ (with the base-changed form, regular as well), the Hasse algebra of $EV$
computed with $Y$ is $E$-isomorphic to $E \otimes_F S(V)$, with $S(V)$ computed with $X$. (Proof: $1 \otimes X$ is an
orthogonal base of $EV$ whose values are the images of those of $X$; 58:2 over $E$ and the algebraic form
`nonempty_algEquiv_baseChange_hasseAlg`.) -/
@[kb "omeara1963" "§58, 58:3, p. 152 (S(EV) ≅ E S(V))"]
theorem nonempty_algEquiv_hasseAlg_baseChange {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X : Module.Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X)
    (hQE : (QuadraticMap.associated (Q.baseChange E)).Nondegenerate)
    (Y : Module.Basis (Fin n) E (E ⊗[F] V)) (hY : IsOrthogonalBasis (Q.baseChange E) Y) :
    Nonempty (hasseAlg (Rev.values hQE Y hY) ≃ₐ[E] E ⊗[F] hasseAlg (Rev.values hQ X hX)) := by
  have hbil : ∀ i j, bil (Q.baseChange E) ((X.baseChange E) i) ((X.baseChange E) j) =
      algebraMap F E (bil Q (X i) (X j)) := fun i j => by
    simp only [bil, Module.Basis.baseChange_apply, QuadraticForm.associated_baseChange,
      LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
  have hXE : IsOrthogonalBasis (Q.baseChange E) (X.baseChange E) := fun i j hij => by
    rw [hbil, hX i j hij, map_zero]
  have hv : Rev.values hQE (X.baseChange E) hXE = (Rev.values hQ X hX).map (uE E) := by
    simp only [Rev.values, List.map_ofFn]
    congr 1
    funext i
    apply Units.ext
    simp [Module.Basis.baseChange_apply, QuadraticForm.baseChange_tmul, Algebra.smul_def]
  obtain ⟨e1⟩ := nonempty_algEquiv_hasseAlg_values hQE Y (X.baseChange E) hY hXE
  obtain ⟨e2⟩ := nonempty_algEquiv_baseChange_hasseAlg (E := E) (Rev.values hQ X hX)
  refine ⟨e1.trans (AlgEquiv.trans ?_ e2.symm)⟩
  rw [hv]

end BaseChange

/-! ### 58:3: the ternary and quaternary rules as printed -/

section Printed

variable {F : Type u} [Field F] [Invertible (2 : F)]

/-- $(x, -xy) \sim (x, y)$ (57:10 (3) with 57:11). -/
theorem B_neg_mul_right (x y : Fˣ) : B x (-x * y) = B x y := by
  rw [neg_mul, neg_eq_neg_one_mul (x * y), B_mul_right, B_mul_right, B_self, B_sq_mul]

theorem B_neg_mul_left (a b c : Fˣ) : B (-(a * b)) (-(a * c)) = B (-(a * b)) (-(b * c)) := by
  rw [← B_neg_mul_right (-(a * b)) (-(a * c))]
  have h : -(-(a * b)) * -(a * c) = a ^ 2 * -(b * c) := by
    ext; simp; ring
  rw [h, B_sq_mul_right]

/-- **O'Meara 58:3, ternary spaces, as printed** (§58, p. 152, read from the page image): for a ternary space with
an orthogonal base of values $a_0, a_1, a_2$ (0-based; the book's $\alpha_1, \alpha_2, \alpha_3$),
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_0a_2).$$
The library's `isBrauerEquivalent_hasseAlg_ternary` has the equivalent right-hand side $(-a_0a_1, -a_1a_2)$
(reconstructed before the page image was available); the two agree since $(x, y) \sim (x, -xy)$. -/
@[kb "omeara1963" "§58, 58:3, p. 152 (ternary: (-1,-1) ⊗ SV ~ (-α₁α₂, -α₁α₃))"]
theorem isBrauerEquivalent_hasseAlg_ternary_printed (a b c : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c])) (qs (-(a * b)) (-(a * c))) := by
  refine (isBrauerEquivalent_hasseAlg_ternary a b c).trans (cls_eq_iff.1 ?_)
  exact (B_neg_mul_left a b c).symm

/-- **O'Meara 58:3, quaternary spaces, as printed** (§58, p. 152, read from the page image): for a quaternary space
with an orthogonal base of values $a_0, \dots, a_3$ (the book's $\alpha_1, \dots, \alpha_4$) and $dV = a_0a_1a_2a_3$,
$$(-1,-1) \otimes S V \sim (-a_0a_1,\ -a_0a_2) \otimes (a_3, dV).$$ -/
@[kb "omeara1963" "§58, 58:3, p. 152 (quaternary: (-1,-1) ⊗ SV ~ (-α₁α₂, -α₁α₃) ⊗ (α₄, dV))"]
theorem isBrauerEquivalent_hasseAlg_quaternary_printed (a b c d : Fˣ) :
    IsBrauerEquivalent (tensor (qs (-1) (-1)) (hasseAlg [a, b, c, d]))
      (tensor (qs (-(a * b)) (-(a * c))) (qs d (a * b * c * d))) := by
  refine (isBrauerEquivalent_hasseAlg_quaternary a b c d).trans (cls_eq_iff.1 ?_)
  show B _ _ * B _ _ = B _ _ * B _ _
  rw [B_neg_mul_left]

end Printed

end QuadFormsKB.OMeara.Hasse58
