/-
# Similar ternary forms have isomorphic even Clifford algebras (Voight, Theorem 22.2.11)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Lemma 5.3.21 and
Theorem 22.2.11 (key `voight2021`).

**Statement.** Two ternary quadratic forms $Q, Q'$ over a commutative ring $R$ are *similar* if
$Q'(\vec x) = c\,Q(P\vec x)$ for some $P \in \mathrm{GL}_3(R)$ and $c \in R^\times$ (`Similar`, Voight 22.1).
Voight's Theorem 22.2.11 says that $Q \mapsto \operatorname{Clf}^0(Q)$ is a functor from quadratic modules
under similarities to $R$-algebras; in particular similar forms have isomorphic even Clifford algebras
(`nonempty_clf0_equiv_of_similar`). This is the "if" direction of the bijection in Main Theorem 22.4.1.

**Proof.** An isometry $e : Q_1 \to Q_2$ of Mathlib quadratic forms induces an isomorphism of even Clifford
algebras (`evenEquivOfIsometry`, via `CliffordAlgebra.even.lift`: the products
$\iota(e\,m)\iota(e\,n)$ satisfy the defining relations of the even Clifford algebra); combined with the
identification `clf0EquivEven` of Voight's table algebra with Mathlib's even Clifford algebra, this handles
the change of variables $P$, and `clf0SmulEquiv` handles the rescaling by $c$. No hypothesis on $R$.

Indices are 0-based (Voight's $e_1, e_2, e_3$ are $e_0, e_1, e_2$).
-/
import QuadFormsKB.Literature.Voight.EvenCliffordMathlib
import QuadFormsKB.Literature.Voight.Correspondence

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Voight

open CliffordAlgebra

section Iso

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The `EvenHom` $(m, n) \mapsto \iota(f m)\,\iota(f n)$ into the even Clifford algebra of $Q_2$, for a
linear map $f$ with $Q_2(f m) = Q_1(m)$. -/
def evenHomOfLinear (f : M₁ →ₗ[R] M₂) (hf : ∀ m, Q₂ (f m) = Q₁ m) :
    CliffordAlgebra.EvenHom Q₁ (CliffordAlgebra.even Q₂) where
  bilin := ((even.ι Q₂).bilin.compl₂ f).comp f
  contract m := by
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply]
    rw [(even.ι Q₂).contract, hf]
  contract_mid m₁ m₂ m₃ := by
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply]
    rw [(even.ι Q₂).contract_mid, hf]

/-- The algebra map $\operatorname{Clf}^0(Q_1) \to \operatorname{Clf}^0(Q_2)$ induced by a linear map
$f$ with $Q_2 \circ f = Q_1$: $\iota(m)\iota(n) \mapsto \iota(f m)\iota(f n)$. -/
noncomputable def evenMapOfLinear (f : M₁ →ₗ[R] M₂) (hf : ∀ m, Q₂ (f m) = Q₁ m) :
    CliffordAlgebra.even Q₁ →ₐ[R] CliffordAlgebra.even Q₂ :=
  even.lift Q₁ (evenHomOfLinear f hf)

theorem evenMapOfLinear_ι (f : M₁ →ₗ[R] M₂) (hf : ∀ m, Q₂ (f m) = Q₁ m) (m n : M₁) :
    evenMapOfLinear f hf ((even.ι Q₁).bilin m n) = (even.ι Q₂).bilin (f m) (f n) :=
  even.lift_ι Q₁ _ m n

/-- **The even Clifford algebra is functorial for isometries** (Voight 2021, Lemma 5.3.21): an
isometry $e : Q_1 \xrightarrow{\sim} Q_2$ of quadratic forms over any commutative ring induces an
$R$-algebra isomorphism $\operatorname{Clf}^0(Q_1) \cong \operatorname{Clf}^0(Q_2)$ of Mathlib's even Clifford
algebras, with $\iota(m)\iota(n) \mapsto \iota(e\,m)\,\iota(e\,n)$. -/
@[kb "voight2021" "Lemma 5.3.21, p. 72"]
noncomputable def evenEquivOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    CliffordAlgebra.even Q₁ ≃ₐ[R] CliffordAlgebra.even Q₂ :=
  AlgEquiv.ofAlgHom (evenMapOfLinear e.toLinearEquiv.toLinearMap e.map_app)
    (evenMapOfLinear e.symm.toLinearEquiv.toLinearMap e.symm.map_app)
    (by
      apply even.algHom_ext
      apply CliffordAlgebra.EvenHom.ext
      refine LinearMap.ext₂ fun m n => ?_
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply]
      have h1 := evenMapOfLinear_ι e.symm.toLinearEquiv.toLinearMap e.symm.map_app m n
      have h2 := evenMapOfLinear_ι e.toLinearEquiv.toLinearMap e.map_app
        (e.symm.toLinearEquiv m) (e.symm.toLinearEquiv n)
      rw [h1]
      refine h2.trans ?_
      congr 2 <;> exact (e.toLinearEquiv.apply_symm_apply _))
    (by
      apply even.algHom_ext
      apply CliffordAlgebra.EvenHom.ext
      refine LinearMap.ext₂ fun m n => ?_
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin, LinearMap.compr₂_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply]
      have h1 := evenMapOfLinear_ι e.toLinearEquiv.toLinearMap e.map_app m n
      have h2 := evenMapOfLinear_ι e.symm.toLinearEquiv.toLinearMap e.symm.map_app
        (e.toLinearEquiv m) (e.toLinearEquiv n)
      rw [h1]
      refine h2.trans ?_
      congr 2 <;> exact (e.toLinearEquiv.symm_apply_apply _))

end Iso

section Clf0

variable {R : Type*} [CommRing R]

/-- **Isometric ternary forms have isomorphic even Clifford algebras**: if $Q(P\vec x) = Q'(\vec x)$ for
some $P \in \mathrm{GL}_3(R)$ (`QuadForm.IsometricIn R Q Q'`), then
$\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$. -/
theorem clf0EquivOfIsometricIn {Q Q' : QuadForm R 3} (h : Q.IsometricIn R Q') :
    Nonempty (Clf0 Q ≃ₐ[R] Clf0 Q') := by
  obtain ⟨P, hP, hPQ⟩ := h
  let hinv := P.invertibleOfIsUnitDet hP
  let e : Q'.toQuadraticForm.IsometryEquiv Q.toQuadraticForm :=
    { Matrix.toLinearEquiv' P hinv with
      map_app' := fun x => by
        simp only [QuadForm.toQuadraticForm_apply]
        exact hPQ x }
  exact ⟨(clf0EquivEven Q).trans ((evenEquivOfIsometry e).symm.trans (clf0EquivEven Q').symm)⟩

/-- **Similar ternary forms have isomorphic even Clifford algebras** (Voight 2021, Theorem 22.2.11:
$Q \mapsto \operatorname{Clf}^0(Q)$ is a functor from quadratic modules under similarities to algebras;
over $R^3$ a similarity is $Q'(\vec x) = c\,Q(P\vec x)$ with $P \in \mathrm{GL}_3(R)$, $c \in R^\times$).
For every commutative ring $R$ and ternary forms $Q, Q'$ over $R$: if $Q$ and $Q'$ are similar then
$\operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q')$ as $R$-algebras. This is the "if" direction of
`EvenCliffordCorrespondence.nonempty_equiv_iff_similar` (Main Theorem 22.4.1), with no hypothesis on $R$. -/
@[kb "voight2021" "Theorem 22.2.11, p. 357"]
theorem nonempty_clf0_equiv_of_similar {Q Q' : QuadForm R 3} (h : Similar Q Q') :
    Nonempty (Clf0 Q ≃ₐ[R] Clf0 Q') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨e⟩ := clf0EquivOfIsometricIn hc
  exact ⟨(clf0SmulEquiv c Q).symm.trans e⟩

end Clf0

end QuadFormsKB.Voight
