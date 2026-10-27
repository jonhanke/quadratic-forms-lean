/-
# O'Meara §52B–§52F: minimal left ideals and Wedderburn's theorem (52:3, 52:4, 52:7, 52:8, 52:9)

**Setting.** $F$ is a field; an *algebra* is a finite-dimensional associative $F$-algebra with identity
(`[Ring A] [Algebra F A] [FiniteDimensional F A]`); *central simple* means
`Algebra.IsCentral F A ∧ IsSimpleRing A`; a *division algebra over $F$* is
`[DivisionRing D] [Algebra F D] [FiniteDimensional F D]`. A *minimal left ideal* of $A$ is an atom
`IsAtom a` of the lattice `Submodule A A` of left ideals (equivalently `IsSimpleModule A a`).

**Convention for $R_A(\mathfrak a)$.** O'Meara (p. 120) writes $A$-linear maps $\mathfrak a \to \mathfrak a$ on the
*right* of their argument, so that $x(\varphi\psi) = (x\varphi)\psi$; his $R_A(\mathfrak a)$ is therefore the
endomorphism algebra with the *opposite* multiplication of composition. Here $R_A(\mathfrak a)$ is
`(Module.End A a)ᵐᵒᵖ`, where `Module.End A a` carries composition $(f g)(x) = f(g(x))$ and the $F$-algebra
structure $(c f)(x) = c\,f(x)$. Statements that are insensitive to the opposite (invertibility, existence of an
isomorphism of algebras between the endomorphism algebras of two ideals) are given for `Module.End A a` itself.

**Reuse of Mathlib.** Schur's lemma (`Module.End.instDivisionRing`, `LinearMap.bijective_of_ne_zero`), the
Wedderburn–Artin theorem (`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`), the isotypic property of
simple Artinian rings (`IsSimpleRing.isIsotypic`), `matrixEquivTensor`, `Matrix.compAlgEquiv`, and
`IsBrauerEquivalent`. Nothing of these is redefined.

**Proves**
* `isUnit_or_eq_zero_of_isAtom`, `minimalLeftIdealDivisionRing`, `finiteDimensional_endMulOpposite` (**52:3**):
  for a minimal left ideal $\mathfrak a$, $R_A(\mathfrak a)$ is a division algebra over $F$;
* `nonempty_linearEquiv_of_isAtom`, `nonempty_algEquiv_end_of_isAtom` (**52:4**): two minimal left ideals of a
  simple algebra are isomorphic as $A$-modules, hence their endomorphism algebras are isomorphic;
* `nonempty_matrix_tensor_algEquiv_matrix` (**52:7**): $M_n(F)\otimes_F D \cong M_n(D)$;
* `isCentral_of_algEquiv_matrix`, `nonempty_algEquiv_of_algEquiv_matrix`, `eq_of_algEquiv_matrix`
  (combined: `omeara_52_8`) (**52:8**): if $A$ is central simple and $A \cong M_n(D)$ with $D$ a division algebra,
  then $D$ is central, $n$ is unique and $D$ is unique up to isomorphism;
* `exists_algEquiv_matrix_tensor_division` and `unique_algEquiv_matrix_tensor_division` (**52:9**, Wedderburn);
* `isBrauerEquivalent_iff_nonempty_algEquiv`, `isBrauerEquivalent_iff_tensor`,
  `splits_iff_nonempty_algEquiv_base` (**§52F**): O'Meara's similarity of central simple algebras is Mathlib's
  `IsBrauerEquivalent`; splitting is isomorphism of the division algebra component with $F$.

Auxiliary (untagged): `nonempty_linearEquiv_of_isSimpleModule`, `vecEndAlgEquiv` ($\mathrm{End}_{M_n(D)}(D^n)
\cong D^{op}$), `endAlgEquivOfSMul`, `exists_isAtom_end_algEquiv`, `matrixMatrixAlgEquiv`.
-/
import Mathlib
import QuadFormsKB.Citation

open scoped TensorProduct
open Module

set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace QuadFormsKB.OMeara

section MinimalLeftIdeal

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- **52:3, invertibility** (O'Meara 1973, §52B, p. 121): if $\mathfrak a$ is a minimal left ideal of an algebra $A$,
every $A$-linear map $\varphi : \mathfrak a \to \mathfrak a$ is either $0$ or invertible (Schur's lemma). -/
@[kb "omeara1963" "§52B, 52:3, p. 121"]
theorem isUnit_or_eq_zero_of_isAtom {a : Submodule A A} (ha : IsAtom a) (f : Module.End A a) :
    IsUnit f ∨ f = 0 := by
  classical
  have : IsSimpleModule A a := isSimpleModule_iff_isAtom.2 ha
  by_cases h : f = 0
  · exact Or.inr h
  · exact Or.inl (isUnit_iff_ne_zero.2 h)

/-- **52:3, the division ring** (O'Meara 1973, §52B, p. 121): $R_A(\mathfrak a) = (\mathrm{End}_A\,\mathfrak a)^{op}$
is a division ring for a minimal left ideal $\mathfrak a$; the underlying ring is the one of `Module.End A a`
(with the opposite multiplication). -/
@[kb "omeara1963" "§52B, 52:3, p. 121", instance_reducible]
def minimalLeftIdealDivisionRing {a : Submodule A A} (ha : IsAtom a) :
    DivisionRing (Module.End A a)ᵐᵒᵖ :=
  have : IsSimpleModule A a := isSimpleModule_iff_isAtom.2 ha
  have : Nontrivial (Module.End A a) := by
    classical
    exact (inferInstance : DivisionRing (Module.End A a)).toNontrivial
  DivisionRing.ofIsUnitOrEqZero fun f => by
    rcases isUnit_or_eq_zero_of_isAtom ha f.unop with h | h
    · exact Or.inl (by have := h.op; rwa [MulOpposite.op_unop] at this)
    · exact Or.inr (MulOpposite.unop_injective (by simpa using h))

/-- **52:3, finite dimension** (O'Meara 1973, §52B, p. 121): $R_A(\mathfrak a)$ is finite dimensional over $F$ when
$A$ is, so with `minimalLeftIdealDivisionRing` it is a division algebra over $F$. -/
@[kb "omeara1963" "§52B, 52:3, p. 121"]
instance finiteDimensional_endMulOpposite [FiniteDimensional F A] (a : Submodule A A) :
    FiniteDimensional F (Module.End A a)ᵐᵒᵖ := by
  have : FiniteDimensional F (Module.End A a) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ F A a a F)
      (LinearMap.restrictScalars_injective F)
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv F)

end MinimalLeftIdeal

section Simple

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- Any two simple modules over a simple Artinian ring are isomorphic. This is the module form of O'Meara's 52:4
(the case of two minimal left ideals is `nonempty_linearEquiv_of_isAtom`), and follows from Mathlib's
`IsSimpleRing.isIsotypic` applied to $S \times T$. -/
theorem nonempty_linearEquiv_of_isSimpleModule [IsSimpleRing A] [IsArtinianRing A]
    (S : Type*) [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (T : Type*) [AddCommGroup T] [Module A T] [IsSimpleModule A T] :
    Nonempty (S ≃ₗ[A] T) := by
  have h := IsSimpleRing.isIsotypic A (S × T)
  let e1 : S ≃ₗ[A] LinearMap.range (LinearMap.inl A S T) :=
    LinearEquiv.ofInjective _ LinearMap.inl_injective
  let e2 : T ≃ₗ[A] LinearMap.range (LinearMap.inr A S T) :=
    LinearEquiv.ofInjective _ LinearMap.inr_injective
  have : IsSimpleModule A (LinearMap.range (LinearMap.inl A S T)) := IsSimpleModule.congr e1.symm
  have : IsSimpleModule A (LinearMap.range (LinearMap.inr A S T)) := IsSimpleModule.congr e2.symm
  obtain ⟨e⟩ := h (LinearMap.range (LinearMap.inl A S T)) (LinearMap.range (LinearMap.inr A S T))
  exact ⟨e1.trans (e.symm.trans e2.symm)⟩

/-- **52:4, first part** (O'Meara 1973, §52B, p. 121): any two minimal left ideals $\mathfrak a, \mathfrak b$ of a
simple algebra $A$ are isomorphic as $A$-modules, i.e. there is an $A$-linear bijection $\mathfrak a \to \mathfrak b$. -/
@[kb "omeara1963" "§52B, 52:4, p. 121"]
theorem nonempty_linearEquiv_of_isAtom [FiniteDimensional F A] [IsSimpleRing A]
    {a b : Submodule A A} (ha : IsAtom a) (hb : IsAtom b) : Nonempty (a ≃ₗ[A] b) := by
  have := IsArtinianRing.of_finite F A
  have := isSimpleModule_iff_isAtom.2 ha
  have := isSimpleModule_iff_isAtom.2 hb
  exact nonempty_linearEquiv_of_isSimpleModule a b

/-- **52:4, second part** (O'Meara 1973, §52B, p. 121): for minimal left ideals $\mathfrak a, \mathfrak b$ of a simple
algebra $A$, the endomorphism algebras $\mathrm{End}_A\,\mathfrak a$ and $\mathrm{End}_A\,\mathfrak b$ are isomorphic
as $F$-algebras (conjugation by an $A$-linear bijection). Taking opposites gives the isomorphism
$R_A(\mathfrak a) \cong R_A(\mathfrak b)$ (see `nonempty_algEquiv_endMulOpposite_of_isAtom`). -/
@[kb "omeara1963" "§52B, 52:4, p. 121"]
theorem nonempty_algEquiv_end_of_isAtom [FiniteDimensional F A] [IsSimpleRing A]
    {a b : Submodule A A} (ha : IsAtom a) (hb : IsAtom b) :
    Nonempty (Module.End A a ≃ₐ[F] Module.End A b) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_isAtom (F := F) ha hb
  exact ⟨e.conjAlgEquiv F⟩

/-- **52:4, second part, in O'Meara's notation**: $R_A(\mathfrak a) \cong R_A(\mathfrak b)$ as $F$-algebras. -/
@[kb "omeara1963" "§52B, 52:4, p. 121"]
theorem nonempty_algEquiv_endMulOpposite_of_isAtom [FiniteDimensional F A] [IsSimpleRing A]
    {a b : Submodule A A} (ha : IsAtom a) (hb : IsAtom b) :
    Nonempty ((Module.End A a)ᵐᵒᵖ ≃ₐ[F] (Module.End A b)ᵐᵒᵖ) := by
  obtain ⟨e⟩ := nonempty_algEquiv_end_of_isAtom (F := F) ha hb
  exact ⟨AlgEquiv.op e⟩

end Simple

section MatrixModule

variable {F : Type*} [Field F] {D : Type*} [DivisionRing D] [Algebra F D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The column space $D^\iota$ is a simple module over the matrix ring $M_\iota(D)$ of a division ring $D$
(O'Meara's minimal left ideal "all columns but the first vanish", p. 124, seen as a module). -/
theorem isSimpleModule_matrix_vec [Nonempty ι] : IsSimpleModule (Matrix ι ι D) (ι → D) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun v hv w => ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  refine ⟨Matrix.of fun j k => if k = i then w j * (v i)⁻¹ else 0, ?_⟩
  ext j
  simp only [Pi.zero_apply] at hi
  simp [LinearMap.toSpanSingleton_apply, Matrix.mulVec, dotProduct, hi]

/-- Right multiplication of column vectors by an element of $D$ is $M_\iota(D)$-linear; as $R_A(\mathfrak a)$ is
the *opposite* of the endomorphism ring, it is naturally indexed by $D^{op}$. -/
def vecRightMul (d : Dᵐᵒᵖ) : Module.End (Matrix ι ι D) (ι → D) where
  toFun v := fun i => v i * d.unop
  map_add' v w := by ext; simp [add_mul]
  map_smul' M v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- `vecRightMul` as an $F$-algebra homomorphism $D^{op} \to \mathrm{End}_{M_\iota(D)}(D^\iota)$. -/
def vecRightMulAlgHom : Dᵐᵒᵖ →ₐ[F] Module.End (Matrix ι ι D) (ι → D) where
  toFun := vecRightMul
  map_one' := by ext; simp [vecRightMul]
  map_mul' d e := by ext v i; simp [vecRightMul, mul_assoc]
  map_zero' := by ext; simp [vecRightMul]
  map_add' d e := by ext v i; simp [vecRightMul, mul_add]
  commutes' c := by
    ext v i
    simp [vecRightMul, Algebra.smul_def, Algebra.commutes]

theorem vecRightMulAlgHom_bijective [Nonempty ι] :
    Function.Bijective (vecRightMulAlgHom (F := F) (D := D) (ι := ι)) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  constructor
  · rw [injective_iff_map_eq_zero]
    intro d hd
    have := congrArg (fun f : Module.End (Matrix ι ι D) (ι → D) => f (Pi.single i₀ 1) i₀) hd
    simpa [vecRightMulAlgHom, vecRightMul] using this
  · intro f
    refine ⟨MulOpposite.op (f (Pi.single i₀ 1) i₀), ?_⟩
    ext v k
    have key : f v = (Matrix.of fun j l => if l = i₀ then v j else 0) • f (Pi.single i₀ 1) := by
      rw [← map_smul]
      congr 1
      ext j
      simp [Matrix.mulVec, dotProduct]
    simp [vecRightMulAlgHom, vecRightMul, key, Matrix.mulVec, dotProduct]

/-- The endomorphism algebra $\mathrm{End}_{M_\iota(D)}(D^\iota)$ is $D^{op}$ (the step "$R_{A'}(\mathfrak a')
\cong D$" of O'Meara's proof of 52:8, p. 124). -/
noncomputable def vecEndAlgEquiv [Nonempty ι] :
    Dᵐᵒᵖ ≃ₐ[F] Module.End (Matrix ι ι D) (ι → D) :=
  AlgEquiv.ofBijective vecRightMulAlgHom vecRightMulAlgHom_bijective

end MatrixModule

section Transport

variable {F : Type*} [Field F] {A B N : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  [AddCommGroup N] [Module A N] [Module B N] [Module F N] [SMulCommClass A F N]
  [SMulCommClass B F N] [IsScalarTower F A N] [IsScalarTower F B N]

/-- If the $A$-module structure on $N$ is the restriction of a $B$-module structure along a ring isomorphism
$e : A \to B$, the endomorphism algebras agree. -/
def endAlgEquivOfSMul (e : A ≃ₐ[F] B) (h : ∀ (a : A) (x : N), a • x = e a • x) :
    Module.End A N ≃ₐ[F] Module.End B N where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b x => by
        obtain ⟨a, rfl⟩ := e.surjective b
        simp [← h] }
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a x => by
        simp [h] }
  left_inv f := rfl
  right_inv g := rfl
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

theorem isSimpleModule_of_smul (e : A ≃+* B) (h : ∀ (a : A) (x : N), a • x = e a • x)
    [IsSimpleModule B N] : IsSimpleModule A N := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨IsSimpleModule.nontrivial B N, fun v hv w => ?_⟩
  obtain ⟨b, hb⟩ := (isSimpleModule_iff_toSpanSingleton_surjective.1 ‹IsSimpleModule B N›).2 v hv w
  obtain ⟨a, rfl⟩ := e.surjective b
  exact ⟨a, by simpa [h] using hb⟩

end Transport

section MatrixAtom

variable {F : Type*} [Field F] {D : Type*} [DivisionRing D] [Algebra F D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [Ring A] [Algebra F A]

/-- If a finite-dimensional algebra $A$ is isomorphic to $M_\iota(D)$ ($D$ a division ring, $\iota \ne \emptyset$),
then some minimal left ideal $\mathfrak a$ of $A$ has $\mathrm{End}_A\,\mathfrak a \cong D^{op}$ (that is,
$R_A(\mathfrak a) \cong D$ in O'Meara's notation). This is O'Meara's step 3) in the proof of 52:8, p. 124; the
column module $D^\iota$ is transported along the isomorphism and compared with a minimal left ideal using
`nonempty_linearEquiv_of_isSimpleModule`. -/
theorem exists_isAtom_end_algEquiv [Nonempty ι] [FiniteDimensional F A]
    (e : A ≃ₐ[F] Matrix ι ι D) :
    ∃ a : Submodule A A, IsAtom a ∧ Nonempty (Module.End A a ≃ₐ[F] Dᵐᵒᵖ) := by
  have hA : IsSimpleRing A := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  let : Module A (ι → D) := Module.compHom _ (e : A →+* Matrix ι ι D)
  have hs : ∀ (a : A) (x : ι → D), a • x = e a • x := fun _ _ => rfl
  have : SMulCommClass A F (ι → D) := ⟨fun a c x => smul_comm (e a) c x⟩
  have : IsSimpleModule A (ι → D) := by
    have := isSimpleModule_matrix_vec (D := D) (ι := ι)
    exact isSimpleModule_of_smul e.toRingEquiv hs
  have : Nontrivial A := e.toRingEquiv.toEquiv.nontrivial
  obtain ⟨a, ha⟩ := IsAtomic.exists_atom (Submodule A A)
  have : IsSimpleModule A a := isSimpleModule_iff_isAtom.2 ha
  obtain ⟨φ⟩ := nonempty_linearEquiv_of_isSimpleModule (A := A) a (ι → D)
  have : IsScalarTower F A (ι → D) :=
    ⟨fun c a x => by
      show (e (c • a)) • x = c • (e a • x)
      rw [map_smul]
      exact smul_assoc c (e a) x⟩
  exact ⟨a, ha, ⟨((φ.conjAlgEquiv F).trans (endAlgEquivOfSMul e hs)).trans
    (vecEndAlgEquiv (F := F) (D := D) (ι := ι)).symm⟩⟩

end MatrixAtom

section Wedderburn

variable {F : Type*} [Field F]

/-- **52:7** (O'Meara 1973, §52C, p. 123): $M_n(F) \otimes_F D \cong M_n(D)$ as $F$-algebras.

*Update:* O'Meara assumes that $D$ is a central division algebra over $F$ (his proof goes through 52:2); the
isomorphism holds, and is proved here (from `matrixEquivTensor` and the commutativity of the tensor product), for
every $F$-algebra $D$, with no hypothesis on $D$. -/
@[kb "omeara1963" "§52C, 52:7, p. 123"]
theorem nonempty_matrix_tensor_algEquiv_matrix (n : ℕ) (D : Type*) [Ring D] [Algebra F D] :
    Nonempty (Matrix (Fin n) (Fin n) F ⊗[F] D ≃ₐ[F] Matrix (Fin n) (Fin n) D) :=
  ⟨(Algebra.TensorProduct.comm F _ _).trans (matrixEquivTensor (Fin n) F D).symm⟩

section Unique

variable {A : Type*} [Ring A] [Algebra F A]
variable {D : Type*} [DivisionRing D] [Algebra F D] {D' : Type*} [DivisionRing D'] [Algebra F D']
variable {n m : ℕ}

private theorem nonempty_fin_of_neZero (n : ℕ) [NeZero n] : Nonempty (Fin n) :=
  ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩

/-- **52:8, centre of $D$** (O'Meara 1973, §52C, p. 123): if the algebra $A$ is central and isomorphic to $M_n(D)$
for a division algebra $D$ ($n \ge 1$), then $D$ is central. (O'Meara's proof: for $d$ in the centre of $D$, the
scalar matrix $d \cdot 1$ is central in $M_n(D)$.) -/
@[kb "omeara1963" "§52C, 52:8, p. 123"]
theorem isCentral_of_algEquiv_matrix [Algebra.IsCentral F A] [NeZero n]
    (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) : Algebra.IsCentral F D := by
  have := nonempty_fin_of_neZero n
  refine ⟨fun d hd => ?_⟩
  rw [Subalgebra.mem_center_iff] at hd
  have hx : e.symm (Matrix.diagonal fun _ => d) ∈ Subalgebra.center F A := by
    rw [Subalgebra.mem_center_iff]
    intro y
    apply e.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, hd]
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hx)
  have h0 := congrArg (fun x : A => e x (Classical.arbitrary (Fin n)) (Classical.arbitrary (Fin n))) hc
  simp only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] at h0
  rw [Algebra.mem_bot]
  exact ⟨c, by simpa [Matrix.algebraMap_matrix_apply] using h0⟩

/-- **52:8, uniqueness of $D$** (O'Meara 1973, §52C, p. 123–124): if a finite-dimensional algebra $A$ is isomorphic
both to $M_n(D)$ and to $M_m(D')$ for division algebras $D, D'$ ($n, m \ge 1$), then $D \cong D'$ as
$F$-algebras. The proof follows O'Meara: a minimal left ideal $\mathfrak a$ of $A$ has $R_A(\mathfrak a) \cong D$
(`exists_isAtom_end_algEquiv`), and by 52:4 the algebra $R_A(\mathfrak a)$ does not depend on $\mathfrak a$
(`nonempty_algEquiv_end_of_isAtom`).

*Update:* neither centrality nor simplicity of $A$ is needed, since $M_n(D)$ is automatically simple. -/
@[kb "omeara1963" "§52C, 52:8, p. 123"]
theorem nonempty_algEquiv_of_algEquiv_matrix [FiniteDimensional F A] [NeZero n] [NeZero m]
    (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) (e' : A ≃ₐ[F] Matrix (Fin m) (Fin m) D') :
    Nonempty (D ≃ₐ[F] D') := by
  have := nonempty_fin_of_neZero n
  have := nonempty_fin_of_neZero m
  have hA : IsSimpleRing A := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  obtain ⟨a, ha, ⟨f⟩⟩ := exists_isAtom_end_algEquiv e
  obtain ⟨a', ha', ⟨f'⟩⟩ := exists_isAtom_end_algEquiv e'
  obtain ⟨g⟩ := nonempty_algEquiv_end_of_isAtom (F := F) ha ha'
  exact ⟨AlgEquiv.unop (f.symm.trans (g.trans f'))⟩

/-- **52:8, uniqueness of $n$** (O'Meara 1973, §52C, p. 123–124): under the hypotheses of
`nonempty_algEquiv_of_algEquiv_matrix`, with $D, D'$ finite dimensional over $F$, $n = m$. -/
@[kb "omeara1963" "§52C, 52:8, p. 123"]
theorem eq_of_algEquiv_matrix [FiniteDimensional F A] [FiniteDimensional F D] [FiniteDimensional F D']
    [NeZero n] [NeZero m]
    (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) (e' : A ≃ₐ[F] Matrix (Fin m) (Fin m) D') : n = m := by
  obtain ⟨g⟩ := nonempty_algEquiv_of_algEquiv_matrix e e'
  have h1 := e.toLinearEquiv.finrank_eq
  have h2 := e'.toLinearEquiv.finrank_eq
  have h3 := g.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix] at h1 h2
  simp only [Fintype.card_fin] at h1 h2
  have hpos : 0 < Module.finrank F D := Module.finrank_pos
  have : n * n = m * m := by
    have h4 : n * n * Module.finrank F D = m * m * Module.finrank F D := by
      rw [← h1, h2, h3]
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  exact Nat.mul_self_inj.1 this

/-- **52:8** (O'Meara 1973, §52C, p. 123–124), as stated in the book: let $A$ be a central simple algebra with
$A \cong M_n(D)$ for a division algebra $D$ ($n \ge 1$). Then $D$ is central, and for any other such
decomposition $A \cong M_m(D')$ one has $m = n$ and $D \cong D'$. -/
@[kb "omeara1963" "§52C, 52:8, p. 123"]
theorem omeara_52_8 [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]
    [FiniteDimensional F D] [NeZero n] (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) :
    Algebra.IsCentral F D ∧ ∀ (m : ℕ) [NeZero m] (D' : Type _) [DivisionRing D'] [Algebra F D']
      [FiniteDimensional F D'], (A ≃ₐ[F] Matrix (Fin m) (Fin m) D') →
        (m = n ∧ Nonempty (D ≃ₐ[F] D')) := by
  refine ⟨isCentral_of_algEquiv_matrix e, fun m _ D' _ _ _ e' => ?_⟩
  exact ⟨(eq_of_algEquiv_matrix e e').symm, nonempty_algEquiv_of_algEquiv_matrix e e'⟩

end Unique

/-- **52:9, existence** (O'Meara 1973, §52E, Wedderburn's theorem, p. 125): a central simple algebra $A$ over $F$ is
isomorphic to $M_n(F) \otimes_F D$ for some $n \ge 1$ and some central division algebra $D$ over $F$ (which is
finite dimensional, and simple, being a division ring).

O'Meara proves the isomorphism $A \cong M_n(D)$ in steps 1)–4) (pp. 125–127); here that is Mathlib's
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`. Centrality of $D$ is `isCentral_of_algEquiv_matrix`
(52:8) and the passage to $M_n(F) \otimes_F D$ is 52:7. -/
@[kb "omeara1963" "§52E, 52:9, p. 125"]
theorem exists_algEquiv_matrix_tensor_division (A : Type u) [Ring A] [Algebra F A] [FiniteDimensional F A]
    [Algebra.IsCentral F A] [IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : FiniteDimensional F D), Algebra.IsCentral F D ∧
        Nonempty (A ≃ₐ[F] Matrix (Fin n) (Fin n) F ⊗[F] D) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
  obtain ⟨t⟩ := nonempty_matrix_tensor_algEquiv_matrix (F := F) n D
  exact ⟨n, hn, D, inferInstance, inferInstance, inferInstance, isCentral_of_algEquiv_matrix e,
    ⟨e.trans t.symm⟩⟩

section UniqueTensor

variable {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]
variable {D : Type*} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
variable {D' : Type*} [DivisionRing D'] [Algebra F D'] [FiniteDimensional F D']
variable {n m : ℕ} [NeZero n] [NeZero m]

/-- **52:9, uniqueness** (O'Meara 1973, §52E, p. 125, 127): if $A \cong M_n(F) \otimes_F D$ and
$A \cong M_m(F) \otimes_F D'$ for division algebras $D, D'$ over $F$ (and $n, m \ge 1$), then $n = m$ and
$D \cong D'$. This follows from 52:7 and the uniqueness part of 52:8. -/
@[kb "omeara1963" "§52E, 52:9, p. 125"]
theorem unique_algEquiv_matrix_tensor_division
    (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) F ⊗[F] D) (e' : A ≃ₐ[F] Matrix (Fin m) (Fin m) F ⊗[F] D') :
    n = m ∧ Nonempty (D ≃ₐ[F] D') := by
  obtain ⟨t⟩ := nonempty_matrix_tensor_algEquiv_matrix (F := F) n D
  obtain ⟨t'⟩ := nonempty_matrix_tensor_algEquiv_matrix (F := F) m D'
  exact ⟨eq_of_algEquiv_matrix (e.trans t) (e'.trans t'),
    nonempty_algEquiv_of_algEquiv_matrix (e.trans t) (e'.trans t')⟩

end UniqueTensor

end Wedderburn

section Similarity

variable {F : Type u} [Field F]

/-- The reindexing isomorphism $M_r(M_n(D)) \cong M_{rn}(D)$. -/
def matrixMatrixAlgEquiv (r n : ℕ) (D : Type*) [Ring D] [Algebra F D] :
    Matrix (Fin r) (Fin r) (Matrix (Fin n) (Fin n) D) ≃ₐ[F] Matrix (Fin (r * n)) (Fin (r * n)) D :=
  (Matrix.compAlgEquiv (Fin r) (Fin n) D F).trans (Matrix.reindexAlgEquiv F D finProdFinEquiv)

variable {A A' : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]
  [IsSimpleRing A] [Ring A'] [Algebra F A'] [FiniteDimensional F A'] [Algebra.IsCentral F A']
  [IsSimpleRing A']
variable {D D' : Type*} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [DivisionRing D'] [Algebra F D'] [FiniteDimensional F D']
variable {n m : ℕ} [NeZero n] [NeZero m]

/-- **§52F, similarity of central simple algebras = Brauer equivalence** (O'Meara 1973, p. 127–128, with the
definition of similarity $A \sim A'$): for central simple algebras $A \cong M_n(D)$ and $A' \cong M_m(D')$ (their
Wedderburn decompositions, 52:9), $A \sim A'$, that is, $D \cong D'$, holds if and only if $A$ and $A'$ are
Brauer equivalent in the sense of Mathlib (`IsBrauerEquivalent`: $M_r(A) \cong M_s(A')$ for some $r, s \ge 1$).
O'Meara's similarity is therefore not redefined; it is Mathlib's `IsBrauerEquivalent`. -/
@[kb "omeara1963" "§52F, p. 127–128"]
theorem isBrauerEquivalent_iff_nonempty_algEquiv
    (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) (e' : A' ≃ₐ[F] Matrix (Fin m) (Fin m) D') :
    IsBrauerEquivalent (⟨AlgCat.of F A⟩ : CSA F) ⟨AlgCat.of F A'⟩ ↔ Nonempty (D ≃ₐ[F] D') := by
  constructor
  · rintro ⟨r, s, hr, hs, ⟨g⟩⟩
    have : NeZero r := ⟨hr⟩
    have : NeZero s := ⟨hs⟩
    have g₁ : Matrix (Fin r) (Fin r) A ≃ₐ[F] Matrix (Fin (r * n)) (Fin (r * n)) D :=
      (e.mapMatrix (m := Fin r)).trans (matrixMatrixAlgEquiv r n D)
    have g₂ : Matrix (Fin s) (Fin s) A' ≃ₐ[F] Matrix (Fin (s * m)) (Fin (s * m)) D' :=
      (e'.mapMatrix (m := Fin s)).trans (matrixMatrixAlgEquiv s m D')
    exact nonempty_algEquiv_of_algEquiv_matrix (A := Matrix (Fin r) (Fin r) A) g₁ (g.trans g₂)
  · rintro ⟨ε⟩
    refine ⟨m, n, NeZero.ne m, NeZero.ne n, ⟨?_⟩⟩
    exact ((e.mapMatrix (m := Fin m)).trans (matrixMatrixAlgEquiv m n D)).trans
      ((ε.mapMatrix (m := Fin (m * n))).trans
        ((Matrix.reindexAlgEquiv F D' (finCongr (Nat.mul_comm m n))).trans
          (matrixMatrixAlgEquiv n m D').symm)) |>.trans (e'.mapMatrix (m := Fin n)).symm

/-- **§52F, remark** (O'Meara 1973, p. 128): $A \sim A'$ if and only if $A \otimes M_r(F) \cong A' \otimes M_s(F)$ for
some $r, s \ge 1$. Here $\sim$ is Mathlib's `IsBrauerEquivalent`, whose defining isomorphism
$M_r(A) \cong M_s(A')$ is rewritten with `matrixEquivTensor`. -/
@[kb "omeara1963" "§52F, p. 128"]
theorem isBrauerEquivalent_iff_tensor :
    IsBrauerEquivalent (⟨AlgCat.of F A⟩ : CSA F) ⟨AlgCat.of F A'⟩ ↔
      ∃ r s : ℕ, r ≠ 0 ∧ s ≠ 0 ∧
        Nonempty (A ⊗[F] Matrix (Fin r) (Fin r) F ≃ₐ[F] A' ⊗[F] Matrix (Fin s) (Fin s) F) := by
  refine exists_congr fun r => exists_congr fun s => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨g⟩
    exact ⟨((matrixEquivTensor (Fin r) F A).symm.trans g).trans (matrixEquivTensor (Fin s) F A')⟩
  · rintro ⟨g⟩
    exact ⟨(matrixEquivTensor (Fin r) F A).trans (g.trans (matrixEquivTensor (Fin s) F A').symm)⟩

/-- **§52F, splitting** (O'Meara 1973, p. 128): a central simple algebra $A \cong M_n(D)$ *splits*
($A \cong M_k(F)$ for some $k \ge 1$) if and only if its division algebra component $D$ is isomorphic to $F$. -/
@[kb "omeara1963" "§52F, p. 128"]
theorem splits_iff_nonempty_algEquiv_base (e : A ≃ₐ[F] Matrix (Fin n) (Fin n) D) :
    (∃ k : ℕ, k ≠ 0 ∧ Nonempty (A ≃ₐ[F] Matrix (Fin k) (Fin k) F)) ↔ Nonempty (D ≃ₐ[F] F) := by
  constructor
  · rintro ⟨k, hk, ⟨g⟩⟩
    have : NeZero k := ⟨hk⟩
    exact nonempty_algEquiv_of_algEquiv_matrix e g
  · rintro ⟨ε⟩
    exact ⟨n, NeZero.ne n, ⟨e.trans ε.mapMatrix⟩⟩

end Similarity

end QuadFormsKB.OMeara
