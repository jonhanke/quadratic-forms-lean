/-
# O'Meara §51: tensor products (running text, pp. 113-118)

**Setting.** $F$ a field; vector spaces and algebras over $F$.  The tensor product of the book is Mathlib's
`TensorProduct` (`U ⊗[F] V`); the comparison lemmas below show that the book's universal property and
Mathlib's `IsTensorProduct` agree, and that the book's constructions for algebras are Mathlib's
`Algebra.TensorProduct`.

**Defines** (namespace `QuadFormsKB.OMeara.Tensor51`)
* `IsMultiplicative ω`: the book's *multiplicative bilinear mapping* of algebras (p. 116);
* `tprodList l`: the left-nested iterated tensor product $A_1 \otimes \cdots \otimes A_r$ of a list of algebras
  (p. 118), as a bundled `AlgCat`.

**Proves**
* `hasTensorUP_iff_isTensorProduct`, `existsUnique_linearEquiv_of_isTensorProduct` (p. 113-114): the universal
  property, and uniqueness of the tensor product up to a unique isomorphism;
* `linearIndependent_tmul_basis`, `span_tmul_basis`, `span_tmul_eq_top` (p. 114): the products of basis vectors
  form a basis; pure tensors span;
* `exists_algHom_of_basis_mul` (p. 115): a linear map multiplicative on a basis is an algebra homomorphism;
* `assoc_of_basis`, `one_mul_of_basis`, `mul_one_of_basis` (pp. 115-116): structure constants;
* `existsUnique_algHom_of_isMultiplicative` (p. 117): the universal property of the tensor product of algebras;
* `tprodList_singleton`, `tprodList_append`, `tprodList_perm` (p. 118): iterated tensor products.
-/
import Mathlib
import QuadFormsKB.Citation

open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Tensor51

/-! ### Uniqueness of the tensor product (pp. 113-114) -/

section Universal

universe u

variable {F : Type u} [Field F] {U V T : Type u} [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup T] [Module F T]

/-- O'Meara's universal property of a pair $(\iota, T)$ (p. 113): for every $F$-space $W$ and every bilinear
$\omega : U \times V \to W$ there is exactly one linear $\varphi : T \to W$ with
$\varphi(\iota(u,v)) = \omega(u,v)$.  *Deviation:* the book quantifies over all spaces $W$; here $W$ ranges over
`Type u`, the universe of $U$, $V$, $T$ (enough, since $W = U \otimes V$ and $W = T$ are used). -/
@[kb "omeara1963" "§51, p. 113 (tensor product: the universal mapping property)"]
def HasTensorUP (ι' : U →ₗ[F] V →ₗ[F] T) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module F W] (ω : U →ₗ[F] V →ₗ[F] W),
    ∃! φ : T →ₗ[F] W, ∀ u v, φ (ι' u v) = ω u v

/-- **O'Meara §51, p. 113-114** (comparison): the book's universal property of the tensor product is
equivalent to Mathlib's `IsTensorProduct` (bijectivity of `TensorProduct.lift ι'`). -/
@[kb "omeara1963" "§51, p. 113 (universal property is IsTensorProduct)"]
theorem hasTensorUP_iff_isTensorProduct (ι' : U →ₗ[F] V →ₗ[F] T) :
    HasTensorUP ι' ↔ IsTensorProduct ι' := by
  constructor
  · intro h
    obtain ⟨ψ, hψ, -⟩ := h (U ⊗[F] V) (TensorProduct.mk F U V)
    have h1 : (TensorProduct.lift ι').comp ψ = LinearMap.id := by
      obtain ⟨_, -, hu⟩ := h T ι'
      have e1 := hu ((TensorProduct.lift ι').comp ψ) (fun u v => by rw [LinearMap.comp_apply, hψ]; simp)
      have e2 := hu LinearMap.id (fun u v => rfl)
      exact e1.trans e2.symm
    have h2 : ψ.comp (TensorProduct.lift ι') = LinearMap.id := by
      apply TensorProduct.ext'
      intro u v
      simp [hψ]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      calc x = ψ (TensorProduct.lift ι' x) := (LinearMap.congr_fun h2 x).symm
        _ = ψ (TensorProduct.lift ι' y) := by rw [hxy]
        _ = y := LinearMap.congr_fun h2 y
    · intro t
      exact ⟨ψ t, by simpa using LinearMap.congr_fun h1 t⟩
  · intro h W _ _ ω
    refine ⟨h.lift ω, fun u v => h.lift_eq ω u v, ?_⟩
    intro φ hφ
    apply LinearMap.ext
    intro t
    refine h.inductionOn t (fun u v => ?_) (fun x y hx hy => by simp [hx, hy])
    rw [hφ, h.lift_eq]

/-- **O'Meara §51, p. 114** (uniqueness of the tensor product): if $(\iota', T)$ is a tensor product of
$U$ and $V$ (Mathlib's `IsTensorProduct`, equivalently the book's universal property by
`hasTensorUP_iff_isTensorProduct`), there is exactly one linear isomorphism
$e : U \otimes_F V \to T$ with $e(u \otimes v) = \iota'(u,v)$. -/
@[kb "omeara1963" "§51, p. 114 (tensor product unique up to unique isomorphism)"]
theorem existsUnique_linearEquiv_of_isTensorProduct {ι' : U →ₗ[F] V →ₗ[F] T}
    (h : IsTensorProduct ι') :
    ∃! e : U ⊗[F] V ≃ₗ[F] T, ∀ u v, e (u ⊗ₜ[F] v) = ι' u v := by
  refine ⟨h.equiv, fun u v => by simp, ?_⟩
  intro e he
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro u v
  simp [he]

end Universal

/-! ### Bases of a tensor product (p. 114) -/

section Basis

variable {F : Type*} [Field F] {U V : Type*} [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] {ι κ : Type*}

/-- **O'Meara §51, p. 114**: if $(u_i)$, $(v_j)$ are bases of $U$, $V$, then the vectors
$u_i \otimes v_j$ are linearly independent (Mathlib `Basis.tensorProduct`). -/
@[kb "omeara1963" "§51, p. 114 (u_i ⊗ v_j linearly independent)"]
theorem linearIndependent_tmul_basis (b : Module.Basis ι F U) (c : Module.Basis κ F V) :
    LinearIndependent F (fun p : ι × κ => b p.1 ⊗ₜ[F] c p.2) := by
  convert (Module.Basis.tensorProduct b c).linearIndependent using 1
  ext p
  rw [Module.Basis.tensorProduct_apply]

/-- **O'Meara §51, p. 114**: the vectors $u_i \otimes v_j$ span $U \otimes_F V$ (Mathlib
`Basis.tensorProduct`); together with `linearIndependent_tmul_basis`, they form a basis. -/
@[kb "omeara1963" "§51, p. 114 (u_i ⊗ v_j span)"]
theorem span_tmul_basis (b : Module.Basis ι F U) (c : Module.Basis κ F V) :
    Submodule.span F (Set.range (fun p : ι × κ => b p.1 ⊗ₜ[F] c p.2)) = ⊤ := by
  convert (Module.Basis.tensorProduct b c).span_eq using 2
  ext p
  simp

/-- **O'Meara §51, p. 114**: the pure tensors $u \otimes v$ span $U \otimes_F V$ (Mathlib
`TensorProduct.span_tmul_eq_top`). -/
@[kb "omeara1963" "§51, p. 114 (pure tensors span)"]
theorem span_tmul_eq_top :
    Submodule.span F {t : U ⊗[F] V | ∃ u v, t = u ⊗ₜ[F] v} = ⊤ := by
  have := TensorProduct.span_tmul_eq_top F U V
  have h : {t : U ⊗[F] V | ∃ u v, t = u ⊗ₜ[F] v} = {t | ∃ m n, m ⊗ₜ[F] n = t} := by
    ext t; simp [eq_comm]
  rw [h]; exact this

end Basis

/-! ### Algebras from bases (pp. 115-116) -/

section Algebras

variable {F : Type*} [Field F] {ι : Type*}

/-- Induction over a basis: a property of vectors that holds for $0$, the basis vectors, and is
closed under sums and scalar multiples holds everywhere. -/
theorem basis_induction {A : Type*} [AddCommGroup A] [Module F A] (b : Module.Basis ι F A)
    {P : A → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : F) x, P x → P (a • x)) (hb : ∀ i, P (b i)) (x : A) : P x := by
  have hx : x ∈ Submodule.span F (Set.range b) := by rw [b.span_eq]; trivial
  exact Submodule.span_induction (fun _ ⟨i, hi⟩ => hi ▸ hb i) h0 (fun x y _ _ => hadd x y)
    (fun a x _ => hsmul a x) hx

/-- **O'Meara §51, p. 115**: an $F$-linear map $\varphi : A \to B$ of $F$-algebras with $\varphi(1) = 1$
that is multiplicative on a basis $(x_i)$ ($\varphi(x_i x_j) = \varphi(x_i)\varphi(x_j)$) is an algebra
homomorphism. -/
@[kb "omeara1963" "§51, p. 115 (multiplicative on a basis implies homomorphism)"]
theorem exists_algHom_of_basis_mul {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
    (b : Module.Basis ι F A) (φ : A →ₗ[F] B) (h1 : φ 1 = 1)
    (hb : ∀ i j, φ (b i * b j) = φ (b i) * φ (b j)) :
    ∃ ψ : A →ₐ[F] B, ⇑ψ = ⇑φ := by
  have hmul : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    induction x using basis_induction b with
    | h0 => simp
    | hadd x x' hx hx' => simp [add_mul, hx, hx']
    | hsmul a x hx => simp [hx]
    | hb i =>
      induction y using basis_induction b with
      | h0 => simp
      | hadd y y' hy hy' => simp [mul_add, hy, hy']
      | hsmul a y hy => simp [hy]
      | hb j => exact hb i j
  exact ⟨AlgHom.ofLinearMap φ h1 hmul, rfl⟩

variable {A : Type*} [AddCommGroup A] [Module F A]

/-- **O'Meara §51, p. 115-116** (structure constants): a bilinear multiplication $m$ on a vector space $A$
with basis $(x_i)$ (that is, one given by structure constants $x_i x_j = \sum_k \gamma_{ij}^k x_k$) that is
associative on basis vectors is associative on all of $A$.  Bilinearity of `m` is the rule
$\alpha(xy) = (\alpha x)y = x(\alpha y)$ of an algebra. -/
@[kb "omeara1963" "§51, p. 116 (associativity on a basis implies associativity)"]
theorem assoc_of_basis (b : Module.Basis ι F A) (m : A →ₗ[F] A →ₗ[F] A)
    (h : ∀ i j k, m (m (b i) (b j)) (b k) = m (b i) (m (b j) (b k))) (x y z : A) :
    m (m x y) z = m x (m y z) := by
  induction x using basis_induction b with
  | h0 => simp
  | hadd x x' hx hx' => simp [hx, hx']
  | hsmul a x hx => simp [hx]
  | hb i =>
    induction y using basis_induction b with
    | h0 => simp
    | hadd y y' hy hy' => simp [hy, hy']
    | hsmul a y hy => simp [hy]
    | hb j =>
      induction z using basis_induction b with
      | h0 => simp
      | hadd z z' hz hz' => simp [hz, hz']
      | hsmul a z hz => simp [hz]
      | hb k => exact h i j k

/-- **O'Meara §51, p. 116**: if $e$ satisfies $e x_i = x_i = x_i e$ on a basis, then $e x = x = x e$ for all
$x \in A$ (left identity part). -/
@[kb "omeara1963" "§51, p. 116 (identity on a basis is an identity)"]
theorem one_mul_of_basis (b : Module.Basis ι F A) (m : A →ₗ[F] A →ₗ[F] A) (e : A)
    (h : ∀ i, m e (b i) = b i ∧ m (b i) e = b i) (x : A) : m e x = x := by
  induction x using basis_induction b with
  | h0 => simp
  | hadd x x' hx hx' => simp [hx, hx']
  | hsmul a x hx => simp [hx]
  | hb i => exact (h i).1

/-- **O'Meara §51, p. 116**: right identity part of `one_mul_of_basis`. -/
@[kb "omeara1963" "§51, p. 116 (identity on a basis is an identity)"]
theorem mul_one_of_basis (b : Module.Basis ι F A) (m : A →ₗ[F] A →ₗ[F] A) (e : A)
    (h : ∀ i, m e (b i) = b i ∧ m (b i) e = b i) (x : A) : m x e = x := by
  induction x using basis_induction b with
  | h0 => simp
  | hadd x x' hx hx' => simp [hx, hx']
  | hsmul a x hx => simp [hx]
  | hb i => exact (h i).2

end Algebras

/-! ### Multiplicative bilinear maps and the tensor product of algebras (pp. 116-117) -/

section Mult

variable {F : Type*} [Field F] {A B C : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  [Ring C] [Algebra F C]

/-- **O'Meara §51, p. 116**: a bilinear map $\omega : A \times B \to C$ of $F$-algebras is
*multiplicative* if $\omega(1_A,1_B) = 1_C$ and
$\omega(x,y)\,\omega(x',y') = \omega(xx', yy')$ for all $x, x' \in A$, $y, y' \in B$.  (The book includes
the condition $\omega(1_A,1_B) = 1_C$; Mathlib has no such notion.) -/
@[kb "omeara1963" "§51, p. 116 (multiplicative bilinear mapping)"]
def IsMultiplicative (ω : A →ₗ[F] B →ₗ[F] C) : Prop :=
  ω 1 1 = 1 ∧ ∀ x y x' y', ω x y * ω x' y' = ω (x * x') (y * y')

/-- **O'Meara §51, p. 117** (universal property of the tensor product of algebras): a multiplicative
bilinear map $\omega : A \times B \to C$ induces exactly one algebra homomorphism
$\varphi : A \otimes_F B \to C$ with $\varphi(x \otimes y) = \omega(x,y)$.  *Deviation:* none; the book
first gets a unique linear map and then shows it is an algebra homomorphism; here the homomorphism is built
directly with `Algebra.TensorProduct.lift` and uniqueness (even among algebra homomorphisms) is
`Algebra.TensorProduct.ext'`; uniqueness among linear maps is `hasTensorUP_iff_isTensorProduct`. -/
@[kb "omeara1963" "§51, p. 117 (multiplicative bilinear map induces algebra homomorphism)"]
theorem existsUnique_algHom_of_isMultiplicative {ω : A →ₗ[F] B →ₗ[F] C} (h : IsMultiplicative ω) :
    ∃! φ : A ⊗[F] B →ₐ[F] C, ∀ x y, φ (x ⊗ₜ[F] y) = ω x y := by
  obtain ⟨h1, hm⟩ := h
  let f : A →ₐ[F] C := AlgHom.ofLinearMap (ω.flip 1) (by simpa using h1) (fun x y => by
    have := hm x 1 y 1
    simpa using this.symm)
  let g : B →ₐ[F] C := AlgHom.ofLinearMap (ω 1) h1 (fun x y => by
    have := hm 1 x 1 y
    simpa using this.symm)
  have hc : ∀ x y, Commute (f x) (g y) := by
    intro x y
    have e1 := hm x 1 1 y
    have e2 := hm 1 y x 1
    simp only [mul_one, one_mul] at e1 e2
    exact e1.trans e2.symm
  refine ⟨Algebra.TensorProduct.lift f g hc, fun x y => ?_, ?_⟩
  · rw [Algebra.TensorProduct.lift_tmul]
    have := hm x 1 1 y
    simpa [f, g] using this
  · intro φ hφ
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [hφ, Algebra.TensorProduct.lift_tmul]
    have := hm x 1 1 y
    simpa [f, g] using (this.trans (by simp)).symm

end Mult

/-! ### Iterated tensor products (p. 118) -/

section Iterated

universe u

variable {F : Type u} [Field F]

/-- **O'Meara §51, p. 118**: the iterated tensor product of a list of $F$-algebras, nested to the left:
$A_1 \otimes \cdots \otimes A_r := (A_1 \otimes \cdots \otimes A_{r-1}) \otimes A_r$.  *Deviation:* the
fold starts from the algebra $F$, so there is one extra initial factor $F$; this is harmless since
$F \otimes A \cong A$ (`tprodList_singleton`).  The empty list gives $F$. -/
@[kb "omeara1963" "§51, p. 118 (A₁ ⊗ ... ⊗ A_r defined inductively)"]
def tprodList (l : List (AlgCat.{u} F)) : AlgCat.{u} F :=
  l.foldl (fun (T A : AlgCat.{u} F) => AlgCat.of F (↥T ⊗[F] ↥A)) (AlgCat.of F F)

/-- Auxiliary: folding from an arbitrary start $T$ gives $T \otimes \mathrm{tprodList}\, l$. -/
theorem foldl_tprod (l : List (AlgCat.{u} F)) :
    ∀ T : AlgCat.{u} F, Nonempty
      ((l.foldl (fun (T A : AlgCat.{u} F) => AlgCat.of F (↥T ⊗[F] ↥A)) T : AlgCat.{u} F) ≃ₐ[F] (↥T ⊗[F] ↥(tprodList l))) := by
  induction l with
  | nil => intro T; exact ⟨(Algebra.TensorProduct.rid F F T).symm⟩
  | cons a l ih =>
    intro T
    obtain ⟨e1⟩ := ih (AlgCat.of F (↥T ⊗[F] ↥a))
    obtain ⟨e2⟩ := ih (AlgCat.of F (F ⊗[F] ↥a))
    let e3 : ↥a ⊗[F] ↥(tprodList l) ≃ₐ[F] ↥(tprodList (a :: l)) :=
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid F a).symm AlgEquiv.refl).trans e2.symm
    exact ⟨e1.trans ((Algebra.TensorProduct.assoc F F F T a (tprodList l)).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl e3))⟩

/-- **O'Meara §51, p. 118**: for a single algebra, `tprodList [A] ≃ A` (the extra factor $F$ is
harmless: $F \otimes A \cong A$). -/
@[kb "omeara1963" "§51, p. 118 (iterated tensor product of one algebra)"]
theorem tprodList_singleton (A : AlgCat.{u} F) : Nonempty (tprodList [A] ≃ₐ[F] A) :=
  by
  unfold tprodList
  exact ⟨Algebra.TensorProduct.lid F A⟩

/-- **O'Meara §51, p. 118** (associativity of iterated products): 
$A_1 \otimes \cdots \otimes A_{r+s} \cong (A_1 \otimes \cdots \otimes A_r) \otimes
(A_{r+1} \otimes \cdots \otimes A_{r+s})$ as algebras. -/
@[kb "omeara1963" "§51, p. 118 (iterated tensor product of a concatenation)"]
theorem tprodList_append (l₁ l₂ : List (AlgCat.{u} F)) :
    Nonempty (tprodList (l₁ ++ l₂) ≃ₐ[F] (↥(tprodList l₁) ⊗[F] ↥(tprodList l₂))) := by
  have := foldl_tprod l₂ (tprodList l₁)
  unfold tprodList at this ⊢
  rw [List.foldl_append]
  exact this

/-- **O'Meara §51, p. 118** (commutativity of iterated products): permuting the factors of an iterated
tensor product gives an isomorphic algebra. -/
@[kb "omeara1963" "§51, p. 118 (iterated tensor product up to permutation)"]
theorem tprodList_perm {l₁ l₂ : List (AlgCat.{u} F)} (h : l₁.Perm l₂) :
    Nonempty (tprodList l₁ ≃ₐ[F] tprodList l₂) := by
  induction h with
  | nil => exact ⟨AlgEquiv.refl⟩
  | @cons x l₁ l₂ _ ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨a⟩ := tprodList_append [x] l₁
    obtain ⟨b⟩ := tprodList_append [x] l₂
    exact ⟨a.trans ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans b.symm)⟩
  | swap x y l =>
    obtain ⟨a⟩ := tprodList_append [y, x] l
    obtain ⟨b⟩ := tprodList_append [x, y] l
    obtain ⟨c⟩ := tprodList_append [y] [x]
    obtain ⟨d⟩ := tprodList_append [x] [y]
    obtain ⟨cx⟩ := tprodList_singleton x
    obtain ⟨cy⟩ := tprodList_singleton y
    have e : tprodList [y, x] ≃ₐ[F] tprodList [x, y] :=
      (c.trans (Algebra.TensorProduct.congr cy cx)).trans
        ((Algebra.TensorProduct.comm F y x).trans
          ((Algebra.TensorProduct.congr cx.symm cy.symm).trans d.symm))
    exact ⟨a.trans ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans b.symm)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨e1.trans e2⟩

end Iterated

end QuadFormsKB.OMeara.Tensor51
