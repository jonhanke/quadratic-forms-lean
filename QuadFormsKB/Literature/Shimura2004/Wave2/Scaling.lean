/-
# Shimura 2004, Lemma 3.8 (i): scaling the form

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, Lemma 3.8 (i),
printed p. 24. Page numbers are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/CliffordGroups.lean`. For $c \in F^\times$ the
form $c\varphi$ is Mathlib's `(c : F) • Q` (so $(c\varphi)[x] = c\,\varphi[x]$), $A^+(V,\varphi)$ is the even
subalgebra `CliffordAlgebra.even Q` (a subalgebra of `CliffordAlgebra Q` whose underlying submodule is `evenOdd Q 0`),
$G^+(V,\varphi)$ is `Cassels.M0 Q`, and $\xi \mapsto \xi^*$ is `CliffordAlgebra.reverse`. Shimura's $F$-linear
ring-isomorphism $f : A^+(V,c\varphi) \to A^+(V,\varphi)$ is `evenScaleEquiv c`.

*Construction.* Shimura proves the lemma by adjoining $\sqrt c$. Here $f$ is constructed directly, by the universal
property of the even Clifford algebra (`CliffordAlgebra.even.lift`): $f(\iota(x)\iota(y)) = c\,\iota(x)\iota(y)$ (the
product on the right being taken in $A(V,\varphi)$). The inverse is the same construction with $c^{-1}$. To transport
the Clifford group we use the $F$-algebra homomorphism $\Phi : A(V,c\varphi) \to M_2(A(V,\varphi))$ with
$\Phi(\iota'(x)) = \left(\begin{smallmatrix}0 & c\,\iota(x)\\ \iota(x) & 0\end{smallmatrix}\right)$ (a matrix model of
$\sqrt c$), which restricts on $A^+$ to $f$ placed on the diagonal. Everything is proved for a general pair of forms
$Q'$, $Q$ with $Q' = d\,Q$ ($d \in F^\times$), so that the inverse direction is the same statement with $d^{-1}$; the
statements for $c\varphi$ are the case $d = c$.

*Indices.* Nothing is indexed here.

**Proves** (all unconditional except $\nu$, which needs $\varphi$ and $c\varphi$ nondegenerate; standard axioms only)
* $f : A^+(V,c\varphi) \cong A^+(V,\varphi)$ is an $F$-algebra isomorphism with $f(\iota'(x)\iota'(y)) =
  c\,\iota(x)\iota(y)$ (`evenScaleEquiv`, `evenScaleEquiv_ι`).
* $f(\xi)^* = f(\xi^*)$ (`reverse_evenScaleEquiv`).
* $f(G^+(V,c\varphi)) = G^+(V,\varphi)$, as an isomorphism of groups $G^+(V,c\varphi) \cong G^+(V,\varphi)$
  extending $f$ (`evenScaleM0Equiv`, `coe_evenScaleM0Equiv`).
* $\tau(a) = \tau(f(a))$ for $a \in G^+(V,c\varphi)$ (`tau_evenScaleM0Equiv`).
* $\nu(a) = \nu(f(a))$ for $a \in G^+(V,c\varphi)$ (`multiplier_evenScaleM0Equiv`).
-/
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.Data.Matrix.Basic
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q Q' : QuadraticForm F V}

/-! ### The isomorphism $f : A^+(V, Q') \cong A^+(V, Q)$ for $Q' = dQ$ -/

/-- The `EvenHom` $(x, y) \mapsto d\,\iota(x)\iota(y) \in A^+(V,Q)$ for the form $Q'$, where $Q' = dQ$. -/
def scaleEvenHom (Q Q' : QuadraticForm F V) (d : F) (h : ∀ m, Q' m = d * Q m) : EvenHom Q' (even Q) where
  bilin := d • (even.ι Q).bilin
  contract m := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, (even.ι Q).contract, h, map_mul, Algebra.smul_def]
  contract_mid m₁ m₂ m₃ := by
    simp only [LinearMap.smul_apply]
    rw [smul_mul_smul_comm, (even.ι Q).contract_mid, h, smul_smul, smul_smul]
    congr 1
    ring

/-- The algebra homomorphism $A^+(V,Q') \to A^+(V,Q)$, $\iota'(x)\iota'(y) \mapsto d\,\iota(x)\iota(y)$, for
$Q' = dQ$. -/
def scaleHom (Q Q' : QuadraticForm F V) (d : F) (h : ∀ m, Q' m = d * Q m) : even Q' →ₐ[F] even Q :=
  even.lift Q' (scaleEvenHom Q Q' d h)

theorem scaleHom_ι (d : F) (h : ∀ m, Q' m = d * Q m) (m₁ m₂ : V) :
    scaleHom Q Q' d h ((even.ι Q').bilin m₁ m₂) = d • (even.ι Q).bilin m₁ m₂ := by
  rw [scaleHom, even.lift_ι]
  rfl

/-- If $Q' = dQ$ and $d \ne 0$ then $Q = d^{-1}Q'$. -/
theorem scale_inv_h {d : F} (hd : d ≠ 0) (h : ∀ m, Q' m = d * Q m) : ∀ m, Q m = d⁻¹ * Q' m := fun m => by
  rw [h, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem scaleHom_scaleHom {d d' : F} (hdd : d * d' = 1) (h : ∀ m, Q' m = d * Q m) (h' : ∀ m, Q m = d' * Q' m)
    (x : even Q') : scaleHom Q' Q d' h' (scaleHom Q Q' d h x) = x := by
  have key : (scaleHom Q' Q d' h').comp (scaleHom Q Q' d h) = AlgHom.id F _ := by
    apply even.algHom_ext Q'
    refine EvenHom.ext (LinearMap.ext₂ fun m₁ m₂ => ?_)
    change (scaleHom Q' Q d' h').comp (scaleHom Q Q' d h) ((even.ι Q').bilin m₁ m₂) =
      (AlgHom.id F _) ((even.ι Q').bilin m₁ m₂)
    rw [AlgHom.comp_apply, scaleHom_ι, map_smul, scaleHom_ι, smul_smul, hdd, one_smul]
    rfl
  exact AlgHom.congr_fun key x

/-- The isomorphism $A^+(V,Q') \cong A^+(V,Q)$ for $Q' = dQ$, $d \ne 0$. -/
def evenScaleEquivOf (d : F) (hd : d ≠ 0) (h : ∀ m, Q' m = d * Q m) : even Q' ≃ₐ[F] even Q :=
  AlgEquiv.ofAlgHom (scaleHom Q Q' d h) (scaleHom Q' Q d⁻¹ (scale_inv_h hd h))
    (AlgHom.ext fun x => scaleHom_scaleHom (inv_mul_cancel₀ hd) (scale_inv_h hd h) h x)
    (AlgHom.ext fun x => scaleHom_scaleHom (mul_inv_cancel₀ hd) h (scale_inv_h hd h) x)

/-! ### Reversion -/

theorem reverse_scaleHom (d : F) (h : ∀ m, Q' m = d * Q m) (e : even Q') :
    reverse (scaleHom Q Q' d h e : CliffordAlgebra Q) =
      scaleHom Q Q' d h ⟨reverse (e : CliffordAlgebra Q'), (reverse_mem_evenOdd_iff Q').2 e.2⟩ := by
  obtain ⟨x, hx⟩ := e
  induction x, hx using even_induction with
  | algebraMap r =>
    have e1 : (⟨algebraMap F _ r, SetLike.algebraMap_mem_graded _ _⟩ : even Q') = algebraMap F (even Q') r := rfl
    have e2 : (⟨reverse (algebraMap F (CliffordAlgebra Q') r), (reverse_mem_evenOdd_iff Q').2
        (SetLike.algebraMap_mem_graded _ _)⟩ : even Q') = algebraMap F (even Q') r :=
      Subtype.ext (reverse.commutes r)
    rw [e2]
    simp only [e1, AlgHom.commutes]
    exact reverse.commutes r
  | add x y hx hy ihx ihy =>
    have e1 : (⟨x + y, Submodule.add_mem _ hx hy⟩ : even Q') = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    have e2 : (⟨reverse (x + y), (reverse_mem_evenOdd_iff Q').2 (Submodule.add_mem _ hx hy)⟩ : even Q') =
        ⟨reverse x, (reverse_mem_evenOdd_iff Q').2 hx⟩ + ⟨reverse y, (reverse_mem_evenOdd_iff Q').2 hy⟩ :=
      Subtype.ext (map_add _ _ _)
    rw [e2, e1, map_add, map_add, Subalgebra.coe_add, Subalgebra.coe_add, map_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have e1 : ∀ hm, (⟨ι Q' m₁ * ι Q' m₂ * x, hm⟩ : even Q') = (even.ι Q').bilin m₁ m₂ * ⟨x, hx⟩ :=
      fun hm => rfl
    have e2 : ∀ hm, (⟨reverse (ι Q' m₁ * ι Q' m₂ * x), hm⟩ : even Q') =
        ⟨reverse x, (reverse_mem_evenOdd_iff Q').2 hx⟩ * (even.ι Q').bilin m₂ m₁ := fun hm => by
      apply Subtype.ext
      change reverse (ι Q' m₁ * ι Q' m₂ * x) = reverse x * (ι Q' m₂ * ι Q' m₁)
      rw [reverse.map_mul, reverse.map_mul, reverse_ι, reverse_ι]
    refine Eq.trans (b := reverse ↑(scaleHom Q Q' d h ((even.ι Q').bilin m₁ m₂ * ⟨x, hx⟩))) rfl ?_
    refine Eq.trans ?_
      (congrArg (fun z : even Q' => (scaleHom Q Q' d h z : CliffordAlgebra Q)) (e2 _)).symm
    rw [map_mul, map_mul, scaleHom_ι, scaleHom_ι, Subalgebra.coe_mul, Subalgebra.coe_mul,
      reverse.map_mul, ← ih]
    have h1 : ((d • (even.ι Q).bilin m₁ m₂ : even Q) : CliffordAlgebra Q) = d • (ι Q m₁ * ι Q m₂) := rfl
    have h2 : ((d • (even.ι Q).bilin m₂ m₁ : even Q) : CliffordAlgebra Q) = d • (ι Q m₂ * ι Q m₁) := rfl
    rw [h1, h2, map_smul, reverse.map_mul, reverse_ι, reverse_ι]

/-! ### A matrix model of $\sqrt d$ -/

/-- The linear map $x \mapsto \left(\begin{smallmatrix}0 & d\,\iota(x)\\ \iota(x) & 0\end{smallmatrix}\right)$
from $V$ to $M_2(A(V,Q))$. -/
def phiVec (Q : QuadraticForm F V) (d : F) : V →ₗ[F] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) where
  toFun x := Matrix.of ![![0, d • ι Q x], ![ι Q x, 0]]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_add]
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_smul, mul_comm]

theorem phiVec_sq (d : F) (h : ∀ m, Q' m = d * Q m) (x : V) :
    phiVec Q d x * phiVec Q d x =
      algebraMap F (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) (Q' x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phiVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply, h, Algebra.smul_def,
      mul_assoc, ι_sq_scalar, Algebra.left_comm]

/-- The algebra homomorphism $\Phi : A(V,Q') \to M_2(A(V,Q))$ with $\Phi(\iota'(x)) =
\left(\begin{smallmatrix}0 & d\,\iota(x)\\ \iota(x) & 0\end{smallmatrix}\right)$ (for $Q' = dQ$). -/
def phi (d : F) (h : ∀ m, Q' m = d * Q m) :
    CliffordAlgebra Q' →ₐ[F] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  CliffordAlgebra.lift Q' ⟨phiVec Q d, phiVec_sq d h⟩

theorem phi_ι (d : F) (h : ∀ m, Q' m = d * Q m) (x : V) : phi d h (ι Q' x) = phiVec Q d x :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- On $A^+(V,Q')$, $\Phi$ is $f$ placed on the diagonal. -/
theorem phi_even (d : F) (h : ∀ m, Q' m = d * Q m) (e : even Q') :
    phi d h (e : CliffordAlgebra Q') = Matrix.scalar (Fin 2) (scaleHom Q Q' d h e : CliffordAlgebra Q) := by
  have key : (phi d h).comp (even Q').val =
      ((Matrix.scalarAlgHom (Fin 2) F).comp (even Q).val).comp (scaleHom Q Q' d h) := by
    apply even.algHom_ext Q'
    refine EvenHom.ext (LinearMap.ext₂ fun m₁ m₂ => ?_)
    change (phi d h) (ι Q' m₁ * ι Q' m₂) =
      Matrix.scalar (Fin 2) ((scaleHom Q Q' d h ((even.ι Q').bilin m₁ m₂) : even Q) : CliffordAlgebra Q)
    have hc : ((even.ι Q).bilin m₁ m₂ : CliffordAlgebra Q) = ι Q m₁ * ι Q m₂ := rfl
    rw [scaleHom_ι, map_mul, phi_ι, phi_ι]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phiVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hc]
  exact AlgHom.congr_fun key e

/-- **Key identity.** If $e_1\,\iota'(x)\,e_2 = \iota'(y)$ in $A(V,Q')$ with $e_1, e_2 \in A^+(V,Q')$, then
$f(e_1)\,\iota(x)\,f(e_2) = \iota(y)$ in $A(V,Q)$ (compare the $(2,1)$ entries of $\Phi$). -/
theorem phi_core (d : F) (h : ∀ m, Q' m = d * Q m) (e₁ e₂ : even Q') (x y : V)
    (hxy : (e₁ : CliffordAlgebra Q') * ι Q' x * (e₂ : CliffordAlgebra Q') = ι Q' y) :
    (scaleHom Q Q' d h e₁ : CliffordAlgebra Q) * ι Q x * (scaleHom Q Q' d h e₂ : CliffordAlgebra Q) = ι Q y := by
  have := congrArg (fun z => phi d h z 1 0) hxy
  simp only [map_mul, phi_even, phi_ι] at this
  simpa [phiVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] using this

/-! ### The Clifford group $G^+$ -/

/-- An element $a \in G^+(V,Q')$ as an element of $A^+(V,Q')$. -/
def evenOfM0 (a : M0 Q') : even Q' := ⟨(a : (CliffordAlgebra Q')ˣ), a.2.1⟩

theorem evenOfM0_mul_inv (a : M0 Q') : evenOfM0 a * evenOfM0 a⁻¹ = 1 :=
  Subtype.ext (by
    change ((a : (CliffordAlgebra Q')ˣ) : CliffordAlgebra Q') * (((a⁻¹ : M0 Q') : (CliffordAlgebra Q')ˣ) :
      CliffordAlgebra Q') = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl)

theorem evenOfM0_inv_mul (a : M0 Q') : evenOfM0 a⁻¹ * evenOfM0 a = 1 :=
  Subtype.ext (by
    change (((a⁻¹ : M0 Q') : (CliffordAlgebra Q')ˣ) : CliffordAlgebra Q') * ((a : (CliffordAlgebra Q')ˣ) :
      CliffordAlgebra Q') = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl)

/-- The unit $f(a)$ of $A(V,Q)$, for $a \in G^+(V,Q')$ ($f(a)^{-1} = f(a^{-1})$). -/
def scaleUnit (d : F) (h : ∀ m, Q' m = d * Q m) (a : M0 Q') : (CliffordAlgebra Q)ˣ where
  val := scaleHom Q Q' d h (evenOfM0 a)
  inv := scaleHom Q Q' d h (evenOfM0 a⁻¹)
  val_inv := by
    rw [← Subalgebra.coe_mul, ← map_mul, evenOfM0_mul_inv, map_one]
    rfl
  inv_val := by
    rw [← Subalgebra.coe_mul, ← map_mul, evenOfM0_inv_mul, map_one]
    rfl

theorem coe_scaleUnit (d : F) (h : ∀ m, Q' m = d * Q m) (a : M0 Q') :
    ((scaleUnit d h a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = scaleHom Q Q' d h (evenOfM0 a) := rfl

theorem coe_scaleUnit_inv (d : F) (h : ∀ m, Q' m = d * Q m) (a : M0 Q') :
    (((scaleUnit d h a)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = scaleHom Q Q' d h (evenOfM0 a⁻¹) := rfl

/-- $f(G^+(V,Q')) \subseteq G^+(V,Q)$. -/
theorem scaleUnit_mem (d : F) (h : ∀ m, Q' m = d * Q m) (a : M0 Q') : scaleUnit d h a ∈ M0 Q := by
  refine ⟨(scaleHom Q Q' d h (evenOfM0 a)).2, fun x => ?_⟩
  obtain ⟨y, hy⟩ := a.2.2 x
  exact ⟨y, (phi_core d h (evenOfM0 a) (evenOfM0 a⁻¹) x y hy.symm).symm⟩

/-- The isomorphism of groups $G^+(V,Q') \cong G^+(V,Q)$ induced by $f$, for $Q' = dQ$, $d \ne 0$. -/
def scaleM0Equiv {d : F} (hd : d ≠ 0) (h : ∀ m, Q' m = d * Q m) : M0 Q' ≃* M0 Q where
  toFun a := ⟨scaleUnit d h a, scaleUnit_mem d h a⟩
  invFun b := ⟨scaleUnit d⁻¹ (scale_inv_h hd h) b, scaleUnit_mem _ _ b⟩
  left_inv a := Subtype.ext (Units.ext
    (congrArg Subtype.val (scaleHom_scaleHom (mul_inv_cancel₀ hd) h (scale_inv_h hd h) (evenOfM0 a))))
  right_inv b := Subtype.ext (Units.ext
    (congrArg Subtype.val (scaleHom_scaleHom (inv_mul_cancel₀ hd) (scale_inv_h hd h) h (evenOfM0 b))))
  map_mul' a b := Subtype.ext (Units.ext (by
    change ((scaleHom Q Q' d h (evenOfM0 (a * b)) : even Q) : CliffordAlgebra Q) =
      ((scaleHom Q Q' d h (evenOfM0 a) : even Q) : CliffordAlgebra Q) *
        ((scaleHom Q Q' d h (evenOfM0 b) : even Q) : CliffordAlgebra Q)
    rw [← Subalgebra.coe_mul, ← map_mul]
    rfl))

/-! ### $\nu$ -/

/-- $\nu(f(a)) = \nu(a)$ for $a \in G^+(V,Q')$, $Q' = dQ$ (both forms nondegenerate). -/
theorem multiplier_scaleM0Equiv {d : F} (hd : d ≠ 0) (h : ∀ m, Q' m = d * Q m)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hQ' : (QuadraticMap.associated Q').Nondegenerate)
    (a : M0 Q') :
    multiplier hQ ⟨scaleM0Equiv hd h a, M0_le_homogeneous (scaleM0Equiv hd h a).2⟩ =
      multiplier hQ' ⟨a, M0_le_homogeneous a.2⟩ := by
  apply Units.ext
  apply (algebraMap F (CliffordAlgebra Q)).injective
  have hA := algebraMap_multiplier hQ' ⟨a, M0_le_homogeneous a.2⟩
  have hE : evenOfM0 a * ⟨reverse (evenOfM0 a : CliffordAlgebra Q'), (reverse_mem_evenOdd_iff Q').2 (evenOfM0 a).2⟩ =
      algebraMap F (even Q') (multiplier hQ' ⟨a, M0_le_homogeneous a.2⟩ : F) :=
    Subtype.ext hA.symm
  rw [algebraMap_multiplier hQ]
  change ((scaleHom Q Q' d h (evenOfM0 a) : even Q) : CliffordAlgebra Q) *
      reverse ((scaleHom Q Q' d h (evenOfM0 a) : even Q) : CliffordAlgebra Q) = _
  rw [reverse_scaleHom d h, ← Subalgebra.coe_mul, ← map_mul, hE, AlgHom.commutes]
  rfl

/-! ### Lemma 3.8 (i) for the form $c\varphi$ -/

section Main

variable (Q)

/-- **Lemma 3.8 (i), the isomorphism** (Shimura, p. 24): for $c \in F^\times$, the $F$-linear ring isomorphism
$f : A^+(V,c\varphi) \to A^+(V,\varphi)$, with $f(\iota'(x)\iota'(y)) = c\,\iota(x)\iota(y)$
(`evenScaleEquiv_ι`). Constructed directly from the universal property of the even Clifford algebra (Shimura adjoins
$\sqrt c$). -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (an F-algebra isomorphism f : A⁺(V,cφ) ≅ A⁺(V,φ))"]
def evenScaleEquiv (c : Fˣ) : even ((c : F) • Q) ≃ₐ[F] even Q :=
  evenScaleEquivOf (c : F) c.ne_zero (fun _ => rfl)

/-- $f(\iota'(x)\iota'(y)) = c\,\iota(x)\iota(y)$. -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (f(ι'(x)ι'(y)) = c ι(x)ι(y))"]
theorem evenScaleEquiv_ι (c : Fˣ) (x y : V) :
    evenScaleEquiv Q c ((even.ι ((c : F) • Q)).bilin x y) = (c : F) • (even.ι Q).bilin x y :=
  scaleHom_ι _ _ _ _

/-- **$f(\xi)^* = f(\xi^*)$** (Shimura, Lemma 3.8 (i), p. 24), for $\xi \in A^+(V,c\varphi)$; $\xi^*$ and $f(\xi)^*$
are the reversions in the ambient Clifford algebras (the reversion preserves the even part). -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (f(ξ)* = f(ξ*))"]
theorem reverse_evenScaleEquiv (c : Fˣ) (ξ : even ((c : F) • Q)) :
    reverse (evenScaleEquiv Q c ξ : CliffordAlgebra Q) =
      evenScaleEquiv Q c ⟨reverse (ξ : CliffordAlgebra ((c : F) • Q)),
        (reverse_mem_evenOdd_iff ((c : F) • Q)).2 ξ.2⟩ :=
  reverse_scaleHom _ _ ξ

/-- **$f(G^+(V,c\varphi)) = G^+(V,\varphi)$** (Shimura, Lemma 3.8 (i), p. 24), as an isomorphism of groups
$G^+(V,c\varphi) \to G^+(V,\varphi)$ whose underlying element is $f(a)$ (`coe_evenScaleM0Equiv`). Here
$G^+(V,\varphi)$ is `Cassels.M0 Q` (units of $A(V,\varphi)$ lying in $A^+$ and normalizing $V$). -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (f(G⁺(V,cφ)) = G⁺(V,φ))"]
def evenScaleM0Equiv (c : Fˣ) : M0 ((c : F) • Q) ≃* M0 Q :=
  scaleM0Equiv c.ne_zero (fun _ => rfl)

/-- The element $f(a)$ of $G^+(V,\varphi)$ is the image of $a \in A^+(V,c\varphi)$ under `evenScaleEquiv`. -/
theorem coe_evenScaleM0Equiv (c : Fˣ) (a : M0 ((c : F) • Q)) :
    (((evenScaleM0Equiv Q c a : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      evenScaleEquiv Q c ⟨((a : (CliffordAlgebra ((c : F) • Q))ˣ) : CliffordAlgebra ((c : F) • Q)), a.2.1⟩ :=
  rfl

/-- **$f(G^+(V,c\varphi)) = G^+(V,\varphi)$, set-theoretically** (Shimura, Lemma 3.8 (i), p. 24): a unit $b$ of
$A(V,\varphi)$ is in $G^+(V,\varphi)$ if and only if it is $f(a)$ for some $a \in G^+(V,c\varphi)$. -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (f(G⁺(V,cφ)) = G⁺(V,φ), set form)"]
theorem mem_M0_iff_exists_evenScale (c : Fˣ) (b : (CliffordAlgebra Q)ˣ) :
    b ∈ M0 Q ↔ ∃ a : M0 ((c : F) • Q), ((evenScaleM0Equiv Q c a : M0 Q) : (CliffordAlgebra Q)ˣ) = b := by
  constructor
  · intro hb
    exact ⟨(evenScaleM0Equiv Q c).symm ⟨b, hb⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    exact (evenScaleM0Equiv Q c a).2

/-- **$\tau(a) = \tau(f(a))$** (Shimura, Lemma 3.8 (i), p. 24), for $a \in G^+(V,c\varphi)$: the two linear maps
$x \mapsto a^{-1}xa$ of $V$ (in $A(V,c\varphi)$ and in $A(V,\varphi)$ respectively) coincide. -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (τ(a) = τ(f(a)))"]
theorem tau_evenScaleM0Equiv (c : Fˣ) (a : M0 ((c : F) • Q)) :
    tau (Subgroup.inclusion M0_le (evenScaleM0Equiv Q c a)) = tau (Subgroup.inclusion M0_le a) := by
  ext x
  symm
  apply cliffordι_injective Q
  have h1 := tau_spec (Subgroup.inclusion M0_le a) x
  have h2 := phi_core (Q := Q) (c : F) (fun _ => rfl) (evenOfM0 a⁻¹) (evenOfM0 a) x
    (tau (Subgroup.inclusion M0_le a) x) h1.symm
  rw [tau_spec (Subgroup.inclusion M0_le (evenScaleM0Equiv Q c a)) x]
  exact h2.symm

/-- **$\nu(a) = \nu(f(a))$** (Shimura, Lemma 3.8 (i), p. 24), for $a \in G^+(V,c\varphi)$, with $\varphi$ and
$c\varphi$ nondegenerate. -/
@[kb "shimura2004" "Lemma 3.8 (i), p. 24 (ν(a) = ν(f(a)))"]
theorem multiplier_evenScaleM0Equiv (c : Fˣ) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQ' : (QuadraticMap.associated ((c : F) • Q)).Nondegenerate) (a : M0 ((c : F) • Q)) :
    multiplier hQ ⟨evenScaleM0Equiv Q c a, M0_le_homogeneous (evenScaleM0Equiv Q c a).2⟩ =
      multiplier hQ' ⟨a, M0_le_homogeneous a.2⟩ :=
  multiplier_scaleM0Equiv c.ne_zero (fun _ => rfl) hQ hQ' a

end Main

end QuadFormsKB.Shimura2004
