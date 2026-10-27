import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec58Hasse
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Witt.Cancellation

open scoped TensorProduct
open Quaternion QuadFormsKB.Quat QuadFormsKB.OMeara.Quaternions57 QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Class58

open Hasse58 CSA52 Sp58

universe u

section Diag

variable {F : Type u} [Field F]

/-- The diagonal quadratic form $\langle f_0\rangle \perp \cdots \perp \langle f_{n-1}\rangle$ on $F^n$ with
unit weights $f_i$ (0-based): $x \mapsto \sum_i f_i x_i^2$. -/
abbrev dg {n : ℕ} (f : Fin n → Fˣ) : QuadraticForm F (Fin n → F) :=
  weightedSumSquares F (fun i => (f i : F))

theorem dg_apply {n : ℕ} (f : Fin n → Fˣ) (x : Fin n → F) :
    dg f x = ∑ i, (f i : F) * x i ^ 2 := by
  simp [dg, weightedSumSquares_apply, pow_two, smul_eq_mul]

theorem dg_single {n : ℕ} (f : Fin n → Fˣ) (i : Fin n) : dg f (Pi.single i 1) = f i := by
  rw [dg_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- Scaling the weights by squares of units gives an isometric form. -/
theorem equivalent_dg_of_sq {n : ℕ} (f g : Fin n → Fˣ) (u : Fin n → Fˣ) (h : ∀ i, g i * u i ^ 2 = f i) :
    (dg f : QuadraticForm F (Fin n → F)).Equivalent (dg g) :=
  ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares u
    (fun i => by simpa using congrArg Units.val (h i))⟩

/-- The scalar multiple $c\,\mathrm{dg}(f)$ is the diagonal form with weights $c f_i$. -/
theorem smul_dg {n : ℕ} (c : F) (f : Fin n → Fˣ) :
    c • (dg f : QuadraticForm F (Fin n → F)) = weightedSumSquares F (fun i => c * (f i : F)) := by
  ext x
  simp [weightedSumSquares_apply, Finset.mul_sum, smul_eq_mul, mul_assoc]

section Gen

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem Equivalent.smul {Q : QuadraticForm F V} {Q' : QuadraticForm F W} (c : F)
    (h : Q.Equivalent Q') : (c • Q).Equivalent (c • Q') := by
  obtain ⟨e⟩ := h
  exact ⟨{ e.toLinearEquiv with map_app' := fun x => by simp [e.map_app] }⟩

/-- $c' Q \cong c Q$ if $c' = t^2 c$ for a unit $t$ (the map $x \mapsto t x$). -/
theorem equivalent_smul_of_sq {Q : QuadraticForm F V} (c c' t : F) (ht : t ≠ 0) (h : c' = t ^ 2 * c) :
    (c' • Q).Equivalent (c • Q) :=
  ⟨{ (LinearEquiv.smulOfNeZero F V t ht) with
    map_app' := fun x => by
      show (c • Q) (t • x) = (c' • Q) x
      simp only [smul_apply, QuadraticMap.map_smul, h, smul_eq_mul]
      ring }⟩

end Gen

end Diag

/-! ### Orthogonal bases and diagonal forms -/

section Geom

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem bil_dg {n : ℕ} (f : Fin n → Fˣ) (x y : Fin n → F) :
    bil (dg f : QuadraticForm F (Fin n → F)) x y = ∑ i, (f i : F) * (x i * y i) := by
  have h := two_mul_bil (dg f : QuadraticForm F (Fin n → F)) x y
  rw [dg_apply, dg_apply, dg_apply] at h
  have h2 : (2 : F) * bil (dg f : QuadraticForm F (Fin n → F)) x y =
      2 * ∑ i, (f i : F) * (x i * y i) := by
    rw [h, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  exact mul_left_cancel₀ (two_ne_zero' (F := F)) h2

/-- A basis of pairwise orthogonal anisotropic vectors makes the space regular. -/
theorem nondegenerate_of_orthogonalBasis {n : ℕ} (X : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X)
    (h : ∀ i, Q (X i) ≠ 0) : (QuadraticMap.associated Q).Nondegenerate := by
  set B : LinearMap.BilinForm F V := QuadraticMap.associated Q with hB
  have hO : B.iIsOrtho X := by
    intro i j hij
    show B (X i) (X j) = 0
    exact hX i j hij
  refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self _ X hO).mpr
    fun i => ?_
  show B (X i) (X i) ≠ 0
  show bil Q _ _ ≠ 0
  rw [bil_self]
  exact h i

theorem isOrthogonalBasis_pi {n : ℕ} (f : Fin n → Fˣ) :
    IsOrthogonalBasis (dg f : QuadraticForm F (Fin n → F)) (Pi.basisFun F (Fin n)) := by
  intro i j hij
  rw [Pi.basisFun_apply, Pi.basisFun_apply, bil_dg]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk; simp [hij.symm]
  · simp [Pi.single_apply, hk]

/-- **The diagonal form is regular.** -/
theorem dg_nondegenerate {n : ℕ} (f : Fin n → Fˣ) :
    (QuadraticMap.associated (dg f : QuadraticForm F (Fin n → F))).Nondegenerate :=
  nondegenerate_of_orthogonalBasis (Pi.basisFun F (Fin n)) (isOrthogonalBasis_pi f) fun i => by
    rw [Pi.basisFun_apply, dg_single]; exact (f i).ne_zero

/-- **A space with an orthogonal basis is isometric to the diagonal form of the values of the basis.** -/
theorem equivalent_dg_of_orthogonalBasis {n : ℕ} (X : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X)
    (f : Fin n → Fˣ) (hf : ∀ i, (f i : F) = Q (X i)) : Q.Equivalent (dg f) := by
  have hO : (QuadraticMap.associated Q : LinearMap.BilinForm F V).IsOrthoᵢ X := by
    rw [LinearMap.isOrthoᵢ_def]
    exact hX
  have h1 := basisRepr_eq_of_iIsOrtho Q X hO
  have h2 : (fun i => Q (X i)) = fun i => ((f i : Fˣ) : F) := funext fun i => (hf i).symm
  rw [h2] at h1
  show Q.Equivalent (weightedSumSquares F fun i => ((f i : Fˣ) : F))
  rw [← h1]
  exact ⟨Q.isometryEquivBasisRepr X⟩

end Geom

/-! ### The invariants of a diagonal form and of a space -/

section Values

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {Q' : QuadraticForm F W}

/-- The function $i \mapsto Q(X_i)$ of the values of an orthogonal basis of a regular space, as units. The
list `Rev.values` of Sec58Hasse is `List.ofFn` of this function. -/
def vf (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) : Fin n → Fˣ :=
  fun i => Units.mk0 (Q (X i)) ((isOrthAniso_basis hQ X hX).aniso i)

theorem values_eq_ofFn (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) : Rev.values hQ X hX = List.ofFn (vf hQ X hX) := rfl

theorem equivalent_dg_vf (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (hX : IsOrthogonalBasis Q X) : Q.Equivalent (dg (vf hQ X hX)) :=
  equivalent_dg_of_orthogonalBasis X hX _ (fun _ => rfl)

/-- **Equal invariants of two value functions**: the products agree up to a square of a unit (equal
discriminants) and the Hasse algebras of the value lists are similar. -/
def SameInv {n : ℕ} (f g : Fin n → Fˣ) : Prop :=
  (∃ t : Fˣ, ∏ i, g i = t ^ 2 * ∏ i, f i) ∧
    IsBrauerEquivalent (hasseAlg (List.ofFn f)) (hasseAlg (List.ofFn g))

theorem SameInv.symm {n : ℕ} {f g : Fin n → Fˣ} (h : SameInv f g) : SameInv g f := by
  obtain ⟨⟨t, ht⟩, hb⟩ := h
  refine ⟨⟨t⁻¹, ?_⟩, hb.symm⟩
  rw [ht]; group

theorem SameInv.trans {n : ℕ} {f g h : Fin n → Fˣ} (h1 : SameInv f g) (h2 : SameInv g h) :
    SameInv f h := by
  obtain ⟨⟨t, ht⟩, hb⟩ := h1
  obtain ⟨⟨s, hs⟩, hc⟩ := h2
  exact ⟨⟨s * t, by rw [hs, ht, mul_pow, mul_assoc]⟩, hb.trans hc⟩

/-- Two orthogonal bases of a regular space have the same invariants (the discriminant is well defined
modulo squares, and 58:2). -/
theorem sameInv_of_bases (hQ : (QuadraticMap.associated Q).Nondegenerate) {n : ℕ}
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    SameInv (vf hQ X hX) (vf hQ Y hY) := by
  refine ⟨?_, isBrauerEquivalent_hasseAlg_values hQ X Y hX hY⟩
  obtain ⟨t, ht⟩ := Rev.exists_prod_values_eq hQ X Y hX hY
  rw [values_eq_ofFn, values_eq_ofFn, List.prod_ofFn, List.prod_ofFn] at ht
  exact ⟨t, ht⟩

theorem bil_map (e : Q.IsometryEquiv Q') (x y : V) : bil Q' (e x) (e y) = bil Q x y := by
  have h1 := two_mul_bil Q x y
  have h2 := two_mul_bil Q' (e x) (e y)
  rw [← map_add, e.map_app, e.map_app, e.map_app] at h2
  exact mul_left_cancel₀ (two_ne_zero' (F := F)) (h2.trans h1.symm)

/-- **Isometric regular spaces have the same invariants** (for any orthogonal bases). -/
theorem sameInv_of_equivalent (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQ' : (QuadraticMap.associated Q').Nondegenerate) (e : Q.IsometryEquiv Q') {n : ℕ}
    (X : Basis (Fin n) F V) (Y : Basis (Fin n) F W) (hX : IsOrthogonalBasis Q X)
    (hY : IsOrthogonalBasis Q' Y) : SameInv (vf hQ X hX) (vf hQ' Y hY) := by
  let Y' : Basis (Fin n) F W := X.map e.toLinearEquiv
  have hY' : IsOrthogonalBasis Q' Y' := fun i j hij => by
    simp only [Y', Basis.map_apply, IsometryEquiv.coe_toLinearEquiv]
    rw [bil_map]; exact hX i j hij
  have h := sameInv_of_bases hQ' Y' Y hY' hY
  have : vf hQ' Y' hY' = vf hQ X hX := by
    funext i; apply Units.ext
    simp [vf, Y']
  rwa [this] at h

/-- If the diagonal forms with equal invariants are isometric (`core`), then spaces with equal invariants
are isometric; conversely isometric spaces have equal invariants. -/
theorem equivalent_iff_sameInv (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQ' : (QuadraticMap.associated Q').Nondegenerate) {n : ℕ}
    (X : Basis (Fin n) F V) (Y : Basis (Fin n) F W) (hX : IsOrthogonalBasis Q X)
    (hY : IsOrthogonalBasis Q' Y)
    (core : ∀ f g : Fin n → Fˣ, SameInv f g →
      (dg f : QuadraticForm F (Fin n → F)).Equivalent (dg g)) :
    Q.Equivalent Q' ↔ SameInv (vf hQ X hX) (vf hQ' Y hY) := by
  constructor
  · rintro ⟨e⟩
    exact sameInv_of_equivalent hQ hQ' e X Y hX hY
  · intro h
    exact (equivalent_dg_vf hQ X hX).trans ((core _ _ h).trans (equivalent_dg_vf hQ' Y hY).symm)

end Values

/-! ### Brauer computations -/

section BrauerComp

variable {F : Type u} [Field F] [Invertible (2 : F)]

theorem SameInv.cls_eq {n : ℕ} {f g : Fin n → Fˣ} (h : SameInv f g) :
    Hasse58.cls (hasseAlg (List.ofFn f)) = Hasse58.cls (hasseAlg (List.ofFn g)) :=
  cls_eq_iff.2 h.2

theorem cls_ternary (a b c : Fˣ) :
    B (-1) (-1) * Hasse58.cls (hasseAlg [a, b, c]) = B (-(a * b)) (-(b * c)) := by
  have h := cls_eq_iff.2 (isBrauerEquivalent_hasseAlg_ternary a b c)
  rwa [cls_tensor] at h

theorem B_ident (a b c : Fˣ) : B (-(b * c)) (-(c * a)) = B (-(a * b)) (-(b * c)) := by
  rw [neg_eq_neg_one_mul (b * c), neg_eq_neg_one_mul (c * a), neg_eq_neg_one_mul (a * b)]
  simp only [B_mul_right, B_self, B_comm, mul_comm, mul_left_comm, B_mul_self, mul_one, mul_assoc]

theorem cls_hasseAlg_cons_one (l : List Fˣ) :
    Hasse58.cls (hasseAlg (1 :: l)) = Hasse58.cls (hasseAlg l) := by
  rw [cls_hasseAlg_eq, cls_hasseAlg_eq, Rev.cls_hasseAlg_cons, B_one_left, one_mul]

theorem nonempty_algEquiv_of_B_eq {α β α' β' : Fˣ} (h : B α β = B α' β') :
    Nonempty (ℍ[F, (α : F), (β : F)] ≃ₐ[F] ℍ[F, (α' : F), (β' : F)]) :=
  Rev.nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq (A := qs α β) (A' := qs α' β')
    (cls_eq_iff.1 h)
    ((QuaternionAlgebra.finrank_eq_four _ _ _).trans (QuaternionAlgebra.finrank_eq_four _ _ _).symm)

end BrauerComp

/-! ### The pure quaternions as a diagonal form, and ternary forms -/

section Ternary

variable {F : Type u} [Field F] [Invertible (2 : F)]

theorem smul_dg' {n : ℕ} (D : Fˣ) (f : Fin n → Fˣ) :
    (D : F) • (dg f : QuadraticForm F (Fin n → F)) = dg (fun i => D * f i) := by
  ext x
  simp [Finset.mul_sum, mul_assoc]

/-- Coordinates of a pure quaternion: $x_1 i + x_2 j + x_3 k \mapsto (x_1,x_2,x_3)$. -/
def pureEquiv (α β : F) : pureSubmodule α β ≃ₗ[F] (Fin 3 → F) where
  toFun p := ![(p : ℍ[F,α,β]).imI, (p : ℍ[F,α,β]).imJ, (p : ℍ[F,α,β]).imK]
  invFun x := ⟨⟨0, x 0, x 1, x 2⟩, rfl⟩
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  left_inv p := by
    apply Subtype.ext
    have h := mem_pureSubmodule.1 p.2
    ext <;> simp [h]
  right_inv x := by ext i; fin_cases i <;> rfl

/-- The space of pure quaternions $(\alpha,\beta)^\circ$ is $\langle -\alpha\rangle \perp \langle -\beta\rangle
\perp \langle \alpha\beta\rangle$ (O'Meara 1963, §57B, p. 146). -/
theorem pure_equivalent_dg (α β : Fˣ) :
    (pureQuadraticForm (α : F) (β : F)).Equivalent (dg ![-α, -β, α * β]) :=
  ⟨{ pureEquiv (α : F) (β : F) with
    map_app' := fun p => by
      have h := mem_pureSubmodule.1 p.2
      rw [dg_apply, Fin.sum_univ_three, pureQuadraticForm_apply, nrd]
      simp [pureEquiv, h]
      ring }⟩

theorem dg_ternary_equiv_pure (a b c : Fˣ) :
    (dg ![a, b, c] : QuadraticForm F (Fin 3 → F)).Equivalent
      (((a * b * c : Fˣ) : F) • pureQuadraticForm ((-(b * c) : Fˣ) : F) ((-(c * a) : Fˣ) : F)) := by
  have h1 := Equivalent.smul ((a * b * c : Fˣ) : F) (pure_equivalent_dg (F := F) (-(b * c)) (-(c * a)))
  rw [smul_dg'] at h1
  refine (equivalent_dg_of_sq ![a, b, c] _ ![(b * c)⁻¹, (a * c)⁻¹, (a * b * c)⁻¹] ?_).trans h1.symm
  intro i
  fin_cases i <;> (apply Units.ext; simp; field_simp)

/-- Ternary case of the classification (the core of 58:4), for explicit value triples. -/
theorem equivalent_dg_ternary_aux (a b c a' b' c' t : Fˣ) (ht : a' * b' * c' = t ^ 2 * (a * b * c))
    (hb : Hasse58.cls (hasseAlg [a, b, c]) = Hasse58.cls (hasseAlg [a', b', c'])) :
    (dg ![a, b, c] : QuadraticForm F (Fin 3 → F)).Equivalent (dg ![a', b', c']) := by
  have hB : B (-(b * c)) (-(c * a)) = B (-(b' * c')) (-(c' * a')) := by
    rw [B_ident a b c, B_ident a' b' c', ← cls_ternary a b c, ← cls_ternary a' b' c', hb]
  obtain ⟨e⟩ := nonempty_algEquiv_of_B_eq hB
  have tf := QuatIso57.tfae_iso (F := F) (γ := ((-(b' * c') : Fˣ) : F)) (δ := ((-(c' * a') : Fˣ) : F))
    (-(b * c)).ne_zero (-(c * a)).ne_zero
  have hP : (pureQuadraticForm ((-(b * c) : Fˣ) : F) ((-(c * a) : Fˣ) : F)).Equivalent
      (pureQuadraticForm ((-(b' * c') : Fˣ) : F) ((-(c' * a') : Fˣ) : F)) :=
    (tf.out 1 3).1 (Nonempty.intro e)
  have hD : (((a' * b' * c' : Fˣ)) : F) = (t : F) ^ 2 * ((a * b * c : Fˣ) : F) := by
    rw [ht]; simp
  refine (dg_ternary_equiv_pure a b c).trans ?_
  refine (Equivalent.smul _ hP).trans ?_
  exact (equivalent_smul_of_sq _ _ (t : F) t.ne_zero hD).symm.trans (dg_ternary_equiv_pure a' b' c').symm

end Ternary

/-! ### Splitting off a leading value, and the classification in dimension at most three -/

section Cons

variable {F : Type u} [Field F] [Invertible (2 : F)]

/-- $F^{m+1} \cong F \times F^m$ (first coordinate and the rest). -/
def consEquiv (m : ℕ) : (Fin (m + 1) → F) ≃ₗ[F] (Fin 1 → F) × (Fin m → F) where
  toFun x := (fun _ => x 0, Fin.tail x)
  invFun p := Fin.cons (p.1 0) p.2
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [Fin.tail]
  map_smul' c x := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [Fin.tail]
  left_inv x := by simp [Fin.cons_self_tail]
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) (by simp)
    fin_cases i; simp

theorem equivalent_dg_cons {m : ℕ} (c : Fˣ) (f : Fin m → Fˣ) :
    (dg (Fin.cons c f : Fin (m + 1) → Fˣ) : QuadraticForm F (Fin (m + 1) → F)).Equivalent
      ((dg (fun _ : Fin 1 => c) : QuadraticForm F (Fin 1 → F)).prod (dg f)) :=
  ⟨{ consEquiv m with
    map_app' := fun x => by
      simp [Fin.sum_univ_succ, QuadraticMap.prod_apply, consEquiv, Fin.tail] }⟩

theorem equivalent_dg_cons_congr {m : ℕ} (c : Fˣ) {f g : Fin m → Fˣ}
    (h : (dg f : QuadraticForm F (Fin m → F)).Equivalent (dg g)) :
    (dg (Fin.cons c f : Fin (m + 1) → Fˣ) : QuadraticForm F (Fin (m + 1) → F)).Equivalent
      (dg (Fin.cons c g : Fin (m + 1) → Fˣ)) := by
  obtain ⟨e⟩ := h
  have e2 : ((dg (fun _ : Fin 1 => c) : QuadraticForm F (Fin 1 → F)).prod (dg f)).Equivalent
      ((dg (fun _ : Fin 1 => c) : QuadraticForm F (Fin 1 → F)).prod (dg g)) :=
    ⟨{ LinearEquiv.prodCongr (LinearEquiv.refl F (Fin 1 → F)) e.toLinearEquiv with
      map_app' := fun x => by simp [QuadraticMap.prod_apply] }⟩
  exact ((equivalent_dg_cons c f).trans e2).trans (equivalent_dg_cons c g).symm

/-- Witt cancellation of a leading value. -/
theorem equivalent_of_cons {m : ℕ} (c : Fˣ) {f g : Fin m → Fˣ}
    (h : (dg (Fin.cons c f : Fin (m + 1) → Fˣ) : QuadraticForm F (Fin (m + 1) → F)).Equivalent
      (dg (Fin.cons c g : Fin (m + 1) → Fˣ))) :
    (dg f : QuadraticForm F (Fin m → F)).Equivalent (dg g) :=
  QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated
    (dg_nondegenerate (fun _ : Fin 1 => c)) (dg_nondegenerate f)
    (((equivalent_dg_cons c f).symm.trans h).trans (equivalent_dg_cons c g))

theorem sameInv_cons_one {m : ℕ} {f g : Fin m → Fˣ} (h : SameInv f g) :
    SameInv (Fin.cons 1 f : Fin (m + 1) → Fˣ) (Fin.cons 1 g : Fin (m + 1) → Fˣ) := by
  obtain ⟨⟨t, ht⟩, hb⟩ := h
  refine ⟨⟨t, by simpa [Fin.prod_univ_succ] using ht⟩, cls_eq_iff.1 ?_⟩
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [cls_hasseAlg_cons_one, cls_hasseAlg_cons_one]
  exact cls_eq_iff.2 hb

/-- **The classification of diagonal forms of dimension at most three** (the core of 58:4). -/
theorem equivalent_dg_of_sameInv_le_three {n : ℕ} (hn : n ≤ 3) (f g : Fin n → Fˣ) (h : SameInv f g) :
    (dg f : QuadraticForm F (Fin n → F)).Equivalent (dg g) := by
  obtain ⟨⟨t, ht⟩, hb⟩ := h
  have hcls : Hasse58.cls (hasseAlg (List.ofFn f)) = Hasse58.cls (hasseAlg (List.ofFn g)) :=
    cls_eq_iff.2 hb
  interval_cases n
  · have : f = g := funext fun i => i.elim0
    rw [this]
  · refine equivalent_dg_of_sq f g (fun _ => t⁻¹) fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [Fin.prod_univ_one] at ht
    apply Units.ext; simp [ht]
  · have hf : (Fin.cons 1 f : Fin 3 → Fˣ) = ![1, f 0, f 1] := by
      funext i; fin_cases i <;> rfl
    have hg : (Fin.cons 1 g : Fin 3 → Fˣ) = ![1, g 0, g 1] := by
      funext i; fin_cases i <;> rfl
    refine equivalent_of_cons 1 ?_
    rw [hf, hg]
    refine equivalent_dg_ternary_aux 1 (f 0) (f 1) 1 (g 0) (g 1) t ?_ ?_
    · simpa [Fin.prod_univ_two] using ht
    · have e1 : Hasse58.cls (hasseAlg [1, f 0, f 1]) = Hasse58.cls (hasseAlg [f 0, f 1]) :=
        cls_hasseAlg_cons_one _
      have e2 : Hasse58.cls (hasseAlg [1, g 0, g 1]) = Hasse58.cls (hasseAlg [g 0, g 1]) :=
        cls_hasseAlg_cons_one _
      rw [e1, e2]
      exact hcls
  · have hf : f = ![f 0, f 1, f 2] := by funext i; fin_cases i <;> rfl
    have hg : g = ![g 0, g 1, g 2] := by funext i; fin_cases i <;> rfl
    have := equivalent_dg_ternary_aux (F := F) (f 0) (f 1) (f 2) (g 0) (g 1) (g 2) t
      (by simpa [Fin.prod_univ_three] using ht) hcls
    rwa [← hf, ← hg] at this

end Cons

/-! ### 58:4 -/

section Main584

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {Q' : QuadraticForm F W}

/-- `SameInv` of the value functions of two orthogonal bases, written with the discriminants
$\prod Q(X_i)$, $\prod Q'(Y_i)$ in $F$ and the Hasse algebras of the value lists. -/
theorem sameInv_iff (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQ' : (QuadraticMap.associated Q').Nondegenerate) {n : ℕ} (X : Basis (Fin n) F V)
    (Y : Basis (Fin n) F W) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q' Y) :
    SameInv (vf hQ X hX) (vf hQ' Y hY) ↔
      ((∃ t : Fˣ, ∏ i, Q' (Y i) = (t : F) ^ 2 * ∏ i, Q (X i)) ∧
        IsBrauerEquivalent (hasseAlg (Rev.values hQ X hX)) (hasseAlg (Rev.values hQ' Y hY))) := by
  unfold SameInv
  rw [← values_eq_ofFn, ← values_eq_ofFn]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa [vf] using congrArg Units.val ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Units.ext (by simpa [vf] using ht)⟩

/-- **O'Meara 58:4** (1963, p. 152): *$V$ and $W$ are regular $n$-ary quadratic spaces with $n \le 3$.  Then $V$
is isometric to $W$ if and only if $\dim V = \dim W$, $dV = dW$, $S V \sim S W$.*

**Formalization.**  $V, W$ are regular finite-dimensional quadratic spaces over $F$ ($2$ invertible) and
$X, Y$ are orthogonal bases of $V, W$ indexed by `Fin n` (so $\dim V = \dim W = n$ is built in).  The
discriminants are $dV = \prod_i Q(X_i)$ and $dW = \prod_i Q'(Y_i)$ (the determinants of the Gram matrices,
`det_gram_of_isOrthAniso`), compared modulo squares of $F^\times$, and $S V$, $S W$ are the Hasse algebras
`hasseAlg` of the value lists `Rev.values` of these bases, compared by Mathlib's `IsBrauerEquivalent`
(similarity).  By 58:2 and the well-definedness of the discriminant modulo squares the right-hand side does not
depend on the choice of the orthogonal bases (`sameInv_of_bases`).  Dimension $n = 0$ is included (trivial); the
book has $1 \le n \le 3$.

*Proof* (as in the book, with the details in the diagonal form): the unary case is trivial; the ternary case
(`equivalent_dg_ternary_aux`) writes $V^{dV} \cong (\alpha,\beta)^\circ$, applies the ternary rule of 58:3,
$(-1,-1) \otimes S V \sim (\alpha,\beta)$, and 57:8; the binary case adds $\langle 1\rangle$ and cancels it by
Witt (`equivalent_of_cons`).  Instead of scaling the space by $dV$ we use $\langle a,b,c\rangle \cong
(abc)\cdot\langle -bc,-ca,\ldots\rangle$ directly (`dg_ternary_equiv_pure`) and compare $(abc)$ and $(a'b'c')$
which differ by a square. -/
@[kb "omeara1963" "§58, 58:4, p. 152"]
theorem isometric_iff_invariants_of_dim_le_three (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hQ' : (QuadraticMap.associated Q').Nondegenerate) {n : ℕ} (hn : n ≤ 3) (X : Basis (Fin n) F V)
    (Y : Basis (Fin n) F W) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q' Y) :
    Nonempty (Q.IsometryEquiv Q') ↔
      ((∃ t : Fˣ, ∏ i, Q' (Y i) = (t : F) ^ 2 * ∏ i, Q (X i)) ∧
        IsBrauerEquivalent (hasseAlg (Rev.values hQ X hX)) (hasseAlg (Rev.values hQ' Y hY))) :=
  (equivalent_iff_sameInv hQ hQ' X Y hX hY (equivalent_dg_of_sameInv_le_three hn)).trans
    (sameInv_iff hQ hQ' X Y hX hY)

end Main584

/-! ### Splitting quaternion algebras and isotropy (58:6) -/

section Isotropy

variable {F : Type u} [Field F] [Invertible (2 : F)]

/-- The class of $(\alpha,\beta)$ is trivial iff $\alpha\xi^2 + \beta\eta^2 = 1$ is solvable (57:9). -/
theorem B_eq_one_iff (α β : Fˣ) :
    B α β = 1 ↔ ∃ ξ η : F, (α : F) * ξ ^ 2 + (β : F) * η ^ 2 = 1 := by
  have tf := QuatIso57.tfae_division (F := F) α.ne_zero β.ne_zero
  constructor
  · intro h
    have h1 : IsBrauerEquivalent (qs α β) CSA52.one := cls_eq_iff.1 (h.trans cls_one.symm)
    have h2 := h1.trans isBrauerEquivalent_quaternion_one_neg_one.symm
    obtain ⟨e⟩ := Rev.nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq
      (A := qs α β) (A' := quaternion (1 : F) (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero)) h2
      ((QuaternionAlgebra.finrank_eq_four _ _ _).trans (QuaternionAlgebra.finrank_eq_four _ _ _).symm)
    exact (tf.out 1 5).1 (Nonempty.intro e)
  · intro h
    obtain ⟨e⟩ := (tf.out 1 5).2 h
    have h1 : IsBrauerEquivalent (qs α β)
        (quaternion (1 : F) (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero)) := isBrauerEquivalent_of_algEquiv e
    exact (cls_eq_iff.2 (h1.trans isBrauerEquivalent_quaternion_one_neg_one)).trans (cls_one (F := F))

theorem mul_eq_one_iff_eq (w : Br F) : B (-1) (-1) * w = 1 ↔ w = B (-1) (-1) := by
  constructor
  · intro h
    calc w = B (-1) (-1) * (B (-1) (-1) * w) := (B_sq_mul _ _ w).symm
      _ = B (-1) (-1) := by rw [h, mul_one]
  · intro h; rw [h]; exact B_mul_self _ _

theorem ternary_rep_iff (a b c : Fˣ) :
    (∃ ξ η : F, ((-(a * b) : Fˣ) : F) * ξ ^ 2 + ((-(b * c) : Fˣ) : F) * η ^ 2 = 1) ↔
      ∃ x : Fin 3 → F, x ≠ 0 ∧ (dg ![a, b, c] : QuadraticForm F (Fin 3 → F)) x = 0 := by
  have hb := b.ne_zero
  have h2 := two_ne_zero' (F := F)
  constructor
  · rintro ⟨ξ, η, h⟩
    refine ⟨![b * ξ, 1, b * η], fun h0 => ?_, ?_⟩
    · have := congrFun h0 1
      simp at this
    · rw [dg_apply, Fin.sum_univ_three]
      simp only [Units.val_neg, Units.val_mul] at h
      simp
      linear_combination (-(b : F)) * h
  · rintro ⟨x, hx, h⟩
    rw [dg_apply, Fin.sum_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h
    simp only [Units.val_neg, Units.val_mul]
    by_cases hy : x 1 = 0
    · rw [hy] at h
      have hx0 : x 0 ≠ 0 := by
        intro h0
        rw [h0] at h
        have : (c : F) * x 2 ^ 2 = 0 := by linear_combination h
        have h2' : x 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 this).resolve_left c.ne_zero)
        apply hx
        funext i; fin_cases i <;> simp [h0, hy, h2']
      have hx2 : x 2 ≠ 0 := by
        intro h0
        rw [h0] at h
        have : (a : F) * x 0 ^ 2 = 0 := by linear_combination h
        exact hx0 (pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 this).resolve_left a.ne_zero))
      have ha := a.ne_zero
      have hc := c.ne_zero
      refine ⟨(((a : F) * b)⁻¹ - 1) / 2, (1 + ((a : F) * b)⁻¹) * x 2 / (2 * x 0), ?_⟩
      have hcc : (c : F) = -(a : F) * (x 0 / x 2) ^ 2 := by
        field_simp
        linear_combination h
      rw [show -((b : F) * c) = -(b : F) * c by ring, hcc]
      field_simp
      ring
    · refine ⟨x 0 / (b * x 1), x 2 / (b * x 1), ?_⟩
      field_simp
      linear_combination (-1 : F) * h

theorem isotropic_dg_ternary_iff (f : Fin 3 → Fˣ) :
    (∃ x : Fin 3 → F, x ≠ 0 ∧ (dg f : QuadraticForm F (Fin 3 → F)) x = 0) ↔
      IsBrauerEquivalent (hasseAlg (List.ofFn f)) (qs (-1) (-1)) := by
  have hf : f = ![f 0, f 1, f 2] := by funext i; fin_cases i <;> rfl
  rw [hf]
  rw [← ternary_rep_iff, ← B_eq_one_iff, ← cls_ternary, mul_eq_one_iff_eq]
  have e : List.ofFn ![f 0, f 1, f 2] = [f 0, f 1, f 2] := rfl
  rw [e]
  exact (cls_eq_iff (A := hasseAlg [f 0, f 1, f 2]) (B := qs (-1) (-1)))

theorem isotropic_iff_of_equivalent {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] {Q : QuadraticForm F V} {Q' : QuadraticForm F W} (h : Q.Equivalent Q') :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔ ∃ w : W, w ≠ 0 ∧ Q' w = 0 := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨v, hv, h0⟩
    exact ⟨e v, fun h => hv (e.toLinearEquiv.injective (by simpa using h)), by rw [e.map_app]; exact h0⟩
  · rintro ⟨w, hw, h0⟩
    refine ⟨e.symm w, fun h => hw ?_, ?_⟩
    · simpa using congrArg e h
    · rw [← e.map_app, e.apply_symm_apply]; exact h0

end Isotropy

/-! ### 58:6 -/

section Main586

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- **O'Meara 58:6** (1963, p. 153): *a regular ternary space $V$ is isotropic if and only if
$S V \sim (-1,-1)$.*

**Formalization.**  $V$ is regular with an orthogonal basis $X$ indexed by `Fin 3` (so $\dim V = 3$), $S V$ is the
Hasse algebra `hasseAlg` of the value list of $X$ (independent of $X$ by 58:2), `qs (-1) (-1)` is the quaternion
algebra $(-1,-1)$, and $\sim$ is `IsBrauerEquivalent`; isotropic means $Q(v) = 0$ for some $v \ne 0$.

*Deviation from the book's proof.*  The book writes $V$ isotropic iff $V \cong \langle 1\rangle \perp \langle
-1\rangle \perp \langle -dV\rangle$ and applies 58:4.  Here the equivalence is proved directly: by the ternary rule
of 58:3, $(-1,-1)\otimes S V \sim (-a_0a_1,-a_1a_2)$, and this algebra splits iff $-a_0a_1\xi^2 - a_1a_2\eta^2 = 1$ is
solvable (57:9), iff $a_0x_0^2 + a_1x_1^2 + a_2x_2^2 = 0$ has a nontrivial solution (`ternary_rep_iff`). -/
@[kb "omeara1963" "§58, 58:6, p. 153"]
theorem isotropic_iff_hasseAlg_eq_of_dim_three (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (X : Basis (Fin 3) F V) (hX : IsOrthogonalBasis Q X) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      IsBrauerEquivalent (hasseAlg (Rev.values hQ X hX)) (qs (-1) (-1)) := by
  rw [isotropic_iff_of_equivalent (equivalent_dg_vf hQ X hX), values_eq_ofFn]
  exact isotropic_dg_ternary_iff _

end Main586

/-! ### Quaternary forms of square discriminant (for 58:7a) -/

section Quaternary

variable {K : Type u} [Field K] [Invertible (2 : K)]

theorem cls_quaternary (a b c d : Kˣ) :
    B (-1) (-1) * Hasse58.cls (hasseAlg [a, b, c, d]) =
      B (-(a * b)) (-(b * c)) * B d (a * b * c * d) := by
  have h := cls_eq_iff.2 (isBrauerEquivalent_hasseAlg_quaternary a b c d)
  rwa [cls_tensor, cls_tensor] at h

/-- A quaternary diagonal form whose discriminant $abce = \rho^2$ is a square is isotropic iff
$S \sim (-1,-1)$ (the heart of 58:7a): by the quaternary rule of 58:3 this says $(-ab,-bc)$ splits, and the
form is $abc$ times the norm form of $(-ab,-bc)$ (up to squares), so 57:9 applies. -/
theorem isotropic_dg_quaternary_iff (a b c e ρ : Kˣ) (hρ : a * b * c * e = ρ ^ 2) :
    (∃ x : Fin 4 → K, x ≠ 0 ∧ (dg ![a, b, c, e] : QuadraticForm K (Fin 4 → K)) x = 0) ↔
      IsBrauerEquivalent (hasseAlg [a, b, c, e]) (qs (-1) (-1)) := by
  have hB : B e (a * b * c * e) = 1 := by
    rw [hρ]
    have := B_sq_mul_right e ρ 1
    rwa [mul_one, B_one_right] at this
  have key : IsBrauerEquivalent (hasseAlg [a, b, c, e]) (qs (-1) (-1)) ↔
      B (-(a * b)) (-(b * c)) = 1 := by
    rw [show IsBrauerEquivalent (hasseAlg [a, b, c, e]) (qs (-1) (-1)) ↔
        Hasse58.cls (hasseAlg [a, b, c, e]) = B (-1) (-1) from cls_eq_iff.symm,
      ← mul_eq_one_iff_eq, cls_quaternary, hB, mul_one]
  rw [key, B_eq_one_iff]
  have ha := a.ne_zero
  have hb := b.ne_zero
  have hc := c.ne_zero
  have hρ0 := ρ.ne_zero
  have hρK : (a : K) * b * c * e = (ρ : K) ^ 2 := by
    have := congrArg Units.val hρ
    simpa using this
  have he : (e : K) = (ρ : K) ^ 2 / (a * b * c) := by
    field_simp
    linear_combination hρK
  constructor
  · rintro ⟨x, hx, h⟩
    rw [dg_apply, Fin.sum_univ_four] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three] at h
    have tf := QuatIso57.tfae_division (F := K) (-(a * b)).ne_zero (-(b * c)).ne_zero
    suffices H : ∃ q : ℍ[K, ((-(a * b) : Kˣ) : K), ((-(b * c) : Kˣ) : K)], q ≠ 0 ∧
        nrdQuadraticForm ((-(a * b) : Kˣ) : K) ((-(b * c) : Kˣ) : K) q = 0 from (tf.out 3 5).1 H
    refine ⟨⟨(ρ : K) * x 3 / (a * b * c), x 2 / (a * b), x 0 / (b * c), x 1 / (a * b * c)⟩, ?_, ?_⟩
    · intro h0
      have h0' := QuaternionAlgebra.ext_iff.1 h0
      simp only [QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero, QuaternionAlgebra.imJ_zero,
        QuaternionAlgebra.imK_zero] at h0'
      obtain ⟨h1, h2, h3, h4⟩ := h0'
      apply hx
      funext i
      fin_cases i
      · simpa [hb, hc] using h3
      · simpa [ha, hb, hc] using h4
      · simpa [ha, hb] using h2
      · simpa [ha, hb, hc, hρ0] using h1
    · rw [nrdQuadraticForm_apply, nrd_mk]
      have : (e : K) = (ρ : K) ^ 2 / (a * b * c) := he
      rw [he] at h
      simp only [Units.val_neg, Units.val_mul]
      field_simp
      field_simp at h
      linear_combination h
  · rintro ⟨ξ, η, h⟩
    refine ⟨![b * ξ, 1, b * η, 0], fun h0 => ?_, ?_⟩
    · have := congrFun h0 1
      simp at this
    · rw [dg_apply, Fin.sum_univ_four]
      simp only [Units.val_neg, Units.val_mul] at h
      simp
      linear_combination (-(b : K)) * h

end Quaternary

/-! ### 58:7a -/

section Main587a

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
variable {E : Type u} [Field E] [Algebra F E]

/-- The value of the extension of scalars on $\sum_i t_i \otimes X_i$ for an orthogonal basis $X$. -/
theorem baseChange_sum_tmul {n : ℕ} (X : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (t : Fin n → E)
    (s : Finset (Fin n)) :
    Q.baseChange E (∑ i ∈ s, t i ⊗ₜ[F] X i) = ∑ i ∈ s, algebraMap F E (Q (X i)) * t i ^ 2 := by
  classical
  let _ : Invertible (2 : E) := (Invertible.map (algebraMap F E) 2).copy 2 (map_ofNat _ _).symm
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, QuadraticMap.map_add (Q.baseChange E), ih]
    have hpol : QuadraticMap.polar (Q.baseChange E) (t j ⊗ₜ[F] X j) (∑ i ∈ s, t i ⊗ₜ[F] X i) = 0 := by
      have h1 : QuadraticMap.polar (Q.baseChange E) (t j ⊗ₜ[F] X j) (∑ i ∈ s, t i ⊗ₜ[F] X i) =
          (QuadraticMap.polarBilin (Q.baseChange E)) (t j ⊗ₜ[F] X j) (∑ i ∈ s, t i ⊗ₜ[F] X i) := rfl
      rw [h1, map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      have hp := congrArg (fun B => B (t j ⊗ₜ[F] X j) (t i ⊗ₜ[F] X i))
        (QuadraticForm.polarBilin_baseChange (A := E) Q)
      simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.baseChange_tmul] at hp
      rw [QuadraticMap.polarBilin_apply_apply, hp]
      have h2 := two_mul_bil Q (X j) (X i)
      rw [hX j i hij.symm, mul_zero] at h2
      have h3 : QuadraticMap.polar Q (X j) (X i) = 0 := by
        simp only [QuadraticMap.polar]; linear_combination -h2
      rw [h3, zero_smul]
    rw [hpol, QuadraticForm.baseChange_tmul, add_zero, Algebra.smul_def]
    ring

theorem isotropic_baseChange_iff_aux {n : ℕ} (X : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) :
    (∃ z : E ⊗[F] V, z ≠ 0 ∧ Q.baseChange E z = 0) ↔
      ∃ t : Fin n → E, t ≠ 0 ∧ ∑ i, algebraMap F E (Q (X i)) * t i ^ 2 = 0 := by
  have hsum : ∀ t : Fin n → E, ∑ i, t i ⊗ₜ[F] X i = ∑ i, t i • (X.baseChange E) i := by
    intro t
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hz : ∀ z : E ⊗[F] V, z = ∑ i, ((X.baseChange E).repr z i) ⊗ₜ[F] X i := by
    intro z
    rw [hsum]
    exact ((X.baseChange E).sum_repr z).symm
  constructor
  · rintro ⟨z, hz0, hQ⟩
    refine ⟨fun i => (X.baseChange E).repr z i, ?_, ?_⟩
    · intro h
      apply hz0
      rw [hz z]
      refine Finset.sum_eq_zero fun i _ => ?_
      have := congrFun h i
      simp only [Pi.zero_apply] at this
      rw [this, TensorProduct.zero_tmul]
    · rw [hz z, baseChange_sum_tmul X hX] at hQ
      exact hQ
  · rintro ⟨t, ht, h⟩
    refine ⟨∑ i, t i ⊗ₜ[F] X i, ?_, ?_⟩
    · intro h0
      apply ht
      have hr : ∀ i, (X.baseChange E).repr (∑ i, t i ⊗ₜ[F] X i) i = t i := by
        intro i
        rw [hsum, Basis.repr_sum_self]
      funext i
      rw [← hr i, h0]
      simp
    · rw [baseChange_sum_tmul X hX t Finset.univ]
      exact h

/-- **O'Meara 58:7a** (1963, p. 153): *$V$ is a regular quaternary space with discriminant $d$ and $E = F(\sqrt d)$.
Then $V$ is isotropic if and only if $E(S V) \sim (-1,-1)$.*

**Formalization.**  $V$ is regular with an orthogonal basis $X$ indexed by `Fin 4` (so $\dim V = 4$) and the
discriminant is $d = \prod_i Q(X_i)$ (a representative of $dV$; as in 58:7 the theorem holds for every such
representative).  $E$ is a field extension generated by a square root $r$ of $d$ (`hr`, `hgen`; $E = F(\sqrt d)$,
including the case $E = F$ for square $d$).  *Deviation of notation:* the book writes $E(S V)$ and uses
$S(EV) \cong E(S V)$ (§53B); here $S(EV)$ is taken as the Hasse algebra, over $E$, of the *image in $E$ of the value
list of $X$* (`List.map (Units.map (algebraMap F E))`), which is the Hasse algebra of the orthogonal basis
$1 \otimes X_i$ of $EV$ and is (by 58:2 over $E$) $S(EV)$.  The base-change rule $S(EV) \cong E\,S(V)$ of 58:3
is not formalized.  `Invertible (2 : E)` holds automatically (it is the image of that of $F$) and is only needed to
form `hasseAlg` over $E$.

*Proof.*  58:7 reduces to the isotropy of $EV$, i.e. to a nontrivial solution of $\sum_i Q(X_i) t_i^2 = 0$ in $E$
(`isotropic_baseChange_iff_aux`).  Over $E$ the discriminant $\prod Q(X_i) = r^2$ is a square, and
`isotropic_dg_quaternary_iff` applies (quaternary rule of 58:3: $(-1,-1)\otimes S \sim (-a_0a_1,-a_1a_2)\otimes
(a_3, r^2)$, and 57:9; the form is $a_0a_1a_2$ times the norm form of $(-a_0a_1,-a_1a_2)$).  The book instead
passes to a ternary subspace $U$ and uses 42:12 and 58:6. -/
@[kb "omeara1963" "§58, 58:7a, p. 153"]
theorem isotropic_iff_hasseAlg_baseChange_of_dim_four [Invertible (2 : E)]
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (X : Basis (Fin 4) F V)
    (hX : IsOrthogonalBasis Q X) (r : E) (hr : r ^ 2 = algebraMap F E (∏ i, Q (X i)))
    (hgen : Algebra.adjoin F {r} = ⊤) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      IsBrauerEquivalent
        (hasseAlg ((Rev.values hQ X hX).map (Units.map (algebraMap F E : F →* E))))
        (qs (-1) (-1)) := by
  have hdim : finrank F V = 4 := by rw [finrank_eq_card_basis X]; simp
  have hd : (∏ i, Q (X i)) = (gram Q X).det :=
    (det_gram_of_isOrthAniso (isOrthAniso_basis hQ X hX)).symm
  rw [isotropic_iff_baseChange_isotropic hQ hdim X hd r hr hgen, isotropic_baseChange_iff_aux X hX]
  set vE : Fin 4 → Eˣ := fun i => Units.map (algebraMap F E : F →* E) (vf hQ X hX i) with hvE
  have hvE' : ∀ i, (vE i : E) = algebraMap F E (Q (X i)) := fun i => rfl
  have hlist : (Rev.values hQ X hX).map (Units.map (algebraMap F E : F →* E)) = List.ofFn vE := by
    rw [values_eq_ofFn, List.map_ofFn]; rfl
  have hne : r ≠ 0 := by
    intro h0
    rw [h0] at hr
    have : algebraMap F E (∏ i, Q (X i)) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap F E).injective]
      exact Finset.prod_ne_zero_iff.2 fun i _ => (isOrthAniso_basis hQ X hX).aniso i
    exact this (by simpa using hr.symm)
  have hρ : vE 0 * vE 1 * vE 2 * vE 3 = (Units.mk0 r hne) ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hvE', hr]
    simp [Fin.prod_univ_four, map_mul]
  have hf : vE = ![vE 0, vE 1, vE 2, vE 3] := by funext i; fin_cases i <;> rfl
  rw [hlist, hf]
  have e : List.ofFn ![vE 0, vE 1, vE 2, vE 3] = [vE 0, vE 1, vE 2, vE 3] := rfl
  rw [e, ← isotropic_dg_quaternary_iff _ _ _ _ _ hρ]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [dg_apply, Fin.sum_univ_four]
  simp only [Fin.sum_univ_four]
  simp [hvE']

end Main587a

/-! ### 58:5 -/

section Example585

theorem cls_hasseAlg_ones {F : Type u} [Field F] [Invertible (2 : F)] :
    Hasse58.cls (hasseAlg ([1, 1, 1, 1] : List Fˣ)) = 1 := by
  rw [cls_hasseAlg_eq]
  simp [Rev.cls_hasseAlg_cons, Rev.cls_hasseAlg_nil, B_one_right]

theorem cls_hasseAlg_neg_ones {F : Type u} [Field F] [Invertible (2 : F)] :
    Hasse58.cls (hasseAlg ([-1, -1, -1, -1] : List Fˣ)) = 1 := by
  rw [cls_hasseAlg_eq]
  simp [Rev.cls_hasseAlg_cons, Rev.cls_hasseAlg_nil, B_one_right]
  exact B_mul_self _ _

/-- **O'Meara 58:5** (1963, p. 152), example: over $\mathbb R$ the quadratic spaces
$V = \langle 1\rangle\perp\langle 1\rangle\perp\langle 1\rangle\perp\langle 1\rangle$ and
$W = \langle -1\rangle\perp\langle -1\rangle\perp\langle -1\rangle\perp\langle -1\rangle$ (`dg` of the constant
value functions on $\mathbb R^4$) have the same invariants but are not isometric.  Both have dimension $4$
(both live on `Fin 4 → ℝ`), the discriminant products $1$ and $(-1)^4 = 1$ agree, and both Hasse algebras are
similar to $\mathbb R$ (`SameInv` packages discriminant and Hasse algebra), but $V$ represents $1 > 0$ whereas
every value of $W$ is $\le 0$.  *Reconstruction note:* the machine-read text of the example is garbled; the
spaces are reconstructed as the sums of four copies of $\langle 1\rangle$ and of $\langle -1\rangle$ (the book
says "the real quadratic spaces ... have the same invariants but are not isometric"). -/
@[kb "omeara1963" "§58, 58:5, p. 152"]
theorem example_58_5 [Invertible (2 : ℝ)] :
    SameInv (fun _ : Fin 4 => (1 : ℝˣ)) (fun _ : Fin 4 => (-1 : ℝˣ)) ∧
      ¬ (dg (fun _ : Fin 4 => (1 : ℝˣ)) : QuadraticForm ℝ (Fin 4 → ℝ)).Equivalent
        (dg (fun _ : Fin 4 => (-1 : ℝˣ))) := by
  refine ⟨⟨⟨1, Units.ext (by norm_num)⟩, ?_⟩, ?_⟩
  · refine cls_eq_iff.1 ?_
    have h1 : List.ofFn (fun _ : Fin 4 => (1 : ℝˣ)) = [1, 1, 1, 1] := rfl
    have h2 : List.ofFn (fun _ : Fin 4 => (-1 : ℝˣ)) = [-1, -1, -1, -1] := rfl
    rw [h1, h2, cls_hasseAlg_ones, cls_hasseAlg_neg_ones]
  · rintro ⟨e⟩
    have h := e.map_app (Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)
    rw [dg_apply, dg_apply] at h
    have h1 : ∑ i : Fin 4, ((1 : ℝˣ) : ℝ) * ((Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) i) ^ 2 = 1 := by
      simp [Pi.single_apply]
    have h2 : ∑ i : Fin 4, (((-1 : ℝˣ)) : ℝ) * (e (Pi.single 0 1) i) ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun i _ => by
        have := sq_nonneg (e (Pi.single 0 1) i)
        simp only [Units.val_neg, Units.val_one]
        nlinarith
    linarith

end Example585

end QuadFormsKB.OMeara.Class58
