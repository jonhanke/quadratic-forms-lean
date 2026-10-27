/-
# O'Meara §52A, §52F: tensor products of central simple algebras (52:1, 52:2, 52:10)

**Setting.** $F$ a field; algebras are finite-dimensional associative $F$-algebras with identity
(`[Ring A] [Algebra F A] [FiniteDimensional F A]`).  O'Meara's *central simple algebra* over $F$ is an
algebra that is central (`Algebra.IsCentral F A`: the centre is $F \cdot 1$) and simple
(`IsSimpleRing A`: no two-sided ideals other than $0$ and $A$; in particular $A \ne 0$).  The reciprocal
algebra $A^*$ of §52F is the opposite algebra `Aᵐᵒᵖ`.

**Proves**
* `isCentral_tensorProduct`, `isSimpleRing_tensorProduct_of_isCentral` (**52:1**, the two halves, in the
  stronger form "central simple $\otimes$ simple is simple"), `isCentralSimple_tensorProduct` (**52:1**
  as stated in the book);
* `tensorProduct_equiv_sup` (**52:2**): commuting central simple subalgebras $B$, $C$ of $A$ generate a
  subalgebra isomorphic to $B \otimes_F C$, via $b \otimes c \mapsto bc$; `mem_sup_iff_mem_span_mul`
  (its first assertion: elements of $B \sqcup C$ are sums of products $bc$);
* `tensorProduct_mulOpposite_equiv_end`, `tensorProduct_mulOpposite_equiv_matrix` (**52:10**):
  $A \otimes_F A^* \cong \mathrm{End}_F(A) \cong M_m(F)$ with $m = \dim_F A$.

Reused from Mathlib: `Algebra.IsCentral`, `IsSimpleRing`, `Algebra.TensorProduct`,
`AlgHom.mulLeftRight` (the map $a \otimes b \mapsto (x \mapsto a x b)$), `algEquivMatrix`.
Mathlib has no tensor-product theorem for central or simple algebras, so 52:1 is proved here following
O'Meara's minimal-length argument, with a fixed basis of $B$ in place of the change of basis.

The cancellation law quoted after 52:10 (p. 129), "$A \otimes B \sim A' \otimes B$ implies $A \sim A'$", is
`CSA52.isBrauerEquivalent_of_tensor` in `Sec52F.lean`.
-/
import Mathlib
import QuadFormsKB.Citation

open scoped TensorProduct
open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Coefficients

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  {ι : Type*} [Fintype ι]

/-- The $i$-th coefficient of $z \in A \otimes_F B$ with respect to a basis $(e_i)$ of $B$:
$z = \sum_i \mathrm{coeff}_i(z) \otimes e_i$, and
$\mathrm{coeff}_i(a \otimes b) = e_i^*(b)\, a$ where $e_i^*$ is the $i$-th coordinate functional. -/
def tensorCoeff (e : Basis ι F B) (i : ι) : A ⊗[F] B →ₗ[F] A :=
  (TensorProduct.rid F A).toLinearMap ∘ₗ LinearMap.lTensor A (e.coord i)

@[simp]
theorem tensorCoeff_tmul (e : Basis ι F B) (i : ι) (a : A) (b : B) :
    tensorCoeff e i (a ⊗ₜ b) = e.coord i b • a := by
  simp [tensorCoeff]

/-- Every element of $A \otimes_F B$ is $\sum_i \mathrm{coeff}_i(z) \otimes e_i$. -/
theorem sum_tensorCoeff_tmul (e : Basis ι F B) (z : A ⊗[F] B) :
    ∑ i, tensorCoeff e i z ⊗ₜ e i = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp_rw [tensorCoeff_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    simp
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

theorem tensorCoeff_tmul_one_mul (e : Basis ι F B) (i : ι) (x : A) (z : A ⊗[F] B) :
    tensorCoeff e i ((x ⊗ₜ (1 : B)) * z) = x * tensorCoeff e i z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp [mul_add, hy, hz]

theorem tensorCoeff_mul_tmul_one (e : Basis ι F B) (i : ι) (x : A) (z : A ⊗[F] B) :
    tensorCoeff e i (z * (x ⊗ₜ (1 : B))) = tensorCoeff e i z * x := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp [add_mul, hy, hz]

theorem eq_zero_of_tensorCoeff_eq_zero (e : Basis ι F B) {z : A ⊗[F] B}
    (h : ∀ i, tensorCoeff e i z = 0) : z = 0 := by
  rw [← sum_tensorCoeff_tmul e z]
  simp [h]

end Coefficients

section Tensor

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  [FiniteDimensional F B]

/-- **O'Meara 52:1 (1), first half**: if $A$ is central and $z \in A \otimes_F B$ commutes with every
$a \otimes 1$, then $z = 1 \otimes b$ for some $b \in B$.  (Expand $z$ in a basis of
$B$; the coefficients commute with all of $A$, hence lie in $F \cdot 1$.) -/
theorem exists_eq_one_tmul_of_commute [Algebra.IsCentral F A] {z : A ⊗[F] B}
    (h : ∀ a : A, (a ⊗ₜ (1 : B) : A ⊗[F] B) * z = z * (a ⊗ₜ (1 : B))) :
    ∃ b : B, z = (1 : A) ⊗ₜ b := by
  let e := Module.finBasis F B
  have hc : ∀ i, ∃ f : F, algebraMap F A f = tensorCoeff e i z := by
    intro i
    have hcen : tensorCoeff e i z ∈ Subalgebra.center F A := by
      rw [Subalgebra.mem_center_iff]
      intro a
      have := congrArg (tensorCoeff e i) (h a)
      rwa [tensorCoeff_tmul_one_mul, tensorCoeff_mul_tmul_one] at this
    have := Algebra.IsCentral.out hcen
    rwa [Algebra.mem_bot] at this
  choose f hf using hc
  refine ⟨∑ i, f i • e i, ?_⟩
  conv_lhs => rw [← sum_tensorCoeff_tmul e z]
  simp_rw [← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [TensorProduct.tmul_sum]

/-- **Key step of O'Meara 52:1 (2)** (the minimal-length argument): if $A$ is central simple and $I$ is a
two-sided ideal of $A \otimes_F B$ containing a nonzero element, then $I$ contains $1 \otimes b$ for some
$b \ne 0$.  Length of $z$ is the number of nonzero coefficients with respect to a fixed basis of $B$. -/
theorem exists_one_tmul_mem_of_ne_zero [IsSimpleRing A] [Algebra.IsCentral F A]
    (I : TwoSidedIdeal (A ⊗[F] B)) {z : A ⊗[F] B} (hz : z ∈ I) (hz0 : z ≠ 0) :
    ∃ b : B, b ≠ 0 ∧ ((1 : A) ⊗ₜ b : A ⊗[F] B) ∈ I := by
  classical
  let e := Module.finBasis F B
  let supp : A ⊗[F] B → Finset (Fin (finrank F B)) :=
    fun z => Finset.univ.filter (fun i => tensorCoeff e i z ≠ 0)
  suffices H : ∀ n, ∀ z ∈ I, z ≠ 0 → (supp z).card = n →
      ∃ b : B, b ≠ 0 ∧ ((1 : A) ⊗ₜ b : A ⊗[F] B) ∈ I from H _ z hz hz0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hz hz0 hn
  obtain ⟨i0, hi0⟩ : ∃ i0, tensorCoeff e i0 z ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (eq_zero_of_tensorCoeff_eq_zero e h)
  -- the ideal of `A` of `i0`-coefficients of elements of `I` supported inside the support of `z`
  let J : TwoSidedIdeal A := TwoSidedIdeal.mk'
    {w | ∃ z' ∈ I, (∀ i, tensorCoeff e i z = 0 → tensorCoeff e i z' = 0) ∧ tensorCoeff e i0 z' = w}
    ⟨0, I.zero_mem, fun _ _ => rfl, by simp⟩
    (fun {_ _} h h' => by
      obtain ⟨z1, h1, s1, rfl⟩ := h
      obtain ⟨z2, h2, s2, rfl⟩ := h'
      exact ⟨z1 + z2, I.add_mem h1 h2, fun i hi => by simp [s1 i hi, s2 i hi], by simp⟩)
    (fun {_} h => by
      obtain ⟨z1, h1, s1, rfl⟩ := h
      exact ⟨-z1, I.neg_mem h1, fun i hi => by simp [s1 i hi], by simp⟩)
    (fun {x _} h => by
      obtain ⟨z1, h1, s1, rfl⟩ := h
      exact ⟨(x ⊗ₜ 1) * z1, I.mul_mem_left _ _ h1,
        fun i hi => by rw [tensorCoeff_tmul_one_mul, s1 i hi, mul_zero],
        tensorCoeff_tmul_one_mul e i0 x z1⟩)
    (fun {_ x} h => by
      obtain ⟨z1, h1, s1, rfl⟩ := h
      exact ⟨z1 * (x ⊗ₜ 1), I.mul_mem_right _ _ h1,
        fun i hi => by rw [tensorCoeff_mul_tmul_one, s1 i hi, zero_mul],
        tensorCoeff_mul_tmul_one e i0 x z1⟩)
  have hJ : (1 : A) ∈ J := by
    refine IsSimpleRing.one_mem_of_ne_zero_mem J hi0 ?_
    rw [TwoSidedIdeal.mem_mk']
    exact ⟨z, hz, fun i hi => hi, rfl⟩
  rw [show J = _ from rfl, TwoSidedIdeal.mem_mk'] at hJ
  obtain ⟨z', hz'I, hsupp, hz'1⟩ := hJ
  have hsub : supp z' ⊆ supp z := by
    intro i hi
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (hsupp i h)
  by_cases hall : ∀ a : A, ((a ⊗ₜ 1 : A ⊗[F] B) * z' - z' * (a ⊗ₜ 1)) = 0
  · -- all coefficients are central
    obtain ⟨b, hb⟩ := exists_eq_one_tmul_of_commute (F := F) (B := B) (z := z')
      (fun a => sub_eq_zero.mp (hall a))
    refine ⟨b, ?_, hb ▸ hz'I⟩
    rintro rfl
    rw [hb] at hz'1
    simp at hz'1
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    set w : A ⊗[F] B := (a ⊗ₜ 1 : A ⊗[F] B) * z' - z' * (a ⊗ₜ 1) with hw
    have hwI : w ∈ I := I.sub_mem (I.mul_mem_left _ _ hz'I) (I.mul_mem_right _ _ hz'I)
    have hcoef : ∀ i, tensorCoeff e i w = a * tensorCoeff e i z' - tensorCoeff e i z' * a := by
      intro i
      rw [hw, map_sub, tensorCoeff_tmul_one_mul, tensorCoeff_mul_tmul_one]
    have hsw : supp w ⊆ (supp z).erase i0 := by
      intro i hi
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase]
      refine ⟨?_, hsub ?_⟩
      · rintro rfl
        apply hi
        rw [hcoef, hz'1]
        simp
      · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        apply hi
        rw [hcoef, h]
        simp
    have hi0mem : i0 ∈ supp z := by simp [supp, hi0]
    have hlt : (supp w).card < n := by
      calc (supp w).card ≤ ((supp z).erase i0).card := Finset.card_le_card hsw
        _ < (supp z).card := Finset.card_erase_lt_of_mem hi0mem
        _ = n := hn
    exact ih _ hlt w hwI ha rfl

/-- **O'Meara 52:1 (1)**: the tensor product of two central algebras over $F$ is central. -/
@[kb "omeara1963" "§52A, 52:1, p. 119 (central part)"]
theorem isCentral_tensorProduct [Algebra.IsCentral F A] [Algebra.IsCentral F B] [Nontrivial A] :
    Algebra.IsCentral F (A ⊗[F] B) where
  out := by
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    obtain ⟨b, rfl⟩ := exists_eq_one_tmul_of_commute (F := F) (B := B) (z := z)
      (fun a => hz _)
    have hb : b ∈ Subalgebra.center F B := by
      rw [Subalgebra.mem_center_iff]
      intro y
      have := hz (1 ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul] at this
      exact Algebra.TensorProduct.includeRight_injective (R := F)
        (FaithfulSMul.algebraMap_injective F A) this
    obtain ⟨g, rfl⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hb)
    refine Algebra.mem_bot.mpr ⟨g, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one (A := A ⊗[F] B), Algebra.algebraMap_eq_smul_one (A := B),
      TensorProduct.tmul_smul]
    rfl

/-- **O'Meara 52:1 (2), in the stronger form it proves**: if $A$ is central simple and $B$ is a
finite-dimensional simple algebra over $F$ (not necessarily central), then $A \otimes_F B$ is simple. -/
@[kb "omeara1963" "§52A, 52:1, p. 119–120 (simple part)"]
theorem isSimpleRing_tensorProduct_of_isCentral [IsSimpleRing A] [Algebra.IsCentral F A]
    [IsSimpleRing B] : IsSimpleRing (A ⊗[F] B) := by
  have : Nontrivial (A ⊗[F] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left F A B
      (FaithfulSMul.algebraMap_injective F B)
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨z, hzI, hz0 : z ≠ 0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨b, hb0, hbI⟩ := exists_one_tmul_mem_of_ne_zero I hzI hz0
  let K : TwoSidedIdeal B := TwoSidedIdeal.mk' {y | ((1 : A) ⊗ₜ y : A ⊗[F] B) ∈ I}
    (by simp)
    (fun {x y} hx hy => by simpa [TensorProduct.tmul_add] using I.add_mem hx hy)
    (fun {x} hx => by simpa [TensorProduct.tmul_neg] using I.neg_mem hx)
    (fun {x y} hy => by
      have := I.mul_mem_left ((1 : A) ⊗ₜ x) _ hy
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this)
    (fun {x y} hx => by
      have := I.mul_mem_right _ ((1 : A) ⊗ₜ y) hx
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this)
  have hK : (1 : B) ∈ K :=
    IsSimpleRing.one_mem_of_ne_zero_mem K hb0 ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr hbI)
  rw [TwoSidedIdeal.mem_mk'] at hK
  exact (TwoSidedIdeal.one_mem_iff I).mp (by simpa [Algebra.TensorProduct.one_def] using hK)

/-- **O'Meara 52:1**: if $A$ and $B$ are central simple algebras over $F$, then so is
$A \otimes_F B$. -/
@[kb "omeara1963" "§52A, 52:1, p. 119"]
theorem isCentralSimple_tensorProduct [Algebra.IsCentral F A] [IsSimpleRing A]
    [Algebra.IsCentral F B] [IsSimpleRing B] :
    Algebra.IsCentral F (A ⊗[F] B) ∧ IsSimpleRing (A ⊗[F] B) :=
  ⟨isCentral_tensorProduct, isSimpleRing_tensorProduct_of_isCentral⟩

end Tensor

section Subalgebras

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- The algebra homomorphism $B \otimes_F C \to A$, $b \otimes c \mapsto bc$, for two subalgebras
$B$, $C$ of $A$ that commute elementwise (O'Meara's $\varphi$ in the proof of 52:2, built from the
universal property of the tensor product, §51B). -/
def subalgebraTensorMap (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c) :
    B ⊗[F] C →ₐ[F] A :=
  Algebra.TensorProduct.lift B.val C.val (fun x y => h x x.2 y y.2)

@[simp]
theorem subalgebraTensorMap_tmul (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    (b : B) (c : C) : subalgebraTensorMap B C h (b ⊗ₜ c) = (b : A) * c := by
  exact Algebra.TensorProduct.lift_tmul B.val C.val _ b c

/-- The image of $b \otimes c \mapsto bc$ is the subalgebra $B \sqcup C$ generated by $B$ and $C$. -/
theorem range_subalgebraTensorMap (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c) :
    (subalgebraTensorMap B C h).range = B ⊔ C := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    change subalgebraTensorMap B C h t ∈ B ⊔ C
    induction t using TensorProduct.inductionOn with
    | tmul b c =>
      rw [subalgebraTensorMap_tmul]
      exact Subalgebra.mul_mem _ ((le_sup_left : B ≤ B ⊔ C) b.2)
        ((le_sup_right : C ≤ B ⊔ C) c.2)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · refine sup_le ?_ ?_
    · intro b hb
      exact ⟨⟨b, hb⟩ ⊗ₜ 1, by simp⟩
    · intro c hc
      exact ⟨1 ⊗ₜ ⟨c, hc⟩, by simp⟩

/-- **O'Meara 52:2, first assertion** (p. 120): the subalgebra generated by two elementwise
commuting subalgebras $B$, $C$ consists of the finite sums of products $bc$ with $b \in B$, $c \in C$
(equivalently, it is the $F$-linear span of these products). -/
@[kb "omeara1963" "§52A, 52:2, p. 120 (first assertion)"]
theorem mem_sup_iff_mem_span_mul (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    (x : A) :
    x ∈ B ⊔ C ↔ x ∈ Submodule.span F {y : A | ∃ b ∈ B, ∃ c ∈ C, y = b * c} := by
  rw [← range_subalgebraTensorMap B C h]
  constructor
  · rintro ⟨t, rfl⟩
    change subalgebraTensorMap B C h t ∈ _
    induction t using TensorProduct.inductionOn with
    | tmul b c =>
      rw [subalgebraTensorMap_tmul]
      exact Submodule.subset_span ⟨b, b.2, c, c.2, rfl⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro hx
    have : Submodule.span F {y : A | ∃ b ∈ B, ∃ c ∈ C, y = b * c} ≤
        Subalgebra.toSubmodule (subalgebraTensorMap B C h).range :=
      Submodule.span_le.mpr (by
        rintro _ ⟨b, hb, c, hc, rfl⟩
        exact ⟨⟨b, hb⟩ ⊗ₜ ⟨c, hc⟩, by simp⟩)
    exact this hx

/-- **O'Meara 52:2, second assertion** (p. 120): if $B$, $C$ are central simple subalgebras of $A$
(containing the identity of $A$, as every `Subalgebra` does) that commute elementwise, then
$b \otimes c \mapsto bc$ is injective on $B \otimes_F C$. -/
theorem subalgebraTensorMap_injective (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    [Algebra.IsCentral F B] [IsSimpleRing B] [IsSimpleRing C] [Algebra.IsCentral F C]
    [FiniteDimensional F C] : Function.Injective (subalgebraTensorMap B C h) := by
  have : IsSimpleRing (B ⊗[F] C) := isSimpleRing_tensorProduct_of_isCentral
  have : Nontrivial A := (Subtype.val_injective (p := (· ∈ B))).nontrivial
  exact RingHom.injective (subalgebraTensorMap B C h).toRingHom

/-- **O'Meara 52:2** (p. 120), isomorphism part: for central simple subalgebras $B$, $C$ of $A$ that
commute elementwise, the subalgebra $B \sqcup C$ they generate is isomorphic to $B \otimes_F C$
(via $b \otimes c \mapsto bc$, see `subalgebraTensorMap`, `range_subalgebraTensorMap`). -/
@[kb "omeara1963" "§52A, 52:2, p. 120"]
theorem tensorProduct_equiv_sup (B C : Subalgebra F A) (h : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    [Algebra.IsCentral F B] [IsSimpleRing B] [IsSimpleRing C] [Algebra.IsCentral F C]
    [FiniteDimensional F C] : Nonempty ((B ⊗[F] C) ≃ₐ[F] ↥(B ⊔ C)) :=
  ⟨(AlgEquiv.ofInjective _ (subalgebraTensorMap_injective B C h)).trans
    (Subalgebra.equivOfEq _ _ (range_subalgebraTensorMap B C h))⟩

end Subalgebras

section Reciprocal

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- **O'Meara 52:10** (p. 128–129), first form: if $A$ is central simple over $F$, then
$A \otimes_F A^*$ (with $A^* = $ `Aᵐᵒᵖ` the reciprocal algebra) is isomorphic to the algebra
$\mathrm{End}_F(A)$ of linear transformations of $A$, via $a \otimes b \mapsto (x \mapsto a x b)$
(`AlgHom.mulLeftRight`). -/
theorem mulLeftRight_bijective [Algebra.IsCentral F A] [IsSimpleRing A] :
    Function.Bijective (AlgHom.mulLeftRight F A) := by
  have : IsSimpleRing (A ⊗[F] Aᵐᵒᵖ) := isSimpleRing_tensorProduct_of_isCentral
  have hinj : Function.Injective (AlgHom.mulLeftRight F A) :=
    RingHom.injective (AlgHom.mulLeftRight F A).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank F (A ⊗[F] Aᵐᵒᵖ) = Module.finrank F (Module.End F A) := by
    rw [Module.finrank_tensorProduct, Module.finrank_linearMap,
      (MulOpposite.opLinearEquiv F (M := A)).finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight F A).toLinearMap) hdim).mp hinj

/-- **O'Meara 52:10** (p. 128–129): for a central simple algebra $A$ over $F$, the algebra
$A \otimes_F A^*$ splits: it is isomorphic to $\mathrm{End}_F(A)$. -/
@[kb "omeara1963" "§52F, 52:10, p. 128 (A ⊗ A* ≅ End_F A)"]
theorem tensorProduct_mulOpposite_equiv_end [Algebra.IsCentral F A] [IsSimpleRing A] :
    Nonempty (A ⊗[F] Aᵐᵒᵖ ≃ₐ[F] Module.End F A) :=
  ⟨AlgEquiv.ofBijective _ mulLeftRight_bijective⟩

/-- **O'Meara 52:10** (p. 128–129), matrix form: for a central simple algebra $A$ over $F$ of
dimension $m$, $A \otimes_F A^* \cong M_m(F)$ (the full matrix algebra, so $A \otimes A^*$ is
split). -/
@[kb "omeara1963" "§52F, 52:10, p. 128 (A ⊗ A* ≅ M_m(F))"]
theorem tensorProduct_mulOpposite_equiv_matrix [Algebra.IsCentral F A] [IsSimpleRing A] :
    Nonempty (A ⊗[F] Aᵐᵒᵖ ≃ₐ[F]
      Matrix (Fin (Module.finrank F A)) (Fin (Module.finrank F A)) F) := by
  obtain ⟨e⟩ := tensorProduct_mulOpposite_equiv_end (F := F) (A := A)
  exact ⟨e.trans (algEquivMatrix (Module.finBasis F A))⟩

end Reciprocal

end QuadFormsKB.OMeara
