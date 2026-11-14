/-
# Shimura 2004, Theorem 14.2 (ii): $G^0(V)/\mathbb R^\times \cong G^1(V)/\{\pm1\} \cong \tau(G^1(V))$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter IV, Theorem 14.2 (ii)
(printed p. 139). Page numbers are printed pages.

**Statement in the book.** For a nondegenerate real quadratic space $(V, \varphi)$, $\tau$ induces isomorphisms
$G^0(V)/\mathbb R^\times \cong G^1(V)/\{\pm1\} \cong SO^\varphi_0(V)$, where $SO^\varphi_0(V)$ is the identity
component of $SO^\varphi(V)$.

**Setting and dictionary.** $V$ is a finite-dimensional real vector space, `Q : QuadraticForm ℝ V` is nondegenerate
(`hQ`). $G^+(V)$ = `Cassels.M0 Q`; $G^0(V)$ = `G0 hQ` (a subgroup of $G^+(V)$); $G^1(V)$ = `spinGroupG1 Q` (a subgroup
of the units of the Clifford algebra); $\tau$ = `tau`; $SO^\varphi(V)$ = `OMeara.orthPlus Q`. Because `tau` is an
anti-homomorphism for composition of maps (`tau_mul`), the group isomorphisms below are stated through the
homomorphism `conjM0` ($a \mapsto (x \mapsto a x a^{-1})$, so $\mathtt{conjM0}(a) = \tau(a^{-1})$); the images
agree with the images of $\tau$ as subsets because the groups are closed under inverses
(`mem_range_G0_iff_tau`, `mem_range_G1_iff_tau`).
* `scalarSubgroupG0 hQ` is $\mathbb R^\times \subset G^0(V)$, the scalars $c \cdot 1$ for $c \in \mathbb R^\times$
  (`scalarM0 c`; each has $\nu(c) = c^2 > 0$), defined as the kernel of `conjM0` on $G^0(V)$ and identified with
  the scalars in `mem_scalarSubgroupG0_iff`;
* `signSubgroupG1 Q` is $\{\pm 1\} \subset G^1(V)$.

**Proves** (unconditional; standard axioms only)
* the algebraic part of Theorem 14.2 (ii): a group isomorphism
  $G^1(V)/\{\pm1\} \cong G^0(V)/\mathbb R^\times$ induced by the inclusion $G^1(V) \subset G^0(V)$
  (`spinQuotientEquiv`; surjective by $G^0(V) = \mathbb R_{>0}\, G^1(V)$, `exists_pos_mul_of_mem_G0`; kernel
  $G^1(V) \cap \mathbb R^\times = \{\pm1\}$, `algebraMap_mem_spinGroupG1_iff`), and its inverse
  (`theorem_14_2_ii_algebraic`);
* $\tau(G^0(V)) = \tau(G^1(V))$ (`tau_image_G0_iff_G1`), kernel of $\tau$ on $G^0(V)$ is $\mathbb R^\times$
  (`tau_eq_one_iff_mem_scalarSubgroupG0`), and the isomorphisms $G^0(V)/\mathbb R^\times \cong \tau(G^0(V))$,
  $G^1(V)/\{\pm1\} \cong \tau(G^1(V))$ (`g0QuotientEquivRange`, `g1QuotientEquivRange`).

**States** (named proposition, not proved) the topological part of (ii): $\tau(G^1(V))$ is the identity component of
$SO^\varphi(V)$ (`Theorem14_2_ii_identityComponent`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.RealClifford
import QuadFormsKB.Literature.Shimura2004.Wave2.Multiplier
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Connected.Basic
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}

local notation "A" => CliffordAlgebra Q

/-! ### The subgroups $\mathbb R^\times \subset G^0(V)$ and $\{\pm1\} \subset G^1(V)$ -/

/-- **$\mathbb R^\times \subset G^0(V)$**: the scalar subgroup of $G^0(V)$, defined as the kernel of the conjugation
homomorphism `conjM0` restricted to $G^0(V)$ (normal automatically). Its elements are exactly the scalars
(`mem_scalarSubgroupG0_iff`). -/
def scalarSubgroupG0 (hQ : (QuadraticMap.associated Q).Nondegenerate) : Subgroup (G0 hQ) :=
  ((conjM0 (Q := Q)).comp (G0 hQ).subtype).ker

instance (hQ : (QuadraticMap.associated Q).Nondegenerate) : (scalarSubgroupG0 hQ).Normal :=
  MonoidHom.normal_ker _

/-- Membership in `scalarSubgroupG0`: the underlying Clifford algebra element is a real scalar. -/
theorem mem_scalarSubgroupG0_iff_range (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : G0 hQ) :
    a ∈ scalarSubgroupG0 hQ ↔
      (((a : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ Set.range (algebraMap ℝ A) := by
  rw [scalarSubgroupG0, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact conjM0_eq_one_iff hQ _

/-- The elements of $\mathbb R^\times \subset G^0(V)$ are exactly the scalars `scalarM0 c`, $c \in \mathbb R^\times$. -/
theorem mem_scalarSubgroupG0_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : G0 hQ) :
    a ∈ scalarSubgroupG0 hQ ↔ ∃ c : ℝˣ, (a : M0 Q) = scalarM0 c := by
  rw [mem_scalarSubgroupG0_iff_range]
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (a : M0 Q).1.ne_zero (by rw [← hc, map_zero])
    exact ⟨Units.mk0 c hc0, Subtype.ext (Units.ext (by simpa [scalarM0] using hc.symm))⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; rfl⟩

/-- Every scalar $c \in \mathbb R^\times$ lies in $G^0(V)$ ($\nu(c) = c^2 > 0$). -/
theorem scalarM0_mem_G0 (hQ : (QuadraticMap.associated Q).Nondegenerate) (c : ℝˣ) : scalarM0 c ∈ G0 hQ := by
  rw [mem_G0_iff, multiplier_scalar]
  have : (c : ℝ) ≠ 0 := c.ne_zero
  push_cast
  positivity

/-- **$\{\pm1\} \subset G^1(V)$**: the elements $\pm 1$ of the spin group. -/
def signSubgroupG1 (Q : QuadraticForm ℝ V) : Subgroup (spinGroupG1 Q) where
  carrier := {b | ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 ∨
    ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    change (((a : (CliffordAlgebra Q)ˣ) * (b : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) = 1 ∨ _
    rw [Units.val_mul]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  inv_mem' := by
    rintro a (ha | ha)
    · left
      have : a = 1 := Subtype.ext (Units.ext ha)
      simp [this]
    · right
      have h1 : ((a⁻¹ : spinGroupG1 Q) : (CliffordAlgebra Q)ˣ) = (a : (CliffordAlgebra Q)ˣ)⁻¹ := rfl
      have h2 : (a : (CliffordAlgebra Q)ˣ) = -1 := by
        apply Units.ext
        simpa using ha
      rw [h1]
      have : ((a : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) = -1 := by
        rw [h2]; simp
      rw [this]; simp

instance : (signSubgroupG1 Q).Normal where
  conj_mem := by
    rintro n (hn | hn) g
    · have : n = 1 := Subtype.ext (Units.ext hn)
      subst this
      simp [signSubgroupG1]
    · right
      change (((g * n * g⁻¹ : spinGroupG1 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = -1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hn]
      simp

/-! ### The isomorphism $G^1(V)/\{\pm1\} \cong G^0(V)/\mathbb R^\times$ -/

/-- Every element of $G^1(V)$ lies in $G^0(V)$ ($\nu = 1 > 0$): the inclusion $G^1(V) \to G^0(V)$. -/
def spinG1ToG0 (hQ : (QuadraticMap.associated Q).Nondegenerate) : spinGroupG1 Q →* G0 hQ where
  toFun b := ⟨⟨b, b.2.1⟩, by
    rw [mem_G0_iff]
    have h := (mem_spinGroupG1_iff_multiplier hQ ⟨b, b.2.1⟩).1 b.2
    rw [h]; simp⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The composite $G^1(V) \to G^0(V) \to G^0(V)/\mathbb R^\times$. -/
def spinToQuotient (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    spinGroupG1 Q →* G0 hQ ⧸ scalarSubgroupG0 hQ :=
  (QuotientGroup.mk' (scalarSubgroupG0 hQ)).comp (spinG1ToG0 hQ)

theorem spinToQuotient_surjective (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    Function.Surjective (spinToQuotient hQ) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨r, hr, b, hb, hab⟩ := exists_pos_mul_of_mem_G0 hQ a.2
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk (spinG1ToG0 hQ ⟨b, hb⟩) : G0 hQ ⧸ scalarSubgroupG0 hQ) = QuotientGroup.mk a
    rw [QuotientGroup.eq, mem_scalarSubgroupG0_iff_range]
    refine ⟨r, ?_⟩
    change algebraMap ℝ A r = (((b : (CliffordAlgebra Q)ˣ)⁻¹ * ((a : M0 Q) : (CliffordAlgebra Q)ˣ) :
      (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    rw [Units.val_mul, hab, ← mul_assoc, ← Algebra.commutes, mul_assoc]
    simp

theorem ker_spinToQuotient (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (spinToQuotient hQ).ker = signSubgroupG1 Q := by
  ext b
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk (spinG1ToG0 hQ b) : G0 hQ ⧸ scalarSubgroupG0 hQ) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_scalarSubgroupG0_iff_range]
  have h1 := tau_eq_one_iff hQ ⟨b, b.2.1⟩
  have h2 := tau_eq_one_iff_of_mem_spinGroupG1 hQ b.2
  exact h1.symm.trans h2

/-- **The isomorphism $G^1(V)/\{\pm1\} \cong G^0(V)/\mathbb R^\times$**, induced by the inclusion
$G^1(V) \subset G^0(V)$. -/
def spinQuotientEquiv (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    spinGroupG1 Q ⧸ signSubgroupG1 Q ≃* G0 hQ ⧸ scalarSubgroupG0 hQ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_spinToQuotient hQ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (spinToQuotient_surjective hQ))

theorem spinQuotientEquiv_mk (hQ : (QuadraticMap.associated Q).Nondegenerate) (b : spinGroupG1 Q) :
    spinQuotientEquiv hQ (QuotientGroup.mk b) = QuotientGroup.mk (spinG1ToG0 hQ b) := rfl

/-! ### The images $\tau(G^0(V)) = \tau(G^1(V))$ -/

/-- The image of $G^0(V)$ under `conjM0` (equal to $\tau(G^0(V))$ as a set, `mem_range_G0_iff_tau`). -/
def rangeG0 (hQ : (QuadraticMap.associated Q).Nondegenerate) : Subgroup (V ≃ₗ[ℝ] V) :=
  ((conjM0 (Q := Q)).comp (G0 hQ).subtype).range

/-- The image of $G^1(V)$ under `conjM0` (equal to $\tau(G^1(V))$ as a set, `mem_range_G1_iff_tau`). -/
def rangeG1 (Q : QuadraticForm ℝ V) : Subgroup (V ≃ₗ[ℝ] V) :=
  ((conjM0 (Q := Q)).comp (Subgroup.inclusion (spinGroupG1_le_M0 (Q := Q)))).range

theorem tau_eq_conjM0_inv (a : M0 Q) : tau (Subgroup.inclusion M0_le a) = conjM0 a⁻¹ := by
  simp [tau, conjM0_apply]

theorem mem_range_G0_iff_tau (hQ : (QuadraticMap.associated Q).Nondegenerate) (α : V ≃ₗ[ℝ] V) :
    α ∈ rangeG0 hQ ↔ ∃ a : M0 Q, a ∈ G0 hQ ∧ tau (Subgroup.inclusion M0_le a) = α := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : M0 Q)⁻¹, (G0 hQ).inv_mem a.2, ?_⟩
    rw [tau_eq_conjM0_inv, inv_inv]; rfl
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a⁻¹, (G0 hQ).inv_mem ha⟩, (tau_eq_conjM0_inv a).symm⟩

theorem mem_range_G1_iff_tau (α : V ≃ₗ[ℝ] V) :
    α ∈ rangeG1 Q ↔ ∃ a : (CliffordAlgebra Q)ˣ, ∃ ha : a ∈ spinGroupG1 Q, tau ⟨a, ha.1.2⟩ = α := by
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨((b⁻¹ : spinGroupG1 Q) : (CliffordAlgebra Q)ˣ), (b⁻¹).2, ?_⟩
    exact (tau_eq_conjM0_inv (Subgroup.inclusion (spinGroupG1_le_M0 (Q := Q)) b⁻¹)).trans (by simp)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩⁻¹, ?_⟩
    have := tau_eq_conjM0_inv (Subgroup.inclusion (spinGroupG1_le_M0 (Q := Q)) ⟨a, ha⟩)
    exact this.symm

/-- **$\tau(G^0(V)) = \tau(G^1(V))$** (Shimura, §14.1 and Theorem 14.2 (ii), p. 139), as sets of linear
automorphisms of $V$. -/
theorem tau_image_G0_iff_G1 (hQ : (QuadraticMap.associated Q).Nondegenerate) (α : V ≃ₗ[ℝ] V) :
    (∃ a : M0 Q, a ∈ G0 hQ ∧ tau (Subgroup.inclusion M0_le a) = α) ↔
      ∃ a : (CliffordAlgebra Q)ˣ, ∃ ha : a ∈ spinGroupG1 Q, tau ⟨a, ha.1.2⟩ = α := by
  rw [← mem_range_G0_iff_tau, ← mem_range_G1_iff_tau]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨r, hr, b, hb, hab⟩ := exists_pos_mul_of_mem_G0 hQ ha
    refine ⟨⟨b, hb⟩, ?_⟩
    -- `a = (scalar r) * b`, and the scalar acts trivially
    have hs : (conjM0 (scalarM0 (Q := Q) (Units.mk0 r hr.ne')) : V ≃ₗ[ℝ] V) = 1 :=
      (conjM0_eq_one_iff hQ _).2 ⟨r, rfl⟩
    have heq : a = scalarM0 (Units.mk0 r hr.ne') * (⟨b, hb.1⟩ : M0 Q) :=
      Subtype.ext (Units.ext (by simpa [scalarM0] using hab))
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    change conjM0 (⟨b, hb.1⟩ : M0 Q) = conjM0 a
    rw [heq, map_mul, hs, one_mul]
  · rintro ⟨b, rfl⟩
    exact ⟨spinG1ToG0 hQ b, rfl⟩

/-- **The kernel of $\tau$ on $G^0(V)$ is $\mathbb R^\times$.** -/
theorem tau_eq_one_iff_mem_scalarSubgroupG0 (hQ : (QuadraticMap.associated Q).Nondegenerate) (a : G0 hQ) :
    tau (Subgroup.inclusion M0_le (a : M0 Q)) = 1 ↔ a ∈ scalarSubgroupG0 hQ :=
  (tau_eq_one_iff hQ (a : M0 Q)).trans (mem_scalarSubgroupG0_iff_range hQ a).symm

/-- **$G^0(V)/\mathbb R^\times \cong \tau(G^0(V))$**, via `conjM0`. -/
def g0QuotientEquivRange (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    G0 hQ ⧸ scalarSubgroupG0 hQ ≃* rangeG0 hQ :=
  QuotientGroup.quotientKerEquivRange ((conjM0 (Q := Q)).comp (G0 hQ).subtype)

/-- The kernel of `conjM0` on $G^1(V)$ is $\{\pm1\}$. -/
theorem ker_conjM0_spinGroupG1 (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ((conjM0 (Q := Q)).comp (Subgroup.inclusion (spinGroupG1_le_M0 (Q := Q)))).ker = signSubgroupG1 Q := by
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, conjM0_eq_one_iff hQ]
  have h1 := tau_eq_one_iff hQ ⟨b, b.2.1⟩
  have h2 := tau_eq_one_iff_of_mem_spinGroupG1 hQ b.2
  exact h1.symm.trans h2

/-- **$G^1(V)/\{\pm1\} \cong \tau(G^1(V))$**, via `conjM0`. -/
def g1QuotientEquivRange (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    spinGroupG1 Q ⧸ signSubgroupG1 Q ≃* rangeG1 Q :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conjM0_spinGroupG1 hQ).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

theorem rangeG0_eq_rangeG1 (hQ : (QuadraticMap.associated Q).Nondegenerate) : rangeG0 hQ = rangeG1 Q := by
  ext α
  rw [mem_range_G0_iff_tau, mem_range_G1_iff_tau]
  exact tau_image_G0_iff_G1 hQ α

/-- **Theorem 14.2 (ii), algebraic part** (Shimura 2004, p. 139): for a nondegenerate real quadratic space,
with $\mathbb R^\times \subset G^0(V)$ the scalars (`scalarSubgroupG0`) and $\{\pm1\} \subset G^1(V)$
(`signSubgroupG1`):
1. the inclusion $G^1(V) \subset G^0(V)$ induces an isomorphism $G^1(V)/\{\pm1\} \cong G^0(V)/\mathbb R^\times$
   (hence also $G^0(V)/\mathbb R^\times \cong G^1(V)/\{\pm1\}$, by `symm`), explicitly
   $b\{\pm1\} \mapsto b\,\mathbb R^\times$;
2. $\tau(G^0(V)) = \tau(G^1(V))$ as sets of linear automorphisms of $V$;
3. the kernel of $\tau$ on $G^0(V)$ is $\mathbb R^\times$;
4. $G^0(V)/\mathbb R^\times \cong \tau(G^0(V))$ and $G^1(V)/\{\pm1\} \cong \tau(G^1(V))$ (images of `conjM0`,
   which agree with the images of $\tau$ by `mem_range_G0_iff_tau`, `mem_range_G1_iff_tau`).

The identification of $\tau(G^1(V))$ with the identity component $SO^\varphi_0(V)$ is the topological part,
stated as `Theorem14_2_ii_identityComponent`. -/
@[kb "shimura2004" "Thm. 14.2 (ii), p. 139 (G⁰(V)/ℝ^× ≅ G¹(V)/{±1} ≅ τ(G¹(V)))"]
theorem theorem_14_2_ii_algebraic (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (∃ e : spinGroupG1 Q ⧸ signSubgroupG1 Q ≃* G0 hQ ⧸ scalarSubgroupG0 hQ,
      ∀ b : spinGroupG1 Q, e (QuotientGroup.mk b) = QuotientGroup.mk (spinG1ToG0 hQ b)) ∧
    Nonempty (G0 hQ ⧸ scalarSubgroupG0 hQ ≃* spinGroupG1 Q ⧸ signSubgroupG1 Q) ∧
    (∀ α : V ≃ₗ[ℝ] V,
      (∃ a : M0 Q, a ∈ G0 hQ ∧ tau (Subgroup.inclusion M0_le a) = α) ↔
        ∃ a : (CliffordAlgebra Q)ˣ, ∃ ha : a ∈ spinGroupG1 Q, tau ⟨a, ha.1.2⟩ = α) ∧
    (∀ a : G0 hQ, tau (Subgroup.inclusion M0_le (a : M0 Q)) = 1 ↔ a ∈ scalarSubgroupG0 hQ) ∧
    Nonempty (G0 hQ ⧸ scalarSubgroupG0 hQ ≃* rangeG0 hQ) ∧
    Nonempty (spinGroupG1 Q ⧸ signSubgroupG1 Q ≃* rangeG1 Q) ∧ rangeG0 hQ = rangeG1 Q :=
  ⟨⟨spinQuotientEquiv hQ, spinQuotientEquiv_mk hQ⟩, ⟨(spinQuotientEquiv hQ).symm⟩,
    tau_image_G0_iff_G1 hQ, tau_eq_one_iff_mem_scalarSubgroupG0 hQ, ⟨g0QuotientEquivRange hQ⟩,
    ⟨g1QuotientEquivRange hQ⟩, rangeG0_eq_rangeG1 hQ⟩

/-- **Theorem 14.2 (ii), identity component** (Shimura 2004, p. 139), *stated, not proved*: for a nondegenerate real
quadratic space $V$, $\tau(G^1(V))$ is the identity component $SO^\varphi_0(V)$ of $SO^\varphi(V)$. The topology is
the natural one: $\operatorname{End}_{\mathbb R}(V)$ is a finite-dimensional real vector space
(`moduleTopology ℝ`) and $SO^\varphi(V)$ is viewed as the subset of those endomorphisms that are the underlying
linear map of an element of `OMeara.orthPlus Q`. For $\alpha \in SO^\varphi(V)$: $\alpha \in \tau(G^1(V))$ if and
only if the linear map of $\alpha$ lies in the connected component of the identity map in that subset
(`connectedComponentIn`). This is the topological part of (ii), whose algebraic part is
`theorem_14_2_ii_algebraic`. -/
@[kb "shimura2004" "Thm. 14.2 (ii), p. 139 (τ(G¹(V)) = SO^φ_0(V), the identity component of SO^φ(V))"]
def Theorem14_2_ii_identityComponent : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (_hQ : (QuadraticMap.associated Q).Nondegenerate),
    letI : TopologicalSpace (Module.End ℝ V) := moduleTopology ℝ (Module.End ℝ V)
    ∀ α : V ≃ₗ[ℝ] V, α ∈ orthPlus Q →
      ((∃ a : (CliffordAlgebra Q)ˣ, ∃ ha : a ∈ spinGroupG1 Q, tau ⟨a, ha.1.2⟩ = α) ↔
        (α : Module.End ℝ V) ∈
          connectedComponentIn {β : Module.End ℝ V | ∃ γ ∈ orthPlus Q, (γ : Module.End ℝ V) = β}
            (1 : Module.End ℝ V))

end QuadFormsKB.Shimura2004
