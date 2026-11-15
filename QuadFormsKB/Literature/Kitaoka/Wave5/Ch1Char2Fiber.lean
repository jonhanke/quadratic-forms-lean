/-
# Kitaoka 1993, Theorem 1.3.2: the fibration $r(A \perp B, W) = \sum_\tau r(B, \tau(A)^\perp)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, proof of Theorem 1.3.2, p. 16 (printed page):
$r(U \perp U_1, W) = \sum_{\sigma : U \to W} r(U_1, \sigma(U)^\perp)$.

**Proves** (any field; used for characteristic $2$, where $U$ is a regular plane):
* `prodFiberEquiv`: for a regular space $(A, Q_A)$, the isometries $A \perp B \to W$ are the pairs of an isometry
  $\tau : A \to W$ and an isometry $B \to \tau(A)^\perp$;
* `isomCount_prod_eq`: hence $r(A \perp B, W) = r(A, W)\,R$ when every $r(B, \tau(A)^\perp)$ equals $R$;
* `perpRange_split`: for an isometry $\tau : A \to W$ of regular spaces, $\tau(A)^\perp$ is regular and
  $A \perp \tau(A)^\perp \cong W$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1IsometryCountProof

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F]

section Fiber

variable {A B W : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup W] [Module F W]

/-- $\tau(A)^\perp = \{y \in W : b(\tau a, y) = 0 \text{ for all } a\}$ for a linear map $\tau : A \to W$. -/
def perpRange (QW : QuadraticForm F W) (τ : A →ₗ[F] W) : Submodule F W where
  carrier := {y | ∀ a, polar QW (τ a) y = 0}
  add_mem' := by
    intro x y hx hy a
    rw [polar_add_right, hx a, hy a, add_zero]
  zero_mem' := by intro a; simp
  smul_mem' := by
    intro c x hx a
    rw [polar_smul_right, hx a, smul_zero]

theorem mem_perpRange (QW : QuadraticForm F W) (τ : A →ₗ[F] W) (y : W) :
    y ∈ perpRange QW τ ↔ ∀ a, polar QW (τ a) y = 0 := Iff.rfl

/-- The isometries $A \to W$ (injective linear maps preserving the forms). -/
abbrev IsoT (QA : QuadraticForm F A) (QW : QuadraticForm F W) : Type :=
  {τ : A →ₗ[F] W // Function.Injective τ ∧ ∀ x, QW (τ x) = QA x}

/-- The restriction of an isometry $A \perp B \to W$ to $A$. -/
def restrA (QA : QuadraticForm F A) (QB : QuadraticForm F B) (QW : QuadraticForm F W)
    (σ : IsoT (QA.prod QB) QW) : IsoT QA QW :=
  ⟨σ.1.comp (LinearMap.inl F A B), σ.2.1.comp (fun a b h => by simpa using h), fun x => by
    simp [σ.2.2, QuadraticMap.prod_apply]⟩

/-- **The fibre.** For a regular $(A, Q_A)$ and an isometry $\tau : A \to W$, the isometries
$A \perp B \to W$ restricting to $\tau$ on $A$ correspond to the isometries $B \to \tau(A)^\perp$. -/
def prodFiberEquiv {QA : QuadraticForm F A} (hA : (polarBilin QA).Nondegenerate) (QB : QuadraticForm F B)
    (QW : QuadraticForm F W) (τ : IsoT QA QW) :
    {σ : IsoT (QA.prod QB) QW // σ.1.comp (LinearMap.inl F A B) = τ.1} ≃
      IsoT QB (QW.comp (perpRange QW τ.1).subtype) where
  toFun σ :=
    ⟨LinearMap.codRestrict (perpRange QW τ.1) (σ.1.1.comp (LinearMap.inr F A B))
        (fun b a => by
          have h := polar_of_iso σ.1.1 σ.1.2.2 (a, 0) (0, b)
          have ha : τ.1 a = σ.1.1 (a, 0) := by
            exact (LinearMap.congr_fun σ.2 a).symm
          simp only [LinearMap.comp_apply, LinearMap.inr_apply]
          rw [ha, h]
          simp [polar, QuadraticMap.prod_apply]),
      fun a b h => by
        have h' := congrArg Subtype.val h
        exact (Prod.mk.inj (σ.1.2.1 (show σ.1.1 (0, a) = σ.1.1 (0, b) from h'))).2,
      fun b => by
        show QW (σ.1.1 (0, b)) = QB b
        rw [σ.1.2.2]
        simp [QuadraticMap.prod_apply]⟩
  invFun ρ :=
    ⟨⟨τ.1.coprod ((perpRange QW τ.1).subtype.comp ρ.1),
      by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        rintro ⟨a, b⟩ h
        simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
        have ha : a = 0 := by
          apply (QuadraticForm.nondegenerate_polarBilin_iff QA).mp hA a
          intro a'
          have h1 := congrArg (polar QW (τ.1 a')) h
          rw [polar_add_right, (ρ.1 b).2 a', add_zero, QuadraticMap.polar_zero_right,
            polar_of_iso τ.1 τ.2.2] at h1
          rw [polar_comm]; exact h1
        subst ha
        simp only [map_zero, zero_add] at h
        have hb : ρ.1 b = 0 := Subtype.ext h
        have := ρ.2.1 (hb.trans (map_zero ρ.1).symm)
        simp [this],
      by
        rintro ⟨a, b⟩
        simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        rw [QuadraticMap.map_add QW, (ρ.1 b).2 a, add_zero, τ.2.2]
        have := ρ.2.2 b
        simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
        rw [this]
        simp [QuadraticMap.prod_apply]⟩,
     by ext a; simp⟩
  left_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have ha : τ.1 a = σ.1.1 (a, 0) := by
      exact (LinearMap.congr_fun σ.2 a).symm
    show τ.1 a + σ.1.1 (0, b) = σ.1.1 (a, b)
    rw [ha, ← map_add]
    simp
  right_inv ρ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp

/-- $r(A \perp B, W) = r(A, W)\,R$ when every $r(B, \tau(A)^\perp)$ equals $R$ ($A$ regular). -/
theorem isomCount_prod_eq [Finite F] [FiniteDimensional F A] [FiniteDimensional F B] [FiniteDimensional F W]
    {QA : QuadraticForm F A} (hA : (polarBilin QA).Nondegenerate) (QB : QuadraticForm F B)
    (QW : QuadraticForm F W) (R : ℝ)
    (hR : ∀ τ : IsoT QA QW, (isomCount QB (QW.comp (perpRange QW τ.1).subtype) : ℝ) = R) :
    (isomCount (QA.prod QB) QW : ℝ) = isomCount QA QW * R := by
  classical
  have : Finite W := Module.finite_of_finite F
  have : Finite (A →ₗ[F] W) := Module.finite_of_finite F
  have : Finite ((A × B) →ₗ[F] W) := Module.finite_of_finite F
  have : Fintype (IsoT QA QW) := Fintype.ofFinite _
  let f := restrA QA QB QW
  have hcard : isomCount (QA.prod QB) QW = Nat.card (Σ b, {a // f a = b}) :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
  have hfib : ∀ b : IsoT QA QW, Nat.card {a // f a = b} =
      isomCount QB (QW.comp (perpRange QW b.1).subtype) := by
    intro b
    rw [isomCount, ← Nat.card_congr (prodFiberEquiv hA QB QW b)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [f, restrA, Subtype.ext_iff])
  rw [hcard, Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl fun b _ => by rw [hfib b, hR b], Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, isomCount, Nat.card_eq_fintype_card]

/-- The map $A \times \tau(A)^\perp \to W$, $(a, y) \mapsto \tau a + y$. -/
def splitMap (QW : QuadraticForm F W) (τ : A →ₗ[F] W) : (A × perpRange QW τ) →ₗ[F] W :=
  τ.coprod (perpRange QW τ).subtype

theorem splitMap_apply (QW : QuadraticForm F W) (τ : A →ₗ[F] W) (a : A) (y : perpRange QW τ) :
    splitMap QW τ (a, y) = τ a + y := by simp [splitMap]

/-- $\tau(A)^\perp$ is the kernel of $y \mapsto (a \mapsto b(\tau a, y))$. -/
theorem perpRange_eq_ker (QW : QuadraticForm F W) (τ : A →ₗ[F] W) :
    perpRange QW τ = LinearMap.ker (((polarBilin QW).comp τ).flip) := by
  ext y
  simp [mem_perpRange, LinearMap.ext_iff]

/-- **Splitting off the image of a regular space.** For an isometry $\tau : A \to W$ from a regular space,
$A \perp \tau(A)^\perp \cong W$, and $\tau(A)^\perp$ is regular when $W$ is. -/
theorem perpRange_split [FiniteDimensional F A] [FiniteDimensional F W] {QA : QuadraticForm F A}
    {QW : QuadraticForm F W} (hA : (polarBilin QA).Nondegenerate) (τ : IsoT QA QW) :
    (QA.prod (QW.comp (perpRange QW τ.1).subtype)).Equivalent QW ∧
      finrank F A + finrank F (perpRange QW τ.1) = finrank F W ∧
      ((polarBilin QW).Nondegenerate → (polarBilin (QW.comp (perpRange QW τ.1).subtype)).Nondegenerate) := by
  classical
  have hinj : Function.Injective (splitMap QW τ.1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    rw [splitMap_apply] at h
    have ha : a = 0 := by
      apply (QuadraticForm.nondegenerate_polarBilin_iff QA).mp hA a
      intro a'
      have h1 := congrArg (polar QW (τ.1 a')) h
      rw [polar_add_right, b.2 a', add_zero, QuadraticMap.polar_zero_right, polar_of_iso τ.1 τ.2.2] at h1
      rw [polar_comm]; exact h1
    subst ha
    simp only [map_zero, zero_add] at h
    have hb : b = 0 := Subtype.ext h
    simp [hb]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hge : finrank F W ≤ finrank F A + finrank F (perpRange QW τ.1) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (((polarBilin QW).comp τ.1).flip)
    have h2 : finrank F (LinearMap.range (((polarBilin QW).comp τ.1).flip)) ≤ finrank F A := by
      calc _ ≤ finrank F (Module.Dual F A) := Submodule.finrank_le _
        _ = finrank F A := Subspace.dual_finrank_eq
    rw [← perpRange_eq_ker] at h1
    omega
  rw [Module.finrank_prod] at hle
  have heq : finrank F (A × perpRange QW τ.1) = finrank F W := by rw [Module.finrank_prod]; omega
  have hbij : Function.Bijective (splitMap QW τ.1) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj⟩
  let e : (A × perpRange QW τ.1) ≃ₗ[F] W := LinearEquiv.ofBijective _ hbij
  have hQ : ∀ p : A × perpRange QW τ.1, QW (e p) = (QA.prod (QW.comp (perpRange QW τ.1).subtype)) p := by
    rintro ⟨a, b⟩
    show QW (splitMap QW τ.1 (a, b)) = _
    rw [splitMap_apply, QuadraticMap.map_add QW, b.2 a, add_zero, τ.2.2]
    simp [QuadraticMap.prod_apply]
  refine ⟨⟨{ toLinearEquiv := e, map_app' := hQ }⟩, by omega, fun hW => ?_⟩
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro y hy
  apply Subtype.ext
  apply (QuadraticForm.nondegenerate_polarBilin_iff QW).mp hW y
  intro w
  obtain ⟨⟨a, b⟩, rfl⟩ := hbij.2 w
  show polar QW y (splitMap QW τ.1 (a, b)) = 0
  rw [splitMap_apply, polar_add_right, polar_comm, y.2 a, zero_add]
  have := hy b
  simpa [polar] using this

/-- The map $(a, y) \mapsto \tau a + y$ is a bijection $A \times \tau(A)^\perp \to W$ ($A$ regular). -/
theorem splitMap_bijective [FiniteDimensional F A] [FiniteDimensional F W] {QA : QuadraticForm F A}
    {QW : QuadraticForm F W} (hA : (polarBilin QA).Nondegenerate) (τ : IsoT QA QW) :
    Function.Bijective (splitMap QW τ.1) := by
  have hinj : Function.Injective (splitMap QW τ.1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    rw [splitMap_apply] at h
    have ha : a = 0 := by
      apply (QuadraticForm.nondegenerate_polarBilin_iff QA).mp hA a
      intro a'
      have h1 := congrArg (polar QW (τ.1 a')) h
      rw [polar_add_right, b.2 a', add_zero, QuadraticMap.polar_zero_right, polar_of_iso τ.1 τ.2.2] at h1
      rw [polar_comm]; exact h1
    subst ha
    simp only [map_zero, zero_add] at h
    have hb : b = 0 := Subtype.ext h
    simp [hb]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hge : finrank F W ≤ finrank F A + finrank F (perpRange QW τ.1) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (((polarBilin QW).comp τ.1).flip)
    have h2 : finrank F (LinearMap.range (((polarBilin QW).comp τ.1).flip)) ≤ finrank F A := by
      calc _ ≤ finrank F (Module.Dual F A) := Submodule.finrank_le _
        _ = finrank F A := Subspace.dual_finrank_eq
    rw [← perpRange_eq_ker] at h1
    omega
  rw [Module.finrank_prod] at hle
  have heq : finrank F (A × perpRange QW τ.1) = finrank F W := by rw [Module.finrank_prod]; omega
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj⟩

end Fiber

end QuadFormsKB.Kitaoka.FqCount
