/-
# Shimura 2004, Lemma 3.8 (ii): transport of the Clifford group along an isometry

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, Lemma 3.8 (ii),
printed p. 24. Page numbers are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/CliffordGroups.lean`. Shimura's data
$(\gamma, \psi)$, an $F$-linear bijection $\gamma : V \to W$ together with the quadratic form $\psi$ on $W$ defined by
$\psi[x\gamma] = \varphi[x]$, is the same as an isometry equivalence `e : Q.IsometryEquiv R` with `Q : QuadraticForm F V`
and `R : QuadraticForm F W` ($R = \psi$, $e = \gamma$). The ring isomorphism $a \mapsto a^\gamma$ of $A(V,\varphi)$ onto
$A(W,\psi)$ is Mathlib's `CliffordAlgebra.equivOfIsometry e`; on units it is `cliffordUnitMap e`, and on $G(V)$ it is
`cliffordGroupMap e`.

*Right actions.* Shimura lets $\gamma$ act on the right, so his $\gamma^{-1}\tau(a)\gamma$ ("first $\gamma^{-1}$, then
$\tau(a)$, then $\gamma$") is, for Lean's left actions, the composite $e \circ \tau(a) \circ e^{-1}$ of linear maps of
$W$ (`tau_cliffordGroupMap`). Likewise $\gamma^{-1}\xi\gamma$ for $\xi \in SO^\varphi(V)$ is `e * ξ * e⁻¹`
(`conjIsometry`).

**Proves** (all unconditional; standard axioms only)
* $\iota(x)^\gamma = \iota(x\gamma)$ (`equivOfIsometry_ι`, `equivOfIsometry_algebraMap`).
* $a \in G(V) \iff a^\gamma \in G(W)$, and the same for $G^+$ and $G^-$ (`cliffordUnitMap_mem_cliffordGroup_iff`,
  `cliffordUnitMap_mem_M0_iff`, `cliffordUnitMap_mem_cliffordGroupOdd_iff`), so $G^\pm(V)$ is mapped onto $G^\pm(W)$,
  and $G'(V)$ onto $G'(W)$ (`cliffordUnitMap_mem_homogeneous_iff`).
* $\tau(a^\gamma) = \gamma^{-1}\tau(a)\gamma$ (`tau_cliffordGroupMap`).
* $\nu(a^\gamma) = \nu(a)$ for $a \in G'(V)$ (`multiplier_cliffordUnitMap`), with $\varphi$ nondegenerate (so $\psi$
  is, `nondegenerate_of_isometryEquiv`).
* $\sigma(\gamma^{-1}\xi\gamma) = \sigma(\xi)$ for $\xi \in SO^\varphi(V)$ (`spinorNormHom_conjIsometry`).
* The special case $(V,\varphi) = (W,\psi)$: `cliffordUnitMap e` is an automorphism of $A(V)$ for $e \in O^\varphi(V)$
  (this is `equivOfIsometry e` with `W = V`, `R = Q`).
-/
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V W : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {R : QuadraticForm F W}

/-! ### The ring isomorphism $a \mapsto a^\gamma$ -/

/-- $\iota(x)^\gamma = \iota(x\gamma)$: the isomorphism $a \mapsto a^\gamma$ extends $x \mapsto x\gamma$
(Shimura, Lemma 3.8 (ii), p. 24). -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (a ↦ a^γ extends x ↦ xγ)"]
theorem equivOfIsometry_ι (e : Q.IsometryEquiv R) (x : V) :
    CliffordAlgebra.equivOfIsometry e (ι Q x) = ι R (e x) := by
  rw [CliffordAlgebra.equivOfIsometry_apply]
  exact CliffordAlgebra.map_apply_ι _ _

theorem equivOfIsometry_algebraMap (e : Q.IsometryEquiv R) (c : F) :
    CliffordAlgebra.equivOfIsometry e (algebraMap F _ c) = algebraMap F _ c :=
  AlgEquiv.commutes _ c

/-- The isomorphism $a \mapsto a^\gamma$ on the unit groups, $A(V)^\times \cong A(W)^\times$. -/
def cliffordUnitMap (e : Q.IsometryEquiv R) : (CliffordAlgebra Q)ˣ ≃* (CliffordAlgebra R)ˣ :=
  Units.mapEquiv (CliffordAlgebra.equivOfIsometry e).toRingEquiv.toMulEquiv

@[simp] theorem coe_cliffordUnitMap (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    ((cliffordUnitMap e a : (CliffordAlgebra R)ˣ) : CliffordAlgebra R) =
      CliffordAlgebra.equivOfIsometry e (a : CliffordAlgebra Q) := rfl

theorem cliffordUnitMap_symm_apply (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    cliffordUnitMap e.symm (cliffordUnitMap e a) = a := by
  apply Units.ext
  simp only [coe_cliffordUnitMap, ← CliffordAlgebra.equivOfIsometry_symm]
  exact (CliffordAlgebra.equivOfIsometry e).symm_apply_apply _

/-! ### Membership in $G(V)$, $G^+(V)$, $G^-(V)$, $G'(V)$ -/

theorem map_evenOdd_le (e : Q.IsometryEquiv R) (i : ZMod 2) {a : CliffordAlgebra Q}
    (ha : a ∈ evenOdd Q i) : CliffordAlgebra.equivOfIsometry e a ∈ evenOdd R i := by
  have h : Submodule.map (CliffordAlgebra.map e.toIsometry).toLinearMap (evenOdd Q i) ≤ evenOdd R i := by
    rw [evenOdd, Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rw [Submodule.map_pow]
    refine le_trans ?_ (le_iSup (fun j : { n : ℕ // (n : ZMod 2) = i } => LinearMap.range (ι R) ^ (j : ℕ)) j)
    refine pow_le_pow_left' ?_ _
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, by simp [CliffordAlgebra.map_apply_ι]⟩
  exact h ⟨a, ha, rfl⟩

theorem cliffordUnitMap_mem_evenOdd_iff (e : Q.IsometryEquiv R) (i : ZMod 2) (a : CliffordAlgebra Q) :
    CliffordAlgebra.equivOfIsometry e a ∈ evenOdd R i ↔ a ∈ evenOdd Q i := by
  refine ⟨fun h => ?_, map_evenOdd_le e i⟩
  have := map_evenOdd_le e.symm i h
  rwa [← CliffordAlgebra.equivOfIsometry_symm, AlgEquiv.symm_apply_apply] at this

theorem cliffordUnitMap_mem_cliffordGroup (e : Q.IsometryEquiv R) {a : (CliffordAlgebra Q)ˣ}
    (ha : a ∈ cliffordGroup Q) : cliffordUnitMap e a ∈ cliffordGroup R := by
  intro x'
  obtain ⟨y, hy⟩ := ha (e.symm x')
  refine ⟨e y, ?_⟩
  have := congrArg (CliffordAlgebra.equivOfIsometry e) hy
  rw [equivOfIsometry_ι, map_mul, map_mul, equivOfIsometry_ι, QuadraticMap.IsometryEquiv.apply_symm_apply] at this
  rw [this]
  rfl

/-- **$a \in G(V) \iff a^\gamma \in G(W)$** (Shimura, Lemma 3.8 (ii), p. 24). -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (a ∈ G(V) iff a^γ ∈ G(W))"]
theorem cliffordUnitMap_mem_cliffordGroup_iff (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    cliffordUnitMap e a ∈ cliffordGroup R ↔ a ∈ cliffordGroup Q := by
  refine ⟨fun h => ?_, cliffordUnitMap_mem_cliffordGroup e⟩
  simpa [cliffordUnitMap_symm_apply] using cliffordUnitMap_mem_cliffordGroup e.symm h

/-- **$G^+(V)$ is mapped onto $G^+(W)$** (Shimura, Lemma 3.8 (ii), p. 24): $a \in G^+(V) \iff a^\gamma \in G^+(W)$. -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (G⁺(V) is mapped onto G⁺(W))"]
theorem cliffordUnitMap_mem_M0_iff (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    cliffordUnitMap e a ∈ M0 R ↔ a ∈ M0 Q := by
  rw [mem_M0_iff, mem_M0_iff, cliffordUnitMap_mem_cliffordGroup_iff, coe_cliffordUnitMap,
    cliffordUnitMap_mem_evenOdd_iff]

/-- **$G^-(V)$ is mapped onto $G^-(W)$** (Shimura, Lemma 3.8 (ii), p. 24): $a \in G^-(V) \iff a^\gamma \in G^-(W)$. -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (G⁻(V) is mapped onto G⁻(W))"]
theorem cliffordUnitMap_mem_cliffordGroupOdd_iff (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    cliffordUnitMap e a ∈ cliffordGroupOdd R ↔ a ∈ cliffordGroupOdd Q := by
  change cliffordUnitMap e a ∈ cliffordGroup R ∧ _ ↔ a ∈ cliffordGroup Q ∧ _
  rw [cliffordUnitMap_mem_cliffordGroup_iff, coe_cliffordUnitMap, cliffordUnitMap_mem_evenOdd_iff]

/-- $G'(V)$ is mapped onto $G'(W)$ (consequence of the two previous statements). -/
theorem cliffordUnitMap_mem_homogeneous_iff (e : Q.IsometryEquiv R) (a : (CliffordAlgebra Q)ˣ) :
    cliffordUnitMap e a ∈ homogeneousCliffordGroup R ↔ a ∈ homogeneousCliffordGroup Q := by
  rw [mem_homogeneous_iff, mem_homogeneous_iff, cliffordUnitMap_mem_M0_iff,
    cliffordUnitMap_mem_cliffordGroupOdd_iff]

/-- The isomorphism $a \mapsto a^\gamma$ restricted to $G(V) \to G(W)$. -/
def cliffordGroupMap (e : Q.IsometryEquiv R) (a : cliffordGroup Q) : cliffordGroup R :=
  ⟨cliffordUnitMap e a, cliffordUnitMap_mem_cliffordGroup e a.2⟩

/-- The isomorphism $a \mapsto a^\gamma$ restricted to $G'(V) \to G'(W)$. -/
def homogeneousMap (e : Q.IsometryEquiv R) (a : homogeneousCliffordGroup Q) : homogeneousCliffordGroup R :=
  ⟨cliffordUnitMap e a, (cliffordUnitMap_mem_homogeneous_iff e a).2 a.2⟩

/-! ### $\tau(a^\gamma) = \gamma^{-1}\tau(a)\gamma$ -/

/-- **$\tau(a^\gamma) = \gamma^{-1}\tau(a)\gamma$** (Shimura, Lemma 3.8 (ii), p. 24). Shimura's maps act on the right,
so "$\gamma^{-1}\tau(a)\gamma$" means: first $\gamma^{-1}$, then $\tau(a)$, then $\gamma$. For Lean's left actions this
is the composite $e \circ \tau(a) \circ e^{-1}$, which is what is stated (`e.symm ≪ tau a ≪ e` as a linear
equivalence of $W$). -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (τ(a^γ) = γ⁻¹τ(a)γ)"]
theorem tau_cliffordGroupMap (e : Q.IsometryEquiv R) (a : cliffordGroup Q) :
    tau (cliffordGroupMap e a) = (e.toLinearEquiv.symm.trans (tau a)).trans e.toLinearEquiv := by
  ext y
  apply cliffordι_injective R
  rw [tau_spec]
  change _ = ι R (e (tau a (e.symm y)))
  rw [← equivOfIsometry_ι, tau_spec]
  simp only [map_mul, equivOfIsometry_ι, QuadraticMap.IsometryEquiv.apply_symm_apply]
  rfl

/-! ### $\nu(a^\gamma) = \nu(a)$ -/

theorem nondegenerate_of_isometryEquiv (e : Q.IsometryEquiv R)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) : (QuadraticMap.associated R).Nondegenerate := by
  have h := LinearMap.BilinForm.Nondegenerate.congr (B := QuadraticMap.associated Q) e.toLinearEquiv hQ
  convert h using 1
  ext x y
  simp only [LinearMap.BilinForm.congr_apply, QuadraticMap.associated_apply]
  have key : ∀ z, R z = Q (e.symm z) := fun z => by
    conv_lhs => rw [← e.apply_symm_apply z]
    exact e.map_app _
  rw [key (x + y), key x, key y, map_add]
  congr!

theorem reverse_equivOfIsometry (e : Q.IsometryEquiv R) (a : CliffordAlgebra Q) :
    reverse (CliffordAlgebra.equivOfIsometry e a) = CliffordAlgebra.equivOfIsometry e (reverse a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [equivOfIsometry_algebraMap, reverse.commutes, reverse.commutes,
      equivOfIsometry_algebraMap]
  | ι x => rw [equivOfIsometry_ι, reverse_ι, reverse_ι, equivOfIsometry_ι]
  | mul a b ha hb => rw [map_mul, reverse.map_mul, ha, hb, reverse.map_mul, map_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **$\nu(a^\gamma) = \nu(a)$ for $a \in G'(V)$** (Shimura, Lemma 3.8 (ii), p. 24); $\varphi$ nondegenerate (hence
$\psi$ too, `nondegenerate_of_isometryEquiv`). -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (ν(a^γ) = ν(a) for a ∈ G'(V))"]
theorem multiplier_cliffordUnitMap (e : Q.IsometryEquiv R) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hR : (QuadraticMap.associated R).Nondegenerate) (a : homogeneousCliffordGroup Q) :
    multiplier hR (homogeneousMap e a) = multiplier hQ a := by
  apply Units.ext
  apply (algebraMap F (CliffordAlgebra R)).injective
  rw [algebraMap_multiplier hR]
  change CliffordAlgebra.equivOfIsometry e _ * reverse (CliffordAlgebra.equivOfIsometry e _) = _
  rw [reverse_equivOfIsometry, ← map_mul, ← algebraMap_multiplier hQ a, equivOfIsometry_algebraMap]

/-! ### $\sigma(\gamma^{-1}\xi\gamma) = \sigma(\xi)$ -/

/-- $\gamma^{-1}\xi\gamma$ (right actions), i.e. $e \circ \xi \circ e^{-1}$ in Lean's left actions, as an element of
$SO^\varphi(W)$ for $\xi \in SO^\varphi(V)$. -/
def conjIsometry (e : Q.IsometryEquiv R) (ξ : orthPlus Q) : orthPlus R :=
  ⟨(e.toLinearEquiv.symm.trans ξ.1).trans e.toLinearEquiv, by
    refine ⟨fun y => ?_, ?_⟩
    · have h := ξ.2.1 (e.symm y)
      change R (e (ξ.1 (e.symm y))) = R y
      rw [e.map_app, h, ← e.map_app, e.apply_symm_apply]
    · have h : LinearEquiv.det ξ.1 = 1 := ξ.2.2
      change LinearEquiv.det ((e.toLinearEquiv.symm.trans ξ.1).trans e.toLinearEquiv) = 1
      rw [LinearEquiv.det_conj, h]⟩

/-- **$\sigma(\gamma^{-1}\xi\gamma) = \sigma(\xi)$ for $\xi \in SO^\varphi(V)$** (Shimura, Lemma 3.8 (ii), p. 24); the
left side is the spinor norm on $W$ of $e \circ \xi \circ e^{-1}$ (see the module docstring on right actions).
Nondegenerate $\varphi$. -/
@[kb "shimura2004" "Lemma 3.8 (ii), p. 24 (σ(γ⁻¹ξγ) = σ(ξ) for ξ ∈ SO^φ(V))"]
theorem spinorNormHom_conjIsometry (e : Q.IsometryEquiv R) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hR : (QuadraticMap.associated R).Nondegenerate) (ξ : orthPlus Q) :
    spinorNormHom R hR (conjIsometry e ξ) = spinorNormHom Q hQ ξ := by
  obtain ⟨a, ha⟩ := exists_tau_eq hQ ξ.2
  let a' : M0 R := ⟨cliffordUnitMap e a, (cliffordUnitMap_mem_M0_iff e a).2 a.2⟩
  have h1 : conjIsometry e ξ = ⟨tau (Subgroup.inclusion M0_le a'), tau_mem_orthPlus hR a'⟩ := by
    apply Subtype.ext
    change (e.toLinearEquiv.symm.trans ξ.1).trans e.toLinearEquiv = _
    rw [← ha]
    exact (tau_cliffordGroupMap e (Subgroup.inclusion M0_le a)).symm
  have h2 : ξ = ⟨tau (Subgroup.inclusion M0_le a), tau_mem_orthPlus hQ a⟩ := Subtype.ext ha.symm
  rw [h1, spinorNormHom_tau hR a']
  conv_rhs => rw [h2, spinorNormHom_tau hQ a]
  congr 2
  exact (multiplier_cliffordUnitMap e hQ hR ⟨a, M0_le_homogeneous a.2⟩)

end QuadFormsKB.Shimura2004
