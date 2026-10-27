/-
# Quadratic spaces and lattices over $\mathcal O_F$

**Layer:** coordinate-free. $F$ is a number field, $V$ a finite-dimensional $F$-vector space and
$Q$ = `Q : QuadraticForm F V` (Mathlib's `QuadraticForm`); $(V, Q)$ is a **quadratic space**, *nondegenerate* if the
polar form $B(x, y) = Q(x+y) - Q(x) - Q(y)$ is (`IsNondeg`). A **lattice** $L \subseteq V$ is a finitely generated
$\mathcal O_F$-submodule spanning $V$ over $F$ (Mathlib's `Submodule.IsLattice F L`); it is projective but need not be
free when $h_F > 1$. Keep *forms* (`QuadForm R n`, a free lattice with a chosen basis) and *lattices* distinct.

**Defines** integrality $Q(L) \subseteq \mathcal O_F$ (`IsIntegralLattice`), isometry of lattices (`IsometricLattices`,
an isometry $\sigma : (V, Q) \to (V', Q')$ with $\sigma L = L'$; **classes** are its equivalence classes),
$O(V)$ (`orthGroupV`), $O(L)$ (`autLatV`), the **Gram form** $Q_b \in$ `QuadForm (𝓞 F) n` of a free lattice with basis
$b$ (`gramForm`: $Q_b(x) = Q(\sum_i x_i b_i)$, Hessian = the Gram matrix $(B(b_i, b_j))$), and the coordinate model
$(F^n, Q_e)$ of $(V, Q)$ in a basis $e$ (`coordForm`).

**Proves** that `gramForm` evaluates correctly (`algebraMap_eval_gramForm`), has Hessian $(B(b_i,b_j))_{ij}$
(`hessian_gramForm`), is unchanged by an isometry carrying one basis to the other (`gramForm_isometry`), and that
$(V, Q) \cong (F^n, Q_e)$ (`coordIsometry`). The coordinate layer (genus, class set, finiteness) is in
`Lattices/{Local,Genus,ClassSet,Finite}.lean`; forms over $\mathcal O_F$ and the bridge to the $\mathbb Q$ files are in
`Lattices/Forms.lean`.

O'Meara 1963, §§81–82, pp. 208–238. *Related work (consulted, not imported):* Tau Ceti's
`IntegralLattice` API and `QuadraticForm/OrthogonalGroup/FiniteAdelic.lean`.
-/
import QuadFormsKB.Lattices.Local
import QuadFormsKB.Equiv.Mathlib

open NumberField Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F]

/-! ### Quadratic spaces and lattices -/

section Abstract

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module (𝓞 F) V'] [IsScalarTower (𝓞 F) F V']

/-- **A nondegenerate quadratic space** $(V, Q)$: the polar bilinear form $B(x,y) = Q(x+y) - Q(x) - Q(y)$ is
nondegenerate. -/
@[kb "omeara1963" "§42B, p. 91 (regular space)"]
def IsNondeg (Q : QuadraticForm F V) : Prop := (QuadraticMap.polarBilin Q).Nondegenerate

/-- **Integral lattice:** $Q(x) \in \mathcal O_F$ for all $x \in L$. In O'Meara's terms this is $\mathfrak nL \subseteq \mathfrak o$
(§82E, p. 227), weaker than his "integral scale" $\mathfrak sL \subseteq \mathfrak o$ (used in 103:4). -/
@[kb "omeara1963" "§82E, p. 227 (norm nL ⊆ 𝓞)"]
def IsIntegralLattice (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V) : Prop :=
  ∀ x ∈ L, Q x ∈ (algebraMap (𝓞 F) F).range

/-- The $\mathcal O_F$-linear map underlying an isometry. -/
abbrev IsometryEquiv.toOLinear {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}
    (σ : Q.IsometryEquiv Q') : V →ₗ[𝓞 F] V' :=
  σ.toLinearEquiv.toLinearMap.restrictScalars (𝓞 F)

/-- **Isometric lattices** $L \subseteq (V, Q)$, $L' \subseteq (V', Q')$: some isometry $\sigma : (V, Q) \cong (V', Q')$
carries $L$ onto $L'$ (O'Meara §82C, p. 222). Its equivalence classes are the **classes** $\mathrm{cls}(L)$. -/
@[kb "omeara1963" "§82A, p. 220 (isometry of lattices); §82C, p. 222 (cls L)"]
def IsometricLattices (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (L : Submodule (𝓞 F) V)
    (L' : Submodule (𝓞 F) V') : Prop :=
  ∃ σ : Q.IsometryEquiv Q', L.map (IsometryEquiv.toOLinear σ) = L'

theorem IsometricLattices.refl (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V) :
    IsometricLattices Q Q L L :=
  ⟨QuadraticMap.IsometryEquiv.refl Q, by
    ext x
    simp only [Submodule.mem_map]
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ hy, fun h => ⟨x, h, rfl⟩⟩⟩

theorem IsometricLattices.symm {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}
    {L : Submodule (𝓞 F) V} {L' : Submodule (𝓞 F) V'} (h : IsometricLattices Q Q' L L') :
    IsometricLattices Q' Q L' L := by
  obtain ⟨σ, rfl⟩ := h
  refine ⟨σ.symm, ?_⟩
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have : σ.symm.toLinearEquiv (σ.toLinearEquiv y) = y := σ.toLinearEquiv.symm_apply_apply y
    rw [this]; exact hy
  · intro hx
    exact ⟨σ.toLinearEquiv x, ⟨x, hx, rfl⟩, σ.toLinearEquiv.symm_apply_apply x⟩

/-- **The orthogonal group** $O(V) = \{g \in \mathrm{GL}(V) : Q(gx) = Q(x)\}$. -/
@[kb "omeara1963" "§41A, p. 84 (orthogonal group)"]
def orthGroupV (Q : QuadraticForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  mul_mem' {a b} ha hb x := by
    change Q (a (b x)) = Q x
    rw [ha, hb]
  one_mem' x := rfl
  inv_mem' {a} ha x := by
    change Q (a.symm x) = Q x
    conv_rhs => rw [← a.apply_symm_apply x]
    rw [ha]

/-- **The automorphism group** $O(L) = \{g \in O(V) : gL = L\}$ of a lattice. -/
@[kb "omeara1963" "§82C, p. 223 (O(L))"]
def autLatV (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V) : Subgroup (orthGroupV Q) where
  carrier := {g | L.map ((g : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) = L}
  mul_mem' {a b} ha hb := by
    change L.map (((a : V ≃ₗ[F] V) * b).toLinearMap.restrictScalars (𝓞 F)) = L
    rw [show ((a : V ≃ₗ[F] V) * b).toLinearMap.restrictScalars (𝓞 F) =
      ((a : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)).comp
        ((b : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) from rfl, Submodule.map_comp]
    rw [show L.map ((b : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) = L from hb]; exact ha
  one_mem' := by
    change L.map ((1 : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) = L
    ext x; simp
  inv_mem' {a} ha := by
    change L.map (((a : V ≃ₗ[F] V)⁻¹).toLinearMap.restrictScalars (𝓞 F)) = L
    have ha' : L.map ((a : V ≃ₗ[F] V).toLinearMap.restrictScalars (𝓞 F)) = L := ha
    conv_lhs => rw [← ha']
    rw [← Submodule.map_comp]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Function.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : (a : V ≃ₗ[F] V)⁻¹ ((a : V ≃ₗ[F] V) y) = y := (a : V ≃ₗ[F] V).symm_apply_apply y
      rw [this]; exact hy
    · intro hx
      exact ⟨x, hx, (a : V ≃ₗ[F] V).symm_apply_apply x⟩

end Abstract

/-! ### Forms of free lattices (Gram forms) -/

section Gram

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
variable {n : ℕ}

/-- Evaluation commutes with a change of coefficient rings $f : A \to B$: $(fQ)(f\vec x) = f(Q(\vec x))$. -/
theorem eval_map_comp {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Q : QuadForm A n)
    (x : Fin n → A) : (Q.map f).eval (fun i => f (x i)) = f (Q.eval x) := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, map_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **A form over $\mathcal O_F$ is determined by its values on $\mathcal O_F^n$**, in fact over any commutative ring
(`ofQuadraticForm_toQuadraticForm`). -/
theorem QuadForm.ext_eval {R : Type*} [CommRing R] {Q₁ Q₂ : QuadForm R n}
    (h : ∀ x, Q₁.eval x = Q₂.eval x) : Q₁ = Q₂ := by
  rw [← QuadForm.ofQuadraticForm_toQuadraticForm Q₁, ← QuadForm.ofQuadraticForm_toQuadraticForm Q₂]
  congr 1
  ext x
  rw [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply, h]

variable (Q : QuadraticForm F V)

/-- The form $y \mapsto Q(\sum_i y_i b_i)$ on $F^n$ for vectors $b_0, \dots, b_{n-1} \in V$, as a `QuadForm F n`. -/
def gramFormF (b : Fin n → V) : QuadForm F n :=
  QuadForm.ofQuadraticForm (Q.comp (Fintype.linearCombination F b))

theorem eval_gramFormF (b : Fin n → V) (y : Fin n → F) :
    (gramFormF Q b).eval y = Q (∑ i, y i • b i) := by
  rw [gramFormF, QuadForm.eval_ofQuadraticForm, QuadraticMap.comp_apply,
    Fintype.linearCombination_apply]

theorem evalIn_gramFormF (b : Fin n → V) (y : Fin n → F) :
    (gramFormF Q b).evalIn F y = Q (∑ i, y i • b i) := eval_gramFormF Q b y

/-- If $b_i \in L$ and $L$ is integral, every coefficient of `gramFormF` is in $\mathcal O_F$. -/
theorem gramFormF_coeff_mem {L : Submodule (𝓞 F) V} (hL : IsIntegralLattice Q L) {b : Fin n → V}
    (hb : ∀ i, b i ∈ L) (i j : Fin n) : (gramFormF Q b).coeff i j ∈ (algebraMap (𝓞 F) F).range := by
  have hQ : ∀ y : Fin n → F, (∀ k, y k ∈ (algebraMap (𝓞 F) F).range) →
      Q.comp (Fintype.linearCombination F b) y ∈ (algebraMap (𝓞 F) F).range := by
    intro y hy
    choose c hc using hy
    refine hL _ ?_
    rw [Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← hc k, algebraMap_smul]
    exact L.smul_mem _ (hb k)
  have he : ∀ k, (Pi.single k (1 : F) : Fin n → F) ∈ intVec := single_one_mem_intVec
  simp only [gramFormF, QuadForm.ofQuadraticForm, QuadForm.ofUpper, Matrix.of_apply]
  split_ifs with h1 h2
  · exact hQ _ (he i)
  · rw [QuadraticMap.polar]
    refine Subring.sub_mem _ (Subring.sub_mem _ (hQ _ (intVec.add_mem (he i) (he j))) (hQ _ (he i)))
      (hQ _ (he j))
  · exact ⟨0, map_zero _⟩

/-- **The Gram form of a free integral lattice** with basis $b = (b_0, \dots, b_{n-1})$ (`b : Basis (Fin n) (𝓞 F) L`):
the form $Q_b \in$ `QuadForm (𝓞 F) n` with $Q_b(x) = Q(\sum_i x_i b_i)$ for $x \in \mathcal O_F^n$
(`algebraMap_eval_gramForm`). Its Hessian is the Gram matrix $(B(b_i, b_j))_{ij}$ (`hessian_gramForm`). -/
@[kb "omeara1963" "§82B, p. 221 (matrix of a free lattice)"]
def gramForm {L : Submodule (𝓞 F) V} (hL : IsIntegralLattice Q L) (b : Basis (Fin n) (𝓞 F) L) :
    QuadForm (𝓞 F) n :=
  QuadForm.ofUpper fun i j => (gramFormF_coeff_mem Q hL (fun k => (b k).2) i j).choose

theorem gramForm_map {L : Submodule (𝓞 F) V} (hL : IsIntegralLattice Q L)
    (b : Basis (Fin n) (𝓞 F) L) :
    (gramForm Q hL b).map (algebraMap (𝓞 F) F) = gramFormF Q (fun k => (b k : V)) := by
  ext i j
  simp only [gramForm, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · exact (gramFormF_coeff_mem Q hL (fun k => (b k).2) i j).choose_spec
  · rw [map_zero, (gramFormF Q _).upper (show j < i from not_le.mp h)]

/-- **The Gram form evaluates to $Q$:** $Q_b(x) = Q(\sum_i x_i b_i)$ in $F$, for $x \in \mathcal O_F^n$. -/
@[kb "omeara1963" "§82B, p. 221"]
theorem algebraMap_eval_gramForm {L : Submodule (𝓞 F) V} (hL : IsIntegralLattice Q L)
    (b : Basis (Fin n) (𝓞 F) L) (x : Fin n → 𝓞 F) :
    algebraMap (𝓞 F) F ((gramForm Q hL b).eval x) = Q (∑ i, x i • (b i : V)) := by
  rw [← eval_map_comp, gramForm_map, eval_gramFormF]
  simp only [algebraMap_smul]

/-- **The Hessian of the Gram form is the Gram matrix** $(B(b_i, b_j))_{ij}$ of the polar form
$B(x, y) = Q(x+y) - Q(x) - Q(y)$. -/
@[kb "omeara1963" "§82B, p. 221"]
theorem hessian_gramForm {L : Submodule (𝓞 F) V} (hL : IsIntegralLattice Q L)
    (b : Basis (Fin n) (𝓞 F) L) (i j : Fin n) :
    algebraMap (𝓞 F) F ((gramForm Q hL b).hessian i j) = QuadraticMap.polar Q (b i : V) (b j : V) := by
  have h := QuadForm.polar_eq_hessian F (gramFormF Q (fun k => (b k : V))) (Pi.single i 1) (Pi.single j 1)
  rw [evalIn_gramFormF, evalIn_gramFormF, evalIn_gramFormF] at h
  have hs : ∀ k : Fin n, ∑ l, (Pi.single k (1 : F) : Fin n → F) l • (b l : V) = b k := by
    intro k
    simp [Pi.single_apply]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hs] at h
  rw [QuadraticMap.polar, h, ← gramForm_map Q hL b]
  simp [QuadForm.hessian, QuadForm.map]

/-- **Isometric free lattices have the same Gram form** in corresponding bases: if $\sigma$ is an isometry with
$\sigma(b_i) = b'_i$, then $Q'_{b'} = Q_b$. -/
theorem gramForm_isometry {V' : Type*} [AddCommGroup V'] [Module F V'] [Module (𝓞 F) V']
    [IsScalarTower (𝓞 F) F V'] {Q' : QuadraticForm F V'} (σ : Q.IsometryEquiv Q')
    {L : Submodule (𝓞 F) V} {L' : Submodule (𝓞 F) V'} (hL : IsIntegralLattice Q L)
    (hL' : IsIntegralLattice Q' L') (b : Basis (Fin n) (𝓞 F) L) (b' : Basis (Fin n) (𝓞 F) L')
    (hσ : ∀ i, σ (b i : V) = (b' i : V')) : gramForm Q' hL' b' = gramForm Q hL b := by
  apply QuadForm.ext_eval
  intro x
  apply IsFractionRing.injective (𝓞 F) F
  rw [algebraMap_eval_gramForm, algebraMap_eval_gramForm, ← σ.map_app]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul F (x i) (b i : V), ← algebraMap_smul F (x i) (b' i : V'), ← hσ]
  exact (σ.toLinearEquiv.map_smul _ _).symm

end Gram

/-! ### Coordinates -/

section Coordinates

variable {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ}

/-- **The coordinate form** $Q_e \in$ `QuadForm F n` of $(V, Q)$ in an $F$-basis $e$: $Q_e(y) = Q(\sum_i y_i e_i)$. -/
def coordForm (Q : QuadraticForm F V) (e : Basis (Fin n) F V) : QuadForm F n :=
  QuadForm.ofQuadraticForm (Q.comp e.equivFun.symm.toLinearMap)

/-- **Every quadratic space is isometric to a coordinate model:** $(V, Q) \cong (F^n, Q_e)$ via $x \mapsto$ the
coordinates of $x$ in the basis $e$. -/
@[kb "omeara1963" "§41B, p. 85 (matrix of a quadratic space; V ≅ ⟨M⟩)"]
def coordIsometry (Q : QuadraticForm F V) (e : Basis (Fin n) F V) :
    Q.IsometryEquiv (coordForm Q e).toQuadraticForm where
  toLinearEquiv := e.equivFun
  map_app' x := by
    rw [QuadForm.toQuadraticForm_apply, coordForm, QuadForm.eval_ofQuadraticForm,
      QuadraticMap.comp_apply, LinearEquiv.coe_coe]
    exact congrArg Q (e.equivFun.symm_apply_apply x)

end Coordinates

end QuadFormsKB.Lattices
