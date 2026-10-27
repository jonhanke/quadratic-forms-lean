/-
# A Witt step for the proof of 91:2: moving one hyperbolic pair onto another

**Setting**: a field $F$ with $2 \in F^\times$, a finite-dimensional regular quadratic space $(V, Q)$ over $F$
(O'Meara's $B$ = `bil Q`), a regular subspace $W$.

**Proves** `exists_orth_map_pair`: if $x, y$ and $x', y'$ are hyperbolic pairs in $W$ with the same matrix
$\begin{pmatrix} 0 & \gamma \\ \gamma & 0 \end{pmatrix}$, there is $\sigma \in O(V)$ with $\sigma x = x'$, $\sigma y = y'$,
fixing $W^\perp$ pointwise and mapping $W$ into $W$. This is Witt's extension theorem (O'Meara 1963, 42:17, p. 98;
`QuadraticForm.exists_isometryEquiv_extend_of_associated`) applied to the isometry
$x \mapsto x'$, $y \mapsto y'$, $v \mapsto v$ ($v \in W^\perp$) of $Fx + Fy + W^\perp$.
-/
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Witt.Extension

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The linear map $(a, b, v) \mapsto a x + b y + v$ from $F \times F \times P$ to $V$. -/
def combMap (x y : V) (P : Submodule F V) : (F × F × P) →ₗ[F] V :=
  LinearMap.toSpanSingleton F V x ∘ₗ LinearMap.fst F F (F × P) +
    LinearMap.toSpanSingleton F V y ∘ₗ (LinearMap.fst F F P ∘ₗ LinearMap.snd F F (F × P)) +
    P.subtype ∘ₗ (LinearMap.snd F F P ∘ₗ LinearMap.snd F F (F × P))

theorem combMap_apply (x y : V) (P : Submodule F V) (a b : F) (v : P) :
    combMap x y P (a, b, v) = a • x + b • y + (v : V) := by
  simp [combMap]

theorem bil_comb_left (x y v z : V) (a b : F) :
    bil Q (a • x + b • y + v) z = a * bil Q x z + b * bil Q y z + bil Q v z := by
  simp [bil_add_left, bil_smul_left]

theorem Q_comb {x y v : V} {γ : F} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = γ)
    (hvx : bil Q v x = 0) (hvy : bil Q v y = 0) (a b : F) :
    Q (a • x + b • y + v) = 2 * a * b * γ + Q v := by
  have h1 : bil Q (a • x + b • y) v = 0 := by
    rw [bil_add_left, bil_smul_left, bil_smul_left, bil_comm Q x v, bil_comm Q y v, hvx, hvy]
    simp
  have h2 : Q (a • x + b • y) = 2 * a * b * γ := by
    rw [Q_add, Q_smul, Q_smul, hQx, hQy, bil_smul_left, bil_smul_right, hxy]; ring
  rw [Q_add, h1, h2]; ring

theorem mem_perp_iff (W : Submodule F V) (v : V) :
    v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W ↔ ∀ w ∈ W, bil Q w v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]

theorem combMap_injective {W : Submodule F V} {x y : V} {γ : F} (hx : x ∈ W) (hy : y ∈ W)
    (hQx : Q x = 0) (hQy : Q y = 0) (hγ : γ ≠ 0) (hxy : bil Q x y = γ) :
    Function.Injective (combMap x y (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b, v⟩ h
  rw [combMap_apply] at h
  have hv := (mem_perp_iff Q W v).mp v.2
  have hvx : bil Q v x = 0 := by rw [bil_comm]; exact hv x hx
  have hvy : bil Q v y = 0 := by rw [bil_comm]; exact hv y hy
  have e1 : bil Q (a • x + b • y + (v : V)) x = 0 := by rw [h]; simp [bil]
  have e2 : bil Q (a • x + b • y + (v : V)) y = 0 := by rw [h]; simp [bil]
  rw [bil_comb_left, bil_self, hQx, bil_comm Q y x, hxy, hvx] at e1
  rw [bil_comb_left, bil_self, hQy, hxy, hvy] at e2
  have hb : b = 0 := by
    have : b * γ = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right hγ
  have ha : a = 0 := by
    have : a * γ = 0 := by linear_combination e2
    exact (mul_eq_zero.mp this).resolve_right hγ
  subst ha hb
  have : (v : V) = 0 := by simpa using h
  simp [Subtype.ext_iff, this]

theorem bil_map_of_isometry (f : V →ₗ[F] V) (hσ : ∀ x, Q (f x) = Q x) (a b : V) :
    bil Q (f a) (f b) = bil Q a b := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  have h1 := hσ (a + b)
  rw [map_add, Q_add, Q_add, hσ, hσ] at h1
  have : 2 * bil Q (f a) (f b) = 2 * bil Q a b := by linear_combination h1
  exact mul_left_cancel₀ h2 this

/-- **Witt step** (O'Meara 1963, 42:17, p. 98, used in the proof of 91:2): hyperbolic pairs $x, y$ and $x', y'$ in a
regular subspace $W$ with $B(x, y) = B(x', y') = \gamma \ne 0$ are carried onto each other by an isometry of $V$ that
fixes $W^\perp$ pointwise and maps $W$ into itself. -/
theorem exists_orth_map_pair (hV : (QuadraticMap.associated Q).Nondegenerate) {W : Submodule F V}
    (_hWreg : ∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) {x y x' y' : V} (hx : x ∈ W) (hy : y ∈ W)
    (hx' : x' ∈ W) (hy' : y' ∈ W) (hQx : Q x = 0) (hQy : Q y = 0) (hQx' : Q x' = 0) (hQy' : Q y' = 0) {γ : F}
    (hγ : γ ≠ 0) (hxy : bil Q x y = γ) (hxy' : bil Q x' y' = γ) :
    ∃ σ ∈ orth Q, σ x = x' ∧ σ y = y' ∧ (∀ v, (∀ w ∈ W, bil Q v w = 0) → σ v = v) ∧ ∀ w ∈ W, σ w ∈ W := by
  classical
  set P := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W with hP
  have hg := combMap_injective Q hx hy hQx hQy hγ hxy
  have hf := combMap_injective Q hx' hy' hQx' hQy' hγ hxy'
  set g := combMap x y P
  set f := combMap x' y' P
  let e := LinearEquiv.ofInjective g hg
  let τ : LinearMap.range g →ₗ[F] V := f ∘ₗ e.symm.toLinearMap
  have hτ : ∀ p, τ (e p) = f p := fun p => by simp [τ]
  have hP' : ∀ v : P, bil Q v x = 0 ∧ bil Q v y = 0 ∧ bil Q v x' = 0 ∧ bil Q v y' = 0 := by
    intro v
    have hv := (mem_perp_iff Q W v).mp v.2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bil_comm] <;> apply hv <;> assumption
  have hQg : ∀ p : F × F × P, Q (g p) = 2 * p.1 * p.2.1 * γ + Q (p.2.2 : V) := by
    rintro ⟨a, b, v⟩
    obtain ⟨h1, h2, -, -⟩ := hP' v
    simp only [g, combMap_apply]
    exact Q_comb Q hQx hQy hxy h1 h2 a b
  have hQf : ∀ p : F × F × P, Q (f p) = 2 * p.1 * p.2.1 * γ + Q (p.2.2 : V) := by
    rintro ⟨a, b, v⟩
    obtain ⟨-, -, h1, h2⟩ := hP' v
    simp only [f, combMap_apply]
    exact Q_comb Q hQx' hQy' hxy' h1 h2 a b
  have hτQ : ∀ s, Q (τ s) = Q (s : V) := by
    intro s
    obtain ⟨p, rfl⟩ := e.surjective s
    rw [hτ]
    have : ((e p : LinearMap.range g) : V) = g p := rfl
    rw [this, hQf, hQg]
  have hτi : Function.Injective τ := hf.comp e.symm.injective
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated Q hV τ hτi hτQ
  have hρ' : ∀ p, ρ (g p) = f p := by
    intro p
    have := hρ (e p)
    rw [hτ] at this
    exact this
  have hσQ : ∀ z, Q (ρ.toLinearEquiv z) = Q z := fun z => ρ.map_app z
  have hfix : ∀ v ∈ P, ρ.toLinearEquiv v = v := by
    intro v hvP
    have := hρ' (0, 0, ⟨v, hvP⟩)
    simpa [g, f, combMap_apply] using this
  refine ⟨ρ.toLinearEquiv, hσQ, ?_, ?_, ?_, ?_⟩
  · have := hρ' (1, 0, 0)
    simpa [g, f, combMap_apply] using this
  · have := hρ' (0, 1, 0)
    simpa [g, f, combMap_apply] using this
  · intro v hv
    exact hfix v ((mem_perp_iff Q W v).mpr (fun w hw => by rw [bil_comm]; exact hv w hw))
  · intro w hw
    have hB : (QuadraticMap.associated Q : LinearMap.BilinForm F V).Nondegenerate := hV
    have hR : (QuadraticMap.associated Q : LinearMap.BilinForm F V).IsRefl :=
      fun a b h => by
        have h' : bil Q a b = 0 := h
        exact (show bil Q b a = 0 by rw [bil_comm]; exact h')
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hR W]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hn' := (mem_perp_iff Q W n).mp hn
    have := bil_map_of_isometry Q (ρ.toLinearEquiv : V →ₗ[F] V) hσQ n w
    have h3 : bil Q (ρ.toLinearEquiv n) (ρ.toLinearEquiv w) = bil Q n w := this
    rw [hfix n hn] at h3
    show bil Q n (ρ.toLinearEquiv w) = 0
    rw [h3, bil_comm]; exact hn' w hw

end Field

end QuadFormsKB.OMeara
