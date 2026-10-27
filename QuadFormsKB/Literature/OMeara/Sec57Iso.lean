/-
# O'Meara §57B: the quadratic space of a quaternion algebra, and isomorphisms (57:7–57:10)

**Setting.** As in `Sec57.lean`: $F$ is a field of characteristic $\ne 2$ and $(\alpha,\beta)$ is Mathlib's
`ℍ[F,α,β]`, with defining base $1, i, j, k$ (O'Meara's $1, x_1, x_2, x_3$, 0-based here); $\alpha, \beta \ne 0$ is
assumed wherever a statement needs it. The quadratic space $(\alpha,\beta)$ of §57B is the algebra with
$Q(x) = Nx$ (`Quaternions57.nrdQuadraticForm`), and O'Meara's bilinear form $B$ is `OMeara.bil`.

**Contents.**
* §57B running text: `bil_nrdQuadraticForm_apply`, `bil_scalar_pure`, `bil_pure_eq_zero_iff`,
  `nrdQuadraticForm_equivalent_diag`, `gram_det` (the discriminant is $1$);
* **57:7** `nonempty_algEquiv_of_pure`;
* **57:8** `tfae_iso` (algebras, norm forms, pure parts);
* **57:9** `tfae_division` (six equivalent conditions);
* **57:10** `algEquiv_one_chain`, `algEquiv_swap`, `algEquiv_scale`, `algEquiv_neg_mul`, `algEquiv_mul_neg`,
  `nonempty_algEquiv_tensor`;
* **57:11** (only the direct statement): `nonempty_algEquiv_mulOpposite`, $(\alpha,\beta) \cong (\alpha,\beta)^{op}$
  by conjugation. The similarity versions of 57:11 are in another file.
-/
import QuadFormsKB.Literature.OMeara.Sec57
import QuadFormsKB.Literature.OMeara.Sec52A
import QuadFormsKB.Witt.Cancellation

open Quaternion QuadFormsKB.Quat QuadFormsKB.OMeara.Quaternions57 TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

universe u

noncomputable section

namespace QuadFormsKB.OMeara

namespace QuatIso57

variable {F : Type u} [Field F] [Invertible (2 : F)] {α β γ δ : F}

/-! ### §57B: the quadratic space $(\alpha,\beta)$ -/

/-- **The bilinear form of the quaternion algebra** (O'Meara 1963, §57B, p. 145): in the defining base,
$B(x,y) = \tfrac12 T(x\bar y) = \xi_0\eta_0 - \alpha\xi_1\eta_1 - \beta\xi_2\eta_2 + \alpha\beta\,\xi_3\eta_3$
for $x = \sum \xi_a e_a$, $y = \sum \eta_a e_a$ (here `re, imI, imJ, imK`); with $Q(x) = Nx$. -/
@[kb "omeara1963" "§57B, p. 145"]
theorem bil_nrdQuadraticForm_apply (x y : ℍ[F,α,β]) :
    bil (nrdQuadraticForm α β) x y =
      x.re * y.re - α * x.imI * y.imI - β * x.imJ * y.imJ + α * β * x.imK * y.imK := by
  have h := two_mul_bil (nrdQuadraticForm α β) x y
  rw [nrdQuadraticForm_apply, nrdQuadraticForm_apply, nrdQuadraticForm_apply] at h
  simp only [nrd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add] at h
  have h2 : (2 : F) * bil (nrdQuadraticForm α β) x y =
      2 * (x.re * y.re - α * x.imI * y.imI - β * x.imJ * y.imJ + α * β * x.imK * y.imK) := by
    rw [h]; ring
  exact mul_left_cancel₀ two_ne_zero' h2

/-- §57B (O'Meara 1963, p. 146): a scalar quaternion is orthogonal to every pure quaternion,
$B(x,y) = \tfrac12 T(x\bar y) = 0$; hence $(\alpha,\beta) = (F1) \perp (\alpha,\beta)^\circ$. -/
@[kb "omeara1963" "§57B, p. 146"]
theorem bil_scalar_pure (r : F) {y : ℍ[F,α,β]} (hy : y.re = 0) :
    bil (nrdQuadraticForm α β) (r : ℍ[F,α,β]) y = 0 := by
  rw [bil_nrdQuadraticForm_apply]; simp [hy]

/-- For pure quaternions, $xy + yx = -2B(x,y)$ (a scalar). -/
theorem mul_add_mul_pure {x y : ℍ[F,α,β]} (hx : x.re = 0) (hy : y.re = 0) :
    x * y + y * x = ((-(2 * bil (nrdQuadraticForm α β) x y) : F) : ℍ[F,α,β]) := by
  rw [bil_nrdQuadraticForm_apply]
  rw [show ∀ c : F, (c : ℍ[F,α,β]) = ⟨c, 0, 0, 0⟩ from fun c => rfl]
  ext <;> simp [hx, hy] <;> ring

/-- §57B (O'Meara 1963, p. 146): for pure quaternions $x, y$: $B(x,y) = 0 \iff xy = -yx$. -/
@[kb "omeara1963" "§57B, p. 146"]
theorem bil_pure_eq_zero_iff {x y : ℍ[F,α,β]} (hx : x.re = 0) (hy : y.re = 0) :
    bil (nrdQuadraticForm α β) x y = 0 ↔ x * y = -(y * x) := by
  have h := mul_add_mul_pure hx hy
  constructor
  · intro h0
    rw [h0, mul_zero, neg_zero, QuaternionAlgebra.coe_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro h0
    rw [h0, neg_add_cancel] at h
    have h' := congrArg QuaternionAlgebra.re h
    rw [QuaternionAlgebra.re_coe] at h'
    have : (2 : F) * bil (nrdQuadraticForm α β) x y = 0 := by
      simpa using h'.symm
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero'

/-- **The quadratic space $(\alpha,\beta)$** (O'Meara 1963, §57B, p. 146):
$(\alpha,\beta) \cong \langle 1\rangle \perp \langle -\alpha\rangle \perp \langle -\beta\rangle \perp
\langle \alpha\beta\rangle$, i.e. the norm form is isometric to the library's diagonal form
`Quat.nrdForm` (the defining base is an orthogonal base with these values of $Q$). -/
@[kb "omeara1963" "§57B, p. 146"]
theorem nrdQuadraticForm_equivalent_diag (α β : F) :
    (nrdQuadraticForm α β).Equivalent (Quat.nrdForm α β).toQuadraticForm :=
  ⟨{ QuaternionAlgebra.linearEquivTuple α 0 β with
     map_app' := fun x => by
       have := toQuadraticForm_nrdForm_apply α β (QuaternionAlgebra.equivTuple α 0 β x)
       rw [Equiv.symm_apply_apply] at this
       rw [nrdQuadraticForm_apply]
       exact this }⟩

/-- Coordinates of the defining base $1, i, j, k$ (Mathlib's `basisOneIJK`). -/
theorem basis_coords (α β : F) (a : Fin 4) :
    (QuaternionAlgebra.basisOneIJK α 0 β a).re = (if a = 0 then 1 else 0) ∧
    (QuaternionAlgebra.basisOneIJK α 0 β a).imI = (if a = 1 then 1 else 0) ∧
    (QuaternionAlgebra.basisOneIJK α 0 β a).imJ = (if a = 2 then 1 else 0) ∧
    (QuaternionAlgebra.basisOneIJK α 0 β a).imK = (if a = 3 then 1 else 0) := by
  have h := QuaternionAlgebra.coe_basisOneIJK_repr α 0 β (QuaternionAlgebra.basisOneIJK α 0 β a)
  rw [Module.Basis.repr_self] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [Finsupp.single_apply] at h0 h1 h2 h3
  exact ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩

/-- The Gram matrix $\bigl(B(e_a, e_b)\bigr)$ of the quaternion algebra in the defining base
$1, i, j, k$ is $\mathrm{diag}(1, -\alpha, -\beta, \alpha\beta)$. -/
theorem gram_matrix (α β : F) :
    LinearMap.BilinForm.toMatrix (QuaternionAlgebra.basisOneIJK α 0 β)
        (QuadraticMap.associated (nrdQuadraticForm α β)) =
      Matrix.diagonal ![1, -α, -β, α * β] := by
  ext a b
  rw [LinearMap.BilinForm.toMatrix_apply]
  change bil (nrdQuadraticForm α β) _ _ = _
  rw [bil_nrdQuadraticForm_apply]
  obtain ⟨a0, a1, a2, a3⟩ := basis_coords α β a
  obtain ⟨b0, b1, b2, b3⟩ := basis_coords α β b
  rw [a0, a1, a2, a3, b0, b1, b2, b3]
  fin_cases a <;> fin_cases b <;> simp

/-- **Discriminant of $(\alpha,\beta)$** (O'Meara 1963, §57B, p. 146: $d(\alpha,\beta) = 1$): the determinant
of the Gram matrix of $B$ in the defining base is $\alpha^2\beta^2 = (\alpha\beta)^2$, a square, so the
discriminant (the determinant modulo squares) is $1$. -/
@[kb "omeara1963" "§57B, p. 146"]
theorem gram_det (α β : F) :
    (LinearMap.BilinForm.toMatrix (QuaternionAlgebra.basisOneIJK α 0 β)
        (QuadraticMap.associated (nrdQuadraticForm α β))).det = α ^ 2 * β ^ 2 ∧
    ∃ s : F, (LinearMap.BilinForm.toMatrix (QuaternionAlgebra.basisOneIJK α 0 β)
        (QuadraticMap.associated (nrdQuadraticForm α β))).det = s ^ 2 := by
  have h : (LinearMap.BilinForm.toMatrix (QuaternionAlgebra.basisOneIJK α 0 β)
        (QuadraticMap.associated (nrdQuadraticForm α β))).det = α ^ 2 * β ^ 2 := by
    rw [gram_matrix, Matrix.det_diagonal]
    simp [Fin.prod_univ_four]; ring
  exact ⟨h, α * β, by rw [h]; ring⟩

/-! ### 57:7 Quaternion algebras from a binary subspace of pure quaternions -/

/-- A pure quaternion squares to $-Nx$. -/
theorem pure_mul_self {x : ℍ[F,γ,δ]} (hx : x.re = 0) : x * x = ((-nrd x : F) : ℍ[F,γ,δ]) := by
  rw [show ∀ c : F, (c : ℍ[F,γ,δ]) = ⟨c, 0, 0, 0⟩ from fun c => rfl]
  ext <;> simp [nrd, hx] <;> ring

section Anticomm

variable {A : Type*} [Ring A] [Algebra F A] [Nontrivial A] [FiniteDimensional F A]

/-- **57:3 plus dimension** (used in 57:7 and 57:10): if $A$ is a nontrivial $F$-algebra of dimension $4$ and
$y, z \in A$ satisfy $y^2 = \alpha$, $z^2 = \beta$, $yz = -zy$ with $\alpha, \beta \ne 0$, then
$A \cong (\alpha,\beta)$ (the subalgebra $F1 + Fy + Fz + Fyz$ of 57:3 is all of $A$ by dimension). -/
theorem nonempty_algEquiv_of_anticomm (hα : α ≠ 0) (hβ : β ≠ 0) (hA : Module.finrank F A = 4)
    (y z : A) (hy : y * y = α • (1 : A)) (hz : z * z = β • (1 : A)) (hyz : y * z = -(z * y)) :
    Nonempty (ℍ[F,α,β] ≃ₐ[F] A) := by
  have hinj := liftHom_injective hα hβ y z hy hz hyz
  set φ := (basisOfAnticomm y z hy hz hyz).liftHom
  have hrank : Module.finrank F ℍ[F,α,β] = Module.finrank F A := by
    rw [QuaternionAlgebra.finrank_eq_four, hA]
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end Anticomm

/-- **57:7, in terms of squares** (O'Meara 1963, 57:7, p. 146): if $x, y$ are elements of a quaternion algebra
$C = (\gamma,\delta)$ with $x^2 = \alpha$, $y^2 = \beta$, $xy = -yx$ ($\alpha, \beta \ne 0$), then
$(\alpha,\beta) \cong C$. (Proposition 57:3 and dimension $4$.) -/
theorem nonempty_algEquiv_of_sq (hα : α ≠ 0) (hβ : β ≠ 0) (x y : ℍ[F,γ,δ])
    (hx : x * x = α • (1 : ℍ[F,γ,δ])) (hy : y * y = β • (1 : ℍ[F,γ,δ])) (hxy : x * y = -(y * x)) :
    Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) :=
  nonempty_algEquiv_of_anticomm hα hβ (QuaternionAlgebra.finrank_eq_four _ _ _) x y hx hy hxy

/-- **57:7** (O'Meara 1963, 57:7, p. 146): let $C = (\gamma,\delta)$ be a quaternion algebra and $x, y$ pure
quaternions of $C$ spanning a binary subspace $\langle -\alpha\rangle \perp \langle -\beta\rangle$ with
$Q(x) = Nx = -\alpha$, $Q(y) = Ny = -\beta$, $B(x,y) = 0$ ($\alpha, \beta \ne 0$). Then $x^2 = \alpha$, $y^2 = \beta$,
$xy = -yx$ (`pure_mul_self`, `bil_pure_eq_zero_iff`), and $C \cong (\alpha,\beta)$ as $F$-algebras. -/
@[kb "omeara1963" "57:7, p. 146"]
theorem nonempty_algEquiv_of_pure (hα : α ≠ 0) (hβ : β ≠ 0) {x y : ℍ[F,γ,δ]} (hx : x.re = 0)
    (hy : y.re = 0) (hxx : nrd x = -α) (hyy : nrd y = -β)
    (hxy : bil (nrdQuadraticForm γ δ) x y = 0) : Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) := by
  refine nonempty_algEquiv_of_sq hα hβ x y ?_ ?_ ((bil_pure_eq_zero_iff hx hy).1 hxy)
  · rw [pure_mul_self hx, hxx, neg_neg]; ext <;> simp
  · rw [pure_mul_self hy, hyy, neg_neg]; ext <;> simp

/-! ### 57:8 Isomorphism of quaternion algebras, of norm forms, of pure parts -/

/-- The splitting $(\alpha,\beta) = F1 \perp (\alpha,\beta)^\circ$ as a linear equivalence, $q \mapsto
(\mathrm{re}\,q,\ q - \mathrm{re}\,q)$. -/
def splitEquiv (α β : F) : ℍ[F,α,β] ≃ₗ[F] F × pureSubmodule α β where
  toFun q := (q.re, ⟨q - (q.re : ℍ[F,α,β]), by simp [mem_pureSubmodule]⟩)
  map_add' a b := by
    ext <;> simp <;> ring
  map_smul' c a := by
    ext <;> simp <;> ring
  invFun p := (p.1 : ℍ[F,α,β]) + (p.2 : ℍ[F,α,β])
  left_inv q := by simp
  right_inv p := by
    obtain ⟨r, p, hp⟩ := p
    rw [mem_pureSubmodule] at hp
    ext <;> simp [hp]

/-- **The scalars and the pure quaternions are orthogonal** (§57B, p. 146): $Q = \langle 1\rangle \perp
Q|_{(\alpha,\beta)^\circ}$, i.e. the norm form of $(\alpha,\beta)$ is isometric to the orthogonal sum of
$x \mapsto x^2$ on $F$ and the norm form of the pure quaternions. -/
@[kb "omeara1963" "§57B, p. 146"]
theorem nrdQuadraticForm_equivalent_prod (α β : F) :
    (nrdQuadraticForm α β).Equivalent
      ((QuadraticMap.sq : QuadraticForm F F).prod (pureQuadraticForm α β)) :=
  ⟨{ splitEquiv α β with
     map_app' := fun q => by
       rw [QuadraticMap.prod_apply, pureQuadraticForm_apply, nrdQuadraticForm_apply]
       simp [splitEquiv, nrd]
       ring }⟩

/-- The pure part of a quaternion algebra has zero radical when $\alpha, \beta \ne 0$ (it is regular). -/
theorem pure_radical_eq_bot (hα : α ≠ 0) (hβ : β ≠ 0) : (pureQuadraticForm α β).radical = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨_, hx2⟩ := hx
  have hpol : ∀ w, QuadraticMap.polar (pureQuadraticForm α β) x w = 0 := fun w => by
    simpa using congr($hx2 w)
  obtain ⟨x, hx0⟩ := x
  rw [mem_pureSubmodule] at hx0
  have e1 := hpol ⟨⟨0, 1, 0, 0⟩, rfl⟩
  have e2 := hpol ⟨⟨0, 0, 1, 0⟩, rfl⟩
  have e3 := hpol ⟨⟨0, 0, 0, 1⟩, rfl⟩
  simp only [QuadraticMap.polar, pureQuadraticForm_apply, Submodule.coe_add] at e1 e2 e3
  simp [nrd, hx0] at e1 e2 e3
  have h1 : x.imI = 0 := by
    have : (2 * α) * x.imI = 0 := by linear_combination -e1
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero' hα)
  have h2 : x.imJ = 0 := by
    have : (2 * β) * x.imJ = 0 := by linear_combination -e2
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero' hβ)
  have h3 : x.imK = 0 := by
    have : (2 * (α * β)) * x.imK = 0 := by linear_combination e3
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero' (mul_ne_zero hα hβ))
  ext <;> simp [hx0, h1, h2, h3]

/-- Algebra isomorphisms are isometries of the norm forms (57:6). -/
theorem equivalent_nrd_of_algEquiv (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) :
    (nrdQuadraticForm α β).Equivalent (nrdQuadraticForm γ δ) :=
  ⟨{ φ.toLinearEquiv with
     map_app' := fun x => by
       rw [nrdQuadraticForm_apply, nrdQuadraticForm_apply]
       exact algEquiv_nrd φ x }⟩

/-- **57:8** (O'Meara 1963, 57:8, p. 146): for quaternion algebras $C = (\alpha,\beta)$ and $D = (\gamma,\delta)$
over $F$ (with $\alpha,\beta \ne 0$; the book assumes this implicitly) the following are equivalent:
(1) $C \cong D$ as $F$-algebras; (2) $C$ and $D$ are isometric as quadratic spaces ($Q = N$); (3) the spaces
$C^\circ$ and $D^\circ$ of pure quaternions are isometric. (1) implies (2) by 57:6 (`algEquiv_nrd`); (2) implies (3) by
Witt cancellation of $\langle 1\rangle$ (`nrdQuadraticForm_equivalent_prod`,
`QuadraticForm.equivalent_of_prod_equivalent_prod`; the book cites Witt's theorem); (3) implies (1) by 57:7. -/
@[kb "omeara1963" "57:8, p. 146"]
theorem tfae_iso (hα : α ≠ 0) (hβ : β ≠ 0) :
    List.TFAE [Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]),
      (nrdQuadraticForm α β).Equivalent (nrdQuadraticForm γ δ),
      (pureQuadraticForm α β).Equivalent (pureQuadraticForm γ δ)] := by
  tfae_have 1 → 2 := fun ⟨φ⟩ => equivalent_nrd_of_algEquiv φ
  tfae_have 2 → 3 := by
    intro h
    have hQ : (QuadraticMap.polarBilin (QuadraticMap.sq : QuadraticForm F F)).Nondegenerate := by
      rw [QuadraticForm.nondegenerate_polarBilin_iff]
      intro v hv
      have := hv 1
      simp [QuadraticMap.polar] at this
      have h2 : (2 : F) * v = 0 := by linear_combination this
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero'
    refine QuadraticForm.equivalent_of_prod_equivalent_prod hQ (pure_radical_eq_bot hα hβ) ?_
    exact ((nrdQuadraticForm_equivalent_prod α β).symm.trans h).trans
      (nrdQuadraticForm_equivalent_prod γ δ)
  tfae_have 3 → 1 := by
    rintro ⟨ψ⟩
    have hn : ∀ p : pureSubmodule α β, nrd (ψ p : ℍ[F,γ,δ]) = nrd (p : ℍ[F,α,β]) := fun p => by
      rw [← pureQuadraticForm_apply, ← pureQuadraticForm_apply, ψ.map_app]
    set iC : pureSubmodule α β := ⟨⟨0, 1, 0, 0⟩, rfl⟩
    set jC : pureSubmodule α β := ⟨⟨0, 0, 1, 0⟩, rfl⟩
    refine nonempty_algEquiv_of_pure hα hβ (x := (ψ iC : ℍ[F,γ,δ])) (y := (ψ jC : ℍ[F,γ,δ]))
      (ψ iC).2 (ψ jC).2 ?_ ?_ ?_
    · rw [hn]; simp [iC, nrd]
    · rw [hn]; simp [jC, nrd]
    · have h1 := two_mul_bil (nrdQuadraticForm γ δ) (ψ iC : ℍ[F,γ,δ]) (ψ jC : ℍ[F,γ,δ])
      have h2 : ((ψ iC : ℍ[F,γ,δ]) + (ψ jC : ℍ[F,γ,δ])) = ((ψ (iC + jC) : pureSubmodule γ δ) : ℍ[F,γ,δ]) := by
        rw [map_add]; rfl
      rw [h2, nrdQuadraticForm_apply, nrdQuadraticForm_apply, nrdQuadraticForm_apply, hn, hn, hn] at h1
      simp [iC, jC, nrd] at h1
      have : (2 : F) * bil (nrdQuadraticForm γ δ) (ψ iC : ℍ[F,γ,δ]) (ψ jC : ℍ[F,γ,δ]) = 0 := by
        rw [h1]; ring
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero'
  tfae_finish

/-! ### 57:9 When a quaternion algebra is split -/

/-- (5) implies (6) of 57:9: if $\alpha\xi^2 + \beta\eta^2 = 1$ then $\alpha = \xi'^2 - \beta\eta'^2$ for some
$\xi', \eta'$ (the form $\langle 1\rangle \perp \langle -\beta\rangle$, the norm form of $F(\sqrt\beta)$,
represents $\alpha$). -/
theorem exists_norm_of_represents (h : ∃ ξ η : F, α * ξ ^ 2 + β * η ^ 2 = 1) :
    ∃ ξ η : F, α = ξ ^ 2 - β * η ^ 2 := by
  obtain ⟨ξ, η, h⟩ := h
  by_cases hξ : ξ = 0
  · subst hξ
    have hη : η ≠ 0 := by
      rintro rfl; simp at h
    refine ⟨(1 + α) / 2, (α - 1) * η / 2, ?_⟩
    have h2 := two_ne_zero' (F := F)
    field_simp
    have hh : β * η ^ 2 = 1 := by linear_combination h
    linear_combination ((α - 1) ^ 2) * hh
  · refine ⟨1 / ξ, η / ξ, ?_⟩
    field_simp
    linear_combination h

/-- (6) implies (5) of 57:9. -/
theorem represents_of_exists_norm (hα : α ≠ 0) (hβ : β ≠ 0) (h : ∃ ξ η : F, α = ξ ^ 2 - β * η ^ 2) :
    ∃ ξ η : F, α * ξ ^ 2 + β * η ^ 2 = 1 := by
  obtain ⟨ξ, η, h⟩ := h
  by_cases hξ : ξ = 0
  · subst hξ
    have hη : η ≠ 0 := by
      rintro rfl; simp at h; exact hα h
    refine ⟨(β⁻¹ - 1) / (2 * η), (β⁻¹ + 1) / 2, ?_⟩
    have h2 := two_ne_zero' (F := F)
    rw [h]
    field_simp
    ring
  · refine ⟨1 / ξ, η / ξ, ?_⟩
    rw [h]
    field_simp
    ring

/-- **57:9** (O'Meara 1963, 57:9, pp. 146–147): for $\alpha, \beta \in F^\times$ the following are equivalent:
(1) $(\alpha,\beta) \cong (1,-1)$ as $F$-algebras;
(2) $(\alpha,\beta)$ is not a division algebra (there is a nonzero non-unit $x$);
(3) $(\alpha,\beta)$ is isotropic ($Nx = 0$ for some $x \ne 0$);
(4) $(\alpha,\beta)^\circ$ is isotropic;
(5) $\langle\alpha\rangle \perp \langle\beta\rangle$ represents $1$ ($\alpha\xi^2 + \beta\eta^2 = 1$);
(6) $\alpha$ is a norm from $E = F(\sqrt\beta)$: stated as $\alpha = \xi^2 - \beta\eta^2$ for some $\xi,\eta\in F$, which
is the norm $N_{E/F}(\xi + \eta\sqrt\beta)$ of the norm form $\langle 1\rangle \perp \langle -\beta\rangle$ of $E$
(O'Meara's proof uses exactly this; if $\beta$ is a square, $E = F\oplus F$ is not a field and the statement is
the condition on this form). The implication (3)$\Rightarrow$(1) and the equivalence (3)$\Leftrightarrow$(5) are
routed through the library's Hilbert symbol (`Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero`,
`hilbertSymbol_eq_one_iff_conic`, `Quat.nonempty_algEquiv_matrix_iff`) and 57:4, rather than through the book's
Witt-theory steps (4)$\Rightarrow$(5)$\Rightarrow$(6); (5)$\Rightarrow$(4) is by an explicit pure isotropic vector
$-\beta\eta\, i + \alpha\xi\, j + k$. -/
@[kb "omeara1963" "57:9, pp. 146–147"]
theorem tfae_division (hα : α ≠ 0) (hβ : β ≠ 0) :
    List.TFAE [Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,1,-1]),
      ∃ x : ℍ[F,α,β], x ≠ 0 ∧ ¬ IsUnit x,
      ∃ x : ℍ[F,α,β], x ≠ 0 ∧ nrdQuadraticForm α β x = 0,
      ∃ x : pureSubmodule α β, x ≠ 0 ∧ pureQuadraticForm α β x = 0,
      ∃ ξ η : F, α * ξ ^ 2 + β * η ^ 2 = 1,
      ∃ ξ η : F, α = ξ ^ 2 - β * η ^ 2] := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have hH : hilbertSymbol F α β = 1 ↔ ∃ x y : F, α * x ^ 2 + β * y ^ 2 = 1 :=
    hilbertSymbol_eq_one_iff_conic F h2 hα hβ
  tfae_have 1 → 2 := by
    rintro ⟨e⟩
    refine ⟨e.symm ⟨0, 1, 1, 0⟩, fun h0 => ?_, fun hu => ?_⟩
    · have := congrArg e h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      have := congrArg QuaternionAlgebra.imI this
      simp at this
    · have hu' : IsUnit (⟨0, 1, 1, 0⟩ : ℍ[F,1,-1]) := by
        have := hu.map e
        rwa [AlgEquiv.apply_symm_apply] at this
      exact ((isUnit_iff_nrd_ne_zero _).1 hu') (by simp [nrd])
  tfae_have 2 → 3 := by
    rintro ⟨x, hx, hn⟩
    refine ⟨x, hx, ?_⟩
    rw [nrdQuadraticForm_apply]
    by_contra h
    exact hn ((isUnit_iff_nrd_ne_zero x).2 h)
  tfae_have 3 → 5 := by
    rintro ⟨x, hx, hn⟩
    rw [nrdQuadraticForm_apply] at hn
    exact hH.1 ((hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 hα hβ).2 ⟨x, hx, hn⟩)
  tfae_have 5 → 3 := by
    intro h
    obtain ⟨x, hx, hn⟩ := (hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 hα hβ).1 (hH.2 h)
    exact ⟨x, hx, by rw [nrdQuadraticForm_apply]; exact hn⟩
  tfae_have 5 → 4 := by
    rintro ⟨ξ, η, h⟩
    refine ⟨⟨⟨0, -(β * η), α * ξ, 1⟩, rfl⟩, fun h0 => ?_, ?_⟩
    · have := congrArg (fun p : pureSubmodule α β => (p : ℍ[F,α,β]).imK) h0
      simp at this
    · rw [pureQuadraticForm_apply]
      simp only [nrd]
      linear_combination (-(α * β)) * h
  tfae_have 4 → 3 := by
    rintro ⟨p, hp, h⟩
    refine ⟨p, fun h0 => hp (Subtype.ext h0), ?_⟩
    rwa [pureQuadraticForm_apply, ← nrdQuadraticForm_apply] at h
  tfae_have 3 → 1 := by
    rintro ⟨x, hx, hn⟩
    rw [nrdQuadraticForm_apply] at hn
    have h1 : hilbertSymbol F α β = 1 :=
      (hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 hα hβ).2 ⟨x, hx, hn⟩
    obtain ⟨e⟩ := (nonempty_algEquiv_matrix_iff h2 hα hβ).2 h1
    obtain ⟨e'⟩ := nonempty_algEquiv_matrix_one_neg_one (F := F)
    exact ⟨e.trans e'.symm⟩
  tfae_have 5 → 6 := exists_norm_of_represents
  tfae_have 6 → 5 := represents_of_exists_norm hα hβ
  tfae_finish

/-! ### 57:10 Isomorphisms of quaternion algebras -/

/-- If $\alpha\xi^2 + \beta\eta^2 = 1$ ($\alpha,\beta\neq 0$) then $(\alpha,\beta) \cong (1,-1)$ (57:9, (5) implies (1)). -/
theorem nonempty_algEquiv_one_neg_one_of_represents (hα : α ≠ 0) (hβ : β ≠ 0) (ξ η : F)
    (h : α * ξ ^ 2 + β * η ^ 2 = 1) : Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,1,-1]) := by
  have key := (tfae_division hα hβ).out 5 1
  exact (key : (∃ ξ η : F, α * ξ ^ 2 + β * η ^ 2 = 1) ↔ Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,1,-1])).1
    ⟨ξ, η, h⟩

/-- **57:10 (1)** (O'Meara 1963, 57:10, p. 147): for $\alpha \ne 0$,
$(1,\alpha) \cong (1,-1) \cong (\alpha,-\alpha)$, and for $\alpha \ne 0, 1$ also $(\alpha,-\alpha) \cong (\alpha, 1-\alpha)$.
(Each follows from 57:9 (5): $1\cdot 1^2 + \alpha\cdot 0^2 = 1$; $\alpha\xi^2 - \alpha\eta^2 = 1$ with
$\xi = \tfrac{1+\alpha}{2\alpha}$, $\eta = \tfrac{1-\alpha}{2\alpha}$; $\alpha\cdot 1^2 + (1-\alpha)\cdot 1^2 = 1$.) -/
@[kb "omeara1963" "57:10 (1), p. 147"]
theorem algEquiv_one_chain (hα : α ≠ 0) :
    Nonempty (ℍ[F,1,α] ≃ₐ[F] ℍ[F,1,-1]) ∧ Nonempty (ℍ[F,1,-1] ≃ₐ[F] ℍ[F,α,-α]) ∧
      (α ≠ 1 → Nonempty (ℍ[F,α,-α] ≃ₐ[F] ℍ[F,α,1-α])) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have hna : -α ≠ 0 := neg_ne_zero.2 hα
  have e2 : Nonempty (ℍ[F,α,-α] ≃ₐ[F] ℍ[F,1,-1]) :=
    nonempty_algEquiv_one_neg_one_of_represents hα hna ((1 + α) / (2 * α)) ((1 - α) / (2 * α)) (by
      field_simp; ring)
  refine ⟨nonempty_algEquiv_one_neg_one_of_represents one_ne_zero hα 1 0 (by ring), ?_, fun h1 => ?_⟩
  · obtain ⟨e⟩ := e2
    exact ⟨e.symm⟩
  · have h1' : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    obtain ⟨e⟩ := e2
    obtain ⟨e'⟩ := nonempty_algEquiv_one_neg_one_of_represents hα h1' 1 1 (by ring)
    exact ⟨e.trans e'.symm⟩

section Local

/-- The quaternion $i$ of $(a,b)$. -/
def qI (a b : F) : ℍ[F,a,b] := ⟨0, 1, 0, 0⟩

/-- The quaternion $j$ of $(a,b)$. -/
def qJ (a b : F) : ℍ[F,a,b] := ⟨0, 0, 1, 0⟩

/-- The quaternion $k = ij$ of $(a,b)$. -/
def qK (a b : F) : ℍ[F,a,b] := ⟨0, 0, 0, 1⟩

theorem qI_mul_qI (a b : F) : qI a b * qI a b = a • (1 : ℍ[F,a,b]) := by ext <;> simp [qI]
theorem qJ_mul_qJ (a b : F) : qJ a b * qJ a b = b • (1 : ℍ[F,a,b]) := by ext <;> simp [qJ]
theorem qK_mul_qK (a b : F) : qK a b * qK a b = (-(a * b)) • (1 : ℍ[F,a,b]) := by ext <;> simp [qK]
theorem qJ_mul_qI (a b : F) : qJ a b * qI a b = -(qI a b * qJ a b) := by ext <;> simp [qI, qJ]
theorem qK_mul_qI (a b : F) : qK a b * qI a b = -(qI a b * qK a b) := by ext <;> simp [qI, qK]

end Local

/-- **57:10 (2), swap** (O'Meara 1963, 57:10, p. 147): $(\beta,\alpha) \cong (\alpha,\beta)$ (take $y = j$, $z = i$
in $(\alpha,\beta)$; 57:7). -/
@[kb "omeara1963" "57:10 (2), p. 147"]
theorem algEquiv_swap (hα : α ≠ 0) (hβ : β ≠ 0) : Nonempty (ℍ[F,β,α] ≃ₐ[F] ℍ[F,α,β]) :=
  nonempty_algEquiv_of_sq hβ hα (qJ α β) (qI α β) (qJ_mul_qJ _ _) (qI_mul_qI _ _) (qJ_mul_qI _ _)

/-- **57:10 (2), scaling** (O'Meara 1963, 57:10, p. 147): for $\lambda, \mu \ne 0$,
$(\alpha,\beta) \cong (\alpha\lambda^2, \beta\mu^2)$ (take $y = \lambda i$, $z = \mu j$ in the second algebra's
quaternion algebra $(\alpha,\beta)$; 57:7). Stated as an isomorphism $(\alpha\lambda^2,\beta\mu^2) \cong (\alpha,\beta)$. -/
@[kb "omeara1963" "57:10 (2), p. 147"]
theorem algEquiv_scale (hα : α ≠ 0) (hβ : β ≠ 0) {l m : F} (hl : l ≠ 0) (hm : m ≠ 0) :
    Nonempty (ℍ[F,α * l ^ 2,β * m ^ 2] ≃ₐ[F] ℍ[F,α,β]) := by
  refine nonempty_algEquiv_of_sq (mul_ne_zero hα (pow_ne_zero 2 hl)) (mul_ne_zero hβ (pow_ne_zero 2 hm))
    (l • qI α β) (m • qJ α β) ?_ ?_ ?_
  · rw [smul_mul_smul_comm, qI_mul_qI, smul_smul]; congr 1; ring
  · rw [smul_mul_smul_comm, qJ_mul_qJ, smul_smul]; congr 1; ring
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, qJ_mul_qI, mul_comm m l, smul_neg, neg_neg]

/-- **57:10 (3)** (O'Meara 1963, 57:10, p. 147; the machine-read statement is garbled): for $\alpha,\beta\ne 0$,
$(\alpha, -\alpha\beta) \cong (\alpha,\beta)$ (take $y = i$, $z = k = ij$, $k^2 = -\alpha\beta$, $ik = -ki$;
57:7). *Reconstruction:* the book's line reads "$(\alpha, \alpha\beta) \cong (\alpha, -\ldots)$" with the right-hand
side lost; `algEquiv_mul_neg` is the form "$(\alpha,\alpha\beta) \cong (\alpha,-\beta)$", which is this statement
for $-\beta$ in place of $\beta$. -/
@[kb "omeara1963" "57:10 (3), p. 147 [garbled; reconstructed]"]
theorem algEquiv_neg_mul (hα : α ≠ 0) (hβ : β ≠ 0) :
    Nonempty (ℍ[F,α,-(α * β)] ≃ₐ[F] ℍ[F,α,β]) :=
  nonempty_algEquiv_of_sq hα (neg_ne_zero.2 (mul_ne_zero hα hβ)) (qI α β) (qK α β) (qI_mul_qI _ _)
    (qK_mul_qK _ _) (by rw [← neg_neg (qI α β * qK α β), ← qK_mul_qI])

/-- **57:10 (3), the form $(\alpha,\alpha\beta) \cong (\alpha,-\beta)$** (reconstruction of the garbled line): for
$\alpha, \beta \ne 0$ (take $y = i$, $z = k$ in $(\alpha,-\beta)$, where $k^2 = \alpha\beta$). -/
@[kb "omeara1963" "57:10 (3), p. 147 [garbled; reconstructed]"]
theorem algEquiv_mul_neg (hα : α ≠ 0) (hβ : β ≠ 0) :
    Nonempty (ℍ[F,α,α * β] ≃ₐ[F] ℍ[F,α,-β]) := by
  have := algEquiv_neg_mul hα (neg_ne_zero.2 hβ)
  rwa [mul_neg, neg_neg] at this

/-! ### 57:10 (4) $(\alpha,\beta)\otimes(\alpha,\gamma) \cong (\alpha,\beta\gamma)\otimes(1,-1)$ -/

section TensorFour

/-- If every generator of a quaternion basis $B$ commutes with $a$, then $a$ commutes with all of the image
of $B$. -/
theorem commute_lift_right {A : Type*} [Ring A] [Algebra F A] {c₁ c₂ c₃ : F}
    (B : QuaternionAlgebra.Basis A c₁ c₂ c₃) (a : A) (hi : Commute a B.i) (hj : Commute a B.j)
    (hk : Commute a B.k) (q : ℍ[F,c₁,c₂,c₃]) : Commute a (B.lift q) := by
  unfold QuaternionAlgebra.Basis.lift
  exact (((Algebra.commute_algebraMap_right q.re a).add_right (hi.smul_right _)).add_right
    (hj.smul_right _)).add_right (hk.smul_right _)

/-- Elements of the images of two quaternion bases commute if the generators do. -/
theorem commute_lift {A : Type*} [Ring A] [Algebra F A] {c₁ c₂ c₃ d₁ d₂ d₃ : F}
    (B : QuaternionAlgebra.Basis A c₁ c₂ c₃) (B' : QuaternionAlgebra.Basis A d₁ d₂ d₃)
    (h : ∀ a, (a = B.i ∨ a = B.j ∨ a = B.k) → ∀ b, (b = B'.i ∨ b = B'.j ∨ b = B'.k) → Commute a b)
    (q : ℍ[F,c₁,c₂,c₃]) (q' : ℍ[F,d₁,d₂,d₃]) : Commute (B.lift q) (B'.lift q') := by
  have h1 : ∀ a, (a = B.i ∨ a = B.j ∨ a = B.k) → Commute a (B'.lift q') := fun a ha =>
    commute_lift_right B' a (h a ha _ (Or.inl rfl)) (h a ha _ (Or.inr (Or.inl rfl)))
      (h a ha _ (Or.inr (Or.inr rfl))) q'
  exact (commute_lift_right B (B'.lift q') (h1 _ (Or.inl rfl)).symm (h1 _ (Or.inr (Or.inl rfl))).symm
    (h1 _ (Or.inr (Or.inr rfl))).symm q).symm

/-- For the bases of 57:3 built from $(y,z)$ and $(u,v)$: if $y,z$ commute with $u,v$ then the two images
commute elementwise (the elements $yz$, $uv$ are products). -/
theorem commute_liftHom_of_commute {A : Type*} [Ring A] [Algebra F A] {a₁ a₂ b₁ b₂ : F}
    (y z u v : A) (hy : y * y = a₁ • (1 : A)) (hz : z * z = a₂ • (1 : A)) (hyz : y * z = -(z * y))
    (hu : u * u = b₁ • (1 : A)) (hv : v * v = b₂ • (1 : A)) (huv : u * v = -(v * u))
    (hyu : Commute y u) (hyv : Commute y v) (hzu : Commute z u) (hzv : Commute z v)
    (q : ℍ[F,a₁,0,a₂]) (q' : ℍ[F,b₁,0,b₂]) :
    Commute ((basisOfAnticomm y z hy hz hyz).liftHom q) ((basisOfAnticomm u v hu hv huv).liftHom q') := by
  refine commute_lift (basisOfAnticomm y z hy hz hyz) (basisOfAnticomm u v hu hv huv) ?_ q q'
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact hyu
  · exact hyv
  · exact hyu.mul_right hyv
  · exact hzu
  · exact hzv
  · exact hzu.mul_right hzv
  · exact hyu.mul_left hzu
  · exact hyv.mul_left hzv
  · exact (hyu.mul_right hyv).mul_left (hzu.mul_right hzv)

/-- $i \otimes 1$ in $(a,b)\otimes(a,c)$ (the book's $x_1 \otimes 1$). -/
def tY (a b c : F) : ℍ[F,a,b] ⊗[F] ℍ[F,a,c] := qI a b ⊗ₜ[F] (1 : ℍ[F,a,c])

/-- $j \otimes j$ in $(a,b)\otimes(a,c)$ (the book's $x_2 \otimes y_2$). -/
def tZ (a b c : F) : ℍ[F,a,b] ⊗[F] ℍ[F,a,c] := qJ a b ⊗ₜ[F] qJ a c

/-- $a^{-1}\, i \otimes i$ in $(a,b)\otimes(a,c)$; its square is $1$. -/
def tU (a b c : F) : ℍ[F,a,b] ⊗[F] ℍ[F,a,c] := a⁻¹ • (qI a b ⊗ₜ[F] qI a c)

/-- $1 \otimes j$ in $(a,b)\otimes(a,c)$ (the book's $1 \otimes y_2$). -/
def tV (a b c : F) : ℍ[F,a,b] ⊗[F] ℍ[F,a,c] := (1 : ℍ[F,a,b]) ⊗ₜ[F] qJ a c

section Rel

variable (a b c : F)

theorem tY_mul_tY : tY a b c * tY a b c = a • (1 : ℍ[F,a,b] ⊗[F] ℍ[F,a,c]) := by
  simp [tY, Algebra.TensorProduct.tmul_mul_tmul, qI_mul_qI, TensorProduct.smul_tmul',
    Algebra.TensorProduct.one_def]

theorem tZ_mul_tZ : tZ a b c * tZ a b c = (b * c) • (1 : ℍ[F,a,b] ⊗[F] ℍ[F,a,c]) := by
  simp [tZ, Algebra.TensorProduct.tmul_mul_tmul, qJ_mul_qJ, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_smul, Algebra.TensorProduct.one_def]
  rw [mul_comm c b]

theorem tY_mul_tZ : tY a b c * tZ a b c = -(tZ a b c * tY a b c) := by
  simp [tY, tZ, Algebra.TensorProduct.tmul_mul_tmul, qJ_mul_qI, TensorProduct.neg_tmul]

theorem tV_mul_tV : tV a b c * tV a b c = c • (1 : ℍ[F,a,b] ⊗[F] ℍ[F,a,c]) := by
  simp [tV, Algebra.TensorProduct.tmul_mul_tmul, qJ_mul_qJ, TensorProduct.tmul_smul,
    Algebra.TensorProduct.one_def]

theorem tU_mul_tU (ha : a ≠ 0) : tU a b c * tU a b c = (1 : F) • (1 : ℍ[F,a,b] ⊗[F] ℍ[F,a,c]) := by
  simp only [tU, smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, qI_mul_qI,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  field_simp

theorem tU_mul_tV : tU a b c * tV a b c = -(tV a b c * tU a b c) := by
  simp [tU, tV, smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, qJ_mul_qI,
    TensorProduct.tmul_neg]

theorem commute_tY_tU : Commute (tY a b c) (tU a b c) := by
  unfold tU
  refine Commute.smul_right ?_ _
  unfold Commute SemiconjBy tY
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem commute_tY_tV : Commute (tY a b c) (tV a b c) := by
  unfold Commute SemiconjBy tY tV
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem commute_tZ_tU : Commute (tZ a b c) (tU a b c) := by
  unfold tU
  refine Commute.smul_right ?_ _
  unfold Commute SemiconjBy tZ
  simp [Algebra.TensorProduct.tmul_mul_tmul, qJ_mul_qI, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem commute_tZ_tV : Commute (tZ a b c) (tV a b c) := by
  unfold Commute SemiconjBy tZ tV
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end Rel

/-- If two subalgebras $X, Y$ of a finite-dimensional algebra $A$ commute elementwise, are isomorphic to central
simple algebras $P, Q$, and $\dim P \cdot \dim Q = \dim A$, then $A \cong P \otimes_F Q$ (52:2 and dimension). -/
theorem equiv_tensor_of_subalgebras {A P Q : Type u} [Ring A] [Algebra F A] [FiniteDimensional F A]
    [Ring P] [Algebra F P] [FiniteDimensional F P] [Algebra.IsCentral F P] [IsSimpleRing P]
    [Ring Q] [Algebra F Q] [FiniteDimensional F Q] [Algebra.IsCentral F Q] [IsSimpleRing Q]
    (X Y : Subalgebra F A) (eX : P ≃ₐ[F] X) (eY : Q ≃ₐ[F] Y)
    (hcomm : ∀ b ∈ X, ∀ c ∈ Y, Commute b c)
    (hdim : Module.finrank F P * Module.finrank F Q = Module.finrank F A) :
    Nonempty (A ≃ₐ[F] P ⊗[F] Q) := by
  have : Algebra.IsCentral F X := Algebra.IsCentral.of_algEquiv F P ↥X eX
  have : IsSimpleRing X := IsSimpleRing.of_ringEquiv eX.toRingEquiv inferInstance
  have : Algebra.IsCentral F Y := Algebra.IsCentral.of_algEquiv F Q ↥Y eY
  have : IsSimpleRing Y := IsSimpleRing.of_ringEquiv eY.toRingEquiv inferInstance
  have : FiniteDimensional F Y := LinearEquiv.finiteDimensional eY.toLinearEquiv
  have hinj := subalgebraTensorMap_injective X Y hcomm
  have hrank : Module.finrank F (X ⊗[F] Y) = Module.finrank F A := by
    rw [Module.finrank_tensorProduct, ← eX.toLinearEquiv.finrank_eq, ← eY.toLinearEquiv.finrank_eq, hdim]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (subalgebraTensorMap X Y hcomm).toLinearMap)).1 hinj
  exact ⟨(AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.trans
    (Algebra.TensorProduct.congr eX.symm eY.symm)⟩

/-- **57:10 (4)** (O'Meara 1963, 57:10, p. 148): for $\alpha,\beta,\gamma \ne 0$,
$(\alpha,\beta)\otimes(\alpha,\gamma) \cong (\alpha,\beta\gamma)\otimes(1,-1)$ as $F$-algebras.
Following the book, in $A = (\alpha,\beta)\otimes(\alpha,\gamma)$ let $X = F1 + F(i\otimes 1) + F(j\otimes j) +
F(k\otimes j)$, which is $\cong (\alpha,\beta\gamma)$ by 57:3 ($y = i\otimes 1$, $z = j\otimes j$). For $Y$ the
book's definition is garbled in the machine-read text; we take $Y$ spanned by $1$, $u = \alpha^{-1}\, i\otimes i$,
$v = 1\otimes j$ and $uv$ ($u^2 = 1$, $v^2 = \gamma$, $uv = -vu$), so $Y \cong (1,\gamma) \cong (1,-1)$ by 57:3
and 57:10 (1). The generators of $X$ and $Y$ commute, both are central simple (57:2), so
$X \otimes Y \to A$ is injective (52:2, `subalgebraTensorMap_injective`) and bijective by dimension $16$. -/
@[kb "omeara1963" "57:10 (4), p. 148"]
theorem nonempty_algEquiv_tensor (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    Nonempty (ℍ[F,α,β] ⊗[F] ℍ[F,α,γ] ≃ₐ[F] ℍ[F,α,β * γ] ⊗[F] ℍ[F,1,-1]) := by
  have hβγ : β * γ ≠ 0 := mul_ne_zero hβ hγ
  have : Nontrivial (ℍ[F,α,β] ⊗[F] ℍ[F,α,γ]) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left F _ _
      (FaithfulSMul.algebraMap_injective F ℍ[F,α,γ])
  obtain ⟨eX⟩ := nonempty_algEquiv_range_liftHom hα hβγ (tY α β γ) (tZ α β γ) (tY_mul_tY α β γ)
    (tZ_mul_tZ α β γ) (tY_mul_tZ α β γ)
  obtain ⟨eY⟩ := nonempty_algEquiv_range_liftHom (one_ne_zero (α := F)) hγ (tU α β γ) (tV α β γ)
    (tU_mul_tU α β γ hα) (tV_mul_tV α β γ) (tU_mul_tV α β γ)
  obtain ⟨e1⟩ := (algEquiv_one_chain hγ).1
  have hcomm := fun q q' => commute_liftHom_of_commute (F := F) _ _ _ _ (tY_mul_tY α β γ)
    (tZ_mul_tZ α β γ) (tY_mul_tZ α β γ) (tU_mul_tU α β γ hα) (tV_mul_tV α β γ) (tU_mul_tV α β γ)
    (commute_tY_tU α β γ)
    (commute_tY_tV α β γ) (commute_tZ_tU α β γ) (commute_tZ_tV α β γ) q q'
  have : Algebra.IsCentral F ℍ[F,α,β * γ] := isCentral hα hβγ
  have : IsSimpleRing ℍ[F,α,β * γ] := isSimpleRing hα hβγ
  have : Algebra.IsCentral F ℍ[F,1,γ] := isCentral one_ne_zero hγ
  have : IsSimpleRing ℍ[F,1,γ] := isSimpleRing one_ne_zero hγ
  obtain ⟨e⟩ := equiv_tensor_of_subalgebras _ _ eX eY (by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
    exact hcomm q q') (by
    rw [QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four, Module.finrank_tensorProduct,
      QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four])
  exact ⟨e.trans (Algebra.TensorProduct.congr (AlgEquiv.refl) e1)⟩

end TensorFour

/-! ### 57:11 (direct statement) -/

/-- **57:11** (O'Meara 1963, 57:11, p. 148), the direct form of "$(\alpha,\beta)$ is isomorphic to its own
reciprocal": conjugation $x \mapsto \bar x$ is an anti-automorphism of $(\alpha,\beta)$, hence an $F$-algebra
isomorphism $(\alpha,\beta) \to (\alpha,\beta)^{op}$ (the reciprocal algebra is the opposite algebra). The book
deduces this from $(\alpha,\beta)\otimes(\alpha,\beta)\sim 1$; that similarity version is not treated here. -/
@[kb "omeara1963" "57:11, p. 148"]
def algEquivMulOpposite (α β : F) : ℍ[F,α,β] ≃ₐ[F] (ℍ[F,α,β])ᵐᵒᵖ where
  toFun x := MulOpposite.op (star x)
  invFun y := star (MulOpposite.unop y)
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by simp [star_mul]
  map_add' x y := by simp
  commutes' r := by
    rw [MulOpposite.algebraMap_apply]
    simp

theorem nonempty_algEquiv_mulOpposite (α β : F) : Nonempty (ℍ[F,α,β] ≃ₐ[F] (ℍ[F,α,β])ᵐᵒᵖ) :=
  ⟨algEquivMulOpposite α β⟩

end QuatIso57

end QuadFormsKB.OMeara
