import QuadFormsKB.Literature.OMeara.Sec42

/-!
# O'Meara §42C: radical splittings and representations (42:8 (1))

**Setting** (as in `Sec42.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ and $(V_1, Q_1)$ quadratic spaces over $F$,
$B$ = `bil Q`, $\operatorname{rad} V = \{x : B(x, V) = 0\}$ = `splitComp (R := F) Q ⊤ ⊤`. A *radical splitting*
$V = U \perp \operatorname{rad} V$ is a subspace $U$ complementary to $\operatorname{rad} V$ (`IsCompl`); it is
automatically orthogonal to the radical.

**Proves** (O'Meara 1973 printing, Chapter IV, §42C, p. 93):
* `exists_rep_iff_of_radical` (**42:8 (1)**): if $V = U \perp \operatorname{rad} V$ and
  $V_1 = U_1 \perp \operatorname{rad} V_1$ are radical splittings, then $V$ is represented by $V_1$ iff $U$ is
  represented by $U_1$.

Part (2) of 42:8 is the case $R = F$, $L = V$ of `isometricLat_iff_of_radical` (`Sec82Radical.lean`), cited in
`CitationsIV.lean`.

**Proof notes.** As in the book: a representation $\sigma$ of $V$ gives the representation $\varphi$ of $U$ obtained by
projecting $\sigma x$ to $U_1$ along $\operatorname{rad} V_1$ (`Submodule.projectionOnto`), since
$Q_1(p + z) = Q_1(p)$ for $z$ in the radical; conversely $\varphi \perp 0$ is a representation of $V$.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec42Rad

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
variable {V₁ : Type*} [AddCommGroup V₁] [Module F V₁] (Q₁ : QuadraticForm F V₁)

/-- Adding a radical vector does not change $Q$. -/
theorem iv_Q_add_rad {p r : V} (hr : r ∈ splitComp (R := F) Q ⊤ ⊤) : Q (p + r) = Q p := by
  have h1 : bil Q p r = 0 := by rw [bil_comm]; exact hr.2 p Submodule.mem_top
  have h2 : Q r = 0 := by rw [← bil_self]; exact hr.2 r Submodule.mem_top
  rw [Q_add, h1, h2]; ring

/-- In a radical splitting $V = U \perp \operatorname{rad} V$, $Q(x) = Q(\pi_U x)$. -/
theorem iv_Q_proj {U : Submodule F V} (h : IsCompl U (splitComp (R := F) Q ⊤ ⊤)) (x : V) :
    Q (Submodule.projectionOnto U _ h x : V) = Q x := by
  conv_rhs => rw [← Submodule.projection_add_projection_eq_self h x]
  rw [Submodule.coe_projectionOnto_apply, iv_Q_add_rad Q (Submodule.projection_apply_mem _ _)]

/-- **O'Meara 42:8 (1)** (p. 93). Let $V = U \perp \operatorname{rad} V$ and $V_1 = U_1 \perp \operatorname{rad} V_1$ be
radical splittings. Then there is a representation $\sigma : V \to V_1$ ($Q_1(\sigma x) = Q(x)$) if and only if there
is a representation $\varphi : U \to U_1$ ($Q_1(\varphi u) = Q(u)$). -/
@[kb "omeara1963" "§42C, 42:8 (1), p. 93"]
theorem exists_rep_iff_of_radical {U : Submodule F V} {U₁ : Submodule F V₁}
    (h : IsCompl U (splitComp (R := F) Q ⊤ ⊤)) (h₁ : IsCompl U₁ (splitComp (R := F) Q₁ ⊤ ⊤)) :
    (∃ σ : V →ₗ[F] V₁, ∀ x, Q₁ (σ x) = Q x) ↔ ∃ φ : U →ₗ[F] U₁, ∀ u, Q₁ (φ u : V₁) = Q (u : V) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(Submodule.projectionOnto U₁ _ h₁).comp (σ.comp U.subtype), fun u => ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [iv_Q_proj Q₁ h₁, hσ]
  · rintro ⟨φ, hφ⟩
    refine ⟨U₁.subtype.comp (φ.comp (Submodule.projectionOnto U _ h)), fun x => ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hφ, iv_Q_proj Q h]

end Sec42Rad

end QuadFormsKB.OMeara
