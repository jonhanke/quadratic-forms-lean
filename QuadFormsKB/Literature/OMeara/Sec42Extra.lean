import QuadFormsKB.Literature.OMeara.Sec42
import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec43E

/-!
# O'Meara §42, remaining items (42:4 (b), 42:6, 42:15 (iii)–(iv), and the running-text remarks)

**Setting** (as in `Sec42.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`), $(V, Q)$ a (finite-dimensional)
quadratic space, $B$ = `bil Q` with $B(x,x) = Q(x)$, *regular* = `(QuadraticMap.associated Q).Nondegenerate`,
$O(V)$ = `orth Q`, $\tau_u$ = `symmetry Q u hu`, $\operatorname{rad} S$ = `splitComp (R := F) Q S S`,
$U^\perp$ = `LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U`. A subspace $U$ is regular when
`(QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate`.

**Proves** (O'Meara 1973 printing, Chapter IV, §42, pp. 89–97):
* `eq_orthogonal_of_splitting` (**42:4 (b)**): if $U$ is regular and $V = U \perp W$ then $W = U^\perp$;
* `exists_unique_rep_of_splitting`, `prodMap_rep`, `orthSum`, `orthSum_mul`, `orthSum_inv`, `det_orthSum`
  (**§42 text, audit row 42.r8**): the orthogonal sum $\sigma_1 \perp \sigma_2$ of representations, and the rules
  $\sigma\tau = \sigma_1\tau_1 \perp \sigma_2\tau_2$, $\sigma^{-1} = \sigma_1^{-1} \perp \sigma_2^{-1}$,
  $\det\sigma = \det\sigma_1 \det\sigma_2$;
* `hyperbolic_orth_interchange`, `hyperbolic_orth_not_interchange` (**42:15 (iii), (iv)**);
* `symmetry_eq_symmetry_iff`, `symmetryOfLine_injective` (**§42 text, audit row 42.r25**);
* `hyperbolic_Q_comb`, `mem_isotropic_line_iff`, `hyperbolic_universal` (**§42 text, audit row 42.r20**);
  `hyperbolicPlane_isometric`, `hyperbolicPlane_regular` (**§42 text, audit row 42.r19**); `totallyIsotropic_iff` (**§42 text, audit row 42.r17**);
  `exists_isCompl_rad`, `regular_of_isCompl_rad` (**§42 text, audit row 42.r14**); `finrank_add_finrank_orthogonal_regular`,
  `orthogonal_orthogonal_regular` (**42:6**); `exists_dual_equiv`, `dual_base_unique` (**§42 text, audit row 42.r12**, **§42 text, audit row 42.r13**);
  `exists_orthogonal_basis'` (**42:1**); `mem_orthogonal_iff_bil` (**§42 text, audit row 42.r9**), `rad_eq_orthogonal_top`
  (**§42 text, audit row 42.r10**); `neg_mem_orth` (**§42 text, audit row 42.r21**).

**Conventions.** Indices are 0-based. In 42.r8 the orthogonal sum of representations is stated in two forms:
internally (the book's: $V = V_1 \perp V_2$ inside one space, linear maps into a space $W$ whose images are
orthogonal) and externally (Mathlib's `QuadraticMap.prod` on $V_1 \times V_2$, with `LinearMap.prodMap`); only two
components are treated (the general finite case is an induction).

**Deviations.** 42:15 (iii): the page image (p. 97) reads $\sigma = \tau_{x-\alpha y}$, which is what is proved
(the machine-read text and the audit table had $\tau_{x-\alpha^{-1}y}$, a misreading; no erratum). 42:1 is stated for all finite-dimensional spaces (the case $V = 0$
is trivial). The book's hyperbolic plane $H = Fx + Fy$ is normalized here by $B(x,y) = 1$ in 42:15 (as in
`hyperbolic_symmetry`) and by $B(x,y) \ne 0$ in 42.r20.
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec42Extra

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- **O'Meara §42 (running text, audit row 42.r25)** (p. 97). For anisotropic vectors $u, v$ ($Q(u) \ne 0 \ne Q(v)$) the symmetries agree,
$\tau_u = \tau_v$, if and only if the lines coincide, $Fu = Fv$. ($\Leftarrow$ is `Sp55.symmetry_smul_vec`.) -/
@[kb "omeara1963" "§42E, p. 97 (τ_y = τ_y' iff Fy = Fy')"]
theorem symmetry_eq_symmetry_iff {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0) :
    symmetry Q u hu = symmetry Q v hv ↔ Submodule.span F {u} = Submodule.span F {v} := by
  have key : ∀ {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0), symmetry Q u hu = symmetry Q v hv →
      u ∈ Submodule.span F {v} := by
    intro u v hu hv h
    have h1 : symmetry Q u hu u = symmetry Q v hv u := by rw [h]
    have hself : symmetry Q u hu u = -u := by
      rw [symmetry_apply, bil_self]
      have : 2 * Q u / Q u = 2 := by field_simp
      rw [this, two_smul]; abel
    rw [hself, symmetry_apply] at h1
    have h2 : (2 : F) • u = (2 * bil Q u v / Q v) • v := by
      rw [two_smul]
      calc u + u = u - -u := by abel
        _ = _ := by rw [h1]; abel
    have : u = ((2 : F)⁻¹ * (2 * bil Q u v / Q v)) • v := by
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ iv_two_ne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]; exact key hu hv h
    · rw [Submodule.span_singleton_le_iff_mem]; exact key hv hu h.symm
  · intro h
    have hvu : v ∈ Submodule.span F {u} := h ▸ Submodule.mem_span_singleton_self v
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hvu
    have ht : t ≠ 0 := by rintro rfl; simp [QuadraticMap.map_zero] at hv
    ext x
    rw [symmetry_apply, symmetry_apply, bil_smul_right, Q_smul, smul_smul]
    congr 2
    field_simp

/-- The **anisotropic lines** of $V$: lines $Fu$ with $Q(u) \ne 0$. -/
def AnisoLine : Type _ := {L : Submodule F V // ∃ u, Q u ≠ 0 ∧ L = Submodule.span F {u}}

/-- The symmetry $\tau_L = \tau_u$ attached to an anisotropic line $L = Fu$ (independent of the choice of $u$ by
`symmetry_eq_symmetry_iff`; here $u$ is chosen). -/
def symmetryOfLine (L : AnisoLine Q) : V ≃ₗ[F] V :=
  symmetry Q L.2.choose L.2.choose_spec.1

/-- **O'Meara §42 (running text, audit row 42.r25)** (p. 97, "there are exactly as many symmetries as anisotropic lines"): the map from
anisotropic lines to symmetries is injective, and its image is the set of all symmetries; with
`symmetry_eq_symmetry_iff` this is the bijection. -/
@[kb "omeara1963" "§42E, p. 97 (symmetries ↔ anisotropic lines)"]
theorem symmetryOfLine_injective : Function.Injective (symmetryOfLine Q) := by
  intro L L' h
  apply Subtype.ext
  have h1 := (symmetry_eq_symmetry_iff Q L.2.choose_spec.1 L'.2.choose_spec.1).1 h
  rw [L.2.choose_spec.2, L'.2.choose_spec.2]; exact h1

theorem symmetryOfLine_range : Set.range (symmetryOfLine Q) =
    {τ | ∃ (u : V) (hu : Q u ≠ 0), τ = symmetry Q u hu} := by
  ext τ
  constructor
  · rintro ⟨L, rfl⟩; exact ⟨_, _, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    let L : AnisoLine Q := ⟨Submodule.span F {u}, u, hu, rfl⟩
    refine ⟨L, ?_⟩
    exact ((symmetry_eq_symmetry_iff Q hu L.2.choose_spec.1).2 L.2.choose_spec.2).symm

/-! ### 42:4 (b) -/

/-- **O'Meara 42:4 (b)** (p. 91). Let $U$ be a regular subspace of $V$ and $V = U \perp W$ any splitting
($U$, $W$ complementary and $B(U, W) = 0$). Then $W = U^\perp$. (The book's hypothesis is that $U$ is regular, as
in the first sentence of 42:4; $V$ need not be regular.) -/
@[kb "omeara1963" "§42B, 42:4 (b), p. 91"]
theorem eq_orthogonal_of_splitting {U W : Submodule F V}
    (hU : (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate) (hc : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) :
    W = LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U := by
  have hperp := Sp55.isCompl_perp Q hU
  have hle : W ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U :=
    fun w hw => by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      exact horth u hu w hw
  refine le_antisymm hle fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc x
  have hb : (b : V) ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U :=
    hle b.2
  have ha : (a : V) ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U := by
    have := Submodule.sub_mem _ hx hb
    rwa [add_sub_cancel_right] at this
  have : (a : V) ∈ U ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U :=
    ⟨a.2, ha⟩
  rw [hperp.inf_eq_bot, Submodule.mem_bot] at this
  rw [this, zero_add]; exact b.2

/-! ### 42.r8: orthogonal sums of representations -/

section Rep

variable {X : Type*} [AddCommGroup X] [Module F X] (Q' : QuadraticForm F X)

/-- **O'Meara §42 (running text, audit row 42.r8), existence and uniqueness** (p. 90). Let $V = U \perp W$ be a splitting ($U$, $W$ complementary,
$B(U,W) = 0$) and let $\sigma_1 : U \to X$, $\sigma_2 : W \to X$ be representations ($Q'(\sigma_1 a) = Q(a)$,
$Q'(\sigma_2 b) = Q(b)$) into a quadratic space $(X, Q')$ whose images are orthogonal,
$B'(\sigma_1 U, \sigma_2 W) = 0$. Then there is a unique linear map $\sigma = \sigma_1 \perp \sigma_2 : V \to X$
agreeing with $\sigma_1$ on $U$ and with $\sigma_2$ on $W$, and it is a representation of $V$. -/
@[kb "omeara1963" "§42A, p. 90 (orthogonal sum of representations)"]
theorem exists_unique_rep_of_splitting {U W : Submodule F V} (hc : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) (σ₁ : U →ₗ[F] X) (σ₂ : W →ₗ[F] X)
    (h₁ : ∀ a : U, Q' (σ₁ a) = Q (a : V)) (h₂ : ∀ b : W, Q' (σ₂ b) = Q (b : V))
    (horth' : ∀ (a : U) (b : W), bil Q' (σ₁ a) (σ₂ b) = 0) :
    ∃ σ : V →ₗ[F] X, (∀ a : U, σ a = σ₁ a) ∧ (∀ b : W, σ b = σ₂ b) ∧ (∀ x, Q' (σ x) = Q x) ∧
      ∀ σ' : V →ₗ[F] X, (∀ a : U, σ' a = σ₁ a) → (∀ b : W, σ' b = σ₂ b) → σ' = σ := by
  let e := Submodule.prodEquivOfIsCompl U W hc
  let σ : V →ₗ[F] X := (σ₁.coprod σ₂).comp (e.symm : V →ₗ[F] U × W)
  have hσ : ∀ (a : U) (b : W), σ ((a : V) + b) = σ₁ a + σ₂ b := by
    intro a b
    have : (a : V) + b = e (a, b) := by simp [e]
    simp only [σ, this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.coprod_apply]
  have hU : ∀ a : U, σ a = σ₁ a := fun a => by
    have := hσ a 0; simpa using this
  have hW : ∀ b : W, σ b = σ₂ b := fun b => by
    have := hσ 0 b; simpa using this
  refine ⟨σ, hU, hW, fun x => ?_, fun σ' h1 h2 => ?_⟩
  · obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc x
    rw [hσ, Q_add, Q_add, horth _ a.2 _ b.2, horth' a b, h₁, h₂]
  · refine LinearMap.ext fun x => ?_
    obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc x
    rw [hσ, map_add, h1, h2]

end Rep

/-- **O'Meara §42 (running text, audit row 42.r8), external form** (p. 90). If $\sigma_i : V_i \to W_i$ are representations
($Q_i'(\sigma_i x) = Q_i(x)$), then $\sigma_1 \times \sigma_2 : V_1 \times V_2 \to W_1 \times W_2$ is a
representation of the orthogonal sum `Q₁.prod Q₂` into `Q₁'.prod Q₂'`. -/
@[kb "omeara1963" "§42A, p. 90 (σ₁ ⊥ σ₂ is a representation)"]
theorem prodMap_rep {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
    [AddCommGroup W₁] [Module F W₁] [AddCommGroup W₂] [Module F W₂]
    (Q₁ : QuadraticForm F V₁) (Q₂ : QuadraticForm F V₂) (Q₁' : QuadraticForm F W₁) (Q₂' : QuadraticForm F W₂)
    (σ₁ : V₁ →ₗ[F] W₁) (σ₂ : V₂ →ₗ[F] W₂) (h₁ : ∀ x, Q₁' (σ₁ x) = Q₁ x) (h₂ : ∀ x, Q₂' (σ₂ x) = Q₂ x)
    (x : V₁ × V₂) : (Q₁'.prod Q₂') ((σ₁.prodMap σ₂) x) = (Q₁.prod Q₂) x := by
  simp [QuadraticMap.prod_apply, h₁, h₂]

/-- **O'Meara §42 (running text, audit row 42.r8), the rule $\sigma\tau = \sigma_1\tau_1 \perp \sigma_2\tau_2$** (p. 90), external form. -/
@[kb "omeara1963" "§42A, p. 90 (στ = σ₁τ₁ ⊥ σ₂τ₂)"]
theorem prodMap_comp_prodMap {A₁ A₂ B₁ B₂ C₁ C₂ : Type*} [AddCommGroup A₁] [Module F A₁] [AddCommGroup A₂]
    [Module F A₂] [AddCommGroup B₁] [Module F B₁] [AddCommGroup B₂] [Module F B₂] [AddCommGroup C₁]
    [Module F C₁] [AddCommGroup C₂] [Module F C₂]
    (σ₁ : B₁ →ₗ[F] C₁) (σ₂ : B₂ →ₗ[F] C₂) (τ₁ : A₁ →ₗ[F] B₁) (τ₂ : A₂ →ₗ[F] B₂) :
    (σ₁.prodMap σ₂).comp (τ₁.prodMap τ₂) = (σ₁.comp τ₁).prodMap (σ₂.comp τ₂) := by
  ext <;> simp

/-- **O'Meara §42 (running text, audit row 42.r8), the rule $\sigma^{-1} = \sigma_1^{-1} \perp \sigma_2^{-1}$** (p. 90), external form. -/
@[kb "omeara1963" "§42A, p. 90 (σ⁻¹ = σ₁⁻¹ ⊥ σ₂⁻¹)"]
theorem prodCongr_symm_eq {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
    [AddCommGroup W₁] [Module F W₁] [AddCommGroup W₂] [Module F W₂] (σ₁ : V₁ ≃ₗ[F] W₁) (σ₂ : V₂ ≃ₗ[F] W₂) :
    (σ₁.prodCongr σ₂).symm = σ₁.symm.prodCongr σ₂.symm := rfl

/-- **O'Meara §42 (running text, audit row 42.r8), the rule $\det\sigma = \det\sigma_1\det\sigma_2$** (p. 90), external form. -/
@[kb "omeara1963" "§42A, p. 90 (det σ = det σ₁ · det σ₂)"]
theorem det_prodCongr {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
    [Module.Free F V₁] [Module.Finite F V₁] [Module.Free F V₂] [Module.Finite F V₂]
    (σ₁ : V₁ ≃ₗ[F] V₁) (σ₂ : V₂ ≃ₗ[F] V₂) :
    LinearEquiv.det (σ₁.prodCongr σ₂) = LinearEquiv.det σ₁ * LinearEquiv.det σ₂ := by
  refine Units.ext ?_
  simp only [LinearEquiv.coe_det, Units.val_mul]
  exact LinearMap.det_prodMap (σ₁ : V₁ →ₗ[F] V₁) (σ₂ : V₂ →ₗ[F] V₂)

section OrthSum

variable {U W : Submodule F V}

/-- **The orthogonal sum $\sigma \perp \tau$ of $\sigma \in GL(U)$ and $\tau \in GL(W)$** on $V = U \perp W$
(O'Meara §42 (running text, audit row 42.r8), p. 90, internal form with $V = W$, $V_1 = U$, $V_2 = W$): $(\sigma \perp \tau)(a + b) =
\sigma a + \tau b$. -/
@[kb "omeara1963" "§42A, p. 90 (σ₁ ⊥ ... ⊥ σ_r in O(V))"]
def orthSum (hc : IsCompl U W) (σ : U ≃ₗ[F] U) (τ : W ≃ₗ[F] W) : V ≃ₗ[F] V :=
  ((Submodule.prodEquivOfIsCompl U W hc).symm.trans (σ.prodCongr τ)).trans
    (Submodule.prodEquivOfIsCompl U W hc)

theorem orthSum_apply (hc : IsCompl U W) (σ : U ≃ₗ[F] U) (τ : W ≃ₗ[F] W) (a : U) (b : W) :
    orthSum hc σ τ ((a : V) + b) = ((σ a : U) : V) + ((τ b : W) : V) := by
  have : (a : V) + b = Submodule.prodEquivOfIsCompl U W hc (a, b) := by simp
  rw [this]
  simp [orthSum]

theorem orthSum_ext {hc : IsCompl U W} {f g : V ≃ₗ[F] V}
    (h : ∀ (a : U) (b : W), f ((a : V) + b) = g ((a : V) + b)) : f = g :=
  LinearEquiv.ext fun x => by
    obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc x; exact h a b

/-- $\sigma \perp \tau \in O(V)$ when $\sigma \in O(U)$, $\tau \in O(W)$ and $V = U \perp W$. -/
theorem orthSum_mem_orth (hc : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0)
    {σ : U ≃ₗ[F] U} {τ : W ≃ₗ[F] W} (hσ : σ ∈ orth (Q.comp U.subtype)) (hτ : τ ∈ orth (Q.comp W.subtype)) :
    orthSum hc σ τ ∈ orth Q := by
  intro x
  obtain ⟨a, b, rfl⟩ := Sp55.exists_decomp hc x
  rw [orthSum_apply, Q_add, Q_add, horth _ (σ a).2 _ (τ b).2, horth _ a.2 _ b.2]
  have h1 : Q ((σ a : U) : V) = Q (a : V) := hσ a
  have h2 : Q ((τ b : W) : V) = Q (b : V) := hτ b
  rw [h1, h2]

/-- **O'Meara §42 (running text, audit row 42.r8): $\sigma\tau = \sigma_1\tau_1 \perp \sigma_2\tau_2$** (p. 90). -/
theorem orthSum_mul (hc : IsCompl U W) (σ σ' : U ≃ₗ[F] U) (τ τ' : W ≃ₗ[F] W) :
    orthSum hc σ τ * orthSum hc σ' τ' = orthSum hc (σ * σ') (τ * τ') := by
  refine orthSum_ext (hc := hc) fun a b => ?_
  rw [LinearEquiv.mul_apply, orthSum_apply, orthSum_apply, orthSum_apply]
  rfl

theorem orthSum_one (hc : IsCompl U W) : orthSum hc (1 : U ≃ₗ[F] U) (1 : W ≃ₗ[F] W) = 1 := by
  refine orthSum_ext (hc := hc) fun a b => ?_
  rw [orthSum_apply]; rfl

/-- **O'Meara §42 (running text, audit row 42.r8): $(\sigma_1 \perp \sigma_2)^{-1} = \sigma_1^{-1} \perp \sigma_2^{-1}$** (p. 90). -/
theorem orthSum_inv (hc : IsCompl U W) (σ : U ≃ₗ[F] U) (τ : W ≃ₗ[F] W) :
    (orthSum hc σ τ)⁻¹ = orthSum hc σ⁻¹ τ⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [orthSum_mul, mul_inv_cancel, mul_inv_cancel, orthSum_one]

/-- **O'Meara §42 (running text, audit row 42.r8): $\det(\sigma_1 \perp \sigma_2) = \det\sigma_1 \cdot \det\sigma_2$** (p. 90). -/
theorem det_orthSum (hc : IsCompl U W) (σ : U ≃ₗ[F] U) (τ : W ≃ₗ[F] W) :
    LinearEquiv.det (orthSum hc σ τ) = LinearEquiv.det σ * LinearEquiv.det τ := by
  rw [← det_prodCongr]
  refine Units.ext ?_
  simp only [LinearEquiv.coe_det]
  have : (orthSum hc σ τ : V →ₗ[F] V) =
      ((Submodule.prodEquivOfIsCompl U W hc : (U × W) ≃ₗ[F] V) : (U × W) →ₗ[F] V).comp
        (((σ.prodCongr τ : (U × W) ≃ₗ[F] (U × W)) : (U × W) →ₗ[F] (U × W)).comp
          ((Submodule.prodEquivOfIsCompl U W hc).symm : V →ₗ[F] (U × W))) := by
    ext x; simp [orthSum]
  rw [this, LinearMap.det_conj]

end OrthSum

/-! ### 42:15 (iii), (iv) -/

section Hyperbolic

variable {x y : V}

/-- **O'Meara 42:15 (iii)** (p. 97). Let $H = Fx + Fy$ be a hyperbolic plane ($Q(x) = Q(y) = 0$, $B(x,y) = 1$,
and $x, y$ span $V$, i.e. `hspan`). If $\sigma \in O(H)$ interchanges the isotropic lines, $\sigma x = \alpha y$,
then $\alpha \ne 0$, $\sigma y = \alpha^{-1}x$, $Q(x - \alpha y) \ne 0$ and $\sigma$ is the symmetry
$\tau_{x - \alpha y}$.

(Checked against the page image of p. 97: the book prints $\tau_{x-\alpha y}$; the machine-read text's
$\tau_{x-\alpha^{-1}y}$ is a misreading.) -/
@[kb "omeara1963" "§42E, 42:15 (iii), p. 97"]
theorem hyperbolic_orth_interchange (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hspan : Submodule.span F {x, y} = ⊤) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {α : F} (hσx : σ x = α • y) :
    α ≠ 0 ∧ σ y = α⁻¹ • x ∧ ∃ hu : Q (x - α • y) ≠ 0, σ = symmetry Q (x - α • y) hu := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [iv_bil_zero_left] at hxy; exact zero_ne_one hxy
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hσx
    exact hx0 (σ.map_eq_zero_iff.1 hσx)
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top (x := σ y))
  have hb := iv_bil_orth Q hσ x y
  rw [hσx, ← hpq, hxy, bil_smul_left, bil_add_right, bil_smul_right, bil_smul_right, bil_comm Q y x, hxy,
    bil_self, hy] at hb
  have hp : p = α⁻¹ := by
    field_simp
    linear_combination hb
  have hQ := hσ y
  rw [← hpq, iv_Q_comb, hx, hy, hxy] at hQ
  have hq : q = 0 := by
    have : 2 * p * q = 0 := by linear_combination hQ
    rcases mul_eq_zero.1 this with h | h
    · exfalso
      rcases mul_eq_zero.1 h with h | h
      · exact iv_two_ne h
      · exact inv_ne_zero hα (hp ▸ h)
    · exact h
  have hσy : σ y = α⁻¹ • x := by rw [← hpq, hq, hp]; simp
  have hu : Q (x - α • y) ≠ 0 := hyperbolic_Q_ne_zero Q hx hy hxy hα
  refine ⟨hα, hσy, hu, ?_⟩
  obtain ⟨h1, h2, -⟩ := hyperbolic_symmetry Q hx hy hxy hα rfl hu
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext_on hspan fun z hz => ?_)
  rcases hz with h | h
  · rw [h]; exact hσx.trans h1.symm
  · rw [Set.mem_singleton_iff.1 h]; exact hσy.trans h2.symm

/-- **O'Meara 42:15 (iv), converse** (p. 97). With $H = Fx + Fy$ as in (iii): if $\sigma \in O(H)$ does not
interchange the isotropic lines ($\sigma x \notin Fy$), then there is $\alpha \ne 0$ with $\sigma x = \alpha x$,
$\sigma y = \alpha^{-1}y$, and $\sigma = \tau_{x-y}\tau_{x-\alpha y}$ (for the anisotropic vectors $x-y$,
$x - \alpha y$). -/
@[kb "omeara1963" "§42E, 42:15 (iv), p. 97 (every σ not interchanging the lines is τ_{x−y}τ_{x−αy})"]
theorem hyperbolic_orth_not_interchange (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
    (hspan : Submodule.span F {x, y} = ⊤) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hne : ∀ α : F, σ x ≠ α • y) :
    ∃ α : F, α ≠ 0 ∧ σ x = α • x ∧ σ y = α⁻¹ • y ∧
      ∃ (hu : Q (x - y) ≠ 0) (hv : Q (x - α • y) ≠ 0), σ = symmetry Q (x - y) hu * symmetry Q (x - α • y) hv := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [iv_bil_zero_left] at hxy; exact zero_ne_one hxy
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top (x := σ x))
  have hQx := hσ x
  rw [← hpq, iv_Q_comb, hx, hy, hxy] at hQx
  have hp : p ≠ 0 := by
    rintro rfl
    exact hne q (by rw [← hpq]; simp)
  have hq : q = 0 := by
    have : 2 * p * q = 0 := by linear_combination hQx
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero iv_two_ne hp)
    · exact h
  have hσx : σ x = p • x := by rw [← hpq, hq]; simp
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top (x := σ y))
  have hb := iv_bil_orth Q hσ x y
  rw [hσx, ← hrs, hxy, bil_smul_left, bil_add_right, bil_smul_right, bil_smul_right, hxy, bil_self, hx] at hb
  have hs : s = p⁻¹ := by
    field_simp
    linear_combination hb
  have hQy := hσ y
  rw [← hrs, iv_Q_comb, hx, hy, hxy] at hQy
  have hr : r = 0 := by
    have : 2 * r * s = 0 := by linear_combination hQy
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h iv_two_ne
      · exact h
    · exact absurd (hs ▸ h) (inv_ne_zero hp)
  have hσy : σ y = p⁻¹ • y := by rw [← hrs, hr, hs]; simp
  have hu : Q (x - y) ≠ 0 := by
    simpa using hyperbolic_Q_ne_zero Q hx hy hxy (one_ne_zero (α := F))
  have hv : Q (x - p • y) ≠ 0 := hyperbolic_Q_ne_zero Q hx hy hxy hp
  refine ⟨p, hp, hσx, hσy, hu, hv, ?_⟩
  obtain ⟨-, h1, h2, -⟩ := hyperbolic_rotation Q hx hy hxy hp (u := x - y) (v := x - p • y) rfl rfl hu hv
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext_on hspan fun z hz => ?_)
  rcases hz with h | h
  · rw [h]; exact hσx.trans h1.symm
  · rw [Set.mem_singleton_iff.1 h]; exact hσy.trans h2.symm

end Hyperbolic

/-! ### 42.r20, 42.r19, 42.r17 -/

section Isotropy

/-- **O'Meara §42 (running text, audit row 42.r20), the formula** (p. 94). For $x, y \in V$ with $Q(x) = Q(y) = 0$ and scalars $\alpha, \beta$:
$Q(\alpha x + \beta y) = 2\alpha\beta B(x,y)$. -/
@[kb "omeara1963" "§42D, p. 94 (Q(αx+βy) = 2αβB(x,y))"]
theorem hyperbolic_Q_comb {x y : V} (hx : Q x = 0) (hy : Q y = 0) (α β : F) :
    Q (α • x + β • y) = 2 * α * β * bil Q x y := by
  rw [iv_Q_comb, hx, hy]; ring

/-- **O'Meara §42 (running text, audit row 42.r20), the isotropic lines** (p. 94). In $H = Fx + Fy$ with $Q(x) = Q(y) = 0$,
$B(x,y) \ne 0$ (regular), the vectors $v \ne 0$ with $Q(v) = 0$ are exactly the non-zero vectors of $Fx$ or $Fy$:
the only isotropic lines are $Fx$ and $Fy$. -/
@[kb "omeara1963" "§42D, p. 94 (the only isotropic lines of H are Fx, Fy)"]
theorem mem_isotropic_line_iff {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y ≠ 0)
    (hspan : Submodule.span F {x, y} = ⊤) (v : V) :
    Q v = 0 ↔ v ∈ Submodule.span F {x} ∨ v ∈ Submodule.span F {y} := by
  constructor
  · intro h
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top (x := v))
    rw [hyperbolic_Q_comb Q hx hy] at h
    have : a * b = 0 := by
      have h2 : (2 : F) * bil Q x y ≠ 0 := mul_ne_zero iv_two_ne hxy
      have : (2 * bil Q x y) * (a * b) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left h2
    rcases mul_eq_zero.1 this with rfl | rfl
    · right; simpa using Submodule.smul_mem _ b (Submodule.mem_span_singleton_self y)
    · left; simpa using Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)
  · rintro (h | h)
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 h
      rw [Q_smul, hx, mul_zero]
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 h
      rw [Q_smul, hy, mul_zero]

/-- **O'Meara §42 (running text, audit row 42.r20), universality** (p. 94): $Q(H) = F$ for $H = Fx + Fy$ with $Q(x) = Q(y) = 0$,
$B(x,y) \ne 0$. -/
@[kb "omeara1963" "§42D, p. 94 (the hyperbolic plane is universal)"]
theorem hyperbolic_universal {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y ≠ 0) (c : F) :
    ∃ v ∈ Submodule.span F {x, y}, Q v = c := by
  refine ⟨(c / (2 * bil Q x y)) • x + (1 : F) • y, Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))), ?_⟩
  rw [hyperbolic_Q_comb Q hx hy]
  have : (2 : F) * bil Q x y ≠ 0 := mul_ne_zero iv_two_ne hxy
  field_simp

variable {V' : Type*} [AddCommGroup V'] [Module F V'] (Q' : QuadraticForm F V')

/-- **O'Meara §42 (running text, audit row 42.r19), isometry** (p. 94): any two hyperbolic planes (spaces with matrix
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in some base) are isometric. -/
@[kb "omeara1963" "§42D, p. 94 (all hyperbolic planes are isometric)"]
theorem hyperbolicPlane_isometric (h : IsHyperbolicPlane Q) (h' : IsHyperbolicPlane Q') :
    Nonempty (Q.IsometryEquiv Q') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨c, hc⟩ := h'
  obtain ⟨σ, hσ⟩ := (exists_isometry_iff_gram Q Q' b c).2 ⟨1, by simp, by simp [hb, hc]⟩
  exact ⟨⟨σ, hσ⟩⟩

/-- **O'Meara §42 (running text, audit row 42.r19), regularity and discriminant** (p. 94): a hyperbolic plane is binary, regular, and has a base
with discriminant $-1$ (so $dV = -1$). -/
@[kb "omeara1963" "§42D, p. 94 (hyperbolic planes are regular, of discriminant −1)"]
theorem hyperbolicPlane_regular (h : IsHyperbolicPlane Q) :
    finrank F V = 2 ∧ (QuadraticMap.associated Q).Nondegenerate ∧ ∃ b : Basis (Fin 2) F V, (gram Q b).det = -1 := by
  have h2 : finrank F V = 2 := by
    obtain ⟨b, -⟩ := h
    simpa using finrank_eq_card_basis b
  have t := isHyperbolicPlane_tfae Q h2
  have hreg : (∃ x : V, x ≠ 0 ∧ Q x = 0) ∧ (QuadraticMap.associated Q).Nondegenerate := (t.out 1 2).1 h
  have hdet : ∃ b : Basis (Fin 2) F V, (gram Q b).det = -1 := (t.out 1 3).1 h
  exact ⟨h2, hreg.2, hdet⟩

/-- **O'Meara §42 (running text, audit row 42.r17)** (p. 94). For a subspace $S$: $Q(S) = 0$ if and only if $B(S,S) = 0$ (polarization
$B(x,y) = \tfrac12\{Q(x+y) - Q(x) - Q(y)\}$); so $S$ is totally isotropic iff either holds. -/
@[kb "omeara1963" "§42D, p. 94 (Q(V) = 0 iff B(V,V) = 0)"]
theorem totallyIsotropic_iff (S : Submodule F V) :
    (∀ x ∈ S, Q x = 0) ↔ ∀ x ∈ S, ∀ y ∈ S, bil Q x y = 0 := by
  constructor
  · intro h x hx y hy
    have h1 := h (x + y) (S.add_mem hx hy)
    rw [Q_add, h x hx, h y hy] at h1
    have : (2 : F) * bil Q x y = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left iv_two_ne
  · intro h x hx
    rw [← bil_self]; exact h x hx x hx

end Isotropy

/-! ### 42.r14, 42:6, 42.r9, 42.r10, 42.r12, 42.r13, 42.r21 -/

section Misc

/-- **O'Meara §42 (running text, audit row 42.r14), existence** (p. 93): a radical splitting exists: there is a subspace $U$ with
$V = U \oplus \operatorname{rad} V$ (and then $V = U \perp \operatorname{rad} V$, by the next theorem). -/
@[kb "omeara1963" "§42C, p. 93 (radical splitting exists)"]
theorem exists_isCompl_rad : ∃ U : Submodule F V, IsCompl U (splitComp (R := F) Q ⊤ ⊤) :=
  (Submodule.exists_isCompl (splitComp (R := F) Q ⊤ ⊤)).elim fun q hq => ⟨q, hq.symm⟩

/-- **O'Meara §42 (running text, audit row 42.r14), regularity of $U$** (p. 93). If $V = U \oplus \operatorname{rad} V$ then
$B(U, \operatorname{rad} V) = 0$ (so $V = U \perp \operatorname{rad} V$) and $U$ is regular. -/
@[kb "omeara1963" "§42C, p. 93 (a complement of rad V is regular)"]
theorem regular_of_isCompl_rad {U : Submodule F V} (h : IsCompl U (splitComp (R := F) Q ⊤ ⊤)) :
    (∀ u ∈ U, ∀ r ∈ splitComp (R := F) Q ⊤ ⊤, bil Q u r = 0) ∧
      (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate := by
  have horth : ∀ u ∈ U, ∀ r ∈ splitComp (R := F) Q ⊤ ⊤, bil Q u r = 0 := fun u _ r hr => by
    rw [bil_comm]; exact hr.2 u Submodule.mem_top
  refine ⟨horth, ?_⟩
  have left : ∀ a : U, (∀ b : U, bil (Q.comp U.subtype) a b = 0) → a = 0 := by
    intro a ha
    have hrad : (a : V) ∈ splitComp (R := F) Q ⊤ ⊤ := by
      refine ⟨Submodule.mem_top, fun z _ => ?_⟩
      obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top : z ∈ U ⊔ _)
      rw [bil_add_right, horth _ a.2 r hr, add_zero, ← Sp55.bil_comp_subtype Q U a ⟨c, hc⟩]
      exact ha _
    have : (a : V) ∈ U ⊓ splitComp (R := F) Q ⊤ ⊤ := ⟨a.2, hrad⟩
    rw [h.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  exact ⟨fun a ha => left a ha, fun a ha => left a fun b => by rw [bil_comm]; exact ha b⟩

/-- **O'Meara 42:6 (a)** (p. 92). For a subspace $U$ of a regular space $V$:
$\dim U + \dim U^\perp = \dim V$. -/
@[kb "omeara1963" "§42B, 42:6 (a), p. 92"]
theorem finrank_add_finrank_orthogonal_regular (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (U : Submodule F V) :
    finrank F U + finrank F (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U)
      = finrank F V := by
  have h := LinearMap.BilinForm.finrank_orthogonal hQ U
  have := Submodule.finrank_le U
  omega

/-- **O'Meara 42:6 (b)** (p. 92). For a subspace $U$ of a regular space $V$: $U^{\perp\perp} = U$. -/
@[kb "omeara1963" "§42B, 42:6 (b), p. 92"]
theorem orthogonal_orthogonal_regular (hQ : (QuadraticMap.associated Q).Nondegenerate) (U : Submodule F V) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U) = U :=
  LinearMap.BilinForm.orthogonal_orthogonal hQ (fun a b h => (bil_comm Q b a).trans h) U

/-- **O'Meara §42 (running text, audit row 42.r9)** (p. 90): $U^\perp = \{x \in V \mid B(x, U) = 0\}$. -/
@[kb "omeara1963" "§42B, p. 90 (orthogonal complement U^⊥)"]
theorem mem_orthogonal_iff_bil (U : Submodule F V) (x : V) :
    x ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) U ↔
      ∀ u ∈ U, bil Q x u = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  exact forall₂_congr fun u _ => by rw [bil_comm]

/-- **O'Meara §42 (running text, audit row 42.r10)** (p. 91): $\operatorname{rad} V = V^\perp$. -/
@[kb "omeara1963" "§42B, p. 91 (rad V = V^⊥)"]
theorem rad_eq_orthogonal_top :
    splitComp (R := F) Q ⊤ ⊤ =
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q : LinearMap.BilinForm F V) ⊤ := by
  ext x
  rw [mem_orthogonal_iff_bil]
  exact ⟨fun h u hu => h.2 u hu, fun h => ⟨Submodule.mem_top, h⟩⟩

/-- **O'Meara §42 (running text, audit row 42.r12)** (p. 92). For regular $V$, $x \mapsto B(x, \cdot)$ is an isomorphism $\Phi$ of $V$ onto the
dual space $V'$: $\Phi(x)(y) = B(x,y)$. -/
@[kb "omeara1963" "§42B, p. 92 (V ≅ V' via x ↦ B(x,·))"]
theorem exists_dual_equiv (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ Φ : V ≃ₗ[F] Module.Dual F V, ∀ x y, Φ x y = bil Q x y :=
  ⟨LinearMap.BilinForm.toDual (QuadraticMap.associated Q : LinearMap.BilinForm F V) hQ, fun _ _ =>
    LinearMap.BilinForm.toDual_def hQ⟩

/-- **O'Meara §42 (running text, audit row 42.r13), uniqueness of the dual base** (p. 92). For regular $V$ and a base $(x_i)$, there is at most
one family $(y_j)$ with $B(x_i, y_j) = \delta_{ij}$. -/
@[kb "omeara1963" "§42B, p. 92 (the dual base is unique)"]
theorem dual_base_unique (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [DecidableEq ι]
    (b : Basis ι F V) {y y' : ι → V} (hy : ∀ i j, bil Q (b i) (y j) = if i = j then 1 else 0)
    (hy' : ∀ i j, bil Q (b i) (y' j) = if i = j then 1 else 0) : y = y' := by
  funext j
  rw [← sub_eq_zero]
  refine hQ.2 _ fun v => ?_
  have hL : ((QuadraticMap.associated Q : LinearMap.BilinForm F V).flip (y j - y' j)) = 0 := by
    refine b.ext fun i => ?_
    simp only [LinearMap.flip_apply, LinearMap.zero_apply]
    show bil Q (b i) (y j - y' j) = 0
    rw [bil_sub_right, hy i j, hy' i j, sub_self]
  have := congrArg (fun L : V →ₗ[F] F => L v) hL
  simpa using this

/-- **O'Meara 42:1** (p. 90). A quadratic space has an orthogonal base: $B(x_i, x_j) = 0$ for $i \ne j$. (Stated for
every finite-dimensional space; the book's "non-zero" is only to avoid the empty base.) -/
@[kb "omeara1963" "§42A, 42:1, p. 90"]
theorem exists_orthogonal_basis' :
    ∃ b : Basis (Fin (finrank F V)) F V, ∀ i j, i ≠ j → bil Q (b i) (b j) = 0 := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := (QuadraticMap.associated Q : LinearMap.BilinForm F V)) (QuadraticForm.associated_isSymm F Q)
  exact ⟨b, fun i j hij => hb hij⟩

/-- **O'Meara §42 (running text, audit row 42.r21)** (p. 96): $\pm 1_V \in O(V)$. -/
@[kb "omeara1963" "§42E, p. 96 (±1_V ∈ O(V))"]
theorem neg_mem_orth : (1 : V ≃ₗ[F] V) ∈ orth Q ∧ (LinearEquiv.neg F : V ≃ₗ[F] V) ∈ orth Q :=
  ⟨(orth Q).one_mem, fun x => by simp⟩

end Misc

/-! ### Tags on existing declarations -/

attribute [kb "omeara1963" "§42D, 42:10 (b), p. 95 (a regular isotropic space is universal)"]
  exists_eq_of_isotropic'
attribute [kb "omeara1963" "§42D, p. 95 (proof of 42:10, 42:13: partner y with Q(y) = 0, B(x,y) = 1)"]
  exists_hyp_partner
attribute [kb "omeara1963" "§42E, p. 97 (τ_y is an involution: its own inverse)"] symmetry_symmetry
attribute [kb "omeara1963" "§42E, p. 97 (τ_y reverses every vector of Fy)"] iv_symmetry_self_apply
attribute [kb "omeara1963" "§42A, p. 88 (orthogonal splitting: pairwise orthogonality)"] PairwiseOrth
attribute [kb "omeara1963" "§42B, p. 91 (rad V = V^⊥, radical of a subspace)"] splitComp
attribute [kb "omeara1963" "§42A, p. 89 (discriminant of an orthogonal splitting)"] Sp55.det_gram_orthogonal

attribute [kb "omeara1963" "§41A, p. 84 (O_Q(V) = O_{Q^a}(V) for a ≠ 0)"] orth_smul
attribute [kb "omeara1963" "§41A, p. 82 (standing assumption: 2 ≠ 0 in F)"] iv_two_ne
attribute [kb "omeara1963" "§41A, p. 83 (Q(x) = B(x, x))"] bil_self
attribute [kb "omeara1963" "§42A, p. 89 (U is a component of V = U ⊥ W)"] eq_orthogonal_of_splitting

/-- O'Meara §41A, p. 83: $V$ *represents* $\alpha$ when $\alpha \in Q(V)$, i.e. $Q(x) = \alpha$ for some $x$. -/
@[kb "omeara1963" "§41A, p. 83 (V represents α iff α ∈ Q(V))"]
theorem represents_iff_mem_range (a : F) : (∃ x, Q x = a) ↔ a ∈ Set.range Q := Iff.rfl

attribute [kb "omeara1963" "§41A, p. 83 (orthogonality: B(x, U) = 0)"] mem_orthogonal_iff_bil

end Sec42Extra

end QuadFormsKB.OMeara
