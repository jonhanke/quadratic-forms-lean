/-
# Witt cancellation, in every characteristic

For quadratic forms $Q$ on $V_0$, $Q_1$ on $V_1$, $Q_2$ on $V_2$ over a field $K$, write
$Q \perp Q_1$ for the orthogonal sum `Q.prod Q₁` on $V_0 \times V_1$,
$(Q \perp Q_1)(x, y) = Q(x) + Q_1(y)$.

**Main result** (`QuadraticForm.equivalent_of_prod_equivalent_prod`, EKM Thm 8.4).
If $V_0, V_1$ are finite-dimensional, the polar form of $Q$ is nondegenerate (*$Q$ nonsingular*)
and the quadratic radical of $Q_1$ is $0$, then
$$Q \perp Q_1 \cong Q \perp Q_2 \implies Q_1 \cong Q_2 .$$

**Special cases.** `QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate` ($Q$, $Q_1$
both nonsingular, every characteristic) and
`QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated` (characteristic $\neq 2$, $Q$ and
$Q_1$ nondegenerate; Lam Ch. I Thm 4.2, Scharlau Ch. 1 §5, O'Meara 42:16, p. 97; Lam and Scharlau locators unverified).

**Why $Q$ must be nonsingular in characteristic $2$.** Over $\mathbb{F}_2$, let $\langle 1 \rangle$
be $x \mapsto x^2$ on $K$ (its polar form is $0$), $\mathbb{H}$ the hyperbolic plane $xy$ and
$[1, 1]$ the anisotropic plane $x^2 + xy + y^2$. Then
$\langle 1 \rangle \perp [1, 1] \cong \langle 1 \rangle \perp \mathbb{H}$ (with $e$ spanning
$\langle 1 \rangle$, the vectors $f_1 + e$, $f_2 + e$ form a hyperbolic pair orthogonal to $e$),
but $[1, 1] \not\cong \mathbb{H}$.

**Proof.** Let $f : Q \perp Q_1 \cong Q \perp Q_2$. The map $\sigma : (v, 0) \mapsto f^{-1}(v, 0)$
on $V_0 \times 0$ is an isometric embedding respecting the polar radical (both sides meet it in
$0$, as $Q$ is nonsingular). Witt's extension theorem (`QuadraticForm.exists_isometryEquiv_extend`,
whose hypothesis holds for $Q \perp Q_1$) extends it to $\rho$; then $g = f \circ \rho$ fixes
$V_0 \times 0$ pointwise, hence maps its orthogonal complement $0 \times V_1$ onto $0 \times V_2$.

Sources: EKM Thm 8.4; Lam Ch. I §4; Scharlau Ch. 1 §5; O'Meara 42:16.
-/
import QuadFormsKB.Witt.Extension

open Module QuadraticMap

namespace QuadraticForm

variable {K V₀ V₁ V₂ : Type*} [Field K] [AddCommGroup V₀] [Module K V₀] [AddCommGroup V₁]
  [Module K V₁] [AddCommGroup V₂] [Module K V₂]

/-- **Nonsingularity in terms of the polar form**: $b$ is nondegenerate iff
$b(v, w) = 0$ for all $w$ forces $v = 0$. -/
theorem nondegenerate_polarBilin_iff (Q : QuadraticForm K V₀) :
    (polarBilin Q).Nondegenerate ↔ ∀ v, (∀ w, polar Q v w = 0) → v = 0 := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (fun x y h => by simpa [polar_comm] using h)]
  rfl

/-- The orthogonal sum of a nonsingular form and a form with zero quadratic radical has zero
quadratic radical. -/
theorem radical_prod_eq_bot {Q : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁}
    (hQ : (polarBilin Q).Nondegenerate) (hQ₁ : Q₁.radical = ⊥) : (Q.prod Q₁).radical = ⊥ := by
  rw [nondegenerate_polarBilin_iff] at hQ
  refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot K).mpr ?_
  obtain ⟨hx0, hx1⟩ := hx
  have hpol : ∀ y, polar (Q.prod Q₁) x y = 0 := fun y => by simpa using congr($hx1 y)
  have h1 : x.1 = 0 := hQ _ fun w => by simpa using hpol (w, 0)
  have h2 : x.2 = 0 := by
    rw [← Submodule.mem_bot K, ← hQ₁]
    refine ⟨?_, LinearMap.ext fun w => by simpa using hpol (0, w)⟩
    simpa [h1] using hx0
  exact Prod.ext h1 h2

/-- The orthogonal sum of two nonsingular forms is nonsingular. -/
theorem nondegenerate_polarBilin_prod {Q : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁}
    (hQ : (polarBilin Q).Nondegenerate) (hQ₁ : (polarBilin Q₁).Nondegenerate) :
    (polarBilin (Q.prod Q₁)).Nondegenerate := by
  rw [nondegenerate_polarBilin_iff] at hQ hQ₁ ⊢
  intro x hx
  exact Prod.ext (hQ _ fun w => by simpa using hx (w, 0)) (hQ₁ _ fun w => by simpa using hx (0, w))

/-- If $Q \perp Q_1$ has zero quadratic radical, so does $Q_1$. -/
theorem radical_eq_bot_of_prod_right {Q : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁}
    (h : (Q.prod Q₁).radical = ⊥) : Q₁.radical = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot K).mpr ?_
  have : ((0 : V₀), x) ∈ (Q.prod Q₁).radical :=
    ⟨by simpa using hx.1, LinearMap.ext fun y => by simpa using congr($(hx.2) y.2)⟩
  rw [h, Submodule.mem_bot] at this
  exact congr($this.2)

/-- An anisotropic form has zero quadratic radical. -/
theorem radical_eq_bot_of_anisotropic {Q : QuadraticForm K V₀} (hQ : Q.Anisotropic) :
    Q.radical = ⊥ :=
  eq_bot_iff.mpr fun x hx => (Submodule.mem_bot K).mpr (hQ x hx.1)

/-- **Witt cancellation** (EKM Thm 8.4; every field, including characteristic $2$).

Let $Q$, $Q_1$, $Q_2$ be quadratic forms on $V_0$, $V_1$, $V_2$ over a field $K$, with $V_0$ and
$V_1$ finite-dimensional. Assume
* $Q$ is **nonsingular**: its polar form $b_Q(x, y) = Q(x + y) - Q(x) - Q(y)$ is nondegenerate;
* the **quadratic radical** of $Q_1$, $\{v \in \operatorname{rad} b_{Q_1} : Q_1(v) = 0\}$, is $0$.

If $Q \perp Q_1 \cong Q \perp Q_2$ (`(Q.prod Q₁).Equivalent (Q.prod Q₂)`) then $Q_1 \cong Q_2$.

The nonsingularity of $Q$ cannot be dropped in characteristic $2$ (module docstring). -/
@[kb "ekm2008" "Thm 8.4; cassels1978 Ch. 2, Thm. 4.1, Cor. 1–2, pp. 21–22 (Witt cancellation)"]
theorem equivalent_of_prod_equivalent_prod [FiniteDimensional K V₀] [FiniteDimensional K V₁]
    {Q : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (hQ : (polarBilin Q).Nondegenerate) (hQ₁ : Q₁.radical = ⊥)
    (h : (Q.prod Q₁).Equivalent (Q.prod Q₂)) : Q₁.Equivalent Q₂ := by
  obtain ⟨f⟩ := h
  have hQ' := hQ
  rw [nondegenerate_polarBilin_iff] at hQ'
  set W := LinearMap.range (LinearMap.inl K V₀ V₁)
  -- `σ (v, 0) = f⁻¹ (v, 0)`
  let σ : W →ₗ[K] V₀ × V₁ :=
    f.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inl K V₀ V₂ ∘ₗ LinearMap.fst K V₀ V₁ ∘ₗ W.subtype
  have hW2 : ∀ w : W, (w : V₀ × V₁).2 = 0 := fun ⟨_, ⟨a, rfl⟩⟩ => rfl
  have hσw : ∀ w : W, σ w = f.symm ((w : V₀ × V₁).1, 0) := fun w => rfl
  have hσ : ∀ w : W, (Q.prod Q₁) (σ w) = (Q.prod Q₁) w := fun w => by
    rw [hσw, f.symm.map_app]
    simp [hW2 w]
  have hker1 : ∀ a : V₀, ((a, 0) : V₀ × V₁) ∈ LinearMap.ker (polarBilin (Q.prod Q₁)) ↔ a = 0 := by
    intro a
    rw [Witt.mem_ker_polarBilin]
    refine ⟨fun h => hQ' a fun w => by simpa using h (w, 0), ?_⟩
    rintro rfl y
    simp
  have hker2 : ∀ a : V₀, ((a, 0) : V₀ × V₂) ∈ LinearMap.ker (polarBilin (Q.prod Q₂)) ↔ a = 0 := by
    intro a
    rw [Witt.mem_ker_polarBilin]
    refine ⟨fun h => hQ' a fun w => by simpa using h (w, 0), ?_⟩
    rintro rfl y
    simp
  have hσR : ∀ w : W, σ w ∈ LinearMap.ker (polarBilin (Q.prod Q₁)) ↔ (w : V₀ × V₁) ∈
      LinearMap.ker (polarBilin (Q.prod Q₁)) := fun w => by
    have hw : (w : V₀ × V₁) = ((w : V₀ × V₁).1, 0) := Prod.ext rfl (hW2 w)
    rw [hw, hker1, hσw, f.symm.mem_ker_polarBilin_iff, hker2]
  obtain ⟨ρ, hρ⟩ := exists_isometryEquiv_extend (Q.prod Q₁) (radical_prod_eq_bot hQ hQ₁) σ hσ hσR
  set g := ρ.trans f
  have hg1 : ∀ a : V₀, g (a, 0) = (a, 0) := fun a => by
    have := hρ ⟨(a, 0), ⟨a, rfl⟩⟩
    change f (ρ (a, 0)) = (a, 0)
    rw [this]
    exact f.apply_symm_apply _
  have hg2 : ∀ b : V₁, (g (0, b)).1 = 0 := fun b => by
    refine hQ' _ fun a => ?_
    have h := g.polar_map (0, b) (a, 0)
    rw [hg1, polar_prod, polar_prod] at h
    simpa using h
  -- the restriction `V₁ → V₂`
  let φ : V₁ →ₗ[K] V₂ :=
    LinearMap.snd K V₀ V₂ ∘ₗ g.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inr K V₀ V₁
  have hφ : ∀ b, g (0, b) = (0, φ b) := fun b => Prod.ext (hg2 b) rfl
  have hφQ : ∀ b, Q₂ (φ b) = Q₁ b := fun b => by
    have := g.map_app (0, b)
    rw [hφ] at this
    simpa using this
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    have : g (0, b) = g 0 := by rw [hφ, hb, map_zero]; rfl
    exact (Submodule.mem_bot K).mpr congr($(g.injective this).2)
  have hφsurj : Function.Surjective φ := fun d => by
    obtain ⟨⟨a, b⟩, hab⟩ := g.surjective (0, d)
    change g (a, b) = (0, d) at hab
    have hsplit : g (a, b) = (a, φ b) := by
      rw [show ((a, b) : V₀ × V₁) = (a, 0) + (0, b) by simp, map_add, hg1, hφ]; simp
    rw [hsplit] at hab
    exact ⟨b, congr($hab.2)⟩
  exact ⟨{ LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with map_app' := hφQ }⟩

/-- **Witt cancellation for nonsingular forms** (every characteristic): if $Q$ and $Q_1$ have
nondegenerate polar forms and $Q \perp Q_1 \cong Q \perp Q_2$, then $Q_1 \cong Q_2$. -/
@[kb "ekm2008" "Thm 8.4 (nonsingular case)"]
theorem equivalent_of_prod_equivalent_prod_of_nondegenerate [FiniteDimensional K V₀]
    [FiniteDimensional K V₁] {Q : QuadraticForm K V₀} {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (hQ : (polarBilin Q).Nondegenerate)
    (hQ₁ : (polarBilin Q₁).Nondegenerate) (h : (Q.prod Q₁).Equivalent (Q.prod Q₂)) :
    Q₁.Equivalent Q₂ :=
  equivalent_of_prod_equivalent_prod hQ (radical_eq_bot_of_nondegenerate Q₁ hQ₁) h

/-- **Witt cancellation in characteristic $\neq 2$** (Lam Ch. I Thm 4.2; Scharlau Ch. 1
§5; O'Meara 42:16, p. 97; Lam and Scharlau locators unverified): if $2$ is invertible in $K$, the associated bilinear forms
$\tfrac12 b_Q$ and $\tfrac12 b_{Q_1}$ (`QuadraticMap.associated`) are nondegenerate, and
$Q \perp Q_1 \cong Q \perp Q_2$, then $Q_1 \cong Q_2$. -/
@[kb "lam2005" "Ch. I, Thm 4.2; omeara1963 §42F, 42:16, p. 97 (Witt cancellation)"]
theorem equivalent_of_prod_equivalent_prod_of_associated [FiniteDimensional K V₀]
    [FiniteDimensional K V₁] [Invertible (2 : K)] {Q : QuadraticForm K V₀}
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (hQ : (associated Q).Nondegenerate)
    (hQ₁ : (associated Q₁).Nondegenerate) (h : (Q.prod Q₁).Equivalent (Q.prod Q₂)) :
    Q₁.Equivalent Q₂ :=
  equivalent_of_prod_equivalent_prod_of_nondegenerate
    ((nondegenerate_polar_iff).mpr ((nondegenerate_associated_iff).mp hQ))
    ((nondegenerate_polar_iff).mpr ((nondegenerate_associated_iff).mp hQ₁)) h

end QuadraticForm
