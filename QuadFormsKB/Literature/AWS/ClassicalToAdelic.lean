/-
# Hanke, AWS 2009 notes, §4.1–§4.2: classical to adelic modular forms for $\mathrm{GL}_2$

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.1 (pp. 55–56) and
§4.2 (pp. 56–57). The list D1, D2, … of the notes' derivations is in `AWS/Overview.lean`; this file is
**D9, D10, D11**. Mathlib provides $\mathcal{H}$ (`UpperHalfPlane`), the weight-$k$ slash action of
$\mathrm{GL}_2(\mathbb{R})$ (`ModularForm.slash`), $\Gamma_0(N)$ (`CongruenceSubgroup.Gamma0`), the map
$\gamma \mapsto d \bmod N$ (`CongruenceSubgroup.Gamma0Map`) and Dirichlet characters
(`DirichletCharacter`).

- **D9** (§4.1, (4.1) and p. 56): for $f$ with $(f|_k\gamma) = \chi(d) f$ on $\Gamma_0(N)$ (`HasNebentypus`,
  the transformation law (2.2)/(4.1)), the function $\tilde f(g) = (f|_k g)(i)$ on $\mathrm{GL}_2^+(\mathbb{R})$
  satisfies $\tilde f(\gamma g) = \chi(d)\tilde f(g)$ (`liftGL_mul`).
- **D10** (§4.2, p. 57): $\gamma \mapsto \chi(d_\gamma)$ is a character of $\Gamma_0(N)$ (`charGamma0`).
- **D11** (§4.2, (4.2), p. 57): on $U = \mathrm{SL}_2(\mathbb{R}) \times K_f$ the function
  $\varphi(g_\infty, k) = \tilde f(g_\infty)\,\varepsilon(k)^{-1}$ is left-invariant under the diagonal
  $\Gamma_0(N)$ (`phiU_left`), and its lift $\mathcal{F}$ to $\mathrm{SL}_2(\mathbb{A})$ (via strong approximation,
  `AWS.exists_unique_lift`) satisfies $\mathcal{F}(g k_f) = \varepsilon(k_f)^{-1}\mathcal{F}(g)$
  (`adelicLift_exists`).

*Erratum (candidate; pending author):* p. 57, second bullet: "$\mathcal{F}(g_\mathbb{A}k_f) =
\mathcal{F}(g_\mathbb{A})\cdot\chi(k_f)$". With the notes' definitions ($\chi(k_f) = \prod_p\chi_p(d_p)$,
and (4.2) containing $\prod_p \chi_p(d_p)^{-1}$) one gets $\mathcal{F}(g_\mathbb{A}k_f) =
\mathcal{F}(g_\mathbb{A})\,\chi(k_f)^{-1} = \mathcal{F}(g_\mathbb{A})\,\overline{\chi}(k_f)$; the printed form holds
only if $\chi^2 = 1$ on $K_f(N)$ (`printed_right_equivariance_forces`). Left
$\Gamma_0(N)$-invariance forces the character $\varepsilon^{-1}$ once $\varepsilon \circ \delta = \chi \circ d$.
-/
import QuadFormsKB.Literature.AWS.DoubleCosets

open Matrix ModularForm UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace QuadFormsKB.AWS

variable {N : ℕ}

/-! ### D9: §4.1 -/

/-- **The transformation law of $M_k(N,\chi)$** ((2.2), Definition 2.3.1, rewritten as (4.1),
p. 55): $(f|_{k,\chi}\gamma) = f$ for all $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(N)$,
where $(f|_{k,\chi}\gamma)(z) = f(\gamma z)(cz+d)^{-k}\chi(d)^{-1}$; equivalently
$f|_k\gamma = \chi(d)\,f$ ("the twisted invariance", p. 55). Only the transformation law is
recorded (holomorphy and the cusp conditions play no role in §4.1–§4.2). -/
@[kb "hanke2011aws" "§4.1, (4.1), p. 55"]
def HasNebentypus (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  ∀ γ : Gamma0 N, f ∣[k] (γ : SL(2, ℤ)) = χ (Gamma0Map N γ) • f

/-- **The lift to $\mathrm{GL}_2(\mathbb{R})$** (p. 56): $\tilde f(g) := (f|_k g)(i)$. -/
@[kb "hanke2011aws" "§4.1, p. 56"]
noncomputable def liftGL (k : ℤ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) : ℂ := (f ∣[k] g) I

/-- **D9 (p. 56): $\tilde f(\gamma g) = \chi(d)\,\tilde f(g)$** for $\gamma \in \Gamma_0(N)$ and
$g \in \mathrm{GL}_2^+(\mathbb{R})$ ($\det g > 0$). -/
@[kb "hanke2011aws" "§4.1, p. 56"]
theorem liftGL_mul {k : ℤ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ} (hf : HasNebentypus k χ f)
    (γ : Gamma0 N) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    liftGL k f (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * g) = χ (Gamma0Map N γ) * liftGL k f g := by
  simp only [liftGL]
  rw [SlashAction.slash_mul, ← SL_slash, hf γ, smul_slash]
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by simpa using hg
  simp [σ, hg']

/-! ### D10: the character $\gamma \mapsto \chi(d)$ -/

/-- **D10 (§4.2, p. 57): $\gamma \mapsto \chi(d_\gamma)$ is a character of $\Gamma_0(N)$** (the
restriction to $\Gamma_0(N)$ of "$\chi$ thought of as a character on $K_f(N)$"):
$\chi(d_{\gamma\delta}) = \chi(d_\gamma)\chi(d_\delta)$, because $d_{\gamma\delta} \equiv d_\gamma d_\delta
\pmod N$ when $N \mid c_\gamma$ (`CongruenceSubgroup.Gamma0Map` is a homomorphism). -/
@[kb "hanke2011aws" "§4.2, p. 57"]
noncomputable def charGamma0 (χ : DirichletCharacter ℂ N) : Gamma0 N →* ℂ :=
  χ.toMonoidHom.comp (Gamma0Map N)

@[simp] theorem charGamma0_apply (χ : DirichletCharacter ℂ N) (γ : Gamma0 N) :
    charGamma0 χ γ = χ (Gamma0Map N γ) := rfl

/-! ### D11: the adelic lift (4.2) -/

/-- The real points of $\gamma \in \Gamma_0(N)$, as an element of $\mathrm{SL}_2(\mathbb{R})$. -/
noncomputable def gamma0ToSLR : Gamma0 N →* SL(2, ℝ) :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ)).comp (Gamma0 N).subtype

/-- **The data for the adelic lift** (§4.2, p. 57), abstractly: a group `Kf` (the notes'
$K_f(N) = \prod_p K_p(N)$) with

- `ε : Kf →* ℂ`: the character "$\chi : (x_p) \mapsto \prod_p \chi_p(x_p)$", evaluated at the
  $d$-entries;
- `δ : Γ₀(N) →* SL(2,ℝ) × Kf`: the diagonal embedding $\gamma \mapsto (\gamma_\infty, (\gamma_p)_p)$,
  whose archimedean component is $\gamma$ itself (`δ_fst`);
- `ε_δ`: the compatibility $\varepsilon(\gamma_f) = \chi(d_\gamma)$, which is the content of "writing
  the Dirichlet character $\chi(d)$ as a product of prime-power characters $\chi_p$" (p. 57). -/
structure AdelicSL2Data (N : ℕ) (χ : DirichletCharacter ℂ N) where
  Kf : Type
  [group : Group Kf]
  ε : Kf →* ℂ
  δ : Gamma0 N →* SL(2, ℝ) × Kf
  δ_fst : ∀ γ, (δ γ).1 = gamma0ToSLR γ
  ε_δ : ∀ γ, ε (δ γ).2 = χ (Gamma0Map N γ)

attribute [instance] AdelicSL2Data.group

variable {χ : DirichletCharacter ℂ N}

/-- **The adelic lift on $U = \mathrm{SL}_2(\mathbb{R}) \times K_f$** ((4.2), p. 57):
$\varphi(g_\infty, k_f) = (f|_{k,\chi,\mathbb{A}}(g_\infty,k_f))(i) = \tilde f(g_\infty)\,\varepsilon(k_f)^{-1}$. -/
@[kb "hanke2011aws" "§4.2, (4.2), p. 57"]
noncomputable def phiU (D : AdelicSL2Data N χ) (k : ℤ) (f : ℍ → ℂ) (u : SL(2, ℝ) × D.Kf) : ℂ :=
  liftGL k f (u.1 : GL (Fin 2) ℝ) * (D.ε u.2)⁻¹

theorem ε_ne_zero (D : AdelicSL2Data N χ) (x : D.Kf) : D.ε x ≠ 0 := by
  intro h
  have : D.ε (x * x⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
  rw [map_mul, h, zero_mul] at this
  exact zero_ne_one this

/-- **D11 (p. 57, first bullet, on $U$): left invariance under the diagonal $\Gamma_0(N)$**:
$\varphi(\delta(\gamma)\,u) = \varphi(u)$. ("for all $\gamma \in \Gamma_0(N)$ … we have the invariance
property $(f|_{k,\chi,\mathbb{A}}\gamma)(z) = (f|_{k,\chi}\gamma)(z) = f(z)$".) -/
@[kb "hanke2011aws" "§4.2, p. 57"]
theorem phiU_left (D : AdelicSL2Data N χ) {k : ℤ} {f : ℍ → ℂ} (hf : HasNebentypus k χ f)
    (γ : Gamma0 N) (u : SL(2, ℝ) × D.Kf) : phiU D k f (D.δ γ * u) = phiU D k f u := by
  have hγ : ((gamma0ToSLR γ : SL(2, ℝ)) : GL (Fin 2) ℝ) = (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
    ext i j; simp [gamma0ToSLR]
  have hdet : (0 : ℝ) < (u.1 : GL (Fin 2) ℝ).det.val := by simp
  have hχ : χ (Gamma0Map N γ) ≠ 0 := by rw [← D.ε_δ]; exact ε_ne_zero D _
  simp only [phiU, Prod.fst_mul, Prod.snd_mul, map_mul, D.δ_fst, D.ε_δ, hγ]
  rw [liftGL_mul hf γ hdet]
  field_simp

/-- **D11, second bullet of p. 57, on $U$:** $\varphi(u\,(1,x)) = \varepsilon(x)^{-1}\varphi(u)$. -/
theorem phiU_right (D : AdelicSL2Data N χ) (k : ℤ) (f : ℍ → ℂ) (u : SL(2, ℝ) × D.Kf) (x : D.Kf) :
    phiU D k f (u * (1, x)) = (D.ε x)⁻¹ * phiU D k f u := by
  simp only [phiU, Prod.fst_mul, Prod.snd_mul, mul_one, map_mul, mul_inv]
  ring

/-- **D11 ((4.2) and the two bullets, p. 57): the adelic lift.** Let $S$ ($= \mathrm{SL}_2(\mathbb{A})$) be a
group with an injective homomorphism $j : \mathrm{SL}_2(\mathbb{R}) \times K_f \to S$ (onto
$U = \mathrm{SL}_2(\mathbb{R}) K_f(N)$) and a subgroup $\Gamma$ ($= \mathrm{SL}_2(\mathbb{Q})$) such that

- `hSA` (strong approximation for $\mathrm{SL}_2$): $S = \Gamma\,U$;
- `hΓU` ($\Gamma \cap U = \Gamma_0(N)$, diagonally): if $\gamma \in \Gamma$ and $\gamma\,j(u) \in U$ then
  $\gamma = j(\delta(\gamma_0))$ for some $\gamma_0 \in \Gamma_0(N)$.

Then there is $\mathcal{F} : S \to \mathbb{C}$ with
$\mathcal{F}(\gamma g) = \mathcal{F}(g)$ ($\gamma \in \Gamma$), $\mathcal{F}(j(g_\infty, k_f)) =
\tilde f(g_\infty)\varepsilon(k_f)^{-1}$ (the formula (4.2) on $U$), and
$\mathcal{F}(g\,k_f) = \varepsilon(k_f)^{-1}\,\mathcal{F}(g)$ for $k_f \in K_f$ (**corrected** second bullet;
see the erratum in the module docstring). -/
@[kb "hanke2011aws" "§4.2, (4.2), p. 57"]
theorem adelicLift_exists (D : AdelicSL2Data N χ) {k : ℤ} {f : ℍ → ℂ} (hf : HasNebentypus k χ f)
    {S : Type*} [Group S] (j : SL(2, ℝ) × D.Kf →* S) (hj : Function.Injective j)
    (Γ : Subgroup S) (hSA : ∀ g : S, ∃ γ ∈ Γ, ∃ u, g = γ * j u)
    (hΓU : ∀ γ ∈ Γ, ∀ u u', γ * j u = j u' → ∃ γ₀ : Gamma0 N, γ = j (D.δ γ₀)) :
    ∃ F : S → ℂ, (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) ∧ (∀ u, F (j u) = phiU D k f u) ∧
      ∀ g (x : D.Kf), F (g * j (1, x)) = (D.ε x)⁻¹ * F g := by
  classical
  let φ' : S → ℂ := fun s => if h : s ∈ j.range then phiU D k f h.choose else 0
  have hφ'j : ∀ u, φ' (j u) = phiU D k f u := by
    intro u
    have h : j u ∈ j.range := ⟨u, rfl⟩
    simp only [φ', dif_pos h]
    rw [hj h.choose_spec]
  have hSA' : ∀ g : S, ∃ γ ∈ Γ, ∃ s ∈ j.range, g = γ * s := by
    intro g
    obtain ⟨γ, hγ, u, rfl⟩ := hSA g
    exact ⟨γ, hγ, j u, ⟨u, rfl⟩, rfl⟩
  have hφ : ∀ γ ∈ Γ, ∀ s ∈ j.range, γ * s ∈ j.range → φ' (γ * s) = φ' s := by
    rintro γ hγ _ ⟨u, rfl⟩ ⟨u', hu'⟩
    obtain ⟨γ₀, rfl⟩ := hΓU γ hγ u u' hu'.symm
    rw [← map_mul, hφ'j, hφ'j, phiU_left D hf]
  obtain ⟨F, ⟨hF1, hF2⟩, -⟩ := exists_unique_lift Γ j.range hSA' φ' hφ
  refine ⟨F, hF1, fun u => by rw [hF2 _ ⟨u, rfl⟩, hφ'j], ?_⟩
  -- right equivariance, via `lift_mul_right`
  let Kf' : Subgroup S := (j.comp (MonoidHom.inr _ _)).range
  have hKf' : Kf' ≤ j.range := by rintro _ ⟨x, rfl⟩; exact ⟨(1, x), rfl⟩
  let ε' : S → ℂ := fun s => if h : s ∈ Kf' then (D.ε h.choose)⁻¹ else 1
  have hε'j : ∀ x, ε' (j (1, x)) = (D.ε x)⁻¹ := by
    intro x
    have h : j (1, x) ∈ Kf' := ⟨x, rfl⟩
    simp only [ε', dif_pos h]
    have := hj h.choose_spec
    simp only [MonoidHom.inr_apply, Prod.mk.injEq] at this
    rw [this.2]
  have hε : ∀ s ∈ j.range, ∀ t ∈ Kf', φ' (s * t) = ε' t * φ' s := by
    rintro _ ⟨u, rfl⟩ _ ⟨x, rfl⟩
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
    rw [← map_mul, hφ'j, hφ'j, hε'j, phiU_right]
  intro g x
  have := lift_mul_right Γ j.range Kf' hKf' F φ' ε' hSA' hF1 hF2 hε g (k := j (1, x)) ⟨x, rfl⟩
  rw [this, hε'j]

/-- **Check of the erratum to p. 57:** if a lift satisfied both the (correct) relation
$\mathcal{F}(gk_f) = \varepsilon(k_f)^{-1}\mathcal{F}(g)$ and the printed one
$\mathcal{F}(gk_f) = \mathcal{F}(g)\,\varepsilon(k_f)$ at some $g$ with $\mathcal{F}(g) \ne 0$, then
$\varepsilon(k_f)^2 = 1$; so for $\chi^2 \ne 1$ and $f \ne 0$ the printed relation fails. -/
theorem printed_right_equivariance_forces (D : AdelicSL2Data N χ) {S : Type*} [Group S]
    (j : SL(2, ℝ) × D.Kf →* S) (F : S → ℂ) (g : S) (x : D.Kf)
    (hF : F (g * j (1, x)) = (D.ε x)⁻¹ * F g) (hprinted : F (g * j (1, x)) = F g * D.ε x)
    (hg : F g ≠ 0) : D.ε x ^ 2 = 1 := by
  have hε := ε_ne_zero D x
  rw [hF] at hprinted
  have : (D.ε x)⁻¹ = D.ε x := by
    rw [mul_comm (F g)] at hprinted
    exact mul_right_cancel₀ hg hprinted
  rw [sq]
  calc D.ε x * D.ε x = D.ε x * (D.ε x)⁻¹ := by rw [this]
    _ = 1 := mul_inv_cancel₀ hε

end QuadFormsKB.AWS
