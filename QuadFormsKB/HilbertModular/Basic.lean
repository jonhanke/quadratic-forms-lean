/-
# Hilbert modular forms I: $\mathbb{H}^\iota$, the componentwise action, the slash operator

Throughout, $\iota$ is a finite index type (later: the real places of a totally real field $F$, so
$|\iota| = d = [F:\mathbb{Q}]$). We write $\mathbb{H}^\iota$ for the functions $\iota \to \mathbb{H}$ (`ι → ℍ`).

* **The group.** $G_\infty^+ = \prod_{v\in\iota}\mathrm{GL}_2^+(\mathbb{R})$ (`ι → GL(2, ℝ)⁺`, the Pi group of
  Mathlib's `Matrix.GLPos`), acting on $\mathbb{H}^\iota$ componentwise by Möbius transformations:
  $(\gamma z)_v = \gamma_v z_v = \frac{a_v z_v + b_v}{c_v z_v + d_v}$ (Mathlib's `Pi.mulAction'`).
  Only positive determinants occur: these are the matrices that preserve $\mathbb{H}$ in every variable, and
  $\mathrm{GL}_2^+(F)$ (totally positive determinant) maps into this group (`Congruence.lean`).
* **The slash operator, vector weight** $\vec k = (k_v) \in \mathbb{Z}^\iota$ (`slashVec`):
  $$(f\,|_{\vec k}\,\gamma)(z) = f(\gamma z)\prod_{v}\det(\gamma_v)^{k_v-1}\,(c_vz_v + d_v)^{-k_v}.$$
  **Parallel weight** $k \in \mathbb{Z}$ is $\vec k = (k, \dots, k)$; it is the `SlashAction ℤ` instance, so the
  notation `f ∣[k] γ` of Mathlib applies.
* **Normalization of the determinant.** We use Mathlib's normalization $\det(\gamma_v)^{k_v - 1}$
  (`ModularForm.slash_def`: $|\det g|^{k-1}$), not Shimura's $\det(\gamma_v)^{k_v/2}$. The two differ by the
  factor $\prod_v\det(\gamma_v)^{k_v/2-1}$, which is $1$ on $\mathrm{SL}_2$; on $\mathrm{SL}_2$ (where modular forms are
  defined below) they agree. The choice makes $d = 1$ literally Mathlib's operator (`slash_unique`), and avoids
  half-integral real powers.
* **Holomorphy** (`IsHolomorphic`): $f$ is continuous on $\mathbb{H}^\iota$ and holomorphic in each variable
  separately (the others fixed). By Osgood's lemma this is equivalent to joint complex differentiability (and
  by Hartogs' theorem continuity could even be dropped); we take the Osgood form because series of holomorphic
  functions (theta and Eisenstein series) are checked one variable at a time with Mathlib's one-variable
  theory. `IsHolomorphic.of_differentiableOn` gives it from joint differentiability.
* **Bounded / zero at $\infty$** (`IsBoundedAtImInftyPi`, `IsZeroAtImInftyPi`): along the filter
  `atImInftyPi` $= \bigwedge_v \operatorname{comap}(\operatorname{Im} z_v)\,\mathrm{atTop}$, i.e. on regions
  $\{z : \operatorname{Im}z_v \ge A \text{ for all } v\}$. For one variable this is Mathlib's `atImInfty`
  (`atImInftyPi_unique`).

Main results: `jFactor_mul` (the cocycle), the `SlashAction` laws (`slashVec_mul`, `slashVec_one`),
`slashVec_mul_mul` (product of forms: weights add), `IsHolomorphic.slash` (the slash of a holomorphic function
is holomorphic), and the $d = 1$ comparison with Mathlib (`slash_unique`, `isHolomorphic_unique_iff`,
`isBoundedAtImInftyPi_unique_iff`).

Sources: Shimura, *The special values of the zeta functions associated with Hilbert modular forms*, Duke
Math. J. 45 (1978), §1 [unverified]; Garrett, *Holomorphic Hilbert Modular Forms* (1990), Ch. 1 [unverified];
Freitag, *Hilbert Modular Forms* (1990), Ch. I [unverified].
-/
import Mathlib
import QuadFormsKB.Citation

open Complex UpperHalfPlane Matrix Filter
open scoped MatrixGroups Manifold ModularForm Topology

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### Elements of $\mathrm{GL}_2^+(\mathbb{R})$ -/

/-- The determinant of an element of $\mathrm{GL}_2^+(\mathbb{R})$ is positive. -/
lemma det_glPos_pos (g : GL(2, ℝ)⁺) : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) :=
  (Matrix.mem_glpos _).mp g.2

/-- For $\det g > 0$, Mathlib's $\sigma(g)$ (complex conjugation when $\det g < 0$) is the identity. -/
lemma σ_glPos (g : GL(2, ℝ)⁺) (x : ℂ) : σ (g : GL (Fin 2) ℝ) x = x := by
  simp only [σ, det_glPos_pos g, if_true]; rfl

/-- The Möbius action of $\mathrm{GL}_2^+(\mathbb{R})$ on $\mathbb{H}$ is the restriction of Mathlib's
$\mathrm{GL}_2(\mathbb{R})$-action. -/
lemma glPos_smul_eq (g : GL(2, ℝ)⁺) (z : ℍ) : g • z = (g : GL (Fin 2) ℝ) • z := rfl

/-- The cocycle relation $j(gh, z) = j(g, hz)\,j(h, z)$ for $j(g, z) = cz + d$, $\det h > 0$. -/
lemma denom_mul_glPos (g h : GL(2, ℝ)⁺) (z : ℍ) :
    denom ((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) z =
      denom (g : GL (Fin 2) ℝ) ↑(h • z) * denom (h : GL (Fin 2) ℝ) z := by
  rw [Subgroup.coe_mul, denom_cocycle_σ, σ_glPos]; rfl

lemma continuous_glPos_smul (g : GL(2, ℝ)⁺) : Continuous fun z : ℍ => g • z :=
  (mdifferentiable_smul (det_glPos_pos g)).continuous

variable {ι : Type*} [Fintype ι]

/-! ### The automorphy factor and the slash operator -/

/-- **The automorphy factor of vector weight $\vec k$**:
$$J_{\vec k}(\gamma, z) = \prod_{v\in\iota}\det(\gamma_v)^{k_v-1}\,(c_vz_v + d_v)^{-k_v},$$
for $\gamma = (\gamma_v) \in \prod_v\mathrm{GL}_2^+(\mathbb{R})$, $\gamma_v = \begin{pmatrix}a_v&b_v\\c_v&d_v\end{pmatrix}$, and
$z \in \mathbb{H}^\iota$ ($c_vz_v + d_v$ is Mathlib's `denom`). -/
noncomputable def jFactor (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (z : ι → ℍ) : ℂ :=
  ∏ v, ((((γ v : GL (Fin 2) ℝ).det.val ^ (k v - 1) : ℝ)) : ℂ) *
    denom (γ v : GL (Fin 2) ℝ) (z v) ^ (-k v)

/-- **The slash operator of vector weight $\vec k \in \mathbb{Z}^\iota$** on functions $f : \mathbb{H}^\iota \to \mathbb{C}$:
$(f\,|_{\vec k}\,\gamma)(z) = f(\gamma z)\,J_{\vec k}(\gamma, z)$, with $J$ the automorphy factor `jFactor` and
$(\gamma z)_v = \gamma_v z_v$ (Shimura 1978, (1.4) [unverified], with Mathlib's determinant normalization; see
the module docstring). -/
@[kb "shimura1978" "§1, (1.4) [unverified]"]
noncomputable def slashVec (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) : (ι → ℍ) → ℂ :=
  fun z => f (γ • z) * jFactor k γ z

lemma slashVec_apply (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) (z : ι → ℍ) :
    slashVec k γ f z = f (γ • z) * jFactor k γ z := rfl

lemma jFactor_ne_zero (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (z : ι → ℍ) : jFactor k γ z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero ?_ (zpow_ne_zero _ (denom_ne_zero _ _))
  exact ofReal_ne_zero.mpr (zpow_ne_zero _ (det_glPos_pos (γ v)).ne')

/-- **The cocycle relation** $J_{\vec k}(\gamma\delta, z) = J_{\vec k}(\gamma, \delta z)\,J_{\vec k}(\delta, z)$. -/
lemma jFactor_mul (k : ι → ℤ) (γ δ : ι → GL(2, ℝ)⁺) (z : ι → ℍ) :
    jFactor k (γ * δ) z = jFactor k γ (δ • z) * jFactor k δ z := by
  simp only [jFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hc : denom ((γ * δ) v : GL (Fin 2) ℝ) (z v) =
      denom (γ v : GL (Fin 2) ℝ) ((δ • z) v) * denom (δ v : GL (Fin 2) ℝ) (z v) :=
    denom_mul_glPos (γ v) (δ v) (z v)
  rw [hc, Pi.mul_apply, Subgroup.coe_mul, map_mul, Units.val_mul, mul_zpow, ofReal_mul, mul_zpow]
  ring

@[simp] lemma jFactor_one (k : ι → ℤ) (z : ι → ℍ) : jFactor k 1 z = 1 := by
  refine Finset.prod_eq_one fun v _ => ?_
  simp only [Pi.one_apply, OneMemClass.coe_one, map_one, Units.val_one, _root_.one_zpow]
  rw [denom_one, _root_.one_zpow]; simp

lemma slashVec_mul (k : ι → ℤ) (γ δ : ι → GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) :
    slashVec k (γ * δ) f = slashVec k δ (slashVec k γ f) := by
  funext z
  simp only [slashVec_apply, mul_smul, jFactor_mul]
  ring

@[simp] lemma slashVec_one (k : ι → ℤ) (f : (ι → ℍ) → ℂ) : slashVec k 1 f = f := by
  funext z; simp [slashVec_apply]

lemma slashVec_add (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (f g : (ι → ℍ) → ℂ) :
    slashVec k γ (f + g) = slashVec k γ f + slashVec k γ g := by
  funext z; simp [slashVec_apply, add_mul]

lemma slashVec_smul (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (c : ℂ) (f : (ι → ℍ) → ℂ) :
    slashVec k γ (c • f) = c • slashVec k γ f := by
  funext z; simp [slashVec_apply, mul_assoc]

@[simp] lemma slashVec_zero (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) :
    slashVec k γ (0 : (ι → ℍ) → ℂ) = 0 := by
  funext z; simp [slashVec_apply]

/-- **Products of forms: weights add.**
$(fg)\,|_{\vec k + \vec l}\,\gamma = \big(\prod_v\det\gamma_v\big)\,(f\,|_{\vec k}\,\gamma)(g\,|_{\vec l}\,\gamma)$
(cf. Mathlib's `ModularForm.mul_slash`). -/
lemma slashVec_mul_mul (k l : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) (f g : (ι → ℍ) → ℂ) :
    slashVec (k + l) γ (f * g) =
      (∏ v, (((γ v : GL (Fin 2) ℝ).det.val : ℝ) : ℂ)) • (slashVec k γ f * slashVec l γ g) := by
  funext z
  simp only [slashVec_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, jFactor]
  have h : ∀ v, ((((γ v : GL (Fin 2) ℝ).det.val ^ ((k + l) v - 1) : ℝ)) : ℂ) *
      denom (γ v : GL (Fin 2) ℝ) (z v) ^ (-(k + l) v) =
      (((γ v : GL (Fin 2) ℝ).det.val : ℝ) : ℂ) *
        (((((γ v : GL (Fin 2) ℝ).det.val ^ (k v - 1) : ℝ)) : ℂ) *
          denom (γ v : GL (Fin 2) ℝ) (z v) ^ (-k v)) *
        (((((γ v : GL (Fin 2) ℝ).det.val ^ (l v - 1) : ℝ)) : ℂ) *
          denom (γ v : GL (Fin 2) ℝ) (z v) ^ (-l v)) := by
    intro v
    have hd : ((γ v : GL (Fin 2) ℝ).det.val : ℝ) ≠ 0 := (det_glPos_pos (γ v)).ne'
    have hj : denom (γ v : GL (Fin 2) ℝ) (z v) ≠ 0 := denom_ne_zero _ _
    have e1 : ((k + l) v - 1) = 1 + (k v - 1) + (l v - 1) := by simp only [Pi.add_apply]; ring
    have e2 : -(k + l) v = -k v + -l v := by simp only [Pi.add_apply]; ring
    rw [e1, e2, zpow_add₀ hd, zpow_add₀ hd, zpow_one, zpow_add₀ hj]
    push_cast
    ring
  simp only [h, Finset.prod_mul_distrib]
  ring

/-! ### Parallel weight: the `SlashAction` instance -/

/-- **The parallel-weight slash action** $f\,|_k\,\gamma = f\,|_{(k,\dots,k)}\,\gamma$ of
$\prod_v\mathrm{GL}_2^+(\mathbb{R})$ on functions $\mathbb{H}^\iota \to \mathbb{C}$, as a Mathlib `SlashAction`
(notation `f ∣[k] γ`). -/
noncomputable instance instSlashAction :
    SlashAction ℤ (ι → GL(2, ℝ)⁺) ((ι → ℍ) → ℂ) where
  map k γ f := slashVec (fun _ => k) γ f
  zero_slash _ γ := slashVec_zero _ γ
  slash_one _ f := slashVec_one _ f
  slash_mul _ γ δ f := slashVec_mul _ γ δ f
  add_slash _ γ f g := slashVec_add _ γ f g

lemma slash_def (k : ℤ) (γ : ι → GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) :
    f ∣[k] γ = slashVec (fun _ => k) γ f := rfl

/-- $(f\,|_k\,\gamma)(z) = f(\gamma z)\prod_v\det(\gamma_v)^{k-1}(c_vz_v + d_v)^{-k}$. -/
lemma slash_apply (k : ℤ) (γ : ι → GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) (z : ι → ℍ) :
    (f ∣[k] γ) z = f (γ • z) * ∏ v, ((((γ v : GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ)) : ℂ) *
      denom (γ v : GL (Fin 2) ℝ) (z v) ^ (-k) := rfl

lemma smul_slash (k : ℤ) (γ : ι → GL(2, ℝ)⁺) (c : ℂ) (f : (ι → ℍ) → ℂ) :
    (c • f) ∣[k] γ = c • (f ∣[k] γ) :=
  slashVec_smul _ γ c f

/-- **Products, parallel weight**: $(fg)\,|_{k+l}\,\gamma = \big(\prod_v\det\gamma_v\big)\,(f\,|_k\,\gamma)(g\,|_l\,\gamma)$. -/
lemma mul_slash (k l : ℤ) (γ : ι → GL(2, ℝ)⁺) (f g : (ι → ℍ) → ℂ) :
    (f * g) ∣[k + l] γ =
      (∏ v, (((γ v : GL (Fin 2) ℝ).det.val : ℝ) : ℂ)) • (f ∣[k] γ * g ∣[l] γ) :=
  slashVec_mul_mul (fun _ => k) (fun _ => l) γ f g

/-- **Products, determinant one**: if $\det\gamma_v = 1$ for all $v$ then $(fg)\,|_{k+l}\,\gamma = (f\,|_k\,\gamma)(g\,|_l\,\gamma)$. -/
lemma mul_slash_of_det_one (k l : ℤ) (γ : ι → GL(2, ℝ)⁺)
    (hγ : ∀ v, ((γ v : GL (Fin 2) ℝ).det.val : ℝ) = 1) (f g : (ι → ℍ) → ℂ) :
    (f * g) ∣[k + l] γ = f ∣[k] γ * g ∣[l] γ := by
  rw [mul_slash]; simp [hγ]

/-! ### Holomorphy on $\mathbb{H}^\iota$ -/

open Classical in
/-- **Holomorphy on $\mathbb{H}^\iota$**: $f$ is continuous, and holomorphic in each variable $z_v$ when the other
variables are fixed: for every $z \in \mathbb{H}^\iota$ and $v \in \iota$, $w \mapsto f(z_{v \leftarrow w})$ is holomorphic
on $\mathbb{H}$ (`MDifferentiable` for Mathlib's complex-manifold structure on `ℍ`; $z_{v\leftarrow w}$ is
`Function.update z v w`).

By Osgood's lemma this is equivalent to $f$ being complex differentiable in all variables jointly (Hartogs'
theorem even removes the continuity hypothesis). Fields: the conjunction (continuity, separate holomorphy). -/
@[kb "freitag1990" "Ch. I, §1 (holomorphic functions of several variables) [unverified]"]
def IsHolomorphic (f : (ι → ℍ) → ℂ) : Prop :=
  Continuous f ∧ ∀ (z : ι → ℍ) (v : ι), MDiff (fun w : ℍ => f (Function.update z v w))

lemma isHolomorphic_zero : IsHolomorphic (0 : (ι → ℍ) → ℂ) :=
  ⟨continuous_const, fun _ _ => mdifferentiable_const⟩

lemma IsHolomorphic.add {f g : (ι → ℍ) → ℂ} (hf : IsHolomorphic f) (hg : IsHolomorphic g) :
    IsHolomorphic (f + g) :=
  ⟨hf.1.add hg.1, fun z v => (hf.2 z v).add (hg.2 z v)⟩

lemma IsHolomorphic.const_smul {f : (ι → ℍ) → ℂ} (c : ℂ) (hf : IsHolomorphic f) :
    IsHolomorphic (c • f) :=
  ⟨hf.1.const_smul c, fun z v => (hf.2 z v).const_smul c⟩

lemma IsHolomorphic.mul {f g : (ι → ℍ) → ℂ} (hf : IsHolomorphic f) (hg : IsHolomorphic g) :
    IsHolomorphic (f * g) :=
  ⟨hf.1.mul hg.1, fun z v => (hf.2 z v).mul (hg.2 z v)⟩

/-- Componentwise action commutes with updating one coordinate. -/
lemma smul_update [DecidableEq ι] (γ : ι → GL(2, ℝ)⁺) (z : ι → ℍ) (v : ι) (w : ℍ) :
    γ • Function.update z v w = Function.update (γ • z) v (γ v • w) := by
  funext u
  by_cases h : u = v
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma continuous_pi_smul (γ : ι → GL(2, ℝ)⁺) : Continuous fun z : ι → ℍ => γ • z :=
  continuous_pi fun v => (continuous_glPos_smul (γ v)).comp (continuous_apply v)

lemma continuous_jFactor (k : ι → ℤ) (γ : ι → GL(2, ℝ)⁺) : Continuous (jFactor k γ) := by
  refine continuous_finset_prod _ fun v _ => continuous_const.mul ?_
  exact (mdifferentiable_denom_zpow (γ v : GL (Fin 2) ℝ) (-k v)).continuous.comp (continuous_apply v)

/-- **The slash of a holomorphic function is holomorphic** (any vector weight). -/
lemma IsHolomorphic.slashVec {f : (ι → ℍ) → ℂ} (hf : IsHolomorphic f) (k : ι → ℤ)
    (γ : ι → GL(2, ℝ)⁺) : IsHolomorphic (slashVec k γ f) := by
  classical
  refine ⟨(hf.1.comp (continuous_pi_smul γ)).mul (continuous_jFactor k γ), fun z v => ?_⟩
  simp only [slashVec_apply, smul_update]
  refine MDifferentiable.mul ?_ ?_
  · exact (hf.2 (γ • z) v).comp (mdifferentiable_smul (det_glPos_pos (γ v)))
  · have : (fun w : ℍ => jFactor k γ (Function.update z v w)) =
        ∏ u ∈ Finset.univ, fun w : ℍ => ((((γ u : GL (Fin 2) ℝ).det.val ^ (k u - 1) : ℝ)) : ℂ) *
          denom (γ u : GL (Fin 2) ℝ) (Function.update z v w u) ^ (-k u) := by
      funext w; simp [jFactor, Finset.prod_apply]
    rw [this]
    refine MDifferentiable.prod fun u _ => mdifferentiable_const.mul ?_
    by_cases h : u = v
    · subst h; simpa using mdifferentiable_denom_zpow (γ u : GL (Fin 2) ℝ) (-k u)
    · simpa [Function.update_of_ne h] using mdifferentiable_const

lemma IsHolomorphic.slash {f : (ι → ℍ) → ℂ} (hf : IsHolomorphic f) (k : ℤ)
    (γ : ι → GL(2, ℝ)⁺) : IsHolomorphic (f ∣[k] γ) :=
  hf.slashVec _ γ

/-! ### Behaviour at $\infty$ -/

/-- **The filter at $i\infty$ on $\mathbb{H}^\iota$**: $\bigwedge_{v}\operatorname{comap}(z \mapsto \operatorname{Im} z_v)\,\mathrm{atTop}$; its
sets contain $\{z : \operatorname{Im} z_v \ge A\ \forall v\}$ for some $A$. -/
def atImInftyPi : Filter (ι → ℍ) := ⨅ v, comap (fun z : ι → ℍ => (z v).im) atTop

/-- **$f$ is bounded at $i\infty$**: bounded on $\{z \in \mathbb{H}^\iota : \operatorname{Im} z_v \ge A \text{ for all } v\}$ for
some $A$ (`Filter.BoundedAtFilter` along `atImInftyPi`). -/
@[kb "garrett1990" "Ch. 1 (holomorphy at the cusps) [unverified]"]
def IsBoundedAtImInftyPi (f : (ι → ℍ) → ℂ) : Prop := atImInftyPi.BoundedAtFilter f

/-- **$f$ vanishes at $i\infty$**: $f(z) \to 0$ as $\min_v\operatorname{Im} z_v \to \infty$ (along `atImInftyPi`). -/
def IsZeroAtImInftyPi (f : (ι → ℍ) → ℂ) : Prop := atImInftyPi.ZeroAtFilter f

lemma isBoundedAtImInftyPi_zero : IsBoundedAtImInftyPi (0 : (ι → ℍ) → ℂ) :=
  Filter.const_boundedAtFilter _ 0

lemma IsBoundedAtImInftyPi.add {f g : (ι → ℍ) → ℂ} (hf : IsBoundedAtImInftyPi f)
    (hg : IsBoundedAtImInftyPi g) : IsBoundedAtImInftyPi (f + g) := Filter.BoundedAtFilter.add hf hg

lemma IsBoundedAtImInftyPi.const_smul {f : (ι → ℍ) → ℂ} (c : ℂ) (hf : IsBoundedAtImInftyPi f) :
    IsBoundedAtImInftyPi (c • f) := Filter.BoundedAtFilter.smul c hf

lemma isZeroAtImInftyPi_zero : IsZeroAtImInftyPi (0 : (ι → ℍ) → ℂ) :=
  Filter.zero_zeroAtFilter _

lemma IsZeroAtImInftyPi.add {f g : (ι → ℍ) → ℂ} (hf : IsZeroAtImInftyPi f)
    (hg : IsZeroAtImInftyPi g) : IsZeroAtImInftyPi (f + g) := Filter.ZeroAtFilter.add hf hg

lemma IsZeroAtImInftyPi.const_smul {f : (ι → ℍ) → ℂ} (c : ℂ) (hf : IsZeroAtImInftyPi f) :
    IsZeroAtImInftyPi (c • f) := Filter.ZeroAtFilter.smul c hf

lemma IsZeroAtImInftyPi.isBoundedAtImInftyPi {f : (ι → ℍ) → ℂ} (hf : IsZeroAtImInftyPi f) :
    IsBoundedAtImInftyPi f := Filter.ZeroAtFilter.boundedAtFilter hf

/-! ### One variable: agreement with Mathlib -/

section Unique

variable [Unique ι]

/-- The identification $\mathbb{H} \to \mathbb{H}^\iota$, $z \mapsto (z)$, for a one-point index set. -/
def constH (z : ℍ) : ι → ℍ := fun _ => z

omit [Fintype ι] in
lemma constH_eval (z : ι → ℍ) : constH (z default) = z := by
  funext u; simp [constH, Unique.eq_default u]

omit [Fintype ι] in
lemma funUnique_symm_eq : ⇑(Equiv.funUnique ι ℍ).symm = constH := by
  funext z u; simp [constH]

/-- **$d = 1$: the slash operator is Mathlib's.** For $|\iota| = 1$ and $\gamma \in \mathrm{GL}_2^+(\mathbb{R})$,
$(f\,|_k\,\gamma)((z)) = (f|_{\mathbb{H}}\,|_k\,\gamma)(z)$, where $f|_{\mathbb{H}} = f \circ (z \mapsto (z))$ and the right side is
`ModularForm.slash` (Mathlib's operator $\sigma_g(f(gz))\,|\det g|^{k-1}(cz+d)^{-k}$). -/
lemma slash_unique (k : ℤ) (γ : GL(2, ℝ)⁺) (f : (ι → ℍ) → ℂ) (z : ℍ) :
    (f ∣[k] (fun _ : ι => γ)) (constH z) =
      ((f ∘ constH) ∣[k] (γ : GL (Fin 2) ℝ)) z := by
  rw [slash_apply, ModularForm.slash_apply, σ_glPos, Fintype.prod_unique,
    abs_of_pos (det_glPos_pos γ)]
  have : ((fun _ : ι => γ) • (constH z : ι → ℍ)) = constH ((γ : GL (Fin 2) ℝ) • z) := by
    funext u; rfl
  simp only [this, Function.comp_apply, ofReal_zpow]
  simp only [constH]
  ring

omit [Fintype ι] in
lemma atImInftyPi_unique :
    (atImInftyPi : Filter (ι → ℍ)) = Filter.map (Equiv.funUnique ι ℍ).symm atImInfty := by
  rw [atImInftyPi, iInf_unique, Filter.map_equiv_symm, atImInfty, Filter.comap_comap]
  rfl

omit [Fintype ι] in
/-- $d = 1$: bounded at $i\infty$ on $\mathbb{H}^\iota$ iff Mathlib's `IsBoundedAtImInfty`. -/
lemma isBoundedAtImInftyPi_unique_iff (f : (ι → ℍ) → ℂ) :
    IsBoundedAtImInftyPi f ↔ IsBoundedAtImInfty (f ∘ constH) := by
  rw [IsBoundedAtImInftyPi, IsBoundedAtImInfty, atImInftyPi_unique, Filter.BoundedAtFilter,
    Filter.BoundedAtFilter, Asymptotics.isBigO_map, funUnique_symm_eq]
  rfl

omit [Fintype ι] in
/-- $d = 1$: zero at $i\infty$ on $\mathbb{H}^\iota$ iff Mathlib's `IsZeroAtImInfty`. -/
lemma isZeroAtImInftyPi_unique_iff (f : (ι → ℍ) → ℂ) :
    IsZeroAtImInftyPi f ↔ IsZeroAtImInfty (f ∘ constH) := by
  rw [IsZeroAtImInftyPi, IsZeroAtImInfty, atImInftyPi_unique, Filter.ZeroAtFilter,
    Filter.ZeroAtFilter, Filter.tendsto_map'_iff, funUnique_symm_eq]

omit [Fintype ι] in
/-- $d = 1$: holomorphy on $\mathbb{H}^\iota$ is holomorphy on $\mathbb{H}$ (`MDifferentiable`). -/
lemma isHolomorphic_unique_iff (f : (ι → ℍ) → ℂ) :
    IsHolomorphic f ↔ MDiff (f ∘ constH) := by
  constructor
  · rintro ⟨-, h⟩
    have := h (constH (default : ℍ)) default
    convert this using 1
    funext w
    simp only [Function.comp_apply]
    congr 1
    funext u
    obtain rfl := Unique.eq_default u
    simp [Function.update, constH]
  · intro h
    refine ⟨?_, fun z v => ?_⟩
    · have hc : Continuous (f ∘ constH) := h.continuous
      have : f = (f ∘ constH) ∘ (fun z : ι → ℍ => z default) := by
        funext z; simp [constH_eval]
      rw [this]
      exact hc.comp (continuous_apply default)
    · convert h using 1
      funext w
      simp only [Function.comp_apply]
      congr 1
      funext u
      obtain rfl := Unique.eq_default u
      obtain rfl := Unique.eq_default v
      simp [Function.update, constH]

end Unique

end QuadFormsKB.HilbertModular
