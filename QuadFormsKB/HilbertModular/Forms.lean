/-
# Hilbert modular forms III: the spaces $M_k(\Gamma)$, $S_k(\Gamma)$, $M_k(\Gamma_0(\mathfrak N), \chi)$

Let $K$ be a field with real embeddings $\varphi = (\varphi_v)_{v\in\iota}$ (for a totally real number field $F$:
$\iota$ = the infinite places, $\varphi_v$ = `realEmb F v`), and $\Gamma \le \mathrm{SL}_2(K)$ a subgroup. For $k \in \mathbb{Z}$
(parallel weight) the **space of Hilbert modular forms** `modularFormSpace φ Γ k` $= M_k(\Gamma)$ is the $\mathbb{C}$-subspace of
functions $f : \mathbb{H}^\iota \to \mathbb{C}$ such that

1. $f\,|_k\,\gamma = f$ for all $\gamma \in \Gamma$ (via `slHom φ`, i.e. $\gamma$ acting through $(\varphi_v(\gamma))_v$);
2. $f$ is holomorphic on $\mathbb{H}^\iota$ (`IsHolomorphic`: continuous and holomorphic in each variable);
3. $f$ is holomorphic at every cusp: $f\,|_k\,\gamma$ is bounded on $\{\operatorname{Im} z_v \ge A\ \forall v\}$ for some $A$, for
   **every** $\gamma \in \mathrm{SL}_2(K)$ (`IsBoundedAtImInftyPi`).

Cusp forms `cuspFormSpace φ Γ k` $= S_k(\Gamma)$ replace 3 by: $f\,|_k\,\gamma \to 0$ at $i\infty$ for every $\gamma \in \mathrm{SL}_2(K)$.

Condition 3 runs over all of $\mathrm{SL}_2(K)$, so the cusps are $\mathbb{P}^1(K) = \mathrm{SL}_2(K)\infty$ (for $\mathcal{O}_F$ of class
number $> 1$ these are *not* all $\mathrm{SL}_2(\mathcal{O}_F)$-equivalent to $\infty$). For $d = [F:\mathbb{Q}] \ge 2$ and $\Gamma$
commensurable with $\mathrm{SL}_2(\mathcal{O}_F)$, condition 3 follows from 1 and 2 (**Koecher principle**); it is part
of the definition so that the definition is uniform in $d$ and agrees with Mathlib's for $d = 1$.

**Arithmetic subgroups**: `IsHilbertArithmetic Γ` says $\Gamma$ is commensurable with $\mathrm{SL}_2(\mathcal{O}_F)$ (`SL2O`).
The definitions above make sense for any $\Gamma$; theorems that need it (Koecher, finite dimension) assume it.

**Nebentypus.** For an integral ideal $\mathfrak N$ and a character $\chi : (\mathcal{O}_F/\mathfrak N) \to \mathbb{C}$ (`MulChar`),
`modularFormChar 𝔑 χ k` $= M_k(\Gamma_0(\mathfrak N), \chi)$: forms on $\Gamma_1(\mathfrak N)$ with
$f\,|_k\,\gamma = \chi(d)\,f$ for every $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ ($\gamma \in \mathrm{SL}_2(\mathcal{O}_F)$,
$c \in \mathfrak N$). This is the packaging of `QuadFormsKB.Siegel.IsCuspFormWithChar` and `thetaMFGamma1` over $\mathbb{Q}$.

**$d = 1$.** `mem_modularFormSpace_rat_iff`: for $K = \mathbb{Q}$, $|\iota| = 1$ and $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ of finite index,
$f \in M_k(\Gamma)$ (ours, $\Gamma$ viewed in $\mathrm{SL}_2(\mathbb{Q})$) iff $f$ (as a function on $\mathbb{H}$) is a Mathlib
`ModularForm Γ k`; `mem_cuspFormSpace_rat_iff` is the same for cusp forms. Since $F = \mathbb{Q}$ has one infinite place
(`InfinitePlace ℚ` is `Unique`), this covers our spaces over $F = \mathbb{Q}$ (`realEmb ℚ`).
-/
import QuadFormsKB.HilbertModular.Congruence

open Matrix NumberField UpperHalfPlane ModularForm Filter OnePoint
open scoped MatrixGroups Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

section General

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] (φ : ι → K →+* ℝ)

/-- **Hilbert modular forms of parallel weight $k$ for $\Gamma \le \mathrm{SL}_2(K)$**, $M_k(\Gamma)$: the functions
$f : \mathbb{H}^\iota \to \mathbb{C}$ with (i) $f\,|_k\,\gamma = f$ for $\gamma \in \Gamma$, (ii) `IsHolomorphic f`, (iii)
$f\,|_k\,\gamma$ bounded at $i\infty$ for every $\gamma \in \mathrm{SL}_2(K)$; $\gamma$ acts through the real embeddings $\varphi$
(`slHom φ`). A $\mathbb{C}$-subspace.

Parameters: `φ` (the real embeddings, indexed by `ι`), `Γ` (the group), `k` (the weight). -/
@[kb "garrett1990" "Ch. 1, definition of holomorphic Hilbert modular forms [unverified]"]
def modularFormSpace (Γ : Subgroup SL(2, K)) (k : ℤ) : Submodule ℂ ((ι → ℍ) → ℂ) where
  carrier := {f | (∀ γ ∈ Γ, f ∣[k] slHom φ γ = f) ∧ IsHolomorphic f ∧
    ∀ γ : SL(2, K), IsBoundedAtImInftyPi (f ∣[k] slHom φ γ)}
  zero_mem' := ⟨fun _ _ => SlashAction.zero_slash _ _, isHolomorphic_zero,
    fun _ => by rw [SlashAction.zero_slash]; exact isBoundedAtImInftyPi_zero⟩
  add_mem' {f g} hf hg := ⟨fun γ hγ => by rw [SlashAction.add_slash, hf.1 γ hγ, hg.1 γ hγ],
    hf.2.1.add hg.2.1, fun γ => by rw [SlashAction.add_slash]; exact (hf.2.2 γ).add (hg.2.2 γ)⟩
  smul_mem' c f hf := ⟨fun γ hγ => by rw [smul_slash, hf.1 γ hγ], hf.2.1.const_smul c,
    fun γ => by rw [smul_slash]; exact (hf.2.2 γ).const_smul c⟩

/-- **Hilbert cusp forms of parallel weight $k$ for $\Gamma$**, $S_k(\Gamma)$: as `modularFormSpace`, with (iii) replaced by
$f\,|_k\,\gamma \to 0$ at $i\infty$ for every $\gamma \in \mathrm{SL}_2(K)$. -/
@[kb "garrett1990" "Ch. 1, definition of cusp forms [unverified]"]
def cuspFormSpace (Γ : Subgroup SL(2, K)) (k : ℤ) : Submodule ℂ ((ι → ℍ) → ℂ) where
  carrier := {f | (∀ γ ∈ Γ, f ∣[k] slHom φ γ = f) ∧ IsHolomorphic f ∧
    ∀ γ : SL(2, K), IsZeroAtImInftyPi (f ∣[k] slHom φ γ)}
  zero_mem' := ⟨fun _ _ => SlashAction.zero_slash _ _, isHolomorphic_zero,
    fun _ => by rw [SlashAction.zero_slash]; exact isZeroAtImInftyPi_zero⟩
  add_mem' {f g} hf hg := ⟨fun γ hγ => by rw [SlashAction.add_slash, hf.1 γ hγ, hg.1 γ hγ],
    hf.2.1.add hg.2.1, fun γ => by rw [SlashAction.add_slash]; exact (hf.2.2 γ).add (hg.2.2 γ)⟩
  smul_mem' c f hf := ⟨fun γ hγ => by rw [smul_slash, hf.1 γ hγ], hf.2.1.const_smul c,
    fun γ => by rw [smul_slash]; exact (hf.2.2 γ).const_smul c⟩

lemma cuspFormSpace_le (Γ : Subgroup SL(2, K)) (k : ℤ) :
    cuspFormSpace φ Γ k ≤ modularFormSpace φ Γ k :=
  fun _ hf => ⟨hf.1, hf.2.1, fun γ => (hf.2.2 γ).isBoundedAtImInftyPi⟩

/-- Smaller groups have more forms: $\Gamma' \le \Gamma \Rightarrow M_k(\Gamma) \le M_k(\Gamma')$. -/
lemma modularFormSpace_anti {Γ Γ' : Subgroup SL(2, K)} (h : Γ' ≤ Γ) (k : ℤ) :
    modularFormSpace φ Γ k ≤ modularFormSpace φ Γ' k :=
  fun _ hf => ⟨fun γ hγ => hf.1 γ (h hγ), hf.2.1, hf.2.2⟩

/-- **Products**: $M_k(\Gamma)\cdot M_l(\Gamma) \subseteq M_{k+l}(\Gamma)$ (determinants are $1$ on $\mathrm{SL}_2$). The cusp
condition is multiplicative because $(fg)\,|_{k+l}\,\gamma = (f\,|_k\,\gamma)(g\,|_l\,\gamma)$. -/
lemma mul_mem_modularFormSpace {Γ : Subgroup SL(2, K)} {k l : ℤ} {f g : (ι → ℍ) → ℂ}
    (hf : f ∈ modularFormSpace φ Γ k) (hg : g ∈ modularFormSpace φ Γ l) :
    f * g ∈ modularFormSpace φ Γ (k + l) := by
  have hm : ∀ γ : SL(2, K), (f * g) ∣[k + l] slHom φ γ = f ∣[k] slHom φ γ * g ∣[l] slHom φ γ :=
    fun γ => mul_slash_of_det_one k l _ (slHom_det φ γ) f g
  refine ⟨fun γ hγ => by rw [hm, hf.1 γ hγ, hg.1 γ hγ], hf.2.1.mul hg.2.1, fun γ => ?_⟩
  rw [hm]
  exact Filter.BoundedAtFilter.mul (hf.2.2 γ) (hg.2.2 γ)

end General

/-! ### Over a totally real field -/

section TotallyReal

variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

/-- **$M_k(\Gamma)$ over a totally real field $F$**: `modularFormSpace` with $\iota$ = the $d$ infinite (real) places of
$F$ and the real embeddings `realEmb F`. -/
noncomputable abbrev HMF (Γ : Subgroup SL(2, F)) (k : ℤ) : Submodule ℂ ((InfinitePlace F → ℍ) → ℂ) :=
  modularFormSpace (realEmb F) Γ k

/-- **$S_k(\Gamma)$ over a totally real field $F$.** -/
noncomputable abbrev HCF (Γ : Subgroup SL(2, F)) (k : ℤ) : Submodule ℂ ((InfinitePlace F → ℍ) → ℂ) :=
  cuspFormSpace (realEmb F) Γ k

variable {F}

/-- **$\Gamma$ is commensurable with $\mathrm{SL}_2(\mathcal{O}_F)$** (Mathlib's `Subgroup.Commensurable`: both
$[\Gamma : \Gamma \cap \mathrm{SL}_2(\mathcal{O}_F)]$ and $[\mathrm{SL}_2(\mathcal{O}_F) : \Gamma \cap \mathrm{SL}_2(\mathcal{O}_F)]$ are finite). -/
def IsHilbertArithmetic (Γ : Subgroup SL(2, F)) : Prop := Γ.Commensurable SL2O

lemma isHilbertArithmetic_SL2O : IsHilbertArithmetic (SL2O : Subgroup SL(2, F)) :=
  Subgroup.Commensurable.refl _

/-- **$M_k(\Gamma_0(\mathfrak N), \chi)$**: forms $f \in M_k(\Gamma_1(\mathfrak N))$ with
$f\,|_k\,\gamma = \chi(d \bmod \mathfrak N)\,f$ for every $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$
($\gamma \in \mathrm{SL}_2(\mathcal{O}_F)$, $c \in \mathfrak N$; $d = \gamma_{11}$ 0-based).

Parameters: `𝔑` (the level, an ideal of $\mathcal{O}_F$), `χ` (a multiplicative character of $\mathcal{O}_F/\mathfrak N$ with values in
$\mathbb{C}$), `k` (parallel weight). -/
@[kb "shimura1978" "§2, M_k(Γ₀(𝔑), ψ) [unverified]"]
def modularFormChar (𝔑 : Ideal (𝓞 F)) (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) (k : ℤ) :
    Submodule ℂ ((InfinitePlace F → ℍ) → ℂ) where
  carrier := {f | f ∈ HMF F (Gamma1 𝔑) k ∧ ∀ γ ∈ Gamma0R 𝔑,
    f ∣[k] slHom (realEmb F) (toF F γ) = χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • f}
  zero_mem' := ⟨(HMF F (Gamma1 𝔑) k).zero_mem, fun _ _ => by simp⟩
  add_mem' {f g} hf hg := ⟨(HMF F (Gamma1 𝔑) k).add_mem hf.1 hg.1, fun γ hγ => by
    rw [SlashAction.add_slash, hf.2 γ hγ, hg.2 γ hγ, smul_add]⟩
  smul_mem' c f hf := ⟨(HMF F (Gamma1 𝔑) k).smul_mem c hf.1, fun γ hγ => by
    rw [smul_slash, hf.2 γ hγ, smul_comm]⟩

/-- **$S_k(\Gamma_0(\mathfrak N), \chi)$**: cusp forms on $\Gamma_1(\mathfrak N)$ with the $\chi$-twisted law under $\Gamma_0(\mathfrak N)$. -/
noncomputable def cuspFormChar (𝔑 : Ideal (𝓞 F)) (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) (k : ℤ) :
    Submodule ℂ ((InfinitePlace F → ℍ) → ℂ) :=
  HCF F (Gamma1 𝔑) k ⊓ modularFormChar 𝔑 χ k

/-- For the trivial character, $M_k(\Gamma_0(\mathfrak N), 1) \subseteq M_k(\Gamma_0(\mathfrak N))$. -/
lemma modularFormChar_one_le (𝔑 : Ideal (𝓞 F)) (k : ℤ) :
    modularFormChar 𝔑 1 k ≤ HMF F (Gamma0 𝔑) k := by
  intro f hf
  refine ⟨?_, hf.1.2.1, hf.1.2.2⟩
  rintro _ ⟨γ, hγ, rfl⟩
  rw [hf.2 γ hγ]
  have hu : IsUnit (Ideal.Quotient.mk 𝔑 ((γ : SL(2, 𝓞 F)) 1 1)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔑 ((γ : SL(2, 𝓞 F)) 0 0)) ?_
    have hdet := γ.2
    rw [det_fin_two] at hdet
    have hc : Ideal.Quotient.mk 𝔑 ((γ : SL(2, 𝓞 F)) 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hγ
    have := congrArg (Ideal.Quotient.mk 𝔑) hdet
    simp only [map_sub, map_mul, hc, mul_zero, sub_zero, map_one] at this
    rw [mul_comm]; exact this
  rw [MulChar.one_apply hu, one_smul]

end TotallyReal

/-! ### $d = 1$: agreement with Mathlib's `ModularForm` -/

section Rat

variable {ι : Type*} [Fintype ι] [Unique ι] (φ : ι → ℚ →+* ℝ)

/-- $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Q})$. -/
noncomputable def ratSL : SL(2, ℤ) →* SL(2, ℚ) := SpecialLinearGroup.map (Int.castRingHom ℚ)

omit [Fintype ι] [Unique ι] in
lemma slHom_rat (γ : SL(2, ℚ)) (v : ι) :
    (slHom φ γ v : GL (Fin 2) ℝ) = SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  simp [eq_ratCast]

omit [Fintype ι] [Unique ι] in
lemma mapGL_ratSL (γ : SL(2, ℤ)) :
    SpecialLinearGroup.mapGL ℝ (ratSL γ) = SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  simp [ratSL]

/-- **$d = 1$: the slash by $\gamma \in \mathrm{SL}_2(\mathbb{Q})$ is Mathlib's slash** by its image in $\mathrm{GL}_2(\mathbb{R})$. -/
lemma slash_rat (k : ℤ) (γ : SL(2, ℚ)) (f : (ι → ℍ) → ℂ) :
    (f ∣[k] slHom φ γ) ∘ constH = (f ∘ constH) ∣[k] SpecialLinearGroup.mapGL ℝ γ := by
  funext z
  have h : slHom φ γ = fun _ => slHom φ γ default := funext fun v => by rw [Unique.eq_default v]
  rw [Function.comp_apply, h, slash_unique, slHom_rat]

omit [Fintype ι] in
lemma eq_of_comp_constH {f g : (ι → ℍ) → ℂ} (h : f ∘ constH = g ∘ constH) : f = g := by
  funext z
  rw [← constH_eval z]
  exact congrFun h (z default)

/-- Every $\gamma \in \mathrm{SL}_2(\mathbb{Q})$ sends $\infty$ to a cusp of $\mathrm{SL}_2(\mathbb{Z})$. -/
lemma isCusp_mapGL_rat (γ : SL(2, ℚ)) :
    IsCusp (SpecialLinearGroup.mapGL ℝ γ • (∞ : OnePoint ℝ)) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff, OnePoint.smul_infty_eq_ite]
  by_cases h : γ 1 0 = 0
  · refine ⟨∞, ?_⟩
    simp [h]
  · refine ⟨((γ 0 0 / γ 1 0 : ℚ) : OnePoint ℚ), ?_⟩
    simp [h]

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)

/-- **$d = 1$: our $M_k(\Gamma)$ is Mathlib's** `ModularForm Γ k`, for $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ of finite index (viewed in
$\mathrm{SL}_2(\mathbb{Q})$ via `ratSL`): $f \in M_k(\Gamma)$ iff $f \circ (z \mapsto (z))$ is (the function of) a Mathlib modular form. -/
theorem mem_modularFormSpace_rat_iff (f : (ι → ℍ) → ℂ) :
    f ∈ modularFormSpace φ (Γ.map ratSL) k ↔ ∃ g : ModularForm Γ k, ⇑g = f ∘ constH := by
  constructor
  · intro hf
    refine ⟨{ toFun := f ∘ constH
              slash_action_eq' := ?_
              holo' := (isHolomorphic_unique_iff f).mp hf.2.1
              bdd_at_cusps' := ?_ }, rfl⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      rw [← mapGL_ratSL, ← slash_rat, hf.1 _ ⟨γ, hγ, rfl⟩]
    · intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      obtain ⟨g, rfl⟩ := isCusp_SL2Z_iff'.mp hc
      rw [OnePoint.isBoundedAt_iff rfl, ← mapGL_ratSL, ← slash_rat]
      exact (isBoundedAtImInftyPi_unique_iff _).mp (hf.2.2 (ratSL g))
  · rintro ⟨g, hg⟩
    refine ⟨?_, (isHolomorphic_unique_iff f).mpr (hg ▸ g.holo'), fun γ => ?_⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      apply eq_of_comp_constH
      rw [slash_rat, mapGL_ratSL, ← hg]
      exact SlashInvariantForm.slash_action_eqn g _ ⟨γ, hγ, rfl⟩
    · rw [isBoundedAtImInftyPi_unique_iff, slash_rat, ← hg]
      have hc : IsCusp (SpecialLinearGroup.mapGL ℝ γ • (∞ : OnePoint ℝ)) (Γ : Subgroup _) :=
        (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (isCusp_mapGL_rat γ)
      exact (OnePoint.isBoundedAt_iff rfl).mp (g.bdd_at_cusps' hc)

/-- **$d = 1$: our $S_k(\Gamma)$ is Mathlib's** `CuspForm Γ k` (same hypotheses as `mem_modularFormSpace_rat_iff`). -/
theorem mem_cuspFormSpace_rat_iff (f : (ι → ℍ) → ℂ) :
    f ∈ cuspFormSpace φ (Γ.map ratSL) k ↔ ∃ g : CuspForm Γ k, ⇑g = f ∘ constH := by
  constructor
  · intro hf
    refine ⟨{ toFun := f ∘ constH
              slash_action_eq' := ?_
              holo' := (isHolomorphic_unique_iff f).mp hf.2.1
              zero_at_cusps' := ?_ }, rfl⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      rw [← mapGL_ratSL, ← slash_rat, hf.1 _ ⟨γ, hγ, rfl⟩]
    · intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      obtain ⟨g, rfl⟩ := isCusp_SL2Z_iff'.mp hc
      rw [OnePoint.isZeroAt_iff rfl, ← mapGL_ratSL, ← slash_rat]
      exact (isZeroAtImInftyPi_unique_iff _).mp (hf.2.2 (ratSL g))
  · rintro ⟨g, hg⟩
    refine ⟨?_, (isHolomorphic_unique_iff f).mpr (hg ▸ g.holo'), fun γ => ?_⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      apply eq_of_comp_constH
      rw [slash_rat, mapGL_ratSL, ← hg]
      exact SlashInvariantForm.slash_action_eqn g _ ⟨γ, hγ, rfl⟩
    · rw [isZeroAtImInftyPi_unique_iff, slash_rat, ← hg]
      have hc : IsCusp (SpecialLinearGroup.mapGL ℝ γ • (∞ : OnePoint ℝ)) (Γ : Subgroup _) :=
        (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (isCusp_mapGL_rat γ)
      exact (OnePoint.isZeroAt_iff rfl).mp (g.zero_at_cusps' hc)

/-- **$F = \mathbb{Q}$**: `HMF ℚ` is Mathlib's space of modular forms (the one infinite place of $\mathbb{Q}$). -/
theorem mem_HMF_rat_iff (f : (InfinitePlace ℚ → ℍ) → ℂ) :
    f ∈ HMF ℚ (Γ.map ratSL) k ↔ ∃ g : ModularForm Γ k, ⇑g = f ∘ constH :=
  mem_modularFormSpace_rat_iff (realEmb ℚ) Γ k f

end Rat

end QuadFormsKB.HilbertModular
