/-
# Shimura 2004, §4: parabolic subgroups of $O^\varphi$, $SO^\varphi$ and the Clifford groups

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §4.1–Proposition 4.3 (printed
pp. 28–30). Page numbers are printed pages.

**Setting and dictionary.** As in `Wave2/CliffordLemmas.lean`. Shimura lets $O^\varphi$ act on the right
($J\alpha$); here linear maps act on the left, so $J\alpha$ is `J.map α`, and $\tau(a)$ is `tau a`
($x \mapsto a^{-1}xa$). The definitions are made for every subspace $J$; Shimura uses them for totally
$\varphi$-isotropic $J$ (in (4.8) for $J = I_m = \sum_{i\le m}Fe_i$), which is the case of interest.

**Defines**
* (4.2) $P^J = \{\alpha \in O^\varphi \mid J\alpha \subseteq J\}$ (`parabolicO`), with "the condition $J\alpha
  \subseteq J$ can be replaced by $J\alpha = J$" (`mem_parabolicO_iff_le`);
* (4.7) $\lambda^J : P^J \to GL(J)$, restriction to $J$ (`lambdaJ`), a homomorphism;
* (4.8a,b) $P^{SO}_J = \{\gamma \in SO^\varphi \mid J\gamma = J\}$ (`parabolicSO`), $P'_J = \{a \in G'(V) \mid
  J\tau(a) = J\}$ (`parabolicG'`), $P^+_J = G^+(V) \cap P'_J$ (`parabolicGPlus`), $P^1_J = G^1(V) \cap P'_J$
  (`parabolicG1`).

**Proves** (all unconditional; standard axioms only)
* $P^{J\beta} = \beta^{-1}P^J\beta$ (`mem_parabolicO_map_iff`, §4.1);
* $\tau(P^+_J) = P^{SO}_J$ (`tau_mem_parabolicSO`, `exists_tau_eq_of_mem_parabolicSO`, §4.2);
* (4.9a) for $J = Fe$, $P'_J = \{a \in G'(V) \mid a^{-1}ea \in Fe\}$ (`mem_parabolicG'_span_iff`);
* Proposition 4.3, the assertion $G^+(V) = P_1^+G^1(V)$ (`prop_4_3_M0_eq_mul`), for a weak Witt decomposition
  $V = U + Fe + Ff$, through the elements $e(r,1)$ of Lemma 3.10.
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.CliffordLemmas
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### (4.2): the parabolic subgroup $P^J$ of $O^\varphi$ -/

/-- For a linear automorphism $\alpha$ of the finite-dimensional $V$, $J\alpha \subseteq J$ implies $J\alpha = J$. -/
theorem map_eq_of_map_le {J : Submodule F V} {α : V ≃ₗ[F] V} (h : J.map (α : V →ₗ[F] V) ≤ J) :
    J.map (α : V →ₗ[F] V) = J :=
  Submodule.eq_of_le_of_finrank_eq h (LinearEquiv.finrank_map_eq α J)

theorem map_symm_eq {J : Submodule F V} {α : V ≃ₗ[F] V} (h : J.map (α : V →ₗ[F] V) = J) :
    J.map (α.symm : V →ₗ[F] V) = J := by
  conv_lhs => rw [← h]
  rw [← Submodule.map_comp]
  simp

theorem map_map_symm (α : V ≃ₗ[F] V) (X : Submodule F V) :
    (X.map (α.symm : V →ₗ[F] V)).map (α : V →ₗ[F] V) = X := by
  rw [← Submodule.map_comp]; simp

theorem map_symm_map (α : V ≃ₗ[F] V) (X : Submodule F V) :
    (X.map (α : V →ₗ[F] V)).map (α.symm : V →ₗ[F] V) = X := by
  rw [← Submodule.map_comp]; simp

variable (Q) in
/-- **The parabolic subgroup** $P^J = \{\alpha \in O^\varphi \mid J\alpha \subseteq J\}$ of $O^\varphi$ (Shimura
(4.2), p. 28), for a (totally isotropic) subspace $J$ of $V$. Defined with $J\alpha = J$, which is equivalent
(`mem_parabolicO_iff_le`). -/
@[kb "shimura2004" "(4.2), p. 28 (the parabolic subgroup P^J = {α ∈ O^φ | Jα ⊂ J})"]
def parabolicO (J : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {α | α ∈ orth Q ∧ J.map (α : V →ₗ[F] V) = J}
  one_mem' := ⟨(orth Q).one_mem, by simp⟩
  mul_mem' := by
    rintro α β ⟨hα, hαJ⟩ ⟨hβ, hβJ⟩
    refine ⟨(orth Q).mul_mem hα hβ, ?_⟩
    change J.map ((α : V →ₗ[F] V) ∘ₗ (β : V →ₗ[F] V)) = J
    rw [Submodule.map_comp, hβJ, hαJ]
  inv_mem' := by
    rintro α ⟨hα, hαJ⟩
    exact ⟨(orth Q).inv_mem hα, map_symm_eq hαJ⟩

/-- Shimura (p. 28): "the condition $J\alpha \subset J$ can be replaced by $J\alpha = J$". -/
@[kb "shimura2004" "§4.1, p. 28 (Jα ⊂ J can be replaced by Jα = J)"]
theorem mem_parabolicO_iff_le (J : Submodule F V) (α : V ≃ₗ[F] V) :
    α ∈ parabolicO Q J ↔ α ∈ orth Q ∧ J.map (α : V →ₗ[F] V) ≤ J :=
  ⟨fun h => ⟨h.1, h.2.le⟩, fun h => ⟨h.1, map_eq_of_map_le h.2⟩⟩

/-- $P^{J\beta} = \beta^{-1}P^J\beta$ for $\beta \in O^\varphi$ (Shimura, p. 28), written for left actions:
$\alpha \in P^{\beta J}$ iff $\beta^{-1}\alpha\beta \in P^J$. -/
@[kb "shimura2004" "§4.1, p. 28 (P^{Jβ} = β⁻¹P^Jβ)"]
theorem mem_parabolicO_map_iff (J : Submodule F V) {β : V ≃ₗ[F] V} (hβ : β ∈ orth Q) (α : V ≃ₗ[F] V) :
    α ∈ parabolicO Q (J.map (β : V →ₗ[F] V)) ↔ β⁻¹ * α * β ∈ parabolicO Q J := by
  have horth : α ∈ orth Q ↔ β⁻¹ * α * β ∈ orth Q := by
    constructor
    · intro h; exact (orth Q).mul_mem ((orth Q).mul_mem ((orth Q).inv_mem hβ) h) hβ
    · intro h
      have := (orth Q).mul_mem ((orth Q).mul_mem hβ h) ((orth Q).inv_mem hβ)
      simpa [mul_assoc] using this
  have hmap : (J.map (β : V →ₗ[F] V)).map (α : V →ₗ[F] V) = J.map (β : V →ₗ[F] V) ↔
      J.map ((β⁻¹ * α * β : V ≃ₗ[F] V) : V →ₗ[F] V) = J := by
    have e : ((β⁻¹ * α * β : V ≃ₗ[F] V) : V →ₗ[F] V) =
        (β.symm : V →ₗ[F] V) ∘ₗ (α : V →ₗ[F] V) ∘ₗ (β : V →ₗ[F] V) := rfl
    rw [e, Submodule.map_comp, Submodule.map_comp]
    constructor
    · intro h; rw [h, map_symm_map]
    · intro h
      have h' := congrArg (Submodule.map (β : V →ₗ[F] V)) h
      rwa [map_map_symm] at h'
  exact ⟨fun h => ⟨horth.1 h.1, hmap.1 h.2⟩, fun h => ⟨horth.2 h.1, hmap.2 h.2⟩⟩

/-- **The homomorphism** $\lambda^J : P^J \to GL(J)$ of (4.7) (Shimura, p. 29): the restriction of $\alpha$ to $J$. -/
@[kb "shimura2004" "(4.7), p. 29 (λ^J : P^J → GL(J), restriction to J)"]
def lambdaJ (J : Submodule F V) : parabolicO Q J →* (J ≃ₗ[F] J) where
  toFun α := (α : V ≃ₗ[F] V).ofSubmodules J J α.2.2
  map_one' := by ext; rfl
  map_mul' α β := by ext; rfl

theorem lambdaJ_apply (J : Submodule F V) (α : parabolicO Q J) (x : J) :
    ((lambdaJ J α x : J) : V) = (α : V ≃ₗ[F] V) x := rfl

/-! ### (4.8): the parabolic subgroups of $SO^\varphi$, $G'(V)$, $G^+(V)$, $G^1(V)$ -/

variable (Q) in
/-- $P^{SO}_J = \{\gamma \in SO^\varphi(V) \mid J\gamma = J\}$ (Shimura (4.8a), p. 29, for $J = I_m$). -/
@[kb "shimura2004" "(4.8a), p. 29 (P_m^{SO} = {γ ∈ SO^φ(V) | I_mγ = I_m})"]
def parabolicSO (J : Submodule F V) : Subgroup (V ≃ₗ[F] V) := parabolicO Q J ⊓ orthPlus Q

theorem tau_map_mul {J : Submodule F V} {a b : cliffordGroup Q}
    (ha : J.map (tau a : V →ₗ[F] V) = J) (hb : J.map (tau b : V →ₗ[F] V) = J) :
    J.map (tau (a * b) : V →ₗ[F] V) = J := by
  rw [tau_mul]
  change J.map ((tau b : V →ₗ[F] V) ∘ₗ (tau a : V →ₗ[F] V)) = J
  rw [Submodule.map_comp, ha, hb]

variable (Q) in
/-- $P'_J = \{a \in G'(V) \mid J\tau(a) = J\}$ (Shimura (4.8a), p. 29, for $J = I_m$). -/
@[kb "shimura2004" "(4.8a), p. 29 (P'_m = {a ∈ G'(V) | I_mτ(a) = I_m})"]
def parabolicG' (J : Submodule F V) : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {a | ∃ h : a ∈ homogeneousCliffordGroup Q,
    J.map (tau ⟨a, homogeneous_le_cliffordGroup h⟩ : V →ₗ[F] V) = J}
  one_mem' := ⟨(homogeneousCliffordGroup Q).one_mem, by
    have : (⟨1, homogeneous_le_cliffordGroup (homogeneousCliffordGroup Q).one_mem⟩ : cliffordGroup Q) = 1 := rfl
    rw [this, tau_one]; simp⟩
  mul_mem' := by
    rintro a b ⟨ha, haJ⟩ ⟨hb, hbJ⟩
    refine ⟨(homogeneousCliffordGroup Q).mul_mem ha hb, ?_⟩
    have : (⟨a * b, homogeneous_le_cliffordGroup ((homogeneousCliffordGroup Q).mul_mem ha hb)⟩ :
        cliffordGroup Q) = ⟨a, homogeneous_le_cliffordGroup ha⟩ * ⟨b, homogeneous_le_cliffordGroup hb⟩ :=
      Subtype.ext rfl
    rw [this]
    exact tau_map_mul haJ hbJ
  inv_mem' := by
    rintro a ⟨ha, haJ⟩
    refine ⟨(homogeneousCliffordGroup Q).inv_mem ha, ?_⟩
    have : (⟨a⁻¹, homogeneous_le_cliffordGroup ((homogeneousCliffordGroup Q).inv_mem ha)⟩ : cliffordGroup Q) =
        (⟨a, homogeneous_le_cliffordGroup ha⟩ : cliffordGroup Q)⁻¹ := Subtype.ext rfl
    rw [this, tau_inv]
    exact map_symm_eq haJ

variable (Q) in
/-- $P^+_J = G^+(V) \cap P'_J$ (Shimura (4.8b), p. 29). -/
@[kb "shimura2004" "(4.8b), p. 29 (P_m^+ = G⁺(V) ∩ P'_m)"]
def parabolicGPlus (J : Submodule F V) : Subgroup (CliffordAlgebra Q)ˣ := M0 Q ⊓ parabolicG' Q J

variable (Q) in
/-- $P^1_J = G^1(V) \cap P'_J$ (Shimura (4.8b), p. 29). -/
@[kb "shimura2004" "(4.8b), p. 29 (P_m^1 = G¹(V) ∩ P'_m)"]
def parabolicG1 (J : Submodule F V) : Subgroup (CliffordAlgebra Q)ˣ := spinGroupG1 Q ⊓ parabolicG' Q J

/-- $\tau(P^+_J) \subseteq P^{SO}_J$ (Shimura, p. 29). -/
@[kb "shimura2004" "§4.2, p. 29 (τ(P_m^+) = P_m^{SO}, inclusion)"]
theorem tau_mem_parabolicSO (hQ : (QuadraticMap.associated Q).Nondegenerate) (J : Submodule F V)
    {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ parabolicGPlus Q J) :
    tau (Subgroup.inclusion M0_le ⟨a, ha.1⟩) ∈ parabolicSO Q J := by
  obtain ⟨_, hJ⟩ := ha.2
  exact ⟨⟨tau_mem_orth _, hJ⟩, tau_mem_orthPlus hQ ⟨a, ha.1⟩⟩

/-- $P^{SO}_J \subseteq \tau(P^+_J)$ (Shimura, p. 29: "Since $\tau(G^+(V)) = SO^\varphi(V)$, we have
$\tau(P^+) = P^{SO}$"). -/
@[kb "shimura2004" "§4.2, p. 29 (τ(P_m^+) = P_m^{SO}, surjectivity)"]
theorem exists_tau_eq_of_mem_parabolicSO (hQ : (QuadraticMap.associated Q).Nondegenerate) (J : Submodule F V)
    {α : V ≃ₗ[F] V} (hα : α ∈ parabolicSO Q J) :
    ∃ (a : (CliffordAlgebra Q)ˣ) (ha : a ∈ parabolicGPlus Q J), tau (Subgroup.inclusion M0_le ⟨a, ha.1⟩) = α := by
  obtain ⟨a, ha⟩ := exists_tau_eq hQ hα.2
  refine ⟨a, ⟨a.2, M0_le_homogeneous a.2, ?_⟩, ha⟩
  have := hα.1.2
  rw [← ha] at this
  exact this

/-! ### (4.9a): $P'_1$ for $J = Fe$ -/

/-- **(4.9a)** (Shimura, p. 30): for an isotropic (indeed any nonzero) vector $e$ and $J = Fe$,
$a \in G'(V)$ lies in $P'_J$ if and only if $a^{-1}ea \in Fe$. -/
@[kb "shimura2004" "(4.9a), p. 30 (P'_1 = {a ∈ G'(V) | a⁻¹ea ∈ Fe})"]
theorem mem_parabolicG'_span_iff (e : V) (he : e ≠ 0) (a : (CliffordAlgebra Q)ˣ)
    (ha : a ∈ homogeneousCliffordGroup Q) :
    a ∈ parabolicG' Q (F ∙ e) ↔
      ∃ c : F, ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q e * a = ι Q (c • e) := by
  set t := tau (⟨a, homogeneous_le_cliffordGroup ha⟩ : cliffordGroup Q)
  have hspec : ((a⁻¹ : (CliffordAlgebra Q)ˣ) : A) * ι Q e * a = ι Q (t e) := (tau_spec ⟨a, homogeneous_le_cliffordGroup ha⟩ e).symm
  rw [hspec]
  have key : (F ∙ e).map (t : V →ₗ[F] V) = (F ∙ e) ↔ ∃ c : F, t e = c • e := by
    rw [Submodule.map_span, Set.image_singleton]
    constructor
    · intro h
      have : t e ∈ F ∙ e := h ▸ Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact he (t.injective (by rw [hc, map_zero]))
      change F ∙ (t e) = F ∙ e
      rw [hc, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0)]
  constructor
  · rintro ⟨h, hJ⟩
    obtain ⟨c, hc⟩ := key.1 hJ
    exact ⟨c, by rw [hc]⟩
  · rintro ⟨c, hc⟩
    exact ⟨ha, key.2 ⟨c, cliffordι_injective Q hc⟩⟩

/-! ### Proposition 4.3: $G^+(V) = P_1^+G^1(V)$ -/

/-- **Proposition 4.3** (Shimura 2004, p. 30), the assertion $G^+(V) = P_1^+G^1(V)$: for a weak Witt decomposition
$V = U + Fe + Ff$ ($e^2 = f^2 = 0$, $ef + fe = 1$) and nondegenerate $\varphi$, every $a \in G^+(V)$ is $pg$ with
$p \in P_1^+$ (for $J = Fe$) and $g \in G^1(V)$. Shimura's proof: $P_1^+$ contains $\zeta = e(r,1)$ with
$\nu(\zeta) = r$ for every $r \in F^\times$ (Lemma 3.10). -/
@[kb "shimura2004" "Prop. 4.3, p. 30 (G⁺(V) = P_1^+ G¹(V))"]
theorem prop_4_3_M0_eq_mul (hQ : (QuadraticMap.associated Q).Nondegenerate) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) {a : (CliffordAlgebra Q)ˣ} (ha : a ∈ M0 Q) :
    ∃ p ∈ parabolicGPlus Q (F ∙ e), ∃ g ∈ spinGroupG1 Q, a = p * g := by
  set r := multiplier hQ ⟨a, M0_le_homogeneous ha⟩
  set p := eabHom he hf hef (r, 1)
  have hpM0 : p ∈ M0 Q := eabHom_mem_M0 he hf hef (r, 1)
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hef
  have hp : p ∈ parabolicGPlus Q (F ∙ e) := by
    refine ⟨hpM0, (mem_parabolicG'_span_iff e he0 p (M0_le_homogeneous hpM0)).2 ⟨(1 / r : F), ?_⟩⟩
    have h := tau_eab he hf hef r 1 e
    refine (tau_spec (⟨p, M0_le hpM0⟩ : cliffordGroup Q) e).symm.trans ?_
    rw [h]
    congr 1
    have hee : QuadraticMap.polar Q e e = 0 := by rw [QuadraticMap.polar_self, he, smul_zero]
    simp [hee, hef]
  refine ⟨p, hp, p⁻¹ * a, ?_, by group⟩
  have hg : p⁻¹ * a ∈ M0 Q := (M0 Q).mul_mem ((M0 Q).inv_mem hpM0) ha
  refine (mem_spinGroupG1_iff_multiplier hQ ⟨p⁻¹ * a, hg⟩).2 ?_
  have hmul := map_mul (multiplier hQ) ⟨p⁻¹, M0_le_homogeneous ((M0 Q).inv_mem hpM0)⟩
    ⟨a, M0_le_homogeneous ha⟩
  have hinv := map_inv (multiplier hQ) ⟨p, M0_le_homogeneous hpM0⟩
  have hνp : multiplier hQ ⟨p, M0_le_homogeneous hpM0⟩ = r := by
    ext
    rw [multiplier_eab hQ he hf hef r 1]
    simp
  have hx : (⟨((⟨p⁻¹ * a, hg⟩ : M0 Q) : (CliffordAlgebra Q)ˣ), M0_le_homogeneous hg⟩ :
      homogeneousCliffordGroup Q) = ⟨p, M0_le_homogeneous hpM0⟩⁻¹ * ⟨a, M0_le_homogeneous ha⟩ := Subtype.ext rfl
  rw [hx, map_mul, hinv, hνp]
  exact inv_mul_cancel r

end QuadFormsKB.Shimura2004
