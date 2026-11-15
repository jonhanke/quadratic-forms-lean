/-
# Shimura 2004, §4.7: $P^\varphi_m = Q^\varphi R^\varphi$ in $SO^\varphi$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §4.7, (4.23a), (4.23b) and the
sentence after them (printed p. 32); the remark after (4.6) (p. 29). Page numbers are printed pages.

**Setting.** As in `Wave5/Levi.lean`. Shimura's (4.23a) is
$Q^\varphi = \{\mathrm{diag}[\hat a, e, a] \mid a \in GL_m(F),\ e \in SO^\omega(W)\}$; here `leviQ hH`, the
isometries preserving each of $I'_m$, $W$, $I_m$ whose $W$-block $\pi^J(q)$ lies in $SO^\omega(W)$.

**Proves** (all unconditional; standard axioms only)
* for an endomorphism preserving the three summands of $V = I_m + W + I'_m$, the determinant is the product of the
  three block determinants (`det_eq_mul_three`);
* for $q = \mathrm{diag}[\hat a, e, a] \in Q^J$: $\det q = \det e$, because $\hat a$ is the inverse transpose of $a$
  by (4.22) (`det_eq_det_piJ`); so $\mathrm{diag}[\hat a, e, a] \in SO^\varphi$ if and only if $e \in SO^\omega$,
  Shimura's remark after (4.6) for block-diagonal elements (`leviQO_mem_orthPlus_iff`);
* **§4.7**: $P^\varphi_m = Q^\varphi R^\varphi$ and $R^\varphi$ is a normal subgroup of $P^\varphi_m$
  (`theorem_4_23`, `leviQ_le`, `unipR_normal`), with $Q^\varphi \cap R^\varphi = 1$ (`leviQ_inf_unipR`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave5.Unipotent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

namespace Levi

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ}

omit [Invertible (2 : F)] in
/-- **Block determinants.** If $V = A \oplus B \oplus C$ (as subspaces) and $g$ preserves each of $A$, $B$, $C$,
then $\det g = \det(g|_A)\det(g|_B)\det(g|_C)$. -/
theorem det_eq_mul_three (g : Module.End F V) (A B C : Submodule F V)
    (hinj : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a + (b + c) = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hsurj : ∀ x, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + (b + c) = x)
    (hA : ∀ x ∈ A, g x ∈ A) (hB : ∀ x ∈ B, g x ∈ B) (hC : ∀ x ∈ C, g x ∈ C) :
    LinearMap.det g =
      LinearMap.det (g.restrict hA) * (LinearMap.det (g.restrict hB) * LinearMap.det (g.restrict hC)) := by
  let φ : A × (B × C) →ₗ[F] V := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨a, b, c⟩ h
      have := hinj a a.2 b b.2 c c.2 h
      ext <;> simp [this.1, this.2.1, this.2.2]
    · intro x
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hsurj x
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), rfl⟩
  let E := LinearEquiv.ofBijective φ hφ
  let ψ : Module.End F (A × (B × C)) := (g.restrict hA).prodMap ((g.restrict hB).prodMap (g.restrict hC))
  have key : (E : A × (B × C) →ₗ[F] V) ∘ₗ ψ = g ∘ₗ (E : A × (B × C) →ₗ[F] V) := by
    ext <;> simp [E, ψ, φ, LinearMap.restrict_apply]
  have hg : g = (E : A × (B × C) →ₗ[F] V) ∘ₗ ψ ∘ₗ (E.symm : V →ₗ[F] A × (B × C)) := by
    ext x
    have := congrArg (fun h => h (E.symm x)) key
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact this.symm
  have hc := LinearMap.det_conj ψ E
  rw [← hg] at hc
  rw [hc]
  simp only [ψ, LinearMap.det_prodMap]

variable {e f : Fin m → V} (hH : IsHypFamily Q e f)
include hH

/-- The symmetric form of the duality: an element of $I_m$ orthogonal to $I'_m$ is $0$. -/
theorem eq_zero_of_polar_spanF {x : V} (hx : x ∈ spanE F e) (h : ∀ y ∈ spanE F f, QuadraticMap.polar Q x y = 0) :
    x = 0 := by
  rw [← projE_of_mem_spanE hH hx, projE_apply]
  simp [h _ (Submodule.subset_span ⟨_, rfl⟩)]

/-- The pairing $I'_m \to (I_m)^*$, $y \mapsto 2\varphi(y, \cdot)$. -/
def pairF : spanE F f →ₗ[F] Module.Dual F (spanE F e) :=
  ((QuadraticMap.polarBilin Q).compl₂ (spanE F e).subtype).comp (spanE F f).subtype

omit hH in
theorem pairF_apply (y : spanE F f) (x : spanE F e) :
    pairF (Q := Q) (e := e) (f := f) y x = QuadraticMap.polar Q y x := rfl

theorem pairF_injective : Function.Injective (pairF (Q := Q) (e := e) (f := f)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  exact Subtype.ext (eq_zero_of_polar_spanE hH y.2 fun x hx => by
    have := congrArg (fun φ : Module.Dual F (spanE F e) => φ ⟨x, hx⟩) hy
    simpa [pairF_apply] using this)

theorem finrank_spanF_eq : finrank F (spanE F f) = finrank F (Module.Dual F (spanE F e)) := by
  apply le_antisymm (LinearMap.finrank_le_finrank_of_injective (pairF_injective hH))
  rw [Subspace.dual_finrank_eq]
  let pairE : spanE F e →ₗ[F] Module.Dual F (spanE F f) :=
    ((QuadraticMap.polarBilin Q).compl₂ (spanE F f).subtype).comp (spanE F e).subtype
  have hinj : Function.Injective pairE := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (eq_zero_of_polar_spanF hH x.2 fun y hy => by
      have := congrArg (fun φ : Module.Dual F (spanE F f) => φ ⟨y, hy⟩) hx
      simpa [pairE] using this)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

/-- The duality $I'_m \cong (I_m)^*$ of §4.7. -/
def pairEquiv : spanE F f ≃ₗ[F] Module.Dual F (spanE F e) :=
  LinearMap.linearEquivOfInjective _ (pairF_injective hH) (finrank_spanF_eq hH)

/-- **$\det q = \det \pi^J(q)$ for $q = \mathrm{diag}[\hat a, e, a] \in Q^J$**: $\det \hat a \det a = 1$ since
$\hat a$ is the inverse transpose of $a$ (4.22). -/
theorem det_eq_det_piJ {q : V ≃ₗ[F] V} (hq : q ∈ leviQO Q e f) :
    LinearMap.det (q : V →ₗ[F] V) =
      LinearMap.det ((piJ e f hH ⟨q, leviQO_le hq⟩ : wSpace Q e f ≃ₗ[F] wSpace Q e f) :
        wSpace Q e f →ₗ[F] wSpace Q e f) := by
  obtain ⟨hO, hE, hF, hW⟩ := id hq
  have mE : ∀ x ∈ spanE F e, (q : V →ₗ[F] V) x ∈ spanE F e := fun x hx => by rw [← hE]; exact ⟨x, hx, rfl⟩
  have mF : ∀ x ∈ spanE F f, (q : V →ₗ[F] V) x ∈ spanE F f := fun x hx => by rw [← hF]; exact ⟨x, hx, rfl⟩
  have mW : ∀ x ∈ wSpace Q e f, (q : V →ₗ[F] V) x ∈ wSpace Q e f := fun x hx => by
    rw [← hW]; exact ⟨x, hx, rfl⟩
  have hdet := det_eq_mul_three (q : V →ₗ[F] V) (spanE F e) (wSpace Q e f) (spanE F f)
    (fun a ha b hb c hc h => by
      have h1 := congrArg (projE Q e f) h
      have h2 := congrArg (projW Q e f) h
      have h3 := congrArg (projF Q e f) h
      simp only [map_add, map_zero, projE_of_mem_spanE hH ha, projE_of_mem_wSpace hH hb,
        projE_of_mem_spanF hH hc, projW_of_mem_spanE hH ha, projW_of_mem_wSpace hH hb, projW_of_mem_spanF hH hc,
        projF_of_mem_spanE hH ha, projF_of_mem_wSpace hH hb, projF_of_mem_spanF hH hc, add_zero, zero_add]
        at h1 h2 h3
      exact ⟨h1, h2, h3⟩)
    (fun x => ⟨_, projE_mem x, _, projW_mem hH x, _, projF_mem x, by
      conv_rhs => rw [decomp (Q := Q) (e := e) (f := f) x]
      abel⟩)
    mE mW mF
  -- the `W`-block is `π^J(q)`
  have hWb : (q : V →ₗ[F] V).restrict mW =
      ((piJ e f hH ⟨q, leviQO_le hq⟩ : wSpace Q e f ≃ₗ[F] wSpace Q e f) :
        wSpace Q e f →ₗ[F] wSpace Q e f) := by
    ext w
    simp only [LinearMap.restrict_apply, LinearEquiv.coe_coe]
    rw [piJ_apply]
    exact (projW_of_mem_wSpace hH (mW _ w.2)).symm
  -- the two hyperbolic blocks have inverse determinants
  have mE' : ∀ x ∈ spanE F e, (q.symm : V →ₗ[F] V) x ∈ spanE F e := fun x hx => by
    rw [← map_symm_eq hE]; exact ⟨x, hx, rfl⟩
  set a := (q : V →ₗ[F] V).restrict mE
  set a' := (q.symm : V →ₗ[F] V).restrict mE'
  have haa' : a * a' = 1 := by
    ext x; simp [a, a', LinearMap.restrict_apply]
  have hdual : (pairEquiv hH : spanE F f →ₗ[F] Module.Dual F (spanE F e)) ∘ₗ (q : V →ₗ[F] V).restrict mF ∘ₗ
      ((pairEquiv hH).symm : Module.Dual F (spanE F e) →ₗ[F] spanE F f) = a'.dualMap := by
    apply LinearMap.ext; intro φ
    apply LinearMap.ext; intro x
    obtain ⟨y, rfl⟩ := (pairEquiv hH).surjective φ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.dualMap_apply]
    change pairF (Q := Q) (e := e) (f := f) _ x = pairF (Q := Q) (e := e) (f := f) y (a' x)
    rw [pairF_apply, pairF_apply]
    simp only [LinearMap.restrict_apply, a']
    have := polar_map_of_mem_orth hO (y : V) (q.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  have hF' : LinearMap.det ((q : V →ₗ[F] V).restrict mF) = LinearMap.det a' := by
    rw [← LinearMap.det_conj ((q : V →ₗ[F] V).restrict mF) (pairEquiv hH), hdual, LinearMap.det_dualMap]
  have h1 : LinearMap.det a * LinearMap.det a' = 1 := by
    rw [← map_mul, haa', map_one]
  rw [hdet, hWb, hF']
  linear_combination (LinearMap.det ((piJ e f hH ⟨q, leviQO_le hq⟩ :
    wSpace Q e f ≃ₗ[F] wSpace Q e f) : wSpace Q e f →ₗ[F] wSpace Q e f)) * h1

/-- $\mathrm{diag}[\hat a, e, a] \in SO^\varphi$ if and only if $e \in SO^\omega$ (Shimura, p. 29, after (4.6)). -/
@[kb "shimura2004" "(4.6), p. 29 (ε ∈ SO^φ iff e ∈ SO^ω, for block-diagonal ε)"]
theorem leviQO_mem_orthPlus_iff {q : V ≃ₗ[F] V} (hq : q ∈ leviQO Q e f) :
    q ∈ orthPlus Q ↔ piJ e f hH ⟨q, leviQO_le hq⟩ ∈ orthPlus (Q.restrict (wSpace Q e f)) := by
  have hd := det_eq_det_piJ hH hq
  simp only [orthPlus, Subgroup.mem_inf, MonoidHom.mem_ker, ← Units.val_eq_one, LinearEquiv.coe_det]
  rw [hd]
  exact ⟨fun h => ⟨piJ_mem_orth hH _, h.2⟩, fun h => ⟨hq.1, h.2⟩⟩

variable (e f) in
/-- **$Q^\varphi = \{\mathrm{diag}[\hat a, e, a] \mid a \in GL_m(F),\ e \in SO^\omega(W)\}$** ((4.23a), p. 32): the
isometries preserving each of $I'_m$, $W$, $I_m$ (so of the form $\mathrm{diag}[\hat a, e, a]$ with $\hat a$ dual to
$a$ by (4.22), `polar_projF_map`) whose $W$-block $e = \pi^J(q)$ is in $SO^\omega(W)$. -/
@[kb "shimura2004" "(4.23a), p. 32 (Q^φ = {diag[â, e, a] | a ∈ GL_m(F), e ∈ SO^ω(W)})"]
def leviQ : Subgroup (V ≃ₗ[F] V) :=
  leviQO Q e f ⊓ ((orthPlus (Q.restrict (wSpace Q e f))).comap (piJ e f hH)).map (parabolicO Q (spanE F e)).subtype

theorem mem_leviQ_iff (q : V ≃ₗ[F] V) :
    q ∈ leviQ e f hH ↔ ∃ hq : q ∈ leviQO Q e f,
      piJ e f hH ⟨q, leviQO_le hq⟩ ∈ orthPlus (Q.restrict (wSpace Q e f)) := by
  constructor
  · rintro ⟨hq, ⟨q', hq', rfl⟩⟩
    exact ⟨hq, hq'⟩
  · rintro ⟨hq, h⟩
    exact ⟨hq, ⟨⟨q, leviQO_le hq⟩, h, rfl⟩⟩

/-- $Q^\varphi \subseteq P^\varphi_m$. -/
theorem leviQ_le : leviQ e f hH ≤ parabolicSO Q (spanE F e) := by
  intro q hq
  obtain ⟨hq, h⟩ := (mem_leviQ_iff hH q).1 hq
  exact ⟨leviQO_le hq, (leviQO_mem_orthPlus_iff hH hq).2 h⟩

/-- **$P^\varphi_m = Q^\varphi R^\varphi$** (Shimura §4.7, p. 32: "It can easily be seen that
$P^\varphi_m = Q^\varphi R^\varphi$"): every $\varepsilon \in P^\varphi_m$ is $qr$ with $q \in Q^\varphi$,
$r \in R^\varphi$. -/
@[kb "shimura2004" "§4.7, p. 32 (P^φ_m = Q^φR^φ)"]
theorem theorem_4_23 {α : V ≃ₗ[F] V} (hα : α ∈ parabolicSO Q (spanE F e)) :
    ∃ q ∈ leviQ e f hH, ∃ r ∈ unipR Q e f, α = q * r := by
  obtain ⟨q, hq, r, hr, rfl⟩ := parabolicO_eq_leviQO_mul_unipRO hH hα.1
  have hrSO := unipRO_le_orthPlus hH hr
  have hqSO : q ∈ orthPlus Q := by
    have := (orthPlus Q).mul_mem hα.2 ((orthPlus Q).inv_mem hrSO)
    rwa [mul_inv_cancel_right] at this
  refine ⟨q, (mem_leviQ_iff hH q).2 ⟨hq, (leviQO_mem_orthPlus_iff hH hq).1 hqSO⟩, r, ?_, rfl⟩
  rw [unipR_eq_unipRO hH]; exact hr

/-- $Q^\varphi \cap R^\varphi = 1$. -/
theorem leviQ_inf_unipR : leviQ e f hH ⊓ unipR Q e f = ⊥ := by
  rw [eq_bot_iff, ← leviQO_inf_unipRO hH, unipR_eq_unipRO hH]
  exact inf_le_inf_right _ inf_le_left

/-- **$R^\varphi$ is a normal subgroup of $P^\varphi_m$** (Shimura §4.7, p. 32). -/
@[kb "shimura2004" "§4.7, p. 32 (R^φ is a normal subgroup of P^φ_m)"]
theorem unipR_normal : ((unipR Q e f).subgroupOf (parabolicSO Q (spanE F e))).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, unipR_eq_unipRO hH] at hn ⊢
  have := (unipRO_normal hH).conj_mem ⟨n, n.2.1⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, g.2.1⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

end Levi

end QuadFormsKB.Shimura2004
