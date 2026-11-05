/-
# Orders of orthogonal groups of nonsingular quadratic forms over finite fields

Work in progress towards `EvenOrthogonalOrderChar2`. This file works with Mathlib's abstract `QuadraticForm K V` over a finite field $K$ with
nondegenerate polar form $b(x,y)=Q(x+y)-Q(x)-Q(y)$ (any characteristic unless noted), and the group $O(Q)$ of linear automorphisms preserving
$Q$ (`orthGrp`). The method: $O(Q)$ acts on the set of hyperbolic pairs $\{(x,y):Q(x)=Q(y)=0,\ b(x,y)=1\}$ transitively (Witt's extension
theorem, `exists_isometryEquiv_extend_of_nondegenerate`); the stabilizer of a pair is the orthogonal group of the complement
(`exists_split_hyperbolicPlane`), which gives $|O(Q)|=\#\{\text{pairs}\}\cdot|O(Q')|$ with $Q\cong\mathbb H\perp Q'$.
-/
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Literature.Hanke2005.WittDiag
import QuadFormsKB.Siegel.KneserConnectedProof
import QuadFormsKB.Equiv.Mathlib
import QuadFormsKB.Tamagawa.OrthFq
import QuadFormsKB.Literature.Hanke2005.DensityDyadicSelfDual

open QuadraticMap QuadraticForm Module QuadraticForm.Witt

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

section Orth

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The orthogonal group $O(Q)$** of a quadratic form: the linear automorphisms $\sigma$ with $Q(\sigma x)=Q(x)$ (any characteristic;
O'Meara's `OMeara.orth` needs $2$ invertible). -/
def orthGrp (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {σ | ∀ x, Q (σ x) = Q x}
  mul_mem' := by
    intro σ τ hσ hτ x
    simp [hσ (τ x), hτ x]
  one_mem' := fun x => rfl
  inv_mem' := by
    intro σ hσ x
    have := hσ (σ⁻¹ x)
    simp only [LinearEquiv.coe_inv] at this ⊢
    rw [← this]; simp

theorem mem_orthGrp {Q : QuadraticForm K V} {σ : V ≃ₗ[K] V} : σ ∈ orthGrp Q ↔ ∀ x, Q (σ x) = Q x := Iff.rfl

/-- The set of hyperbolic pairs of $Q$. -/
def hypPairs (Q : QuadraticForm K V) : Set (V × V) :=
  {p | Q p.1 = 0 ∧ Q p.2 = 0 ∧ polar Q p.1 p.2 = 1}

theorem polar_orth {Q : QuadraticForm K V} {σ : V ≃ₗ[K] V} (hσ : σ ∈ orthGrp Q) (x y : V) :
    polar Q (σ x) (σ y) = polar Q x y := by
  simp only [polar, ← map_add, hσ _]

/-- The linear map $K^2\to V$, $(a,b)\mapsto ae+bf$. -/
def pairMap (e f : V) : K × K →ₗ[K] V :=
  (LinearMap.fst K K K).smulRight e + (LinearMap.snd K K K).smulRight f

theorem pairMap_apply (e f : V) (c : K × K) : pairMap e f c = c.1 • e + c.2 • f := rfl

theorem Q_pairMap {Q : QuadraticForm K V} {e f : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    (c : K × K) : Q (pairMap e f c) = c.1 * c.2 := by
  rw [pairMap_apply, map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, he, hf,
    polar_smul_left, polar_smul_right, hef]
  simp [smul_eq_mul]

theorem injective_pairMap {Q : QuadraticForm K V} {e f : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Injective (pairMap (K := K) e f) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ h
  rw [pairMap_apply] at h
  have h1 : polar Q e (a • e + b • f) = 0 := by rw [h]; simp
  have h2 : polar Q f (a • e + b • f) = 0 := by rw [h]; simp
  have hee : polar Q e e = 0 := by rw [polar_self_eq, he, mul_zero]
  have hff : polar Q f f = 0 := by rw [polar_self_eq, hf, mul_zero]
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  rw [polar_add_right, polar_smul_right, polar_smul_right, hee, hef] at h1
  rw [polar_add_right, polar_smul_right, polar_smul_right, hfe, hff] at h2
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, add_zero] at h1 h2
  ext <;> simp [h1, h2]

/-- **Witt transitivity on hyperbolic pairs:** a nonsingular $Q$ has an isometry carrying one hyperbolic pair to another. -/
theorem exists_orth_apply [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {e f x y : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 1) :
    ∃ σ ∈ orthGrp Q, σ e = x ∧ σ f = y := by
  have hi := injective_pairMap (K := K) he hf hef
  let W : Submodule K V := LinearMap.range (pairMap e f)
  let φ : (K × K) ≃ₗ[K] W := LinearEquiv.ofInjective (pairMap e f) hi
  let σ : W →ₗ[K] V := (pairMap x y).comp φ.symm.toLinearMap
  have hσi : Function.Injective σ := (injective_pairMap hx hy hxy).comp φ.symm.injective
  have hσ : ∀ w, Q (σ w) = Q w := by
    intro w
    obtain ⟨c, rfl⟩ := φ.surjective w
    simp only [σ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [Q_pairMap hx hy hxy]
    have : ((φ c : W) : V) = pairMap e f c := rfl
    rw [this, Q_pairMap he hf hef]
  obtain ⟨ρ, hρ⟩ := exists_isometryEquiv_extend_of_nondegenerate Q hQ σ hσi hσ
  refine ⟨ρ.toLinearEquiv, fun v => ρ.map_app v, ?_, ?_⟩
  · have h1 := hρ ⟨e, ⟨(1, 0), by simp [pairMap_apply]⟩⟩
    have h2 : σ ⟨e, ⟨(1, 0), by simp [pairMap_apply]⟩⟩ = x := by
      have : φ (1, 0) = ⟨e, ⟨(1, 0), by simp [pairMap_apply]⟩⟩ := Subtype.ext (by
        show ((LinearEquiv.ofInjective (pairMap e f) hi) (1, 0) : V) = e
        rw [LinearEquiv.ofInjective_apply]; simp [pairMap_apply])
      rw [← this]; simp [σ, pairMap_apply]
    simpa [h2] using h1
  · have h1 := hρ ⟨f, ⟨(0, 1), by simp [pairMap_apply]⟩⟩
    have h2 : σ ⟨f, ⟨(0, 1), by simp [pairMap_apply]⟩⟩ = y := by
      have : φ (0, 1) = ⟨f, ⟨(0, 1), by simp [pairMap_apply]⟩⟩ := Subtype.ext (by
        show ((LinearEquiv.ofInjective (pairMap e f) hi) (0, 1) : V) = f
        rw [LinearEquiv.ofInjective_apply]; simp [pairMap_apply])
      rw [← this]; simp [σ, pairMap_apply]
    simpa [h2] using h1

/-- **Orbit-stabilizer for hyperbolic pairs:** $|O(Q)|=\#\{\text{hyperbolic pairs}\}\cdot|\mathrm{Stab}(e,f)|$. -/
theorem card_orthGrp_eq [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {e f : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Nat.card (orthGrp Q) = Nat.card (hypPairs Q) * Nat.card (MulAction.stabilizer (orthGrp Q) (e, f)) := by
  have horb : (MulAction.orbit (orthGrp Q) (e, f) : Set (V × V)) = hypPairs Q := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨σ, hσ⟩, h⟩
      simp only [Prod.smul_mk, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : σ e = x := h1
      have h2' : σ f = y := h2
      subst h1' h2'
      exact ⟨by rw [hσ, he], by rw [hσ, hf], by rw [polar_orth hσ, hef]⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨σ, hσ, h1, h2⟩ := exists_orth_apply hQ he hf hef hx hy hxy
      exact ⟨⟨σ, hσ⟩, by simp only [Prod.smul_mk, Prod.mk.injEq]; exact ⟨h1, h2⟩⟩
  have h1 : Nat.card (MulAction.orbit (orthGrp Q) (e, f)) = Nat.card (orthGrp Q ⧸ MulAction.stabilizer (orthGrp Q) (e, f)) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (orthGrp Q) (e, f))
  have h2 : Nat.card (MulAction.orbit (orthGrp Q) (e, f)) = Nat.card (hypPairs Q) :=
    by rw [horb]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (orthGrp Q) (e, f)), ← h1, h2]

/-- **Orbit-stabilizer for a nonsingular vector:** $|O(Q)|=\#\{v:Q(v)=Q(e)\}\cdot|\mathrm{Stab}(e)|$ for $Q(e)\ne0$. -/
theorem card_orthGrp_vec [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {e : V} (he : Q e ≠ 0) :
    Nat.card (orthGrp Q) = Nat.card {v : V // Q v = Q e} * Nat.card (MulAction.stabilizer (orthGrp Q) e) := by
  have horb : (MulAction.orbit (orthGrp Q) e : Set V) = {v | Q v = Q e} := by
    ext x
    constructor
    · rintro ⟨⟨σ, hσ⟩, h⟩
      have h1 : σ e = x := h
      subst h1
      exact hσ e
    · intro hx
      obtain ⟨ρ, hρ⟩ := exists_isometryEquiv_apply_eq_of_nondegenerate Q hQ he (v := e) (w := x) rfl hx
      exact ⟨⟨ρ.toLinearEquiv, fun v => ρ.map_app v⟩, hρ⟩
  have h1 : Nat.card (MulAction.orbit (orthGrp Q) e) = Nat.card (orthGrp Q ⧸ MulAction.stabilizer (orthGrp Q) e) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (orthGrp Q) e)
  have h2 : Nat.card (MulAction.orbit (orthGrp Q) e) = Nat.card {v : V // Q v = Q e} := by
    show Nat.card ((MulAction.orbit (orthGrp Q) e : Set V)) = _
    rw [horb]; rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (orthGrp Q) e), ← h1, h2]

/-- The transvection $v\mapsto v+Q(e)^{-1}b(v,e)\,e$ (an isometry fixing $e$ in characteristic $2$). -/
def transv (Q : QuadraticForm K V) (e : V) : V →ₗ[K] V :=
  LinearMap.id + ((Q e)⁻¹ • (polarBilin Q).flip e).smulRight e

theorem transv_apply (Q : QuadraticForm K V) (e v : V) : transv Q e v = v + ((Q e)⁻¹ * polar Q v e) • e := by
  simp [transv, polarBilin_apply_apply]

section Char2

variable [CharP K 2]

theorem two_eq_zero' : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  simpa using this

theorem polar_self_zero (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq, two_eq_zero', zero_mul]

theorem Q_transv {Q : QuadraticForm K V} {e : V} (he : Q e ≠ 0) (v : V) : Q (transv Q e v) = Q v := by
  rw [transv_apply, map_add_smul]
  have h2 : (2 : K) = 0 := two_eq_zero'
  have hinv : (Q e)⁻¹ * Q e = 1 := inv_mul_cancel₀ he
  linear_combination ((Q e)⁻¹ * polar Q v e ^ 2) * hinv + ((Q e)⁻¹ * polar Q v e ^ 2) * h2

theorem transv_transv {Q : QuadraticForm K V} {e : V} (he : Q e ≠ 0) (v : V) :
    transv Q e (transv Q e v) = v := by
  have hp : polar Q (transv Q e v) e = polar Q v e := by
    rw [transv_apply, polar_add_left, polar_smul_left, polar_self_zero, smul_eq_mul, mul_zero, add_zero]
  rw [transv_apply Q e (transv Q e v), hp, transv_apply, add_assoc, ← two_smul K (((Q e)⁻¹ * polar Q v e) • e),
    two_eq_zero', zero_smul, add_zero]

theorem transv_self {Q : QuadraticForm K V} {e : V} : transv Q e e = e := by
  rw [transv_apply, polar_self_zero, mul_zero, zero_smul, add_zero]

/-- **The stabilizer of a nonzero vector in $O(Q)$ for an anisotropic nonsingular plane in characteristic $2$ has order $2$**
(the identity and the transvection $t_e$). -/
theorem card_stab_aniso [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hQa : Q.Anisotropic) (h2 : finrank K V = 2) {e : V} (he0 : e ≠ 0) :
    Nat.card (MulAction.stabilizer (orthGrp Q) e) = 2 := by
  have hc : Q e ≠ 0 := fun h => he0 (hQa e h)
  obtain ⟨w, hw⟩ : ∃ w, polar Q e w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he0 ((nondegenerate_polarBilin_iff Q).1 hQ e hall)
  set f := (polar Q e w)⁻¹ • w with hf
  have hef : polar Q e f = 1 := by rw [hf, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw]
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  have hee : polar Q e e = 0 := polar_self_zero Q e
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : polar Q e (s • e + t • f) = 0 := by rw [h]; simp
    rw [polar_add_right, polar_smul_right, polar_smul_right, hee, hef] at h1
    have ht : t = 0 := by simpa using h1
    subst ht
    have : s • e = 0 := by simpa using h
    exact ⟨(smul_eq_zero.1 this).resolve_right he0, rfl⟩
  have hspan : Submodule.span K {e, f} = ⊤ := by
    have := hli.span_eq_top_of_card_eq_finrank (by simp [h2])
    rwa [show Set.range ![e, f] = {e, f} by ext x; simp [Fin.exists_fin_two, eq_comm]; tauto] at this
  let tE : V ≃ₗ[K] V := LinearEquiv.ofLinear (transv Q e) (transv Q e)
    (LinearMap.ext fun v => transv_transv hc v) (LinearMap.ext fun v => transv_transv hc v)
  have htE : tE ∈ orthGrp Q := fun v => Q_transv hc v
  have htEv : ∀ v, tE v = transv Q e v := fun v => rfl
  have h1E : (1 : V ≃ₗ[K] V) ∈ orthGrp Q := (orthGrp Q).one_mem
  have htf : tE f = f + ((Q e)⁻¹ : K) • e := by
    rw [htEv, transv_apply, hfe, mul_one]
  have hne : (⟨⟨1, h1E⟩, by simp⟩ : MulAction.stabilizer (orthGrp Q) e) ≠ ⟨⟨tE, htE⟩, by
      rw [MulAction.mem_stabilizer_iff]; show tE e = e; rw [htEv]; exact transv_self⟩ := by
    intro h
    have := congrArg (fun z => (z.1.1 : V ≃ₗ[K] V) f) h
    simp only [LinearEquiv.coe_one, id_eq] at this
    rw [htf] at this
    have h0 : ((Q e)⁻¹ : K) • e = 0 := by
      have : f + 0 = f + ((Q e)⁻¹ : K) • e := by simpa using this
      exact (add_left_cancel this).symm
    exact he0 ((smul_eq_zero.1 h0).resolve_left (inv_ne_zero hc))
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨⟨1, h1E⟩, by simp⟩, ⟨⟨tE, htE⟩, by
      rw [MulAction.mem_stabilizer_iff]; show tE e = e; rw [htEv]; exact transv_self⟩, hne, ?_⟩
  ext ⟨⟨g, hg⟩, hst⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  have hge : g e = e := by
    have := MulAction.mem_stabilizer_iff.1 hst
    exact this
  have hx : polar Q e (g f - f) = 0 := by
    have h1 := polar_orth hg e f
    rw [hge] at h1
    rw [polar_sub_right, h1, hef, sub_self]
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top : g f - f ∈ Submodule.span K {e, f})
  have hb : b = 0 := by
    rw [← hab, polar_add_right, polar_smul_right, polar_smul_right, hee, hef] at hx
    simpa using hx
  subst hb
  have hgf : g f = f + a • e := by
    have : g f - f = a • e := by rw [← hab]; simp
    rw [← this]; abel
  have hQf : Q (g f) = Q f := hg f
  rw [hgf, map_add_smul, hfe] at hQf
  have ha : a * (a * Q e + 1) = 0 := by linear_combination hQf
  rcases mul_eq_zero.1 ha with h0 | h0
  · left
    subst h0
    have hg1 : g = 1 := by
      apply LinearEquiv.toLinearMap_injective
      refine LinearMap.ext_on hspan fun x hx => ?_
      rcases hx with rfl | rfl
      · simpa using hge
      · simpa using hgf
    exact Subtype.ext (Subtype.ext hg1)
  · right
    have hac : a = (Q e)⁻¹ := by
      have h3 : a * Q e = -1 := by linear_combination h0
      calc a = a * Q e * (Q e)⁻¹ := by field_simp
        _ = -1 * (Q e)⁻¹ := by rw [h3]
        _ = (Q e)⁻¹ := by rw [neg_one_mul, CharTwo.neg_eq]
    have hgt : g = tE := by
      apply LinearEquiv.toLinearMap_injective
      refine LinearMap.ext_on hspan fun x hx => ?_
      rcases hx with rfl | rfl
      · simp [hge, htEv, transv_self]
      · simp [hgf, htf, hac]
    exact Subtype.ext (Subtype.ext hgt)

end Char2

/-- **Isometric spaces have isomorphic orthogonal groups** (same cardinality). -/
theorem card_orthGrp_congr {V' : Type*} [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V}
    {Q' : QuadraticForm K V'} (E : Q.IsometryEquiv Q') : Nat.card (orthGrp Q) = Nat.card (orthGrp Q') := by
  refine Nat.card_congr
    { toFun := fun σ => ⟨E.toLinearEquiv.symm.trans (σ.1.trans E.toLinearEquiv), fun x => ?_⟩
      invFun := fun τ => ⟨E.toLinearEquiv.trans (τ.1.trans E.toLinearEquiv.symm), fun x => ?_⟩
      left_inv := fun σ => Subtype.ext (LinearEquiv.ext fun x => by simp)
      right_inv := fun τ => Subtype.ext (LinearEquiv.ext fun x => by simp) }
  · have hE : ∀ y, Q' (E.toLinearEquiv y) = Q y := fun y => E.map_app y
    simp only [LinearEquiv.trans_apply]
    rw [hE, σ.2, ← hE, LinearEquiv.apply_symm_apply]
  · have hE : ∀ y, Q' (E.toLinearEquiv y) = Q y := fun y => E.map_app y
    simp only [LinearEquiv.trans_apply]
    rw [← hE, LinearEquiv.apply_symm_apply, τ.2, hE]

end Orth

section Model

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (QU : QuadraticForm K U)

/-- The model $\mathbb H\perp Q_U$ on $(K\times K)\times U$. -/
abbrev modelForm : QuadraticForm K ((K × K) × U) := (hyperbolicPlane K).prod QU

theorem modelForm_apply (a b : K) (u : U) : modelForm QU ((a, b), u) = a * b + QU u := by
  simp [modelForm, QuadraticMap.prod_apply]

theorem polar_modelForm (a b a' b' : K) (u u' : U) :
    polar (modelForm QU) ((a, b), u) ((a', b'), u') = a * b' + a' * b + polar QU u u' := by
  simp only [polar, Prod.mk_add_mk, modelForm_apply]
  ring

/-- The first hyperbolic basis vector $e$ of the model. -/
def modE : (K × K) × U := ((1, 0), 0)

/-- The second hyperbolic basis vector $f$ of the model. -/
def modF : (K × K) × U := ((0, 1), 0)

theorem modE_hyp : (modE (K := K) (U := U), modF (K := K) (U := U)) ∈ hypPairs (modelForm QU) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [modE, modelForm_apply]
  · simp [modF, modelForm_apply]
  · show polar (modelForm QU) ((1, 0), 0) ((0, 1), 0) = 1
    rw [polar_modelForm]; simp

/-- The $U$-part of an automorphism of the model: $u\mapsto\mathrm{snd}(\sigma(0,u))$. -/
def uPart (σ : (((K × K) × U) ≃ₗ[K] ((K × K) × U))) : U →ₗ[K] U :=
  (LinearMap.snd K (K × K) U).comp ((σ : ((K × K) × U) →ₗ[K] ((K × K) × U)).comp (LinearMap.inr K (K × K) U))

theorem uPart_apply (σ : (((K × K) × U) ≃ₗ[K] ((K × K) × U))) (u : U) : uPart σ u = (σ ((0, 0), u)).2 := rfl

/-- An isometry of the model fixing $e,f$ preserves the complement: $\sigma(0,u)=(0,\sigma_U u)$. -/
theorem stab_apply_inr {σ : (((K × K) × U) ≃ₗ[K] ((K × K) × U))} (hσ : σ ∈ orthGrp (modelForm QU))
    (he : σ modE = modE) (hf : σ modF = modF) (u : U) : σ ((0, 0), u) = ((0, 0), uPart σ u) := by
  obtain ⟨a, b, u', hz⟩ : ∃ a b u', σ ((0, 0), u) = ((a, b), u') := ⟨_, _, _, rfl⟩
  have h1 := polar_orth hσ ((0, 0), u) modE
  have h2 := polar_orth hσ ((0, 0), u) modF
  rw [hz, he] at h1
  rw [hz, hf] at h2
  simp only [modE, modF, polar_modelForm, polar_zero_right] at h1 h2
  have hb : b = 0 := by simpa using h1
  have ha : a = 0 := by simpa using h2
  rw [uPart_apply, hz, ha, hb]

/-- Extension of an isometry of $U$ by the identity on $\mathbb H$. -/
def extId (h : orthGrp QU) : orthGrp (modelForm QU) :=
  ⟨LinearEquiv.prodCongr (LinearEquiv.refl K (K × K)) h.1, fun x => by
    obtain ⟨⟨a, b⟩, u⟩ := x
    simp only [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, modelForm_apply]
    rw [h.2 u]⟩

theorem extId_apply (h : orthGrp QU) (p : K × K) (u : U) : (extId QU h).1 (p, u) = (p, h.1 u) := rfl

theorem extId_mem_stab (h : orthGrp QU) :
    extId QU h ∈ MulAction.stabilizer (orthGrp (modelForm QU)) (modE (K := K) (U := U), modF (K := K) (U := U)) := by
  rw [MulAction.mem_stabilizer_iff]
  show ((extId QU h).1 modE, (extId QU h).1 modF) = (modE, modF)
  simp [modE, modF, extId_apply]

/-- **The stabilizer of the hyperbolic pair $(e,f)$ in $O(\mathbb H\perp Q_U)$ is $O(Q_U)$.** -/
theorem card_stab_model :
    Nat.card (MulAction.stabilizer (orthGrp (modelForm QU)) (modE (K := K) (U := U), modF (K := K) (U := U))) =
      Nat.card (orthGrp QU) := by
  symm
  refine Nat.card_eq_of_bijective (fun h => ⟨extId QU h, extId_mem_stab QU h⟩) ⟨?_, ?_⟩
  · intro h h' hh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    have := congrArg (fun z => ((z.1 : orthGrp (modelForm QU)).1 ((0, 0), u)).2) hh
    simpa [extId_apply] using this
  · rintro ⟨⟨σ, hσ⟩, hst⟩
    rw [MulAction.mem_stabilizer_iff] at hst
    have hst' : σ modE = modE ∧ σ modF = modF := by
      have := hst
      simp only [Prod.smul_mk, Prod.mk.injEq] at this
      exact this
    obtain ⟨he, hf⟩ := hst'
    have hst2 : (⟨σ⁻¹, (orthGrp (modelForm QU)).inv_mem hσ⟩ : orthGrp (modelForm QU)) ∈
        MulAction.stabilizer (orthGrp (modelForm QU)) (modE (K := K) (U := U), modF (K := K) (U := U)) := by
      have := (MulAction.stabilizer (orthGrp (modelForm QU)) (modE (K := K) (U := U), modF (K := K) (U := U))).inv_mem
        (MulAction.mem_stabilizer_iff.2 hst)
      exact this
    have hinv : σ⁻¹ modE = modE ∧ σ⁻¹ modF = modF := by
      rw [MulAction.mem_stabilizer_iff] at hst2
      simp only [Prod.smul_mk, Prod.mk.injEq] at hst2
      exact hst2
    have h1 : ∀ u, uPart σ (uPart σ⁻¹ u) = u := by
      intro u
      have := stab_apply_inr QU hσ he hf (uPart σ⁻¹ u)
      have h2 := stab_apply_inr QU ((orthGrp (modelForm QU)).inv_mem hσ) hinv.1 hinv.2 u
      rw [← h2] at this
      have h3 : σ (σ⁻¹ ((0, 0), u)) = ((0, 0), u) := by simp
      rw [h3] at this
      exact (congrArg Prod.snd this).symm
    have h1' : ∀ u, uPart σ⁻¹ (uPart σ u) = u := by
      intro u
      have h2 := stab_apply_inr QU hσ he hf u
      have := stab_apply_inr QU ((orthGrp (modelForm QU)).inv_mem hσ) hinv.1 hinv.2 (uPart σ u)
      rw [← h2] at this
      have h3 : σ⁻¹ (σ ((0, 0), u)) = ((0, 0), u) := by simp
      rw [h3] at this
      exact (congrArg Prod.snd this).symm
    let h : U ≃ₗ[K] U := LinearEquiv.ofLinear (uPart σ) (uPart σ⁻¹)
      (LinearMap.ext h1) (LinearMap.ext h1')
    have hh : h ∈ orthGrp QU := by
      intro u
      have := hσ ((0, 0), u)
      rw [stab_apply_inr QU hσ he hf u] at this
      show QU (uPart σ u) = QU u
      simpa [modelForm_apply] using this
    refine ⟨⟨h, hh⟩, Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))⟩
    obtain ⟨⟨a, b⟩, u⟩ := x
    have hx : ((a, b), u) = a • modE + b • modF + ((0, 0), u) := by
      ext <;> simp [modE, modF]
    show (extId QU ⟨h, hh⟩).1 ((a, b), u) = σ ((a, b), u)
    rw [extId_apply, hx, map_add, map_add, map_smul, map_smul, he, hf, stab_apply_inr QU hσ he hf u]
    simp [modE, modF, h]

/-- $\mathbb H\cong\mathbb H\perp\mathbb H^0$ composed with $\mathbb H^1\cong\mathbb H\perp\mathbb H^0$: $\mathbb H^1\cong\mathbb H$. -/
def hyp1Iso : (hyperbolicSpace K 1).IsometryEquiv (hyperbolicPlane K) :=
  (Witt.hyperbolicSpaceSucc (K := K) 0).symm.trans
    { toLinearEquiv := LinearEquiv.prodUnique
      map_app' := fun x => by simp [hyperbolicSpace_apply] }

end Model

section Split

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **Splitting off a hyperbolic plane from a nonsingular form of positive Witt index.** -/
theorem exists_split_model [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hw : 1 ≤ wittIndex Q) :
    ∃ U : Submodule K V, Nonempty ((modelForm (Q.comp U.subtype)).IsometryEquiv Q) := by
  have hrad := radical_eq_bot_of_nondegenerate Q hQ
  obtain ⟨A, _, _, _, Qa, ha, he⟩ := wittIndex_spec Q hrad
  obtain ⟨w, hw'⟩ : ∃ w, wittIndex Q = w + 1 := ⟨wittIndex Q - 1, by omega⟩
  rw [hw'] at he
  have hna := not_anisotropic_hyperbolicSpace_succ_prod w Qa
  have hnaQ : ¬ Q.Anisotropic := fun h => hna (anisotropic_of_isometryEquiv he.some.symm h)
  simp only [QuadraticMap.Anisotropic, not_forall] at hnaQ
  obtain ⟨v, hv, hv0⟩ := hnaQ
  obtain ⟨U, -, hU⟩ := exists_split_hyperbolicPlane Q hrad hv hv0
  exact ⟨U, hU⟩

variable {U : Type*} [AddCommGroup U] [Module K U]

theorem nondeg_of_model {QU : QuadraticForm K U} {Q : QuadraticForm K V} (E : (modelForm QU).IsometryEquiv Q)
    (hQ : (polarBilin Q).Nondegenerate) : (polarBilin QU).Nondegenerate := by
  rw [nondegenerate_polarBilin_iff] at hQ ⊢
  intro u hu
  have h : E ((0, 0), u) = 0 := by
    apply hQ
    intro y
    obtain ⟨⟨⟨a, b⟩, u'⟩, rfl⟩ := E.surjective y
    show polar Q (E ((0, 0), u)) (E ((a, b), u')) = 0
    rw [QuadraticMap.IsometryEquiv.polar_map, polar_modelForm]
    simpa using hu u'
  have := E.injective (h.trans (map_zero E).symm)
  exact congrArg Prod.snd this

theorem wittIndex_model [FiniteDimensional K V] [FiniteDimensional K U] {QU : QuadraticForm K U}
    {Q : QuadraticForm K V} (E : (modelForm QU).IsometryEquiv Q) (hQ : (polarBilin Q).Nondegenerate) :
    wittIndex Q = wittIndex QU + 1 := by
  have hradQ := radical_eq_bot_of_nondegenerate Q hQ
  have hU := nondeg_of_model E hQ
  have hradU := radical_eq_bot_of_nondegenerate QU hU
  have h1 : wittIndex Q = wittIndex (modelForm QU) := wittIndex_eq_of_equivalent ⟨E.symm⟩ hradQ
  have h2 : wittIndex ((hyperbolicSpace K 1).prod QU) = 1 + wittIndex QU :=
    wittIndex_hyperbolic_prod 1 QU hradU
  have h3 : wittIndex ((hyperbolicSpace K 1).prod QU) = wittIndex (modelForm QU) :=
    wittIndex_eq_of_equivalent ⟨hyp1Iso.prod (QuadraticMap.IsometryEquiv.refl QU)⟩
      (radical_prod_eq_bot (nondegenerate_hyperbolicSpace K 1) hradU)
  omega

end Split

section Count

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The number of solutions of $ab=c$ in $K^2$: $2q-1$ if $c=0$ and $q-1$ otherwise. -/
theorem card_mul_eq (c : K) :
    Nat.card {p : K × K // p.1 * p.2 = c} = if c = 0 then 2 * Fintype.card K - 1 else Fintype.card K - 1 := by
  classical
  have e : {p : K × K // p.1 * p.2 = c} ≃ Σ a : K, {b : K // a * b = c} :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ a : K, Nat.card {b : K // a * b = c} = if a = 0 then (if c = 0 then Fintype.card K else 0) else 1 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      by_cases hc : c = 0
      · simp [hc, Nat.card_eq_fintype_card]
      · have : IsEmpty {b : K // 0 * b = c} := ⟨fun b => hc (by simpa using b.2.symm)⟩
        rw [if_pos rfl, if_neg hc]
        exact Nat.card_of_isEmpty
    · simp only [ha, if_false]
      have : Nonempty {b : K // a * b = c} := ⟨⟨c / a, by field_simp⟩⟩
      haveI : Subsingleton {b : K // a * b = c} := ⟨fun x y => Subtype.ext (mul_left_cancel₀ ha (x.2.trans y.2.symm))⟩
      exact Nat.card_unique
  simp only [hfib]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
  have h1 : ∑ a ∈ Finset.univ.erase (0 : K), (if a = 0 then (if c = 0 then Fintype.card K else 0) else 1) =
      Fintype.card K - 1 := by
    rw [Finset.sum_congr rfl (fun a ha => if_neg (Finset.ne_of_mem_erase ha))]
    simp [Finset.card_erase_of_mem]
  rw [h1, if_pos rfl]
  have hq : 0 < Fintype.card K := Fintype.card_pos
  split_ifs <;> omega

variable {U : Type*} [AddCommGroup U] [Module K U] [Fintype U] (QU : QuadraticForm K U)

/-- **Zeros of $\mathbb H\perp Q_U$:** $Z(\mathbb H\perp Q_U)=(q-1)|U|+q\,Z(Q_U)$. -/
theorem zeros_model :
    Nat.card {v : (K × K) × U // modelForm QU v = 0} =
      (Fintype.card K - 1) * Fintype.card U + Fintype.card K * Nat.card {u : U // QU u = 0} := by
  classical
  have e : {v : (K × K) × U // modelForm QU v = 0} ≃ Σ u : U, {p : K × K // p.1 * p.2 = -QU u} :=
    { toFun := fun v => ⟨v.1.2, v.1.1, by
        obtain ⟨⟨⟨a, b⟩, u⟩, h⟩ := v
        rw [modelForm_apply] at h
        exact eq_neg_of_add_eq_zero_left h⟩
      invFun := fun p => ⟨(p.2.1, p.1), by
        rw [modelForm_apply]; exact add_eq_zero_iff_eq_neg.2 p.2.2⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_mul_eq, neg_eq_zero]
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have h1 : ∀ u : U, (if QU u = 0 then 2 * Fintype.card K - 1 else Fintype.card K - 1) =
      (Fintype.card K - 1) + (if QU u = 0 then Fintype.card K else 0) := by
    intro u; split_ifs <;> omega
  simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

/-- **Chevalley--Warning for abstract quadratic forms:** over a finite field, a quadratic form on a space of dimension $\ge3$ has a nonzero zero. -/
theorem exists_isotropic_three {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (h3 : 3 ≤ finrank K V) : ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  have e : V ≃ₗ[K] (Fin (finrank K V) → K) := LinearEquiv.ofFinrankEq V _ (by simp)
  let Q' : QuadraticForm K (Fin (finrank K V) → K) := Q.comp e.symm.toLinearMap
  obtain ⟨z, hz0, hz⟩ := Siegel.Kneser.exists_isotropic_of_three_le (K := K) h3 (QuadFormsKB.QuadForm.ofQuadraticForm Q')
  rw [QuadFormsKB.QuadForm.eval_ofQuadraticForm] at hz
  exact ⟨e.symm z, fun h => hz0 (by simpa using h), hz⟩

/-- **Level sets of an anisotropic plane over a finite field of characteristic $2$:** $\#\{v:Q(v)=c\}=q+1$ for $c\ne0$. -/
theorem card_level_aniso {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hK : ringChar K = 2) (Q : QuadraticForm K V) (hQa : Q.Anisotropic) (h2 : finrank K V = 2)
    {c : K} (hc : c ≠ 0) : Nat.card {v : V // Q v = c} = Fintype.card K + 1 := by
  classical
  have hfin : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  set N : K → ℕ := fun c => Nat.card {v : V // Q v = c} with hN
  have hN0 : N 0 = 1 := by
    simp only [hN]
    haveI : Unique {v : V // Q v = 0} :=
      { default := ⟨0, map_zero Q⟩
        uniq := fun v => Subtype.ext (hQa v.1 v.2) }
    exact Nat.card_unique
  have hconst : ∀ c' : K, c' ≠ 0 → N c' = N c := by
    intro c' hc'
    obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two hK (c' / c)
    have hl0 : l ≠ 0 := by
      intro h0
      rw [h0, mul_zero, div_eq_zero_iff] at hl
      rcases hl with h | h
      · exact hc' h
      · exact hc h
    have hl2 : c' = l ^ 2 * c := by
      have h := (div_eq_iff hc).1 hl
      rw [h]; ring
    simp only [hN]
    refine Nat.card_congr
      { toFun := fun v => ⟨l⁻¹ • v.1, by
          rw [QuadraticMap.map_smul, v.2, smul_eq_mul, hl2]; field_simp⟩
        invFun := fun v => ⟨l • v.1, by rw [QuadraticMap.map_smul, v.2, smul_eq_mul, hl2]; ring⟩
        left_inv := fun v => Subtype.ext (by simp [smul_smul, hl0])
        right_inv := fun v => Subtype.ext (by simp [smul_smul, hl0]) }
  have hsum : ∑ x : K, N x = Fintype.card K ^ 2 := by
    have e : V ≃ Σ x : K, {v : V // Q v = x} := (Equiv.sigmaFiberEquiv Q).symm
    have := Nat.card_congr e
    rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := K) (V := V), h2, Nat.card_eq_fintype_card] at this
    exact this.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), hN0,
    Finset.sum_congr rfl (fun x hx => hconst x (Finset.ne_of_mem_erase hx)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul] at hsum
  have hq : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
    omega
  have : (Fintype.card K - 1) * (N c) = (Fintype.card K - 1) * (Fintype.card K + 1) := by
    have h3 : (Fintype.card K - 1) * (Fintype.card K + 1) = Fintype.card K ^ 2 - 1 := by
      obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 1 := ⟨Fintype.card K - 1, by omega⟩
      rw [hr]; simp; ring_nf; omega
    rw [h3]; omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-- The partners $y$ of the standard singular vector $e$ in the model: $\#=|U|$. -/
theorem card_partners_modE :
    Nat.card {y : (K × K) × U // modelForm QU y = 0 ∧ polar (modelForm QU) modE y = 1} = Fintype.card U := by
  classical
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective (fun u => ⟨((-QU u, 1), u), ?_, ?_⟩) ⟨?_, ?_⟩
  · rw [modelForm_apply]; ring
  · show polar (modelForm QU) ((1, 0), 0) ((-QU u, 1), u) = 1
    rw [polar_modelForm]; simp
  · intro u u' h
    have := congrArg (fun z => z.1.2) h
    simpa using this
  · rintro ⟨⟨⟨a, b⟩, u⟩, h1, h2⟩
    refine ⟨u, Subtype.ext ?_⟩
    simp only [modE, polar_modelForm] at h2
    rw [modelForm_apply] at h1
    have hb : b = 1 := by simpa using h2
    have ha : a = -QU u := eq_neg_of_add_eq_zero_left (by subst hb; simpa using h1)
    simp [ha, hb]

variable [FiniteDimensional K U]

/-- **Hyperbolic pairs of the model:** $\#\{\text{pairs}\}=(Z-1)\,|U|$, $Z$ the number of zeros of $\mathbb H\perp Q_U$. -/
theorem card_hypPairs_model (hM : (polarBilin (modelForm QU)).Nondegenerate) :
    Nat.card (hypPairs (modelForm QU)) =
      (Nat.card {v : (K × K) × U // modelForm QU v = 0} - 1) * Fintype.card U := by
  classical
  set QM := modelForm QU with hQM
  have hrad := radical_eq_bot_of_nondegenerate QM hM
  -- fiber over a singular vector
  let S := {x : (K × K) × U // QM x = 0 ∧ x ≠ 0}
  let Y : S → Type _ := fun x => {y : (K × K) × U // QM y = 0 ∧ polar QM x.1 y = 1}
  have e : hypPairs QM ≃ Σ x : S, Y x :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1, fun h0 => by
          have := p.2.2.2; rw [h0] at this; simp at this⟩, ⟨p.1.2, p.2.2.1, p.2.2.2⟩⟩
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  have hY : ∀ x : S, Nat.card (Y x) = Fintype.card U := by
    intro x
    rw [← card_partners_modE QU]
    obtain ⟨ρ, hρ⟩ := exists_isometryEquiv_apply_eq_of_isotropic QM hrad (v := modE) (w := x.1)
      (by simp [modE, Prod.ext_iff]) x.2.2 (by simp [hQM, modE, modelForm_apply]) x.2.1
    refine (Nat.card_congr (Equiv.subtypeEquiv ρ.toLinearEquiv.toEquiv (fun y => ?_))).symm
    show (QM y = 0 ∧ polar QM modE y = 1) ↔ QM (ρ y) = 0 ∧ polar QM x.1 (ρ y) = 1
    rw [← hρ, QuadraticMap.IsometryEquiv.polar_map, ρ.map_app]
  have hS : Nat.card S = Nat.card {v : (K × K) × U // modelForm QU v = 0} - 1 := by
    have hfil : (Finset.univ.filter fun v : (K × K) × U => QM v = 0) =
        insert 0 (Finset.univ.filter fun v : (K × K) × U => QM v = 0 ∧ v ≠ 0) := by
      ext v
      by_cases h : v = 0 <;> simp [h]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype, hfil,
      Finset.card_insert_of_notMem (by simp)]
    simp
  haveI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun x _ => hY x), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hS]

end Count

/-- **$|O(Q)|=2(q+1)$ for an anisotropic nonsingular plane over $\mathbb F_q$, $q$ even.** -/
theorem card_orthGrp_aniso_plane {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hQa : Q.Anisotropic) (h2 : finrank K V = 2) :
    Nat.card (orthGrp Q) = 2 * (Fintype.card K + 1) := by
  have hpos : 0 < finrank K V := by omega
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨e, he0⟩ := exists_ne (0 : V)
  have hc : Q e ≠ 0 := fun h => he0 (hQa e h)
  rw [card_orthGrp_vec hQ hc, card_stab_aniso hQ hQa h2 he0,
    card_level_aniso (ringChar.eq K 2) Q hQa h2 hc]
  ring

section Induction

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]

theorem nondeg_model_of_equiv {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {QU : QuadraticForm K U} {Q : QuadraticForm K V} (E : (modelForm QU).IsometryEquiv Q)
    (hQ : (polarBilin Q).Nondegenerate) : (polarBilin (modelForm QU)).Nondegenerate := by
  rw [nondegenerate_polarBilin_iff] at hQ ⊢
  intro x hx
  have h : E x = 0 := by
    apply hQ
    intro y
    obtain ⟨y', rfl⟩ := E.surjective y
    exact (QuadraticMap.IsometryEquiv.polar_map E x y').trans (hx y')
  exact E.injective (h.trans (map_zero E).symm)

/-- **The inductive step:** if $Q\cong\mathbb H\perp Q_U$ is nonsingular then the numbers of zeros and the orders of the orthogonal groups
are related by $Z(Q)=(q-1)q^d+qZ(Q_U)$ and $|O(Q)|=(Z(Q)-1)q^d|O(Q_U)|$, $d=\dim U$. -/
theorem step_model {V U : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {QU : QuadraticForm K U} {Q : QuadraticForm K V}
    (E : (modelForm QU).IsometryEquiv Q) (hQ : (polarBilin Q).Nondegenerate) :
    finrank K V = finrank K U + 2 ∧ (polarBilin QU).Nondegenerate ∧
    Nat.card {v : V // Q v = 0} =
      (Fintype.card K - 1) * Fintype.card K ^ finrank K U + Fintype.card K * Nat.card {u : U // QU u = 0} ∧
    Nat.card (orthGrp Q) =
      (Nat.card {v : V // Q v = 0} - 1) * Fintype.card K ^ finrank K U * Nat.card (orthGrp QU) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  haveI : Fintype U := Fintype.ofFinite U
  have hM := nondeg_model_of_equiv E hQ
  have hU : Fintype.card U = Fintype.card K ^ finrank K U := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
  have hZ : Nat.card {v : V // Q v = 0} = Nat.card {v : (K × K) × U // modelForm QU v = 0} :=
    (Nat.card_congr (Equiv.subtypeEquiv E.toLinearEquiv.toEquiv (fun v => by
      show modelForm QU v = 0 ↔ Q (E v) = 0
      rw [E.map_app]))).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := E.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self] at this
    omega
  · exact nondeg_of_model E hQ
  · rw [hZ, zeros_model QU, hU]
  · rw [← card_orthGrp_congr E, card_orthGrp_eq hM (modE_hyp QU).1 (modE_hyp QU).2.1 (modE_hyp QU).2.2,
      card_stab_model QU, card_hypPairs_model QU hM, hZ, hU]

/-- A nonsingular form with a nonzero zero is a model $\mathbb H\perp Q_U$. -/
theorem exists_model_of_isotropic {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : v ≠ 0) (hv0 : Q v = 0) :
    ∃ U : Submodule K V, Nonempty ((modelForm (Q.comp U.subtype)).IsometryEquiv Q) := by
  obtain ⟨U, -, hU⟩ := exists_split_hyperbolicPlane Q (radical_eq_bot_of_nondegenerate Q hQ) hv0 hv
  exact ⟨U, hU⟩

theorem card_zeros_pos {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) : 0 < Nat.card {v : V // Q v = 0} := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Nonempty {v : V // Q v = 0} := ⟨⟨0, map_zero Q⟩⟩
  exact Nat.card_pos

/-- **Zeros and order for the space of dimension $2(k+1)$ over $\mathbb F_q$, $q$ even.** -/
theorem zeros_and_card [CharP K 2] (k : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V),
      (polarBilin Q).Nondegenerate → finrank K V = 2 * (k + 1) →
      ((Nat.card {v : V // Q v = 0} : ℤ) = (Fintype.card K : ℤ) ^ (2 * k + 1) +
          (if wittIndex Q = k + 1 then 1 else -1) * ((Fintype.card K : ℤ) ^ (k + 1) - (Fintype.card K : ℤ) ^ k)) ∧
      (Nat.card (orthGrp Q) : ℤ) =
        QuadFormsKB.LocalDensity.DVR.oEven (Fintype.card K : ℤ) (k + 1) (if wittIndex Q = k + 1 then 1 else -1) := by
  induction k with
  | zero =>
    intro V _ _ _ Q hQ hd
    by_cases hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0
    · obtain ⟨v, hv, hv0⟩ := hiso
      obtain ⟨U, ⟨E⟩⟩ := exists_model_of_isotropic Q hQ hv hv0
      obtain ⟨hdim, hU, hZ, hO⟩ := step_model E hQ
      have hd0 : finrank K U = 0 := by omega
      haveI : Subsingleton U := Module.finrank_zero_iff.1 hd0
      have hQUa : (Q.comp U.subtype).Anisotropic := fun x _ => Subsingleton.elim _ _
      have hw : wittIndex Q = 1 := by
        symm
        exact eq_wittIndex Q (radical_eq_bot_of_nondegenerate Q hQ) hQUa
          ⟨E.symm.trans (hyp1Iso.prod (QuadraticMap.IsometryEquiv.refl _)).symm⟩
      have hZU : Nat.card {u : U // (Q.comp U.subtype) u = 0} = 1 := by
        haveI : Unique {u : U // (Q.comp U.subtype) u = 0} :=
          { default := ⟨0, map_zero _⟩, uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
        exact Nat.card_unique
      have hOU : Nat.card (orthGrp (Q.comp U.subtype)) = 1 := by
        haveI : Unique (orthGrp (Q.comp U.subtype)) :=
          { default := 1, uniq := fun x => Subtype.ext (LinearEquiv.ext fun u => Subsingleton.elim _ _) }
        exact Nat.card_unique
      rw [hZU, hd0] at hZ
      have hpos := card_zeros_pos Q
      rw [hw]
      simp only [if_true]
      have hq : 1 ≤ Fintype.card K := Fintype.card_pos
      have hZz : (Nat.card {v : V // Q v = 0} : ℤ) = 2 * Fintype.card K - 1 := by
        rw [hZ]; push_cast [Nat.cast_sub hq]; ring
      refine ⟨by rw [hZz]; ring, ?_⟩
      rw [hO, hOU, hd0]
      push_cast [Nat.cast_sub hpos]
      rw [hZz]
      simp only [QuadFormsKB.LocalDensity.DVR.oEven]
      simp
      ring
    · push Not at hiso
      have hQa : Q.Anisotropic := fun x hx => by_contra fun h => hiso x h hx
      have hw : wittIndex Q ≠ 1 := by
        intro h1
        have hrad := radical_eq_bot_of_nondegenerate Q hQ
        obtain ⟨A, _, _, _, Qa, ha, he⟩ := wittIndex_spec Q hrad
        rw [h1] at he
        have hna := not_anisotropic_hyperbolicSpace_succ_prod 0 Qa
        exact hna (anisotropic_of_isometryEquiv he.some.symm hQa)
      rw [if_neg hw]
      have hZ : Nat.card {v : V // Q v = 0} = 1 := by
        haveI : Unique {v : V // Q v = 0} :=
          { default := ⟨0, map_zero Q⟩, uniq := fun v => Subtype.ext (hQa v.1 v.2) }
        exact Nat.card_unique
      constructor
      · rw [hZ]; push_cast; ring
      · rw [card_orthGrp_aniso_plane hQ hQa (by omega)]
        simp only [QuadFormsKB.LocalDensity.DVR.oEven]
        push_cast
        simp
  | succ k ih =>
    intro V _ _ _ Q hQ hd
    have hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0 :=
      exists_isotropic_three Q (by omega)
    obtain ⟨v, hv, hv0⟩ := hiso
    obtain ⟨U, ⟨E⟩⟩ := exists_model_of_isotropic Q hQ hv hv0
    obtain ⟨hdim, hU, hZ, hO⟩ := step_model E hQ
    have hdU : finrank K U = 2 * (k + 1) := by omega
    obtain ⟨ihZ, ihO⟩ := ih U (Q.comp U.subtype) hU hdU
    have hw : wittIndex Q = wittIndex (Q.comp U.subtype) + 1 := wittIndex_model E hQ
    have hε : (if wittIndex Q = k + 1 + 1 then (1 : ℤ) else -1) =
        (if wittIndex (Q.comp U.subtype) = k + 1 then 1 else -1) := by
      rw [hw]; simp
    rw [hε]
    set ε : ℤ := (if wittIndex (Q.comp U.subtype) = k + 1 then 1 else -1) with hεdef
    have hε2 : ε * ε = 1 := by rw [hεdef]; split_ifs <;> norm_num
    have hq : 1 ≤ Fintype.card K := Fintype.card_pos
    have hpos := card_zeros_pos Q
    rw [hdU] at hZ hO
    have hZz : (Nat.card {v : V // Q v = 0} : ℤ) = (Fintype.card K : ℤ) ^ (2 * (k + 1) + 1) +
        ε * ((Fintype.card K : ℤ) ^ (k + 1 + 1) - (Fintype.card K : ℤ) ^ (k + 1)) := by
      rw [hZ]; push_cast [Nat.cast_sub hq]; rw [ihZ]; ring
    refine ⟨by rw [show 2 * (k + 1) + 1 = 2 * (k + 1) + 1 from rfl] at hZz; convert hZz using 2, ?_⟩
    rw [hO]
    push_cast [Nat.cast_sub hpos]
    rw [hZz, ihO]
    simp only [QuadFormsKB.LocalDensity.DVR.oEven, Nat.add_sub_cancel, Finset.prod_range_succ]
    generalize (Fintype.card K : ℤ) = x at *
    generalize (∏ i ∈ Finset.range k, (x ^ (2 * (i + 1)) - 1)) = P
    have key : x ^ (2 * (k + 1) + 1) + ε * (x ^ (k + 1 + 1) - x ^ (k + 1)) - 1 =
        (x ^ (k + 1 + 1) - ε) * (x ^ (k + 1) + ε) := by
      linear_combination (1 : ℤ) * hε2
    rw [key]
    linear_combination (-(x ^ (k + 1 + 1) - ε) * x ^ (2 * (k + 1)) * 2 * x ^ ((k + 1) * k) * P) * hε2

end Induction

section Bridge

open QuadFormsKB Matrix

theorem card_GL_orth {k : Type*} [Field k] {n : ℕ} (Q : QuadForm k n) :
    Nat.card {g : GL (Fin n) k // Q.compMat g.val = Q} = Nat.card (orthGrp Q.toQuadraticForm) := by
  let e : GL (Fin n) k ≃* ((Fin n → k) ≃ₗ[k] (Fin n → k)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k))
  have he : ∀ g x, e g x = g.val *ᵥ x := fun g x => rfl
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun g => ?_))
  show _ ↔ e g ∈ orthGrp Q.toQuadraticForm
  rw [mem_orthGrp]
  simp only [he, QuadForm.toQuadraticForm_apply]
  constructor
  · intro h x
    have := congrArg (fun F => QuadForm.eval F x) h
    simp only [QuadForm.eval_compMat] at this
    exact this
  · intro h
    exact QuadForm.eq_of_eval_eq fun x => by rw [QuadForm.eval_compMat, h]

theorem map_injective_quadForm {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : Function.Injective φ) {n : ℕ}
    {Q₁ Q₂ : QuadForm A n} (h : Q₁.map φ = Q₂.map φ) : Q₁ = Q₂ := by
  have := congrArg QuadForm.coeff h
  apply QuadForm.ext
  ext i j
  exact hφ (congrFun (congrFun this i) j)

/-- **$|O(Q\bmod\pi)|$ is the order of the orthogonal group of the reduction $\bar Q$ over the residue field.** -/
theorem card_orthMod_eq_orthGrp {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
    (hπ : Irreducible π) {n : ℕ} (Q : QuadForm R n) :
    Nat.card (QuadFormsKB.LocalDensity.DVR.orthMod Q π 1) =
      Nat.card (orthGrp (Q.map (IsLocalRing.residue R)).toQuadraticForm) := by
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  let φ : (R ⧸ Ideal.span {π ^ 1}) ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq (by rw [pow_one, ← hmax])
  have hφ : ∀ r : R, φ (Ideal.Quotient.mk _ r) = IsLocalRing.residue R r := fun r => rfl
  rw [← card_GL_orth]
  let Ψ := Units.mapEquiv (φ.mapMatrix (m := Fin n)).toMulEquiv
  refine Nat.card_congr (Equiv.subtypeEquiv Ψ.toEquiv (fun g => ?_))
  have h1 : Q.map (IsLocalRing.residue R) = (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).map φ.toRingHom := by
    apply QuadForm.ext
    ext i j
    simp [QuadForm.map, hφ]
  have h2 : ((Ψ g : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = g.val.map φ := rfl
  show _ ↔ (Q.map (IsLocalRing.residue R)).compMat (Ψ g).val = Q.map (IsLocalRing.residue R)
  have h3 := QuadForm.map_compMat φ.toRingHom (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))) g.val
  rw [h2, h1]
  change _ ↔ _ = _
  show (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).compMat g.val = Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1})) ↔ _
  rw [show (g.val.map ⇑φ) = g.val.map ⇑φ.toRingHom from rfl, h3]
  constructor
  · intro h
    exact congrArg (QuadForm.map φ.toRingHom) h
  · intro h
    exact map_injective_quadForm _ φ.injective h

theorem nondegenerate_toQuadraticForm {k : Type*} [Field k] {n : ℕ} (Q : QuadForm k n) (hdet : Q.hessian.det ≠ 0) :
    (polarBilin Q.toQuadraticForm).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  apply Matrix.eq_zero_of_vecMul_eq_zero hdet
  funext j
  have h := hv (Pi.single j 1)
  rw [polar, QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply,
    QuadForm.toQuadraticForm_apply, QuadForm.eval, QuadForm.eval, QuadForm.eval, QuadForm.polar_eq_hessian k] at h
  simp at h
  exact h

/-- **The order of $O(Q\bmod\pi)$ for a unimodular even-dimensional form, $\pi\mid2$** (the content of `EvenOrthogonalOrderChar2`). -/
theorem card_orthMod_even {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) {m : ℕ} (hm : 1 ≤ m)
    (Q : QuadForm R (2 * m)) (hdet : IsUnit Q.hessian.det) :
    (Nat.card (QuadFormsKB.LocalDensity.DVR.orthMod Q π 1) : ℤ) =
      QuadFormsKB.LocalDensity.DVR.oEven (QuadFormsKB.LocalDensity.DVR.q R) m
        (if QuadraticForm.wittIndex (Q.map (IsLocalRing.residue R)).toQuadraticForm = m then 1 else -1) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  haveI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have h20 : (2 : IsLocalRing.ResidueField R) = 0 := by
    have : (IsLocalRing.residue R) 2 = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]; exact h2
    exact (map_ofNat (IsLocalRing.residue R) 2).symm.trans this
  haveI : CharP (IsLocalRing.ResidueField R) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h20
  have hdet' : (Q.map (IsLocalRing.residue R)).hessian.det ≠ 0 := by
    have : (Q.map (IsLocalRing.residue R)).hessian = Q.hessian.map (IsLocalRing.residue R) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this, show (Q.hessian.map (IsLocalRing.residue R)).det = IsLocalRing.residue R Q.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (hdet.map _).ne_zero
  have hnd := nondegenerate_toQuadraticForm _ hdet'
  have := (zeros_and_card (K := IsLocalRing.ResidueField R) j (Fin (2 * (j + 1)) → IsLocalRing.ResidueField R)
    (Q.map (IsLocalRing.residue R)).toQuadraticForm hnd (by simp)).2
  rw [card_orthMod_eq_orthGrp hπ, this, QuadFormsKB.LocalDensity.DVR.q, Nat.card_eq_fintype_card]

/-- **`EvenOrthogonalOrderChar2` is a theorem**: the order $2q^{m(m-1)}(q^m-\varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1)$ of the
orthogonal group of a nonsingular quadratic form in $2m$ variables over $\mathbb F_q$, $q$ even, proved by counting
hyperbolic pairs and stabilizers (`zeros_and_card`) and transferred to matrices over $R/\pi$ (`card_orthMod_even`). -/
@[kb "omeara1963" "93:15 (even unimodular lattices); order of O^ε_{2m}(F_q), q even: Dieudonne, La geometrie des groupes classiques, Ch. III [unverified]"]
theorem evenOrthogonalOrderChar2 : EvenOrthogonalOrderChar2 :=
  ⟨fun {R} _ _ _ _ {π} hπ h2 {m} hm Q hdet => card_orthMod_even hπ h2 hm Q hdet⟩

/-- **`DyadicOrthogonalOrder` from the Hensel link alone**: `dyadicOrthogonalOrder_of_split` with the finite-field
group order `evenOrthogonalOrderChar2` proved; the only named input left is `DyadicWittLink`. -/
@[kb "omeara1963" "93:15, 93:16--93:18 (order of the orthogonal group of the reduction; Hensel link)"]
theorem dyadicOrthogonalOrder_of_wittLink {F : Type} [Field F] [NumberField F] (I : DyadicWittLink F) :
    DyadicOrthogonalOrder F :=
  dyadicOrthogonalOrder_of_split evenOrthogonalOrderChar2 I

end Bridge

end QuadFormsKB.Hanke2005
