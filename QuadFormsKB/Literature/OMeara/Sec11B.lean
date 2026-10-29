/-
# O'Meara §11F: completions (11:10 – 11:15)

**Setting.** A field $K$ with a valuation $|\ |$ (Mathlib `AbsoluteValue K ℝ`). A *completion* of $(K, |\ |)$ in
O'Meara's sense (§11F, p. 9) is a field $E$ with a complete valuation, containing $K$ as a dense subfield and
inducing the original valuation on $K$. Here $E$ is a Mathlib `NormedField` and the inclusion is a ring homomorphism
$\iota\colon K \to E$; this is the structure `IsCompletion`. (O'Meara's "spot" $\mathfrak P$ on $E$ is the
equivalence class of the valuation, which is not recorded separately.)

**Proves**
* `isCompletion_self`, `surjective_of_isCompletion` (**11:10**): a complete field is its own completion, and has no
  other (every completion is surjective, so it is $K$ itself);
* `completeSpace_iff_of_isTopologicalIso` (**11:12**): completeness is invariant under topological isomorphism
  (`IsTopologicalIso`);
* `exists_isCompletion` (**11:13**): every valued field has a completion, namely Mathlib's
  `UniformSpace.Completion (WithAbs v)`;
* `exists_prolongation` (**11:14**) and `exists_unique_equiv_of_isCompletion` (**11:15**): the universal property
  and uniqueness of the completion.

**Special case in 11:14.** O'Meara's $\varphi\colon F \to G$ is a topological isomorphism into a complete field; by
11:6 one may choose valuations making it analytic. We state the analytic case: $\lVert\varphi x\rVert = |x|$
(an isometric field embedding into a complete normed field), and prove existence and isometry of the prolongation
and its uniqueness among continuous ring homomorphisms.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Topology.UniformSpace.UniformEmbedding

open Filter Topology

namespace QuadFormsKB.OMeara

universe u
variable {K : Type u} [Field K]

/-- **Completion of a valued field** (O'Meara §11F, p. 9). `IsCompletion v E ι` says that the normed field $E$,
together with the field embedding $\iota\colon K \to E$, is a completion of $K$ at the valuation $v$: $\iota$ is
isometric ($\lVert\iota x\rVert = v(x)$, so $E$ induces the original valuation on $K$), the image $\iota(K)$ is dense
in $E$, and $E$ is complete. The topology on $E$ is that of its norm. -/
@[kb "omeara1963" "§11F, definition of a completion, p. 9"]
structure IsCompletion (v : AbsoluteValue K ℝ) (E : Type*) [NormedField E] (ι : K →+* E) : Prop where
  norm_eq : ∀ x, ‖ι x‖ = v x
  dense : DenseRange ι
  complete : CompleteSpace E

/-- The map $x \mapsto \iota(x)$ from $(K, v)$ to a completion $E$ is an isometry. -/
theorem IsCompletion.isometry {v : AbsoluteValue K ℝ} {E : Type*} [NormedField E] {ι : K →+* E}
    (h : IsCompletion v E ι) : Isometry (fun x : WithAbs v => ι (WithAbs.ofAbs x)) := by
  refine AddMonoidHomClass.isometry_of_norm
    ((ι.comp (WithAbs.equiv v).toRingHom).toAddMonoidHom) fun x => ?_
  simpa [WithAbs.norm_eq_apply_ofAbs] using h.norm_eq (WithAbs.ofAbs x)

/-- The embedding of a completion has dense range (stated for `WithAbs v`). -/
theorem IsCompletion.denseRange' {v : AbsoluteValue K ℝ} {E : Type*} [NormedField E]
    {ι : K →+* E} (h : IsCompletion v E ι) :
    DenseRange (fun x : WithAbs v => ι (WithAbs.ofAbs x)) := by
  have : Set.range (fun x : WithAbs v => ι (WithAbs.ofAbs x)) = Set.range ι := by
    ext z; constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨WithAbs.toAbs v x, rfl⟩
  unfold DenseRange
  rw [this]; exact h.dense

/-- **11:10 (first half).** A complete field is its own completion: if $K$ is complete under the valuation $v$
(`CompleteSpace (WithAbs v)`), then $K$ itself, with the identity embedding, is a completion of $K$. -/
@[kb "omeara1963" "§11F, 11:10, p. 9"]
theorem isCompletion_self (v : AbsoluteValue K ℝ) [CompleteSpace (WithAbs v)] :
    IsCompletion v (WithAbs v) (WithAbs.equiv v).symm.toRingHom where
  norm_eq _ := rfl
  dense := (WithAbs.equiv v).symm.surjective.denseRange
  complete := inferInstance

/-- **11:10 (second half).** A complete field has no other completion: if $K$ is complete under the valuation $v$
and $(E, \iota)$ is a completion of $K$, then $\iota\colon K \to E$ is surjective (so an isomorphism). -/
@[kb "omeara1963" "§11F, 11:10, p. 9"]
theorem surjective_of_isCompletion (v : AbsoluteValue K ℝ) [CompleteSpace (WithAbs v)]
    {E : Type*} [NormedField E] (ι : K →+* E) (h : IsCompletion v E ι) :
    Function.Surjective ι := by
  have hc : IsClosed (Set.range (fun x : WithAbs v => ι (WithAbs.ofAbs x))) :=
    h.isometry.isClosedEmbedding.isClosed_range
  have hcl := h.denseRange'.closure_eq
  rw [hc.closure_eq] at hcl
  intro y
  have hy : y ∈ Set.range (fun x : WithAbs v => ι (WithAbs.ofAbs x)) := hcl ▸ Set.mem_univ y
  obtain ⟨x, hx⟩ := hy
  exact ⟨WithAbs.ofAbs x, hx⟩

/-- A ring isomorphism $\sigma\colon F \to G$ is a *topological isomorphism* for the valuations $v$ on $F$ and $w$
on $G$ if it is a homeomorphism between the topologies they define (O'Meara §11D, 11:6). Phrased through Mathlib's
`WithAbs.congr`. -/
def IsTopologicalIso {F G : Type*} [Field F] [Field G] (v : AbsoluteValue F ℝ)
    (w : AbsoluteValue G ℝ) (σ : F ≃+* G) : Prop :=
  IsHomeomorph (WithAbs.congr v w σ)

/-- **11:12.** Let $\sigma\colon F \to G$ be a topological isomorphism of fields with valuations $v$, $w$
(`IsTopologicalIso`). Then $F$ is complete at $v$ if and only if $G$ is complete at $w$. Complete means every
Cauchy sequence converges (`CompleteSpace (WithAbs v)`); since the isomorphism is additive and continuous it is
uniformly continuous, so Cauchy sequences correspond. -/
@[kb "omeara1963" "§11F, 11:12, p. 10"]
theorem completeSpace_iff_of_isTopologicalIso {F G : Type*} [Field F] [Field G]
    (v : AbsoluteValue F ℝ) (w : AbsoluteValue G ℝ) (σ : F ≃+* G)
    (h : IsTopologicalIso v w σ) : CompleteSpace (WithAbs v) ↔ CompleteSpace (WithAbs w) := by
  let e := (WithAbs.congr v w σ)
  have hc : Continuous e := h.continuous
  have hc' : Continuous e.symm := by
    refine h.homeomorph.symm.continuous.congr fun x => ?_
    apply e.injective
    exact (h.homeomorph.apply_symm_apply x).trans (e.apply_symm_apply x).symm
  have u1 : UniformContinuous e :=
    uniformContinuous_addMonoidHom_of_continuous (f := e.toAddMonoidHom) hc
  have u2 : UniformContinuous e.symm :=
    uniformContinuous_addMonoidHom_of_continuous (f := e.symm.toAddMonoidHom) hc'
  exact (UniformEquiv.completeSpace_iff
    { toEquiv := e.toEquiv, uniformContinuous_toFun := u1, uniformContinuous_invFun := u2 })

/-- **11:13.** A field $K$ with a valuation $v$ has a completion: there are a normed field $E$ and an embedding
$\iota\colon K \to E$ with `IsCompletion v E ι`. The witness is Mathlib's `v.Completion`
$= $ `UniformSpace.Completion (WithAbs v)`. -/
@[kb "omeara1963" "§11F, 11:13, p. 10"]
theorem exists_isCompletion (v : AbsoluteValue K ℝ) :
    ∃ (E : Type u) (_ : NormedField E) (ι : K →+* E), IsCompletion v E ι := by
  refine ⟨v.Completion, inferInstance,
    (UniformSpace.Completion.coeRingHom).comp (WithAbs.equiv v).symm.toRingHom, ?_⟩
  refine ⟨fun x => ?_, ?_, inferInstance⟩
  · show ‖((WithAbs.toAbs v x : WithAbs v) : UniformSpace.Completion (WithAbs v))‖ = v x
    rw [UniformSpace.Completion.norm_coe]; rfl
  · exact (UniformSpace.Completion.denseRange_coe).comp (WithAbs.equiv v).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)


/-- **11:14 (analytic case).** Let $(E, \iota)$ be a completion of $(K, v)$ and let $\sigma\colon K \to G$ be a
field embedding into a complete normed field $G$ with $\lVert\sigma x\rVert = v(x)$. Then $\sigma$ extends to a
ring homomorphism $\tau\colon E \to G$ with $\tau\circ\iota = \sigma$, which is isometric
($\lVert\tau y\rVert = \lVert y\rVert$), and $\tau$ is the only continuous ring homomorphism with
$\tau\circ\iota = \sigma$. O'Meara states this for a topological isomorphism $\sigma$, obtained by 11:6 from an
analytic one after choosing valuations; the analytic case is the one proved here. -/
@[kb "omeara1963" "§11F, 11:14, p. 10"]
theorem exists_prolongation (v : AbsoluteValue K ℝ) {E G : Type*} [NormedField E] [NormedField G]
    [CompleteSpace G] (ι : K →+* E) (hι : IsCompletion v E ι) (σ : K →+* G)
    (hσ : ∀ x, ‖σ x‖ = v x) :
    ∃ τ : E →+* G, (∀ x, τ (ι x) = σ x) ∧ (∀ y, ‖τ y‖ = ‖y‖) ∧
      ∀ τ' : E →+* G, Continuous τ' → (∀ x, τ' (ι x) = σ x) → τ' = τ := by
  set e : WithAbs v → E := fun x => ι (WithAbs.ofAbs x) with he_def
  set f : WithAbs v → G := fun x => σ (WithAbs.ofAbs x) with hf_def
  have hei : Isometry e := hι.isometry
  have hfi : Isometry f := by
    refine AddMonoidHomClass.isometry_of_norm
      ((σ.comp (WithAbs.equiv v).toRingHom).toAddMonoidHom) fun x => ?_
    simpa [WithAbs.norm_eq_apply_ofAbs] using hσ (WithAbs.ofAbs x)
  have hind : IsUniformInducing e := hei.isUniformInducing
  have hd : DenseRange e := hι.denseRange'
  have hdi := hind.isDenseInducing hd
  set τf : E → G := hdi.extend f with hτf
  have hτc : Continuous τf := (uniformContinuous_uniformly_extend hind hd hfi.uniformContinuous).continuous
  have hτe : ∀ x, τf (e x) = f x := fun x => uniformly_extend_of_ind hind hd hfi.uniformContinuous x
  have hadd : ∀ x y, τf (x + y) = τf x + τf y := by
    have := DenseRange.equalizer (hd.prodMap hd) (g := fun p : E × E => τf (p.1 + p.2))
      (h := fun p => τf p.1 + τf p.2) (by fun_prop) (by fun_prop) (by
        funext p
        obtain ⟨x, y⟩ := p
        simp only [Function.comp_apply, Prod.map]
        have h1 : e x + e y = e (x + y) := by simp [he_def, map_add]
        rw [h1, hτe, hτe, hτe]
        simp [hf_def, map_add])
    intro x y
    exact congrFun this (x, y)
  have hmul : ∀ x y, τf (x * y) = τf x * τf y := by
    have := DenseRange.equalizer (hd.prodMap hd) (g := fun p : E × E => τf (p.1 * p.2))
      (h := fun p => τf p.1 * τf p.2) (by fun_prop) (by fun_prop) (by
        funext p
        obtain ⟨x, y⟩ := p
        simp only [Function.comp_apply, Prod.map]
        have h1 : e x * e y = e (x * y) := by simp [he_def, map_mul]
        rw [h1, hτe, hτe, hτe]
        simp [hf_def, map_mul])
    intro x y
    exact congrFun this (x, y)
  have hone : τf 1 = 1 := by
    have : (1 : E) = e 1 := by simp [he_def]
    rw [this, hτe]; simp [hf_def]
  let τ : E →+* G :=
    { toFun := τf
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hadd 0 0
        simpa using this
      map_add' := hadd }
  refine ⟨τ, fun x => ?_, fun y => ?_, fun τ' hτ' h' => ?_⟩
  · show τf (ι x) = σ x
    exact hτe (WithAbs.toAbs v x)
  · have := DenseRange.equalizer hd (g := fun y : E => ‖τf y‖) (h := fun y => ‖y‖)
      (by fun_prop) (by fun_prop) (by
        funext x
        simp only [Function.comp_apply]
        rw [hτe]
        simp only [hf_def, he_def]
        rw [hσ, hι.norm_eq])
    exact congrFun this y
  · ext y
    have := DenseRange.equalizer hd (g := fun y : E => τ' y) (h := τf) hτ' hτc (by
      funext x
      simp only [Function.comp_apply]
      rw [hτe]
      exact h' _)
    exact congrFun this y


/-- **11:15.** Let $(E_1, \iota_1)$ and $(E_2, \iota_2)$ be completions of $(K, v)$. Then there is a ring
isomorphism $e\colon E_1 \to E_2$ with $e\circ\iota_1 = \iota_2$, which is isometric (hence a topological
isomorphism), and it is the only continuous ring isomorphism with this property. -/
@[kb "omeara1963" "§11F, 11:15, p. 11"]
theorem exists_unique_equiv_of_isCompletion (v : AbsoluteValue K ℝ) {E₁ E₂ : Type*}
    [NormedField E₁] [NormedField E₂] (ι₁ : K →+* E₁) (ι₂ : K →+* E₂)
    (h₁ : IsCompletion v E₁ ι₁) (h₂ : IsCompletion v E₂ ι₂) :
    ∃ e : E₁ ≃+* E₂, (∀ x, e (ι₁ x) = ι₂ x) ∧ (∀ y, ‖e y‖ = ‖y‖) ∧
      ∀ e' : E₁ ≃+* E₂, Continuous e' → (∀ x, e' (ι₁ x) = ι₂ x) → e' = e := by
  have := h₁.complete
  have := h₂.complete
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_prolongation v ι₁ h₁ ι₂ (fun x => h₂.norm_eq x)
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_prolongation v ι₂ h₂ ι₁ (fun x => h₁.norm_eq x)
  obtain ⟨i1, -, -, hi1⟩ := exists_prolongation v ι₁ h₁ ι₁ (fun x => h₁.norm_eq x)
  obtain ⟨i2, -, -, hi2⟩ := exists_prolongation v ι₂ h₂ ι₂ (fun x => h₂.norm_eq x)
  have ac : Continuous a := (AddMonoidHomClass.isometry_of_norm a ha2).continuous
  have bc : Continuous b := (AddMonoidHomClass.isometry_of_norm b hb2).continuous
  have hba : b.comp a = RingHom.id E₁ := by
    have e1 := hi1 (b.comp a) (bc.comp ac) (fun x => by simp [ha1, hb1])
    have e2 := hi1 (RingHom.id E₁) continuous_id (fun x => rfl)
    rw [e1, e2]
  have hab : a.comp b = RingHom.id E₂ := by
    have e1 := hi2 (a.comp b) (ac.comp bc) (fun x => by simp [ha1, hb1])
    have e2 := hi2 (RingHom.id E₂) continuous_id (fun x => rfl)
    rw [e1, e2]
  let e : E₁ ≃+* E₂ := RingEquiv.ofRingHom a b hab hba
  refine ⟨e, ha1, ha2, fun e' hc he' => ?_⟩
  ext y
  have := ha3 e'.toRingHom hc he'
  exact congrFun (congrArg DFunLike.coe this) y

end QuadFormsKB.OMeara
