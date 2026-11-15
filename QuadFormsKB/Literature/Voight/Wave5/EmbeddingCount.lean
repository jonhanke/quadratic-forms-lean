/-
# Embedding numbers for class number one (Voight, Corollary 30.4.17, Proposition 30.7.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Theorem 30.4.7 and
Corollary 30.4.17 (pp. 548–550), Proposition 30.5.3 (p. 552), Proposition 30.7.4 (p. 559).

**Setting** (as in `Wave4.TraceFormulaEmb`). $F$ a number field, $B = (a, b)_F$ with $a, b \in \mathbb Z_F$ nonzero,
$\mathcal O \subseteq B$ an order, $\operatorname{Cls}\mathcal O$ = `ClsO O` (classes of nonzero locally principal left
ideals), $S$ a quadratic $\mathbb Z_F$-order that is a domain, $h(S) = \#\operatorname{Pic}S$ (`ClassGroup S`),
$m(S, \mathcal O; \Gamma)$ = `embNum`. The book works with right ideals and left orders; here left ideals and right orders
(`Wave4.rightOrder`), as in the earlier waves.

**Contents.**
* `embNum_eq_of_clsNum_eq_one` (**Corollary 30.4.17**, **proved conditional on** the trace formula
  `Wave4.TraceFormulaEmb F`): if $\#\operatorname{Cls}\mathcal O = 1$ then
  $m(S, \mathcal O; \mathcal O^\times) = h(S)\,m(\widehat S, \widehat{\mathcal O}; \widehat{\mathcal O}^\times)$.
  Ingredients proved here, without inputs: the unit ideal's class lies in $\operatorname{Cls}\mathcal O$, the class of a
  locally principal ideal consists of locally principal ideals, $\mathcal O_R(\mathcal O\beta) = \beta^{-1}\mathcal O\beta$,
  and embedding numbers are invariant under conjugating the order.
* `normalizerUnits`, `embNumNorm`: the normalizer $N_{B^\times}(\mathcal O)$ and $m(S, \mathcal O; N_{B^\times}(\mathcal O))$.
* `EmbNumNormalizerClassOne` (**Proposition 30.7.4**, with a corrected hypothesis): stated.
-/
import QuadFormsKB.Literature.Voight.Wave5.ClassNumber
import QuadFormsKB.Tamagawa.TernaryGlueNF

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight.Wave7

open NumberField IsDedekindDomain QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave4

/-! ### The normalizer and embedding numbers modulo the normalizer -/

section Normalizer

variable (R F : Type*) {B : Type*} (S : Type*) [CommRing R] [Field F] [Algebra R F] [Ring B] [Algebra F B]
  [Algebra R B] [IsScalarTower R F B] [CommRing S] [Algebra R S]

/-- **The normalizer** $N_{B^\times}(\mathcal O) = \{\beta \in B^\times : \beta^{-1}\mathcal O\beta = \mathcal O\}$ of an
$R$-subalgebra $\mathcal O \subseteq B$ (Voight 2021, 30.3.10 and Proposition 30.5.3 (b)). -/
@[kb "voight2021" "Proposition 30.7.4, p. 559"]
def normalizerUnits (O : Subalgebra R B) : Subgroup Bˣ where
  carrier := {β | ∀ x, x ∈ O ↔ ((β⁻¹ : Bˣ) : B) * x * (β : B) ∈ O}
  one_mem' x := by simp
  mul_mem' {β γ} hβ hγ x := by
    rw [hβ, hγ]
    simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
  inv_mem' {β} hβ x := by
    simp only [inv_inv]
    rw [hβ ((β : B) * x * ((β⁻¹ : Bˣ) : B))]
    rw [show ((β⁻¹ : Bˣ) : B) * ((β : B) * x * ((β⁻¹ : Bˣ) : B)) * (β : B) = x by
      simp only [← mul_assoc, Units.inv_mul, one_mul]; rw [mul_assoc, Units.inv_mul, mul_one]]

variable {R S}

/-- **Conjugacy of optimal embeddings by the normalizer** (Voight 2021, 30.3.10): $\psi = \beta^{-1}\varphi\beta$ for some
$\beta \in N_{B^\times}(\mathcal O)$. -/
def embSetoidNorm (O : Subalgebra R B) : Setoid (OptEmb R F S O) where
  r φ ψ := ∃ β ∈ normalizerUnits R O, ∀ s, ψ.1 s = ((β⁻¹ : Bˣ) : B) * φ.1 s * (β : B)
  iseqv := by
    refine ⟨fun φ => ⟨1, (normalizerUnits R O).one_mem, fun s => by simp⟩, ?_, ?_⟩
    · rintro φ ψ ⟨β, hβ, h⟩
      refine ⟨β⁻¹, (normalizerUnits R O).inv_mem hβ, fun s => ?_⟩
      rw [h s, inv_inv]
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    · rintro φ ψ χ ⟨β, hβ, h⟩ ⟨γ, hγ, h'⟩
      refine ⟨β * γ, (normalizerUnits R O).mul_mem hβ hγ, fun s => ?_⟩
      rw [h' s, h s, _root_.mul_inv_rev]
      simp only [Units.val_mul, mul_assoc]

variable (S)

/-- **The embedding number modulo the normalizer** $m(S, \mathcal O; N_{B^\times}(\mathcal O))$ (Voight 2021, (30.3.11)):
the number of $N_{B^\times}(\mathcal O)$-conjugacy classes of optimal embeddings $S \to \mathcal O$ (`Nat.card`). -/
@[kb "voight2021" "Proposition 30.7.4, p. 559"]
def embNumNorm (O : Subalgebra R B) : ℕ := Nat.card (Quotient (embSetoidNorm F (S := S) O))

end Normalizer

/-! ### Proposition 30.7.4 (stated) -/

section Global

variable {F : Type} [Field F] [NumberField F]

/-- **Embedding numbers of a maximal order of class number one, modulo the normalizer** (Voight 2021, Proposition 30.7.4),
as a named proposition about the number field $F$: let $\mathcal O \subseteq (a, b)_F$ be a maximal order with
$\#\operatorname{Cls}\mathcal O = 1$ and $S$ a quadratic $\mathbb Z_F$-order that is a domain, whose fraction field embeds in
$B$, such that $\operatorname{Emb}(S_{\mathfrak p}, \mathcal O_{\mathfrak p}) \neq \emptyset$ for every prime $\mathfrak p$. Then
$m(S, \mathcal O; N_{B^\times}(\mathcal O)) = h(S)$.

*Update:* the book states this without the local hypothesis. It is needed: by Proposition 30.5.3 (b), at a ramified prime
$\mathfrak p$ with $S_{\mathfrak p}$ not integrally closed there is no optimal embedding, so the left side is $0$ (for the
Hurwitz order over $\mathbb Q$, ramified at $2$, and $S = \mathbb Z[2i]$: $m = 0$, $h(S) = 1$). With the hypothesis, every
local embedding number modulo the local normalizer is $1$ (Proposition 30.5.3), which is what the book's proof uses.
Stated, not proved (it needs the normalizer version of the trace formula). -/
@[kb "voight2021" "Proposition 30.7.4, p. 559"]
def EmbNumNormalizerClassOne (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsMaximalOrder (𝓞 F) F O →
  clsNum O = 1 →
  ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Finite (𝓞 F) S], Module.finrank (𝓞 F) S = 2 →
    (∃ φ : S →ₐ[𝓞 F] QuatF F a b, Function.Injective φ) →
    (∀ v : HeightOneSpectrum (𝓞 F),
      embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S) (localOrder (v := v) a b O) ⊤
        ≠ 0) →
    embNumNorm F S O = Nat.card (ClassGroup S)

end Global


/-! ### Embedding numbers are invariant under conjugating the order -/

section Conj

variable {R F : Type*} {B : Type*} {S : Type*} [CommRing R] [Field F] [Algebra R F] [Ring B] [Algebra F B]
  [Algebra R B] [IsScalarTower R F B] [CommRing S] [Algebra R S]

/-- The $F$-algebra automorphism $x \mapsto \beta^{-1}x\beta$ of $B$, for $\beta \in B^\times$. -/
def conjAlg (β : Bˣ) : B ≃ₐ[F] B where
  toFun x := ((β⁻¹ : Bˣ) : B) * x * (β : B)
  invFun x := (β : B) * x * ((β⁻¹ : Bˣ) : B)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by simp [← Algebra.commutes r]

theorem conjAlg_apply (β : Bˣ) (x : B) : conjAlg (F := F) β x = ((β⁻¹ : Bˣ) : B) * x * (β : B) := rfl

/-- The image of an optimal embedding under an $F$-algebra automorphism is an optimal embedding of the image order. -/
theorem isOptimalEmbedding_map_iff (e : B ≃ₐ[F] B) (O : Subalgebra R B) (φ : S →ₐ[R] B) :
    IsOptimalEmbedding R F S (O.map (e.restrictScalars R).toAlgHom) ((e.restrictScalars R).toAlgHom.comp φ) ↔
      IsOptimalEmbedding R F S O φ := by
  have hspan : Submodule.span F (Set.range ((e.restrictScalars R).toAlgHom.comp φ)) =
      (Submodule.span F (Set.range φ)).map e.toLinearMap := by
    rw [Submodule.map_span, AlgHom.coe_comp, Set.range_comp]; rfl
  have hinj : Function.Injective e := e.injective
  constructor
  · intro h
    refine ⟨fun s t hst => h.injective (by simpa using congrArg e hst), fun s => ?_, fun x hx hxs => ?_⟩
    · obtain ⟨y, hy, hys⟩ := h.mem s
      have : y = φ s := hinj hys
      rw [← this]; exact hy
    · have hx' : e x ∈ (O.map (e.restrictScalars R).toAlgHom) := ⟨x, hx, rfl⟩
      have hxs' : e x ∈ Submodule.span F (Set.range ((e.restrictScalars R).toAlgHom.comp φ)) := by
        rw [hspan]; exact ⟨x, hxs, rfl⟩
      obtain ⟨s, hs⟩ := h.optimal _ hx' hxs'
      exact ⟨s, hinj hs⟩
  · intro h
    refine ⟨fun s t hst => h.injective (hinj hst), fun s => ⟨φ s, h.mem s, rfl⟩, fun x hx hxs => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hspan] at hxs
    obtain ⟨z, hz, hzy⟩ := hxs
    have : z = y := hinj hzy
    subst this
    obtain ⟨s, hs⟩ := h.optimal _ hy hz
    exact ⟨s, by simp [hs]⟩

/-- Conjugacy by all units transports along an automorphism of $B$ carrying $\mathcal O$ onto $\mathcal O'$. -/
theorem conjBy_top_comp {O O' : Subalgebra R B} (e : B ≃ₐ[R] B) (f : O ≃* O') (hf : ∀ x : O, ((f x : O') : B) = e x)
    {φ ψ : S →ₐ[R] B} (h : ConjBy (⊤ : Subgroup Oˣ) φ ψ) :
    ConjBy (⊤ : Subgroup O'ˣ) (e.toAlgHom.comp φ) (e.toAlgHom.comp ψ) := by
  obtain ⟨γ, -, hγ⟩ := h
  refine ⟨Units.map f.toMonoidHom γ, Subgroup.mem_top _, fun s => ?_⟩
  have h1 : ((((Units.map f.toMonoidHom γ)⁻¹ : O'ˣ) : O') : B) = e (((γ⁻¹ : Oˣ) : O) : B) := by
    rw [← map_inv]; exact hf _
  have h2 : (((Units.map f.toMonoidHom γ : O'ˣ) : O') : B) = e (((γ : Oˣ) : O) : B) := hf _
  simp only [AlgHom.coe_comp, Function.comp_apply]
  rw [hγ s, map_mul, map_mul, h1, h2]; rfl

/-- **Embedding numbers are invariant under an automorphism of $B$:** $m(S, e(\mathcal O); e(\mathcal O)^\times) =
m(S, \mathcal O; \mathcal O^\times)$ for an $F$-algebra automorphism $e$ of $B$. -/
theorem embNum_map (e : B ≃ₐ[F] B) (O : Subalgebra R B) :
    embNum F S (O.map (e.restrictScalars R).toAlgHom) ⊤ = embNum F S O ⊤ := by
  set ε := e.restrictScalars R with hε
  let f : O ≃* O.map ε.toAlgHom := (Subalgebra.equivMapOfInjective O ε.toAlgHom ε.injective).toMulEquiv
  have hf : ∀ x : O, ((f x : O.map ε.toAlgHom) : B) = ε x := fun x => rfl
  have hf' : ∀ x : O.map ε.toAlgHom, ((f.symm x : O) : B) = ε.symm x := fun x => by
    apply ε.injective
    rw [AlgEquiv.apply_symm_apply, ← hf, MulEquiv.apply_symm_apply]
  have hc1 : ∀ ψ : S →ₐ[R] B, ε.toAlgHom.comp (ε.symm.toAlgHom.comp ψ) = ψ := fun ψ => by ext; simp
  have hc2 : ∀ ψ : S →ₐ[R] B, ε.symm.toAlgHom.comp (ε.toAlgHom.comp ψ) = ψ := fun ψ => by ext; simp
  let g : OptEmb R F S O ≃ OptEmb R F S (O.map ε.toAlgHom) :=
    { toFun := fun φ => ⟨ε.toAlgHom.comp φ.1, (isOptimalEmbedding_map_iff e O φ.1).2 φ.2⟩
      invFun := fun ψ => ⟨ε.symm.toAlgHom.comp ψ.1, (isOptimalEmbedding_map_iff e O _).1
        (by rw [hc1]; exact ψ.2)⟩
      left_inv := fun φ => Subtype.ext (hc2 _)
      right_inv := fun ψ => Subtype.ext (hc1 _) }
  refine (Nat.card_congr (Quotient.congr g (fun φ φ' => ?_))).symm
  show ConjBy (⊤ : Subgroup Oˣ) φ.1 φ'.1 ↔ ConjBy (⊤ : Subgroup (O.map ε.toAlgHom)ˣ) (ε.toAlgHom.comp φ.1)
    (ε.toAlgHom.comp φ'.1)
  refine ⟨conjBy_top_comp ε f hf, fun h => ?_⟩
  have := conjBy_top_comp ε.symm f.symm hf' h
  rwa [hc2, hc2] at this

end Conj

/-! ### The class of the unit ideal and the right order of its translates -/

section ClassOne

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- The unit ideal of $\mathcal O$, as a subset of $B$, is $\mathcal O$. -/
theorem idealSet_top : idealSet (⊤ : Ideal O) = (O : Set (QuatF F a b)) :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- The unit ideal is locally principal. -/
theorem isLocPrincipal_top : IsLocPrincipal (⊤ : Ideal O) := by
  intro v
  refine ⟨1, ?_⟩
  rw [Units.val_one, rTrans_one]
  ext y
  constructor
  · exact fun h => h.1
  · intro hy
    refine ⟨hy, ?_⟩
    rw [Gen.mem_localIdeal_iff]
    have : idealImage (v := v) (⊤ : Ideal O) = complHom v a b '' (O : Set (QuatF F a b)) := by
      ext z
      constructor
      · rintro ⟨x, -, rfl⟩; exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [this]; exact hy

/-- Local principality is invariant under $J \mapsto J\beta$. -/
theorem IsLocPrincipal.of_idealRel {J J' : Ideal O} (h : IdealRel J J') (hJ : IsLocPrincipal J) :
    IsLocPrincipal J' := by
  obtain ⟨β, hβ⟩ := h
  intro v
  obtain ⟨α, hα⟩ := hJ v
  refine ⟨α * Units.map (complHom v a b).toRingHom.toMonoidHom β, ?_⟩
  rw [idealSet_localIdeal_rTrans_nf v hβ, hα, rTrans_rTrans]
  rfl

/-- If $J \sim \mathcal O$ then $J = \mathcal O\beta$ for a unit $\beta$, $J \ne 0$, and $J$ is locally principal. -/
theorem exists_unit_of_idealRel_top {J : Ideal O} (h : IdealRel (⊤ : Ideal O) J) :
    ∃ β : (QuatF F a b)ˣ, idealSet J = rTrans (O : Set (QuatF F a b)) β := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, by rw [hβ, idealSet_top]⟩

theorem ne_bot_of_idealRel_top {J : Ideal O} (h : IdealRel (⊤ : Ideal O) J) : J ≠ ⊥ := by
  obtain ⟨β, hβ⟩ := exists_unit_of_idealRel_top h
  intro hJ
  have hmem : (β : QuatF F a b) ∈ idealSet J := by rw [hβ]; exact ⟨1, O.one_mem, one_mul _⟩
  obtain ⟨h1, h2⟩ := hmem
  rw [hJ, Ideal.mem_bot] at h2
  exact β.ne_zero (congrArg Subtype.val h2)

/-- **The right order of $\mathcal O\beta$** is the conjugate order $\beta^{-1}\mathcal O\beta$. -/
theorem rightOrder_eq_map {J : Ideal O} {β : (QuatF F a b)ˣ} (hβ : idealSet J = rTrans (O : Set (QuatF F a b)) β) :
    rightOrder J = O.map ((conjAlg (F := F) β).restrictScalars (𝓞 F)).toAlgHom := by
  ext x
  rw [Subalgebra.mem_map]
  constructor
  · intro hx
    have h1 : (β : QuatF F a b) ∈ idealSet J := by rw [hβ]; exact ⟨1, O.one_mem, one_mul _⟩
    have h2 := hx _ h1
    rw [hβ] at h2
    obtain ⟨z, hz, hzx⟩ := h2
    refine ⟨z, hz, ?_⟩
    show ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) * z * (β : QuatF F a b) = x
    have : z = (β : QuatF F a b) * x * ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) := by
      rw [← hzx]; simp [mul_assoc]
    rw [this]; simp [mul_assoc]
  · rintro ⟨o, ho, rfl⟩ y hy
    rw [hβ] at hy ⊢
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z * o, O.mul_mem hz ho, ?_⟩
    show z * o * (β : QuatF F a b) = z * (β : QuatF F a b) * (((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) * o * β)
    simp [mul_assoc]

end ClassOne

/-! ### Corollary 30.4.17 -/

section Cor

variable {F : Type} [Field F] [NumberField F]

/-- **Embedding numbers when $\#\operatorname{Cls}\mathcal O = 1$** (Voight 2021, Corollary 30.4.17): if $\mathcal O \subseteq
(a, b)_F$ is an order with $\#\operatorname{Cls}\mathcal O = 1$ and $S$ is a quadratic $\mathbb Z_F$-order that is a domain and
embeds in $B$, then
$$m(S, \mathcal O; \mathcal O^\times) = h(S)\prod_{\mathfrak p} m(S_{\mathfrak p}, \mathcal O_{\mathfrak p};
\mathcal O_{\mathfrak p}^\times).$$
**Proved conditional on** the trace formula `Wave4.TraceFormulaEmb F` (Theorem 30.4.7). The proof: the class of the unit
ideal lies in $\operatorname{Cls}\mathcal O$, hence is the unique class, and the right order of its representative
$J = \mathcal O\beta$ is $\beta^{-1}\mathcal O\beta$, which has the same embedding number as $\mathcal O$. -/
@[kb "voight2021" "Corollary 30.4.17, p. 550"]
theorem embNum_eq_of_clsNum_eq_one (hT : TraceFormulaEmb F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Finite (𝓞 F) S] (hS : Module.finrank (𝓞 F) S = 2)
    (hemb : ∃ φ : S →ₐ[𝓞 F] QuatF F a b, Function.Injective φ) (h1 : clsNum O = 1) :
    embNum F S O ⊤ = Nat.card (ClassGroup S) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S) (localOrder (v := v) a b O) ⊤ := by
  have h := hT a b ha hb O hO S hS hemb
  have hrel : IdealRel (⊤ : Ideal O) (Quotient.mk (idealSetoid O) (⊤ : Ideal O)).out :=
    (Quotient.mk_out (s := idealSetoid O) (⊤ : Ideal O)).symm
  let c₀ : ClsO O := ⟨Quotient.mk (idealSetoid O) (⊤ : Ideal O), ne_bot_of_idealRel_top hrel,
    IsLocPrincipal.of_idealRel hrel isLocPrincipal_top⟩
  have hsub : Subsingleton (ClsO O) := (Nat.card_eq_one_iff_unique.1 h1).1
  rw [finsum_eq_single _ c₀ (fun c hc => absurd (Subsingleton.elim c c₀) hc)] at h
  rw [← h]
  obtain ⟨β, hβ⟩ := exists_unit_of_idealRel_top hrel
  show embNum F S O ⊤ = embNum F S (rightOrder (Quotient.mk (idealSetoid O) (⊤ : Ideal O)).out) ⊤
  rw [rightOrder_eq_map hβ, embNum_map]

end Cor


end QuadFormsKB.Voight.Wave7
