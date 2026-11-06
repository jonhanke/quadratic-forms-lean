/-
# O'Meara 93:28, sufficiency: the spaces $FK_1$ from conditions (i)–(iii)

**Setting** (as in `Sec93E.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275: "condition (ii) holds.
Hence in this case we have $FL_1 \cong FK_1$")
* `isometryEquiv_of_rep_disc`: nonsingular spaces $U_1$, $U_2$ of the same dimension and the same discriminant with
  $U_1 \to U_2 \perp \langle c\rangle$ ($c \ne 0$) are isometric (Witt);
* `spanIso_of_spanRepresents`: the same for the spaces $FM$, $FN$ of regular lattices;
* `exists_lagrangian_of_spanIso`: a hyperbolic $FM$ (a totally isotropic subspace of half the dimension) makes
  every isometric $FN$ hyperbolic.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffResplit
import QuadFormsKB.Literature.OMeara.Sec93FCoreHyp

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreSpace

open RepTransfer NecBlocks Resplit
open QuadFormsKB.OMeara.D18 (subQ spanF)

section Abstract

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {U₁ U₂ : Type*} [AddCommGroup U₁] [Module F U₁] [AddCommGroup U₂] [Module F U₂]

/-- **Witt's theorem with discriminants** (O'Meara 1963, §42F, 42:17, and §93F, p. 274): let $U_1$, $U_2$ be
nonsingular quadratic spaces with bases $e$, $e'$ of the same length whose discriminants differ by a square,
$d(e) = r^2 d(e')$, and let $U_1 \to U_2 \perp \langle c\rangle$ with $c \ne 0$. Then $U_1 \cong U_2$. (The orthogonal
complement of the image of $U_1$ is a line $\langle a_1\rangle$ with $a_1 d(e) = s^2 c\,d(e')$, so
$\langle a_1\rangle \cong \langle c\rangle$, and $\langle c\rangle$ cancels.) -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (FL₁ ≅ FK₁ from condition (ii); Witt 42:17)"]
theorem isometryEquiv_of_rep_disc [FiniteDimensional F U₁] [FiniteDimensional F U₂] {Q₁ : QuadraticForm F U₁}
    {Q₂ : QuadraticForm F U₂} (h₁ : (polarBilin Q₁).Nondegenerate) (h₂ : (polarBilin Q₂).Nondegenerate) {c : F}
    (hc : c ≠ 0) {n : ℕ} (e : Basis (Fin n) F U₁) (e' : Basis (Fin n) F U₂)
    (hd' : (gram Q₂ fun i => e' i).det ≠ 0) {r : F}
    (hr : (gram Q₁ fun i => e i).det = r ^ 2 * (gram Q₂ fun i => e' i).det)
    (h : Rep Q₁ (Q₂.prod (c • (QuadraticMap.sq : QuadraticForm F F)))) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨a₁, s, hs, ha₁, hdisc, ⟨eA⟩⟩ := rep_complement_disc h₁ hc e e' hd' h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [hr] at hdisc
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero] at hdisc
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hs) hc) hd' hdisc.symm
  have ha : a₁ = (s / r) ^ 2 * c := by
    rw [hr] at hdisc
    field_simp
    apply mul_right_cancel₀ hd'
    linear_combination hdisc
  -- `⟨c⟩ ≅ ⟨a₁⟩` by `t ↦ (r / s) t`
  have hrs : r / s ≠ 0 := div_ne_zero hr0 hs
  let eL : F ≃ₗ[F] F := LinearEquiv.smulOfNeZero F F (r / s) hrs
  let eC : (c • (QuadraticMap.sq : QuadraticForm F F)).IsometryEquiv
      (a₁ • (QuadraticMap.sq : QuadraticForm F F)) :=
    { eL with
      map_app' := fun t => by
        have : (eL : F →ₗ[F] F).toFun t = r / s * t := rfl
        simp only [QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul, this]
        rw [ha]
        field_simp }
  let e₁ := (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl Q₁) eC).trans eA
  have hrep : Rep (Q₁.prod (c • (QuadraticMap.sq : QuadraticForm F F)))
      (Q₂.prod (c • (QuadraticMap.sq : QuadraticForm F F))) :=
    ⟨e₁.toLinearEquiv.toLinearMap, e₁.toLinearEquiv.injective, fun x => e₁.map_app x⟩
  obtain ⟨f, hf, hQ⟩ := Rep.cancel_right h₂ (nondegenerate_smul_sq hc) hrep
  have hdim : finrank F U₁ = finrank F U₂ := by
    rw [Module.finrank_eq_card_basis e, Module.finrank_eq_card_basis e']
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  exact ⟨{ LinearEquiv.ofBijective f ⟨hf, hsurj⟩ with map_app' := hQ }⟩

end Abstract

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$FM \cong FN$ from a representation and equal discriminants** (O'Meara 1963, §93F, p. 274): for regular
lattices $M$, $N$ with bases $b$, $b'$ of the same length with $d(b) = r^2 d(b')$, and $c \ne 0$,
$FM \to FN \perp \langle c\rangle$ implies $FM \cong FN$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274 (FL₁ ≅ FK₁ from condition (ii))"]
theorem spanIso_of_spanRepresents {M N : Submodule R V} {n : ℕ} (b : Basis (Fin n) R M) (b' : Basis (Fin n) R N)
    (hMreg : IsRegular Q M) (hNreg : IsRegular Q N) {r : F}
    (hr : (gram Q fun i => (b i : V)).det = r ^ 2 * (gram Q fun i => (b' i : V)).det) {c : F} (hc : c ≠ 0)
    (h : SpanRepresents Q M N c) : Nonempty ((subQ Q M).IsometryEquiv (subQ Q N)) := by
  have hdM := Transfer28.det_gram_ne_zero_of_isRegular Q hMreg b
  have hdN := Transfer28.det_gram_ne_zero_of_isRegular Q hNreg b'
  obtain ⟨e, he⟩ := exists_spanBasis Q b hdM
  obtain ⟨e', he'⟩ := exists_spanBasis Q b' hdN
  rw [spanRepresents_iff_rep] at h
  refine isometryEquiv_of_rep_disc (nondegenerate_subQ Q hMreg) (nondegenerate_subQ Q hNreg) hc e e'
    (by rw [he']; exact hdN) (r := r) (by rw [he, he']; exact hr) h

/-- **Hyperbolicity passes along an isometry $FM \cong FN$**: if $FM$ contains a totally isotropic subspace $T$ with
$\operatorname{rank} M \le 2\dim T$ and $\operatorname{rank} M = \operatorname{rank} N$, so does $FN$. -/
theorem exists_lagrangian_of_spanIso {M N : Submodule R V} (e : (subQ Q M).IsometryEquiv (subQ Q N))
    (hrk : finrank R M = finrank R N)
    (hT : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (M : Set V)) ∧
      finrank R M ≤ 2 * finrank F T) :
    ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (N : Set V)) ∧
      finrank R N ≤ 2 * finrank F T := by
  obtain ⟨T, hTiso, hTM, hTdim⟩ := hT
  set T₀ : Submodule F (spanF F M) := T.comap (spanF F M).subtype with hT₀
  set φ : spanF F M →ₗ[F] V := (spanF F N).subtype ∘ₗ e.toLinearEquiv.toLinearMap with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.toLinearEquiv.injective
  refine ⟨T₀.map φ, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : Q (φ y) = subQ Q N (e y) := rfl
    rw [h1, e.map_app]
    exact hTiso _ hy
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · have hT₀ : finrank F T₀ = finrank F T := by
      have hle : T ≤ spanF F M := fun x hx => hTM x hx
      exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    have hmap : finrank F (T₀.map φ) = finrank F T₀ :=
      (Submodule.equivMapOfInjective φ hφinj T₀).finrank_eq.symm
    rw [← hrk, hmap, hT₀]
    exact hTdim

end Lattice

section Final

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]

/-- **`SuffCore` from `SuffCoreHyp`** (O'Meara 1963, §93F, p. 273): the re-splitting invariance of (i)–(iii) is
`Resplit.cond93_resplit`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 3–8, pp. 273–276"]
theorem suffCore_of_hyp [CharZero F] (hHil : PadicClass.LocalHilbertField F) (h : CoreHyp.SuffCoreHyp.{u, v} R F) :
    Suff28.SuffCore.{u, v} R F :=
  CoreHyp.suffCore_of_hyp_of_resplit (fun Q h2p hQ _ _ _ _ _ _ _ _ _ hL hK hK' hS hC =>
    Resplit.cond93_resplit Q hHil h2p hQ hL hK hK' hS hC) h

variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **Theorem 93:28 from the reduced core** (O'Meara 1963, §93F, pp. 267–276): over a dyadic field with
`LocalHilbertField`, the named statement `SuffCoreHyp` (steps 4–8 of the sufficiency, in the form "$K$ has a saturated
splitting with $FK_1'$ hyperbolic") implies `DyadicClassification`. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276"]
theorem dyadicClassification_of_hyp (Q : QuadraticForm F V)
    (hHil : ∀ [CharZero F], PadicClass.LocalHilbertField F)
    (h : ∀ [CharZero F], CoreHyp.SuffCoreHyp.{u, v} R F) : DyadicClassification R Q :=
  Main28.dyadicClassification_of_core Q hHil (fun [CharZero F] => suffCore_of_hyp hHil h)

end Final

section NumberField

open NumberField IsDedekindDomain

universe v

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field, from the reduced core** (O'Meara 1963,
§93F, pp. 267–276): only the named statement `SuffCoreHyp` for $F_\mathfrak p$ is assumed. -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field)"]
theorem dyadicClassification_hyp_nf
    (h : CoreHyp.SuffCoreHyp.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_of_hyp Q (HasseIsoNF.localHilbertField_adicCompletion v) h

end NumberField

end QuadFormsKB.OMeara.CoreSpace
