/-
# Forms over $\mathcal O_F$: The genus of a form, and the bridge to $F = \mathbb Q$

**Layer:** forms `Q : QuadForm (𝓞 F) n` (a free lattice $\mathcal O_F^n$ with a chosen basis). The genus of a *form* compares
two forms locally everywhere, over every completion $\mathfrak o_\mathfrak p$ and every real place; the genus of
*lattices in one space* (`SameGenus`, `Lattices/Genus.lean`) needs no archimedean condition.

**Defines** `FormSameGenus Q Q'`: $Q \cong Q'$ over $\mathfrak o_\mathfrak p$ (by $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$) for every
finite prime $\mathfrak p$, and over $\mathbb R$ (by $\mathrm{GL}_n(\mathbb R)$) for every real embedding
$\sigma : F \to \mathbb R$. Complex places impose no condition on forms that are already locally equivalent at one
finite prime (both are then nondegenerate or both degenerate of the same rank, and over $\mathbb C$ such forms are
equivalent), so they are omitted.

**Proves**
* `isometricGL_map_ringEquiv`: equivalence of forms transports along ring isomorphisms;
* `formSameGenus_rat_iff`: for $F = \mathbb Q$ and integral forms $Q, Q'$ over $\mathbb Z$, `FormSameGenus` of their images
  over $\mathcal O_{\mathbb Q} = \mathbb Z$ is exactly the existing `Siegel.SameGenus Q Q'` (equivalence over every
  $\mathbb Z_p$ and over $\mathbb R$), via Mathlib's $\mathfrak o_{\mathfrak p} \cong \mathbb Z_p$ for $\mathbb Q$.
-/
import QuadFormsKB.Lattices.Basic
import QuadFormsKB.Siegel.Genus

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### Transport of equivalence along ring maps -/

theorem QuadForm.map_map {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (Q : QuadForm A n) : (Q.map f).map g = Q.map (g.comp f) := by
  ext i j; simp [QuadForm.map]

theorem QuadForm.map_id' {A : Type*} [CommRing A] (Q : QuadForm A n) : Q.map (RingHom.id A) = Q := by
  ext i j; simp [QuadForm.map]

/-- **Equivalence transports along a ring isomorphism** $\varphi : A \cong B$: if $Q(g\vec x) = Q'(\vec x)$ on $A^n$ then
$(\varphi Q)(\varphi(g)\vec y) = (\varphi Q')(\vec y)$ on $B^n$. -/
theorem IsometricGL.map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B)
    {Q Q' : QuadForm A n} (h : Siegel.IsometricGL Q Q') :
    Siegel.IsometricGL (Q.map (φ : A →+* B)) (Q'.map (φ : A →+* B)) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨GeneralLinearGroup.map (φ : A →+* B) g, fun y => ?_⟩
  have hy : y = fun i => φ ((fun i => φ.symm (y i)) i) := by funext i; simp
  rw [hy]
  have e : (GeneralLinearGroup.map (φ : A →+* B) g).val *ᵥ (fun i => φ ((fun i => φ.symm (y i)) i)) =
      fun i => φ ((g.val *ᵥ fun i => φ.symm (y i)) i) := by
    funext i
    exact (RingHom.map_mulVec (φ : A →+* B) g.val _ i).symm
  rw [e]
  exact (eval_map_comp (φ : A →+* B) Q _).trans
    ((congrArg φ (hg _)).trans (eval_map_comp (φ : A →+* B) Q' _).symm)

theorem isometricGL_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (Q Q' : QuadForm A n) :
    Siegel.IsometricGL (Q.map (φ : A →+* B)) (Q'.map (φ : A →+* B)) ↔ Siegel.IsometricGL Q Q' := by
  refine ⟨fun h => ?_, IsometricGL.map_ringEquiv φ⟩
  have := IsometricGL.map_ringEquiv φ.symm h
  have e : ((φ.symm : B →+* A).comp (φ : A →+* B)) = RingHom.id A := by ext; simp
  rwa [QuadForm.map_map, QuadForm.map_map, e, QuadForm.map_id', QuadForm.map_id'] at this

/-! ### The genus of a form over $\mathcal O_F$ -/

variable {F : Type*} [Field F] [NumberField F]

/-- **Forms in the same genus** over $\mathcal O_F$: $Q \cong Q'$ over the completion $\mathfrak o_\mathfrak p$ (by an element
of $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$) for every finite prime $\mathfrak p$, and over $\mathbb R$ for every real embedding
$\sigma : F \to \mathbb R$ (cf. O'Meara §102A, p. 297, where the genus is defined for lattices on one space $V$, so no condition at the real places is needed). For $F = \mathbb Q$ this is `Siegel.SameGenus`
(`formSameGenus_rat_iff`). -/
@[kb "omeara1963" "§102A, p. 297 (genus); §82B, 82:1, p. 222 (free lattices and matrices)"]
def FormSameGenus (Q Q' : QuadForm (𝓞 F) n) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F),
      Siegel.IsometricGL (Q.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))
        (Q'.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))) ∧
    ∀ σ : F →+* ℝ, Siegel.IsometricGL (Q.map (σ.comp (algebraMap (𝓞 F) F)))
      (Q'.map (σ.comp (algebraMap (𝓞 F) F)))

theorem FormSameGenus.refl (Q : QuadForm (𝓞 F) n) : FormSameGenus Q Q :=
  ⟨fun _ => Siegel.IsometricGL.refl _, fun _ => Siegel.IsometricGL.refl _⟩

theorem FormSameGenus.symm {Q Q' : QuadForm (𝓞 F) n} (h : FormSameGenus Q Q') : FormSameGenus Q' Q :=
  ⟨fun v => (h.1 v).symm, fun σ => (h.2 σ).symm⟩

theorem FormSameGenus.trans {Q Q' Q'' : QuadForm (𝓞 F) n} (h : FormSameGenus Q Q')
    (h' : FormSameGenus Q' Q'') : FormSameGenus Q Q'' :=
  ⟨fun v => (h.1 v).trans (h'.1 v), fun σ => (h.2 σ).trans (h'.2 σ)⟩

/-! ### The case $F = \mathbb Q$ -/

/-- The ring map $\mathbb Z \to \mathcal O_{\mathbb Q}$ (an isomorphism, `Rat.ringOfIntegersEquiv`). -/
abbrev toOQ : ℤ →+* 𝓞 ℚ := algebraMap ℤ (𝓞 ℚ)

/-- **The genus over $\mathcal O_{\mathbb Q}$ is the genus over $\mathbb Z$:** for integral forms $Q, Q'$,
`FormSameGenus` of their images in `QuadForm (𝓞 ℚ) n` holds iff `Siegel.SameGenus Q Q'` (equivalence over every
$\mathbb Z_p$ and over $\mathbb R$). Uses Mathlib's isomorphisms $\mathfrak o_{\mathfrak p} \cong \mathbb Z_p$
(`PadicInt.adicCompletionIntegersEquiv`, `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`). -/
@[kb "omeara1963" "§102A, p. 297"]
theorem formSameGenus_rat_iff (Q Q' : QuadForm ℤ n) :
    FormSameGenus (Q.map toOQ) (Q'.map toOQ) ↔ Siegel.SameGenus Q Q' := by
  constructor
  · rintro ⟨hfin, hinf⟩
    refine ⟨fun p hp => ?_, ?_⟩
    · let P : Nat.Primes := ⟨p, hp.out⟩
      let φ := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P).toAlgEquiv.toRingEquiv
      have h := IsometricGL.map_ringEquiv φ.symm
        (hfin (Rat.HeightOneSpectrum.primesEquiv.symm P))
      rwa [QuadForm.map_map, QuadForm.map_map, QuadForm.map_map, QuadForm.map_map,
        RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom ℤ_[p])] at h
    · have h := hinf (Rat.castHom ℝ)
      rwa [QuadForm.map_map, QuadForm.map_map,
        RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom ℝ)] at h
  · rintro ⟨hfin, hinf⟩
    refine ⟨fun v => ?_, fun σ => ?_⟩
    · have : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
      let φ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
      have h := hfin (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
      rw [← isometricGL_map_ringEquiv φ.symm, QuadForm.map_map, QuadForm.map_map] at h
      rw [QuadForm.map_map, QuadForm.map_map, RingHom.ext_int
        ((algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)).comp toOQ)
        (φ.symm.toRingHom.comp (Int.castRingHom _))]
      exact h
    · rwa [QuadForm.map_map, QuadForm.map_map,
        RingHom.ext_int (RingHom.comp _ toOQ) (Int.castRingHom ℝ)]

end QuadFormsKB.Lattices
