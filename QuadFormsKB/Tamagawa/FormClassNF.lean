/-
# Classes of lattices in the genus of $\mathcal O_F^n$ are classes of forms over $\mathcal O_F$, every number field

**Layer.** $F$ a totally real number field, **any class number**; $Q_0$ a totally positive definite form over $\mathcal O_F$ in
$n$ variables; $V = (F^n, Q_0)$, $L = \mathcal O_F^n$. Route W states Siegel's formula with the *lattice* objects: the
$O(V)(F)$-classes of lattices in the genus of $L$ (`Lattices.genusClasses`), $|O(M)|$ (`LatClass.autCard`) and $r_M(m)$
(`LatClass.repCount`). This file identifies them with the classical *forms* objects over $\mathcal O_F$:

| forms over $\mathcal O_F$ | lattices in $(F^n, Q_0)$ | Lean |
|---|---|---|
| $\mathrm{GL}_n(\mathcal O_F)$-classes of totally positive definite $Q'$ with `FormSameGenus Q₀ Q'` (`formGenusClasses`) | classes in $\mathrm{gen}(\mathcal O_F^n)$ | `bijOn_formClass` |
| $|\mathrm{Aut}_{\mathrm{GL}_n(\mathcal O_F)}(Q')|$ (`FormClass.autCard`) | $|O(M)|$ | `autCard_eq_formClass` |
| $r_{Q'}(m) = \#\{x \in \mathcal O_F^n : Q'(x) = m\}$ (`FormClass.repNum`) | $r_M(m)$ | `repCount_eq_formClass` |
| `formMass`, `formRepMass` | `Lattices.mass`, `repMass` | `formMass_eq`, `formRepMass_eq` |

**Why it holds for every class number.** (1) Every lattice in the genus of $\mathcal O_F^n$ is free, $M = \gamma\mathcal O_F^n$
(`HilbertModular.genusFree_formF`, Steinitz: the Steinitz class is a genus invariant, as $M_\mathfrak p = \sigma_\mathfrak pL_\mathfrak p$ with
$\det\sigma_\mathfrak p = \pm1$; O'Meara 81:5, §82). Its Gram form $Q_\gamma$ (`gramZ`) is a form over $\mathcal O_F$ in the genus of $Q_0$
(`formSameGenus_gramZ`); isometric free lattices have $\mathrm{GL}_n(\mathcal O_F)$-equivalent Gram forms and conversely
(`isIsometric_latOf_iff`). (2) Conversely a form $Q'$ in the genus of $Q_0$ is $F$-equivalent to $Q_0$ (**Hasse–Minkowski over $F$
for isometry**, `isometricIn_of_everywhere_nf`, proved here from `represents_iff_everywhere_nf` and Witt cancellation as in
Serre IV §3.3, Thm 9), so $Q' = Q_\gamma$ for a lattice $\gamma\mathcal O_F^n$ in the genus (`sameGenus_latOf_iff`).

*Convention.* `formGenusClasses Q₀` asks for $Q'$ totally positive definite in addition to `FormSameGenus Q₀ Q'`. (This is implied
by the real places of `FormSameGenus`; it is kept explicit so that the nondegeneracy needed by Hasse–Minkowski is immediate.)
Classes are $\mathrm{GL}_n$ (not $\mathrm{SL}_n$) classes; $\mathrm{Aut}$ includes improper automorphisms, matching $O(M)$.

Sources: Steinitz, Math. Ann. 71 (1911); O'Meara 1963, 81:5, §82, §102, 66:3 [unverified]; Serre 1973, IV §3.3, Thm 9.
-/
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.HilbertModular.SteinitzGenus
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain

open NumberField Matrix IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FormClassNF

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular

variable {n : ℕ}

/-! ### Classes of forms over a commutative ring -/

section Ring

variable {A : Type*} [CommRing A]

/-- Conjugation $h \mapsto ghg^{-1}$ identifies $\mathrm{Aut}(Q')$ with $\mathrm{Aut}(Q)$ when $Q(gx) = Q'(x)$ (any commutative ring;
the $\mathbb Z$ case is `Siegel.autEquivOfIsometry`). -/
def autEquivOfIsometry {Q Q' : QuadForm A n} (g : GL (Fin n) A)
    (hg : ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x) : Siegel.aut Q' ≃ Siegel.aut Q where
  toFun h := ⟨g * h.1 * g⁻¹, fun x => by
    have hh := h.2
    have hinv : ∀ y, Q.eval y = Q'.eval ((g⁻¹).val *ᵥ y) := fun y => by
      rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hg, hh (((g⁻¹).val *ᵥ x)), hinv x]⟩
  invFun h := ⟨g⁻¹ * h.1 * g, fun x => by
    have hh := h.2
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      hh (g.val *ᵥ x), hg]⟩
  left_inv h := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]

theorem card_aut_eq {Q Q' : QuadForm A n} (h : Siegel.IsometricGL Q Q') :
    Nat.card (Siegel.aut Q) = Nat.card (Siegel.aut Q') := by
  obtain ⟨g, hg⟩ := h
  exact (Nat.card_congr (autEquivOfIsometry g hg)).symm

/-- **The representation number** $r_Q(m) = \#\{x \in A^n : Q(x) = m\}$ (`Nat.card`). -/
@[kb "hanke2004" "§2, r_Q(m), p. 357 (over 𝓞_F)"]
def repNum (Q : QuadForm A n) (m : A) : ℕ := Nat.card {x : Fin n → A // Q.eval x = m}

theorem repNum_eq {Q Q' : QuadForm A n} (h : Siegel.IsometricGL Q Q') (m : A) : repNum Q m = repNum Q' m := by
  obtain ⟨g, hg⟩ := h
  have hinv : ∀ y, Q.eval y = Q'.eval ((g⁻¹).val *ᵥ y) := fun y => by
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine Nat.card_congr
    { toFun := fun x => ⟨(g⁻¹).val *ᵥ x.1, by rw [← hinv, x.2]⟩
      invFun := fun y => ⟨g.val *ᵥ y.1, by rw [hg, y.2]⟩
      left_inv := fun x => by
        ext1; simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      right_inv := fun y => by
        ext1; simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] }

omit [CommRing A] in
/-- $\mathrm{GL}_n(A)$-equivalence of forms over $A$ as a setoid. -/
def formSetoid (A : Type*) [CommRing A] (n : ℕ) : Setoid (QuadForm A n) where
  r := Siegel.IsometricGL
  iseqv := ⟨Siegel.IsometricGL.refl, Siegel.IsometricGL.symm, Siegel.IsometricGL.trans⟩

omit [CommRing A] in
/-- **Classes of forms** over $A$: $\mathrm{GL}_n(A)$-equivalence classes (for $A = \mathbb Z$ this is `Siegel.QClass`). -/
abbrev FormClass (A : Type*) [CommRing A] (n : ℕ) := Quotient (formSetoid A n)

/-- $|\mathrm{Aut}(Q')|$ of a class (well defined by `card_aut_eq`). -/
def FormClass.autCard (c : FormClass A n) : ℕ :=
  Quotient.lift (s := formSetoid A n) (fun Q => Nat.card (Siegel.aut Q)) (fun _ _ h => card_aut_eq h) c

/-- $r_{Q'}(m)$ of a class (well defined by `repNum_eq`). -/
def FormClass.repNum (c : FormClass A n) (m : A) : ℕ :=
  Quotient.lift (s := formSetoid A n) (fun Q => FormClassNF.repNum Q m) (fun _ _ h => repNum_eq h m) c

@[simp] theorem FormClass.autCard_mk (Q : QuadForm A n) :
    FormClass.autCard (Quotient.mk (formSetoid A n) Q) = Nat.card (Siegel.aut Q) := rfl

@[simp] theorem FormClass.repNum_mk (Q : QuadForm A n) (m : A) :
    FormClass.repNum (Quotient.mk (formSetoid A n) Q) m = FormClassNF.repNum Q m := rfl

end Ring

/-! ### The genus of a form over $\mathcal O_F$ as a set of classes -/

variable {F : Type} [Field F] [NumberField F]

/-- **The classes of forms in the genus of $Q_0$** over $\mathcal O_F$: $\mathrm{GL}_n(\mathcal O_F)$-classes of totally positive definite
forms $Q'$ over $\mathcal O_F$ with $Q' \cong Q_0$ over every $\mathfrak o_\mathfrak p$ and every real place (`FormSameGenus`). -/
@[kb "omeara1963" "§102 (classes in the genus of a form) [unverified]"]
def formGenusClasses (Q₀ : QuadForm (𝓞 F) n) : Set (FormClass (𝓞 F) n) :=
  {c | ∃ Q' : QuadForm (𝓞 F) n, Quotient.mk _ Q' = c ∧ FormSameGenus Q₀ Q' ∧ IsTotallyPosDef (formF Q')}

/-- **The mass of the genus of a form** $Q_0$ over $\mathcal O_F$: $\sum_{[Q']}1/|\mathrm{Aut}(Q')|$ (for $F = \mathbb Q$: `Siegel.mass`). -/
@[kb "siegel1935" "mass of a genus of forms, over F [unverified]"]
def formMass (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  ∑ᶠ c ∈ formGenusClasses Q₀, ((FormClass.autCard c : ℝ))⁻¹

/-- **The weighted representation number of the genus of a form**: $\sum_{[Q']}r_{Q'}(m)/|\mathrm{Aut}(Q')|$ (for $F = \mathbb Q$:
`Siegel.genusRepSum`). -/
@[kb "siegel1935" "Σ r_{Q'}(m)/|Aut Q'| over the genus, over F [unverified]"]
def formRepMass (Q₀ : QuadForm (𝓞 F) n) (m : 𝓞 F) : ℝ :=
  ∑ᶠ c ∈ formGenusClasses Q₀, (FormClass.repNum c m : ℝ) / FormClass.autCard c

/-! ### Hasse–Minkowski over $F$ for isometry -/

theorem everywhere_mono {P P' : (K : Type) → [Field K] → [Algebra F K] → Prop}
    (H : ∀ (K : Type) [Field K] [Algebra F K], P K → P' K) (h : NFPlace.Everywhere P) :
    NFPlace.Everywhere P' := by
  intro v
  cases v with
  | infinite w => exact H _ (h (.infinite w))
  | finite v => exact H _ (h (.finite v))

/-- **Hasse–Minkowski for isometry over a number field** (O'Meara 66:4; Serre IV §3.3, Thm 9 over $\mathbb Q$): two nondegenerate forms
over $F$ that are isometric over every completion $F_v$ are isometric over $F$. *Proof* as `isometric_of_everywhere` over $\mathbb Q$:
split off a value $b$ of $R$ (represented by $Q$ everywhere, hence over $F$, `represents_iff_everywhere_nf`), cancel it at every place
(Witt, `isometricIn_of_diag_cons`) and induct. -/
@[kb "omeara1963" "66:4 [unverified]"]
theorem isometricIn_of_everywhere_nf : ∀ {n : ℕ} (Q R : QuadForm F n), Q.Nondegenerate → R.Nondegenerate →
    NFPlace.Everywhere (F := F) (fun K _ _ => Q.IsometricIn K R) → Q.IsometricIn F R
  | 0, Q, R, _, _, _ => ⟨1, by simp, fun x => by simp [QuadForm.evalIn]⟩
  | m + 1, Q, R, hQ, hR, h => by
    obtain ⟨β, hβ, hRβ⟩ := FieldGen.exists_isometric_diag R hR
    have hrep : ∀ (K : Type) [Field K] [Algebra F K], (QuadForm.diag β).RepresentsIn K (β 0) := by
      intro K _ _
      refine ⟨Pi.single 0 1, ?_⟩
      rw [QuadForm.evalIn_diag, Finset.sum_eq_single 0]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    have hQb : Q.RepresentsIn F (β 0) := by
      rw [represents_iff_everywhere_nf Q hQ _ (hβ 0)]
      exact everywhere_mono (fun K _ _ hK => QuadForm.representsIn_of_isometricIn K
        (QuadForm.isometricIn_trans K hK (FieldGen.isometricIn_of_base K hRβ)) (hrep K)) h
    obtain ⟨α, hα, hQα⟩ := QuadForm.exists_isometric_diag_cons hQ (hβ 0) hQb
    have hβc : Fin.cons (β 0) (Fin.tail β) = β := Fin.cons_self_tail β
    have hloc : NFPlace.Everywhere (F := F) fun K _ _ =>
        (QuadForm.diag α).IsometricIn K (QuadForm.diag (Fin.tail β)) :=
      everywhere_mono (fun K _ _ hK => by
        refine QuadForm.isometricIn_of_diag_cons K (hβ 0) hα ?_
        rw [hβc]
        exact QuadForm.isometricIn_trans K
          (QuadForm.isometricIn_symm K (FieldGen.isometricIn_of_base K hQα))
          (QuadForm.isometricIn_trans K hK (FieldGen.isometricIn_of_base K hRβ))) h
    have ih := isometricIn_of_everywhere_nf _ _ (QuadForm.nondegenerate_diag hα)
      (QuadForm.nondegenerate_diag (a := Fin.tail β) fun i => hβ i.succ) hloc
    have := QuadForm.isometricIn_diag_cons_of F (β 0) ih
    rw [hβc] at this
    exact QuadForm.isometricIn_trans F hQα
      (QuadForm.isometricIn_trans F this (QuadForm.isometricIn_symm F hRβ))

/-- $\mathrm{GL}_n(K)$-equivalence of the base changes of two forms over $\mathcal O_F$ to a field $K \supseteq F$ is isometry over $K$. -/
theorem isometricIn_formF_of_isometricGL (K : Type) [Field K] [Algebra F K] {Q Q' : QuadForm (𝓞 F) n}
    (h : Siegel.IsometricGL (Q.map ((algebraMap F K).comp (algebraMap (𝓞 F) F)))
      (Q'.map ((algebraMap F K).comp (algebraMap (𝓞 F) F)))) :
    (formF Q).IsometricIn K (formF Q') := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
  rw [evalIn_eq_eval_map, evalIn_eq_eval_map, formF, formF, QuadForm.map_map, QuadForm.map_map]
  exact hg x

/-- **Forms in one genus over $\mathcal O_F$ are isometric over every completion** ($F$ totally real, so every infinite place is real). -/
theorem everywhere_isometricIn_of_formSameGenus [IsTotallyReal F] {Q Q' : QuadForm (𝓞 F) n}
    (h : FormSameGenus Q Q') :
    NFPlace.Everywhere (F := F) (fun K _ _ => (formF Q).IsometricIn K (formF Q')) := by
  intro v
  cases v with
  | infinite w =>
    let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
    have h1 := IsometricGL.map_ringEquiv ψ.symm (h.2 ((ψ : w.Completion →+* ℝ).comp (algebraMap F w.Completion)))
    rw [QuadForm.map_map, QuadForm.map_map] at h1
    have e : (ψ.symm : ℝ →+* w.Completion).comp
        (((ψ : w.Completion →+* ℝ).comp (algebraMap F w.Completion)).comp (algebraMap (𝓞 F) F)) =
        (algebraMap F w.Completion).comp (algebraMap (𝓞 F) F) := by
      ext x; simp
    rw [e] at h1
    exact isometricIn_formF_of_isometricGL _ h1
  | finite v =>
    have h1 := RatBridge.isometricGL_map_hom (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (h.1 v)
    rw [QuadForm.map_map, QuadForm.map_map] at h1
    have e : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).comp
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) = (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F) := by
      ext x; rfl
    rw [e] at h1
    exact isometricIn_formF_of_isometricGL _ h1

/-- **Forms in one genus over $\mathcal O_F$ are equivalent over $F$** (Hasse–Minkowski over $F$). -/
theorem isometricIn_of_formSameGenus [IsTotallyReal F] {Q Q' : QuadForm (𝓞 F) n}
    (hQ : (formF Q).Nondegenerate) (hQ' : (formF Q').Nondegenerate) (h : FormSameGenus Q Q') :
    (formF Q).IsometricIn F (formF Q') :=
  isometricIn_of_everywhere_nf _ _ hQ hQ' (everywhere_isometricIn_of_formSameGenus h)

/-! ### The class bijection -/

section Classes

variable (Q₀ : QuadForm (𝓞 F) n)

open Classical in
/-- **The form of a lattice** $M$ in $(F^n, Q_0)$: the Gram form over $\mathcal O_F$ of a basis $\gamma$ of $M$ (`gramZ`); junk value $Q_0$
if $M$ is not free and integral (never the case in the genus of $\mathcal O_F^n$, `genusFree_formF`). -/
def latForm (M : Lat F n) : QuadForm (𝓞 F) n :=
  if h : ∃ γ : GL (Fin n) F, M.1 = latOf γ ∧ IsIntegral (formF Q₀) (latOf γ) then
    gramZ (formF Q₀) h.choose h.choose_spec.2 else Q₀

theorem latForm_isometricGL (M : Lat F n) (γ : GL (Fin n) F) (hM : M.1 = latOf γ)
    (h : IsIntegral (formF Q₀) (latOf γ)) : Siegel.IsometricGL (latForm Q₀ M) (gramZ (formF Q₀) γ h) := by
  have hex : ∃ γ : GL (Fin n) F, M.1 = latOf γ ∧ IsIntegral (formF Q₀) (latOf γ) := ⟨γ, hM, h⟩
  rw [latForm, dite_eq_left_of_eq_true (eq_true hex)]
  refine (isIsometric_latOf_iff (formF Q₀) γ _ h hex.choose_spec.2).mp ?_
  rw [← hM, ← hex.choose_spec.1]
  exact IsIsometric.refl _ _

theorem isTotallyPosDef_gramZ (hpd : IsTotallyPosDef (formF Q₀)) (γ : GL (Fin n) F)
    (h : IsIntegral (formF Q₀) (latOf γ)) : IsTotallyPosDef (formF (gramZ (formF Q₀) γ h)) := by
  intro y hy
  rw [formF, gramZ_map, eval_gramFormF_col]
  refine hpd _ fun h0 => hy ?_
  have := congrArg (fun w => (γ⁻¹).val *ᵥ w) h0
  simpa [mulVec_mulVec, ← Units.val_mul] using this

variable [IsTotallyReal F] {Q₀}

theorem exists_free_of_mem (hpd : IsTotallyPosDef (formF Q₀)) {c : LatClass (formF Q₀)}
    (hc : c ∈ genusClasses (formF Q₀) (stdLat F n)) :
    ∃ γ : GL (Fin n) F, c.out.1 = latOf γ ∧ IsIntegral (formF Q₀) (latOf γ) ∧
      SameGenus (formF Q₀) intVec (latOf γ) := by
  have hs := sameGenus_out hc
  obtain ⟨γ, hγ⟩ := genusFree_formF hpd c.out hs
  exact ⟨γ, hγ, hγ ▸ SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hs, hγ ▸ hs⟩

/-- **Every totally positive definite form in the genus of $Q_0$ is the Gram form of a lattice in the genus of $\mathcal O_F^n$** in
$(F^n, Q_0)$ (Hasse–Minkowski over $F$ gives $Q' = Q_0\circ\gamma$; then $\gamma\mathcal O_F^n$). -/
theorem exists_latOf_of_formSameGenus (hpd : IsTotallyPosDef (formF Q₀)) {Q' : QuadForm (𝓞 F) n}
    (hpd' : IsTotallyPosDef (formF Q')) (hg : FormSameGenus Q₀ Q') :
    ∃ (γ : GL (Fin n) F) (h : IsIntegral (formF Q₀) (latOf γ)),
      SameGenus (formF Q₀) intVec (latOf γ) ∧ gramZ (formF Q₀) γ h = Q' := by
  obtain ⟨P, hP, hPe⟩ := isometricIn_of_formSameGenus hpd.nondegenerate hpd'.nondegenerate hg
  set γ : GL (Fin n) F := ((Matrix.isUnit_iff_isUnit_det P).mpr hP).unit
  have hγP : γ.val = P := rfl
  have hval : ∀ x : Fin n → 𝓞 F,
      (formF Q₀).eval (γ.val *ᵥ intCoe x) = algebraMap (𝓞 F) F (Q'.eval x) := by
    intro x
    have := hPe (intCoe x)
    rw [evalIn_eq_eval_map, evalIn_eq_eval_map, Algebra.algebraMap_self, QuadForm.map_id',
      QuadForm.map_id'] at this
    rw [hγP, this, ← eval_map_comp]
  have hint : IsIntegral (formF Q₀) (latOf γ) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
    exact ⟨Q'.eval x, (hval x).symm⟩
  have hG : gramZ (formF Q₀) γ hint = Q' :=
    QuadForm.ext_eval fun x => IsFractionRing.injective (𝓞 F) F (by rw [algebraMap_eval_gramZ, hval])
  refine ⟨γ, hint, ?_, hG⟩
  have h1 := (sameGenus_latOf_iff (formF Q₀) 1 γ (isIntegral_latOf_one Q₀) hint).mpr (by
    rw [gramZ_one, hG]; exact hg)
  rwa [latOf_one] at h1

/-- **The class map** $\mathrm{cls}(M) \mapsto [\text{Gram form of } M]$ is a bijection from the classes of lattices in the genus of
$\mathcal O_F^n$ in $(F^n, Q_0)$ onto the $\mathrm{GL}_n(\mathcal O_F)$-classes of forms in the genus of $Q_0$, over every totally real
number field, any class number. -/
@[kb "omeara1963" "§§82, 102 (classes of lattices in gen(𝓞_F^n) = classes of forms; Steinitz) [unverified]"]
theorem bijOn_formClass (hpd : IsTotallyPosDef (formF Q₀)) :
    Set.BijOn (fun c : LatClass (formF Q₀) => (Quotient.mk (formSetoid (𝓞 F) n) (latForm Q₀ c.out)))
      (genusClasses (formF Q₀) (stdLat F n)) (formGenusClasses Q₀) := by
  refine ⟨fun c hc => ?_, fun c hc c' hc' hcc => ?_, fun d hd => ?_⟩
  · obtain ⟨γ, hγ, hi, hs⟩ := exists_free_of_mem hpd hc
    exact ⟨gramZ (formF Q₀) γ hi, Quotient.sound (latForm_isometricGL Q₀ _ γ hγ hi).symm,
      formSameGenus_gramZ Q₀ hs hi, isTotallyPosDef_gramZ Q₀ hpd γ hi⟩
  · obtain ⟨γ, hγ, hi, -⟩ := exists_free_of_mem hpd hc
    obtain ⟨γ', hγ', hi', -⟩ := exists_free_of_mem hpd hc'
    have h1 : Siegel.IsometricGL (latForm Q₀ c.out) (latForm Q₀ c'.out) := Quotient.exact hcc
    have h2 : Siegel.IsometricGL (gramZ (formF Q₀) γ hi) (gramZ (formF Q₀) γ' hi') :=
      Siegel.IsometricGL.trans (Siegel.IsometricGL.symm (latForm_isometricGL Q₀ _ γ hγ hi))
        (Siegel.IsometricGL.trans h1 (latForm_isometricGL Q₀ _ γ' hγ' hi'))
    have h3 := (isIsometric_latOf_iff (formF Q₀) γ' γ hi' hi).mpr h2
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    refine Quotient.sound ?_
    change IsIsometric (formF Q₀) c.out.1 c'.out.1
    rw [hγ, hγ']
    exact IsIsometric.symm _ h3
  · obtain ⟨Q', rfl, hg, hpd'⟩ := hd
    obtain ⟨γ, hi, hs, hQ'⟩ := exists_latOf_of_formSameGenus hpd hpd' hg
    set M : Lat F n := ⟨latOf γ, latOf_isLattice γ⟩
    have hc : (Quotient.mk _ M : LatClass (formF Q₀)) ∈ genusClasses (formF Q₀) (stdLat F n) :=
      ⟨M, rfl, hs⟩
    refine ⟨_, hc, ?_⟩
    obtain ⟨γ', hγ', hi', -⟩ := exists_free_of_mem hpd hc
    have hiso : IsIsometric (formF Q₀) (latOf γ') (latOf γ) := by
      rw [← hγ']
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (latSetoid (formF Q₀)) M))
    refine Quotient.sound ?_
    refine Siegel.IsometricGL.trans (latForm_isometricGL Q₀ _ γ' hγ' hi') ?_
    rw [← hQ']
    exact (isIsometric_latOf_iff (formF Q₀) γ γ' hi hi').mp (IsIsometric.symm _ hiso)

theorem autCard_eq_formClass (hpd : IsTotallyPosDef (formF Q₀)) {c : LatClass (formF Q₀)}
    (hc : c ∈ genusClasses (formF Q₀) (stdLat F n)) :
    LatClass.autCard (formF Q₀) c = FormClass.autCard (Quotient.mk (formSetoid (𝓞 F) n) (latForm Q₀ c.out)) := by
  obtain ⟨γ, hγ, hi, -⟩ := exists_free_of_mem hpd hc
  have e : LatClass.autCard (formF Q₀) c = Nat.card (autLat (formF Q₀) c.out.1) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [e, FormClass.autCard_mk, hγ, RatBridge.card_autLat_latOf _ γ hi,
    card_aut_eq (latForm_isometricGL Q₀ _ γ hγ hi)]

theorem repCount_eq_formClass (hpd : IsTotallyPosDef (formF Q₀)) {c : LatClass (formF Q₀)}
    (hc : c ∈ genusClasses (formF Q₀) (stdLat F n)) (m : 𝓞 F) :
    LatClass.repCount (formF Q₀) c (algebraMap (𝓞 F) F m) =
      FormClass.repNum (Quotient.mk (formSetoid (𝓞 F) n) (latForm Q₀ c.out)) m := by
  obtain ⟨γ, hγ, hi, -⟩ := exists_free_of_mem hpd hc
  have e : LatClass.repCount (formF Q₀) c (algebraMap (𝓞 F) F m) =
      repCount (formF Q₀) c.out (algebraMap (𝓞 F) F m) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  have hc' : c.out = ⟨latOf γ, latOf_isLattice γ⟩ := Subtype.ext hγ
  rw [e, FormClass.repNum_mk, repNum_eq (latForm_isometricGL Q₀ _ γ hγ hi), hc', RatBridge.repCount_latOf _ γ hi]
  rfl

/-- **$\mathrm{Mass}(Q_0) = \mathrm{Mass}(\mathcal O_F^n)$**: the mass over $\mathrm{GL}_n(\mathcal O_F)$-classes of forms in the genus of $Q_0$ is
The mass of the genus of $\mathcal O_F^n$ in $(F^n, Q_0)$, every totally real $F$, any class number. -/
@[kb "siegel1935" "Mass of a genus of forms = lattice mass, over F [unverified]"]
theorem formMass_eq (hpd : IsTotallyPosDef (formF Q₀)) :
    formMass Q₀ = Lattices.mass (formF Q₀) (stdLat F n) := by
  symm
  refine finsum_mem_eq_of_bijOn _ (bijOn_formClass hpd) fun c hc => ?_
  rw [autCard_eq_formClass hpd hc]

/-- **$\sum_{[Q']}r_{Q'}(m)/|\mathrm{Aut}(Q')| = \mathrm{repMass}(\mathcal O_F^n, m)$**, every totally real $F$, any class number. -/
@[kb "siegel1935" "Σ r_{Q'}(m)/|Aut Q'| = lattice repMass, over F [unverified]"]
theorem formRepMass_eq (hpd : IsTotallyPosDef (formF Q₀)) (m : 𝓞 F) :
    formRepMass Q₀ m = repMass (formF Q₀) (stdLat F n) (algebraMap (𝓞 F) F m) := by
  symm
  refine finsum_mem_eq_of_bijOn _ (bijOn_formClass hpd) fun c hc => ?_
  rw [autCard_eq_formClass hpd hc, repCount_eq_formClass hpd hc]

end Classes

end QuadFormsKB.Tamagawa.FormClassNF
