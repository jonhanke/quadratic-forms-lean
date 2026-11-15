/-
# Kitaoka 1993, §1.3: $\chi$ in characteristic $2$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, pp. 13–16 (printed pages): Theorem 1.3.1,
Corollaries 1.3.1, 1.3.2 and the definition of $\chi$ (p. 14).

**Proves** (finite fields of characteristic $2$; regular means the polar form is nondegenerate):
* `char2_decomp`: a regular space is $H^k$ or $H^k \perp W_a$ with $W_a$ an anisotropic plane (Theorem 1.3.1);
* `even_finrank_char2`: a regular space has even dimension;
* `chiGen_hypSpace_prod`: $\chi(H^k \perp Y) = \chi(Y)$;
* `chiGen_plane_prod`: $\chi(A \perp X) = \chi(A)\chi(X)$ for a regular plane $A$ and a regular space $X$;
* `chiGen_plane_sq`: $\chi(A)^2 = 1$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2Fiber
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Binary

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F]

section Char2

theorem two_eq_zero_of_ringChar (hF : ringChar F = 2) : (2 : F) = 0 := by
  have : CharP F 2 := hF ▸ ringChar.charP F
  simpa using CharP.cast_eq_zero F 2

theorem neg_eq_self_of_ringChar (hF : ringChar F = 2) (x : F) : -x = x := by
  have h2 := two_eq_zero_of_ringChar hF
  rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]

theorem polar_self_char2 (hF : ringChar F = 2) {V : Type} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, two_eq_zero_of_ringChar hF, zero_mul]

theorem neg_form_char2 (hF : ringChar F = 2) {V : Type} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) :
    -Q = Q := by
  ext x
  simp [neg_eq_self_of_ringChar hF]

end Char2

/-- $\chi(H^k \perp Y) = \chi(Y)$ for a regular $Y$. -/
theorem chiGen_hypSpace_prod {Y : Type} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    {P : QuadraticForm F Y} (hP : (polarBilin P).Nondegenerate) (k : ℕ) :
    chiGen ((QuadraticForm.hyperbolicSpace F k).prod P) = chiGen P := by
  induction k with
  | zero =>
    have hreg : (polarBilin ((QuadraticForm.hyperbolicSpace F 0).prod P)).Nondegenerate :=
      QuadraticForm.nondegenerate_polarBilin_prod (QuadraticForm.nondegenerate_hyperbolicSpace F 0) hP
    exact chiGen_congr hreg ⟨QuadraticForm.Witt.hyperbolicSpaceZeroProd P⟩
  | succ k ih =>
    have hreg : (polarBilin ((QuadraticForm.hyperbolicSpace F (k + 1)).prod P)).Nondegenerate :=
      QuadraticForm.nondegenerate_polarBilin_prod (QuadraticForm.nondegenerate_hyperbolicSpace F _) hP
    have hregk : (polarBilin ((QuadraticForm.hyperbolicSpace F k).prod P)).Nondegenerate :=
      QuadraticForm.nondegenerate_polarBilin_prod (QuadraticForm.nondegenerate_hyperbolicSpace F _) hP
    have e : ((QuadraticForm.hyperbolicSpace F (k + 1)).prod P).Equivalent
        ((QuadraticForm.hyperbolicPlane F).prod ((QuadraticForm.hyperbolicSpace F k).prod P)) :=
      ⟨(((QuadraticForm.Witt.hyperbolicSpaceSucc k).symm.prod (QuadraticMap.IsometryEquiv.refl P)).trans
        (QuadraticForm.Witt.prodAssoc _ _ _))⟩
    rw [chiGen_congr hreg e, chiGen_hyp_prod hregk, ih]

theorem finrank_hypSpace (k : ℕ) : finrank F (Fin k → F × F) = 2 * k := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod]
  ring

/-- $\chi(H^k) = 1$. -/
theorem chiGen_hypSpace (k : ℕ) : chiGen (QuadraticForm.hyperbolicSpace F k) = 1 := by
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate _ (QuadraticForm.nondegenerate_hyperbolicSpace F k)
  have ha : (0 : QuadraticForm F (Fin 0 → F)).Anisotropic := fun x _ => Subsingleton.elim x 0
  have e : (QuadraticForm.hyperbolicSpace F k).Equivalent
      ((QuadraticForm.hyperbolicSpace F k).prod (0 : QuadraticForm F (Fin 0 → F))) :=
    ⟨{ toLinearEquiv := LinearEquiv.prodUnique.symm, map_app' := fun x => by
        rw [QuadraticMap.prod_apply, QuadraticMap.zero_apply, add_zero]; rfl }⟩
  have hw := QuadraticForm.eq_wittIndex _ hrad ha e
  have hd : finrank F (Fin k → F × F) = 2 * k := finrank_hypSpace k
  simp only [chiGen, hd, ← hw]
  have : ¬ Odd (2 * k) := by simp
  simp [this]

/-- $\chi(H^k \perp W_a) = -1$ for an anisotropic plane $W_a$. -/
theorem chiGen_hypSpace_aniso {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    {Wa : QuadraticForm F U} (ha : Wa.Anisotropic) (hdim : finrank F U = 2)
    (hreg : (polarBilin Wa).Nondegenerate) (k : ℕ) :
    chiGen ((QuadraticForm.hyperbolicSpace F k).prod Wa) = -1 := by
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate _
    (QuadraticForm.nondegenerate_polarBilin_prod (QuadraticForm.nondegenerate_hyperbolicSpace F k) hreg)
  have hw := QuadraticForm.eq_wittIndex _ hrad ha (QuadraticMap.Equivalent.refl _)
  have hd : finrank F ((Fin k → F × F) × U) = 2 * k + 2 := by
    rw [Module.finrank_prod, finrank_hypSpace, hdim]
  simp only [chiGen, hd, ← hw]
  have : ¬ Odd (2 * k + 2) := by
    rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩
  simp only [this, if_false]
  rw [if_neg (by omega)]

/-- **Theorem 1.3.1 for a general space in characteristic $2$**: a regular space is $H^k$ or $H^k \perp W_a$ with
$W_a$ an anisotropic plane. -/
theorem char2_decomp [Finite F] (hF : ringChar F = 2) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : (polarBilin Q).Nondegenerate) :
    ∃ k : ℕ, Q.Equivalent (QuadraticForm.hyperbolicSpace F k) ∨
      ∃ Wa : QuadraticForm F (Fin 2 → F), Wa.Anisotropic ∧ (polarBilin Wa).Nondegenerate ∧
        Q.Equivalent ((QuadraticForm.hyperbolicSpace F k).prod Wa) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set n := finrank F V
  let e : V ≃ₗ[F] (Fin n → F) := LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let Q' := Q.comp e.symm.toLinearMap
  have hQQ' : Q.Equivalent Q' := ⟨{ toLinearEquiv := e, map_app' := fun x => by simp [Q'] }⟩
  have hQ' : (polarBilin Q').Nondegenerate := by
    rw [QuadraticForm.nondegenerate_polarBilin_iff] at hQ ⊢
    intro x hx
    have : e.symm x = 0 := hQ (e.symm x) fun y => by
      have := hx (e y)
      simpa [Q', polar] using this
    simpa using this
  obtain ⟨k, h1 | ⟨Wa, ha, hWa⟩ | ⟨hch, -⟩⟩ := theorem131 F (Fin n → F) Q' hQ'
  · exact ⟨k, Or.inl (hQQ'.trans h1)⟩
  · refine ⟨k, Or.inr ⟨Wa, ha, ?_, hQQ'.trans hWa⟩⟩
    -- the anisotropic part of a regular space is regular
    obtain ⟨g⟩ := hQQ'.trans hWa
    rw [QuadraticForm.nondegenerate_polarBilin_iff] at hQ ⊢
    intro x hx
    have h0 : g.symm (0, x) = 0 := hQ _ fun y => by
      obtain ⟨⟨u, w⟩, rfl⟩ := g.symm.surjective y
      have h := polar_of_iso g.symm.toLinearEquiv.toLinearMap (fun z => g.symm.map_app z) (0, x) (u, w)
      simp only [LinearEquiv.coe_coe] at h
      erw [h]
      simp only [polar, QuadraticMap.prod_apply, Prod.mk_add_mk, zero_add, map_zero]
      have := hx w
      simp only [polar] at this
      linear_combination this
    have h1 : g (g.symm (0, x)) = g 0 := by rw [h0]
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply, map_zero] at h1
    exact (Prod.mk.inj h1).2
  · exact absurd hF hch

/-- A regular space in characteristic $2$ has even dimension. -/
theorem even_finrank_char2 [Finite F] (hF : ringChar F = 2) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : (polarBilin Q).Nondegenerate) :
    Even (finrank F V) := by
  obtain ⟨k, h | ⟨Wa, -, -, h⟩⟩ := char2_decomp hF Q hQ
  · obtain ⟨g⟩ := h
    rw [g.toLinearEquiv.finrank_eq, finrank_hypSpace]
    exact ⟨k, by ring⟩
  · obtain ⟨g⟩ := h
    rw [g.toLinearEquiv.finrank_eq, Module.finrank_prod, finrank_hypSpace]
    exact ⟨k + 1, by simp; ring⟩

/-- Two anisotropic planes over a finite field are isometric. -/
theorem aniso_planes_equiv [Finite F] {U U' : Type} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    {A : QuadraticForm F U} {B : QuadraticForm F U'} (hU : finrank F U = 2) (hU' : finrank F U' = 2)
    (hA : A.Anisotropic) (hB : B.Anisotropic) : A.Equivalent B := by
  obtain ⟨F', _, _, hF'⟩ := Binary.exists_quadExt_of_anisotropic hU A hA
  obtain ⟨eA, hA'⟩ := Binary.exists_normIsometry hU A hA F' hF'
  obtain ⟨eB, hB'⟩ := Binary.exists_normIsometry hU' B hB F' hF'
  refine ⟨{ toLinearEquiv := eA.trans eB.symm, map_app' := fun x => ?_ }⟩
  show B (eB.symm (eA x)) = A x
  rw [← hB', LinearEquiv.apply_symm_apply, hA']

open Classical in
/-- $\chi$ of a regular plane: $1$ if isotropic, $-1$ if anisotropic. -/
theorem chiGen_plane [Finite F] {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    {A : QuadraticForm F U} (hU : finrank F U = 2) (hA : (polarBilin A).Nondegenerate) :
    chiGen A = if A.Anisotropic then -1 else 1 := by
  split_ifs with h
  · have e : A.Equivalent ((QuadraticForm.hyperbolicSpace F 0).prod A) :=
      ⟨(QuadraticForm.Witt.hyperbolicSpaceZeroProd A).symm⟩
    rw [chiGen_congr hA e, chiGen_hypSpace_aniso h hU hA 0]
  · simp only [QuadraticMap.Anisotropic, not_forall] at h
    obtain ⟨v, hv, hv0⟩ := h
    have hH := Radical.proposition122_plane A hU hA ⟨v, hv0, hv⟩
    have e : A.Equivalent (QuadraticForm.hyperbolicSpace F 1) :=
      hH.trans ⟨(((QuadraticForm.Witt.hyperbolicSpaceZeroProd _).symm.trans
        (QuadraticMap.IsometryEquiv.prodComm _ _)).trans (QuadraticForm.Witt.hyperbolicSpaceSucc 0))⟩
    rw [chiGen_congr hA e, chiGen_hypSpace]

theorem chiGen_plane_sq [Finite F] {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    {A : QuadraticForm F U} (hU : finrank F U = 2) (hA : (polarBilin A).Nondegenerate) :
    chiGen A * chiGen A = 1 := by
  classical
  rw [chiGen_plane hU hA]; split_ifs <;> norm_num

/-- **Multiplicativity of $\chi$** in characteristic $2$: $\chi(A \perp X) = \chi(A)\chi(X)$ for a regular plane $A$
and a regular space $X$. -/
theorem chiGen_plane_prod [Finite F] (hF : ringChar F = 2) {U X : Type} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    {A : QuadraticForm F U} {QX : QuadraticForm F X} (hU : finrank F U = 2) (hA : (polarBilin A).Nondegenerate)
    (hX : (polarBilin QX).Nondegenerate) :
    chiGen (A.prod QX) = chiGen A * chiGen QX := by
  have hAX : (polarBilin (A.prod QX)).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod hA hX
  by_cases han : A.Anisotropic
  · rw [chiGen_plane hU hA, if_pos han]
    obtain ⟨k, h | ⟨Wa, ha, hWa, h⟩⟩ := char2_decomp hF QX hX
    · -- $A \perp H^k \cong H^k \perp A$
      have e : (A.prod QX).Equivalent ((QuadraticForm.hyperbolicSpace F k).prod A) :=
        (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl A) h).trans
          ⟨QuadraticMap.IsometryEquiv.prodComm _ _⟩
      rw [chiGen_congr hAX e, chiGen_hypSpace_aniso han hU hA, chiGen_congr hX h, chiGen_hypSpace]
      ring
    · -- $A \perp H^k \perp W_a \cong H^k \perp (A \perp W_a) \cong H^k \perp H^2$
      have hfin : finrank F (Fin 2 → F) = 2 := by simp
      have hAW : A.Equivalent Wa := aniso_planes_equiv hU hfin han ha
      have h2 := Binary.corollary132 hU A Wa hA hAW
      have hreg2 : (polarBilin (A.prod Wa)).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod hA hWa
      have e : (A.prod QX).Equivalent ((QuadraticForm.hyperbolicSpace F k).prod (A.prod Wa)) :=
        (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl A) h).trans
          ⟨((QuadraticForm.Witt.prodAssoc _ _ _).symm.trans
            ((QuadraticMap.IsometryEquiv.prodComm _ _).prod (QuadraticMap.IsometryEquiv.refl _))).trans
            (QuadraticForm.Witt.prodAssoc _ _ _)⟩
      rw [chiGen_congr hAX e, chiGen_hypSpace_prod hreg2, chiGen_congr hreg2 h2, chiGen_hypSpace,
        chiGen_congr hX h, chiGen_hypSpace_aniso ha hfin hWa]
      ring
  · rw [chiGen_plane hU hA, if_neg han, one_mul]
    simp only [QuadraticMap.Anisotropic, not_forall] at han
    obtain ⟨v, hv, hv0⟩ := han
    have hH := Radical.proposition122_plane A hU hA ⟨v, hv0, hv⟩
    rw [chiGen_congr hAX (hH.prod (QuadraticMap.Equivalent.refl QX)), chiGen_hyp_prod hX]

end QuadFormsKB.Kitaoka.FqCount
