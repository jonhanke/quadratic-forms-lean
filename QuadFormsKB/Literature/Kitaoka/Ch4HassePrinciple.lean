/-
# Kitaoka 1993, Corollary 4.1.2: the Hasse principle for representations of quadratic spaces (over every number field)

**Statement.** Let $F$ be a number field and $U$, $V$ regular (nondegenerate) quadratic spaces over $F$. Then $U$ is
represented by $V$ over $F$ (there is an injective $F$-linear map $\sigma : U \to V$ with $Q_V(\sigma x) = Q_U(x)$) as soon
as $U_v$ is represented by $V_v$ over the completion $F_v$ for **every** place $v$ of $F$, infinite and finite
(`NFPlace.Everywhere`). The converse is trivial. This is `isRepresentedBy_of_everywhere`.

**Proof** (Kitaoka's, by induction on $m = \dim U$). For $m = 0$ there is nothing to prove. For $m \ge 1$ diagonalize
$U \cong \langle a \rangle \perp U'$ with $a \ne 0$. At every place $a$ is a value of $V_v$ (the image of the first basis
vector), so by the Hasse principle for values (`represents_iff_everywhere_nf`) $a$ is represented by $V$ over $F$, hence
$V \cong \langle a \rangle \perp V'$ over $F$ (`exists_isometric_diag_cons`; $\dim V \ge 1$ since $V$ represents $a \ne 0$).
Locally $\langle a \rangle \perp U'_v \to \langle a \rangle \perp V'_v$, and **representation cancellation**
(`representation_cancellation`, Kitaoka Cor. 1.2.3, from Witt's transitivity theorem: move the image of the first basis
vector back to itself by an isometry of the target; the isometry then maps $\langle a\rangle^\perp$ into
$\langle a \rangle^\perp$) gives $U'_v \to V'_v$ at every place. Induction gives $U' \to V'$ over $F$, hence
$U \cong \langle a \rangle \perp U' \to \langle a \rangle \perp V' \cong V$.

Cancellation is proved over any field of characteristic $0$ for Mathlib quadratic forms; the induction is for the
repository's `QuadForm` with `toQuadraticFormIn`, in the style of `isometricIn_of_everywhere_nf`.
-/
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Tamagawa.FormClassNF

open NumberField QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

section Cancellation

variable {K X Y : Type*} [Field K] [CharZero K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

omit [CharZero K] in
/-- A representation $X \to Y$ extends to a representation $Q_1 \perp X \to Q_1 \perp Y$ by the identity on $Q_1$. -/
theorem isRepresentedBy_prod_left {Z : Type*} [AddCommGroup Z] [Module K Z] (Q₁ : QuadraticForm K Z)
    {QX : QuadraticForm K X} {QY : QuadraticForm K Y} (h : OMeara.IsRepresentedBy QX QY) :
    OMeara.IsRepresentedBy (Q₁.prod QX) (Q₁.prod QY) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨⟨LinearMap.prodMap LinearMap.id σ.toLinearMap, fun x => ?_⟩, ?_⟩
  · simp [QuadraticMap.prod_apply, σ.map_app]
  · exact Function.Injective.prodMap Function.injective_id hσ

/-- **Representation cancellation** (Kitaoka 1993, Cor. 1.2.3, p. 7; characteristic $0$): if
$\langle b \rangle \perp X \to \langle b \rangle \perp Y$ with $b \ne 0$ a nondegenerate one-dimensional form $Q_1$
of value $b$ at $(1)$, and $Y$ nondegenerate (finite dimensional), then $X \to Y$. -/
@[kb "kitaoka1993" "§1.2, Cor. 1.2.3, p. 7 (representation cancellation)"]
theorem representation_cancellation [FiniteDimensional K Y] (Q₁ : QuadraticForm K (Fin 1 → K))
    (hQ₁ : (polarBilin Q₁).Nondegenerate) (hb : Q₁ (fun _ => 1) ≠ 0)
    (QX : QuadraticForm K X) (QY : QuadraticForm K Y) (hY : (polarBilin QY).Nondegenerate)
    (h : OMeara.IsRepresentedBy (Q₁.prod QX) (Q₁.prod QY)) : OMeara.IsRepresentedBy QX QY := by
  obtain ⟨σ, hσ⟩ := h
  set e0 : (Fin 1 → K) × X := (fun _ => 1, 0) with he0
  set b := Q₁ (fun _ => 1) with hbdef
  have hnd : (polarBilin (Q₁.prod QY)).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod hQ₁ hY
  have hv : (Q₁.prod QY) (σ e0) = b := by
    rw [σ.map_app, he0, QuadraticMap.prod_apply]; simp [hbdef]
  have hw : (Q₁.prod QY) ((fun _ => 1 : Fin 1 → K), (0 : Y)) = b := by
    rw [QuadraticMap.prod_apply]; simp [hbdef]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate (Q₁.prod QY) hnd hb hv hw
  let τ : (Q₁.prod QX) →qᵢ (Q₁.prod QY) := ρ.toIsometry.comp σ
  have hτ : Function.Injective τ := ρ.injective.comp hσ
  have hτe : τ e0 = ((fun _ => 1 : Fin 1 → K), (0 : Y)) := hρ
  have hpol : ∀ u v, polar (Q₁.prod QY) (τ u) (τ v) = polar (Q₁.prod QX) u v := fun u v => by
    simp only [polar, ← map_add, τ.map_app]
  have hfst : ∀ x : X, (τ (0, x)).1 = 0 := by
    intro x
    have h0 := hpol e0 (0, x)
    rw [hτe] at h0
    have h1 : polar (Q₁.prod QX) e0 (0, x) = 0 := by
      simp [polar, he0, QuadraticMap.prod_apply]
    rw [h1] at h0
    have h2 : polar (Q₁.prod QY) ((fun _ => 1 : Fin 1 → K), (0 : Y)) (τ (0, x)) =
        polar Q₁ (fun _ => 1) (τ (0, x)).1 := by
      generalize τ (0, x) = w
      obtain ⟨t, y⟩ := w
      simp [polar, QuadraticMap.prod_apply]
      ring
    rw [h2] at h0
    have h3 : (τ (0, x)).1 = (τ (0, x)).1 0 • (fun _ => 1 : Fin 1 → K) := by
      ext i; simp [Subsingleton.elim i 0]
    rw [h3, polar_smul_right, polar_self] at h0
    have h4 : (2 : K) * b ≠ 0 := mul_ne_zero two_ne_zero hb
    have h5 : (τ (0, x)).1 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd (by simpa [hbdef] using h) h4
    ext i; simp [Subsingleton.elim i 0, h5]
  refine ⟨⟨(LinearMap.snd K _ _) ∘ₗ τ.toLinearMap ∘ₗ (LinearMap.inr K _ _), fun x => ?_⟩, ?_⟩
  · have := τ.map_app (0, x)
    rw [QuadraticMap.prod_apply, QuadraticMap.prod_apply, hfst x] at this
    simp only [map_zero, zero_add] at this
    simpa using this
  · intro x x' hxx
    have hxx' : (τ (0, x)).2 = (τ (0, x')).2 := hxx
    have : ((0 : Fin 1 → K), x) = (0, x') := hτ (Prod.ext (by simp [hfst]) hxx')
    exact (Prod.mk.inj this).2

end Cancellation

section Transport

variable {F : Type} [Field F] {m n : ℕ} (K : Type) [Field K] [Algebra F K]
open QuadFormsKB QuadFormsKB.QuadForm

/-- The first diagonal entry $a$ of $\langle a, \alpha \rangle$ is a value of it. -/
theorem representsIn_diag_head (a : F) {k : ℕ} (α : Fin k → F) :
    (diag (Fin.cons a α : Fin (k + 1) → F)).RepresentsIn K a := by
  refine ⟨Pi.single 0 1, ?_⟩
  rw [evalIn_diag, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [hj]
  · simp

variable {QU : QuadForm F (m + 1)} {QV : QuadForm F (n + 1)} {a : F} {α : Fin m → F} {β : Fin n → F}

/-- Local representation of the heads/tails: $\langle a, \alpha \rangle \to \langle a, \beta \rangle$ with $a \ne 0$ and
$\beta$ nondegenerate reduces to $\langle \alpha \rangle \to \langle \beta \rangle$ (cancellation; characteristic $0$). -/
theorem isRepresentedBy_tail [NeZero (2 : F)] [CharZero K] (ha : a ≠ 0) (hβ : ∀ i, β i ≠ 0)
    (h : OMeara.IsRepresentedBy ((diag (Fin.cons a α : Fin (m + 1) → F)).toQuadraticFormIn K)
      ((diag (Fin.cons a β : Fin (n + 1) → F)).toQuadraticFormIn K)) :
    OMeara.IsRepresentedBy ((diag α).toQuadraticFormIn K) ((diag β).toQuadraticFormIn K) := by
  have ha' : ∀ i, (![a] : Fin 1 → F) i ≠ 0 := fun i => by simpa [Subsingleton.elim i 0] using ha
  refine representation_cancellation ((diag ![a]).toQuadraticFormIn K)
    (nondegenerate_polarBilin_toQuadraticFormIn K (nondegenerate_diag ha')) ?_ _ _
    (nondegenerate_polarBilin_toQuadraticFormIn K (nondegenerate_diag hβ)) ?_
  · rw [toQuadraticFormIn_apply, evalIn_diag]
    simpa using (map_ne_zero_iff _ (algebraMap F K).injective).mpr ha
  · exact (OMeara.IsRepresentedBy.of_equivalent ⟨(isometryEquivDiagCons K a α).symm⟩).trans
      (h.trans (OMeara.IsRepresentedBy.of_equivalent ⟨isometryEquivDiagCons K a β⟩))

/-- Adding a common first diagonal entry preserves representation (any field $K$ over $F$). -/
theorem isRepresentedBy_cons (a : F)
    (h : OMeara.IsRepresentedBy ((diag α).toQuadraticFormIn K) ((diag β).toQuadraticFormIn K)) :
    OMeara.IsRepresentedBy ((diag (Fin.cons a α : Fin (m + 1) → F)).toQuadraticFormIn K)
      ((diag (Fin.cons a β : Fin (n + 1) → F)).toQuadraticFormIn K) :=
  (OMeara.IsRepresentedBy.of_equivalent ⟨isometryEquivDiagCons K a α⟩).trans
    ((isRepresentedBy_prod_left _ h).trans
      (OMeara.IsRepresentedBy.of_equivalent ⟨(isometryEquivDiagCons K a β).symm⟩))

/-- Representation transports represented values: if $Q \to Q'$ over $K$ and $Q$ represents $c$ over $K$, so does $Q'$. -/
theorem representsIn_of_isRepresentedBy {k l : ℕ} {Q : QuadForm F k} {Q' : QuadForm F l} {c : F}
    (h : OMeara.IsRepresentedBy (Q.toQuadraticFormIn K) (Q'.toQuadraticFormIn K))
    (hc : Q.RepresentsIn K c) : Q'.RepresentsIn K c := by
  obtain ⟨σ, -⟩ := h
  obtain ⟨x, hx⟩ := hc
  refine ⟨σ x, ?_⟩
  rw [← toQuadraticFormIn_apply, σ.map_app, toQuadraticFormIn_apply, hx]

/-- If $Q \cong Q'$ over $K$ then $Q \to Q'$ over $K$. -/
theorem isRepresentedBy_of_isometricIn {k : ℕ} {Q Q' : QuadForm F k} (h : Q.IsometricIn K Q') :
    OMeara.IsRepresentedBy (Q.toQuadraticFormIn K) (Q'.toQuadraticFormIn K) := by
  obtain ⟨e⟩ := (isometricIn_iff_equivalent K Q Q').mp h
  exact OMeara.IsRepresentedBy.of_equivalent ⟨e.symm⟩

/-- If $Q \cong Q'$ over $K$ then $Q' \to Q$ over $K$. -/
theorem isRepresentedBy_of_isometricIn_symm {k : ℕ} {Q Q' : QuadForm F k} (h : Q.IsometricIn K Q') :
    OMeara.IsRepresentedBy (Q'.toQuadraticFormIn K) (Q.toQuadraticFormIn K) :=
  OMeara.IsRepresentedBy.of_equivalent ((isometricIn_iff_equivalent K Q Q').mp h)

end Transport

open QuadFormsKB.QuadForm in
/-- **The Hasse principle for representations of regular spaces over a number field** (Kitaoka 1993, Cor. 4.1.2, p. 67):
a regular quadratic space $U$ over a number field $F$ is represented by a regular space $V$ over $F$ as soon as $U_v$ is
represented by $V_v$ over every completion $F_v$ (all infinite and finite places). Only the "if" direction is the theorem
(the converse is trivial). Proof: induction on $\dim U$; split off a value $a$ of $U$ (represented by $V$ everywhere,
hence over $F$), cancel $\langle a \rangle$ locally (`representation_cancellation`) and apply the induction hypothesis. -/
@[kb "kitaoka1993" "§4.1, Cor. 4.1.2, p. 67 (over every number field)"]
theorem isRepresentedBy_of_everywhere {F : Type} [Field F] [NumberField F] {m n : ℕ}
    (QU : QuadForm F m) (QV : QuadForm F n) (hU : QU.Nondegenerate) (hV : QV.Nondegenerate)
    (h : NFPlace.Everywhere (F := F) fun K _ _ =>
      OMeara.IsRepresentedBy (QU.toQuadraticFormIn K) (QV.toQuadraticFormIn K)) :
    OMeara.IsRepresentedBy (QU.toQuadraticFormIn F) (QV.toQuadraticFormIn F) := by
  induction m generalizing n with
  | zero =>
    refine ⟨⟨0, fun x => ?_⟩, fun x y _ => Subsingleton.elim x y⟩
    have h0 : x = 0 := Subsingleton.elim _ _
    have h1 : (QU.toQuadraticFormIn F) x = 0 := by rw [h0, map_zero]
    rw [h1]
    exact map_zero (QV.toQuadraticFormIn F)
  | succ m ih =>
    obtain ⟨α, hα, hQα⟩ := FieldGen.exists_isometric_diag QU hU
    have hc : Fin.cons (α 0) (Fin.tail α) = α := Fin.cons_self_tail α
    have hQα' : QU.IsometricIn F (diag (Fin.cons (α 0) (Fin.tail α) : Fin (m + 1) → F)) := by
      rw [hc]; exact hQα
    have hQloc : ∀ (K : Type) [Field K] [Algebra F K], QU.IsometricIn K
        (diag (Fin.cons (α 0) (Fin.tail α) : Fin (m + 1) → F)) :=
      fun K _ _ => FieldGen.isometricIn_of_base K hQα'
    have hQrep : ∀ (K : Type) [Field K] [Algebra F K], QU.RepresentsIn K (α 0) :=
      fun K _ _ => representsIn_of_isometricIn K (hQloc K) (representsIn_diag_head K _ _)
    have hVrep : QV.RepresentsIn F (α 0) := by
      rw [represents_iff_everywhere_nf QV hV _ (hα 0)]
      exact Tamagawa.FormClassNF.everywhere_mono
        (fun K _ _ hK => representsIn_of_isRepresentedBy K hK (hQrep K)) h
    cases n with
    | zero =>
      exfalso
      obtain ⟨x, hx⟩ := hVrep
      have h0 : x = 0 := Subsingleton.elim _ _
      have : QV.evalIn F x = 0 := by
        rw [← toQuadraticFormIn_apply, h0, map_zero]
      rw [this] at hx
      exact hα 0 (by simpa using hx.symm)
    | succ n =>
      obtain ⟨β, hβ, hRβ⟩ := exists_isometric_diag_cons hV (hα 0) hVrep
      have hRloc : ∀ (K : Type) [Field K] [Algebra F K], QV.IsometricIn K
          (diag (Fin.cons (α 0) β : Fin (n + 1) → F)) :=
        fun K _ _ => FieldGen.isometricIn_of_base K hRβ
      have hloc : NFPlace.Everywhere (F := F) fun K _ _ =>
          OMeara.IsRepresentedBy ((diag (Fin.tail α)).toQuadraticFormIn K)
            ((diag β).toQuadraticFormIn K) := by
        refine Tamagawa.FormClassNF.everywhere_mono (fun K _ _ hK => ?_) h
        have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
        exact isRepresentedBy_tail K (hα 0) hβ
          ((isRepresentedBy_of_isometricIn_symm K (hQloc K)).trans
            (hK.trans (isRepresentedBy_of_isometricIn K (hRloc K))))
      have ih' := ih (diag (Fin.tail α)) (diag β) (nondegenerate_diag fun i => hα i.succ)
        (nondegenerate_diag hβ) hloc
      exact (isRepresentedBy_of_isometricIn F hQα').trans
        ((isRepresentedBy_cons F (α 0) ih').trans (isRepresentedBy_of_isometricIn_symm F hRβ))

end QuadFormsKB.Kitaoka