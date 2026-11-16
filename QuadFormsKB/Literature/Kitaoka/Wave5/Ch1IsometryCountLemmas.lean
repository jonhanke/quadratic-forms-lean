/-
# Lemmas for Kitaoka's Theorem 1.3.2 over $\mathbb F_q$, $q$ odd

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, pp. 14–17 (printed pages).

**Setting.** $F$ is a finite field of odd characteristic, quadratic spaces are Mathlib quadratic forms on
finite-dimensional spaces, regular means `(polarBilin Q).Nondegenerate`, $\chi$ is `Kitaoka.FqCount.chiGen`
($0$ in odd dimension, $1$ for hyperbolic spaces, $-1$ otherwise), $a(t, W)$ is `Kitaoka.FqCount.valCount`,
and $\langle t\rangle$ is `lineForm t` ($x \mapsto tx^2$ on $F$).

**Proves** (helpers, unconditional)
* `chiGen_congr`: $\chi$ is an isometry invariant;
* `chiGen_neg`: $\chi(W^{(-1)}) = \chi(W)$;
* `chiGen_hyp_prod`: $\chi(H \perp P) = \chi(P)$;
* `lineForm_prod_neg_equiv`: $\langle t\rangle \perp \langle -t\rangle \cong H$;
* `orthSplit`: for $Q(x) = t \ne 0$, $x^\perp$ is regular of dimension $\dim W - 1$ and $\langle t\rangle \perp x^\perp
  \cong W$;
* `valCount_odd`: for $\dim W = w$ odd and $t \ne 0$, $a(t, W) = q^{w-1} + \chi(W \perp \langle -t\rangle)q^{(w-1)/2}$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch5Lemma569Proof
import Mathlib.Algebra.Order.PUnit

open QuadraticMap Module QuadraticForm.Witt

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F]

/-- The one-dimensional quadratic space $\langle t\rangle$: $x \mapsto tx^2$ on $F$. -/
def lineForm (t : F) : QuadraticForm F F := t • QuadraticMap.sq

@[simp] theorem lineForm_apply (t x : F) : lineForm t x = t * (x * x) := rfl

/-- The orthogonal complement $x^\perp = \{y \mid b(x, y) = 0\}$ of a vector $x$. -/
def perpVec {W : Type} [AddCommGroup W] [Module F W] (Q : QuadraticForm F W) (x : W) : Submodule F W :=
  LinearMap.ker (polarBilin Q x)

theorem mem_perpVec {W : Type} [AddCommGroup W] [Module F W] (Q : QuadraticForm F W) (x y : W) :
    y ∈ perpVec Q x ↔ polar Q x y = 0 := Iff.rfl

/-- $\chi$ is an isometry invariant. -/
theorem chiGen_congr {V W : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {P : QuadraticForm F W}
    (hQ : (polarBilin Q).Nondegenerate) (h : Q.Equivalent P) : chiGen Q = chiGen P := by
  obtain ⟨e⟩ := h
  have hQr : Q.radical = ⊥ := QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ
  have hPr : P.radical = ⊥ := radical_eq_bot_of_isometryEquiv e.symm hQr
  obtain ⟨U, _, _, _, Qa, ha, ⟨g⟩⟩ := QuadraticForm.wittIndex_spec P hPr
  have hw : QuadraticForm.wittIndex P = QuadraticForm.wittIndex Q :=
    QuadraticForm.eq_wittIndex Q hQr ha ⟨e.trans g⟩
  simp only [chiGen, e.toLinearEquiv.finrank_eq, hw]

/-- $\chi(W^{(-1)}) = \chi(W)$ for a regular space $W$. -/
theorem chiGen_neg {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F W}
    (hQ : (polarBilin Q).Nondegenerate) : chiGen (-Q) = chiGen Q := by
  have hrad : Q.radical = ⊥ := QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ
  have hnd : (polarBilin (-Q)).Nondegenerate := by
    rw [QuadraticForm.nondegenerate_polarBilin_iff] at hQ ⊢
    intro v hv
    exact hQ v fun w => by
      have h := hv w
      have h' : polar Q v w = -polar (⇑(-Q)) v w := by simp [polar]; ring
      rw [h', h, neg_zero]
  have hrad' := QuadraticForm.radical_eq_bot_of_nondegenerate (-Q) hnd
  obtain ⟨U, _, _, _, Qa, ha, ⟨g⟩⟩ := QuadraticForm.wittIndex_spec Q hrad
  set m := QuadraticForm.wittIndex Q with hm
  have ha' : (-Qa).Anisotropic := fun u hu => ha u (by rwa [neg_apply, neg_eq_zero] at hu)
  let ψ : (Fin m → F × F) ≃ₗ[F] (Fin m → F × F) :=
    LinearEquiv.piCongrRight fun _ => LinearEquiv.prodCongr (LinearEquiv.refl F F) (LinearEquiv.neg F)
  let e : (-Q).IsometryEquiv ((QuadraticForm.hyperbolicSpace F m).prod (-Qa)) :=
    { toLinearEquiv := g.toLinearEquiv.trans (LinearEquiv.prodCongr ψ (LinearEquiv.refl F U))
      map_app' := fun v => by
        have := g.map_app v
        simp only [QuadraticMap.prod_apply, QuadraticForm.hyperbolicSpace_apply] at this ⊢
        simp [ψ, Finset.sum_neg_distrib, ← this]
        ring }
  have h1 : QuadraticForm.wittIndex (-Q) = m := (QuadraticForm.eq_wittIndex (-Q) hrad' ha' ⟨e⟩).symm
  simp only [chiGen, h1, ← hm]

/-- Splitting off a hyperbolic plane keeps $\chi$ (`chiGen_finrank_of_hyp` without its extra `[Finite F]`). -/
theorem chiGen_hyp_aux {V W : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F V} {P : QuadraticForm F W}
    (hQ : Q.radical = ⊥) (e : ((QuadraticForm.hyperbolicPlane F).prod P).IsometryEquiv Q) :
    chiGen P = chiGen Q := by
  have hP : P.radical = ⊥ :=
    QuadraticForm.radical_eq_bot_of_prod_right (radical_eq_bot_of_isometryEquiv e hQ)
  have hdim : finrank F V = finrank F W + 2 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, Module.finrank_self]; ring
  obtain ⟨U, _, _, _, Qa, ha, ⟨g⟩⟩ := QuadraticForm.wittIndex_spec P hP
  have hW : QuadraticForm.wittIndex Q = QuadraticForm.wittIndex P + 1 := by
    refine (QuadraticForm.eq_wittIndex Q hQ ha ⟨?_⟩).symm
    exact e.symm.trans (((QuadraticMap.IsometryEquiv.refl _).prod g).trans
      ((prodAssoc _ _ _).symm.trans ((hyperbolicSpaceSucc _).prod (QuadraticMap.IsometryEquiv.refl _))))
  simp only [chiGen, hdim, hW]
  have hodd : Odd (finrank F W + 2) ↔ Odd (finrank F W) := by
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := h; exact ⟨k - 1, by omega⟩
    · obtain ⟨k, hk⟩ := h; exact ⟨k + 1, by omega⟩
  have hidx : QuadraticForm.wittIndex P + 1 = (finrank F W + 2) / 2 ↔
      QuadraticForm.wittIndex P = finrank F W / 2 := by omega
  simp only [hodd, hidx]

/-- $\chi(H \perp P) = \chi(P)$ for a regular space $P$. -/
theorem chiGen_hyp_prod {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {P : QuadraticForm F W}
    (hP : (polarBilin P).Nondegenerate) :
    chiGen ((QuadraticForm.hyperbolicPlane F).prod P) = chiGen P := by
  have hrad : ((QuadraticForm.hyperbolicPlane F).prod P).radical = ⊥ :=
    QuadraticForm.radical_eq_bot_of_nondegenerate _
      (QuadraticForm.nondegenerate_polarBilin_prod (QuadraticForm.nondegenerate_hyperbolicPlane F) hP)
  exact (chiGen_hyp_aux hrad (QuadraticMap.IsometryEquiv.refl _)).symm

/-- $\langle t\rangle \perp \langle -t\rangle$ is a hyperbolic plane ($\operatorname{char} F \ne 2$, $t \ne 0$). -/
theorem lineForm_prod_neg_equiv (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    ((lineForm t).prod (lineForm (-t))).Equivalent (QuadraticForm.hyperbolicPlane F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  let e : (F × F) ≃ₗ[F] (F × F) :=
    { toFun := fun p => (t * (p.1 - p.2), p.1 + p.2)
      invFun := fun q => ((q.1 / t + q.2) / 2, (q.2 - q.1 / t) / 2)
      map_add' := fun p q => by ext <;> simp <;> ring
      map_smul' := fun c p => by ext <;> simp <;> ring
      left_inv := fun p => by ext <;> simp <;> field_simp <;> ring
      right_inv := fun q => by ext <;> simp <;> field_simp <;> ring }
  refine ⟨{ toLinearEquiv := e, map_app' := fun p => ?_ }⟩
  simp only [QuadraticForm.hyperbolicPlane_apply, QuadraticMap.prod_apply, lineForm_apply]
  show t * (p.1 - p.2) * (p.1 + p.2) = _
  ring

/-- $\langle t \rangle$ is regular for $t \ne 0$ ($\operatorname{char} F \ne 2$). -/
theorem lineForm_nondegenerate (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    (polarBilin (lineForm t)).Nondegenerate := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  have := hv 1
  simp only [polar, lineForm_apply] at this
  have h3 : (2 * t) * v = 0 := by linear_combination this
  exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero h2 ht)

/-- **Orthogonal splitting** ($\operatorname{char} F \ne 2$): if $W$ is regular and $Q(x) = t \ne 0$, then
$x^\perp$ is regular, $\dim x^\perp + 1 = \dim W$, and $\langle t\rangle \perp x^\perp \cong W$ via
$(s, y) \mapsto sx + y$. -/
theorem orthSplit (hF : ringChar F ≠ 2) {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {Q : QuadraticForm F W} (hQ : (polarBilin Q).Nondegenerate) {x : W} {t : F} (hx : Q x = t) (ht : t ≠ 0) :
    (polarBilin (Q.comp (perpVec Q x).subtype)).Nondegenerate ∧ finrank F (perpVec Q x) + 1 = finrank F W ∧
      ((lineForm t).prod (Q.comp (perpVec Q x).subtype)).Equivalent Q := by
  have h2t : polar Q x x = 2 * t := by
    rw [QuadraticMap.polar_self, hx]; simp
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc : 2 * t ≠ 0 := mul_ne_zero h2 ht
  let L : F × perpVec Q x →ₗ[F] W :=
    (LinearMap.toSpanSingleton F W x).coprod (perpVec Q x).subtype
  have hL : ∀ (s : F) (y : perpVec Q x), L (s, y) = s • x + (y : W) := fun s y => rfl
  have hperp : ∀ y : perpVec Q x, polar Q x y = 0 := fun y => (mem_perpVec Q x y).1 y.2
  have hpolx : ∀ (s : F) (y : perpVec Q x), polar Q x (s • x + (y : W)) = s * (2 * t) := by
    intro s y
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, h2t, hperp y]
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, y⟩ h
    rw [hL] at h
    have h1 : s * (2 * t) = 0 := by rw [← hpolx s y, h]; exact QuadraticMap.polar_zero_right _ _
    have hs : s = 0 := (mul_eq_zero.1 h1).resolve_right hc
    have hy : (y : W) = 0 := by simpa [hs] using h
    exact Prod.ext hs (Subtype.ext hy)
  have hsurj : Function.Surjective L := fun w => by
    have hy : w - (polar Q x w / (2 * t)) • x ∈ perpVec Q x := by
      rw [mem_perpVec, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, h2t, smul_eq_mul,
        div_mul_cancel₀ _ hc, sub_self]
    exact ⟨(polar Q x w / (2 * t), ⟨_, hy⟩), by rw [hL]; simp⟩
  let e0 := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hQe : ∀ (s : F) (y : perpVec Q x),
      Q (s • x + (y : W)) = t * (s * s) + (Q.comp (perpVec Q x).subtype) y := by
    intro s y
    rw [QuadraticMap.map_add (⇑Q) (s • x) (y : W), QuadraticMap.map_smul, hx, QuadraticMap.polar_smul_left, hperp y]
    simp only [smul_eq_mul, mul_zero, add_zero, QuadraticMap.comp_apply, Submodule.subtype_apply]
    ring
  have iso : ((lineForm t).prod (Q.comp (perpVec Q x).subtype)).IsometryEquiv Q :=
    { toLinearEquiv := e0
      map_app' := fun ⟨s, y⟩ => by
        show Q (L (s, y)) = _
        rw [hL, hQe]
        rfl }
  refine ⟨?_, ?_, ⟨iso⟩⟩
  · rw [QuadraticForm.nondegenerate_polarBilin_iff]
    intro y hy
    have hy' : ∀ w, polar Q (y : W) w = 0 := by
      intro w
      obtain ⟨⟨s, z⟩, hz⟩ := hsurj w
      rw [← hz, hL, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm Q (y : W) x, hperp y]
      have hz' : polar Q (y : W) (z : W) = 0 := by
        have := hy z
        simpa [polar] using this
      rw [hz']
      simp
    exact Subtype.ext ((QuadraticForm.nondegenerate_polarBilin_iff Q).1 hQ y hy')
  · have := e0.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at this
    omega

/-- A one-dimensional quadratic space spanned by a vector $u$ with $Q(u) = t$ is $\cong \langle t\rangle$. -/
def lineIso {U : Type} [AddCommGroup U] [Module F U] (Qa : QuadraticForm F U) {u : U} (hu : u ≠ 0)
    (h1 : finrank F U = 1) {t : F} (ht : Qa u = t) : (lineForm t).IsometryEquiv Qa where
  toLinearEquiv := LinearEquiv.ofBijective (LinearMap.toSpanSingleton F U u)
    ⟨fun a b h => smul_left_injective F hu h,
      fun w => (finrank_eq_one_iff_of_nonzero' u hu).1 h1 w⟩
  map_app' s := by
    show Qa (s • u) = t * (s * s)
    rw [QuadraticMap.map_smul, ht, smul_eq_mul, mul_comm]

/-- $a(t, \langle t\rangle) = 2$ for $t \ne 0$, $\operatorname{char} F \ne 2$. -/
theorem valCount_lineForm_self [Finite F] (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    valCount (lineForm t) t = 2 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  unfold valCount
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨-1, by simp⟩, ?_, ?_⟩
  · intro h
    have h' : (1 : F) = -1 := congrArg Subtype.val h
    apply h2
    linear_combination h'
  · ext ⟨x, hx⟩
    simp only [lineForm_apply] at hx
    have hx2 : (x - 1) * (x + 1) = 0 := by
      have : t * ((x - 1) * (x + 1)) = 0 := by linear_combination hx
      exact (mul_eq_zero.1 this).resolve_left ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases mul_eq_zero.1 hx2 with h | h
    · left; exact Subtype.ext (by simpa [sub_eq_zero] using h)
    · right; exact Subtype.ext (by simpa [add_eq_zero_iff_eq_neg] using h)

/-- **$a(t, W)$ in odd dimension** ($\operatorname{char} F \ne 2$): for a regular $W$ of odd dimension $w$ over a
finite field with $q$ elements and $t \ne 0$, $a(t, W) = q^{w-1} + \chi(W \perp \langle -t\rangle)\,q^{(w-1)/2}$. -/
theorem valCount_odd [Finite F] (hF : ringChar F ≠ 2) {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {Q : QuadraticForm F W} (hQ : (polarBilin Q).Nondegenerate)
    (hw : Odd (finrank F W)) {t : F} (ht : t ≠ 0) :
    (valCount Q t : ℝ) = (Nat.card F : ℝ) ^ (finrank F W - 1) +
      chiGen (Q.prod (lineForm (-t))) * (Nat.card F : ℝ) ^ ((finrank F W - 1) / 2) := by
  classical
  have hrad : Q.radical = ⊥ := QuadraticForm.radical_eq_bot_of_nondegenerate Q hQ
  obtain ⟨U, _, _, _, Qa, ha, g⟩ := QuadraticForm.wittIndex_spec Q hrad
  set m := QuadraticForm.wittIndex Q with hm
  have hcount := valCount_wittDecomp Q Qa m g t
  have hdim : finrank F W = 2 * m + finrank F U := by
    obtain ⟨e⟩ := g
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype]
    simp [Module.finrank_prod]
    ring
  have h2 := finrank_le_two_of_anisotropic Qa ha
  obtain ⟨k, hk⟩ := hw
  have hU1 : finrank F U = 1 := by omega
  have hW : finrank F W = 2 * m + 1 := by omega
  have hℓ : (polarBilin (lineForm (-t))).Nondegenerate := lineForm_nondegenerate hF (neg_ne_zero.2 ht)
  have hrad2 : (Q.prod (lineForm (-t))).radical = ⊥ :=
    QuadraticForm.radical_eq_bot_of_nondegenerate _ (QuadraticForm.nondegenerate_polarBilin_prod hQ hℓ)
  have hfin : finrank F (W × F) = 2 * m + 2 := by
    rw [Module.finrank_prod, Module.finrank_self]; omega
  have hnodd : ¬ Odd (finrank F (W × F)) := by
    rw [hfin, Nat.odd_iff]; omega
  have e12 : (Q.prod (lineForm (-t))).IsometryEquiv
      ((QuadraticForm.hyperbolicSpace F m).prod (Qa.prod (lineForm (-t)))) :=
    (g.some.prod (QuadraticMap.IsometryEquiv.refl _)).trans (prodAssoc _ _ _)
  suffices H : chiGen (Q.prod (lineForm (-t))) = (valCount Qa t : ℝ) - 1 by
    have e1 : ((finrank F W : ℕ) : ℤ) - 1 = ((2 * m : ℕ) : ℤ) := by rw [hW]; push_cast; ring
    rw [hcount, H, e1, zpow_natCast, hU1, hW]
    have e2 : 2 * m + 1 - 1 = 2 * m := by omega
    have e3 : (2 * m) / 2 = m := by omega
    rw [e2, e3]
    simp only [Nat.cast_one, sub_self, zpow_zero]
    ring
  by_cases hex : ∃ u, Qa u = t
  · obtain ⟨u, hu⟩ := hex
    have hu0 : u ≠ 0 := by
      rintro rfl
      apply ht
      rw [← hu]
      exact map_zero _
    let j := lineIso Qa hu0 hU1 hu
    have hcnt : valCount Qa t = 2 := by
      rw [valCount_congr (⟨j.symm⟩ : Qa.Equivalent (lineForm t)) t]
      exact valCount_lineForm_self hF ht
    let Z : QuadraticForm F PUnit.{1} := 0
    have hZ : Z.Anisotropic := fun x _ => Subsingleton.elim _ _
    let eZ : (QuadraticForm.hyperbolicSpace F (m + 1)).IsometryEquiv
        ((QuadraticForm.hyperbolicSpace F (m + 1)).prod Z) :=
      { toLinearEquiv := (LinearEquiv.prodUnique (R := F) (M := Fin (m + 1) → F × F) (M₂ := PUnit.{1})).symm
        map_app' := fun x => by simp [Z] }
    let hyp := (lineForm_prod_neg_equiv hF ht).some
    let chain : (Q.prod (lineForm (-t))).IsometryEquiv
        ((QuadraticForm.hyperbolicSpace F (m + 1)).prod Z) :=
      e12.trans (((QuadraticMap.IsometryEquiv.refl _).prod
        ((j.symm.prod (QuadraticMap.IsometryEquiv.refl _)).trans hyp)).trans
        ((QuadraticMap.IsometryEquiv.prodComm _ _).trans ((hyperbolicSpaceSucc m).trans eZ)))
    have hwi : m + 1 = QuadraticForm.wittIndex (Q.prod (lineForm (-t))) :=
      QuadraticForm.eq_wittIndex _ hrad2 hZ ⟨chain⟩
    rw [chiGen, if_neg hnodd, if_pos (by rw [← hwi, hfin]; omega), hcnt]
    norm_num
  · have hcnt0 : valCount Qa t = 0 := by
      have : IsEmpty {x // Qa x = t} := ⟨fun ⟨u, hu⟩ => hex ⟨u, hu⟩⟩
      exact Nat.card_of_isEmpty
    have haa : (Qa.prod (lineForm (-t))).Anisotropic := by
      rintro ⟨u, s⟩ h
      simp only [QuadraticMap.prod_apply, lineForm_apply] at h
      by_cases hs : s = 0
      · subst hs
        simp only [mul_zero, add_zero] at h
        exact Prod.ext (ha u h) rfl
      · exfalso
        apply hex
        refine ⟨s⁻¹ • u, ?_⟩
        rw [QuadraticMap.map_smul, smul_eq_mul]
        have : Qa u = t * (s * s) := by linear_combination h
        rw [this]
        field_simp
    have hwi : m = QuadraticForm.wittIndex (Q.prod (lineForm (-t))) :=
      QuadraticForm.eq_wittIndex _ hrad2 haa ⟨e12⟩
    rw [chiGen, if_neg hnodd, if_neg (by rw [← hwi, hfin]; omega), hcnt0]
    norm_num

end QuadFormsKB.Kitaoka.FqCount
