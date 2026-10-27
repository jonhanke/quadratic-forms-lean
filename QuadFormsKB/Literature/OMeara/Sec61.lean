/-
# O'Meara §61A: quadratic spaces over the real field

**Setting.** O'Meara (1973 printing, §61, pp. 154–156) works over a *real complete field*, a field complete at a real
archimedean spot; such a field is topologically isomorphic to $\mathbb R$ (§12), and every notion below is invariant
under field isomorphisms, so the statements are made over `ℝ` itself. $(V, Q)$ is a finite-dimensional quadratic
space over $\mathbb R$ (Mathlib `QuadraticForm ℝ V`); *regular* means `Q.radical = ⊥`.

**Positive and negative indices.** O'Meara defines $\operatorname{ind}^{+}V$ as the common dimension of the maximal
positive definite subspaces of $V$ (p. 155). Mathlib's `QuadraticForm.sigPos Q` is the *largest* dimension of a
positive definite subspace, and `QuadraticForm.sigNeg Q = sigPos (-Q)`; the two definitions agree
(`finrank_eq_sigPos_of_maximal`, which is O'Meara's claim that all maximal positive definite subspaces have the same
dimension). So $\operatorname{ind}^{+}V$ is `sigPos Q` and $\operatorname{ind}^{-}V$ is `sigNeg Q` below. The Witt
index $\operatorname{ind}V$ of §42F is `QuadFormsKB.wittIndex Q` (`Witt/Decomposition.lean`).

**Defines** (§61A, p. 154) negative definite (`IsNegDef`), definite (`IsDefinite`) and indefinite (`IsIndefinite`)
spaces; *positive definite* is Mathlib's `QuadraticMap.PosDef` ($Q(x) > 0$ for $x \ne 0$), which is O'Meara's
definition ($Q(x) \in \dot F^{2}$ for $x \ne 0$) by `posDef_iff_isSquare`.

**Proves** (§61A, pp. 154–156)
* `posDef_iff_isSquare`: O'Meara's definition of positive definite;
* `exists_equivalent_one_neg_one` (p. 155): $V \cong \langle 1\rangle^{p} \perp \langle -1\rangle^{q}$ with
  $p = \operatorname{ind}^{+}V$, $q = \operatorname{ind}^{-}V$;
* `posDef_iff_sigPos_eq`, `isNegDef_iff_sigNeg_eq`, `isIndefinite_iff_sigPos_pos_sigNeg_pos`,
  `isIndefinite_iff_not_anisotropic` (p. 155): $V$ is positive definite iff $p = n$, negative definite iff $q = n$,
  indefinite iff $0 < p, q$, and indefinite iff isotropic;
* `range_eq_of_posDef`, `range_eq_of_isIndefinite`, `range_eq_of_isNegDef` (p. 155): $Q(V) = F^{2}$, $F$, $-F^{2}$;
* `posDef_restrict`, `radical_restrict_eq_bot_of_posDef`, `subsingleton_of_posDef_of_isNegDef` (p. 155);
* `finrank_eq_sigPos_of_maximal`, `finrank_eq_sigNeg_of_maximal` (p. 155): all maximal positive (negative) definite
  subspaces have dimension $\operatorname{ind}^{+}V$ ($\operatorname{ind}^{-}V$);
* `sigPos_add_sigNeg` and `wittIndex_eq_min` (p. 155): $\operatorname{ind}^{+}V + \operatorname{ind}^{-}V = \dim V$
  and $\operatorname{ind}V = \min(\operatorname{ind}^{+}V, \operatorname{ind}^{-}V)$;
* `isRepresentedBy_iff_sigPos_le` and `equivalent_iff_sigPos_eq` (Theorem 61:1, p. 156).
-/
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Witt.Decomposition

open QuadraticMap QuadraticForm Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {U : Type*} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]

/-! ### Definite and indefinite spaces -/

/-- **Negative definite** (O'Meara 1963, §61A, p. 154): $Q(x) \in -\dot F^{2}$, i.e. $Q(x) < 0$, for every
$x \ne 0$; equivalently $-Q$ is positive definite. -/
@[kb "omeara1963" "§61A, p. 154 (negative definite space)"]
def IsNegDef (Q : QuadraticForm ℝ V) : Prop := (-Q).PosDef

/-- **Definite** (O'Meara 1963, §61A, p. 154): positive definite or negative definite. -/
@[kb "omeara1963" "§61A, p. 154 (definite space)"]
def IsDefinite (Q : QuadraticForm ℝ V) : Prop := Q.PosDef ∨ IsNegDef Q

/-- **Indefinite** (O'Meara 1963, §61A, p. 154): not definite. -/
@[kb "omeara1963" "§61A, p. 154 (indefinite space)"]
def IsIndefinite (Q : QuadraticForm ℝ V) : Prop := ¬ IsDefinite Q

private lemma posDef_iff_restrict_top (Q : QuadraticForm ℝ V) :
    Q.PosDef ↔ (Q.restrict (⊤ : Submodule ℝ V)).PosDef := by
  constructor
  · intro h x hx
    have hx' : (x : V) ≠ 0 := by simpa using hx
    simpa [restrict_apply] using h (x : V) hx'
  · intro h x hx
    have := h (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule ℝ V)) (by simpa using hx)
    simpa [restrict_apply] using this

private lemma radical_eq_bot_of_posDef {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : QuadraticForm ℝ W} (h : Q.PosDef) : Q.radical = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  exact h.anisotropic x ((QuadraticMap.mem_radical_iff'.1 hx).1)

theorem isNegDef_iff (Q : QuadraticForm ℝ V) : IsNegDef Q ↔ ∀ x, x ≠ 0 → Q x < 0 := by
  simp [IsNegDef, QuadraticMap.PosDef]

/-- **O'Meara's definition of positive definite** (O'Meara 1963, §61A, p. 154): $V$ is positive definite if and only
if $Q(x) \in \dot F^{2}$ (a nonzero square) for every $x \ne 0$. -/
@[kb "omeara1963" "§61A, p. 154 (positive definite: Q(x) a nonzero square for x ≠ 0)"]
theorem posDef_iff_isSquare (Q : QuadraticForm ℝ V) :
    Q.PosDef ↔ ∀ x, x ≠ 0 → IsSquare (Q x) ∧ Q x ≠ 0 := by
  constructor
  · intro h x hx
    have := h x hx
    exact ⟨⟨Real.sqrt (Q x), (Real.mul_self_sqrt this.le).symm⟩, this.ne'⟩
  · intro h x hx
    obtain ⟨⟨r, hr⟩, hne⟩ := h x hx
    have : 0 ≤ Q x := by rw [hr]; exact mul_self_nonneg r
    exact lt_of_le_of_ne this (Ne.symm hne)

/-! ### The normal form and the indices -/

private lemma wss_equivalent_of_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (w : ι → ℝ) (w' : ι' → ℝ) (h : ∀ i, w' (e i) = w i) :
    (weightedSumSquares ℝ w).Equivalent (weightedSumSquares ℝ w') := by
  refine ⟨{ toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ e.symm, map_app' := ?_ }⟩
  intro x
  simp only [weightedSumSquares_apply]
  rw [← Equiv.sum_comp e]
  simp [h, LinearEquiv.funCongrLeft_apply]

private lemma radical_eq_bot_imp_sep (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    (associated (R := ℝ) Q).SeparatingLeft := by
  intro x hx
  have : x ∈ Q.radical := by
    rw [radical_eq_ker_associated, LinearMap.mem_ker]
    ext y
    exact hx y
  rw [hQ] at this
  simpa using this

/-- **Sylvester's normal form** (O'Meara 1963, §61A, pp. 154–155): a regular real quadratic space has an orthogonal
base $x_1, \dots, x_p, y_1, \dots, y_q$ with $Q(x_i) = 1$ and $Q(y_j) = -1$, i.e.
$V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle -1\rangle \perp \cdots \perp
\langle -1\rangle$, and then $p = \operatorname{ind}^{+}V$ (`sigPos`), $q = \operatorname{ind}^{-}V$ (`sigNeg`). The
model space is $\mathbb R^{p} \times \mathbb R^{q}$, indexed by `Fin p ⊕ Fin q`. -/
@[kb "omeara1963" "§61A, pp. 154–155 (V ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨1⟩ ⊥ ⟨−1⟩ ⊥ ⋯ ⊥ ⟨−1⟩, p = ind⁺V, q = ind⁻V)"]
theorem exists_equivalent_one_neg_one (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    Q.Equivalent (weightedSumSquares ℝ
      (Sum.elim (fun _ : Fin (sigPos Q) => (1 : ℝ)) (fun _ : Fin (sigNeg Q) => (-1 : ℝ)))) := by
  classical
  obtain ⟨w, hw, e⟩ := equivalent_one_neg_one_weighted_sum_squared Q (radical_eq_bot_imp_sep Q hQ)
  have hp : sigPos Q = {i | 0 < w i}.ncard := sigPos_of_equiv_weightedSumSquares e
  have hq : sigNeg Q = {i | w i < 0}.ncard := sigNeg_of_equiv_weightedSumSquares e
  have hset : {i | w i < 0} = {i | ¬ 0 < w i} := by
    ext i; rcases hw i with h | h <;> simp [h]; norm_num
  have h1 : Fintype.card {i // 0 < w i} = sigPos Q := by
    rw [hp, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]; rfl
  have h2 : Fintype.card {i // ¬ 0 < w i} = sigNeg Q := by
    rw [hq, hset, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]; rfl
  let f := (Equiv.sumCompl (fun i => 0 < w i)).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq h1) (Fintype.equivFinOfCardEq h2))
  refine e.trans (wss_equivalent_of_equiv f w _ ?_)
  intro i
  by_cases hi : 0 < w i
  · have : w i = 1 := by rcases hw i with h | h <;> [linarith; exact h]
    simp [f, this]
  · have : w i = -1 := by rcases hw i with h | h <;> [exact h; linarith]
    simp [f, this]

/-- **$\operatorname{ind}^{+}V + \operatorname{ind}^{-}V = \dim V$** for a regular space (O'Meara 1963, §61A,
p. 155). -/
@[kb "omeara1963" "§61A, p. 155 (ind⁺V + ind⁻V = dim V)"]
theorem sigPos_add_sigNeg (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    sigPos Q + sigNeg Q = finrank ℝ V := by
  have := sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hQ] at this
  simpa using this

/-- **$V$ is positive definite if and only if $p = n$** (O'Meara 1963, §61A, p. 155), i.e.
$\operatorname{ind}^{+}V = \dim V$. -/
@[kb "omeara1963" "§61A, p. 155 (positive definite iff p = n)"]
theorem posDef_iff_sigPos_eq (Q : QuadraticForm ℝ V) : Q.PosDef ↔ sigPos Q = finrank ℝ V := by
  constructor
  · intro h
    have hP := (posDef_iff_restrict_top Q).1 h
    have := le_sigPos_of_posDef Q hP
    rw [finrank_top] at this
    exact le_antisymm (sigPos_le_finrank Q) this
  · intro h
    obtain ⟨W, hW, hpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have : W = ⊤ := Submodule.eq_top_of_finrank_eq (hW.trans h)
    subst this
    exact (posDef_iff_restrict_top Q).2 hpos

/-- **$V$ is negative definite if and only if $q = n$** (O'Meara 1963, §61A, p. 155), i.e.
$\operatorname{ind}^{-}V = \dim V$. -/
@[kb "omeara1963" "§61A, p. 155 (negative definite iff q = n)"]
theorem isNegDef_iff_sigNeg_eq (Q : QuadraticForm ℝ V) : IsNegDef Q ↔ sigNeg Q = finrank ℝ V := by
  exact posDef_iff_sigPos_eq (-Q)

private lemma exists_isotropic_of_pos_neg (Q : QuadraticForm ℝ V) {x y : V} (hx : 0 < Q x)
    (hy : Q y < 0) : ∃ z, z ≠ 0 ∧ Q z = 0 := by
  have hq : ∀ t : ℝ, Q (x + t • y) = Q y * t * t + polar Q x y * t + Q x := by
    intro t
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_right]; ring
  set b := polar Q x y
  have hd : 0 ≤ discrim (Q y) b (Q x) := by
    unfold discrim
    nlinarith [sq_nonneg b, mul_pos hx (neg_pos.2 hy)]
  have hs : discrim (Q y) b (Q x) = Real.sqrt (discrim (Q y) b (Q x)) * Real.sqrt (discrim (Q y) b (Q x)) :=
    (Real.mul_self_sqrt hd).symm
  have hroot := (quadratic_eq_zero_iff (ne_of_lt hy) hs
    ((-b + Real.sqrt (discrim (Q y) b (Q x))) / (2 * Q y))).2 (Or.inl rfl)
  set t := (-b + Real.sqrt (discrim (Q y) b (Q x))) / (2 * Q y)
  refine ⟨x + t • y, ?_, by rw [hq]; linarith [hroot, mul_assoc (Q y) t t]⟩
  intro hz
  have hxe : x = (-t) • y := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hz
  have : Q x = (-t) * (-t) * Q y := by rw [hxe, QuadraticMap.map_smul, smul_eq_mul]
  nlinarith [mul_self_nonneg t]

private lemma isDefinite_of_anisotropic {Q : QuadraticForm ℝ V} (ha : Q.Anisotropic) :
    IsDefinite Q := by
  by_contra hnd
  simp only [IsDefinite, not_or] at hnd
  obtain ⟨h1, h2⟩ := hnd
  have h1' : ∃ x, x ≠ 0 ∧ Q x < 0 := by
    by_contra hc
    push Not at hc
    apply h1
    intro x hx
    rcases lt_or_eq_of_le (hc x hx) with h | h
    · exact h
    · exact absurd (ha x h.symm) hx
  have h2' : ∃ y, y ≠ 0 ∧ 0 < Q y := by
    by_contra hc
    push Not at hc
    apply h2
    show (-Q).PosDef
    intro y hy
    rcases lt_or_eq_of_le (hc y hy) with h | h
    · simpa using h
    · exact absurd (ha y h) hy
  obtain ⟨x, hx, hxn⟩ := h1'
  obtain ⟨y, hy, hyp⟩ := h2'
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_of_pos_neg Q hyp hxn
  exact hz (ha z hz0)

/-- **A regular space is indefinite if and only if $0 < p$ and $0 < q$** (O'Meara 1963, §61A, p. 155; the book's
"$0 < p < n$"). -/
@[kb "omeara1963" "§61A, p. 155 (indefinite iff 0 < p < n)"]
theorem isIndefinite_iff_sigPos_pos_sigNeg_pos (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    IsIndefinite Q ↔ 0 < sigPos Q ∧ 0 < sigNeg Q := by
  have hs := sigPos_add_sigNeg Q hQ
  rw [IsIndefinite, IsDefinite, posDef_iff_sigPos_eq, isNegDef_iff_sigNeg_eq]
  omega

/-- **$V$ is indefinite if and only if it is isotropic** (O'Meara 1963, §61A, p. 155). O'Meara states it for regular
spaces; it holds for every real quadratic space (a nonzero radical vector is isotropic, and a degenerate space is not
definite). -/
@[kb "omeara1963" "§61A, p. 155 (V is indefinite if and only if it is isotropic)"]
theorem isIndefinite_iff_not_anisotropic (Q : QuadraticForm ℝ V) : IsIndefinite Q ↔ ¬ Q.Anisotropic := by
  constructor
  · exact fun hI h => hI (isDefinite_of_anisotropic h)
  · intro hna hdef
    apply hna
    rcases hdef with h | h
    · exact h.anisotropic
    · intro x hx
      exact (show (-Q).PosDef from h).anisotropic x (by simpa using hx)

/-! ### The values $Q(V)$ -/

/-- **$Q(V) = F^{2}$ for a positive definite $V \ne 0$** (O'Meara 1963, §61A, p. 155): the values of $Q$ are the
squares, i.e. the nonnegative reals. (For $V = 0$ the only value is $0$.) -/
@[kb "omeara1963" "§61A, p. 155 (Q(V) = F² for positive definite V)"]
theorem range_eq_of_posDef (Q : QuadraticForm ℝ V) [Nontrivial V] (hQ : Q.PosDef) :
    Set.range Q = Set.Ici 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' := hQ v hv
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact hQ.nonneg x
  · intro ha
    refine ⟨Real.sqrt (a / Q v) • v, ?_⟩
    rw [QuadraticMap.map_smul, Real.mul_self_sqrt (div_nonneg ha hv'.le)]
    simp only [smul_eq_mul]
    field_simp

/-- **$Q(V) = F$ for an indefinite regular $V$** (O'Meara 1963, §61A, p. 155): $V$ is universal. -/
@[kb "omeara1963" "§61A, p. 155 (Q(V) = F for indefinite V)"]
theorem range_eq_of_isIndefinite (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) (h : IsIndefinite Q) :
    Set.range Q = Set.univ := by
  have hna : ¬ Q.Anisotropic := (isIndefinite_iff_not_anisotropic Q).1 h
  obtain ⟨z, hz, hz0⟩ := (QuadraticMap.not_anisotropic_iff_exists Q).1 hna
  have hex : ∃ w, polar Q z w ≠ 0 := by
    by_contra hc
    push Not at hc
    have hz' : z ∈ Q.radical := by
      rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
      ext y
      exact hc y
    rw [hQ] at hz'
    exact hz (by simpa using hz')
  obtain ⟨w, hw⟩ := hex
  ext a
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨((a - Q w) / polar Q z w) • z + w, ?_⟩
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hz0, QuadraticMap.polar_smul_left]
  have hc : (a - Q w) / polar Q z w * polar Q z w = a - Q w := div_mul_cancel₀ _ hw
  simp only [smul_eq_mul, mul_zero, zero_add]
  linarith [hc]

/-- **$Q(V) = -F^{2}$ for a negative definite $V \ne 0$** (O'Meara 1963, §61A, p. 155). -/
@[kb "omeara1963" "§61A, p. 155 (Q(V) = −F² for negative definite V)"]
theorem range_eq_of_isNegDef (Q : QuadraticForm ℝ V) [Nontrivial V] (hQ : IsNegDef Q) :
    Set.range Q = Set.Iic 0 := by
  have h := range_eq_of_posDef (-Q) hQ
  ext a
  have : a ∈ Set.range Q ↔ -a ∈ Set.range (-Q) := by
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩; exact ⟨x, by simpa using hx⟩
  rw [this, h]
  simp

/-! ### Subspaces of definite spaces -/

/-- **Every subspace of a positive definite space is positive definite** (O'Meara 1963, §61A, p. 155). -/
@[kb "omeara1963" "§61A, p. 155 (subspaces of a positive definite space are positive definite)"]
theorem posDef_restrict {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) (W : Submodule ℝ V) : (Q.restrict W).PosDef := by
  intro x hx
  have hx' : (x : V) ≠ 0 := by simpa using hx
  simpa [restrict_apply] using hQ (x : V) hx'

/-- **Every subspace of a positive definite space is regular** (O'Meara 1963, §61A, p. 155). -/
@[kb "omeara1963" "§61A, p. 155 (subspaces of a positive definite space are regular)"]
theorem radical_restrict_eq_bot_of_posDef {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) (W : Submodule ℝ V) :
    (Q.restrict W).radical = ⊥ := by
  exact radical_eq_bot_of_posDef (posDef_restrict hQ W)

/-- **The same for negative definite spaces** (O'Meara 1963, §61A, p. 155, "similarly with negative definite
spaces"). -/
@[kb "omeara1963" "§61A, p. 155 (subspaces of a negative definite space)"]
theorem isNegDef_restrict {Q : QuadraticForm ℝ V} (hQ : IsNegDef Q) (W : Submodule ℝ V) :
    IsNegDef (Q.restrict W) ∧ (Q.restrict W).radical = ⊥ := by
  have h : IsNegDef (Q.restrict W) := by
    rw [isNegDef_iff]
    intro x hx
    have hx' : (x : V) ≠ 0 := by simpa using hx
    simpa [restrict_apply] using (isNegDef_iff Q).1 hQ (x : V) hx'
  refine ⟨h, ?_⟩
  have h2 : (-(Q.restrict W)).PosDef := h
  have := radical_eq_bot_of_posDef h2
  have e : (-(Q.restrict W)).radical = (Q.restrict W).radical := by
    ext x; simp [QuadraticMap.mem_radical_iff']
  rwa [e] at this

/-- **The only space that is both positive and negative definite is $0$** (O'Meara 1963, §61A, p. 155). -/
@[kb "omeara1963" "§61A, p. 155 (only the zero space is both positive and negative definite)"]
theorem subsingleton_of_posDef_of_isNegDef {Q : QuadraticForm ℝ V} (h₁ : Q.PosDef) (h₂ : IsNegDef Q) :
    Subsingleton V := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : V, z = 0 := fun z => by
    by_contra hz
    have h1 := h₁ z hz
    have h2 := (isNegDef_iff Q).1 h₂ z hz
    linarith
  rw [key x, key y]

/-! ### Maximal definite subspaces -/

private lemma radical_neg_eq {W : Type*} [AddCommGroup W] [Module ℝ W] (Q : QuadraticForm ℝ W) :
    (-Q).radical = Q.radical := by
  ext x; simp [QuadraticMap.mem_radical_iff']

private lemma restrict_neg_eq (Q : QuadraticForm ℝ V) (P : Submodule ℝ V) :
    (-Q).restrict P = -(Q.restrict P) := by
  ext x; simp [restrict_apply]

private lemma nondegenerate_polarBilin_of_radical (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    (polarBilin Q).Nondegenerate := by
  rw [nondegenerate_polarBilin_iff]
  intro v hv
  have : v ∈ Q.radical := by
    rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
    ext y
    exact hv y
  rw [hQ] at this
  simpa using this

/-- **All maximal positive definite subspaces have the same dimension $\operatorname{ind}^{+}V$** (O'Meara 1963,
§61A, p. 155): a positive definite subspace $P$ of a regular space $V$ that is contained in no strictly larger
positive definite subspace has $\dim P$ = `sigPos Q`. This identifies O'Meara's definition of the positive index
with Mathlib's `sigPos` (the largest dimension of a positive definite subspace). O'Meara proves it with Witt's
theorem; the proof here bounds $\dim P$ through the negative semidefinite orthogonal complement of $P$. -/
@[kb "omeara1963" "§61A, p. 155 (all maximal positive definite subspaces have dimension ind⁺V)"]
theorem finrank_eq_sigPos_of_maximal (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) (P : Submodule ℝ V)
    (hP : (Q.restrict P).PosDef) (hmax : ∀ P' : Submodule ℝ V, P ≤ P' → (Q.restrict P').PosDef → P' = P) :
    finrank ℝ P = sigPos Q := by
  have hB := nondegenerate_polarBilin_of_radical Q hQ
  have hneg : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P, Q x ≤ 0 := by
    intro x hx
    by_contra hpos
    push Not at hpos
    have hperp : ∀ p ∈ P, polar Q p x = 0 := by
      intro p hp
      have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) p hp
      simpa using this
    have hPos' : (Q.restrict (P ⊔ ℝ ∙ x)).PosDef := by
      intro u hu0
      obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.1 u.2
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [restrict_apply]
      have hu' : (u : V) = p + c • x := hpy.symm
      rw [hu', QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
        hperp p hp]
      simp only [smul_eq_mul, mul_zero, add_zero]
      have hcc : 0 ≤ c * c * Q x := mul_nonneg (mul_self_nonneg c) hpos.le
      by_cases hp0 : p = 0
      · subst hp0
        have hc : c ≠ 0 := by
          rintro rfl
          exact hu0 (Subtype.ext (by simp [hu']))
        have := mul_pos (mul_self_pos.2 hc) hpos
        simpa using this
      · have h1 := hP ⟨p, hp⟩ (by simpa using hp0)
        simp only [restrict_apply] at h1
        linarith
    have hxP : x ∈ P := by
      have := hmax _ le_sup_left hPos'
      rw [← this]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have h0 := hperp x hxP
    rw [QuadraticMap.polar_self] at h0
    simp at h0
    linarith
  have h1 := sigPos_add_finrank_le_of_nonpos hneg
  have h2 := LinearMap.BilinForm.finrank_orthogonal hB P
  have h3 : finrank ℝ P ≤ finrank ℝ V := Submodule.finrank_le P
  have h4 := le_sigPos_of_posDef Q hP
  omega

/-- **All maximal negative definite subspaces have the same dimension $\operatorname{ind}^{-}V$** (O'Meara 1963,
§61A, p. 155, "similarly define the negative index"). -/
@[kb "omeara1963" "§61A, p. 155 (all maximal negative definite subspaces have dimension ind⁻V)"]
theorem finrank_eq_sigNeg_of_maximal (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) (P : Submodule ℝ V)
    (hP : IsNegDef (Q.restrict P)) (hmax : ∀ P' : Submodule ℝ V, P ≤ P' → IsNegDef (Q.restrict P') → P' = P) :
    finrank ℝ P = sigNeg Q := by
  have h := finrank_eq_sigPos_of_maximal (-Q) (by rw [radical_neg_eq]; exact hQ) P
    (by rw [restrict_neg_eq]; exact hP)
    (fun P' hle hP' => hmax P' hle (by rw [restrict_neg_eq] at hP'; exact hP'))
  simpa using h

private lemma finrank_le_sigPos_of_inj {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] (Q : QuadraticForm ℝ W)
    (σ : A →ₗ[ℝ] W) (hσ : Function.Injective σ) (hA : ∀ a, a ≠ 0 → 0 < Q (σ a)) :
    finrank ℝ A ≤ sigPos Q := by
  have hpos : (Q.restrict (LinearMap.range σ)).PosDef := by
    intro u hu
    obtain ⟨a, ha⟩ := u.2
    rw [restrict_apply, ← ha]
    apply hA
    rintro rfl
    apply hu
    apply Subtype.ext
    simp [← ha]
  have := le_sigPos_of_posDef Q hpos
  rwa [LinearMap.finrank_range_of_inj hσ] at this

private lemma sigPos_le_of_inj {QU : QuadraticForm ℝ U} {Q : QuadraticForm ℝ V} (σ : U →ₗ[ℝ] V)
    (hσ : Function.Injective σ) (h : ∀ x, Q (σ x) = QU x) : sigPos QU ≤ sigPos Q := by
  obtain ⟨P, hP, hpos⟩ := exists_finrank_eq_sigPos_and_posDef QU
  rw [← hP]
  refine finrank_le_sigPos_of_inj Q (σ.comp P.subtype) (hσ.comp P.injective_subtype) ?_
  intro a ha
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, h]
  simpa [restrict_apply] using hpos a ha

private lemma sigPos_add_le_sigPos_prod {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℝ W₁]
    [FiniteDimensional ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂] [FiniteDimensional ℝ W₂]
    (Q₁ : QuadraticForm ℝ W₁) (Q₂ : QuadraticForm ℝ W₂) :
    sigPos Q₁ + sigPos Q₂ ≤ sigPos (Q₁.prod Q₂) := by
  obtain ⟨P₁, h₁, p₁⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
  obtain ⟨P₂, h₂, p₂⟩ := exists_finrank_eq_sigPos_and_posDef Q₂
  have key := finrank_le_sigPos_of_inj (Q₁.prod Q₂) (P₁.subtype.prodMap P₂.subtype)
    (fun x y h => Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h)))
    (by
      rintro ⟨a, b⟩ hab
      simp only [LinearMap.prodMap_apply, Submodule.subtype_apply, QuadraticMap.prod_apply]
      have ha : 0 ≤ Q₁ a := by
        by_cases h : a = 0
        · simp [h]
        · have := p₁ a (by simpa using h)
          simpa [restrict_apply] using this.le
      have hb : 0 ≤ Q₂ b := by
        by_cases h : b = 0
        · simp [h]
        · have := p₂ b (by simpa using h)
          simpa [restrict_apply] using this.le
      by_cases h : a = 0
      · subst h
        have hb0 : b ≠ 0 := by rintro rfl; exact hab rfl
        have := p₂ b hb0
        simp only [restrict_apply] at this
        simpa using this
      · have := p₁ a h
        simp only [restrict_apply] at this
        linarith)
  rwa [Module.finrank_prod, h₁, h₂] at key

private lemma hyperbolicSpace_le_sigPos (m : ℕ) : m ≤ sigPos (hyperbolicSpace ℝ m) := by
  have key := finrank_le_sigPos_of_inj (hyperbolicSpace ℝ m)
    (LinearMap.pi fun i : Fin m => (LinearMap.proj i).prod (LinearMap.proj i))
    (fun a b h => funext fun i => by simpa using congrArg Prod.fst (congrFun h i))
    (by
      intro a ha
      simp only [hyperbolicSpace_apply, LinearMap.pi_apply, LinearMap.prod_apply,
        LinearMap.coe_proj]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩)
  simpa using key

private lemma hyperbolicSpace_le_sigNeg (m : ℕ) : m ≤ sigNeg (hyperbolicSpace ℝ m) := by
  let σ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ × ℝ) :=
    LinearMap.pi fun i : Fin m => (LinearMap.proj i).prod (-(LinearMap.proj i))
  have key := finrank_le_sigPos_of_inj (-(hyperbolicSpace ℝ m)) σ
    (fun a b h => funext fun i => by simpa [σ] using congrArg Prod.fst (congrFun h i))
    (by
      intro a ha
      obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
      have : (-(hyperbolicSpace ℝ m)) (σ a) = ∑ j, a j * a j := by
        simp [σ, hyperbolicSpace_apply, Finset.sum_neg_distrib]
      rw [this]
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩)
  simpa using key

/-- **$\operatorname{ind}V = \min(\operatorname{ind}^{+}V, \operatorname{ind}^{-}V)$** (O'Meara 1963, §61A, p. 155):
the Witt index of a regular real space (the number of hyperbolic planes in a Witt decomposition, §42F) is the
smaller of its two indices. -/
@[kb "omeara1963" "§61A, p. 155 (ind V = min(ind⁺V, ind⁻V))"]
theorem wittIndex_eq_min {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : Q.radical = ⊥) :
    wittIndex Q = min (sigPos Q) (sigNeg Q) := by
  obtain ⟨U, _, _, _, Qa, ha, e⟩ := wittIndex_spec Q hQ
  have hQa : Qa.radical = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact ha x ((QuadraticMap.mem_radical_iff'.1 hx).1)
  have hsa := sigPos_add_sigNeg Qa hQa
  have hsQ := sigPos_add_sigNeg Q hQ
  have hdim : finrank ℝ V = 2 * wittIndex Q + finrank ℝ U := by
    obtain ⟨e'⟩ := e
    rw [e'.toLinearEquiv.finrank_eq, Module.finrank_prod]
    simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_comm]
  have hP : wittIndex Q + sigPos Qa ≤ sigPos Q := by
    rw [e.sigPos_eq]
    exact (Nat.add_le_add_right (hyperbolicSpace_le_sigPos _) _).trans
      (sigPos_add_le_sigPos_prod _ _)
  have hN : wittIndex Q + sigNeg Qa ≤ sigNeg Q := by
    rw [e.sigNeg_eq]
    have h := sigPos_add_le_sigPos_prod (-(hyperbolicSpace ℝ (wittIndex Q))) (-Qa)
    have hneg : (-(hyperbolicSpace ℝ (wittIndex Q))).prod (-Qa) =
        -((hyperbolicSpace ℝ (wittIndex Q)).prod Qa) := by
      ext x; simp; ring
    rw [hneg] at h
    have h2 := hyperbolicSpace_le_sigNeg (wittIndex Q)
    simp only [sigPos_neg] at h
    omega
  have hdef : sigPos Qa = 0 ∨ sigNeg Qa = 0 := by
    rcases isDefinite_of_anisotropic ha with h | h
    · right; have := (posDef_iff_sigPos_eq Qa).1 h; omega
    · left; have := (isNegDef_iff_sigNeg_eq Qa).1 h; omega
  omega

/-! ### Theorem 61:1 -/

private noncomputable abbrev NF (p q : ℕ) : QuadraticForm ℝ (Fin p ⊕ Fin q → ℝ) :=
  weightedSumSquares ℝ (Sum.elim (fun _ : Fin p => (1 : ℝ)) (fun _ : Fin q => (-1 : ℝ)))

private lemma NF_equivalent_of_eq {p p' q q' : ℕ} (hp : p = p') (hq : q = q') :
    (NF p q).Equivalent (NF p' q') := by
  subst hp hq
  exact Equivalent.refl _

private lemma isRepresentedBy_NF {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') :
    IsRepresentedBy (NF p q) (NF p' q') := by
  let s : Fin p ⊕ Fin q → Fin p' ⊕ Fin q' := Sum.map (Fin.castLE hp) (Fin.castLE hq)
  have hs : Function.Injective s := (Fin.castLE_injective hp).sumMap (Fin.castLE_injective hq)
  refine ⟨⟨Function.ExtendByZero.linearMap ℝ ℝ s, ?_⟩, ?_⟩
  · intro x
    simp only [weightedSumSquares_apply]
    refine (Fintype.sum_of_injective s hs _ _ ?_ ?_).symm
    · intro j hj
      have : ¬ ∃ a, s a = j := by simpa using hj
      simp [Function.extend_apply' _ _ _ this]
    · intro i
      have e : (Function.ExtendByZero.linearMap ℝ ℝ s).toFun x (s i) = x i :=
        hs.extend_apply x 0 i
      rw [e]
      rcases i with i | i <;> simp [s]
  · intro x y hxy
    exact Function.extend_injective hs 0 hxy

/-- **Theorem 61:1, representation part** (O'Meara 1963, p. 156): a regular space $U$ is represented by a regular
space $V$ over the real field if and only if $\operatorname{ind}^{+}U \le \operatorname{ind}^{+}V$ and
$\operatorname{ind}^{-}U \le \operatorname{ind}^{-}V$. (O'Meara: "the proof is almost trivial and the details are
omitted".) -/
@[kb "omeara1963" "§61A, 61:1, p. 156 (representation: ind⁺U ≤ ind⁺V and ind⁻U ≤ ind⁻V)"]
theorem isRepresentedBy_iff_sigPos_le (QU : QuadraticForm ℝ U) (Q : QuadraticForm ℝ V) (hU : QU.radical = ⊥)
    (hV : Q.radical = ⊥) :
    IsRepresentedBy QU Q ↔ sigPos QU ≤ sigPos Q ∧ sigNeg QU ≤ sigNeg Q := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨sigPos_le_of_inj σ.toLinearMap hσ (fun x => σ.map_app x), ?_⟩
    have := sigPos_le_of_inj (QU := -QU) (Q := -Q) σ.toLinearMap hσ
      (fun x => by simp [σ.map_app x])
    simpa using this
  · rintro ⟨h1, h2⟩
    have eU := exists_equivalent_one_neg_one QU hU
    have eV := exists_equivalent_one_neg_one Q hV
    exact (IsRepresentedBy.of_equivalent eU).trans
      ((isRepresentedBy_NF h1 h2).trans (IsRepresentedBy.of_equivalent eV.symm))

/-- **Theorem 61:1, isometry part** (O'Meara 1963, p. 156): regular real spaces $U$, $V$ are isometric if and only if
$\operatorname{ind}^{+}U = \operatorname{ind}^{+}V$ and $\operatorname{ind}^{-}U = \operatorname{ind}^{-}V$. -/
@[kb "omeara1963" "§61A, 61:1, p. 156 (isometry: ind⁺U = ind⁺V and ind⁻U = ind⁻V)"]
theorem equivalent_iff_sigPos_eq (QU : QuadraticForm ℝ U) (Q : QuadraticForm ℝ V) (hU : QU.radical = ⊥)
    (hV : Q.radical = ⊥) :
    QU.Equivalent Q ↔ sigPos QU = sigPos Q ∧ sigNeg QU = sigNeg Q := by
  constructor
  · intro h
    exact ⟨h.sigPos_eq, h.sigNeg_eq⟩
  · rintro ⟨h1, h2⟩
    have eU := exists_equivalent_one_neg_one QU hU
    have eV := exists_equivalent_one_neg_one Q hV
    exact eU.trans ((NF_equivalent_of_eq h1 h2).trans eV.symm)

end QuadFormsKB.OMeara
