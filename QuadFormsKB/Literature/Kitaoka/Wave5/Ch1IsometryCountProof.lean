/-
# Kitaoka 1993, Theorem 1.3.2 in odd characteristic: the number of isometries over $\mathbb F_q$, $q$ odd

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, Theorem 1.3.2, p. 16, and the claim in its
proof, pp. 16–17 (printed pages). The statement `Kitaoka.FqCount.Theorem132` is in `Ch1IsometryCount.lean`.

**Proves** `theorem132_odd`: `Theorem132` for every finite field of odd characteristic (unconditional). The case of
characteristic $2$ (where $V$ is an orthogonal sum of planes and Kitaoka computes $r(V, W)$ for planes $V$) is not
covered; it is recorded as a loose end.

**Proof** (Kitaoka's induction on $v = \dim V$). Pick $x_0 \in V$ with $t = Q(x_0) \ne 0$; then
$V \cong \langle t\rangle \perp V_1$ with $V_1 = x_0^\perp$ regular (`orthSplit`). An isometry
$\sigma : \langle t\rangle \perp V_1 \to W$ is the same as a vector $x = \sigma(1, 0)$ with $Q(x) = t$ and an isometry
$V_1 \to x^\perp$ (`fiberEquiv`), so $r(V, W) = \sum_{Q(x) = t} r(V_1, x^\perp)$. For each such $x$,
$\langle t\rangle \perp x^\perp \cong W$, hence $\chi(x^\perp) = \chi(W \perp \langle -t\rangle)$ and
$\chi(V_1 \perp x^{\perp(-1)}) = \chi(V \perp W^{(-1)})$ (cancel $\langle t\rangle \perp \langle -t\rangle \cong H$), so
by induction every summand is the same number and $r(V, W) = a(t, W)\,r'(v - 1, w - 1)$. The counts
$a(t, W)$ are Lemma 1.3.2 ($w$ even) and `valCount_odd` ($w$ odd); the formula then follows by algebra
(`rForm_step_even`, `rForm_step_odd`).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1IsometryCount
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1IsometryCountLemmas

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

/-! ### The formula -/

/-- Kitaoka's $r'(V, W)$ as a function of $q$, $v$, $w$, $\chi(W)$ and $\chi(V \perp W^{(-1)})$. -/
def rForm (q : ℝ) (v w : ℕ) (cW c : ℝ) : ℝ :=
  q ^ ((v * w : ℤ) - (v * (v + 1) / 2 : ℕ)) * (1 - cW * q ^ (-(w : ℝ) / 2)) *
    (1 + c * q ^ (((v : ℝ) - w) / 2)) * ∏ e ∈ (Finset.Icc (w - v + 1) (w - 1)).filter Even, (1 - q ^ (-(e : ℤ)))

/-- $q^{-(k+k)/2} = (q^k)^{-1}$ (a real power with an integral exponent). -/
theorem half_rpow {q : ℝ} (hq : 0 < q) (k : ℕ) : q ^ (-((k + k : ℕ) : ℝ) / 2) = (q ^ k)⁻¹ := by
  rw [show (-((k + k : ℕ) : ℝ) / 2) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hq.le, Real.rpow_natCast]

/-- $\frac{(v+1)(v+2)}{2} = \frac{v(v+1)}{2} + (v + 1)$. -/
theorem tri_succ (v : ℕ) : (v + 1) * (v + 1 + 1) / 2 = v * (v + 1) / 2 + (v + 1) := by
  rw [show (v + 1) * (v + 1 + 1) = v * (v + 1) + 2 * (v + 1) by ring, Nat.add_mul_div_left _ _ two_pos]

/-- $v = 1$, $w$ even: $r'(1, w) = q^{w-1}(1 - \chi(W)q^{-w/2})$. -/
theorem rForm_one_even {q : ℝ} (hq : 0 < q) {w : ℕ} (hw : Even w) (cW : ℝ) :
    rForm q 1 w cW 0 = q ^ ((w : ℤ) - 1) * (1 - cW * q ^ (-((w / 2 : ℕ) : ℤ))) := by
  obtain ⟨k, rfl⟩ := hw
  have hempty : (Finset.Icc (k + k - 1 + 1) (k + k - 1)).filter Even = ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
    omega
  unfold rForm
  rw [hempty, half_rpow hq, show (k + k) / 2 = k by omega]
  simp only [Finset.prod_empty, mul_one, zero_mul, add_zero, zpow_neg, zpow_natCast]
  congr 2
  push_cast
  ring

/-- $v = 1$, $w$ odd: $r'(1, w) = q^{w-1} + c\,q^{(w-1)/2}$. -/
theorem rForm_one_odd {q : ℝ} (hq : 0 < q) {w : ℕ} (hw : Odd w) (c : ℝ) :
    rForm q 1 w 0 c = q ^ (w - 1) + c * q ^ ((w - 1) / 2) := by
  obtain ⟨k, rfl⟩ := hw
  have hempty : (Finset.Icc (2 * k + 1 - 1 + 1) (2 * k + 1 - 1)).filter Even = ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
    omega
  have hr : q ^ ((((1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ)) / 2) = (q ^ k)⁻¹ := by
    rw [show (((1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ)) / 2 = -(k : ℝ) by push_cast; ring, Real.rpow_neg hq.le,
      Real.rpow_natCast]
  have he : ((1 * (2 * k + 1) : ℕ) : ℤ) - ((1 * (1 + 1) / 2 : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  unfold rForm
  rw [hempty, hr]
  simp only [Finset.prod_empty, mul_one, zero_mul, sub_zero, Nat.cast_one, one_mul]
  rw [show (2 * k + 1 - 1) = 2 * k by omega, show 2 * k / 2 = k by omega]
  have he' : ((2 * k + 1 : ℕ) : ℤ) - ((1 + 1) / 2 : ℕ) = ((2 * k : ℕ) : ℤ) := by push_cast; norm_num
  rw [he', zpow_natCast]
  have hqk : q ^ k ≠ 0 := pow_ne_zero _ hq.ne'
  rw [pow_mul]
  field_simp
  ring

/-- The induction step for $w$ even: $a(t, W)\,r'(v, w - 1) = r'(v + 1, w)$ with
$a(t, W) = q^{w-1}(1 - \chi(W)q^{-w/2})$ and $\chi(x^\perp) = 0$. -/
theorem rForm_step_even {q : ℝ} (hq : 0 < q) {v w : ℕ} (hv : 1 ≤ v) (hvw : v + 1 ≤ w) (hw : Even w)
    (cW c : ℝ) :
    q ^ ((w : ℤ) - 1) * (1 - cW * q ^ (-((w / 2 : ℕ) : ℤ))) * rForm q v (w - 1) 0 c = rForm q (v + 1) w cW c := by
  have hw1 : 1 ≤ w := by omega
  have hP : (Finset.Icc (w - 1 - v + 1) (w - 1 - 1)).filter Even =
      (Finset.Icc (w - (v + 1) + 1) (w - 1)).filter Even := by
    obtain ⟨k, hk⟩ := hw
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.even_iff]
    omega
  have hC : (((v : ℕ) : ℝ) - ((w - 1 : ℕ) : ℝ)) / 2 = (((v + 1 : ℕ) : ℝ) - (w : ℝ)) / 2 := by
    rw [Nat.cast_sub hw1]
    push_cast
    ring
  have hE : ((↑(v + 1) * ↑w : ℤ) - ((v + 1) * (v + 1 + 1) / 2 : ℕ)) =
      ((↑v * ↑(w - 1) : ℤ) - (v * (v + 1) / 2 : ℕ)) + ((w : ℤ) - 1) := by
    rw [tri_succ v]
    push_cast [Nat.cast_sub hw1]
    ring
  have hW : q ^ (-(w : ℝ) / 2) = q ^ (-((w / 2 : ℕ) : ℤ)) := by
    obtain ⟨k, rfl⟩ := hw
    rw [half_rpow hq, show (k + k) / 2 = k by omega, zpow_neg, zpow_natCast]
  unfold rForm
  rw [hP, hC, hE, hW, zpow_add₀ hq.ne']
  ring

/-- The induction step for $w$ odd: $a(t, W)\,r'(v, w - 1) = r'(v + 1, w)$ with
$a(t, W) = q^{w-1} + c'q^{(w-1)/2}$, $c' = \chi(x^\perp) = \pm 1$ and $\chi(W) = 0$. -/
theorem rForm_step_odd {q : ℝ} (hq : 0 < q) {v w : ℕ} (hv : 1 ≤ v) (hvw : v + 1 ≤ w) (hw : Odd w)
    {c' : ℝ} (hc' : c' ^ 2 = 1) (c : ℝ) :
    (q ^ (w - 1) + c' * q ^ ((w - 1) / 2)) * rForm q v (w - 1) c' c = rForm q (v + 1) w 0 c := by
  have hw1 : 1 ≤ w := by omega
  obtain ⟨k, hk⟩ := hw
  have hw2 : w - 1 = k + k := by omega
  have hnot : w - 1 ∉ (Finset.Icc (w - 1 - v + 1) (w - 1 - 1)).filter Even := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hP : (Finset.Icc (w - (v + 1) + 1) (w - 1)).filter Even =
      insert (w - 1) ((Finset.Icc (w - 1 - v + 1) (w - 1 - 1)).filter Even) := by
    ext e
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, Nat.even_iff]
    omega
  have hC : (((v : ℕ) : ℝ) - ((w - 1 : ℕ) : ℝ)) / 2 = (((v + 1 : ℕ) : ℝ) - (w : ℝ)) / 2 := by
    rw [Nat.cast_sub hw1]
    push_cast
    ring
  have hE : ((↑(v + 1) * ↑w : ℤ) - ((v + 1) * (v + 1 + 1) / 2 : ℕ)) =
      ((↑v * ↑(w - 1) : ℤ) - (v * (v + 1) / 2 : ℕ)) + ((w - 1 : ℕ) : ℤ) := by
    rw [tri_succ v]
    push_cast [Nat.cast_sub hw1]
    ring
  have hW : q ^ (-((w - 1 : ℕ) : ℝ) / 2) = (q ^ k)⁻¹ := by
    rw [hw2, half_rpow hq]
  unfold rForm
  rw [hP, Finset.prod_insert hnot, hC, hE, hW, zpow_add₀ hq.ne', hw2, show (k + k) / 2 = k by omega]
  have hqk : q ^ k ≠ 0 := pow_ne_zero _ hq.ne'
  have h2 : q ^ (k + k) = q ^ k * q ^ k := pow_add _ _ _
  simp only [zpow_neg, zpow_natCast, h2, zero_mul, sub_zero, mul_one]
  have hcc : c' * c' = 1 := by rw [← _root_.sq]; exact hc'
  rcases mul_self_eq_one_iff.mp hcc with h | h <;> subst h <;> field_simp <;> ring

/-! ### Transport and small cases -/

variable {F : Type} [Field F]

theorem isomCount_congr_left {V V' W : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    [AddCommGroup W] [Module F W] {QV : QuadraticForm F V} {QV' : QuadraticForm F V'} (QW : QuadraticForm F W)
    (h : QV.Equivalent QV') : isomCount QV QW = isomCount QV' QW := by
  obtain ⟨e⟩ := h
  have h1 : ∀ x, QV (e.toLinearEquiv.symm x) = QV' x := fun x => by
    rw [← e.map_app]
    exact congrArg QV' (e.toLinearEquiv.apply_symm_apply x)
  refine Nat.card_congr
    { toFun := fun σ => ⟨σ.1.comp e.toLinearEquiv.symm.toLinearMap, σ.2.1.comp e.toLinearEquiv.symm.injective,
        fun x => by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]; rw [σ.2.2, h1]⟩
      invFun := fun τ => ⟨τ.1.comp e.toLinearEquiv.toLinearMap, τ.2.1.comp e.toLinearEquiv.injective,
        fun x => by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]; rw [τ.2.2]; exact e.map_app x⟩
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp }

theorem isomCount_congr_right {V W W' : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W'] (QV : QuadraticForm F V) {QW : QuadraticForm F W} {QW' : QuadraticForm F W'}
    (h : QW.Equivalent QW') : isomCount QV QW = isomCount QV QW' := by
  obtain ⟨e⟩ := h
  have h1 : ∀ y, QW (e.toLinearEquiv.symm y) = QW' y := fun y => by
    rw [← e.map_app]
    exact congrArg QW' (e.toLinearEquiv.apply_symm_apply y)
  refine Nat.card_congr
    { toFun := fun σ => ⟨e.toLinearEquiv.toLinearMap.comp σ.1, e.toLinearEquiv.injective.comp σ.2.1,
        fun x => by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]; rw [← σ.2.2 x]; exact e.map_app _⟩
      invFun := fun τ => ⟨e.toLinearEquiv.symm.toLinearMap.comp τ.1, e.toLinearEquiv.symm.injective.comp τ.2.1,
        fun x => by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]; rw [h1, τ.2.2]⟩
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp }

/-- There is exactly one isometry from the zero space. -/
theorem isomCount_of_subsingleton {V W : Type} [AddCommGroup V] [Module F V] [Subsingleton V] [AddCommGroup W]
    [Module F W] (QV : QuadraticForm F V) (QW : QuadraticForm F W) : isomCount QV QW = 1 := by
  rw [isomCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, fun a b _ => Subsingleton.elim a b, fun x => by rw [Subsingleton.elim x 0]; simp⟩, fun σ => ?_⟩
  ext x
  simp [Subsingleton.elim x 0]

/-- An isometry preserves the polar form. -/
theorem polar_of_iso {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {QV : QuadraticForm F V} {QW : QuadraticForm F W} (σ : V →ₗ[F] W) (hσ : ∀ x, QW (σ x) = QV x) (a b : V) :
    polar QW (σ a) (σ b) = polar QV a b := by
  simp only [polar, ← map_add, hσ]

/-! ### The fibration over the image of the first basis vector -/

section Fiber

variable {V1 W : Type} [AddCommGroup V1] [Module F V1] [AddCommGroup W] [Module F W]
  (QV1 : QuadraticForm F V1) (QW : QuadraticForm F W) {t : F}

/-- The isometries $\langle t\rangle \perp V_1 \to W$. -/
abbrev IsoSet : Type :=
  {σ : (F × V1) →ₗ[F] W // Function.Injective σ ∧ ∀ y, QW (σ y) = ((lineForm t).prod QV1) y}

/-- The isometries $\langle t\rangle \perp V_1 \to W$ sending $(1, 0)$ to $x$ correspond to the isometries
$V_1 \to x^\perp$. -/
def lineFiberEquiv (hF : ringChar F ≠ 2) (ht : t ≠ 0) (x : W) (hx : QW x = t) :
    {σ : IsoSet QV1 QW (t := t) // σ.1 (1, 0) = x} ≃
      {τ : V1 →ₗ[F] perpVec QW x // Function.Injective τ ∧ ∀ v, (QW.comp (perpVec QW x).subtype) (τ v) = QV1 v} where
  toFun σ :=
    ⟨LinearMap.codRestrict (perpVec QW x) (σ.1.1.comp (LinearMap.inr F F V1)) (fun v => by
        have h := polar_of_iso σ.1.1 σ.1.2.2 (1, 0) (0, v)
        rw [σ.2] at h
        rw [mem_perpVec, LinearMap.comp_apply, LinearMap.inr_apply, h]
        simp [polar, QuadraticMap.prod_apply]),
      fun a b h => by
        have h' := congrArg Subtype.val h
        simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.inr_apply] at h'
        exact (Prod.mk.inj (σ.1.2.1 h')).2,
      fun v => by
        simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, LinearMap.codRestrict_apply,
          LinearMap.comp_apply, LinearMap.inr_apply]
        rw [σ.1.2.2]
        simp [QuadraticMap.prod_apply]⟩
  invFun τ :=
    ⟨⟨(LinearMap.fst F F V1).smulRight x + (perpVec QW x).subtype.comp (τ.1.comp (LinearMap.snd F F V1)),
      by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        rintro ⟨s, v⟩ h
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
          LinearMap.comp_apply, LinearMap.snd_apply, Submodule.subtype_apply] at h
        have hpol := congrArg (polar QW x) h
        rw [polar_add_right, polar_smul_right, (mem_perpVec QW x _).mp (τ.1 v).2,
          QuadraticMap.polar_zero_right, polar_self, hx] at hpol
        have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
        have hs : s = 0 := by
          simp only [smul_eq_mul, add_zero] at hpol
          rcases mul_eq_zero.mp hpol with h0 | h0
          · exact h0
          · exact absurd h0 (by rw [two_nsmul, ← two_mul]; exact mul_ne_zero h2 ht)
        subst hs
        simp only [zero_smul, zero_add] at h
        have hv : τ.1 v = 0 := Subtype.ext h
        have := τ.2.1 (hv.trans (map_zero τ.1).symm)
        simp [this],
      by
        rintro ⟨s, v⟩
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
          LinearMap.comp_apply, LinearMap.snd_apply, Submodule.subtype_apply]
        rw [QuadraticMap.map_add QW, QuadraticMap.map_smul, polar_smul_left,
          (mem_perpVec QW x _).mp (τ.1 v).2, hx]
        have := τ.2.2 v
        simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
        rw [this]
        simp [QuadraticMap.prod_apply, smul_eq_mul]
        ring⟩,
     by simp⟩
  left_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨s, v⟩
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.comp_apply, LinearMap.snd_apply, Submodule.subtype_apply, LinearMap.codRestrict_apply,
      LinearMap.inr_apply]
    rw [show ((s, v) : F × V1) = s • ((1 : F), (0 : V1)) + ((0 : F), v) by ext <;> simp, map_add, map_smul,
      σ.2]
  right_inv τ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp

end Fiber

/-! ### Two identities for $\chi$ -/

theorem neg_prod {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (A : QuadraticForm F V) (B : QuadraticForm F W) : -(A.prod B) = (-A).prod (-B) := by
  ext x
  simp [QuadraticMap.prod_apply]
  ring

theorem neg_lineForm (t : F) : -(lineForm t) = lineForm (-t) := by
  ext x
  simp

theorem Equivalent.neg' {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {A : QuadraticForm F V} {B : QuadraticForm F W} (h : A.Equivalent B) : (-A).Equivalent (-B) := by
  obtain ⟨e⟩ := h
  refine ⟨{ toLinearEquiv := e.toLinearEquiv, map_app' := fun x => ?_ }⟩
  show -(B (e x)) = -(A x)
  rw [e.map_app]

theorem nondegenerate_neg {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) : (polarBilin (-Q)).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff] at hQ ⊢
  intro x hx
  exact hQ x fun y => by
    have := hx y
    simp only [polar, neg_apply] at this
    simp only [polar]
    linear_combination -this

/-- $\chi(x^\perp) = \chi(W \perp \langle -t\rangle)$ when $Q(x) = t \ne 0$. -/
theorem chi_perp (hF : ringChar F ≠ 2) {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {QW : QuadraticForm F W} (hQW : (polarBilin QW).Nondegenerate) {x : W} {t : F} (hx : QW x = t) (ht : t ≠ 0) :
    chiGen (QW.comp (perpVec QW x).subtype) = chiGen (QW.prod (lineForm (-t))) := by
  obtain ⟨hreg, -, hsplit⟩ := orthSplit hF hQW hx ht
  have ht' : -t ≠ 0 := neg_ne_zero.mpr ht
  have a4 : ((lineForm (-t)).prod (lineForm t)).Equivalent (QuadraticForm.hyperbolicPlane F) := by
    have := lineForm_prod_neg_equiv hF ht'
    rwa [neg_neg] at this
  have e1 : (QW.prod (lineForm (-t))).Equivalent
      ((QuadraticForm.hyperbolicPlane F).prod (QW.comp (perpVec QW x).subtype)) :=
    QuadraticMap.Equivalent.trans (hsplit.symm.prod (QuadraticMap.Equivalent.refl _))
      (QuadraticMap.Equivalent.trans ⟨QuadraticMap.IsometryEquiv.prodComm _ _⟩
        (QuadraticMap.Equivalent.trans ⟨(QuadraticForm.Witt.prodAssoc _ _ _).symm⟩
          (a4.prod (QuadraticMap.Equivalent.refl _))))
  have hreg' : (polarBilin (QW.prod (lineForm (-t)))).Nondegenerate :=
    QuadraticForm.nondegenerate_polarBilin_prod hQW (lineForm_nondegenerate hF ht')
  rw [chiGen_congr hreg' e1, chiGen_hyp_prod hreg]

/-- $\chi(V \perp W^{(-1)}) = \chi(V_1 \perp W_1^{(-1)})$ when $V \cong \langle t\rangle \perp V_1$ and
$W \cong \langle t\rangle \perp W_1$. -/
theorem chi_cancel (hF : ringChar F ≠ 2) {V V1 W W1 : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup V1] [Module F V1] [FiniteDimensional F V1] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [AddCommGroup W1] [Module F W1] [FiniteDimensional F W1] {QV : QuadraticForm F V} {QV1 : QuadraticForm F V1}
    {QW : QuadraticForm F W} {QW1 : QuadraticForm F W1} (hQV : (polarBilin QV).Nondegenerate)
    (hQW : (polarBilin QW).Nondegenerate) (hQV1 : (polarBilin QV1).Nondegenerate)
    (hQW1 : (polarBilin QW1).Nondegenerate) {t : F} (ht : t ≠ 0)
    (hV : ((lineForm t).prod QV1).Equivalent QV) (hW : ((lineForm t).prod QW1).Equivalent QW) :
    chiGen (QV.prod (-QW)) = chiGen (QV1.prod (-QW1)) := by
  have hH : ((lineForm t).prod (lineForm (-t))).Equivalent (QuadraticForm.hyperbolicPlane F) :=
    lineForm_prod_neg_equiv hF ht
  have hW' : (-QW).Equivalent ((lineForm (-t)).prod (-QW1)) := by
    have := Equivalent.neg' hW.symm
    rwa [neg_prod, neg_lineForm] at this
  have e1 : (QV.prod (-QW)).Equivalent ((QuadraticForm.hyperbolicPlane F).prod (QV1.prod (-QW1))) :=
    QuadraticMap.Equivalent.trans (hV.symm.prod hW')
      (QuadraticMap.Equivalent.trans ⟨QuadraticMap.IsometryEquiv.prodProdProdComm _ _ _ _⟩
        (hH.prod (QuadraticMap.Equivalent.refl _)))
  have hreg : (polarBilin (QV.prod (-QW))).Nondegenerate :=
    QuadraticForm.nondegenerate_polarBilin_prod hQV (nondegenerate_neg hQW)
  have hreg1 : (polarBilin (QV1.prod (-QW1))).Nondegenerate :=
    QuadraticForm.nondegenerate_polarBilin_prod hQV1 (nondegenerate_neg hQW1)
  rw [chiGen_congr hreg e1, chiGen_hyp_prod hreg1]

/-- $\chi$ of an odd-dimensional space is $0$. -/
theorem chiGen_of_odd {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)
    (h : Odd (finrank F V)) : chiGen Q = 0 := by
  simp [chiGen, h]

/-- $\chi$ of an even-dimensional space is $\pm 1$. -/
theorem chiGen_sq_of_even {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)
    (h : Even (finrank F V)) : chiGen Q ^ 2 = 1 := by
  have : ¬ Odd (finrank F V) := Nat.not_odd_iff_even.mpr h
  unfold chiGen
  rw [if_neg this]
  split_ifs <;> norm_num

/-! ### The induction -/

section Main

variable [Finite F]

/-- $r(\langle t\rangle \perp V_1, W) = a(t, W)\,R$ when every $r(V_1, x^\perp)$ with $Q(x) = t$ equals $R$. -/
theorem isomCount_line_prod_eq {V1 W : Type} [AddCommGroup V1] [Module F V1] [FiniteDimensional F V1]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (QV1 : QuadraticForm F V1) (QW : QuadraticForm F W)
    (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) (R : ℝ)
    (hR : ∀ x, QW x = t → (isomCount QV1 (QW.comp (perpVec QW x).subtype) : ℝ) = R) :
    (isomCount ((lineForm t).prod QV1) QW : ℝ) = valCount QW t * R := by
  classical
  have : Finite W := Module.finite_of_finite F
  have : Finite ((F × V1) →ₗ[F] W) := Module.finite_of_finite F
  have : Fintype {x : W // QW x = t} := Fintype.ofFinite _
  let f : IsoSet QV1 QW (t := t) → {x : W // QW x = t} := fun σ =>
    ⟨σ.1 (1, 0), by rw [σ.2.2]; simp [QuadraticMap.prod_apply]⟩
  have hcard : isomCount ((lineForm t).prod QV1) QW = Nat.card (Σ b, {a // f a = b}) :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
  have hfib : ∀ b : {x : W // QW x = t}, Nat.card {a // f a = b} =
      isomCount QV1 (QW.comp (perpVec QW b.1).subtype) := by
    intro b
    rw [isomCount, ← Nat.card_congr (lineFiberEquiv QV1 QW hF ht b.1 b.2)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [f, Subtype.ext_iff])
  rw [hcard, Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl fun b _ => by rw [hfib b, hR b.1 b.2], Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, valCount, Nat.card_eq_fintype_card]

/-- Splitting off an anisotropic line: $V \cong \langle t\rangle \perp V_1$ with $V_1$ regular. -/
theorem exists_line_split (hF : ringChar F ≠ 2) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {QV : QuadraticForm F V} (hQV : (polarBilin QV).Nondegenerate) (hpos : 0 < finrank F V) :
    ∃ x0 : V, QV x0 ≠ 0 ∧ (polarBilin (QV.comp (perpVec QV x0).subtype)).Nondegenerate ∧
      finrank F (perpVec QV x0) + 1 = finrank F V ∧
      ((lineForm (QV x0)).prod (QV.comp (perpVec QV x0).subtype)).Equivalent QV := by
  obtain ⟨x0, hx0⟩ : ∃ x0, QV x0 ≠ 0 := by
    by_contra! h
    have hall : ∀ y : V, y = 0 := fun y =>
      (QuadraticForm.nondegenerate_polarBilin_iff QV).mp hQV y fun w => by simp [polar, h]
    have : Subsingleton V := ⟨fun a b => (hall a).trans (hall b).symm⟩
    rw [Module.finrank_zero_of_subsingleton] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨h1, h2, h3⟩ := orthSplit hF hQV rfl hx0
  exact ⟨x0, hx0, h1, h2, h3⟩

/-- Lemma 1.3.2 (the count) for a general even-dimensional space. -/
theorem valCount_even {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {QW : QuadraticForm F W} (hQW : (polarBilin QW).Nondegenerate) (hw : Even (finrank F W)) {t : F}
    (ht : t ≠ 0) :
    (valCount QW t : ℝ) = (Nat.card F : ℝ) ^ ((finrank F W : ℤ) - 1) *
      (1 - chiGen QW * (Nat.card F : ℝ) ^ (-((finrank F W / 2 : ℕ) : ℤ))) := by
  set w := finrank F W
  let e : (Fin w → F) ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by simp [w])
  let QW' := QW.comp e.toLinearMap
  have hequiv : QW'.Equivalent QW := ⟨{ toLinearEquiv := e, map_app' := fun x => rfl }⟩
  have hreg' : (polarBilin QW').Nondegenerate := by
    rw [QuadraticForm.nondegenerate_polarBilin_iff] at hQW ⊢
    intro x hx
    have : e x = 0 := hQW (e x) fun y => by
      obtain ⟨z, rfl⟩ := e.surjective y
      have := hx z
      simpa [QW', polar] using this
    exact e.injective (this.trans (map_zero e).symm)
  rw [← valCount_congr hequiv t, lemma132 QW' hreg' hw ht, chiV_eq_chiGen, chiGen_congr hreg' hequiv]

/-- **The general form of Theorem 1.3.2 in odd characteristic**, by induction on $\dim V = v + 1$. -/
theorem theorem132_gen (hF : ringChar F ≠ 2) (v : ℕ) : ∀ {V W : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (QV : QuadraticForm F V) (QW : QuadraticForm F W), (polarBilin QV).Nondegenerate →
    (polarBilin QW).Nondegenerate → finrank F V = v + 1 → v + 1 ≤ finrank F W →
    (isomCount QV QW : ℝ) =
      rForm (Nat.card F) (v + 1) (finrank F W) (chiGen QW) (chiGen (QV.prod (-QW))) := by
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  induction v with
  | zero =>
    intro V W _ _ _ _ _ _ QV QW hQV hQW hV hvw
    obtain ⟨x0, hx0, hV1reg, hV1dim, hVsplit⟩ := exists_line_split hF hQV (by omega)
    set t := QV x0
    have hV1 : Subsingleton (perpVec QV x0) := by
      rw [← Module.finrank_zero_iff (R := F)]
      omega
    rw [isomCount_congr_left QW hVsplit.symm,
      isomCount_line_prod_eq _ QW hF hx0 1 fun x _ => by rw [isomCount_of_subsingleton]; simp, mul_one]
    rcases Nat.even_or_odd (finrank F W) with hw | hw
    · have hc : chiGen (QV.prod (-QW)) = 0 := by
        apply chiGen_of_odd
        rw [Module.finrank_prod, hV, zero_add]
        exact hw.one_add
      rw [hc, valCount_even hQW hw hx0]
      exact (rForm_one_even hq hw _).symm
    · have hW0 : chiGen QW = 0 := chiGen_of_odd QW hw
      have hc : chiGen (QV.prod (-QW)) = chiGen (QW.prod (lineForm (-t))) := by
        have : Unique (perpVec QV x0) := uniqueOfSubsingleton 0
        have hL : ((lineForm t).prod (QV.comp (perpVec QV x0).subtype)).Equivalent (lineForm t) :=
          ⟨{ toLinearEquiv := LinearEquiv.prodUnique, map_app' := fun p => by
              obtain ⟨a, b⟩ := p
              rw [Subsingleton.elim b 0]
              simp [QuadraticMap.prod_apply] }⟩
        have e1 : (QV.prod (-QW)).Equivalent (-(QW.prod (lineForm (-t)))) := by
          rw [neg_prod, neg_lineForm, neg_neg]
          exact ((hVsplit.symm.trans hL).prod (QuadraticMap.Equivalent.refl _)).trans
            ⟨QuadraticMap.IsometryEquiv.prodComm _ _⟩
        rw [chiGen_congr (QuadraticForm.nondegenerate_polarBilin_prod hQV (nondegenerate_neg hQW)) e1,
          chiGen_neg (QuadraticForm.nondegenerate_polarBilin_prod hQW
            (lineForm_nondegenerate hF (neg_ne_zero.mpr hx0)))]
      rw [valCount_odd hF hQW hw hx0, hW0, hc]
      exact (rForm_one_odd hq hw _).symm
  | succ v ih =>
    intro V W _ _ _ _ _ _ QV QW hQV hQW hV hvw
    obtain ⟨x0, hx0, hV1reg, hV1dim, hVsplit⟩ := exists_line_split hF hQV (by omega)
    set t := QV x0
    set QV1 := QV.comp (perpVec QV x0).subtype
    have hc' : ∀ x, QW x = t → chiGen (QV1.prod (-(QW.comp (perpVec QW x).subtype))) =
        chiGen (QV.prod (-QW)) := by
      intro x hx
      obtain ⟨hWreg, -, hWsplit⟩ := orthSplit hF hQW hx hx0
      exact (chi_cancel hF hQV hQW hV1reg hWreg hx0 hVsplit hWsplit).symm
    have hR : ∀ x, QW x = t → (isomCount QV1 (QW.comp (perpVec QW x).subtype) : ℝ) =
        rForm (Nat.card F) (v + 1) (finrank F W - 1) (chiGen (QW.prod (lineForm (-t))))
          (chiGen (QV.prod (-QW))) := by
      intro x hx
      obtain ⟨hWreg, hWdim, -⟩ := orthSplit hF hQW hx hx0
      rw [ih QV1 _ hV1reg hWreg (by omega) (by omega), hc' x hx, chi_perp hF hQW hx hx0, ← hWdim,
        Nat.add_sub_cancel]
    rw [isomCount_congr_left QW hVsplit.symm, isomCount_line_prod_eq _ QW hF hx0 _ hR]
    rcases Nat.even_or_odd (finrank F W) with hw | hw
    · rw [valCount_even hQW hw hx0]
      have h0 : chiGen (QW.prod (lineForm (-t))) = 0 := by
        apply chiGen_of_odd
        rw [Module.finrank_prod, Module.finrank_self]
        exact hw.add_one
      rw [h0]
      exact rForm_step_even hq (by omega) (by omega) hw _ _
    · rw [valCount_odd hF hQW hw hx0]
      have h0 : chiGen QW = 0 := chiGen_of_odd QW hw
      rw [h0]
      exact rForm_step_odd hq (by omega) (by omega) hw (chiGen_sq_of_even _ (by
        rw [Module.finrank_prod, Module.finrank_self]; exact hw.add_one)) _

end Main

/-- **Kitaoka 1993, Theorem 1.3.2** (p. 16) **for $q$ odd**. For a finite field $K$ of odd characteristic with $q$
elements and regular quadratic forms $Q_V$ on $K^v$, $Q_W$ on $K^w$ with $1 \le v \le w$, the number of isometries
$r(V, W)$ is $q^{vw - v(v+1)/2}(1 - \chi(W)q^{-w/2})(1 + \chi(V \perp W^{(-1)})q^{(v-w)/2})
\prod_{w-v+1 \le e \le w-1,\ e \text{ even}}(1 - q^{-e})$ (the body of `Theorem132` for this $K$). Unconditional;
characteristic $2$ is not covered. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.2, p. 16 (q odd)"]
theorem theorem132_odd (K : Type) [Field K] [Fintype K] (hK : ringChar K ≠ 2) (v w : ℕ)
    (QV : QuadraticForm K (Fin v → K)) (QW : QuadraticForm K (Fin w → K)) (hQV : (polarBilin QV).Nondegenerate)
    (hQW : (polarBilin QW).Nondegenerate) (hv : 0 < v) (hvw : v ≤ w) :
    let q : ℝ := Fintype.card K
    (isomCount QV QW : ℝ) =
      q ^ ((v * w : ℤ) - (v * (v + 1) / 2 : ℕ)) * (1 - chiGen QW * q ^ (-(w : ℝ) / 2)) *
        (1 + chiGen (QV.prod (-QW)) * q ^ (((v : ℝ) - w) / 2)) *
        ∏ e ∈ (Finset.Icc (w - v + 1) (w - 1)).filter Even, (1 - q ^ (-(e : ℤ))) := by
  intro q
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have h := theorem132_gen hK v' QV QW hQV hQW (by simp) (by simpa using hvw)
  rw [h, Module.finrank_fin_fun, Nat.card_eq_fintype_card]
  rfl

end QuadFormsKB.Kitaoka.FqCount
