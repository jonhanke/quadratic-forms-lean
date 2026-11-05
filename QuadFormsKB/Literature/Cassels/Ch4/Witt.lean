/-
# Cassels, Chapter 4, §3: the Witt group of $\mathbb Q_p$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, §3, *The Witt group*, Lemma 3.1
(pp. 63–65, Springer's theorem for $\mathbb Q_p$, $p$ odd) and Lemma 3.2 (p. 65, $p = 2$).

**Setting.** $W(k)$ = `W k` is the Witt group of Chapter 2, §5 (`Ch2/WittGroup.lean`), and $\langle a\rangle$ =
`toW k (toG k (unary k a))` for $a \in k^{\times}$; it is presented by the generators $\langle a\rangle$ and Cassels'
relations (i)–(iii) (`W_lift`, Ch. 2, Lemma 5.6, Corollary). $U = \mathbb Z_p^{\times}$; a unit $u \in U$ is also a unit
of $\mathbb Q_p$ (`unitQ p u`), and $\bar u \in \mathbb F_p^{\times}$ is its residue (`unitF p u`). The instance
`[Invertible (2 : ZMod p)]` says that $p$ is odd.

**Proves.**
* Lemma 3.1 (p. 63): for $p$ odd, $W(\mathbb Q_p) \cong W(\mathbb F_p) \oplus W(\mathbb F_p)$, by Cassels' map
  $\langle p^{l}u\rangle \mapsto (\langle\bar u\rangle, 0)$ for $l$ even and $(0, \langle\bar u\rangle)$ for $l$ odd
  (`witt_padic_odd`).
* Lemma 3.2 (p. 65, $p = 2$) is in `Ch4/WittTwo.lean` (`witt_padic_two`).
-/
import QuadFormsKB.Literature.Cassels.Ch2.WittRing
import QuadFormsKB.Literature.Cassels.Ch2.WittFinite

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

variable (p : ℕ) [Fact p.Prime]

/-- A $p$-adic unit $u \in \mathbb Z_p^{\times}$ as a unit of $\mathbb Q_p$. -/
def unitQ (u : ℤ_[p]ˣ) : ℚ_[p]ˣ := Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u

/-- The residue $\bar u \in \mathbb F_p^{\times}$ of a $p$-adic unit $u$. -/
def unitF (u : ℤ_[p]ˣ) : (ZMod p)ˣ := Units.map (PadicInt.toZMod (p := p)).toMonoidHom u

/-- The prime $p$ as a unit of $\mathbb Q_p$. -/
def primeQ : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

section Decomp

/-- The valuation $v_p(x)$ of $x \in \mathbb Q_p^{\times}$. -/
abbrev val (x : ℚ_[p]ˣ) : ℤ := (x : ℚ_[p]).valuation

theorem norm_unit_part (x : ℚ_[p]ˣ) : ‖(x : ℚ_[p]) * (p : ℚ_[p]) ^ (-val p x)‖ = 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_p_zpow, neg_neg,
    ← zpow_add₀ (by positivity)]
  simp

/-- The unit part $u \in \mathbb Z_p^{\times}$ of $x = p^{v_p(x)}u \in \mathbb Q_p^{\times}$. -/
def uc (x : ℚ_[p]ˣ) : ℤ_[p]ˣ := PadicInt.mkUnits (norm_unit_part p x)

theorem p_ne_zero' : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem decomp (x : ℚ_[p]ˣ) : (x : ℚ_[p]) = (p : ℚ_[p]) ^ val p x * ((uc p x : ℤ_[p]) : ℚ_[p]) := by
  rw [uc, PadicInt.mkUnits_eq, mul_comm, mul_assoc, ← zpow_add₀ (p_ne_zero' p)]
  simp

/-- Uniqueness of the decomposition $x = p^{l}w$. -/
theorem decomp_unique {x : ℚ_[p]ˣ} {l : ℤ} {w : ℤ_[p]ˣ} (h : (x : ℚ_[p]) = (p : ℚ_[p]) ^ l * ((w : ℤ_[p]) : ℚ_[p])) :
    val p x = l ∧ uc p x = w := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hw : ‖((w : ℤ_[p]) : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp w.isUnit
  have hv : val p x = l := by
    have h1 := Padic.norm_eq_zpow_neg_valuation x.ne_zero
    have h2 : ‖(x : ℚ_[p])‖ = (p : ℝ) ^ (-l) := by rw [h, norm_mul, hw, mul_one, Padic.norm_p_zpow]
    rw [h2] at h1
    have := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp.ne' h1
    simp only [neg_inj] at this
    exact this.symm
  refine ⟨hv, Units.ext (Subtype.ext ?_)⟩
  change (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-val p x) = _
  rw [hv, h, mul_comm, ← mul_assoc, ← zpow_add₀ (p_ne_zero' p)]
  simp

/-- The residue $\bar u \in \mathbb F_p^{\times}$ of the unit part of $x$. -/
abbrev rc (x : ℚ_[p]ˣ) : (ZMod p)ˣ := unitF p (uc p x)

theorem val_mul (x y : ℚ_[p]ˣ) : val p (x * y) = val p x + val p y ∧ uc p (x * y) = uc p x * uc p y := by
  apply decomp_unique
  rw [Units.val_mul, decomp p x, decomp p y, Units.val_mul, PadicInt.coe_mul, zpow_add₀ (p_ne_zero' p)]
  ring

theorem rc_mul (x y : ℚ_[p]ˣ) : rc p (x * y) = rc p x * rc p y := by
  rw [rc, (val_mul p x y).2, unitF, map_mul]
  rfl

theorem isUnit_of_toZMod_ne_zero {z : ℤ_[p]} (h : PadicInt.toZMod z ≠ 0) : IsUnit z := by
  by_contra hz
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact hz

theorem val_unitQ (u : ℤ_[p]ˣ) : val p (unitQ p u) = 0 ∧ uc p (unitQ p u) = u :=
  decomp_unique p (by simp [unitQ])

theorem val_primeQ_mul (u : ℤ_[p]ˣ) : val p (primeQ p * unitQ p u) = 1 ∧ uc p (primeQ p * unitQ p u) = u :=
  decomp_unique p (by simp [unitQ, primeQ])

theorem val_mul3 (x y z : ℚ_[p]ˣ) : val p (x * y * z) = val p x + val p y + val p z := by
  rw [(val_mul p _ _).1, (val_mul p _ _).1]

theorem rc_mul3 (x y z : ℚ_[p]ˣ) : rc p (x * y * z) = rc p x * rc p y * rc p z := by
  rw [rc_mul, rc_mul]

theorem toZMod_p : PadicInt.toZMod (p : ℤ_[p]) = 0 := by simp

theorem coe_unitF (u : ℤ_[p]ˣ) : ((unitF p u : (ZMod p)ˣ) : ZMod p) = PadicInt.toZMod (u : ℤ_[p]) := rfl

theorem coe_unitQ (u : ℤ_[p]ˣ) : ((unitQ p u : ℚ_[p]ˣ) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := rfl

theorem unitQ_mul (u v : ℤ_[p]ˣ) : unitQ p (u * v) = unitQ p u * unitQ p v := map_mul _ u v

theorem unitF_mul (u v : ℤ_[p]ˣ) : unitF p (u * v) = unitF p u * unitF p v := map_mul _ u v

theorem unitF_inv (u : ℤ_[p]ˣ) : unitF p u⁻¹ = (unitF p u)⁻¹ := map_inv _ u

theorem unitF_pow (u : ℤ_[p]ˣ) (n : ℕ) : unitF p (u ^ n) = unitF p u ^ n := map_pow _ u n

theorem unitQ_pow (u : ℤ_[p]ˣ) (n : ℕ) : unitQ p (u ^ n) = unitQ p u ^ n := map_pow _ u n

theorem unitQ_one : unitQ p 1 = 1 := map_one _

end Decomp

section Odd

variable [Invertible (2 : ZMod p)]

/-! ### The map $\Psi\colon W(\mathbb Q_p) \to W(\mathbb F_p) \oplus W(\mathbb F_p)$ -/

/-- The summand selected by the parity of $l$: $t \mapsto (t, 0)$ for $l$ even, $(0, t)$ for $l$ odd. -/
def slot (l : ℤ) : W (ZMod p) →+ W (ZMod p) × W (ZMod p) :=
  if Even l then AddMonoidHom.inl _ _ else AddMonoidHom.inr _ _

theorem slot_add_two_mul (l k : ℤ) : slot p (l + 2 * k) = slot p l := by
  simp [slot, Int.even_add]

/-- Cassels' map on generators: $\langle p^{l}u\rangle \mapsto$ `slot l` $\langle\bar u\rangle$. -/
def gψ (x : ℚ_[p]ˣ) : W (ZMod p) × W (ZMod p) := slot p (val p x) (gW (rc p x))

theorem gψ_rel1 (a b : ℚ_[p]ˣ) : gψ p (a * b ^ 2) = gψ p a := by
  simp only [gψ, _root_.sq]
  rw [(val_mul p _ _).1, (val_mul p _ _).1, rc_mul, rc_mul, ← two_mul, slot_add_two_mul, ← _root_.sq, gW_sq]

theorem gψ_rel2_le (a b : ℚ_[p]ˣ) (hab : (a : ℚ_[p]) + b ≠ 0) (hle : val p a ≤ val p b) :
    gψ p a + gψ p b = gψ p (Units.mk0 _ hab) + gψ p (a * b * Units.mk0 _ hab) := by
  set c := Units.mk0 _ hab with hc
  have hcv : (c : ℚ_[p]) = a + b := rfl
  simp only [gψ]
  rw [val_mul3, rc_mul3]
  have ha := decomp p a
  have hb := decomp p b
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, val p b = val p a + ((k + 1 : ℕ) : ℤ) :=
      ⟨(val p b - val p a - 1).toNat, by omega⟩
    set z : ℤ_[p] := (uc p a : ℤ_[p]) + (p : ℤ_[p]) ^ (k + 1) * (uc p b : ℤ_[p]) with hz
    have hzr : PadicInt.toZMod z = PadicInt.toZMod (uc p a : ℤ_[p]) := by simp [z]
    have hzu : IsUnit z := isUnit_of_toZMod_ne_zero p (by rw [hzr, ← coe_unitF]; exact Units.ne_zero _)
    have hcz : (c : ℚ_[p]) = (p : ℚ_[p]) ^ val p a * ((hzu.unit : ℤ_[p]) : ℚ_[p]) := by
      rw [hcv, IsUnit.unit_spec, ha, hb, hk, zpow_add₀ (p_ne_zero' p), zpow_natCast, hz]
      push_cast
      ring
    obtain ⟨hv, hu⟩ := decomp_unique p hcz
    have hr : rc p c = rc p a := Units.ext (by rw [rc, hu, coe_unitF, IsUnit.unit_spec, hzr]; rfl)
    rw [hv, hr, show val p a + val p b + val p a = val p b + 2 * val p a by ring, slot_add_two_mul,
      show rc p a * rc p b * rc p a = rc p b * rc p a ^ 2 by rw [_root_.sq]; ac_rfl, gW_sq]
  · set z : ℤ_[p] := (uc p a : ℤ_[p]) + (uc p b : ℤ_[p]) with hz
    have hzr : PadicInt.toZMod z = (rc p a : ZMod p) + rc p b := by simp [z, coe_unitF]
    have hcz : (c : ℚ_[p]) = (p : ℚ_[p]) ^ val p a * (z : ℚ_[p]) := by
      rw [hcv, ha, hb, ← heq, hz]
      push_cast
      ring
    rw [← heq]
    by_cases hz0 : (rc p a : ZMod p) + rc p b = 0
    · have hrb : rc p b = -rc p a := Units.ext (by rw [Units.val_neg]; linear_combination hz0)
      rw [hrb, ← map_add, gW_add_neg, map_zero,
        show val p a + val p a + val p c = val p c + 2 * val p a by ring, slot_add_two_mul,
        show rc p a * -rc p a * rc p c = -rc p c * rc p a ^ 2 from Units.ext (by simp; ring), gW_sq,
        ← map_add, gW_add_neg, map_zero]
    · have hzu : IsUnit z := isUnit_of_toZMod_ne_zero p (by rw [hzr]; exact hz0)
      have hcz' : (c : ℚ_[p]) = (p : ℚ_[p]) ^ val p a * ((hzu.unit : ℤ_[p]) : ℚ_[p]) := by
        rw [IsUnit.unit_spec]; exact hcz
      obtain ⟨hv, hu⟩ := decomp_unique p hcz'
      have hr : rc p c = Units.mk0 _ hz0 :=
        Units.ext (by rw [rc, hu, coe_unitF, IsUnit.unit_spec, hzr]; rfl)
      rw [hv, hr, ← map_add, gW_add _ _ hz0, map_add,
        show val p a + val p a + val p a = val p a + 2 * val p a by ring, slot_add_two_mul]

theorem gψ_rel2 (a b : ℚ_[p]ˣ) (hab : (a : ℚ_[p]) + b ≠ 0) :
    gψ p a + gψ p b = gψ p (Units.mk0 _ hab) + gψ p (a * b * Units.mk0 _ hab) := by
  rcases le_total (val p a) (val p b) with h | h
  · exact gψ_rel2_le p a b hab h
  · have hba : (b : ℚ_[p]) + a ≠ 0 := by rwa [add_comm]
    have e1 : Units.mk0 _ hba = Units.mk0 _ hab := Units.ext (add_comm _ _)
    have e2 : b * a * Units.mk0 _ hba = a * b * Units.mk0 _ hab := by rw [e1, mul_comm b a]
    rw [add_comm, gψ_rel2_le p b a hba h, e2, e1]

theorem val_one_neg : val p 1 = 0 ∧ uc p 1 = 1 ∧ val p (-1) = 0 ∧ uc p (-1) = -1 := by
  obtain ⟨h1, h2⟩ := decomp_unique (x := 1) (l := 0) (w := 1) p (by simp)
  obtain ⟨h3, h4⟩ := decomp_unique (x := -1) (l := 0) (w := -1) p (by simp)
  exact ⟨h1, h2, h3, h4⟩

theorem gψ_rel3 : gψ p 1 + gψ p (-1) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := val_one_neg p
  simp only [gψ, rc]
  rw [h1, h2, h3, h4, ← map_add, show unitF p (-1) = -unitF p 1 from Units.ext (by simp [coe_unitF]),
    gW_add_neg, map_zero]

/-- Cassels' map $\Psi$ (3.5), (3.10). -/
def Ψmap : W ℚ_[p] →+ W (ZMod p) × W (ZMod p) :=
  (W_lift (gψ p) (gψ_rel1 p) (gψ_rel2 p) (gψ_rel3 p)).choose

theorem Ψmap_gen (x : ℚ_[p]ˣ) : Ψmap p (gW x) = gψ p x :=
  (W_lift (gψ p) (gψ_rel1 p) (gψ_rel2 p) (gψ_rel3 p)).choose_spec.1 x

/-! ### The inverse map, through lifts of residues -/

/-- A $p$-adic unit lifting $c \in \mathbb F_p^{\times}$. -/
def liftU (c : (ZMod p)ˣ) : ℤ_[p]ˣ :=
  (isUnit_of_toZMod_ne_zero p (z := (ZMod.ringHom_surjective PadicInt.toZMod (c : ZMod p)).choose)
    (by rw [(ZMod.ringHom_surjective PadicInt.toZMod (c : ZMod p)).choose_spec]; exact c.ne_zero)).unit

theorem unitF_liftU (c : (ZMod p)ˣ) : unitF p (liftU p c) = c :=
  Units.ext (by rw [coe_unitF, liftU, IsUnit.unit_spec,
    (ZMod.ringHom_surjective PadicInt.toZMod (c : ZMod p)).choose_spec])

theorem norm_two_eq_one : ‖(2 : ℤ_[p])‖ = 1 := by
  apply PadicInt.isUnit_iff.mp
  apply isUnit_of_toZMod_ne_zero
  rw [map_ofNat]
  exact Invertible.ne_zero 2

/-- **Hensel.** ($p$ odd.) Two $p$-adic units with the same residue differ by a square factor. -/
theorem exists_sq_of_unitF_eq {u u' : ℤ_[p]ˣ} (h : unitF p u = unitF p u') :
    ∃ s : ℚ_[p]ˣ, unitQ p u' = unitQ p u * s ^ 2 := by
  set c : ℤ_[p] := ((u' * u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hc1 : PadicInt.toZMod (1 - c) = 0 := by
    have := congrArg (fun v : (ZMod p)ˣ => ((v * (unitF p u)⁻¹ : (ZMod p)ˣ) : ZMod p)) h
    simp only [mul_inv_cancel, Units.val_one] at this
    rw [map_sub, map_one, hc, ← coe_unitF, unitF_mul, unitF_inv, ← this]
    simp
  have hnorm : ‖(1 - c : ℤ_[p])‖ < 1 := by
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod]
    exact hc1
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C c
  have hF : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C]
    simp only [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, one_pow, sub_zero, map_mul,
      map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
    norm_num
    rw [norm_two_eq_one]
    simpa using hnorm
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  have hz2 : z ^ 2 = c := by
    simp only [F, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply] at hz
    exact sub_eq_zero.mp hz
  have hzu : IsUnit z := (isUnit_pow_iff two_ne_zero).mp (by rw [hz2]; exact Units.isUnit _)
  refine ⟨unitQ p hzu.unit, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_unitQ, coe_unitQ, coe_unitQ, IsUnit.unit_spec,
    ← PadicInt.coe_pow, ← PadicInt.coe_mul, hz2, hc]
  congr 1
  rw [Units.val_mul, mul_left_comm, Units.mul_inv, mul_one]

/-- $\langle tu\rangle$ depends only on the residue of the unit $u$. -/
theorem gW_unitQ_congr (t : ℚ_[p]ˣ) {u u' : ℤ_[p]ˣ} (h : unitF p u = unitF p u') :
    gW (t * unitQ p u') = gW (t * unitQ p u) := by
  obtain ⟨s, hs⟩ := exists_sq_of_unitF_eq p h
  rw [hs, ← mul_assoc, gW_sq]

/-- On generators: $c \mapsto \langle t\tilde c\rangle$, $\tilde c$ a lift of $c$. -/
def gφ (t : ℚ_[p]ˣ) (c : (ZMod p)ˣ) : W ℚ_[p] := gW (t * unitQ p (liftU p c))

theorem gφ_eq (t : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) {c : (ZMod p)ˣ} (h : unitF p u = c) : gφ p t c = gW (t * unitQ p u) :=
  gW_unitQ_congr p t (by rw [h, unitF_liftU])

theorem gφ_rel1 (t : ℚ_[p]ˣ) (c d : (ZMod p)ˣ) : gφ p t (c * d ^ 2) = gφ p t c := by
  rw [gφ_eq p t (liftU p c * liftU p d ^ 2) (by rw [unitF_mul, unitF_pow, unitF_liftU, unitF_liftU]), gφ,
    unitQ_mul, unitQ_pow, ← mul_assoc, gW_sq]

theorem gφ_rel2 (t : ℚ_[p]ˣ) (c d : (ZMod p)ˣ) (hcd : (c : ZMod p) + d ≠ 0) :
    gφ p t c + gφ p t d = gφ p t (Units.mk0 _ hcd) + gφ p t (c * d * Units.mk0 _ hcd) := by
  set z : ℤ_[p] := (liftU p c : ℤ_[p]) + (liftU p d : ℤ_[p]) with hz
  have hzr : PadicInt.toZMod z = (c : ZMod p) + d := by
    rw [hz, map_add, ← coe_unitF, ← coe_unitF, unitF_liftU, unitF_liftU]
  have hzu : IsUnit z := isUnit_of_toZMod_ne_zero p (by rw [hzr]; exact hcd)
  have hU : unitF p hzu.unit = Units.mk0 _ hcd := Units.ext (by rw [coe_unitF, IsUnit.unit_spec, hzr]; rfl)
  rw [gφ_eq p t hzu.unit hU, gφ_eq p t (liftU p c * liftU p d * hzu.unit) (c := c * d * Units.mk0 _ hcd)
    (by rw [unitF_mul, unitF_mul, unitF_liftU, unitF_liftU, hU])]
  have hAB : ((t * unitQ p (liftU p c) : ℚ_[p]ˣ) : ℚ_[p]) + (t * unitQ p (liftU p d) : ℚ_[p]ˣ) ≠ 0 := by
    rw [Units.val_mul, Units.val_mul, ← mul_add]
    refine mul_ne_zero t.ne_zero ?_
    rw [coe_unitQ, coe_unitQ, ← PadicInt.coe_add, ← hz]
    exact PadicInt.coe_ne_zero.mpr hzu.ne_zero
  have e1 : Units.mk0 _ hAB = t * unitQ p hzu.unit := Units.ext (by
    simp only [Units.val_mk0, Units.val_mul, coe_unitQ, IsUnit.unit_spec, hz]; push_cast; ring)
  have e2 : t * unitQ p (liftU p c) * (t * unitQ p (liftU p d)) * Units.mk0 _ hAB =
      t * unitQ p (liftU p c * liftU p d * hzu.unit) * t ^ 2 := by
    rw [e1, unitQ_mul, unitQ_mul]
    exact Units.ext (by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring)
  rw [gφ, gφ, gW_add _ _ hAB, e2, gW_sq, e1]

theorem gφ_rel3 (t : ℚ_[p]ˣ) : gφ p t 1 + gφ p t (-1) = 0 := by
  rw [gφ_eq p t 1 (map_one _), unitQ_one, gφ_eq p t (-1) (Units.ext (by simp [coe_unitF])),
    show unitQ p (-1) = -1 from Units.ext (by simp [coe_unitQ]), mul_one, mul_neg_one, gW_add_neg]

/-- The map $W(\mathbb F_p) \to W(\mathbb Q_p)$, $\langle c\rangle \mapsto \langle t\tilde c\rangle$. -/
def Φmap (t : ℚ_[p]ˣ) : W (ZMod p) →+ W ℚ_[p] :=
  (W_lift (gφ p t) (gφ_rel1 p t) (gφ_rel2 p t) (gφ_rel3 p t)).choose

theorem Φmap_gen (t : ℚ_[p]ˣ) (c : (ZMod p)ˣ) : Φmap p t (gW c) = gφ p t c :=
  (W_lift (gφ p t) (gφ_rel1 p t) (gφ_rel2 p t) (gφ_rel3 p t)).choose_spec.1 c

/-- The inverse of $\Psi$: $(s, t) \mapsto \Phi_1(s) + \Phi_p(t)$. -/
def Φfull : W (ZMod p) × W (ZMod p) →+ W ℚ_[p] := (Φmap p 1).coprod (Φmap p (primeQ p))

theorem gψ_unitQ (u : ℤ_[p]ˣ) : gψ p (unitQ p u) = (gW (unitF p u), 0) := by
  obtain ⟨h1, h2⟩ := val_unitQ p u
  simp [gψ, rc, h1, h2, slot]

theorem gψ_primeQ_mul (u : ℤ_[p]ˣ) : gψ p (primeQ p * unitQ p u) = (0, gW (unitF p u)) := by
  obtain ⟨h1, h2⟩ := val_primeQ_mul p u
  simp [gψ, rc, h1, h2, slot]

theorem Ψ_Φ : (Ψmap p).comp (Φfull p) = AddMonoidHom.id _ := by
  have h1 : ((Ψmap p).comp (Φfull p)).comp (AddMonoidHom.inl _ _) = AddMonoidHom.inl _ _ := by
    refine W_hom_ext _ _ fun c => ?_
    show Ψmap p (Φfull p (gW c, 0)) = (gW c, 0)
    rw [Φfull, AddMonoidHom.coprod_apply, map_zero, add_zero, Φmap_gen, gφ, one_mul, Ψmap_gen, gψ_unitQ, unitF_liftU]
  have h2 : ((Ψmap p).comp (Φfull p)).comp (AddMonoidHom.inr _ _) = AddMonoidHom.inr _ _ := by
    refine W_hom_ext _ _ fun c => ?_
    show Ψmap p (Φfull p (0, gW c)) = (0, gW c)
    rw [Φfull, AddMonoidHom.coprod_apply, map_zero, zero_add, Φmap_gen, gφ, Ψmap_gen, gψ_primeQ_mul, unitF_liftU]
  refine AddMonoidHom.ext fun x => ?_
  have e : x = AddMonoidHom.inl _ _ x.1 + AddMonoidHom.inr _ _ x.2 := by simp
  rw [e, map_add, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, h1, h2]
  simp

theorem Φ_Ψ : (Φfull p).comp (Ψmap p) = AddMonoidHom.id _ := by
  refine W_hom_ext _ _ fun x => ?_
  rw [AddMonoidHom.comp_apply, Ψmap_gen, AddMonoidHom.id_apply, gψ]
  have hx := decomp p x
  have key : ∀ k : ℤ, (p : ℚ_[p]) ^ (2 * k) = ((p : ℚ_[p]) ^ k) ^ 2 := fun k => by
    rw [mul_comm, zpow_mul]; norm_cast
  have hval : ∀ k : ℤ, (((primeQ p ^ k) ^ 2 : ℚ_[p]ˣ) : ℚ_[p]) = ((p : ℚ_[p]) ^ k) ^ 2 := fun k => by
    rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]; rfl
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (val p x)
  · have hs : slot p (val p x) = AddMonoidHom.inl _ _ := by
      simp only [slot, show Even (val p x) by rw [hk]; exact even_two_mul k, ↓reduceIte]
    rw [hs, AddMonoidHom.inl_apply, Φfull, AddMonoidHom.coprod_apply, map_zero, add_zero, Φmap_gen,
      gφ_eq p 1 (uc p x) rfl, one_mul]
    have e : x = unitQ p (uc p x) * (primeQ p ^ k) ^ 2 := Units.ext (by
      rw [hx, hk, Units.val_mul, hval, coe_unitQ, key, mul_comm])
    conv_rhs => rw [e]
    rw [gW_sq]
  · have hs : slot p (val p x) = AddMonoidHom.inr _ _ := by
      simp only [slot, show ¬Even (val p x) by rw [hk, Int.not_even_iff_odd]; exact odd_two_mul_add_one k, ↓reduceIte]
    rw [hs, AddMonoidHom.inr_apply, Φfull, AddMonoidHom.coprod_apply, map_zero, zero_add, Φmap_gen,
      gφ_eq p (primeQ p) (uc p x) rfl]
    have e : x = primeQ p * unitQ p (uc p x) * (primeQ p ^ k) ^ 2 := Units.ext (by
      rw [hx, hk, Units.val_mul, Units.val_mul, hval, coe_unitQ, zpow_add₀ (p_ne_zero' p), key, zpow_one]
      simp only [primeQ, Units.val_mk0]
      ring)
    conv_rhs => rw [e]
    rw [gW_sq]

end Odd

/-- **Cassels, Ch. 4, Lemma 3.1 (Springer).** Let $p$ be odd. Then $W(\mathbb Q_p)$ is isomorphic to the direct sum
of two copies of $W(\mathbb F_p)$: there is an isomorphism $\Psi$ with $\Psi\langle u\rangle = (\langle\bar u\rangle, 0)$
and $\Psi\langle pu\rangle = (0, \langle\bar u\rangle)$ for every unit $u \in \mathbb Z_p^{\times}$ (Cassels' map
$\langle a\rangle \mapsto (\psi_1\langle a\rangle, \psi_2\langle a\rangle)$ of (3.5), (3.10); every $a \in \mathbb Q_p^{\times}$
is $p^{l}u$, and $\langle p^{l}u\rangle = \langle p^{l \bmod 2}u\rangle$). -/
@[kb "cassels1978" "Ch. 4, Lemma 3.1, pp. 63–65"]
theorem witt_padic_odd [Invertible (2 : ZMod p)] :
    ∃ Ψ : W ℚ_[p] ≃+ W (ZMod p) × W (ZMod p), ∀ u : ℤ_[p]ˣ,
      Ψ (toW _ (toG _ (unary _ (unitQ p u)))) = (toW _ (toG _ (unary _ (unitF p u))), 0) ∧
      Ψ (toW _ (toG _ (unary _ (primeQ p * unitQ p u)))) = (0, toW _ (toG _ (unary _ (unitF p u)))) :=
  ⟨AddMonoidHom.toAddEquiv (Ψmap p) (Φfull p) (Φ_Ψ p) (Ψ_Φ p), fun u =>
    ⟨(Ψmap_gen p _).trans (gψ_unitQ p u), (Ψmap_gen p _).trans (gψ_primeQ_mul p u)⟩⟩

end QuadFormsKB.Cassels
