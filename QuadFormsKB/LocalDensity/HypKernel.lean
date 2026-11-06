/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.LocalDensity.HypCount

/-!
# Adding a hyperbolic plane: the density step $\beta(L\perp\mathbb H) / \beta(L)$ from residue counts

**Layer:** a discrete valuation ring $R$ (uniformizer $\pi$, finite residue field $\mathbb F = R/\pi$ of size $q$; every
residue characteristic, dyadic included); complete for the anisotropic statement.

For a form $L$ in $m$ variables let $Z(L)$ be the number of zeros of $\bar L = L \bmod \pi$ in $\mathbb F^m$ and $Z_{\mathrm{rad}}(L)$
the number of those in the radical of $\bar B_L$ (`resZero`, `resRadZero`).

* `localDensityForm_hypExt_hyperbolic`: $\beta_\pi(L\perp\mathbb H, \mathbb H) = \big((q-1)q^m + qZ(L) - Z_{\mathrm{rad}}(L)\big)/q^{m+1}$
  (level $1$ suffices because $\mathbb H$ is unimodular; the count of hyperbolic pairs is `card_reps_hyperbolic`).
* `localDensityForm_hypExt_step`: with the frame lemma, for $L$ and $L\perp\mathbb H$ nondegenerate,
  $\beta_\pi(L\perp\mathbb H, L\perp\mathbb H) = \big((q-1)q^m + qZ(L) - Z_{\mathrm{rad}}(L)\big)q^{-(m+1)}\,\beta_\pi(L, L)$.
* `resZero_hypExt`, `resRadZero_hypExt`: $Z(L\perp\mathbb H) + q^m = q^{m+1} + qZ(L)$, $Z_{\mathrm{rad}}(L\perp\mathbb H) = Z_{\mathrm{rad}}(L)$.
* `resRadZero_eq_resZero_of_aniso` (complete $R$): if $L$ is anisotropic over $R$, every zero of $\bar L$ lies in the radical
  of $\bar B_L$, so $Z_{\mathrm{rad}}(L) = Z(L)$. *Proof* (Hensel): if $\pi\mid L(x)$ but $\pi\nmid B(x,y)$, we may take
  $\pi\nmid L(y)$ (else replace $y$ by $x+y$); then $L(x+sy) = L(x) + sB(x,y) + s^2L(y)$ has a simple root $s\equiv0$, an
  isotropic vector.

Sources: Kitaoka 1993, §5.6 [unverified] (densities); the counts are elementary. Indices are 0-based.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.LocalDensity.HypFrame

open QuadForm QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {m : ℕ}

/-- $Z(L)$: the number of zeros of $L \bmod \pi$ in $(R/\pi)^m$. -/
def resZero (π : R) (L : QuadForm R m) : ℕ := zeroCount (L.map (Ideal.Quotient.mk (Ideal.span {π ^ 1})))

/-- $Z_{\mathrm{rad}}(L)$: the number of zeros of $L \bmod \pi$ in the radical of its bilinear form. -/
def resRadZero (π : R) (L : QuadForm R m) : ℕ := radZeroCount (L.map (Ideal.Quotient.mk (Ideal.span {π ^ 1})))

theorem hyperbolic_hessian_det : (hyperbolic R).hessian.det = -1 := by
  simp [QuadForm.hessian, hyperbolic, QuadForm.ofUpper, Matrix.det_fin_two]

theorem resZero_hypExt [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (L : QuadForm R m) :
    resZero π (hypExt L) + q R ^ m = q R * q R ^ m + q R * resZero π L := by
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have := finite_quot_pow π hπ 1
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  unfold resZero
  rw [map_hypExt, ← hcard]
  exact zeroCount_hypExt _

theorem resRadZero_hypExt [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (L : QuadForm R m) :
    resRadZero π (hypExt L) = resRadZero π L := by
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have := finite_quot_pow π hπ 1
  unfold resRadZero
  rw [map_hypExt]
  exact radZeroCount_hypExt _

/-- **$\beta_\pi(L\perp\mathbb H, \mathbb H)$ from residue counts.** -/
@[kb "kitaoka1993" "§5.6 [unverified] (density of H by L ⊥ H from the count of hyperbolic pairs mod π)"]
theorem localDensityForm_hypExt_hyperbolic [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (L : QuadForm R m) :
    localDensityForm (hypExt L) (hyperbolic R) π =
      (((q R : ℝ) - 1) * (q R : ℝ) ^ m + q R * resZero π L - resRadZero π L) / (q R : ℝ) ^ (m + 1) := by
  have hH : IsUnit (hyperbolic R).hessian.det := by rw [hyperbolic_hessian_det]; exact isUnit_one.neg
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hH (by omega)]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have := finite_quot_pow π hπ 1
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  unfold repCountForm
  rw [map_hypExt, hyperbolic_map_ring]
  have h1 := card_reps_hyperbolic (L.map (Ideal.Quotient.mk (Ideal.span {π ^ 1})))
  have h2 := zeroCount_hypExt (L.map (Ideal.Quotient.mk (Ideal.span {π ^ 1})))
  rw [hcard] at h1 h2
  unfold resZero resRadZero
  have hexp : (m + 2) * 2 - 2 * (2 + 1) / 2 = 2 * m + 1 := by omega
  rw [hexp]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have e1 := congrArg (Nat.cast (R := ℝ)) h1
  have e2 := congrArg (Nat.cast (R := ℝ)) h2
  push_cast at e1 e2
  rw [div_eq_div_iff (pow_pos hq _).ne' (pow_pos hq _).ne']
  have hp : (q R : ℝ) ^ (2 * m + 1) = (q R : ℝ) ^ m * (q R : ℝ) ^ (m + 1) := by rw [← pow_add]; ring_nf
  rw [hp]
  linear_combination (q R : ℝ) ^ (m + 1) * e1 + (q R : ℝ) ^ m * (q R : ℝ) ^ (m + 1) * e2

/-- **One hyperbolic step:** $\beta_\pi(L\perp\mathbb H) = \big((q-1)q^m + qZ(L) - Z_{\mathrm{rad}}(L)\big)q^{-(m+1)}\beta_\pi(L)$. -/
@[kb "kitaoka1993" "§5.6 [unverified] (α(L ⊥ H) = α(L ⊥ H, H) α(L))"]
theorem localDensityForm_hypExt_step [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (L : QuadForm R m) (hL : L.Nondegenerate) (hQ : (hypExt L).Nondegenerate) :
    localDensityForm (hypExt L) (hypExt L) π =
      (((q R : ℝ) - 1) * (q R : ℝ) ^ m + q R * resZero π L - resRadZero π L) / (q R : ℝ) ^ (m + 1) *
        localDensityForm L L π := by
  rw [localDensityForm_hypFrame hπ L hL hQ, localDensityForm_hypExt_hyperbolic hπ L]

/-! ### Anisotropic forms: residue zeros lie in the radical -/

theorem eval_map_gen {A S : Type*} [CommRing A] [CommRing S] (φ : A →+* S) {n : ℕ} (Q : QuadForm A n)
    (x : Fin n → A) : (Q.map φ).eval (fun i => φ (x i)) = φ (Q.eval x) := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, map_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem map_bil {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (P : QuadForm R n) (x y : Fin n → R) :
    bil (P.map f) (fun i => f (x i)) (fun i => f (y i)) = f (bil P x y) := by
  have h1 := eval_add_bil (P.map f) (fun i => f (x i)) (fun i => f (y i))
  have h2 := congrArg f (eval_add_bil P x y)
  have hxy : (fun i => f (x i)) + (fun i => f (y i)) = fun i => f ((x + y) i) := by
    ext i; simp
  rw [hxy, eval_map_gen, eval_map_gen, eval_map_gen] at h1
  rw [map_add, map_add] at h2
  linear_combination h2 - h1

/-- **Hensel:** over a complete discrete valuation ring, if $L$ is anisotropic and $\pi \mid L(x)$, then
$\pi \mid B_L(x, y)$ for every $y$. -/
theorem dvd_bil_of_aniso [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (L : QuadForm R m) (han : ∀ x, L.eval x = 0 → x = 0) (x : Fin m → R) (hx : π ∣ L.eval x) (y : Fin m → R) :
    π ∣ bil L x y := by
  have hmaxI : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hmem : ∀ z : R, z ∈ IsLocalRing.maximalIdeal R ↔ π ∣ z := fun z => by
    rw [hmaxI, Ideal.mem_span_singleton]
  -- the key case: `π ∤ L(y)`
  have key : ∀ y, ¬ π ∣ bil L x y → ¬ π ∣ L.eval y → False := by
    intro y hB hc
    obtain ⟨c, hc'⟩ := dvr_isUnit_of_not_dvd hπ hc
    set B := bil L x y
    let f : Polynomial R := Polynomial.X ^ 2 + Polynomial.C ((↑c⁻¹ : R) * B) * Polynomial.X +
      Polynomial.C ((↑c⁻¹ : R) * L.eval x)
    have hf : f.Monic := by unfold f; monicity!
    have hev : f.eval 0 ∈ IsLocalRing.maximalIdeal R := by
      rw [hmem]
      simp [f]
      first | exact hx | exact dvd_mul_of_dvd_right hx _
    have hder : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.derivative.eval 0)) := by
      refine IsUnit.map _ ?_
      have : f.derivative.eval 0 = (↑c⁻¹ : R) * B := by
        simp [f, Polynomial.derivative_add, Polynomial.derivative_mul]
      rw [this]
      exact (Units.isUnit _).mul (dvr_isUnit_of_not_dvd hπ hB)
    obtain ⟨s, hs, hs0⟩ := HenselianRing.is_henselian f hf 0 hev hder
    have hroot : s ^ 2 + (↑c⁻¹ : R) * B * s + (↑c⁻¹ : R) * L.eval x = 0 := by
      simpa [f, Polynomial.IsRoot] using hs
    have hiso : L.eval (x + s • y) = 0 := by
      rw [eval_add_bil, eval_smul', bil_smul_right]
      have hcc : (c : R) * (↑c⁻¹ : R) = 1 := by simp
      rw [← hc']
      linear_combination (c : R) * hroot - (s * B + L.eval x) * hcc
    have h0 := han _ hiso
    have hxs : x = -(s • y) := eq_neg_of_add_eq_zero_left h0
    apply hB
    show π ∣ bil L x y
    rw [hxs]
    have : bil L (-(s • y)) y = -(s * (2 * L.eval y)) := by
      rw [← neg_one_smul R (s • y), bil_smul_left, bil_smul_left, bil_self]; ring
    rw [this]
    have hs' : π ∣ s := by rw [← hmem]; simpa using hs0
    exact (dvd_neg).2 (dvd_mul_of_dvd_left hs' _)
  by_contra hB
  by_cases hc : π ∣ L.eval y
  · -- replace `y` by `x + y`
    apply key (x + y)
    · intro h
      apply hB
      have e : bil L x (x + y) = 2 * L.eval x + bil L x y := by
        rw [bil_comm, bil_add_left, bil_comm L y x, bil_self]
      rw [e] at h
      have := dvd_sub h (dvd_mul_of_dvd_right hx 2)
      simpa using this
    · intro h
      apply hB
      have e : bil L x y = L.eval (x + y) - L.eval x - L.eval y := by rw [eval_add_bil]; ring
      rw [e]
      exact dvd_sub (dvd_sub h hx) hc
  · exact key y hB hc

/-- **Anisotropic forms over a complete ring:** $Z_{\mathrm{rad}}(L) = Z(L)$. -/
theorem resRadZero_eq_resZero_of_aniso [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (L : QuadForm R m) (han : ∀ x, L.eval x = 0 → x = 0) : resRadZero π L = resZero π L := by
  unfold resRadZero resZero radZeroCount zeroCount
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have hdvd : ∀ z : R, mk z = 0 ↔ π ∣ z := fun z => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun xb => ⟨fun h => h.1, fun h => ⟨h, fun yb => ?_⟩⟩)
  choose x hx using fun i => Ideal.Quotient.mk_surjective (xb i)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (yb i)
  have ex : xb = fun i => mk (x i) := funext fun i => (hx i).symm
  have ey : yb = fun i => mk (y i) := funext fun i => (hy i).symm
  rw [ex, eval_map_gen, hdvd] at h
  rw [ex, ey, map_bil, hdvd]
  exact dvd_bil_of_aniso hπ L han x h y

end QuadFormsKB.LocalDensity.HypFrame
