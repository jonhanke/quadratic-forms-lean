/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.LocalDensity.HypFrame

/-!
# Counting zeros and hyperbolic pairs of $L\perp\mathbb H$ over a finite field

Let $K$ be a finite field with $q$ elements, $L$ a quadratic form in $m$ variables over $K$, and
$Q = L\perp\mathbb H$ (`hypExt L`), $Q(l, s, t) = L(l) + st$. Write $Z(P) = \#\{x : P(x) = 0\}$ (`zeroCount`) and
$R(P) = \#\{x : P(x) = 0,\ B_P(x, \cdot) = 0\}$ (`radZeroCount`), the zeros in the radical of the bilinear form.

* `zeroCount_hypExt`: $Z(Q) + q^m = q\cdot q^m + q\,Z(L)$, i.e. $Z(Q) = (q-1)q^m + q\,Z(L)$.
* `radZeroCount_hypExt`: $R(Q) = R(L)$.
* `card_reps_hyperbolic`: the number of representations $Y\in K^{(m+2)\times 2}$ of $\mathbb H$ by $Q$
  ($Q\circ Y = \mathbb H$) satisfies $\#\{Y\} + q^m R(L) = q^m Z(Q)$, i.e. $\#\{Y\} = q^m\,(Z(Q) - R(L))$.

*Proof of the last.* By `compMat_eq_hyperbolic_iff`, $Y$ is a pair of columns $(u, w)$ with $Q(u) = Q(w) = 0$,
$B(u, w) = 1$. Over a field, $u$ has a partner exactly when it is not in the radical; for each such $u$ the set of
partners is in bijection (via a good isometry $g$ with $g(u) = e$, `exists_good_vec`) with the partners of $e$, which are
$(l, -L(l), 1)$, $l\in K^m$: $q^m$ of them. Indices are 0-based; the hyperbolic coordinates are $m$ and $m+1$.
Source: Kitaoka 1993, §5.6 [unverified].
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.HypFrame

open QuadForm QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

/-- Number of zeros of `P` in `A^n`. -/
def zeroCount {A : Type*} [CommRing A] {n : ℕ} (P : QuadForm A n) : ℕ :=
  Nat.card {x : Fin n → A // P.eval x = 0}

/-- Number of zeros of `P` in the radical of its bilinear form. -/
def radZeroCount {A : Type*} [CommRing A] {n : ℕ} (P : QuadForm A n) : ℕ :=
  Nat.card {x : Fin n → A // P.eval x = 0 ∧ ∀ y, bil P x y = 0}

section Aux

/-- Splitting a finite set of solutions of `p` by a second predicate `r`. -/
theorem card_split {α : Type*} [Finite α] (p r : α → Prop) :
    Nat.card {x // p x ∧ r x} + Nat.card {x // p x ∧ ¬ r x} = Nat.card {x // p x} := by
  classical
  haveI := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) r
  simpa [Finset.filter_filter] using this

variable {K : Type*} [Field K] [Finite K]

open Classical in
/-- The number of $(s, t)$ with $c + st = 0$ is $(q - 1) + [c = 0]\,q$. -/
theorem pair_count (c : K) :
    Nat.card {p : K × K // c + p.1 * p.2 = 0} = Nat.card K - 1 + if c = 0 then Nat.card K else 0 := by
  classical
  haveI := Fintype.ofFinite K
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun s t : K => c + s * t = 0)), Nat.card_sigma]
  have hfib : ∀ s : K, Nat.card {t : K // c + s * t = 0} =
      (if s = 0 then (if c = 0 then Nat.card K else 0) else 0) + (if s = 0 then 0 else 1) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      by_cases hc : c = 0
      · subst hc
        simp
      · simp [hc]
    · simp only [hs, if_false, zero_add]
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨-c / s, ?_⟩, fun t => Subtype.ext ?_⟩
      · field_simp; ring
      · have := t.2
        field_simp
        linear_combination this
  simp only [hfib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [add_comm]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.card_eq_fintype_card]

end Aux

section Main

variable {K : Type*} [Field K] [Finite K] {m : ℕ}

theorem zeroCount_hypExt_aux (L : QuadForm K m) :
    zeroCount (hypExt L) = Nat.card K ^ m * (Nat.card K - 1) + Nat.card K * zeroCount L := by
  classical
  haveI := Fintype.ofFinite K
  have e : {u : Fin (m + 2) → K // (hypExt L).eval u = 0} ≃
      Σ l : Fin m → K, {p : K × K // L.eval l + p.1 * p.2 = 0} :=
    { toFun := fun u => ⟨lp u.1, (sp u.1, tp u.1), by
        have := u.2; rw [eval_hypExt] at this; exact this⟩
      invFun := fun x => ⟨vec x.1 x.2.1.1 x.2.1.2, by rw [eval_vec]; exact x.2.2⟩
      left_inv := fun u => Subtype.ext (vec_eta _)
      right_inv := fun x => Sigma.subtype_ext (by simp) (by simp) }
  unfold zeroCount
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [pair_count, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have h1 : Fintype.card (Fin m → K) = Nat.card K ^ m := by
    simp [Fintype.card_fun, Nat.card_eq_fintype_card]
  have h2 : (Finset.univ.filter fun l : Fin m → K => L.eval l = 0).card = Nat.card {l : Fin m → K // L.eval l = 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, h2, mul_comm (Nat.card {l : Fin m → K // L.eval l = 0})]

@[kb "kitaoka1993" "§5.6 [unverified] (hyperbolic pair count)"]
theorem zeroCount_hypExt (L : QuadForm K m) :
    zeroCount (hypExt L) + Nat.card K ^ m = Nat.card K * Nat.card K ^ m + Nat.card K * zeroCount L := by
  rw [zeroCount_hypExt_aux]
  have hq : 0 < Nat.card K := Nat.card_pos
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [hr]
  simp only [Nat.add_sub_cancel]
  ring

@[kb "kitaoka1993" "§5.6 [unverified] (hyperbolic pair count)"]
theorem radZeroCount_hypExt (L : QuadForm K m) : radZeroCount (hypExt L) = radZeroCount L := by
  unfold radZeroCount
  refine Nat.card_congr
    { toFun := fun u => ⟨lp u.1, ?_, ?_⟩
      invFun := fun l => ⟨vec l.1 0 0, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨u, hu, hr⟩ := u
    have hs : sp u = 0 := by rw [← bil_fV L, bil_comm]; exact hr _
    have ht : tp u = 0 := by rw [← bil_eV L, bil_comm]; exact hr _
    rw [eval_hypExt, hs, ht] at hu
    simpa using hu
  · obtain ⟨u, hu, hr⟩ := u
    intro y
    have hs : sp u = 0 := by rw [← bil_fV L, bil_comm]; exact hr _
    have ht : tp u = 0 := by rw [← bil_eV L, bil_comm]; exact hr _
    have := hr (vec y 0 0)
    rw [bil_hypExt, hs, ht] at this
    simpa using this
  · obtain ⟨l, hl, hr⟩ := l
    rw [eval_vec, hl]; simp
  · obtain ⟨l, hl, hr⟩ := l
    intro y
    rw [bil_hypExt]
    simpa using hr (lp y)
  · rintro ⟨u, hu, hr⟩
    have hs : sp u = 0 := by rw [← bil_fV L, bil_comm]; exact hr _
    have ht : tp u = 0 := by rw [← bil_eV L, bil_comm]; exact hr _
    refine Subtype.ext ?_
    show vec (lp u) 0 0 = u
    conv_rhs => rw [← vec_eta u]
    rw [hs, ht]
  · rintro ⟨l, hl, hr⟩
    exact Subtype.ext (lp_vec _ _ _)

/-- The partners of `e` are the vectors `(l, -L(l), 1)`. -/
theorem partner_eV_card (L : QuadForm K m) :
    Nat.card {w : Fin (m + 2) → K // (hypExt L).eval w = 0 ∧ bil (hypExt L) (eV m) w = 1} =
      Nat.card K ^ m := by
  have e : {w : Fin (m + 2) → K // (hypExt L).eval w = 0 ∧ bil (hypExt L) (eV m) w = 1} ≃ (Fin m → K) :=
    { toFun := fun w => lp w.1
      invFun := fun l => ⟨vec l (-L.eval l) 1, by rw [eval_vec]; ring, by rw [bil_eV]; simp⟩
      left_inv := by
        rintro ⟨w, hw, hb⟩
        refine Subtype.ext ?_
        rw [bil_eV] at hb
        rw [eval_hypExt, hb] at hw
        show vec (lp w) (-L.eval (lp w)) 1 = w
        have hs : sp w = -L.eval (lp w) := by linear_combination hw
        rw [← hb, ← hs]; exact vec_eta w
      right_inv := fun l => lp_vec _ _ _ }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

/-- Each isotropic vector with a partner has exactly `q^m` partners. -/
theorem partner_card (L : QuadForm K m) (u y : Fin (m + 2) → K) (hu : (hypExt L).eval u = 0)
    (hy : bil (hypExt L) u y = 1) :
    Nat.card {w : Fin (m + 2) → K // (hypExt L).eval w = 0 ∧ bil (hypExt L) u w = 1} = Nat.card K ^ m := by
  obtain ⟨g, hg, hgu⟩ := exists_good_vec L u y hu hy
  obtain ⟨g', hg2, hg3⟩ := hg.2
  rw [← partner_eV_card L]
  refine Nat.card_congr
    { toFun := fun w => ⟨g w.1, by rw [hg.1]; exact w.2.1, by rw [← hgu, hg.bil L]; exact w.2.2⟩
      invFun := fun w => ⟨g' w.1, by rw [← hg.1, hg3]; exact w.2.1, by rw [← hg.bil L, hgu, hg3]; exact w.2.2⟩
      left_inv := fun w => Subtype.ext (hg2 _)
      right_inv := fun w => Subtype.ext (hg3 _) }

/-- Over a field, a vector has a partner iff it is not in the radical. -/
theorem exists_partner_iff {n : ℕ} (P : QuadForm K n) (u : Fin n → K) :
    (∃ y, bil P u y = 1) ↔ ¬ ∀ y, bil P u y = 0 := by
  constructor
  · rintro ⟨y, hy⟩ h
    have := h y
    rw [hy] at this
    exact one_ne_zero this
  · intro h
    push_neg at h
    obtain ⟨y, hy⟩ := h
    refine ⟨(bil P u y)⁻¹ • y, ?_⟩
    rw [bil_smul_right, inv_mul_cancel₀ hy]

@[kb "kitaoka1993" "§5.6 [unverified] (hyperbolic pair count)"]
theorem card_reps_hyperbolic (L : QuadForm K m) :
    Nat.card {Y : Matrix (Fin (m + 2)) (Fin 2) K // (hypExt L).compMat Y = hyperbolic K} +
        Nat.card K ^ m * radZeroCount L =
      Nat.card K ^ m * zeroCount (hypExt L) := by
  classical
  haveI := Fintype.ofFinite K
  let S := {u : Fin (m + 2) → K // (hypExt L).eval u = 0 ∧ ∃ y, bil (hypExt L) u y = 1}
  haveI : Finite S := inferInstance
  haveI := Fintype.ofFinite S
  have e : {Y : Matrix (Fin (m + 2)) (Fin 2) K // (hypExt L).compMat Y = hyperbolic K} ≃
      Σ u : S, {w : Fin (m + 2) → K // (hypExt L).eval w = 0 ∧ bil (hypExt L) u.1 w = 1} :=
    { toFun := fun Y =>
        ⟨⟨col Y.1 0, ((compMat_eq_hyperbolic_iff _ Y.1).1 Y.2).1,
            col Y.1 1, ((compMat_eq_hyperbolic_iff _ Y.1).1 Y.2).2.2⟩,
          ⟨col Y.1 1, ((compMat_eq_hyperbolic_iff _ Y.1).1 Y.2).2.1, ((compMat_eq_hyperbolic_iff _ Y.1).1 Y.2).2.2⟩⟩
      invFun := fun x => ⟨Matrix.of fun i j => ![x.1.1, x.2.1] j i, by
        rw [compMat_eq_hyperbolic_iff]
        exact ⟨x.1.2.1, x.2.2.1, x.2.2.2⟩⟩
      left_inv := fun Y => by
        refine Subtype.ext ?_
        ext i j
        fin_cases j <;> rfl
      right_inv := by
        rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
        rfl }
  have hfib : ∀ x : S, Nat.card {w : Fin (m + 2) → K // (hypExt L).eval w = 0 ∧ bil (hypExt L) x.1 w = 1} =
      Nat.card K ^ m := fun x => by
    obtain ⟨u, hu, y, hy⟩ := x
    exact partner_card L u y hu hy
  have h1 : Nat.card {Y : Matrix (Fin (m + 2)) (Fin 2) K // (hypExt L).compMat Y = hyperbolic K} =
      Nat.card S * Nat.card K ^ m := by
    rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun x _ => hfib x), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have h2 : Nat.card S = Nat.card {u : Fin (m + 2) → K // (hypExt L).eval u = 0 ∧ ¬ ∀ y, bil (hypExt L) u y = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => by rw [exists_partner_iff])
  have h3 := card_split (α := Fin (m + 2) → K) (fun u => (hypExt L).eval u = 0)
    (fun u => ∀ y, bil (hypExt L) u y = 0)
  have h4 : radZeroCount (hypExt L) = radZeroCount L := radZeroCount_hypExt L
  unfold radZeroCount at h4
  unfold radZeroCount zeroCount
  rw [h1, ← h4, ← h3, h2]
  ring

end Main

end QuadFormsKB.LocalDensity.HypFrame
