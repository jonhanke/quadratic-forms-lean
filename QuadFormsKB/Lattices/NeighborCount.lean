/-
# Kneser neighbours over a Dedekind domain, part 1: The quadratic and polar forms, and counts over a finite field

**Layer:** a form $Q$ (`QuadForm R n`) over any commutative ring $R$, evaluated in an $R$-algebra $S$: $\bar Q(\vec x) = Q(\vec x)$
(`qv S Q`) and the polar form $\bar B(\vec x, \vec y) = \vec x^{\mathsf T}\bar H\vec y$ (`bv S Q`, $H = C + C^{\mathsf T}$ the Hessian), so
$\bar Q(\vec x + t\vec y) = \bar Q(\vec x) + t\bar B(\vec x, \vec y) + t^2\bar Q(\vec y)$ and $\bar B(\vec x, \vec x) = 2\bar Q(\vec x)$. Typical uses:
$S = K$ the fraction field of $R$ (the global form) and $S = k = R/\mathfrak p$ a residue field (the reduction mod $\mathfrak p$).

**Counts over a finite field** $k$ with $q = |k|$, $\operatorname{char}k \ne 2$, $\det\bar H \ne 0$ (a good prime):
- for $\vec x \ne 0$: $\#\{\vec y : \bar B(\vec x, \vec y) = d\} = q^{n-1}$ (`card_bv_eq`);
- for $\bar Q(\vec x) \ne 0$, $n$ even, if $\bar Q$ takes every nonzero value equally often (true for $n$ even, Table 1):
  $\#\{\vec y \in \vec x^\perp : \bar Q(\vec y) = 0\} = q^{n-2}$ (`card_perp_anisotropic`).

These generalize `Siegel/NeighborCount.lean` (over $\mathbb F_p$) to any finite field; the proofs are the same
(translation along $\vec x$, and the count $\#\{(t,s) : s^2 - t^2 = e\} = q - 1 + q[e = 0]$). The isotropic counts
$\#\{\bar Q = c\}$ themselves come from Table 1 over $F$ (`LocalDensity.NF.card_mod_p_of_unimodular`).
-/
import QuadFormsKB.LocalDensity.Hensel
import QuadFormsKB.LocalDensity.JordanForm

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Lattices.Nbr

variable {R : Type*} [CommRing R] {n : ℕ}

section Ring

variable (S : Type*) [CommRing S] [Algebra R S] (Q : QuadForm R n)

/-- **The form in an $R$-algebra $S$:** $\bar Q(\vec y) = Q(\vec y) \in S$ for $\vec y \in S^n$ (`QuadForm.evalIn`). -/
abbrev qv (y : Fin n → S) : S := Q.evalIn S y

/-- **The polar form in $S$:** $\bar B(\vec x, \vec y) = \vec x^{\mathsf T}\bar H\vec y$ ($H = C + C^{\mathsf T}$ the Hessian, mapped to $S$), so
$\bar Q(\vec x + \vec y) = \bar Q(\vec x) + \bar Q(\vec y) + \bar B(\vec x, \vec y)$. -/
def bv (x y : Fin n → S) : S := x ⬝ᵥ (Q.hessian.map (algebraMap R S) *ᵥ y)

variable {S Q}

theorem qv_add_smul (x y : Fin n → S) (t : S) :
    qv S Q (x + t • y) = qv S Q x + t * bv S Q x y + t ^ 2 * qv S Q y := by
  have h1 := QuadForm.polar_eq_hessian S Q x (t • y)
  have h2 : Q.evalIn S (t • y) = t ^ 2 * Q.evalIn S y := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
  unfold bv
  linear_combination h1 + h2

theorem hessian_transpose (Q : QuadForm R n) : Q.hessianᵀ = Q.hessian := by
  ext i j; simp [QuadForm.hessian, add_comm]

theorem bv_comm (x y : Fin n → S) : bv S Q x y = bv S Q y x := by
  unfold bv
  have hs : (Q.hessian.map (algebraMap R S))ᵀ = Q.hessian.map (algebraMap R S) := by
    rw [← Matrix.transpose_map, hessian_transpose]
  conv_lhs => rw [← hs]
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

theorem bv_add_right (x y z : Fin n → S) : bv S Q x (y + z) = bv S Q x y + bv S Q x z := by
  simp [bv, mulVec_add, dotProduct_add]

theorem bv_add_left (x y z : Fin n → S) : bv S Q (x + y) z = bv S Q x z + bv S Q y z := by
  simp [bv, add_dotProduct]

theorem bv_smul_right (x y : Fin n → S) (t : S) : bv S Q x (t • y) = t * bv S Q x y := by
  simp [bv, mulVec_smul, dotProduct_smul]

theorem bv_smul_left (x y : Fin n → S) (t : S) : bv S Q (t • x) y = t * bv S Q x y := by
  simp [bv, smul_dotProduct]

theorem bv_sub_right (x y z : Fin n → S) : bv S Q x (y - z) = bv S Q x y - bv S Q x z := by
  simp [bv, mulVec_sub, dotProduct_sub]

theorem qv_zero : qv S Q 0 = 0 := by simp [QuadForm.evalIn]

theorem bv_zero_left (y : Fin n → S) : bv S Q 0 y = 0 := by simp [bv]

theorem bv_zero_right (y : Fin n → S) : bv S Q y 0 = 0 := by simp [bv]

theorem bv_self (x : Fin n → S) : bv S Q x x = 2 * qv S Q x := by
  have h1 := qv_add_smul (Q := Q) x x 1
  have h2 := qv_add_smul (Q := Q) 0 x 2
  rw [zero_add, qv_zero, bv_zero_left] at h2
  have e : x + (1 : S) • x = (2 : S) • x := by rw [one_smul, two_smul]
  rw [e, h2] at h1
  linear_combination -h1

theorem qv_smul (x : Fin n → S) (t : S) : qv S Q (t • x) = t ^ 2 * qv S Q x := by
  have h := qv_add_smul (Q := Q) 0 x t
  rwa [zero_add, qv_zero, bv_zero_left, mul_zero, zero_add, zero_add] at h

/-- **Base change:** for an $S$-algebra $T$ (compatible with $R$), $\bar Q$ and $\bar B$ commute with $S \to T$. -/
theorem qv_map {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : Fin n → S) :
    qv T Q (fun i => algebraMap S T (x i)) = algebraMap S T (qv S Q x) := by
  simp only [qv, QuadForm.evalIn, map_sum, map_mul, apply_ite (algebraMap S T), map_zero,
    IsScalarTower.algebraMap_apply R S T]

theorem bv_map {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x y : Fin n → S) :
    bv T Q (fun i => algebraMap S T (x i)) (fun i => algebraMap S T (y i)) = algebraMap S T (bv S Q x y) := by
  simp only [bv, dotProduct, mulVec, Matrix.map_apply, map_sum, map_mul, IsScalarTower.algebraMap_apply R S T]

end Ring

/-! ### Counts over a finite field -/

section FF

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] [Algebra R k] {Q : QuadForm R n}

/-- **The polar functional of $\vec x \ne 0$ takes each value $q^{n-1}$ times** ($\det\bar H \ne 0$, so $\vec x^{\mathsf T}\bar H \ne 0$). -/
theorem card_bv_eq (hdet : (Q.hessian.map (algebraMap R k)).det ≠ 0) {x : Fin n → k} (hx : x ≠ 0)
    (d : k) : (Finset.univ.filter fun y => bv k Q x y = d).card = Fintype.card k ^ (n - 1) := by
  set H := Q.hessian.map (algebraMap R k)
  set w := x ᵥ* H
  have hw : w ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hdet h)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  have hb : ∀ y, bv k Q x y = ∑ i, w i * y i := by
    intro y; show x ⬝ᵥ (H *ᵥ y) = _; rw [dotProduct_mulVec]; rfl
  have := LocalDensity.DVR.nat_card_linear_eq_of_isUnit (n := n) w i0 (Ne.isUnit hi0) d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card] at this
  simp_rw [hb]; exact this

theorem two_ne_zero_of_ringChar (hk : ringChar k ≠ 2) : (2 : k) ≠ 0 := Ring.two_ne_zero hk

/-- $\#\{(u, w) \in k^2 : uw = e\} = q - 1 + q[e = 0]$. -/
theorem sum_mul_eq (e : k) :
    (∑ u : k, ∑ w : k, if u * w = e then (1 : ℤ) else 0) =
      (Fintype.card k - 1 : ℤ) + if e = 0 then (Fintype.card k : ℤ) else 0 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h1 : ∀ u ∈ Finset.univ.erase (0 : k), (∑ w : k, if u * w = e then (1 : ℤ) else 0) = 1 := by
    intro u hu
    have hu0 := Finset.ne_of_mem_erase hu
    rw [Finset.sum_eq_single (u⁻¹ * e)]
    · rw [if_pos (by field_simp)]
    · intro w _ hw
      rw [if_neg]
      intro h; apply hw; rw [← h]; field_simp
    · simp
  rw [Finset.sum_congr rfl h1]
  simp only [zero_mul, Finset.sum_const, Finset.card_univ, Finset.card_erase_of_mem
    (Finset.mem_univ _), nsmul_eq_mul, mul_one]
  have hq1 : 1 ≤ Fintype.card k := Fintype.card_pos
  by_cases he : e = 0
  · subst he; simp [Nat.cast_sub hq1]; ring
  · rw [if_neg (Ne.symm he), if_neg he]; simp [Nat.cast_sub hq1]

/-- $\#\{(t, s) \in k^2 : s^2 - t^2 = e\} = q - 1 + q[e = 0]$ for $\operatorname{char}k \ne 2$ ($(t,s) \mapsto (s - t, s + t)$). -/
theorem sum_sq_sub_sq_eq (hk : ringChar k ≠ 2) (e : k) :
    (∑ t : k, ∑ s : k, if s ^ 2 - t ^ 2 = e then (1 : ℤ) else 0) =
      (Fintype.card k - 1 : ℤ) + if e = 0 then (Fintype.card k : ℤ) else 0 := by
  have h2 := two_ne_zero_of_ringChar hk
  rw [← sum_mul_eq e, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let E : k × k ≃ k × k :=
    { toFun := fun ts => (ts.2 - ts.1, ts.2 + ts.1)
      invFun := fun uw => ((uw.2 - uw.1) / 2, (uw.1 + uw.2) / 2)
      left_inv := fun ts => by ext <;> simp <;> field_simp <;> ring
      right_inv := fun uw => by ext <;> simp <;> field_simp <;> ring }
  refine Fintype.sum_equiv E _ _ fun ts => ?_
  simp only [E, Equiv.coe_fn_mk]
  congr 1; apply propext; constructor <;> intro h <;> linear_combination h

/-- **Isotropic vectors orthogonal to an anisotropic $\vec x$** ($n$ even, $n \ge 2$, $\operatorname{char}k \ne 2$, $\det\bar H \ne 0$,
$\bar Q(\vec x) \ne 0$), given that $\bar Q$ takes every nonzero value equally often (`hconst`; Table 1 for $n$ even):
$\#\{\vec y : \bar Q(\vec y) = 0,\ \bar B(\vec x, \vec y) = 0\} = q^{n-2}$. -/
theorem card_perp_anisotropic (hk : ringChar k ≠ 2) (hdet : (Q.hessian.map (algebraMap R k)).det ≠ 0)
    (hn2 : 2 ≤ n)
    (hconst : ∀ c : k, c ≠ 0 → (Finset.univ.filter fun y => qv k Q y = c).card =
      (Finset.univ.filter fun y => qv k Q y = 1).card)
    {x : Fin n → k} (hx : qv k Q x ≠ 0) :
    (Finset.univ.filter fun y => qv k Q y = 0 ∧ bv k Q x y = 0).card = Fintype.card k ^ (n - 2) := by
  classical
  have h2 := two_ne_zero_of_ringChar hk
  set q := Fintype.card k with hq
  set a := qv k Q x with ha
  set χ := quadraticChar k
  set S : ℤ := ∑ y : Fin n → k, ∑ s : k, if qv k Q y = a * s ^ 2 then (1 : ℤ) else 0 with hS
  have hS1 : S = (q : ℤ) ^ n := by
    have hrow : ∀ y : Fin n → k, (∑ s : k, if qv k Q y = a * s ^ 2 then (1 : ℤ) else 0) =
        χ (qv k Q y * a⁻¹) + 1 := by
      intro y
      rw [← quadraticChar_card_sqrts hk, Finset.sum_boole]
      congr 2
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
        Set.mem_ofPred_eq]
      constructor <;> intro h
      · rw [h]; field_simp
      · rw [h]; field_simp
    rw [hS, Finset.sum_congr rfl fun y _ => hrow y, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Nat.cast_pow]
    suffices hχ : ∑ y : Fin n → k, χ (qv k Q y * a⁻¹) = 0 by rw [hχ, zero_add]
    have hfib : ∑ y : Fin n → k, χ (qv k Q y * a⁻¹) =
        ∑ c : k, ((Finset.univ.filter fun y => qv k Q y = c).card : ℤ) * χ (c * a⁻¹) := by
      rw [← Finset.sum_fiberwise Finset.univ (qv k Q)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2], Finset.sum_const,
        nsmul_eq_mul]
    rw [hfib]
    have hc' : ∀ c : k, ((Finset.univ.filter fun y => qv k Q y = c).card : ℤ) * χ (c * a⁻¹) =
        ((Finset.univ.filter fun y => qv k Q y = 1).card : ℤ) * χ (c * a⁻¹) := by
      intro c
      by_cases hc : c = 0
      · subst hc
        rw [zero_mul, show χ 0 = 0 from quadraticChar_zero, mul_zero, mul_zero]
      · rw [hconst c hc]
    rw [Finset.sum_congr rfl fun c _ => hc' c, ← Finset.mul_sum]
    have : ∑ c : k, χ (c * a⁻¹) = ∑ c : k, χ c :=
      Fintype.sum_equiv (Equiv.mulRight₀ a⁻¹ (inv_ne_zero hx)) _ _ fun c => rfl
    rw [this, quadraticChar_sum_zero hk, mul_zero]
  set Z := {z : Fin n → k // bv k Q x z = 0}
  have hbxx : bv k Q x x = 2 * a := bv_self x
  let E : Z × k ≃ (Fin n → k) :=
    { toFun := fun zt => zt.1.1 + zt.2 • x
      invFun := fun y => (⟨y - (bv k Q x y / (2 * a)) • x, by
          rw [bv_sub_right, bv_smul_right, hbxx]; field_simp; ring⟩, bv k Q x y / (2 * a))
      left_inv := fun zt => by
        obtain ⟨⟨z, hz⟩, t⟩ := zt
        have : bv k Q x (z + t • x) / (2 * a) = t := by
          rw [bv_add_right, bv_smul_right, hz, hbxx]; field_simp; ring
        ext <;> simp [this]
      right_inv := fun y => by simp }
  have hS2 : S = ((q : ℤ) - 1) * q ^ (n - 1) +
      q * (Finset.univ.filter fun y => qv k Q y = 0 ∧ bv k Q x y = 0).card := by
    rw [hS, ← Fintype.sum_equiv E (fun zt => ∑ s : k,
      if qv k Q (zt.1.1 + zt.2 • x) = a * s ^ 2 then (1 : ℤ) else 0) _ (fun _ => rfl),
      Fintype.sum_prod_type]
    have hrow : ∀ z : Z, (∑ t : k, ∑ s : k,
        if qv k Q (z.1 + t • x) = a * s ^ 2 then (1 : ℤ) else 0) =
        (q - 1 : ℤ) + if qv k Q z.1 = 0 then (q : ℤ) else 0 := by
      intro z
      have : ∀ t s : k, (qv k Q (z.1 + t • x) = a * s ^ 2) ↔ s ^ 2 - t ^ 2 = qv k Q z.1 * a⁻¹ := by
        intro t s
        rw [qv_add_smul, bv_comm, z.2, ← ha]
        constructor <;> intro h
        · field_simp; linear_combination -h
        · field_simp at h; linear_combination -h
      simp_rw [this]
      rw [sum_sq_sub_sq_eq hk]
      congr 1
      simp [hx, hq]
    rw [Finset.sum_congr rfl fun z _ => hrow z, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ]
    have hZ : Fintype.card Z = q ^ (n - 1) := by
      rw [Fintype.card_subtype]; exact card_bv_eq hdet (fun h => hx (by rw [ha, h, qv_zero])) 0
    rw [hZ, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    have hc : (Finset.univ.filter fun z : Z => qv k Q z.1 = 0).card =
        (Finset.univ.filter fun y => qv k Q y = 0 ∧ bv k Q x y = 0).card := by
      refine Finset.card_nbij' (fun z => z.1) (fun y => if h : bv k Q x y = 0 then ⟨y, h⟩ else ⟨0, by
        rw [bv_comm, bv_zero_left]⟩) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
        exact ⟨hz, z.2⟩
      · intro y hy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
        rw [dif_pos hy.2]; exact hy.1
      · intro z _; simp [z.2]
      · intro y hy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
        simp [hy.2]
    rw [hc]; ring
  have := hS1.symm.trans hS2
  have hpow : (q : ℤ) ^ n = q * q ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hpow2 : (q : ℤ) ^ (n - 1) = q * q ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
  rw [hpow, hpow2] at this
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h' : ((Finset.univ.filter fun y => qv k Q y = 0 ∧ bv k Q x y = 0).card : ℤ) = q ^ (n - 2) := by
    have := mul_left_cancel₀ hq0 (show (q : ℤ) * ((Finset.univ.filter fun y => qv k Q y = 0 ∧
      bv k Q x y = 0).card : ℤ) = q * q ^ (n - 2) by linear_combination -this)
    exact this
  exact_mod_cast h'

end FF

end QuadFormsKB.Lattices.Nbr
