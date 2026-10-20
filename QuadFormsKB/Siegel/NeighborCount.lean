/-
# Kneser neighbours, part 1: isotropic vectors of a form over $\mathbb{F}_p$

**Layer:** integral forms $Q$ (`QuadForm ℤ n`) reduced mod an odd prime $p \nmid \det H$ ($H$ the Hessian), i.e. the
nondegenerate quadratic space $(\mathbb{F}_p^n, \bar Q)$ with polar form $\bar B(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T}\bar H\vec{y}$
(`bv`, so $\bar B(\vec{x}, \vec{x}) = 2\bar Q(\vec{x})$).

**Proves** the counts used by Kneser's neighbour method (`Siegel/Neighbors.lean`) and the Eichler commutation relation
(`Siegel/EichlerCommutation.lean`), for **even** $n$, with $\varepsilon = \left(\frac{(-1)^{n/2}\det H}{p}\right)$:
- $\#\{\vec{y} : \bar Q(\vec{y}) = 0\} = p^{n-1} + \varepsilon(p-1)p^{n/2-1}$ and $\#\{\vec{y} : \bar Q(\vec{y}) = c\} = p^{n-1} - \varepsilon p^{n/2-1}$
  for $c \ne 0$ (`card_qv_zero`, `card_qv_ne_zero`; from Table 1, `LocalDensity.card_diag_mod_p`, via the determinant-tracking
  diagonalization `exists_diag_unimodular_same_counts_det`);
- for $\vec{x} \ne 0$: $\#\{\vec{y} : \bar B(\vec{x}, \vec{y}) = d\} = p^{n-1}$ (`card_bv_eq`);
- for $\vec{x} \ne 0$ isotropic: $\#\{\vec{y} \in \vec{x}^\perp : \bar Q(\vec{y}) = 0\} + (p-1)p^{n-2} = \#\{\vec{y} : \bar Q(\vec{y}) = 0\}$
  (`card_perp_isotropic`, any $n \ge 2$);
- for $\bar Q(\vec{x}) \ne 0$: $\#\{\vec{y} \in \vec{x}^\perp : \bar Q(\vec{y}) = 0\} = p^{n-2}$ (`card_perp_anisotropic`, $n$ even).

For $n = 4$ ($\varepsilon = \left(\frac{\det H}{p}\right)$): $p^3 + \varepsilon p(p-1)$ isotropic vectors, so
$p^2 + p + 1 + \varepsilon p$ isotropic lines (`card_qv_zero_four`).

*Proof of the perpendicular counts (elementary, no Witt theorem).* Isotropic $\vec{x}$: translation $\vec{y} \mapsto \vec{y} + t\vec{x}$
shows $\#\{\bar Q = c, \bar B(\vec{x}, \cdot) = d\}$ is independent of $c$ for $d \ne 0$. Anisotropic $\vec{x}$, $a = \bar Q(\vec{x})$:
count $S = \#\{(\vec{y}, s) : \bar Q(\vec{y}) = a s^2\}$ twice: $S = p^n$ because $\bar Q$ takes every nonzero value equally often
($n$ even), and $S = (p-1)p^{n-1} + p\,\#\{\vec{z} \in \vec{x}^\perp : \bar Q(\vec{z}) = 0\}$ by $\vec{y} = \vec{z} + t\vec{x}$ and
$\#\{(t,s) : s^2 - t^2 = e\} = p - 1 + p[e = 0]$.
-/
import QuadFormsKB.Siegel.LocalProduct

open Matrix

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

section FF

variable (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]

/-- **The reduction $\bar Q$ of $Q$ mod $p$:** $\bar Q(\vec{y}) = Q(\vec{y}) \in \mathbb{F}_p$ for $\vec{y} \in \mathbb{F}_p^n$. -/
abbrev qv (y : Fin n → ZMod p) : ZMod p := Q.evalIn (ZMod p) y

/-- **The polar form mod $p$:** $\bar B(\vec{x}, \vec{y}) = \vec{x}^{\mathsf T} \bar H \vec{y}$ ($H = C + C^{\mathsf T}$ the Hessian), so
$\bar Q(\vec{x} + \vec{y}) = \bar Q(\vec{x}) + \bar Q(\vec{y}) + \bar B(\vec{x}, \vec{y})$ and $\bar B(\vec{x}, \vec{x}) = 2\bar Q(\vec{x})$. -/
def bv (x y : Fin n → ZMod p) : ZMod p := x ⬝ᵥ (Q.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ y)

variable {Q p}

theorem qv_add_smul (x y : Fin n → ZMod p) (t : ZMod p) :
    qv Q p (x + t • y) = qv Q p x + t * bv Q p x y + t ^ 2 * qv Q p y := by
  have h1 := QuadForm.polar_eq_hessian (ZMod p) Q x (t • y)
  have h2 : Q.evalIn (ZMod p) (t • y) = t ^ 2 * Q.evalIn (ZMod p) y := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
  unfold bv
  linear_combination h1 + h2

theorem bv_comm (x y : Fin n → ZMod p) : bv Q p x y = bv Q p y x := by
  unfold bv
  have hs : (Q.hessian.map (algebraMap ℤ (ZMod p)))ᵀ = Q.hessian.map (algebraMap ℤ (ZMod p)) := by
    rw [← Matrix.transpose_map, LocalDensity.hessian_isSymm Q]
  conv_lhs => rw [← hs]
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

theorem bv_add_right (x y z : Fin n → ZMod p) : bv Q p x (y + z) = bv Q p x y + bv Q p x z := by
  simp [bv, mulVec_add, dotProduct_add]

theorem bv_smul_right (x y : Fin n → ZMod p) (t : ZMod p) : bv Q p x (t • y) = t * bv Q p x y := by
  simp [bv, mulVec_smul, dotProduct_smul]

theorem bv_sub_right (x y z : Fin n → ZMod p) : bv Q p x (y - z) = bv Q p x y - bv Q p x z := by
  simp [bv, mulVec_sub, dotProduct_sub]

theorem qv_zero : qv Q p 0 = 0 := by simp [QuadForm.evalIn]

theorem bv_zero_left (y : Fin n → ZMod p) : bv Q p 0 y = 0 := by simp [bv]

theorem bv_self (x : Fin n → ZMod p) : bv Q p x x = 2 * qv Q p x := by
  have h1 := qv_add_smul (Q := Q) (p := p) x x 1
  have h2 := qv_add_smul (Q := Q) (p := p) 0 x 2
  rw [zero_add, qv_zero, bv_zero_left] at h2
  have e : x + (1 : ZMod p) • x = (2 : ZMod p) • x := by rw [one_smul, two_smul]
  rw [e, h2] at h1
  linear_combination -h1

theorem qv_smul (x : Fin n → ZMod p) (t : ZMod p) : qv Q p (t • x) = t ^ 2 * qv Q p x := by
  have h := qv_add_smul (Q := Q) (p := p) 0 x t
  rwa [zero_add, qv_zero, bv_zero_left, mul_zero, zero_add, zero_add] at h

/-- `repCount` mod $p$ (on $\mathbb{Z}/p^1$) is the $\mathbb{F}_p$-count of $\bar Q = m$. -/
theorem repCount_one_eq_card (m : ℤ) :
    LocalDensity.repCount Q p 1 m = (Finset.univ.filter fun y => qv Q p y = (m : ZMod p)).card := by
  unfold LocalDensity.repCount
  rw [pow_one, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h'
  have := (Fact.out : p.Prime).two_le
  have : p = 2 := by omega
  exact hp this

theorem ringChar_ne_two (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp

/-- **The discriminant sign** $\varepsilon = \left(\frac{(-1)^{n/2}\det H}{p}\right)$ (meaningful for even $n$; for $n = 4$ it is
$\left(\frac{\det H}{p}\right)$, the value at $p$ of the character of $\theta_Q$). -/
noncomputable def discSign (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : ℤ := legendreSym p ((-1) ^ (n / 2) * Q.hessian.det)

theorem legendre_diag_eq (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : Even n) (a : Fin n → ℤ)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hdu : 2 ^ n * ∏ i, a i = u ^ 2 * Q.hessian.det) :
    legendreSym p ((-1) ^ (n / 2) * ∏ i, a i) = discSign Q p := by
  obtain ⟨k, rfl⟩ := hn
  have hk : (k + k) / 2 = k := by omega
  unfold discSign
  rw [hk]
  have h2 : ((2 : ℤ) ^ k : ZMod p) ≠ 0 := by
    push_cast; exact pow_ne_zero _ (two_ne_zero_zmod hp)
  have h2' : (((2 ^ k : ℤ)) : ZMod p) ≠ 0 := by exact_mod_cast h2
  have hu' : ((u : ℤ) : ZMod p) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
  have e : (2 ^ k) ^ 2 * ((-1) ^ k * ∏ i, a i) = u ^ 2 * ((-1) ^ k * Q.hessian.det) := by
    rw [← pow_mul, show k * 2 = k + k by ring]; linear_combination (-1) ^ k * hdu
  have := congrArg (legendreSym p) e
  rwa [legendreSym.mul p ((2 ^ k) ^ 2), legendreSym.mul p (u ^ 2), legendreSym.sq_one' p h2',
    legendreSym.sq_one' p hu', one_mul, one_mul] at this

/-- **Isotropic vectors mod $p$** ($n$ even, $p$ odd, $p \nmid \det H$):
$\#\{\vec{y} \in \mathbb{F}_p^n : \bar Q(\vec{y}) = 0\} = p^{n-1} + \varepsilon(p-1)p^{n/2-1}$, $\varepsilon$ = `discSign Q p`. -/
@[kb "hanke2004" "Table 1, p. 363 (general form, via Lemma 2.1)"]
theorem card_qv_zero (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : Even n) (hn1 : 1 ≤ n) :
    ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) =
      p ^ (n - 1) + discSign Q p * (p - 1) * p ^ (n / 2 - 1) := by
  obtain ⟨a, ha, hc, u, hu, hdu⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  have h := ((LocalDensity.card_diag_mod_p a p hp ha hn1 1 (by
    intro h; exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by omega) h))).1 hn).1
  rw [← hc, repCount_one_eq_card, legendre_diag_eq hp hdet hn a u hu hdu] at h
  simpa using h

/-- **Nonzero values mod $p$** ($n$ even, $p$ odd, $p \nmid \det H$, $c \ne 0$):
$\#\{\vec{y} : \bar Q(\vec{y}) = c\} = p^{n-1} - \varepsilon p^{n/2-1}$, independent of $c$. -/
@[kb "hanke2004" "Table 1, p. 363 (general form, via Lemma 2.1)"]
theorem card_qv_ne_zero (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : Even n) (hn1 : 1 ≤ n)
    (c : ZMod p) (hc0 : c ≠ 0) :
    ((Finset.univ.filter fun y => qv Q p y = c).card : ℤ) = p ^ (n - 1) - discSign Q p * p ^ (n / 2 - 1) := by
  obtain ⟨a, ha, hc, u, hu, hdu⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  have hcu : ¬ (p : ℤ) ∣ ((c.val : ℕ) : ℤ) := by
    intro h
    apply hc0
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    simpa using this
  have h := ((LocalDensity.card_diag_mod_p a p hp ha hn1 _ hcu).1 hn).2
  rw [← hc, repCount_one_eq_card, legendre_diag_eq hp hdet hn a u hu hdu] at h
  simpa using h

/-- **The polar functional of $\vec{x} \ne 0$ takes each value $p^{n-1}$ times** ($p \nmid \det H$, so $\bar H$ is invertible
and $\vec{x}^{\mathsf T}\bar H \ne 0$). -/
theorem card_bv_eq (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {x : Fin n → ZMod p} (hx : x ≠ 0) (d : ZMod p) :
    (Finset.univ.filter fun y => bv Q p x y = d).card = p ^ (n - 1) := by
  set H := Q.hessian.map (algebraMap ℤ (ZMod p))
  have hH : H.det ≠ 0 := by
    have : H.det = algebraMap ℤ (ZMod p) Q.hessian.det := (RingHom.map_det _ _).symm
    rw [this]
    intro h
    exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by simpa using h))
  set w := x ᵥ* H
  have hw : w ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hH h)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  have hb : ∀ y, bv Q p x y = ∑ i, w i * y i := by
    intro y; show x ⬝ᵥ (H *ᵥ y) = _; rw [dotProduct_mulVec]; rfl
  have := LocalDensity.DVR.nat_card_linear_eq_of_isUnit (n := n) w i0 (Ne.isUnit hi0) d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_zmod] at this
  simp_rw [hb]; exact this

/-- **Translation along an isotropic vector:** for $\bar Q(\vec{x}) = 0$ and $d \ne 0$, the number of $\vec{y}$ with
$\bar Q(\vec{y}) = c$, $\bar B(\vec{x}, \vec{y}) = d$ does not depend on $c$ ($\vec{y} \mapsto \vec{y} + (c/d)\vec{x}$). -/
theorem card_qv_bv_shift {x : Fin n → ZMod p} (hx : qv Q p x = 0) {d : ZMod p} (hd : d ≠ 0) (c : ZMod p) :
    (Finset.univ.filter fun y => qv Q p y = c ∧ bv Q p x y = d).card =
      (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = d).card := by
  set t := c / d
  have key : ∀ y : Fin n → ZMod p, ∀ s : ZMod p, qv Q p (y + s • x) = qv Q p y + s * bv Q p x y ∧
      bv Q p x (y + s • x) = bv Q p x y := by
    intro y s
    refine ⟨?_, ?_⟩
    · rw [qv_add_smul, hx, bv_comm]; ring
    · rw [bv_add_right, bv_smul_right, bv_self, hx]; ring
  refine Finset.card_nbij' (fun y => y - t • x) (fun y => y + t • x) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    have h1 := key y (-t)
    rw [neg_smul, ← sub_eq_add_neg] at h1
    rw [h1.1, h1.2, hy.1, hy.2]
    refine ⟨?_, rfl⟩
    simp only [t]; field_simp; ring
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    have h1 := key y t
    rw [h1.1, h1.2, hy.1, hy.2]
    refine ⟨?_, rfl⟩
    simp only [t]; field_simp; ring
  · intro y _; simp
  · intro y _; simp

/-- **Isotropic vectors orthogonal to an isotropic $\vec{x} \ne 0$** ($p \nmid \det H$, $n \ge 2$):
$$\#\{\vec{y} : \bar Q(\vec{y}) = 0,\ \bar B(\vec{x}, \vec{y}) = 0\} + (p-1)p^{n-2} = \#\{\vec{y} : \bar Q(\vec{y}) = 0\}.$$ -/
theorem card_perp_isotropic (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : 2 ≤ n) {x : Fin n → ZMod p}
    (hx0 : x ≠ 0) (hx : qv Q p x = 0) :
    (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = 0).card + (p - 1) * p ^ (n - 2) =
      (Finset.univ.filter fun y => qv Q p y = 0).card := by
  classical
  have hp := (Fact.out : p.Prime)
  -- for d ≠ 0 the count is p^(n-2)
  have hd : ∀ d : ZMod p, d ≠ 0 →
      (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = d).card = p ^ (n - 2) := by
    intro d hd
    have htot := card_bv_eq hdet hx0 d
    rw [Finset.card_eq_sum_card_fiberwise (f := qv Q p) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _))] at htot
    have e : ∀ c : ZMod p, (Finset.filter (fun a => qv Q p a = c)
        (Finset.univ.filter fun y => bv Q p x y = d)).card =
        (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = d).card := by
      intro c
      rw [Finset.filter_filter, ← card_qv_bv_shift hx hd c]
      congr 1; ext y; simp [and_comm]
    simp_rw [e] at htot
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at htot
    have : p ^ (n - 1) = p * p ^ (n - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [this] at htot
    exact Nat.eq_of_mul_eq_mul_left hp.pos htot
  have htot := Finset.card_eq_sum_card_fiberwise (f := bv Q p x) (t := Finset.univ)
    (s := Finset.univ.filter fun y => qv Q p y = 0) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [htot, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have e : ∀ d ∈ Finset.univ.erase (0 : ZMod p), (Finset.filter (fun a => bv Q p x a = d)
      (Finset.univ.filter fun y => qv Q p y = 0)).card = p ^ (n - 2) := by
    intro d hd'
    rw [Finset.filter_filter]
    exact hd d (Finset.ne_of_mem_erase hd')
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card, smul_eq_mul, Finset.filter_filter]

/-- $\#\{(u, w) \in \mathbb{F}_p^2 : uw = e\} = p - 1 + p[e = 0]$. -/
theorem sum_mul_eq (e : ZMod p) :
    (∑ u : ZMod p, ∑ w : ZMod p, if u * w = e then (1 : ℤ) else 0) =
      (p - 1 : ℤ) + if e = 0 then (p : ℤ) else 0 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h1 : ∀ u ∈ Finset.univ.erase (0 : ZMod p), (∑ w : ZMod p, if u * w = e then (1 : ℤ) else 0) = 1 := by
    intro u hu
    have hu0 := Finset.ne_of_mem_erase hu
    rw [Finset.sum_eq_single (u⁻¹ * e)]
    · rw [if_pos (by field_simp)]
    · intro w _ hw
      rw [if_neg]
      intro h; apply hw; rw [← h]; field_simp
    · simp
  rw [Finset.sum_congr rfl h1]
  simp only [zero_mul, Finset.sum_const, Finset.card_univ, ZMod.card, Finset.card_erase_of_mem
    (Finset.mem_univ _), nsmul_eq_mul, mul_one]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  by_cases he : e = 0
  · subst he; simp [Nat.cast_sub hp1]; ring
  · rw [if_neg (Ne.symm he), if_neg he]; simp [Nat.cast_sub hp1]

/-- $\#\{(t, s) \in \mathbb{F}_p^2 : s^2 - t^2 = e\} = p - 1 + p[e = 0]$ for $p$ odd ($(t,s) \mapsto (s - t, s + t)$). -/
theorem sum_sq_sub_sq_eq (hp : p ≠ 2) (e : ZMod p) :
    (∑ t : ZMod p, ∑ s : ZMod p, if s ^ 2 - t ^ 2 = e then (1 : ℤ) else 0) =
      (p - 1 : ℤ) + if e = 0 then (p : ℤ) else 0 := by
  have h2 := two_ne_zero_zmod hp
  rw [← sum_mul_eq e, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let E : ZMod p × ZMod p ≃ ZMod p × ZMod p :=
    { toFun := fun ts => (ts.2 - ts.1, ts.2 + ts.1)
      invFun := fun uw => ((uw.2 - uw.1) / 2, (uw.1 + uw.2) / 2)
      left_inv := fun ts => by ext <;> simp <;> field_simp <;> ring
      right_inv := fun uw => by ext <;> simp <;> field_simp <;> ring }
  refine Fintype.sum_equiv E _ _ fun ts => ?_
  simp only [E, Equiv.coe_fn_mk]
  congr 1; apply propext; constructor <;> intro h <;> linear_combination h

/-- **Isotropic vectors orthogonal to an anisotropic $\vec{x}$** ($n$ even, $n \ge 2$, $p$ odd, $p \nmid \det H$,
$\bar Q(\vec{x}) \ne 0$): $\#\{\vec{y} : \bar Q(\vec{y}) = 0,\ \bar B(\vec{x}, \vec{y}) = 0\} = p^{n-2}$
(the zeros of the nondegenerate $(n-1)$-dimensional form on $\vec{x}^\perp$). -/
theorem card_perp_anisotropic (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : Even n) (hn2 : 2 ≤ n)
    {x : Fin n → ZMod p} (hx : qv Q p x ≠ 0) :
    (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = 0).card = p ^ (n - 2) := by
  classical
  have hpp := (Fact.out : p.Prime)
  have h2 := two_ne_zero_zmod hp
  have hF := ringChar_ne_two hp
  set a := qv Q p x with ha
  set χ := quadraticChar (ZMod p)
  -- S counted via the fibres of qv
  set S : ℤ := ∑ y : Fin n → ZMod p, ∑ s : ZMod p, if qv Q p y = a * s ^ 2 then (1 : ℤ) else 0 with hS
  have hS1 : S = (p : ℤ) ^ n := by
    have hrow : ∀ y : Fin n → ZMod p, (∑ s : ZMod p, if qv Q p y = a * s ^ 2 then (1 : ℤ) else 0) =
        χ (qv Q p y * a⁻¹) + 1 := by
      intro y
      rw [← quadraticChar_card_sqrts hF, Finset.sum_boole]
      congr 2
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
        Set.mem_ofPred_eq]
      constructor <;> intro h
      · rw [h]; field_simp
      · rw [h]; field_simp
    rw [hS, Finset.sum_congr rfl fun y _ => hrow y, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one, Nat.cast_pow]
    suffices hχ : ∑ y : Fin n → ZMod p, χ (qv Q p y * a⁻¹) = 0 by rw [hχ, zero_add]
    -- group by the value c = qv y
    have hfib : ∑ y : Fin n → ZMod p, χ (qv Q p y * a⁻¹) =
        ∑ c : ZMod p, ((Finset.univ.filter fun y => qv Q p y = c).card : ℤ) * χ (c * a⁻¹) := by
      rw [← Finset.sum_fiberwise Finset.univ (qv Q p)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2], Finset.sum_const,
        nsmul_eq_mul]
    rw [hfib]
    have hN1 := card_qv_ne_zero hp hdet hn (by omega) (1 : ZMod p) one_ne_zero
    have hconst : ∀ c : ZMod p, ((Finset.univ.filter fun y => qv Q p y = c).card : ℤ) * χ (c * a⁻¹) =
        ((Finset.univ.filter fun y => qv Q p y = 1).card : ℤ) * χ (c * a⁻¹) := by
      intro c
      by_cases hc : c = 0
      · subst hc
        rw [zero_mul, show χ 0 = 0 from quadraticChar_zero, mul_zero, mul_zero]
      · rw [card_qv_ne_zero hp hdet hn (by omega) c hc, hN1]
    rw [Finset.sum_congr rfl fun c _ => hconst c, ← Finset.mul_sum]
    have : ∑ c : ZMod p, χ (c * a⁻¹) = ∑ c : ZMod p, χ c :=
      Fintype.sum_equiv (Equiv.mulRight₀ a⁻¹ (inv_ne_zero hx)) _ _ fun c => rfl
    rw [this, quadraticChar_sum_zero hF, mul_zero]
  -- S counted via y = z + t x with z ⟂ x
  set Z := {z : Fin n → ZMod p // bv Q p x z = 0}
  have hbxx : bv Q p x x = 2 * a := bv_self x
  let E : Z × ZMod p ≃ (Fin n → ZMod p) :=
    { toFun := fun zt => zt.1.1 + zt.2 • x
      invFun := fun y => (⟨y - (bv Q p x y / (2 * a)) • x, by
          rw [bv_sub_right, bv_smul_right, hbxx]; field_simp; ring⟩, bv Q p x y / (2 * a))
      left_inv := fun zt => by
        obtain ⟨⟨z, hz⟩, t⟩ := zt
        have : bv Q p x (z + t • x) / (2 * a) = t := by
          rw [bv_add_right, bv_smul_right, hz, hbxx]; field_simp; ring
        ext <;> simp [this]
      right_inv := fun y => by simp }
  have hS2 : S = ((p : ℤ) - 1) * p ^ (n - 1) +
      p * (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = 0).card := by
    rw [hS, ← Fintype.sum_equiv E (fun zt => ∑ s : ZMod p,
      if qv Q p (zt.1.1 + zt.2 • x) = a * s ^ 2 then (1 : ℤ) else 0) _ (fun _ => rfl),
      Fintype.sum_prod_type]
    have hrow : ∀ z : Z, (∑ t : ZMod p, ∑ s : ZMod p,
        if qv Q p (z.1 + t • x) = a * s ^ 2 then (1 : ℤ) else 0) =
        (p - 1 : ℤ) + if qv Q p z.1 = 0 then (p : ℤ) else 0 := by
      intro z
      have : ∀ t s : ZMod p, (qv Q p (z.1 + t • x) = a * s ^ 2) ↔ s ^ 2 - t ^ 2 = qv Q p z.1 * a⁻¹ := by
        intro t s
        rw [qv_add_smul, bv_comm, z.2, ← ha]
        constructor <;> intro h
        · field_simp; linear_combination -h
        · field_simp at h; linear_combination -h
      simp_rw [this]
      rw [sum_sq_sub_sq_eq hp]
      congr 1
      simp [hx]
    rw [Finset.sum_congr rfl fun z _ => hrow z, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ]
    have hZ : Fintype.card Z = p ^ (n - 1) := by
      rw [Fintype.card_subtype]; exact card_bv_eq hdet (fun h => hx (by rw [ha, h, qv_zero])) 0
    rw [hZ, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    have hc : (Finset.univ.filter fun z : Z => qv Q p z.1 = 0).card =
        (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = 0).card := by
      refine Finset.card_nbij' (fun z => z.1) (fun y => if h : bv Q p x y = 0 then ⟨y, h⟩ else ⟨0, by
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
  have hpow : (p : ℤ) ^ n = p * p ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hpow2 : (p : ℤ) ^ (n - 1) = p * p ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
  rw [hpow, hpow2] at this
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have h' : ((Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p x y = 0).card : ℤ) = p ^ (n - 2) := by
    have := mul_left_cancel₀ hp0 (show (p : ℤ) * ((Finset.univ.filter fun y => qv Q p y = 0 ∧
      bv Q p x y = 0).card : ℤ) = p * p ^ (n - 2) by linear_combination -this)
    exact this
  exact_mod_cast h'

/-- **$n = 4$:** $\#\{\vec{y} \in \mathbb{F}_p^4 : \bar Q(\vec{y}) = 0\} = p^3 + \varepsilon p(p - 1)$ with
$\varepsilon = \left(\frac{\det H}{p}\right)$, i.e. $(p-1)(p^2 + p + 1 + \varepsilon p)$ nonzero isotropic vectors and
$p^2 + p + 1 + \varepsilon p$ isotropic lines ($(p+1)^2$ if $\varepsilon = 1$, $p^2 + 1$ if $\varepsilon = -1$). -/
theorem card_qv_zero_four {Q : QuadForm ℤ 4} (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) =
      1 + (p - 1) * (p ^ 2 + p + 1 + legendreSym p Q.hessian.det * p) := by
  rw [card_qv_zero hp hdet (by decide) (by norm_num)]
  have : discSign Q p = legendreSym p Q.hessian.det := by simp [discSign]
  rw [this]; norm_num; ring

end FF

end QuadFormsKB.Siegel.Kneser
