/-
# Kneser neighbours, part 3: the Eichler commutation relation at the coefficient level

**Layer:** lattices in $\mathbb{Q}^n$ with the form of an integral positive definite $Q$ (`Siegel/Neighbors.lean`).

**Defines** the representation numbers of a lattice, $r_{L'}(m) = \#\{\vec{x} \in L' : Q(\vec{x}) = m\}$ (`latRep`; for
$L' = \mathbb{Z}^n$ it is $r_Q(m)$, `latRep_stdLat`), and $r_Q(m/p^2)$ (`repNumDiv`, $0$ unless $p^2 \mid m$).

**Proves** the **single-lattice neighbour relation** (Eichler's commutation relation for the $p$-neighbour operator, at
the level of $q$-coefficients): for $p$ an odd prime, $p \nmid \det H$, and $n = 4$, with $\varepsilon = \left(\frac{\det H}{p}\right)$,
$$\sum_{L' \sim_p \mathbb{Z}^4} r_{L'}(m) = r_Q(p^2m) + \big(p + [p \mid m]\,\varepsilon p\big)\, r_Q(m) + p^2\, r_Q(m/p^2)$$
(`sum_latRep_neighbors_four`); for general even $n$ the version multiplied by $p - 1$ (`sum_latRep_neighbors_even`).

*Proof.* Every $\vec{x}$ with $Q(\vec{x}) = m$ lying in some neighbour is $\frac1p\vec{y}$ with $\vec{y} \in \mathbb{Z}^n$, $Q(\vec{y}) = p^2m$. Count
the neighbours containing it, i.e. ($\times (p-1)$) the nonzero isotropic $\bar{\vec{v}}$ with $\frac1p\vec{y} \in L(\bar{\vec{v}})$:
- $p \nmid \vec{y}$: exactly the points of the line $\mathbb{F}_p\bar{\vec{y}}$: $p - 1$;
- $\vec{y} = p\vec{z}$, $p \nmid \vec{z}$: the isotropic $\bar{\vec{v}} \ne 0$ with $\bar B(\bar{\vec{z}}, \bar{\vec{v}}) = 0$: $p^{n-2} - 1$ if $p \nmid m$
  (`card_perp_anisotropic`), $p^{n-1} - (p-1)p^{n-2} + \varepsilon(p-1)p^{n/2-1} - 1$ if $p \mid m$ (`card_perp_isotropic`);
- $\vec{y} = p^2\vec{w}$: all of them.
The numbers of such $\vec{y}$ are $r_Q(p^2m) - r_Q(m)$, $r_Q(m) - r_Q(m/p^2)$, $r_Q(m/p^2)$.

*In Hecke-operator terms* (weight $2$, character $\chi$ with $\chi(p) = \varepsilon$, $T_p : a(m) \mapsto a(pm) + \chi(p)p\,a(m/p)$):
$T_p^2 a(m) = a(p^2m) + 2\chi(p)p\,a(m) + p^2 a(m/p^2)$, so the neighbour operator is
$K_p = T_p^2 - 2\chi(p)p + p + \chi(p)p\,[p \mid m]$ on coefficients — a **$T(p^2)$-type** relation, not the $T_p$-relation.
-/
import QuadFormsKB.Siegel.Neighbors

open Matrix

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-- **The representation numbers of a lattice** $L' \subset \mathbb{Q}^n$: $r_{L'}(m) = \#\{\vec{x} \in L' : Q(\vec{x}) = m\}$ (a `Nat.card`,
so $0$ if infinite; finite for positive definite $Q$ and $L' \subseteq \frac1p\mathbb{Z}^n$). -/
noncomputable def latRep (Q : QuadForm ℤ n) (L : Submodule ℤ (Fin n → ℚ)) (m : ℤ) : ℕ :=
  Nat.card {x : Fin n → ℚ // x ∈ L ∧ Q.evalIn ℚ x = m}

/-- **$r_Q(m/p^2)$**: `repNum Q (m / p^2)` if $p^2 \mid m$, and $0$ otherwise. -/
noncomputable def repNumDiv (Q : QuadForm ℤ n) (p : ℕ) (m : ℤ) : ℕ :=
  if (p : ℤ) ^ 2 ∣ m then repNum Q (m / (p : ℤ) ^ 2) else 0

/-- **$r_{\mathbb{Z}^n}(m) = r_Q(m)$:** the lattice representation numbers of the standard lattice are those of $Q$. -/
theorem latRep_stdLat (Q : QuadForm ℤ n) (m : ℤ) : latRep Q (stdLat n) m = repNum Q m := by
  unfold latRep repNum repSet
  refine Nat.card_congr
    { toFun := fun x => ⟨intPart x.1, by
        obtain ⟨⟨y, hy⟩, hq⟩ := x.2
        simp only [Set.mem_setOf_eq]
        rw [hy, intPart_cv]
        have := hq; rw [hy, evalIn_cv] at this; exact_mod_cast this⟩
      invFun := fun y => ⟨cv y.1, ⟨y.1, rfl⟩, by rw [evalIn_cv]; exact_mod_cast y.2⟩
      left_inv := fun x => by
        obtain ⟨x, ⟨y, rfl⟩, -⟩ := x
        simp
      right_inv := fun y => by simp }

section Single

open Classical

variable {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime]

/-- The solutions of $Q(\vec{y}) = M$ as a `Finset` (positive definite $Q$). -/
noncomputable def repFinset (hQ : IntQF.PosDef Q) (M : ℤ) : Finset (Fin n → ℤ) :=
  (IntQF.PosDef.repSet_finite hQ M).toFinset

theorem mem_repFinset (hQ : IntQF.PosDef Q) {M : ℤ} {y : Fin n → ℤ} : y ∈ repFinset hQ M ↔ Q.eval y = M := by
  simp [repFinset, repSet]

theorem card_repFinset (hQ : IntQF.PosDef Q) (M : ℤ) : (repFinset hQ M).card = repNum Q M := by
  unfold repFinset repNum
  rw [Nat.card_eq_card_finite_toFinset]

theorem eval_smulZ (c : ℤ) (z : Fin n → ℤ) : Q.eval (c • z) = c ^ 2 * Q.eval z := by
  have := eval_add_smulZ Q 0 z c
  simpa [bZ, QuadForm.evalIn] using this

/-- **Solutions divisible by $c$:** $\#\{\vec{y} : Q(\vec{y}) = c^2M,\ c \mid \vec{y}\} = r_Q(M)$ ($\vec{y} = c\vec{z}$). -/
theorem card_filter_dvd (hQ : IntQF.PosDef Q) {c : ℤ} (hc : c ≠ 0) (M : ℤ) :
    ((repFinset hQ (c ^ 2 * M)).filter fun y => ∀ i, c ∣ y i).card = repNum Q M := by
  rw [← card_repFinset hQ M]
  refine (Finset.card_nbij' (fun y => fun i => y i / c) (fun z => c • z) ?_ ?_ ?_ ?_)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_repFinset] at hy
    simp only [Finset.mem_coe, mem_repFinset]
    have e : y = c • fun i => y i / c := by
      ext i; simp only [Pi.smul_apply, smul_eq_mul]; rw [Int.mul_ediv_cancel' (hy.2 i)]
    have := hy.1
    rw [e, eval_smulZ] at this
    exact mul_left_cancel₀ (pow_ne_zero 2 hc) this
  · intro z hz
    simp only [Finset.mem_coe, mem_repFinset] at hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_repFinset]
    refine ⟨by rw [eval_smulZ, hz], fun i => ⟨z i, rfl⟩⟩
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy
    ext i; simp only [Pi.smul_apply, smul_eq_mul]; rw [Int.mul_ediv_cancel' (hy.2 i)]
  · intro z _
    ext i; simp [Int.mul_ediv_cancel_left _ hc]

/-- $\#\{\vec{y} : Q(\vec{y}) = p^2m,\ p \mid \vec{y}\} = r_Q(m)$. -/
theorem card_filter_red_eq_zero (hQ : IntQF.PosDef Q) (m : ℤ) :
    ((repFinset hQ ((p : ℤ) ^ 2 * m)).filter fun y => red p y = 0).card = repNum Q m := by
  rw [← card_filter_dvd hQ (c := p) (by exact_mod_cast hp.out.ne_zero) m]
  congr 1; ext y; simp [red_eq_zero_iff]

/-- The coordinatewise quotient $\vec{y}/p$ (exact when $p \mid \vec{y}$). -/
def divP (p : ℕ) (y : Fin n → ℤ) : Fin n → ℤ := fun i => y i / p

theorem eq_smul_divP {y : Fin n → ℤ} (hy : red p y = 0) : y = (p : ℤ) • divP p y := by
  ext i; simp only [Pi.smul_apply, smul_eq_mul, divP]
  rw [Int.mul_ediv_cancel' ((red_eq_zero_iff y).mp hy i)]

/-- $\#\{\vec{y} : Q(\vec{y}) = p^2m,\ p^2 \mid \vec{y}\} = r_Q(m/p^2)$ (`repNumDiv`). -/
theorem card_filter_red_divP (hQ : IntQF.PosDef Q) (m : ℤ) :
    ((repFinset hQ ((p : ℤ) ^ 2 * m)).filter fun y => red p y = 0 ∧ red p (divP p y) = 0).card =
      repNumDiv Q p m := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : ∀ y : Fin n → ℤ, (red p y = 0 ∧ red p (divP p y) = 0) ↔ ∀ i, (p : ℤ) ^ 2 ∣ y i := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩ i
      rw [eq_smul_divP h1]
      simp only [Pi.smul_apply, smul_eq_mul, sq]
      exact mul_dvd_mul_left _ ((red_eq_zero_iff _).mp h2 i)
    · intro h
      have h1 : red p y = 0 := (red_eq_zero_iff y).mpr fun i => (dvd_pow_self _ two_ne_zero).trans (h i)
      refine ⟨h1, (red_eq_zero_iff _).mpr fun i => ?_⟩
      obtain ⟨c, hc⟩ := h i
      refine ⟨c, ?_⟩
      simp only [divP]; rw [hc, sq, mul_assoc, Int.mul_ediv_cancel_left _ hpZ]
  simp_rw [e]
  unfold repNumDiv
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := hm
    rw [Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hpZ), ← card_filter_dvd hQ (pow_ne_zero 2 hpZ) k,
      show (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * k) = ((p : ℤ) ^ 2) ^ 2 * k by ring]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy h
    rw [mem_repFinset] at hy
    apply hm
    have : y = ((p : ℤ) ^ 2) • fun i => y i / (p : ℤ) ^ 2 := by
      ext i; simp only [Pi.smul_apply, smul_eq_mul]; rw [Int.mul_ediv_cancel' (h i)]
    rw [this, eval_smulZ] at hy
    exact ⟨Q.eval _, by
      apply mul_left_cancel₀ (pow_ne_zero 2 hpZ); rw [← hy]; ring⟩

/-- **$r_{L(\bar{\vec{v}})}(m)$ as a count of integer vectors:** $\#\{\vec{y} : Q(\vec{y}) = p^2m,\ \frac1p\vec{y} \in L(\bar{\vec{v}})\}$. -/
theorem latRep_nbOf (hQ : IntQF.PosDef Q) (vb : Fin n → ZMod p) (m : ℤ) :
    latRep Q (nbOf Q p vb) m =
      ((repFinset hQ ((p : ℤ) ^ 2 * m)).filter fun y => (1 / (p : ℚ)) • cv y ∈ nbOf Q p vb).card := by
  have hp0 := p_ne_zero (p := p)
  unfold latRep
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun x => ⟨intPart ((p : ℚ) • x.1), by
        obtain ⟨hx, hq⟩ := x.2
        obtain ⟨y, hy⟩ := exists_eq_of_mem_nbLat hx
        have e : intPart ((p : ℚ) • x.1) = y := by
          rw [hy, smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv]
        rw [Finset.mem_filter, mem_repFinset, e, ← hy]
        refine ⟨?_, hx⟩
        rw [hy, evalIn_smulQ, evalIn_cv] at hq
        have : (Q.eval y : ℚ) = (p : ℚ) ^ 2 * m := by field_simp at hq; linear_combination hq
        exact_mod_cast this⟩
      invFun := fun y => ⟨(1 / (p : ℚ)) • cv y.1, by
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp y.2
        refine ⟨hy2, ?_⟩
        rw [evalIn_smulQ, evalIn_cv, (mem_repFinset hQ).mp hy1]
        push_cast; field_simp⟩
      left_inv := fun x => by
        obtain ⟨x, hx, -⟩ := x
        obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hx
        simp only [Subtype.mk.injEq]
        rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv]
      right_inv := fun y => by
        apply Subtype.ext
        show intPart ((p : ℚ) • ((1 / (p : ℚ)) • cv y.1)) = y.1
        rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv] }

/-- **Neighbours containing $\frac1p\vec{y}$, $p \nmid \vec{y}$:** $(p - 1)$ isotropic vectors (one line). -/
theorem card_mem_of_red_ne_zero (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {m : ℤ} {y : Fin n → ℤ}
    (hy : Q.eval y = (p : ℤ) ^ 2 * m) (hy0 : red p y ≠ 0) :
    ((isoSet Q p).filter fun vb => (1 / (p : ℚ)) • cv y ∈ nbOf Q p vb).card = p - 1 := by
  rw [← card_line hy0]
  have hy2 : (p : ℤ) ^ 2 ∣ Q.eval y := ⟨m, hy⟩
  have hqy : qv Q p (red p y) = 0 := by
    rw [qv_red, dvd_of_red]; exact (dvd_pow_self _ two_ne_zero).trans hy2
  congr 1
  ext vb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hv, hmem⟩
    obtain ⟨h1, h2⟩ := liftV_spec hdet hv
    unfold nbOf at hmem
    rw [mem_nbLat_iff_of_red_ne_zero h2 hy2 hy0, h1] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hc, zero_smul])
    exact ⟨(mem_isoSet.mp hv).1, c⁻¹, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  · rintro ⟨hv0, c, rfl⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
    have hv : c • red p y ∈ isoSet Q p := by
      rw [mem_isoSet, qv_smul, hqy, mul_zero]; exact ⟨hv0, rfl⟩
    refine ⟨hv, ?_⟩
    obtain ⟨h1, h2⟩ := liftV_spec hdet hv
    unfold nbOf
    rw [mem_nbLat_iff_of_red_ne_zero h2 hy2 hy0, h1]
    exact ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

/-- **Neighbours containing $\vec{z} \in \mathbb{Z}^n$:** the isotropic $\bar{\vec{v}} \ne 0$ with $\bar B(\bar{\vec{z}}, \bar{\vec{v}}) = 0$. -/
theorem card_mem_cv (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (z : Fin n → ℤ) :
    ((isoSet Q p).filter fun vb => cv z ∈ nbOf Q p vb).card =
      ((isoSet Q p).filter fun vb => bv Q p (red p z) vb = 0).card := by
  congr 1
  ext vb
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hv
  obtain ⟨h1, h2⟩ := liftV_spec hdet hv
  unfold nbOf
  rw [cv_mem_nbLat_iff h2, ← dvd_of_red, ← bv_red, h1]

/-- **The neighbour count of $\frac1p\vec{y}$** ($n$ even, $p$ odd, $p \nmid \det H$, $Q(\vec{y}) = p^2m$): with
$N_0 = \#\{\bar Q = 0\}$ and $\kappa = p^{n-2}$ if $p \nmid m$, $\kappa = N_0 - (p-1)p^{n-2}$ if $p \mid m$,
$$\#\{\bar{\vec{v}} : \tfrac1p\vec{y} \in L(\bar{\vec{v}})\} = (p - 1) + (\kappa - p)[p \mid \vec{y}] + (N_0 - \kappa)[p^2 \mid \vec{y}].$$ -/
theorem card_mem_eq (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hn : Even n) (hn2 : 2 ≤ n) {m : ℤ}
    {y : Fin n → ℤ} (hy : Q.eval y = (p : ℤ) ^ 2 * m) :
    (((isoSet Q p).filter fun vb => (1 / (p : ℚ)) • cv y ∈ nbOf Q p vb).card : ℤ) =
      ((p : ℤ) - 1) +
        (if red p y = 0 then
          (if (p : ℤ) ∣ m then ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) - (p - 1) * p ^ (n - 2)
            else (p : ℤ) ^ (n - 2)) - p else 0) +
        (if red p y = 0 ∧ red p (divP p y) = 0 then
          ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) -
            (if (p : ℤ) ∣ m then ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) - (p - 1) * p ^ (n - 2)
              else (p : ℤ) ^ (n - 2)) else 0) := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp0 := p_ne_zero (p := p)
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set N0 := ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ)
  have hiso : ((isoSet Q p).card : ℤ) = N0 - 1 := by
    have := card_isoSet (Q := Q) (p := p); simp only [N0]; rw [← this]; push_cast; ring
  set κ : ℤ := if (p : ℤ) ∣ m then N0 - (p - 1) * p ^ (n - 2) else (p : ℤ) ^ (n - 2) with hκ
  by_cases hy0 : red p y = 0
  · set z := divP p y
    have hyz := eq_smul_divP hy0
    have e : (1 / (p : ℚ)) • cv y = cv z := by
      rw [hyz, cv_smul, smul_smul]; push_cast; rw [show 1 / (p : ℚ) * p = 1 by field_simp, one_smul]
    have hz : Q.eval z = m := by
      have := hy; rw [hyz, eval_smulZ] at this; exact mul_left_cancel₀ (pow_ne_zero 2 hpZ) this
    simp_rw [e]
    rw [card_mem_cv hdet z, if_pos hy0]
    by_cases hz0 : red p z = 0
    · rw [if_pos (show red p y = 0 ∧ red p z = 0 from ⟨hy0, hz0⟩), hz0]
      have : ((isoSet Q p).filter fun vb => bv Q p 0 vb = 0) = isoSet Q p :=
        Finset.filter_true_of_mem fun vb _ => bv_zero_left vb
      rw [this, hiso]
      ring
    · rw [if_neg (show ¬ (red p y = 0 ∧ red p z = 0) from fun h => hz0 h.2), add_zero]
      -- the isotropic vectors orthogonal to z̄, minus 0
      have hK : (((isoSet Q p).filter fun vb => bv Q p (red p z) vb = 0).card : ℤ) + 1 =
          ((Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p (red p z) y = 0).card : ℤ) := by
        have : (Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p (red p z) y = 0) =
            insert 0 ((isoSet Q p).filter fun vb => bv Q p (red p z) vb = 0) := by
          ext w; by_cases hw : w = 0
          · subst hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, true_or,
              iff_true]
            exact ⟨qv_zero, by rw [bv_comm, bv_zero_left]⟩
          · simp [isoSet, hw]
        rw [this, Finset.card_insert_of_notMem (by simp [isoSet])]; push_cast; ring
      have hqz : qv Q p (red p z) = (m : ZMod p) := by rw [qv_red, hz]
      by_cases hm : (p : ℤ) ∣ m
      · have hκ' : κ = N0 - (p - 1) * p ^ (n - 2) := by rw [hκ, if_pos hm]
        have hiz : qv Q p (red p z) = 0 := by rw [hqz, dvd_of_red]; exact hm
        have := card_perp_isotropic hdet hn2 hz0 hiz
        have h' : ((Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p (red p z) y = 0).card : ℤ) +
            ((p : ℤ) - 1) * p ^ (n - 2) = N0 := by
          simp only [N0]; rw [← this]; push_cast [Nat.cast_sub hp1]; ring
        rw [hκ']
        linear_combination hK + h'
      · have hκ' : κ = (p : ℤ) ^ (n - 2) := by rw [hκ, if_neg hm]
        have hiz : qv Q p (red p z) ≠ 0 := by rw [hqz]; exact fun h => hm ((dvd_of_red m).mp h)
        have := card_perp_anisotropic hp2 hdet hn hn2 hiz
        have h' : ((Finset.univ.filter fun y => qv Q p y = 0 ∧ bv Q p (red p z) y = 0).card : ℤ) =
            (p : ℤ) ^ (n - 2) := by rw [this]; push_cast; ring
        rw [hκ']
        linear_combination hK + h'
  · rw [if_neg hy0, if_neg (show ¬ (red p y = 0 ∧ red p (divP p y) = 0) from fun h => hy0 h.1),
      card_mem_of_red_ne_zero hdet hy hy0]
    push_cast [Nat.cast_sub hp1]; ring

/-- **The neighbour relation for even $n$** ($p$ odd, $p \nmid \det H$, $Q$ positive definite): with $N_0 = \#\{\bar Q = 0\}$
($= p^{n-1} + \varepsilon(p-1)p^{n/2-1}$, `card_qv_zero`) and $\kappa = p^{n-2}$ ($p \nmid m$), $\kappa = N_0 - (p-1)p^{n-2}$ ($p \mid m$),
$$(p - 1)\sum_{L' \sim_p \mathbb{Z}^n} r_{L'}(m) = (p-1)\,r_Q(p^2m) + (\kappa - p)\,r_Q(m) + (N_0 - \kappa)\,r_Q(m/p^2).$$ -/
theorem sum_latRep_neighbors_even (hQ : IntQF.PosDef Q) (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (hn : Even n) (hn2 : 2 ≤ n) (m : ℤ) :
    ((p : ℤ) - 1) * ∑ L ∈ neighbors Q p, (latRep Q L m : ℤ) =
      ((p : ℤ) - 1) * repNum Q ((p : ℤ) ^ 2 * m) +
        ((if (p : ℤ) ∣ m then ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) - (p - 1) * p ^ (n - 2)
            else (p : ℤ) ^ (n - 2)) - p) * repNum Q m +
        (((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) -
            (if (p : ℤ) ∣ m then ((Finset.univ.filter fun y => qv Q p y = 0).card : ℤ) - (p - 1) * p ^ (n - 2)
              else (p : ℤ) ^ (n - 2))) * repNumDiv Q p m := by
  classical
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have h1 := sum_neighbors hdet (Q := Q) (fun L => (latRep Q L m : ℤ))
  rw [nsmul_eq_mul, Nat.cast_sub hp1, Nat.cast_one] at h1
  rw [h1]
  set R := repFinset hQ ((p : ℤ) ^ 2 * m)
  have h2 : ∑ vb ∈ isoSet Q p, (latRep Q (nbOf Q p vb) m : ℤ) =
      ∑ y ∈ R, (((isoSet Q p).filter fun vb => (1 / (p : ℚ)) • cv y ∈ nbOf Q p vb).card : ℤ) := by
    simp_rw [latRep_nbOf hQ, Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  rw [h2, Finset.sum_congr rfl fun y hy => card_mem_eq hp2 hdet hn hn2 ((mem_repFinset hQ).mp hy)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite, Finset.sum_ite,
    Finset.sum_const_zero, Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, Finset.sum_const,
    card_filter_red_eq_zero hQ, card_filter_red_divP hQ, card_repFinset hQ]
  simp only [nsmul_eq_mul]
  ring

/-- **The neighbour relation for $n = 4$** (Eichler commutation at the coefficient level; $p$ an odd prime,
$p \nmid \det H$, $Q$ positive definite, $\varepsilon = \left(\frac{\det H}{p}\right)$, $m \in \mathbb{Z}$):
$$\sum_{L' \sim_p \mathbb{Z}^4} r_{L'}(m) = r_Q(p^2m) + \big(p + [p \mid m]\,\varepsilon p\big)\,r_Q(m) + p^2\, r_Q(m/p^2).$$
The sum is over the $p^2 + p + 1 + \varepsilon p$ $p$-neighbours of $\mathbb{Z}^4$ (`card_neighbors_four`), and
$r_Q(m/p^2) = 0$ unless $p^2 \mid m$ (`repNumDiv`). -/
theorem sum_latRep_neighbors_four {Q : QuadForm ℤ 4} (hQ : IntQF.PosDef Q) (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) :
    ∑ L ∈ neighbors Q p, (latRep Q L m : ℤ) =
      repNum Q ((p : ℤ) ^ 2 * m) +
        (p + (if (p : ℤ) ∣ m then legendreSym p Q.hessian.det * p else 0)) * repNum Q m +
        (p : ℤ) ^ 2 * repNumDiv Q p m := by
  have h := sum_latRep_neighbors_even hQ hp2 hdet (by decide) (by norm_num) m
  have hN := card_qv_zero_four hp2 hdet (Q := Q) (p := p)
  rw [hN] at h
  have hp0 : ((p : ℤ) - 1) ≠ 0 := by have := hp.out.one_lt; omega
  apply mul_left_cancel₀ hp0
  rw [h]
  have hdiv : ¬ (p : ℤ) ∣ m → repNumDiv Q p m = 0 := by
    intro hm; unfold repNumDiv
    rw [if_neg]; exact fun h2 => hm ((dvd_pow_self _ two_ne_zero).trans h2)
  split_ifs with hm
  · norm_num; ring
  · rw [hdiv hm]; norm_num; ring

end Single

end QuadFormsKB.Siegel.Kneser
