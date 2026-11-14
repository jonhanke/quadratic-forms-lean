/-
# Absolute convergence of the singular series for sums of squares (Moreno–Wagstaff (6.17), p. 188)

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapter 6, (6.17), p. 188
(printed page): the singular series $\rho_s(n) = \sum_{m \ge 1} A_m(n)$ converges absolutely for $s \ge 5$.

**What is proved.** For $Q = x_0^2 + \dots + x_{s-1}^2$ and $S(h, c) = \sum_{t \bmod c} e(ht^2/c)$:

* `gz_sumSq`: the $s$-ary Gauss sum is the $s$-th power, $G(h, c) = S(h, c)^s$.
* `norm_gaussSum1_sq_le`: for $\gcd(h, c) = 1$, $|S(h, c)|^2 \le 2c$ (expand $|S|^2$, substitute $x = y + t$,
  and use orthogonality of the primitive character $\psi_c$: $\sum_y \psi_c(2hty) = c\cdot[2ht \equiv 0]$,
  which has at most two solutions $t$).
* `norm_ssTerm_sumSq_le`: for $c \ge 1$, $|A_c(m)| \le 2^{s/2}\,c^{1 - s/2}$ (at most $c$ residues $h$, each with
  $|S(h,c)^s| \le (2c)^{s/2}$, divided by $c^s$).
* `summable_ssTerm_sumSq`: for $s \ge 5$ the exponent $1 - s/2 \le -3/2 < -1$, so $\sum_c A_c(m)$ converges absolutely.

This is unconditional (no input hypotheses).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements

open Complex

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-- The evaluation of $I_s = x_0^2 + \dots + x_{s-1}^2$ over any commutative ring $R$:
$I_s(\vec r) = \sum_i r_i^2$. -/
lemma evalIn_sumSq (R : Type*) [CommRing R] {s : ℕ} (r : Fin s → R) :
    (sumSq s).evalIn R r = ∑ i, r i ^ 2 := by
  simp only [sumSq, QuadForm.diag, QuadForm.evalIn, Matrix.diagonal_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp [sq]

/-- An additive character turns a finite sum into a product: $\psi(\sum_{i \in S} f_i) = \prod_{i \in S}\psi(f_i)$. -/
lemma addChar_sum_eq_prod {G : Type*} [AddCommGroup G] (ψ : AddChar G ℂ) {ι : Type*} (S : Finset ι)
    (f : ι → G) : ψ (∑ i ∈ S, f i) = ∏ i ∈ S, ψ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- **The one-variable quadratic Gauss sum** $S(h, c) = \sum_{t \bmod c} e(h t^2 / c)$,
with $\psi_c$ = `ZMod.stdAddChar`. -/
noncomputable def gaussSum1 (c : ℕ) [NeZero c] (a : ZMod c) : ℂ :=
  ∑ t : ZMod c, ZMod.stdAddChar (a * t ^ 2)

/-- The $s$-ary Gauss sum of $I_s$ is the $s$-th power of the one-variable one: $G(h, c) = S(h, c)^s$. -/
lemma gz_sumSq (s c : ℕ) [NeZero c] (a : ZMod c) :
    SingularSeries.gz (sumSq s) c a = gaussSum1 c a ^ s := by
  unfold SingularSeries.gz gaussSum1
  have h1 : ∀ r : Fin s → ZMod c, ZMod.stdAddChar (a * (sumSq s).evalIn (ZMod c) r) =
      ∏ i, ZMod.stdAddChar (a * r i ^ 2) := by
    intro r
    rw [evalIn_sumSq, Finset.mul_sum, addChar_sum_eq_prod]
  simp_rw [h1]
  have := Finset.prod_univ_sum (fun _ : Fin s => (Finset.univ : Finset (ZMod c)))
    (fun _ t => (ZMod.stdAddChar (a * t ^ 2) : ℂ))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp

/-- The kernel of doubling on $\mathbb{Z}/c$ has at most two elements: $\#\{t : 2t = 0\} \le 2$. -/
lemma card_double_eq_zero_le (c : ℕ) [NeZero c] :
    (Finset.univ.filter fun t : ZMod c => 2 * t = 0).card ≤ 2 := by
  classical
  refine le_trans (Finset.card_le_card (t := {0, ((c / 2 : ℕ) : ZMod c)}) ?_) Finset.card_le_two
  intro t ht
  rw [Finset.mem_filter] at ht
  have h2 : ((2 * t.val : ℕ) : ZMod c) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val]; exact ht.2
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  have hlt := ZMod.val_lt t
  have hk2 : k < 2 := by
    by_contra h
    push_neg at h
    have : c * 2 ≤ c * k := Nat.mul_le_mul_left c h
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  interval_cases k
  · left
    have : t.val = 0 := by omega
    exact (ZMod.val_eq_zero t).mp this
  · right
    have : t.val = c / 2 := by omega
    rw [← this, ZMod.natCast_zmod_val]

/-- **Quadratic Gauss sum bound:** for $h$ a unit modulo $c$, $|S(h, c)|^2 \le 2c$. -/
lemma norm_gaussSum1_sq_le (c : ℕ) [NeZero c] (a : ZMod c) (ha : IsUnit a) :
    ‖gaussSum1 c a‖ ^ 2 ≤ 2 * (c : ℝ) := by
  classical
  set ψ : AddChar (ZMod c) ℂ := ZMod.stdAddChar with hψ
  have hconj : (starRingEnd ℂ) (gaussSum1 c a) = ∑ y : ZMod c, ψ (-(a * y ^ 2)) := by
    unfold gaussSum1
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.map_neg_eq_conj]
  have key : gaussSum1 c a * (starRingEnd ℂ) (gaussSum1 c a) =
      ∑ t : ZMod c, ψ (a * t ^ 2) * (if 2 * a * t = 0 then (c : ℂ) else 0) := by
    rw [hconj]
    unfold gaussSum1
    rw [Finset.sum_mul_sum]
    have step : ∀ y : ZMod c, ∑ x : ZMod c, ψ (a * x ^ 2) * ψ (-(a * y ^ 2)) =
        ∑ t : ZMod c, ψ (a * t ^ 2) * ψ (y * (2 * a * t)) := by
      intro y
      rw [← Fintype.sum_equiv (Equiv.addLeft y) (fun t => ψ (a * (y + t) ^ 2) * ψ (-(a * y ^ 2)))
        _ (fun _ => rfl)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [Finset.sum_comm]
    rw [← hψ]
    simp_rw [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have h := AddChar.sum_mulShift (ψ := ψ) (2 * a * t) (ZMod.isPrimitive_stdAddChar c)
    rw [h, ZMod.card]
    split_ifs <;> simp
  have hnorm : ‖gaussSum1 c a‖ ^ 2 = ‖gaussSum1 c a * (starRingEnd ℂ) (gaussSum1 c a)‖ := by
    rw [norm_mul, Complex.norm_conj, sq]
  rw [hnorm, key]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ t : ZMod c, ‖ψ (a * t ^ 2) * (if 2 * a * t = 0 then (c : ℂ) else 0)‖ =
      if 2 * t = 0 then (c : ℝ) else 0 := by
    intro t
    have hiff : 2 * a * t = 0 ↔ 2 * t = 0 := by
      rw [mul_comm 2 a, mul_assoc]
      exact ha.mul_right_eq_zero
    rw [norm_mul, AddChar.norm_apply, one_mul]
    by_cases h : 2 * t = 0
    · simp [h, hiff.mpr h]
    · simp [h, mt hiff.mp h]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have := card_double_eq_zero_le c
  have h' : ((Finset.univ.filter fun t : ZMod c => 2 * t = 0).card : ℝ) ≤ 2 := by exact_mod_cast this
  nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]

/-- For $h$ a unit modulo $c$: $|S(h, c)^s| \le (2c)^{s/2}$. -/
lemma norm_gz_sumSq_le (s c : ℕ) [NeZero c] (a : ZMod c) (ha : IsUnit a) :
    ‖SingularSeries.gz (sumSq s) c a‖ ≤ (2 * (c : ℝ)) ^ ((s : ℝ) / 2) := by
  rw [gz_sumSq, norm_pow]
  have h1 : ‖gaussSum1 c a‖ ≤ Real.sqrt (2 * c) := by
    have := Real.abs_le_sqrt (norm_gaussSum1_sq_le c a ha)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 s) ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  apply le_of_eq
  congr 1
  ring

/-- **Termwise bound:** for $c \ge 1$, $|A_c(m)| \le 2^{s/2}\,c^{1 - s/2}$ for $Q = x_0^2 + \dots + x_{s-1}^2$. -/
theorem norm_ssTerm_sumSq_le (s : ℕ) (m : ℤ) {c : ℕ} (hc : 1 ≤ c) :
    ‖SingularSeries.ssTerm (sumSq s) m c‖ ≤ 2 ^ ((s : ℝ) / 2) * (c : ℝ) ^ (1 - (s : ℝ) / 2) := by
  haveI : NeZero c := ⟨by omega⟩
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  set B : ℝ := (2 * (c : ℝ)) ^ ((s : ℝ) / 2) with hB
  have hU : ‖SingularSeries.uSum (sumSq s) m c‖ ≤ c * B := by
    unfold SingularSeries.uSum
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ a ∈ (Finset.range c).filter (fun a => Nat.Coprime a c),
        ‖SingularSeries.fz (sumSq s) m c (a : ZMod c)‖ ≤ B := by
      intro a ha
      have hcop := (Finset.mem_filter.mp ha).2
      have hu : IsUnit (a : ZMod c) := (ZMod.isUnit_iff_coprime a c).mpr hcop
      unfold SingularSeries.fz
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact norm_gz_sumSq_le s c _ hu
    refine le_trans (Finset.sum_le_card_nsmul _ _ B hterm) ?_
    rw [nsmul_eq_mul]
    have hcard : (((Finset.range c).filter (fun a => Nat.Coprime a c)).card : ℝ) ≤ c := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    have hB0 : 0 ≤ B := by positivity
    exact mul_le_mul_of_nonneg_right hcard hB0
  rw [SingularSeries.ssTerm_eq, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hmul : (c : ℝ)⁻¹ ^ 0 = 1 := by simp
  have h1 : ((c : ℝ) ^ s)⁻¹ * ‖SingularSeries.uSum (sumSq s) m c‖ ≤ ((c : ℝ) ^ s)⁻¹ * (c * B) :=
    mul_le_mul_of_nonneg_left hU (by positivity)
  refine le_trans h1 (le_of_eq ?_)
  set x : ℝ := (c : ℝ) ^ ((s : ℝ) / 2) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hcpos _
  have hcs : (c : ℝ) ^ s = x * x := by
    rw [hx, ← Real.rpow_add hcpos, ← Real.rpow_natCast]
    congr 1; ring
  have hB' : B = 2 ^ ((s : ℝ) / 2) * x := by
    rw [hB, Real.mul_rpow (by norm_num) hcpos.le]
  have hexp : (c : ℝ) ^ (1 - (s : ℝ) / 2) = c / x := by
    rw [Real.rpow_sub hcpos, Real.rpow_one]
  rw [hcs, hB', hexp]
  field_simp

/-- **Absolute convergence of the singular series** (Moreno–Wagstaff (6.17), $s \ge 5$): the series
$\sum_c A_c(m)$ of $x_0^2 + \dots + x_{s-1}^2$ is summable (indeed absolutely, since $|A_c(m)| \ll c^{1 - s/2}$
with $1 - s/2 \le -3/2$). -/
theorem summable_ssTerm_sumSq {s : ℕ} (hs : 5 ≤ s) (m : ℤ) :
    Summable (SingularSeries.ssTerm (sumSq s) m) := by
  have hs' : (5 : ℝ) ≤ s := by exact_mod_cast hs
  have hsum : Summable (fun c : ℕ => (c : ℝ) ^ (1 - (s : ℝ) / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded (hsum.mul_left (2 ^ ((s : ℝ) / 2))) fun c => ?_
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [SingularSeries.ssTerm_zero, norm_zero]
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by linarith)]
    simp
  · exact norm_ssTerm_sumSq_le s m hc

end QuadFormsKB.MorenoWagstaff
