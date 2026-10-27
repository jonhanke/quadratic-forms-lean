/-
# Local densities over $\mathbb{Q}$: local representability, stability, anisotropy, explicit values

**Layer:** $\mathbb{Q}$. **Defines** Hanke 2004, Def. 3.5 (locally represented, p. 362; `IsLocallyRepresentedAt`),
Def. 3.6 ($p$-stable, p. 362; `IsPStable`); Def. 3.7 (anisotropic, p. 363) is `¬ Q.IsotropicIn ℚ_[p]`.
**Proves** Table 1 for $n \le 4$ (p. 363; `table1_one` … `table1_four`), Remark 3.5.1 (`isLocallyRepresentedAt_of_good`),
Lemma 3.8 *corrected* (p. 363; `anisotropic_iff_zeroType`), Cor. 3.8.2
(p. 364; `card_rep_mul_pow_sq`), and (5.6), (5.7) (p. 369; `localDensity_le_mul_sq`, `localDensity_pow_sq`).
**Depends on** `General.lean`.
-/
import QuadFormsKB.LocalDensity.General

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **Local density of solutions of a given type** (Hanke 2004, Def. 5.1, p. 368):
$\beta^{T}_p(m) = \lim_k r^{T}_{p^k}(m)/p^{k(n-1)}$ for a type predicate $T$ at each level $k$
(e.g. $\beta^{\mathrm{Good}}_p$, $\beta^{\mathrm{Good} \cup \mathrm{Bad}}_p$). Normalized as `localDensity`. -/
noncomputable def localDensityOf (Q : QuadForm ℤ n) (p : ℕ) (m : ℤ)
    (T : (k : ℕ) → (Fin n → ZMod (p ^ k)) → Prop) : ℝ :=
  Filter.limUnder Filter.atTop fun k : ℕ => (repCountOf Q p k m (T k) : ℝ) / (p : ℝ) ^ (k * (n - 1))

/-- **Locally represented at $p$** (Hanke 2004, Def. 3.5, p. 362): $r_{p^k}(m) > 0$ for all large $k$. -/
def IsLocallyRepresentedAt (Q : QuadForm ℤ n) (p : ℕ) (m : ℤ) : Prop :=
  ∀ᶠ k in Filter.atTop, 0 < repCount Q p k m

/-- **$p$-stable** (Hanke 2004, Def. 3.6, p. 362), for a form in local normal form with unimodular
coordinates $S_0$: $m$ is locally represented at $p$, and for all large $k$ the number of non-Zero-type
solutions $r^{\mathrm{Good}}_{p^k}(p^{2\nu}m) + r^{\mathrm{Bad}}_{p^k}(p^{2\nu}m)$ is the same for every $\nu \ge 1$. -/
def IsPStable (Q : QuadForm ℤ n) (S₀ : Finset (Fin n)) (p : ℕ) (m : ℤ) : Prop :=
  IsLocallyRepresentedAt Q p m ∧
    ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q p k ((p : ℤ) ^ (2 * ν) * m) (fun x => ¬ IsZeroType p k x) =
        repCountOf Q p k ((p : ℤ) ^ 2 * m) (fun x => ¬ IsZeroType p k x)

/-! ### Table 1: solutions mod $p$ for $p \nmid 2N$, $n \le 4$ (p. 363)

For a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with $p \nmid 2\prod a_i$, $D = \prod a_i$ (the
determinant of the symmetric matrix $(c_{ij})$ of (2.1)) and $u$ a unit mod $p$; $(\frac{\cdot}{p})$ is the
Legendre symbol. *Proof:* Gauss sums (Kitaoka, Lemmas 1.3.1–1.3.2), or directly by counting points on
conics. -/

/-- **Table 1, $n = 1$:** $r_p(0) = 1$, $r_p(u) = 1 + (\frac{Du}{p})$. -/
@[kb "hanke2004" "Table 1, p. 363"]
theorem table1_one (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ¬ (p : ℤ) ∣ a) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) :
    repCount (QuadForm.diag ![a]) p 1 0 = 1 ∧
      (repCount (QuadForm.diag ![a]) p 1 u : ℤ) = 1 + legendreSym p (a * u) := by
  have ha' : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ m : ℤ, repCount (QuadForm.diag ![a]) p 1 m = Nat.card {y : ZMod p // y ^ 2 = ((a * m : ℤ) : ZMod p)} := by
    intro m
    unfold repCount
    simp only [QuadForm.evalIn, QuadForm.diag]
    rw [pow_one]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨(a : ZMod p) * x.1 0, by
        have := x.2
        simp at this
        push_cast
        linear_combination (a : ZMod p) * this⟩
      invFun := fun y => ⟨fun _ => (a : ZMod p)⁻¹ * y.1, by
        have := y.2
        push_cast at this
        simp
        field_simp
        linear_combination this⟩
      left_inv := by
        intro x
        ext i
        fin_cases i
        simp
        field_simp
      right_inv := by
        intro y
        ext
        simp
        field_simp }
  constructor
  · rw [key]
    simp
  · rw [key, Nat.card_eq_fintype_card, Fintype.card_subtype, add_comm]
    have := legendreSym.card_sqrts p hp (a * u)
    rw [← this]
    simp

/-- **Table 1, $n = 2$:** $r_p(0) = p + (p-1)(\frac{-D}{p})$, $r_p(u) = p - (\frac{-D}{p})$. -/
@[kb "hanke2004" "Table 1, p. 363"]
theorem table1_two (a b : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    (repCount (QuadForm.diag ![a, b]) p 1 0 : ℤ) = p + (p - 1) * legendreSym p (-(a * b)) ∧
      (repCount (QuadForm.diag ![a, b]) p 1 u : ℤ) = p - legendreSym p (-(a * b)) := by
  have hcount : ∀ m : ℤ, (repCount (QuadForm.diag ![a,b]) p 1 m : ℤ) = ((Finset.univ.filter (fun z : ZMod p × ZMod p => (a:ZMod p) * z.1^2 + (b:ZMod p) * z.2^2 = m)).card : ℤ) := by
    intro m
    unfold repCount
    rw [pow_one, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    congr 1
    refine Fintype.card_congr (Equiv.subtypeEquiv (piFinTwoEquiv _) (fun x => ?_))
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
    constructor <;> intro h <;> linear_combination h
  have hsum : ∀ (A B M : ZMod p), A ≠ 0 → B ≠ 0 →
      ((Finset.univ.filter (fun z : ZMod p × ZMod p => A * z.1^2 + B * z.2^2 = M)).card : ℤ)
        = ∑ x : ZMod p, (quadraticChar (ZMod p) ((M - A * x^2) / B) + 1) := by
    intro A B M hA hB
    have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← quadraticChar_card_sqrts hc, Set.toFinset_ofPred, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    apply propext
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; field_simp at h; linear_combination h
  have hU : ∀ (A B U : ZMod p), A ≠ 0 → B ≠ 0 → U ≠ 0 →
      ∑ x : ZMod p, (quadraticChar (ZMod p) ((U - A * x^2) / B) + 1) = p - quadraticChar (ZMod p) (-(A*B)) := by
    intro A B U hA hB hU
    have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    have hinv : (quadraticChar (ZMod p))⁻¹ = quadraticChar (ZMod p) := (quadraticChar_isQuadratic _).inv
    have hj : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = - quadraticChar (ZMod p) (-1) := by
      have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hc); rwa [hinv] at this
    set χ := quadraticChar (ZMod p)
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    have hfib : ∀ g : ZMod p → ℤ, ∑ x : ZMod p, g (x^2) = ∑ s : ZMod p, (χ s + 1) * g s := by
      intro g
      rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x^2)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => g s) (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
      rw [Finset.sum_const, nsmul_eq_mul, ← quadraticChar_card_sqrts hc, Set.toFinset_ofPred]
    rw [hfib (fun s => χ ((U - A * s) / B))]
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    have h1 : ∑ s : ZMod p, χ ((U - A * s) / B) = 0 := by
      rw [← quadraticChar_sum_zero hc]
      refine Fintype.sum_bijective (fun s => (U - A * s) / B) ?_ _ _ (fun _ => rfl)
      rw [← Finite.injective_iff_bijective]
      intro s t h
      simp only at h
      rw [div_left_inj' hB, sub_right_inj] at h
      exact mul_left_cancel₀ hA h
    have h2 : ∑ s : ZMod p, χ s * χ ((U - A * s) / B) = χ (A * B) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      symm
      refine Fintype.sum_bijective (fun t => U / A * t) ?_ _ _ ?_
      · rw [← Finite.injective_iff_bijective]
        intro s t h
        exact mul_left_cancel₀ (div_ne_zero hU hA) h
      · intro t
        have e2 : (U - A * (U / A * t)) / B = (U / B) * (1 - t) := by field_simp
        have e3 : χ (U/A) * χ (U/B) = χ (A*B) := by
          rw [← map_mul, show U/A*(U/B) = (U/(A*B))^2 * (A*B) by field_simp, map_mul,
            quadraticChar_sq_one' (by simp [hU,hA,hB]), one_mul]
        rw [e2, ← e3, map_mul χ (U/A) t, map_mul χ (U/B) (1-t)]
        ring
    rw [h1, h2, hj, show -(A*B) = -1 * (A*B) by ring, map_mul χ (-1)]
    ring
  have h0 : ∀ (A B : ZMod p), A ≠ 0 → B ≠ 0 →
      ∑ x : ZMod p, (quadraticChar (ZMod p) ((0 - A * x^2) / B) + 1) = p + (p - 1) * quadraticChar (ZMod p) (-(A*B)) := by
    intro A B hA hB
    set χ := quadraticChar (ZMod p)
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl (g := fun x => if x = 0 then 0 else χ (-(A*B))) ?_]
    · rw [Finset.sum_ite]
      simp [Finset.filter_ne', ZMod.card]
      rw [Nat.cast_sub (Fact.out : p.Prime).one_le]
      push_cast
      ring
    · intro x _
      split_ifs with hx
      · simp [hx, χ]
      · rw [show (0 - A * x^2) / B = (x / B)^2 * (-(A*B)) by field_simp <;> ring, map_mul,
          quadraticChar_sq_one' (by simp [hx, hB]), one_mul]
  have hA : (a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB : (b : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hU' : (u : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hleg : legendreSym p (-(a*b)) = quadraticChar (ZMod p) (-((a : ZMod p) * (b : ZMod p))) := by
    rw [legendreSym]; push_cast; rfl
  constructor
  · rw [hcount, hsum _ _ _ hA hB, hleg]
    simpa using h0 _ _ hA hB
  · rw [hcount, hsum _ _ _ hA hB, hleg]
    exact hU _ _ _ hA hB hU'

/-- **Table 1, $n = 3$:** $r_p(0) = p^2$, $r_p(u) = p^2 + p(\frac{-Du}{p})$. -/
@[kb "hanke2004" "Table 1, p. 363"]
theorem table1_three (a b c : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    repCount (QuadForm.diag ![a, b, c]) p 1 0 = p ^ 2 ∧
      (repCount (QuadForm.diag ![a, b, c]) p 1 u : ℤ) = p ^ 2 + p * legendreSym p (-(a * b * c * u)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hsq : ∀ f : ZMod p → ℤ, ∑ y : ZMod p, f (y^2) = ∑ t : ZMod p, (1 + quadraticChar (ZMod p) t) * f t := by
    intro f
    have h1 : ∀ y : ZMod p, f (y^2) = ∑ t : ZMod p, if y^2 = t then f t else 0 := by
      intro y; rw [Finset.sum_ite_eq]; simp
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := quadraticChar_card_sqrts hF t
    rw [Set.toFinset_setOf] at this
    rw [this]; ring
  have hlin : ∀ A B : ZMod p, B ≠ 0 → ∑ t : ZMod p, quadraticChar (ZMod p) (A + B * t) = 0 := by
    intro A B hB
    have hbij : Function.Bijective (fun t : ZMod p => A + B * t) := by
      rw [← Finite.injective_iff_bijective]
      intro x y h; simpa [hB] using h
    rw [Fintype.sum_bijective _ hbij _ (fun s => quadraticChar (ZMod p) s) (fun _ => rfl)]
    exact quadraticChar_sum_zero hF
  have hJ : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = - quadraticChar (ZMod p) (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic (ZMod p)).inv] at this
  have hB : ∀ A B : ZMod p, B ≠ 0 → ∑ y : ZMod p, quadraticChar (ZMod p) (A + B * y^2) = if A = 0 then (Fintype.card (ZMod p) - 1) * quadraticChar (ZMod p) B else - quadraticChar (ZMod p) B := by
    intro A B hB
    set χ := quadraticChar (ZMod p)
    rw [hsq (fun s => χ (A + B * s))]
    simp only [add_mul, one_mul, Finset.sum_add_distrib, hlin A B hB, zero_add]
    have hm1 : χ (-1) * χ (-1) = 1 := by
      rw [← map_mul]; norm_num
    split_ifs with hA
    · subst hA
      have : ∀ t : ZMod p, χ t * χ (0 + B * t) = χ B * (1 - if t = 0 then 1 else 0) := by
        intro t
        by_cases ht : t = 0
        · simp [ht, MulChar.map_zero]
        · simp only [ht, ite_false, sub_zero, mul_one, zero_add]
          rw [← map_mul, show t * (B * t) = B * t^2 by ring, map_mul, quadraticChar_sq_one' ht, mul_one]
      simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp; ring
    · have hbij : Function.Bijective (fun s : ZMod p => -A / B * s) := by
        rw [← Finite.injective_iff_bijective]
        intro x y h; simpa [hB, hA] using h
      rw [← Fintype.sum_bijective _ hbij (fun s => χ (-A / B * s) * χ (A + B * (-A / B * s))) _ (fun _ => rfl)]
      have : ∀ s : ZMod p, χ (-A / B * s) * χ (A + B * (-A / B * s)) = χ (-B) * (χ s * χ (1 - s)) := by
        intro s
        rw [← map_mul, ← map_mul, ← map_mul]
        have : -A / B * s * (A + B * (-A / B * s)) = (A / B)^2 * (-B * (s * (1 - s))) := by
          field_simp; ring
        rw [this, map_mul, quadraticChar_sq_one' (div_ne_zero hA hB), one_mul]
      simp_rw [this, ← Finset.mul_sum]
      rw [← jacobiSum, hJ, show -B = -1 * B by ring, map_mul]
      linear_combination (- χ B) * hm1
  have hcount : ∀ (a b c : ZMod p), a ≠ 0 → b ≠ 0 → c ≠ 0 → ∀ m : ZMod p,
      ∑ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p, (if a * x^2 + b * y^2 + c * z^2 = m then 1 else 0 : ℤ) = (Fintype.card (ZMod p))^2 + Fintype.card (ZMod p) * quadraticChar (ZMod p) (-(a*b*c*m)) := by
    intro a b c ha hb hc m
    set χ := quadraticChar (ZMod p)
    set q : ℤ := (Fintype.card (ZMod p) : ℤ)
    have hA : ∀ (a t : ZMod p), a ≠ 0 → ∑ x : ZMod p, (if a * x^2 = t then 1 else 0 : ℤ) = 1 + χ (a * t) := by
      intro a t ha
      rw [hsq (fun s => if a * s = t then 1 else 0)]
      simp only [mul_ite, mul_one, mul_zero]
      have : ∀ s : ZMod p, (a * s = t) ↔ s = t / a := by
        intro s; constructor
        · rintro rfl; field_simp
        · rintro rfl; field_simp
      simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      congr 1
      rw [show a * t = a^2 * (t / a) by field_simp, map_mul, quadraticChar_sq_one' ha, one_mul]
    have hM : ∀ r : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) = q - χ (-(b*c)) + q * χ (-(b*c)) * (if r = 0 then 1 else 0) := by
      intro r
      have : ∀ y : ZMod p, ∑ z : ZMod p, (if b * y^2 + c * z^2 = r then 1 else 0 : ℤ) = 1 + χ (c * r + (-(c * b)) * y^2) := by
        intro y
        have h2 : ∀ z : ZMod p, (b * y^2 + c * z^2 = r) ↔ c * z^2 = r - b * y^2 := by
          intro z; constructor <;> intro h <;> linear_combination h
        simp_rw [h2]
        rw [hA c _ hc]; ring_nf
      simp_rw [this, Finset.sum_add_distrib, hB _ _ (neg_ne_zero.mpr (mul_ne_zero hc hb))]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_eq_zero, hc, false_or]
      rw [show -(c*b) = -(b*c) by ring]
      split_ifs <;> ring
    have : ∀ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p, (if a * x^2 + b * y^2 + c * z^2 = m then 1 else 0 : ℤ) = q - χ (-(b*c)) + q * χ (-(b*c)) * (if a * x^2 = m then 1 else 0) := by
      intro x
      have h2 : ∀ y z : ZMod p, (a * x^2 + b * y^2 + c * z^2 = m) ↔ b * y^2 + c * z^2 = m - a * x^2 := by
        intro y z; constructor <;> intro h <;> linear_combination h
      simp_rw [h2]
      rw [hM]
      congr 2
      apply if_congr _ rfl rfl
      constructor <;> intro h <;> linear_combination -h
    have hχ : χ (-(a*b*c*m)) = χ (-(b*c)) * χ (a*m) := by
      rw [← map_mul]; ring_nf
    rw [hχ]
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hA a m ha]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hconv : ∀ m : ℤ, (repCount (QuadForm.diag ![a, b, c]) p 1 m : ℤ) = ∑ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p, if (a : ZMod p) * x^2 + b * y^2 + c * z^2 = m then 1 else 0 := by
    intro m
    unfold repCount
    rw [pow_one]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    rw [← (Fin.consEquiv fun _ => ZMod p).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← (Fin.consEquiv fun _ => ZMod p).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← (Fin.consEquiv fun _ => ZMod p).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_unique]
    have e : ∀ w : Fin 3 → ZMod p, QuadForm.evalIn (ZMod p) (QuadForm.diag ![a, b, c]) w = (a : ZMod p) * w 0 ^ 2 + b * w 1 ^ 2 + c * w 2 ^ 2 := by
      intro w
      simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
      ring
    rw [e, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  have hne : ∀ t : ℤ, ¬ (p : ℤ) ∣ t → (t : ZMod p) ≠ 0 := fun t ht h =>
    ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
  have key : ∀ m : ℤ, (repCount (QuadForm.diag ![a, b, c]) p 1 m : ℤ) = (p : ℤ)^2 + p * legendreSym p (-(a*b*c*m)) := by
    intro m
    rw [hconv, hcount _ _ _ (hne a ha) (hne b hb) (hne c hc), ZMod.card]
    unfold legendreSym
    push_cast
    rfl
  refine ⟨?_, key u⟩
  have := key 0
  simp only [mul_zero, neg_zero, legendreSym.at_zero, add_zero] at this
  exact_mod_cast this

/-- **Table 1, $n = 4$:** $r_p(0) = p^3 + p(p-1)(\frac{D}{p})$, $r_p(u) = p^3 - p(\frac{D}{p})$. -/
@[kb "hanke2004" "Table 1, p. 363"]
theorem table1_four (a b c d : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c) (hd : ¬ (p : ℤ) ∣ d) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    (repCount (QuadForm.diag ![a, b, c, d]) p 1 0 : ℤ) = p ^ 3 + p * (p - 1) * legendreSym p (a * b * c * d) ∧
      (repCount (QuadForm.diag ![a, b, c, d]) p 1 u : ℤ) = p ^ 3 - p * legendreSym p (a * b * c * d) := by
  set χ := quadraticChar (ZMod p) with hχ
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hsum : ∑ t, χ t = 0 := quadraticChar_sum_zero hF
  have cast_ne : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → (z : ZMod p) ≠ 0 := by
    intro z hz h; exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h)
  have N1 : ∀ e : ZMod p, e ≠ 0 → ∀ t : ZMod p, (∑ x : ZMod p, if e * x ^ 2 = t then (1:ℤ) else 0) = 1 + χ (e * t) := by
    intro e he t
    have h1 := quadraticChar_card_sqrts hF (t * e⁻¹)
    have key : χ (e * t) = χ (t * e⁻¹) := by
      have h2 : e * t = e ^ 2 * (t * e⁻¹) := by field_simp
      rw [h2, map_mul, quadraticChar_sq_one' he, one_mul]
    rw [Finset.sum_boole]
    have h3 : (Finset.univ.filter fun x : ZMod p => e * x ^ 2 = t) = {x | x ^ 2 = t * e⁻¹}.toFinset := by
      ext x; simp; constructor <;> intro h
      · rw [← h]; field_simp
      · rw [h]; field_simp
    rw [h3, h1, add_comm, key]
  have conv : ∀ {α β : Type} [Fintype α] [Fintype β] (f : α → ZMod p) (g : β → ZMod p) (s : ZMod p),
      (∑ x, ∑ y, if f x + g y = s then (1:ℤ) else 0) =
        ∑ t, (∑ x, if f x = t then (1:ℤ) else 0) * (∑ y, if g y = s - t then (1:ℤ) else 0) := by
    intro α β _ _ f g s
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    apply propext
    constructor <;> intro h <;> linear_combination h
  have S1 : ∀ e : ZMod p, ∑ t, χ (e * t) = 0 := by
    intro e
    simp_rw [map_mul, ← Finset.mul_sum, hsum, mul_zero]
  have S2 : ∀ e s : ZMod p, ∑ t, χ (e * (s - t)) = 0 := by
    intro e s
    simp_rw [map_mul, ← Finset.mul_sum]
    rw [Fintype.sum_equiv (Equiv.subLeft s) (fun t => χ (s - t)) χ (fun t => rfl), hsum, mul_zero]
  have J : ∀ s : ZMod p, ∑ t, χ t * χ (s - t) = if s = 0 then χ (-1) * (p - 1) else -χ (-1) := by
    intro s
    split_ifs with hs
    · subst hs
      have : ∀ t : ZMod p, χ t * χ (0 - t) = χ (-1) * (1 - if t = 0 then 1 else 0) := by
        intro t
        by_cases ht : t = 0
        · simp [ht, hχ]
        · rw [if_neg ht, zero_sub, neg_eq_neg_one_mul, map_mul, mul_left_comm, ← map_mul, ← sq, quadraticChar_sq_one' ht]; ring
      simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp [ZMod.card]
    · rw [← Fintype.sum_equiv (Equiv.mulLeft₀ s hs) (fun r => χ (s * r) * χ (s - s * r)) _ (fun r => rfl)]
      have : ∀ r : ZMod p, χ (s * r) * χ (s - s * r) = χ r * χ (1 - r) := by
        intro r
        rw [show s - s * r = s * (1 - r) by ring, map_mul, map_mul]
        have : χ s * χ s = 1 := by rw [← map_mul, ← sq, quadraticChar_sq_one' hs]
        linear_combination (χ r * χ (1 - r)) * this
      simp_rw [this]
      have hinv : χ⁻¹ = χ := (quadraticChar_isQuadratic (ZMod p)).inv
      have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
      rw [hinv] at this
      rw [← this]
      rfl
  have N2 : ∀ e1 e2 : ZMod p, e1 ≠ 0 → e2 ≠ 0 → ∀ s : ZMod p,
      (∑ x : ZMod p, ∑ y : ZMod p, if e1 * x ^ 2 + e2 * y ^ 2 = s then (1:ℤ) else 0) =
        p - χ (-(e1 * e2)) + if s = 0 then p * χ (-(e1 * e2)) else 0 := by
    intro e1 e2 h1 h2 s
    rw [conv (fun x => e1 * x ^ 2) (fun y => e2 * y ^ 2) s]
    simp only [N1 e1 h1, N1 e2 h2]
    have : ∀ t, (1 + χ (e1 * t)) * (1 + χ (e2 * (s - t))) = 1 + χ (e1 * t) + χ (e2 * (s - t)) + χ e1 * χ e2 * (χ t * χ (s - t)) := by
      intro t; rw [map_mul, map_mul]; ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, S1, S2, J]
    have hn : χ (-(e1 * e2)) = χ (-1) * χ e1 * χ e2 := by
      rw [neg_eq_neg_one_mul, map_mul, map_mul]; ring
    rw [hn]
    split_ifs <;> simp [ZMod.card] <;> ring
  have N4 : ∀ s : ZMod p, (∑ v : Fin 4 → ZMod p, if (a : ZMod p) * v 0 ^ 2 + b * v 1 ^ 2 + (c * v 2 ^ 2 + d * v 3 ^ 2) = s then (1:ℤ) else 0)
      = p ^ 3 - p * (χ (-(a * b)) * χ (-(c * d))) + if s = 0 then p ^ 2 * (χ (-(a * b)) * χ (-(c * d))) else 0 := by
    intro s
    let e : ((ZMod p × ZMod p) × (ZMod p × ZMod p)) ≃ (Fin 4 → ZMod p) :=
      { toFun := fun q => ![q.1.1, q.1.2, q.2.1, q.2.2]
        invFun := fun v => ((v 0, v 1), (v 2, v 3))
        left_inv := fun q => rfl
        right_inv := fun v => by ext i; fin_cases i <;> rfl }
    rw [← Fintype.sum_equiv e (fun q => if (a : ZMod p) * q.1.1 ^ 2 + b * q.1.2 ^ 2 + (c * q.2.1 ^ 2 + d * q.2.2 ^ 2) = s then (1:ℤ) else 0) _ (fun q => rfl)]
    rw [Fintype.sum_prod_type]
    rw [conv (fun q : ZMod p × ZMod p => (a : ZMod p) * q.1 ^ 2 + b * q.2 ^ 2) (fun q : ZMod p × ZMod p => (c : ZMod p) * q.1 ^ 2 + d * q.2 ^ 2) s]
    simp only [Fintype.sum_prod_type]
    simp only [N2 _ _ (cast_ne a ha) (cast_ne b hb), N2 _ _ (cast_ne c hc) (cast_ne d hd)]
    simp only [sub_eq_zero, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    split_ifs <;> ring
  have hcount : ∀ m : ℤ, (repCount (QuadForm.diag ![a,b,c,d]) p 1 m : ℤ) = ∑ v : Fin 4 → ZMod p, if (a : ZMod p) * v 0 ^ 2 + b * v 1 ^ 2 + (c * v 2 ^ 2 + d * v 3 ^ 2) = (m : ZMod p) then (1:ℤ) else 0 := by
    intro m
    unfold repCount; rw [pow_one]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    have : QuadForm.evalIn (ZMod p) (QuadForm.diag ![a,b,c,d]) v = (a : ZMod p) * v 0 ^ 2 + b * v 1 ^ 2 + (c * v 2 ^ 2 + d * v 3 ^ 2) := by
      simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal]
      ring
    simp only [this]
  have hL : legendreSym p (a * b * c * d) = χ (-(a * b)) * χ (-(c * d)) := by
    rw [← map_mul, hχ]; unfold legendreSym; push_cast; ring_nf
  rw [hcount, hcount, N4, N4, hL]
  have hu' := cast_ne u hu
  constructor
  · push_cast; simp only [ite_true]; ring
  · simp only [hu', ite_false]; ring

/-! ### Local representability, anisotropy, and the main-term recursion -/

/-- **Remark 3.5.1** (Hanke 2004, p. 362): for $n \ge 3$ and $p \nmid N$ (here: a diagonal form with
$p \nmid 2\prod a_i$), every $m$ is locally represented at $p$. *Proof:* by Table 1 every residue mod $p$
has a Good-type solution, and Good-type solutions lift (Lemma 3.2). -/
@[kb "hanke2004" "Remark 3.5.1, p. 362"]
theorem isLocallyRepresentedAt_of_good (a : Fin n → ℤ) (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (m : ℤ) :
    IsLocallyRepresentedAt (QuadForm.diag a) p m := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  have hpp : p.Prime := Fact.out
  have hev : ∀ (k : ℕ) (w : Fin (n'+3) → ℤ), QuadForm.evalIn (ZMod (p^k)) (QuadForm.diag a) (fun i => ((w i : ℤ) : ZMod (p^k))) = ((∑ i, a i * w i ^ 2 : ℤ) : ZMod (p^k)) := by
    intro k w
    simp [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]; exact hpp.mod_two_eq_one_iff_ne_two.mpr hp
  have hne : ∀ i, ((a i : ℤ) : ZMod p) ≠ 0 := fun i h => ha i ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (p:ℤ) ∣ a 0 * u^2 + a 1 * v^2 + a 2 - m := by
    obtain ⟨y0, y1, h⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C ((a 0 : ZMod p)) * Polynomial.X ^ 2 + Polynomial.C ((a 2 - m : ℤ) : ZMod p))
      (g := Polynomial.C ((a 1 : ZMod p)) * Polynomial.X ^ 2) (by compute_degree!; exact hne 0) (by compute_degree!; exact hne 1) hcard
    refine ⟨y0.val, y1.val, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id] 
    simp at h
    linear_combination h
  set w : Fin (n'+3) → ℤ := Fin.cons u (Fin.cons v (Fin.cons 1 0)) with hw
  have hsum : ∑ i, a i * w i ^ 2 = a 0 * u^2 + a 1 * v^2 + a 2 := by
    simp [hw, Fin.sum_univ_succ]
    ring
  have hp1 : ((p : ℕ) : ZMod (p^1)) = 0 := by rw [ZMod.natCast_eq_zero_iff]; simp
  have hpos : 0 < repCountOf (QuadForm.diag a) p 1 m (IsGoodType {i | ¬ (p:ℤ) ∣ a i} p 1) := by
    rw [repCountOf, Nat.card_pos_iff]
    refine ⟨⟨⟨fun i => ((w i : ℤ) : ZMod (p^1)), ?_, ?_⟩⟩, inferInstance⟩
    · rw [hev, hsum, ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      rw [pow_one]
      have := dvd_neg.mpr huv
      convert this using 1; ring
    · have h2 : ¬ (p : ZMod (p^1)) ∣ ((w 2 : ℤ) : ZMod (p^1)) := by
        rw [hp1, zero_dvd_iff]
        have : w 2 = 1 := by simp [hw]; rfl
        rw [this]
        intro h
        have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 (p^1)).mp h
        push_cast at h'; rw [pow_one] at h'; exact hpp.not_dvd_one (by exact_mod_cast h')
      refine ⟨fun h => h2 (h 2), 2, by simp [ha], h2⟩
  rw [IsLocallyRepresentedAt, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  have := repCountGood_add_diag a p m 1 l (by simp [hp])
  have hle : repCountOf (QuadForm.diag a) p (1 + l) m (IsGoodType {i | ¬ (p:ℤ) ∣ a i} p (1 + l)) ≤ repCount (QuadForm.diag a) p (1+l) m :=
    Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2.1⟩) (fun x y h => by ext1; simpa using h)
  refine lt_of_lt_of_le ?_ hle
  rw [this]
  exact Nat.mul_pos (pow_pos hpp.pos _) hpos

/-- **Zero / non-Zero split:** $r_{p^k}(m) = r^{\mathrm{Zero}}_{p^k}(m) + r^{\mathrm{Good}\cup\mathrm{Bad}}_{p^k}(m)$. -/
theorem repCount_eq_zero_add_nonZero (Q : QuadForm ℤ n) (p k : ℕ) [Fact p.Prime] (m : ℤ) :
    repCount Q p k m = repCountOf Q p k m (IsZeroType p k) +
      repCountOf Q p k m (fun x => ¬ IsZeroType p k x) := by
  classical
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold repCount repCountOf
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (fun x => IsZeroType p k x), Finset.filter_filter,
    Finset.filter_filter]

/-- **Homogeneity** over any commutative ring: $Q(c\vec{y}) = c^2 Q(\vec{y})$. -/
theorem evalIn_const_mul {K : Type*} [CommRing K] [Algebra ℤ K] (Q : QuadForm ℤ n) (c : K)
    (y : Fin n → K) : Q.evalIn K (fun j => c * y j) = c ^ 2 * Q.evalIn K y := by
  simp only [QuadForm.evalIn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- An isotropic form over $\mathbb{Q}_p$ has a primitive solution of $Q \equiv 0 \pmod{p^k}$ for every
$k \ge 1$: scale an isotropic vector so that its largest coordinate is $1$ and reduce mod $p^k$. -/
theorem exists_primitive_zero_mod_of_isotropicIn (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (hiso : Q.IsotropicIn ℚ_[p]) (k : ℕ) (hk : 1 ≤ k) :
    ∃ x : Fin n → ZMod (p ^ k), Q.evalIn (ZMod (p ^ k)) x = 0 ∧ ¬ IsZeroType p k x := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx0
  have : Nonempty (Fin n) := ⟨i0⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ‖x j‖)
  have hxi : x i ≠ 0 := by
    intro h
    have := hi i0
    rw [h, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  let y : Fin n → ℤ_[p] := fun j => ⟨x j / x i, by
    show ‖x j / x i‖ ≤ 1
    rw [norm_div]
    exact div_le_one_of_le₀ (hi j) (norm_nonneg _)⟩
  have hyi : y i = 1 := PadicInt.ext (by simp [y, hxi])
  have hy : Q.evalIn ℤ_[p] y = 0 := by
    have h2 : (fun j => PadicInt.Coe.ringHom (y j)) = fun j => (x i)⁻¹ * x j := by
      funext j; change x j / x i = _; rw [div_eq_mul_inv, mul_comm]
    have : PadicInt.Coe.ringHom (Q.evalIn ℤ_[p] y) = 0 := by
      rw [evalIn_intForm_map, h2, evalIn_const_mul, hx, mul_zero]
    exact PadicInt.ext this
  refine ⟨fun j => PadicInt.toZModPow k (y j), ?_, ?_⟩
  · rw [← evalIn_intForm_map, hy, map_zero]
  · intro h
    have := h i
    simp only [hyi, map_one] at this
    have h1 := intCast_pow_dvd_of_zmod p k 1 hk 1 (by simpa using this)
    simp only [pow_one] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

/-- **Compactness of $\mathbb{Z}_p^n$:** if for every $C$ some primitive integer vector $\vec{z}$ has
$p^C \mid Q(\vec{z})$, then $Q$ is isotropic over $\mathbb{Q}_p$ (a limit point of these vectors in
$\mathbb{Z}_p^n$ has sup-norm $1$ and $Q = 0$). -/
theorem isotropicIn_of_primitive_pow_dvd (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (h : ∀ C : ℕ, ∃ z : Fin n → ℤ, (∃ i, ¬ (p : ℤ) ∣ z i) ∧ (p : ℤ) ^ C ∣ Q.eval z) :
    Q.IsotropicIn ℚ_[p] := by
  choose z hz hdvd using h
  let y : ℕ → Fin n → ℤ_[p] := fun C i => (z C i : ℤ_[p])
  have hy1 : ∀ C, ‖y C‖ = 1 := by
    intro C
    obtain ⟨i, hi⟩ := hz C
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => PadicInt.norm_le_one _) ?_
    have : ‖y C i‖ = 1 := by
      have h1 := (PadicInt.norm_int_lt_one_iff_dvd (p := p) (z C i)).not.mpr hi
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h1)
    exact this ▸ norm_le_pi_norm (y C) i
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := y) (fun _ => Set.mem_univ _)
  have ha1 : ‖a‖ = 1 := by
    have := (continuous_norm.tendsto a).comp hlim
    simp only [Function.comp_def, hy1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  let F : (Fin n → ℤ_[p]) → ℤ_[p] := fun v => Q.evalIn ℤ_[p] v
  have hF : Continuous F := by
    simp only [F, QuadForm.evalIn]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs <;> fun_prop
  have hFy : ∀ C, ‖F (y C)‖ ≤ (p : ℝ) ^ (-(C : ℤ)) := by
    intro C
    simp only [F, y, evalIn_intCast_vec]
    exact PadicInt.norm_int_le_pow_iff_dvd.mpr (by exact_mod_cast hdvd C)
  have hFa : ∀ C : ℕ, ‖F a‖ ≤ (p : ℝ) ^ (-(C : ℤ)) := by
    intro C
    have hl := (continuous_norm.tendsto _).comp ((hF.tendsto a).comp hlim)
    refine le_of_tendsto hl (Filter.eventually_atTop.2 ⟨C, fun j hj => ?_⟩)
    refine (hFy (φ j)).trans (zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) ?_)
    have := hφ.id_le j
    simp only [id] at this
    simp only [neg_le_neg_iff, Nat.cast_le]; omega
  have hF0 : F a = 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have ht : Filter.Tendsto (fun C : ℕ => (p : ℝ) ^ (-(C : ℤ))) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0:ℝ) ≤ (p : ℝ)⁻¹)
        (inv_lt_one_of_one_lt₀ hp1)
      refine this.congr fun C => ?_
      rw [zpow_neg, zpow_natCast, inv_pow]
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hFa)
  refine ⟨fun i => (a i : ℚ_[p]), ?_, ?_⟩
  · intro h0
    have : a = 0 := funext fun i => PadicInt.ext (by simpa using congrFun h0 i)
    rw [this, norm_zero] at ha1
    exact zero_ne_one ha1
  · have := evalIn_intForm_map (PadicInt.Coe.ringHom (p := p)) Q a
    change PadicInt.Coe.ringHom (F a) = _ at this
    rw [hF0, map_zero] at this
    exact this.symm

/-- **Bounded valuation of primitive vectors** (Hanke 2004, p. 363, O'Meara 91:1): if $Q$ is anisotropic
over $\mathbb{Q}_p$, there is $C$ such that for $k \ge C$ every solution of $Q(\vec{x}) \equiv 0
\pmod{p^k}$ is of Zero type. -/
@[kb "omeara1963" "§91A, 91:1, p. 239 (the set {x : Q(x) ∈ 𝔞} is a lattice on an anisotropic space)"]
theorem exists_isZeroType_of_anisotropic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (haniso : ¬ Q.IsotropicIn ℚ_[p]) :
    ∃ C : ℕ, ∀ k ≥ C, ∀ x : Fin n → ZMod (p ^ k),
      Q.evalIn (ZMod (p ^ k)) x = 0 → IsZeroType p k x := by
  by_contra hcon
  push Not at hcon
  apply haniso
  apply isotropicIn_of_primitive_pow_dvd
  intro C
  obtain ⟨k, hk, x, hx, hxz⟩ := hcon C
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hcast : (fun i => (((x i).val : ℤ) : ZMod (p ^ k))) = x := by
    funext i; simp
  refine ⟨fun i => ((x i).val : ℤ), ?_, ?_⟩
  · unfold IsZeroType at hxz
    push Not at hxz
    obtain ⟨i, hi⟩ := hxz
    refine ⟨i, fun hd => hi ?_⟩
    simpa using map_dvd (Int.castRingHom (ZMod (p ^ k))) hd
  · have h1 := evalIn_intCast_vec (ZMod (p ^ k)) Q (fun i => ((x i).val : ℤ))
    rw [hcast, hx, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact (pow_dvd_pow _ hk).trans (by exact_mod_cast h1)

/-- **No non-Zero-type solutions at $p^{2\nu}m$** ($\nu \ge 1$, $k \gg 1$) for $Q$ anisotropic at $p$ under
the constancy half of $p$-stability: the common count equals the count at $p^{2k}m \equiv 0 \pmod{p^k}$,
which vanishes for $k$ beyond the valuation bound of `exists_isZeroType_of_anisotropic`. -/
theorem eventually_repCountOf_nonZero_eq_zero (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (haniso : ¬ Q.IsotropicIn ℚ_[p]) (m : ℤ)
    (hstab : ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q p k ((p : ℤ) ^ (2 * ν) * m) (fun x => ¬ IsZeroType p k x) =
        repCountOf Q p k ((p : ℤ) ^ 2 * m) (fun x => ¬ IsZeroType p k x)) :
    ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q p k ((p : ℤ) ^ (2 * ν) * m) (fun x => ¬ IsZeroType p k x) = 0 := by
  obtain ⟨C, hC⟩ := exists_isZeroType_of_anisotropic Q p haniso
  filter_upwards [hstab, Filter.eventually_ge_atTop (max C 1)] with k hk hkC ν hν
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [hk ν hν, ← hk k (by omega : k ≥ 1)]
  rw [repCountOf, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx, hxz⟩ => hxz (hC k (by omega) x ?_)⟩
  rw [hx, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- **Lemma 3.8, corrected** (Hanke 2004, p. 363; erratum confirmed by the author 2026-10-15):
for $Q$ nondegenerate in local normal form and $m$ $p$-stable (Def. 3.6,
constancy for $\nu \ge 1$), $Q$ is anisotropic at $p$ iff for all large $k$ every solution of
$Q(\vec{x}) \equiv p^2 m \pmod{p^k}$ is of Zero type.

*Erratum:* the paper states the conclusion for $m$ itself (with $p \mid m$), which is false: $p = 3$,
$Q = x^2 + y^2 + 3z^2$, $m = 3$ ($Q$ anisotropic at 3, $m$ 3-stable, but $(0,0,1)$ is a primitive solution). The
proof's reduction to "$m$ sufficiently $p$-divisible" is valid from $p^2 m$ on, which is what stability gives.

*Proof* (pp. 363–364, applied at $p^2m$). ($\Rightarrow$) For anisotropic $Q$, primitive vectors have
bounded valuation $v_p(Q(\vec{x})) \le C$ (the set $\{\vec{x} : Q(\vec{x}) \in \mathbb{Z}_p\}$ is a lattice, O'Meara 91:1),
so $p^{2\nu}m$ has no primitive solutions mod $p^k$ for $\nu$ large and $k > C$; $p$-stability (constancy for
$\nu \ge 1$) transports this to $\nu = 1$. ($\Leftarrow$) If $Q$ is isotropic, a hyperbolic pair gives primitive
solutions of $Q = p^{2\nu}m$ for $\nu$ large (valuation $r + t$, see the p. 364 typo entry), and stability
transports them to $p^2m$. -/
@[kb "hanke2004" "Lemma 3.8, p. 363 (corrected)"]
theorem anisotropic_iff_zeroType (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (m : ℤ)
    (hm : IsPStable Q (unimodularCoords ν) p m) :
    ¬ Q.IsotropicIn ℚ_[p] ↔
      ∀ᶠ k in Filter.atTop,
        repCount Q p k ((p : ℤ) ^ 2 * m) = repCountOf Q p k ((p : ℤ) ^ 2 * m) (IsZeroType p k) := by
  constructor
  · intro haniso
    filter_upwards [eventually_repCountOf_nonZero_eq_zero Q p haniso m hm.2] with k hk
    have := hk 1 le_rfl
    rw [mul_one] at this
    rw [repCount_eq_zero_add_nonZero, this, add_zero]
  · intro h hiso
    obtain ⟨k, hk, hks, hk1⟩ := (h.and (hm.2.and (Filter.eventually_ge_atTop 1))).exists
    have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨x, hx, hxz⟩ := exists_primitive_zero_mod_of_isotropicIn Q p hiso k hk1
    have hpos : 0 < repCountOf Q p k ((p : ℤ) ^ (2 * k) * m) (fun x => ¬ IsZeroType p k x) := by
      rw [repCountOf, Nat.card_pos_iff]
      refine ⟨⟨⟨x, ?_, hxz⟩⟩, inferInstance⟩
      rw [hx, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    rw [hks k hk1] at hpos
    have := repCount_eq_zero_add_nonZero Q p k ((p : ℤ) ^ 2 * m)
    omega

/-- Solutions of a given type are among all solutions: $r^{T}_{p^k}(m) \le r_{p^k}(m)$. -/
theorem repCountOf_le_repCount (Q : QuadForm ℤ n) (p k : ℕ) [Fact p.Prime] (m : ℤ)
    (T : (Fin n → ZMod (p ^ k)) → Prop) : repCountOf Q p k m T ≤ repCount Q p k m := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold repCountOf repCount
  exact Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2.1⟩)
    (fun x y h => Subtype.ext (congrArg Subtype.val h :))

/-- A nondegenerate form in one variable is anisotropic over $\mathbb{Q}_p$; so an isotropic
nondegenerate form has $n \ne 1$. -/
theorem ne_one_of_isotropicIn (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hiso : Q.IsotropicIn ℚ_[p]) : n ≠ 1 := by
  rintro rfl
  obtain ⟨x, hx0, hx⟩ := hiso
  have hc : Q.coeff 0 0 ≠ 0 := by
    intro h; apply hQ; simp [hessian, Matrix.det_unique, h]
  have hx1 : x 0 ≠ 0 := fun h => hx0 (funext fun i => by fin_cases i; exact h)
  simp [evalIn] at hx
  rcases hx with h | h
  · exact hc (by exact_mod_cast h)
  · exact hx1 h

/-- Exponent bookkeeping for the map $\pi_Z$: $n + (k-2)(n-1) + (n-2) = k(n-1)$ for $k \ge 2$, $n \ne 1$. -/
theorem exponent_piZ (n k : ℕ) (hn : n ≠ 1) (hk : 2 ≤ k) :
    n + (k - 2) * (n - 1) + (n - 2) = k * (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rcases n with _ | _ | n
  · simp
  · exact absurd rfl hn
  · simp only [Nat.add_sub_cancel]
    ring_nf; omega

/-- **Normalized Zero-type count** (map $\pi_Z$, Hanke 2004, p. 359): for $k \ge 2$ and $n \ne 1$,
$r^{\mathrm{Zero}}_{p^k}(p^2m)/p^{k(n-1)} = p^{-(n-2)}\, r_{p^{k-2}}(m)/p^{(k-2)(n-1)}$. -/
theorem repCountZero_normalized (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (hn : n ≠ 1) (m : ℤ)
    (k : ℕ) (hk : 2 ≤ k) :
    (repCountOf Q p k ((p : ℤ) ^ 2 * m) (IsZeroType p k) : ℝ) / (p : ℝ) ^ (k * (n - 1)) =
      ((p : ℝ) ^ (n - 2))⁻¹ * ((repCount Q p (k - 2) m : ℝ) / (p : ℝ) ^ ((k - 2) * (n - 1))) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [repCountZero_eq Q p _ k hk]
  simp only [dvd_mul_right, ↓reduceIte]
  rw [Int.mul_ediv_cancel_left _ hpZ,
    ← exponent_piZ n k hn hk, pow_add, pow_add]
  push_cast
  field_simp

/-- **Split of the normalized count** at $p^2m$ into the Zero part (via $\pi_Z$) and the
Good ∪ Bad part, for $k \ge 2$ and $n \ne 1$. -/
theorem normalized_split (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (hn : n ≠ 1) (m : ℤ)
    (k : ℕ) (hk : 2 ≤ k) :
    (repCount Q p k ((p : ℤ) ^ 2 * m) : ℝ) / (p : ℝ) ^ (k * (n - 1)) =
      ((p : ℝ) ^ (n - 2))⁻¹ * ((repCount Q p (k - 2) m : ℝ) / (p : ℝ) ^ ((k - 2) * (n - 1))) +
      (repCountOf Q p k ((p : ℤ) ^ 2 * m) (fun x => ¬ IsZeroType p k x) : ℝ) /
        (p : ℝ) ^ (k * (n - 1)) := by
  rw [repCount_eq_zero_add_nonZero, Nat.cast_add, add_div, repCountZero_normalized Q p hn m k hk]

/-- **(5.6)** (Hanke 2004, p. 369): for $Q$ nondegenerate, $n \ge 3$ and $m \ne 0$,
$\beta_p(p^2 m) \ge p^{2-n}\beta_p(m)$. *Proof:* $r_{p^k}(p^2m) \ge r^{\mathrm{Zero}}_{p^k}(p^2m) = p^n r_{p^{k-2}}(m)$
(`repCountZero_eq`); divide by $p^{k(n-1)}$ and let $k \to \infty$ (`localDensity_eventually_eq`). -/
@[kb "hanke2004" "(5.6), p. 369"]
theorem localDensity_le_mul_sq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    localDensity Q p m ≤ (p : ℝ) ^ (n - 2) * localDensity Q p ((p : ℤ) ^ 2 * m) := by
  have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := localDensity_eventually_eq Q hQ p ((p : ℤ) ^ 2 * m) (mul_ne_zero hpZ hm)
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ p m hm)
  obtain ⟨k, hk1, hk2, hk⟩ := (h1.and (h2.and (Filter.eventually_ge_atTop 2))).exists
  rw [← hk1, ← hk2, normalized_split Q p (by omega) m k hk, mul_add,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0.ne'), one_mul, le_add_iff_nonneg_right]
  positivity

-- copied defs from Explicit.lean
/-- **Non-Zero-type density at $p^2T$ is a genuine limit** (Hanke 2004, p. 369): under the
$p$-stability condition, $r^{\mathrm{Good}\cup\mathrm{Bad}}_{p^k}(p^2T)/p^{k(n-1)}$ is eventually
$\beta_p(p^2T) - p^{-(n-2)}\beta_p(T)$, so `localDensityOf` equals that value. -/
theorem localDensityOf_nonZero_eq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hn : n ≠ 1) (T : ℤ) (hT0 : T ≠ 0) :
    localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
      localDensity Q p ((p : ℤ) ^ 2 * T) - ((p : ℝ) ^ (n - 2))⁻¹ * localDensity Q p T := by
  have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 := localDensity_eventually_eq Q hQ p ((p : ℤ) ^ 2 * T) (mul_ne_zero hpZ hT0)
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ p T hT0)
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 2] with k hk1 hk2 hk
  rw [← hk1, ← hk2, normalized_split Q p hn T k hk]
  ring

/-- **One step of (5.7)**: under $p$-stability, for $\nu \ge 1$,
$\beta_p(p^{2\nu}T) = K + p^{-(n-2)}\beta_p(p^{2(\nu-1)}T)$ with
$K = \beta_p(p^2T) - p^{-(n-2)}\beta_p(T)$. -/
theorem localDensity_pow_sq_step (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hn : n ≠ 1) (T : ℤ) (hT0 : T ≠ 0)
    (hstab : ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q p k ((p : ℤ) ^ (2 * ν) * T) (fun x => ¬ IsZeroType p k x) =
        repCountOf Q p k ((p : ℤ) ^ 2 * T) (fun x => ¬ IsZeroType p k x))
    (e : ℕ) :
    localDensity Q p ((p : ℤ) ^ (2 * (e + 1)) * T) =
      (localDensity Q p ((p : ℤ) ^ 2 * T) - ((p : ℝ) ^ (n - 2))⁻¹ * localDensity Q p T) +
        ((p : ℝ) ^ (n - 2))⁻¹ * localDensity Q p ((p : ℤ) ^ (2 * e) * T) := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have hpe : ((p : ℤ) ^ (2 * e) * T) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp) hT0
  have heq : (p : ℤ) ^ (2 * (e + 1)) * T = (p : ℤ) ^ 2 * ((p : ℤ) ^ (2 * e) * T) := by ring
  have h1 := localDensity_eventually_eq Q hQ p ((p : ℤ) ^ 2 * T) (mul_ne_zero hpZ hT0)
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ p T hT0)
  have h3 := localDensity_eventually_eq Q hQ p ((p : ℤ) ^ (2 * (e + 1)) * T)
    (heq ▸ mul_ne_zero hpZ hpe)
  have h4 := (Filter.tendsto_sub_atTop_nat 2).eventually
    (localDensity_eventually_eq Q hQ p ((p : ℤ) ^ (2 * e) * T) hpe)
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5, hk⟩ :=
    (h1.and (h2.and (h3.and (h4.and (hstab.and (Filter.eventually_ge_atTop 2)))))).exists
  rw [← hk1, ← hk2, ← hk3, ← hk4, normalized_split Q p hn T k hk, heq,
    normalized_split Q p hn _ k hk, ← heq, hk5 (e + 1) (by omega)]
  ring

/-- **(5.7)** (Hanke 2004, p. 369): for $Q$ nondegenerate in local normal form, isotropic at $p$, and
$T'$ $p$-stable with $T' \ne 0$, writing $K = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_p(p^2 T')$ and $q = p$,
$$\beta_p(T' p^{2\nu}) = K \sum_{i=0}^{\nu-1} q^{-(n-2)i} + \frac{\beta_p(T')}{q^{(n-2)\nu}}.$$
*Proof:* by $p$-stability the non-Zero-type part of $\beta_p(T'p^{2i})$ is $K$ for every $i \ge 1$, and
the Zero-type part is $q^{-(n-2)}\beta_p(T'p^{2(i-1)})$ (map $\pi_Z$); iterate. -/
@[kb "hanke2004" "(5.7), p. 369"]
theorem localDensity_pow_sq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν)
    (hiso : Q.IsotropicIn ℚ_[p]) (T : ℤ) (hT0 : T ≠ 0) (hT : IsPStable Q (unimodularCoords ν) p T)
    (e : ℕ) :
    localDensity Q p ((p : ℤ) ^ (2 * e) * T) =
      localDensityOf Q p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) *
          ∑ i ∈ Finset.range e, ((p : ℝ) ^ (n - 2))⁻¹ ^ i +
        localDensity Q p T / (p : ℝ) ^ ((n - 2) * e) := by
  have hn := ne_one_of_isotropicIn Q hQ p hiso
  rw [localDensityOf_nonZero_eq Q hQ p hn T hT0]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [localDensity_pow_sq_step Q hQ p hn T hT0 hT.2 e, ih, Finset.sum_range_succ', pow_mul,
      pow_mul, Finset.sum_congr rfl (fun i _ => pow_succ ((p : ℝ) ^ (n - 2))⁻¹ i), ← Finset.sum_mul,
      pow_succ (_ ^ _) e, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

/-- **Corollary 3.8.2** (Hanke 2004, p. 364): if $Q$ (nondegenerate) is anisotropic at $p$ and $m$ is
$p$-stable, then $r_Q(mp^{2\nu}) = r_Q(m)$ for all $\nu \ge 0$, where
$r_Q(m) = \#\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) = m\}$. *Proof:* by Lemma 3.8 every representation of $mp^{2\nu}$ is
$p^\nu\vec{x}'$ with $Q(\vec{x}') = m$; $\vec{x}' \mapsto p^\nu\vec{x}'$ is a bijection. -/
@[kb "hanke2004" "Cor. 3.8.2, p. 364"]
theorem card_rep_mul_pow_sq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν)
    (haniso : ¬ Q.IsotropicIn ℚ_[p]) (m : ℤ) (hm : IsPStable Q (unimodularCoords ν) p m) (e : ℕ) :
    Set.ncard {x : Fin n → ℤ | Q.eval x = (p : ℤ) ^ (2 * e) * m} = Set.ncard {x : Fin n → ℤ | Q.eval x = m} := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- every integral solution at $p^{2\nu}m$, $\nu \ge 1$, is divisible by $p$
  have hdiv : ∀ μ ≥ 1, ∀ z : Fin n → ℤ, Q.eval z = (p : ℤ) ^ (2 * μ) * m → ∀ i, (p : ℤ) ∣ z i := by
    intro μ hμ z hz
    obtain ⟨k, hk, hk1⟩ := ((eventually_repCountOf_nonZero_eq_zero Q p haniso m hm.2).and
      (Filter.eventually_ge_atTop 1)).exists
    have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    have hzt : IsZeroType p k (fun i => (z i : ZMod (p ^ k))) := by
      by_contra hzt
      have h0 := hk μ hμ
      rw [repCountOf, Nat.card_eq_zero] at h0
      rcases h0 with h0 | h0
      · refine h0.false ⟨_, ?_, hzt⟩
        rw [evalIn_intCast_vec, hz]
      · exact absurd h0 (not_infinite_iff_finite.mpr inferInstance)
    intro i
    have := intCast_pow_dvd_of_zmod p k 1 hk1 (z i) (by simpa using hzt i)
    simpa using this
  induction e with
  | zero => simp
  | succ e ih =>
    rw [← ih]
    symm
    refine Set.ncard_congr (fun x _ => fun i => (p : ℤ) * x i) ?_ ?_ ?_
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      change Q.evalIn ℤ (fun i => (p : ℤ) * x i) = _
      rw [evalIn_const_mul, show Q.evalIn ℤ x = _ from hx]
      ring
    · intro a b _ _ hab
      funext i
      exact mul_left_cancel₀ hp0 (congrFun hab i)
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      have hd := hdiv (e + 1) (by omega) z hz
      choose w hw using hd
      refine ⟨w, ?_, funext fun i => (hw i).symm⟩
      simp only [Set.mem_ofPred_eq]
      have h2 : Q.eval z = (p : ℤ) ^ 2 * Q.eval w := evalIn_const_mul Q (p : ℤ) w ▸ congrArg Q.eval (funext hw)
      rw [h2, show 2 * (e + 1) = 2 + 2 * e by ring, pow_add, mul_assoc] at hz
      exact mul_left_cancel₀ (pow_ne_zero _ hp0) hz

end QuadFormsKB.LocalDensity
